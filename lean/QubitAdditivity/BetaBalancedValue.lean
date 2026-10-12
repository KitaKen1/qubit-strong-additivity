import QubitAdditivity.BetaNormalizedOuter
import QubitAdditivity.BetaSupportMinimum
import QubitAdditivity.BetaTC4Structure

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius

namespace QubitAdditivity.BetaBalancedValue
open BetaDual BetaEntropy BetaDualValue BetaIsometryEntropy BetaBlockIsometry BetaGramSplit BetaScalarMinimum
open BetaNormalizedOuter BetaSupportMinimum BetaTC4Structure

@[reducible] local instance mNorm {k : Type*} [Fintype k] [DecidableEq k] :
    NormedAddCommGroup (Matrix k k ℂ) :=
  Matrix.frobeniusNormedRing.toNonUnitalNormedRing.toNormedAddCommGroup
@[reducible] local instance mSpace {k : Type*} [Fintype k] [DecidableEq k] :
    NormedSpace ℝ (Matrix k k ℂ) := NormedAlgebra.toNormedSpace (Matrix k k ℂ)
@[reducible] local instance mTop {k : Type*} [Fintype k] [DecidableEq k] :
    TopologicalSpace (Matrix k k ℂ) := mNorm.toUniformSpace.toTopologicalSpace
@[reducible] local instance mAdd {k : Type*} [Fintype k] [DecidableEq k] :
    AddCommGroup (Matrix k k ℂ) := mNorm.toAddCommGroup
@[reducible] local instance mModule {k : Type*} [Fintype k] [DecidableEq k] :
    Module ℝ (Matrix k k ℂ) := mSpace.toModule
@[reducible] local instance hTop {k : Type*} [Fintype k] : TopologicalSpace (HermitianMat k ℂ) :=
  HermitianMat.instNormedAddCommGroupComplex.toUniformSpace.toTopologicalSpace
@[reducible] local instance hAdd {k : Type*} [Fintype k] : AddCommGroup (HermitianMat k ℂ) :=
  HermitianMat.instNormedAddCommGroupComplex.toAddCommGroup
@[reducible] local instance hModule {k : Type*} [Fintype k] : Module ℝ (HermitianMat k ℂ) :=
  HermitianMat.instNormedSpace.toModule


@[reducible] local instance pAdd {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] :
    AddCommGroup (E × F) := Prod.normedAddCommGroup.toAddCommGroup
@[reducible] local instance pTop {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] :
    TopologicalSpace (E × F) := Prod.normedAddCommGroup.toUniformSpace.toTopologicalSpace
@[reducible] local instance pModule {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F] : Module ℝ (E × F) := Prod.normedSpace.toModule


@[reducible] local instance matrixHMul {a b c : Type*} [Fintype b] :
    HMul (Matrix a b ℂ) (Matrix b c ℂ) (Matrix a c ℂ) :=
  Matrix.instHMulOfFintypeOfMulOfAddCommMonoid



variable {r s : Type*} [Fintype r] [Fintype s] [DecidableEq r] [DecidableEq s]

theorem outer_zero : outer (0 : r → ℂ) = 0 := by
  apply HermitianMat.ext
  ext i j
  change (0 : ℂ)*star (0 : ℂ) = 0
  simp

theorem outer_sum_trace (u : r → ℂ) (v : s → ℂ) :
    (outer (Sum.elim u v)).mat.trace.re = vecMass u+vecMass v := by
  rw [outer_trace_re]
  simp [vecMass,Fintype.sum_sum_type]

/-- An arbitrary nonzero two-block vector has exactly the scalar dual value at its two masses. -/
theorem value_outer_eq (u : r → ℂ) (v : s → ℂ) (hu : 0 < vecMass u) (hv : 0 < vecMass v)
    {lambda₀ lambda₁ : ℝ} (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) :
    value (outer (Sum.elim u v)) lambda₀ lambda₁ = value (rankOne (vecMass u) (vecMass v)) lambda₀ lambda₁ := by
  rw [← outer_embed_rankOne u v hu hv]
  exact value_embed (normalizedColumn u) (normalizedColumn v)
    (normalizedColumn_isometry u hu) (normalizedColumn_isometry v hv) (rankOne_posSemidef _ _) hl₀ hl₁

/-- The equality includes zero atoms; a fixed positive mass ratio fixes the entire scalar dual value. -/
theorem value_outer_ratio_eq (u : r → ℂ) (v : s → ℂ) {x z lambda₀ lambda₁ : ℝ}
    (hx : 0 < x) (hz : 0 < z) (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0)
    (hr : z*vecMass u = x*vecMass v) :
    value (outer (Sum.elim u v)) lambda₀ lambda₁ = vecMass u/x*value (rankOne x z) lambda₀ lambda₁ := by
  by_cases he : vecMass u = 0
  · have hv : vecMass v = 0 := by rw [he,mul_zero] at hr; exact (mul_eq_zero.mp hr.symm).resolve_left hx.ne'
    have hu0 := (vecMass_zero_iff u).mp he
    have hv0 := (vecMass_zero_iff v).mp hv
    have hzero : Sum.elim u v = 0 := by rw [hu0,hv0]; funext i; cases i <;> rfl
    rw [hzero,outer_zero,value_zero hl₀ hl₁,he,zero_div,zero_mul]
  · have hu : 0 < vecMass u := lt_of_le_of_ne (vecMass_nonneg u) (Ne.symm he)
    have hv : 0 < vecMass v := by nlinarith [vecMass_nonneg v]
    let c := vecMass u/x
    have hc : 0 < c := div_pos hu hx
    have hcX : c*x = vecMass u := div_mul_cancel₀ _ hx.ne'
    have hcZ : c*z = vecMass v := by dsimp [c]; field_simp; nlinarith [hr]
    change value (outer (Sum.elim u v)) lambda₀ lambda₁ = c*value (rankOne x z) lambda₀ lambda₁
    rw [value_outer_eq u v hu hv hl₀ hl₁,← hcX,← hcZ,rankOne_smul hc.le hx.le hz.le,
      value_smul hc.le (rankOne_posSemidef x z) hl₀ hl₁]

/-- A balanced vector attains the trace-proportional lower bound used by the sign-frame reduction. -/
theorem balanced_outer_value (v : r ⊕ s → ℂ) {x z lambda₀ lambda₁ : ℝ}
    (hx : 0 < x) (hz : 0 < z) (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0)
    (hr : z*(pinchLeft (outer v)).mat.trace.re = x*(pinchRight (outer v)).mat.trace.re) :
    value (rankOne x z) lambda₀ lambda₁/(x+z)*(outer v).mat.trace.re = value (outer v) lambda₀ lambda₁ := by
  let u := v ∘ Sum.inl
  let w := v ∘ Sum.inr
  have he : Sum.elim u w = v := by funext i; cases i <;> rfl
  rw [← he] at hr ⊢
  rw [pinchLeft_outer,pinchRight_outer,outer_trace_re,outer_trace_re] at hr
  rw [outer_sum_trace,value_outer_ratio_eq u w hx hz hl₀ hl₁ hr]
  have ht : vecMass u+vecMass w = (vecMass u/x)*(x+z) := by field_simp; nlinarith [hr]
  rw [ht]
  field_simp [(add_pos hx hz).ne'] <;> ring

end QubitAdditivity.BetaBalancedValue
