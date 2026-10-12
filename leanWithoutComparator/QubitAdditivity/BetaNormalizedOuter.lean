import QubitAdditivity.BetaBlockIsometry
import QubitAdditivity.BetaScalarMinimum
import QubitAdditivity.Partner

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius

namespace QubitAdditivity.BetaNormalizedOuter
open BetaDual BetaEntropy BetaDualValue BetaIsometryEntropy BetaBlockIsometry BetaGramSplit BetaScalarMinimum

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

theorem vecMass_star_dotProduct (u : r → ℂ) : star u ⬝ᵥ u = (vecMass u : ℂ) := by
  simp [vecMass,dotProduct,Pi.star_apply,← RCLike.normSq_eq_conj_mul_self]

theorem vecMass_zero_iff (u : r → ℂ) : vecMass u = 0 ↔ u = 0 := by
  constructor
  · intro h
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg (u i))).mp h
    funext i
    exact Complex.normSq_eq_zero.mp (hi i (Finset.mem_univ i))
  · intro h
    rw [h]
    simp [vecMass]

theorem outer_trace_re (u : r → ℂ) : (outer u).mat.trace.re = vecMass u := by
  rw [outer_trace,vecMass_star_dotProduct,Complex.ofReal_re]

def normalizedColumn (u : r → ℂ) : Matrix r (Fin 1) ℂ := fun i _ =>
  ((Real.sqrt (vecMass u))⁻¹ : ℝ) • u i

theorem normalizedColumn_isometry (u : r → ℂ) (hu : 0 < vecMass u) :
    (normalizedColumn u)ᴴ*normalizedColumn u = 1 := by
  have hs : Real.sqrt (vecMass u) ≠ 0 := (Real.sqrt_pos.mpr hu).ne'
  have hi := vecMass_star_dotProduct u
  ext i j
  have he (i : Fin 1) : i = 0 := Subsingleton.elim _ _
  rw [he i,he j]
  change (∑ k, star (((Real.sqrt (vecMass u))⁻¹ : ℝ) • u k)*
    (((Real.sqrt (vecMass u))⁻¹ : ℝ) • u k)) = 1
  simp only [star_smul,star_trivial,Complex.real_smul]
  calc
    _ = ((Real.sqrt (vecMass u))⁻¹ : ℂ)*((Real.sqrt (vecMass u))⁻¹ : ℂ)*(star u ⬝ᵥ u) := by
      simp only [dotProduct,Pi.star_apply,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [star_mul,star_inv₀,Complex.star_def,Complex.conj_ofReal,Complex.ofReal_inv]
      ring
    _ = 1 := by
      have hsc : (Real.sqrt (vecMass u) : ℂ) ≠ 0 := by exact_mod_cast hs
      have hsq : (Real.sqrt (vecMass u) : ℂ)*(Real.sqrt (vecMass u) : ℂ) = (vecMass u : ℂ) := by
        exact_mod_cast Real.mul_self_sqrt hu.le
      rw [hi,← hsq]
      field_simp [hsc]

theorem normalizedColumn_mul_sqrt (u : r → ℂ) (hu : 0 < vecMass u) :
    normalizedColumn u *ᵥ (fun _ : Fin 1 => (Real.sqrt (vecMass u) : ℂ)) = u := by
  have hs : (Real.sqrt (vecMass u) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hu).ne'
  funext i
  simp [normalizedColumn,Matrix.mulVec,dotProduct,Fin.sum_univ_one,Complex.real_smul,Complex.ofReal_inv,
    mul_comm,mul_left_comm,mul_assoc,hs]

theorem outer_conj (v : r → ℂ) (R : Matrix s r ℂ) : (outer v).conj R = outer (R *ᵥ v) := by
  apply HermitianMat.ext
  change R*Matrix.vecMulVec v (star v)*Rᴴ = Matrix.vecMulVec (R *ᵥ v) (star (R *ᵥ v))
  rw [Matrix.mul_vecMulVec,Matrix.vecMulVec_mul,star_mulVec]

theorem outer_embed_rankOne (u : r → ℂ) (v : s → ℂ) (hu : 0 < vecMass u) (hv : 0 < vecMass v) :
    (rankOne (vecMass u) (vecMass v)).conj (blockEmbedding (normalizedColumn u) (normalizedColumn v)) =
      outer (Sum.elim u v) := by
  rw [rankOne,outer_conj]
  congr 1
  simp only [blockEmbedding,Matrix.fromBlocks_mulVec,Function.comp_def,Sum.elim_inl,Sum.elim_inr,
    Matrix.zero_mulVec,add_zero,zero_add,normalizedColumn_mul_sqrt u hu,normalizedColumn_mul_sqrt v hv]

theorem rankOne_smul {c x z : ℝ} (hc : 0 ≤ c) (hx : 0 ≤ x) (hz : 0 ≤ z) :
    rankOne (c*x) (c*z) = c • rankOne x z := by
  have he : Sum.elim (fun _ : Fin 1 => (Real.sqrt (c*x) : ℂ)) (fun _ : Fin 1 => (Real.sqrt (c*z) : ℂ)) =
      Real.sqrt c • Sum.elim (fun _ : Fin 1 => (Real.sqrt x : ℂ)) (fun _ : Fin 1 => (Real.sqrt z : ℂ)) := by
    funext i
    cases i <;> simp [Real.sqrt_mul hc,Complex.real_smul,Complex.ofReal_mul]
  unfold rankOne
  rw [he,outer_sqrt_smul hc]

theorem pinchLeft_outer (u : r → ℂ) (v : s → ℂ) : pinchLeft (outer (Sum.elim u v)) = outer u := by
  apply HermitianMat.ext
  rfl

theorem pinchRight_outer (u : r → ℂ) (v : s → ℂ) : pinchRight (outer (Sum.elim u v)) = outer v := by
  apply HermitianMat.ext
  rfl

end QubitAdditivity.BetaNormalizedOuter
