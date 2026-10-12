import QubitAdditivity.BetaPWBound
import QubitAdditivity.BetaComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Elementwise

namespace QubitAdditivity.BetaKM
open BetaOperators BetaPowers BetaBridge BetaBlocks BetaStrict BetaComparison

local instance matrixNormedAddCommGroup {i j : Type*} [Fintype i] [Fintype j] :
    NormedAddCommGroup (Matrix i j ℂ) :=
  inferInstanceAs (NormedAddCommGroup (i → j → ℂ))
local instance matrixNormedSpace {i j : Type*} [Fintype i] [Fintype j] :
    NormedSpace ℝ (Matrix i j ℂ) :=
  inferInstanceAs (NormedSpace ℝ (i → j → ℂ))
local instance matrixENormedAddMonoid {i j : Type*} [Fintype i] [Fintype j] :
    ENormedAddMonoid (Matrix i j ℂ) :=
  inferInstanceAs (ENormedAddMonoid (i → j → ℂ))

variable {n : Type*} [Fintype n] [DecidableEq n]

def quadraticLM (v : n → ℂ) : Matrix n n ℂ →ₗ[ℝ] ℝ where
  toFun A := quadratic A v
  map_add' A B := by simp [quadratic, pairing, Matrix.add_mulVec, dotProduct_add]
  map_smul' c A := by simp [quadratic_smul, smul_eq_mul]

def quadraticCLM (v : n → ℂ) : Matrix n n ℂ →L[ℝ] ℝ :=
  (quadraticLM v).toContinuousLinearMap

@[simp] theorem quadraticCLM_apply (v : n → ℂ) (A : Matrix n n ℂ) :
    quadraticCLM v A = quadratic A v := rfl

theorem quadratic_integral {f : ℝ → Matrix n n ℂ}
    (hf : IntervalIntegrable f MeasureTheory.volume 0 1) (v : n → ℂ) :
    quadratic (∫ t in (0 : ℝ)..1, f t) v = ∫ t in (0 : ℝ)..1, quadratic (f t) v := by
  convert! ((quadraticCLM v).intervalIntegral_comp_comm hf).symm using 1
  all_goals rfl

/-- A continuous positive definite matrix curve has a strictly positive
integral. This includes empty index types and uses scalar quadratic forms. -/
theorem integral_posDef {f : ℝ → Matrix n n ℂ} (hf : Continuous f)
    (hp : ∀ t ∈ Set.Icc (0 : ℝ) 1, (f t).PosDef) :
    (∫ t in (0 : ℝ)..1, f t).PosDef := by
  have hfi : IntervalIntegrable f MeasureTheory.volume 0 1 := hf.intervalIntegrable 0 1
  have hnonneg : 0 ≤ ∫ t in (0 : ℝ)..1, f t := by
    have hh := intervalIntegral_mono_on
      (show IntervalIntegrable (fun _ : ℝ => (0 : Matrix n n ℂ)) MeasureTheory.volume 0 1 from
        continuous_const.intervalIntegrable 0 1) hfi
      (fun t ht => (hp t ht).posSemidef.nonneg)
    simpa using hh
  have hH := (Matrix.LE.le.posSemidef hnonneg).1
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hH
  intro v hv
  apply Complex.pos_iff.mpr
  refine ⟨?_, (hH.im_star_dotProduct_mulVec_self v).symm⟩
  change 0 < quadratic (∫ t in (0 : ℝ)..1, f t) v
  rw [quadratic_integral hfi]
  have hc : Continuous (fun t => quadratic (f t) v) := by
    convert! (quadraticCLM v).continuous.comp hf using 1
  exact intervalIntegral.integral_pos zero_lt_one hc.continuousOn
    (fun t ht => (quadratic_pos (hp t ⟨ht.1.le,ht.2⟩) hv).le)
    ⟨0, ⟨le_rfl, zero_le_one⟩, quadratic_pos (hp 0 ⟨le_rfl,zero_le_one⟩) hv⟩

/-- Strict positive definiteness of the actual Kubo–Mori operator. -/
theorem km_posDef {A : Matrix n n ℂ} (hA : A.PosDef) : (km A).PosDef :=
  integral_posDef (continuous_pw hA) (fun t _ => pw_posDef hA t)

section blocks
variable {r s : Type*} [Fintype r] [Fintype s] [DecidableEq r] [DecidableEq s]
local notation "Vβ" => blockInclusion (r := r) (s := s)

def residual (T : Matrix (r ⊕ s) (r ⊕ s) ℂ) (A : Matrix r r ℂ) (B : Matrix s s ℂ) :=
  km T - Vβ * blockKM A B * Vβᴴ

theorem blockKM_posDef {A : Matrix r r ℂ} {B : Matrix s s ℂ}
    (hA : A.PosDef) (hB : B.PosDef) : (blockKM A B).PosDef :=
  diagonal_posDef (km_posDef hA) (km_posDef hB)

theorem continuous_pw_residual {T : Matrix (r ⊕ s) (r ⊕ s) ℂ}
    {A : Matrix r r ℂ} {B : Matrix s s ℂ}
    (hT : T.PosDef) (hA : A.PosDef) (hB : B.PosDef) :
    Continuous (fun t => pw T t - Vβ * blockPW A B t * Vβᴴ) := by
  have hq := continuous_pw hT
  have hb := continuous_blockPW hA hB
  fun_prop

set_option maxHeartbeats 800000 in
theorem residual_eq_integral {T : Matrix (r ⊕ s) (r ⊕ s) ℂ}
    {A : Matrix r r ℂ} {B : Matrix s s ℂ}
    (hT : T.PosDef) (hA : A.PosDef) (hB : B.PosDef) :
    residual T A B = ∫ t in (0 : ℝ)..1, pw T t - Vβ * blockPW A B t * Vβᴴ := by
  have he := (compressionCLM Vβᴴ).intervalIntegral_comp_comm
    (intervalIntegrable_blockPW hA hB)
  have he' : (∫ t in (0 : ℝ)..1, Vβ * blockPW A B t * Vβᴴ) = Vβ * blockKM A B * Vβᴴ := by
    rw [← blockKM_eq_integral hA hB] at he
    change (∫ t in (0 : ℝ)..1, Vβᴴᴴ * blockPW A B t * Vβᴴ) =
      Vβᴴᴴ * blockKM A B * Vβᴴ at he
    simpa only [conjTranspose_conjTranspose] using he
  have hc : Continuous (fun t => Vβ * blockPW A B t * Vβᴴ) := by
    have hb := continuous_blockPW hA hB
    fun_prop
  rw [intervalIntegral.integral_sub (intervalIntegrable_pw hT) (hc.intervalIntegrable 0 1), he']
  rfl

/-- The positive input gap proves the integrated residual is strictly positive.
No stationarity, KM premise, or independently assumed residual is needed. -/
theorem residual_posDef {T : Matrix (r ⊕ s) (r ⊕ s) ℂ}
    {A : Matrix r r ℂ} {B : Matrix s s ℂ}
    (hT : T.PosDef) (hA : A.PosDef) (hB : B.PosDef)
    (hgap : (T - Matrix.fromBlocks A 0 0 B).PosDef) : (residual T A B).PosDef := by
  rw [residual_eq_integral hT hA hB]
  exact integral_posDef (continuous_pw_residual hT hA hB)
    (fun _ ht => BetaStrict.residual_posDef hT hA hB hgap ht)

/-- Compression subtracts exactly the block KM operator because V is an isometry. -/
theorem residual_compression (T : Matrix (r ⊕ s) (r ⊕ s) ℂ)
    (A : Matrix r r ℂ) (B : Matrix s s ℂ) :
    Vβᴴ * residual T A B * Vβ = Vβᴴ * km T * Vβ - blockKM A B := by
  simp only [residual, Matrix.mul_sub, Matrix.sub_mul]
  congr 1
  calc
    _ = (Vβᴴ * Vβ) * blockKM A B * (Vβᴴ * Vβ) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [blockInclusion_isometry]; simp

end blocks
end QubitAdditivity.BetaKM
