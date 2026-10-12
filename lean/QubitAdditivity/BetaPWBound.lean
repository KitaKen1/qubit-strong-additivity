import QubitAdditivity.BetaBarrier
import QubitAdditivity.BetaEndpoints

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix
open scoped Matrix ComplexOrder MatrixOrder

namespace QubitAdditivity.BetaPWBound
open BetaOperators BetaPowers BetaBridge BetaBlocks BetaStrict BetaEndpoints
variable {r s : Type*} [Fintype r] [Fintype s] [DecidableEq r] [DecidableEq s]
local notation "Vβ" => blockInclusion (r := r) (s := s)

/-- PW from a positive input gap and logarithmic stationarity. Neither D_s
positivity nor the PW comparison is an independent premise. -/
theorem pw_of_stationarity {T : Matrix (r ⊕ s) (r ⊕ s) ℂ}
    {A : Matrix r r ℂ} {B : Matrix s s ℂ}
    (hT : T.PosDef) (hA : A.PosDef) (hB : B.PosDef)
    (hgap : (T - Matrix.fromBlocks A 0 0 B).PosDef)
    (lambda₀ lambda₁ : ℂ)
    (h₀ : logarithm A = (logarithm T).submatrix Sum.inl Sum.inl + lambda₀ • 1)
    (h₁ : logarithm B = (logarithm T).submatrix Sum.inr Sum.inr + lambda₁ • 1) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, Vβᴴ * pw T t * Vβ ≤ blockPW A B t +
      blockPW (T.submatrix Sum.inl Sum.inl - A) (T.submatrix Sum.inr Sum.inr - B) t := by
  let P₀ := T.submatrix Sum.inl Sum.inl - A
  let P₁ := T.submatrix Sum.inr Sum.inr - B
  have hP := gap_blocks_posDef hgap
  have hQ : ∀ u, (blockPW P₀ P₁ u).PosDef :=
    fun u => diagonal_posDef (pw_posDef hP.1 u) (pw_posDef hP.2 u)
  have hK : (blockGenerator (logarithm P₀) (logarithm P₁)).IsHermitian :=
    (generator_isHermitian (logarithm_isHermitian P₀)).fromBlocks (by simp)
      (generator_isHermitian (logarithm_isHermitian P₁))
  have hzero : curve T A B 0 ≤ blockPW P₀ P₁ 0 := by
    rw [curve_zero hT.1 hA.1 hB.1, blockPW_zero hP.1.1 hP.2.1]
  have hone : curve T A B 1 ≤ blockPW P₀ P₁ 1 := by
    rw [curve_one hT.1 hA.1 hB.1, blockPW_one hP.1.1 hP.2.1]
  have hh := BetaBarrier.le_of_exponential (curve T A B) (curveFirst T A B)
    (curveSecond T A B) (blockPW P₀ P₁) (blockGenerator (logarithm P₀) (logarithm P₁))
    (hasDerivAt_curve hT hA hB) (hasDerivAt_curveFirst hT hA hB)
    (hasDerivAt_blockPW hP.1 hP.2)
    (fun _ ht => (curve_posDef_of_positive_gap hT hA hB hgap ht).1) hQ hK
    (fun u => (blockPW_generator_commute P₀ P₁ u).eq.symm)
    (fun _ ht => stationaryGram_of_positive_gap hT hA hB hgap lambda₀ lambda₁
      ⟨ht.1.le,ht.2.le⟩ h₀ h₁) hzero hone
  intro t ht
  have hi := hh t ht
  change Vβᴴ * pw T t * Vβ - blockPW A B t ≤ blockPW P₀ P₁ t at hi
  simpa only [add_comm] using (sub_le_iff_le_add).mp hi

/-- The formerly assumed PW premise is discharged before integrating to KM. -/
theorem km_of_stationarity {T : Matrix (r ⊕ s) (r ⊕ s) ℂ}
    {A : Matrix r r ℂ} {B : Matrix s s ℂ}
    (hT : T.PosDef) (hA : A.PosDef) (hB : B.PosDef)
    (hgap : (T - Matrix.fromBlocks A 0 0 B).PosDef)
    (lambda₀ lambda₁ : ℂ)
    (h₀ : logarithm A = (logarithm T).submatrix Sum.inl Sum.inl + lambda₀ • 1)
    (h₁ : logarithm B = (logarithm T).submatrix Sum.inr Sum.inr + lambda₁ • 1) :
    Vβᴴ * km T * Vβ ≤ blockKM A B +
      blockKM (T.submatrix Sum.inl Sum.inl - A) (T.submatrix Sum.inr Sum.inr - B) :=
  km_of_pw hT hA hB (gap_blocks_posDef hgap).1 (gap_blocks_posDef hgap).2
    (pw_of_stationarity hT hA hB hgap lambda₀ lambda₁ h₀ h₁)

end QubitAdditivity.BetaPWBound
