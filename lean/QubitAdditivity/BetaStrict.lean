import QubitAdditivity.BetaBlocks
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix
open scoped Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.Elementwise

namespace QubitAdditivity.BetaStrict
open BetaOperators BetaPowers BetaBridge BetaBlocks
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A positive definite gap remains positive after adding a nonnegative gap. -/
theorem posDef_of_le {A B : Matrix n n ℂ} (hA : A.PosDef) (hAB : A ≤ B) : B.PosDef :=
by
  have hp := hA.add_posSemidef (Matrix.le_iff.mp hAB)
  convert hp using 1
  abel

/-- Strict Loewner monotonicity of a spectral power. The exponent zero is excluded. -/
theorem power_sub_posDef {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (hgap : (A - B).PosDef) {t : ℝ} (ht : 0 < t) (ht₁ : t ≤ 1) :
    (power A t - power B t).PosDef := by
  cases isEmpty_or_nonempty n with
  | inl hn =>
    letI := hn
    exact Matrix.PosDef.of_dotProduct_mulVec_pos
      ((power_isHermitian A t).sub (power_isHermitian B t))
      (fun _ hx => (hx (Subsingleton.elim _ _)).elim)
  | inr hn =>
    letI := hn
    obtain ⟨d, hd, hdl⟩ := (CFC.exists_pos_algebraMap_le_iff (A - B) hgap.1).mpr
      (by
        rw [hgap.1.spectrum_real_eq_range_eigenvalues]
        rintro _ ⟨i, rfl⟩
        exact hgap.eigenvalues_pos i)
    let C := B + algebraMap ℝ (Matrix n n ℂ) d
    have hBC : B ≤ C := by
      have hh : (algebraMap ℝ (Matrix n n ℂ) d).PosSemidef := by
        rw [Algebra.algebraMap_eq_smul_one]
        exact Matrix.PosSemidef.one.smul (α := ℝ) hd.le
      exact le_add_of_nonneg_right hh.nonneg
    have hC : C.PosDef := posDef_of_le hB hBC
    have hCA : C ≤ A := by
      dsimp [C]
      have hh := (le_sub_iff_add_le).mp hdl
      rwa [add_comm] at hh
    have he : power C t = cfc (fun x : ℝ => (x + d) ^ t) B := by
      have hh := cfc_comp' (fun x : ℝ => x ^ t) (fun x : ℝ => x + d) B
        (((Set.toFinite (spectrum ℝ B)).image (fun x : ℝ => x+d)).continuousOn _)
        (continuousOn_spectrum _ _) hB.1
      have hs : cfc (fun x : ℝ => x + d) B = B + algebraMap ℝ (Matrix n n ℂ) d := by
        calc
          _ = cfc id B + algebraMap ℝ (Matrix n n ℂ) d :=
            cfc_add_const d id B (continuousOn_spectrum _ _) hB.1
          _ = _ := congrArg (fun X => X + algebraMap ℝ (Matrix n n ℂ) d) (cfc_id' ℝ B hB.1)
      rw [hs] at hh
      exact hh.symm
    have hp : (power C t - power B t).PosDef := by
      rw [he, power, ← cfc_sub _ _ B (continuousOn_spectrum _ _) (continuousOn_spectrum _ _)]
      apply IsStrictlyPositive.posDef
      apply (cfc_isStrictlyPositive_iff _ B (continuousOn_spectrum _ _) hB.1).mpr
      rw [hB.1.spectrum_real_eq_range_eigenvalues]
      rintro _ ⟨i, rfl⟩
      exact sub_pos.mpr (Real.rpow_lt_rpow (hB.eigenvalues_pos i).le
        (lt_add_of_pos_right _ hd) ht)
    exact posDef_of_le hp (sub_le_sub_right
      (power_mono hC.posSemidef hA.posSemidef ⟨ht.le, ht₁⟩ hCA) _)

/-- Strict positivity for the full PW gap, including both endpoints. -/
theorem pw_sub_posDef {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (hgap : (A - B).PosDef) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    (pw A t - pw B t).PosDef := by
  by_cases hzero : t = 0
  · subst t
    rw [pw_zero hA.1, pw_zero hB.1]
    have hh : (right (A-B)).PosDef := Matrix.PosDef.one.kronecker hgap.transpose
    convert hh using 1
    ext i j
    simp [right, kroneckerMap_apply, mul_sub]
  by_cases hone : t = 1
  · subst t
    rw [pw_one hA.1, pw_one hB.1]
    have hh : (left (A-B)).PosDef := hgap.kronecker Matrix.PosDef.one
    convert hh using 1
    ext i j
    simp [left, kroneckerMap_apply, sub_mul]
  have hp := (power_sub_posDef hA hB hgap (lt_of_le_of_ne ht.1 (Ne.symm hzero)) ht.2).kronecker
    (power_posDef hA (1-t)).transpose
  have hq := (power_posDef hB t).posSemidef.kronecker
    (Matrix.le_iff.mp (power_mono hB.posSemidef hA.posSemidef
      (t := 1-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩ (sub_nonneg.mp hgap.posSemidef.nonneg))).transpose
  convert hp.add_posSemidef hq using 1
  ext i j
  simp only [pw_eq_kronecker, kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.transpose_apply]
  ring

section blocks
variable {r s : Type*} [Fintype r] [Fintype s] [DecidableEq r] [DecidableEq s]
local notation "Vβ" => blockInclusion (r := r) (s := s)

/-- The strict residual D_s is derived from the positive input gap, rather
than supplied as an independent premise. Both endpoints are included. -/
theorem residual_posDef {T : Matrix (r ⊕ s) (r ⊕ s) ℂ}
    {A : Matrix r r ℂ} {B : Matrix s s ℂ}
    (hT : T.PosDef) (hA : A.PosDef) (hB : B.PosDef)
    (hgap : (T - Matrix.fromBlocks A 0 0 B).PosDef)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    (pw T t - Vβ * blockPW A B t * Vβᴴ).PosDef := by
  have hW := diagonal_posDef hA hB
  have hp := pw_sub_posDef hT hW hgap ht
  have hq := pw_diagonal_residual_posSemidef hA hB t hW
  convert hp.add_posSemidef hq using 1
  abel

theorem curve_posDef_of_positive_gap {T : Matrix (r ⊕ s) (r ⊕ s) ℂ}
    {A : Matrix r r ℂ} {B : Matrix s s ℂ}
    (hT : T.PosDef) (hA : A.PosDef) (hB : B.PosDef)
    (hgap : (T - Matrix.fromBlocks A 0 0 B).PosDef)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) : (curve T A B t).PosDef :=
  curve_posDef_of_residual T A B t (residual_posDef hT hA hB hgap ht)

/-- The actual Gram no longer has an independent residual-positivity premise. -/
theorem stationaryGram_of_positive_gap {T : Matrix (r ⊕ s) (r ⊕ s) ℂ}
    {A : Matrix r r ℂ} {B : Matrix s s ℂ}
    (hT : T.PosDef) (hA : A.PosDef) (hB : B.PosDef)
    (hgap : (T - Matrix.fromBlocks A 0 0 B).PosDef)
    (lambda₀ lambda₁ : ℂ) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (h₀ : logarithm A = (logarithm T).submatrix Sum.inl Sum.inl + lambda₀ • 1)
    (h₁ : logarithm B = (logarithm T).submatrix Sum.inr Sum.inr + lambda₁ • 1) :
    (Matrix.fromBlocks (curve T A B t) (curveFirst T A B t)
      (curveFirst T A B t) (curveSecond T A B t)).PosSemidef :=
  stationaryGram_pw T A B lambda₀ lambda₁ t h₀ h₁ (residual_posDef hT hA hB hgap ht).posSemidef

/-- Positive gap and stationarity supply the actual Riccati inequality. -/
theorem curve_riccati_of_positive_gap {T : Matrix (r ⊕ s) (r ⊕ s) ℂ}
    {A : Matrix r r ℂ} {B : Matrix s s ℂ}
    (hT : T.PosDef) (hA : A.PosDef) (hB : B.PosDef)
    (hgap : (T - Matrix.fromBlocks A 0 0 B).PosDef)
    (lambda₀ lambda₁ : ℂ) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (h₀ : logarithm A = (logarithm T).submatrix Sum.inl Sum.inl + lambda₀ • 1)
    (h₁ : logarithm B = (logarithm T).submatrix Sum.inr Sum.inr + lambda₁ • 1) :
    (curveSecond T A B t - curveFirst T A B t * (curve T A B t)⁻¹ *
      curveFirst T A B t).PosSemidef :=
  curve_riccati_of_stationarity hT hA hB lambda₀ lambda₁ t h₀ h₁
    (residual_posDef hT hA hB hgap ht)

end blocks
end QubitAdditivity.BetaStrict
