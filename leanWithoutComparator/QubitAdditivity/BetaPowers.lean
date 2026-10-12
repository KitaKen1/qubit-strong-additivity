import QubitAdditivity.BetaOperators
import QubitAdditivity.BetaOrder
import QubitAdditivity.Imported.MatrixCalculus
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.Elementwise

namespace QubitAdditivity.BetaPowers
open BetaOperators
variable {n : Type*} [Fintype n] [DecidableEq n]

-- The entrywise matrix topology is the Pi topology. Expose the Pi ENorm instance
-- explicitly because the matrix alias otherwise blocks instance synthesis.
local instance matrixENormedAddMonoid {i j : Type*} [Fintype i] [Fintype j] :
    ENormedAddMonoid (Matrix i j ℂ) :=
  inferInstanceAs (ENormedAddMonoid (i → j → ℂ))

/-- The real spectral power, including negative exponents on positive definite matrices. -/
def power (A : Matrix n n ℂ) (t : ℝ) : Matrix n n ℂ :=
  cfc (fun x : ℝ => x ^ t) A

def logarithm (A : Matrix n n ℂ) : Matrix n n ℂ := cfc Real.log A

/-- The PW curve in the matrix-unit coordinates fixed in BetaOperators. -/
def pw (A : Matrix n n ℂ) (t : ℝ) : Matrix (n × n) (n × n) ℂ :=
  left (power A t) * right (power A (1 - t))

def km (A : Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ :=
  ∫ t in (0 : ℝ)..1, pw A t

theorem continuousOn_spectrum (A : Matrix n n ℂ) (f : ℝ → ℝ) :
    ContinuousOn f (spectrum ℝ A) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_of_discreteTopology

theorem cfc_commute (A : Matrix n n ℂ) (f g : ℝ → ℝ) :
    Commute (cfc f A) (cfc g A) :=
  ((Commute.refl A).cfc_real g).symm.cfc_real f

theorem power_logarithm_commute (A : Matrix n n ℂ) (t : ℝ) :
    Commute (power A t) (logarithm A) := cfc_commute A _ _

theorem power_isHermitian (A : Matrix n n ℂ) (t : ℝ) :
    (power A t).IsHermitian := cfc_predicate _ A

theorem logarithm_isHermitian (A : Matrix n n ℂ) :
    (logarithm A).IsHermitian := cfc_predicate _ A

theorem power_zero {A : Matrix n n ℂ} (hA : A.IsHermitian) : power A 0 = 1 := by
  simp only [power, Real.rpow_zero]
  exact cfc_const_one ℝ A hA

theorem power_one {A : Matrix n n ℂ} (hA : A.IsHermitian) : power A 1 = A := by
  simp only [power, Real.rpow_one]
  exact cfc_id' ℝ A hA

theorem pw_eq_kronecker (A : Matrix n n ℂ) (t : ℝ) :
    pw A t = power A t ⊗ₖ (power A (1 - t))ᵀ := by
  simp only [pw, left, right, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

theorem pw_zero {A : Matrix n n ℂ} (hA : A.IsHermitian) : pw A 0 = right A := by
  simp [pw, power_zero hA, power_one hA, left]

theorem pw_one {A : Matrix n n ℂ} (hA : A.IsHermitian) : pw A 1 = left A := by
  simp [pw, power_zero hA, power_one hA, right]

theorem pw_generator_commute (A : Matrix n n ℂ) (t : ℝ) :
    Commute (pw A t) (generator (logarithm A)) := by
  have hl : Commute (left (power A t)) (left (logarithm A)) := by
    rw [commute_iff_eq, ← left_mul, ← left_mul]
    exact congrArg left (power_logarithm_commute A t).eq
  have hr : Commute (right (power A (1-t))) (right (logarithm A)) := by
    rw [commute_iff_eq, ← right_mul, ← right_mul]
    exact congrArg right (power_logarithm_commute A (1-t)).eq.symm
  exact (hl.mul_left (show Commute (right (power A (1-t))) (left (logarithm A))
    from (left_right_commute _ _).symm)).sub_right
    ((show Commute (left (power A t)) (right (logarithm A))
      from left_right_commute _ _).mul_left hr)

/-- Parameter differentiation of the CFC on a fixed finite spectrum. -/
theorem hasDerivAt_cfc_parameter {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (f : ℝ → ℝ → ℝ) (g : ℝ → ℝ) (t : ℝ)
    (hf : ∀ i, HasDerivAt (fun s => f s (hA.eigenvalues i)) (g (hA.eigenvalues i)) t) :
    HasDerivAt (fun s => cfc (f s) A) (cfc g A) t := by
  have hd : HasDerivAt
      (fun s => Matrix.diagonal (fun i => (f s (hA.eigenvalues i) : ℂ)))
      (Matrix.diagonal (fun i => (g (hA.eigenvalues i) : ℂ))) t := by
    apply hasDerivAt_pi.2
    intro i
    apply hasDerivAt_pi.2
    intro j
    by_cases hij : i = j
    · subst j
      simpa only [Matrix.diagonal_apply_eq, Function.comp_def, Complex.ofRealCLM_apply] using
        Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (hf i)
    · simpa only [Matrix.diagonal_apply_ne _ hij] using hasDerivAt_const t (0 : ℂ)
  have hh := OpenAICalculus.hasDerivAt_matrix_mul
    (OpenAICalculus.hasDerivAt_matrix_mul
      (hasDerivAt_const t (hA.eigenvectorUnitary : Matrix n n ℂ)) hd)
    (hasDerivAt_const t (star hA.eigenvectorUnitary : Matrix n n ℂ))
  convert! hh using 1 <;>
    simp only [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
      Function.comp_def, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero]
  all_goals rfl

theorem power_posDef {A : Matrix n n ℂ} (hA : A.PosDef) (t : ℝ) :
    (power A t).PosDef := by
  apply IsStrictlyPositive.posDef
  apply (cfc_isStrictlyPositive_iff _ A (continuousOn_spectrum _ _) hA.1).mpr
  rw [hA.1.spectrum_real_eq_range_eigenvalues]
  rintro _ ⟨i, rfl⟩
  exact Real.rpow_pos_of_pos (hA.eigenvalues_pos i) t

theorem hasDerivAt_power {A : Matrix n n ℂ} (hA : A.PosDef) (t : ℝ) :
    HasDerivAt (power A) (power A t * logarithm A) t := by
  have hh := hasDerivAt_cfc_parameter hA.1 (fun s x => x ^ s)
    (fun x => x ^ t * Real.log x) t
    (fun i => (Real.hasStrictDerivAt_const_rpow (hA.eigenvalues_pos i) t).hasDerivAt)
  change HasDerivAt (fun s => cfc (fun x : ℝ => x ^ s) A)
    (cfc (fun x : ℝ => x ^ t) A * cfc Real.log A) t
  rw [← cfc_mul _ _ A (continuousOn_spectrum _ _) (continuousOn_spectrum _ _)]
  exact hh

theorem continuous_power {A : Matrix n n ℂ} (hA : A.PosDef) : Continuous (power A) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_power hA t).continuousAt

theorem pw_posDef {A : Matrix n n ℂ} (hA : A.PosDef) (t : ℝ) :
    (pw A t).PosDef := by
  rw [pw_eq_kronecker]
  exact (power_posDef hA t).kronecker (power_posDef hA (1-t)).transpose

open scoped Matrix.Norms.L2Operator in
theorem power_mono {A B : Matrix n n ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) (hAB : A ≤ B) : power A t ≤ power B t := by
  unfold power
  rw [← CFC.rpow_eq_cfc_real hA.nonneg, ← CFC.rpow_eq_cfc_real hB.nonneg]
  exact CFC.rpow_le_rpow ht hAB

/-- Kronecker product differentiation in the fixed entrywise topology. -/
theorem hasDerivAt_kronecker {A B : ℝ → Matrix n n ℂ}
    {H K : Matrix n n ℂ} {t : ℝ} (hA : HasDerivAt A H t) (hB : HasDerivAt B K t) :
    HasDerivAt (fun s => A s ⊗ₖ B s) (H ⊗ₖ B t + A t ⊗ₖ K) t := by
  apply hasDerivAt_pi.2
  intro i
  apply hasDerivAt_pi.2
  intro j
  exact (hasDerivAt_pi.1 (hasDerivAt_pi.1 hA i.1) j.1).mul
    (hasDerivAt_pi.1 (hasDerivAt_pi.1 hB i.2) j.2)

theorem hasDerivAt_transpose {A : ℝ → Matrix n n ℂ}
    {H : Matrix n n ℂ} {t : ℝ} (hA : HasDerivAt A H t) :
    HasDerivAt (fun s => (A s)ᵀ) Hᵀ t := by
  apply hasDerivAt_pi.2
  intro i
  apply hasDerivAt_pi.2
  intro j
  exact hasDerivAt_pi.1 (hasDerivAt_pi.1 hA j) i

theorem hasDerivAt_pw {A : Matrix n n ℂ} (hA : A.PosDef) (t : ℝ) :
    HasDerivAt (pw A) (generator (logarithm A) * pw A t) t := by
  have hs := (hasDerivAt_power hA (1-t)).scomp t
    ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t))
  have hh := hasDerivAt_kronecker (hasDerivAt_power hA t) (hasDerivAt_transpose hs)
  simp only [zero_sub, neg_smul, one_smul, Matrix.transpose_neg] at hh
  convert! hh using 1
  · exact funext fun s => pw_eq_kronecker A s
  · rw [generator, pw_eq_kronecker, Matrix.sub_mul]
    simp only [left, right, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
    rw [← (power_logarithm_commute A t).eq]
    ext i j
    simp only [kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply,
      Matrix.transpose_apply, Matrix.neg_apply, Matrix.transpose_mul, Function.comp_apply]
    ring

theorem hasDerivAt_pw_first {A : Matrix n n ℂ} (hA : A.PosDef) (t : ℝ) :
    HasDerivAt (fun s => generator (logarithm A) * pw A s)
      (generator (logarithm A) * generator (logarithm A) * pw A t) t := by
  simpa only [Matrix.zero_mul, zero_add, Matrix.mul_assoc] using
    OpenAICalculus.hasDerivAt_matrix_mul
      (hasDerivAt_const t (generator (logarithm A))) (hasDerivAt_pw hA t)

theorem continuous_pw {A : Matrix n n ℂ} (hA : A.PosDef) : Continuous (pw A) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_pw hA t).continuousAt

theorem intervalIntegrable_pw {A : Matrix n n ℂ} (hA : A.PosDef) :
    IntervalIntegrable (pw A) MeasureTheory.volume 0 1 :=
  (continuous_pw hA).intervalIntegrable 0 1

theorem pw_mono {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) (hAB : A ≤ B) : pw A t ≤ pw B t := by
  have ht' : 1-t ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hl := Matrix.le_iff.mp (power_mono hA.posSemidef hB.posSemidef ht hAB)
  have hr := (Matrix.le_iff.mp (power_mono hA.posSemidef hB.posSemidef ht' hAB)).transpose
  have hp := (hl.kronecker (power_posDef hB (1-t)).posSemidef.transpose).add
    ((power_posDef hA t).posSemidef.kronecker hr)
  apply Matrix.le_iff.mpr
  convert hp using 1
  ext i j
  simp only [pw_eq_kronecker, kroneckerMap_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.transpose_apply]
  ring

end QubitAdditivity.BetaPowers
