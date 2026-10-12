/-
Derived from openai/math, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Apache-2.0; see vendor/openai/LICENSE.
Both generic logarithmic determinant derivative proof bodies are unchanged.
-/
import QubitAdditivity.Imported.MatrixCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option autoImplicit false
noncomputable section
universe u_1
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
namespace QubitAdditivity.OpenAICalculus
variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

/-- Logarithmic norm differentiation, without choosing a complex logarithm branch. -/
theorem hasDerivAt_log_norm_of_mul {z : ℝ → ℂ} {w : ℂ} {t : ℝ}
    (hz : HasDerivAt z (z t * w) t) (h0 : z t ≠ 0) :
    HasDerivAt (fun s ↦ Real.log ‖z s‖) w.re t := by
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hz
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hz
  change HasDerivAt (fun s ↦ (z s).re) (z t * w).re t at hr
  change HasDerivAt (fun s ↦ (z s).im) (z t * w).im t at hi
  have hq : HasDerivAt (fun s ↦ Complex.normSq (z s))
      (2 * Complex.normSq (z t) * w.re) t := by
    convert! (hr.mul hr).add (hi.mul hi) using 1
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  have hn : Complex.normSq (z t) ≠ 0 := ne_of_gt (Complex.normSq_pos.2 h0)
  have h := (hq.log hn).div_const 2
  convert! h using 1
  · ext s
    rw [Complex.normSq_eq_norm_sq, Real.log_pow]
    simp
  · field_simp

/-- Jacobi's formula for log absolute determinant, valid for every nonsingular complex matrix. -/
theorem hasDerivAt_logNormDet {A : ℝ → Matrix ι ι ℂ} {H : Matrix ι ι ℂ} {t : ℝ}
    (hA : HasDerivAt A H t) (hdet : (A t).det ≠ 0) :
    HasDerivAt (fun s ↦ Real.log ‖(A s).det‖) (Matrix.trace (H * (A t)⁻¹)).re t := by
  have ha : (A t).adjugate = (A t).det • (A t)⁻¹ := by
    rw [Matrix.inv_def, Ring.inverse_eq_inv, smul_smul, mul_inv_cancel₀ hdet, one_smul]
  have h := hasDerivAt_det hA
  rw [ha, Matrix.mul_smul, Matrix.trace_smul] at h
  exact hasDerivAt_log_norm_of_mul h hdet

end QubitAdditivity.OpenAICalculus
