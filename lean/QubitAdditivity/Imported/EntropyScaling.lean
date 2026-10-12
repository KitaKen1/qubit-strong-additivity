/-
Derived from openai/math, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Apache-2.0; see vendor/openai/LICENSE. The theorem body is copied unchanged
from ZeroBlockEntropy.lean. Imports and namespace are adapted.
-/
import QubitAdditivity.Imported.MatrixEntropy

noncomputable section
open Matrix
open scoped ComplexOrder MatrixOrder
namespace QubitAdditivity.OpenAIEntropy
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem entropy_smul (a : ℝ) {P : Matrix ι ι ℂ} (hP : P.IsHermitian) :
    entropy (a • P) = a * entropy P + Real.negMulLog a * P.trace.re := by
  rw [entropy, ← cfc_comp_smul a Real.negMulLog P, trace_cfc_eq hP]
  simp only [smul_eq_mul, Complex.re_sum, Complex.ofReal_re,
    Real.negMulLog_mul, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    ← entropy_eq_sum hP]
  rw [hP.trace_eq_sum_eigenvalues]
  simp
  ring

end QubitAdditivity.OpenAIEntropy
