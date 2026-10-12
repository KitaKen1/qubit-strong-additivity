/-
Derived from openai/math, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Apache-2.0; see vendor/openai/LICENSE.
The six proof bodies are copied unchanged from MatrixDifferentiation.lean;
only imports and namespace are adapted. No GAD-channel assumption is used.
-/
import Mathlib.Analysis.Calculus.FDeriv.ContinuousMultilinearMap
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FunProp

set_option autoImplicit false
noncomputable section
universe u_1
open scoped BigOperators Matrix.Norms.Elementwise
open Matrix
namespace QubitAdditivity.OpenAICalculus
variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

/-- The determinant as a continuous multilinear map in its rows. -/
def detMultilinear : ContinuousMultilinearMap ℂ (fun _ : ι ↦ ι → ℂ) ℂ :=
  { Matrix.detRowAlternating.toMultilinearMap with
    cont := by
      change Continuous (Matrix.det : Matrix ι ι ℂ → ℂ)
      fun_prop }

/-- Jacobi's differential, without an invertibility assumption. -/
theorem det_linearDeriv (A H : Matrix ι ι ℂ) :
    detMultilinear.linearDeriv A H = Matrix.trace (H * A.adjugate) := by
  change (detMultilinear.linearDeriv (fun i j ↦ A i j)) (fun i j ↦ H i j) = _
  rw [ContinuousMultilinearMap.linearDeriv_apply]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  change (A.updateRow i (H i)).det = _
  rw [← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec,
    ← Matrix.adjugate_transpose]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Jacobi's formula along any differentiable complex-matrix curve. -/
theorem hasDerivAt_det {A : ℝ → Matrix ι ι ℂ} {H : Matrix ι ι ℂ} {t : ℝ}
    (hA : HasDerivAt A H t) :
    HasDerivAt (fun s ↦ (A s).det) (Matrix.trace (H * (A t).adjugate)) t := by
  have h := ((detMultilinear.hasFDerivAt (A t)).restrictScalars ℝ).comp_hasDerivAt t hA
  change HasDerivAt (fun s ↦ (A s).det) (detMultilinear.linearDeriv (A t) H) t at h
  rwa [det_linearDeriv] at h

omit [DecidableEq ι] in
/-- Product differentiation with the entrywise matrix topology. -/
theorem hasDerivAt_matrix_mul {A B : ℝ → Matrix ι ι ℂ}
    {H K : Matrix ι ι ℂ} {t : ℝ}
    (hA : HasDerivAt A H t) (hB : HasDerivAt B K t) :
    HasDerivAt (fun s ↦ A s * B s) (H * B t + A t * K) t := by
  apply hasDerivAt_pi.2
  intro i
  apply hasDerivAt_pi.2
  intro j
  have hh := HasDerivAt.sum (u := Finset.univ) (fun k _ ↦
    ((hasDerivAt_pi.1 (hasDerivAt_pi.1 hA i) k).mul
      (hasDerivAt_pi.1 (hasDerivAt_pi.1 hB k) j)))
  convert! hh using 1
  · ext s
    simp [Matrix.mul_apply]
  · simp [Matrix.mul_apply, Finset.sum_add_distrib]

/-- The row replacement operation is affine. -/
theorem hasDerivAt_updateRow {A : ℝ → Matrix ι ι ℂ} {H : Matrix ι ι ℂ} {t : ℝ}
    (hA : HasDerivAt A H t) (i : ι) (x : ι → ℂ) :
    HasDerivAt (fun s ↦ (A s).updateRow i x) (H.updateRow i 0) t := by
  apply hasDerivAt_pi.2
  intro j
  by_cases hj : j = i
  · subst j
    simpa using hasDerivAt_const t x
  · simpa [Matrix.updateRow_ne hj] using hasDerivAt_pi.1 hA j

/-- Polynomial differentiability of the adjugate, with no nonsingularity restriction. -/
theorem differentiableAt_adjugate {A : ℝ → Matrix ι ι ℂ} {H : Matrix ι ι ℂ} {t : ℝ}
    (hA : HasDerivAt A H t) :
    DifferentiableAt ℝ (fun s ↦ (A s).adjugate) t := by
  apply differentiableAt_pi.2
  intro i
  apply differentiableAt_pi.2
  intro j
  simpa only [Matrix.adjugate_apply] using
    (hasDerivAt_det (hasDerivAt_updateRow hA j (Pi.single i 1))).differentiableAt

/-- The full noncommutative derivative of matrix inversion. -/
theorem hasDerivAt_matrix_inv {A : ℝ → Matrix ι ι ℂ} {H : Matrix ι ι ℂ} {t : ℝ}
    (hA : HasDerivAt A H t) (hdet : (A t).det ≠ 0) :
    HasDerivAt (fun s ↦ (A s)⁻¹) (-(A t)⁻¹ * H * (A t)⁻¹) t := by
  have hd := (hasDerivAt_det hA).differentiableAt.inv hdet
  have hi : DifferentiableAt ℝ (fun s ↦ (A s)⁻¹) t := by
    convert! hd.smul (differentiableAt_adjugate hA) using 1
    ext s
    simp only [Matrix.inv_def, Ring.inverse_eq_inv]
    rfl
  have hev := (hasDerivAt_det hA).continuousAt.eventually_ne hdet
  have hc : HasDerivAt (fun s ↦ A s * (A s)⁻¹) 0 t :=
    (hasDerivAt_const t (1 : Matrix ι ι ℂ)).congr_of_eventuallyEq
      (hev.mono fun s hs ↦ Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hs))
  have hh := (hasDerivAt_matrix_mul hA hi.hasDerivAt).unique hc
  have he := congrArg (fun M ↦ (A t)⁻¹ * M) hh
  simp only [Matrix.mul_add, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.2 hdet), Matrix.one_mul, Matrix.mul_zero] at he
  have hk := eq_neg_of_add_eq_zero_right he
  convert! hi.hasDerivAt using 1
  simp only [hk, Matrix.neg_mul]

end QubitAdditivity.OpenAICalculus
