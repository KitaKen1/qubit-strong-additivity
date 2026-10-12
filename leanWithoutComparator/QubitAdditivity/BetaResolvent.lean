import QubitAdditivity.BetaOrder
import QubitAdditivity.Imported.LogDetCalculus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Elementwise

namespace QubitAdditivity.BetaResolvent
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Strict inverse compression follows from the semidefinite Schur estimate
and invertibility of the two complementary Schur complements. -/
theorem inverse_compression_strict_posDef
    (Z : Matrix n n ℂ) (C : Matrix m m ℂ) (V : Matrix n m ℂ)
    (hZ : Z.PosDef) (hC : C.PosDef) (hgap : (C - Vᴴ * Z * V).PosDef) :
    (Z⁻¹ - V * C⁻¹ * Vᴴ).PosDef := by
  have hp := BetaOrder.inverse_compression_residual_posSemidef Z C V hZ hC hgap.posSemidef
  letI : Invertible Z := hZ.isUnit.invertible
  letI : Invertible Z⁻¹ := hZ.inv.isUnit.invertible
  letI : Invertible C := hC.isUnit.invertible
  have hM : IsUnit (Matrix.fromBlocks Z⁻¹ V Vᴴ C) := by
    apply Matrix.isUnit_fromBlocks_iff_of_invertible₁₁.mpr
    simpa only [Matrix.invOf_eq_nonsing_inv, Matrix.inv_inv_of_invertible] using hgap.isUnit
  have hi : IsUnit (Z⁻¹ - V * C⁻¹ * Vᴴ) := by
    simpa only [Matrix.invOf_eq_nonsing_inv] using
      Matrix.isUnit_fromBlocks_iff_of_invertible₂₂.mp hM
  exact hp.posDef_iff_isUnit.mpr hi

theorem inv_sub_posDef {A B : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (hgap : (A - B).PosDef) :
    (B⁻¹ - A⁻¹).PosDef := by
  have hg : (A - (1 : Matrix n n ℂ)ᴴ * B * 1).PosDef := by simpa using hgap
  simpa using inverse_compression_strict_posDef B A 1 hB hA hg

def shift (A : Matrix n n ℂ) (u : ℝ) : Matrix n n ℂ := A + u • 1
def resolvent (A : Matrix n n ℂ) (u : ℝ) : Matrix n n ℂ := (shift A u)⁻¹

theorem shift_posDef {A : Matrix n n ℂ} (hA : A.PosDef) {u : ℝ} (hu : 0 ≤ u) :
    (shift A u).PosDef := by
  exact hA.add_posSemidef (Matrix.PosSemidef.one.smul hu)

theorem resolvent_posDef {A : Matrix n n ℂ} (hA : A.PosDef) {u : ℝ} (hu : 0 ≤ u) :
    (resolvent A u).PosDef := (shift_posDef hA hu).inv

theorem shift_sub (A B : Matrix n n ℂ) (u : ℝ) : shift A u - shift B u = A - B := by
  unfold shift
  abel

/-- Strict inverse order for the actual shifted resolvents, including noncommuting A and B. -/
theorem resolvent_sub_posDef {A B : Matrix n n ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (hgap : (A - B).PosDef) {u : ℝ} (hu : 0 ≤ u) :
    (resolvent B u - resolvent A u).PosDef := by
  apply inv_sub_posDef (shift_posDef hA hu) (shift_posDef hB hu)
  rwa [shift_sub]

/-- Noncommuting matrix-curve derivative. The shift parameter is fixed. -/
theorem hasDerivAt_resolvent {A : ℝ → Matrix n n ℂ} {H : Matrix n n ℂ} {t : ℝ}
    (hA : HasDerivAt A H t) (hpos : (A t).PosDef) (u : ℝ) (hu : 0 ≤ u) :
    HasDerivAt (fun s => resolvent (A s) u)
      (-resolvent (A t) u * H * resolvent (A t) u) t := by
  exact OpenAICalculus.hasDerivAt_matrix_inv (hA.add_const (u • 1))
    (shift_posDef hpos hu).det_pos.ne'

/-- OpenAI's unchanged log-determinant derivative applies to every positive
matrix curve, with no amplitude-damping or commutation assumption. -/
theorem hasDerivAt_logNormDet_shift {A : ℝ → Matrix n n ℂ} {H : Matrix n n ℂ} {t : ℝ}
    (hA : HasDerivAt A H t) (hpos : (A t).PosDef) (u : ℝ) (hu : 0 ≤ u) :
    HasDerivAt (fun s => Real.log ‖(shift (A s) u).det‖)
      (Matrix.trace (H * resolvent (A t) u)).re t := by
  exact OpenAICalculus.hasDerivAt_logNormDet (hA.add_const (u • 1))
    (shift_posDef hpos hu).det_pos.ne'

/-- Differentiating the resolvent trace yields the noncommuting log-det
curvature expression. Identifying a dual objective Hessian is a separate task. -/
theorem hasDerivAt_resolvent_trace {A : ℝ → Matrix n n ℂ}
    {H K : Matrix n n ℂ} {t : ℝ}
    (hA : HasDerivAt A H t) (hpos : (A t).PosDef) (u : ℝ) (hu : 0 ≤ u) :
    HasDerivAt (fun s => (Matrix.trace (K * resolvent (A s) u)).re)
      (Matrix.trace (K * (-resolvent (A t) u * H * resolvent (A t) u))).re t := by
  have hm := OpenAICalculus.hasDerivAt_matrix_mul (hasDerivAt_const t K)
    (hasDerivAt_resolvent hA hpos u hu)
  have hh := HasDerivAt.sum (u := Finset.univ)
    (fun i _ => hasDerivAt_pi.1 (hasDerivAt_pi.1 hm i) i)
  simpa only [Matrix.zero_mul, zero_add, Matrix.trace, Matrix.diag, Finset.sum_apply, Function.comp_def, Complex.reCLM_apply] using Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hh

end QubitAdditivity.BetaResolvent
