import QubitAdditivity.BetaEntropy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Elementwise

namespace QubitAdditivity.BetaKMOrder
open BetaPowers
variable {n : Type*} [Fintype n] [DecidableEq n]

local instance matrixNorm {i j : Type*} [Fintype i] [Fintype j] : NormedAddCommGroup (Matrix i j ℂ) :=
  inferInstanceAs (NormedAddCommGroup (i → j → ℂ))
local instance matrixSpace {i j : Type*} [Fintype i] [Fintype j] : NormedSpace ℝ (Matrix i j ℂ) :=
  inferInstanceAs (NormedSpace ℝ (i → j → ℂ))
local instance matrixENorm {i j : Type*} [Fintype i] [Fintype j] : ENormedAddMonoid (Matrix i j ℂ) :=
  inferInstanceAs (ENormedAddMonoid (i → j → ℂ))

/-- Strict order for the full actual KM operator, with no stationarity premise. -/
theorem km_sub_posDef {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (hgap : (A-B).PosDef) : (km A-km B).PosDef := by
  have hc : Continuous (fun t : ℝ => pw A t-pw B t) := (continuous_pw hA).sub (continuous_pw hB)
  have hp := BetaKM.integral_posDef hc (fun _ ht => BetaStrict.pw_sub_posDef hA hB hgap ht)
  simpa only [intervalIntegral.integral_sub (intervalIntegrable_pw hA) (intervalIntegrable_pw hB),km] using hp

theorem inverseKM_sub_posDef {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (hgap : (A-B).PosDef) : ((km B)⁻¹-(km A)⁻¹).PosDef :=
  BetaResolvent.inv_sub_posDef (BetaKM.km_posDef hA) (BetaKM.km_posDef hB) (km_sub_posDef hA hB hgap)

/-- Strict curvature of Ψ(B)-Ψ(A) when both matrices move in the same direction. -/
theorem psiHessian_gap_pos {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (hgap : (A-B).PosDef) {H : HermitianMat n ℂ} (hH : H ≠ 0) :
    0 < BetaEntropy.psiHessianRow B H H-BetaEntropy.psiHessianRow A H H := by
  have hp := BetaComparison.quadratic_pos (inverseKM_sub_posDef hA hB hgap)
    (show (fun ij : n × n => H.mat ij.1 ij.2) ≠ 0 from by
      intro hz
      apply hH
      apply Subtype.ext
      ext i j
      exact congrFun hz (i,j))
  rw [BetaComparison.quadratic_sub] at hp
  simpa only [BetaEntropy.psiHessianRow_eq_pairing,BetaComparison.quadratic] using hp

end QubitAdditivity.BetaKMOrder
