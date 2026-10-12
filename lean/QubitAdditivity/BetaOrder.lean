import QubitAdditivity.BetaCore
import Mathlib.Analysis.Matrix.Order

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Matrix ComplexOrder MatrixOrder

namespace QubitAdditivity.BetaOrder
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The stationary Gram inequality implies the Riccati residual inequality.
The derivative interpretation of F, G, H belongs to the analytic layer. -/
theorem gram_schur_residual_posSemidef
    (F G H : Matrix n n ℂ) (hF : F.PosDef) (hG : G.IsHermitian)
    (hGram : (Matrix.fromBlocks F G G H).PosSemidef) :
    (H - G * F⁻¹ * G).PosSemidef := by
  letI : Invertible F := hF.isUnit.invertible
  have hG' : Gᴴ = G := hG
  have hh := (Matrix.PosDef.fromBlocks₁₁ G H hF).mp
    (show (Matrix.fromBlocks F G Gᴴ H).PosSemidef by simpa only [hG'] using hGram)
  simpa only [hG'] using hh

/-- Inverse compression with a dominating matrix C, obtained from a block Gram
and one Schur complement. No square root or inverse-order theorem is needed. -/
theorem inverse_compression_residual_posSemidef
    (Z : Matrix n n ℂ) (C : Matrix m m ℂ) (V : Matrix n m ℂ)
    (hZ : Z.PosDef) (hC : C.PosDef) (hKM : (C - Vᴴ * Z * V).PosSemidef) :
    (Z⁻¹ - V * C⁻¹ * Vᴴ).PosSemidef := by
  letI : Invertible C := hC.isUnit.invertible
  have hi : IsUnit Z.det := (Matrix.isUnit_iff_isUnit_det Z).mp hZ.isUnit
  have hzi : Z⁻¹ᴴ = Z⁻¹ := by rw [conjTranspose_nonsing_inv, hZ.1]
  have hg := hZ.posSemidef.conjTranspose_mul_mul_same (Matrix.fromCols Z⁻¹ V)
  have heq : (Matrix.fromCols Z⁻¹ V)ᴴ * Z * Matrix.fromCols Z⁻¹ V =
      Matrix.fromBlocks Z⁻¹ V Vᴴ (Vᴴ * Z * V) := by
    rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul,
      fromRows_mul_fromCols]
    simp only [hzi, Matrix.nonsing_inv_mul Z hi, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv Z hi, Matrix.mul_one]
  rw [heq] at hg
  have hn := hKM.mul_mul_conjTranspose_same
    (Matrix.fromRows (0 : Matrix n m ℂ) (1 : Matrix m m ℂ))
  simp only [conjTranspose_fromRows_eq_fromCols_conjTranspose, conjTranspose_zero,
    conjTranspose_one, fromRows_mul, fromRows_mul_fromCols, Matrix.zero_mul,
    Matrix.mul_zero, Matrix.mul_one, Matrix.one_mul] at hn
  have hp : (Matrix.fromBlocks Z⁻¹ V Vᴴ C).PosSemidef := by
    convert hg.add hn using 1
    ext i j
    cases i <;> cases j <;> simp
  exact (Matrix.PosDef.fromBlocks₂₂ Z⁻¹ V hC).mp hp

/-- Once KM and positivity have been supplied, the eliminated dual Hessian is
nonpositive. This proves the order step, without asserting minimizer calculus. -/
theorem eliminatedHessian_nonpos
    (A : Matrix n n ℂ) (B C : Matrix m m ℂ) (V : Matrix n m ℂ)
    (hA : IsUnit A) (hB : IsUnit B)
    (hE : IsUnit (B⁻¹ - Vᴴ * A⁻¹ * V))
    (hZ : (A - V * B * Vᴴ).PosDef) (hC : C.PosDef)
    (hKM : (C - Vᴴ * (A - V * B * Vᴴ) * V).PosSemidef) :
    V * C⁻¹ * Vᴴ - A⁻¹ -
      A⁻¹ * V * (B⁻¹ - Vᴴ * A⁻¹ * V)⁻¹ * Vᴴ * A⁻¹ ≤ 0 := by
  rw [BetaCore.eliminatedHessian_eq A B C V hA hB hE]
  exact sub_nonpos.mpr (sub_nonneg.mp
    (inverse_compression_residual_posSemidef (A - V * B * Vᴴ) C V hZ hC hKM).nonneg)
end QubitAdditivity.BetaOrder
