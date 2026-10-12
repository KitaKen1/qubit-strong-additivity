import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Basic.Complex.BigOperators
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

noncomputable section
open scoped Matrix BigOperators

namespace QubitAdditivity

variable {r s k l t : Type*}
variable [Fintype r] [Fintype s]
variable [Fintype k] [Fintype l] [Fintype t]

def blockMass (A : Matrix r k ℂ) : ℝ := (Matrix.trace (A * A.conjTranspose)).re

theorem blockMass_eq_sum_normSq (A : Matrix r k ℂ) :
    blockMass A = ∑ i, ∑ j, Complex.normSq (A i j) := by
  simp [blockMass, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.mul_conj]

theorem blockMass_nonneg (A : Matrix r k ℂ) : 0 ≤ blockMass A := by
  rw [blockMass_eq_sum_normSq]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    Complex.normSq_nonneg (A i j)

def tc4Matrix (A : Matrix r k ℂ) (B : Matrix r l ℂ)
    (C : Matrix s k ℂ) (D : Matrix s t ℂ) :
    Matrix (r ⊕ s) (k ⊕ (l ⊕ t)) ℂ
  | .inl i, .inl j => A i j
  | .inl i, .inr (.inl j) => B i j
  | .inl _, .inr (.inr _) => 0
  | .inr i, .inl j => C i j
  | .inr _, .inr (.inl _) => 0
  | .inr i, .inr (.inr j) => D i j

def tc4ScalarMatrix (x y z w : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(x + y : ℂ), (Real.sqrt (x * z) : ℂ);
     (Real.sqrt (x * z) : ℂ), (z + w : ℂ)]

theorem tc4Matrix_mass (A : Matrix r k ℂ) (B : Matrix r l ℂ)
    (C : Matrix s k ℂ) (D : Matrix s t ℂ) :
    blockMass (tc4Matrix A B C D) =
      blockMass A + blockMass B + blockMass C + blockMass D := by
  simp only [blockMass_eq_sum_normSq, Fintype.sum_sum_type, tc4Matrix,
    Complex.normSq_zero, Finset.sum_const_zero, add_zero, zero_add]
  simp only [Finset.sum_add_distrib]
  ring

/-- Exact expansion of the determinant of the scalar comparison matrix. -/
theorem tc4_scalar_determinant (x y z w : ℝ) (hxz : 0 ≤ x * z) :
    (x + y) * (z + w) - (Real.sqrt (x * z)) ^ 2 = x * w + y * z + y * w := by
  rw [Real.sq_sqrt hxz]
  ring

theorem tc4_scalar_determinant_nonneg (x y z w : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hw : 0 ≤ w) :
    0 ≤ (x + y) * (z + w) - (Real.sqrt (x * z)) ^ 2 := by
  rw [tc4_scalar_determinant x y z w (mul_nonneg hx hz)]
  positivity

end QubitAdditivity
