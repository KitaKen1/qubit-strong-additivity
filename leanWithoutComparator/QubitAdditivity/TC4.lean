import QubitAdditivity.Blocks
import QubitAdditivity.Imported.MatrixEntropy
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-! The manuscript's four-block inequality, stated with actual matrices.
There is deliberately no theorem claiming this inequality has been proved. -/

noncomputable section
open scoped Matrix BigOperators ComplexOrder

namespace QubitAdditivity

variable {r s k l t : Type*}
variable [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
variable [Fintype k] [Fintype l] [Fintype t]

def scalarFactor (x y z w : ℝ) : Matrix (Fin 2) (Fin 3) ℂ :=
  !![(Real.sqrt x : ℂ), (Real.sqrt y : ℂ), 0;
     (Real.sqrt z : ℂ), 0, (Real.sqrt w : ℂ)]

theorem scalarFactor_gram (x y z w : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hw : 0 ≤ w) :
    scalarFactor x y z w * (scalarFactor x y z w).conjTranspose =
      tc4ScalarMatrix x y z w := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply,
      scalarFactor, tc4ScalarMatrix, ← Complex.ofReal_mul, ← Complex.ofReal_add] <;>
    nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, Real.sq_sqrt hz,
      Real.sq_sqrt hw, Real.sqrt_mul hx z]

theorem tc4ScalarMatrix_posSemidef (x y z w : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hw : 0 ≤ w) :
    (tc4ScalarMatrix x y z w).PosSemidef := by
  rw [← scalarFactor_gram x y z w hx hy hz hw]
  exact Matrix.posSemidef_self_mul_conjTranspose _

theorem tc4ScalarMatrix_isState (x y z w : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hsum : x + y + z + w = 1) :
    OpenAIEntropy.IsState (tc4ScalarMatrix x y z w) := by
  refine ⟨tc4ScalarMatrix_posSemidef x y z w hx hy hz hw, ?_⟩
  simp [tc4ScalarMatrix, Matrix.trace, Fin.sum_univ_two]
  norm_cast
  linarith

/-- This is zero when the block has zero mass, as in the manuscript. -/
def weightedBlockEntropy (A : Matrix r k ℂ) : ℝ :=
  blockMass A * OpenAIEntropy.entropy ((blockMass A)⁻¹ • (A * A.conjTranspose))

/-- Exact finite-dimensional TC4 statement for arbitrary finite block index types, with
normalization and no commutativity restriction. -/
def TC4Bound : Prop :=
  ∀ {R S Kc L T : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    [Fintype Kc] [Fintype L] [Fintype T]
    (A : Matrix R Kc ℂ) (B : Matrix R L ℂ) (C : Matrix S Kc ℂ) (D : Matrix S T ℂ),
    blockMass A + blockMass B + blockMass C + blockMass D = 1 →
    OpenAIEntropy.entropy (tc4ScalarMatrix (blockMass A) (blockMass B)
      (blockMass C) (blockMass D)) + weightedBlockEntropy A +
      weightedBlockEntropy B + weightedBlockEntropy C + weightedBlockEntropy D ≤
    OpenAIEntropy.entropy (tc4Matrix A B C D * (tc4Matrix A B C D).conjTranspose)

theorem weightedBlockEntropy_zero_mass (A : Matrix r k ℂ) (h : blockMass A = 0) :
    weightedBlockEntropy A = 0 := by
  simp [weightedBlockEntropy, h]

end QubitAdditivity
