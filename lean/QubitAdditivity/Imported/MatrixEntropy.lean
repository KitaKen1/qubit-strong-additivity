/-
Derived from openai/math, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Apache-2.0; see vendor/openai/LICENSE. The proof bodies below are copied unchanged
from Model.lean and SpectralEntropy.lean; only imports and namespace are adapted.
This isolates general matrix results from unrelated GAD channel/calculus modules.
-/
import QuantumInfo.ForMathlib.HermitianMat.CFC
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Tactic.FunProp

noncomputable section
universe u
open scoped BigOperators ComplexOrder MatrixOrder CStarAlgebra
open Matrix
namespace QubitAdditivity.OpenAIEntropy
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The spectral definition of -Tr(P log P), with 0 log 0 = 0. -/
def entropy {ι : Type u} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℂ) : ℝ :=
  (Matrix.trace (cfc Real.negMulLog P)).re

def IsState {ι : Type u} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℂ) : Prop :=
  P.PosSemidef ∧ Matrix.trace P = 1


/-- Trace invariance under a unitary change of basis. -/
theorem trace_unitary_conj (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) :
    (Unitary.conjStarAlgAut ℂ _ U A).trace = A.trace := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
  simp

/-- Spectral trace for any function on the finite real spectrum. -/
theorem trace_cfc_eq {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, (f (hA.eigenvalues i) : ℂ) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, trace_unitary_conj]
  simp [Matrix.trace_diagonal, Function.comp_def]

theorem entropy_eq_sum {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    entropy A = ∑ i, Real.negMulLog (hA.eigenvalues i) := by
  simp [entropy, trace_cfc_eq hA]

/-- Entropy is invariant under every unitary basis change. -/
theorem entropy_unitary_conj (U : Matrix.unitaryGroup ι ℂ)
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    entropy (Unitary.conjStarAlgAut ℂ _ U A) = entropy A := by
  have hφA : (Unitary.conjStarAlgAut ℂ _ U A).IsHermitian := by
    simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
      Matrix.isHermitian_mul_mul_conjTranspose (U : Matrix ι ι ℂ) hA
  have hm := StarAlgHomClass.map_cfc (S := ℂ)
    (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) U) Real.negMulLog A
    Real.continuous_negMulLog.continuousOn
    (show Continuous (fun P : Matrix ι ι ℂ ↦ (U : Matrix ι ι ℂ) * P * star U) by fun_prop)
    hA hφA
  unfold entropy
  calc
    _ = (Matrix.trace (Unitary.conjStarAlgAut ℂ _ U (cfc Real.negMulLog A))).re :=
      congrArg (fun P : Matrix ι ι ℂ ↦ P.trace.re) hm.symm
    _ = _ := congrArg Complex.re (trace_unitary_conj U _)

end QubitAdditivity.OpenAIEntropy
