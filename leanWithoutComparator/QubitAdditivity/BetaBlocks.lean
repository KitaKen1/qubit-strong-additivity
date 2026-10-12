import QubitAdditivity.BetaBridge
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix
open scoped Matrix Kronecker ComplexOrder MatrixOrder

namespace QubitAdditivity.BetaBlocks
open BetaOperators BetaPowers BetaBridge
variable {r s : Type*} [Fintype r] [Fintype s] [DecidableEq r] [DecidableEq s]

def diagonalHom : (Matrix r r ℂ × Matrix s s ℂ) →⋆ₐ[ℝ] Matrix (r ⊕ s) (r ⊕ s) ℂ where
  toFun X := Matrix.fromBlocks X.1 0 0 X.2
  map_one' := by ext i j; cases i <;> cases j <;> simp [Matrix.one_apply]
  map_mul' X Y := by simp [Matrix.fromBlocks_multiply]
  map_zero' := by ext i j; cases i <;> cases j <;> simp
  map_add' X Y := by ext i j; cases i <;> cases j <;> simp
  commutes' c := by ext i j; cases i <;> cases j <;> simp [Algebra.algebraMap_eq_smul_one, Matrix.one_apply]
  map_star' X := by simp [star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose]

open scoped Matrix.Norms.L2Operator in
theorem cfc_diagonal (A : Matrix r r ℂ) (B : Matrix s s ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℝ) :
    cfc f (Matrix.fromBlocks A 0 0 B) = Matrix.fromBlocks (cfc f A) 0 0 (cfc f B) := by
  letI : ContinuousFunctionalCalculus ℝ (Matrix r r ℂ × Matrix s s ℂ) IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  have hf : ContinuousOn f (spectrum ℝ A ∪ spectrum ℝ B) :=
    ((Set.toFinite (spectrum ℝ A)).union (Set.toFinite (spectrum ℝ B))).continuousOn f
  have hh := diagonalHom.map_cfc f (A, B) (by rwa [Prod.spectrum_eq])
    (by change Continuous (fun X : Matrix r r ℂ × Matrix s s ℂ => Matrix.fromBlocks X.1 0 0 X.2); fun_prop) (show IsSelfAdjoint (A, B) from Prod.ext hA hB)
    (show IsSelfAdjoint (Matrix.fromBlocks A 0 0 B) from hA.fromBlocks (by simp) hB)
  rw [cfc_map_prod (S := ℝ) (pab := IsSelfAdjoint) (pa := IsSelfAdjoint) (pb := IsSelfAdjoint) f A B hf (show IsSelfAdjoint (A, B) from Prod.ext hA hB) hA hB] at hh
  exact hh.symm

theorem power_diagonal (A : Matrix r r ℂ) (B : Matrix s s ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (t : ℝ) :
    power (Matrix.fromBlocks A 0 0 B) t =
      Matrix.fromBlocks (power A t) 0 0 (power B t) := cfc_diagonal A B hA hB _

/-- The full PW operator restricts to the block algebra without mixing its complement. -/
theorem pw_diagonal_compression (A : Matrix r r ℂ) (B : Matrix s s ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (t : ℝ) :
    blockInclusionᴴ * pw (Matrix.fromBlocks A 0 0 B) t * blockInclusion = blockPW A B t := by
  rw [blockInclusion, coordinateInclusion_compression, pw_eq_kronecker,
    power_diagonal A B hA hB, power_diagonal A B hA hB]
  ext i j
  cases i <;> cases j <;>
    simp [blockPW, pw_eq_kronecker, kroneckerMap_apply]

theorem pw_diagonal_reduces (A : Matrix r r ℂ) (B : Matrix s s ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (t : ℝ) :
    pw (Matrix.fromBlocks A 0 0 B) t * blockInclusion = blockInclusion * blockPW A B t := by
  rw [pw_eq_kronecker, power_diagonal A B hA hB, power_diagonal A B hA hB]
  ext i j
  rcases i with ⟨i, k⟩
  cases i <;> cases k <;> cases j <;>
    simp [blockInclusion, coordinateInclusion, Matrix.mul_apply, Fintype.sum_prod_type,
      blockPW, pw_eq_kronecker, kroneckerMap_apply, Matrix.one_apply, ite_and]

/-- The complementary PW operator is positive, since the block algebra reduces it. -/
theorem pw_diagonal_residual_posSemidef {A : Matrix r r ℂ} {B : Matrix s s ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (t : ℝ)
    (hW : (Matrix.fromBlocks A 0 0 B).PosDef) :
    (pw (Matrix.fromBlocks A 0 0 B) t -
      blockInclusion * blockPW A B t * blockInclusionᴴ).PosSemidef := by
  let V := blockInclusion (r := r) (s := s)
  let Q := pw (Matrix.fromBlocks A 0 0 B) t
  have hV : Vᴴ * V = 1 := blockInclusion_isometry
  have hred : Q * V = V * blockPW A B t := pw_diagonal_reduces A B hA.1 hB.1 t
  have hcomp : Vᴴ * Q * V = blockPW A B t := pw_diagonal_compression A B hA.1 hB.1 t
  have hh := (pw_posDef hW t).posSemidef.conjTranspose_mul_mul_same (1 - V * Vᴴ)
  convert hh using 1
  simp only [conjTranspose_sub, conjTranspose_one, conjTranspose_mul,
    conjTranspose_conjTranspose, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one]
  have hright : Q * (V * Vᴴ) = V * blockPW A B t * Vᴴ := by
    rw [← Matrix.mul_assoc, hred]
  have hleft : V * Vᴴ * Q = V * blockPW A B t * Vᴴ := by
    have hh := congrArg Matrix.conjTranspose hright
    have hb : (blockPW A B t).IsHermitian :=
      (pw_posDef hA t).1.fromBlocks (by simp) (pw_posDef hB t).1
    simpa [conjTranspose_mul, (pw_posDef hW t).1.eq, hb.eq, V, Q, Matrix.mul_assoc] using hh
  have hh' : (V * blockPW A B t * Vᴴ) * (V * Vᴴ) = V * blockPW A B t * Vᴴ := by
    calc
      _ = V * blockPW A B t * (Vᴴ * V) * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hV]; simp
  change Q - V * blockPW A B t * Vᴴ = _
  rw [hright, hleft, hh']
  abel

theorem diagonal_posDef {A : Matrix r r ℂ} {B : Matrix s s ℂ}
    (hA : A.PosDef) (hB : B.PosDef) : (Matrix.fromBlocks A 0 0 B).PosDef := by
  letI : Invertible A := hA.isUnit.invertible
  have hh : (Matrix.fromBlocks A 0 0 B).PosSemidef := by
    simpa only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, sub_zero] using
      (Matrix.PosDef.fromBlocks₁₁ (0 : Matrix r s ℂ) B hA).mpr
        (by simpa using hB.posSemidef)
  exact hh.posDef_iff_isUnit.mpr (Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hA.isUnit,hB.isUnit⟩)

end QubitAdditivity.BetaBlocks
