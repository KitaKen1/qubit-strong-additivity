import QubitAdditivity.BetaTC4Gram
import QubitAdditivity.BetaTC4Unitary
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix
open scoped Matrix ComplexOrder MatrixOrder

namespace QubitAdditivity.BetaIsometryEntropy
open BetaEntropy
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- An isometric embedding is a non-unital star algebra map. -/
def embeddingHom (R : Matrix m n ℂ) (hR : Rᴴ*R = 1) :
    (Matrix n n ℂ) →⋆ₙₐ[ℝ] Matrix m m ℂ where
  toFun A := R*A*Rᴴ
  map_zero' := by simp
  map_add' A B := by simp [Matrix.mul_add,Matrix.add_mul]
  map_mul' A B := by
    simp only [Matrix.mul_assoc,← Matrix.mul_assoc Rᴴ R (B*Rᴴ),hR,Matrix.one_mul]
  map_smul' c A := by simp [Matrix.mul_smul,Matrix.smul_mul]
  map_star' A := by simp [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_mul,Matrix.mul_assoc]

@[simp] theorem embeddingHom_apply (R : Matrix m n ℂ) (hR : Rᴴ*R = 1) (A : Matrix n n ℂ) :
    embeddingHom R hR A = R*A*Rᴴ := rfl

open scoped Matrix.Norms.L2Operator in
/-- The zero-preserving CFC passes through a rectangular isometry. -/
theorem cfc_isometry (R : Matrix m n ℂ) (hR : Rᴴ*R = 1) (A : Matrix n n ℂ)
    (hA : A.IsHermitian) (f : ℝ → ℝ) (hf : Continuous f) (hf0 : f 0 = 0) :
    cfc f (R*A*Rᴴ) = R*cfc f A*Rᴴ := by
  have hm := (embeddingHom R hR).map_cfcₙ f A hf.continuousOn hf0
    (by change Continuous (fun X : Matrix n n ℂ => R*X*Rᴴ); fun_prop) hA
    (Matrix.isHermitian_mul_mul_conjTranspose R hA)
  rw [cfcₙ_eq_cfc hf.continuousOn hf0,cfcₙ_eq_cfc hf.continuousOn hf0] at hm
  exact hm.symm

/-- Trace and entropy are preserved under rectangular isometric conjugation. -/
theorem trace_isometry (R : Matrix m n ℂ) (hR : Rᴴ*R = 1) (A : Matrix n n ℂ) :
    (R*A*Rᴴ).trace = A.trace := by
  rw [Matrix.trace_mul_cycle,hR,Matrix.one_mul]

theorem entropy_isometry (R : Matrix m n ℂ) (hR : Rᴴ*R = 1) (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    OpenAIEntropy.entropy (R*A*Rᴴ) = OpenAIEntropy.entropy A := by
  unfold OpenAIEntropy.entropy
  rw [cfc_isometry R hR A hA Real.negMulLog Real.continuous_negMulLog (by simp),trace_isometry R hR]

theorem psi_isometry (R : Matrix m n ℂ) (hR : Rᴴ*R = 1) (A : HermitianMat n ℂ) :
    psi (A.conj R) = psi A := by
  unfold psi
  exact congrArg Neg.neg (entropy_isometry R hR A.mat A.H)

end QubitAdditivity.BetaIsometryEntropy
