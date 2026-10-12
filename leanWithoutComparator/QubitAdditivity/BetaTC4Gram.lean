import QubitAdditivity.BetaGramSplit
import QubitAdditivity.TC4

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

namespace QubitAdditivity.BetaTC4Gram
open BetaDual BetaEntropy BetaDualValue BetaTC4Structure BetaGramSplit

@[reducible] local instance mNorm {k : Type*} [Fintype k] [DecidableEq k] :
    NormedAddCommGroup (Matrix k k ℂ) :=
  Matrix.frobeniusNormedRing.toNonUnitalNormedRing.toNormedAddCommGroup
@[reducible] local instance mSpace {k : Type*} [Fintype k] [DecidableEq k] :
    NormedSpace ℝ (Matrix k k ℂ) := NormedAlgebra.toNormedSpace (Matrix k k ℂ)
@[reducible] local instance mTop {k : Type*} [Fintype k] [DecidableEq k] :
    TopologicalSpace (Matrix k k ℂ) := mNorm.toUniformSpace.toTopologicalSpace
@[reducible] local instance mAdd {k : Type*} [Fintype k] [DecidableEq k] :
    AddCommGroup (Matrix k k ℂ) := mNorm.toAddCommGroup
@[reducible] local instance mModule {k : Type*} [Fintype k] [DecidableEq k] :
    Module ℝ (Matrix k k ℂ) := mSpace.toModule
@[reducible] local instance hTop {k : Type*} [Fintype k] : TopologicalSpace (HermitianMat k ℂ) :=
  HermitianMat.instNormedAddCommGroupComplex.toUniformSpace.toTopologicalSpace
@[reducible] local instance hAdd {k : Type*} [Fintype k] : AddCommGroup (HermitianMat k ℂ) :=
  HermitianMat.instNormedAddCommGroupComplex.toAddCommGroup
@[reducible] local instance hModule {k : Type*} [Fintype k] : Module ℝ (HermitianMat k ℂ) :=
  HermitianMat.instNormedSpace.toModule


@[reducible] local instance pAdd {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] :
    AddCommGroup (E × F) := Prod.normedAddCommGroup.toAddCommGroup
@[reducible] local instance pTop {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] :
    TopologicalSpace (E × F) := Prod.normedAddCommGroup.toUniformSpace.toTopologicalSpace
@[reducible] local instance pModule {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F] : Module ℝ (E × F) := Prod.normedSpace.toModule

@[reducible] local instance matrixHMul {a b c : Type*} [Fintype b] :
    HMul (Matrix a b ℂ) (Matrix b c ℂ) (Matrix a c ℂ) :=
  Matrix.instHMulOfFintypeOfMulOfAddCommMonoid


variable {r s k l t : Type*} [Fintype r] [Fintype s] [Fintype k] [Fintype l] [Fintype t]
  [DecidableEq r] [DecidableEq s]

def gram (A : Matrix r k ℂ) : HermitianMat r ℂ :=
  ⟨A*Aᴴ,Matrix.isHermitian_mul_conjTranspose_self A⟩

theorem gram_posSemidef (A : Matrix r k ℂ) : (gram A).mat.PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose A

theorem gram_trace (A : Matrix r k ℂ) : (gram A).mat.trace.re = blockMass A := rfl

theorem gram_zero_of_mass_zero (A : Matrix r k ℂ) (hm : blockMass A = 0) : gram A = 0 := by
  apply HermitianMat.ext
  apply (gram_posSemidef A).trace_zero
  have hr : (gram A).trace = (gram A).mat.trace.re := (gram A).trace_eq_re_trace
  have ht : ((gram A).trace : ℂ) = (gram A).mat.trace := (gram A).trace_eq_trace_rc
  rw [hr] at ht
  rw [← ht]
  change (blockMass A : ℂ) = 0
  rw [hm]
  rfl

/-- The homogeneous entropy identity remains valid at zero mass. -/
theorem weightedBlockEntropy_eq (A : Matrix r k ℂ) :
    weightedBlockEntropy A = -psi (gram A)+blockMass A*Real.log (blockMass A) := by
  by_cases hm : blockMass A = 0
  · rw [weightedBlockEntropy_zero_mass A hm,gram_zero_of_mass_zero A hm,psi_zero,hm]
    simp
  · have hs : OpenAIEntropy.entropy ((blockMass A)⁻¹ • (A*Aᴴ)) =
        (blockMass A)⁻¹*OpenAIEntropy.entropy (A*Aᴴ)+Real.negMulLog ((blockMass A)⁻¹)*blockMass A := by
      convert! OpenAIEntropy.entropy_smul ((blockMass A)⁻¹) (gram A).H using 1
    have he : OpenAIEntropy.entropy (A*Aᴴ) = -psi (gram A) := by
      simp only [psi,gram,neg_neg]
      rfl
    rw [weightedBlockEntropy,hs,he]
    rw [Real.negMulLog,Real.log_inv]
    field_simp

def gramBlocks (B : Matrix r l ℂ) (D : Matrix s t ℂ) : Blocks r s := (gram B,gram D)

theorem gramBlocks_mem_positiveCone (B : Matrix r l ℂ) (D : Matrix s t ℂ) :
    gramBlocks B D ∈ BetaDual.positiveCone := ⟨gram_posSemidef B,gram_posSemidef D⟩

theorem gramPair_posSemidef (A : Matrix r k ℂ) (C : Matrix s k ℂ) :
    (gramPair A C).mat.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose _

theorem pinchLeft_gramPair (A : Matrix r k ℂ) (C : Matrix s k ℂ) : pinchLeft (gramPair A C) = gram A := by
  apply HermitianMat.ext
  change ((Matrix.fromRows A C*(Matrix.fromRows A C)ᴴ).submatrix Sum.inl Sum.inl) = A*Aᴴ
  ext i j
  simp [Matrix.submatrix_apply,Matrix.mul_apply,Matrix.fromRows,Matrix.conjTranspose_apply]

theorem pinchRight_gramPair (A : Matrix r k ℂ) (C : Matrix s k ℂ) : pinchRight (gramPair A C) = gram C := by
  apply HermitianMat.ext
  change ((Matrix.fromRows A C*(Matrix.fromRows A C)ᴴ).submatrix Sum.inr Sum.inr) = C*Cᴴ
  ext i j
  simp [Matrix.submatrix_apply,Matrix.mul_apply,Matrix.fromRows,Matrix.conjTranspose_apply]

theorem psi_pinching_gramPair (A : Matrix r k ℂ) (C : Matrix s k ℂ) :
    psi (pinching (gramPair A C)) = psi (gram A)+psi (gram C) := by
  change psi (diagonal (pinchLeft (gramPair A C),pinchRight (gramPair A C))) = _
  rw [pinchLeft_gramPair,pinchRight_gramPair,psi_diagonal]

theorem tc4Matrix_eq_fromCols (A : Matrix r k ℂ) (B : Matrix r l ℂ) (C : Matrix s k ℂ) (D : Matrix s t ℂ) :
    tc4Matrix A B C D = Matrix.fromCols (Matrix.fromRows A C) (Matrix.fromBlocks B 0 0 D) := by
  ext i j
  cases i <;> cases j with
  | inl j => rfl
  | inr j => cases j <;> rfl

/-- Exact four-block Gram expansion, including empty row and column types. -/
theorem gram_tc4Matrix (A : Matrix r k ℂ) (B : Matrix r l ℂ) (C : Matrix s k ℂ) (D : Matrix s t ℂ) :
    gram (tc4Matrix A B C D) = gramPair A C+diagonal (gramBlocks B D) := by
  apply HermitianMat.ext
  change tc4Matrix A B C D*(tc4Matrix A B C D)ᴴ =
    Matrix.fromRows A C*(Matrix.fromRows A C)ᴴ+Matrix.fromBlocks (B*Bᴴ) 0 0 (D*Dᴴ)
  rw [tc4Matrix_eq_fromCols,Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromCols_mul_fromRows,Matrix.fromBlocks_conjTranspose,Matrix.fromBlocks_multiply]
  simp

end QubitAdditivity.BetaTC4Gram
