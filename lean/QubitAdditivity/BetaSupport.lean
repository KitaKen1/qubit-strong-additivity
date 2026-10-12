import QubitAdditivity.BetaBlockIsometry
import QubitAdditivity.BetaOrthogonalEntropy
import QubitAdditivity.BetaReflection

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius

namespace QubitAdditivity.BetaSupport
open BetaDual BetaEntropy BetaDualValue BetaIsometryEntropy BetaBlockIsometry BetaOrthogonalEntropy BetaReflection

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


variable {m n r s a b : Type*} [Fintype m] [Fintype n] [Fintype r] [Fintype s] [Fintype a] [Fintype b]
  [DecidableEq m] [DecidableEq n] [DecidableEq r] [DecidableEq s] [DecidableEq a] [DecidableEq b]

def rangeProjection (R : Matrix m n ℂ) : HermitianMat m ℂ :=
  ⟨R*Rᴴ,Matrix.isHermitian_mul_conjTranspose_self R⟩

theorem rangeProjection_sq (R : Matrix m n ℂ) (hR : Rᴴ*R = 1) :
    (rangeProjection R).mat*(rangeProjection R).mat = (rangeProjection R).mat := by
  change (R*Rᴴ)*(R*Rᴴ) = R*Rᴴ
  rw [Matrix.mul_assoc,← Matrix.mul_assoc Rᴴ R Rᴴ,hR,Matrix.one_mul]

theorem rangeProjection_mul (R : Matrix m n ℂ) (hR : Rᴴ*R = 1) :
    (rangeProjection R).mat*R = R := by
  change (R*Rᴴ)*R = R
  rw [Matrix.mul_assoc,hR,Matrix.mul_one]

theorem adjoint_complement_zero (R : Matrix m n ℂ) (hR : Rᴴ*R = 1) :
    Rᴴ*(1-(rangeProjection R).mat) = 0 := by
  change Rᴴ*(1-R*Rᴴ) = 0
  rw [Matrix.mul_sub,Matrix.mul_one,← Matrix.mul_assoc,hR,Matrix.one_mul,sub_self]

theorem embedded_orthogonal_complement (R : Matrix m n ℂ) (hR : Rᴴ*R = 1)
    (A : HermitianMat n ℂ) (W : HermitianMat m ℂ) :
    (A.conj R).mat*(W.conj (1-(rangeProjection R).mat)).mat = 0 := by
  let Q := 1-(rangeProjection R).mat
  have hz : Rᴴ*Q = 0 := adjoint_complement_zero R hR
  change (R*A.mat*Rᴴ)*(Q*W.mat*Qᴴ) = 0
  simp only [Matrix.mul_assoc,← Matrix.mul_assoc Rᴴ Q (W.mat*Qᴴ),hz,Matrix.zero_mul,Matrix.mul_zero]

theorem psi_embedded_add_complement (R : Matrix m n ℂ) (hR : Rᴴ*R = 1)
    (A : HermitianMat n ℂ) (W : HermitianMat m ℂ) :
    psi (A.conj R+W.conj (1-(rangeProjection R).mat)) =
      psi A+psi (W.conj (1-(rangeProjection R).mat)) := by
  rw [psi_add_of_mul_eq_zero _ _ (embedded_orthogonal_complement R hR A W),psi_isometry R hR]

def complementBlocks (R : Matrix r a ℂ) (S : Matrix s b ℂ) (W : Blocks r s) : Blocks r s :=
  (W.1.conj (1-(rangeProjection R).mat),W.2.conj (1-(rangeProjection S).mat))

theorem complementBlocks_mem_positiveCone (R : Matrix r a ℂ) (S : Matrix s b ℂ) {W : Blocks r s} (hW : W ∈ positiveCone) :
    complementBlocks R S W ∈ positiveCone :=
  ⟨hW.1.mul_mul_conjTranspose_same _,hW.2.mul_mul_conjTranspose_same _⟩

theorem block_complement_eq (R : Matrix r a ℂ) (S : Matrix s b ℂ) :
    blockEmbedding (1-(rangeProjection R).mat) (1-(rangeProjection S).mat) =
      1-(rangeProjection (blockEmbedding R S)).mat := by
  change Matrix.fromBlocks (1-R*Rᴴ) 0 0 (1-S*Sᴴ) =
    1-Matrix.fromBlocks R 0 0 S*(Matrix.fromBlocks R 0 0 S)ᴴ
  rw [Matrix.fromBlocks_conjTranspose,Matrix.fromBlocks_multiply]
  simp only [Matrix.conjTranspose_zero,Matrix.zero_mul,Matrix.mul_zero,add_zero,zero_add]
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks,Matrix.sub_apply,Matrix.one_apply]

theorem diagonal_complementBlocks (R : Matrix r a ℂ) (S : Matrix s b ℂ) (W : Blocks r s) :
    diagonal (complementBlocks R S W) =
      (diagonal W).conj (1-(rangeProjection (blockEmbedding R S)).mat) := by
  change diagonal (embedBlocks (1-(rangeProjection R).mat) (1-(rangeProjection S).mat) W) = _
  rw [diagonal_embedBlocks,block_complement_eq]

/-- Orthogonal entropy terms cancel, leaving the penalty on the discarded complement. -/
theorem objective_support_split (R : Matrix r a ℂ) (S : Matrix s b ℂ) (hR : Rᴴ*R = 1) (hS : Sᴴ*S = 1)
    (J : HermitianMat (a ⊕ b) ℂ) (lambda₀ lambda₁ : ℝ) (Z : Blocks a b) (W : Blocks r s) :
    objective (J.conj (blockEmbedding R S)) lambda₀ lambda₁ (embedBlocks R S Z+complementBlocks R S W) =
      objective J lambda₀ lambda₁ Z-linearPenalty lambda₀ lambda₁ (complementBlocks R S W) := by
  have hT := blockEmbedding_isometry R S hR hS
  have hd : diagonal (embedBlocks R S Z+complementBlocks R S W) =
      diagonal (embedBlocks R S Z)+diagonal (complementBlocks R S W) :=
    map_add diagonalCLM _ _
  rw [objective_eq,hd,diagonal_embedBlocks,diagonal_complementBlocks,
    psi_embedded_add_complement _ hT]
  have hsum : J.conj (blockEmbedding R S)+
      ((diagonal Z).conj (blockEmbedding R S)+(diagonal W).conj (1-(rangeProjection (blockEmbedding R S)).mat)) =
      (J+diagonal Z).conj (blockEmbedding R S)+(diagonal W).conj (1-(rangeProjection (blockEmbedding R S)).mat) := by
    rw [map_add,add_assoc]
  rw [hsum,psi_embedded_add_complement _ hT,objective_eq]
  change psi (diagonal Z)+psi ((diagonal W).conj (1-(rangeProjection (blockEmbedding R S)).mat))-
      (psi (J+diagonal Z)+psi ((diagonal W).conj (1-(rangeProjection (blockEmbedding R S)).mat)))-
      linearPenalty lambda₀ lambda₁ (embedBlocks R S Z+complementBlocks R S W) =
    psi (diagonal Z)-psi (J+diagonal Z)-linearPenalty lambda₀ lambda₁ Z-
      linearPenalty lambda₀ lambda₁ (complementBlocks R S W)
  simp only [map_add,linearPenalty_apply,embedBlocks,HermitianMat.conj_apply_mat,
    trace_isometry R hR,trace_isometry S hS]
  ring

end QubitAdditivity.BetaSupport
