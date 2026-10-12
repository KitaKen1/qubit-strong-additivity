import QubitAdditivity.BetaIsometryEntropy

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius

namespace QubitAdditivity.BetaBlockIsometry
open BetaDual BetaEntropy BetaDualValue BetaIsometryEntropy

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

variable {r s a b : Type*} [Fintype r] [Fintype s] [Fintype a] [Fintype b]
  [DecidableEq r] [DecidableEq s] [DecidableEq a] [DecidableEq b]

def blockEmbedding (R : Matrix r a ℂ) (S : Matrix s b ℂ) : Matrix (r ⊕ s) (a ⊕ b) ℂ :=
  Matrix.fromBlocks R 0 0 S

theorem blockEmbedding_isometry (R : Matrix r a ℂ) (S : Matrix s b ℂ) (hR : Rᴴ*R = 1) (hS : Sᴴ*S = 1) :
    (blockEmbedding R S)ᴴ*blockEmbedding R S = 1 := by
  rw [blockEmbedding,Matrix.fromBlocks_conjTranspose,Matrix.fromBlocks_multiply]
  simp only [Matrix.conjTranspose_zero,Matrix.zero_mul,Matrix.mul_zero,add_zero,zero_add,hR,hS]
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks,Matrix.one_apply]

def embedBlocks (R : Matrix r a ℂ) (S : Matrix s b ℂ) (W : Blocks a b) : Blocks r s :=
  (W.1.conj R,W.2.conj S)

def compressBlocks (R : Matrix r a ℂ) (S : Matrix s b ℂ) (W : Blocks r s) : Blocks a b :=
  (W.1.conj Rᴴ,W.2.conj Sᴴ)

theorem diagonal_embedBlocks (R : Matrix r a ℂ) (S : Matrix s b ℂ) (W : Blocks a b) :
    diagonal (embedBlocks R S W) = (diagonal W).conj (blockEmbedding R S) := by
  apply HermitianMat.ext
  simp [BetaDual.diagonal,embedBlocks,HermitianMat.conj_apply_mat,blockEmbedding,
    Matrix.fromBlocks_conjTranspose,Matrix.fromBlocks_multiply]

theorem embedBlocks_mem_positiveCone (R : Matrix r a ℂ) (S : Matrix s b ℂ) {W : Blocks a b} (hW : W ∈ positiveCone) :
    embedBlocks R S W ∈ positiveCone :=
  ⟨hW.1.mul_mul_conjTranspose_same R,hW.2.mul_mul_conjTranspose_same S⟩

theorem compressBlocks_mem_positiveCone (R : Matrix r a ℂ) (S : Matrix s b ℂ) {W : Blocks r s} (hW : W ∈ positiveCone) :
    compressBlocks R S W ∈ positiveCone :=
  ⟨hW.1.mul_mul_conjTranspose_same Rᴴ,hW.2.mul_mul_conjTranspose_same Sᴴ⟩

theorem pinching_embed (R : Matrix r a ℂ) (S : Matrix s b ℂ) (J : HermitianMat (a ⊕ b) ℂ) :
    pinching (J.conj (blockEmbedding R S)) = (pinching J).conj (blockEmbedding R S) := by
  have hl : pinchLeft (J.conj (blockEmbedding R S)) = (pinchLeft J).conj R := by
    apply HermitianMat.ext
    change ((blockEmbedding R S)*J.mat*(blockEmbedding R S)ᴴ).submatrix Sum.inl Sum.inl =
      R*(J.mat.submatrix Sum.inl Sum.inl)*Rᴴ
    ext i j
    simp [blockEmbedding,Matrix.submatrix_apply,Matrix.mul_apply,Fintype.sum_sum_type,
      Matrix.fromBlocks,Matrix.conjTranspose_apply]
  have hr : pinchRight (J.conj (blockEmbedding R S)) = (pinchRight J).conj S := by
    apply HermitianMat.ext
    change ((blockEmbedding R S)*J.mat*(blockEmbedding R S)ᴴ).submatrix Sum.inr Sum.inr =
      S*(J.mat.submatrix Sum.inr Sum.inr)*Sᴴ
    ext i j
    simp [blockEmbedding,Matrix.submatrix_apply,Matrix.mul_apply,Fintype.sum_sum_type,
      Matrix.fromBlocks,Matrix.conjTranspose_apply]
  change diagonal (pinchLeft (J.conj (blockEmbedding R S)),pinchRight (J.conj (blockEmbedding R S))) = _
  rw [hl,hr]
  exact diagonal_embedBlocks R S (pinchLeft J,pinchRight J)

theorem psi_pinching_embed (R : Matrix r a ℂ) (S : Matrix s b ℂ) (hR : Rᴴ*R = 1) (hS : Sᴴ*S = 1)
    (J : HermitianMat (a ⊕ b) ℂ) :
    psi (pinching (J.conj (blockEmbedding R S))) = psi (pinching J) := by
  rw [pinching_embed]
  exact psi_isometry _ (blockEmbedding_isometry R S hR hS) _

/-- Embedding a candidate preserves the entire objective and its linear trace penalty. -/
theorem objective_embed (R : Matrix r a ℂ) (S : Matrix s b ℂ) (hR : Rᴴ*R = 1) (hS : Sᴴ*S = 1)
    (J : HermitianMat (a ⊕ b) ℂ) (lambda₀ lambda₁ : ℝ) (W : Blocks a b) :
    objective (J.conj (blockEmbedding R S)) lambda₀ lambda₁ (embedBlocks R S W) = objective J lambda₀ lambda₁ W := by
  rw [objective_eq,diagonal_embedBlocks,← map_add,psi_isometry _ (blockEmbedding_isometry R S hR hS),
    psi_isometry _ (blockEmbedding_isometry R S hR hS),objective_eq]
  change psi (diagonal W)-psi (J+diagonal W)-
    (lambda₀*(R*W.1.mat*Rᴴ).trace.re+lambda₁*(S*W.2.mat*Sᴴ).trace.re) = _
  rw [trace_isometry R hR,trace_isometry S hS]

end QubitAdditivity.BetaBlockIsometry
