import QubitAdditivity.BetaSupport

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius

namespace QubitAdditivity.BetaSupportMinimum
open BetaDual BetaEntropy BetaDualValue BetaIsometryEntropy BetaBlockIsometry BetaOrthogonalEntropy BetaReflection BetaSupport
open BetaDualBoundary BetaTC4Convex BetaTC4Unitary

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

theorem reflection_mul_isometry (R : Matrix r a ℂ) (hR : Rᴴ*R = 1) :
    (reflection (rangeProjection R) (rangeProjection_sq R hR)).val*R = R := by
  rw [reflection_val,Matrix.sub_mul,Matrix.smul_mul,Matrix.one_mul,rangeProjection_mul R hR]
  module

theorem embed_compress_eq (R : Matrix r a ℂ) (S : Matrix s b ℂ) (W : Blocks r s) :
    embedBlocks R S (compressBlocks R S W) =
      (W.1.conj (rangeProjection R).mat,W.2.conj (rangeProjection S).mat) := by
  apply Prod.ext
  · change (W.1.conj Rᴴ).conj R = W.1.conj (R*Rᴴ)
    rw [HermitianMat.conj_conj]
  · change (W.2.conj Sᴴ).conj S = W.2.conj (S*Sᴴ)
    rw [HermitianMat.conj_conj]

/-- A block reflection fixes every matrix supported on the embedded block space. -/
theorem block_reflection_fix (R : Matrix r a ℂ) (S : Matrix s b ℂ) (hR : Rᴴ*R = 1) (hS : Sᴴ*S = 1)
    (J : HermitianMat (a ⊕ b) ℂ) :
    (J.conj (blockEmbedding R S)).conj
      (blockUnitary (reflection (rangeProjection R) (rangeProjection_sq R hR))
        (reflection (rangeProjection S) (rangeProjection_sq S hS))).val = J.conj (blockEmbedding R S) := by
  have he : (blockUnitary (reflection (rangeProjection R) (rangeProjection_sq R hR))
      (reflection (rangeProjection S) (rangeProjection_sq S hS))).val*blockEmbedding R S = blockEmbedding R S := by
    change Matrix.fromBlocks _ 0 0 _*Matrix.fromBlocks R 0 0 S = Matrix.fromBlocks R 0 0 S
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul,Matrix.mul_zero,add_zero,zero_add,reflection_mul_isometry R hR,reflection_mul_isometry S hS]
  rw [HermitianMat.conj_conj,he]

/-- The average equals a lifted compression plus its PSD complement. -/
theorem block_reflection_average (R : Matrix r a ℂ) (S : Matrix s b ℂ) (hR : Rᴴ*R = 1) (hS : Sᴴ*S = 1)
    (W : Blocks r s) :
    (1/2 : ℝ) • (W+conjugateBlocks (reflection (rangeProjection R) (rangeProjection_sq R hR))
      (reflection (rangeProjection S) (rangeProjection_sq S hS)) W) =
      embedBlocks R S (compressBlocks R S W)+complementBlocks R S W := by
  rw [embed_compress_eq]
  apply Prod.ext
  · apply HermitianMat.ext
    change ((1/2 : ℝ) • (W.1+W.1.conj (reflection (rangeProjection R) (rangeProjection_sq R hR)).val)).mat =
      (W.1.conj (rangeProjection R).mat+W.1.conj (1-(rangeProjection R).mat)).mat
    rw [reflection_average]
    simp only [HermitianMat.mat_add,HermitianMat.conj_apply_mat,(rangeProjection R).H.eq,
      Matrix.conjTranspose_sub,Matrix.conjTranspose_one]
  · apply HermitianMat.ext
    change ((1/2 : ℝ) • (W.2+W.2.conj (reflection (rangeProjection S) (rangeProjection_sq S hS)).val)).mat =
      (W.2.conj (rangeProjection S).mat+W.2.conj (1-(rangeProjection S).mat)).mat
    rw [reflection_average]
    simp only [HermitianMat.mat_add,HermitianMat.conj_apply_mat,(rangeProjection S).H.eq,
      Matrix.conjTranspose_sub,Matrix.conjTranspose_one]

/-- Convexity and reflection invariance show that discarding the cross terms cannot increase F. -/
theorem objective_average_le (R : Matrix r a ℂ) (S : Matrix s b ℂ) (hR : Rᴴ*R = 1) (hS : Sᴴ*S = 1)
    {J : HermitianMat (a ⊕ b) ℂ} (hJ : J.mat.PosSemidef) (lambda₀ lambda₁ : ℝ)
    {W : Blocks r s} (hW : W ∈ positiveCone) :
    objective (J.conj (blockEmbedding R S)) lambda₀ lambda₁
        (embedBlocks R S (compressBlocks R S W)+complementBlocks R S W) ≤
      objective (J.conj (blockEmbedding R S)) lambda₀ lambda₁ W := by
  let U := reflection (rangeProjection R) (rangeProjection_sq R hR)
  let V := reflection (rangeProjection S) (rangeProjection_sq S hS)
  have hc := convexOn_objective_psd (J := J.conj (blockEmbedding R S)) lambda₀ lambda₁
    (hJ.mul_mul_conjTranspose_same (blockEmbedding R S))
  have hi := hc.2 hW (conjugateBlocks_mem_positiveCone U V hW)
    (show 0 ≤ (1/2 : ℝ) by norm_num) (show 0 ≤ (1/2 : ℝ) by norm_num) (by norm_num)
  have he := objective_conj U V (J.conj (blockEmbedding R S)) lambda₀ lambda₁ W
  rw [block_reflection_fix R S hR hS J] at he
  rw [← smul_add,block_reflection_average R S hR hS W,he] at hi
  simp only [smul_eq_mul] at hi
  linarith


/-- The penalty on a PSD complement is nonpositive for negative dual coefficients. -/
theorem linearPenalty_nonpos {lambda₀ lambda₁ : ℝ} (hl₀ : lambda₀ ≤ 0) (hl₁ : lambda₁ ≤ 0)
    {W : Blocks r s} (hW : W ∈ positiveCone) : linearPenalty lambda₀ lambda₁ W ≤ 0 := by
  have ht₀ : 0 ≤ W.1.mat.trace.re := (RCLike.nonneg_iff.mp hW.1.trace_nonneg).1
  have ht₁ : 0 ≤ W.2.mat.trace.re := (RCLike.nonneg_iff.mp hW.2.trace_nonneg).1
  rw [linearPenalty_apply]
  exact add_nonpos (mul_nonpos_of_nonpos_of_nonneg hl₀ ht₀) (mul_nonpos_of_nonpos_of_nonneg hl₁ ht₁)

/-- Compression to the input support decreases the true dual objective. -/
theorem objective_compression_le (R : Matrix r a ℂ) (S : Matrix s b ℂ) (hR : Rᴴ*R = 1) (hS : Sᴴ*S = 1)
    {J : HermitianMat (a ⊕ b) ℂ} (hJ : J.mat.PosSemidef) {lambda₀ lambda₁ : ℝ}
    (hl₀ : lambda₀ ≤ 0) (hl₁ : lambda₁ ≤ 0) {W : Blocks r s} (hW : W ∈ positiveCone) :
    objective J lambda₀ lambda₁ (compressBlocks R S W) ≤
      objective (J.conj (blockEmbedding R S)) lambda₀ lambda₁ W := by
  have hi := objective_average_le R S hR hS hJ lambda₀ lambda₁ hW
  rw [objective_support_split R S hR hS] at hi
  have hp := linearPenalty_nonpos hl₀ hl₁ (complementBlocks_mem_positiveCone R S hW)
  linarith

/-- The actual infimum is preserved by independent rectangular block isometries. -/
theorem minimumValue_embed (R : Matrix r a ℂ) (S : Matrix s b ℂ) (hR : Rᴴ*R = 1) (hS : Sᴴ*S = 1)
    {J : HermitianMat (a ⊕ b) ℂ} (hJ : J.mat.PosSemidef) {lambda₀ lambda₁ : ℝ}
    (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) :
    minimumValue (J.conj (blockEmbedding R S)) lambda₀ lambda₁ = minimumValue J lambda₀ lambda₁ := by
  have hs := minimizer_spec_psd hJ hl₀ hl₁
  have hm : IsMinOn (objective (J.conj (blockEmbedding R S)) lambda₀ lambda₁) positiveCone
      (embedBlocks R S (BetaMinimizer.minimizer J lambda₀ lambda₁)) := by
    intro W hW
    change objective (J.conj (blockEmbedding R S)) lambda₀ lambda₁
      (embedBlocks R S (BetaMinimizer.minimizer J lambda₀ lambda₁)) ≤
        objective (J.conj (blockEmbedding R S)) lambda₀ lambda₁ W
    rw [objective_embed R S hR hS]
    have hi : objective J lambda₀ lambda₁ (BetaMinimizer.minimizer J lambda₀ lambda₁) ≤
        objective J lambda₀ lambda₁ (compressBlocks R S W) :=
      hs.2 (compressBlocks_mem_positiveCone R S hW)
    exact hi.trans (objective_compression_le R S hR hS hJ hl₀.le hl₁.le hW)
  have he := minimumValue_eq_of_isMinOn (J := J.conj (blockEmbedding R S))
    (hJ.mul_mul_conjTranspose_same (blockEmbedding R S)) hl₀ hl₁
    (embedBlocks_mem_positiveCone R S hs.1) hm
  rw [objective_embed R S hR hS] at he
  exact he

/-- The complete dual value is invariant under block isometric embedding, including zero padding. -/
theorem value_embed (R : Matrix r a ℂ) (S : Matrix s b ℂ) (hR : Rᴴ*R = 1) (hS : Sᴴ*S = 1)
    {J : HermitianMat (a ⊕ b) ℂ} (hJ : J.mat.PosSemidef) {lambda₀ lambda₁ : ℝ}
    (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) :
    value (J.conj (blockEmbedding R S)) lambda₀ lambda₁ = value J lambda₀ lambda₁ := by
  rw [value,value,psi_pinching_embed R S hR hS,minimumValue_embed R S hR hS hJ hl₀ hl₁]

end QubitAdditivity.BetaSupportMinimum
