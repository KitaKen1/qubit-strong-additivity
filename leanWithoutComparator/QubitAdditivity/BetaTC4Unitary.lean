import QubitAdditivity.BetaTC4Convex

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

namespace QubitAdditivity.BetaTC4Unitary
open BetaTC4Convex BetaDualBoundary BetaDual BetaDualConvex BetaDualInterior BetaDualDerivative BetaMinimizer BetaEntropy BetaDualValue BetaDualExistence

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

variable {k : Type*} [Fintype k] [DecidableEq k]
variable {r s : Type*} [Fintype r] [Fintype s] [DecidableEq r] [DecidableEq s]

/-- Independent changes of basis in the two block spaces. -/
def blockUnitary (U : Matrix.unitaryGroup r ℂ) (V : Matrix.unitaryGroup s ℂ) :
    Matrix.unitaryGroup (r ⊕ s) ℂ :=
  ⟨Matrix.fromBlocks U.val 0 0 V.val,by
    rw [Matrix.mem_unitaryGroup_iff,Matrix.star_eq_conjTranspose,Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply]
    have hU : U.val*U.valᴴ = 1 := U.prop.2
    have hV : V.val*V.valᴴ = 1 := V.prop.2
    simp only [Matrix.conjTranspose_zero,Matrix.zero_mul,Matrix.mul_zero,add_zero,zero_add,hU,hV]
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks,Matrix.one_apply]⟩

def conjugateBlocks (U : Matrix.unitaryGroup r ℂ) (V : Matrix.unitaryGroup s ℂ) (W : Blocks r s) : Blocks r s :=
  (W.1.conj U.val,W.2.conj V.val)

theorem diagonal_conjugateBlocks (U : Matrix.unitaryGroup r ℂ) (V : Matrix.unitaryGroup s ℂ) (W : Blocks r s) :
    diagonal (conjugateBlocks U V W) = (diagonal W).conj (blockUnitary U V).val := by
  apply HermitianMat.ext
  simp [BetaDual.diagonal,conjugateBlocks,HermitianMat.conj_apply_mat,blockUnitary,
    Matrix.fromBlocks_conjTranspose,Matrix.fromBlocks_multiply]

theorem pinching_conj (U : Matrix.unitaryGroup r ℂ) (V : Matrix.unitaryGroup s ℂ)
    (J : HermitianMat (r ⊕ s) ℂ) :
    pinching (J.conj (blockUnitary U V).val) = (pinching J).conj (blockUnitary U V).val := by
  have hl : pinchLeft (J.conj (blockUnitary U V).val) = (pinchLeft J).conj U.val := by
    apply HermitianMat.ext
    change ((blockUnitary U V).val*J.mat*(blockUnitary U V).valᴴ).submatrix Sum.inl Sum.inl =
      U.val*(J.mat.submatrix Sum.inl Sum.inl)*U.valᴴ
    ext i j
    simp [pinchLeft,HermitianMat.conj_apply_mat,blockUnitary,Matrix.submatrix_apply,
      Matrix.mul_apply,Fintype.sum_sum_type,Matrix.fromBlocks,Matrix.conjTranspose_apply]
  have hr : pinchRight (J.conj (blockUnitary U V).val) = (pinchRight J).conj V.val := by
    apply HermitianMat.ext
    change ((blockUnitary U V).val*J.mat*(blockUnitary U V).valᴴ).submatrix Sum.inr Sum.inr =
      V.val*(J.mat.submatrix Sum.inr Sum.inr)*V.valᴴ
    ext i j
    simp [pinchRight,HermitianMat.conj_apply_mat,blockUnitary,Matrix.submatrix_apply,
      Matrix.mul_apply,Fintype.sum_sum_type,Matrix.fromBlocks,Matrix.conjTranspose_apply]
  change diagonal (pinchLeft (J.conj (blockUnitary U V).val),pinchRight (J.conj (blockUnitary U V).val)) = _
  rw [hl,hr]
  exact diagonal_conjugateBlocks U V (pinchLeft J,pinchRight J)

theorem psi_conj_unitary (U : Matrix.unitaryGroup k ℂ) (J : HermitianMat k ℂ) :
    psi (J.conj U.val) = psi J := by
  unfold psi
  exact congrArg Neg.neg (OpenAIEntropy.entropy_unitary_conj U J.H)

theorem trace_conj_unitary (U : Matrix.unitaryGroup k ℂ) (J : HermitianMat k ℂ) :
    (J.conj U.val).mat.trace.re = J.mat.trace.re := by
  exact congrArg Complex.re (OpenAIEntropy.trace_unitary_conj U J.mat)

theorem conjugateBlocks_mem_positiveCone (U : Matrix.unitaryGroup r ℂ) (V : Matrix.unitaryGroup s ℂ)
    {W : Blocks r s} (hW : W ∈ positiveCone) : conjugateBlocks U V W ∈ positiveCone :=
  ⟨hW.1.mul_mul_conjTranspose_same U.val,hW.2.mul_mul_conjTranspose_same V.val⟩

theorem conjugateBlocks_inverse (U : Matrix.unitaryGroup r ℂ) (V : Matrix.unitaryGroup s ℂ) (W : Blocks r s) :
    conjugateBlocks U V (conjugateBlocks (star U) (star V) W) = W := by
  apply Prod.ext
  · change (W.1.conj (star U).val).conj U.val = W.1
    rw [HermitianMat.conj_conj]
    have he : U.val*(star U).val = 1 := Unitary.coe_mul_star_self U
    rw [he,HermitianMat.conj_one]
  · change (W.2.conj (star V).val).conj V.val = W.2
    rw [HermitianMat.conj_conj]
    have he : V.val*(star V).val = 1 := Unitary.coe_mul_star_self V
    rw [he,HermitianMat.conj_one]

/-- The entire objective, including the penalty, is invariant under block unitary conjugation. -/
theorem objective_conj (U : Matrix.unitaryGroup r ℂ) (V : Matrix.unitaryGroup s ℂ)
    (J : HermitianMat (r ⊕ s) ℂ) (lambda₀ lambda₁ : ℝ) (W : Blocks r s) :
    objective (J.conj (blockUnitary U V).val) lambda₀ lambda₁ (conjugateBlocks U V W) =
      objective J lambda₀ lambda₁ W := by
  rw [objective_eq,diagonal_conjugateBlocks,← map_add,psi_conj_unitary,psi_conj_unitary,objective_eq]
  change psi (diagonal W)-psi (J+diagonal W)-
    (lambda₀*(W.1.conj U.val).mat.trace.re+lambda₁*(W.2.conj V.val).mat.trace.re) = _
  rw [trace_conj_unitary,trace_conj_unitary]

/-- Conjugating a certified minimum gives a certified minimum; its choice need not be equivariant. -/
theorem isMinOn_conj (U : Matrix.unitaryGroup r ℂ) (V : Matrix.unitaryGroup s ℂ)
    {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ} {W : Blocks r s}
    (hmin : IsMinOn (objective J lambda₀ lambda₁) positiveCone W) :
    IsMinOn (objective (J.conj (blockUnitary U V).val) lambda₀ lambda₁) positiveCone (conjugateBlocks U V W) := by
  intro Z hZ
  change objective (J.conj (blockUnitary U V).val) lambda₀ lambda₁ (conjugateBlocks U V W) ≤
    objective (J.conj (blockUnitary U V).val) lambda₀ lambda₁ Z
  have hi := hmin (conjugateBlocks_mem_positiveCone (star U) (star V) hZ)
  rw [objective_conj,← conjugateBlocks_inverse U V Z,objective_conj]
  exact hi

theorem minimumValue_conj (U : Matrix.unitaryGroup r ℂ) (V : Matrix.unitaryGroup s ℂ)
    {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosSemidef) (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) :
    minimumValue (J.conj (blockUnitary U V).val) lambda₀ lambda₁ = minimumValue J lambda₀ lambda₁ := by
  have hs := minimizer_spec_psd hJ hl₀ hl₁
  rw [minimumValue_eq_of_isMinOn (hJ.mul_mul_conjTranspose_same _) hl₀ hl₁
    (conjugateBlocks_mem_positiveCone U V hs.1) (isMinOn_conj U V hs.2),objective_conj]
  rfl

theorem value_conj (U : Matrix.unitaryGroup r ℂ) (V : Matrix.unitaryGroup s ℂ)
    {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosSemidef) (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) :
    value (J.conj (blockUnitary U V).val) lambda₀ lambda₁ = value J lambda₀ lambda₁ := by
  rw [value,pinching_conj,psi_conj_unitary,minimumValue_conj U V hJ hl₀ hl₁]
  rfl

end QubitAdditivity.BetaTC4Unitary

