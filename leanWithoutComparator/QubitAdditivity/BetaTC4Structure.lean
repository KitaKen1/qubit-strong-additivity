import QubitAdditivity.BetaTC4Convex
import QubitAdditivity.Imported.EntropyScaling

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

namespace QubitAdditivity.BetaTC4Structure
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

@[simp] theorem psi_zero : psi (0 : HermitianMat k ℂ) = 0 := by
  rw [psi_eq_trace]
  simp

/-- Entropy homogeneity includes the trace correction, including c=0. -/
theorem psi_smul (c : ℝ) (A : HermitianMat k ℂ) :
    psi (c • A) = c*psi A-Real.negMulLog c*A.mat.trace.re := by
  unfold psi
  rw [HermitianMat.mat_smul,OpenAIEntropy.entropy_smul c A.H]
  ring

theorem trace_pinching (J : HermitianMat (r ⊕ s) ℂ) : (pinching J).mat.trace.re = J.mat.trace.re := by
  simp [pinching,BetaDualDerivative.pinchCLM,BetaDualDerivative.pinchLM,
    BetaDual.diagonal,BetaDual.pinchLeft,BetaDual.pinchRight,Matrix.trace,
    Fintype.sum_sum_type,Matrix.fromBlocks,Matrix.submatrix]

theorem trace_diagonal (W : Blocks r s) : (diagonal W).mat.trace.re = W.1.mat.trace.re+W.2.mat.trace.re := by
  simp [BetaDual.diagonal,Matrix.trace,Fintype.sum_sum_type,Matrix.fromBlocks]

/-- Simultaneous scaling leaves only the input-trace correction in F. -/
theorem objective_smul (c : ℝ) (J : HermitianMat (r ⊕ s) ℂ) (lambda₀ lambda₁ : ℝ) (W : Blocks r s) :
    objective (c • J) lambda₀ lambda₁ (c • W) =
      c*objective J lambda₀ lambda₁ W+Real.negMulLog c*J.mat.trace.re := by
  have he : c • J+diagonal (c • W) = c • (J+diagonal W) := by
    rw [← diagonalCLM_apply, map_smul,diagonalCLM_apply,smul_add]
  rw [objective_eq,he,← diagonalCLM_apply,map_smul,diagonalCLM_apply,psi_smul,psi_smul,
    objective_eq,trace_diagonal]
  simp only [Prod.smul_fst,Prod.smul_snd,HermitianMat.mat_smul,Matrix.trace_smul,
    HermitianMat.mat_add,Matrix.trace_add,Complex.add_re,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,trace_diagonal]
  ring

theorem smul_mem_positiveCone {c : ℝ} (hc : 0 ≤ c) {W : Blocks r s} (hW : W ∈ positiveCone) :
    c • W ∈ positiveCone := by
  constructor
  · exact hW.1.smul hc
  · exact hW.2.smul hc

/-- Minima transform by positive scaling, with no uniqueness at singular J. -/
theorem isMinOn_smul {c : ℝ} (hc : 0 < c) {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    {W : Blocks r s} (hmin : IsMinOn (objective J lambda₀ lambda₁) positiveCone W) :
    IsMinOn (objective (c • J) lambda₀ lambda₁) positiveCone (c • W) := by
  intro Z hZ
  change objective (c • J) lambda₀ lambda₁ (c • W) ≤ objective (c • J) lambda₀ lambda₁ Z
  have hi := mul_le_mul_of_nonneg_left (hmin (smul_mem_positiveCone (inv_pos.mpr hc).le hZ)) hc.le
  have he : c • (c⁻¹ • Z) = Z := by rw [smul_smul,mul_inv_cancel₀ hc.ne',one_smul]
  rw [objective_smul,← he,objective_smul]
  exact add_le_add hi le_rfl

theorem minimumValue_smul_pos {c : ℝ} (hc : 0 < c) {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosSemidef) (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) :
    minimumValue (c • J) lambda₀ lambda₁ =
      c*minimumValue J lambda₀ lambda₁+Real.negMulLog c*J.mat.trace.re := by
  have hs := minimizer_spec_psd hJ hl₀ hl₁
  rw [minimumValue_eq_of_isMinOn (by exact hJ.smul hc.le) hl₀ hl₁
    (smul_mem_positiveCone hc.le hs.1) (isMinOn_smul hc hs.2),objective_smul]
  rfl

/-- Cancellation of the trace corrections gives genuine degree-one homogeneity of g. -/
theorem value_smul_pos {c : ℝ} (hc : 0 < c) {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosSemidef) (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) :
    value (c • J) lambda₀ lambda₁ = c*value J lambda₀ lambda₁ := by
  unfold value
  rw [map_smul,psi_smul,minimumValue_smul_pos hc hJ hl₀ hl₁,trace_pinching]
  ring

theorem objective_zero (lambda₀ lambda₁ : ℝ) (W : Blocks r s) :
    objective (0 : HermitianMat (r ⊕ s) ℂ) lambda₀ lambda₁ W = -linearPenalty lambda₀ lambda₁ W := by
  rw [objective_eq,zero_add,sub_self,zero_sub,linearPenalty_apply]

theorem isMinOn_zero {lambda₀ lambda₁ : ℝ} (hl₀ : lambda₀ ≤ 0) (hl₁ : lambda₁ ≤ 0) :
    IsMinOn (objective (0 : HermitianMat (r ⊕ s) ℂ) lambda₀ lambda₁) positiveCone 0 := by
  intro W hW
  change objective (0 : HermitianMat (r ⊕ s) ℂ) lambda₀ lambda₁ 0 ≤ objective 0 lambda₀ lambda₁ W
  rw [objective_zero,objective_zero,map_zero,neg_zero]
  have h₀ := mul_nonpos_of_nonpos_of_nonneg hl₀ (le_trans (norm_nonneg _) (norm_le_trace hW.1))
  have h₁ := mul_nonpos_of_nonpos_of_nonneg hl₁ (le_trans (norm_nonneg _) (norm_le_trace hW.2))
  change 0 ≤ -(lambda₀*W.1.mat.trace.re+lambda₁*W.2.mat.trace.re)
  linarith

theorem minimumValue_zero {lambda₀ lambda₁ : ℝ} (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) :
    minimumValue (0 : HermitianMat (r ⊕ s) ℂ) lambda₀ lambda₁ = 0 := by
  rw [minimumValue_eq_of_isMinOn (J := 0) (by change (0 : Matrix (r ⊕ s) (r ⊕ s) ℂ).PosSemidef; exact Matrix.PosSemidef.zero) hl₀ hl₁
    (show (0 : Blocks r s) ∈ positiveCone from ⟨Matrix.PosSemidef.zero,Matrix.PosSemidef.zero⟩)
    (isMinOn_zero hl₀.le hl₁.le),objective_zero,map_zero,neg_zero]

theorem value_zero {lambda₀ lambda₁ : ℝ} (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) :
    value (0 : HermitianMat (r ⊕ s) ℂ) lambda₀ lambda₁ = 0 := by
  rw [value,map_zero,psi_zero,minimumValue_zero hl₀ hl₁,zero_add]

theorem value_smul {c : ℝ} (hc : 0 ≤ c) {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosSemidef) (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) :
    value (c • J) lambda₀ lambda₁ = c*value J lambda₀ lambda₁ := by
  by_cases he : c = 0
  · rw [he,zero_smul,value_zero hl₀ hl₁,zero_mul]
  · exact value_smul_pos (lt_of_le_of_ne hc (Ne.symm he)) hJ hl₀ hl₁

/-- Concavity and exact homogeneity give the finite-decomposition comparison step. -/
theorem value_add_ge {J K : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosSemidef) (hK : K.mat.PosSemidef) (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) :
    value J lambda₀ lambda₁+value K lambda₀ lambda₁ ≤ value (J+K) lambda₀ lambda₁ := by
  have hi : (1/2 : ℝ)*value J lambda₀ lambda₁+(1/2 : ℝ)*value K lambda₀ lambda₁ ≤
      value ((1/2 : ℝ) • J+(1/2 : ℝ) • K) lambda₀ lambda₁ :=
    (concaveOn_value_psd hl₀ hl₁).2 hJ hK (by norm_num) (by norm_num) (by norm_num)
  rw [← smul_add,value_smul (J := J+K) (by norm_num : 0 ≤ (1/2 : ℝ)) (hJ.add hK) hl₀ hl₁] at hi
  linarith

/-- Finite PSD sums stay in the input cone. -/
theorem sum_posSemidef {ι : Type*} (t : Finset ι) (J : ι → HermitianMat (r ⊕ s) ℂ)
    (hJ : ∀ i ∈ t, (J i).mat.PosSemidef) : (∑ i ∈ t, J i).mat.PosSemidef := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using (Matrix.PosSemidef.zero (n := r ⊕ s) (R := ℂ))
  | @insert i t hi ih =>
    rw [Finset.sum_insert hi]
    exact (hJ i (Finset.mem_insert_self _ _)).add (ih (fun j hj => hJ j (Finset.mem_insert_of_mem hj)))

/-- A Gram decomposition can be compared term by term without normalizing zero summands. -/
theorem sum_value_le_value_sum {ι : Type*} (t : Finset ι) (J : ι → HermitianMat (r ⊕ s) ℂ)
    {lambda₀ lambda₁ : ℝ} (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0)
    (hJ : ∀ i ∈ t, (J i).mat.PosSemidef) :
    ∑ i ∈ t, value (J i) lambda₀ lambda₁ ≤ value (∑ i ∈ t, J i) lambda₀ lambda₁ := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [value_zero hl₀ hl₁]
  | @insert i t hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    have hs := ih (fun j hj => hJ j (Finset.mem_insert_of_mem hj))
    exact (add_le_add le_rfl hs).trans (value_add_ge (hJ i (Finset.mem_insert_self _ _))
      (sum_posSemidef t J (fun j hj => hJ j (Finset.mem_insert_of_mem hj))) hl₀ hl₁)

end QubitAdditivity.BetaTC4Structure




