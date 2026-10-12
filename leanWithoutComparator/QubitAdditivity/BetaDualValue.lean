import QubitAdditivity.BetaMinimizer

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

namespace QubitAdditivity.BetaDualValue
open BetaDual BetaDualConvex BetaDualInterior BetaDualDerivative BetaMinimizer BetaEntropy

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



variable {r s : Type*} [Fintype r] [Fintype s] [DecidableEq r] [DecidableEq s]

def objectiveJointDerivative (J : HermitianMat (r ⊕ s) ℂ) (lambda₀ lambda₁ : ℝ) (W : Blocks r s) :
    (HermitianMat (r ⊕ s) ℂ × Blocks r s) →L[ℝ] ℝ :=
  (-(psiGradient (J+BetaDual.diagonal W).mat)).comp (ContinuousLinearMap.fst ℝ _ _)+
    (gradient J lambda₀ lambda₁ W).comp (ContinuousLinearMap.snd ℝ _ _)

theorem hasFDerivAt_jointObjective (lambda₀ lambda₁ : ℝ)
    {J : HermitianMat (r ⊕ s) ℂ} {W : Blocks r s} (hA : W.1.mat.PosDef) (hB : W.2.mat.PosDef)
    (hT : (J+BetaDual.diagonal W).mat.PosDef) :
    HasFDerivAt (fun X : HermitianMat (r ⊕ s) ℂ × Blocks r s => objective X.1 lambda₀ lambda₁ X.2)
      (objectiveJointDerivative J lambda₀ lambda₁ W) (J,W) := by
  let S := (diagonalCLM (r := r) (s := s)).comp
    (ContinuousLinearMap.snd ℝ (HermitianMat (r ⊕ s) ℂ) (Blocks r s))
  let L := (ContinuousLinearMap.fst ℝ (HermitianMat (r ⊕ s) ℂ) (Blocks r s))+S
  have hdW := (hasFDerivAt_psi (A := BetaDual.diagonal W) (BetaBlocks.diagonal_posDef hA hB)).comp (J,W) S.hasFDerivAt
  have hdT := (hasFDerivAt_psi hT).comp (J,W) L.hasFDerivAt
  have hp := (linearPenalty lambda₀ lambda₁).hasFDerivAt.comp (J,W)
    (ContinuousLinearMap.snd ℝ (HermitianMat (r ⊕ s) ℂ) (Blocks r s)).hasFDerivAt
  convert! (hdW.sub hdT).sub hp using 1
  · ext X
    exact objective_eq X.1 lambda₀ lambda₁ X.2
  · apply ContinuousLinearMap.ext
    intro X
    change -psiGradient (J+BetaDual.diagonal W).mat X.1+gradient J lambda₀ lambda₁ W X.2 =
      psiGradient (BetaDual.diagonal W).mat (BetaDual.diagonal X.2)-
        psiGradient (J+BetaDual.diagonal W).mat (X.1+BetaDual.diagonal X.2)-linearPenalty lambda₀ lambda₁ X.2
    rw [gradient_diagonal,map_add]
    simp only [ContinuousLinearMap.comp_apply,_root_.sub_apply,diagonalCLM_apply]
    ring

/-- The actual minimized term, with the certified global cone minimizer. -/
def minimumValue (J : HermitianMat (r ⊕ s) ℂ) (lambda₀ lambda₁ : ℝ) : ℝ :=
  objective J lambda₀ lambda₁ (minimizer J lambda₀ lambda₁)

def minimumValueGradient (J : HermitianMat (r ⊕ s) ℂ) (lambda₀ lambda₁ : ℝ) :
    HermitianMat (r ⊕ s) ℂ →L[ℝ] ℝ := -psiGradient (J+BetaDual.diagonal (minimizer J lambda₀ lambda₁)).mat

/-- The envelope derivative follows from the real minimizer derivative and stationarity. -/
theorem hasFDerivAt_minimumValue {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosDef) (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) :
    HasFDerivAt (fun K : HermitianMat (r ⊕ s) ℂ => minimumValue K lambda₀ lambda₁)
      (minimumValueGradient J lambda₀ lambda₁) J := by
  have hW := minimizer_positiveInterior hJ hl₀ hl₁
  have hd := (hasFDerivAt_jointObjective lambda₀ lambda₁ hW.1 hW.2
    (total_posDef hJ hW.1 hW.2)).comp J
    ((hasFDerivAt_id J).prodMk (hasStrictFDerivAt_minimizer hJ hl₀ hl₁).hasFDerivAt)
  have hz : gradient J lambda₀ lambda₁ (minimizer J lambda₀ lambda₁) = 0 := by
    rw [gradient_eq_blockPairing,minimizer_stationary hJ hl₀ hl₁,map_zero]
  convert! hd using 1
  apply ContinuousLinearMap.ext
  intro H
  simp [objectiveJointDerivative,hz,minimumValueGradient]

theorem continuousAt_minimumValue {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosDef) (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) :
    ContinuousAt (fun K : HermitianMat (r ⊕ s) ℂ => minimumValue K lambda₀ lambda₁) J :=
  (hasFDerivAt_minimumValue hJ hl₀ hl₁).continuousAt

def totalDerivative (J : HermitianMat (r ⊕ s) ℂ) (lambda₀ lambda₁ : ℝ) :
    HermitianMat (r ⊕ s) ℂ →L[ℝ] HermitianMat (r ⊕ s) ℂ :=
  ContinuousLinearMap.id ℝ _+diagonalCLM.comp (minimizerDerivative J lambda₀ lambda₁)

def minimumValueHessianRow (J : HermitianMat (r ⊕ s) ℂ) (lambda₀ lambda₁ : ℝ)
    (H : HermitianMat (r ⊕ s) ℂ) : HermitianMat (r ⊕ s) ℂ →L[ℝ] ℝ :=
  -(psiHessianRow (J+BetaDual.diagonal (minimizer J lambda₀ lambda₁)).mat H).comp
    (totalDerivative J lambda₀ lambda₁)

theorem hasFDerivAt_minimumValueGradient_row {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosDef) (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) (H : HermitianMat (r ⊕ s) ℂ) :
    HasFDerivAt (fun K : HermitianMat (r ⊕ s) ℂ => minimumValueGradient K lambda₀ lambda₁ H)
      (minimumValueHessianRow J lambda₀ lambda₁ H) J := by
  have hW := minimizer_positiveInterior hJ hl₀ hl₁
  have hd : HasFDerivAt (fun K : HermitianMat (r ⊕ s) ℂ =>
      K+BetaDual.diagonal (minimizer K lambda₀ lambda₁)) (totalDerivative J lambda₀ lambda₁) J := by
    convert! (hasFDerivAt_id J).add ((diagonalCLM (r := r) (s := s)).hasFDerivAt
      (x := minimizer J lambda₀ lambda₁) |>.comp J
        (hasStrictFDerivAt_minimizer hJ hl₀ hl₁).hasFDerivAt) using 1
  convert! ((hasFDerivAt_psiGradient_row (total_posDef hJ hW.1 hW.2) H).comp J hd).neg using 1

/-- Pinching the two diagonal blocks, as an actual real continuous linear map. -/
def pinching : HermitianMat (r ⊕ s) ℂ →L[ℝ] HermitianMat (r ⊕ s) ℂ := diagonalCLM.comp pinchCLM

theorem pinching_posDef {J : HermitianMat (r ⊕ s) ℂ} (hJ : J.mat.PosDef) :
    (pinching J).mat.PosDef := by
  exact BetaBlocks.diagonal_posDef (hJ.submatrix Sum.inl_injective) (hJ.submatrix Sum.inr_injective)

/-- The manuscript's complete minimized dual value. -/
def value (J : HermitianMat (r ⊕ s) ℂ) (lambda₀ lambda₁ : ℝ) : ℝ :=
  psi (pinching J)+minimumValue J lambda₀ lambda₁

def valueGradient (J : HermitianMat (r ⊕ s) ℂ) (lambda₀ lambda₁ : ℝ) :
    HermitianMat (r ⊕ s) ℂ →L[ℝ] ℝ :=
  (psiGradient (pinching J).mat).comp pinching+minimumValueGradient J lambda₀ lambda₁

theorem hasFDerivAt_value {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosDef) (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) :
    HasFDerivAt (fun K : HermitianMat (r ⊕ s) ℂ => value K lambda₀ lambda₁)
      (valueGradient J lambda₀ lambda₁) J :=
  ((hasFDerivAt_psi (pinching_posDef hJ)).comp J pinching.hasFDerivAt).add
    (hasFDerivAt_minimumValue hJ hl₀ hl₁)

def valueHessianRow (J : HermitianMat (r ⊕ s) ℂ) (lambda₀ lambda₁ : ℝ)
    (H : HermitianMat (r ⊕ s) ℂ) : HermitianMat (r ⊕ s) ℂ →L[ℝ] ℝ :=
  (psiHessianRow (pinching J).mat (pinching H)).comp pinching+
    minimumValueHessianRow J lambda₀ lambda₁ H

/-- The actual value Hessian before identifying the Schur expression. -/
theorem hasFDerivAt_valueGradient_row {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosDef) (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) (H : HermitianMat (r ⊕ s) ℂ) :
    HasFDerivAt (fun K : HermitianMat (r ⊕ s) ℂ => valueGradient K lambda₀ lambda₁ H)
      (valueHessianRow J lambda₀ lambda₁ H) J := by
  have hd := (hasFDerivAt_psiGradient_row (pinching_posDef hJ) (pinching H)).comp J pinching.hasFDerivAt
  convert! hd.add (hasFDerivAt_minimumValueGradient_row hJ hl₀ hl₁ H) using 1

theorem continuousAt_value {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosDef) (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) :
    ContinuousAt (fun K : HermitianMat (r ⊕ s) ℂ => value K lambda₀ lambda₁) J :=
  (hasFDerivAt_value hJ hl₀ hl₁).continuousAt

end QubitAdditivity.BetaDualValue
