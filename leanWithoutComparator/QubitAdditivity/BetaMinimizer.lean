import QubitAdditivity.BetaDualDerivative

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

namespace QubitAdditivity.BetaMinimizer
open BetaDual BetaDualConvex BetaDualInterior BetaDualDerivative

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

/-- A positive stationary point minimizes the actual objective on the positive interior. -/
theorem isMinOn_interior_of_stationary {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosDef) {W : Blocks r s} (hW : W ∈ positiveInterior)
    (hs : stationaryResidual J lambda₀ lambda₁ W = 0) :
    IsMinOn (objective J lambda₀ lambda₁) positiveInterior W := by
  intro Z hZ
  by_cases he : W = Z
  · subst Z
    exact le_refl (objective J lambda₀ lambda₁ W)
  have hc := (strictConvexOn_objective_line lambda₀ lambda₁ hJ hW hZ he).convexOn
  have hd := hasDerivAt_objective_line lambda₀ lambda₁ W (Z-W)
    (t := 0) (by simpa [line] using hW.1) (by simpa [line] using hW.2)
    (by simpa [line] using total_posDef hJ hW.1 hW.2)
  have hz : gradient J lambda₀ lambda₁ (line W (Z-W) 0) (Z-W) = 0 := by
    simp only [line,zero_smul,add_zero,gradient_eq_blockPairing,hs,map_zero]
    rfl
  rw [hz] at hd
  have hi := hc.le_slope_of_hasDerivAt (x := 0) (y := 1) (by simp) (by simp) (by norm_num) hd
  simpa [slope_def_field,line,sub_le_iff_le_add] using hi

theorem eq_of_stationary {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosDef) {W Z : Blocks r s} (hW : W ∈ positiveInterior) (hZ : Z ∈ positiveInterior)
    (hsW : stationaryResidual J lambda₀ lambda₁ W = 0)
    (hsZ : stationaryResidual J lambda₀ lambda₁ Z = 0) : W = Z :=
  (strictConvexOn_objective lambda₀ lambda₁ hJ).eq_of_isMinOn
    (isMinOn_interior_of_stationary hJ hW hsW) (isMinOn_interior_of_stationary hJ hZ hsZ) hW hZ

/-- A total choice of the true cone minimum, used only where existence is established. -/
def minimizer (J : HermitianMat (r ⊕ s) ℂ) (lambda₀ lambda₁ : ℝ) : Blocks r s :=
  Classical.epsilon (fun W => W ∈ positiveCone ∧ IsMinOn (objective J lambda₀ lambda₁) positiveCone W)

theorem minimizer_spec {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosDef) (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) :
    minimizer J lambda₀ lambda₁ ∈ positiveCone ∧
      IsMinOn (objective J lambda₀ lambda₁) positiveCone (minimizer J lambda₀ lambda₁) := by
  obtain ⟨W,hW,hmin⟩ := BetaDualExistence.exists_minOn_positiveCone hJ hl₀ hl₁
  exact Classical.epsilon_spec (p := fun W : Blocks r s =>
    W ∈ positiveCone ∧ IsMinOn (objective J lambda₀ lambda₁) positiveCone W) ⟨W,hW,hmin⟩

theorem minimizer_positiveInterior {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosDef) (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) :
    minimizer J lambda₀ lambda₁ ∈ positiveInterior := by
  have hs := minimizer_spec hJ hl₀ hl₁
  exact positiveInterior_of_minOn hJ hs.1 hs.2

theorem minimizer_stationary {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosDef) (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) :
    stationaryResidual J lambda₀ lambda₁ (minimizer J lambda₀ lambda₁) = 0 := by
  have hs := minimizer_spec hJ hl₀ hl₁
  exact stationarity_of_minOn hJ hs.1 hs.2

def minimizerDerivative (J : HermitianMat (r ⊕ s) ℂ) (lambda₀ lambda₁ : ℝ) :
    HermitianMat (r ⊕ s) ℂ →L[ℝ] Blocks r s :=
  (-(residualDerivative J (minimizer J lambda₀ lambda₁)).inverse).comp
    (parameterDerivative J (minimizer J lambda₀ lambda₁))

/-- The true global cone minimizer is strictly Fréchet differentiable on J>0. -/
theorem hasStrictFDerivAt_minimizer {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosDef) (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) :
    HasStrictFDerivAt (fun K : HermitianMat (r ⊕ s) ℂ => minimizer K lambda₀ lambda₁)
      (minimizerDerivative J lambda₀ lambda₁) J := by
  let W := minimizer J lambda₀ lambda₁
  have hW := minimizer_positiveInterior hJ hl₀ hl₁
  have hT := total_posDef hJ hW.1 hW.2
  let df := hasStrictFDerivAt_jointResidual lambda₀ lambda₁ hW.1 hW.2 hT
  have hi : ((jointDerivative J W).comp (ContinuousLinearMap.inr ℝ _ _)).IsInvertible := by
    rw [jointDerivative_comp_inr]
    exact residualDerivative_isInvertible hJ hW.1 hW.2
  let f := df.implicitFunctionOfProdDomain hi
  have hd : HasStrictFDerivAt f (minimizerDerivative J lambda₀ lambda₁) J := by
    convert! df.hasStrictFDerivAt_implicitFunctionOfProdDomain hi using 1 <;>
      simp only [jointDerivative_comp_inr,jointDerivative_comp_inl,minimizerDerivative,ContinuousLinearMap.neg_comp]
  have hc : Tendsto f (𝓝 J) (𝓝 W) := df.tendsto_implicitFunctionOfProdDomain hi
  have hp₀ : ∀ᶠ K in 𝓝 J, (f K).1.mat.PosDef :=
    (continuous_fst.continuousAt.tendsto.comp hc).eventually (BetaLog.eventually_posDef hW.1)
  have hp₁ : ∀ᶠ K in 𝓝 J, (f K).2.mat.PosDef :=
    (continuous_snd.continuousAt.tendsto.comp hc).eventually (BetaLog.eventually_posDef hW.2)
  have hs : ∀ᶠ K in 𝓝 J, stationaryResidual K lambda₀ lambda₁ (f K) = 0 := by
    filter_upwards [df.eventually_apply_implicitFunctionOfProdDomain hi] with K hK
    exact hK.trans (minimizer_stationary hJ hl₀ hl₁)
  apply hd.congr_of_eventuallyEq
  filter_upwards [BetaLog.eventually_posDef hJ,hp₀,hp₁,hs] with K hK h₀ h₁ hstat
  exact eq_of_stationary hK ⟨h₀,h₁⟩ (minimizer_positiveInterior hK hl₀ hl₁)
    hstat (minimizer_stationary hK hl₀ hl₁)

theorem continuousAt_minimizer {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosDef) (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) :
    ContinuousAt (fun K : HermitianMat (r ⊕ s) ℂ => minimizer K lambda₀ lambda₁) J :=
  (hasStrictFDerivAt_minimizer hJ hl₀ hl₁).continuousAt

end QubitAdditivity.BetaMinimizer
