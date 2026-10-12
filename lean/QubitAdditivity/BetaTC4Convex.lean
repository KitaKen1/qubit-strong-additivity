import QubitAdditivity.BetaDualBoundary

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

namespace QubitAdditivity.BetaTC4Convex
open BetaDualBoundary BetaDual BetaDualConvex BetaDualInterior BetaDualDerivative BetaMinimizer BetaEntropy BetaDualValue BetaDualExistence

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

theorem convex_positiveCone : Convex ℝ (positiveCone (r := r) (s := s)) := by
  intro W hW Z hZ a b ha hb hab
  constructor
  · convert! (hW.1.smul ha).add (hZ.1.smul hb) using 1
  · convert! (hW.2.smul ha).add (hZ.2.smul hb) using 1

/-- W-convexity holds for every PSD input, including the rank-one comparison input. -/
theorem convexOn_objective_psd {J : HermitianMat (r ⊕ s) ℂ} (lambda₀ lambda₁ : ℝ)
    (hJ : J.mat.PosSemidef) : ConvexOn ℝ positiveCone (objective J lambda₀ lambda₁) := by
  refine ⟨convex_positiveCone,?_⟩
  intro W hW Z hZ a b ha hb hab
  let regularize : Blocks r s → ℝ → Blocks r s := fun X t => X+t • (1,1)
  have hpos (X : Blocks r s) (hX : X ∈ positiveCone) (t : ℝ) (ht : 0 < t) :
      regularize X t ∈ positiveInterior := by
    constructor
    · exact BetaDualBoundary.regularization_posDef hX.1 ht
    · exact BetaDualBoundary.regularization_posDef hX.2 ht
  have hcont (X : Blocks r s) : Continuous (fun t : ℝ => objective (J+t • 1) lambda₀ lambda₁ (regularize X t)) := by
    have hX : Continuous (regularize X) := by unfold regularize; fun_prop
    have hK : Continuous (fun t : ℝ => J+t • (1 : HermitianMat (r ⊕ s) ℂ)) := by fun_prop
    have hd : Continuous (fun t : ℝ => diagonal (regularize X t)) := diagonalCLM.continuous.comp hX
    have hc : Continuous (fun t : ℝ => psi (diagonal (regularize X t))-
        psi (J+t • 1+diagonal (regularize X t))-linearPenalty lambda₀ lambda₁ (regularize X t)) :=
      ((continuous_psi.comp hd).sub (continuous_psi.comp (hK.add hd))).sub
        ((linearPenalty lambda₀ lambda₁).continuous.comp hX)
    convert! hc using 1
    funext t
    exact objective_eq (J+t • 1) lambda₀ lambda₁ (regularize X t)
  have ht (X : Blocks r s) : Tendsto (fun t : ℝ => objective (J+t • 1) lambda₀ lambda₁ (regularize X t))
      (𝓝[>] 0) (𝓝 (objective J lambda₀ lambda₁ X)) := by
    have hh : Tendsto (fun t : ℝ => objective (J+t • 1) lambda₀ lambda₁ (regularize X t))
        (𝓝[>] 0) (𝓝 (objective (J+(0 : ℝ) • 1) lambda₀ lambda₁ (regularize X 0))) :=
      ((hcont X).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    have he : J+(0 : ℝ) • 1 = J := by simp
    have hx : regularize X (0 : ℝ) = X := by simp [regularize]
    rw [he,hx] at hh
    exact hh
  apply le_of_tendsto_of_tendsto (ht (a • W+b • Z))
    ((tendsto_const_nhds.mul (ht W)).add (tendsto_const_nhds.mul (ht Z)))
  filter_upwards [self_mem_nhdsWithin] with t ht'
  have hi := (strictConvexOn_objective lambda₀ lambda₁
    (BetaDualBoundary.regularization_posDef hJ ht')).convexOn.2
      (hpos W hW t ht') (hpos Z hZ t ht') ha hb hab
  have he : a • regularize W t+b • regularize Z t = regularize (a • W+b • Z) t := by
    unfold regularize
    calc
      _ = a • W+b • Z+(a+b) • (t • (1,1)) := by module
      _ = _ := by rw [hab,one_smul]
  simpa only [he,smul_eq_mul] using hi

/-- Restrict the certified convex objective to any segment in the closed block cone. -/
theorem convexOn_objective_line_psd {J : HermitianMat (r ⊕ s) ℂ} (lambda₀ lambda₁ : ℝ)
    (hJ : J.mat.PosSemidef) {W Z : Blocks r s} (hW : W ∈ positiveCone) (hZ : Z ∈ positiveCone) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) (fun t => objective J lambda₀ lambda₁ (line W (Z-W) t)) := by
  refine ⟨convex_Icc _ _,?_⟩
  intro x hx y hy a b ha hb hab
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : line W (Z-W) t ∈ positiveCone := by
    have he : line W (Z-W) t = (1-t) • W+t • Z := by unfold line; module
    rw [he]
    exact convex_positiveCone hW hZ (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have he : line W (Z-W) (a*x+b*y) = a • line W (Z-W) x+b • line W (Z-W) y := by
    unfold line
    have hh : (a+b) • W = W := by rw [hab,one_smul]
    calc
      _ = (a+b) • W+(a*x+b*y) • (Z-W) := by rw [hh]
      _ = _ := by module
  change objective J lambda₀ lambda₁ (line W (Z-W) (a*x+b*y)) ≤
    a*objective J lambda₀ lambda₁ (line W (Z-W) x)+b*objective J lambda₀ lambda₁ (line W (Z-W) y)
  rw [he]
  exact (convexOn_objective_psd lambda₀ lambda₁ hJ).2 (hp x hx) (hp y hy) ha hb hab

/-- For PSD J, any positive block stationary point is a global closed-cone minimum. -/
theorem isMinOn_positiveCone_of_stationary_psd {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosSemidef) {W : Blocks r s} (hW : W ∈ positiveInterior)
    (hs : stationaryResidual J lambda₀ lambda₁ W = 0) :
    IsMinOn (objective J lambda₀ lambda₁) positiveCone W := by
  intro Z hZ
  have hW' : W ∈ positiveCone := ⟨hW.1.posSemidef,hW.2.posSemidef⟩
  have hc := convexOn_objective_line_psd lambda₀ lambda₁ hJ hW' hZ
  have hT : (J+diagonal W).mat.PosDef := by
    change (J.mat+(diagonal W).mat).PosDef
    rw [add_comm]
    exact (BetaBlocks.diagonal_posDef hW.1 hW.2).add_posSemidef hJ
  have hd := hasDerivAt_objective_line lambda₀ lambda₁ W (Z-W)
    (t := 0) (by simpa [line] using hW.1) (by simpa [line] using hW.2) (by simpa [line] using hT)
  have hz : gradient J lambda₀ lambda₁ (line W (Z-W) 0) (Z-W) = 0 := by
    simp only [line,zero_smul,add_zero,gradient_eq_blockPairing,hs,map_zero]
    rfl
  rw [hz] at hd
  have hi := hc.le_slope_of_hasDerivAt (x := 0) (y := 1) (by simp) (by simp) (by norm_num) hd
  simpa [slope_def_field,line,sub_le_iff_le_add] using hi

/-- A cone minimum gives the actual minimum value without a uniqueness premise. -/
theorem minimumValue_eq_of_isMinOn {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosSemidef) (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0)
    {W : Blocks r s} (hW : W ∈ positiveCone) (hmin : IsMinOn (objective J lambda₀ lambda₁) positiveCone W) :
    minimumValue J lambda₀ lambda₁ = objective J lambda₀ lambda₁ W := by
  have h := minimizer_spec_psd hJ hl₀ hl₁
  exact le_antisymm (h.2 hW) (hmin h.1)

/-- The supporting dual inequality holds on the full PSD cone. -/
theorem value_le_primal {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosSemidef) (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0)
    {W : Blocks r s} (hW : W ∈ positiveCone) :
    value J lambda₀ lambda₁+linearPenalty lambda₀ lambda₁ W ≤
      psi (pinching J)+psi (diagonal W)-psi (J+diagonal W) := by
  have hi := (minimizer_spec_psd hJ hl₀ hl₁).2 hW
  change minimumValue J lambda₀ lambda₁ ≤ objective J lambda₀ lambda₁ W at hi
  rw [objective_eq] at hi
  change psi (pinching J)+minimumValue J lambda₀ lambda₁+linearPenalty lambda₀ lambda₁ W ≤ _
  rw [linearPenalty_apply]
  linarith

end QubitAdditivity.BetaTC4Convex
