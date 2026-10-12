import QubitAdditivity.BetaBoundaryEntropy

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

namespace QubitAdditivity.BetaDualInterior
open BetaDual BetaDualConvex BetaDualExistence BetaEntropy

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



variable {r s : Type*} [Fintype r] [Fintype s] [DecidableEq r] [DecidableEq s]

def correction (J : HermitianMat (r ⊕ s) ℂ) (lambda₀ lambda₁ : ℝ) (W : Blocks r s) : ℝ :=
  -psi (J+BetaDual.diagonal W)-linearPenalty lambda₀ lambda₁ W

def correctionGradient (J : HermitianMat (r ⊕ s) ℂ) (lambda₀ lambda₁ : ℝ) (W : Blocks r s) :
    Blocks r s →L[ℝ] ℝ := -(psiGradient (J+BetaDual.diagonal W).mat).comp diagonalCLM-linearPenalty lambda₀ lambda₁

theorem objective_eq_correction (J : HermitianMat (r ⊕ s) ℂ) (lambda₀ lambda₁ : ℝ) (W : Blocks r s) :
    objective J lambda₀ lambda₁ W = psi W.1+psi W.2+correction J lambda₀ lambda₁ W := by
  rw [objective,correction,linearPenalty_apply]
  ring

theorem hasFDerivAt_correction {J : HermitianMat (r ⊕ s) ℂ} (lambda₀ lambda₁ : ℝ)
    {W : Blocks r s} (hT : (J+BetaDual.diagonal W).mat.PosDef) :
    HasFDerivAt (correction J lambda₀ lambda₁) (correctionGradient J lambda₀ lambda₁ W) W := by
  have hl := (diagonalCLM (r := r) (s := s)).hasFDerivAt (x := W) |>.const_add J
  have hd := (hasFDerivAt_psi hT).comp W hl
  convert! hd.neg.sub ((linearPenalty lambda₀ lambda₁).hasFDerivAt (x := W)) using 1

theorem total_posDef_on_cone {J : HermitianMat (r ⊕ s) ℂ} {W : Blocks r s}
    (hJ : J.mat.PosDef) (hW : W ∈ positiveCone) : (J+BetaDual.diagonal W).mat.PosDef := by
  convert! hJ.add_posSemidef (diagonal_posSemidef hW) using 1

/-- Any minimum is interior in its first block. -/
theorem left_posDef_of_minOn {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosDef) {W : Blocks r s} (hW : W ∈ positiveCone)
    (hmin : IsMinOn (objective J lambda₀ lambda₁) positiveCone W) : W.1.mat.PosDef := by
  by_contra hnot
  let H : Blocks r s := (1,0)
  let g : ℝ → ℝ := fun t => psi W.2+correction J lambda₀ lambda₁ (line W H t)
  have ht : (J+BetaDual.diagonal (line W H 0)).mat.PosDef := by
    simpa [line] using total_posDef_on_cone hJ hW
  have hd : HasDerivAt g (correctionGradient J lambda₀ lambda₁ W H) 0 := by
    convert! ((hasFDerivAt_correction lambda₀ lambda₁ ht).comp_hasDerivAt 0
      (hasDerivAt_line W H 0)).const_add (psi W.2) using 1 <;> simp only [line,zero_smul,add_zero]
  obtain ⟨t,htp,hi⟩ := BetaBoundaryEntropy.exists_boundary_descent hW.1 hnot hd
  have hp : line W H t ∈ positiveCone := by
    constructor
    · convert! hW.1.add (Matrix.PosDef.one.posSemidef.smul htp.le) using 1
    · simpa [line,H] using hW.2
  have he (t : ℝ) : objective J lambda₀ lambda₁ (line W H t) = psi (W.1+t • 1)+g t := by
    rw [objective_eq_correction]
    simp [line,H,g]
    ring
  have hi' : objective J lambda₀ lambda₁ (line W H t) < objective J lambda₀ lambda₁ W := by
    have hbase : objective J lambda₀ lambda₁ W = psi W.1+g 0 := by simpa [line] using he 0
    rw [he,hbase]
    exact hi
  exact (not_lt_of_ge (hmin hp)) hi'

/-- Any minimum is interior in its second block. -/
theorem right_posDef_of_minOn {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosDef) {W : Blocks r s} (hW : W ∈ positiveCone)
    (hmin : IsMinOn (objective J lambda₀ lambda₁) positiveCone W) : W.2.mat.PosDef := by
  by_contra hnot
  let H : Blocks r s := (0,1)
  let g : ℝ → ℝ := fun t => psi W.1+correction J lambda₀ lambda₁ (line W H t)
  have ht : (J+BetaDual.diagonal (line W H 0)).mat.PosDef := by
    simpa [line] using total_posDef_on_cone hJ hW
  have hd : HasDerivAt g (correctionGradient J lambda₀ lambda₁ W H) 0 := by
    convert! ((hasFDerivAt_correction lambda₀ lambda₁ ht).comp_hasDerivAt 0
      (hasDerivAt_line W H 0)).const_add (psi W.1) using 1 <;> simp only [line,zero_smul,add_zero]
  obtain ⟨t,htp,hi⟩ := BetaBoundaryEntropy.exists_boundary_descent hW.2 hnot hd
  have hp : line W H t ∈ positiveCone := by
    constructor
    · simpa [line,H] using hW.1
    · convert! hW.2.add (Matrix.PosDef.one.posSemidef.smul htp.le) using 1
  have he (t : ℝ) : objective J lambda₀ lambda₁ (line W H t) = psi (W.2+t • 1)+g t := by
    rw [objective_eq_correction]
    simp [line,H,g]
    ring
  have hi' : objective J lambda₀ lambda₁ (line W H t) < objective J lambda₀ lambda₁ W := by
    have hbase : objective J lambda₀ lambda₁ W = psi W.2+g 0 := by simpa [line] using he 0
    rw [he,hbase]
    exact hi
  exact (not_lt_of_ge (hmin hp)) hi'

/-- The positive-definiteness premises on a cone minimum are discharged. -/
theorem positiveInterior_of_minOn {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosDef) {W : Blocks r s} (hW : W ∈ positiveCone)
    (hmin : IsMinOn (objective J lambda₀ lambda₁) positiveCone W) : W ∈ positiveInterior :=
  ⟨left_posDef_of_minOn hJ hW hmin,right_posDef_of_minOn hJ hW hmin⟩

/-- Existence, interiority and uniqueness on the entire original PSD cone. -/
theorem existsUnique_minOn_positiveCone {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosDef) (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) :
    ∃! W : Blocks r s, W ∈ positiveCone ∧ IsMinOn (objective J lambda₀ lambda₁) positiveCone W := by
  obtain ⟨W,hW,hmin⟩ := exists_minOn_positiveCone hJ hl₀ hl₁
  refine ⟨W,⟨hW,hmin⟩,?_⟩
  intro Z hZ
  exact eq_of_minOn_positiveCone hJ (positiveInterior_of_minOn hJ hZ.1 hZ.2)
    (positiveInterior_of_minOn hJ hW hmin) hZ.2 hmin

theorem stationarity_of_minOn {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosDef) {W : Blocks r s} (hW : W ∈ positiveCone)
    (hmin : IsMinOn (objective J lambda₀ lambda₁) positiveCone W) :
    stationaryResidual J lambda₀ lambda₁ W = 0 := by
  have hp := positiveInterior_of_minOn hJ hW hmin
  exact stationarity_of_minOn_positiveCone hp.1 hp.2 (total_posDef_on_cone hJ hW) hmin

theorem km_of_minOn {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosDef) {W : Blocks r s} (hW : W ∈ positiveCone)
    (hmin : IsMinOn (objective J lambda₀ lambda₁) positiveCone W) :
    (BetaOperators.blockInclusion (r := r) (s := s))ᴴ * BetaPowers.km (J+BetaDual.diagonal W).mat *
      BetaOperators.blockInclusion ≤ BetaBridge.blockKM W.1.mat W.2.mat +
      BetaBridge.blockKM ((J+BetaDual.diagonal W).mat.submatrix Sum.inl Sum.inl-W.1.mat)
        ((J+BetaDual.diagonal W).mat.submatrix Sum.inr Sum.inr-W.2.mat) := by
  have hp := positiveInterior_of_minOn hJ hW hmin
  exact km_of_minOn_positiveCone hJ hp.1 hp.2 hmin

theorem curvature_nonpos_of_minOn {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosDef) {W : Blocks r s} (hW : W ∈ positiveCone)
    (hmin : IsMinOn (objective J lambda₀ lambda₁) positiveCone W) :
    BetaHessian.curvature (J+BetaDual.diagonal W).mat W.1.mat W.2.mat ≤ 0 := by
  have hp := positiveInterior_of_minOn hJ hW hmin
  exact curvature_nonpos_of_minOn_positiveCone hJ hp.1 hp.2 hmin

end QubitAdditivity.BetaDualInterior
