import QubitAdditivity.BetaKMOrder
import QubitAdditivity.BetaHessian
import Mathlib.Analysis.Calculus.LocalExtr.Basic

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology RealInnerProductSpace

namespace QubitAdditivity.BetaDual
open BetaPowers BetaEntropy

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

/-- Real coordinates for the block diagonal Hermitian algebra. -/
abbrev Blocks (r s : Type*) := HermitianMat r ℂ × HermitianMat s ℂ

def diagonal (W : Blocks r s) : HermitianMat (r ⊕ s) ℂ :=
  ⟨Matrix.fromBlocks W.1.mat 0 0 W.2.mat, W.1.H.fromBlocks (by simp) W.2.H⟩

@[simp] theorem diagonal_mat (W : Blocks r s) :
    (diagonal W).mat = Matrix.fromBlocks W.1.mat 0 0 W.2.mat := rfl

def diagonalLM : Blocks r s →ₗ[ℝ] HermitianMat (r ⊕ s) ℂ where
  toFun := diagonal
  map_add' W Z := by
    apply HermitianMat.ext
    change Matrix.fromBlocks (W.1.mat+Z.1.mat) 0 0 (W.2.mat+Z.2.mat) =
      Matrix.fromBlocks W.1.mat 0 0 W.2.mat + Matrix.fromBlocks Z.1.mat 0 0 Z.2.mat
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks]
  map_smul' c W := by
    apply HermitianMat.ext
    change Matrix.fromBlocks (c • W.1.mat) 0 0 (c • W.2.mat) =
      c • Matrix.fromBlocks W.1.mat 0 0 W.2.mat
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks]

def diagonalCLM : Blocks r s →L[ℝ] HermitianMat (r ⊕ s) ℂ :=
  diagonalLM.toContinuousLinearMap

@[simp] theorem diagonalCLM_apply (W : Blocks r s) : diagonalCLM W = diagonal W := rfl

def traceHerm {k : Type*} [Fintype k] [DecidableEq k] : HermitianMat k ℂ →L[ℝ] ℝ :=
  (BetaLog.traceRe (n := k)).comp BetaLog.inclusion

@[simp] theorem traceHerm_apply {k : Type*} [Fintype k] [DecidableEq k] (H : HermitianMat k ℂ) :
    traceHerm H = H.mat.trace.re := rfl

theorem trace_diagonal_mul (H : Blocks r s) (X : Matrix (r ⊕ s) (r ⊕ s) ℂ) :
    ((diagonal H).mat * X).trace =
      (H.1.mat * X.submatrix Sum.inl Sum.inl).trace +
      (H.2.mat * X.submatrix Sum.inr Sum.inr).trace := by
  simp [Matrix.trace,Matrix.mul_apply,Fintype.sum_sum_type,diagonal,Matrix.fromBlocks,
    Matrix.submatrix_apply]

theorem logarithm_diagonal (W : Blocks r s) : logarithm (diagonal W).mat =
    Matrix.fromBlocks (logarithm W.1.mat) 0 0 (logarithm W.2.mat) := by
  convert! BetaBlocks.cfc_diagonal W.1.mat W.2.mat W.1.H W.2.H Real.log using 1

theorem psi_diagonal (W : Blocks r s) : psi (diagonal W) = psi W.1 + psi W.2 := by
  rw [psi_eq_trace,psi_eq_trace,psi_eq_trace]
  rw [logarithm_diagonal,trace_diagonal_mul]
  have h₀ : (Matrix.fromBlocks (logarithm W.1.mat) 0 0 (logarithm W.2.mat)).submatrix
      Sum.inl Sum.inl = logarithm W.1.mat := rfl
  have h₁ : (Matrix.fromBlocks (logarithm W.1.mat) 0 0 (logarithm W.2.mat)).submatrix
      Sum.inr Sum.inr = logarithm W.2.mat := rfl
  rw [h₀,h₁,Complex.add_re]

/-- The minimized term in the manuscript's dual value, in real block coordinates. -/
def objective (J : HermitianMat (r ⊕ s) ℂ) (lambda₀ lambda₁ : ℝ) (W : Blocks r s) : ℝ :=
  psi W.1 + psi W.2 - psi (J+diagonal W) -
    (lambda₀ * W.1.mat.trace.re + lambda₁ * W.2.mat.trace.re)

theorem objective_eq (J : HermitianMat (r ⊕ s) ℂ) (lambda₀ lambda₁ : ℝ) (W : Blocks r s) :
    objective J lambda₀ lambda₁ W = psi (diagonal W) - psi (J+diagonal W) -
      (lambda₀ * W.1.mat.trace.re + lambda₁ * W.2.mat.trace.re) := by
  rw [objective,psi_diagonal]

def linearPenalty (lambda₀ lambda₁ : ℝ) : Blocks r s →L[ℝ] ℝ :=
  (lambda₀ • traceHerm).comp (ContinuousLinearMap.fst ℝ (HermitianMat r ℂ) (HermitianMat s ℂ)) +
  (lambda₁ • traceHerm).comp (ContinuousLinearMap.snd ℝ (HermitianMat r ℂ) (HermitianMat s ℂ))

@[simp] theorem linearPenalty_apply (lambda₀ lambda₁ : ℝ) (H : Blocks r s) :
    linearPenalty lambda₀ lambda₁ H = lambda₀ * H.1.mat.trace.re + lambda₁ * H.2.mat.trace.re := rfl

def gradient (J : HermitianMat (r ⊕ s) ℂ) (lambda₀ lambda₁ : ℝ) (W : Blocks r s) :
    Blocks r s →L[ℝ] ℝ :=
  (psiGradient W.1.mat).comp (ContinuousLinearMap.fst ℝ (HermitianMat r ℂ) (HermitianMat s ℂ)) +
  (psiGradient W.2.mat).comp (ContinuousLinearMap.snd ℝ (HermitianMat r ℂ) (HermitianMat s ℂ)) -
  (psiGradient (J+diagonal W).mat).comp diagonalCLM - linearPenalty lambda₀ lambda₁

theorem hasFDerivAt_objective {J : HermitianMat (r ⊕ s) ℂ} (lambda₀ lambda₁ : ℝ)
    {W : Blocks r s} (hA : W.1.mat.PosDef) (hB : W.2.mat.PosDef)
    (hT : (J+diagonal W).mat.PosDef) :
    HasFDerivAt (objective J lambda₀ lambda₁) (gradient J lambda₀ lambda₁ W) W := by
  have ha := (hasFDerivAt_psi hA).comp W
    (ContinuousLinearMap.fst ℝ (HermitianMat r ℂ) (HermitianMat s ℂ)).hasFDerivAt
  have hb := (hasFDerivAt_psi hB).comp W
    (ContinuousLinearMap.snd ℝ (HermitianMat r ℂ) (HermitianMat s ℂ)).hasFDerivAt
  have hd : HasFDerivAt (fun Z : Blocks r s => J+diagonal Z) diagonalCLM W := by
    convert! (diagonalCLM (r := r) (s := s)).hasFDerivAt.const_add J using 1
  have ht := (hasFDerivAt_psi hT).comp W hd
  have hp := (linearPenalty (r := r) (s := s) lambda₀ lambda₁).hasFDerivAt (x := W)
  convert! ((ha.add hb).sub ht).sub hp using 1

def hermLog {k : Type*} [Fintype k] [DecidableEq k] (A : HermitianMat k ℂ) : HermitianMat k ℂ :=
  ⟨logarithm A.mat,logarithm_isHermitian A.mat⟩

def pinchLeft (T : HermitianMat (r ⊕ s) ℂ) : HermitianMat r ℂ :=
  ⟨T.mat.submatrix Sum.inl Sum.inl,T.H.submatrix Sum.inl⟩

def pinchRight (T : HermitianMat (r ⊕ s) ℂ) : HermitianMat s ℂ :=
  ⟨T.mat.submatrix Sum.inr Sum.inr,T.H.submatrix Sum.inr⟩

/-- The logarithmic stationarity residual in the real block algebra. -/
def stationaryResidual (J : HermitianMat (r ⊕ s) ℂ) (lambda₀ lambda₁ : ℝ) (W : Blocks r s) : Blocks r s :=
  (hermLog W.1 - pinchLeft (hermLog (J+diagonal W)) - lambda₀ • 1,
   hermLog W.2 - pinchRight (hermLog (J+diagonal W)) - lambda₁ • 1)

theorem trace_mul_residual {k : Type*} [Fintype k] [DecidableEq k]
    (H L X : Matrix k k ℂ) (c : ℝ) :
    (H*(L-X-c • 1)).trace.re = (H*(L+1)).trace.re - (H*(X+1)).trace.re - c*H.trace.re := by
  simp [Matrix.mul_sub,Matrix.mul_add,Matrix.mul_smul,Matrix.mul_one,Matrix.trace_sub,
    Matrix.trace_add,Matrix.trace_smul]

theorem gradient_apply (J : HermitianMat (r ⊕ s) ℂ) (lambda₀ lambda₁ : ℝ)
    (W H : Blocks r s) :
    gradient J lambda₀ lambda₁ W H =
      (H.1.mat * (stationaryResidual J lambda₀ lambda₁ W).1.mat).trace.re +
      (H.2.mat * (stationaryResidual J lambda₀ lambda₁ W).2.mat).trace.re := by
  simp only [gradient,ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',
    psiGradient_apply,diagonalCLM_apply,linearPenalty_apply]
  rw [trace_diagonal_mul,Complex.add_re]
  have ht₀ : (logarithm (J+diagonal W).mat+1).submatrix Sum.inl Sum.inl =
      (logarithm (J+diagonal W).mat).submatrix Sum.inl Sum.inl + 1 := by
    ext i j
    simp [Matrix.submatrix_apply,Matrix.add_apply,Matrix.one_apply]
  have ht₁ : (logarithm (J+diagonal W).mat+1).submatrix Sum.inr Sum.inr =
      (logarithm (J+diagonal W).mat).submatrix Sum.inr Sum.inr + 1 := by
    ext i j
    simp [Matrix.submatrix_apply,Matrix.add_apply,Matrix.one_apply]
  have hr₀ : (stationaryResidual J lambda₀ lambda₁ W).1.mat =
      logarithm W.1.mat - (logarithm (J+diagonal W).mat).submatrix Sum.inl Sum.inl - lambda₀ • 1 := rfl
  have hr₁ : (stationaryResidual J lambda₀ lambda₁ W).2.mat =
      logarithm W.2.mat - (logarithm (J+diagonal W).mat).submatrix Sum.inr Sum.inr - lambda₁ • 1 := rfl
  rw [ht₀,ht₁,hr₀,hr₁,trace_mul_residual,trace_mul_residual]
  ring

theorem gradient_eq_zero_of_localMin {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    {W : Blocks r s} (hA : W.1.mat.PosDef) (hB : W.2.mat.PosDef)
    (hT : (J+diagonal W).mat.PosDef) (hmin : IsLocalMin (objective J lambda₀ lambda₁) W) :
    gradient J lambda₀ lambda₁ W = 0 :=
  hmin.hasFDerivAt_eq_zero (hasFDerivAt_objective lambda₀ lambda₁ hA hB hT)

theorem stationaryResidual_eq_zero {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    {W : Blocks r s} (hg : gradient J lambda₀ lambda₁ W = 0) :
    stationaryResidual J lambda₀ lambda₁ W = 0 := by
  let R := stationaryResidual J lambda₀ lambda₁ W
  have he := congrArg (fun L : Blocks r s →L[ℝ] ℝ => L R) hg
  simp only [gradient_apply,ContinuousLinearMap.zero_apply] at he
  have hh : inner ℝ R.1 R.1 + inner ℝ R.2 R.2 = 0 := by
    simp only [HermitianMat.inner_eq_re_trace]
    convert! he using 1
  have hp₀ : 0 ≤ inner ℝ R.1 R.1 := by convert! real_inner_self_nonneg (x := R.1) using 1
  have hp₁ : 0 ≤ inner ℝ R.2 R.2 := by convert! real_inner_self_nonneg (x := R.2) using 1
  have hz₀ : inner ℝ R.1 R.1 = 0 := by linarith
  have hz₁ : inner ℝ R.2 R.2 = 0 := by linarith
  have h₀ : R.1 = 0 := by convert! (inner_self_eq_zero (𝕜 := ℝ)).mp hz₀ using 1
  have h₁ : R.2 = 0 := by convert! (inner_self_eq_zero (𝕜 := ℝ)).mp hz₁ using 1
  exact Prod.ext h₀ h₁

/-- Interior local minima supply the logarithmic stationarity hypothesis. -/
theorem stationarity_of_localMin {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    {W : Blocks r s} (hA : W.1.mat.PosDef) (hB : W.2.mat.PosDef)
    (hT : (J+diagonal W).mat.PosDef) (hmin : IsLocalMin (objective J lambda₀ lambda₁) W) :
    stationaryResidual J lambda₀ lambda₁ W = 0 :=
  stationaryResidual_eq_zero (gradient_eq_zero_of_localMin hA hB hT hmin)

def positiveCone : Set (Blocks r s) := {W | W.1.mat.PosSemidef ∧ W.2.mat.PosSemidef}

theorem positiveCone_mem_nhds {W : Blocks r s} (hA : W.1.mat.PosDef) (hB : W.2.mat.PosDef) :
    positiveCone (r := r) (s := s) ∈ 𝓝 W := by
  have ha : ∀ᶠ Z : Blocks r s in 𝓝 W, Z.1.mat.PosDef :=
    (continuous_fst.tendsto W).eventually (BetaLog.eventually_posDef hA)
  have hb : ∀ᶠ Z : Blocks r s in 𝓝 W, Z.2.mat.PosDef :=
    (continuous_snd.tendsto W).eventually (BetaLog.eventually_posDef hB)
  filter_upwards [ha,hb] with Z hz₀ hz₁
  exact ⟨hz₀.posSemidef,hz₁.posSemidef⟩

/-- A positive-definite minimum on the closed positive cone is stationary.
Existence and interiority of such a minimum are separate remaining tasks. -/
theorem stationarity_of_minOn_positiveCone {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    {W : Blocks r s} (hA : W.1.mat.PosDef) (hB : W.2.mat.PosDef)
    (hT : (J+diagonal W).mat.PosDef)
    (hmin : IsMinOn (objective J lambda₀ lambda₁) positiveCone W) :
    stationaryResidual J lambda₀ lambda₁ W = 0 :=
  stationarity_of_localMin hA hB hT (hmin.isLocalMin (positiveCone_mem_nhds hA hB))

theorem real_smul_identity {k : Type*} [Fintype k] [DecidableEq k] (c : ℝ) :
    c • (1 : Matrix k k ℂ) = (c : ℂ) • (1 : Matrix k k ℂ) := by
  ext i j
  simp [Matrix.smul_apply,Complex.real_smul]

theorem log_stationarity_of_residual_zero {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    {W : Blocks r s} (hs : stationaryResidual J lambda₀ lambda₁ W = 0) :
    logarithm W.1.mat = (logarithm (J+diagonal W).mat).submatrix Sum.inl Sum.inl + (lambda₀ : ℂ) • 1 ∧
    logarithm W.2.mat = (logarithm (J+diagonal W).mat).submatrix Sum.inr Sum.inr + (lambda₁ : ℂ) • 1 := by
  have h₀ := congrArg (fun Z : Blocks r s => Z.1.mat) hs
  have h₁ := congrArg (fun Z : Blocks r s => Z.2.mat) hs
  change logarithm W.1.mat - (logarithm (J+diagonal W).mat).submatrix Sum.inl Sum.inl - lambda₀ • 1 = 0 at h₀
  change logarithm W.2.mat - (logarithm (J+diagonal W).mat).submatrix Sum.inr Sum.inr - lambda₁ • 1 = 0 at h₁
  rw [real_smul_identity,sub_sub] at h₀ h₁
  exact ⟨sub_eq_zero.mp h₀,sub_eq_zero.mp h₁⟩

theorem total_posDef {J : HermitianMat (r ⊕ s) ℂ} {W : Blocks r s}
    (hJ : J.mat.PosDef) (hA : W.1.mat.PosDef) (hB : W.2.mat.PosDef) :
    (J+diagonal W).mat.PosDef := by
  convert! hJ.add_posSemidef (BetaBlocks.diagonal_posDef hA hB).posSemidef using 1

theorem total_gap_posDef {J : HermitianMat (r ⊕ s) ℂ} {W : Blocks r s} (hJ : J.mat.PosDef) :
    ((J+diagonal W).mat - Matrix.fromBlocks W.1.mat 0 0 W.2.mat).PosDef := by
  simpa only [HermitianMat.mat_add,diagonal_mat,add_sub_cancel_right] using hJ

/-- A positive-definite cone minimum supplies all log premises of actual PW/KM. -/
theorem km_of_minOn_positiveCone {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    {W : Blocks r s} (hJ : J.mat.PosDef) (hA : W.1.mat.PosDef) (hB : W.2.mat.PosDef)
    (hmin : IsMinOn (objective J lambda₀ lambda₁) positiveCone W) :
    (BetaOperators.blockInclusion (r := r) (s := s))ᴴ * km (J+diagonal W).mat *
      BetaOperators.blockInclusion ≤ BetaBridge.blockKM W.1.mat W.2.mat +
      BetaBridge.blockKM ((J+diagonal W).mat.submatrix Sum.inl Sum.inl - W.1.mat)
        ((J+diagonal W).mat.submatrix Sum.inr Sum.inr - W.2.mat) := by
  have hT := total_posDef hJ hA hB
  have hs := log_stationarity_of_residual_zero (stationarity_of_minOn_positiveCone hA hB hT hmin)
  exact BetaPWBound.km_of_stationarity hT hA hB (total_gap_posDef hJ)
    (lambda₀ : ℂ) (lambda₁ : ℂ) hs.1 hs.2

/-- The candidate eliminated curvature order now follows from an actual interior minimum. -/
theorem curvature_nonpos_of_minOn_positiveCone {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    {W : Blocks r s} (hJ : J.mat.PosDef) (hA : W.1.mat.PosDef) (hB : W.2.mat.PosDef)
    (hmin : IsMinOn (objective J lambda₀ lambda₁) positiveCone W) :
    BetaHessian.curvature (J+diagonal W).mat W.1.mat W.2.mat ≤ 0 := by
  have hT := total_posDef hJ hA hB
  have hs := log_stationarity_of_residual_zero (stationarity_of_minOn_positiveCone hA hB hT hmin)
  exact BetaHessian.curvature_nonpos_of_stationarity hT hA hB (total_gap_posDef hJ)
    (lambda₀ : ℂ) (lambda₁ : ℂ) hs.1 hs.2

theorem diagonal_injective : Function.Injective (diagonal (r := r) (s := s)) := by
  intro H K he
  have h₀ := congrArg (fun Z : HermitianMat (r ⊕ s) ℂ => Z.mat.submatrix Sum.inl Sum.inl) he
  have h₁ := congrArg (fun Z : HermitianMat (r ⊕ s) ℂ => Z.mat.submatrix Sum.inr Sum.inr) he
  exact Prod.ext (HermitianMat.ext h₀) (HermitianMat.ext h₁)

theorem psiGradient_diagonal_apply (W H : Blocks r s) :
    psiGradient (diagonal W).mat (diagonal H) =
      psiGradient W.1.mat H.1 + psiGradient W.2.mat H.2 := by
  simp only [psiGradient_apply]
  rw [trace_diagonal_mul,Complex.add_re]
  have h₀ : (logarithm (diagonal W).mat+1).submatrix Sum.inl Sum.inl = logarithm W.1.mat+1 := by
    rw [logarithm_diagonal]
    ext i j
    simp [Matrix.submatrix_apply,Matrix.add_apply,Matrix.one_apply]
  have h₁ : (logarithm (diagonal W).mat+1).submatrix Sum.inr Sum.inr = logarithm W.2.mat+1 := by
    rw [logarithm_diagonal]
    ext i j
    simp [Matrix.submatrix_apply,Matrix.add_apply,Matrix.one_apply]
  rw [h₀,h₁]

theorem gradient_diagonal (J : HermitianMat (r ⊕ s) ℂ) (lambda₀ lambda₁ : ℝ) (W : Blocks r s) :
    gradient J lambda₀ lambda₁ W =
      (psiGradient (diagonal W).mat-psiGradient (J+diagonal W).mat).comp diagonalCLM -
        linearPenalty lambda₀ lambda₁ := by
  apply ContinuousLinearMap.ext
  intro H
  simp only [gradient,ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',
    diagonalCLM_apply,psiGradient_diagonal_apply]

/-- The actual W-objective Hessian row, before eliminating the minimum. -/
def hessianRow (J : HermitianMat (r ⊕ s) ℂ) (W H : Blocks r s) : Blocks r s →L[ℝ] ℝ :=
  (psiHessianRow (diagonal W).mat (diagonal H) -
    psiHessianRow (J+diagonal W).mat (diagonal H)).comp diagonalCLM

@[simp] theorem hessianRow_apply (J : HermitianMat (r ⊕ s) ℂ) (W H K : Blocks r s) :
    hessianRow J W H K = psiHessianRow (diagonal W).mat (diagonal H) (diagonal K) -
      psiHessianRow (J+diagonal W).mat (diagonal H) (diagonal K) := rfl

theorem hasFDerivAt_gradient_row {J : HermitianMat (r ⊕ s) ℂ} (lambda₀ lambda₁ : ℝ)
    {W : Blocks r s} (hA : W.1.mat.PosDef) (hB : W.2.mat.PosDef)
    (hT : (J+diagonal W).mat.PosDef) (H : Blocks r s) :
    HasFDerivAt (fun Z : Blocks r s => gradient J lambda₀ lambda₁ Z H) (hessianRow J W H) W := by
  have hW : (diagonal W).mat.PosDef := BetaBlocks.diagonal_posDef hA hB
  have hw := (hasFDerivAt_psiGradient_row hW (diagonal H)).comp W
    (diagonalCLM (r := r) (s := s)).hasFDerivAt
  have hd : HasFDerivAt (fun Z : Blocks r s => J+diagonal Z) diagonalCLM W := by
    convert! (diagonalCLM (r := r) (s := s)).hasFDerivAt.const_add J using 1
  have ht := (hasFDerivAt_psiGradient_row hT (diagonal H)).comp W hd
  convert! (hw.sub ht).sub_const (linearPenalty lambda₀ lambda₁ H) using 1
  · ext Z
    simp only [gradient_diagonal,ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply,
      diagonalCLM_apply,Function.comp_apply,Pi.sub_apply]

/-- Strict positive curvature of the actual dual W-objective. No minimum or
stationarity is assumed; the positive input gap supplies the strict order. -/
theorem hessianRow_self_pos {J : HermitianMat (r ⊕ s) ℂ} {W : Blocks r s}
    (hJ : J.mat.PosDef) (hA : W.1.mat.PosDef) (hB : W.2.mat.PosDef)
    {H : Blocks r s} (hH : H ≠ 0) : 0 < hessianRow J W H H := by
  have hW : (diagonal W).mat.PosDef := BetaBlocks.diagonal_posDef hA hB
  have hg : ((J+diagonal W).mat-(diagonal W).mat).PosDef := by
    simpa only [HermitianMat.mat_add,add_sub_cancel_right] using hJ
  have hn : diagonal H ≠ 0 := by
    intro hz
    apply hH
    apply diagonal_injective
    change diagonalCLM H = diagonalCLM (0 : Blocks r s)
    rw [map_zero]
    exact hz
  exact BetaKMOrder.psiHessian_gap_pos (total_posDef hJ hA hB) hW hg hn

end QubitAdditivity.BetaDual
