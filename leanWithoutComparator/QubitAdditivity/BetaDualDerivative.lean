import QubitAdditivity.BetaDualInterior
import QubitAdditivity.BetaLogRegularity
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

namespace QubitAdditivity.BetaDualDerivative
open BetaDual BetaDualConvex BetaDualInterior BetaEntropy

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

/-- The real linear projection onto Hermitian matrices, in Frobenius topology. -/
def hermitianPartLM : Matrix k k ℂ →ₗ[ℝ] HermitianMat k ℂ where
  toFun M := ⟨(1/2 : ℝ) • (M+Mᴴ), (Matrix.isHermitian_add_transpose_self M).smul (by simp)⟩
  map_add' M N := by
    apply HermitianMat.ext
    change (1/2 : ℝ) • (M+N+(M+N)ᴴ) = (1/2 : ℝ) • (M+Mᴴ)+(1/2 : ℝ) • (N+Nᴴ)
    rw [Matrix.conjTranspose_add]
    module
  map_smul' c M := by
    apply HermitianMat.ext
    change (1/2 : ℝ) • (c • M+(c • M)ᴴ) = c • ((1/2 : ℝ) • (M+Mᴴ))
    simp only [Matrix.conjTranspose_smul,star_trivial]
    module

def hermitianPart : Matrix k k ℂ →L[ℝ] HermitianMat k ℂ := hermitianPartLM.toContinuousLinearMap

theorem hermitianPart_mat (A : HermitianMat k ℂ) : hermitianPart A.mat = A := by
  apply HermitianMat.ext
  change (1/2 : ℝ) • (A.mat+A.matᴴ) = A.mat
  rw [A.H.eq]
  module

def logHermDeriv (A : HermitianMat k ℂ) : HermitianMat k ℂ →L[ℝ] HermitianMat k ℂ :=
  hermitianPart.comp (BetaLog.logDeriv A.mat)

theorem logHermDeriv_mat {A : HermitianMat k ℂ} (hA : A.mat.PosDef) (H : HermitianMat k ℂ) :
    (logHermDeriv A H).mat = BetaLogKM.inverseKM A.mat H := by
  have hh : (BetaLog.logDeriv A.mat H).IsHermitian := BetaLog.logDeriv_isHermitian hA H
  have he := hermitianPart_mat (⟨BetaLog.logDeriv A.mat H,hh⟩ : HermitianMat k ℂ)
  have hm := congrArg HermitianMat.mat he
  change (hermitianPart (BetaLog.logDeriv A.mat H)).mat = BetaLog.logDeriv A.mat H at hm
  change (hermitianPart (BetaLog.logDeriv A.mat H)).mat = _
  rw [hm,BetaLogKM.logDeriv_eq_inverseKM_clm hA]

theorem hasStrictFDerivAt_hermLog {A : HermitianMat k ℂ} (hA : A.mat.PosDef) :
    HasStrictFDerivAt hermLog (logHermDeriv A) A := by
  have hd := hermitianPart.hasStrictFDerivAt.comp A (BetaLogRegularity.hasStrictFDerivAt_logarithm hA)
  apply hd.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro B
  exact hermitianPart_mat (hermLog B)

def pinchLM : HermitianMat (r ⊕ s) ℂ →ₗ[ℝ] Blocks r s where
  toFun A := (pinchLeft A,pinchRight A)
  map_add' A B := by
    apply Prod.ext <;> apply HermitianMat.ext <;> rfl
  map_smul' c A := by
    apply Prod.ext <;> apply HermitianMat.ext <;> rfl

def pinchCLM : HermitianMat (r ⊕ s) ℂ →L[ℝ] Blocks r s := pinchLM.toContinuousLinearMap

@[simp] theorem pinchCLM_apply (A : HermitianMat (r ⊕ s) ℂ) :
    pinchCLM A = (pinchLeft A,pinchRight A) := rfl

def blockLog (W : Blocks r s) : Blocks r s := (hermLog W.1,hermLog W.2)

def blockLogDeriv (W : Blocks r s) : Blocks r s →L[ℝ] Blocks r s :=
  ((logHermDeriv W.1).comp (ContinuousLinearMap.fst ℝ _ _)).prod
    ((logHermDeriv W.2).comp (ContinuousLinearMap.snd ℝ _ _))

theorem hasStrictFDerivAt_blockLog {W : Blocks r s} (hA : W.1.mat.PosDef) (hB : W.2.mat.PosDef) :
    HasStrictFDerivAt blockLog (blockLogDeriv W) W := by
  exact ((hasStrictFDerivAt_hermLog hA).comp W hasStrictFDerivAt_fst).prodMk
    ((hasStrictFDerivAt_hermLog hB).comp W hasStrictFDerivAt_snd)

/-- The full W derivative of the matrix-valued stationarity residual. -/
def residualDerivative (J : HermitianMat (r ⊕ s) ℂ) (W : Blocks r s) : Blocks r s →L[ℝ] Blocks r s :=
  blockLogDeriv W-pinchCLM.comp ((logHermDeriv (J+BetaDual.diagonal W)).comp diagonalCLM)

theorem hasStrictFDerivAt_stationaryResidual {J : HermitianMat (r ⊕ s) ℂ} (lambda₀ lambda₁ : ℝ)
    {W : Blocks r s} (hA : W.1.mat.PosDef) (hB : W.2.mat.PosDef)
    (hT : (J+BetaDual.diagonal W).mat.PosDef) :
    HasStrictFDerivAt (stationaryResidual J lambda₀ lambda₁) (residualDerivative J W) W := by
  have hl := (diagonalCLM (r := r) (s := s)).hasStrictFDerivAt (x := W) |>.const_add J
  have ht := (hasStrictFDerivAt_hermLog hT).comp W hl
  have hp := (pinchCLM (r := r) (s := s)).hasStrictFDerivAt.comp W ht
  convert! ((hasStrictFDerivAt_blockLog hA hB).sub hp).sub_const
    (lambda₀ • (1 : HermitianMat r ℂ),lambda₁ • (1 : HermitianMat s ℂ)) using 1

def parameterDerivative (J : HermitianMat (r ⊕ s) ℂ) (W : Blocks r s) :
    HermitianMat (r ⊕ s) ℂ →L[ℝ] Blocks r s := -pinchCLM.comp (logHermDeriv (J+BetaDual.diagonal W))

def jointDerivative (J : HermitianMat (r ⊕ s) ℂ) (W : Blocks r s) :
    (HermitianMat (r ⊕ s) ℂ × Blocks r s) →L[ℝ] Blocks r s :=
  (parameterDerivative J W).comp (ContinuousLinearMap.fst ℝ _ _)+
    (residualDerivative J W).comp (ContinuousLinearMap.snd ℝ _ _)

/-- Joint strict derivative with respect to J and W, required by the implicit function theorem. -/
theorem hasStrictFDerivAt_jointResidual (lambda₀ lambda₁ : ℝ)
    {J : HermitianMat (r ⊕ s) ℂ} {W : Blocks r s} (hA : W.1.mat.PosDef) (hB : W.2.mat.PosDef)
    (hT : (J+BetaDual.diagonal W).mat.PosDef) :
    HasStrictFDerivAt (fun X : HermitianMat (r ⊕ s) ℂ × Blocks r s =>
      stationaryResidual X.1 lambda₀ lambda₁ X.2) (jointDerivative J W) (J,W) := by
  let L : (HermitianMat (r ⊕ s) ℂ × Blocks r s) →L[ℝ] HermitianMat (r ⊕ s) ℂ :=
    ContinuousLinearMap.fst ℝ _ _+diagonalCLM.comp (ContinuousLinearMap.snd ℝ _ _)
  have ht : HasStrictFDerivAt (fun X : HermitianMat (r ⊕ s) ℂ × Blocks r s =>
      hermLog (X.1+BetaDual.diagonal X.2)) ((logHermDeriv (J+BetaDual.diagonal W)).comp L) (J,W) :=
    (hasStrictFDerivAt_hermLog hT).comp (J,W) L.hasStrictFDerivAt
  have hp := (pinchCLM (r := r) (s := s)).hasStrictFDerivAt.comp (J,W) ht
  have hw : HasStrictFDerivAt (fun X : HermitianMat (r ⊕ s) ℂ × Blocks r s => blockLog X.2)
      ((blockLogDeriv W).comp (ContinuousLinearMap.snd ℝ _ _)) (J,W) := by
    convert! (hasStrictFDerivAt_blockLog (W := W) hA hB).comp (J,W)
      ((ContinuousLinearMap.snd ℝ (HermitianMat (r ⊕ s) ℂ) (Blocks r s)).hasStrictFDerivAt (x := (J,W))) using 1
  convert! (hw.sub hp).sub_const
    (lambda₀ • (1 : HermitianMat r ℂ),lambda₁ • (1 : HermitianMat s ℂ)) using 1
  apply ContinuousLinearMap.ext
  intro X
  change -pinchCLM (logHermDeriv (J+BetaDual.diagonal W) X.1)+
      (blockLogDeriv W X.2-pinchCLM (logHermDeriv (J+BetaDual.diagonal W) (BetaDual.diagonal X.2))) =
    blockLogDeriv W X.2-pinchCLM (logHermDeriv (J+BetaDual.diagonal W) (X.1+BetaDual.diagonal X.2))
  rw [map_add,map_add]
  abel

/-- The block pairing is a real continuous linear map into the whole dual space. -/
def blockPairingLM : Blocks r s →ₗ[ℝ] (Blocks r s →L[ℝ] ℝ) where
  toFun R := (innerSL ℝ R.1).comp (ContinuousLinearMap.fst ℝ _ _)+
    (innerSL ℝ R.2).comp (ContinuousLinearMap.snd ℝ _ _)
  map_add' R S := by
    apply ContinuousLinearMap.ext
    intro H
    simp [inner_add_left]
    ring
  map_smul' c R := by
    apply ContinuousLinearMap.ext
    intro H
    simp

def blockPairing : Blocks r s →L[ℝ] (Blocks r s →L[ℝ] ℝ) := blockPairingLM.toContinuousLinearMap

@[simp] theorem blockPairing_apply (R H : Blocks r s) :
    blockPairing R H = inner ℝ R.1 H.1+inner ℝ R.2 H.2 := rfl

theorem gradient_eq_blockPairing (J : HermitianMat (r ⊕ s) ℂ) (lambda₀ lambda₁ : ℝ)
    (W : Blocks r s) : gradient J lambda₀ lambda₁ W = blockPairing (stationaryResidual J lambda₀ lambda₁ W) := by
  apply ContinuousLinearMap.ext
  intro H
  rw [gradient_apply,blockPairing_apply]
  simp only [real_inner_comm,HermitianMat.inner_eq_re_trace]
  rfl

/-- Actual derivative of the entire gradient, rather than only one fixed row. -/
theorem hasStrictFDerivAt_gradient {J : HermitianMat (r ⊕ s) ℂ} (lambda₀ lambda₁ : ℝ)
    {W : Blocks r s} (hA : W.1.mat.PosDef) (hB : W.2.mat.PosDef)
    (hT : (J+BetaDual.diagonal W).mat.PosDef) :
    HasStrictFDerivAt (gradient J lambda₀ lambda₁) (blockPairing.comp (residualDerivative J W)) W := by
  have hd := (blockPairing (r := r) (s := s)).hasStrictFDerivAt (x := stationaryResidual J lambda₀ lambda₁ W) |>.comp W
    (hasStrictFDerivAt_stationaryResidual lambda₀ lambda₁ hA hB hT)
  apply hd.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun Z => (gradient_eq_blockPairing J lambda₀ lambda₁ Z).symm)

/-- The full residual derivative agrees with the already verified W-Hessian. -/
theorem residualDerivative_pairing {J : HermitianMat (r ⊕ s) ℂ} {W : Blocks r s}
    (hA : W.1.mat.PosDef) (hB : W.2.mat.PosDef) (hT : (J+BetaDual.diagonal W).mat.PosDef)
    (H K : Blocks r s) : blockPairing (residualDerivative J W K) H = hessianRow J W H K := by
  have hd := (hasStrictFDerivAt_gradient (0 : ℝ) 0 hA hB hT).hasFDerivAt.clm_apply
    (hasFDerivAt_const (x := W) H)
  have hr := hasFDerivAt_gradient_row (0 : ℝ) 0 hA hB hT H
  have he := congrArg (fun L : Blocks r s →L[ℝ] ℝ => L K) (hd.unique hr)
  simpa using he

theorem residualDerivative_self_pos {J : HermitianMat (r ⊕ s) ℂ} {W : Blocks r s}
    (hJ : J.mat.PosDef) (hA : W.1.mat.PosDef) (hB : W.2.mat.PosDef)
    {H : Blocks r s} (hne : H ≠ 0) : 0 < blockPairing (residualDerivative J W H) H := by
  rw [residualDerivative_pairing hA hB (total_posDef hJ hA hB)]
  exact hessianRow_self_pos hJ hA hB hne

theorem residualDerivative_injective {J : HermitianMat (r ⊕ s) ℂ} {W : Blocks r s}
    (hJ : J.mat.PosDef) (hA : W.1.mat.PosDef) (hB : W.2.mat.PosDef) :
    Function.Injective (residualDerivative J W) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro H hH
  by_contra hne
  have hp := residualDerivative_self_pos hJ hA hB hne
  rw [hH,map_zero] at hp
  exact (lt_irrefl 0) hp

/-- Positive Hessian supplies the genuine continuous linear inverse used by IFT. -/
theorem residualDerivative_isInvertible {J : HermitianMat (r ⊕ s) ℂ} {W : Blocks r s}
    (hJ : J.mat.PosDef) (hA : W.1.mat.PosDef) (hB : W.2.mat.PosDef) :
    (residualDerivative J W).IsInvertible := by
  have hi := residualDerivative_injective hJ hA hB
  let e : Blocks r s ≃ₗ[ℝ] Blocks r s := LinearEquiv.ofBijective (residualDerivative J W).toLinearMap
    ⟨hi,LinearMap.injective_iff_surjective.mp hi⟩
  exact ⟨e.toContinuousLinearEquiv,rfl⟩

@[simp] theorem jointDerivative_comp_inr (J : HermitianMat (r ⊕ s) ℂ) (W : Blocks r s) :
    (jointDerivative J W).comp (ContinuousLinearMap.inr ℝ _ _) = residualDerivative J W := by
  apply ContinuousLinearMap.ext
  intro H
  simp [jointDerivative]

@[simp] theorem jointDerivative_comp_inl (J : HermitianMat (r ⊕ s) ℂ) (W : Blocks r s) :
    (jointDerivative J W).comp (ContinuousLinearMap.inl ℝ _ _) = parameterDerivative J W := by
  apply ContinuousLinearMap.ext
  intro H
  simp [jointDerivative]

end QubitAdditivity.BetaDualDerivative
