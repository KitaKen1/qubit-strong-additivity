import QubitAdditivity.BetaValueHessian
import Mathlib.Analysis.Convex.Deriv

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

namespace QubitAdditivity.BetaDualConcave
open BetaDual BetaDualConvex BetaDualInterior BetaDualDerivative BetaMinimizer BetaEntropy BetaDualValue
open BetaValueHessian

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

/-- Positive-definite input domain of the true minimized dual function. -/
def positiveInputs : Set (HermitianMat (r ⊕ s) ℂ) := {J | J.mat.PosDef}

theorem convex_positiveInputs : Convex ℝ (positiveInputs (r := r) (s := s)) := by
  intro J hJ K hK a b ha hb hab
  convert! posDef_convex_combination hJ hK ha hb hab using 1

def inputLine (J H : HermitianMat (r ⊕ s) ℂ) (t : ℝ) : HermitianMat (r ⊕ s) ℂ := J+t • H

theorem continuous_inputLine (J H : HermitianMat (r ⊕ s) ℂ) : Continuous (inputLine J H) := by
  unfold inputLine
  fun_prop

theorem hasDerivAt_inputLine (J H : HermitianMat (r ⊕ s) ℂ) (t : ℝ) : HasDerivAt (inputLine J H) H t := by
  convert! ((hasDerivAt_id t).smul_const H).const_add J using 1 <;> simp

theorem inputLine_mem_positiveInputs {J K : HermitianMat (r ⊕ s) ℂ} (hJ : J ∈ positiveInputs)
    (hK : K ∈ positiveInputs) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    inputLine J (K-J) t ∈ positiveInputs := by
  have he : inputLine J (K-J) t = (1-t) • J+t • K := by unfold inputLine; module
  rw [he]
  exact convex_positiveInputs hJ hK (sub_nonneg.mpr ht.2) ht.1 (by ring)

theorem hasDerivAt_value_line {lambda₀ lambda₁ : ℝ} (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0)
    (J H : HermitianMat (r ⊕ s) ℂ) {t : ℝ} (hJ : (inputLine J H t).mat.PosDef) :
    HasDerivAt (fun u : ℝ => value (inputLine J H u) lambda₀ lambda₁)
      (valueGradient (inputLine J H t) lambda₀ lambda₁ H) t := by
  convert! (hasFDerivAt_value hJ hl₀ hl₁).comp_hasDerivAt t (hasDerivAt_inputLine J H t) using 1

/-- The true scalar second derivative uses the already identified Schur Hessian. -/
theorem hasDerivAt_deriv_value_line {lambda₀ lambda₁ : ℝ} (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0)
    (J H : HermitianMat (r ⊕ s) ℂ) {t : ℝ} (hJ : (inputLine J H t).mat.PosDef) :
    HasDerivAt (deriv (fun u : ℝ => value (inputLine J H u) lambda₀ lambda₁))
      (valueHessianRow (inputLine J H t) lambda₀ lambda₁ H H) t := by
  have hd : HasDerivAt (fun u : ℝ => valueGradient (inputLine J H u) lambda₀ lambda₁ H)
      (valueHessianRow (inputLine J H t) lambda₀ lambda₁ H H) t := by
    convert! (hasFDerivAt_valueGradient_row hJ hl₀ hl₁ H).comp_hasDerivAt t
      (hasDerivAt_inputLine J H t) using 1
  have hp : ∀ᶠ u : ℝ in 𝓝 t, (inputLine J H u).mat.PosDef :=
    (continuous_inputLine J H).tendsto t |>.eventually (BetaLog.eventually_posDef hJ)
  apply hd.congr_of_eventuallyEq
  filter_upwards [hp] with u hu
  exact (hasDerivAt_value_line hl₀ hl₁ J H hu).deriv

theorem concaveOn_value_line {lambda₀ lambda₁ : ℝ} (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0)
    {J K : HermitianMat (r ⊕ s) ℂ} (hJ : J ∈ positiveInputs) (hK : K ∈ positiveInputs) :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) (fun t : ℝ => value (inputLine J (K-J) t) lambda₀ lambda₁) := by
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) := inputLine_mem_positiveInputs hJ hK ht
  apply concaveOn_of_deriv2_nonpos' (convex_Icc _ _)
  · intro t ht
    exact (hasDerivAt_value_line hl₀ hl₁ J (K-J) (hp t ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    exact (hasDerivAt_deriv_value_line hl₀ hl₁ J (K-J) (hp t ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    change deriv (deriv (fun u : ℝ => value (inputLine J (K-J) u) lambda₀ lambda₁)) t ≤ 0
    rw [(hasDerivAt_deriv_value_line hl₀ hl₁ J (K-J) (hp t ht)).deriv]
    exact valueHessianRow_self_nonpos (hp t ht) hl₀ hl₁ (K-J)

/-- Actual concavity of the manuscript's minimized dual value on all J>0. -/
theorem concaveOn_value {lambda₀ lambda₁ : ℝ} (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) :
    ConcaveOn ℝ positiveInputs (fun J : HermitianMat (r ⊕ s) ℂ => value J lambda₀ lambda₁) := by
  refine ⟨convex_positiveInputs,?_⟩
  intro J hJ K hK a b ha hb hab
  have hs := concaveOn_value_line hl₀ hl₁ hJ hK
  have hi := hs.2 (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) ha hb hab
  have he : inputLine J (K-J) (a • (0 : ℝ)+b • (1 : ℝ)) = a • J+b • K := by
    simp only [smul_eq_mul,mul_zero,mul_one,zero_add,inputLine]
    have hh : 1-b = a := by linarith
    calc
      J+b • (K-J) = (1-b) • J+b • K := by module
      _ = _ := by rw [hh]
  have h₀ : inputLine J (K-J) 0 = J := by simp [inputLine]
  have h₁ : inputLine J (K-J) 1 = K := by simp [inputLine]
  simpa only [he,h₀,h₁] using hi

end QubitAdditivity.BetaDualConcave
