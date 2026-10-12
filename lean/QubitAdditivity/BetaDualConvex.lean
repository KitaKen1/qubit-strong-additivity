import QubitAdditivity.BetaDual
import Mathlib.Analysis.Convex.Deriv

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Topology

namespace QubitAdditivity.BetaDualConvex
open BetaDual
@[reducible] local instance hTop {k : Type*} [Fintype k] : TopologicalSpace (HermitianMat k ℂ) :=
  HermitianMat.instNormedAddCommGroupComplex.toUniformSpace.toTopologicalSpace
@[reducible] local instance hAdd {k : Type*} [Fintype k] : AddCommGroup (HermitianMat k ℂ) :=
  HermitianMat.instNormedAddCommGroupComplex.toAddCommGroup
@[reducible] local instance hModule {k : Type*} [Fintype k] : Module ℝ (HermitianMat k ℂ) :=
  HermitianMat.instNormedSpace.toModule

variable {r s : Type*} [Fintype r] [Fintype s] [DecidableEq r] [DecidableEq s]

def positiveInterior : Set (Blocks r s) := {W | W.1.mat.PosDef ∧ W.2.mat.PosDef}

theorem posDef_convex_combination {k : Type*} [Fintype k] [DecidableEq k]
    {A B : Matrix k k ℂ} (hA : A.PosDef) (hB : B.PosDef) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b = 1) : (a • A+b • B).PosDef := by
  by_cases hz : a = 0
  · have he : b = 1 := by simpa only [hz,zero_add] using hab
    simpa only [hz,he,zero_smul,one_smul,zero_add] using hB
  · exact (hA.smul (lt_of_le_of_ne ha (Ne.symm hz))).add_posSemidef (hB.posSemidef.smul hb)

theorem convex_positiveInterior : Convex ℝ (positiveInterior (r := r) (s := s)) := by
  intro W hW Z hZ a b ha hb hab
  constructor
  · convert! posDef_convex_combination hW.1 hZ.1 ha hb hab using 1
  · convert! posDef_convex_combination hW.2 hZ.2 ha hb hab using 1

def line (W H : Blocks r s) (t : ℝ) : Blocks r s := W+t • H

theorem continuous_line (W H : Blocks r s) : Continuous (line W H) := by
  unfold line
  fun_prop

theorem hasDerivAt_line (W H : Blocks r s) (t : ℝ) : HasDerivAt (line W H) H t := by
  convert! ((hasDerivAt_id t).smul_const H).const_add W using 1 <;> simp

theorem hasDerivAt_objective_line {J : HermitianMat (r ⊕ s) ℂ} (lambda₀ lambda₁ : ℝ)
    (W H : Blocks r s) {t : ℝ} (hA : (line W H t).1.mat.PosDef)
    (hB : (line W H t).2.mat.PosDef) (hT : (J+diagonal (line W H t)).mat.PosDef) :
    HasDerivAt (fun u : ℝ => objective J lambda₀ lambda₁ (line W H u))
      (gradient J lambda₀ lambda₁ (line W H t) H) t := by
  convert! (hasFDerivAt_objective lambda₀ lambda₁ hA hB hT).comp_hasDerivAt t
    (hasDerivAt_line W H t) using 1

/-- The true second derivative along an affine line equals the W-Hessian. -/
theorem hasDerivAt_deriv_objective_line {J : HermitianMat (r ⊕ s) ℂ} (lambda₀ lambda₁ : ℝ)
    (W H : Blocks r s) {t : ℝ} (hA : (line W H t).1.mat.PosDef)
    (hB : (line W H t).2.mat.PosDef) (hT : (J+diagonal (line W H t)).mat.PosDef) :
    HasDerivAt (deriv (fun u : ℝ => objective J lambda₀ lambda₁ (line W H u)))
      (hessianRow J (line W H t) H H) t := by
  have hd : HasDerivAt (fun u : ℝ => gradient J lambda₀ lambda₁ (line W H u) H)
      (hessianRow J (line W H t) H H) t := by
    convert! (hasFDerivAt_gradient_row lambda₀ lambda₁ hA hB hT H).comp_hasDerivAt t
      (hasDerivAt_line W H t) using 1
  have ha : ∀ᶠ u : ℝ in 𝓝 t, (line W H u).1.mat.PosDef :=
    (continuous_fst.comp (continuous_line W H)).tendsto t |>.eventually (BetaLog.eventually_posDef hA)
  have hb : ∀ᶠ u : ℝ in 𝓝 t, (line W H u).2.mat.PosDef :=
    (continuous_snd.comp (continuous_line W H)).tendsto t |>.eventually (BetaLog.eventually_posDef hB)
  have hc : Continuous (fun u : ℝ => J+diagonal (line W H u)) := by
    convert! continuous_const.add ((diagonalCLM (r := r) (s := s)).continuous.comp
      (continuous_line W H)) using 1
  have ht : ∀ᶠ u : ℝ in 𝓝 t, (J+diagonal (line W H u)).mat.PosDef :=
    (hc.tendsto t).eventually (BetaLog.eventually_posDef hT)
  apply hd.congr_of_eventuallyEq
  filter_upwards [ha,hb,ht] with u hu₀ hu₁ hut
  exact (hasDerivAt_objective_line lambda₀ lambda₁ W H hu₀ hu₁ hut).deriv

theorem line_mem_positiveInterior {W Z : Blocks r s} (hW : W ∈ positiveInterior)
    (hZ : Z ∈ positiveInterior) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    line W (Z-W) t ∈ positiveInterior := by
  have he : line W (Z-W) t = (1-t) • W+t • Z := by unfold line; module
  rw [he]
  exact convex_positiveInterior hW hZ (sub_nonneg.mpr ht.2) ht.1 (by ring)

theorem strictConvexOn_objective_line {J : HermitianMat (r ⊕ s) ℂ} (lambda₀ lambda₁ : ℝ)
    (hJ : J.mat.PosDef) {W Z : Blocks r s} (hW : W ∈ positiveInterior)
    (hZ : Z ∈ positiveInterior) (hne : W ≠ Z) :
    StrictConvexOn ℝ (Icc (0 : ℝ) 1)
      (fun t : ℝ => objective J lambda₀ lambda₁ (line W (Z-W) t)) := by
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) := line_mem_positiveInterior hW hZ ht
  have hn : Z-W ≠ 0 := sub_ne_zero.mpr hne.symm
  apply strictConvexOn_of_deriv2_pos' (convex_Icc _ _)
  · intro t ht
    exact (hasDerivAt_objective_line lambda₀ lambda₁ W (Z-W) (hp t ht).1 (hp t ht).2
      (total_posDef hJ (hp t ht).1 (hp t ht).2)).continuousAt.continuousWithinAt
  · intro t ht
    change 0 < deriv (deriv (fun u : ℝ => objective J lambda₀ lambda₁ (line W (Z-W) u))) t
    rw [(hasDerivAt_deriv_objective_line lambda₀ lambda₁ W (Z-W) (hp t ht).1 (hp t ht).2
      (total_posDef hJ (hp t ht).1 (hp t ht).2)).deriv]
    exact hessianRow_self_pos hJ (hp t ht).1 (hp t ht).2 hn

/-- Actual strict convexity on the positive block cone. -/
theorem strictConvexOn_objective {J : HermitianMat (r ⊕ s) ℂ} (lambda₀ lambda₁ : ℝ)
    (hJ : J.mat.PosDef) : StrictConvexOn ℝ positiveInterior (objective J lambda₀ lambda₁) := by
  refine ⟨convex_positiveInterior,?_⟩
  intro W hW Z hZ hne a b ha hb hab
  have hs := strictConvexOn_objective_line lambda₀ lambda₁ hJ hW hZ hne
  have hi := hs.2 (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp) (by norm_num : (0 : ℝ) ≠ 1) ha hb hab
  have he : line W (Z-W) (a • (0 : ℝ)+b • (1 : ℝ)) = a • W+b • Z := by
    simp only [smul_eq_mul,mul_zero,mul_one,zero_add,line]
    have hh : 1-b = a := by linarith
    calc
      W+b • (Z-W) = (1-b) • W+b • Z := by module
      _ = _ := by rw [hh]
  have h₀ : line W (Z-W) 0 = W := by simp [line]
  have h₁ : line W (Z-W) 1 = Z := by simp [line]
  simpa only [he,h₀,h₁] using hi

/-- Positive-definite minima on the original closed cone are unique.
Existence and exclusion of singular boundary minima remain separate tasks. -/
theorem eq_of_minOn_positiveCone {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosDef) {W Z : Blocks r s} (hW : W ∈ positiveInterior)
    (hZ : Z ∈ positiveInterior) (hw : IsMinOn (objective J lambda₀ lambda₁) positiveCone W)
    (hz : IsMinOn (objective J lambda₀ lambda₁) positiveCone Z) : W = Z := by
  apply (strictConvexOn_objective lambda₀ lambda₁ hJ).eq_of_isMinOn
    (fun U hu => hw ⟨hu.1.posSemidef,hu.2.posSemidef⟩)
    (fun U hu => hz ⟨hu.1.posSemidef,hu.2.posSemidef⟩) hW hZ

end QubitAdditivity.BetaDualConvex
