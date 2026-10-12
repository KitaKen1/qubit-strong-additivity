import QubitAdditivity.BetaDualExistence
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

namespace QubitAdditivity.BetaBoundaryEntropy
open BetaEntropy

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



variable {k : Type*} [Fintype k] [DecidableEq k]

theorem psi_eq_sum (A : HermitianMat k ℂ) :
    psi A = ∑ i, A.H.eigenvalues i * Real.log (A.H.eigenvalues i) := by
  simp [psi,OpenAIEntropy.entropy_eq_sum A.H,Real.negMulLog,Finset.sum_neg_distrib]

/-- Shifted eigenvalues are read in the fixed basis of A, including repeated zero eigenvalues. -/
theorem psi_shift_eq_sum (A : HermitianMat k ℂ) (t : ℝ) :
    psi (A+t • 1) = ∑ i, (A.H.eigenvalues i+t)*Real.log (A.H.eigenvalues i+t) := by
  have hshift : A.cfc (fun x => x+t) = A+t • 1 := by
    convert! HermitianMat.cfc_add_apply A id (fun _ => t) using 1 <;> simp
  have he (B : HermitianMat k ℂ) : psi B = -(B.cfc Real.negMulLog).trace := by
    convert! rfl using 1
  rw [he,← hshift,← HermitianMat.cfc_comp_apply,HermitianMat.trace_cfc_eq]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [Real.negMulLog]
  ring

/-- A uniform upper bound for all nonselected spectral increments. -/
theorem scalar_increment_div_le {a t : ℝ} (ha : 0 ≤ a) (ht : 0 < t) (ht₁ : t ≤ 1) :
    ((a+t)*Real.log (a+t)-a*Real.log a)/t ≤ Real.log (a+1)+1 := by
  have hap : 0 < a+t := by linarith
  have hi := Real.convexOn_mul_log.slope_le_of_hasDerivAt (x := a) (y := a+t)
    ha hap.le (by linarith) (Real.hasDerivAt_mul_log hap.ne')
  have hl : Real.log (a+t)+1 ≤ Real.log (a+1)+1 := by
    exact add_le_add (Real.log_le_log hap (show a+t ≤ a+1 by linarith)) le_rfl
  simpa [slope_def_field] using hi.trans hl

/-- A single zero eigenvalue supplies the logarithmic boundary descent. -/
theorem psi_shift_div_le {A : HermitianMat k ℂ} (hA : A.mat.PosSemidef)
    (i₀ : k) (hi₀ : A.H.eigenvalues i₀ = 0) {t : ℝ} (ht : 0 < t) (ht₁ : t ≤ 1) :
    (psi (A+t • 1)-psi A)/t ≤ Real.log t+
      ∑ i ∈ Finset.univ.erase i₀, (Real.log (A.H.eigenvalues i+1)+1) := by
  let q : k → ℝ := fun i => ((A.H.eigenvalues i+t)*Real.log (A.H.eigenvalues i+t)-
    A.H.eigenvalues i*Real.log (A.H.eigenvalues i))/t
  have hzero : q i₀ = Real.log t := by simp [q,hi₀,ht.ne']
  have hsum : ∑ i ∈ Finset.univ.erase i₀, q i ≤
      ∑ i ∈ Finset.univ.erase i₀, (Real.log (A.H.eigenvalues i+1)+1) := by
    exact Finset.sum_le_sum (fun i _ => scalar_increment_div_le (hA.eigenvalues_nonneg i) ht ht₁)
  rw [psi_shift_eq_sum,psi_eq_sum,← Finset.sum_sub_distrib,Finset.sum_div]
  change (∑ i, q i) ≤ _
  calc
    _ = (∑ i ∈ Finset.univ.erase i₀, q i)+q i₀ := (Finset.sum_erase_add _ _ (Finset.mem_univ i₀)).symm
    _ ≤ (∑ i ∈ Finset.univ.erase i₀, (Real.log (A.H.eigenvalues i+1)+1))+Real.log t := by
      rw [hzero]
      exact add_le_add hsum le_rfl
    _ = _ := add_comm _ _

/-- Singular PSD matrices have entropy-gradient slope tending to minus infinity. -/
theorem tendsto_psi_shift_div_atBot {A : HermitianMat k ℂ} (hA : A.mat.PosSemidef)
    (hnot : ¬ A.mat.PosDef) :
    Tendsto (fun t : ℝ => (psi (A+t • 1)-psi A)/t) (𝓝[>] 0) atBot := by
  have hx : ∃ i, A.H.eigenvalues i = 0 := by
    have hh : ¬ ∀ i, 0 < A.H.eigenvalues i := by
      intro hh
      exact hnot (A.H.posDef_iff_eigenvalues_pos.mpr hh)
    push_neg at hh
    obtain ⟨i,hi⟩ := hh
    exact ⟨i,le_antisymm hi (hA.eigenvalues_nonneg i)⟩
  obtain ⟨i₀,hi₀⟩ := hx
  let C := ∑ i ∈ Finset.univ.erase i₀, (Real.log (A.H.eigenvalues i+1)+1)
  have hl : Tendsto (fun t : ℝ => Real.log t+C) (𝓝[>] 0) atBot :=
    tendsto_atBot_add_const_right _ _ Real.tendsto_log_nhdsGT_zero
  apply tendsto_atBot.2
  intro b
  filter_upwards [hl.eventually_le_atBot b,self_mem_nhdsWithin,
    (show ∀ᶠ t : ℝ in 𝓝[>] 0, t ≤ 1 from
      (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds)] with t hb ht ht₁
  exact (psi_shift_div_le hA i₀ hi₀ ht ht₁).trans hb

/-- A finite differentiable correction cannot cancel descent of a zero eigenvalue. -/
theorem exists_boundary_descent {A : HermitianMat k ℂ} (hA : A.mat.PosSemidef)
    (hnot : ¬ A.mat.PosDef) {g : ℝ → ℝ} {g' : ℝ} (hg : HasDerivAt g g' 0) :
    ∃ t : ℝ, 0 < t ∧ psi (A+t • 1)+g t < psi A+g 0 := by
  have hp := tendsto_psi_shift_div_atBot hA hnot
  have hs : Tendsto (fun t : ℝ => (g t-g 0)/t) (𝓝[>] 0) (𝓝 g') := by
    convert! hg.tendsto_slope_zero_right using 1
    ext t
    simp [smul_eq_mul,div_eq_mul_inv,mul_comm]
  have hb : ∀ᶠ t : ℝ in 𝓝[>] 0, (g t-g 0)/t < g'+1 :=
    hs.eventually (gt_mem_nhds (by linarith : g' < g'+1))
  have hc := hp.eventually_lt_atBot (-g'-1)
  have htpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t,ht,htg,htp⟩ := (htpos.and (hb.and hc)).exists
  have ht : 0 < t := ht
  have hn : (psi (A+t • 1)-psi A)/t+(g t-g 0)/t < 0 := by linarith
  have hh : psi (A+t • 1)-psi A+(g t-g 0) < 0 := by
    have hi := (div_lt_iff₀ ht).mp (show
      (psi (A+t • 1)-psi A+(g t-g 0))/t < 0 by rw [add_div]; exact hn)
    simpa using hi
  exact ⟨t,ht,by linarith⟩

end QubitAdditivity.BetaBoundaryEntropy
