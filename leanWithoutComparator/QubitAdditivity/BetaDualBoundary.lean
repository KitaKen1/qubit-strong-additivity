import QubitAdditivity.BetaDualConcave

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

namespace QubitAdditivity.BetaDualBoundary
open BetaDual BetaDualConvex BetaDualInterior BetaDualDerivative BetaMinimizer BetaEntropy BetaDualValue BetaDualExistence

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

theorem eq_zero_of_trace_zero {J : HermitianMat k ℂ} (hJ : J.mat.PosSemidef)
    (hz : J.mat.trace.re = 0) : J = 0 := by
  exact norm_eq_zero.mp (le_antisymm (by simpa [hz] using norm_le_trace hJ) (norm_nonneg J))

/-- The positive-input coercivity estimate extends to every PSD input by continuity. -/
theorem objective_lower_bound_psd {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ c : ℝ}
    (hJ : J.mat.PosSemidef) (hc₀ : c ≤ -lambda₀) (hc₁ : c ≤ -lambda₁)
    {W : Blocks r s} (hW : W ∈ positiveCone) :
    c*blockTrace W-J.mat.trace.re*(Real.log (blockTrace W+J.mat.trace.re)+1) ≤
      objective J lambda₀ lambda₁ W := by
  have hm : 0 ≤ J.mat.trace.re := le_trans (norm_nonneg J) (norm_le_trace hJ)
  by_cases hz : J.mat.trace.re = 0
  · have he := eq_zero_of_trace_zero hJ hz
    subst J
    have hp₀ := norm_le_trace hW.1
    have hp₁ := norm_le_trace hW.2
    have hl₀ := mul_le_mul_of_nonneg_right hc₀ (le_trans (norm_nonneg _) hp₀)
    have hl₁ := mul_le_mul_of_nonneg_right hc₁ (le_trans (norm_nonneg _) hp₁)
    rw [objective_eq]
    simp only [zero_add,HermitianMat.mat_zero,Matrix.trace_zero,Complex.zero_re,zero_mul,sub_zero]
    unfold blockTrace at *
    nlinarith
  have hp : 0 < J.mat.trace.re := lt_of_le_of_ne hm (Ne.symm hz)
  let f : ℝ → HermitianMat (r ⊕ s) ℂ := fun t => J+t • 1
  have hf : Continuous f := by unfold f; fun_prop
  have htr : Continuous (fun t => (f t).mat.trace.re) := by
    convert! (traceHerm (k := r ⊕ s)).continuous.comp hf using 1
  have hlog : ContinuousAt (fun t => Real.log (blockTrace W+(f t).mat.trace.re)) 0 := by
    have hq : 0 ≤ blockTrace W := blockTrace_nonneg hW
    have hqp : 0 < blockTrace W+J.mat.trace.re := by linarith
    have hn : blockTrace W+(f 0).mat.trace.re ≠ 0 := by simpa [f] using hqp.ne'
    exact (Real.continuousAt_log hn).comp (x := 0)
      (show ContinuousAt (fun t : ℝ => blockTrace W+(f t).mat.trace.re) 0 from
        (continuous_const.add htr).continuousAt)
  have hl : Tendsto (fun t => c*blockTrace W-(f t).mat.trace.re*(Real.log (blockTrace W+(f t).mat.trace.re)+1))
      (𝓝[>] 0) (𝓝 (c*blockTrace W-J.mat.trace.re*(Real.log (blockTrace W+J.mat.trace.re)+1))) := by
    have hh : ContinuousAt (fun t : ℝ => c*blockTrace W-
        (f t).mat.trace.re*(Real.log (blockTrace W+(f t).mat.trace.re)+1)) 0 :=
      continuousAt_const.sub (htr.continuousAt.mul (hlog.add continuousAt_const))
    simpa [f] using hh.tendsto.mono_left nhdsWithin_le_nhds
  have ho : Continuous (fun t => objective (f t) lambda₀ lambda₁ W) := by
    unfold objective
    exact continuous_const.sub (continuous_psi.comp (hf.add continuous_const)) |>.sub continuous_const
  have hr : Tendsto (fun t => objective (f t) lambda₀ lambda₁ W) (𝓝[>] 0)
      (𝓝 (objective J lambda₀ lambda₁ W)) := by
    have he : f (0 : ℝ) = J := by simp [f]
    have ht : Tendsto (fun t : ℝ => objective (f t) lambda₀ lambda₁ W) (𝓝[>] 0)
        (𝓝 (objective (f 0) lambda₀ lambda₁ W)) := (ho.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    rw [he] at ht
    exact ht
  apply le_of_tendsto_of_tendsto hl hr
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : 0 < t := ht
  have hj : (f t).mat.PosDef := by
    change (J.mat+t • (1 : Matrix (r ⊕ s) (r ⊕ s) ℂ)).PosDef
    rw [add_comm]
    exact (Matrix.PosDef.one.smul (α := ℝ) ht').add_posSemidef hJ
  exact objective_lower_bound hj hc₀ hc₁ hW

/-- One common lower bound for every bounded family of PSD inputs, including J=0. -/
theorem objective_uniform_lower_bound {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ c M : ℝ}
    (hJ : J.mat.PosSemidef) (hc₀ : c ≤ -lambda₀) (hc₁ : c ≤ -lambda₁)
    (hM : 1 ≤ M) (hmM : J.mat.trace.re ≤ M) {W : Blocks r s} (hW : W ∈ positiveCone) :
    c*blockTrace W-M*(Real.log (blockTrace W+M)+1) ≤ objective J lambda₀ lambda₁ W := by
  have hm : 0 ≤ J.mat.trace.re := le_trans (norm_nonneg J) (norm_le_trace hJ)
  have hq := blockTrace_nonneg hW
  have hL : 0 ≤ Real.log (blockTrace W+M)+1 := by
    have hh : 1 ≤ blockTrace W+M := by linarith
    linarith [Real.log_nonneg hh]
  have hi : J.mat.trace.re*(Real.log (blockTrace W+J.mat.trace.re)+1) ≤
      M*(Real.log (blockTrace W+M)+1) := by
    by_cases hz : J.mat.trace.re = 0
    · simpa [hz] using mul_nonneg (by linarith : 0 ≤ M) hL
    have hp : 0 < blockTrace W+J.mat.trace.re := by
      exact add_pos_of_nonneg_of_pos hq (lt_of_le_of_ne hm (Ne.symm hz))
    have hl := Real.log_le_log hp (show blockTrace W+J.mat.trace.re ≤ blockTrace W+M by linarith)
    exact (mul_le_mul_of_nonneg_left (add_le_add hl le_rfl) hm).trans
      (mul_le_mul_of_nonneg_right hmM hL)
  exact (sub_le_sub_left hi _).trans (objective_lower_bound_psd hJ hc₀ hc₁ hW)

/-- Uniform coercivity on any trace-bounded PSD input family. -/
theorem exists_uniform_trace_threshold {lambda₀ lambda₁ : ℝ} (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0)
    {M : ℝ} (hM : 1 ≤ M) (a : ℝ) : ∃ R : ℝ, ∀ (J : HermitianMat (r ⊕ s) ℂ) (W : Blocks r s),
      J.mat.PosSemidef → J.mat.trace.re ≤ M → W ∈ positiveCone → R ≤ blockTrace W →
        a ≤ objective J lambda₀ lambda₁ W := by
  let c := min (-lambda₀) (-lambda₁)
  have hc : 0 < c := lt_min (neg_pos.mpr hl₀) (neg_pos.mpr hl₁)
  obtain ⟨R,hR⟩ := eventually_atTop.1 ((tendsto_scalar_lower_bound c M hc).eventually_ge_atTop a)
  refine ⟨R,?_⟩
  intro J W hJ hmM hW hlarge
  exact (hR (blockTrace W) hlarge).trans
    (objective_uniform_lower_bound hJ (min_le_left _ _) (min_le_right _ _) hM hmM hW)

theorem objective_eventually_ge_psd {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosSemidef) (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) (a : ℝ) :
    ∀ᶠ W in cocompact (Blocks r s) ⊓ 𝓟 positiveCone, a ≤ objective J lambda₀ lambda₁ W := by
  obtain ⟨R,hR⟩ := exists_uniform_trace_threshold (r := r) (s := s) hl₀ hl₁
    (M := max 1 J.mat.trace.re) (le_max_left _ _) a
  rw [eventually_inf_principal]
  filter_upwards [(isCompact_traceSublevel (r := r) (s := s) R).compl_mem_cocompact]
    with W houtside hW
  have hlarge : R ≤ blockTrace W := by
    by_contra! hsmall
    exact houtside ⟨hW,hsmall.le⟩
  exact hR J W hJ (le_max_right _ _) hW hlarge

/-- Actual minima exist even for singular PSD inputs; no uniqueness or interiority is imposed. -/
theorem exists_minOn_positiveCone_psd {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosSemidef) (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) :
    ∃ W ∈ positiveCone, IsMinOn (objective J lambda₀ lambda₁) positiveCone W := by
  apply (continuous_objective J lambda₀ lambda₁).continuousOn.exists_isMinOn' isClosed_positiveCone
    (x₀ := (0 : Blocks r s))
  · constructor <;> exact Matrix.PosSemidef.zero
  · exact objective_eventually_ge_psd hJ hl₀ hl₁ _

theorem minimizer_spec_psd {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosSemidef) (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) :
    minimizer J lambda₀ lambda₁ ∈ positiveCone ∧
      IsMinOn (objective J lambda₀ lambda₁) positiveCone (minimizer J lambda₀ lambda₁) := by
  obtain ⟨W,hW,hmin⟩ := exists_minOn_positiveCone_psd hJ hl₀ hl₁
  exact Classical.epsilon_spec (p := fun W : Blocks r s =>
    W ∈ positiveCone ∧ IsMinOn (objective J lambda₀ lambda₁) positiveCone W) ⟨W,hW,hmin⟩

/-- Joint entropy continuity on the full real parameter space, including singular points. -/
theorem continuous_jointObjective (lambda₀ lambda₁ : ℝ) :
    Continuous (fun X : HermitianMat (r ⊕ s) ℂ × Blocks r s => objective X.1 lambda₀ lambda₁ X.2) := by
  have hd : Continuous (fun X : HermitianMat (r ⊕ s) ℂ × Blocks r s => BetaDual.diagonal X.2) :=
    (diagonalCLM (r := r) (s := s)).continuous.comp continuous_snd
  have hc : Continuous (fun X : HermitianMat (r ⊕ s) ℂ × Blocks r s =>
      psi (BetaDual.diagonal X.2)-psi (X.1+BetaDual.diagonal X.2)-linearPenalty lambda₀ lambda₁ X.2) :=
    ((continuous_psi.comp hd).sub (continuous_psi.comp (continuous_fst.add hd))).sub
      ((linearPenalty lambda₀ lambda₁).continuous.comp continuous_snd)
  convert! hc using 1
  apply funext
  intro X
  exact objective_eq X.1 lambda₀ lambda₁ X.2

/-- Every local trace-bounded family has all of its true minima in one compact set. -/
theorem continuousWithinAt_minimumValue_psd {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosSemidef) (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) :
    ContinuousWithinAt (fun K : HermitianMat (r ⊕ s) ℂ => minimumValue K lambda₀ lambda₁)
      {K | K.mat.PosSemidef} J := by
  let M := max 1 J.mat.trace.re+1
  let a := -psi J+1
  have hM : 1 ≤ M := (le_max_left (1 : ℝ) J.mat.trace.re).trans (le_add_of_nonneg_right zero_le_one)
  obtain ⟨R,hR⟩ := exists_uniform_trace_threshold (r := r) (s := s) hl₀ hl₁ hM a
  let C : Set (Blocks r s) := {W | W ∈ positiveCone ∧ blockTrace W ≤ R}
  have hm : ∀ᶠ K : HermitianMat (r ⊕ s) ℂ in 𝓝 J, K.mat.trace.re ≤ M := by
    have hc : Continuous (fun K : HermitianMat (r ⊕ s) ℂ => K.mat.trace.re) := by
      convert! (traceHerm (k := r ⊕ s)).continuous using 1
    have hJM : J.mat.trace.re < M := (le_max_right (1 : ℝ) J.mat.trace.re).trans_lt (lt_add_one _)
    have hlt : ∀ᶠ K : HermitianMat (r ⊕ s) ℂ in 𝓝 J, K.mat.trace.re < M :=
      (hc.continuousAt (x := J)).eventually_lt (continuousAt_const (x := J) (y := M)) hJM
    exact hlt.mono fun K hK => hK.le
  have ha : ∀ᶠ K : HermitianMat (r ⊕ s) ℂ in 𝓝 J, objective K lambda₀ lambda₁ (0 : Blocks r s) < a := by
    have hbase (K : HermitianMat (r ⊕ s) ℂ) : objective K lambda₀ lambda₁ (0 : Blocks r s) = -psi K := by
      rw [objective_eq]
      have hd : BetaDual.diagonal (0 : Blocks r s) = 0 := map_zero diagonalCLM
      rw [hd,add_zero]
      have hz : psi (0 : HermitianMat (r ⊕ s) ℂ) = 0 := by
        rw [psi_eq_trace]
        simp
      simp only [hz,zero_sub,HermitianMat.mat_zero,Matrix.trace_zero,Complex.zero_re,
        mul_zero,add_zero,sub_zero]
      change -psi K-(lambda₀*(0 : Matrix r r ℂ).trace.re+lambda₁*(0 : Matrix s s ℂ).trace.re) = -psi K
      simp
    have hh : ∀ᶠ K : HermitianMat (r ⊕ s) ℂ in 𝓝 J, -psi K < a :=
      ((continuous_psi (k := r ⊕ s)).neg.continuousAt (x := J)).eventually_lt
        (continuousAt_const (x := J) (y := a)) (lt_add_one _)
    exact hh.mono fun K hK => by rw [hbase K]; exact hK
  have he : ∀ᶠ K : HermitianMat (r ⊕ s) ℂ in 𝓝[{K | K.mat.PosSemidef}] J,
      minimumValue K lambda₀ lambda₁ = sInf (objective K lambda₀ lambda₁ '' C) := by
    filter_upwards [hm.filter_mono nhdsWithin_le_nhds,ha.filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin]
      with K hmK haK hK
    have hs := minimizer_spec_psd hK hl₀ hl₁
    have hzero : (0 : Blocks r s) ∈ positiveCone := ⟨Matrix.PosSemidef.zero,Matrix.PosSemidef.zero⟩
    have hmin : objective K lambda₀ lambda₁ (minimizer K lambda₀ lambda₁) ≤ objective K lambda₀ lambda₁ 0 := hs.2 hzero
    have hq : blockTrace (minimizer K lambda₀ lambda₁) < R := by
      by_contra! hn
      have hi := hR K (minimizer K lambda₀ lambda₁) hK hmK hs.1 hn
      exact (not_lt_of_ge (hi.trans hmin)) haK
    have his : IsLeast (objective K lambda₀ lambda₁ '' C) (minimumValue K lambda₀ lambda₁) := by
      refine ⟨⟨minimizer K lambda₀ lambda₁,⟨hs.1,hq.le⟩,rfl⟩,?_⟩
      rintro _ ⟨Z,hZ,rfl⟩
      exact hs.2 hZ.1
    exact his.csInf_eq.symm
  have hc : Continuous (fun K : HermitianMat (r ⊕ s) ℂ => sInf (objective K lambda₀ lambda₁ '' C)) :=
    (isCompact_traceSublevel R).continuous_sInf (continuous_jointObjective lambda₀ lambda₁)
  exact hc.continuousAt.continuousWithinAt.congr_of_eventuallyEq_of_mem he hJ

theorem continuousOn_minimumValue_psd {lambda₀ lambda₁ : ℝ} (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) :
    ContinuousOn (fun J : HermitianMat (r ⊕ s) ℂ => minimumValue J lambda₀ lambda₁) {J | J.mat.PosSemidef} :=
  fun _ hJ => continuousWithinAt_minimumValue_psd hJ hl₀ hl₁

theorem continuousWithinAt_value_psd {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosSemidef) (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) :
    ContinuousWithinAt (fun K : HermitianMat (r ⊕ s) ℂ => value K lambda₀ lambda₁)
      {K | K.mat.PosSemidef} J :=
  (continuous_psi.comp pinching.continuous).continuousAt.continuousWithinAt.add
    (continuousWithinAt_minimumValue_psd hJ hl₀ hl₁)

theorem continuousOn_value_psd {lambda₀ lambda₁ : ℝ} (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) :
    ContinuousOn (fun J : HermitianMat (r ⊕ s) ℂ => value J lambda₀ lambda₁) {J | J.mat.PosSemidef} :=
  fun _ hJ => continuousWithinAt_value_psd hJ hl₀ hl₁

theorem regularization_posDef {J : HermitianMat k ℂ} (hJ : J.mat.PosSemidef) {t : ℝ} (ht : 0 < t) :
    (J+t • 1).mat.PosDef := by
  change (J.mat+t • (1 : Matrix k k ℂ)).PosDef
  rw [add_comm]
  exact (Matrix.PosDef.one.smul (α := ℝ) ht).add_posSemidef hJ

/-- The actual PSD minimum value, not an assumed boundary extension, is the regularization limit. -/
theorem tendsto_value_regularization {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosSemidef) (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) :
    Tendsto (fun t : ℝ => value (J+t • 1) lambda₀ lambda₁) (𝓝[>] 0) (𝓝 (value J lambda₀ lambda₁)) := by
  have hc : Continuous (fun t : ℝ => J+t • (1 : HermitianMat (r ⊕ s) ℂ)) := by fun_prop
  have ht : Tendsto (fun t : ℝ => J+t • (1 : HermitianMat (r ⊕ s) ℂ)) (𝓝[>] 0)
      (𝓝[{K | K.mat.PosSemidef}] J) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact (regularization_posDef hJ ht).posSemidef
  exact (continuousWithinAt_value_psd hJ hl₀ hl₁).tendsto.comp ht

/-- Concavity of the true minimized dual value includes every singular PSD input. -/
theorem concaveOn_value_psd {lambda₀ lambda₁ : ℝ} (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) :
    ConcaveOn ℝ {J : HermitianMat (r ⊕ s) ℂ | J.mat.PosSemidef}
      (fun J => value J lambda₀ lambda₁) := by
  constructor
  · intro J hJ K hK a b ha hb hab
    convert! (hJ.smul ha).add (hK.smul hb) using 1
  intro J hJ K hK a b ha hb hab
  have hC : (a • J+b • K).mat.PosSemidef := by
    convert! (hJ.smul ha).add (hK.smul hb) using 1
  have hL : Tendsto (fun t : ℝ => a*value (J+t • 1) lambda₀ lambda₁+
      b*value (K+t • 1) lambda₀ lambda₁) (𝓝[>] 0)
      (𝓝 (a*value J lambda₀ lambda₁+b*value K lambda₀ lambda₁)) :=
    (tendsto_const_nhds.mul (tendsto_value_regularization hJ hl₀ hl₁)).add
      (tendsto_const_nhds.mul (tendsto_value_regularization hK hl₀ hl₁))
  apply le_of_tendsto_of_tendsto hL (tendsto_value_regularization hC hl₀ hl₁)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hi := (BetaDualConcave.concaveOn_value hl₀ hl₁).2
    (regularization_posDef hJ ht) (regularization_posDef hK ht) ha hb hab
  have he : a • (J+t • 1)+b • (K+t • 1) = a • J+b • K+t • 1 := by
    calc
      _ = a • J+b • K+(a+b) • (t • (1 : HermitianMat (r ⊕ s) ℂ)) := by module
      _ = _ := by rw [hab,one_smul]
  simpa only [he,smul_eq_mul] using hi

end QubitAdditivity.BetaDualBoundary
