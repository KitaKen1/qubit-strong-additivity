import QubitAdditivity.BetaDualConvex
import QubitAdditivity.Imported.SpectralEntropy
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

namespace QubitAdditivity.BetaDualExistence
open BetaDual BetaEntropy

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
variable {r s : Type*} [Fintype r] [Fintype s] [DecidableEq r] [DecidableEq s]

/-- Continuity includes singular matrices: the spectral function uses 0 log 0 = 0. -/
theorem continuous_psi : Continuous (psi : HermitianMat k ℂ → ℝ) := by
  have hc := (traceHerm (k := k)).continuous.comp
    (HermitianMat.cfc_continuous Real.continuous_negMulLog)
  convert! hc.neg using 1

theorem continuous_objective (J : HermitianMat (r ⊕ s) ℂ) (lambda₀ lambda₁ : ℝ) :
    Continuous (objective J lambda₀ lambda₁) := by
  unfold objective
  apply Continuous.sub
  · apply Continuous.sub
    · exact (continuous_psi.comp continuous_fst).add (continuous_psi.comp continuous_snd)
    · exact continuous_psi.comp (continuous_const.add diagonalCLM.continuous)
  · exact (continuous_const.mul ((traceHerm (k := r)).continuous.comp continuous_fst)).add
      (continuous_const.mul ((traceHerm (k := s)).continuous.comp continuous_snd))

theorem isClosed_positiveCone : IsClosed (positiveCone (r := r) (s := s)) := by
  have h₀ := (HermitianMat.isClosed_nonneg (n := r) (𝕜 := ℂ)).preimage (continuous_fst (X := HermitianMat r ℂ) (Y := HermitianMat s ℂ))
  have h₁ := (HermitianMat.isClosed_nonneg (n := s) (𝕜 := ℂ)).preimage (continuous_snd (X := HermitianMat r ℂ) (Y := HermitianMat s ℂ))
  convert! h₀.inter h₁ using 1
  ext W
  simp [positiveCone,HermitianMat.zero_le_iff]

theorem convex_psi : ConvexOn ℝ {A : HermitianMat k ℂ | A.mat.PosSemidef} psi := by
  constructor
  · intro A hA B hB a b ha hb hab
    convert! (hA.smul ha).add (hB.smul hb) using 1
  · intro A hA B hB a b ha hb hab
    have hi := (OpenAIEntropy.concaveOn_entropy (ι := k)).2 hA hB ha hb hab
    change psi (a • A+b • B) ≤ a*psi A+b*psi B
    unfold psi
    convert! neg_le_neg hi using 1 <;> ring

theorem norm_le_trace {A : HermitianMat k ℂ} (hA : A.mat.PosSemidef) :
    ‖A‖ ≤ A.mat.trace.re := by
  have hp : 0 ≤ A.trace := HermitianMat.trace_nonneg (HermitianMat.zero_le_iff.mpr hA)
  have hs : ‖A‖^2 ≤ A.trace^2 := by
    rw [HermitianMat.norm_eq_sum_eigenvalues_sq,← A.sum_eigenvalues_eq_trace]
    exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hA.eigenvalues_nonneg i)
  have he : A.trace = A.mat.trace.re := by convert! A.trace_eq_re_trace using 1
  rw [← he]
  nlinarith [norm_nonneg A]

/-- The endpoint derivative bounds the whole entropy increment, even when W is singular. -/
theorem psi_increment_le_gradient {W J : HermitianMat k ℂ} (hW : W.mat.PosSemidef)
    (hJ : J.mat.PosSemidef) (hT : (W+J).mat.PosDef) :
    psi (W+J)-psi W ≤ psiGradient (W+J).mat J := by
  let f : ℝ → ℝ := fun t => psi (W+t • J)
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (W+t • J).mat.PosSemidef := by
    convert! hW.add (hJ.smul ht.1) using 1
  have hc : ConvexOn ℝ (Icc (0 : ℝ) 1) f := by
    refine ⟨convex_Icc _ _,?_⟩
    intro x hx y hy a b ha hb hab
    have he : W+(a*x+b*y) • J = a • (W+x • J)+b • (W+y • J) := by
      have hw : (a+b) • W = W := by rw [hab,one_smul]
      calc
        W+(a*x+b*y) • J = (a+b) • W+(a*x+b*y) • J := by rw [hw]
        _ = _ := by module
    change psi (W+(a*x+b*y) • J) ≤ a*psi (W+x • J)+b*psi (W+y • J)
    rw [he]
    exact convex_psi.2 (hp x hx) (hp y hy) ha hb hab
  have hd : HasDerivAt f (psiGradient (W+J).mat J) 1 := by
    have hl : HasDerivAt (fun t : ℝ => W+t • J) J 1 := by
      simpa using ((hasDerivAt_id (1 : ℝ)).smul_const J).const_add W
    have ht : (W+(1 : ℝ) • J).mat.PosDef := by simpa using hT
    convert! (hasFDerivAt_psi ht).comp_hasDerivAt 1 hl using 1 <;> simp only [one_smul]
  have hi := hc.slope_le_of_hasDerivAt (x := 0) (y := 1) (by simp) (by simp) (by norm_num) hd
  simpa [slope_def_field,f] using hi

/-- Spectral log is bounded by log of the trace. No simple-spectrum hypothesis is used. -/
theorem hermLog_le_log_trace {T : HermitianMat k ℂ} (hT : T.mat.PosDef) :
    hermLog T ≤ Real.log T.mat.trace.re • (1 : HermitianMat k ℂ) := by
  have he : hermLog T = T.cfc Real.log := by
    apply HermitianMat.ext
    rfl
  rw [he,← sub_nonneg,← HermitianMat.cfc_const,← HermitianMat.cfc_sub]
  rw [HermitianMat.cfc_nonneg_iff]
  intro i
  have hl : T.H.eigenvalues i ≤ T.mat.trace.re := by
    have hs := Finset.single_le_sum (fun j _ => hT.posSemidef.eigenvalues_nonneg j)
      (Finset.mem_univ i)
    have ht : (∑ j, T.H.eigenvalues j) = T.mat.trace.re := by
      convert! T.sum_eigenvalues_eq_trace.trans T.trace_eq_re_trace using 1
    simpa only [ht] using hs
  exact sub_nonneg.mpr (Real.log_le_log (hT.eigenvalues_pos i) hl)

theorem psiGradient_le_trace {J T : HermitianMat k ℂ} (hJ : J.mat.PosSemidef)
    (hT : T.mat.PosDef) :
    psiGradient T.mat J ≤ J.mat.trace.re * (Real.log T.mat.trace.re+1) := by
  have ho : hermLog T+1 ≤ (Real.log T.mat.trace.re+1) • (1 : HermitianMat k ℂ) := by
    have hh := add_le_add_right (hermLog_le_log_trace hT) (1 : HermitianMat k ℂ)
    simpa only [add_smul,one_smul,add_comm] using hh
  have hi := HermitianMat.inner_mono (HermitianMat.zero_le_iff.mpr hJ) ho
  have he : J.trace = J.mat.trace.re := by convert! J.trace_eq_re_trace using 1
  rw [inner_smul_right,HermitianMat.inner_one,he] at hi
  rw [psiGradient_apply]
  calc
    _ = inner ℝ J (hermLog T+1) := by
      convert! (HermitianMat.inner_eq_re_trace J (hermLog T+1)).symm using 1
    _ ≤ (Real.log T.mat.trace.re+1)*J.mat.trace.re := hi
    _ = _ := mul_comm _ _

theorem psi_increment_le_trace {W J : HermitianMat k ℂ} (hW : W.mat.PosSemidef)
    (hJ : J.mat.PosSemidef) (hT : (W+J).mat.PosDef) :
    psi (W+J)-psi W ≤ J.mat.trace.re * (Real.log (W+J).mat.trace.re+1) :=
  (psi_increment_le_gradient hW hJ hT).trans (psiGradient_le_trace hJ hT)

theorem diagonal_posSemidef {W : Blocks r s} (hW : W ∈ positiveCone) :
    (diagonal W).mat.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (diagonal W).H
  intro x
  change 0 ≤ star x ⬝ᵥ (Matrix.fromBlocks W.1.mat 0 0 W.2.mat *ᵥ x)
  have h₀ := hW.1.dotProduct_mulVec_nonneg (fun i => x (Sum.inl i))
  have h₁ := hW.2.dotProduct_mulVec_nonneg (fun i => x (Sum.inr i))
  simpa [BetaDual.diagonal,Matrix.fromBlocks,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,
    Finset.mul_sum] using add_nonneg h₀ h₁

def blockTrace (W : Blocks r s) : ℝ := W.1.mat.trace.re+W.2.mat.trace.re

theorem continuous_blockTrace : Continuous (blockTrace (r := r) (s := s)) := by
  exact ((traceHerm (k := r)).continuous.comp continuous_fst).add
    ((traceHerm (k := s)).continuous.comp continuous_snd)

theorem trace_diagonal (W : Blocks r s) : (diagonal W).mat.trace.re = blockTrace W := by
  simp [blockTrace,BetaDual.diagonal,Matrix.trace,Fintype.sum_sum_type,Matrix.fromBlocks]

theorem blockTrace_nonneg {W : Blocks r s} (hW : W ∈ positiveCone) : 0 ≤ blockTrace W := by
  have h₀ := HermitianMat.trace_nonneg (HermitianMat.zero_le_iff.mpr hW.1)
  have h₁ := HermitianMat.trace_nonneg (HermitianMat.zero_le_iff.mpr hW.2)
  have e₀ : W.1.trace = W.1.mat.trace.re := by convert! W.1.trace_eq_re_trace using 1
  have e₁ : W.2.trace = W.2.mat.trace.re := by convert! W.2.trace_eq_re_trace using 1
  simpa only [blockTrace,e₀,e₁] using add_nonneg h₀ h₁

theorem norm_le_blockTrace {W : Blocks r s} (hW : W ∈ positiveCone) : ‖W‖ ≤ blockTrace W := by
  have h₀ := norm_le_trace hW.1
  have h₁ := norm_le_trace hW.2
  rw [Prod.norm_def,max_le_iff]
  unfold blockTrace
  constructor <;> linarith [norm_nonneg W.1,norm_nonneg W.2]

theorem isCompact_traceSublevel (R : ℝ) :
    IsCompact {W : Blocks r s | W ∈ positiveCone ∧ blockTrace W ≤ R} := by
  have hc : IsClosed {W : Blocks r s | W ∈ positiveCone ∧ blockTrace W ≤ R} :=
    isClosed_positiveCone.inter (isClosed_Iic.preimage continuous_blockTrace)
  apply Metric.isCompact_of_isClosed_isBounded hc
  apply (Metric.isBounded_closedBall (x := (0 : Blocks r s)) (r := R)).subset
  intro W hW
  rw [Metric.mem_closedBall,dist_zero_right]
  exact (norm_le_blockTrace hW.1).trans hW.2

/-- A lower bound valid on the original closed PSD block cone. -/
theorem objective_lower_bound {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ c : ℝ}
    (hJ : J.mat.PosDef) (hc₀ : c ≤ -lambda₀) (hc₁ : c ≤ -lambda₁)
    {W : Blocks r s} (hW : W ∈ positiveCone) :
    c*blockTrace W-J.mat.trace.re*(Real.log (blockTrace W+J.mat.trace.re)+1) ≤
      objective J lambda₀ lambda₁ W := by
  have hT : (diagonal W+J).mat.PosDef := by
    change ((diagonal W).mat+J.mat).PosDef
    rw [add_comm]
    exact hJ.add_posSemidef (diagonal_posSemidef hW)
  have hi := psi_increment_le_trace (diagonal_posSemidef hW) hJ.posSemidef hT
  have ht : (diagonal W+J).mat.trace.re = blockTrace W+J.mat.trace.re := by
    change ((diagonal W).mat+J.mat).trace.re = _
    rw [Matrix.trace_add,Complex.add_re,trace_diagonal]
  rw [ht,add_comm (diagonal W) J] at hi
  have hp₀ := norm_le_trace hW.1
  have hp₁ := norm_le_trace hW.2
  have hl₀ := mul_le_mul_of_nonneg_right hc₀ (le_trans (norm_nonneg _) hp₀)
  have hl₁ := mul_le_mul_of_nonneg_right hc₁ (le_trans (norm_nonneg _) hp₁)
  rw [objective_eq]
  unfold blockTrace at *
  nlinarith

/-- Positive linear growth dominates the logarithmic entropy increment. -/
theorem tendsto_scalar_lower_bound (c m : ℝ) (hc : 0 < c) :
    Tendsto (fun q : ℝ => c*q-m*(Real.log (q+m)+1)) atTop atTop := by
  have hs : Tendsto (fun q : ℝ => q+m) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_id
  have hl : Tendsto (fun q : ℝ => Real.log (q+m)/q) atTop (𝓝 0) := by
    convert! (Real.tendsto_pow_log_div_mul_add_atTop 1 (-m) 1 one_ne_zero).comp hs using 1
    ext q
    simp
  have hi : Tendsto (fun q : ℝ => (1 : ℝ)/q) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop tendsto_id
  have hh : Tendsto (fun q : ℝ => c-m*(Real.log (q+m)/q+1/q)) atTop (𝓝 c) := by
    convert! tendsto_const_nhds.sub (tendsto_const_nhds.mul (hl.add hi)) using 1 <;> simp
  have hp := tendsto_id.atTop_mul_pos hc hh
  apply hp.congr'
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with q hq
  dsimp only [id]
  field_simp

/-- Coercivity on the closed PSD cone, with both dual coefficients strictly negative. -/
theorem objective_eventually_ge {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosDef) (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) (a : ℝ) :
    ∀ᶠ W in cocompact (Blocks r s) ⊓ 𝓟 positiveCone, a ≤ objective J lambda₀ lambda₁ W := by
  let c := min (-lambda₀) (-lambda₁)
  have hc : 0 < c := lt_min (neg_pos.mpr hl₀) (neg_pos.mpr hl₁)
  rcases eventually_atTop.1 ((tendsto_scalar_lower_bound c J.mat.trace.re hc).eventually_ge_atTop a)
    with ⟨R,hR⟩
  rw [eventually_inf_principal]
  filter_upwards [(isCompact_traceSublevel (r := r) (s := s) R).compl_mem_cocompact]
    with W houtside hW
  have hlarge : R < blockTrace W := by
    by_contra! hsmall
    exact houtside ⟨hW,hsmall⟩
  exact (hR (blockTrace W) hlarge.le).trans
    (objective_lower_bound hJ (min_le_left _ _) (min_le_right _ _) hW)

theorem tendsto_objective_cocompact {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosDef) (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) :
    Tendsto (objective J lambda₀ lambda₁) (cocompact (Blocks r s) ⊓ 𝓟 positiveCone) atTop := by
  exact tendsto_atTop.2 (objective_eventually_ge hJ hl₀ hl₁)

/-- Existence on the closed cone is proved, with no positive-definiteness assumption on W. -/
theorem exists_minOn_positiveCone {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosDef) (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) :
    ∃ W ∈ positiveCone, IsMinOn (objective J lambda₀ lambda₁) positiveCone W := by
  apply (continuous_objective J lambda₀ lambda₁).continuousOn.exists_isMinOn' isClosed_positiveCone
    (x₀ := (0 : Blocks r s))
  · constructor <;> exact Matrix.PosSemidef.zero
  · exact objective_eventually_ge hJ hl₀ hl₁ _

end QubitAdditivity.BetaDualExistence
