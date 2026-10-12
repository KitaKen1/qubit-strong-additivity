import QubitAdditivity.Imported.MatrixEntropy
import QubitAdditivity.BetaKM
import QubitAdditivity.BetaResolvent
import QuantumInfo.ForMathlib.HermitianMat.CFC
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

namespace QubitAdditivity.BetaLog
variable {n : Type*} [Fintype n] [DecidableEq n]

@[reducible] local instance mNorm : NormedAddCommGroup (Matrix n n ℂ) := Matrix.frobeniusNormedRing.toNonUnitalNormedRing.toNormedAddCommGroup
@[reducible] local instance mSpace : NormedSpace ℝ (Matrix n n ℂ) := NormedAlgebra.toNormedSpace (Matrix n n ℂ)
@[reducible] local instance mTop : TopologicalSpace (Matrix n n ℂ) := mNorm.toUniformSpace.toTopologicalSpace
@[reducible] local instance hTop : TopologicalSpace (HermitianMat n ℂ) :=
  HermitianMat.instNormedAddCommGroupComplex.toUniformSpace.toTopologicalSpace
@[reducible] local instance mAdd : AddCommGroup (Matrix n n ℂ) := mNorm.toAddCommGroup
@[reducible] local instance hAdd : AddCommGroup (HermitianMat n ℂ) := HermitianMat.instNormedAddCommGroupComplex.toAddCommGroup
@[reducible] local instance mModule : Module ℝ (Matrix n n ℂ) := mSpace.toModule
@[reducible] local instance hModule : Module ℝ (HermitianMat n ℂ) := HermitianMat.instNormedSpace.toModule

local instance matrixCFC : ContinuousFunctionalCalculus ℝ (Matrix n n ℂ) Matrix.IsHermitian := by
  letI : TopologicalSpace (Matrix n n ℂ) := inferInstanceAs (TopologicalSpace (n → n → ℂ))
  letI : AddCommGroup (Matrix n n ℂ) := Matrix.addCommGroup
  letI : Module ℝ (Matrix n n ℂ) := Matrix.module
  convert! (Matrix.IsHermitian.instContinuousFunctionalCalculus (𝕜 := ℂ) (n := n)) using 1

def inclusion : HermitianMat n ℂ →L[ℝ] Matrix n n ℂ := by
  convert! (HermitianMat.matₗ (R := ℝ) (n := n) (α := ℂ)) using 1

@[simp] theorem inclusion_apply (H : HermitianMat n ℂ) : inclusion H = H.mat := rfl

/-- The affine positive path from the identity to A. -/
def segment (A : Matrix n n ℂ) (t : ℝ) : Matrix n n ℂ := 1 + t • (A - 1)
def inverseSegment (A : Matrix n n ℂ) (t : ℝ) : Matrix n n ℂ := (segment A t)⁻¹
def kernel (A : Matrix n n ℂ) (t : ℝ) : Matrix n n ℂ := (A - 1) * inverseSegment A t

def sandwich (R : Matrix n n ℂ) : Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
  ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) R R

def kernelDeriv (A : Matrix n n ℂ) (t : ℝ) :
    HermitianMat n ℂ →L[ℝ] Matrix n n ℂ :=
  (sandwich (inverseSegment A t)).comp inclusion

def logDeriv (A : Matrix n n ℂ) : HermitianMat n ℂ →L[ℝ] Matrix n n ℂ :=
  ∫ t in (0 : ℝ)..1, kernelDeriv A t

@[simp] theorem sandwich_apply (R H : Matrix n n ℂ) : sandwich R H = R * H * R := rfl
@[simp] theorem kernelDeriv_apply (A : Matrix n n ℂ) (t : ℝ) (H : HermitianMat n ℂ) :
    kernelDeriv A t H = inverseSegment A t * H.mat * inverseSegment A t := rfl

theorem segment_zero (A : Matrix n n ℂ) : segment A 0 = 1 := by simp [segment]
theorem segment_one (A : Matrix n n ℂ) : segment A 1 = A := by simp [segment]

theorem segment_posDef {A : Matrix n n ℂ} (hA : A.PosDef)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : (segment A t).PosDef := by
  by_cases h : t = 0
  · simpa [h, segment] using (Matrix.PosDef.one (n := n) (R := ℂ))
  have he : segment A t = t • A + (1-t) • (1 : Matrix n n ℂ) := by
    unfold segment
    module
  rw [he]
  exact (hA.smul (lt_of_le_of_ne ht.1 (Ne.symm h))).add_posSemidef
    (Matrix.PosSemidef.one.smul (sub_nonneg.mpr ht.2))

theorem continuousOn_inverseSegment {A : Matrix n n ℂ} (hA : A.PosDef) :
    ContinuousOn (inverseSegment A) (Icc (0 : ℝ) 1) := by
  intro t ht
  have hc : Continuous (segment A) := by unfold segment; fun_prop
  unfold inverseSegment
  simp_rw [Matrix.nonsing_inv_eq_ringInverse]
  have hi : ContinuousAt Ring.inverse (segment A t) := by
    convert! NormedRing.inverse_continuousAt (segment_posDef hA ht).isUnit.unit using 1
  exact (hi.comp hc.continuousAt).continuousWithinAt

theorem continuousOn_kernel {A : Matrix n n ℂ} (hA : A.PosDef) :
    ContinuousOn (kernel A) (Icc (0 : ℝ) 1) :=
  continuousOn_const.mul (continuousOn_inverseSegment hA)

theorem continuousOn_kernelDeriv {A : Matrix n n ℂ} (hA : A.PosDef) :
    ContinuousOn (kernelDeriv A) (Icc (0 : ℝ) 1) := by
  unfold kernelDeriv sandwich
  have hc := continuousOn_inverseSegment hA
  fun_prop

/-- The scalar compact-interval logarithm formula. -/
theorem scalar_log_integral {a : ℝ} (ha : 0 < a) :
    (∫ t in (0 : ℝ)..1, (a-1) / (1+t*(a-1))) = Real.log a := by
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 < 1+t*(a-1) := by
    by_cases h : t = 0
    · simp [h]
    have hta : 0 < t*a := mul_pos (lt_of_le_of_ne ht.1 (Ne.symm h)) ha
    nlinarith [ht.2]
  have hc : ContinuousOn (fun t : ℝ => (a-1)/(1+t*(a-1))) (Icc (0 : ℝ) 1) :=
    continuousOn_const.div (by fun_prop) (fun t ht => (hp t ht).ne')
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ => Real.log (1+t*(a-1))) ((a-1)/(1+t*(a-1))) t := by
    convert! (((hasDerivAt_id t).mul_const (a-1)).const_add 1).log (hp t ht).ne' using 1 <;> simp
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1)
    (fun t ht => hd t (by simpa using ht))
    ((show ContinuousOn _ (uIcc (0 : ℝ) 1) from by simpa using hc).intervalIntegrable)
  simpa using hh

/-- The compact-interval normalization needed for the entropy gradient. -/
theorem scalar_inverse_square_integral {a : ℝ} (ha : 0 < a) :
    (∫ t in (0 : ℝ)..1, a / (1+t*(a-1))^2) = 1 := by
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : 0 < 1+t*(a-1) := by
    by_cases h : t = 0
    · simp [h]
    have hta : 0 < t*a := mul_pos (lt_of_le_of_ne ht.1 (Ne.symm h)) ha
    nlinarith [ht.2]
  have hc : ContinuousOn (fun t : ℝ => a/(1+t*(a-1))^2) (Icc (0 : ℝ) 1) :=
    continuousOn_const.div (by fun_prop) (fun t ht => pow_ne_zero _ (hp t ht).ne')
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ => t*a/(1+t*(a-1))) (a/(1+t*(a-1))^2) t := by
    convert! ((hasDerivAt_id t).mul_const a).div
      (((hasDerivAt_id t).mul_const (a-1)).const_add 1) (hp t ht).ne' using 1 <;> simp <;> ring
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1)
    (fun t ht => hd t (by simpa using ht))
    ((show ContinuousOn _ (uIcc (0 : ℝ) 1) from by simpa using hc).intervalIntegrable)
  simpa [ha.ne'] using hh


/-- Positive definiteness is open in the real Hermitian space. Compactness of
unit vectors avoids perturbation bounds for eigenvalues. -/
theorem eventually_posDef {A : HermitianMat n ℂ} (hA : A.mat.PosDef) :
    ∀ᶠ B : HermitianMat n ℂ in 𝓝 A, B.mat.PosDef := by
  let S : Set (n → ℂ) := Metric.sphere 0 1
  let U : Set (HermitianMat n ℂ × (n → ℂ)) :=
    {z | 0 < BetaComparison.quadratic z.1.mat z.2}
  have hc : Continuous (fun z : HermitianMat n ℂ × (n → ℂ) =>
      BetaComparison.quadratic z.1.mat z.2) := by
    have hm : Continuous (fun B : HermitianMat n ℂ => B.mat) := by
      convert! (HermitianMat.matₗ (R := ℝ) (n := n) (α := ℂ)).continuous using 1
    have he (i j : n) : Continuous (fun z : HermitianMat n ℂ × (n → ℂ) => z.1.mat i j) :=
      (continuous_apply j).comp ((continuous_apply i).comp (hm.comp continuous_fst))
    simp only [BetaComparison.quadratic, BetaComparison.pairing, dotProduct, Matrix.mulVec]
    exact Complex.continuous_re.comp (continuous_finset_sum _ fun i _ =>
      (continuous_apply i |>.comp continuous_snd).star.mul
        (continuous_finset_sum _ fun j _ => (he i j).mul
          (continuous_apply j |>.comp continuous_snd)))
  have hU : IsOpen U := isOpen_lt continuous_const hc
  have he : U ∈ 𝓝 A ×ˢ 𝓝ˢ S := (isCompact_sphere (0 : n → ℂ) 1).mem_prod_nhdsSet_of_forall
    (fun v hv => by
      rw [← nhds_prod_eq]
      apply hU.mem_nhds
      apply BetaComparison.quadratic_pos hA
      have hn : ‖v‖ = 1 := by simpa [S, Metric.mem_sphere, dist_zero_right] using hv
      intro hz
      change v = 0 at hz
      rw [hz, norm_zero] at hn
      exact zero_ne_one hn)
  rcases Filter.mem_prod_iff.mp he with ⟨P,hP,Q,hQ,hPQ⟩
  filter_upwards [hP] with B hB
  apply Matrix.PosDef.of_dotProduct_mulVec_pos B.H
  intro v hv
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hu : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  have hh := hPQ (a := (B, (‖v‖⁻¹ : ℝ) • v)) ⟨hB,subset_of_mem_nhdsSet hQ (by simpa [S,Metric.mem_sphere,dist_zero_right] using hu)⟩
  change 0 < BetaComparison.quadratic B.mat ((‖v‖⁻¹ : ℝ) • v) at hh
  rw [BetaComparison.quadratic_smul_vector] at hh
  apply Complex.pos_iff.mpr
  exact ⟨(mul_pos_iff_of_pos_left (sq_pos_of_pos (inv_pos.mpr hn))).mp hh,
    (B.H.im_star_dotProduct_mulVec_self v).symm⟩

theorem scalar_segment_pos {a t : ℝ} (ha : 0 < a) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < 1+t*(a-1) := by
  by_cases h : t = 0
  · simp [h]
  have hta : 0 < t*a := mul_pos (lt_of_le_of_ne ht.1 (Ne.symm h)) ha
  nlinarith [ht.2]

theorem segment_eq_cfc {A : Matrix n n ℂ} (hA : A.IsHermitian) (t : ℝ) :
    segment A t = cfc (fun a : ℝ => 1+t*(a-1)) A := by
  have h1 : cfc (fun a : ℝ => 1) A = 1 := by convert! cfc_const_one ℝ A hA using 1
  have hid : cfc (fun a : ℝ => a) A = A := by convert! cfc_id' ℝ A hA using 1
  have hc : cfc (fun a : ℝ => t) A = t • (1 : Matrix n n ℂ) := by
    convert! cfc_const t A hA using 1
    exact (Algebra.algebraMap_eq_smul_one t).symm
  rw [cfc_add, cfc_mul, cfc_sub, h1, hid, hc]
  · simp [segment, Matrix.smul_mul]
  all_goals exact BetaPowers.continuousOn_spectrum _ _

theorem kernel_eq_cfc {A : Matrix n n ℂ} (hA : A.PosDef) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    kernel A t = cfc (fun a : ℝ => (a-1)/(1+t*(a-1))) A := by
  have hz : ∀ a ∈ spectrum ℝ A, 1+t*(a-1) ≠ 0 := by
    rw [hA.1.spectrum_real_eq_range_eigenvalues]
    rintro _ ⟨i,rfl⟩
    exact (scalar_segment_pos (hA.eigenvalues_pos i) ht).ne'
  have hd : cfc (fun a : ℝ => (a-1)/(1+t*(a-1))) A =
      cfc (fun a : ℝ => a-1) A * Ring.inverse (cfc (fun a : ℝ => 1+t*(a-1)) A) := by
    convert! cfc_map_div (fun a : ℝ => a-1) (fun a : ℝ => 1+t*(a-1)) A hz
      (BetaPowers.continuousOn_spectrum _ _) (BetaPowers.continuousOn_spectrum _ _) hA.1 using 1
  have hs : cfc (fun a : ℝ => a-1) A = A-1 := by
    have hid : cfc (fun a : ℝ => a) A = A := by convert! cfc_id' ℝ A hA.1 using 1
    have h1 : cfc (fun a : ℝ => 1) A = 1 := by convert! cfc_const_one ℝ A hA.1 using 1
    rw [cfc_sub _ _ A (BetaPowers.continuousOn_spectrum _ _) (by fun_prop),hid,h1]
  rw [hd,hs,← segment_eq_cfc hA.1 t]
  exact congrArg ((A-1) * ·) (Matrix.nonsing_inv_eq_ringInverse _)

/-- Integration on a fixed finite spectrum commutes with real CFC. -/
theorem integral_cfc {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (f : ℝ → ℝ → ℝ)
    (hf : ∀ i, IntervalIntegrable (fun t => f t (hA.eigenvalues i)) MeasureTheory.volume 0 1) :
    (∫ t in (0 : ℝ)..1, cfc (f t) A) = cfc (fun a => ∫ t in (0 : ℝ)..1, f t a) A := by
  let B : HermitianMat n ℂ := ⟨A,hA⟩
  have hh := B.integral_cfc_eq_cfc_integral 0 1 f hf
  have hi := B.integrable_cfc 0 1 f hf
  have hm := congrArg HermitianMat.mat hh
  rw [HermitianMat.integral_toMat _ 0 1 hi] at hm
  simp only [HermitianMat.mat_cfc] at hm
  convert! hm using 1

/-- A compact-interval formula for the actual CFC logarithm. -/
theorem logarithm_eq_integral {A : Matrix n n ℂ} (hA : A.PosDef) :
    BetaPowers.logarithm A = ∫ t in (0 : ℝ)..1, kernel A t := by
  have hf (i : n) : IntervalIntegrable
      (fun t : ℝ => (hA.1.eigenvalues i-1)/(1+t*(hA.1.eigenvalues i-1)))
      MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div (by fun_prop)
    intro t ht
    exact (scalar_segment_pos (hA.eigenvalues_pos i) (by simpa using ht)).ne'
  rw [intervalIntegral.integral_congr (fun t ht => kernel_eq_cfc hA (by simpa using ht)),
    integral_cfc hA.1 _ hf]
  apply cfc_congr
  rw [hA.1.spectrum_real_eq_range_eigenvalues]
  rintro _ ⟨i,rfl⟩
  exact (scalar_log_integral (hA.eigenvalues_pos i)).symm

/-- The kernel derivative preserves the order of noncommuting factors. -/
theorem hasFDerivAt_kernel {A : HermitianMat n ℂ} (hA : A.mat.PosDef)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasFDerivAt (fun B : HermitianMat n ℂ => kernel B.mat t) (kernelDeriv A.mat t) A := by
  let L : HermitianMat n ℂ →L[ℝ] Matrix n n ℂ := inclusion
  have hd : HasFDerivAt (fun B : HermitianMat n ℂ => segment B.mat t) (t • L) A :=
    ((L.hasFDerivAt.sub_const 1).const_smul t).const_add 1
  have hp := (segment_posDef hA ht).isUnit
  have hi := (hasFDerivAt_ringInverse hp.unit).comp A hd
  have hm := (L.hasFDerivAt.sub_const 1).mul' hi
  convert! hm using 1
  · ext B
    simp [kernel,inverseSegment,Matrix.nonsing_inv_eq_ringInverse,L]
  · apply ContinuousLinearMap.ext
    intro H
    let R := inverseSegment A.mat t
    have hr : R + t • ((A.mat-1)*R) = 1 := by
      have hh := Matrix.mul_nonsing_inv (segment A.mat t)
        ((Matrix.isUnit_iff_isUnit_det _).mp hp)
      simpa only [R,inverseSegment,segment,Matrix.add_mul,Matrix.one_mul,Matrix.smul_mul] using hh
    have hu : (↑hp.unit⁻¹ : Matrix n n ℂ) = R := by
      rw [← Ring.inverse_unit hp.unit,hp.unit_spec]
      exact (Matrix.nonsing_inv_eq_ringInverse _).symm
    simp only [hu, kernelDeriv_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, ContinuousLinearMap.mulLeftRight_apply,
      hp.unit_spec, ← Matrix.nonsing_inv_eq_ringInverse, L,
      inclusion_apply, Function.comp_apply]
    simp only [smul_eq_mul]
    change R * H.mat * R = (A.mat-1) * (-(R * (t • H.mat) * R)) + H.mat * R
    have hh := congrArg (fun X : Matrix n n ℂ => X * H.mat * R) hr
    simp only [Matrix.add_mul,Matrix.one_mul,Matrix.smul_mul] at hh
    simp only [Matrix.mul_smul,Matrix.smul_mul,Matrix.neg_mul,Matrix.mul_neg,
      Matrix.mul_assoc] at hh ⊢
    simpa only [sub_eq_add_neg, add_comm] using (eq_sub_iff_add_eq.mpr hh)

/-- Joint continuity of the inverse segment at a positive base point. -/
theorem continuousAt_inverseSegment {A : HermitianMat n ℂ} (hA : A.mat.PosDef)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ContinuousAt (fun z : HermitianMat n ℂ × ℝ => inverseSegment z.1.mat z.2) (A,t) := by
  have hc : Continuous (fun z : HermitianMat n ℂ × ℝ => segment z.1.mat z.2) := by
    change Continuous (fun z : HermitianMat n ℂ × ℝ => 1+z.2 • (inclusion z.1-1))
    fun_prop
  have hi : ContinuousAt Ring.inverse (segment A.mat t) := by
    convert! NormedRing.inverse_continuousAt (segment_posDef hA ht).isUnit.unit using 1
  simp only [inverseSegment,Matrix.nonsing_inv_eq_ringInverse]
  convert! hi.comp (x := (A,t))
    (f := fun z : HermitianMat n ℂ × ℝ => segment z.1.mat z.2)
    (hc.continuousAt (x := (A,t))) using 1

/-- A compact positive neighborhood supplies the uniform bound required for
Fréchet differentiation under the interval integral. -/
theorem hasFDerivAt_logarithm {A : HermitianMat n ℂ} (hA : A.mat.PosDef) :
    HasFDerivAt (fun B : HermitianMat n ℂ => BetaPowers.logarithm B.mat) (logDeriv A.mat) A := by
  obtain ⟨r,hr,hPD⟩ := Metric.eventually_nhds_iff_ball.mp (eventually_posDef hA)
  let K : Set (HermitianMat n ℂ) := Metric.closedBall A (r/2)
  have hKPD (B : HermitianMat n ℂ) (hB : B ∈ K) : B.mat.PosDef := by
    apply hPD B
    exact (Metric.mem_closedBall.mp hB).trans_lt (by linarith)
  have hc : ContinuousOn (fun z : HermitianMat n ℂ × ℝ => inverseSegment z.1.mat z.2)
      (K ×ˢ Icc (0 : ℝ) 1) := by
    intro z hz
    exact (continuousAt_inverseSegment (hKPD z.1 hz.1) hz.2).continuousWithinAt
  obtain ⟨M,hM⟩ := ((isCompact_closedBall A (r/2)).prod isCompact_Icc).bddAbove_image hc.norm
  have hb (B : HermitianMat n ℂ) (hB : B ∈ K) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖kernelDeriv B.mat t‖ ≤ (max M 0)^2 * ‖(inclusion (n := n))‖ := by
    have hRM : ‖inverseSegment B.mat t‖ ≤ M := by
      convert! hM (mem_image_of_mem
        (fun z : HermitianMat n ℂ × ℝ => ‖inverseSegment z.1.mat z.2‖)
        (show (B,t) ∈ K ×ˢ Icc (0 : ℝ) 1 from ⟨hB,ht⟩)) using 1
    have hR : ‖inverseSegment B.mat t‖ ≤ max M 0 := hRM.trans (le_max_left _ _)
    calc
      _ ≤ ‖sandwich (inverseSegment B.mat t)‖ * ‖(inclusion (n := n))‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (‖inverseSegment B.mat t‖ * ‖inverseSegment B.mat t‖) * ‖(inclusion (n := n))‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le ℝ _ _ _
      _ ≤ (max M 0)^2 * ‖(inclusion (n := n))‖ := by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_right (mul_self_le_mul_self (norm_nonneg _) hR) (norm_nonneg _)
  have hKi : K ∈ 𝓝 A := Metric.closedBall_mem_nhds A (by linarith)
  have hk (B : HermitianMat n ℂ) (hB : B.mat.PosDef) :
      IntervalIntegrable (kernel B.mat) MeasureTheory.volume 0 1 :=
    (show ContinuousOn _ (uIcc (0 : ℝ) 1) from by simpa using continuousOn_kernel hB).intervalIntegrable
  have hd := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun B : HermitianMat n ℂ => kernel B.mat)
    (F' := fun B : HermitianMat n ℂ => kernelDeriv B.mat)
    (bound := fun _ : ℝ => (max M 0)^2 * ‖(inclusion (n := n))‖) (a := (0 : ℝ)) (b := 1) (μ := MeasureTheory.volume)
    hKi
    (by filter_upwards [eventually_posDef hA] with B hB; exact (hk B hB).aestronglyMeasurable_restrict_uIoc)
    (hk A hA)
    ((show ContinuousOn _ (uIcc (0 : ℝ) 1) from by simpa using continuousOn_kernelDeriv hA).intervalIntegrable.aestronglyMeasurable_restrict_uIoc)
    (Filter.Eventually.of_forall (fun t ht B hB =>
      hb B hB t (Ioc_subset_Icc_self (show t ∈ Ioc (0 : ℝ) 1 from by simpa using ht))))
    (intervalIntegrable_const)
    (Filter.Eventually.of_forall (fun t ht B hB =>
      hasFDerivAt_kernel (hKPD B hB) (Ioc_subset_Icc_self (show t ∈ Ioc (0 : ℝ) 1 from by simpa using ht))))
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_posDef hA] with B hB
  exact logarithm_eq_integral hB

/-- Evaluation of the actual noncommutative logarithm differential. -/
theorem logDeriv_apply {A : Matrix n n ℂ} (hA : A.PosDef) (H : HermitianMat n ℂ) :
    logDeriv A H = ∫ t in (0 : ℝ)..1, inverseSegment A t * H.mat * inverseSegment A t := by
  unfold logDeriv
  have hi : IntervalIntegrable (kernelDeriv A) MeasureTheory.volume 0 1 :=
    (show ContinuousOn _ (uIcc (0 : ℝ) 1) from by simpa using continuousOn_kernelDeriv hA).intervalIntegrable
  exact ContinuousLinearMap.intervalIntegral_apply hi H

/-- The real Hermitian tangent space is preserved by the actual log derivative. -/
theorem logDeriv_isHermitian {A : HermitianMat n ℂ} (hA : A.mat.PosDef) (H : HermitianMat n ℂ) :
    (logDeriv A.mat H).IsHermitian := by
  have hl := hasFDerivAt_logarithm hA
  have hs := hl.star
  have he : (fun B : HermitianMat n ℂ => BetaPowers.logarithm B.mat) =ᶠ[𝓝 A]
      (fun B : HermitianMat n ℂ => star (BetaPowers.logarithm B.mat)) := by
    apply Filter.Eventually.of_forall
    intro B
    simpa only [Matrix.star_eq_conjTranspose] using (BetaPowers.logarithm_isHermitian B.mat).symm
  have hd := (hs.congr_of_eventuallyEq he).unique hl
  have hh := congrArg (fun L : HermitianMat n ℂ →L[ℝ] Matrix n n ℂ => L H) hd
  change star (logDeriv A.mat H) = logDeriv A.mat H at hh
  rw [Matrix.IsHermitian]
  convert! hh using 1

/-- CFC realization of the compact-interval entropy normalization kernel. -/
theorem normalization_eq_cfc {A : Matrix n n ℂ} (hA : A.PosDef) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    A * inverseSegment A t * inverseSegment A t =
      cfc (fun a : ℝ => a/(1+t*(a-1))^2) A := by
  have hz : ∀ a ∈ spectrum ℝ A, 1+t*(a-1) ≠ 0 := by
    rw [hA.1.spectrum_real_eq_range_eigenvalues]
    rintro _ ⟨i,rfl⟩
    exact (scalar_segment_pos (hA.eigenvalues_pos i) ht).ne'
  have hi : cfc (fun a : ℝ => (1+t*(a-1))⁻¹) A = inverseSegment A t := by
    have h := cfc_inv (f := fun a : ℝ => 1+t*(a-1)) (a := A) hz
      (BetaPowers.continuousOn_spectrum _ _) hA.1
    convert! h using 1
    rw [← segment_eq_cfc hA.1 t]
    exact Matrix.nonsing_inv_eq_ringInverse _
  have hid : cfc (fun a : ℝ => a) A = A := by convert! cfc_id' ℝ A hA.1 using 1
  have he : (fun a : ℝ => a/(1+t*(a-1))^2) =
      (fun a : ℝ => (a*(1+t*(a-1))⁻¹)*(1+t*(a-1))⁻¹) := by
    ext a
    simp [div_eq_mul_inv,pow_two,← mul_assoc]
  rw [he,cfc_mul,cfc_mul,hid,hi]
  all_goals exact BetaPowers.continuousOn_spectrum _ _

/-- The normalized sandwich integral equals the identity, with no commutation
assumption on perturbations. -/
theorem normalization_integral {A : Matrix n n ℂ} (hA : A.PosDef) :
    (∫ t in (0 : ℝ)..1, A * inverseSegment A t * inverseSegment A t) = 1 := by
  have hf (i : n) : IntervalIntegrable
      (fun t : ℝ => hA.1.eigenvalues i/(1+t*(hA.1.eigenvalues i-1))^2)
      MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_const.div (by fun_prop)
    intro t ht
    exact pow_ne_zero _ (scalar_segment_pos (hA.eigenvalues_pos i) (by simpa using ht)).ne'
  rw [intervalIntegral.integral_congr (fun t ht => normalization_eq_cfc hA (by simpa using ht)),
    integral_cfc hA.1 _ hf]
  have h : cfc (fun a => ∫ t in (0 : ℝ)..1, a/(1+t*(a-1))^2) A = cfc (fun _ : ℝ => 1) A := by
    apply cfc_congr
    rw [hA.1.spectrum_real_eq_range_eigenvalues]
    rintro _ ⟨i,rfl⟩
    exact scalar_inverse_square_integral (hA.eigenvalues_pos i)
  rw [h]
  convert! cfc_const_one ℝ A hA.1 using 1

/-- Real trace as a continuous real linear map. -/
def traceRe : Matrix n n ℂ →L[ℝ] ℝ where
  toFun X := X.trace.re
  map_add' X Y := by simp [Matrix.trace_add]
  map_smul' r X := by simp [Matrix.trace_smul]
  cont := by
    simp only [Matrix.trace,Matrix.diag]
    fun_prop

@[simp] theorem traceRe_apply (X : Matrix n n ℂ) : traceRe X = X.trace.re := rfl

/-- Trace normalization of the actual logarithm differential. -/
theorem trace_mul_logDeriv {A : Matrix n n ℂ} (hA : A.PosDef) (H : HermitianMat n ℂ) :
    (A * logDeriv A H).trace.re = H.mat.trace.re := by
  let L : Matrix n n ℂ →L[ℝ] ℝ := (traceRe (n := n)).comp
    (ContinuousLinearMap.mul ℝ (Matrix n n ℂ) A)
  let M : Matrix n n ℂ →L[ℝ] ℝ := (traceRe (n := n)).comp
    (ContinuousLinearMap.mul ℝ (Matrix n n ℂ) H.mat)
  have hi : IntervalIntegrable (fun t => inverseSegment A t * H.mat * inverseSegment A t)
      MeasureTheory.volume 0 1 :=
    (show ContinuousOn _ (uIcc (0 : ℝ) 1) from by
      have hc := continuousOn_inverseSegment hA
      convert! (hc.mul continuousOn_const).mul hc using 1 <;> simp).intervalIntegrable
  have hn : IntervalIntegrable (fun t => A*inverseSegment A t*inverseSegment A t)
      MeasureTheory.volume 0 1 :=
    (show ContinuousOn _ (uIcc (0 : ℝ) 1) from by
      have hc := continuousOn_inverseSegment hA
      convert! (continuousOn_const.mul hc).mul hc using 1 <;> simp).intervalIntegrable
  have hM : M 1 = H.mat.trace.re := by simp [M,traceRe]
  rw [← hM]
  change L (logDeriv A H) = M 1
  rw [logDeriv_apply hA,← L.intervalIntegral_comp_comm hi,← normalization_integral hA,
    ← M.intervalIntegral_comp_comm hn]
  apply intervalIntegral.integral_congr
  intro t ht
  let R := inverseSegment A t
  have hcomm : Commute R A := by
    have hs : Commute (segment A t) A := by
      unfold segment
      exact (Commute.one_left A).add_left (((Commute.refl A).sub_left (Commute.one_left A)).smul_left t)
    have hd := ((Matrix.isUnit_iff_isUnit_det _).mp (segment_posDef hA (by simpa using ht)).isUnit)
    have hleft : R * segment A t = 1 := Matrix.nonsing_inv_mul _ hd
    have hright : segment A t * R = 1 := Matrix.mul_nonsing_inv _ hd
    rw [commute_iff_eq]
    calc
      R*A = R*A*(segment A t*R) := by rw [hright,Matrix.mul_one]
      _ = R*(A*segment A t)*R := by simp only [Matrix.mul_assoc]
      _ = R*(segment A t*A)*R := by rw [hs.eq]
      _ = A*R := by rw [← Matrix.mul_assoc,hleft,Matrix.one_mul]
  change (A * (R * H.mat * R)).trace.re = (H.mat * (A * R * R)).trace.re
  congr 1
  calc
    _ = (R*(A*(R*H.mat))).trace := by
      simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle' A (R*H.mat) R
    _ = (A*R*R*H.mat).trace := by
      rw [← Matrix.mul_assoc R A, hcomm.eq]
      simp only [Matrix.mul_assoc]
    _ = (H.mat*(A*R*R)).trace := Matrix.trace_mul_comm _ _

/-- The entropy gradient as a real linear functional. -/
def entropyGradient (A : Matrix n n ℂ) : HermitianMat n ℂ →L[ℝ] ℝ :=
  - (traceRe (n := n)).comp
    ((ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) 1 (BetaPowers.logarithm A+1)).comp inclusion)

@[simp] theorem entropyGradient_apply (A : Matrix n n ℂ) (H : HermitianMat n ℂ) :
    entropyGradient A H = -(H.mat * (BetaPowers.logarithm A+1)).trace.re := by
  simp only [entropyGradient,ContinuousLinearMap.neg_apply,ContinuousLinearMap.comp_apply,
    inclusion_apply,ContinuousLinearMap.mulLeftRight_apply,Matrix.one_mul,traceRe_apply]

/-- Compatibility with the spectral entropy already imported from OpenAI. -/
theorem entropy_eq_trace {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    OpenAIEntropy.entropy A = -(A * BetaPowers.logarithm A).trace.re := by
  have hid : cfc (fun a : ℝ => a) A = A := by convert! cfc_id' ℝ A hA using 1
  have he : cfc Real.negMulLog A = -(A * BetaPowers.logarithm A) := by
    rw [Real.negMulLog_eq_neg,cfc_neg,cfc_mul,hid]
    all_goals first | rfl | exact BetaPowers.continuousOn_spectrum _ _
  unfold OpenAIEntropy.entropy
  convert! congrArg (fun X : Matrix n n ℂ => X.trace.re) he using 1
  simp only [Matrix.trace_neg,Complex.neg_re]

/-- The Fréchet derivative of the actual spectral entropy on the real
Hermitian positive cone. No commutation is imposed on a direction. -/
theorem hasFDerivAt_entropy {A : HermitianMat n ℂ} (hA : A.mat.PosDef) :
    HasFDerivAt (fun B : HermitianMat n ℂ => OpenAIEntropy.entropy B.mat)
      (entropyGradient A.mat) A := by
  have hl := hasFDerivAt_logarithm hA
  have hp := (inclusion (n := n)).hasFDerivAt.mul' hl
  have ht := (traceRe (n := n)).hasFDerivAt.comp A hp
  have hn := ht.neg
  have hd : - ((traceRe (n := n)).comp
      (A.mat • logDeriv A.mat + MulOpposite.op (BetaPowers.logarithm A.mat) • inclusion)) =
      entropyGradient A.mat := by
    apply ContinuousLinearMap.ext
    intro H
    simp only [ContinuousLinearMap.neg_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.add_apply,_root_.smul_apply,inclusion_apply,traceRe_apply,entropyGradient_apply]
    change -(A.mat * logDeriv A.mat H + H.mat * BetaPowers.logarithm A.mat).trace.re =
      -(H.mat * (BetaPowers.logarithm A.mat+1)).trace.re
    rw [Matrix.trace_add,Complex.add_re,trace_mul_logDeriv hA,
      Matrix.mul_add,Matrix.mul_one,Matrix.trace_add,Complex.add_re]
    ring
  have h := hn.congr_fderiv hd
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun B => entropy_eq_trace B.H)

end QubitAdditivity.BetaLog

