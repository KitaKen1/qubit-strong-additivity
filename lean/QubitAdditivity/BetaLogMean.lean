import QubitAdditivity.BetaLog

set_option autoImplicit false
noncomputable section
open Set

namespace QubitAdditivity.BetaLogMean

/-- Scalar coefficient of the PW integral in a spectral matrix-unit basis. -/
def mean (a b : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, a^t * b^(1-t)

/-- Scalar coefficient of the compact-interval logarithm differential. -/
def inverseMean (a b : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, (1+t*(a-1))⁻¹ * (1+t*(b-1))⁻¹

theorem mean_mul_log_sub {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    mean a b * (Real.log a - Real.log b) = a-b := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => a^t*b^(1-t))
      (a^t*b^(1-t)*(Real.log a-Real.log b)) t := by
    have ha' := (Real.hasStrictDerivAt_const_rpow ha t).hasDerivAt
    have hb' := (Real.hasStrictDerivAt_const_rpow hb (1-t)).hasDerivAt.comp t
      ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t))
    convert! ha'.mul hb' using 1 <;> simp <;> ring
  have hc : Continuous (fun t : ℝ => a^t*b^(1-t)*(Real.log a-Real.log b)) := by
    exact ((Real.continuous_const_rpow ha.ne').mul
      ((Real.continuous_const_rpow hb.ne').comp (continuous_const.sub continuous_id))).mul continuous_const
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun t _ => hd t) (hc.intervalIntegrable 0 1)
  simpa [mean,intervalIntegral.integral_mul_const] using h

theorem inverseMean_mul_sub {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    inverseMean a b * (a-b) = Real.log a - Real.log b := by
  have hpa (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) := BetaLog.scalar_segment_pos ha ht
  have hpb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) := BetaLog.scalar_segment_pos hb ht
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ => Real.log (1+t*(a-1))-Real.log (1+t*(b-1)))
        ((1+t*(a-1))⁻¹ * (1+t*(b-1))⁻¹ * (a-b)) t := by
    convert! ((((hasDerivAt_id t).mul_const (a-1)).const_add 1).log (hpa t ht).ne').sub
      ((((hasDerivAt_id t).mul_const (b-1)).const_add 1).log (hpb t ht).ne') using 1
    simp
    field_simp [(hpa t ht).ne',(hpb t ht).ne']
    ring
  have hsa : ContinuousOn (fun t : ℝ => (1+t*(a-1))⁻¹) (Icc (0 : ℝ) 1) :=
    (by fun_prop : ContinuousOn (fun t : ℝ => 1+t*(a-1)) (Icc (0 : ℝ) 1)).inv₀
      (fun t ht => (hpa t ht).ne')
  have hsb : ContinuousOn (fun t : ℝ => (1+t*(b-1))⁻¹) (Icc (0 : ℝ) 1) :=
    (by fun_prop : ContinuousOn (fun t : ℝ => 1+t*(b-1)) (Icc (0 : ℝ) 1)).inv₀
      (fun t ht => (hpb t ht).ne')
  have hc : ContinuousOn (fun t : ℝ =>
      (1+t*(a-1))⁻¹ * (1+t*(b-1))⁻¹ * (a-b)) (Icc (0 : ℝ) 1) :=
    (hsa.mul hsb).mul continuousOn_const
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun t ht => hd t (by simpa using ht))
    ((show ContinuousOn _ (uIcc (0 : ℝ) 1) from by simpa using hc).intervalIntegrable)
  simpa [inverseMean,intervalIntegral.integral_mul_const] using h

theorem mean_self {a : ℝ} (ha : 0 < a) : mean a a = a := by
  have he (t : ℝ) : a^t*a^(1-t) = a := by
    rw [← Real.rpow_add ha,show t+(1-t) = 1 by ring,Real.rpow_one]
  simp only [mean,he]
  simp

theorem self_mul_inverseMean {a : ℝ} (ha : 0 < a) : a * inverseMean a a = 1 := by
  have he (t : ℝ) : a*((1+t*(a-1))⁻¹ * (1+t*(a-1))⁻¹) = a/(1+t*(a-1))^2 := by
    simp [div_eq_mul_inv,pow_two,← mul_assoc]
  rw [inverseMean,← intervalIntegral.integral_const_mul]
  simpa only [he] using BetaLog.scalar_inverse_square_integral ha

/-- The divided-difference and logarithmic-mean coefficients are inverses,
including the coincident-eigenvalue case. -/
theorem mean_mul_inverseMean {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    mean a b * inverseMean a b = 1 := by
  by_cases hab : a = b
  · subst b
    rw [mean_self ha]
    exact self_mul_inverseMean ha
  have hlog : Real.log a - Real.log b ≠ 0 := by
    intro h
    exact hab (Real.log_injOn_pos ha hb (sub_eq_zero.mp h))
  have h1 := mean_mul_log_sub ha hb
  have h2 := inverseMean_mul_sub ha hb
  apply mul_right_cancel₀ hlog
  calc
    (mean a b * inverseMean a b) * (Real.log a-Real.log b) =
        inverseMean a b * (a-b) := by rw [mul_assoc, mul_comm (inverseMean a b),← mul_assoc,h1,mul_comm]
    _ = 1 * (Real.log a-Real.log b) := by simpa using h2

end QubitAdditivity.BetaLogMean
