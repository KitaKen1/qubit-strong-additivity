import QubitAdditivity.BetaBridge
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix
open scoped Matrix ComplexOrder MatrixOrder

namespace QubitAdditivity.BetaComparison
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The contact-point square completion uses the full Gram inequality directly.
It does not require a pseudoinverse or a simple contact eigenvalue. -/
theorem gram_completion_posSemidef (F G H C : Matrix n n ℂ)
    (hC : C.IsHermitian)
    (hGram : (Matrix.fromBlocks F G G H).PosSemidef) :
    (H - G * C - C * G + C * F * C).PosSemidef := by
  have hh := hGram.conjTranspose_mul_mul_same (Matrix.fromRows (-C) 1)
  convert hh using 1
  rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.conjTranspose_neg, hC.eq, Matrix.conjTranspose_one,
    Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]
  simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.one_mul, Matrix.mul_one,
    Matrix.add_mul, Matrix.mul_add, neg_neg]
  abel

/-- A scalar multiple of a commuting exponential barrier has strictly negative
second variation at a contact. The trial-vector velocity is -C v / 2. -/
theorem contact_second_nonpos (F G H B C : Matrix n n ℂ) (lambda : ℝ)
    (hC : C.IsHermitian) (hCB : C * B = B * C)
    (hR : (lambda • B - F).PosSemidef)
    (hGram : (Matrix.fromBlocks F G G H).PosSemidef) :
    (lambda • (C * C * B) - H - C * (lambda • (C * B) - G) -
      (lambda • (C * B) - G) * C + (1/2 : ℝ) • (C * (lambda • B - F) * C)) ≤ 0 := by
  have hp := gram_completion_posSemidef F G H C hC hGram
  have hq : (C * (lambda • B - F) * C).PosSemidef := by
    simpa only [hC.eq] using hR.conjTranspose_mul_mul_same C
  have hh := hp.add (hq.smul (α := ℝ) (by norm_num : 0 ≤ (1/2 : ℝ)))
  have he : lambda • (C * C * B) - H - C * (lambda • (C * B) - G) -
      (lambda • (C * B) - G) * C + (1/2 : ℝ) • (C * (lambda • B - F) * C) =
      -(H - G * C - C * G + C * F * C + (1/2 : ℝ) • (C * (lambda • B - F) * C)) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
    simp only [Matrix.mul_assoc]
    have he : C * (B * C) = C * (C * B) := congrArg (fun X => C * X) hCB.symm
    simp only [he]
    module
  rw [he]
  exact neg_nonpos.mpr hh.nonneg

open scoped Topology

/-- The necessary second derivative test, proved without a continuity assumption
on the second derivative. -/
theorem second_nonneg_of_localMin {f : ℝ → ℝ} {t : ℝ}
    (hmin : IsLocalMin f t) (hf : ContinuousAt f t) : 0 ≤ deriv (deriv f) t := by
  by_contra! hn
  have hmax := isLocalMax_of_deriv_deriv_neg hn hmin.deriv_eq_zero hf
  have he : f =ᶠ[nhds t] (fun _ => f t) := by
    filter_upwards [hmin, hmax] with u hu hv
    exact le_antisymm hv hu
  have hh := he.deriv.deriv_eq
  rw [deriv_const', deriv_const] at hh
  linarith

def pairing (x : n → ℂ) (A : Matrix n n ℂ) (y : n → ℂ) : ℂ :=
  star x ⬝ᵥ A *ᵥ y

def quadratic (A : Matrix n n ℂ) (x : n → ℂ) : ℝ := (pairing x A x).re

theorem posSemidef_of_quadratic {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (h : ∀ x, 0 ≤ quadratic A x) : A.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hA
  intro x
  exact Complex.nonneg_iff.mpr ⟨h x, (hA.im_star_dotProduct_mulVec_self x).symm⟩

theorem quadratic_nonneg {A : Matrix n n ℂ} (hA : A.PosSemidef) (x : n → ℂ) :
    0 ≤ quadratic A x := (Complex.nonneg_iff.mp (hA.dotProduct_mulVec_nonneg x)).1

theorem quadratic_pos {A : Matrix n n ℂ} (hA : A.PosDef) {x : n → ℂ} (hx : x ≠ 0) :
    0 < quadratic A x := by
  exact (Complex.pos_iff.mp (hA.dotProduct_mulVec_pos hx)).1

theorem hasDerivAt_pairing {x y : ℝ → n → ℂ} {A : ℝ → Matrix n n ℂ}
    {u v : n → ℂ} {H : Matrix n n ℂ} {t : ℝ}
    (hx : HasDerivAt x u t) (hA : HasDerivAt A H t) (hy : HasDerivAt y v t) :
    HasDerivAt (fun z => pairing (x z) (A z) (y z))
      (pairing u (A t) (y t) + pairing (x t) H (y t) + pairing (x t) (A t) v) t := by
  have hh := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
      (((hasDerivAt_pi.1 hx i).star.mul (hasDerivAt_pi.1 (hasDerivAt_pi.1 hA i) j)).mul
        (hasDerivAt_pi.1 hy j))))
  convert hh using 1
  · ext z
    simp [pairing, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  · simp [pairing, dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_add_distrib,
      add_mul, mul_assoc]

theorem quadratic_sub (A B : Matrix n n ℂ) (x : n → ℂ) :
    quadratic (A-B) x = quadratic A x - quadratic B x := by
  simp [quadratic, pairing, Matrix.sub_mulVec, dotProduct_sub]

theorem quadratic_smul (c : ℝ) (A : Matrix n n ℂ) (x : n → ℂ) :
    quadratic (c • A) x = c * quadratic A x := by
  simp [quadratic, pairing, Matrix.smul_mulVec, dotProduct_smul, Complex.real_smul]

theorem quadratic_smul_vector (c : ℝ) (A : Matrix n n ℂ) (x : n → ℂ) :
    quadratic A (c • x) = c^2 * quadratic A x := by
  simp [quadratic, pairing, Matrix.mulVec_smul, star_smul, smul_dotProduct,
    dotProduct_smul, Complex.real_smul, pow_two, mul_assoc]

theorem le_of_quadratic_unit {A B : Matrix n n ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian)
    (h : ∀ x : n → ℂ, ‖x‖ = 1 → quadratic A x ≤ quadratic B x) : A ≤ B := by
  apply Matrix.le_iff.mpr
  apply posSemidef_of_quadratic (hB.sub hA)
  intro x
  by_cases hx : x = 0
  · simp [hx, quadratic, pairing]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hunit : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := by rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  have hh := h ((‖x‖⁻¹ : ℝ) • x) hunit
  rw [quadratic_smul_vector, quadratic_smul_vector] at hh
  have hh' := (mul_le_mul_iff_right₀ (sq_pos_of_pos (inv_pos.mpr hn))).mp hh
  rw [quadratic_sub]
  exact sub_nonneg.mpr hh'

/-- The exact second derivative along the affine trial vector. -/
theorem affine_trial_second {R R₁ R₂ : ℝ → Matrix n n ℂ} {t : ℝ}
    (hR : ∀ u, HasDerivAt R (R₁ u) u)
    (hR₁ : HasDerivAt R₁ (R₂ t) t) (v w : n → ℂ) :
    deriv (deriv (fun u => quadratic (R u) (v + (u-t) • w))) t =
      (pairing v (R₂ t) v + 2 * pairing w (R₁ t) v +
        2 * pairing v (R₁ t) w + 2 * pairing w (R t) w).re := by
  let x : ℝ → n → ℂ := fun u => v + (u-t) • w
  have hx (u : ℝ) : HasDerivAt x w u := by
    apply hasDerivAt_pi.2
    intro i
    simpa [x] using (((hasDerivAt_id u).sub_const t).smul_const (w i)).const_add (v i)
  let d : ℝ → ℝ := fun u =>
    (pairing w (R u) (x u) + pairing (x u) (R₁ u) (x u) + pairing (x u) (R u) w).re
  have hd (u : ℝ) : HasDerivAt (fun z => quadratic (R z) (x z)) (d u) u := by
    have hh := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u (hasDerivAt_pairing (hx u) (hR u) (hx u))
    exact hh
  have he : deriv (fun z => quadratic (R z) (x z)) = d := funext fun u => (hd u).deriv
  rw [he]
  have hh := ((hasDerivAt_pairing (hasDerivAt_const t w) (hR t) (hx t)).add
    (hasDerivAt_pairing (hx t) hR₁ (hx t))).add
      (hasDerivAt_pairing (hx t) (hR t) (hasDerivAt_const t w))
  have hh' := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hh).deriv
  convert hh' using 1
  · rfl
  · simp only [Complex.reCLM_apply, x, sub_self, zero_smul, add_zero, pairing, star_zero,
      dotProduct_zero, zero_dotProduct, Matrix.mulVec_zero, zero_add]
    ring

/-- Compactness produces an interior contact with a globally dominating
scalar multiple of the barrier. There is no eigenvalue multiplicity premise. -/
theorem exists_contact_of_not_le {F B : ℝ → Matrix n n ℂ}
    (hF : Continuous F) (hB : Continuous B)
    (hFH : ∀ u ∈ Set.Icc (0 : ℝ) 1, (F u).IsHermitian)
    (hBP : ∀ u ∈ Set.Icc (0 : ℝ) 1, (B u).PosDef)
    (hzero : F 0 ≤ B 0) (hone : F 1 ≤ B 1)
    {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) (hfail : ¬ F a ≤ B a) :
    ∃ lambda > (1 : ℝ), ∃ t ∈ Set.Ioo (0 : ℝ) 1, ∃ v : n → ℂ,
      ‖v‖ = 1 ∧ (∀ u ∈ Set.Icc (0 : ℝ) 1, (lambda • B u - F u).PosSemidef) ∧
      quadratic (lambda • B t - F t) v = 0 := by
  classical
  obtain ⟨v₁, hv₁, hvfail⟩ : ∃ v : n → ℂ, ‖v‖ = 1 ∧ quadratic (B a) v < quadratic (F a) v := by
    by_contra! hn
    exact hfail (le_of_quadratic_unit (hFH a ha) (hBP a ha).1 hn)
  let S : Set (ℝ × (n → ℂ)) := Set.Icc (0 : ℝ) 1 ×ˢ Metric.sphere 0 1
  let q : (ℝ × (n → ℂ)) → ℝ := fun z => quadratic (F z.1) z.2 / quadratic (B z.1) z.2
  have hqF : Continuous (fun z : ℝ × (n → ℂ) => quadratic (F z.1) z.2) := by
    simp only [quadratic, pairing, dotProduct, Matrix.mulVec]
    fun_prop
  have hqB : Continuous (fun z : ℝ × (n → ℂ) => quadratic (B z.1) z.2) := by
    simp only [quadratic, pairing, dotProduct, Matrix.mulVec]
    fun_prop
  have hpos (z : ℝ × (n → ℂ)) (hz : z ∈ S) : 0 < quadratic (B z.1) z.2 := by
    apply quadratic_pos (hBP z.1 hz.1)
    have hh : ‖z.2‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hz.2
    intro he
    simp [he] at hh
  have hq : ContinuousOn q S := hqF.continuousOn.div hqB.continuousOn
    (fun z hz => (hpos z hz).ne')
  have hcompact : IsCompact S := isCompact_Icc.prod (isCompact_sphere (0 : n → ℂ) 1)
  have hvS : (a, v₁) ∈ S := ⟨ha, by simpa [Metric.mem_sphere, dist_zero_right] using hv₁⟩
  obtain ⟨z, hz, hmax⟩ := hcompact.exists_isMaxOn ⟨(a,v₁), hvS⟩ hq
  let lambda := q z
  have hlambda : 1 < lambda := by
    have hh := hmax hvS
    have hqv : 1 < q (a,v₁) := (one_lt_div (hpos _ hvS)).mpr hvfail
    exact hqv.trans_le hh
  have hbound : ∀ u ∈ Set.Icc (0 : ℝ) 1, (lambda • B u - F u).PosSemidef := by
    intro u hu
    have hh : F u ≤ lambda • B u := by
      apply le_of_quadratic_unit (hFH u hu) ((hBP u hu).1.smul (by rfl : IsSelfAdjoint lambda))
      intro v hv
      have hvS' : (u,v) ∈ S := ⟨hu, by simpa [Metric.mem_sphere, dist_zero_right] using hv⟩
      have hm := hmax hvS'
      have hm' : quadratic (F u) v ≤ lambda * quadratic (B u) v :=
        (div_le_iff₀ (hpos _ hvS')).mp hm
      rwa [quadratic_smul]
    exact Matrix.le_iff.mp hh
  have hz0 : z.1 ≠ 0 := by
    intro he
    have hh := (Matrix.le_iff.mp hzero).dotProduct_mulVec_nonneg z.2
    have hq0 := quadratic_nonneg (Matrix.le_iff.mp hzero) z.2
    rw [quadratic_sub] at hq0
    have hm : q z ≤ 1 := by
      dsimp [q]
      rw [he]
      exact (div_le_one (by simpa [he] using hpos z hz)).mpr (sub_nonneg.mp hq0)
    exact (not_le_of_gt hlambda) hm
  have hz1 : z.1 ≠ 1 := by
    intro he
    have hq1 := quadratic_nonneg (Matrix.le_iff.mp hone) z.2
    rw [quadratic_sub] at hq1
    have hm : q z ≤ 1 := by
      dsimp [q]
      rw [he]
      exact (div_le_one (by simpa [he] using hpos z hz)).mpr (sub_nonneg.mp hq1)
    exact (not_le_of_gt hlambda) hm
  refine ⟨lambda, hlambda, z.1, ⟨lt_of_le_of_ne hz.1.1 hz0.symm,
    lt_of_le_of_ne hz.1.2 hz1⟩, z.2, ?_, hbound, ?_⟩
  · simpa [Metric.mem_sphere, dist_zero_right] using hz.2
  · rw [quadratic_sub, quadratic_smul]
    dsimp [lambda, q]
    rw [div_mul_cancel₀ _ (hpos z hz).ne', sub_self]

theorem pairing_mulVec_left (x y : n → ℂ) (A C : Matrix n n ℂ) :
    pairing (C *ᵥ x) A y = pairing x (Cᴴ * A) y := by
  simp only [pairing, star_mulVec, ← dotProduct_mulVec, Matrix.mulVec_mulVec]

theorem pairing_mulVec_right (x y : n → ℂ) (A C : Matrix n n ℂ) :
    pairing x A (C *ᵥ y) = pairing x (A * C) y := by
  simp only [pairing, Matrix.mulVec_mulVec]

theorem pairing_smul_left (c : ℝ) (x y : n → ℂ) (A : Matrix n n ℂ) :
    pairing (c • x) A y = c • pairing x A y := by
  simp [pairing, star_smul, smul_dotProduct]

theorem pairing_smul_right (c : ℝ) (x y : n → ℂ) (A : Matrix n n ℂ) :
    pairing x A (c • y) = c • pairing x A y := by
  simp [pairing, Matrix.mulVec_smul, dotProduct_smul]

theorem pairing_sub (x y : n → ℂ) (A B : Matrix n n ℂ) :
    pairing x (A-B) y = pairing x A y - pairing x B y := by
  simp [pairing, Matrix.sub_mulVec, dotProduct_sub]

theorem pairing_add (x y : n → ℂ) (A B : Matrix n n ℂ) :
    pairing x (A+B) y = pairing x A y + pairing x B y := by
  simp [pairing, Matrix.add_mulVec, dotProduct_add]

theorem pairing_smul_matrix (c : ℝ) (x y : n → ℂ) (A : Matrix n n ℂ) :
    pairing x (c • A) y = c • pairing x A y := by
  simp [pairing, Matrix.smul_mulVec, dotProduct_smul]

/-- The affine trial-vector second variation written as a matrix quadratic form. -/
theorem affine_second_eq_quadratic (R R₁ R₂ C : Matrix n n ℂ)
    (hC : C.IsHermitian) (v : n → ℂ) :
    (pairing v R₂ v + 2 * pairing ((-1/2 : ℝ) • (C *ᵥ v)) R₁ v +
      2 * pairing v R₁ ((-1/2 : ℝ) • (C *ᵥ v)) +
      2 * pairing ((-1/2 : ℝ) • (C *ᵥ v)) R ((-1/2 : ℝ) • (C *ᵥ v))).re =
    quadratic (R₂ - C * R₁ - R₁ * C + (1/2 : ℝ) • (C * R * C)) v := by
  simp only [quadratic, pairing_smul_left, pairing_smul_right, pairing_mulVec_left,
    pairing_mulVec_right, hC.eq, pairing_sub, pairing_add, pairing_smul_matrix,
    Complex.real_smul, Matrix.mul_assoc]
  congr 1
  norm_num <;> ring

theorem quadratic_mono {A B : Matrix n n ℂ} (h : A ≤ B) (v : n → ℂ) :
    quadratic A v ≤ quadratic B v := by
  have hh := quadratic_nonneg (Matrix.le_iff.mp h) v
  rw [quadratic_sub] at hh
  exact sub_nonneg.mp hh

/-- Matrix maximum principle for a commuting strict exponential barrier.
All analytic derivative hypotheses are explicit, and the conclusion has no
matrix-comparison premise. The curvature input is the full stationary Gram. -/
theorem le_of_strict_barrier
    (F F₁ F₂ B B₁ B₂ C : ℝ → Matrix n n ℂ) (a : ℝ) (ha : 0 < a)
    (hF : ∀ u, HasDerivAt F (F₁ u) u) (hF₁ : ∀ u, HasDerivAt F₁ (F₂ u) u)
    (hB : ∀ u, HasDerivAt B (B₁ u) u) (hB₁ : ∀ u, HasDerivAt B₁ (B₂ u) u)
    (hFH : ∀ u ∈ Set.Icc (0 : ℝ) 1, (F u).IsHermitian)
    (hBP : ∀ u ∈ Set.Icc (0 : ℝ) 1, (B u).PosDef)
    (hC : ∀ u, (C u).IsHermitian) (hCB : ∀ u, C u * B u = B u * C u)
    (hBfirst : ∀ u, B₁ u = C u * B u)
    (hBsecond : ∀ u, B₂ u = C u * C u * B u - a • B u)
    (hGram : ∀ u ∈ Set.Ioo (0 : ℝ) 1,
      (Matrix.fromBlocks (F u) (F₁ u) (F₁ u) (F₂ u)).PosSemidef)
    (hzero : F 0 ≤ B 0) (hone : F 1 ≤ B 1) :
    ∀ u ∈ Set.Icc (0 : ℝ) 1, F u ≤ B u := by
  intro u hu
  by_contra hn
  have hFc : Continuous F := continuous_pi fun i => continuous_pi fun j =>
    continuous_iff_continuousAt.mpr fun z =>
      (hasDerivAt_pi.1 (hasDerivAt_pi.1 (hF z) i) j).continuousAt
  have hBc : Continuous B := continuous_pi fun i => continuous_pi fun j =>
    continuous_iff_continuousAt.mpr fun z =>
      (hasDerivAt_pi.1 (hasDerivAt_pi.1 (hB z) i) j).continuousAt
  obtain ⟨lambda, hlambda, t, ht, v, hv, hR, hzeroR⟩ :=
    exists_contact_of_not_le hFc hBc hFH hBP hzero hone hu hn
  let R : ℝ → Matrix n n ℂ := fun z => lambda • B z - F z
  let R₁ : ℝ → Matrix n n ℂ := fun z => lambda • B₁ z - F₁ z
  let R₂ : ℝ → Matrix n n ℂ := fun z => lambda • B₂ z - F₂ z
  let w : n → ℂ := (-1/2 : ℝ) • (C t *ᵥ v)
  let q : ℝ → ℝ := fun z => quadratic (R z) (v + (z-t) • w)
  have hdR (z : ℝ) : HasDerivAt R (R₁ z) z := by
    apply hasDerivAt_pi.2
    intro i
    apply hasDerivAt_pi.2
    intro j
    simpa [R, R₁, Pi.sub_def, Pi.smul_def] using ((hasDerivAt_pi.1 (hasDerivAt_pi.1 (hB z) i) j).const_smul lambda).sub
      (hasDerivAt_pi.1 (hasDerivAt_pi.1 (hF z) i) j)
  have hdR₁ : HasDerivAt R₁ (R₂ t) t := by
    apply hasDerivAt_pi.2
    intro i
    apply hasDerivAt_pi.2
    intro j
    simpa [R₁, R₂, Pi.sub_def, Pi.smul_def] using ((hasDerivAt_pi.1 (hasDerivAt_pi.1 (hB₁ t) i) j).const_smul lambda).sub
      (hasDerivAt_pi.1 (hasDerivAt_pi.1 (hF₁ t) i) j)
  have hqmin : IsLocalMin q t := by
    have hnh : Set.Icc (0 : ℝ) 1 ∈ nhds t := Icc_mem_nhds ht.1 ht.2
    filter_upwards [hnh] with z hz
    have hh := quadratic_nonneg (hR z hz) (v + (z-t) • w)
    simpa [q, R, sub_self, zero_smul, hzeroR] using hh
  have hx : HasDerivAt (fun z => v + (z-t) • w) w t := by
    apply hasDerivAt_pi.2
    intro i
    simpa using (((hasDerivAt_id t).sub_const t).smul_const (w i)).const_add (v i)
  have hqc : ContinuousAt q t :=
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_pairing hx (hdR t) hx)).continuousAt
  have hs := affine_trial_second hdR hdR₁ v w
  rw [affine_second_eq_quadratic (R t) (R₁ t) (R₂ t) (C t) (hC t) v] at hs
  let Z := lambda • (C t * C t * B t) - F₂ t - C t * (lambda • (C t * B t) - F₁ t) -
    (lambda • (C t * B t) - F₁ t) * C t + (1/2 : ℝ) • (C t * (lambda • B t - F t) * C t)
  have hZ : Z ≤ 0 := contact_second_nonpos (F t) (F₁ t) (F₂ t) (B t) (C t) lambda
    (hC t) (hCB t) (hR t ⟨ht.1.le,ht.2.le⟩) (hGram t ht)
  have he : R₂ t - C t * R₁ t - R₁ t * C t + (1/2 : ℝ) • (C t * R t * C t) =
      Z - (lambda*a) • B t := by
    dsimp [R, R₁, R₂, Z]
    simp only [hBfirst, hBsecond, smul_sub]
    module
  rw [he, quadratic_sub, quadratic_smul] at hs
  have hZv : quadratic Z v ≤ 0 := by
    simpa [quadratic, pairing] using quadratic_mono hZ v
  have hvne : v ≠ 0 := by intro he; simp [he] at hv
  have hpos := quadratic_pos (hBP t ⟨ht.1.le,ht.2.le⟩) hvne
  have hprod : 0 < (lambda*a) * quadratic (B t) v := mul_pos (mul_pos (by linarith) ha) hpos
  have hnonneg := second_nonneg_of_localMin hqmin hqc
  change deriv (deriv q) t = _ at hs
  linarith

end QubitAdditivity.BetaComparison
