import QubitAdditivity.TC4
import QubitAdditivity.Imported.SpectralEntropy
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Qubit tools for the single-channel bound: the bilinear form `⟨v, M w⟩`, the 2×2 Gram
identity, entropy of 2×2 matrices through trace and determinant, and a positivity test. -/

noncomputable section
open scoped Matrix BigOperators ComplexOrder
open Matrix

namespace QubitAdditivity

/-- `⟨v, M w⟩`. -/
def bform {n : Type*} [Fintype n] (M : Matrix n n ℂ) (v w : n → ℂ) : ℂ := star v ⬝ᵥ (M *ᵥ w)

section bform

variable {n : Type*} [Fintype n]

theorem bform_add (M N : Matrix n n ℂ) (v w : n → ℂ) :
    bform (M + N) v w = bform M v w + bform N v w := by
  simp [bform, Matrix.add_mulVec, dotProduct_add]

theorem bform_smul (r : ℝ) (M : Matrix n n ℂ) (v w : n → ℂ) :
    bform (r • M) v w = r * bform M v w := by
  simp [bform, Matrix.smul_mulVec, dotProduct_smul, Complex.real_smul]

theorem bform_self_im {M : Matrix n n ℂ} (hM : M.IsHermitian) (v : n → ℂ) :
    (bform M v v).im = 0 :=
  hM.im_star_dotProduct_mulVec_self v

theorem bform_self_re_nonneg {M : Matrix n n ℂ} (hM : M.PosSemidef) (v : n → ℂ) :
    0 ≤ (bform M v v).re :=
  (Complex.nonneg_iff.mp (hM.dotProduct_mulVec_nonneg v)).1

theorem bform_self_eq_re {M : Matrix n n ℂ} (hM : M.IsHermitian) (v : n → ℂ) :
    bform M v v = ((bform M v v).re : ℂ) :=
  Complex.ext rfl (by simp [bform_self_im hM])

theorem star_bform {M : Matrix n n ℂ} (hM : M.IsHermitian) (v w : n → ℂ) :
    star (bform M v w) = bform M w v := by
  simp only [bform, dotProduct, Matrix.mulVec, Pi.star_apply, star_sum, star_mul', star_star,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [hM.apply j i]
  ring

theorem sum_bform_self_eq_re {M : Matrix n n ℂ} (hM : M.IsHermitian) {ι : Type*} [Fintype ι]
    (u : ι → n → ℂ) : ∑ j, bform M (u j) (u j) = ((∑ j, (bform M (u j) (u j)).re : ℝ) : ℂ) := by
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun j _ => bform_self_eq_re hM (u j)

end bform

/-- The 2×2 Gram identity: `det (V* M V) = |det V|² det M` for `V = [a c]`. -/
theorem bform_gram_det (M : Matrix (Fin 2) (Fin 2) ℂ) (a c : Fin 2 → ℂ) :
    bform M a a * bform M c c - bform M a c * bform M c a =
      star (a 0 * c 1 - a 1 * c 0) * M.det * (a 0 * c 1 - a 1 * c 0) := by
  simp only [bform, Matrix.det_fin_two, dotProduct, Matrix.mulVec, Fin.sum_univ_two,
    Pi.star_apply, star_sub, star_mul']
  ring

/-- For a singular 2×2 matrix the cross term saturates Cauchy–Schwarz. -/
theorem bform_cross_of_det_zero {M : Matrix (Fin 2) (Fin 2) ℂ} (hdet : M.det = 0)
    (a c : Fin 2 → ℂ) : bform M a c * bform M c a = bform M a a * bform M c c := by
  have h := bform_gram_det M a c
  rw [hdet, mul_zero, zero_mul] at h
  linear_combination -h

section spectrum

variable {M N : Matrix (Fin 2) (Fin 2) ℂ}

theorem eigenvalues_sum_fin_two (hM : M.IsHermitian) :
    hM.eigenvalues 0 + hM.eigenvalues 1 = M.trace.re := by
  have h := hM.trace_eq_sum_eigenvalues
  rw [Fin.sum_univ_two] at h
  rw [h]
  simp

theorem eigenvalues_prod_fin_two (hM : M.IsHermitian) :
    hM.eigenvalues 0 * hM.eigenvalues 1 = M.det.re := by
  have h := hM.det_eq_prod_eigenvalues
  rw [Fin.prod_univ_two] at h
  rw [h]
  simp [← Complex.ofReal_mul]

theorem det_im_fin_two (hM : M.IsHermitian) : M.det.im = 0 := by
  have h := hM.det_eq_prod_eigenvalues
  rw [Fin.prod_univ_two] at h
  rw [h]
  simp [← Complex.ofReal_mul]

/-- Two 2×2 Hermitian matrices with the same trace and determinant have the same entropy. -/
theorem entropy_eq_of_trace_det (hM : M.IsHermitian) (hN : N.IsHermitian)
    (htr : M.trace = N.trace) (hdet : M.det = N.det) :
    OpenAIEntropy.entropy M = OpenAIEntropy.entropy N := by
  rw [OpenAIEntropy.entropy_eq_sum hM, OpenAIEntropy.entropy_eq_sum hN, Fin.sum_univ_two,
    Fin.sum_univ_two]
  have hs : hM.eigenvalues 0 + hM.eigenvalues 1 = hN.eigenvalues 0 + hN.eigenvalues 1 := by
    rw [eigenvalues_sum_fin_two hM, eigenvalues_sum_fin_two hN, htr]
  have hp : hM.eigenvalues 0 * hM.eigenvalues 1 = hN.eigenvalues 0 * hN.eigenvalues 1 := by
    rw [eigenvalues_prod_fin_two hM, eigenvalues_prod_fin_two hN, hdet]
  have hl1 : hM.eigenvalues 1 = hN.eigenvalues 0 + hN.eigenvalues 1 - hM.eigenvalues 0 := by
    linarith
  have hroot : (hM.eigenvalues 0 - hN.eigenvalues 0) * (hM.eigenvalues 0 - hN.eigenvalues 1) =
      0 := by
    rw [hl1] at hp
    linear_combination -hp
  rcases mul_eq_zero.mp hroot with h | h
  · rw [show hM.eigenvalues 0 = hN.eigenvalues 0 by linarith,
      show hM.eigenvalues 1 = hN.eigenvalues 1 by linarith]
  · rw [show hM.eigenvalues 0 = hN.eigenvalues 1 by linarith,
      show hM.eigenvalues 1 = hN.eigenvalues 0 by linarith, add_comm]

/-- A 2×2 Hermitian matrix with nonnegative trace and determinant is positive semidefinite. -/
theorem posSemidef_of_fin_two (hM : M.IsHermitian) (htr : 0 ≤ M.trace.re)
    (hdet : 0 ≤ M.det.re) : M.PosSemidef := by
  rw [hM.posSemidef_iff_eigenvalues_nonneg]
  have hs := eigenvalues_sum_fin_two hM
  have hp := eigenvalues_prod_fin_two hM
  have h0 : 0 ≤ hM.eigenvalues 0 := by
    by_contra hneg
    have hneg := not_le.mp hneg
    have : hM.eigenvalues 1 ≤ 0 := by
      by_contra h1
      have h1 := not_le.mp h1
      nlinarith
    linarith
  have h1 : 0 ≤ hM.eigenvalues 1 := by
    by_contra hneg
    have hneg := not_le.mp hneg
    have : hM.eigenvalues 0 ≤ 0 := by
      by_contra h0'
      have h0' := not_le.mp h0'
      nlinarith
    linarith
  intro i
  fin_cases i
  · exact h0
  · exact h1

end spectrum

section direction

/-- Traceless Hermitian 2×2 matrices, parametrized by three real numbers. -/
def dirMat (v : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(v 0 : ℂ), (v 1 : ℂ) + (v 2 : ℂ) * Complex.I;
     (v 1 : ℂ) - (v 2 : ℂ) * Complex.I, -(v 0 : ℂ)]

theorem dirMat_add (v w : Fin 3 → ℝ) : dirMat (v + w) = dirMat v + dirMat w := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dirMat] <;> ring

theorem dirMat_smul (r : ℝ) (v : Fin 3 → ℝ) : dirMat (r • v) = r • dirMat v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dirMat, Complex.real_smul] <;> ring

theorem dirMat_isHermitian (v : Fin 3 → ℝ) : (dirMat v).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dirMat, Matrix.conjTranspose_apply, sub_eq_add_neg]

theorem dirMat_trace (v : Fin 3 → ℝ) : (dirMat v).trace = 0 := by
  simp [dirMat, Matrix.trace_fin_two]

theorem dirMat_det (v : Fin 3 → ℝ) :
    (dirMat v).det = -(((v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 : ℝ) : ℂ) := by
  rw [dirMat, Matrix.det_fin_two_of]
  push_cast
  linear_combination ((v 2 : ℂ)) ^ 2 * Complex.I_sq

/-- Real parts of the two expectations along `dirMat v`. -/
def expectMap (a c : Fin 2 → ℂ) : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun v := ![(bform (dirMat v) a a).re, (bform (dirMat v) c c).re]
  map_add' v w := by
    ext i
    fin_cases i <;> simp [dirMat_add, bform_add]
  map_smul' r v := by
    ext i
    fin_cases i <;> simp [dirMat_smul, bform_smul]

/-- A nonzero traceless Hermitian direction along which both expectations are constant. -/
theorem exists_dir (a c : Fin 2 → ℂ) :
    ∃ v : Fin 3 → ℝ, v ≠ 0 ∧ bform (dirMat v) a a = 0 ∧ bform (dirMat v) c c = 0 := by
  have hlt : Module.finrank ℝ (Fin 2 → ℝ) < Module.finrank ℝ (Fin 3 → ℝ) := by simp
  obtain ⟨v, hv, hv0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := expectMap a c) hlt)
  rw [LinearMap.mem_ker] at hv
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  simp only [expectMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.cons_val_zero,
    Matrix.cons_val_one, Pi.zero_apply] at h0 h1
  exact ⟨v, hv0, Complex.ext h0 (bform_self_im (dirMat_isHermitian v) a),
    Complex.ext h1 (bform_self_im (dirMat_isHermitian v) c)⟩

theorem dirMat_ne_det (v : Fin 3 → ℝ) (hv : v ≠ 0) :
    0 < (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 := by
  by_contra h
  apply hv
  have h0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  have h2 : v 2 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
  ext i
  fin_cases i <;> simp [h0, h1, h2]

theorem det_add_smul_fin_two (ρ H : Matrix (Fin 2) (Fin 2) ℂ) (t : ℝ) :
    (ρ + t • H).det = ρ.det +
      (t : ℂ) * (ρ 0 0 * H 1 1 + ρ 1 1 * H 0 0 - ρ 0 1 * H 1 0 - ρ 1 0 * H 0 1) +
      (t : ℂ) ^ 2 * H.det := by
  simp only [Matrix.det_fin_two, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
  ring

end direction

section split

theorem isHermitian_add_real_smul {ρ H : Matrix (Fin 2) (Fin 2) ℂ} (hρ : ρ.IsHermitian)
    (hH : H.IsHermitian) (t : ℝ) : (ρ + t • H).IsHermitian := by
  unfold Matrix.IsHermitian at *
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hρ, hH, star_trivial]

theorem quad_root {D β δ S t : ℝ} (hδ : 0 < δ) (hS2 : S ^ 2 = β ^ 2 + 4 * δ * D)
    (ht : 2 * δ * t = β + S ∨ 2 * δ * t = β - S) : D + β * t - δ * t ^ 2 = 0 := by
  have key : 4 * δ * (D + β * t - δ * t ^ 2) =
      4 * δ * D + 2 * β * (2 * δ * t) - (2 * δ * t) ^ 2 := by ring
  have h4 : 4 * δ * (D + β * t - δ * t ^ 2) = 0 := by
    rcases ht with h | h <;> rw [key, h] <;> linear_combination (-1 : ℝ) * hS2
  exact (mul_eq_zero.mp h4).resolve_left (by positivity)

/-- A qubit state is a mixture of two singular states with the same two expectations
`⟨a, · a⟩` and `⟨c, · c⟩`. -/
theorem exists_two_expectation_split {ρ : Matrix (Fin 2) (Fin 2) ℂ}
    (hρ : OpenAIEntropy.IsState ρ) (a c : Fin 2 → ℂ) :
    ∃ (p : ℝ) (σ₁ σ₂ : Matrix (Fin 2) (Fin 2) ℂ),
      0 ≤ p ∧ p ≤ 1 ∧ OpenAIEntropy.IsState σ₁ ∧ OpenAIEntropy.IsState σ₂ ∧
      σ₁.det = 0 ∧ σ₂.det = 0 ∧ ρ = p • σ₁ + (1 - p) • σ₂ ∧
      bform σ₁ a a = bform ρ a a ∧ bform σ₂ a a = bform ρ a a ∧
      bform σ₁ c c = bform ρ c c ∧ bform σ₂ c c = bform ρ c c := by
  have hH : ρ.IsHermitian := hρ.1.isHermitian
  by_cases hdet : ρ.det = 0
  · exact ⟨1, ρ, ρ, zero_le_one, le_refl _, hρ, hρ, hdet, hdet, by simp, rfl, rfl, rfl, rfl⟩
  have hD : 0 < ρ.det.re := by
    have hre := (Complex.nonneg_iff.mp hρ.1.det_nonneg).1
    rcases hre.lt_or_eq with h | h
    · exact h
    · exact absurd (Complex.ext h.symm (det_im_fin_two hH)) hdet
  obtain ⟨v, hv0, hva, hvc⟩ := exists_dir a c
  have hδ := dirMat_ne_det v hv0
  set δ := (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2
  set D := ρ.det.re
  set β := (ρ 0 0 * dirMat v 1 1 + ρ 1 1 * dirMat v 0 0 - ρ 0 1 * dirMat v 1 0 -
    ρ 1 0 * dirMat v 0 1).re
  have hdetRe (t : ℝ) : (ρ + t • dirMat v).det.re = D + β * t - δ * t ^ 2 := by
    rw [det_add_smul_fin_two, dirMat_det]
    have h1 : (t : ℂ) ^ 2 * -(((v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 : ℝ) : ℂ) =
        ((-(δ * t ^ 2) : ℝ) : ℂ) := by
      simp only [δ]
      push_cast
      ring
    rw [h1, Complex.add_re, Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re]
    ring
  set S := Real.sqrt (β ^ 2 + 4 * δ * D)
  have hS2 : S ^ 2 = β ^ 2 + 4 * δ * D := Real.sq_sqrt (by positivity)
  have hSβ : |β| < S := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg β) (by nlinarith)
  set tp := (β + S) / (2 * δ) with htpdef
  set tm := (β - S) / (2 * δ) with htmdef
  have htp : 0 < tp := div_pos (by linarith [neg_abs_le β]) (by positivity)
  have htm : tm < 0 := div_neg_of_neg_of_pos (by linarith [le_abs_self β]) (by positivity)
  have hdtp : 2 * δ * tp = β + S := by rw [htpdef]; field_simp
  have hdtm : 2 * δ * tm = β - S := by rw [htmdef]; field_simp
  have hstate (t : ℝ) (ht : D + β * t - δ * t ^ 2 = 0) :
      OpenAIEntropy.IsState (ρ + t • dirMat v) ∧ (ρ + t • dirMat v).det = 0 := by
    have hHt := isHermitian_add_real_smul hH (dirMat_isHermitian v) t
    have htr : (ρ + t • dirMat v).trace = 1 := by
      rw [Matrix.trace_add, Matrix.trace_smul, dirMat_trace, smul_zero, add_zero, hρ.2]
    have hd : (ρ + t • dirMat v).det = 0 :=
      Complex.ext (by rw [hdetRe, ht]; rfl) (by rw [det_im_fin_two hHt]; rfl)
    refine ⟨⟨posSemidef_of_fin_two hHt (by rw [htr]; norm_num) (by rw [hd]; rfl), htr⟩, hd⟩
  have hexp (t : ℝ) (w : Fin 2 → ℂ) (hw : bform (dirMat v) w w = 0) :
      bform (ρ + t • dirMat v) w w = bform ρ w w := by
    rw [bform_add, bform_smul, hw, mul_zero, add_zero]
  obtain ⟨hσm, hdm⟩ := hstate tm (quad_root hδ hS2 (Or.inr hdtm))
  obtain ⟨hσp, hdp⟩ := hstate tp (quad_root hδ hS2 (Or.inl hdtp))
  have hgap : 0 < tp - tm := by linarith
  refine ⟨tp / (tp - tm), ρ + tm • dirMat v, ρ + tp • dirMat v,
    div_nonneg htp.le hgap.le, (div_le_one hgap).mpr (by linarith), hσm, hσp, hdm, hdp,
    ?_, hexp tm a hva, hexp tp a hva, hexp tm c hvc, hexp tp c hvc⟩
  have hcoef : tp / (tp - tm) * tm + (1 - tp / (tp - tm)) * tp = 0 := by
    field_simp
    ring
  calc ρ = ρ + (tp / (tp - tm) * tm + (1 - tp / (tp - tm)) * tp) • dirMat v := by
        rw [hcoef, zero_smul, add_zero]
    _ = (tp / (tp - tm)) • (ρ + tm • dirMat v) +
          (1 - tp / (tp - tm)) • (ρ + tp • dirMat v) := by
        module

end split

section normalForm

theorem bform_mix_re (p q : ℝ) (σ₁ σ₂ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    (bform (p • σ₁ + q • σ₂) v v).re = p * (bform σ₁ v v).re + q * (bform σ₂ v v).re := by
  rw [bform_add, bform_smul, bform_smul, Complex.add_re, Complex.re_ofReal_mul,
    Complex.re_ofReal_mul]

theorem tc4ScalarMatrix_isHermitian (x y z w : ℝ) : (tc4ScalarMatrix x y z w).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tc4ScalarMatrix, Matrix.conjTranspose_apply]

/-- A qubit channel in the one-common-branch normal form: the common Kraus operator has rows
`a*` and `c*`; the operators with rows `b j*` reach only output 0, those with `d k*` only
output 1. -/
structure QubitNormalForm (J K : Type*) [Fintype J] [Fintype K] where
  a : Fin 2 → ℂ
  c : Fin 2 → ℂ
  b : J → Fin 2 → ℂ
  d : K → Fin 2 → ℂ

namespace QubitNormalForm

variable {J K : Type*} [Fintype J] [Fintype K] (N : QubitNormalForm J K)

/-- The output on a 2×2 input. -/
def act (ρ : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![bform ρ N.a N.a + ∑ j, bform ρ (N.b j) (N.b j), bform ρ N.a N.c;
     bform ρ N.c N.a, bform ρ N.c N.c + ∑ k, bform ρ (N.d k) (N.d k)]

/-- The four Frobenius masses of the output blocks at the input `ρ`. -/
def mx (ρ : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := (bform ρ N.a N.a).re
def my (ρ : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := ∑ j, (bform ρ (N.b j) (N.b j)).re
def mz (ρ : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := (bform ρ N.c N.c).re
def mw (ρ : Matrix (Fin 2) (Fin 2) ℂ) : ℝ := ∑ k, (bform ρ (N.d k) (N.d k)).re

theorem act_isHermitian {σ : Matrix (Fin 2) (Fin 2) ℂ} (hσ : σ.IsHermitian) :
    (N.act σ).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [act, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Fin.zero_eta, Fin.mk_one, star_add, star_sum, star_bform hσ]

theorem act_trace {σ : Matrix (Fin 2) (Fin 2) ℂ} (hσ : σ.IsHermitian) :
    (N.act σ).trace = ((N.mx σ + N.my σ + N.mz σ + N.mw σ : ℝ) : ℂ) := by
  have ha : bform σ N.a N.a = (N.mx σ : ℂ) := bform_self_eq_re hσ N.a
  have hc : bform σ N.c N.c = (N.mz σ : ℂ) := bform_self_eq_re hσ N.c
  have hb : ∑ j, bform σ (N.b j) (N.b j) = (N.my σ : ℂ) := sum_bform_self_eq_re hσ N.b
  have hd : ∑ k, bform σ (N.d k) (N.d k) = (N.mw σ : ℂ) := sum_bform_self_eq_re hσ N.d
  rw [act, Matrix.trace_fin_two_of, ha, hb, hc, hd]
  push_cast
  ring

theorem act_det_of_det_zero {σ : Matrix (Fin 2) (Fin 2) ℂ} (hσ : σ.IsHermitian)
    (hdet : σ.det = 0) :
    (N.act σ).det = (((N.mx σ + N.my σ) * (N.mz σ + N.mw σ) - N.mx σ * N.mz σ : ℝ) : ℂ) := by
  have ha : bform σ N.a N.a = (N.mx σ : ℂ) := bform_self_eq_re hσ N.a
  have hc : bform σ N.c N.c = (N.mz σ : ℂ) := bform_self_eq_re hσ N.c
  have hb : ∑ j, bform σ (N.b j) (N.b j) = (N.my σ : ℂ) := sum_bform_self_eq_re hσ N.b
  have hd : ∑ k, bform σ (N.d k) (N.d k) = (N.mw σ : ℂ) := sum_bform_self_eq_re hσ N.d
  rw [act, Matrix.det_fin_two_of, bform_cross_of_det_zero hdet, ha, hb, hc, hd]
  push_cast
  ring

theorem masses_nonneg {σ : Matrix (Fin 2) (Fin 2) ℂ} (hσ : σ.PosSemidef) :
    0 ≤ N.mx σ ∧ 0 ≤ N.my σ ∧ 0 ≤ N.mz σ ∧ 0 ≤ N.mw σ :=
  ⟨bform_self_re_nonneg hσ _, Finset.sum_nonneg fun _ _ => bform_self_re_nonneg hσ _,
    bform_self_re_nonneg hσ _, Finset.sum_nonneg fun _ _ => bform_self_re_nonneg hσ _⟩

/-- On a singular state the output has the entropy of the scalar comparison matrix. -/
theorem entropy_act_of_det_zero {σ : Matrix (Fin 2) (Fin 2) ℂ} (hσ : σ.PosSemidef)
    (hdet : σ.det = 0) :
    OpenAIEntropy.entropy (N.act σ) =
      OpenAIEntropy.entropy (tc4ScalarMatrix (N.mx σ) (N.my σ) (N.mz σ) (N.mw σ)) := by
  obtain ⟨hx, -, hz, -⟩ := N.masses_nonneg hσ
  apply entropy_eq_of_trace_det (N.act_isHermitian hσ.isHermitian)
    (tc4ScalarMatrix_isHermitian _ _ _ _)
  · rw [N.act_trace hσ.isHermitian]
    simp [tc4ScalarMatrix, Matrix.trace_fin_two]
    ring
  · rw [N.act_det_of_det_zero hσ.isHermitian hdet]
    simp only [tc4ScalarMatrix, Matrix.det_fin_two_of]
    rw [← Complex.ofReal_mul (Real.sqrt _), Real.mul_self_sqrt (mul_nonneg hx hz)]
    push_cast
    ring

/-- The single-channel bound: a two-member ensemble with average `ρ` whose average output
entropy is at most the entropy of the scalar comparison matrix at `ρ`. -/
theorem scalar_bound {ρ : Matrix (Fin 2) (Fin 2) ℂ} (hρ : OpenAIEntropy.IsState ρ) :
    ∃ (p : ℝ) (σ₁ σ₂ : Matrix (Fin 2) (Fin 2) ℂ), 0 ≤ p ∧ p ≤ 1 ∧
      OpenAIEntropy.IsState σ₁ ∧ OpenAIEntropy.IsState σ₂ ∧ ρ = p • σ₁ + (1 - p) • σ₂ ∧
      p * OpenAIEntropy.entropy (N.act σ₁) + (1 - p) * OpenAIEntropy.entropy (N.act σ₂) ≤
        OpenAIEntropy.entropy (tc4ScalarMatrix (N.mx ρ) (N.my ρ) (N.mz ρ) (N.mw ρ)) := by
  obtain ⟨p, σ₁, σ₂, hp0, hp1, h₁, h₂, hd₁, hd₂, hmix, ha₁, ha₂, hc₁, hc₂⟩ :=
    exists_two_expectation_split hρ N.a N.c
  refine ⟨p, σ₁, σ₂, hp0, hp1, h₁, h₂, hmix, ?_⟩
  rw [N.entropy_act_of_det_zero h₁.1 hd₁, N.entropy_act_of_det_zero h₂.1 hd₂]
  have hx₁ : N.mx σ₁ = N.mx ρ := by simp only [mx, ha₁]
  have hx₂ : N.mx σ₂ = N.mx ρ := by simp only [mx, ha₂]
  have hz₁ : N.mz σ₁ = N.mz ρ := by simp only [mz, hc₁]
  have hz₂ : N.mz σ₂ = N.mz ρ := by simp only [mz, hc₂]
  have hy : N.my ρ = p * N.my σ₁ + (1 - p) * N.my σ₂ := by
    simp only [my, hmix, bform_mix_re, Finset.sum_add_distrib, Finset.mul_sum]
  have hw : N.mw ρ = p * N.mw σ₁ + (1 - p) * N.mw σ₂ := by
    simp only [mw, hmix, bform_mix_re, Finset.sum_add_distrib, Finset.mul_sum]
  obtain ⟨-, hy₁, -, hw₁⟩ := N.masses_nonneg h₁.1
  obtain ⟨-, hy₂, -, hw₂⟩ := N.masses_nonneg h₂.1
  obtain ⟨hx, -, hz, -⟩ := N.masses_nonneg hρ.1
  have hT : tc4ScalarMatrix (N.mx ρ) (N.my ρ) (N.mz ρ) (N.mw ρ) =
      p • tc4ScalarMatrix (N.mx ρ) (N.my σ₁) (N.mz ρ) (N.mw σ₁) +
        (1 - p) • tc4ScalarMatrix (N.mx ρ) (N.my σ₂) (N.mz ρ) (N.mw σ₂) := by
    rw [hy, hw]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [tc4ScalarMatrix, Complex.real_smul] <;> ring
  rw [hx₁, hx₂, hz₁, hz₂, hT]
  exact OpenAIEntropy.concaveOn_entropy.2 (tc4ScalarMatrix_posSemidef _ _ _ _ hx hy₁ hz hw₁)
    (tc4ScalarMatrix_posSemidef _ _ _ _ hx hy₂ hz hw₂) hp0 (by linarith) (by ring)

end QubitNormalForm

end normalForm

end QubitAdditivity
