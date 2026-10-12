import QubitAdditivity.PureInput
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Existence of the one-common-branch normal form for every qubit channel.

An output rotation with first row `(s, t)` turns the off-diagonal dual image into
`s² Q + s t (R - P) - t² Qᴴ`. Its determinant is a binary quartic, which has a unit zero by
the fundamental theorem of algebra; then the off-diagonal block has rank at most one. -/

noncomputable section
open scoped Matrix BigOperators ComplexOrder Kronecker MatrixMap
open Matrix Polynomial

namespace QubitAdditivity

section rotation

/-- The output rotation with first row `(s, t)`. -/
def rotU (s t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![s, t; -star t, star s]

theorem rotU_mul_conjTranspose {s t : ℂ} (h : Complex.normSq s + Complex.normSq t = 1) :
    rotU s t * (rotU s t)ᴴ = 1 := by
  have h' : s * (starRingEnd ℂ) s + t * (starRingEnd ℂ) t = 1 := by
    rw [Complex.mul_conj, Complex.mul_conj]
    exact_mod_cast h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotU, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Complex.star_def] <;>
    first | (solve | ring) | linear_combination h'

theorem rotU_mem_unitary {s t : ℂ} (h : Complex.normSq s + Complex.normSq t = 1) :
    rotU s t ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  exact rotU_mul_conjTranspose h

theorem rotU_mul_rows (s t : ℂ) (p q : Fin 2 → ℂ) :
    rotU s t * QubitNormalForm.rows p q =
      QubitNormalForm.rows (star s • p + star t • q) (-t • p + s • q) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotU, QubitNormalForm.rows, Matrix.mul_apply, Fin.sum_univ_two]

/-- `∑ₖ pₖ pₖᴴ`. -/
def massMat {κ : Type*} [Fintype κ] (p : κ → Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ k, vecMulVec (p k) (star (p k))

/-- `∑ₖ qₖ pₖᴴ`, the off-diagonal dual image of a Kraus family with rows `pₖᴴ`, `qₖᴴ`. -/
def crossMat {κ : Type*} [Fintype κ] (p q : κ → Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ∑ k, vecMulVec (q k) (star (p k))

theorem crossMat_rot {κ : Type*} [Fintype κ] (s t : ℂ) (p q : κ → Fin 2 → ℂ) :
    crossMat (fun k => star s • p k + star t • q k) (fun k => -t • p k + s • q k) =
      s ^ 2 • crossMat p q + (s * t) • (massMat q - massMat p) +
        (-t ^ 2) • (crossMat p q)ᴴ := by
  ext i j
  simp only [crossMat, massMat, Matrix.sum_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.conjTranspose_apply, vecMulVec_apply, Pi.add_apply,
    Pi.smul_apply, Pi.star_apply, star_add, star_smul, star_star, star_sum,
    star_mul', smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

end rotation

section quartic

/-- The determinant of `z² A + z B + C` as an explicit quartic. -/
def quarticPoly (A B C : Matrix (Fin 2) (Fin 2) ℂ) : ℂ[X] :=
  Polynomial.C (A 0 0 * A 1 1 - A 0 1 * A 1 0) * X ^ 4 +
  Polynomial.C (A 0 0 * B 1 1 + B 0 0 * A 1 1 - A 0 1 * B 1 0 - B 0 1 * A 1 0) * X ^ 3 +
  Polynomial.C (A 0 0 * C 1 1 + B 0 0 * B 1 1 + C 0 0 * A 1 1 - A 0 1 * C 1 0 -
    B 0 1 * B 1 0 - C 0 1 * A 1 0) * X ^ 2 +
  Polynomial.C (B 0 0 * C 1 1 + C 0 0 * B 1 1 - B 0 1 * C 1 0 - C 0 1 * B 1 0) * X +
  Polynomial.C (C 0 0 * C 1 1 - C 0 1 * C 1 0)

theorem eval_quarticPoly (A B C : Matrix (Fin 2) (Fin 2) ℂ) (z : ℂ) :
    (quarticPoly A B C).eval z = (z ^ 2 • A + z • B + C).det := by
  simp only [quarticPoly, eval_add, eval_mul, eval_C, eval_pow, eval_X, Matrix.det_fin_two,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem coeff_four_quarticPoly (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    (quarticPoly A B C).coeff 4 = A.det := by
  simp only [quarticPoly, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C]
  norm_num [Matrix.det_fin_two]

/-- A binary quartic `det (s² A + s t B + t² C)` has a zero on the unit sphere. -/
theorem exists_unit_zero (A B C : Matrix (Fin 2) (Fin 2) ℂ) :
    ∃ s t : ℂ, Complex.normSq s + Complex.normSq t = 1 ∧
      (s ^ 2 • A + (s * t) • B + t ^ 2 • C).det = 0 := by
  by_cases hdeg : (quarticPoly A B C).degree = 0
  · refine ⟨1, 0, by simp, ?_⟩
    have h4 : (quarticPoly A B C).coeff 4 = 0 :=
      coeff_eq_zero_of_degree_lt (by rw [hdeg]; norm_num)
    rw [coeff_four_quarticPoly] at h4
    simpa using h4
  · obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (quarticPoly A B C) hdeg
    rw [IsRoot, eval_quarticPoly] at hz
    set r := Complex.normSq z + 1 with hr
    have hrpos : 0 < r := add_pos_of_nonneg_of_pos (Complex.normSq_nonneg z) one_pos
    set l : ℝ := 1 / Real.sqrt r
    have hl2 : l ^ 2 * r = 1 := by
      simp only [l, div_pow, one_pow, Real.sq_sqrt hrpos.le]
      field_simp
    refine ⟨(l : ℂ) * z, (l : ℂ), ?_, ?_⟩
    · simp only [Complex.normSq_mul, Complex.normSq_ofReal]
      nlinarith [hl2]
    · have hM : ((l : ℂ) * z) ^ 2 • A + ((l : ℂ) * z * (l : ℂ)) • B + (l : ℂ) ^ 2 • C =
          ((l : ℂ) ^ 2) • (z ^ 2 • A + z • B + C) := by
        ext i j
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        ring
      rw [hM, Matrix.det_smul, hz, mul_zero]

end quartic

section outer

/-- A singular 2×2 matrix is an outer product. -/
theorem exists_outer_of_det_zero {Q : Matrix (Fin 2) (Fin 2) ℂ} (h : Q.det = 0) :
    ∃ x y : Fin 2 → ℂ, Q = vecMulVec x (star y) := by
  rw [Matrix.det_fin_two] at h
  by_cases h00 : Q 0 0 = 0
  · by_cases h01 : Q 0 1 = 0
    · refine ⟨![0, 1], ![star (Q 1 0), star (Q 1 1)], ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [vecMulVec_apply, h00, h01]
    · have h10 : Q 1 0 = 0 := by
        rw [h00, zero_mul, zero_sub, neg_eq_zero] at h
        exact (mul_eq_zero.mp h).resolve_left h01
      refine ⟨![1, Q 1 1 / Q 0 1], ![star (Q 0 0), star (Q 0 1)], ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [vecMulVec_apply, h00, h10] <;> field_simp
  · refine ⟨![1, Q 1 0 / Q 0 0], ![star (Q 0 0), star (Q 0 1)], ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [vecMulVec_apply] <;> field_simp <;>
      linear_combination h

end outer

section rotatedOuter

/-- A normalized output rotation makes the off-diagonal Gram block singular. -/
theorem exists_rotation_cross_det_zero {κ : Type*} [Fintype κ] (p q : κ → Fin 2 → ℂ) :
    ∃ s t : ℂ, Complex.normSq s+Complex.normSq t = 1 ∧
      (crossMat (fun k => star s • p k+star t • q k) (fun k => -t • p k+s • q k)).det = 0 := by
  obtain ⟨s,t,hst,hdet⟩ := exists_unit_zero (crossMat p q) (massMat q-massMat p) (-(crossMat p q)ᴴ)
  refine ⟨s,t,hst,?_⟩
  rw [crossMat_rot]
  simpa only [smul_neg,neg_smul] using hdet

/-- The rotated cross block is an explicit outer product, without a rank predicate. -/
theorem exists_rotated_outer {κ : Type*} [Fintype κ] (p q : κ → Fin 2 → ℂ) :
    ∃ s t : ℂ, ∃ x y : Fin 2 → ℂ, Complex.normSq s+Complex.normSq t = 1 ∧
      crossMat (fun k => star s • p k+star t • q k) (fun k => -t • p k+s • q k) =
        vecMulVec x (star y) := by
  obtain ⟨s,t,hst,hdet⟩ := exists_rotation_cross_det_zero p q
  obtain ⟨x,y,hxy⟩ := exists_outer_of_det_zero hdet
  exact ⟨s,t,x,y,hst,hxy⟩

end rotatedOuter

end QubitAdditivity
