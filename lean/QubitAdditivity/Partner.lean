import QubitAdditivity.UpperBound
import QubitAdditivity.TwoExpectation

/-! Kraus forms for the partner side of the pure-input inequality: Kraus families of arbitrary
channels, the column matrix of a Kraus family on a vector, and the normal-form qubit channel as
a CPTP map. -/

noncomputable section
open scoped Matrix BigOperators ComplexOrder Kronecker MatrixMap
open Matrix

namespace QubitAdditivity

section kraus

variable {dIn dOut : Type*} [Fintype dIn] [Fintype dOut] [DecidableEq dIn]

/-- Trace preservation of a Kraus map forces `∑ Kᴴ K = 1`. The proof is that of the private
Physlib lemma `CPTPMap.kraus_sum_eq_one_of_TP` (Apache-2.0, vendored commit a4ef461). -/
theorem kraus_sum_eq_one_of_TP {κ : Type*} [Fintype κ] {K : κ → Matrix dOut dIn ℂ}
    (hTP : (MatrixMap.of_kraus K K).IsTracePreserving) : ∑ k, (K k)ᴴ * K k = 1 := by
  ext1 i j
  have := hTP (Matrix.of fun x y ↦ if x = j then if y = i then 1 else 0 else 0)
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.of_apply, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte] at this
  convert this using 1
  · simp [MatrixMap.of_kraus, Matrix.sum_apply, Matrix.mul_apply]
    rw [Finset.sum_comm]
    congr! 2
    ring
  · simp [Matrix.one_apply, eq_comm]

/-- Every channel has a Kraus family with `∑ Kᴴ K = 1`. -/
theorem exists_kraus_family [DecidableEq dOut] (Ω : CPTPMap dIn dOut) :
    ∃ W : (dOut × dIn) → Matrix dOut dIn ℂ,
      Ω.map = MatrixMap.of_kraus W W ∧ ∑ k, (W k)ᴴ * W k = 1 := by
  obtain ⟨W, hW⟩ := MatrixMap.IsCompletelyPositive.exists_kraus Ω.map Ω.cp
  refine ⟨W, hW, kraus_sum_eq_one_of_TP ?_⟩
  rw [← hW]
  exact Ω.TP

/-- The column matrix of a Kraus family on a vector: column `k` is `K k *ᵥ ψ`. -/
def krausColumns {κ : Type*} (K : κ → Matrix dOut dIn ℂ) (ψ : dIn → ℂ) : Matrix dOut κ ℂ :=
  Matrix.of fun o k => (K k *ᵥ ψ) o

theorem of_kraus_vecMulVec {κ : Type*} [Fintype κ] (K : κ → Matrix dOut dIn ℂ)
    (ψ : dIn → ℂ) :
    MatrixMap.of_kraus K K (vecMulVec ψ (star ψ)) = krausColumns K ψ * (krausColumns K ψ)ᴴ := by
  ext o p
  simp only [MatrixMap.of_kraus, LinearMap.coe_sum, Finset.sum_apply, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.sum_apply, Matrix.mul_apply, krausColumns, Matrix.of_apply,
    Matrix.conjTranspose_apply, vecMulVec_apply, mulVec, dotProduct, Pi.star_apply, star_sum,
    star_mul']
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  ring

end kraus

namespace QubitNormalForm

variable {J K : Type*} [Fintype J] [Fintype K] (N : QubitNormalForm J K)

/-- The 2×2 matrix with rows `star u` and `star v`. -/
def rows (u v : Fin 2 → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![star (u 0), star (u 1); star (v 0), star (v 1)]

/-- The Kraus family of the normal form: the common branch, then the branches reaching only
output 0, then those reaching only output 1. -/
def kraus : Unit ⊕ (J ⊕ K) → Matrix (Fin 2) (Fin 2) ℂ
  | .inl _ => rows N.a N.c
  | .inr (.inl j) => rows (N.b j) 0
  | .inr (.inr k) => rows 0 (N.d k)

/-- Trace preservation of the normal form. -/
def Complete : Prop := ∑ f, (N.kraus f)ᴴ * N.kraus f = 1

theorem rows_conj (u v : Fin 2 → ℂ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    rows u v * ρ * (rows u v)ᴴ = !![bform ρ u u, bform ρ u v; bform ρ v u, bform ρ v v] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rows, bform, Matrix.mul_apply, Fin.sum_univ_two, dotProduct, mulVec, vecMul,
      Matrix.conjTranspose_apply] <;> ring

theorem act_eq_of_kraus (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    MatrixMap.of_kraus N.kraus N.kraus ρ = N.act ρ := by
  simp only [MatrixMap.of_kraus, LinearMap.coe_sum, Finset.sum_apply, LinearMap.coe_mk,
    AddHom.coe_mk, Fintype.sum_sum_type, Fintype.univ_punit, Finset.sum_singleton, kraus,
    rows_conj]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [act, Matrix.sum_apply, bform, dotProduct, mulVec, Fin.sum_univ_two]

/-- The normal form as a channel. -/
def toCPTP (h : N.Complete) : CPTPMap (Fin 2) (Fin 2) :=
  CPTPMap.of_kraus_CPTPMap N.kraus h

theorem toCPTP_m (h : N.Complete) (ρ : MState (Fin 2)) : (N.toCPTP h ρ).m = N.act ρ.m := by
  rw [CPTPMap.mat_coe_eq_apply_mat]
  exact N.act_eq_of_kraus ρ.m

end QubitNormalForm

section joint

/-- The density matrix of a pure state. -/
theorem pure_m {d : Type*} [Fintype d] [DecidableEq d] (ψ : Ket d) :
    (MState.pure ψ).m = vecMulVec (ψ : d → ℂ) (star (ψ : d → ℂ)) := by
  ext i j
  change vecMulVec (ψ : d → ℂ) ((ψ : Bra d) : d → ℂ) i j = _
  rw [vecMulVec_apply, vecMulVec_apply, Bra.eq_conj]
  rfl

/-- The branch vector `(⟨u| ⊗ I) ψ`. -/
def branch {dB : Type*} [Fintype dB] (u : Fin 2 → ℂ) (ψ : Fin 2 × dB → ℂ) : dB → ℂ :=
  fun j => ∑ i, star (u i) * ψ (i, j)

/-- Row equivalence `Fin 2 × α ≃ α ⊕ α`. -/
def rowEquiv (α : Type*) : Fin 2 × α ≃ α ⊕ α where
  toFun x := if x.1 = 0 then Sum.inl x.2 else Sum.inr x.2
  invFun := Sum.elim (fun a => (0, a)) (fun a => (1, a))
  left_inv := by
    rintro ⟨i, a⟩
    fin_cases i <;> rfl
  right_inv := by
    rintro (a | a) <;> rfl

/-- Column equivalence for the joint Kraus family. -/
def colEquiv (J K κ : Type*) : (Unit ⊕ (J ⊕ K)) × κ ≃ (Unit × κ) ⊕ ((J × κ) ⊕ (K × κ)) :=
  (Equiv.sumProdDistrib _ _ _).trans
    (Equiv.sumCongr (Equiv.refl _) (Equiv.sumProdDistrib _ _ _))

/-- The output block of a family of branch vectors `η i`: column `(i, μ)` is `W μ *ᵥ η i`. -/
def branchBlock {I dB eB κ : Type*} [Fintype dB] (W : κ → Matrix eB dB ℂ) (η : I → dB → ℂ) :
    Matrix eB (I × κ) ℂ :=
  Matrix.of fun o x => (W x.2 *ᵥ η x.1) o

namespace QubitNormalForm

variable {J K : Type*} [Fintype J] [Fintype K] (N : QubitNormalForm J K)
variable {dB eB κ : Type*} [Fintype dB] [DecidableEq dB] [Fintype eB] [DecidableEq eB]
variable [Fintype κ]

theorem rows_zero (u v : Fin 2 → ℂ) (i : Fin 2) : rows u v 0 i = star (u i) := by
  fin_cases i <;> rfl

theorem rows_one (u v : Fin 2 → ℂ) (i : Fin 2) : rows u v 1 i = star (v i) := by
  fin_cases i <;> rfl

/-- The four output blocks of TC4 for the input `ψ`. -/
def blockA (W : κ → Matrix eB dB ℂ) (ψ : Fin 2 × dB → ℂ) : Matrix eB (Unit × κ) ℂ :=
  branchBlock W fun _ : Unit => branch N.a ψ

def blockB (W : κ → Matrix eB dB ℂ) (ψ : Fin 2 × dB → ℂ) : Matrix eB (J × κ) ℂ :=
  branchBlock W fun j => branch (N.b j) ψ

def blockC (W : κ → Matrix eB dB ℂ) (ψ : Fin 2 × dB → ℂ) : Matrix eB (Unit × κ) ℂ :=
  branchBlock W fun _ : Unit => branch N.c ψ

def blockD (W : κ → Matrix eB dB ℂ) (ψ : Fin 2 × dB → ℂ) : Matrix eB (K × κ) ℂ :=
  branchBlock W fun k => branch (N.d k) ψ

/-- The joint Kraus family of the normal form and `W`. -/
def jointKraus (W : κ → Matrix eB dB ℂ) :
    (Unit ⊕ (J ⊕ K)) × κ → Matrix (Fin 2 × eB) (Fin 2 × dB) ℂ :=
  fun x => N.kraus x.1 ⊗ₖ W x.2

/-- The four-block matrix of TC4 at the input `ψ`. -/
def tc4At (W : κ → Matrix eB dB ℂ) (ψ : Fin 2 × dB → ℂ) :
    Matrix (eB ⊕ eB) ((Unit × κ) ⊕ ((J × κ) ⊕ (K × κ))) ℂ :=
  tc4Matrix (N.blockA W ψ) (N.blockB W ψ) (N.blockC W ψ) (N.blockD W ψ)

/-- The joint column matrix is the four-block matrix of TC4, up to relabelling. -/
theorem jointColumns_eq (W : κ → Matrix eB dB ℂ) (ψ : Fin 2 × dB → ℂ) :
    krausColumns (N.jointKraus W) ψ =
      (N.tc4At W ψ).submatrix (rowEquiv eB) (colEquiv J K κ) := by
  ext ⟨o, o'⟩ ⟨f, μ⟩
  fin_cases o <;> rcases f with ⟨⟩ | j | k <;>
    simp [krausColumns, jointKraus, tc4At, tc4Matrix, rowEquiv, colEquiv, blockA, blockB,
      blockC, blockD, branchBlock, branch, kraus, rows_zero, rows_one, mulVec, dotProduct,
      Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Finset.mul_sum]
  all_goals
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem jointKraus_eq_kron (W : κ → Matrix eB dB ℂ) :
    MatrixMap.of_kraus N.kraus N.kraus ⊗ₖₘ MatrixMap.of_kraus W W =
      MatrixMap.of_kraus (N.jointKraus W) (N.jointKraus W) :=
  MatrixMap.kron_of_kraus N.kraus W

/-- The joint output of the normal form and a partner channel on a pure input is the Gram
matrix of the four-block matrix, up to relabelling the rows. -/
theorem joint_output_m (h : N.Complete) (Ω : CPTPMap dB eB) (W : κ → Matrix eB dB ℂ)
    (hW : Ω.map = MatrixMap.of_kraus W W) (ψ : Ket (Fin 2 × dB)) :
    ((N.toCPTP h ⊗ᶜᵖ Ω) (MState.pure ψ)).m =
      (N.tc4At W ψ * (N.tc4At W ψ).conjTranspose).submatrix (rowEquiv eB) (rowEquiv eB) := by
  rw [CPTPMap.mat_coe_eq_apply_mat]
  change (MatrixMap.of_kraus N.kraus N.kraus ⊗ₖₘ Ω.map) (MState.pure ψ).m = _
  rw [hW, N.jointKraus_eq_kron, pure_m, of_kraus_vecMulVec, N.jointColumns_eq,
    Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]

end QubitNormalForm

end joint

section branchBlock

variable {I dB eB κ : Type*} [Fintype I] [Fintype dB] [DecidableEq dB] [Fintype eB]
variable [DecidableEq eB] [Fintype κ]

/-- Squared norm of a vector. -/
def vecMass (η : dB → ℂ) : ℝ := ∑ j, Complex.normSq (η j)

theorem vecMass_nonneg (η : dB → ℂ) : 0 ≤ vecMass η :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- The pure state of a nonzero vector; the default state for the zero vector. -/
def vecState [Nonempty dB] (η : dB → ℂ) : MState dB :=
  if h : ∃ x, η x ≠ 0 then MState.pure (Ket.normalize η h) else default

theorem vecMass_smul_vecState_m [Nonempty dB] (η : dB → ℂ) :
    vecMass η • (vecState η).m = vecMulVec η (star η) := by
  by_cases h : ∃ x, η x ≠ 0
  · rw [vecState, dif_pos h, pure_m]
    have hpos : 0 < vecMass η := by
      obtain ⟨x, hx⟩ := h
      exact lt_of_lt_of_le (Complex.normSq_pos.mpr hx)
        (Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (η j)) (Finset.mem_univ x))
    have hnorm : (∑ x : dB, ‖η x‖ ^ 2) = vecMass η := by
      simp [vecMass, Complex.normSq_eq_norm_sq]
    ext i j
    simp only [Matrix.smul_apply, vecMulVec_apply, Pi.star_apply, Ket.normalize, Ket.apply,
      hnorm, Complex.real_smul, star_div₀, Complex.star_def, Complex.conj_ofReal]
    have hs : (Real.sqrt (vecMass η) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr hpos).ne'
    have hsq : (Real.sqrt (vecMass η) : ℂ) * (Real.sqrt (vecMass η) : ℂ) = (vecMass η : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hpos.le]
    field_simp
    rw [← hsq]
    ring
  · have hz : η = 0 := funext fun x => by
      by_contra hx
      exact h ⟨x, hx⟩
    subst hz
    simp [vecMass]

theorem branchBlock_gram (W : κ → Matrix eB dB ℂ) (η : I → dB → ℂ) :
    branchBlock W η * (branchBlock W η)ᴴ =
      ∑ i, MatrixMap.of_kraus W W (vecMulVec (η i) (star (η i))) := by
  simp_rw [of_kraus_vecMulVec]
  ext o p
  simp [branchBlock, krausColumns, Matrix.mul_apply, Matrix.sum_apply, Fintype.sum_prod_type,
    Matrix.conjTranspose_apply]

theorem blockMass_branchBlock (W : κ → Matrix eB dB ℂ) (hW : ∑ k, (W k)ᴴ * W k = 1)
    (η : I → dB → ℂ) : blockMass (branchBlock W η) = ∑ i, vecMass (η i) := by
  have hTP : ∀ x, (MatrixMap.of_kraus W W x).trace = x.trace :=
    MatrixMap.IsTracePreserving.of_kraus_isTracePreserving W W hW
  unfold blockMass
  rw [branchBlock_gram, Matrix.trace_sum]
  simp_rw [hTP]
  simp [Matrix.trace, vecMulVec_apply, vecMass, Complex.mul_conj, Complex.re_sum]

/-- The internal term of TC4 bounds the average output entropy of the branch states. -/
theorem weightedBlockEntropy_branchBlock_ge [Nonempty dB] (Ω : CPTPMap dB eB)
    (W : κ → Matrix eB dB ℂ) (hW : Ω.map = MatrixMap.of_kraus W W) (η : I → dB → ℂ) :
    ∑ i, vecMass (η i) * Sᵥₙ (Ω (vecState (η i))) ≤ weightedBlockEntropy (branchBlock W η) := by
  have hW1 : ∑ k, (W k)ᴴ * W k = 1 := kraus_sum_eq_one_of_TP (hW ▸ Ω.TP)
  have hmass := blockMass_branchBlock W hW1 η
  have hgram : branchBlock W η * (branchBlock W η)ᴴ =
      ∑ i, vecMass (η i) • (Ω (vecState (η i))).m := by
    rw [branchBlock_gram]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← vecMass_smul_vecState_m, CPTPMap.mat_coe_eq_apply_mat, hW,
      (MatrixMap.of_kraus W W).map_smul_of_tower]
  simp only [entropy_eq_openai]
  unfold weightedBlockEntropy
  rw [hgram, hmass]
  set M := ∑ i, vecMass (η i)
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => vecMass_nonneg (η i)
  rcases hM0.lt_or_eq with hM | hM
  · have hMne : M ≠ 0 := hM.ne'
    have hJ := OpenAIEntropy.concaveOn_entropy.le_map_sum (t := Finset.univ)
      (w := fun i => vecMass (η i) / M) (p := fun i => (Ω (vecState (η i))).m)
      (fun i _ => div_nonneg (vecMass_nonneg _) hM.le)
      (by rw [← Finset.sum_div]; exact div_self hM.ne')
      (fun i _ => (Ω (vecState (η i))).psd)
    have hsum : M⁻¹ • ∑ i, vecMass (η i) • (Ω (vecState (η i))).m =
        ∑ i, (vecMass (η i) / M) • (Ω (vecState (η i))).m := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, div_eq_inv_mul]
    rw [hsum]
    calc ∑ i, vecMass (η i) * OpenAIEntropy.entropy (Ω (vecState (η i))).m
        = M * ∑ i, (vecMass (η i) / M) • OpenAIEntropy.entropy (Ω (vecState (η i))).m := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_eq_mul]
          field_simp
      _ ≤ M * OpenAIEntropy.entropy (∑ i, (vecMass (η i) / M) • (Ω (vecState (η i))).m) :=
          mul_le_mul_of_nonneg_left hJ hM.le
  · have hzero (i : I) : vecMass (η i) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => vecMass_nonneg (η j)).mp hM.symm i
        (Finset.mem_univ i)
    have hMz : M = 0 := hM.symm
    rw [hMz]
    simp [hzero]

end branchBlock

section marginals

variable {dB : Type*} [Fintype dB] [DecidableEq dB]

theorem traceRight_pure_m (ψ : Ket (Fin 2 × dB)) :
    (MState.pure ψ).traceRight.m = Matrix.of fun i k => ∑ j, ψ (i, j) * star (ψ (k, j)) := by
  change (MState.pure ψ).m.traceRight = _
  rw [pure_m]
  ext i k
  simp [Matrix.traceRight, vecMulVec_apply]

theorem traceLeft_pure_m (ψ : Ket (Fin 2 × dB)) :
    (MState.pure ψ).traceLeft.m = Matrix.of fun x y => ∑ i, ψ (i, x) * star (ψ (i, y)) := by
  change (MState.pure ψ).m.traceLeft = _
  rw [pure_m]
  ext x y
  simp [Matrix.traceLeft, vecMulVec_apply]

/-- `‖(⟨u| ⊗ I) ψ‖² = ⟨u, ρ_A u⟩`. -/
theorem vecMass_branch (ψ : Ket (Fin 2 × dB)) (u : Fin 2 → ℂ) :
    vecMass (branch u ψ) = (bform (MState.pure ψ).traceRight.m u u).re := by
  have h : bform (MState.pure ψ).traceRight.m u u =
      ∑ j, branch u ψ j * star (branch u ψ j) := by
    rw [traceRight_pure_m]
    simp only [bform, dotProduct, mulVec, Matrix.of_apply, branch, Fin.sum_univ_two,
      Pi.star_apply, star_add, star_mul', star_star, Finset.mul_sum, Finset.sum_mul, mul_add,
      add_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h, vecMass, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show star (branch u ψ j) = (starRingEnd ℂ) (branch u ψ j) from rfl, Complex.mul_conj,
    Complex.ofReal_re]

/-- `∑ₗ (⟨u l| ⊗ I) ψ ((⟨u l| ⊗ I) ψ)ᴴ`, entrywise, through the matrix `∑ₗ u l (u l)ᴴ`. -/
theorem sum_branch_outer {L : Type*} [Fintype L] (u : L → Fin 2 → ℂ) (ψ : Fin 2 × dB → ℂ)
    (x y : dB) :
    ∑ l, branch (u l) ψ x * star (branch (u l) ψ y) =
      ∑ i, ∑ k, ψ (i, x) * star (ψ (k, y)) * ∑ l, u l k * star (u l i) := by
  simp only [branch, Fin.sum_univ_two, star_add, star_mul', star_star, Finset.mul_sum,
    mul_add, add_mul, Finset.sum_add_distrib]
  simp only [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

end marginals

namespace QubitNormalForm

variable {J K : Type*} [Fintype J] [Fintype K] (N : QubitNormalForm J K)

/-- Entries of the completeness relation `a a* + c c* + ∑ b b* + ∑ d d* = 1`. -/
theorem complete_entry (h : N.Complete) (k i : Fin 2) :
    N.a k * star (N.a i) + N.c k * star (N.c i) + ∑ j, N.b j k * star (N.b j i) +
      ∑ l, N.d l k * star (N.d l i) = (1 : Matrix (Fin 2) (Fin 2) ℂ) k i := by
  have hk := congrFun (congrFun h k) i
  rw [← hk]
  simp only [Matrix.sum_apply, Fintype.sum_sum_type, Fintype.univ_punit, Finset.sum_singleton,
    kraus, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, rows_zero, rows_one,
    star_star, Pi.zero_apply, star_zero, zero_mul, add_zero, zero_add]
  ring

variable {dB : Type*} [Fintype dB] [DecidableEq dB]

/-- The partner marginal: the branch vectors decompose `ρ_B`. -/
theorem traceLeft_pure_eq (h : N.Complete) (ψ : Ket (Fin 2 × dB)) :
    (MState.pure ψ).traceLeft.m =
      vecMulVec (branch N.a ψ) (star (branch N.a ψ)) +
        ∑ j, vecMulVec (branch (N.b j) ψ) (star (branch (N.b j) ψ)) +
        vecMulVec (branch N.c ψ) (star (branch N.c ψ)) +
        ∑ l, vecMulVec (branch (N.d l) ψ) (star (branch (N.d l) ψ)) := by
  rw [traceLeft_pure_m]
  ext x y
  simp only [Matrix.of_apply, Matrix.add_apply, Matrix.sum_apply, vecMulVec_apply,
    Pi.star_apply]
  have ha := sum_branch_outer (fun _ : Unit => N.a) ψ x y
  have hc := sum_branch_outer (fun _ : Unit => N.c) ψ x y
  have hb := sum_branch_outer N.b ψ x y
  have hd := sum_branch_outer N.d ψ x y
  simp only [Fintype.univ_punit, Finset.sum_singleton] at ha hc
  rw [ha, hc, hb, hd]
  simp only [Fin.sum_univ_two]
  have h00 := N.complete_entry h 0 0
  have h01 := N.complete_entry h 0 1
  have h10 := N.complete_entry h 1 0
  have h11 := N.complete_entry h 1 1
  simp only [Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at h00 h01 h10 h11
  linear_combination (-(ψ (0, x) * star (ψ (0, y)))) * h00 -
    (ψ (1, x) * star (ψ (0, y))) * h01 - (ψ (0, x) * star (ψ (1, y))) * h10 -
    (ψ (1, x) * star (ψ (1, y))) * h11

end QubitNormalForm

end QubitAdditivity
