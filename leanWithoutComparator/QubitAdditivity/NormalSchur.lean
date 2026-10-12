import QubitAdditivity.NormalForm
import Mathlib.Analysis.Matrix.Hermitian

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix
open scoped Matrix ComplexOrder MatrixOrder

namespace QubitAdditivity.NormalSchur

@[reducible] local instance matrixHMul {a b c : Type*} [Fintype b] :
    HMul (Matrix a b ℂ) (Matrix b c ℂ) (Matrix a c ℂ) :=
  Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

def vectorColumn (v : n → ℂ) : Matrix n (Fin 1) ℂ := fun i _ => v i

def scalarMatrix (d : ℝ) : Matrix (Fin 1) (Fin 1) ℂ := fun _ _ => (d : ℂ)

def outerM (v : n → ℂ) : Matrix n n ℂ := Matrix.vecMulVec v (star v)

def inverseMass (P : Matrix n n ℂ) (a : n → ℂ) : ℝ := (star a ⬝ᵥ P⁻¹ *ᵥ a).re

theorem inverseMass_pos {P : Matrix n n ℂ} (hP : P.PosDef) {a : n → ℂ} (ha : a ≠ 0) :
    0 < inverseMass P a := (Complex.pos_iff.mp (hP.inv.dotProduct_mulVec_pos ha)).1

theorem inverseMass_cast {P : Matrix n n ℂ} (hP : P.PosDef) (a : n → ℂ) :
    (inverseMass P a : ℂ) = star a ⬝ᵥ P⁻¹ *ᵥ a := by
  apply Complex.ext
  · rfl
  · exact (hP.inv.1.im_star_dotProduct_mulVec_self a).symm

theorem scalarMatrix_posDef {d : ℝ} (hd : 0 < d) : (scalarMatrix d).PosDef := by
  have hp : (d • (1 : Matrix (Fin 1) (Fin 1) ℂ)).PosDef :=
    Matrix.PosDef.one.smul (α := ℝ) hd
  have he : scalarMatrix d = d • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [scalarMatrix,Matrix.one_apply,Complex.real_smul]
  rw [he]
  exact hp

theorem scalarMatrix_inv {d : ℝ} (hd : d ≠ 0) : (scalarMatrix d)⁻¹ = scalarMatrix d⁻¹ := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j
  simp [scalarMatrix,Matrix.mul_apply,Fin.sum_univ_one,Matrix.one_apply,
    Complex.ofReal_ne_zero.mpr hd]

theorem column_sandwich {P : Matrix n n ℂ} (hP : P.PosDef) (a : n → ℂ) :
    (vectorColumn a)ᴴ*P⁻¹*vectorColumn a = scalarMatrix (inverseMass P a) := by
  ext i j
  fin_cases i <;> fin_cases j
  change (∑ j, (∑ i, star (a i)*P⁻¹ i j)*a j) = (inverseMass P a : ℂ)
  rw [inverseMass_cast hP a]
  simp only [Matrix.mulVec,dotProduct,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.star_apply]
  ring

theorem column_scalar_sandwich (a : n → ℂ) (d : ℝ) :
    vectorColumn a*scalarMatrix d*(vectorColumn a)ᴴ = d • outerM a := by
  ext i j
  simp [vectorColumn,scalarMatrix,outerM,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Fin.sum_univ_one,Matrix.vecMulVec_apply,Complex.real_smul]
  ring

/-- Two Schur complements supply the rank-one subtraction bound. -/
theorem left_residual_posSemidef {P : Matrix n n ℂ} (hP : P.PosDef)
    {a : n → ℂ} (ha : a ≠ 0) : (P-(inverseMass P a)⁻¹ • outerM a).PosSemidef := by
  letI := hP.isUnit.invertible
  have hd := inverseMass_pos hP ha
  have hD := scalarMatrix_posDef hd
  have hb : (Matrix.fromBlocks P (vectorColumn a) (vectorColumn a)ᴴ
      (scalarMatrix (inverseMass P a))).PosSemidef := by
    apply (Matrix.PosDef.fromBlocks₁₁ (vectorColumn a) (scalarMatrix (inverseMass P a)) hP).mpr
    rw [column_sandwich hP a,sub_self]
    exact Matrix.PosSemidef.zero
  letI := hD.isUnit.invertible
  have hi := (Matrix.PosDef.fromBlocks₂₂ P (vectorColumn a) hD).mp hb
  rw [scalarMatrix_inv hd.ne',column_scalar_sandwich] at hi
  exact hi

/-- A rank-one cross block has a scalar inverse-Gram Schur term. -/
theorem outer_sandwich {P : Matrix n n ℂ} (hP : P.PosDef) (a : n → ℂ) (c : m → ℂ) :
    Matrix.vecMulVec c (star a)*P⁻¹*(Matrix.vecMulVec c (star a))ᴴ = inverseMass P a • outerM c := by
  rw [Matrix.conjTranspose_vecMulVec,star_star,Matrix.vecMulVec_mul,Matrix.vecMulVec_mul_vecMulVec,
    ← Matrix.dotProduct_mulVec,← inverseMass_cast hP a]
  ext i j
  simp [outerM,Matrix.vecMulVec_apply,Complex.real_smul]
  ring

theorem right_residual_posSemidef {P : Matrix n n ℂ} {Q : Matrix m m ℂ}
    (hP : P.PosDef) (a : n → ℂ) (c : m → ℂ)
    (hblock : (Matrix.fromBlocks P (Matrix.vecMulVec a (star c)) (Matrix.vecMulVec c (star a)) Q).PosSemidef) :
    (Q-inverseMass P a • outerM c).PosSemidef := by
  letI := hP.isUnit.invertible
  have hb : (Matrix.fromBlocks P (Matrix.vecMulVec a (star c))
      (Matrix.vecMulVec a (star c))ᴴ Q).PosSemidef := by
    simpa only [Matrix.conjTranspose_vecMulVec,star_star] using hblock
  have hi := (Matrix.PosDef.fromBlocks₁₁ (Matrix.vecMulVec a (star c)) Q hP).mp hb
  have he : Matrix.vecMulVec c (star a)*P⁻¹*Matrix.vecMulVec a (star c) =
      inverseMass P a • outerM c := by
    simpa only [Matrix.conjTranspose_vecMulVec,star_star] using outer_sandwich hP a c
  simpa only [Matrix.conjTranspose_vecMulVec,star_star,he] using hi

theorem outerM_smul (a : n → ℂ) (t : ℝ) : outerM (t • a) = t^2 • outerM a := by
  ext i j
  simp [outerM,Matrix.vecMulVec_apply,Complex.real_smul,pow_two] <;> ring

theorem cross_scaled_inverse_sqrt {d : ℝ} (hd : 0 < d) (a : n → ℂ) (c : m → ℂ) :
    Matrix.vecMulVec (Real.sqrt d • c) (star ((Real.sqrt d)⁻¹ • a)) = Matrix.vecMulVec c (star a) := by
  have hs : (Real.sqrt d : ℂ)*((Real.sqrt d)⁻¹ : ℝ) = 1 := by
    rw [← Complex.ofReal_mul,mul_inv_cancel₀ (Real.sqrt_pos.mpr hd).ne']
    rfl
  ext i j
  simp only [Matrix.vecMulVec_apply,Pi.smul_apply,Pi.star_apply,Complex.real_smul]
  rw [star_mul]
  simp only [Complex.star_def,Complex.conj_ofReal]
  calc
    ((Real.sqrt d : ℂ)*c i)*(star (a j)*((Real.sqrt d)⁻¹ : ℝ)) =
        ((Real.sqrt d : ℂ)*((Real.sqrt d)⁻¹ : ℝ))*(c i*star (a j)) := by ring
    _ = c i*star (a j) := by rw [hs,one_mul]

/-- One positive diagonal block suffices to extract a common rank-one branch. -/
theorem exists_common_branch_of_posDef {P : Matrix n n ℂ} {Q : Matrix m m ℂ}
    (hP : P.PosDef) {a : n → ℂ} (ha : a ≠ 0) (c : m → ℂ)
    (hblock : (Matrix.fromBlocks P (Matrix.vecMulVec a (star c)) (Matrix.vecMulVec c (star a)) Q).PosSemidef) :
    ∃ u : n → ℂ, ∃ v : m → ℂ,
      Matrix.vecMulVec v (star u) = Matrix.vecMulVec c (star a) ∧
      (P-outerM u).PosSemidef ∧ (Q-outerM v).PosSemidef := by
  let d := inverseMass P a
  have hd : 0 < d := inverseMass_pos hP ha
  refine ⟨(Real.sqrt d)⁻¹ • a,Real.sqrt d • c,cross_scaled_inverse_sqrt hd a c,?_,?_⟩
  · rw [outerM_smul,inv_pow,Real.sq_sqrt hd.le]
    exact left_residual_posSemidef hP ha
  · rw [outerM_smul,Real.sq_sqrt hd.le]
    exact right_residual_posSemidef hP a c hblock

end QubitAdditivity.NormalSchur
