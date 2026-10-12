import QubitAdditivity.NormalCommonBranch

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix
open scoped Matrix ComplexOrder MatrixOrder

namespace QubitAdditivity.NormalKraus
open NormalSchur NormalCommonBranch

@[reducible] local instance matrixHMul {a b c : Type*} [Fintype b] :
    HMul (Matrix a b ℂ) (Matrix b c ℂ) (Matrix a c ℂ) :=
  Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k]

/-- Column Gram expansion in raw matrices, including empty column families. -/
theorem sum_outer_columns (Y : Matrix n k ℂ) :
    (∑ j, outerM (fun i => Y i j)) = Y*Yᴴ := by
  ext i l
  simp [outerM,Matrix.sum_apply,Matrix.vecMulVec_apply,Matrix.mul_apply,Matrix.conjTranspose_apply]

/-- Every PSD matrix is a finite sum of vector outer products. -/
theorem exists_outer_decomposition {P : Matrix n n ℂ} (hP : P.PosSemidef) :
    ∃ b : n → n → ℂ, (∑ j, outerM (b j)) = P := by
  obtain ⟨Y,hY⟩ := CStarAlgebra.nonneg_iff_eq_mul_star_self.mp hP.nonneg
  refine ⟨fun j i => Y i j,?_⟩
  exact (sum_outer_columns Y).trans (by simpa only [Matrix.star_eq_conjTranspose] using hY.symm)

variable (p q : k → Fin 2 → ℂ)

/-- The row Gram blocks of a Kraus family form a PSD block matrix. -/
theorem gramBlocks_posSemidef :
    (Matrix.fromBlocks (massMat p) (crossMat q p) (crossMat p q) (massMat q)).PosSemidef := by
  have he : Matrix.fromBlocks (massMat p) (crossMat q p) (crossMat p q) (massMat q) =
      ∑ j, outerM (Sum.elim (p j) (q j)) := by
    ext i l
    cases i <;> cases l <;> simp [massMat,crossMat,outerM,Matrix.sum_apply,
      Matrix.fromBlocks,Matrix.vecMulVec_apply]
  rw [he]
  exact Matrix.posSemidef_sum Finset.univ (fun j _ => Matrix.posSemidef_vecMulVec_self_star _)

theorem crossMat_conjTranspose : (crossMat p q)ᴴ = crossMat q p := by
  simp [crossMat,Matrix.conjTranspose_sum,Matrix.conjTranspose_vecMulVec]

/-- A rank-one cross Gram block can be realized by one common branch and PSD residuals. -/
theorem exists_common_rows (a c : Fin 2 → ℂ)
    (he : crossMat p q = Matrix.vecMulVec c (star a)) :
    ∃ u v : Fin 2 → ℂ,
      Matrix.vecMulVec v (star u) = crossMat p q ∧
      (massMat p-outerM u).PosSemidef ∧ (massMat q-outerM v).PosSemidef := by
  have htop : crossMat q p = Matrix.vecMulVec a (star c) := by
    rw [← crossMat_conjTranspose p q,he,Matrix.conjTranspose_vecMulVec,star_star]
  obtain ⟨u,v,hcross,hP,hQ⟩ := exists_common_branch a c (by
    simpa only [← he,← htop] using gramBlocks_posSemidef p q)
  exact ⟨u,v,hcross.trans he.symm,hP,hQ⟩

/-- The complete row Gram data admit the one-common-branch normal form. -/
theorem exists_normal_gram (a c : Fin 2 → ℂ)
    (he : crossMat p q = Matrix.vecMulVec c (star a)) :
    ∃ N : QubitNormalForm (Fin 2) (Fin 2),
      massMat p = outerM N.a+∑ j,outerM (N.b j) ∧
      massMat q = outerM N.c+∑ j,outerM (N.d j) ∧
      crossMat p q = Matrix.vecMulVec N.c (star N.a) := by
  obtain ⟨u,v,hcross,hP,hQ⟩ := exists_common_rows p q a c he
  obtain ⟨b,hb⟩ := exists_outer_decomposition hP
  obtain ⟨d,hd⟩ := exists_outer_decomposition hQ
  refine ⟨⟨u,v,b,d⟩,?_,?_,hcross.symm⟩
  · rw [hb]
    abel
  · rw [hd]
    abel

/-- Every finite qubit row family has rotated Gram data in normal form. -/
theorem exists_rotated_normal_gram :
    ∃ s t : ℂ, ∃ N : QubitNormalForm (Fin 2) (Fin 2),
      Complex.normSq s+Complex.normSq t = 1 ∧
      massMat (fun j => star s • p j+star t • q j) = outerM N.a+∑ j,outerM (N.b j) ∧
      massMat (fun j => -t • p j+s • q j) = outerM N.c+∑ j,outerM (N.d j) ∧
      crossMat (fun j => star s • p j+star t • q j) (fun j => -t • p j+s • q j) =
        Matrix.vecMulVec N.c (star N.a) := by
  obtain ⟨s,t,x,y,hst,hxy⟩ := exists_rotated_outer p q
  obtain ⟨N,hP,hQ,hC⟩ := exists_normal_gram
    (fun j => star s • p j+star t • q j) (fun j => -t • p j+s • q j) y x hxy
  exact ⟨s,t,N,hst,hP,hQ,hC⟩

end QubitAdditivity.NormalKraus
