import QubitAdditivity.BetaStrict

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Matrix Kronecker ComplexOrder MatrixOrder

namespace QubitAdditivity.BetaEndpoints
open BetaOperators BetaPowers BetaBridge BetaBlocks BetaStrict
variable {r s : Type*} [Fintype r] [Fintype s] [DecidableEq r] [DecidableEq s]
local notation "Vβ" => blockInclusion (r := r) (s := s)

theorem left_compression (T : Matrix (r ⊕ s) (r ⊕ s) ℂ) :
    Vβᴴ * left T * Vβ =
      Matrix.fromBlocks (left (T.submatrix Sum.inl Sum.inl)) 0 0
        (left (T.submatrix Sum.inr Sum.inr)) := by
  rw [blockInclusion, coordinateInclusion_compression]
  ext i j
  cases i <;> cases j <;> simp [left, kroneckerMap_apply, Matrix.one_apply]

theorem right_compression (T : Matrix (r ⊕ s) (r ⊕ s) ℂ) :
    Vβᴴ * right T * Vβ =
      Matrix.fromBlocks (right (T.submatrix Sum.inl Sum.inl)) 0 0
        (right (T.submatrix Sum.inr Sum.inr)) := by
  rw [blockInclusion, coordinateInclusion_compression]
  ext i j
  cases i <;> cases j <;> simp [right, kroneckerMap_apply, Matrix.one_apply]

theorem blockPW_zero {A : Matrix r r ℂ} {B : Matrix s s ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    blockPW A B 0 = Matrix.fromBlocks (right A) 0 0 (right B) := by
  simp [blockPW, pw_zero hA, pw_zero hB]

theorem blockPW_one {A : Matrix r r ℂ} {B : Matrix s s ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    blockPW A B 1 = Matrix.fromBlocks (left A) 0 0 (left B) := by
  simp [blockPW, pw_one hA, pw_one hB]

theorem curve_zero {T : Matrix (r ⊕ s) (r ⊕ s) ℂ}
    {A : Matrix r r ℂ} {B : Matrix s s ℂ}
    (hT : T.IsHermitian) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    curve T A B 0 = Matrix.fromBlocks
      (right (T.submatrix Sum.inl Sum.inl - A)) 0 0
      (right (T.submatrix Sum.inr Sum.inr - B)) := by
  rw [curve, pw_zero hT, right_compression, blockPW_zero hA hB]
  ext i j
  cases i <;> cases j <;> simp [right, kroneckerMap_apply, mul_sub]

theorem curve_one {T : Matrix (r ⊕ s) (r ⊕ s) ℂ}
    {A : Matrix r r ℂ} {B : Matrix s s ℂ}
    (hT : T.IsHermitian) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    curve T A B 1 = Matrix.fromBlocks
      (left (T.submatrix Sum.inl Sum.inl - A)) 0 0
      (left (T.submatrix Sum.inr Sum.inr - B)) := by
  rw [curve, pw_one hT, left_compression, blockPW_one hA hB]
  ext i j
  cases i <;> cases j <;> simp [left, kroneckerMap_apply, sub_mul]

theorem gap_blocks_posDef {T : Matrix (r ⊕ s) (r ⊕ s) ℂ}
    {A : Matrix r r ℂ} {B : Matrix s s ℂ}
    (hgap : (T - Matrix.fromBlocks A 0 0 B).PosDef) :
    (T.submatrix Sum.inl Sum.inl - A).PosDef ∧
      (T.submatrix Sum.inr Sum.inr - B).PosDef := by
  constructor
  · have hp := hgap.submatrix (Sum.inl_injective (β := s))
    have he : (T - Matrix.fromBlocks A 0 0 B).submatrix Sum.inl Sum.inl =
        T.submatrix Sum.inl Sum.inl - A := by
      ext i j
      rfl
    rwa [he] at hp
  · have hp := hgap.submatrix (Sum.inr_injective (α := r))
    have he : (T - Matrix.fromBlocks A 0 0 B).submatrix Sum.inr Sum.inr =
        T.submatrix Sum.inr Sum.inr - B := by
      ext i j
      rfl
    rwa [he] at hp

end QubitAdditivity.BetaEndpoints
