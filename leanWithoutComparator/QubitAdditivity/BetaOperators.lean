import QubitAdditivity.BetaCore
import Mathlib.Analysis.Matrix.Order

set_option autoImplicit false

/-! Finite matrix coordinates for the beta-route Hilbert--Schmidt operators.

Row-major coordinates identify a matrix X with the vector (i,j) ↦ X i j.
Left and right multiplication are A ⊗ I and I ⊗ Aᵀ. The block inclusion
selects the two diagonal matrix blocks, and its adjoint is the compression.
This module supplies the inclusion and generator hypotheses of BetaCore.
It does not yet prove the CFC, curve-comparison, or minimizer assertions. -/

noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix

namespace QubitAdditivity.BetaOperators

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Left multiplication in the orthonormal matrix-unit coordinates. -/
def left (A : Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ := A ⊗ₖ (1 : Matrix n n ℂ)

/-- Right multiplication; the transpose is required by row-major coordinates. -/
def right (A : Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ := (1 : Matrix n n ℂ) ⊗ₖ Aᵀ

/-- The commutator generator L_A - R_A. -/
def generator (A : Matrix n n ℂ) := left A - right A

theorem left_mulVec (A X : Matrix n n ℂ) (i j : n) :
    (left A *ᵥ fun ij => X ij.1 ij.2) (i, j) = (A * X) i j := by
  simp [left, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.mul_apply,
    Matrix.one_apply]

theorem right_mulVec (A X : Matrix n n ℂ) (i j : n) :
    (right A *ᵥ fun ij => X ij.1 ij.2) (i, j) = (X * A) i j := by
  simp [right, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.mul_apply,
    Matrix.one_apply, mul_comm]

theorem left_mul (A B : Matrix n n ℂ) : left (A * B) = left A * left B := by
  simp only [left, ← mul_kronecker_mul, Matrix.one_mul]

theorem right_mul (A B : Matrix n n ℂ) : right (A * B) = right B * right A := by
  simp only [right, ← mul_kronecker_mul, Matrix.one_mul, transpose_mul]

theorem left_right_commute (A B : Matrix n n ℂ) :
    left A * right B = right B * left A := by
  simp only [left, right, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]

theorem left_conjTranspose (A : Matrix n n ℂ) : (left A)ᴴ = left Aᴴ := by
  simp only [left, conjTranspose_kronecker, conjTranspose_one]

theorem right_conjTranspose (A : Matrix n n ℂ) : (right A)ᴴ = right Aᴴ := by
  simp only [right, conjTranspose_kronecker, conjTranspose_one,
    conjTranspose_transpose_eq_transpose_conjTranspose]

theorem generator_isHermitian {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (generator A).IsHermitian := by
  unfold IsHermitian generator
  rw [conjTranspose_sub, left_conjTranspose, right_conjTranspose, hA]

theorem left_posSemidef {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    (left A).PosSemidef := hA.kronecker Matrix.PosSemidef.one

theorem right_posSemidef {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    (right A).PosSemidef := Matrix.PosSemidef.one.kronecker hA.transpose

theorem generator_add_scalar (A : Matrix n n ℂ) (c : ℂ) :
    generator (A + c • (1 : Matrix n n ℂ)) = generator A := by
  simp only [generator, left, right, add_kronecker, transpose_add, transpose_smul,
    transpose_one, kronecker_add, smul_kronecker, kronecker_smul]
  abel

section inclusion
variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Inclusion of a subset of orthonormal coordinates. -/
def coordinateInclusion (e : m ↪ n) : Matrix n m ℂ := (1 : Matrix n n ℂ).submatrix id e

theorem coordinateInclusion_compression (e : m ↪ n) (A : Matrix n n ℂ) :
    (coordinateInclusion e)ᴴ * A * coordinateInclusion e = A.submatrix e e := by
  simp only [coordinateInclusion, conjTranspose_submatrix, conjTranspose_one]
  change (1 : Matrix n n ℂ).submatrix e (Equiv.refl n) * A *
    (1 : Matrix n n ℂ).submatrix (Equiv.refl n) e = _
  rw [one_submatrix_mul e (Equiv.refl n), mul_submatrix_one (Equiv.refl n) e]
  rfl

theorem coordinateInclusion_isometry (e : m ↪ n) :
    (coordinateInclusion e)ᴴ * coordinateInclusion e = 1 := by
  have h := coordinateInclusion_compression e (1 : Matrix n n ℂ)
  simpa only [Matrix.mul_one, submatrix_one_embedding] using h
end inclusion

section blocks
variable {r s : Type*} [Fintype r] [Fintype s] [DecidableEq r] [DecidableEq s]

/-- Matrix-unit coordinates in the two diagonal blocks. -/
def blockCoordinates : ((r × r) ⊕ (s × s)) ↪ ((r ⊕ s) × (r ⊕ s)) where
  toFun := Sum.elim (fun ij => (Sum.inl ij.1, Sum.inl ij.2))
    (fun ij => (Sum.inr ij.1, Sum.inr ij.2))
  inj' := by
    intro a b h
    cases a <;> cases b <;> simp_all [Prod.mk.injEq]
    all_goals exact Prod.ext h.1 h.2

@[simp] theorem blockCoordinates_inl (i : r × r) :
    blockCoordinates (s := s) (Sum.inl i) = (Sum.inl i.1, Sum.inl i.2) := rfl

@[simp] theorem blockCoordinates_inr (i : s × s) :
    blockCoordinates (r := r) (Sum.inr i) = (Sum.inr i.1, Sum.inr i.2) := rfl

def blockInclusion : Matrix ((r ⊕ s) × (r ⊕ s)) ((r × r) ⊕ (s × s)) ℂ :=
  coordinateInclusion blockCoordinates

def blockGenerator (A : Matrix r r ℂ) (B : Matrix s s ℂ) :=
  Matrix.fromBlocks (generator A) 0 0 (generator B)

theorem blockInclusion_isometry :
    (blockInclusion (r := r) (s := s))ᴴ * blockInclusion (r := r) (s := s) = 1 :=
  coordinateInclusion_isometry blockCoordinates

/-- Compression discards cross-block entries of the commutator generator. -/
theorem generator_compression (H : Matrix (r ⊕ s) (r ⊕ s) ℂ) :
    blockInclusionᴴ * generator H * blockInclusion =
      blockGenerator (H.submatrix Sum.inl Sum.inl) (H.submatrix Sum.inr Sum.inr) := by
  rw [blockInclusion, coordinateInclusion_compression]
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j => simp [blockGenerator, generator, left, right,
        Matrix.one_apply]
    | inr j => simp [blockGenerator, generator, left, right,
        Matrix.one_apply]
  | inr i =>
    cases j with
    | inl j => simp [blockGenerator, generator, left, right,
        Matrix.one_apply]
    | inr j => simp [blockGenerator, generator, left, right,
        Matrix.one_apply]

/-- Adding a central scalar to either block leaves its commutator unchanged. -/
theorem generator_compression_of_stationarity
    (H : Matrix (r ⊕ s) (r ⊕ s) ℂ) (W₀ : Matrix r r ℂ) (W₁ : Matrix s s ℂ)
    (lambda₀ lambda₁ : ℂ)
    (h₀ : W₀ = H.submatrix Sum.inl Sum.inl + lambda₀ • 1)
    (h₁ : W₁ = H.submatrix Sum.inr Sum.inr + lambda₁ • 1) :
    blockInclusionᴴ * generator H * blockInclusion = blockGenerator W₀ W₁ := by
  rw [generator_compression, h₀, h₁]
  simp only [blockGenerator, generator_add_scalar]

local notation "Vβ" => blockInclusion (r := r) (s := s)

/-- The stationary Gram theorem instantiated with actual matrix-unit coordinates.
Only the analytic CFC commutation and positivity assumptions remain explicit. -/
theorem stationaryGram_of_blockStationarity
    (C : Matrix ((r ⊕ s) × (r ⊕ s)) ((r ⊕ s) × (r ⊕ s)) ℂ)
    (B : Matrix ((r × r) ⊕ (s × s)) ((r × r) ⊕ (s × s)) ℂ)
    (H : Matrix (r ⊕ s) (r ⊕ s) ℂ) (W₀ : Matrix r r ℂ) (W₁ : Matrix s s ℂ)
    (lambda₀ lambda₁ : ℂ) (hH : H.IsHermitian)
    (h₀ : W₀ = H.submatrix Sum.inl Sum.inl + lambda₀ • 1)
    (h₁ : W₁ = H.submatrix Sum.inr Sum.inr + lambda₁ • 1)
    (hC : C * generator H = generator H * C)
    (hB : B * blockGenerator W₀ W₁ = blockGenerator W₀ W₁ * B)
    (hD : (C - Vβ * B * Vβᴴ).PosSemidef) :
    (Matrix.fromBlocks
      (Vβᴴ * C * Vβ - B)
      (Vβᴴ * C * generator H * Vβ - B * blockGenerator W₀ W₁)
      (Vβᴴ * C * generator H * Vβ - B * blockGenerator W₀ W₁)
      (Vβᴴ * C * generator H * generator H * Vβ -
        blockGenerator W₀ W₁ * B * blockGenerator W₀ W₁)).PosSemidef :=
  BetaCore.stationaryGram_posSemidef C (generator H) B (blockGenerator W₀ W₁)
    Vβ blockInclusion_isometry (generator_isHermitian hH) hC hB
    (generator_compression_of_stationarity H W₀ W₁ lambda₀ lambda₁ h₀ h₁) hD
end blocks
end QubitAdditivity.BetaOperators
