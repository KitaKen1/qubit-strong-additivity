import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Abel
import Mathlib.Analysis.Complex.Order

set_option autoImplicit false

/-! Algebraic audit of the beta-route stationary Gram identity.

This module does not prove TC4, matrix-curve comparison, or the existence of a
stationary minimizer. It proves the finite-dimensional Gram factorization and its
positivity once the explicitly listed operator identities are supplied. -/

noncomputable section
open scoped Matrix ComplexOrder

namespace QubitAdditivity.BetaCore

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The exact stationary Gram identity, with inclusion and compressed-generator
hypotheses explicit. All matrices may have complex entries. -/
theorem stationaryGram_identity
    (C K : Matrix n n ℂ) (B k : Matrix m m ℂ) (V : Matrix n m ℂ)
    (hV : Vᴴ * V = 1) (hK : Kᴴ = K)
    (hCK : C * K = K * C) (hBk : B * k = k * B)
    (hcomp : Vᴴ * K * V = k) :
    (Matrix.fromCols V (K * V))ᴴ * (C - V * B * Vᴴ) *
        Matrix.fromCols V (K * V) =
      Matrix.fromBlocks
        (Vᴴ * C * V - B)
        (Vᴴ * C * K * V - B * k)
        (Vᴴ * C * K * V - B * k)
        (Vᴴ * C * K * K * V - k * B * k) := by
  have h11 : Vᴴ * (C - V * B * Vᴴ) * V = Vᴴ * C * V - B := by
    have hs : Vᴴ * (V * B * Vᴴ) * V = B := by
      calc
        _ = (Vᴴ * V) * B * (Vᴴ * V) := by simp only [Matrix.mul_assoc]
        _ = B := by rw [hV]; simp
    rw [Matrix.mul_sub, Matrix.sub_mul, hs]
  have h12 : Vᴴ * (C - V * B * Vᴴ) * (K * V) =
      Vᴴ * C * K * V - B * k := by
    have hs : Vᴴ * (V * B * Vᴴ) * (K * V) = B * k := by
      calc
        _ = (Vᴴ * V) * B * (Vᴴ * K * V) := by simp only [Matrix.mul_assoc]
        _ = B * k := by rw [hV, hcomp]; simp
    rw [Matrix.mul_sub, Matrix.sub_mul, hs]
    simp only [Matrix.mul_assoc]
  have h21 : (K * V)ᴴ * (C - V * B * Vᴴ) * V =
      Vᴴ * C * K * V - B * k := by
    rw [Matrix.conjTranspose_mul, hK, Matrix.mul_sub, Matrix.sub_mul]
    have hs : Vᴴ * K * (V * B * Vᴴ) * V = k * B := by
      calc
        _ = (Vᴴ * K * V) * B * (Vᴴ * V) := by simp only [Matrix.mul_assoc]
        _ = k * B := by rw [hcomp, hV]; simp
    have ht : Vᴴ * K * C * V = Vᴴ * C * K * V := by
      calc
        _ = Vᴴ * (K * C) * V := by simp only [Matrix.mul_assoc]
        _ = Vᴴ * (C * K) * V := by rw [← hCK]
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [hs, ht, ← hBk]
  have h22 : (K * V)ᴴ * (C - V * B * Vᴴ) * (K * V) =
      Vᴴ * C * K * K * V - k * B * k := by
    rw [Matrix.conjTranspose_mul, hK, Matrix.mul_sub, Matrix.sub_mul]
    have hs : Vᴴ * K * (V * B * Vᴴ) * (K * V) = k * B * k := by
      calc
        _ = (Vᴴ * K * V) * B * (Vᴴ * K * V) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hcomp]
    have ht : Vᴴ * K * C * (K * V) = Vᴴ * C * K * K * V := by
      calc
        _ = Vᴴ * (K * C) * K * V := by simp only [Matrix.mul_assoc]
        _ = Vᴴ * (C * K) * K * V := by rw [← hCK]
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [hs, ht]
  rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols, h11, h12, h21, h22]

/-- Positivity of the factored operator implies positivity of the entire two-by-two
block Gram matrix. This does not assume the sought PW or TC4 inequality. -/
theorem stationaryGram_posSemidef
    (C K : Matrix n n ℂ) (B k : Matrix m m ℂ) (V : Matrix n m ℂ)
    (hV : Vᴴ * V = 1) (hK : Kᴴ = K)
    (hCK : C * K = K * C) (hBk : B * k = k * B)
    (hcomp : Vᴴ * K * V = k) (hD : (C - V * B * Vᴴ).PosSemidef) :
    (Matrix.fromBlocks
      (Vᴴ * C * V - B)
      (Vᴴ * C * K * V - B * k)
      (Vᴴ * C * K * V - B * k)
      (Vᴴ * C * K * K * V - k * B * k)).PosSemidef := by
  rw [← stationaryGram_identity C K B k V hV hK hCK hBk hcomp]
  exact hD.conjTranspose_mul_mul_same (Matrix.fromCols V (K * V))

/-- Woodbury with the minus sign used by the eliminated dual-value Hessian. -/
theorem woodbury_sub
    (A : Matrix n n ℂ) (B : Matrix m m ℂ) (V : Matrix n m ℂ)
    (hA : IsUnit A) (hB : IsUnit B)
    (hE : IsUnit (B⁻¹ - Vᴴ * A⁻¹ * V)) :
    (A - V * B * Vᴴ)⁻¹ =
      A⁻¹ + A⁻¹ * V * (B⁻¹ - Vᴴ * A⁻¹ * V)⁻¹ * Vᴴ * A⁻¹ := by
  have hE' : IsUnit (B⁻¹ + Vᴴ * A⁻¹ * (-V)) := by
    simpa only [Matrix.mul_neg, sub_eq_add_neg] using hE
  have h := Matrix.add_mul_mul_inv_eq_sub A (-V) B Vᴴ hA hB hE'
  simpa only [Matrix.neg_mul, Matrix.mul_neg, sub_eq_add_neg, neg_neg] using h

/-- The Schur-complement Hessian and the inverse-difference formula coincide.
The derivative and minimizer-existence hypotheses still have to be supplied by
the analytic part of the beta route. -/
theorem eliminatedHessian_eq
    (A : Matrix n n ℂ) (B C : Matrix m m ℂ) (V : Matrix n m ℂ)
    (hA : IsUnit A) (hB : IsUnit B)
    (hE : IsUnit (B⁻¹ - Vᴴ * A⁻¹ * V)) :
    V * C⁻¹ * Vᴴ - A⁻¹ -
        A⁻¹ * V * (B⁻¹ - Vᴴ * A⁻¹ * V)⁻¹ * Vᴴ * A⁻¹ =
      V * C⁻¹ * Vᴴ - (A - V * B * Vᴴ)⁻¹ := by
  rw [woodbury_sub A B V hA hB hE]
  abel

end QubitAdditivity.BetaCore
