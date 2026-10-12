import QubitAdditivity.BetaTC4Unitary
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Module

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius

namespace QubitAdditivity.BetaReflection
open BetaDual BetaEntropy BetaDualValue BetaTC4Unitary

@[reducible] local instance mNorm {k : Type*} [Fintype k] [DecidableEq k] :
    NormedAddCommGroup (Matrix k k ℂ) :=
  Matrix.frobeniusNormedRing.toNonUnitalNormedRing.toNormedAddCommGroup
@[reducible] local instance mSpace {k : Type*} [Fintype k] [DecidableEq k] :
    NormedSpace ℝ (Matrix k k ℂ) := NormedAlgebra.toNormedSpace (Matrix k k ℂ)
@[reducible] local instance mTop {k : Type*} [Fintype k] [DecidableEq k] :
    TopologicalSpace (Matrix k k ℂ) := mNorm.toUniformSpace.toTopologicalSpace
@[reducible] local instance mAdd {k : Type*} [Fintype k] [DecidableEq k] :
    AddCommGroup (Matrix k k ℂ) := mNorm.toAddCommGroup
@[reducible] local instance mModule {k : Type*} [Fintype k] [DecidableEq k] :
    Module ℝ (Matrix k k ℂ) := mSpace.toModule
@[reducible] local instance hTop {k : Type*} [Fintype k] : TopologicalSpace (HermitianMat k ℂ) :=
  HermitianMat.instNormedAddCommGroupComplex.toUniformSpace.toTopologicalSpace
@[reducible] local instance hAdd {k : Type*} [Fintype k] : AddCommGroup (HermitianMat k ℂ) :=
  HermitianMat.instNormedAddCommGroupComplex.toAddCommGroup
@[reducible] local instance hModule {k : Type*} [Fintype k] : Module ℝ (HermitianMat k ℂ) :=
  HermitianMat.instNormedSpace.toModule


@[reducible] local instance pAdd {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] :
    AddCommGroup (E × F) := Prod.normedAddCommGroup.toAddCommGroup
@[reducible] local instance pTop {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] :
    TopologicalSpace (E × F) := Prod.normedAddCommGroup.toUniformSpace.toTopologicalSpace
@[reducible] local instance pModule {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F] : Module ℝ (E × F) := Prod.normedSpace.toModule


@[reducible] local instance matrixHMul {a b c : Type*} [Fintype b] :
    HMul (Matrix a b ℂ) (Matrix b c ℂ) (Matrix a c ℂ) :=
  Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Reflect in the range of a Hermitian projection. -/
def reflection (P : HermitianMat n ℂ) (hP : P.mat*P.mat = P.mat) : Matrix.unitaryGroup n ℂ :=
  ⟨(2 : ℝ) • P.mat-1,by
    rw [Matrix.mem_unitaryGroup_iff,Matrix.star_eq_conjTranspose]
    simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_smul,Matrix.conjTranspose_one,P.H.eq,star_trivial]
    simp only [two_smul ℝ P.mat]
    noncomm_ring [hP]⟩

@[simp] theorem reflection_val (P : HermitianMat n ℂ) (hP : P.mat*P.mat = P.mat) :
    (reflection P hP).val = (2 : ℝ) • P.mat-1 := rfl

theorem reflection_isHermitian (P : HermitianMat n ℂ) (hP : P.mat*P.mat = P.mat) :
    (reflection P hP).val.IsHermitian := by
  change ((2 : ℝ) • P.mat-1)ᴴ = (2 : ℝ) • P.mat-1
  simp only [Matrix.conjTranspose_sub,Matrix.conjTranspose_smul,Matrix.conjTranspose_one,P.H.eq,star_trivial]

theorem reflection_fix (P J : HermitianMat n ℂ) (hP : P.mat*P.mat = P.mat) (hPJ : P.mat*J.mat = J.mat) :
    J.conj (reflection P hP).val = J := by
  have hJP : J.mat*P.mat = J.mat := by
    have h := congrArg Matrix.conjTranspose hPJ
    simpa only [Matrix.conjTranspose_mul,P.H.eq,J.H.eq] using h
  apply HermitianMat.ext
  change (reflection P hP).val*J.mat*(reflection P hP).valᴴ = J.mat
  rw [(reflection_isHermitian P hP).eq,reflection_val]
  simp only [two_smul ℝ P.mat]
  noncomm_ring [hPJ,hJP]

/-- One reflection average removes exactly the cross terms between support and complement. -/
theorem reflection_average (P W : HermitianMat n ℂ) (hP : P.mat*P.mat = P.mat) :
    ((1/2 : ℝ) • (W+W.conj (reflection P hP).val)).mat =
      P.mat*W.mat*P.mat+(1-P.mat)*W.mat*(1-P.mat) := by
  change (1/2 : ℝ) • (W.mat+(reflection P hP).val*W.mat*(reflection P hP).valᴴ) = _
  rw [(reflection_isHermitian P hP).eq,reflection_val]
  simp only [Matrix.sub_mul,Matrix.mul_sub,Matrix.smul_mul,Matrix.mul_smul,
    Matrix.one_mul,Matrix.mul_one,smul_smul,Matrix.mul_assoc]
  module

end QubitAdditivity.BetaReflection
