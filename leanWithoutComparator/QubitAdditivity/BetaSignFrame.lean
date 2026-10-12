import QubitAdditivity.BetaTC4Structure
import Mathlib.Logic.Equiv.Bool

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

namespace QubitAdditivity.BetaSignFrame
open BetaTC4Convex BetaDualBoundary BetaDual BetaDualConvex BetaDualInterior BetaDualDerivative BetaMinimizer BetaEntropy BetaDualValue BetaDualExistence

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

def sign (b : Bool) : ℂ := if b then -1 else 1

@[simp] theorem star_sign (b : Bool) : star (sign b) = sign b := by cases b <;> norm_num [sign]
@[simp] theorem sign_sq (b : Bool) : sign b*sign b = 1 := by cases b <;> norm_num [sign]
@[simp] theorem sign_not (b : Bool) : sign (!b) = -sign b := by cases b <;> norm_num [sign]

/-- Flip one coordinate of the complete finite family of signs. -/
def flip (i : n) : Equiv.Perm (n → Bool) :=
  Equiv.piCongrRight (fun j => if j = i then Equiv.boolNot else Equiv.refl Bool)

@[simp] theorem flip_apply_same (i : n) (f : n → Bool) : flip i f i = !f i := by
  simp [flip,Equiv.piCongrRight,Equiv.boolNot]

theorem flip_apply_ne {i j : n} (h : j ≠ i) (f : n → Bool) : flip i f j = f j := by
  simp [flip,Equiv.piCongrRight,h]

/-- Distinct sign coordinates have zero covariance, by a pairing involution. -/
theorem sum_sign_mul_ne {i j : n} (h : i ≠ j) : ∑ f : n → Bool, sign (f i)*sign (f j) = 0 := by
  have he := Equiv.sum_comp (flip i) (fun f : n → Bool => sign (f i)*sign (f j))
  have hn : (∑ f : n → Bool, sign (f i)*sign (f j)) = -(∑ f : n → Bool, sign (f i)*sign (f j)) := by
    calc
      _ = ∑ f : n → Bool, sign (flip i f i)*sign (flip i f j) := he.symm
      _ = _ := by simp [flip_apply_ne h.symm,Finset.sum_neg_distrib]
  have hz : (2 : ℂ)*(∑ f : n → Bool, sign (f i)*sign (f j)) = 0 := by linear_combination hn
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

theorem sum_sign_mul (i j : n) : ∑ f : n → Bool, sign (f i)*sign (f j) =
    if i = j then (Fintype.card (n → Bool) : ℂ) else 0 := by
  by_cases h : i = j
  · subst j
    simp
  · simp [h,sum_sign_mul_ne h]

def signMatrix : Matrix n (n → Bool) ℂ := fun i f => sign (f i)

/-- A redundant flat frame works in every finite dimension; no DFT roots are required. -/
theorem signMatrix_mul_conjTranspose : (signMatrix (n := n))*signMatrixᴴ =
    (Fintype.card (n → Bool) : ℂ) • (1 : Matrix n n ℂ) := by
  ext i j
  change (∑ f : n → Bool, sign (f i)*star (sign (f j))) =
    (Fintype.card (n → Bool) : ℂ)*(if i = j then 1 else 0)
  simp [sum_sign_mul]

theorem signMatrix_quadratic_diagonal (d : n → ℝ) (f : n → Bool) :
    star (fun i => sign (f i)) ⬝ᵥ (Matrix.diagonal (fun i => (d i : ℂ)) *ᵥ fun i => sign (f i)) =
      (∑ i, d i : ℝ) := by
  simp only [Matrix.mulVec_diagonal,dotProduct,Pi.star_apply,star_sign]
  have he (i : n) : sign (f i)*((d i : ℂ)*sign (f i)) = (d i : ℂ) := by
    rw [mul_left_comm,sign_sq,mul_one]
  simp only [he,Complex.ofReal_sum]

/-- A flat redundant frame expressed in a Hermitian matrix's fixed spectral basis. -/
def spectralFrame (H : HermitianMat n ℂ) : Matrix n (n → Bool) ℂ :=
  fun i f => ∑ j, H.H.eigenvectorUnitary.val i j*sign (f j)

theorem spectralFrame_gram (H : HermitianMat n ℂ) : spectralFrame H*(spectralFrame H)ᴴ =
    (Fintype.card (n → Bool) : ℂ) • (1 : Matrix n n ℂ) := by
  change ((H.H.eigenvectorUnitary.val : Matrix n n ℂ)*(signMatrix (n := n))) *
    ((H.H.eigenvectorUnitary.val : Matrix n n ℂ)*(signMatrix (n := n)))ᴴ = _
  rw [Matrix.conjTranspose_mul]
  rw [Matrix.mul_assoc,← Matrix.mul_assoc signMatrix signMatrixᴴ H.H.eigenvectorUnitary.valᴴ]
  erw [signMatrix_mul_conjTranspose]
  rw [Matrix.smul_mul,Matrix.one_mul,Matrix.mul_smul]
  have hU : H.H.eigenvectorUnitary.val*H.H.eigenvectorUnitary.valᴴ = 1 := H.H.eigenvectorUnitary.prop.2
  rw [hU]

theorem spectralFrame_column (H : HermitianMat n ℂ) (f : n → Bool) :
    (fun i => spectralFrame H i f) = H.H.eigenvectorUnitary.val *ᵥ (fun i => sign (f i)) := rfl

/-- Every column has exactly the same quadratic expectation, namely tr H. -/
theorem spectralFrame_quadratic (H : HermitianMat n ℂ) (f : n → Bool) :
    star (fun i => spectralFrame H i f) ⬝ᵥ (H.mat *ᵥ fun i => spectralFrame H i f) = H.mat.trace := by
  rw [spectralFrame_column]
  change BetaComparison.pairing (H.H.eigenvectorUnitary.val *ᵥ fun i => sign (f i)) H.mat
    (H.H.eigenvectorUnitary.val *ᵥ fun i => sign (f i)) = _
  rw [BetaComparison.pairing_mulVec_left,BetaComparison.pairing_mulVec_right]
  have hd : H.H.eigenvectorUnitary.valᴴ*H.mat*H.H.eigenvectorUnitary.val =
      Matrix.diagonal (fun i => (H.H.eigenvalues i : ℂ)) := by
    simpa only [Unitary.conjStarAlgAut_apply,Unitary.coe_star,Matrix.star_eq_conjTranspose,star_star,Matrix.conjTranspose_conjTranspose,Function.comp_def,RCLike.ofReal_eq_complex_ofReal]
      using H.H.conjStarAlgAut_star_eigenvectorUnitary
  rw [hd]
  change star (fun i => sign (f i)) ⬝ᵥ (Matrix.diagonal (fun i => (H.H.eigenvalues i : ℂ)) *ᵥ
    fun i => sign (f i)) = _
  rw [signMatrix_quadratic_diagonal]
  exact_mod_cast H.H.trace_eq_sum_eigenvalues.symm

theorem spectralFrame_quadratic_zero {H : HermitianMat n ℂ} (hH : H.mat.trace = 0) (f : n → Bool) :
    star (fun i => spectralFrame H i f) ⬝ᵥ (H.mat *ᵥ fun i => spectralFrame H i f) = 0 := by
  rw [spectralFrame_quadratic,hH]

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Passing the frame through an arbitrary Gram factor preserves its Gram matrix up to the frame size. -/
theorem imageFrame_gram (X : Matrix m n ℂ) (H : HermitianMat n ℂ) :
    (X*spectralFrame H)*(X*spectralFrame H)ᴴ = (Fintype.card (n → Bool) : ℂ) • (X*Xᴴ) := by
  calc
    _ = X*(spectralFrame H*(spectralFrame H)ᴴ)*Xᴴ := by simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
    _ = X*((Fintype.card (n → Bool) : ℂ) • (1 : Matrix n n ℂ))*Xᴴ := by rw [spectralFrame_gram]
    _ = _ := by rw [Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul]

end QubitAdditivity.BetaSignFrame

