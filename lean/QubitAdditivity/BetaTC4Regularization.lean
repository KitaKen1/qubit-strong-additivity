import QubitAdditivity.BetaTC4Gram
import QubitAdditivity.BetaBlockIsometry
import QubitAdditivity.TwoExpectation

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

namespace QubitAdditivity.BetaTC4Regularization
open BetaDual BetaEntropy BetaDualValue BetaTC4Structure BetaGramSplit
open BetaTC4Gram BetaIsometryEntropy BetaBlockIsometry BetaDualExistence

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


variable {r s k l q : Type*} [Fintype r] [Fintype s] [Fintype k] [Fintype l] [Fintype q]
  [DecidableEq r] [DecidableEq s]

/-- Append one row and one column; the new diagonal entry is real t. -/
def regularized (A : Matrix r k ℂ) (t : ℝ) : Matrix (r ⊕ Fin 1) (k ⊕ Fin 1) ℂ :=
  Matrix.fromBlocks A 0 0 (t • (1 : Matrix (Fin 1) (Fin 1) ℂ))

def rowEmbedding (r : Type*) [Fintype r] [DecidableEq r] : Matrix (r ⊕ Fin 1) r ℂ :=
  Matrix.fromRows 1 0

theorem rowEmbedding_isometry : (rowEmbedding r)ᴴ*rowEmbedding r = 1 := by
  simp [rowEmbedding,Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,Matrix.fromCols_mul_fromRows]

theorem rowEmbedding_mul (A : Matrix r k ℂ) : rowEmbedding r*A = Matrix.fromRows A 0 := by
  simp [rowEmbedding,Matrix.fromRows_mul]

theorem regularized_zero (A : Matrix r k ℂ) :
    regularized A 0 = Matrix.fromCols (rowEmbedding r*A) 0 := by
  rw [rowEmbedding_mul]
  ext i j
  cases i <;> cases j <;> simp [regularized,Matrix.fromBlocks,Matrix.fromCols,Matrix.fromRows]

/-- Every mass is positive for t > 0, even when the original row or column type is empty. -/
theorem blockMass_regularized (A : Matrix r k ℂ) (t : ℝ) :
    blockMass (regularized A t) = blockMass A+t^2 := by
  simp [regularized,blockMass_eq_sum_normSq,Matrix.fromBlocks,Fintype.sum_sum_type,
    Fin.sum_univ_one,Matrix.one_apply,Complex.real_smul,Complex.normSq_ofReal,pow_two]

theorem gram_fromCols_zero (A : Matrix r k ℂ) :
    gram (Matrix.fromCols A (0 : Matrix r (Fin 1) ℂ)) = gram A := by
  apply HermitianMat.ext
  change Matrix.fromCols A 0*(Matrix.fromCols A 0)ᴴ = A*Aᴴ
  rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,Matrix.fromCols_mul_fromRows]
  simp

theorem gram_mul {a : Type*} [Fintype a] [DecidableEq a]
    (R : Matrix a r ℂ) (A : Matrix r k ℂ) : gram (R*A) = (gram A).conj R := by
  apply HermitianMat.ext
  change (R*A)*(R*A)ᴴ = R*(A*Aᴴ)*Rᴴ
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem gram_regularized_zero (A : Matrix r k ℂ) :
    gram (regularized A 0) = (gram A).conj (rowEmbedding r) := by
  rw [regularized_zero,gram_fromCols_zero,gram_mul]

theorem weighted_regularized_zero (A : Matrix r k ℂ) :
    weightedBlockEntropy (regularized A 0) = weightedBlockEntropy A := by
  rw [weightedBlockEntropy_eq,weightedBlockEntropy_eq,gram_regularized_zero,
    psi_isometry (rowEmbedding r) rowEmbedding_isometry,blockMass_regularized]
  simp

theorem continuous_regularized (A : Matrix r k ℂ) : Continuous (regularized A) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  cases i <;> cases j <;> simp only [regularized,Matrix.fromBlocks,Matrix.of_apply,Sum.elim_inl,Sum.elim_inr] <;> fun_prop

theorem continuous_gram {X : Type*} [TopologicalSpace X] (f : X → Matrix r k ℂ)
    (hf : Continuous f) : Continuous (fun x => gram (f x)) := by
  apply Continuous.subtype_mk
  change Continuous (fun x => f x*(f x)ᴴ)
  fun_prop

theorem continuous_gram_regularized (A : Matrix r k ℂ) :
    Continuous (fun t => gram (regularized A t)) := continuous_gram _ (continuous_regularized A)

theorem continuous_weighted_regularized (A : Matrix r k ℂ) :
    Continuous (fun t => weightedBlockEntropy (regularized A t)) := by
  have hg := (continuous_psi.comp (continuous_gram_regularized A)).neg
  have hm : Continuous (fun t : ℝ => blockMass A+t^2) := by fun_prop
  have h := hg.sub (Real.continuous_negMulLog.comp hm)
  convert! h using 1
  funext t
  rw [weightedBlockEntropy_eq,blockMass_regularized]
  simp [Real.negMulLog] <;> ring


theorem gramPair_regularized_zero (A : Matrix r k ℂ) (C : Matrix s k ℂ) :
    gramPair (regularized A 0) (regularized C 0) =
      (gramPair A C).conj (blockEmbedding (rowEmbedding r) (rowEmbedding s)) := by
  change gram (Matrix.fromRows (regularized A 0) (regularized C 0)) =
    (gram (Matrix.fromRows A C)).conj _
  rw [regularized_zero,regularized_zero]
  have he : Matrix.fromRows (Matrix.fromCols (rowEmbedding r*A) (0 : Matrix (r ⊕ Fin 1) (Fin 1) ℂ))
      (Matrix.fromCols (rowEmbedding s*C) 0) =
      Matrix.fromCols (Matrix.fromRows (rowEmbedding r*A) (rowEmbedding s*C)) 0 := by
    ext i j
    cases i <;> cases j <;> rfl
  rw [he,gram_fromCols_zero]
  have hf : Matrix.fromRows (rowEmbedding r*A) (rowEmbedding s*C) =
      blockEmbedding (rowEmbedding r) (rowEmbedding s)*Matrix.fromRows A C := by
    simp [blockEmbedding,Matrix.fromBlocks_mul_fromRows]
  rw [hf,gram_mul]

theorem gram_tc4_regularized_zero (A : Matrix r k ℂ) (B : Matrix r l ℂ)
    (C : Matrix s k ℂ) (D : Matrix s q ℂ) :
    gram (tc4Matrix (regularized A 0) (regularized B 0) (regularized C 0) (regularized D 0)) =
      (gram (tc4Matrix A B C D)).conj (blockEmbedding (rowEmbedding r) (rowEmbedding s)) := by
  rw [gram_tc4Matrix,gramPair_regularized_zero]
  have hd : diagonal (gramBlocks (regularized B 0) (regularized D 0)) =
      (diagonal (gramBlocks B D)).conj (blockEmbedding (rowEmbedding r) (rowEmbedding s)) := by
    change diagonal (gram (regularized B 0),gram (regularized D 0)) = _
    rw [gram_regularized_zero,gram_regularized_zero]
    exact diagonal_embedBlocks (rowEmbedding r) (rowEmbedding s) (gramBlocks B D)
  rw [hd,← map_add,← gram_tc4Matrix]

theorem entropy_tc4_regularized_zero (A : Matrix r k ℂ) (B : Matrix r l ℂ)
    (C : Matrix s k ℂ) (D : Matrix s q ℂ) :
    OpenAIEntropy.entropy ((tc4Matrix (regularized A 0) (regularized B 0) (regularized C 0) (regularized D 0))*
      (tc4Matrix (regularized A 0) (regularized B 0) (regularized C 0) (regularized D 0))ᴴ) =
      OpenAIEntropy.entropy (tc4Matrix A B C D*(tc4Matrix A B C D)ᴴ) := by
  have hi := psi_isometry (blockEmbedding (rowEmbedding r) (rowEmbedding s))
    (blockEmbedding_isometry _ _ rowEmbedding_isometry rowEmbedding_isometry) (gram (tc4Matrix A B C D))
  rw [← gram_tc4_regularized_zero A B C D] at hi
  simpa [psi,gram] using congrArg Neg.neg hi

theorem continuous_gram_tc4_regularized (A : Matrix r k ℂ) (B : Matrix r l ℂ)
    (C : Matrix s k ℂ) (D : Matrix s q ℂ) :
    Continuous (fun t => gram (tc4Matrix (regularized A t) (regularized B t) (regularized C t) (regularized D t))) := by
  apply continuous_gram
  have hA := continuous_regularized A
  have hB := continuous_regularized B
  have hC := continuous_regularized C
  have hD := continuous_regularized D
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  rcases i with i|i <;> rcases j with j|(j|j)
  all_goals simp only [tc4Matrix]; fun_prop

theorem continuous_entropy_tc4_regularized (A : Matrix r k ℂ) (B : Matrix r l ℂ)
    (C : Matrix s k ℂ) (D : Matrix s q ℂ) :
    Continuous (fun t => OpenAIEntropy.entropy
      (tc4Matrix (regularized A t) (regularized B t) (regularized C t) (regularized D t)*
        (tc4Matrix (regularized A t) (regularized B t) (regularized C t) (regularized D t))ᴴ)) := by
  convert! (continuous_psi.comp (continuous_gram_tc4_regularized A B C D)).neg using 1
  funext t
  simp [psi,gram]

/-- Entropy of the scalar comparison is continuous at zero masses as well. -/
theorem continuous_scalar_entropy {X : Type*} [TopologicalSpace X]
    (x y z w : X → ℝ) (hx : Continuous x) (hy : Continuous y) (hz : Continuous z) (hw : Continuous w) :
    Continuous (fun t => OpenAIEntropy.entropy (tc4ScalarMatrix (x t) (y t) (z t) (w t))) := by
  let f : X → HermitianMat (Fin 2) ℂ := fun t =>
    ⟨tc4ScalarMatrix (x t) (y t) (z t) (w t),tc4ScalarMatrix_isHermitian _ _ _ _⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    change Continuous (fun t => tc4ScalarMatrix (x t) (y t) (z t) (w t))
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    fin_cases i <;> fin_cases j <;> simp only [tc4ScalarMatrix,Matrix.of_apply,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_fin_one] <;> fun_prop
  convert! (continuous_psi.comp hf).neg using 1
  funext t
  simp [psi,f]

theorem continuous_scalar_entropy_regularized (A : Matrix r k ℂ) (B : Matrix r l ℂ)
    (C : Matrix s k ℂ) (D : Matrix s q ℂ) :
    Continuous (fun t => OpenAIEntropy.entropy (tc4ScalarMatrix
      (blockMass (regularized A t)) (blockMass (regularized B t))
      (blockMass (regularized C t)) (blockMass (regularized D t)))) := by
  simp_rw [blockMass_regularized]
  apply continuous_scalar_entropy <;> fun_prop

end QubitAdditivity.BetaTC4Regularization
