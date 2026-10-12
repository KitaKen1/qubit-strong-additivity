import QubitAdditivity.BetaScalarValue
import QubitAdditivity.BetaTC4Gram
import QubitAdditivity.BetaOuterReduction

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

namespace QubitAdditivity.BetaTC4Bridge
open BetaDual BetaEntropy BetaDualValue BetaTC4Structure BetaTC4Convex BetaGramSplit
open BetaScalarMinimum BetaScalarValue BetaTC4Gram

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



variable {r s k l t : Type*} [Fintype r] [Fintype s] [Fintype k] [Fintype l] [Fintype t]
  [DecidableEq r] [DecidableEq s]

/-- The remaining dual comparison implies the exact four-block entropy inequality.
No rank-one comparison or symmetry averaging is assumed to have been proved here. -/
theorem tc4_of_dual_comparison (A : Matrix r k ℂ) (B : Matrix r l ℂ) (C : Matrix s k ℂ) (D : Matrix s t ℂ)
    (hx : 0 < blockMass A) (hy : 0 < blockMass B) (hz : 0 < blockMass C) (hw : 0 < blockMass D)
    (hcompare : value (rankOne (blockMass A) (blockMass C))
        (lambdaLeft (blockMass A) (blockMass B) (blockMass C) (blockMass D))
        (lambdaRight (blockMass A) (blockMass B) (blockMass C) (blockMass D)) ≤
      value (gramPair A C)
        (lambdaLeft (blockMass A) (blockMass B) (blockMass C) (blockMass D))
        (lambdaRight (blockMass A) (blockMass B) (blockMass C) (blockMass D))) :
    OpenAIEntropy.entropy (tc4ScalarMatrix (blockMass A) (blockMass B) (blockMass C) (blockMass D))+
      weightedBlockEntropy A+weightedBlockEntropy B+weightedBlockEntropy C+weightedBlockEntropy D ≤
    OpenAIEntropy.entropy (tc4Matrix A B C D*(tc4Matrix A B C D)ᴴ) := by
  let lambda₀ := lambdaLeft (blockMass A) (blockMass B) (blockMass C) (blockMass D)
  let lambda₁ := lambdaRight (blockMass A) (blockMass B) (blockMass C) (blockMass D)
  have hi := value_le_primal (lambda₀ := lambda₀) (lambda₁ := lambda₁) (gramPair_posSemidef A C) (lambdaLeft_neg hx hy hw)
    (lambdaRight_neg hz hy hw) (gramBlocks_mem_positiveCone B D)
  rw [psi_pinching_gramPair,psi_diagonal,← gram_tc4Matrix] at hi
  rw [linearPenalty_apply] at hi
  change value (gramPair A C) lambda₀ lambda₁+
    (lambda₀*blockMass B+lambda₁*blockMass D) ≤
    psi (gram A)+psi (gram C)+(psi (gram B)+psi (gram D))-psi (gram (tc4Matrix A B C D)) at hi
  have hs := value_rankOne_eq hx hy hz hw
  rw [scalarDifference_eq hx.le hz.le] at hs
  change value (rankOne (blockMass A) (blockMass C)) lambda₀ lambda₁+
      lambda₀*blockMass B+lambda₁*blockMass D = _ at hs
  have he : OpenAIEntropy.entropy (tc4Matrix A B C D*(tc4Matrix A B C D)ᴴ) =
      -psi (gram (tc4Matrix A B C D)) := by
    simp only [psi,gram,neg_neg]
    rfl
  rw [weightedBlockEntropy_eq,weightedBlockEntropy_eq,weightedBlockEntropy_eq,weightedBlockEntropy_eq,he]
  change OpenAIEntropy.entropy (tc4ScalarMatrix (blockMass A) (blockMass B) (blockMass C) (blockMass D))+
    (-psi (gram A)+blockMass A*Real.log (blockMass A))+
    (-psi (gram B)+blockMass B*Real.log (blockMass B))+
    (-psi (gram C)+blockMass C*Real.log (blockMass C))+
    (-psi (gram D)+blockMass D*Real.log (blockMass D)) ≤ -psi (gram (tc4Matrix A B C D))
  linarith


/-- Connect the explicit balanced outer products to TC4 without a converse factorization theorem. -/
theorem tc4_of_outer_comparison (A : Matrix r k ℂ) (B : Matrix r l ℂ) (C : Matrix s k ℂ) (D : Matrix s t ℂ)
    (hx : 0 < blockMass A) (hy : 0 < blockMass B) (hz : 0 < blockMass C) (hw : 0 < blockMass D)
    (houter : ∀ v : r ⊕ s → ℂ,
      blockMass C*(pinchLeft (outer v)).mat.trace.re = blockMass A*(pinchRight (outer v)).mat.trace.re →
      value (rankOne (blockMass A) (blockMass C))
          (lambdaLeft (blockMass A) (blockMass B) (blockMass C) (blockMass D))
          (lambdaRight (blockMass A) (blockMass B) (blockMass C) (blockMass D)) /
        (blockMass A+blockMass C)*(outer v).mat.trace.re ≤
      value (outer v)
        (lambdaLeft (blockMass A) (blockMass B) (blockMass C) (blockMass D))
        (lambdaRight (blockMass A) (blockMass B) (blockMass C) (blockMass D))) :
    OpenAIEntropy.entropy (tc4ScalarMatrix (blockMass A) (blockMass B) (blockMass C) (blockMass D))+
      weightedBlockEntropy A+weightedBlockEntropy B+weightedBlockEntropy C+weightedBlockEntropy D ≤
    OpenAIEntropy.entropy (tc4Matrix A B C D*(tc4Matrix A B C D)ᴴ) := by
  classical
  apply tc4_of_dual_comparison A B C D hx hy hz hw
  have hi := BetaOuterReduction.value_gramPair_ge_of_outer A C
    (lambdaLeft_neg (z := blockMass C) hx hy hw) (lambdaRight_neg (x := blockMass A) hz hy hw) houter
  rw [div_mul_cancel₀ _ (ne_of_gt (add_pos hx hz))] at hi
  exact hi

end QubitAdditivity.BetaTC4Bridge
