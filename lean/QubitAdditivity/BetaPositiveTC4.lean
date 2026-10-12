import QubitAdditivity.BetaBalancedValue
import QubitAdditivity.BetaTC4Bridge

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius

namespace QubitAdditivity.BetaPositiveTC4
open BetaDual BetaEntropy BetaDualValue BetaTC4Structure BetaGramSplit BetaScalarMinimum BetaBalancedValue BetaTC4Bridge

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

/-- The manuscript's four-block inequality for positive masses, with no dual comparison assumption. -/
theorem tc4_positive_mass (A : Matrix r k ℂ) (B : Matrix r l ℂ) (C : Matrix s k ℂ) (D : Matrix s t ℂ)
    (hx : 0 < blockMass A) (hy : 0 < blockMass B) (hz : 0 < blockMass C) (hw : 0 < blockMass D) :
    OpenAIEntropy.entropy (tc4ScalarMatrix (blockMass A) (blockMass B) (blockMass C) (blockMass D))+
      weightedBlockEntropy A+weightedBlockEntropy B+weightedBlockEntropy C+weightedBlockEntropy D ≤
    OpenAIEntropy.entropy (tc4Matrix A B C D*(tc4Matrix A B C D)ᴴ) := by
  apply tc4_of_outer_comparison A B C D hx hy hz hw
  intro v hr
  exact (balanced_outer_value v hx hz (lambdaLeft_neg (z := blockMass C) hx hy hw)
    (lambdaRight_neg (x := blockMass A) hz hy hw) hr).le

end QubitAdditivity.BetaPositiveTC4
