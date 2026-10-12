import QubitAdditivity.BetaTC4Regularization
import QubitAdditivity.BetaPositiveTC4

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

namespace QubitAdditivity.BetaTC4Boundary
open BetaDual BetaEntropy BetaDualValue BetaTC4Structure BetaGramSplit
open BetaTC4Gram BetaIsometryEntropy BetaBlockIsometry BetaDualExistence
open BetaTC4Regularization BetaPositiveTC4

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

/-- TC4 for arbitrary finite block types and arbitrary masses, including zero and empty dimensions. -/
theorem tc4_all_masses (A : Matrix r k ℂ) (B : Matrix r l ℂ) (C : Matrix s k ℂ) (D : Matrix s q ℂ) :
    OpenAIEntropy.entropy (tc4ScalarMatrix (blockMass A) (blockMass B) (blockMass C) (blockMass D))+
      weightedBlockEntropy A+weightedBlockEntropy B+weightedBlockEntropy C+weightedBlockEntropy D ≤
    OpenAIEntropy.entropy (tc4Matrix A B C D*(tc4Matrix A B C D)ᴴ) := by
  let L : ℝ → ℝ := fun t => OpenAIEntropy.entropy (tc4ScalarMatrix
    (blockMass (regularized A t)) (blockMass (regularized B t))
    (blockMass (regularized C t)) (blockMass (regularized D t)))+
    weightedBlockEntropy (regularized A t)+weightedBlockEntropy (regularized B t)+
    weightedBlockEntropy (regularized C t)+weightedBlockEntropy (regularized D t)
  let R : ℝ → ℝ := fun t => OpenAIEntropy.entropy
    (tc4Matrix (regularized A t) (regularized B t) (regularized C t) (regularized D t)*
      (tc4Matrix (regularized A t) (regularized B t) (regularized C t) (regularized D t))ᴴ)
  have hL : Continuous L := by
    exact ((((continuous_scalar_entropy_regularized A B C D).add (continuous_weighted_regularized A)).add
      (continuous_weighted_regularized B)).add (continuous_weighted_regularized C)).add
      (continuous_weighted_regularized D)
  have hR : Continuous R := continuous_entropy_tc4_regularized A B C D
  have hl : Tendsto L (𝓝[>] (0 : ℝ)) (𝓝 (L 0)) := (hL.tendsto 0).mono_left nhdsWithin_le_nhds
  have hr : Tendsto R (𝓝[>] (0 : ℝ)) (𝓝 (R 0)) := (hR.tendsto 0).mono_left nhdsWithin_le_nhds
  have hi : L 0 ≤ R 0 := by
    apply le_of_tendsto_of_tendsto hl hr
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hA : 0 < blockMass (regularized A t) := by
      rw [blockMass_regularized]
      exact add_pos_of_nonneg_of_pos (blockMass_nonneg A) (sq_pos_of_pos ht)
    have hB : 0 < blockMass (regularized B t) := by
      rw [blockMass_regularized]
      exact add_pos_of_nonneg_of_pos (blockMass_nonneg B) (sq_pos_of_pos ht)
    have hC : 0 < blockMass (regularized C t) := by
      rw [blockMass_regularized]
      exact add_pos_of_nonneg_of_pos (blockMass_nonneg C) (sq_pos_of_pos ht)
    have hD : 0 < blockMass (regularized D t) := by
      rw [blockMass_regularized]
      exact add_pos_of_nonneg_of_pos (blockMass_nonneg D) (sq_pos_of_pos ht)
    exact tc4_positive_mass (regularized A t) (regularized B t) (regularized C t) (regularized D t)
      hA hB hC hD
  simpa only [L,R,blockMass_regularized,zero_pow (by decide : (2 : ℕ) ≠ 0),add_zero,
    weighted_regularized_zero,entropy_tc4_regularized_zero] using hi

/-- The exact frozen four-block statement used by the qubit pure-input bridge. -/
theorem tc4Bound : TC4Bound := by
  intro r s k l q _ _ _ _ _ _ _ A B C D _
  exact tc4_all_masses A B C D

end QubitAdditivity.BetaTC4Boundary
