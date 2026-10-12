import QubitAdditivity.BetaGramSplit

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

namespace QubitAdditivity.BetaOuterReduction
open BetaDual BetaEntropy BetaDualValue BetaTC4Structure BetaGramSplit BetaSignFrame

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


variable {n r s : Type*} [Fintype n] [Fintype r] [Fintype s]
  [DecidableEq n] [DecidableEq r] [DecidableEq s]

def atomVector (A : Matrix r n ℂ) (C : Matrix s n ℂ) (f : n → Bool) : r ⊕ s → ℂ :=
  Real.sqrt (Fintype.card (n → Bool) : ℝ)⁻¹ •
    Sum.elim (A *ᵥ fun i => spectralFrame (balanceMatrix A C) i f)
      (C *ᵥ fun i => spectralFrame (balanceMatrix A C) i f)

/-- Use the vectors already supplied by the sign frame; no converse rank-one factorization is needed. -/
theorem decomposition_eq_outer (A : Matrix r n ℂ) (C : Matrix s n ℂ) (f : n → Bool) :
    decomposition A C f = outer (atomVector A C f) := by
  unfold decomposition balancedAtom atomVector
  exact (outer_sqrt_smul (inv_nonneg.mpr (Nat.cast_nonneg _)) _).symm

/-- The arbitrary Gram comparison needs only an outer-product bound on explicit vectors. -/
theorem value_gramPair_ge_of_outer (A : Matrix r n ℂ) (C : Matrix s n ℂ)
    {lambda₀ lambda₁ c : ℝ} (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0)
    (hR : ∀ v : r ⊕ s → ℂ,
      blockMass C*(pinchLeft (outer v)).mat.trace.re = blockMass A*(pinchRight (outer v)).mat.trace.re →
      c*(outer v).mat.trace.re ≤ value (outer v) lambda₀ lambda₁) :
    c*(blockMass A+blockMass C) ≤ value (gramPair A C) lambda₀ lambda₁ := by
  have hi : ∑ f : n → Bool, c*(decomposition A C f).mat.trace.re ≤
      ∑ f : n → Bool, value (decomposition A C f) lambda₀ lambda₁ := by
    apply Finset.sum_le_sum
    intro f hf
    rw [decomposition_eq_outer]
    apply hR
    rw [← decomposition_eq_outer]
    exact decomposition_mass A C f
  have hs := sum_value_le_value_sum Finset.univ (decomposition A C) hl₀ hl₁
    (fun f _ => decomposition_posSemidef A C f)
  rw [decomposition_sum_eq] at hs
  have ht : ∑ f : n → Bool, (decomposition A C f).mat.trace.re = blockMass A+blockMass C := by
    have hh := map_sum (traceHerm (k := r ⊕ s)) (decomposition A C) Finset.univ
    rw [decomposition_sum_eq,traceHerm_apply,gramPair_trace] at hh
    exact hh.symm
  rw [← Finset.mul_sum,ht] at hi
  exact hi.trans hs


end QubitAdditivity.BetaOuterReduction
