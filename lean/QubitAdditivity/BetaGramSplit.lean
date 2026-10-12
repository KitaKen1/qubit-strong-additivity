import QubitAdditivity.BetaSignFrame
import QubitAdditivity.Blocks

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

namespace QubitAdditivity.BetaGramSplit
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

open BetaSignFrame BetaTC4Structure
variable {n m r s : Type*} [Fintype n] [Fintype m] [Fintype r] [Fintype s]
  [DecidableEq n] [DecidableEq m] [DecidableEq r] [DecidableEq s]

def outer (v : m → ℂ) : HermitianMat m ℂ :=
  ⟨Matrix.vecMulVec v (star v),(Matrix.posSemidef_vecMulVec_self_star v).1⟩

theorem outer_posSemidef (v : m → ℂ) : (outer v).mat.PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star v

theorem outer_rank_le_one (v : m → ℂ) : (outer v).mat.rank ≤ 1 :=
  Matrix.rank_vecMulVec_le v (star v)

theorem mat_sum {ι : Type*} (t : Finset ι) (J : ι → HermitianMat m ℂ) :
    (∑ i ∈ t, J i).mat = ∑ i ∈ t, (J i).mat := by
  exact map_sum (BetaLog.inclusion (n := m)) J t

/-- Sum the rank-at-most-one column Gram matrices, with empty column types included. -/
theorem sum_outer_columns (Y : Matrix m n ℂ) :
    (∑ j, outer (fun i => Y i j)).mat = Y*Yᴴ := by
  have h : (∑ j, Matrix.vecMulVec (fun i => Y i j) (star (fun i => Y i j)) : Matrix m m ℂ) = Y*Yᴴ := by
    ext i k
    simp only [Matrix.sum_apply,Matrix.vecMulVec_apply,Pi.star_apply,Matrix.mul_apply,Matrix.conjTranspose_apply]
  exact (mat_sum Finset.univ (fun j => outer (fun i => Y i j))).trans h

/-- Exact, unnormalized rank-one decomposition supplied by the finite sign frame. -/
theorem sum_image_outer (X : Matrix m n ℂ) (H : HermitianMat n ℂ) :
    (∑ f : n → Bool, outer (fun i => (X*spectralFrame H) i f)).mat =
      (Fintype.card (n → Bool) : ℂ) • (X*Xᴴ) := by
  rw [sum_outer_columns,imageFrame_gram]

def rightGram (A : Matrix r n ℂ) : HermitianMat n ℂ :=
  ⟨Aᴴ*A,Matrix.isHermitian_conjTranspose_mul_self A⟩

theorem rightGram_trace (A : Matrix r n ℂ) : (rightGram A).mat.trace.re = blockMass A := by
  exact congrArg Complex.re (Matrix.trace_mul_comm Aᴴ A)

/-- One traceless constraint enforces the two required block-mass proportions. -/
def balanceMatrix (A : Matrix r n ℂ) (C : Matrix s n ℂ) : HermitianMat n ℂ :=
  blockMass C • rightGram A-blockMass A • rightGram C

theorem balanceMatrix_trace_zero (A : Matrix r n ℂ) (C : Matrix s n ℂ) :
    (balanceMatrix A C).mat.trace = 0 := by
  have hr : (balanceMatrix A C).mat.trace.re = 0 := by
    simp only [balanceMatrix,HermitianMat.mat_sub,HermitianMat.mat_smul,Matrix.trace_sub,
      Matrix.trace_smul,Complex.sub_re,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero,rightGram_trace]
    ring
  have he : ((balanceMatrix A C).mat.trace.re : ℂ) = (balanceMatrix A C).mat.trace := by
    have h₁ : (balanceMatrix A C).trace = (balanceMatrix A C).mat.trace.re := by
      exact HermitianMat.trace_eq_re_trace (balanceMatrix A C)
    have h₂ : ((balanceMatrix A C).trace : ℂ) = (balanceMatrix A C).mat.trace := by
      exact HermitianMat.trace_eq_trace_rc (balanceMatrix A C)
    rw [h₁] at h₂
    exact h₂
  rw [hr] at he
  exact he.symm

theorem rightGram_pairing (A : Matrix r n ℂ) (v : n → ℂ) :
    star v ⬝ᵥ ((rightGram A).mat *ᵥ v) = star (A *ᵥ v) ⬝ᵥ (A *ᵥ v) := by
  change star v ⬝ᵥ ((Aᴴ*A) *ᵥ v) = _
  rw [← Matrix.mulVec_mulVec,dotProduct_mulVec,← star_mulVec]

/-- Every frame column balances the two blocks before normalization. -/
theorem imageFrame_balance (A : Matrix r n ℂ) (C : Matrix s n ℂ) (f : n → Bool) :
    blockMass C*(star (A *ᵥ fun i => spectralFrame (balanceMatrix A C) i f) ⬝ᵥ
      (A *ᵥ fun i => spectralFrame (balanceMatrix A C) i f)).re =
    blockMass A*(star (C *ᵥ fun i => spectralFrame (balanceMatrix A C) i f) ⬝ᵥ
      (C *ᵥ fun i => spectralFrame (balanceMatrix A C) i f)).re := by
  have hq := spectralFrame_quadratic_zero (balanceMatrix_trace_zero A C) f
  change BetaComparison.pairing (fun i => spectralFrame (balanceMatrix A C) i f)
    (balanceMatrix A C).mat (fun i => spectralFrame (balanceMatrix A C) i f) = 0 at hq
  have hm : (balanceMatrix A C).mat = blockMass C • (rightGram A).mat-blockMass A • (rightGram C).mat := rfl
  rw [hm,BetaComparison.pairing_sub,BetaComparison.pairing_smul_matrix,
    BetaComparison.pairing_smul_matrix] at hq
  have hr := congrArg Complex.re hq
  simp only [Complex.sub_re,Complex.real_smul,Complex.zero_re,BetaComparison.pairing] at hr
  rw [rightGram_pairing,rightGram_pairing] at hr
  simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using sub_eq_zero.mp hr

def balancedAtom (A : Matrix r n ℂ) (C : Matrix s n ℂ) (f : n → Bool) : HermitianMat (r ⊕ s) ℂ :=
  outer (Sum.elim (A *ᵥ fun i => spectralFrame (balanceMatrix A C) i f)
    (C *ᵥ fun i => spectralFrame (balanceMatrix A C) i f))

theorem balancedAtom_posSemidef (A : Matrix r n ℂ) (C : Matrix s n ℂ) (f : n → Bool) :
    (balancedAtom A C f).mat.PosSemidef := outer_posSemidef _

theorem balancedAtom_rank_le_one (A : Matrix r n ℂ) (C : Matrix s n ℂ) (f : n → Bool) :
    (balancedAtom A C f).mat.rank ≤ 1 := outer_rank_le_one _

theorem outer_trace (v : m → ℂ) : (outer v).mat.trace = star v ⬝ᵥ v := by
  change (Matrix.vecMulVec v (star v)).trace = _
  rw [Matrix.trace_vecMulVec,dotProduct_comm]

theorem balancedAtom_mass (A : Matrix r n ℂ) (C : Matrix s n ℂ) (f : n → Bool) :
    blockMass C*(pinchLeft (balancedAtom A C f)).mat.trace.re =
      blockMass A*(pinchRight (balancedAtom A C f)).mat.trace.re := by
  have hl : pinchLeft (balancedAtom A C f) = outer (A *ᵥ fun i => spectralFrame (balanceMatrix A C) i f) := by
    apply HermitianMat.ext
    rfl
  have hr : pinchRight (balancedAtom A C f) = outer (C *ᵥ fun i => spectralFrame (balanceMatrix A C) i f) := by
    apply HermitianMat.ext
    rfl
  rw [hl,hr,outer_trace,outer_trace]
  exact imageFrame_balance A C f

/-- The column family reproduces the original two-row-block Gram matrix exactly up to its size. -/
theorem sum_balancedAtom (A : Matrix r n ℂ) (C : Matrix s n ℂ) :
    (∑ f : n → Bool, balancedAtom A C f).mat =
      (Fintype.card (n → Bool) : ℂ) • (Matrix.fromRows A C*(Matrix.fromRows A C)ᴴ) := by
  have he (f : n → Bool) : balancedAtom A C f =
      outer (fun i => (Matrix.fromRows A C*spectralFrame (balanceMatrix A C)) i f) := by
    have hv : Sum.elim (A *ᵥ fun i => spectralFrame (balanceMatrix A C) i f)
        (C *ᵥ fun i => spectralFrame (balanceMatrix A C) i f) =
        (fun i => (Matrix.fromRows A C*spectralFrame (balanceMatrix A C)) i f) := by
      funext i
      cases i <;> rfl
    unfold balancedAtom
    rw [hv]
  simp_rw [he]
  exact sum_image_outer (Matrix.fromRows A C) (balanceMatrix A C)

theorem outer_sqrt_smul {c : ℝ} (hc : 0 ≤ c) (v : m → ℂ) :
    outer (Real.sqrt c • v) = c • outer v := by
  apply HermitianMat.ext
  change Matrix.vecMulVec (Real.sqrt c • v) (star (Real.sqrt c • v)) = c • Matrix.vecMulVec v (star v)
  rw [star_smul,star_trivial,Matrix.smul_vecMulVec,Matrix.vecMulVec_smul,smul_smul,Real.mul_self_sqrt hc]

def decomposition (A : Matrix r n ℂ) (C : Matrix s n ℂ) (f : n → Bool) : HermitianMat (r ⊕ s) ℂ :=
  (Fintype.card (n → Bool) : ℝ)⁻¹ • balancedAtom A C f

theorem decomposition_posSemidef (A : Matrix r n ℂ) (C : Matrix s n ℂ) (f : n → Bool) :
    (decomposition A C f).mat.PosSemidef :=
  (balancedAtom_posSemidef A C f).smul (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem decomposition_rank_le_one (A : Matrix r n ℂ) (C : Matrix s n ℂ) (f : n → Bool) :
    (decomposition A C f).mat.rank ≤ 1 := by
  have hc : 0 ≤ (Fintype.card (n → Bool) : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  unfold decomposition balancedAtom
  rw [← outer_sqrt_smul hc]
  exact outer_rank_le_one _

theorem decomposition_mass (A : Matrix r n ℂ) (C : Matrix s n ℂ) (f : n → Bool) :
    blockMass C*(pinchLeft (decomposition A C f)).mat.trace.re =
      blockMass A*(pinchRight (decomposition A C f)).mat.trace.re := by
  have hl : pinchLeft (decomposition A C f) =
      (Fintype.card (n → Bool) : ℝ)⁻¹ • pinchLeft (balancedAtom A C f) := rfl
  have hr : pinchRight (decomposition A C f) =
      (Fintype.card (n → Bool) : ℝ)⁻¹ • pinchRight (balancedAtom A C f) := rfl
  rw [hl,hr]
  simp only [HermitianMat.mat_smul,Matrix.trace_smul,Complex.real_smul,Complex.mul_re,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have hi := congrArg (fun q : ℝ => (Fintype.card (n → Bool) : ℝ)⁻¹*q) (balancedAtom_mass A C f)
  linarith only [hi]

/-- Exact PSD rank-one decomposition with the two block masses in the original ratio. -/
theorem sum_decomposition (A : Matrix r n ℂ) (C : Matrix s n ℂ) :
    (∑ f : n → Bool, decomposition A C f).mat = Matrix.fromRows A C*(Matrix.fromRows A C)ᴴ := by
  unfold decomposition
  rw [← Finset.smul_sum,HermitianMat.mat_smul,sum_balancedAtom]
  have hc : (Fintype.card (n → Bool) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he (M : Matrix (r ⊕ s) (r ⊕ s) ℂ) :
      (Fintype.card (n → Bool) : ℂ) • M = (Fintype.card (n → Bool) : ℝ) • M := by
    ext i j
    simp [Complex.real_smul]
  rw [he,smul_smul,inv_mul_cancel₀ hc,one_smul]

def gramPair (A : Matrix r n ℂ) (C : Matrix s n ℂ) : HermitianMat (r ⊕ s) ℂ :=
  ⟨Matrix.fromRows A C*(Matrix.fromRows A C)ᴴ,Matrix.isHermitian_mul_conjTranspose_self _⟩

theorem decomposition_sum_eq (A : Matrix r n ℂ) (C : Matrix s n ℂ) :
    ∑ f : n → Bool, decomposition A C f = gramPair A C := by
  apply HermitianMat.ext
  exact sum_decomposition A C

theorem gramPair_trace (A : Matrix r n ℂ) (C : Matrix s n ℂ) :
    (gramPair A C).mat.trace.re = blockMass A+blockMass C := by
  change (Matrix.fromRows A C*(Matrix.fromRows A C)ᴴ).trace.re = _
  rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,Matrix.fromRows_mul_fromCols]
  simp [Matrix.trace,Fintype.sum_sum_type,Matrix.fromBlocks,blockMass]

/-- The rank-one comparison is the only remaining input needed to compare arbitrary Gram factors.
The reduction allows zero atoms and arbitrary finite rectangular column dimensions. -/
theorem value_gramPair_ge_of_rank_one (A : Matrix r n ℂ) (C : Matrix s n ℂ)
    {lambda₀ lambda₁ c : ℝ} (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0)
    (hR : ∀ H : HermitianMat (r ⊕ s) ℂ, H.mat.PosSemidef → H.mat.rank ≤ 1 →
      blockMass C*(pinchLeft H).mat.trace.re = blockMass A*(pinchRight H).mat.trace.re →
      c*H.mat.trace.re ≤ value H lambda₀ lambda₁) :
    c*(blockMass A+blockMass C) ≤ value (gramPair A C) lambda₀ lambda₁ := by
  have hi : ∑ f : n → Bool, c*(decomposition A C f).mat.trace.re ≤
      ∑ f : n → Bool, value (decomposition A C f) lambda₀ lambda₁ := by
    apply Finset.sum_le_sum
    intro f hf
    exact hR _ (decomposition_posSemidef A C f) (decomposition_rank_le_one A C f) (decomposition_mass A C f)
  have hs := sum_value_le_value_sum Finset.univ (decomposition A C) hl₀ hl₁
    (fun f _ => decomposition_posSemidef A C f)
  rw [decomposition_sum_eq] at hs
  have ht : ∑ f : n → Bool, (decomposition A C f).mat.trace.re = blockMass A+blockMass C := by
    have hh := map_sum (traceHerm (k := r ⊕ s)) (decomposition A C) Finset.univ
    rw [decomposition_sum_eq,traceHerm_apply,gramPair_trace] at hh
    exact hh.symm
  rw [← Finset.mul_sum,ht] at hi
  exact hi.trans hs

end QubitAdditivity.BetaGramSplit

