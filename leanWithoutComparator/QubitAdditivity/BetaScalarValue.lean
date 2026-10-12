import QubitAdditivity.BetaScalarMinimum
import QubitAdditivity.TC4
import QubitAdditivity.Imported.TensorEntropy

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

namespace QubitAdditivity.BetaScalarValue
open BetaDual BetaEntropy BetaDualValue BetaTC4Convex BetaScalarMinimum BetaGramSplit

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


/-- The scalar support value, expressed with the actual CFC entropy. -/
def scalarDifference (x y z w : ℝ) : ℝ :=
  x*Real.log x+y*Real.log y+z*Real.log z+w*Real.log w-psi (comparison x y z w)

theorem scalarBlock_trace (c : ℝ) : (scalarBlock c).mat.trace.re = c := by
  simp [scalarBlock,Matrix.trace,Matrix.smul_apply,Complex.real_smul,Fin.sum_univ_one]

theorem psi_scalarBlock (c : ℝ) : psi (scalarBlock c) = c*Real.log c := by
  rw [psi_eq_trace,logarithm_scalarBlock]
  change ((c • (1 : Matrix (Fin 1) (Fin 1) ℂ))*(Real.log c • 1)).trace.re = _
  rw [Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,smul_smul]
  simp [Matrix.trace,Matrix.smul_apply,Complex.real_smul,Fin.sum_univ_one]

theorem pinchLeft_rankOne {x : ℝ} (hx : 0 ≤ x) (z : ℝ) : pinchLeft (rankOne x z) = scalarBlock x := by
  apply HermitianMat.ext
  change ((rankOne x z).mat).submatrix Sum.inl Sum.inl = x • (1 : Matrix (Fin 1) (Fin 1) ℂ)
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i
  subst j
  simp [rankOne,outer,Matrix.submatrix_apply,Matrix.vecMulVec_apply,Complex.real_smul,
    ← Complex.ofReal_mul,Real.mul_self_sqrt hx]

theorem pinchRight_rankOne (x : ℝ) {z : ℝ} (hz : 0 ≤ z) : pinchRight (rankOne x z) = scalarBlock z := by
  apply HermitianMat.ext
  change ((rankOne x z).mat).submatrix Sum.inr Sum.inr = z • (1 : Matrix (Fin 1) (Fin 1) ℂ)
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i
  subst j
  simp [rankOne,outer,Matrix.submatrix_apply,Matrix.vecMulVec_apply,Complex.real_smul,
    ← Complex.ofReal_mul,Real.mul_self_sqrt hz]

theorem psi_pinching_rankOne {x z : ℝ} (hx : 0 ≤ x) (hz : 0 ≤ z) :
    psi (pinching (rankOne x z)) = x*Real.log x+z*Real.log z := by
  change psi (diagonal (pinchLeft (rankOne x z),pinchRight (rankOne x z))) = _
  rw [pinchLeft_rankOne hx,pinchRight_rankOne x hz,psi_diagonal,psi_scalarBlock,psi_scalarBlock]

theorem penalty_candidate (y w lambda₀ lambda₁ : ℝ) :
    linearPenalty lambda₀ lambda₁ (candidate y w) = lambda₀*y+lambda₁*w := by
  rw [linearPenalty_apply]
  change lambda₀*(scalarBlock y).mat.trace.re+lambda₁*(scalarBlock w).mat.trace.re = _
  rw [scalarBlock_trace,scalarBlock_trace]

/-- Evaluate the genuine infimum at the proven scalar minimizer. -/
theorem value_rankOne_eq {x y z w : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hw : 0 < w) :
    value (rankOne x z) (lambdaLeft x y z w) (lambdaRight x y z w)+
      lambdaLeft x y z w*y+lambdaRight x y z w*w = scalarDifference x y z w := by
  rw [value,minimumValue_eq_candidate hx hy hz hw,psi_pinching_rankOne hx.le hz.le,objective]
  change x*Real.log x+z*Real.log z+
    (psi (scalarBlock y)+psi (scalarBlock w)-psi (comparison x y z w)-
      (lambdaLeft x y z w*(scalarBlock y).mat.trace.re+
        lambdaRight x y z w*(scalarBlock w).mat.trace.re)) +
    lambdaLeft x y z w*y+lambdaRight x y z w*w = _
  rw [psi_scalarBlock,psi_scalarBlock,scalarBlock_trace,scalarBlock_trace]
  unfold scalarDifference
  ring

/-- Scalar entropy comparison for arbitrary PSD block candidates, including their boundary. -/
theorem scalar_primal_lower_bound {x y z w : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hw : 0 < w)
    {W : Blocks (Fin 1) (Fin 1)} (hW : W ∈ BetaDual.positiveCone) :
    scalarDifference x y z w + linearPenalty (lambdaLeft x y z w) (lambdaRight x y z w) W-
      (lambdaLeft x y z w*y+lambdaRight x y z w*w) ≤
    psi (pinching (rankOne x z))+psi (diagonal W)-psi (rankOne x z+diagonal W) := by
  have hi := value_le_primal (lambda₀ := lambdaLeft x y z w) (lambda₁ := lambdaRight x y z w)
    (rankOne_posSemidef x z) (lambdaLeft_neg hx hy hw) (lambdaRight_neg hz hy hw) hW
  have he := value_rankOne_eq hx hy hz hw
  linarith


/-- Identify the finite one-dimensional block comparison with the target TC4 scalar matrix. -/
theorem comparison_reindex {x y z w : ℝ} (hx : 0 ≤ x) (hz : 0 ≤ z) :
    Matrix.reindex (finSumFinEquiv : Index ≃ Fin 2) finSumFinEquiv (comparison x y z w).mat =
      tc4ScalarMatrix x y z w := by
  have h0 : (finSumFinEquiv : Index ≃ Fin 2).symm 0 = .inl 0 := rfl
  have h1 : (finSumFinEquiv : Index ≃ Fin 2).symm 1 = .inr 0 := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [h0,h1,Matrix.reindex,Matrix.submatrix_apply,comparison,rankOne,outer,BetaDual.diagonal,candidate,
      scalarBlock,tc4ScalarMatrix,Matrix.fromBlocks,Matrix.vecMulVec_apply,
      Complex.real_smul,← Complex.ofReal_mul,← Complex.ofReal_add,
      Real.mul_self_sqrt hx,Real.mul_self_sqrt hz,Real.sqrt_mul hx z,mul_comm]

theorem psi_comparison_eq {x y z w : ℝ} (hx : 0 ≤ x) (hz : 0 ≤ z) :
    psi (comparison x y z w) = -OpenAIEntropy.entropy (tc4ScalarMatrix x y z w) := by
  have he := OpenAIEntropy.entropy_reindex (finSumFinEquiv : Index ≃ Fin 2) (comparison x y z w).H
  rw [comparison_reindex hx hz] at he
  exact congrArg Neg.neg he.symm

theorem scalarDifference_eq {x y z w : ℝ} (hx : 0 ≤ x) (hz : 0 ≤ z) :
    scalarDifference x y z w =
      x*Real.log x+y*Real.log y+z*Real.log z+w*Real.log w+
        OpenAIEntropy.entropy (tc4ScalarMatrix x y z w) := by
  rw [scalarDifference,psi_comparison_eq hx hz,sub_neg_eq_add]

end QubitAdditivity.BetaScalarValue
