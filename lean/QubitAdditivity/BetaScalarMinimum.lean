import QubitAdditivity.BetaLogOrder
import QubitAdditivity.BetaGramSplit

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

namespace QubitAdditivity.BetaScalarMinimum
open BetaDualBoundary BetaDual BetaDualConvex BetaDualInterior BetaDualDerivative BetaMinimizer BetaEntropy BetaDualValue BetaDualExistence

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

open BetaTC4Convex BetaLogOrder BetaGramSplit
local instance scalarCFC : ContinuousFunctionalCalculus ℝ (Matrix (Fin 1) (Fin 1) ℂ) Matrix.IsHermitian := by
  letI : TopologicalSpace (Matrix (Fin 1) (Fin 1) ℂ) := inferInstanceAs (TopologicalSpace (Fin 1 → Fin 1 → ℂ))
  letI : AddCommGroup (Matrix (Fin 1) (Fin 1) ℂ) := Matrix.addCommGroup
  letI : Module ℝ (Matrix (Fin 1) (Fin 1) ℂ) := Matrix.module
  convert! (Matrix.IsHermitian.instContinuousFunctionalCalculus (𝕜 := ℂ) (n := Fin 1)) using 1

abbrev Index := Fin 1 ⊕ Fin 1

def scalarBlock (c : ℝ) : HermitianMat (Fin 1) ℂ := c • 1
def candidate (y w : ℝ) : Blocks (Fin 1) (Fin 1) := (scalarBlock y,scalarBlock w)
def rankOne (x z : ℝ) : HermitianMat Index ℂ :=
  outer (Sum.elim (fun _ : Fin 1 => (Real.sqrt x : ℂ)) (fun _ : Fin 1 => (Real.sqrt z : ℂ)))
def comparison (x y z w : ℝ) : HermitianMat Index ℂ := rankOne x z+diagonal (candidate y w)
def lambdaLeft (x y z w : ℝ) : ℝ := Real.log y-(BetaPowers.logarithm (comparison x y z w).mat (.inl 0) (.inl 0)).re
def lambdaRight (x y z w : ℝ) : ℝ := Real.log w-(BetaPowers.logarithm (comparison x y z w).mat (.inr 0) (.inr 0)).re

theorem rankOne_posSemidef (x z : ℝ) : (rankOne x z).mat.PosSemidef := outer_posSemidef _

theorem rankOne_left_diagonal {x : ℝ} (hx : 0 ≤ x) (z : ℝ) :
    ((rankOne x z).mat (.inl 0) (.inl 0)).re = x := by
  change ((Real.sqrt x : ℂ)*star (Real.sqrt x : ℂ)).re = x
  simp [← Complex.ofReal_mul,Real.mul_self_sqrt hx]

theorem rankOne_right_diagonal (x : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    ((rankOne x z).mat (.inr 0) (.inr 0)).re = z := by
  change ((Real.sqrt z : ℂ)*star (Real.sqrt z : ℂ)).re = z
  simp [← Complex.ofReal_mul,Real.mul_self_sqrt hz]

theorem scalarBlock_posDef {c : ℝ} (hc : 0 < c) : (scalarBlock c).mat.PosDef :=
  Matrix.PosDef.one.smul hc

theorem candidate_positive {y w : ℝ} (hy : 0 < y) (hw : 0 < w) : candidate y w ∈ positiveInterior :=
  ⟨scalarBlock_posDef hy,scalarBlock_posDef hw⟩

theorem diagonal_candidate_posDef {y w : ℝ} (hy : 0 < y) (hw : 0 < w) :
    (diagonal (candidate y w)).mat.PosDef := BetaBlocks.diagonal_posDef (scalarBlock_posDef hy) (scalarBlock_posDef hw)

theorem comparison_posDef (x z : ℝ) {y w : ℝ} (hy : 0 < y) (hw : 0 < w) :
    (comparison x y z w).mat.PosDef := by
  change ((rankOne x z).mat+(diagonal (candidate y w)).mat).PosDef
  rw [add_comm]
  exact (diagonal_candidate_posDef hy hw).add_posSemidef (rankOne_posSemidef x z)

theorem logarithm_scalarBlock (c : ℝ) : BetaPowers.logarithm (scalarBlock c).mat =
    Real.log c • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  change cfc Real.log (c • (1 : Matrix (Fin 1) (Fin 1) ℂ)) = _
  have h := cfc_algebraMap (A := Matrix (Fin 1) (Fin 1) ℂ) c Real.log
  simpa only [Algebra.algebraMap_eq_smul_one] using h

theorem log_candidate_left (y w : ℝ) :
    (BetaPowers.logarithm (diagonal (candidate y w)).mat (.inl 0) (.inl 0)).re = Real.log y := by
  rw [logarithm_diagonal]
  change (BetaPowers.logarithm (scalarBlock y).mat 0 0).re = _
  rw [logarithm_scalarBlock]
  simp [Matrix.smul_apply,Complex.real_smul]

theorem log_candidate_right (y w : ℝ) :
    (BetaPowers.logarithm (diagonal (candidate y w)).mat (.inr 0) (.inr 0)).re = Real.log w := by
  rw [logarithm_diagonal]
  change (BetaPowers.logarithm (scalarBlock w).mat 0 0).re = _
  rw [logarithm_scalarBlock]
  simp [Matrix.smul_apply,Complex.real_smul]

/-- Strictly negative dual coefficients follow from the noncommutative log derivative. -/
theorem lambdaLeft_neg {x y z w : ℝ} (hx : 0 < x) (hy : 0 < y) (hw : 0 < w) :
    lambdaLeft x y z w < 0 := by
  have hi := logarithm_diagonal_lt (i := .inl 0) (diagonal_candidate_posDef hy hw) (rankOne_posSemidef x z)
    (by simpa only [rankOne_left_diagonal hx.le z] using hx)
  rw [log_candidate_left] at hi
  unfold lambdaLeft comparison
  rw [add_comm]
  exact sub_neg.mpr hi

theorem lambdaRight_neg {x y z w : ℝ} (hz : 0 < z) (hy : 0 < y) (hw : 0 < w) :
    lambdaRight x y z w < 0 := by
  have hi := logarithm_diagonal_lt (i := .inr 0) (diagonal_candidate_posDef hy hw) (rankOne_posSemidef x z)
    (by simpa only [rankOne_right_diagonal x hz.le] using hz)
  rw [log_candidate_right] at hi
  unfold lambdaRight comparison
  rw [add_comm]
  exact sub_neg.mpr hi

/-- The chosen coefficients make the actual matrix residual zero at the scalar candidate. -/
theorem candidate_stationary (x y z w : ℝ) :
    stationaryResidual (rankOne x z) (lambdaLeft x y z w) (lambdaRight x y z w) (candidate y w) = 0 := by
  apply Prod.ext
  · apply HermitianMat.ext
    change BetaPowers.logarithm (scalarBlock y).mat-
      (BetaPowers.logarithm (comparison x y z w).mat).submatrix Sum.inl Sum.inl-
      lambdaLeft x y z w • (1 : Matrix (Fin 1) (Fin 1) ℂ) = 0
    rw [logarithm_scalarBlock]
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst i
    subst j
    simp only [Matrix.sub_apply,Matrix.smul_apply,Matrix.submatrix_apply,Matrix.one_apply_eq,
      Complex.real_smul,mul_one,Matrix.zero_apply]
    have hr : ((BetaPowers.logarithm (comparison x y z w).mat (.inl 0) (.inl 0)).re : ℂ) =
        BetaPowers.logarithm (comparison x y z w).mat (.inl 0) (.inl 0) :=
      (BetaPowers.logarithm_isHermitian (comparison x y z w).mat).coe_re_apply_self (.inl 0)
    rw [← hr,lambdaLeft]
    push_cast
    ring
  · apply HermitianMat.ext
    change BetaPowers.logarithm (scalarBlock w).mat-
      (BetaPowers.logarithm (comparison x y z w).mat).submatrix Sum.inr Sum.inr-
      lambdaRight x y z w • (1 : Matrix (Fin 1) (Fin 1) ℂ) = 0
    rw [logarithm_scalarBlock]
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst i
    subst j
    simp only [Matrix.sub_apply,Matrix.smul_apply,Matrix.submatrix_apply,Matrix.one_apply_eq,
      Complex.real_smul,mul_one,Matrix.zero_apply]
    have hr : ((BetaPowers.logarithm (comparison x y z w).mat (.inr 0) (.inr 0)).re : ℂ) =
        BetaPowers.logarithm (comparison x y z w).mat (.inr 0) (.inr 0) :=
      (BetaPowers.logarithm_isHermitian (comparison x y z w).mat).coe_re_apply_self (.inr 0)
    rw [← hr,lambdaRight]
    push_cast
    ring

theorem candidate_isMinOn (x z : ℝ) {y w : ℝ} (hy : 0 < y) (hw : 0 < w) :
    IsMinOn (objective (rankOne x z) (lambdaLeft x y z w) (lambdaRight x y z w)) positiveCone (candidate y w) :=
  isMinOn_positiveCone_of_stationary_psd (rankOne_posSemidef x z) (candidate_positive hy hw)
    (candidate_stationary x y z w)

theorem minimumValue_eq_candidate {x y z w : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hw : 0 < w) :
    minimumValue (rankOne x z) (lambdaLeft x y z w) (lambdaRight x y z w) =
      objective (rankOne x z) (lambdaLeft x y z w) (lambdaRight x y z w) (candidate y w) :=
  minimumValue_eq_of_isMinOn (rankOne_posSemidef x z) (lambdaLeft_neg hx hy hw) (lambdaRight_neg hz hy hw)
    ⟨(scalarBlock_posDef hy).posSemidef,(scalarBlock_posDef hw).posSemidef⟩ (candidate_isMinOn x z hy hw)

end QubitAdditivity.BetaScalarMinimum




