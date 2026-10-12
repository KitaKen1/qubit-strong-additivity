import QubitAdditivity.BetaTC4Convex

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

namespace QubitAdditivity.BetaLogOrder
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

open BetaLog
variable {n : Type*} [Fintype n] [DecidableEq n]

def diagonalEvalLM (i : n) : Matrix n n ℂ →ₗ[ℝ] ℝ where
  toFun A := (A i i).re
  map_add' A B := by simp
  map_smul' c A := by simp [Complex.real_smul]

def diagonalEval (i : n) : Matrix n n ℂ →L[ℝ] ℝ := (diagonalEvalLM i).toContinuousLinearMap

@[simp] theorem diagonalEval_apply (i : n) (A : Matrix n n ℂ) : diagonalEval i A = (A i i).re := rfl

theorem diagonal_integral (i : n) {f : ℝ → Matrix n n ℂ}
    (hf : IntervalIntegrable f MeasureTheory.volume 0 1) :
    ((∫ t in (0 : ℝ)..1, f t) i i).re = ∫ t in (0 : ℝ)..1, (f t i i).re := by
  exact ((diagonalEval i).intervalIntegral_comp_comm hf).symm

theorem sandwich_posSemidef {A : Matrix n n ℂ} (hA : A.PosDef)
    {H : HermitianMat n ℂ} (hH : H.mat.PosSemidef) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (inverseSegment A t*H.mat*inverseSegment A t).PosSemidef := by
  have hR : (inverseSegment A t).IsHermitian := (segment_posDef hA ht).inv.1
  simpa only [hR.eq] using hH.conjTranspose_mul_mul_same (inverseSegment A t)

theorem continuousOn_diagonal_sandwich {A : Matrix n n ℂ} (hA : A.PosDef)
    (H : HermitianMat n ℂ) (i : n) :
    ContinuousOn (fun t : ℝ => (inverseSegment A t*H.mat*inverseSegment A t) i i |>.re)
      (Icc (0 : ℝ) 1) := by
  have hc : ContinuousOn (fun t : ℝ => inverseSegment A t*H.mat*inverseSegment A t) (Icc (0 : ℝ) 1) :=
    ((continuousOn_inverseSegment hA).mul continuousOn_const).mul (continuousOn_inverseSegment hA)
  exact (diagonalEval i).continuous.comp_continuousOn hc

/-- Noncommutative log differentiation is positive on PSD directions. -/
theorem logDeriv_diagonal_nonneg {A : Matrix n n ℂ} (hA : A.PosDef)
    {H : HermitianMat n ℂ} (hH : H.mat.PosSemidef) (i : n) :
    0 ≤ (logDeriv A H i i).re := by
  rw [logDeriv_apply hA]
  have hc : ContinuousOn (fun t : ℝ => inverseSegment A t*H.mat*inverseSegment A t) (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    convert! ((continuousOn_inverseSegment hA).mul continuousOn_const).mul (continuousOn_inverseSegment hA) using 1
  rw [diagonal_integral i hc.intervalIntegrable]
  apply intervalIntegral.integral_nonneg zero_le_one
  intro t ht
  exact (Complex.nonneg_iff.mp (sandwich_posSemidef hA hH ht).diag_nonneg).1

/-- A positive diagonal direction gives a strictly positive logarithm differential there.
The t=0 inverse-segment sandwich equals H, so no strict operator order is needed. -/
theorem logDeriv_diagonal_pos {A : Matrix n n ℂ} (hA : A.PosDef)
    {H : HermitianMat n ℂ} (hH : H.mat.PosSemidef) {i : n} (hi : 0 < (H.mat i i).re) :
    0 < (logDeriv A H i i).re := by
  rw [logDeriv_apply hA]
  have hc : ContinuousOn (fun t : ℝ => inverseSegment A t*H.mat*inverseSegment A t) (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    convert! ((continuousOn_inverseSegment hA).mul continuousOn_const).mul (continuousOn_inverseSegment hA) using 1
  rw [diagonal_integral i hc.intervalIntegrable]
  apply intervalIntegral.integral_pos zero_lt_one (continuousOn_diagonal_sandwich hA H i)
  · intro t ht
    exact (Complex.nonneg_iff.mp (sandwich_posSemidef hA hH ⟨ht.1.le,ht.2⟩).diag_nonneg).1
  · refine ⟨0,⟨le_rfl,zero_le_one⟩,?_⟩
    simpa [inverseSegment,BetaLog.segment] using hi

theorem hasDerivAt_log_diagonal (W H : HermitianMat n ℂ) (i : n) {t : ℝ}
    (ht : (W+t • H).mat.PosDef) :
    HasDerivAt (fun u : ℝ => (BetaPowers.logarithm (W+u • H).mat i i).re)
      (logDeriv (W+t • H).mat H i i).re t := by
  have hl : HasDerivAt (fun u : ℝ => W+u • H) H t := by
    convert! ((hasDerivAt_id t).smul_const H).const_add W using 1 <;> simp
  have hd := (hasFDerivAt_logarithm ht).comp_hasDerivAt t hl
  exact (diagonalEval i).hasFDerivAt.comp_hasDerivAt t hd

/-- Strict increase of any positively affected diagonal under an arbitrary PSD increment. -/
theorem logarithm_diagonal_lt {W H : HermitianMat n ℂ} (hW : W.mat.PosDef)
    (hH : H.mat.PosSemidef) {i : n} (hi : 0 < (H.mat i i).re) :
    (BetaPowers.logarithm W.mat i i).re < (BetaPowers.logarithm (W+H).mat i i).re := by
  let f : ℝ → ℝ := fun t => (BetaPowers.logarithm (W+t • H).mat i i).re
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (W+t • H).mat.PosDef := by
    change (W.mat+t • H.mat).PosDef
    exact hW.add_posSemidef (hH.smul ht.1)
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt f (logDeriv (W+t • H).mat H i i).re t := hasDerivAt_log_diagonal W H i (hp t ht)
  have hm : StrictMonoOn f (Icc (0 : ℝ) 1) := strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (fun t ht => (hd t ht).continuousAt.continuousWithinAt) (by
      intro t ht
      have ht' := interior_subset ht
      rw [(hd t ht').deriv]
      exact logDeriv_diagonal_pos (hp t ht') hH hi)
  simpa only [f,zero_smul,one_smul,add_zero] using hm (by simp) (by simp) zero_lt_one

end QubitAdditivity.BetaLogOrder




