import QubitAdditivity.BetaLogKM
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

namespace QubitAdditivity.BetaLogRegularity
open BetaLog

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


variable {n : Type*} [Fintype n] [DecidableEq n]

theorem continuousAt_kernelDeriv {A : HermitianMat n ℂ} (hA : A.mat.PosDef)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ContinuousAt (fun z : HermitianMat n ℂ × ℝ => kernelDeriv z.1.mat z.2) (A,t) := by
  have hc := continuousAt_inverseSegment hA ht
  have hm : Continuous (fun R : Matrix n n ℂ => (sandwich R).comp inclusion) := by
    unfold sandwich
    fun_prop
  exact hm.continuousAt.comp hc

/-- The noncommutative log differential is continuous in operator norm on the PD cone. -/
theorem continuousAt_logDeriv {A : HermitianMat n ℂ} (hA : A.mat.PosDef) :
    ContinuousAt (fun B : HermitianMat n ℂ => BetaLog.logDeriv B.mat) A := by
  obtain ⟨r,hr,hPD⟩ := Metric.eventually_nhds_iff_ball.mp (eventually_posDef hA)
  let K : Set (HermitianMat n ℂ) := Metric.closedBall A (r/2)
  have hKPD (B : HermitianMat n ℂ) (hB : B ∈ K) : B.mat.PosDef := by
    apply hPD B
    exact (Metric.mem_closedBall.mp hB).trans_lt (by linarith)
  have hc : ContinuousOn (fun z : HermitianMat n ℂ × ℝ => kernelDeriv z.1.mat z.2)
      (K ×ˢ Icc (0 : ℝ) 1) := by
    intro z hz
    exact (continuousAt_kernelDeriv (hKPD z.1 hz.1) hz.2).continuousWithinAt
  obtain ⟨M,hM⟩ := ((isCompact_closedBall A (r/2)).prod isCompact_Icc).bddAbove_image hc.norm
  have hb (B : HermitianMat n ℂ) (hB : B ∈ K) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      ‖kernelDeriv B.mat t‖ ≤ max M 0 := by
    apply le_trans ?_ (le_max_left _ _)
    convert! hM (mem_image_of_mem
      (fun z : HermitianMat n ℂ × ℝ => ‖kernelDeriv z.1.mat z.2‖)
      (show (B,t) ∈ K ×ˢ Icc (0 : ℝ) 1 from ⟨hB,ht⟩)) using 1
  unfold BetaLog.logDeriv
  apply intervalIntegral.continuousAt_of_dominated_interval
    (bound := fun _ => max M 0)
  · filter_upwards [eventually_posDef hA] with B hB
    exact (show ContinuousOn _ (uIcc (0 : ℝ) 1) from by simpa using continuousOn_kernelDeriv hB).intervalIntegrable.aestronglyMeasurable_restrict_uIoc
  · filter_upwards [Metric.closedBall_mem_nhds A (show 0 < r/2 by linarith)] with B hB
    exact Filter.Eventually.of_forall (fun t ht => hb B hB t
      (Ioc_subset_Icc_self (show t ∈ Ioc (0 : ℝ) 1 from by simpa using ht)))
  · exact intervalIntegrable_const
  · apply Filter.Eventually.of_forall
    intro t ht
    have hti : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self (by simpa using ht)
    convert! (continuousAt_kernelDeriv hA hti).comp (x := A)
      (f := fun B : HermitianMat n ℂ => (B,t)) (by fun_prop) using 1

theorem hasStrictFDerivAt_logarithm {A : HermitianMat n ℂ} (hA : A.mat.PosDef) :
    HasStrictFDerivAt (fun B : HermitianMat n ℂ => BetaPowers.logarithm B.mat) (BetaLog.logDeriv A.mat) A := by
  apply hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt (𝕜 := ℝ)
    (f' := fun B : HermitianMat n ℂ => BetaLog.logDeriv B.mat)
  · filter_upwards [eventually_posDef hA] with B hB
    exact hasFDerivAt_logarithm hB
  · exact continuousAt_logDeriv hA

theorem hasStrictFDerivAt_logarithm_inverseKM {A : HermitianMat n ℂ} (hA : A.mat.PosDef) :
    HasStrictFDerivAt (fun B : HermitianMat n ℂ => BetaPowers.logarithm B.mat)
      (BetaLogKM.inverseKM A.mat) A := by
  rw [← BetaLogKM.logDeriv_eq_inverseKM_clm hA]
  exact hasStrictFDerivAt_logarithm hA

end QubitAdditivity.BetaLogRegularity
