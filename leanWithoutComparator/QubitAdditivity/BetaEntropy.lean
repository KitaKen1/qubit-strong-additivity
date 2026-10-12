import QubitAdditivity.BetaLogKM

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Filter
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

namespace QubitAdditivity.BetaEntropy
variable {n : Type*} [Fintype n] [DecidableEq n]

@[reducible] local instance mNorm : NormedAddCommGroup (Matrix n n ℂ) :=
  Matrix.frobeniusNormedRing.toNonUnitalNormedRing.toNormedAddCommGroup
@[reducible] local instance mSpace : NormedSpace ℝ (Matrix n n ℂ) :=
  NormedAlgebra.toNormedSpace (Matrix n n ℂ)
@[reducible] local instance mTop : TopologicalSpace (Matrix n n ℂ) := mNorm.toUniformSpace.toTopologicalSpace
@[reducible] local instance mAdd : AddCommGroup (Matrix n n ℂ) := mNorm.toAddCommGroup
@[reducible] local instance mModule : Module ℝ (Matrix n n ℂ) := mSpace.toModule
@[reducible] local instance hTop : TopologicalSpace (HermitianMat n ℂ) :=
  HermitianMat.instNormedAddCommGroupComplex.toUniformSpace.toTopologicalSpace
@[reducible] local instance hAdd : AddCommGroup (HermitianMat n ℂ) :=
  HermitianMat.instNormedAddCommGroupComplex.toAddCommGroup
@[reducible] local instance hModule : Module ℝ (HermitianMat n ℂ) := HermitianMat.instNormedSpace.toModule

/-- Negative spectral entropy, the trace X log X term in the dual objective. -/
def psi (A : HermitianMat n ℂ) : ℝ := -OpenAIEntropy.entropy A.mat

theorem psi_eq_trace (A : HermitianMat n ℂ) :
    psi A = (A.mat * BetaPowers.logarithm A.mat).trace.re := by
  simp only [psi,BetaLog.entropy_eq_trace A.H,neg_neg]

def psiGradient (A : Matrix n n ℂ) : HermitianMat n ℂ →L[ℝ] ℝ := -BetaLog.entropyGradient A

theorem psiGradient_apply (A : Matrix n n ℂ) (H : HermitianMat n ℂ) :
    psiGradient A H = (H.mat * (BetaPowers.logarithm A+1)).trace.re := by
  simp [psiGradient,BetaLog.entropyGradient_apply]

theorem hasFDerivAt_psi {A : HermitianMat n ℂ} (hA : A.mat.PosDef) :
    HasFDerivAt psi (psiGradient A.mat) A := by
  convert! (BetaLog.hasFDerivAt_entropy hA).neg using 1

/-- One Hessian row as a continuous real linear form. -/
def psiHessianRow (A : Matrix n n ℂ) (H : HermitianMat n ℂ) : HermitianMat n ℂ →L[ℝ] ℝ :=
  (BetaLog.traceRe (n := n)).comp
    ((ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) H.mat 1).comp (BetaLogKM.inverseKM A))

@[simp] theorem psiHessianRow_apply (A : Matrix n n ℂ) (H K : HermitianMat n ℂ) :
    psiHessianRow A H K = (H.mat * BetaLogKM.inverseKM A K).trace.re := by
  simp only [psiHessianRow,ContinuousLinearMap.comp_apply,ContinuousLinearMap.mulLeftRight_apply,
    Matrix.mul_one,BetaLog.traceRe_apply]

/-- Actual differentiation of the entropy gradient, with the original KM inverse. -/
theorem hasFDerivAt_psiGradient_row {A : HermitianMat n ℂ} (hA : A.mat.PosDef)
    (H : HermitianMat n ℂ) :
    HasFDerivAt (fun B : HermitianMat n ℂ => psiGradient B.mat H) (psiHessianRow A.mat H) A := by
  have hl := (BetaLogKM.hasFDerivAt_logarithm_inverseKM hA).add_const (1 : Matrix n n ℂ)
  let L := ContinuousLinearMap.mulLeftRight ℝ (Matrix n n ℂ) H.mat 1
  have hm := L.hasFDerivAt.comp A hl
  have ht := (BetaLog.traceRe (n := n)).hasFDerivAt.comp A hm
  convert! ht using 1
  · ext B
    simp only [psiGradient_apply,ContinuousLinearMap.coe_comp',Function.comp_apply,
      ContinuousLinearMap.mulLeftRight_apply,Matrix.mul_one,BetaLog.traceRe_apply,L]

theorem trace_mul_eq_vector_pairing (H : HermitianMat n ℂ) (X : Matrix n n ℂ) :
    (H.mat * X).trace = star (fun ij : n × n => H.mat ij.1 ij.2) ⬝ᵥ
      (fun ij : n × n => X ij.1 ij.2) := by
  calc
    (H.mat * X).trace = (H.matᴴ * X).trace := by rw [H.H]
    _ = _ := by
      simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
        dotProduct,Pi.star_apply,Fintype.sum_prod_type]
      rw [Finset.sum_comm]

theorem psiHessianRow_eq_pairing (A : Matrix n n ℂ) (H K : HermitianMat n ℂ) :
    psiHessianRow A H K = (BetaComparison.pairing
      (fun ij : n × n => H.mat ij.1 ij.2) (BetaPowers.km A)⁻¹
      (fun ij : n × n => K.mat ij.1 ij.2)).re := by
  rw [psiHessianRow_apply,trace_mul_eq_vector_pairing]
  rfl

/-- Strict positive entropy curvature on every nonzero real Hermitian direction. -/
theorem psiHessianRow_self_pos {A : Matrix n n ℂ} (hA : A.PosDef)
    {H : HermitianMat n ℂ} (hH : H ≠ 0) : 0 < psiHessianRow A H H := by
  rw [psiHessianRow_eq_pairing]
  apply BetaComparison.quadratic_pos (BetaKM.km_posDef hA).inv
  intro hv
  apply hH
  apply Subtype.ext
  ext i j
  exact congrFun hv (i,j)

theorem psiHessianRow_self_nonneg {A : Matrix n n ℂ} (hA : A.PosDef)
    (H : HermitianMat n ℂ) : 0 ≤ psiHessianRow A H H := by
  by_cases hz : H = 0
  · subst H
    simp [psiHessianRow_apply]
  · exact (psiHessianRow_self_pos hA hz).le

end QubitAdditivity.BetaEntropy
