import QubitAdditivity.BetaTC4Gram

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix
open scoped Matrix ComplexOrder MatrixOrder

namespace QubitAdditivity.BetaOrthogonalEntropy
open BetaEntropy
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Compute the entropy trace in a fixed eigenbasis, without sorting the new eigenvalues. -/
theorem psi_cfc (C : HermitianMat n ℂ) (f : ℝ → ℝ) :
    psi (C.cfc f) = ∑ i, f (C.H.eigenvalues i)*Real.log (f (C.H.eigenvalues i)) := by
  have he (B : HermitianMat n ℂ) : psi B = -(B.cfc Real.negMulLog).trace := by
    convert! rfl using 1
  rw [he,← HermitianMat.cfc_comp_apply,HermitianMat.trace_cfc_eq,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [Real.negMulLog]
  ring

/-- Entropy is additive on orthogonal Hermitian supports, including singular supports. -/
theorem psi_add_of_mul_eq_zero (A B : HermitianMat n ℂ) (hAB : A.mat*B.mat = 0) :
    psi (A+B) = psi A+psi B := by
  have hBA : B.mat*A.mat = 0 := by
    have h := congrArg Matrix.conjTranspose hAB
    simpa only [Matrix.conjTranspose_mul,A.H.eq,B.H.eq,Matrix.conjTranspose_zero] using h
  have hc : Commute A.mat B.mat := hAB.trans hBA.symm
  obtain ⟨C,⟨f,rfl⟩,⟨g,rfl⟩⟩ := hc.exists_HermitianMat_cfc
  have hh : (C.cfc (f*g)).mat = 0 := (C.mat_cfc_mul f g).trans hAB
  have he : cfc (f*g) C.mat = cfc (fun _ => (0 : ℝ)) C.mat := by
    exact hh.trans (cfc_const_zero (R := ℝ) (a := C.mat)).symm
  have hfg := eqOn_of_cfc_eq_cfc he (BetaPowers.continuousOn_spectrum C.mat _) continuousOn_const C.H
  rw [← HermitianMat.cfc_add,psi_cfc,psi_cfc,psi_cfc,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have h0 : f (C.H.eigenvalues i)*g (C.H.eigenvalues i) = 0 := by
    exact hfg ((C.H.spectrum_real_eq_range_eigenvalues).symm ▸ Set.mem_range_self i)
  rcases mul_eq_zero.mp h0 with hf | hg
  · simp [hf]
  · simp [hg]

end QubitAdditivity.BetaOrthogonalEntropy
