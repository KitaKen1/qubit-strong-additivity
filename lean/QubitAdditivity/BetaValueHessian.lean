import QubitAdditivity.BetaDualValue

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology

namespace QubitAdditivity.BetaValueHessian
open BetaDual BetaDualConvex BetaDualInterior BetaDualDerivative BetaMinimizer BetaEntropy BetaDualValue
open BetaOperators BetaPowers BetaBridge

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



variable {n : Type*} [Fintype n] [DecidableEq n]
variable {r s : Type*} [Fintype r] [Fintype s] [DecidableEq r] [DecidableEq s]
local notation "Vβ" => blockInclusion (r := r) (s := s)

def vector (H : HermitianMat n ℂ) : n × n → ℂ := fun ij => H.mat ij.1 ij.2

def blockVector (H : Blocks r s) : (r × r) ⊕ (s × s) → ℂ := Sum.elim (vector H.1) (vector H.2)

theorem vector_diagonal (H : Blocks r s) : vector (BetaDual.diagonal H) = Vβ *ᵥ blockVector H := by
  ext ij
  rcases ij with ⟨i,j⟩
  change (Matrix.fromBlocks H.1.mat 0 0 H.2.mat) i j =
    (Vβ *ᵥ Sum.elim (fun ij => H.1.mat ij.1 ij.2) (fun ij => H.2.mat ij.1 ij.2)) (i,j)
  cases i <;> cases j <;>
    simp [blockInclusion,coordinateInclusion,Matrix.mulVec,dotProduct,Matrix.one_apply,
      blockCoordinates,ite_and,Fintype.sum_prod_type]

theorem vector_pinch (H : HermitianMat (r ⊕ s) ℂ) : blockVector (pinchCLM H) = Vβᴴ *ᵥ vector H := by
  ext ij
  change Sum.elim (fun ij => H.mat (Sum.inl ij.1) (Sum.inl ij.2))
    (fun ij => H.mat (Sum.inr ij.1) (Sum.inr ij.2)) ij =
    (Vβᴴ *ᵥ (fun ij => H.mat ij.1 ij.2)) ij
  cases ij <;>
    simp [blockInclusion,coordinateInclusion,Matrix.mulVec,dotProduct,Matrix.one_apply,
      blockCoordinates,Matrix.conjTranspose_apply,Fintype.sum_prod_type,ite_and]

theorem vector_logHermDeriv {A : HermitianMat n ℂ} (hA : A.mat.PosDef) (H : HermitianMat n ℂ) :
    vector (logHermDeriv A H) = (km A.mat)⁻¹ *ᵥ vector H := by
  ext ij
  change (logHermDeriv A H).mat ij.1 ij.2 =
    ((km A.mat)⁻¹ *ᵥ (fun ij => H.mat ij.1 ij.2)) ij
  exact congrFun (congrFun (logHermDeriv_mat hA H) ij.1) ij.2

theorem blockKM_inv {A : Matrix r r ℂ} {B : Matrix s s ℂ} (hA : A.PosDef) (hB : B.PosDef) :
    (blockKM A B)⁻¹ = Matrix.fromBlocks (km A)⁻¹ 0 0 (km B)⁻¹ := by
  change (Matrix.fromBlocks (km A) 0 0 (km B))⁻¹ = _
  simpa using Matrix.inv_fromBlocks_zero₂₁_of_isUnit_iff (km A) 0 (km B)
    (iff_of_true (BetaKM.km_posDef hA).isUnit (BetaKM.km_posDef hB).isUnit)

theorem vector_blockLogDeriv {W : Blocks r s} (hA : W.1.mat.PosDef) (hB : W.2.mat.PosDef)
    (H : Blocks r s) : blockVector (blockLogDeriv W H) = (blockKM W.1.mat W.2.mat)⁻¹ *ᵥ blockVector H := by
  rw [blockKM_inv hA hB]
  change Sum.elim (vector (logHermDeriv W.1 H.1)) (vector (logHermDeriv W.2 H.2)) = _
  rw [vector_logHermDeriv hA,vector_logHermDeriv hB]
  simp [blockVector,Matrix.fromBlocks_mulVec]

@[simp] theorem vector_add (H K : HermitianMat n ℂ) : vector (H+K) = vector H+vector K := rfl
@[simp] theorem blockVector_sub (H K : Blocks r s) : blockVector (H-K) = blockVector H-blockVector K := by
  ext ij
  cases ij <;> rfl

theorem logHermDeriv_diagonal {W : Blocks r s} (hA : W.1.mat.PosDef) (hB : W.2.mat.PosDef)
    (H : Blocks r s) : logHermDeriv (BetaDual.diagonal W) (BetaDual.diagonal H) =
      BetaDual.diagonal (blockLogDeriv W H) := by
  have he (Z : Blocks r s) : hermLog (BetaDual.diagonal Z) = BetaDual.diagonal (blockLog Z) := by
    apply HermitianMat.ext
    exact logarithm_diagonal Z
  have hd₁ := (hasStrictFDerivAt_hermLog (A := BetaDual.diagonal W) (BetaBlocks.diagonal_posDef hA hB)).hasFDerivAt.comp W
    ((diagonalCLM (r := r) (s := s)).hasFDerivAt (x := W))
  have hd₂ := (diagonalCLM (r := r) (s := s)).hasFDerivAt (x := blockLog W) |>.comp W
    (hasStrictFDerivAt_blockLog hA hB).hasFDerivAt
  have hd₂' : HasFDerivAt (fun Z : Blocks r s => hermLog (BetaDual.diagonal Z))
    (diagonalCLM.comp (blockLogDeriv W)) W := by
    convert! hd₂ using 1
    apply funext
    intro Z
    exact he Z
  exact congrArg (fun L : Blocks r s →L[ℝ] HermitianMat (r ⊕ s) ℂ => L H) (hd₁.unique hd₂')

/-- The actual residual Jacobian in the same matrix-unit coordinates as KM. -/
theorem vector_residualDerivative {J : HermitianMat (r ⊕ s) ℂ} {W : Blocks r s}
    (hA : W.1.mat.PosDef) (hB : W.2.mat.PosDef) (hT : (J+BetaDual.diagonal W).mat.PosDef)
    (H : Blocks r s) : blockVector (residualDerivative J W H) =
      ((blockKM W.1.mat W.2.mat)⁻¹-Vβᴴ*(km (J+BetaDual.diagonal W).mat)⁻¹*Vβ) *ᵥ blockVector H := by
  change blockVector (blockLogDeriv W H-pinchCLM (logHermDeriv (J+BetaDual.diagonal W) (BetaDual.diagonal H))) = _
  rw [blockVector_sub,vector_blockLogDeriv hA hB,vector_pinch,vector_logHermDeriv hT,vector_diagonal]
  simp only [Matrix.sub_mulVec,← Matrix.mulVec_mulVec]

/-- Differentiating stationarity gives the genuine minimizer derivative equation. -/
theorem minimizerDerivative_equation {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosDef) (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) (H : HermitianMat (r ⊕ s) ℂ) :
    residualDerivative J (minimizer J lambda₀ lambda₁) (minimizerDerivative J lambda₀ lambda₁ H) =
      pinchCLM (logHermDeriv (J+BetaDual.diagonal (minimizer J lambda₀ lambda₁)) H) := by
  have hW := minimizer_positiveInterior hJ hl₀ hl₁
  have hi := residualDerivative_isInvertible hJ hW.1 hW.2
  change residualDerivative J (minimizer J lambda₀ lambda₁)
    (-((residualDerivative J (minimizer J lambda₀ lambda₁)).inverse
      (-pinchCLM (logHermDeriv (J+BetaDual.diagonal (minimizer J lambda₀ lambda₁)) H)))) = _
  rw [map_neg,hi.self_apply_inverse,neg_neg]

/-- Solving the certified Jacobian equation identifies the original complex Schur inverse. -/
theorem vector_minimizerDerivative {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosDef) (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) (H : HermitianMat (r ⊕ s) ℂ) :
    blockVector (minimizerDerivative J lambda₀ lambda₁ H) =
      ((blockKM (minimizer J lambda₀ lambda₁).1.mat (minimizer J lambda₀ lambda₁).2.mat)⁻¹-
        Vβᴴ*(km (J+BetaDual.diagonal (minimizer J lambda₀ lambda₁)).mat)⁻¹*Vβ)⁻¹ *ᵥ
        (Vβᴴ *ᵥ ((km (J+BetaDual.diagonal (minimizer J lambda₀ lambda₁)).mat)⁻¹ *ᵥ vector H)) := by
  let W := minimizer J lambda₀ lambda₁
  let E := (blockKM W.1.mat W.2.mat)⁻¹-Vβᴴ*(km (J+BetaDual.diagonal W).mat)⁻¹*Vβ
  have hW := minimizer_positiveInterior hJ hl₀ hl₁
  have hT := total_posDef hJ hW.1 hW.2
  have hE : E.PosDef := BetaHessian.inverseKM_compression_gap_posDef hT hW.1 hW.2 (total_gap_posDef (W := W) hJ)
  have he := congrArg blockVector (minimizerDerivative_equation hJ hl₀ hl₁ H)
  rw [vector_residualDerivative hW.1 hW.2 hT,vector_pinch,vector_logHermDeriv hT] at he
  change E *ᵥ blockVector (minimizerDerivative J lambda₀ lambda₁ H) = _ at he
  have hinv : E⁻¹*E = 1 := Matrix.nonsing_inv_mul E (Matrix.isUnit_iff_isUnit_det E |>.mp hE.isUnit)
  change blockVector (minimizerDerivative J lambda₀ lambda₁ H) = E⁻¹ *ᵥ _
  rw [← he,Matrix.mulVec_mulVec,hinv,Matrix.one_mulVec]

/-- The Schur coordinates are derived from the chosen true minimizer. -/
theorem vector_totalDerivative {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosDef) (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) (H : HermitianMat (r ⊕ s) ℂ) :
    vector (totalDerivative J lambda₀ lambda₁ H) = vector H+
      Vβ *ᵥ (((blockKM (minimizer J lambda₀ lambda₁).1.mat (minimizer J lambda₀ lambda₁).2.mat)⁻¹-
        Vβᴴ*(km (J+BetaDual.diagonal (minimizer J lambda₀ lambda₁)).mat)⁻¹*Vβ)⁻¹ *ᵥ
        (Vβᴴ *ᵥ ((km (J+BetaDual.diagonal (minimizer J lambda₀ lambda₁)).mat)⁻¹ *ᵥ vector H))) := by
  change vector (H+BetaDual.diagonal (minimizerDerivative J lambda₀ lambda₁ H)) = _
  rw [vector_add,vector_diagonal,vector_minimizerDerivative hJ hl₀ hl₁]

theorem vector_pinching (H : HermitianMat (r ⊕ s) ℂ) : vector (pinching H) = Vβ *ᵥ (Vβᴴ *ᵥ vector H) := by
  change vector (BetaDual.diagonal (pinchCLM H)) = _
  rw [vector_diagonal,vector_pinch]

private theorem block_pairing_lift (x y : (r × r) ⊕ (s × s) → ℂ) :
    star (Vβ *ᵥ x) ⬝ᵥ (Vβ *ᵥ y) = star x ⬝ᵥ y := by
  rw [Matrix.star_mulVec,← Matrix.dotProduct_mulVec,Matrix.mulVec_mulVec,
    blockInclusion_isometry,Matrix.one_mulVec]

/-- The entropy curvature of the pinched input is the actual block-KM inverse. -/
theorem pinched_psiHessianRow_eq_pairing {J : HermitianMat (r ⊕ s) ℂ} (hJ : J.mat.PosDef)
    (H K : HermitianMat (r ⊕ s) ℂ) :
    psiHessianRow (pinching J).mat (pinching H) (pinching K) =
      (BetaComparison.pairing (vector H) (Vβ*(blockKM (pinchLeft J).mat (pinchRight J).mat)⁻¹*Vβᴴ) (vector K)).re := by
  have hA := hJ.submatrix Sum.inl_injective
  have hB := hJ.submatrix Sum.inr_injective
  rw [psiHessianRow_apply,← logHermDeriv_mat (pinching_posDef hJ),trace_mul_eq_vector_pairing]
  change (star (vector (pinching H)) ⬝ᵥ vector (logHermDeriv (pinching J) (pinching K))).re = _
  have he : vector (logHermDeriv (pinching J) (pinching K)) =
      Vβ *ᵥ ((blockKM (pinchLeft J).mat (pinchRight J).mat)⁻¹ *ᵥ (Vβᴴ *ᵥ vector K)) := by
    change vector (logHermDeriv (BetaDual.diagonal (pinchCLM J)) (BetaDual.diagonal (pinchCLM K))) = _
    rw [logHermDeriv_diagonal (W := pinchCLM J) hA hB,vector_diagonal,
      vector_blockLogDeriv (W := pinchCLM J) hA hB,vector_pinch]
    rfl
  rw [vector_pinching,he,block_pairing_lift,Matrix.star_mulVec,← Matrix.dotProduct_mulVec]
  simp only [BetaComparison.pairing,← Matrix.mulVec_mulVec,Matrix.conjTranspose_conjTranspose]

theorem gapKM_total (J : HermitianMat (r ⊕ s) ℂ) (W : Blocks r s) :
    BetaHessian.gapKM (J+BetaDual.diagonal W).mat W.1.mat W.2.mat =
      blockKM (pinchLeft J).mat (pinchRight J).mat := by
  unfold BetaHessian.gapKM
  congr 1 <;> ext i j <;>
    simp [HermitianMat.mat_add,diagonal_mat,Matrix.submatrix_apply,Matrix.sub_apply,Matrix.add_apply,pinchLeft,pinchRight] <;> rfl

/-- The same eliminated matrix already certified by the KM order argument. -/
def eliminatedMatrix (J : HermitianMat (r ⊕ s) ℂ) (W : Blocks r s) :=
  Vβ*(BetaHessian.gapKM (J+BetaDual.diagonal W).mat W.1.mat W.2.mat)⁻¹*Vβᴴ-
    (km (J+BetaDual.diagonal W).mat)⁻¹-
    (km (J+BetaDual.diagonal W).mat)⁻¹*Vβ*
      ((blockKM W.1.mat W.2.mat)⁻¹-Vβᴴ*(km (J+BetaDual.diagonal W).mat)⁻¹*Vβ)⁻¹*
      Vβᴴ*(km (J+BetaDual.diagonal W).mat)⁻¹

/-- Identity for the actual value Hessian, including the derivative of the global minimum. -/
theorem valueHessianRow_eq_eliminated_pairing {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosDef) (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) (H K : HermitianMat (r ⊕ s) ℂ) :
    valueHessianRow J lambda₀ lambda₁ H K =
      (BetaComparison.pairing (vector H) (eliminatedMatrix J (minimizer J lambda₀ lambda₁)) (vector K)).re := by
  change psiHessianRow (pinching J).mat (pinching H) (pinching K)-
    psiHessianRow (J+BetaDual.diagonal (minimizer J lambda₀ lambda₁)).mat H
      (totalDerivative J lambda₀ lambda₁ K) = _
  rw [pinched_psiHessianRow_eq_pairing hJ,psiHessianRow_eq_pairing]
  change (BetaComparison.pairing (vector H) (Vβ*(blockKM (pinchLeft J).mat (pinchRight J).mat)⁻¹*Vβᴴ) (vector K)).re-
    (BetaComparison.pairing (vector H) (km (J+BetaDual.diagonal (minimizer J lambda₀ lambda₁)).mat)⁻¹
      (vector (totalDerivative J lambda₀ lambda₁ K))).re = _
  rw [vector_totalDerivative hJ hl₀ hl₁]
  simp only [eliminatedMatrix,gapKM_total,BetaComparison.pairing,Matrix.sub_mulVec,
    Matrix.mulVec_add,← Matrix.mulVec_mulVec,dotProduct_sub,dotProduct_add,Complex.sub_re,Complex.add_re]
  ring

/-- The actual dual value Hessian is negative semidefinite on J>0. -/
theorem valueHessianRow_self_nonpos {J : HermitianMat (r ⊕ s) ℂ} {lambda₀ lambda₁ : ℝ}
    (hJ : J.mat.PosDef) (hl₀ : lambda₀ < 0) (hl₁ : lambda₁ < 0) (H : HermitianMat (r ⊕ s) ℂ) :
    valueHessianRow J lambda₀ lambda₁ H H ≤ 0 := by
  let W := minimizer J lambda₀ lambda₁
  have hW := minimizer_positiveInterior hJ hl₀ hl₁
  have hs := log_stationarity_of_residual_zero (minimizer_stationary hJ hl₀ hl₁)
  have hm : eliminatedMatrix J W ≤ 0 := BetaHessian.eliminated_expression_nonpos
    (total_posDef hJ hW.1 hW.2) hW.1 hW.2 (total_gap_posDef hJ)
    (lambda₀ : ℂ) (lambda₁ : ℂ) hs.1 hs.2
  rw [valueHessianRow_eq_eliminated_pairing hJ hl₀ hl₁]
  simpa [BetaComparison.quadratic,BetaComparison.pairing] using BetaComparison.quadratic_mono hm (vector H)

end QubitAdditivity.BetaValueHessian
