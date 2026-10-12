import QubitAdditivity.BetaKM
import QubitAdditivity.BetaResolvent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix
open scoped Matrix ComplexOrder MatrixOrder

namespace QubitAdditivity.BetaHessian
open BetaOperators BetaPowers BetaBridge BetaEndpoints
variable {r s : Type*} [Fintype r] [Fintype s] [DecidableEq r] [DecidableEq s]
local notation "Vβ" => blockInclusion (r := r) (s := s)

def gapKM (T : Matrix (r ⊕ s) (r ⊕ s) ℂ) (A : Matrix r r ℂ) (B : Matrix s s ℂ) :=
  blockKM (T.submatrix Sum.inl Sum.inl - A) (T.submatrix Sum.inr Sum.inr - B)

/-- The matrix expression predicted for the eliminated dual curvature.
No derivative of the minimizer or value function is asserted by this definition. -/
def curvature (T : Matrix (r ⊕ s) (r ⊕ s) ℂ) (A : Matrix r r ℂ) (B : Matrix s s ℂ) :=
  Vβ * (gapKM T A B)⁻¹ * Vβᴴ - (BetaKM.residual T A B)⁻¹

theorem gapKM_posDef {T : Matrix (r ⊕ s) (r ⊕ s) ℂ}
    {A : Matrix r r ℂ} {B : Matrix s s ℂ}
    (hgap : (T - Matrix.fromBlocks A 0 0 B).PosDef) : (gapKM T A B).PosDef :=
  BetaKM.blockKM_posDef (gap_blocks_posDef hgap).1 (gap_blocks_posDef hgap).2

/-- KM supplies the actual compressed residual inequality, rather than an
independent hKM premise. Logarithmic stationarity is still explicit. -/
theorem compression_gap_posSemidef {T : Matrix (r ⊕ s) (r ⊕ s) ℂ}
    {A : Matrix r r ℂ} {B : Matrix s s ℂ}
    (hT : T.PosDef) (hA : A.PosDef) (hB : B.PosDef)
    (hgap : (T - Matrix.fromBlocks A 0 0 B).PosDef)
    (lambda₀ lambda₁ : ℂ)
    (h₀ : logarithm A = (logarithm T).submatrix Sum.inl Sum.inl + lambda₀ • 1)
    (h₁ : logarithm B = (logarithm T).submatrix Sum.inr Sum.inr + lambda₁ • 1) :
    (gapKM T A B - Vβᴴ * BetaKM.residual T A B * Vβ).PosSemidef := by
  have hk := BetaPWBound.km_of_stationarity hT hA hB hgap lambda₀ lambda₁ h₀ h₁
  have hc : Vβᴴ * BetaKM.residual T A B * Vβ ≤ gapKM T A B := by
    rw [BetaKM.residual_compression]
    apply sub_le_iff_le_add.mpr
    simpa only [gapKM, add_comm] using hk
  exact Matrix.LE.le.posSemidef (sub_nonneg.mpr hc)

/-- All positivity and KM order hypotheses are supplied by the actual operators.
The remaining analytic premise is logarithmic stationarity. -/
theorem curvature_nonpos_of_stationarity {T : Matrix (r ⊕ s) (r ⊕ s) ℂ}
    {A : Matrix r r ℂ} {B : Matrix s s ℂ}
    (hT : T.PosDef) (hA : A.PosDef) (hB : B.PosDef)
    (hgap : (T - Matrix.fromBlocks A 0 0 B).PosDef)
    (lambda₀ lambda₁ : ℂ)
    (h₀ : logarithm A = (logarithm T).submatrix Sum.inl Sum.inl + lambda₀ • 1)
    (h₁ : logarithm B = (logarithm T).submatrix Sum.inr Sum.inr + lambda₁ • 1) :
    curvature T A B ≤ 0 := by
  have hp := BetaOrder.inverse_compression_residual_posSemidef
    (BetaKM.residual T A B) (gapKM T A B) Vβ
    (BetaKM.residual_posDef hT hA hB hgap) (gapKM_posDef hgap)
    (compression_gap_posSemidef hT hA hB hgap lambda₀ lambda₁ h₀ h₁)
  exact sub_nonpos.mpr (sub_nonneg.mp hp.nonneg)

theorem curvature_quadratic_nonpos {T : Matrix (r ⊕ s) (r ⊕ s) ℂ}
    {A : Matrix r r ℂ} {B : Matrix s s ℂ}
    (hT : T.PosDef) (hA : A.PosDef) (hB : B.PosDef)
    (hgap : (T - Matrix.fromBlocks A 0 0 B).PosDef)
    (lambda₀ lambda₁ : ℂ)
    (h₀ : logarithm A = (logarithm T).submatrix Sum.inl Sum.inl + lambda₀ • 1)
    (h₁ : logarithm B = (logarithm T).submatrix Sum.inr Sum.inr + lambda₁ • 1)
    (v : ((r ⊕ s) × (r ⊕ s)) → ℂ) :
    BetaComparison.quadratic (curvature T A B) v ≤ 0 := by
  simpa [BetaComparison.quadratic, BetaComparison.pairing] using
    BetaComparison.quadratic_mono
      (curvature_nonpos_of_stationarity hT hA hB hgap lambda₀ lambda₁ h₀ h₁) v

/-- Strict positivity of the inverse-KM compression gap. This is the operator
expected in the W-Hessian, without yet identifying an actual objective Hessian. -/
theorem inverseKM_compression_gap_posDef {T : Matrix (r ⊕ s) (r ⊕ s) ℂ}
    {A : Matrix r r ℂ} {B : Matrix s s ℂ}
    (hT : T.PosDef) (hA : A.PosDef) (hB : B.PosDef)
    (hgap : (T - Matrix.fromBlocks A 0 0 B).PosDef) :
    ((blockKM A B)⁻¹ - Vβᴴ * (km T)⁻¹ * Vβ).PosDef := by
  have hg : (km T - Vβᴴᴴ * blockKM A B * Vβᴴ).PosDef := by
    simpa only [BetaKM.residual, conjTranspose_conjTranspose] using BetaKM.residual_posDef hT hA hB hgap
  simpa only [conjTranspose_conjTranspose] using
    BetaResolvent.inverse_compression_strict_posDef (blockKM A B) (km T) Vβᴴ
      (BetaKM.blockKM_posDef hA hB) (BetaKM.km_posDef hT) hg

/-- The full Schur expression now uses actual KM operators. Invertibility,
residual positivity and KM compression are proved, not additional assumptions. -/
theorem eliminated_expression_nonpos {T : Matrix (r ⊕ s) (r ⊕ s) ℂ}
    {A : Matrix r r ℂ} {B : Matrix s s ℂ}
    (hT : T.PosDef) (hA : A.PosDef) (hB : B.PosDef)
    (hgap : (T - Matrix.fromBlocks A 0 0 B).PosDef)
    (lambda₀ lambda₁ : ℂ)
    (h₀ : logarithm A = (logarithm T).submatrix Sum.inl Sum.inl + lambda₀ • 1)
    (h₁ : logarithm B = (logarithm T).submatrix Sum.inr Sum.inr + lambda₁ • 1) :
    Vβ * (gapKM T A B)⁻¹ * Vβᴴ - (km T)⁻¹ -
      (km T)⁻¹ * Vβ * ((blockKM A B)⁻¹ - Vβᴴ * (km T)⁻¹ * Vβ)⁻¹ * Vβᴴ * (km T)⁻¹ ≤ 0 := by
  exact BetaOrder.eliminatedHessian_nonpos (km T) (blockKM A B) (gapKM T A B) Vβ
    (BetaKM.km_posDef hT).isUnit (BetaKM.blockKM_posDef hA hB).isUnit
    (inverseKM_compression_gap_posDef hT hA hB hgap).isUnit
    (BetaKM.residual_posDef hT hA hB hgap) (gapKM_posDef hgap)
    (compression_gap_posSemidef hT hA hB hgap lambda₀ lambda₁ h₀ h₁)

end QubitAdditivity.BetaHessian
