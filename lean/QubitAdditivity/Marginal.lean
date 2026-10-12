import QubitAdditivity.Holevo
import QuantumInfo.Entropy.SSA
import QuantumInfo.ForMathlib.HermitianMat.Peierls

/-! Marginals of product channels on arbitrary, possibly entangled, inputs, the resulting
output-entropy subadditivity, and concavity of entropy over ensembles.
Physlib states the marginal identity only for product inputs. -/

noncomputable section
open scoped BigOperators MatrixMap

namespace QubitAdditivity

section kron

variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
variable [DecidableEq A] [DecidableEq C]

/-- A linear map on matrices is determined by its values on matrix units. -/
theorem matrixMap_eq_sum_single {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
    (M : MatrixMap X Y ℂ) (N : Matrix X X ℂ) :
    M N = ∑ x₁, ∑ x₂, N x₁ x₂ • M (Matrix.single x₁ x₂ 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single N]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun x₁ _ => Finset.sum_congr rfl fun x₂ _ => ?_
  rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

/-- Diagonal sums of the image of a matrix unit under a trace-preserving map. -/
theorem sum_diag_single_of_tracePreserving {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] {M : MatrixMap X Y ℂ} (hM : M.IsTracePreserving) (x₁ x₂ : X) :
    ∑ y, M (Matrix.single x₁ x₂ 1) y y = if x₁ = x₂ then 1 else 0 := by
  have h := hM (Matrix.single x₁ x₂ 1)
  simp only [Matrix.trace, Matrix.diag] at h
  rw [h]
  change Matrix.trace (Matrix.single x₁ x₂ (1 : ℂ)) = _
  by_cases hx : x₁ = x₂
  · subst hx
    simp [Matrix.trace_single_eq_same]
  · simp [Matrix.trace_single_eq_of_ne x₁ x₂ (1 : ℂ) hx, hx]

/-- Tracing out the second output of `M₁ ⊗ M₂` gives `M₁` applied to the partial trace of the
input. Only trace preservation of `M₂` is used. -/
theorem kron_traceRight (M₁ : MatrixMap A B ℂ) (M₂ : MatrixMap C D ℂ)
    (h₂ : M₂.IsTracePreserving) (M : Matrix (A × C) (A × C) ℂ) :
    ((M₁ ⊗ₖₘ M₂) M).traceRight = M₁ M.traceRight := by
  ext b₁ b₂
  rw [matrixMap_eq_sum_single M₁ M.traceRight]
  simp only [Matrix.traceRight, Matrix.of_apply, MatrixMap.kron_def, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
  have hinner (a₁ a₂ : A) (c₁ c₂ : C) :
      ∑ d, M₁ (Matrix.single a₁ a₂ 1) b₁ b₂ * M₂ (Matrix.single c₁ c₂ 1) d d *
          M (a₁, c₁) (a₂, c₂) =
        if c₁ = c₂ then M₁ (Matrix.single a₁ a₂ 1) b₁ b₂ * M (a₁, c₁) (a₂, c₂) else 0 := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, sum_diag_single_of_tracePreserving h₂]
    split_ifs <;> ring
  calc ∑ d, ∑ a₁, ∑ a₂, ∑ c₁, ∑ c₂, M₁ (Matrix.single a₁ a₂ 1) b₁ b₂ *
          M₂ (Matrix.single c₁ c₂ 1) d d * M (a₁, c₁) (a₂, c₂)
      = ∑ a₁, ∑ a₂, ∑ c₁, ∑ c₂, ∑ d, M₁ (Matrix.single a₁ a₂ 1) b₁ b₂ *
          M₂ (Matrix.single c₁ c₂ 1) d d * M (a₁, c₁) (a₂, c₂) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a₁ _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a₂ _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c₁ _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ a₁, ∑ a₂, (∑ c, M (a₁, c) (a₂, c)) * M₁ (Matrix.single a₁ a₂ 1) b₁ b₂ := by
        refine Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun a₂ _ => ?_
        simp only [hinner, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_mul]
        exact Finset.sum_congr rfl fun c _ => mul_comm _ _

/-- Tracing out the first output of `M₁ ⊗ M₂` gives `M₂` applied to the partial trace of the
input. Only trace preservation of `M₁` is used. -/
theorem kron_traceLeft (M₁ : MatrixMap A B ℂ) (M₂ : MatrixMap C D ℂ)
    (h₁ : M₁.IsTracePreserving) (M : Matrix (A × C) (A × C) ℂ) :
    ((M₁ ⊗ₖₘ M₂) M).traceLeft = M₂ M.traceLeft := by
  ext d₁ d₂
  rw [matrixMap_eq_sum_single M₂ M.traceLeft]
  simp only [Matrix.traceLeft, Matrix.of_apply, MatrixMap.kron_def, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul]
  have hinner (a₁ a₂ : A) (c₁ c₂ : C) :
      ∑ b, M₁ (Matrix.single a₁ a₂ 1) b b * M₂ (Matrix.single c₁ c₂ 1) d₁ d₂ *
          M (a₁, c₁) (a₂, c₂) =
        if a₁ = a₂ then M₂ (Matrix.single c₁ c₂ 1) d₁ d₂ * M (a₁, c₁) (a₂, c₂) else 0 := by
    simp_rw [mul_assoc]
    rw [← Finset.sum_mul, sum_diag_single_of_tracePreserving h₁]
    split_ifs <;> ring
  have hsum (a₁ a₂ : A) :
      ∑ c₁, ∑ c₂, ∑ b, M₁ (Matrix.single a₁ a₂ 1) b b * M₂ (Matrix.single c₁ c₂ 1) d₁ d₂ *
          M (a₁, c₁) (a₂, c₂) =
        if a₁ = a₂ then
          ∑ c₁, ∑ c₂, M₂ (Matrix.single c₁ c₂ 1) d₁ d₂ * M (a₁, c₁) (a₂, c₂) else 0 := by
    split_ifs with h <;> simp [hinner, h]
  calc ∑ b, ∑ a₁, ∑ a₂, ∑ c₁, ∑ c₂, M₁ (Matrix.single a₁ a₂ 1) b b *
          M₂ (Matrix.single c₁ c₂ 1) d₁ d₂ * M (a₁, c₁) (a₂, c₂)
      = ∑ a₁, ∑ a₂, ∑ c₁, ∑ c₂, ∑ b, M₁ (Matrix.single a₁ a₂ 1) b b *
          M₂ (Matrix.single c₁ c₂ 1) d₁ d₂ * M (a₁, c₁) (a₂, c₂) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a₁ _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a₂ _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c₁ _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ a, ∑ c₁, ∑ c₂, M₂ (Matrix.single c₁ c₂ 1) d₁ d₂ * M (a, c₁) (a, c₂) := by
        refine Finset.sum_congr rfl fun a₁ _ => ?_
        simp only [hsum, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    _ = ∑ c₁, ∑ c₂, (∑ a, M (a, c₁) (a, c₂)) * M₂ (Matrix.single c₁ c₂ 1) d₁ d₂ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c₁ _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c₂ _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => mul_comm _ _

end kron

section channels

variable {dA eA dB eB : Type*} [Fintype dA] [Fintype eA] [Fintype dB] [Fintype eB]
variable [DecidableEq dA] [DecidableEq eA] [DecidableEq dB] [DecidableEq eB]

/-- The first marginal of a product-channel output, for any input state. -/
theorem prod_apply_traceRight (Φ : CPTPMap dA eA) (Ω : CPTPMap dB eB) (ρ : MState (dA × dB)) :
    ((Φ ⊗ᶜᵖ Ω) ρ).traceRight = Φ ρ.traceRight := by
  apply MState.ext_m
  change ((Φ ⊗ᶜᵖ Ω) ρ).m.traceRight = (Φ ρ.traceRight).m
  rw [CPTPMap.mat_coe_eq_apply_mat, CPTPMap.mat_coe_eq_apply_mat]
  exact kron_traceRight Φ.map Ω.map Ω.TP ρ.m

/-- The second marginal of a product-channel output, for any input state. -/
theorem prod_apply_traceLeft (Φ : CPTPMap dA eA) (Ω : CPTPMap dB eB) (ρ : MState (dA × dB)) :
    ((Φ ⊗ᶜᵖ Ω) ρ).traceLeft = Ω ρ.traceLeft := by
  apply MState.ext_m
  change ((Φ ⊗ᶜᵖ Ω) ρ).m.traceLeft = (Ω ρ.traceLeft).m
  rw [CPTPMap.mat_coe_eq_apply_mat, CPTPMap.mat_coe_eq_apply_mat]
  exact kron_traceLeft Φ.map Ω.map Φ.TP ρ.m

/-- Output-entropy subadditivity of a product channel; entangled inputs are allowed. -/
theorem entropy_prod_channel_le (Φ : CPTPMap dA eA) (Ω : CPTPMap dB eB) (ρ : MState (dA × dB)) :
    Sᵥₙ ((Φ ⊗ᶜᵖ Ω) ρ) ≤ Sᵥₙ (Φ ρ.traceRight) + Sᵥₙ (Ω ρ.traceLeft) := by
  have h := Sᵥₙ_subadditivity ((Φ ⊗ᶜᵖ Ω) ρ)
  rwa [prod_apply_traceRight, prod_apply_traceLeft] at h

end channels

section concavity

variable {d α : Type*} [Fintype d] [DecidableEq d] [Fintype α]

theorem entropy_eq_neg_trace_mul_log (ρ : MState d) :
    Sᵥₙ ρ = -(ρ.M.cfc (fun x => x * Real.log x)).trace := by
  rw [Sᵥₙ_eq_trace_cfc_negMulLog, Real.negMulLog_eq_neg, HermitianMat.cfc_neg_apply,
    HermitianMat.trace_neg]

theorem mix_M (E : MEnsemble d α) :
    (Ensemble.mix E).M = ∑ i, (E.distr i : ℝ) • (E.states i).M := by
  ext1
  rw [HermitianMat.mat_finset_sum]
  simp only [HermitianMat.mat_smul]
  exact Ensemble.mix_of E

/-- Concavity of von Neumann entropy over a finite ensemble. -/
theorem entropy_mix_ge (E : MEnsemble d α) :
    ∑ i, (E.distr i : ℝ) * Sᵥₙ (E.states i) ≤ Sᵥₙ (Ensemble.mix E) := by
  have hJ := (HermitianMat.trace_function_convex_ici Real.convexOn_mul_log).map_sum_le
    (t := Finset.univ) (w := fun i => (E.distr i : ℝ)) (p := fun i => (E.states i).M)
    (fun i _ => Prob.zero_le_coe) E.distr.normalized (fun i _ => (E.states i).nonneg)
  rw [← mix_M] at hJ
  simp only [smul_eq_mul] at hJ
  simp only [entropy_eq_neg_trace_mul_log, mul_neg, Finset.sum_neg_distrib]
  linarith

end concavity

end QubitAdditivity
