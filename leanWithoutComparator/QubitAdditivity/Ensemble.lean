import QuantumInfo.States.Ensemble
import QubitAdditivity.Entropy

noncomputable section
open scoped BigOperators Kronecker

namespace QubitAdditivity

variable {d e f g α β : Type*}
variable [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
variable [Fintype f] [DecidableEq f] [Fintype g] [DecidableEq g]
variable [Fintype α] [Fintype β]

/-- Apply a channel to every member without changing its probability. -/
def outputEnsemble (Φ : CPTPMap d e) (E : MEnsemble d α) : MEnsemble e α :=
  ⟨fun i => Φ (E.states i), E.distr⟩

/-- The finite-ensemble Holevo expression, in nats. -/
def holevoValue (Φ : CPTPMap d e) (E : MEnsemble d α) : ℝ :=
  Sᵥₙ (Φ (Ensemble.mix E)) - ∑ i, (E.distr i : ℝ) * Sᵥₙ (Φ (E.states i))

/-- Independent sampling of two ensembles, with product input states. -/
def productEnsemble (E : MEnsemble d α) (F : MEnsemble f β) :
    MEnsemble (d × f) (α × β) :=
  ⟨fun i => E.states i.1 ⊗ᴹ F.states i.2, E.distr.prod F.distr⟩

theorem channel_mix (Φ : CPTPMap d e) (E : MEnsemble d α) :
    Φ (Ensemble.mix E) = Ensemble.mix (outputEnsemble Φ E) := by
  apply MState.ext_m
  simp only [CPTPMap.mat_coe_eq_apply_mat, Ensemble.mix_of, outputEnsemble,
    MEnsemble.states]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact Φ.map.map_smul_of_tower (E.distr i : ℝ) (E.states i).m

theorem holevoValue_le_log_card (Φ : CPTPMap d e) (E : MEnsemble d α) :
    holevoValue Φ E ≤ Real.log (Fintype.card e) := by
  have hsum : 0 ≤ ∑ i, (E.distr i : ℝ) * Sᵥₙ (Φ (E.states i)) :=
    Finset.sum_nonneg fun i _ => mul_nonneg Prob.zero_le_coe (Sᵥₙ_nonneg _)
  exact (sub_le_self _ hsum).trans (Sᵥₙ_le_log_d _)

theorem productEnsemble_mix (E : MEnsemble d α) (F : MEnsemble f β) :
    Ensemble.mix (productEnsemble E F) = Ensemble.mix E ⊗ᴹ Ensemble.mix F := by
  have hprod (ρ : MState d) (σ : MState f) : (ρ ⊗ᴹ σ).m = ρ.m ⊗ₖ σ.m := rfl
  apply MState.ext_m
  rw [Ensemble.mix_of]
  change (∑ i : α × β, (E.distr.prod F.distr i : ℝ) •
      (E.states i.1 ⊗ᴹ F.states i.2).m) = (Ensemble.mix E ⊗ᴹ Ensemble.mix F).m
  simp_rw [hprod]
  rw [Ensemble.mix_of, Ensemble.mix_of]
  ext ⟨a, b⟩ ⟨c, k⟩
  simp only [ProbDistribution.prod_def, Prob.coe_mul, Matrix.kronecker_apply,
    Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul, Complex.ofReal_mul,
    Fintype.sum_prod_type]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Product sampling gives exactly the sum of the two Holevo values. -/
theorem holevoValue_product (Φ : CPTPMap d e) (Ω : CPTPMap f g)
    (E : MEnsemble d α) (F : MEnsemble f β) :
    holevoValue (Φ ⊗ᶜᵖ Ω) (productEnsemble E F) =
      holevoValue Φ E + holevoValue Ω F := by
  unfold holevoValue
  rw [productEnsemble_mix, CPTPMap.prod_apply_prod, entropy_prod]
  have hsum :
      (∑ i : α × β, ((productEnsemble E F).distr i : ℝ) *
        Sᵥₙ ((Φ ⊗ᶜᵖ Ω) ((productEnsemble E F).states i))) =
      (∑ i, (E.distr i : ℝ) * Sᵥₙ (Φ (E.states i))) +
      (∑ j, (F.distr j : ℝ) * Sᵥₙ (Ω (F.states j))) := by
    simp only [productEnsemble, MEnsemble.states,
      ProbDistribution.prod_def, Prob.coe_mul, Fintype.sum_prod_type,
      CPTPMap.prod_apply_prod, entropy_prod, mul_add, Finset.sum_add_distrib]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    simp only [← Finset.sum_mul, ProbDistribution.normalized, one_mul]
  rw [hsum]
  ring

theorem holevoValue_reindex (Φ : CPTPMap d e) (E : MEnsemble d α) (σ : α ≃ β) :
    holevoValue Φ (Ensemble.congrMEnsemble σ E) = holevoValue Φ E := by
  unfold holevoValue
  rw [Ensemble.mix_congrMEnsemble_eq_mix]
  congr 1
  simp only [Ensemble.congrMEnsemble, ProbDistribution.congrRandVar,
    Equiv.coe_fn_mk, MEnsemble.states, Function.comp_apply,
    ProbDistribution.congr_apply]
  exact Equiv.sum_comp σ.symm (fun i : α => (E.distr i : ℝ) * Sᵥₙ (Φ (E.states i)))

end QubitAdditivity
