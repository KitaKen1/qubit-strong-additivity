import QubitAdditivity.Ensemble

noncomputable section

namespace QubitAdditivity

variable {d e f g : Type*}
variable [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
variable [Fintype f] [DecidableEq f] [Fintype g] [DecidableEq g]

/-- All finite ensembles, including arbitrary mixed and entangled inputs. -/
def holevoValues (Φ : CPTPMap d e) : Set ℝ :=
  {v | ∃ k : ℕ, ∃ E : MEnsemble d (Fin k), holevoValue Φ E = v}

/-- The single-use Holevo information is the supremum over all finite ensembles. -/
def holevo (Φ : CPTPMap d e) : ℝ := sSup (holevoValues Φ)

theorem holevoValues_bddAbove (Φ : CPTPMap d e) : BddAbove (holevoValues Φ) := by
  refine ⟨Real.log (Fintype.card e), ?_⟩
  rintro v ⟨k, E, rfl⟩
  exact holevoValue_le_log_card Φ E

theorem zero_mem_holevoValues [Nonempty d] (Φ : CPTPMap d e) :
    0 ∈ holevoValues Φ := by
  let E : MEnsemble d (Fin 1) :=
    ⟨fun _ => MState.uniform, ProbDistribution.constant 0⟩
  refine ⟨1, E, ?_⟩
  simp only [holevoValue, E, Ensemble.mix, ProbDistribution.expect_val_constant]
  simp [MEnsemble.states, ProbDistribution.constant]

theorem holevoValues_nonempty [Nonempty d] (Φ : CPTPMap d e) :
    (holevoValues Φ).Nonempty := ⟨0, zero_mem_holevoValues Φ⟩

theorem holevo_nonneg [Nonempty d] (Φ : CPTPMap d e) : 0 ≤ holevo Φ :=
  le_csSup (holevoValues_bddAbove Φ) (zero_mem_holevoValues Φ)

theorem holevo_le_log_card [Nonempty d] (Φ : CPTPMap d e) :
    holevo Φ ≤ Real.log (Fintype.card e) := by
  apply csSup_le (holevoValues_nonempty Φ)
  rintro v ⟨k, E, rfl⟩
  exact holevoValue_le_log_card Φ E

theorem holevoValue_le_holevo (Φ : CPTPMap d e) {k : ℕ}
    (E : MEnsemble d (Fin k)) : holevoValue Φ E ≤ holevo Φ :=
  le_csSup (holevoValues_bddAbove Φ) ⟨k, E, rfl⟩

theorem sum_mem_product_holevoValues (Φ : CPTPMap d e) (Ω : CPTPMap f g)
    {a b : ℝ} (ha : a ∈ holevoValues Φ) (hb : b ∈ holevoValues Ω) :
    a + b ∈ holevoValues (Φ ⊗ᶜᵖ Ω) := by
  rcases ha with ⟨k, E, rfl⟩
  rcases hb with ⟨l, F, rfl⟩
  refine ⟨k * l,
    Ensemble.congrMEnsemble (finProdFinEquiv) (productEnsemble E F), ?_⟩
  rw [holevoValue_reindex, holevoValue_product]

/-- The product-ensemble lower bound; valid for all channels, not only qubit channels. -/
theorem holevo_product_ge [Nonempty d] [Nonempty f]
    (Φ : CPTPMap d e) (Ω : CPTPMap f g) :
    holevo Φ + holevo Ω ≤ holevo (Φ ⊗ᶜᵖ Ω) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨a, ha, haε⟩ := exists_lt_of_lt_csSup (holevoValues_nonempty Φ)
    (show holevo Φ - ε / 2 < sSup (holevoValues Φ) by unfold holevo; linarith)
  obtain ⟨b, hb, hbε⟩ := exists_lt_of_lt_csSup (holevoValues_nonempty Ω)
    (show holevo Ω - ε / 2 < sSup (holevoValues Ω) by unfold holevo; linarith)
  have hab : a + b ≤ holevo (Φ ⊗ᶜᵖ Ω) :=
    le_csSup (holevoValues_bddAbove _) (sum_mem_product_holevoValues Φ Ω ha hb)
  linarith

end QubitAdditivity
