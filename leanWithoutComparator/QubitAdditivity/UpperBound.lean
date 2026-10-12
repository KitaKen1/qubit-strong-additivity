import QubitAdditivity.Marginal
import QubitAdditivity.Target

/-! The Holevo upper bound for a product channel, from an entropy inequality for pure inputs.
Only explicit finite ensembles are used: no convex roof, infimum, or approximation. -/

noncomputable section
open scoped BigOperators

namespace QubitAdditivity

section sigma

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {ι : Type*} [Fintype ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]

/-- Two-stage weights: first `i` with probability `p i`, then `j` with probability `q i j`. -/
def sigmaDistr (p : ProbDistribution ι) (q : ∀ i, ProbDistribution (κ i)) :
    ProbDistribution (Σ i, κ i) :=
  ProbDistribution.mk' (fun x => (p x.1 : ℝ) * (q x.1 x.2 : ℝ))
    (fun _ => mul_nonneg Prob.zero_le_coe Prob.zero_le_coe)
    (by
      rw [Fintype.sum_sigma]
      simp only [← Finset.mul_sum, ProbDistribution.normalized, mul_one])

theorem sigmaDistr_apply (p : ProbDistribution ι) (q : ∀ i, ProbDistribution (κ i))
    (x : Σ i, κ i) : (sigmaDistr p q x : ℝ) = (p x.1 : ℝ) * (q x.1 x.2 : ℝ) := rfl

/-- Merge the ensembles `E i`, chosen with probabilities `p i`, into one ensemble. -/
def sigmaEnsemble (p : ProbDistribution ι) (E : ∀ i, MEnsemble d (κ i)) :
    MEnsemble d (Σ i, κ i) :=
  ⟨fun x => (E x.1).states x.2, sigmaDistr p fun i => (E i).distr⟩

theorem sigmaEnsemble_sum (p : ProbDistribution ι) (E : ∀ i, MEnsemble d (κ i))
    (f : MState d → ℝ) :
    ∑ x, ((sigmaEnsemble p E).distr x : ℝ) * f ((sigmaEnsemble p E).states x) =
      ∑ i, (p i : ℝ) * ∑ j, ((E i).distr j : ℝ) * f ((E i).states j) := by
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  change (p i : ℝ) * ((E i).distr j : ℝ) * f ((E i).states j) = _
  ring

theorem sigmaEnsemble_mix (p : ProbDistribution ι) (E : ∀ i, MEnsemble d (κ i)) :
    (Ensemble.mix (sigmaEnsemble p E)).m = ∑ i, (p i : ℝ) • (Ensemble.mix (E i)).m := by
  rw [Ensemble.mix_of, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Ensemble.mix_of, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul]
  rfl

end sigma

section reindex

variable {d e α β : Type*} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
variable [Fintype α] [Fintype β]

/-- Average output entropy of an ensemble through a channel. -/
def avgOutputEntropy (Φ : CPTPMap d e) (E : MEnsemble d α) : ℝ :=
  ∑ i, (E.distr i : ℝ) * Sᵥₙ (Φ (E.states i))

theorem holevoValue_eq (Φ : CPTPMap d e) (E : MEnsemble d α) :
    holevoValue Φ E = Sᵥₙ (Φ (Ensemble.mix E)) - avgOutputEntropy Φ E := rfl

theorem avgOutputEntropy_reindex (Φ : CPTPMap d e) (E : MEnsemble d α) (σ : α ≃ β) :
    avgOutputEntropy Φ (Ensemble.congrMEnsemble σ E) = avgOutputEntropy Φ E := by
  have h := holevoValue_reindex Φ E σ
  rw [holevoValue_eq, holevoValue_eq, Ensemble.mix_congrMEnsemble_eq_mix] at h
  linarith

end reindex

section bounds

variable {dA eA dB eB : Type*} [Fintype dA] [Fintype eA] [Fintype dB] [Fintype eB]
variable [DecidableEq dA] [DecidableEq eA] [DecidableEq dB] [DecidableEq eB]

/-- Explicit ensembles for the two marginals of `ρ`, with total average output entropy at
most `s`. -/
def SplitBelow (Φ : CPTPMap dA eA) (Ω : CPTPMap dB eB) (ρ : MState (dA × dB)) (s : ℝ) :
    Prop :=
  ∃ (k l : ℕ) (E : MEnsemble dA (Fin k)) (F : MEnsemble dB (Fin l)),
    Ensemble.mix E = ρ.traceRight ∧ Ensemble.mix F = ρ.traceLeft ∧
      avgOutputEntropy Φ E + avgOutputEntropy Ω F ≤ s

/-- The pure-input inequality that TC4, the qubit normal form and the partner marginal are to
supply. This is a proposition, not an assumption of any theorem in the main development. -/
def PureInputBound (Φ : CPTPMap dA eA) (Ω : CPTPMap dB eB) : Prop :=
  ∀ ψ : Ket (dA × dB), SplitBelow Φ Ω (MState.pure ψ) (Sᵥₙ ((Φ ⊗ᶜᵖ Ω) (MState.pure ψ)))

/-- The same inequality for all, possibly mixed, inputs. -/
def MixedInputBound (Φ : CPTPMap dA eA) (Ω : CPTPMap dB eB) : Prop :=
  ∀ ρ : MState (dA × dB), SplitBelow Φ Ω ρ (Sᵥₙ ((Φ ⊗ᶜᵖ Ω) ρ))

theorem traceRight_mix_m {α : Type*} [Fintype α] (G : MEnsemble (dA × dB) α) :
    (Ensemble.mix G).traceRight.m = ∑ i, (G.distr i : ℝ) • (G.states i).traceRight.m := by
  change (Ensemble.mix G).m.traceRight = ∑ i, (G.distr i : ℝ) • (G.states i).m.traceRight
  rw [Ensemble.mix_of]
  ext a₁ a₂
  simp only [Matrix.traceRight, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum]

theorem traceLeft_mix_m {α : Type*} [Fintype α] (G : MEnsemble (dA × dB) α) :
    (Ensemble.mix G).traceLeft.m = ∑ i, (G.distr i : ℝ) • (G.states i).traceLeft.m := by
  change (Ensemble.mix G).m.traceLeft = ∑ i, (G.distr i : ℝ) • (G.states i).m.traceLeft
  rw [Ensemble.mix_of]
  ext b₁ b₂
  simp only [Matrix.traceLeft, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum]

/-- Splits of the members of an ensemble combine into a split of its average. -/
theorem splitBelow_mix {α : Type*} [Fintype α] (Φ : CPTPMap dA eA) (Ω : CPTPMap dB eB)
    (G : MEnsemble (dA × dB) α) (s : α → ℝ) (h : ∀ i, SplitBelow Φ Ω (G.states i) (s i)) :
    SplitBelow Φ Ω (Ensemble.mix G) (∑ i, (G.distr i : ℝ) * s i) := by
  choose k l E F hE hF hs using h
  let σE := Fintype.equivFin (Σ i, Fin (k i))
  let σF := Fintype.equivFin (Σ i, Fin (l i))
  refine ⟨Fintype.card (Σ i, Fin (k i)), Fintype.card (Σ i, Fin (l i)),
    Ensemble.congrMEnsemble σE (sigmaEnsemble G.distr E),
    Ensemble.congrMEnsemble σF (sigmaEnsemble G.distr F), ?_, ?_, ?_⟩
  · rw [Ensemble.mix_congrMEnsemble_eq_mix]
    apply MState.ext_m
    rw [sigmaEnsemble_mix, traceRight_mix_m]
    simp only [hE]
  · rw [Ensemble.mix_congrMEnsemble_eq_mix]
    apply MState.ext_m
    rw [sigmaEnsemble_mix, traceLeft_mix_m]
    simp only [hF]
  · rw [avgOutputEntropy_reindex, avgOutputEntropy_reindex]
    unfold avgOutputEntropy
    rw [sigmaEnsemble_sum G.distr E (fun ρ => Sᵥₙ (Φ ρ)),
      sigmaEnsemble_sum G.distr F (fun ρ => Sᵥₙ (Ω ρ)), ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (hs i) Prob.zero_le_coe

/-- Spectral decomposition reduces the mixed-input inequality to pure inputs. -/
theorem mixedInputBound_of_pure (Φ : CPTPMap dA eA) (Ω : CPTPMap dB eB)
    (h : PureInputBound Φ Ω) : MixedInputBound Φ Ω := by
  intro ρ
  let G : MEnsemble (dA × dB) (dA × dB) := ↑(Ensemble.spectral_ensemble ρ)
  have hmix : Ensemble.mix G = ρ := Ensemble.spectral_ensemble_mix
  have hsplit := splitBelow_mix Φ Ω G (fun i => Sᵥₙ ((Φ ⊗ᶜᵖ Ω) (G.states i)))
    (fun i => h ((Ensemble.spectral_ensemble ρ).states i))
  rw [hmix] at hsplit
  obtain ⟨k, l, E, F, hE, hF, hs⟩ := hsplit
  refine ⟨k, l, E, F, hE, hF, hs.trans ?_⟩
  have hc := entropy_mix_ge (outputEnsemble (Φ ⊗ᶜᵖ Ω) G)
  rw [← channel_mix, hmix] at hc
  exact hc

/-- One ensemble at a time: the Holevo value of the product channel is bounded. -/
theorem holevoValue_prod_le (Φ : CPTPMap dA eA) (Ω : CPTPMap dB eB)
    (h : MixedInputBound Φ Ω) {k : ℕ} (G : MEnsemble (dA × dB) (Fin k)) :
    holevoValue (Φ ⊗ᶜᵖ Ω) G ≤ holevo Φ + holevo Ω := by
  obtain ⟨k₁, l₁, E, F, hE, hF, hs⟩ :=
    splitBelow_mix Φ Ω G (fun i => Sᵥₙ ((Φ ⊗ᶜᵖ Ω) (G.states i))) (fun i => h (G.states i))
  have hsub := entropy_prod_channel_le Φ Ω (Ensemble.mix G)
  have h₁ := holevoValue_le_holevo Φ E
  have h₂ := holevoValue_le_holevo Ω F
  rw [holevoValue_eq, hE] at h₁
  rw [holevoValue_eq, hF] at h₂
  rw [holevoValue_eq]
  have hG : avgOutputEntropy (Φ ⊗ᶜᵖ Ω) G =
      ∑ i, (G.distr i : ℝ) * Sᵥₙ ((Φ ⊗ᶜᵖ Ω) (G.states i)) := rfl
  linarith

theorem holevo_prod_le_of_mixedInputBound [Nonempty dA] [Nonempty dB]
    (Φ : CPTPMap dA eA) (Ω : CPTPMap dB eB) (h : MixedInputBound Φ Ω) :
    holevo (Φ ⊗ᶜᵖ Ω) ≤ holevo Φ + holevo Ω := by
  apply csSup_le (holevoValues_nonempty _)
  rintro v ⟨k, G, rfl⟩
  exact holevoValue_prod_le Φ Ω h G

/-- Strong additivity for one pair of channels, from the pure-input inequality. -/
theorem holevo_prod_eq_of_pureInputBound [Nonempty dA] [Nonempty dB]
    (Φ : CPTPMap dA eA) (Ω : CPTPMap dB eB) (h : PureInputBound Φ Ω) :
    holevo (Φ ⊗ᶜᵖ Ω) = holevo Φ + holevo Ω :=
  le_antisymm (holevo_prod_le_of_mixedInputBound Φ Ω (mixedInputBound_of_pure Φ Ω h))
    (holevo_product_ge Φ Ω)

end bounds

/-- What remains for the main theorem: the pure-input inequality for every qubit channel and
every finite-dimensional partner. An unproved proposition, not an axiom. -/
def QubitPureInputBound : Prop :=
  ∀ (Φ : CPTPMap (Fin 2) (Fin 2)) (n m : ℕ) (Ω : CPTPMap (Fin (n + 1)) (Fin (m + 1))),
    PureInputBound Φ Ω

theorem strongAdditivity_of_qubitPureInputBound (h : QubitPureInputBound) :
    GeneralQubitStrongAdditivity :=
  fun Φ n m Ω => holevo_prod_eq_of_pureInputBound Φ Ω (h Φ n m Ω)

end QubitAdditivity
