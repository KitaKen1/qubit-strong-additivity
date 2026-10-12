import QubitAdditivity.GeneralResult
import QubitAdditivity.Presentation.Model

/-!
# The Mathlib-only Kraus statement, proved from the Physlib-based main theorem

`Presentation/Model.lean` states strong Holevo additivity with Kraus families and plain
matrices. This file identifies that vocabulary with the bundled channels, states and ensembles
used by the proof, and transfers `GeneralResult.strongHolevoAdditivity`.

The identification is exact in both directions: every trace-preserving Kraus family is a
`CPTPMap` with the same action and the same Holevo information (`channel`, `channel_m`,
`holevo_eq`), and every `CPTPMap` arises this way (`exists_channel_eq`).

The final section adds additivity over independent uses, `χ(Φ^{⊗n}) = n χ(Φ)`, by induction
on `n` with the partner `Φ^{⊗n}`.
-/

set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators ComplexOrder Kronecker MatrixMap
open Matrix

namespace QubitAdditivity.Presentation

universe u v w u' v' w'

section single

variable {dIn : Type u} {dOut : Type v} {ρ : Type w}
  [Fintype dIn] [DecidableEq dIn] [Fintype dOut] [DecidableEq dOut] [Fintype ρ]

theorem entropy_eq (P : Matrix dIn dIn ℂ) :
    QubitHolevo.entropy P = OpenAIEntropy.entropy P := rfl

theorem isState_iff (P : Matrix dIn dIn ℂ) :
    QubitHolevo.IsState P ↔ OpenAIEntropy.IsState P := Iff.rfl

/-- The bundled channel of a trace-preserving Kraus family. -/
def channel (K : ρ → Matrix dOut dIn ℂ) (hK : QubitHolevo.IsKraus K) : CPTPMap dIn dOut :=
  CPTPMap.of_kraus_CPTPMap K hK

omit [DecidableEq dIn] [Fintype dOut] [DecidableEq dOut] in
theorem of_kraus_apply (K : ρ → Matrix dOut dIn ℂ) (P : Matrix dIn dIn ℂ) :
    MatrixMap.of_kraus K K P = QubitHolevo.applyKraus K P := by
  simp [MatrixMap.of_kraus, QubitHolevo.applyKraus]

/-- The bundled channel acts on state matrices by the Kraus formula. -/
theorem channel_m (K : ρ → Matrix dOut dIn ℂ) (hK : QubitHolevo.IsKraus K) (σ : MState dIn) :
    (channel K hK σ).m = QubitHolevo.applyKraus K σ.m := by
  rw [CPTPMap.mat_coe_eq_apply_mat]
  exact of_kraus_apply K σ.m

theorem entropy_channel (K : ρ → Matrix dOut dIn ℂ) (hK : QubitHolevo.IsKraus K)
    (σ : MState dIn) :
    Sᵥₙ (channel K hK σ) = QubitHolevo.entropy (QubitHolevo.applyKraus K σ.m) := by
  rw [entropy_eq_openai, channel_m]
  rfl

/-- Every bundled channel is the channel of a trace-preserving Kraus family. -/
theorem exists_channel_eq (Φ : CPTPMap dIn dOut) :
    ∃ (K : dOut × dIn → Matrix dOut dIn ℂ) (hK : QubitHolevo.IsKraus K), Φ = channel K hK := by
  obtain ⟨W, hW, hsum⟩ := exists_kraus_family Φ
  exact ⟨W, hsum, CPTPMap.ext hW⟩

/-- An ensemble of the statement vocabulary as a bundled ensemble. -/
def toMEnsemble (E : QubitHolevo.Ensemble dIn) : MEnsemble dIn (Fin E.size) :=
  ⟨fun a => stateOf (E.signal a) (E.signal_state a),
    ProbDistribution.mk' E.weight E.weight_nonneg E.weight_sum⟩

theorem toMEnsemble_mix_m (E : QubitHolevo.Ensemble dIn) :
    (Ensemble.mix (toMEnsemble E)).m = ∑ a, E.weight a • E.signal a := by
  rw [Ensemble.mix_of]
  rfl

theorem holevoValue_toMEnsemble (K : ρ → Matrix dOut dIn ℂ) (hK : QubitHolevo.IsKraus K)
    (E : QubitHolevo.Ensemble dIn) :
    holevoValue (channel K hK) (toMEnsemble E) = QubitHolevo.ensembleValue K E := by
  unfold holevoValue QubitHolevo.ensembleValue
  rw [entropy_channel, toMEnsemble_mix_m]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [entropy_channel]
  rfl

/-- A bundled ensemble over `Fin k` as an ensemble of the statement vocabulary. -/
def ofMEnsemble {k : ℕ} (E : MEnsemble dIn (Fin k)) : QubitHolevo.Ensemble dIn where
  size := k
  weight a := (E.distr a : ℝ)
  weight_nonneg _ := Prob.zero_le_coe
  weight_sum := E.distr.normalized
  signal a := (E.states a).m
  signal_state a := matrix_isState (E.states a)

theorem ensembleValue_ofMEnsemble (K : ρ → Matrix dOut dIn ℂ) (hK : QubitHolevo.IsKraus K)
    {k : ℕ} (E : MEnsemble dIn (Fin k)) :
    QubitHolevo.ensembleValue K (ofMEnsemble E) = holevoValue (channel K hK) E := by
  unfold holevoValue QubitHolevo.ensembleValue
  rw [entropy_channel, Ensemble.mix_of]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [entropy_channel]
  rfl

/-- The two vocabularies produce the same set of ensemble values. -/
theorem holevoValues_eq (K : ρ → Matrix dOut dIn ℂ) (hK : QubitHolevo.IsKraus K) :
    holevoValues (channel K hK) = Set.range (QubitHolevo.ensembleValue K) := by
  ext v
  constructor
  · rintro ⟨k, E, rfl⟩
    exact ⟨ofMEnsemble E, ensembleValue_ofMEnsemble K hK E⟩
  · rintro ⟨E, rfl⟩
    exact ⟨E.size, toMEnsemble E, holevoValue_toMEnsemble K hK E⟩

/-- The Holevo information of the statement vocabulary is that of the bundled channel. -/
theorem holevo_eq (K : ρ → Matrix dOut dIn ℂ) (hK : QubitHolevo.IsKraus K) :
    holevo (channel K hK) = QubitHolevo.holevo K := by
  -- The set in the definition of `QubitHolevo.holevo`, with its ensembles bundled.
  have hset : Set.range (QubitHolevo.ensembleValue K) =
      {x | ∃ (n : ℕ) (p : Fin n → ℝ) (σ : Fin n → Matrix dIn dIn ℂ),
        (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1 ∧ (∀ a, (σ a).PosSemidef ∧ (σ a).trace = 1) ∧
        x = QubitHolevo.entropy (QubitHolevo.applyKraus K (∑ a, p a • σ a)) -
          ∑ a, p a * QubitHolevo.entropy (QubitHolevo.applyKraus K (σ a))} := by
    ext x
    constructor
    · rintro ⟨E, rfl⟩
      exact ⟨E.size, E.weight, E.signal, E.weight_nonneg, E.weight_sum, E.signal_state, rfl⟩
    · rintro ⟨n, p, σ, hp, hsum, hσ, rfl⟩
      exact ⟨⟨n, p, hp, hsum, σ, hσ⟩, rfl⟩
  unfold holevo
  rw [holevoValues_eq K hK, hset]
  rfl

/-- The supremum defining `QubitHolevo.holevo` is over a set that is bounded above. -/
theorem ensembleValues_bddAbove (K : ρ → Matrix dOut dIn ℂ) (hK : QubitHolevo.IsKraus K) :
    BddAbove (Set.range (QubitHolevo.ensembleValue K)) := by
  rw [← holevoValues_eq K hK]
  exact holevoValues_bddAbove _

/-- The supremum defining `QubitHolevo.holevo` is over a nonempty set. -/
theorem ensembleValues_nonempty [Nonempty dIn] (K : ρ → Matrix dOut dIn ℂ)
    (hK : QubitHolevo.IsKraus K) : (Set.range (QubitHolevo.ensembleValue K)).Nonempty := by
  rw [← holevoValues_eq K hK]
  exact holevoValues_nonempty _

end single

section tensor

variable {dIn : Type u} {dOut : Type v} {ρ : Type w} {dIn' : Type u'} {dOut' : Type v'}
  {ρ' : Type w'}
  [Fintype dIn] [DecidableEq dIn] [Fintype dOut] [DecidableEq dOut] [Fintype ρ]
  [Fintype dIn'] [DecidableEq dIn'] [Fintype dOut'] [DecidableEq dOut'] [Fintype ρ']

omit [DecidableEq dOut] [DecidableEq dOut'] in
/-- The product of two trace-preserving Kraus families is trace preserving. -/
theorem isKraus_tensor {K : ρ → Matrix dOut dIn ℂ} {L : ρ' → Matrix dOut' dIn' ℂ}
    (hK : QubitHolevo.IsKraus K) (hL : QubitHolevo.IsKraus L) :
    QubitHolevo.IsKraus (QubitHolevo.tensorKraus K L) := by
  have h := (MatrixMap.IsTracePreserving.of_kraus_isTracePreserving K K hK).kron
    (MatrixMap.IsTracePreserving.of_kraus_isTracePreserving L L hL)
  rw [MatrixMap.kron_of_kraus] at h
  exact kraus_sum_eq_one_of_TP (K := QubitHolevo.tensorKraus K L) h

omit [DecidableEq dOut] [DecidableEq dOut'] in
/-- The product Kraus family is the Kraus family of the tensor product channel. -/
theorem channel_tensor {K : ρ → Matrix dOut dIn ℂ} {L : ρ' → Matrix dOut' dIn' ℂ}
    (hK : QubitHolevo.IsKraus K) (hL : QubitHolevo.IsKraus L) :
    channel (QubitHolevo.tensorKraus K L) (isKraus_tensor hK hL) =
      channel K hK ⊗ᶜᵖ channel L hL := by
  apply CPTPMap.ext
  exact (MatrixMap.kron_of_kraus K L).symm

end tensor

/-- Strong Holevo additivity in Kraus form, for arbitrary finite index types. -/
theorem strong_additivity_kraus {ρ : Type w} {ρ' : Type w'} [Fintype ρ] [Fintype ρ']
    {dB eB : Type} [Fintype dB] [DecidableEq dB] [Fintype eB] [DecidableEq eB] [Nonempty dB]
    (K : ρ → Matrix (Fin 2) (Fin 2) ℂ) (hK : QubitHolevo.IsKraus K)
    (L : ρ' → Matrix eB dB ℂ) (hL : QubitHolevo.IsKraus L) :
    QubitHolevo.holevo (QubitHolevo.tensorKraus K L) =
      QubitHolevo.holevo K + QubitHolevo.holevo L := by
  rw [← holevo_eq K hK, ← holevo_eq L hL, ← holevo_eq _ (isKraus_tensor hK hL),
    channel_tensor]
  exact GeneralResult.strongHolevoAdditivity _ _

section relabel

variable {dIn : Type u} {dOut : Type v} {dIn' : Type u'} {dOut' : Type v'}
  [Fintype dIn] [DecidableEq dIn] [Fintype dOut] [DecidableEq dOut]
  [Fintype dIn'] [DecidableEq dIn'] [Fintype dOut'] [DecidableEq dOut']

theorem holevoValue_compose {α : Type*} [Fintype α] (Φ : CPTPMap dIn dOut)
    (Ψ : CPTPMap dIn' dIn) (E : MEnsemble dIn' α) :
    holevoValue (Φ ∘ₘ Ψ) E = holevoValue Φ (outputEnsemble Ψ E) := by
  unfold holevoValue
  rw [CPTPMap.compose_eq, channel_mix]
  rfl

/-- Preprocessing the input cannot produce new ensemble values. -/
theorem holevoValues_compose_subset (Φ : CPTPMap dIn dOut) (Ψ : CPTPMap dIn' dIn) :
    holevoValues (Φ ∘ₘ Ψ) ⊆ holevoValues Φ := by
  rintro v ⟨k, E, rfl⟩
  exact ⟨k, outputEnsemble Ψ E, (holevoValue_compose Φ Ψ E).symm⟩

theorem ofEquiv_comp_symm (e : dIn' ≃ dIn) :
    CPTPMap.ofEquiv e ∘ₘ CPTPMap.ofEquiv e.symm = CPTPMap.id := by
  apply CPTPMap.funext
  intro σ
  apply MState.ext_m
  simp

/-- Relabelling the input system does not change the Holevo information. -/
theorem holevo_input_equiv (e : dIn' ≃ dIn) (Φ : CPTPMap dIn dOut) :
    holevo (Φ ∘ₘ CPTPMap.ofEquiv e) = holevo Φ := by
  unfold holevo
  congr 1
  refine Set.Subset.antisymm (holevoValues_compose_subset _ _) ?_
  have h : Φ = (Φ ∘ₘ CPTPMap.ofEquiv e) ∘ₘ CPTPMap.ofEquiv e.symm := by
    rw [CPTPMap.compose_assoc, ofEquiv_comp_symm, CPTPMap.compose_id]
  intro v hv
  rw [h] at hv
  exact holevoValues_compose_subset _ _ hv

theorem holevoValue_output_equiv {α : Type*} [Fintype α] (e : dOut ≃ dOut')
    (Φ : CPTPMap dIn dOut) (E : MEnsemble dIn α) :
    holevoValue (CPTPMap.ofEquiv e ∘ₘ Φ) E = holevoValue Φ E := by
  unfold holevoValue
  simp only [CPTPMap.compose_eq, CPTPMap.ofEquiv_apply, Sᵥₙ_relabel]

/-- Relabelling the output system does not change the Holevo information. -/
theorem holevo_output_equiv (e : dOut ≃ dOut') (Φ : CPTPMap dIn dOut) :
    holevo (CPTPMap.ofEquiv e ∘ₘ Φ) = holevo Φ := by
  unfold holevo holevoValues
  congr 1
  ext v
  simp only [holevoValue_output_equiv]

variable {ρ : Type w} {ρ' : Type w'} [Fintype ρ] [Fintype ρ']

omit [Fintype dIn] [DecidableEq dOut] [Fintype dIn'] [DecidableEq dOut'] in
/-- Trace preservation is unchanged by relabelling the systems and the Kraus index. -/
theorem isKraus_reindex (eo : dOut ≃ dOut') (ei : dIn ≃ dIn') (er : ρ ≃ ρ')
    {K : ρ → Matrix dOut dIn ℂ} (hK : QubitHolevo.IsKraus K)
    {K' : ρ' → Matrix dOut' dIn' ℂ}
    (h : ∀ r, K' (er r) = (K r).submatrix eo.symm ei.symm) : QubitHolevo.IsKraus K' := by
  unfold QubitHolevo.IsKraus at hK ⊢
  rw [← Equiv.sum_comp er]
  have hsum : ∑ r, ((K r)ᴴ * K r).submatrix ei.symm ei.symm =
      (∑ r, (K r)ᴴ * K r).submatrix ei.symm ei.symm :=
    (map_sum (Matrix.reindexLinearEquiv ℂ ℂ ei ei) (fun r => (K r)ᴴ * K r) Finset.univ).symm
  rw [← Matrix.submatrix_one_equiv ei.symm, ← hK, ← hsum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [h, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]

omit [DecidableEq dOut'] in
/-- Relabelling the systems and the Kraus index conjugates the channel by relabellings. -/
theorem channel_reindex (eo : dOut ≃ dOut') (ei : dIn ≃ dIn') (er : ρ ≃ ρ')
    {K : ρ → Matrix dOut dIn ℂ} (hK : QubitHolevo.IsKraus K)
    {K' : ρ' → Matrix dOut' dIn' ℂ} (hK' : QubitHolevo.IsKraus K')
    (h : ∀ r, K' (er r) = (K r).submatrix eo.symm ei.symm) :
    channel K' hK' = CPTPMap.ofEquiv eo ∘ₘ channel K hK ∘ₘ CPTPMap.ofEquiv ei.symm := by
  apply CPTPMap.ext
  apply LinearMap.ext
  intro X
  change MatrixMap.of_kraus K' K' X =
    (MatrixMap.of_kraus K K (X.submatrix ei ei)).submatrix eo.symm eo.symm
  rw [of_kraus_apply, of_kraus_apply]
  unfold QubitHolevo.applyKraus
  rw [← Equiv.sum_comp er]
  have hsum := map_sum (Matrix.reindexLinearEquiv ℂ ℂ eo eo)
    (fun r => K r * X.submatrix ei ei * (K r)ᴴ) Finset.univ
  refine Eq.trans ?_ hsum.symm
  refine Finset.sum_congr rfl fun r _ => ?_
  have hX : X = (X.submatrix ei ei).submatrix ei.symm ei.symm := by simp
  rw [h]
  conv_lhs => rw [hX]
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  rfl

/-- The Holevo information of the statement vocabulary is unchanged by relabelling. -/
theorem holevo_reindex (eo : dOut ≃ dOut') (ei : dIn ≃ dIn') (er : ρ ≃ ρ')
    {K : ρ → Matrix dOut dIn ℂ} (hK : QubitHolevo.IsKraus K)
    {K' : ρ' → Matrix dOut' dIn' ℂ}
    (h : ∀ r, K' (er r) = (K r).submatrix eo.symm ei.symm) :
    QubitHolevo.holevo K' = QubitHolevo.holevo K := by
  have hK' := isKraus_reindex eo ei er hK h
  rw [← holevo_eq K' hK', ← holevo_eq K hK, channel_reindex eo ei er hK hK' h,
    holevo_input_equiv, holevo_output_equiv]

end relabel

section power

variable {ι : Type u} {κ : Type v} {ρ : Type w}

/-- One more use of the channel is a tensor factor, up to splitting off the first site. -/
theorem powerKraus_succ (K : ρ → Matrix ι κ ℂ) (n : ℕ) (x : ρ × (Fin n → ρ)) :
    QubitHolevo.powerKraus K (n + 1) (Fin.consEquiv (fun _ => ρ) x) =
      (QubitHolevo.tensorKraus K (QubitHolevo.powerKraus K n) x).submatrix
        (Fin.consEquiv (fun _ => ι)).symm (Fin.consEquiv (fun _ => κ)).symm := by
  ext i j
  simp [QubitHolevo.powerKraus, QubitHolevo.tensorKraus, Fin.consEquiv, Fin.prod_univ_succ,
    Fin.tail]

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype ρ]

omit [DecidableEq ι] in
/-- Independent uses of a trace-preserving Kraus family are trace preserving. -/
theorem isKraus_power {K : ρ → Matrix ι κ ℂ} (hK : QubitHolevo.IsKraus K) :
    ∀ n : ℕ, QubitHolevo.IsKraus (QubitHolevo.powerKraus K n)
  | 0 => by
    unfold QubitHolevo.IsKraus
    ext i j
    simp [QubitHolevo.powerKraus, Matrix.mul_apply, Matrix.one_apply, Subsingleton.elim i j]
  | n + 1 =>
    isKraus_reindex (Fin.consEquiv fun _ => ι) (Fin.consEquiv fun _ => κ)
      (Fin.consEquiv fun _ => ρ) (isKraus_tensor hK (isKraus_power hK n)) (powerKraus_succ K n)

end power

section qubitPower

variable {ρ : Type w} [Fintype ρ]

/-- Zero uses carry no information. -/
theorem holevo_power_zero {K : ρ → Matrix (Fin 2) (Fin 2) ℂ} (hK : QubitHolevo.IsKraus K) :
    QubitHolevo.holevo (QubitHolevo.powerKraus K 0) = 0 := by
  have hP := isKraus_power hK 0
  rw [← holevo_eq _ hP]
  refine le_antisymm ?_ (holevo_nonneg _)
  have h := holevo_le_log_card (channel _ hP)
  simpa using h

theorem holevo_power_succ (K : ρ → Matrix (Fin 2) (Fin 2) ℂ) (hK : QubitHolevo.IsKraus K)
    (n : ℕ) :
    QubitHolevo.holevo (QubitHolevo.powerKraus K (n + 1)) =
      QubitHolevo.holevo K + QubitHolevo.holevo (QubitHolevo.powerKraus K n) := by
  rw [holevo_reindex (Fin.consEquiv fun _ => Fin 2) (Fin.consEquiv fun _ => Fin 2)
    (Fin.consEquiv fun _ => ρ) (isKraus_tensor hK (isKraus_power hK n)) (powerKraus_succ K n)]
  exact strong_additivity_kraus K hK _ (isKraus_power hK n)

/-- Additivity over independent uses of a qubit channel, for an arbitrary Kraus index type. -/
theorem power_additivity_kraus (K : ρ → Matrix (Fin 2) (Fin 2) ℂ)
    (hK : QubitHolevo.IsKraus K) :
    ∀ n : ℕ, QubitHolevo.holevo (QubitHolevo.powerKraus K n) = n * QubitHolevo.holevo K
  | 0 => by rw [holevo_power_zero hK]; simp
  | n + 1 => by
    rw [holevo_power_succ K hK n, power_additivity_kraus K hK n]
    push_cast
    ring

end qubitPower

end QubitAdditivity.Presentation

namespace QubitHolevo

/-- Strong Holevo additivity: $\chi(\Phi \otimes \Omega) = \chi(\Phi) + \chi(\Omega)$ for every
qubit channel $\Phi$ and every channel $\Omega$ between systems of positive finite dimension. -/
theorem strong_additivity {r s n m : ℕ}
    (K : Fin r → Matrix (Fin 2) (Fin 2) ℂ) (hK : IsKraus K)
    (L : Fin s → Matrix (Fin (m + 1)) (Fin (n + 1)) ℂ) (hL : IsKraus L) :
    holevo (tensorKraus K L) = holevo K + holevo L :=
  QubitAdditivity.Presentation.strong_additivity_kraus K hK L hL

/-- Additivity over independent uses: $\chi(\Phi^{\otimes n}) = n\,\chi(\Phi)$ for every qubit
channel $\Phi$. -/
theorem power_additivity {r : ℕ} (K : Fin r → Matrix (Fin 2) (Fin 2) ℂ) (hK : IsKraus K)
    (n : ℕ) : holevo (powerKraus K n) = n * holevo K :=
  QubitAdditivity.Presentation.power_additivity_kraus K hK n

end QubitHolevo
