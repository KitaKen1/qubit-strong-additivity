import QubitAdditivity.Partner

/-! TC4 gives the pure-input inequality for a normal-form qubit channel and an arbitrary
partner channel. The qubit-side ensemble comes from the two-expectation split, and the
partner-side ensemble from the normalized branch vectors. -/

noncomputable section
open scoped Matrix BigOperators ComplexOrder Kronecker MatrixMap
open Matrix

namespace QubitAdditivity

section ensembles

variable {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]

theorem isState_psd {σ : Matrix d d ℂ} (h : OpenAIEntropy.IsState σ) : σ.PosSemidef := h.1

theorem isState_trace {σ : Matrix d d ℂ} (h : OpenAIEntropy.IsState σ) : σ.trace = 1 := h.2

set_option backward.isDefEq.respectTransparency false in
/-- The `MState` with a given state matrix. -/
def stateOf (σ : Matrix d d ℂ) (h : OpenAIEntropy.IsState σ) : MState d where
  M := ⟨σ, (isState_psd h).1⟩
  nonneg := HermitianMat.zero_le_iff.mpr (isState_psd h)
  tr := by
    have h2 := isState_trace h
    simp [HermitianMat.trace_eq_re_trace, h2]

theorem stateOf_m (σ : Matrix d d ℂ) (h : OpenAIEntropy.IsState σ) : (stateOf σ h).m = σ := rfl

/-- The two-member ensemble `p σ₁ + (1 - p) σ₂`. -/
def pairEnsemble (p : Prob) (σ₁ σ₂ : MState d) : MEnsemble d (Fin 2) :=
  ⟨![σ₁, σ₂], ProbDistribution.coin p⟩

theorem pairEnsemble_mix_m (p : Prob) (σ₁ σ₂ : MState d) :
    (Ensemble.mix (pairEnsemble p σ₁ σ₂)).m = (p : ℝ) • σ₁.m + (1 - (p : ℝ)) • σ₂.m := by
  rw [Ensemble.mix_of, Fin.sum_univ_two]
  simp [pairEnsemble, Prob.coe_one_minus]
  rfl

theorem avgOutputEntropy_pair (Φ : CPTPMap d e) (p : Prob) (σ₁ σ₂ : MState d) :
    avgOutputEntropy Φ (pairEnsemble p σ₁ σ₂) =
      (p : ℝ) * Sᵥₙ (Φ σ₁) + (1 - (p : ℝ)) * Sᵥₙ (Φ σ₂) := by
  simp [avgOutputEntropy, pairEnsemble, Fin.sum_univ_two, Prob.coe_one_minus]
  rfl

variable {I : Type*} [Fintype I] [Nonempty d]

/-- Normalized vectors with weights their squared norms. -/
def vecEnsemble (η : I → d → ℂ) (hη : ∑ i, vecMass (η i) = 1) : MEnsemble d I :=
  ⟨fun i => vecState (η i),
    ProbDistribution.mk' (fun i => vecMass (η i)) (fun _ => vecMass_nonneg _) hη⟩

theorem vecEnsemble_mix_m (η : I → d → ℂ) (hη : ∑ i, vecMass (η i) = 1) :
    (Ensemble.mix (vecEnsemble η hη)).m = ∑ i, vecMulVec (η i) (star (η i)) := by
  rw [Ensemble.mix_of]
  exact Finset.sum_congr rfl fun j _ => vecMass_smul_vecState_m (η j)

theorem avgOutputEntropy_vecEnsemble (Ω : CPTPMap d e) (η : I → d → ℂ)
    (hη : ∑ i, vecMass (η i) = 1) :
    avgOutputEntropy Ω (vecEnsemble η hη) =
      ∑ i, vecMass (η i) * Sᵥₙ (Ω (vecState (η i))) := rfl

end ensembles

theorem trace_vecMulVec_re {d : Type*} [Fintype d] (η : d → ℂ) :
    (Matrix.trace (vecMulVec η (star η))).re = vecMass η := by
  simp only [Matrix.trace, Matrix.diag, vecMulVec_apply, Pi.star_apply, Complex.re_sum, vecMass]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [show star (η x) = (starRingEnd ℂ) (η x) from rfl, Complex.mul_conj, Complex.ofReal_re]

theorem entropy_submatrix_equiv {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : κ ≃ ι) {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    OpenAIEntropy.entropy (A.submatrix e e) = OpenAIEntropy.entropy A := by
  have h := OpenAIEntropy.entropy_reindex e.symm hA
  simpa [Matrix.reindex_apply] using h

namespace QubitNormalForm

variable {J K : Type} [Fintype J] [Fintype K] (N : QubitNormalForm J K)
variable {dB eB : Type} [Fintype dB] [DecidableEq dB] [Fintype eB] [DecidableEq eB]

/-- The branch vectors of `ψ`, grouped by output row: `a`, the `b j`, then `c`, the `d k`. -/
def branches (ψ : Fin 2 × dB → ℂ) : (Unit ⊕ J) ⊕ (Unit ⊕ K) → dB → ℂ
  | .inl (.inl _) => branch N.a ψ
  | .inl (.inr j) => branch (N.b j) ψ
  | .inr (.inl _) => branch N.c ψ
  | .inr (.inr k) => branch (N.d k) ψ

omit [DecidableEq dB] in
theorem sum_branches {X : Type*} [AddCommMonoid X] (ψ : Fin 2 × dB → ℂ) (f : (dB → ℂ) → X) :
    ∑ x, f (N.branches ψ x) =
      f (branch N.a ψ) + ∑ j, f (branch (N.b j) ψ) +
        (f (branch N.c ψ) + ∑ k, f (branch (N.d k) ψ)) := by
  simp [Fintype.sum_sum_type, branches]

theorem branches_mass (h : N.Complete) (ψ : Ket (Fin 2 × dB)) :
    ∑ x, vecMass (N.branches ψ x) = 1 := by
  have ht := congrArg (fun M => (Matrix.trace M).re) (N.traceLeft_pure_eq h ψ)
  simp only [MState.tr', Complex.one_re, Matrix.trace_add, Matrix.trace_sum, Complex.add_re,
    Complex.re_sum, trace_vecMulVec_re] at ht
  rw [N.sum_branches ψ vecMass]
  linarith

theorem mass_eq (W : (eB × dB) → Matrix eB dB ℂ) (hW1 : ∑ k, (W k)ᴴ * W k = 1)
    (ψ : Ket (Fin 2 × dB)) :
    blockMass (N.blockA W ψ) = N.mx (MState.pure ψ).traceRight.m ∧
      blockMass (N.blockB W ψ) = N.my (MState.pure ψ).traceRight.m ∧
      blockMass (N.blockC W ψ) = N.mz (MState.pure ψ).traceRight.m ∧
      blockMass (N.blockD W ψ) = N.mw (MState.pure ψ).traceRight.m := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [blockA, blockB, blockC, blockD, blockMass_branchBlock W hW1, vecMass_branch, mx, my,
      mz, mw]

/-- **TC4 implies the pure-input inequality** for a normal-form qubit channel and any partner. -/
theorem pureInputBound_of_TC4 (hTC4 : TC4Bound) (h : N.Complete) [Nonempty dB]
    (Ω : CPTPMap dB eB) : PureInputBound (N.toCPTP h) Ω := by
  intro ψ
  obtain ⟨W, hW, hW1⟩ := exists_kraus_family Ω
  set ρA := (MState.pure ψ).traceRight with hρA
  obtain ⟨p, σ₁, σ₂, hp0, hp1, h₁, h₂, hmixA, hscalar⟩ := N.scalar_bound (matrix_isState ρA)
  have hmass := N.branches_mass h ψ
  let σF := Fintype.equivFin ((Unit ⊕ J) ⊕ (Unit ⊕ K))
  refine ⟨2, Fintype.card ((Unit ⊕ J) ⊕ (Unit ⊕ K)),
    pairEnsemble ⟨p, hp0, hp1⟩ (stateOf σ₁ h₁) (stateOf σ₂ h₂),
    Ensemble.congrMEnsemble σF (vecEnsemble (N.branches ψ) hmass), ?_, ?_, ?_⟩
  · apply MState.ext_m
    rw [pairEnsemble_mix_m, stateOf_m, stateOf_m]
    exact hmixA.symm
  · rw [Ensemble.mix_congrMEnsemble_eq_mix]
    apply MState.ext_m
    rw [vecEnsemble_mix_m, N.sum_branches ψ (fun η => vecMulVec η (star η)),
      N.traceLeft_pure_eq h ψ]
    abel
  · rw [avgOutputEntropy_reindex, avgOutputEntropy_pair, avgOutputEntropy_vecEnsemble,
      N.sum_branches ψ (fun η => vecMass η * Sᵥₙ (Ω (vecState η)))]
    have hΦ (σ : Matrix (Fin 2) (Fin 2) ℂ) (hσ : OpenAIEntropy.IsState σ) :
        Sᵥₙ (N.toCPTP h (stateOf σ hσ)) = OpenAIEntropy.entropy (N.act σ) := by
      rw [entropy_eq_openai, N.toCPTP_m, stateOf_m]
    rw [hΦ σ₁ h₁, hΦ σ₂ h₂]
    obtain ⟨hmA, hmB, hmC, hmD⟩ := N.mass_eq W hW1 ψ
    have hnorm : blockMass (N.blockA W ψ) + blockMass (N.blockB W ψ) +
        blockMass (N.blockC W ψ) + blockMass (N.blockD W ψ) = 1 := by
      rw [← hmass, N.sum_branches ψ vecMass]
      simp only [blockA, blockB, blockC, blockD, blockMass_branchBlock W hW1,
        Fintype.univ_punit, Finset.sum_singleton]
      ring
    have hT := hTC4 (N.blockA W ψ) (N.blockB W ψ) (N.blockC W ψ) (N.blockD W ψ) hnorm
    rw [hmA, hmB, hmC, hmD] at hT
    have hA := weightedBlockEntropy_branchBlock_ge Ω W hW (fun _ : Unit => branch N.a ψ)
    have hB := weightedBlockEntropy_branchBlock_ge Ω W hW (fun j => branch (N.b j) ψ)
    have hC := weightedBlockEntropy_branchBlock_ge Ω W hW (fun _ : Unit => branch N.c ψ)
    have hD := weightedBlockEntropy_branchBlock_ge Ω W hW (fun k => branch (N.d k) ψ)
    simp only [Fintype.univ_punit, Finset.sum_singleton] at hA hC
    have hjoint : Sᵥₙ ((N.toCPTP h ⊗ᶜᵖ Ω) (MState.pure ψ)) =
        OpenAIEntropy.entropy (N.tc4At W ψ * (N.tc4At W ψ).conjTranspose) := by
      rw [entropy_eq_openai, N.joint_output_m h Ω W hW ψ]
      exact entropy_submatrix_equiv _ (Matrix.isHermitian_mul_conjTranspose_self _)
    rw [hjoint]
    unfold tc4At
    simp only [blockA, blockB, blockC, blockD] at hT ⊢
    linarith

end QubitNormalForm

end QubitAdditivity
