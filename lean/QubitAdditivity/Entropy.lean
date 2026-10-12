import QuantumInfo.Entropy.VonNeumann
import QubitAdditivity.Imported.TensorEntropy

/-! Bridge the bundled states of Physlib to OpenAI's matrix entropy.
All entropies in this project use the natural logarithm. -/

noncomputable section

namespace QubitAdditivity

variable {d e : Type*} [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]

theorem matrix_isState (ρ : MState d) : OpenAIEntropy.IsState ρ.m := by
  refine ⟨ρ.psd, ?_⟩
  have h := HermitianMat.trace_eq_trace_rc ρ.M
  simpa using h.symm

theorem entropy_eq_openai (ρ : MState d) : Sᵥₙ ρ = OpenAIEntropy.entropy ρ.m := by
  rw [Sᵥₙ_eq_trace_cfc_negMulLog, HermitianMat.trace_eq_re_trace,
    HermitianMat.mat_cfc]
  rfl

/-- Entropy additivity for arbitrary finite-dimensional product states. -/
theorem entropy_prod (ρ : MState d) (σ : MState e) :
    Sᵥₙ (ρ ⊗ᴹ σ) = Sᵥₙ ρ + Sᵥₙ σ := by
  rw [entropy_eq_openai, entropy_eq_openai, entropy_eq_openai]
  exact OpenAIEntropy.entropy_kronecker_state (matrix_isState ρ) (matrix_isState σ)

end QubitAdditivity
