import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Strong Holevo additivity for qubit channels: a Mathlib-only statement vocabulary

Self-contained definitions for the statement `χ(Φ ⊗ Ω) = χ(Φ) + χ(Ω)`, where `Φ` is an
arbitrary qubit channel and `Ω` an arbitrary channel between finite-dimensional systems.
Channels are given by finite Kraus families. Nothing here depends on Physlib or on the proof.

The definitions `entropy` and `IsState` and the shape of `Ensemble` follow `OAI.GAD` in
openai/math, commit fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0; see
vendor/openai/LICENSE), generalized from the amplitude-damping Kraus operators to arbitrary
Kraus families. Entropies use the natural logarithm.

The block between the two markers is the whole statement vocabulary. It is repeated verbatim in
`ComparatorChallenges/QubitHolevoAdditivity.lean`; `scripts/verify.py` checks the two copies.
The definitions after the block are not part of the statement: they name the ensembles and
ensemble values inside `holevo` for the proof in `FCPresentation.lean`.
-/

namespace QubitHolevo

noncomputable section
open scoped ComplexOrder Kronecker
open Matrix

-- BEGIN MODEL
/-- The von Neumann entropy $S(P) = -\operatorname{Tr}(P \log P)$, with the natural logarithm. -/
def entropy {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℂ) : ℝ :=
  (cfc Real.negMulLog P).trace.re

/-- A finite family $(K_i)$ of matrices is a channel in Kraus form when
$\sum_i K_i^* K_i = 1$. -/
def IsKraus {ι κ ρ : Type*} [Fintype ι] [DecidableEq κ] [Fintype ρ]
    (K : ρ → Matrix ι κ ℂ) : Prop :=
  ∑ i, (K i)ᴴ * K i = 1

/-- The Holevo information $\chi(\Phi)$ of the channel $\Phi(P) = \sum_i K_i P K_i^*$: the
supremum of $S(\Phi(\sum_a p_a \sigma_a)) - \sum_a p_a S(\Phi(\sigma_a))$ over all finite
ensembles of density matrices $\sigma_a$ with probabilities $p_a$. -/
def holevo {ι κ ρ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype ρ]
    (K : ρ → Matrix ι κ ℂ) : ℝ :=
  let Φ (P : Matrix κ κ ℂ) : Matrix ι ι ℂ := ∑ i, K i * P * (K i)ᴴ
  sSup {x | ∃ (n : ℕ) (p : Fin n → ℝ) (σ : Fin n → Matrix κ κ ℂ),
    (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1 ∧ (∀ a, (σ a).PosSemidef ∧ (σ a).trace = 1) ∧
    x = entropy (Φ (∑ a, p a • σ a)) - ∑ a, p a * entropy (Φ (σ a))}

/-- The Kraus family $(K_i \otimes L_j)$ of the tensor product of two channels. -/
def tensorKraus {ι κ ρ ι' κ' ρ' : Type*} (K : ρ → Matrix ι κ ℂ) (L : ρ' → Matrix ι' κ' ℂ) :
    ρ × ρ' → Matrix (ι × ι') (κ × κ') ℂ :=
  fun i ↦ K i.1 ⊗ₖ L i.2

/-- The Kraus family $(K_{i_1} \otimes \dots \otimes K_{i_n})$ of $n$ independent uses of a
channel. -/
def powerKraus {ι κ ρ : Type*} (K : ρ → Matrix ι κ ℂ) (n : ℕ) :
    (Fin n → ρ) → Matrix (Fin n → ι) (Fin n → κ) ℂ :=
  fun i a b ↦ ∏ k, K (i k) (a k) (b k)
-- END MODEL

universe u v w

/-- Density matrices: positive semidefinite with unit trace. -/
def IsState {ι : Type u} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℂ) : Prop :=
  P.PosSemidef ∧ Matrix.trace P = 1

/-- The channel of a Kraus family: `P ↦ ∑ r, K r * P * (K r)ᴴ`. -/
def applyKraus {ι : Type u} {κ : Type v} {ρ : Type w} [Fintype κ] [Fintype ρ]
    (K : ρ → Matrix ι κ ℂ) (P : Matrix κ κ ℂ) : Matrix ι ι ℂ :=
  ∑ r, K r * P * (K r).conjTranspose

/-- All finite ensembles of input states, without any product or purity restriction. -/
structure Ensemble (κ : Type v) [Fintype κ] [DecidableEq κ] where
  size : ℕ
  weight : Fin size → ℝ
  weight_nonneg : ∀ a, 0 ≤ weight a
  weight_sum : ∑ a, weight a = 1
  signal : Fin size → Matrix κ κ ℂ
  signal_state : ∀ a, IsState (signal a)

/-- The Holevo quantity `S(Φ(∑ₐ pₐ ρₐ)) - ∑ₐ pₐ S(Φ(ρₐ))` of an input ensemble, in nats: an
element of the set whose supremum is `holevo`. -/
def ensembleValue {ι : Type u} {κ : Type v} {ρ : Type w} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [Fintype ρ] (K : ρ → Matrix ι κ ℂ) (E : Ensemble κ) : ℝ :=
  entropy (applyKraus K (∑ a, E.weight a • E.signal a)) -
    ∑ a, E.weight a * entropy (applyKraus K (E.signal a))

end

end QubitHolevo
