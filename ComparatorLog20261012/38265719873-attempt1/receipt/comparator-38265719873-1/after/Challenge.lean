import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Logic.Equiv.Fin.Basic

namespace QubitHolevo

noncomputable section
open scoped ComplexOrder Kronecker
open Matrix

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

/-- Strong Holevo additivity: $\chi(\Phi \otimes \Omega) = \chi(\Phi) + \chi(\Omega)$ for every
qubit channel $\Phi$ and every channel $\Omega$ between systems of positive finite dimension. -/
theorem strong_additivity {r s n m : ℕ}
    (K : Fin r → Matrix (Fin 2) (Fin 2) ℂ) (hK : IsKraus K)
    (L : Fin s → Matrix (Fin (m + 1)) (Fin (n + 1)) ℂ) (hL : IsKraus L) :
    holevo (tensorKraus K L) = holevo K + holevo L := by
  sorry

/-- Additivity over independent uses: $\chi(\Phi^{\otimes n}) = n\,\chi(\Phi)$ for every qubit
channel $\Phi$. -/
theorem power_additivity {r : ℕ} (K : Fin r → Matrix (Fin 2) (Fin 2) ℂ) (hK : IsKraus K)
    (n : ℕ) : holevo (powerKraus K n) = n * holevo K := by
  sorry

end

end QubitHolevo
