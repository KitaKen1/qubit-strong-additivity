import QubitAdditivity.Holevo

namespace QubitAdditivity

/-- The exact proposed conjecture. This is a proposition, not a proved theorem. -/
def GeneralQubitStrongAdditivity : Prop :=
  ∀ (Φ : CPTPMap (Fin 2) (Fin 2)) (n m : ℕ),
    ∀ Ω : CPTPMap (Fin (n + 1)) (Fin (m + 1)),
      holevo (Φ ⊗ᶜᵖ Ω) = holevo Φ + holevo Ω

/-- The remaining upper bound has precisely the same channel scope as the target. -/
def GeneralQubitUpperBound : Prop :=
  ∀ (Φ : CPTPMap (Fin 2) (Fin 2)) (n m : ℕ),
    ∀ Ω : CPTPMap (Fin (n + 1)) (Fin (m + 1)),
      holevo (Φ ⊗ᶜᵖ Ω) ≤ holevo Φ + holevo Ω

/-- The lower bound leaves only the upper bound to prove. No upper bound is assumed globally. -/
theorem strongAdditivity_iff_upperBound :
    GeneralQubitStrongAdditivity ↔ GeneralQubitUpperBound := by
  constructor
  · intro h Φ n m Ω
    exact (h Φ n m Ω).le
  · intro h Φ n m Ω
    exact le_antisymm (h Φ n m Ω) (holevo_product_ge Φ Ω)

end QubitAdditivity
