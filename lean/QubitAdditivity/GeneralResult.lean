import QubitAdditivity.RotationInvariant
import QubitAdditivity.TC4Result

set_option autoImplicit false
noncomputable section
open scoped MatrixMap

namespace QubitAdditivity.GeneralResult
open NormalChannel RotationInvariant

variable {dB eB : Type} [Fintype dB] [DecidableEq dB]
  [Fintype eB] [DecidableEq eB] [Nonempty dB]

/-- Strong Holevo additivity for every qubit channel and every finite partner. -/
theorem strongHolevoAdditivity (Phi : CPTPMap (Fin 2) (Fin 2)) (Omega : CPTPMap dB eB) :
    holevo (Phi ⊗ᶜᵖ Omega) = holevo Phi+holevo Omega := by
  obtain ⟨U,N,h,hEq⟩ := exists_normal_channel Phi
  have hN := N.strongHolevoAdditivity h Omega
  rw [hEq,holevo_prod_output_unitary,holevo_output_unitary] at hN
  exact hN

/-- The exact frozen original target, with no extra premises. -/
theorem generalQubitStrongAdditivity : GeneralQubitStrongAdditivity := by
  intro Phi n m Omega
  exact strongHolevoAdditivity Phi Omega

/-- The exact frozen upper-bound target is also supplied. -/
theorem generalQubitUpperBound : GeneralQubitUpperBound :=
  strongAdditivity_iff_upperBound.mp generalQubitStrongAdditivity

end QubitAdditivity.GeneralResult
