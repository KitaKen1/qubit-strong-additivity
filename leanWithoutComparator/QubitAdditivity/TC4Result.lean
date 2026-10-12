import QubitAdditivity.BetaTC4Boundary
import QubitAdditivity.PureInput

set_option autoImplicit false
noncomputable section
open scoped Matrix Kronecker MatrixMap

namespace QubitAdditivity.QubitNormalForm

variable {J K : Type} [Fintype J] [Fintype K] (N : QubitNormalForm J K)
variable {dB eB : Type} [Fintype dB] [DecidableEq dB] [Fintype eB] [DecidableEq eB]

/-- The pure-input inequality now uses the proved TC4Bound. -/
theorem pureInputBound (h : N.Complete) [Nonempty dB]
    (Ω : CPTPMap dB eB) : PureInputBound (N.toCPTP h) Ω :=
  N.pureInputBound_of_TC4 BetaTC4Boundary.tc4Bound h Ω

/-- Strong Holevo additivity for every complete normal form and every finite partner. -/
theorem strongHolevoAdditivity (h : N.Complete) [Nonempty dB]
    (Ω : CPTPMap dB eB) :
    holevo (N.toCPTP h ⊗ᶜᵖ Ω) = holevo (N.toCPTP h)+holevo Ω :=
  holevo_prod_eq_of_pureInputBound _ _ (N.pureInputBound h Ω)

end QubitAdditivity.QubitNormalForm
