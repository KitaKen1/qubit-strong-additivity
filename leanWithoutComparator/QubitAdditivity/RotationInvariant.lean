import QubitAdditivity.NormalChannel

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix
open scoped Matrix ComplexOrder MatrixOrder MatrixMap Kronecker

namespace QubitAdditivity.RotationInvariant

@[reducible] local instance matrixHMul {a b c : Type*} [Fintype b] :
    HMul (Matrix a b ℂ) (Matrix b c ℂ) (Matrix a c ℂ) :=
  Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {d e f g h : Type*}
  [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
  [Fintype f] [DecidableEq f] [Fintype g] [DecidableEq g]
  [Fintype h] [DecidableEq h]

theorem entropy_output_unitary (U : Matrix.unitaryGroup e ℂ) (rho : MState e) :
    Sᵥₙ (CPTPMap.ofUnitary U rho) = Sᵥₙ rho := by
  rw [entropy_eq_openai,entropy_eq_openai,CPTPMap.mat_coe_eq_apply_mat]
  change OpenAIEntropy.entropy ((U : Matrix e e ℂ)*rho.m*(U : Matrix e e ℂ)ᴴ) =
    OpenAIEntropy.entropy rho.m
  simpa only [Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose] using
    OpenAIEntropy.entropy_unitary_conj U rho.psd.isHermitian

theorem holevoValue_output_unitary (U : Matrix.unitaryGroup e ℂ) (Phi : CPTPMap d e)
    {a : Type*} [Fintype a] (E : MEnsemble d a) :
    holevoValue (CPTPMap.ofUnitary U ∘ₘ Phi) E = holevoValue Phi E := by
  unfold holevoValue
  simp only [CPTPMap.compose_eq,entropy_output_unitary]

theorem holevo_output_unitary (U : Matrix.unitaryGroup e ℂ) (Phi : CPTPMap d e) :
    holevo (CPTPMap.ofUnitary U ∘ₘ Phi) = holevo Phi := by
  unfold holevo holevoValues
  congr 1
  ext v
  simp only [holevoValue_output_unitary]

theorem prod_compose {r : Type*} [Fintype r] [DecidableEq r]
    (P : CPTPMap e h) (Phi : CPTPMap d e) (Q : CPTPMap g r) (Omega : CPTPMap f g) :
    (P ∘ₘ Phi) ⊗ᶜᵖ (Q ∘ₘ Omega) = (P ⊗ᶜᵖ Q) ∘ₘ (Phi ⊗ᶜᵖ Omega) := by
  apply CPTPMap.ext
  exact MatrixMap.kron_comp_distrib Phi.map P.map Omega.map Q.map

theorem unitary_prod (U : Matrix.unitaryGroup e ℂ) (V : Matrix.unitaryGroup g ℂ) :
    CPTPMap.ofUnitary U ⊗ᶜᵖ CPTPMap.ofUnitary V = CPTPMap.ofUnitary (Matrix.unitary_kron U V) := by
  apply CPTPMap.ext
  exact MatrixMap.conj_kron (U : Matrix e e ℂ) (V : Matrix g g ℂ)

theorem unitary_one : CPTPMap.ofUnitary (1 : Matrix.unitaryGroup g ℂ) = CPTPMap.id := by
  apply CPTPMap.ext
  change MatrixMap.conj (1 : Matrix g g ℂ) = LinearMap.id
  exact MatrixMap.congruence_one_eq_id

theorem prod_output_unitary (U : Matrix.unitaryGroup e ℂ) (Phi : CPTPMap d e)
    (Omega : CPTPMap f g) :
    (CPTPMap.ofUnitary U ∘ₘ Phi) ⊗ᶜᵖ Omega =
      CPTPMap.ofUnitary (Matrix.unitary_kron U (1 : Matrix.unitaryGroup g ℂ)) ∘ₘ (Phi ⊗ᶜᵖ Omega) := by
  calc
    _ = (CPTPMap.ofUnitary U ∘ₘ Phi) ⊗ᶜᵖ
        (CPTPMap.ofUnitary (1 : Matrix.unitaryGroup g ℂ) ∘ₘ Omega) := by
      rw [unitary_one,CPTPMap.id_compose]
    _ = (CPTPMap.ofUnitary U ⊗ᶜᵖ CPTPMap.ofUnitary (1 : Matrix.unitaryGroup g ℂ)) ∘ₘ
        (Phi ⊗ᶜᵖ Omega) := prod_compose _ _ _ _
    _ = _ := by rw [unitary_prod]

theorem holevo_prod_output_unitary (U : Matrix.unitaryGroup e ℂ) (Phi : CPTPMap d e)
    (Omega : CPTPMap f g) :
    holevo ((CPTPMap.ofUnitary U ∘ₘ Phi) ⊗ᶜᵖ Omega) = holevo (Phi ⊗ᶜᵖ Omega) := by
  rw [prod_output_unitary,holevo_output_unitary]

end QubitAdditivity.RotationInvariant
