import QubitAdditivity.NormalKraus

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix
open scoped Matrix ComplexOrder MatrixOrder MatrixMap

namespace QubitAdditivity.NormalChannel
open NormalSchur NormalKraus QubitNormalForm

@[reducible] local instance matrixHMul {a b c : Type*} [Fintype b] :
    HMul (Matrix a b ℂ) (Matrix b c ℂ) (Matrix a c ℂ) :=
  Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k]

theorem bform_trace_outer (rho : Matrix n n ℂ) (p q : n → ℂ) :
    bform rho p q = (rho*Matrix.vecMulVec q (star p)).trace := by
  simp only [bform,Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,Matrix.vecMulVec_apply,
    Matrix.mulVec,dotProduct,Pi.star_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

variable (p q : k → Fin 2 → ℂ)

theorem sum_bform_trace (rho : Matrix (Fin 2) (Fin 2) ℂ) :
    (∑ j,bform rho (p j) (q j)) = (rho*crossMat p q).trace := by
  simp_rw [bform_trace_outer]
  rw [crossMat,Matrix.mul_sum,Matrix.trace_sum]

theorem rows_adjoint_rows (p q : Fin 2 → ℂ) :
    (rows p q)ᴴ*rows p q = outerM p+outerM q := by
  ext i j
  simp only [Matrix.mul_apply,Fin.sum_univ_two,Matrix.conjTranspose_apply,
    rows_zero,rows_one,star_star,Matrix.add_apply,outerM,Matrix.vecMulVec_apply,Pi.star_apply]

theorem rows_family_complete_iff :
    (∑ j,(rows (p j) (q j))ᴴ*rows (p j) (q j)) = 1 ↔ massMat p+massMat q = 1 := by
  simp only [rows_adjoint_rows,Finset.sum_add_distrib,massMat,outerM]

def gramAct (P Q E : Matrix (Fin 2) (Fin 2) ℂ) (rho : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![(rho*P).trace,(rho*E).trace;(rho*Eᴴ).trace,(rho*Q).trace]

theorem rows_family_action (rho : Matrix (Fin 2) (Fin 2) ℂ) :
    MatrixMap.of_kraus (fun j => rows (p j) (q j)) (fun j => rows (p j) (q j)) rho =
      !![∑ j,bform rho (p j) (p j),∑ j,bform rho (p j) (q j);
         ∑ j,bform rho (q j) (p j),∑ j,bform rho (q j) (q j)] := by
  simp only [MatrixMap.of_kraus,LinearMap.coe_sum,Finset.sum_apply,LinearMap.coe_mk,
    AddHom.coe_mk,rows_conj]
  ext i l
  fin_cases i <;> fin_cases l <;> simp [Matrix.sum_apply]

theorem rows_family_action_gram (rho : Matrix (Fin 2) (Fin 2) ℂ) :
    MatrixMap.of_kraus (fun j => rows (p j) (q j)) (fun j => rows (p j) (q j)) rho =
      gramAct (massMat p) (massMat q) (crossMat p q) rho := by
  rw [rows_family_action,gramAct,crossMat_conjTranspose]
  simp only [sum_bform_trace,crossMat,massMat]

variable {J L : Type*} [Fintype J] [Fintype L]

theorem normal_kraus_sum (N : QubitNormalForm J L) :
    (∑ j,(N.kraus j)ᴴ*N.kraus j) =
      outerM N.a+∑ j,outerM (N.b j)+outerM N.c+∑ j,outerM (N.d j) := by
  simp only [Fintype.sum_sum_type,Fintype.univ_punit,Finset.sum_singleton,kraus,
    rows_adjoint_rows,Finset.sum_add_distrib]
  simp only [outerM,star_zero,Matrix.vecMulVec_zero,Matrix.zero_vecMulVec,
    add_zero,zero_add,Finset.sum_const_zero]
  abel

theorem normal_action_gram (N : QubitNormalForm J L) (rho : Matrix (Fin 2) (Fin 2) ℂ) :
    N.act rho = gramAct (outerM N.a+massMat N.b) (outerM N.c+massMat N.d)
      (Matrix.vecMulVec N.c (star N.a)) rho := by
  rw [act,gramAct]
  simp only [Matrix.mul_add,Matrix.trace_add,Matrix.conjTranspose_vecMulVec,star_star,
    bform_trace_outer,sum_bform_trace,crossMat,massMat,outerM,Matrix.mul_sum,Matrix.trace_sum]

theorem complete_of_gram (N : QubitNormalForm J L)
    (hP : massMat p = outerM N.a+massMat N.b)
    (hQ : massMat q = outerM N.c+massMat N.d)
    (hTP : (∑ j,(rows (p j) (q j))ᴴ*rows (p j) (q j)) = 1) : N.Complete := by
  have h := (rows_family_complete_iff p q).mp hTP
  rw [hP,hQ] at h
  unfold Complete
  rw [normal_kraus_sum]
  simpa only [massMat,outerM,add_assoc] using h

theorem action_eq_of_gram (N : QubitNormalForm J L)
    (hP : massMat p = outerM N.a+massMat N.b)
    (hQ : massMat q = outerM N.c+massMat N.d)
    (hE : crossMat p q = Matrix.vecMulVec N.c (star N.a))
    (rho : Matrix (Fin 2) (Fin 2) ℂ) :
    MatrixMap.of_kraus (fun j => rows (p j) (q j)) (fun j => rows (p j) (q j)) rho = N.act rho := by
  rw [rows_family_action_gram,hP,hQ,hE,normal_action_gram]

theorem unitary_kraus_complete (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (W : k → Matrix (Fin 2) (Fin 2) ℂ) (hTP : (∑ j,(W j)ᴴ*W j) = 1) :
    (∑ j,((U : Matrix (Fin 2) (Fin 2) ℂ)*W j)ᴴ*((U : Matrix (Fin 2) (Fin 2) ℂ)*W j)) = 1 := by
  have hU : (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ*(U : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using U.property.1
  calc
    _ = ∑ j,(W j)ᴴ*W j := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
        (U : Matrix (Fin 2) (Fin 2) ℂ) (W j),hU,Matrix.one_mul]
    _ = 1 := hTP

theorem unitary_kraus_action (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (W : k → Matrix (Fin 2) (Fin 2) ℂ) (rho : Matrix (Fin 2) (Fin 2) ℂ) :
    MatrixMap.of_kraus (fun j => (U : Matrix (Fin 2) (Fin 2) ℂ)*W j)
      (fun j => (U : Matrix (Fin 2) (Fin 2) ℂ)*W j) rho =
    (U : Matrix (Fin 2) (Fin 2) ℂ)*MatrixMap.of_kraus W W rho*(U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ := by
  simp only [MatrixMap.of_kraus,LinearMap.coe_sum,Finset.sum_apply,LinearMap.coe_mk,AddHom.coe_mk]
  rw [Matrix.mul_sum,Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]

/-- Every qubit CPTP map is a complete normal form after a unitary output rotation. -/
theorem exists_normal_channel (Phi : CPTPMap (Fin 2) (Fin 2)) :
    ∃ U : Matrix.unitaryGroup (Fin 2) ℂ, ∃ N : QubitNormalForm (Fin 2) (Fin 2),
      ∃ h : N.Complete, N.toCPTP h = CPTPMap.ofUnitary U ∘ₘ Phi := by
  obtain ⟨W,hW,hTP⟩ := exists_kraus_family Phi
  let p : (Fin 2 × Fin 2) → Fin 2 → ℂ := fun j i => star (W j 0 i)
  let q : (Fin 2 × Fin 2) → Fin 2 → ℂ := fun j i => star (W j 1 i)
  have hrows : ∀ j,W j = rows (p j) (q j) := by
    intro j
    ext i l
    fin_cases i <;> simp [rows_zero,rows_one,p,q]
  obtain ⟨s,t,N,hst,hP,hQ,hE⟩ := exists_rotated_normal_gram p q
  let U : Matrix.unitaryGroup (Fin 2) ℂ := ⟨rotU s t,rotU_mem_unitary hst⟩
  let pr := fun j => star s • p j+star t • q j
  let qr := fun j => -t • p j+s • q j
  have hrot : ∀ j,(U : Matrix (Fin 2) (Fin 2) ℂ)*W j = rows (pr j) (qr j) := by
    intro j
    rw [hrows j]
    exact rotU_mul_rows s t (p j) (q j)
  have hrTP : (∑ j,(rows (pr j) (qr j))ᴴ*rows (pr j) (qr j)) = 1 := by
    simpa only [hrot] using unitary_kraus_complete U W hTP
  have hN : N.Complete := complete_of_gram pr qr N hP hQ hrTP
  refine ⟨U,N,hN,?_⟩
  apply CPTPMap.ext
  apply LinearMap.ext
  intro rho
  change MatrixMap.of_kraus N.kraus N.kraus rho =
    (U : Matrix (Fin 2) (Fin 2) ℂ)*Phi.map rho*(U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ
  rw [act_eq_of_kraus,← action_eq_of_gram pr qr N hP hQ hE,hW]
  simpa only [hrot] using unitary_kraus_action U W rho

end QubitAdditivity.NormalChannel
