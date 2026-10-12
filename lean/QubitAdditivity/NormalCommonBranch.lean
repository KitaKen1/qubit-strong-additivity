import QubitAdditivity.NormalSchur
import Mathlib.Analysis.Matrix.Order
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Filter Set
open scoped Matrix ComplexOrder MatrixOrder Topology

namespace QubitAdditivity.NormalCommonBranch
open NormalSchur

@[reducible] local instance matrixHMul {a b c : Type*} [Fintype b] :
    HMul (Matrix a b ℂ) (Matrix b c ℂ) (Matrix a c ℂ) :=
  Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- A PSD rank-one residual gives a uniform bound in the finite product norm. -/
theorem norm_bound_of_residual (P : Matrix n n ℂ) {t : ℝ} (ht : t ≤ 1)
    {u : n → ℂ} (h : (P+t • (1 : Matrix n n ℂ)-outerM u).PosSemidef) :
    ‖u‖ ≤ ‖fun i => P i i‖+1 := by
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ ‖fun i => P i i‖+1)).mpr
  intro i
  have hi := (Complex.nonneg_iff.mp (h.diag_nonneg (i := i))).1
  have he : (outerM u i i).re = ‖u i‖^2 := by
    simp only [outerM,Matrix.vecMulVec_apply,Pi.star_apply,Complex.star_def,
      Complex.mul_conj,Complex.ofReal_re,Complex.normSq_eq_norm_sq]
  have hdiag : ‖P i i‖ ≤ ‖fun i => P i i‖ :=
    norm_le_pi_norm (fun i => P i i) i
  have hre : (P i i).re ≤ ‖fun i => P i i‖ := (Complex.re_le_norm (P i i)).trans hdiag
  simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply_eq,
    Complex.real_smul,mul_one,Complex.sub_re,Complex.add_re,Complex.ofReal_re,he] at hi
  have hu := norm_nonneg (u i)
  have hp := norm_nonneg (fun i => P i i)
  nlinarith

/-- A positive scalar perturbation of a PSD matrix is positive definite. -/
theorem posDef_add_identity {P : Matrix n n ℂ} (hP : P.PosSemidef) {t : ℝ} (ht : 0 < t) :
    (P+t • (1 : Matrix n n ℂ)).PosDef := by
  have htI : (t • (1 : Matrix n n ℂ)).PosDef := Matrix.PosDef.one.smul (α := ℝ) ht
  exact Matrix.PosDef.posSemidef_add hP htI

theorem fromBlocks_add_identity (P : Matrix n n ℂ) (Q : Matrix m m ℂ)
    (A : Matrix n m ℂ) (B : Matrix m n ℂ) (t : ℝ) :
    Matrix.fromBlocks (P+t • 1) A B (Q+t • 1) =
      Matrix.fromBlocks P A B Q+t • (1 : Matrix (n ⊕ m) (n ⊕ m) ℂ) := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.fromBlocks,Matrix.one_apply]

/-- Common-branch extraction for singular diagonal blocks, by compactness. -/
theorem exists_common_branch {P : Matrix n n ℂ} {Q : Matrix m m ℂ}
    (a : n → ℂ) (c : m → ℂ)
    (hblock : (Matrix.fromBlocks P (Matrix.vecMulVec a (star c))
      (Matrix.vecMulVec c (star a)) Q).PosSemidef) :
    ∃ u : n → ℂ, ∃ v : m → ℂ,
      Matrix.vecMulVec v (star u) = Matrix.vecMulVec c (star a) ∧
      (P-outerM u).PosSemidef ∧ (Q-outerM v).PosSemidef := by
  have hP : P.PosSemidef := by
    convert hblock.submatrix Sum.inl using 1
    ext i j
    rfl
  have hQ : Q.PosSemidef := by
    convert hblock.submatrix Sum.inr using 1
    ext i j
    rfl
  by_cases ha : a = 0
  · subst a
    refine ⟨0,0,?_,?_,?_⟩
    · ext i j; simp [Matrix.vecMulVec_apply]
    · simpa [outerM] using hP
    · simpa [outerM] using hQ
  let e : ℕ → ℝ := fun j => 1/((j : ℝ)+1)
  have hepos : ∀ j, 0 < e j := fun j => by dsimp [e]; positivity
  have hele : ∀ j, e j ≤ 1 := fun j => by
    dsimp [e]
    rw [div_le_one (by positivity : (0 : ℝ) < (j : ℝ)+1)]
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have hex : ∀ j, ∃ u : n → ℂ, ∃ v : m → ℂ,
      Matrix.vecMulVec v (star u) = Matrix.vecMulVec c (star a) ∧
      (P+e j • 1-outerM u).PosSemidef ∧ (Q+e j • 1-outerM v).PosSemidef := by
    intro j
    apply exists_common_branch_of_posDef (posDef_add_identity hP (hepos j)) ha c
    rw [fromBlocks_add_identity]
    exact hblock.add (Matrix.PosSemidef.one.smul (α := ℝ) (hepos j).le)
  choose us vs hc hu hv using hex
  let w : ℕ → (n → ℂ) × (m → ℂ) := fun j => (us j,vs j)
  let R : ℝ := ‖fun i => P i i‖+‖fun i => Q i i‖+1
  have hbound : ∀ j, w j ∈ Metric.closedBall 0 R := by
    intro j
    rw [Metric.mem_closedBall,dist_zero_right]
    apply (max_le_iff).mpr
    constructor
    · exact (norm_bound_of_residual P (hele j) (hu j)).trans (by dsimp [R]; nlinarith [norm_nonneg (fun i => Q i i)])
    · exact (norm_bound_of_residual Q (hele j) (hv j)).trans (by dsimp [R]; nlinarith [norm_nonneg (fun i => P i i)])
  obtain ⟨z,_,f,hf,hz⟩ := (isCompact_closedBall (0 : (n → ℂ) × (m → ℂ)) R).tendsto_subseq hbound
  have he0 : Tendsto (e ∘ f) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hf.tendsto_atTop
  have huz : Tendsto (us ∘ f) atTop (𝓝 z.1) := by
    simpa [w,Function.comp_def] using hz.fst_nhds
  have hvz : Tendsto (vs ∘ f) atTop (𝓝 z.2) := by
    simpa [w,Function.comp_def] using hz.snd_nhds
  have hccont : Continuous (fun z : (n → ℂ) × (m → ℂ) => Matrix.vecMulVec z.2 (star z.1)) := by
    fun_prop
  have hcZ : Matrix.vecMulVec z.2 (star z.1) = Matrix.vecMulVec c (star a) := by
    have hlim := hccont.continuousAt.tendsto.comp hz
    have hconst : (fun j => Matrix.vecMulVec (vs (f j)) (star (us (f j)))) =
        (fun _ : ℕ => Matrix.vecMulVec c (star a)) := by funext j; exact hc (f j)
    change Tendsto (fun j => Matrix.vecMulVec (vs (f j)) (star (us (f j)))) atTop
      (𝓝 (Matrix.vecMulVec z.2 (star z.1))) at hlim
    rw [hconst] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  refine ⟨z.1,z.2,hcZ,?_,?_⟩
  · have hcR : Continuous (fun p : ℝ × (n → ℂ) => P+p.1 • 1-outerM p.2) := by
      unfold outerM
      fun_prop
    have hlim := hcR.continuousAt.tendsto.comp (he0.prodMk_nhds huz)
    have hres := Matrix.posSemidef_is_closed.mem_of_tendsto hlim
      (Eventually.of_forall (fun j => hu (f j)))
    simpa using hres
  · have hcR : Continuous (fun p : ℝ × (m → ℂ) => Q+p.1 • 1-outerM p.2) := by
      unfold outerM
      fun_prop
    have hlim := hcR.continuousAt.tendsto.comp (he0.prodMk_nhds hvz)
    have hres := Matrix.posSemidef_is_closed.mem_of_tendsto hlim
      (Eventually.of_forall (fun j => hv (f j)))
    simpa using hres

end QubitAdditivity.NormalCommonBranch
