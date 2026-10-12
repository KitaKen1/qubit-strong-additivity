import QubitAdditivity.BetaComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology

namespace QubitAdditivity.BetaBarrier
open BetaComparison
variable {n : Type*} [Fintype n] [DecidableEq n]

def weight (epsilon t : ℝ) := Real.exp (epsilon*t*(1-t))

theorem hasDerivAt_weight (epsilon t : ℝ) :
    HasDerivAt (weight epsilon) (epsilon*(1-2*t)*weight epsilon t) t := by
  have hh := (((hasDerivAt_const t epsilon).mul (hasDerivAt_id t)).mul
    ((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t))).exp
  convert hh using 1
  · rfl
  · dsimp [weight]
    ring

/-- Comparison with a commuting exponential family is all that PW needs.
The strict barrier removes the comparison premise; epsilon then tends to zero. -/
theorem le_of_exponential
    (F F₁ F₂ Q : ℝ → Matrix n n ℂ) (K : Matrix n n ℂ)
    (hF : ∀ u, HasDerivAt F (F₁ u) u) (hF₁ : ∀ u, HasDerivAt F₁ (F₂ u) u)
    (hQ : ∀ u, HasDerivAt Q (K * Q u) u)
    (hFH : ∀ u ∈ Set.Icc (0 : ℝ) 1, (F u).IsHermitian)
    (hQP : ∀ u, (Q u).PosDef) (hK : K.IsHermitian)
    (hKQ : ∀ u, K * Q u = Q u * K)
    (hGram : ∀ u ∈ Set.Ioo (0 : ℝ) 1,
      (Matrix.fromBlocks (F u) (F₁ u) (F₁ u) (F₂ u)).PosSemidef)
    (hzero : F 0 ≤ Q 0) (hone : F 1 ≤ Q 1) :
    ∀ u ∈ Set.Icc (0 : ℝ) 1, F u ≤ Q u := by
  have heps (epsilon : ℝ) (hepsilon : 0 < epsilon) :
      ∀ u ∈ Set.Icc (0 : ℝ) 1, F u ≤ weight epsilon u • Q u := by
    let B : ℝ → Matrix n n ℂ := fun u => weight epsilon u • Q u
    let C : ℝ → Matrix n n ℂ := fun u => (epsilon*(1-2*u)) • 1 + K
    let B₁ : ℝ → Matrix n n ℂ := fun u => C u * B u
    let B₂ : ℝ → Matrix n n ℂ := fun u => C u * C u * B u - (2*epsilon) • B u
    have hB (u : ℝ) : HasDerivAt B (B₁ u) u := by
      have hh := (hasDerivAt_weight epsilon u).smul (hQ u)
      convert hh using 1
      · rfl
      · simp only [B₁, C, B, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul,
          Matrix.one_mul, smul_smul]
        module
    have hC (u : ℝ) : HasDerivAt C ((-(2*epsilon)) • 1) u := by
      have hh := (((hasDerivAt_const u (1:ℝ)).sub ((hasDerivAt_id u).const_mul 2)).const_mul epsilon).smul_const
        (1 : Matrix n n ℂ) |>.add_const K
      convert! hh using 1 <;> congr 1 <;> ring
    have hB₁ (u : ℝ) : HasDerivAt B₁ (B₂ u) u := by
      have hh := OpenAICalculus.hasDerivAt_matrix_mul (hC u) (hB u)
      convert! hh using 1 <;>
        simp only [B₂, B₁, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc]
      all_goals module
    have hCP (u : ℝ) : (C u).IsHermitian :=
      (Matrix.isHermitian_one.smul (by rfl : IsSelfAdjoint (epsilon*(1-2*u)))).add hK
    have hCQ (u : ℝ) : C u * B u = B u * C u := by
      simp only [C, B, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul, hKQ u]
      module
    apply le_of_strict_barrier F F₁ F₂ B B₁ B₂ C (2*epsilon) (by positivity)
      hF hF₁ hB hB₁ hFH (fun u _ => (hQP u).smul (Real.exp_pos _))
      hCP hCQ (fun _ => rfl) (fun _ => rfl) hGram
    · simpa [B, weight] using hzero
    · simpa [B, weight] using hone
  intro u hu
  letI : OrderClosedTopology (Matrix n n ℂ) := Matrix.instOrderClosedTopology
  have hlim : Filter.Tendsto (fun epsilon : ℝ => weight epsilon u • Q u)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (Q u)) := by
    have hh : Continuous (fun epsilon : ℝ => weight epsilon u • Q u) := by
      dsimp [weight]
      fun_prop
    simpa [weight] using (hh.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (Filter.eventually_of_mem self_mem_nhdsWithin
    (fun epsilon hepsilon => heps epsilon hepsilon u hu))

end QubitAdditivity.BetaBarrier
