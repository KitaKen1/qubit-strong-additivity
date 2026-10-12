import QubitAdditivity.BetaPowers

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix
open scoped Matrix Kronecker ComplexOrder MatrixOrder Matrix.Norms.Elementwise

/-! Actual PW curves, their stationary Gram, and integration to KM.

The stationarity and strict residual positivity hypotheses are explicit.
The matrix-curve comparison theorem that supplies PW is not asserted here.
All powers and logarithms below are the spectral CFC from BetaPowers. -/

namespace QubitAdditivity.BetaBridge
open BetaOperators BetaPowers

local instance matrixNormedAddCommGroup {i j : Type*} [Fintype i] [Fintype j] :
    NormedAddCommGroup (Matrix i j ℂ) :=
  inferInstanceAs (NormedAddCommGroup (i → j → ℂ))

local instance matrixNormedSpace {i j : Type*} [Fintype i] [Fintype j] :
    NormedSpace ℝ (Matrix i j ℂ) :=
  inferInstanceAs (NormedSpace ℝ (i → j → ℂ))

local instance matrixENormedAddMonoid {i j : Type*} [Fintype i] [Fintype j] :
    ENormedAddMonoid (Matrix i j ℂ) :=
  inferInstanceAs (ENormedAddMonoid (i → j → ℂ))

local instance matrixClosedIciTopology {i : Type*} : ClosedIciTopology (Matrix i i ℂ) where
  isClosed_Ici a := by
    letI : OrderClosedTopology (Matrix i i ℂ) := Matrix.instOrderClosedTopology
    exact isClosed_le continuous_const continuous_id

local instance matrixNormClosedIciTopology {i : Type*} [Fintype i] :
    @ClosedIciTopology (Matrix i i ℂ)
      (matrixNormedAddCommGroup (i := i) (j := i)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (Matrix.instPartialOrder (𝕜 := ℂ) (n := i)).toPreorder := by
  convert! (matrixClosedIciTopology (i := i)) using 1

local instance matrixPairENormedAddMonoid {i j : Type*} [Fintype i] [Fintype j] :
    ENormedAddMonoid (Matrix i i ℂ × Matrix j j ℂ) := by
  convert! (NormedAddGroup.toENormedAddMonoid (F := Matrix i i ℂ × Matrix j j ℂ)) using 1

section compression
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def compressionLM (V : Matrix n m ℂ) : Matrix n n ℂ →ₗ[ℝ] Matrix m m ℂ where
  toFun X := Vᴴ * X * V
  map_add' X Y := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

def compressionCLM (V : Matrix n m ℂ) : Matrix n n ℂ →L[ℝ] Matrix m m ℂ :=
  (compressionLM V).toContinuousLinearMap

@[simp] theorem compressionCLM_apply (V : Matrix n m ℂ) (X : Matrix n n ℂ) :
    compressionCLM V X = Vᴴ * X * V := rfl

theorem isometry_mulVec_injective {V : Matrix n m ℂ} (hV : Vᴴ * V = 1) :
    Function.Injective V.mulVec := by
  intro x y h
  have hh := congrArg (fun z => Vᴴ *ᵥ z) h
  simpa only [Matrix.mulVec_mulVec, hV, Matrix.one_mulVec] using hh

theorem compression_posDef {V : Matrix n m ℂ} {D : Matrix n n ℂ}
    (hV : Vᴴ * V = 1) (hD : D.PosDef) : (Vᴴ * D * V).PosDef :=
  hD.conjTranspose_mul_mul_same (isometry_mulVec_injective hV)

/-- Coordinate compression differentiates entry by entry in the fixed matrix topology. -/
theorem hasDerivAt_coordinateCompression {A : ℝ → Matrix n n ℂ}
    {H : Matrix n n ℂ} {t : ℝ} (e : m ↪ n) (hA : HasDerivAt A H t) :
    HasDerivAt (fun u => (coordinateInclusion e)ᴴ * A u * coordinateInclusion e)
      ((coordinateInclusion e)ᴴ * H * coordinateInclusion e) t := by
  simp only [coordinateInclusion_compression]
  apply hasDerivAt_pi.2
  intro i
  apply hasDerivAt_pi.2
  intro j
  exact hasDerivAt_pi.1 (hasDerivAt_pi.1 hA (e i)) (e j)

/-- Integration preserves the Loewner order, using the entrywise matrix topology. -/
theorem intervalIntegral_mono_on {f g : ℝ → Matrix n n ℂ}
    (hf : IntervalIntegrable f MeasureTheory.volume 0 1)
    (hg : IntervalIntegrable g MeasureTheory.volume 0 1)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t ≤ g t) :
    (∫ t in (0 : ℝ)..1, f t) ≤ ∫ t in (0 : ℝ)..1, g t := by
  rw [intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_of_le zero_le_one]
  apply MeasureTheory.integral_mono_ae hf.1 hg.1
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc
    (fun t ht => h t ⟨ht.1.le, ht.2⟩)

theorem km_posSemidef {A : Matrix n n ℂ} (hA : A.PosDef) : (km A).PosSemidef := by
  apply Matrix.LE.le.posSemidef
  rw [km, intervalIntegral.integral_of_le zero_le_one]
  exact MeasureTheory.integral_nonneg (fun t => (pw_posDef hA t).posSemidef.nonneg)

theorem km_mono {A B : Matrix n n ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (hAB : A ≤ B) : km A ≤ km B :=
  intervalIntegral_mono_on (intervalIntegrable_pw hA) (intervalIntegrable_pw hB)
    (fun _ ht => pw_mono hA hB ht hAB)
end compression

section blocks
variable {r s : Type*} [Fintype r] [Fintype s] [DecidableEq r] [DecidableEq s]

def diagonalBlocksLM :
    (Matrix (r × r) (r × r) ℂ × Matrix (s × s) (s × s) ℂ) →ₗ[ℝ]
      Matrix ((r × r) ⊕ (s × s)) ((r × r) ⊕ (s × s)) ℂ where
  toFun X := Matrix.fromBlocks X.1 0 0 X.2
  map_add' X Y := by
    ext i j
    cases i <;> cases j <;> simp
  map_smul' c X := by
    ext i j
    cases i <;> cases j <;> simp

def diagonalBlocksCLM :
    (Matrix (r × r) (r × r) ℂ × Matrix (s × s) (s × s) ℂ) →L[ℝ]
      Matrix ((r × r) ⊕ (s × s)) ((r × r) ⊕ (s × s)) ℂ :=
  diagonalBlocksLM.toContinuousLinearMap

@[simp] theorem diagonalBlocksCLM_apply
    (X : Matrix (r × r) (r × r) ℂ) (Y : Matrix (s × s) (s × s) ℂ) :
    diagonalBlocksCLM (X, Y) = Matrix.fromBlocks X 0 0 Y := rfl

def blockPW (A : Matrix r r ℂ) (B : Matrix s s ℂ) (t : ℝ) :=
  diagonalBlocksCLM (pw A t, pw B t)

def blockKM (A : Matrix r r ℂ) (B : Matrix s s ℂ) :=
  diagonalBlocksCLM (km A, km B)

theorem blockPW_generator_commute (A : Matrix r r ℂ) (B : Matrix s s ℂ) (t : ℝ) :
    Commute (blockPW A B t) (blockGenerator (logarithm A) (logarithm B)) := by
  change Matrix.fromBlocks (pw A t) 0 0 (pw B t) *
      Matrix.fromBlocks (generator (logarithm A)) 0 0 (generator (logarithm B)) =
    Matrix.fromBlocks (generator (logarithm A)) 0 0 (generator (logarithm B)) *
      Matrix.fromBlocks (pw A t) 0 0 (pw B t)
  simp only [Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    (pw_generator_commute A t).eq, (pw_generator_commute B t).eq]

theorem hasDerivAt_blockPW {A : Matrix r r ℂ} {B : Matrix s s ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (t : ℝ) :
    HasDerivAt (blockPW A B)
      (blockGenerator (logarithm A) (logarithm B) * blockPW A B t) t := by
  have hh := diagonalBlocksCLM.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_pw hA t).prodMk (hasDerivAt_pw hB t))
  convert! hh using 1 <;>
    simp only [Function.comp_def, blockPW, diagonalBlocksCLM_apply, blockGenerator,
      Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  all_goals rfl

theorem hasDerivAt_blockPW_first {A : Matrix r r ℂ} {B : Matrix s s ℂ}
    (hA : A.PosDef) (hB : B.PosDef) (t : ℝ) :
    HasDerivAt (fun u => blockGenerator (logarithm A) (logarithm B) * blockPW A B u)
      (blockGenerator (logarithm A) (logarithm B) *
        blockGenerator (logarithm A) (logarithm B) * blockPW A B t) t := by
  simpa only [Matrix.zero_mul, zero_add, Matrix.mul_assoc] using
    OpenAICalculus.hasDerivAt_matrix_mul
      (hasDerivAt_const t (blockGenerator (logarithm A) (logarithm B)))
      (hasDerivAt_blockPW hA hB t)

theorem continuous_blockPW {A : Matrix r r ℂ} {B : Matrix s s ℂ}
    (hA : A.PosDef) (hB : B.PosDef) : Continuous (blockPW A B) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_blockPW hA hB t).continuousAt

theorem intervalIntegrable_blockPW {A : Matrix r r ℂ} {B : Matrix s s ℂ}
    (hA : A.PosDef) (hB : B.PosDef) :
    IntervalIntegrable (blockPW A B) MeasureTheory.volume 0 1 :=
  (continuous_blockPW hA hB).intervalIntegrable 0 1

theorem blockKM_eq_integral {A : Matrix r r ℂ} {B : Matrix s s ℂ}
    (hA : A.PosDef) (hB : B.PosDef) :
    blockKM A B = ∫ t in (0 : ℝ)..1, blockPW A B t := by
  have hp : (∫ t in (0 : ℝ)..1, (pw A t, pw B t)) = (km A, km B) := by
    rw [intervalIntegral, integral_pair (intervalIntegrable_pw hA).1
      (intervalIntegrable_pw hB).1, integral_pair
      (intervalIntegrable_pw hA).2 (intervalIntegrable_pw hB).2]
    rfl
  change diagonalBlocksCLM (km A, km B) = ∫ t in (0 : ℝ)..1, diagonalBlocksCLM (pw A t, pw B t)
  have hip : IntervalIntegrable (fun t => (pw A t, pw B t)) MeasureTheory.volume 0 1 :=
    ⟨(intervalIntegrable_pw hA).1.prodMk (intervalIntegrable_pw hB).1,
      (intervalIntegrable_pw hA).2.prodMk (intervalIntegrable_pw hB).2⟩
  calc
    diagonalBlocksCLM (km A, km B) =
        diagonalBlocksCLM (∫ t in (0 : ℝ)..1, (pw A t, pw B t)) := by rw [hp]
    _ = ∫ t in (0 : ℝ)..1, diagonalBlocksCLM (pw A t, pw B t) := by
      convert! (diagonalBlocksCLM.intervalIntegral_comp_comm hip).symm using 1
      all_goals rfl

local notation "Vβ" => blockInclusion (r := r) (s := s)

/-- The actual CFC PW curve supplies all commutation hypotheses of the Gram identity. -/
theorem stationaryGram_pw
    (T : Matrix (r ⊕ s) (r ⊕ s) ℂ) (A : Matrix r r ℂ) (B : Matrix s s ℂ)
    (lambda₀ lambda₁ : ℂ) (t : ℝ)
    (h₀ : logarithm A = (logarithm T).submatrix Sum.inl Sum.inl + lambda₀ • 1)
    (h₁ : logarithm B = (logarithm T).submatrix Sum.inr Sum.inr + lambda₁ • 1)
    (hD : (pw T t - Vβ * blockPW A B t * Vβᴴ).PosSemidef) :
    (Matrix.fromBlocks
      (Vβᴴ * pw T t * Vβ - blockPW A B t)
      (Vβᴴ * pw T t * (generator (logarithm T)) * Vβ - blockPW A B t * (blockGenerator (logarithm A) (logarithm B)))
      (Vβᴴ * pw T t * (generator (logarithm T)) * Vβ - blockPW A B t * (blockGenerator (logarithm A) (logarithm B)))
      (Vβᴴ * pw T t * (generator (logarithm T)) * (generator (logarithm T)) * Vβ - (blockGenerator (logarithm A) (logarithm B)) * blockPW A B t * (blockGenerator (logarithm A) (logarithm B)))).PosSemidef :=
  stationaryGram_of_blockStationarity (pw T t) (blockPW A B t)
    (logarithm T) (logarithm A) (logarithm B) lambda₀ lambda₁
    (logarithm_isHermitian T) h₀ h₁ (pw_generator_commute T t).eq
    (blockPW_generator_commute A B t).eq hD

def curve (T : Matrix (r ⊕ s) (r ⊕ s) ℂ)
    (A : Matrix r r ℂ) (B : Matrix s s ℂ) (t : ℝ) :=
  Vβᴴ * pw T t * Vβ - blockPW A B t

def curveFirst (T : Matrix (r ⊕ s) (r ⊕ s) ℂ)
    (A : Matrix r r ℂ) (B : Matrix s s ℂ) (t : ℝ) :=
  Vβᴴ * pw T t * (generator (logarithm T)) * Vβ - blockPW A B t * (blockGenerator (logarithm A) (logarithm B))

def curveSecond (T : Matrix (r ⊕ s) (r ⊕ s) ℂ)
    (A : Matrix r r ℂ) (B : Matrix s s ℂ) (t : ℝ) :=
  Vβᴴ * pw T t * (generator (logarithm T)) * (generator (logarithm T)) * Vβ - (blockGenerator (logarithm A) (logarithm B)) * blockPW A B t * (blockGenerator (logarithm A) (logarithm B))

theorem hasDerivAt_curve {T : Matrix (r ⊕ s) (r ⊕ s) ℂ}
    {A : Matrix r r ℂ} {B : Matrix s s ℂ}
    (hT : T.PosDef) (hA : A.PosDef) (hB : B.PosDef) (t : ℝ) :
    HasDerivAt (curve T A B) (curveFirst T A B t) t := by
  have hp : HasDerivAt (pw T) (pw T t * (generator (logarithm T))) t := by
    simpa only [(pw_generator_commute T t).eq] using hasDerivAt_pw hT t
  have hb : HasDerivAt (blockPW A B) (blockPW A B t * (blockGenerator (logarithm A) (logarithm B))) t := by
    simpa only [(blockPW_generator_commute A B t).eq] using hasDerivAt_blockPW hA hB t
  have hc := hasDerivAt_coordinateCompression blockCoordinates hp
  have hh := hc.sub hb
  convert! hh using 1 <;>
    simp only [curve, curveFirst, blockInclusion, Matrix.mul_assoc]
  all_goals rfl

theorem hasDerivAt_curveFirst {T : Matrix (r ⊕ s) (r ⊕ s) ℂ}
    {A : Matrix r r ℂ} {B : Matrix s s ℂ}
    (hT : T.PosDef) (hA : A.PosDef) (hB : B.PosDef) (t : ℝ) :
    HasDerivAt (curveFirst T A B) (curveSecond T A B t) t := by
  have hp : HasDerivAt (pw T) (pw T t * (generator (logarithm T))) t := by
    simpa only [(pw_generator_commute T t).eq] using hasDerivAt_pw hT t
  have hq := OpenAICalculus.hasDerivAt_matrix_mul hp
    (hasDerivAt_const t ((generator (logarithm T))))
  have hb := OpenAICalculus.hasDerivAt_matrix_mul (hasDerivAt_blockPW hA hB t)
    (hasDerivAt_const t ((blockGenerator (logarithm A) (logarithm B))))
  have hc := hasDerivAt_coordinateCompression blockCoordinates hq
  have hh := hc.sub hb
  convert! hh using 1 <;>
    simp only [curveFirst, curveSecond, blockInclusion, Function.comp_def,
      Matrix.mul_zero, add_zero, Matrix.mul_assoc]
  all_goals
    first | rfl | (ext u; simp only [curveFirst, Pi.sub_apply, blockInclusion, Matrix.mul_assoc])

theorem curve_posDef_of_residual
    (T : Matrix (r ⊕ s) (r ⊕ s) ℂ) (A : Matrix r r ℂ) (B : Matrix s s ℂ) (t : ℝ)
    (hD : (pw T t - Vβ * blockPW A B t * Vβᴴ).PosDef) :
    (curve T A B t).PosDef := by
  have hh := compression_posDef blockInclusion_isometry hD
  have he : Vβᴴ * (pw T t - Vβ * blockPW A B t * Vβᴴ) * Vβ = curve T A B t := by
    rw [Matrix.mul_sub, Matrix.sub_mul, curve]
    congr 1
    calc
      Vβᴴ * (Vβ * blockPW A B t * Vβᴴ) * Vβ =
          (Vβᴴ * Vβ) * blockPW A B t * (Vβᴴ * Vβ) := by
        simp only [Matrix.mul_assoc]
      _ = blockPW A B t := by
        rw [blockInclusion_isometry]
        simp only [Matrix.one_mul, Matrix.mul_one]
  rwa [he] at hh

theorem curveFirst_isHermitian
    (T : Matrix (r ⊕ s) (r ⊕ s) ℂ) (A : Matrix r r ℂ) (B : Matrix s s ℂ)
    (t : ℝ) (hT : T.PosDef) (hA : A.PosDef) (hB : B.PosDef) :
    (curveFirst T A B t).IsHermitian := by
  have hq := ((pw_posDef hT t).1.commute_iff
    (generator_isHermitian (logarithm_isHermitian T))).mp (pw_generator_commute T t)
  have hb : (blockPW A B t * (blockGenerator (logarithm A) (logarithm B))).IsHermitian := by
    have hbq : (blockPW A B t).IsHermitian :=
      (pw_posDef hA t).1.fromBlocks (by simp) (pw_posDef hB t).1
    have hbk : ((blockGenerator (logarithm A) (logarithm B))).IsHermitian :=
      (generator_isHermitian (logarithm_isHermitian A)).fromBlocks (by simp)
        (generator_isHermitian (logarithm_isHermitian B))
    exact (hbq.commute_iff hbk).mp (blockPW_generator_commute A B t)
  have hc := Matrix.isHermitian_conjTranspose_mul_mul Vβ hq
  simpa only [curveFirst, Matrix.mul_assoc] using hc.sub hb

/-- The Gram and Schur steps now concern the actual curve and its two derivatives.
Strict residual positivity and logarithmic stationarity still need analytic proofs. -/
theorem curve_riccati_of_stationarity
    {T : Matrix (r ⊕ s) (r ⊕ s) ℂ} {A : Matrix r r ℂ} {B : Matrix s s ℂ}
    (hT : T.PosDef) (hA : A.PosDef) (hB : B.PosDef)
    (lambda₀ lambda₁ : ℂ) (t : ℝ)
    (h₀ : logarithm A = (logarithm T).submatrix Sum.inl Sum.inl + lambda₀ • 1)
    (h₁ : logarithm B = (logarithm T).submatrix Sum.inr Sum.inr + lambda₁ • 1)
    (hD : (pw T t - Vβ * blockPW A B t * Vβᴴ).PosDef) :
    (curveSecond T A B t - curveFirst T A B t * (curve T A B t)⁻¹ *
      curveFirst T A B t).PosSemidef :=
  BetaOrder.gram_schur_residual_posSemidef _ _ _
    (curve_posDef_of_residual T A B t hD) (curveFirst_isHermitian T A B t hT hA hB)
    (stationaryGram_pw T A B lambda₀ lambda₁ t h₀ h₁ hD.posSemidef)

/-- PW implies KM by an actual Bochner integral, with no integration hypothesis left over.
The PW premise is the result to be supplied by matrix-curve comparison. -/
theorem km_of_pw
    {T : Matrix (r ⊕ s) (r ⊕ s) ℂ}
    {W₀ P₀ : Matrix r r ℂ} {W₁ P₁ : Matrix s s ℂ}
    (hT : T.PosDef) (hW₀ : W₀.PosDef) (hW₁ : W₁.PosDef)
    (hP₀ : P₀.PosDef) (hP₁ : P₁.PosDef)
    (hPW : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Vβᴴ * pw T t * Vβ ≤ blockPW W₀ W₁ t + blockPW P₀ P₁ t) :
    Vβᴴ * km T * Vβ ≤ blockKM W₀ W₁ + blockKM P₀ P₁ := by
  have hc := (compressionCLM Vβ).continuous.comp (continuous_pw hT)
  have hh := intervalIntegral_mono_on (hc.intervalIntegrable 0 1)
    ((intervalIntegrable_blockPW hW₀ hW₁).add (intervalIntegrable_blockPW hP₀ hP₁)) hPW
  simp only [Function.comp_def] at hh
  calc
    Vβᴴ * km T * Vβ = ∫ t in (0 : ℝ)..1, compressionCLM Vβ (pw T t) := by
      convert! ((compressionCLM Vβ).intervalIntegral_comp_comm (intervalIntegrable_pw hT)).symm using 1
      all_goals rfl
    _ ≤ ∫ t in (0 : ℝ)..1, blockPW W₀ W₁ t + blockPW P₀ P₁ t := by
      convert! hh using 1
      all_goals rfl
    _ = blockKM W₀ W₁ + blockKM P₀ P₁ := by
      rw [intervalIntegral.integral_add (intervalIntegrable_blockPW hW₀ hW₁)
        (intervalIntegrable_blockPW hP₀ hP₁),
        ← blockKM_eq_integral hW₀ hW₁, ← blockKM_eq_integral hP₀ hP₁]

end blocks
end QubitAdditivity.BetaBridge
