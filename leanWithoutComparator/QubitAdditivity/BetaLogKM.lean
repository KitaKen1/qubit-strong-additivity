import QubitAdditivity.BetaLogMean

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Matrix Set
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Elementwise Topology

namespace QubitAdditivity.BetaLogKM
open BetaPowers BetaLogMean
variable {n : Type*} [Fintype n] [DecidableEq n]

-- The log derivative uses the Frobenius norm; the already-defined KM matrix
-- uses its original entrywise norm. Scalar spectral coordinates bridge them.
@[reducible] local instance oNorm : NormedAddCommGroup (Matrix (n × n) (n × n) ℂ) :=
  inferInstanceAs (NormedAddCommGroup ((n × n) → (n × n) → ℂ))
@[reducible] local instance oSpace : NormedSpace ℝ (Matrix (n × n) (n × n) ℂ) :=
  inferInstanceAs (NormedSpace ℝ ((n × n) → (n × n) → ℂ))
@[reducible] local instance oTop : TopologicalSpace (Matrix (n × n) (n × n) ℂ) := oNorm.toUniformSpace.toTopologicalSpace
@[reducible] local instance oAdd : AddCommGroup (Matrix (n × n) (n × n) ℂ) := oNorm.toAddCommGroup
@[reducible] local instance oModule : Module ℝ (Matrix (n × n) (n × n) ℂ) := oSpace.toModule

local instance oComplete : CompleteSpace (Matrix (n × n) (n × n) ℂ) := by
  convert! (inferInstance : CompleteSpace ((n × n) → (n × n) → ℂ)) using 1

open scoped Matrix.Norms.Frobenius

@[reducible] local instance mNorm : NormedAddCommGroup (Matrix n n ℂ) :=
  Matrix.frobeniusNormedRing.toNonUnitalNormedRing.toNormedAddCommGroup
@[reducible] local instance mSpace : NormedSpace ℝ (Matrix n n ℂ) :=
  NormedAlgebra.toNormedSpace (Matrix n n ℂ)
@[reducible] local instance mTop : TopologicalSpace (Matrix n n ℂ) := mNorm.toUniformSpace.toTopologicalSpace
@[reducible] local instance mAdd : AddCommGroup (Matrix n n ℂ) := mNorm.toAddCommGroup
@[reducible] local instance mModule : Module ℝ (Matrix n n ℂ) := mSpace.toModule

@[reducible] local instance hTop : TopologicalSpace (HermitianMat n ℂ) :=
  HermitianMat.instNormedAddCommGroupComplex.toUniformSpace.toTopologicalSpace
@[reducible] local instance hAdd : AddCommGroup (HermitianMat n ℂ) :=
  HermitianMat.instNormedAddCommGroupComplex.toAddCommGroup
@[reducible] local instance hModule : Module ℝ (HermitianMat n ℂ) := HermitianMat.instNormedSpace.toModule

local instance matrixCFC : ContinuousFunctionalCalculus ℝ (Matrix n n ℂ) Matrix.IsHermitian := by
  letI : TopologicalSpace (Matrix n n ℂ) := inferInstanceAs (TopologicalSpace (n → n → ℂ))
  letI : AddCommGroup (Matrix n n ℂ) := Matrix.addCommGroup
  letI : Module ℝ (Matrix n n ℂ) := Matrix.module
  convert! (Matrix.IsHermitian.instContinuousFunctionalCalculus (𝕜 := ℂ) (n := n)) using 1

/-- Coordinates in one fixed eigenbasis of the base matrix. -/
def coordinates {A : Matrix n n ℂ} (hA : A.IsHermitian) (X : Matrix n n ℂ) : Matrix n n ℂ :=
  (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hA.eigenvectorUnitary).symm X

theorem coordinates_injective {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    Function.Injective (coordinates hA) :=
  (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hA.eigenvectorUnitary).symm.injective

theorem coordinates_mul {A : Matrix n n ℂ} (hA : A.IsHermitian) (X Y : Matrix n n ℂ) :
    coordinates hA (X*Y) = coordinates hA X * coordinates hA Y :=
  map_mul _ _ _

theorem coordinates_cfc {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    coordinates hA (cfc f A) = Matrix.diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) := by
  have hc : cfc f A = hA.cfc f := by convert! hA.cfc_eq f using 1
  rw [hc,Matrix.IsHermitian.cfc]
  exact (Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hA.eigenvectorUnitary).symm_apply_apply _

def coordinateLM {A : Matrix n n ℂ} (hA : A.IsHermitian) (i j : n) : Matrix n n ℂ →ₗ[ℝ] ℂ where
  toFun X := coordinates hA X i j
  map_add' X Y := by simp [coordinates,map_add]
  map_smul' r X := by
    simp [coordinates,Unitary.conjStarAlgAut_symm_apply,Matrix.mul_smul,Matrix.smul_mul]

def coordinateCLM {A : Matrix n n ℂ} (hA : A.IsHermitian) (i j : n) : Matrix n n ℂ →L[ℝ] ℂ :=
  (coordinateLM hA i j).toContinuousLinearMap

@[simp] theorem coordinateCLM_apply {A : Matrix n n ℂ} (hA : A.IsHermitian) (i j : n) (X : Matrix n n ℂ) :
    coordinateCLM hA i j X = coordinates hA X i j := rfl

theorem coordinates_power {A : Matrix n n ℂ} (hA : A.IsHermitian) (t : ℝ) :
    coordinates hA (power A t) = Matrix.diagonal (fun i => (((hA.eigenvalues i)^t : ℝ) : ℂ)) := by
  convert! coordinates_cfc hA (fun a => a^t) using 1

theorem inverseSegment_eq_cfc {A : Matrix n n ℂ} (hA : A.PosDef) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    BetaLog.inverseSegment A t = cfc (fun a : ℝ => (1+t*(a-1))⁻¹) A := by
  have hz : ∀ a ∈ spectrum ℝ A, 1+t*(a-1) ≠ 0 := by
    rw [hA.1.spectrum_real_eq_range_eigenvalues]
    rintro _ ⟨i,rfl⟩
    exact (BetaLog.scalar_segment_pos (hA.eigenvalues_pos i) ht).ne'
  have hi := cfc_inv (f := fun a : ℝ => 1+t*(a-1)) (a := A) hz
    (continuousOn_spectrum _ _) hA.1
  have hs : cfc (fun a : ℝ => 1+t*(a-1)) A = BetaLog.segment A t := by
    convert! (BetaLog.segment_eq_cfc hA.1 t).symm using 1
  rw [hs] at hi
  convert! hi.symm using 1
  exact Matrix.nonsing_inv_eq_ringInverse _

theorem coordinates_inverseSegment {A : Matrix n n ℂ} (hA : A.PosDef) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    coordinates hA.1 (BetaLog.inverseSegment A t) =
      Matrix.diagonal (fun i => (((1+t*(hA.1.eigenvalues i-1))⁻¹ : ℝ) : ℂ)) := by
  rw [inverseSegment_eq_cfc hA ht]
  exact coordinates_cfc hA.1 _

/-- The actual matrix-unit action of the already-defined KM matrix. -/
def kmApply (A X : Matrix n n ℂ) : Matrix n n ℂ :=
  fun i j => (km A *ᵥ fun ij => X ij.1 ij.2) (i,j)

/-- Operator evaluation followed by a scalar spectral coordinate. -/
def operatorCoordinateLM {A : Matrix n n ℂ} (hA : A.IsHermitian) (X : Matrix n n ℂ) (i j : n) :
    Matrix (n × n) (n × n) ℂ →ₗ[ℝ] ℂ where
  toFun K := coordinates hA (fun i j => (K *ᵥ fun ij => X ij.1 ij.2) (i,j)) i j
  map_add' K L := by
    simp only [Matrix.add_mulVec,Pi.add_apply]
    change coordinates hA ((fun i j => (K *ᵥ fun ij => X ij.1 ij.2) (i,j)) +
      (fun i j => (L *ᵥ fun ij => X ij.1 ij.2) (i,j))) i j = _
    exact (coordinateLM hA i j).map_add _ _
  map_smul' r K := by
    simp only [Matrix.smul_mulVec,Pi.smul_apply]
    change coordinates hA (r • (fun i j => (K *ᵥ fun ij => X ij.1 ij.2) (i,j))) i j = _
    exact (coordinateLM hA i j).map_smul r _

def operatorCoordinateCLM {A : Matrix n n ℂ} (hA : A.IsHermitian) (X : Matrix n n ℂ) (i j : n) :
    Matrix (n × n) (n × n) ℂ →L[ℝ] ℂ :=
  (operatorCoordinateLM hA X i j).toContinuousLinearMap

@[simp] theorem operatorCoordinateCLM_apply {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (X : Matrix n n ℂ) (i j : n) (K : Matrix (n × n) (n × n) ℂ) :
    operatorCoordinateCLM hA X i j K =
      coordinates hA (fun i j => (K *ᵥ fun ij => X ij.1 ij.2) (i,j)) i j := rfl

theorem pw_mulVec (A X : Matrix n n ℂ) (t : ℝ) :
    (fun i j => (pw A t *ᵥ fun ij => X ij.1 ij.2) (i,j)) = power A t * X * power A (1-t) := by
  ext i j
  rw [pw,← Matrix.mulVec_mulVec]
  have hr : (BetaOperators.right (power A (1-t)) *ᵥ fun ij => X ij.1 ij.2) =
      (fun ij => (X * power A (1-t)) ij.1 ij.2) := by
    ext ij
    exact BetaOperators.right_mulVec _ _ ij.1 ij.2
  rw [hr,BetaOperators.left_mulVec,← Matrix.mul_assoc]

theorem pw_spectral_coordinate {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (X : Matrix n n ℂ) (t : ℝ) (i j : n) :
    operatorCoordinateCLM hA X i j (pw A t) =
      (((hA.eigenvalues i)^t * (hA.eigenvalues j)^(1-t) : ℝ) : ℂ) * coordinates hA X i j := by
  rw [operatorCoordinateCLM_apply,pw_mulVec,coordinates_mul,coordinates_mul,
    coordinates_power,coordinates_power,Matrix.mul_diagonal,Matrix.diagonal_mul]
  simp only [Complex.ofReal_mul]
  ring

theorem coordinates_kmApply {A : Matrix n n ℂ} (hA : A.PosDef)
    (X : Matrix n n ℂ) (i j : n) :
    coordinates hA.1 (kmApply A X) i j =
      (mean (hA.1.eigenvalues i) (hA.1.eigenvalues j) : ℂ) * coordinates hA.1 X i j := by
  have hp : IntervalIntegrable (fun t : ℝ =>
      (hA.1.eigenvalues i)^t*(hA.1.eigenvalues j)^(1-t)) MeasureTheory.volume 0 1 :=
    ((Real.continuous_const_rpow (hA.eigenvalues_pos i).ne').mul
      ((Real.continuous_const_rpow (hA.eigenvalues_pos j).ne').comp
        (continuous_const.sub continuous_id))).intervalIntegrable 0 1
  calc
    coordinates hA.1 (kmApply A X) i j =
        ∫ t in (0 : ℝ)..1, operatorCoordinateCLM hA.1 X i j (pw A t) := by
      convert! ((operatorCoordinateCLM hA.1 X i j).intervalIntegral_comp_comm
        (intervalIntegrable_pw hA)).symm using 1
      all_goals convert! (oComplete (n := n)) using 1
    _ = ∫ t in (0 : ℝ)..1,
        (((hA.1.eigenvalues i)^t*(hA.1.eigenvalues j)^(1-t) : ℝ) : ℂ) *
          coordinates hA.1 X i j := by
      apply intervalIntegral.integral_congr
      intro t _
      exact pw_spectral_coordinate hA.1 X t i j
    _ = (mean (hA.1.eigenvalues i) (hA.1.eigenvalues j) : ℂ) *
        coordinates hA.1 X i j := by
      rw [intervalIntegral.integral_mul_const]
      congr 1
      exact Complex.ofRealCLM.intervalIntegral_comp_comm hp

theorem sandwich_spectral_coordinate {A : Matrix n n ℂ} (hA : A.PosDef)
    (H : HermitianMat n ℂ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (i j : n) :
    coordinates hA.1 (BetaLog.inverseSegment A t * H.mat * BetaLog.inverseSegment A t) i j =
      (((1+t*(hA.1.eigenvalues i-1))⁻¹ * (1+t*(hA.1.eigenvalues j-1))⁻¹ : ℝ) : ℂ) *
        coordinates hA.1 H.mat i j := by
  rw [coordinates_mul,coordinates_mul,coordinates_inverseSegment hA ht,
    Matrix.mul_diagonal,Matrix.diagonal_mul]
  simp only [Complex.ofReal_mul]
  ring

theorem coordinates_logDeriv {A : Matrix n n ℂ} (hA : A.PosDef)
    (H : HermitianMat n ℂ) (i j : n) :
    coordinates hA.1 (BetaLog.logDeriv A H) i j =
      (inverseMean (hA.1.eigenvalues i) (hA.1.eigenvalues j) : ℂ) * coordinates hA.1 H.mat i j := by
  have hr : IntervalIntegrable (fun t : ℝ =>
      BetaLog.inverseSegment A t * H.mat * BetaLog.inverseSegment A t)
      MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    convert! ((BetaLog.continuousOn_inverseSegment hA).mul continuousOn_const).mul
      (BetaLog.continuousOn_inverseSegment hA) using 1 <;> simp
  have hp : IntervalIntegrable (fun t : ℝ =>
      (1+t*(hA.1.eigenvalues i-1))⁻¹ * (1+t*(hA.1.eigenvalues j-1))⁻¹)
      MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul
    all_goals
      apply ContinuousOn.inv₀ (by fun_prop)
      intro t ht
      exact (BetaLog.scalar_segment_pos (hA.eigenvalues_pos _) (by simpa using ht)).ne'
  calc
    coordinates hA.1 (BetaLog.logDeriv A H) i j =
        ∫ t in (0 : ℝ)..1, coordinates hA.1
          (BetaLog.inverseSegment A t * H.mat * BetaLog.inverseSegment A t) i j := by
      rw [BetaLog.logDeriv_apply hA]
      convert! ((coordinateCLM hA.1 i j).intervalIntegral_comp_comm hr).symm using 1
    _ = ∫ t in (0 : ℝ)..1,
        (((1+t*(hA.1.eigenvalues i-1))⁻¹*(1+t*(hA.1.eigenvalues j-1))⁻¹ : ℝ) : ℂ) *
          coordinates hA.1 H.mat i j := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact sandwich_spectral_coordinate hA H (by simpa using ht) i j
    _ = (inverseMean (hA.1.eigenvalues i) (hA.1.eigenvalues j) : ℂ) *
        coordinates hA.1 H.mat i j := by
      rw [intervalIntegral.integral_mul_const]
      congr 1
      exact Complex.ofRealCLM.intervalIntegral_comp_comm hp

/-- The actual PW/KM integral inverts the noncommutative logarithm derivative.
The perturbation need not commute with the base matrix. -/
theorem kmApply_logDeriv {A : Matrix n n ℂ} (hA : A.PosDef) (H : HermitianMat n ℂ) :
    kmApply A (BetaLog.logDeriv A H) = H.mat := by
  apply coordinates_injective hA.1
  ext i j
  rw [coordinates_kmApply hA,coordinates_logDeriv hA,← mul_assoc]
  have hm : (mean (hA.1.eigenvalues i) (hA.1.eigenvalues j) : ℂ) *
      (inverseMean (hA.1.eigenvalues i) (hA.1.eigenvalues j) : ℂ) = 1 := by
    exact_mod_cast mean_mul_inverseMean (hA.eigenvalues_pos i) (hA.eigenvalues_pos j)
  rw [hm,one_mul]

/-- Matrix-unit coordinates of D log are the actual nonsingular KM inverse. -/
theorem logDeriv_eq_inverseKM {A : Matrix n n ℂ} (hA : A.PosDef) (H : HermitianMat n ℂ) :
    (fun ij : n × n => BetaLog.logDeriv A H ij.1 ij.2) =
      (km A)⁻¹ *ᵥ (fun ij : n × n => H.mat ij.1 ij.2) := by
  have hk : IsUnit (km A).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (BetaKM.km_posDef hA).isUnit
  have he : km A *ᵥ (fun ij : n × n => BetaLog.logDeriv A H ij.1 ij.2) =
      (fun ij : n × n => H.mat ij.1 ij.2) := by
    ext ij
    exact congrFun (congrFun (kmApply_logDeriv hA H) ij.1) ij.2
  rw [← he,Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ hk,Matrix.one_mulVec]

/-- Direct pointwise form for subsequent entropy Hessians and stationarity. -/
theorem logDeriv_eq_inverseKM_apply {A : Matrix n n ℂ} (hA : A.PosDef)
    (H : HermitianMat n ℂ) (i j : n) :
    BetaLog.logDeriv A H i j = ((km A)⁻¹ *ᵥ (fun ij : n × n => H.mat ij.1 ij.2)) (i,j) :=
  congrFun (logDeriv_eq_inverseKM hA H) (i,j)

/-- The inverse of the actual KM matrix, restricted to real Hermitian directions. -/
def inverseKMLM (A : Matrix n n ℂ) : HermitianMat n ℂ →ₗ[ℝ] Matrix n n ℂ where
  toFun H := fun i j => ((km A)⁻¹ *ᵥ fun ij : n × n => H.mat ij.1 ij.2) (i,j)
  map_add' H K := by
    ext i j
    simp only [HermitianMat.mat_add,Matrix.add_apply]
    change ((km A)⁻¹ *ᵥ ((fun ij : n × n => H.mat ij.1 ij.2) +
      (fun ij : n × n => K.mat ij.1 ij.2))) (i,j) = _
    rw [Matrix.mulVec_add]
    rfl
  map_smul' r H := by
    ext i j
    simp only [HermitianMat.mat_smul,Matrix.smul_apply]
    change ((km A)⁻¹ *ᵥ (r • (fun ij : n × n => H.mat ij.1 ij.2))) (i,j) = _
    rw [Matrix.mulVec_smul]
    rfl

def inverseKM (A : Matrix n n ℂ) : HermitianMat n ℂ →L[ℝ] Matrix n n ℂ :=
  (inverseKMLM A).toContinuousLinearMap

@[simp] theorem inverseKM_apply (A : Matrix n n ℂ) (H : HermitianMat n ℂ) (i j : n) :
    inverseKM A H i j = ((km A)⁻¹ *ᵥ fun ij : n × n => H.mat ij.1 ij.2) (i,j) := rfl

theorem logDeriv_eq_inverseKM_clm {A : Matrix n n ℂ} (hA : A.PosDef) :
    BetaLog.logDeriv A = inverseKM A := by
  ext H i j
  exact logDeriv_eq_inverseKM_apply hA H i j

/-- The actual noncommutative CFC log derivative is the inverse of the original
PW/KM integral, on the real Hermitian tangent space. -/
theorem hasFDerivAt_logarithm_inverseKM {A : HermitianMat n ℂ} (hA : A.mat.PosDef) :
    HasFDerivAt (fun B : HermitianMat n ℂ => logarithm B.mat) (inverseKM A.mat) A := by
  convert! (BetaLog.hasFDerivAt_logarithm hA).congr_fderiv
    (logDeriv_eq_inverseKM_clm hA) using 1

theorem inverseKM_isHermitian {A : HermitianMat n ℂ} (hA : A.mat.PosDef)
    (H : HermitianMat n ℂ) : (inverseKM A.mat H).IsHermitian := by
  rw [← logDeriv_eq_inverseKM_clm hA]
  exact BetaLog.logDeriv_isHermitian hA H

end QubitAdditivity.BetaLogKM
