-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergy.Galerkin.FiniteProjection
public import AVenhance.Infra.Parabolic.FourierGalerkin.ScalarSpace
public import AVRegularity.CoupledEnergy.Galerkin.WeakMass
import AVenhance.Infra.Parabolic.FourierGalerkin.MatrixOperator

section
@[expose] public section
noncomputable section
open MeasureTheory
open AVenhance.Infra.Parabolic.FourierGalerkin
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Vector valued Fourier modes and their finite orthogonal projections. -/

local instance torusMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance torusMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance torusProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance torusProbability : IsProbabilityMeasure (volume : Measure Torus) := inferInstance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

abbrev VectorFourierIndex (N : ℕ) (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :=
  Fin (RealFourierDimension N) × Fin (Module.finrank ℝ E)

/-- A normalized real Fourier mode with one orthonormal fiber direction. -/
noncomputable def vectorFourierMode (N : ℕ) (i : Fin (RealFourierDimension N))
    (j : Fin (Module.finrank ℝ E)) : Lp E 2 (volume : Measure Torus) :=
  ((ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
    ((stdOrthonormalBasis ℝ E) j)).compLpL 2 volume) (realFourierModeL2 N i)

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
/-- The vector valued Fourier family is orthonormal in torus `L²`. -/
theorem vectorFourierMode_orthonormal (N : ℕ)
    (i i' : Fin (RealFourierDimension N))
    (j j' : Fin (Module.finrank ℝ E)) :
    inner ℝ (vectorFourierMode N i j) (vectorFourierMode N i' j') =
      if (i, j) = (i', j') then 1 else 0 := by
  rw [MeasureTheory.L2.inner_def]
  have hvi := ContinuousLinearMap.coeFn_compLpL
    (L := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
      ((stdOrthonormalBasis ℝ E) j)) (realFourierModeL2 N i)
  have hvj := ContinuousLinearMap.coeFn_compLpL
    (L := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
      ((stdOrthonormalBasis ℝ E) j')) (realFourierModeL2 N i')
  have hmi := (realFourierModeFin_memLp N i).coeFn_toLp
  have hmj := (realFourierModeFin_memLp N i').coeFn_toLp
  calc
    ∫ x : Torus,
        inner ℝ (vectorFourierMode N i j x) (vectorFourierMode N i' j' x) =
      ∫ x : Torus,
        realFourierModeFin N i x * realFourierModeFin N i' x *
          inner ℝ ((stdOrthonormalBasis ℝ E) j) ((stdOrthonormalBasis ℝ E) j') := by
        apply integral_congr_ae
        filter_upwards [hvi, hvj, hmi, hmj] with x hvi hvj hmi hmj
        have hmi' : realFourierModeL2 N i x = realFourierModeFin N i x := by
          simpa [realFourierModeL2] using hmi
        have hmj' : realFourierModeL2 N i' x = realFourierModeFin N i' x := by
          simpa [realFourierModeL2] using hmj
        simp only [vectorFourierMode]
        rw [hvi, hvj, hmi', hmj']
        change inner ℝ (realFourierModeFin N i x • (stdOrthonormalBasis ℝ E) j)
          (realFourierModeFin N i' x • (stdOrthonormalBasis ℝ E) j') = _
        rw [real_inner_smul_left, real_inner_smul_right]
        ring
    _ = (∫ x : Torus, realFourierModeFin N i x * realFourierModeFin N i' x) *
        inner ℝ ((stdOrthonormalBasis ℝ E) j) ((stdOrthonormalBasis ℝ E) j') := by
          rw [integral_mul_const]
    _ = (if i = i' then 1 else 0) *
        (if j = j' then 1 else 0) := by
          rw [realFourierModeFin_orthonormal, OrthonormalBasis.inner_eq_ite]
    _ = if (i, j) = (i', j') then 1 else 0 := by
          by_cases hi : i = i' <;> by_cases hj : j = j' <;>
            simp [hi, hj]

/-- The torus `L²` projection onto all fiber-valued modes in the frequency box. -/
noncomputable def vectorFourierProjection (N : ℕ) :
    Lp E 2 (volume : Measure Torus) →L[ℝ] Lp E 2 (volume : Measure Torus) :=
  finiteOrthonormalProjection
    (fun p : VectorFourierIndex N E => vectorFourierMode N p.1 p.2)

theorem vectorFourierProjection_norm_le (N : ℕ)
    (f : Lp E 2 (volume : Measure Torus)) :
    ‖vectorFourierProjection (E := E) N f‖ ≤ ‖f‖ := by
  exact finiteOrthonormalProjection_norm_le
    (v := fun p : VectorFourierIndex N E => vectorFourierMode N p.1 p.2)
    (by
      intro p q
      exact vectorFourierMode_orthonormal N p.1 q.1 p.2 q.2)
    f

omit [MeasurableSpace E] [BorelSpace E] in
/-- Testing the vector-valued cutoff modes is the same as testing the matching scalar Fourier
mode after taking one orthonormal fiber coordinate. -/
theorem vectorFourierMode_coordinate_inner (N : ℕ)
    (f : Lp E 2 (volume : Measure Torus))
    (i : Fin (RealFourierDimension N)) (j : Fin (Module.finrank ℝ E)) :
    inner ℝ f (vectorFourierMode N i j) =
      inner ℝ
        ((InnerProductSpace.toDual ℝ E ((stdOrthonormalBasis ℝ E) j)).compLpL
          2 volume f)
        (realFourierModeL2 N i) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  have hmode := ContinuousLinearMap.coeFn_compLpL
    (L := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
      ((stdOrthonormalBasis ℝ E) j)) (realFourierModeL2 N i)
  have hcoord := ContinuousLinearMap.coeFn_compLpL
    (L := InnerProductSpace.toDual ℝ E ((stdOrthonormalBasis ℝ E) j)) f
  apply integral_congr_ae
  filter_upwards [hmode, hcoord] with x hmode hcoord
  change inner ℝ (f x)
      (((ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
        ((stdOrthonormalBasis ℝ E) j)).compLpL 2 volume (realFourierModeL2 N i)) x) = _
  rw [hmode, hcoord]
  change inner ℝ (f x)
      (realFourierModeL2 N i x • (stdOrthonormalBasis ℝ E) j) =
    inner ℝ (inner ℝ ((stdOrthonormalBasis ℝ E) j) (f x))
      (realFourierModeL2 N i x)
  rw [real_inner_smul_right]
  rw [real_inner_comm (f x) ((stdOrthonormalBasis ℝ E) j)]
  rw [Real.inner_apply]
  ring

end AVRegularity.CoupledEnergy.Galerkin
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
open scoped Topology
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Galerkin ODEs on plain finite scalar coefficient vectors. -/

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- A finite scalar vector with the standard Pi norm and instances. -/
abbrev PlainCoefficients (J : Type*) := J → ℝ

/-- The explicit finite matrix action, without a Sobolev subspace in its instance chain. -/
def plainMatrixCLM (A : J → J → ℝ) : PlainCoefficients J →L[ℝ] PlainCoefficients J :=
  ∑ i, ∑ j, A i j •
    (ContinuousLinearMap.proj j : PlainCoefficients J →L[ℝ] ℝ).smulRight (Pi.single i 1)

@[simp] theorem plainMatrixCLM_apply (A : J → J → ℝ) (x : PlainCoefficients J) (i : J) :
    plainMatrixCLM A x i = ∑ j, A i j * x j := by
  simp [plainMatrixCLM, Pi.single_apply]

/-- Scalar-entry measurability gives operator measurability by a finite rank-one sum. -/
theorem plainMatrixCLM_aestronglyMeasurable (A : ℝ → J → J → ℝ)
    (hA : ∀ i j, AEStronglyMeasurable (fun t => A t i j) volume) :
    AEStronglyMeasurable (fun t => plainMatrixCLM (A t)) volume := by
  unfold plainMatrixCLM
  apply AVenhance.Infra.Parabolic.FourierGalerkin.MatrixOperator.aestronglyMeasurable_finset_sum
  intro i _
  apply AVenhance.Infra.Parabolic.FourierGalerkin.MatrixOperator.aestronglyMeasurable_finset_sum
  intro j _
  exact (hA i j).smul aestronglyMeasurable_const

/-- A uniform scalar entry bound controls the plain matrix operator norm. -/
theorem plainMatrixCLM_norm_le (A : J → J → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ i j, |A i j| ≤ C) :
    ‖plainMatrixCLM A‖ ≤ (Fintype.card J : ℝ) * C := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (Nat.cast_nonneg _) hC)
  intro x
  apply pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC)
    (norm_nonneg x)) |>.mpr
  intro i
  rw [plainMatrixCLM_apply]
  calc
    ‖∑ j, A i j * x j‖ ≤ ∑ j, ‖A i j * x j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : J, C * ‖x‖ := Finset.sum_le_sum fun j _ => by
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul (hA i j) (norm_le_pi_norm x j) (norm_nonneg _) hC
    _ = (Fintype.card J : ℝ) * C * ‖x‖ := by simp [mul_assoc]

/-- Bounded measurable matrices and integrable forcing give a plain coefficient ODE. -/
def plainMatrixODEData {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → J → J → ℝ) (f : ℝ → PlainCoefficients J) (initial : PlainCoefficients J)
    (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ i j, AEStronglyMeasurable (fun t => A t i j) volume)
    (hbound : ∀ t i j, |A t i j| ≤ C)
    (hf : IntervalIntegrable f volume a b) :
    FiniteGalerkinODEData (V := PlainCoefficients J) a b hab where
  operator := fun t => plainMatrixCLM (A t)
  forcing := f
  initial := initial
  operatorBound := (Fintype.card J : ℝ) * C
  operatorBound_nonneg := mul_nonneg (Nat.cast_nonneg _) hC
  operator_aestronglyMeasurable := plainMatrixCLM_aestronglyMeasurable A hA
  operator_norm_le := fun t => plainMatrixCLM_norm_le (A t) C hC (hbound t)
  forcing_intervalIntegrable := hf

/-- The finite matrix right-hand side is integrable along every continuous coefficient path. -/
theorem plainMatrixODE_rhs_intervalIntegrable {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → J → J → ℝ) (f : ℝ → PlainCoefficients J) (initial : PlainCoefficients J)
    (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ i j, AEStronglyMeasurable (fun t => A t i j) volume)
    (hbound : ∀ t i j, |A t i j| ≤ C)
    (hf : IntervalIntegrable f volume a b) (y : C(Icc a b, PlainCoefficients J)) :
    IntervalIntegrable (fun t => plainMatrixCLM (A t) (AVenhance.Infra.ODE.extendCurve hab y t) + f t)
      volume a b :=
  ((plainMatrixODEData hab A f initial C hC hA hbound hf).toLinearODE hab).rhs_intervalIntegrable y

theorem plainMatrixODE_existsUnique {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → J → J → ℝ) (f : ℝ → PlainCoefficients J) (initial : PlainCoefficients J)
    (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ i j, AEStronglyMeasurable (fun t => A t i j) volume)
    (hbound : ∀ t i j, |A t i j| ≤ C)
    (hf : IntervalIntegrable f volume a b) :
    ∃! y : C(Icc a b, PlainCoefficients J),
      AVenhance.Infra.ODE.IsLinearIntegralSolution (fun t => plainMatrixCLM (A t)) f
          initial a b (AVenhance.Infra.ODE.extendCurve hab y) ∧
        AbsolutelyContinuousOnInterval (AVenhance.Infra.ODE.extendCurve hab y) a b :=
  (plainMatrixODEData hab A f initial C hC hA hbound hf).existsUnique_absolutelyContinuous hab

end AVRegularity.CoupledEnergy.Galerkin
end
end
