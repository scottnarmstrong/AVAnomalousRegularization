-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergy.Galerkin.PlainMatrix
public import AVRegularity.Statements.Intermediate.CoupledEnergy.CoefficientSeminorm
import AVenhance.Infra.Parabolic.WeakUniqueness.WeakProjection
public import AVenhance.Infra.Classical.GalerkinModeCalculus
import AVenhance.Infra.Classical.GalerkinGenerator
public import AVRegularity.Sobolev.Multiply.Carrier
public import AVenhance.Statements.Roots.IsPeriodicH1With
import AVenhance.Infra.ODE.Linear.Energy
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Tactic.Monotonicity.Lemmas

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Entrywise measurability and bounds for mass-inverted finite weak forms. -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- The elementary bilinear form associated to a trial and a test basis coordinate. -/
def weakRankOneForm (b : Module.Basis J ℝ V) (i j : J) : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
  (b.coord j).smulRight (b.coord i)

omit [FiniteDimensional ℝ V] in
/-- Finite weak forms are exactly the sum of their matrix entries. -/
theorem weakForm_eq_sum (b : Module.Basis J ℝ V) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    B = ∑ i, ∑ j, B (b j) (b i) • weakRankOneForm b i j := by
  apply b.ext
  intro k
  apply b.ext
  intro l
  simp [weakRankOneForm, Module.Basis.coord_apply, Finsupp.single_apply]

/-- Mass inversion is linear in the weak bilinear form. -/
def weakGeneratorOfFormLinearMap (M : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hM : Function.Injective M) :
    (V →ₗ[ℝ] V →ₗ[ℝ] ℝ) →ₗ[ℝ] V →L[ℝ] V where
  toFun := weakMassGeneratorCLM M hM
  map_add' := by
    intro B C
    apply ContinuousLinearMap.ext
    intro x
    change (weakMassEquiv M hM).symm ((B + C) x) =
      (weakMassEquiv M hM).symm (B x) + (weakMassEquiv M hM).symm (C x)
    rw [LinearMap.add_apply, map_add]
  map_smul' := by
    intro c B
    apply ContinuousLinearMap.ext
    intro x
    change (weakMassEquiv M hM).symm ((c • B) x) =
      c • (weakMassEquiv M hM).symm (B x)
    rw [LinearMap.smul_apply, map_smul]

/-- The continuous generator has exactly the same finite matrix expansion. -/
theorem weakMassGeneratorCLM_eq_sum (b : Module.Basis J ℝ V)
    (M : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hM : Function.Injective M)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    weakMassGeneratorCLM M hM B = ∑ i, ∑ j,
      B (b j) (b i) • weakMassGeneratorCLM M hM (weakRankOneForm b i j) := by
  have heq := congrArg (weakGeneratorOfFormLinearMap M hM) (weakForm_eq_sum b B)
  simpa only [map_sum, map_smul, weakGeneratorOfFormLinearMap,
    LinearMap.coe_mk, AddHom.coe_mk] using heq

/-- Entrywise time measurability suffices for a mass-inverted weak operator. -/
theorem weakMassGeneratorCLM_aestronglyMeasurable (b : Module.Basis J ℝ V)
    (M : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hM : Function.Injective M)
    (B : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hB : ∀ i j, AEStronglyMeasurable (fun t => B t (b j) (b i)) volume) :
    AEStronglyMeasurable (fun t => weakMassGeneratorCLM M hM (B t)) volume := by
  have hsum : AEStronglyMeasurable (fun t => ∑ i, ∑ j,
      B t (b j) (b i) • weakMassGeneratorCLM M hM (weakRankOneForm b i j)) volume := by
    apply AVenhance.Infra.Parabolic.FourierGalerkin.MatrixOperator.aestronglyMeasurable_finset_sum
    intro i _
    apply AVenhance.Infra.Parabolic.FourierGalerkin.MatrixOperator.aestronglyMeasurable_finset_sum
    intro j _
    exact (hB i j).smul aestronglyMeasurable_const
  exact hsum.congr (Filter.Eventually.of_forall fun t =>
    (weakMassGeneratorCLM_eq_sum b M hM (B t)).symm)

/-- Uniform entry bounds give a uniform bound for the actual evolution operator. -/
theorem weakMassGeneratorCLM_norm_le (b : Module.Basis J ℝ V)
    (M : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hM : Function.Injective M)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (C : J → J → ℝ)
    (hB : ∀ i j, |B (b j) (b i)| ≤ C i j) :
    ‖weakMassGeneratorCLM M hM B‖ ≤ ∑ i, ∑ j,
      C i j * ‖weakMassGeneratorCLM M hM (weakRankOneForm b i j)‖ := by
  rw [weakMassGeneratorCLM_eq_sum b M hM B]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hB i j) (norm_nonneg _)

end AVRegularity.CoupledEnergy.Galerkin
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Integrability of mass-inverted forcing from its finitely many test pairings. -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]
variable {J : Type*} [Fintype J] [DecidableEq J]

omit [FiniteDimensional ℝ V] [DecidableEq J] in
/-- Test values determine a finite-dimensional functional. -/
theorem weakFunctional_eq_sum (b : Module.Basis J ℝ V) (q : V →ₗ[ℝ] ℝ) :
    q = ∑ i, q (b i) • b.coord i := by
  apply b.ext
  intro j
  simp

omit [DecidableEq J] in
/-- Inverting the mass map preserves the finite functional expansion. -/
theorem weakMassSource_eq_sum (b : Module.Basis J ℝ V)
    (M : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hM : Function.Injective M) (q : V →ₗ[ℝ] ℝ) :
    weakMassSource M hM q = ∑ i, q (b i) • weakMassSource M hM (b.coord i) := by
  have heq := congrArg (weakMassEquiv M hM).symm (weakFunctional_eq_sum b q)
  simpa only [map_sum, map_smul, weakMassSource] using heq

end AVRegularity.CoupledEnergy.Galerkin
end
end

section
/-! Fiber coordinates of the finite vector-valued Fourier projection. -/

@[expose] public section

noncomputable section

open MeasureTheory
open AVenhance.Infra.Parabolic.FourierGalerkin

local instance torusMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance torusMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance torusProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance torusProbability : IsProbabilityMeasure (volume : Measure Torus) := inferInstance

namespace AVRegularity.CoupledEnergy.Galerkin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The scalar `L²` coordinate in one vector of the standard fiber basis. -/
noncomputable def vectorFourierCoordinate (j : Fin (Module.finrank ℝ E)) :
    Lp E 2 (volume : Measure Torus) →L[ℝ] Lp ℝ 2 (volume : Measure Torus) :=
  (InnerProductSpace.toDual ℝ E ((stdOrthonormalBasis ℝ E) j)).compLpL 2 volume

omit [MeasurableSpace E] [BorelSpace E] in
theorem vectorFourierCoordinate_mode (N : ℕ)
    (i : Fin (RealFourierDimension N))
    (j j' : Fin (Module.finrank ℝ E)) :
    vectorFourierCoordinate (E := E) j'
      (vectorFourierMode (E := E) N i j) =
      if j = j' then realFourierModeL2 N i else 0 := by
  apply Lp.ext
  have hcoord := ContinuousLinearMap.coeFn_compLpL
    (L := InnerProductSpace.toDual ℝ E ((stdOrthonormalBasis ℝ E) j'))
    (vectorFourierMode (E := E) N i j)
  have hmode := ContinuousLinearMap.coeFn_compLpL
    (L := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
      ((stdOrthonormalBasis ℝ E) j)) (realFourierModeL2 N i)
  have hreal := (realFourierModeFin_memLp N i).coeFn_toLp
  filter_upwards [hcoord, hmode, hreal] with x hcoord hmode hreal
  change ((InnerProductSpace.toDual ℝ E ((stdOrthonormalBasis ℝ E) j')).compLpL
      2 volume (vectorFourierMode (E := E) N i j)) x =
    (if j = j' then realFourierModeL2 N i else 0) x
  rw [hcoord]
  change ((InnerProductSpace.toDual ℝ E ((stdOrthonormalBasis ℝ E) j'))
      (((ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
        ((stdOrthonormalBasis ℝ E) j)).compLpL 2 volume
        (realFourierModeL2 N i)) x)) =
    (if j = j' then realFourierModeL2 N i else 0) x
  rw [hmode]
  have hreal' : realFourierModeL2 N i x = realFourierModeFin N i x := by
    simpa [realFourierModeL2] using hreal
  rw [hreal']
  change inner ℝ ((stdOrthonormalBasis ℝ E) j')
      (realFourierModeFin N i x • (stdOrthonormalBasis ℝ E) j) = _
  rw [real_inner_smul_right, OrthonormalBasis.inner_eq_ite]
  by_cases hj : j = j'
  · simpa [hj] using hreal'.symm
  · by_cases hji : j' = j
    · exact (hj hji.symm).elim
    · simp [hj, hji]

/-- The scalar orthogonal cutoff in the fixed real Fourier frame. -/
noncomputable def scalarFourierProjection (N : ℕ) :
    Lp ℝ 2 (volume : Measure Torus) →L[ℝ] Lp ℝ 2 (volume : Measure Torus) :=
  finiteOrthonormalProjection (fun i : Fin (RealFourierDimension N) =>
    realFourierModeL2 N i)

theorem scalarFourierProjection_eq_realFourierScalarMap (N : ℕ)
    (f : Lp ℝ 2 (volume : Measure Torus)) :
    scalarFourierProjection N f = realFourierScalarMap N
      (modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
        (fun x => f x)) := by
  classical
  have hc : finiteProjectionCoefficients
      (fun i : Fin (RealFourierDimension N) => realFourierModeL2 N i) f =
      modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
        (fun x => f x) := by
    apply PiLp.ext
    intro i
    simp only [finiteProjectionCoefficients, modeProjectionCoefficients, PiLp.toLp_apply]
    rw [MeasureTheory.L2.inner_def]
    change (∫ x : Torus, inner ℝ (f x) (realFourierModeL2 N i x)) = _
    apply integral_congr_ae
    filter_upwards [(realFourierModeFin_memLp N i).coeFn_toLp] with x hx
    have hmode : realFourierModeL2 N i x = realFourierModeFin N i x := by
      simpa [realFourierModeL2] using hx
    rw [hmode, Real.inner_apply]
  change finiteOrthonormalProjection
      (fun i : Fin (RealFourierDimension N) => realFourierModeL2 N i) f = _
  rw [finiteOrthonormalProjection_apply, realFourierScalarMap_apply, hc]
  rfl

theorem vectorFourierProjection_coordinate (N : ℕ)
    (f : Lp E 2 (volume : Measure Torus)) (j : Fin (Module.finrank ℝ E)) :
    vectorFourierCoordinate (E := E) j (vectorFourierProjection N f) =
      scalarFourierProjection N (vectorFourierCoordinate (E := E) j f) := by
  classical
  simp [vectorFourierProjection, scalarFourierProjection,
    finiteOrthonormalProjection_apply, finiteProjectionSynthesis,
    finiteProjectionCoefficients, Fintype.sum_prod_type,
    vectorFourierCoordinate_mode,
    vectorFourierMode_coordinate_inner]
  rfl

end AVRegularity.CoupledEnergy.Galerkin

end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set AVenhance.Infra.ODE
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Integrated row equations and energy chain rules after linear synthesis.
The a.e. integration in time uses the measurable-ODE energy API. -/

section
variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Applying a fixed linear observable to the plain ODE gives its integrated weak identity. -/
theorem plainODE_observable_identity {a b : ℝ} (hab : a ≤ b)
    (A : ℝ → J → J → ℝ) (f y : ℝ → PlainCoefficients J) (initial : PlainCoefficients J)
    (hy : IsLinearIntegralSolution (fun s => plainMatrixCLM (A s)) f initial a b y)
    (hint : IntervalIntegrable (linearRhs (fun s => plainMatrixCLM (A s)) f y) volume a b)
    (L : PlainCoefficients J →L[ℝ] ℝ) (t : ℝ) (ht : t ∈ Icc a b) :
    L (y t) - L initial = ∫ s in a..t, L (plainMatrixCLM (A s) (y s) + f s) := by
  have hsub : uIcc a t ⊆ uIcc a b := by
    rw [uIcc_of_le ht.1, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl ht.2
  have hcomm := L.intervalIntegral_comp_comm (hint.mono_set hsub)
  rw [hy t ht, map_add, add_sub_cancel_left]
  exact hcomm.symm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

omit [DecidableEq J] in
/-- The finite reconstruction chain rule, with a plain Pi state and an arbitrary Hilbert readout. -/
theorem plainSynthesis_hasDerivAt (R : PlainCoefficients J →L[ℝ] H)
    {y : ℝ → PlainCoefficients J} {q : PlainCoefficients J} {t : ℝ}
    (hy : HasDerivAt y q t) : HasDerivAt (fun s => R (y s)) (R q) t :=
  R.hasFDerivAt.comp_hasDerivAt t hy

omit [DecidableEq J] in
/-- Squared synthesized energy has the exact Hilbert chain-rule derivative. -/
theorem plainSynthesis_energy_hasDerivAt (R : PlainCoefficients J →L[ℝ] H)
    {y : ℝ → PlainCoefficients J} {q : PlainCoefficients J} {t : ℝ}
    (hy : HasDerivAt y q t) :
    HasDerivAt (fun s => ‖R (y s)‖ ^ 2) (2 * inner ℝ (R (y t)) (R q)) t :=
  (plainSynthesis_hasDerivAt R hy).norm_sq
end

/-! A finite Pi trajectory specified by its integrated scalar rows is the
zero-operator integral ODE with the prescribed forcing. This lets the
synthesis energy chain rule apply to projected weak traces. -/

section
variable {J : Type*} [Fintype J] [DecidableEq J]

theorem plainMatrixCLM_zero_apply (c : PlainCoefficients J) :
    plainMatrixCLM (fun _ _ => (0 : ℝ)) c = 0 := by
  funext r
  simp only [plainMatrixCLM_apply, zero_mul, Finset.sum_const_zero, Pi.zero_apply]

/-- Integrated scalar rows give a genuine finite vector primitive. -/
theorem plainRows_isIntegralSolution {a b : ℝ} (hab : a ≤ b)
    (q y : ℝ → PlainCoefficients J) (initial : PlainCoefficients J)
    (hq : IntervalIntegrable q volume a b)
    (hy : ∀ t ∈ Icc a b, ∀ r, y t r - initial r = ∫ s in a..t, q s r) :
    IsLinearIntegralSolution (fun _ => plainMatrixCLM (fun _ _ => (0 : ℝ))) q initial a b y := by
  intro t ht
  have hsub : uIcc a t ⊆ uIcc a b := by
    rw [uIcc_of_le ht.1, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl ht.2
  have hint := hq.mono_set hsub
  funext r
  have he := (ContinuousLinearMap.proj r : PlainCoefficients J →L[ℝ] ℝ).intervalIntegral_comp_comm hint
  simp only [linearRhs, plainMatrixCLM_zero_apply, zero_add]
  change y t r = initial r + (∫ s in a..t, q s) r
  simp only [ContinuousLinearMap.proj_apply] at he
  rw [← he]
  exact eq_add_of_sub_eq (hy t ht r) |>.trans (add_comm _ _)

/-- The zero-operator RHS is the given integrable vector forcing. -/
theorem plainRows_rhs_integrable {a b : ℝ} (q y : ℝ → PlainCoefficients J)
    (hq : IntervalIntegrable q volume a b) :
    IntervalIntegrable (linearRhs (fun _ => plainMatrixCLM (fun _ _ => (0 : ℝ))) q y) volume a b := by
  have he : linearRhs (fun _ => plainMatrixCLM (fun _ _ => (0 : ℝ))) q y = q := by
    funext t
    simp only [linearRhs, plainMatrixCLM_zero_apply, zero_add]
  rw [he]
  exact hq
end

end AVRegularity.CoupledEnergy.Galerkin
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped Topology
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Convert a bounded measurable finite-dimensional weak form to its ODE. -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- ODE data obtained by inverting a finite-dimensional weak mass form. The hypotheses on the
transformed operator and source are exactly the bounded measurable ODE hypotheses consumed by
the upstream linear ODE theorem. -/
noncomputable def weakGalerkinODEData {a b : ℝ} (hab : a ≤ b)
    (M : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hM : Function.Injective M)
    (B : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (q : ℝ → V →ₗ[ℝ] ℝ)
    (initial : V) (C : ℝ) (hC : 0 ≤ C)
    (hA : AEStronglyMeasurable (fun t =>
      weakMassGeneratorCLM M hM (B t)) volume)
    (hAbound : ∀ t, ‖weakMassGeneratorCLM M hM (B t)‖ ≤ C)
    (hq : IntervalIntegrable (fun t => weakMassSource M hM (q t)) volume a b) :
    FiniteGalerkinODEData (V := V) a b hab where
  operator := fun t => weakMassGeneratorCLM M hM (B t)
  forcing := fun t => weakMassSource M hM (q t)
  initial := initial
  operatorBound := C
  operatorBound_nonneg := hC
  operator_aestronglyMeasurable := hA
  operator_norm_le := hAbound
  forcing_intervalIntegrable := hq

/-- Every bounded measurable weak-form system on a finite-dimensional space has a unique
absolutely continuous trajectory after inversion of its nondegenerate mass form. -/
theorem weakGalerkinODE_existsUnique {a b : ℝ} (hab : a ≤ b)
    (M : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hM : Function.Injective M)
    (B : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (q : ℝ → V →ₗ[ℝ] ℝ)
    (initial : V) (C : ℝ) (hC : 0 ≤ C)
    (hA : AEStronglyMeasurable (fun t =>
      weakMassGeneratorCLM M hM (B t)) volume)
    (hAbound : ∀ t, ‖weakMassGeneratorCLM M hM (B t)‖ ≤ C)
    (hq : IntervalIntegrable (fun t => weakMassSource M hM (q t)) volume a b) :
    ∃! y : ContinuousMap (Set.Icc a b) V,
      AVenhance.Infra.ODE.IsLinearIntegralSolution
          (fun t => weakMassGeneratorCLM M hM (B t))
          (fun t => weakMassSource M hM (q t)) initial a b
          (AVenhance.Infra.ODE.extendCurve hab y) ∧
        AbsolutelyContinuousOnInterval (AVenhance.Infra.ODE.extendCurve hab y) a b := by
  exact (weakGalerkinODEData hab M hM B q initial C hC hA hAbound hq)
    |>.existsUnique_absolutelyContinuous hab

end AVRegularity.CoupledEnergy.Galerkin
end
end
end

section
@[expose] public section
noncomputable section
open Homogenization MeasureTheory
open scoped ENNReal NNReal
open AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Pointwise coefficient derivative bounds extracted from the factorial seminorm. -/

/-- A finite factorial coefficient seminorm controls every pointwise derivative array on the
specified time interval. -/
theorem coefficientSeminorm_derivative_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (ρ : ℝ) (hρ : 0 < ρ) (K : ℕ) (t₀ t₁ : ℝ)
    (A : ℝ → Vec 2 → E →L[ℝ] F)
    (hA : coefficientSeminorm ρ K t₀ t₁ A ≠ ⊤)
    (j : Fin (K + 1)) (t : ℝ) (ht : t ∈ Set.Icc t₀ t₁) (x : Vec 2) :
    ‖coefficientDerivativeArray (A t) j.val x‖ ≤
      (coefficientSeminorm ρ K t₀ t₁ A).toReal *
        ((j.val.factorial : ℝ) / ρ ^ j.val) := by
  let w : ℝ := ρ ^ j.val / (j.val.factorial : ℝ)
  have hw : 0 < w := by
    dsimp [w]
    positivity
  have hpoint :
      ‖coefficientDerivativeArray (A t) j.val x‖₊ ≤
        (⨆ s ∈ Set.Icc t₀ t₁, ⨆ y : Vec 2,
          (‖coefficientDerivativeArray (A s) j.val y‖₊ : ℝ≥0∞)) :=
    le_iSup_of_le t (le_iSup_of_le ht (le_iSup_of_le x le_rfl))
  have hsum :
      ENNReal.ofReal w * ‖coefficientDerivativeArray (A t) j.val x‖₊ ≤
        coefficientSeminorm ρ K t₀ t₁ A := by
    calc
      ENNReal.ofReal w * ‖coefficientDerivativeArray (A t) j.val x‖₊ ≤
          ENNReal.ofReal w *
            (⨆ s ∈ Set.Icc t₀ t₁, ⨆ y : Vec 2,
              (‖coefficientDerivativeArray (A s) j.val y‖₊ : ℝ≥0∞)) :=
        mul_le_mul_of_nonneg_left hpoint (show 0 ≤ ENNReal.ofReal w from zero_le)
      _ ≤ coefficientSeminorm ρ K t₀ t₁ A := by
        unfold coefficientSeminorm
        change ENNReal.ofReal (ρ ^ j.val / (j.val.factorial : ℝ)) *
            (⨆ s ∈ Set.Icc t₀ t₁, ⨆ y : Vec 2,
              (‖coefficientDerivativeArray (A s) j.val y‖₊ : ℝ≥0∞)) ≤
          ∑ l ∈ Finset.range (K + 1), ENNReal.ofReal (ρ ^ l / (l.factorial : ℝ)) *
            (⨆ s ∈ Set.Icc t₀ t₁, ⨆ y : Vec 2,
              (‖coefficientDerivativeArray (A s) l y‖₊ : ℝ≥0∞))
        exact Finset.single_le_sum
          (f := fun l : ℕ => ENNReal.ofReal (ρ ^ l / (l.factorial : ℝ)) *
            (⨆ s ∈ Set.Icc t₀ t₁, ⨆ y : Vec 2,
              (‖coefficientDerivativeArray (A s) l y‖₊ : ℝ≥0∞)))
          (fun _ _ => (bot_le : (0 : ℝ≥0∞) ≤ _))
          (Finset.mem_range.mpr j.isLt)
  have hreal := ENNReal.toReal_mono hA hsum
  have hreal' : w * ‖coefficientDerivativeArray (A t) j.val x‖ ≤
      (coefficientSeminorm ρ K t₀ t₁ A).toReal := by
    simpa [w, ENNReal.toReal_mul, hw.ne', ENNReal.toReal_ofReal hw.le] using hreal
  have hfactorial : (j.val.factorial : ℝ) ≠ 0 := by positivity
  have hρpow : ρ ^ j.val ≠ 0 := (pow_pos hρ _).ne'
  have hbound :
      ‖coefficientDerivativeArray (A t) j.val x‖ ≤
        (coefficientSeminorm ρ K t₀ t₁ A).toReal / w := by
    apply (le_div_iff₀ hw).2
    simpa [mul_comm] using hreal'
  have hinv : w⁻¹ = (j.val.factorial : ℝ) / ρ ^ j.val := by
    dsimp [w]
    field_simp
  calc
    ‖coefficientDerivativeArray (A t) j.val x‖ ≤
        (coefficientSeminorm ρ K t₀ t₁ A).toReal / w := hbound
    _ = (coefficientSeminorm ρ K t₀ t₁ A).toReal *
        ((j.val.factorial : ℝ) / ρ ^ j.val) := by
      rw [div_eq_mul_inv, hinv]

end AVRegularity.CoupledEnergy.Galerkin
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set AVenhance.Infra.ODE
namespace AVRegularity.CoupledEnergy.Galerkin

/-! An integrable native row primitive satisfies the actual matrix ODE
when the two right hand sides agree almost everywhere on the time interval. -/

section
variable {J : Type*} [Fintype J] [DecidableEq J]

theorem plainPrimitive_changeRhs {a b : ℝ} (hab : a ≤ b)
    (q y z : ℝ → PlainCoefficients J) (initial : PlainCoefficients J)
    (L : ℝ → PlainCoefficients J →L[ℝ] PlainCoefficients J)
    (source : ℝ → PlainCoefficients J) (hq : IntervalIntegrable q volume a b)
    (hy : IsLinearIntegralSolution (fun _ => plainMatrixCLM (fun _ _ => (0 : ℝ)))
      q initial a b y)
    (hz : ∀ t ∈ Icc a b, z t = y t)
    (he : q =ᵐ[volume.restrict (Icc a b)] linearRhs L source z) :
    IntervalIntegrable (linearRhs L source z) volume a b ∧
      IsLinearIntegralSolution L source initial a b z := by
  have hn : IntegrableOn (linearRhs L source z) (Icc a b) :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hq).congr he
  refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hn, ?_⟩
  intro t ht
  rw [hz t ht, hy t ht]
  simp only [linearRhs, plainMatrixCLM_zero_apply, zero_add]
  congr 1
  apply intervalIntegral.integral_congr_ae_restrict
  apply ae_restrict_of_ae_restrict_of_subset _ he
  rw [uIoc_of_le ht.1]
  exact fun s hs => ⟨hs.1.le, hs.2.trans ht.2⟩
end

/-! The energy chain rule for differences of finite Fourier readouts. It
uses ordinary finite Pi coefficient primitives on both cutoffs, through
the reconstruction energy argument, without a Sobolev subspace ODE. -/

section
variable {J L H : Type*} [Fintype J] [DecidableEq J] [Fintype L] [DecidableEq L]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Difference readouts of two finite primitives have the exact Hilbert energy identity. -/
theorem plainPrimitive_band_energy_identity {a b : ℝ} (hab : a ≤ b)
    (q y : ℝ → PlainCoefficients J) (p z : ℝ → PlainCoefficients L)
    (initial : PlainCoefficients J) (initial' : PlainCoefficients L)
    (hq : IntervalIntegrable q volume a b) (hp : IntervalIntegrable p volume a b)
    (hy : IsLinearIntegralSolution (fun _ => plainMatrixCLM (fun _ _ => (0 : ℝ))) q initial a b y)
    (hz : IsLinearIntegralSolution (fun _ => plainMatrixCLM (fun _ _ => (0 : ℝ))) p initial' a b z)
    (R : PlainCoefficients J →L[ℝ] H) (S : PlainCoefficients L →L[ℝ] H) :
    (∫ t in a..b, 2 * inner ℝ (R (y t) - S (z t)) (R (q t) - S (p t))) =
      ‖R (y b) - S (z b)‖ ^ 2 - ‖R (y a) - S (z a)‖ ^ 2 := by
  have hq' := plainRows_rhs_integrable q y hq
  have hp' := plainRows_rhs_integrable p z hp
  have hacy := R.lipschitzWith.comp_absolutelyContinuousOnInterval
    (hy.absolutelyContinuousOnInterval hab hq')
  have hacz := S.lipschitzWith.comp_absolutelyContinuousOnInterval
    (hz.absolutelyContinuousOnInterval hab hp')
  have hdY := hy.ae_hasDerivAt hab hq'
  have hdZ := hz.ae_hasDerivAt hab hp'
  have hd : ∀ᵐ t ∂volume, t ∈ uIcc a b → HasDerivAt
      (fun s => ‖R (y s) - S (z s)‖ ^ 2)
        (2 * inner ℝ (R (y t) - S (z t)) (R (q t) - S (p t))) t := by
    filter_upwards [hdY, hdZ] with t hyt hzt
    intro ht
    have hmem : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using ht
    have hyq : HasDerivAt y (q t) t := by
      simpa only [linearRhs, plainMatrixCLM_zero_apply, zero_add] using hyt hmem
    have hzp : HasDerivAt z (p t) t := by
      simpa only [linearRhs, plainMatrixCLM_zero_apply, zero_add] using hzt hmem
    exact ((plainSynthesis_hasDerivAt R hyq).sub (plainSynthesis_hasDerivAt S hzp)).norm_sq
  exact integral_energy_eq_norm_sq_sub (hacy.sub hacz).norm_sq hd
end

end AVRegularity.CoupledEnergy.Galerkin
end
end

section
@[expose] public section
open MeasureTheory Homogenization
open AVRegularity.Sobolev
open AVenhance.Infra.Torus AVenhance.Infra.Parabolic.FourierGalerkin
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Scalar Fourier tests extracted from a vector valued periodic weak jet. -/

noncomputable local instance cellBridgeMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance cellBridgeMeasureIsAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance cellBridgeProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance cellBridgeProbabilityTorus : IsProbabilityMeasure
    (volume : Measure (UnitAddTorus (Fin 2))) := inferInstance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- A scalar coordinate of one value in a periodic ordered jet. -/
noncomputable def torusJetCoordinateValue {K : ℕ} (f : TorusHk K E)
    (a : JetIndex2 K) (e : E) : Vec 2 → ℝ :=
  fun x => inner ℝ e (f.toFunction.jet a x)

/-- The scalar gradient coordinate given by the next ordered jet slots. -/
noncomputable def torusJetCoordinateGradient {K : ℕ} (f : TorusHk K E)
    (j : Fin K) (w : DerivativeWord2 j.val) (e : E) : Vec 2 → Vec 2 :=
  fun x i => inner ℝ e (f.toFunction.jet (nextIndex2 j w i) x)

/-- Every scalar coordinate of a torus weak jet is an upstream periodic `H¹` field. -/
theorem torusJetCoordinate_isPeriodicH1With {K : ℕ} (f : TorusHk K E)
    (j : Fin K) (w : DerivativeWord2 j.val) (e : E) :
    AVenhance.IsPeriodicH1With
      (torusJetCoordinateValue f (lowerIndex2 j w) e)
      (torusJetCoordinateGradient f j w e) := by
  let F := f.toFunction
  have hF := F.hasPeriodicWeakJet
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n x
    have hshift : AVenhance.Infra.Torus.intVector n = AVenhance.latticeShift n := rfl
    change inner ℝ e (F.jet (lowerIndex2 j w)
      (x + AVenhance.Infra.Torus.intVector n)) = inner ℝ e (F.jet (lowerIndex2 j w) x)
    rw [hshift]
    exact congrArg (inner ℝ e) (hF.1 (lowerIndex2 j w) n x)
  · intro n x
    funext i
    have hshift : AVenhance.Infra.Torus.intVector n = AVenhance.latticeShift n := rfl
    change inner ℝ e (F.jet (nextIndex2 j w i)
      (x + AVenhance.Infra.Torus.intVector n)) = inner ℝ e (F.jet (nextIndex2 j w i) x)
    rw [hshift]
    exact congrArg (inner ℝ e) (hF.1 (nextIndex2 j w i) n x)
  · exact (InnerProductSpace.toDual ℝ E e).comp_memLp'
      (hF.2.1 (lowerIndex2 j w))
  · intro i
    exact (InnerProductSpace.toDual ℝ E e).comp_memLp'
      (hF.2.1 (nextIndex2 j w i))
  · intro i
    exact hF.2.2 j w i e

/-- Fourier truncation commutes with one ordered weak derivative after taking any scalar
coordinate in the finite dimensional fiber. -/
theorem torusJetCoordinate_fourierDerivative {K : ℕ} (f : TorusHk K E)
    (j : Fin K) (w : DerivativeWord2 j.val) (e : E) (N : ℕ) (i : Fin 2) :
    modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
        (periodicToTorus (torusJetCoordinateGradient f j w e · i)) =
      AVenhance.Infra.Classical.realFourierModeDerivativeCoefficients N
        (modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
          (periodicToTorus (torusJetCoordinateValue f (lowerIndex2 j w) e))) i := by
  exact (AVenhance.Infra.Parabolic.WeakUniqueness.weakGradient_realFourierProjectionCoefficients
    (torusJetCoordinate_isPeriodicH1With f j w e) N i).symm

end AVRegularity.CoupledEnergy.Galerkin
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVenhance.Infra.Torus AVenhance.Infra.Parabolic.FourierGalerkin
open AVenhance.Infra.Classical
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Smooth finite Fourier representatives attached to periodic jet coordinates. -/

local instance coupledPolynomialMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance coupledPolynomialAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance coupledPolynomialCircleProbability : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance coupledPolynomialTorusProbability : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The scalar trigonometric polynomial obtained by cutting off one periodic jet coordinate. -/
noncomputable def torusJetCoordinateFourierPolynomial {K : ℕ} (N : ℕ)
    (f : TorusHk K E) (a : JetIndex2 K) (e : E) : Vec 2 → ℝ :=
  realFourierModeAmbientExpansion N
    (modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
      (periodicToTorus (torusJetCoordinateValue f a e)))

omit [FiniteDimensional ℝ E] in
theorem torusJetCoordinateFourierPolynomial_contDiff {K : ℕ} (N : ℕ)
    (f : TorusHk K E) (a : JetIndex2 K) (e : E) :
    ContDiff ℝ ⊤ (torusJetCoordinateFourierPolynomial N f a e) := by
  simpa [torusJetCoordinateFourierPolynomial] using
    realFourierModeAmbientExpansion_contDiff N
      (modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
        (periodicToTorus (torusJetCoordinateValue f a e)))

omit [FiniteDimensional ℝ E] in
theorem torusJetCoordinateFourierPolynomial_periodic {K : ℕ} (N : ℕ)
    (f : TorusHk K E) (a : JetIndex2 K) (e : E) :
    AVenhance.IsZ2Periodic (torusJetCoordinateFourierPolynomial N f a e) := by
  simpa [torusJetCoordinateFourierPolynomial] using
    realFourierModeAmbientExpansion_periodic N
      (modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
        (periodicToTorus (torusJetCoordinateValue f a e)))

omit [FiniteDimensional ℝ E] in
theorem torusJetCoordinateFourierPolynomial_derivative {K : ℕ} (N : ℕ)
    (f : TorusHk K E) (j : Fin K) (w : DerivativeWord2 j.val) (e : E)
    (i : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (torusJetCoordinateFourierPolynomial N f (lowerIndex2 j w) e)
        x i =
      torusJetCoordinateFourierPolynomial N f (nextIndex2 j w i) e x := by
  have hcoeff := torusJetCoordinate_fourierDerivative f j w e N i
  change AVenhance.spaceGrad (realFourierModeAmbientExpansion N
      (modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
        (periodicToTorus (torusJetCoordinateValue f (lowerIndex2 j w) e)))) x i =
    realFourierModeAmbientExpansion N
      (modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
        (periodicToTorus (torusJetCoordinateValue f (nextIndex2 j w i) e))) x
  have hderiv := congrFun
    (spaceGrad_realFourierModeAmbientExpansion_eq_derivativeExpansion N
      (modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
        (periodicToTorus (torusJetCoordinateValue f (lowerIndex2 j w) e))) i) x
  have hcoeff' :
      modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
          (periodicToTorus (torusJetCoordinateValue f (nextIndex2 j w i) e)) =
      realFourierModeDerivativeCoefficients N
          (modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
            (periodicToTorus (torusJetCoordinateValue f (lowerIndex2 j w) e))) i := by
    exact hcoeff
  rw [hderiv, hcoeff']

end AVRegularity.CoupledEnergy.Galerkin
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Bounded continuous spatial coefficients act linearly on L² classes. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

/-- Pointwise coefficient multiplication, using its L² integrability proof. -/
def boundedCoefficientL2 {U : Set (Vec 2)} (C : Vec 2 → E →L[ℝ] F)
    (hC : Continuous C) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x, ‖C x‖ ≤ M)
    (u : Lp E 2 (volume.restrict U)) : Lp F 2 (volume.restrict U) :=
  (memLp_operator_mul hC (Lp.memLp u) hM hb).toLp (fun x => C x (u x))

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] in
theorem boundedCoefficientL2_ae {U : Set (Vec 2)} (C : Vec 2 → E →L[ℝ] F)
    (hC : Continuous C) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x, ‖C x‖ ≤ M)
    (u : Lp E 2 (volume.restrict U)) :
    boundedCoefficientL2 C hC M hM hb u =ᵐ[volume.restrict U] fun x => C x (u x) :=
  (memLp_operator_mul hC (Lp.memLp u) hM hb).coeFn_toLp

/-- The coefficient multiplier respects the L² quotient and is linear. -/
def boundedCoefficientL2LinearMap {U : Set (Vec 2)} (C : Vec 2 → E →L[ℝ] F)
    (hC : Continuous C) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x, ‖C x‖ ≤ M) :
    Lp E 2 (volume.restrict U) →ₗ[ℝ] Lp F 2 (volume.restrict U) where
  toFun := boundedCoefficientL2 C hC M hM hb
  map_add' := by
    intro u v
    apply Lp.ext
    filter_upwards [boundedCoefficientL2_ae C hC M hM hb (u + v),
      boundedCoefficientL2_ae C hC M hM hb u,
      boundedCoefficientL2_ae C hC M hM hb v,
      Lp.coeFn_add u v,
      Lp.coeFn_add (boundedCoefficientL2 C hC M hM hb u)
        (boundedCoefficientL2 C hC M hM hb v)] with x huv hu hv hadd hout
    rw [huv, hout, hadd]
    simp only [Pi.add_apply]
    rw [hu, hv]
    exact (C x).map_add _ _
  map_smul' := by
    intro c u
    apply Lp.ext
    filter_upwards [boundedCoefficientL2_ae C hC M hM hb (c • u),
      boundedCoefficientL2_ae C hC M hM hb u,
      Lp.coeFn_smul c u,
      Lp.coeFn_smul c (boundedCoefficientL2 C hC M hM hb u)] with x hcu hu hin hout
    change boundedCoefficientL2 C hC M hM hb (c • u) x =
      (c • boundedCoefficientL2 C hC M hM hb u) x
    rw [hcu, hout, hin]
    simp only [Pi.smul_apply]
    rw [hu]
    exact (C x).map_smul c _

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] in
theorem boundedCoefficientL2_norm_le {U : Set (Vec 2)} (C : Vec 2 → E →L[ℝ] F)
    (hC : Continuous C) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x, ‖C x‖ ≤ M)
    (u : Lp E 2 (volume.restrict U)) :
    ‖boundedCoefficientL2 C hC M hM hb u‖ ≤ M * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [boundedCoefficientL2_ae C hC M hM hb u] with x hx
  rw [hx]
  exact ((C x).le_opNorm (u x)).trans
    (mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _))

/-- The genuine bounded L² coefficient operator. -/
def boundedCoefficientL2CLM {U : Set (Vec 2)} (C : Vec 2 → E →L[ℝ] F)
    (hC : Continuous C) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x, ‖C x‖ ≤ M) :
    Lp E 2 (volume.restrict U) →L[ℝ] Lp F 2 (volume.restrict U) :=
  (boundedCoefficientL2LinearMap C hC M hM hb).mkContinuous M
    (boundedCoefficientL2_norm_le C hC M hM hb)


omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] in
/-- The spatial coefficient bound is also its L² operator norm bound. -/
theorem boundedCoefficientL2CLM_norm_le {U : Set (Vec 2)}
    (C : Vec 2 → E →L[ℝ] F) (hC : Continuous C) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ x, ‖C x‖ ≤ M) : ‖boundedCoefficientL2CLM (U := U) C hC M hM hb‖ ≤ M := by
  exact LinearMap.mkContinuous_norm_le (boundedCoefficientL2LinearMap C hC M hM hb) hM
    (boundedCoefficientL2_norm_le C hC M hM hb)

end AVRegularity.CoupledEnergy.Galerkin
end
end

section
/-! The exact seminorm budget for the factorial coefficient multiplier. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal NNReal

namespace AVRegularity.CoupledEnergy.Galerkin

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Extended supremum of one ordered coefficient derivative array on the time interval. -/
def coefficientOrderSup (a b : ℝ) (A : ℝ → Vec 2 → E →L[ℝ] F) (l : ℕ) : ℝ≥0∞ :=
  ⨆ t ∈ Set.Icc a b, ⨆ x : Vec 2, (‖coefficientDerivativeArray (A t) l x‖₊ : ℝ≥0∞)

/-- Each weighted summand is finite when the full seminorm is finite. -/
theorem coefficientOrderTerm_ne_top (ρ : ℝ) (K : ℕ) (a b : ℝ)
    (A : ℝ → Vec 2 → E →L[ℝ] F) (hA : coefficientSeminorm ρ K a b A ≠ ⊤)
    (l : ℕ) (hl : l ≤ K) :
    ENNReal.ofReal (factorialRootWeight ρ l) * coefficientOrderSup a b A l ≠ ⊤ := by
  apply ne_top_of_le_ne_top hA
  change ENNReal.ofReal (factorialRootWeight ρ l) * coefficientOrderSup a b A l ≤
    ∑ j ∈ Finset.range (K + 1), ENNReal.ofReal (factorialRootWeight ρ j) * coefficientOrderSup a b A j
  exact Finset.single_le_sum
    (f := fun j => ENNReal.ofReal (factorialRootWeight ρ j) * coefficientOrderSup a b A j)
    (fun _ _ => zero_le) (Finset.mem_range.mpr (Nat.lt_succ_of_le hl))

/-- Positive factorial weights force the individual derivative supremum to be finite. -/
theorem coefficientOrderSup_ne_top (ρ : ℝ) (hρ : 0 < ρ) (K : ℕ) (a b : ℝ)
    (A : ℝ → Vec 2 → E →L[ℝ] F) (hA : coefficientSeminorm ρ K a b A ≠ ⊤)
    (l : ℕ) (hl : l ≤ K) : coefficientOrderSup a b A l ≠ ⊤ := by
  have hw : 0 < factorialRootWeight ρ l := by unfold factorialRootWeight; positivity
  intro htop
  have hterm := coefficientOrderTerm_ne_top ρ K a b A hA l hl
  rw [htop, ENNReal.mul_top (by positivity)] at hterm
  exact hterm rfl

/-- The real supremum bounds every coefficient derivative at every interval time. -/
theorem coefficientOrderSup_derivative_bound (ρ : ℝ) (hρ : 0 < ρ) (K : ℕ) (a b : ℝ)
    (A : ℝ → Vec 2 → E →L[ℝ] F) (hA : coefficientSeminorm ρ K a b A ≠ ⊤)
    (l : ℕ) (hl : l ≤ K) (t : ℝ) (ht : t ∈ Set.Icc a b) (x : Vec 2) :
    ‖coefficientDerivativeArray (A t) l x‖ ≤ (coefficientOrderSup a b A l).toReal := by
  have hpoint : (‖coefficientDerivativeArray (A t) l x‖₊ : ℝ≥0∞) ≤
      coefficientOrderSup a b A l :=
    le_iSup_of_le t (le_iSup_of_le ht (le_iSup_of_le x le_rfl))
  exact ENNReal.toReal_mono (coefficientOrderSup_ne_top ρ hρ K a b A hA l hl) hpoint

/-- Summing the individual real suprema uses the seminorm once, without an order-dependent loss. -/
theorem coefficientSeminorm_eq_sum_real_budget (ρ : ℝ) (hρ : 0 < ρ) (K : ℕ) (a b : ℝ)
    (A : ℝ → Vec 2 → E →L[ℝ] F) (hA : coefficientSeminorm ρ K a b A ≠ ⊤) :
    (∑ l : Fin (K + 1), factorialRootWeight ρ l.val * (coefficientOrderSup a b A l.val).toReal) =
      (coefficientSeminorm ρ K a b A).toReal := by
  change (∑ l : Fin (K + 1), factorialRootWeight ρ l.val * (coefficientOrderSup a b A l.val).toReal) =
    (∑ j ∈ Finset.range (K + 1), ENNReal.ofReal (factorialRootWeight ρ j) * coefficientOrderSup a b A j).toReal
  rw [ENNReal.toReal_sum (fun l hl =>
    coefficientOrderTerm_ne_top ρ K a b A hA l (Nat.le_of_lt_succ (Finset.mem_range.mp hl)))]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro l _
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal]
  unfold factorialRootWeight
  positivity

end AVRegularity.CoupledEnergy.Galerkin

namespace AVRegularity.CoupledEnergy.Galerkin

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

/-- The carrier multiplier at one interval time, using the actual per-order seminorm suprema. -/
def torusMultiplyIntervalCoefficient (ρ : ℝ) (hρ : 0 < ρ) (K : ℕ) (a b : ℝ)
    (A : ℝ → Vec 2 → E →L[ℝ] F) (hA : coefficientSeminorm ρ K a b A ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (hC : ContDiff ℝ (K : ℕ) (A t))
    (hp : AVenhance.IsZ2Periodic (A t)) (w : TorusHk K E) : TorusHk K F :=
  w.mulCoefficient (A t) hC hp (fun l x =>
    coefficientOrderSup_derivative_bound ρ hρ K a b A hA l.val
      (Nat.le_of_lt_succ l.isLt) t ht x)

omit [FiniteDimensional ℝ F] in
/-- The exact coefficient seminorm controls the factorial multiplier norm. -/
theorem torusMultiplyIntervalCoefficient_factorialNorm_le
    (ρ : ℝ) (hρ : 0 < ρ) (K : ℕ) (a b : ℝ)
    (A : ℝ → Vec 2 → E →L[ℝ] F) (hA : coefficientSeminorm ρ K a b A ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (hC : ContDiff ℝ (K : ℕ) (A t))
    (hp : AVenhance.IsZ2Periodic (A t)) (w : TorusHk K E) :
    Real.sqrt (factorialNormSq ρ (torusMultiplyIntervalCoefficient ρ hρ K a b A hA t ht hC hp w).val) ≤
      (coefficientSeminorm ρ K a b A).toReal * Real.sqrt (factorialNormSq ρ w.val) := by
  have hb := fun (l : Fin (K + 1)) (x : Vec 2) =>
    coefficientOrderSup_derivative_bound ρ hρ K a b A hA l.val
      (Nat.le_of_lt_succ l.isLt) t ht x
  have h := w.mulCoefficient_factorialNorm_le hC hp hb hρ.le
  rw [coefficientSeminorm_eq_sum_real_budget ρ hρ K a b A hA] at h
  exact h

end AVRegularity.CoupledEnergy.Galerkin
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Measurable matrix entries of bounded spatial coefficient forms. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] in
/-- Pairing a coefficient multiplier with a test is the literal spatial integral. -/
theorem boundedCoefficientL2_inner_eq_integral {U : Set (Vec 2)}
    (C : Vec 2 → E →L[ℝ] F) (hC : Continuous C) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ x, ‖C x‖ ≤ M) (u : Lp E 2 (volume.restrict U))
    (z : Lp F 2 (volume.restrict U)) :
    inner ℝ (boundedCoefficientL2 C hC M hM hb u) z =
      ∫ x, inner ℝ (C x (u x)) (z x) ∂volume.restrict U := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [boundedCoefficientL2_ae C hC M hM hb u] with x hx
  rw [hx]

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

omit [CompleteSpace E] [CompleteSpace F] in
/-- Joint measurability of a coefficient gives measurability of each weak matrix entry.
No time continuity or derivative of the coefficient is required. -/
theorem coefficientPairing_stronglyMeasurable {T : Type*} [MeasurableSpace T]
    {U : Set (Vec 2)} (C : T → Vec 2 → E →L[ℝ] F)
    (hC : Measurable (Function.uncurry C))
    (u : Lp E 2 (volume.restrict U)) (z : Lp F 2 (volume.restrict U)) :
    StronglyMeasurable (fun t => ∫ x, inner ℝ (C t x (u x)) (z x)
      ∂volume.restrict U) := by
  have hu : Measurable (fun p : T × Vec 2 => u p.2) :=
    (Lp.stronglyMeasurable u).measurable.comp measurable_snd
  have hz : Measurable (fun p : T × Vec 2 => z p.2) :=
    (Lp.stronglyMeasurable z).measurable.comp measurable_snd
  have heval : Measurable (fun p : T × Vec 2 => C p.1 p.2 (u p.2)) := by
    exact (continuous_fst.clm_apply continuous_snd).measurable.comp
      (hC.prodMk hu)
  exact (heval.inner hz).stronglyMeasurable.integral_prod_right'

end AVRegularity.CoupledEnergy.Galerkin
end
end
