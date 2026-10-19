-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MetricTaylorTimeCoefficient
public import AVRegularity.CycleEvolution.CellTimeMetricDriftCLM
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction
public import AVRegularity.EntryWeak.SourceParameterPeriodicity
import AVRegularity.CycleWords.PlaneScalarBlochSurjective
import AVRegularity.EntryWeak.JointSourceCongruence
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open AVRegularity.Sobolev AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open scoped AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! A finite invertible scalar system recovers the original coefficients in the native carrier. -/

theorem torusHigher_native_linear_system (K N : ℕ) (A B : Matrix (Fin N) (Fin N) ℂ)
    (hBA : B * A = 1) (c : Fin N → ComplexCellL2)
    (hex : ∀ j, ∃ U : TorusHk K ℂ, torusHkValueCLM U = ∑ i, A j i • c i) :
    ∀ i, ∃ U : TorusHk K ℂ, torusHkValueCLM U = c i := by
  classical
  choose U hU using hex
  intro i
  refine ⟨∑ j, B i j • U j, ?_⟩
  simp only [map_sum, torusHigher_complex_value_smul, hU, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  have he (l : Fin N) : ∑ j, B i j * A j l = if i = l then 1 else 0 := by
    have hh := congrArg (fun M : Matrix (Fin N) (Fin N) ℂ => M i l) hBA
    simpa only [Matrix.mul_apply, Matrix.one_apply] using hh
  simp only [he, ite_smul, one_smul, zero_smul]
  simp

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane
open AVRegularity.Analysis.Convolution AVRegularity.Weighted
open scoped Topology
namespace AVRegularity.CycleWords

/-! Distributional forcing measurability passes to all stored Sobolev words. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeProjectedJetSourcePair_aestronglyMeasurable {K : ℕ} {μ : Measure ℝ}
    (H : ℝ → PlaneHk Set.univ K E)
    (S : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (hweak : ∀ Z : PlaneHk Set.univ 1 E, AEStronglyMeasurable
      (fun t => inner ℝ (planeHkValueOperator K (H t)) (planeHkValueOperator 1 Z) -
        inner ℝ (planeFluxValueOperator K (S t)) (planeH1GradientOperator Z)) μ)
    (N : ℕ) (α : JetIndex2 K) (Z : PlaneHk Set.univ 1 E) :
    AEStronglyMeasurable (fun t => planeProjectedJetSourcePair N α (H t) (S t) Z) μ := by
  have hm := hweak (planeOrderedCutoffTest N α.2 Z)
  simp_rw [planeOrderedCutoffTest_value, planeHk_ordered_cutoff_test_pair,
    PiLp.inner_apply, planeFlux_ordered_cutoff_component_pair,
    ← Finset.mul_sum, ← mul_sub] at hm
  have hm' := hm.mul (aestronglyMeasurable_const (b := ((-1 : ℝ) ^ α.1.val)⁻¹))
  convert hm' using 1
  funext t
  dsimp only [planeProjectedJetSourcePair, Pi.mul_apply]
  field_simp


theorem planeJetSourcePair_tendsto {K : ℕ} (α : JetIndex2 K)
    (H : PlaneHk Set.univ K E)
    (S : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (Z : PlaneHk Set.univ 1 E) :
    Tendsto (fun N => planeProjectedJetSourcePair N α H S Z) atTop
      (𝓝 (planeJetSourcePair α H S Z)) := by
  exact ((tendsto_hilbertProjection (univToPlane (H.val α))).inner (𝕜 := ℝ)
    (tendsto_const_nhds (x := planeHkValueOperator 1 Z))).sub
    (tendsto_finsetSum Finset.univ (fun k _ =>
      (tendsto_hilbertProjection (univToPlane
        ((mapPlaneHk (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k) S).val α))).inner
        (𝕜 := ℝ) (tendsto_const_nhds (x := planeH1GradientOperator Z k))))

theorem planeJetSourceDual_aestronglyMeasurable {K : ℕ} {μ : Measure ℝ}
    (H : ℝ → PlaneHk Set.univ K E)
    (S : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (hweak : ∀ Z : PlaneHk Set.univ 1 E, AEStronglyMeasurable
      (fun t => inner ℝ (planeHkValueOperator K (H t)) (planeHkValueOperator 1 Z) -
        inner ℝ (planeFluxValueOperator K (S t)) (planeH1GradientOperator Z)) μ)
    (α : JetIndex2 K) :
    AEStronglyMeasurable (fun t => planeSourceDual
      (planeJetReadoutOperator K α (H t)) (planeJetFluxOperator K α (S t))) μ := by
  apply planeHk_time_aestronglyMeasurable_of_weak
  intro Z
  have hm := aestronglyMeasurable_of_tendsto_ae atTop
    (fun N => planeProjectedJetSourcePair_aestronglyMeasurable H S hweak N α Z)
    (Eventually.of_forall (fun t => planeJetSourcePair_tendsto α (H t) (S t) Z))
  have heq : (fun t => inner ℝ Z (planeSourceDual
      (planeJetReadoutOperator K α (H t)) (planeJetFluxOperator K α (S t)))) =
      (fun t => planeJetSourcePair α (H t) (S t) Z) := by
    funext t
    rw [real_inner_comm, planeSourceDual_pair]
    simp only [planeJetSourcePair, PiLp.inner_apply, planeJetReadoutOperator_apply,
      planeJetFluxOperator_apply]
  rw [heq]
  exact hm

end AVRegularity.CycleWords
end

section
open MeasureTheory UnitAddTorus AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Exact Fourier coefficients of native cell L2 data. -/

local instance scalarCellFourierCoefficientMeasure : MeasureSpace UnitAddCircle := instMeasureSpaceUnitAddCircle

theorem scalarCellToTorus_fourierCoeff_pair (f : ComplexCellL2) (n : Fin 2 → ℤ) :
    mFourierCoeff (scalarCellToTorus f) n =
      cellComplexPair f (scalarTorusToCell (mFourierLp 2 n)) := by
  rw [← mFourierBasis_repr, HilbertBasis.repr_apply_apply, coe_mFourierBasis,
    cellComplexPair_eq_inner]
  have hi := scalarTorusToCellComplex.inner_map_map (mFourierLp 2 n) (scalarCellToTorus f)
  simpa only [scalarTorusToCellComplex_eq, scalarTorusToCell_scalarCellToTorus] using hi.symm

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory UnitAddTorus AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Actual committed cell H1 carriers with exact value and derivative readouts from Fourier data. -/

local instance scalarTorusH1FourierCarrierMeasure : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

def scalarTorusH1OfFourier (u : ScalarTorusL2) (d : Fin 2 → ScalarTorusL2)
    (hd : ∀ i n, mFourierCoeff (d i) n =
      ((2 * (Real.pi : ℂ) * Complex.I) * (n i : ℂ)) * mFourierCoeff u n) : TorusHk 1 ℂ :=
  cellComplexH1RealEquiv ⟨scalarCellFirstJet u d, scalarCellFirstJet_mem_H1 u d hd⟩

theorem scalarTorusH1OfFourier_value (u : ScalarTorusL2) (d : Fin 2 → ScalarTorusL2)
    (hd : ∀ i n, mFourierCoeff (d i) n =
      ((2 * (Real.pi : ℂ) * Complex.I) * (n i : ℂ)) * mFourierCoeff u n) :
    torusHkValueCLM (scalarTorusH1OfFourier u d hd) = scalarTorusToCell u := by
  change scalarCellFirstJet u d (valueIndex2 1) = scalarTorusToCell u
  simp [scalarCellFirstJet, valueIndex2, valueIndex]

theorem scalarTorusH1OfFourier_derivative (u : ScalarTorusL2) (d : Fin 2 → ScalarTorusL2)
    (hd : ∀ i n, mFourierCoeff (d i) n =
      ((2 * (Real.pi : ℂ) * Complex.I) * (n i : ℂ)) * mFourierCoeff u n) (i : Fin 2) :
    cellDerivativeCLM i (scalarTorusH1OfFourier u d hd) = scalarTorusToCell (d i) := by
  change scalarCellFirstJet u d ⟨⟨1, by decide⟩, fun _ => i⟩ = scalarTorusToCell (d i)
  simp [scalarCellFirstJet]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The actual finite cell Fourier states have canonical continuous lifts at every spatial order. -/

def cellGalerkinHigherStateCLM (N q : ℕ) :
    CellGalerkinSpace (E := ℂ) N →L[ℝ] TorusHk (q + 1) ℂ :=
  rangeSmoothFourierLiftCLM (E := ℂ) (K := 1) (L := q + 1) (by omega) N

theorem cellGalerkinHigherStateCLM_truncate (N q : ℕ)
    (u : CellGalerkinSpace (E := ℂ) N) :
    truncateTorusHk (by omega : 1 ≤ q + 1) (cellGalerkinHigherStateCLM N q u) = u.val :=
  rangeSmoothFourierLift_truncate (by omega) N u

theorem cellGalerkinHigherStateCLM_value (N q : ℕ)
    (u : CellGalerkinSpace (E := ℂ) N) :
    torusHkValueCLM (cellGalerkinHigherStateCLM N q u) = cellGalerkinValue N u := by
  have h := cellGalerkinHigherStateCLM_truncate N q u
  exact congrArg (torusHkValueCLM (E := ℂ) (K := 1)) h

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! On quiet times the real shifted generator is the actual Hermitian diffusion form. -/

theorem cellDriftEntryCLM_at_quiet_time {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v) (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (t : ℝ) (hquiet : ∀ x, v t x = 0) (j : Fin 2) (u : ComplexCellL2) :
    cellDriftEntryCLM ⟨0, v, 0, 0⟩ V hv.1 hb t j u = 0 := by
  apply Lp.ext
  filter_upwards [cellDriftEntryCLM_ae ⟨0, v, 0, 0⟩ V hv.1 hb t j u,
    Lp.coeFn_zero (E := ℂ) (p := 2) (μ := volume.restrict AVenhance.unitCube)] with x hx hz
  rw [hx, hz]
  simp only [hquiet x, Pi.zero_apply, Complex.ofReal_zero, zero_mul]

theorem cellComplexShiftedDriftForm_at_quiet_time {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v) (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (θ : Fin 2 → ℂ) (t : ℝ) (hquiet : ∀ x, v t x = 0) (u z : TorusHk 1 ℂ) :
    cellComplexShiftedDriftForm v V hv hb θ t u z = 0 := by
  rw [cellComplexShiftedDriftForm_eq_sum]
  simp only [cellDriftEntryCLM_at_quiet_time hv V hb t hquiet,
    cellComplexPair_zero_left, Finset.sum_const_zero]

theorem cellComplexGenerator_at_quiet_time
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (θ : Fin 2 → ℂ) (t : ℝ) (hquiet : ∀ x, v t x = 0) (u z : TorusHk 1 ℂ) :
    cellComplexGenerator ⟨G, v, θ, 0⟩ hG V hv.1 hb t u z =
      cellComplexDiffusionForm hG θ t u z := by
  rw [cellComplexGenerator_decomposition _ hG V hv hb,
    cellComplexShiftedDriftForm_at_quiet_time hv V hb θ t hquiet]
  simp only [Pi.zero_apply, cellScalarCLM_smul, zero_smul, cellComplexPair_zero_left,
    sub_zero, add_zero]

theorem cellComplexGenerator_quiet_symmetry
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (θ : Fin 2 → ℂ) (hθ : ∀ j, star (θ j) = θ j)
    (t : ℝ) (hquiet : ∀ x, v t x = 0) (u z : TorusHk 1 ℂ) :
    cellComplexGenerator ⟨G, v, θ, 0⟩ hG V hv.1 hb t u z =
      star (cellComplexGenerator ⟨G, v, θ, 0⟩ hG V hv.1 hb t z u) := by
  rw [cellComplexGenerator_at_quiet_time hG hv V hb θ t hquiet,
    cellComplexGenerator_at_quiet_time hG hv V hb θ t hquiet,
    cellComplexDiffusionForm_adjoint]
  rw [show (fun j => star (θ j)) = θ from funext hθ]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The genuine Bloch unitary with values in the cell solver's L2 carrier. -/

def planeCellBlochTransform (a : Vec 2) (P : ℝ) (hP : 0 < P) :
    Lp ℂ 2 (volume : Measure (Vec 2)) →ₗᵢ[ℝ]
      Lp ComplexCellL2 2 (volume.restrict (planeFrequencyCell a P)) :=
  (liftLinearIsometryL2 (volume.restrict (planeFrequencyCell a P)) scalarTorusToCell).comp
    (planeScalarBlochTransform a P hP)

theorem planeCellBlochTransform_ae (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (f : Lp ℂ 2 (volume : Measure (Vec 2))) :
    ∀ᵐ θ ∂volume.restrict (planeFrequencyCell a P),
      planeCellBlochTransform a P hP f θ =
        scalarTorusToCell (planeScalarBlochTransform a P hP f θ) :=
  liftLinearIsometryL2_ae _ scalarTorusToCell _

theorem planeCellBlochTransform_surjective (a : Vec 2) (P : ℝ) (hP : 0 < P) :
    Function.Surjective (planeCellBlochTransform a P hP) :=
  (liftLinearIsometryL2_surjective _ scalarTorusToCell scalarTorusToCell_surjective).comp
    (planeScalarBlochTransform_surjective a P hP)

def planeCellBlochUnitary (a : Vec 2) (P : ℝ) (hP : 0 < P) :
    Lp ℂ 2 (volume : Measure (Vec 2)) ≃ₗᵢ[ℝ]
      Lp ComplexCellL2 2 (volume.restrict (planeFrequencyCell a P)) :=
  LinearIsometryEquiv.ofSurjective (planeCellBlochTransform a P hP)
    (planeCellBlochTransform_surjective a P hP)

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Spatially constant Bloch diffusion of an actual H2 state is a genuine native L2 field. -/

def cellConstantMetricStrongDiffusionCLM
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (θ : Fin 2 → ℂ) (t : ℝ) :
    TorusHk 2 ℂ →L[ℝ] ComplexCellL2 :=
  (∑ j : Fin 2, ∑ k : Fin 2, (cellScalarCLM (G t j k : ℂ)).comp
    ((cellDerivativeCLM k).comp (cellH2DerivativeH1CLM j))) +
  (∑ j : Fin 2, (cellScalarCLM (2 * Complex.I * ∑ k : Fin 2, (G t j k : ℂ) * θ k)).comp
    ((cellDerivativeCLM j).comp cellH2BaseCLM)) +
  (cellScalarCLM (-(∑ j : Fin 2, ∑ k : Fin 2, (G t j k : ℂ) * θ j * θ k))).comp
    (torusHkValueCLM.comp cellH2BaseCLM)

theorem cellConstantMetricStrongDiffusionCLM_pair
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (t : ℝ) (u : TorusHk 2 ℂ) (z : TorusHk 1 ℂ) :
    cellComplexDiffusionForm hG θ t (cellH2BaseCLM u) z =
      cellComplexPair (cellConstantMetricStrongDiffusionCLM G θ t u) (torusHkValueCLM z) := by
  rw [cellConstantMetric_bloch_expansion]
  simp only [cellConstantMetricStrongDiffusionCLM, add_apply,
    ContinuousLinearMap.comp_apply, Fin.sum_univ_two, cellComplexPair_add_left,
    cellComplexPair_scalar_left]
  simp_rw [cellH2_second_derivative_pair,
    cellComplexDerivative_skew _ (cellH2BaseCLM u) z]
  ring

/-! Higher lifts and all ordered derivatives stay in the original finite Fourier band. -/

theorem galerkinProj_truncate_commute {K L : ℕ} (hKL : K ≤ L) (N : ℕ)
    (u : TorusHk L ℂ) :
    truncateTorusHk hKL (galerkinProj N u) = galerkinProj N (truncateTorusHk hKL u) := by
  ext j
  simp only [truncateTorusHk_apply, galerkinProj_val, cellJetFourierProjection_apply]
  exact Filter.EventuallyEq.rfl

theorem rangeSmoothFourierLift_fixed {L : ℕ} (hL : 1 ≤ L) (N : ℕ)
    (u : CellGalerkinSpace (E := ℂ) N) :
    galerkinProj N (rangeSmoothFourierLiftCLM hL N u) = rangeSmoothFourierLiftCLM hL N u := by
  apply TorusHk.ext_value
  have he := congrArg (torusHkValueCLM (E := ℂ) (K := 1))
    (galerkinProj_truncate_commute hL N (rangeSmoothFourierLiftCLM hL N u))
  have ht : truncateTorusHk hL (rangeSmoothFourierLiftCLM hL N u) = u.val :=
    rangeSmoothFourierLift_truncate hL N u
  have hp : galerkinProj (E := ℂ) (K := 1) N u.val = u.val :=
    galerkinProj_fixed_of_range (E := ℂ) (K := 1) N u
  rw [ht, hp] at he
  exact he.trans (congrArg (torusHkValueCLM (E := ℂ) (K := 1)) ht).symm

end AVRegularity.CycleWords
end

section
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! A common frequency disc for the full gap and all spatial derivative orders. -/

def constructedScalarCommonRadius (Cw ρ : ℝ) : ℝ :=
  min (fibreCoefficientMajorantRadius Cw / 2048) (ρ / 4)

theorem constructedScalarCommonRadius_pos {Cw ρ : ℝ}
    (hCw : 0 ≤ Cw) (hρ : 0 < ρ) :
    0 < constructedScalarCommonRadius Cw ρ := by
  exact lt_min (div_pos (fibreCoefficientMajorantRadius_pos hCw) (by norm_num))
    (div_pos hρ (by norm_num))

theorem constructedScalarCommonDisc_bounds {Cw ρ : ℝ}
    (hCw : 0 ≤ Cw) (hρ : 0 < ρ) (ξ : Fin 2 → ℂ)
    (hξ : fibreNorm ξ ≤ constructedScalarCommonRadius Cw ρ) :
    fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 1024 ∧
    fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16 ∧
    ‖ξ‖ < ρ / 2 ∧
    (ρ / 2)⁻¹ * ‖ξ‖ < 1 ∧
    Cw * fibreNorm ξ + 1032 * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2 / 16 := by
  have hr := fibreCoefficientMajorantRadius_pos hCw
  have hsmall := hξ.trans (min_le_left _ _)
  have hhalf := hξ.trans (min_le_right _ _)
  have hgap : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 1024 := by
    linarith
  have hnorm : ‖ξ‖ < ρ / 2 := by
    have hn := (fibrePiNorm_le_fibreNorm ξ).trans hhalf
    linarith
  refine ⟨hgap, ?_, hnorm, ?_, fibreKernel_frequency_small hCw ξ hgap⟩
  · linarith
  · rw [inv_mul_lt_iff₀ (by positivity : 0 < ρ / 2)]
    simpa using hnorm

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Exact plane real Hilbert pairing through the actual cell Bloch transform. -/

theorem planeCellBloch_inverse_inner (a : Vec 2)
    (F G : Lp ComplexCellL2 2 (volume.restrict (planeFrequencyCell a 1))) :
    inner ℝ ((planeCellBlochUnitary a 1 (by norm_num)).symm F)
      ((planeCellBlochUnitary a 1 (by norm_num)).symm G) = inner ℝ F G :=
  (planeCellBlochUnitary a 1 (by norm_num)).symm.inner_map_map F G

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory UnitAddTorus AVRegularity.Sobolev
open AVenhance.Infra.Torus AVRegularity.CycleEvolution
open scoped ENNReal Classical
namespace AVRegularity.CycleWords

/-! The genuine norm-one transverse Fourier projection preserves the actual cell H¹ graph. -/

local instance scalarTorusTransverseProjectionMeasure : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

def scalarTorusTransverseProjection (e : Fin 2) : ScalarTorusL2 →L[ℂ] ScalarTorusL2 :=
  hilbertBasisSectorProjection (mFourierBasis (d := Fin 2)) {n | n e = 0}

theorem scalarTorusTransverseProjection_fourierCoeff (e : Fin 2) (u : ScalarTorusL2)
    (n : Fin 2 → ℤ) :
    mFourierCoeff (scalarTorusTransverseProjection e u) n =
      if n e = 0 then mFourierCoeff u n else 0 := by
  simpa only [scalarTorusTransverseProjection, Set.mem_ofPred_eq, mFourierBasis_repr] using
    hilbertBasisSectorProjection_repr (mFourierBasis (d := Fin 2)) {n | n e = 0} u n

theorem scalarTorusTransverseProjection_norm_le (e : Fin 2) (u : ScalarTorusL2) :
    ‖scalarTorusTransverseProjection e u‖ ≤ ‖u‖ :=
  hilbertBasisSectorProjection_norm_le _ _ u

theorem scalarTorusTransverseProjection_eq_self (e : Fin 2) (u : ScalarTorusL2)
    (hu : ∀ n : Fin 2 → ℤ, n e ≠ 0 → mFourierCoeff u n = 0) :
    scalarTorusTransverseProjection e u = u := by
  apply hilbertBasisSectorProjection_eq_self
  intro n hn
  rw [mFourierBasis_repr]
  exact hu n hn

theorem scalarTorusTransverseProjection_derivative_coeff
    (e i : Fin 2) (u v : ScalarTorusL2)
    (huv : ∀ n : Fin 2 → ℤ, mFourierCoeff v n =
      (2 * (Real.pi : ℂ) * Complex.I) * (n i : ℂ) * mFourierCoeff u n)
    (n : Fin 2 → ℤ) :
    mFourierCoeff (scalarTorusTransverseProjection e v) n =
      (2 * (Real.pi : ℂ) * Complex.I) * (n i : ℂ) *
        mFourierCoeff (scalarTorusTransverseProjection e u) n := by
  rw [scalarTorusTransverseProjection_fourierCoeff, scalarTorusTransverseProjection_fourierCoeff]
  split_ifs
  · exact huv n
  · exact (mul_zero _).symm

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleComparison.Lift AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Nonempty ordered weak derivatives of the actual constant torus state vanish. -/

theorem torusHigherConstant_derivative {K r : ℕ} (w : DerivativeWord2 r) (hr : 0 < r) (c : ℂ) :
    derivativeTorusHk (K := K) w (torusHigherConstant (K + r) c) = 0 := by
  apply TorusHk.ext_value
  change torusHkValueCLM (derivativeTorusHk w (torusHigherConstant (K + r) c)) = (torusHkValueCLM (E := ℂ) (K := K)) 0
  rw [map_zero]
  apply Lp.ext
  have hi : prefixJetIndex w (valueIndex2 K) =
      (⟨⟨r, by omega⟩, w⟩ : JetIndex2 (K + r)) := by
    simp only [prefixJetIndex, valueIndex2, valueIndex, Fin.val_zero, Nat.add_zero, Fin.append_elim0]
    rfl
  have ha := finiteSmoothPeriodicHk_jet_ae (K + r) (fun _ => c) contDiff_const
    (fun _ _ => rfl) (⟨⟨r, by omega⟩, w⟩ : JetIndex2 (K + r))
  rw [orderedDerivative_const w c hr] at ha
  change ((torusHigherConstant (K + r) c).val (prefixJetIndex w (valueIndex2 K)) : Vec 2 → ℂ) =ᵐ[_] _
  rw [hi]
  exact ha.trans (Lp.coeFn_zero ℂ 2 (volume.restrict AVenhance.unitCube)).symm

end AVRegularity.CycleWords
end

section
open AVRegularity.Sobolev AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Every canonical higher Fourier lift has the same original native value and truncations. -/

theorem cellGalerkinRangeHigher_value {L : ℕ} (hL : 1 ≤ L) (N : ℕ)
    (u : CellGalerkinSpace (E := ℂ) N) :
    torusHkValueCLM (rangeSmoothFourierLiftCLM hL N u) = cellGalerkinValue N u := by
  exact congrArg (torusHkValueCLM (E := ℂ) (K := 1))
    (rangeSmoothFourierLift_truncate hL N u)

theorem cellGalerkinRangeHigher_truncate {K L : ℕ} (hK : 1 ≤ K) (hL : 1 ≤ L)
    (hKL : K ≤ L) (N : ℕ) (u : CellGalerkinSpace (E := ℂ) N) :
    truncateTorusHk hKL (rangeSmoothFourierLiftCLM hL N u) = rangeSmoothFourierLiftCLM hK N u := by
  apply TorusHk.ext_value
  change torusHkValueCLM (rangeSmoothFourierLiftCLM hL N u) =
    torusHkValueCLM (rangeSmoothFourierLiftCLM hK N u)
  rw [cellGalerkinRangeHigher_value, cellGalerkinRangeHigher_value]

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Projecting an actual higher source commutes with its retained native lift and ordered derivatives. -/

theorem cellGalerkinL2Initial_higher_lift {L : ℕ} (hL : 1 ≤ L) (N : ℕ) (Y : TorusHk L ℂ) :
    rangeSmoothFourierLiftCLM hL N (cellGalerkinL2Initial N (torusHkValueCLM Y)) = galerkinProj N Y := by
  apply TorusHk.ext_value
  have ht : truncateTorusHk hL (rangeSmoothFourierLiftCLM hL N
      (cellGalerkinL2Initial N (torusHkValueCLM Y))) =
        (cellGalerkinL2Initial N (torusHkValueCLM Y)).val :=
    rangeSmoothFourierLift_truncate hL N _
  have hv := congrArg (torusHkValueCLM (E := ℂ) (K := 1)) ht
  change torusHkValueCLM (rangeSmoothFourierLiftCLM hL N
    (cellGalerkinL2Initial N (torusHkValueCLM Y))) =
    cellGalerkinValue N (cellGalerkinL2Initial N (torusHkValueCLM Y)) at hv
  exact hv.trans (by
    rw [cellGalerkinL2Initial_eq_fourier, cellL2FourierState_value]
    rfl)

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The inverse cell Bloch transform is the actual torus transfer followed by reconstruction. -/

theorem planeCellBlochUnitary_symm_apply (a : Vec 2)
    (F : Lp ComplexCellL2 2 (volume.restrict (planeFrequencyCell a 1))) :
    (planeCellBlochUnitary a 1 (by norm_num)).symm F =
      planeScalarBlochReconstruct a 1 (by norm_num)
        (scalarCellToTorusField (volume.restrict (planeFrequencyCell a 1)) F) := by
  apply (planeCellBlochUnitary a 1 (by norm_num)).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  change F = liftLinearIsometryL2 (volume.restrict (planeFrequencyCell a 1)) scalarTorusToCell
    (planeScalarBlochTransform a 1 (by norm_num)
      (planeScalarBlochReconstruct a 1 (by norm_num) _))
  rw [planeScalarBlochTransform_reconstruct, scalarCellToTorusField_inverse]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! Native linear correction bounds persist through a bounded reciprocal normalization. -/

theorem torusHigher_normalized_correction_norm_le (J : ℕ) (η δ B D : ℝ)
    (hδ : 0 ≤ δ) (hD : 0 ≤ D)
    (U : TorusHk J ℂ) (hU : ‖U‖ ≤ B * peFactor η ^ J * δ)
    (c : ℂ) (hc : ‖c‖ ≤ 2) (hcm : ‖c - 1‖ ≤ D * δ) :
    ‖c • U + (c - 1) • torusHigherConstant J 1‖ ≤
      (2 * B + D * ‖torusHigherConstant J 1‖) * peFactor η ^ J * δ := by
  have hprice := mul_le_mul_of_nonneg_left (one_le_peFactor_pow η J)
    (mul_nonneg hD (norm_nonneg (torusHigherConstant J 1)))
  calc
    _ ≤ ‖c • U‖ + ‖(c - 1) • torusHigherConstant J 1‖ := norm_add_le _ _
    _ = ‖c‖ * ‖U‖ + ‖c - 1‖ * ‖torusHigherConstant J 1‖ := by rw [norm_smul, norm_smul]
    _ ≤ 2 * (B * peFactor η ^ J * δ) + (D * δ) * ‖torusHigherConstant J 1‖ :=
      add_le_add (mul_le_mul hc hU (norm_nonneg _) (by norm_num))
        (mul_le_mul_of_nonneg_right hcm (norm_nonneg _))
    _ ≤ 2 * (B * peFactor η ^ J * δ) +
        (D * ‖torusHigherConstant J 1‖ * peFactor η ^ J) * δ := by
      apply add_le_add le_rfl
      have hh := mul_le_mul_of_nonneg_right hprice hδ
      simpa only [mul_one] using (show (D * δ) * ‖torusHigherConstant J 1‖ ≤
        (D * ‖torusHigherConstant J 1‖ * peFactor η ^ J) * δ from by
          calc
            _ = (D * ‖torusHigherConstant J 1‖) * δ := by ring
            _ ≤ _ := by simpa only [mul_one] using hh)
    _ = _ := by ring

end AVRegularity.CycleWords
end

section
open MeasureTheory Homogenization AVRegularity.Weighted
namespace AVRegularity.CycleWords

/-! Compact tests only decrease the positive value-commutator budget. -/

variable {E : Type*} [NormedAddCommGroup E]

theorem cutoff_weighted_value_product_le
    (q χ : Vec 2 → ℝ) (hq : Continuous q) (hχ : Continuous χ)
    (hq0 : ∀ x, 0 ≤ q x) (B : ℝ) (hqb : ∀ x, |q x| ≤ B)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (R U : Lp E 2 (volume : Measure (Vec 2))) :
    (∫ x, χ x ^ 2 * q x * (‖R x‖ * ‖U x‖)) ≤
      ∫ x, q x * (‖R x‖ * ‖U x‖) := by
  have hχsq x : χ x ^ 2 ≤ 1 := by nlinarith [hχ0 x, hχ1 x]
  have hbound x : |χ x ^ 2 * q x| ≤ B := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    exact (mul_le_mul (hχsq x) (hqb x) (abs_nonneg _) (by norm_num)).trans_eq (one_mul B)
  apply integral_mono
    (bounded_weight_value_product_integrable R U (fun x => χ x ^ 2 * q x)
      ((hχ.pow 2).mul hq).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hbound x)))
    (bounded_weight_value_product_integrable R U q hq.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hqb x)))
  intro x
  have hqχ : χ x ^ 2 * q x ≤ q x := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hχsq x) (hq0 x)
  exact mul_le_mul_of_nonneg_right hqχ (mul_nonneg (norm_nonneg _) (norm_nonneg _))

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Actual sampled original flux coefficients retain their positive molecular price. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem familyMolecular_ae_sample_budget (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (dom : F.Domain)
    (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ)
    (henv : IsMolecularEnvelope F π K dom ν e E ρ C J b₀)
    (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0) (d : ℕ)
    (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder)
    (I : DerivativeWord2 (d - 1)) (p : P) (c : Ctx p) :
    ∀ᵐ t ∂volume, (∀ Y : Vec 2, (t, Y) ∈ dom p c) →
      ∀ X0 φ j, j ≤ K v → ∀ z,
      (ρ / e) ^ j * ‖iteratedFDeriv ℝ j (fun y =>
        F.flux p c v u γ d I t (X0 + (e / E) • y) (y + φ)) z‖ ≤
        (4 : ℝ) ^ Kmax * (Kmax.factorial : ℝ) ^ 2 *
          molecularRealPrice ν ρ (K v) (d - 2)
            (molecularJet ρ e (K v) 0 (fun x : F.Index => dom x.1 x.2)
              (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)) /
                derivativeReserveFactor (ρ / e) (K v) (d - 2) := by
  filter_upwards [familyMolecular_ae_uniform_reserve F π hπ K Kmax hK dom ν e E ρ
    hν he hE hρ C J b₀ henv v u γ hγ d hd I 0 (Nat.zero_le J) p c] with t ht
  intro hdom X0 φ j hj z
  let M := molecularRealPrice ν ρ (K v) (d - 2)
    (molecularJet ρ e (K v) 0 (fun x : F.Index => dom x.1 x.2)
      (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I))
  let R := derivativeReserveFactor (ρ / e) (K v) (d - 2)
  have hR : 0 < R := by dsimp [R, derivativeReserveFactor]; positivity
  have hM : 0 ≤ M := molecularRealPrice_nonneg ν ρ hν.le hρ.le _ _ _
  have hf : ContDiff ℝ (K v : ℕ) (Function.uncurry (F.flux p c v u γ d I t)) :=
    (molecular_joint_contDiff F dom E hE.ne' (fun v => K v + J)
      henv.1 p c t hdom v u γ d I).of_le (by exact_mod_cast Nat.le_add_right (K v) J)
  have hb (a b : ℕ) (hab : a + b ≤ K v) (X z : Vec 2) :
      (ρ / e) ^ (a + b) * |e / E| ^ a *
        ‖iteratedFDeriv ℝ a (fun X' => iteratedFDeriv ℝ b
          (F.flux p c v u γ d I t X') z) X‖ ≤ (Kmax.factorial : ℝ) ^ 2 * M / R := by
    apply (le_div_iff₀ hR).mpr
    have hh := ht hdom a b hab X z
    rw [Nat.zero_add] at hh
    simpa only [pow_zero, mul_one, abs_of_pos (div_pos he hE), M, R] using hh
  have hh := jointSample_normalized_jet_le hf (ρ / e) (e / E)
    ((Kmax.factorial : ℝ) ^ 2 * M / R) (div_pos hρ he).le (by positivity) hb X0 φ j hj z
  apply hh.trans
  have hs := mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) (hK v))
    (show 0 ≤ (Kmax.factorial : ℝ) ^ 2 * M / R by positivity)
  simpa only [mul_div_assoc, mul_assoc, M, R] using hs

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Literal flux lower integrals suffice for square integrability of measurable stored-word duals. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeJetSourceDual_memLp_of_measurable_lower_integral {K : ℕ} {μ : Measure ℝ}
    (H : ℝ → PlaneHk Set.univ K E)
    (Q F S : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (hH : MemLp H 2 μ) (hQ : MemLp Q 2 μ)
    (hF : (∫⁻ t, ENNReal.ofReal (‖F t‖ ^ 2) ∂μ) < ⊤)
    (hsplit : ∀ t, S t = Q t + F t)
    (α : JetIndex2 K)
    (hm : AEStronglyMeasurable (fun t => planeSourceDual (planeJetReadoutOperator K α (H t))
      (planeJetFluxOperator K α (S t))) μ) :
    MemLp (fun t => planeSourceDual (planeJetReadoutOperator K α (H t))
      (planeJetFluxOperator K α (S t))) 2 μ := by
  let A : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)) →L[ℝ]
      PlaneHk Set.univ 1 E :=
    (planeH1GradientOperator (E := E)).adjoint.comp (planeJetFluxOperator K α)
  have hu := planeJetSourceDual_memLp H Q hH hQ α
  apply memLp_two_of_measurable_linear_majorant μ _ hm _ hu F hF
    1 ‖A‖ (by norm_num) (norm_nonneg A)
  intro t
  have heq : planeSourceDual (planeJetReadoutOperator K α (H t))
      (planeJetFluxOperator K α (S t)) =
      planeSourceDual (planeJetReadoutOperator K α (H t))
        (planeJetFluxOperator K α (Q t)) - A (F t) := by
    rw [hsplit t]
    simp only [planeSourceDual, map_add, ContinuousLinearMap.comp_apply, A]
    abel
  rw [heq, one_mul]
  exact (norm_sub_le _ _).trans (add_le_add (le_refl _) (A.le_opNorm (F t)))

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory
open AVRegularity.CoupledEnergyPlane
namespace AVRegularity.CycleWords

/-! The measurable periodic drift multiplier has its literal real plane readout. -/

theorem planeRealDriftReadout (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v)
    (t : ℝ) (i : Fin 2) (C : ℝ)
    (hC : ∀ z, ‖cellDriftTorusSymbol v t i z‖ ≤ C)
    (f : Lp ℂ 2 (volume : Measure (Vec 2))) :
    planeComplexRealPartL2
      (planeMeasurableTorusSymbolMultiplication (cellDriftTorusSymbol v t i)
        (cellDriftTorusSymbol_measurable v hv t i) C hC f) =ᵐ[volume]
      fun x => v t x i * (planeComplexRealPartL2 f x) := by
  let op := planeMeasurableTorusSymbolMultiplication (cellDriftTorusSymbol v t i)
    (cellDriftTorusSymbol_measurable v hv t i) C hC
  have hm := L2Multiplier.operator_ae
    (fun x => cellDriftTorusSymbol v t i (AVRegularity.Analysis.Convolution.torusQuotient x))
    (measurableTorusSymbol_plane_memLp_top _ (cellDriftTorusSymbol_measurable v hv t i) C hC) f
  filter_upwards [Complex.reCLM.coeFn_compLpL (op f), hm,
    Complex.reCLM.coeFn_compLpL f] with x hr hm hf
  change planeComplexRealPartL2 (op f) x = (op f x).re at hr
  change op f x = _ at hm
  change planeComplexRealPartL2 f x = (f x).re at hf
  rw [hr, hm, hf, cellDriftTorusSymbol_plane v hv t i x]
  simp

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Filter AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped Topology
namespace AVRegularity.CycleWords

/-! Arbitrary existing plane Sobolev data admit a native pullback through a bounded smooth renewal. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeSobolev_pullback_sequence_limit {K : ℕ} (U : PlaneHk Set.univ K E)
    (UN : ℕ → PlaneHk Set.univ K E) (fN : ℕ → Vec 2 → E)
    (ht : Tendsto UN atTop (𝓝 U)) (hs : ∀ N, ContDiff ℝ (⊤ : ℕ∞) (fN N))
    (hv : ∀ N, planeValue (UN N) =ᵐ[volume] fN N)
    (X : Vec 2 → Vec 2) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hμ : MeasurePreserving X volume volume) (B : ℕ → ℝ)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ z, ‖iteratedFDeriv ℝ j X z‖ ≤ B j) :
    ∃ V : PlaneHk Set.univ K E,
      Tendsto (fun N => smoothPlanePullback (UN N) (fN N) (hs N) (hv N) X hX hμ B hb)
        atTop (𝓝 V) ∧ planeValue V =ᵐ[volume] planeValue U ∘ X ∧
      ‖V‖ ≤ smoothPullbackNormBound B K * ‖U‖ := by
  let VN N := smoothPlanePullback (UN N) (fN N) (hs N) (hv N) X hX hμ B hb
  have hc : CauchySeq VN := cauchySeq_of_norm_sub_le UN VN (smoothPullbackNormBound B K)
    ht.cauchySeq (fun N M => smoothPlanePullback_sub_norm_le (UN N) (UN M)
      (fN N) (fN M) (hs N) (hs M) (hv N) (hv M) X hX hμ B hb)
  obtain ⟨V, hV⟩ := cauchySeq_tendsto_of_complete hc
  let A := planeHkValueOperator (E := E) K
  have heN N : A (VN N) = Lp.compMeasurePreserving X hμ (A (UN N)) := by
    apply planeValueLp_transport_eq
    exact (smoothPlanePullback_value_ae (UN N) (fN N) (hs N) (hv N) X hX hμ B hb).trans
      (hμ.quasiMeasurePreserving.ae_eq_comp (hv N)).symm
  have hl : Tendsto (fun N => A (VN N)) atTop (𝓝 (A V)) :=
    (A.continuous.tendsto V).comp hV
  have hr : Tendsto (fun N => Lp.compMeasurePreserving X hμ (A (UN N))) atTop
      (𝓝 (Lp.compMeasurePreserving X hμ (A U))) :=
    ((Lp.compMeasurePreservingₗᵢ ℝ X hμ).continuous.tendsto (A U)).comp
      ((A.continuous.tendsto U).comp ht)
  have he : A V = Lp.compMeasurePreserving X hμ (A U) :=
    tendsto_nhds_unique hl (hr.congr (fun N => (heN N).symm))
  refine ⟨V, hV, ?_, ?_⟩
  · have hv' : planeValue V =ᵐ[volume] (Lp.compMeasurePreserving X hμ (A U) : Vec 2 → E) := by
      rw [← he]
      exact (planeValueLp_ae V).symm
    exact hv'.trans ((Lp.coeFn_compMeasurePreserving (A U) hμ).trans
      (hμ.quasiMeasurePreserving.ae_eq_comp (planeValueLp_ae U)))
  · apply le_of_tendsto_of_tendsto hV.norm (tendsto_const_nhds.mul ht.norm)
    exact Filter.Eventually.of_forall (fun N =>
      smoothPlanePullback_norm_le (UN N) (fN N) (hs N) (hv N) X hX hμ B hb)

end AVRegularity.CycleWords
end

section
open AVRegularity.Sobolev AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open scoped AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! Homogeneous native values recover each literal bivariate coefficient through a finite Vandermonde system. -/

theorem torusHigher_native_bivariate_coefficients (K n : ℕ) (c : ℕ × ℕ → ComplexCellL2)
    (hex : ∀ ξ : Fin 2 → ℂ, ∃ U : TorusHk K ℂ,
      torusHkValueCLM U = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, fibreMonomial ξ p • c p) :
    ∀ i : Fin (n + 1), ∃ U : TorusHk K ℂ, torusHkValueCLM U = c (i.val, n - i.val) := by
  classical
  let A := Matrix.vandermonde (fun j : Fin (n + 1) => (j.val : ℂ))
  have hinj : Function.Injective (fun j : Fin (n + 1) => (j.val : ℂ)) := by
    intro i j h
    exact Fin.ext (Nat.cast_injective h)
  have hdet : IsUnit A.det := isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hinj)
  apply torusHigher_native_linear_system K (n + 1) A A⁻¹ (Matrix.nonsing_inv_mul A hdet)
    (fun i => c (i.val, n - i.val))
  intro j
  let ξ : Fin 2 → ℂ := fun i => if i = 0 then (j.val : ℂ) else 1
  obtain ⟨U, hU⟩ := hex ξ
  refine ⟨U, hU.trans ?_⟩
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  simp only [fibreMonomial, ξ, ite_eq_left rfl, show (1 : Fin 2) ≠ 0 by decide,
    ite_false, one_pow, mul_one, A, Matrix.vandermonde_apply]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory UnitAddTorus AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The transverse sector projection on the committed cell L² carrier. -/

local instance cellTransverseProjectionMeasure : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

def cellTransverseProjection (e : Fin 2) : ComplexCellL2 →L[ℝ] ComplexCellL2 :=
  scalarTorusCellUnitary.toLinearIsometry.toContinuousLinearMap.comp
    (((scalarTorusTransverseProjection e).restrictScalars ℝ).comp
      scalarTorusCellUnitary.symm.toLinearIsometry.toContinuousLinearMap)

theorem cellTransverseProjection_torus (e : Fin 2) (u : ScalarTorusL2) :
    cellTransverseProjection e (scalarTorusToCell u) =
      scalarTorusToCell (scalarTorusTransverseProjection e u) := by
  change scalarTorusCellUnitary
    (scalarTorusTransverseProjection e (scalarTorusCellUnitary.symm (scalarTorusCellUnitary u))) = _
  rw [scalarTorusCellUnitary.symm_apply_apply]
  rfl

theorem cellTransverseProjection_apply (e : Fin 2) (u : ComplexCellL2) :
    cellTransverseProjection e u =
      scalarTorusToCell (scalarTorusTransverseProjection e (scalarCellToTorus u)) := by
  change scalarTorusToCell (scalarTorusTransverseProjection e (scalarTorusCellUnitary.symm u)) = _
  rw [scalarTorusCellUnitary_symm_apply]

theorem cellTransverseProjection_norm_le (e : Fin 2) (u : ComplexCellL2) :
    ‖cellTransverseProjection e u‖ ≤ ‖u‖ := by
  change ‖scalarTorusCellUnitary
    (scalarTorusTransverseProjection e (scalarTorusCellUnitary.symm u))‖ ≤ ‖u‖
  rw [scalarTorusCellUnitary.norm_map]
  exact (scalarTorusTransverseProjection_norm_le e _).trans_eq
    (scalarTorusCellUnitary.symm.norm_map u)

theorem cellTransverseProjection_idempotent (e : Fin 2) (u : ComplexCellL2) :
    cellTransverseProjection e (cellTransverseProjection e u) = cellTransverseProjection e u := by
  rw [cellTransverseProjection_apply e u, cellTransverseProjection_torus]
  congr 1
  exact hilbertBasisSectorProjection_idempotent _ _ _

end AVRegularity.CycleWords
end

section
open MeasureTheory Homogenization AVRegularity.Weighted
namespace AVRegularity.CycleWords

/-! Compact value commutators are bounded by the full factorial word budget. -/

variable {E : Type*} [NormedAddCommGroup E]

theorem cutoff_weighted_value_word_sum_le {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (q χ : Vec 2 → ℝ) (hq : Continuous q) (hχ : Continuous χ)
    (hq0 : ∀ x, 0 ≤ q x) (B : ℝ) (hqb : ∀ x, |q x| ≤ B)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (R U : ι → Lp E 2 (volume : Measure (Vec 2))) :
    (∑ i, c i * (∫ x, χ x ^ 2 * q x * (‖R i x‖ * ‖U i x‖))) ≤
      ∑ i, c i * (∫ x, q x * (‖R i x‖ * ‖U i x‖)) := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left
    (cutoff_weighted_value_product_le q χ hq hχ hq0 B hqb hχ0 hχ1 (R i) (U i)) (hc i)

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! A genuine real continuous L2 multiplier for the bounded measurable periodic velocity. -/

def planeRealDriftMultiplier (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v)
    (t : ℝ) (i : Fin 2) (C : ℝ)
    (hC : ∀ z, ‖cellDriftTorusSymbol v t i z‖ ≤ C) :
    Lp ℝ 2 (volume : Measure (Vec 2)) →L[ℝ] Lp ℝ 2 (volume : Measure (Vec 2)) :=
  planeComplexRealPartL2.comp
    (((planeMeasurableTorusSymbolMultiplication (cellDriftTorusSymbol v t i)
      (cellDriftTorusSymbol_measurable v hv t i) C hC).restrictScalars ℝ).comp (ofRealL2 volume))

theorem planeRealDriftMultiplier_ae (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v)
    (t : ℝ) (i : Fin 2) (C : ℝ)
    (hC : ∀ z, ‖cellDriftTorusSymbol v t i z‖ ≤ C)
    (f : Lp ℝ 2 (volume : Measure (Vec 2))) :
    planeRealDriftMultiplier v hv t i C hC f =ᵐ[volume] fun x => v t x i * f x := by
  have h := planeRealDriftReadout v hv t i C hC (ofRealL2 volume f)
  change planeRealDriftMultiplier v hv t i C hC f =ᵐ[volume]
    fun x => v t x i * reL2 volume (ofRealL2 volume f) x at h
  simpa only [reL2_ofRealL2] using h

theorem planeRealDriftMultiplier_realPart (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v)
    (t : ℝ) (i : Fin 2) (C : ℝ)
    (hC : ∀ z, ‖cellDriftTorusSymbol v t i z‖ ≤ C)
    (f : Lp ℂ 2 (volume : Measure (Vec 2))) :
    planeComplexRealPartL2
      (planeMeasurableTorusSymbolMultiplication (cellDriftTorusSymbol v t i)
        (cellDriftTorusSymbol_measurable v hv t i) C hC f) =
      planeRealDriftMultiplier v hv t i C hC (planeComplexRealPartL2 f) := by
  apply Lp.ext
  exact (planeRealDriftReadout v hv t i C hC f).trans
    (planeRealDriftMultiplier_ae v hv t i C hC (planeComplexRealPartL2 f)).symm

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.EntryWeakProofs
open AVRegularity.CoupledEnergy.Variational AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Real and imaginary canonical Fourier lifts give a classical representative of a native complex value. -/

def torusHigherClassicalValue (K : ℕ) (U : TorusHk K ℂ) : Vec 2 → ℂ :=
  fun x => (realClassicalLift K (mapTorusHk Complex.reCLM U) x : ℂ) +
    Complex.I * (realClassicalLift K (mapTorusHk Complex.imCLM U) x : ℂ)

theorem torusHigherClassicalValue_contDiff (K n : ℕ) (hn : n + 2 ≤ K) (U : TorusHk K ℂ) :
    ContDiff ℝ (n : ℕ∞) (torusHigherClassicalValue K U) := by
  exact ((Complex.ofRealCLM.contDiff.comp (realClassicalLift_contDiff K n hn _)).add
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (realClassicalLift_contDiff K n hn _))))

theorem torusHigherClassicalValue_periodic (K : ℕ) (U : TorusHk K ℂ) :
    AVenhance.IsZ2Periodic (torusHigherClassicalValue K U) := by
  intro m x
  unfold torusHigherClassicalValue
  rw [realClassicalLift_periodic K _ m x, realClassicalLift_periodic K _ m x]

theorem torusHigherClassicalValue_ae (K : ℕ) (hK : 2 ≤ K) (U : TorusHk K ℂ) :
    torusHigherClassicalValue K U =ᵐ[volume.restrict AVenhance.unitCube]
      (torusHkValueCLM U : Vec 2 → ℂ) := by
  have hr := realClassicalLift_value_ae K hK (mapTorusHk Complex.reCLM U)
  have hi := realClassicalLift_value_ae K hK (mapTorusHk Complex.imCLM U)
  have hrv := mapTorusHk_jet_ae Complex.reCLM U (valueIndex2 K)
  have hiv := mapTorusHk_jet_ae Complex.imCLM U (valueIndex2 K)
  filter_upwards [hr, hi, hrv, hiv] with x hx hy hxr hxi
  change (realClassicalLift K (mapTorusHk Complex.reCLM U) x : ℂ) +
    Complex.I * (realClassicalLift K (mapTorusHk Complex.imCLM U) x : ℂ) = _
  rw [hx, hy, hxr, hxi]
  exact Complex.ext (by simp; rfl) (by simp; rfl)

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Literal cell differences have exactly the norm of their genuine Hilbert trace difference. -/

theorem cellL2Norm_difference_of_raw_traces (D E : ℝ → RawJet2 1 ℂ) (t : ℝ)
    (hD : MemLp (cellValue D t) 2 (volume.restrict AVenhance.unitCube))
    (hE : MemLp (cellValue E t) 2 (volume.restrict AVenhance.unitCube)) :
    cellL2Norm (fun x => cellValue D t x - cellValue E t x) =
      ENNReal.ofReal ‖cellRawTrace D t - cellRawTrace E t‖ := by
  apply cellL2Norm_eq_of_class
  exact (Lp.coeFn_sub _ _).trans ((cellRawTrace_ae D t hD).sub (cellRawTrace_ae E t hE))

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleWords

/-! Actual drift multipliers depend on the velocity at the consumed time alone. -/

theorem planeRealDriftMultiplier_congr_time
    (v v' : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (hv' : IsCellDrift v')
    (t t' : ℝ) (ht : v t = v' t') (i : Fin 2) (C C' : ℝ)
    (hC : ∀ z, ‖cellDriftTorusSymbol v t i z‖ ≤ C)
    (hC' : ∀ z, ‖cellDriftTorusSymbol v' t' i z‖ ≤ C')
    (f : Lp ℝ 2 (volume : Measure (Vec 2))) :
    planeRealDriftMultiplier v hv t i C hC f =
      planeRealDriftMultiplier v' hv' t' i C' hC' f := by
  apply Lp.ext
  exact (planeRealDriftMultiplier_ae v hv t i C hC f).trans
    (by simpa only [ht] using (planeRealDriftMultiplier_ae v' hv' t' i C' hC' f).symm)

end AVRegularity.CycleWords
end
