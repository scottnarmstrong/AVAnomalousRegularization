-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.PlaneBlochH1Measurable
public import AVRegularity.CycleEvolution.CellEnergySeriesRegularity
import AVRegularity.CycleComparison.Residual.CoarseFluxDiff.SlowJet
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

@[expose] public noncomputable section

section
open Homogenization MeasureTheory UnitAddTorus AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! The actual centered Bloch H1 field belongs to L2 in frequency. -/

local instance centeredPlaneBlochH1L2Measure : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

def centeredPlaneFrequencyBase : Vec 2 := fun _ => -(1 / 2 : ℝ)

abbrev centeredPlaneFrequencyMeasure : Measure (Vec 2) :=
  volume.restrict (planeFrequencyCell centeredPlaneFrequencyBase 1)

theorem centeredPlaneFrequency_coordinate_bound (i : Fin 2) :
    ∀ᵐ θ ∂centeredPlaneFrequencyMeasure, |θ i| ≤ 1 := by
  filter_upwards [ae_restrict_mem (planeFrequencyCell_measurable centeredPlaneFrequencyBase 1)]
    with θ hθ
  have hi := hθ i
  change -(1 / 2 : ℝ) < θ i ∧ θ i ≤ -(1 / 2 : ℝ) + 1 at hi
  rw [abs_le]
  constructor <;> linarith

theorem centeredPlaneBlochDerivative_memLp
    (u v : Lp ScalarTorusL2 2 centeredPlaneFrequencyMeasure) (i : Fin 2) :
    MemLp (fun θ => planeBlochCellDerivative θ i (u θ) (v θ)) 2
      centeredPlaneFrequencyMeasure := by
  have hC : 0 ≤ 2 * Real.pi := by positivity
  have hc : Continuous (fun θ : Vec 2 => (2 * (Real.pi : ℂ) * Complex.I) * (θ i : ℂ)) := by
    fun_prop
  have hsmul : MemLp (fun θ => ((2 * (Real.pi : ℂ) * Complex.I) * (θ i : ℂ)) • u θ)
      2 centeredPlaneFrequencyMeasure := by
    apply ((Lp.memLp u).const_smul (2 * Real.pi)).of_le
      (hc.aestronglyMeasurable.smul (Lp.aestronglyMeasurable u))
    filter_upwards [centeredPlaneFrequency_coordinate_bound i] with θ hθ
    simp only [Pi.smul_apply, Pi.smul_apply']
    rw [norm_smul, norm_smul, Real.norm_of_nonneg hC]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have he : ‖(2 * (Real.pi : ℂ) * Complex.I) * (θ i : ℂ)‖ =
        (2 * Real.pi) * |θ i| := by
      simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    rw [he]
    exact mul_le_of_le_one_right hC hθ
  exact (Lp.memLp v).sub hsmul

theorem centeredPlaneBlochRealCellJet_memLp
    (f : Lp ℝ 2 (volume : Measure (Vec 2)))
    (g : Fin 2 → Lp ℝ 2 (volume : Measure (Vec 2))) :
    MemLp (planeBlochRealCellJet centeredPlaneFrequencyBase f g) 2
      centeredPlaneFrequencyMeasure := by
  apply MemLp.of_eval_piLp
  intro a
  change MemLp (fun θ => if h : a.1.val = 0 then
    scalarTorusToCell (planeScalarBlochTransform centeredPlaneFrequencyBase 1
      (by norm_num) (ofRealL2 volume f) θ) else
    scalarTorusToCell (planeBlochCellDerivative θ (a.2 ⟨0, by omega⟩)
      (planeScalarBlochTransform centeredPlaneFrequencyBase 1 (by norm_num) (ofRealL2 volume f) θ)
      (planeScalarBlochTransform centeredPlaneFrequencyBase 1 (by norm_num)
        (ofRealL2 volume (g (a.2 ⟨0, by omega⟩))) θ))) 2 centeredPlaneFrequencyMeasure
  split_ifs
  · exact scalarTorusToCell.toContinuousLinearMap.comp_memLp' (Lp.memLp _)
  · exact scalarTorusToCell.toContinuousLinearMap.comp_memLp'
      (centeredPlaneBlochDerivative_memLp _ _ _)

theorem centeredPlaneBlochRealH1_memLp
    (f : Lp ℝ 2 (volume : Measure (Vec 2)))
    (g : Fin 2 → Lp ℝ 2 (volume : Measure (Vec 2)))
    (hfg : ∀ i, HasWeakPartialDerivOn Set.univ i f (g i)) :
    MemLp (planeBlochRealH1 centeredPlaneFrequencyBase f g) 2
      centeredPlaneFrequencyMeasure := by
  apply (centeredPlaneBlochRealCellJet_memLp f g).of_le
    (planeBlochRealH1_aestronglyMeasurable centeredPlaneFrequencyBase f g hfg)
  filter_upwards [planeBlochRealH1_val_ae centeredPlaneFrequencyBase f g hfg] with θ hθ
  change ‖(planeBlochRealH1 centeredPlaneFrequencyBase f g θ).val‖ ≤ _
  rw [hθ]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane
open AVRegularity.Analysis.Convolution AVRegularity.Weighted
namespace AVRegularity.CycleWords

/-! Actual stored words inherit the weak Hilbert time curve from the original source equation. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem plane_ordered_source_curve_of_dual_memLp {K : ℕ} {a b : ℝ}
    (U H : ℝ → PlaneHk Set.univ K E)
    (W : ℝ → PlaneHk Set.univ (K + 1) E)
    (S : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (hU : ContinuousOn U (Set.Icc a b))
    (hW : MemLp W 2 (volume.restrict (Set.Icc a b)))
    (hagrees : ∀ᵐ r ∂volume.restrict (Set.Icc a b),
      U r = truncatePlaneHk (Nat.le_succ K) (W r))
    (heq : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, s ≤ t →
      ∀ Z : PlaneHk Set.univ 1 E,
      inner ℝ (planeHkValueOperator K (U t)) (planeHkValueOperator 1 Z) -
        inner ℝ (planeHkValueOperator K (U s)) (planeHkValueOperator 1 Z) =
      ∫ r in s..t, inner ℝ (planeHkValueOperator K (H r)) (planeHkValueOperator 1 Z) -
        inner ℝ (planeFluxValueOperator K (S r)) (planeH1GradientOperator Z))
    (α : JetIndex2 K)
    (hdual : MemLp (fun t => planeSourceDual (planeJetReadoutOperator K α (H t))
      (planeJetFluxOperator K α (S t))) 2 (volume.restrict (Set.Icc a b))) :
    PlaneWeakHilbertCurve a b (fun t => planeJetReadoutOperator K α (U t))
      (fun t => planeWordH1SliceOperator K α (W t))
      (fun t => planeSourceDual (planeJetReadoutOperator K α (H t))
        (planeJetFluxOperator K α (S t))) := by
  refine ⟨(planeJetReadoutOperator K α).continuous.comp_continuousOn hU,
    (planeWordH1SliceOperator K α).comp_memLp' hW,
    hdual, ?_, ?_⟩
  · filter_upwards [hagrees] with t ht
    rw [ht, planeWordH1Slice_value]
    rfl
  · intro s hs t ht hst Z
    have hi := plane_ordered_source_increment_of_dual_memLp U H S hs ht hst
      (heq s hs t ht hst) α hdual Z
    simp only [planeJetReadoutOperator_apply]
    rw [hi]
    apply intervalIntegral.integral_congr
    intro r _
    dsimp only
    rw [planeSourceDual_pair]
    simp only [planeJetSourcePair,
      PiLp.inner_apply, planeJetFluxOperator_apply]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory UnitAddTorus AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Genuine cell Bloch intertwining for the actual bounded measurable periodic drift. -/

local instance planeCellBlochDriftMultiplierMeasure : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

theorem planeCellBloch_drift_multiplier (a : Vec 2)
    (A : CellCoefficients) (hv : IsCellDrift A.v) (V : ℝ)
    (hb : ∀ t x, ∑ i, A.v t x i ^ 2 ≤ V ^ 2)
    (C : ℝ) (hCpos : 0 < C) (hC : ∀ t i z, ‖cellDriftTorusSymbol A.v t i z‖ ≤ C)
    (t : ℝ) (i : Fin 2) (f : Lp ℂ 2 (volume : Measure (Vec 2))) :
    planeCellBlochTransform a 1 (by norm_num)
      (planeMeasurableTorusSymbolMultiplication (cellDriftTorusSymbol A.v t i)
        (cellDriftTorusSymbol_measurable A.v hv t i) C (hC t i) f) =
      (cellDriftEntryCLM A V hv.1 hb t i).compLp
        (planeCellBlochTransform a 1 (by norm_num) f) := by
  change liftLinearIsometryL2 (volume.restrict (planeFrequencyCell a 1)) scalarTorusToCell
    (planeScalarBlochTransform a 1 (by norm_num) _) = _
  rw [planeBloch_measurableMultiplier a f _ _ C hCpos (hC t i)]
  apply Lp.ext
  have hl := liftLinearIsometryL2_ae (volume.restrict (planeFrequencyCell a 1)) scalarTorusToCell
    ((measurableTorusSymbolMultiplication (cellDriftTorusSymbol A.v t i)
      (cellDriftTorusSymbol_measurable A.v hv t i) C (hC t i)).compLp
        (planeScalarBlochTransform a 1 (by norm_num) f))
  have hm := (measurableTorusSymbolMultiplication (cellDriftTorusSymbol A.v t i)
    (cellDriftTorusSymbol_measurable A.v hv t i) C (hC t i)).coeFn_compLp
      (planeScalarBlochTransform a 1 (by norm_num) f)
  have hr := (cellDriftEntryCLM A V hv.1 hb t i).coeFn_compLp
    (planeCellBlochTransform a 1 (by norm_num) f)
  filter_upwards [hl, hm, hr, planeCellBlochTransform_ae a 1 (by norm_num) f]
    with θ hlθ hmθ hrθ hpθ
  rw [hlθ, hmθ, hrθ, hpθ]
  exact scalarTorusToCell_drift_multiplier A hv V hb C hC t i _

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution Metric Filter Topology
open AVRegularity.CoupledEnergy.Galerkin
open scoped NNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! The literal homogeneous coefficient of the original L2 series is a native frequency derivative. -/

theorem torusHigher_native_homogeneous_coefficient_bound (K n : ℕ)
    (c : ℕ × ℕ → ComplexCellL2) (R : ℝ≥0) (hR : 0 < R)
    (hs : Summable (fun p => ‖c p‖ * (R : ℝ) ^ (p.1 + p.2)))
    (F : (Fin 2 → ℂ) → TorusHk K ℂ)
    (hF : ∀ ξ ∈ ball (0 : Fin 2 → ℂ) (R : ℝ),
      torusHkValueCLM (F ξ) = ∑' p, fibreMonomial ξ p • c p)
    (hf : ContDiffOn ℂ (⊤ : ℕ∞) F (ball 0 (R : ℝ)))
    (M : ℝ) (hb : ∀ ξ ∈ ball 0 (R : ℝ), ‖F ξ‖ ≤ M)
    (ξ : Fin 2 → ℂ) (hξ : ‖ξ‖ ≤ 1) :
    ∃ U : TorusHk K ℂ,
      torusHkValueCLM U = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, fibreMonomial ξ p • c p ∧ ‖U‖ ≤ M * ((R : ℝ) / 2)⁻¹ ^ n := by
  have hf0 : ContDiffAt ℂ (n : WithTop ℕ∞) F 0 :=
    ((hf 0 (mem_ball_self hR)).contDiffAt (ball_mem_nhds 0 hR)).of_le (by simp)
  let g := fun ξ => ∑' p, fibreMonomial ξ p • c p
  have hp := fibreBivariateSum_hasFPowerSeriesOnBall c R hR hs
  have he : g =ᶠ[𝓝 (0 : Fin 2 → ℂ)] (torusHigherComplexValueCLM K) ∘ F := by
    filter_upwards [ball_mem_nhds (0 : Fin 2 → ℂ) (show (0 : ℝ) < R from hR)] with x hx
    exact (hF x hx).symm
  have hd : torusHkValueCLM (iteratedFDeriv ℂ n F 0 (fun _ => ξ)) =
      iteratedFDeriv ℂ n g 0 (fun _ => ξ) := by
    rw [(he.iteratedFDeriv (𝕜 := ℂ) n).self_of_nhds]
    rw [(torusHigherComplexValueCLM K).iteratedFDeriv_comp_left hf0 le_rfl]
    rfl
  refine ⟨((n.factorial : ℂ)⁻¹) • iteratedFDeriv ℂ n F 0 (fun _ => ξ), ?_, ?_⟩
  · rw [torusHigher_complex_value_smul, hd, ← hp.factorial_smul ξ n, fibreFormalSeries_diag]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr n.factorial_ne_zero), one_smul]
  · let δ : ℝ≥0 := ⟨(R : ℝ) / 2, (half_pos (show (0 : ℝ) < R from hR)).le⟩
    have hdpos : 0 < δ := half_pos hR
    apply complexDirectionalTaylor_norm_le F (ball 0 (R : ℝ)) isOpen_ball hf
      (mem_ball_self hR) ξ δ hdpos M _ hb n
    intro z hz
    have hz' : ‖z‖ ≤ (R : ℝ) / 2 := by
      have hzz : ‖z‖ ≤ (δ : ℝ) := by simpa only [mem_closedBall, dist_zero_right] using hz
      rw [show (δ : ℝ) = (R : ℝ) / 2 from rfl] at hzz
      exact hzz
    have hnorm : ‖z • ξ‖ ≤ (R : ℝ) / 2 := by
      rw [norm_smul]
      exact (mul_le_mul_of_nonneg_left hξ (norm_nonneg z)).trans
        (by simpa only [mul_one] using hz')
    exact mem_ball_zero_iff.mpr (hnorm.trans_lt (half_lt_self (show (0 : ℝ) < R from hR)))

end AVRegularity.CycleWords
end

section
open MeasureTheory Set AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Actual cell H1 time states of a frequency field of compatible energy carriers. -/

local instance {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : Measure X) : AddCommMonoid (Lp E 2 μ) :=
  (inferInstance : NormedAddCommGroup (Lp E 2 μ)).toAddCommMonoid

local instance {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℂ E] (μ : Measure X) : Module ℂ (Lp E 2 μ) :=
  (inferInstance : NormedSpace ℂ (Lp E 2 μ)).toModule

def cellEnergyTimeStateOperator {a b : ℝ} (hab : a ≤ b) :
    CellEnergySpace a b →L[ℂ] Lp CellComplexH1 2 (volume.restrict (Icc a b)) :=
  (cellFiniteEnergyTimeStateCLM hab).comp (cellEnergySpaceToCarrierCLM a b)

def cellEnergyFrequencyTimeState {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {a b : ℝ} (hab : a ≤ b) (F : Lp (CellEnergySpace a b) 2 μ) :
    Lp (Lp CellComplexH1 2 (volume.restrict (Icc a b))) 2 μ :=
  (cellEnergyTimeStateOperator hab).compLp F

theorem cellEnergyFrequencyTimeState_ae {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {a b : ℝ} (hab : a ≤ b) (F : Lp (CellEnergySpace a b) 2 μ) :
    ∀ᵐ θ ∂μ, cellEnergyFrequencyTimeState μ hab F θ =
      cellFiniteEnergyTimeStateCLM hab (cellEnergySpaceToCarrierCLM a b (F θ)) :=
  (cellEnergyTimeStateOperator hab).coeFn_compLp F

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleWords

/-! Physical derivative shifts on the centered Fourier cell. -/

def planePhysicalBlochShift (θ : Vec 2) : Fin 2 → ℂ :=
  fun j => (2 * Real.pi * θ j : ℝ)

theorem planePhysicalBlochShift_continuous : Continuous planePhysicalBlochShift := by
  unfold planePhysicalBlochShift
  fun_prop

theorem planePhysicalBlochShift_real (θ : Vec 2) (j : Fin 2) :
    star (planePhysicalBlochShift θ j) = planePhysicalBlochShift θ j :=
  Complex.conj_ofReal _

theorem centeredPlanePhysicalBlochShift_bound :
    ∀ᵐ θ ∂centeredPlaneFrequencyMeasure,
      ∑ j, ‖planePhysicalBlochShift θ j‖ ^ 2 ≤ 2 * (2 * Real.pi) ^ 2 := by
  have hi (j : Fin 2) : ∀ᵐ θ ∂centeredPlaneFrequencyMeasure,
      ‖planePhysicalBlochShift θ j‖ ^ 2 ≤ (2 * Real.pi) ^ 2 := by
    filter_upwards [centeredPlaneFrequency_coordinate_bound j] with θ hθ
    have hp : 0 ≤ 2 * Real.pi := by positivity
    have hn : ‖planePhysicalBlochShift θ j‖ ≤ 2 * Real.pi := by
      simp only [planePhysicalBlochShift, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg hp]
      exact mul_le_of_le_one_right hp hθ
    exact pow_le_pow_left₀ (norm_nonneg _) hn 2
  filter_upwards [hi 0, hi 1] with θ h₀ h₁
  simp only [Fin.sum_univ_two]
  linarith

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Actual reconstruction intertwines the native cell drift with its plane multiplier. -/

theorem planeCellBloch_drift_inverse (a : Vec 2)
    (A : CellCoefficients) (hv : IsCellDrift A.v) (V : ℝ)
    (hb : ∀ t x, ∑ i, A.v t x i ^ 2 ≤ V ^ 2)
    (C : ℝ) (hCpos : 0 < C) (hC : ∀ t i z, ‖cellDriftTorusSymbol A.v t i z‖ ≤ C)
    (t : ℝ) (i : Fin 2)
    (F : Lp ComplexCellL2 2 (volume.restrict (planeFrequencyCell a 1))) :
    (planeCellBlochUnitary a 1 (by norm_num)).symm
      ((cellDriftEntryCLM A V hv.1 hb t i).compLp F) =
        planeMeasurableTorusSymbolMultiplication (cellDriftTorusSymbol A.v t i)
          (cellDriftTorusSymbol_measurable A.v hv t i) C (hC t i)
          ((planeCellBlochUnitary a 1 (by norm_num)).symm F) := by
  apply (planeCellBlochUnitary a 1 (by norm_num)).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  change _ = planeCellBlochTransform a 1 (by norm_num) _
  rw [planeCellBloch_drift_multiplier a A hv V hb C hCpos hC t i]
  change _ = (cellDriftEntryCLM A V hv.1 hb t i).compLp
    ((planeCellBlochUnitary a 1 (by norm_num))
      ((planeCellBlochUnitary a 1 (by norm_num)).symm F))
  rw [LinearIsometryEquiv.apply_symm_apply]

end AVRegularity.CycleWords
end

section
open Homogenization Metric AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped NNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! Complex circle extraction gives geometric native bounds for every original bivariate coefficient. -/

theorem torusHigher_native_coefficient_geometric_bound (K : ℕ)
    (c : ℕ × ℕ → ComplexCellL2) (R : ℝ≥0) (hR : 0 < R)
    (hs : Summable (fun p => ‖c p‖ * (R : ℝ) ^ (p.1 + p.2)))
    (F : (Fin 2 → ℂ) → TorusHk K ℂ)
    (hF : ∀ ξ ∈ ball 0 (R : ℝ), torusHkValueCLM (F ξ) = ∑' p, fibreMonomial ξ p • c p)
    (hf : ContDiffOn ℂ (⊤ : ℕ∞) F (ball 0 (R : ℝ)))
    (M : ℝ) (hb : ∀ ξ ∈ ball 0 (R : ℝ), ‖F ξ‖ ≤ M)
    (U : ℕ × ℕ → TorusHk K ℂ) (hU : ∀ p, torusHkValueCLM (U p) = c p)
    (p : ℕ × ℕ) : ‖U p‖ ≤ M * ((R : ℝ) / 2)⁻¹ ^ (p.1 + p.2) := by
  let n := p.1 + p.2
  have hpoly (z : ℂ) (hz : z ∈ sphere 0 1) :
      ‖∑ j ∈ Finset.range (n + 1), z ^ j • U (j, n - j)‖ ≤ M * ((R : ℝ) / 2)⁻¹ ^ n := by
    let ξ : Fin 2 → ℂ := fun i => if i = 0 then z else 1
    have hzn : ‖z‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hz
    have hξ : ‖ξ‖ ≤ 1 := (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr (by
      intro i
      dsimp only [ξ]
      split_ifs <;> simp only [hzn, norm_one, le_refl])
    obtain ⟨W, hwv, hwb⟩ := torusHigher_native_homogeneous_coefficient_bound K n c R hR hs
      F hF hf M hb ξ hξ
    have hv : torusHkValueCLM (∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, fibreMonomial ξ q • U q) =
        torusHkValueCLM W := by
      rw [hwv, map_sum]
      apply Finset.sum_congr rfl
      intro q _
      rw [torusHigher_complex_value_smul, hU q]
    have he : (∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, fibreMonomial ξ q • U q) = W :=
      torusHigherComplexValueCLM_injective K hv
    have hp : (∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, fibreMonomial ξ q • U q) =
        ∑ j ∈ Finset.range (n + 1), z ^ j • U (j, n - j) := by
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      apply Finset.sum_congr rfl
      intro j _
      simp only [fibreMonomial, ξ, ite_eq_left rfl, show (1 : Fin 2) ≠ 0 by decide,
        ite_false, one_pow, mul_one]
    rw [hp] at he
    simpa only [he] using hwb
  have hc := complexVectorPolynomial_coefficient_norm_le (n + 1)
    (fun j => U (j, n - j)) 1 (M * ((R : ℝ) / 2)⁻¹ ^ n) (by norm_num)
    hpoly p.1 (by dsimp only [n]; omega)
  simpa only [n, Nat.add_sub_cancel_left, Prod.mk.eta, one_pow, div_one] using hc

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory UnitAddTorus AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Native value and physical derivative readouts of an actual first cell jet. -/

local instance cellFirstJetBlochReadoutMeasure : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

theorem cellFirstJet_value_readout (w : CellComplexH1) (u : ScalarTorusL2)
    (d : Fin 2 → ScalarTorusL2) (hw : w.val = scalarCellFirstJet u d) :
    cellComplexH1ValueCLM w = scalarTorusToCell u := by
  change w.val (valueIndex2 1) = _
  rw [hw]
  simp [scalarCellFirstJet, valueIndex2, valueIndex]

theorem cellFirstJet_physical_readout (θ : Vec 2) (w : CellComplexH1)
    (u : ScalarTorusL2) (v : Fin 2 → ScalarTorusL2)
    (hw : w.val = scalarCellFirstJet u (fun j => planeBlochCellDerivative θ j u (v j)))
    (i : Fin 2) :
    cellShiftedDerivativeCLM (planePhysicalBlochShift θ) i (cellComplexH1RealEquiv w) =
      scalarTorusToCell (v i) := by
  have hv := cellFirstJet_value_readout w u _ hw
  have hd : cellDerivativeCLM i (cellComplexH1RealEquiv w) =
      scalarTorusToCell (planeBlochCellDerivative θ i u (v i)) := by
    change w.val ⟨⟨1, by decide⟩, fun _ => i⟩ = _
    rw [hw]
    simp [scalarCellFirstJet]
  rw [cellShiftedDerivativeCLM, add_apply, ContinuousLinearMap.comp_apply, hd,
    cellScalarCLM_smul, ← cellComplexH1ValueCLM_eq, hv]
  have hc : Complex.I * planePhysicalBlochShift θ i =
      (2 * (Real.pi : ℂ) * Complex.I) * (θ i : ℂ) := by
    unfold planePhysicalBlochShift
    push_cast
    ring
  rw [hc, ← scalarTorusToCell_complex_smul, ← map_add]
  congr 1
  exact sub_add_cancel (v i) _

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Actual real constant metric entries commute with the frequency L2 readout. -/

theorem cellScalarCLM_real_smul (c : ℝ) (u : ComplexCellL2) :
    cellScalarCLM (c : ℂ) u = c • u := by
  rw [cellScalarCLM_smul]
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul (c : ℂ) u, Lp.coeFn_smul c u] with x hc hr
  rw [hc, hr]
  exact (RCLike.real_smul_eq_coe_smul (K := ℂ) c (u x)).symm

theorem cellScalarCLM_real_compLp (c : ℝ)
    (F : Lp ComplexCellL2 2 centeredPlaneFrequencyMeasure) :
    (cellScalarCLM (c : ℂ)).compLp F = c • F := by
  apply Lp.ext
  filter_upwards [(cellScalarCLM (c : ℂ)).coeFn_compLp F, Lp.coeFn_smul c F] with θ hc hr
  rw [hc, hr, cellScalarCLM_real_smul, Pi.smul_apply]

end AVRegularity.CycleWords
end

section
open Homogenization
namespace AVRegularity.CycleWords

/-! Exact normalization between physical plane Bloch frequency and the scalar-package frequency. -/

def planePhysicalFibreFrequency (η : ℝ) (θ : Vec 2) (i : Fin 2) : ℂ :=
  (Real.sqrt η : ℂ)⁻¹ * planePhysicalBlochShift θ i

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Weighted
namespace AVRegularity.CycleWords

/-! Actual compact flux production with the cell ellipticity budget. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def cellMetricCutoffFluxProduction
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (v : Vec 2 → Vec 2)
    (q χ : Vec 2 → ℝ) (Φ : Fin 2 → Vec 2 → ℝ) (dt : Vec 2 → ℝ)
    (x : Vec 2) (du F : PiLp 2 (fun _ : Fin 2 => E)) (u : E) : ℝ :=
  let p : PiLp 2 (fun _ : Fin 2 => ℝ) := WithLp.toLp 2 (fun i => fderiv ℝ q x (basisVec i))
  let h : PiLp 2 (fun _ : Fin 2 => ℝ) := WithLp.toLp 2 (fun i => fderiv ℝ χ x (basisVec i))
  let φ : PiLp 2 (fun _ : Fin 2 => ℝ) := WithLp.toLp 2 (fun i => Φ i x)
  (χ x ^ 2 * dt x + ∑ i : Fin 2,
    fderiv ℝ (fun y => χ y ^ 2 * scalarChartFlux v G q Φ i y) x (basisVec i)) * ‖u‖ ^ 2 -
    2 * inner ℝ du (scalarHilbertTensor
      (χ x ^ 2 • φ + (2 * χ x * q x) • finiteMetricFlux (G x) h) u) -
    2 * inner ℝ F ((χ x ^ 2 * q x) • du + χ x ^ 2 • scalarHilbertTensor p u +
      (2 * χ x * q x) • scalarHilbertTensor h u) -
    2 * χ x ^ 2 * q x * (∑ k : Fin 2, ∑ j : Fin 2,
      G x k j * inner ℝ (du k) (du j)) + (1 / 2) * χ x ^ 2 * q x * ‖du‖ ^ 2

theorem cellMetric_cutoff_flux_energy_pointwise
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (hCell : IsCellMetric G)
    (t : ℝ) (x : Vec 2)
    (v : Vec 2 → Vec 2) (q χ : Vec 2 → ℝ) (Φ : Fin 2 → Vec 2 → ℝ)
    (hχd : Differentiable ℝ χ)
    (hA : ∀ i, Differentiable ℝ (scalarChartFlux v (G t) q Φ i))
    (dt : ℝ) {lam M η : ℝ} (hlam : 0 ≤ lam) (hM : 0 ≤ M) (hη : 0 ≤ η)
    (hq : 0 ≤ q x) (hχ : 0 ≤ χ x) (hχ1 : χ x ≤ 1)
    (hv : ‖v x‖ ≤ M) (hdχ : ‖fderiv ℝ χ x‖ ≤ η)
    (hp : ‖(WithLp.toLp 2 (fun i => fderiv ℝ q x (basisVec i)) :
      PiLp 2 (fun _ : Fin 2 => ℝ))‖ ≤ Real.sqrt lam * q x)
    (hΦ : ‖(WithLp.toLp 2 (fun i => Φ i x) : PiLp 2 (fun _ : Fin 2 => ℝ))‖ ≤
      Real.sqrt lam * q x)
    (hdef : dt + (∑ i : Fin 2,
      fderiv ℝ (scalarChartFlux v (G t) q Φ i) x (basisVec i)) ≤ 2 * lam * q x)
    (du F : PiLp 2 (fun _ : Fin 2 => E)) (u : E) :
    let p : PiLp 2 (fun _ : Fin 2 => ℝ) := WithLp.toLp 2 (fun i => fderiv ℝ q x (basisVec i))
    let h : PiLp 2 (fun _ : Fin 2 => ℝ) := WithLp.toLp 2 (fun i => fderiv ℝ χ x (basisVec i))
    let φ : PiLp 2 (fun _ : Fin 2 => ℝ) := WithLp.toLp 2 (fun i => Φ i x)
    (χ x ^ 2 * dt + ∑ i : Fin 2,
      fderiv ℝ (fun y => χ y ^ 2 * scalarChartFlux v (G t) q Φ i y) x (basisVec i)) * ‖u‖ ^ 2 -
      2 * inner ℝ du (scalarHilbertTensor
        (χ x ^ 2 • φ + (2 * χ x * q x) • finiteMetricFlux (G t x) h) u) -
      2 * inner ℝ F ((χ x ^ 2 * q x) • du + χ x ^ 2 • scalarHilbertTensor p u +
        (2 * χ x * q x) • scalarHilbertTensor h u) -
      2 * χ x ^ 2 * q x * (∑ k : Fin 2, ∑ j : Fin 2,
        G t x k j * inner ℝ (du k) (du j)) + (1 / 2) * χ x ^ 2 * q x * ‖du‖ ^ 2 ≤
    18 * lam * χ x ^ 2 * q x * ‖u‖ ^ 2 + 8 * q x * ‖F‖ ^ 2 +
      (4096 * η ^ 2 + 16 * M * η) * q x * ‖u‖ ^ 2 := by
  let p : PiLp 2 (fun _ : Fin 2 => ℝ) := WithLp.toLp 2 (fun i => fderiv ℝ q x (basisVec i))
  let h : PiLp 2 (fun _ : Fin 2 => ℝ) := WithLp.toLp 2 (fun i => fderiv ℝ χ x (basisVec i))
  let φ : PiLp 2 (fun _ : Fin 2 => ℝ) := WithLp.toLp 2 (fun i => Φ i x)
  let V : PiLp 2 (fun _ : Fin 2 => ℝ) := WithLp.toLp 2 (v x)
  have hV : ‖V‖ ≤ 2 * M :=
    (scalar_vector_piLp_norm_le_two (v x)).trans (by linarith only [hv])
  have hh : ‖h‖ ≤ 2 * η := cutoff_gradient_piLp_norm_le χ x hdχ
  have hflux := cellMetric_cutoff_chart_metric_pointwise G hCell t x V p φ h du F u
    hq hlam hM hχ hχ1 hη hV hp hΦ hh
  have hcut := cutoff_defect_le χ hχd (scalarChartFlux v (G t) q Φ) hA x dt (q x)
    (2 * lam) hdef
  have he : (∑ i : Fin 2, fderiv ℝ χ x (basisVec i) * scalarChartFlux v (G t) q Φ i x) =
      inner ℝ h (q x • V + finiteMetricFlux (G t x) p - φ) := by
    simp only [PiLp.inner_apply, Real.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    change fderiv ℝ χ x (basisVec i) *
      (q x * v x i + ∑ j : Fin 2, G t x i j * fderiv ℝ q x (basisVec j) - Φ i x) =
      fderiv ℝ χ x (basisVec i) *
        (q x * v x i + ∑ j : Fin 2, G t x i j * fderiv ℝ q x (basisVec j) - Φ i x)
    rfl
  rw [he] at hcut
  have hmass := mul_le_mul_of_nonneg_right hcut (sq_nonneg ‖u‖)
  have hr := cutoff_residual_eq (G t x) V p φ h du F u (χ x) (q x)
  change _ ≤ _
  nlinarith only [hflux, hmass, hr]

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
open AVRegularity.CycleComparison.Lift AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The actual constant metric Bloch diffusion commutes with every smooth ordered derivative. -/

theorem finiteSmoothPeriodicHk_diffusion_derivative_value {K r : ℕ}
    (w : DerivativeWord2 r) (f : Vec 2 → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (θ : Fin 2 → ℂ) (t : ℝ) :
    torusHkValueCLM (derivativeTorusHk (K := K) w
      (torusHigherStrongDiffusionCLM (K + r) G θ t
        (finiteSmoothPeriodicHk (K + r + 2) f (hf.of_le (by simp)) hp))) =
      torusHkValueCLM (torusHigherStrongDiffusionCLM 0 G θ t
        (finiteSmoothPeriodicHk 2 (orderedDerivative w f)
          (orderedDerivative_contDiff w 2 f (hf.of_le (by simp)))
          (orderedDerivative_periodic w f (hf.of_le (by simp)) hp))) := by
  simp only [torusHigherStrongDiffusionCLM, add_apply, ContinuousLinearMap.comp_apply,
    Fin.sum_univ_two, map_add, torusHigherScalarCLM_derivative,
    torusHigherScalarCLM_value]
  simp only [finiteSmoothPeriodicHk_ordered_first_value w 0 f hf hp,
    finiteSmoothPeriodicHk_ordered_first_value w 1 f hf hp,
    finiteSmoothPeriodicHk_ordered_second_value w 0 0 f hf hp,
    finiteSmoothPeriodicHk_ordered_second_value w 0 1 f hf hp,
    finiteSmoothPeriodicHk_ordered_second_value w 1 0 f hf hp,
    finiteSmoothPeriodicHk_ordered_second_value w 1 1 f hf hp,
    finiteSmoothPeriodicHk_ordered_truncate_value w f hf hp]
  rfl

theorem finiteSmoothPeriodicHk_diffusion_derivative_strong_value {K r : ℕ}
    (w : DerivativeWord2 r) (f : Vec 2 → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (θ : Fin 2 → ℂ) (t : ℝ) :
    torusHkValueCLM (derivativeTorusHk (K := K) w
      (torusHigherStrongDiffusionCLM (K + r) G θ t
        (finiteSmoothPeriodicHk (K + r + 2) f (hf.of_le (by simp)) hp))) =
      cellConstantMetricStrongDiffusionCLM G θ t
        (finiteSmoothPeriodicHk 2 (orderedDerivative w f)
          (orderedDerivative_contDiff w 2 f (hf.of_le (by simp)))
          (orderedDerivative_periodic w f (hf.of_le (by simp)) hp)) := by
  rw [finiteSmoothPeriodicHk_diffusion_derivative_value w f hf hp,
    torusHigherStrongDiffusionCLM_value]
  congr 1

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory UnitAddTorus AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The norm-one transverse projection on the existing periodic weak H¹ carrier. -/

local instance cellTransverseH1ProjectionMeasure : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

def cellTransverseH1 (e : Fin 2) (u : TorusHk 1 ℂ) : TorusHk 1 ℂ :=
  scalarTorusH1OfFourier
    (scalarTorusTransverseProjection e (scalarCellToTorus (torusHkValueCLM u)))
    (fun i => scalarTorusTransverseProjection e (scalarCellToTorus (cellDerivativeCLM i u)))
    (fun i n => scalarTorusTransverseProjection_derivative_coeff e i _ _
      (cellH1_fourierDerivative u i) n)

theorem cellTransverseH1_value (e : Fin 2) (u : TorusHk 1 ℂ) :
    torusHkValueCLM (cellTransverseH1 e u) = cellTransverseProjection e (torusHkValueCLM u) := by
  rw [cellTransverseH1, scalarTorusH1OfFourier_value, cellTransverseProjection_apply]

theorem cellTransverseH1_derivative (e i : Fin 2) (u : TorusHk 1 ℂ) :
    cellDerivativeCLM i (cellTransverseH1 e u) = cellTransverseProjection e (cellDerivativeCLM i u) := by
  rw [cellTransverseH1, scalarTorusH1OfFourier_derivative, cellTransverseProjection_apply]

theorem cellTransverseH1_norm_le (e : Fin 2) (u : TorusHk 1 ℂ) :
    ‖cellTransverseH1 e u‖ ≤ ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [cellH1_norm_sq, cellH1_norm_sq, cellTransverseH1_value]
  simp_rw [cellTransverseH1_derivative]
  apply add_le_add
  · exact pow_le_pow_left₀ (norm_nonneg _) (cellTransverseProjection_norm_le e _) 2
  · apply Finset.sum_le_sum
    intro i _
    exact pow_le_pow_left₀ (norm_nonneg _) (cellTransverseProjection_norm_le e _) 2

def cellTransverseH1Projection (e : Fin 2) : TorusHk 1 ℂ →L[ℝ] TorusHk 1 ℂ := by
  let L : TorusHk 1 ℂ →ₗ[ℝ] TorusHk 1 ℂ :=
    { toFun := cellTransverseH1 e
      map_add' := fun u v => by
        apply TorusHk.ext_value
        change torusHkValueCLM (cellTransverseH1 e (u + v)) =
          torusHkValueCLM (cellTransverseH1 e u + cellTransverseH1 e v)
        simp only [cellTransverseH1_value, map_add]
      map_smul' := fun c u => by
        apply TorusHk.ext_value
        change torusHkValueCLM (cellTransverseH1 e (c • u)) =
          torusHkValueCLM (c • cellTransverseH1 e u)
        simp only [cellTransverseH1_value, map_smul] }
  exact L.mkContinuous 1 (fun u => by
    change ‖cellTransverseH1 e u‖ ≤ 1 * ‖u‖
    rw [one_mul]
    exact cellTransverseH1_norm_le e u)

theorem cellTransverseH1Projection_value (e : Fin 2) (u : TorusHk 1 ℂ) :
    torusHkValueCLM (cellTransverseH1Projection e u) =
      cellTransverseProjection e (torusHkValueCLM u) := cellTransverseH1_value e u

theorem cellTransverseH1Projection_derivative (e i : Fin 2) (u : TorusHk 1 ℂ) :
    cellDerivativeCLM i (cellTransverseH1Projection e u) =
      cellTransverseProjection e (cellDerivativeCLM i u) := cellTransverseH1_derivative e i u

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! The actual quadratic adjoint coordinate weight has a contrast uniform defect. -/

def adjointCellQuadratic (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ)
    (ν B T : ℝ) (yc : Vec 2) (t : ℝ) (z : Vec 2) : ℝ :=
  1 + adjointCellCoordinate α q Λ ζ m ν B T yc t z 0 ^ 2 +
    adjointCellCoordinate α q Λ ζ m ν B T yc t z 1 ^ 2

theorem adjointCellQuadratic_defect {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν B T C : ℝ}
    (hν : 0 < ν) (hB : 0 < B) (hT : 0 < T) (hC : 0 ≤ C)
    (he : ν + ocEpsilon q Λ m ^ (2 * (1 + α)) / ν ≤ C * B)
    (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ k t, |deriv (ocCutoff α q Λ m k) t| ≤ K / ocTau α q Λ m)
    (hdur : Real.sqrt T * ocEll q Λ m ν / ocTau α q Λ m *
      Real.exp (-Real.pi ^ 2 * ocTau α q Λ m / (3 * ocEll q Λ m ν ^ 2)) ≤ 1)
    (yc : Vec 2) (t : ℝ) (z : Vec 2) :
    scalarAdjointOperator (ocCellDrift α q Λ ζ m ν yc)
      (adjointCellQuadratic α q Λ ζ m ν B T yc) t z ≤
        (4 * K * (1 + C) + 16 * C) * (ocEll q Λ m ν ^ 2 / T) *
          adjointCellQuadratic α q Λ ζ m ν B T yc t z := by
  have hspace : ∀ j : Fin 2, ∀ s, ContDiff ℝ 2
      (fun x => adjointCellCoordinate α q Λ ζ m ν B T yc s x j) :=
    fun j s => adjointCellCoordinate_space_contDiff hΛ hζ ν B T yc s j 2
  have htime : ∀ j : Fin 2, ∀ x, Differentiable ℝ
      (fun s => adjointCellCoordinate α q Λ ζ m ν B T yc s x j) :=
    fun j x => (adjointCellCoordinate_time_contDiff hΛ hζ ν B T yc x j 1).differentiable (by norm_num)
  have hR : ∀ j : Fin 2, |scalarAdjointOperator (ocCellDrift α q Λ ζ m ν yc)
      (fun s x => adjointCellCoordinate α q Λ ζ m ν B T yc s x j) t z| ≤
        K * (1 + C) * (ocEll q Λ m ν ^ 2 / T) := by
    intro j
    unfold scalarAdjointOperator
    rw [adjointCellCoordinate_equation hΛ hζ hν hB hT yc t z j]
    exact adjointResidual_cell_duration_bound hΛ hζ hν hB hT hC he K hK hb hdur _ _ j
  have hgrad := adjointCellCoordinate_gradient_sum_bound hΛ hζ hν hB hT he yc t z
  unfold adjointCellQuadratic at *
  rw [scalarAdjointOperator_quadratic _ _ _ (hspace 0) (hspace 1) (htime 0) (htime 1)]
  simp only [Fin.sum_univ_two]
  have hh := quadratic_coordinate_defect_bound
    (x := adjointCellCoordinate α q Λ ζ m ν B T yc t z 0)
    (y := adjointCellCoordinate α q Λ ζ m ν B T yc t z 1)
    (show 0 ≤ 8 * C * (ocEll q Λ m ν ^ 2 / T) by positivity)
    (show 0 ≤ K * (1 + C) * (ocEll q Λ m ν ^ 2 / T) by positivity) (hR 0) (hR 1)
    (by simpa only [Fin.sum_univ_two] using hgrad)
  convert hh using 1
  ring

end AVRegularity.CycleWords
end

section
open Homogenization Set
namespace AVRegularity.CycleWords

/-! Pointwise weighted energy production with the literal clipped ChartWeights fields. -/

open AVRegularity.Weighted

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem cellMetric_chartWeights_clipped_cutoff_energy_pointwise
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {t₀ S ϖ : ℝ} {zc : Vec 2} {N : ℕ} {Cw : ℕ → ℝ}
    (W : ChartWeights G v t₀ S ϖ zc N Cw) (m : ℕ) (hm : m ≤ N)
    (t : ℝ) (ht : t ∈ Icc t₀ (t₀ + S)) (B : ℝ) (hB : 0 < B)
    (hCell : IsCellMetric G)
    (hv : ContDiff ℝ 1 (v t))
    (hdiv : ∀ x, ∑ j : Fin 2, fderiv ℝ (v t) x (basisVec j) j = 0)
    (hGs : ∀ x, (G t x).IsSymm)
    (hG : ∀ i j : Fin 2, ContDiff ℝ 1 (fun x => G t x i j))
    (χ : Vec 2 → ℝ) (hχd : Differentiable ℝ χ) (x : Vec 2)
    {M η : ℝ} (hM : 0 ≤ M) (hη : 0 ≤ η)
    (hχ : 0 ≤ χ x) (hχ1 : χ x ≤ 1)
    (hvb : ‖v t x‖ ≤ M) (hdχ : ‖fderiv ℝ χ x‖ ≤ η)
    (du F : PiLp 2 (fun _ : Fin 2 => E)) (u : E) :
    let q := fun y => clipWeight B (W.W m t y)
    let Φ := fun i y => clipWeightDeriv B (W.W m t y) * W.Phi m t y i
    let dt := fun y => deriv (fun s => clipWeight B (W.W m s y)) t
    cellMetricCutoffFluxProduction (G t) (v t) q χ Φ dt x du F u ≤
      18 * W.lam m * χ x ^ 2 * q x * ‖u‖ ^ 2 + 8 * q x * ‖F‖ ^ 2 +
        (4096 * η ^ 2 + 16 * M * η) * q x * ‖u‖ ^ 2 := by
  obtain ⟨hA, hdef⟩ := cellMetric_chartWeights_clipped_flux_defect W m hm t ht B hB hCell
    hv hdiv hGs hG
  obtain ⟨hp, hΦ⟩ := chartWeights_clipped_log_norm_bounds W m hm t ht x B hB
  exact cellMetric_cutoff_flux_energy_pointwise G hCell t x (v t)
    (fun y => clipWeight B (W.W m t y)) χ
    (fun i y => clipWeightDeriv B (W.W m t y) * W.Phi m t y i) hχd
    (fun i => (hA i).differentiable (by norm_num))
    (deriv (fun s => clipWeight B (W.W m s x)) t) (W.lam_bound m hm).1 hM hη
    (clipWeight_pos hB (W.pos m hm t x)).le hχ hχ1 hvb hdχ hp hΦ (hdef x) du F u

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory UnitAddTorus AVRegularity.Sobolev
open AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The weak parallel derivative of the actual transverse projection is zero. -/

local instance cellTransverseParallelDerivativeMeasure : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

theorem scalarTorusTransverseProjection_parallel_derivative_zero
    (e : Fin 2) (u : TorusHk 1 ℂ) :
    scalarTorusTransverseProjection e (scalarCellToTorus (cellDerivativeCLM e u)) = 0 := by
  apply (mFourierBasis (d := Fin 2)).repr.injective
  apply lp.ext
  funext n
  rw [mFourierBasis_repr, map_zero]
  change mFourierCoeff
    (scalarTorusTransverseProjection e (scalarCellToTorus (cellDerivativeCLM e u))) n = 0
  rw [scalarTorusTransverseProjection_fourierCoeff]
  split_ifs with hn
  · rw [cellH1_fourierDerivative, hn]
    simp only [Int.cast_zero, mul_zero, zero_mul]
  · rfl

theorem cellTransverseH1Projection_parallel_derivative_zero
    (e : Fin 2) (u : TorusHk 1 ℂ) :
    cellDerivativeCLM e (cellTransverseH1Projection e u) = 0 := by
  rw [cellTransverseH1Projection_derivative, cellTransverseProjection_apply,
    scalarTorusTransverseProjection_parallel_derivative_zero, map_zero]

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! A literal slow Taylor degree keeps its slow ratio while retaining all fast coefficient jets. -/

theorem slowHomogeneous_sample_jet_budget (r J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Vec 2 → Vec 2 → ℝ), IsBoxSmooth r J f →
      ∀ (ϖ ρ δ ζ B : ℝ), 0 < ϖ → 0 ≤ ρ → ρ * ϖ ≤ 1 →
      0 ≤ ζ → 0 ≤ B → δ = ζ * ϖ →
      (∀ k ≤ J, ∀ X z, ρ ^ k *
        ‖iteratedFDeriv ℝ r (fun X' => iteratedFDeriv ℝ k (f X') z) X‖ ≤ B) →
      ∀ X j, j ≤ J → ∀ z,
        ρ ^ j * ‖iteratedFDeriv ℝ j (fun z =>
          iteratedFDeriv ℝ r (fun X' => f X' z) X (fun _ => δ • z)) z‖ ≤
          C * B * ζ ^ r * polynomialMomentRoot ϖ z ^ r := by
  obtain ⟨C, hC, hb⟩ := variableMultilinear_scaled_normalized_jet_budget r J
  refine ⟨C * 2 ^ J, by positivity, ?_⟩
  intro f hf ϖ ρ δ ζ B hϖ hρ hscale hζ hB hδ hjet X j hj z
  let a := fun (_ : Unit) (z : Vec 2) => ζ ^ r • iteratedFDeriv ℝ r (fun X' => f X' z) X
  have ha (_t : Unit) : ContDiff ℝ (J : ℕ) (a _t) := by
    have hh := CoarseFluxDiff.contDiff_slowJet hf X
    exact (hh.of_le (by exact_mod_cast le_refl J)).const_smul _
  have hab (_t : Unit) (w : DerivativeWord2 r) (k : ℕ) (hk : k ≤ J) (z : Vec 2) :
      ρ ^ k * ‖iteratedFDeriv ℝ k (fun z => a _t z (fun i => basisVec (w i))) z‖ ≤
        2 ^ J * B * ζ ^ r := by
    have hc : ContDiff ℝ (k : ℕ) (fun z => iteratedFDeriv ℝ r (fun X' => f X' z) X
        (fun i => basisVec (w i))) :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin r => Vec 2) ℝ
        (fun i => basisVec (w i))).contDiff.comp
        ((CoarseFluxDiff.contDiff_slowJet hf X).of_le (by exact_mod_cast hk))
    change ρ ^ k * ‖iteratedFDeriv ℝ k (fun z => ζ ^ r •
      iteratedFDeriv ℝ r (fun X' => f X' z) X (fun i => basisVec (w i))) z‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' hc.contDiffAt, norm_smul,
      Real.norm_of_nonneg (pow_nonneg hζ r)]
    have hh := slowCoefficient_fast_jet_le (hf.mono le_rfl hk) w X z
    have hs : ρ ^ k * ‖iteratedFDeriv ℝ k (fun z =>
        iteratedFDeriv ℝ r (fun X' => f X' z) X (fun i => basisVec (w i))) z‖ ≤ 2 ^ J * B := by
      calc
        _ ≤ ρ ^ k * (2 ^ k * ‖iteratedFDeriv ℝ r
            (fun X' => iteratedFDeriv ℝ k (f X') z) X‖) :=
          mul_le_mul_of_nonneg_left hh (pow_nonneg hρ k)
        _ = 2 ^ k * (ρ ^ k * ‖iteratedFDeriv ℝ r
            (fun X' => iteratedFDeriv ℝ k (f X') z) X‖) := by ring
        _ ≤ 2 ^ k * B := mul_le_mul_of_nonneg_left (hjet k hk X z) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk) hB
    have hs' := mul_le_mul_of_nonneg_right hs (pow_nonneg hζ r)
    convert hs' using 1; ring
  have he : (fun z : Vec 2 => a () z (fun _ => ϖ • z)) =
      (fun z => iteratedFDeriv ℝ r (fun X' => f X' z) X (fun _ => δ • z)) := by
    funext y
    dsimp only [a]
    rw [smul_apply, ContinuousMultilinearMap.map_smul_univ]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_smul]
    rw [hδ, mul_smul]
    rw [ContinuousMultilinearMap.map_smul_univ]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_smul, mul_pow]
  have hh := hb a ha ϖ ρ (2 ^ J * B * ζ ^ r) hϖ hρ hscale (by positivity) hab () j hj z
  rw [he] at hh
  simpa only [mul_assoc] using hh

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleWords

/-! Joint measurability of the actual real-frequency cell generator. -/

theorem cellPhysicalShiftedDerivative_continuous (i : Fin 2) (u : TorusHk 1 ℂ) :
    Continuous (fun θ => cellShiftedDerivativeCLM (planePhysicalBlochShift θ) i u) := by
  simp only [cellShiftedDerivativeCLM, add_apply, ContinuousLinearMap.comp_apply,
    cellScalarCLM_smul]
  exact continuous_const.add ((continuous_const.mul
    ((continuous_apply i).comp planePhysicalBlochShift_continuous)).smul continuous_const)

theorem cellPhysicalGenerator_continuous
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (t : ℝ) (u z : TorusHk 1 ℂ) :
    Continuous (fun θ => cellGeneratorForm ⟨fun t _ => G t, v,
      planePhysicalBlochShift θ, 0⟩ hG V hv hb t u z) := by
  have hstar (θ : Vec 2) : (fun i => star (planePhysicalBlochShift θ i)) =
      planePhysicalBlochShift θ := funext (planePhysicalBlochShift_real θ)
  simp only [cellGeneratorForm, cellDiffusionForm, neg_apply, sum_apply, add_apply,
    sub_apply, pullbackInnerCLM_apply, ContinuousLinearMap.comp_apply, hstar]
  apply Continuous.add
  · apply Continuous.sub
    · apply Continuous.neg
      apply continuous_finsetSum
      intro i _
      apply continuous_finsetSum
      intro j _
      exact ((cellMetricEntryCLM hG t i j).continuous.comp
        (cellPhysicalShiftedDerivative_continuous i u)).inner
          (cellPhysicalShiftedDerivative_continuous j z)
    · apply continuous_finsetSum
      intro i _
      exact ((cellDriftEntryCLM ⟨fun t _ => G t, v, 0, 0⟩ V hv hb t i).continuous.comp
        (cellPhysicalShiftedDerivative_continuous i u)).inner continuous_const
  · exact continuous_const

theorem cellPhysicalGenerator_fixedPair_stronglyMeasurable
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (u z : TorusHk 1 ℂ) :
    StronglyMeasurable (fun p : Vec 2 × ℝ => cellGeneratorForm
      ⟨fun t _ => G t, v, planePhysicalBlochShift p.1, 0⟩ hG V hv hb p.2 u z) := by
  exact stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    (fun t => cellPhysicalGenerator_continuous G hG v V hv hb t u z)
    (fun θ => cellGeneratorForm_pairing_stronglyMeasurable
      ⟨fun t _ => G t, v, planePhysicalBlochShift θ, 0⟩ hG V hv hb measurable_const u z)

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! The quadratic base has a uniform logarithmic gradient budget. -/

theorem adjointCellQuadratic_gradient_budget {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν B T C : ℝ}
    (hν : 0 < ν) (hB : 0 < B) (hT : 0 < T) (hC : 0 ≤ C)
    (he : ν + ocEpsilon q Λ m ^ (2 * (1 + α)) / ν ≤ C * B)
    (yc : Vec 2) (t : ℝ) (z : Vec 2) :
    (∑ i : Fin 2, (fderiv ℝ (adjointCellQuadratic α q Λ ζ m ν B T yc t) z (basisVec i)) ^ 2) ≤
      (32 * C * (ocEll q Λ m ν ^ 2 / T)) * adjointCellQuadratic α q Λ ζ m ν B T yc t z ^ 2 := by
  have h0 := (adjointCellCoordinate_space_contDiff (α := α) (q := q) (m := m)
    hΛ hζ ν B T yc t 0 1).differentiable (by norm_num)
  have h1 := (adjointCellCoordinate_space_contDiff (α := α) (q := q) (m := m)
    hΛ hζ ν B T yc t 1 1).differentiable (by norm_num)
  have hgrad := adjointCellCoordinate_gradient_sum_bound hΛ hζ hν hB hT he yc t z
  have hh := quadratic_weight_gradient_sum _ _ h0 h1 z
  have hU : 1 ≤ adjointCellQuadratic α q Λ ζ m ν B T yc t z := by
    unfold adjointCellQuadratic
    nlinarith only [sq_nonneg (adjointCellCoordinate α q Λ ζ m ν B T yc t z 0),
      sq_nonneg (adjointCellCoordinate α q Λ ζ m ν B T yc t z 1)]
  have hU0 : 0 ≤ adjointCellQuadratic α q Λ ζ m ν B T yc t z := by linarith
  have hUsq : adjointCellQuadratic α q Λ ζ m ν B T yc t z ≤
      adjointCellQuadratic α q Λ ζ m ν B T yc t z ^ 2 := by nlinarith only [hU, hU0]
  have hmul := mul_le_mul_of_nonneg_left hgrad (show 0 ≤
      4 * adjointCellQuadratic α q Λ ζ m ν B T yc t z by positivity)
  unfold adjointCellQuadratic at *
  simp only [Fin.sum_univ_two] at hmul hh ⊢
  apply hh.trans
  apply hmul.trans
  have hs := mul_le_mul_of_nonneg_left hUsq
    (show 0 ≤ 32 * C * (ocEll q Λ m ν ^ 2 / T) by positivity)
  convert hs using 1
  ring

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The actual physical Bloch derivatives of L2 cell H1 fields are L2 in frequency. -/

local instance centeredCellBlochGradientENorm : ENorm ComplexCellL2 :=
  (inferInstance : NormedAddCommGroup ComplexCellL2).toENormedAddCommMonoid.toENorm

theorem centeredCellH1ValueField_memLp
    (u : Lp CellComplexH1 2 centeredPlaneFrequencyMeasure) :
    MemLp (fun θ => torusHkValueCLM (cellComplexH1RealEquiv (u θ)))
      2 centeredPlaneFrequencyMeasure := by
  simpa only [Function.comp_def, cellComplexH1ValueCLM_eq] using
    cellComplexH1ValueCLM.comp_memLp' (Lp.memLp u)

theorem centeredPhysicalBlochPhase_norm_le (i : Fin 2) :
    ∀ᵐ θ ∂centeredPlaneFrequencyMeasure,
      ‖Complex.I * planePhysicalBlochShift θ i‖ ≤ 2 * Real.pi := by
  filter_upwards [centeredPlaneFrequency_coordinate_bound i] with θ hθ
  have hp : 0 ≤ 2 * Real.pi := by positivity
  have he : ‖Complex.I * planePhysicalBlochShift θ i‖ = (2 * Real.pi) * |θ i| := by
    simp only [planePhysicalBlochShift, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
  rw [he]
  exact mul_le_of_le_one_right hp hθ

theorem centeredCellBlochPhase_memLp
    (u : Lp CellComplexH1 2 centeredPlaneFrequencyMeasure) (i : Fin 2) :
    MemLp (fun θ => (Complex.I * planePhysicalBlochShift θ i) •
      torusHkValueCLM (cellComplexH1RealEquiv (u θ))) 2 centeredPlaneFrequencyMeasure := by
  have hval := centeredCellH1ValueField_memLp u
  have hc : Continuous (fun θ => Complex.I * planePhysicalBlochShift θ i) := by
    dsimp only [planePhysicalBlochShift]
    fun_prop
  apply (hval.const_smul (2 * Real.pi)).of_le
    (hc.aestronglyMeasurable.smul hval.aestronglyMeasurable)
  filter_upwards [centeredPhysicalBlochPhase_norm_le i] with θ hθ
  change ‖(Complex.I * planePhysicalBlochShift θ i) •
    torusHkValueCLM (cellComplexH1RealEquiv (u θ))‖ ≤
    ‖(2 * Real.pi) • torusHkValueCLM (cellComplexH1RealEquiv (u θ))‖
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
  exact mul_le_mul_of_nonneg_right hθ (norm_nonneg _)

theorem centeredCellBlochGradient_memLp
    (u : Lp CellComplexH1 2 centeredPlaneFrequencyMeasure) (i : Fin 2) :
    MemLp (fun θ => cellShiftedDerivativeCLM (planePhysicalBlochShift θ) i
      (cellComplexH1RealEquiv (u θ))) 2 centeredPlaneFrequencyMeasure := by
  have hd := (cellComplexH1DerivativeCLM i).comp_memLp' (Lp.memLp u)
  have hp := centeredCellBlochPhase_memLp u i
  change MemLp ((fun θ => cellComplexH1DerivativeCLM i (u θ)) +
    fun θ => (Complex.I * planePhysicalBlochShift θ i) •
      torusHkValueCLM (cellComplexH1RealEquiv (u θ))) 2 centeredPlaneFrequencyMeasure
  exact hd.add hp

end AVRegularity.CycleWords
end
