-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleDamping.ReferenceSourceMode
import AVRegularity.CycleReference.ChartIntegrandAlgebra
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.CycleReference.CorrectorMeanGeometry
import AVRegularity.CycleReference.SingleModeFlux
import AVenhance.Infra.Classical.GalerkinGenerator
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization AVenhance
namespace AVRegularity.CycleDamping

/-! Joint continuity of the actual switching residual, obtained from the exact mode equation. -/

theorem cellSwitchResidual_component_continuous {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (B : ℝ) (y₀ : Vec 2) (j : Fin 2) :
    Continuous (fun p : ℝ × Vec 2 => cellSwitchResidual α q Λ ζ m ν B y₀ p.1 p.2 j) := by
  have ha := cellReferenceAmplitude_contDiff_one (α := α) (q := q) (m := m) hΛ hζ ν B j
  have hc : Continuous (fun p : ℝ × Vec 2 =>
      (deriv (cellReferenceAmplitude α q Λ ζ m ν B j) p.1 +
        4 * Real.pi ^ 2 * cellReferenceAmplitude α q Λ ζ m ν B j p.1) *
      Real.cos (2 * Real.pi * (p.2 (1 - j) + y₀ (1 - j) / ocEpsilon q Λ m))) :=
    ((ha.continuous_deriv_one.comp continuous_fst).add
      (continuous_const.mul (ha.continuous.comp continuous_fst))).mul (by fun_prop)
  have hv : Continuous (fun p : ℝ × Vec 2 =>
      Real.sqrt (ν / B) * ocCellDrift α q Λ ζ m ν y₀ p.1 p.2 j) :=
    continuous_const.mul ((continuous_apply j).comp (ocCellDrift_joint_continuous hΛ hζ ν y₀))
  have he : (fun p : ℝ × Vec 2 => cellSwitchResidual α q Λ ζ m ν B y₀ p.1 p.2 j) =
      fun p => (deriv (cellReferenceAmplitude α q Λ ζ m ν B j) p.1 +
        4 * Real.pi ^ 2 * cellReferenceAmplitude α q Λ ζ m ν B j p.1) *
      Real.cos (2 * Real.pi * (p.2 (1 - j) + y₀ (1 - j) / ocEpsilon q Λ m)) -
        Real.sqrt (ν / B) * ocCellDrift α q Λ ζ m ν y₀ p.1 p.2 j := by
    funext p
    have h := cellReferenceSource_single_mode (α := α) (q := q) (m := m) hΛ hζ hν B p.1 y₀ p.2 j
    linarith only [h]
  rw [he]
  exact hc.sub hv

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CycleDamping

/-! The actual switching-corrected reference source is mean-free. -/

theorem cellReferenceSource_mean_zero {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (B t : ℝ) (y₀ : Vec 2) (j : Fin 2) :
    cellMean (fun x => ((Real.sqrt (ν / B) * ocCellDrift α q Λ ζ m ν y₀ t x j +
      cellSwitchResidual α q Λ ζ m ν B y₀ t x j : ℝ) : ℂ)) = 0 := by
  unfold cellMean
  simp_rw [cellReferenceSource_single_mode hΛ hζ hν]
  rw [integral_complex_ofReal, integral_const_mul, cell_cosine_mean_zero, mul_zero]
  rfl

theorem cellReferenceSource_q0 {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (B t : ℝ) (y₀ : Vec 2) (j : Fin 2) :
    cellQ0 (fun x => ((Real.sqrt (ν / B) * ocCellDrift α q Λ ζ m ν y₀ t x j +
      cellSwitchResidual α q Λ ζ m ν B y₀ t x j : ℝ) : ℂ)) =
      fun x => ((Real.sqrt (ν / B) * ocCellDrift α q Λ ζ m ν y₀ t x j +
        cellSwitchResidual α q Λ ζ m ν B y₀ t x j : ℝ) : ℂ) := by
  funext x
  rw [cellQ0, cellReferenceSource_mean_zero hΛ hζ hν, sub_zero]

end AVRegularity.CycleDamping
end

section
open MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleDamping

/-! Time integrability and elementary mean decomposition of the actual weak trace. -/

theorem weak_trace_normSq_intervalIntegrable {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → ComplexCellL2} {slice g : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice g) (J : ComplexCellL2 →L[ℝ] H) :
    IntervalIntegrable (fun t => ‖J (u t)‖ ^ 2) volume a b := by
  apply ((cellTime_normSq_intervalIntegrable hab
    ((J.comp torusHkValueCLM).comp_memLp' h.state))).congr_ae
  have hh := h.agrees.filter_mono (ae_mono (Measure.restrict_mono Ioc_subset_Icc_self le_rfl))
  rw [uIoc_of_le hab]
  filter_upwards [hh] with t ht
  simp only [Function.comp_def, ContinuousLinearMap.comp_apply, ht]

theorem cell_mean_decomposition_energy (u : ComplexCellL2) :
    ‖u‖ ^ 2 ≤ 2 * ‖cellMean u‖ ^ 2 + 2 * ‖cellQ0CLM u‖ ^ 2 := by
  have hdec : u = cellQ0CLM u + cellConstantCLM (cellMeanCLM u) := by
    change u = (u - cellConstantCLM (cellMeanCLM u)) + cellConstantCLM (cellMeanCLM u)
    exact (sub_add_cancel _ _).symm
  have hn := norm_add_le (cellQ0CLM u) (cellConstantCLM (cellMeanCLM u))
  rw [← hdec, cellConstantCLM_norm, cellMeanCLM_apply] at hn
  nlinarith only [hn, norm_nonneg u, norm_nonneg (cellMean u), norm_nonneg (cellQ0CLM u),
    sq_nonneg (‖cellMean u‖ - ‖cellQ0CLM u‖)]

theorem cosine_moment_full_norm_le (u : ComplexCellL2) (j : Fin 2) (phase : ℝ) :
    ‖cellComplexPair u (torusHkValueCLM (cellCosineH1 j phase))‖ ≤ ‖u‖ := by
  have hn : ‖torusHkValueCLM (cellCosineH1 j phase)‖ ≤ 1 := by
    have he := cellCosineH1_value_norm_sq j phase
    nlinarith only [he, norm_nonneg (torusHkValueCLM (cellCosineH1 j phase))]
  exact (pair_norm_le _ _).trans (by
    simpa only [mul_one] using (mul_le_mul_of_nonneg_left hn (norm_nonneg u)))

theorem cosine_mean_endpoint_bound (u : ComplexCellL2) (j : Fin 2) (phase : ℝ) :
    ‖cellComplexPair u (torusHkValueCLM (cellCosineH1 j phase))‖ * ‖cellMean u‖ ≤ ‖u‖ ^ 2 := by
  have hm : ‖cellMean u‖ ≤ ‖u‖ := by
    simpa only [cellMeanCLM_apply] using cellMeanCLM_norm_le u
  simpa only [pow_two] using mul_le_mul (cosine_moment_full_norm_le u j phase) hm
    (norm_nonneg _) (norm_nonneg _)

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleDamping

/-! The exact mean equation on a single stationary shear slice. -/

theorem shear_mean_generator
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2)
    (t : ℝ) (u : TorusHk 1 ℂ) (j k : Fin 2) (phase A : ℝ)
    (hshear : ∀ x i, v t x i = if i = k then A * cellCosine j phase x else 0) :
    cellComplexGenerator ⟨fun s _ => G s, v, fun i => (θ i : ℂ), 0⟩ hG V hv.1 hb t u cellH1One =
      -(realMetricSymbol (G t) θ : ℂ) * cellMean (torusHkValueCLM u) -
      Complex.I * ((A * θ k : ℝ) : ℂ) *
        cellComplexPair (torusHkValueCLM u) (torusHkValueCLM (cellCosineH1 j phase)) := by
  rw [real_shift_mean_generator hG v hv V hb θ t u, realMetricSymbol_complex,
    shear_drift_mean_moment ⟨fun s _ => G s, v, 0, 0⟩ V hv.1 hb t
      (torusHkValueCLM u) j k phase A hshear (fun i => (θ i : ℂ))]
  simp only [Complex.ofReal_mul]
  ring

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVenhance
namespace AVRegularity.CycleDamping

/-! Mean-zero reference correctors on every translated cell. -/

local instance referenceMeanZeroProbCube : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using CycleEvolution.cellCube_volume_one⟩

theorem cellPulseCorrector_mean_zero {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) {k : ℤ} (hk : Odd k) (ν t : ℝ) (y₀ : Vec 2) (j : Fin 2) :
    (∫ z in unitCube, ocPulseCorrector α q Λ ζ m ν k t
      (y₀ + ocEpsilon q Λ m • z) j) = 0 := by
  have he := (AVRegularity.Construction.Stream.ocEpsilon_pos
    (q := q) (n := m) hΛ).ne'
  have hm (i : Fin 2) : (∫ z in unitCube,
      Real.cos (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ *
        (y₀ + ocEpsilon q Λ m • z) i)) = 0 := by
    simp_rw [scaled_cell_cosine_eq _ he]
    exact cell_cosine_mean_zero i _
  rcases CycleReference.odd_int_mod_four hk with h1 | h3
  · have hc := CycleReference.pulseCorrector_horizontal_components
      (α := α) (q := q) (Λ := Λ) (m := m) (ζ := ζ) h1 ν t
    fin_cases j
    · change (∫ z in unitCube, ocPulseCorrector α q Λ ζ m ν k t
        (y₀ + ocEpsilon q Λ m • z) 0) = 0
      simp_rw [congrFun hc.1]
      simp only [integral_zero]
    · change (∫ z in unitCube, ocPulseCorrector α q Λ ζ m ν k t
        (y₀ + ocEpsilon q Λ m • z) 1) = 0
      simp_rw [congrFun hc.2]
      rw [integral_const_mul, hm, mul_zero]
  · have hc := CycleReference.pulseCorrector_vertical_components
      (α := α) (q := q) (Λ := Λ) (m := m) (ζ := ζ) h3 ν t
    fin_cases j
    · change (∫ z in unitCube, ocPulseCorrector α q Λ ζ m ν k t
        (y₀ + ocEpsilon q Λ m • z) 0) = 0
      simp_rw [congrFun hc.1]
      rw [integral_const_mul, hm, mul_zero]
    · change (∫ z in unitCube, ocPulseCorrector α q Λ ζ m ν k t
        (y₀ + ocEpsilon q Λ m • z) 1) = 0
      simp_rw [congrFun hc.2]
      simp only [integral_zero]

theorem cellReferenceValue_mean_zero {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (ν B t : ℝ) (y₀ : Vec 2) (j : Fin 2) :
    (∫ z in unitCube, cellReferenceValue α q Λ ζ m ν B y₀ t z j) = 0 := by
  classical
  let u := ocEll q Λ m ν ^ 2 * t
  simp only [cellReferenceValue, Pi.smul_apply, smul_eq_mul]
  rw [integral_const_mul]
  change -(Real.sqrt (ν / B) / ocEpsilon q Λ m) *
    (∫ z in unitCube, ocRefCorrector α q Λ ζ m ν u (y₀ + ocEpsilon q Λ m • z) j) = 0
  have hs := CycleReference.ocRefCorrector_component_sum
    (α := α) (q := q) (m := m) (ζ := ζ) hΛ ν u j
  simp_rw [congrFun hs]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
    have hz (k : {k : ℤ // Odd k}) :
        (∫ z in unitCube, ocPulseCorrector α q Λ ζ m ν k.1 u
          (y₀ + ocEpsilon q Λ m • z) j) = 0 :=
      cellPulseCorrector_mean_zero hΛ k.2 ν u y₀ j
    simp_rw [hz, mul_zero]
    simp only [Finset.sum_const_zero, mul_zero]
  · intro k hk
    have hp : Continuous (fun z : Vec 2 => ocPulseCorrector α q Λ ζ m ν k.1 u
        (y₀ + ocEpsilon q Λ m • z) j) :=
      (CycleReference.pulseCorrector_component_contDiff k.2 ν u j).continuous.comp (by fun_prop)
    exact (AVenhance.Infra.Parabolic.WeakUniqueness.weak_continuous_memL2On
      (continuous_const.mul hp)).integrable (by norm_num)

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleDamping

/-! A genuine complex periodic H¹ raw jet for each reference corrector component. -/

def cellReferenceJet (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ)
    (ν B : ℝ) (y₀ : Vec 2) (j : Fin 2) (t : ℝ) : RawJet2 1 ℂ :=
  mapRawJet Complex.ofRealCLM (CycleEvolution.cellSmoothScalarJet
    (fun z => cellReferenceValue α q Λ ζ m ν B y₀ t z j))

theorem cellReferenceJet_value (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ)
    (ν B : ℝ) (y₀ : Vec 2) (j : Fin 2) (t : ℝ) (z : Vec 2) :
    cellValue (cellReferenceJet α q Λ ζ m ν B y₀ j) t z =
      ((cellReferenceValue α q Λ ζ m ν B y₀ t z j : ℝ) : ℂ) := rfl

theorem cellReferenceJet_periodicWeak {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (ν B t : ℝ) (y₀ : Vec 2) (j : Fin 2) :
    HasPeriodicOrderedWeakJet (cellReferenceJet α q Λ ζ m ν B y₀ j t) :=
  mapRawJet_hasPeriodicWeakJet Complex.ofRealCLM _
    (cellReferenceValue_periodicWeak hΛ ν B t y₀ j)

theorem cellReferenceJet_value_memLp {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (ν B t : ℝ) (y₀ : Vec 2) (j : Fin 2) :
    MemLp (cellValue (cellReferenceJet α q Λ ζ m ν B y₀ j) t) 2
      (volume.restrict AVenhance.unitCube) :=
  (cellReferenceJet_periodicWeak hΛ ν B t y₀ j).2.1 (valueIndex2 1)

theorem cellReferenceJet_value_periodic {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (ν B t : ℝ) (y₀ : Vec 2) (j : Fin 2) :
    AVenhance.IsZ2Periodic (cellValue (cellReferenceJet α q Λ ζ m ν B y₀ j) t) :=
  (cellReferenceJet_periodicWeak hΛ ν B t y₀ j).1 (valueIndex2 1)

theorem cellReferenceJet_mean_zero {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (ν B t : ℝ) (y₀ : Vec 2) (j : Fin 2) :
    cellMean (cellValue (cellReferenceJet α q Λ ζ m ν B y₀ j) t) = 0 := by
  change cellMean (fun z => ((cellReferenceValue α q Λ ζ m ν B y₀ t z j : ℝ) : ℂ)) = 0
  rw [cellMean, integral_complex_ofReal, cellReferenceValue_mean_zero hΛ]
  rfl

end AVRegularity.CycleDamping
end

section
open Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open AVenhance.Infra.Classical
namespace AVRegularity.CycleDamping

/-! Continuous scalar time coefficients of the actual reference raw jet. -/

theorem cellReferenceAmplitude_continuous {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν B : ℝ) (j : Fin 2) :
    Continuous (cellReferenceAmplitude α q Λ ζ m ν B j) := by
  have hr := refCorrector_joint_continuous (α := α) (q := q) (m := m) hΛ hζ ν j
  have ha : Continuous (fun t : ℝ => (ocEll q Λ m ν ^ 2 * t, (0 : Vec 2))) := by fun_prop
  change Continuous (fun t : ℝ => -(Real.sqrt (ν / B) / ocEpsilon q Λ m) *
    ocRefCorrector α q Λ ζ m ν (ocEll q Λ m ν ^ 2 * t) 0 j)
  simpa only [Function.comp_def, Pi.mul_def] using
    continuous_const.mul (hr.comp ha)

theorem cellReferenceJet_single_mode {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (ν B t : ℝ) (y₀ : Vec 2) (j : Fin 2) :
    cellReferenceJet α q Λ ζ m ν B y₀ j t =
      fun a z => ((cellReferenceAmplitude α q Λ ζ m ν B j t : ℝ) : ℂ) *
        ((CycleEvolution.cellSmoothScalarJet (fun x => Real.cos
          (2 * Real.pi * (x (1 - j) + y₀ (1 - j) / ocEpsilon q Λ m))) a z : ℝ) : ℂ) := by
  unfold cellReferenceJet
  have he : (fun z => cellReferenceValue α q Λ ζ m ν B y₀ t z j) =
      fun z => cellReferenceAmplitude α q Λ ζ m ν B j t * Real.cos
        (2 * Real.pi * (z (1 - j) + y₀ (1 - j) / ocEpsilon q Λ m)) := by
    funext z
    exact cellReferenceValue_single_mode hΛ ν B t y₀ z j
  rw [he, cellSmoothScalarJet_const_mul _ _ (by fun_prop)]
  funext a z
  simp only [mapRawJet, Pi.smul_apply, smul_eq_mul, Complex.ofRealCLM_apply, Complex.ofReal_mul]

theorem cellReferenceJet_joint_continuous {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν B : ℝ) (y₀ : Vec 2)
    (j : Fin 2) (a : JetIndex2 1) :
    Continuous (fun p : ℝ × Vec 2 => cellReferenceJet α q Λ ζ m ν B y₀ j p.1 a p.2) := by
  simp_rw [cellReferenceJet_single_mode hΛ]
  have ht : Continuous (fun p : ℝ × Vec 2 =>
      ((cellReferenceAmplitude α q Λ ζ m ν B j p.1 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp ((cellReferenceAmplitude_continuous hΛ hζ ν B j).comp continuous_fst)
  have hx : Continuous (fun z : Vec 2 => CycleEvolution.cellSmoothScalarJet
      (fun x => Real.cos (2 * Real.pi * (x (1 - j) + y₀ (1 - j) / ocEpsilon q Λ m))) a z) :=
    (GalerkinGenerator.classicalWordDerivative_smooth _ _ (by fun_prop)).continuous
  exact ht.mul (Complex.continuous_ofReal.comp (hx.comp continuous_snd))

end AVRegularity.CycleDamping
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleDamping

/-! Genuine weak solutions on a stationary shear interval control the integrated spatial mean. -/

theorem shear_weak_mean_integral {a b : ℝ} (hab : a ≤ b)
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2) (hθ : ∀ i, |θ i| ≤ Real.pi)
    (j k : Fin 2) (hkj : k ≠ j) (phase A L : ℝ)
    (hK : 0 < A * θ k) (hL : 28 * Real.pi ^ 2 + A * θ k ≤ A * θ k * L)
    (hshear : ∀ t ∈ Icc a b, ∀ x i, v t x i = if i = k then A * cellCosine j phase x else 0)
    {u : ℝ → ComplexCellL2} {slice : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice (fun t =>
      cellDualDerivative ⟨fun s _ => G s, v, fun i => (θ i : ℂ), 0⟩ hG V hv.1 hb t (slice t) 0 0)) :
    (A * θ k / 4) * (∫ t in a..b, ‖cellMean (u t)‖ ^ 2) ≤
      2 * ‖u a‖ ^ 2 + (A * θ k) * (1 + 4 * L ^ 2) *
        (∫ t in a..b, ‖cellQ0CLM (u t)‖ ^ 2) := by
  let C : CellCoefficients := ⟨fun s _ => G s, v, fun i => (θ i : ℂ), 0⟩
  let m : ℝ → ℂ := fun t => cellMean (u t)
  let z : ℝ → ℂ := fun t => cellComplexPair (u t) (torusHkValueCLM (cellCosineH1 j phase))
  let dm : ℝ → ℂ := fun t => cellComplexGenerator C hG V hv.1 hb t (slice t) cellH1One
  let dz : ℝ → ℂ := fun t => cellComplexGenerator C hG V hv.1 hb t (slice t) (cellCosineH1 j phase)
  have hm : StrongTimeRegularity a b m dm := by
    simpa only [m, dm, C, cellH1One_value, cellComplexPair_one,
      homogeneous_dual_complex_generator] using weak_complex_test_strongTime hab h cellH1One
  have hz : StrongTimeRegularity a b z dz := by
    simpa only [z, dz, C, homogeneous_dual_complex_generator] using
      weak_complex_test_strongTime hab h (cellCosineH1 j phase)
  have hmi : IntervalIntegrable (fun t => ‖m t‖ ^ 2) volume a b := by
    simpa only [m, cellMeanCLM_apply] using weak_trace_normSq_intervalIntegrable hab h cellMeanCLM
  have hqi := weak_trace_normSq_intervalIntegrable hab h cellQ0CLM
  have hA : ∀ᵐ t ∂volume.restrict (Icc a b), 0 ≤ realMetricSymbol (G t) θ :=
    Filter.Eventually.of_forall (fun t => (realMetricSymbol_bounds hG θ hθ t).1)
  have hAL : ∀ᵐ t ∂volume.restrict (Icc a b), realMetricSymbol (G t) θ ≤ A * θ k * L := by
    apply Filter.Eventually.of_forall
    intro t
    have he := (realMetricSymbol_bounds hG θ hθ t).2
    have hp : 0 ≤ Real.pi ^ 2 := sq_nonneg _
    linarith only [he, hL, hK, hp]
  refine shear_moment_integral_bound hab m dm z dz (fun t => ‖cellQ0CLM (u t)‖)
    (fun t => realMetricSymbol (G t) θ) (A * θ k) L (‖u a‖ ^ 2) hm hz hK hA hAL hmi hqi
    ?_ ?_ ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall (fun t => norm_nonneg _)
  · exact Filter.Eventually.of_forall (fun t => cosine_moment_norm_le (u t) j phase)
  · filter_upwards [h.agrees, ae_restrict_mem measurableSet_Icc] with t ht hti
    dsimp only [dm, m, z, C]
    rw [shear_mean_generator hG v hv V hb θ t (slice t) j k phase A (hshear t hti), ← ht]
  · filter_upwards [h.agrees, ae_restrict_mem measurableSet_Icc] with t ht hti
    have he := shear_cosine_error_norm_le hG v hv V hb θ hθ t (slice t) j k hkj phase A (hshear t hti)
    simp only [← ht, abs_of_pos hK] at he
    exact he.trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  · exact cosine_mean_endpoint_bound (u a) j phase
  · have he := cosine_mean_endpoint_bound (u b) j phase
    have hc := real_shift_weak_contraction hab hG v hv V hb θ h
    have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hc
    exact he.trans hs

end AVRegularity.CycleDamping
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleDamping

/-! The constructed drift is a stationary single shear on each complete core. -/

theorem shear_cell_amplitude_identity {α q : ℝ} {Λ m : ℕ} (hΛ : 1 ≤ Λ) (ν : ℝ) :
    (ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m) *
      (2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) * (ocEpsilon q Λ m)⁻¹) =
      2 * Real.pi * ocA α q Λ m * ocEll q Λ m ν ^ 2 := by
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  have hp : ocEpsilon q Λ m ^ (1 + α) / ocEpsilon q Λ m ^ 2 = ocEpsilon q Λ m ^ (α - 1) := by
    rw [← Real.rpow_two, ← Real.rpow_sub he]
    congr 1
    ring
  unfold ocA
  rw [show 1 + α - 2 = α - 1 by ring, ← hp]
  field_simp

theorem ocCellDrift_on_horizontal_core {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (y₀ : Vec 2)
    (l n : ℤ) (hcore : IsOCCompleteCore α q Λ m l n) (hn : n % 4 = 1)
    (t : ℝ) (ht : ocEll q Λ m ν ^ 2 * t ∈
      Set.Icc (((n : ℝ) - 1 / 3) * ocTau α q Λ m) (((n : ℝ) + 1 / 3) * ocTau α q Λ m))
    (z : Vec 2) (i : Fin 2) :
    ocCellDrift α q Λ ζ m ν y₀ t z i =
      if i = 1 then (2 * Real.pi * ocA α q Λ m * ocEll q Λ m ν ^ 2) *
        cellCosine 0 (y₀ 0 / ocEpsilon q Λ m) z else 0 := by
  have hp := CycleReference.pulse_eq_one_on_completeCore hΛ hζ l n hcore _ ht
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  simp only [ocCellDrift, CycleReference.pulseStreamVel_eq_active hΛ hζ hcore.1
    (show ocPulse α q Λ ζ m n (ocEll q Λ m ν ^ 2 * t) ≠ 0 by rw [hp]; norm_num),
    hp, one_smul, CycleReference.ocShearVel_horizontal hn, Pi.smul_apply, smul_eq_mul]
  fin_cases i
  · norm_num
  · norm_num [cellCosine]
    have hc := scaled_cell_cosine_eq (ocEpsilon q Λ m) he.ne' y₀ z (0 : Fin 2)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hc
    rw [hc, ← mul_assoc, shear_cell_amplitude_identity hΛ]

theorem ocCellDrift_on_vertical_core {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (y₀ : Vec 2)
    (l n : ℤ) (hcore : IsOCCompleteCore α q Λ m l n) (hn : n % 4 = 3)
    (t : ℝ) (ht : ocEll q Λ m ν ^ 2 * t ∈
      Set.Icc (((n : ℝ) - 1 / 3) * ocTau α q Λ m) (((n : ℝ) + 1 / 3) * ocTau α q Λ m))
    (z : Vec 2) (i : Fin 2) :
    ocCellDrift α q Λ ζ m ν y₀ t z i =
      if i = 0 then -(2 * Real.pi * ocA α q Λ m * ocEll q Λ m ν ^ 2) *
        cellCosine 1 (y₀ 1 / ocEpsilon q Λ m) z else 0 := by
  have hp := CycleReference.pulse_eq_one_on_completeCore hΛ hζ l n hcore _ ht
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  simp only [ocCellDrift, CycleReference.pulseStreamVel_eq_active hΛ hζ hcore.1
    (show ocPulse α q Λ ζ m n (ocEll q Λ m ν ^ 2 * t) ≠ 0 by rw [hp]; norm_num),
    hp, one_smul, CycleReference.ocShearVel_vertical hn, Pi.smul_apply, smul_eq_mul]
  fin_cases i
  · norm_num [cellCosine]
    have hc := scaled_cell_cosine_eq (ocEpsilon q Λ m) he.ne' y₀ z (1 : Fin 2)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hc
    rw [hc, ← mul_assoc, shear_cell_amplitude_identity hΛ]
  · norm_num

end AVRegularity.CycleDamping
end

section
open Homogenization
namespace AVRegularity.CycleDamping

/-! One common orientation formula for both constructed complete-core shears. -/

theorem ocCellDrift_on_oriented_core {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (y₀ : Vec 2)
    (j : Fin 2) (l n : ℤ) (hcore : IsOCCompleteCore α q Λ m l n)
    (hn : n % 4 = if j = 0 then 3 else 1)
    (t : ℝ) (ht : ocEll q Λ m ν ^ 2 * t ∈
      Set.Icc (((n : ℝ) - 1 / 3) * ocTau α q Λ m) (((n : ℝ) + 1 / 3) * ocTau α q Λ m))
    (z : Vec 2) (i : Fin 2) :
    ocCellDrift α q Λ ζ m ν y₀ t z i =
      if i = j then ((if j = 0 then (-1 : ℝ) else 1) *
        (2 * Real.pi * ocA α q Λ m * ocEll q Λ m ν ^ 2)) *
        cellCosine (1 - j) (y₀ (1 - j) / ocEpsilon q Λ m) z else 0 := by
  fin_cases j
  · norm_num at hn ⊢
    simpa only [neg_mul] using ocCellDrift_on_vertical_core hΛ hζ ν y₀ l n hcore hn t ht z i
  · norm_num at hn ⊢
    exact ocCellDrift_on_horizontal_core hΛ hζ ν y₀ l n hcore hn t ht z i

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.CycleDamping

/-! Periodicity and weak divergence freedom of the actual constructed cell drift. -/

theorem ocCellDrift_periodic {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν t : ℝ) (y₀ : Vec 2) :
    IsZ2Periodic (ocCellDrift α q Λ ζ m ν y₀ t) := by
  classical
  by_cases hp : ∃ k : ℤ, Odd k ∧ ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t) ≠ 0
  · obtain ⟨k, hk, hp⟩ := hp
    intro n z
    ext i
    simp only [ocCellDrift, CycleReference.pulseStreamVel_eq_active hΛ hζ hk hp,
      Pi.smul_apply, smul_eq_mul]
    have he := cell_shear_component_periodic (α := α) (q := q) (m := m) hΛ hk y₀ i n z
    exact congrArg (fun r : ℝ => ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m *
      (ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t) * r)) he
  · have hz : ∀ k : ℤ, Odd k → ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t) = 0 := by
      intro k hk
      by_contra hn
      exact hp ⟨k, hk, hn⟩
    intro n z
    simp only [ocCellDrift, CycleReference.pulseStreamVel_eq_zero_of_quiet hz, smul_zero]

theorem ocCellDrift_weak_divergence {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν t : ℝ) (y₀ : Vec 2)
    (ψ : TorusHkFunction 1 ℝ) :
    (∫ x in unitCube, ∑ i : Fin 2, ocCellDrift α q Λ ζ m ν y₀ t x i *
      ψ.jet ⟨⟨1, by decide⟩, fun _ => i⟩ x) = 0 := by
  classical
  by_cases hp : ∃ k : ℤ, Odd k ∧ ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t) ≠ 0
  · obtain ⟨k, hk, hp⟩ := hp
    have hweak := smooth_divergence_free_weak
      (fun z => ocShearVel α q Λ m k (y₀ + ocEpsilon q Λ m • z))
      (cell_shear_component_contDiff hk y₀) (cell_shear_component_periodic hΛ hk y₀)
      (fun x => by simp_rw [cell_shear_diagonal_derivative_zero hk]; simp) ψ
    simp only [ocCellDrift, CycleReference.pulseStreamVel_eq_active hΛ hζ hk hp,
      Pi.smul_apply, smul_eq_mul]
    simp_rw [← mul_assoc, mul_assoc (ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m *
      ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t)), ← Finset.mul_sum]
    rw [integral_const_mul, hweak, mul_zero]
  · have hz : ∀ k : ℤ, Odd k → ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t) = 0 := by
      intro k hk
      by_contra hn
      exact hp ⟨k, hk, hn⟩
    simp only [ocCellDrift, CycleReference.pulseStreamVel_eq_zero_of_quiet hz,
      smul_zero, Pi.zero_apply, zero_mul, Finset.sum_const_zero, integral_zero]

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.CycleDamping

/-! The actual switching residual obeys a uniform cell-time source norm bound. -/

theorem cellSwitchResidual_ul_bound {α q : ℝ} {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, 0 < C ∧ ∀ Λ : ℕ, 1 ≤ Λ → ∀ m : ℕ, ∀ ν : ℝ, 0 < ν →
      6 ≤ ocMu q Λ m ν * ocTau α q Λ m → ∀ y₀ : Vec 2, ∀ j : Fin 2,
      cellUlNorm Set.univ (fun t x =>
        ((cellSwitchResidual α q Λ ζ m ν (ocMeanFlux α q Λ ζ m ν) y₀ t x j : ℝ) : ℂ)) ≤
      ENNReal.ofReal (C * (ocEll q Λ m ν ^ 2 / ocTau α q Λ m *
        Real.exp (-(Real.pi ^ 2) * ocTau α q Λ m / (3 * ocEll q Λ m ν ^ 2)))) := by
  obtain ⟨C, hC, hbound⟩ := cellSwitchResidual_uniform_bound (α := α) (q := q) hζ
  refine ⟨C, hC, ?_⟩
  intro Λ hΛ m ν hν hr y₀ j
  have hc := Complex.continuous_ofReal.comp
    (cellSwitchResidual_component_continuous (α := α) (q := q) (m := m) hΛ hζ hν
      (ocMeanFlux α q Λ ζ m ν) y₀ j)
  apply cellUlNorm_le_uniform_bound _ (fun t =>
    (hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  intro t x
  change ‖((cellSwitchResidual α q Λ ζ m ν (ocMeanFlux α q Λ ζ m ν) y₀ t x j : ℝ) : ℂ)‖ ≤ _
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact (vec_coordinate_abs_le _ j).trans (hbound Λ hΛ m ν hν hr y₀ t x)

end AVRegularity.CycleDamping
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleDamping

/-! A literal global bound and the full admissible-drift predicate for the constructed cell drift. -/

theorem shear_component_abs_bound {α q : ℝ} {Λ m : ℕ} {k : ℤ} (hk : Odd k)
    (y : Vec 2) (i : Fin 2) :
    |ocShearVel α q Λ m k y i| ≤
      |2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) * (ocEpsilon q Λ m)⁻¹| := by
  have hc (c z : ℝ) : |c * Real.cos z| ≤ |c| := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one z) (abs_nonneg c)).trans_eq
      (mul_one _)
  rcases CycleReference.odd_int_mod_four hk with h1 | h3
  · simp only [CycleReference.ocShearVel_horizontal h1]
    fin_cases i
    · change |(0 : ℝ)| ≤ _
      rw [abs_zero]
      exact abs_nonneg _
    · exact hc _ _
  · simp only [CycleReference.ocShearVel_vertical h3]
    fin_cases i
    · change |(-_) * Real.cos _| ≤ _
      simpa only [abs_neg] using hc
        (-(2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) * (ocEpsilon q Λ m)⁻¹))
        (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y 1)
    · change |(0 : ℝ)| ≤ _
      rw [abs_zero]
      exact abs_nonneg _

theorem ocCellDrift_component_abs_bound {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν t : ℝ) (y₀ z : Vec 2) (i : Fin 2) :
    |ocCellDrift α q Λ ζ m ν y₀ t z i| ≤
      |ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m| *
        |2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) * (ocEpsilon q Λ m)⁻¹| := by
  classical
  by_cases hp : ∃ k : ℤ, Odd k ∧ ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t) ≠ 0
  · obtain ⟨k, hk, hp⟩ := hp
    have hr := CycleReference.ocPulse_range (α := α) (q := q) (m := m) (Λ := Λ)
      hζ k (ocEll q Λ m ν ^ 2 * t)
    simp only [ocCellDrift, CycleReference.pulseStreamVel_eq_active hΛ hζ hk hp,
      Pi.smul_apply, smul_eq_mul, abs_mul]
    rw [abs_of_nonneg hr.1]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    calc
      _ ≤ 1 * |ocShearVel α q Λ m k (y₀ + ocEpsilon q Λ m • z) i| :=
        mul_le_mul_of_nonneg_right hr.2 (abs_nonneg _)
      _ ≤ _ := by
        rw [one_mul]
        simpa only [abs_mul] using shear_component_abs_bound (α := α) (q := q)
          (Λ := Λ) (m := m) hk (y₀ + ocEpsilon q Λ m • z) i
  · have hz : ∀ k : ℤ, Odd k → ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t) = 0 := by
      intro k hk
      by_contra hn
      exact hp ⟨k, hk, hn⟩
    simp only [ocCellDrift, CycleReference.pulseStreamVel_eq_zero_of_quiet hz,
      smul_zero, Pi.zero_apply, abs_zero]
    positivity

theorem ocCellDrift_isCellDrift {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (y₀ : Vec 2) :
    IsCellDrift (ocCellDrift α q Λ ζ m ν y₀) := by
  refine ⟨(ocCellDrift_joint_continuous hΛ hζ ν y₀).measurable, ?_,
    (fun t => ocCellDrift_periodic hΛ hζ ν t y₀),
    (fun t ψ => ocCellDrift_weak_divergence hΛ hζ ν t y₀ ψ)⟩
  let A := |ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m| *
    |2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) * (ocEpsilon q Λ m)⁻¹|
  refine ⟨2 * A, ?_⟩
  intro t z
  have h0 := ocCellDrift_component_abs_bound (α := α) (q := q) (m := m) hΛ hζ ν t y₀ z 0
  have h1 := ocCellDrift_component_abs_bound (α := α) (q := q) (m := m) hΛ hζ ν t y₀ z 1
  change |ocCellDrift α q Λ ζ m ν y₀ t z 0| ≤ A at h0
  change |ocCellDrift α q Λ ζ m ν y₀ t z 1| ≤ A at h1
  have hs0 := sq_le_sq₀ (abs_nonneg _) (show 0 ≤ A by positivity) |>.mpr h0
  have hs1 := sq_le_sq₀ (abs_nonneg _) (show 0 ≤ A by positivity) |>.mpr h1
  simp only [sq_abs] at hs0 hs1
  simp only [Fin.sum_univ_two]
  nlinarith only [hs0, hs1, sq_nonneg A]

end AVRegularity.CycleDamping
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleDamping

/-! Full time-energy observability on a genuine stationary shear interval. -/

theorem shear_weak_time_energy {a b : ℝ} (hab : a ≤ b)
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2) (hθ : ∀ i, |θ i| ≤ Real.pi)
    (j k : Fin 2) (hkj : k ≠ j) (phase A L : ℝ)
    (hK : 0 < A * θ k) (hL : 28 * Real.pi ^ 2 + A * θ k ≤ A * θ k * L)
    (hshear : ∀ t ∈ Icc a b, ∀ x i, v t x i = if i = k then A * cellCosine j phase x else 0)
    {u : ℝ → ComplexCellL2} {slice : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice (fun t =>
      cellDualDerivative ⟨fun s _ => G s, v, fun i => (θ i : ℂ), 0⟩ hG V hv.1 hb t (slice t) 0 0)) :
    (A * θ k) * Real.pi ^ 2 * (∫ t in a..b, ‖u t‖ ^ 2) ≤
      (16 * Real.pi ^ 2 + 4 * (A * θ k) * (10 + 32 * L ^ 2)) * ‖u a‖ ^ 2 := by
  have hUi : IntervalIntegrable (fun t => ‖u t‖ ^ 2) volume a b := by
    simpa only [ContinuousLinearMap.id_apply] using
      weak_trace_normSq_intervalIntegrable hab h (ContinuousLinearMap.id ℝ ComplexCellL2)
  have hmi : IntervalIntegrable (fun t => ‖cellMean (u t)‖ ^ 2) volume a b := by
    simpa only [cellMeanCLM_apply] using weak_trace_normSq_intervalIntegrable hab h cellMeanCLM
  have hqi := weak_trace_normSq_intervalIntegrable hab h cellQ0CLM
  have hsum := intervalIntegral.integral_mono_ae_restrict hab hUi
    ((hmi.const_mul 2).add (hqi.const_mul 2))
    (Filter.Eventually.of_forall (fun t => cell_mean_decomposition_energy (u t)))
  rw [intervalIntegral.integral_add (hmi.const_mul 2) (hqi.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hsum
  have hm := shear_weak_mean_integral hab hG v hv V hb θ hθ j k hkj phase A L hK hL hshear h
  have hq := real_shift_integrated_meanFree_gap hab hG v hv V hb θ hθ h
  have hsumK := mul_le_mul_of_nonneg_left hsum hK.le
  have ht : (A * θ k) * (∫ t in a..b, ‖u t‖ ^ 2) ≤
      16 * ‖u a‖ ^ 2 + (A * θ k) * (10 + 32 * L ^ 2) *
        (∫ t in a..b, ‖cellQ0CLM (u t)‖ ^ 2) := by
    nlinarith only [hsumK, hm]
  have htp := mul_le_mul_of_nonneg_left ht (sq_nonneg Real.pi)
  have hqp := mul_le_mul_of_nonneg_left hq
    (by positivity : 0 ≤ (A * θ k) * (10 + 32 * L ^ 2))
  nlinarith only [htp, hqp]

end AVRegularity.CycleDamping
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping

/-! Half-norm contraction for a sufficiently long stationary shear interval. -/

theorem shear_weak_half_contraction {a b : ℝ} (hab : a ≤ b)
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2) (hθ : ∀ i, |θ i| ≤ Real.pi)
    (j k : Fin 2) (hkj : k ≠ j) (phase A L : ℝ)
    (hK : 0 < A * θ k) (hL : 28 * Real.pi ^ 2 + A * θ k ≤ A * θ k * L)
    (hlong : 4 * (16 * Real.pi ^ 2 + 4 * (A * θ k) * (10 + 32 * L ^ 2)) ≤
      (A * θ k) * Real.pi ^ 2 * (b - a))
    (hshear : ∀ t ∈ Icc a b, ∀ x i, v t x i = if i = k then A * cellCosine j phase x else 0)
    {u : ℝ → ComplexCellL2} {slice : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice (fun t =>
      cellDualDerivative ⟨fun s _ => G s, v, fun i => (θ i : ℂ), 0⟩ hG V hv.1 hb t (slice t) 0 0)) :
    ‖u b‖ ≤ (1 / 2 : ℝ) * ‖u a‖ := by
  have hUi : IntervalIntegrable (fun t => ‖u t‖ ^ 2) volume a b := by
    simpa only [ContinuousLinearMap.id_apply] using
      weak_trace_normSq_intervalIntegrable hab h (ContinuousLinearMap.id ℝ ComplexCellL2)
  have hs (t : ℝ) (ht : t ∈ Icc a b) : ‖u b‖ ^ 2 ≤ ‖u t‖ ^ 2 := by
    have hm := real_shift_weak_contraction ht.2 hG v hv V hb θ
      (h.mono (Icc_subset_Icc ht.1 le_rfl))
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hm
  have hlow := intervalIntegral.integral_mono_on hab intervalIntegrable_const hUi hs
  rw [intervalIntegral.integral_const] at hlow
  simp only [smul_eq_mul] at hlow
  have he := shear_weak_time_energy hab hG v hv V hb θ hθ j k hkj phase A L hK hL hshear h
  have hm := mul_le_mul_of_nonneg_left hlow (by positivity : 0 ≤ (A * θ k) * Real.pi ^ 2)
  have hlong' := mul_le_mul_of_nonneg_right hlong (sq_nonneg ‖u b‖)
  have hR : 0 < 16 * Real.pi ^ 2 + 4 * (A * θ k) * (10 + 32 * L ^ 2) := by positivity
  have hsq : 4 * ‖u b‖ ^ 2 ≤ ‖u a‖ ^ 2 := by
    apply (mul_le_mul_iff_right₀ hR).mp
    nlinarith only [hm, he, hlong']
  nlinarith only [hsq, norm_nonneg (u a), norm_nonneg (u b)]

/-! A contrast-independent contraction time for either sign of a stationary shear coupling. -/

theorem uniform_stationary_shear_contraction (K₀ : ℝ) (hK₀ : 0 < K₀) :
    ∃ d : ℝ, 0 < d ∧ ∀ a b : ℝ, a ≤ b → d ≤ b - a →
      ∀ (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
        (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
        (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
        (θ : Vec 2), (∀ i, |θ i| ≤ Real.pi) →
      ∀ (j k : Fin 2), k ≠ j → ∀ phase A : ℝ, K₀ ≤ |A * θ k| →
      (∀ t ∈ Icc a b, ∀ x i, v t x i = if i = k then A * cellCosine j phase x else 0) →
      ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ),
        CellWeakHilbertCurve a b u slice (fun t =>
          cellDualDerivative ⟨fun s _ => G s, v, fun i => (θ i : ℂ), 0⟩ hG V hv.1 hb t (slice t) 0 0) →
        ‖u b‖ ≤ (1 / 2 : ℝ) * ‖u a‖ := by
  obtain ⟨L, d, _hL, hd, hc⟩ := uniform_shear_constants K₀ hK₀
  refine ⟨d, hd, ?_⟩
  intro a b hab hlong G hG v hv V hb θ hθ j k hkj phase A hcouple hshear u slice h
  obtain ⟨phase', A', heq, hshear'⟩ := stationary_shear_sign_normalization v j k phase A (θ k) hshear
  have hK : 0 < A' * θ k := by rw [heq]; exact hK₀.trans_le hcouple
  have hcoeff := hc (A' * θ k) (by rw [heq]; exact hcouple)
  have hlength : 4 * (16 * Real.pi ^ 2 + 4 * (A' * θ k) * (10 + 32 * L ^ 2)) ≤
      (A' * θ k) * Real.pi ^ 2 * (b - a) := hcoeff.2.trans
    (mul_le_mul_of_nonneg_left hlong (by positivity))
  exact shear_weak_half_contraction hab hG v hv V hb θ hθ j k hkj phase' A' L hK
    hcoeff.1 hlength hshear' h

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.CycleDamping

/-! Joint measurability and finite uniformly local norm of the actual cell forcing. -/

theorem cellForcing_joint_continuous {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν B : ℝ) (y₀ : Vec 2) (j : Fin 2) :
    Continuous (fun p : ℝ × Vec 2 => ((Real.sqrt (ν / B) *
      ocCellDrift α q Λ ζ m ν y₀ p.1 p.2 j : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.comp (continuous_const.mul
    ((continuous_apply j).comp (ocCellDrift_joint_continuous hΛ hζ ν y₀)))

theorem cellForcing_ul_finite {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν B : ℝ) (y₀ : Vec 2) (j : Fin 2) :
    cellUlNorm Set.univ (fun t x => ((Real.sqrt (ν / B) *
      ocCellDrift α q Λ ζ m ν y₀ t x j : ℝ) : ℂ)) < ⊤ := by
  let A := |Real.sqrt (ν / B)| * (|ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m| *
    |2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) * (ocEpsilon q Λ m)⁻¹|)
  apply (cellUlNorm_le_uniform_bound _ (fun t =>
    ((cellForcing_joint_continuous hΛ hζ ν B y₀ j).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable) A ?_).trans_lt
    ENNReal.ofReal_lt_top
  intro t x
  change ‖((Real.sqrt (ν / B) * ocCellDrift α q Λ ζ m ν y₀ t x j : ℝ) : ℂ)‖ ≤ A
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (ocCellDrift_component_abs_bound hΛ hζ ν t y₀ x j)
    (abs_nonneg _)

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
open scoped ENNReal
namespace AVRegularity.CycleDamping

/-! Finite all-time energy of the actual normalized reference corrector. -/

theorem cellReferenceJet_energy_finite {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (hrelax : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m) (y₀ : Vec 2) (j : Fin 2) :
    cellEnergyNorm Set.univ
      (cellReferenceJet α q Λ ζ m ν (ocMeanFlux α q Λ ζ m ν) y₀ j) < ⊤ := by
  let f : Vec 2 → ℝ := fun x => Real.cos
    (2 * Real.pi * (x (1 - j) + y₀ (1 - j) / ocEpsilon q Λ m))
  have hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f := by fun_prop
  have hp : AVenhance.IsZ2Periodic f := by
    have he := (AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ).ne'
    have h := scaled_cell_cosine_periodic (ocEpsilon q Λ m) he y₀ (1 - j)
    simpa only [scaled_cell_cosine_eq _ he] using h
  let J : RawJet2 1 ℂ := mapRawJet Complex.ofRealCLM (CycleEvolution.cellSmoothScalarJet f)
  have hJ : HasPeriodicOrderedWeakJet J :=
    mapRawJet_hasPeriodicWeakJet Complex.ofRealCLM _
      (CycleEvolution.cellSmoothScalarJet_periodicWeak f hf hp)
  have heq : cellReferenceJet α q Λ ζ m ν (ocMeanFlux α q Λ ζ m ν) y₀ j =
      fun t => ((cellReferenceAmplitude α q Λ ζ m ν (ocMeanFlux α q Λ ζ m ν) j t : ℝ) : ℂ) • J := by
    funext t a z
    rw [cellReferenceJet_single_mode hΛ]
    rfl
  rw [heq]
  apply fixed_mode_energy_finite J hJ _
    (ENNReal.ofReal (Real.sqrt (2 / ((1 - Real.exp (-2)) / 96)) / (2 * Real.pi)))
    ENNReal.ofReal_lt_top
  intro t
  rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
  exact ENNReal.ofReal_le_ofReal (cellReferenceAmplitude_uniform_bound hΛ hζ hν hrelax j t)

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleDamping

/-! Exact spatial pairing of the reference cell equation with a weak H¹ test. -/

def referenceWeakRhs (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ)
    (ν B : ℝ) (y₀ : Vec 2) (j : Fin 2) (ψ : TorusHkFunction 1 ℂ)
    (t : ℝ) (x : Vec 2) : ℂ :=
  -(∑ i : Fin 2, cellGradComp (cellReferenceJet α q Λ ζ m ν B y₀ j t) i x *
      ψ.jet ⟨⟨1, by decide⟩, fun _ => i⟩ x) +
    ((Real.sqrt (ν / B) * ocCellDrift α q Λ ζ m ν y₀ t x j +
      cellSwitchResidual α q Λ ζ m ν B y₀ t x j : ℝ) : ℂ) *
        ψ.jet (valueIndex2 1) x

theorem cellReferenceJet_grad (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ)
    (ν B : ℝ) (y₀ : Vec 2) (j i : Fin 2) (t : ℝ) (x : Vec 2) :
    cellGradComp (cellReferenceJet α q Λ ζ m ν B y₀ j t) i x =
      ((fderiv ℝ (fun z => cellReferenceValue α q Λ ζ m ν B y₀ t z j)
        x (basisVec i) : ℝ) : ℂ) := rfl

theorem referenceWeakRhs_integrable {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (B t : ℝ) (y₀ : Vec 2) (j : Fin 2) (ψ : TorusHkFunction 1 ℂ) :
    Integrable (referenceWeakRhs α q Λ ζ m ν B y₀ j ψ t)
      (volume.restrict AVenhance.unitCube) := by
  have hi (i : Fin 2) := memLp_one_iff_integrable.mp
    (((cellReferenceJet_periodicWeak (α := α) (q := q) (m := m) (ζ := ζ) hΛ ν B t y₀ j).2.1
      ⟨⟨1, by decide⟩, fun _ => i⟩).mul
      (ψ.hasPeriodicWeakJet.2.1 ⟨⟨1, by decide⟩, fun _ => i⟩) : MemLp _ 1 _)
  have hs := continuous_weak_pair_integrable
    (fun x => Real.sqrt (ν / B) * ocCellDrift α q Λ ζ m ν y₀ t x j +
      cellSwitchResidual α q Λ ζ m ν B y₀ t x j) ?_
    (ψ.jet (valueIndex2 1)) (ψ.hasPeriodicWeakJet.2.1 (valueIndex2 1))
  · exact (integrable_finsetSum Finset.univ (fun i _ => hi i)).neg.add hs
  · simp_rw [cellReferenceSource_single_mode hΛ hζ hν]
    fun_prop

theorem referenceWeakRhs_pair {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (B t : ℝ) (y₀ : Vec 2) (j : Fin 2) (ψ : TorusHkFunction 1 ℂ) :
    (∫ x in AVenhance.unitCube, referenceWeakRhs α q Λ ζ m ν B y₀ j ψ t x) =
      ∫ x in AVenhance.unitCube,
        ((deriv (fun s => cellReferenceValue α q Λ ζ m ν B y₀ s x j) t : ℝ) : ℂ) *
          ψ.jet (valueIndex2 1) x := by
  let Q : Vec 2 → ℝ := fun x => cellReferenceValue α q Λ ζ m ν B y₀ t x j
  have hQ := cellReferenceValue_contDiff (α := α) (q := q) (m := m) (ζ := ζ) hΛ ν B t y₀ j
  have hi (i : Fin 2) := continuous_weak_pair_integrable
    (fun x => fderiv ℝ Q x (basisVec i))
    (AVenhance.Infra.Classical.GalerkinGenerator.classicalWordDerivative_smooth
      [i] Q hQ).continuous (ψ.jet ⟨⟨1, by decide⟩, fun _ => i⟩)
    (ψ.hasPeriodicWeakJet.2.1 ⟨⟨1, by decide⟩, fun _ => i⟩)
  have hs := continuous_weak_pair_integrable
    (fun x => Real.sqrt (ν / B) * ocCellDrift α q Λ ζ m ν y₀ t x j +
      cellSwitchResidual α q Λ ζ m ν B y₀ t x j) (by
        simp_rw [cellReferenceSource_single_mode hΛ hζ hν]; fun_prop)
    (ψ.jet (valueIndex2 1)) (ψ.hasPeriodicWeakJet.2.1 (valueIndex2 1))
  unfold referenceWeakRhs
  simp_rw [cellReferenceJet_grad]
  have hgi : Integrable (fun x => -(∑ i : Fin 2,
      ((fderiv ℝ Q x (basisVec i) : ℝ) : ℂ) *
        ψ.jet ⟨⟨1, by decide⟩, fun _ => i⟩ x))
      (volume.restrict AVenhance.unitCube) := by
    simpa only [Pi.neg_def] using
      (integrable_finsetSum Finset.univ (fun i _ => hi i)).neg
  rw [integral_add hgi hs, integral_neg]
  rw [smooth_laplacian_weak_pair Q hQ (cellReferenceValue_periodic hΛ ν B t y₀ j)]
  have hl := continuous_weak_pair_integrable
    (fun x => ∑ i : Fin 2, fderiv ℝ (fun z => fderiv ℝ Q z (basisVec i)) x
      (basisVec i)) (by
        change Continuous (fun x => ∑ i : Fin 2, fderiv ℝ (fun z => fderiv ℝ
          (fun y => cellReferenceValue α q Λ ζ m ν B y₀ t y j) z (basisVec i))
          x (basisVec i))
        simp_rw [cellReferenceValue_laplacian hΛ]
        exact continuous_const.mul hQ.continuous)
    (ψ.jet (valueIndex2 1)) (ψ.hasPeriodicWeakJet.2.1 (valueIndex2 1))
  rw [← integral_add hl hs]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← add_mul, ← Complex.ofReal_add]
  congr 1
  rw [cellReferenceValue_laplacian hΛ, ← cellReferenceValue_time_equation hΛ hζ hν]
  ring_nf

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVenhance
open scoped ENNReal
namespace AVRegularity.CycleDamping

/-! The scaled actual drift has a universal bound once the relaxation interval is long enough. -/

theorem cellForcing_component_uniform_bound {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m) (y₀ z : Vec 2) (t : ℝ) (j : Fin 2) :
    |Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) * ocCellDrift α q Λ ζ m ν y₀ t z j| ≤
      2 * Real.pi * Real.sqrt (2 / ((1 - Real.exp (-2)) / 96)) := by
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  have hA : 0 < 2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) * (ocEpsilon q Λ m)⁻¹ := by positivity
  have hamp : 2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) * (ocEpsilon q Λ m)⁻¹ =
      2 * Real.pi * ocA α q Λ m * ocEpsilon q Λ m := by
    have hp : ocEpsilon q Λ m ^ α = ocEpsilon q Λ m ^ (α - 1) * ocEpsilon q Λ m := by
      calc
        _ = ocEpsilon q Λ m ^ ((α - 1) + 1) := by congr 1; ring
        _ = _ := by rw [Real.rpow_add he, Real.rpow_one]
    unfold ocA
    rw [mul_assoc, ← div_eq_mul_inv, ← Real.rpow_sub_one he.ne']
    rw [show 1 + α - 1 = α by ring, hp]
    ring_nf
  have hb := mul_le_mul_of_nonneg_left
    (ocCellDrift_component_abs_bound (α := α) (q := q) (m := m) hΛ hζ ν t y₀ z j)
    (Real.sqrt_nonneg (ν / ocMeanFlux α q Λ ζ m ν))
  rw [abs_of_nonneg (div_nonneg (sq_nonneg _) he.le), abs_of_pos hA, hamp] at hb
  have hs : |Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) * ocCellDrift α q Λ ζ m ν y₀ t z j| ≤
      2 * Real.pi * (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) * ocA α q Λ m *
        ocEll q Λ m ν ^ 2) := by
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    apply hb.trans_eq
    field_simp
  exact hs.trans (mul_le_mul_of_nonneg_left (corrector_amplitude_bound hΛ hζ hν hr)
    (mul_pos (by norm_num) Real.pi_pos).le)

theorem cellForcing_ul_uniform_bound {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m) (y₀ : Vec 2) (j : Fin 2) :
    cellUlNorm Set.univ (fun t x => ((Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      ocCellDrift α q Λ ζ m ν y₀ t x j : ℝ) : ℂ)) ≤
      ENNReal.ofReal (2 * Real.pi * Real.sqrt (2 / ((1 - Real.exp (-2)) / 96))) := by
  have hc := cellForcing_joint_continuous (α := α) (q := q) (m := m) hΛ hζ ν
    (ocMeanFlux α q Λ ζ m ν) y₀ j
  apply cellUlNorm_le_uniform_bound _ (fun t =>
    (hc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  intro t x
  change ‖((Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
    ocCellDrift α q Λ ζ m ν y₀ t x j : ℝ) : ℂ)‖ ≤ _
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact cellForcing_component_uniform_bound hΛ hζ hν hr y₀ x t j

end AVRegularity.CycleDamping
end

section
open Homogenization
namespace AVRegularity.CycleDamping

/-! The constructed weighted drift has a uniform graph-construction budget. -/

theorem weighted_vecNorm_le_of_coordinate_bound (a W : ℝ) (ha : 0 ≤ a) (hW : 0 ≤ W)
    (v : Vec 2) (hb : ∀ j, |a * v j| ≤ W) :
    a * Real.sqrt (∑ j, v j ^ 2) ≤ Real.sqrt 2 * W := by
  have hv : 0 ≤ ∑ j, v j ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have h0 := hb 0
  have h1 := hb 1
  have hs0 : (a * v 0) ^ 2 ≤ W ^ 2 := by
    nlinarith only [h0, abs_nonneg (a * v 0), hW, sq_abs (a * v 0)]
  have hs1 : (a * v 1) ^ 2 ≤ W ^ 2 := by
    nlinarith only [h1, abs_nonneg (a * v 1), hW, sq_abs (a * v 1)]
  have hsq : (a * Real.sqrt (∑ j, v j ^ 2)) ^ 2 ≤ (Real.sqrt 2 * W) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hv, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    simp only [Fin.sum_univ_two]
    nlinarith only [hs0, hs1]
  have hl : 0 ≤ a * Real.sqrt (∑ j, v j ^ 2) := mul_nonneg ha (Real.sqrt_nonneg _)
  have hr : 0 ≤ Real.sqrt 2 * W := mul_nonneg (Real.sqrt_nonneg _) hW
  nlinarith only [hsq, hl, hr]

theorem ocCellDrift_weighted_uniform_bound {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m) (y₀ z : Vec 2) (t : ℝ) :
    Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ j, ocCellDrift α q Λ ζ m ν y₀ t z j ^ 2) ≤
      Real.sqrt 2 * (2 * Real.pi * Real.sqrt (2 / ((1 - Real.exp (-2)) / 96))) := by
  apply weighted_vecNorm_le_of_coordinate_bound _ _ (Real.sqrt_nonneg _) (by positivity)
  intro j
  exact cellForcing_component_uniform_bound hΛ hζ hν hr y₀ z t j

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.CycleDamping

/-! Joint L², gradient energy, and the continuous trace for the actual reference raw jet. -/

theorem cellReferenceJet_product_memLp {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν B : ℝ) (y₀ : Vec 2)
    (j : Fin 2) (a b : ℝ) (w : JetIndex2 1) :
    MemLp (fun p : ℝ × Vec 2 => cellReferenceJet α q Λ ζ m ν B y₀ j p.1 w p.2) 2
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict AVenhance.unitCube)) :=
  continuous_cell_product_memLp _ (cellReferenceJet_joint_continuous hΛ hζ ν B y₀ j w) a b

theorem cellReferenceJet_gradient_energy_finite {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν B : ℝ) (y₀ : Vec 2)
    (j : Fin 2) (a b : ℝ) :
    (∫⁻ t in Set.Icc a b, cellL2Norm
      (cellGradient (cellReferenceJet α q Λ ζ m ν B y₀ j t)) ^ 2) < ⊤ :=
  CycleEvolution.cellProduct_cellNormSq_finite (Set.Icc a b) _
    (CycleEvolution.cellRawGradient_memLp _ _
      (cellReferenceJet_product_memLp hΛ hζ ν B y₀ j a b))

theorem cellReferenceJet_trace_continuous {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν B : ℝ) (y₀ : Vec 2) (j : Fin 2) :
    ∀ t₀ : ℝ, Tendsto (fun t => ∫⁻ x in AVenhance.unitCube,
      ‖cellValue (cellReferenceJet α q Λ ζ m ν B y₀ j) t x -
        cellValue (cellReferenceJet α q Λ ζ m ν B y₀ j) t₀ x‖ₑ ^ 2) (𝓝 t₀) (𝓝 0) := by
  let f : Vec 2 → ℝ := fun x => Real.cos
    (2 * Real.pi * (x (1 - j) + y₀ (1 - j) / ocEpsilon q Λ m))
  have hf : MemLp (fun x => (f x : ℂ)) 2 (volume.restrict AVenhance.unitCube) :=
    Complex.ofRealCLM.comp_memLp'
      (AVenhance.Infra.Parabolic.WeakUniqueness.weak_continuous_memL2On (by fun_prop))
  have he (t : ℝ) (x : Vec 2) :
      cellValue (cellReferenceJet α q Λ ζ m ν B y₀ j) t x =
        ((cellReferenceAmplitude α q Λ ζ m ν B j t : ℝ) : ℂ) * (f x : ℂ) := by
    rw [cellReferenceJet_value, cellReferenceValue_single_mode hΛ, Complex.ofReal_mul]
  simp_rw [he]
  exact scalar_cell_trace_continuous _ (cellReferenceAmplitude_continuous hΛ hζ ν B j) _ hf

end AVRegularity.CycleDamping
end
