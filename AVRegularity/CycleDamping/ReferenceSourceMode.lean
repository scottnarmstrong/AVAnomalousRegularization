-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleDamping.CellTrigonometricMean
public import AVRegularity.CycleDamping.ReferenceTimeEquation
import AVRegularity.CycleReference.CorrectorMeanGeometry
import AVRegularity.CycleEvolution.CellEnergySpaceRawDirectionalLimit
public import AVRegularity.CycleEvolution.CellTimeMetricDriftCLM
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.CycleReference.CoreFlux
import AVRegularity.CycleReference.ChartTestCalculus
import AVRegularity.CycleReference.SingleModeFlux
import AVenhance.Infra.Section3.CorrectorGradient
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleDamping

/-! Exact diffusion contribution to the cosine moment for a frozen spatial metric. -/

theorem cosine_diffusion_moment
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric (fun t _ => G t))
    (θ : Vec 2) (t : ℝ) (u : TorusHk 1 ℂ) (j : Fin 2) (phase : ℝ) :
    -(∑ i : Fin 2, ∑ k : Fin 2, cellComplexPair
      (cellMetricEntryCLM hG t i k (cellShiftedDerivativeCLM (fun l => (θ l : ℂ)) i u))
      (cellShiftedDerivativeCLM (fun l => star (θ l : ℂ)) k (cellCosineH1 j phase))) =
    -((2 * Real.pi : ℂ) ^ 2 * (G t j j : ℂ)) *
      cellComplexPair (torusHkValueCLM u) (torusHkValueCLM (cellCosineH1 j phase)) +
    Complex.I * (2 * Real.pi : ℂ) *
      (∑ i : Fin 2, (θ i : ℂ) * ((G t i j : ℂ) + (G t j i : ℂ))) *
      cellComplexPair (torusHkValueCLM u) (torusHkValueCLM (cellSineH1 j phase)) -
    (∑ i : Fin 2, ∑ k : Fin 2, (θ k : ℂ) * (G t i k : ℂ) * (θ i : ℂ)) *
      cellComplexPair (torusHkValueCLM u) (torusHkValueCLM (cellCosineH1 j phase)) := by
  have ht (k : Fin 2) :
      cellShiftedDerivativeCLM (fun l => star (θ l : ℂ)) k (cellCosineH1 j phase) =
        cellScalarCLM (if k = j then (-(2 * Real.pi) : ℂ) else 0)
          (torusHkValueCLM (cellSineH1 j phase)) +
        cellScalarCLM (Complex.I * (θ k : ℂ))
          (torusHkValueCLM (cellCosineH1 j phase)) := by
    change cellDerivativeCLM k (cellCosineH1 j phase) +
      cellScalarCLM (Complex.I * star (θ k : ℂ)) (torusHkValueCLM (cellCosineH1 j phase)) = _
    rw [cellCosineH1_derivative, Complex.star_def, Complex.conj_ofReal]
  simp_rw [ht, frozen_metric_entry_scalar, pair_scalar_left, pair_add_right,
    pair_scalar_right, shifted_sine_pair, shifted_cosine_pair]
  fin_cases j <;> norm_num [Fin.sum_univ_two, Complex.star_def, map_ofNat]
  all_goals
    ring_nf
    simp only [Complex.I_sq]
    ring

end AVRegularity.CycleDamping
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleDamping

/-! Integrated Brillouin coercivity on genuine weak-time trajectories. -/

theorem real_shift_integrated_meanFree_gap {a b : ℝ} (hab : a ≤ b)
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2)
    (hθ : ∀ j, |θ j| ≤ Real.pi)
    {u : ℝ → ComplexCellL2} {slice : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice (fun t =>
      cellDualDerivative ⟨G, v, fun j => (θ j : ℂ), 0⟩ hG V hv.1 hb t (slice t) 0 0)) :
    Real.pi ^ 2 * (∫ t in a..b, ‖cellQ0CLM (u t)‖ ^ 2) ≤ 4 * ‖u a‖ ^ 2 := by
  have hq : IntervalIntegrable (fun t => ‖cellQ0CLM (u t)‖ ^ 2) volume a b := by
    apply ((cellTime_normSq_intervalIntegrable hab
      ((cellQ0CLM.comp torusHkValueCLM).comp_memLp' h.state))).congr_ae
    have hh := h.agrees.filter_mono (ae_mono (Measure.restrict_mono Ioc_subset_Icc_self le_rfl))
    rw [uIoc_of_le hab]
    filter_upwards [hh] with t ht
    simp only [Function.comp_def, ContinuousLinearMap.comp_apply, ht]
  have hi (j : Fin 2) := cellTime_normSq_intervalIntegrable hab
    ((cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j).comp_memLp' h.state)
  have hD : IntervalIntegrable (fun t => ∑ j : Fin 2,
      ‖cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j (slice t)‖ ^ 2) volume a b := by
    simpa only [Fin.sum_univ_two, Function.comp_def] using (hi 0).add (hi 1)
  have hm := intervalIntegral.integral_mono_ae_restrict hab (hq.const_mul (Real.pi ^ 2))
    (hD.const_mul 4) (by
      filter_upwards [h.agrees] with t ht
      rw [ht]
      exact cellH1_meanFree_shifted_gap θ hθ (slice t))
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hm
  have he := real_shift_weak_energy hab hG v hv V hb θ h
  nlinarith only [hm, he, sq_nonneg ‖u b‖]

/-! A quantitative spectral contraction on any real-shift weak cell interval. -/

theorem real_shift_spectral_contraction {a b : ℝ} (hab : a ≤ b)
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2)
    (hθ : ∀ j, |θ j| ≤ Real.pi)
    {u : ℝ → ComplexCellL2} {slice : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice (fun t =>
      cellDualDerivative ⟨G, v, fun j => (θ j : ℂ), 0⟩ hG V hv.1 hb t (slice t) 0 0)) :
    (1 + (∑ j : Fin 2, θ j ^ 2) * (b - a)) * ‖u b‖ ^ 2 ≤ ‖u a‖ ^ 2 := by
  have hi (j : Fin 2) := cellTime_normSq_intervalIntegrable hab
    ((cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j).comp_memLp' h.state)
  have hD : IntervalIntegrable (fun t => ∑ j : Fin 2,
      ‖cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j (slice t)‖ ^ 2) volume a b := by
    simpa only [Fin.sum_univ_two, Function.comp_def] using (hi 0).add (hi 1)
  have hsum : 0 ≤ ∑ j : Fin 2, θ j ^ 2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hs (t : ℝ) (ht : t ∈ Icc a b) : ‖u b‖ ^ 2 ≤ ‖u t‖ ^ 2 := by
    have hm := real_shift_weak_contraction ht.2 hG v hv V hb θ
      (h.mono (Icc_subset_Icc ht.1 le_rfl))
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hm
  have hlow := intervalIntegral.integral_mono_ae_restrict hab intervalIntegrable_const hD (by
    filter_upwards [h.agrees, ae_restrict_mem measurableSet_Icc] with t he ht
    have hm := mul_le_mul_of_nonneg_left (hs t ht) hsum
    rw [he] at hm
    exact hm.trans (cellH1_shifted_frequency_gap θ hθ (slice t)))
  rw [intervalIntegral.integral_const] at hlow
  have he := real_shift_weak_energy hab hG v hv V hb θ h
  simp only [smul_eq_mul] at hlow
  nlinarith only [hlow, he]

end AVRegularity.CycleDamping
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping

/-! A fixed half-norm drop from molecular spectral damping. -/

theorem spectral_weak_half_contraction {a b : ℝ} (hab : a ≤ b)
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2)
    (hθ : ∀ j, |θ j| ≤ Real.pi)
    (hlong : 3 ≤ (∑ j : Fin 2, θ j ^ 2) * (b - a))
    {u : ℝ → ComplexCellL2} {slice : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice (fun t =>
      cellDualDerivative ⟨G, v, fun j => (θ j : ℂ), 0⟩ hG V hv.1 hb t (slice t) 0 0)) :
    ‖u b‖ ≤ (1 / 2 : ℝ) * ‖u a‖ := by
  have he := real_shift_spectral_contraction hab hG v hv V hb θ hθ h
  have hm := mul_le_mul_of_nonneg_right hlong (sq_nonneg ‖u b‖)
  nlinarith only [he, hm, norm_nonneg (u a), norm_nonneg (u b)]

theorem scaled_real_frequency_gap (η ξlo : ℝ) (hη : 1 / 2 ≤ η) (hlo : 0 < ξlo)
    (ξ : Vec 2) (hξ : ξlo ≤ Real.sqrt (∑ i : Fin 2, ξ i ^ 2)) :
    ξlo ^ 2 / 2 ≤ ∑ i : Fin 2, (Real.sqrt η * ξ i) ^ 2 := by
  have hη0 : 0 ≤ η := by linarith only [hη]
  have hs := (sq_le_sq₀ hlo.le (Real.sqrt_nonneg _)).mpr hξ
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))] at hs
  simp only [mul_pow, Real.sq_sqrt hη0, ← Finset.mul_sum]
  have hm := mul_le_mul_of_nonneg_left hs hη0
  have hp := mul_le_mul_of_nonneg_right hη (sq_nonneg ξlo)
  nlinarith only [hm, hp]

/-! A uniform molecular contraction time above any positive physical-frequency cutoff. -/

theorem molecular_contraction_time (ξlo : ℝ) (hlo : 0 < ξlo) :
    ∃ d : ℝ, 0 < d ∧ ∀ η : ℝ, 1 / 2 ≤ η →
      ∀ ξ : Vec 2, (∀ j, |Real.sqrt η * ξ j| ≤ Real.pi) →
      ξlo ≤ Real.sqrt (∑ j : Fin 2, ξ j ^ 2) →
      ∀ a b : ℝ, a ≤ b → d ≤ b - a →
      ∀ (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric G)
        (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
        (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
        (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ),
        CellWeakHilbertCurve a b u slice (fun t => cellDualDerivative
          ⟨G, v, fun i => ((Real.sqrt η * ξ i : ℝ) : ℂ), 0⟩ hG V hv.1 hb t (slice t) 0 0) →
        ‖u b‖ ≤ (1 / 2 : ℝ) * ‖u a‖ := by
  let d : ℝ := 6 / ξlo ^ 2
  have hd : 0 < d := by dsimp [d]; positivity
  refine ⟨d, hd, ?_⟩
  intro η hη ξ hθ hξ a b hab hlong G hG v hv V hb u slice h
  have hgap := scaled_real_frequency_gap η ξlo hη hlo ξ hξ
  have hm := mul_le_mul_of_nonneg_right hgap (sub_nonneg.mpr hab)
  have hl := mul_le_mul_of_nonneg_left hlong (by positivity : 0 ≤ ξlo ^ 2 / 2)
  have hc : (ξlo ^ 2 / 2) * d = 3 := by dsimp [d]; field_simp; ring
  rw [hc] at hl
  have hlength : 3 ≤ (∑ j : Fin 2, (Real.sqrt η * ξ j) ^ 2) * (b - a) := hl.trans hm
  exact spectral_weak_half_contraction hab hG v hv V hb (fun i => Real.sqrt η * ξ i) hθ hlength h

end AVRegularity.CycleDamping
end

section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleDamping

/-! Cell periodicity and smooth weak jets of the translated reference corrector. -/

theorem scaled_cell_cosine_eq (e : ℝ) (he : e ≠ 0) (y₀ z : Vec 2) (j : Fin 2) :
    Real.cos (2 * Real.pi * e⁻¹ * (y₀ + e • z) j) =
      Real.cos (2 * Real.pi * (z j + y₀ j / e)) := by
  congr 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

theorem scaled_cell_cosine_periodic (e : ℝ) (he : e ≠ 0) (y₀ : Vec 2) (j : Fin 2) :
    IsZ2Periodic (fun z : Vec 2 =>
      Real.cos (2 * Real.pi * e⁻¹ * (y₀ + e • z) j)) := by
  intro n z
  have ha : 2 * Real.pi * e⁻¹ * (y₀ + e • (z + latticeShift n)) j =
      2 * Real.pi * e⁻¹ * (y₀ + e • z) j + (n j : ℝ) * (2 * Real.pi) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, latticeShift]
    field_simp
    ring
  change Real.cos (2 * Real.pi * e⁻¹ * (y₀ + e • (z + latticeShift n)) j) = _
  rw [ha, Real.cos_add_int_mul_two_pi]

theorem cellPulseCorrector_periodic {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) {k : ℤ} (hk : Odd k) (ν t : ℝ) (y₀ : Vec 2) (j : Fin 2) :
    IsZ2Periodic (fun z => ocPulseCorrector α q Λ ζ m ν k t
      (y₀ + ocEpsilon q Λ m • z) j) := by
  have he := (AVRegularity.Construction.Stream.ocEpsilon_pos
    (q := q) (n := m) hΛ).ne'
  have hp (i : Fin 2) := scaled_cell_cosine_periodic (ocEpsilon q Λ m) he y₀ i
  rcases CycleReference.odd_int_mod_four hk with h1 | h3
  · rcases CycleReference.pulseCorrector_horizontal_components
      (α := α) (q := q) (Λ := Λ) (m := m) (ζ := ζ) h1 ν t with ⟨h0, hf⟩
    fin_cases j
    · intro n z
      exact (congrFun h0 _).trans (congrFun h0 _).symm
    · intro n z
      change ocPulseCorrector α q Λ ζ m ν k t (y₀ + ocEpsilon q Λ m • (z + latticeShift n)) 1 =
        ocPulseCorrector α q Λ ζ m ν k t (y₀ + ocEpsilon q Λ m • z) 1
      rw [congrFun hf _, congrFun hf _]
      exact congrArg (fun x : ℝ => _ * x) (hp 0 n z)
  · rcases CycleReference.pulseCorrector_vertical_components
      (α := α) (q := q) (Λ := Λ) (m := m) (ζ := ζ) h3 ν t with ⟨hf, h1⟩
    fin_cases j
    · intro n z
      change ocPulseCorrector α q Λ ζ m ν k t (y₀ + ocEpsilon q Λ m • (z + latticeShift n)) 0 =
        ocPulseCorrector α q Λ ζ m ν k t (y₀ + ocEpsilon q Λ m • z) 0
      rw [congrFun hf _, congrFun hf _]
      exact congrArg (fun x : ℝ => _ * x) (hp 1 n z)
    · intro n z
      exact (congrFun h1 _).trans (congrFun h1 _).symm

theorem cellReferenceValue_periodic {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (ν B t : ℝ) (y₀ : Vec 2) (j : Fin 2) :
    IsZ2Periodic (fun z => cellReferenceValue α q Λ ζ m ν B y₀ t z j) := by
  classical
  intro n z
  simp only [cellReferenceValue, Pi.smul_apply, smul_eq_mul]
  congr 1
  have hs := CycleReference.ocRefCorrector_component_sum
    (α := α) (q := q) (m := m) (ζ := ζ) hΛ ν (ocEll q Λ m ν ^ 2 * t) j
  rw [congrFun hs _, congrFun hs _]
  apply Finset.sum_congr rfl
  intro k hk
  exact congrArg (fun x : ℝ => _ * x)
    (cellPulseCorrector_periodic (α := α) (q := q) (m := m) (ζ := ζ)
      hΛ k.2 ν (ocEll q Λ m ν ^ 2 * t) y₀ j n z)

theorem cellReferenceValue_contDiff {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (ν B t : ℝ) (y₀ : Vec 2) (j : Fin 2) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun z => cellReferenceValue α q Λ ζ m ν B y₀ t z j) := by
  change ContDiff ℝ (↑(⊤ : ℕ∞)) (fun z =>
    -(Real.sqrt (ν / B) / ocEpsilon q Λ m) *
      ocRefCorrector α q Λ ζ m ν (ocEll q Λ m ν ^ 2 * t)
        (y₀ + ocEpsilon q Λ m • z) j)
  apply contDiff_const.mul
  have ha : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun z : Vec 2 => y₀ + ocEpsilon q Λ m • z) := by
    fun_prop
  exact ((CycleReference.ocRefCorrector_component_contDiff
    (α := α) (q := q) (m := m) (ζ := ζ) hΛ ν _ j).of_le (by simp)).comp ha

theorem cellReferenceValue_periodicWeak {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (ν B t : ℝ) (y₀ : Vec 2) (j : Fin 2) :
    HasPeriodicOrderedWeakJet (CycleEvolution.cellSmoothScalarJet
      (fun z => cellReferenceValue α q Λ ζ m ν B y₀ t z j)) :=
  CycleEvolution.cellSmoothScalarJet_periodicWeak _
    (cellReferenceValue_contDiff hΛ ν B t y₀ j)
    (cellReferenceValue_periodic hΛ ν B t y₀ j)

end AVRegularity.CycleDamping
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleDamping

/-! Each reference-corrector component lies in a fixed one-dimensional spatial mode. -/

theorem pulseCorrector_mode {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    {k : ℤ} (hk : Odd k) (ν t : ℝ) (y : Vec 2) (j : Fin 2) :
    ocPulseCorrector α q Λ ζ m ν k t y j =
      ocPulseCorrector α q Λ ζ m ν k t 0 j *
        Real.cos (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y (1 - j)) := by
  rcases CycleReference.odd_int_mod_four hk with h1 | h3
  · fin_cases j <;> norm_num [ocPulseCorrector, CycleReference.ocShearVel_horizontal h1]
    ring
  · fin_cases j <;> norm_num [ocPulseCorrector, CycleReference.ocShearVel_vertical h3]
    ring

theorem refCorrector_mode {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (ν t : ℝ) (y : Vec 2) (j : Fin 2) :
    ocRefCorrector α q Λ ζ m ν t y j =
      ocRefCorrector α q Λ ζ m ν t 0 j *
        Real.cos (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y (1 - j)) := by
  classical
  have hs := CycleReference.ocRefCorrector_component_sum
    (α := α) (q := q) (m := m) (ζ := ζ) hΛ ν t j
  rw [congrFun hs y, congrFun hs 0]
  have hm (k : {k : ℤ // Odd k}) := pulseCorrector_mode
    (α := α) (q := q) (Λ := Λ) (m := m) (ζ := ζ) k.2 ν t y j
  simp_rw [hm]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

def cellReferenceAmplitude (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ)
    (ν B : ℝ) (j : Fin 2) (t : ℝ) : ℝ :=
  -(Real.sqrt (ν / B) / ocEpsilon q Λ m) *
    ocRefCorrector α q Λ ζ m ν (ocEll q Λ m ν ^ 2 * t) 0 j

theorem cellReferenceValue_single_mode {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (ν B t : ℝ) (y₀ z : Vec 2) (j : Fin 2) :
    cellReferenceValue α q Λ ζ m ν B y₀ t z j =
      cellReferenceAmplitude α q Λ ζ m ν B j t *
        Real.cos (2 * Real.pi * (z (1 - j) + y₀ (1 - j) / ocEpsilon q Λ m)) := by
  simp only [cellReferenceValue, Pi.smul_apply, smul_eq_mul]
  rw [refCorrector_mode hΛ]
  rw [scaled_cell_cosine_eq _
    (AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ).ne']
  simp only [cellReferenceAmplitude, mul_assoc]

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleDamping

/-! Unit-cell shear moments have exact norms and are controlled by fluctuations. -/

theorem cellCosineH1_value_norm_sq (j : Fin 2) (phase : ℝ) :
    ‖torusHkValueCLM (cellCosineH1 j phase)‖ ^ 2 = (1 / 2 : ℝ) := by
  rw [← cellL2_norm_sq_integral]
  calc
    _ = ∫ x in unitCube, cellCosine j phase x ^ 2 := by
      apply integral_congr_ae
      filter_upwards [cellCosineH1_value_ae j phase] with x hx
      rw [hx, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    _ = (1 / 2 : ℝ) := cell_cosine_sq_mean j phase

theorem cellSineH1_value_eq_cosine (j : Fin 2) (phase : ℝ) :
    torusHkValueCLM (cellSineH1 j phase) = torusHkValueCLM (cellCosineH1 j (phase - 1 / 4)) := by
  apply Lp.ext
  filter_upwards [cellSineH1_value_ae j phase, cellCosineH1_value_ae j (phase - 1 / 4)] with x hs hc
  rw [hs, hc]
  congr 1
  unfold cellSine cellCosine
  have he : 2 * Real.pi * (x j + (phase - 1 / 4)) =
      2 * Real.pi * (x j + phase) - Real.pi / 2 := by ring
  rw [he, Real.cos_sub_pi_div_two]

theorem cosine_moment_norm_le (u : ComplexCellL2) (j : Fin 2) (phase : ℝ) :
    ‖cellComplexPair u (torusHkValueCLM (cellCosineH1 j phase))‖ ≤ ‖cellQ0CLM u‖ := by
  rw [meanFree_pair_of_zero_mean u _ (cellCosineH1_mean j phase)]
  have hn : ‖torusHkValueCLM (cellCosineH1 j phase)‖ ≤ 1 := by
    have he := cellCosineH1_value_norm_sq j phase
    nlinarith only [he, norm_nonneg (torusHkValueCLM (cellCosineH1 j phase))]
  exact (pair_norm_le _ _).trans (by simpa only [mul_one] using
    (mul_le_mul_of_nonneg_left hn (norm_nonneg (cellQ0CLM u))))

theorem sine_moment_norm_le (u : ComplexCellL2) (j : Fin 2) (phase : ℝ) :
    ‖cellComplexPair u (torusHkValueCLM (cellSineH1 j phase))‖ ≤ ‖cellQ0CLM u‖ := by
  rw [cellSineH1_value_eq_cosine]
  exact cosine_moment_norm_le u j (phase - 1 / 4)

/-! The actual squared cosine test, including its mean and transverse derivative. -/

def cellCosineSquareH1 (j : Fin 2) (phase : ℝ) : TorusHk 1 ℂ :=
  complexSmoothScalarH1 (fun x => cellCosine j phase x ^ 2)
    ((cellCosine_smooth j phase).pow 2)
    (fun n x => congrArg (fun r : ℝ => r ^ 2) (cellCosine_periodic j phase n x))

theorem cellCosineSquareH1_value_ae (j : Fin 2) (phase : ℝ) :
    torusHkValueCLM (cellCosineSquareH1 j phase) =ᵐ[volume.restrict unitCube]
      fun x => ((cellCosine j phase x ^ 2 : ℝ) : ℂ) :=
  complexSmoothScalarH1_ae _ ((cellCosine_smooth j phase).pow 2)
    (fun n x => congrArg (fun r : ℝ => r ^ 2) (cellCosine_periodic j phase n x)) (valueIndex2 1)

theorem cellCosineSquareH1_mean (j : Fin 2) (phase : ℝ) :
    cellMean (torusHkValueCLM (cellCosineSquareH1 j phase)) = (1 / 2 : ℂ) := by
  have he : cellMean (torusHkValueCLM (cellCosineSquareH1 j phase)) =
      ∫ x in unitCube, ((cellCosine j phase x ^ 2 : ℝ) : ℂ) :=
    integral_congr_ae (cellCosineSquareH1_value_ae j phase)
  rw [he, integral_complex_ofReal]
  change ((∫ x in unitCube, Real.cos (2 * Real.pi * (x j + phase)) ^ 2 : ℝ) : ℂ) = _
  rw [cell_cosine_sq_mean]
  norm_num

theorem cellCosineSquareH1_transverse_derivative (j i : Fin 2) (hij : i ≠ j) (phase : ℝ) :
    cellDerivativeCLM i (cellCosineSquareH1 j phase) = 0 := by
  apply Lp.ext
  have hd := complexSmoothScalarH1_ae _ ((cellCosine_smooth j phase).pow 2)
    (fun n x => congrArg (fun r : ℝ => r ^ 2) (cellCosine_periodic j phase n x))
    ⟨⟨1, by decide⟩, fun _ => i⟩
  filter_upwards [hd, Lp.coeFn_zero (E := ℂ) (p := 2) (μ := volume.restrict unitCube)] with x hx hz
  change cellDerivativeCLM i (cellCosineSquareH1 j phase) x = _ at hx
  rw [hx, hz]
  change ((fderiv ℝ (fun y => cellCosine j phase y ^ 2) x (basisVec i) : ℝ) : ℂ) = 0
  have hdiff := (cellCosine_smooth j phase).differentiable (by simp)
  simp only [pow_two, ← Pi.mul_def]
  rw [fderiv_mul (hdiff x) (hdiff x)]
  simp only [add_apply, smul_apply, smul_eq_mul, cellCosine_derivative, hij,
    ite_false, mul_zero, add_zero, Complex.ofReal_zero]

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVenhance
namespace AVRegularity.CycleDamping

/-! Each constructed cell drift has zero spatial mean at every time and center. -/

theorem cell_shear_mean_zero {α q : ℝ} {Λ m : ℕ} (hΛ : 1 ≤ Λ)
    {k : ℤ} (hk : Odd k) (y₀ : Vec 2) (j : Fin 2) :
    (∫ z in unitCube, ocShearVel α q Λ m k (y₀ + ocEpsilon q Λ m • z) j) = 0 := by
  have he := (AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ).ne'
  have hc (i : Fin 2) : (∫ z in unitCube,
      Real.cos (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ *
        (y₀ + ocEpsilon q Λ m • z) i)) = 0 := by
    simp_rw [scaled_cell_cosine_eq _ he]
    exact cell_cosine_mean_zero i _
  rcases CycleReference.odd_int_mod_four hk with h1 | h3
  · simp only [CycleReference.ocShearVel_horizontal h1]
    fin_cases j
    · change (∫ _z : Vec 2 in unitCube, (0 : ℝ)) = 0
      simp only [integral_zero]
    · change (∫ z in unitCube,
        (2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) * (ocEpsilon q Λ m)⁻¹) *
          Real.cos (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * (y₀ + ocEpsilon q Λ m • z) 0)) = 0
      rw [integral_const_mul, hc 0, mul_zero]
  · simp only [CycleReference.ocShearVel_vertical h3]
    fin_cases j
    · change (∫ z in unitCube,
        -(2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) * (ocEpsilon q Λ m)⁻¹) *
          Real.cos (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * (y₀ + ocEpsilon q Λ m • z) 1)) = 0
      rw [integral_const_mul, hc 1, mul_zero]
    · change (∫ _z : Vec 2 in unitCube, (0 : ℝ)) = 0
      simp only [integral_zero]

theorem ocCellDrift_mean_zero {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν t : ℝ) (y₀ : Vec 2) (j : Fin 2) :
    (∫ z in unitCube, ocCellDrift α q Λ ζ m ν y₀ t z j) = 0 := by
  classical
  by_cases hp : ∃ k : ℤ, Odd k ∧ ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t) ≠ 0
  · obtain ⟨k, hk, hp⟩ := hp
    unfold ocCellDrift
    simp_rw [CycleReference.pulseStreamVel_eq_active hΛ hζ hk hp,
      Pi.smul_apply, smul_eq_mul, ← mul_assoc]
    rw [integral_const_mul, cell_shear_mean_zero hΛ hk, mul_zero]
  · have hz : ∀ k : ℤ, Odd k → ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t) = 0 := by
      intro k hk
      by_contra hn
      exact hp ⟨k, hk, hn⟩
    unfold ocCellDrift
    simp only [CycleReference.pulseStreamVel_eq_zero_of_quiet hz,
      Pi.smul_apply, Pi.zero_apply, smul_eq_mul, mul_zero, integral_zero]

end AVRegularity.CycleDamping
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping

/-! Actual homogeneous raw Bloch solutions supply their weak Hilbert moment curves. -/

theorem cellSourceSlice_zero (t : ℝ) :
    cellSourceSlice (fun (_ : ℝ) (_ : Vec 2) => (0 : ℂ)) t = 0 := by
  apply Lp.ext
  exact (cellSourceSlice_ae _ t MemLp.zero).trans
    (Lp.coeFn_zero (E := ℂ) (p := 2) (μ := volume.restrict AVenhance.unitCube)).symm

theorem raw_homogeneous_weak_curve {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric G)
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (θ : Fin 2 → ℂ) (D : ℝ → RawJet2 1 ℂ)
    (h : IsCellSolution (Icc a b) ⟨G, v, θ, 0⟩ (fun _ _ => 0) (fun _ _ => 0) D) :
    CellWeakHilbertCurve a b (cellRawTrace D) (cellH1Slice D)
      (fun t => cellDualDerivative ⟨G, v, θ, 0⟩ hG V hv hb t (cellH1Slice D t) 0 0) := by
  have hh := cellSolution_to_Hilbert hab ⟨G, v, θ, 0⟩ hG V 0 hv hb
    measurable_const (fun _ => by simp) (fun _ _ => 0) (fun _ _ => 0)
    MemLp.zero MemLp.zero D h
  change CellWeakHilbertCurve a b (cellRawTrace D) (cellH1Slice D)
    (fun t => cellDualDerivative ⟨G, v, θ, 0⟩ hG V hv hb t (cellH1Slice D t)
      (cellSourceSlice (fun _ _ => 0) t)
      (fun j => cellSourceSlice (fun r x => (0 : PiLp 2 (fun _ : Fin 2 => ℂ)) j) t)) at hh
  simpa only [cellSourceSlice_zero, PiLp.zero_apply, Pi.zero_apply,
    show (fun _ : Fin 2 => (0 : ComplexCellL2)) = 0 from rfl] using hh

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleDamping

/-! Splitting the squared-cosine moment into its exact mean and fluctuation. -/

theorem cellComplexPair_mean_split (u z : ComplexCellL2) :
    cellComplexPair u z = cellComplexPair (cellQ0CLM u) z + cellMean u * star (cellMean z) := by
  change cellComplexPair u z =
    cellComplexPair (u - cellConstantCLM (cellMeanCLM u)) z + cellMean u * star (cellMean z)
  simp only [cellComplexPair_inner, inner_sub_right]
  rw [← cellComplexPair_inner (cellConstantCLM (cellMeanCLM u)) z,
    cellComplexPair_constant_left, cellMeanCLM_apply]
  ring

theorem cosine_square_moment_split (u : ComplexCellL2) (j : Fin 2) (phase : ℝ) :
    cellComplexPair u (torusHkValueCLM (cellCosineSquareH1 j phase)) =
      (1 / 2 : ℂ) * cellMean u +
      cellComplexPair (cellQ0CLM u) (torusHkValueCLM (cellCosineSquareH1 j phase)) := by
  rw [cellComplexPair_mean_split, cellCosineSquareH1_mean]
  norm_num [Complex.star_def]
  ring

theorem cellCosineSquareH1_value_norm_le (j : Fin 2) (phase : ℝ) :
    ‖torusHkValueCLM (cellCosineSquareH1 j phase)‖ ≤ 1 := by
  let c := torusHkValueCLM (cellCosineH1 j phase)
  let c2 := torusHkValueCLM (cellCosineSquareH1 j phase)
  have hi := integral_mono_ae
    (integrable_normSq_of_memLp (Lp.memLp c2)) (integrable_normSq_of_memLp (Lp.memLp c)) (by
      filter_upwards [cellCosineH1_value_ae j phase, cellCosineSquareH1_value_ae j phase] with x hc hc2
      change ‖c2 x‖ ^ 2 ≤ ‖c x‖ ^ 2
      rw [hc, hc2, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        sq_abs, sq_abs]
      have hs : cellCosine j phase x ^ 2 ≤ 1 := by
        exact Real.cos_sq_le_one _
      have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg (cellCosine j phase x))
      nlinarith only [hm])
  rw [cellL2_norm_sq_integral, cellL2_norm_sq_integral] at hi
  change ‖c2‖ ^ 2 ≤ ‖torusHkValueCLM (cellCosineH1 j phase)‖ ^ 2 at hi
  rw [cellCosineH1_value_norm_sq] at hi
  change ‖c2‖ ≤ 1
  nlinarith only [hi, norm_nonneg c2]

theorem cosine_square_fluctuation_norm_le (u : ComplexCellL2) (j : Fin 2) (phase : ℝ) :
    ‖cellComplexPair (cellQ0CLM u) (torusHkValueCLM (cellCosineSquareH1 j phase))‖ ≤ ‖cellQ0CLM u‖ := by
  exact (pair_norm_le _ _).trans (by
    simpa only [mul_one] using (mul_le_mul_of_nonneg_left
      (cellCosineSquareH1_value_norm_le j phase) (norm_nonneg (cellQ0CLM u))))

end AVRegularity.CycleDamping
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleDamping

/-! Smoothness, cell periodicity, and zero divergence of each translated shear. -/

theorem shear_component_contDiff {α q : ℝ} {Λ m : ℕ} {k : ℤ} (hk : Odd k)
    (i : Fin 2) : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun y => ocShearVel α q Λ m k y i) := by
  rcases CycleReference.odd_int_mod_four hk with h1 | h3
  · simp only [CycleReference.ocShearVel_horizontal h1]
    fin_cases i <;> norm_num <;> fun_prop
  · simp only [CycleReference.ocShearVel_vertical h3]
    fin_cases i <;> norm_num <;> fun_prop

theorem cell_shear_component_contDiff {α q : ℝ} {Λ m : ℕ} {k : ℤ} (hk : Odd k)
    (y₀ : Vec 2) (i : Fin 2) : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun z => ocShearVel α q Λ m k (y₀ + ocEpsilon q Λ m • z) i) :=
  (shear_component_contDiff hk i).comp (by fun_prop)

theorem cell_shear_component_periodic {α q : ℝ} {Λ m : ℕ} (hΛ : 1 ≤ Λ)
    {k : ℤ} (hk : Odd k) (y₀ : Vec 2) (i : Fin 2) :
    IsZ2Periodic (fun z => ocShearVel α q Λ m k (y₀ + ocEpsilon q Λ m • z) i) := by
  have he := (AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ).ne'
  have hc (j : Fin 2) := scaled_cell_cosine_periodic (ocEpsilon q Λ m) he y₀ j
  rcases CycleReference.odd_int_mod_four hk with h1 | h3
  · simp only [CycleReference.ocShearVel_horizontal h1]
    fin_cases i
    · intro n z; rfl
    · intro n z
      change _ * Real.cos (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ *
        (y₀ + ocEpsilon q Λ m • (z + latticeShift n)) 0) =
        _ * Real.cos (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * (y₀ + ocEpsilon q Λ m • z) 0)
      exact congrArg (fun r : ℝ => (2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) * (ocEpsilon q Λ m)⁻¹) * r) (hc 0 n z)
  · simp only [CycleReference.ocShearVel_vertical h3]
    fin_cases i
    · intro n z
      change _ * Real.cos (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ *
        (y₀ + ocEpsilon q Λ m • (z + latticeShift n)) 1) =
        _ * Real.cos (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * (y₀ + ocEpsilon q Λ m • z) 1)
      exact congrArg (fun r : ℝ => -(2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) * (ocEpsilon q Λ m)⁻¹) * r) (hc 1 n z)
    · intro n z; rfl

theorem shear_diagonal_derivative_zero {α q : ℝ} {Λ m : ℕ} {k : ℤ} (hk : Odd k)
    (y : Vec 2) (i : Fin 2) :
    fderiv ℝ (fun z => ocShearVel α q Λ m k z i) y (basisVec i) = 0 := by
  rcases CycleReference.odd_int_mod_four hk with h1 | h3
  · simp only [CycleReference.ocShearVel_horizontal h1]
    fin_cases i
    · change fderiv ℝ (fun _ : Vec 2 => (0 : ℝ)) y (basisVec 0) = 0
      simp
    · change spaceGrad (fun z => _ * Real.cos (_ * z 0)) y 1 = 0
      rw [AVenhance.Infra.Section3.CorrectorGradient.spaceGrad_cosCoordinate]
      norm_num
  · simp only [CycleReference.ocShearVel_vertical h3]
    fin_cases i
    · change spaceGrad (fun z => _ * Real.cos (_ * z 1)) y 0 = 0
      rw [AVenhance.Infra.Section3.CorrectorGradient.spaceGrad_cosCoordinate]
      norm_num
    · change fderiv ℝ (fun _ : Vec 2 => (0 : ℝ)) y (basisVec 1) = 0
      simp

theorem cell_shear_diagonal_derivative_zero {α q : ℝ} {Λ m : ℕ} {k : ℤ} (hk : Odd k)
    (y₀ z : Vec 2) (i : Fin 2) :
    fderiv ℝ (fun x => ocShearVel α q Λ m k (y₀ + ocEpsilon q Λ m • x) i)
      z (basisVec i) = 0 := by
  rw [affine_coord_derivative _ ((shear_component_contDiff hk i).differentiable (by simp)),
    shear_diagonal_derivative_zero hk, mul_zero]

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping

/-! Real physical frequencies give exactly the real-shift weak cell carrier. -/

theorem real_fibre_coefficients (η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (ξ : Vec 2) :
    fibreCoefficients η G v (fun i => (ξ i : ℂ)) (fun _ => 0) =
      ⟨fun t _ => G t, v, fun i => ((Real.sqrt η * ξ i : ℝ) : ℂ), 0⟩ := by
  unfold fibreCoefficients
  congr 1
  · funext i
    rw [Complex.ofReal_mul]
  · funext t
    exact neg_zero

theorem scaled_real_brillouin (η : ℝ) (hη : 0 < η) (ξ : Vec 2)
    (hξ : ∀ j, |ξ j| ≤ Real.pi / Real.sqrt η) :
    ∀ j, |Real.sqrt η * ξ j| ≤ Real.pi := by
  intro j
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hs := mul_le_mul_of_nonneg_left (hξ j) (Real.sqrt_nonneg η)
  have hc : Real.sqrt η * (Real.pi / Real.sqrt η) = Real.pi := by
    field_simp
  exact hs.trans_eq hc

end AVRegularity.CycleDamping
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleDamping

/-! The normalized reference corrector is a cell Laplacian eigenfunction and has zero transport. -/

theorem cellReferenceValue_laplacian {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (ν B t : ℝ) (y₀ z : Vec 2) (j : Fin 2) :
    (∑ i : Fin 2, fderiv ℝ (fun x => fderiv ℝ
      (fun y => cellReferenceValue α q Λ ζ m ν B y₀ t y j) x (basisVec i)) z
        (basisVec i)) = -4 * Real.pi ^ 2 *
          cellReferenceValue α q Λ ζ m ν B y₀ t z j := by
  let u := ocEll q Λ m ν ^ 2 * t
  let f : Vec 2 → ℝ := fun y => ocRefCorrector α q Λ ζ m ν u y j
  let c := -(Real.sqrt (ν / B) / ocEpsilon q Λ m)
  have hf : ContDiff ℝ 2 f :=
    (CycleReference.ocRefCorrector_component_contDiff hΛ ν u j).of_le (by simp)
  have ha : ContDiff ℝ 2 (fun y : Vec 2 => f (y₀ + ocEpsilon q Λ m • y)) :=
    hf.comp (by fun_prop)
  change (∑ i : Fin 2, fderiv ℝ (fun x => fderiv ℝ
    (fun y => c * f (y₀ + ocEpsilon q Λ m • y)) x (basisVec i)) z (basisVec i)) =
      -4 * Real.pi ^ 2 * (c * f (y₀ + ocEpsilon q Λ m • z))
  simp_rw [CycleReference.secondDerivative_const_mul c _ ha]
  rw [← Finset.mul_sum, affine_laplacian f hf]
  have hl := CycleReference.refCorrector_laplacian (α := α) (q := q) (m := m)
    (ζ := ζ) hΛ ν u (y₀ + ocEpsilon q Λ m • z) j
  change (∑ i : Fin 2, fderiv ℝ (fun x => fderiv ℝ f x (basisVec i))
    (y₀ + ocEpsilon q Λ m • z) (basisVec i)) =
      -(2 * Real.pi * (ocEpsilon q Λ m)⁻¹) ^ 2 * f (y₀ + ocEpsilon q Λ m • z) at hl
  rw [hl]
  have he := (AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ).ne'
  field_simp
  ring

theorem cellReferenceValue_transport_zero {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν B t : ℝ) (y₀ z : Vec 2) (j : Fin 2) :
    (∑ i : Fin 2, ocCellDrift α q Λ ζ m ν y₀ t z i * fderiv ℝ
      (fun y => cellReferenceValue α q Λ ζ m ν B y₀ t y j) z (basisVec i)) = 0 := by
  let u := ocEll q Λ m ν ^ 2 * t
  let f : Vec 2 → ℝ := fun y => ocRefCorrector α q Λ ζ m ν u y j
  let c := -(Real.sqrt (ν / B) / ocEpsilon q Λ m)
  have hf : Differentiable ℝ f :=
    (CycleReference.ocRefCorrector_component_contDiff (α := α) (q := q) (m := m)
      (ζ := ζ) hΛ ν u j).differentiable (by simp)
  have ha : Differentiable ℝ (fun y : Vec 2 => f (y₀ + ocEpsilon q Λ m • y)) :=
    hf.comp (by fun_prop)
  change (∑ i : Fin 2, (ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m *
    streamVel (ocPulseStream α q Λ ζ m) u (y₀ + ocEpsilon q Λ m • z) i) *
      fderiv ℝ (fun y => c * f (y₀ + ocEpsilon q Λ m • y)) z (basisVec i)) = 0
  have hg (i : Fin 2) : fderiv ℝ (fun y => c * f (y₀ + ocEpsilon q Λ m • y)) z
      (basisVec i) = c * (ocEpsilon q Λ m * fderiv ℝ f
        (y₀ + ocEpsilon q Λ m • z) (basisVec i)) := by
    rw [fderiv_const_mul (ha z)]
    simp only [smul_apply, smul_eq_mul]
    rw [affine_coord_derivative f hf]
  simp_rw [hg]
  have ht := CycleReference.pulseStream_transport_refCorrector_zero
    (α := α) (q := q) (m := m) (ζ := ζ) hΛ hζ ν u (y₀ + ocEpsilon q Λ m • z) j
  change (∑ i : Fin 2, streamVel (ocPulseStream α q Λ ζ m) u
    (y₀ + ocEpsilon q Λ m • z) i * fderiv ℝ f (y₀ + ocEpsilon q Λ m • z)
      (basisVec i)) = 0 at ht
  calc
    _ = (ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m * c * ocEpsilon q Λ m) *
        ∑ i : Fin 2, streamVel (ocPulseStream α q Λ ζ m) u
          (y₀ + ocEpsilon q Λ m • z) i * fderiv ℝ f
            (y₀ + ocEpsilon q Λ m • z) (basisVec i) := by
      simp only [Fin.sum_univ_two]
      ring
    _ = 0 := by rw [ht, mul_zero]

end AVRegularity.CycleDamping
end

section
open Homogenization AVenhance Filter Topology
namespace AVRegularity.CycleDamping

/-! Continuous time derivatives of the reference amplitudes. -/

theorem pulseMemory_contDiff_one {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (k : ℤ) :
    ContDiff ℝ 1 (ocPulseMemory α q Λ ζ m ν k) := by
  have hd (t : ℝ) := CycleReference.ocPulseMemory_hasDerivAt
    (α := α) (q := q) (m := m) hΛ hζ ν k t
  have hc : Continuous (ocPulseMemory α q Λ ζ m ν k) :=
    continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun t => (hd t).differentiableAt, ?_⟩
  have he : deriv (ocPulseMemory α q Λ ζ m ν k) =
      fun t => ocPulse α q Λ ζ m k t -
        ocMu q Λ m ν * ocPulseMemory α q Λ ζ m ν k t :=
    funext (fun t => (hd t).deriv)
  rw [he]
  exact (CycleReference.ocPulse_continuous hζ k).sub (continuous_const.mul hc)

theorem refCorrector_contDiff_one {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (y : Vec 2) (j : Fin 2) :
    ContDiff ℝ 1 (fun t => ocRefCorrector α q Λ ζ m ν t y j) := by
  classical
  apply contDiff_iff_contDiffAt.mpr
  intro t
  obtain ⟨S, hS⟩ := CycleReference.refCorrector_locally_finite (ζ := ζ) hΛ ν t
  have he : (fun s => ocRefCorrector α q Λ ζ m ν s y j) =ᶠ[𝓝 t]
      (fun s => ∑ k ∈ S, ocCutoff α q Λ m k.1 s *
        ocPulseCorrector α q Λ ζ m ν k.1 s y j) := by
    filter_upwards [hS] with s hs
    rw [hs]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply ContDiffAt.congr_of_eventuallyEq _ he
  apply ContDiff.contDiffAt
  apply ContDiff.sum
  intro k hk
  have hp : ContDiff ℝ 1 (fun s => ocPulseCorrector α q Λ ζ m ν k.1 s y j) :=
    (pulseMemory_contDiff_one hΛ hζ ν k.1).neg.mul contDiff_const
  exact ((CycleReference.ocCutoff_contDiff hΛ k.1).of_le (by simp)).mul hp

theorem cellReferenceAmplitude_contDiff_one {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν B : ℝ) (j : Fin 2) :
    ContDiff ℝ 1 (cellReferenceAmplitude α q Λ ζ m ν B j) := by
  have hc := refCorrector_contDiff_one (α := α) (q := q) (m := m) hΛ hζ ν 0 j
  exact contDiff_const.mul (hc.comp (contDiff_const.mul contDiff_id))

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleDamping

/-! Exact mean of the shear multiplication term in the actual cell equation. -/

theorem shear_drift_mean_moment (C : CellCoefficients) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (t : ℝ) (u : ComplexCellL2) (j k : Fin 2) (phase A : ℝ)
    (hshear : ∀ x i, C.v t x i = if i = k then A * cellCosine j phase x else 0)
    (θ : Fin 2 → ℂ) :
    (∑ i : Fin 2, θ i * cellMean (cellDriftEntryCLM C V hv hb t i u)) =
      θ k * (A : ℂ) * cellComplexPair u (torusHkValueCLM (cellCosineH1 j phase)) := by
  have hp (i : Fin 2) : cellMean (cellDriftEntryCLM C V hv hb t i u) =
      if i = k then (A : ℂ) * cellComplexPair u (torusHkValueCLM (cellCosineH1 j phase)) else 0 := by
    by_cases hik : i = k
    · rw [ite_eq_left hik, cellMean, cellComplexPair, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [cellDriftEntryCLM_ae C V hv hb t i u,
        cellCosineH1_value_ae j phase] with x hd hc
      rw [hd, hshear, ite_eq_left hik, hc]
      simp only [Complex.ofReal_mul, Complex.star_def, Complex.conj_ofReal]
      ring
    · rw [ite_eq_right hik]
      apply integral_eq_zero_of_ae
      filter_upwards [cellDriftEntryCLM_ae C V hv hb t i u] with x hd
      rw [hd, hshear, ite_eq_right hik]
      simp only [Complex.ofReal_zero, zero_mul, Pi.zero_apply]
  simp_rw [hp, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ k)]
  ring

/-! Exact shear transport contribution to the actual cosine test equation. -/

theorem shear_drift_cosine_moment (C : CellCoefficients) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (t : ℝ) (u : TorusHk 1 ℂ) (j k : Fin 2) (hkj : k ≠ j) (phase A : ℝ)
    (hshear : ∀ x i, C.v t x i = if i = k then A * cellCosine j phase x else 0) :
    (∑ i : Fin 2, cellComplexPair
      (cellDriftEntryCLM C V hv hb t i (cellShiftedDerivativeCLM C.θ i u))
      (torusHkValueCLM (cellCosineH1 j phase))) =
    (A : ℂ) * Complex.I * C.θ k *
      cellComplexPair (torusHkValueCLM u) (torusHkValueCLM (cellCosineSquareH1 j phase)) := by
  have hp (i : Fin 2) (f : ComplexCellL2) :
      cellComplexPair (cellDriftEntryCLM C V hv hb t i f)
        (torusHkValueCLM (cellCosineH1 j phase)) =
      if i = k then (A : ℂ) * cellComplexPair f
        (torusHkValueCLM (cellCosineSquareH1 j phase)) else 0 := by
    by_cases hik : i = k
    · rw [ite_eq_left hik]
      rw [cellComplexPair, cellComplexPair, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [cellDriftEntryCLM_ae C V hv hb t i f,
        cellCosineH1_value_ae j phase, cellCosineSquareH1_value_ae j phase] with x hd hc hc2
      rw [hd, hshear, ite_eq_left hik, hc, hc2]
      simp only [Complex.ofReal_mul, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_pow, map_pow]
      ring
    · rw [ite_eq_right hik]
      apply integral_eq_zero_of_ae
      filter_upwards [cellDriftEntryCLM_ae C V hv hb t i f] with x hd
      rw [hd, hshear, ite_eq_right hik]
      simp only [Complex.ofReal_zero, zero_mul, Pi.zero_apply]
  simp_rw [hp]
  rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ k)]
  have hd : cellComplexPair (cellDerivativeCLM k u)
      (torusHkValueCLM (cellCosineSquareH1 j phase)) = 0 := by
    rw [weak_complex_derivative_pairing,
      cellCosineSquareH1_transverse_derivative j k hkj phase,
      cellComplexPair_zero_right, neg_zero]
  change (A : ℂ) * cellComplexPair (cellDerivativeCLM k u +
    cellScalarCLM (Complex.I * C.θ k) (torusHkValueCLM u)) _ = _
  rw [pair_add_left, hd, zero_add, pair_scalar_left]
  ring

end AVRegularity.CycleDamping
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleDamping

/-! The temporal coefficient of every reference mode is uniformly bounded. -/

theorem vec_coordinate_abs_le (v : Vec 2) (j : Fin 2) :
    |v j| ≤ Real.sqrt (vecNormSq v) := by
  apply Real.abs_le_sqrt
  change v j ^ 2 ≤ ∑ i : Fin 2, v i * v i
  simpa only [pow_two] using
    (Finset.single_le_sum (fun i _ => mul_self_nonneg (v i)) (Finset.mem_univ j))

theorem cellReferenceAmplitude_uniform_bound {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (hrelax : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m) (j : Fin 2) (t : ℝ) :
    |cellReferenceAmplitude α q Λ ζ m ν (ocMeanFlux α q Λ ζ m ν) j t| ≤
      Real.sqrt (2 / ((1 - Real.exp (-2)) / 96)) / (2 * Real.pi) := by
  have hb := (vec_coordinate_abs_le
    (cellReferenceValue α q Λ ζ m ν (ocMeanFlux α q Λ ζ m ν) 0 t 0) j).trans
    (cellReferenceValue_uniform_bound (α := α) (q := q) (m := m) hΛ hζ hν hrelax t 0 0)
  simpa only [cellReferenceValue, cellReferenceAmplitude, Pi.smul_apply, smul_eq_mul,
    smul_zero, add_zero] using hb

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleDamping

/-! The literal cosine moment generator, including its nonzero mean coupling. -/

theorem shear_cosine_generator
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2)
    (t : ℝ) (u : TorusHk 1 ℂ) (j k : Fin 2) (hkj : k ≠ j) (phase A : ℝ)
    (hshear : ∀ x i, v t x i = if i = k then A * cellCosine j phase x else 0) :
    cellComplexGenerator ⟨fun s _ => G s, v, fun i => (θ i : ℂ), 0⟩ hG V hv.1 hb t u (cellCosineH1 j phase) =
    -((2 * Real.pi : ℂ) ^ 2 * (G t j j : ℂ)) *
      cellComplexPair (torusHkValueCLM u) (torusHkValueCLM (cellCosineH1 j phase)) +
    Complex.I * (2 * Real.pi : ℂ) *
      (∑ i : Fin 2, (θ i : ℂ) * ((G t i j : ℂ) + (G t j i : ℂ))) *
      cellComplexPair (torusHkValueCLM u) (torusHkValueCLM (cellSineH1 j phase)) -
    (∑ i : Fin 2, ∑ l : Fin 2, (θ l : ℂ) * (G t i l : ℂ) * (θ i : ℂ)) *
      cellComplexPair (torusHkValueCLM u) (torusHkValueCLM (cellCosineH1 j phase)) -
    Complex.I * ((A * θ k : ℝ) : ℂ) *
      ((1 / 2 : ℂ) * cellMean (torusHkValueCLM u) +
        cellComplexPair (cellQ0CLM (torusHkValueCLM u))
          (torusHkValueCLM (cellCosineSquareH1 j phase))) := by
  have hzero : cellScalarCLM (0 : ℂ) (torusHkValueCLM u) = 0 := by
    change (0 : ℂ) • torusHkValueCLM u = 0
    exact zero_smul _ _
  rw [cellComplexGenerator]
  simp only [Pi.zero_apply, hzero, cellComplexPair_zero_left, add_zero]
  rw [cosine_diffusion_moment hG θ t u j phase,
    shear_drift_cosine_moment ⟨fun s _ => G s, v, fun i => (θ i : ℂ), 0⟩ V hv.1 hb t u j k hkj phase A hshear,
    cosine_square_moment_split]
  simp only [Complex.ofReal_mul]
  ring

/-! Uniform error bound for the actual cosine moment after extracting the mean coupling. -/

theorem four_term_moment_norm_le (D R P K b d e : ℂ) (q : ℝ)
    (hb : ‖b‖ ≤ q) (hd : ‖d‖ ≤ q) (he : ‖e‖ ≤ q) :
    ‖-D * b + R * d - P * b - Complex.I * K * e‖ ≤
      (‖D‖ + ‖R‖ + ‖P‖ + ‖K‖) * q := by
  have hn := (norm_sub_le (-D * b + R * d - P * b) (Complex.I * K * e)).trans
    (add_le_add ((norm_sub_le (-D * b + R * d) (P * b)).trans
      (add_le_add (norm_add_le (-D * b) (R * d)) le_rfl)) le_rfl)
  simp only [norm_mul, norm_neg, Complex.norm_I, one_mul] at hn
  have hDb := mul_le_mul_of_nonneg_left hb (norm_nonneg D)
  have hRd := mul_le_mul_of_nonneg_left hd (norm_nonneg R)
  have hPb := mul_le_mul_of_nonneg_left hb (norm_nonneg P)
  have hKe := mul_le_mul_of_nonneg_left he (norm_nonneg K)
  nlinarith only [hn, hDb, hRd, hPb, hKe]

theorem shear_cosine_error_norm_le
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2) (hθ : ∀ i, |θ i| ≤ Real.pi)
    (t : ℝ) (u : TorusHk 1 ℂ) (j k : Fin 2) (hkj : k ≠ j) (phase A : ℝ)
    (hshear : ∀ x i, v t x i = if i = k then A * cellCosine j phase x else 0) :
    ‖cellComplexGenerator ⟨fun s _ => G s, v, fun i => (θ i : ℂ), 0⟩ hG V hv.1 hb t u (cellCosineH1 j phase) +
      Complex.I * ((A * θ k / 2 : ℝ) : ℂ) * cellMean (torusHkValueCLM u)‖ ≤
    (28 * Real.pi ^ 2 + |A * θ k|) * ‖cellQ0CLM (torusHkValueCLM u)‖ := by
  rw [shear_cosine_generator hG v hv V hb θ t u j k hkj phase A hshear,
    realMetricSymbol_complex]
  have heq (D R P m b d e : ℂ) (K : ℝ) :
      -D * b + R * d - P * b - Complex.I * (K : ℂ) * ((1 / 2 : ℂ) * m + e) +
        Complex.I * ((K / 2 : ℝ) : ℂ) * m = -D * b + R * d - P * b - Complex.I * (K : ℂ) * e := by
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
    ring
  rw [heq]
  have hm := four_term_moment_norm_le
    ((2 * Real.pi : ℂ) ^ 2 * (G t j j : ℂ))
    (Complex.I * (2 * Real.pi : ℂ) *
      (∑ i : Fin 2, (θ i : ℂ) * ((G t i j : ℂ) + (G t j i : ℂ))))
    (realMetricSymbol (G t) θ : ℂ) ((A * θ k : ℝ) : ℂ) _ _ _ _
    (cosine_moment_norm_le (torusHkValueCLM u) j phase)
    (sine_moment_norm_le (torusHkValueCLM u) j phase)
    (cosine_square_fluctuation_norm_le (torusHkValueCLM u) j phase)
  have hD := cosine_diffusion_diagonal_norm_le hG t j
  have hR := cosine_diffusion_cross_norm_le hG θ hθ t j
  have hP : ‖(realMetricSymbol (G t) θ : ℂ)‖ ≤ 4 * Real.pi ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (realMetricSymbol_bounds hG θ hθ t).1]
    exact (realMetricSymbol_bounds hG θ hθ t).2
  have hsum := add_le_add (add_le_add hD hR) hP
  have hs : ‖(2 * Real.pi : ℂ) ^ 2 * (G t j j : ℂ)‖ +
      ‖Complex.I * (2 * Real.pi : ℂ) * (∑ i : Fin 2, (θ i : ℂ) * ((G t i j : ℂ) + (G t j i : ℂ)))‖ +
      ‖(realMetricSymbol (G t) θ : ℂ)‖ + ‖((A * θ k : ℝ) : ℂ)‖ ≤
        28 * Real.pi ^ 2 + |A * θ k| := by
    simp only [Complex.norm_real, Real.norm_eq_abs] at hsum ⊢
    linarith only [hsum]
  exact hm.trans (mul_le_mul_of_nonneg_right hs (norm_nonneg _))

end AVRegularity.CycleDamping
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleDamping

/-! The switching-corrected forcing has the same fixed spatial mode as the corrector. -/

theorem cellReferenceValue_deriv_mode {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν B t : ℝ)
    (y₀ z : Vec 2) (j : Fin 2) :
    deriv (fun s => cellReferenceValue α q Λ ζ m ν B y₀ s z j) t =
      deriv (cellReferenceAmplitude α q Λ ζ m ν B j) t *
        Real.cos (2 * Real.pi * (z (1 - j) + y₀ (1 - j) / ocEpsilon q Λ m)) := by
  have he : (fun s => cellReferenceValue α q Λ ζ m ν B y₀ s z j) =
      fun s => cellReferenceAmplitude α q Λ ζ m ν B j s *
        Real.cos (2 * Real.pi * (z (1 - j) + y₀ (1 - j) / ocEpsilon q Λ m)) :=
    funext (fun s => cellReferenceValue_single_mode hΛ ν B s y₀ z j)
  rw [he]
  exact (((cellReferenceAmplitude_contDiff_one hΛ hζ ν B j).differentiable
    (by norm_num) t).hasDerivAt.mul_const _).deriv

theorem cellReferenceSource_single_mode {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (B t : ℝ) (y₀ z : Vec 2) (j : Fin 2) :
    Real.sqrt (ν / B) * ocCellDrift α q Λ ζ m ν y₀ t z j +
      cellSwitchResidual α q Λ ζ m ν B y₀ t z j =
    (deriv (cellReferenceAmplitude α q Λ ζ m ν B j) t +
      4 * Real.pi ^ 2 * cellReferenceAmplitude α q Λ ζ m ν B j t) *
        Real.cos (2 * Real.pi * (z (1 - j) + y₀ (1 - j) / ocEpsilon q Λ m)) := by
  rw [← cellReferenceValue_time_equation hΛ hζ hν B t y₀ z j,
    cellReferenceValue_deriv_mode hΛ hζ, cellReferenceValue_single_mode hΛ]
  ring

end AVRegularity.CycleDamping
end
