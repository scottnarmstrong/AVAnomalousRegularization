-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleDamping.Graph.FibreCoefficientHomogeneousEnergy
import AVRegularity.CycleEvolution.FibreCoefficientGraphModeRatio

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping.Graph

/-! Uniform absolute convergence of the actual complete symbol coefficients. -/

/-- The actual complete symbol has a weighted coefficient majorant uniform in time and contrast. -/
theorem fibreCoefficientFamily_weighted_symbol_le (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    (∑' p, fibreCoefficientWeight (ENNReal.ofReal (fibreCoefficientMajorantRadius Cw)) p *
      ⨆ t, ‖fibreCoefficientSymbol η G v r p t‖ₑ) ≤ ENNReal.ofReal (6 * Cw + 24) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let ρ := ENNReal.ofReal (fibreCoefficientMajorantRadius Cw)
  let B := ENNReal.ofReal Cw
  have hρ : ρ ≤ 1 := (ENNReal.ofReal_le_ofReal (fibreCoefficientMajorantRadius_le_one hCw)).trans_eq (by norm_num)
  have hη' : ENNReal.ofReal |η| ≤ 1 := by
    rw [abs_of_nonneg hη0]
    exact (ENNReal.ofReal_le_ofReal hη).trans_eq (by norm_num)
  have hu p : (⨆ t, ‖fibreCoefficientSymbol η G v r p t‖ₑ) ≤
      (⨆ t, ‖fibreCoefficientMetricSymbol η G p t‖ₑ) +
        ⨆ t, ‖fibreCoefficientDriftSymbol η v r p t‖ₑ := by
    apply iSup_le
    intro t
    exact (enorm_add_le _ _).trans (add_le_add
      (le_iSup_of_le t le_rfl) (le_iSup_of_le t le_rfl))
  have hb : (∑' p, fibreCoefficientWeight ρ p * ⨆ t, ‖fibreCoefficientSymbol η G v r p t‖ₑ) ≤
      8 * ENNReal.ofReal |η| * ρ ^ 2 + (2 * ρ) * (3 * B + 8) := by
    apply (ENNReal.tsum_le_tsum (fun p => mul_le_mul' le_rfl (hu p))).trans
    simp_rw [mul_add]
    rw [ENNReal.tsum_add]
    have hd : (∑' p, fibreCoefficientWeight ρ p * ⨆ t, ‖fibreCoefficientDriftSymbol η v r p t‖ₑ) ≤
        (2 * ρ) * (3 * B + 8) :=
      fibreCoefficientFamily_weighted_drift_symbol_le η Cw hη hCw G hG hv hw
    exact add_le_add (fibreCoefficientMetricSymbol_weighted_le η G hG ρ)
      (by simpa only [mul_add] using hd)
  have hm : 8 * ENNReal.ofReal |η| * ρ ^ 2 ≤ 8 := by
    simpa only [mul_one, one_pow] using
      mul_le_mul' (mul_le_mul' (le_rfl : (8 : ℝ≥0∞) ≤ 8) hη') (pow_le_pow_left' hρ 2)
  have hd : (2 * ρ) * (3 * B + 8) ≤ 2 * (3 * B + 8) := by
    simpa only [mul_one] using
      mul_le_mul' (mul_le_mul' (le_rfl : (2 : ℝ≥0∞) ≤ 2) hρ) (le_rfl : 3 * B + 8 ≤ 3 * B + 8)
  apply hb.trans ((add_le_add hm hd).trans_eq ?_)
  have he : ENNReal.ofReal (6 * Cw + 24) = 6 * B + 24 := by
    rw [ENNReal.ofReal_add (by positivity : 0 ≤ 6 * Cw) (by norm_num : (0 : ℝ) ≤ 24),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6)]
    dsimp only [B]
    norm_num
  rw [he]
  ring

/-- Actual symbol coefficients are absolutely summable uniformly in time throughout the coefficient disc. -/
theorem fibreCoefficientFamily_symbol_series_absolute (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    (∑' p, ENNReal.ofReal ‖fibreMonomial ξ p‖ *
      ⨆ t, ‖fibreCoefficientSymbol η G v r p t‖ₑ) < ⊤ := by
  exact ((fibreMonomial_weighted_energy_le _ ξ hξ _).trans
    (fibreCoefficientFamily_weighted_symbol_le η Cw hη0 hη hCw G hG hv hw)).trans_lt
      ENNReal.ofReal_lt_top

end AVRegularity.CycleDamping.Graph
end

section
open Homogenization AVRegularity.Sobolev MeasureTheory
open scoped ENNReal
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping.Graph

/-! Every-time identification of the literal projected coefficient forcing series. -/

/-- The literal projected forcing sum equals the projection of its unprojected series on every time trace. -/
theorem fibreCoefficientFamily_projected_source_series (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) (t : ℝ) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    (fun x => ∑' p, fibreCoefficientScaledSource η v r ξ p t x) =ᵐ[volume.restrict AVenhance.unitCube]
      cellQ0 (fun x => ∑' p, fibreMonomial ξ p * fibreCoefficientSource η v r p t x) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let f := fun p x => fibreMonomial ξ p * fibreCoefficientSource η v r p t x
  have hs : (∑' p, cellL2Norm (f p)) < ⊤ :=
    fibreCoefficientFamily_source_trace_summable η Cw hη hCw G hG hv hw ξ hξ t
  have hx := (cellLpSeries_memLp_bound (volume.restrict AVenhance.unitCube) f hs).2.2
  filter_upwards [hx] with x hx
  have hq := cellQ0_tsum_of_cellL2Norm f hs x hx.of_norm
  have he p : cellQ0 (f p) x = fibreCoefficientScaledSource η v r ξ p t x := by
    change cellQ0 (fibreMonomial ξ p • fibreCoefficientSource η v r p t) x = _
    rw [cellQ0_complex_smul]
    rfl
  exact (tsum_congr (fun p => (he p).symm)).trans hq.symm

end AVRegularity.CycleDamping.Graph
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping.Graph

/-! Uniform all-frequency homogeneous bounds for the actual symbol family. -/

/-- The actual symbol coefficients have individual geometric bounds uniform in time. -/
theorem fibreCoefficientFamily_symbol_individual_le (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) (p : ℕ × ℕ) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    (⨆ t, ‖fibreCoefficientSymbol η G v r p t‖ₑ) ≤
      ENNReal.ofReal ((6 * Cw + 24) * (fibreCoefficientMajorantRadius Cw)⁻¹ ^ (p.1 + p.2)) :=
  fibreCoefficient_individual_of_total_le _ _ (fibreCoefficientMajorantRadius_pos hCw) _
    (fibreCoefficientFamily_weighted_symbol_le η Cw hη0 hη hCw G hG hv hw) p

/-- Every actual homogeneous symbol polynomial has the uniform geometric Taylor estimate. -/
theorem fibreCoefficientFamily_symbol_homogeneous_le (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (n : ℕ) (ξ : Fin 2 → ℂ) (t : ℝ) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    ‖fibreHomogeneous (fibreCoefficientSymbol η G v r) ξ n t‖ ≤
      (6 * Cw + 24) * (2 * (fibreCoefficientMajorantRadius Cw)⁻¹) ^ n * fibreNorm ξ ^ n := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  have hR : 0 < fibreCoefficientMajorantRadius Cw := fibreCoefficientMajorantRadius_pos hCw
  apply fibreHomogeneous_scalar_le_of_geometric _ _ _ (by positivity) (by positivity)
  intro p s
  have he := (le_iSup_of_le s (le_rfl : ‖fibreCoefficientSymbol η G v r p s‖ₑ ≤
    ‖fibreCoefficientSymbol η G v r p s‖ₑ)).trans
      (fibreCoefficientFamily_symbol_individual_le η Cw hη0 hη hCw G hG hv hw p)
  rw [← ofReal_norm] at he
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp he

end AVRegularity.CycleDamping.Graph
end

section
open Homogenization AVRegularity.Sobolev MeasureTheory
open scoped ENNReal
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping.Graph

/-! Absolute pointwise convergence of the actual value and flux coefficient series. -/

/-- The constructed value and actual scaled flux series converge absolutely jointly almost everywhere. -/
theorem fibreCoefficientFamily_value_flux_summable_norm_ae (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    ∀ᵐ z ∂((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)),
      Summable (fun p => ‖fibreMonomial ξ p * cellValue (r p) z.1 z.2‖) ∧
      Summable (fun p => ‖fibreCoefficientScaledFlux η G r ξ p z.1 z.2‖) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let D := fun p => fibreMonomial ξ p • r p
  have hsD : (∑' p, cellEnergyNorm Set.univ (D p)) < ⊤ :=
    (fibreCoefficientFamily_series_energy_le η Cw hη hCw G hG hv hw ξ hξ).trans_lt (by simp)
  have hsol p : IsCellSolution Set.univ ⟨fun t _ => G t, v, 0, 0⟩
      (fibreCoefficientScaledSource η v r ξ p) (fibreCoefficientScaledFlux η G r ξ p) (D p) :=
    (fibreCoefficientFamily_scaled_isInverse η Cw hη G hG hv hw ξ p).1
  have hval := cellSolutionSeries_value_summable_norm_ae (fun _ => ⟨fun t _ => G t, v, 0, 0⟩)
    (fibreCoefficientScaledSource η v r ξ) (fibreCoefficientScaledFlux η G r ξ) D hsol hsD
  have hsum := fibreCoefficientFamily_scaled_forcing_summable η Cw hη hCw G hG hv hw ξ hξ
  have hFs : (∑' p, cellUlNorm Set.univ (fibreCoefficientScaledFlux η G r ξ p)) < ⊤ :=
    (ENNReal.tsum_le_tsum (fun p => le_add_left le_rfl)).trans_lt hsum
  have hflux := cellUlSeries_summable_norm_ae (fibreCoefficientScaledFlux η G r ξ)
    (fibreCoefficientFamily_scaled_flux_aestronglyMeasurable η Cw hη G hG hv hw ξ) hFs
  filter_upwards [hval, hflux] with z hz hzF
  exact ⟨hz, hzF⟩

end AVRegularity.CycleDamping.Graph
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal BigOperators
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping.Graph

/-! The actual weighted coordinate means recover the arbitrary-frequency graph pairing. -/

local instance graphFibreCoefficientMeanCoordinateSeriesProbCube : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using cellCube_volume_one⟩

/-- The actual coordinate mean series is the arbitrary-frequency mean of the literal graph value. -/
theorem fibreCoefficientFamily_mean_coordinate_series (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) (t : ℝ) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    (∑ j : Fin 2, ξ j * ∑' p, fibreMonomial ξ p * cellMean (fun y =>
      fibreDriftCoupling η v (fibreCoordinateFrequency j) t y * cellValue (r p) t y)) =
      cellMean (fun y => fibreDriftCoupling η v ξ t y * cellValue (fibreSeriesJet r ξ) t y) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let ρ := cellValue (fibreSeriesJet r ξ)
  have hi := fibreCoefficientFamily_series_isInverse η Cw hη hCw G hG hv hw ξ hξ
  have hsV := fibreCoefficientFamily_value_trace_summable η Cw hη hCw G hG hv hw ξ hξ t
  have hmean j : (∑' p, fibreMonomial ξ p * cellMean (fun y =>
      fibreDriftCoupling η v (fibreCoordinateFrequency j) t y * cellValue (r p) t y)) =
      cellMean (fun y => fibreDriftCoupling η v (fibreCoordinateFrequency j) t y * ρ t y) := by
    let b := fibreDriftCoupling η v (fibreCoordinateFrequency j) t
    have hb : Measurable b := (fibreDriftCoupling_measurable η hv
      (fibreCoordinateFrequency j)).comp ((measurable_const (a := t)).prodMk measurable_id)
    have hB y : ‖b y‖ ≤ Cw := by
      simpa only [fibreCoordinateFrequency_norm, mul_one] using
        fibreDriftCoupling_norm_le η Cw v hw (fibreCoordinateFrequency j) t y
    have hbl : MemLp b 2 (volume.restrict AVenhance.unitCube) :=
      MemLp.of_bound hb.aestronglyMeasurable Cw (Filter.Eventually.of_forall hB)
    exact (fibreMean_monomial_tsum ξ b hbl (fun p => cellValue (r p) t) hsV).symm
  have hcoord : (∑ j : Fin 2, ξ j * ∑' p, fibreMonomial ξ p * cellMean (fun y =>
      fibreDriftCoupling η v (fibreCoordinateFrequency j) t y * cellValue (r p) t y)) =
      cellMean (fun y => fibreDriftCoupling η v ξ t y * ρ t y) := by
    simp_rw [hmean]
    exact fibreDriftCoupling_mean_coordinates η Cw hv hw ξ t (ρ t)
      (hi.1.2.2.1 t (Set.mem_univ t)).1
  exact hcoord

end AVRegularity.CycleDamping.Graph
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped BigOperators
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping.Graph

/-! Actual convergence and evaluation of the coordinate drift-mean symbol series. -/

/-- The actual drift symbol series converges at every time in the coefficient disc. -/
theorem fibreCoefficientFamily_drift_symbol_summable (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) (t : ℝ) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    Summable (fun p => fibreMonomial ξ p * fibreCoefficientDriftSymbol η v r p t) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  exact fibreTaylor_coordinate_summable ξ (fun _ => -Complex.I)
    (fun j p => cellMean (fun x => fibreDriftCoupling η v (fibreCoordinateFrequency j) t x *
      cellValue (r p) t x))
    (fun j => (fibreCoefficientFamily_mean_summable_norm η Cw hη hCw G hG hv hw ξ hξ t j).of_norm)

/-- The actual drift symbol series has the literal arbitrary-frequency multiplier mean. -/
theorem fibreCoefficientFamily_drift_symbol_series (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) (t : ℝ) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    (∑' p, fibreMonomial ξ p * fibreCoefficientDriftSymbol η v r p t) =
      -Complex.I * cellMean (fun x => fibreDriftCoupling η v ξ t x *
        cellValue (fibreSeriesJet r ξ) t x) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let f := fun j p => cellMean (fun x => fibreDriftCoupling η v (fibreCoordinateFrequency j) t x *
    cellValue (r p) t x)
  have hs j : Summable (fun p => fibreMonomial ξ p * f j p) :=
    (fibreCoefficientFamily_mean_summable_norm η Cw hη hCw G hG hv hw ξ hξ t j).of_norm
  have hh := fibreTaylor_coordinate_series ξ (fun _ => -Complex.I) f hs
  have he : (∑ j : Fin 2, -Complex.I * ξ j * ∑' p, fibreMonomial ξ p * f j p) =
      -Complex.I * ∑ j : Fin 2, ξ j * ∑' p, fibreMonomial ξ p * f j p := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hcoord : (∑ j : Fin 2, ξ j * ∑' p, fibreMonomial ξ p * f j p) =
      cellMean (fun x => fibreDriftCoupling η v ξ t x *
        cellValue (fibreSeriesJet r ξ) t x) :=
    fibreCoefficientFamily_mean_coordinate_series η Cw hη hCw G hG hv hw ξ hξ t
  rw [he, hcoord] at hh
  exact hh

end AVRegularity.CycleDamping.Graph
end

section
open Homogenization AVRegularity.Sobolev
open scoped BigOperators
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping.Graph

/-! The actual convergent symbol series has the literal metric and drift-mean formula. -/

/-- The actual symbol Taylor series converges and evaluates to the literal graph symbol at every time. -/
theorem fibreCoefficientFamily_symbol_series (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) (t : ℝ) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    fibreSeriesC (fibreCoefficientSymbol η G v r) ξ t =
      -(η : ℂ) * fibreQuad (G t) ξ - Complex.I *
        cellMean (fun x => fibreDriftCoupling η v ξ t x * cellValue (fibreSeriesJet r ξ) t x) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  have hm := fibreCoefficientMetricSymbol_hasSum η G ξ t
  have hd := fibreCoefficientFamily_drift_symbol_summable η Cw hη hCw G hG hv hw ξ hξ t
  change (∑' p, fibreMonomial ξ p * fibreCoefficientSymbol η G v r p t) = _
  simp only [fibreCoefficientSymbol, mul_add]
  rw [hm.summable.tsum_add hd, hm.tsum_eq,
    fibreCoefficientFamily_drift_symbol_series η Cw hη hCw G hG hv hw ξ hξ t]
  ring

end AVRegularity.CycleDamping.Graph
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal BigOperators
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping.Graph

/-! Every-time identification of the actual nonlinear scalar Taylor series. -/

local instance graphFibreCoefficientUnprojectedGraphSeriesProbCube : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using cellCube_volume_one⟩

/-- The actual unprojected scalar forcing equals the nonlinear graph expression almost everywhere on every trace. -/
theorem fibreCoefficientFamily_unprojected_graph_series (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) (t : ℝ) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let ρ := cellValue (fibreSeriesJet r ξ)
    (fun x => ∑' p, fibreMonomial ξ p * fibreCoefficientSource η v r p t x) =ᵐ[volume.restrict AVenhance.unitCube]
      (fun x => -Complex.I * (fibreDriftCoupling η v ξ t x * (1 + ρ t x)) +
        Complex.I * ρ t x * cellMean (fun y => fibreDriftCoupling η v ξ t y * ρ t y)) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let ρ := cellValue (fibreSeriesJet r ξ)
  have hi := fibreCoefficientFamily_series_isInverse η Cw hη hCw G hG hv hw ξ hξ
  have hsV := fibreCoefficientFamily_value_trace_summable η Cw hη hCw G hG hv hw ξ hξ t
  have hsS := fibreCoefficientFamily_source_trace_summable η Cw hη hCw G hG hv hw ξ hξ t
  have hg := fibreCoefficientFamily_mean_summable_norm η Cw hη hCw G hG hv hw ξ hξ t
  have hmean j : (∑' p, fibreMonomial ξ p * cellMean (fun y =>
      fibreDriftCoupling η v (fibreCoordinateFrequency j) t y * cellValue (r p) t y)) =
      cellMean (fun y => fibreDriftCoupling η v (fibreCoordinateFrequency j) t y * ρ t y) := by
    let b := fibreDriftCoupling η v (fibreCoordinateFrequency j) t
    have hb : Measurable b := (fibreDriftCoupling_measurable η hv
      (fibreCoordinateFrequency j)).comp ((measurable_const (a := t)).prodMk measurable_id)
    have hB y : ‖b y‖ ≤ Cw := by
      simpa only [fibreCoordinateFrequency_norm, mul_one] using
        fibreDriftCoupling_norm_le η Cw v hw (fibreCoordinateFrequency j) t y
    have hbl : MemLp b 2 (volume.restrict AVenhance.unitCube) :=
      MemLp.of_bound hb.aestronglyMeasurable Cw (Filter.Eventually.of_forall hB)
    exact (fibreMean_monomial_tsum ξ b hbl (fun p => cellValue (r p) t) hsV).symm
  have hcoord : (∑ j : Fin 2, ξ j * ∑' p, fibreMonomial ξ p * cellMean (fun y =>
      fibreDriftCoupling η v (fibreCoordinateFrequency j) t y * cellValue (r p) t y)) =
      cellMean (fun y => fibreDriftCoupling η v ξ t y * ρ t y) := by
    simp_rw [hmean]
    exact fibreDriftCoupling_mean_coordinates η Cw hv hw ξ t (ρ t)
      (hi.1.2.2.1 t (Set.mem_univ t)).1
  have hVs := (cellLpSeries_memLp_bound (volume.restrict AVenhance.unitCube)
    (fun p y => fibreMonomial ξ p * cellValue (r p) t y) hsV).2.2
  have hSs := (cellLpSeries_memLp_bound (volume.restrict AVenhance.unitCube)
    (fun p y => fibreMonomial ξ p * fibreCoefficientSource η v r p t y) hsS).2.2
  filter_upwards [hVs, hSs] with x hxV hxS
  have he := fibreCoefficientSource_series_of_summable η v r ξ t x hxS.of_norm hxV hg
  have hρ : (∑' p, fibreMonomial ξ p * cellValue (r p) t x) = ρ t x := rfl
  rw [hcoord, hρ] at he
  apply he.trans
  change _ = -Complex.I * (fibreDriftCoupling η v ξ t x * (1 + ρ t x)) +
    Complex.I * ρ t x * cellMean (fun y => fibreDriftCoupling η v ξ t y * ρ t y)
  ring

end AVRegularity.CycleDamping.Graph
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping.Graph

/-! Identification of the actual projected scalar coefficient forcing with the graph source. -/

/-- The actual projected coefficient series equals the literal graph source on every time trace. -/
theorem fibreCoefficientFamily_graph_source_series (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) (t : ℝ) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    (fun x => ∑' p, fibreCoefficientScaledSource η v r ξ p t x) =ᵐ[volume.restrict AVenhance.unitCube]
      fibreGraphSource η v ξ (cellValue (fibreSeriesJet r ξ)) t := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  have hi := fibreCoefficientFamily_series_isInverse η Cw hη hCw G hG hv hw ξ hξ
  have hp := fibreCoefficientFamily_projected_source_series η Cw hη hCw G hG hv hw ξ hξ t
  have hu := fibreCoefficientFamily_unprojected_graph_series η Cw hη hCw G hG hv hw ξ hξ t
  have hq := cellQ0_congr_ae _ _ hu
  have he := fibreGraphSource_projection η Cw hv hw ξ hi t
  exact hp.trans (hq.trans (Filter.Eventually.of_forall (congrFun he)))

/-! The constructed literal Taylor series solves the actual nonlinear graph equation. -/

/-- The actual coefficient family gives a genuine mean-zero inverse for the literal nonlinear graph source and flux. -/
theorem fibreCoefficientFamily_graph_isInverse (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    IsCellInverseValue ⟨fun t _ => G t, v, 0, 0⟩
      (fibreGraphSource η v ξ (cellValue (fibreSeriesJet r ξ)))
      (fibreGraphFlux η G ξ (cellValue (fibreSeriesJet r ξ))) (fibreSeriesJet r ξ) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  have hi := fibreCoefficientFamily_series_isInverse η Cw hη hCw G hG hv hw ξ hξ
  have hs : ∀ᵐ t ∂volume.restrict Set.univ,
      (fun x => ∑' p, fibreCoefficientScaledSource η v r ξ p t x) =ᵐ[volume.restrict AVenhance.unitCube]
        fibreGraphSource η v ξ (cellValue (fibreSeriesJet r ξ)) t :=
    Filter.Eventually.of_forall (fibreCoefficientFamily_graph_source_series η Cw hη hCw G hG hv hw ξ hξ)
  have hpoint := fibreCoefficientFamily_value_flux_summable_norm_ae η Cw hη hCw G hG hv hw ξ hξ
  have hF : ∀ᵐ z ∂((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)),
      (∑' p, fibreCoefficientScaledFlux η G r ξ p z.1 z.2) =
        fibreGraphFlux η G ξ (cellValue (fibreSeriesJet r ξ)) z.1 z.2 := by
    filter_upwards [hpoint] with z hz
    exact fibreCoefficientFlux_series_of_summable η G r ξ z.1 z.2 hz.2.of_norm hz.1.of_norm
  refine ⟨?_, hi.2⟩
  exact cellSolution_source_congr_sections Set.univ ⟨fun t _ => G t, v, 0, 0⟩ _ _ _ _
    (fibreSeriesJet r ξ) hs (Measure.ae_ae_of_ae_prod hF) hi.1

end AVRegularity.CycleDamping.Graph
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping.Graph

/-! An actual convergent fibre graph and symbol constructed from the literal inverse coefficients. -/

/-- A graph bound depending only on the scaled drift bound. -/
def fibreCoefficientGraphBound (Cw : ℝ) : ℝ :=
  2 * (fibreCoefficientMajorantRadius Cw)⁻¹ + (6 * Cw + 24) + 2

/-- The literal coefficient construction gives the complete public fibre graph predicate. -/
theorem fibreCoefficientFamily_isFibreGraph (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    IsFibreGraph η G v (fibreCoefficientMajorantRadius Cw) (fibreCoefficientGraphBound Cw)
      r (fibreCoefficientSymbol η G v r) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let R := fibreCoefficientMajorantRadius Cw
  let C := fibreCoefficientGraphBound Cw
  have hR : 0 < R := fibreCoefficientMajorantRadius_pos hCw
  have hRi : 0 ≤ R⁻¹ := (inv_pos.mpr hR).le
  have hK : 0 ≤ 6 * Cw + 24 := by positivity
  have heC : C = 2 * R⁻¹ + (6 * Cw + 24) + 2 := rfl
  have h2 : 2 ≤ C := by rw [heC]; linarith
  have hC0 : 2 * R⁻¹ ≤ C := by rw [heC]; linarith
  have hCK : 6 * Cw + 24 ≤ C := by rw [heC]; linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fibreCoefficientFamily_symbol_low_order η Cw hη G hG hv hw
  · intro ξ hξ
    have hξ' : fibreNorm ξ ≤ R := hξ.le
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact ((fibreMonomial_weighted_energy_le R ξ hξ' _).trans
        (fibreCoefficientFamily_weighted_energy_le η Cw hη hCw G hG hv hw)).trans_lt (by simp)
    · exact fibreCoefficientFamily_symbol_series_absolute η Cw hη0 hη hCw G hG hv hw ξ hξ'
    · exact fibreCoefficientFamily_graph_isInverse η Cw hη hCw G hG hv hw ξ hξ'
    · intro t
      exact fibreCoefficientFamily_symbol_series η Cw hη hCw G hG hv hw ξ hξ' t
    · apply (fibreCoefficientFamily_summed_energy_le η Cw hη hCw G hG hv hw ξ hξ').trans
      have ht : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by norm_num
      rw [ht, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      apply ENNReal.ofReal_le_ofReal
      change 2 * (fibreNorm ξ / R) ≤ C * fibreNorm ξ
      have he : 2 * (fibreNorm ξ / R) = (2 * R⁻¹) * fibreNorm ξ := by
        rw [div_eq_mul_inv]
        ring
      rw [he]
      exact mul_le_mul_of_nonneg_right hC0 (fibreNorm_nonneg ξ)
  · intro n ξ
    apply (fibreCoefficientFamily_homogeneous_energy_le η Cw hη hCw G hG hv hw n ξ).trans
    apply ENNReal.ofReal_le_ofReal
    change 2 * (2 * R⁻¹) ^ n * fibreNorm ξ ^ n ≤ C * (2 / R) ^ n * fibreNorm ξ ^ n
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h2 (by positivity)) (pow_nonneg (fibreNorm_nonneg ξ) n)
  · intro n ξ t
    apply (fibreCoefficientFamily_symbol_homogeneous_le η Cw hη0 hη hCw G hG hv hw n ξ t).trans
    change (6 * Cw + 24) * (2 * R⁻¹) ^ n * fibreNorm ξ ^ n ≤ C * (2 / R) ^ n * fibreNorm ξ ^ n
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCK (by positivity)) (pow_nonneg (fibreNorm_nonneg ξ) n)

end AVRegularity.CycleDamping.Graph
end
