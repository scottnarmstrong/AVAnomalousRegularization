-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.FibreCoefficientFamilyMajorant
import AVRegularity.CycleEvolution.CellEnergySpaceRawJetCauchyBound
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Geometric individual coefficient bounds from the proved total weighted majorant. -/

/-- A positive-radius unit weighted majorant bounds each coefficient by the inverse radius power. -/
theorem fibreCoefficient_individual_le (R : ℝ) (hR : 0 < R)
    (E : ℕ × ℕ → ℝ≥0∞)
    (hE : (∑' p, fibreCoefficientWeight (ENNReal.ofReal R) p * E p) ≤ 1) (p : ℕ × ℕ) :
    E p ≤ ENNReal.ofReal ((R⁻¹) ^ (p.1 + p.2)) := by
  let a := ENNReal.ofReal (R ^ (p.1 + p.2))
  have ha0 : a ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hR _))
  have hat : a ≠ ⊤ := ENNReal.ofReal_ne_top
  have hh : a * E p ≤ 1 := by
    dsimp only [a]
    rw [ENNReal.ofReal_pow hR.le]
    exact (ENNReal.le_tsum p).trans hE
  calc
    E p = a⁻¹ * (a * E p) := (ENNReal.inv_mul_cancel_left ha0 hat).symm
    _ ≤ a⁻¹ * 1 := mul_le_mul' le_rfl hh
    _ = ENNReal.ofReal ((R⁻¹) ^ (p.1 + p.2)) := by
      rw [mul_one]
      dsimp only [a]
      rw [← ENNReal.ofReal_inv_of_pos (pow_pos hR _), inv_pow]

/-- Every actual coefficient of the constructed family has the geometric energy bound. -/
theorem fibreCoefficientFamily_individual_energy_le (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) (p : ℕ × ℕ) :
    cellEnergyNorm Set.univ (fibreCoefficientFamily η Cw hη G hG hv hw p) ≤
      ENNReal.ofReal ((fibreCoefficientMajorantRadius Cw)⁻¹ ^ (p.1 + p.2)) :=
  fibreCoefficient_individual_le _ (fibreCoefficientMajorantRadius_pos hCw) _
    (fibreCoefficientFamily_weighted_energy_le η Cw hη hCw G hG hv hw) p

/-- A positive-radius weighted total bound gives the corresponding individual geometric bound. -/
theorem fibreCoefficient_individual_of_total_le (R K : ℝ) (hR : 0 < R)
    (E : ℕ × ℕ → ℝ≥0∞)
    (hE : (∑' p, fibreCoefficientWeight (ENNReal.ofReal R) p * E p) ≤ ENNReal.ofReal K)
    (p : ℕ × ℕ) : E p ≤ ENNReal.ofReal (K * (R⁻¹) ^ (p.1 + p.2)) := by
  let a := ENNReal.ofReal (R ^ (p.1 + p.2))
  have ha0 : a ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos hR _))
  have hat : a ≠ ⊤ := ENNReal.ofReal_ne_top
  have hh : a * E p ≤ ENNReal.ofReal K := by
    dsimp only [a]
    rw [ENNReal.ofReal_pow hR.le]
    exact (ENNReal.le_tsum p).trans hE
  calc
    E p = a⁻¹ * (a * E p) := (ENNReal.inv_mul_cancel_left ha0 hat).symm
    _ ≤ a⁻¹ * ENNReal.ofReal K := mul_le_mul' le_rfl hh
    _ = ENNReal.ofReal (K * (R⁻¹) ^ (p.1 + p.2)) := by
      dsimp only [a]
      rw [← ENNReal.ofReal_inv_of_pos (pow_pos hR _),
        ← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg hR.le _)), inv_pow]
      congr 1
      exact mul_comm _ _

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Absolute energy summability of the actual literal fibre coefficient series. -/

/-- The actual monomial-scaled coefficients have absolutely summable energy within the explicit radius. -/
theorem fibreCoefficientFamily_series_energy_le (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) :
    (∑' p, cellEnergyNorm Set.univ
      (fibreMonomial ξ p • fibreCoefficientFamily η Cw hη G hG hv hw p)) ≤ 1 := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  calc
    _ ≤ ∑' p, ENNReal.ofReal ‖fibreMonomial ξ p‖ * cellEnergyNorm Set.univ (r p) := by
      apply ENNReal.tsum_le_tsum
      intro p
      simpa only [ofReal_norm] using cellEnergyNorm_complex_smul Set.univ
        (fibreMonomial ξ p) (r p)
        (cellSolution_gradient_aestronglyMeasurable
          (fibreCoefficientFamily_isInverse η Cw hη G hG hv hw p).1)
    _ ≤ ∑' p, fibreCoefficientWeight (ENNReal.ofReal (fibreCoefficientMajorantRadius Cw)) p *
        cellEnergyNorm Set.univ (r p) :=
      fibreMonomial_weighted_energy_le _ ξ hξ _
    _ ≤ 1 := fibreCoefficientFamily_weighted_energy_le η Cw hη hCw G hG hv hw

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Minus-conjugate reality of the literal graph series, obtained from the actual coefficient recurrence. -/

theorem fibreMonomial_star (ξ : Fin 2 → ℂ) (p : ℕ × ℕ) :
    fibreMonomial (fun j => star (ξ j)) p = star (fibreMonomial ξ p) := by
  change star (ξ 0) ^ p.1 * star (ξ 1) ^ p.2 = star (ξ 0 ^ p.1 * ξ 1 ^ p.2)
  rw [star_mul, star_pow, star_pow]
  ring

theorem fibreSeriesJet_reality_of_coefficients (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ)
    (hr : ∀ p t, (fun x => star (cellValue (r p) t x)) =ᵐ[volume.restrict AVenhance.unitCube]
      (fun x => fibreRealitySign p * cellValue (r p) t x)) (ξ : Fin 2 → ℂ) (t : ℝ) :
    cellValue (fibreSeriesJet r (fun j => -star (ξ j))) t =ᵐ[volume.restrict AVenhance.unitCube]
      (fun x => star (cellValue (fibreSeriesJet r ξ) t x)) := by
  filter_upwards [ae_all_iff.mpr (fun p => hr p t)] with x hx
  change (∑' p, fibreMonomial (fun j => -star (ξ j)) p * cellValue (r p) t x) =
    star (∑' p, fibreMonomial ξ p * cellValue (r p) t x)
  rw [tsum_star]
  apply tsum_congr
  intro p
  rw [fibreMonomial_neg, fibreMonomial_star, star_mul, hx p]
  change fibreRealitySign p * star (fibreMonomial ξ p) * cellValue (r p) t x = _
  ring

theorem fibreCoefficientFamily_graph_reality (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (t : ℝ) :
    cellValue (fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hw)
      (fun j => -star (ξ j))) t =ᵐ[volume.restrict AVenhance.unitCube]
      (fun x => star (cellValue (fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hw) ξ) t x)) :=
  fibreSeriesJet_reality_of_coefficients _
    (fibreCoefficientFamily_reality η Cw hη G hG hv hw) ξ t

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Absolute weighted forcing bounds for the actual fibre coefficient construction. -/

/-- The actual coefficient forcing has finite total weighted uniformly local energy. -/
theorem fibreCoefficientFamily_weighted_forcing_le (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    (∑' p, fibreCoefficientWeight (ENNReal.ofReal (fibreCoefficientMajorantRadius Cw)) p *
      (cellUlNorm Set.univ (fibreCoefficientSource η v r p) +
        cellUlNorm Set.univ (fibreCoefficientFlux η G r p))) ≤
      (2 * ENNReal.ofReal (fibreCoefficientMajorantRadius Cw)) * (3 * ENNReal.ofReal Cw + 8) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let E := fun p => cellEnergyNorm Set.univ (r p)
  let U := fun p => cellUlNorm Set.univ (fibreCoefficientSource η v r p) +
    cellUlNorm Set.univ (fibreCoefficientFlux η G r p)
  have hz : U 0 = 0 := by
    dsimp only [U]
    rw [fibreCoefficientSource_zero, fibreCoefficientFlux_zero,
      cellUlNorm_zero_field, cellUlNorm_zero_field, zero_add]
  let A := fun p : ℕ × ℕ => fibreCoefficientStage η Cw hη G hG hv hw (p.1 + p.2) p
  apply fibreCoefficient_weighted_forcing_total_le _ (ENNReal.ofReal Cw) E U hz
    (fibreCoefficientFamily_weighted_energy_le η Cw hη hCw G hG hv hw)
  intro p
  exact fibreCoefficient_forcing_norm_bound η Cw hη G hG hv hw A p

/-! Small-radius absolute uniform L2 bounds for the actual forward graph coefficients. -/

theorem fibreCoefficientFamily_uniform_radius_gain (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ ≤ fibreCoefficientMajorantRadius Cw) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    (∑' p, fibreCoefficientWeight (ENNReal.ofReal ρ) p *
      ⨆ t, cellL2Norm (cellValue (r p) t)) ≤ ENNReal.ofReal (ρ / fibreCoefficientMajorantRadius Cw) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  calc
    _ ≤ ∑' p, fibreCoefficientWeight (ENNReal.ofReal ρ) p * cellEnergyNorm Set.univ (r p) := by
      apply ENNReal.tsum_le_tsum
      intro p
      exact mul_le_mul' le_rfl (iSup_le (fun t => cellValue_cellL2Norm_le_energy (r p) t))
    _ ≤ ENNReal.ofReal (ρ / fibreCoefficientMajorantRadius Cw) *
        ∑' p, fibreCoefficientWeight (ENNReal.ofReal (fibreCoefficientMajorantRadius Cw)) p *
          cellEnergyNorm Set.univ (r p) :=
      fibreCoefficient_weighted_radius_gain hρ (fibreCoefficientMajorantRadius_pos hCw) hρR _
        (fibreCoefficientFamily_energy_zero η Cw hη G hG hv hw)
    _ ≤ ENNReal.ofReal (ρ / fibreCoefficientMajorantRadius Cw) * 1 :=
      mul_le_mul' le_rfl (fibreCoefficientFamily_weighted_energy_le η Cw hη hCw G hG hv hw)
    _ = _ := mul_one _

end AVRegularity.CycleEvolution
end

section
namespace AVRegularity.CycleEvolution

/-! Actual weighted scalar Taylor majorants bound every coefficient at every time. -/

theorem fibreScalar_weighted_coefficient_norm_le (a : ℕ × ℕ → ℝ → ℂ) (R K : ℝ)
    (hR : 0 < R) (hK : 0 ≤ K)
    (ha : (∑' p, fibreCoefficientWeight (ENNReal.ofReal R) p * ⨆ t, ‖a p t‖ₑ) ≤ ENNReal.ofReal K)
    (p : ℕ × ℕ) (t : ℝ) : ‖a p t‖ ≤ K * R⁻¹ ^ (p.1 + p.2) := by
  have hi := fibreCoefficient_individual_of_total_le R K hR
    (fun p => ⨆ t, ‖a p t‖ₑ) ha p
  have hb := (le_iSup (fun t => ‖a p t‖ₑ) t).trans hi
  rw [← ofReal_norm] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK (by positivity))).mp hb

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! An actual future-dependent coefficient family from the reversed metric and opposite drift. -/

def fibreAdjointCorrectionCoefficients (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) :
    ℕ × ℕ → ℝ → Vec 2 → ℂ :=
  fibreReverseValueCoefficients
    (fibreCoefficientFamily η Cw hη (fun t => G (-t)) (cellMetric_timeReverse hG)
      (cellDrift_timeReverse hv) (cellDrift_timeReverse_scaled_bound hw))

theorem fibreAdjointCorrectionCoefficients_zero (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) :
    fibreAdjointCorrectionCoefficients η Cw hη G hG hv hw 0 = 0 := by
  funext t x
  simp [fibreAdjointCorrectionCoefficients, fibreReverseValueCoefficients,
    fibreCoefficientFamily_zero, cellValue]

theorem fibreAdjointCorrectionCoefficients_mean_zero (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) :
    ∀ p t, cellMean (fibreAdjointCorrectionCoefficients η Cw hη G hG hv hw p t) = 0 := by
  apply fibreReverseValueCoefficients_mean_zero
  intro p t
  exact (fibreCoefficientFamily_isInverse η Cw hη _ (cellMetric_timeReverse hG)
    (cellDrift_timeReverse hv) (cellDrift_timeReverse_scaled_bound hw) p).2.1 t

theorem fibreAdjointCorrectionCoefficients_memLp (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (p : ℕ × ℕ) (t : ℝ) :
    MemLp (fibreAdjointCorrectionCoefficients η Cw hη G hG hv hw p t) 2
      (volume.restrict AVenhance.unitCube) := by
  have hi := fibreCoefficientFamily_isInverse η Cw hη _ (cellMetric_timeReverse hG)
    (cellDrift_timeReverse hv) (cellDrift_timeReverse_scaled_bound hw) p
  exact (hi.1.2.2.1 (-t) (Set.mem_univ _)).1.const_smul ((-1 : ℂ) ^ (p.1 + p.2))

theorem fibreAdjointCorrectionCoefficients_weighted_le (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ ≤ fibreCoefficientMajorantRadius Cw) :
    (∑' p, fibreCoefficientWeight (ENNReal.ofReal ρ) p *
      ⨆ t, cellL2Norm (fibreAdjointCorrectionCoefficients η Cw hη G hG hv hw p t)) ≤
        ENNReal.ofReal (ρ / fibreCoefficientMajorantRadius Cw) := by
  apply fibreReverseValueCoefficients_weighted_le _ hρ
    (fibreCoefficientMajorantRadius_pos hCw) hρR
  · exact fibreCoefficientFamily_energy_zero η Cw hη _ (cellMetric_timeReverse hG)
      (cellDrift_timeReverse hv) (cellDrift_timeReverse_scaled_bound hw)
  · exact fibreCoefficientFamily_weighted_energy_le η Cw hη hCw _ (cellMetric_timeReverse hG)
      (cellDrift_timeReverse hv) (cellDrift_timeReverse_scaled_bound hw)

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! Absolute uniform time convergence of the actual drift-mean symbol coefficients. -/

/-- The actual drift symbol coefficients have a finite total weighted majorant uniform in time. -/
theorem fibreCoefficientFamily_weighted_drift_symbol_le (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    (∑' p, fibreCoefficientWeight (ENNReal.ofReal (fibreCoefficientMajorantRadius Cw)) p *
      ⨆ t, ‖fibreCoefficientDriftSymbol η v r p t‖ₑ) ≤
      (2 * ENNReal.ofReal (fibreCoefficientMajorantRadius Cw)) * (3 * ENNReal.ofReal Cw + 8) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let E := fun p => cellEnergyNorm Set.univ (r p)
  let U := fun p => ⨆ t, ‖fibreCoefficientDriftSymbol η v r p t‖ₑ
  have hz : U 0 = 0 := by
    simp [U, fibreCoefficientDriftSymbol, fibreCoefficientDirections_zero]
  let A := fun p : ℕ × ℕ => fibreCoefficientStage η Cw hη G hG hv hw (p.1 + p.2) p
  apply fibreCoefficient_weighted_forcing_total_le _ (ENNReal.ofReal Cw) E U hz
    (fibreCoefficientFamily_weighted_energy_le η Cw hη hCw G hG hv hw)
  intro p
  apply (fibreCoefficientDriftSymbol_uniform_le η Cw hv hw A p).trans
  have hl : (∑ j ∈ fibreCoefficientDirections p, ENNReal.ofReal Cw * E (fibreCoefficientPrevious p j)) ≤
      ∑ j ∈ fibreCoefficientDirections p, ENNReal.ofReal Cw *
        ((if p = cellJetDirection j then 1 else 0) + E (fibreCoefficientPrevious p j)) := by
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul' le_rfl (le_add_left le_rfl)
  exact hl.trans ((le_add_right le_rfl).trans (le_add_right le_rfl))

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Every-time weighted scalar forcing majorants for the actual family. -/

/-- Every trace of the actual scalar coefficient forcing has the weighted total majorant. -/
theorem fibreCoefficientFamily_weighted_source_trace_le (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) (t : ℝ) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    (∑' p, fibreCoefficientWeight (ENNReal.ofReal (fibreCoefficientMajorantRadius Cw)) p *
      cellL2Norm (fibreCoefficientSource η v r p t)) ≤
      (2 * ENNReal.ofReal (fibreCoefficientMajorantRadius Cw)) * (3 * ENNReal.ofReal Cw + 8) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let E := fun p => cellEnergyNorm Set.univ (r p)
  let U := fun p => cellL2Norm (fibreCoefficientSource η v r p t)
  have hz : U 0 = 0 := by
    dsimp only [U]
    rw [fibreCoefficientSource_zero]
    simp [cellL2Norm]
  let A := fun p : ℕ × ℕ => fibreCoefficientStage η Cw hη G hG hv hw (p.1 + p.2) p
  apply fibreCoefficient_weighted_forcing_total_le _ (ENNReal.ofReal Cw) E U hz
    (fibreCoefficientFamily_weighted_energy_le η Cw hη hCw G hG hv hw)
  intro p
  exact (fibreCoefficientSource_cellL2Norm_le η Cw hv hw A p t).trans
    (le_add_right le_rfl)

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Every-time convergence and interchange for the actual coefficient multiplier means. -/

local instance cycleEvolutionFibreCoefficientMeanSeriesProbCube : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using cellCube_volume_one⟩

/-- The actual monomial value traces are absolutely L2 summable at every time. -/
theorem fibreCoefficientFamily_value_trace_summable (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) (t : ℝ) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    (∑' p, cellL2Norm (fun x => fibreMonomial ξ p * cellValue (r p) t x)) < ⊤ := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  have hs : (∑' p, cellEnergyNorm Set.univ (fibreMonomial ξ p • r p)) < ⊤ :=
    (fibreCoefficientFamily_series_energy_le η Cw hη hCw G hG hv hw ξ hξ).trans_lt (by simp)
  exact (ENNReal.tsum_le_tsum (fun p =>
    cellValue_cellL2Norm_le_energy (fibreMonomial ξ p • r p) t)).trans_lt hs

/-- Each actual coordinate multiplier mean series is absolutely convergent on every time trace. -/
theorem fibreCoefficientFamily_mean_summable_norm (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) (t : ℝ) (j : Fin 2) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    Summable (fun p => ‖fibreMonomial ξ p *
      cellMean (fun x => fibreDriftCoupling η v (fibreCoordinateFrequency j) t x *
        cellValue (r p) t x)‖) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let b := fibreDriftCoupling η v (fibreCoordinateFrequency j) t
  have hb : Measurable b := (fibreDriftCoupling_measurable η hv
    (fibreCoordinateFrequency j)).comp ((measurable_const (a := t)).prodMk measurable_id)
  have hB x : ‖b x‖ ≤ Cw := by
    simpa only [fibreCoordinateFrequency_norm, mul_one] using
      fibreDriftCoupling_norm_le η Cw v hw (fibreCoordinateFrequency j) t x
  have hbl : MemLp b 2 (volume.restrict AVenhance.unitCube) :=
    MemLp.of_bound hb.aestronglyMeasurable Cw (Filter.Eventually.of_forall hB)
  exact fibreMean_monomial_summable_norm ξ b hbl (fun p => cellValue (r p) t)
    (fibreCoefficientFamily_value_trace_summable η Cw hη hCw G hG hv hw ξ hξ t)

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Absolute forcing summability of the actual monomial coefficient series. -/

/-- Monomial weighting preserves the finite forcing majorant throughout the coefficient radius. -/
theorem fibreCoefficientFamily_series_forcing_le (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    (∑' p, ENNReal.ofReal ‖fibreMonomial ξ p‖ *
      (cellUlNorm Set.univ (fibreCoefficientSource η v r p) +
        cellUlNorm Set.univ (fibreCoefficientFlux η G r p))) ≤
      (2 * ENNReal.ofReal (fibreCoefficientMajorantRadius Cw)) * (3 * ENNReal.ofReal Cw + 8) := by
  exact (fibreMonomial_weighted_energy_le _ ξ hξ _).trans
    (fibreCoefficientFamily_weighted_forcing_le η Cw hη hCw G hG hv hw)

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Exact minus-conjugate reality of the actual scalar symbol series at every time. -/

theorem fibreSeriesC_reality_of_coefficients (lam : ℕ × ℕ → ℝ → ℂ)
    (hlam : ∀ p t, star (lam p t) = fibreRealitySign p * lam p t)
    (ξ : Fin 2 → ℂ) (t : ℝ) :
    fibreSeriesC lam (fun j => -star (ξ j)) t = star (fibreSeriesC lam ξ t) := by
  change (∑' p, fibreMonomial (fun j => -star (ξ j)) p * lam p t) =
    star (∑' p, fibreMonomial ξ p * lam p t)
  rw [tsum_star]
  apply tsum_congr
  intro p
  rw [fibreMonomial_neg, fibreMonomial_star, star_mul, hlam p t]
  change fibreRealitySign p * star (fibreMonomial ξ p) * lam p t = _
  ring

theorem fibreCoefficientFamily_symbol_series_reality (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (t : ℝ) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    fibreSeriesC (fibreCoefficientSymbol η G v r) (fun j => -star (ξ j)) t =
      star (fibreSeriesC (fibreCoefficientSymbol η G v r) ξ t) :=
  fibreSeriesC_reality_of_coefficients _
    (fibreCoefficientFamily_symbol_reality η Cw hη G hG hv hw) ξ t

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Every-time L2 membership, zero mean and first-order bound of the actual reversed graph series. -/

theorem fibreAdjointCorrectionCoefficients_series_properties (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) (t : ℝ) :
    let a := fibreAdjointCorrectionCoefficients η Cw hη G hG hv hw
    MemLp (fibreSeriesFun a ξ t) 2 (volume.restrict AVenhance.unitCube) ∧
      cellMean (fibreSeriesFun a ξ t) = 0 ∧
      cellL2Norm (fibreSeriesFun a ξ t) ≤
        ENNReal.ofReal (fibreNorm ξ / fibreCoefficientMajorantRadius Cw) := by
  let a := fibreAdjointCorrectionCoefficients η Cw hη G hG hv hw
  have hm := fibreAdjointCorrectionCoefficients_weighted_le η Cw hη hCw G hG hv hw
    (fibreNorm_nonneg ξ) hξ
  have hb := (fibreL2Series_norm_sum_le a (fibreNorm ξ) ξ le_rfl t).trans hm
  have hs := hb.trans_lt ENNReal.ofReal_lt_top
  have hsum := cellL2Series_memLp_bound (fun p x => fibreMonomial ξ p * a p t x) hs
  refine ⟨hsum.1, ?_, hsum.2.1.trans hb⟩
  change cellMean (fun x => ∑' p, fibreMonomial ξ p * a p t x) = 0
  rw [cellMean_tsum_of_cellL2Norm _ hs]
  have hz (p : ℕ × ℕ) : cellMean (fun x => fibreMonomial ξ p * a p t x) = 0 := by
    unfold cellMean
    rw [integral_const_mul]
    change fibreMonomial ξ p * cellMean (a p t) = 0
    rw [fibreAdjointCorrectionCoefficients_mean_zero η Cw hη G hG hv hw p t, mul_zero]
  simp only [hz, tsum_zero]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! First-order energy control of the actual summed fibre coefficient series. -/

/-- The energy sum of the actual monomial-scaled coefficients gains one frequency factor. -/
theorem fibreCoefficientFamily_series_linear_energy_le (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) :
    (∑' p, cellEnergyNorm Set.univ
      (fibreMonomial ξ p • fibreCoefficientFamily η Cw hη G hG hv hw p)) ≤
      ENNReal.ofReal (fibreNorm ξ / fibreCoefficientMajorantRadius Cw) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  calc
    _ ≤ ∑' p, ENNReal.ofReal ‖fibreMonomial ξ p‖ * cellEnergyNorm Set.univ (r p) := by
      apply ENNReal.tsum_le_tsum
      intro p
      simpa only [ofReal_norm] using cellEnergyNorm_complex_smul Set.univ
        (fibreMonomial ξ p) (r p)
        (cellSolution_gradient_aestronglyMeasurable
          (fibreCoefficientFamily_isInverse η Cw hη G hG hv hw p).1)
    _ ≤ ENNReal.ofReal (fibreNorm ξ / fibreCoefficientMajorantRadius Cw) *
        ∑' p, fibreCoefficientWeight (ENNReal.ofReal (fibreCoefficientMajorantRadius Cw)) p *
          cellEnergyNorm Set.univ (r p) :=
      fibreMonomial_linear_energy_le _ (fibreCoefficientMajorantRadius_pos hCw) ξ hξ _
        (fibreCoefficientFamily_energy_zero η Cw hη G hG hv hw)
    _ ≤ ENNReal.ofReal (fibreNorm ξ / fibreCoefficientMajorantRadius Cw) * 1 :=
      mul_le_mul' le_rfl (fibreCoefficientFamily_weighted_energy_le η Cw hη hCw G hG hv hw)
    _ = _ := mul_one _

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Absolute spatial L2 convergence of the actual unprojected scalar forcing series. -/

/-- The actual scalar forcing series is absolutely L2 convergent at every time throughout the coefficient disc. -/
theorem fibreCoefficientFamily_source_trace_summable (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) (t : ℝ) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    (∑' p, cellL2Norm (fun x => fibreMonomial ξ p * fibreCoefficientSource η v r p t x)) < ⊤ := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  have he p : cellL2Norm (fun x => fibreMonomial ξ p * fibreCoefficientSource η v r p t x) =
      ENNReal.ofReal ‖fibreMonomial ξ p‖ * cellL2Norm (fibreCoefficientSource η v r p t) := by
    change eLpNorm (fibreMonomial ξ p • fibreCoefficientSource η v r p t) 2 _ = _
    rw [eLpNorm_const_smul, ofReal_norm]
    rfl
  change (∑' p, cellL2Norm (fun x => fibreMonomial ξ p * fibreCoefficientSource η v r p t x)) < ⊤
  simp_rw [he]
  apply ((fibreMonomial_weighted_energy_le _ ξ hξ _).trans
    (fibreCoefficientFamily_weighted_source_trace_le η Cw hη hCw G hG hv hw t)).trans_lt
  finiteness

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! All-frequency homogeneous energy bounds for the actual correction coefficients. -/

/-- Every actual homogeneous correction polynomial has the geometric Taylor energy bound at every frequency. -/
theorem fibreCoefficientFamily_homogeneous_energy_le (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (n : ℕ) (ξ : Fin 2 → ℂ) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    cellEnergyNorm Set.univ (fibreHomogeneous r ξ n) ≤
      ENNReal.ofReal (2 * (2 * (fibreCoefficientMajorantRadius Cw)⁻¹) ^ n * fibreNorm ξ ^ n) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let R := fibreCoefficientMajorantRadius Cw
  let D := fun p => fibreMonomial ξ p • r p
  have hi p := fibreCoefficientFamily_scaled_isInverse η Cw hη G hG hv hw ξ p
  have hb := cellEnergyNorm_finset_sum_le_two (Finset.HasAntidiagonal.antidiagonal n) D
    (fun p _ a => (hi p).1.2.2.2.1 a) (fun p _ => (hi p).2.2)
  have hp p (hpn : p ∈ Finset.HasAntidiagonal.antidiagonal n) : cellEnergyNorm Set.univ (D p) ≤
      ENNReal.ofReal ((R⁻¹) ^ n * fibreNorm ξ ^ n) := by
    have ho : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hpn
    have he := fibreCoefficientFamily_individual_energy_le η Cw hη hCw G hG hv hw p
    have hm := cellEnergyNorm_complex_smul Set.univ (fibreMonomial ξ p) (r p)
      (cellSolution_gradient_aestronglyMeasurable
        (fibreCoefficientFamily_isInverse η Cw hη G hG hv hw p).1)
    apply hm.trans
    calc
      _ ≤ ENNReal.ofReal (fibreNorm ξ ^ n) * ENNReal.ofReal ((R⁻¹) ^ n) := by
        apply mul_le_mul'
        · rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (by simpa only [ho] using fibreMonomial_norm_le ξ p)
        · simpa only [ho] using he
      _ = _ := by
        rw [← ENNReal.ofReal_mul (pow_nonneg (fibreNorm_nonneg ξ) n)]
        congr 1
        exact mul_comm _ _
  have hn : ((n + 1 : ℕ) : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ n := by
    exact_mod_cast Nat.succ_le_of_lt ((show n < 2 ^ n from Nat.lt_two_pow_self))
  have hs : (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, cellEnergyNorm Set.univ (D p)) ≤
      (2 : ℝ≥0∞) ^ n * ENNReal.ofReal ((R⁻¹) ^ n * fibreNorm ξ ^ n) := by
    apply (Finset.sum_le_sum hp).trans
    rw [Finset.sum_const, nsmul_eq_mul, Finset.Nat.card_antidiagonal]
    exact mul_le_mul' hn le_rfl
  change cellEnergyNorm Set.univ (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, D p) ≤ _
  apply hb.trans
  apply (mul_le_mul' le_rfl hs).trans
  have hpow : (2 : ℝ≥0∞) ^ n = ENNReal.ofReal ((2 : ℝ) ^ n) := by
    simp [ENNReal.ofReal_pow]
  rw [hpow, ← ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)]
  have htwo : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by norm_num
  rw [htwo, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  apply ENNReal.ofReal_le_ofReal
  dsimp only [R]
  rw [mul_pow]
  ring_nf
  exact le_rfl

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! The actual forward/reversed graph overlap has a quadratically small Taylor majorant. -/

def fibreAdjointOverlapCoefficients (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) :
    ℕ × ℕ → ℝ → ℂ :=
  fibreMeanConvolution (fibreAdjointCorrectionCoefficients η Cw hη G hG hv hw)
    (fun p => cellValue (fibreCoefficientFamily η Cw hη G hG hv hw p))

theorem fibreAdjointOverlapCoefficients_weighted_le (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρR : ρ ≤ fibreCoefficientMajorantRadius Cw) :
    (∑' p, fibreCoefficientWeight (ENNReal.ofReal ρ) p *
      ⨆ t, ‖fibreAdjointOverlapCoefficients η Cw hη G hG hv hw p t‖ₑ) ≤
        ENNReal.ofReal (ρ / fibreCoefficientMajorantRadius Cw) ^ 2 := by
  have he := fibreMeanConvolution_weighted_le
    (fibreAdjointCorrectionCoefficients η Cw hη G hG hv hw)
    (fun p => cellValue (fibreCoefficientFamily η Cw hη G hG hv hw p))
    (fibreAdjointCorrectionCoefficients_memLp η Cw hη G hG hv hw)
    (fun p t => ((fibreCoefficientFamily_isInverse η Cw hη G hG hv hw p).1.2.2.1
      t (Set.mem_univ t)).1) (ENNReal.ofReal ρ)
  apply he.trans
  rw [pow_two]
  exact mul_le_mul'
    (fibreAdjointCorrectionCoefficients_weighted_le η Cw hη hCw G hG hv hw hρ hρR)
    (fibreCoefficientFamily_uniform_radius_gain η Cw hη hCw G hG hv hw hρ hρR)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! A first-order energy bound for the literal summed fibre graph series. -/

/-- The literal series of the actual coefficient family satisfies a linear energy estimate. -/
theorem fibreCoefficientFamily_summed_energy_le (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) :
    cellEnergyNorm Set.univ (fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hw) ξ) ≤
      2 * ENNReal.ofReal (fibreNorm ξ / fibreCoefficientMajorantRadius Cw) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let D := fun p => fibreMonomial ξ p • r p
  have hi := fun p => cellInverse_complex_smul
    (fibreCoefficientFamily_isInverse η Cw hη G hG hv hw p) (fibreMonomial ξ p)
  have hm : ∀ p a, AEStronglyMeasurable (fun z : ℝ × Vec 2 => D p z.1 a z.2)
      ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)) :=
    fun p => (hi p).1.2.2.2.1
  have hs : (∑' p, cellEnergyNorm Set.univ (D p)) < ⊤ :=
    (fibreCoefficientFamily_series_energy_le η Cw hη hCw G hG hv hw ξ hξ).trans_lt (by simp)
  have hb := (cellEnergyNorm_tsum_le D hm hs).trans
    (mul_le_mul' le_rfl (fibreCoefficientFamily_series_linear_energy_le η Cw hη hCw G hG hv hw ξ hξ))
  have he : fibreSeriesJet r ξ = (fun t a x => ∑' p, D p t a x) := by rfl
  change cellEnergyNorm Set.univ (fibreSeriesJet r ξ) ≤ _
  rw [he]
  exact hb

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

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

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev MeasureTheory
namespace AVRegularity.CycleEvolution

/-! The actual overlap correction has vanishing constant coefficient. -/

theorem fibreAdjointOverlapCoefficients_zero (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) :
    ∀ t, fibreAdjointOverlapCoefficients η Cw hη G hG hv hw 0 t = 0 := by
  intro t
  have hz : fibreAdjointCorrectionCoefficients η Cw hη G hG hv hw (0, 0) = 0 :=
    fibreAdjointCorrectionCoefficients_zero η Cw hη G hG hv hw
  simp [fibreAdjointOverlapCoefficients, fibreMeanConvolution, fibreCoefficientPairs,
    hz, cellMean]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! The actual graph gradient has the required linear squared interval-length bound. -/

theorem fibreCoefficientFamily_finite_gradient_energy (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw)
    {a b : ℝ} (hab : a ≤ b) :
    let D := fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hw) ξ
    (∫⁻ t in Set.Icc a b, cellL2Norm (cellGradient (D t)) ^ 2) ≤
      ENNReal.ofReal (b - a + 1) * (2 * ENNReal.ofReal (fibreNorm ξ / fibreCoefficientMajorantRadius Cw)) ^ 2 := by
  let D := fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hw) ξ
  have henergy := fibreCoefficientFamily_summed_energy_le η Cw hη hCw G hG hv hw ξ hξ
  have hgrad : cellUlNorm Set.univ (fun t => cellGradient (D t)) ≤
      2 * ENNReal.ofReal (fibreNorm ξ / fibreCoefficientMajorantRadius Cw) :=
    (show cellUlNorm Set.univ (fun t => cellGradient (D t)) ≤ cellEnergyNorm Set.univ D from
      le_add_left le_rfl).trans henergy
  have hi := cellUl_finite_interval_squared_le Set.univ (fun t => cellGradient (D t)) hab
  simp only [Set.inter_univ] at hi
  exact hi.trans (mul_le_mul' le_rfl (pow_le_pow_left' hgrad 2))

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleEvolution

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

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Absolute uniformly local summability of the projected scaled coefficient forcing. -/

/-- The actual projected scalar and vector coefficient forcing are absolutely uniformly locally summable. -/
theorem fibreCoefficientFamily_scaled_forcing_summable (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    (∑' p, (cellUlNorm Set.univ (fibreCoefficientScaledSource η v r ξ p) +
      cellUlNorm Set.univ (fibreCoefficientScaledFlux η G r ξ p))) < ⊤ := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  have hb := ENNReal.tsum_le_tsum
    (fibreCoefficientFamily_scaled_forcing_bound η Cw hη G hG hv hw ξ)
  rw [ENNReal.tsum_mul_left] at hb
  apply hb.trans_lt
  apply (mul_le_mul' le_rfl (fibreCoefficientFamily_series_forcing_le η Cw hη hCw G hG hv hw ξ hξ)).trans_lt
  finiteness

end AVRegularity.CycleEvolution
end

section
open Homogenization
namespace AVRegularity.CycleEvolution

/-! A real quadratic jet and the actual weighted Taylor majorant imply the required real-part estimate. -/

theorem fibreScalarSeries_real_part_bound (a : ℕ × ℕ → ℝ → ℂ) (R K : ℝ)
    (hR : 0 < R) (hK : 0 ≤ K)
    (hz : ∀ p, p.1 + p.2 ≤ 1 → ∀ t, a p t = 0)
    (hreal : ∀ p, p.1 + p.2 = 2 → ∀ t, (a p t).im = 0)
    (ha : (∑' p, fibreCoefficientWeight (ENNReal.ofReal R) p * ⨆ t, ‖a p t‖ₑ) ≤ ENNReal.ofReal K)
    (x y : Vec 2) (hxy : fibreNorm (fun j => (x j : ℂ) + Complex.I * (y j : ℂ)) ≤ R / 2)
    (hxy1 : fibreNorm (fun j => (x j : ℂ) + Complex.I * (y j : ℂ)) ≤ 1) (t : ℝ) :
    |(fibreSeriesC a (fun j => (x j : ℂ) + Complex.I * (y j : ℂ)) t -
        fibreSeriesC a (fun j => (x j : ℂ)) t).re| ≤
      (3 * K / R ^ 3 + 2 * K * R⁻¹ ^ 2) *
        (Real.sqrt (∑ j, y j ^ 2) * ∑ j, x j ^ 2 + ∑ j, y j ^ 2) := by
  let ξ := fun j => (x j : ℂ) + Complex.I * (y j : ℂ)
  let ζ := fun j => (x j : ℂ)
  let M := fibreNorm ξ
  let δ := Real.sqrt (∑ j, y j ^ 2)
  let B := K * R⁻¹ ^ 2
  let A := 3 * K / R ^ 3
  have hM : 0 ≤ M := fibreNorm_nonneg ξ
  have hδ : 0 ≤ δ := Real.sqrt_nonneg _
  have hδ1 : δ ≤ 1 := (fibreNorm_imaginary_part_le x y).trans hxy1
  have hζ : fibreNorm ζ ≤ M := fibreNorm_real_projection_le x y
  have hξR : fibreNorm ξ ≤ R := hxy.trans (by linarith)
  have hζR : fibreNorm ζ ≤ R := hζ.trans hξR
  have hfinite := ha.trans_lt (ENNReal.ofReal_lt_top : ENNReal.ofReal K < ⊤)
  have hsplitξ := fibreScalarSeries_quadratic_split a hz ξ t
    (fibreScalarSeries_summable_norm a R hfinite ξ hξR t).of_norm
  have hsplitζ := fibreScalarSeries_quadratic_split a hz ζ t
    (fibreScalarSeries_summable_norm a R hfinite ζ hζR t).of_norm
  have htail := fibreScalarSeries_high_increment_bound (fibreScalarHighCoefficients a) R K M
    hR hK hM hxy (fun p hp _ => by simp only [fibreScalarHighCoefficients, hp, ite_true])
    ((fibreScalarHighCoefficients_majorant_le a R).trans ha) ξ ζ le_rfl hζ t
  rw [fibreNorm_complex_real_difference x y] at htail
  have hM2 : M ^ 2 = (∑ j, x j ^ 2) + ∑ j, y j ^ 2 := fibreNorm_complex_parts_sq x y
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hx2 : 0 ≤ ∑ j, x j ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hy2 : 0 ≤ ∑ j, y j ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have htail' : ‖fibreSeriesC (fibreScalarHighCoefficients a) ξ t -
      fibreSeriesC (fibreScalarHighCoefficients a) ζ t‖ ≤
      A * (δ * ∑ j, x j ^ 2 + ∑ j, y j ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hδ1 hy2) hA
    have he : (3 * K * M ^ 2 / R ^ 3) * δ = A * M ^ 2 * δ := by dsimp only [A]; ring
    change _ ≤ (3 * K * M ^ 2 / R ^ 3) * δ at htail
    rw [he, hM2] at htail
    nlinarith
  have hc (p : ℕ × ℕ) (hp : p.1 + p.2 = 2) : |(a p t).re| ≤ B :=
    (Complex.abs_re_le_norm _).trans (by
      simpa only [hp] using fibreScalar_weighted_coefficient_norm_le a R K hR hK ha p t)
  have hquad := complex_real_quadratic_increment (a (2, 0) t) (a (1, 1) t) (a (0, 2) t)
    (hreal _ rfl t) (hreal _ rfl t) (hreal _ rfl t) x y
  have hqb := real_quadratic_abs_bound (a (2, 0) t).re (a (1, 1) t).re (a (0, 2) t).re
    B hB (hc _ rfl) (hc _ rfl) (hc _ rfl) y
  have hq : |(fibreScalarQuadraticValue a ξ t - fibreScalarQuadraticValue a ζ t).re| ≤
      2 * B * ∑ j, y j ^ 2 := by
    change |((a (2, 0) t * ξ 0 ^ 2 + a (1, 1) t * ξ 0 * ξ 1 + a (0, 2) t * ξ 1 ^ 2) -
      (a (2, 0) t * ζ 0 ^ 2 + a (1, 1) t * ζ 0 * ζ 1 + a (0, 2) t * ζ 1 ^ 2)).re| ≤ _
    rw [hquad, abs_neg]
    exact hqb
  rw [hsplitξ, hsplitζ]
  have he : ((fibreScalarQuadraticValue a ξ t + fibreSeriesC (fibreScalarHighCoefficients a) ξ t) -
      (fibreScalarQuadraticValue a ζ t + fibreSeriesC (fibreScalarHighCoefficients a) ζ t)).re =
      (fibreScalarQuadraticValue a ξ t - fibreScalarQuadraticValue a ζ t).re +
      (fibreSeriesC (fibreScalarHighCoefficients a) ξ t - fibreSeriesC (fibreScalarHighCoefficients a) ζ t).re := by
    simp only [Complex.add_re, Complex.sub_re]
    ring
  rw [he]
  have habs := abs_add_le (fibreScalarQuadraticValue a ξ t - fibreScalarQuadraticValue a ζ t).re
    (fibreSeriesC (fibreScalarHighCoefficients a) ξ t - fibreSeriesC (fibreScalarHighCoefficients a) ζ t).re
  have htailre := (Complex.abs_re_le_norm _).trans htail'
  have hconst : 3 * K / R ^ 3 + 2 * K * R⁻¹ ^ 2 = A + 2 * B := by
    dsimp only [A, B]
    ring
  rw [hconst]
  change _ ≤ (A + 2 * B) * (δ * ∑ j, x j ^ 2 + ∑ j, y j ^ 2)
  nlinarith [mul_nonneg hB (mul_nonneg hδ hx2)]

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

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

end AVRegularity.CycleEvolution
end
