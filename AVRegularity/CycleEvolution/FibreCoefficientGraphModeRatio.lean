-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.FibreCoefficientSymbolHomogeneous
import AVRegularity.CycleEvolution.CellInverseJetFactorialBound
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The constructed fibre symbol is uniformly quadratic throughout its convergence disc. -/

theorem fibreCoefficientFamily_symbol_quadratic_bound (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) (t : ℝ) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    ‖fibreSeriesC (fibreCoefficientSymbol η G v r) ξ t‖ ≤
      (6 * Cw + 24) * (fibreNorm ξ / fibreCoefficientMajorantRadius Cw) ^ 2 := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  have hz : ∀ p : ℕ × ℕ, p.1 + p.2 < 2 → ∀ s,
      fibreCoefficientSymbol η G v r p s = 0 := by
    intro p hp s
    exact fibreCoefficientFamily_symbol_low_order η Cw hη G hG hv hw p (by omega) s
  have he := fibreScalarSeries_order_enorm_le (fibreCoefficientSymbol η G v r)
    (fibreCoefficientMajorantRadius Cw) (6 * Cw + 24)
    (fibreCoefficientMajorantRadius_pos hCw) 2 hz
    (fibreCoefficientFamily_weighted_symbol_le η Cw hη0 hη hCw G hG hv hw) ξ hξ t
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (sq_nonneg _)] at he
  change ‖fibreSeriesC (fibreCoefficientSymbol η G v r) ξ t‖ ≤ _
  exact ((ENNReal.ofReal_le_ofReal_iff (by positivity)).mp he).trans_eq (mul_comm _ _)

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Actual reciprocal overlap coefficients for the normalized future-dependent dual row. -/

def fibreAdjointNormalizationCoefficients (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) :
    ℕ × ℕ → ℝ → ℂ :=
  fun p t => fibreScalarInverseCoefficient
    (fun a => fibreAdjointOverlapCoefficients η Cw hη G hG hv hw a t) p

theorem fibreAdjointNormalizationCoefficients_weighted_le_two (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) :
    (∑' p, fibreCoefficientWeight (ENNReal.ofReal (fibreCoefficientMajorantRadius Cw / 16)) p *
      ⨆ t, ‖fibreAdjointNormalizationCoefficients η Cw hη G hG hv hw p t‖ₑ) ≤ 2 := by
  let R := fibreCoefficientMajorantRadius Cw
  let d := fibreAdjointOverlapCoefficients η Cw hη G hG hv hw
  have hR : 0 < R := fibreCoefficientMajorantRadius_pos hCw
  have hρ : 0 < R / 16 := by positivity
  have hρR : R / 16 ≤ R := by linarith
  have hratio : (R / 16) / R = 1 / 16 := by field_simp
  have hD := fibreAdjointOverlapCoefficients_weighted_le η Cw hη hCw G hG hv hw hρ.le hρR
  change (∑' p, fibreCoefficientWeight (ENNReal.ofReal (R / 16)) p * ⨆ t, ‖d p t‖ₑ) ≤
    ENNReal.ofReal ((R / 16) / R) ^ 2 at hD
  rw [hratio] at hD
  have hn : ENNReal.ofReal (1 / 16 : ℝ) ^ 2 ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 16)]
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hsmall : (∑' p, fibreCoefficientWeight (ENNReal.ofReal (R / 16)) p *
      ⨆ t, ‖d p t‖ₑ) ≤ 1 / 2 := hD.trans (hn.trans_eq hhalf)
  have hfinite (p : ℕ × ℕ) : (⨆ t, ‖d p t‖ₑ) < ⊤ := by
    have hi := fibreCoefficient_individual_of_total_le (R / 16) 1 hρ
      (fun p => ⨆ t, ‖d p t‖ₑ) (hsmall.trans (by norm_num)) p
    exact hi.trans_lt ENNReal.ofReal_lt_top
  exact fibreScalarInverseCoefficient_weighted_le_two d _ ENNReal.ofReal_lt_top hfinite hsmall

/-! Actual normalized dual-row Taylor coefficients and their uniform cell L2 majorant. -/

def fibreAdjointRowCoefficients (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) :
    ℕ × ℕ → ℝ → Vec 2 → ℂ :=
  fibreRowCoefficients (fibreAdjointNormalizationCoefficients η Cw hη G hG hv hw)
    (fibreAdjointCorrectionCoefficients η Cw hη G hG hv hw)

theorem fibreAdjointRowCoefficients_weighted_le_four (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) :
    (∑' p, fibreCoefficientWeight (ENNReal.ofReal (fibreCoefficientMajorantRadius Cw / 16)) p *
      ⨆ t, cellL2Norm (fibreAdjointRowCoefficients η Cw hη G hG hv hw p t)) ≤ 4 := by
  let R := fibreCoefficientMajorantRadius Cw
  let k := fibreAdjointNormalizationCoefficients η Cw hη G hG hv hw
  let a := fibreAdjointCorrectionCoefficients η Cw hη G hG hv hw
  have hR : 0 < R := fibreCoefficientMajorantRadius_pos hCw
  have hρ : 0 ≤ R / 16 := by positivity
  have hρR : R / 16 ≤ R := by linarith
  have ha := fibreAdjointCorrectionCoefficients_weighted_le η Cw hη hCw G hG hv hw hρ hρR
  have hratio : (R / 16) / R ≤ 1 := (div_le_one hR).mpr hρR
  have ha' : (∑' p, fibreCoefficientWeight (ENNReal.ofReal (R / 16)) p *
      ⨆ t, cellL2Norm (a p t)) ≤ 1 :=
    ha.trans ((ENNReal.ofReal_le_ofReal hratio).trans_eq (by norm_num))
  have hk : (∑' p, fibreCoefficientWeight (ENNReal.ofReal (R / 16)) p * ⨆ t, ‖k p t‖ₑ) ≤ 2 :=
    fibreAdjointNormalizationCoefficients_weighted_le_two η Cw hη hCw G hG hv hw
  apply (fibreRowCoefficients_weighted_le k a (ENNReal.ofReal (R / 16))).trans
  exact (add_le_add hk (mul_le_mul' hk ha')).trans_eq (by norm_num)

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The actual normalized dual row has the constant Taylor coefficient one. -/

theorem fibreAdjointRowCoefficients_zero (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) :
    ∀ t x, fibreAdjointRowCoefficients η Cw hη G hG hv hw 0 t x = 1 := by
  intro t x
  have ha : fibreAdjointCorrectionCoefficients η Cw hη G hG hv hw (0, 0) = 0 :=
    fibreAdjointCorrectionCoefficients_zero η Cw hη G hG hv hw
  simp [fibreAdjointRowCoefficients, fibreRowCoefficients, fibreCoefficientPairs,
    fibreCoefficientComplement, ha, fibreAdjointNormalizationCoefficients,
    fibreScalarInverseCoefficient_zero]

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Every-time cell L2 membership and uniform size of the literal normalized row series. -/

theorem fibreAdjointRowCoefficients_series_memLp_bound (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16) (t : ℝ) :
    let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
    MemLp (fibreSeriesFun ell ξ t) 2 (volume.restrict AVenhance.unitCube) ∧
      cellL2Norm (fibreSeriesFun ell ξ t) ≤ 4 := by
  let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
  have hb := (fibreL2Series_norm_sum_le ell (fibreCoefficientMajorantRadius Cw / 16) ξ hξ t).trans
    (fibreAdjointRowCoefficients_weighted_le_four η Cw hη hCw G hG hv hw)
  have hs := cellL2Series_memLp_bound (fun p x => fibreMonomial ξ p * ell p t x)
    (hb.trans_lt (by norm_num : (4 : ℝ≥0∞) < ⊤))
  exact ⟨hs.1, hs.2.1.trans hb⟩

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! The actual overlap Taylor series is the literal cell pairing of the reversed and forward graphs. -/

theorem fibreAdjointOverlapCoefficients_series (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) (t : ℝ) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let a := fibreAdjointCorrectionCoefficients η Cw hη G hG hv hw
    fibreSeriesC (fibreAdjointOverlapCoefficients η Cw hη G hG hv hw) ξ t =
      cellMean (fun x => fibreSeriesFun a ξ t x * cellValue (fibreSeriesJet r ξ) t x) := by
  let R := fibreCoefficientMajorantRadius Cw
  let a := fibreAdjointCorrectionCoefficients η Cw hη G hG hv hw
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  have hR : 0 < R := fibreCoefficientMajorantRadius_pos hCw
  have ha : (∑' p, cellL2Norm (fun x => fibreMonomial ξ p * a p t x)) < ⊤ := by
    apply (fibreL2Series_norm_sum_le a R ξ hξ t).trans_lt
    have hm := fibreAdjointCorrectionCoefficients_weighted_le η Cw hη hCw G hG hv hw hR.le le_rfl
    exact hm.trans_lt ENNReal.ofReal_lt_top
  exact fibreMean_monomial_cauchy_product ξ (fun p => a p t) (fun p => cellValue (r p) t) ha
    (fibreCoefficientFamily_value_trace_summable η Cw hη hCw G hG hv hw ξ hξ t)

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleEvolution

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

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! The actual reciprocal overlap Taylor series is convergent and normalizes its denominator. -/

theorem fibreAdjointNormalizationCoefficients_series_mul (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16) (t : ℝ) :
    (1 + fibreSeriesC (fibreAdjointOverlapCoefficients η Cw hη G hG hv hw) ξ t) *
      fibreSeriesC (fibreAdjointNormalizationCoefficients η Cw hη G hG hv hw) ξ t = 1 := by
  let R := fibreCoefficientMajorantRadius Cw
  let d := fibreAdjointOverlapCoefficients η Cw hη G hG hv hw
  let k := fibreAdjointNormalizationCoefficients η Cw hη G hG hv hw
  have hR : 0 < R := fibreCoefficientMajorantRadius_pos hCw
  have hρ : 0 ≤ R / 16 := by positivity
  have hρR : R / 16 ≤ R := by linarith
  have hD := fibreAdjointOverlapCoefficients_weighted_le η Cw hη hCw G hG hv hw hρ hρR
  have hd : (∑' p, fibreCoefficientWeight (ENNReal.ofReal (R / 16)) p * ⨆ s, ‖d p s‖ₑ) < ⊤ :=
    hD.trans_lt (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
  have hk : (∑' p, fibreCoefficientWeight (ENNReal.ofReal (R / 16)) p * ⨆ s, ‖k p s‖ₑ) < ⊤ :=
    (fibreAdjointNormalizationCoefficients_weighted_le_two η Cw hη hCw G hG hv hw).trans_lt
      (by norm_num)
  exact fibreScalarInverseCoefficient_series_mul (fun p => d p t)
    (fibreAdjointOverlapCoefficients_zero η Cw hη G hG hv hw t) ξ
    (fibreScalarSeries_summable_norm d (R / 16) hd ξ hξ t)
    (fibreScalarSeries_summable_norm k (R / 16) hk ξ hξ t)

/-! The actual normalization scalar has uniform norm at most two. -/

theorem fibreAdjointNormalization_series_norm_le_two (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16) (t : ℝ) :
    ‖fibreSeriesC (fibreAdjointNormalizationCoefficients η Cw hη G hG hv hw) ξ t‖ ≤ 2 := by
  let k := fibreAdjointNormalizationCoefficients η Cw hη G hG hv hw
  have he : ‖fibreSeriesC k ξ t‖ₑ ≤ 2 :=
    (enorm_tsum_le_tsum_enorm (f := fun p => fibreMonomial ξ p * k p t)).trans
      ((fibreScalarSeries_enorm_sum_le k (fibreCoefficientMajorantRadius Cw / 16) ξ hξ t).trans
        (fibreAdjointNormalizationCoefficients_weighted_le_two η Cw hη hCw G hG hv hw))
  rw [← ofReal_norm, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num] at he
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp he

/-! First-order and all-frequency homogeneous bounds for the actual normalized dual row. -/

theorem fibreAdjointRowCoefficients_sub_one_le (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16) (t : ℝ) :
    cellL2Norm (fun x => fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ t x - 1) ≤
      ENNReal.ofReal ((4 / (fibreCoefficientMajorantRadius Cw / 16)) * fibreNorm ξ) := by
  have hR := fibreCoefficientMajorantRadius_pos hCw
  have he := fibreL2Series_sub_one_le (fibreAdjointRowCoefficients η Cw hη G hG hv hw)
    (fibreCoefficientMajorantRadius Cw / 16) (by positivity) 4 (by norm_num)
    (fibreAdjointRowCoefficients_zero η Cw hη G hG hv hw)
    (fibreAdjointRowCoefficients_weighted_le_four η Cw hη hCw G hG hv hw) ξ hξ t
  apply he.trans_eq
  rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul
    (div_nonneg (fibreNorm_nonneg ξ) (by positivity))]
  congr 1
  ring

theorem fibreAdjointRowCoefficients_homogeneous_le (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (n : ℕ) (ξ : Fin 2 → ℂ) (t : ℝ) :
    cellL2Norm (fibreHomogeneous (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ n t) ≤
      ENNReal.ofReal (4 * (2 / (fibreCoefficientMajorantRadius Cw / 16)) ^ n * fibreNorm ξ ^ n) := by
  let ρ := fibreCoefficientMajorantRadius Cw / 16
  let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
  have hR := fibreCoefficientMajorantRadius_pos hCw
  have hρ : 0 < ρ := by dsimp only [ρ]; positivity
  have hcoef p s : cellL2Norm (ell p s) ≤ ENNReal.ofReal (4 * (ρ⁻¹) ^ (p.1 + p.2)) := by
    have hi := fibreCoefficient_individual_of_total_le ρ 4 hρ
      (fun p => ⨆ t, cellL2Norm (ell p t))
      (by simpa only [ENNReal.ofReal_ofNat] using
        fibreAdjointRowCoefficients_weighted_le_four η Cw hη hCw G hG hv hw) p
    exact (le_iSup (fun t => cellL2Norm (ell p t)) s).trans hi
  change cellL2Norm (fibreHomogeneous ell ξ n t) ≤ ENNReal.ofReal (4 * (2 / ρ) ^ n * fibreNorm ξ ^ n)
  rw [div_eq_mul_inv]
  exact fibreHomogeneous_cellL2_le_of_geometric ell 4 ρ⁻¹ hcoef n ξ t

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! The literal normalized dual-row Taylor series equals the actual reciprocal times reversed graph. -/

theorem fibreAdjointRowCoefficients_series_ae (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16) (t : ℝ) :
    let k := fibreAdjointNormalizationCoefficients η Cw hη G hG hv hw
    let a := fibreAdjointCorrectionCoefficients η Cw hη G hG hv hw
    ∀ᵐ x ∂(volume.restrict AVenhance.unitCube),
      fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ t x =
        fibreSeriesC k ξ t * (1 + fibreSeriesFun a ξ t x) := by
  let R := fibreCoefficientMajorantRadius Cw
  let k := fibreAdjointNormalizationCoefficients η Cw hη G hG hv hw
  let a := fibreAdjointCorrectionCoefficients η Cw hη G hG hv hw
  have hR : 0 < R := fibreCoefficientMajorantRadius_pos hCw
  have hρ : 0 ≤ R / 16 := by positivity
  have hρR : R / 16 ≤ R := by linarith
  have hkfinite := (fibreAdjointNormalizationCoefficients_weighted_le_two
    η Cw hη hCw G hG hv hw).trans_lt (by norm_num : (2 : ℝ≥0∞) < ⊤)
  have hk := fibreScalarSeries_summable_norm k (R / 16) hkfinite ξ hξ t
  have hafinite := (fibreAdjointCorrectionCoefficients_weighted_le η Cw hη hCw G hG hv hw
    hρ hρR).trans_lt ENNReal.ofReal_lt_top
  have hs := (fibreL2Series_norm_sum_le a (R / 16) ξ hξ t).trans_lt hafinite
  filter_upwards [(cellL2Series_memLp_bound (fun p x => fibreMonomial ξ p * a p t x) hs).2.2]
    with x hx
  exact fibreRowCoefficients_series_pointwise k a ξ t x hk hx

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The actual normalized row class is uniformly close to the constant mean row on a smaller disk. -/

theorem fibreAdjointRow_class_small (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 1024) (t : ℝ) :
    let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
    ‖cellSourceSlice ell t - cellConstantCLM 1‖ ≤ 1 / 16 := by
  let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
  have hR := fibreCoefficientMajorantRadius_pos hCw
  have hξ16 : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16 := by linarith
  have hl := (fibreAdjointRowCoefficients_series_memLp_bound η Cw hη hCw G hG hv hw ξ hξ16 t).1
  have hn := fibreAdjointRowCoefficients_sub_one_le η Cw hη hCw G hG hv hw ξ hξ16 t
  have he : (cellSourceSlice ell t - cellConstantCLM 1 : ComplexCellL2) =ᵐ[
      volume.restrict AVenhance.unitCube] (fun x => ell t x - 1) :=
    (Lp.coeFn_sub _ _).trans ((cellSourceSlice_ae ell t hl).sub (cellConstantCLM_ae 1))
  rw [cellL2Norm_eq_of_class _ _ he] at hn
  have hc : (4 / (fibreCoefficientMajorantRadius Cw / 16)) * fibreNorm ξ ≤ 1 / 16 := by
    have hd : 0 < fibreCoefficientMajorantRadius Cw / 16 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hd]
    nlinarith
  have hb := hn.trans (ENNReal.ofReal_le_ofReal hc)
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 1 / 16)).mp hb

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The required real-part estimate for the actual constructed graph symbol, uniformly in contrast. -/

def fibreCoefficientRealPartBound (Cw : ℝ) : ℝ :=
  3 * (6 * Cw + 24) / fibreCoefficientMajorantRadius Cw ^ 3 +
    2 * (6 * Cw + 24) * (fibreCoefficientMajorantRadius Cw)⁻¹ ^ 2

theorem fibreCoefficientFamily_symbol_real_part_bound (η Cw : ℝ) (hη0 : 0 ≤ η)
    (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (x y : Vec 2)
    (hxy : fibreNorm (fun j => (x j : ℂ) + Complex.I * (y j : ℂ)) ≤
      fibreCoefficientMajorantRadius Cw / 2) (t : ℝ) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G v r
    |(fibreSeriesC lam (fun j => (x j : ℂ) + Complex.I * (y j : ℂ)) t -
        fibreSeriesC lam (fun j => (x j : ℂ)) t).re| ≤
      fibreCoefficientRealPartBound Cw *
        (Real.sqrt (∑ j, y j ^ 2) * ∑ j, x j ^ 2 + ∑ j, y j ^ 2) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let lam := fibreCoefficientSymbol η G v r
  have hR := fibreCoefficientMajorantRadius_pos hCw
  have hK : 0 ≤ 6 * Cw + 24 := by positivity
  have hz (p : ℕ × ℕ) (hp : p.1 + p.2 ≤ 1) (s : ℝ) : lam p s = 0 :=
    fibreCoefficientFamily_symbol_low_order η Cw hη G hG hv hw p hp s
  have hreal (p : ℕ × ℕ) (hp : p.1 + p.2 = 2) (s : ℝ) : (lam p s).im = 0 := by
    have hr := fibreCoefficientFamily_symbol_reality η Cw hη G hG hv hw p s
    have hs : fibreRealitySign p = 1 := by rw [fibreRealitySign, hp]; norm_num
    rw [hs, one_mul] at hr
    have hi := congrArg Complex.im hr
    simp only [Complex.star_def, Complex.conj_im] at hi
    change -(lam p s).im = (lam p s).im at hi
    linarith
  have hxy1 : fibreNorm (fun j => (x j : ℂ) + Complex.I * (y j : ℂ)) ≤ 1 :=
    hxy.trans (by have hr := fibreCoefficientMajorantRadius_le_one hCw; linarith)
  exact fibreScalarSeries_real_part_bound lam (fibreCoefficientMajorantRadius Cw) (6 * Cw + 24)
    hR hK hz hreal (fibreCoefficientFamily_weighted_symbol_le η Cw hη0 hη hCw G hG hv hw)
    x y hxy hxy1 t

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! The actual literal coefficient series solves its actual summed cell equation. -/

/-- The constructed graph candidate is an actual bounded mean-zero inverse for its literal summed forcing. -/
theorem fibreCoefficientFamily_series_isInverse (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    IsCellInverseValue ⟨fun t _ => G t, v, 0, 0⟩
      (fun t x => ∑' p, fibreCoefficientScaledSource η v r ξ p t x)
      (fun t x => ∑' p, fibreCoefficientScaledFlux η G r ξ p t x) (fibreSeriesJet r ξ) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let D := fun p => fibreMonomial ξ p • r p
  have hsD : (∑' p, cellEnergyNorm Set.univ (D p)) < ⊤ :=
    (fibreCoefficientFamily_series_energy_le η Cw hη hCw G hG hv hw ξ hξ).trans_lt (by simp)
  have hsF := fibreCoefficientFamily_scaled_forcing_summable η Cw hη hCw G hG hv hw ξ hξ
  have hss : (∑' p, cellUlNorm Set.univ (fibreCoefficientScaledSource η v r ξ p)) < ⊤ :=
    (ENNReal.tsum_le_tsum (fun p => le_add_right le_rfl)).trans_lt hsF
  have hFs : (∑' p, cellUlNorm Set.univ (fibreCoefficientScaledFlux η G r ξ p)) < ⊤ :=
    (ENNReal.tsum_le_tsum (fun p => le_add_left le_rfl)).trans_lt hsF
  have hb := cellInverseSeries_isInverse (fun t _ => G t) hG v hv
    (fibreCoefficientScaledSource η v r ξ) (fibreCoefficientScaledFlux η G r ξ) D
    (fibreCoefficientFamily_scaled_isInverse η Cw hη G hG hv hw ξ) hsD
    (fibreCoefficientFamily_scaled_source_aestronglyMeasurable η Cw hη G hG hv hw ξ)
    (fibreCoefficientFamily_scaled_flux_aestronglyMeasurable η Cw hη G hG hv hw ξ) hss hFs
  have he : fibreSeriesJet r ξ = (fun t a x => ∑' p, D p t a x) := by rfl
  change IsCellInverseValue _ _ _ (fibreSeriesJet r ξ)
  rw [he]
  exact hb

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! The actual weighted coordinate means recover the arbitrary-frequency graph pairing. -/

local instance cycleEvolutionFibreCoefficientMeanCoordinateSeriesProbCube : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
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

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped BigOperators
namespace AVRegularity.CycleEvolution

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

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
open scoped BigOperators
namespace AVRegularity.CycleEvolution

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

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! Every-time identification of the actual nonlinear scalar Taylor series. -/

local instance cycleEvolutionFibreCoefficientUnprojectedGraphSeriesProbCube : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
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

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

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

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! The constructed graph has a normalized mean and a linear Hilbert correction bound at every trace time. -/

local instance fibreCoefficientGraphClassNormalizationProbCube : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using cellCube_volume_one⟩

theorem cellMeanCLM_one : cellMeanCLM (cellConstantCLM 1) = 1 := by
  rw [cellMeanCLM_apply]
  unfold cellMean
  rw [integral_congr_ae (cellConstantCLM_ae 1), integral_const]
  simp

theorem fibreCoefficientFamily_graph_class_mean (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) (t : ℝ) :
    let D := fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hw) ξ
    cellMean ((cellRawTrace D t + cellConstantCLM 1 : ComplexCellL2)) = 1 := by
  let D := fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hw) ξ
  have hi := fibreCoefficientFamily_graph_isInverse η Cw hη hCw G hG hv hw ξ hξ
  have hp := cellRawTrace_ae D t (hi.1.2.2.1 t (mem_univ t)).1
  have hm : cellMean (cellRawTrace D t) = 0 := by
    calc
      _ = cellMean (cellValue D t) := integral_congr_ae hp
      _ = 0 := hi.2.1 t
  change cellMean ((cellRawTrace D t + cellConstantCLM 1 : ComplexCellL2)) = 1
  rw [← cellMeanCLM_apply (cellRawTrace D t + cellConstantCLM 1), map_add,
    cellMeanCLM_apply, hm, cellMeanCLM_one, zero_add]

theorem fibreCoefficientFamily_graph_class_correction_bound (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) (t : ℝ) :
    let D := fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hw) ξ
    ‖cellRawTrace D t‖ ≤ (2 / fibreCoefficientMajorantRadius Cw) * fibreNorm ξ := by
  let D := fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hw) ξ
  have hi := fibreCoefficientFamily_graph_isInverse η Cw hη hCw G hG hv hw ξ hξ
  have hp := cellRawTrace_ae D t (hi.1.2.2.1 t (mem_univ t)).1
  have hn := (cellValue_cellL2Norm_le_energy D t).trans
    (fibreCoefficientFamily_summed_energy_le η Cw hη hCw G hG hv hw ξ hξ)
  rw [cellL2Norm_eq_of_class _ _ hp] at hn
  have hn' : ENNReal.ofReal ‖cellRawTrace D t‖ ≤
      ENNReal.ofReal (2 * (fibreNorm ξ / fibreCoefficientMajorantRadius Cw)) :=
    hn.trans_eq (by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]; norm_num)
  have hfn := fibreNorm_nonneg ξ
  have hR := fibreCoefficientMajorantRadius_pos hCw
  have hr := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hn'
  change ‖cellRawTrace D t‖ ≤ _
  convert hr using 1
  ring

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev MeasureTheory
namespace AVRegularity.CycleEvolution

/-! The actual normalized dual row pairs integrably with the forward graph and gives exactly one. -/

theorem fibreAdjointRowCoefficients_normalization (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16) (t : ℝ) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
    Integrable (fun x => fibreSeriesFun ell ξ t x * (1 + cellValue (fibreSeriesJet r ξ) t x))
      (volume.restrict AVenhance.unitCube) ∧
      cellMean (fun x => fibreSeriesFun ell ξ t x * (1 + cellValue (fibreSeriesJet r ξ) t x)) = 1 := by
  let R := fibreCoefficientMajorantRadius Cw
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let a := fibreAdjointCorrectionCoefficients η Cw hη G hG hv hw
  let k := fibreAdjointNormalizationCoefficients η Cw hη G hG hv hw
  let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
  have hR : 0 < R := fibreCoefficientMajorantRadius_pos hCw
  have hξR : fibreNorm ξ ≤ R := hξ.trans (by linarith)
  have hi := fibreCoefficientFamily_series_isInverse η Cw hη hCw G hG hv hw ξ hξR
  have hr := (hi.1.2.2.1 t (Set.mem_univ t)).1
  have ha := fibreAdjointCorrectionCoefficients_series_properties η Cw hη hCw G hG hv hw ξ hξR t
  have hell := fibreAdjointRowCoefficients_series_memLp_bound η Cw hη hCw G hG hv hw ξ hξ t
  have hconst : MemLp (fun _ : Vec 2 => (1 : ℂ)) 2 (volume.restrict AVenhance.unitCube) := by
    change cellL2Norm (fun _ : Vec 2 => (1 : ℂ)) < ⊤
    rw [cellL2Norm_const]
    simp
  refine ⟨memLp_one_iff_integrable.mp (hell.1.mul (hconst.add hr)), ?_⟩
  have he := fibreAdjointRowCoefficients_series_ae η Cw hη hCw G hG hv hw ξ hξ t
  have hmean := cellMean_one_add_mul_one_add (fibreSeriesFun a ξ t)
    (cellValue (fibreSeriesJet r ξ) t) ha.1 hr ha.2.1 (hi.2.1 t)
  have hop := fibreAdjointOverlapCoefficients_series η Cw hη hCw G hG hv hw ξ hξR t
  calc
    _ = cellMean (fun x => fibreSeriesC k ξ t *
        ((1 + fibreSeriesFun a ξ t x) * (1 + cellValue (fibreSeriesJet r ξ) t x))) := by
      apply integral_congr_ae
      filter_upwards [he] with x hx
      rw [hx, mul_assoc]
    _ = fibreSeriesC k ξ t * cellMean (fun x =>
        (1 + fibreSeriesFun a ξ t x) * (1 + cellValue (fibreSeriesJet r ξ) t x)) :=
      integral_const_mul _ _
    _ = fibreSeriesC k ξ t * (1 +
        fibreSeriesC (fibreAdjointOverlapCoefficients η Cw hη G hG hv hw) ξ t) :=
      congrArg (fun z => fibreSeriesC k ξ t * z)
        (hmean.trans (congrArg (fun z => 1 + z) hop.symm))
    _ = 1 := by
      rw [mul_comm]
      exact fibreAdjointNormalizationCoefficients_series_mul η Cw hη hCw G hG hv hw ξ hξ t

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! The finite-interval graph gradient budget in its actual H¹ Hilbert slices. -/

theorem fibreCoefficientFamily_finite_hilbert_gradient (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw)
    {a b : ℝ} (hab : a ≤ b) :
    let D := fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hw) ξ
    (∫ t in a..b, ∑ j, ‖cellDerivativeCLM j (cellH1Slice D t)‖ ^ 2) ≤
      4 * (b - a + 1) * (fibreNorm ξ / fibreCoefficientMajorantRadius Cw) ^ 2 := by
  let D := fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hw) ξ
  have hR := fibreCoefficientMajorantRadius_pos hCw
  have hfn := fibreNorm_nonneg ξ
  have hδ : 0 ≤ b - a + 1 := by linarith
  have hinv := fibreCoefficientFamily_graph_isInverse η Cw hη hCw G hG hv hw ξ hξ
  have hsol := cellSolution_restrict (Set.subset_univ (Icc a b)) Set.ordConnected_Icc hinv.1
  have hid := cellSolution_gradient_lintegral_of_state hab hsol (cellH1Slice D)
    (cellSolution_slice_memLp hab hsol) (cellSolution_slice_ae hsol)
  have hbound := fibreCoefficientFamily_finite_gradient_energy η Cw hη hCw G hG hv hw ξ hξ hab
  dsimp only at hbound
  rw [hid] at hbound
  have hnum : (2 : ENNReal) * ENNReal.ofReal (fibreNorm ξ / fibreCoefficientMajorantRadius Cw) =
      ENNReal.ofReal (2 * (fibreNorm ξ / fibreCoefficientMajorantRadius Cw)) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hrhs : ENNReal.ofReal (b - a + 1) *
      (2 * ENNReal.ofReal (fibreNorm ξ / fibreCoefficientMajorantRadius Cw)) ^ 2 =
        ENNReal.ofReal (4 * (b - a + 1) * (fibreNorm ξ / fibreCoefficientMajorantRadius Cw) ^ 2) := by
    rw [hnum, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul hδ]
    congr 1
    ring
  have hn := hbound.trans_eq hrhs
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hn

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Uniform upper and lower norms of the genuine constructed normalized graph mode. -/

theorem fibreCoefficientFamily_graph_mode_norm_bounds (η Cw : ℝ)
    (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) (t : ℝ) :
    let D := fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hw) ξ
    1 ≤ ‖cellRawTrace D t + cellConstantCLM 1‖ ∧
      ‖cellRawTrace D t + cellConstantCLM 1‖ ≤ 3 := by
  have hi := fibreCoefficientFamily_graph_isInverse η Cw hη hCw G hG hv hw ξ hξ
  have he := fibreCoefficientFamily_summed_energy_le η Cw hη hCw G hG hv hw ξ hξ
  have hR := fibreCoefficientMajorantRadius_pos hCw
  have hdiv : fibreNorm ξ / fibreCoefficientMajorantRadius Cw ≤ 1 :=
    (div_le_one hR).mpr hξ
  have hen := he.trans (mul_le_mul' le_rfl
    (show ENNReal.ofReal (fibreNorm ξ / fibreCoefficientMajorantRadius Cw) ≤ 1 by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hdiv))
  have htwo : (cellEnergyNorm univ
      (fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hw) ξ)).toReal ≤ 2 := by
    have h := ENNReal.toReal_mono (by simp : (2 * 1 : ENNReal) ≠ ⊤) hen
    norm_num at h
    exact h
  refine ⟨cellInverse_normalized_mode_lower hi t, ?_⟩
  exact (cellInverse_normalized_mode_upper hi t).trans (by linarith)

/-! Uniform exact ratio of actual normalized graph modes at arbitrary times. -/

theorem fibreCoefficientFamily_graph_mode_ratio (η Cw : ℝ)
    (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) (s t : ℝ) :
    let D := fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hw) ξ
    cellL2Norm (fun x => 1 + cellValue D s x) ≤
      ENNReal.ofReal 3 * cellL2Norm (fun x => 1 + cellValue D t x) := by
  let D := fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hw) ξ
  have hi := fibreCoefficientFamily_graph_isInverse η Cw hη hCw G hG hv hw ξ hξ
  have hs := fibreCoefficientFamily_graph_mode_norm_bounds η Cw hη hCw G hG hv hw ξ hξ s
  have ht := fibreCoefficientFamily_graph_mode_norm_bounds η Cw hη hCw G hG hv hw ξ hξ t
  have hn : ‖cellRawTrace D s + cellConstantCLM 1‖ ≤
      3 * ‖cellRawTrace D t + cellConstantCLM 1‖ := by
    linarith [hs.2, ht.1]
  change cellL2Norm (fun x => 1 + cellValue D s x) ≤
    ENNReal.ofReal 3 * cellL2Norm (fun x => 1 + cellValue D t x)
  rw [cellL2Norm_normalized_raw_trace D s (hi.1.2.2.1 s (mem_univ s)).1,
    cellL2Norm_normalized_raw_trace D t (hi.1.2.2.1 t (mem_univ t)).1,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
  exact ENNReal.ofReal_le_ofReal hn

end AVRegularity.CycleEvolution
end
