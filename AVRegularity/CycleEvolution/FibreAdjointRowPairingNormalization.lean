-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.FibreCoefficientGraphRawDual
public import AVRegularity.CycleEvolution.FibreCoefficientGraphModeRatio
import AVRegularity.CycleEvolution.CellInverseJetFactorialBound
import AVRegularity.CycleEvolution.CellEnergySpaceRawDirectionalLimit
import AVRegularity.CycleEvolution.CellLimitMoments
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
namespace AVRegularity.CycleEvolution

/-! One universal graph bound and a smaller disc discharge all quantitative smallness conditions. -/

def fibreEvolutionBound (Cw : ℝ) : ℝ :=
  100 + fibreCoefficientGraphBound Cw + fibreCoefficientRealPartBound Cw +
    312 / fibreCoefficientMajorantRadius Cw +
    (4 + Cw * (312 / fibreCoefficientMajorantRadius Cw)) +
    64 / fibreCoefficientMajorantRadius Cw

def fibreEvolutionRadius (Cw : ℝ) : ℝ :=
  min (fibreCoefficientMajorantRadius Cw / 1024)
    (min (1 / (fibreEvolutionBound Cw + 1)) (1 / (26 * (4 * Cw + 8))))

theorem fibreEvolutionBound_bounds {Cw : ℝ} (hw : 0 ≤ Cw) :
    100 ≤ fibreEvolutionBound Cw ∧
    fibreCoefficientGraphBound Cw ≤ fibreEvolutionBound Cw ∧
    fibreCoefficientRealPartBound Cw ≤ fibreEvolutionBound Cw ∧
    312 / fibreCoefficientMajorantRadius Cw ≤ fibreEvolutionBound Cw ∧
    4 + Cw * (312 / fibreCoefficientMajorantRadius Cw) ≤ fibreEvolutionBound Cw ∧
    64 / fibreCoefficientMajorantRadius Cw ≤ fibreEvolutionBound Cw := by
  have hr := fibreCoefficientMajorantRadius_pos hw
  have hg : 0 ≤ fibreCoefficientGraphBound Cw := by
    unfold fibreCoefficientGraphBound
    positivity
  have hp : 0 ≤ fibreCoefficientRealPartBound Cw := by
    unfold fibreCoefficientRealPartBound
    positivity
  have he : 0 ≤ 312 / fibreCoefficientMajorantRadius Cw := by positivity
  have hs : 0 ≤ 4 + Cw * (312 / fibreCoefficientMajorantRadius Cw) := by positivity
  have hl : 0 ≤ 64 / fibreCoefficientMajorantRadius Cw := by positivity
  unfold fibreEvolutionBound
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem fibreEvolutionRadius_pos {Cw : ℝ} (hw : 0 ≤ Cw) : 0 < fibreEvolutionRadius Cw := by
  have hr := fibreCoefficientMajorantRadius_pos hw
  have hc := (fibreEvolutionBound_bounds hw).1
  unfold fibreEvolutionRadius
  apply lt_min
  · positivity
  apply lt_min <;> positivity

theorem fibreEvolutionRadius_le_majorant {Cw : ℝ} :
    fibreEvolutionRadius Cw ≤ fibreCoefficientMajorantRadius Cw / 1024 := min_le_left _ _

theorem fibreEvolution_frequency_small {Cw : ℝ} (hw : 0 ≤ Cw) {q : ℝ}
    (hq : q ≤ fibreEvolutionRadius Cw) :
    fibreEvolutionBound Cw * q ≤ 1 ∧ 13 * (4 * Cw + 8) * q ≤ 1 / 2 := by
  have hc := (fibreEvolutionBound_bounds hw).1
  have hqC : q ≤ 1 / (fibreEvolutionBound Cw + 1) :=
    hq.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hqW : q ≤ 1 / (26 * (4 * Cw + 8)) :=
    hq.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hCp : 0 < fibreEvolutionBound Cw + 1 := by linarith
  have hWp : 0 < 26 * (4 * Cw + 8) := by positivity
  have hCq := (le_div_iff₀ hCp).mp hqC
  have hWq := (le_div_iff₀ hWp).mp hqW
  constructor
  · by_cases hq0 : 0 ≤ q
    · nlinarith
    · exact (mul_nonpos_of_nonneg_of_nonpos (by linarith) (le_of_not_ge hq0)).trans (by norm_num)
  · nlinarith

/-! Fixed complex frequency radii supply every smallness condition for the normalized word operators. -/

def fibreWordSymbolBound (Cw : ℝ) : ℝ :=
  (6 * Cw + 24) / fibreCoefficientMajorantRadius Cw ^ 2

def fibreWordCorrectionBound (Cw : ℝ) : ℝ := 2 / fibreCoefficientMajorantRadius Cw

def fibreWordRadius (Cw : ℝ) : ℝ := min (fibreEvolutionRadius Cw)
  (1 / (2 * (Cw + 1033 + fibreWordSymbolBound Cw + fibreWordCorrectionBound Cw * Cw)))

theorem fibreWordBounds_nonneg {Cw : ℝ} (hCw : 0 ≤ Cw) :
    0 ≤ fibreWordSymbolBound Cw ∧ 0 ≤ fibreWordCorrectionBound Cw := by
  have hR := fibreCoefficientMajorantRadius_pos hCw
  constructor
  · unfold fibreWordSymbolBound
    positivity
  · unfold fibreWordCorrectionBound
    positivity

theorem fibreWordRadius_pos {Cw : ℝ} (hCw : 0 ≤ Cw) : 0 < fibreWordRadius Cw := by
  obtain ⟨hL, hCr⟩ := fibreWordBounds_nonneg hCw
  have hr := fibreEvolutionRadius_pos hCw
  unfold fibreWordRadius
  exact lt_min hr (by positivity)

theorem fibreWordRadius_le_graph (Cw : ℝ) : fibreWordRadius Cw ≤ fibreEvolutionRadius Cw :=
  min_le_left _ _

theorem fibreWord_frequency_small {Cw : ℝ} (hCw : 0 ≤ Cw) (ξ : Fin 2 → ℂ)
    (hξ : fibreNorm ξ ≤ fibreWordRadius Cw) :
    fibreNorm ξ ≤ 1 ∧ fibreWordCorrectionBound Cw * fibreNorm ξ ≤ 1 ∧
      Cw * fibreNorm ξ + (1032 + fibreWordSymbolBound Cw +
        fibreWordCorrectionBound Cw * Cw) * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2 := by
  have hfn := fibreNorm_nonneg ξ
  have hR := fibreCoefficientMajorantRadius_pos hCw
  have hR1 := fibreCoefficientMajorantRadius_le_one hCw
  obtain ⟨hL, hCr⟩ := fibreWordBounds_nonneg hCw
  have hr := (hξ.trans (fibreWordRadius_le_graph Cw)).trans
    (fibreEvolutionRadius_le_majorant (Cw := Cw))
  have hq : fibreNorm ξ ≤ 1 := by linarith
  have hc : fibreWordCorrectionBound Cw * fibreNorm ξ ≤ 1 := by
    unfold fibreWordCorrectionBound
    rw [div_mul_eq_mul_div, div_le_iff₀ hR]
    linarith
  have hd : 0 < 2 * (Cw + 1033 + fibreWordSymbolBound Cw + fibreWordCorrectionBound Cw * Cw) := by
    positivity
  have hr' := hξ.trans (min_le_right (fibreEvolutionRadius Cw)
    (1 / (2 * (Cw + 1033 + fibreWordSymbolBound Cw + fibreWordCorrectionBound Cw * Cw))))
  have hs := (le_div_iff₀ hd).mp hr'
  have hqq : fibreNorm ξ ^ 2 ≤ fibreNorm ξ := by nlinarith
  have ha : 0 ≤ 1032 + fibreWordSymbolBound Cw + fibreWordCorrectionBound Cw * Cw := by positivity
  have hm := mul_le_mul_of_nonneg_left hqq ha
  have hp : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.two_le_pi]
  exact ⟨hq, hc, by nlinarith⟩

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The constructed coefficient graph is an actual normalized weak Bloch evolution. -/

theorem fibreCoefficientFamily_graph_weak_evolution (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw)
    {a b : ℝ} (hab : a ≤ b) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let D := fibreSeriesJet r ξ
    CellWeakHilbertCurve a b (fun t => cellRawTrace D t + cellConstantCLM 1)
      (fun t => cellH1Slice D t + cellH1One)
      (fun t => cellDualDerivative
        ⟨fun t _ => G t, v, fun j => (Real.sqrt η : ℂ) * ξ j,
          fun s => -fibreSeriesC (fibreCoefficientSymbol η G v r) ξ s⟩ hG V hv.1 hb t
        (cellH1Slice D t + cellH1One) 0 0) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let D := fibreSeriesJet r ξ
  have hi := fibreCoefficientFamily_graph_isInverse η Cw hη hCw G hG hv hw ξ hξ
  have hGm : Measurable G := hG.1.comp
    (measurable_id.prodMk (measurable_const (a := (0 : Vec 2))))
  have he (t : ℝ) (i j : Fin 2) : |G t i j| ≤ 2 :=
    cellMetric_entry_bound hG t 0 i j
  have hs := fibreGraphSource_interval_memLp η Cw hv hw ξ hi a b
  have hF := fibreGraphFlux_interval_memLp η hη G hGm he ξ hi a b
  have hr := cellSolution_restrict (Set.subset_univ (Icc a b)) ordConnected_Icc hi.1
  have hh := cellSolution_to_Hilbert hab ⟨fun t _ => G t, v, 0, 0⟩ hG V 0 hv.1 hb
    measurable_const (fun _ => by simp) _ _ hs hF D hr
  apply hh.add_one.dual_congr
  exact fibreCoefficientFamily_graph_raw_dual_ae η Cw hη0 hη hCw G hG
    hv hm hw V hb ξ hξ a b

end AVRegularity.CycleEvolution
end

section
namespace AVRegularity.CycleEvolution

/-! Explicit constants for the two polynomial word-operator estimates. -/

def fibreWordHomogeneousAmplitude (Cw : ℝ) : ℝ := 5 + 24 * Cw / Real.pi ^ 2

def fibreWordForcedAmplitude (Cw : ℝ) : ℝ :=
  Real.sqrt 14 + 2 * (Cw * Real.sqrt (28 / Real.pi ^ 2) + 2)

def fibreWordGradientFactor (Cw : ℝ) : ℝ :=
  Real.sqrt (32 / fibreCoefficientMajorantRadius Cw ^ 2 + 4)

def fibreWordHomogeneousNormConstant (Cw : ℝ) : ℝ :=
  fibreWordHomogeneousAmplitude Cw + 12 + fibreWordHomogeneousAmplitude Cw * fibreWordGradientFactor Cw

def fibreWordForcedNormConstant (Cw : ℝ) : ℝ :=
  15 + fibreWordForcedAmplitude Cw + fibreWordForcedAmplitude Cw * fibreWordGradientFactor Cw

theorem fibreWord_amplitudes_pos {Cw : ℝ} (hCw : 0 ≤ Cw) :
    0 < fibreWordHomogeneousAmplitude Cw ∧ 0 < fibreWordForcedAmplitude Cw := by
  unfold fibreWordHomogeneousAmplitude fibreWordForcedAmplitude
  constructor <;> positivity

theorem fibreWord_norm_constants_pos {Cw : ℝ} (hCw : 0 ≤ Cw) :
    0 < fibreWordHomogeneousNormConstant Cw ∧ 0 < fibreWordForcedNormConstant Cw := by
  obtain ⟨hh, hf⟩ := fibreWord_amplitudes_pos hCw
  have hg : 0 ≤ fibreWordGradientFactor Cw := Real.sqrt_nonneg _
  unfold fibreWordHomogeneousNormConstant fibreWordForcedNormConstant
  constructor <;> positivity

theorem fibreWord_forced_amplitude_le {Cw q S δ : ℝ} (hCw : 0 ≤ Cw) (hq : 0 ≤ q) (hδ : δ ≤ S) :
    Real.sqrt 14 + 2 * (Cw * Real.sqrt (28 / Real.pi ^ 2) + 2) * q * Real.sqrt δ ≤
      fibreWordForcedAmplitude Cw * (1 + Real.sqrt S * q) := by
  have hb : 0 ≤ 2 * (Cw * Real.sqrt (28 / Real.pi ^ 2) + 2) := by positivity
  have hroot := Real.sqrt_le_sqrt hδ
  have hx : 0 ≤ Real.sqrt S * q := mul_nonneg (Real.sqrt_nonneg _) hq
  have hh := mul_le_mul_of_nonneg_left hroot (mul_nonneg hb hq)
  have hz := mul_nonneg (Real.sqrt_nonneg (14 : ℝ)) hx
  unfold fibreWordForcedAmplitude
  nlinarith

end AVRegularity.CycleEvolution
end

section
open Metric
namespace AVRegularity.CycleEvolution

/-! Quantitative frequency balls for Cauchy estimates at the parabolic scale. -/

theorem fibreNorm_add_le (ξ ζ : Fin 2 → ℂ) : fibreNorm (ξ + ζ) ≤ fibreNorm ξ + fibreNorm ζ := by
  simp only [fibreNorm_eq_piLp_norm]
  exact norm_add_le (WithLp.toLp 2 ξ) (WithLp.toLp 2 ζ)

theorem fibreNorm_le_two_piNorm (ξ : Fin 2 → ℂ) : fibreNorm ξ ≤ 2 * ‖ξ‖ := by
  have h0 : ‖ξ 0‖ ≤ ‖ξ‖ := norm_le_pi_norm ξ 0
  have h1 : ‖ξ 1‖ ≤ ‖ξ‖ := norm_le_pi_norm ξ 1
  have hs : fibreNorm ξ ^ 2 = ‖ξ 0‖ ^ 2 + ‖ξ 1‖ ^ 2 := by
    unfold fibreNorm
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg ‖ξ i‖)), Fin.sum_univ_two]
  nlinarith [sq_le_sq₀ (norm_nonneg (ξ 0)) (norm_nonneg ξ) |>.2 h0,
    sq_le_sq₀ (norm_nonneg (ξ 1)) (norm_nonneg ξ) |>.2 h1,
    fibreNorm_nonneg ξ, norm_nonneg ξ]

def fibreWordCauchyRadius (Cw S : ℝ) : ℝ := fibreWordRadius Cw / (16 * Real.sqrt S)

theorem fibreWordCauchyRadius_pos {Cw S : ℝ} (hCw : 0 ≤ Cw) (hS : 1 ≤ S) :
    0 < fibreWordCauchyRadius Cw S := by
  have hw := fibreWordRadius_pos hCw
  have hs : 0 < Real.sqrt S := Real.sqrt_pos.2 (by linarith)
  exact div_pos hw (mul_pos (by norm_num) hs)

theorem fibreWordFrequencyBall_subset {Cw S : ℝ} (hCw : 0 ≤ Cw) (hS : 1 ≤ S)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ < fibreWordRadius Cw / 4)
    {ζ : Fin 2 → ℂ} (hζ : ζ ∈ ball ξ (fibreWordCauchyRadius Cw S)) :
    fibreNorm ζ < fibreWordRadius Cw := by
  have hw := fibreWordRadius_pos hCw
  have hs : 1 ≤ Real.sqrt S := (Real.le_sqrt (by norm_num) (by linarith)).2 (by simpa using hS)
  have hdist : ‖ζ - ξ‖ < fibreWordRadius Cw / (16 * Real.sqrt S) := by
    simpa only [mem_ball, dist_eq_norm, fibreWordCauchyRadius] using hζ
  have hb : fibreWordRadius Cw / (16 * Real.sqrt S) ≤ fibreWordRadius Cw / 16 :=
    div_le_div_of_nonneg_left hw.le (by norm_num) (by linarith)
  have ht := fibreNorm_add_le (ζ - ξ) ξ
  have hn := fibreNorm_le_two_piNorm (ζ - ξ)
  rw [sub_add_cancel] at ht
  linarith

/-! Uniform polynomial and covariant-shift budgets on the parabolic Cauchy ball. -/

theorem fibreWordRadius_le_one {Cw : ℝ} (hCw : 0 ≤ Cw) : fibreWordRadius Cw ≤ 1 := by
  have h := (fibreWordRadius_le_graph Cw).trans (fibreEvolutionRadius_le_majorant (Cw := Cw))
  linarith [fibreCoefficientMajorantRadius_le_one hCw]

theorem fibreWordFrequencyBall_scaled_difference_le {Cw S : ℝ}
    (hS : 1 ≤ S) (ξ : Fin 2 → ℂ)
    {ζ : Fin 2 → ℂ} (hζ : ζ ∈ ball ξ (fibreWordCauchyRadius Cw S)) :
    Real.sqrt S * fibreNorm (ζ - ξ) ≤ fibreWordRadius Cw / 8 := by
  have hs : 0 < Real.sqrt S := Real.sqrt_pos.2 (by linarith)
  have hd : ‖ζ - ξ‖ < fibreWordRadius Cw / (16 * Real.sqrt S) := by
    simpa only [mem_ball, dist_eq_norm, fibreWordCauchyRadius] using hζ
  have hn := mul_le_mul_of_nonneg_left (fibreNorm_le_two_piNorm (ζ - ξ)) hs.le
  have hm := mul_le_mul_of_nonneg_left hd.le hs.le
  have he : Real.sqrt S * (fibreWordRadius Cw / (16 * Real.sqrt S)) =
      fibreWordRadius Cw / 16 := by field_simp
  rw [he] at hm
  linarith

theorem fibreWordFrequencyBall_polynomial_le {Cw S : ℝ}
    (hCw : 0 ≤ Cw) (hS : 1 ≤ S) (ξ : Fin 2 → ℂ)
    {ζ : Fin 2 → ℂ} (hζ : ζ ∈ ball ξ (fibreWordCauchyRadius Cw S)) :
    1 + Real.sqrt S * fibreNorm ζ ≤ 3 * (1 + Real.sqrt S * fibreNorm ξ) := by
  have hd := fibreWordFrequencyBall_scaled_difference_le hS ξ hζ
  have ht := mul_le_mul_of_nonneg_left (fibreNorm_add_le (ζ - ξ) ξ) (Real.sqrt_nonneg S)
  rw [sub_add_cancel] at ht
  have hw := fibreWordRadius_le_one hCw
  have hn := mul_nonneg (Real.sqrt_nonneg S) (fibreNorm_nonneg ξ)
  linarith

theorem fibreWordFrequencyBall_shift_factor_le {Cw S η a b : ℝ}
    (hCw : 0 ≤ Cw) (hS : 1 ≤ S) (hη : η ≤ 1) (hb : b - a ≤ S)
    (ξ : Fin 2 → ℂ) {ζ : Fin 2 → ℂ}
    (hζ : ζ ∈ ball ξ (fibreWordCauchyRadius Cw S)) (j : Fin 2) :
    ‖(Real.sqrt η : ℂ) * ξ j - (Real.sqrt η : ℂ) * ζ j‖ * Real.sqrt (b - a) ≤ 1 := by
  have hn : ‖(Real.sqrt η : ℂ) * ξ j - (Real.sqrt η : ℂ) * ζ j‖ ≤ fibreNorm (ζ - ξ) := by
    rw [← mul_sub]
    have he : ξ j - ζ j = -(ζ - ξ) j := by simp only [Pi.sub_apply]; ring
    rw [he, mul_neg, norm_neg]
    exact fibreScaledFrequency_coordinate_le η hη (ζ - ξ) j
  have hm := mul_le_mul hn (Real.sqrt_le_sqrt hb) (Real.sqrt_nonneg (b - a))
    (fibreNorm_nonneg (ζ - ξ))
  have hd := fibreWordFrequencyBall_scaled_difference_le hS ξ hζ
  have hw := fibreWordRadius_le_one hCw
  rw [mul_comm (fibreNorm (ζ - ξ))] at hm
  linarith

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The constructed scalar gauge has the quadratic bound used at the fixed word-operator radius. -/

theorem fibreCoefficientFamily_word_symbol_bound (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) (t : ℝ) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    ‖fibreSeriesC (fibreCoefficientSymbol η G v r) ξ t‖ ≤ fibreWordSymbolBound Cw * fibreNorm ξ ^ 2 := by
  have hb := fibreCoefficientFamily_symbol_quadratic_bound η Cw hη0 hη hCw G hG hv hw ξ hξ t
  dsimp only at hb ⊢
  convert hb using 1
  unfold fibreWordSymbolBound
  simp only [div_eq_mul_inv, mul_pow, inv_pow]
  ring

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization
namespace AVRegularity.CycleEvolution

/-! Actual normalized fibre evolution on complete finite energy data, with L2 initial traces. -/

def fibreCoefficientEnergyEvolutionCLM {a b : ℝ} (hab : a ≤ b)
    (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) :
    CellFiniteEnergyDatum a b →L[ℂ] CellEnergySpace a b := by
  let lam := fibreSeriesC (fibreCoefficientSymbol η G v (fibreCoefficientFamily η Cw hη G hG hv hw)) ξ
  let C := fibreCoefficients η G v ξ lam
  let k := (6 * Cw + 24) * (fibreNorm ξ / fibreCoefficientMajorantRadius Cw) ^ 2
  have hκ : AEStronglyMeasurable C.κ (volume.restrict (Icc a b)) :=
    (fibreCoefficientFamily_symbol_memLp_top η Cw hη0 hη hCw G hG hv hw ξ hξ a b).aestronglyMeasurable.neg
  have hκb : ∀ t, ‖C.κ t‖ ≤ k := by
    intro t
    change ‖-lam t‖ ≤ k
    rw [norm_neg]
    exact fibreCoefficientFamily_symbol_quadratic_bound η Cw hη0 hη hCw G hG hv hw ξ hξ t
  exact (cellEnergySpaceOfCarrierCLM a b).comp
    (cellFiniteEnergyEvolutionCLM hab C hG V k hv.1 hb hκ hκb)

theorem fibreCoefficientEnergyEvolutionCLM_solves {a b : ℝ} (hab : a ≤ b)
    (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw)
    (d : CellFiniteEnergyDatum a b) :
    IsCellFiniteEnergyEvolution
      (fibreCoefficients η G v ξ (fibreSeriesC
        (fibreCoefficientSymbol η G v (fibreCoefficientFamily η Cw hη G hG hv hw)) ξ))
      hG V hv.1 hb d
      (fibreCoefficientEnergyEvolutionCLM hab η Cw hη0 hη hCw G hG hv hw V hb ξ hξ d) := by
  unfold fibreCoefficientEnergyEvolutionCLM
  dsimp only
  simp only [ContinuousLinearMap.comp_apply, cellEnergySpaceOfCarrier_eq]
  exact cellFiniteEnergyEvolutionCLM_solves hab _ hG V _ hv.1 hb _ _ d

/-! A fixed-data normalized fibre solution family, using the actual complete energy evolution. -/

def fibreCoefficientEnergyFamily {a b : ℝ} (hab : a ≤ b)
    (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (d : CellFiniteEnergyDatum a b) (ξ : Fin 2 → ℂ) : CellEnergySpace a b :=
  if hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw then
    fibreCoefficientEnergyEvolutionCLM hab η Cw hη0 hη hCw G hG hv hw V hb ξ hξ d
  else 0

theorem fibreCoefficientEnergyFamily_solves {a b : ℝ} (hab : a ≤ b)
    (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (d : CellFiniteEnergyDatum a b) (ξ : Fin 2 → ℂ)
    (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) :
    IsCellFiniteEnergyEvolution
      (fibreCoefficients η G v ξ (fibreSeriesC
        (fibreCoefficientSymbol η G v (fibreCoefficientFamily η Cw hη G hG hv hw)) ξ))
      hG V hv.1 hb d
      (fibreCoefficientEnergyFamily hab η Cw hη0 hη hCw G hG hv hw V hb d ξ) := by
  unfold fibreCoefficientEnergyFamily
  rw [dite_eq_left hξ]
  exact fibreCoefficientEnergyEvolutionCLM_solves hab η Cw hη0 hη hCw G hG hv hw V hb ξ hξ d

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The actual normalized fibre graph gives the exact scalar mean increment. -/

theorem fibreCoefficient_normalized_mean_increment (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw)
    {a b : ℝ} (_hab : a ≤ b) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let D := fibreSeriesJet r ξ
    let C := fibreCoefficients η G v ξ (fibreSeriesC (fibreCoefficientSymbol η G v r) ξ)
    let R := fun t => cellRawTrace D t + cellConstantCLM 1
    ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
      (F : ℝ → Fin 2 → ComplexCellL2),
      CellWeakHilbertCurve a b u slice
        (fun t => cellDualDerivative C hG V hv.1 hb t (slice t) 0 (F t)) →
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
        cellMean (u t) - cellMean (u s) = ∫ τ in s..t,
          -Complex.I * cellBlochDriftMeanCLM η Cw hCw hv hw ξ τ
            (u τ - cellScalarCLM (cellMean (u τ)) (R τ)) +
            ∑ j : Fin 2, Complex.I * ((Real.sqrt η : ℂ) * ξ j) * cellMean (F τ j) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let D := fibreSeriesJet r ξ
  let lam := fibreSeriesC (fibreCoefficientSymbol η G v r) ξ
  let C : CellCoefficients := ⟨fun t _ => G t, v,
    (fun j => (Real.sqrt η : ℂ) * ξ j), (fun t => -lam t)⟩
  let R := fun t => cellRawTrace D t + cellConstantCLM 1
  dsimp only
  intro u slice F h s hs t ht hst
  change CellWeakHilbertCurve a b u slice
    (fun τ => cellDualDerivative C hG V hv.1 hb τ (slice τ) 0 (F τ)) at h
  rw [h.mean_increment s hs t ht hst]
  apply intervalIntegral.integral_congr_ae_restrict
  have ha := h.agrees.filter_mono (ae_mono (Measure.restrict_mono
    (show Ioc s t ⊆ Icc a b from Ioc_subset_Icc_self.trans (Icc_subset_Icc hs.1 ht.2)) le_rfl))
  rw [uIoc_of_le hst]
  filter_upwards [ha] with τ hτ
  have hA : cellMean (torusHkValueCLM (slice τ)) = cellMean (u τ) :=
    congrArg (fun z : ComplexCellL2 => cellMean z) hτ.symm
  have hdecomp : torusHkValueCLM (slice τ) =
      cellScalarCLM (cellMean (torusHkValueCLM (slice τ))) (cellRawTrace D τ + cellConstantCLM 1) +
        (u τ - cellScalarCLM (cellMean (u τ)) (R τ)) := by
    rw [hA, ← hτ]
    change u τ = cellScalarCLM (cellMean (u τ)) (R τ) +
      (u τ - cellScalarCLM (cellMean (u τ)) (R τ))
    abel
  have hκ : C.κ τ = (η : ℂ) * fibreQuad (G τ) ξ +
      Complex.I * cellBlochDriftMeanCLM η Cw hCw hv hw ξ τ (cellRawTrace D τ) := by
    change -lam τ = _
    have hsymbol := fibreCoefficientFamily_symbol_class η Cw hη hCw G hG hv hw ξ hξ τ
    dsimp only at hsymbol
    change lam τ = _ at hsymbol
    rw [hsymbol]
    ring
  exact cellBloch_normalized_mean_identity η Cw hη0 hCw G hG hv hw hm V hb
    ξ C.κ τ (slice τ) (cellRawTrace D τ)
    (u τ - cellScalarCLM (cellMean (u τ)) (R τ)) hκ hdecomp (F τ)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization
namespace AVRegularity.CycleEvolution

/-! The actual normalized fibre family satisfies the baseline Bloch equation with the analytic potential-difference class. -/

theorem fibreCoefficientEnergyFamily_shifted_solves {a b : ℝ} (hab : a ≤ b)
    (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (d : CellFiniteEnergyDatum a b) (ξ ζ : Fin 2 → ℂ)
    (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw)
    (hζ : fibreNorm ζ ≤ fibreCoefficientMajorantRadius Cw) :
    let lam := fibreCoefficientSymbol η G v (fibreCoefficientFamily η Cw hη G hG hv hw)
    let C := fibreCoefficients η G v ξ (fibreSeriesC lam ξ)
    let Q := fibreCoefficientSymbolTimeClass (Icc a b) η Cw hη0 hη hCw G hG hv hw
    IsCellFiniteEnergyEvolution
      { C with
        θ := C.θ + (Real.sqrt η : ℂ) • (ζ - ξ)
        κ := fun t => C.κ t + (-Q ζ + Q ξ) t }
      hG V hv.1 hb d
      (fibreCoefficientEnergyFamily hab η Cw hη0 hη hCw G hG hv hw V hb d ζ) := by
  let lam := fibreCoefficientSymbol η G v (fibreCoefficientFamily η Cw hη G hG hv hw)
  let Q := fibreCoefficientSymbolTimeClass (Icc a b) η Cw hη0 hη hCw G hG hv hw
  have hz := fibreCoefficientEnergyFamily_solves hab η Cw hη0 hη hCw G hG hv hw V hb d ζ hζ
  have hq := fibreCoefficientSymbolTimeDifference_ae (Icc a b) η Cw hη0 hη hCw G hG hv hw ξ ζ hξ hζ
  have he : (fun t => -fibreSeriesC lam ζ t) =ᵐ[volume.restrict (Icc a b)]
      fun t => -fibreSeriesC lam ξ t + (-Q ζ + Q ξ) t := by
    filter_upwards [hq] with t ht
    rw [ht]
    ring
  have hr := cellFiniteEnergyEvolution_potential_congr
    (fibreCoefficients η G v ζ (fibreSeriesC lam ζ)) hG V hv.1 hb
    (fun t => -fibreSeriesC lam ζ t)
    (fun t => -fibreSeriesC lam ξ t + (-Q ζ + Q ξ) t) he d
    (fibreCoefficientEnergyFamily hab η Cw hη0 hη hCw G hG hv hw V hb d ζ) hz
  dsimp only
  rw [fibreCoefficients_theta_add_shift]
  exact hr

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The phase times the constructed graph mode satisfies the genuine homogeneous Bloch equation. -/

theorem fibreCoefficientFamily_graph_homogeneous_evolution (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw)
    {a b : ℝ} (hab : a ≤ b) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let D := fibreSeriesJet r ξ
    let lam := fibreSeriesC (fibreCoefficientSymbol η G v r) ξ
    let phase := fun t => Complex.exp (∫ s in a..t, lam s)
    CellWeakHilbertCurve a b
      (fun t => cellScalarCLM (phase t) (cellRawTrace D t + cellConstantCLM 1))
      (fun t => cellH1Scalar (phase t) (cellH1Slice D t + cellH1One))
      (fun t => cellDualDerivative
        ⟨fun t _ => G t, v, fun j => (Real.sqrt η : ℂ) * ξ j, 0⟩ hG V hv.1 hb t
        (cellH1Scalar (phase t) (cellH1Slice D t + cellH1One)) 0 0) := by
  have hh := fibreCoefficientFamily_graph_weak_evolution η Cw hη0 hη hCw G hG
    hv hm hw V hb ξ hξ hab
  have hl := fibreCoefficientFamily_symbol_memLp_top η Cw hη0 hη hCw G hG
    hv hw ξ hξ a b
  exact hh.remove_potential hab (fun t _ => G t) hG v V hv.1 hb _ _ hl

/-! The actual graph mode obeys the real-frequency phase-weighted L² ratio inequality. -/

theorem fibreBloch_real_star (η : ℝ) (ξ : Fin 2 → ℂ)
    (hξ : ∀ j, (ξ j).im = 0) (j : Fin 2) :
    star ((Real.sqrt η : ℂ) * ξ j) = (Real.sqrt η : ℂ) * ξ j := by
  have hs : star (ξ j) = ξ j := by
    apply Complex.ext
    · exact Complex.conj_re _
    · simp only [Complex.star_def, Complex.conj_im, hξ j, neg_zero]
  rw [star_mul, show star (Real.sqrt η : ℂ) = (Real.sqrt η : ℂ) from Complex.conj_ofReal _, hs]
  exact mul_comm _ _

theorem fibreCoefficientFamily_graph_real_contraction (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hreal : ∀ j, (ξ j).im = 0)
    (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw)
    {a b : ℝ} (hab : a ≤ b) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let D := fibreSeriesJet r ξ
    ‖Complex.exp (∫ s in a..b, fibreSeriesC (fibreCoefficientSymbol η G v r) ξ s)‖ *
      ‖cellRawTrace D b + cellConstantCLM 1‖ ≤ ‖cellRawTrace D a + cellConstantCLM 1‖ := by
  have hh := fibreCoefficientFamily_graph_homogeneous_evolution η Cw hη0 hη hCw
    G hG hv hm hw V hb ξ hξ hab
  have hn := hh.real_shift_contraction hab hG hv V hb _ (fibreBloch_real_star η ξ hreal)
  simpa only [cellScalarCLM_smul, norm_smul, intervalIntegral.integral_same,
    Complex.exp_zero, norm_one, one_mul] using hn

/-! The actual normalized fibre graph gives the genuine triangular mean-zero equation with arbitrary divergence forcing. -/

theorem fibreCoefficient_normalized_mean_remainder (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw)
    {a b : ℝ} (hab : a ≤ b) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let D := fibreSeriesJet r ξ
    let C := fibreCoefficients η G v ξ (fibreSeriesC (fibreCoefficientSymbol η G v r) ξ)
    let R := fun t => cellRawTrace D t + cellConstantCLM 1
    let Rslice := fun t => cellH1Slice D t + cellH1One
    ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
      (F : ℝ → Fin 2 → ComplexCellL2),
      CellWeakHilbertCurve a b u slice
        (fun t => cellDualDerivative C hG V hv.1 hb t (slice t) 0 (F t)) →
      CellWeakHilbertCurve a b
        (fun t => u t - cellScalarCLM (cellMean (u t)) (R t))
        (fun t => slice t - cellH1Scalar (cellMean (u t)) (Rslice t))
        (fun t => cellDualDerivative C hG V hv.1 hb t
          (slice t - cellH1Scalar (cellMean (u t)) (Rslice t)) 0 (F t) -
          cellPivotDualCLM (cellScalarCLM
            (-Complex.I * cellBlochDriftMeanCLM η Cw hCw hv hw ξ t
              (torusHkValueCLM (slice t - cellH1Scalar (cellMean (u t)) (Rslice t))) +
              ∑ j : Fin 2, Complex.I * ((Real.sqrt η : ℂ) * ξ j) * cellMean (F t j)) (R t))) ∧
      ∀ t, cellMean ((u t - cellScalarCLM (cellMean (u t)) (R t) : ComplexCellL2)) = 0 := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let D := fibreSeriesJet r ξ
  let lam := fibreSeriesC (fibreCoefficientSymbol η G v r) ξ
  let C : CellCoefficients := ⟨fun t _ => G t, v,
    (fun j => (Real.sqrt η : ℂ) * ξ j), (fun t => -lam t)⟩
  let R := fun t => cellRawTrace D t + cellConstantCLM 1
  let Rslice := fun t => cellH1Slice D t + cellH1One
  dsimp only
  intro u slice F h
  change CellWeakHilbertCurve a b u slice
    (fun t => cellDualDerivative C hG V hv.1 hb t (slice t) 0 (F t)) at h
  have hR := fibreCoefficientFamily_graph_weak_evolution η Cw hη0 hη hCw G hG hv hm hw V hb ξ hξ hab
  change CellWeakHilbertCurve a b R Rslice
    (fun t => cellDualDerivative C hG V hv.1 hb t (Rslice t) 0 0) at hR
  have hz := cellWeakForcedGraph_mean_remainder hab C hG V hv.1 hb (fun _ => 0) F h hR
  refine ⟨hz.dual_congr ?_, ?_⟩
  · filter_upwards [h.agrees, hR.agrees] with t ht htR
    have hA : cellMean (torusHkValueCLM (slice t)) = cellMean (u t) :=
      congrArg (fun z : ComplexCellL2 => cellMean z) ht.symm
    have hzval : torusHkValueCLM (slice t - cellH1Scalar (cellMean (u t)) (Rslice t)) =
        torusHkValueCLM (slice t) - cellScalarCLM (cellMean (u t)) (R t) := by
      rw [map_sub, cellH1Scalar_value, ← htR]
    have hdecomp : torusHkValueCLM (slice t) =
        cellScalarCLM (cellMean (torusHkValueCLM (slice t))) (cellRawTrace D t + cellConstantCLM 1) +
        torusHkValueCLM (slice t - cellH1Scalar (cellMean (u t)) (Rslice t)) := by
      rw [hA, hzval]
      change torusHkValueCLM (slice t) =
        cellScalarCLM (cellMean (u t)) (R t) +
          (torusHkValueCLM (slice t) - cellScalarCLM (cellMean (u t)) (R t))
      abel
    have hκ : C.κ t = (η : ℂ) * fibreQuad (G t) ξ +
        Complex.I * cellBlochDriftMeanCLM η Cw hCw hv hw ξ t (cellRawTrace D t) := by
      change -lam t = _
      have hs := fibreCoefficientFamily_symbol_class η Cw hη hCw G hG hv hw ξ hξ t
      dsimp only at hs
      change lam t = _ at hs
      rw [hs]
      ring
    have hd := cellBloch_normalized_mean_identity η Cw hη0 hCw G hG hv hw hm V hb
      ξ C.κ t (slice t) (cellRawTrace D t)
      (torusHkValueCLM (slice t - cellH1Scalar (cellMean (u t)) (Rslice t))) hκ hdecomp (F t)
    change cellDualComplexPair (cellDualDerivative C hG V hv.1 hb t (slice t) 0 (F t)) cellH1One = _ at hd
    rw [hd]
    rfl
  · intro t
    apply cellMean_graph_mean_remainder_zero
    exact fibreCoefficientFamily_graph_class_mean η Cw hη hCw G hG hv hw ξ hξ t

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The first exact real-frequency ratio clause of the fibre graph. -/

theorem fibreCoefficientFamily_graph_real_ratio (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hreal : ∀ j, (ξ j).im = 0)
    (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw)
    {a b : ℝ} (hab : a ≤ b) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let D := fibreSeriesJet r ξ
    ENNReal.ofReal ‖Complex.exp (∫ s in a..b, fibreSeriesC (fibreCoefficientSymbol η G v r) ξ s)‖ *
      cellL2Norm (fun x => 1 + cellValue D b x) ≤
        cellL2Norm (fun x => 1 + cellValue D a x) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let D := fibreSeriesJet r ξ
  have hi := fibreCoefficientFamily_graph_isInverse η Cw hη hCw G hG hv hw ξ hξ
  have hn := fibreCoefficientFamily_graph_real_contraction η Cw hη0 hη hCw G hG
    hv hm hw V hb ξ hreal hξ hab
  change ENNReal.ofReal ‖Complex.exp (∫ s in a..b,
    fibreSeriesC (fibreCoefficientSymbol η G v r) ξ s)‖ *
    cellL2Norm (fun x => 1 + cellValue D b x) ≤ cellL2Norm (fun x => 1 + cellValue D a x)
  rw [cellL2Norm_normalized_raw_trace D b (hi.1.2.2.1 b (Set.mem_univ b)).1,
    cellL2Norm_normalized_raw_trace D a (hi.1.2.2.1 a (Set.mem_univ a)).1,
    ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hn

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The genuine graph remainder has the exact projected-feedback equation used by the energy estimates. -/

theorem fibreCoefficient_projected_remainder (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw)
    {a b : ℝ} (hab : a ≤ b) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let D := fibreSeriesJet r ξ
    let lam := fibreSeriesC (fibreCoefficientSymbol η G v r) ξ
    let C := fibreCoefficients η G v ξ lam
    let C0 := fibreCoefficients η G v ξ (fun _ => 0)
    let R := fun t => cellRawTrace D t + cellConstantCLM 1
    let Rslice := fun t => cellH1Slice D t + cellH1One
    ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
      (F : ℝ → Fin 2 → ComplexCellL2),
      CellWeakHilbertCurve a b u slice
        (fun t => cellDualDerivative C hG V hv.1 hb t (slice t) 0 (F t)) →
      CellWeakHilbertCurve a b
        (fun t => u t - cellScalarCLM (cellMean (u t)) (R t))
        (fun t => slice t - cellH1Scalar (cellMean (u t)) (Rslice t))
        (fun t => cellDualDerivative C0 hG V hv.1 hb t
          (slice t - cellH1Scalar (cellMean (u t)) (Rslice t)) 0 (F t) -
          cellPivotDualCLM (cellScalarCLM (lam t)
            (torusHkValueCLM (slice t - cellH1Scalar (cellMean (u t)) (Rslice t)))) -
          cellPivotDualCLM (cellScalarCLM
            (-Complex.I * cellBlochDriftMeanCLM η Cw hCw hv hw ξ t
              (torusHkValueCLM (slice t - cellH1Scalar (cellMean (u t)) (Rslice t))) +
              ∑ j : Fin 2, Complex.I * ((Real.sqrt η : ℂ) * ξ j) * cellMean (F t j)) (R t))) ∧
      ∀ t, cellMean ((u t - cellScalarCLM (cellMean (u t)) (R t) : ComplexCellL2)) = 0 := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let D := fibreSeriesJet r ξ
  let lam := fibreSeriesC (fibreCoefficientSymbol η G v r) ξ
  let R := fun t => cellRawTrace D t + cellConstantCLM 1
  let Rslice := fun t => cellH1Slice D t + cellH1One
  dsimp only
  intro u slice F h
  have hz := fibreCoefficient_normalized_mean_remainder η Cw hη0 hη hCw G hG hv hm hw V hb ξ hξ hab
    u slice F h
  refine ⟨hz.1.dual_congr ?_, hz.2⟩
  apply Filter.Eventually.of_forall
  intro t
  change cellDualDerivative
    ⟨fun t _ => G t, v, (fun j => (Real.sqrt η : ℂ) * ξ j), (fun t => -lam t)⟩
    hG V hv.1 hb t (slice t - cellH1Scalar (cellMean (u t)) (Rslice t)) 0 (F t) -
    cellPivotDualCLM (cellScalarCLM
      (-Complex.I * cellBlochDriftMeanCLM η Cw hCw hv hw ξ t
        (torusHkValueCLM (slice t - cellH1Scalar (cellMean (u t)) (Rslice t))) +
        ∑ j : Fin 2, Complex.I * ((Real.sqrt η : ℂ) * ξ j) * cellMean (F t j)) (R t)) = _
  rw [cellDualDerivative_negative_potential]
  simp only [fibreCoefficients, neg_zero]
  rfl

/-! The actual future-dependent reversed graph supplies a genuine homogeneous backward adjoint mode. -/

def fibreAdjointGraphRaw (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) (ξ : Fin 2 → ℂ) :
    ℝ → RawJet2 1 ℂ :=
  fibreSeriesJet (fibreCoefficientFamily η Cw hη (fun t => G (-t))
    (cellMetric_timeReverse hG) (cellDrift_timeReverse hv)
    (cellDrift_timeReverse_scaled_bound hw)) (fun j => -ξ j)

def fibreAdjointGraphSymbol (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) (ξ : Fin 2 → ℂ) : ℝ → ℂ :=
  fibreSeriesC (fibreCoefficientSymbol η (fun t => G (-t)) (fun t x => -v (-t) x)
    (fibreCoefficientFamily η Cw hη (fun t => G (-t)) (cellMetric_timeReverse hG)
      (cellDrift_timeReverse hv) (cellDrift_timeReverse_scaled_bound hw))) (fun j => -ξ j)

def fibreAdjointGraphPhase (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (b t : ℝ) : ℂ :=
  Complex.exp (∫ s in -b..-t, fibreAdjointGraphSymbol η Cw hη G hG hv hw ξ s)

theorem fibreAdjointGraph_backward_homogeneous (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw)
    {a b : ℝ} (hab : a ≤ b) :
    let D := fibreAdjointGraphRaw η Cw hη G hG hv hw ξ
    let phase := fibreAdjointGraphPhase η Cw hη G hG hv hw ξ b
    let u := fun t => cellFiberCLM Complex.conjCLE.toContinuousLinearMap
      (cellScalarCLM (phase t) (cellRawTrace D (-t) + cellConstantCLM 1))
    let slice := fun t => cellH1Conj
      (cellH1Scalar (phase t) (cellH1Slice D (-t) + cellH1One))
    CellWeakHilbertCurve a b u slice
      (fun t => -cellDualDerivative
        (cellAdjointCoefficients ⟨fun t _ => G t, v, fun j => (Real.sqrt η : ℂ) * ξ j, 0⟩)
        hG V (cellDrift_neg hv).1 (cellDrift_neg_bound hb) t (slice t) 0 0) := by
  have hr (s : ℝ) (x : Vec 2) : ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2 := by
    simpa only [Pi.neg_apply, neg_sq] using hb (-s) x
  have hn : fibreNorm (fun j => -ξ j) ≤ fibreCoefficientMajorantRadius Cw := by
    rwa [fibreNorm_neg]
  have ha : -b ≤ -a := by linarith
  have hh := fibreCoefficientFamily_graph_homogeneous_evolution η Cw hη0 hη hCw
    (fun t => G (-t)) (cellMetric_timeReverse hG) (cellDrift_timeReverse hv)
    (cellDrift_timeReverse_mean_zero hm) (cellDrift_timeReverse_scaled_bound hw)
    V hr (fun j => -ξ j) hn ha
  dsimp only at hh
  have he : (fun j => (Real.sqrt η : ℂ) * -ξ j) =
      (fun j => -((Real.sqrt η : ℂ) * ξ j)) := by
    funext j
    exact mul_neg _ _
  rw [he] at hh
  have ht := hh.reflected_adjoint (fun t _ => G t) hG hv V hb
    (fun j => (Real.sqrt η : ℂ) * ξ j)
  simpa only [fibreAdjointGraphRaw, fibreAdjointGraphSymbol, fibreAdjointGraphPhase] using ht

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization Filter Topology
namespace AVRegularity.CycleEvolution

/-! The actual fixed-data normalized fibre solution is analytic in complex frequency on its full coefficient domain. -/

theorem fibreCoefficientEnergyFamily_analyticAt {a b : ℝ} (hab : a ≤ b)
    (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (d : CellFiniteEnergyDatum a b) (ξ : Fin 2 → ℂ)
    (hξ : fibreNorm ξ < fibreCoefficientMajorantRadius Cw) :
    AnalyticAt ℂ (fibreCoefficientEnergyFamily hab η Cw hη0 hη hCw G hG hv hw V hb d) ξ := by
  let lam := fibreCoefficientSymbol η G v (fibreCoefficientFamily η Cw hη G hG hv hw)
  let C := fibreCoefficients η G v ξ (fibreSeriesC lam ξ)
  let k := (6 * Cw + 24) * (fibreNorm ξ / fibreCoefficientMajorantRadius Cw) ^ 2
  let Q := fibreCoefficientSymbolTimeClass (Icc a b) η Cw hη0 hη hCw G hG hv hw
  let δ := fun ζ : Fin 2 → ℂ => (Real.sqrt η : ℂ) • (ζ - ξ)
  let q := fun ζ => -Q ζ + Q ξ
  have hκ : AEStronglyMeasurable C.κ (volume.restrict (Icc a b)) :=
    (fibreCoefficientFamily_symbol_memLp_top η Cw hη0 hη hCw G hG hv hw ξ hξ.le a b).aestronglyMeasurable.neg
  have hκb : ∀ t, ‖C.κ t‖ ≤ k := by
    intro t
    change ‖-fibreSeriesC lam ξ t‖ ≤ k
    rw [norm_neg]
    exact fibreCoefficientFamily_symbol_quadratic_bound η Cw hη0 hη hCw G hG hv hw ξ hξ.le t
  have hδ : AnalyticAt ℂ δ ξ := fibreBlochFrequencyDifference_analyticAt η ξ
  have hq : AnalyticAt ℂ q ξ :=
    fibreCoefficientSymbolTimeDifference_analyticAt (Icc a b) η Cw hη0 hη hCw G hG hv hw ξ
      ((fibrePiNorm_le ξ).trans_lt hξ)
  refine cellBlochEvolution_family_analyticAt hab C hG V k hv.1 hb hκ hκb δ q ξ hδ hq ?_ ?_ d
    (fibreCoefficientEnergyFamily hab η Cw hη0 hη hCw G hG hv hw V hb d) ?_
  · exact fibreBlochFrequencyDifference_zero η ξ
  · exact neg_add_cancel _
  · have hnear : ∀ᶠ ζ in 𝓝 ξ, fibreNorm ζ < fibreCoefficientMajorantRadius Cw :=
      fibreNorm_continuous.continuousAt.eventually (gt_mem_nhds hξ)
    filter_upwards [hnear] with ζ hζ
    exact fibreCoefficientEnergyFamily_shifted_solves hab η Cw hη0 hη hCw G hG hv hw V hb d ξ ζ hξ.le hζ.le

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The convergent normalized dual row is the actual reciprocal times the reversed graph L² class. -/

theorem fibreAdjointCorrection_series_reverse (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (t : ℝ) (x : Vec 2) :
    fibreSeriesFun (fibreAdjointCorrectionCoefficients η Cw hη G hG hv hw) ξ t x =
      cellValue (fibreAdjointGraphRaw η Cw hη G hG hv hw ξ) (-t) x := by
  exact fibreReverseValueCoefficients_series
    (fibreCoefficientFamily η Cw hη (fun s => G (-s)) (cellMetric_timeReverse hG)
      (cellDrift_timeReverse hv) (cellDrift_timeReverse_scaled_bound hw)) ξ t x

theorem fibreAdjointRow_source_slice (η Cw : ℝ) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16) (t : ℝ) :
    cellSourceSlice (fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ) t =
      cellScalarCLM (fibreSeriesC (fibreAdjointNormalizationCoefficients η Cw hη G hG hv hw) ξ t)
        (cellRawTrace (fibreAdjointGraphRaw η Cw hη G hG hv hw ξ) (-t) + cellConstantCLM 1) := by
  have hR := fibreCoefficientMajorantRadius_pos hCw
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := hξ.trans (by linarith)
  have hn : fibreNorm (fun j => -ξ j) ≤ fibreCoefficientMajorantRadius Cw := by
    rwa [fibreNorm_neg]
  have hi := fibreCoefficientFamily_graph_isInverse η Cw hη hCw (fun s => G (-s))
    (cellMetric_timeReverse hG) (cellDrift_timeReverse hv)
    (cellDrift_timeReverse_scaled_bound hw) (fun j => -ξ j) hn
  have ht : MemLp (cellValue (fibreAdjointGraphRaw η Cw hη G hG hv hw ξ) (-t)) 2
      (volume.restrict AVenhance.unitCube) := (hi.1.2.2.1 (-t) (mem_univ (-t))).1
  apply cellSourceSlice_eq_of_ae
  filter_upwards [cellScalarCLM_ae
    (fibreSeriesC (fibreAdjointNormalizationCoefficients η Cw hη G hG hv hw) ξ t)
    (cellRawTrace (fibreAdjointGraphRaw η Cw hη G hG hv hw ξ) (-t) + cellConstantCLM 1),
    cellRawTrace_add_one_ae (fibreAdjointGraphRaw η Cw hη G hG hv hw ξ) (-t) ht,
    fibreAdjointRowCoefficients_series_ae η Cw hη hCw G hG hv hw ξ hξ t] with x hs hr he
  rw [hs, hr]
  rw [fibreAdjointCorrection_series_reverse] at he
  exact he.symm

/-! The reversed graph class is exactly the correction series class. -/

theorem fibreAdjointCorrection_source_slice (η Cw : ℝ) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16) (t : ℝ) :
    cellSourceSlice (fibreSeriesFun (fibreAdjointCorrectionCoefficients η Cw hη G hG hv hw) ξ) t =
      cellRawTrace (fibreAdjointGraphRaw η Cw hη G hG hv hw ξ) (-t) := by
  have hR := fibreCoefficientMajorantRadius_pos hCw
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := hξ.trans (by linarith)
  have hn : fibreNorm (fun j => -ξ j) ≤ fibreCoefficientMajorantRadius Cw := by
    rwa [fibreNorm_neg]
  have hi := fibreCoefficientFamily_graph_isInverse η Cw hη hCw (fun s => G (-s))
    (cellMetric_timeReverse hG) (cellDrift_timeReverse hv)
    (cellDrift_timeReverse_scaled_bound hw) (fun j => -ξ j) hn
  have ht : MemLp (cellValue (fibreAdjointGraphRaw η Cw hη G hG hv hw ξ) (-t)) 2
      (volume.restrict AVenhance.unitCube) := (hi.1.2.2.1 (-t) (mem_univ (-t))).1
  apply cellSourceSlice_eq_of_ae
  have ha := cellRawTrace_ae (fibreAdjointGraphRaw η Cw hη G hG hv hw ξ) (-t) ht
  exact ha.trans (Filter.Eventually.of_forall (fun x =>
    (fibreAdjointCorrection_series_reverse η Cw hη G hG hv hw ξ t x).symm))

/-! The actual normalized row source class pairs exactly to one with the actual forward graph trace. -/

theorem fibreAdjointRow_pairing_normalization (η Cw : ℝ) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16) (t : ℝ) :
    let D := fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hw) ξ
    let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
    cellComplexPair (cellRawTrace D t + cellConstantCLM 1)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellSourceSlice ell t)) = 1 := by
  let D := fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hw) ξ
  let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
  have hR := fibreCoefficientMajorantRadius_pos hCw
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := hξ.trans (by linarith)
  have hi := fibreCoefficientFamily_graph_isInverse η Cw hη hCw G hG hv hw ξ hξR
  have hl := (fibreAdjointRowCoefficients_series_memLp_bound η Cw hη hCw G hG hv hw ξ hξ t).1
  change cellComplexPair (cellRawTrace D t + cellConstantCLM 1)
    (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellSourceSlice ell t)) = 1
  rw [cellComplexPair_conjugate_source_slice ell t hl]
  have he : cellMean (fun x => ell t x * (cellRawTrace D t + cellConstantCLM 1) x) =
      cellMean (fun x => ell t x * (1 + cellValue D t x)) := by
    apply integral_congr_ae
    filter_upwards [cellRawTrace_add_one_ae D t (hi.1.2.2.1 t (mem_univ t)).1] with x hx
    rw [hx]
  exact he.trans (fibreAdjointRowCoefficients_normalization η Cw hη hCw G hG hv hw ξ hξ t).2

end AVRegularity.CycleEvolution
end
