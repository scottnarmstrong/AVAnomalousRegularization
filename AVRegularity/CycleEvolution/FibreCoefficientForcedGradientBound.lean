-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.FibreAdjointRowPairingNormalization
public import AVRegularity.CycleEvolution.CellEnergySpaceRawJetCauchyBound
import AVRegularity.CycleEvolution.CellLimitMoments
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The actual normalized row is exactly the conserved backward-mode pairing ratio. -/

theorem fibreAdjointRow_pairing_ratio (η Cw : ℝ) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16)
    (b t : ℝ) (u : ComplexCellL2) :
    let D := fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hw) ξ
    let Dr := fibreAdjointGraphRaw η Cw hη G hG hv hw ξ
    let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
    let q := cellFiberCLM Complex.conjCLE.toContinuousLinearMap
      (cellScalarCLM (fibreAdjointGraphPhase η Cw hη G hG hv hw ξ b t)
        (cellRawTrace Dr (-t) + cellConstantCLM 1))
    cellComplexPair u (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellSourceSlice ell t)) =
      cellComplexPair u q / cellComplexPair (cellRawTrace D t + cellConstantCLM 1) q := by
  let D := fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hw) ξ
  let Dr := fibreAdjointGraphRaw η Cw hη G hG hv hw ξ
  let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
  let A := cellRawTrace Dr (-t) + cellConstantCLM 1
  let phase := fibreAdjointGraphPhase η Cw hη G hG hv hw ξ b t
  have hn := fibreAdjointRow_pairing_normalization η Cw hη hCw G hG hv hw ξ hξ t
  have hs := fibreAdjointRow_source_slice η Cw hη hCw G hG hv hw ξ hξ t
  dsimp only at hn
  change cellComplexPair u (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellSourceSlice ell t)) =
    cellComplexPair u (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellScalarCLM phase A)) /
      cellComplexPair (cellRawTrace D t + cellConstantCLM 1)
        (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellScalarCLM phase A))
  rw [hs]
  simp only [cellFiberConj_scalar, cellComplexPair_scalar_right, star_star]
  rw [hs] at hn
  simp only [cellFiberConj_scalar, cellComplexPair_scalar_right, star_star] at hn
  exact complex_normalized_pairing_ratio _ _ phase _ hn (Complex.exp_ne_zero _)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! The actual normalized row distance is bounded by the actual reversed graph norm. -/

theorem fibreAdjointRow_reverse_distance (η Cw : ℝ) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16) (t : ℝ) :
    ‖cellSourceSlice (fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ) t -
      cellConstantCLM 1‖ ≤ 4 *
        ‖cellRawTrace (fibreAdjointGraphRaw η Cw hη G hG hv hw ξ) (-t)‖ := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let D := fibreSeriesJet r ξ
  let A := cellRawTrace (fibreAdjointGraphRaw η Cw hη G hG hv hw ξ) (-t)
  let a := fibreSeriesFun (fibreAdjointCorrectionCoefficients η Cw hη G hG hv hw) ξ
  let k := fibreSeriesC (fibreAdjointNormalizationCoefficients η Cw hη G hG hv hw) ξ t
  have hR := fibreCoefficientMajorantRadius_pos hCw
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := hξ.trans (by linarith)
  have hi := fibreCoefficientFamily_graph_isInverse η Cw hη hCw G hG hv hw ξ hξR
  have hraw := cellRawTrace_ae D t (hi.1.2.2.1 t (mem_univ t)).1
  have hρ : ‖cellRawTrace D t‖ ≤ 1 := by
    have he := (cellValue_cellL2Norm_le_energy D t).trans
      (fibreCoefficientFamily_summed_energy_le η Cw hη hCw G hG hv hw ξ hξR)
    rw [cellL2Norm_eq_of_class _ _ hraw] at he
    have hnum : 2 * (fibreNorm ξ / fibreCoefficientMajorantRadius Cw) ≤ 1 := by
      rw [← mul_div_assoc, div_le_iff₀ hR]
      linarith
    have hbound : 2 * ENNReal.ofReal (fibreNorm ξ / fibreCoefficientMajorantRadius Cw) ≤
        ENNReal.ofReal 1 := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num)]
      exact ENNReal.ofReal_le_ofReal hnum
    exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mp (he.trans hbound)
  have ha := fibreAdjointCorrectionCoefficients_series_properties η Cw hη hCw G hG hv hw ξ hξR t
  have hp : cellComplexPair (cellRawTrace D t)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap A) =
      fibreSeriesC (fibreAdjointOverlapCoefficients η Cw hη G hG hv hw) ξ t := by
    dsimp only [A]
    rw [← fibreAdjointCorrection_source_slice η Cw hη hCw G hG hv hw ξ hξ t,
      cellComplexPair_conjugate_source_slice _ t ha.1]
    calc
      _ = cellMean (fun x => a t x * cellValue D t x) := by
        apply integral_congr_ae
        filter_upwards [hraw] with x hx
        rw [hx]
      _ = _ := (fibreAdjointOverlapCoefficients_series η Cw hη hCw G hG hv hw ξ hξR t).symm
  rw [fibreAdjointRow_source_slice η Cw hη hCw G hG hv hw ξ hξ t]
  apply cellNormalizedRow_distance A (cellRawTrace D t) k
    (fibreAdjointNormalization_series_norm_le_two η Cw hη hCw G hG hv hw ξ hξ t) hρ
  rw [hp]
  exact fibreAdjointNormalizationCoefficients_series_mul η Cw hη hCw G hG hv hw ξ hξ t

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Raw complex norm-jet families of the actual normalized fixed-data fibre evolution. -/

def fibreCoefficientRawJetFamily {a b : ℝ} (hab : a ≤ b)
    (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (d : CellFiniteEnergyDatum a b) : ℕ × ℕ → (Fin 2 → ℂ) → ℝ → RawJet2 1 ℂ :=
  cellEnergySpaceAnalyticRawJet hab (fibreCoefficientEnergyFamily hab η Cw hη0 hη hCw G hG hv hw V hb d)

theorem fibreCoefficientRawJetFamily_isNormJetFamily {a b : ℝ} (hab : a ≤ b)
    (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (d : CellFiniteEnergyDatum a b) (K : ℕ) :
    IsNormJetFamily (𝕜 := ℂ) (cellEnergyNorm (Icc a b)) K
      {ξ | fibreNorm ξ < fibreCoefficientMajorantRadius Cw} (fibreCoefficientRawJetFamily hab η Cw hη0 hη hCw G hG hv hw V hb d) := by
  apply cellEnergySpaceAnalyticRawJet_isNormJetFamily
  intro ξ hξ
  exact fibreCoefficientEnergyFamily_analyticAt hab η Cw hη0 hη hCw G hG hv hw V hb d ξ hξ

theorem fibreCoefficientRawJetFamily_zero_isCellSolution {a b : ℝ} (hab : a ≤ b)
    (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (d : CellFiniteEnergyDatum a b)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hS : d.2.1 =ᵐ[volume.restrict (Icc a b)] fun t => cellSourceSlice src t)
    (hflux : ∀ j : Fin 2, d.2.2 j =ᵐ[volume.restrict (Icc a b)]
      fun t => cellSourceSlice (fun s x => F s x j) t)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) :
    IsCellSolution (Icc a b)
      (fibreCoefficients η G v ξ (fibreSeriesC
        (fibreCoefficientSymbol η G v (fibreCoefficientFamily η Cw hη G hG hv hw)) ξ))
      src F (fibreCoefficientRawJetFamily hab η Cw hη0 hη hCw G hG hv hw V hb d (0, 0) ξ) :=
  cellEnergySpaceRaw_isCellSolution hab _ hG V hv.1 hb src F hsrc hF d _ hS hflux
    (fibreCoefficientEnergyFamily_solves hab η Cw hη0 hη hCw G hG hv hw V hb d ξ hξ) _
    (cellEnergySpaceAnalyticRawJet_zero_represents hab (fibreCoefficientEnergyFamily hab η Cw hη0 hη hCw G hG hv hw V hb d) ξ)

theorem fibreCoefficientRawJetFamily_initial_ae {a b : ℝ} (hab : a ≤ b)
    (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (d : CellFiniteEnergyDatum a b) (ξ : Fin 2 → ℂ)
    (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) :
    cellValue (fibreCoefficientRawJetFamily hab η Cw hη0 hη hCw G hG hv hw V hb d (0, 0) ξ) a
      =ᵐ[volume.restrict AVenhance.unitCube] d.1 :=
  cellEnergySpaceRaw_initial_ae hab _ hG V hv.1 hb d _
    (fibreCoefficientEnergyFamily_solves hab η Cw hη0 hη hCw G hG hv hw V hb d ξ hξ) _
    (cellEnergySpaceAnalyticRawJet_zero_represents hab (fibreCoefficientEnergyFamily hab η Cw hη0 hη hCw G hG hv hw V hb d) ξ)

/-! Actual homogeneous norm jets with an arbitrary initial L2 class. -/

def cellHomogeneousEnergyDatum (a b : ℝ) (u : ComplexCellL2) : CellFiniteEnergyDatum a b :=
  (u, 0, fun _ => 0)

theorem fibreCoefficientHomogeneousJetFamily_solves {a b : ℝ} (hab : a ≤ b)
    (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (u : ComplexCellL2) (ξ : Fin 2 → ℂ)
    (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) :
    IsCellSolution (Icc a b)
      (fibreCoefficients η G v ξ (fibreSeriesC (fibreCoefficientSymbol η G v
        (fibreCoefficientFamily η Cw hη G hG hv hw)) ξ))
      (fun _ _ => 0) (fun _ _ => 0)
      (fibreCoefficientRawJetFamily hab η Cw hη0 hη hCw G hG hv hw V hb
        (cellHomogeneousEnergyDatum a b u) (0, 0) ξ) := by
  apply fibreCoefficientRawJetFamily_zero_isCellSolution hab η Cw hη0 hη hCw G hG hv hw V hb
    (cellHomogeneousEnergyDatum a b u) (fun _ _ => 0) (fun _ _ => 0) MemLp.zero MemLp.zero
  · filter_upwards [Lp.coeFn_zero (E := ComplexCellL2) (p := 2)
      (μ := volume.restrict (Icc a b))] with t ht
    simpa only [cellHomogeneousEnergyDatum, cellSourceSlice_zero, Pi.zero_apply] using ht
  · intro j
    filter_upwards [Lp.coeFn_zero (E := ComplexCellL2) (p := 2)
      (μ := volume.restrict (Icc a b))] with t ht
    simpa only [cellHomogeneousEnergyDatum, PiLp.zero_apply, cellSourceSlice_zero, Pi.zero_apply] using ht
  · exact hξ

/-! Actual divergence-source norm jets for arbitrary jointly L2 flux data. -/

def cellDivergenceEnergyDatum (a b : ℝ)
    (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube))) : CellFiniteEnergyDatum a b :=
  (0, 0, fun j => (cellSourceSlice_memLp (Icc a b) (fun t x => F t x j)
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).comp_memLp' hF)).toLp
      (cellSourceSlice (fun t x => F t x j)))

def cellDivergenceEnergyBudget (a b : ℝ)
    (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) : ℝ :=
  Real.sqrt (∫ t in a..b, ∑ j, ‖cellSourceSlice (fun r x => F r x j) t‖ ^ 2)

theorem fibreCoefficientForcedJetFamily_solves {a b : ℝ} (hab : a ≤ b)
    (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) :
    IsCellSolution (Icc a b)
      (fibreCoefficients η G v ξ (fibreSeriesC (fibreCoefficientSymbol η G v
        (fibreCoefficientFamily η Cw hη G hG hv hw)) ξ))
      (fun _ _ => 0) F
      (fibreCoefficientRawJetFamily hab η Cw hη0 hη hCw G hG hv hw V hb
        (cellDivergenceEnergyDatum a b F hF) (0, 0) ξ) := by
  apply fibreCoefficientRawJetFamily_zero_isCellSolution hab η Cw hη0 hη hCw G hG hv hw V hb
    (cellDivergenceEnergyDatum a b F hF) (fun _ _ => 0) F MemLp.zero hF
  · filter_upwards [Lp.coeFn_zero (E := ComplexCellL2) (p := 2)
      (μ := volume.restrict (Icc a b))] with t ht
    simpa only [cellDivergenceEnergyDatum, cellSourceSlice_zero, Pi.zero_apply] using ht
  · intro j
    exact (cellSourceSlice_memLp (Icc a b) (fun t x => F t x j)
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).comp_memLp' hF)).coeFn_toLp
  · exact hξ

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Uniform Hilbert norm of the actual normalized graph on the word radius. -/

theorem fibreCoefficientFamily_word_graph_norm_le_two (η Cw : ℝ)
    (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreWordRadius Cw)
    :
    ∀ t, ‖cellRawTrace (fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hw) ξ) t +
      cellConstantCLM 1‖ ≤ 2 := by
  intro t
  have hsmall := fibreWord_frequency_small hCw ξ hξ
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := by
    have ht := (hξ.trans (fibreWordRadius_le_graph Cw)).trans
      (fibreEvolutionRadius_le_majorant (Cw := Cw))
    have hp := fibreCoefficientMajorantRadius_pos hCw
    linarith
  have hr := fibreCoefficientFamily_graph_class_correction_bound η Cw hη hCw G hG hv hw ξ hξR t
  dsimp only at hr
  change ‖cellRawTrace (fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hw) ξ) t‖ ≤
    fibreWordCorrectionBound Cw * fibreNorm ξ at hr
  have hrsmall := hr.trans hsmall.2.1
  calc
    _ ≤ ‖cellRawTrace (fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hw) ξ) t‖ +
        ‖cellConstantCLM 1‖ := norm_add_le _ _
    _ ≤ 2 := by rw [cellConstantCLM_norm, norm_one]; linarith

/-! The forced normalized scalar mean has a square-root interval length bound. -/

theorem fibreCoefficient_forced_mean_bound (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreWordRadius Cw)
    {a b : ℝ} (hab : a ≤ b) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let D := fibreSeriesJet r ξ
    let lam := fibreSeriesC (fibreCoefficientSymbol η G v r) ξ
    let R := fun t => cellRawTrace D t + cellConstantCLM 1
    ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ) (F : ℝ → Fin 2 → ComplexCellL2),
      (∀ j, MemLp (fun t => F t j) 2 (volume.restrict (Icc a b))) →
      CellWeakHilbertCurve a b u slice
        (fun t => cellDualDerivative (fibreCoefficients η G v ξ lam) hG V hv.1 hb t (slice t) 0 (F t)) →
      let z := fun t => u t - cellScalarCLM (cellMean (u t)) (R t)
      ‖cellMean (u b)‖ ≤ ‖cellMean (u a)‖ + fibreNorm ξ * Real.sqrt (b - a) *
        (Cw * Real.sqrt (∫ t in a..b, ‖z t‖ ^ 2) +
          Real.sqrt (∫ t in a..b, ‖F t 0‖ ^ 2) + Real.sqrt (∫ t in a..b, ‖F t 1‖ ^ 2)) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let D := fibreSeriesJet r ξ
  let lam := fibreSeriesC (fibreCoefficientSymbol η G v r) ξ
  let R := fun t => cellRawTrace D t + cellConstantCLM 1
  dsimp only
  intro u slice F hF h
  let z := fun t => u t - cellScalarCLM (cellMean (u t)) (R t)
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := by
    have ht := (hξ.trans (fibreWordRadius_le_graph Cw)).trans
      (fibreEvolutionRadius_le_majorant (Cw := Cw))
    have hp := fibreCoefficientMajorantRadius_pos hCw
    linarith
  have hz := (fibreCoefficient_projected_remainder η Cw hη0 hη hCw G hG hv hm hw V hb
    ξ hξR hab u slice F h).1
  have hzL2 := cellContinuous_trace_memLp z hz.trace
  have hinc := fibreCoefficient_normalized_mean_increment η Cw hη0 hη hCw G hG hv hm hw V hb
    ξ hξR hab u slice F h a ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩ hab
  have hi := cellBloch_triangular_source_integral_bound hab η Cw hη hCw hv hw ξ z hzL2 F hF
  calc
    ‖cellMean (u b)‖ ≤ ‖cellMean (u a)‖ + ‖cellMean (u b) - cellMean (u a)‖ := by
      simpa only [add_sub_cancel] using norm_add_le (cellMean (u a)) (cellMean (u b) - cellMean (u a))
    _ ≤ _ := by rw [hinc]; exact add_le_add le_rfl hi

/-! The actual normalized dual row transports every genuine homogeneous Bloch weak solution by the actual scalar symbol. -/

theorem fibreAdjointRow_pairing_transport (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16)
    {a b : ℝ} (hab : a ≤ b) {u : ℝ → ComplexCellL2} {slice : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice (fun t =>
      cellDualDerivative ⟨fun t _ => G t, v, fun j => (Real.sqrt η : ℂ) * ξ j, 0⟩
        hG V hv.1 hb t (slice t) 0 0)) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
    cellComplexPair (u b) (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellSourceSlice ell b)) =
      Complex.exp (∫ t in a..b, fibreSeriesC (fibreCoefficientSymbol η G v r) ξ t) *
        cellComplexPair (u a) (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellSourceSlice ell a)) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let D := fibreSeriesJet r ξ
  let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
  let q := fun t => cellFiberCLM Complex.conjCLE.toContinuousLinearMap
    (cellScalarCLM (fibreAdjointGraphPhase η Cw hη G hG hv hw ξ b t)
      (cellRawTrace (fibreAdjointGraphRaw η Cw hη G hG hv hw ξ) (-t) + cellConstantCLM 1))
  let phase := Complex.exp (∫ t in a..b, fibreSeriesC (fibreCoefficientSymbol η G v r) ξ t)
  have hR := fibreCoefficientMajorantRadius_pos hCw
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := hξ.trans (by linarith)
  have hg := fibreCoefficientFamily_graph_homogeneous_evolution η Cw hη0 hη hCw G hG
    hv hm hw V hb ξ hξR hab
  have hq := fibreAdjointGraph_backward_homogeneous η Cw hη0 hη hCw G hG
    hv hm hw V hb ξ hξR hab
  have hc := cellWeakAdjointPairing_ratio hab
    ⟨fun t _ => G t, v, fun j => (Real.sqrt η : ℂ) * ξ j, 0⟩ hG V hv hb h hg hq
  dsimp only at hc
  simp only [cellComplexPair_scalar_left, intervalIntegral.integral_same,
    Complex.exp_zero, one_mul] at hc
  have ht := complex_ratio_phase_transport phase (cellComplexPair (u b) (q b))
    (cellComplexPair (cellRawTrace D b + cellConstantCLM 1) (q b))
    (cellComplexPair (u a) (q a))
    (cellComplexPair (cellRawTrace D a + cellConstantCLM 1) (q a)) (Complex.exp_ne_zero _) hc
  change cellComplexPair (u b)
    (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellSourceSlice ell b)) =
    phase * cellComplexPair (u a)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellSourceSlice ell a))
  rw [fibreAdjointRow_pairing_ratio η Cw hη hCw G hG hv hw ξ hξ b b,
    fibreAdjointRow_pairing_ratio η Cw hη hCw G hG hv hw ξ hξ b a]
  exact ht

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! The actual normalized row has a quantitative quiet-future buffer. -/

theorem fibreAdjointRow_quiet_future (η Cw : ℝ) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 1024)
    (s a : ℝ) (ha : 0 ≤ a) (hquiet : ∀ t ∈ Icc s (s + a), ∀ x, v t x = 0) :
    cellL2Norm (fun x =>
      fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ s x - 1) ≤
      ENNReal.ofReal ((8 / fibreCoefficientMajorantRadius Cw) * fibreNorm ξ *
        Real.exp (-(Real.pi ^ 2) * a)) := by
  let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
  let D := fibreAdjointGraphRaw η Cw hη G hG hv hw ξ
  have hR := fibreCoefficientMajorantRadius_pos hCw
  have hξ16 : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16 := by linarith
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := by linarith
  have hnξ : fibreNorm (fun j => -ξ j) ≤ fibreCoefficientMajorantRadius Cw / 1024 := by
    rwa [fibreNorm_neg]
  have hgrev : IsMetricNearIdentity (fun t _ => G (-t)) g := fun t x w => hg (-t) x w
  have hqr : ∀ t ∈ Icc (-s - a) (-s), ∀ x, -v (-t) x = 0 := by
    intro t ht x
    have hti : -t ∈ Icc s (s + a) := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    rw [hquiet (-t) hti x, neg_zero]
  have hbuf := fibreCoefficientFamily_quiet_past η Cw hη hCw (fun t => G (-t))
    (cellMetric_timeReverse hG) hgrev hgsmall (cellDrift_timeReverse hv)
    (cellDrift_timeReverse_scaled_bound hw) (fun j => -ξ j) hnξ (-s) a ha hqr
  dsimp only at hbuf
  change cellL2Norm (cellValue D (-s)) ≤
    ENNReal.ofReal ((2 / fibreCoefficientMajorantRadius Cw) * fibreNorm (fun j => -ξ j) *
      Real.exp (-(2 * Real.pi ^ 2) * a)) at hbuf
  rw [fibreNorm_neg] at hbuf
  have hi := fibreCoefficientFamily_graph_isInverse η Cw hη hCw (fun t => G (-t))
    (cellMetric_timeReverse hG) (cellDrift_timeReverse hv)
    (cellDrift_timeReverse_scaled_bound hw) (fun j => -ξ j) (by rwa [fibreNorm_neg])
  have hraw := cellRawTrace_ae D (-s) (hi.1.2.2.1 (-s) (mem_univ (-s))).1
  rw [cellL2Norm_eq_of_class _ _ hraw] at hbuf
  have hdist := fibreAdjointRow_reverse_distance η Cw hη hCw G hG hv hw ξ hξ16 s
  have hl := (fibreAdjointRowCoefficients_series_memLp_bound η Cw hη hCw G hG hv hw ξ hξ16 s).1
  have hell : (cellSourceSlice ell s - cellConstantCLM 1 : ComplexCellL2) =ᵐ[
      volume.restrict AVenhance.unitCube] (fun x => ell s x - 1) :=
    (Lp.coeFn_sub _ _).trans ((cellSourceSlice_ae ell s hl).sub (cellConstantCLM_ae 1))
  have hcmp : -(2 * Real.pi ^ 2) * a ≤ -(Real.pi ^ 2) * a := by
    have hp := mul_nonneg (sq_nonneg Real.pi) ha
    linarith
  have hfn := fibreNorm_nonneg ξ
  change cellL2Norm (fun x => ell s x - 1) ≤ _
  rw [cellL2Norm_eq_of_class _ _ hell]
  calc
    _ ≤ ENNReal.ofReal (4 * ‖cellRawTrace D (-s)‖) := ENNReal.ofReal_le_ofReal hdist
    _ = 4 * ENNReal.ofReal ‖cellRawTrace D (-s)‖ := by
      rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
    _ ≤ 4 * ENNReal.ofReal ((2 / fibreCoefficientMajorantRadius Cw) * fibreNorm ξ *
        Real.exp (-(2 * Real.pi ^ 2) * a)) := mul_le_mul' le_rfl hbuf
    _ = ENNReal.ofReal ((8 / fibreCoefficientMajorantRadius Cw) * fibreNorm ξ *
        Real.exp (-(2 * Real.pi ^ 2) * a)) := by
      rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hcmp) (by positivity))

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The actual constructed normalized fibre has a forced mean-zero energy bound uniform in interval length. -/

theorem fibreCoefficient_fast_decay (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreWordRadius Cw)
    {a b : ℝ} (hab : a ≤ b) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let D := fibreSeriesJet r ξ
    let lam := fibreSeriesC (fibreCoefficientSymbol η G v r) ξ
    let R := fun t => cellRawTrace D t + cellConstantCLM 1
    ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ),
      CellWeakHilbertCurve a b u slice
        (fun t => cellDualDerivative (fibreCoefficients η G v ξ lam) hG V hv.1 hb t (slice t) 0 (fun _ => 0)) →
      ∀ t ∈ Icc a b,
        ‖u t - cellScalarCLM (cellMean (u t)) (R t)‖ ^ 2 ≤
          Real.exp (-(Real.pi ^ 2 / 2) * (t - a)) *
            ‖u a - cellScalarCLM (cellMean (u a)) (R a)‖ ^ 2 := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let D := fibreSeriesJet r ξ
  let lam := fibreSeriesC (fibreCoefficientSymbol η G v r) ξ
  let R := fun t => cellRawTrace D t + cellConstantCLM 1
  let Rslice := fun t => cellH1Slice D t + cellH1One
  dsimp only
  intro u slice h
  have hR := fibreCoefficientMajorantRadius_pos hCw
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := by
    have ht := (hξ.trans (fibreWordRadius_le_graph Cw)).trans
      (fibreEvolutionRadius_le_majorant (Cw := Cw))
    linarith
  have hsmall := fibreWord_frequency_small hCw ξ hξ
  have hz := fibreCoefficient_projected_remainder η Cw hη0 hη hCw G hG hv hm hw V hb ξ hξR hab
    u slice (fun _ _ => 0) h
  let z := fun t => u t - cellScalarCLM (cellMean (u t)) (R t)
  let zslice := fun t => slice t - cellH1Scalar (cellMean (u t)) (Rslice t)
  have hzero : (0 : ℝ → ℂ) = (fun _ => 0) := by
    funext t
    simp only [Pi.zero_apply]
  have hzcurve : CellWeakHilbertCurve a b z zslice (fun t => cellDualDerivative
      ⟨fun t _ => G t, v, (fun j => (Real.sqrt η : ℂ) * ξ j), 0⟩ hG V hv.1 hb t (zslice t) 0 (fun _ => 0) -
      cellPivotDualCLM (cellScalarCLM (lam t) (torusHkValueCLM (zslice t))) -
      cellPivotDualCLM (cellScalarCLM
        (-Complex.I * cellBlochDriftMeanCLM η Cw hCw hv hw ξ t (torusHkValueCLM (zslice t)) +
          ∑ j : Fin 2, Complex.I * ((Real.sqrt η : ℂ) * ξ j) * cellMean (0 : ComplexCellL2))
        (cellRawTrace D t + cellConstantCLM 1))) := by
    simpa only [z, zslice, R, Rslice, D, r, lam, fibreCoefficients, neg_zero, hzero] using hz.1
  have hρ : ∀ t, ‖cellRawTrace D t‖ ≤ fibreWordCorrectionBound Cw * fibreNorm ξ :=
    fun t => fibreCoefficientFamily_graph_class_correction_bound η Cw hη hCw G hG hv hw ξ hξR t
  have hρsmall : ∀ t, ‖cellRawTrace D t‖ ≤ 1 := fun t => (hρ t).trans hsmall.2.1
  have hlam : ∀ t, ‖lam t‖ ≤ fibreWordSymbolBound Cw * fibreNorm ξ ^ 2 :=
    fun t => fibreCoefficientFamily_word_symbol_bound η Cw hη0 hη hCw G hG hv hw ξ hξR t
  exact cellWeak_projected_feedback_decay hab η Cw hη0 hη hCw G hG hg hgsmall hv hw V hb
    ξ (fibreWordSymbolBound Cw) (fibreWordCorrectionBound Cw) hsmall.2.2 hsmall.1
    (fibreScaledFrequency_coordinate_le η hη ξ) z zslice lam hlam (cellRawTrace D) hρ hρsmall hzcurve
    (fun t _ => hz.2 t)

/-! Separate value and gradient bounds for the actual normalized graph remainder. -/

theorem fibreCoefficient_fast_energy_components (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreWordRadius Cw)
    {a b : ℝ} (hab : a ≤ b) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let D := fibreSeriesJet r ξ
    let lam := fibreSeriesC (fibreCoefficientSymbol η G v r) ξ
    let R := fun t => cellRawTrace D t + cellConstantCLM 1
    let Rslice := fun t => cellH1Slice D t + cellH1One
    ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ) (F : ℝ → Fin 2 → ComplexCellL2),
      (∀ j, MemLp (fun t => F t j) 2 (volume.restrict (Icc a b))) →
      CellWeakHilbertCurve a b u slice
        (fun t => cellDualDerivative (fibreCoefficients η G v ξ lam) hG V hv.1 hb t (slice t) 0 (F t)) →
      let z := fun t => u t - cellScalarCLM (cellMean (u t)) (R t)
      let zslice := fun t => slice t - cellH1Scalar (cellMean (u t)) (Rslice t)
      let B := ‖z a‖ ^ 2 + 14 * ∫ t in a..b, ∑ j, ‖F t j‖ ^ 2
      ‖z b‖ ^ 2 ≤ B ∧
        (Real.pi ^ 2 / 2) * (∫ t in a..b, ‖z t‖ ^ 2) ≤ B ∧
        (1 / 4 : ℝ) * (∫ t in a..b, ∑ j, ‖cellDerivativeCLM j (zslice t)‖ ^ 2) ≤ B := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let D := fibreSeriesJet r ξ
  let lam := fibreSeriesC (fibreCoefficientSymbol η G v r) ξ
  let R := fun t => cellRawTrace D t + cellConstantCLM 1
  let Rslice := fun t => cellH1Slice D t + cellH1One
  dsimp only
  intro u slice F hF h
  have hR := fibreCoefficientMajorantRadius_pos hCw
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := by
    have ht := (hξ.trans (fibreWordRadius_le_graph Cw)).trans
      (fibreEvolutionRadius_le_majorant (Cw := Cw))
    linarith
  have hsmall := fibreWord_frequency_small hCw ξ hξ
  have hz := fibreCoefficient_projected_remainder η Cw hη0 hη hCw G hG hv hm hw V hb ξ hξR hab
    u slice F h
  let z := fun t => u t - cellScalarCLM (cellMean (u t)) (R t)
  let zslice := fun t => slice t - cellH1Scalar (cellMean (u t)) (Rslice t)
  have hzero : (0 : ℝ → ℂ) = (fun _ => 0) := by
    funext t
    simp only [Pi.zero_apply]
  have hzcurve : CellWeakHilbertCurve a b z zslice (fun t => cellDualDerivative
      ⟨fun t _ => G t, v, (fun j => (Real.sqrt η : ℂ) * ξ j), 0⟩ hG V hv.1 hb t (zslice t) 0 (F t) -
      cellPivotDualCLM (cellScalarCLM (lam t) (torusHkValueCLM (zslice t))) -
      cellPivotDualCLM (cellScalarCLM
        (-Complex.I * cellBlochDriftMeanCLM η Cw hCw hv hw ξ t (torusHkValueCLM (zslice t)) +
          ∑ j : Fin 2, Complex.I * ((Real.sqrt η : ℂ) * ξ j) * cellMean (F t j))
        (cellRawTrace D t + cellConstantCLM 1))) := by
    simpa only [z, zslice, R, Rslice, D, r, lam, fibreCoefficients, neg_zero, hzero] using hz.1
  have hρ : ∀ t, ‖cellRawTrace D t‖ ≤ fibreWordCorrectionBound Cw * fibreNorm ξ :=
    fun t => fibreCoefficientFamily_graph_class_correction_bound η Cw hη hCw G hG hv hw ξ hξR t
  have hρsmall : ∀ t, ‖cellRawTrace D t‖ ≤ 1 := fun t => (hρ t).trans hsmall.2.1
  have hlam : ∀ t, ‖lam t‖ ≤ fibreWordSymbolBound Cw * fibreNorm ξ ^ 2 :=
    fun t => fibreCoefficientFamily_word_symbol_bound η Cw hη0 hη hCw G hG hv hw ξ hξR t
  exact cellWeak_projected_feedback_energy_components hab η Cw hη0 hη hCw G hG hg hgsmall hv hw V hb
    ξ (fibreWordSymbolBound Cw) (fibreWordCorrectionBound Cw) hsmall.2.2 hsmall.1
    (fibreScaledFrequency_coordinate_le η hη ξ) z zslice lam hlam (cellRawTrace D) hρ hρsmall F hF hzcurve
    (fun t _ => hz.2 t)

/-! The homogeneous normalized scalar mean is bounded uniformly in interval length. -/

theorem fibreCoefficient_homogeneous_mean_bound (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreWordRadius Cw)
    {a b : ℝ} (hab : a ≤ b) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let D := fibreSeriesJet r ξ
    let lam := fibreSeriesC (fibreCoefficientSymbol η G v r) ξ
    let R := fun t => cellRawTrace D t + cellConstantCLM 1
    ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ),
      CellWeakHilbertCurve a b u slice
        (fun t => cellDualDerivative (fibreCoefficients η G v ξ lam) hG V hv.1 hb t (slice t) 0 (fun _ => 0)) →
      ‖cellMean (u b)‖ ≤ ‖cellMean (u a)‖ +
        (4 * Cw * fibreNorm ξ / Real.pi ^ 2) *
          ‖u a - cellScalarCLM (cellMean (u a)) (R a)‖ := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let D := fibreSeriesJet r ξ
  let lam := fibreSeriesC (fibreCoefficientSymbol η G v r) ξ
  let R := fun t => cellRawTrace D t + cellConstantCLM 1
  dsimp only
  intro u slice h
  let z := fun t => u t - cellScalarCLM (cellMean (u t)) (R t)
  have hdecay := fibreCoefficient_fast_decay η Cw hη0 hη hCw G hG hg hgsmall hv hm hw V hb ξ hξ hab
    u slice h
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := by
    have ht := (hξ.trans (fibreWordRadius_le_graph Cw)).trans
      (fibreEvolutionRadius_le_majorant (Cw := Cw))
    have hp := fibreCoefficientMajorantRadius_pos hCw
    linarith
  have hinc := fibreCoefficient_normalized_mean_increment η Cw hη0 hη hCw G hG hv hm hw V hb
    ξ hξR hab u slice (fun _ _ => 0) h a ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩ hab
  have hzero : cellMean (0 : ComplexCellL2) = 0 := by
    rw [← cellMeanCLM_apply (0 : ComplexCellL2), map_zero]
  simp only [hzero, mul_zero, Finset.sum_const_zero, add_zero] at hinc
  let f := fun t => -Complex.I * cellBlochDriftMeanCLM η Cw hCw hv hw ξ t (z t)
  have hp : 0 < Real.pi ^ 2 / 4 := by positivity
  have hf : ∀ᵐ t ∂volume.restrict (Icc a b),
      ‖f t‖ ≤ (Cw * fibreNorm ξ * ‖z a‖) * Real.exp (-(Real.pi ^ 2 / 4) * (t - a)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hd := norm_bound_of_squared_exponential (z t) (z a) (Real.pi ^ 2 / 2) (t - a)
      (hdecay t ht)
    rw [show -(Real.pi ^ 2 / 2) * (t - a) / 2 = -(Real.pi ^ 2 / 4) * (t - a) by ring] at hd
    dsimp only [f]
    simp only [norm_mul, norm_neg, Complex.norm_I, one_mul]
    calc
      _ ≤ Cw * fibreNorm ξ * ‖z t‖ :=
        cellBlochDriftMeanCLM_norm_le η Cw hCw hv hw ξ t (z t)
      _ ≤ Cw * fibreNorm ξ * (Real.exp (-(Real.pi ^ 2 / 4) * (t - a)) * ‖z a‖) :=
        mul_le_mul_of_nonneg_left hd (mul_nonneg hCw (fibreNorm_nonneg ξ))
      _ = _ := by ring
  have hi := decay_derivative_integral_norm_bound hab hp
    (mul_nonneg (mul_nonneg hCw (fibreNorm_nonneg ξ)) (norm_nonneg (z a))) f hf
  change cellMean (u b) - cellMean (u a) = ∫ t in a..b, f t at hinc
  calc
    ‖cellMean (u b)‖ ≤ ‖cellMean (u a)‖ + ‖cellMean (u b) - cellMean (u a)‖ := by
      simpa only [add_sub_cancel] using norm_add_le (cellMean (u a)) (cellMean (u b) - cellMean (u a))
    _ ≤ ‖cellMean (u a)‖ + (Cw * fibreNorm ξ * ‖z a‖) / (Real.pi ^ 2 / 4) := by
      rw [hinc]
      exact add_le_add le_rfl hi
    _ = _ := by dsimp only [z]; ring

/-! The actual normalized homogeneous solution has a value bound uniform in interval length. -/

theorem fibreCoefficient_homogeneous_value_bound (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreWordRadius Cw)
    {a b : ℝ} (hab : a ≤ b) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreSeriesC (fibreCoefficientSymbol η G v r) ξ
    ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ),
      CellWeakHilbertCurve a b u slice
        (fun t => cellDualDerivative (fibreCoefficients η G v ξ lam) hG V hv.1 hb t (slice t) 0 (fun _ => 0)) →
      ‖u b‖ ≤ (5 + 24 * Cw / Real.pi ^ 2) * ‖u a‖ := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let D := fibreSeriesJet r ξ
  let lam := fibreSeriesC (fibreCoefficientSymbol η G v r) ξ
  let R := fun t => cellRawTrace D t + cellConstantCLM 1
  dsimp only
  intro u slice h
  let z := fun t => u t - cellScalarCLM (cellMean (u t)) (R t)
  have hfn := fibreNorm_nonneg ξ
  have hsmall := fibreWord_frequency_small hCw ξ hξ
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := by
    have ht := (hξ.trans (fibreWordRadius_le_graph Cw)).trans
      (fibreEvolutionRadius_le_majorant (Cw := Cw))
    have hp := fibreCoefficientMajorantRadius_pos hCw
    linarith
  have hRnorm : ∀ t, ‖R t‖ ≤ 2 := by
    intro t
    have hr := fibreCoefficientFamily_graph_class_correction_bound η Cw hη hCw G hG hv hw ξ hξR t
    change ‖cellRawTrace D t‖ ≤ fibreWordCorrectionBound Cw * fibreNorm ξ at hr
    have hrsmall := hr.trans hsmall.2.1
    calc
      ‖R t‖ ≤ ‖cellRawTrace D t‖ + ‖cellConstantCLM 1‖ := norm_add_le _ _
      _ ≤ 2 := by rw [cellConstantCLM_norm, norm_one]; linarith
  have hA : ‖cellMean (u a)‖ ≤ ‖u a‖ := by
    rw [← cellMeanCLM_apply (u a)]
    exact cellMeanCLM_norm_le _
  have hza : ‖z a‖ ≤ 3 * ‖u a‖ := by
    calc
      _ ≤ ‖u a‖ + ‖cellScalarCLM (cellMean (u a)) (R a)‖ := norm_sub_le _ _
      _ = ‖u a‖ + ‖cellMean (u a)‖ * ‖R a‖ := by rw [cellScalarCLM_norm]
      _ ≤ ‖u a‖ + ‖u a‖ * 2 := by gcongr; exact hRnorm a
      _ = _ := by ring
  have hd := fibreCoefficient_fast_decay η Cw hη0 hη hCw G hG hg hgsmall hv hm hw V hb ξ hξ hab
    u slice h b ⟨hab, le_rfl⟩
  have hzb := norm_bound_of_squared_exponential (z b) (z a) (Real.pi ^ 2 / 2) (b - a) hd
  have hexp : Real.exp (-(Real.pi ^ 2 / 2) * (b - a) / 2) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    apply div_nonpos_of_nonpos_of_nonneg
    · exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (sub_nonneg.mpr hab)
    · norm_num
  have hzb' : ‖z b‖ ≤ ‖z a‖ := hzb.trans (by
    simpa only [one_mul] using (mul_le_mul_of_nonneg_right hexp (norm_nonneg (z a))))
  have hmean := fibreCoefficient_homogeneous_mean_bound η Cw hη0 hη hCw G hG hg hgsmall hv hm hw
    V hb ξ hξ hab u slice h
  have hα : 0 ≤ 4 * Cw * fibreNorm ξ / Real.pi ^ 2 := by positivity
  have hαbound : 4 * Cw * fibreNorm ξ / Real.pi ^ 2 ≤ 4 * Cw / Real.pi ^ 2 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hsmall.1 (by positivity : 0 ≤ 4 * Cw)
  calc
    ‖u b‖ = ‖cellScalarCLM (cellMean (u b)) (R b) + z b‖ := by congr 1; dsimp only [z]; abel
    _ ≤ ‖cellScalarCLM (cellMean (u b)) (R b)‖ + ‖z b‖ := norm_add_le _ _
    _ = ‖cellMean (u b)‖ * ‖R b‖ + ‖z b‖ := by rw [cellScalarCLM_norm]
    _ ≤ (‖cellMean (u a)‖ + (4 * Cw * fibreNorm ξ / Real.pi ^ 2) * ‖z a‖) * 2 + ‖z a‖ := by
      exact add_le_add (mul_le_mul hmean (hRnorm b) (norm_nonneg _) (by positivity)) hzb'
    _ ≤ (‖u a‖ + (4 * Cw / Real.pi ^ 2) * (3 * ‖u a‖)) * 2 + 3 * ‖u a‖ := by
      gcongr
    _ = _ := by ring

/-! The normalized zero-trace forced solution has the sharper linear amplitude bound. -/

theorem fibreCoefficient_forced_value_bound (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreWordRadius Cw)
    {a b : ℝ} (hab : a ≤ b) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreSeriesC (fibreCoefficientSymbol η G v r) ξ
    ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ) (F : ℝ → Fin 2 → ComplexCellL2),
      (∀ j, MemLp (fun t => F t j) 2 (volume.restrict (Icc a b))) →
      CellWeakHilbertCurve a b u slice
        (fun t => cellDualDerivative (fibreCoefficients η G v ξ lam) hG V hv.1 hb t (slice t) 0 (F t)) →
      u a = 0 →
      ‖u b‖ ≤ (Real.sqrt 14 + 2 * (Cw * Real.sqrt (28 / Real.pi ^ 2) + 2) *
        fibreNorm ξ * Real.sqrt (b - a)) * Real.sqrt (∫ t in a..b, ∑ j, ‖F t j‖ ^ 2) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let D := fibreSeriesJet r ξ
  let lam := fibreSeriesC (fibreCoefficientSymbol η G v r) ξ
  let R := fun t => cellRawTrace D t + cellConstantCLM 1
  dsimp only
  intro u slice F hF h hu0
  let z := fun t => u t - cellScalarCLM (cellMean (u t)) (R t)
  let Q := ∫ t in a..b, ∑ j, ‖F t j‖ ^ 2
  have hQ : 0 ≤ Q := intervalIntegral.integral_nonneg hab
    (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hfn := fibreNorm_nonneg ξ
  have hsmall := fibreWord_frequency_small hCw ξ hξ
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := by
    have ht := (hξ.trans (fibreWordRadius_le_graph Cw)).trans
      (fibreEvolutionRadius_le_majorant (Cw := Cw))
    have hp := fibreCoefficientMajorantRadius_pos hCw
    linarith
  have hzero : cellMean (0 : ComplexCellL2) = 0 := by
    rw [← cellMeanCLM_apply (0 : ComplexCellL2), map_zero]
  have hz0 : z a = 0 := by
    dsimp only [z]
    rw [hu0, hzero, cellScalarCLM_smul, zero_smul, sub_zero]
  have henergy := fibreCoefficient_fast_energy_components η Cw hη0 hη hCw G hG hg hgsmall hv hm hw
    V hb ξ hξ hab u slice F hF h
  dsimp only at henergy
  change ‖z b‖ ^ 2 ≤ ‖z a‖ ^ 2 + 14 * Q ∧
    (Real.pi ^ 2 / 2) * (∫ t in a..b, ‖z t‖ ^ 2) ≤ ‖z a‖ ^ 2 + 14 * Q ∧ _ at henergy
  rw [hz0, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at henergy
  have hzb : ‖z b‖ ≤ Real.sqrt 14 * Real.sqrt Q := by
    calc
      _ = Real.sqrt (‖z b‖ ^ 2) := by rw [Real.sqrt_sq_eq_abs, abs_norm]
      _ ≤ Real.sqrt (14 * Q) := Real.sqrt_le_sqrt henergy.1
      _ = _ := Real.sqrt_mul (by norm_num) Q
  have hmass : (∫ t in a..b, ‖z t‖ ^ 2) ≤ (28 / Real.pi ^ 2) * Q := by
    have hc : 0 < Real.pi ^ 2 / 2 := by positivity
    have he : (∫ t in a..b, ‖z t‖ ^ 2) ≤ 14 * Q / (Real.pi ^ 2 / 2) :=
      (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using henergy.2.1)
    exact he.trans_eq (by ring)
  have hmroot : Real.sqrt (∫ t in a..b, ‖z t‖ ^ 2) ≤
      Real.sqrt (28 / Real.pi ^ 2) * Real.sqrt Q := by
    exact (Real.sqrt_le_sqrt hmass).trans_eq (Real.sqrt_mul (by positivity) Q)
  have hFint (j : Fin 2) := cellTime_normSq_intervalIntegrable hab (hF j)
  have hsumint : IntervalIntegrable (fun t => ∑ j, ‖F t j‖ ^ 2) volume a b := by
    simpa only [Fin.sum_univ_two, Pi.add_apply] using (hFint 0).add (hFint 1)
  have hFroot (j : Fin 2) : Real.sqrt (∫ t in a..b, ‖F t j‖ ^ 2) ≤ Real.sqrt Q := by
    apply Real.sqrt_le_sqrt
    exact intervalIntegral.integral_mono_on hab (hFint j) hsumint (fun t _ =>
      Finset.single_le_sum (f := fun k : Fin 2 => ‖F t k‖ ^ 2)
        (fun k _ => sq_nonneg ‖F t k‖) (Finset.mem_univ j))
  have hmean := fibreCoefficient_forced_mean_bound η Cw hη0 hη hCw G hG hv hm hw V hb ξ hξ hab
    u slice F hF h
  dsimp only at hmean
  rw [hu0, hzero, norm_zero, zero_add] at hmean
  have hmean' : ‖cellMean (u b)‖ ≤ fibreNorm ξ * Real.sqrt (b - a) *
      (Cw * Real.sqrt (28 / Real.pi ^ 2) + 2) * Real.sqrt Q := by
    apply hmean.trans
    calc
      _ ≤ fibreNorm ξ * Real.sqrt (b - a) *
          (Cw * (Real.sqrt (28 / Real.pi ^ 2) * Real.sqrt Q) + Real.sqrt Q + Real.sqrt Q) := by
        exact mul_le_mul_of_nonneg_left (add_le_add
          (add_le_add (mul_le_mul_of_nonneg_left hmroot hCw) (hFroot 0)) (hFroot 1))
          (mul_nonneg hfn (Real.sqrt_nonneg _))
      _ = _ := by ring
  have hRnorm : ‖R b‖ ≤ 2 := by
    have hr := fibreCoefficientFamily_graph_class_correction_bound η Cw hη hCw G hG hv hw ξ hξR b
    change ‖cellRawTrace D b‖ ≤ fibreWordCorrectionBound Cw * fibreNorm ξ at hr
    have hrsmall := hr.trans hsmall.2.1
    calc
      ‖R b‖ ≤ ‖cellRawTrace D b‖ + ‖cellConstantCLM 1‖ := norm_add_le _ _
      _ ≤ 2 := by rw [cellConstantCLM_norm, norm_one]; linarith
  calc
    ‖u b‖ = ‖cellScalarCLM (cellMean (u b)) (R b) + z b‖ := by congr 1; dsimp only [z]; abel
    _ ≤ ‖cellScalarCLM (cellMean (u b)) (R b)‖ + ‖z b‖ := norm_add_le _ _
    _ = ‖cellMean (u b)‖ * ‖R b‖ + ‖z b‖ := by rw [cellScalarCLM_norm]
    _ ≤ (fibreNorm ξ * Real.sqrt (b - a) * (Cw * Real.sqrt (28 / Real.pi ^ 2) + 2) * Real.sqrt Q) * 2 +
        Real.sqrt 14 * Real.sqrt Q :=
      add_le_add (mul_le_mul hmean' hRnorm (norm_nonneg _) (by positivity)) hzb
    _ = _ := by dsimp only [Q]; ring

/-! The actual normalized homogeneous solution has a value bound uniform in interval length. -/

theorem fibreCoefficient_homogeneous_uniform_value_bound (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreWordRadius Cw)
    {a b : ℝ} (_hab : a ≤ b) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreSeriesC (fibreCoefficientSymbol η G v r) ξ
    ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ),
      CellWeakHilbertCurve a b u slice
        (fun t => cellDualDerivative (fibreCoefficients η G v ξ lam) hG V hv.1 hb t (slice t) 0 (fun _ => 0)) →
      ∀ t ∈ Icc a b, ‖u t‖ ≤ (5 + 24 * Cw / Real.pi ^ 2) * ‖u a‖ := by
  dsimp only
  intro u slice h t ht
  exact fibreCoefficient_homogeneous_value_bound η Cw hη0 hη hCw G hG hg hgsmall hv hm hw
    V hb ξ hξ ht.1 u slice (h.mono (Icc_subset_Icc le_rfl ht.2))

/-! Uniform amplitude control of the normalized forced solution on its entire time interval. -/

theorem fibreCoefficient_forced_uniform_value_bound (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreWordRadius Cw)
    {a b : ℝ} (hab : a ≤ b) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreSeriesC (fibreCoefficientSymbol η G v r) ξ
    ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ) (F : ℝ → Fin 2 → ComplexCellL2),
      (∀ j, MemLp (fun t => F t j) 2 (volume.restrict (Icc a b))) →
      CellWeakHilbertCurve a b u slice
        (fun t => cellDualDerivative (fibreCoefficients η G v ξ lam) hG V hv.1 hb t (slice t) 0 (F t)) →
      u a = 0 →
      ∀ t ∈ Icc a b, ‖u t‖ ≤ (Real.sqrt 14 + 2 * (Cw * Real.sqrt (28 / Real.pi ^ 2) + 2) *
        fibreNorm ξ * Real.sqrt (b - a)) * Real.sqrt (∫ τ in a..b, ∑ j, ‖F τ j‖ ^ 2) := by
  dsimp only
  intro u slice F hF h hu0 t ht
  have hfn := fibreNorm_nonneg ξ
  have hFint (j : Fin 2) := cellTime_normSq_intervalIntegrable hab (hF j)
  have hsumint : IntervalIntegrable (fun τ => ∑ j, ‖F τ j‖ ^ 2) volume a b := by
    simpa only [Fin.sum_univ_two, Pi.add_apply] using (hFint 0).add (hFint 1)
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  have hFt (j : Fin 2) : MemLp (fun τ => F τ j) 2 (volume.restrict (Icc a t)) :=
    (hF j).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hvbound := fibreCoefficient_forced_value_bound η Cw hη0 hη hCw G hG hg hgsmall hv hm hw
    V hb ξ hξ ht.1 u slice F hFt (h.mono hsub) hu0
  have hQ := intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
    (Filter.Eventually.of_forall (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))) hsumint
  have hroot := Real.sqrt_le_sqrt hQ
  have htime := Real.sqrt_le_sqrt (sub_le_sub_right ht.2 a)
  apply hvbound.trans
  apply mul_le_mul
  · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left htime (by positivity))
  · exact hroot
  · exact Real.sqrt_nonneg _
  · positivity

/-! Reconstruction gives the polynomial finite-time forced gradient budget. -/

theorem fibreCoefficient_forced_gradient_bound (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreWordRadius Cw)
    {a b : ℝ} (hab : a ≤ b) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreSeriesC (fibreCoefficientSymbol η G v r) ξ
    ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ) (F : ℝ → Fin 2 → ComplexCellL2),
      (∀ j, MemLp (fun t => F t j) 2 (volume.restrict (Icc a b))) →
      CellWeakHilbertCurve a b u slice
        (fun t => cellDualDerivative (fibreCoefficients η G v ξ lam) hG V hv.1 hb t (slice t) 0 (F t)) →
      u a = 0 →
      (∫ t in a..b, ∑ j, ‖cellDerivativeCLM j (slice t)‖ ^ 2) ≤
        (112 + 8 * (b - a + 1) * (fibreNorm ξ / fibreCoefficientMajorantRadius Cw) ^ 2 *
          (Real.sqrt 14 + 2 * (Cw * Real.sqrt (28 / Real.pi ^ 2) + 2) *
            fibreNorm ξ * Real.sqrt (b - a)) ^ 2) * (∫ t in a..b, ∑ j, ‖F t j‖ ^ 2) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let D := fibreSeriesJet r ξ
  let lam := fibreSeriesC (fibreCoefficientSymbol η G v r) ξ
  let R := fun t => cellRawTrace D t + cellConstantCLM 1
  dsimp only
  intro u slice F hF h hu0
  let z := fun t => u t - cellScalarCLM (cellMean (u t)) (R t)
  let Q := ∫ t in a..b, ∑ j, ‖F t j‖ ^ 2
  let Cf := Real.sqrt 14 + 2 * (Cw * Real.sqrt (28 / Real.pi ^ 2) + 2) *
    fibreNorm ξ * Real.sqrt (b - a)
  have hQ : 0 ≤ Q := intervalIntegral.integral_nonneg hab
    (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hfn := fibreNorm_nonneg ξ
  have hCf : 0 ≤ Cf := by dsimp only [Cf]; positivity
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := by
    have ht := (hξ.trans (fibreWordRadius_le_graph Cw)).trans
      (fibreEvolutionRadius_le_majorant (Cw := Cw))
    have hp := fibreCoefficientMajorantRadius_pos hCw
    linarith
  have hmean : ∀ t ∈ Icc a b, ‖cellMean (u t)‖ ≤ Cf * Real.sqrt Q := by
    intro t ht
    have hvnorm := fibreCoefficient_forced_uniform_value_bound η Cw hη0 hη hCw G hG hg hgsmall
      hv hm hw V hb ξ hξ hab u slice F hF h hu0 t ht
    have hmnorm : ‖cellMean (u t)‖ ≤ ‖u t‖ := by
      rw [← cellMeanCLM_apply (u t)]
      exact cellMeanCLM_norm_le (u t)
    exact hmnorm.trans hvnorm
  have hinv := fibreCoefficientFamily_graph_isInverse η Cw hη hCw G hG hv hw ξ hξR
  have hsol := cellSolution_restrict (Set.subset_univ (Icc a b)) Set.ordConnected_Icc hinv.1
  have hρ := cellSolution_slice_memLp hab hsol
  have hz := (fibreCoefficient_projected_remainder η Cw hη0 hη hCw G hG hv hm hw V hb
    ξ hξR hab u slice F h).1
  have hsplit := cellMeanRemainder_gradient_integral_le hab slice (cellH1Slice D)
    (fun t => cellMean (u t)) (Cf * Real.sqrt Q) (mul_nonneg hCf (Real.sqrt_nonneg _)) hmean h.state hρ hz.state
  have hzero : cellMean (0 : ComplexCellL2) = 0 := by
    rw [← cellMeanCLM_apply (0 : ComplexCellL2), map_zero]
  have hz0 : z a = 0 := by
    dsimp only [z]
    rw [hu0, hzero, cellScalarCLM_smul, zero_smul, sub_zero]
  have henergy := fibreCoefficient_fast_energy_components η Cw hη0 hη hCw G hG hg hgsmall hv hm hw
    V hb ξ hξ hab u slice F hF h
  dsimp only at henergy
  have hfast : (∫ t in a..b, ∑ j, ‖cellDerivativeCLM j
      (slice t - cellH1Scalar (cellMean (u t)) (cellH1Slice D t + cellH1One))‖ ^ 2) ≤ 56 * Q := by
    have he := henergy.2.2
    change (1 / 4 : ℝ) * (∫ t in a..b, ∑ j, ‖cellDerivativeCLM j
      (slice t - cellH1Scalar (cellMean (u t)) (cellH1Slice D t + cellH1One))‖ ^ 2) ≤ ‖z a‖ ^ 2 + 14 * Q at he
    rw [hz0, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at he
    linarith
  have hgraph := fibreCoefficientFamily_finite_hilbert_gradient η Cw hη hCw G hG hv hw ξ hξR hab
  calc
    _ ≤ 2 * (Cf * Real.sqrt Q) ^ 2 * (∫ t in a..b, ∑ j, ‖cellDerivativeCLM j (cellH1Slice D t)‖ ^ 2) +
        2 * ∫ t in a..b, ∑ j, ‖cellDerivativeCLM j
          (slice t - cellH1Scalar (cellMean (u t)) (cellH1Slice D t + cellH1One))‖ ^ 2 := hsplit
    _ ≤ 2 * (Cf * Real.sqrt Q) ^ 2 * (4 * (b - a + 1) *
          (fibreNorm ξ / fibreCoefficientMajorantRadius Cw) ^ 2) + 2 * (56 * Q) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hgraph (by positivity))
        (mul_le_mul_of_nonneg_left hfast (by norm_num))
    _ = _ := by rw [mul_pow, Real.sq_sqrt hQ]; dsimp only [Cf, Q]; ring

end AVRegularity.CycleEvolution
end
