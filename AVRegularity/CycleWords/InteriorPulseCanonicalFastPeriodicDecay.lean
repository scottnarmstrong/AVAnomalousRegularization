-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.ConstructedCanonicalRowPeriodicRepresentative
import AVRegularity.CycleWords.ConstructedCanonicalFastRoughSmoothing
import AVRegularity.CycleWords.ConstructedRawFastPeriodicDecayPrice
public import AVRegularity.CycleWords.ConstructedReflectedFibreGraphNativeLinearGain
import AVRegularity.CycleWords.ConstructedScalarFibreConstants
import AVRegularity.CycleWords.InteriorPulseReflectedActualWeakAllNativeOrders
import AVRegularity.CycleEvolution.CellEnergySpaceRawJetCauchyBound
import AVRegularity.CycleWords.FibreGraphNativeSeries
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped NNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! The actual canonical normalized row has polynomial native higher linear-frequency bounds. -/

theorem interiorPulseCanonicalRow_native_linear_bound
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) {slot : ℤ} (hslot : Odd slot) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot))
    (V : ℝ) (hb : ∀ t x, ∑ j, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x i ^ 2) ≤ Cw)
    (hη0 : 0 ≤ ν / ocMeanFlux α q Λ ζ m ν)
    (hη : ν / ocMeanFlux α q Λ ζ m ν ≤ 1)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j : ℂ)) = 0)
    (ρ : ℝ≥0) (hρ : 0 < ρ)
    (hband : fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ)) < fibreCoefficientMajorantRadius Cw)
    (t : ℝ) (J : ℕ) (ξ : Fin 2 → ℂ)
    (hξ : ξ ∈ Metric.ball 0 ((ρ : ℝ) / 2))
    (hsmall : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16) :
    ∃ U : TorusHk J ℂ,
      torusHkValueCLM U =
        cellSourceSlice (fibreSeriesFun (fibreAdjointRowCoefficients
          (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw) ξ) t - cellConstantCLM 1 ∧
      ‖U‖ ≤
        (2 * (64 * (Real.sqrt (constructedGraphNativeBaseSquareBudget J
          (fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ))) (fibreCoefficientGraphBound Cw) Cw)
          + ‖torusHigherConstant J 1‖) / (ρ : ℝ)) +
          (2 / fibreCoefficientMajorantRadius Cw) * ‖torusHigherConstant J 1‖) *
        peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ J * fibreNorm ξ := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let r := fibreCoefficientFamily η Cw hη (fun s => G (-s)) (cellMetric_timeReverse hG)
    (cellDrift_timeReverse hv) (cellDrift_timeReverse_scaled_bound hw)
  let lam := fibreCoefficientSymbol η (fun s => G (-s))
    (fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x) r
  have hg := fibreCoefficientFamily_isFibreGraph η Cw hη0 hη hCw (fun s => G (-s))
    (cellMetric_timeReverse hG) (cellDrift_timeReverse hv) (cellDrift_timeReverse_scaled_bound hw)
  have hrad := fibreCoefficientMajorantRadius_pos hCw
  have hCg : 0 ≤ fibreCoefficientGraphBound Cw := by unfold fibreCoefficientGraphBound; positivity
  have hn : (fun i => -ξ i) ∈ Metric.ball 0 ((ρ : ℝ) / 2) := by
    change -ξ ∈ Metric.ball 0 ((ρ : ℝ) / 2)
    simpa only [Metric.mem_ball, dist_zero_right, norm_neg] using hξ
  obtain ⟨U, hU, hbU⟩ := interiorPulseReflectedFibreGraph_native_linear_gain hΛ hζ hν hr
    y₀ hslot hv V hb G hG Cw hCw hw hη0 hη hm
    (fibreCoefficientMajorantRadius Cw) (fibreCoefficientGraphBound Cw) hCg r lam hg
    ρ hρ hband (-t) J (fun i => -ξ i) hn
  rw [fibreNorm_neg] at hbU
  have hbudget : ∀ J R Cg Cw η, constructedReflectedGraphNativeSquareBudget J R Cg Cw η =
      constructedGraphNativeSquareBudget J R Cg Cw η := fun _ _ _ _ _ => rfl
  simp only [hbudget] at hbU
  let B := 64 * (Real.sqrt (constructedGraphNativeBaseSquareBudget J
    (fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ))) (fibreCoefficientGraphBound Cw) Cw)
    + ‖torusHigherConstant J 1‖) / (ρ : ℝ)
  have hbP : ‖U‖ ≤ B * peFactor η ^ J * fibreNorm ξ := by
    apply hbU.trans
    have hp := constructedGraphNativeCorrection_polynomial_price J
      (fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ))) (fibreCoefficientGraphBound Cw) Cw η
    have hh := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 64))
        ρ.coe_nonneg) (fibreNorm_nonneg ξ)
    convert hh using 1
    dsimp only [B]
    ring
  let c := fibreSeriesC (fibreAdjointNormalizationCoefficients η Cw hη G hG hv hw) ξ t
  refine ⟨c • U + (c - 1) • torusHigherConstant J 1, ?_, ?_⟩
  · rw [map_add, torusHigher_complex_value_smul, torusHigher_complex_value_smul,
      torusHigherConstant_value, hU, fibreAdjointRow_source_slice η Cw hη hCw G hG hv hw ξ hsmall t,
      cellScalarCLM_smul]
    change c • cellRawTrace (fibreAdjointGraphRaw η Cw hη G hG hv hw ξ) (-t) +
      (c - 1) • cellConstantCLM 1 = _
    rw [smul_add, sub_smul, one_smul]
    abel
  · exact torusHigher_normalized_correction_norm_le J η (fibreNorm ξ) B
      (2 / fibreCoefficientMajorantRadius Cw) (fibreNorm_nonneg ξ) (by positivity) U hbP c
      (fibreAdjointNormalization_series_norm_le_two η Cw hη hCw G hG hv hw ξ hsmall t)
      (canonicalNormalization_correction_linear_le η Cw hη hCw G hG hv hw ξ hsmall t)

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal NNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! The actual row native price controls any smooth representative's classical Sobolev norm. -/

theorem interiorPulseCanonicalRow_smooth_cellSobolev_bound
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) {slot : ℤ} (hslot : Odd slot) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot))
    (V : ℝ) (hb : ∀ t x, ∑ j, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x i ^ 2) ≤ Cw)
    (hη0 : 0 ≤ ν / ocMeanFlux α q Λ ζ m ν)
    (hη : ν / ocMeanFlux α q Λ ζ m ν ≤ 1)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j : ℂ)) = 0)
    (ρ : ℝ≥0) (hρ : 0 < ρ)
    (hband : fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ)) < fibreCoefficientMajorantRadius Cw)
    (t : ℝ) (J : ℕ) (ξ : Fin 2 → ℂ)
    (hξ : ξ ∈ Metric.ball 0 ((ρ : ℝ) / 2))
    (hsmall : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16)
    (f : Vec 2 → ℂ) (hf : ContDiff ℝ (J : ℕ∞) f)
    (he : f =ᵐ[volume.restrict AVenhance.unitCube]
      (fun x => fibreSeriesFun (fibreAdjointRowCoefficients
        (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw) ξ t x - 1)) :
    cellSobolevNorm J f ≤
      (∑ b ∈ Finset.range (J + 1), (Fintype.card (DerivativeWord2 b) : ℝ≥0∞)) *
      ENNReal.ofReal ((2 * (64 * (Real.sqrt (constructedGraphNativeBaseSquareBudget J
          (fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ))) (fibreCoefficientGraphBound Cw) Cw)
          + ‖torusHigherConstant J 1‖) / (ρ : ℝ)) +
          (2 / fibreCoefficientMajorantRadius Cw) * ‖torusHigherConstant J 1‖) *
        peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ J * fibreNorm ξ) := by
  obtain ⟨U, hU, hbU⟩ := interiorPulseCanonicalRow_native_linear_bound hΛ hζ hν hr y₀ hslot hv V hb
    G hG Cw hCw hw hη0 hη hm ρ hρ hband t J ξ hξ hsmall
  have hmem := (fibreAdjointRowCoefficients_series_memLp_bound
    (ν / ocMeanFlux α q Λ ζ m ν) Cw hη hCw G hG hv hw ξ hsmall t).1
  have hval : (torusHkValueCLM U : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] f := by
    rw [hU]
    have hae : ((cellSourceSlice (fibreSeriesFun (fibreAdjointRowCoefficients
        (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw) ξ) t - cellConstantCLM 1 : ComplexCellL2) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube]
        (fun x => fibreSeriesFun (fibreAdjointRowCoefficients
          (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw) ξ t x - 1) := by
      filter_upwards [Lp.coeFn_sub _ (cellConstantCLM 1),
        cellSourceSlice_ae _ t hmem, cellConstantCLM_ae 1] with x hx hy hz
      rw [hx]
      change (cellSourceSlice _ t : Vec 2 → ℂ) x - (cellConstantCLM 1 : Vec 2 → ℂ) x = _
      rw [hy, hz]
    exact hae.trans he.symm
  apply (torusHigher_smooth_cellSobolevNorm_le U f hf hval).trans
  apply mul_le_mul' le_rfl
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hbU

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Full rough fast smoothing in the literal raw notation, with periodic outputs. -/

theorem constructedRawFast_rough_smoothing (J : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (V : ℝ) (hb : ∀ t x, ∑ j, ocCellDrift α q Λ ζ m ν y₀ t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (R : ℝ) (hR : 0 ≤ R) (hξ : fibreNorm ξ ≤ R)
    (hθ : ∀ i, ‖(Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i‖ ≤ R)
    (hη0 : 0 ≤ ν / ocMeanFlux α q Λ ζ m ν)
    (hη : ν / ocMeanFlux α q Λ ζ m ν ≤ 1)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (ocCellDrift α q Λ ζ m ν y₀ t x j : ℂ)) = 0)
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    (hdisc : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 1024)
    (hfreq : Cw * fibreNorm ξ + 1032 * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2 / 16)
    {a b : ℝ} (hab : a < b)
    (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc a b)
      (fibreCoefficients (ν / ocMeanFlux α q Λ ζ m ν) G
        (ocCellDrift α q Λ ζ m ν y₀) ξ 0) (fun _ _ => 0) (fun _ _ => 0) D)
 :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r
    let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
    let B := Real.exp (6 * Real.pi ^ 2) * constructedGapSmoothingBasePrice J R 0 Cw *
      Real.exp (constructedAllOrderPrice 0 R 0 Cw)
    let C := 13 * ((Real.sqrt B * peFactor η ^ J * Real.exp (-(6 * Real.pi ^ 2) * (b - a) / 2)) *
      (1 + (b - a) ^ (-(J : ℝ) / 2)))
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (⊤ : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      fibreFastPart r lam ell ξ D a b =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm J g₁ ≤
        ((∑ l ∈ Finset.range (J + 1), (Fintype.card (DerivativeWord2 l) : ℝ≥0∞)) *
          ENNReal.ofReal C) * cellL2Norm (cellValue D a) := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r
  let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
  have hraw := cellRawHomogeneous_to_Hilbert hab.le (fun t _ => G t) hG
    (ocCellDrift α q Λ ζ m ν y₀) V hv.1 hb (fun i => (Real.sqrt η : ℂ) * ξ i) D (by
      simpa only [fibreCoefficients, Pi.zero_apply, neg_zero,
        show (fun _ : ℝ => (0 : ℂ)) = 0 from rfl] using hD)
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := constructedCanonicalFast_rough_smoothing
    J hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hg hgsmall
    hdisc hfreq hab (cellRawTrace D) (cellH1Slice D) hraw
  have hrad := fibreCoefficientMajorantRadius_pos hCw
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := by linarith only [hdisc, hrad]
  have hξ16 : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16 := by linarith only [hdisc, hrad]
  have hgraph := fibreCoefficientFamily_graph_isInverse η Cw hη hCw G hG hv hw ξ hξR
  have hrow := (fibreAdjointRowCoefficients_series_memLp_bound η Cw hη hCw G hG hv hw ξ hξ16 a).1
  have he := fibreFast_native_class_ae r lam ell ξ D a b
    (hD.2.2.1 a ⟨le_rfl, hab.le⟩).1 (hD.2.2.1 b ⟨hab.le, le_rfl⟩).1
    (hgraph.1.2.2.1 b (mem_univ b)).1 hrow
  refine ⟨g₁, hg₁, hp₁, he.symm.trans he₁, ?_⟩
  rw [cellL2Norm_eq_of_class _ (cellRawTrace D a)
    (cellRawTrace_ae D a (hD.2.2.1 a ⟨le_rfl, hab.le⟩).1)]
  exact hb₁

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! A native periodic entrance gives a polynomially bounded native fast entrance. -/

theorem interiorPulseCanonicalAdjointFast_entrance_representative (J : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) {slot : ℤ} (hslot : Odd slot) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot))
    (V : ℝ) (hb : ∀ t x, ∑ j, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (R : ℝ) (hR : 0 ≤ R) (hξ : fibreNorm ξ ≤ R)
    (hθ : ∀ i, ‖(Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i‖ ≤ R)
    (hη0 : 0 ≤ ν / ocMeanFlux α q Λ ζ m ν)
    (hη : ν / ocMeanFlux α q Λ ζ m ν ≤ 1)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j : ℂ)) = 0)
    (hdisc : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 1024)
    (g₀ : Vec 2 → ℂ) (hg₀ : ContDiff ℝ (J : ℕ∞) g₀)
    (hp₀ : AVenhance.IsZ2Periodic g₀) (t : ℝ) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
    let initial := finiteSmoothPeriodicHk J g₀ hg₀ hp₀
    let c := cellComplexPair (torusHkValueCLM initial)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap
        (cellRawTrace (fibreSeriesJet r ξ) t + cellConstantCLM 1))
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (J : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      ((torusHkValueCLM initial - cellScalarCLM c (cellSourceSlice ell t) : ComplexCellL2) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm J g₁ ≤
        ((∑ l ∈ Finset.range (J + 1), (Fintype.card (DerivativeWord2 l) : ℝ≥0∞)) *
          ENNReal.ofReal (1 + 3 * (2 * Real.sqrt (constructedReflectedGraphNativeSquareBudget J R
            (fibreCoefficientGraphBound Cw) Cw η))) * (Fintype.card (JetIndex2 J) : ℝ≥0∞)) *
              cellSobolevNorm J g₀ := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let rr := fibreCoefficientFamily η Cw hη (fun s => G (-s)) (cellMetric_timeReverse hG)
    (cellDrift_timeReverse hv) (cellDrift_timeReverse_scaled_bound hw)
  let lam := fibreCoefficientSymbol η (fun s => G (-s))
    (fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x) rr
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
  let k := fibreSeriesC (fibreAdjointNormalizationCoefficients η Cw hη G hG hv hw) ξ t
  let B := constructedReflectedGraphNativeSquareBudget J R (fibreCoefficientGraphBound Cw) Cw η
  have hgraph := fibreCoefficientFamily_isFibreGraph η Cw hη0 hη hCw (fun s => G (-s))
    (cellMetric_timeReverse hG) (cellDrift_timeReverse hv) (cellDrift_timeReverse_scaled_bound hw)
  have hrad := fibreCoefficientMajorantRadius_pos hCw
  have hsmall : fibreNorm (fun i => -ξ i) < fibreCoefficientMajorantRadius Cw := by
    rw [fibreNorm_neg]
    linarith only [hdisc, hrad]
  have h16 : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16 := by linarith only [hdisc, hrad]
  have hdiscR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := by linarith only [hdisc, hrad]
  have hCg : 0 ≤ fibreCoefficientGraphBound Cw := by unfold fibreCoefficientGraphBound; positivity
  have hneg : fibreNorm (fun i => -ξ i) ≤ R := by simpa only [fibreNorm_neg] using hξ
  have hθneg : ∀ i, ‖(Real.sqrt η : ℂ) * -ξ i‖ ≤ R := by
    intro i
    simpa only [mul_neg, norm_neg] using hθ i
  obtain ⟨Rj, hRj, hRjb⟩ := interiorPulseReflectedFibreGraph_uniform_native_orders hΛ hζ hν hr
    y₀ hslot hv V hb G hG Cw hCw hw (fun i => -ξ i) R hR hneg hθneg hη0 hη hm
    (fibreCoefficientMajorantRadius Cw) (fibreCoefficientGraphBound Cw) hCg rr lam
    hgraph hsmall (-t) J
  let Lj := torusHigherScalarCLM J k Rj
  have hLv : torusHkValueCLM Lj = cellSourceSlice ell t := by
    rw [torusHigherScalarCLM_value, hRj]
    exact (fibreAdjointRow_source_slice η Cw hη hCw G hG hv hw ξ h16 t).symm
  have hLb : ‖Lj‖ ≤ 2 * Real.sqrt B := by
    rw [torusHigherScalarCLM_norm]
    exact mul_le_mul
      (fibreAdjointNormalization_series_norm_le_two η Cw hη hCw G hG hv hw ξ h16 t)
      (Real.le_sqrt_of_sq_le hRjb) (norm_nonneg _) (by norm_num)
  let R0 := cellRawTrace (fibreSeriesJet r ξ) t + cellConstantCLM 1
  have hRb : ‖R0‖ ≤ 3 :=
    (fibreCoefficientFamily_graph_mode_norm_bounds η Cw hη hCw G hG hv hw ξ hdiscR t).2
  obtain ⟨f, hf, hpf, hef⟩ := interiorPulseCanonicalRow_exists_periodic_smooth_rep
    hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm h16 t
  have hLRep : (torusHkValueCLM Lj : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] f := by
    rw [hLv]
    have hmem := (fibreAdjointRowCoefficients_series_memLp_bound η Cw hη hCw G hG hv hw ξ h16 t).1
    exact (cellSourceSlice_ae _ t hmem).trans hef.symm
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := torusHigher_periodic_projection_representative J
    g₀ f hg₀ hp₀ (hf.of_le (by simp)) hpf Lj hLRep R0 3 (2 * Real.sqrt B) hRb hLb
  refine ⟨g₁, hg₁, hp₁, ?_, hb₁⟩
  simpa only [hLv] using he₁

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords

theorem constructedRawFast_zero_order_decay
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (V : ℝ) (hb : ∀ t x, ∑ j, ocCellDrift α q Λ ζ m ν y₀ t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (R : ℝ) (hR : 0 ≤ R) (hξ : fibreNorm ξ ≤ R)
    (hθ : ∀ i, ‖(Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i‖ ≤ R)
    (hη0 : 0 ≤ ν / ocMeanFlux α q Λ ζ m ν)
    (hη : ν / ocMeanFlux α q Λ ζ m ν ≤ 1)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (ocCellDrift α q Λ ζ m ν y₀ t x j : ℂ)) = 0)
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    (hdisc : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 1024)
    (hfreq : Cw * fibreNorm ξ + 1032 * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2 / 16)
    {a b : ℝ} (hab : a < b)
    (g₀ : Vec 2 → ℂ) (hg₀ : Continuous g₀)
    (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc a b)
      (fibreCoefficients (ν / ocMeanFlux α q Λ ζ m ν) G
        (ocCellDrift α q Λ ζ m ν y₀) ξ 0) (fun _ _ => 0) (fun _ _ => 0) D)

    (hi : cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] g₀) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r
    let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
    let B := Real.exp (6 * Real.pi ^ 2) * constructedGapSmoothingBasePrice 0 R 0 Cw *
      Real.exp (constructedAllOrderPrice 0 R 0 Cw)
    let C := 13 * ((Real.sqrt B * peFactor η ^ 0 * Real.exp (-(6 * Real.pi ^ 2) * (b - a) / 2)) *
      (1 + (b - a) ^ (-(0 : ℝ) / 2)))
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (⊤ : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      fibreFastPart r lam ell ξ D a b =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm 0 g₁ ≤
        ((∑ l ∈ Finset.range (0 + 1), (Fintype.card (DerivativeWord2 l) : ℝ≥0∞)) *
          ENNReal.ofReal C) * cellSobolevNorm 0 g₀ := by
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := constructedRawFast_rough_smoothing
    0 hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hg hgsmall
    hdisc hfreq hab D hD
  refine ⟨g₁, hg₁, hp₁, he₁, ?_⟩
  rw [cellSobolevNorm_zero_eq g₀ hg₀]
  have hn : cellL2Norm (cellValue D a) = cellL2Norm g₀ := by
    exact eLpNorm_congr_ae hi
  rw [hn] at hb₁
  simpa only [Nat.cast_zero] using hb₁

/-! Full rough fast smoothing in the literal raw notation, with periodic outputs. -/

theorem constructedRawFast_rough_smoothing_price (J : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (V : ℝ) (hb : ∀ t x, ∑ j, ocCellDrift α q Λ ζ m ν y₀ t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (R : ℝ) (hR : 0 ≤ R) (hξ : fibreNorm ξ ≤ R)
    (hθ : ∀ i, ‖(Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i‖ ≤ R)
    (hη0 : 0 ≤ ν / ocMeanFlux α q Λ ζ m ν)
    (hη : ν / ocMeanFlux α q Λ ζ m ν ≤ 1)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (ocCellDrift α q Λ ζ m ν y₀ t x j : ℂ)) = 0)
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    (hdisc : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 1024)
    (hfreq : Cw * fibreNorm ξ + 1032 * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2 / 16)
    {a b : ℝ} (hab : a < b)
    (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc a b)
      (fibreCoefficients (ν / ocMeanFlux α q Λ ζ m ν) G
        (ocCellDrift α q Λ ζ m ν y₀) ξ 0) (fun _ _ => 0) (fun _ _ => 0) D)
 :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r
    let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (J : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      fibreFastPart r lam ell ξ D a b =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm J g₁ ≤
        ENNReal.ofReal (constructedSmoothingPrice J R Cw * peFactor η ^ (2 * J) *
          (1 + (b - a) ^ (-(J : ℝ) / 2)) * Real.exp (-(3 * Real.pi ^ 2) * (b - a))) *
          cellL2Norm (cellValue D a) := by
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := constructedRawFast_rough_smoothing J hΛ hζ hν hr y₀ hv V hb G hG
    Cw hCw hw ξ R hR hξ hθ hη0 hη hm hg hgsmall hdisc hfreq hab D hD
  refine ⟨g₁, hg₁.of_le (by simp), hp₁, he₁, hb₁.trans ?_⟩
  rw [nativeSobolevWordPrice_mul_ofReal]
  apply mul_le_mul_left
  exact ENNReal.ofReal_le_ofReal (constructedSmoothingPrice_bound J R Cw
    (ν / ocMeanFlux α q Λ ζ m ν) (b - a) (sub_nonneg.mpr hab.le))

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleWords

theorem interiorPulseRawAdjointFast_same_time_decay (J : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) {slot : ℤ} (hslot : Odd slot) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot))
    (V : ℝ) (hb : ∀ t x, ∑ j, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (R : ℝ) (hR : 0 ≤ R) (hξ : fibreNorm ξ ≤ R)
    (hθ : ∀ i, ‖(Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i‖ ≤ R)
    (hη0 : 0 ≤ ν / ocMeanFlux α q Λ ζ m ν)
    (hη : ν / ocMeanFlux α q Λ ζ m ν ≤ 1)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j : ℂ)) = 0)
    (hdisc : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 1024)
    (g₀ : Vec 2 → ℂ) (hg₀ : ContDiff ℝ (J : ℕ∞) g₀)
    (hp₀ : AVenhance.IsZ2Periodic g₀) (t : ℝ)
    (D : ℝ → RawJet2 1 ℂ)
    (hD : MemLp (cellValue D (-t)) 2 (volume.restrict AVenhance.unitCube))
    (hi : cellValue D (-t) =ᵐ[volume.restrict AVenhance.unitCube] g₀) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (J : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      fibreAdjointFastPart r lam (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ D t t
        =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm J g₁ ≤
        ((∑ l ∈ Finset.range (J + 1), (Fintype.card (DerivativeWord2 l) : ℝ≥0∞)) *
          ENNReal.ofReal (1 + 3 * (2 * Real.sqrt (constructedReflectedGraphNativeSquareBudget J R
            (fibreCoefficientGraphBound Cw) Cw η))) * (Fintype.card (JetIndex2 J) : ℝ≥0∞)) *
              cellSobolevNorm J g₀ := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r
  let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
  let initial := finiteSmoothPeriodicHk J g₀ hg₀ hp₀
  have hiv : cellRawTrace D (-t) = torusHkValueCLM initial := by
    apply Lp.ext
    exact (cellRawTrace_ae D (-t) hD).trans (hi.trans
      (finiteSmoothPeriodicHk_value_ae J g₀ hg₀ hp₀).symm)
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := interiorPulseCanonicalAdjointFast_entrance_representative J
    hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hdisc g₀ hg₀ hp₀ t
  have hrad := fibreCoefficientMajorantRadius_pos hCw
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := by linarith only [hdisc, hrad]
  have h16 : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16 := by linarith only [hdisc, hrad]
  have hgi := fibreCoefficientFamily_graph_isInverse η Cw hη hCw G hG hv hw ξ hξR
  have hl := (fibreAdjointRowCoefficients_series_memLp_bound η Cw hη hCw G hG hv hw ξ h16 t).1
  have he := fibreAdjointFast_native_class_ae r lam ell ξ D t t hD hD
    (hgi.1.2.2.1 t (mem_univ t)).1 hl
  have he' := he.symm
  simp only [intervalIntegral.integral_same, Complex.exp_zero, cellScalarCLM_smul, one_smul, hiv] at he'
  exact ⟨g₁, hg₁, hp₁, he'.trans he₁, hb₁⟩

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords

theorem constructedRawFast_zero_order_decay_price
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (V : ℝ) (hb : ∀ t x, ∑ j, ocCellDrift α q Λ ζ m ν y₀ t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (R : ℝ) (hR : 0 ≤ R) (hξ : fibreNorm ξ ≤ R)
    (hθ : ∀ i, ‖(Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i‖ ≤ R)
    (hη0 : 0 ≤ ν / ocMeanFlux α q Λ ζ m ν)
    (hη : ν / ocMeanFlux α q Λ ζ m ν ≤ 1)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (ocCellDrift α q Λ ζ m ν y₀ t x j : ℂ)) = 0)
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    (hdisc : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 1024)
    (hfreq : Cw * fibreNorm ξ + 1032 * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2 / 16)
    {a b : ℝ} (hab : a < b)
    (g₀ : Vec 2 → ℂ) (hg₀ : Continuous g₀)
    (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc a b)
      (fibreCoefficients (ν / ocMeanFlux α q Λ ζ m ν) G
        (ocCellDrift α q Λ ζ m ν y₀) ξ 0) (fun _ _ => 0) (fun _ _ => 0) D)

    (hi : cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] g₀) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r
    let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (0 : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      fibreFastPart r lam ell ξ D a b =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm 0 g₁ ≤
        ENNReal.ofReal (constructedForwardDecayPrice 0 R Cw *
          Real.exp (-(3 * Real.pi ^ 2) * (b - a))) * cellSobolevNorm 0 g₀ := by
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := constructedRawFast_zero_order_decay
    hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hg hgsmall
    hdisc hfreq hab g₀ hg₀ D hD hi
  refine ⟨g₁, hg₁.of_le (by simp), hp₁, he₁, hb₁.trans ?_⟩
  rw [nativeSobolevWordPrice_mul_ofReal]
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = constructedForwardZeroDecayPrice R Cw * Real.exp (-(3 * Real.pi ^ 2) * (b - a)) := by
      have hexp : -(6 * Real.pi ^ 2) * (b - a) / 2 = -(3 * Real.pi ^ 2) * (b - a) := by ring
      rw [hexp]
      simp only [pow_zero, mul_one, neg_zero, zero_div, Real.rpow_zero]
      dsimp only [constructedForwardZeroDecayPrice]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (constructedForwardZeroDecayPrice_le 0 R Cw)
      (Real.exp_nonneg _)

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Actual chart renewal bounds for graded Taylor responses, given the
adjoint weights that the construction supplies. -/

theorem geometryError_cover_remainder_from_weights
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (Λ : ℕ) (hΛ : 128 ≤ Λ) (D H K J n Kmax qJ : ℕ) (hD : 2 ≤ D)
    (hK : 1 ≤ K) (hqJ : K + 1 + Kmax ≤ qJ)
    (Cenv CG Cw : ℕ → ℝ) (Cb CT g0 : ℝ) (hg0 : g0 ≤ 1 / 4) :
    ∃ C : ℝ, 1 ≤ C ∧
    ∀ {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
        [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
        [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        (π : ι → ℝ) (_hπ : ∀ x, 0 < π x) (Kslot : ι → ℕ) (_hKslot : ∀ x, Kslot x ≤ Kmax)
        (Φ : ℕ → ℝ → Vec 2 → ℝ) (_hΦ : IsOCStreamSeq α q Λ ζ Φ)
        (M' : ℕ) (κ' : ℕ → ℝ) (_hband : IsOCBandChain α q Λ ζ M' κ')
        (m : ℕ) (_hm2 : 2 ≤ m) (_hmM : m ≤ M') (ν B : ℝ) (_hν : κ' m = ν) (_hB : κ' (m - 1) = B)
        (hφ : IsAdmissibleStream (Φ (m - 1)))
        (ta T ρs g a B₀ lam : ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
        (_cov : IsGeometryCover α q Λ m ζ Φ hφ ν B T ta ρs g g0 a B₀ lam Cb CT qJ Kmax CG l₀ P y₀)
        {P' : Type*} {Ctx : P' → Type*} (Fam : ChartedFamily ι h D P' Ctx)
        (pc : Fin P → P') (ctx : ∀ i, Ctx (pc i)) (dom : Fam.Domain)
        (_hdom : ∀ i : Fin P,
          Set.Icc (ocEll q Λ m ν ^ 2 * ocPieceStart α q Λ m ν ta (l₀ + i))
            (ocEll q Λ m ν ^ 2 * ocPieceEnd α q Λ m ν ta T (l₀ + i)) ×ˢ Set.univ ⊆
              dom (pc i) (ctx i))
        (_hdepth : Fam.HasDepthAtMost H) (_hdesc : Fam.IsDescending Kslot)
        (b : ι → ι → ℝ) (Θ : ℝ) (_hΘ : Θ ≤ 1) (_hb : ∀ x y, 0 ≤ b x y)
        (_hrow : ∀ x, ∑ y, b x y ≤ Θ) (_hcol : ∀ y, ∑ x, b x y ≤ Θ)
        (_henv : IsMolecularEnvelope Fam π Kslot dom ν
          (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) ρs Cenv (K + 1) b)
        (_hmeas : Fam.IsTimeMeasurable)
        (ϖ ζr rstar : ℝ) (_hϖ : ϖ = ocEpsilon q Λ m / Real.sqrt (B * T))
        (_hζr : ζr = Real.sqrt (B * T) / ocEpsilon q Λ (m - 1))
        (_hrstar : rstar = ρs / ocEpsilon q Λ m)
        (F : ∀ x, PlaneHk Set.univ (Kslot x) (h x))
        (_hfinite : (∑ x, ENNReal.ofReal ((π x)⁻¹) *
          weightedFactorialNormSq (n + (J + H + 2) * (K + 1)) ϖ 0 rstar (Kslot x) (F x)) ≠ ⊤)
        (_hweights : ∀ i : Fin P, ∀ N : ℕ, Nonempty (ChartWeights
          (fun t _ => ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ + i) ν
            (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i) t 0)
          (ocCellDrift α q Λ ζ m ν (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i))
          (ta / ocEll q Λ m ν ^ 2) (T / ocEll q Λ m ν ^ 2) ϖ 0 N Cw))
        (fZ : ∀ (_ : Fin P) (_ : Fin (J + 1)) (x : ι), PlaneHk Set.univ (Kslot x) (h x))
        (Z : ∀ (_ : Fin P) (_ : Fin (J + 1)) (x : ι), ℝ → PlaneHk Set.univ (Kslot x) (h x))
        (Zw : ∀ (_ : Fin P) (_ : Fin (J + 1)) (x : ι), ℝ →
          PlaneHk Set.univ (Kslot x + 1) (h x))
        (_hZ : ∀ i : Fin P, IsPlaneChainFrom
          (geometryResponseData J K (ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ + i) ν
            (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i)) 0
            (ocCellFiber Fam q Λ m ν (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i) (pc i) (ctx i))
            ((ocEpsilon q Λ (m - 1))⁻¹ • ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i)
            (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)))
          (fun _ x => Kslot x) (ocPieceStart α q Λ m ν ta (l₀ + i))
          (ocPieceEnd α q Λ m ν ta T (l₀ + i))
          (ocCellDrift α q Λ ζ m ν (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i))
          (fun j x => fZ i j x) (fun _ _ _ => 0) (Z i) (Zw i))
        (_hfZ0 : ∀ i : Fin P, i.val = 0 → ∀ j x, fZ i j x = if j = 0 then F x else 0)
        (_hfZ : ∀ i i' : Fin P, i'.val = i.val + 1 → ∀ j x, planeValue (fZ i' j x) =ᵐ[volume]
          fun z => planeValue (Z i j x (ocPieceEnd α q Λ m ν ta T (l₀ + i)))
            (ocCellTransition α q Λ m (Φ (m - 1)) hφ (l₀ + i)
              (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i)
              (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i') z)),
    ∀ i : Fin P, ∃ V : ∀ x, ℝ → PlaneHk Set.univ (Kslot x) (PiLp 2 (fun _ : Fin 2 => h x)),
      (∀ x, MemLp (V x) 2 (volume.restrict (Set.Icc
        (ocPieceStart α q Λ m ν ta (l₀ + i)) (ocPieceEnd α q Λ m ν ta T (l₀ + i))))) ∧
      (∀ x, ∀ᵐ t ∂volume.restrict (Set.Icc
        (ocPieceStart α q Λ m ν ta (l₀ + i)) (ocPieceEnd α q Λ m ν ta T (l₀ + i))),
        planeValue (V x t) =ᵐ[volume] geometryErrorRemainderFlux Fam J K Kslot (pc i) (ctx i)
          (ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ + i) ν
            (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i))
          (ocEll q Λ m ν ^ 2) (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1))
          ((ocEpsilon q Λ (m - 1))⁻¹ • ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i)
          ((ocEpsilon q Λ m)⁻¹ • ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i)
          (fun j u => Zw i j u t) x t) ∧
      (∑ x, ENNReal.ofReal ((π x)⁻¹) * ∫⁻ t in Set.Icc
        (ocPieceStart α q Λ m ν ta (l₀ + i)) (ocPieceEnd α q Λ m ν ta T (l₀ + i)),
        weightedFactorialNormSq n ϖ 0 rstar (Kslot x) (V x t)) ≤
      ENNReal.ofReal C * (ENNReal.ofReal ((ζr ^ (K + 1)) ^ 2) +
        (ENNReal.ofReal ((g * ζr) ^ 2)) ^ (J + 1)) *
        ∑ x, ENNReal.ofReal ((π x)⁻¹) *
          weightedFactorialNormSq (n + (J + H + 2) * (K + 1)) ϖ 0 rstar (Kslot x) (F x) := by
  classical
  let CGu := fun r => |CG r|
  obtain ⟨Cresp, hCresp, hresponse⟩ := geometryResponse_cover_mass_budget_from_weights
    α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ D H K J (n + (K + 1)) Kmax qJ hD hK hqJ
    Cenv CG Cw Cb CT g0 hg0
  obtain ⟨Cforce, hCforce, hforcing⟩ := geometryError_remainder_from_response_bounds_uniform
    K Kmax J CGu Cenv (fun r => abs_nonneg (CG r)) Cresp hCresp
  refine ⟨Cforce, hCforce, ?_⟩
  intro ι _ h _ _ _ _ _ _ π hπ Kslot hKslot Φ hΦ M' κ' hband m hm2 hmM ν B hν hB hφ
    ta T ρs g a B₀ lam l₀ P y₀ cov P' Ctx Fam pc ctx dom hdom hdepth hdesc
    b Θ hΘ hb hrow hcol henv hmeas ϖ ζr rstar hϖ hζr hrstar F hfinite hweights fZ Z Zw hZ hfZ0 hfZ
  let M := n + (J + H + 2) * (K + 1)
  let Mresp := n + (K + 1) + (J + H) * K
  let Ddata := ∑ x, ENNReal.ofReal ((π x)⁻¹) * weightedFactorialNormSq M ϖ 0 rstar (Kslot x) (F x)
  have hreserve : Mresp ≤ M := by
    have hh : M = Mresp + (J + H + K + 1) := by dsimp [M, Mresp]; ring
    rw [hh]
    omega
  have hdata : (∑ x, ENNReal.ofReal ((π x)⁻¹) *
      weightedFactorialNormSq Mresp ϖ 0 rstar (Kslot x) (F x)) ≤ Ddata :=
    Finset.sum_le_sum (fun x _ => mul_le_mul_right
      (weightedFactorialNormSq_moment_mono hreserve ϖ 0 rstar (Kslot x) (F x)) _)
  have hfiniteR := ne_top_of_le_ne_top hfinite hdata
  have hrb := hresponse π hπ Kslot hKslot Φ hΦ M' κ' hband m hm2 hmM ν B hν hB hφ
    ta T ρs g a B₀ lam l₀ P y₀ cov Fam pc ctx dom hdom hdepth hdesc b Θ hΘ hb hrow hcol
    henv hmeas ϖ ζr rstar hϖ hζr hrstar F hfiniteR hweights fZ Z Zw hZ hfZ0 hfZ
  have hΛ1 : 1 ≤ Λ := by omega
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ1
  have hE := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m - 1) hΛ1
  have hRT : 0 < Real.sqrt (B * T) := Real.sqrt_pos.mpr (mul_pos cov.pos.2.1 cov.pos.2.2.1)
  have hϖpos : 0 < ϖ := by rw [hϖ]; exact div_pos he hRT
  have hζrpos : 0 ≤ ζr := by rw [hζr]; exact (div_pos hRT hE).le
  have hζr1 : ζr ≤ 1 := by rw [hζr]; exact (div_le_one hE).mpr cov.RE
  have hscale : (ρs / ocEpsilon q Λ m) * ϖ ≤ 1 := by
    rw [hϖ, div_mul_div_cancel₀ he.ne']
    exact (div_le_one hRT).mpr cov.rho_R
  have hδ : ocEpsilon q Λ m / ocEpsilon q Λ (m - 1) = ζr * ϖ := by
    rw [hζr, hϖ]
    field_simp
  have hell : 0 < ocEll q Λ m ν ^ 2 := by
    unfold ocEll
    exact sq_pos_of_pos (div_pos he (Real.sqrt_pos.mpr cov.pos.1))
  let left := fun i : Fin P => ocPieceStart α q Λ m ν ta (l₀ + i)
  let right := fun i : Fin P => ocPieceEnd α q Λ m ν ta T (l₀ + i)
  let yc := fun i : Fin P => ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i
  let G := fun i : Fin P => ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ + i) ν (yc i)
  intro i
  have hZlp := fun j x => (hZ i).2.1 (j, x)
  have hbound (j : Fin (J + 1)) (k : ℕ) (hk : k ≤ n + (K + 1)) :
      (∫⁻ t in Set.Icc (left i) (right i), ∑ x, ENNReal.ofReal ((π x)⁻¹) *
        weightedGradFactorialNormSq k ϖ 0 rstar (Kslot x) (Zw i j x t)) ≤
      (ENNReal.ofReal Cresp) ^ (j.val + 1) * (ENNReal.ofReal ((g * ζr) ^ 2)) ^ j.val * Ddata := by
    have hgrad := nativeGradient_mass_le_graded_energy Kslot
      (fun x => responseGrade (n + (K + 1)) J H K j.val (familyDepthRank Fam H x)) k
      (fun x => hk.trans (Nat.le_add_right _ _)) (fun x => ENNReal.ofReal ((π x)⁻¹))
      ϖ rstar (left i) (right i) (Z i j) (Zw i j) (hZlp j)
    exact hgrad.trans ((hrb i j).trans (mul_le_mul_right hdata _))
  have hsub := ocPiece_interval_subset α q Λ m ν ta T (l₀ + i) hell
  have hm : ∀ X k l, Measurable (fun t => G i t X k l) := by
    intro X k l
    exact ((ocCellMetric_joint_contDiff α q Λ m hφ (l₀ + i) ν (yc i) k l).continuous.comp
      (continuous_id.prodMk continuous_const)).measurable
  have hs : ∀ t ∈ Set.Icc (left i) (right i), ∀ k l,
      ContDiff ℝ (K + 1 + Kmax : ℕ) (fun z => G i t z k l) := by
    intro t ht k l
    exact (cov.metric_smooth i t (hsub ht) k l).of_le (by exact_mod_cast hqJ)
  have hj : ∀ᵐ t ∂volume.restrict (Set.Icc (left i) (right i)), ∀ r, K + 1 ≤ r →
      r ≤ K + 1 + Kmax → ∀ y k l,
      ‖iteratedFDeriv ℝ r (fun z => G i t z k l) y‖ ≤ CGu r * g * (ζr * ϖ) ^ r := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    intro r hr hrmax y k l
    rw [← hδ]
    exact (cov.metric_jets i t (hsub ht) y r (by omega) (hrmax.trans hqJ) k l).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self (CG r)) cov.g_range.1)
        (pow_nonneg (div_nonneg he.le hE.le) r))
  have hjt : ∀ᵐ t ∂volume.restrict (Set.Icc (left i) (right i)), ∀ r, 1 ≤ r → r ≤ K → ∀ k l,
      ‖iteratedFDeriv ℝ r (fun z => G i t z k l) 0‖ ≤ CGu r * g * (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)) ^ r := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    intro r hr hrmax k l
    exact (cov.metric_jets i t (hsub ht) 0 r hr (by omega) k l).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self (CG r)) cov.g_range.1)
        (pow_nonneg (div_nonneg he.le hE.le) r))
  have hwin : ∀ t ∈ Set.Icc (left i) (right i), ∀ Y : Vec 2,
      (ocEll q Λ m ν ^ 2 * t, Y) ∈ dom (pc i) (ctx i) := by
    intro t ht Y
    apply hdom i
    exact ⟨⟨mul_le_mul_of_nonneg_left ht.1 hell.le, mul_le_mul_of_nonneg_left ht.2 hell.le⟩, Set.mem_univ Y⟩
  have hf := hforcing Fam π hπ Kslot hKslot hdesc dom ν (ocEpsilon q Λ m)
    (ocEpsilon q Λ (m - 1)) ρs cov.pos.1 he hE cov.pos.2.2.2 (K + 1) b (by omega)
    henv hmeas hb (fun x => (hrow x).trans hΘ) (fun x => (hcol x).trans hΘ)
    (pc i) (ctx i) (ocEll q Λ m ν ^ 2) (left i) (right i) ϖ ζr g hell.ne' hϖpos hscale
    hζrpos hζr1 cov.g_range.1 (by linarith [cov.g_range.2]) hδ
    ((ocEpsilon q Λ (m - 1))⁻¹ • yc i) ((ocEpsilon q Λ m)⁻¹ • yc i)
    hwin (G i) hm hs hj hjt n (Zw i) hZlp Ddata hfinite
    (by simpa only [← hrstar] using fun j => hbound j (n + (K + 1)) le_rfl)
    (by simpa only [Fin.val_last, ← hrstar] using hbound (Fin.last J) (n + K) (by omega))
  simpa only [← hrstar, left, right, G, yc, Ddata, M] using hf

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal NNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

theorem interiorPulseCanonicalRow_coefficients_smooth_series_replacement
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) {slot : ℤ} (hslot : Odd slot) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot))
    (V : ℝ) (hb : ∀ t x, ∑ j, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x i ^ 2) ≤ Cw)
    (hη0 : 0 ≤ ν / ocMeanFlux α q Λ ζ m ν)
    (hη : ν / ocMeanFlux α q Λ ζ m ν ≤ 1)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j : ℂ)) = 0)
    (ρ : ℝ≥0) (hρ : 0 < ρ)
    (hband : fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ)) < fibreCoefficientMajorantRadius Cw) :
    ∃ ell : ℕ × ℕ → ℝ → Vec 2 → ℂ,
      (∀ p t, ContDiff ℝ (⊤ : ℕ∞) (ell p t)) ∧
      (∀ p t, AVenhance.IsZ2Periodic (ell p t)) ∧
      (∀ ξ t, AVenhance.IsZ2Periodic (fibreSeriesFun ell ξ t)) ∧
      (∀ ξ t, ((ρ : ℝ) / 2)⁻¹ * ‖ξ‖ < 1 →
        fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16 →
        ContDiff ℝ (⊤ : ℕ∞) (fibreSeriesFun ell ξ t)) ∧
      (∀ p t, ell p t =ᵐ[volume.restrict AVenhance.unitCube]
        fibreAdjointRowCoefficients (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw p t) := by
  classical
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let r := fibreCoefficientFamily η Cw hη (fun s => G (-s)) (cellMetric_timeReverse hG)
    (cellDrift_timeReverse hv) (cellDrift_timeReverse_scaled_bound hw)
  let lam := fibreCoefficientSymbol η (fun s => G (-s))
    (fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x) r
  have hg := fibreCoefficientFamily_isFibreGraph η Cw hη0 hη hCw (fun s => G (-s))
    (cellMetric_timeReverse hG) (cellDrift_timeReverse hv) (cellDrift_timeReverse_scaled_bound hw)
  have hrad := fibreCoefficientMajorantRadius_pos hCw
  have hCg : 0 ≤ fibreCoefficientGraphBound Cw := by unfold fibreCoefficientGraphBound; positivity
  have hex : ∀ p t, ∃ f : Vec 2 → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧
      AVenhance.IsZ2Periodic f ∧ f =ᵐ[volume.restrict AVenhance.unitCube] cellValue (r p) (-t) := by
    intro p t
    exact interiorPulseReflectedFibreGraph_coefficient_smooth_rep hΛ hζ hν hr y₀ hslot hv V hb G hG
      Cw hCw hw hη0 hη hm (fibreCoefficientMajorantRadius Cw) (fibreCoefficientGraphBound Cw)
      hCg r lam hg ρ hρ hband (-t) p
  choose f hf hp he using hex
  let a := fun p t x => (-1 : ℂ) ^ (p.1 + p.2) * f p t x
  have ha : ∀ p t, ContDiff ℝ (⊤ : ℕ∞) (a p t) := fun p t => contDiff_const.mul (hf p t)
  have hap : ∀ p t, AVenhance.IsZ2Periodic (a p t) := by
    intro p t n x
    dsimp only [a]
    rw [hp p t n x]
  have hae : ∀ p t, a p t =ᵐ[volume.restrict AVenhance.unitCube]
      fibreAdjointCorrectionCoefficients η Cw hη G hG hv hw p t := by
    intro p t
    filter_upwards [he p t] with x hx
    change (-1 : ℂ) ^ (p.1 + p.2) * f p t x =
      (-1 : ℂ) ^ (p.1 + p.2) * cellValue (r p) (-t) x
    rw [hx]
  let k := fibreAdjointNormalizationCoefficients η Cw hη G hG hv hw
  refine ⟨fibreRowCoefficients k a, fibreRowCoefficients_contDiff k a ha,
    fibreRowCoefficients_periodic k a hap, ?_, ?_, ?_⟩
  · exact fibreSeriesFun_periodic _ (fibreRowCoefficients_periodic k a hap)
  · intro ξ t hξ hsmall
    have hkfinite := (fibreAdjointNormalizationCoefficients_weighted_le_two
      η Cw hη hCw G hG hv hw).trans_lt (by norm_num : (2 : ℝ≥0∞) < ⊤)
    have hk := fibreScalarSeries_summable_norm k
      (fibreCoefficientMajorantRadius Cw / 16) hkfinite ξ hsmall t
    apply fibreRowCoefficients_series_contDiff_of_native_coefficients k a t
      (fun p => ha p t) (fun p => hap p t) ((ρ : ℝ) / 2)⁻¹ (by positivity)
      (fun J => Real.sqrt (constructedReflectedGraphNativeSquareBudget J
        (fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ))) (fibreCoefficientGraphBound Cw) Cw η)
        + ‖torusHigherConstant J 1‖) _ ξ hξ hk
    intro J
    obtain ⟨U, hU, hUb⟩ := interiorPulseReflectedFibreGraph_coefficients_native_geometric_bound
      hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw hη0 hη hm
      (fibreCoefficientMajorantRadius Cw) (fibreCoefficientGraphBound Cw) hCg
      r lam hg ρ hρ hband (-t) J
    refine ⟨fun p => (-1 : ℂ) ^ (p.1 + p.2) • U p, ?_, ?_⟩
    · intro p
      rw [torusHigher_complex_value_smul, hU p]
      filter_upwards [he p t, cellRawTrace_ae (r p) (-t)
        (fibreGraphCoefficient_memLp hg ρ hρ hband p (-t)),
        Lp.coeFn_smul ((-1 : ℂ) ^ (p.1 + p.2)) (cellRawTrace (r p) (-t))] with x hx hxU hxsm
      rw [hxsm]
      change (-1 : ℂ) ^ (p.1 + p.2) * f p t x =
        (-1 : ℂ) ^ (p.1 + p.2) * (cellRawTrace (r p) (-t) : Vec 2 → ℂ) x
      rw [hx, hxU]
    · intro p
      simpa only [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul] using hUb p
  · exact fibreRowCoefficients_congr_ae k a _ hae

/-! The actual smooth row satisfies the common scalar jet price. -/

theorem interiorPulseCanonicalRow_scalar_jet_bound
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) {slot : ℤ} (hslot : Odd slot) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot))
    (V : ℝ) (hb : ∀ t x, ∑ j, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x i ^ 2) ≤ Cw)
    (hη0 : 0 ≤ ν / ocMeanFlux α q Λ ζ m ν)
    (hη : ν / ocMeanFlux α q Λ ζ m ν ≤ 1)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j : ℂ)) = 0)
    (ρ : ℝ≥0) (hρ : 0 < ρ)
    (hband : fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ)) < fibreCoefficientMajorantRadius Cw)
    (t : ℝ) (J : ℕ) (ξ : Fin 2 → ℂ)
    (hξ : ξ ∈ Metric.ball 0 ((ρ : ℝ) / 2))
    (hsmall : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16)
    (f : Vec 2 → ℂ) (hf : ContDiff ℝ (J : ℕ∞) f)
    (he : f =ᵐ[volume.restrict AVenhance.unitCube]
      (fun x => fibreSeriesFun (fibreAdjointRowCoefficients
        (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw) ξ t x - 1)) :
    cellSobolevNorm J f ≤
      ENNReal.ofReal (constructedScalarJetPrice J
        (fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ))) Cw (ρ : ℝ) *
        peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ (2 * J) * fibreNorm ξ) := by
  exact (interiorPulseCanonicalRow_smooth_cellSobolev_bound hΛ hζ hν hr y₀ hslot hv V hb
    G hG Cw hCw hw hη0 hη hm ρ hρ hband t J ξ hξ hsmall f hf he).trans
      (constructedRowJetPrice_bound J (fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ)))
        Cw (ρ : ℝ) (ν / ocMeanFlux α q Λ ζ m ν) (fibreNorm ξ) (fibreNorm_nonneg ξ))

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleWords

theorem interiorPulseRawAdjointFast_same_time_decay_price (J : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) {slot : ℤ} (hslot : Odd slot) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot))
    (V : ℝ) (hb : ∀ t x, ∑ j, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (R : ℝ) (hR : 0 ≤ R) (hξ : fibreNorm ξ ≤ R)
    (hθ : ∀ i, ‖(Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i‖ ≤ R)
    (hη0 : 0 ≤ ν / ocMeanFlux α q Λ ζ m ν)
    (hη : ν / ocMeanFlux α q Λ ζ m ν ≤ 1)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j : ℂ)) = 0)
    (hdisc : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 1024)
    (g₀ : Vec 2 → ℂ) (hg₀ : ContDiff ℝ (J : ℕ∞) g₀)
    (hp₀ : AVenhance.IsZ2Periodic g₀) (t : ℝ)
    (D : ℝ → RawJet2 1 ℂ)
    (hD : MemLp (cellValue D (-t)) 2 (volume.restrict AVenhance.unitCube))
    (hi : cellValue D (-t) =ᵐ[volume.restrict AVenhance.unitCube] g₀) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (J : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      fibreAdjointFastPart r lam (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ D t t
        =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm J g₁ ≤
        ENNReal.ofReal (constructedAdjointDecayPrice J R Cw * peFactor η ^ (2 * J)) *
          cellSobolevNorm J g₀ := by
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := interiorPulseRawAdjointFast_same_time_decay J
    hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hdisc
    g₀ hg₀ hp₀ t D hD hi
  have hbudget : ∀ J R Cg Cw η, constructedReflectedGraphNativeSquareBudget J R Cg Cw η =
      constructedGraphNativeSquareBudget J R Cg Cw η := fun _ _ _ _ _ => rfl
  have hmul : ∀ x : ℝ, 3 * (2 * x) = 6 * x := fun x => by ring
  simp only [hbudget, hmul] at hb₁
  refine ⟨g₁, hg₁, hp₁, he₁, hb₁.trans ?_⟩
  rw [nativeSobolevReadoutPrice_ofReal]
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  let η := ν / ocMeanFlux α q Λ ζ m ν
  have hcard : 0 ≤ (Fintype.card (JetIndex2 J) : ℝ) := Nat.cast_nonneg _
  have hpe : 0 ≤ peFactor η ^ (2 * J) := pow_nonneg
    ((by norm_num : (0 : ℝ) ≤ 1).trans (one_le_peFactor η)) _
  calc
    _ ≤ nativeSobolevWordPrice J *
        ((1 + 6 * Real.sqrt (constructedGraphNativeBaseSquareBudget J R
          (fibreCoefficientGraphBound Cw) Cw)) * peFactor η ^ (2 * J)) *
        (Fintype.card (JetIndex2 J) : ℝ) := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (constructedAdjointEntrance_native_price J R Cw η)
            (nativeSobolevWordPrice_nonneg J)) hcard
    _ = constructedAdjointEntrancePrice J R Cw * peFactor η ^ (2 * J) := by
      dsimp only [constructedAdjointEntrancePrice]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (constructedAdjointEntrancePrice_le J R Cw) hpe

/-! Full two-orientation fast decay with a periodic entrance and periodic output. -/

theorem interiorPulseCanonicalFast_periodic_entrance_decay (J : ℕ) (hJ : 1 ≤ J)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) {slot : ℤ} (hslot : Odd slot) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot))
    (V : ℝ) (hb : ∀ t x, ∑ j, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (R : ℝ) (hR : 0 ≤ R) (hξ : fibreNorm ξ ≤ R)
    (hθ : ∀ i, ‖(Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i‖ ≤ R)
    (hη0 : 0 ≤ ν / ocMeanFlux α q Λ ζ m ν)
    (hη : ν / ocMeanFlux α q Λ ζ m ν ≤ 1)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j : ℂ)) = 0)
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    (hdisc : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 1024)
    (hfreq : Cw * fibreNorm ξ + 1032 * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2 / 16)
    {a b : ℝ} (hab : a < b)
    (U : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (hU : CellWeakHilbertCurve a b U slice (fun t => cellDualDerivative
      ⟨fun t _ => G t, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot,
        fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, 0⟩
      hG V hv.1 hb t (slice t) 0 0))
    (g₀ : Vec 2 → ℂ) (hg₀ : ContDiff ℝ (J : ℕ∞) g₀)
    (hp₀ : AVenhance.IsZ2Periodic g₀)
    (hi : (U a : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] g₀) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r
    let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
    let c := cellComplexPair (U a)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellSourceSlice ell a))
    let phase := Complex.exp (∫ τ in a..b, fibreSeriesC lam ξ τ)
    let A := 1 + 4 * Real.sqrt (constructedGraphNativeSquareBudget J R
      (fibreCoefficientGraphBound Cw) Cw η)
    let C := (Real.sqrt (constructedNativeGapBasePrice J R 0 Cw (6 * Real.pi ^ 2)) *
      peFactor η ^ J * Real.exp (-(6 * Real.pi ^ 2) * (b - a) / 2)) * A
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (⊤ : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      ((U b - cellScalarCLM c (cellScalarCLM phase
        (cellRawTrace (fibreSeriesJet r ξ) b + cellConstantCLM 1)) : ComplexCellL2) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm J g₁ ≤
        ((∑ l ∈ Finset.range (J + 1), (Fintype.card (DerivativeWord2 l) : ℝ≥0∞)) *
          ENNReal.ofReal C * (Fintype.card (JetIndex2 J) : ℝ≥0∞)) * cellSobolevNorm J g₀ := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r
  let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
  let c := cellComplexPair (U a)
    (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellSourceSlice ell a))
  let phase := fun t => Complex.exp (∫ τ in a..t, fibreSeriesC lam ξ τ)
  let w := fun t => U t - cellScalarCLM c (cellScalarCLM (phase t)
    (cellRawTrace (fibreSeriesJet r ξ) t + cellConstantCLM 1))
  let ws := fun t => slice t - cellH1Scalar c (cellH1Scalar (phase t)
    (cellH1Slice (fibreSeriesJet r ξ) t + cellH1One))
  let A := 1 + 4 * Real.sqrt (constructedGraphNativeSquareBudget J R
    (fibreCoefficientGraphBound Cw) Cw η)
  let B := constructedNativeGapBasePrice J R 0 Cw (6 * Real.pi ^ 2)
  let C := (Real.sqrt B * peFactor η ^ J *
    Real.exp (-(6 * Real.pi ^ 2) * (b - a) / 2)) * A
  let initial := finiteSmoothPeriodicHk J g₀ hg₀ hp₀
  have hiv : U a = torusHkValueCLM initial := by
    apply Lp.ext
    exact hi.trans (finiteSmoothPeriodicHk_value_ae J g₀ hg₀ hp₀).symm
  obtain ⟨I, hIv, hIb⟩ := interiorPulseCanonicalFast_native_entrance J hΛ hζ hν hr
    y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hdisc initial a
  have hI : U a - cellScalarCLM c
      (cellRawTrace (fibreSeriesJet r ξ) a + cellConstantCLM 1) = torusHkValueCLM I := by
    simpa only [← hiv] using hIv.symm
  obtain ⟨W, hwv, hwb⟩ := interiorPulseCanonicalFast_native_decay J hJ hΛ hζ hν hr
    y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hg hgsmall hdisc hfreq
    hab U slice hU I hI
  have hprice := constructedNativeGap_polynomial_price J R 0 Cw η (6 * Real.pi ^ 2)
    hR le_rfl hCw ξ hξ hθ
  have hB := constructedNativeGapBasePrice_nonneg J R 0 Cw (6 * Real.pi ^ 2) hR le_rfl hCw
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hp : 0 ≤ peFactor η := (by norm_num : (0 : ℝ) ≤ 1).trans (one_le_peFactor η)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hIb2 : ‖I‖ ^ 2 ≤ A ^ 2 * ‖initial‖ ^ 2 := by
    have hh := (sq_le_sq₀ (norm_nonneg I) (mul_nonneg hA (norm_nonneg initial))).mpr hIb
    simpa only [mul_pow] using hh
  have hW : ‖W‖ ^ 2 ≤ C ^ 2 * ‖initial‖ ^ 2 := by
    have hb := hwb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hprice (Real.exp_pos _).le) (sq_nonneg ‖I‖))
    have hh := hb.trans (mul_le_mul_of_nonneg_left hIb2
      (mul_nonneg (mul_nonneg hB (pow_nonneg hp _)) (Real.exp_pos _).le))
    dsimp only [C]
    rw [mul_pow, polynomial_decay_square_price _ _ _ _ _ hB]
    convert hh using 1
    ring
  have hgraph := fibreCoefficientFamily_isFibreGraph η Cw hη0 hη hCw G hG hv hw
  have hrad := fibreCoefficientMajorantRadius_pos hCw
  have hsmall : fibreNorm ξ < fibreCoefficientMajorantRadius Cw := by linarith only [hdisc, hrad]
  have hCg : 0 ≤ fibreCoefficientGraphBound Cw := by
    unfold fibreCoefficientGraphBound
    positivity
  have he := fibreGraph_actual_fast_weak_evolution hgraph hη0 hη hCg hCw hG hv hm hw V hb
    ξ hsmall hab.le c U slice hU
  obtain ⟨g₁, hg₁, hp₁, he₁⟩ := interiorPulseActualWeak_positive_window_smooth
    hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ 0 0 (fun _ => by simp)
    measurable_zero hab (w a) w ws he rfl
  refine ⟨g₁, hg₁, hp₁, he₁.symm, ?_⟩
  exact torusHigher_periodic_entrance_sobolev_transfer J g₀ g₁ hg₀ hp₀
    (hg₁.of_le (by simp)) W (by rw [hwv]; exact he₁.symm) C hC hW

end AVRegularity.CycleWords
end
