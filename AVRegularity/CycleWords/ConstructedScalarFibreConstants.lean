-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.ConstructedReflectedFibreGraphNativeLinearGain
import AVRegularity.CycleWords.GeometryErrorPieceMassBudget
public import AVRegularity.CycleWords.PlaneBlochEnergyRealStateIncrement
import AVRegularity.CycleEvolution.FibreWordHomogeneousJets

@[expose] public noncomputable section

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.CycleWords

/-! Polynomial native smoothing for the actual full finite equation, with its zeroth bound discharged. -/

theorem constructedReflectedFibreGraph_exists_smooth_rep
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
    (ξ₀ Cg : ℝ) (hCg : 0 ≤ Cg)
    (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (lam : ℕ × ℕ → ℝ → ℂ)
    (hgraph : IsFibreGraph (ν / ocMeanFlux α q Λ ζ m ν) (fun s => G (-s))
      (fun s x => -ocCellDrift α q Λ ζ m ν y₀ (-s) x) ξ₀ Cg r lam)
    (hdisc : fibreNorm ξ < ξ₀) (t : ℝ) :
    ∃ f : Vec 2 → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧ AVenhance.IsZ2Periodic f ∧
      f =ᵐ[volume.restrict AVenhance.unitCube] cellValue (fibreSeriesJet r ξ) t := by
  have hall := constructedReflectedFibreGraph_uniform_native_orders hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm ξ₀ Cg hCg r lam hgraph hdisc t
  have hex : ∀ J : ℕ, ∃ U : TorusHk J ℂ,
      torusHkValueCLM U = cellRawTrace (fibreSeriesJet r ξ) t := by
    intro J
    obtain ⟨W, hwv, _⟩ := hall J
    refine ⟨W - torusHigherConstant J 1, ?_⟩
    rw [map_sub, torusHigherConstant_value, hwv, add_sub_cancel_right]
  obtain ⟨f, hf, hp, he⟩ := torusHigher_all_order_smooth_representative
    (cellRawTrace (fibreSeriesJet r ξ) t) hex
  exact ⟨f, hf, hp, he.trans (cellRawTrace_ae (fibreSeriesJet r ξ) t
    ((hgraph.2.1 ξ hdisc).2.2.1.1.2.2.1 t (Set.mem_univ t)).1)⟩

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
open scoped NNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! Polynomial native smoothing for the actual full finite equation, with its zeroth bound discharged. -/

theorem constructedFibreGraph_coefficients_native_geometric_bound
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (V : ℝ) (hb : ∀ t x, ∑ j, ocCellDrift α q Λ ζ m ν y₀ t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2) ≤ Cw)
    (hη0 : 0 ≤ ν / ocMeanFlux α q Λ ζ m ν)
    (hη : ν / ocMeanFlux α q Λ ζ m ν ≤ 1)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (ocCellDrift α q Λ ζ m ν y₀ t x j : ℂ)) = 0)
    (ξ₀ Cg : ℝ) (hCg : 0 ≤ Cg)
    (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (lam : ℕ × ℕ → ℝ → ℂ)
    (hgraph : IsFibreGraph (ν / ocMeanFlux α q Λ ζ m ν) G
      (ocCellDrift α q Λ ζ m ν y₀) ξ₀ Cg r lam)
    (ρ : ℝ≥0) (hρ : 0 < ρ)
    (hband : fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ)) < ξ₀) (t : ℝ) :
    ∀ J : ℕ, ∃ U : ℕ × ℕ → TorusHk J ℂ,
      (∀ p, torusHkValueCLM (U p) = cellRawTrace (r p) t) ∧
      (∀ p, ‖U p‖ ≤
        (Real.sqrt (constructedGraphNativeSquareBudget J
          (fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ))) Cg Cw
          (ν / ocMeanFlux α q Λ ζ m ν)) + ‖torusHigherConstant J 1‖) *
          ((ρ : ℝ) / 2)⁻¹ ^ (p.1 + p.2)) := by
  let c := fun p => fibreGraphCoefficientClass hgraph ρ hρ hband p t
  have hsum := fibreUniformMajorant_weighted_summable
    (fibreGraphCoefficientClass hgraph ρ hρ hband) ρ
    (fibreGraphCoefficientClass_majorant hgraph ρ hρ hband) t
  have hex : ∀ J : ℕ, ∃ F : (Fin 2 → ℂ) → TorusHk J ℂ,
      (∀ ξ ∈ Metric.ball (0 : Fin 2 → ℂ) (ρ : ℝ),
        torusHkValueCLM (F ξ) = ∑' p, fibreMonomial ξ p • c p) ∧
      ContDiffAt ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) F 0 := by
    intro J
    obtain ⟨F, hF, hs, _⟩ := constructedFibreGraph_native_frequency_smooth hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw hη0 hη hm ξ₀ Cg hCg r lam hgraph ρ hρ hband t J
    refine ⟨F, ?_, hs.contDiffAt (Metric.ball_mem_nhds (0 : Fin 2 → ℂ) (show (0 : ℝ) < ρ from hρ))⟩
    intro ξ hξ
    have hn : ‖ξ‖ ≤ ρ := le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hξ)
    have hd := (fibreNorm_le_constant_of_norm_le ξ ρ.coe_nonneg hn).trans_lt hband
    exact (hF ξ hξ).1.trans (fibreGraphTrace_eq_nativeSeries hgraph ρ hρ hband ξ hd hn t)
  intro J
  classical
  have hcoeff (p : ℕ × ℕ) : ∃ U : TorusHk J ℂ, torusHkValueCLM U = c p :=
    torusHigher_native_taylor_coefficients c ρ hρ hsum hex p J
  choose U hU using hcoeff
  obtain ⟨F, hF, hs, _⟩ := constructedFibreGraph_native_frequency_smooth hΛ hζ hν hr y₀ hv V hb
    G hG Cw hCw hw hη0 hη hm ξ₀ Cg hCg r lam hgraph ρ hρ hband t J
  have hseries : ∀ ξ ∈ Metric.ball (0 : Fin 2 → ℂ) (ρ : ℝ),
      torusHkValueCLM (F ξ) = ∑' p, fibreMonomial ξ p • c p := by
    intro ξ hξ
    have hn : ‖ξ‖ ≤ ρ := le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hξ)
    have hd := (fibreNorm_le_constant_of_norm_le ξ ρ.coe_nonneg hn).trans_lt hband
    exact (hF ξ hξ).1.trans (fibreGraphTrace_eq_nativeSeries hgraph ρ hρ hband ξ hd hn t)
  refine ⟨U, ?_, ?_⟩
  · intro p
    rw [hU p]
    apply Lp.ext
    exact (fibreGraphCoefficientClass_ae hgraph ρ hρ hband p t).trans
      (cellRawTrace_ae (r p) t (fibreGraphCoefficient_memLp hgraph ρ hρ hband p t)).symm
  · exact torusHigher_native_coefficient_geometric_bound J c ρ hρ hsum F hseries hs _
      (fun ξ hξ => (hF ξ hξ).2) U hU

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! A native periodic entrance gives a polynomially bounded native fast entrance. -/

theorem constructedCanonicalAdjointFast_native_entrance (J : ℕ)
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
    (hdisc : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 1024)
    (initial : TorusHk J ℂ) (t : ℝ) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
    let c := cellComplexPair (torusHkValueCLM initial)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap
        (cellRawTrace (fibreSeriesJet r ξ) t + cellConstantCLM 1))
    ∃ W : TorusHk J ℂ, torusHkValueCLM W =
      torusHkValueCLM initial - cellScalarCLM c (cellSourceSlice ell t) ∧
      ‖W‖ ≤ (1 + 3 * (2 * Real.sqrt (constructedReflectedGraphNativeSquareBudget J R
        (fibreCoefficientGraphBound Cw) Cw η))) * ‖initial‖ := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let rr := fibreCoefficientFamily η Cw hη (fun s => G (-s)) (cellMetric_timeReverse hG)
    (cellDrift_timeReverse hv) (cellDrift_timeReverse_scaled_bound hw)
  let lam := fibreCoefficientSymbol η (fun s => G (-s))
    (fun s x => -ocCellDrift α q Λ ζ m ν y₀ (-s) x) rr
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
  obtain ⟨Rj, hRj, hRjb⟩ := constructedReflectedFibreGraph_uniform_native_orders hΛ hζ hν hr
    y₀ hv V hb G hG Cw hCw hw (fun i => -ξ i) R hR hneg hθneg hη0 hη hm
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
  refine ⟨initial - torusHigherScalarCLM J
    (cellComplexPair (torusHkValueCLM initial)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap R0)) Lj, ?_, ?_⟩
  · rw [torusHigher_normalized_projection_value, hLv]
  · exact torusHigher_normalized_projection_norm J initial Lj R0
      3 (2 * Real.sqrt B) hRb hLb

/-! A native periodic entrance gives a polynomially bounded native fast entrance. -/

theorem interiorPulseCanonicalFast_native_entrance (J : ℕ)
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
    (initial : TorusHk J ℂ) (t : ℝ) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
    let c := cellComplexPair (torusHkValueCLM initial)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellSourceSlice ell t))
    ∃ W : TorusHk J ℂ, torusHkValueCLM W =
      torusHkValueCLM initial - cellScalarCLM c
        (cellRawTrace (fibreSeriesJet r ξ) t + cellConstantCLM 1) ∧
      ‖W‖ ≤ (1 + 4 * Real.sqrt (constructedGraphNativeSquareBudget J R
        (fibreCoefficientGraphBound Cw) Cw η)) * ‖initial‖ := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r
  let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
  let B := constructedGraphNativeSquareBudget J R (fibreCoefficientGraphBound Cw) Cw η
  have hgraph := fibreCoefficientFamily_isFibreGraph η Cw hη0 hη hCw G hG hv hw
  have hrad := fibreCoefficientMajorantRadius_pos hCw
  have hsmall : fibreNorm ξ < fibreCoefficientMajorantRadius Cw := by linarith only [hdisc, hrad]
  have hCg : 0 ≤ fibreCoefficientGraphBound Cw := by
    unfold fibreCoefficientGraphBound
    positivity
  obtain ⟨Rj, hRj, hRjb⟩ := interiorPulseFibreGraph_uniform_native_orders hΛ hζ hν hr
    y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm
    (fibreCoefficientMajorantRadius Cw) (fibreCoefficientGraphBound Cw) hCg r lam
    hgraph hsmall t J
  have hRb : ‖Rj‖ ≤ Real.sqrt B := Real.le_sqrt_of_sq_le hRjb
  have hell : ‖cellSourceSlice ell t‖ ≤ 4 := by
    have he := fibreAdjointRow_class_small η Cw hη hCw G hG hv hw ξ hdisc t
    have hn : ‖cellSourceSlice ell t‖ ≤ ‖cellSourceSlice ell t - cellConstantCLM 1‖ +
        ‖cellConstantCLM 1‖ := by
      simpa only [sub_add_cancel] using
        norm_add_le (cellSourceSlice ell t - cellConstantCLM 1) (cellConstantCLM 1)
    rw [cellConstantCLM_norm, norm_one] at hn
    linarith only [hn, he]
  refine ⟨initial - torusHigherScalarCLM J
    (cellComplexPair (torusHkValueCLM initial)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellSourceSlice ell t))) Rj, ?_, ?_⟩
  · rw [torusHigher_normalized_projection_value, hRj]
  · exact torusHigher_normalized_projection_norm J initial Rj (cellSourceSlice ell t)
      4 (Real.sqrt B) hell hRb

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
open scoped NNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! Polynomial native smoothing for the actual full finite equation, with its zeroth bound discharged. -/

theorem interiorPulseFibreGraph_native_frequency_smooth
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
    (ξ₀ Cg : ℝ) (hCg : 0 ≤ Cg)
    (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (lam : ℕ × ℕ → ℝ → ℂ)
    (hgraph : IsFibreGraph (ν / ocMeanFlux α q Λ ζ m ν) G
      (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) ξ₀ Cg r lam)
    (ρ : ℝ≥0) (hρ : 0 < ρ)
    (hband : fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ)) < ξ₀) (t : ℝ) (J : ℕ) :
    ∃ F : (Fin 2 → ℂ) → TorusHk J ℂ,
      (∀ ξ ∈ Metric.ball 0 (ρ : ℝ),
        torusHkValueCLM (F ξ) = cellRawTrace (fibreSeriesJet r ξ) t ∧
        ‖F ξ‖ ≤ Real.sqrt (constructedGraphNativeSquareBudget J
          (fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ))) Cg Cw
          (ν / ocMeanFlux α q Λ ζ m ν)) + ‖torusHigherConstant J 1‖) ∧
      ContDiffOn ℂ (⊤ : ℕ∞) F (Metric.ball 0 (ρ : ℝ)) ∧ F 0 = 0 := by
  let R := fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ))
  let k := (8 + Cw * Cg) * R ^ 2
  let B := (Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1) *
      constructedNativeWindowPrice J R k Cw) ^ J *
    peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ (2 * J) *
    (Real.exp (constructedAllOrderPrice 0 R k Cw) * (1 + Cg * R) ^ 2)
  let M := Real.sqrt B + ‖torusHigherConstant J 1‖
  have hex : ∀ ξ ∈ Metric.ball (0 : Fin 2 → ℂ) (ρ : ℝ),
      ∃ W : TorusHk J ℂ, torusHkValueCLM W = ∑' p, fibreMonomial ξ p •
        fibreGraphCoefficientClass hgraph ρ hρ hband p t ∧ ‖W‖ ≤ M := by
    intro ξ hξ
    have hn : ‖ξ‖ ≤ ρ := by exact le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hξ)
    have hf : fibreNorm ξ ≤ R := fibreNorm_le_constant_of_norm_le ξ ρ.coe_nonneg hn
    have hd : fibreNorm ξ < ξ₀ := hf.trans_lt hband
    have hall := interiorPulseFibreGraph_uniform_native_orders hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R
      (fibreNorm_nonneg _) hf (fun i => (normalizedFrequency_coordinate_le hη ξ i).trans hf)
      hη0 hη hm ξ₀ Cg hCg r lam hgraph hd t J
    obtain ⟨W, hwv, hwn⟩ := torusHigher_correction_witness J (cellRawTrace (fibreSeriesJet r ξ) t) B hall
    exact ⟨W, hwv.trans (fibreGraphTrace_eq_nativeSeries hgraph ρ hρ hband ξ hd hn t), hwn⟩
  obtain ⟨F, hF, hs, hz⟩ := fibreGraph_native_smooth_zero_of_witnesses hgraph
    (lt_of_le_of_lt (fibreNorm_nonneg _) hband) ρ hρ hband t J M
    (add_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) hex
  refine ⟨F, ?_, hs, hz⟩
  intro ξ hξ
  have hn : ‖ξ‖ ≤ ρ := by exact le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hξ)
  have hd := (fibreNorm_le_constant_of_norm_le ξ ρ.coe_nonneg hn).trans_lt hband
  exact ⟨(hF ξ hξ).1.trans (fibreGraphTrace_eq_nativeSeries hgraph ρ hρ hband ξ hd hn t).symm, (hF ξ hξ).2⟩

/-! Polynomial native smoothing for the actual full finite equation, with its zeroth bound discharged. -/

theorem interiorPulseFibreGraph_native_linear_gain
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
    (ξ₀ Cg : ℝ) (hCg : 0 ≤ Cg)
    (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (lam : ℕ × ℕ → ℝ → ℂ)
    (hgraph : IsFibreGraph (ν / ocMeanFlux α q Λ ζ m ν) G
      (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) ξ₀ Cg r lam)
    (ρ : ℝ≥0) (hρ : 0 < ρ)
    (hband : fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ)) < ξ₀) (t : ℝ) (J : ℕ)
    (ξ : Fin 2 → ℂ) (hξ : ξ ∈ Metric.ball 0 ((ρ : ℝ) / 2)) :
    ∃ U : TorusHk J ℂ, torusHkValueCLM U = cellRawTrace (fibreSeriesJet r ξ) t ∧
      ‖U‖ ≤ (64 * (Real.sqrt (constructedGraphNativeSquareBudget J
        (fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ))) Cg Cw
        (ν / ocMeanFlux α q Λ ζ m ν)) + ‖torusHigherConstant J 1‖) / (ρ : ℝ)) * fibreNorm ξ := by
  obtain ⟨F, hF, _, hz⟩ := interiorPulseFibreGraph_native_frequency_smooth hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw hη0 hη hm ξ₀ Cg hCg r lam hgraph ρ hρ hband t J
  let M := Real.sqrt (constructedGraphNativeSquareBudget J
    (fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ))) Cg Cw
    (ν / ocMeanFlux α q Λ ζ m ν)) + ‖torusHigherConstant J 1‖
  let g := fun ξ => ∑' p, fibreMonomial ξ p • fibreGraphCoefficientClass hgraph ρ hρ hband p t
  have hFg : ∀ ξ ∈ Metric.ball (0 : Fin 2 → ℂ) (ρ : ℝ),
      torusHkValueCLM (F ξ) = g ξ ∧ ‖F ξ‖ ≤ M := by
    intro ζ hζ
    have hn : ‖ζ‖ ≤ ρ := le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hζ)
    have hd := (fibreNorm_le_constant_of_norm_le ζ ρ.coe_nonneg hn).trans_lt hband
    exact ⟨(hF ζ hζ).1.trans (fibreGraphTrace_eq_nativeSeries hgraph ρ hρ hband ζ hd hn t), (hF ζ hζ).2⟩
  have hn := torusHigher_native_frequency_zero_gain J g F ρ M hρ
    (add_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    (fibreGraphNativeSeries_analyticOnNhd hgraph ρ hρ hband t) hFg hz ξ hξ
  have hξ' := Metric.ball_subset_ball (by have h := ρ.coe_nonneg; linarith : (ρ : ℝ) / 2 ≤ ρ) hξ
  refine ⟨F ξ, (hF ξ hξ').1, hn.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (fibrePiNorm_le ξ) (by dsimp only [M]; positivity)

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.CycleWords

/-! Polynomial native smoothing for the actual full finite equation, with its zeroth bound discharged. -/

theorem interiorPulseFibreGraph_exists_smooth_rep
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
    (ξ₀ Cg : ℝ) (hCg : 0 ≤ Cg)
    (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (lam : ℕ × ℕ → ℝ → ℂ)
    (hgraph : IsFibreGraph (ν / ocMeanFlux α q Λ ζ m ν) G
      (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) ξ₀ Cg r lam)
    (hdisc : fibreNorm ξ < ξ₀) (t : ℝ) :
    ∃ f : Vec 2 → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧ AVenhance.IsZ2Periodic f ∧
      f =ᵐ[volume.restrict AVenhance.unitCube] cellValue (fibreSeriesJet r ξ) t := by
  have hall := interiorPulseFibreGraph_uniform_native_orders hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm ξ₀ Cg hCg r lam hgraph hdisc t
  have hex : ∀ J : ℕ, ∃ U : TorusHk J ℂ,
      torusHkValueCLM U = cellRawTrace (fibreSeriesJet r ξ) t := by
    intro J
    obtain ⟨W, hwv, _⟩ := hall J
    refine ⟨W - torusHigherConstant J 1, ?_⟩
    rw [map_sub, torusHigherConstant_value, hwv, add_sub_cancel_right]
  obtain ⟨f, hf, hp, he⟩ := torusHigher_all_order_smooth_representative
    (cellRawTrace (fibreSeriesJet r ξ) t) hex
  exact ⟨f, hf, hp, he.trans (cellRawTrace_ae (fibreSeriesJet r ξ) t
    ((hgraph.2.1 ξ hdisc).2.2.1.1.2.2.1 t (Set.mem_univ t)).1)⟩

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
open scoped NNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! Literal smooth periodic graph coefficient representatives have a common smooth-series radius. -/

theorem constructedFibreGraph_smooth_coefficient_series
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (V : ℝ) (hb : ∀ t x, ∑ j, ocCellDrift α q Λ ζ m ν y₀ t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2) ≤ Cw)
    (hη0 : 0 ≤ ν / ocMeanFlux α q Λ ζ m ν)
    (hη : ν / ocMeanFlux α q Λ ζ m ν ≤ 1)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (ocCellDrift α q Λ ζ m ν y₀ t x j : ℂ)) = 0)
    (ξ₀ Cg : ℝ) (hCg : 0 ≤ Cg)
    (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (lam : ℕ × ℕ → ℝ → ℂ)
    (hgraph : IsFibreGraph (ν / ocMeanFlux α q Λ ζ m ν) G
      (ocCellDrift α q Λ ζ m ν y₀) ξ₀ Cg r lam)
    (ρ : ℝ≥0) (hρ : 0 < ρ)
    (hband : fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ)) < ξ₀) (t : ℝ)
    (f : ℕ × ℕ → ℝ → Vec 2 → ℂ)
    (hf : ∀ p, ContDiff ℝ (⊤ : ℕ∞) (f p t))
    (hp : ∀ p, AVenhance.IsZ2Periodic (f p t))
    (he : ∀ p, f p t =ᵐ[volume.restrict AVenhance.unitCube] cellValue (r p) t)
    (ξ : Fin 2 → ℂ) (hξ : ((ρ : ℝ) / 2)⁻¹ * ‖ξ‖ < 1) :
    ContDiff ℝ (⊤ : ℕ∞) (fibreSeriesFun f ξ t) := by
  apply fibreSeriesFun_contDiff_of_native_coefficients f t hf hp
    ((ρ : ℝ) / 2)⁻¹ (by positivity)
    (fun J => Real.sqrt (constructedGraphNativeSquareBudget J
      (fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ))) Cg Cw
      (ν / ocMeanFlux α q Λ ζ m ν)) + ‖torusHigherConstant J 1‖) _ ξ hξ
  intro J
  obtain ⟨U, hU, hbU⟩ := constructedFibreGraph_coefficients_native_geometric_bound
    hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw hη0 hη hm ξ₀ Cg hCg r lam
    hgraph ρ hρ hband t J
  refine ⟨U, ?_, hbU⟩
  intro p
  rw [hU p]
  exact (he p).trans (cellRawTrace_ae (r p) t
    (fibreGraphCoefficient_memLp hgraph ρ hρ hband p t)).symm

/-! Literal smooth periodic graph coefficient representatives have a common smooth-series radius. -/

theorem constructedFibreGraph_smooth_coefficient_replacement
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (V : ℝ) (hb : ∀ t x, ∑ j, ocCellDrift α q Λ ζ m ν y₀ t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2) ≤ Cw)
    (hη0 : 0 ≤ ν / ocMeanFlux α q Λ ζ m ν)
    (hη : ν / ocMeanFlux α q Λ ζ m ν ≤ 1)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (ocCellDrift α q Λ ζ m ν y₀ t x j : ℂ)) = 0)
    (ξ₀ Cg : ℝ) (hCg : 0 ≤ Cg)
    (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (lam : ℕ × ℕ → ℝ → ℂ)
    (hgraph : IsFibreGraph (ν / ocMeanFlux α q Λ ζ m ν) G
      (ocCellDrift α q Λ ζ m ν y₀) ξ₀ Cg r lam)
    (ρ : ℝ≥0) (hρ : 0 < ρ)
    (hband : fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ)) < ξ₀) :
    ∃ f : ℕ × ℕ → ℝ → Vec 2 → ℂ,
      (∀ p t, ContDiff ℝ (⊤ : ℕ∞) (f p t)) ∧
      (∀ p t, AVenhance.IsZ2Periodic (f p t)) ∧
      (∀ p t, f p t =ᵐ[volume.restrict AVenhance.unitCube] cellValue (r p) t) ∧
      (∀ ξ t, ((ρ : ℝ) / 2)⁻¹ * ‖ξ‖ < 1 →
        ContDiff ℝ (⊤ : ℕ∞) (fibreSeriesFun f ξ t)) ∧
      (∀ ξ t, AVenhance.IsZ2Periodic (fibreSeriesFun f ξ t)) := by
  classical
  have hex : ∀ p t, ∃ f : Vec 2 → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧
      AVenhance.IsZ2Periodic f ∧
      f =ᵐ[volume.restrict AVenhance.unitCube] cellValue (r p) t := by
    intro p t
    exact constructedFibreGraph_coefficient_smooth_rep hΛ hζ hν hr y₀ hv V hb G hG
      Cw hCw hw hη0 hη hm ξ₀ Cg hCg r lam hgraph ρ hρ hband t p
  choose f hf hp he using hex
  refine ⟨f, hf, hp, he, ?_, ?_⟩
  · intro ξ t hξ
    exact constructedFibreGraph_smooth_coefficient_series hΛ hζ hν hr y₀ hv V hb G hG
      Cw hCw hw hη0 hη hm ξ₀ Cg hCg r lam hgraph ρ hρ hband t f
      (fun p => hf p t) (fun p => hp p t) (fun p => he p t) ξ hξ
  · exact fibreSeriesFun_periodic f hp

/-! Polynomial native smoothing for the actual full finite equation, with its zeroth bound discharged. -/

theorem constructedReflectedFibreGraph_coefficient_smooth_rep
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (V : ℝ) (hb : ∀ t x, ∑ j, ocCellDrift α q Λ ζ m ν y₀ t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2) ≤ Cw)
    (hη0 : 0 ≤ ν / ocMeanFlux α q Λ ζ m ν)
    (hη : ν / ocMeanFlux α q Λ ζ m ν ≤ 1)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (ocCellDrift α q Λ ζ m ν y₀ t x j : ℂ)) = 0)
    (ξ₀ Cg : ℝ) (hCg : 0 ≤ Cg)
    (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (lam : ℕ × ℕ → ℝ → ℂ)
    (hgraph : IsFibreGraph (ν / ocMeanFlux α q Λ ζ m ν) (fun s => G (-s))
      (fun s x => -ocCellDrift α q Λ ζ m ν y₀ (-s) x) ξ₀ Cg r lam)
    (ρ : ℝ≥0) (hρ : 0 < ρ)
    (hband : fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ)) < ξ₀) (t : ℝ) (p : ℕ × ℕ) :
    ∃ f : Vec 2 → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧ AVenhance.IsZ2Periodic f ∧
      f =ᵐ[volume.restrict AVenhance.unitCube] cellValue (r p) t := by
  let c := fun p => fibreGraphCoefficientClass hgraph ρ hρ hband p t
  have hsum := fibreUniformMajorant_weighted_summable
    (fibreGraphCoefficientClass hgraph ρ hρ hband) ρ
    (fibreGraphCoefficientClass_majorant hgraph ρ hρ hband) t
  have hex : ∀ J : ℕ, ∃ F : (Fin 2 → ℂ) → TorusHk J ℂ,
      (∀ ξ ∈ Metric.ball (0 : Fin 2 → ℂ) (ρ : ℝ),
        torusHkValueCLM (F ξ) = ∑' p, fibreMonomial ξ p • c p) ∧
      ContDiffAt ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) F 0 := by
    intro J
    obtain ⟨F, hF, hs, _⟩ := constructedReflectedFibreGraph_native_frequency_smooth hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw hη0 hη hm ξ₀ Cg hCg r lam hgraph ρ hρ hband t J
    refine ⟨F, ?_, hs.contDiffAt (Metric.ball_mem_nhds (0 : Fin 2 → ℂ) (show (0 : ℝ) < ρ from hρ))⟩
    intro ξ hξ
    have hn : ‖ξ‖ ≤ ρ := le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hξ)
    have hd := (fibreNorm_le_constant_of_norm_le ξ ρ.coe_nonneg hn).trans_lt hband
    exact (hF ξ hξ).1.trans (fibreGraphTrace_eq_nativeSeries hgraph ρ hρ hband ξ hd hn t)
  obtain ⟨f, hf, hp, he⟩ := torusHigher_taylor_coefficients_smooth_representatives c ρ hρ hsum hex p
  exact ⟨f, hf, hp, he.trans (fibreGraphCoefficientClass_ae hgraph ρ hρ hband p t)⟩

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
open scoped ENNReal NNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! Polynomial native smoothing for the actual full finite equation, with its zeroth bound discharged. -/

theorem interiorPulseFibreGraph_smooth_cellSobolev_bound
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
    (ξ₀ Cg : ℝ) (hCg : 0 ≤ Cg)
    (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (lam : ℕ × ℕ → ℝ → ℂ)
    (hgraph : IsFibreGraph (ν / ocMeanFlux α q Λ ζ m ν) G
      (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) ξ₀ Cg r lam)
    (ρ : ℝ≥0) (hρ : 0 < ρ)
    (hband : fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ)) < ξ₀) (t : ℝ) (J : ℕ)
    (ξ : Fin 2 → ℂ) (hξ : ξ ∈ Metric.ball 0 ((ρ : ℝ) / 2))
    (f : Vec 2 → ℂ) (hf : ContDiff ℝ (J : ℕ∞) f)
    (he : f =ᵐ[volume.restrict AVenhance.unitCube] cellValue (fibreSeriesJet r ξ) t) :
    cellSobolevNorm J f ≤
      (∑ b ∈ Finset.range (J + 1), (Fintype.card (DerivativeWord2 b) : ℝ≥0∞)) *
      ENNReal.ofReal ((64 * (Real.sqrt (constructedGraphNativeBaseSquareBudget J
        (fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ))) Cg Cw) + ‖torusHigherConstant J 1‖) / (ρ : ℝ)) *
        peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ J * fibreNorm ξ) := by
  obtain ⟨U, hv, hbU⟩ := interiorPulseFibreGraph_native_linear_gain hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw hη0 hη hm ξ₀ Cg hCg r lam hgraph ρ hρ hband t J ξ hξ
  have hξ' := Metric.ball_subset_ball (by have h := ρ.coe_nonneg; linarith : (ρ : ℝ) / 2 ≤ ρ) hξ
  have hn : ‖ξ‖ ≤ ρ := le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hξ')
  have hd := (fibreNorm_le_constant_of_norm_le ξ ρ.coe_nonneg hn).trans_lt hband
  have hval : (torusHkValueCLM U : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] f := by
    rw [hv]
    exact (cellRawTrace_ae (fibreSeriesJet r ξ) t
      ((hgraph.2.1 ξ hd).2.2.1.1.2.2.1 t (Set.mem_univ t)).1).trans he.symm
  have hprice := constructedGraphNativeCorrection_polynomial_price J
    (fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ))) Cg Cw (ν / ocMeanFlux α q Λ ζ m ν)
  have hu : ‖U‖ ≤ (64 * (Real.sqrt (constructedGraphNativeBaseSquareBudget J
        (fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ))) Cg Cw) + ‖torusHigherConstant J 1‖) / (ρ : ℝ)) *
        peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ J * fibreNorm ξ := by
    apply hbU.trans
    have hh := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hprice (by norm_num : (0 : ℝ) ≤ 64)) ρ.coe_nonneg)
      (fibreNorm_nonneg ξ)
    convert hh using 1
    ring
  apply (torusHigher_smooth_cellSobolevNorm_le U f hf hval).trans
  apply mul_le_mul' le_rfl
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hu

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
open scoped NNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! Literal smooth periodic graph coefficient representatives have a common smooth-series radius. -/

local instance graphSmoothReplacementMeasurableSpace : MeasurableSpace ComplexCellL2 := borel _
local instance graphSmoothReplacementBorelSpace : BorelSpace ComplexCellL2 := ⟨rfl⟩


theorem constructedFibreGraph_smooth_coefficient_replacement_measurable
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (V : ℝ) (hb : ∀ t x, ∑ j, ocCellDrift α q Λ ζ m ν y₀ t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2) ≤ Cw)
    (hη0 : 0 ≤ ν / ocMeanFlux α q Λ ζ m ν)
    (hη : ν / ocMeanFlux α q Λ ζ m ν ≤ 1)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (ocCellDrift α q Λ ζ m ν y₀ t x j : ℂ)) = 0)
    (ξ₀ Cg : ℝ) (hCg : 0 ≤ Cg)
    (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (lam : ℕ × ℕ → ℝ → ℂ)
    (hgraph : IsFibreGraph (ν / ocMeanFlux α q Λ ζ m ν) G
      (ocCellDrift α q Λ ζ m ν y₀) ξ₀ Cg r lam)
    (ρ : ℝ≥0) (hρ : 0 < ρ)
    (hband : fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ)) < ξ₀)
    (hc : ∀ p, Continuous (cellRawTrace (r p))) :
    ∃ f : ℕ × ℕ → ℝ → Vec 2 → ℂ,
      (∀ p t, ContDiff ℝ (⊤ : ℕ∞) (f p t)) ∧
      (∀ p t, AVenhance.IsZ2Periodic (f p t)) ∧
      (∀ p t, f p t =ᵐ[volume.restrict AVenhance.unitCube] cellValue (r p) t) ∧
      (∀ ξ t, ((ρ : ℝ) / 2)⁻¹ * ‖ξ‖ < 1 →
        ContDiff ℝ (⊤ : ℕ∞) (fibreSeriesFun f ξ t)) ∧
      (∀ ξ t, AVenhance.IsZ2Periodic (fibreSeriesFun f ξ t)) ∧
      (∀ p, StronglyMeasurable (fun z : ℝ × Vec 2 => f p z.1 z.2)) := by
  obtain ⟨f, hf, hp, he, hs, hsp⟩ := constructedFibreGraph_smooth_coefficient_replacement
    hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw hη0 hη hm ξ₀ Cg hCg r lam hgraph ρ hρ hband
  refine ⟨f, hf, hp, he, hs, hsp, ?_⟩
  intro p
  have hex : ∀ t, ∃ U : TorusHk 2 ℂ, torusHkValueCLM U = cellRawTrace (r p) t := by
    intro t
    obtain ⟨U, hU, _⟩ := constructedFibreGraph_coefficients_native_geometric_bound
      hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw hη0 hη hm ξ₀ Cg hCg r lam hgraph
      ρ hρ hband t 2
    exact ⟨U p, hU p⟩
  choose U hU using hex
  have hme : Measurable (fun t => torusHkValueCLM (U t)) := by
    have heq : (fun t => torusHkValueCLM (U t)) = cellRawTrace (r p) := funext hU
    rw [heq]
    exact (hc p).measurable
  apply torusHigher_periodic_representative_jointly_stronglyMeasurable 2 le_rfl U
    (cellNative_stronglyMeasurable_of_value 2 U hme) (f p)
    (fun t => (hf p t).continuous) (hp p)
  intro t
  rw [hU t]
  exact (he p t).trans (cellRawTrace_ae (r p) t
    (fibreGraphCoefficient_memLp hgraph ρ hρ hband p t)).symm

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! A native periodic entrance gives a polynomially bounded native fast entrance. -/

theorem constructedCanonicalFast_entrance_representative (J : ℕ)
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
    (hdisc : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 1024)
    (g₀ : Vec 2 → ℂ) (hg₀ : ContDiff ℝ (J : ℕ∞) g₀)
    (hp₀ : AVenhance.IsZ2Periodic g₀) (t : ℝ) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
    let initial := finiteSmoothPeriodicHk J g₀ hg₀ hp₀
    let c := cellComplexPair (torusHkValueCLM initial)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellSourceSlice ell t))
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (J : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      ((torusHkValueCLM initial - cellScalarCLM c
        (cellRawTrace (fibreSeriesJet r ξ) t + cellConstantCLM 1) : ComplexCellL2) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm J g₁ ≤
        ((∑ l ∈ Finset.range (J + 1), (Fintype.card (DerivativeWord2 l) : ℝ≥0∞)) *
          ENNReal.ofReal (1 + 4 * Real.sqrt (constructedGraphNativeSquareBudget J R
            (fibreCoefficientGraphBound Cw) Cw η)) * (Fintype.card (JetIndex2 J) : ℝ≥0∞)) *
              cellSobolevNorm J g₀ := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r
  let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
  let B := constructedGraphNativeSquareBudget J R (fibreCoefficientGraphBound Cw) Cw η
  have hgraph := fibreCoefficientFamily_isFibreGraph η Cw hη0 hη hCw G hG hv hw
  have hrad := fibreCoefficientMajorantRadius_pos hCw
  have hsmall : fibreNorm ξ < fibreCoefficientMajorantRadius Cw := by linarith only [hdisc, hrad]
  have hCg : 0 ≤ fibreCoefficientGraphBound Cw := by
    unfold fibreCoefficientGraphBound
    positivity
  obtain ⟨Rj, hRj, hRjb⟩ := constructedFibreGraph_uniform_native_orders hΛ hζ hν hr
    y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm
    (fibreCoefficientMajorantRadius Cw) (fibreCoefficientGraphBound Cw) hCg r lam
    hgraph hsmall t J
  have hRb : ‖Rj‖ ≤ Real.sqrt B := Real.le_sqrt_of_sq_le hRjb
  have hell : ‖cellSourceSlice ell t‖ ≤ 4 := by
    have he := fibreAdjointRow_class_small η Cw hη hCw G hG hv hw ξ hdisc t
    have hn : ‖cellSourceSlice ell t‖ ≤ ‖cellSourceSlice ell t - cellConstantCLM 1‖ +
        ‖cellConstantCLM 1‖ := by
      simpa only [sub_add_cancel] using
        norm_add_le (cellSourceSlice ell t - cellConstantCLM 1) (cellConstantCLM 1)
    rw [cellConstantCLM_norm, norm_one] at hn
    linarith only [hn, he]
  obtain ⟨f, hf, hpf, hef⟩ := constructedFibreGraph_exists_smooth_rep
    hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm
    (fibreCoefficientMajorantRadius Cw) (fibreCoefficientGraphBound Cw) hCg r lam
    hgraph hsmall t
  have hRF : (torusHkValueCLM Rj : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      (fun x => 1 + f x) := by
    rw [hRj]
    have hgi := fibreCoefficientFamily_graph_isInverse η Cw hη hCw G hG hv hw ξ hsmall.le
    filter_upwards [cellRawTrace_add_one_ae (fibreSeriesJet r ξ) t
      (hgi.1.2.2.1 t (mem_univ t)).1, hef] with x hx hf
    rw [hx, hf, add_comm]
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := torusHigher_periodic_projection_representative J
    g₀ (fun x => 1 + f x) hg₀ hp₀
    (contDiff_const.add (hf.of_le (by simp))) (by intro n x; simp only [hpf n x])
    Rj hRF (cellSourceSlice ell t) 4 (Real.sqrt B) hell hRb
  refine ⟨g₁, hg₁, hp₁, ?_, hb₁⟩
  simpa only [hRj] using he₁

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
open scoped NNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! Polynomial native smoothing for the actual full finite equation, with its zeroth bound discharged. -/

theorem constructedReflectedFibreGraph_coefficients_native_geometric_bound
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (V : ℝ) (hb : ∀ t x, ∑ j, ocCellDrift α q Λ ζ m ν y₀ t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2) ≤ Cw)
    (hη0 : 0 ≤ ν / ocMeanFlux α q Λ ζ m ν)
    (hη : ν / ocMeanFlux α q Λ ζ m ν ≤ 1)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (ocCellDrift α q Λ ζ m ν y₀ t x j : ℂ)) = 0)
    (ξ₀ Cg : ℝ) (hCg : 0 ≤ Cg)
    (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (lam : ℕ × ℕ → ℝ → ℂ)
    (hgraph : IsFibreGraph (ν / ocMeanFlux α q Λ ζ m ν) (fun s => G (-s))
      (fun s x => -ocCellDrift α q Λ ζ m ν y₀ (-s) x) ξ₀ Cg r lam)
    (ρ : ℝ≥0) (hρ : 0 < ρ)
    (hband : fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ)) < ξ₀) (t : ℝ) :
    ∀ J : ℕ, ∃ U : ℕ × ℕ → TorusHk J ℂ,
      (∀ p, torusHkValueCLM (U p) = cellRawTrace (r p) t) ∧
      (∀ p, ‖U p‖ ≤
        (Real.sqrt (constructedReflectedGraphNativeSquareBudget J
          (fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ))) Cg Cw
          (ν / ocMeanFlux α q Λ ζ m ν)) + ‖torusHigherConstant J 1‖) *
          ((ρ : ℝ) / 2)⁻¹ ^ (p.1 + p.2)) := by
  let c := fun p => fibreGraphCoefficientClass hgraph ρ hρ hband p t
  have hsum := fibreUniformMajorant_weighted_summable
    (fibreGraphCoefficientClass hgraph ρ hρ hband) ρ
    (fibreGraphCoefficientClass_majorant hgraph ρ hρ hband) t
  have hex : ∀ J : ℕ, ∃ F : (Fin 2 → ℂ) → TorusHk J ℂ,
      (∀ ξ ∈ Metric.ball (0 : Fin 2 → ℂ) (ρ : ℝ),
        torusHkValueCLM (F ξ) = ∑' p, fibreMonomial ξ p • c p) ∧
      ContDiffAt ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) F 0 := by
    intro J
    obtain ⟨F, hF, hs, _⟩ := constructedReflectedFibreGraph_native_frequency_smooth hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw hη0 hη hm ξ₀ Cg hCg r lam hgraph ρ hρ hband t J
    refine ⟨F, ?_, hs.contDiffAt (Metric.ball_mem_nhds (0 : Fin 2 → ℂ) (show (0 : ℝ) < ρ from hρ))⟩
    intro ξ hξ
    have hn : ‖ξ‖ ≤ ρ := le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hξ)
    have hd := (fibreNorm_le_constant_of_norm_le ξ ρ.coe_nonneg hn).trans_lt hband
    exact (hF ξ hξ).1.trans (fibreGraphTrace_eq_nativeSeries hgraph ρ hρ hband ξ hd hn t)
  intro J
  classical
  have hcoeff (p : ℕ × ℕ) : ∃ U : TorusHk J ℂ, torusHkValueCLM U = c p :=
    torusHigher_native_taylor_coefficients c ρ hρ hsum hex p J
  choose U hU using hcoeff
  obtain ⟨F, hF, hs, _⟩ := constructedReflectedFibreGraph_native_frequency_smooth hΛ hζ hν hr y₀ hv V hb
    G hG Cw hCw hw hη0 hη hm ξ₀ Cg hCg r lam hgraph ρ hρ hband t J
  have hseries : ∀ ξ ∈ Metric.ball (0 : Fin 2 → ℂ) (ρ : ℝ),
      torusHkValueCLM (F ξ) = ∑' p, fibreMonomial ξ p • c p := by
    intro ξ hξ
    have hn : ‖ξ‖ ≤ ρ := le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hξ)
    have hd := (fibreNorm_le_constant_of_norm_le ξ ρ.coe_nonneg hn).trans_lt hband
    exact (hF ξ hξ).1.trans (fibreGraphTrace_eq_nativeSeries hgraph ρ hρ hband ξ hd hn t)
  refine ⟨U, ?_, ?_⟩
  · intro p
    rw [hU p]
    apply Lp.ext
    exact (fibreGraphCoefficientClass_ae hgraph ρ hρ hband p t).trans
      (cellRawTrace_ae (r p) t (fibreGraphCoefficient_memLp hgraph ρ hρ hband p t)).symm
  · exact torusHigher_native_coefficient_geometric_bound J c ρ hρ hsum F hseries hs _
      (fun ξ hξ => (hF ξ hξ).2) U hU

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Higher full-equation decay of the actual canonical slow remainder. -/

theorem constructedCanonicalFast_native_decay (J : ℕ) (hJ : 1 ≤ J)
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
    (U : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (hU : CellWeakHilbertCurve a b U slice (fun t => cellDualDerivative
      ⟨fun t _ => G t, ocCellDrift α q Λ ζ m ν y₀,
        fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, 0⟩
      hG V hv.1 hb t (slice t) 0 0))
    (initial : TorusHk J ℂ) 
    (hi :
      let η := ν / ocMeanFlux α q Λ ζ m ν
      let r := fibreCoefficientFamily η Cw hη G hG hv hw
      let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
      let c := cellComplexPair (U a)
        (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellSourceSlice ell a))
      U a - cellScalarCLM c (cellRawTrace (fibreSeriesJet r ξ) a + cellConstantCLM 1) =
        torusHkValueCLM initial) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r
    let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
    let c := cellComplexPair (U a)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellSourceSlice ell a))
    let phase := fun t => Complex.exp (∫ τ in a..t, fibreSeriesC lam ξ τ)
    let δ₀ := constructedNativeSmoothingTime J R 0 Cw η
    let P := (Real.exp 1 * (2 * Real.exp 1) / (δ₀ / (J : ℝ))) ^ J
    ∃ W : TorusHk J ℂ, torusHkValueCLM W =
      U b - cellScalarCLM c (cellScalarCLM (phase b)
        (cellRawTrace (fibreSeriesJet r ξ) b + cellConstantCLM 1)) ∧ ‖W‖ ^ 2 ≤
      (Real.exp (6 * Real.pi ^ 2) * (Real.exp 1 + P * Real.exp
        (cellFullZerothGrowth η Cw ξ 0))) *
        Real.exp (-(6 * Real.pi ^ 2) * (b - a)) * ‖initial‖ ^ 2 := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r
  let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
  let c := cellComplexPair (U a)
    (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellSourceSlice ell a))
  let phase := fun t => Complex.exp (∫ τ in a..t, fibreSeriesC lam ξ τ)
  let w := fun t => U t - cellScalarCLM c (cellScalarCLM (phase t)
    (cellRawTrace (fibreSeriesJet r ξ) t + cellConstantCLM 1))
  let ws := fun t => slice t - cellH1Scalar c (cellH1Scalar (phase t)
    (cellH1Slice (fibreSeriesJet r ξ) t + cellH1One))
  have hgraph := fibreCoefficientFamily_isFibreGraph η Cw hη0 hη hCw G hG hv hw
  have hrad := fibreCoefficientMajorantRadius_pos hCw
  have hsmall : fibreNorm ξ < fibreCoefficientMajorantRadius Cw := by linarith only [hdisc, hrad]
  have hCg : 0 ≤ fibreCoefficientGraphBound Cw := by
    unfold fibreCoefficientGraphBound
    positivity
  have he := fibreGraph_actual_fast_weak_evolution hgraph hη0 hη hCg hCw hG hv hm hw V hb
    ξ hsmall hab.le c U slice hU
  have hgap := fibreGraph_weak_remainder_decay hab.le η Cw hη0 hη hCw G hG hg hgsmall
    hv hm hw V hb ξ hdisc hfreq U slice hU
  have hi' : w a = torusHkValueCLM initial := by
    dsimp only [w, phase]
    simpa only [intervalIntegral.integral_same, Complex.exp_zero, cellScalarCLM_smul,
      one_smul] using hi
  exact constructedActualWeak_native_gap_decay J hJ hΛ hζ hν hr y₀ hv V hb G hG
    Cw hCw hw ξ R hR hξ hθ 0 0 (fun _ => by simp) measurable_zero hab
    w ws he initial hi' (6 * Real.pi ^ 2) (by positivity) hgap

end AVRegularity.CycleWords
end

section
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The fibre constants are fixed by the scaled drift bound before contrast and time windows. -/

def constructedScalarFibreConstants (seed : ScalarConstants) (Cw : ℝ) (hCw : 0 ≤ Cw) :
    ScalarConstants :=
  { seed with
    ξ0 := fibreCoefficientMajorantRadius Cw / 2048
    Cg := constructedScalarGraphPrice Cw
    Cw := Cw
    g0 := 1 / 16
    Cj := fun J => constructedScalarJetPrice J
      (fibreNorm (fun _ : Fin 2 => ((constructedScalarNativeRadius Cw hCw : ℝ) : ℂ)))
      Cw (constructedScalarNativeRadius Cw hCw : ℝ)
    cj := fun _ => 3 * Real.pi ^ 2
    Qj := fun J => 2 * J }

theorem constructedScalarFibreConstants_positive (seed : ScalarConstants)
    (Cw : ℝ) (hCw : 0 ≤ Cw) :
    0 < (constructedScalarFibreConstants seed Cw hCw).ξ0 ∧
    0 < (constructedScalarFibreConstants seed Cw hCw).Cg ∧
    0 < (constructedScalarFibreConstants seed Cw hCw).g0 ∧
    ∀ J, 0 < (constructedScalarFibreConstants seed Cw hCw).Cj J ∧
      0 < (constructedScalarFibreConstants seed Cw hCw).cj J := by
  refine ⟨div_pos (fibreCoefficientMajorantRadius_pos hCw) (by norm_num),
    constructedScalarGraphPrice_pos Cw, by norm_num [constructedScalarFibreConstants], ?_⟩
  intro J
  refine ⟨constructedScalarJetPrice_pos J _ _ _, ?_⟩
  change 0 < 3 * Real.pi ^ 2
  positivity

end AVRegularity.CycleWords
end
