-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.ConstructedReflectedFibreGraphNativeLinearGain
import AVRegularity.CycleWords.ConstructedScalarFibreConstants
import AVRegularity.CycleWords.GeometryErrorPieceMassBudget
import AVRegularity.CycleWords.InteriorPulseActualWeakNativeShortPropagation
import AVRegularity.CycleWords.CanonicalGraphCommonDriftWindowDifferenceDecay

@[expose] public noncomputable section

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal NNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! The actual smooth graph satisfies the common scalar jet price. -/

theorem constructedFibreGraph_scalar_jet_bound
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
    (ξ₀ : ℝ)
    (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (lam : ℕ × ℕ → ℝ → ℂ)
    (hgraph : IsFibreGraph (ν / ocMeanFlux α q Λ ζ m ν) G
      (ocCellDrift α q Λ ζ m ν y₀) ξ₀ (fibreCoefficientGraphBound Cw) r lam)
    (ρ : ℝ≥0) (hρ : 0 < ρ)
    (hband : fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ)) < ξ₀) (t : ℝ) (J : ℕ)
    (ξ : Fin 2 → ℂ) (hξ : ξ ∈ Metric.ball 0 ((ρ : ℝ) / 2))
    (f : Vec 2 → ℂ) (hf : ContDiff ℝ (J : ℕ∞) f)
    (he : f =ᵐ[volume.restrict AVenhance.unitCube] cellValue (fibreSeriesJet r ξ) t) :
    cellSobolevNorm J f ≤
      ENNReal.ofReal (constructedScalarJetPrice J
        (fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ))) Cw (ρ : ℝ) *
        peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ (2 * J) * fibreNorm ξ) := by
  have hrad := fibreCoefficientMajorantRadius_pos hCw
  have hCg : 0 ≤ fibreCoefficientGraphBound Cw := by
    unfold fibreCoefficientGraphBound
    positivity
  exact (constructedFibreGraph_smooth_cellSobolev_bound hΛ hζ hν hr y₀ hv V hb
    G hG Cw hCw hw hη0 hη hm ξ₀ (fibreCoefficientGraphBound Cw) hCg r lam hgraph
    ρ hρ hband t J ξ hξ f hf he).trans
      (constructedGraphJetPrice_bound J (fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ)))
        Cw (ρ : ℝ) (ν / ocMeanFlux α q Λ ζ m ν) (fibreNorm ξ) (fibreNorm_nonneg ξ))

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleWords

theorem constructedRawFast_same_time_decay (J : ℕ)
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
    (hp₀ : AVenhance.IsZ2Periodic g₀) (t : ℝ)
    (D : ℝ → RawJet2 1 ℂ)
    (hD : MemLp (cellValue D t) 2 (volume.restrict AVenhance.unitCube))
    (hi : cellValue D t =ᵐ[volume.restrict AVenhance.unitCube] g₀) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (J : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      fibreFastPart r lam (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ D t t
        =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm J g₁ ≤
        ((∑ l ∈ Finset.range (J + 1), (Fintype.card (DerivativeWord2 l) : ℝ≥0∞)) *
          ENNReal.ofReal (1 + 4 * Real.sqrt (constructedGraphNativeSquareBudget J R
            (fibreCoefficientGraphBound Cw) Cw η)) * (Fintype.card (JetIndex2 J) : ℝ≥0∞)) *
              cellSobolevNorm J g₀ := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r
  let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
  let initial := finiteSmoothPeriodicHk J g₀ hg₀ hp₀
  have hiv : cellRawTrace D t = torusHkValueCLM initial := by
    apply Lp.ext
    exact (cellRawTrace_ae D t hD).trans (hi.trans
      (finiteSmoothPeriodicHk_value_ae J g₀ hg₀ hp₀).symm)
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := constructedCanonicalFast_entrance_representative J
    hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hdisc g₀ hg₀ hp₀ t
  have hrad := fibreCoefficientMajorantRadius_pos hCw
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := by linarith only [hdisc, hrad]
  have h16 : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16 := by linarith only [hdisc, hrad]
  have hgi := fibreCoefficientFamily_graph_isInverse η Cw hη hCw G hG hv hw ξ hξR
  have hl := (fibreAdjointRowCoefficients_series_memLp_bound η Cw hη hCw G hG hv hw ξ h16 t).1
  have he := fibreFast_native_class_ae r lam ell ξ D t t hD hD
    (hgi.1.2.2.1 t (mem_univ t)).1 hl
  have he' := he.symm
  simp only [intervalIntegral.integral_same, Complex.exp_zero, cellScalarCLM_smul, one_smul, hiv] at he'
  exact ⟨g₁, hg₁, hp₁, he'.trans he₁, hb₁⟩

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
open scoped NNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! Polynomial native smoothing for the actual full finite equation, with its zeroth bound discharged. -/

theorem interiorPulseFibreGraph_coefficient_smooth_rep
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
    obtain ⟨F, hF, hs, _⟩ := interiorPulseFibreGraph_native_frequency_smooth hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw hη0 hη hm ξ₀ Cg hCg r lam hgraph ρ hρ hband t J
    refine ⟨F, ?_, hs.contDiffAt (Metric.ball_mem_nhds (0 : Fin 2 → ℂ) (show (0 : ℝ) < ρ from hρ))⟩
    intro ξ hξ
    have hn : ‖ξ‖ ≤ ρ := le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hξ)
    have hd := (fibreNorm_le_constant_of_norm_le ξ ρ.coe_nonneg hn).trans_lt hband
    exact (hF ξ hξ).1.trans (fibreGraphTrace_eq_nativeSeries hgraph ρ hρ hband ξ hd hn t)
  obtain ⟨f, hf, hp, he⟩ := torusHigher_taylor_coefficients_smooth_representatives c ρ hρ hsum hex p
  exact ⟨f, hf, hp, he.trans (fibreGraphCoefficientClass_ae hgraph ρ hρ hband p t)⟩

/-! Polynomial native smoothing for the actual full finite equation, with its zeroth bound discharged. -/

theorem interiorPulseReflectedFibreGraph_native_frequency_smooth
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
    (hgraph : IsFibreGraph (ν / ocMeanFlux α q Λ ζ m ν) (fun s => G (-s))
      (fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x) ξ₀ Cg r lam)
    (ρ : ℝ≥0) (hρ : 0 < ρ)
    (hband : fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ)) < ξ₀) (t : ℝ) (J : ℕ) :
    ∃ F : (Fin 2 → ℂ) → TorusHk J ℂ,
      (∀ ξ ∈ Metric.ball 0 (ρ : ℝ),
        torusHkValueCLM (F ξ) = cellRawTrace (fibreSeriesJet r ξ) t ∧
        ‖F ξ‖ ≤ Real.sqrt (constructedReflectedGraphNativeSquareBudget J
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
    have hall := interiorPulseReflectedFibreGraph_uniform_native_orders hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R
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

theorem interiorPulseReflectedFibreGraph_native_linear_gain
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
    (hgraph : IsFibreGraph (ν / ocMeanFlux α q Λ ζ m ν) (fun s => G (-s))
      (fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x) ξ₀ Cg r lam)
    (ρ : ℝ≥0) (hρ : 0 < ρ)
    (hband : fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ)) < ξ₀) (t : ℝ) (J : ℕ)
    (ξ : Fin 2 → ℂ) (hξ : ξ ∈ Metric.ball 0 ((ρ : ℝ) / 2)) :
    ∃ U : TorusHk J ℂ, torusHkValueCLM U = cellRawTrace (fibreSeriesJet r ξ) t ∧
      ‖U‖ ≤ (64 * (Real.sqrt (constructedReflectedGraphNativeSquareBudget J
        (fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ))) Cg Cw
        (ν / ocMeanFlux α q Λ ζ m ν)) + ‖torusHigherConstant J 1‖) / (ρ : ℝ)) * fibreNorm ξ := by
  obtain ⟨F, hF, _, hz⟩ := interiorPulseReflectedFibreGraph_native_frequency_smooth hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw hη0 hη hm ξ₀ Cg hCg r lam hgraph ρ hρ hband t J
  let M := Real.sqrt (constructedReflectedGraphNativeSquareBudget J
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

theorem interiorPulseReflectedFibreGraph_exists_smooth_rep
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
    (hgraph : IsFibreGraph (ν / ocMeanFlux α q Λ ζ m ν) (fun s => G (-s))
      (fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x) ξ₀ Cg r lam)
    (hdisc : fibreNorm ξ < ξ₀) (t : ℝ) :
    ∃ f : Vec 2 → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧ AVenhance.IsZ2Periodic f ∧
      f =ᵐ[volume.restrict AVenhance.unitCube] cellValue (fibreSeriesJet r ξ) t := by
  have hall := interiorPulseReflectedFibreGraph_uniform_native_orders hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm ξ₀ Cg hCg r lam hgraph hdisc t
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
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleWords

theorem constructedRawFast_same_time_decay_price (J : ℕ)
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
    (hp₀ : AVenhance.IsZ2Periodic g₀) (t : ℝ)
    (D : ℝ → RawJet2 1 ℂ)
    (hD : MemLp (cellValue D t) 2 (volume.restrict AVenhance.unitCube))
    (hi : cellValue D t =ᵐ[volume.restrict AVenhance.unitCube] g₀) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (J : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      fibreFastPart r lam (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ D t t
        =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm J g₁ ≤
        ENNReal.ofReal (constructedForwardDecayPrice J R Cw * peFactor η ^ (2 * J)) *
          cellSobolevNorm J g₀ := by
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := constructedRawFast_same_time_decay J
    hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hdisc
    g₀ hg₀ hp₀ t D hD hi
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
        ((1 + 4 * Real.sqrt (constructedGraphNativeBaseSquareBudget J R
          (fibreCoefficientGraphBound Cw) Cw)) * peFactor η ^ (2 * J)) *
        (Fintype.card (JetIndex2 J) : ℝ) := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (constructedForwardEntrance_native_price J R Cw η)
            (nativeSobolevWordPrice_nonneg J)) hcard
    _ = constructedForwardEntrancePrice J R Cw * peFactor η ^ (2 * J) := by
      dsimp only [constructedForwardEntrancePrice]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (constructedForwardEntrancePrice_le J R Cw) hpe

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
open scoped NNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! Polynomial native smoothing for the actual full finite equation, with its zeroth bound discharged. -/

theorem interiorPulseFibreGraph_coefficients_native_geometric_bound
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
    obtain ⟨F, hF, hs, _⟩ := interiorPulseFibreGraph_native_frequency_smooth hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw hη0 hη hm ξ₀ Cg hCg r lam hgraph ρ hρ hband t J
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
  obtain ⟨F, hF, hs, _⟩ := interiorPulseFibreGraph_native_frequency_smooth hΛ hζ hν hr y₀ hslot hv V hb
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
open scoped NNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! A full canonical graph with smooth periodic literal Taylor-series values. -/

theorem constructedCanonicalGraph_smooth_value_replacement
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
    (ρ : ℝ≥0) (hρ : 0 < ρ)
    (hband : fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ)) < fibreCoefficientMajorantRadius Cw) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r
    ∃ R : ℕ × ℕ → ℝ → RawJet2 1 ℂ,
      IsFibreGraph η G (ocCellDrift α q Λ ζ m ν y₀)
        (fibreCoefficientMajorantRadius Cw) (fibreCoefficientGraphBound Cw) R lam ∧
      (∀ p t a, R p t a =ᵐ[volume.restrict AVenhance.unitCube] r p t a) ∧
      (∀ ξ t, ((ρ : ℝ) / 2)⁻¹ * ‖ξ‖ < 1 →
        ContDiff ℝ (⊤ : ℕ∞) (cellValue (fibreSeriesJet R ξ) t)) ∧
      (∀ ξ t, AVenhance.IsZ2Periodic (cellValue (fibreSeriesJet R ξ) t)) := by
  dsimp only
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r
  have hg := fibreCoefficientFamily_isFibreGraph η Cw hη0 hη hCw G hG hv hw
  have hrad := fibreCoefficientMajorantRadius_pos hCw
  have hCg : 0 ≤ fibreCoefficientGraphBound Cw := by unfold fibreCoefficientGraphBound; positivity
  have hc : ∀ p, Continuous (cellRawTrace (r p)) := by
    intro p
    have hi := fibreCoefficientFamily_isInverse η Cw hη G hG hv hw p
    exact continuousOn_univ.mp (cellRawTrace_continuous univ (r p)
      (fun t _ => (hi.1.2.2.1 t (mem_univ t)).1) hi.1.2.2.2.2.1)
  obtain ⟨f, hf, hp, he, hs, hsp, hmeas⟩ :=
    constructedFibreGraph_smooth_coefficient_replacement_measurable
      hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw hη0 hη hm
      (fibreCoefficientMajorantRadius Cw) (fibreCoefficientGraphBound Cw) hCg
      r lam hg ρ hρ hband hc
  refine ⟨fibreGraphValueReplacement r f,
    fibreGraph_value_replacement_isFibreGraph r lam hg f hp hmeas he, ?_, ?_, ?_⟩
  · intro p t a
    exact cellValueRepresentativeJet_ae (r p t) (f p t) (he p t) a
  · intro ξ t hξ
    change ContDiff ℝ (⊤ : ℕ∞)
      (fibreSeriesJet (fibreGraphValueReplacement r f) ξ t (valueIndex2 1))
    rw [fibreGraphValueReplacement_series, cellValueRepresentativeJet_value]
    exact hs ξ t hξ
  · intro ξ t
    change AVenhance.IsZ2Periodic
      (fibreSeriesJet (fibreGraphValueReplacement r f) ξ t (valueIndex2 1))
    rw [fibreGraphValueReplacement_series, cellValueRepresentativeJet_value]
    exact hsp ξ t

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! A native periodic entrance gives a polynomially bounded native fast entrance. -/

theorem interiorPulseCanonicalAdjointFast_native_entrance (J : ℕ)
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
  refine ⟨initial - torusHigherScalarCLM J
    (cellComplexPair (torusHkValueCLM initial)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap R0)) Lj, ?_, ?_⟩
  · rw [torusHigher_normalized_projection_value, hLv]
  · exact torusHigher_normalized_projection_norm J initial Lj R0
      3 (2 * Real.sqrt B) hRb hLb

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Actual chart renewal bounds for graded Taylor responses, given the
adjoint weights that the construction supplies. -/

theorem geometryResponse_cover_mass_budget_from_weights
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (Λ : ℕ) (hΛ : 128 ≤ Λ) (D H K J n Kmax qJ : ℕ) (hD : 2 ≤ D)
    (_hK : 1 ≤ K) (hqJ : K + 1 + Kmax ≤ qJ)
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
          weightedFactorialNormSq (n + (J + H) * K) ϖ 0 rstar (Kslot x) (F x)) ≠ ⊤)
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
    ∀ i : Fin P, ∀ j : Fin (J + 1),
      (∑ x, ENNReal.ofReal ((π x)⁻¹) *
        nativeComponentEnergy (responseGrade n J H K j.val (familyDepthRank Fam H x)) ϖ rstar
          (ocPieceStart α q Λ m ν ta (l₀ + i)) (ocPieceEnd α q Λ m ν ta T (l₀ + i))
          (Z i j x) (Zw i j x)) ≤
        (ENNReal.ofReal C) ^ (j.val + 1) * (ENNReal.ofReal ((g * ζr) ^ 2)) ^ j.val *
          ∑ x, ENNReal.ofReal ((π x)⁻¹) *
            weightedFactorialNormSq (n + (J + H) * K) ϖ 0 rstar (Kslot x) (F x) := by
  classical
  let M := n + (J + H) * K
  let CGu := fun r => |CG r|
  obtain ⟨A, hA, hpiece⟩ := geometryResponse_piece_mass_budget_uniform H K J Kmax M n
    (by exact le_rfl) CGu Cw Cenv (fun r => abs_nonneg (CG r))
  let L := cellTransitionMomentBudget Kmax M
  let R := (1 + A) ^ (H + 1)
  have hL : 1 ≤ L := cellTransitionMomentBudget_ge_one Kmax M
  have hR : 1 ≤ R := one_le_pow₀ (by linarith)
  let N := Nat.ceil (CT + 2)
  let C := (2 * R * A * L) ^ N
  have hbase : 1 ≤ 2 * R * A * L := by
    have hRA : 1 ≤ R * A := by nlinarith [mul_nonneg (sub_nonneg.mpr hR) (sub_nonneg.mpr hA)]
    have hRAL : 1 ≤ R * A * L := by nlinarith [mul_nonneg (sub_nonneg.mpr hRA) (sub_nonneg.mpr hL)]
    nlinarith
  have hC : 1 ≤ C := one_le_pow₀ hbase
  refine ⟨C, hC, ?_⟩
  intro ι _ h _ _ _ _ _ _ π hπ Kslot hKslot Φ hΦ M' κ' _hband m hm2 _hmM ν B _hν _hB hφ
    ta T ρs g a B₀ lam l₀ P y₀ cov P' Ctx Fam pc ctx dom hdom hdepth hdesc
    b Θ hΘ hb hrow hcol henv hmeas ϖ ζr rstar hϖ hζr hrstar F hfinite hweights fZ Z Zw hZ hfZ0 hfZ
  have hΛ1 : 1 ≤ Λ := by omega
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ1
  have hE := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m - 1) hΛ1
  have hRT : 0 < Real.sqrt (B * T) := Real.sqrt_pos.mpr (mul_pos cov.pos.2.1 cov.pos.2.2.1)
  have hϖpos : 0 < ϖ := by rw [hϖ]; exact div_pos he hRT
  have hζrpos : 0 ≤ ζr := by rw [hζr]; exact (div_pos hRT hE).le
  have hζr1 : ζr ≤ 1 := by rw [hζr]; exact (div_le_one hE).mpr cov.RE
  have hr : 0 < rstar := by rw [hrstar]; exact div_pos cov.pos.2.2.2 he
  have hr1 : rstar ≤ 1 := by rw [hrstar]; exact (div_le_one he).mpr cov.rho_e
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
  have hcount : P ≤ N := by
    have hh := AVRegularity.Construction.Stream.ocTauPP_pos (α := α) (q := q) (m := m) hΛ1
    have hbP := renewal_piece_count_bound (ocTauPP α q Λ m) ta T CT l₀ P hh
      cov.window.2.1 cov.window.2.2.1 cov.comparable.1
    exact_mod_cast hbP.le.trans (Nat.le_ceil (CT + 2))
  have hRenn : (1 + ENNReal.ofReal A) ^ (H + 1) = ENNReal.ofReal R := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (zero_le_one.trans hA),
      ← ENNReal.ofReal_pow (by linarith : 0 ≤ 1 + A)]
  have hCenn : (2 * ENNReal.ofReal R * ENNReal.ofReal A * ENNReal.ofReal L) ^ N = ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_ofNat (n := 2), ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * R),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * R * A), ← ENNReal.ofReal_pow (by positivity)]
  have hrenew : ∀ i i' : Fin P, i'.val = i.val + 1 → ∀ j : Fin (J + 1), ∀ x,
      weightedFactorialNormSq (responseGrade n J H K j.val (familyDepthRank Fam H x)) ϖ 0 rstar
        (Kslot x) (fZ i' j x) ≤
        ENNReal.ofReal L * nativeComponentEnergy (responseGrade n J H K j.val (familyDepthRank Fam H x))
          ϖ rstar (left i) (right i) (Z i j x) (Zw i j x) := by
    intro i i' hi j x
    have hcent : yc i' = ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ (i.val + 1) := by
      dsimp only [yc]
      rw [hi]
    have hreserve : responseGrade n J H K j.val (familyDepthRank Fam H x) ≤ M := by
      unfold responseGrade M
      have hn : J - j.val + H - familyDepthRank Fam H x ≤ J + H := by omega
      exact Nat.add_le_add_left (Nat.mul_le_mul_right K hn) n
    have hp := cellTransition_polynomial_factorial_energy_reserved α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ
      Φ hΦ m (by omega) hφ l₀ y₀ i.val ϖ
      (responseGrade n J H K j.val (familyDepthRank Fam H x)) M hreserve
      (hKslot x) (Z i j x (right i)) (fZ i' j x) rstar hr.le hr1
      (by simpa only [yc, hcent, left, right] using hfZ i i' hi j x)
    have ht : right i ∈ Set.Icc (left i) (right i) := by
      exact ⟨geometryCover_piece_nonempty hΛ1 cov i, le_rfl⟩
    have hend : weightedFactorialNormSq (responseGrade n J H K j.val (familyDepthRank Fam H x))
        ϖ 0 rstar (Kslot x) (Z i j x (right i)) ≤
        nativeComponentEnergy (responseGrade n J H K j.val (familyDepthRank Fam H x))
          ϖ rstar (left i) (right i) (Z i j x) (Zw i j x) := by
      unfold nativeComponentEnergy
      apply le_add_right
      exact le_iSup₂_of_le (right i) ht le_rfl
    exact hp.trans (mul_le_mul_right hend (ENNReal.ofReal L))
  have hbPiece : ∀ i : Fin P,
      (∀ j x q, q + (j.val + familyDepthRank Fam H x) * K ≤ M →
        weightedFactorialNormSq q ϖ 0 rstar (Kslot x) (fZ i j x) ≠ ⊤) →
      ∀ j : Fin (J + 1), (∑ x, ENNReal.ofReal ((π x)⁻¹) *
        nativeComponentEnergy (responseGrade n J H K j.val (familyDepthRank Fam H x))
          ϖ rstar (left i) (right i) (Z i j x) (Zw i j x)) ≤
        ennResponseMassMajorant (ENNReal.ofReal R) (ENNReal.ofReal ((g * ζr) ^ 2))
          (fun l => ENNReal.ofReal A * ∑ x, ENNReal.ofReal ((π x)⁻¹) *
            weightedFactorialNormSq (responseGrade n J H K l (familyDepthRank Fam H x))
              ϖ 0 rstar (Kslot x) (fZ i ⟨min l J, by omega⟩ x)) j.val := by
    intro i hd
    have hsub := ocPiece_interval_subset α q Λ m ν ta T (l₀ + i) hell
    have HC := geometryCover_piece_scalar_inputs Kmax CG hΛ1 hζ hφ (by omega) cov hg0 i
      (fun t _ => G i t 0) (Or.inr rfl)
    have HCu := HC.metric_mono (fun r => le_abs_self (CG r))
    let Gc := metricClamp (ta / ocEll q Λ m ν ^ 2) ((ta + T) / ocEll q Λ m ν ^ 2) (G i)
    have hc : ∀ t ∈ Set.Icc (left i) (right i), Gc t = G i t :=
      fun t ht => metricClamp_of_mem (G i) (hsub ht)
    have hm : ∀ X k l, Measurable (fun t => Gc t X k l) := by
      intro X k l
      exact ((ocCellMetric_joint_contDiff α q Λ m hφ (l₀ + i) ν (yc i) k l).continuous.comp
        ((continuous_const.max (continuous_id.min continuous_const)).prodMk continuous_const)).measurable
    have hs : ∀ t ∈ Set.Icc (left i) (right i), ∀ k l, ContDiff ℝ (K : ℕ) (fun z => Gc t z k l) := by
      intro t ht k l
      rw [hc t ht]
      exact (cov.metric_smooth i t (hsub ht) k l).of_le (by exact_mod_cast (show K ≤ qJ by omega))
    have hj : ∀ᵐ t ∂volume.restrict (Set.Icc (left i) (right i)), ∀ r, 1 ≤ r → r ≤ K → ∀ k l,
        ‖iteratedFDeriv ℝ r (fun z => Gc t z k l) 0‖ ≤ CGu r * g * (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)) ^ r := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      intro r hr hK k l
      rw [hc t ht]
      exact (cov.metric_jets i t (hsub ht) 0 r hr (by omega) k l).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self (CG r)) cov.g_range.1)
          (pow_nonneg (div_nonneg he.le hE.le) r))
    let W : ∀ N, ChartWeights (fun t _ => Gc t 0)
        (ocCellDrift α q Λ ζ m ν (yc i))
        (ta / ocEll q Λ m ν ^ 2) (T / ocEll q Λ m ν ^ 2) ϖ 0 N Cw :=
      fun N => chartWeightsOfEqOn (Classical.choice (hweights i N))
      (fun t ht => by
        have ht' : t ∈ Set.Icc (ta / ocEll q Λ m ν ^ 2) ((ta + T) / ocEll q Λ m ν ^ 2) := by
          simpa only [add_div] using ht
        funext z
        exact congrFun (metricClamp_of_mem (G i) ht') 0)
    have hsol : IsPlaneChainFrom
        (geometryResponseData J K Gc 0
          (ocCellFiber Fam q Λ m ν (yc i) (pc i) (ctx i))
          ((ocEpsilon q Λ (m - 1))⁻¹ • yc i)
          (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)))
        (fun _ x => Kslot x) (left i) (right i)
        (ocCellDrift α q Λ ζ m ν (yc i))
        (fun j x => fZ i j x) (fun _ _ _ => 0) (Z i) (Zw i) := by
      unfold IsPlaneChainFrom
      apply isCoupledWeakSolutionPlane_congr_coeff (hsol := hZ i)
      intro j j' d t ht
      funext z
      have hTaylor : metricTaylor 1 K Gc t 0 z = metricTaylor 1 K (G i) t 0 z := by
        unfold metricTaylor
        rw [hc t ht]
      simp only [planeChainCoefficient, geometryResponseData, hc t ht, hTaylor]
      rfl
    have hwin : ∀ t ∈ Set.Icc (left i) (right i), ∀ Y : Vec 2,
        (ocEll q Λ m ν ^ 2 * t, Y) ∈ dom (pc i) (ctx i) := by
      intro t ht Y
      apply hdom i
      exact ⟨⟨mul_le_mul_of_nonneg_left ht.1 hell.le, mul_le_mul_of_nonneg_left ht.2 hell.le⟩, Set.mem_univ Y⟩
    have hp := hpiece Fam hD hdepth π hπ Kslot hKslot hdesc dom ν
      (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) ρs cov.pos.1 he hE cov.pos.2.2.2
      (K + 1) b (by omega) henv hmeas hb (fun x => (hrow x).trans hΘ) (fun x => (hcol x).trans hΘ)
      (pc i) (ctx i) (ocEll q Λ m ν ^ 2) (left i) (right i) ϖ ζr g hell.ne' hϖpos hscale hζrpos hζr1 hδ
      ((ocEpsilon q Λ (m - 1))⁻¹ • yc i) ((ocEpsilon q Λ m)⁻¹ • yc i) hwin
      (ocCellDrift α q Λ ζ m ν (yc i)) Gc hm hs hj a B₀ lam HCu
      (ta / ocEll q Λ m ν ^ 2) (T / ocEll q Λ m ν ^ 2)
      (ocPieceStart_global_lower α q Λ m ν ta (l₀ + i) hell)
      (by simpa only [add_div] using ocPieceEnd_global_upper α q Λ m ν ta T (l₀ + i) hell)
      (fun q _ => W q) (fZ i) (Z i) (Zw i)
      (by simpa only [← hrstar] using hd) hsol
    simpa only [hRenn, ← hrstar, responseGrade, left, right] using hp
  have hh := gradedResponse_renewal_mass_budget hcount H K J n (familyDepthRank Fam H)
    (familyDepthRank_le Fam H) π hπ Kslot ϖ rstar left right F fZ Z Zw
    (ENNReal.ofReal R) (ENNReal.ofReal A) (ENNReal.ofReal L) (ENNReal.ofReal ((g * ζr) ^ 2))
    (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hR)
    (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hA)
    (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hL)
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    hfinite hfZ0 hrenew hbPiece
  simpa only [hCenn, left, right] using hh

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Full canonical fast smoothing from arbitrary L2 entrances with periodic smooth outputs. -/

theorem constructedCanonicalAdjointFast_native_decay (J : ℕ) (hJ : 1 ≤ J)
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
    (hU : CellWeakHilbertCurve (-b) (-a) U slice (fun t => cellDualDerivative
      ⟨fun s _ => G (-s), fun s x => -ocCellDrift α q Λ ζ m ν y₀ (-s) x,
        fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * -ξ i, 0⟩
      (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
      (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t (slice t) 0 0))
    (initial : TorusHk J ℂ)
    (hi :
      let η := ν / ocMeanFlux α q Λ ζ m ν
      let r := fibreCoefficientFamily η Cw hη G hG hv hw
      let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
      let c := cellComplexPair (U (-b)) (cellFiberCLM Complex.conjCLE.toContinuousLinearMap
        (cellRawTrace (fibreSeriesJet r ξ) b + cellConstantCLM 1))
      U (-b) - cellScalarCLM c (cellSourceSlice ell b) = torusHkValueCLM initial) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r
    let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
    let c := cellComplexPair (U (-b)) (cellFiberCLM Complex.conjCLE.toContinuousLinearMap
      (cellRawTrace (fibreSeriesJet r ξ) b + cellConstantCLM 1))
    let δ₀ := constructedNativeSmoothingTime J R 0 Cw η
    let P := (Real.exp 1 * (2 * Real.exp 1) / (δ₀ / (J : ℝ))) ^ J
    ∃ W : TorusHk J ℂ, torusHkValueCLM W =
      U (-a) - cellScalarCLM c (cellScalarCLM
        (Complex.exp (∫ τ in a..b, fibreSeriesC lam ξ τ)) (cellSourceSlice ell a)) ∧
      ‖W‖ ^ 2 ≤ (Real.exp (6 * Real.pi ^ 2) * (Real.exp 1 + P * Real.exp
        (cellFullZerothGrowth η Cw (fun i => -ξ i) 0))) *
        Real.exp (-(6 * Real.pi ^ 2) * (b - a)) * ‖initial‖ ^ 2 := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
  let D := fibreAdjointGraphRaw η Cw hη G hG hv hw ξ
  let k := fibreSeriesC (fibreAdjointNormalizationCoefficients η Cw hη G hG hv hw) ξ b
  let pair := cellComplexPair (U (-b)) (cellFiberCLM Complex.conjCLE.toContinuousLinearMap
    (cellRawTrace (fibreSeriesJet r ξ) b + cellConstantCLM 1))
  let phase := fun τ => Complex.exp (∫ s in -b..τ,
    fibreAdjointGraphSymbol η Cw hη G hG hv hw ξ s)
  let w := fun τ => U τ - cellScalarCLM (k * pair) (cellScalarCLM (phase τ)
    (cellRawTrace D τ + cellConstantCLM 1))
  let ws := fun τ => slice τ - cellH1Scalar (k * pair) (cellH1Scalar (phase τ)
    (cellH1Slice D τ + cellH1One))
  have hrad := fibreCoefficientMajorantRadius_pos hCw
  have hdiscR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := by linarith only [hdisc, hrad]
  have h16 : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16 := by linarith only [hdisc, hrad]
  have he := canonicalAdjoint_mode_subtraction_weak η Cw hη0 hη hCw G hG hv hm hw V hb
    ξ hdiscR hab.le U slice hU (k * pair)
  have hgap := canonicalAdjoint_fast_remainder_decay η Cw hη0 hη hCw G hG hv hm hw V hb
    hg hgsmall ξ hdisc hfreq hab.le U slice hU
  have hphase := canonicalAdjoint_row_phase_class η Cw hη0 hη hCw G hG hv hm hw V hb
    ξ h16 hab.le
  have hend : w (-a) = U (-a) - cellScalarCLM pair
      (cellScalarCLM (Complex.exp (∫ τ in a..b,
        fibreSeriesC (fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r) ξ τ))
        (cellSourceSlice ell a)) := by
    dsimp only at hphase
    rw [hphase]
    simp only [cellScalarCLM_smul, smul_smul]
    dsimp only [w, phase, D, k, fibreAdjointGraphPhase]
    simp only [cellScalarCLM_smul, smul_smul]
    congr 2
    ring
  have hi' : w (-b) = torusHkValueCLM initial := by
    dsimp only at hi
    rw [fibreAdjointRow_source_slice η Cw hη hCw G hG hv hw ξ h16 b] at hi
    simpa only [w, phase, intervalIntegral.integral_same, Complex.exp_zero,
      cellScalarCLM_smul, one_smul, smul_smul, mul_one, one_mul, k, pair, r, D, mul_comm] using hi
  have hneg : fibreNorm (fun i => -ξ i) ≤ R := by simpa only [fibreNorm_neg] using hξ
  have hθneg : ∀ i, ‖(Real.sqrt η : ℂ) * -ξ i‖ ≤ R := by
    intro i
    simpa only [mul_neg, norm_neg] using hθ i
  obtain ⟨W, hwv, hwb⟩ := constructedReflectedActualWeak_native_gap_decay J hJ
    hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw (fun i => -ξ i) R hR hneg hθneg
    0 0 (fun _ => by simp) measurable_zero (by linarith : -b < -a) w ws he initial hi'
    (6 * Real.pi ^ 2) (by positivity) (by simpa only [sub_neg_eq_add] using hgap)
  refine ⟨W, hwv.trans hend, ?_⟩
  simpa only [show -a - -b = b - a by ring] using hwb

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The actual canonical dual row has a smooth periodic spatial representative. -/

theorem constructedCanonicalRow_exists_periodic_smooth_rep
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
    (hdisc : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16) (t : ℝ) :
    ∃ f : Vec 2 → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧ AVenhance.IsZ2Periodic f ∧
      f =ᵐ[volume.restrict AVenhance.unitCube]
        fibreSeriesFun (fibreAdjointRowCoefficients (ν / ocMeanFlux α q Λ ζ m ν)
          Cw hη G hG hv hw) ξ t := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let rad := fibreCoefficientMajorantRadius Cw
  let Cg := fibreCoefficientGraphBound Cw
  let r := fibreCoefficientFamily η Cw hη (fun s => G (-s))
    (cellMetric_timeReverse hG) (cellDrift_timeReverse hv)
    (cellDrift_timeReverse_scaled_bound hw)
  let lam := fibreCoefficientSymbol η (fun s => G (-s))
    (fun s x => -ocCellDrift α q Λ ζ m ν y₀ (-s) x) r
  have hg := fibreCoefficientFamily_isFibreGraph η Cw hη0 hη hCw (fun s => G (-s))
    (cellMetric_timeReverse hG) (cellDrift_timeReverse hv)
    (cellDrift_timeReverse_scaled_bound hw)
  have hCg : 0 ≤ Cg := by
    dsimp [Cg, fibreCoefficientGraphBound]
    have hr := (fibreCoefficientMajorantRadius_pos hCw).le
    positivity
  have hξneg : fibreNorm (fun i => -ξ i) ≤ R := by simpa only [fibreNorm_neg] using hξ
  have hθneg : ∀ i, ‖(Real.sqrt η : ℂ) * (-ξ i)‖ ≤ R := by
    intro i
    simpa only [mul_neg, norm_neg] using hθ i
  have hsmall : fibreNorm (fun i => -ξ i) < rad := by
    rw [fibreNorm_neg]
    have hr := fibreCoefficientMajorantRadius_pos hCw
    dsimp [rad]
    linarith only [hdisc, hr]
  obtain ⟨f, hf, hp, he⟩ := constructedReflectedFibreGraph_exists_smooth_rep
    hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw (fun i => -ξ i) R hR hξneg hθneg
    hη0 hη hm rad Cg hCg r lam hg hsmall (-t)
  let c := fibreSeriesC (fibreAdjointNormalizationCoefficients η Cw hη G hG hv hw) ξ t
  refine ⟨fun x => c * (1 + f x), contDiff_const.mul (contDiff_const.add hf), ?_, ?_⟩
  · intro n x
    simp only [hp n x]
  · have hs := fibreAdjointRowCoefficients_series_ae η Cw hη hCw G hG hv hw ξ hdisc t
    filter_upwards [he, hs] with x hx hsx
    rw [fibreAdjointCorrection_series_reverse] at hsx
    change f x = cellValue (fibreAdjointGraphRaw η Cw hη G hG hv hw ξ) (-t) x at hx
    rw [hsx, hx]

end AVRegularity.CycleWords
end
