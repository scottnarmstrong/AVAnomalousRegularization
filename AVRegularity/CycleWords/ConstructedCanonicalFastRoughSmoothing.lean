-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.InteriorPulseReflectedTracePolynomialSmoothing
import AVRegularity.CycleWords.FibreGraphNativeSeries
import AVRegularity.CycleWords.CanonicalGraphCommonDriftWindowDifferenceDecay
import AVRegularity.CycleWords.ConstructedCanonicalRowPeriodicRepresentative
import AVRegularity.CycleEvolution.FibreWordHomogeneousJets
import AVRegularity.CycleWords.InteriorPulseActualWeakNativeShortPropagation
public import AVRegularity.CycleWords.ConstructedReflectedFibreGraphNativeLinearGain
import AVRegularity.CycleWords.ConstructedScalarFibreConstants
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Full canonical fast smoothing from arbitrary L2 entrances with periodic smooth outputs. -/

theorem constructedCanonicalAdjointFast_rough_smoothing (J : ℕ)
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
 :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r
    let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
    let c := cellComplexPair (U (-b))
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap
        (cellRawTrace (fibreSeriesJet r ξ) b + cellConstantCLM 1))
    let phase := Complex.exp (∫ τ in a..b, fibreSeriesC lam ξ τ)
    let B := Real.exp (6 * Real.pi ^ 2) * constructedGapSmoothingBasePrice J R 0 Cw *
      Real.exp (constructedAllOrderPrice 0 R 0 Cw)
    let C := 13 * ((Real.sqrt B * peFactor η ^ J * Real.exp (-(6 * Real.pi ^ 2) * (b - a) / 2)) *
      (1 + (b - a) ^ (-(J : ℝ) / 2)))
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (⊤ : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      ((U (-a) - cellScalarCLM c (cellScalarCLM phase
        (cellSourceSlice ell a)) : ComplexCellL2) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm J g₁ ≤
        ((∑ l ∈ Finset.range (J + 1), (Fintype.card (DerivativeWord2 l) : ℝ≥0∞)) *
          ENNReal.ofReal C) * ENNReal.ofReal ‖U (-b)‖ := by
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
  let B := Real.exp (6 * Real.pi ^ 2) * constructedGapSmoothingBasePrice J R 0 Cw *
    Real.exp (constructedAllOrderPrice 0 R 0 Cw)
  let C := (Real.sqrt B * peFactor η ^ J * Real.exp (-(6 * Real.pi ^ 2) * (b - a) / 2)) *
    (1 + (b - a) ^ (-(J : ℝ) / 2))
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
  have hinit : ‖w (-b)‖ ≤ 13 * ‖U (-b)‖ := by
    have hh := canonicalAdjointFast_initial_norm_le η Cw hη hCw G hG hv hw ξ hdisc (U (-b)) b
    dsimp only at hh
    rw [fibreAdjointRow_source_slice η Cw hη hCw G hG hv hw ξ h16 b] at hh
    simpa only [w, phase, intervalIntegral.integral_same, Complex.exp_zero,
      cellScalarCLM_smul, one_smul, smul_smul, mul_one, one_mul, k, pair, r, D, mul_comm] using hh
  have hneg : fibreNorm (fun i => -ξ i) ≤ R := by simpa only [fibreNorm_neg] using hξ
  have hθneg : ∀ i, ‖(Real.sqrt η : ℂ) * -ξ i‖ ≤ R := by
    intro i
    simpa only [mul_neg, norm_neg] using hθ i
  obtain ⟨W, hwv, hwb⟩ := constructedReflectedActualWeak_native_gap_polynomial_smoothing J
    hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw (fun i => -ξ i) R hR hneg hθneg
    0 0 (fun _ => by simp) measurable_zero (by linarith : -b < -a) w ws he
    (6 * Real.pi ^ 2) (by positivity) (by simpa only [sub_neg_eq_add] using hgap)
  have hp : 0 ≤ peFactor η := (by norm_num : (0 : ℝ) ≤ 1).trans (one_le_peFactor η)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hW : ‖W‖ ^ 2 ≤ (13 * C) ^ 2 * ‖U (-b)‖ ^ 2 := by
    have hh : ‖W‖ ^ 2 ≤ C ^ 2 * ‖w (-b)‖ ^ 2 := by
      simpa only [show -a - -b = b - a by ring] using hwb
    have hbnd := hh.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hinit 2) (sq_nonneg C))
    convert hbnd using 1
    ring
  obtain ⟨g₁, hg₁, hp₁, he₁⟩ := constructedReflectedActualWeak_positive_window_smooth
    hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw (fun i => -ξ i) R hR hneg hθneg
    0 0 (fun _ => by simp) measurable_zero (by linarith : -b < -a) (w (-b)) w ws he rfl
  refine ⟨g₁, hg₁, hp₁, ?_, ?_⟩
  · rw [← hend]
    exact he₁.symm
  · exact torusHigher_rough_entrance_sobolev_transfer J g₁ (hg₁.of_le (by simp)) W (U (-b))
      (by rw [hwv]; exact he₁.symm) (13 * C) (mul_nonneg (by norm_num) hC) hW

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
open scoped NNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! Literal smooth periodic graph coefficient representatives have a common smooth-series radius. -/

theorem interiorPulseFibreGraph_smooth_coefficient_series
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
  obtain ⟨U, hU, hbU⟩ := interiorPulseFibreGraph_coefficients_native_geometric_bound
    hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw hη0 hη hm ξ₀ Cg hCg r lam
    hgraph ρ hρ hband t J
  refine ⟨U, ?_, hbU⟩
  intro p
  rw [hU p]
  exact (he p).trans (cellRawTrace_ae (r p) t
    (fibreGraphCoefficient_memLp hgraph ρ hρ hband p t)).symm

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Higher full-equation decay of the actual canonical slow remainder. -/

theorem interiorPulseCanonicalFast_native_decay (J : ℕ) (hJ : 1 ≤ J)
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
    let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r
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
  let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r
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
  exact interiorPulseActualWeak_native_gap_decay J hJ hΛ hζ hν hr y₀ hslot hv V hb G hG
    Cw hCw hw ξ R hR hξ hθ 0 0 (fun _ => by simp) measurable_zero hab
    w ws he initial hi' (6 * Real.pi ^ 2) (by positivity) hgap

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
open scoped NNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! Literal smooth periodic graph coefficient representatives have a common smooth-series radius. -/

theorem interiorPulseFibreGraph_smooth_coefficient_replacement
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
    exact interiorPulseFibreGraph_coefficient_smooth_rep hΛ hζ hν hr y₀ hslot hv V hb G hG
      Cw hCw hw hη0 hη hm ξ₀ Cg hCg r lam hgraph ρ hρ hband t p
  choose f hf hp he using hex
  refine ⟨f, hf, hp, he, ?_, ?_⟩
  · intro ξ t hξ
    exact interiorPulseFibreGraph_smooth_coefficient_series hΛ hζ hν hr y₀ hslot hv V hb G hG
      Cw hCw hw hη0 hη hm ξ₀ Cg hCg r lam hgraph ρ hρ hband t f
      (fun p => hf p t) (fun p => hp p t) (fun p => he p t) ξ hξ
  · exact fibreSeriesFun_periodic f hp

/-! Polynomial native smoothing for the actual full finite equation, with its zeroth bound discharged. -/

theorem interiorPulseReflectedFibreGraph_coefficient_smooth_rep
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
    obtain ⟨F, hF, hs, _⟩ := interiorPulseReflectedFibreGraph_native_frequency_smooth hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw hη0 hη hm ξ₀ Cg hCg r lam hgraph ρ hρ hband t J
    refine ⟨F, ?_, hs.contDiffAt (Metric.ball_mem_nhds (0 : Fin 2 → ℂ) (show (0 : ℝ) < ρ from hρ))⟩
    intro ξ hξ
    have hn : ‖ξ‖ ≤ ρ := le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hξ)
    have hd := (fibreNorm_le_constant_of_norm_le ξ ρ.coe_nonneg hn).trans_lt hband
    exact (hF ξ hξ).1.trans (fibreGraphTrace_eq_nativeSeries hgraph ρ hρ hband ξ hd hn t)
  obtain ⟨f, hf, hp, he⟩ := torusHigher_taylor_coefficients_smooth_representatives c ρ hρ hsum hex p
  exact ⟨f, hf, hp, he.trans (fibreGraphCoefficientClass_ae hgraph ρ hρ hband p t)⟩

/-! Literal smooth periodic graph coefficient representatives have a common smooth-series radius. -/

section
local instance interiorPulseGraphSmoothReplacementMeasurableSpace : MeasurableSpace ComplexCellL2 := borel _
local instance interiorPulseGraphSmoothReplacementBorelSpace : BorelSpace ComplexCellL2 := ⟨rfl⟩


theorem interiorPulseFibreGraph_smooth_coefficient_replacement_measurable
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
  obtain ⟨f, hf, hp, he, hs, hsp⟩ := interiorPulseFibreGraph_smooth_coefficient_replacement
    hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw hη0 hη hm ξ₀ Cg hCg r lam hgraph ρ hρ hband
  refine ⟨f, hf, hp, he, hs, hsp, ?_⟩
  intro p
  have hex : ∀ t, ∃ U : TorusHk 2 ℂ, torusHkValueCLM U = cellRawTrace (r p) t := by
    intro t
    obtain ⟨U, hU, _⟩ := interiorPulseFibreGraph_coefficients_native_geometric_bound
      hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw hη0 hη hm ξ₀ Cg hCg r lam hgraph
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
end

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! A native periodic entrance gives a polynomially bounded native fast entrance. -/

theorem interiorPulseCanonicalFast_entrance_representative (J : ℕ)
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
  obtain ⟨f, hf, hpf, hef⟩ := interiorPulseFibreGraph_exists_smooth_rep
    hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm
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
open AVRegularity.CoupledEnergy.Galerkin
open scoped NNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! The actual canonical normalized row has polynomial native higher linear-frequency bounds. -/

theorem constructedCanonicalRow_native_linear_bound
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
    (fun s x => -ocCellDrift α q Λ ζ m ν y₀ (-s) x) r
  have hg := fibreCoefficientFamily_isFibreGraph η Cw hη0 hη hCw (fun s => G (-s))
    (cellMetric_timeReverse hG) (cellDrift_timeReverse hv) (cellDrift_timeReverse_scaled_bound hw)
  have hrad := fibreCoefficientMajorantRadius_pos hCw
  have hCg : 0 ≤ fibreCoefficientGraphBound Cw := by unfold fibreCoefficientGraphBound; positivity
  have hn : (fun i => -ξ i) ∈ Metric.ball 0 ((ρ : ℝ) / 2) := by
    change -ξ ∈ Metric.ball 0 ((ρ : ℝ) / 2)
    simpa only [Metric.mem_ball, dist_zero_right, norm_neg] using hξ
  obtain ⟨U, hU, hbU⟩ := constructedReflectedFibreGraph_native_linear_gain hΛ hζ hν hr
    y₀ hv V hb G hG Cw hCw hw hη0 hη hm
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
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
open scoped NNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! Polynomial native smoothing for the actual full finite equation, with its zeroth bound discharged. -/

theorem interiorPulseReflectedFibreGraph_coefficients_native_geometric_bound
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
    obtain ⟨F, hF, hs, _⟩ := interiorPulseReflectedFibreGraph_native_frequency_smooth hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw hη0 hη hm ξ₀ Cg hCg r lam hgraph ρ hρ hband t J
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
  obtain ⟨F, hF, hs, _⟩ := interiorPulseReflectedFibreGraph_native_frequency_smooth hΛ hζ hν hr y₀ hslot hv V hb
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
open scoped ENNReal NNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! The actual row native price controls any smooth representative's classical Sobolev norm. -/

theorem constructedCanonicalRow_smooth_cellSobolev_bound
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
  obtain ⟨U, hU, hbU⟩ := constructedCanonicalRow_native_linear_bound hΛ hζ hν hr y₀ hv V hb
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
open scoped ENNReal NNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! The actual smooth graph satisfies the common scalar jet price. -/

theorem interiorPulseFibreGraph_scalar_jet_bound
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
    (ξ₀ : ℝ)
    (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (lam : ℕ × ℕ → ℝ → ℂ)
    (hgraph : IsFibreGraph (ν / ocMeanFlux α q Λ ζ m ν) G
      (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) ξ₀ (fibreCoefficientGraphBound Cw) r lam)
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
  exact (interiorPulseFibreGraph_smooth_cellSobolev_bound hΛ hζ hν hr y₀ hslot hv V hb
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

theorem interiorPulseRawFast_same_time_decay (J : ℕ)
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
    (hD : MemLp (cellValue D t) 2 (volume.restrict AVenhance.unitCube))
    (hi : cellValue D t =ᵐ[volume.restrict AVenhance.unitCube] g₀) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r
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
  let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r
  let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
  let initial := finiteSmoothPeriodicHk J g₀ hg₀ hp₀
  have hiv : cellRawTrace D t = torusHkValueCLM initial := by
    apply Lp.ext
    exact (cellRawTrace_ae D t hD).trans (hi.trans
      (finiteSmoothPeriodicHk_value_ae J g₀ hg₀ hp₀).symm)
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := interiorPulseCanonicalFast_entrance_representative J
    hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hdisc g₀ hg₀ hp₀ t
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

/-! A native periodic entrance gives a polynomially bounded native fast entrance. -/

theorem constructedCanonicalAdjointFast_entrance_representative (J : ℕ)
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
  obtain ⟨f, hf, hpf, hef⟩ := constructedCanonicalRow_exists_periodic_smooth_rep
    hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm h16 t
  have hLRep : (torusHkValueCLM Lj : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] f := by
    rw [hLv]
    have hmem := (fibreAdjointRowCoefficients_series_memLp_bound η Cw hη hCw G hG hv hw ξ h16 t).1
    exact (cellSourceSlice_ae _ t hmem).trans hef.symm
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := torusHigher_periodic_projection_representative J
    g₀ f hg₀ hp₀ (hf.of_le (by simp)) hpf Lj hLRep R0 3 (2 * Real.sqrt B) hRb hLb
  refine ⟨g₁, hg₁, hp₁, ?_, hb₁⟩
  simpa only [hLv] using he₁

/-! Full canonical fast smoothing from arbitrary L2 entrances with periodic smooth outputs. -/

theorem constructedCanonicalFast_rough_smoothing (J : ℕ)
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
 :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r
    let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
    let c := cellComplexPair (U a)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellSourceSlice ell a))
    let phase := Complex.exp (∫ τ in a..b, fibreSeriesC lam ξ τ)
    let B := Real.exp (6 * Real.pi ^ 2) * constructedGapSmoothingBasePrice J R 0 Cw *
      Real.exp (constructedAllOrderPrice 0 R 0 Cw)
    let C := 13 * ((Real.sqrt B * peFactor η ^ J * Real.exp (-(6 * Real.pi ^ 2) * (b - a) / 2)) *
      (1 + (b - a) ^ (-(J : ℝ) / 2)))
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (⊤ : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      ((U b - cellScalarCLM c (cellScalarCLM phase
        (cellRawTrace (fibreSeriesJet r ξ) b + cellConstantCLM 1)) : ComplexCellL2) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm J g₁ ≤
        ((∑ l ∈ Finset.range (J + 1), (Fintype.card (DerivativeWord2 l) : ℝ≥0∞)) *
          ENNReal.ofReal C) * ENNReal.ofReal ‖U a‖ := by
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
  let B := Real.exp (6 * Real.pi ^ 2) * constructedGapSmoothingBasePrice J R 0 Cw *
    Real.exp (constructedAllOrderPrice 0 R 0 Cw)
  let C := (Real.sqrt B * peFactor η ^ J * Real.exp (-(6 * Real.pi ^ 2) * (b - a) / 2)) *
    (1 + (b - a) ^ (-(J : ℝ) / 2))
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
  have hinit : ‖w a‖ ≤ 13 * ‖U a‖ := by
    simpa only [w, phase, intervalIntegral.integral_same, Complex.exp_zero,
      cellScalarCLM_smul, one_smul] using
      canonicalFast_initial_norm_le η Cw hη hCw G hG hv hw ξ hdisc (U a) a
  obtain ⟨W, hwv, hwb⟩ := constructedActualWeak_native_gap_polynomial_smoothing J
    hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ 0 0 (fun _ => by simp)
    measurable_zero hab w ws he (6 * Real.pi ^ 2) (by positivity) hgap
  have hp : 0 ≤ peFactor η := (by norm_num : (0 : ℝ) ≤ 1).trans (one_le_peFactor η)
  have hτ : 0 ≤ b - a := (sub_pos.mpr hab).le
  have hT := Real.rpow_nonneg hτ (-(J : ℝ) / 2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hW : ‖W‖ ^ 2 ≤ (13 * C) ^ 2 * ‖U a‖ ^ 2 := by
    have hh := hwb.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hinit 2) (sq_nonneg C))
    convert hh using 1
    ring
  obtain ⟨g₁, hg₁, hp₁, he₁⟩ := constructedActualWeak_positive_window_smooth
    hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ 0 0 (fun _ => by simp)
    measurable_zero hab (w a) w ws he rfl
  refine ⟨g₁, hg₁, hp₁, he₁.symm, ?_⟩
  exact torusHigher_rough_entrance_sobolev_transfer J g₁ (hg₁.of_le (by simp)) W (U a)
    (by rw [hwv]; exact he₁.symm) (13 * C) (mul_nonneg (by norm_num) hC) hW

end AVRegularity.CycleWords
end
