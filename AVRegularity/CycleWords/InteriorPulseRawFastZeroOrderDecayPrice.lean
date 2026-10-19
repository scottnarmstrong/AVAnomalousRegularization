-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.ConstructedScalarFibreConstants
import AVRegularity.CycleWords.ConstructedCanonicalRowPeriodicRepresentative
import AVRegularity.CycleWords.ConstructedCanonicalFastRoughSmoothing
import AVRegularity.CycleWords.InteriorPulseCanonicalFastPeriodicDecay
import AVRegularity.CycleEvolution.CellEnergySpaceRawJetCauchyBound
import AVRegularity.CycleWords.ConstructedRawFastPeriodicDecayPrice
public import AVRegularity.CycleWords.ConstructedReflectedFibreGraphNativeLinearGain
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Full two-orientation fast decay with a periodic entrance and periodic output. -/

theorem constructedCanonicalAdjointFast_periodic_entrance_decay (J : ℕ) (hJ : 1 ≤ J)
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
    (g₀ : Vec 2 → ℂ) (hg₀ : ContDiff ℝ (J : ℕ∞) g₀)
    (hp₀ : AVenhance.IsZ2Periodic g₀)
    (hi : (U (-b) : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] g₀) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r
    let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
    let c := cellComplexPair (U (-b))
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap
        (cellRawTrace (fibreSeriesJet r ξ) b + cellConstantCLM 1))
    let phase := Complex.exp (∫ τ in a..b, fibreSeriesC lam ξ τ)
    let A := 1 + 3 * (2 * Real.sqrt (constructedReflectedGraphNativeSquareBudget J R
      (fibreCoefficientGraphBound Cw) Cw η))
    let C := (Real.sqrt (constructedNativeGapBasePrice J R 0 Cw (6 * Real.pi ^ 2)) *
      peFactor η ^ J * Real.exp (-(6 * Real.pi ^ 2) * (b - a) / 2)) * A
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (⊤ : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      ((U (-a) - cellScalarCLM c (cellScalarCLM phase
        (cellSourceSlice ell a)) : ComplexCellL2) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm J g₁ ≤
        ((∑ l ∈ Finset.range (J + 1), (Fintype.card (DerivativeWord2 l) : ℝ≥0∞)) *
          ENNReal.ofReal C * (Fintype.card (JetIndex2 J) : ℝ≥0∞)) * cellSobolevNorm J g₀ := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r
  let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
  let c := cellComplexPair (U (-b)) (cellFiberCLM Complex.conjCLE.toContinuousLinearMap
    (cellRawTrace (fibreSeriesJet r ξ) b + cellConstantCLM 1))
  let A := 1 + 3 * (2 * Real.sqrt (constructedReflectedGraphNativeSquareBudget J R
    (fibreCoefficientGraphBound Cw) Cw η))
  let B := constructedNativeGapBasePrice J R 0 Cw (6 * Real.pi ^ 2)
  let C := (Real.sqrt B * peFactor η ^ J *
    Real.exp (-(6 * Real.pi ^ 2) * (b - a) / 2)) * A
  let initial := finiteSmoothPeriodicHk J g₀ hg₀ hp₀
  have hiv : U (-b) = torusHkValueCLM initial := by
    apply Lp.ext
    exact hi.trans (finiteSmoothPeriodicHk_value_ae J g₀ hg₀ hp₀).symm
  obtain ⟨I, hIv, hIb⟩ := constructedCanonicalAdjointFast_native_entrance J hΛ hζ hν hr
    y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hdisc initial b
  have hI : U (-b) - cellScalarCLM c (cellSourceSlice ell b) = torusHkValueCLM I := by
    simpa only [← hiv] using hIv.symm
  obtain ⟨W, hwv, hwb⟩ := constructedCanonicalAdjointFast_native_decay J hJ hΛ hζ hν hr
    y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hg hgsmall hdisc hfreq
    hab U slice hU I hI
  have hneg : fibreNorm (fun i => -ξ i) ≤ R := by simpa only [fibreNorm_neg] using hξ
  have hθneg : ∀ i, ‖(Real.sqrt η : ℂ) * -ξ i‖ ≤ R := by
    intro i
    simpa only [mul_neg, norm_neg] using hθ i
  have hprice := constructedNativeGap_polynomial_price J R 0 Cw η (6 * Real.pi ^ 2)
    hR le_rfl hCw (fun i => -ξ i) hneg hθneg
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
  obtain ⟨g₁, hg₁, hp₁, he₁, _⟩ := constructedCanonicalAdjointFast_rough_smoothing
    J hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hg hgsmall
    hdisc hfreq hab U slice hU
  refine ⟨g₁, hg₁, hp₁, he₁, ?_⟩
  exact torusHigher_periodic_entrance_sobolev_transfer J g₀ g₁ hg₀ hp₀
    (hg₁.of_le (by simp)) W (by rw [hwv]; exact he₁) C hC hW

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! The full forward producer in the original raw fast-part notation. -/

theorem interiorPulseRawFast_periodic_entrance_decay (J : ℕ) (hJ : 1 ≤ J)
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
    (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc a b)
      (fibreCoefficients (ν / ocMeanFlux α q Λ ζ m ν) G
        (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) ξ 0) (fun _ _ => 0) (fun _ _ => 0) D)
    (g₀ : Vec 2 → ℂ) (hg₀ : ContDiff ℝ (J : ℕ∞) g₀)
    (hp₀ : AVenhance.IsZ2Periodic g₀)
    (hi : cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] g₀) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r
    let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
    let C := Real.sqrt (constructedNativeGapBasePrice J R 0 Cw (6 * Real.pi ^ 2)) *
      (1 + 4 * Real.sqrt (constructedGraphNativeBaseSquareBudget J R
        (fibreCoefficientGraphBound Cw) Cw))
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (⊤ : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      fibreFastPart r lam ell ξ D a b =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm J g₁ ≤
        ((∑ l ∈ Finset.range (J + 1), (Fintype.card (DerivativeWord2 l) : ℝ≥0∞)) *
          ENNReal.ofReal (C * peFactor η ^ (2 * J) * Real.exp (-(6 * Real.pi ^ 2) * (b - a) / 2)) *
            (Fintype.card (JetIndex2 J) : ℝ≥0∞)) * cellSobolevNorm J g₀ := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r
  let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
  have hraw := cellRawHomogeneous_to_Hilbert hab.le (fun t _ => G t) hG
    (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) V hv.1 hb (fun i => (Real.sqrt η : ℂ) * ξ i) D (by
      simpa only [fibreCoefficients, Pi.zero_apply, neg_zero,
        show (fun _ : ℝ => (0 : ℂ)) = 0 from rfl] using hD)
  have hi' := (cellRawTrace_ae D a (hD.2.2.1 a ⟨le_rfl, hab.le⟩).1).trans hi
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := interiorPulseCanonicalFast_periodic_entrance_decay
    J hJ hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hg hgsmall
    hdisc hfreq hab (cellRawTrace D) (cellH1Slice D) hraw g₀ hg₀ hp₀ hi'
  have hrad := fibreCoefficientMajorantRadius_pos hCw
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := by linarith only [hdisc, hrad]
  have hξ16 : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16 := by linarith only [hdisc, hrad]
  have hgraph := fibreCoefficientFamily_graph_isInverse η Cw hη hCw G hG hv hw ξ hξR
  have hrow := (fibreAdjointRowCoefficients_series_memLp_bound η Cw hη hCw G hG hv hw ξ hξ16 a).1
  have he := fibreFast_native_class_ae r lam ell ξ D a b
    (hD.2.2.1 a ⟨le_rfl, hab.le⟩).1 (hD.2.2.1 b ⟨hab.le, le_rfl⟩).1
    (hgraph.1.2.2.1 b (mem_univ b)).1 hrow
  refine ⟨g₁, hg₁, hp₁, he.symm.trans he₁, hb₁.trans ?_⟩
  have hc := ENNReal.ofReal_le_ofReal (constructedFastNativeDecay_polynomial_price
    J R (fibreCoefficientGraphBound Cw) Cw η (6 * Real.pi ^ 2) (b - a))
  exact mul_le_mul_left
    (mul_le_mul_left (mul_le_mul_right hc
      (∑ l ∈ Finset.range (J + 1), (Fintype.card (DerivativeWord2 l) : ℝ≥0∞)))
      (Fintype.card (JetIndex2 J) : ℝ≥0∞)) (cellSobolevNorm J g₀)

/-! Full rough fast smoothing in the literal raw notation, with periodic outputs. -/

theorem constructedRawAdjointFast_rough_smoothing (J : ℕ)
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
    (hD : IsCellSolution (Icc (-b) (-a))
      (fibreCoefficients (ν / ocMeanFlux α q Λ ζ m ν) (fun s => G (-s))
        (fun s x => -ocCellDrift α q Λ ζ m ν y₀ (-s) x) (fun i => -ξ i) 0) (fun _ _ => 0) (fun _ _ => 0) D)
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
      fibreAdjointFastPart r lam ell ξ D a b =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm J g₁ ≤
        ((∑ l ∈ Finset.range (J + 1), (Fintype.card (DerivativeWord2 l) : ℝ≥0∞)) *
          ENNReal.ofReal C) * cellL2Norm (cellValue D (-b)) := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r
  let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
  have hraw := cellRawHomogeneous_to_Hilbert (by linarith : -b ≤ -a)
    (fun s _ => G (-s)) (cellMetric_timeReverse hG)
    (fun s x => -ocCellDrift α q Λ ζ m ν y₀ (-s) x) V (cellDrift_timeReverse hv).1
    (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x)
    (fun i => (Real.sqrt η : ℂ) * -ξ i) D (by
      simpa only [fibreCoefficients, Pi.zero_apply, neg_zero,
        show (fun _ : ℝ => (0 : ℂ)) = 0 from rfl] using hD)
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := constructedCanonicalAdjointFast_rough_smoothing
    J hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hg hgsmall
    hdisc hfreq hab (cellRawTrace D) (cellH1Slice D) hraw
  have hrad := fibreCoefficientMajorantRadius_pos hCw
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := by linarith only [hdisc, hrad]
  have hξ16 : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16 := by linarith only [hdisc, hrad]
  have hgraph := fibreCoefficientFamily_graph_isInverse η Cw hη hCw G hG hv hw ξ hξR
  have hrow := (fibreAdjointRowCoefficients_series_memLp_bound η Cw hη hCw G hG hv hw ξ hξ16 a).1
  have he := fibreAdjointFast_native_class_ae r lam ell ξ D a b
    (hD.2.2.1 (-b) ⟨le_rfl, by linarith⟩).1
    (hD.2.2.1 (-a) ⟨by linarith, le_rfl⟩).1
    (hgraph.1.2.2.1 b (mem_univ b)).1 hrow
  refine ⟨g₁, hg₁, hp₁, he.symm.trans he₁, ?_⟩
  rw [cellL2Norm_eq_of_class _ (cellRawTrace D (-b))
    (cellRawTrace_ae D (-b) (hD.2.2.1 (-b) ⟨le_rfl, by linarith⟩).1)]
  exact hb₁

theorem constructedRawAdjointFast_zero_order_decay
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
    (hD : IsCellSolution (Icc (-b) (-a))
      (fibreCoefficients (ν / ocMeanFlux α q Λ ζ m ν) (fun s => G (-s))
        (fun s x => -ocCellDrift α q Λ ζ m ν y₀ (-s) x) (fun i => -ξ i) 0) (fun _ _ => 0) (fun _ _ => 0) D)

    (hi : cellValue D (-b) =ᵐ[volume.restrict AVenhance.unitCube] g₀) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r
    let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
    let B := Real.exp (6 * Real.pi ^ 2) * constructedGapSmoothingBasePrice 0 R 0 Cw *
      Real.exp (constructedAllOrderPrice 0 R 0 Cw)
    let C := 13 * ((Real.sqrt B * peFactor η ^ 0 * Real.exp (-(6 * Real.pi ^ 2) * (b - a) / 2)) *
      (1 + (b - a) ^ (-(0 : ℝ) / 2)))
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (⊤ : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      fibreAdjointFastPart r lam ell ξ D a b =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm 0 g₁ ≤
        ((∑ l ∈ Finset.range (0 + 1), (Fintype.card (DerivativeWord2 l) : ℝ≥0∞)) *
          ENNReal.ofReal C) * cellSobolevNorm 0 g₀ := by
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := constructedRawAdjointFast_rough_smoothing
    0 hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hg hgsmall
    hdisc hfreq hab D hD
  refine ⟨g₁, hg₁, hp₁, he₁, ?_⟩
  rw [cellSobolevNorm_zero_eq g₀ hg₀]
  have hn : cellL2Norm (cellValue D (-b)) = cellL2Norm g₀ := by
    exact eLpNorm_congr_ae hi
  rw [hn] at hb₁
  simpa only [Nat.cast_zero] using hb₁

/-! Full rough fast smoothing in the literal raw notation, with periodic outputs. -/

theorem constructedRawAdjointFast_rough_smoothing_price (J : ℕ)
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
    (hD : IsCellSolution (Icc (-b) (-a))
      (fibreCoefficients (ν / ocMeanFlux α q Λ ζ m ν) (fun s => G (-s))
        (fun s x => -ocCellDrift α q Λ ζ m ν y₀ (-s) x) (fun i => -ξ i) 0) (fun _ _ => 0) (fun _ _ => 0) D)
 :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r
    let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (J : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      fibreAdjointFastPart r lam ell ξ D a b =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm J g₁ ≤
        ENNReal.ofReal (constructedSmoothingPrice J R Cw * peFactor η ^ (2 * J) *
          (1 + (b - a) ^ (-(J : ℝ) / 2)) * Real.exp (-(3 * Real.pi ^ 2) * (b - a))) *
          cellL2Norm (cellValue D (-b)) := by
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := constructedRawAdjointFast_rough_smoothing J hΛ hζ hν hr y₀ hv V hb G hG
    Cw hCw hw ξ R hR hξ hθ hη0 hη hm hg hgsmall hdisc hfreq hab D hD
  refine ⟨g₁, hg₁.of_le (by simp), hp₁, he₁, hb₁.trans ?_⟩
  rw [nativeSobolevWordPrice_mul_ofReal]
  apply mul_le_mul_left
  exact ENNReal.ofReal_le_ofReal (constructedSmoothingPrice_bound J R Cw
    (ν / ocMeanFlux α q Λ ζ m ν) (b - a) (sub_nonneg.mpr hab.le))

/-! The full forward producer in the original raw fast-part notation. -/

theorem interiorPulseRawFast_periodic_entrance_decay_price (J : ℕ) (hJ : 1 ≤ J)
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
    (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc a b)
      (fibreCoefficients (ν / ocMeanFlux α q Λ ζ m ν) G
        (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) ξ 0) (fun _ _ => 0) (fun _ _ => 0) D)
    (g₀ : Vec 2 → ℂ) (hg₀ : ContDiff ℝ (J : ℕ∞) g₀)
    (hp₀ : AVenhance.IsZ2Periodic g₀)
    (hi : cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] g₀) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r
    let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (J : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      fibreFastPart r lam ell ξ D a b =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm J g₁ ≤
        ENNReal.ofReal (constructedForwardDecayPrice J R Cw * peFactor η ^ (2 * J) *
          Real.exp (-(3 * Real.pi ^ 2) * (b - a))) * cellSobolevNorm J g₀ := by
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := interiorPulseRawFast_periodic_entrance_decay J hJ
    hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hg hgsmall
    hdisc hfreq hab D hD g₀ hg₀ hp₀ hi
  refine ⟨g₁, hg₁.of_le (by simp), hp₁, he₁, hb₁.trans ?_⟩
  rw [nativeSobolevReadoutPrice_ofReal]
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  let η := ν / ocMeanFlux α q Λ ζ m ν
  have hpe : 0 ≤ peFactor η ^ (2 * J) := pow_nonneg
    ((by norm_num : (0 : ℝ) ≤ 1).trans (one_le_peFactor η)) _
  calc
    _ = constructedForwardHigherDecayPrice J R Cw * peFactor η ^ (2 * J) *
        Real.exp (-(3 * Real.pi ^ 2) * (b - a)) := by
      have hexp : -(6 * Real.pi ^ 2) * (b - a) / 2 = -(3 * Real.pi ^ 2) * (b - a) := by ring
      rw [hexp]
      dsimp only [constructedForwardHigherDecayPrice]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (constructedForwardHigherDecayPrice_le J R Cw) hpe)
      (Real.exp_nonneg _)

/-! Full rough smoothing for the chosen smooth graph and row, with the common scalar price. -/

theorem constructedSmoothFast_rough_smoothing (J : ℕ)
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

    (ρ : ℝ) (r' : ℕ × ℕ → ℝ → RawJet2 1 ℂ)
    (ell' : ℕ × ℕ → ℝ → Vec 2 → ℂ)
    (her : ∀ p t, cellValue (r' p) t =ᵐ[volume.restrict AVenhance.unitCube]
      cellValue (fibreCoefficientFamily (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw p) t)
    (heell : ∀ p t, ell' p t =ᵐ[volume.restrict AVenhance.unitCube]
      fibreAdjointRowCoefficients (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw p t) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (J : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      fibreFastPart r' lam ell' ξ D a b =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm J g₁ ≤
        ENNReal.ofReal (constructedScalarJetPrice J R Cw ρ * peFactor η ^ (2 * J) *
          (1 + (b - a) ^ (-(J : ℝ) / 2)) * Real.exp (-(3 * Real.pi ^ 2) * (b - a))) *
          cellL2Norm (cellValue D a) := by
  dsimp only
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := constructedRawFast_rough_smoothing_price J
    hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm
    hg hgsmall hdisc hfreq hab D hD
  have hgraph := fibreFastPart_graph_congr_ae
    (fibreCoefficientFamily (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw) r'
    (fibreCoefficientSymbol (ν / ocMeanFlux α q Λ ζ m ν) G
      (ocCellDrift α q Λ ζ m ν y₀)
      (fibreCoefficientFamily (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw))
    (fibreAdjointRowCoefficients (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw)
    (fun p t => (her p t).symm) ξ D a b
  have hrow := fibreFastPart_row_congr_ae r'
    (fibreCoefficientSymbol (ν / ocMeanFlux α q Λ ζ m ν) G
      (ocCellDrift α q Λ ζ m ν y₀)
      (fibreCoefficientFamily (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw))
    (fibreAdjointRowCoefficients (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw) ell'
    (fun p t => (heell p t).symm) ξ D a b
  refine ⟨g₁, hg₁, hp₁, (hgraph.trans hrow).symm.trans he₁, hb₁.trans ?_⟩
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  have ht : 0 ≤ b - a := sub_nonneg.mpr hab.le
  have hp : 0 ≤ 1 + (b - a) ^ (-(J : ℝ) / 2) :=
    add_nonneg (by norm_num) (Real.rpow_nonneg ht _)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (constructedSmoothingPrice_le_scalar J R Cw ρ)
        (pow_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans
          (one_le_peFactor (ν / ocMeanFlux α q Λ ζ m ν))) _)) hp) (Real.exp_pos _).le

/-! The full forward producer in the original raw fast-part notation. -/

theorem constructedRawAdjointFast_periodic_entrance_decay (J : ℕ) (hJ : 1 ≤ J)
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
    (hD : IsCellSolution (Icc (-b) (-a))
      (fibreCoefficients (ν / ocMeanFlux α q Λ ζ m ν) (fun s => G (-s))
        (fun s x => -ocCellDrift α q Λ ζ m ν y₀ (-s) x) (fun i => -ξ i) 0) (fun _ _ => 0) (fun _ _ => 0) D)
    (g₀ : Vec 2 → ℂ) (hg₀ : ContDiff ℝ (J : ℕ∞) g₀)
    (hp₀ : AVenhance.IsZ2Periodic g₀)
    (hi : cellValue D (-b) =ᵐ[volume.restrict AVenhance.unitCube] g₀) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r
    let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
    let C := Real.sqrt (constructedNativeGapBasePrice J R 0 Cw (6 * Real.pi ^ 2)) *
      (1 + 6 * Real.sqrt (constructedGraphNativeBaseSquareBudget J R
        (fibreCoefficientGraphBound Cw) Cw))
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (⊤ : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      fibreAdjointFastPart r lam ell ξ D a b =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm J g₁ ≤
        ((∑ l ∈ Finset.range (J + 1), (Fintype.card (DerivativeWord2 l) : ℝ≥0∞)) *
          ENNReal.ofReal (C * peFactor η ^ (2 * J) * Real.exp (-(6 * Real.pi ^ 2) * (b - a) / 2)) *
            (Fintype.card (JetIndex2 J) : ℝ≥0∞)) * cellSobolevNorm J g₀ := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r
  let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
  have hraw := cellRawHomogeneous_to_Hilbert (by linarith : -b ≤ -a)
    (fun s _ => G (-s)) (cellMetric_timeReverse hG)
    (fun s x => -ocCellDrift α q Λ ζ m ν y₀ (-s) x) V (cellDrift_timeReverse hv).1
    (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x)
    (fun i => (Real.sqrt η : ℂ) * -ξ i) D (by
      simpa only [fibreCoefficients, Pi.zero_apply, neg_zero,
        show (fun _ : ℝ => (0 : ℂ)) = 0 from rfl] using hD)
  have hi' := (cellRawTrace_ae D (-b) (hD.2.2.1 (-b) ⟨le_rfl, by linarith⟩).1).trans hi
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := constructedCanonicalAdjointFast_periodic_entrance_decay
    J hJ hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hg hgsmall
    hdisc hfreq hab (cellRawTrace D) (cellH1Slice D) hraw g₀ hg₀ hp₀ hi'
  have hrad := fibreCoefficientMajorantRadius_pos hCw
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := by linarith only [hdisc, hrad]
  have hξ16 : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16 := by linarith only [hdisc, hrad]
  have hgraph := fibreCoefficientFamily_graph_isInverse η Cw hη hCw G hG hv hw ξ hξR
  have hrow := (fibreAdjointRowCoefficients_series_memLp_bound η Cw hη hCw G hG hv hw ξ hξ16 a).1
  have he := fibreAdjointFast_native_class_ae r lam ell ξ D a b
    (hD.2.2.1 (-b) ⟨le_rfl, by linarith⟩).1
    (hD.2.2.1 (-a) ⟨by linarith, le_rfl⟩).1
    (hgraph.1.2.2.1 b (mem_univ b)).1 hrow
  have hprice := constructedAdjointFastNativeDecay_polynomial_price
    J R (fibreCoefficientGraphBound Cw) Cw η (6 * Real.pi ^ 2) (b - a)
  have hc := ENNReal.ofReal_le_ofReal hprice
  simp only [show ∀ x : ℝ, 3 * (2 * x) = 6 * x by intro x; ring] at hb₁
  refine ⟨g₁, hg₁, hp₁, he.symm.trans he₁, hb₁.trans ?_⟩
  exact mul_le_mul_left
    (mul_le_mul_left (mul_le_mul_right hc
      (∑ l ∈ Finset.range (J + 1), (Fintype.card (DerivativeWord2 l) : ℝ≥0∞)))
      (Fintype.card (JetIndex2 J) : ℝ≥0∞)) (cellSobolevNorm J g₀)

/-! Full rough fast smoothing in the literal raw notation, with periodic outputs. -/

theorem interiorPulseRawFast_rough_smoothing (J : ℕ)
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
    (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc a b)
      (fibreCoefficients (ν / ocMeanFlux α q Λ ζ m ν) G
        (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) ξ 0) (fun _ _ => 0) (fun _ _ => 0) D)
 :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r
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
  let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r
  let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
  have hraw := cellRawHomogeneous_to_Hilbert hab.le (fun t _ => G t) hG
    (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) V hv.1 hb (fun i => (Real.sqrt η : ℂ) * ξ i) D (by
      simpa only [fibreCoefficients, Pi.zero_apply, neg_zero,
        show (fun _ : ℝ => (0 : ℂ)) = 0 from rfl] using hD)
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := interiorPulseCanonicalFast_rough_smoothing
    J hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hg hgsmall
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

/-! The full forward producer in the original raw fast-part notation. -/

theorem constructedRawAdjointFast_periodic_entrance_decay_price (J : ℕ) (hJ : 1 ≤ J)
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
    (hD : IsCellSolution (Icc (-b) (-a))
      (fibreCoefficients (ν / ocMeanFlux α q Λ ζ m ν) (fun s => G (-s))
        (fun s x => -ocCellDrift α q Λ ζ m ν y₀ (-s) x) (fun i => -ξ i) 0) (fun _ _ => 0) (fun _ _ => 0) D)
    (g₀ : Vec 2 → ℂ) (hg₀ : ContDiff ℝ (J : ℕ∞) g₀)
    (hp₀ : AVenhance.IsZ2Periodic g₀)
    (hi : cellValue D (-b) =ᵐ[volume.restrict AVenhance.unitCube] g₀) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r
    let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (J : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      fibreAdjointFastPart r lam ell ξ D a b =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm J g₁ ≤
        ENNReal.ofReal (constructedAdjointDecayPrice J R Cw * peFactor η ^ (2 * J) *
          Real.exp (-(3 * Real.pi ^ 2) * (b - a))) * cellSobolevNorm J g₀ := by
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := constructedRawAdjointFast_periodic_entrance_decay J hJ
    hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hg hgsmall
    hdisc hfreq hab D hD g₀ hg₀ hp₀ hi
  refine ⟨g₁, hg₁.of_le (by simp), hp₁, he₁, hb₁.trans ?_⟩
  rw [nativeSobolevReadoutPrice_ofReal]
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  let η := ν / ocMeanFlux α q Λ ζ m ν
  have hpe : 0 ≤ peFactor η ^ (2 * J) := pow_nonneg
    ((by norm_num : (0 : ℝ) ≤ 1).trans (one_le_peFactor η)) _
  calc
    _ = constructedAdjointHigherDecayPrice J R Cw * peFactor η ^ (2 * J) *
        Real.exp (-(3 * Real.pi ^ 2) * (b - a)) := by
      have hexp : -(6 * Real.pi ^ 2) * (b - a) / 2 = -(3 * Real.pi ^ 2) * (b - a) := by ring
      rw [hexp]
      dsimp only [constructedAdjointHigherDecayPrice]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (constructedAdjointHigherDecayPrice_le J R Cw) hpe)
      (Real.exp_nonneg _)

theorem interiorPulseRawFast_zero_order_decay
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
    (g₀ : Vec 2 → ℂ) (hg₀ : Continuous g₀)
    (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc a b)
      (fibreCoefficients (ν / ocMeanFlux α q Λ ζ m ν) G
        (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) ξ 0) (fun _ _ => 0) (fun _ _ => 0) D)

    (hi : cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] g₀) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r
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
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := interiorPulseRawFast_rough_smoothing
    0 hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hg hgsmall
    hdisc hfreq hab D hD
  refine ⟨g₁, hg₁, hp₁, he₁, ?_⟩
  rw [cellSobolevNorm_zero_eq g₀ hg₀]
  have hn : cellL2Norm (cellValue D a) = cellL2Norm g₀ := by
    exact eLpNorm_congr_ae hi
  rw [hn] at hb₁
  simpa only [Nat.cast_zero] using hb₁

theorem constructedRawAdjointFast_zero_order_decay_price
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
    (hD : IsCellSolution (Icc (-b) (-a))
      (fibreCoefficients (ν / ocMeanFlux α q Λ ζ m ν) (fun s => G (-s))
        (fun s x => -ocCellDrift α q Λ ζ m ν y₀ (-s) x) (fun i => -ξ i) 0) (fun _ _ => 0) (fun _ _ => 0) D)

    (hi : cellValue D (-b) =ᵐ[volume.restrict AVenhance.unitCube] g₀) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r
    let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (0 : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      fibreAdjointFastPart r lam ell ξ D a b =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm 0 g₁ ≤
        ENNReal.ofReal (constructedAdjointDecayPrice 0 R Cw *
          Real.exp (-(3 * Real.pi ^ 2) * (b - a))) * cellSobolevNorm 0 g₀ := by
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := constructedRawAdjointFast_zero_order_decay
    hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hg hgsmall
    hdisc hfreq hab g₀ hg₀ D hD hi
  refine ⟨g₁, hg₁.of_le (by simp), hp₁, he₁, hb₁.trans ?_⟩
  rw [nativeSobolevWordPrice_mul_ofReal]
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = constructedAdjointZeroDecayPrice R Cw * Real.exp (-(3 * Real.pi ^ 2) * (b - a)) := by
      have hexp : -(6 * Real.pi ^ 2) * (b - a) / 2 = -(3 * Real.pi ^ 2) * (b - a) := by ring
      rw [hexp]
      simp only [pow_zero, mul_one, neg_zero, zero_div, Real.rpow_zero]
      dsimp only [constructedAdjointZeroDecayPrice]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (constructedAdjointZeroDecayPrice_le 0 R Cw)
      (Real.exp_nonneg _)

/-! Full rough fast smoothing in the literal raw notation, with periodic outputs. -/

theorem interiorPulseRawFast_rough_smoothing_price (J : ℕ)
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
    (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc a b)
      (fibreCoefficients (ν / ocMeanFlux α q Λ ζ m ν) G
        (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) ξ 0) (fun _ _ => 0) (fun _ _ => 0) D)
 :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r
    let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (J : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      fibreFastPart r lam ell ξ D a b =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm J g₁ ≤
        ENNReal.ofReal (constructedSmoothingPrice J R Cw * peFactor η ^ (2 * J) *
          (1 + (b - a) ^ (-(J : ℝ) / 2)) * Real.exp (-(3 * Real.pi ^ 2) * (b - a))) *
          cellL2Norm (cellValue D a) := by
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := interiorPulseRawFast_rough_smoothing J hΛ hζ hν hr y₀ hslot hv V hb G hG
    Cw hCw hw ξ R hR hξ hθ hη0 hη hm hg hgsmall hdisc hfreq hab D hD
  refine ⟨g₁, hg₁.of_le (by simp), hp₁, he₁, hb₁.trans ?_⟩
  rw [nativeSobolevWordPrice_mul_ofReal]
  apply mul_le_mul_left
  exact ENNReal.ofReal_le_ofReal (constructedSmoothingPrice_bound J R Cw
    (ν / ocMeanFlux α q Λ ζ m ν) (b - a) (sub_nonneg.mpr hab.le))

/-! The full forward producer in the original raw fast-part notation. -/

theorem constructedRawFast_all_time_periodic_decay (J : ℕ)
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
    {a b : ℝ} (hab : a ≤ b)
    (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc a b)
      (fibreCoefficients (ν / ocMeanFlux α q Λ ζ m ν) G
        (ocCellDrift α q Λ ζ m ν y₀) ξ 0) (fun _ _ => 0) (fun _ _ => 0) D)
    (g₀ : Vec 2 → ℂ) (hg₀ : ContDiff ℝ (J : ℕ∞) g₀)
    (hp₀ : AVenhance.IsZ2Periodic g₀)
    (hi : cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] g₀) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r
    let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (J : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      fibreFastPart r lam ell ξ D a b =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm J g₁ ≤
        ENNReal.ofReal (constructedForwardDecayPrice J R Cw * peFactor η ^ (2 * J) *
          Real.exp (-(3 * Real.pi ^ 2) * (b - a))) * cellSobolevNorm J g₀ := by
  by_cases heq : a = b
  · subst b
    have hmem := (hD.2.2.1 a ⟨le_rfl, le_rfl⟩).1
    have h := constructedRawFast_same_time_decay_price J hΛ hζ hν hr y₀ hv V hb G hG
      Cw hCw hw ξ R hR hξ hθ hη0 hη hm hdisc g₀ hg₀ hp₀ a D hmem hi
    simpa only [sub_self, mul_zero, Complex.exp_zero, Real.exp_zero, mul_one] using h
  · have hlt : a < b := lt_of_le_of_ne hab heq
    by_cases hzero : J = 0
    · subst J
      have h := constructedRawFast_zero_order_decay_price hΛ hζ hν hr y₀ hv V hb G hG
        Cw hCw hw ξ R hR hξ hθ hη0 hη hm hg hgsmall hdisc hfreq hlt g₀ hg₀.continuous D hD hi
      simpa only [Nat.mul_zero, Nat.cast_zero, pow_zero, mul_one] using h
    · exact constructedRawFast_periodic_entrance_decay_price J (by omega) hΛ hζ hν hr
        y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hg hgsmall
        hdisc hfreq hlt D hD g₀ hg₀ hp₀ hi

theorem interiorPulseRawFast_zero_order_decay_price
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
    (g₀ : Vec 2 → ℂ) (hg₀ : Continuous g₀)
    (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc a b)
      (fibreCoefficients (ν / ocMeanFlux α q Λ ζ m ν) G
        (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) ξ 0) (fun _ _ => 0) (fun _ _ => 0) D)

    (hi : cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] g₀) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r
    let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (0 : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      fibreFastPart r lam ell ξ D a b =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm 0 g₁ ≤
        ENNReal.ofReal (constructedForwardDecayPrice 0 R Cw *
          Real.exp (-(3 * Real.pi ^ 2) * (b - a))) * cellSobolevNorm 0 g₀ := by
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := interiorPulseRawFast_zero_order_decay
    hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hg hgsmall
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
