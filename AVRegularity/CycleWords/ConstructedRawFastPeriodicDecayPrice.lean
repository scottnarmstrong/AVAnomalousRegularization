-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.ConstructedCanonicalFastRoughSmoothing
import AVRegularity.CycleWords.InteriorPulseReflectedActualWeakAllNativeOrders
import AVRegularity.CycleWords.FibreGraphNativeSeries
public import AVRegularity.CycleWords.ConstructedReflectedFibreGraphNativeLinearGain
import AVRegularity.CycleWords.ConstructedScalarFibreConstants
import AVRegularity.CycleEvolution.FibreWordHomogeneousJets
import AVRegularity.CycleWords.InteriorPulseReflectedTracePolynomialSmoothing
import AVRegularity.CycleWords.ConstructedCanonicalRowPeriodicRepresentative
import AVRegularity.CycleWords.CanonicalGraphCommonDriftWindowDifferenceDecay
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleWords

theorem constructedRawAdjointFast_same_time_decay (J : ℕ)
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
    (hD : MemLp (cellValue D (-t)) 2 (volume.restrict AVenhance.unitCube))
    (hi : cellValue D (-t) =ᵐ[volume.restrict AVenhance.unitCube] g₀) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r
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
  let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r
  let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
  let initial := finiteSmoothPeriodicHk J g₀ hg₀ hp₀
  have hiv : cellRawTrace D (-t) = torusHkValueCLM initial := by
    apply Lp.ext
    exact (cellRawTrace_ae D (-t) hD).trans (hi.trans
      (finiteSmoothPeriodicHk_value_ae J g₀ hg₀ hp₀).symm)
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := constructedCanonicalAdjointFast_entrance_representative J
    hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hdisc g₀ hg₀ hp₀ t
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

/-! Full canonical fast smoothing from arbitrary L2 entrances with periodic smooth outputs. -/

theorem interiorPulseCanonicalAdjointFast_native_decay (J : ℕ) (hJ : 1 ≤ J)
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
    (hU : CellWeakHilbertCurve (-b) (-a) U slice (fun t => cellDualDerivative
      ⟨fun s _ => G (-s), fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x,
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
    let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r
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
        fibreSeriesC (fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r) ξ τ))
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
  obtain ⟨W, hwv, hwb⟩ := interiorPulseReflectedActualWeak_native_gap_decay J hJ
    hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw (fun i => -ξ i) R hR hneg hθneg
    0 0 (fun _ => by simp) measurable_zero (by linarith : -b < -a) w ws he initial hi'
    (6 * Real.pi ^ 2) (by positivity) (by simpa only [sub_neg_eq_add] using hgap)
  refine ⟨W, hwv.trans hend, ?_⟩
  simpa only [show -a - -b = b - a by ring] using hwb

theorem interiorPulseRawFast_same_time_decay_price (J : ℕ)
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
        ENNReal.ofReal (constructedForwardDecayPrice J R Cw * peFactor η ^ (2 * J)) *
          cellSobolevNorm J g₀ := by
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := interiorPulseRawFast_same_time_decay J
    hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hdisc
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

/-! Full canonical fast smoothing from arbitrary L2 entrances with periodic smooth outputs. -/

theorem interiorPulseCanonicalAdjointFast_rough_smoothing (J : ℕ)
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
    (hU : CellWeakHilbertCurve (-b) (-a) U slice (fun t => cellDualDerivative
      ⟨fun s _ => G (-s), fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x,
        fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * -ξ i, 0⟩
      (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
      (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t (slice t) 0 0))
 :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r
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
        fibreSeriesC (fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r) ξ τ))
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
  obtain ⟨W, hwv, hwb⟩ := interiorPulseReflectedActualWeak_native_gap_polynomial_smoothing J
    hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw (fun i => -ξ i) R hR hneg hθneg
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
  obtain ⟨g₁, hg₁, hp₁, he₁⟩ := interiorPulseReflectedActualWeak_positive_window_smooth
    hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw (fun i => -ξ i) R hR hneg hθneg
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
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal NNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

theorem constructedCanonicalRow_coefficients_smooth_series_replacement
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
    (fun s x => -ocCellDrift α q Λ ζ m ν y₀ (-s) x) r
  have hg := fibreCoefficientFamily_isFibreGraph η Cw hη0 hη hCw (fun s => G (-s))
    (cellMetric_timeReverse hG) (cellDrift_timeReverse hv) (cellDrift_timeReverse_scaled_bound hw)
  have hrad := fibreCoefficientMajorantRadius_pos hCw
  have hCg : 0 ≤ fibreCoefficientGraphBound Cw := by unfold fibreCoefficientGraphBound; positivity
  have hex : ∀ p t, ∃ f : Vec 2 → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧
      AVenhance.IsZ2Periodic f ∧ f =ᵐ[volume.restrict AVenhance.unitCube] cellValue (r p) (-t) := by
    intro p t
    exact constructedReflectedFibreGraph_coefficient_smooth_rep hΛ hζ hν hr y₀ hv V hb G hG
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
    obtain ⟨U, hU, hUb⟩ := constructedReflectedFibreGraph_coefficients_native_geometric_bound
      hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw hη0 hη hm
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

theorem constructedCanonicalRow_scalar_jet_bound
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
      ENNReal.ofReal (constructedScalarJetPrice J
        (fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ))) Cw (ρ : ℝ) *
        peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ (2 * J) * fibreNorm ξ) := by
  exact (constructedCanonicalRow_smooth_cellSobolev_bound hΛ hζ hν hr y₀ hv V hb
    G hG Cw hCw hw hη0 hη hm ρ hρ hband t J ξ hξ hsmall f hf he).trans
      (constructedRowJetPrice_bound J (fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ)))
        Cw (ρ : ℝ) (ν / ocMeanFlux α q Λ ζ m ν) (fibreNorm ξ) (fibreNorm_nonneg ξ))

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped NNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! A full canonical graph with smooth periodic literal Taylor-series values. -/

theorem interiorPulseCanonicalGraph_smooth_value_replacement
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
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r
    ∃ R : ℕ × ℕ → ℝ → RawJet2 1 ℂ,
      IsFibreGraph η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot)
        (fibreCoefficientMajorantRadius Cw) (fibreCoefficientGraphBound Cw) R lam ∧
      (∀ p t a, R p t a =ᵐ[volume.restrict AVenhance.unitCube] r p t a) ∧
      (∀ ξ t, ((ρ : ℝ) / 2)⁻¹ * ‖ξ‖ < 1 →
        ContDiff ℝ (⊤ : ℕ∞) (cellValue (fibreSeriesJet R ξ) t)) ∧
      (∀ ξ t, AVenhance.IsZ2Periodic (cellValue (fibreSeriesJet R ξ) t)) := by
  dsimp only
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r
  have hg := fibreCoefficientFamily_isFibreGraph η Cw hη0 hη hCw G hG hv hw
  have hrad := fibreCoefficientMajorantRadius_pos hCw
  have hCg : 0 ≤ fibreCoefficientGraphBound Cw := by unfold fibreCoefficientGraphBound; positivity
  have hc : ∀ p, Continuous (cellRawTrace (r p)) := by
    intro p
    have hi := fibreCoefficientFamily_isInverse η Cw hη G hG hv hw p
    exact continuousOn_univ.mp (cellRawTrace_continuous univ (r p)
      (fun t _ => (hi.1.2.2.1 t (mem_univ t)).1) hi.1.2.2.2.2.1)
  obtain ⟨f, hf, hp, he, hs, hsp, hmeas⟩ :=
    interiorPulseFibreGraph_smooth_coefficient_replacement_measurable
      hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw hη0 hη hm
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
open scoped ENNReal
namespace AVRegularity.CycleWords

theorem constructedRawAdjointFast_same_time_decay_price (J : ℕ)
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
    (hD : MemLp (cellValue D (-t)) 2 (volume.restrict AVenhance.unitCube))
    (hi : cellValue D (-t) =ᵐ[volume.restrict AVenhance.unitCube] g₀) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ (J : ℕ∞) g₁ ∧ AVenhance.IsZ2Periodic g₁ ∧
      fibreAdjointFastPart r lam (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ D t t
        =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm J g₁ ≤
        ENNReal.ofReal (constructedAdjointDecayPrice J R Cw * peFactor η ^ (2 * J)) *
          cellSobolevNorm J g₀ := by
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := constructedRawAdjointFast_same_time_decay J
    hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hdisc
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

theorem constructedCanonicalFast_periodic_entrance_decay (J : ℕ) (hJ : 1 ≤ J)
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
    (g₀ : Vec 2 → ℂ) (hg₀ : ContDiff ℝ (J : ℕ∞) g₀)
    (hp₀ : AVenhance.IsZ2Periodic g₀)
    (hi : (U a : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] g₀) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r
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
  let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r
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
  obtain ⟨I, hIv, hIb⟩ := constructedCanonicalFast_native_entrance J hΛ hζ hν hr
    y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hdisc initial a
  have hI : U a - cellScalarCLM c
      (cellRawTrace (fibreSeriesJet r ξ) a + cellConstantCLM 1) = torusHkValueCLM I := by
    simpa only [← hiv] using hIv.symm
  obtain ⟨W, hwv, hwb⟩ := constructedCanonicalFast_native_decay J hJ hΛ hζ hν hr
    y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hg hgsmall hdisc hfreq
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
  obtain ⟨g₁, hg₁, hp₁, he₁⟩ := constructedActualWeak_positive_window_smooth
    hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ 0 0 (fun _ => by simp)
    measurable_zero hab (w a) w ws he rfl
  refine ⟨g₁, hg₁, hp₁, he₁.symm, ?_⟩
  exact torusHigher_periodic_entrance_sobolev_transfer J g₀ g₁ hg₀ hp₀
    (hg₁.of_le (by simp)) W (by rw [hwv]; exact he₁.symm) C hC hW

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The actual canonical dual row has a smooth periodic spatial representative. -/

theorem interiorPulseCanonicalRow_exists_periodic_smooth_rep
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
    (fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x) r
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
  obtain ⟨f, hf, hp, he⟩ := interiorPulseReflectedFibreGraph_exists_smooth_rep
    hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw (fun i => -ξ i) R hR hξneg hθneg
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

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! The full forward producer in the original raw fast-part notation. -/

theorem constructedRawFast_periodic_entrance_decay (J : ℕ) (hJ : 1 ≤ J)
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
    (g₀ : Vec 2 → ℂ) (hg₀ : ContDiff ℝ (J : ℕ∞) g₀)
    (hp₀ : AVenhance.IsZ2Periodic g₀)
    (hi : cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] g₀) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r
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
  let lam := fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀) r
  let ell := fibreAdjointRowCoefficients η Cw hη G hG hv hw
  have hraw := cellRawHomogeneous_to_Hilbert hab.le (fun t _ => G t) hG
    (ocCellDrift α q Λ ζ m ν y₀) V hv.1 hb (fun i => (Real.sqrt η : ℂ) * ξ i) D (by
      simpa only [fibreCoefficients, Pi.zero_apply, neg_zero,
        show (fun _ : ℝ => (0 : ℂ)) = 0 from rfl] using hD)
  have hi' := (cellRawTrace_ae D a (hD.2.2.1 a ⟨le_rfl, hab.le⟩).1).trans hi
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := constructedCanonicalFast_periodic_entrance_decay
    J hJ hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm hg hgsmall
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

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Full canonical fast smoothing from arbitrary L2 entrances with periodic smooth outputs. -/

theorem interiorPulseCanonicalFast_rough_smoothing (J : ℕ)
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
 :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r
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
  let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r
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
  obtain ⟨W, hwv, hwb⟩ := interiorPulseActualWeak_native_gap_polynomial_smoothing J
    hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ 0 0 (fun _ => by simp)
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
  obtain ⟨g₁, hg₁, hp₁, he₁⟩ := interiorPulseActualWeak_positive_window_smooth
    hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ 0 0 (fun _ => by simp)
    measurable_zero hab (w a) w ws he rfl
  refine ⟨g₁, hg₁, hp₁, he₁.symm, ?_⟩
  exact torusHigher_rough_entrance_sobolev_transfer J g₁ (hg₁.of_le (by simp)) W (U a)
    (by rw [hwv]; exact he₁.symm) (13 * C) (mul_nonneg (by norm_num) hC) hW

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! The full forward producer in the original raw fast-part notation. -/

theorem constructedRawFast_periodic_entrance_decay_price (J : ℕ) (hJ : 1 ≤ J)
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
  obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := constructedRawFast_periodic_entrance_decay J hJ
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
    _ = constructedForwardHigherDecayPrice J R Cw * peFactor η ^ (2 * J) *
        Real.exp (-(3 * Real.pi ^ 2) * (b - a)) := by
      have hexp : -(6 * Real.pi ^ 2) * (b - a) / 2 = -(3 * Real.pi ^ 2) * (b - a) := by ring
      rw [hexp]
      dsimp only [constructedForwardHigherDecayPrice]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (constructedForwardHigherDecayPrice_le J R Cw) hpe)
      (Real.exp_nonneg _)

end AVRegularity.CycleWords
end
