-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.ConstructedScalarRowBounds
import AVRegularity.CycleEvolution.CellEnergySpaceRawJetCauchyBound
import AVRegularity.CycleEvolution.FibreAdjointRowPairingNormalization
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! A full finite native energy hierarchy for the actual single-pulse extension. -/

theorem interiorPulseGalerkin_all_order_energy (K N : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) {slot : ℤ} (hslot : Odd slot) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot))
    (V : ℝ) (hb : ∀ t x, ∑ j, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (R : ℝ)
    (hθ : ∀ i, ‖(Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i‖ ≤ R)
    (κ : ℝ → ℂ) (t k : ℝ) (hk : ‖κ t‖ ≤ k) (u : CellGalerkinSpace (E := ℂ) N) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let θ := fun i => (Real.sqrt η : ℂ) * ξ i
    let A := cellGalerkinOperator N (cellGeneratorB
      ⟨fun t _ => G t, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot, θ, κ⟩ hG V hv.1 hb t)
    2 * inner ℝ (cellGalerkinNativeLiftCLM N K (A u)) (cellGalerkinNativeLiftCLM N K u) +
      (1 / 2) * ‖cellGalerkinNativeLiftCLM N (K + 1) u‖ ^ 2 ≤
      constructedAllOrderGrowth K R k η Cw ξ * ‖cellGalerkinNativeLiftCLM N K u‖ ^ 2 := by
  dsimp only
  cases K with
  | zero =>
    change _ + (1 / 2) * ‖cellGalerkinNativeLiftCLM N 1 u‖ ^ 2 ≤ _
    have he := cellFullGalerkin_zeroth_adjacent_energy N (ν / ocMeanFlux α q Λ ζ m ν)
      Cw hCw G hG hv hw V hb ξ κ t k hk u
    simpa only [constructedAllOrderGrowth, torusH0_inner_value,
      cellGalerkinNativeLiftCLM_value, cellGalerkinNativeLiftCLM_one,
      cellGalerkinNativeLiftCLM_zero_norm_sq] using he
  | succ j =>
    have he := interiorPulseGalerkinOperator_higher_energy (by omega : 1 ≤ j + 1) N
      hΛ hζ hν hr y₀ hslot hv V hb G hG
      (fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i) R hθ κ t k hk u
    have hv' := pow_le_pow_left₀ (norm_nonneg (cellGalerkinValue N u))
      (cellGalerkinRangeHigher_value_norm_le (by omega : 1 ≤ j + 1) N u) 2
    have hp := energyGradientDifference_absorb hv' he
    simpa only [constructedAllOrderGrowth,
      cellGalerkinNativeLiftCLM_eq_range (by omega : 1 ≤ j + 1),
      cellGalerkinNativeLiftCLM_eq_range (by omega : 1 ≤ (j + 1) + 1)] using hp

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Polynomial native smoothing for the actual full reflected finite equation, with its zeroth bound discharged. -/

theorem constructedReflectedGalerkin_native_polynomial_smoothing (J N : ℕ)
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
    (κ : ℝ → ℂ) (k : ℝ) (hk : ∀ t, ‖κ t‖ ≤ k)
    {a b : ℝ} (hab : a ≤ b) (y : ℝ → CellGalerkinSpace (E := ℂ) N)
    (hy : StrongTimeRegularity a b y (fun t =>
      cellGalerkinOperator N (cellGeneratorB
        ⟨fun s _ => G (-s), fun s x => -ocCellDrift α q Λ ζ m ν y₀ (-s) x,
          fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
          (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
          (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t) (y t)))

    (hwindow : b - a ≤ 1) (t : ℝ)
    (ht : a + J * constructedNativeSmoothingTime J R k Cw (ν / ocMeanFlux α q Λ ζ m ν) ≤ t)
    (htb : t ≤ b) :
    ‖cellGalerkinNativeLiftCLM N J (y t)‖ ^ 2 ≤
      (Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1) * constructedNativeWindowPrice J R k Cw) ^ J *
        peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ (2 * J) *
        (Real.exp (cellFullZerothGrowth (ν / ocMeanFlux α q Λ ζ m ν) Cw ξ k) *
          ‖cellGalerkinValue N (y a)‖ ^ 2) := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let A := cellFullZerothGrowth η Cw ξ k
  let B := Real.exp A * ‖cellGalerkinValue N (y a)‖ ^ 2
  have hA : 0 ≤ A := cellFullZerothGrowth_nonneg η Cw hCw ξ k ((norm_nonneg _).trans (hk a))
  have hzero : ∀ s ∈ Icc a b, ‖cellGalerkinValue N (y s)‖ ^ 2 ≤ B := by
    intro s hs
    have he := cellFullGalerkin_zeroth_propagation N η Cw hCw (fun s => G (-s)) (cellMetric_timeReverse hG)
      (cellDrift_timeReverse hv) (cellDrift_timeReverse_scaled_bound hw) V
      (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) ξ κ k hk hab y hy s hs
    have hs1 : s - a ≤ 1 := (sub_le_sub_right hs.2 a).trans hwindow
    have hex : Real.exp (A * (s - a)) ≤ Real.exp A :=
      Real.exp_le_exp.mpr (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hs1 hA)
    exact he.trans (by simpa only [B, mul_comm] using mul_le_mul_of_nonneg_left hex (sq_nonneg ‖cellGalerkinValue N (y a)‖))
  have he := constructedReflectedGalerkin_native_smoothing J N hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ k hk hab y hy
    (constructedNativeSmoothingTime J R k Cw η) B
    (constructedNativeSmoothingTime_pos J R k Cw η hR ((norm_nonneg _).trans (hk a)) hCw)
    (mul_nonneg (Real.exp_pos A).le (sq_nonneg _))
    (constructedNativeSmoothingTime_budget J R k Cw η hR ((norm_nonneg _).trans (hk a)) hCw)
    hzero t ht htb
  rw [constructedNativeSmoothingTime_polynomial_price] at he
  exact he

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The actual reconstructed plane trace has the genuine metric and drift weak increment. -/

theorem planeBlochEnergyWeakIncrement {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (C : ℝ) (hCpos : 0 < C) (hC : ∀ t i z, ‖cellDriftTorusSymbol v t i z‖ ≤ C)
    (f : Lp ℂ 2 (volume : Measure (Vec 2)))
    (s t : CellCompactTime a b) (hst : s.val ≤ t.val)
    (test : Lp CellComplexH1 2 centeredPlaneFrequencyMeasure) :
    let F := planeBlochEnergyField hab G hG v V hv.1 hb
      (planeCellBlochTransform centeredPlaneFrequencyBase 1 (by norm_num) f)
    inner ℝ (planeBlochEnergyReconstructedTrace hab G hG v V hv.1 hb f t)
        (cellFrequencyPlaneValue test) -
      inner ℝ (planeBlochEnergyReconstructedTrace hab G hG v V hv.1 hb f s)
        (cellFrequencyPlaneValue test) =
      ∫ r in s.val..t.val,
        -(∑ i : Fin 2, ∑ j : Fin 2, inner ℝ
          (G r i j • cellFrequencyPlaneGradient (cellEnergyTimeFrequencyState hab F r) i)
          (cellFrequencyPlaneGradient test j)) -
        ∑ i : Fin 2, inner ℝ
          (planeMeasurableTorusSymbolMultiplication (cellDriftTorusSymbol v r i)
            (cellDriftTorusSymbol_measurable v hv r i) C (hC r i)
              (cellFrequencyPlaneGradient (cellEnergyTimeFrequencyState hab F r) i))
          (cellFrequencyPlaneValue test) := by
  let F := planeBlochEnergyField hab G hG v V hv.1 hb
    (planeCellBlochTransform centeredPlaneFrequencyBase 1 (by norm_num) f)
  change inner ℝ
      ((planeCellBlochUnitary centeredPlaneFrequencyBase 1 (by norm_num)).symm
        ((cellEnergyTraceAtCLM a b t).compLp F))
      ((planeCellBlochUnitary centeredPlaneFrequencyBase 1 (by norm_num)).symm
        (centeredCellBlochValueField test)) -
    inner ℝ ((planeCellBlochUnitary centeredPlaneFrequencyBase 1 (by norm_num)).symm
        ((cellEnergyTraceAtCLM a b s).compLp F))
      ((planeCellBlochUnitary centeredPlaneFrequencyBase 1 (by norm_num)).symm
        (centeredCellBlochValueField test)) = _
  rw [planeCellBloch_inverse_inner, planeCellBloch_inverse_inner]
  apply (planeBlochEnergyIntegratedIncrement hab G hG v V hv.1 hb _ s t hst test).trans
  exact cellEnergyJointGenerator_planeIntegral hab G hG v hv V hb C hCpos hC F test s t hst

/-! The quiet mean of every public fibre energy solution retains its original time history. -/

theorem cellRaw_quiet_mean_evolution (η Cw : ℝ) (hη : 0 ≤ η) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) {a b : ℝ} (hab : a ≤ b)
    (hquiet : ∀ t ∈ Icc a b, ∀ x, v t x = 0)
    (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc a b) (fibreCoefficients η G v ξ (fun _ => 0))
      (fun _ _ => 0) (fun _ _ => 0) D) :
    cellMean (cellValue D b) =
      Complex.exp (-(η : ℂ) * ∫ t in a..b, fibreQuad (G t) ξ) * cellMean (cellValue D a) := by
  have hh := cellRawHomogeneous_to_Hilbert hab (fun t _ => G t) hG v V hv.1 hb
    (fun j => (Real.sqrt η : ℂ) * ξ j) D (by
      simpa only [fibreCoefficients, neg_zero,
        show (fun _ : ℝ => (0 : ℂ)) = 0 from rfl] using hD)
  have hs := cellWeak_quiet_mean_strongTime hab η Cw hη hCw G hG hv V hb hw ξ
    (cellRawTrace D) (cellH1Slice D) hh hquiet
  have he := complexHomogeneous_strongTime_evolution hab
    (fun t => -(η : ℂ) * fibreQuad (G t) ξ) (fun t => cellMean (cellRawTrace D t))
    (fibreMetricSymbol_intervalIntegrable η G hG ξ a b) hs
  have hm (t : ℝ) (ht : t ∈ Icc a b) :
      cellMean (cellRawTrace D t) = cellMean (cellValue D t) :=
    integral_congr_ae (cellRawTrace_ae D t (hD.2.2.1 t ht).1)
  rw [hm b ⟨hab, le_rfl⟩, hm a ⟨le_rfl, hab⟩, intervalIntegral.integral_const_mul] at he
  exact he

end AVRegularity.CycleWords
end

section
open AVRegularity.CycleEvolution
open scoped NNReal
namespace AVRegularity.CycleWords

/-! A native analytic radius chosen solely from the scaled drift bound. -/

def constructedScalarNativeRadius (Cw : ℝ) (hCw : 0 ≤ Cw) : ℝ≥0 :=
  ⟨fibreCoefficientMajorantRadius Cw / 8,
    (div_pos (fibreCoefficientMajorantRadius_pos hCw) (by norm_num)).le⟩

theorem constructedScalarNativeRadius_pos (Cw : ℝ) (hCw : 0 ≤ Cw) :
    0 < constructedScalarNativeRadius Cw hCw := by
  change 0 < fibreCoefficientMajorantRadius Cw / 8
  exact div_pos (fibreCoefficientMajorantRadius_pos hCw) (by norm_num)

theorem constructedScalarNativeRadius_band (Cw : ℝ) (hCw : 0 ≤ Cw) :
    fibreNorm (fun _ : Fin 2 => ((constructedScalarNativeRadius Cw hCw : ℝ) : ℂ)) <
      fibreCoefficientMajorantRadius Cw := by
  have hr := fibreCoefficientMajorantRadius_pos hCw
  have hb := fibreNorm_le_two_piNorm
    (fun _ : Fin 2 => ((constructedScalarNativeRadius Cw hCw : ℝ) : ℂ))
  simp only [pi_norm_const, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (constructedScalarNativeRadius Cw hCw).coe_nonneg] at hb
  change fibreNorm _ ≤ 2 * (fibreCoefficientMajorantRadius Cw / 8) at hb
  exact hb.trans_lt (by linarith)

theorem constructedScalarCommonRadius_native (Cw : ℝ) (hCw : 0 ≤ Cw) :
    constructedScalarCommonRadius Cw (constructedScalarNativeRadius Cw hCw : ℝ) =
      fibreCoefficientMajorantRadius Cw / 2048 := by
  unfold constructedScalarCommonRadius constructedScalarNativeRadius
  apply min_eq_left
  change fibreCoefficientMajorantRadius Cw / 2048 ≤
    (fibreCoefficientMajorantRadius Cw / 8) / 4
  have hr := fibreCoefficientMajorantRadius_pos hCw
  linarith

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! A given scalar real plane chain has the genuine rough-drift weak Hilbert curve. -/

theorem scalarRealPlaneChain_weakCurve {ι : Type*} [Fintype ι]
    (a b : ℝ) (hab : a ≤ b) (κ : Fin 1 → ι → ℕ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (C : ℝ) (hCpos : 0 < C)
    (hC : ∀ t i z, ‖cellDriftTorusSymbol v t i z‖ ≤ C)
    (f : ∀ p : Fin 1 × ι, PlaneHk Set.univ (κ p.1 p.2) ℝ)
    (u : ∀ p : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) ℝ)
    (w : ∀ p : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) ℝ)
    (hsln : IsCoupledWeakSolutionPlane (h := fun _ : Fin 1 × ι => ℝ) 1 a b v 2
      (fun p => κ p.1 p.2)
      (planeChainCoefficient (geometryScalarData (h := fun _ : ι => ℝ) 2 (fun t _ => G t)) κ)
      f (fun _ _ => 0) (fun _ _ => 0) u w)
    (p : Fin 1 × ι) :
    PlaneWeakHilbertCurve a b (coupledPlaneL2Trace u p) (coupledPlaneH1Slice w p)
      (fun t => planeRealBlochGeneratorDual (G t) v hv t C (hC t)
        (coupledPlaneH1Slice w p t)) := by
  apply coupledWeakSolution_planeWeakHilbertCurve hsln p
  · exact planeRealBlochGeneratorDual_timeMemLp _ G hG v hv C hCpos.le hC _
      (coupledWeakSolution_h1_trace_data hsln p).2.1
  · intro s hs t ht _ φ
    rw [scalarChainTrace_increment (h := fun _ : ι => ℝ) a b hab κ v (fun t _ => G t) f
      (fun _ _ => 0) u w hsln p hs ht φ]
    apply intervalIntegral.integral_congr
    intro r _
    exact (integral_congr_ae (planeRealBlochScalarRawRhs_ae (κ p.1 p.2) (v r) (G r)
      (hG.2.2.1 r 0) (w p r) φ)).symm.trans
      (planeRealBlochGeneratorDual_spatialPair (G r) v hv r C (hC r)
        (coupledPlaneH1Slice w p r) φ).symm

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Every full finite native energy level uses one common short contrast-dependent window. -/

theorem interiorPulseGalerkin_native_window (J N : ℕ)
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
    (κ : ℝ → ℂ) (k : ℝ) (hk : ∀ t, ‖κ t‖ ≤ k)
    {a b : ℝ} (hab : a ≤ b) (y : ℝ → CellGalerkinSpace (E := ℂ) N)
    (hy : StrongTimeRegularity a b y (fun t =>
      cellGalerkinOperator N (cellGeneratorB
        ⟨fun t _ => G t, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot,
          fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩ hG V hv.1 hb t) (y t)))
    (hshort : (constructedNativeWindowPrice J R k Cw * peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ 2) * (b - a) ≤ 1) :
    ∀ K ≤ J,
      ‖cellGalerkinNativeLiftCLM N K (y b)‖ ^ 2 ≤ Real.exp 1 * ‖cellGalerkinNativeLiftCLM N K (y a)‖ ^ 2 ∧
        (∫ t in a..b, ‖cellGalerkinNativeLiftCLM N (K + 1) (y t)‖ ^ 2) ≤
          (2 * Real.exp 1) * ‖cellGalerkinNativeLiftCLM N K (y a)‖ ^ 2 := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let A := constructedNativeWindowPrice J R k Cw * peFactor η ^ 2
  have hk0 : 0 ≤ k := (norm_nonneg _).trans (hk a)
  have hA : 0 ≤ A := mul_nonneg (constructedNativeWindowPrice_pos J R k Cw hR hk0 hCw).le (sq_nonneg _)
  intro K hK
  let : NormedAddCommGroup (TorusHk K ℂ) := inferInstance
  let : InnerProductSpace ℝ (TorusHk K ℂ) := inferInstance
  let : NormedAddCommGroup (TorusHk (K + 1) ℂ) := inferInstance
  let : InnerProductSpace ℝ (TorusHk (K + 1) ℂ) := inferInstance
  apply finiteObservable_short_window_bounds hab hy (cellGalerkinNativeLiftCLM N K)
    (cellGalerkinNativeLiftCLM N (K + 1)) A hA hshort
  apply Filter.Eventually.of_forall
  intro t
  have he := interiorPulseGalerkin_all_order_energy K N hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hθ κ t k (hk t) (y t)
  have hprice : constructedAllOrderGrowth K R k η Cw ξ ≤ A :=
    (constructedAllOrderGrowth_polynomial_bound K R k η Cw ξ hR hk0 hCw hξ hθ).trans
      (mul_le_mul_of_nonneg_right (constructedAllOrderPrice_le_window J K hK R k Cw hR hk0 hCw) (sq_nonneg _))
  exact he.trans (mul_le_mul_of_nonneg_right hprice (sq_nonneg ‖cellGalerkinNativeLiftCLM N K (y t)‖))

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! Fixed coordinates of a divergence-forced Hilbert-valued scalar chain obey the actual forced generator increment. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeScalarCoordinateForced_increment
    (a b : ℝ) (hab : a ≤ b) (κ : Fin 1 → ι → ℕ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (C : ℝ)
    (hC : ∀ t i z, ‖cellDriftTorusSymbol v t i z‖ ≤ C)
    (f : ∀ p : Fin 1 × ι, PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (F : ∀ p : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2)
      (PiLp 2 (fun _ : Fin 2 => h p.2)))
    (u : ∀ p : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (w : ∀ p : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hsln : IsCoupledWeakSolutionPlane (h := fun p : Fin 1 × ι => h p.2) 1 a b v 2
      (fun p => κ p.1 p.2)
      (planeChainCoefficient (geometryScalarData (h := h) 2 (fun t _ => G t)) κ)
      f F (fun _ _ => 0) u w)
    (p : Fin 1 × ι) (e : h p.2) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (φ : PlaneHk Set.univ 1 ℝ) :
    inner ℝ (planeFiberCoordinateCLM e (coupledPlaneL2Trace u p t))
        (planeHkValueOperator 1 φ) -
      inner ℝ (planeFiberCoordinateCLM e (coupledPlaneL2Trace u p s))
        (planeHkValueOperator 1 φ) =
      ∫ r in s..t, inner ℝ
        (planeRealBlochGeneratorDual (G r) v hv r C (hC r)
          (mapPlaneHk (InnerProductSpace.toDual ℝ (h p.2) e)
            (coupledPlaneH1Slice w p r)) +
          planeSourceDual 0 (planeFluxValueOperator (κ p.1 p.2)
            (mapPlaneHk (planeFiberFluxCoordinate e) (F p r)))) φ := by
  rw [planeFiberCoordinate_pair, planeFiberCoordinate_pair]
  have hinj : planeFiberInjectionCLM e (planeHkValueOperator 1 φ) =
      planeHkValueOperator 1
        (mapPlaneHk ((ContinuousLinearMap.id ℝ ℝ).smulRight e) φ) :=
    (planeHkFiberValue 1 _ φ).symm
  rw [hinj, scalarChainTrace_increment a b hab κ v (fun t _ => G t) f
    F u w hsln p hs ht]
  apply intervalIntegral.integral_congr
  intro r _
  have hr := (integral_congr_ae (planeScalarCoordinateForcedRawRhs
    (κ p.1 p.2) e (v r) (fun _ => G r) (w p r) (F p r) φ)).symm
  have hp := planeRealBlochForcedDual_pair (κ p.1 p.2) (G r) (hG.2.2.1 r 0)
    v hv r C (hC r) (mapPlaneHk (InnerProductSpace.toDual ℝ (h p.2) e) (w p r))
    (mapPlaneHk (planeFiberFluxCoordinate e) (F p r)) φ
  simpa only [coupledPlaneH1Slice, planeHkFiberTruncate] using hr.trans hp.symm

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleWords

/-! Exact duality for forward and backward actual scalar plane energy equations. -/

/-- A moving adjoint test reads precisely the actual forcing of the forward equation. -/
theorem planeWeakAdjointPair_forcing {a b s t : ℝ}
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (C : ℝ) (hCpos : 0 < C) (hC : ∀ t i z, ‖cellDriftTorusSymbol v t i z‖ ≤ C)
    (C' : ℝ) (hC'pos : 0 < C')
    (hC' : ∀ t i z, ‖cellDriftTorusSymbol (fun t x => -v t x) t i z‖ ≤ C')
    (u w : ℝ → Lp ℝ 2 (volume : Measure (Vec 2)))
    (slice slice' source : ℝ → PlaneHk Set.univ 1 ℝ)
    (h : PlaneWeakHilbertCurve a b u slice
      (fun r => planeRealBlochGeneratorDual (G r) v hv r C (hC r) (slice r) + source r))
    (h' : PlaneWeakHilbertCurve a b w slice'
      (fun r => -planeRealBlochGeneratorDual (G r) (fun t x => -v t x)
        (AVRegularity.CycleEvolution.cellDrift_neg hv) r C' (hC' r) (slice' r)))
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    inner ℝ (u t) (w t) - inner ℝ (u s) (w s) =
      ∫ r in s..t, inner ℝ (source r) (slice' r) := by
  have he := planeWeakPair_increment h h' hs ht hst
  apply he.trans
  apply intervalIntegral.integral_congr
  intro r _
  dsimp only
  rw [inner_add_left, inner_neg_left, planeRealBlochGeneratorDual_pair,
    planeRealBlochGeneratorDual_pair,
    planeRealBlochGeneratorForm_opposite_drift G hG v hv V hb C hCpos hC C' hC'pos hC']
  ring

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The full finite constructed equation smooths with polynomial contrast cost on a common frequency disc. -/

theorem interiorPulseGalerkin_native_smoothing (J N : ℕ)
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
    (κ : ℝ → ℂ) (k : ℝ) (hk : ∀ t, ‖κ t‖ ≤ k)
    {a b : ℝ} (hab : a ≤ b) (y : ℝ → CellGalerkinSpace (E := ℂ) N)
    (hy : StrongTimeRegularity a b y (fun t =>
      cellGalerkinOperator N (cellGeneratorB
        ⟨fun t _ => G t, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot,
          fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩ hG V hv.1 hb t) (y t)))
    (δ B : ℝ) (hδ : 0 < δ) (hB : 0 ≤ B)
    (hshort : (constructedNativeWindowPrice J R k Cw * peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ 2) * δ ≤ 1)
    (hzero : ∀ t ∈ Icc a b, ‖cellGalerkinValue N (y t)‖ ^ 2 ≤ B)
    (t : ℝ) (ht : a + J * δ ≤ t) (htb : t ≤ b) :
    ‖cellGalerkinNativeLiftCLM N J (y t)‖ ^ 2 ≤
      (Real.exp 1 * (2 * Real.exp 1) / δ) ^ J * B := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let A := constructedNativeWindowPrice J R k Cw * peFactor η ^ 2
  let E := fun K s => ‖cellGalerkinNativeLiftCLM N K (y s)‖ ^ 2
  have hA : 0 ≤ A := mul_nonneg
    (constructedNativeWindowPrice_pos J R k Cw hR ((norm_nonneg _).trans (hk a)) hCw).le (sq_nonneg _)
  have hcontinuous : ContinuousOn y (Icc a b) := by simpa only [uIcc_of_le hab] using hy.ac.continuousOn
  have hlocal (s d : ℝ) (has : a ≤ s) (hsd : s ≤ d) (hdb : d ≤ b) (hds : d - s ≤ δ) :
      ∀ K ≤ J, E K d ≤ Real.exp 1 * E K s ∧
        (∫ u in s..d, E (K + 1) u) ≤ (2 * Real.exp 1) * E K s := by
    have hsub : uIcc s d ⊆ uIcc a b := by
      rw [uIcc_of_le hsd, uIcc_of_le hab]
      intro x hx
      exact ⟨has.trans hx.1, hx.2.trans hdb⟩
    have hsmall : A * (d - s) ≤ 1 := (mul_le_mul_of_nonneg_left hds hA).trans hshort
    exact interiorPulseGalerkin_native_window J N hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ k hk
      hsd y (hy.mono hsub) hsmall
  apply continuous_energy_short_window_polynomial_price E (2 * Real.exp 1) (Real.exp 1) B a b δ J
    hδ (by positivity) (Real.exp_pos 1).le
    (fun K _ => ((cellGalerkinNativeLiftCLM N K).continuous.comp_continuousOn hcontinuous).norm.pow 2)
    (fun s hs => by simpa only [E, cellGalerkinNativeLiftCLM_zero_norm_sq] using hzero s hs) hB
    (fun K hK s has hsb => (hlocal s (s + δ) has (by linarith only [hδ]) hsb
      (by simp only [add_sub_cancel_left, le_refl]) K (by omega)).2)
    (fun K _ hK s d has hsd hdb hds => (hlocal s d has hsd hdb hds K hK).1) t ht htb

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleWords

/-! Genuine real plane weak Hilbert curves for the rough metric generator are unique. -/

theorem planeRealBlochWeakCurve_unique {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (C : ℝ) (hCpos : 0 < C) (hC : ∀ t i z, ‖cellDriftTorusSymbol v t i z‖ ≤ C)
    (u u' : ℝ → Lp ℝ 2 (volume : Measure (Vec 2)))
    (w w' : ℝ → PlaneHk Set.univ 1 ℝ)
    (hu : PlaneWeakHilbertCurve a b u w
      (fun t => planeRealBlochGeneratorDual (G t) v hv t C (hC t) (w t)))
    (hu' : PlaneWeakHilbertCurve a b u' w'
      (fun t => planeRealBlochGeneratorDual (G t) v hv t C (hC t) (w' t)))
    (hinit : u a = u' a) : ∀ t ∈ Icc a b, u t = u' t := by
  apply planeWeakHilbert_unique_of_nonpositive_difference hab hu hu' hinit
  exact Filter.Eventually.of_forall (fun t => by
    rw [← map_sub]
    exact mul_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 2)
      (planeRealBlochGeneratorDual_nonpositive G hG v hv V hb C hCpos hC t (w t - w' t)))

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The reconstructed plane evolution tested against every real plane H1 carrier. -/

theorem planeBlochEnergyRealWeakIncrement {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (C : ℝ) (hCpos : 0 < C) (hC : ∀ t i z, ‖cellDriftTorusSymbol v t i z‖ ≤ C)
    (f : Lp ℂ 2 (volume : Measure (Vec 2)))
    (s t : CellCompactTime a b) (hst : s.val ≤ t.val)
    (φ : PlaneHk Set.univ 1 ℝ) :
    let F := planeBlochEnergyField hab G hG v V hv.1 hb
      (planeCellBlochTransform centeredPlaneFrequencyBase 1 (by norm_num) f)
    inner ℝ (planeComplexRealPartL2
      (planeBlochEnergyReconstructedTrace hab G hG v V hv.1 hb f t))
      (AVRegularity.CoupledEnergyPlane.Fourier.planeHkValueOperator 1 φ) -
    inner ℝ (planeComplexRealPartL2
      (planeBlochEnergyReconstructedTrace hab G hG v V hv.1 hb f s))
      (AVRegularity.CoupledEnergyPlane.Fourier.planeHkValueOperator 1 φ) =
    ∫ r in s.val..t.val,
      -(∑ i : Fin 2, ∑ j : Fin 2, inner ℝ
        (planeComplexRealPartL2
          (G r i j • cellFrequencyPlaneGradient (cellEnergyTimeFrequencyState hab F r) i))
        (planeRealH1TestGradient φ j)) -
      ∑ i : Fin 2, inner ℝ
        (planeComplexRealPartL2
          (planeMeasurableTorusSymbolMultiplication (cellDriftTorusSymbol v r i)
            (cellDriftTorusSymbol_measurable v hv r i) C (hC r i)
            (cellFrequencyPlaneGradient (cellEnergyTimeFrequencyState hab F r) i)))
        (AVRegularity.CoupledEnergyPlane.Fourier.planeHkValueOperator 1 φ) := by
  have h := planeBlochEnergyWeakIncrement hab G hG v hv V hb C hCpos hC f s t hst
    (planeRealH1BlochTest φ)
  simp only [planeRealH1BlochTest_value, planeRealH1BlochTest_gradient,
    planeComplexRealPairing] at h
  exact h

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The actual full reflected finite equation has the same native energy hierarchy. -/

theorem interiorPulseReflectedGalerkin_all_order_energy (K N : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) {slot : ℤ} (hslot : Odd slot) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot))
    (V : ℝ) (hb : ∀ t x, ∑ j, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (R : ℝ)
    (hθ : ∀ i, ‖(Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i‖ ≤ R)
    (κ : ℝ → ℂ) (t k : ℝ) (hk : ‖κ t‖ ≤ k) (u : CellGalerkinSpace (E := ℂ) N) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let θ := fun i => (Real.sqrt η : ℂ) * ξ i
    let A := cellGalerkinOperator N (cellGeneratorB
      ⟨fun s _ => G (-s), fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x, θ, κ⟩
      (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
      (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t)
    2 * inner ℝ (cellGalerkinNativeLiftCLM N K (A u)) (cellGalerkinNativeLiftCLM N K u) +
      (1 / 2) * ‖cellGalerkinNativeLiftCLM N (K + 1) u‖ ^ 2 ≤
      constructedAllOrderGrowth K R k η Cw ξ * ‖cellGalerkinNativeLiftCLM N K u‖ ^ 2 := by
  dsimp only
  cases K with
  | zero =>
    change _ + (1 / 2) * ‖cellGalerkinNativeLiftCLM N 1 u‖ ^ 2 ≤ _
    have he := cellFullGalerkin_zeroth_adjacent_energy N (ν / ocMeanFlux α q Λ ζ m ν)
      Cw hCw (fun s => G (-s)) (cellMetric_timeReverse hG)
      (cellDrift_timeReverse hv) (cellDrift_timeReverse_scaled_bound hw) V
      (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) ξ κ t k hk u
    simpa only [constructedAllOrderGrowth, torusH0_inner_value,
      cellGalerkinNativeLiftCLM_value, cellGalerkinNativeLiftCLM_one,
      cellGalerkinNativeLiftCLM_zero_norm_sq] using he
  | succ j =>
    have he := interiorPulseReflectedGalerkinOperator_higher_energy (by omega : 1 ≤ j + 1) N
      hΛ hζ hν hr y₀ hslot hv V hb G hG
      (fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i) R hθ κ t k hk u
    have hv' := pow_le_pow_left₀ (norm_nonneg (cellGalerkinValue N u))
      (cellGalerkinRangeHigher_value_norm_le (by omega : 1 ≤ j + 1) N u) 2
    have hp := energyGradientDifference_absorb hv' he
    simpa only [constructedAllOrderGrowth,
      cellGalerkinNativeLiftCLM_eq_range (by omega : 1 ≤ j + 1),
      cellGalerkinNativeLiftCLM_eq_range (by omega : 1 ≤ (j + 1) + 1)] using hp

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Polynomial native smoothing for the actual full finite equation, with its zeroth bound discharged. -/

theorem interiorPulseFullGalerkin_native_polynomial_smoothing (J N : ℕ)
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
    (κ : ℝ → ℂ) (k : ℝ) (hk : ∀ t, ‖κ t‖ ≤ k)
    {a b : ℝ} (hab : a ≤ b) (y : ℝ → CellGalerkinSpace (E := ℂ) N)
    (hy : StrongTimeRegularity a b y (fun t =>
      cellGalerkinOperator N (cellGeneratorB
        ⟨fun t _ => G t, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot,
          fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩ hG V hv.1 hb t) (y t)))

    (hwindow : b - a ≤ 1) (t : ℝ)
    (ht : a + J * constructedNativeSmoothingTime J R k Cw (ν / ocMeanFlux α q Λ ζ m ν) ≤ t)
    (htb : t ≤ b) :
    ‖cellGalerkinNativeLiftCLM N J (y t)‖ ^ 2 ≤
      (Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1) * constructedNativeWindowPrice J R k Cw) ^ J *
        peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ (2 * J) *
        (Real.exp (cellFullZerothGrowth (ν / ocMeanFlux α q Λ ζ m ν) Cw ξ k) *
          ‖cellGalerkinValue N (y a)‖ ^ 2) := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let A := cellFullZerothGrowth η Cw ξ k
  let B := Real.exp A * ‖cellGalerkinValue N (y a)‖ ^ 2
  have hA : 0 ≤ A := cellFullZerothGrowth_nonneg η Cw hCw ξ k ((norm_nonneg _).trans (hk a))
  have hzero : ∀ s ∈ Icc a b, ‖cellGalerkinValue N (y s)‖ ^ 2 ≤ B := by
    intro s hs
    have he := cellFullGalerkin_zeroth_propagation N η Cw hCw G hG hv hw V hb ξ κ k hk hab y hy s hs
    have hs1 : s - a ≤ 1 := (sub_le_sub_right hs.2 a).trans hwindow
    have hex : Real.exp (A * (s - a)) ≤ Real.exp A :=
      Real.exp_le_exp.mpr (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hs1 hA)
    exact he.trans (by simpa only [B, mul_comm] using mul_le_mul_of_nonneg_left hex (sq_nonneg ‖cellGalerkinValue N (y a)‖))
  have he := interiorPulseGalerkin_native_smoothing J N hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ k hk hab y hy
    (constructedNativeSmoothingTime J R k Cw η) B
    (constructedNativeSmoothingTime_pos J R k Cw η hR ((norm_nonneg _).trans (hk a)) hCw)
    (mul_nonneg (Real.exp_pos A).le (sq_nonneg _))
    (constructedNativeSmoothingTime_budget J R k Cw η hR ((norm_nonneg _).trans (hk a)) hCw)
    hzero t ht htb
  rw [constructedNativeSmoothingTime_polynomial_price] at he
  exact he

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! Actual word components have the precise native forced increment with only an L2 flux source. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

theorem wordChainCoordinateNative_increment (hD : 2 ≤ D)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (letters : Fin N → CycleLetter ι h D) (X0 : Vec 2) (δ : ℝ)
    (κ : Fin (N + 1) → ι → ℕ) (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (C : ℝ)
    (hC : ∀ t i z, ‖cellDriftTorusSymbol v t i z‖ ≤ C)
    (f : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (U : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (Uw : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hsol : IsPlaneChainFrom (wordChainData G letters X0 δ) κ a b v
      (fun j x => f (j, x)) (fun _ _ _ => 0)
      (fun j x => U (j, x)) (fun j x => Uw (j, x)))
    (i : Fin (N + 1) × ι) (S : ℝ → PlaneFluxL2 (h i.2))
    (hS : ∀ᵐ r ∂volume.restrict (Icc a b), ∀ k, S r k =ᵐ[volume]
      fun x => wordChainPreviousFlux letters X0 δ κ (fun p => Uw p r) i r x k)
    (e : h i.2) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (φ : PlaneHk Set.univ 1 ℝ) :
    inner ℝ (planeFiberCoordinateCLM e (coupledPlaneL2Trace U i t)) (planeHkValueOperator 1 φ) -
      inner ℝ (planeFiberCoordinateCLM e (coupledPlaneL2Trace U i s)) (planeHkValueOperator 1 φ) =
      ∫ r in s..t, inner ℝ (planeRealBlochGeneratorDual (G r) v hv r C (hC r)
        (mapPlaneHk (InnerProductSpace.toDual ℝ (h i.2) e) (coupledPlaneH1Slice Uw i r)) +
          planeSourceDual 0 (planeFluxFiberCoordinateCLM e (S r))) φ := by
  let Φ := mapPlaneHk ((ContinuousLinearMap.id ℝ ℝ).smulRight e) φ
  rw [planeFiberCoordinate_pair, planeFiberCoordinate_pair]
  have hinj : planeFiberInjectionCLM e (planeHkValueOperator 1 φ) = planeHkValueOperator 1 Φ :=
    (planeHkFiberValue 1 _ φ).symm
  rw [hinj, coupledPlaneL2Trace_inner, coupledPlaneL2Trace_inner]
  have he := coupledWeakIdentity_fixed_increment (volume.restrict Set.univ) hab v
    (fun r => (U i r).toFunction.jet (valueIndex2 (κ i.1 i.2)))
    ((f i).toFunction.jet (valueIndex2 (κ i.1 i.2))) (Φ.toFunction.jet (valueIndex2 1))
    (fun k => Φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩)
    (fun r k => (Uw i r).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩)
    (fun r => wordChainRawFlux G letters X0 δ κ (fun p => Uw p r) i r)
    (fun _ => (0 : PlaneHk Set.univ (κ i.1 i.2) (PiLp 2 (fun _ : Fin 2 => h i.2))).toFunction.jet
      (valueIndex2 (κ i.1 i.2)))
    (fun _ => (0 : PlaneHk Set.univ (κ i.1 i.2) (h i.2)).toFunction.jet (valueIndex2 (κ i.1 i.2)))
    (fun r hr => hsol.2.2.2.2 i r hr Φ) hs ht
  simp only [Measure.restrict_univ] at he
  rw [he]
  apply intervalIntegral.integral_congr_ae_restrict
  have hsub : Set.uIoc s t ⊆ Icc a b := by
    rw [uIoc_of_le hst]
    exact fun r hr => ⟨hs.1.trans hr.1.le, hr.2.trans ht.2⟩
  have hSr := ae_restrict_of_ae_restrict_of_subset hsub hS
  filter_upwards [hSr] with r hr
  have hp := planeScalarCoordinateNativeFlux_pair (κ i.1 i.2) e (G r) (hG.2.2.1 r 0)
    v hv r C (hC r) (Uw i r) (S r)
    (wordChainPreviousFlux letters X0 δ κ (fun p => Uw p r) i r) hr φ
  have hraw := integral_congr_ae (wordChainRawSpatialRhs_split hD G letters X0 δ κ v Uw i Φ r)
  simpa only [coupledPlaneH1Slice, Φ] using hraw.trans hp.symm
end

/-! Every fixed fiber coordinate of a forced scalar plane chain is an actual forced real energy curve. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeScalarCoordinateForced_weakCurve
    (a b : ℝ) (hab : a ≤ b) (κ : Fin 1 → ι → ℕ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (C : ℝ) (hCpos : 0 < C)
    (hC : ∀ t i z, ‖cellDriftTorusSymbol v t i z‖ ≤ C)
    (f : ∀ p : Fin 1 × ι, PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (F : ∀ p : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2)
      (PiLp 2 (fun _ : Fin 2 => h p.2)))
    (hF : ∀ p, MemLp (F p) 2 (volume.restrict (Icc a b)))
    (u : ∀ p : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (w : ∀ p : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hsln : IsCoupledWeakSolutionPlane (h := fun p : Fin 1 × ι => h p.2) 1 a b v 2
      (fun p => κ p.1 p.2)
      (planeChainCoefficient (geometryScalarData (h := h) 2 (fun t _ => G t)) κ)
      f F (fun _ _ => 0) u w)
    (p : Fin 1 × ι) (e : h p.2) :
    PlaneWeakHilbertCurve a b
      (fun t => planeFiberCoordinateCLM e (coupledPlaneL2Trace u p t))
      (fun t => mapPlaneHk (InnerProductSpace.toDual ℝ (h p.2) e) (coupledPlaneH1Slice w p t))
      (fun t => planeRealBlochGeneratorDual (G t) v hv t C (hC t)
        (mapPlaneHk (InnerProductSpace.toDual ℝ (h p.2) e) (coupledPlaneH1Slice w p t)) +
        planeSourceDual 0 (planeFluxValueOperator (κ p.1 p.2)
          (mapPlaneHk (planeFiberFluxCoordinate e) (F p t)))) := by
  have hd := coupledWeakSolution_h1_trace_data hsln p
  have hm : MemLp (fun t => mapPlaneHk (InnerProductSpace.toDual ℝ (h p.2) e)
      (coupledPlaneH1Slice w p t)) 2 (volume.restrict (Icc a b)) := by
    simpa only [Function.comp_def, mapPlaneHkOperator_apply] using
      (mapPlaneHkOperator 1 (InnerProductSpace.toDual ℝ (h p.2) e)).comp_memLp' hd.2.1
  have hgen : MemLp (fun t => planeRealBlochGeneratorDual (G t) v hv t C (hC t)
      (mapPlaneHk (InnerProductSpace.toDual ℝ (h p.2) e) (coupledPlaneH1Slice w p t)))
      2 (volume.restrict (Icc a b)) :=
    planeRealBlochGeneratorDual_timeMemLp _ G hG v hv C hCpos.le hC _ hm
  have hFc : MemLp (fun t => mapPlaneHk (planeFiberFluxCoordinate e) (F p t))
      2 (volume.restrict (Icc a b)) := by
    simpa only [Function.comp_def, mapPlaneHkOperator_apply] using
      (mapPlaneHkOperator (κ p.1 p.2) (planeFiberFluxCoordinate e)).comp_memLp' (hF p)
  have hflux := planeFluxValueOperator_memLp (κ p.1 p.2) _ hFc
  have hzero : MemLp (fun _ : ℝ => (0 : Lp ℝ 2 (volume : Measure (Vec 2))))
      2 (volume.restrict (Icc a b)) := MemLp.zero'
  have hsource := planeSourceDual_memLp (fun _ => 0) hzero _ hflux
  refine ⟨(planeFiberCoordinateCLM e).continuous.comp_continuousOn hd.1, hm,
    nativeTime_add_memLp (volume.restrict (Icc a b)) _ _ hgen hsource, ?_, ?_⟩
  · filter_upwards [hd.2.2] with t ht
    rw [ht, planeHkFiberValue]
    rfl
  · intro s hs t ht _ φ
    exact planeScalarCoordinateForced_increment a b hab κ G hG v hv C hC f F u w hsln p e hs ht φ
end

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Every full reflected finite native energy level uses one common short contrast-dependent window. -/

theorem interiorPulseReflectedGalerkin_native_window (J N : ℕ)
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
    (κ : ℝ → ℂ) (k : ℝ) (hk : ∀ t, ‖κ t‖ ≤ k)
    {a b : ℝ} (hab : a ≤ b) (y : ℝ → CellGalerkinSpace (E := ℂ) N)
    (hy : StrongTimeRegularity a b y (fun t =>
      cellGalerkinOperator N (cellGeneratorB
        ⟨fun s _ => G (-s), fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x,
          fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
          (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
          (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t) (y t)))
    (hshort : (constructedNativeWindowPrice J R k Cw * peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ 2) * (b - a) ≤ 1) :
    ∀ K ≤ J,
      ‖cellGalerkinNativeLiftCLM N K (y b)‖ ^ 2 ≤ Real.exp 1 * ‖cellGalerkinNativeLiftCLM N K (y a)‖ ^ 2 ∧
        (∫ t in a..b, ‖cellGalerkinNativeLiftCLM N (K + 1) (y t)‖ ^ 2) ≤
          (2 * Real.exp 1) * ‖cellGalerkinNativeLiftCLM N K (y a)‖ ^ 2 := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let A := constructedNativeWindowPrice J R k Cw * peFactor η ^ 2
  have hk0 : 0 ≤ k := (norm_nonneg _).trans (hk a)
  have hA : 0 ≤ A := mul_nonneg (constructedNativeWindowPrice_pos J R k Cw hR hk0 hCw).le (sq_nonneg _)
  intro K hK
  let : NormedAddCommGroup (TorusHk K ℂ) := inferInstance
  let : InnerProductSpace ℝ (TorusHk K ℂ) := inferInstance
  let : NormedAddCommGroup (TorusHk (K + 1) ℂ) := inferInstance
  let : InnerProductSpace ℝ (TorusHk (K + 1) ℂ) := inferInstance
  apply finiteObservable_short_window_bounds hab hy (cellGalerkinNativeLiftCLM N K)
    (cellGalerkinNativeLiftCLM N (K + 1)) A hA hshort
  apply Filter.Eventually.of_forall
  intro t
  have he := interiorPulseReflectedGalerkin_all_order_energy K N hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hθ κ t k (hk t) (y t)
  have hprice : constructedAllOrderGrowth K R k η Cw ξ ≤ A :=
    (constructedAllOrderGrowth_polynomial_bound K R k η Cw ξ hR hk0 hCw hξ hθ).trans
      (mul_le_mul_of_nonneg_right (constructedAllOrderPrice_le_window J K hK R k Cw hR hk0 hCw) (sq_nonneg _))
  exact he.trans (mul_le_mul_of_nonneg_right hprice (sq_nonneg ‖cellGalerkinNativeLiftCLM N K (y t)‖))

/-! The full reflected finite constructed equation smooths with polynomial contrast cost on a common frequency disc. -/

theorem interiorPulseReflectedGalerkin_native_smoothing (J N : ℕ)
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
    (κ : ℝ → ℂ) (k : ℝ) (hk : ∀ t, ‖κ t‖ ≤ k)
    {a b : ℝ} (hab : a ≤ b) (y : ℝ → CellGalerkinSpace (E := ℂ) N)
    (hy : StrongTimeRegularity a b y (fun t =>
      cellGalerkinOperator N (cellGeneratorB
        ⟨fun s _ => G (-s), fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x,
          fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
          (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
          (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t) (y t)))
    (δ B : ℝ) (hδ : 0 < δ) (hB : 0 ≤ B)
    (hshort : (constructedNativeWindowPrice J R k Cw * peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ 2) * δ ≤ 1)
    (hzero : ∀ t ∈ Icc a b, ‖cellGalerkinValue N (y t)‖ ^ 2 ≤ B)
    (t : ℝ) (ht : a + J * δ ≤ t) (htb : t ≤ b) :
    ‖cellGalerkinNativeLiftCLM N J (y t)‖ ^ 2 ≤
      (Real.exp 1 * (2 * Real.exp 1) / δ) ^ J * B := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let A := constructedNativeWindowPrice J R k Cw * peFactor η ^ 2
  let E := fun K s => ‖cellGalerkinNativeLiftCLM N K (y s)‖ ^ 2
  have hA : 0 ≤ A := mul_nonneg
    (constructedNativeWindowPrice_pos J R k Cw hR ((norm_nonneg _).trans (hk a)) hCw).le (sq_nonneg _)
  have hcontinuous : ContinuousOn y (Icc a b) := by simpa only [uIcc_of_le hab] using hy.ac.continuousOn
  have hlocal (s d : ℝ) (has : a ≤ s) (hsd : s ≤ d) (hdb : d ≤ b) (hds : d - s ≤ δ) :
      ∀ K ≤ J, E K d ≤ Real.exp 1 * E K s ∧
        (∫ u in s..d, E (K + 1) u) ≤ (2 * Real.exp 1) * E K s := by
    have hsub : uIcc s d ⊆ uIcc a b := by
      rw [uIcc_of_le hsd, uIcc_of_le hab]
      intro x hx
      exact ⟨has.trans hx.1, hx.2.trans hdb⟩
    have hsmall : A * (d - s) ≤ 1 := (mul_le_mul_of_nonneg_left hds hA).trans hshort
    exact interiorPulseReflectedGalerkin_native_window J N hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ k hk
      hsd y (hy.mono hsub) hsmall
  apply continuous_energy_short_window_polynomial_price E (2 * Real.exp 1) (Real.exp 1) B a b δ J
    hδ (by positivity) (Real.exp_pos 1).le
    (fun K _ => ((cellGalerkinNativeLiftCLM N K).continuous.comp_continuousOn hcontinuous).norm.pow 2)
    (fun s hs => by simpa only [E, cellGalerkinNativeLiftCLM_zero_norm_sq] using hzero s hs) hB
    (fun K hK s has hsb => (hlocal s (s + δ) has (by linarith only [hδ]) hsb
      (by simp only [add_sub_cancel_left, le_refl]) K (by omega)).2)
    (fun K _ hK s d has hsd hdb hds => (hlocal s d has hsd hdb hds K hK).1) t ht htb

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! The actual word component is a forced native energy curve using its L2 flux source. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

theorem wordChainCoordinateNative_weakCurve (hD : 2 ≤ D)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (letters : Fin N → CycleLetter ι h D) (X0 : Vec 2) (δ : ℝ)
    (κ : Fin (N + 1) → ι → ℕ) (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (C : ℝ) (hCpos : 0 < C)
    (hC : ∀ t i z, ‖cellDriftTorusSymbol v t i z‖ ≤ C)
    (f : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (U : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (Uw : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hsol : IsPlaneChainFrom (wordChainData G letters X0 δ) κ a b v
      (fun j x => f (j, x)) (fun _ _ _ => 0)
      (fun j x => U (j, x)) (fun j x => Uw (j, x)))
    (i : Fin (N + 1) × ι) (S : ℝ → PlaneFluxL2 (h i.2))
    (hSl : MemLp S 2 (volume.restrict (Icc a b)))
    (hS : ∀ᵐ r ∂volume.restrict (Icc a b), ∀ k, S r k =ᵐ[volume]
      fun x => wordChainPreviousFlux letters X0 δ κ (fun p => Uw p r) i r x k)
    (e : h i.2) :
    PlaneWeakHilbertCurve a b
      (fun r => planeFiberCoordinateCLM e (coupledPlaneL2Trace U i r))
      (fun r => mapPlaneHk (InnerProductSpace.toDual ℝ (h i.2) e) (coupledPlaneH1Slice Uw i r))
      (fun r => planeRealBlochGeneratorDual (G r) v hv r C (hC r)
        (mapPlaneHk (InnerProductSpace.toDual ℝ (h i.2) e) (coupledPlaneH1Slice Uw i r)) +
          planeSourceDual 0 (planeFluxFiberCoordinateCLM e (S r))) := by
  have hd := coupledWeakSolution_h1_trace_data hsol i
  have hm : MemLp (fun r => mapPlaneHk (InnerProductSpace.toDual ℝ (h i.2) e)
      (coupledPlaneH1Slice Uw i r)) 2 (volume.restrict (Icc a b)) := by
    simpa only [Function.comp_def, mapPlaneHkOperator_apply] using
      (mapPlaneHkOperator 1 (InnerProductSpace.toDual ℝ (h i.2) e)).comp_memLp' hd.2.1
  have hgen := planeRealBlochGeneratorDual_timeMemLp (volume.restrict (Icc a b))
    G hG v hv C hCpos.le hC _ hm
  have hflux : MemLp (fun r => planeFluxFiberCoordinateCLM e (S r))
      2 (volume.restrict (Icc a b)) := (planeFluxFiberCoordinateCLM e).comp_memLp' hSl
  have hzero : MemLp (fun _ : ℝ => (0 : Lp ℝ 2 (volume : Measure (Vec 2))))
      2 (volume.restrict (Icc a b)) := MemLp.zero'
  have hsource := planeSourceDual_memLp (fun _ => 0) hzero _ hflux
  refine ⟨(planeFiberCoordinateCLM e).continuous.comp_continuousOn hd.1, hm,
    nativeTime_add_memLp (volume.restrict (Icc a b)) _ _ hgen hsource, ?_, ?_⟩
  · filter_upwards [hd.2.2] with r hr
    rw [hr, planeHkFiberValue]
    rfl
  · intro s hs t ht hst φ
    exact wordChainCoordinateNative_increment hD G hG letters X0 δ κ a b hab v hv C hC
      f U Uw hsol i S hS e hs ht hst φ

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Polynomial native smoothing for the actual full reflected finite equation, with its zeroth bound discharged. -/

theorem interiorPulseReflectedGalerkin_native_polynomial_smoothing (J N : ℕ)
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
    (κ : ℝ → ℂ) (k : ℝ) (hk : ∀ t, ‖κ t‖ ≤ k)
    {a b : ℝ} (hab : a ≤ b) (y : ℝ → CellGalerkinSpace (E := ℂ) N)
    (hy : StrongTimeRegularity a b y (fun t =>
      cellGalerkinOperator N (cellGeneratorB
        ⟨fun s _ => G (-s), fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x,
          fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
          (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
          (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t) (y t)))

    (hwindow : b - a ≤ 1) (t : ℝ)
    (ht : a + J * constructedNativeSmoothingTime J R k Cw (ν / ocMeanFlux α q Λ ζ m ν) ≤ t)
    (htb : t ≤ b) :
    ‖cellGalerkinNativeLiftCLM N J (y t)‖ ^ 2 ≤
      (Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1) * constructedNativeWindowPrice J R k Cw) ^ J *
        peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ (2 * J) *
        (Real.exp (cellFullZerothGrowth (ν / ocMeanFlux α q Λ ζ m ν) Cw ξ k) *
          ‖cellGalerkinValue N (y a)‖ ^ 2) := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let A := cellFullZerothGrowth η Cw ξ k
  let B := Real.exp A * ‖cellGalerkinValue N (y a)‖ ^ 2
  have hA : 0 ≤ A := cellFullZerothGrowth_nonneg η Cw hCw ξ k ((norm_nonneg _).trans (hk a))
  have hzero : ∀ s ∈ Icc a b, ‖cellGalerkinValue N (y s)‖ ^ 2 ≤ B := by
    intro s hs
    have he := cellFullGalerkin_zeroth_propagation N η Cw hCw (fun s => G (-s)) (cellMetric_timeReverse hG)
      (cellDrift_timeReverse hv) (cellDrift_timeReverse_scaled_bound hw) V
      (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) ξ κ k hk hab y hy s hs
    have hs1 : s - a ≤ 1 := (sub_le_sub_right hs.2 a).trans hwindow
    have hex : Real.exp (A * (s - a)) ≤ Real.exp A :=
      Real.exp_le_exp.mpr (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hs1 hA)
    exact he.trans (by simpa only [B, mul_comm] using mul_le_mul_of_nonneg_left hex (sq_nonneg ‖cellGalerkinValue N (y a)‖))
  have he := interiorPulseReflectedGalerkin_native_smoothing J N hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ k hk hab y hy
    (constructedNativeSmoothingTime J R k Cw η) B
    (constructedNativeSmoothingTime_pos J R k Cw η hR ((norm_nonneg _).trans (hk a)) hCw)
    (mul_nonneg (Real.exp_pos A).le (sq_nonneg _))
    (constructedNativeSmoothingTime_budget J R k Cw η hR ((norm_nonneg _).trans (hk a)) hCw)
    hzero t ht htb
  rw [constructedNativeSmoothingTime_polynomial_price] at he
  exact he

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! The actual real plane H1 state supplies the full metric and transport weak increment. -/

theorem planeBlochEnergyRealStateIncrement {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (C : ℝ) (hCpos : 0 < C) (hC : ∀ t i z, ‖cellDriftTorusSymbol v t i z‖ ≤ C)
    (f : Lp ℂ 2 (volume : Measure (Vec 2)))
    (s t : CellCompactTime a b) (hst : s.val ≤ t.val)
    (φ : PlaneHk Set.univ 1 ℝ) :
    let F := planeBlochEnergyField hab G hG v V hv.1 hb
      (planeCellBlochTransform centeredPlaneFrequencyBase 1 (by norm_num) f)
    inner ℝ (planeComplexRealPartL2
      (planeBlochEnergyReconstructedTrace hab G hG v V hv.1 hb f t))
      (planeHkValueOperator 1 φ) -
    inner ℝ (planeComplexRealPartL2
      (planeBlochEnergyReconstructedTrace hab G hG v V hv.1 hb f s))
      (planeHkValueOperator 1 φ) =
    ∫ r in s.val..t.val, planeRealBlochGeneratorForm (G r) v hv r C (hC r)
      (cellEnergyPlaneRealH1State hab F r) φ := by
  let F := planeBlochEnergyField hab G hG v V hv.1 hb
    (planeCellBlochTransform centeredPlaneFrequencyBase 1 (by norm_num) f)
  apply (planeBlochEnergyRealWeakIncrement hab G hG v hv V hb C hCpos hC f s t hst φ).trans
  rw [intervalIntegral.integral_of_le hst, intervalIntegral.integral_of_le hst]
  apply integral_congr_ae
  exact (planeRealBlochGeneratorForm_readout hab F G v hv C hC φ).filter_mono
    (ae_mono (Measure.restrict_mono
      (Ioc_subset_Icc_self.trans (Icc_subset_Icc s.property.1 t.property.2)) le_rfl))

end AVRegularity.CycleWords
end
