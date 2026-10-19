-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.CanonicalGraphCommonDriftWindowDifferenceDecay
import AVRegularity.CycleWords.PlaneBlochEnergyRealStateIncrement
import AVRegularity.CycleWords.InteriorPulseActualWeakNativeShortPropagation
import AVRegularity.CycleWords.InteriorPulseReflectedTracePolynomialSmoothing
public import AVRegularity.CycleWords.ConstructedActualWeakNativeGapDecay
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! A proved L2 gap and periodic native entrance yield higher full-equation decay. -/

theorem interiorPulseReflectedActualWeak_native_gap_decay (J : ℕ) (hJ : 1 ≤ J)
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
    (hκ : Measurable κ) {a b : ℝ} (hab : a < b)
    (U : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (hU : CellWeakHilbertCurve a b U slice (fun t => cellDualDerivative
      ⟨fun s _ => G (-s), fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x,
        fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
      (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
        (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t (slice t) 0 0))
    (initial : TorusHk J ℂ) (hi : U a = torusHkValueCLM initial)
    (γ : ℝ) (hγ : 0 ≤ γ)
    (hgap : ∀ s ∈ Icc a b, ‖U s‖ ^ 2 ≤ Real.exp (-γ * (s - a)) * ‖U a‖ ^ 2) :
    let δ₀ := constructedNativeSmoothingTime J R k Cw (ν / ocMeanFlux α q Λ ζ m ν)
    let P := (Real.exp 1 * (2 * Real.exp 1) / (δ₀ / (J : ℝ))) ^ J
    ∃ W : TorusHk J ℂ, torusHkValueCLM W = U b ∧ ‖W‖ ^ 2 ≤
      (Real.exp γ * (Real.exp 1 + P * Real.exp
        (cellFullZerothGrowth (ν / ocMeanFlux α q Λ ζ m ν) Cw ξ k))) *
        Real.exp (-γ * (b - a)) * ‖initial‖ ^ 2 := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let δ₀ := constructedNativeSmoothingTime J R k Cw η
  let A := constructedNativeWindowPrice J R k Cw * peFactor η ^ 2
  let P := (Real.exp 1 * (2 * Real.exp 1) / (δ₀ / (J : ℝ))) ^ J
  let Z := cellFullZerothGrowth η Cw ξ k
  have hj : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hjpos : 0 < (J : ℝ) := lt_of_lt_of_le (by norm_num) hj
  have hd : 0 < δ₀ := constructedNativeSmoothingTime_pos J R k Cw η hR
    ((norm_nonneg _).trans (hk a)) hCw
  have hd1 : δ₀ ≤ 1 := by
    have he := constructedNativeSmoothingTime_orders_le_one J R k Cw η hR
      ((norm_nonneg _).trans (hk a)) hCw
    have hh : δ₀ ≤ (J : ℝ) * δ₀ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hj hd.le
    exact hh.trans he
  have hA : 0 ≤ A := mul_nonneg (constructedNativeWindowPrice_pos J R k Cw hR
    ((norm_nonneg _).trans (hk a)) hCw).le (sq_nonneg _)
  have hbudget : A * δ₀ ≤ 1 := constructedNativeSmoothingTime_budget J R k Cw η hR
    ((norm_nonneg _).trans (hk a)) hCw
  have hP : 0 ≤ P := pow_nonneg (div_nonneg (by positivity) (div_pos hd hjpos).le) _
  have hx (s : ℝ) (hs : b - s ≤ 1) :
      Real.exp (-γ * (s - a)) ≤ Real.exp γ * Real.exp (-γ * (b - a)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have he := mul_le_mul_of_nonneg_left hs hγ
    nlinarith only [he]
  by_cases hsmall : b - a ≤ δ₀
  · obtain ⟨W, hwv, hwb⟩ := interiorPulseReflectedActualWeak_native_short_propagation J hΛ hζ hν hr
      y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ k hk hκ hab U slice hU initial hi
      ((mul_le_mul_of_nonneg_left hsmall hA).trans hbudget)
    refine ⟨W, hwv, hwb.trans ?_⟩
    have he : (1 : ℝ) ≤ Real.exp γ * Real.exp (-γ * (b - a)) := by
      simpa only [sub_self, mul_zero, Real.exp_zero] using hx a (hsmall.trans hd1)
    have hp : Real.exp 1 ≤ Real.exp 1 + P * Real.exp Z :=
      le_add_of_nonneg_right (mul_nonneg hP (Real.exp_pos Z).le)
    have hm := mul_le_mul hp he (by norm_num : (0 : ℝ) ≤ 1)
      ((Real.exp_pos 1).le.trans hp)
    have hm' := mul_le_mul_of_nonneg_right hm (sq_nonneg ‖initial‖)
    convert hm' using 1 <;> ring
  · let s := b - δ₀
    have has : a ≤ s := by dsimp only [s]; linarith only [hsmall]
    have hsb : s < b := by dsimp only [s]; linarith only [hd]
    have hsub : Icc s b ⊆ Icc a b := Icc_subset_Icc has le_rfl
    have hstep : 0 < δ₀ / (J : ℝ) := div_pos hd hjpos
    have hδ : δ₀ / (J : ℝ) ≤ δ₀ := div_le_self hd.le hj
    have hfit : (J : ℝ) * (δ₀ / (J : ℝ)) ≤ b - s := by
      dsimp only [s]
      rw [mul_div_cancel₀ δ₀ hjpos.ne']
      linarith
    obtain ⟨W, hwv, hwb⟩ := interiorPulseReflectedActualWeak_native_smoothing_of_step J hΛ hζ hν hr
      y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ k hk hκ hsb (U s) U slice
      (hU.mono hsub) rfl (by dsimp only [s]; linarith only [hd1])
      (δ₀ / (J : ℝ)) hstep ((mul_le_mul_of_nonneg_left hδ hA).trans hbudget) hfit
    refine ⟨W, hwv, hwb.trans ?_⟩
    have hiNorm : ‖U a‖ ^ 2 ≤ ‖initial‖ ^ 2 := by
      rw [hi]
      exact pow_le_pow_left₀ (norm_nonneg _) (torusHigherValue_norm_le initial) 2
    have hg := hgap s ⟨has, hsb.le⟩
    have hxs := hx s (by dsimp only [s]; linarith only [hd1])
    have hupper : ‖U s‖ ^ 2 ≤
        (Real.exp γ * Real.exp (-γ * (b - a))) * ‖initial‖ ^ 2 :=
      hg.trans (mul_le_mul hxs hiNorm (sq_nonneg _)
        (mul_nonneg (Real.exp_pos γ).le (Real.exp_pos _).le))
    have hm := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hupper (Real.exp_pos Z).le) hP
    have hp : P * Real.exp Z ≤ Real.exp 1 + P * Real.exp Z :=
      le_add_of_nonneg_left (Real.exp_pos 1).le
    have hf := mul_le_mul_of_nonneg_right hp
      (mul_nonneg (mul_nonneg (Real.exp_pos γ).le
        (Real.exp_pos (-γ * (b - a))).le) (sq_nonneg ‖initial‖))
    exact hm.trans (by convert hf using 1 <;> ring)

/-! Full higher smoothing from an L2 entrance with the entire lower-order gap retained. -/

theorem interiorPulseReflectedActualWeak_native_gap_smoothing (J : ℕ)
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
    (hκ : Measurable κ) {a b : ℝ} (hab : a < b)
    (U : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (hU : CellWeakHilbertCurve a b U slice (fun t => cellDualDerivative
      ⟨fun s _ => G (-s), fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x,
        fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
      (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
        (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t (slice t) 0 0))
    (γ : ℝ) (hγ : 0 ≤ γ)
    (hgap : ∀ s ∈ Icc a b, ‖U s‖ ^ 2 ≤ Real.exp (-γ * (s - a)) * ‖U a‖ ^ 2) :
    let δ₀ := constructedNativeSmoothingTime J R k Cw (ν / ocMeanFlux α q Λ ζ m ν)
    let C := Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1)
    let P := (C / δ₀) ^ J + (C / (b - a)) ^ J
    ∃ W : TorusHk J ℂ, torusHkValueCLM W = U b ∧ ‖W‖ ^ 2 ≤
      (Real.exp γ * P * Real.exp
        (cellFullZerothGrowth (ν / ocMeanFlux α q Λ ζ m ν) Cw ξ k)) *
        Real.exp (-γ * (b - a)) * ‖U a‖ ^ 2 := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let δ₀ := constructedNativeSmoothingTime J R k Cw η
  let A := constructedNativeWindowPrice J R k Cw * peFactor η ^ 2
  let d := min δ₀ (b - a)
  let δ := d / ((J : ℝ) + 1)
  let s := b - d
  let C := Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1)
  let P := (C / δ₀) ^ J + (C / (b - a)) ^ J
  let Z := cellFullZerothGrowth η Cw ξ k
  have hk0 := (norm_nonneg (κ a)).trans (hk a)
  have hd0 : 0 < δ₀ := constructedNativeSmoothingTime_pos J R k Cw η hR hk0 hCw
  have hbudget : A * δ₀ ≤ 1 := constructedNativeSmoothingTime_budget J R k Cw η hR hk0 hCw
  have hM := constructedNativeWindowPrice_one_le J R k Cw hR hk0 hCw
  have hA1 : 1 ≤ A := by
    simpa only [one_mul] using mul_le_mul hM (one_le_peFactor_pow η 2)
      (by norm_num : (0 : ℝ) ≤ 1) ((by norm_num : (0 : ℝ) ≤ 1).trans hM)
  have hdA : δ₀ ≤ A * δ₀ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hA1 hd0.le
  have hd01 : δ₀ ≤ 1 := hdA.trans hbudget
  have hd : 0 < d := lt_min hd0 (sub_pos.mpr hab)
  have hd1 : d ≤ 1 := (min_le_left _ _).trans hd01
  have hdτ : d ≤ b - a := min_le_right _ _
  have hj : 1 ≤ (J : ℝ) + 1 := by have hh := Nat.cast_nonneg (α := ℝ) J; linarith only [hh]
  have hδ : 0 < δ := div_pos hd (lt_of_lt_of_le (by norm_num) hj)
  have hδd : δ ≤ d := div_le_self hd.le hj
  have has : a ≤ s := by dsimp only [s]; linarith only [hdτ]
  have hsb : s < b := by dsimp only [s]; linarith only [hd]
  have hsub : Icc s b ⊆ Icc a b := Icc_subset_Icc has le_rfl
  have hfit : (J : ℝ) * δ ≤ b - s := by
    have hj' : (J : ℝ) / ((J : ℝ) + 1) ≤ 1 :=
      (div_le_one₀ (lt_of_lt_of_le (by norm_num) hj)).mpr (by linarith)
    have hh := mul_le_mul_of_nonneg_left hj' hd.le
    dsimp only [δ, s]
    convert hh using 1 <;> ring
  have hshort : A * δ ≤ 1 :=
    (mul_le_mul_of_nonneg_left (hδd.trans (min_le_left _ _))
      ((by norm_num : (0 : ℝ) ≤ 1).trans hA1)).trans hbudget
  obtain ⟨W, hwv, hwb⟩ := interiorPulseReflectedActualWeak_native_smoothing_of_step J hΛ hζ hν hr
    y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ k hk hκ hsb (U s) U slice
    (hU.mono hsub) rfl (by dsimp only [s]; linarith only [hd1]) δ hδ hshort hfit
  have hprice := shortSmoothingTail_price J (Real.exp 1 * (2 * Real.exp 1)) δ₀ (b - a)
    (by positivity) hd0 (sub_pos.mpr hab)
  have hP : 0 ≤ P := by dsimp [P, C]; positivity
  have hxs : Real.exp (-γ * (s - a)) ≤ Real.exp γ * Real.exp (-γ * (b - a)) := by
    have heq : s - a = b - a - d := by dsimp only [s]; ring
    rw [heq]
    exact shortSmoothingTail_gap γ (b - a) d hγ hd1
  have hupper := (hgap s ⟨has, hsb.le⟩).trans
    (mul_le_mul_of_nonneg_right hxs (sq_nonneg ‖U a‖))
  have hm := mul_le_mul hprice (mul_le_mul_of_nonneg_left hupper (Real.exp_pos Z).le)
    (mul_nonneg (Real.exp_pos Z).le (sq_nonneg ‖U s‖)) hP
  refine ⟨W, hwv, hwb.trans ?_⟩
  convert hm using 1
  ring

end AVRegularity.CycleWords
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Uniform norm prices for actual canonical graph differences on common-drift windows. -/

theorem canonicalGraph_common_drift_window_uniform_difference_decay (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    (v w : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (hw : IsCellDrift w)
    (hmv : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hmw : ∀ t (j : Fin 2), cellMean (fun x => (w t x j : ℂ)) = 0)
    (hsv : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hsw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, w t x i ^ 2) ≤ Cw)
    (V : ℝ) (hbv : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (hbw : ∀ t x, ∑ i, w t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreWordRadius Cw)
    {a b : ℝ} (hab : a ≤ b)
    (hvw : ∀ t ∈ Icc a b, w t = v t) :
    let D := fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hsv) ξ
    let E := fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hw hsw) ξ
    ∀ t ∈ Icc a b, ‖cellRawTrace D t - cellRawTrace E t‖ ^ 2 ≤
      Real.exp (-(Real.pi ^ 2 / 2) * (t - a)) * (2 * fibreWordCorrectionBound Cw * fibreNorm ξ) ^ 2 := by
  let D := fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hsv) ξ
  let E := fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hw hsw) ξ
  have he := canonicalGraph_common_drift_window_difference_decay η Cw hη0 hη hCw G hG
    hg hgsmall v w hv hw hmv hmw hsv hsw V hbv hbw ξ hξ hab hvw
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := by
    have hr := (hξ.trans (fibreWordRadius_le_graph Cw)).trans
      (fibreEvolutionRadius_le_majorant (Cw := Cw))
    have hR := fibreCoefficientMajorantRadius_pos hCw
    linarith
  have hd := fibreCoefficientFamily_graph_class_correction_bound η Cw hη hCw G hG
    hv hsv ξ hξR a
  have hd' := fibreCoefficientFamily_graph_class_correction_bound η Cw hη hCw G hG
    hw hsw ξ hξR a
  have hn : ‖cellRawTrace D a - cellRawTrace E a‖ ≤
      2 * fibreWordCorrectionBound Cw * fibreNorm ξ := by
    have hh := (norm_sub_le (cellRawTrace D a) (cellRawTrace E a)).trans (add_le_add hd hd')
    change ‖cellRawTrace D a - cellRawTrace E a‖ ≤ _ at hh
    unfold fibreWordCorrectionBound
    convert hh using 1
    ring
  have hn2 : ‖cellRawTrace D a - cellRawTrace E a‖ ^ 2 ≤
      (2 * fibreWordCorrectionBound Cw * fibreNorm ξ) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hn 2
  dsimp only
  intro t ht
  exact (he t ht).trans (mul_le_mul_of_nonneg_left hn2 (Real.exp_pos _).le)

theorem canonicalGraph_common_drift_window_norm_difference_decay (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    (v w : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (hw : IsCellDrift w)
    (hmv : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hmw : ∀ t (j : Fin 2), cellMean (fun x => (w t x j : ℂ)) = 0)
    (hsv : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hsw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, w t x i ^ 2) ≤ Cw)
    (V : ℝ) (hbv : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (hbw : ∀ t x, ∑ i, w t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreWordRadius Cw)
    {a b : ℝ} (hab : a ≤ b)
    (hvw : ∀ t ∈ Icc a b, w t = v t) :
    let D := fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hsv) ξ
    let E := fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hw hsw) ξ
    ∀ t ∈ Icc a b, ‖cellRawTrace D t - cellRawTrace E t‖ ≤
      Real.exp (-(Real.pi ^ 2 / 4) * (t - a)) * (2 * fibreWordCorrectionBound Cw * fibreNorm ξ) := by
  have he := canonicalGraph_common_drift_window_uniform_difference_decay η Cw hη0 hη hCw
    G hG hg hgsmall v w hv hw hmv hmw hsv hsw V hbv hbw ξ hξ hab hvw
  dsimp only
  intro t ht
  have hB : 0 ≤ 2 * fibreWordCorrectionBound Cw * fibreNorm ξ :=
    mul_nonneg (mul_nonneg (by norm_num) (fibreWordBounds_nonneg hCw).2) (fibreNorm_nonneg ξ)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le hB)).mp
  have hx : Real.exp (-(Real.pi ^ 2 / 4) * (t - a)) ^ 2 =
      Real.exp (-(Real.pi ^ 2 / 2) * (t - a)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [mul_pow, hx]
  exact he t ht

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Exact normalized pairing and real phase ratios survive smooth coefficient selection. -/

variable (η Cw : ℝ) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
  (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
  {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
  (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
  (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ)
  (her : ∀ p t a, r p t a =ᵐ[volume.restrict AVenhance.unitCube]
    fibreCoefficientFamily η Cw hη G hG hv hw p t a)

include her in
omit hCw in
theorem constructedScalarGraph_normalized_norm_eq (ξ : Fin 2 → ℂ) (t : ℝ) :
    cellL2Norm (fun x => 1 + cellValue (fibreSeriesJet r ξ) t x) =
      cellL2Norm (fun x => 1 + cellValue
        (fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hw) ξ) t x) := by
  apply eLpNorm_congr_ae
  filter_upwards [fibreSeriesJet_congr_ae_sections r _ her ξ t (valueIndex2 1)] with x hx
  change cellValue (fibreSeriesJet r ξ) t x =
    cellValue (fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hw) ξ) t x at hx
  rw [hx]

include hCw her in
theorem constructedScalarGraphRow_normalization
    (ell : ℕ × ℕ → ℝ → Vec 2 → ℂ)
    (heell : ∀ p t, ell p t =ᵐ[volume.restrict AVenhance.unitCube]
      fibreAdjointRowCoefficients η Cw hη G hG hv hw p t)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16) (t : ℝ) :
    Integrable (fun x => fibreSeriesFun ell ξ t x *
      (1 + cellValue (fibreSeriesJet r ξ) t x)) (volume.restrict AVenhance.unitCube) ∧
    (∫ x in AVenhance.unitCube, fibreSeriesFun ell ξ t x *
      (1 + cellValue (fibreSeriesJet r ξ) t x)) = 1 := by
  have hn := fibreAdjointRowCoefficients_normalization η Cw hη hCw G hG hv hw ξ hξ t
  have he : (fun x => fibreSeriesFun ell ξ t x *
      (1 + cellValue (fibreSeriesJet r ξ) t x)) =ᵐ[volume.restrict AVenhance.unitCube]
      (fun x => fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ t x *
        (1 + cellValue (fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hw) ξ) t x)) := by
    filter_upwards [fibreSeriesFun_congr_ae ell _ heell ξ t,
      fibreSeriesJet_congr_ae_sections r _ her ξ t (valueIndex2 1)] with x hx hy
    change cellValue (fibreSeriesJet r ξ) t x =
      cellValue (fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hw) ξ) t x at hy
    rw [hx, hy]
  exact ⟨hn.1.congr he.symm, (integral_congr_ae he).trans hn.2⟩

include hCw her in
theorem constructedScalarGraph_real_ratio (hη0 : 0 ≤ η)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hreal : ∀ j, (ξ j).im = 0)
    (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw)
    {s t : ℝ} (hst : s ≤ t) :
    ENNReal.ofReal ‖Complex.exp (∫ τ in s..t,
      fibreSeriesC (fibreCoefficientSymbol η G v
        (fibreCoefficientFamily η Cw hη G hG hv hw)) ξ τ)‖ *
      cellL2Norm (fun x => 1 + cellValue (fibreSeriesJet r ξ) t x) ≤
        cellL2Norm (fun x => 1 + cellValue (fibreSeriesJet r ξ) s x) ∧
    cellL2Norm (fun x => 1 + cellValue (fibreSeriesJet r ξ) s x) ≤
      ENNReal.ofReal (constructedScalarGraphPrice Cw) *
        cellL2Norm (fun x => 1 + cellValue (fibreSeriesJet r ξ) t x) := by
  rw [constructedScalarGraph_normalized_norm_eq η Cw hη G hG hv hw r her ξ t,
    constructedScalarGraph_normalized_norm_eq η Cw hη G hG hv hw r her ξ s]
  refine ⟨fibreCoefficientFamily_graph_real_ratio η Cw hη0 hη hCw G hG hv hm hw V hb
    ξ hreal hξ hst, ?_⟩
  apply (fibreCoefficientFamily_graph_mode_ratio η Cw hη hCw G hG hv hw ξ hξ s t).trans
  apply mul_le_mul' _ le_rfl
  exact ENNReal.ofReal_le_ofReal
    ((by norm_num : (3 : ℝ) ≤ 4).trans (constructedScalarGraphPrice_four Cw))

end AVRegularity.CycleWords
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Buffered zero-order graph and quadratic symbol replacement from actual common-drift evolution. -/

theorem canonicalGraph_buffered_norm_difference_bound (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    (v w : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (hw : IsCellDrift w)
    (hmv : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hmw : ∀ t (j : Fin 2), cellMean (fun x => (w t x j : ℂ)) = 0)
    (hsv : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hsw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, w t x i ^ 2) ≤ Cw)
    (V : ℝ) (hbv : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (hbw : ∀ t x, ∑ i, w t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreWordRadius Cw)
    (lo hi buffer : ℝ) (hlohi : lo ≤ hi) (hbuffer : 0 ≤ buffer)
    (hvw : ∀ t ∈ Icc (lo - buffer) (hi + buffer), w t = v t) :
    let D := fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hsv) ξ
    let E := fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hw hsw) ξ
    ∀ t ∈ Icc lo (hi + buffer), ‖cellRawTrace D t - cellRawTrace E t‖ ≤
      Real.exp (-(Real.pi ^ 2 / 4) * buffer) * (2 * fibreWordCorrectionBound Cw * fibreNorm ξ) := by
  have hab : lo - buffer ≤ hi + buffer := by linarith
  have he := canonicalGraph_common_drift_window_norm_difference_decay η Cw hη0 hη hCw
    G hG hg hgsmall v w hv hw hmv hmw hsv hsw V hbv hbw ξ hξ hab hvw
  dsimp only
  intro t ht
  have hti : t ∈ Icc (lo - buffer) (hi + buffer) := ⟨by linarith [ht.1], ht.2⟩
  have hd : buffer ≤ t - (lo - buffer) := by linarith [ht.1]
  have hexp : Real.exp (-(Real.pi ^ 2 / 4) * (t - (lo - buffer))) ≤
      Real.exp (-(Real.pi ^ 2 / 4) * buffer) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left hd (neg_nonpos.mpr (by positivity))
  exact (he t hti).trans (mul_le_mul_of_nonneg_right hexp
    (mul_nonneg (mul_nonneg (by norm_num) (fibreWordBounds_nonneg hCw).2) (fibreNorm_nonneg ξ)))

theorem canonicalGraph_buffered_symbol_difference_bound (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    (v w : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (hw : IsCellDrift w)
    (hmv : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hmw : ∀ t (j : Fin 2), cellMean (fun x => (w t x j : ℂ)) = 0)
    (hsv : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hsw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, w t x i ^ 2) ≤ Cw)
    (V : ℝ) (hbv : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (hbw : ∀ t x, ∑ i, w t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreWordRadius Cw)
    (lo hi buffer : ℝ) (hlohi : lo ≤ hi) (hbuffer : 0 ≤ buffer)
    (hvw : ∀ t ∈ Icc (lo - buffer) (hi + buffer), w t = v t) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hsv
    let s := fibreCoefficientFamily η Cw hη G hG hw hsw
    ∀ t ∈ Icc lo (hi + buffer),
      ‖fibreSeriesC (fibreCoefficientSymbol η G v r) ξ t -
        fibreSeriesC (fibreCoefficientSymbol η G w s) ξ t‖ ≤
      (2 * Cw * fibreWordCorrectionBound Cw) * fibreNorm ξ ^ 2 *
        Real.exp (-(Real.pi ^ 2 / 4) * buffer) := by
  have he := canonicalGraph_buffered_norm_difference_bound η Cw hη0 hη hCw G hG
    hg hgsmall v w hv hw hmv hmw hsv hsw V hbv hbw ξ hξ lo hi buffer hlohi hbuffer hvw
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := by
    have hr := (hξ.trans (fibreWordRadius_le_graph Cw)).trans
      (fibreEvolutionRadius_le_majorant (Cw := Cw))
    have hR := fibreCoefficientMajorantRadius_pos hCw
    linarith
  dsimp only
  intro t ht
  have hti : t ∈ Icc (lo - buffer) (hi + buffer) := ⟨by linarith [ht.1], ht.2⟩
  have hs := canonicalGraph_symbol_difference_norm_at_common_drift η Cw hη hCw G hG
    v w hv hw hsv hsw ξ hξR t (hvw t hti).symm
  have hm := mul_le_mul_of_nonneg_left (he t ht) (mul_nonneg hCw (fibreNorm_nonneg ξ))
  apply hs.trans
  convert hm using 1
  ring

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.CycleWords

/-! Polynomial native smoothing for the actual full finite equation, with its zeroth bound discharged. -/

theorem interiorPulseActualWeak_native_polynomial_smoothing_aePotential (J : ℕ)
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
    {a b : ℝ} (hab : a < b)
    (hκ : AEStronglyMeasurable κ (volume.restrict (Icc a b)))
    (initial : ComplexCellL2)
    (U : ℝ → ComplexCellL2)
    (slice : ℝ → TorusHk 1 ℂ)
    (hU : CellWeakHilbertCurve a b U slice
      (fun t => cellDualDerivative
        ⟨fun t _ => G t, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot,
          fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
        hG V hv.1 hb t (slice t) 0 0))
    (hinitial : U a = initial) (hwindow : b - a ≤ 1) (t : ℝ) (htI : t ∈ Icc a b)
    (ht : a + J * constructedNativeSmoothingTime J R k Cw (ν / ocMeanFlux α q Λ ζ m ν) ≤ t) :
    ∃ W : TorusHk J ℂ, torusHkValueCLM W = U t ∧ ‖W‖ ^ 2 ≤
      (Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1) * constructedNativeWindowPrice J R k Cw) ^ J *
        peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ (2 * J) *
        (Real.exp (cellFullZerothGrowth (ν / ocMeanFlux α q Λ ζ m ν) Cw ξ k) * ‖initial‖ ^ 2) := by
  obtain ⟨κ', hm, he, hb'⟩ := complexBounded_measurable_representative κ hκ k
    ((norm_nonneg _).trans (hk a)) (Filter.Eventually.of_forall hk)
  have hu' : CellWeakHilbertCurve a b U slice
      (fun t => cellDualDerivative
        ⟨fun t _ => G t, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot,
          fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ'⟩
        hG V hv.1 hb t (slice t) 0 0) := by
    apply hU.dual_congr
    filter_upwards [he] with t het
    exact cellDualDerivative_potential_congr
      ⟨fun t _ => G t, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot,
        fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
      hG V hv.1 hb κ κ' t het (slice t) 0 0
  exact interiorPulseActualWeak_native_polynomial_smoothing J hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ' k hb' hm hab initial U slice hu' hinitial hwindow t htI ht

end AVRegularity.CycleWords
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Buffered zero-order graph and quadratic symbol replacement from actual common-drift evolution. -/

theorem canonicalGraph_buffered_literal_L2_difference_bound (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    (v w : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (hw : IsCellDrift w)
    (hmv : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hmw : ∀ t (j : Fin 2), cellMean (fun x => (w t x j : ℂ)) = 0)
    (hsv : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hsw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, w t x i ^ 2) ≤ Cw)
    (V : ℝ) (hbv : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (hbw : ∀ t x, ∑ i, w t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreWordRadius Cw)
    (lo hi buffer : ℝ) (hlohi : lo ≤ hi) (hbuffer : 0 ≤ buffer)
    (hvw : ∀ t ∈ Icc (lo - buffer) (hi + buffer), w t = v t) :
    let D := fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hsv) ξ
    let E := fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hw hsw) ξ
    ∀ t ∈ Icc lo (hi + buffer), cellL2Norm (fun x => cellValue D t x - cellValue E t x) ≤
      ENNReal.ofReal (Real.exp (-(Real.pi ^ 2 / 4) * buffer) *
        (2 * fibreWordCorrectionBound Cw * fibreNorm ξ)) := by
  have he := canonicalGraph_buffered_norm_difference_bound η Cw hη0 hη hCw G hG
    hg hgsmall v w hv hw hmv hmw hsv hsw V hbv hbw ξ hξ lo hi buffer hlohi hbuffer hvw
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := by
    have hr := (hξ.trans (fibreWordRadius_le_graph Cw)).trans
      (fibreEvolutionRadius_le_majorant (Cw := Cw))
    have hR := fibreCoefficientMajorantRadius_pos hCw
    linarith
  have hD := fibreCoefficientFamily_graph_isInverse η Cw hη hCw G hG hv hsv ξ hξR
  have hE := fibreCoefficientFamily_graph_isInverse η Cw hη hCw G hG hw hsw ξ hξR
  dsimp only
  intro t ht
  rw [cellL2Norm_difference_of_raw_traces _ _ t
    (hD.1.2.2.1 t (Set.mem_univ t)).1 (hE.1.2.2.1 t (Set.mem_univ t)).1]
  exact ENNReal.ofReal_le_ofReal (he t ht)

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.CycleWords

/-! Polynomial native smoothing for the actual full finite equation, with its zeroth bound discharged. -/

theorem interiorPulseActualWeak_unit_window_all_native_orders
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
    {a b : ℝ} (hab : a < b)
    (hκ : AEStronglyMeasurable κ (volume.restrict (Icc a b)))
    (initial : ComplexCellL2)
    (U : ℝ → ComplexCellL2)
    (slice : ℝ → TorusHk 1 ℂ)
    (hU : CellWeakHilbertCurve a b U slice
      (fun t => cellDualDerivative
        ⟨fun t _ => G t, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot,
          fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
        hG V hv.1 hb t (slice t) 0 0))
    (hinitial : U a = initial) (hwindow : b - a = 1) :
    ∀ J : ℕ,
    ∃ W : TorusHk J ℂ, torusHkValueCLM W = U b ∧ ‖W‖ ^ 2 ≤
      (Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1) * constructedNativeWindowPrice J R k Cw) ^ J *
        peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ (2 * J) *
        (Real.exp (cellFullZerothGrowth (ν / ocMeanFlux α q Λ ζ m ν) Cw ξ k) * ‖initial‖ ^ 2) := by
  intro J
  have hd := constructedNativeSmoothingTime_orders_le_one J R k Cw
    (ν / ocMeanFlux α q Λ ζ m ν) hR ((norm_nonneg _).trans (hk a)) hCw
  have ht : a + J * constructedNativeSmoothingTime J R k Cw
      (ν / ocMeanFlux α q Λ ζ m ν) ≤ b := by linarith only [hd, hwindow]
  exact interiorPulseActualWeak_native_polynomial_smoothing_aePotential J hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ k hk hab hκ initial U slice hU hinitial hwindow.le b ⟨hab.le, le_rfl⟩ ht

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Full native gap smoothing with explicit polynomial contrast and classical time prices. -/

theorem interiorPulseReflectedActualWeak_native_gap_polynomial_smoothing (J : ℕ)
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
    (hκ : Measurable κ) {a b : ℝ} (hab : a < b)
    (U : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (hU : CellWeakHilbertCurve a b U slice (fun t => cellDualDerivative
      ⟨fun s _ => G (-s), fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x,
        fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
      (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
        (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t (slice t) 0 0))
    (γ : ℝ) (hγ : 0 ≤ γ)
    (hgap : ∀ s ∈ Icc a b, ‖U s‖ ^ 2 ≤ Real.exp (-γ * (s - a)) * ‖U a‖ ^ 2) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let B := Real.exp γ * constructedGapSmoothingBasePrice J R k Cw *
      Real.exp (constructedAllOrderPrice 0 R k Cw)
    let C := (Real.sqrt B * peFactor η ^ J * Real.exp (-γ * (b - a) / 2)) *
      (1 + (b - a) ^ (-(J : ℝ) / 2))
    ∃ W : TorusHk J ℂ, torusHkValueCLM W = U b ∧ ‖W‖ ^ 2 ≤ C ^ 2 * ‖U a‖ ^ 2 := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let τ := b - a
  let Base := constructedGapSmoothingBasePrice J R k Cw
  let Z := constructedAllOrderPrice 0 R k Cw
  let B := Real.exp γ * Base * Real.exp Z
  let T := 1 + τ ^ (-(J : ℝ) / 2)
  have hk0 := (norm_nonneg (κ a)).trans (hk a)
  have hM := constructedNativeWindowPrice_pos J R k Cw hR hk0 hCw
  have hBase : 0 ≤ Base := by dsimp [Base, constructedGapSmoothingBasePrice]; positivity
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (Real.exp_pos γ).le hBase) (Real.exp_pos Z).le
  have ht : (∑ i : Fin 2, ‖(Real.sqrt η : ℂ) * ξ i‖ ^ 2) ≤ 2 * R ^ 2 := by
    simp only [Fin.sum_univ_two]
    exact (add_le_add (pow_le_pow_left₀ (norm_nonneg _) (hθ 0) 2)
      (pow_le_pow_left₀ (norm_nonneg _) (hθ 1) 2)).trans_eq (by ring)
  have hz : cellFullZerothGrowth η Cw ξ k ≤ Z := by
    have hf := mul_le_mul_of_nonneg_left hξ hCw
    unfold cellFullZerothGrowth
    dsimp only [Z, constructedAllOrderPrice]
    linarith only [ht, hf]
  obtain ⟨W, hwv, hwb⟩ := interiorPulseReflectedActualWeak_native_gap_smoothing J hΛ hζ hν hr
    y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ k hk hκ hab U slice hU γ hγ hgap
  have hP := constructedGapSmoothing_polynomial_square_price J R k Cw η τ
    hR hk0 hCw (sub_pos.mpr hab)
  have hconst := mul_le_mul_of_nonneg_left
    (mul_le_mul hP (Real.exp_le_exp.mpr hz) (Real.exp_pos _).le (sq_nonneg _))
    (Real.exp_pos γ).le
  rw [← mul_assoc] at hconst
  have hh := hwb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hconst (Real.exp_pos _).le) (sq_nonneg ‖U a‖))
  refine ⟨W, hwv, hh.trans_eq ?_⟩
  change Real.exp γ * ((Real.sqrt Base * peFactor η ^ J * T) ^ 2 * Real.exp Z) *
    Real.exp (-γ * τ) * ‖U a‖ ^ 2 =
      ((Real.sqrt B * peFactor η ^ J * Real.exp (-γ * τ / 2)) * T) ^ 2 * ‖U a‖ ^ 2
  conv_rhs => rw [mul_pow, polynomial_decay_square_price B (peFactor η) γ τ J hB]
  dsimp only [B]
  simp only [mul_pow, Real.sq_sqrt hBase]
  rw [show 2 * J = J * 2 by omega, pow_mul]
  ring

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The actual normalized adjoint projection lies in the forward graph annihilator. -/

theorem canonicalAdjoint_initial_kernel (η Cw : ℝ) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16)
    (u : ComplexCellL2) (t : ℝ) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let R := cellRawTrace (fibreSeriesJet r ξ) t + cellConstantCLM 1
    let A := cellRawTrace (fibreAdjointGraphRaw η Cw hη G hG hv hw ξ) (-t) + cellConstantCLM 1
    let k := fibreSeriesC (fibreAdjointNormalizationCoefficients η Cw hη G hG hv hw) ξ t
    let c := k * cellComplexPair u (cellFiberCLM Complex.conjCLE.toContinuousLinearMap R)
    cellComplexPair (u - cellScalarCLM c A)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap R) = 0 := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let R := cellRawTrace (fibreSeriesJet r ξ) t + cellConstantCLM 1
  let A := cellRawTrace (fibreAdjointGraphRaw η Cw hη G hG hv hw ξ) (-t) + cellConstantCLM 1
  let k := fibreSeriesC (fibreAdjointNormalizationCoefficients η Cw hη G hG hv hw) ξ t
  let m := cellComplexPair u (cellFiberCLM Complex.conjCLE.toContinuousLinearMap R)
  let d := cellComplexPair R (cellFiberCLM Complex.conjCLE.toContinuousLinearMap A)
  have hn : k * d = 1 := by
    have hh := fibreAdjointRow_pairing_normalization η Cw hη hCw G hG hv hw ξ hξ t
    dsimp only at hh
    rw [fibreAdjointRow_source_slice η Cw hη hCw G hG hv hw ξ hξ t] at hh
    simpa only [cellFiberConj_scalar, cellComplexPair_scalar_right, star_star] using hh
  dsimp only
  rw [cellComplexPair_eq_inner, inner_sub_right, ← cellComplexPair_eq_inner,
    ← cellComplexPair_eq_inner, cellComplexPair_scalar_left, cellComplexPair_bilinear_symm A R]
  change m - (k * m) * d = 0
  calc
    _ = m - m * (k * d) := by ring
    _ = 0 := by rw [hn, mul_one, sub_self]

end AVRegularity.CycleWords
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! The actual canonical normalization satisfies the cell overlap reciprocal equation. -/

theorem canonicalRow_overlap_normalization (η Cw : ℝ) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16) (t : ℝ) :
    (1 + cellComplexPair
      (cellRawTrace (fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hw) ξ) t)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap
        (cellRawTrace (fibreAdjointGraphRaw η Cw hη G hG hv hw ξ) (-t)))) *
      fibreSeriesC (fibreAdjointNormalizationCoefficients η Cw hη G hG hv hw) ξ t = 1 := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let D := fibreSeriesJet r ξ
  let A := cellRawTrace (fibreAdjointGraphRaw η Cw hη G hG hv hw ξ) (-t)
  let a := fibreSeriesFun (fibreAdjointCorrectionCoefficients η Cw hη G hG hv hw) ξ
  let k := fibreSeriesC (fibreAdjointNormalizationCoefficients η Cw hη G hG hv hw) ξ t
  have hR := fibreCoefficientMajorantRadius_pos hCw
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := hξ.trans (by linarith)
  have hi := fibreCoefficientFamily_graph_isInverse η Cw hη hCw G hG hv hw ξ hξR
  have hraw := cellRawTrace_ae D t (hi.1.2.2.1 t (mem_univ t)).1
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
  rw [hp]
  exact fibreAdjointNormalizationCoefficients_series_mul η Cw hη hCw G hG hv hw ξ hξ t

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Any positive short full-equation window produces one smooth periodic endpoint representative. -/

theorem interiorPulseActualWeak_positive_short_window_smooth
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
    (hκ : Measurable κ) {a b : ℝ} (hab : a < b)
    (initial : ComplexCellL2)
    (U : ℝ → ComplexCellL2)
    (slice : ℝ → TorusHk 1 ℂ)
    (hU : CellWeakHilbertCurve a b U slice
      (fun t => cellDualDerivative
        ⟨fun t _ => G t, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot,
          fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
        hG V hv.1 hb t (slice t) 0 0))
    (hinitial : U a = initial) (hwindow : b - a ≤ 1)
    : ∃ f : Vec 2 → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧ AVenhance.IsZ2Periodic f ∧
      f =ᵐ[volume.restrict AVenhance.unitCube] (U b : Vec 2 → ℂ) := by
  apply torusHigher_all_order_smooth_representative (U b)
  intro J
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let δ₀ := constructedNativeSmoothingTime J R k Cw η
  have hδ₀ := constructedNativeSmoothingTime_pos J R k Cw η hR ((norm_nonneg _).trans (hk a)) hCw
  have hA : 0 ≤ constructedNativeWindowPrice J R k Cw * peFactor η ^ 2 :=
    mul_nonneg (constructedNativeWindowPrice_pos J R k Cw hR
      ((norm_nonneg _).trans (hk a)) hCw).le (sq_nonneg _)
  obtain ⟨hδ, hbudget, hfit⟩ := shortSmoothingStep_budget J δ₀ (b - a)
    (constructedNativeWindowPrice J R k Cw * peFactor η ^ 2) hδ₀ (sub_pos.mpr hab) hA
    (constructedNativeSmoothingTime_budget J R k Cw η hR ((norm_nonneg _).trans (hk a)) hCw)
  obtain ⟨W, hw, _⟩ := interiorPulseActualWeak_native_smoothing_of_step J hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ k hk hκ hab initial U slice hU
    hinitial hwindow (min δ₀ ((b - a) / ((J : ℝ) + 1))) hδ hbudget hfit
  exact ⟨W, hw⟩

/-! Every positive full-equation interval has a smooth periodic endpoint representative. -/

theorem interiorPulseActualWeak_positive_window_smooth
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
    (hκ : Measurable κ) {a b : ℝ} (hab : a < b)
    (initial : ComplexCellL2)
    (U : ℝ → ComplexCellL2)
    (slice : ℝ → TorusHk 1 ℂ)
    (hU : CellWeakHilbertCurve a b U slice
      (fun t => cellDualDerivative
        ⟨fun t _ => G t, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot,
          fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
        hG V hv.1 hb t (slice t) 0 0))
    (hinitial : U a = initial) :
    ∃ f : Vec 2 → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧ AVenhance.IsZ2Periodic f ∧
      f =ᵐ[volume.restrict AVenhance.unitCube] (U b : Vec 2 → ℂ) := by
  by_cases hshort : b - a ≤ 1
  · exact interiorPulseActualWeak_positive_short_window_smooth hΛ hζ hν hr y₀ hslot hv V hb
      G hG Cw hCw hw ξ R hR hξ hθ κ k hk hκ hab initial U slice hU hinitial hshort
  · have ha : a ≤ b - 1 := by linarith only [hshort]
    have hsub : Icc (b - 1) b ⊆ Icc a b := Icc_subset_Icc ha le_rfl
    exact interiorPulseActualWeak_positive_short_window_smooth hΛ hζ hν hr y₀ hslot hv V hb
      G hG Cw hCw hw ξ R hR hξ hθ κ k hk hκ (by linarith : b - 1 < b)
      (U (b - 1)) U slice (hU.mono hsub) rfl (by ring_nf; exact le_rfl)

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.CycleWords

/-! Polynomial native smoothing for the actual full finite equation, with its zeroth bound discharged. -/

theorem interiorPulseReflectedActualWeak_native_polynomial_smoothing_aePotential (J : ℕ)
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
    {a b : ℝ} (hab : a < b)
    (hκ : AEStronglyMeasurable κ (volume.restrict (Icc a b)))
    (initial : ComplexCellL2)
    (U : ℝ → ComplexCellL2)
    (slice : ℝ → TorusHk 1 ℂ)
    (hU : CellWeakHilbertCurve a b U slice
      (fun t => cellDualDerivative
        ⟨fun s _ => G (-s), fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x,
          fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
        (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
        (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t (slice t) 0 0))
    (hinitial : U a = initial) (hwindow : b - a ≤ 1) (t : ℝ) (htI : t ∈ Icc a b)
    (ht : a + J * constructedNativeSmoothingTime J R k Cw (ν / ocMeanFlux α q Λ ζ m ν) ≤ t) :
    ∃ W : TorusHk J ℂ, torusHkValueCLM W = U t ∧ ‖W‖ ^ 2 ≤
      (Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1) * constructedNativeWindowPrice J R k Cw) ^ J *
        peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ (2 * J) *
        (Real.exp (cellFullZerothGrowth (ν / ocMeanFlux α q Λ ζ m ν) Cw ξ k) * ‖initial‖ ^ 2) := by
  obtain ⟨κ', hm, he, hb'⟩ := complexBounded_measurable_representative κ hκ k
    ((norm_nonneg _).trans (hk a)) (Filter.Eventually.of_forall hk)
  have hu' : CellWeakHilbertCurve a b U slice
      (fun t => cellDualDerivative
        ⟨fun s _ => G (-s), fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x,
          fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ'⟩
        (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
        (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t (slice t) 0 0) := by
    apply hU.dual_congr
    filter_upwards [he] with t het
    exact cellDualDerivative_potential_congr
      ⟨fun s _ => G (-s), fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x,
        fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
      (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
        (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) κ κ' t het (slice t) 0 0
  exact interiorPulseReflectedActualWeak_native_polynomial_smoothing J hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ' k hb' hm hab initial U slice hu' hinitial hwindow t htI ht

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! Every actual Hilbert-valued scalar forced chain obeys the backward Bloch source formula in each fiber coordinate. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeScalarCoordinateForced_duhamel
    (a b : ℝ) (hab : a ≤ b) (κ : Fin 1 → ι → ℕ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (C : ℝ) (hCpos : 0 < C) (hC : ∀ t i z, ‖cellDriftTorusSymbol v t i z‖ ≤ C)
    (C' : ℝ) (hC'pos : 0 < C')
    (hC' : ∀ t i z, ‖cellDriftTorusSymbol (fun t x => -v t x) t i z‖ ≤ C')
    (Cr : ℝ) (hCrpos : 0 < Cr)
    (hCr : ∀ t i z, ‖cellDriftTorusSymbol (fun r x => -v (-r) x) t i z‖ ≤ Cr)
    (f : ∀ p : Fin 1 × ι, PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (F : ∀ p : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (PiLp 2 (fun _ : Fin 2 => h p.2)))
    (hF : ∀ p, MemLp (F p) 2 (volume.restrict (Icc a b)))
    (u : ∀ p : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (w : ∀ p : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hsln : IsCoupledWeakSolutionPlane (h := fun p : Fin 1 × ι => h p.2) 1 a b v 2
      (fun p => κ p.1 p.2)
      (planeChainCoefficient (geometryScalarData (h := h) 2 (fun t _ => G t)) κ)
      f F (fun _ _ => 0) u w)
    (p : Fin 1 × ι) (e : h p.2) (g : Lp ℝ 2 (volume : Measure (Vec 2))) :
    let B := planeBlochBackwardRealField hab G hG v hv V hb g
    inner ℝ (planeFiberCoordinateCLM e (coupledPlaneL2Trace u p b)) g =
      inner ℝ (planeFiberCoordinateCLM e (planeHkValueOperator (κ p.1 p.2) (f p)))
        (planeHkValueOperator 0 (cellEnergyPlaneRealTrace (neg_le_neg hab) B (-a))) -
      ∫ r in a..b, inner ℝ (planeFluxValueOperator (κ p.1 p.2) (mapPlaneHk (planeFiberFluxCoordinate e) (F p r)))
        (planeH1GradientOperator (cellEnergyPlaneRealH1State (neg_le_neg hab) B (-r))) := by
  have hc := planeScalarCoordinateForced_weakCurve a b hab κ G hG v hv C hCpos hC f F hF u w hsln p e
  have he := planeBlochDuhamel_pair hab G hG v hv V hb C hCpos hC C' hC'pos hC'
    Cr hCrpos hCr (fun r => planeFiberCoordinateCLM e (coupledPlaneL2Trace u p r))
    (fun r => mapPlaneHk (InnerProductSpace.toDual ℝ (h p.2) e) (coupledPlaneH1Slice w p r))
    (fun r => planeSourceDual 0 (planeFluxValueOperator (κ p.1 p.2) (mapPlaneHk (planeFiberFluxCoordinate e) (F p r)))) hc g
  have hi : planeFiberCoordinateCLM e (coupledPlaneL2Trace u p a) =
      planeFiberCoordinateCLM e (planeHkValueOperator (κ p.1 p.2) (f p)) := by
    change planeFiberCoordinateCLM e (planeHkValueOperator (κ p.1 p.2) (u p a)) = _
    rw [hsln.2.2.2.1 p]
  simp only [hi, planeSourceDual_pair, inner_zero_left, zero_sub,
    intervalIntegral.integral_neg] at he
  linarith only [he]

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.CycleWords

/-! Polynomial native smoothing for the actual full finite equation, with its zeroth bound discharged. -/

theorem interiorPulseReflectedActualWeak_unit_window_all_native_orders
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
    {a b : ℝ} (hab : a < b)
    (hκ : AEStronglyMeasurable κ (volume.restrict (Icc a b)))
    (initial : ComplexCellL2)
    (U : ℝ → ComplexCellL2)
    (slice : ℝ → TorusHk 1 ℂ)
    (hU : CellWeakHilbertCurve a b U slice
      (fun t => cellDualDerivative
        ⟨fun s _ => G (-s), fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x,
          fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
        (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
        (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t (slice t) 0 0))
    (hinitial : U a = initial) (hwindow : b - a = 1) :
    ∀ J : ℕ,
    ∃ W : TorusHk J ℂ, torusHkValueCLM W = U b ∧ ‖W‖ ^ 2 ≤
      (Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1) * constructedNativeWindowPrice J R k Cw) ^ J *
        peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ (2 * J) *
        (Real.exp (cellFullZerothGrowth (ν / ocMeanFlux α q Λ ζ m ν) Cw ξ k) * ‖initial‖ ^ 2) := by
  intro J
  have hd := constructedNativeSmoothingTime_orders_le_one J R k Cw
    (ν / ocMeanFlux α q Λ ζ m ν) hR ((norm_nonneg _).trans (hk a)) hCw
  have ht : a + J * constructedNativeSmoothingTime J R k Cw
      (ν / ocMeanFlux α q Λ ζ m ν) ≤ b := by linarith only [hd, hwindow]
  exact interiorPulseReflectedActualWeak_native_polynomial_smoothing_aePotential J hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ k hk hab hκ initial U slice hU hinitial hwindow.le b ⟨hab.le, le_rfl⟩ ht

end AVRegularity.CycleWords
end
