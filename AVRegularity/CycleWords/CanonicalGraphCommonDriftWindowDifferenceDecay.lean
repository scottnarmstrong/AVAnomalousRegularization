-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.PlaneBlochEnergyRealStateIncrement
public import AVRegularity.CycleWords.ConstructedScalarRowBounds
import AVRegularity.CycleEvolution.CellEnergySpaceRawDirectionalLimit
import AVRegularity.CycleWords.InteriorPulseActualWeakNativeShortPropagation
import AVRegularity.CycleWords.InteriorPulseReflectedTracePolynomialSmoothing
public import AVRegularity.CycleEvolution.FibreAdjointRowPairingNormalization
import AVRegularity.CycleEvolution.CellEnergySpaceRawJetCauchyBound
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.CycleWords

/-! Polynomial native smoothing for the actual full finite equation, with its zeroth bound discharged. -/

theorem interiorPulseActualWeak_native_polynomial_smoothing (J : ℕ)
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
    (hinitial : U a = initial) (hwindow : b - a ≤ 1) (t : ℝ) (htI : t ∈ Icc a b)
    (ht : a + J * constructedNativeSmoothingTime J R k Cw (ν / ocMeanFlux α q Λ ζ m ν) ≤ t) :
    ∃ W : TorusHk J ℂ, torusHkValueCLM W = U t ∧ ‖W‖ ^ 2 ≤
      (Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1) * constructedNativeWindowPrice J R k Cw) ^ J *
        peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ (2 * J) *
        (Real.exp (cellFullZerothGrowth (ν / ocMeanFlux α q Λ ζ m ν) Cw ξ k) * ‖initial‖ ^ 2) := by
  let C : CellCoefficients :=
    ⟨fun t _ => G t, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot,
      fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
  obtain ⟨D⟩ := cellGalerkin_actual_limit_data hab.le C hG V k hv.1 hb hκ hk
    0 0 measurable_zero measurable_zero (by simp [cellL2Norm]) (by simp [cellL2Norm]) initial
  obtain ⟨Z, hZ, hi⟩ := D.exists_continuous_trace hab k hκ hk (by apply MemLp.zero) (by apply MemLp.zero)
  have hz : CellWeakHilbertCurve a b (extendCurve hab.le Z) D.limit
      (fun t => cellDualDerivative C hG V hv.1 hb t (D.limit t) 0 0) := by
    change CellWeakHilbertCurve a b (extendCurve hab.le Z) D.limit
      (fun t => cellDualDerivative C hG V hv.1 hb t (D.limit t)
        (cellSourceSlice 0 t) (fun j => cellSourceSlice (fun r x => (0 : PiLp 2 (fun _ : Fin 2 => ℂ)) j) t)) at hZ
    simpa only [PiLp.zero_apply, Pi.zero_def, cellSourceSlice_zero] using hZ
  have heq := cellActualWeak_unique hab.le C hG V k hv.1 hb hk 0 0 U
    (extendCurve hab.le Z) slice D.limit hU hz (hinitial.trans hi.symm) t htI
  obtain ⟨W, hwv, hwb⟩ := interiorPulseFullTrace_native_polynomial_smoothing J hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ k hk hκ hab.le initial D
    (extendCurve hab.le Z) hz hi hwindow t htI ht
  exact ⟨W, hwv.trans heq.symm, hwb⟩

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! A proved L2 gap and periodic native entrance yield higher full-equation decay. -/

theorem interiorPulseActualWeak_native_gap_decay (J : ℕ) (hJ : 1 ≤ J)
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
      ⟨fun t _ => G t, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot,
        fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
      hG V hv.1 hb t (slice t) 0 0))
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
  · obtain ⟨W, hwv, hwb⟩ := interiorPulseActualWeak_native_short_propagation J hΛ hζ hν hr
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
    obtain ⟨W, hwv, hwb⟩ := interiorPulseActualWeak_native_smoothing_of_step J hΛ hζ hν hr
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

theorem interiorPulseActualWeak_native_gap_smoothing (J : ℕ)
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
      ⟨fun t _ => G t, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot,
        fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
      hG V hv.1 hb t (slice t) 0 0))
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
  obtain ⟨W, hwv, hwb⟩ := interiorPulseActualWeak_native_smoothing_of_step J hΛ hζ hν hr
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
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Every given scalar real homogeneous plane chain is the actual Bloch reconstructed evolution. -/

theorem scalarRealPlaneChain_blochValue {ι : Type*} [Fintype ι]
    (a b : ℝ) (hab : a ≤ b) (κ : Fin 1 → ι → ℕ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (C : ℝ) (hCpos : 0 < C) (hC : ∀ t i z, ‖cellDriftTorusSymbol v t i z‖ ≤ C)
    (f : ∀ p : Fin 1 × ι, PlaneHk Set.univ (κ p.1 p.2) ℝ)
    (u : ∀ p : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) ℝ)
    (w : ∀ p : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) ℝ)
    (hsln : IsCoupledWeakSolutionPlane (h := fun _ : Fin 1 × ι => ℝ) 1 a b v 2
      (fun p => κ p.1 p.2)
      (planeChainCoefficient (geometryScalarData (h := fun _ : ι => ℝ) 2 (fun t _ => G t)) κ)
      f (fun _ _ => 0) (fun _ _ => 0) u w)
    (p : Fin 1 × ι) (t : CellCompactTime a b) :
    planeHkValueOperator (κ p.1 p.2) (u p t) =
      planeComplexRealPartL2
        (planeBlochEnergyReconstructedTrace hab G hG v V hv.1 hb
          (ofRealL2 volume (planeHkValueOperator (κ p.1 p.2) (f p))) t) := by
  let f0 := planeHkValueOperator (κ p.1 p.2) (f p)
  let F := planeBlochEnergyField hab G hG v V hv.1 hb
    (planeCellBlochTransform centeredPlaneFrequencyBase 1 (by norm_num) (ofRealL2 volume f0))
  have hc := scalarRealPlaneChain_weakCurve a b hab κ G hG v hv C hCpos hC f u w hsln p
  have hc' := planeBlochEnergyRealWeakCurve hab G hG v hv V hb C hCpos hC (ofRealL2 volume f0)
  have hi : coupledPlaneL2Trace u p a =
      planeHkValueOperator 0 (cellEnergyPlaneRealTrace hab F a) := by
    rw [planeBlochEnergyRealTrace_initial hab G hG v V hv.1 hb f0, planeL2ZeroCarrier_value]
    change planeHkValueOperator (κ p.1 p.2) (u p a) = _
    rw [hsln.2.2.2.1 p]
  have he := planeRealBlochWeakCurve_unique hab G hG v hv V hb C hCpos hC
    (coupledPlaneL2Trace u p)
    (fun r => planeHkValueOperator 0 (cellEnergyPlaneRealTrace hab F r))
    (coupledPlaneH1Slice w p) (cellEnergyPlaneRealH1State hab F) hc hc' hi t t.property
  exact he.trans (planeBlochEnergyRealTrace_value hab G hG v V hv.1 hb (ofRealL2 volume f0) t)

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.CycleWords

/-! Polynomial native smoothing for the actual full finite equation, with its zeroth bound discharged. -/

theorem constructedReflectedActualWeak_native_polynomial_smoothing_aePotential (J : ℕ)
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
    {a b : ℝ} (hab : a < b)
    (hκ : AEStronglyMeasurable κ (volume.restrict (Icc a b)))
    (initial : ComplexCellL2)
    (U : ℝ → ComplexCellL2)
    (slice : ℝ → TorusHk 1 ℂ)
    (hU : CellWeakHilbertCurve a b U slice
      (fun t => cellDualDerivative
        ⟨fun s _ => G (-s), fun s x => -ocCellDrift α q Λ ζ m ν y₀ (-s) x,
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
        ⟨fun s _ => G (-s), fun s x => -ocCellDrift α q Λ ζ m ν y₀ (-s) x,
          fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ'⟩
        (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
        (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t (slice t) 0 0) := by
    apply hU.dual_congr
    filter_upwards [he] with t het
    exact cellDualDerivative_potential_congr
      ⟨fun s _ => G (-s), fun s x => -ocCellDrift α q Λ ζ m ν y₀ (-s) x,
        fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
      (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
        (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) κ κ' t het (slice t) 0 0
  exact constructedReflectedActualWeak_native_polynomial_smoothing J hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ' k hb' hm hab initial U slice hu' hinitial hwindow t htI ht

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! A periodic native entrance propagates on a short full-equation window without losing reserves. -/

theorem interiorPulseReflectedActualWeak_native_short_propagation (J : ℕ)
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
    (hshort : (constructedNativeWindowPrice J R k Cw *
      peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ 2) * (b - a) ≤ 1) :
    ∃ W : TorusHk J ℂ, torusHkValueCLM W = U b ∧
      ‖W‖ ^ 2 ≤ Real.exp 1 * ‖initial‖ ^ 2 := by
  apply cellActualWeak_native_of_finite_bound hab _ (cellMetric_timeReverse hG) V k (cellDrift_timeReverse hv).1
    (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) hκ hk
    (torusHkValueCLM initial) U slice hU hi J b ⟨hab.le, le_rfl⟩
    (Real.exp 1 * ‖initial‖ ^ 2) (mul_nonneg (Real.exp_pos 1).le (sq_nonneg _))
  intro N y hy hyinit
  have he := (interiorPulseReflectedGalerkin_native_window J N hΛ hζ hν hr y₀ hslot hv V hb G hG
    Cw hCw hw ξ R hR hξ hθ κ k hk hab.le y hy hshort J le_rfl).1
  have hi' : cellGalerkinNativeLiftCLM N J (y a) =
      cellGalerkinNativeLiftCLM N J (cellGalerkinL2Initial N (torusHkValueCLM initial)) := by
    apply TorusHk.ext_value
    change torusHkValueCLM (cellGalerkinNativeLiftCLM N J (y a)) =
      torusHkValueCLM (cellGalerkinNativeLiftCLM N J
        (cellGalerkinL2Initial N (torusHkValueCLM initial)))
    simpa only [cellGalerkinNativeLiftCLM_value] using hyinit
  have hn : ‖cellGalerkinNativeLiftCLM N J (y a)‖ ≤ ‖initial‖ := by
    rw [hi']
    exact cellGalerkinHigherInitial_norm_le N J initial
  exact he.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) hn 2) (Real.exp_pos 1).le)

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.CycleWords

/-! Polynomial native smoothing for the actual full finite equation, with its zeroth bound discharged. -/

theorem constructedReflectedActualWeak_unit_window_all_native_orders
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
    {a b : ℝ} (hab : a < b)
    (hκ : AEStronglyMeasurable κ (volume.restrict (Icc a b)))
    (initial : ComplexCellL2)
    (U : ℝ → ComplexCellL2)
    (slice : ℝ → TorusHk 1 ℂ)
    (hU : CellWeakHilbertCurve a b U slice
      (fun t => cellDualDerivative
        ⟨fun s _ => G (-s), fun s x => -ocCellDrift α q Λ ζ m ν y₀ (-s) x,
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
  exact constructedReflectedActualWeak_native_polynomial_smoothing_aePotential J hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ k hk hab hκ initial U slice hU hinitial hwindow.le b ⟨hab.le, le_rfl⟩ ht

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Full native gap smoothing with explicit polynomial contrast and classical time prices. -/

theorem interiorPulseActualWeak_native_gap_polynomial_smoothing (J : ℕ)
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
      ⟨fun t _ => G t, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot,
        fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
      hG V hv.1 hb t (slice t) 0 0))
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
  obtain ⟨W, hwv, hwb⟩ := interiorPulseActualWeak_native_gap_smoothing J hΛ hζ hν hr
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

/-! An arbitrary positive short step gives actual native smoothing without an entrance Sobolev premise. -/

theorem interiorPulseReflectedActualWeak_native_smoothing_of_step (J : ℕ)
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
        ⟨fun s _ => G (-s), fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x,
          fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
        (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
        (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t (slice t) 0 0))
    (hinitial : U a = initial) (hwindow : b - a ≤ 1)
    (δ : ℝ) (hδ : 0 < δ)
    (hshort : (constructedNativeWindowPrice J R k Cw *
      peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ 2) * δ ≤ 1)
    (hfit : J * δ ≤ b - a) :
    ∃ W : TorusHk J ℂ, torusHkValueCLM W = U b ∧ ‖W‖ ^ 2 ≤
      (Real.exp 1 * (2 * Real.exp 1) / δ) ^ J *
        (Real.exp (cellFullZerothGrowth (ν / ocMeanFlux α q Λ ζ m ν) Cw ξ k) * ‖initial‖ ^ 2) := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let A := cellFullZerothGrowth η Cw ξ k
  let P := (Real.exp 1 * (2 * Real.exp 1) / δ) ^ J
  have hP : 0 ≤ P := pow_nonneg (div_nonneg (by positivity) hδ.le) _
  have hA : 0 ≤ A := cellFullZerothGrowth_nonneg η Cw hCw ξ k ((norm_nonneg _).trans (hk a))
  apply cellActualWeak_native_of_finite_bound hab _ (cellMetric_timeReverse hG) V k (cellDrift_timeReverse hv).1
    (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) hκ hk
    initial U slice hU hinitial J b ⟨hab.le, le_rfl⟩
    (P * (Real.exp A * ‖initial‖ ^ 2))
    (mul_nonneg hP (mul_nonneg (Real.exp_pos A).le (sq_nonneg _)))
  intro N y hy hyinit
  let B := Real.exp A * ‖cellGalerkinValue N (y a)‖ ^ 2
  have hzero : ∀ t ∈ Icc a b, ‖cellGalerkinValue N (y t)‖ ^ 2 ≤ B := by
    intro t ht
    have he := cellFullGalerkin_zeroth_propagation N η Cw hCw (fun s => G (-s)) (cellMetric_timeReverse hG)
      (cellDrift_timeReverse hv) (cellDrift_timeReverse_scaled_bound hw) V
      (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) ξ κ k hk hab.le y hy t ht
    have ht1 : t - a ≤ 1 := (sub_le_sub_right ht.2 a).trans hwindow
    have hx : Real.exp (A * (t - a)) ≤ Real.exp A := Real.exp_le_exp.mpr
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left ht1 hA)
    exact he.trans (by simpa only [B, mul_comm] using
      mul_le_mul_of_nonneg_left hx (sq_nonneg ‖cellGalerkinValue N (y a)‖))
  have he := interiorPulseReflectedGalerkin_native_smoothing J N hΛ hζ hν hr y₀ hslot hv V hb G hG
    Cw hCw hw ξ R hR hξ hθ κ k hk hab.le y hy δ B hδ
    (mul_nonneg (Real.exp_pos A).le (sq_nonneg _)) hshort hzero b
    (by linarith only [hfit]) le_rfl
  have hi : ‖cellGalerkinValue N (y a)‖ ^ 2 ≤ ‖initial‖ ^ 2 := by
    rw [hyinit]
    exact pow_le_pow_left₀ (norm_nonneg _) (cellGalerkinL2Initial_norm_le N initial) 2
  exact he.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hi (Real.exp_pos A).le) hP)

/-! Any positive short full-equation window produces one smooth periodic endpoint representative. -/

theorem constructedReflectedActualWeak_positive_short_window_smooth
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
    (hκ : Measurable κ) {a b : ℝ} (hab : a < b)
    (initial : ComplexCellL2)
    (U : ℝ → ComplexCellL2)
    (slice : ℝ → TorusHk 1 ℂ)
    (hU : CellWeakHilbertCurve a b U slice
      (fun t => cellDualDerivative
        ⟨fun s _ => G (-s), fun s x => -ocCellDrift α q Λ ζ m ν y₀ (-s) x,
          fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
        (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
        (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t (slice t) 0 0))
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
  obtain ⟨W, hw, _⟩ := constructedReflectedActualWeak_native_smoothing_of_step J hΛ hζ hν hr y₀
    hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ k hk hκ hab initial U slice hU
    hinitial hwindow (min δ₀ ((b - a) / ((J : ℝ) + 1))) hδ hbudget hfit
  exact ⟨W, hw⟩

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The full reversed equation has the sharp gap on the annihilator of the actual forward graph. -/

theorem canonicalAdjoint_graph_kernel_decay (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 1024)
    (hfreq : Cw * fibreNorm ξ + 1032 * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2 / 16)
    {a b : ℝ} (hab : a ≤ b)
    (U : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (hU : CellWeakHilbertCurve (-b) (-a) U slice (fun t => cellDualDerivative
      ⟨fun s _ => G (-s), fun s x => -v (-s) x, fun i => (Real.sqrt η : ℂ) * -ξ i, 0⟩
      (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
      (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t (slice t) 0 0))
    (hker :
      let r := fibreCoefficientFamily η Cw hη G hG hv hw
      cellComplexPair (U (-b)) (cellFiberCLM Complex.conjCLE.toContinuousLinearMap
        (cellRawTrace (fibreSeriesJet r ξ) b + cellConstantCLM 1)) = 0) :
    ∀ τ ∈ Icc (-b) (-a), ‖U τ‖ ^ 2 ≤
      Real.exp (-(6 * Real.pi ^ 2) * (τ + b)) * ‖U (-b)‖ ^ 2 := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  have hrad := fibreCoefficientMajorantRadius_pos hCw
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := by linarith only [hξ, hrad]
  have hkt := canonicalAdjoint_graph_kernel_transport η Cw hη0 hη hCw G hG hv hm hw V hb
    ξ hξR U slice hU hker
  have hgref : IsMetricNearIdentity (fun t _ => G (-t)) g := fun t x z => hg (-t) x z
  have hf : Cw * fibreNorm (fun i => -ξ i) + 1032 * fibreNorm (fun i => -ξ i) ^ 2 ≤
      Real.pi ^ 2 / 16 := by simpa only [fibreNorm_neg] using hfreq
  have hd := cellWeakBloch_rowKernel_decay (by linarith : -b ≤ -a) η Cw hη0 hη hCw
    (fun t => G (-t)) (cellMetric_timeReverse hG) hgref hgsmall (cellDrift_timeReverse hv)
    (cellDrift_timeReverse_scaled_bound hw) V
    (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x)
    (fun i => -ξ i) hf U slice hU
    (fun τ => cellRawTrace (fibreSeriesJet r ξ) (-τ) + cellConstantCLM 1)
    (fun τ _ => ?_) hkt
  · intro τ hτ
    simpa only [sub_neg_eq_add] using hd τ hτ
  · rw [add_sub_cancel_right]
    have hn := fibreCoefficientFamily_graph_class_correction_bound η Cw hη hCw G hG hv hw ξ hξR (-τ)
    apply hn.trans
    have he : (2 / fibreCoefficientMajorantRadius Cw) * fibreNorm ξ =
        (2 * fibreNorm ξ) / fibreCoefficientMajorantRadius Cw := by ring
    rw [he, div_le_iff₀ hrad]
    linarith only [hξ, hrad]

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Every positive full-equation interval has a smooth periodic endpoint representative. -/

theorem constructedReflectedActualWeak_positive_window_smooth
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
    (hκ : Measurable κ) {a b : ℝ} (hab : a < b)
    (initial : ComplexCellL2)
    (U : ℝ → ComplexCellL2)
    (slice : ℝ → TorusHk 1 ℂ)
    (hU : CellWeakHilbertCurve a b U slice
      (fun t => cellDualDerivative
        ⟨fun s _ => G (-s), fun s x => -ocCellDrift α q Λ ζ m ν y₀ (-s) x,
          fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
        (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
        (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t (slice t) 0 0))
    (hinitial : U a = initial) :
    ∃ f : Vec 2 → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧ AVenhance.IsZ2Periodic f ∧
      f =ᵐ[volume.restrict AVenhance.unitCube] (U b : Vec 2 → ℂ) := by
  by_cases hshort : b - a ≤ 1
  · exact constructedReflectedActualWeak_positive_short_window_smooth hΛ hζ hν hr y₀ hv V hb
      G hG Cw hCw hw ξ R hR hξ hθ κ k hk hκ hab initial U slice hU hinitial hshort
  · have ha : a ≤ b - 1 := by linarith only [hshort]
    have hsub : Icc (b - 1) b ⊆ Icc a b := Icc_subset_Icc ha le_rfl
    exact constructedReflectedActualWeak_positive_short_window_smooth hΛ hζ hν hr y₀ hv V hb
      G hG Cw hCw hw ξ R hR hξ hθ κ k hk hκ (by linarith : b - 1 < b)
      (U (b - 1)) U slice (hU.mono hsub) rfl (by ring_nf; exact le_rfl)

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.CycleWords

/-! Polynomial native smoothing for the actual full finite equation, with its zeroth bound discharged. -/

theorem interiorPulseReflectedActualWeak_native_polynomial_smoothing (J : ℕ)
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
  let C : CellCoefficients :=
    ⟨fun s _ => G (-s), fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x,
      fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
  obtain ⟨D⟩ := cellGalerkin_actual_limit_data hab.le C (cellMetric_timeReverse hG) V k (cellDrift_timeReverse hv).1
    (fun s x => by simpa only [C, Pi.neg_apply, neg_sq] using hb (-s) x) hκ hk
    0 0 measurable_zero measurable_zero (by simp [cellL2Norm]) (by simp [cellL2Norm]) initial
  obtain ⟨Z, hZ, hi⟩ := D.exists_continuous_trace hab k hκ hk (by apply MemLp.zero) (by apply MemLp.zero)
  have hz : CellWeakHilbertCurve a b (extendCurve hab.le Z) D.limit
      (fun t => cellDualDerivative C (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
        (fun s x => by simpa only [C, Pi.neg_apply, neg_sq] using hb (-s) x) t (D.limit t) 0 0) := by
    change CellWeakHilbertCurve a b (extendCurve hab.le Z) D.limit
      (fun t => cellDualDerivative C (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
        (fun s x => by simpa only [C, Pi.neg_apply, neg_sq] using hb (-s) x) t (D.limit t)
        (cellSourceSlice 0 t) (fun j => cellSourceSlice (fun r x => (0 : PiLp 2 (fun _ : Fin 2 => ℂ)) j) t)) at hZ
    simpa only [PiLp.zero_apply, Pi.zero_def, cellSourceSlice_zero] using hZ
  have heq := cellActualWeak_unique hab.le C (cellMetric_timeReverse hG) V k (cellDrift_timeReverse hv).1
    (fun s x => by simpa only [C, Pi.neg_apply, neg_sq] using hb (-s) x) hk 0 0 U
    (extendCurve hab.le Z) slice D.limit hU hz (hinitial.trans hi.symm) t htI
  obtain ⟨W, hwv, hwb⟩ := interiorPulseReflectedTrace_native_polynomial_smoothing J hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ k hk hκ hab.le initial D
    (extendCurve hab.le Z) hz hi hwindow t htI ht
  exact ⟨W, hwv.trans heq.symm, hwb⟩

end AVRegularity.CycleWords
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! The coefficient inputs of each actual or frozen scalar chart piece. The cover controls the chart
metric only on its cell-time window `[ta/ℓ², (ta+T)/ℓ²]`, so the inputs are stated
for the metric clamped in time to that window (`metricClamp`), which agrees with the chart metric on
the window and hence on every piece. -/

theorem geometryCover_piece_scalar_inputs (Kmax : ℕ) (CG : ℕ → ℝ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream (Φ (m - 1)))
    {ν B T ta ρs g g0 a B₀ lam Cb CT : ℝ} {qJ : ℕ} (hqJ : Kmax + 1 ≤ qJ)
    {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
    (cov : IsGeometryCover α q Λ m ζ Φ hφ ν B T ta ρs g g0 a B₀ lam Cb CT qJ Kmax CG l₀ P y₀)
    (hg0 : g0 ≤ 1 / 4) (i : Fin P)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : G = ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ + i) ν
        (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i) ∨
      G = fun t _ => ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ + i) ν
        (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i) t 0)
    : ScalarCoefficientInputs Kmax CG
      (ocPieceStart α q Λ m ν ta (l₀ + i)) (ocPieceEnd α q Λ m ν ta T (l₀ + i))
      (ρs / ocEpsilon q Λ m) (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1))
      (ocCellDrift α q Λ ζ m ν (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i))
      a B₀ lam (metricClamp (ta / ocEll q Λ m ν ^ 2) ((ta + T) / ocEll q Λ m ν ^ 2) G) g := by
  let yc := ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i
  let left := ocPieceStart α q Λ m ν ta (l₀ + i)
  let right := ocPieceEnd α q Λ m ν ta T (l₀ + i)
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  have hE := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m - 1) hΛ
  have hell : 0 < ocEll q Λ m ν ^ 2 := by
    unfold ocEll
    exact sq_pos_of_pos (div_pos he (Real.sqrt_pos.mpr cov.pos.1))
  have hsub := ocPiece_interval_subset α q Λ m ν ta T (l₀ + i) hell
  have hwin : ta / ocEll q Λ m ν ^ 2 ≤ (ta + T) / ocEll q Λ m ν ^ 2 :=
    div_le_div_of_nonneg_right (by linarith [cov.pos.2.2.1]) hell.le
  have hnear := isMetricNearIdentity_metricClamp hwin
    (cellMetricChoice_nearIdentityOn α q Λ m hφ (l₀ + i) ν yc G hG _ g (cov.metric_near i))
  have hc : ∀ t ∈ Set.Icc left right,
      metricClamp (ta / ocEll q Λ m ν ^ 2) ((ta + T) / ocEll q Λ m ν ^ 2) G t = G t :=
    fun t ht => metricClamp_of_mem G (hsub ht)
  have hsym := cellMetricChoice_symmetric α q Λ m hφ (l₀ + i) ν yc G hG
  have hsm := metricChoice_spatial_contDiff _ G hG _ qJ (cov.metric_smooth i)
  have hj := metricChoice_spatial_jets _ G hG _ qJ
    (fun l => CG l * g * (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)) ^ l) (cov.metric_jets i)
  have hgm0 := restrict_time_coefficient_measurable G
    (matrix_coefficient_joint_measurable G (fun j k =>
      (cellMetricChoice_joint_contDiff α q Λ m hφ (l₀ + i) ν yc G hG j k).continuous)) left right
  have hgm : Measurable (fun p : Set.Icc left right × Vec 2 =>
      metricClamp (ta / ocEll q Λ m ν ^ 2) ((ta + T) / ocEll q Λ m ν ^ 2) G p.1 p.2) := by
    have heq : (fun p : Set.Icc left right × Vec 2 =>
        metricClamp (ta / ocEll q Λ m ν ^ 2) ((ta + T) / ocEll q Λ m ν ^ 2) G p.1 p.2) =
        fun p => G p.1 p.2 := funext fun p => by rw [hc p.1 p.1.2]
    rw [heq]
    exact hgm0
  have hvm := restrict_time_coefficient_measurable (ocCellDrift α q Λ ζ m ν yc)
    (cellDrift_joint_contDiff (α := α) (q := q) (m := m) hΛ hζ ν yc).continuous.measurable left right
  obtain ⟨M, hM⟩ := cellDrift_norm_bound (α := α) (q := q) (m := m) hΛ hζ ν yc
  have hscale : (ρs / ocEpsilon q Λ m) * (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)) ≤ 1 := by
    have hρ := cov.rho_R.trans cov.RE
    have heq : (ρs / ocEpsilon q Λ m) * (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)) =
      ρs / ocEpsilon q Λ (m - 1) := div_mul_div_cancel₀ he.ne'
    rw [heq]
    exact (div_le_one hE).mpr hρ
  exact ⟨geometryCover_piece_nonempty hΛ cov i, div_pos cov.pos.2.2.2 he,
    div_nonneg he.le hE.le, hscale, ⟨M, fun t _ z => hM t z⟩, hvm,
    (fun t _ => cellDrift_spatial_contDiff (α := α) (q := q) (m := m) hΛ hζ ν t yc),
    (fun t _ z => cellDrift_divergence_zero (α := α) (q := q) (m := m) hΛ hζ ν t yc z),
    cov.drift_pos.1, cov.drift_pos.2.1, cov.drift_pos.2.2,
    (fun l hl hK t ht z => cov.drift_jets i l hl hK t (hsub ht) z), cov.drift_scale, cov.drift_small,
    cov.g_range.1, cov.g_range.2.trans hg0, hgm, (fun t ht z => by rw [hc t ht]; exact hsym t z),
    hnear,
    (fun t ht j k => by
      rw [hc t ht]
      exact (hsm t (hsub ht) j k).of_le (by exact_mod_cast (show max Kmax 1 ≤ qJ by omega))),
    (fun t ht z l hl hK j k => by rw [hc t ht]; exact hj t (hsub ht) z l hl (by omega) j k)⟩

end AVRegularity.CycleWords
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Canonical graph histories forget entrance data whenever their actual drifts agree on a window. -/

theorem canonicalGraph_common_drift_window_difference_decay (η Cw : ℝ)
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
      Real.exp (-(Real.pi ^ 2 / 2) * (t - a)) * ‖cellRawTrace D a - cellRawTrace E a‖ ^ 2 := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hsv
  let s := fibreCoefficientFamily η Cw hη G hG hw hsw
  let D := fibreSeriesJet r ξ
  let E := fibreSeriesJet s ξ
  let lam := fibreSeriesC (fibreCoefficientSymbol η G v r) ξ
  let mu := fibreSeriesC (fibreCoefficientSymbol η G w s) ξ
  let U := fun t => cellRawTrace D t + cellConstantCLM 1
  let W := fun t => cellRawTrace E t + cellConstantCLM 1
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := by
    have hr := (hξ.trans (fibreWordRadius_le_graph Cw)).trans
      (fibreEvolutionRadius_le_majorant (Cw := Cw))
    have hR := fibreCoefficientMajorantRadius_pos hCw
    linarith
  have hsmall := fibreWord_frequency_small hCw ξ hξ
  have hlam : ∀ t, ‖lam t‖ ≤ fibreWordSymbolBound Cw * fibreNorm ξ ^ 2 :=
    fun t => fibreCoefficientFamily_word_symbol_bound η Cw hη0 hη hCw G hG hv hsv ξ hξR t
  have hρ : ∀ t, ‖W t - cellConstantCLM 1‖ ≤ fibreWordCorrectionBound Cw * fibreNorm ξ := by
    intro t
    simpa only [W, add_sub_cancel_right, fibreWordCorrectionBound] using
      fibreCoefficientFamily_graph_class_correction_bound η Cw hη hCw G hG hw hsw ξ hξR t
  have hρsmall : ∀ t, ‖W t - cellConstantCLM 1‖ ≤ 1 := fun t => (hρ t).trans hsmall.2.1
  have hdiff : ∀ t ∈ Icc a b, lam t - mu t =
      -Complex.I * cellBlochDriftMeanCLM η Cw hCw hv hsv ξ t (U t - W t) := by
    intro t ht
    simpa only [U, W, add_sub_add_right_eq_sub] using
      canonicalGraph_symbol_difference_at_common_drift η Cw hη hCw G hG
        v w hv hw hsv hsw ξ hξR t (hvw t ht).symm
  have h1 := fibreCoefficientFamily_graph_weak_evolution η Cw hη0 hη hCw G hG
    hv hmv hsv V hbv ξ hξR hab
  have h2 := fibreCoefficientFamily_graph_weak_evolution η Cw hη0 hη hCw G hG
    hw hmw hsw V hbw ξ hξR hab
  have h2' := cellWeak_drift_window_congr (fun t _ => G t) hG w v
    (fun j => (Real.sqrt η : ℂ) * ξ j) (fun t => -mu t) V hw.1 hv.1 hbw hbv
    hvw (fun _ => 0) (fun _ _ => 0) W (fun t => cellH1Slice E t + cellH1One) h2
  have hmean : ∀ t ∈ Icc a b, cellMean (U t) = cellMean (W t) := by
    intro t _
    rw [fibreCoefficientFamily_graph_class_mean η Cw hη hCw G hG hv hsv ξ hξR t,
      fibreCoefficientFamily_graph_class_mean η Cw hη hCw G hG hw hsw ξ hξR t]
  have he := cellWeak_normalized_graph_difference_decay hab η Cw hη0 hη hCw G hG
    hg hgsmall hv hsv V hbv ξ (fibreWordSymbolBound Cw) (fibreWordCorrectionBound Cw)
    hsmall.2.2 hsmall.1 (fibreScaledFrequency_coordinate_le η hη ξ)
    U W (fun t => cellH1Slice D t + cellH1One) (fun t => cellH1Slice E t + cellH1One)
    lam mu hlam hρ hρsmall hdiff h1 h2' hmean
  simpa only [U, W, add_sub_add_right_eq_sub] using he

end AVRegularity.CycleWords
end
