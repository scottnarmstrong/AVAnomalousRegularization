-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.InteriorPulseActualWeakNativeShortPropagation
public import AVRegularity.CycleWords.ConstructedActualWeakNativeGapDecay
import AVRegularity.CycleWords.PlaneBlochEnergyRealStateIncrement
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Full native gap smoothing with explicit polynomial contrast and classical time prices. -/

theorem constructedReflectedActualWeak_native_gap_polynomial_smoothing (J : ℕ)
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
    (U : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (hU : CellWeakHilbertCurve a b U slice (fun t => cellDualDerivative
      ⟨fun s _ => G (-s), fun s x => -ocCellDrift α q Λ ζ m ν y₀ (-s) x,
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
  obtain ⟨W, hwv, hwb⟩ := constructedReflectedActualWeak_native_gap_smoothing J hΛ hζ hν hr
    y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ k hk hκ hab U slice hU γ hγ hgap
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
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.CycleWords

/-! The constructed scalar multiplier limit has the prescribed initial continuous L2 trace. -/

theorem CellScalarMultiplierLimitData.weakTimeData
    (a b η : ℝ) (hab : a ≤ b) (hη0 : 0 ≤ η) (hη : η ≤ 1) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v) (ξ : Fin 2 → ℂ)
    (hc : ∀ t ∈ Icc a b, ContDiff ℝ (0 : ℕ) (v t))
    (A : Fin 1 → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ t ∈ Icc a b, ∀ l x,
      ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)
    (κ : ℝ → ℂ) (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hκm : MemLp κ ⊤ (volume.restrict (Icc a b)))
    (k : ℝ) (hκ : ∀ t, ‖κ t‖ ≤ k)
    (hsmall : ∀ t ∈ Icc a b,
      264 * (∑ j, ‖(Real.sqrt η : ℂ) * ξ j‖ ^ 2) + 2 * ‖κ t‖ + 1 ≤ 2)
    (L : ℝ) (hL : 0 ≤ L)
    (hκq : ∀ t ∈ Icc a b, ‖κ t‖ ≤ L * fibreNorm ξ ^ 2)
    (hξ1 : fibreNorm ξ ≤ 1) (hwsmall : Cw * fibreNorm ξ ≤ 1)
    (u₀ : ComplexCellL2)    (D : CellScalarMultiplierLimitData a b η hab G hv ξ hc A hA hb κ u₀) :
    CellWeakTimeData a b D.limit
      (fun t => cellScalarMultiplierDual η Cw hCw G hG hv hw ξ κ t (D.limit t)) u₀ := by
  refine ⟨Lp.memLp D.limit, ?_, ?_⟩
  · exact cellScalarMultiplierDual_memLp η Cw hCw G hG hv hw ξ κ hκm k hκ
      D.limit (Lp.memLp D.limit)
  · intro z
    filter_upwards [D.moment_ae a b η hab hη0 hη G hG hv ξ hc A hA hb κ Cw hCw hw hκm k hκ
      hsmall L hL hκq hξ1 hwsmall u₀ z] with t ht
    simpa only [cellScalarMultiplierDual_pairing] using ht

theorem CellScalarMultiplierLimitData.exists_continuous_trace
    (a b η : ℝ) (hab : a ≤ b) (hη0 : 0 ≤ η) (hη : η ≤ 1) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v) (ξ : Fin 2 → ℂ)
    (hc : ∀ t ∈ Icc a b, ContDiff ℝ (0 : ℕ) (v t))
    (A : Fin 1 → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ t ∈ Icc a b, ∀ l x,
      ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)
    (κ : ℝ → ℂ) (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hκm : MemLp κ ⊤ (volume.restrict (Icc a b)))
    (k : ℝ) (hκ : ∀ t, ‖κ t‖ ≤ k)
    (hsmall : ∀ t ∈ Icc a b,
      264 * (∑ j, ‖(Real.sqrt η : ℂ) * ξ j‖ ^ 2) + 2 * ‖κ t‖ + 1 ≤ 2)
    (L : ℝ) (hL : 0 ≤ L)
    (hκq : ∀ t ∈ Icc a b, ‖κ t‖ ≤ L * fibreNorm ξ ^ 2)
    (hξ1 : fibreNorm ξ ≤ 1) (hwsmall : Cw * fibreNorm ξ ≤ 1)
    (u₀ : ComplexCellL2)    (D : CellScalarMultiplierLimitData a b η hab G hv ξ hc A hA hb κ u₀)    (hab' : a < b) :
    ∃ U : ContinuousMap (Icc a b) ComplexCellL2,
      CellWeakHilbertCurve a b (extendCurve hab U) D.limit
        (fun t => cellScalarMultiplierDual η Cw hCw G hG hv hw ξ κ t (D.limit t)) ∧
      extendCurve hab U a = u₀ := by
  exact (D.weakTimeData a b η hab hη0 hη G hG hv ξ hc A hA hb κ Cw hCw hw hκm k hκ
    hsmall L hL hκq hξ1 hwsmall u₀).exists_hilbert_curve hab'

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Any positive short full-equation window produces one smooth periodic endpoint representative. -/

theorem constructedActualWeak_positive_short_window_smooth
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
        ⟨fun t _ => G t, ocCellDrift α q Λ ζ m ν y₀,
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
  obtain ⟨W, hw, _⟩ := constructedActualWeak_native_smoothing_of_step J hΛ hζ hν hr y₀
    hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ k hk hκ hab initial U slice hU
    hinitial hwindow (min δ₀ ((b - a) / ((J : ℝ) + 1))) hδ hbudget hfit
  exact ⟨W, hw⟩

/-! Every positive full-equation interval has a smooth periodic endpoint representative. -/

theorem constructedActualWeak_positive_window_smooth
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
        ⟨fun t _ => G t, ocCellDrift α q Λ ζ m ν y₀,
          fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
        hG V hv.1 hb t (slice t) 0 0))
    (hinitial : U a = initial) :
    ∃ f : Vec 2 → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧ AVenhance.IsZ2Periodic f ∧
      f =ᵐ[volume.restrict AVenhance.unitCube] (U b : Vec 2 → ℂ) := by
  by_cases hshort : b - a ≤ 1
  · exact constructedActualWeak_positive_short_window_smooth hΛ hζ hν hr y₀ hv V hb
      G hG Cw hCw hw ξ R hR hξ hθ κ k hk hκ hab initial U slice hU hinitial hshort
  · have ha : a ≤ b - 1 := by linarith only [hshort]
    have hsub : Icc (b - 1) b ⊆ Icc a b := Icc_subset_Icc ha le_rfl
    exact constructedActualWeak_positive_short_window_smooth hΛ hζ hν hr y₀ hv V hb
      G hG Cw hCw hw ξ R hR hξ hθ κ k hk hκ (by linarith : b - 1 < b)
      (U (b - 1)) U slice (hU.mono hsub) rfl (by ring_nf; exact le_rfl)

/-! An arbitrary positive short step gives actual native smoothing without an entrance Sobolev premise. -/

theorem interiorPulseActualWeak_native_smoothing_of_step (J : ℕ)
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
  apply cellActualWeak_native_of_finite_bound hab _ hG V k hv.1 hb hκ hk
    initial U slice hU hinitial J b ⟨hab.le, le_rfl⟩
    (P * (Real.exp A * ‖initial‖ ^ 2))
    (mul_nonneg hP (mul_nonneg (Real.exp_pos A).le (sq_nonneg _)))
  intro N y hy hyinit
  let B := Real.exp A * ‖cellGalerkinValue N (y a)‖ ^ 2
  have hzero : ∀ t ∈ Icc a b, ‖cellGalerkinValue N (y t)‖ ^ 2 ≤ B := by
    intro t ht
    have he := cellFullGalerkin_zeroth_propagation N η Cw hCw G hG hv hw V hb ξ κ k hk hab.le y hy t ht
    have ht1 : t - a ≤ 1 := (sub_le_sub_right ht.2 a).trans hwindow
    have hx : Real.exp (A * (t - a)) ≤ Real.exp A := Real.exp_le_exp.mpr
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left ht1 hA)
    exact he.trans (by simpa only [B, mul_comm] using
      mul_le_mul_of_nonneg_left hx (sq_nonneg ‖cellGalerkinValue N (y a)‖))
  have he := interiorPulseGalerkin_native_smoothing J N hΛ hζ hν hr y₀ hslot hv V hb G hG
    Cw hCw hw ξ R hR hξ hθ κ k hk hab.le y hy δ B hδ
    (mul_nonneg (Real.exp_pos A).le (sq_nonneg _)) hshort hzero b
    (by linarith only [hfit]) le_rfl
  have hi : ‖cellGalerkinValue N (y a)‖ ^ 2 ≤ ‖initial‖ ^ 2 := by
    rw [hyinit]
    exact pow_le_pow_left₀ (norm_nonneg _) (cellGalerkinL2Initial_norm_le N initial) 2
  exact he.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hi (Real.exp_pos A).le) hP)

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Common numerical choices simultaneously retain full fibre propagation and buffered graph/symbol prices. -/

def scalarBufferedGraphPrice (K : ScalarConstants) (j : ℕ) : ℝ :=
  max (max (K.Cj j)
    (smoothPeriodicGapPrice (fun k => 2 * K.Cj k)
      (20 * fibreWordCorrectionBound K.Cw + 16 * fibreWordCorrectionBound K.Cw ^ 2) j)) (max
    (smoothPeriodicGapPrice (fun k => 2 * K.Cj k) (2 * fibreWordCorrectionBound K.Cw) j)
    (2 * K.Cw * fibreWordCorrectionBound K.Cw))

def scalarBufferedComparisonConstants (K : ScalarConstants) : ScalarConstants :=
  scalarConstantsWithGapRates
    (scalarConstantsWithJetPrices
      (scalarConstantsWithRadius K (min K.ξ0 (fibreWordRadius K.Cw)))
      (scalarBufferedGraphPrice K))
    (fun j => (Real.pi ^ 2 / 4) / (2 : ℝ) ^ j)

theorem scalarBufferedComparisonConstants_rate_pos (K : ScalarConstants) (j : ℕ) :
    0 < (scalarBufferedComparisonConstants K).cj j := by
  change 0 < (Real.pi ^ 2 / 4) / (2 : ℝ) ^ j
  positivity

def fibreScalarDataWithBufferedConstants {K : ScalarConstants} {η t₀ S : ℝ}
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    (d : FibreScalarData K η G v t₀ S) (hξ : 0 < K.ξ0) (hCw : 0 ≤ K.Cw)
    (hCg : 0 ≤ K.Cg) (hC : ∀ j, 0 ≤ K.Cj j)
    (hc : ∀ j, Real.pi ^ 2 / 4 ≤ K.cj j) :
    FibreScalarData (scalarBufferedComparisonConstants K) η G v t₀ S := by
  let R := min K.ξ0 (fibreWordRadius K.Cw)
  let d₁ := fibreScalarDataWithRadius d R (lt_min hξ (fibreWordRadius_pos hCw))
    (min_le_left _ _) hCg
  let d₂ := fibreScalarDataWithJetPrices d₁ (scalarBufferedGraphPrice K)
    (fun j => (le_max_left _ _).trans (le_max_left _ _))
  exact fibreScalarDataWithGapRates d₂ (fun j => (Real.pi ^ 2 / 4) / (2 : ℝ) ^ j)
    (fun j => (div_le_self (by positivity) (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))).trans (hc j))
    (fun j => (hC j).trans ((le_max_left _ _).trans (le_max_left _ _)))

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.CycleWords

/-! Polynomial native smoothing for the actual full finite equation, with its zeroth bound discharged. -/

theorem interiorPulseReflectedTrace_native_polynomial_smoothing (J : ℕ)
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
    (hκ : Measurable κ) {a b : ℝ} (hab : a ≤ b)
    (initial : ComplexCellL2)
    (D : CellGalerkinLimitData a b hab
      ⟨fun s _ => G (-s), fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x,
        fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩ (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
        (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) 0 0 initial)
    (U : ℝ → ComplexCellL2)
    (hU : CellWeakHilbertCurve a b U D.limit
      (fun t => cellDualDerivative
        ⟨fun s _ => G (-s), fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x,
          fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
        (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
        (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t (D.limit t) 0 0))
    (hinitial : U a = initial) (hwindow : b - a ≤ 1) (t : ℝ) (htI : t ∈ Icc a b)
    (ht : a + J * constructedNativeSmoothingTime J R k Cw (ν / ocMeanFlux α q Λ ζ m ν) ≤ t) :
    ∃ W : TorusHk J ℂ, torusHkValueCLM W = U t ∧ ‖W‖ ^ 2 ≤
      (Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1) * constructedNativeWindowPrice J R k Cw) ^ J *
        peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ (2 * J) *
        (Real.exp (cellFullZerothGrowth (ν / ocMeanFlux α q Λ ζ m ν) Cw ξ k) * ‖initial‖ ^ 2) := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let P := (Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1) * constructedNativeWindowPrice J R k Cw) ^ J *
    peFactor η ^ (2 * J)
  have hM := constructedNativeWindowPrice_pos J R k Cw hR ((norm_nonneg _).trans (hk a)) hCw
  have hP : 0 ≤ P := by
    unfold P
    exact mul_nonneg (pow_nonneg (by positivity) _) (pow_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans (one_le_peFactor η)) _)
  apply CellGalerkinLimitData.full_trace_native_of_uniform_bound hab _ (cellMetric_timeReverse hG) V k (cellDrift_timeReverse hv).1
    (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) hκ hk initial D U hU hinitial J t htI
    (P * (Real.exp (cellFullZerothGrowth η Cw ξ k) * ‖initial‖ ^ 2))
    (mul_nonneg hP (mul_nonneg (Real.exp_pos _).le (sq_nonneg _)))
  intro N
  have he := interiorPulseReflectedGalerkin_native_polynomial_smoothing J N hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ k hk hab
    (extendCurve hab (D.curve N)) (CellGalerkinLimitData.full_homogeneous_strongTime hab _ (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
        (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) initial D N) hwindow t ht htI.2
  have hi : ‖cellGalerkinValue N (extendCurve hab (D.curve N) a)‖ ^ 2 ≤ ‖initial‖ ^ 2 := by
    rw [D.initial_value N]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (cellGalerkinL2Initial_norm_le N initial)
  exact he.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hi (Real.exp_pos _).le) hP)

end AVRegularity.CycleWords
end
