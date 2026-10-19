-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.ConstructedActualWeakNativeGapDecay
import AVRegularity.CycleWords.PlaneBlochEnergyRealStateIncrement
import AVRegularity.CycleEvolution.CellLimitMoments
import AVRegularity.CycleEvolution.CellEnergySpaceRawDirectionalLimit
import AVRegularity.CycleEvolution.CellEnergySpaceRawJetCauchyBound
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Full higher smoothing from an L2 entrance with the entire lower-order gap retained. -/

theorem constructedActualWeak_native_gap_smoothing (J : ℕ)
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
      ⟨fun t _ => G t, ocCellDrift α q Λ ζ m ν y₀,
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
  obtain ⟨W, hwv, hwb⟩ := constructedActualWeak_native_smoothing_of_step J hΛ hζ hν hr
    y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ k hk hκ hsb (U s) U slice
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
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! The actual backward Bloch evolution gives the scalar weak Duhamel formula. -/

theorem planeBlochDuhamel_pair {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (C : ℝ) (hCpos : 0 < C) (hC : ∀ t i z, ‖cellDriftTorusSymbol v t i z‖ ≤ C)
    (C' : ℝ) (hC'pos : 0 < C')
    (hC' : ∀ t i z, ‖cellDriftTorusSymbol (fun t x => -v t x) t i z‖ ≤ C')
    (Cr : ℝ) (hCrpos : 0 < Cr)
    (hCr : ∀ t i z, ‖cellDriftTorusSymbol (fun r x => -v (-r) x) t i z‖ ≤ Cr)
    (u : ℝ → Lp ℝ 2 (volume : Measure (Vec 2)))
    (slice source : ℝ → PlaneHk Set.univ 1 ℝ)
    (h : PlaneWeakHilbertCurve a b u slice
      (fun r => planeRealBlochGeneratorDual (G r) v hv r C (hC r) (slice r) + source r))
    (f : Lp ℝ 2 (volume : Measure (Vec 2))) :
    let F := planeBlochBackwardRealField hab G hG v hv V hb f
    inner ℝ (u b) f - inner ℝ (u a)
        (planeHkValueOperator 0 (cellEnergyPlaneRealTrace (neg_le_neg hab) F (-a))) =
      ∫ r in a..b, inner ℝ (source r) (cellEnergyPlaneRealH1State (neg_le_neg hab) F (-r)) := by
  let F := planeBlochBackwardRealField hab G hG v hv V hb f
  have he := planeWeakAdjointPair_forcing G hG v hv V hb C hCpos hC C' hC'pos hC'
    u (fun r => planeHkValueOperator 0 (cellEnergyPlaneRealTrace (neg_le_neg hab) F (-r)))
    slice (fun r => cellEnergyPlaneRealH1State (neg_le_neg hab) F (-r)) source h
    (planeBlochBackwardReal_weakCurve hab G hG v hv V hb Cr hCrpos hCr C' hC' f)
    (show a ∈ Icc a b from ⟨le_rfl, hab⟩) (show b ∈ Icc a b from ⟨hab, le_rfl⟩) hab
  rw [planeBlochBackwardReal_terminal hab G hG v hv V hb f] at he
  exact he

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev Filter
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
open scoped Topology
namespace AVRegularity.CycleWords

/-! Actual scalar multiplier weak limits satisfy their integrated test equation. -/

theorem CellScalarMultiplierLimitData.moment_ae
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
    (u₀ : ComplexCellL2)    (D : CellScalarMultiplierLimitData a b η hab G hv ξ hc A hA hb κ u₀)    (z : TorusHk 1 ℂ) : ∀ᵐ t ∂volume.restrict (Icc a b),
    inner ℝ (torusHkValueCLM (D.limit t)) (torusHkValueCLM z) =
      inner ℝ u₀ (torusHkValueCLM z) + ∫ r in a..t,
        cellScalarMultiplierForm η Cw hCw G hG hv hw ξ κ r (D.limit r) z := by
  obtain ⟨E, hE, hbound⟩ := D.uniform_trace_bound a b η hab hη0 hη G hG hv ξ hc A hA hb
    κ Cw hCw hw hκm k hκ hsmall L hL hκq hξ1 hwsmall u₀
  let F := (innerSL ℝ (torusHkValueCLM z)).comp (torusHkValueCLM (E := ℂ) (K := 1))
  let p := fun t => inner ℝ u₀ (torusHkValueCLM z) + ∫ r in a..t,
    cellScalarMultiplierForm η Cw hCw G hG hv hw ξ κ r (D.limit r) z
  let state := fun N t => (extendCurve hab (D.curve N) t).val
  have he (n : ℕ) (t : ℝ) : F (state (D.subsequence n) t) =
      inner ℝ (cellGalerkinValue (D.subsequence n) (extendCurve hab (D.curve (D.subsequence n)) t))
        (torusHkValueCLM z) := by
    change inner ℝ (torusHkValueCLM z)
      (cellGalerkinValue (D.subsequence n) (extendCurve hab (D.curve (D.subsequence n)) t)) = _
    exact real_inner_comm _ _
  have hs : ∀ n, ∀ᵐ t ∂volume.restrict (Icc a b),
      (F (state (D.subsequence n) t)) ^ 2 ≤ E * ‖torusHkValueCLM z‖ ^ 2 := by
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [he]
    have hi := abs_real_inner_le_norm
      (cellGalerkinValue (D.subsequence n) (extendCurve hab (D.curve (D.subsequence n)) t))
      (torusHkValueCLM z)
    have hh := (sq_le_sq₀ (abs_nonneg _)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hi
    rw [sq_abs, mul_pow] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (hbound _ t ht) (sq_nonneg _))
  have hl : ∀ᵐ t ∂volume.restrict (Icc a b),
      Tendsto (fun n => F (state (D.subsequence n) t)) atTop (𝓝 (p t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simpa only [he, p] using D.moment_primitive_tendsto a b η hab G hv ξ hc A hA hb κ u₀
      hG Cw hCw hw hκm k hκ z t ht
  have hm := cellWeak_scalar_moment_identification (fun n => state (D.subsequence n))
    (fun n => D.stateLp (D.subsequence n)) D.limit D.weak F p (E * ‖torusHkValueCLM z‖ ^ 2)
    (mul_nonneg hE (sq_nonneg _)) hs hl
  filter_upwards [hm] with t ht
  exact (real_inner_comm _ _).trans ht

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! A periodic native entrance propagates on a short full-equation window without losing reserves. -/

theorem constructedReflectedActualWeak_native_short_propagation (J : ℕ)
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
  have he := (constructedReflectedGalerkin_native_window J N hΛ hζ hν hr y₀ hv V hb G hG
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
open Homogenization MeasureTheory Set AVRegularity.Sobolev Filter
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
open scoped Topology
namespace AVRegularity.CycleWords

/-! Finite value moments converge at every time to the constructed continuous trace. -/

theorem CellScalarMultiplierLimitData.trace_moments_tendsto
    (a b η : ℝ) (hab : a ≤ b) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v) (ξ : Fin 2 → ℂ)
    (hc : ∀ t ∈ Icc a b, ContDiff ℝ (0 : ℕ) (v t))
    (A : Fin 1 → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ t ∈ Icc a b, ∀ l x,
      ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)
    (κ : ℝ → ℂ)
    (u₀ : ComplexCellL2)    (D : CellScalarMultiplierLimitData a b η hab G hv ξ hc A hA hb κ u₀)
    (hG : IsCellMetric (fun t _ => G t)) (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hκm : MemLp κ ⊤ (volume.restrict (Icc a b))) (k : ℝ) (hκ : ∀ t, ‖κ t‖ ≤ k)
    (U : ℝ → ComplexCellL2)
    (hU : CellWeakHilbertCurve a b U D.limit
      (fun t => cellScalarMultiplierDual η Cw hCw G hG hv hw ξ κ t (D.limit t)))
    (hinitial : U a = u₀) (z : TorusHk 1 ℂ) (t : ℝ) (ht : t ∈ Icc a b) :
    Tendsto (fun n => inner ℝ
      (cellGalerkinValue (D.subsequence n) (extendCurve hab (D.curve (D.subsequence n)) t))
      (torusHkValueCLM z)) atTop (𝓝 (inner ℝ (U t) (torusHkValueCLM z))) := by
  have he := hU.increment a ⟨le_rfl, hab⟩ t ht ht.1 z
  rw [hinitial] at he
  simp only [cellScalarMultiplierDual_pairing] at he
  have hv0 : inner ℝ (U t) (torusHkValueCLM z) =
      inner ℝ u₀ (torusHkValueCLM z) + ∫ r in a..t,
        cellScalarMultiplierForm η Cw hCw G hG hv hw ξ κ r (D.limit r) z := by
    linarith only [he]
  rw [hv0]
  exact D.moment_primitive_tendsto a b η hab G hv ξ hc A hA hb κ u₀ hG Cw hCw hw hκm k hκ z t ht

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Full native gap smoothing with explicit polynomial contrast and classical time prices. -/

theorem constructedActualWeak_native_gap_polynomial_smoothing (J : ℕ)
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
      ⟨fun t _ => G t, ocCellDrift α q Λ ζ m ν y₀,
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
  obtain ⟨W, hwv, hwb⟩ := constructedActualWeak_native_gap_smoothing J hΛ hζ hν hr
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
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The reversed full equation preserves the annihilator of the actual forward graph. -/

theorem canonicalAdjoint_graph_kernel_transport (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw)
    {a b : ℝ}
    (U : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (hU : CellWeakHilbertCurve (-b) (-a) U slice (fun t => cellDualDerivative
      ⟨fun s _ => G (-s), fun s x => -v (-s) x, fun i => (Real.sqrt η : ℂ) * -ξ i, 0⟩
      (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
      (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t (slice t) 0 0))
    (hker :
      let r := fibreCoefficientFamily η Cw hη G hG hv hw
      cellComplexPair (U (-b)) (cellFiberCLM Complex.conjCLE.toContinuousLinearMap
        (cellRawTrace (fibreSeriesJet r ξ) b + cellConstantCLM 1)) = 0) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    ∀ τ ∈ Icc (-b) (-a), cellComplexPair (U τ)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap
        (cellRawTrace (fibreSeriesJet r ξ) (-τ) + cellConstantCLM 1)) = 0 := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  have hq := CellWeakHilbertCurve.reflected_adjoint (fun t _ => G t) hG hv V hb
    (fun i => (Real.sqrt η : ℂ) * ξ i) (by simpa only [mul_neg] using hU)
  dsimp only
  dsimp only at hker
  intro τ hτ
  have ht : a ≤ -τ := by linarith only [hτ.2]
  have htb : -τ ≤ b := by linarith only [hτ.1]
  have hg := fibreCoefficientFamily_graph_homogeneous_evolution η Cw hη0 hη hCw G hG
    hv hm hw V hb ξ hξ htb
  have hc := cellWeakAdjointPairing htb
    ⟨fun t _ => G t, v, fun i => (Real.sqrt η : ℂ) * ξ i, 0⟩ hG V hv hb hg
    (hq.mono (Icc_subset_Icc ht le_rfl))
  dsimp only at hc
  simp only [cellComplexPair_scalar_left, intervalIntegral.integral_same,
    Complex.exp_zero, one_mul, neg_neg] at hc
  rw [cellComplexPair_bilinear_symm, hker, mul_zero] at hc
  exact (cellComplexPair_bilinear_symm _ _).trans hc.symm

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! An arbitrary positive short step gives actual native smoothing without an entrance Sobolev premise. -/

theorem constructedReflectedActualWeak_native_smoothing_of_step (J : ℕ)
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
  have he := constructedReflectedGalerkin_native_smoothing J N hΛ hζ hν hr y₀ hv V hb G hG
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
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.CycleWords

/-! Polynomial native smoothing for the actual full finite equation, with its zeroth bound discharged. -/

theorem interiorPulseFullTrace_native_polynomial_smoothing (J : ℕ)
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
      ⟨fun t _ => G t, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot,
        fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩ hG V hv.1 hb 0 0 initial)
    (U : ℝ → ComplexCellL2)
    (hU : CellWeakHilbertCurve a b U D.limit
      (fun t => cellDualDerivative
        ⟨fun t _ => G t, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot,
          fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
        hG V hv.1 hb t (D.limit t) 0 0))
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
  apply CellGalerkinLimitData.full_trace_native_of_uniform_bound hab _ hG V k hv.1 hb hκ hk initial D U hU hinitial J t htI
    (P * (Real.exp (cellFullZerothGrowth η Cw ξ k) * ‖initial‖ ^ 2))
    (mul_nonneg hP (mul_nonneg (Real.exp_pos _).le (sq_nonneg _)))
  intro N
  have he := interiorPulseFullGalerkin_native_polynomial_smoothing J N hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ k hk hab
    (extendCurve hab (D.curve N)) (CellGalerkinLimitData.full_homogeneous_strongTime hab _ hG V hv.1 hb initial D N) hwindow t ht htI.2
  have hi : ‖cellGalerkinValue N (extendCurve hab (D.curve N) a)‖ ^ 2 ≤ ‖initial‖ ^ 2 := by
    rw [D.initial_value N]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (cellGalerkinL2Initial_norm_le N initial)
  exact he.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hi (Real.exp_pos _).le) hP)

/-! Polynomial native smoothing for the actual full finite equation, with its zeroth bound discharged. -/

theorem constructedReflectedActualWeak_native_polynomial_smoothing (J : ℕ)
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
    (hinitial : U a = initial) (hwindow : b - a ≤ 1) (t : ℝ) (htI : t ∈ Icc a b)
    (ht : a + J * constructedNativeSmoothingTime J R k Cw (ν / ocMeanFlux α q Λ ζ m ν) ≤ t) :
    ∃ W : TorusHk J ℂ, torusHkValueCLM W = U t ∧ ‖W‖ ^ 2 ≤
      (Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1) * constructedNativeWindowPrice J R k Cw) ^ J *
        peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ (2 * J) *
        (Real.exp (cellFullZerothGrowth (ν / ocMeanFlux α q Λ ζ m ν) Cw ξ k) * ‖initial‖ ^ 2) := by
  let C : CellCoefficients :=
    ⟨fun s _ => G (-s), fun s x => -ocCellDrift α q Λ ζ m ν y₀ (-s) x,
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
  obtain ⟨W, hwv, hwb⟩ := constructedReflectedTrace_native_polynomial_smoothing J hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ k hk hκ hab.le initial D
    (extendCurve hab.le Z) hz hi hwindow t htI ht
  exact ⟨W, hwv.trans heq.symm, hwb⟩

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! A proved L2 gap and periodic native entrance yield higher full-equation decay. -/

theorem constructedReflectedActualWeak_native_gap_decay (J : ℕ) (hJ : 1 ≤ J)
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
  · obtain ⟨W, hwv, hwb⟩ := constructedReflectedActualWeak_native_short_propagation J hΛ hζ hν hr
      y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ k hk hκ hab U slice hU initial hi
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
    obtain ⟨W, hwv, hwb⟩ := constructedReflectedActualWeak_native_smoothing_of_step J hΛ hζ hν hr
      y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ k hk hκ hsb (U s) U slice
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

theorem constructedReflectedActualWeak_native_gap_smoothing (J : ℕ)
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
  obtain ⟨W, hwv, hwb⟩ := constructedReflectedActualWeak_native_smoothing_of_step J hΛ hζ hν hr
    y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ k hk hκ hsb (U s) U slice
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
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.CycleWords

/-! Polynomial native smoothing for the actual full finite equation, with its zeroth bound discharged. -/

theorem constructedActualWeak_native_polynomial_smoothing_aePotential (J : ℕ)
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
        ⟨fun t _ => G t, ocCellDrift α q Λ ζ m ν y₀,
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
        ⟨fun t _ => G t, ocCellDrift α q Λ ζ m ν y₀,
          fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ'⟩
        hG V hv.1 hb t (slice t) 0 0) := by
    apply hU.dual_congr
    filter_upwards [he] with t het
    exact cellDualDerivative_potential_congr
      ⟨fun t _ => G t, ocCellDrift α q Λ ζ m ν y₀,
        fun i => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i, κ⟩
      hG V hv.1 hb κ κ' t het (slice t) 0 0
  exact constructedActualWeak_native_polynomial_smoothing J hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ' k hb' hm hab initial U slice hu' hinitial hwindow t htI ht

end AVRegularity.CycleWords
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! The actual reverse correction forgets across a quiet future interval. -/

theorem canonicalAdjointGraph_quiet_future_norm_bound (η Cw : ℝ) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 1024)
    (s a : ℝ) (ha : 0 ≤ a) (hquiet : ∀ t ∈ Icc s (s + a), ∀ x, v t x = 0) :
    ‖cellRawTrace (fibreAdjointGraphRaw η Cw hη G hG hv hw ξ) (-s)‖ ≤
      (2 / fibreCoefficientMajorantRadius Cw) * fibreNorm ξ *
        Real.exp (-(2 * Real.pi ^ 2) * a) := by
  have hgrev : IsMetricNearIdentity (fun t _ => G (-t)) g := fun t x z => hg (-t) x z
  have hquietrev : ∀ t ∈ Icc (-s - a) (-s), ∀ x, -v (-t) x = 0 := by
    intro t ht x
    have hti : -t ∈ Icc s (s + a) := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    rw [hquiet (-t) hti x, neg_zero]
  have hnξ : fibreNorm (fun j => -ξ j) ≤ fibreCoefficientMajorantRadius Cw / 1024 := by
    rwa [fibreNorm_neg]
  have he := fibreCoefficientFamily_quiet_past η Cw hη hCw (fun t => G (-t))
    (cellMetric_timeReverse hG) hgrev hgsmall (cellDrift_timeReverse hv)
    (cellDrift_timeReverse_scaled_bound hw) (fun j => -ξ j) hnξ (-s) a ha hquietrev
  have hR := fibreCoefficientMajorantRadius_pos hCw
  have hξR : fibreNorm (fun j => -ξ j) ≤ fibreCoefficientMajorantRadius Cw := by
    rw [fibreNorm_neg]
    linarith only [hξ, hR]
  have hi := fibreCoefficientFamily_graph_isInverse η Cw hη hCw (fun t => G (-t))
    (cellMetric_timeReverse hG) (cellDrift_timeReverse hv)
    (cellDrift_timeReverse_scaled_bound hw) (fun j => -ξ j) hξR
  let D := fibreAdjointGraphRaw η Cw hη G hG hv hw ξ
  have hraw := cellRawTrace_ae D (-s) (hi.1.2.2.1 (-s) (mem_univ (-s))).1
  change cellL2Norm (cellValue D (-s)) ≤ _ at he
  rw [cellL2Norm_eq_of_class _ _ hraw, fibreNorm_neg] at he
  have hfn := fibreNorm_nonneg ξ
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp he

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.CycleWords

/-! Polynomial native smoothing for the actual full finite equation, with its zeroth bound discharged. -/

theorem constructedActualWeak_unit_window_all_native_orders
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
        ⟨fun t _ => G t, ocCellDrift α q Λ ζ m ν y₀,
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
  exact constructedActualWeak_native_polynomial_smoothing_aePotential J hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ κ k hk hab hκ initial U slice hU hinitial hwindow.le b ⟨hab.le, le_rfl⟩ ht

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! A periodic native entrance propagates on a short full-equation window without losing reserves. -/

theorem interiorPulseActualWeak_native_short_propagation (J : ℕ)
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
    (hshort : (constructedNativeWindowPrice J R k Cw *
      peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ 2) * (b - a) ≤ 1) :
    ∃ W : TorusHk J ℂ, torusHkValueCLM W = U b ∧
      ‖W‖ ^ 2 ≤ Real.exp 1 * ‖initial‖ ^ 2 := by
  apply cellActualWeak_native_of_finite_bound hab _ hG V k hv.1 hb hκ hk
    (torusHkValueCLM initial) U slice hU hi J b ⟨hab.le, le_rfl⟩
    (Real.exp 1 * ‖initial‖ ^ 2) (mul_nonneg (Real.exp_pos 1).le (sq_nonneg _))
  intro N y hy hyinit
  have he := (interiorPulseGalerkin_native_window J N hΛ hζ hν hr y₀ hslot hv V hb G hG
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
