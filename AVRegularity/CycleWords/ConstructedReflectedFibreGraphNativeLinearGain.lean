-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.CanonicalGraphCommonDriftWindowDifferenceDecay
public import AVRegularity.CycleWords.ConstructedFastNativePolynomialPrice
import AVRegularity.CycleWords.InteriorPulseReflectedActualWeakAllNativeOrders
import AVRegularity.CycleWords.GeometryErrorPieceMassBudget
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.CycleWords

/-! Uniform native orders for the actual reversed full graph. -/

def constructedReflectedGraphNativeSquareBudget (J : ℕ) (R Cg Cw η : ℝ) : ℝ :=
  (Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1) *
    constructedNativeWindowPrice J R ((8 + Cw * Cg) * R ^ 2) Cw) ^ J *
    peFactor η ^ (2 * J) *
    (Real.exp (constructedAllOrderPrice 0 R ((8 + Cw * Cg) * R ^ 2) Cw) * (1 + Cg * R) ^ 2)

theorem constructedReflectedFibreGraph_uniform_native_orders
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
    ∀ J : ℕ, ∃ W : TorusHk J ℂ,
      torusHkValueCLM W = cellRawTrace (fibreSeriesJet r ξ) t + cellConstantCLM 1 ∧
      ‖W‖ ^ 2 ≤
        (Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1) *
          constructedNativeWindowPrice J R ((8 + Cw * Cg) * R ^ 2) Cw) ^ J *
        peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ (2 * J) *
        (Real.exp (constructedAllOrderPrice 0 R ((8 + Cw * Cg) * R ^ 2) Cw) * (1 + Cg * R) ^ 2) := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let vref := fun s x => -ocCellDrift α q Λ ζ m ν y₀ (-s) x
  have hvref : IsCellDrift vref := cellDrift_timeReverse hv
  have hGref := cellMetric_timeReverse hG
  have hbref : ∀ s x, ∑ j, vref s x j ^ 2 ≤ V ^ 2 := by
    intro s x
    simpa only [vref, Pi.neg_apply, neg_sq] using hb (-s) x
  have hwref : ∀ s x, Real.sqrt η * Real.sqrt (∑ i, vref s x i ^ 2) ≤ Cw := by
    intro s x
    simpa only [vref, Pi.neg_apply, neg_sq, η] using hw (-s) x
  have hmref : ∀ s (j : Fin 2), cellMean (fun x => (vref s x j : ℂ)) = 0 := by
    intro s j
    dsimp only [vref, Pi.neg_apply]
    simp only [Complex.ofReal_neg, cellMean, integral_neg]
    change -cellMean (fun x => (ocCellDrift α q Λ ζ m ν y₀ (-s) x j : ℂ)) = 0
    rw [hm, neg_zero]
  let k := (8 + Cw * Cg) * R ^ 2
  have hk : 0 ≤ k := by unfold k; positivity
  have hκ : ∀ s, ‖-fibreSeriesC lam ξ s‖ ≤ k := by
    intro s
    rw [norm_neg]
    exact (fibreGraph_symbol_quadratic_bound hgraph hη0 hη hCg hCw hGref hvref hwref ξ hdisc s).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (fibreNorm_nonneg ξ) hξ 2) (by positivity))
  have hκm : AEStronglyMeasurable (fun s => -fibreSeriesC lam ξ s)
      (volume.restrict (Icc (t - 1) t)) :=
    ((CycleDamping.graph_symbol_aestronglyMeasurable hGref hvref hgraph ξ hdisc).neg).mono_measure
      Measure.restrict_le_self
  have he := fibreGraph_actual_weak_evolution hgraph hη0 hη hCw hGref hvref hmref hwref V hbref ξ hdisc
    (by linarith : t - 1 ≤ t)
  have hn : ‖cellRawTrace (fibreSeriesJet r ξ) (t - 1) + cellConstantCLM 1‖ ≤ 1 + Cg * R :=
    (fibreGraph_normalized_mode_norm_le hgraph hCg ξ hdisc (t - 1)).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hξ hCg))
  have ht : (∑ i : Fin 2, ‖(Real.sqrt η : ℂ) * ξ i‖ ^ 2) ≤ 2 * R ^ 2 := by
    simp only [Fin.sum_univ_two]
    exact (add_le_add (pow_le_pow_left₀ (norm_nonneg _) (hθ 0) 2)
      (pow_le_pow_left₀ (norm_nonneg _) (hθ 1) 2)).trans_eq (by ring)
  have hA : cellFullZerothGrowth η Cw ξ k ≤ constructedAllOrderPrice 0 R k Cw := by
    have hf := mul_le_mul_of_nonneg_left hξ hCw
    unfold cellFullZerothGrowth constructedAllOrderPrice
    linarith only [ht, hf]
  have hall := constructedReflectedActualWeak_unit_window_all_native_orders hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ
    (fun s => -fibreSeriesC lam ξ s) k hκ
    (by linarith : t - 1 < t) hκm
    (cellRawTrace (fibreSeriesJet r ξ) (t - 1) + cellConstantCLM 1)
    (fun s => cellRawTrace (fibreSeriesJet r ξ) s + cellConstantCLM 1)
    (fun s => cellH1Slice (fibreSeriesJet r ξ) s + cellH1One) he rfl (by ring)
  intro J
  obtain ⟨W, hwv, hwb⟩ := hall J
  refine ⟨W, hwv, hwb.trans ?_⟩
  have hM := constructedNativeWindowPrice_pos J R k Cw hR hk hCw
  apply mul_le_mul_of_nonneg_left
  · exact mul_le_mul (Real.exp_le_exp.mpr hA)
      ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn) (sq_nonneg _) (Real.exp_pos _).le
  · change 0 ≤ (Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1) *
      constructedNativeWindowPrice J R k Cw) ^ J * peFactor η ^ (2 * J)
    exact mul_nonneg (pow_nonneg (by positivity) _)
      (pow_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans (one_le_peFactor η)) _)

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! One real price covers positive-time higher decay, zero-time projection, and order-zero decay. -/

def constructedForwardHigherDecayPrice (J : ℕ) (R Cw : ℝ) : ℝ :=
  nativeSobolevWordPrice J * (Fintype.card (JetIndex2 J) : ℝ) *
    (Real.sqrt (constructedNativeGapBasePrice J R 0 Cw (6 * Real.pi ^ 2)) *
      (1 + 4 * Real.sqrt (constructedGraphNativeBaseSquareBudget J R
        (AVRegularity.CycleEvolution.fibreCoefficientGraphBound Cw) Cw)))

def constructedForwardEntrancePrice (J : ℕ) (R Cw : ℝ) : ℝ :=
  nativeSobolevWordPrice J * (Fintype.card (JetIndex2 J) : ℝ) *
    (1 + 4 * Real.sqrt (constructedGraphNativeBaseSquareBudget J R
      (AVRegularity.CycleEvolution.fibreCoefficientGraphBound Cw) Cw))

def constructedForwardZeroDecayPrice (R Cw : ℝ) : ℝ :=
  nativeSobolevWordPrice 0 * (26 * Real.sqrt (Real.exp (6 * Real.pi ^ 2) *
    constructedGapSmoothingBasePrice 0 R 0 Cw * Real.exp (constructedAllOrderPrice 0 R 0 Cw)))

def constructedForwardDecayPrice (J : ℕ) (R Cw : ℝ) : ℝ :=
  max 1 (max (constructedForwardHigherDecayPrice J R Cw)
    (max (constructedForwardEntrancePrice J R Cw) (constructedForwardZeroDecayPrice R Cw)))

theorem constructedForwardHigherDecayPrice_le (J : ℕ) (R Cw : ℝ) :
    constructedForwardHigherDecayPrice J R Cw ≤ constructedForwardDecayPrice J R Cw :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem constructedForwardEntrancePrice_le (J : ℕ) (R Cw : ℝ) :
    constructedForwardEntrancePrice J R Cw ≤ constructedForwardDecayPrice J R Cw :=
  (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))

theorem constructedForwardZeroDecayPrice_le (J : ℕ) (R Cw : ℝ) :
    constructedForwardZeroDecayPrice R Cw ≤ constructedForwardDecayPrice J R Cw :=
  (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))

theorem constructedForwardEntrance_native_price (J : ℕ) (R Cw η : ℝ) :
    1 + 4 * Real.sqrt (constructedGraphNativeSquareBudget J R
      (AVRegularity.CycleEvolution.fibreCoefficientGraphBound Cw) Cw η) ≤
      (1 + 4 * Real.sqrt (constructedGraphNativeBaseSquareBudget J R
        (AVRegularity.CycleEvolution.fibreCoefficientGraphBound Cw) Cw)) * peFactor η ^ (2 * J) := by
  apply (constructedFastNativeEntrance_polynomial_price J R
    (AVRegularity.CycleEvolution.fibreCoefficientGraphBound Cw) Cw η).trans
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (one_le_peFactor η) (by omega)) (by positivity)

end AVRegularity.CycleWords
end

section
namespace AVRegularity.CycleWords

/-! The initial slow projection and final smoothing have one polynomial contrast price. -/

theorem constructedAdjointFastNativeEntrance_polynomial_price (J : ℕ) (R Cg Cw η : ℝ) :
    1 + 6 * Real.sqrt (constructedGraphNativeSquareBudget J R Cg Cw η) ≤
      (1 + 6 * Real.sqrt (constructedGraphNativeBaseSquareBudget J R Cg Cw)) *
        peFactor η ^ J := by
  rw [constructedGraphNativeSquareBudget_sqrt, add_mul, one_mul]
  have hp := one_le_peFactor_pow η J
  linarith only [hp]

theorem constructedAdjointFastNativeDecay_polynomial_price (J : ℕ) (R Cg Cw η γ τ : ℝ) :
    (Real.sqrt (constructedNativeGapBasePrice J R 0 Cw γ) * peFactor η ^ J *
      Real.exp (-γ * τ / 2)) *
        (1 + 6 * Real.sqrt (constructedGraphNativeSquareBudget J R Cg Cw η)) ≤
      (Real.sqrt (constructedNativeGapBasePrice J R 0 Cw γ) *
        (1 + 6 * Real.sqrt (constructedGraphNativeBaseSquareBudget J R Cg Cw))) *
          peFactor η ^ (2 * J) * Real.exp (-γ * τ / 2) := by
  have hp : 0 ≤ peFactor η := (by norm_num : (0 : ℝ) ≤ 1).trans (one_le_peFactor η)
  have he := mul_le_mul_of_nonneg_left
    (constructedAdjointFastNativeEntrance_polynomial_price J R Cg Cw η)
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg (constructedNativeGapBasePrice J R 0 Cw γ))
      (pow_nonneg hp J)) (Real.exp_pos (-γ * τ / 2)).le)
  calc
    _ ≤ _ := he
    _ = _ := by rw [show 2 * J = J + J by omega, pow_add]; ring

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.CycleWords

/-! Polynomial native smoothing for the actual full finite equation, with its zeroth bound discharged. -/

theorem interiorPulseFibreGraph_uniform_native_orders
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
    ∀ J : ℕ, ∃ W : TorusHk J ℂ,
      torusHkValueCLM W = cellRawTrace (fibreSeriesJet r ξ) t + cellConstantCLM 1 ∧
      ‖W‖ ^ 2 ≤
        (Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1) *
          constructedNativeWindowPrice J R ((8 + Cw * Cg) * R ^ 2) Cw) ^ J *
        peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ (2 * J) *
        (Real.exp (constructedAllOrderPrice 0 R ((8 + Cw * Cg) * R ^ 2) Cw) * (1 + Cg * R) ^ 2) := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let k := (8 + Cw * Cg) * R ^ 2
  have hk : 0 ≤ k := by unfold k; positivity
  have hκ : ∀ s, ‖-fibreSeriesC lam ξ s‖ ≤ k := by
    intro s
    rw [norm_neg]
    exact (fibreGraph_symbol_quadratic_bound hgraph hη0 hη hCg hCw hG hv hw ξ hdisc s).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (fibreNorm_nonneg ξ) hξ 2) (by positivity))
  have hκm : AEStronglyMeasurable (fun s => -fibreSeriesC lam ξ s)
      (volume.restrict (Icc (t - 1) t)) :=
    ((CycleDamping.graph_symbol_aestronglyMeasurable hG hv hgraph ξ hdisc).neg).mono_measure
      Measure.restrict_le_self
  have he := fibreGraph_actual_weak_evolution hgraph hη0 hη hCw hG hv hm hw V hb ξ hdisc
    (by linarith : t - 1 ≤ t)
  have hn : ‖cellRawTrace (fibreSeriesJet r ξ) (t - 1) + cellConstantCLM 1‖ ≤ 1 + Cg * R :=
    (fibreGraph_normalized_mode_norm_le hgraph hCg ξ hdisc (t - 1)).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hξ hCg))
  have ht : (∑ i : Fin 2, ‖(Real.sqrt η : ℂ) * ξ i‖ ^ 2) ≤ 2 * R ^ 2 := by
    simp only [Fin.sum_univ_two]
    exact (add_le_add (pow_le_pow_left₀ (norm_nonneg _) (hθ 0) 2)
      (pow_le_pow_left₀ (norm_nonneg _) (hθ 1) 2)).trans_eq (by ring)
  have hA : cellFullZerothGrowth η Cw ξ k ≤ constructedAllOrderPrice 0 R k Cw := by
    have hf := mul_le_mul_of_nonneg_left hξ hCw
    unfold cellFullZerothGrowth constructedAllOrderPrice
    linarith only [ht, hf]
  have hall := interiorPulseActualWeak_unit_window_all_native_orders hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ
    (fun s => -fibreSeriesC lam ξ s) k hκ
    (by linarith : t - 1 < t) hκm
    (cellRawTrace (fibreSeriesJet r ξ) (t - 1) + cellConstantCLM 1)
    (fun s => cellRawTrace (fibreSeriesJet r ξ) s + cellConstantCLM 1)
    (fun s => cellH1Slice (fibreSeriesJet r ξ) s + cellH1One) he rfl (by ring)
  intro J
  obtain ⟨W, hwv, hwb⟩ := hall J
  refine ⟨W, hwv, hwb.trans ?_⟩
  have hM := constructedNativeWindowPrice_pos J R k Cw hR hk hCw
  apply mul_le_mul_of_nonneg_left
  · exact mul_le_mul (Real.exp_le_exp.mpr hA)
      ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn) (sq_nonneg _) (Real.exp_pos _).le
  · change 0 ≤ (Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1) *
      constructedNativeWindowPrice J R k Cw) ^ J * peFactor η ^ (2 * J)
    exact mul_nonneg (pow_nonneg (by positivity) _)
      (pow_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans (one_le_peFactor η)) _)

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! A native periodic entrance gives a polynomially bounded native fast entrance. -/

theorem constructedCanonicalFast_native_entrance (J : ℕ)
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
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellSourceSlice ell t))
    ∃ W : TorusHk J ℂ, torusHkValueCLM W =
      torusHkValueCLM initial - cellScalarCLM c
        (cellRawTrace (fibreSeriesJet r ξ) t + cellConstantCLM 1) ∧
      ‖W‖ ≤ (1 + 4 * Real.sqrt (constructedGraphNativeSquareBudget J R
        (fibreCoefficientGraphBound Cw) Cw η)) * ‖initial‖ := by
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
  refine ⟨initial - torusHigherScalarCLM J
    (cellComplexPair (torusHkValueCLM initial)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellSourceSlice ell t))) Rj, ?_, ?_⟩
  · rw [torusHigher_normalized_projection_value, hRj]
  · exact torusHigher_normalized_projection_norm J initial Rj (cellSourceSlice ell t)
      4 (Real.sqrt B) hell hRb

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! One real price covers positive-time higher decay, zero-time projection, and order-zero decay. -/

def constructedAdjointHigherDecayPrice (J : ℕ) (R Cw : ℝ) : ℝ :=
  nativeSobolevWordPrice J * (Fintype.card (JetIndex2 J) : ℝ) *
    (Real.sqrt (constructedNativeGapBasePrice J R 0 Cw (6 * Real.pi ^ 2)) *
      (1 + 6 * Real.sqrt (constructedGraphNativeBaseSquareBudget J R
        (AVRegularity.CycleEvolution.fibreCoefficientGraphBound Cw) Cw)))

def constructedAdjointEntrancePrice (J : ℕ) (R Cw : ℝ) : ℝ :=
  nativeSobolevWordPrice J * (Fintype.card (JetIndex2 J) : ℝ) *
    (1 + 6 * Real.sqrt (constructedGraphNativeBaseSquareBudget J R
      (AVRegularity.CycleEvolution.fibreCoefficientGraphBound Cw) Cw))

def constructedAdjointZeroDecayPrice (R Cw : ℝ) : ℝ :=
  nativeSobolevWordPrice 0 * (26 * Real.sqrt (Real.exp (6 * Real.pi ^ 2) *
    constructedGapSmoothingBasePrice 0 R 0 Cw * Real.exp (constructedAllOrderPrice 0 R 0 Cw)))

def constructedAdjointDecayPrice (J : ℕ) (R Cw : ℝ) : ℝ :=
  max 1 (max (constructedAdjointHigherDecayPrice J R Cw)
    (max (constructedAdjointEntrancePrice J R Cw) (constructedAdjointZeroDecayPrice R Cw)))

theorem constructedAdjointHigherDecayPrice_le (J : ℕ) (R Cw : ℝ) :
    constructedAdjointHigherDecayPrice J R Cw ≤ constructedAdjointDecayPrice J R Cw :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem constructedAdjointEntrancePrice_le (J : ℕ) (R Cw : ℝ) :
    constructedAdjointEntrancePrice J R Cw ≤ constructedAdjointDecayPrice J R Cw :=
  (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))

theorem constructedAdjointZeroDecayPrice_le (J : ℕ) (R Cw : ℝ) :
    constructedAdjointZeroDecayPrice R Cw ≤ constructedAdjointDecayPrice J R Cw :=
  (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))

theorem constructedAdjointEntrance_native_price (J : ℕ) (R Cw η : ℝ) :
    1 + 6 * Real.sqrt (constructedGraphNativeSquareBudget J R
      (AVRegularity.CycleEvolution.fibreCoefficientGraphBound Cw) Cw η) ≤
      (1 + 6 * Real.sqrt (constructedGraphNativeBaseSquareBudget J R
        (AVRegularity.CycleEvolution.fibreCoefficientGraphBound Cw) Cw)) * peFactor η ^ (2 * J) := by
  apply (constructedAdjointFastNativeEntrance_polynomial_price J R
    (AVRegularity.CycleEvolution.fibreCoefficientGraphBound Cw) Cw η).trans
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (one_le_peFactor η) (by omega)) (by positivity)

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
open scoped NNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! Polynomial native smoothing for the actual full finite equation, with its zeroth bound discharged. -/

theorem constructedFibreGraph_native_frequency_smooth
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
    have hall := constructedFibreGraph_uniform_native_orders hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R
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

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! One order-dependent real price covers graph, row, decay and smoothing with Pe^(2j). -/

def constructedGraphJetPrice (J : ℕ) (R Cw ρ : ℝ) : ℝ :=
  nativeSobolevWordPrice J *
    (64 * (Real.sqrt (constructedGraphNativeBaseSquareBudget J R
      (fibreCoefficientGraphBound Cw) Cw) + ‖torusHigherConstant J 1‖) / ρ)

def constructedRowJetPrice (J : ℕ) (R Cw ρ : ℝ) : ℝ :=
  nativeSobolevWordPrice J *
    (2 * (64 * (Real.sqrt (constructedGraphNativeBaseSquareBudget J R
      (fibreCoefficientGraphBound Cw) Cw) + ‖torusHigherConstant J 1‖) / ρ) +
      (2 / fibreCoefficientMajorantRadius Cw) * ‖torusHigherConstant J 1‖)

def constructedScalarJetPrice (J : ℕ) (R Cw ρ : ℝ) : ℝ :=
  max 1 (max (constructedForwardDecayPrice J R Cw)
    (max (constructedAdjointDecayPrice J R Cw)
      (max (constructedSmoothingPrice J R Cw)
        (max (constructedGraphJetPrice J R Cw ρ) (constructedRowJetPrice J R Cw ρ)))))

theorem constructedScalarJetPrice_pos (J : ℕ) (R Cw ρ : ℝ) :
    0 < constructedScalarJetPrice J R Cw ρ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)

theorem constructedForwardDecayPrice_le_scalar (J : ℕ) (R Cw ρ : ℝ) :
    constructedForwardDecayPrice J R Cw ≤ constructedScalarJetPrice J R Cw ρ :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem constructedAdjointDecayPrice_le_scalar (J : ℕ) (R Cw ρ : ℝ) :
    constructedAdjointDecayPrice J R Cw ≤ constructedScalarJetPrice J R Cw ρ :=
  (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))

theorem constructedSmoothingPrice_le_scalar (J : ℕ) (R Cw ρ : ℝ) :
    constructedSmoothingPrice J R Cw ≤ constructedScalarJetPrice J R Cw ρ :=
  (le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _)))

theorem constructedGraphJetPrice_le_scalar (J : ℕ) (R Cw ρ : ℝ) :
    constructedGraphJetPrice J R Cw ρ ≤ constructedScalarJetPrice J R Cw ρ :=
  (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))))

theorem constructedRowJetPrice_le_scalar (J : ℕ) (R Cw ρ : ℝ) :
    constructedRowJetPrice J R Cw ρ ≤ constructedScalarJetPrice J R Cw ρ :=
  (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))))

theorem polynomial_frequency_price_absorb (J : ℕ) (η δ C C' : ℝ)
    (hδ : 0 ≤ δ) (hCC : C ≤ C') (hC' : 0 ≤ C') :
    C * peFactor η ^ J * δ ≤ C' * peFactor η ^ (2 * J) * δ := by
  apply mul_le_mul_of_nonneg_right _ hδ
  have hp0 : 0 ≤ peFactor η ^ J := pow_nonneg
    ((by norm_num : (0 : ℝ) ≤ 1).trans (one_le_peFactor η)) J
  exact (mul_le_mul_of_nonneg_right hCC hp0).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one_le_peFactor η) (by omega)) hC')

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
open scoped NNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! Polynomial native smoothing for the actual full finite equation, with its zeroth bound discharged. -/

theorem constructedFibreGraph_native_linear_gain
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
    (hband : fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ)) < ξ₀) (t : ℝ) (J : ℕ)
    (ξ : Fin 2 → ℂ) (hξ : ξ ∈ Metric.ball 0 ((ρ : ℝ) / 2)) :
    ∃ U : TorusHk J ℂ, torusHkValueCLM U = cellRawTrace (fibreSeriesJet r ξ) t ∧
      ‖U‖ ≤ (64 * (Real.sqrt (constructedGraphNativeSquareBudget J
        (fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ))) Cg Cw
        (ν / ocMeanFlux α q Λ ζ m ν)) + ‖torusHigherConstant J 1‖) / (ρ : ℝ)) * fibreNorm ξ := by
  obtain ⟨F, hF, _, hz⟩ := constructedFibreGraph_native_frequency_smooth hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw hη0 hη hm ξ₀ Cg hCg r lam hgraph ρ hρ hband t J
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

theorem constructedFibreGraph_exists_smooth_rep
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
    (hgraph : IsFibreGraph (ν / ocMeanFlux α q Λ ζ m ν) G
      (ocCellDrift α q Λ ζ m ν y₀) ξ₀ Cg r lam)
    (hdisc : fibreNorm ξ < ξ₀) (t : ℝ) :
    ∃ f : Vec 2 → ℂ, ContDiff ℝ (⊤ : ℕ∞) f ∧ AVenhance.IsZ2Periodic f ∧
      f =ᵐ[volume.restrict AVenhance.unitCube] cellValue (fibreSeriesJet r ξ) t := by
  have hall := constructedFibreGraph_uniform_native_orders hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R hR hξ hθ hη0 hη hm ξ₀ Cg hCg r lam hgraph hdisc t
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
open Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Absorption of the graph and row native prices into the common scalar price. -/

theorem constructedGraphJetPrice_bound (J : ℕ) (R Cw ρ η δ : ℝ)
    (hδ : 0 ≤ δ) :
    (∑ b ∈ Finset.range (J + 1), (Fintype.card (DerivativeWord2 b) : ℝ≥0∞)) *
      ENNReal.ofReal ((64 * (Real.sqrt (constructedGraphNativeBaseSquareBudget J R
        (fibreCoefficientGraphBound Cw) Cw) + ‖torusHigherConstant J 1‖) / ρ) *
        peFactor η ^ J * δ) ≤
      ENNReal.ofReal (constructedScalarJetPrice J R Cw ρ * peFactor η ^ (2 * J) * δ) := by
  rw [nativeSobolevWordPrice_mul_ofReal]
  apply ENNReal.ofReal_le_ofReal
  rw [← mul_assoc, ← mul_assoc]
  exact polynomial_frequency_price_absorb J η δ _ _ hδ
    (constructedGraphJetPrice_le_scalar J R Cw ρ)
    (constructedScalarJetPrice_pos J R Cw ρ).le

theorem constructedRowJetPrice_bound (J : ℕ) (R Cw ρ η δ : ℝ)
    (hδ : 0 ≤ δ) :
    (∑ b ∈ Finset.range (J + 1), (Fintype.card (DerivativeWord2 b) : ℝ≥0∞)) *
      ENNReal.ofReal ((2 * (64 * (Real.sqrt (constructedGraphNativeBaseSquareBudget J R
        (fibreCoefficientGraphBound Cw) Cw) + ‖torusHigherConstant J 1‖) / ρ) +
        (2 / fibreCoefficientMajorantRadius Cw) * ‖torusHigherConstant J 1‖) *
        peFactor η ^ J * δ) ≤
      ENNReal.ofReal (constructedScalarJetPrice J R Cw ρ * peFactor η ^ (2 * J) * δ) := by
  rw [nativeSobolevWordPrice_mul_ofReal]
  apply ENNReal.ofReal_le_ofReal
  rw [← mul_assoc, ← mul_assoc]
  exact polynomial_frequency_price_absorb J η δ _ _ hδ
    (constructedRowJetPrice_le_scalar J R Cw ρ)
    (constructedScalarJetPrice_pos J R Cw ρ).le

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
open scoped ENNReal NNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! Polynomial native smoothing for the actual full finite equation, with its zeroth bound discharged. -/

theorem constructedFibreGraph_smooth_cellSobolev_bound
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
    (hband : fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ)) < ξ₀) (t : ℝ) (J : ℕ)
    (ξ : Fin 2 → ℂ) (hξ : ξ ∈ Metric.ball 0 ((ρ : ℝ) / 2))
    (f : Vec 2 → ℂ) (hf : ContDiff ℝ (J : ℕ∞) f)
    (he : f =ᵐ[volume.restrict AVenhance.unitCube] cellValue (fibreSeriesJet r ξ) t) :
    cellSobolevNorm J f ≤
      (∑ b ∈ Finset.range (J + 1), (Fintype.card (DerivativeWord2 b) : ℝ≥0∞)) *
      ENNReal.ofReal ((64 * (Real.sqrt (constructedGraphNativeBaseSquareBudget J
        (fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ))) Cg Cw) + ‖torusHigherConstant J 1‖) / (ρ : ℝ)) *
        peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ J * fibreNorm ξ) := by
  obtain ⟨U, hv, hbU⟩ := constructedFibreGraph_native_linear_gain hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw hη0 hη hm ξ₀ Cg hCg r lam hgraph ρ hρ hband t J ξ hξ
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
namespace AVRegularity.CycleWords

/-! Uniform native orders for the actual reversed full graph. -/

theorem interiorPulseReflectedFibreGraph_uniform_native_orders
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
    ∀ J : ℕ, ∃ W : TorusHk J ℂ,
      torusHkValueCLM W = cellRawTrace (fibreSeriesJet r ξ) t + cellConstantCLM 1 ∧
      ‖W‖ ^ 2 ≤
        (Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1) *
          constructedNativeWindowPrice J R ((8 + Cw * Cg) * R ^ 2) Cw) ^ J *
        peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ (2 * J) *
        (Real.exp (constructedAllOrderPrice 0 R ((8 + Cw * Cg) * R ^ 2) Cw) * (1 + Cg * R) ^ 2) := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let vref := fun s x => -interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x
  have hvref : IsCellDrift vref := cellDrift_timeReverse hv
  have hGref := cellMetric_timeReverse hG
  have hbref : ∀ s x, ∑ j, vref s x j ^ 2 ≤ V ^ 2 := by
    intro s x
    simpa only [vref, Pi.neg_apply, neg_sq] using hb (-s) x
  have hwref : ∀ s x, Real.sqrt η * Real.sqrt (∑ i, vref s x i ^ 2) ≤ Cw := by
    intro s x
    simpa only [vref, Pi.neg_apply, neg_sq, η] using hw (-s) x
  have hmref : ∀ s (j : Fin 2), cellMean (fun x => (vref s x j : ℂ)) = 0 := by
    intro s j
    dsimp only [vref, Pi.neg_apply]
    simp only [Complex.ofReal_neg, cellMean, integral_neg]
    change -cellMean (fun x => (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot (-s) x j : ℂ)) = 0
    rw [hm, neg_zero]
  let k := (8 + Cw * Cg) * R ^ 2
  have hk : 0 ≤ k := by unfold k; positivity
  have hκ : ∀ s, ‖-fibreSeriesC lam ξ s‖ ≤ k := by
    intro s
    rw [norm_neg]
    exact (fibreGraph_symbol_quadratic_bound hgraph hη0 hη hCg hCw hGref hvref hwref ξ hdisc s).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (fibreNorm_nonneg ξ) hξ 2) (by positivity))
  have hκm : AEStronglyMeasurable (fun s => -fibreSeriesC lam ξ s)
      (volume.restrict (Icc (t - 1) t)) :=
    ((CycleDamping.graph_symbol_aestronglyMeasurable hGref hvref hgraph ξ hdisc).neg).mono_measure
      Measure.restrict_le_self
  have he := fibreGraph_actual_weak_evolution hgraph hη0 hη hCw hGref hvref hmref hwref V hbref ξ hdisc
    (by linarith : t - 1 ≤ t)
  have hn : ‖cellRawTrace (fibreSeriesJet r ξ) (t - 1) + cellConstantCLM 1‖ ≤ 1 + Cg * R :=
    (fibreGraph_normalized_mode_norm_le hgraph hCg ξ hdisc (t - 1)).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hξ hCg))
  have ht : (∑ i : Fin 2, ‖(Real.sqrt η : ℂ) * ξ i‖ ^ 2) ≤ 2 * R ^ 2 := by
    simp only [Fin.sum_univ_two]
    exact (add_le_add (pow_le_pow_left₀ (norm_nonneg _) (hθ 0) 2)
      (pow_le_pow_left₀ (norm_nonneg _) (hθ 1) 2)).trans_eq (by ring)
  have hA : cellFullZerothGrowth η Cw ξ k ≤ constructedAllOrderPrice 0 R k Cw := by
    have hf := mul_le_mul_of_nonneg_left hξ hCw
    unfold cellFullZerothGrowth constructedAllOrderPrice
    linarith only [ht, hf]
  have hall := interiorPulseReflectedActualWeak_unit_window_all_native_orders hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw hw ξ R hR hξ hθ
    (fun s => -fibreSeriesC lam ξ s) k hκ
    (by linarith : t - 1 < t) hκm
    (cellRawTrace (fibreSeriesJet r ξ) (t - 1) + cellConstantCLM 1)
    (fun s => cellRawTrace (fibreSeriesJet r ξ) s + cellConstantCLM 1)
    (fun s => cellH1Slice (fibreSeriesJet r ξ) s + cellH1One) he rfl (by ring)
  intro J
  obtain ⟨W, hwv, hwb⟩ := hall J
  refine ⟨W, hwv, hwb.trans ?_⟩
  have hM := constructedNativeWindowPrice_pos J R k Cw hR hk hCw
  apply mul_le_mul_of_nonneg_left
  · exact mul_le_mul (Real.exp_le_exp.mpr hA)
      ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn) (sq_nonneg _) (Real.exp_pos _).le
  · change 0 ≤ (Real.exp 1 * (2 * Real.exp 1) * ((J : ℝ) + 1) *
      constructedNativeWindowPrice J R k Cw) ^ J * peFactor η ^ (2 * J)
    exact mul_nonneg (pow_nonneg (by positivity) _)
      (pow_nonneg ((by norm_num : (0 : ℝ) ≤ 1).trans (one_le_peFactor η)) _)

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
open scoped NNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! Polynomial native smoothing for the actual full finite equation, with its zeroth bound discharged. -/

theorem constructedReflectedFibreGraph_native_frequency_smooth
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
    have hall := constructedReflectedFibreGraph_uniform_native_orders hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ R
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

theorem constructedFibreGraph_coefficient_smooth_rep
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
    obtain ⟨F, hF, hs, _⟩ := constructedFibreGraph_native_frequency_smooth hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw hη0 hη hm ξ₀ Cg hCg r lam hgraph ρ hρ hband t J
    refine ⟨F, ?_, hs.contDiffAt (Metric.ball_mem_nhds (0 : Fin 2 → ℂ) (show (0 : ℝ) < ρ from hρ))⟩
    intro ξ hξ
    have hn : ‖ξ‖ ≤ ρ := le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hξ)
    have hd := (fibreNorm_le_constant_of_norm_le ξ ρ.coe_nonneg hn).trans_lt hband
    exact (hF ξ hξ).1.trans (fibreGraphTrace_eq_nativeSeries hgraph ρ hρ hband ξ hd hn t)
  obtain ⟨f, hf, hp, he⟩ := torusHigher_taylor_coefficients_smooth_representatives c ρ hρ hsum hex p
  exact ⟨f, hf, hp, he.trans (fibreGraphCoefficientClass_ae hgraph ρ hρ hband p t)⟩

/-! Polynomial native smoothing for the actual full finite equation, with its zeroth bound discharged. -/

theorem constructedReflectedFibreGraph_native_linear_gain
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
    (hband : fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ)) < ξ₀) (t : ℝ) (J : ℕ)
    (ξ : Fin 2 → ℂ) (hξ : ξ ∈ Metric.ball 0 ((ρ : ℝ) / 2)) :
    ∃ U : TorusHk J ℂ, torusHkValueCLM U = cellRawTrace (fibreSeriesJet r ξ) t ∧
      ‖U‖ ≤ (64 * (Real.sqrt (constructedReflectedGraphNativeSquareBudget J
        (fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ))) Cg Cw
        (ν / ocMeanFlux α q Λ ζ m ν)) + ‖torusHigherConstant J 1‖) / (ρ : ℝ)) * fibreNorm ξ := by
  obtain ⟨F, hF, _, hz⟩ := constructedReflectedFibreGraph_native_frequency_smooth hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw hη0 hη hm ξ₀ Cg hCg r lam hgraph ρ hρ hband t J
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
