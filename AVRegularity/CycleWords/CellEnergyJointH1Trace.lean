-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.ConstructedCoreRawContraction
import AVRegularity.Weighted.ScalarChainClippedFactorialENNReal
import AVRegularity.CycleEvolution.CellInverseJetFactorialBound
import AVRegularity.CycleEvolution.CellLimitMoments
import AVRegularity.CycleDamping.ReferenceSourceMode
import AVRegularity.CycleWords.CellComplexH1Separability
import AVRegularity.CycleWords.PlaneScalarBlochSurjective
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CycleComparison.Lift AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Higher constant-metric Bloch diffusion has the original finite-coordinate Gårding estimate. -/

theorem finiteEnergyOrder_le_smooth (n : ℕ) :
    (n : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞) := WithTop.coe_le_coe.mpr le_top

 def finiteSmoothHigherGradientEnergy (K : ℕ) (f : Vec 2 → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f) : ℝ :=
  ∑ a : JetIndex2 K, ∑ i : Fin 2,
    ‖cellDerivativeCLM i (cellH2BaseCLM
      (finiteSmoothPeriodicHk 2 (orderedDerivative a.2 f)
        (orderedDerivative_contDiff a.2 2 f (hf.of_le (finiteEnergyOrder_le_smooth _)))
        (orderedDerivative_periodic a.2 f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp)))‖ ^ 2

 theorem finiteSmoothHigherGradientEnergy_nonneg (K : ℕ) (f : Vec 2 → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f) :
    0 ≤ finiteSmoothHigherGradientEnergy K f hf hp :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

 theorem finiteSmoothHigherDiffusion_energy (K : ℕ) (f : Vec 2 → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (t : ℝ) :
    2 * inner ℝ
        (torusHigherStrongDiffusionCLM K G θ t (finiteSmoothPeriodicHk (K + 2) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp))
        (finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp) +
      (3 / 4) * finiteSmoothHigherGradientEnergy K f hf hp ≤
      (264 * (∑ i : Fin 2, ‖θ i‖ ^ 2)) * ‖finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp‖ ^ 2 := by
  let C : CellCoefficients := ⟨fun t _ => G t, 0, θ, 0⟩
  have hcoord (a : JetIndex2 K) :
      2 * inner ℝ
          ((torusHigherStrongDiffusionCLM K G θ t
            (finiteSmoothPeriodicHk (K + 2) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp)).val a)
          ((finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp).val a) +
        (3 / 4) * (∑ i : Fin 2, ‖cellDerivativeCLM i (cellH2BaseCLM
          (finiteSmoothPeriodicHk 2 (orderedDerivative a.2 f)
            (orderedDerivative_contDiff a.2 2 f (hf.of_le (finiteEnergyOrder_le_smooth _)))
            (orderedDerivative_periodic a.2 f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp)))‖ ^ 2) ≤
        (264 * (∑ i : Fin 2, ‖θ i‖ ^ 2)) *
          ‖(finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp).val a‖ ^ 2 := by
    let u := finiteSmoothPeriodicHk 2 (orderedDerivative a.2 f)
      (orderedDerivative_contDiff a.2 2 f (hf.of_le (finiteEnergyOrder_le_smooth _)))
      (orderedDerivative_periodic a.2 f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp)
    have he := congrArg Complex.re (cellConstantMetricStrongDiffusionCLM_pair G hG θ t u (cellH2BaseCLM u))
    rw [cellComplexDiffusionForm_real_part C hG, cellComplexPair_re] at he
    have hd := cellDiffusionForm_sharp_garding C hG t (cellH2BaseCLM u)
    rw [he] at hd
    rw [finiteSmoothDiffusion_jet_coordinate (hf := hf), finiteSmoothValue_jet_coordinate (hf := hf)]
    exact hd
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (JetIndex2 K))) (fun a _ => hcoord a)
  have hn : ‖finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp‖ ^ 2 =
      ∑ a : JetIndex2 K, ‖(finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp).val a‖ ^ 2 :=
    PiLp.norm_sq_eq_of_L2 _ _
  rw [torusHigher_inner_eq_sum, hn]
  simpa only [finiteSmoothHigherGradientEnergy, Finset.sum_add_distrib, ← Finset.mul_sum] using hs

 theorem finiteSmoothHigherGradientEnergy_native_identity (K : ℕ) (f : Vec 2 → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f) :
    ‖finiteSmoothPeriodicHk (K + 1) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp‖ ^ 2 =
      ‖torusHkValueCLM (finiteSmoothPeriodicHk (K + 1) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp)‖ ^ 2 +
        finiteSmoothHigherGradientEnergy K f hf hp := by
  have h := torusHigher_norm_sq_eq_value_gradient K
    (finiteSmoothPeriodicHk (K + 1) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp)
  simp_rw [finiteSmoothPeriodicHk_ordered_truncated_H1 (hf := hf)] at h
  unfold finiteSmoothHigherGradientEnergy
  rw [Fintype.sum_sigma]
  exact h

 theorem finiteSmoothHigher_adjacent_energy_le (K : ℕ) (f : Vec 2 → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f) :
    ‖finiteSmoothPeriodicHk (K + 1) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp‖ ^ 2 ≤
      ‖finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp‖ ^ 2 +
        finiteSmoothHigherGradientEnergy K f hf hp := by
  have he := congrArg (torusHkValueCLM (E := ℂ) (K := K))
    (finiteSmoothPeriodicHk_truncate (K := K) (L := K + 1) (by omega) f hf hp)
  have hb : ‖torusHkValueCLM (finiteSmoothPeriodicHk (K + 1) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp)‖ ≤
      ‖finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp‖ := by
    change torusHkValueCLM (finiteSmoothPeriodicHk (K + 1) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp) =
      torusHkValueCLM (finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp) at he
    exact (congrArg norm he).le.trans (PiLp.norm_apply_le (finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp).val (valueIndex2 K))
  rw [finiteSmoothHigherGradientEnergy_native_identity K f hf hp]
  exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) hb 2) le_rfl

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The literal transverse diffusion and window multiplier define an actual finite Fourier generator. -/

variable (N : ℕ) (a b η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
  {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (ξ : Fin 2 → ℂ)
  (hc : ∀ t ∈ Icc a b, ContDiff ℝ (0 : ℕ) (v t))
  (A : Fin 1 → ℝ) (hA : ∀ l, 0 ≤ A l)
  (hb : ∀ t ∈ Icc a b, ∀ l x,
    ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)
  (κ : ℝ → ℂ)

theorem cellTransverseGalerkinOperator_higher_value
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (q : ℕ) (hcq : ∀ t ∈ Icc a b, ContDiff ℝ (q : ℕ) (v t))
    (Aq : Fin (q + 1) → ℝ) (hAq : ∀ l, 0 ≤ Aq l)
    (hbq : ∀ t ∈ Icc a b, ∀ l x,
      ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ Aq l)
    (t : ℝ) (ht : t ∈ Icc a b) (u : CellGalerkinSpace (E := ℂ) N) :
    cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb κ t u =
      cellGalerkinL2Initial N (torusHkValueCLM
        (torusHigherTransverseWindowSource q a b η G hv ξ hcq Aq hAq hbq κ t
          (rangeSmoothFourierLiftCLM (by omega : 1 ≤ q + 2) N u))) := by
  have hlow := torusHigherTransverseWindowSource_value 0 a b η G hv ξ hc A hA hb κ
    Cw hCw hw t ht (cellGalerkinHigherStateCLM N 1 u)
  have hhigh := torusHigherTransverseWindowSource_value q a b η G hv ξ hcq Aq hAq hbq κ
    Cw hCw hw t ht (rangeSmoothFourierLiftCLM (by omega : 1 ≤ q + 2) N u)
  have htr : truncateTorusHk (by omega : 2 ≤ q + 2)
      (rangeSmoothFourierLiftCLM (by omega : 1 ≤ q + 2) N u) = cellGalerkinHigherStateCLM N 1 u :=
    cellGalerkinRangeHigher_truncate (by omega) (by omega) (by omega) N u
  have hltr : truncateTorusHk (by omega : 2 ≤ 0 + 2) (cellGalerkinHigherStateCLM N 1 u) =
      cellGalerkinHigherStateCLM N 1 u := by
    apply TorusHk.ext_value
    rfl
  rw [htr] at hhigh
  rw [hltr] at hlow
  simp only [cellTransverseGalerkinOperator, ContinuousLinearMap.comp_apply,
    torusHigherTransverseWindowSourceCLM_apply, cellGalerkinL2InitialCLM_apply]
  exact congrArg (cellGalerkinL2Initial N) (hlow.trans hhigh.symm)

end AVRegularity.CycleWords
end
end

section
public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CycleDamping
namespace AVRegularity.CycleWords

/-! One orientation contracts every marked complete core, for real complex frequencies. -/

theorem constructed_core_complex_marks_contraction_time (ξlo : ℝ) (hlo : 0 < ξlo) :
    ∃ d : ℝ, 0 < d ∧ ∀ (α q : ℝ) (Λ m : ℕ) (ζ : ℝ → ℝ),
      1 ≤ Λ → IsFastProfile ζ → ∀ ν : ℝ, 0 < ν →
      6 ≤ ocMu q Λ m ν * ocTau α q Λ m →
      ∀ (y₀ : Vec 2) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
        (_hG : IsCellMetric (fun t _ => G t))
        (_hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀)) (V : ℝ)
        (_hb : ∀ t x, ∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2 ≤ V ^ 2)
        (ξ : Fin 2 → ℂ),
      (∀ i, (ξ i).im = 0 ∧ |(ξ i).re| ≤ Real.pi / Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν)) →
      ξlo ≤ fibreNorm ξ →
      ∃ j : Fin 2,
      ∀ (a b : ℝ), a ≤ b → d ≤ b - a →
      ∀ (l n : ℤ), IsOCCompleteCore α q Λ m l n →
      n % 4 = (if j = 0 then 3 else 1) →
      (∀ t ∈ Icc a b, ocEll q Λ m ν ^ 2 * t ∈
        Icc (((n : ℝ) - 1 / 3) * ocTau α q Λ m) (((n : ℝ) + 1 / 3) * ocTau α q Λ m)) →
      ∀ D : ℝ → RawJet2 1 ℂ,
        IsCellSolution (Icc a b)
          (fibreCoefficients (ν / ocMeanFlux α q Λ ζ m ν) G
            (ocCellDrift α q Λ ζ m ν y₀) ξ (fun _ => 0))
          (fun _ _ => 0) (fun _ _ => 0) D →
        cellL2Norm (cellValue D b) ≤ ENNReal.ofReal (1 / 2) * cellL2Norm (cellValue D a) := by
  obtain ⟨d, hd, hdrop⟩ := constructed_core_raw_contraction_time ξlo hlo
  refine ⟨d, hd, ?_⟩
  intro α q Λ m ζ hΛ hζ ν hν hr y₀ G hG hv V hb ξ hξ hnorm
  have hreal : ∀ i, (ξ i).im = 0 := fun i => (hξ i).1
  have heq := real_frequency_eq ξ hreal
  have hn : ξlo ≤ Real.sqrt (∑ i : Fin 2, (ξ i).re ^ 2) := by
    have hn' := hnorm
    rw [heq] at hn'
    simpa only [fibreNorm, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hn'
  obtain ⟨j, hj⟩ : ∃ j : Fin 2, ξlo / 2 ≤ |(ξ j).re| := by
    rcases real_frequency_large_coordinate (fun i => (ξ i).re) ξlo hlo hn with h0 | h1
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
  refine ⟨j, ?_⟩
  intro a b hab hlong l n hcore horient hinside D hD
  have hB := CycleReference.meanFlux_ge_input (α := α) (q := q) (m := m) hΛ hζ hν
  have hη : 0 < ν / ocMeanFlux α q Λ ζ m ν := div_pos hν (hν.trans_le hB)
  rw [heq] at hD
  exact hdrop α q Λ m ζ hΛ hζ ν hν hr y₀ G hG hv V hb (fun i => (ξ i).re)
    (scaled_real_brillouin _ hη _ (fun i => (hξ i).2)) hn j hj a b hab hlong
    l n hcore horient hinside D hD

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The literal transverse diffusion and window multiplier define an actual finite Fourier generator. -/

variable (N : ℕ) (a b η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
  {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (ξ : Fin 2 → ℂ)
  (hc : ∀ t ∈ Icc a b, ContDiff ℝ (0 : ℕ) (v t))
  (A : Fin 1 → ℝ) (hA : ∀ l, 0 ≤ A l)
  (hb : ∀ t ∈ Icc a b, ∀ l x,
    ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)
  (κ : ℝ → ℂ)

theorem cellTransverseGalerkinOperator_uniform_bound
    (hG : IsCellMetric (fun t _ => G t)) (k : ℝ) (hκ : ∀ t, ‖κ t‖ ≤ k) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t,
      ‖cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb κ t‖ ≤ M := by
  obtain ⟨D, hD, hd⟩ := torusHigherTransverseWindowSourceCLM_uniform_bound
    0 a b η G hv ξ hc A hA hb κ hG k hκ
  let H := cellGalerkinHigherStateCLM N 1
  let V := torusHkValueCLM (E := ℂ) (K := 0)
  let P := cellGalerkinL2InitialCLM N
  refine ⟨‖P‖ * (‖V‖ * (D * ‖H‖)), by positivity, ?_⟩
  intro t
  have hSH : ‖(torusHigherTransverseWindowSourceCLM 0 a b η G hv ξ hc A hA hb κ t).comp H‖ ≤ D * ‖H‖ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hd t) (norm_nonneg _))
  have hVSH : ‖V.comp ((torusHigherTransverseWindowSourceCLM 0 a b η G hv ξ hc A hA hb κ t).comp H)‖ ≤
      ‖V‖ * (D * ‖H‖) := (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left hSH (norm_nonneg _))
  exact (ContinuousLinearMap.opNorm_comp_le P _).trans
    (mul_le_mul_of_nonneg_left hVSH (norm_nonneg _))

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Single-pulse transport consumes one native spatial reserve at the original price. -/

 theorem interiorPulseHigherAdvectionCLM_adjacent_polynomial_bound (K : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) {k : ℤ} (hk : Odd k) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ k))
    (θ : Fin 2 → ℂ) (R : ℝ) (hθ : ∀ i, ‖θ i‖ ≤ R)
    (t : ℝ) (U : TorusHk (K + 2) ℂ) :
    ‖interiorPulseHigherAdvectionCLM K hΛ hζ ν y₀ hk hv θ t U‖ ≤
      (constructedAdvectionAdjacentPrice K R * peFactor (ν / ocMeanFlux α q Λ ζ m ν)) *
        ‖truncateTorusHk (by omega : K + 1 ≤ K + 2) U‖ := by
  have hp : 0 ≤ constructedEntryUniversalNativePrice K * peFactor (ν / ocMeanFlux α q Λ ζ m ν) :=
    mul_nonneg (constructedEntryUniversalNativePrice_nonneg K) (by unfold peFactor; positivity)
  have hi (i : Fin 2) :
      ‖interiorPulseDriftEntryNativeCLM K hΛ hζ ν y₀ hk hv i t (torusHigherShiftedFirstCLM K θ i U)‖ ≤
      (constructedEntryUniversalNativePrice K * peFactor (ν / ocMeanFlux α q Λ ζ m ν)) *
        ((1 + R * (1 + ‖torusHigherScalarCLM K Complex.I‖)) *
          ‖truncateTorusHk (by omega : K + 1 ≤ K + 2) U‖) :=
    (interiorPulseDriftEntryNativeCLM_polynomial_bound K hΛ hζ hν hr y₀ hk hv i t _).trans
      (mul_le_mul_of_nonneg_left (torusHigherShiftedFirstCLM_adjacent_bound K θ R hθ i U) hp)
  simp only [interiorPulseHigherAdvectionCLM, Fin.sum_univ_two, add_apply, ContinuousLinearMap.comp_apply]
  exact ((norm_add_le _ _).trans (add_le_add (hi 0) (hi 1))).trans_eq
    (by unfold constructedAdvectionAdjacentPrice; ring)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The literal transverse diffusion and window multiplier define an actual finite Fourier generator. -/

theorem cellTransverseGalerkin_existsUnique {a b η : ℝ} (hab : a ≤ b)
    (N : ℕ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (ξ : Fin 2 → ℂ)
    (hc : ∀ t ∈ Icc a b, ContDiff ℝ (0 : ℕ) (v t))
    (A : Fin 1 → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ t ∈ Icc a b, ∀ l x,
      ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)
    (κ : ℝ → ℂ) (hκm : MemLp κ ⊤ (volume.restrict (Icc a b)))
    (k : ℝ) (hκ : ∀ t, ‖κ t‖ ≤ k) (u₀ : ComplexCellL2) :
    ∃! y : ContinuousMap (Icc a b) (CellGalerkinSpace (E := ℂ) N),
      AVenhance.Infra.ODE.IsLinearIntegralSolution
        ((Icc a b).indicator (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb κ))
        0 (cellGalerkinL2Initial N u₀) a b (AVenhance.Infra.ODE.extendCurve hab y) ∧
      AbsolutelyContinuousOnInterval (AVenhance.Infra.ODE.extendCurve hab y) a b := by
  obtain ⟨M, hM, hm⟩ := cellTransverseGalerkinOperator_uniform_bound N a b η G hv ξ hc A hA hb κ hG k hκ
  have hmeas : AEStronglyMeasurable ((Icc a b).indicator
      (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb κ)) volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_Icc).mpr
      (cellTransverseGalerkinOperator_aestronglyMeasurable N a b η G hv ξ hc A hA hb κ hG hκm)
  let D : AVenhance.Infra.ODE.LinearODEData (E := CellGalerkinSpace (E := ℂ) N) a b hab :=
    { A := (Icc a b).indicator (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb κ)
      f := 0
      y₀ := cellGalerkinL2Initial N u₀
      operatorBound := M
      operatorBound_nonneg := hM
      operator_aestronglyMeasurable := hmeas
      operator_norm_le := fun t => by
        by_cases ht : t ∈ Icc a b
        · rw [Set.indicator_of_mem ht]
          exact hm t
        · rw [Set.indicator_of_notMem ht, norm_zero]
          exact hM
      forcing_intervalIntegrable := intervalIntegrable_const }
  exact AVenhance.Infra.ODE.LinearODEData.existsUnique_absolutelyContinuous_integralSolution D

/-! Testing the finite generator against any retained mode gives the genuine diffusion pairing. -/

theorem cellTransverseGalerkinOperator_test_pairing
    (N : ℕ) (a b η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v) (ξ : Fin 2 → ℂ)
    (hc : ∀ t ∈ Icc a b, ContDiff ℝ (0 : ℕ) (v t))
    (A : Fin 1 → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ t ∈ Icc a b, ∀ l x,
      ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)
    (κ : ℝ → ℂ) (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (t : ℝ) (ht : t ∈ Icc a b) (u z : CellGalerkinSpace (E := ℂ) N) :
    inner ℝ (cellGalerkinValue N (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb κ t u))
      (cellGalerkinValue N z) =
    inner ℝ (cellDualDerivative ⟨fun t _ => G t, 0, fun j => (Real.sqrt η : ℂ) * ξ j, κ⟩
      hG 0 measurable_const (by intro t x; simp) t u.val
      (-cellScalarCLM Complex.I (cellFibreDriftCouplingCLM η Cw hCw hv hw ξ t (cellGalerkinValue N u))) 0)
      z.val := by
  let U := cellGalerkinHigherStateCLM N 1 u
  let src := -cellScalarCLM Complex.I
    (cellFibreDriftCouplingCLM η Cw hCw hv hw ξ t (cellGalerkinValue N u))
  have hbase : cellH2BaseCLM U = u.val := cellGalerkinHigherStateCLM_truncate N 1 u
  have hvalue : torusHkValueCLM U = cellGalerkinValue N u := cellGalerkinHigherStateCLM_value N 1 u
  have hs := torusHigherTransverseWindowSource_value 0 a b η G hv ξ hc A hA hb κ Cw hCw hw t ht U
  have htr : truncateTorusHk (by omega : 2 ≤ 0 + 2) U = U := by
    apply TorusHk.ext_value
    rfl
  have hd := cellZeroDrift_dual_strong_source G hG (fun j => (Real.sqrt η : ℂ) * ξ j) κ t U src
  have hfull : cellConstantMetricStrongDiffusionCLM G (fun j => (Real.sqrt η : ℂ) * ξ j) t U +
      cellScalarCLM (κ t) (torusHkValueCLM U) + src =
      cellTransverseStrongSource η Cw hCw G hv hw ξ κ t U := by
    dsimp only [cellTransverseStrongSource, src]
    rw [hvalue]
    abel
  have hdu : cellDualDerivative ⟨fun t _ => G t, 0, fun j => (Real.sqrt η : ℂ) * ξ j, κ⟩
      hG 0 measurable_const (by intro t x; simp) t u.val src 0 =
      cellPivotDualCLM (torusHkValueCLM (torusHigherTransverseWindowSource 0 a b η G hv ξ hc A hA hb κ t U)) := by
    rw [hbase] at hd
    exact hd.trans ((congrArg cellPivotDualCLM hfull).trans
      (congrArg cellPivotDualCLM (hs.trans (congrArg
        (cellTransverseStrongSource η Cw hCw G hv hw ξ κ t) htr)).symm))
  have hpair := congrArg (fun d : TorusHk 1 ℂ => inner ℝ d z.val) hdu
  have hadj := ContinuousLinearMap.adjoint_inner_left (torusHkValueCLM (E := ℂ) (K := 1)) z.val
    (torusHkValueCLM (torusHigherTransverseWindowSource 0 a b η G hv ξ hc A hA hb κ t U))
  exact (cellTransverseGalerkinOperator_pairing N a b η G hv ξ hc A hA hb κ t u z).trans
    (hadj.symm.trans hpair.symm)

/-! The literal transverse diffusion and window multiplier define an actual finite Fourier generator. -/

theorem cellTransverseGalerkin_window_operator_data {a b η : ℝ}
    (N : ℕ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (ξ : Fin 2 → ℂ)
    (hc : ∀ t ∈ Icc a b, ContDiff ℝ (0 : ℕ) (v t))
    (A : Fin 1 → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ t ∈ Icc a b, ∀ l x,
      ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)
    (κ : ℝ → ℂ) (hκm : MemLp κ ⊤ (volume.restrict (Icc a b)))
    (k : ℝ) (hκ : ∀ t, ‖κ t‖ ≤ k) :
    ∃ M : ℝ, 0 ≤ M ∧
      AEStronglyMeasurable ((Icc a b).indicator
        (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb κ)) volume ∧
      ∀ t, ‖((Icc a b).indicator
        (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb κ)) t‖ ≤ M := by
  obtain ⟨M, hM, hm⟩ := cellTransverseGalerkinOperator_uniform_bound N a b η G hv ξ hc A hA hb κ hG k hκ
  have hmeas : AEStronglyMeasurable ((Icc a b).indicator
      (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb κ)) volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_Icc).mpr
      (cellTransverseGalerkinOperator_aestronglyMeasurable N a b η G hv ξ hc A hA hb κ hG hκm)
  refine ⟨M, hM, hmeas, ?_⟩
  intro t
  by_cases ht : t ∈ Icc a b
  · rw [Set.indicator_of_mem ht]
    exact hm t
  · rw [Set.indicator_of_notMem ht, norm_zero]
    exact hM

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Measurable native scalar products carry their normalized energy price almost everywhere in time. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

theorem normalizedScalarProduct_time_exists {K : ℕ}
    (n p : ℕ) (ϖ : ℝ) (hϖ : 0 < ϖ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (c : ℝ → Vec 2 → ℝ) (hcm : ∀ x, Measurable (fun t => c t x))
    (hc : ∀ t, ContDiff ℝ (K : ℕ) (c t)) (T : E →L[ℝ] F)
    (A B : ℝ) (hB : 0 ≤ B)
    (hgrowth : ∀ t j, j ≤ K → ∀ x, ‖iteratedFDeriv ℝ j (c t) x‖ ≤ B * (1 + ‖x‖) ^ p)
    (hb : ∀ t j, j ≤ K → ∀ x, ρ ^ j * ‖iteratedFDeriv ℝ j (c t) x‖ ≤
      A * polynomialMomentRoot ϖ x ^ p)
    (μ : Measure ℝ) (U : ℝ → PlaneHk Set.univ K E) (hU : MemLp U 2 μ)
    (he : ∀ α, (∫⁻ t, Weighted.chartScalarEnergy
      (fun x => (Weighted.planeMomentSquareRoot (n + p) ϖ 0 x) ^ 2)
      (Weighted.planeJetReadoutOperator K α (U t)) ∂μ) ≠ ⊤) :
    ∃ V : ℝ → PlaneHk Set.univ K F, MemLp V 2 μ ∧
      (∫⁻ t, weightedFactorialNormSq n ϖ 0 ρ K (V t) ∂μ) ≠ ⊤ ∧
      (∀ᵐ t ∂μ, ∀ α, Weighted.planeJetReadoutOperator K α (V t) =ᵐ[volume]
        multiplicationRawJet (fun x => c t x • T) (U t).toFunction.jet α) ∧
      (∀ᵐ t ∂μ, ∀ m, weightedFactorialNormSq m ϖ 0 ρ K (V t) ≤
        ENNReal.ofReal (multiplicationDensityBudget K * (A * ‖T‖) ^ 2) *
          weightedFactorialNormSq (m + p) ϖ 0 ρ K (U t)) := by
  obtain ⟨V, hV, hVe, hVr⟩ := Weighted.exists_scalar_polynomial_product_time
    n p ϖ hϖ ρ c hcm hc T B hB hgrowth μ U hU he
  refine ⟨V, hV, hVe, hVr, ?_⟩
  filter_upwards [hVr] with t ht
  intro m
  apply polynomialProductReadout_energy_le (U t) (V t) (fun x => c t x • T)
    ρ (A * ‖T‖) ϖ hρ p m _ ht
  intro j hj w x
  have hh := normalized_scalar_operator_word_le (c t) j
    ((hc t).of_le (by exact_mod_cast hj)) T ρ
    (A * polynomialMomentRoot ϖ x ^ p) hρ x (hb t j hj x) w
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hh
end

/-! Time-dependent positive source words produce native polynomial fluxes with the exact reserve cost. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

theorem scalarDerivativeProduct_time_exists {K L r : ℕ}
    (hKL : K + r ≤ L + 1) (hr : 1 ≤ r) (I : DerivativeWord2 r)
    (n p : ℕ) (ϖ : ℝ) (hϖ : 0 < ϖ) (ρ : ℝ) (hρ : 0 < ρ)
    (c : ℝ → Vec 2 → ℝ) (hcm : ∀ x, Measurable (fun t => c t x))
    (hc : ∀ t, ContDiff ℝ (K : ℕ) (c t)) (T : E →L[ℝ] F)
    (A B : ℝ) (hB : 0 ≤ B)
    (hgrowth : ∀ t j, j ≤ K → ∀ x, ‖iteratedFDeriv ℝ j (c t) x‖ ≤ B * (1 + ‖x‖) ^ p)
    (hb : ∀ t j, j ≤ K → ∀ x, ρ ^ j * ‖iteratedFDeriv ℝ j (c t) x‖ ≤
      A * polynomialMomentRoot ϖ x ^ p)
    (μ : Measure ℝ) (U : ℝ → PlaneHk Set.univ (L + 1) E) (hU : MemLp U 2 μ)
    (he : (∫⁻ t, weightedGradFactorialNormSq (n + p) ϖ 0 ρ L (U t) ∂μ) ≠ ⊤) :
    ∃ V : ℝ → PlaneHk Set.univ K F, MemLp V 2 μ ∧
      (∫⁻ t, weightedFactorialNormSq n ϖ 0 ρ K (V t) ∂μ) ≠ ⊤ ∧
      (∀ᵐ t ∂μ, ∀ α, Weighted.planeJetReadoutOperator K α (V t) =ᵐ[volume]
        multiplicationRawJet (fun x => c t x • T)
          (Weighted.derivativeSourceOperator hKL I (U t)).toFunction.jet α) ∧
      (∀ᵐ t ∂μ, ∀ m, weightedFactorialNormSq m ϖ 0 ρ K (V t) ≤
        ENNReal.ofReal (multiplicationDensityBudget K * (A * ‖T‖) ^ 2) *
          ENNReal.ofReal ((derivativeReserveFactor ρ K (r - 1)) ^ 2) *
            weightedGradFactorialNormSq (m + p) ϖ 0 ρ L (U t)) := by
  let W := fun t => Weighted.derivativeSourceOperator hKL I (U t)
  have hW : MemLp W 2 μ := (Weighted.derivativeSourceOperator hKL I).comp_memLp' hU
  have hWe (α : JetIndex2 K) : (∫⁻ t, Weighted.chartScalarEnergy
      (fun x => (Weighted.planeMomentSquareRoot (n + p) ϖ 0 x) ^ 2)
      (Weighted.planeJetReadoutOperator K α (W t)) ∂μ) ≠ ⊤ :=
    Weighted.derivativeSourceOperator_weighted_jet_integral_ne_top hKL
      (by omega) I (n + p) ϖ 0 ρ hρ μ U he α
  obtain ⟨V, hV, hVe, hVr, hVb⟩ := normalizedScalarProduct_time_exists
    n p ϖ hϖ ρ hρ.le c hcm hc T A B hB hgrowth hb μ W hW hWe
  refine ⟨V, hV, hVe, hVr, ?_⟩
  filter_upwards [hVb] with t ht
  intro m
  have hh := derivativeSourceOperator_weightedFactorialNormSq_le hKL hr I ρ hρ (m + p) ϖ 0 (U t)
  exact (ht m).trans ((mul_le_mul_right hh _).trans_eq (mul_assoc _ _ _).symm)
end

/-! Almost-everywhere molecular prices suffice for an actual measurable native source flux. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

theorem scalarDerivativeProduct_ae_time_exists {K L r : ℕ}
    (hKL : K + r ≤ L + 1) (hr : 1 ≤ r) (I : DerivativeWord2 r)
    (n p : ℕ) (ϖ : ℝ) (hϖ : 0 < ϖ) (ρ : ℝ) (hρ : 0 < ρ)
    (c : ℝ → Vec 2 → ℝ) (hcm : ∀ x, Measurable (fun t => c t x))
    (hc : ∀ t, ContDiff ℝ (K : ℕ) (c t)) (T : E →L[ℝ] F)
    (A : ℝ) (hA : 0 ≤ A) (μ : Measure ℝ)
    (hb : ∀ᵐ t ∂μ, ∀ j ≤ K, ∀ x, ρ ^ j * ‖iteratedFDeriv ℝ j (c t) x‖ ≤
      A * polynomialMomentRoot ϖ x ^ p)
    (U : ℝ → PlaneHk Set.univ (L + 1) E) (hU : MemLp U 2 μ)
    (he : (∫⁻ t, weightedGradFactorialNormSq (n + p) ϖ 0 ρ L (U t) ∂μ) ≠ ⊤) :
    ∃ V : ℝ → PlaneHk Set.univ K F, MemLp V 2 μ ∧
      (∫⁻ t, weightedFactorialNormSq n ϖ 0 ρ K (V t) ∂μ) ≠ ⊤ ∧
      (∀ᵐ t ∂μ, ∀ α, Weighted.planeJetReadoutOperator K α (V t) =ᵐ[volume]
        multiplicationRawJet (fun x => c t x • T)
          (Weighted.derivativeSourceOperator hKL I (U t)).toFunction.jet α) ∧
      (∀ᵐ t ∂μ, ∀ m, weightedFactorialNormSq m ϖ 0 ρ K (V t) ≤
        ENNReal.ofReal (multiplicationDensityBudget K * (A * ‖T‖) ^ 2) *
          ENNReal.ofReal ((derivativeReserveFactor ρ K (r - 1)) ^ 2) *
            weightedGradFactorialNormSq (m + p) ϖ 0 ρ L (U t)) := by
  obtain ⟨c', hcm', hc', hb', ⟨B, hB, hg⟩, heq⟩ :=
    normalizedCoefficient_measurable_extension K p ρ ϖ A hρ hA μ c hcm hc hb
  obtain ⟨V, hV, hVe, hVr, hVb⟩ := scalarDerivativeProduct_time_exists
    hKL hr I n p ϖ hϖ ρ hρ c' hcm' hc' T A B hB hg hb' μ U hU he
  refine ⟨V, hV, hVe, ?_, hVb⟩
  filter_upwards [hVr, heq] with t ht he
  simpa only [he] using ht
end

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The finite generator is exactly the retained weak scalar multiplier form. -/

theorem cellTransverseGalerkinOperator_form_pairing
    (N : ℕ) (a b η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v) (ξ : Fin 2 → ℂ)
    (hc : ∀ t ∈ Icc a b, ContDiff ℝ (0 : ℕ) (v t))
    (A : Fin 1 → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ t ∈ Icc a b, ∀ l x,
      ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)
    (κ : ℝ → ℂ) (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (t : ℝ) (ht : t ∈ Icc a b) (u z : CellGalerkinSpace (E := ℂ) N) :
    inner ℝ (cellGalerkinValue N (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb κ t u))
      (cellGalerkinValue N z) = cellScalarMultiplierForm η Cw hCw G hG hv hw ξ κ t u.val z.val := by
  rw [cellTransverseGalerkinOperator_test_pairing N a b η G hG hv ξ hc A hA hb κ Cw hCw hw t ht]
  rw [cellDualDerivative_pairing, cellScalarMultiplierForm_pairing]
  rw [cellSourceFunctional_scalar_only, inner_neg_left, sub_eq_add_neg]
  rfl

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! A reserved coefficient budget produces an actual native flux with exact value and moment density. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

theorem reserved_scalar_native_flux_exists {K L r : ℕ}
    (hKL : K + r ≤ L + 1) (hr : 1 ≤ r) (I : DerivativeWord2 r)
    (n p : ℕ) (ϖ ρ : ℝ) (hϖ : 0 < ϖ) (hρ : 0 < ρ)
    (c : ℝ → Vec 2 → ℝ) (hcm : ∀ x, Measurable (fun t => c t x))
    (hc : ∀ t, ContDiff ℝ (K : ℕ) (c t)) (T : E →L[ℝ] F)
    (B : ℝ) (hB : 0 ≤ B) (μ : Measure ℝ)
    (hb : ∀ᵐ t ∂μ, ∀ j ≤ K, ∀ x, ρ ^ j * ‖iteratedFDeriv ℝ j (c t) x‖ ≤
      B / derivativeReserveFactor ρ K (r - 1) * polynomialMomentRoot ϖ x ^ p)
    (U : ℝ → PlaneHk Set.univ (L + 1) E) (hU : MemLp U 2 μ)
    (he : (∫⁻ t, weightedGradFactorialNormSq (n + p) ϖ 0 ρ L (U t) ∂μ) ≠ ⊤) :
    ∃ V : ℝ → PlaneHk Set.univ K F, MemLp V 2 μ ∧
      (∫⁻ t, weightedFactorialNormSq n ϖ 0 ρ K (V t) ∂μ) ≠ ⊤ ∧
      (∀ᵐ t ∂μ, planeValue (V t) =ᵐ[volume]
        (fun z => c t z • T (planeJetOrder (U t) r I z))) ∧
      (∀ᵐ t ∂μ, ∀ᵐ z ∂volume, planeFactorialDensity ρ (V t) z ≤
        multiplicationDensityBudget K * (B * ‖T‖) ^ 2 *
          (polynomialMomentRoot ϖ z ^ p) ^ 2 * planeGradFactorialDensity ρ (U t) z) := by
  let R := derivativeReserveFactor ρ K (r - 1)
  have hR : 0 < R := by dsimp [R, derivativeReserveFactor]; positivity
  obtain ⟨V, hV, hVe, hVr, _⟩ := scalarDerivativeProduct_ae_time_exists hKL hr I
    n p ϖ hϖ ρ hρ c hcm hc T (B / R) (div_nonneg hB hR.le) μ hb U hU he
  refine ⟨V, hV, hVe, ?_, ?_⟩
  · filter_upwards [hVr] with t ht
    have hh := productReadout_planeValue_ae (Weighted.derivativeSourceOperator hKL I (U t))
      (V t) (fun z => c t z • T) ht
    rw [derivativeSourceOperator_planeValue] at hh
    simpa only [smul_apply] using hh
  · filter_upwards [hVr, hb] with t ht hbt
    have hh := scalarDerivativeProduct_readout_density_le hKL hr I (U t) (V t)
      (c t) (hc t) T ρ (B / R) hρ (fun z => polynomialMomentRoot ϖ z ^ p) hbt ht
    have hcancel : B / R * ‖T‖ * derivativeReserveFactor ρ K (r - 1) = B * ‖T‖ := by
      change B / R * ‖T‖ * R = _
      field_simp
    simpa only [hcancel] using hh

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open AVRegularity.Sobolev AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Smooth Fourier representatives transfer higher energy to the original finite lifts. -/

theorem energyThreeArguments_congr {A B C D : Type*} (f : A → B → C → D)
    {a a' : A} {b b' : B} {c c' : C} (ha : a = a') (hb : b = b') (hc : c = c') :
    f a b c = f a' b' c' := by
  cases ha
  cases hb
  cases hc
  rfl

theorem cellGalerkinSmoothEnergyTransfer {K : ℕ} (hK : 1 ≤ K) (N : ℕ)
    (u : CellGalerkinSpace (E := ℂ) N) (D : TorusHk (K + 2) ℂ →L[ℝ] TorusHk K ℂ) (C : ℝ)
    (h : let f := cellGalerkinSmoothValue N u
      let hf := cellGalerkinSmoothValue_contDiff N u
      let hp := cellGalerkinSmoothValue_periodic N u
      2 * inner ℝ (D (finiteSmoothPeriodicHk (K + 2) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp))
        (finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp) +
        (1 / 2) * (‖finiteSmoothPeriodicHk (K + 1) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp‖ ^ 2 -
          ‖torusHkValueCLM (finiteSmoothPeriodicHk (K + 1) f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp)‖ ^ 2) ≤
        C * ‖finiteSmoothPeriodicHk K f (hf.of_le (finiteEnergyOrder_le_smooth _)) hp‖ ^ 2) :
    2 * inner ℝ (D (rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 2) N u))
      (rangeSmoothFourierLiftCLM hK N u) +
      (1 / 2) * (‖rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 1) N u‖ ^ 2 -
        ‖cellGalerkinValue N u‖ ^ 2) ≤ C * ‖rangeSmoothFourierLiftCLM hK N u‖ ^ 2 := by
  dsimp only at h
  have hU := cellGalerkinRangeHigher_eq_smooth hK N u
  have hW := cellGalerkinRangeHigher_eq_smooth (by omega : 1 ≤ K + 2) N u
  have hB := cellGalerkinRangeHigher_eq_smooth (by omega : 1 ≤ K + 1) N u
  let Φ : TorusHk K ℂ → TorusHk (K + 2) ℂ → TorusHk (K + 1) ℂ → ℝ :=
    fun U W B => 2 * inner ℝ (D W) U + (1 / 2) * (‖B‖ ^ 2 - ‖torusHkValueCLM B‖ ^ 2)
  have hl := energyThreeArguments_congr Φ hU hW hB
  have hr := congrArg (fun U : TorusHk K ℂ => C * ‖U‖ ^ 2) hU
  have hh : Φ (rangeSmoothFourierLiftCLM hK N u)
      (rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 2) N u)
      (rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 1) N u) ≤
      C * ‖rangeSmoothFourierLiftCLM hK N u‖ ^ 2 := hl.le.trans (h.trans hr.ge)
  have hv := congrArg (fun z : ComplexCellL2 =>
    2 * inner ℝ (D (rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 2) N u))
      (rangeSmoothFourierLiftCLM hK N u) + (1 / 2) *
      (‖rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 1) N u‖ ^ 2 - ‖z‖ ^ 2))
    (cellGalerkinRangeHigher_value (by omega : 1 ≤ K + 1) N u)
  exact hv.ge.trans hh

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleWords

/-! The actual admissible letter needs only order-zero forcing regularity for native Duhamel. -/

variable {ι σ : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

theorem exists_admissible_letter_order_zero_flux_time
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (L : CycleLetter ι h D) (ta tb : ℝ) (J H : ℕ)
    (hL : IsCycleLetter π L (Set.Icc ta tb ×ˢ Set.univ) J H)
    (κ : σ → ℕ) (a : σ) (b : ι → σ) (v : ι)
    (lo : ℕ) (X₀ : Vec 2) (δ : ℝ)
    (hm : ∀ u o (k : Fin (L.edge v u o).length), ∀ w X z,
      Measurable (fun t => ((L.edge v u o).get k).coeff w t X z))
    (ϖ : ℝ) (hϖ : 0 < ϖ) (ρ : ℝ) (hρ : 0 < ρ)
    (W : ∀ u, ℝ → PlaneHk Set.univ (κ (b u) + 1) (h u))
    (hW : ∀ u, MemLp (W u) 2 (volume.restrict (Set.Icc ta tb)))
    (he : ∀ u, (∫⁻ t in Set.Icc ta tb,
      weightedGradFactorialNormSq L.slow ϖ 0 ρ (κ (b u)) (W u t)) ≠ ⊤) :
    ∃ V : ℝ → PlaneHk Set.univ 0 (PiLp 2 (fun _ : Fin 2 => h v)),
      MemLp V 2 (volume.restrict (Set.Icc ta tb)) ∧
      ∀ᵐ t ∂volume.restrict (Set.Icc ta tb),
        planeJetReadoutOperator 0 (valueIndex2 0) (V t) =ᵐ[volume]
          letterAdmissibleFlux L κ a b v lo X₀ δ (fun u => W u t) t := by
  classical
  let Idx := Σ u : ι, admissibleOrders κ D a (b u)
  have hreserve (p : Idx) : 0 + (p.2.val - 1) ≤ κ (b p.1) + 1 := by
    have hh := admissible_letter_source_reserve κ D a (b p.1) p.2
    omega
  have hex (p : Idx) := exists_letter_edge_flux_time π hπ L ta tb J H hL v p.1
    (admissibleLetterOrder κ D a (b p.1) p.2) lo X₀ δ (hm p.1 _) 0 (κ (b p.1)) 0
    (Nat.zero_le J) (hreserve p) ϖ hϖ ρ hρ (W p.1) (hW p.1)
    (by simpa only [zero_add] using he p.1)
  choose U hU hUe hUr using hex
  obtain ⟨V, hV, _, hVr⟩ := finite_weighted_sobolev_flux_sum 0 ϖ 0 ρ hρ
    (volume.restrict (Set.Icc ta tb)) U hU hUe _ hUr
  refine ⟨V, hV, ?_⟩
  filter_upwards [hVr] with t ht
  filter_upwards [ht] with z hz
  simpa only [Idx, Fintype.sum_sigma, letterAdmissibleFlux,
    admissibleLetterSourceIndex, admissibleLetterOrder, sourceWordIndex] using! hz

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.CycleWords

/-! Actual finite scalar multiplier trajectories satisfy full-test moment primitives. -/

theorem cellTransverseGalerkin_full_test_primitive
    (N : ℕ) (a b η : ℝ) (hab : a ≤ b) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
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
    (u₀ : ComplexCellL2)
    (y : ContinuousMap (Icc a b) (CellGalerkinSpace (E := ℂ) N))
    (hy : AVenhance.Infra.ODE.IsLinearIntegralSolution
      ((Icc a b).indicator (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb κ))
      0 (cellGalerkinL2Initial N u₀) a b (AVenhance.Infra.ODE.extendCurve hab y)) 
    (z : TorusHk 1 ℂ) (t : ℝ) (ht : t ∈ Icc a b) :
    inner ℝ (cellGalerkinValue N (extendCurve hab y t)) (torusHkValueCLM z) =
      inner ℝ u₀ (torusHkValueCLM (galerkinProj N z)) +
        ∫ r in a..t, cellScalarMultiplierForm η Cw hCw G hG hv hw ξ κ r
          (extendCurve hab y r).val (galerkinProj N z) := by
  let Op := (Icc a b).indicator (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb κ)
  obtain ⟨M, hM, hm, hbOp⟩ := cellTransverseGalerkin_window_operator_data N G hG hv ξ
    hc A hA hb κ hκm k hκ
  have hcurve := cellGalerkin_linear_weak_curve hab N (cellGalerkinState (E := ℂ) N)
    Op 0 (cellGalerkinL2Initial N u₀) y hy hm M hM hbOp (memLp_const 0)
  have hi : extendCurve hab y a = cellGalerkinL2Initial N u₀ := by
    simpa only [intervalIntegral.integral_same, add_zero] using hy a ⟨le_rfl, hab⟩
  have he := hcurve.increment a ⟨le_rfl, hab⟩ t ht ht.1 (cellGalerkinInitial N z).val
  change inner ℝ (cellGalerkinValue N (extendCurve hab y t))
      (cellGalerkinValue N (cellGalerkinInitial N z)) -
    inner ℝ (cellGalerkinValue N (extendCurve hab y a))
      (cellGalerkinValue N (cellGalerkinInitial N z)) = _ at he
  rw [← cellGalerkinValue_projected_test_pairing N (extendCurve hab y t) z, hi,
    cellGalerkinL2Initial_pairing] at he
  have hp : (∫ r in a..t, inner ℝ
      (cellPivotDualCLM (torusHkValueCLM
        (cellGalerkinState N (linearRhs Op 0 (extendCurve hab y) r)))) (cellGalerkinInitial N z).val) =
      ∫ r in a..t, cellScalarMultiplierForm η Cw hCw G hG hv hw ξ κ r
        (extendCurve hab y r).val (galerkinProj N z) := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le ht.1] at hr
    have hrab : r ∈ Icc a b := ⟨hr.1, hr.2.trans ht.2⟩
    have hadj := ContinuousLinearMap.adjoint_inner_left (torusHkValueCLM (E := ℂ) (K := 1))
      (cellGalerkinInitial N z).val
      (torusHkValueCLM (cellGalerkinState N (linearRhs Op 0 (extendCurve hab y) r)))
    apply hadj.trans
    change inner ℝ (cellGalerkinValue N (linearRhs Op 0 (extendCurve hab y) r))
      (cellGalerkinValue N (cellGalerkinInitial N z)) = _
    simp only [linearRhs, Pi.zero_apply, add_zero, Op, indicator_of_mem hrab]
    exact cellTransverseGalerkinOperator_form_pairing N a b η G hG hv ξ hc A hA hb κ
      Cw hCw hw r hrab (extendCurve hab y r) (cellGalerkinInitial N z)
  rw [hp] at he
  change inner ℝ (cellGalerkinValue N (extendCurve hab y t)) (torusHkValueCLM z) -
    inner ℝ u₀ (torusHkValueCLM (galerkinProj N z)) = _ at he
  linarith only [he]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! The four scalar entries of a metric insertion assemble into an actual
native flux with a fixed dimensional price. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem metricMatrix_native_flux_exists (K n p : ℕ) (ϖ ρ : ℝ)
    (hϖ : 0 < ϖ) (hρ : 0 < ρ) (μ : Measure ℝ)
    (c : Fin 2 → Fin 2 → ℝ → Vec 2 → ℝ)
    (hcm : ∀ k l z, Measurable (fun t => c k l t z))
    (hc : ∀ k l t, ContDiff ℝ (K : ℕ) (c k l t))
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ k l, ∀ᵐ t ∂μ, ∀ j ≤ K, ∀ z,
      ρ ^ j * ‖iteratedFDeriv ℝ j (c k l t) z‖ ≤ B * polynomialMomentRoot ϖ z ^ p)
    (U : ℝ → PlaneHk Set.univ (K + 1) E) (hU : MemLp U 2 μ)
    (he : (∫⁻ t, weightedGradFactorialNormSq (n + p) ϖ 0 ρ K (U t) ∂μ) ≠ ⊤) :
    ∃ V : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)),
      MemLp V 2 μ ∧ (∫⁻ t, weightedFactorialNormSq n ϖ 0 ρ K (V t) ∂μ) ≠ ⊤ ∧
      (∀ᵐ t ∂μ, planeValue (V t) =ᵐ[volume] (fun z =>
        ∑ kl : Fin 2 × Fin 2, c kl.1 kl.2 t z •
          Weighted.fluxCoordinateInjection kl.1 (ContinuousLinearMap.id ℝ E)
            (planeJetOrder (U t) 1 (fun _ => kl.2) z))) ∧
      (∀ᵐ t ∂μ, ∀ᵐ z ∂volume, planeFactorialDensity ρ (V t) z ≤
        (4 * Real.sqrt (multiplicationDensityBudget K) * B) ^ 2 *
          (polynomialMomentRoot ϖ z ^ p) ^ 2 * planeGradFactorialDensity ρ (U t) z) := by
  classical
  let T := fun k => Weighted.fluxCoordinateInjection k (ContinuousLinearMap.id ℝ E)
  have hex (kl : Fin 2 × Fin 2) : ∃ V : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)),
      MemLp V 2 μ ∧ (∫⁻ t, weightedFactorialNormSq n ϖ 0 ρ K (V t) ∂μ) ≠ ⊤ ∧
      (∀ᵐ t ∂μ, planeValue (V t) =ᵐ[volume] (fun z =>
        c kl.1 kl.2 t z • T kl.1 (planeJetOrder (U t) 1 (fun _ => kl.2) z))) ∧
      (∀ᵐ t ∂μ, ∀ᵐ z ∂volume, planeFactorialDensity ρ (V t) z ≤
        multiplicationDensityBudget K * (B * ‖T kl.1‖) ^ 2 *
          (polynomialMomentRoot ϖ z ^ p) ^ 2 * planeGradFactorialDensity ρ (U t) z) := by
    apply reserved_scalar_native_flux_exists (K := K) (L := K) (r := 1)
      (by omega) (by omega) (fun _ => kl.2) n p ϖ ρ hϖ hρ
      (c kl.1 kl.2) (hcm kl.1 kl.2) (hc kl.1 kl.2) (T kl.1) B hB μ _ U hU he
    simpa [derivativeReserveFactor, Nat.factorial_ne_zero] using hb kl.1 kl.2
  choose V hV hVe hvalue hdensity using hex
  let A := Real.sqrt (multiplicationDensityBudget K) * B
  have hA : 0 ≤ A := mul_nonneg (Real.sqrt_nonneg _) hB
  have hdens : ∀ᵐ t ∂μ, ∀ᵐ z ∂volume,
      planeFactorialDensity ρ (∑ kl, V kl t) z ≤ (4 * A) ^ 2 *
        (polynomialMomentRoot ϖ z ^ p) ^ 2 * planeGradFactorialDensity ρ (U t) z := by
    filter_upwards [ae_all_iff.mpr hdensity] with t ht
    have hh := nativeFactorialDensity_sum_price_le ρ (fun kl => V kl t)
      (fun _ => A) (fun _ => hA)
      (fun z => (polynomialMomentRoot ϖ z ^ p) ^ 2 * planeGradFactorialDensity ρ (U t) z)
      (fun z => mul_nonneg (sq_nonneg _) (planeGradFactorialDensity_nonneg ρ (U t) z))
      (fun kl => by
        filter_upwards [ht kl] with z hz
        have hT : ‖T kl.1‖ ≤ 1 :=
          (fluxCoordinateInjection_norm_le kl.1 (ContinuousLinearMap.id ℝ E)).trans
            ContinuousLinearMap.norm_id_le
        have hcost : B * ‖T kl.1‖ ≤ B := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hT hB
        have hn := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (mul_nonneg hB (norm_nonneg (T kl.1))) hcost 2)
              (multiplicationDensityBudget_nonneg K)) (sq_nonneg (polynomialMomentRoot ϖ z ^ p)))
          (planeGradFactorialDensity_nonneg ρ (U t) z)
        have hh := hz.trans hn
        simpa only [A, mul_pow, Real.sq_sqrt (multiplicationDensityBudget_nonneg K),
          mul_assoc] using hh)
    simpa [Finset.sum_const, Fintype.card_prod, mul_assoc] using hh
  refine ⟨fun t => ∑ kl, V kl t, ?_, ?_, ?_, ?_⟩
  · exact memLp_finsetSum (ε' := PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
      (f := V) Finset.univ (fun kl _ => hV kl)
  · have hh := nativeFlux_time_moment_shift_budget n p ϖ ρ (4 * A) μ
      (fun t => ∑ kl, V kl t) U hdens
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top he) hh
  · filter_upwards [ae_all_iff.mpr hvalue] with t ht
    have hv := planeJetOrder_finite_sum_ae (Nat.zero_le K) (fun kl => V kl t)
      (fun i : Fin 0 => Fin.elim0 i)
    filter_upwards [hv, ae_all_iff.mpr ht] with z hz hzs
    exact hz.trans (Finset.sum_congr rfl (fun kl _ => hzs kl))
  · simpa only [A, mul_assoc] using hdens

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleWords

/-! The preceding Taylor-letter source has a genuine native L2 realization from the committed envelope and polynomial moment machinery. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

theorem wordChainPrevious_l2_flux_exists (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (letters : Fin N → CycleLetter ι h D) (a b : ℝ) (J H : ℕ)
    (j : Fin N) (x : ι)
    (hL : IsCycleLetter π (letters j) (Set.Icc a b ×ˢ Set.univ) J H)
    (κ : Fin (N + 1) → ι → ℕ)
    (X0 : Vec 2) (δ : ℝ)
    (hm : ∀ u o (k : Fin ((letters j).edge x u o).length), ∀ w X z,
      Measurable (fun t => (((letters j).edge x u o).get k).coeff w t X z))
    (ϖ ρ : ℝ) (hϖ : 0 < ϖ) (hρ : 0 < ρ)
    (Uw : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hUw : ∀ u, MemLp (Uw (j.castSucc, u)) 2 (volume.restrict (Set.Icc a b)))
    (he : ∀ u, (∫⁻ t in Set.Icc a b,
      weightedGradFactorialNormSq (letters j).slow ϖ 0 ρ (κ j.castSucc u) (Uw (j.castSucc, u) t)) ≠ ⊤) :
    ∃ S : ℝ → PlaneFluxL2 (h x), MemLp S 2 (volume.restrict (Set.Icc a b)) ∧
      ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ k, S t k =ᵐ[volume]
        fun z => wordChainPreviousFlux letters X0 δ κ (fun p => Uw p t) (j.succ, x) t z k := by
  obtain ⟨V, hV, hVr⟩ := exists_admissible_letter_order_zero_flux_time π hπ (letters j) a b J H hL
    (fun p : Fin (N + 1) × ι => κ p.1 p.2) (j.succ, x) (fun u => (j.castSucc, u)) x
    (if (letters j).positive then 1 else 0) X0 δ hm ϖ hϖ ρ hρ
    (fun u => Uw (j.castSucc, u)) hUw he
  refine ⟨fun t => planeFluxValueOperator 0 (V t),
    planeFluxValueOperator_memLp _ V hV, ?_⟩
  filter_upwards [hVr] with t ht
  intro k
  have hv := (planeJetReadout_ae_raw (V t) (valueIndex2 0)).symm.trans ht
  filter_upwards [hv, planeFluxValueOperator_ae 0 (V t) k] with z hz hF
  rw [hF, hz, wordChainPreviousFlux_succ]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Every genuine nonlinear raw graph supplies the native equation and local source integrability. -/

theorem cellFibreGraph_native_equation (η Cw : ℝ) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellInverseValue ⟨fun t _ => G t, v, 0, 0⟩
      (fibreGraphSource η v ξ (cellValue D)) (fibreGraphFlux η G ξ (cellValue D)) D) :
    (∀ n : ℕ, MemLp (fun t => cellFibreGraphSourceClass η Cw hCw hv hw ξ t (cellRawTrace D t))
      2 (volume.restrict (Icc (-(n : ℝ)) n))) ∧
    (∀ n : ℕ, ∀ j, MemLp (fun t => cellFibreGraphFluxClass η G ξ t (cellRawTrace D t) j)
      2 (volume.restrict (Icc (-(n : ℝ)) n))) ∧
    Continuous (cellRawTrace D) ∧
    (∀ t, (cellRawTrace D t : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] cellValue D t) ∧
    (∀ᵐ t ∂volume, ∀ a, ((cellH1Slice D t).val a : Vec 2 → ℂ) =ᵐ[
      volume.restrict AVenhance.unitCube] D t a) ∧
    (∀ a b : ℝ, a ≤ b → CellWeakHilbertCurve a b (cellRawTrace D) (cellH1Slice D)
      (fun t => cellDualDerivative ⟨fun t _ => G t, v, 0, 0⟩ hG V hv.1 hb t (cellH1Slice D t)
        (cellFibreGraphSourceClass η Cw hCw hv hw ξ t (cellRawTrace D t))
        (cellFibreGraphFluxClass η G ξ t (cellRawTrace D t)))) := by
  let src := fibreGraphSource η v ξ (cellValue D)
  let F := fibreGraphFlux η G ξ (cellValue D)
  have hDn := hD.2.2
  have hs := fibreGraphSource_ul_bound η Cw hv hw ξ hD
  have hgm : Measurable G := hG.1.comp
    (measurable_id.prodMk (measurable_const (a := (0 : Vec 2))))
  have hf := fibreGraphFlux_ul_bound η hη G hgm
    (fun t i j => cellMetric_entry_bound hG t 0 i j) ξ hD.1
  have hsrc (a b : ℝ) (_ : a ≤ b) : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)) :=
    cellUl_memLp_product_interval_ae univ src hs.2 (hs.1.trans_lt (by finiteness)) a b (subset_univ _)
  have hflux (a b : ℝ) (_ : a ≤ b) : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)) :=
    cellUl_memLp_product_interval_ae univ F hf.2
      (hf.1.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hD.2.2)) a b (subset_univ _)
  obtain ⟨hc, htr, hj, he⟩ := cellSolution_allTime_native
    ⟨fun t _ => G t, v, 0, 0⟩ hG V 0 hv.1 hb measurable_const
    (fun _ => by simp only [Pi.zero_apply, norm_zero, le_refl]) src F hsrc hflux D hD.1
  have hsr (t : ℝ) : cellSourceSlice src t =
      cellFibreGraphSourceClass η Cw hCw hv hw ξ t (cellRawTrace D t) :=
    cellSourceSlice_eq_of_ae src t _
      (cellFibreGraphSourceClass_ae η Cw hCw hv hw ξ t _ (cellValue D) (htr t))
  have hfr (t : ℝ) (j : Fin 2) : cellSourceSlice (fun r x => F r x j) t =
      cellFibreGraphFluxClass η G ξ t (cellRawTrace D t) j :=
    cellSourceSlice_eq_of_ae _ t _ (cellFibreGraphFluxClass_ae η G ξ t _ (cellValue D) (htr t) j)
  have hsrfun : cellSourceSlice src =
      fun t => cellFibreGraphSourceClass η Cw hCw hv hw ξ t (cellRawTrace D t) := funext hsr
  have hfrfun (j : Fin 2) : cellSourceSlice (fun r x => F r x j) =
      fun t => cellFibreGraphFluxClass η G ξ t (cellRawTrace D t) j :=
    funext (fun t => hfr t j)
  have hn (n : ℕ) : -(n : ℝ) ≤ n := neg_le_self (Nat.cast_nonneg n)
  refine ⟨?_, ?_, hc, htr, hj, ?_⟩
  · intro n
    simpa only [hsrfun] using cellSourceSlice_memLp (Icc (-(n : ℝ)) n) src (hsrc _ _ (hn n))
  · intro n j
    have hm := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).comp_memLp' (hflux _ _ (hn n))
    simpa only [hfrfun] using cellSourceSlice_memLp (Icc (-(n : ℝ)) n) (fun r x => F r x j) hm
  · intro a b hab
    simpa only [hsr, hfr] using he a b hab

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Actual joint H1 energy states retain the continuous trace almost everywhere. -/

local instance cellEnergyJointH1RealInner : InnerProductSpace ℝ CellComplexH1 :=
  InnerProductSpace.complexToReal

local instance cellEnergyJointH1TimeCountable (a b : ℝ) :
    SecondCountableTopology (Lp CellComplexH1 2 (volume.restrict (Icc a b))) :=
  cellComplexH1LpSecondCountable _

def cellEnergyJointH1 {a b : ℝ} (hab : a ≤ b)
    (F : Lp (CellEnergySpace a b) 2 centeredPlaneFrequencyMeasure) :
    Lp CellComplexH1 2 (centeredPlaneFrequencyMeasure.prod (volume.restrict (Icc a b))) :=
  bochnerL2Joint centeredPlaneFrequencyMeasure (volume.restrict (Icc a b))
    (cellEnergyFrequencyTimeState centeredPlaneFrequencyMeasure hab F)

theorem cellEnergyJointH1_trace_slices {a b : ℝ} (hab : a ≤ b)
    (F : Lp (CellEnergySpace a b) 2 centeredPlaneFrequencyMeasure) :
    ∀ᵐ θ ∂centeredPlaneFrequencyMeasure, ∀ᵐ t ∂volume.restrict (Icc a b),
      cellComplexH1ValueCLM (cellEnergyJointH1 hab F (θ, t)) =
        cellEnergySpaceTrace hab (F θ) t := by
  have hj := bochnerL2Joint_slices centeredPlaneFrequencyMeasure
    (volume.restrict (Icc a b)) (cellEnergyFrequencyTimeState centeredPlaneFrequencyMeasure hab F)
  have hf := cellEnergyFrequencyTimeState_ae centeredPlaneFrequencyMeasure hab F
  filter_upwards [hj, hf] with θ hj' hf'
  rw [hf'] at hj'
  have ht := cellEnergySpaceTrace_agrees hab (F θ)
  filter_upwards [hj', ht] with t hjt htt
  change cellComplexH1ValueCLM (bochnerL2Joint centeredPlaneFrequencyMeasure
    (volume.restrict (Icc a b)) (cellEnergyFrequencyTimeState centeredPlaneFrequencyMeasure hab F)
      (θ, t)) = _
  rw [← hjt, cellComplexH1ValueCLM_eq]
  exact htt.symm

end AVRegularity.CycleWords
end
end
