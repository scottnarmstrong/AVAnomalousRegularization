-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.CellEnergyJointH1Trace
public import AVRegularity.CycleEvolution.FibreCoefficientGraphModeRatio
import AVRegularity.CycleWords.PlaneScalarBlochSurjective
import AVRegularity.CycleWords.CellComplexH1Separability
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleWords

/-! The full higher constructed generator reads out the original variational cell equation. -/

 theorem constructedHigherFullGeneratorCLM_pairing (K : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (ν : ℝ) (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (V : ℝ) (hb : ∀ t x, ∑ j, ocCellDrift α q Λ ζ m ν y₀ t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) (U : TorusHk (K + 2) ℂ) (z : TorusHk 1 ℂ) :
    inner ℝ (torusHkValueCLM (constructedHigherFullGeneratorCLM K hΛ hζ ν y₀ hv G θ κ t U))
      (torusHkValueCLM z) =
    cellGeneratorForm ⟨fun t _ => G t, ocCellDrift α q Λ ζ m ν y₀, θ, κ⟩ hG V hv.1 hb t
      (cellH2BaseCLM (truncateTorusHk (by omega : 2 ≤ K + 2) U)) z := by
  let C : CellCoefficients := ⟨fun t _ => G t, ocCellDrift α q Λ ζ m ν y₀, θ, κ⟩
  let u := truncateTorusHk (by omega : 2 ≤ K + 2) U
  have hd : cellDiffusionForm C hG t (cellH2BaseCLM u) z =
      inner ℝ (cellConstantMetricStrongDiffusionCLM G θ t u) (torusHkValueCLM z) := by
    have he := congrArg Complex.re (cellConstantMetricStrongDiffusionCLM_pair G hG θ t u z)
    rw [cellComplexDiffusionForm_real_part C hG, cellComplexPair_re] at he
    exact he
  simp only [constructedHigherFullGeneratorCLM, add_apply, sub_apply, ContinuousLinearMap.comp_apply,
    map_add, map_sub, torusHigherStrongDiffusionCLM_value,
    constructedHigherAdvectionCLM_value K hΛ hζ ν y₀ hv V hb,
    torusHigherScalarCLM_value, inner_add_left, inner_sub_left, Fin.sum_univ_two]
  change _ = cellGeneratorForm C hG V hv.1 hb t (cellH2BaseCLM u) z
  simp only [cellGeneratorForm, add_apply, sub_apply, Fin.sum_univ_two,
    pullbackInnerCLM_apply, ContinuousLinearMap.comp_apply]
  rw [hd]
  rfl

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Positive degree metric Taylor insertions produce the literal matrix forcing
with a uniform coefficient constant and a moment shift by the Taylor degree. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem metricTaylorMatrix_native_flux_exists (Ks Kmax : ℕ)
    (M : ℕ → ℝ) (hM : ∀ r, 0 ≤ M r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K ≤ Kmax,
      ∀ (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (a b ϖ ρ δ ζ g : ℝ),
      (∀ X k l, Measurable (fun t => G t X k l)) →
      (∀ t ∈ Set.Icc a b, ∀ k l, ContDiff ℝ (Ks : ℕ) (fun z => G t z k l)) →
      0 < ϖ → 0 < ρ → ρ * ϖ ≤ 1 → 0 ≤ ζ → ζ ≤ 1 → 0 ≤ g → δ = ζ * ϖ →
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ r, 1 ≤ r → r ≤ Ks → ∀ k l,
        ‖iteratedFDeriv ℝ r (fun z => G t z k l) 0‖ ≤ M r * g * δ ^ r) →
      ∀ (n : ℕ) (U : ℝ → PlaneHk Set.univ (K + 1) E),
      MemLp U 2 (volume.restrict (Set.Icc a b)) →
      (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (n + Ks) ϖ 0 ρ K (U t)) ≠ ⊤ →
      ∃ V : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)),
        MemLp V 2 (volume.restrict (Set.Icc a b)) ∧
        (∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 ρ K (V t)) ≠ ⊤ ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V t) =ᵐ[volume] (fun z =>
          ∑ kl : Fin 2 × Fin 2, taylorSlow 1 Ks (fun y => G t y kl.1 kl.2) 0 z •
            Weighted.fluxCoordinateInjection kl.1 (ContinuousLinearMap.id ℝ E)
              (planeJetOrder (U t) 1 (fun _ => kl.2) z))) ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ᵐ z ∂volume,
          planeFactorialDensity ρ (V t) z ≤
            (4 * Real.sqrt (multiplicationDensityBudget K) * (C * g * ζ)) ^ 2 *
              (polynomialMomentRoot ϖ z ^ Ks) ^ 2 * planeGradFactorialDensity ρ (U t) z) := by
  classical
  obtain ⟨C, hC, hcoeff⟩ := metricTaylor_time_coefficient_budget Ks Kmax M hM
  refine ⟨C, hC, ?_⟩
  intro K hK G a b ϖ ρ δ ζ g hm hf hϖ hρ hscale hζ hζ1 hg hδ hjet n U hU he
  let cc := fun k l => metricTaylorTimeCoefficient Ks (fun t z => G t z k l) a b
  have hh (k l : Fin 2) := hcoeff (fun t z => G t z k l) a b ϖ ρ δ ζ g
    (fun X => hm X k l) (fun t ht => hf t ht k l) hϖ hρ.le hscale hζ hζ1 hg hδ
    (by filter_upwards [hjet] with t ht; exact fun r hr hrK => ht r hr hrK k l)
  have hb : ∀ k l, ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j ≤ K, ∀ z,
      ρ ^ j * ‖iteratedFDeriv ℝ j (cc k l t) z‖ ≤
        (C * g * ζ) * polynomialMomentRoot ϖ z ^ Ks := by
    intro k l
    filter_upwards [(hh k l).2.2] with t ht
    exact fun j hj => ht j (hj.trans hK)
  obtain ⟨V, hV, hVe, hv, hdens⟩ := metricMatrix_native_flux_exists K n Ks ϖ ρ hϖ hρ
    (volume.restrict (Set.Icc a b)) cc (fun k l => (hh k l).1)
    (fun k l t => ((hh k l).2.1 t).of_le (by exact_mod_cast hK))
    (C * g * ζ) (mul_nonneg (mul_nonneg hC hg) hζ) hb U hU he
  refine ⟨V, hV, hVe, ?_, hdens⟩
  filter_upwards [hv, ae_restrict_mem measurableSet_Icc] with t ht htI
  simpa only [cc, metricTaylorTimeCoefficient, ite_eq_left htI] using ht
end

/-! Positive degree metric Taylor insertions produce the literal matrix forcing
with a uniform coefficient constant and a moment shift by the Taylor degree. -/

theorem metricTaylorMatrix_native_flux_exists_uniform (Ks Kmax : ℕ)
    (M : ℕ → ℝ) (hM : ∀ r, 0 ≤ M r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E], ∀ K ≤ Kmax,
      ∀ (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (a b ϖ ρ δ ζ g : ℝ),
      (∀ X k l, Measurable (fun t => G t X k l)) →
      (∀ t ∈ Set.Icc a b, ∀ k l, ContDiff ℝ (Ks : ℕ) (fun z => G t z k l)) →
      0 < ϖ → 0 < ρ → ρ * ϖ ≤ 1 → 0 ≤ ζ → ζ ≤ 1 → 0 ≤ g → δ = ζ * ϖ →
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ r, 1 ≤ r → r ≤ Ks → ∀ k l,
        ‖iteratedFDeriv ℝ r (fun z => G t z k l) 0‖ ≤ M r * g * δ ^ r) →
      ∀ (n : ℕ) (U : ℝ → PlaneHk Set.univ (K + 1) E),
      MemLp U 2 (volume.restrict (Set.Icc a b)) →
      (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (n + Ks) ϖ 0 ρ K (U t)) ≠ ⊤ →
      ∃ V : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)),
        MemLp V 2 (volume.restrict (Set.Icc a b)) ∧
        (∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 ρ K (V t)) ≠ ⊤ ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V t) =ᵐ[volume] (fun z =>
          ∑ kl : Fin 2 × Fin 2, taylorSlow 1 Ks (fun y => G t y kl.1 kl.2) 0 z •
            Weighted.fluxCoordinateInjection kl.1 (ContinuousLinearMap.id ℝ E)
              (planeJetOrder (U t) 1 (fun _ => kl.2) z))) ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ᵐ z ∂volume,
          planeFactorialDensity ρ (V t) z ≤
            (4 * Real.sqrt (multiplicationDensityBudget K) * (C * g * ζ)) ^ 2 *
              (polynomialMomentRoot ϖ z ^ Ks) ^ 2 * planeGradFactorialDensity ρ (U t) z) := by
  classical
  obtain ⟨C, hC, hcoeff⟩ := metricTaylor_time_coefficient_budget Ks Kmax M hM
  refine ⟨C, hC, ?_⟩
  intro E _ _ _ _ _ _ K hK G a b ϖ ρ δ ζ g hm hf hϖ hρ hscale hζ hζ1 hg hδ hjet n U hU he
  let cc := fun k l => metricTaylorTimeCoefficient Ks (fun t z => G t z k l) a b
  have hh (k l : Fin 2) := hcoeff (fun t z => G t z k l) a b ϖ ρ δ ζ g
    (fun X => hm X k l) (fun t ht => hf t ht k l) hϖ hρ.le hscale hζ hζ1 hg hδ
    (by filter_upwards [hjet] with t ht; exact fun r hr hrK => ht r hr hrK k l)
  have hb : ∀ k l, ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j ≤ K, ∀ z,
      ρ ^ j * ‖iteratedFDeriv ℝ j (cc k l t) z‖ ≤
        (C * g * ζ) * polynomialMomentRoot ϖ z ^ Ks := by
    intro k l
    filter_upwards [(hh k l).2.2] with t ht
    exact fun j hj => ht j (hj.trans hK)
  obtain ⟨V, hV, hVe, hv, hdens⟩ := metricMatrix_native_flux_exists K n Ks ϖ ρ hϖ hρ
    (volume.restrict (Set.Icc a b)) cc (fun k l => (hh k l).1)
    (fun k l t => ((hh k l).2.1 t).of_le (by exact_mod_cast hK))
    (C * g * ζ) (mul_nonneg (mul_nonneg hC hg) hζ) hb U hU he
  refine ⟨V, hV, hVe, ?_, hdens⟩
  filter_upwards [hv, ae_restrict_mem measurableSet_Icc] with t ht htI
  simpa only [cc, metricTaylorTimeCoefficient, ite_eq_left htI] using ht

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Native joint H1 states agree with each actual energy carrier time state. -/

local instance cellEnergyJointH1StateRealInner : InnerProductSpace ℝ CellComplexH1 :=
  InnerProductSpace.complexToReal

local instance cellEnergyJointH1StateTimeCountable (a b : ℝ) :
    SecondCountableTopology (Lp CellComplexH1 2 (volume.restrict (Set.Icc a b))) :=
  cellComplexH1LpSecondCountable _

theorem cellEnergyJointH1_state_slices {a b : ℝ} (hab : a ≤ b)
    (F : Lp (CellEnergySpace a b) 2 centeredPlaneFrequencyMeasure) :
    ∀ᵐ θ ∂centeredPlaneFrequencyMeasure, ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      cellEnergyJointH1 hab F (θ, t) = cellFiniteEnergyTimeStateCLM hab (F θ) t := by
  have hj := bochnerL2Joint_slices centeredPlaneFrequencyMeasure
    (volume.restrict (Set.Icc a b)) (cellEnergyFrequencyTimeState centeredPlaneFrequencyMeasure hab F)
  filter_upwards [hj, cellEnergyFrequencyTimeState_ae centeredPlaneFrequencyMeasure hab F]
    with θ hj' hf'
  rw [hf'] at hj'
  filter_upwards [hj'] with t ht
  exact ht.symm

end AVRegularity.CycleWords
end

section
namespace AVRegularity.CycleWords

/-! The metric insertion price is bounded using only the maximum slot,
independently of the component Hilbert space. -/

def metricInsertionUniformPrice (Kmax : ℕ) (C : ℝ) : ℝ :=
  4 * (∑ N ∈ Finset.range (Kmax + 1), Real.sqrt (multiplicationDensityBudget N)) * C

theorem metricInsertion_price_le {K Kmax : ℕ} (hK : K ≤ Kmax)
    (C g ζ : ℝ) (hC : 0 ≤ C) (hg : 0 ≤ g) (hζ : 0 ≤ ζ) :
    (4 * Real.sqrt (multiplicationDensityBudget K) * (C * g * ζ)) ^ 2 ≤
      (metricInsertionUniformPrice Kmax C) ^ 2 * (g * ζ) ^ 2 := by
  have hh : Real.sqrt (multiplicationDensityBudget K) ≤
      ∑ N ∈ Finset.range (Kmax + 1), Real.sqrt (multiplicationDensityBudget N) :=
    Finset.single_le_sum (fun N _ => Real.sqrt_nonneg _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hK))
  have hp := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 4))
    (by positivity : 0 ≤ C * g * ζ)
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 4 * Real.sqrt (multiplicationDensityBudget K) * (C * g * ζ)) hp 2
  simpa only [metricInsertionUniformPrice, mul_pow, mul_assoc] using hs

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The finite correction energy consumes the exact scalar forcing of the constant mode. -/

theorem cellTransverseGalerkinOperator_correction_pairing
    (N : ℕ) (a b η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v) (ξ : Fin 2 → ℂ)
    (hc : ∀ t ∈ Icc a b, ContDiff ℝ (0 : ℕ) (v t))
    (A : Fin 1 → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ t ∈ Icc a b, ∀ l x,
      ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)
    (κ : ℝ → ℂ) (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (t : ℝ) (ht : t ∈ Icc a b) (u : CellGalerkinSpace (E := ℂ) N) :
    let z := u - cellGalerkinConstant N 1
    let src := -cellScalarCLM Complex.I (cellFibreDriftCouplingCLM η Cw hCw hv hw ξ t (cellGalerkinValue N u)) +
      cellScalarCLM (κ t - ∑ j : Fin 2, ∑ l : Fin 2,
        (G t j l : ℂ) * ((Real.sqrt η : ℂ) * ξ j) * ((Real.sqrt η : ℂ) * ξ l)) (cellConstantCLM 1)
    inner ℝ (cellGalerkinValue N (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb κ t u))
      (cellGalerkinValue N z) =
    cellGeneratorForm ⟨fun t _ => G t, 0, fun j => (Real.sqrt η : ℂ) * ξ j, κ⟩
      hG 0 measurable_const (by intro t x; simp) t z.val z.val +
      cellSourceFunctional (fun j => (Real.sqrt η : ℂ) * ξ j) src 0 z.val := by
  let z := u - cellGalerkinConstant N 1
  let s := -cellScalarCLM Complex.I
    (cellFibreDriftCouplingCLM η Cw hCw hv hw ξ t (cellGalerkinValue N u))
  have hc1 : (cellGalerkinConstant N 1).val = cellH1One := by
    apply TorusHk.ext_value
    exact (cellGalerkinConstant_value N 1).trans cellH1One_value.symm
  have hz : z.val = u.val - cellH1One := congrArg (fun U : TorusHk 1 ℂ => u.val - U) hc1
  have hp := cellTransverseGalerkinOperator_test_pairing N a b η G hG hv ξ hc A hA hb κ
    Cw hCw hw t ht u z
  have hd := cellZeroDrift_correction_dual G hG (fun j => (Real.sqrt η : ℂ) * ξ j) κ t u.val s
  have hs := congrArg (fun d : TorusHk 1 ℂ => inner ℝ d z.val) hd
  have hback := congrArg (fun U : TorusHk 1 ℂ =>
    inner ℝ (cellDualDerivative ⟨fun t _ => G t, 0, fun j => (Real.sqrt η : ℂ) * ξ j, κ⟩
      hG 0 measurable_const (by intro t x; simp) t U
      (s + cellScalarCLM (κ t - ∑ j : Fin 2, ∑ l : Fin 2,
        (G t j l : ℂ) * ((Real.sqrt η : ℂ) * ξ j) * ((Real.sqrt η : ℂ) * ξ l)) (cellConstantCLM 1)) 0)
      z.val) hz
  exact hp.trans (hs.trans (hback.symm.trans (cellDualDerivative_pairing
    ⟨fun t _ => G t, 0, fun j => (Real.sqrt η : ℂ) * ξ j, κ⟩ hG 0 measurable_const
      (by intro t x; simp) t z.val z.val _ 0)))

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal Classical
namespace AVRegularity.CycleWords

/-! The preceding response level produces the exact metric forcing, including
the zero insertion at level zero, with a uniform metric insertion price. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem metricPreviousResponse_native_flux_exists (Ks Kmax : ℕ)
    (M : ℕ → ℝ) (hM : ∀ r, 0 ≤ M r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K ≤ Kmax, ∀ J : ℕ,
      ∀ (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (a b ϖ ρ δ ζ g : ℝ),
      (∀ X k l, Measurable (fun t => G t X k l)) →
      (∀ t ∈ Set.Icc a b, ∀ k l, ContDiff ℝ (Ks : ℕ) (fun z => G t z k l)) →
      0 < ϖ → 0 < ρ → ρ * ϖ ≤ 1 → 0 ≤ ζ → ζ ≤ 1 → 0 ≤ g → δ = ζ * ϖ →
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ r, 1 ≤ r → r ≤ Ks → ∀ k l,
        ‖iteratedFDeriv ℝ r (fun z => G t z k l) 0‖ ≤ M r * g * δ ^ r) →
      ∀ (j : Fin (J + 1)) (n : ℕ) (U : Fin (J + 1) → ℝ → PlaneHk Set.univ (K + 1) E),
      (∀ j', MemLp (U j') 2 (volume.restrict (Set.Icc a b))) →
      (∀ j', j.val = j'.val + 1 →
        (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (n + Ks) ϖ 0 ρ K (U j' t)) ≠ ⊤) →
      ∃ V : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)),
        MemLp V 2 (volume.restrict (Set.Icc a b)) ∧
        (∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 ρ K (V t)) ≠ ⊤ ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V t) =ᵐ[volume] (fun z =>
          ∑ j' : Fin (J + 1), if j.val = j'.val + 1 then
            WithLp.toLp 2 (fun k : Fin 2 => ∑ l : Fin 2, metricTaylor 1 Ks G t 0 z k l •
              (U j' t).toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => l⟩ z) else 0)) ∧
        (∀ m, (∫⁻ t in Set.Icc a b, weightedFactorialNormSq m ϖ 0 ρ K (V t)) ≤
          ENNReal.ofReal ((4 * Real.sqrt (multiplicationDensityBudget K) * (C * g * ζ)) ^ 2) *
            ∑ j' : Fin (J + 1), if j.val = j'.val + 1 then
              (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (m + Ks) ϖ 0 ρ K (U j' t)) else 0) := by
  classical
  obtain ⟨C, hC, hmatrix⟩ := metricTaylorMatrix_native_flux_exists (E := E) Ks Kmax M hM
  refine ⟨C, hC, ?_⟩
  intro K hK J G a b ϖ ρ δ ζ g hm hf hϖ hρ hscale hζ hζ1 hg hδ hjet j n U hU he
  by_cases hj : j.val = 0
  · refine ⟨fun _ => 0, Weighted.planeHk_zero_time_memLp K (volume.restrict (Set.Icc a b)), ?_, ?_, ?_⟩
    · simp only [Weighted.weightedFactorialNormSq_zero_carrier, lintegral_zero]
      exact ENNReal.zero_ne_top
    · exact Filter.Eventually.of_forall (fun t => by
        simpa only [responsePreviousLevel_sum_zero j hj] using
          (planeValue_zero_ae (E := PiLp 2 (fun _ : Fin 2 => E)) K))
    · intro m
      simp only [Weighted.weightedFactorialNormSq_zero_carrier, lintegral_zero, zero_le]
  · let jp : Fin (J + 1) := ⟨j.val - 1, by have hh := j.isLt; omega⟩
    have hp : j.val = jp.val + 1 := by dsimp [jp]; omega
    obtain ⟨V, hV, hVe, hv, hdens⟩ := hmatrix K hK G a b ϖ ρ δ ζ g hm hf hϖ hρ
      hscale hζ hζ1 hg hδ hjet n (U jp) (hU jp) (he jp hp)
    refine ⟨V, hV, hVe, ?_, ?_⟩
    · filter_upwards [hv] with t ht
      filter_upwards [ht] with z hz
      rw [responsePreviousLevel_sum_eq j hj]
      have hh := metricCoordinateFlux_eq_stored
        (fun k l => taylorSlow 1 Ks (fun y => G t y k l) 0 z) (U jp t) z
      exact hz.trans (by simpa only [metricTaylor, sub_zero, jp] using hh)
    · intro m
      rw [responsePreviousLevel_sum_eq j hj]
      exact nativeFlux_time_moment_shift_budget m Ks ϖ ρ
        (4 * Real.sqrt (multiplicationDensityBudget K) * (C * g * ζ))
        (volume.restrict (Set.Icc a b)) V (U jp) hdens
end

/-! The preceding response level produces the exact metric forcing, including
the zero insertion at level zero, with a uniform metric insertion price. -/

theorem metricPreviousResponse_native_flux_exists_uniform (Ks Kmax : ℕ)
    (M : ℕ → ℝ) (hM : ∀ r, 0 ≤ M r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E], ∀ K ≤ Kmax, ∀ J : ℕ,
      ∀ (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (a b ϖ ρ δ ζ g : ℝ),
      (∀ X k l, Measurable (fun t => G t X k l)) →
      (∀ t ∈ Set.Icc a b, ∀ k l, ContDiff ℝ (Ks : ℕ) (fun z => G t z k l)) →
      0 < ϖ → 0 < ρ → ρ * ϖ ≤ 1 → 0 ≤ ζ → ζ ≤ 1 → 0 ≤ g → δ = ζ * ϖ →
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ r, 1 ≤ r → r ≤ Ks → ∀ k l,
        ‖iteratedFDeriv ℝ r (fun z => G t z k l) 0‖ ≤ M r * g * δ ^ r) →
      ∀ (j : Fin (J + 1)) (n : ℕ) (U : Fin (J + 1) → ℝ → PlaneHk Set.univ (K + 1) E),
      (∀ j', MemLp (U j') 2 (volume.restrict (Set.Icc a b))) →
      (∀ j', j.val = j'.val + 1 →
        (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (n + Ks) ϖ 0 ρ K (U j' t)) ≠ ⊤) →
      ∃ V : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)),
        MemLp V 2 (volume.restrict (Set.Icc a b)) ∧
        (∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 ρ K (V t)) ≠ ⊤ ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V t) =ᵐ[volume] (fun z =>
          ∑ j' : Fin (J + 1), if j.val = j'.val + 1 then
            WithLp.toLp 2 (fun k : Fin 2 => ∑ l : Fin 2, metricTaylor 1 Ks G t 0 z k l •
              (U j' t).toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => l⟩ z) else 0)) ∧
        (∀ m, (∫⁻ t in Set.Icc a b, weightedFactorialNormSq m ϖ 0 ρ K (V t)) ≤
          ENNReal.ofReal ((4 * Real.sqrt (multiplicationDensityBudget K) * (C * g * ζ)) ^ 2) *
            ∑ j' : Fin (J + 1), if j.val = j'.val + 1 then
              (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (m + Ks) ϖ 0 ρ K (U j' t)) else 0) := by
  classical
  obtain ⟨C, hC, hmatrix⟩ := metricTaylorMatrix_native_flux_exists_uniform Ks Kmax M hM
  refine ⟨C, hC, ?_⟩
  intro E _ _ _ _ _ _ K hK J G a b ϖ ρ δ ζ g hm hf hϖ hρ hscale hζ hζ1 hg hδ hjet j n U hU he
  by_cases hj : j.val = 0
  · refine ⟨fun _ => 0, Weighted.planeHk_zero_time_memLp K (volume.restrict (Set.Icc a b)), ?_, ?_, ?_⟩
    · simp only [Weighted.weightedFactorialNormSq_zero_carrier, lintegral_zero]
      exact ENNReal.zero_ne_top
    · exact Filter.Eventually.of_forall (fun t => by
        simpa only [responsePreviousLevel_sum_zero j hj] using
          (planeValue_zero_ae (E := PiLp 2 (fun _ : Fin 2 => E)) K))
    · intro m
      simp only [Weighted.weightedFactorialNormSq_zero_carrier, lintegral_zero, zero_le]
  · let jp : Fin (J + 1) := ⟨j.val - 1, by have hh := j.isLt; omega⟩
    have hp : j.val = jp.val + 1 := by dsimp [jp]; omega
    obtain ⟨V, hV, hVe, hv, hdens⟩ := hmatrix K hK G a b ϖ ρ δ ζ g hm hf hϖ hρ
      hscale hζ hζ1 hg hδ hjet n (U jp) (hU jp) (he jp hp)
    refine ⟨V, hV, hVe, ?_, ?_⟩
    · filter_upwards [hv] with t ht
      filter_upwards [ht] with z hz
      rw [responsePreviousLevel_sum_eq j hj]
      have hh := metricCoordinateFlux_eq_stored
        (fun k l => taylorSlow 1 Ks (fun y => G t y k l) 0 z) (U jp t) z
      exact hz.trans (by simpa only [metricTaylor, sub_zero, jp] using hh)
    · intro m
      rw [responsePreviousLevel_sum_eq j hj]
      exact nativeFlux_time_moment_shift_budget m Ks ϖ ρ
        (4 * Real.sqrt (multiplicationDensityBudget K) * (C * g * ζ))
        (volume.restrict (Set.Icc a b)) V (U jp) hdens

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! The actual reciprocal normalization differs from one by a quadratic frequency price. -/

theorem canonicalNormalization_correction_norm_le (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16) (t : ℝ) :
    ‖fibreSeriesC (fibreAdjointNormalizationCoefficients η Cw hη G hG hv hw) ξ t - 1‖ ≤
      2 * (fibreNorm ξ / fibreCoefficientMajorantRadius Cw) ^ 2 := by
  let R := fibreCoefficientMajorantRadius Cw
  let d := fibreAdjointOverlapCoefficients η Cw hη G hG hv hw
  let k := fibreAdjointNormalizationCoefficients η Cw hη G hG hv hw
  have hR : 0 < R := fibreCoefficientMajorantRadius_pos hCw
  have hξR : fibreNorm ξ ≤ R := hξ.trans (by dsimp only [R]; linarith)
  have hD := fibreAdjointOverlapCoefficients_weighted_le η Cw hη hCw G hG hv hw
    (fibreNorm_nonneg ξ) hξR
  have hd : ‖fibreSeriesC d ξ t‖ ≤ (fibreNorm ξ / R) ^ 2 := by
    have he := (enorm_tsum_le_tsum_enorm (f := fun p => fibreMonomial ξ p * d p t)).trans
      ((fibreScalarSeries_enorm_sum_le d (fibreNorm ξ) ξ le_rfl t).trans hD)
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (div_nonneg (fibreNorm_nonneg ξ) hR.le)] at he
    exact (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp he
  have he := fibreAdjointNormalizationCoefficients_series_mul η Cw hη hCw G hG hv hw ξ hξ t
  have hid : fibreSeriesC k ξ t - 1 = -(fibreSeriesC d ξ t * fibreSeriesC k ξ t) := by
    calc
      _ = fibreSeriesC k ξ t - (1 + fibreSeriesC d ξ t) * fibreSeriesC k ξ t := by rw [he]
      _ = _ := by ring
  rw [hid, norm_neg, norm_mul]
  have hk := fibreAdjointNormalization_series_norm_le_two η Cw hη hCw G hG hv hw ξ hξ t
  exact (mul_le_mul hd hk (norm_nonneg _) (sq_nonneg _)).trans_eq (mul_comm _ _)

theorem canonicalNormalization_correction_linear_le (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16) (t : ℝ) :
    ‖fibreSeriesC (fibreAdjointNormalizationCoefficients η Cw hη G hG hv hw) ξ t - 1‖ ≤
      (2 / fibreCoefficientMajorantRadius Cw) * fibreNorm ξ := by
  have hR := fibreCoefficientMajorantRadius_pos hCw
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := hξ.trans (by linarith)
  have hr0 : 0 ≤ fibreNorm ξ / fibreCoefficientMajorantRadius Cw :=
    div_nonneg (fibreNorm_nonneg ξ) hR.le
  have hr1 : fibreNorm ξ / fibreCoefficientMajorantRadius Cw ≤ 1 := (div_le_one hR).mpr hξR
  have hs : (fibreNorm ξ / fibreCoefficientMajorantRadius Cw) ^ 2 ≤
      fibreNorm ξ / fibreCoefficientMajorantRadius Cw := by
    simpa only [pow_two, one_mul] using mul_le_mul_of_nonneg_right hr1 hr0
  calc
    _ ≤ 2 * (fibreNorm ξ / fibreCoefficientMajorantRadius Cw) ^ 2 :=
      canonicalNormalization_correction_norm_le η Cw hη hCw G hG hv hw ξ hξ t
    _ ≤ 2 * (fibreNorm ξ / fibreCoefficientMajorantRadius Cw) :=
      mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = _ := by ring

end AVRegularity.CycleWords
end

section
open MeasureTheory Set Homogenization AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Actual homogeneous cell energy solutions as a native L2 frequency field. -/

theorem planeBlochHomogeneousFamily_memLp {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (f : Lp ComplexCellL2 2 centeredPlaneFrequencyMeasure) :
    MemLp (fun θ => planeBlochEnergyFamily hab G hG v V hv hb
      (f θ, 0, 0) (planePhysicalBlochShift θ)) 2 centeredPlaneFrequencyMeasure := by
  have hd := (cellHomogeneousDatumCLM a b).comp_memLp' (Lp.memLp f)
  exact planeBlochEnergyFamily_memLp centeredPlaneFrequencyMeasure hab G hG v V hv hb
    (fun θ => cellHomogeneousDatumCLM a b (f θ)) hd planePhysicalBlochShift
    planePhysicalBlochShift_continuous.measurable (2 * (2 * Real.pi) ^ 2)
    centeredPlanePhysicalBlochShift_bound

def planeBlochEnergyField {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (f : Lp ComplexCellL2 2 centeredPlaneFrequencyMeasure) :
    Lp (CellEnergySpace a b) 2 centeredPlaneFrequencyMeasure :=
  (planeBlochHomogeneousFamily_memLp hab G hG v V hv hb f).toLp
    (fun θ => planeBlochEnergyFamily hab G hG v V hv hb
      (f θ, 0, 0) (planePhysicalBlochShift θ))

theorem planeBlochEnergyField_ae {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (f : Lp ComplexCellL2 2 centeredPlaneFrequencyMeasure) :
    ∀ᵐ θ ∂centeredPlaneFrequencyMeasure,
      planeBlochEnergyField hab G hG v V hv hb f θ =
        planeBlochEnergyFamily hab G hG v V hv hb (f θ, 0, 0) (planePhysicalBlochShift θ) :=
  (planeBlochHomogeneousFamily_memLp hab G hG v V hv hb f).coeFn_toLp

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Literal native metric insertions with their integrated moment bounds. -/

theorem metricTaylor_native_insertion_exists_uniform (Ks Kmax : ℕ)
    (M : ℕ → ℝ) (hM : ∀ r, 0 ≤ M r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E], ∀ K ≤ Kmax,
      ∀ (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (a b ϖ ρ δ ζ g : ℝ),
      (∀ X k l, Measurable (fun t => G t X k l)) →
      (∀ t ∈ Set.Icc a b, ∀ k l, ContDiff ℝ (Ks : ℕ) (fun z => G t z k l)) →
      0 < ϖ → 0 < ρ → ρ * ϖ ≤ 1 → 0 ≤ ζ → ζ ≤ 1 → 0 ≤ g → δ = ζ * ϖ →
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ r, 1 ≤ r → r ≤ Ks → ∀ k l,
        ‖iteratedFDeriv ℝ r (fun z => G t z k l) 0‖ ≤ M r * g * δ ^ r) →
      ∀ (n : ℕ) (U : ℝ → PlaneHk Set.univ (K + 1) E),
      MemLp U 2 (volume.restrict (Set.Icc a b)) →
      (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (n + Ks) ϖ 0 ρ K (U t)) ≠ ⊤ →
      ∃ V : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)),
        MemLp V 2 (volume.restrict (Set.Icc a b)) ∧
        (∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 ρ K (V t)) ≠ ⊤ ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V t) =ᵐ[volume]
          (fun z => nativeMetricInsertionFlux (metricTaylor 1 Ks G t 0 z) (U t) z)) ∧
        (∀ m, (∫⁻ t in Set.Icc a b, weightedFactorialNormSq m ϖ 0 ρ K (V t)) ≤
          ENNReal.ofReal ((4 * Real.sqrt (multiplicationDensityBudget K) * (C * g * ζ)) ^ 2) *
            (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (m + (Ks)) ϖ 0 ρ K (U t))) := by
  obtain ⟨C, hC, hmatrix⟩ := metricTaylorMatrix_native_flux_exists_uniform Ks Kmax M hM
  refine ⟨C, hC, ?_⟩
  intro E _ _ _ _ _ _ K hK G a b ϖ ρ δ ζ g hm hf hϖ hρ hscale hζ hζ1 hg hδ hjet n U hU he
  obtain ⟨V, hV, hVe, hv, hdens⟩ := hmatrix K hK G a b ϖ ρ δ ζ g hm hf hϖ hρ hscale hζ hζ1 hg hδ hjet n U hU he
  refine ⟨V, hV, hVe, ?_, ?_⟩
  · filter_upwards [hv] with t ht
    filter_upwards [ht] with z hz
    have hh := metricCoordinateFlux_eq_stored
      (fun k l => taylorSlow 1 Ks (fun y => G t y k l) 0 z) (U t) z
    exact hz.trans (by simpa only [nativeMetricInsertionFlux, Matrix.sub_apply, metricTaylor, sub_zero] using hh)
  · intro m
    exact nativeFlux_time_moment_shift_budget m (Ks) ϖ ρ
      (4 * Real.sqrt (multiplicationDensityBudget K) * (C * g * ζ))
      (volume.restrict (Set.Icc a b)) V U hdens

end AVRegularity.CycleWords
end

section
open MeasureTheory Set Homogenization AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The frequency energy field has exactly its prescribed initial L2 class. -/

theorem planeBlochEnergyFamily_initial {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (f : ComplexCellL2) (ζ : Fin 2 → ℂ) :
    (planeBlochEnergyFamily hab G hG v V hv hb (f, 0, 0) ζ).val.1 ⟨a, le_rfl, hab⟩ = f := by
  obtain ⟨u, slice, hu, hi, ht⟩ :=
    planeBlochEnergyFamily_solves hab G hG v V hv hb (f, 0, 0) ζ
  exact (ht ⟨a, le_rfl, hab⟩).trans hi

theorem planeBlochEnergyField_initial {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (f : Lp ComplexCellL2 2 centeredPlaneFrequencyMeasure) :
    (cellEnergyTraceAtCLM a b ⟨a, le_rfl, hab⟩).compLp
      (planeBlochEnergyField hab G hG v V hv hb f) = f := by
  apply Lp.ext
  filter_upwards [(cellEnergyTraceAtCLM a b ⟨a, le_rfl, hab⟩).coeFn_compLp
    (planeBlochEnergyField hab G hG v V hv hb f),
    planeBlochEnergyField_ae hab G hG v V hv hb f] with θ ht hθ
  rw [ht, hθ, cellEnergyTraceAtCLM_apply]
  exact planeBlochEnergyFamily_initial hab G hG v V hv hb (f θ) (planePhysicalBlochShift θ)

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Almost every native frequency carrier is the actual cell equation solution. -/

theorem planeBlochEnergyField_solves_ae {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (f : Lp ComplexCellL2 2 centeredPlaneFrequencyMeasure) :
    ∀ᵐ θ ∂centeredPlaneFrequencyMeasure,
      IsCellFiniteEnergyEvolution ⟨fun t _ => G t, v, planePhysicalBlochShift θ, 0⟩
        hG V hv hb (f θ, 0, 0) (planeBlochEnergyField hab G hG v V hv hb f θ) := by
  filter_upwards [planeBlochEnergyField_ae hab G hG v V hv hb f] with θ hθ
  rw [hθ]
  exact planeBlochEnergyFamily_solves hab G hG v V hv hb _ _

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Uniform metric insertion prices in the inverse-mass forcing budget. -/

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)]
  [∀ i, CompleteSpace (E i)] [∀ i, FiniteDimensional ℝ (E i)]

theorem nativeMetric_mass_budget (K : ι → ℕ) (Kmax : ℕ) (hK : ∀ v, K v ≤ Kmax)
    (α : ι → ℝ≥0∞) (n p : ℕ) (ϖ ρ C g ζ : ℝ)
    (hC : 0 ≤ C) (hg : 0 ≤ g) (hζ : 0 ≤ ζ) (μ : Measure ℝ)
    (V : ∀ v, ℝ → PlaneHk Set.univ (K v) (PiLp 2 (fun _ : Fin 2 => E v)))
    (U : ∀ v, ℝ → PlaneHk Set.univ (K v + 1) (E v))
    (hU : ∀ v, MemLp (U v) 2 μ)
    (hb : ∀ v, (∫⁻ t, weightedFactorialNormSq n ϖ 0 ρ (K v) (V v t) ∂μ) ≤
      ENNReal.ofReal ((4 * Real.sqrt (multiplicationDensityBudget (K v)) * (C * g * ζ)) ^ 2) *
        ∫⁻ t, weightedGradFactorialNormSq (n + p) ϖ 0 ρ (K v) (U v t) ∂μ) :
    (∑ v, α v * ∫⁻ t, weightedFactorialNormSq n ϖ 0 ρ (K v) (V v t) ∂μ) ≤
      ENNReal.ofReal ((metricInsertionUniformPrice Kmax C) ^ 2 * (g * ζ) ^ 2) *
        ∫⁻ t, (∑ v, α v * weightedGradFactorialNormSq (n + p) ϖ 0 ρ (K v) (U v t)) ∂μ := by
  classical
  rw [weightedNativeGradMass_time_sum K α (n + p) ϖ 0 ρ μ U hU, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  have hc := ENNReal.ofReal_le_ofReal (metricInsertion_price_le (hK v) C g ζ hC hg hζ)
  have hh := (hb v).trans (mul_le_mul' hc le_rfl)
  simpa only [mul_assoc, mul_comm (α v), mul_left_comm (α v)] using mul_le_mul_right hh (α v)

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleWords

/-! The full higher constructed generator reads out the original variational cell equation. -/

 theorem interiorPulseHigherFullGeneratorCLM_pairing (K : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (ν : ℝ) (y₀ : Vec 2) {k : ℤ} (hk : Odd k) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ k))
    (V : ℝ) (hb : ∀ t x, ∑ j, interiorSinglePulseDrift α q Λ ζ m ν y₀ k t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) (U : TorusHk (K + 2) ℂ) (z : TorusHk 1 ℂ) :
    inner ℝ (torusHkValueCLM (interiorPulseHigherFullGeneratorCLM K hΛ hζ ν y₀ hk hv G θ κ t U))
      (torusHkValueCLM z) =
    cellGeneratorForm ⟨fun t _ => G t, interiorSinglePulseDrift α q Λ ζ m ν y₀ k, θ, κ⟩ hG V hv.1 hb t
      (cellH2BaseCLM (truncateTorusHk (by omega : 2 ≤ K + 2) U)) z := by
  let C : CellCoefficients := ⟨fun t _ => G t, interiorSinglePulseDrift α q Λ ζ m ν y₀ k, θ, κ⟩
  let u := truncateTorusHk (by omega : 2 ≤ K + 2) U
  have hd : cellDiffusionForm C hG t (cellH2BaseCLM u) z =
      inner ℝ (cellConstantMetricStrongDiffusionCLM G θ t u) (torusHkValueCLM z) := by
    have he := congrArg Complex.re (cellConstantMetricStrongDiffusionCLM_pair G hG θ t u z)
    rw [cellComplexDiffusionForm_real_part C hG, cellComplexPair_re] at he
    exact he
  simp only [interiorPulseHigherFullGeneratorCLM, add_apply, sub_apply, ContinuousLinearMap.comp_apply,
    map_add, map_sub, torusHigherStrongDiffusionCLM_value,
    interiorPulseHigherAdvectionCLM_value K hΛ hζ ν y₀ hk hv V hb,
    torusHigherScalarCLM_value, inner_add_left, inner_sub_left, Fin.sum_univ_two]
  change _ = cellGeneratorForm C hG V hv.1 hb t (cellH2BaseCLM u) z
  simp only [cellGeneratorForm, add_apply, sub_apply, Fin.sum_univ_two,
    pullbackInnerCLM_apply, ContinuousLinearMap.comp_apply]
  rw [hd]
  rfl

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The committed full finite cell system has the actual full higher generator as its readout. -/

theorem torusHigherProjection_inner (K N : ℕ) (u z : TorusHk K ℂ) :
    inner ℝ (galerkinProj N u) z = inner ℝ u (galerkinProj N z) := by
  rw [torusHigher_inner_eq_sum, torusHigher_inner_eq_sum]
  simp only [galerkinProj_val, cellJetFourierProjection_apply]
  exact Finset.sum_congr rfl (fun _ _ => cellVectorFourierProjection_inner N _ _)

theorem torusHigherProjection_retained_inner (K N : ℕ) (u z : TorusHk K ℂ)
    (hz : galerkinProj N z = z) :
    inner ℝ (galerkinProj N u) z = inner ℝ u z := by
  rw [torusHigherProjection_inner, hz]

theorem constructedFullGalerkinOperator_higher_readout (K N : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (ν : ℝ) (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (V : ℝ) (hb : ∀ t x, ∑ j, ocCellDrift α q Λ ζ m ν y₀ t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) (u : CellGalerkinSpace (E := ℂ) N) :
    cellGalerkinOperator N (cellGeneratorB
      ⟨fun t _ => G t, ocCellDrift α q Λ ζ m ν y₀, θ, κ⟩ hG V hv.1 hb t) u =
    cellGalerkinL2Initial N (torusHkValueCLM
      (constructedHigherFullGeneratorCLM K hΛ hζ ν y₀ hv G θ κ t
        (rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 2) N u))) := by
  apply cellGalerkinMass_injective N
  apply LinearMap.ext
  intro z
  change inner ℝ (cellGalerkinValue N (cellGalerkinOperator N _ u)) (cellGalerkinValue N z) =
    inner ℝ (cellGalerkinValue N (cellGalerkinL2Initial N _)) (cellGalerkinValue N z)
  rw [cellGalerkinOperator_pairing, cellGalerkinL2Initial_pairing]
  change cellGeneratorForm
      ⟨fun t _ => G t, ocCellDrift α q Λ ζ m ν y₀, θ, κ⟩ hG V hv.1 hb t u.val z.val =
    inner ℝ (torusHkValueCLM
      (constructedHigherFullGeneratorCLM K hΛ hζ ν y₀ hv G θ κ t
        (rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 2) N u))) (torusHkValueCLM z.val)
  rw [constructedHigherFullGeneratorCLM_pairing K hΛ hζ ν y₀ hv V hb G hG θ κ t _ z.val]
  have he := rangeSmoothFourierLift_truncate (by omega : 1 ≤ K + 2) N u
  have hbase : cellH2BaseCLM (truncateTorusHk (by omega : 2 ≤ K + 2)
      (rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 2) N u)) = u.val := by
    exact he
  rw [hbase]

theorem constructedFullGalerkinOperator_higher_lift {K : ℕ} (hK : 1 ≤ K) (N : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (ν : ℝ) (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (V : ℝ) (hb : ∀ t x, ∑ j, ocCellDrift α q Λ ζ m ν y₀ t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) (u : CellGalerkinSpace (E := ℂ) N) :
    rangeSmoothFourierLiftCLM hK N
      (cellGalerkinOperator N (cellGeneratorB
        ⟨fun t _ => G t, ocCellDrift α q Λ ζ m ν y₀, θ, κ⟩ hG V hv.1 hb t) u) =
    galerkinProj N (constructedHigherFullGeneratorCLM K hΛ hζ ν y₀ hv G θ κ t
      (rangeSmoothFourierLiftCLM (by omega : 1 ≤ K + 2) N u)) := by
  rw [constructedFullGalerkinOperator_higher_readout K N hΛ hζ ν y₀ hv V hb G hG θ κ t u,
    cellGalerkinL2Initial_higher_lift]

end AVRegularity.CycleWords
end

section
open MeasureTheory Set Homogenization AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Transposed native H1 states agree with the original trace as frequency L2 classes. -/

local instance cellEnergyTimeFrequencyTraceCellMeasurable : MeasurableSpace ComplexCellL2 :=
  borel ComplexCellL2

local instance cellEnergyTimeFrequencyTraceCellBorel : BorelSpace ComplexCellL2 := ⟨rfl⟩

local instance cellEnergyTimeFrequencyTraceCellCountable : SecondCountableTopology ComplexCellL2 :=
  AVRegularity.CoupledEnergy.Variational.cellL2SecondCountableTopology

theorem cellEnergyJointH1_trace_timeSlices {a b : ℝ} (hab : a ≤ b)
    (F : Lp (CellEnergySpace a b) 2 centeredPlaneFrequencyMeasure) :
    ∀ᵐ t ∂volume.restrict (Icc a b), ∀ᵐ θ ∂centeredPlaneFrequencyMeasure,
      cellComplexH1ValueCLM (cellEnergyJointH1 hab F (θ, t)) =
        cellEnergySpaceTrace hab (F θ) t := by
  have hj : StronglyMeasurable (fun p : Vec 2 × ℝ =>
      cellComplexH1ValueCLM (cellEnergyJointH1 hab F p)) :=
    cellComplexH1ValueCLM.continuous.comp_stronglyMeasurable (Lp.stronglyMeasurable _)
  have ht := cellEnergyJointTrace_stronglyMeasurable hab F (Lp.stronglyMeasurable F)
  exact (Measure.ae_ae_comm (hj.measurableSet_eq_fun ht)).mp
    (cellEnergyJointH1_trace_slices hab F)

theorem cellEnergyTimeFrequencyState_value {a b : ℝ} (hab : a ≤ b)
    (F : Lp (CellEnergySpace a b) 2 centeredPlaneFrequencyMeasure) :
    ∀ᵐ t ∂volume.restrict (Icc a b),
      centeredCellBlochValueField (cellEnergyTimeFrequencyState hab F t) =
        (cellEnergyTraceAtCLM a b (projIcc a b hab t)).compLp F := by
  filter_upwards [cellEnergyJointH1_trace_timeSlices hab F,
    cellEnergyTimeFrequencyState_slices hab F] with t ht hs
  apply Lp.ext
  have hv := cellComplexH1ValueCLM.coeFn_compLp (cellEnergyTimeFrequencyState hab F t)
  have he := (cellEnergyTraceAtCLM a b (projIcc a b hab t)).coeFn_compLp F
  filter_upwards [ht, hs, hv, he] with θ htθ hsθ hvθ heθ
  change cellComplexH1ValueCLM.compLp (cellEnergyTimeFrequencyState hab F t) θ = _
  rw [hvθ, hsθ]
  exact htθ.trans heθ.symm

end AVRegularity.CycleWords
end

section
open Set Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! Every actual scalar chain gives a weak time curve for each stored derivative word. -/

open AVRegularity.Weighted

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem constantMetric_scalarChain_words_clipped_source_integral_budgets
    (a b : ℝ) (hab : a ≤ b) (κ : Fin 1 → ι → ℕ) (Kmax : ℕ)
    (hκ : ∀ i : Fin 1 × ι, κ i.1 i.2 ≤ Kmax)
    (v : ℝ → Vec 2 → Vec 2)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hV : 0 ≤ V) (ha : 0 ≤ strain) (hB : 1 ≤ B) (hlam : 0 < lam)
    (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hGm : Measurable (fun p : Set.Icc a b × Vec 2 => G p.1 p.2))
    (hG : ∀ i : Fin 1 × ι, ∀ t ∈ Set.Icc a b, ∀ k j,
      ContDiff ℝ (κ i.1 i.2 : ℕ) (fun x => G t x k j))
    (M : ∀ i : Fin 1 × ι, Fin (κ i.1 i.2 + 1) → ℝ)
    (hb : ∀ i, ∀ t ∈ Set.Icc a b, ∀ (l : Fin (κ i.1 i.2 + 1)) x k j,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k j) x‖ ≤ M i l)
    (hCell : IsCellMetric G)
    (hconstant : ∀ t x, G t x = G t 0)
    (f : ∀ i : Fin 1 × ι, PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (F : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (PiLp 2 (fun _ : Fin 2 => h i.2)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (u : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (w : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2 + 1) (h i.2))
    (hsln : IsCoupledWeakSolutionPlane 1 a b v 2 (fun i : Fin 1 × ι => κ i.1 i.2)
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ) f F
      (fun _ _ => 0) u w) (i : Fin 1 × ι)
    (hG1 : ∀ t ∈ Set.Icc a b, ∀ k j, ContDiff ℝ 1 (fun x => G t x k j))
    (t₀ S ϖ : ℝ) (zc : Vec 2) (N m : ℕ) (Cw : ℕ → ℝ)
    (C : ChartWeights G v t₀ S ϖ zc N Cw) (hm : m ≤ N)
    (clip ρ : ℝ) (hclip : 0 < clip)
    (hρ : 0 < ρ) (ν : ℝ) (hν : 0 < ν) (hsmall : B * ρ / lam ≤ 1 / 2)
    (hstrainSmall : strain * B * ρ ^ 2 ≤ ν / 8)
 :
    let H := scalarSobolevTransportSource (hκ i) hab v hv V strain B lam hbv hjets (w i)
    let Q := scalarSobolevMetricSource hab G (hG i) (M i) (hb i) (w i) (F i)
    let T := planeIntervalTransport (E := h i.2) a b hab v (fun t ht => (hv t ht).continuous) V hbv
    let D := cellMetricIntervalDiffusion (E := h i.2) a b hab G
      (fun t ht k j => (hG1 t ht k j).continuous) hCell
    let R := fun (α : JetIndex2 (κ i.1 i.2)) t => planeJetReadoutOperator (κ i.1 i.2) α (H t) +
      T t (planeH1GradientOperator (planeWordH1SliceOperator (κ i.1 i.2) α (w i t)))
    let L := fun (α : JetIndex2 (κ i.1 i.2)) t => planeJetFluxOperator (κ i.1 i.2) α (Q t) -
      D t (planeH1GradientOperator (planeWordH1SliceOperator (κ i.1 i.2) α (w i t)))
    let q := fun t x => clipWeight clip (C.W m t x)
    let d := fun t => rawWeightedGradientEnergy ρ (q t) (w i t).toFunction.jet
    let fenergy := fun t => rawWeightedFactorialEnergy ρ (q t) (F i t).toFunction.jet
    ((∫ t in a..b, ∑ α : JetIndex2 (κ i.1 i.2), factorialWeight ρ α.1.val *
      (∫ x, q t x * (‖R α t x‖ * ‖planeJetReadoutOperator (κ i.1 i.2) α (u i t) x‖))) ≤
      (ν / 4) * (∫ t in a..b, d t)) ∧
    ((∫ t in a..b, ∑ α : JetIndex2 (κ i.1 i.2), factorialWeight ρ α.1.val *
      (∫ x, q t x * ‖(WithLp.toLp 2 (fun k : Fin 2 => L α t k x) :
        PiLp 2 (fun _ : Fin 2 => h i.2))‖ ^ 2)) ≤
      (∫ t in a..b, fenergy t)) := by
  dsimp only
  have hH := scalarSobolevTransportSource_memLp (hκ i) hab v hvm hv V strain B lam
    hV ha (le_trans (by norm_num) hB) hlam hbv hjets (w i) (hsln.2.1 i)
  have hQ := scalarSobolevMetricSource_memLp hab G hGm (hG i) (M i) (hb i)
    (w i) (F i) (hsln.2.1 i) (hF i)
  have hcv α := cellMetric_scalarChain_ordered_planeWeakHilbertCurve a b hab κ Kmax hκ v hvm hv
    V strain B lam hV ha (le_trans (by norm_num) hB) hlam hbv hjets G hGm hG M hb hCell f F hF u w hsln i α
  have hint α := cellMetric_storedWord_residual_time_integrable a b hab v
    (fun t ht => (hv t ht).of_le (by simp)) hvm V hbv G hG1 hGm hCell
    t₀ S ϖ zc N m Cw C hm (u i) _ (w i) _ hH hQ hcv clip hclip α
  have hRint := intervalIntegrable_of_integrable_Icc hab
    (integrable_finsetSum (Finset.univ : Finset (JetIndex2 (κ i.1 i.2)))
      (fun α _ => (hint α).2.const_mul (factorialWeight ρ α.1.val)))
  have hLint := intervalIntegrable_of_integrable_Icc hab
    (integrable_finsetSum (Finset.univ : Finset (JetIndex2 (κ i.1 i.2)))
      (fun α _ => (hint α).1.const_mul (factorialWeight ρ α.1.val)))
  have hDint := intervalIntegrable_of_integrable_Icc hab
    (rawWeightedGradient_time_integrable C m hm clip hclip ρ _ (w i) (hsln.2.1 i))
  have hFint := intervalIntegrable_of_integrable_Icc hab
    (rawWeightedFlux_time_integrable C m hm clip hclip ρ _ (F i) (hF i))
  have hpoint := hsln.2.2.1 i
  have hbud := hpoint.and (ae_restrict_mem measurableSet_Icc)
  have hbds := hbud.mono (fun t ht =>
    constantMetric_scalarSobolevSource_word_spatial_budget (hκ i) hab v hv V strain B lam hbv hjets
      G (hG i) (M i) (hb i) hCell hconstant (w i) (F i) t ht.2 hG1 (u i t) ht.1.symm
      ρ (fun x => clipWeight clip (C.W m t x)) hρ ν hν ha hB hlam hV hsmall hstrainSmall
      ((chartWeights_clipped_time_coefficient C m hm clip hclip).1 t)
      (fun x => (clipWeight_pos hclip (C.pos m hm t x)).le) clip
      (fun x => clipWeight_le_bound hclip (C.pos m hm t x)))
  constructor
  · have hi := intervalIntegral.integral_mono_ae_restrict hab hRint (hDint.const_mul (ν / 4))
      (hbds.mono (fun _ ht => ht.1))
    rw [intervalIntegral.integral_const_mul] at hi
    exact hi
  · exact intervalIntegral.integral_mono_ae_restrict hab hLint hFint
      (hbds.mono (fun _ ht => ht.2))

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Metric Taylor remainders produce the literal matrix forcing
with a uniform coefficient constant and a moment shift by the first omitted degree. -/

theorem metricRemainderMatrix_native_flux_exists_uniform (Ks Kmax : ℕ)
    (M : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E], ∀ K ≤ Kmax,
      ∀ (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (a b ϖ ρ ζ g : ℝ),
      (∀ X k l, Measurable (fun t => G t X k l)) →
      (∀ t ∈ Set.Icc a b, ∀ k l, ContDiff ℝ (Ks + 1 + Kmax : ℕ) (fun z => G t z k l)) →
      0 < ϖ → 0 < ρ → ρ * ϖ ≤ 1 → 0 ≤ ζ → ζ ≤ 1 → 0 ≤ g →
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ r, Ks + 1 ≤ r → r ≤ Ks + 1 + Kmax → ∀ y k l,
        ‖iteratedFDeriv ℝ r (fun z => G t z k l) y‖ ≤ M r * g * (ζ * ϖ) ^ r) →
      ∀ (n : ℕ) (U : ℝ → PlaneHk Set.univ (K + 1) E),
      MemLp U 2 (volume.restrict (Set.Icc a b)) →
      (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (n + (Ks + 1)) ϖ 0 ρ K (U t)) ≠ ⊤ →
      ∃ V : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)),
        MemLp V 2 (volume.restrict (Set.Icc a b)) ∧
        (∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 ρ K (V t)) ≠ ⊤ ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V t) =ᵐ[volume] (fun z =>
          ∑ kl : Fin 2 × Fin 2, (G t z kl.1 kl.2 - taylorSlow 0 Ks (fun y => G t y kl.1 kl.2) 0 z) •
            Weighted.fluxCoordinateInjection kl.1 (ContinuousLinearMap.id ℝ E)
              (planeJetOrder (U t) 1 (fun _ => kl.2) z))) ∧
        (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ᵐ z ∂volume,
          planeFactorialDensity ρ (V t) z ≤
            (4 * Real.sqrt (multiplicationDensityBudget K) * (C * g * ζ ^ (Ks + 1))) ^ 2 *
              (polynomialMomentRoot ϖ z ^ (Ks + 1)) ^ 2 * planeGradFactorialDensity ρ (U t) z) := by
  classical
  obtain ⟨C, hC, hcoeff⟩ := metricRemainder_time_coefficient_budget Ks Kmax M
  refine ⟨C, hC, ?_⟩
  intro E _ _ _ _ _ _ K hK G a b ϖ ρ ζ g hm hf hϖ hρ hscale hζ hζ1 hg hjet n U hU he
  let cc := fun k l => metricRemainderTimeCoefficient Ks (fun t z => G t z k l) a b
  have hh (k l : Fin 2) := hcoeff (fun t z => G t z k l) a b ϖ ρ ζ g
    (fun X => hm X k l) (fun t ht => hf t ht k l) hϖ hρ.le hscale hζ hζ1 hg
    (by filter_upwards [hjet] with t ht; exact fun r hr hrK y => ht r hr hrK y k l)
  have hb : ∀ k l, ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j ≤ K, ∀ z,
      ρ ^ j * ‖iteratedFDeriv ℝ j (cc k l t) z‖ ≤
        (C * g * ζ ^ (Ks + 1)) * polynomialMomentRoot ϖ z ^ (Ks + 1) := by
    intro k l
    filter_upwards [(hh k l).2.2] with t ht
    exact fun j hj => ht j (hj.trans hK)
  obtain ⟨V, hV, hVe, hv, hdens⟩ := metricMatrix_native_flux_exists K n (Ks + 1) ϖ ρ hϖ hρ
    (volume.restrict (Set.Icc a b)) cc (fun k l => (hh k l).1)
    (fun k l t => ((hh k l).2.1 t).of_le (by exact_mod_cast hK))
    (C * g * ζ ^ (Ks + 1)) (mul_nonneg (mul_nonneg hC hg) (pow_nonneg hζ _)) hb U hU he
  refine ⟨V, hV, hVe, ?_, hdens⟩
  filter_upwards [hv, ae_restrict_mem measurableSet_Icc] with t ht htI
  simpa only [cc, metricRemainderTimeCoefficient, ite_eq_left htI] using ht

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The finite correction growth bound retains a frequency-square forcing cost. -/

theorem cellTransverseGalerkin_correction_local_growth_energy
    (N : ℕ) (a b η : ℝ) (hab : a ≤ b) (hη0 : 0 ≤ η) (hη : η ≤ 1) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
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
    (initial : CellGalerkinSpace (E := ℂ) N)
    (y : ContinuousMap (Icc a b) (CellGalerkinSpace (E := ℂ) N))
    (hy : AVenhance.Infra.ODE.IsLinearIntegralSolution
      ((Icc a b).indicator (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb κ))
      0 initial a b (AVenhance.Infra.ODE.extendCurve hab y))
    (c d : ℝ) (hcd : c ≤ d) (hsub : Icc c d ⊆ Icc a b) :
    let Y := AVenhance.Infra.ODE.extendCurve hab y
    let z := fun t => Y t - cellGalerkinConstant N 1
    Real.exp (-4 * (d - c)) * ‖cellGalerkinValue N (z d)‖ ^ 2 +
      (∫ t in c..d, Real.exp (-4 * (t - c)) *
        ((3 / 4) * ∑ j, ‖cellDerivativeCLM j (z t).val‖ ^ 2)) ≤
      ‖cellGalerkinValue N (z c)‖ ^ 2 + ∫ t in c..d, Real.exp (-4 * (t - c)) * (2 * (Cw + L + 8) ^ 2 * fibreNorm ξ ^ 2) := by
  let A' := (Icc a b).indicator (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb κ)
  let Y := AVenhance.Infra.ODE.extendCurve hab y
  let z := fun t => Y t - cellGalerkinConstant N 1
  let src := fun t => cellZeroDriftCorrectionSource η Cw hCw G hv hw ξ κ t (cellGalerkinValue N (Y t))
  obtain ⟨M, hM, hAm, hAb⟩ := cellTransverseGalerkin_window_operator_data
    N G hG hv ξ hc A hA hb κ hκm k hκ
  have hh := cellGalerkin_linear_weak_curve hab N (cellGalerkinState (E := ℂ) N)
    A' 0 initial y hy hAm M hM hAb MemLp.zero
  have hglobal := hh.sub (cellWeakHilbert_constant a b (cellGalerkinConstant N 1).val)
  simp only [sub_zero] at hglobal
  have h := hglobal.mono hsub
  apply (h.energy_strongTime hcd).scalar_weighted_bound hcd (-4)
    (fun _ => 2 * (Cw + L + 8) ^ 2 * fibreNorm ξ ^ 2) (fun t => (3 / 4) * ∑ j, ‖cellDerivativeCLM j (z t).val‖ ^ 2)
    (intervalIntegrable_const)
    ((cellTime_gradientSq_intervalIntegrable hcd _ h.state).const_mul (3 / 4))
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t hti
  have ht := hsub hti
  have hg := cellZeroDrift_generator_scalar_source_energy G hG (fun j => (Real.sqrt η : ℂ) * ξ j)
    κ t (z t).val (src t)
  have hc0 := mul_le_mul_of_nonneg_right (hsmall t ht) (sq_nonneg ‖cellGalerkinValue N (z t)‖)
  have he : AVenhance.Infra.ODE.linearRhs A' 0 Y t =
      cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb κ t (Y t) := by
    simp only [AVenhance.Infra.ODE.linearRhs, Pi.zero_apply, add_zero, A', Set.indicator_of_mem ht]
  have hp := cellTransverseGalerkinOperator_correction_pairing N a b η G hG hv ξ hc A hA hb κ
    Cw hCw hw t ht (Y t)
  change inner ℝ (cellGalerkinValue N
    (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb κ t (Y t)))
      (cellGalerkinValue N (z t)) =
    cellGeneratorForm ⟨fun t _ => G t, 0, fun j => (Real.sqrt η : ℂ) * ξ j, κ⟩
      hG 0 measurable_const (by intro t x; simp) t (z t).val (z t).val +
    cellSourceFunctional (fun j => (Real.sqrt η : ℂ) * ξ j) (src t) 0 (z t).val at hp
  change 2 * (cellGeneratorForm ⟨fun t _ => G t, 0, fun j => (Real.sqrt η : ℂ) * ξ j, κ⟩
      hG 0 measurable_const (by intro t x; simp) t (z t).val (z t).val +
    cellSourceFunctional (fun j => (Real.sqrt η : ℂ) * ξ j) (src t) 0 (z t).val) +
      (3 / 4) * ∑ j, ‖cellDerivativeCLM j (z t).val‖ ^ 2 ≤
    (264 * (∑ j, ‖(Real.sqrt η : ℂ) * ξ j‖ ^ 2) + 2 * ‖κ t‖ + 1) *
      ‖cellGalerkinValue N (z t)‖ ^ 2 + ‖src t‖ ^ 2 at hg
  have hadj : inner ℝ (cellPivotDualCLM (torusHkValueCLM
      (cellGalerkinState (E := ℂ) N (AVenhance.Infra.ODE.linearRhs A' 0 Y t)))) (z t).val =
      inner ℝ (cellGalerkinValue N (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb κ t (Y t)))
        (cellGalerkinValue N (z t)) := by
    rw [he]
    exact ContinuousLinearMap.adjoint_inner_left (torusHkValueCLM (E := ℂ) (K := 1)) (z t).val _
  change 2 * inner ℝ (cellPivotDualCLM (torusHkValueCLM
      (cellGalerkinState (E := ℂ) N (AVenhance.Infra.ODE.linearRhs A' 0 Y t)))) (z t).val +
    -4 * ‖cellGalerkinValue N (z t)‖ ^ 2 +
      (3 / 4) * ∑ j, ‖cellDerivativeCLM j (z t).val‖ ^ 2 ≤ 2 * (Cw + L + 8) ^ 2 * fibreNorm ξ ^ 2
  rw [hadj, hp]
  have hf := cellZeroDriftCorrectionSource_normSq_le η Cw hη0 hη hCw G hG hv hw ξ κ t
    (cellGalerkinValue N (Y t)) L hL (hκq t ht) hξ1 hwsmall
  have hvz : cellGalerkinValue N (z t) = cellGalerkinValue N (Y t) - cellConstantCLM 1 := by
    simp only [z, map_sub, cellGalerkinConstant_value]
  have hforce : ‖src t‖ ^ 2 ≤ 2 * ‖cellGalerkinValue N (z t)‖ ^ 2 +
      2 * (Cw + L + 8) ^ 2 * fibreNorm ξ ^ 2 :=
    hf.trans_eq (congrArg (fun U : ComplexCellL2 => 2 * ‖U‖ ^ 2 +
      2 * (Cw + L + 8) ^ 2 * fibreNorm ξ ^ 2) hvz.symm)
  linarith only [hg, hc0, hforce]

end AVRegularity.CycleWords
end
