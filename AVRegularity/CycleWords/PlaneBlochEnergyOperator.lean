-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.CellTransverseStrongSourceMemLp
public import AVRegularity.CycleWords.CellMetricStoredWordResidualTimeIntegrability
public import AVRegularity.CycleWords.CellTransitionLipschitz
import AVRegularity.CycleWords.CellComplexH1Separability
public import AVRegularity.CycleEvolution.CellInverseJetEquationExistence
import AVRegularity.CycleEvolution.CellInverseJetFactorialBound
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleWords

/-! The scalar source obtained by subtracting the actual constant-one mode is explicit. -/

theorem cellZeroDrift_constant_dual
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) :
    cellDualDerivative ⟨fun t _ => G t, 0, θ, κ⟩ hG 0 measurable_const
      (by intro t x; simp) t cellH1One 0 0 =
      cellPivotDualCLM (cellScalarCLM
        (κ t - ∑ j : Fin 2, ∑ k : Fin 2, (G t j k : ℂ) * θ j * θ k) (cellConstantCLM 1)) := by
  let C : CellCoefficients := ⟨fun t _ => G t, 0, θ, κ⟩
  let Q := ∑ j : Fin 2, ∑ k : Fin 2, (G t j k : ℂ) * θ j * θ k
  have hd (z : TorusHk 1 ℂ) : cellDiffusionForm C hG t cellH1One z =
      inner ℝ (cellScalarCLM (-Q) (cellConstantCLM 1)) (torusHkValueCLM z) := by
    have hh := cellConstantMetric_graph_diffusion hG θ t (0 : TorusHk 1 ℂ) z
    have hzero : cellComplexDiffusionForm hG (fun _ => 0) t (0 : TorusHk 1 ℂ) z = 0 := by
      simp only [cellComplexDiffusionForm, map_zero, cellComplexPair_zero_left, Finset.sum_const_zero, neg_zero]
    simp only [zero_add, hzero, map_zero, cellComplexPair_zero_left, Finset.sum_const_zero,
      sub_zero, zero_sub] at hh
    have he := congrArg Complex.re hh
    rw [cellComplexDiffusionForm_real_part C hG] at he
    rw [← cellComplexPair_re, cellComplexPair_scalar_left]
    simpa only [Q, neg_mul, Complex.neg_re] using he
  have hz (j : Fin 2) (w : ComplexCellL2) :
      cellDriftEntryCLM C 0 measurable_const (by intro t x; simp [C]) t j w = 0 := by
    apply Lp.ext
    have hh := cellDriftEntryCLM_ae C 0 measurable_const (by intro t x; simp [C]) t j w
    filter_upwards [hh, Lp.coeFn_zero ℂ 2 (volume.restrict AVenhance.unitCube)] with x hx h0
    rw [hx, h0]
    simp only [C, Pi.zero_apply, Complex.ofReal_zero, zero_mul]
  apply ext_inner_right ℝ
  intro z
  rw [cellDualDerivative_pairing, cellSourceFunctional_scalar_only]
  change cellGeneratorForm C hG 0 measurable_const (by intro t x; simp [C]) t cellH1One z +
    inner ℝ (0 : ComplexCellL2) (torusHkValueCLM z) = _
  simp only [cellGeneratorForm, add_apply, sub_apply, Fin.sum_univ_two,
    pullbackInnerCLM_apply, ContinuousLinearMap.comp_apply, hz, inner_zero_left, add_zero, sub_zero]
  rw [hd, cellH1One_value]
  change _ = inner ℝ ((torusHkValueCLM (E := ℂ) (K := 1)).adjoint _) z
  rw [ContinuousLinearMap.adjoint_inner_left, ← inner_add_left]
  congr 1
  simp only [cellScalarCLM_smul, sub_eq_add_neg, add_smul]
  simp only [C, Q, Fin.sum_univ_two]
  exact add_comm _ _

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Subtracting the constant mode gives an exact identity of the original diffusion duals. -/

theorem cellZeroDrift_correction_dual
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) (u : TorusHk 1 ℂ) (src : ComplexCellL2) :
    cellDualDerivative ⟨fun t _ => G t, 0, θ, κ⟩ hG 0 measurable_const
      (by intro t x; simp) t u src 0 =
    cellDualDerivative ⟨fun t _ => G t, 0, θ, κ⟩ hG 0 measurable_const
      (by intro t x; simp) t (u - cellH1One)
      (src + cellScalarCLM (κ t - ∑ j : Fin 2, ∑ k : Fin 2, (G t j k : ℂ) * θ j * θ k)
        (cellConstantCLM 1)) 0 := by
  let C : CellCoefficients := ⟨fun t _ => G t, 0, θ, κ⟩
  have ha := cellDualDerivative_add C hG 0 measurable_const (by intro t x; simp [C])
    t (u - cellH1One) cellH1One src 0 0 0
  simp only [sub_add_cancel, add_zero] at ha
  rw [cellZeroDrift_constant_dual G hG θ κ t] at ha
  exact ha.trans (cellDualDerivative_add_scalar_source C hG 0 measurable_const
    (by intro t x; simp [C]) t (u - cellH1One) src _).symm

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Genuine higher transport and full generator for a single-pulse extension. -/

 def interiorPulseHigherAdvectionCLM (K : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (ν : ℝ) (y₀ : Vec 2) {k : ℤ} (hk : Odd k) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ k))
    (θ : Fin 2 → ℂ) (t : ℝ) : TorusHk (K + 2) ℂ →L[ℝ] TorusHk K ℂ :=
  ∑ i : Fin 2, (interiorPulseDriftEntryNativeCLM K hΛ hζ ν y₀ hk hv i t).comp
    (torusHigherShiftedFirstCLM K θ i)

 theorem interiorPulseHigherAdvectionCLM_value (K : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (ν : ℝ) (y₀ : Vec 2) {k : ℤ} (hk : Odd k) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ k))
    (V : ℝ) (hb : ∀ t x, ∑ j, interiorSinglePulseDrift α q Λ ζ m ν y₀ k t x j ^ 2 ≤ V ^ 2)
    (θ : Fin 2 → ℂ) (t : ℝ) (U : TorusHk (K + 2) ℂ) :
    torusHkValueCLM (interiorPulseHigherAdvectionCLM K hΛ hζ ν y₀ hk hv θ t U) =
      ∑ i : Fin 2, cellDriftEntryCLM ⟨0, interiorSinglePulseDrift α q Λ ζ m ν y₀ k, 0, 0⟩ V hv.1 hb t i
        (cellShiftedDerivativeCLM θ i
          (cellH2BaseCLM (truncateTorusHk (by omega : 2 ≤ K + 2) U))) := by
  simp only [interiorPulseHigherAdvectionCLM, Fin.sum_univ_two, add_apply,
    ContinuousLinearMap.comp_apply, map_add, interiorPulseDriftEntryNativeCLM_value K hΛ hζ ν y₀ hk hv V hb,
    torusHigherShiftedFirstCLM_value]

 def interiorPulseHigherFullGeneratorCLM (K : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (ν : ℝ) (y₀ : Vec 2) {k : ℤ} (hk : Odd k) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ k))
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (θ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) :
    TorusHk (K + 2) ℂ →L[ℝ] TorusHk K ℂ :=
  torusHigherStrongDiffusionCLM K G θ t - interiorPulseHigherAdvectionCLM K hΛ hζ ν y₀ hk hv θ t +
    (torusHigherScalarCLM K (κ t)).comp (truncateTorusHk (by omega : K ≤ K + 2))

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! The fixed reserve cap is an actual solution of the original chronological word. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

theorem wordChainFrom_capped (hD : 2 ≤ D)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (letters : Fin N → CycleLetter ι h D)
    (κ : Fin (N + 1) → ι → ℕ) (K : ℕ) (d : Fin N → ℕ)
    {π : ι → ℝ} {dom : Set (ℝ × Vec 2)} {J H : ℕ}
    (hL : ∀ j, IsCycleLetter π (letters j) dom J H)
    (hd : ∀ j, (letters j).order = d j)
    (hc : ∀ j x y (o : Finset.Icc 2 D), (letters j).edge x y o ≠ [] →
      κ j.succ x + o.1 ≤ κ j.castSucc y + 2)
    (X0 : Vec 2) (δ a b : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (f : ∀ j x, PlaneHk Set.univ (κ j x) (h x))
    (F : ∀ j x, ℝ → PlaneHk Set.univ (κ j x) (PiLp 2 (fun _ : Fin 2 => h x)))
    (u : ∀ j x, ℝ → PlaneHk Set.univ (κ j x) (h x))
    (w : ∀ j x, ℝ → PlaneHk Set.univ (κ j x + 1) (h x))
    (hs : IsPlaneChainFrom (wordChainData G letters X0 δ) κ a b v f F u w) :
    IsPlaneChainFrom (wordChainData G letters X0 δ) (cappedWordSlots κ K d) a b v
      (fun j x => truncatePlaneHk (cappedWordSlots_le_original κ K d j x) (f j x))
      (fun j x t => truncatePlaneHk (cappedWordSlots_le_original κ K d j x) (F j x t))
      (fun j x t => truncatePlaneHk (cappedWordSlots_le_original κ K d j x) (u j x t))
      (fun j x t => truncatePlaneHk (Nat.succ_le_succ
        (cappedWordSlots_le_original κ K d j x)) (w j x t)) := by
  apply wordChainFrom_truncate hD G letters κ (cappedWordSlots κ K d)
    (cappedWordSlots_le_original κ K d) hc
  · intro j x y o hn
    exact (Finset.mem_filter.mp
      (cappedWordSlots_nonempty_edge_admissible κ K d letters hL hd hc j x y o hn)).2
  · exact hs

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Literal product readouts retain the normalized price and exact polynomial moment shift. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

theorem polynomialProductReadout_energy_le {K : ℕ}
    (U : PlaneHk Set.univ K E) (V : PlaneHk Set.univ K F)
    (C : Vec 2 → E →L[ℝ] F) (ρ A ϖ : ℝ) (hρ : 0 ≤ ρ) (p n : ℕ)
    (hb : ∀ l ≤ K, ∀ w : DerivativeWord2 l, ∀ x,
      ρ ^ l * ‖orderedCoefficientDerivative C l w x‖ ≤ A * polynomialMomentRoot ϖ x ^ p)
    (hr : ∀ a, Weighted.planeJetReadoutOperator K a V =ᵐ[volume]
      multiplicationRawJet C U.toFunction.jet a) :
    weightedFactorialNormSq n ϖ 0 ρ K V ≤
      ENNReal.ofReal (multiplicationDensityBudget K * A ^ 2) *
        weightedFactorialNormSq (n + p) ϖ 0 ρ K U := by
  rw [Weighted.weightedFactorialNormSq_stored_readout,
    Weighted.weightedFactorialNormSq_stored_readout]
  have hW : Continuous (Weighted.planeMomentPolynomial n ϖ 0) := by
    unfold Weighted.planeMomentPolynomial
    fun_prop
  have hh := productReadout_energy_le U V C ρ A hρ
    (fun x => polynomialMomentRoot ϖ x ^ p)
    ((polynomialMomentRoot_continuous ϖ).pow p).aemeasurable hb hr
    (Weighted.planeMomentPolynomial n ϖ 0) hW.aemeasurable
    (fun x => by unfold Weighted.planeMomentPolynomial; positivity)
  have hs : (fun x => Weighted.planeMomentPolynomial n ϖ 0 x *
      (polynomialMomentRoot ϖ x ^ p) ^ 2) = Weighted.planeMomentPolynomial (n + p) ϖ 0 :=
    funext (fun x => polynomialMomentRoot_weight_shift ϖ x n p)
  rwa [hs] at hh

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleWords

/-! The reduced scalar multiplier generator is a genuine bounded form on periodic H1. -/

def cellScalarMultiplierForm (η Cw : ℝ) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) :
    TorusHk 1 ℂ →L[ℝ] TorusHk 1 ℂ →L[ℝ] ℝ :=
  cellGeneratorForm ⟨fun t _ => G t, 0, fun j => (Real.sqrt η : ℂ) * ξ j, κ⟩
    hG 0 measurable_const (by intro t x; simp) t -
      pullbackInnerCLM ((cellScalarCLM Complex.I).comp
        ((cellFibreDriftCouplingCLM η Cw hCw hv hw ξ t).comp torusHkValueCLM)) torusHkValueCLM

theorem cellScalarMultiplierForm_pairing (η Cw : ℝ) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) (u z : TorusHk 1 ℂ) :
    cellScalarMultiplierForm η Cw hCw G hG hv hw ξ κ t u z =
      cellGeneratorForm ⟨fun t _ => G t, 0, fun j => (Real.sqrt η : ℂ) * ξ j, κ⟩
        hG 0 measurable_const (by intro t x; simp) t u z -
      inner ℝ (cellScalarCLM Complex.I (cellFibreDriftCouplingCLM η Cw hCw hv hw ξ t
        (torusHkValueCLM u))) (torusHkValueCLM z) := by
  simp only [cellScalarMultiplierForm, sub_apply, pullbackInnerCLM_apply,
    ContinuousLinearMap.comp_apply]

theorem cellScalarMultiplierForm_pairing_aestronglyMeasurable {a b : ℝ}
    (η Cw : ℝ) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (κ : ℝ → ℂ)
    (hκ : AEStronglyMeasurable κ (volume.restrict (Icc a b))) (u z : TorusHk 1 ℂ) :
    AEStronglyMeasurable (fun t => cellScalarMultiplierForm η Cw hCw G hG hv hw ξ κ t u z)
      (volume.restrict (Icc a b)) := by
  have hd := cellDiffusionForm_pairing_stronglyMeasurable
    (⟨fun t _ => G t, 0, fun j => (Real.sqrt η : ℂ) * ξ j, κ⟩ : CellCoefficients) hG u z
  have hp : Continuous (fun c : ℂ => inner ℝ
      (cellScalarCLM c (torusHkValueCLM u)) (torusHkValueCLM z)) :=
    ((ContinuousLinearMap.lsmul ℝ ℂ).continuous.clm_apply continuous_const).inner continuous_const
  have hm := cellCoefficient_fixed_stronglyMeasurable (fibreDriftCoupling η v ξ)
    (fibreDriftCoupling_measurable η hv ξ) (Cw * fibreNorm ξ)
    (mul_nonneg hCw (fibreNorm_nonneg ξ)) (fibreDriftCoupling_norm_le η Cw v hw ξ)
    (torusHkValueCLM u)
  have hm' : StronglyMeasurable (fun t => cellFibreDriftCouplingCLM η Cw hCw hv hw ξ t
      (torusHkValueCLM u)) := hm
  have hsource : AEStronglyMeasurable (fun t => inner ℝ
      (cellScalarCLM Complex.I (cellFibreDriftCouplingCLM η Cw hCw hv hw ξ t
        (torusHkValueCLM u))) (torusHkValueCLM z)) (volume.restrict (Icc a b)) := (((cellScalarCLM Complex.I).continuous.comp_stronglyMeasurable hm').inner
    stronglyMeasurable_const).aestronglyMeasurable
  simp only [cellScalarMultiplierForm_pairing, cellZeroDrift_generator_eq_diffusion]
  exact (hd.aestronglyMeasurable.add (hp.comp_aestronglyMeasurable hκ)).sub hsource

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped NNReal ENNReal
namespace AVRegularity.CycleWords

/-! Polynomial factorial energy transfer for a centred renewal. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem centredSobolev_pullback_energy {K : ℕ} (U V : PlaneHk Set.univ K E)
    (X : Vec 2 ≃ₜ Vec 2) (hX : ContDiff ℝ (⊤ : ℕ∞) (X : Vec 2 → Vec 2))
    (hμ : MeasurePreserving X volume volume) (B : ℕ → ℝ)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ z, ‖iteratedFDeriv ℝ j X z‖ ≤ B j)
    (hv : planeValue V =ᵐ[volume] planeValue U ∘ X)
    (L : ℝ≥0) (hL : LipschitzWith L (X.symm : Vec 2 → Vec 2)) (h0 : X 0 = 0)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (ϖ : ℝ) (n : ℕ) :
    weightedFactorialNormSq n ϖ 0 r K V ≤
      ENNReal.ofReal (pullbackSquareBudget B K * (1 + 4 * (L : ℝ) ^ 2) ^ n) *
        weightedFactorialNormSq n ϖ 0 r K U := by
  rw [Weighted.weightedFactorialNormSq_stored_readout,
    Weighted.weightedFactorialNormSq_stored_readout]
  let W := fun z : Vec 2 => (1 + ϖ ^ 2 * ((z 0) ^ 2 + (z 1) ^ 2)) ^ n
  have hW : Continuous W := by fun_prop
  have hW0 : ∀ z, 0 ≤ W z := fun z => by dsimp [W]; positivity
  have he : Weighted.planeMomentPolynomial n ϖ 0 = W := by
    funext z
    simp [Weighted.planeMomentPolynomial, W]
  rw [he]
  apply planeSobolev_weighted_pullback U V X hX hμ B hb hv r hr hr1
    W W hW.aemeasurable hW.aemeasurable hW0 hW0 _ (by positivity)
  intro z
  exact centred_polynomial_pullback_bound X L L.2
    (centred_homeomorph_inverse_norm X L hL h0) ϖ n z

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Uniform form bounds use the normalized drift amplitude. -/

theorem cellScalarMultiplierForm_uniform_bound (η Cw : ℝ) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (κ : ℝ → ℂ) (k : ℝ) (hκ : ∀ t, ‖κ t‖ ≤ k) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t u,
      ‖cellScalarMultiplierForm η Cw hCw G hG hv hw ξ κ t u‖ ≤ M * ‖u‖ := by
  obtain ⟨M, hM, hb⟩ := cellGeneratorForm_uniform_norm_bound
    (⟨fun t _ => G t, 0, fun j => (Real.sqrt η : ℂ) * ξ j, κ⟩ : CellCoefficients)
    hG 0 k measurable_const (by intro t x; simp) hκ
  let J := ‖torusHkValueCLM (E := ℂ) (K := 1)‖
  have hJ : 0 ≤ J := norm_nonneg (torusHkValueCLM (E := ℂ) (K := 1))
  have hW : 0 ≤ Cw * fibreNorm ξ := mul_nonneg hCw (fibreNorm_nonneg ξ)
  refine ⟨M + Cw * fibreNorm ξ * J * J,
    add_nonneg hM (mul_nonneg (mul_nonneg hW hJ) hJ), fun t u => ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (add_nonneg hM (mul_nonneg (mul_nonneg hW hJ) hJ)) (norm_nonneg u))
  intro z
  rw [Real.norm_eq_abs, cellScalarMultiplierForm_pairing]
  have hbase := ((cellGeneratorForm
    (⟨fun t _ => G t, 0, fun j => (Real.sqrt η : ℂ) * ξ j, κ⟩ : CellCoefficients)
    hG 0 measurable_const (by intro t x; simp) t u).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right (hb t u) (norm_nonneg z))
  rw [Real.norm_eq_abs] at hbase
  have hu := (torusHkValueCLM (E := ℂ) (K := 1)).le_opNorm u
  have hz := (torusHkValueCLM (E := ℂ) (K := 1)).le_opNorm z
  have hm := cellFibreDriftCouplingCLM_apply_norm_le η Cw hCw hv hw ξ t (torusHkValueCLM u)
  have hsrc := abs_real_inner_le_norm
    (cellScalarCLM Complex.I (cellFibreDriftCouplingCLM η Cw hCw hv hw ξ t (torusHkValueCLM u)))
    (torusHkValueCLM z)
  rw [cellScalarCLM_norm, Complex.norm_I, one_mul] at hsrc
  have hsource : |inner ℝ
      (cellScalarCLM Complex.I (cellFibreDriftCouplingCLM η Cw hCw hv hw ξ t (torusHkValueCLM u)))
      (torusHkValueCLM z)| ≤ (Cw * fibreNorm ξ * (J * ‖u‖)) * (J * ‖z‖) :=
    hsrc.trans (mul_le_mul
      (hm.trans (mul_le_mul_of_nonneg_left hu hW)) hz (norm_nonneg _)
      (mul_nonneg hW (mul_nonneg hJ (norm_nonneg u))))
  exact (abs_sub _ _).trans ((add_le_add hbase hsource).trans_eq (by ring))

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleWords

/-! Isolate the actual metric carrier from an arbitrary literal flux. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem scalarSobolevMetricSource_zero_memLp {K : ℕ} {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hGm : Measurable (fun p : Set.Icc a b × Vec 2 => G p.1 p.2))
    (hG : ∀ t ∈ Set.Icc a b, ∀ k j, ContDiff ℝ (K : ℕ) (fun x => G t x k j))
    (M : Fin (K + 1) → ℝ)
    (hb : ∀ t ∈ Set.Icc a b, ∀ (l : Fin (K + 1)) x k j,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k j) x‖ ≤ M l)
    (W : ℝ → PlaneHk Set.univ (K + 1) E)
    (hW : MemLp W 2 (volume.restrict (Set.Icc a b))) :
    MemLp (scalarSobolevMetricSource hab G hG M hb W (fun _ => 0)) 2
      (volume.restrict (Set.Icc a b)) :=
  scalarSobolevMetricSource_memLp (E := E) (K := K) hab G hGm hG M hb W
    (fun _ => 0) hW (planeHk_zero_time_memLp
      (E := PiLp 2 (fun _ : Fin 2 => E)) K (volume.restrict (Set.Icc a b)))

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped NNReal ENNReal
namespace AVRegularity.CycleWords

/-! Uniform polynomial Sobolev renewal constants over a finite slot reserve. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem centredSobolev_pullback_energy_uniform {K Kmax : ℕ} (hK : K ≤ Kmax)
    (U V : PlaneHk Set.univ K E)
    (X : Vec 2 ≃ₜ Vec 2) (hX : ContDiff ℝ (⊤ : ℕ∞) (X : Vec 2 → Vec 2))
    (hμ : MeasurePreserving X volume volume) (B : ℕ → ℝ)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ z, ‖iteratedFDeriv ℝ j X z‖ ≤ B j)
    (hv : planeValue V =ᵐ[volume] planeValue U ∘ X)
    (L : ℝ≥0) (hL : LipschitzWith L (X.symm : Vec 2 → Vec 2)) (h0 : X 0 = 0)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (ϖ : ℝ) (n : ℕ) :
    weightedFactorialNormSq n ϖ 0 r K V ≤
      ENNReal.ofReal (uniformPullbackSquareBudget B Kmax * (1 + 4 * (L : ℝ) ^ 2) ^ n) *
        weightedFactorialNormSq n ϖ 0 r K U := by
  apply (centredSobolev_pullback_energy U V X hX hμ B hb hv L hL h0 r hr hr1 ϖ n).trans
  apply mul_le_mul'
  · exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (pullbackSquareBudget_le_uniform B hK) (by positivity))
  · exact le_rfl

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleWords

/-! The actual normalized drift multiplication lifts through a window-only smooth coefficient. -/

variable {K : ℕ} (a b η : ℝ) {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
  (ξ : Fin 2 → ℂ) (hc : ∀ t ∈ Icc a b, ContDiff ℝ (K : ℕ) (v t))
  (A : Fin (K + 1) → ℝ) (hA : ∀ l, 0 ≤ A l)
  (hb : ∀ t ∈ Icc a b, ∀ l x,
    ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)

def torusNormalizedDriftWindowMultiplier (t : ℝ) (U : TorusHk K ℂ) : TorusHk K ℂ :=
  torusWindowMultiplier a b (normalizedDriftCoefficient η v ξ)
    (fun t ht => normalizedDriftCoefficient_contDiff η v ξ t K (hc t ht))
    (fun t _ => normalizedDriftCoefficient_periodic η hv ξ t) A hA hb t U

theorem torusNormalizedDriftWindowMultiplier_memLp
    (U : ℝ → TorusHk K ℂ) (hU : MemLp U 2 (volume.restrict (Icc a b))) :
    MemLp (fun t => torusNormalizedDriftWindowMultiplier a b η hv ξ hc A hA hb t (U t)) 2
      (volume.restrict (Icc a b)) :=
  torusWindowMultiplier_memLp a b (normalizedDriftCoefficient η v ξ)
    (fun t ht => normalizedDriftCoefficient_contDiff η v ξ t K (hc t ht))
    (fun t _ => normalizedDriftCoefficient_periodic η hv ξ t) A hA hb
    (normalizedDriftCoefficient_measurable η hv ξ) U hU

theorem torusNormalizedDriftWindowMultiplier_value (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (t : ℝ) (ht : t ∈ Icc a b) (U : TorusHk K ℂ) :
    torusHkValueCLM (torusNormalizedDriftWindowMultiplier a b η hv ξ hc A hA hb t U) =
      cellFibreDriftCouplingCLM η Cw hCw hv hw ξ t (torusHkValueCLM U) := by
  unfold torusNormalizedDriftWindowMultiplier
  rw [torusWindowMultiplier_agrees _ _ _ _ _ _ _ _ t ht]
  apply Lp.ext
  have hleft := torusMulCoefficient_value_ae U (normalizedDriftCoefficient η v ξ t)
    (normalizedDriftCoefficient_contDiff η v ξ t K (hc t ht))
    (normalizedDriftCoefficient_periodic η hv ξ t) (hb t ht)
  have hright := cellCoefficientCLM_ae (fibreDriftCoupling η v ξ t)
    (cellBlochDriftCoupling_aestronglyMeasurable η hv ξ t) (Cw * fibreNorm ξ)
    (mul_nonneg hCw (fibreNorm_nonneg ξ)) (fibreDriftCoupling_norm_le η Cw v hw ξ t)
    (torusHkValueCLM U)
  change (torusHkValueCLM (U.mulCoefficient (normalizedDriftCoefficient η v ξ t)
    (normalizedDriftCoefficient_contDiff η v ξ t K (hc t ht))
    (normalizedDriftCoefficient_periodic η hv ξ t) (hb t ht)) : Vec 2 → ℂ) =ᵐ[_]
    (fun x => normalizedDriftCoefficient η v ξ t x (torusHkValueCLM U x)) at hleft
  change (cellFibreDriftCouplingCLM η Cw hCw hv hw ξ t (torusHkValueCLM U) : Vec 2 → ℂ) =ᵐ[_]
    (fun x => fibreDriftCoupling η v ξ t x * torusHkValueCLM U x) at hright
  filter_upwards [hleft, hright] with x hl hr
  rw [hl, hr]
  rw [normalizedDriftCoefficient, normalizedDriftCoefficientEmbedding_coupling]
  rfl

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The literal windowed normalized drift product is a bounded linear map at every native order. -/

variable {K : ℕ} (a b η : ℝ) {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
  (ξ : Fin 2 → ℂ) (hc : ∀ t ∈ Icc a b, ContDiff ℝ (K : ℕ) (v t))
  (A : Fin (K + 1) → ℝ) (hA : ∀ l, 0 ≤ A l)
  (hb : ∀ t ∈ Icc a b, ∀ l x,
    ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)

def torusNormalizedDriftWindowMultiplierCLM (t : ℝ) : TorusHk K ℂ →L[ℝ] TorusHk K ℂ :=
  KernelEnergy.torusMultiplierCLM
    (windowCoefficient a b (normalizedDriftCoefficient η v ξ) t)
    (windowCoefficient_contDiff a b K _
      (fun t ht => normalizedDriftCoefficient_contDiff η v ξ t K (hc t ht)) t)
    (windowCoefficient_periodic a b _ (fun t _ => normalizedDriftCoefficient_periodic η hv ξ t) t)
    A (windowCoefficient_derivative_bound a b K _ A hA hb t) 1 (by norm_num)

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The actual reduced weak generator has a temporal H1 Riesz derivative. -/

def cellScalarMultiplierDual (η Cw : ℝ) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) (u : TorusHk 1 ℂ) : TorusHk 1 ℂ :=
  cellDualDerivative ⟨fun t _ => G t, 0, fun j => (Real.sqrt η : ℂ) * ξ j, κ⟩
    hG 0 measurable_const (by intro t x; simp) t u
      (-cellScalarCLM Complex.I (cellFibreDriftCouplingCLM η Cw hCw hv hw ξ t (torusHkValueCLM u))) 0

theorem cellScalarMultiplierDual_pairing (η Cw : ℝ) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) (u z : TorusHk 1 ℂ) :
    inner ℝ (cellScalarMultiplierDual η Cw hCw G hG hv hw ξ κ t u) z =
      cellScalarMultiplierForm η Cw hCw G hG hv hw ξ κ t u z := by
  rw [cellScalarMultiplierDual, cellDualDerivative_pairing, cellScalarMultiplierForm_pairing,
    cellSourceFunctional_scalar_only, inner_neg_left, sub_eq_add_neg]

theorem cellScalarMultiplierDual_memLp {μ : Measure ℝ}
    (η Cw : ℝ) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (κ : ℝ → ℂ) (hκm : MemLp κ ⊤ μ)
    (k : ℝ) (hκ : ∀ t, ‖κ t‖ ≤ k)
    (u : ℝ → TorusHk 1 ℂ) (hu : MemLp u 2 μ) :
    MemLp (fun t => cellScalarMultiplierDual η Cw hCw G hG hv hw ξ κ t (u t)) 2 μ := by
  have hval := (torusHkValueCLM (E := ℂ) (K := 1)).comp_memLp' hu
  have hmul : MemLp (fun t => cellFibreDriftCouplingCLM η Cw hCw hv hw ξ t
      (torusHkValueCLM (u t))) 2 μ :=
    cellCoefficient_variable_memLp (fibreDriftCoupling η v ξ)
      (fibreDriftCoupling_measurable η hv ξ) (Cw * fibreNorm ξ)
      (mul_nonneg hCw (fibreNorm_nonneg ξ)) (fibreDriftCoupling_norm_le η Cw v hw ξ) _ hval
  exact cellDualDerivative_memLp_aePotential
    (⟨fun t _ => G t, 0, fun j => (Real.sqrt η : ℂ) * ξ j, κ⟩ : CellCoefficients)
    hG 0 k measurable_const (by intro t x; simp) hκm.aestronglyMeasurable hκ u hu
    _ ((cellScalarCLM Complex.I).comp_memLp' hmul).neg _ (fun _ => MemLp.zero')

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleWords

/-! The genuine window multiplier has a uniform bound determined by its finite normalized jet budget. -/

variable {K : ℕ} (a b η : ℝ) {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
  (ξ : Fin 2 → ℂ) (hc : ∀ t ∈ Icc a b, ContDiff ℝ (K : ℕ) (v t))
  (A : Fin (K + 1) → ℝ) (hA : ∀ l, 0 ≤ A l)
  (hb : ∀ t ∈ Icc a b, ∀ l x,
    ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)

theorem torusNormalizedDriftWindowMultiplierCLM_uniform_bound :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t,
      ‖torusNormalizedDriftWindowMultiplierCLM a b η hv ξ hc A hA hb t‖ ≤ D := by
  let D := ((∑ l : Fin (K + 1), factorialRootWeight 1 l.val * A l) *
    Real.sqrt (factorialWeightMax 1 K) / Real.sqrt (factorialWeightMin 1 K))
  have hs : 0 ≤ ∑ l : Fin (K + 1), factorialRootWeight 1 l.val * A l :=
    Finset.sum_nonneg fun l _ => mul_nonneg (by unfold factorialRootWeight; positivity) (hA l)
  have hD : 0 ≤ D := div_nonneg (mul_nonneg hs (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  refine ⟨D, hD, ?_⟩
  intro t
  apply ContinuousLinearMap.opNorm_le_bound _ hD
  intro u
  exact KernelEnergy.torusMultiplier_norm_bound
    (windowCoefficient a b (normalizedDriftCoefficient η v ξ) t)
    (windowCoefficient_contDiff a b K _
      (fun t ht => normalizedDriftCoefficient_contDiff η v ξ t K (hc t ht)) t)
    (windowCoefficient_periodic a b _ (fun t _ => normalizedDriftCoefficient_periodic η hv ξ t) t)
    A (windowCoefficient_derivative_bound a b K _ A hA hb t) 1 (by norm_num) u

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Actual transverse full cell energy curves satisfy the reduced scalar multiplier equation. -/

theorem cellTransverse_actual_reduced_weak_curve {a b : ℝ}
    (η Cw : ℝ) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (e : Fin 2) (hs : ∀ t x, v t x e.rev = 0)
    (ξ : Fin 2 → ℂ) (κ : ℝ → ℂ)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice (fun t =>
      cellDualDerivative ⟨fun t _ => G t, v, fun j => (Real.sqrt η : ℂ) * ξ j, κ⟩
        hG V hv.1 hb t (slice t) 0 0))
    (hfixed : ∀ᵐ t ∂volume.restrict (Icc a b), cellTransverseProjection e (u t) = u t) :
    CellWeakHilbertCurve a b u slice
      (fun t => cellScalarMultiplierDual η Cw hCw G hG hv hw ξ κ t (slice t)) := by
  apply h.dual_congr
  filter_upwards [h.agrees, hfixed] with t hut hft
  have hs0 : cellTransverseH1Projection e (slice t) = slice t := by
    apply TorusHk.ext_value
    change torusHkValueCLM (cellTransverseH1Projection e (slice t)) = torusHkValueCLM (slice t)
    rw [cellTransverseH1Projection_value, ← hut, hft]
  apply ext_inner_right ℝ
  intro z
  rw [cellDualDerivative_pairing, cellSourceFunctional_scalar_only, inner_zero_left, add_zero,
    cellScalarMultiplierDual_pairing, cellScalarMultiplierForm_pairing]
  have hr := cellTransverseH1Projection_reduced_generator η Cw hCw G hG hv hw V hb e hs ξ κ t (slice t) z
  rw [hs0] at hr
  rw [cellZeroDrift_generator_eq_diffusion]
  have hd : cellDiffusionForm ⟨fun t _ => G t, v, fun j => (Real.sqrt η : ℂ) * ξ j, κ⟩ hG t =
      cellDiffusionForm ⟨fun t _ => G t, 0, fun j => (Real.sqrt η : ℂ) * ξ j, κ⟩ hG t := rfl
  rw [hd] at hr
  exact hr.trans (by ring)

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The true reduced generator has a one-sided growth bound in the L2 value norm. -/

theorem cellScalarMultiplierDual_sub (η Cw : ℝ) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) (u w : TorusHk 1 ℂ) :
    cellScalarMultiplierDual η Cw hCw G hG hv hw ξ κ t (u - w) =
      cellScalarMultiplierDual η Cw hCw G hG hv hw ξ κ t u -
        cellScalarMultiplierDual η Cw hCw G hG hv hw ξ κ t w := by
  apply ext_inner_right ℝ
  intro z
  simp only [inner_sub_left, cellScalarMultiplierDual_pairing, map_sub, sub_apply]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleWords

/-! On the original window the clamped full Sobolev sources have the prescribed scalar RHS. -/

open AVRegularity.Weighted

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem constantMetric_scalarSobolevSource_word_spatial_budget {K Kmax : ℕ} {ta tb : ℝ}
    (hK : K ≤ Kmax) (hab : ta ≤ tb)
    (v : ℝ → Vec 2 → Vec 2) (hv : ∀ t ∈ Set.Icc ta tb, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hbv : ∀ t ∈ Set.Icc ta tb, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc ta tb, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ t ∈ Set.Icc ta tb, ∀ k j, ContDiff ℝ (K : ℕ) (fun x => G t x k j))
    (M : Fin (K + 1) → ℝ)
    (hb : ∀ t ∈ Set.Icc ta tb, ∀ (l : Fin (K + 1)) x k j,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k j) x‖ ≤ M l)
    (hCell : IsCellMetric G)
    (hconstant : ∀ t x, G t x = G t 0)
    (W : ℝ → PlaneHk Set.univ (K + 1) E)
    (F : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (t : ℝ) (ht : t ∈ Set.Icc ta tb)
    (hG1 : ∀ t ∈ Set.Icc ta tb, ∀ k j, ContDiff ℝ 1 (fun x => G t x k j))
    (U : PlaneHk Set.univ K E) (hU : U = truncatePlaneHk (Nat.le_succ K) (W t))
    (ρ : ℝ) (q : Vec 2 → ℝ)
    (hρ : 0 < ρ) (ν : ℝ) (hν : 0 < ν) (hstrain : 0 ≤ strain) (hB : 1 ≤ B)
    (hlam : 0 < lam) (hV : 0 ≤ V)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrainSmall : strain * B * ρ ^ 2 ≤ ν / 8)
    (hq : Continuous q) (hq0 : ∀ x, 0 ≤ q x) (Cq : ℝ) (hqb : ∀ x, q x ≤ Cq) :
    let H := scalarSobolevTransportSource hK hab v hv V strain B lam hbv hjets W
    let Q := scalarSobolevMetricSource hab G hG M hb W F
    let T := planeIntervalTransport ta tb hab v (fun t ht => (hv t ht).continuous) V hbv
    let A := cellMetricIntervalDiffusion ta tb hab G (fun t ht k j => (hG1 t ht k j).continuous)
      hCell
    let R := fun α : JetIndex2 K => planeJetReadoutOperator K α (H t) + T t
      (planeH1GradientOperator (planeWordH1SliceOperator K α (W t)))
    let L := fun α : JetIndex2 K => planeJetFluxOperator K α (Q t) - A t
      (planeH1GradientOperator (planeWordH1SliceOperator K α (W t)))
    ((∑ α : JetIndex2 K, factorialWeight ρ α.1.val *
      (∫ x, q x * (‖R α x‖ * ‖planeJetReadoutOperator K α U x‖))) ≤
      (ν / 4) * rawWeightedGradientEnergy ρ q (W t).toFunction.jet) ∧
    ((∑ α : JetIndex2 K, factorialWeight ρ α.1.val *
      (∫ x, q x * ‖(WithLp.toLp 2 (fun k : Fin 2 => L α k x) :
        PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2)) ≤
      rawWeightedFactorialEnergy ρ q (F t).toFunction.jet) := by
  dsimp only
  have hr := cellMetric_scalarSobolevSource_word_energy_readout hK hab v hv V strain B lam hbv hjets
    G hG M hb hCell W F t ht hG1 U hU ρ q
  dsimp only at hr
  constructor
  · rw [hr.1]
    exact planeDriftValueSource_budget hK ρ strain B lam ν V hρ hstrain hB hlam hν hV
      hsmall hstrainSmall (v t) (hv t ht) (hbv t ht) (hjets t ht) q hq hq0 Cq hqb
      (W t).toFunction.jet (W t).toFunction.memL2
  · rw [hr.2]
    have hc : G t = fun _ => G t 0 := funext (hconstant t)
    rw [hc]
    simp_rw [metricCommutatorTerm_constant, zero_add]
    exact le_rfl

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Polynomial forcing growth consumes exactly its degree in the source gradient moment. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

theorem nativeFlux_moment_shift_budget {K L : ℕ} (n p : ℕ) (ϖ ρ A : ℝ)
    (V : PlaneHk Set.univ K F) (U : PlaneHk Set.univ (L + 1) E)
    (hb : ∀ᵐ x ∂volume, planeFactorialDensity ρ V x ≤
      A ^ 2 * (polynomialMomentRoot ϖ x ^ p) ^ 2 * planeGradFactorialDensity ρ U x) :
    weightedFactorialNormSq n ϖ 0 ρ K V ≤
      ENNReal.ofReal (A ^ 2) * weightedGradFactorialNormSq (n + p) ϖ 0 ρ L U := by
  rw [weightedFactorialNormSq_density, weightedGradFactorialNormSq_density,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hb] with x hx
  rw [← ENNReal.ofReal_mul (sq_nonneg A)]
  apply ENNReal.ofReal_le_ofReal
  have hq : 0 ≤ Weighted.planeMomentPolynomial n ϖ 0 x := by
    unfold Weighted.planeMomentPolynomial
    positivity
  have hh := mul_le_mul_of_nonneg_left hx hq
  have he : Weighted.planeMomentPolynomial n ϖ 0 x *
      (A ^ 2 * (polynomialMomentRoot ϖ x ^ p) ^ 2 * planeGradFactorialDensity ρ U x) =
      A ^ 2 * (Weighted.planeMomentPolynomial (n + p) ϖ 0 x * planeGradFactorialDensity ρ U x) := by
    rw [← polynomialMomentRoot_weight_shift]
    ring
  exact hh.trans_eq he

theorem nativeFlux_time_moment_shift_budget {K L : ℕ} (n p : ℕ) (ϖ ρ A : ℝ)
    (μ : Measure ℝ) (V : ℝ → PlaneHk Set.univ K F)
    (U : ℝ → PlaneHk Set.univ (L + 1) E)
    (hb : ∀ᵐ t ∂μ, ∀ᵐ x ∂volume, planeFactorialDensity ρ (V t) x ≤
      A ^ 2 * (polynomialMomentRoot ϖ x ^ p) ^ 2 * planeGradFactorialDensity ρ (U t) x) :
    (∫⁻ t, weightedFactorialNormSq n ϖ 0 ρ K (V t) ∂μ) ≤
      ENNReal.ofReal (A ^ 2) * ∫⁻ t, weightedGradFactorialNormSq (n + p) ϖ 0 ρ L (U t) ∂μ := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hb] with t ht
  exact nativeFlux_moment_shift_budget n p ϖ ρ A (V t) (U t) ht
end

/-! A literal mass-density estimate gives the weighted polynomial forcing estimate at every moment. -/

section
variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

theorem nativeFlux_moment_shift_mass_budget (π : ι → ℝ) (hπ : ∀ v, 0 ≤ π v)
    (K : ι → ℕ) (n p : ℕ) (ϖ : ℝ) (ρ C : ℝ)
    (V : ∀ v, PlaneHk Set.univ (K v) (PiLp 2 (fun _ : Fin 2 => E v)))
    (U : ∀ v, PlaneHk Set.univ (K v + 1) (E v))
    (hb : ∀ᵐ x ∂volume, (∑ v, (π v)⁻¹ * planeFactorialDensity ρ (V v) x) ≤
      C ^ 2 * (polynomialMomentRoot ϖ x ^ p) ^ 2 * ∑ u, (π u)⁻¹ * planeGradFactorialDensity ρ (U u) x) :
    (∑ v, ENNReal.ofReal ((π v)⁻¹) * weightedFactorialNormSq n ϖ 0 ρ (K v) (V v)) ≤
      ENNReal.ofReal (C ^ 2) *
        ∑ u, ENNReal.ofReal ((π u)⁻¹) * weightedGradFactorialNormSq (n + p) ϖ 0 ρ (K u) (U u) := by
  rw [weightedFactorialNormSq_mass_density π hπ K n ϖ 0 ρ,
    weightedGradFactorialNormSq_mass_density π hπ K (n + p) ϖ 0 ρ,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hb] with x hx
  rw [← ENNReal.ofReal_mul (sq_nonneg C)]
  apply ENNReal.ofReal_le_ofReal
  have hq : 0 ≤ Weighted.planeMomentPolynomial n ϖ 0 x := by
    unfold Weighted.planeMomentPolynomial
    positivity
  have hh := mul_le_mul_of_nonneg_left hx hq
  have he : Weighted.planeMomentPolynomial n ϖ 0 x *
      (C ^ 2 * (polynomialMomentRoot ϖ x ^ p) ^ 2 *
        ∑ u, (π u)⁻¹ * planeGradFactorialDensity ρ (U u) x) =
      C ^ 2 * (Weighted.planeMomentPolynomial (n + p) ϖ 0 x *
        ∑ u, (π u)⁻¹ * planeGradFactorialDensity ρ (U u) x) := by
    rw [← polynomialMomentRoot_weight_shift]
    ring
  exact hh.trans_eq he

theorem nativeFlux_time_moment_shift_mass_budget (π : ι → ℝ) (hπ : ∀ v, 0 ≤ π v)
    (K : ι → ℕ) (n p : ℕ) (ϖ : ℝ) (ρ C : ℝ) (μ : Measure ℝ)
    (V : ∀ v, ℝ → PlaneHk Set.univ (K v) (PiLp 2 (fun _ : Fin 2 => E v)))
    (U : ∀ v, ℝ → PlaneHk Set.univ (K v + 1) (E v))
    (hb : ∀ᵐ t ∂μ, ∀ᵐ x ∂volume, (∑ v, (π v)⁻¹ * planeFactorialDensity ρ (V v t) x) ≤
      C ^ 2 * (polynomialMomentRoot ϖ x ^ p) ^ 2 * ∑ u, (π u)⁻¹ * planeGradFactorialDensity ρ (U u t) x) :
    (∫⁻ t, (∑ v, ENNReal.ofReal ((π v)⁻¹) * weightedFactorialNormSq n ϖ 0 ρ (K v) (V v t)) ∂μ) ≤
      ENNReal.ofReal (C ^ 2) *
        ∫⁻ t, (∑ u, ENNReal.ofReal ((π u)⁻¹) * weightedGradFactorialNormSq (n + p) ϖ 0 ρ (K u) (U u t)) ∂μ := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hb] with t ht
  exact nativeFlux_moment_shift_mass_budget π hπ K n p ϖ ρ C (fun v => V v t) (fun u => U u t) ht
end

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! A normalized row forcing estimate consumes exactly the polynomial degree
in the source moments, before any weighted finiteness assumption. -/

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

theorem nativeFlux_row_moment_budget {L : ℕ} (K : ι → ℕ)
    (n s : ℕ) (ϖ ρ α R : ℝ) (hα : 0 ≤ α) (hR : 0 ≤ R)
    (p : ι → ℝ) (hp : ∀ u, 0 ≤ p u)
    (V : PlaneHk Set.univ L F) (U : ∀ u, PlaneHk Set.univ (K u + 1) (E u))
    (hb : ∀ᵐ x ∂volume, α * planeFactorialDensity ρ V x ≤
      R * (polynomialMomentRoot ϖ x ^ s) ^ 2 * ∑ u, p u * planeGradFactorialDensity ρ (U u) x) :
    ENNReal.ofReal α * weightedFactorialNormSq n ϖ 0 ρ L V ≤
      ENNReal.ofReal R * ∑ u, ENNReal.ofReal (p u) *
        weightedGradFactorialNormSq (n + s) ϖ 0 ρ (K u) (U u) := by
  have hh := weightedGradFactorialNormSq_mass_density (fun u => (p u)⁻¹)
    (fun u => inv_nonneg.mpr (hp u)) K (n + s) ϖ 0 ρ U
  simp only [inv_inv] at hh
  rw [weightedFactorialNormSq_density, hh,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hb] with x hx
  rw [← ENNReal.ofReal_mul hα, ← ENNReal.ofReal_mul hR]
  apply ENNReal.ofReal_le_ofReal
  have hq : 0 ≤ Weighted.planeMomentPolynomial n ϖ 0 x := by
    unfold Weighted.planeMomentPolynomial
    positivity
  have he : Weighted.planeMomentPolynomial n ϖ 0 x *
      (R * (polynomialMomentRoot ϖ x ^ s) ^ 2 * ∑ u, p u * planeGradFactorialDensity ρ (U u) x) =
      R * (Weighted.planeMomentPolynomial (n + s) ϖ 0 x *
        ∑ u, p u * planeGradFactorialDensity ρ (U u) x) := by
    rw [← polynomialMomentRoot_weight_shift]
    ring
  have ht := (mul_le_mul_of_nonneg_left hx hq).trans_eq he
  simpa only [mul_comm α, mul_assoc] using ht

theorem nativeFlux_row_time_moment_budget {L : ℕ} (K : ι → ℕ)
    (n s : ℕ) (ϖ ρ α R : ℝ) (hα : 0 ≤ α) (hR : 0 ≤ R)
    (p : ι → ℝ) (hp : ∀ u, 0 ≤ p u) (μ : Measure ℝ)
    (V : ℝ → PlaneHk Set.univ L F) (U : ∀ u, ℝ → PlaneHk Set.univ (K u + 1) (E u))
    (hU : ∀ u, MemLp (U u) 2 μ)
    (hb : ∀ᵐ t ∂μ, ∀ᵐ x ∂volume, α * planeFactorialDensity ρ (V t) x ≤
      R * (polynomialMomentRoot ϖ x ^ s) ^ 2 * ∑ u, p u * planeGradFactorialDensity ρ (U u t) x) :
    ENNReal.ofReal α * (∫⁻ t, weightedFactorialNormSq n ϖ 0 ρ L (V t) ∂μ) ≤
      ENNReal.ofReal R * ∑ u, ENNReal.ofReal (p u) *
        ∫⁻ t, weightedGradFactorialNormSq (n + s) ϖ 0 ρ (K u) (U u t) ∂μ := by
  have hm (u : ι) : AEMeasurable (fun t => weightedGradFactorialNormSq (n + s) ϖ 0 ρ (K u) (U u t)) μ := by
    simp_rw [← planeGradientTensor_weightedFactorialNormSq (n + s) ϖ 0 ρ]
    have hUg : MemLp (fun t => planeGradientTensor (U u t)) 2 μ := by
      simpa only [Function.comp_def, planeGradientTensorOperator_apply] using
        (planeGradientTensorOperator (E := E u) (K u)).comp_memLp' (hU u)
    exact Weighted.weightedFactorialNormSq_time_aemeasurable (n + s) ϖ 0 ρ μ
      (fun t => planeGradientTensor (U u t)) hUg
  have hh : ENNReal.ofReal α * (∫⁻ t, weightedFactorialNormSq n ϖ 0 ρ L (V t) ∂μ) ≤
      ENNReal.ofReal R * ∫⁻ t, (∑ u, ENNReal.ofReal (p u) *
        weightedGradFactorialNormSq (n + s) ϖ 0 ρ (K u) (U u t)) ∂μ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [hb] with t ht
    exact nativeFlux_row_moment_budget K n s ϖ ρ α R hα hR p hp (V t) (fun u => U u t) ht
  rw [lintegral_finsetSum' Finset.univ
    (f := fun u t => ENNReal.ofReal (p u) * weightedGradFactorialNormSq (n + s) ϖ 0 ρ (K u) (U u t))
    (fun u _ => aemeasurable_const.mul (hm u))] at hh
  simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hh
  exact hh

end AVRegularity.CycleWords
end

section
open MeasureTheory Set Homogenization Filter Topology
open AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Actual cell energy evolutions at arbitrary complex Bloch shifts. -/

def planeBlochEnergyFamily {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (d : CellFiniteEnergyDatum a b) (ζ : Fin 2 → ℂ) : CellEnergySpace a b :=
  cellFiniteEnergyEvolutionCLM hab ⟨fun t _ => G t, v, ζ, 0⟩ hG V 0 hv hb
    aestronglyMeasurable_const (fun _ => by simp) d

theorem planeBlochEnergyFamily_solves {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (d : CellFiniteEnergyDatum a b) (ζ : Fin 2 → ℂ) :
    IsCellFiniteEnergyEvolution ⟨fun t _ => G t, v, ζ, 0⟩ hG V hv hb d
      (planeBlochEnergyFamily hab G hG v V hv hb d ζ) :=
  cellFiniteEnergyEvolutionCLM_solves hab _ hG V 0 hv hb
    aestronglyMeasurable_const (fun _ => by simp) d

theorem planeBlochEnergyFamily_analyticAt {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (d : CellFiniteEnergyDatum a b) (ζ : Fin 2 → ℂ) :
    AnalyticAt ℂ (planeBlochEnergyFamily hab G hG v V hv hb d) ζ := by
  let C : CellCoefficients := ⟨fun t _ => G t, v, ζ, 0⟩
  let δ := fun y : Fin 2 → ℂ => y - ζ
  let q := fun _ : Fin 2 → ℂ => (0 : Lp ℂ ∞ (volume.restrict (Icc a b)))
  have hδ : AnalyticAt ℂ δ ζ := analyticAt_id.sub analyticAt_const
  have hq : AnalyticAt ℂ q ζ := analyticAt_const
  refine cellBlochEvolution_family_analyticAt hab C hG V 0 hv hb
    aestronglyMeasurable_const (fun _ => by simp [C]) δ q ζ hδ hq
    (sub_self ζ) rfl d (planeBlochEnergyFamily hab G hG v V hv hb d) ?_
  apply Filter.Eventually.of_forall
  intro y
  have he : (fun _ : ℝ => (0 : ℂ)) =ᵐ[volume.restrict (Icc a b)]
      fun t => (0 : Lp ℂ ∞ (volume.restrict (Icc a b))) t :=
    (Lp.coeFn_zero ℂ ∞ (volume.restrict (Icc a b))).symm
  have hr := cellFiniteEnergyEvolution_potential_congr
    (⟨fun t _ => G t, v, y, 0⟩ : CellCoefficients) hG V hv hb
    (fun _ => 0) (fun t => (0 : Lp ℂ ∞ (volume.restrict (Icc a b))) t) he d
    (planeBlochEnergyFamily hab G hG v V hv hb d y)
    (planeBlochEnergyFamily_solves hab G hG v V hv hb d y)
  simpa only [C, δ, q, Pi.zero_apply, zero_add, add_sub_cancel] using hr

end AVRegularity.CycleWords
end

section
open MeasureTheory Set Homogenization
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! A uniform energy-carrier bound on bounded sets of Bloch shifts. -/

theorem planeBlochEnergyFamily_norm_le {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (d : CellFiniteEnergyDatum a b) (ζ : Fin 2 → ℂ)
    (R : ℝ) (hR : ∑ j, ‖ζ j‖ ^ 2 ≤ R) :
    ‖planeBlochEnergyFamily hab G hG v V hv hb d ζ‖ ≤
      Real.sqrt (20 * (b - a + 2) *
        Real.exp (300 * (1 + R + V ^ 2) * (b - a))) * ‖d‖ := by
  have hn := cellFiniteEnergyEvolution_norm_bound hab
    (⟨fun t _ => G t, v, ζ, 0⟩ : CellCoefficients) hG V 0 hv hb
    (fun _ => by simp) d _ (planeBlochEnergyFamily_solves hab G hG v V hv hb d ζ)
  have he : 300 * (1 + ∑ j, ‖ζ j‖ ^ 2 + V ^ 2) * (b - a) ≤
      300 * (1 + R + V ^ 2) * (b - a) := by
    apply mul_le_mul_of_nonneg_right _ (sub_nonneg.mpr hab)
    exact mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
  have hm := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he)
    (show 0 ≤ 20 * (b - a + 2) by positivity))
  dsimp only at hn
  simp only [add_zero] at hn
  exact hn.trans (mul_le_mul_of_nonneg_right hm (norm_nonneg d))

end AVRegularity.CycleWords
end

section
open MeasureTheory Set Homogenization AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The actual solver as an operator into the named complex energy space. -/

def planeBlochEnergyOperator {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (ζ : Fin 2 → ℂ) :
    CellFiniteEnergyDatum a b →L[ℂ] CellEnergySpace a b :=
  (cellEnergySpaceOfCarrierCLM a b).comp
    (cellFiniteEnergyEvolutionCLM hab ⟨fun t _ => G t, v, ζ, 0⟩ hG V 0 hv hb
      aestronglyMeasurable_const (fun _ => by simp))

theorem planeBlochEnergyOperator_apply {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (ζ : Fin 2 → ℂ)
    (d : CellFiniteEnergyDatum a b) :
    planeBlochEnergyOperator hab G hG v V hv hb ζ d =
      planeBlochEnergyFamily hab G hG v V hv hb d ζ := rfl

end AVRegularity.CycleWords
end
