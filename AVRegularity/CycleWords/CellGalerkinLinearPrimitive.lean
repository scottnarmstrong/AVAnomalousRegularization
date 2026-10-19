-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.PlaneSobolevPullbackWords
import AVRegularity.CycleWords.PlaneScalarBlochSurjective
public import AVRegularity.Weighted.ScaledDriftNormAbsorption
public import AVRegularity.CycleComparison.Lift.LiftMeanRecursionCongruence
public import AVRegularity.CycleComparison.Lift.ParameterIntegral
import AVRegularity.CycleComparison.Lift.LeftTermsBlockCoefficientBox
import AVRegularity.CycleReference.CorrectorMeanGeometry
import AVRegularity.CycleReference.ChartIntegrandAlgebra
import AVRegularity.CycleReference.SingleModeFlux
import AVRegularity.CycleWords.CellTransitionLipschitz
import AVenhance.Infra.Section3.CorrectorGradient
import Mathlib.Algebra.Ring.IsFormallyReal

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev AVRegularity.EntryWeakProofs
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleWords

/-! Classical Fourier evaluation is a bounded real linear map on each native Sobolev space. -/

def realClassicalEvaluationCLM (K : ℕ) (hK : 2 ≤ K) (x : Vec 2) : TorusHk K ℝ →L[ℝ] ℝ :=
  ({ toFun := fun U => realClassicalLift K U x
     map_add' := fun U V => congrFun (realClassicalLift_add K hK U V) x
     map_smul' := fun c U => congrFun (realClassicalLift_smul K hK c U) x } :
    TorusHk K ℝ →ₗ[ℝ] ℝ).mkContinuous (classicalSobolevConstant 0) (fun U => by
      change ‖realClassicalLift K U x‖ ≤ classicalSobolevConstant 0 * ‖U‖
      simpa only [norm_iteratedFDeriv_zero] using
        realClassicalLift_derivative_norm_le K U 0 (by omega) x)

theorem torusHigherClassicalValue_continuous_native (K : ℕ) (hK : 2 ≤ K) (x : Vec 2) :
    Continuous (fun U : TorusHk K ℂ => torusHigherClassicalValue K U x) := by
  have hr := (realClassicalEvaluationCLM K hK x).continuous.comp
    (mapTorusHkCLM K Complex.reCLM).continuous
  have hi := (realClassicalEvaluationCLM K hK x).continuous.comp
    (mapTorusHkCLM K Complex.imCLM).continuous
  simp only [realClassicalEvaluationCLM, LinearMap.mkContinuous_apply,
    Function.comp_def, mapTorusHkCLM_apply, LinearMap.coe_mk, AddHom.coe_mk] at hr hi
  exact (Complex.continuous_ofReal.comp hr).add
    ((continuous_const : Continuous (fun _ : TorusHk K ℂ => Complex.I)).mul
      (Complex.continuous_ofReal.comp hi))

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! Backward scalar energy curves have the exact reflected weak time equation. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] in
theorem planeWeakCurve_timeReflection {a b : ℝ}
    {u : ℝ → Lp E 2 (volume : Measure (Vec 2))}
    {slice dual : ℝ → PlaneHk Set.univ 1 E}
    (h : PlaneWeakHilbertCurve (-b) (-a) u slice dual) :
    PlaneWeakHilbertCurve a b (fun t => u (-t)) (fun t => slice (-t))
      (fun t => -dual (-t)) := by
  have hin : MapsTo (fun t : ℝ => -t) (Icc a b) (Icc (-b) (-a)) := by
    intro t ht
    exact ⟨neg_le_neg ht.2, neg_le_neg ht.1⟩
  refine ⟨h.trace.comp continuous_neg.continuousOn hin,
    nativeTimeReflection_memLp h.state, (nativeTimeReflection_memLp h.dual_mem).neg, ?_, ?_⟩
  · exact (nativeTimeReflection_measurePreserving a b).quasiMeasurePreserving.ae h.agrees
  · intro s hs t ht hst z
    have he := h.increment (-t) (hin ht) (-s) (hin hs) (neg_le_neg hst) z
    have hrev : (∫ r in s..t, inner ℝ (dual (-r)) z) =
        ∫ r in -t..-s, inner ℝ (dual r) z :=
      intervalIntegral.integral_comp_neg (f := fun r => inner ℝ (dual r) z)
    simp only [inner_neg_left]
    rw [intervalIntegral.integral_neg, hrev]
    linarith only [he]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory UnitAddTorus
open scoped ENNReal Classical
namespace AVRegularity.CycleWords

/-! Genuine bounded transverse coefficient multipliers commute with the longitudinal sector projection. -/

local instance transverseMultiplierCommutationMeasure : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

theorem scalarTorusTransverseProjection_multiplier_basis
    (e : Fin 2) (b : UnitAddTorus (Fin 2) → ℂ) (hb : Measurable b)
    (C : ℝ) (hC : ∀ x, ‖b x‖ ≤ C)
    (hs : ∀ k : Fin 2 → ℤ, k e ≠ 0 → mFourierCoeff b k = 0) (n : Fin 2 → ℤ) :
    scalarTorusTransverseProjection e
      (measurableTorusSymbolMultiplication b hb C hC (mFourierBasis (d := Fin 2) n)) =
    measurableTorusSymbolMultiplication b hb C hC
      (scalarTorusTransverseProjection e (mFourierBasis (d := Fin 2) n)) := by
  have hbase : scalarTorusTransverseProjection e (mFourierBasis (d := Fin 2) n) =
      if n e = 0 then mFourierBasis (d := Fin 2) n else 0 :=
    by
      have h := hilbertBasisSectorProjection_basis (mFourierBasis (d := Fin 2)) {k | k e = 0} n
      by_cases hn : n e = 0
      · simpa only [scalarTorusTransverseProjection, Set.mem_ofPred_eq, ite_eq_left hn] using h
      · simpa only [scalarTorusTransverseProjection, Set.mem_ofPred_eq, ite_eq_right hn] using h
  rw [hbase]
  by_cases hn : n e = 0
  · rw [ite_eq_left hn]
    apply scalarTorusTransverseProjection_eq_self
    intro k hk
    rw [measurableTorusSymbolMultiplication_basis_coeff]
    apply hs
    simpa only [Pi.sub_apply, hn, sub_zero] using hk
  · rw [ite_eq_right hn, map_zero]
    apply (mFourierBasis (d := Fin 2)).repr.injective
    apply lp.ext
    funext k
    rw [mFourierBasis_repr, map_zero]
    change mFourierCoeff (scalarTorusTransverseProjection e
      (measurableTorusSymbolMultiplication b hb C hC (mFourierBasis (d := Fin 2) n))) k = 0
    rw [scalarTorusTransverseProjection_fourierCoeff]
    split_ifs with hk
    · rw [measurableTorusSymbolMultiplication_basis_coeff]
      apply hs
      simpa only [Pi.sub_apply, hk, zero_sub] using neg_ne_zero.mpr hn
    · rfl

theorem scalarTorusTransverseProjection_multiplier_commutes
    (e : Fin 2) (b : UnitAddTorus (Fin 2) → ℂ) (hb : Measurable b)
    (C : ℝ) (hC : ∀ x, ‖b x‖ ≤ C)
    (hs : ∀ k : Fin 2 → ℤ, k e ≠ 0 → mFourierCoeff b k = 0) :
    (scalarTorusTransverseProjection e).comp (measurableTorusSymbolMultiplication b hb C hC) =
      (measurableTorusSymbolMultiplication b hb C hC).comp (scalarTorusTransverseProjection e) := by
  apply sub_eq_zero.mp
  apply hilbertBasis_clm_eq_zero (mFourierBasis (d := Fin 2))
  intro n
  change scalarTorusTransverseProjection e
      (measurableTorusSymbolMultiplication b hb C hC (mFourierBasis (d := Fin 2) n)) -
    measurableTorusSymbolMultiplication b hb C hC
      (scalarTorusTransverseProjection e (mFourierBasis (d := Fin 2) n)) = 0
  exact sub_eq_zero.mpr (scalarTorusTransverseProjection_multiplier_basis e b hb C hC hs n)

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleWords

/-! The word equation has precisely the scalar metric RHS and its preceding-letter divergence
source. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

theorem wordChainRawSpatialRhs_split (hD : 2 ≤ D)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (letters : Fin N → CycleLetter ι h D) (X0 : Vec 2) (δ : ℝ)
    (κ : Fin (N + 1) → ι → ℕ) (v : ℝ → Vec 2 → Vec 2)
    (Uw : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (i : Fin (N + 1) × ι) (φ : PlaneHk Set.univ 1 (h i.2)) (t : ℝ) :
    planeWeakSpatialRhs 1 v (φ.toFunction.jet (valueIndex2 1))
      (fun k => φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩)
      (fun r k => (Uw i r).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩)
      (fun r => wordChainRawFlux G letters X0 δ κ (fun p => Uw p r) i r)
      (fun _ => (0 : PlaneHk Set.univ (κ i.1 i.2)
        (PiLp 2 (fun _ : Fin 2 => h i.2))).toFunction.jet (valueIndex2 (κ i.1 i.2)))
      (fun _ => (0 : PlaneHk Set.univ (κ i.1 i.2) (h i.2)).toFunction.jet
        (valueIndex2 (κ i.1 i.2))) t =ᵐ[volume]
      fun x => planeScalarRawRhsZeroFlux (κ i.1 i.2) (v t) (fun _ => G t) (Uw i t) φ x -
        ∑ k : Fin 2, inner ℝ (wordChainPreviousFlux letters X0 δ κ (fun p => Uw p t) i t x k)
          (φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩ x) := by
  filter_upwards [planeZeroJetRepresentative_ae (E := h i.2) (κ i.1 i.2) (valueIndex2 (κ i.1 i.2)),
    planeZeroJetRepresentative_ae (E := PiLp 2 (fun _ : Fin 2 => h i.2))
      (κ i.1 i.2) (valueIndex2 (κ i.1 i.2))] with x hg hF
  simp only [planeWeakSpatialRhs, hg, hF, PiLp.zero_apply, add_zero, inner_zero_left,
    one_mul, wordChainRawFlux_split hD, PiLp.add_apply,
    inner_add_left, Finset.sum_add_distrib, planeScalarRawRhsZeroFlux]
  ring

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleComparison.Lift AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! First and second native coordinate slots have the literal classical diffusion readout. -/

theorem finiteSmoothPeriodicHk_first_value_ae (K : ℕ) (j : Fin 2)
    (f : Vec 2 → ℂ) (hf : ContDiff ℝ (K + 2 : ℕ∞) f)
    (hp : AVenhance.IsZ2Periodic f) :
    (torusHkValueCLM (torusHigherFirstCLM K j
      (finiteSmoothPeriodicHk (K + 2) f hf hp)) : Vec 2 → ℂ) =ᵐ[
        volume.restrict AVenhance.unitCube] coordinateDerivative j f := by
  have hh := finiteSmoothPeriodicHk_jet_ae (K + 2) f hf hp
    (truncateJetIndex (by omega : K + 1 ≤ K + 2)
      (prefixJetIndex (fun _ : Fin 1 => j) (valueIndex2 K)))
  change (finiteSmoothPeriodicHk (K + 2) f hf hp).val
    (truncateJetIndex (by omega : K + 1 ≤ K + 2)
      (prefixJetIndex (fun _ : Fin 1 => j) (valueIndex2 K))) =ᵐ[_] _
  apply hh.trans
  apply Filter.Eventually.of_forall
  intro x
  simp only [truncateJetIndex, prefixJetIndex, valueIndex2, valueIndex,
    Fin.val_zero, Nat.add_zero, Fin.append_elim0]
  rfl

theorem finiteSmoothPeriodicHk_second_value_ae (K : ℕ) (j k : Fin 2)
    (f : Vec 2 → ℂ) (hf : ContDiff ℝ (K + 2 : ℕ∞) f)
    (hp : AVenhance.IsZ2Periodic f) :
    (torusHkValueCLM (torusHigherSecondCLM K j k
      (finiteSmoothPeriodicHk (K + 2) f hf hp)) : Vec 2 → ℂ) =ᵐ[
        volume.restrict AVenhance.unitCube]
      coordinateDerivative k (coordinateDerivative j f) := by
  have hh := finiteSmoothPeriodicHk_jet_ae (K + 2) f hf hp
    (prefixJetIndex (K := K + 1) (r := 1) (fun _ : Fin 1 => j)
      (prefixJetIndex (K := K) (r := 1) (fun _ : Fin 1 => k) (valueIndex2 K)))
  change (finiteSmoothPeriodicHk (K + 2) f hf hp).val
    (prefixJetIndex (K := K + 1) (r := 1) (fun _ : Fin 1 => j)
      (prefixJetIndex (K := K) (r := 1) (fun _ : Fin 1 => k) (valueIndex2 K))) =ᵐ[_] _
  apply hh.trans
  apply Filter.Eventually.of_forall
  intro x
  simp only [prefixJetIndex, valueIndex2, valueIndex, Fin.val_zero, Nat.add_zero,
    Fin.append_elim0]
  change orderedDerivative (Fin.append (fun _ : Fin 1 => j) (fun _ : Fin 1 => k)) f x = _
  rw [orderedDerivative_append]
  rfl

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Finite parameter integrals preserve normalized polynomial coefficient budgets. -/

theorem integralMultilinear_scaled_normalized_jet_budget (r J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {T : Type*} [MeasurableSpace T]
      (μ : Measure T) [IsFiniteMeasure μ]
      (a : T → Vec 2 → ContinuousMultilinearMap ℝ (fun _ : Fin r => Vec 2) ℝ), ∀ (ϖ ρ B : ℝ),
      (∀ z, Measurable (fun t => a t z (fun _ => ϖ • z))) →
      (∀ t, ContDiff ℝ (J : ℕ) (a t)) →
      0 < ϖ → 0 < ρ → ρ * ϖ ≤ 1 → 0 ≤ B →
      (∀ t (w : DerivativeWord2 r) j, j ≤ J → ∀ z,
        ρ ^ j * ‖iteratedFDeriv ℝ j (fun z => a t z (fun i => basisVec (w i))) z‖ ≤ B) →
      ∀ j ≤ J, ∀ z,
        ρ ^ j * ‖iteratedFDeriv ℝ j (fun z => ∫ t, a t z (fun _ => ϖ • z) ∂μ) z‖ ≤
          C * B * μ.real Set.univ * polynomialMomentRoot ϖ z ^ r := by
  obtain ⟨C, hC, hb⟩ := variableMultilinear_scaled_normalized_jet_budget r J
  refine ⟨2 ^ J * C, by positivity, ?_⟩
  intro T _ μ _ a ϖ ρ B hm ha hϖ hρ hscale hB hab j hj z
  let f := fun t (z : Vec 2) => a t z (fun _ => ϖ • z)
  have hf (t : T) : ContDiff ℝ (J : ℕ∞) (f t) :=
    (Weighted.multilinear_diagonal_contDiff J (a t) (ha t) ϖ).of_le (by exact_mod_cast le_refl J)
  let price := fun k => (C * B * (1 + 2 * |ϖ|) ^ r) / ρ ^ k
  have hp (k : ℕ) : 0 ≤ price k := by dsimp only [price]; positivity
  have hg : ∀ k ≤ J, ∀ t x, ‖iteratedFDeriv ℝ k (f t) x‖ ≤ price k * (1 + ‖x‖) ^ r := by
    intro k hk t x
    dsimp only [price]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (pow_pos hρ k)).mpr
    have hh := hb a ha ϖ ρ B hϖ hρ.le hscale hB hab t k hk x
    have hr := pow_le_pow_left₀ (by unfold polynomialMomentRoot; positivity)
      (polynomialMomentRoot_growth_le ϖ x) r
    rw [mul_pow] at hr
    have hh' := hh.trans (mul_le_mul_of_nonneg_left hr (mul_nonneg hC hB))
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hh'
  have hi := parameter_integral_normalized_jet_le μ J f hm hf price hp r hg
    ρ (C * B * polynomialMomentRoot ϖ z ^ r) hρ j hj z
    (fun t => hb a ha ϖ ρ B hϖ hρ.le hscale hB hab t j hj z)
  apply hi.trans
  have hn : 0 ≤ C * B * polynomialMomentRoot ϖ z ^ r * μ.real Set.univ := by
    unfold polynomialMomentRoot
    positivity
  convert mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj) hn using 1 <;> ring

/-! Factorial weighted word budgets for native Sobolev renewals. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeSobolev_pullback_weighted_word_budget {K : ℕ} (U V : PlaneHk Set.univ K E)
    (X : Vec 2 → Vec 2) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hμ : MeasurePreserving X volume volume) (B : ℕ → ℝ)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ z, ‖iteratedFDeriv ℝ j X z‖ ≤ B j)
    (hv : planeValue V =ᵐ[volume] planeValue U ∘ X)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (n : ℕ) (hn : n ≤ K)
    (w : DerivativeWord2 n) :
    ∀ᵐ z ∂volume, factorialWeight r n * ‖planeJetOrder V n w z‖ ^ 2 ≤
      (Fintype.card (Σ c : OrderedFinpartition n, DerivativeWord2 c.length) : ℝ) *
      ∑ a : (Σ c : OrderedFinpartition n, DerivativeWord2 c.length),
        (∏ i : Fin a.1.length, B (a.1.partSize i)) ^ 2 *
          (factorialWeight r a.1.length * ‖planeJetOrder U a.1.length a.2 (X z)‖ ^ 2) := by
  filter_upwards [planeSobolev_pullback_word_budget U V X hX hμ B hb hv n hn w] with z hz
  let J := Σ c : OrderedFinpartition n, DerivativeWord2 c.length
  let c : J → ℝ := fun a => ∏ i : Fin a.1.length, B (a.1.partSize i)
  let u : J → ℝ := fun a => ‖planeJetOrder U a.1.length a.2 (X z)‖
  let j : J → ℕ := fun a => a.1.length
  have hj : ∀ a : J, j a ≤ n := fun a => a.1.length_le
  exact finite_weighted_square_budget c u j n r
    ‖planeJetOrder V n w z‖ hr hr1 (norm_nonneg _) hj hz
end

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleComparison.Lift AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Differentiated native diffusion coordinates are the derivatives of the same smooth state. -/

theorem finiteSmoothPeriodicHk_ordered_first_value_ae {K r : ℕ}
    (w : DerivativeWord2 r) (j : Fin 2) (f : Vec 2 → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f) :
    (torusHkValueCLM (derivativeTorusHk (K := K) w
      (torusHigherFirstCLM (K + r) j
        (finiteSmoothPeriodicHk (K + r + 2) f (hf.of_le (by simp)) hp))) : Vec 2 → ℂ) =ᵐ[
      volume.restrict AVenhance.unitCube] coordinateDerivative j (orderedDerivative w f) := by
  let a := truncateJetIndex (by omega : K + r + 1 ≤ K + r + 2)
    (prefixJetIndex (fun _ : Fin 1 => j) (prefixJetIndex w (valueIndex2 K)))
  have hh := finiteSmoothPeriodicHk_jet_ae (K + r + 2) f (hf.of_le (by simp)) hp a
  change (finiteSmoothPeriodicHk (K + r + 2) f (hf.of_le (by simp)) hp).val a =ᵐ[_] _
  apply hh.trans
  apply Filter.Eventually.of_forall
  intro x
  have he : orderedDerivative a.2 f = orderedDerivative w (coordinateDerivative j f) := by
    dsimp only [a, truncateJetIndex, prefixJetIndex, valueIndex2, valueIndex]
    simp only [Fin.val_zero, Nat.add_zero, Fin.append_elim0]
    rw [orderedDerivative_append]
    rfl
  rw [he, orderedDerivative_coordinate_commute w j f hf]

theorem finiteSmoothPeriodicHk_ordered_second_value_ae {K r : ℕ}
    (w : DerivativeWord2 r) (j k : Fin 2) (f : Vec 2 → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f) :
    (torusHkValueCLM (derivativeTorusHk (K := K) w
      (torusHigherSecondCLM (K + r) j k
        (finiteSmoothPeriodicHk (K + r + 2) f (hf.of_le (by simp)) hp))) : Vec 2 → ℂ) =ᵐ[
      volume.restrict AVenhance.unitCube]
      coordinateDerivative k (coordinateDerivative j (orderedDerivative w f)) := by
  let a := prefixJetIndex (K := K + r + 1) (r := 1) (fun _ : Fin 1 => j)
    (prefixJetIndex (K := K + r) (r := 1) (fun _ : Fin 1 => k)
      (prefixJetIndex w (valueIndex2 K)))
  have hh := finiteSmoothPeriodicHk_jet_ae (K + r + 2) f (hf.of_le (by simp)) hp a
  change (finiteSmoothPeriodicHk (K + r + 2) f (hf.of_le (by simp)) hp).val a =ᵐ[_] _
  apply hh.trans
  apply Filter.Eventually.of_forall
  intro x
  have he : orderedDerivative a.2 f =
      orderedDerivative w (coordinateDerivative k (coordinateDerivative j f)) := by
    dsimp only [a, prefixJetIndex, valueIndex2, valueIndex]
    simp only [Fin.val_zero, Nat.add_zero, Fin.append_elim0]
    rw [orderedDerivative_append, orderedDerivative_append]
    rfl
  rw [he, orderedDerivative_coordinate_commute w k _ (coordinateDerivative_contDiff j f hf),
    orderedDerivative_coordinate_commute w j f hf]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleWords

/-! Smooth periodic spatial representatives of measurable native values are jointly measurable. -/

theorem torusHigher_periodic_representative_jointly_stronglyMeasurable
    (K : ℕ) (hK : 2 ≤ K) (U : ℝ → TorusHk K ℂ)
    (hU : StronglyMeasurable U) (f : ℝ → Vec 2 → ℂ)
    (hf : ∀ t, Continuous (f t)) (hp : ∀ t, AVenhance.IsZ2Periodic (f t))
    (he : ∀ t, f t =ᵐ[volume.restrict AVenhance.unitCube]
      (torusHkValueCLM (U t) : Vec 2 → ℂ)) :
    StronglyMeasurable (fun p : ℝ × Vec 2 => f p.1 p.2) := by
  have hrep : ∀ t, torusHigherClassicalValue K (U t) = f t := by
    intro t
    exact periodicContinuous_eq_of_cell_ae _ _
      (torusHigherClassicalValue_contDiff K 0 (by omega) (U t)).continuous (hf t)
      (torusHigherClassicalValue_periodic K (U t)) (hp t)
      ((torusHigherClassicalValue_ae K hK (U t)).trans (he t).symm)
  have hm : ∀ x, StronglyMeasurable (fun t => f t x) := by
    intro x
    have h := (torusHigherClassicalValue_continuous_native K hK x).comp_stronglyMeasurable hU
    have heq : (fun t => torusHigherClassicalValue K (U t) x) = (fun t => f t x) := by
      funext t
      exact congrFun (hrep t) x
    rw [← heq]
    exact h
  have hj := stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
    (u := fun x t => f t x) hf hm
  exact hj.comp_measurable measurable_swap

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! The future-memory coordinate in cell variables, normalized by the macroscopic radius. -/

def adjointCellCoordinate (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ)
    (ν B T : ℝ) (yc : Vec 2) (t : ℝ) (z : Vec 2) (j : Fin 2) : ℝ :=
  (adjointCoordinate α q Λ ζ m ν (ocEll q Λ m ν ^ 2 * t)
    (yc + ocEpsilon q Λ m • z) j - yc j) / Real.sqrt (B * T)

def adjointCellPolynomialWeight (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ)
    (ν B T : ℝ) (yc : Vec 2) (n : ℕ) (t : ℝ) (z : Vec 2) : ℝ :=
  (1 + adjointCellCoordinate α q Λ ζ m ν B T yc t z 0 ^ 2 +
    adjointCellCoordinate α q Λ ζ m ν B T yc t z 1 ^ 2) ^ n

theorem adjointCellCoordinate_joint_contDiff {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν B T : ℝ) (yc : Vec 2) (j : Fin 2) (n : ℕ) :
    ContDiff ℝ n (fun p : ℝ × Vec 2 => adjointCellCoordinate α q Λ ζ m ν B T yc p.1 p.2 j) := by
  have hmap : ContDiff ℝ n (fun p : ℝ × Vec 2 =>
      (ocEll q Λ m ν ^ 2 * p.1, yc + ocEpsilon q Λ m • p.2)) := by fun_prop
  exact (((adjointCoordinate_joint_contDiff (α := α) (q := q) (m := m) hΛ hζ ν j n).comp hmap).sub contDiff_const).div_const _

theorem adjointCellPolynomialWeight_joint_contDiff {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν B T : ℝ) (yc : Vec 2) (n r : ℕ) :
    ContDiff ℝ r (fun p : ℝ × Vec 2 => adjointCellPolynomialWeight α q Λ ζ m ν B T yc n p.1 p.2) := by
  have h0 := adjointCellCoordinate_joint_contDiff (α := α) (q := q) (m := m) hΛ hζ ν B T yc 0 r
  have h1 := adjointCellCoordinate_joint_contDiff (α := α) (q := q) (m := m) hΛ hζ ν B T yc 1 r
  exact ((contDiff_const.add (h0.pow 2)).add (h1.pow 2)).pow n

theorem adjointCellPolynomialWeight_pos (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ)
    (ν B T : ℝ) (yc : Vec 2) (n : ℕ) (t : ℝ) (z : Vec 2) :
    0 < adjointCellPolynomialWeight α q Λ ζ m ν B T yc n t z := by
  unfold adjointCellPolynomialWeight
  positivity

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleComparison.Lift AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Differentiated diffusion coordinates equal the actual H2 coordinates of the differentiated state. -/

theorem finiteSmoothPeriodicHk_ordered_H2_base {r : ℕ}
    (w : DerivativeWord2 r) (f : Vec 2 → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f) :
    cellH2BaseCLM (finiteSmoothPeriodicHk 2 (orderedDerivative w f)
      (orderedDerivative_contDiff w 2 f (hf.of_le (by simp)))
      (orderedDerivative_periodic w f (hf.of_le (by simp)) hp)) =
    derivativeTorusHk (K := 1) w
      (finiteSmoothPeriodicHk (1 + r) f (hf.of_le (by simp)) hp) := by
  rw [finiteSmoothPeriodicHk_derivative (K := 1) w f (hf.of_le (by simp)) hp]
  apply TorusHk.ext_value
  apply Lp.ext
  have hl := finiteSmoothPeriodicHk_jet_ae 2 (orderedDerivative w f)
    (orderedDerivative_contDiff w 2 f (hf.of_le (by simp)))
    (orderedDerivative_periodic w f (hf.of_le (by simp)) hp) (valueIndex2 2)
  have hr := finiteSmoothPeriodicHk_jet_ae 1 (orderedDerivative w f)
    (orderedDerivative_contDiff w 1 f (hf.of_le (by simp)))
    (orderedDerivative_periodic w f (hf.of_le (by simp)) hp) (valueIndex2 1)
  exact hl.trans hr.symm

theorem finiteSmoothPeriodicHk_ordered_truncate_value {K r : ℕ}
    (w : DerivativeWord2 r) (f : Vec 2 → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f) :
    torusHkValueCLM (derivativeTorusHk (K := K) w
      (truncateTorusHk (by omega : K + r ≤ K + r + 2)
        (finiteSmoothPeriodicHk (K + r + 2) f (hf.of_le (by simp)) hp))) =
      torusHkValueCLM (finiteSmoothPeriodicHk 2 (orderedDerivative w f)
        (orderedDerivative_contDiff w 2 f (hf.of_le (by simp)))
        (orderedDerivative_periodic w f (hf.of_le (by simp)) hp)) := by
  apply Lp.ext
  let a := truncateJetIndex (by omega : K + r ≤ K + r + 2)
    (prefixJetIndex w (valueIndex2 K))
  have hl := finiteSmoothPeriodicHk_jet_ae (K + r + 2) f (hf.of_le (by simp)) hp a
  have hr := finiteSmoothPeriodicHk_jet_ae 2 (orderedDerivative w f)
    (orderedDerivative_contDiff w 2 f (hf.of_le (by simp)))
    (orderedDerivative_periodic w f (hf.of_le (by simp)) hp) (valueIndex2 2)
  change (finiteSmoothPeriodicHk (K + r + 2) f (hf.of_le (by simp)) hp).val a =ᵐ[_] _
  apply hl.trans
  apply Filter.EventuallyEq.trans _ hr.symm
  apply Filter.Eventually.of_forall
  intro x
  simp only [a, truncateJetIndex, prefixJetIndex, valueIndex2, valueIndex,
    Fin.val_zero, Nat.add_zero, Fin.append_elim0]
  rfl

theorem finiteSmoothPeriodicHk_ordered_first_value {K r : ℕ}
    (w : DerivativeWord2 r) (j : Fin 2) (f : Vec 2 → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f) :
    torusHkValueCLM (derivativeTorusHk (K := K) w
      (torusHigherFirstCLM (K + r) j
        (finiteSmoothPeriodicHk (K + r + 2) f (hf.of_le (by simp)) hp))) =
      torusHkValueCLM (torusHigherFirstCLM 0 j
        (finiteSmoothPeriodicHk 2 (orderedDerivative w f)
          (orderedDerivative_contDiff w 2 f (hf.of_le (by simp)))
          (orderedDerivative_periodic w f (hf.of_le (by simp)) hp))) := by
  apply Lp.ext
  exact (finiteSmoothPeriodicHk_ordered_first_value_ae w j f hf hp).trans
    (finiteSmoothPeriodicHk_first_value_ae 0 j (orderedDerivative w f) _ _).symm

theorem finiteSmoothPeriodicHk_ordered_second_value {K r : ℕ}
    (w : DerivativeWord2 r) (j k : Fin 2) (f : Vec 2 → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f) :
    torusHkValueCLM (derivativeTorusHk (K := K) w
      (torusHigherSecondCLM (K + r) j k
        (finiteSmoothPeriodicHk (K + r + 2) f (hf.of_le (by simp)) hp))) =
      torusHkValueCLM (torusHigherSecondCLM 0 j k
        (finiteSmoothPeriodicHk 2 (orderedDerivative w f)
          (orderedDerivative_contDiff w 2 f (hf.of_le (by simp)))
          (orderedDerivative_periodic w f (hf.of_le (by simp)) hp))) := by
  apply Lp.ext
  exact (finiteSmoothPeriodicHk_ordered_second_value_ae w j k f hf hp).trans
    (finiteSmoothPeriodicHk_second_value_ae 0 j k (orderedDerivative w f) _ _).symm

end AVRegularity.CycleWords
end

section
open Homogenization
namespace AVRegularity.CycleWords

/-! Smooth time and space slices of the normalized cell coordinates. -/

theorem adjointCellCoordinate_space_contDiff {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν B T : ℝ) (yc : Vec 2)
    (t : ℝ) (j : Fin 2) (n : ℕ) :
    ContDiff ℝ n (fun z => adjointCellCoordinate α q Λ ζ m ν B T yc t z j) :=
  (adjointCellCoordinate_joint_contDiff hΛ hζ ν B T yc j n).comp
    (contDiff_const.prodMk contDiff_id)

theorem adjointCellCoordinate_time_contDiff {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν B T : ℝ) (yc z : Vec 2)
    (j : Fin 2) (n : ℕ) :
    ContDiff ℝ n (fun t => adjointCellCoordinate α q Λ ζ m ν B T yc t z j) :=
  (adjointCellCoordinate_joint_contDiff hΛ hζ ν B T yc j n).comp
    (contDiff_id.prodMk contDiff_const)

theorem adjointCellPolynomialWeight_space_contDiff {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν B T : ℝ) (yc : Vec 2)
    (n : ℕ) (t : ℝ) (r : ℕ) :
    ContDiff ℝ r (fun z => adjointCellPolynomialWeight α q Λ ζ m ν B T yc n t z) := by
  have h0 := adjointCellCoordinate_space_contDiff (α := α) (q := q) (m := m)
    hΛ hζ ν B T yc t 0 r
  have h1 := adjointCellCoordinate_space_contDiff (α := α) (q := q) (m := m)
    hΛ hζ ν B T yc t 1 r
  exact ((contDiff_const.add (h0.pow 2)).add (h1.pow 2)).pow n

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! Exact spatial and temporal derivative scaling in cell coordinates. -/

theorem affine_cell_hasFDerivAt (yc : Vec 2) (e : ℝ) (z : Vec 2) :
    HasFDerivAt (fun x : Vec 2 => yc + e • x) (e • ContinuousLinearMap.id ℝ (Vec 2)) z := by
  exact ((hasFDerivAt_id z).const_smul e).const_add yc

theorem affine_cell_gradient (f : Vec 2 → ℝ) (hf : Differentiable ℝ f)
    (yc : Vec 2) (e R : ℝ) (z : Vec 2) (i : Fin 2) :
    fderiv ℝ (fun x : Vec 2 => f (yc + e • x) / R) z (basisVec i) =
      (e / R) * fderiv ℝ f (yc + e • z) (basisVec i) := by
  have hd : HasFDerivAt (fun x : Vec 2 => f (yc + e • x) / R)
      (R⁻¹ • ((fderiv ℝ f (yc + e • z)).comp
        (e • ContinuousLinearMap.id ℝ (Vec 2)))) z := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_comm] using
      ((hf (yc + e • z)).hasFDerivAt.comp z (affine_cell_hasFDerivAt yc e z)).const_mul R⁻¹
  rw [hd.fderiv]
  simp [div_eq_mul_inv]
  ring

theorem affine_cell_time_derivative (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (L c R t : ℝ) :
    deriv (fun s => (f (L * s) - c) / R) t = (L / R) * deriv f (L * t) := by
  have hd := (((hf (L * t)).hasDerivAt.comp t
    ((hasDerivAt_id t).const_mul L)).sub_const c).div_const R
  have he : deriv (fun s => (f (L * s) - c) / R) t = deriv f (L * t) * (L * 1) / R := by
    simpa only [Function.comp_def] using hd.deriv
  rw [he]
  ring

/-! Second spatial derivative scaling of a smooth cell pullback. -/

theorem affine_cell_second_derivative (f : Vec 2 → ℝ) (hf : ContDiff ℝ 2 f)
    (yc : Vec 2) (e R : ℝ) (z : Vec 2) (i : Fin 2) :
    fderiv ℝ (fun x => fderiv ℝ (fun y : Vec 2 => f (yc + e • y) / R)
      x (basisVec i)) z (basisVec i) =
      (e ^ 2 / R) * fderiv ℝ (fun x => fderiv ℝ f x (basisVec i))
        (yc + e • z) (basisVec i) := by
  have hfd := hf.differentiable (by norm_num)
  have he := funext (fun x => affine_cell_gradient f hfd yc e R x i)
  rw [he]
  have hd : Differentiable ℝ (fun x => fderiv ℝ f x (basisVec i)) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) |>.clm_apply
      (differentiable_const _)
  have ha : Differentiable ℝ (fun x : Vec 2 => fderiv ℝ f (yc + e • x) (basisVec i)) :=
    hd.comp (by fun_prop)
  rw [fderiv_const_mul (ha z)]
  have hh := affine_cell_gradient (fun x => fderiv ℝ f x (basisVec i)) hd yc e 1 z i
  simp only [div_one] at hh
  simp only [smul_apply, smul_eq_mul]
  rw [hh]
  ring

theorem affine_cell_laplacian (f : Vec 2 → ℝ) (hf : ContDiff ℝ 2 f)
    (yc : Vec 2) (e R : ℝ) (z : Vec 2) :
    (∑ i : Fin 2, fderiv ℝ (fun x => fderiv ℝ (fun y : Vec 2 => f (yc + e • y) / R)
      x (basisVec i)) z (basisVec i)) =
      (e ^ 2 / R) * ∑ i : Fin 2, fderiv ℝ (fun x => fderiv ℝ f x (basisVec i))
        (yc + e • z) (basisVec i) := by
  simp_rw [affine_cell_second_derivative f hf yc e R z]
  exact (Finset.mul_sum _ _ _).symm

/-! The literal rescaled cell drift has zero classical divergence. -/

theorem shear_diagonal_derivative_vanishes {α q : ℝ} {Λ m : ℕ} {k : ℤ} (hk : Odd k)
    (y : Vec 2) (i : Fin 2) :
    fderiv ℝ (fun z => ocShearVel α q Λ m k z i) y (basisVec i) = 0 := by
  rcases CycleReference.odd_int_mod_four hk with h1 | h3
  · simp only [CycleReference.ocShearVel_horizontal h1]
    fin_cases i
    · change fderiv ℝ (fun _ : Vec 2 => (0 : ℝ)) y (basisVec 0) = 0
      simp
    · change spaceGrad (fun z => _ * Real.cos (_ * z 0)) y 1 = 0
      rw [AVenhance.Infra.Section3.CorrectorGradient.spaceGrad_cosCoordinate]
      norm_num
  · simp only [CycleReference.ocShearVel_vertical h3]
    fin_cases i
    · change spaceGrad (fun z => _ * Real.cos (_ * z 1)) y 0 = 0
      rw [AVenhance.Infra.Section3.CorrectorGradient.spaceGrad_cosCoordinate]
      norm_num
    · change fderiv ℝ (fun _ : Vec 2 => (0 : ℝ)) y (basisVec 1) = 0
      simp

theorem cellDrift_component_diagonal_derivative_zero {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν t : ℝ) (yc z : Vec 2) (j : Fin 2) :
    fderiv ℝ (fun x => ocCellDrift α q Λ ζ m ν yc t x j) z (basisVec j) = 0 := by
  classical
  by_cases hp : ∃ k : ℤ, Odd k ∧ ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t) ≠ 0
  · obtain ⟨k, hk, hp⟩ := hp
    have he : (fun x => ocCellDrift α q Λ ζ m ν yc t x j) =
        fun x => (ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m *
          ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t)) *
          ocShearVel α q Λ m k (yc + ocEpsilon q Λ m • x) j := by
      funext x
      simp only [ocCellDrift, CycleReference.pulseStreamVel_eq_active hΛ hζ hk hp,
        Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [he]
    have hd := (ocShearVel_component_contDiff (α := α) (q := q) (Λ := Λ) (m := m) hk j).differentiable (by simp)
    have ha : Differentiable ℝ (fun x : Vec 2 => ocShearVel α q Λ m k (yc + ocEpsilon q Λ m • x) j) :=
      hd.comp (by fun_prop)
    rw [fderiv_const_mul (ha z)]
    simp only [smul_apply, smul_eq_mul]
    have hh := affine_cell_gradient _ hd yc (ocEpsilon q Λ m) 1 z j
    simp only [div_one] at hh
    rw [hh, shear_diagonal_derivative_vanishes hk, mul_zero, mul_zero]
  · have hz : ∀ k : ℤ, Odd k → ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t) = 0 := by
      intro k hk
      by_contra hn
      exact hp ⟨k, hk, hn⟩
    have he : (fun x => ocCellDrift α q Λ ζ m ν yc t x j) = fun _ => 0 := by
      funext x
      simp only [ocCellDrift, CycleReference.pulseStreamVel_eq_zero_of_quiet hz, smul_zero, Pi.zero_apply]
    rw [he]
    simp

theorem cellDrift_divergence_zero {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν t : ℝ) (yc z : Vec 2) :
    (∑ j : Fin 2, fderiv ℝ (ocCellDrift α q Λ ζ m ν yc t) z (basisVec j) j) = 0 := by
  have hd := (cellDrift_spatial_contDiff (α := α) (q := q) (m := m) hΛ hζ ν t yc).differentiable (by simp)
  apply Finset.sum_eq_zero
  intro j _
  have hh := cellDrift_component_diagonal_derivative_zero (α := α) (q := q) (m := m) hΛ hζ ν t yc z j
  rw [fderiv_apply (hd z) j] at hh
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] using hh

/-! The variable metric is removed from the weight defect by its exact flux correction. -/

def metricCorrectionFlux (W : Vec 2 → ℝ) (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (z : Vec 2) (k : Fin 2) : ℝ :=
  (∑ j : Fin 2, G z k j * fderiv ℝ W z (basisVec j)) - fderiv ℝ W z (basisVec k)

theorem weight_gradient_differentiable (W : Vec 2 → ℝ) (hW : ContDiff ℝ 2 W) (i : Fin 2) :
    Differentiable ℝ (fun z => fderiv ℝ W z (basisVec i)) :=
  (hW.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) |>.clm_apply
    (differentiable_const _)

theorem metricCorrectionFlux_divergence (W : Vec 2 → ℝ) (hW : ContDiff ℝ 2 W)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ k j, Differentiable ℝ (fun z => G z k j)) (z : Vec 2) :
    (∑ k : Fin 2, fderiv ℝ (fun x => ∑ j : Fin 2, G x k j *
      fderiv ℝ W x (basisVec j)) z (basisVec k)) =
      (∑ k : Fin 2, fderiv ℝ (fun x => fderiv ℝ W x (basisVec k)) z (basisVec k)) +
      ∑ k : Fin 2, fderiv ℝ (fun x => metricCorrectionFlux W G x k) z (basisVec k) := by
  have hf : ∀ k, Differentiable ℝ (fun x => ∑ j : Fin 2, G x k j *
      fderiv ℝ W x (basisVec j)) := fun k =>
    Differentiable.fun_sum (fun j _ => (hG k j).mul (weight_gradient_differentiable W hW j))
  unfold metricCorrectionFlux
  simp_rw [fderiv_fun_sub (hf _ z) (weight_gradient_differentiable W hW _ z)]
  simp only [sub_apply, Fin.sum_univ_two]
  ring

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Native witnesses for a normalized graph mode yield witnesses for its literal correction. -/

theorem torusHigher_correction_witness (K : ℕ) (u : ComplexCellL2) (B : ℝ)
    (h : ∃ W : TorusHk K ℂ, torusHkValueCLM W = u + cellConstantCLM 1 ∧ ‖W‖ ^ 2 ≤ B) :
    ∃ W : TorusHk K ℂ, torusHkValueCLM W = u ∧
      ‖W‖ ≤ Real.sqrt B + ‖torusHigherConstant K 1‖ := by
  obtain ⟨V, hv, hb⟩ := h
  refine ⟨V - torusHigherConstant K 1, ?_, ?_⟩
  · rw [map_sub, torusHigherConstant_value, hv, add_sub_cancel_right]
  · exact (norm_sub_le _ _).trans
      (add_le_add (Real.le_sqrt_of_sq_le hb) le_rfl)

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! Exact first derivative formulas for the normalized adjoint coordinate. -/

theorem adjointCellCoordinate_gradient {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν B T : ℝ) (yc : Vec 2)
    (t : ℝ) (z : Vec 2) (j i : Fin 2) :
    fderiv ℝ (fun x => adjointCellCoordinate α q Λ ζ m ν B T yc t x j) z (basisVec i) =
      (ocEpsilon q Λ m / Real.sqrt (B * T)) *
        fderiv ℝ (fun y => adjointCoordinate α q Λ ζ m ν (ocEll q Λ m ν ^ 2 * t) y j)
          (yc + ocEpsilon q Λ m • z) (basisVec i) := by
  have hf := adjointCoordinate_space_contDiff (α := α) (q := q) (m := m) hΛ hζ ν
    (ocEll q Λ m ν ^ 2 * t) j 1
  have hd := hf.differentiable (by norm_num)
  have hh := affine_cell_gradient
    (fun y => adjointCoordinate α q Λ ζ m ν (ocEll q Λ m ν ^ 2 * t) y j - yc j)
    (hd.sub_const _) yc (ocEpsilon q Λ m) (Real.sqrt (B * T)) z i
  simpa only [adjointCellCoordinate, fderiv_sub_const] using hh

theorem adjointCellCoordinate_time_derivative {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν B T : ℝ) (yc : Vec 2)
    (t : ℝ) (z : Vec 2) (j : Fin 2) :
    deriv (fun s => adjointCellCoordinate α q Λ ζ m ν B T yc s z j) t =
      (ocEll q Λ m ν ^ 2 / Real.sqrt (B * T)) *
        deriv (fun s => adjointCoordinate α q Λ ζ m ν s (yc + ocEpsilon q Λ m • z) j)
          (ocEll q Λ m ν ^ 2 * t) := by
  have hf := adjointCoordinate_time_contDiff (α := α) (q := q) (m := m) hΛ hζ ν
    (yc + ocEpsilon q Λ m • z) j 1
  exact affine_cell_time_derivative _ (hf.differentiable (by norm_num)) _ _ _ _

end AVRegularity.CycleWords
end

section
open Homogenization Set
namespace AVRegularity.CycleWords

/-! The actual clipped chart flux satisfies the cutoff defect inequality. -/

open AVRegularity.Weighted

theorem cellMetric_chartWeights_clipped_flux_defect
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {t₀ S ϖ : ℝ} {zc : Vec 2} {M : ℕ} {Cw : ℕ → ℝ}
    (W : ChartWeights G v t₀ S ϖ zc M Cw) (m : ℕ) (hm : m ≤ M)
    (t : ℝ) (ht : t ∈ Icc t₀ (t₀ + S)) (B : ℝ) (hB : 0 < B)
    (hCell : IsCellMetric G)
    (hv : ContDiff ℝ 1 (v t))
    (hdiv : ∀ x, ∑ j : Fin 2, fderiv ℝ (v t) x (basisVec j) j = 0)
    (hGs : ∀ x, (G t x).IsSymm)
    (hG : ∀ i j : Fin 2, ContDiff ℝ 1 (fun x => G t x i j)) :
    let q := fun x => clipWeight B (W.W m t x)
    let Φ := fun i x => clipWeightDeriv B (W.W m t x) * W.Phi m t x i
    (∀ i, ContDiff ℝ 1 (scalarChartFlux (v t) (G t) q Φ i)) ∧
    (∀ x, deriv (fun s => clipWeight B (W.W m s x)) t +
      (∑ i : Fin 2, fderiv ℝ (scalarChartFlux (v t) (G t) q Φ i) x (basisVec i)) ≤
        2 * W.lam m * q x) := by
  let q := fun x => clipWeight B (W.W m t x)
  let Φ := fun i x => clipWeightDeriv B (W.W m t x) * W.Phi m t x i
  have hw : ContDiff ℝ 2 (fun x => W.W m t x) := by
    convert (W.smooth m hm).1.comp (contDiff_const.prodMk contDiff_id) using 1 <;> rfl
  have hq : ContDiff ℝ 2 q :=
    (contDiff_const.mul hw).div (contDiff_const.add hw)
      (fun x => ne_of_gt (add_pos hB (W.pos m hm t x)))
  have hΦ i : ContDiff ℝ 1 (Φ i) := by
    have hφ : ContDiff ℝ 1 (fun x => W.Phi m t x i) := by
      have htφ : ContDiff ℝ 1 (fun x => W.Phi m t x) := by
        convert (W.smooth m hm).2.comp (contDiff_const.prodMk contDiff_id) using 1 <;> rfl
      exact contDiff_pi.mp htφ i
    have hc : ContDiff ℝ 1 (fun x => clipWeightDeriv B (W.W m t x)) := by
      exact contDiff_const.div ((contDiff_const.add (hw.of_le (by norm_num))).pow 2)
        (fun x => pow_ne_zero 2 (ne_of_gt (add_pos hB (W.pos m hm t x))))
    exact hc.mul hφ
  refine ⟨fun i => scalarChartFlux_contDiff (v t) hv (G t) hG q hq Φ hΦ i, ?_⟩
  intro x
  rw [scalarChartFlux_divergence (v t) hv hdiv (G t) hG hGs q hq Φ hΦ x]
  have hd := cellMetric_chartWeights_clipped_defect W m hm t ht x B hB hCell 0
    (by simpa using hG)
  change deriv (fun s => clipWeight B (W.W m s x)) t +
    (∑ i : Fin 2, v t x i * fderiv ℝ q x (basisVec i)) +
    (∑ i : Fin 2, fderiv ℝ (fun y => ∑ j : Fin 2,
      G t y i j * fderiv ℝ q y (basisVec j)) x (basisVec i)) ≤
    2 * W.lam m * q x + ∑ i : Fin 2, fderiv ℝ (Φ i) x (basisVec i) at hd
  linarith only [hd]

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! Joint regularity of spatial derivative slices of a smooth space-time field. -/

theorem joint_spatial_gradient_eq (F : ℝ × Vec 2 → ℝ) (hF : ContDiff ℝ 2 F)
    (t : ℝ) (z : Vec 2) (i : Fin 2) :
    fderiv ℝ (fun x => F (t, x)) z (basisVec i) = fderiv ℝ F (t, z) (0, basisVec i) := by
  have hm := (hasFDerivAt_const (𝕜 := ℝ) t z).prodMk (hasFDerivAt_id (𝕜 := ℝ) z)
  have hh := (hF.differentiable (by norm_num) (t, z)).hasFDerivAt.comp z hm
  change fderiv ℝ (F ∘ Prod.mk t) z (basisVec i) = _
  rw [hh.fderiv]
  simp

theorem joint_spatial_gradient_contDiff (F : ℝ × Vec 2 → ℝ) (hF : ContDiff ℝ 2 F) (i : Fin 2) :
    ContDiff ℝ 1 (fun p : ℝ × Vec 2 => fderiv ℝ (fun x => F (p.1, x)) p.2 (basisVec i)) := by
  simp_rw [joint_spatial_gradient_eq F hF]
  exact (hF.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

theorem metricCorrectionFlux_joint_contDiff (W : ℝ → Vec 2 → ℝ)
    (hW : ContDiff ℝ 2 (fun p : ℝ × Vec 2 => W p.1 p.2))
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ k j, ContDiff ℝ 1 (fun p : ℝ × Vec 2 => G p.1 p.2 k j)) :
    ContDiff ℝ 1 (fun p : ℝ × Vec 2 => fun k : Fin 2 => metricCorrectionFlux (W p.1) (G p.1) p.2 k) := by
  apply contDiff_pi.mpr
  intro k
  have hd : ∀ j : Fin 2, ContDiff ℝ 1
      (fun p : ℝ × Vec 2 => fderiv ℝ (W p.1) p.2 (basisVec j)) :=
    fun j => joint_spatial_gradient_contDiff _ hW j
  unfold metricCorrectionFlux
  simp only [Fin.sum_univ_two]
  exact (((hG k 0).mul (hd 0)).add ((hG k 1).mul (hd 1))).sub (hd k)

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.EntryWeakProofs
namespace AVRegularity.CycleWords

/-! A common geometric native coefficient radius yields smooth literal spatial Taylor series. -/

theorem native_coefficients_periodic_derivative_geometric_bound
    (a : ℕ × ℕ → ℝ → Vec 2 → ℂ) (t : ℝ)
    (ha : ∀ p, ContDiff ℝ (⊤ : ℕ∞) (a p t))
    (hp : ∀ p, AVenhance.IsZ2Periodic (a p t)) (A : ℝ)
    (M : ℕ → ℝ)
    (hex : ∀ K : ℕ, ∃ U : ℕ × ℕ → TorusHk K ℂ,
      (∀ p, a p t =ᵐ[volume.restrict AVenhance.unitCube] (torusHkValueCLM (U p) : Vec 2 → ℂ)) ∧
      (∀ p, ‖U p‖ ≤ M K * A ^ (p.1 + p.2)))
    (j : ℕ) (p : ℕ × ℕ) (x : Vec 2) :
    ‖iteratedFDeriv ℝ j (a p t) x‖ ≤
      (torusHigherClassicalSobolevConstant (j + 2) j * M (j + 2)) * A ^ (p.1 + p.2) := by
  obtain ⟨U, hU, hUb⟩ := hex (j + 2)
  have hc : 0 ≤ torusHigherClassicalSobolevConstant (j + 2) j := by
    unfold torusHigherClassicalSobolevConstant classicalSobolevConstant
    positivity
  exact (torusHigher_periodic_representative_derivative_norm_le (j + 2) j (by omega)
    (U p) (a p t) (ha p).continuous (hp p) (hU p) x).trans
      ((mul_le_mul_of_nonneg_left (hUb p) hc).trans_eq (by ring))

theorem fibreSeriesFun_contDiff_of_native_coefficients
    (a : ℕ × ℕ → ℝ → Vec 2 → ℂ) (t : ℝ)
    (ha : ∀ p, ContDiff ℝ (⊤ : ℕ∞) (a p t))
    (hp : ∀ p, AVenhance.IsZ2Periodic (a p t)) (A : ℝ) (hA : 0 ≤ A)
    (M : ℕ → ℝ)
    (hex : ∀ K : ℕ, ∃ U : ℕ × ℕ → TorusHk K ℂ,
      (∀ p, a p t =ᵐ[volume.restrict AVenhance.unitCube] (torusHkValueCLM (U p) : Vec 2 → ℂ)) ∧
      (∀ p, ‖U p‖ ≤ M K * A ^ (p.1 + p.2)))
    (ξ : Fin 2 → ℂ) (hξ : A * ‖ξ‖ < 1) :
    ContDiff ℝ (⊤ : ℕ∞) (fibreSeriesFun a ξ t) := by
  let C := fun j => torusHigherClassicalSobolevConstant (j + 2) j * M (j + 2)
  apply fibreSeriesFun_contDiff_of_geometric_jets a t ha A hA C _ ξ hξ
  intro j p x
  obtain ⟨U, hU, hUb⟩ := hex (j + 2)
  have hc : 0 ≤ torusHigherClassicalSobolevConstant (j + 2) j := by
    unfold torusHigherClassicalSobolevConstant classicalSobolevConstant
    positivity
  exact (torusHigher_periodic_representative_derivative_norm_le (j + 2) j (by omega)
    (U p) (a p t) (ha p).continuous (hp p) (hU p) x).trans
      ((mul_le_mul_of_nonneg_left (hUb p) hc).trans_eq (by dsimp only [C]; ring))

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! Classical first and second spatial derivatives of a polynomial weight. -/

theorem polynomial_weight_gradient (U : Vec 2 → ℝ) (hU : Differentiable ℝ U)
    (n : ℕ) (z : Vec 2) (i : Fin 2) :
    fderiv ℝ (fun x => U x ^ n) z (basisVec i) =
      (n : ℝ) * U z ^ (n - 1) * fderiv ℝ U z (basisVec i) := by
  have hd := (hU z).hasFDerivAt.pow n
  rw [hd.fderiv]
  simp [smul_apply, smul_eq_mul]

theorem polynomial_weight_second_derivative (U : Vec 2 → ℝ) (hU : ContDiff ℝ 2 U)
    (n : ℕ) (z : Vec 2) (i : Fin 2) :
    fderiv ℝ (fun x => fderiv ℝ (fun y => U y ^ n) x (basisVec i)) z (basisVec i) =
      (n : ℝ) * U z ^ (n - 1) *
        fderiv ℝ (fun x => fderiv ℝ U x (basisVec i)) z (basisVec i) +
      (n : ℝ) * (n - 1 : ℕ) * U z ^ (n - 2) * (fderiv ℝ U z (basisVec i)) ^ 2 := by
  have hu := hU.differentiable (by norm_num)
  have he := funext (fun x => polynomial_weight_gradient U hu n x i)
  rw [he]
  have hd := weight_gradient_differentiable U hU i
  have hfirst := ((hu z).hasFDerivAt.pow (n - 1)).const_mul (n : ℝ)
  have hp := hfirst.mul (hd z).hasFDerivAt
  change fderiv ℝ ((fun x => (n : ℝ) * U x ^ (n - 1)) *
    (fun x => fderiv ℝ U x (basisVec i))) z (basisVec i) = _
  rw [hp.fderiv]
  simp [smul_apply, smul_eq_mul, Nat.sub_sub, pow_two]
  ring

/-! Comparison of the actual adjoint weight with the polynomial label weight. -/

theorem adjointCellCoordinate_label_difference (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ)
    (ν B T : ℝ) (yc : Vec 2) (t : ℝ) (z : Vec 2) (j : Fin 2) :
    adjointCellCoordinate α q Λ ζ m ν B T yc t z j -
      (ocEpsilon q Λ m / Real.sqrt (B * T)) * z j =
    (adjointCoordinate α q Λ ζ m ν (ocEll q Λ m ν ^ 2 * t)
      (yc + ocEpsilon q Λ m • z) j - (yc + ocEpsilon q Λ m • z) j) /
        Real.sqrt (B * T) := by
  simp only [adjointCellCoordinate, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem adjointCellCoordinate_label_bound {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν B T C : ℝ}
    (hν : 0 < ν) (hB : 0 < B) (hT : 0 < T) (hC : 0 ≤ C)
    (he : ν + ocEpsilon q Λ m ^ (2 * (1 + α)) / ν ≤ C * B)
    (hell : ocEpsilon q Λ m ^ 2 / ν ≤ T) (yc : Vec 2) (t : ℝ) (z : Vec 2) (j : Fin 2) :
    |adjointCellCoordinate α q Λ ζ m ν B T yc t z j -
      (ocEpsilon q Λ m / Real.sqrt (B * T)) * z j| ≤ 1 + C := by
  rw [adjointCellCoordinate_label_difference]
  exact normalized_displacement_abs_le hB hT hC hell
    (adjointCoordinate_displacement_enhancement hΛ hζ hν hB.le hC he _ _ j)

theorem adjointCellPolynomialWeight_comparable {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν B T C : ℝ}
    (hν : 0 < ν) (hB : 0 < B) (hT : 0 < T) (hC : 0 ≤ C)
    (he : ν + ocEpsilon q Λ m ^ (2 * (1 + α)) / ν ≤ C * B)
    (hell : ocEpsilon q Λ m ^ 2 / ν ≤ T) (yc : Vec 2) (n : ℕ) (t : ℝ) (z : Vec 2) :
    ((2 + 4 * (1 + C) ^ 2) ^ n)⁻¹ *
        (1 + (ocEpsilon q Λ m / Real.sqrt (B * T)) ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ n ≤
      adjointCellPolynomialWeight α q Λ ζ m ν B T yc n t z ∧
    adjointCellPolynomialWeight α q Λ ζ m ν B T yc n t z ≤
      (2 + 4 * (1 + C) ^ 2) ^ n *
        (1 + (ocEpsilon q Λ m / Real.sqrt (B * T)) ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ n := by
  have h0 := adjointCellCoordinate_label_bound hΛ hζ hν hB hT hC he hell yc t z 0
  have h1 := adjointCellCoordinate_label_bound hΛ hζ hν hB hT hC he hell yc t z 1
  have hL : 0 ≤ 1 + C := by linarith
  have hi : 1 + ((ocEpsilon q Λ m / Real.sqrt (B * T)) * z 0) ^ 2 +
      ((ocEpsilon q Λ m / Real.sqrt (B * T)) * z 1) ^ 2 =
      1 + (ocEpsilon q Λ m / Real.sqrt (B * T)) ^ 2 * (z 0 ^ 2 + z 1 ^ 2) := by ring
  constructor
  · simpa only [hi, adjointCellPolynomialWeight] using
      polynomial_weight_shift_lower _ _ _ _ _ n hL h0 h1
  · simpa only [hi, adjointCellPolynomialWeight] using
      polynomial_weight_shift_upper _ _ _ _ _ n hL h0 h1

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.CycleWords

/-! Actual finite Fourier ODE increments lift to genuine higher spatial primitive identities. -/

theorem cellGalerkin_linear_primitive {a b : ℝ} (hab : a ≤ b) (N : ℕ)
    (J : CellGalerkinSpace (E := ℂ) N →L[ℝ] TorusHk 1 ℂ)
    (A : ℝ → CellGalerkinSpace (E := ℂ) N →L[ℝ] CellGalerkinSpace (E := ℂ) N)
    (f : ℝ → CellGalerkinSpace (E := ℂ) N) (u₀ : CellGalerkinSpace (E := ℂ) N)
    (y : ContinuousMap (Icc a b) (CellGalerkinSpace (E := ℂ) N))
    (hy : IsLinearIntegralSolution A f u₀ a b (extendCurve hab y))
    (hA : AEStronglyMeasurable A volume) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ t, ‖A t‖ ≤ M) (hf : MemLp f 2 (volume.restrict (Icc a b))) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
      J (extendCurve hab y t) -
        J (extendCurve hab y s) =
      ∫ r in s..t, J (linearRhs A f (extendCurve hab y) r) := by
  have hr := linearRhs_memLp A hA M hM hb (extendCurve hab y)
    (continuous_extendCurve hab y).continuousOn f hf
  have hint : IntervalIntegrable (linearRhs A f (extendCurve hab y)) volume a b := by
    apply intervalIntegrable_iff.mpr
    rw [uIoc_of_le hab]
    have hi : IntegrableOn (linearRhs A f (extendCurve hab y)) (Icc a b) := hr.integrable (by norm_num)
    exact hi.mono_set Ioc_subset_Icc_self
  intro s hs t ht hst
  have has := hint.mono_set (by rw [uIcc_of_le hs.1, uIcc_of_le hab]; exact Icc_subset_Icc le_rfl hs.2)
  have hstint := hint.mono_set (by rw [uIcc_of_le hst, uIcc_of_le hab]; exact Icc_subset_Icc hs.1 ht.2)
  have hi : extendCurve hab y t - extendCurve hab y s =
      ∫ r in s..t, linearRhs A f (extendCurve hab y) r := by
    rw [hy t ht, hy s hs]
    rw [← intervalIntegral.integral_add_adjacent_intervals has hstint]
    abel
  have he := congrArg (J) hi
  rw [map_sub, ← ContinuousLinearMap.intervalIntegral_comp_comm _ hstint] at he
  exact he

end AVRegularity.CycleWords
end
