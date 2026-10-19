-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Weighted.WeightedMultiplicationTermTime
import AVRegularity.CycleJoint.ReferencePhysicalSpatialSmooth
public import AVRegularity.CycleJoint.ScalarPlaneChainNativeResidualOrderAssembly
import AVRegularity.CycleReference.MeanEnhancementScale
import AVRegularity.CycleJoint.PlaneCoupledFluxScaling
import AVRegularity.CycleJoint.WeightedGradientLiftComparison
import AVRegularity.CycleWords.DerivativeSourceDensity
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleJointProofs

/-! The complete family flux retains its absolute image price and actual localized torus readout. -/

variable {ι X : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] [MeasurableSpace X]

theorem familyFlux_actual_time_transfer (K : ι → ℕ) (D : ℕ) (i : ι)
    (μ : Measure X) [IsFiniteMeasure μ] (S : Set X) (hS : MeasurableSet S)
    (hSae : ∀ᵐ t ∂μ, t ∈ S)
    (A : ∀ i i', (d : admissibleOrders K D i i') → X → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hc : ∀ i' d t, t ∈ S → Continuous (A i i' d t))
    (hj : ∀ i' d, Measurable (Function.uncurry (A i i' d)))
    (MC : ∀ i', admissibleOrders K D i i' → ℝ)
    (hMC : ∀ i' d, 0 ≤ MC i' d)
    (hbA : ∀ i' d t, t ∈ S → ∀ x, ‖A i i' d t x‖ ≤ MC i' d)
    (hpA : ∀ i' d t, t ∈ S → AVenhance.IsZ2Periodic (A i i' d t))
    (f : ∀ i, X → PlaneHk Set.univ (K i + 1) (h i))
    (hf : ∀ i, MemLp (f i) 2 μ) (z : Vec 2)
    (M : ι → X → ℝ) (hM : ∀ i, MemLp (M i) 2 μ)
    (hw : ∀ i α, ∀ᵐ t ∂μ, AEStronglyMeasurable
      (fun y => (1 + ‖y - z‖) ^ 4 • (f i t).toFunction.jet α y) volume)
    (hb : ∀ i α, ∀ᵐ t ∂μ, eLpNorm
      (fun y => (1 + ‖y - z‖) ^ 4 • (f i t).toFunction.jet α y) 2 volume ≤ ENNReal.ofReal ‖M i t‖)
    (T : ∀ i, X → TorusHk (K i + 1) (h i))
    (hr : ∀ i α, ∀ᵐ t ∂μ, (T i t).toFunction.jet α =ᵐ[volume]
      periodizeRawJet (f i t).toFunction.jet α)
    {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (φ : TorusHk 1 (h i)) (k j : Fin 2) :
    let α := fun i' (d : admissibleOrders K D i i') (w : DerivativeWord2 (d.1 - 1)) =>
      (⟨⟨d.1 - 1, by have hd := admissibleOrders_reserve K D i i' d; omega⟩, w⟩ : JetIndex2 (K i' + 1))
    let ψ := spatialPatchLocalization hζ 1 (by norm_num) 0 1 φ
    let G := fun (n : Fin 2 → ℤ) t => ∫ x, inner ℝ
      ((∑ i', ∑ d, A i i' d t x (WithLp.toLp 2 (fun w =>
        (planeCarrierTranslation (K i' + 1) (AVenhance.latticeShift n) (f i' t)).toFunction.jet (α i' d w) x))) k)
      (ψ.toFunction.jet ⟨⟨1, by decide⟩, fun _ => j⟩ x)
    let P := fun t => ∫ x, inner ℝ
      ((∑ i', ∑ d, A i i' d t x (WithLp.toLp 2 (fun w => (T i' t).toFunction.jet (α i' d w) x))) k)
      (ψ.toFunction.jet ⟨⟨1, by decide⟩, fun _ => j⟩ x)
    (∀ n, Integrable (G n) μ) ∧ Summable (fun n => ∫ t, ‖G n t‖ ∂μ) ∧
      Integrable P μ ∧ (∑' n, ∫ t, G n t ∂μ) = ∫ t, P t ∂μ := by
  dsimp only
  let α := fun i' (d : admissibleOrders K D i i') (w : DerivativeWord2 (d.1 - 1)) =>
    (⟨⟨d.1 - 1, by have hd := admissibleOrders_reserve K D i i' d; omega⟩, w⟩ : JetIndex2 (K i' + 1))
  let ψ := spatialPatchLocalization hζ 1 (by norm_num) 0 1 φ
  let β : JetIndex2 1 := ⟨⟨1, by decide⟩, fun _ => j⟩
  let G := fun i' (d : admissibleOrders K D i i') (n : Fin 2 → ℤ) t => ∫ x, inner ℝ
    (A i i' d t x (WithLp.toLp 2 (fun w =>
      (planeCarrierTranslation (K i' + 1) (AVenhance.latticeShift n) (f i' t)).toFunction.jet (α i' d w) x)) k)
    (ψ.toFunction.jet β x)
  let P := fun i' (d : admissibleOrders K D i i') t => ∫ x, inner ℝ
    (A i i' d t x (WithLp.toLp 2 (fun w => (T i' t).toFunction.jet (α i' d w) x)) k)
    (ψ.toFunction.jet β x)
  have hpart (i' : ι) (d : admissibleOrders K D i i') :
      (∀ n, Integrable (G i' d n) μ) ∧ Summable (fun n => ∫ t, ‖G i' d n t‖ ∂μ) ∧
      Integrable (P i' d) μ ∧ (∑' n, ∫ t, G i' d n t ∂μ) = ∫ t, P i' d t ∂μ := by
    exact windowed_couplingFlux_actual_time_transfer i i' μ S hS hSae
      (Metric.ball (0 : Vec 2) 2) measurableSet_ball 2 (by norm_num) Set.Subset.rfl
      (A i i' d) (hc i' d) (hj i' d) (MC i' d) (hMC i' d) (hbA i' d)
      (f i') (hf i') z (α i' d) ψ β k
      (unitPatchLocalization_jet_ball_support_ae hζ 1 φ β)
      (M i') (hM i') (fun w => hw i' (α i' d w)) (fun w => hb i' (α i' d w))
      (T i') (fun w => hr i' (α i' d w))
  have hsource (i' : ι) := finite_pairing_spacetime_readout μ Finset.univ (G i') (P i')
    (fun d _ => (hpart i' d).1) (fun d _ => (hpart i' d).2.1)
    (fun d _ => (hpart i' d).2.2.1) (fun d _ => (hpart i' d).2.2.2)
  have hwhole := finite_pairing_spacetime_readout μ Finset.univ
    (fun i' n t => ∑ d, G i' d n t) (fun i' t => ∑ d, P i' d t)
    (fun i' _ => (hsource i').1) (fun i' _ => (hsource i').2.1)
    (fun i' _ => (hsource i').2.2.1) (fun i' _ => (hsource i').2.2.2)
  have himage (n : Fin 2 → ℤ) :
      (fun t => ∫ x, inner ℝ
        ((∑ i', ∑ d, A i i' d t x (WithLp.toLp 2 (fun w =>
          (planeCarrierTranslation (K i' + 1) (AVenhance.latticeShift n) (f i' t)).toFunction.jet (α i' d w) x))) k)
        (ψ.toFunction.jet β x)) =ᵐ[μ] fun t => ∑ i', ∑ d, G i' d n t := by
    filter_upwards [hSae] with t ht
    apply (couplingFamily_pairing_integral K D i volume _ (ψ.toFunction.jet β) k _).2
    intro i' d
    have hm := couplingFlux_component_memLp i i' Set.univ (A i i' d t)
      (hc i' d t ht) (MC i' d) (hMC i' d) (hbA i' d t ht)
      (α i' d |> fun a => fun w =>
        (planeCarrierTranslation (K i' + 1) (AVenhance.latticeShift n) (f i' t)).toFunction.jet (a w))
      (fun w => (planeCarrierTranslation (K i' + 1) (AVenhance.latticeShift n) (f i' t)).toFunction.memL2 _) k
    simpa only [Measure.restrict_univ] using
      integrable_inner_of_memLp_two (volume.restrict Set.univ) _ _ hm (ψ.toFunction.memL2 β)
  have hactual :
      (fun t => ∫ x, inner ℝ
        ((∑ i', ∑ d, A i i' d t x (WithLp.toLp 2 (fun w => (T i' t).toFunction.jet (α i' d w) x))) k)
        (ψ.toFunction.jet β x)) =ᵐ[μ] fun t => ∑ i', ∑ d, P i' d t := by
    filter_upwards [hSae] with t ht
    apply (couplingFamily_pairing_integral K D i volume _ (ψ.toFunction.jet β) k _).2
    intro i' d
    exact (torusCoefficientArray_unitPatch_pairings_integrable i i' (A i i' d t)
      (hc i' d t ht) (MC i' d) (hMC i' d) (hbA i' d t ht) (hpA i' d t ht)
      (T i' t) (α i' d) k hζ φ).2 j
  refine ⟨fun n => (hwhole.1 n).congr (himage n).symm, ?_,
    hwhole.2.2.1.congr hactual.symm, ?_⟩
  · exact hwhole.2.1.congr (fun n => integral_congr_ae
      ((himage n).symm.mono (fun _ hx => congrArg norm hx)))
  · calc
      _ = ∑' n : Fin 2 → ℤ, ∫ t, ∑ i', ∑ d, G i' d n t ∂μ :=
        tsum_congr (fun n => integral_congr_ae (himage n))
      _ = ∫ t, ∑ i', ∑ d, P i' d t ∂μ := hwhole.2.2.2
      _ = _ := integral_congr_ae hactual.symm

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleJointProofs

/-! Finite weighted native jets give finite polynomial factorial initial energy. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem weightedFactorialNormSq_ne_top_of_weighted_jets
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ) (U : PlaneHk Set.univ K E)
    (hw : ∀ a : JetIndex2 K,
      MemLp (fun x => planeMomentSquareRoot n ϖ zc x • U.toFunction.jet a x) 2 volume) :
    weightedFactorialNormSq n ϖ zc ρ K U ≠ ⊤ := by
  classical
  rw [weightedFactorialNormSq_stored_readout]
  unfold storedChartFactorialEnergy
  apply ENNReal.sum_ne_top.mpr
  intro a _
  apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
  have hi := (hw a).norm.integrable_sq
  have hfin := (hasFiniteIntegral_iff_ofReal
    (Filter.Eventually.of_forall (fun x => sq_nonneg
      ‖planeMomentSquareRoot n ϖ zc x • U.toFunction.jet a x‖))).mp hi.hasFiniteIntegral
  apply ne_of_lt
  apply lt_of_le_of_lt (le_of_eq ?_) hfin
  unfold chartScalarEnergy
  apply lintegral_congr_ae
  filter_upwards [univToPlane_ae (U.val a)] with x hx
  rw [planeJetReadoutOperator_apply, hx, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs, planeMomentSquareRoot_sq]
  rfl

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Measurable unit-bounded time weights preserve native moments with an exact squared density factor. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeUnitWeighted_forcing_exists (μ : Measure ℝ) (w : ℝ → ℝ)
    (hm : Measurable w) (hw : ∀ t, |w t| ≤ 1)
    (K n : ℕ) (ϖ ρ : ℝ) (V : ℝ → PlaneHk Set.univ K E)
    (hV : MemLp V 2 μ)
    (he : (∫⁻ t, weightedFactorialNormSq n ϖ 0 ρ K (V t) ∂μ) ≠ ⊤) :
    ∃ W : ℝ → PlaneHk Set.univ K E, MemLp W 2 μ ∧
      (∫⁻ t, weightedFactorialNormSq n ϖ 0 ρ K (W t) ∂μ) ≠ ⊤ ∧
      (∀ t, planeValue (W t) =ᵐ[volume] fun z => w t • planeValue (V t) z) ∧
      (∀ t, ∀ᵐ z ∂volume, planeFactorialDensity ρ (W t) z =
        w t ^ 2 * planeFactorialDensity ρ (V t) z) := by
  let W := fun t => w t • V t
  have henergy : (∫⁻ t, weightedFactorialNormSq n ϖ 0 ρ K (W t) ∂μ) ≤
      ∫⁻ t, weightedFactorialNormSq n ϖ 0 ρ K (V t) ∂μ :=
    lintegral_mono (fun t => weightedFactorialNormSq_unit_smul_le n ϖ 0 ρ
      (w t) (hw t) (V t))
  have hW : MemLp W 2 μ := supported_weight_memLp μ w V hV hm.aestronglyMeasurable
    1 zero_le_one (fun t _ => hw t)
  refine ⟨W, hW, ne_top_of_le_ne_top he henergy, ?_, ?_⟩
  · intro t
    simp only [W, planeValue, planeJetOrder_eq_stored (Nat.zero_le K)]
    exact planeCarrier_jet_smul_ae (w t) (V t) (valueIndex2 K)
  · intro t
    exact planeFactorialDensity_smul_ae ρ (w t) (V t)

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! The value energy and the genuine gradient production control every higher stored jet. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem polynomialLift_energy_ne_top (n : ℕ) (ϖ : ℝ) (z : Vec 2) (ρ : ℝ) (hρ : 0 < ρ)
    (μ : Measure ℝ) (w : ℝ → PlaneHk Set.univ (K + 1) E) (hw : MemLp w 2 μ)
    (hvalue : (∫⁻ t, chartScalarEnergy (planeMomentPolynomial n ϖ z)
      (planeJetReadoutOperator (K + 1) (valueIndex2 (K + 1)) (w t)) ∂μ) ≠ ⊤)
    (hgrad : (∫⁻ t, weightedGradFactorialNormSq n ϖ z ρ K (w t) ∂μ) ≠ ⊤) :
    (∫⁻ t, weightedFactorialNormSq n ϖ z ρ (K + 1) (w t) ∂μ) ≠ ⊤ := by
  apply integrated_weightedFactorialNormSq_ne_top n ϖ z ρ μ w hw
  intro α
  simp only [planeMomentSquareRoot_sq]
  rcases α with ⟨⟨j, hj⟩, word⟩
  cases j with
  | zero =>
    have he : (⟨⟨0, hj⟩, word⟩ : JetIndex2 (K + 1)) = valueIndex2 (K + 1) := by
      have hword : word = (valueIndex2 (K + 1)).2 := Subsingleton.elim _ _
      cases hword
      rfl
    simpa only [he] using hvalue
  | succ j =>
    have hjK : j < K + 1 := by omega
    have hh := weighted_gradient_readout_integral_ne_top n ϖ z ρ hρ μ w hgrad
      (⟨⟨j, hjK⟩, Fin.init word⟩ : JetIndex2 K) (word (Fin.last j))
    simpa only [Fin.snoc_init_self] using hh
end

/-! Finite sums of actual jet moments give measurable stored time energy. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The stored factorial energy is measurable along an actual Sobolev L² time curve. -/
theorem storedChartFactorialEnergy_time_aemeasurable {K : ℕ}
    (ρ : ℝ) (q : Vec 2 → ℝ) (hq : Continuous q) (hq0 : ∀ x, 0 < q x)
    (μ : Measure ℝ) (U : ℝ → PlaneHk Set.univ K E) (hU : MemLp U 2 μ) :
    AEMeasurable (fun t => storedChartFactorialEnergy ρ q (U t)) μ := by
  classical
  have hm (β : JetIndex2 K) := chartScalarEnergy_stationary_time_aemeasurable
    q hq hq0 μ (fun t => planeJetReadoutOperator K β (U t))
      ((planeJetReadoutOperator (E := E) K β).comp_memLp' hU)
  exact Finset.aemeasurable_fun_sum _ (fun β _ => (hm β).const_mul _)
end

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleJointProofs

/-! The signed coupling directions assemble with the full family flux readout and absolute image price. -/

variable {ι X : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] [MeasurableSpace X]

theorem coupling_actual_time_transfer (K : ι → ℕ) (D : ℕ) (i : ι)
    (μ : Measure X) [IsFiniteMeasure μ] (S : Set X) (hS : MeasurableSet S)
    (hSae : ∀ᵐ t ∂μ, t ∈ S)
    (A : ∀ i i', (d : admissibleOrders K D i i') → X → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hc : ∀ i' d t, t ∈ S → Continuous (A i i' d t))
    (hj : ∀ i' d, Measurable (Function.uncurry (A i i' d)))
    (MC : ∀ i', admissibleOrders K D i i' → ℝ)
    (hMC : ∀ i' d, 0 ≤ MC i' d)
    (hbA : ∀ i' d t, t ∈ S → ∀ x, ‖A i i' d t x‖ ≤ MC i' d)
    (hpA : ∀ i' d t, t ∈ S → AVenhance.IsZ2Periodic (A i i' d t))
    (f : ∀ i, X → PlaneHk Set.univ (K i + 1) (h i))
    (hf : ∀ i, MemLp (f i) 2 μ) (z : Vec 2)
    (M : ι → X → ℝ) (hM : ∀ i, MemLp (M i) 2 μ)
    (hw : ∀ i α, ∀ᵐ t ∂μ, AEStronglyMeasurable
      (fun y => (1 + ‖y - z‖) ^ 4 • (f i t).toFunction.jet α y) volume)
    (hb : ∀ i α, ∀ᵐ t ∂μ, eLpNorm
      (fun y => (1 + ‖y - z‖) ^ 4 • (f i t).toFunction.jet α y) 2 volume ≤ ENNReal.ofReal ‖M i t‖)
    (T : ∀ i, X → TorusHk (K i + 1) (h i))
    (hr : ∀ i α, ∀ᵐ t ∂μ, (T i t).toFunction.jet α =ᵐ[volume]
      periodizeRawJet (f i t).toFunction.jet α)
    {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (φ : TorusHk 1 (h i)) :
    let α := fun i' (d : admissibleOrders K D i i') (w : DerivativeWord2 (d.1 - 1)) =>
      (⟨⟨d.1 - 1, by have hd := admissibleOrders_reserve K D i i' d; omega⟩, w⟩ : JetIndex2 (K i' + 1))
    let ψ := spatialPatchLocalization hζ 1 (by norm_num) 0 1 φ
    let G := fun (n : Fin 2 → ℤ) t => -(∑ k : Fin 2, ∫ x, inner ℝ
      ((∑ i', ∑ d, A i i' d t x (WithLp.toLp 2 (fun w =>
        (planeCarrierTranslation (K i' + 1) (AVenhance.latticeShift n) (f i' t)).toFunction.jet (α i' d w) x))) k)
      (ψ.toFunction.jet ⟨⟨1, by decide⟩, fun _ => k⟩ x))
    let P := fun t => -(∑ k : Fin 2, ∫ x, inner ℝ
      ((∑ i', ∑ d, A i i' d t x (WithLp.toLp 2 (fun w => (T i' t).toFunction.jet (α i' d w) x))) k)
      (ψ.toFunction.jet ⟨⟨1, by decide⟩, fun _ => k⟩ x))
    (∀ n, Integrable (G n) μ) ∧ Summable (fun n => ∫ t, ‖G n t‖ ∂μ) ∧
      Integrable P μ ∧ (∑' n, ∫ t, G n t ∂μ) = ∫ t, P t ∂μ := by
  dsimp only
  let α := fun i' (d : admissibleOrders K D i i') (w : DerivativeWord2 (d.1 - 1)) =>
    (⟨⟨d.1 - 1, by have hd := admissibleOrders_reserve K D i i' d; omega⟩, w⟩ : JetIndex2 (K i' + 1))
  let ψ := spatialPatchLocalization hζ 1 (by norm_num) 0 1 φ
  let G := fun k (n : Fin 2 → ℤ) t => ∫ x, inner ℝ
    ((∑ i', ∑ d, A i i' d t x (WithLp.toLp 2 (fun w =>
      (planeCarrierTranslation (K i' + 1) (AVenhance.latticeShift n) (f i' t)).toFunction.jet (α i' d w) x))) k)
    (ψ.toFunction.jet ⟨⟨1, by decide⟩, fun _ => k⟩ x)
  let P := fun k t => ∫ x, inner ℝ
    ((∑ i', ∑ d, A i i' d t x (WithLp.toLp 2 (fun w => (T i' t).toFunction.jet (α i' d w) x))) k)
    (ψ.toFunction.jet ⟨⟨1, by decide⟩, fun _ => k⟩ x)
  have hdir (k : Fin 2) : (∀ n, Integrable (G k n) μ) ∧
      Summable (fun n => ∫ t, ‖G k n t‖ ∂μ) ∧ Integrable (P k) μ ∧
      (∑' n, ∫ t, G k n t ∂μ) = ∫ t, P k t ∂μ :=
    familyFlux_actual_time_transfer K D i μ S hS hSae A hc hj MC hMC hbA hpA
      f hf z M hM hw hb T hr hζ φ k k
  have hsum := finite_pairing_spacetime_readout μ Finset.univ G P
    (fun k _ => (hdir k).1) (fun k _ => (hdir k).2.1)
    (fun k _ => (hdir k).2.2.1) (fun k _ => (hdir k).2.2.2)
  simpa only [neg_one_mul] using pairing_spacetime_readout_const_mul μ
    (fun n t => ∑ k, G k n t) (fun t => ∑ k, P k t)
    hsum.1 hsum.2.1 hsum.2.2.1 hsum.2.2.2 (-1)

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! The proved polynomial moment controls the radial weight used in image summation. -/

theorem fourth_radial_le_planeMoment (ϖ : ℝ) (hϖ : 0 < ϖ) (z x : Vec 2) :
    (1 + ‖x - z‖) ^ 4 ≤ (Real.sqrt (2 + 4 / ϖ ^ 2)) ^ 4 *
      planeMomentSquareRoot 4 ϖ z x := by
  have hh := plane_polynomial_moment_absorption ϖ hϖ 0 4 (x - z)
  simpa only [planeMomentSquareRoot, planeMomentPolynomial, pow_zero, Real.sqrt_one,
    mul_one, zero_add, Pi.zero_apply, Pi.sub_apply, sub_zero] using hh

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem radialMoment_memLp_of_planeMoment (ϖ : ℝ) (hϖ : 0 < ϖ) (z : Vec 2)
    (f : Vec 2 → E) (hf : AEStronglyMeasurable f volume)
    (hm : MemLp (fun x => planeMomentSquareRoot 4 ϖ z x • f x) 2 volume) :
    MemLp (fun x => (1 + ‖x - z‖) ^ 4 • f x) 2 volume := by
  have hc : Continuous (fun x : Vec 2 => (1 + ‖x - z‖) ^ 4) := by fun_prop
  apply hm.of_le_mul (c := (Real.sqrt (2 + 4 / ϖ ^ 2)) ^ 4)
    (hc.aestronglyMeasurable.smul hf)
  filter_upwards with x
  change ‖(1 + ‖x - z‖) ^ 4 • f x‖ ≤
    (Real.sqrt (2 + 4 / ϖ ^ 2)) ^ 4 * ‖planeMomentSquareRoot 4 ϖ z x • f x‖
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (1 + ‖x - z‖) ^ 4),
    abs_of_nonneg (show 0 ≤ planeMomentSquareRoot 4 ϖ z x from Real.sqrt_nonneg _)]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_right (fourth_radial_le_planeMoment ϖ hϖ z x) (norm_nonneg (f x))

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Finite gradient production and a uniformly bounded lower trajectory supply full lift energy. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem polynomial_production_lift_energy_ne_top (n : ℕ) (ϖ : ℝ) (z : Vec 2)
    (ρ : ℝ) (hρ : 0 < ρ) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (u : ℝ → PlaneHk Set.univ K E) (w : ℝ → PlaneHk Set.univ (K + 1) E)
    (hw : MemLp w 2 μ) (hlift : ∀ᵐ t ∂μ, truncatePlaneHk (Nat.le_succ K) (w t) = u t)
    (C : ℝ) (hb : ∀ᵐ t ∂μ, weightedFactorialNormSq n ϖ z ρ K (u t) ≤ ENNReal.ofReal C)
    (hgrad : (∫⁻ t, weightedGradFactorialNormSq n ϖ z ρ K (w t) ∂μ) ≠ ⊤) :
    (∫⁻ t, weightedFactorialNormSq n ϖ z ρ (K + 1) (w t) ∂μ) ≠ ⊤ := by
  apply polynomialLift_energy_ne_top n ϖ z ρ hρ μ w hw _ hgrad
  have hval : ∀ᵐ t ∂μ, chartScalarEnergy (planeMomentPolynomial n ϖ z)
      (planeJetReadoutOperator (K + 1) (valueIndex2 (K + 1)) (w t)) ≤ ENNReal.ofReal C := by
    filter_upwards [hlift, hb] with t ht hb'
    rw [← plane_value_readout_truncate (Nat.le_succ K) (w t), ht]
    exact (polynomial_value_energy_le n ϖ z ρ (u t)).trans hb'
  apply ne_top_of_le_ne_top _ (lintegral_mono_ae hval)
  rw [lintegral_const]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ Set.univ)

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! The quantitative radial moment price is the same one used in the polynomial readout. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem radialMoment_eLpNorm_le_polynomial (ϖ : ℝ) (hϖ : 0 < ϖ) (z : Vec 2)
    (f : Vec 2 → E) (hf : AEStronglyMeasurable f volume) :
    eLpNorm (fun y => (1 + ‖y - z‖) ^ 4 • f y) 2 volume ≤
      ENNReal.ofReal ((Real.sqrt (2 + 4 / ϖ ^ 2)) ^ 4) *
        eLpNorm (fun y => planeMomentSquareRoot 4 ϖ z y • f y) 2 volume := by
  let C := (Real.sqrt (2 + 4 / ϖ ^ 2)) ^ 4
  have hC : 0 ≤ C := by positivity
  have hm : AEStronglyMeasurable (fun y => (1 + ‖y - z‖) ^ 4 • f y) volume :=
    (show Continuous (fun y : Vec 2 => (1 + ‖y - z‖) ^ 4) by fun_prop).aestronglyMeasurable.smul hf
  have hb (y : Vec 2) : ‖(1 + ‖y - z‖) ^ 4 • f y‖ ≤
      ‖C • (planeMomentSquareRoot 4 ϖ z y • f y)‖ := by
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC,
      abs_of_nonneg (by positivity : 0 ≤ (1 + ‖y - z‖) ^ 4),
      abs_of_nonneg (show 0 ≤ planeMomentSquareRoot 4 ϖ z y from Real.sqrt_nonneg _)]
    simpa only [C, mul_assoc] using mul_le_mul_of_nonneg_right
      (fourth_radial_le_planeMoment ϖ hϖ z y) (norm_nonneg (f y))
  calc
    _ ≤ eLpNorm (fun y => C • (planeMomentSquareRoot 4 ϖ z y • f y)) 2 volume :=
      eLpNorm_mono hm hb
    _ = _ := by
      change eLpNorm (C • (fun y => planeMomentSquareRoot 4 ϖ z y • f y)) 2 volume = _
      rw [eLpNorm_const_smul, ← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hC]

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Finite Sobolev sums preserve finite integrated stored polynomial moments. -/

variable {J E : Type*} [Fintype J] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- Summing finitely many actual Sobolev curves preserves their integrated weighted energy. -/
theorem integrated_stored_energy_finite_sum_ne_top {K : ℕ}
    (ρ : ℝ) (hρ : 0 < ρ) (q : Vec 2 → ℝ) (hq : Continuous q) (hq0 : ∀ x, 0 < q x)
    (μ : Measure ℝ) (U : J → ℝ → PlaneHk Set.univ K E)
    (hU : ∀ j, MemLp (U j) 2 μ)
    (he : ∀ j, (∫⁻ t, storedChartFactorialEnergy ρ (fun x => q x ^ 2) (U j t) ∂μ) ≠ ⊤) :
    (∫⁻ t, storedChartFactorialEnergy ρ (fun x => q x ^ 2) (∑ j, U j t) ∂μ) ≠ ⊤ := by
  classical
  apply integrated_storedChartFactorialEnergy_ne_top ρ (fun x => q x ^ 2)
    (hq.pow 2) (fun x => sq_pos_of_pos (hq0 x)) μ _
    (memLp_fintype_sum U hU)
  intro β
  have hc (j : J) : (∫⁻ t, chartScalarEnergy (fun x => q x ^ 2)
      (planeJetReadoutOperator K β (U j t)) ∂μ) ≠ ⊤ :=
    finite_integrated_weighted_sum_component μ
      (fun γ : JetIndex2 K => factorialWeight ρ γ.1.val)
      (fun γ => factorialWeight_pos_of_radius_pos ρ hρ γ.1.val) _ (he j) β
  have hs := integrated_chart_energy_finite_sum_ne_top q hq hq0 μ
    (fun j t => planeJetReadoutOperator K β (U j t))
    (fun j => (planeJetReadoutOperator (E := E) K β).comp_memLp' (hU j)) hc
  simpa only [map_sum] using hs

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The actual inherited constituent in common reference cell coordinates retains its native Piola array. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem weighted_reference_piece_cell_operator_constructed_remainder
    (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
    (ν e E : ℝ) (hν : ν ≠ 0) (he : 0 < e) (p : P') (c : Ctx p) (v u : ι) (γ : F.Γ v u)
    (r : ℕ) (hr : 1 ≤ r) (Ks : ℕ) (s : ℝ) (t : Set.Icc tS tZ) (yc z : Vec 2)
    (timeScale a b τ : ℝ) (hτ : τ ∈ Set.Icc a b) (htime : timeScale * τ = t.val) :
    let Y := streamFlow φ hφ (F.piece p).anchor (yc + e • z) s
    let Yc := streamFlow φ hφ (F.piece p).anchor yc s
    let J := fun x => naturalPreparationJacobian hφ (F.piece p).anchor s (yc + e • x)
    let Bp : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2 :=
      fun d I a => taylorSlow 0 Ks
        (fun X => F.flux p c v u γ d I t X (e⁻¹ • Y) a) (E⁻¹ • Yc) (E⁻¹ • (Y - Yc))
    ((e * (e ^ r)⁻¹) * ν⁻¹) • (F.weight p t • nativeArrayAssembly r (F.identity v u γ).map
      (fun a A => transportedCoeff
        (chartInvJacobian ⇑(pieceReferenceMaterial F hφ s p t).symm)
        (F.identity v u γ).maxOrder
        (fun d I => F.dimFlux ν e E p c v u γ d I t
          ((pieceReferenceMaterial F hφ s p t).symm (yc + e • z))
          (e⁻¹ • (pieceReferenceMaterial F hφ s p t).symm (yc + e • z))) r A (yc + e • z) a)) =
    F.weight p t • nativeArrayAssembly r (F.identity v u γ).map
      (fun a A => transportedCoeff J (F.identity v u γ).maxOrder Bp r A z a) +
    naturalFamilyRemainderNativeArray Ks F p c v u γ timeScale a b hφ
      (F.piece p).anchor s e E yc r τ z := by
  have hrem := naturalFamilyRemainderNativeArray_readout Ks F p c v u γ
    timeScale a b hφ (F.piece p).anchor s e E yc r τ hτ z
  rw [htime] at hrem
  dsimp only at hrem ⊢
  rw [hrem]
  exact weighted_reference_piece_cell_operator_natural_taylor_split F hc ν e E hν he
    p c v u γ r hr Ks s t yc z

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! The actual transformed drift is the periodic cell pulse drift on its own renewal block. -/

/-- The block restriction is retained explicitly; this equality is not asserted in an old chart at later times. -/
theorem naturalBlock_material_drift {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsOCStreamSeq α q Λ ζ Φ)
    (hm : 1 ≤ m) (hφ : IsAdmissibleStream (Φ (m - 1)))
    (hΨ : IsAdmissibleStream (Φ m)) (l : ℤ) (t : ℝ)
    (ht : ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ t ∧
      t ≤ ((l : ℝ) + 1 / 2) * ocTauPP α q Λ m) (y : Vec 2) :
    chartVector hφ ((l : ℝ) * ocTauPP α q Λ m)
      (fun r x => streamVel (Φ m) r x - streamVel (Φ (m - 1)) r x) t y =
      streamVel (ocPulseStream α q Λ ζ m) t y := by
  have hs : chartStreamIncrement hφ ((l : ℝ) * ocTauPP α q Λ m) (Φ m) t =
      ocPulseStream α q Λ ζ m t := funext
    (chartStreamIncrement_eq_ocPulseStream hΛ hseq hm hφ l t ht)
  have hv := chartStreamIncrement_velocity hφ hΨ ((l : ℝ) * ocTauPP α q Λ m) t y
  change streamVel (chartStreamIncrement hφ ((l : ℝ) * ocTauPP α q Λ m) (Φ m)) t y =
    chartVector hφ ((l : ℝ) * ocTauPP α q Λ m)
      (fun r x => streamVel (Φ m) r x - streamVel (Φ (m - 1)) r x) t y at hv
  rw [← hv]
  unfold streamVel
  rw [hs]

/-- Diffusion and affine spatial normalization give exactly the cell drift `ocCellDrift` on the
current block. -/
theorem naturalBlock_normalized_cell_drift {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsOCStreamSeq α q Λ ζ Φ)
    (hm : 1 ≤ m) (hφ : IsAdmissibleStream (Φ (m - 1)))
    (hΨ : IsAdmissibleStream (Φ m)) {ν : ℝ} (hν : 0 < ν)
    (l : ℤ) (t : ℝ) (yc z : Vec 2)
    (ht : ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ ocEll q Λ m ν ^ 2 * t ∧
      ocEll q Λ m ν ^ 2 * t ≤ ((l : ℝ) + 1 / 2) * ocTauPP α q Λ m) :
    ocEpsilon q Λ m • normalizedMaterialVelocity hφ ((l : ℝ) * ocTauPP α q Λ m) ν
      (streamVel (Φ m)) (ocEpsilon q Λ m ^ 2 * t) (yc + ocEpsilon q Λ m • z) =
      ocCellDrift α q Λ ζ m ν yc t z := by
  have he : ocEpsilon q Λ m ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  have htime : ν⁻¹ * (ocEpsilon q Λ m ^ 2 * t) = ocEll q Λ m ν ^ 2 * t := by
    rw [ocEll_sq_eq hν, div_eq_mul_inv]
    ring
  have hprice : ocEpsilon q Λ m * ν⁻¹ = ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m := by
    rw [ocEll_sq_eq hν]
    field_simp
  dsimp only [normalizedMaterialVelocity, timeNormalizedVelocity]
  rw [htime, naturalBlock_material_drift hΛ hseq hm hφ hΨ l _ ht, smul_smul, hprice]
  rfl

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! Native weak increments tested against compact scalar directions extend to every H1 test. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeWeak_increment_of_scalar_compact {a b : ℝ} (hab : a ≤ b)
    (ua ub : Lp E 2 (volume : Measure (Vec 2)))
    (dual : ℝ → PlaneHk univ 1 E) (hdual : MemLp dual 2 (volume.restrict (Icc a b)))
    (h : ∀ (q : Vec 2 → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hs : HasCompactSupport q) (e : E),
      let z := compactSmoothHilbertH1 (fun x => q x • e) (hq.smul contDiff_const) (hs.smul_right)
      inner ℝ ub (planeHkValueOperator 1 z) - inner ℝ ua (planeHkValueOperator 1 z) =
        ∫ t in a..b, inner ℝ (dual t) z) (z : PlaneHk univ 1 E) :
    inner ℝ ub (planeHkValueOperator 1 z) - inner ℝ ua (planeHkValueOperator 1 z) =
      ∫ t in a..b, inner ℝ (dual t) z := by
  have hi : IntervalIntegrable dual volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr (hdual.integrable (by norm_num))
  have he (w : PlaneHk univ 1 E) : inner ℝ (∫ t in a..b, dual t) w =
      ∫ t in a..b, inner ℝ (dual t) w := by
    have hp := (innerSL ℝ w).intervalIntegral_comp_comm hi
    change (∫ t in a..b, inner ℝ w (dual t)) = inner ℝ w (∫ t in a..b, dual t) at hp
    calc
      _ = inner ℝ w (∫ t in a..b, dual t) := real_inner_comm _ _
      _ = ∫ t in a..b, inner ℝ w (dual t) := hp.symm
      _ = _ := intervalIntegral.integral_congr (fun t _ => real_inner_comm _ _)
  let L : PlaneHk univ 1 E →L[ℝ] ℝ :=
    (innerSL ℝ ub).comp (planeHkValueOperator 1) - (innerSL ℝ ua).comp (planeHkValueOperator 1)
  let M : PlaneHk univ 1 E →L[ℝ] ℝ := innerSL ℝ (∫ t in a..b, dual t)
  have hLM : L = M := by
    apply planeH1_CLM_ext_scalar_compact
    intro q hq hs e
    change inner ℝ ub (planeHkValueOperator 1 _) - inner ℝ ua (planeHkValueOperator 1 _) =
      inner ℝ (∫ t in a..b, dual t) _
    rw [he]
    exact h q hq hs e
  have hp := congrArg (fun T : PlaneHk univ 1 E →L[ℝ] ℝ => T z) hLM
  change inner ℝ ub (planeHkValueOperator 1 z) - inner ℝ ua (planeHkValueOperator 1 z) =
    inner ℝ (∫ t in a..b, dual t) z at hp
  exact hp.trans (he z)
end

/-! The genuine native weak curve is determined by compact scalar-direction increments and its energy time classes. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeWeakCurve_of_compact_tests {a b : ℝ}
    (u : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (slice dual : ℝ → PlaneHk univ 1 E)
    (htrace : ContinuousOn u (Icc a b))
    (hstate : MemLp slice 2 (volume.restrict (Icc a b)))
    (hdual : MemLp dual 2 (volume.restrict (Icc a b)))
    (hagrees : ∀ᵐ t ∂volume.restrict (Icc a b), u t = planeHkValueOperator 1 (slice t))
    (hinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
      ∀ (q : Vec 2 → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hs : HasCompactSupport q) (e : E),
        let z := compactSmoothHilbertH1 (fun x => q x • e) (hq.smul contDiff_const) (hs.smul_right)
        inner ℝ (u t) (planeHkValueOperator 1 z) - inner ℝ (u s) (planeHkValueOperator 1 z) =
          ∫ r in s..t, inner ℝ (dual r) z) : PlaneWeakHilbertCurve a b u slice dual := by
  refine ⟨htrace, hstate, hdual, hagrees, ?_⟩
  intro s hs t ht hst z
  have hm : MemLp dual 2 (volume.restrict (Icc s t)) :=
    hdual.mono_measure (Measure.restrict_mono (Icc_subset_Icc hs.1 ht.2) le_rfl)
  exact planeWeak_increment_of_scalar_compact hst (u s) (u t) dual hm (hinc s hs t ht hst) z
end

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! The normalized reference equation has its explicitly computed coupled array: chart metric deviation on the diagonal and the original transformed sources scaled by inverse viscosity. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*} {φ : ℝ → Vec 2 → ℝ}

variable (F : ChartedFamily ι h D P Ctx) (hφ : IsAdmissibleStream φ) (s ν e E : ℝ)
    (actual : ∀ p, Ctx p) (K : ι → ℕ)

def preparationReferenceNormalizedCoefficient (v u : ι) (d : admissibleOrders K D v u)
    (t : ℝ) (x : Vec 2) :
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h v) :=
  planeDiagonalGradientCoefficient K D
    (fun _ r y => chartMetric hφ s (ν⁻¹ * r) y - 1) v u d t x +
      ν⁻¹ • edgeCoefficient (referenceChartedFamily F hφ s) ν e E actual K v u d (ν⁻¹ * t) x

theorem preparationReferenceNormalizedCoefficient_raw_flux (hD : 2 ≤ D)
    (W : ∀ u, PlaneHk Set.univ (K u + 1) (h u)) (v : ι) (t : ℝ) (x : Vec 2) (k : Fin 2) :
    planeRawCouplingFlux K D t (preparationReferenceNormalizedCoefficient F hφ s ν e E actual K)
      W v x k =
      (∑ j : Fin 2, (chartMetric hφ s (ν⁻¹ * t) x k j - if k = j then 1 else 0) •
        (W v).toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K v))⟩, fun _ => j⟩ x) +
      ν⁻¹ • planeRawCouplingFlux K D (ν⁻¹ * t)
        (edgeCoefficient (referenceChartedFamily F hφ s) ν e E actual K) W v x k := by
  unfold preparationReferenceNormalizedCoefficient
  rw [planeRawCouplingFlux_add]
  rw [planeRawCouplingFlux_smul]
  simp only [WithLp.ofLp_add, WithLp.ofLp_smul, Pi.add_apply, Pi.smul_apply]
  rw [planeRawCouplingFlux_diagonal_gradient K D hD]
  simp only [Matrix.sub_apply, Matrix.one_apply]
  rfl

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Each genuine normalized reference constituent splits over its finite
original pieces into its natural Taylor array and the constructed remainder. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem normalized_reference_constituent_constructed_remainder_split
    (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
    (ν e E : ℝ) (hν : ν ≠ 0) (he : 0 < e) (actual : ∀ p, Ctx p)
    (v u : ι) (γ : F.Γ v u) (d : ℕ) (hd : 2 ≤ d) (Ks : ℕ) (s : ℝ)
    (t : Set.Icc tS tZ) (yc z : Vec 2) (timeScale a b τ : ℝ)
    (hτ : τ ∈ Set.Icc a b) (htime : timeScale * τ = t.val) :
    ((e * (e ^ (d - 1))⁻¹) * ν⁻¹) •
      constituentPhysical (referenceChartedFamily F hφ s) ν e E actual v u γ d
        t (yc + e • z) =
      ∑ p ∈ (F.locally_finite tS tZ).toFinset,
        (F.weight p t • nativeArrayAssembly (d - 1) (F.identity v u γ).map
          (fun k I => transportedCoeff
            (fun x => naturalPreparationJacobian hφ (F.piece p).anchor s (yc + e • x))
            (F.identity v u γ).maxOrder
            (fun d A k =>
              let Y := streamFlow φ hφ (F.piece p).anchor (yc + e • z) s
              let Yc := streamFlow φ hφ (F.piece p).anchor yc s
              taylorSlow 0 Ks (fun X => F.flux p (actual p) v u γ d A t X (e⁻¹ • Y) k)
                (E⁻¹ • Yc) (E⁻¹ • (Y - Yc))) (d - 1) I z k) +
        naturalFamilyRemainderNativeArray Ks F p (actual p) v u γ timeScale a b hφ
          (F.piece p).anchor s e E yc (d - 1) τ z) := by
  classical
  rw [constituentPhysical_eq_window_sum (referenceChartedFamily F hφ s) ν e E actual
    tS tZ t t.property v u γ d (yc + e • z), Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro p _
  simpa only [Nat.add_sub_cancel, Nat.add_sub_cancel_right, ChartedFamily.dimFlux,
    ChartedFamily.slowFlux, referenceChartedFamily] using
    weighted_reference_piece_cell_operator_constructed_remainder F hc ν e E hν he
      p (actual p) v u γ (d - 1) (by omega) Ks s t yc z timeScale a b τ hτ htime

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleJointProofs

/-! Finite public polynomial factorial energy gives the true radial moment domain. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem planeCarrier_polynomial_moment_memLp (f : PlaneHk Set.univ K E)
    (ϖ : ℝ) (z : Vec 2) (ρ : ℝ) (hρ : 0 < ρ)
    (he : weightedFactorialNormSq 4 ϖ z ρ K f ≠ ⊤) (a : JetIndex2 K) :
    MemLp (fun y => planeMomentSquareRoot 4 ϖ z y • f.toFunction.jet a y) 2 volume := by
  rw [weightedFactorialNormSq_stored_readout] at he
  have hc := storedChartFactorialEnergy_component_ne_top ρ hρ
    (planeMomentPolynomial 4 ϖ z) f he a
  have hsq : (fun y => planeMomentSquareRoot 4 ϖ z y ^ 2) =
      planeMomentPolynomial 4 ϖ z := funext (planeMomentSquareRoot_sq 4 ϖ z)
  have hm := weighted_plane_memLp_of_chartEnergy_ne_top (planeMomentSquareRoot 4 ϖ z)
    (planeMomentSquareRoot_continuous 4 ϖ z) (planeJetReadoutOperator K a f)
    (by simpa only [hsq] using hc)
  apply hm.ae_eq
  filter_upwards [univToPlane_ae (f.val a)] with y hy
  exact congrArg (fun v : E => planeMomentSquareRoot 4 ϖ z y • v) hy

theorem hasRadialPlaneMoments_of_finite_polynomial (f : PlaneHk Set.univ K E)
    (ϖ : ℝ) (hϖ : 0 < ϖ) (z : Vec 2) (ρ : ℝ) (hρ : 0 < ρ)
    (he : weightedFactorialNormSq 4 ϖ z ρ K f ≠ ⊤) :
    HasRadialPlaneMoments f z := by
  intro a
  apply radialMoment_memLp_of_planeMoment ϖ hϖ z (f.toFunction.jet a)
  · simpa only [Measure.restrict_univ] using (f.toFunction.memL2 a).aestronglyMeasurable
  · exact planeCarrier_polynomial_moment_memLp f ϖ z ρ hρ he a

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! The computed reference cell array separates the unchanged metric perturbation from the exactly priced original source orders. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*} {φ : ℝ → Vec 2 → ℝ}

variable (F : ChartedFamily ι h D P Ctx) (hφ : IsAdmissibleStream φ)
  (s ν e E : ℝ) (actual : ∀ p, Ctx p) (K : ι → ℕ) (yc : Vec 2)

def preparationReferenceCellCoefficient (v u : ι) (d : admissibleOrders K D v u)
    (t : ℝ) (z : Vec 2) :
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h v) :=
  (e * (e ^ (d.1 - 1))⁻¹) • preparationReferenceNormalizedCoefficient F hφ s ν e E actual K
    v u d (e ^ 2 * t) (yc + e • z)

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem preparationReferenceCellCoefficient_eq_metric_add_source (he : e ≠ 0)
    (v u : ι) (d : admissibleOrders K D v u) (t : ℝ) (z : Vec 2) :
    preparationReferenceCellCoefficient F hφ s ν e E actual K yc v u d t z =
      planeDiagonalGradientCoefficient K D
        (fun _ r x => chartMetric hφ s (ν⁻¹ * (e ^ 2 * r)) (yc + e • x) - 1) v u d t z +
      ((e * (e ^ (d.1 - 1))⁻¹) * ν⁻¹) •
        edgeCoefficient (referenceChartedFamily F hφ s) ν e E actual K v u d
          (ν⁻¹ * (e ^ 2 * t)) (yc + e • z) := by
  rw [preparationReferenceCellCoefficient, preparationReferenceNormalizedCoefficient, smul_add,
    planeDiagonalGradientCoefficient_cell_scaling K D _ e he yc v u d t z, smul_smul]

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleJointProofs

/-! Each actual polynomial weighted jet has a quantitative bound from the public energy. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem polynomialMoment_component_eLpNorm_le (f : PlaneHk Set.univ K E)
    (ϖ : ℝ) (z : Vec 2) (ρ : ℝ) (hρ : 0 < ρ) (C : ℝ) (hC : 0 ≤ C)
    (he : weightedFactorialNormSq 4 ϖ z ρ K f ≤ ENNReal.ofReal C) (a : JetIndex2 K) :
    eLpNorm (fun y => planeMomentSquareRoot 4 ϖ z y • f.toFunction.jet a y) 2 volume ≤
      ENNReal.ofReal (Real.sqrt (C / factorialWeight ρ a.1.val)) := by
  have hfinite := ne_top_of_le_ne_top ENNReal.ofReal_ne_top he
  rw [weightedFactorialNormSq_stored_readout] at he hfinite
  have hc := storedChartFactorialEnergy_component_ne_top ρ hρ
    (planeMomentPolynomial 4 ϖ z) f hfinite a
  let q := planeMomentSquareRoot 4 ϖ z
  have hq : Continuous q := planeMomentSquareRoot_continuous 4 ϖ z
  have hs : (fun y => q y ^ 2) = planeMomentPolynomial 4 ϖ z :=
    funext (planeMomentSquareRoot_sq 4 ϖ z)
  let W := weightedPlaneLpReadout q hq (planeJetReadoutOperator K a f)
  have hW : ENNReal.ofReal (‖W‖ ^ 2) =
      chartScalarEnergy (planeMomentPolynomial 4 ϖ z) (planeJetReadoutOperator K a f) := by
    exact (weightedPlaneLpReadout_energy q hq _ (by simpa only [hs] using hc)).trans
      (congrArg (fun w => chartScalarEnergy w (planeJetReadoutOperator K a f)) hs)
  have hw := factorialWeight_pos_of_radius_pos ρ hρ a.1.val
  have hb : factorialWeight ρ a.1.val * ‖W‖ ^ 2 ≤ C := by
    have hh := (Finset.single_le_sum (f := fun α : JetIndex2 K =>
      ENNReal.ofReal (factorialWeight ρ α.1.val) *
        chartScalarEnergy (planeMomentPolynomial 4 ϖ z) (planeJetReadoutOperator K α f))
      (fun _ _ => bot_le) (Finset.mem_univ a)).trans he
    rw [← hW, ← ENNReal.ofReal_mul hw.le] at hh
    exact (ENNReal.ofReal_le_ofReal_iff hC).mp hh
  have hn : ‖W‖ ≤ Real.sqrt (C / factorialWeight ρ a.1.val) := by
    apply (Real.le_sqrt (norm_nonneg W) (div_nonneg hC hw.le)).mpr
    exact (le_div_iff₀ hw).mpr (by simpa only [mul_comm] using hb)
  have hae : W =ᵐ[volume] fun y => q y • f.toFunction.jet a y := by
    have hraw := univToPlane_ae (f.val a)
    have hr := weightedPlaneLpReadout_ae q hq (planeJetReadoutOperator K a f)
      (by simpa only [hs] using hc)
    filter_upwards [hr, hraw] with y hy hx
    exact hy.trans (congrArg (fun v : E => q y • v) hx)
  rw [← eLpNorm_congr_ae hae, ← Lp.enorm_def, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hn
end

/-! The canonical weighted L2 readout agrees with the literal polynomial-weighted jet. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem polynomialMomentLpReadout_ae (f : PlaneHk Set.univ K E)
    (ϖ : ℝ) (z : Vec 2) (ρ : ℝ) (hρ : 0 < ρ)
    (he : weightedFactorialNormSq 4 ϖ z ρ K f ≠ ⊤) (a : JetIndex2 K) :
    weightedPlaneLpReadout (planeMomentSquareRoot 4 ϖ z)
      (planeMomentSquareRoot_continuous 4 ϖ z) (planeJetReadoutOperator K a f) =ᵐ[volume]
        fun y => planeMomentSquareRoot 4 ϖ z y • f.toFunction.jet a y := by
  rw [weightedFactorialNormSq_stored_readout] at he
  have hc := storedChartFactorialEnergy_component_ne_top ρ hρ
    (planeMomentPolynomial 4 ϖ z) f he a
  have hs : (fun y => planeMomentSquareRoot 4 ϖ z y ^ 2) = planeMomentPolynomial 4 ϖ z :=
    funext (planeMomentSquareRoot_sq 4 ϖ z)
  have hr := weightedPlaneLpReadout_ae (planeMomentSquareRoot 4 ϖ z)
    (planeMomentSquareRoot_continuous 4 ϖ z) (planeJetReadoutOperator K a f)
    (by simpa only [hs] using hc)
  filter_upwards [hr, univToPlane_ae (f.val a)] with y hy hx
  exact hy.trans (congrArg (fun v : E => planeMomentSquareRoot 4 ϖ z y • v) hx)

theorem polynomialMoment_eLpNorm_eq_readout_norm (f : PlaneHk Set.univ K E)
    (ϖ : ℝ) (z : Vec 2) (ρ : ℝ) (hρ : 0 < ρ)
    (he : weightedFactorialNormSq 4 ϖ z ρ K f ≠ ⊤) (a : JetIndex2 K) :
    eLpNorm (fun y => planeMomentSquareRoot 4 ϖ z y • f.toFunction.jet a y) 2 volume =
      ENNReal.ofReal (‖weightedPlaneLpReadout (planeMomentSquareRoot 4 ϖ z)
        (planeMomentSquareRoot_continuous 4 ϖ z) (planeJetReadoutOperator K a f)‖) := by
  rw [← eLpNorm_congr_ae (polynomialMomentLpReadout_ae f ϖ z ρ hρ he a),
    ← Lp.enorm_def, ofReal_norm]
end

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergy.Variational AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Scalar-weighted factorial energies have an actual Hilbert realization which preserves finite source sums. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

/-- The literal weighted raw jets with their factorial Hilbert weights. -/
def scalarWeightedFactorialJet (ρ : ℝ) (q : Vec 2 → ℝ) (U : PlaneHk Set.univ K E)
    (hD : JetMemL2On Set.univ (fun β x => q x • U.toFunction.jet β x)) :
    JetL2 (volume.restrict Set.univ) K E :=
  factorialWeightedJet ρ (jetToL2 (fun β x => q x • U.toFunction.jet β x) hD)

theorem scalarWeightedFactorialJet_normSq (ρ : ℝ) (q : Vec 2 → ℝ)
    (U : PlaneHk Set.univ K E)
    (hD : JetMemL2On Set.univ (fun β x => q x • U.toFunction.jet β x)) :
    ENNReal.ofReal (‖scalarWeightedFactorialJet ρ q U hD‖ ^ 2) =
      storedChartFactorialEnergy ρ (fun x => q x ^ 2) U := by
  rw [scalarWeightedFactorialJet, factorialWeightedJet_normSq,
    storedChartFactorialEnergy_weighted_jet_readout ρ q U hD]

theorem scalarWeightedFactorialJet_moment_normSq (n : ℕ) (ϖ : ℝ) (zc : Vec 2)
    (ρ : ℝ) (U : PlaneHk Set.univ K E)
    (hD : JetMemL2On Set.univ
      (fun β x => planeMomentSquareRoot n ϖ zc x • U.toFunction.jet β x)) :
    ENNReal.ofReal (‖scalarWeightedFactorialJet ρ (planeMomentSquareRoot n ϖ zc) U hD‖ ^ 2) =
      weightedFactorialNormSq n ϖ zc ρ K U := by
  rw [scalarWeightedFactorialJet_normSq]
  have hq : (fun x => planeMomentSquareRoot n ϖ zc x ^ 2) = planeMomentPolynomial n ϖ zc :=
    funext (planeMomentSquareRoot_sq n ϖ zc)
  rw [hq, ← weightedFactorialNormSq_stored_readout]

theorem scalarWeightedFactorialJet_sum {J : Type*} [Fintype J]
    (ρ : ℝ) (q : Vec 2 → ℝ) (U : J → PlaneHk Set.univ K E)
    (hD : ∀ j, JetMemL2On Set.univ (fun β x => q x • (U j).toFunction.jet β x))
    (hS : JetMemL2On Set.univ (fun β x => q x • (∑ j, U j).toFunction.jet β x)) :
    scalarWeightedFactorialJet ρ q (∑ j, U j) hS =
      ∑ j, scalarWeightedFactorialJet ρ q (U j) (hD j) := by
  classical
  unfold scalarWeightedFactorialJet
  rw [← factorialWeightedJet_sum]
  congr 1
  apply PiLp.ext
  intro β
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  apply Lp.ext
  simp only [Measure.restrict_univ]
  have ht := planeJetOrder_finite_sum_ae (Nat.le_of_lt_succ β.1.isLt) U β.2
  have hraw : (∑ j, U j).toFunction.jet β =ᵐ[volume]
      (fun x => ∑ j, (U j).toFunction.jet β x) := by
    filter_upwards [ht] with x hx
    simpa only [planeJetOrder, dite_eq_left (Nat.le_of_lt_succ β.1.isLt)] using hx
  have hs := Lp.coeFn_finsetSum Finset.univ
    (fun j => (hD j β).toLp (fun x => q x • (U j).toFunction.jet β x))
  have hd := ae_all_iff.mpr (fun j => (hD j β).coeFn_toLp)
  simp only [Measure.restrict_univ] at hs hd
  have hsum := hS β |>.coeFn_toLp
  simp only [Measure.restrict_univ] at hsum
  filter_upwards [hraw, hs, hd, hsum] with x hx hsx hdx hsumx
  change ((hS β).toLp _) x = (∑ j, (hD j β).toLp _) x
  rw [hsumx, hsx]
  rw [Finset.sum_apply, hx, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact (hdx j).symm

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted AVRegularity.CycleWords
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Positive derivative tensors consume the original dissipative reserve, with only a fixed derivative-order price. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem planePositiveDerivativeTensor_weighted_gradient_budget {K L : ℕ}
    (ρ : ℝ) (hρ : 0 < ρ) (m : ℕ) (hm : 1 ≤ m) (hKL : K + (m - 1) ≤ L)
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (U : PlaneHk Set.univ (L + 1) E) :
    weightedFactorialNormSq n ϖ zc ρ K (planePositiveDerivativeTensor m hm hKL U) ≤
      (Fintype.card (DerivativeWord2 m) : ℝ≥0∞) *
        (ENNReal.ofReal ((derivativeReserveFactor ρ K (m - 1)) ^ 2) *
          weightedGradFactorialNormSq n ϖ zc ρ L U) := by
  have hres : K + m ≤ L + 1 := by omega
  have ht : planePositiveDerivativeTensor m hm hKL U =
      planeFamilyTensor (fun I : DerivativeWord2 m => derivativeSourceOperator hres I U) := by
    cases m with
    | zero => omega
    | succ s => rfl
  rw [ht, weightedFactorialNormSq_stored_readout]
  have hq : (fun x => planeMomentSquareRoot n ϖ zc x ^ 2) = planeMomentPolynomial n ϖ zc :=
    funext (planeMomentSquareRoot_sq n ϖ zc)
  rw [← hq, planeFamilyTensor_weighted_factorialEnergy ρ _
    (planeMomentSquareRoot_continuous n ϖ zc)]
  simp_rw [hq, ← weightedFactorialNormSq_stored_readout]
  calc
    _ ≤ ∑ _I : DerivativeWord2 m,
        ENNReal.ofReal ((derivativeReserveFactor ρ K (m - 1)) ^ 2) *
          weightedGradFactorialNormSq n ϖ zc ρ L U :=
      Finset.sum_le_sum (fun I _ => derivativeSourceOperator_weightedFactorialNormSq_le
        hres hm I ρ hρ n ϖ zc U)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Finite literal source sums preserve the weighted raw-jet L2 carrier without any quantitative vertex price. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem scalarWeightedJet_memL2_sum {J : Type*} [Fintype J]
    (q : Vec 2 → ℝ) (U : J → PlaneHk Set.univ K E)
    (hD : ∀ j, JetMemL2On Set.univ (fun β x => q x • (U j).toFunction.jet β x)) :
    JetMemL2On Set.univ (fun β x => q x • (∑ j, U j).toFunction.jet β x) := by
  classical
  intro β
  have hj (j : J) : MemLp (fun x => q x • (U j).toFunction.jet β x) 2 volume := by
    simpa only [Measure.restrict_univ] using hD j β
  have hsum := memLp_finsetSum Finset.univ (fun j _ => hj j)
  have hraw : (fun x => q x • (∑ j, U j).toFunction.jet β x) =ᵐ[volume]
      (fun x => ∑ j, q x • (U j).toFunction.jet β x) := by
    filter_upwards [planeJetOrder_finite_sum_ae (Nat.le_of_lt_succ β.1.isLt) U β.2] with x hx
    have he := congrArg (fun y => q x • y) hx
    simpa only [planeJetOrder, dite_eq_left (Nat.le_of_lt_succ β.1.isLt), Finset.smul_sum] using he
  simpa only [Measure.restrict_univ, Finset.sum_apply] using hsum.ae_eq hraw.symm

end AVRegularity.CycleJointProofs
end
