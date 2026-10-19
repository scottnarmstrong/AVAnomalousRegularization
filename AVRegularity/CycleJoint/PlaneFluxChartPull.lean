-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.PlaneCoupledSolutionOfRawFluxCurves
import AVRegularity.CycleJoint.PlaneCoupledFluxScaling
import AVRegularity.CoupledEnergyPlane.Variational.ResidualValueSource

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Actual finite word-array flux pairings have integrable time curves and an absolute image price. -/

variable {ι X : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  [MeasurableSpace X] {K L : ℕ}

theorem couplingFlux_pairing_time_integrable_summable {r : ℕ} (i i' : ι) (μ : Measure X) [IsFiniteMeasure μ]
    (U : Set (Vec 2)) (R : ℝ) (hR : 0 < R) (hU : U ⊆ Metric.ball (0 : Vec 2) R)
    (A : X → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 r => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i)) (hc : ∀ t, Continuous (A t))
    (hj : Measurable (Function.uncurry A)) (MC : ℝ) (hMC : 0 ≤ MC)
    (hA : ∀ t x, ‖A t x‖ ≤ MC)
    (f : X → PlaneHk Set.univ K (h i')) (hf : MemLp f 2 μ) (z : Vec 2) (α : DerivativeWord2 r → JetIndex2 K)
    (φ : PlaneHk Set.univ L (h i)) (β : JetIndex2 L) (k : Fin 2)
    (hφ : ∀ᵐ x ∂volume, x ∉ U → φ.toFunction.jet β x = 0)
    (M : X → ℝ) (hM : MemLp M 2 μ)
    (hw : ∀ j, ∀ᵐ t ∂μ, AEStronglyMeasurable
      (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet (α j) y) volume)
    (hb : ∀ j, ∀ᵐ t ∂μ, eLpNorm
      (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet (α j) y) 2 volume ≤ ENNReal.ofReal ‖M t‖) :
    (∀ n : Fin 2 → ℤ, Integrable (fun t => ∫ x, inner ℝ
      (A t x (WithLp.toLp 2 (fun w =>
        (planeCarrierTranslation K (AVenhance.latticeShift n) (f t)).toFunction.jet (α w) x)) k)
      (φ.toFunction.jet β x)) μ) ∧
    Summable (fun n : Fin 2 → ℤ => ∫ t, ‖∫ x, inner ℝ
      (A t x (WithLp.toLp 2 (fun w =>
        (planeCarrierTranslation K (AVenhance.latticeShift n) (f t)).toFunction.jet (α w) x)) k)
      (φ.toFunction.jet β x)‖ ∂μ) := by
  let C := fun w t => couplingEntryCoefficient i i' (A t) w k
  have hcC : ∀ w t, Continuous (C w t) := fun w t =>
    couplingEntryCoefficient_continuous i i' (A t) (hc t) w k
  have hjC : ∀ w, Measurable (Function.uncurry (C w)) := fun w =>
    couplingEntryCoefficient_joint_measurable i i' A hj w k
  have hbC : ∀ w t x, ‖C w t x‖ ≤ MC := fun w t x =>
    (couplingEntryCoefficient_norm_le i i' (A t) w k x).trans (hA t x)
  let G := fun w (n : Fin 2 → ℤ) t => ∫ x, inner ℝ
    (C w t x ((planeCarrierTranslation K (AVenhance.latticeShift n) (f t)).toFunction.jet (α w) x))
    (φ.toFunction.jet β x)
  have hi : ∀ w n, Integrable (G w n) μ := fun w n =>
    translated_coefficient_pairing_time_integrable μ (C w) (hcC w) (hjC w) MC hMC (hbC w)
      f hf (AVenhance.latticeShift n) (α w) φ β
  have he (n : Fin 2 → ℤ) (t : X) :
      (∫ x, inner ℝ (A t x (WithLp.toLp 2 (fun w =>
        (planeCarrierTranslation K (AVenhance.latticeShift n) (f t)).toFunction.jet (α w) x)) k)
        (φ.toFunction.jet β x)) = ∑ w : DerivativeWord2 r, G w n t :=
    (couplingFlux_pairing_integral i i' volume (A t) _ _ k (fun w =>
      translated_coefficient_pairing_space_integrable (AVenhance.latticeShift n)
        (C w t) (hcC w t) MC hMC (hbC w t) (f t) (α w) φ β)).2
  refine ⟨fun n => ?_, ?_⟩
  · exact (integrable_finsetSum Finset.univ (fun w _ => hi w n)).congr
      (Filter.Eventually.of_forall (fun t => (he n t).symm))
  · have hs := finite_pairing_time_summable μ Finset.univ G (fun w _ n => hi w n)
      (fun w _ => translated_coefficient_pairing_time_summable μ U R hR hU
        (C w) (hcC w) (hjC w) MC hMC (hbC w) f hf z (α w) φ β hφ M hM (hw w) (hb w))
    exact hs.congr (fun n => integral_congr_ae
      (Filter.Eventually.of_forall (fun t => congrArg norm (he n t).symm)))

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The literal weighted native array of an original family's natural-chart
slow remainder, retaining its anchor, reference time and full Piola Jacobian. -/

section
variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

def naturalFamilyRemainderNativeArray (Ks : ℕ) (F : ChartedFamily ι h D P Ctx)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u)
    (timeScale a b : ℝ) {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (r σ e E : ℝ) (yc : Vec 2) (rjet : ℕ) (τ : ℝ) (z : Vec 2) :=
  nativeArrayAssembly rjet (F.identity v u γ).map
    (fun k I => F.weight p (timeScale * τ) * transportedCoeff
      (fun y => naturalPreparationJacobian hφ r σ (yc + e • y))
      (F.identity v u γ).maxOrder
      (fun d I k => naturalSlowRemainderTimeCoefficient Ks
        (fun t X y => F.flux p c v u γ d I (timeScale * t) X y k)
        a b hφ r (fun _ => σ) e E yc τ z) rjet I z k)
end

/-! On the preparation interval the constructed native remainder array is
exactly the weighted difference from the natural slow Taylor array. -/

section
variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem naturalFamilyRemainderNativeArray_readout
    (Ks : ℕ) (F : ChartedFamily ι h D P Ctx)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u)
    (timeScale a b : ℝ) {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (r σ e E : ℝ) (yc : Vec 2) (rjet : ℕ) (τ : ℝ) (hτ : τ ∈ Set.Icc a b) (z : Vec 2) :
    let Y := streamFlow φ hφ r (yc + e • z) σ
    let Yc := streamFlow φ hφ r yc σ
    let B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2 :=
      fun d I => F.flux p c v u γ d I (timeScale * τ) (E⁻¹ • Y) (e⁻¹ • Y)
    let Bp : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2 :=
      fun d I k => taylorSlow 0 Ks
        (fun X => F.flux p c v u γ d I (timeScale * τ) X (e⁻¹ • Y) k)
        (E⁻¹ • Yc) (E⁻¹ • (Y - Yc))
    naturalFamilyRemainderNativeArray Ks F p c v u γ timeScale a b hφ r σ e E yc rjet τ z =
      F.weight p (timeScale * τ) • nativeArrayAssembly rjet (F.identity v u γ).map
        (fun k I => transportedCoeff
          (fun y => naturalPreparationJacobian hφ r σ (yc + e • y))
          (F.identity v u γ).maxOrder (fun d I => B d I - Bp d I) rjet I z k) := by
  dsimp only [naturalFamilyRemainderNativeArray, naturalSlowRemainderTimeCoefficient]
  simp only [ite_eq_left hτ]
  change (nativeArrayAssembly rjet (F.identity v u γ).map)
    (F.weight p (timeScale * τ) • _) = _
  exact map_smul (nativeArrayAssembly rjet (F.identity v u γ).map) _ _
end

/-! The original weighted slow Taylor array in its genuine natural coordinates. -/

section
variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

def naturalFamilyTaylorNativeArray (Ks : ℕ) (F : ChartedFamily ι h D P Ctx)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u)
    (timeScale : ℝ) {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (r σ e E : ℝ) (yc : Vec 2) (rjet : ℕ) (τ : ℝ) (z : Vec 2) :=
  let Y := streamFlow φ hφ r (yc + e • z) σ
  let Yc := streamFlow φ hφ r yc σ
  F.weight p (timeScale * τ) • nativeArrayAssembly rjet (F.identity v u γ).map
    (fun k I => transportedCoeff
      (fun x => naturalPreparationJacobian hφ r σ (yc + e • x))
      (F.identity v u γ).maxOrder
      (fun d A k => taylorSlow 0 Ks
        (fun X => F.flux p c v u γ d A (timeScale * τ) X (e⁻¹ • Y) k)
        (E⁻¹ • Yc) (E⁻¹ • (Y - Yc))) rjet I z k)
end

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleReference AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! The native chart drift pairs with pulled gradients exactly as the physical drift does. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeH1ChartPull_transport_pairing {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (t s : ℝ) (v : ℝ → Vec 2 → Vec 2) (u z : PlaneHk univ 1 E) :
    (∫ y, vecDot (chartVector hφ s v t y) (fun k =>
      inner ℝ (planeHkValueOperator 1 (planeH1ChartPull hφ t s z) y)
        (planeH1GradientOperator (planeH1ChartPull hφ t s u) k y))) =
      ∫ x, vecDot (v t x) (fun k => inner ℝ (planeHkValueOperator 1 z x)
        (planeH1GradientOperator u k x)) := by
  calc
    _ = ∫ y, vecDot (v t (AVRegularity.streamFlow φ hφ t y s)) (fun k =>
        inner ℝ (planeHkValueOperator 1 z (AVRegularity.streamFlow φ hφ t y s))
          (planeH1GradientOperator u k (AVRegularity.streamFlow φ hφ t y s))) := by
      apply integral_congr_ae
      have hu := ae_all_iff.mpr (fun k => planeH1ChartPull_gradient_ae hφ t s u k)
      filter_upwards [hu, planeH1ChartPull_value_ae hφ t s z] with y huy hzy
      simp_rw [huy, hzy, hilbertChartGradient_inner]
      exact inverse_pullback_pairing (chartJac hφ s t y)
        (by rw [chartJac, streamFlow_jacMatrix_det_one hφ]; exact isUnit_one) _ _
    _ = _ := integral_streamFlow hφ t s (fun x => vecDot (v t x)
      (fun k => inner ℝ (planeHkValueOperator 1 z x) (planeH1GradientOperator u k x)))

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The full periodized word-array flux has a genuine integrable time pairing. -/

variable {ι X : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  [MeasurableSpace X] {K L : ℕ}

theorem periodized_couplingFlux_pairing_time_integrable {r : ℕ} (i i' : ι) (μ : Measure X) [IsFiniteMeasure μ]
    (U : Set (Vec 2)) (hUm : MeasurableSet U) (R : ℝ) (hR : 0 < R) (hU : U ⊆ Metric.ball (0 : Vec 2) R)
    (A : X → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 r => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i)) (hc : ∀ t, Continuous (A t))
    (hj : Measurable (Function.uncurry A)) (MC : ℝ) (hMC : 0 ≤ MC)
    (hA : ∀ t x, ‖A t x‖ ≤ MC)
    (f : X → PlaneHk Set.univ K (h i')) (hf : MemLp f 2 μ) (z : Vec 2) (α : DerivativeWord2 r → JetIndex2 K)
    (φ : PlaneHk Set.univ L (h i)) (β : JetIndex2 L) (k : Fin 2)
    (hφ : ∀ᵐ x ∂volume, x ∉ U → φ.toFunction.jet β x = 0)
    (M : X → ℝ) (hM : MemLp M 2 μ)
    (hw : ∀ j, ∀ᵐ t ∂μ, AEStronglyMeasurable
      (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet (α j) y) volume)
    (hb : ∀ j, ∀ᵐ t ∂μ, eLpNorm
      (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet (α j) y) 2 volume ≤ ENNReal.ofReal ‖M t‖) :
    Integrable (fun t => ∫ x, inner ℝ
      (A t x (WithLp.toLp 2 (fun w => periodizeRawJet (f t).toFunction.jet (α w) x)) k)
      (φ.toFunction.jet β x)) μ := by
  let C := fun w t => couplingEntryCoefficient i i' (A t) w k
  have hcC : ∀ w t, Continuous (C w t) := fun w t =>
    couplingEntryCoefficient_continuous i i' (A t) (hc t) w k
  have hjC : ∀ w, Measurable (Function.uncurry (C w)) := fun w =>
    couplingEntryCoefficient_joint_measurable i i' A hj w k
  have hbC : ∀ w t x, ‖C w t x‖ ≤ MC := fun w t x =>
    (couplingEntryCoefficient_norm_le i i' (A t) w k x).trans (hA t x)
  have hi : ∀ w : DerivativeWord2 r, Integrable (fun t => ∫ x, inner ℝ
      (C w t x (periodizeRawJet (f t).toFunction.jet (α w) x)) (φ.toFunction.jet β x)) μ :=
    fun w => periodized_coefficient_pairing_time_integrable μ U R hR hU
      (C w) (hcC w) (hjC w) MC hMC (hbC w) f hf z (α w) φ β hφ M hM (hw w) (hb w)
  apply (integrable_finsetSum Finset.univ (fun w _ => hi w)).congr
  have hwA := ae_all_iff.mpr hw
  have hbA := ae_all_iff.mpr hb
  filter_upwards [hwA, hbA] with t hwt hbt
  exact (couplingFlux_pairing_integral i i' volume (A t) _ _ k (fun w =>
    periodized_compact_coefficient_pairing_integrable U hUm (C w t) (hcC w t)
      MC hMC (hbC w t) (f t) (α w) φ β hφ
      (planeImageJetCLM_radial_enorm_tsum_lt_top U R hR hU z (α w) (f t) ‖M t‖
        (norm_nonneg _) (hwt w) (hbt w)))).2.symm

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The actual physical and edge coefficients retain the independent spatial reserve. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem constituentPhysical_spatial_smooth
    (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
    (ν e E : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ)) E n)
    (actual : ∀ p, Ctx p) (v u : ι) (γ : F.Γ v u) (d : ℕ)
    (t : ℝ) (ht : t ∈ Set.Icc tS tZ) :
    ContDiff ℝ (n v : ℕ) (constituentPhysical F ν e E actual v u γ d t) := by
  let b := fun p t x k (A : DerivativeWord2 (d - 1)) =>
    transportedCoeff (chartInvJacobian ⇑((F.piece p).material t).symm)
      (F.identity v u γ).maxOrder
      (fun d' I => F.dimFlux ν e E p (actual p) v u γ d' I t
        (((F.piece p).material t).symm x)
        (e⁻¹ • ((F.piece p).material t).symm x)) (d - 1) A x k
  change ContDiff ℝ (n v : ℕ) (fun x : Vec 2 => ∑ᶠ p,
    F.weight p t • (nativeArrayAssembly (d - 1) (F.identity v u γ).map (b p t x)))
  apply piece_finsum_spatial_smooth_onWindow F tS tZ
    (fun p s x => F.weight p s • (nativeArrayAssembly (d - 1)
      (F.identity v u γ).map (b p s x))) (n v) _ _ t ht
  · intro p s hs'
    have hm := nativeArrayAssembly_spatial_smooth (d - 1) (n v) (F.identity v u γ).map
      (fun x k A => F.weight p s * b p s x k A)
      (fun k A => weighted_piece_array_spatial_smooth F hc ν e E n hs
        p (actual p) v u γ (d - 1) A k ⟨s, hs'⟩)
    convert hm using 1
    funext x
    exact ((nativeArrayAssembly (d - 1) (F.identity v u γ).map).map_smul
      (F.weight p s) (b p s x)).symm
  · intro p s x hout
    rw [F.weight_zero p s hout]
    exact zero_smul ℝ (nativeArrayAssembly (d - 1) (F.identity v u γ).map (b p s x))

theorem physicalCoefficient_spatial_smooth
    (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
    (ν e E : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ)) E n)
    (actual : ∀ p, Ctx p) (v u : ι) (d : ℕ) (t : ℝ) (ht : t ∈ Set.Icc tS tZ) :
    ContDiff ℝ (n v : ℕ) (physicalCoefficient F ν e E actual v u d t) := by
  unfold physicalCoefficient
  exact ContDiff.sum (fun γ _ =>
    constituentPhysical_spatial_smooth F hc ν e E n hs actual v u γ d t ht)

theorem edgeCoefficient_spatial_smooth [Fintype ι]
    (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
    (ν e E : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ)) E n)
    (actual : ∀ p, Ctx p) (K : ι → ℕ) (v u : ι) (d : admissibleOrders K D v u)
    (t : ℝ) (ht : t ∈ Set.Icc tS tZ) :
    ContDiff ℝ (n v : ℕ) (edgeCoefficient F ν e E actual K v u d t) :=
  physicalCoefficient_spatial_smooth F hc ν e E n hs actual v u d.1 t ht

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! The pulled native Hilbert H1 gradients have the exact physical metric energy pairing. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeH1ChartPull_metric_pairing {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (t s : ℝ) (u z : PlaneHk univ 1 E) :
    (∫ y, ∑ k : Fin 2, inner ℝ (planeH1GradientOperator (planeH1ChartPull hφ t s u) k y)
      (hilbertMatrixAction (chartMetric hφ s t y)
        (fun j => planeH1GradientOperator (planeH1ChartPull hφ t s z) j y) k)) =
      ∫ x, ∑ k : Fin 2, inner ℝ (planeH1GradientOperator u k x)
        (planeH1GradientOperator z k x) := by
  calc
    _ = ∫ y, ∑ k : Fin 2,
        inner ℝ (planeH1GradientOperator u k (AVRegularity.streamFlow φ hφ t y s))
          (planeH1GradientOperator z k (AVRegularity.streamFlow φ hφ t y s)) := by
      apply integral_congr_ae
      have hu := ae_all_iff.mpr (fun k => planeH1ChartPull_gradient_ae hφ t s u k)
      have hz := ae_all_iff.mpr (fun k => planeH1ChartPull_gradient_ae hφ t s z k)
      filter_upwards [hu, hz] with y huy hzy
      simp_rw [huy, hzy]
      exact hilbertMatrixAction_metric_pair
        (jacMatrix (fun x => AVRegularity.streamFlow φ hφ t x s) y)
        (by rw [streamFlow_jacMatrix_det_one hφ]; exact isUnit_one) _ _
    _ = _ := integral_streamFlow hφ t s (fun x => ∑ k : Fin 2,
      inner ℝ (planeH1GradientOperator u k x) (planeH1GradientOperator z k x))

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Both genuine natural native arrays vanish at and above the original
identity's maximal source order, independently of the state jet. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem naturalFamilyTaylorNativeArray_zero_at_or_above
    (Ks : ℕ) (F : ChartedFamily ι h D P Ctx)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u)
    (timeScale : ℝ) {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (r σ e E : ℝ) (yc : Vec 2) (rjet : ℕ)
    (hr : (F.identity v u γ).maxOrder ≤ rjet) (τ : ℝ) (z : Vec 2) :
    naturalFamilyTaylorNativeArray Ks F p c v u γ timeScale hφ r σ e E yc rjet τ z = 0 := by
  dsimp only [naturalFamilyTaylorNativeArray]
  have hb : (fun k I => transportedCoeff
      (fun x => naturalPreparationJacobian hφ r σ (yc + e • x))
      (F.identity v u γ).maxOrder
      (fun d A k => taylorSlow 0 Ks
        (fun X => F.flux p c v u γ d A (timeScale * τ) X
          (e⁻¹ • streamFlow φ hφ r (yc + e • z) σ) k)
        (E⁻¹ • streamFlow φ hφ r yc σ)
        (E⁻¹ • (streamFlow φ hφ r (yc + e • z) σ - streamFlow φ hφ r yc σ))) rjet I z k) = 0 := by
    funext k I
    rw [transportedCoeff_zero_at_or_above _ _ _ _ hr]
    rfl
  rw [hb, map_zero]
  ext g k
  simp

theorem naturalFamilyRemainderNativeArray_zero_at_or_above
    (Ks : ℕ) (F : ChartedFamily ι h D P Ctx)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u)
    (timeScale a b : ℝ) {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (r σ e E : ℝ) (yc : Vec 2) (rjet : ℕ)
    (hr : (F.identity v u γ).maxOrder ≤ rjet) (τ : ℝ) (z : Vec 2) :
    naturalFamilyRemainderNativeArray Ks F p c v u γ timeScale a b hφ r σ e E yc rjet τ z = 0 := by
  dsimp only [naturalFamilyRemainderNativeArray]
  have hb : (fun k I => F.weight p (timeScale * τ) * transportedCoeff
      (fun y => naturalPreparationJacobian hφ r σ (yc + e • y))
      (F.identity v u γ).maxOrder
      (fun d I k => naturalSlowRemainderTimeCoefficient Ks
        (fun t X y => F.flux p c v u γ d I (timeScale * t) X y k)
        a b hφ r (fun _ => σ) e E yc τ z) rjet I z k) = 0 := by
    funext k I
    rw [transportedCoeff_zero_at_or_above _ _ _ _ hr]
    simp only [Pi.zero_apply, mul_zero]
  rw [hb, map_zero]

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! The actual viscosity times chart metric has the physical native diffusion pairing. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeH1ChartPull_diffusion_pairing {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (t s ν : ℝ) (u z : PlaneHk univ 1 E) :
    (∫ y, ∑ k : Fin 2, inner ℝ
      (hilbertMatrixAction (ν • chartMetric hφ s t y)
        (fun j => planeH1GradientOperator (planeH1ChartPull hφ t s u) j y) k)
      (planeH1GradientOperator (planeH1ChartPull hφ t s z) k y)) =
      ν * ∫ x, ∑ k : Fin 2, inner ℝ (planeH1GradientOperator u k x)
        (planeH1GradientOperator z k x) := by
  calc
    _ = ν * ∫ y, ∑ k : Fin 2,
        inner ℝ (planeH1GradientOperator (planeH1ChartPull hφ t s z) k y)
          (hilbertMatrixAction (chartMetric hφ s t y)
            (fun j => planeH1GradientOperator (planeH1ChartPull hφ t s u) j y) k) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        have hm (i j : Fin 2) : (ν • chartMetric hφ s t y) i j =
            ν * chartMetric hφ s t y i j := rfl
        have hi (i j : Fin 2) :
            inner ℝ (planeH1GradientOperator (planeH1ChartPull hφ t s z) i y)
              (planeH1GradientOperator (planeH1ChartPull hφ t s u) j y) =
            inner ℝ (planeH1GradientOperator (planeH1ChartPull hφ t s u) j y)
              (planeH1GradientOperator (planeH1ChartPull hφ t s z) i y) := real_inner_comm _ _
        simp only [hilbertMatrixAction, Fin.sum_univ_two, inner_add_left, inner_add_right,
          real_inner_smul_left, real_inner_smul_right, hm, hi]
        ring
    _ = ν * ∫ x, ∑ k : Fin 2, inner ℝ (planeH1GradientOperator z k x)
        (planeH1GradientOperator u k x) := by
      rw [planeH1ChartPull_metric_pairing]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => Finset.sum_congr rfl
        (fun k _ => real_inner_comm _ _)

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Actual image equations normalize to the signed spatial integral atoms used by transfer. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeHomogeneous_image_integral_atom_equation (K : ι → ℕ) (D : ℕ) (ν a b : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (hvp : ∀ s, AVenhance.IsZ2Periodic (v s))
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hAp : ∀ i i' d s, AVenhance.IsZ2Periodic (A i i' d s))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane ν a b v D K A f (fun _ _ => 0) (fun _ _ => 0) u w)
    (i : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) (ψ : PlaneHk Set.univ 1 (h i))
    (hv : ∀ s ∈ Set.Ioc a t, Continuous (v s))
    (hvb : ∀ s ∈ Set.Ioc a t, ∃ V : ℝ, 0 ≤ V ∧ ∀ x, ‖v s x‖ ≤ V)
    (hc : ∀ s ∈ Set.Ioc a t, ∀ i' d, Continuous (A i i' d s))
    (M : ℝ → ∀ i', admissibleOrders K D i i' → ℝ)
    (hM : ∀ s ∈ Set.Ioc a t, ∀ i' d, 0 ≤ M s i' d)
    (hb : ∀ s ∈ Set.Ioc a t, ∀ i' d x, ‖A i i' d s x‖ ≤ M s i' d)
    (n : Fin 2 → ℤ) :
    let wN := fun j s => planeCarrierTranslation (K j + 1) (AVenhance.latticeShift n) (w j s)
    (∫ x, inner ℝ
      ((planeCarrierTranslation (K i) (AVenhance.latticeShift n) (u i t)).toFunction.jet (valueIndex2 (K i)) x)
      (ψ.toFunction.jet (valueIndex2 1) x)) -
    (∫ x, inner ℝ
      ((planeCarrierTranslation (K i) (AVenhance.latticeShift n) (f i)).toFunction.jet (valueIndex2 (K i)) x)
      (ψ.toFunction.jet (valueIndex2 1) x)) =
    ∫ s in Set.Ioc a t, ∑ j : Fin 3, planeHomogeneousIntegralAtom K D ν v A wN i ψ j s := by
  dsimp only
  let wN := fun k s => planeCarrierTranslation (K k + 1) (AVenhance.latticeShift n) (w k s)
  let du := fun s k => (wN i s).toFunction.jet
    ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩
  let flux := fun s => planeRawCouplingFlux K D s A (fun k => wN k s) i
  let φ0 := ψ.toFunction.jet (valueIndex2 1)
  let dφ := fun k => ψ.toFunction.jet ⟨⟨1, by decide⟩, fun _ => k⟩
  have heq := planeHomogeneous_image_atom_equation K D ν a b v hvp A hAp f u w hs
    i t ht ψ hv hvb hc M hM hb n
  refine heq.trans (integral_congr_ae ?_)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs'
  obtain ⟨V, hV, hbV⟩ := hvb s hs'
  have hdu (k : Fin 2) : MemLp (du s k) 2 (volume.restrict Set.univ) :=
    (wN i s).toFunction.memL2 _
  have hflux (k : Fin 2) : MemLp (fun x => flux s x k) 2 (volume.restrict Set.univ) :=
    planeRawCouplingFlux_component_memLp K D s A i (hc s hs') (M s) (hM s hs')
      (hb s hs') (fun k => wN k s) k
  have hdir := homogeneous_directional_pairings_integrable s v φ0 dφ du flux (hv s hs')
    V hV hbV (ψ.toFunction.memL2 _) (fun k => ψ.toFunction.memL2 _) hdu hflux
  simp only [Measure.restrict_univ] at hdir
  apply Finset.sum_congr rfl
  intro j _
  exact homogeneousWeakRhsAtom_integral volume ν s v φ0 dφ du flux hdir.1 hdir.2.1 hdir.2.2 j

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.Analysis.Convolution
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The actual torus time readout needs coefficient bounds only on the measured window. -/

section
variable {E F X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]
  [MeasurableSpace X] {K L : ℕ}

theorem windowed_coefficient_actual_time_transfer (μ : Measure X) [IsFiniteMeasure μ]
    (S : Set X) (hS : MeasurableSet S) (hSae : ∀ᵐ t ∂μ, t ∈ S)
    (U : Set (Vec 2)) (R : ℝ) (hR : 0 < R) (hU : U ⊆ Metric.ball (0 : Vec 2) R)
    (C : X → Vec 2 → E →L[ℝ] F) (hc : ∀ t ∈ S, Continuous (C t))
    (hj : Measurable (Function.uncurry C)) (MC : ℝ) (hMC : 0 ≤ MC)
    (hC : ∀ t ∈ S, ∀ x, ‖C t x‖ ≤ MC)
    (f : X → PlaneHk Set.univ K E) (hf : MemLp f 2 μ) (z : Vec 2) (α : JetIndex2 K)
    (φ : PlaneHk Set.univ L F) (β : JetIndex2 L)
    (hφ : ∀ᵐ x ∂volume, x ∉ U → φ.toFunction.jet β x = 0)
    (M : X → ℝ) (hM : MemLp M 2 μ)
    (hw : ∀ᵐ t ∂μ, AEStronglyMeasurable
      (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet α y) volume)
    (hb : ∀ᵐ t ∂μ, eLpNorm
      (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet α y) 2 volume ≤ ENNReal.ofReal ‖M t‖)
    (T : X → TorusHk K E)
    (hr : ∀ᵐ t ∂μ, (T t).toFunction.jet α =ᵐ[volume] periodizeRawJet (f t).toFunction.jet α) :
    Integrable (fun t => ∫ x, inner ℝ (C t x ((T t).toFunction.jet α x))
      (φ.toFunction.jet β x)) μ ∧
    (∑' n : Fin 2 → ℤ, ∫ t, (∫ x, inner ℝ
      (C t x ((planeCarrierTranslation K (AVenhance.latticeShift n) (f t)).toFunction.jet α x))
      (φ.toFunction.jet β x)) ∂μ) =
      ∫ t, (∫ x, inner ℝ (C t x ((T t).toFunction.jet α x)) (φ.toFunction.jet β x)) ∂μ := by
  let Cw := windowedPhysicalCoefficient S C
  have hcW : ∀ t, Continuous (Cw t) := windowedPhysicalCoefficient_continuous S C hc
  have hjW : Measurable (Function.uncurry Cw) :=
    windowedPhysicalCoefficient_joint_measurable S hS C hj
  have hbW : ∀ t x, ‖Cw t x‖ ≤ MC := windowedPhysicalCoefficient_norm_le S C MC hMC hC
  obtain ⟨hi, he⟩ := periodized_coefficient_actual_time_transfer μ U R hR hU
    Cw hcW hjW MC hMC hbW f hf z α φ β hφ M hM hw hb T hr
  have hactual : (fun t => ∫ x, inner ℝ (Cw t x ((T t).toFunction.jet α x))
      (φ.toFunction.jet β x)) =ᵐ[μ]
      (fun t => ∫ x, inner ℝ (C t x ((T t).toFunction.jet α x)) (φ.toFunction.jet β x)) := by
    filter_upwards [hSae] with t ht
    rw [show Cw t = C t from windowedPhysicalCoefficient_eq S C t ht]
  refine ⟨hi.congr hactual, ?_⟩
  calc
    _ = ∑' n : Fin 2 → ℤ, ∫ t, (∫ x, inner ℝ
        (Cw t x ((planeCarrierTranslation K (AVenhance.latticeShift n) (f t)).toFunction.jet α x))
        (φ.toFunction.jet β x)) ∂μ := by
      apply tsum_congr
      intro n
      apply integral_congr_ae
      filter_upwards [hSae] with t ht
      rw [show Cw t = C t from windowedPhysicalCoefficient_eq S C t ht]
    _ = ∫ t, (∫ x, inner ℝ (Cw t x ((T t).toFunction.jet α x)) (φ.toFunction.jet β x)) ∂μ := he
    _ = _ := integral_congr_ae hactual
end

/-! A scalar coefficient pairing carries its image price and actual torus time readout together. -/

section
variable {E F X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]
  [MeasurableSpace X] {K L : ℕ}

theorem windowed_scalar_actual_time_transfer (μ : Measure X) [IsFiniteMeasure μ]
    (S : Set X) (hS : MeasurableSet S) (hSae : ∀ᵐ t ∂μ, t ∈ S)
    (U : Set (Vec 2)) (R : ℝ) (hR : 0 < R) (hU : U ⊆ Metric.ball (0 : Vec 2) R)
    (C : X → Vec 2 → E →L[ℝ] F) (hc : ∀ t ∈ S, Continuous (C t))
    (hj : Measurable (Function.uncurry C)) (MC : ℝ) (hMC : 0 ≤ MC)
    (hC : ∀ t ∈ S, ∀ x, ‖C t x‖ ≤ MC)
    (f : X → PlaneHk Set.univ K E) (hf : MemLp f 2 μ) (z : Vec 2) (α : JetIndex2 K)
    (φ : PlaneHk Set.univ L F) (β : JetIndex2 L)
    (hφ : ∀ᵐ x ∂volume, x ∉ U → φ.toFunction.jet β x = 0)
    (M : X → ℝ) (hM : MemLp M 2 μ)
    (hw : ∀ᵐ t ∂μ, AEStronglyMeasurable
      (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet α y) volume)
    (hb : ∀ᵐ t ∂μ, eLpNorm
      (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet α y) 2 volume ≤ ENNReal.ofReal ‖M t‖)
    (T : X → TorusHk K E)
    (hr : ∀ᵐ t ∂μ, (T t).toFunction.jet α =ᵐ[volume] periodizeRawJet (f t).toFunction.jet α) :
    let G := fun (n : Fin 2 → ℤ) t => ∫ x, inner ℝ
      (C t x ((planeCarrierTranslation K (AVenhance.latticeShift n) (f t)).toFunction.jet α x))
      (φ.toFunction.jet β x)
    let P := fun t => ∫ x, inner ℝ (C t x ((T t).toFunction.jet α x)) (φ.toFunction.jet β x)
    (∀ n, Integrable (G n) μ) ∧ Summable (fun n => ∫ t, ‖G n t‖ ∂μ) ∧
      Integrable P μ ∧ (∑' n, ∫ t, G n t ∂μ) = ∫ t, P t ∂μ := by
  obtain ⟨hi, hs⟩ := windowed_coefficient_pairing_time_integrable_summable μ S hS hSae
    U R hR hU C hc hj MC hMC hC f hf z α φ β hφ M hM hw hb
  obtain ⟨hP, he⟩ := windowed_coefficient_actual_time_transfer μ S hS hSae
    U R hR hU C hc hj MC hMC hC f hf z α φ β hφ M hM hw hb T hr
  exact ⟨hi, hs, hP, he⟩
end

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The literal coupled word-array flux transfers through all integer images in spacetime. -/

variable {ι X : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  [MeasurableSpace X] {K L : ℕ}

theorem couplingFlux_pairing_spacetime_transfer {r : ℕ} (i i' : ι) (μ : Measure X) [IsFiniteMeasure μ]
    (U : Set (Vec 2)) (hUm : MeasurableSet U) (R : ℝ) (hR : 0 < R) (hU : U ⊆ Metric.ball (0 : Vec 2) R)
    (A : X → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 r => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i)) (hc : ∀ t, Continuous (A t))
    (hj : Measurable (Function.uncurry A)) (MC : ℝ) (hMC : 0 ≤ MC)
    (hA : ∀ t x, ‖A t x‖ ≤ MC)
    (f : X → PlaneHk Set.univ K (h i')) (hf : MemLp f 2 μ) (z : Vec 2) (α : DerivativeWord2 r → JetIndex2 K)
    (φ : PlaneHk Set.univ L (h i)) (β : JetIndex2 L) (k : Fin 2)
    (hφ : ∀ᵐ x ∂volume, x ∉ U → φ.toFunction.jet β x = 0)
    (M : X → ℝ) (hM : MemLp M 2 μ)
    (hw : ∀ j, ∀ᵐ t ∂μ, AEStronglyMeasurable
      (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet (α j) y) volume)
    (hb : ∀ j, ∀ᵐ t ∂μ, eLpNorm
      (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet (α j) y) 2 volume ≤ ENNReal.ofReal ‖M t‖) :
    (∑' n : Fin 2 → ℤ, ∫ t, (∫ x, inner ℝ
      (A t x (WithLp.toLp 2 (fun w =>
        (planeCarrierTranslation K (AVenhance.latticeShift n) (f t)).toFunction.jet (α w) x)) k)
      (φ.toFunction.jet β x)) ∂μ) =
      ∫ t, (∫ x, inner ℝ
        (A t x (WithLp.toLp 2 (fun w => periodizeRawJet (f t).toFunction.jet (α w) x)) k)
        (φ.toFunction.jet β x)) ∂μ := by
  have he := finite_coefficient_pairing_spacetime_transfer μ Finset.univ U hUm R hR hU
    (fun w t => couplingEntryCoefficient i i' (A t) w k)
    (fun w t => couplingEntryCoefficient_continuous i i' (A t) (hc t) w k)
    (fun w => couplingEntryCoefficient_joint_measurable i i' A hj w k) MC hMC
    (fun w t x => (couplingEntryCoefficient_norm_le i i' (A t) w k x).trans (hA t x))
    f hf z α φ β hφ M hM hw hb
  simp_rw [couplingEntryCoefficient_inner_expansion]
  exact he

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Total native flux readouts assemble scalar responses into the genuine coupled plane equation. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeWeakSolution_total_flux_time_ae_congr {ν a b : ℝ}
    (ρ : ℝ) (hρ : 0 < ρ)
    {v : ℝ → Vec 2 → Vec 2} {D : ℕ} {K : ι → ℕ}
    {A A' : ∀ i j, (o : admissibleOrders K D i j) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (o.1 - 1) => h j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i)}
    {f : ∀ i, PlaneHk Set.univ (K i) (h i)}
    {F F' : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i))}
    {g u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i)}
    {w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)}
    (hA : ∀ i j d, coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hA' : ∀ i j d, coefficientSeminorm ρ (K i) a b (A' i j d) ≠ ⊤)
    (hC : ∀ i j d s, s ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A i j d s))
    (hC' : ∀ i j d s, s ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A' i j d s))
    (hF : ∀ i, ∀ᵐ s ∂volume.restrict (Set.Icc a b),
      (fun z => planeRawCouplingFlux K D s A (fun j => w j s) i z +
        (F i s).toFunction.jet (valueIndex2 (K i)) z) =ᵐ[volume]
      (fun z => planeRawCouplingFlux K D s A' (fun j => w j s) i z +
        (F' i s).toFunction.jet (valueIndex2 (K i)) z))
    (hs : IsCoupledWeakSolutionPlane ν a b v D K A f F g u w) :
    IsCoupledWeakSolutionPlane ν a b v D K A' f F' g u w := by
  refine ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_⟩
  intro i t ht φ
  have hold := hs.2.2.2.2 i t ht φ
  simp only [Measure.restrict_univ] at hold ⊢
  apply coupledWeakIdentity_time_ae_total_flux_congr volume ν a t v _ _ _ _ _ _ _ _ _ _
    (fun k => planeRawJet_memLp φ ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩) _ _ _ hold
  · intro s hs k
    have hsab : s ∈ Set.Icc a b := ⟨hs.1.le, hs.2.trans ht.2⟩
    have hflux := planeRawCouplingFlux_memLp ρ hρ K D a b s hsab A hA
      (fun i j d => hC i j d s hsab) (fun j => w j s) i
    have htot := hflux.add (planeRawJet_memLp (F i s) (valueIndex2 (K i)))
    simpa only [Function.comp_def, PiLp.proj_apply, Pi.add_apply, planeRawCouplingFlux] using
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h i) k).comp_memLp' htot
  · intro s hs k
    have hsab : s ∈ Set.Icc a b := ⟨hs.1.le, hs.2.trans ht.2⟩
    have hflux := planeRawCouplingFlux_memLp ρ hρ K D a b s hsab A' hA'
      (fun i j d => hC' i j d s hsab) (fun j => w j s) i
    have htot := hflux.add (planeRawJet_memLp (F' i s) (valueIndex2 (K i)))
    simpa only [Function.comp_def, PiLp.proj_apply, Pi.add_apply, planeRawCouplingFlux] using
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h i) k).comp_memLp' htot
  · have hsub : Set.Ioc a t ⊆ Set.Icc a b :=
      fun s hmem => ⟨hmem.1.le, hmem.2.trans ht.2⟩
    exact ae_restrict_of_ae_restrict_of_subset hsub (hF i)

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The signed diffusion directions assemble with the genuine torus readout and image price. -/

section
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace X] {K L : ℕ}

theorem diffusion_actual_time_transfer (μ : Measure X) [IsFiniteMeasure μ]
    (U : Set (Vec 2)) (R : ℝ) (hR : 0 < R) (hU : U ⊆ Metric.ball (0 : Vec 2) R)
    (ν : ℝ) (f : X → PlaneHk Set.univ K E) (hf : MemLp f 2 μ) (z : Vec 2)
    (α : Fin 2 → JetIndex2 K) (φ : PlaneHk Set.univ L E) (β : Fin 2 → JetIndex2 L)
    (hφ : ∀ k, ∀ᵐ x ∂volume, x ∉ U → φ.toFunction.jet (β k) x = 0)
    (M : X → ℝ) (hM : MemLp M 2 μ)
    (hw : ∀ k, ∀ᵐ t ∂μ, AEStronglyMeasurable
      (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet (α k) y) volume)
    (hb : ∀ k, ∀ᵐ t ∂μ, eLpNorm
      (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet (α k) y) 2 volume ≤ ENNReal.ofReal ‖M t‖)
    (T : X → TorusHk K E)
    (hr : ∀ k, ∀ᵐ t ∂μ, (T t).toFunction.jet (α k) =ᵐ[volume]
      periodizeRawJet (f t).toFunction.jet (α k)) :
    let G := fun (n : Fin 2 → ℤ) t => -ν * ∑ k : Fin 2, ∫ x, inner ℝ
      ((planeCarrierTranslation K (AVenhance.latticeShift n) (f t)).toFunction.jet (α k) x)
      (φ.toFunction.jet (β k) x)
    let P := fun t => -ν * ∑ k : Fin 2, ∫ x, inner ℝ
      ((T t).toFunction.jet (α k) x) (φ.toFunction.jet (β k) x)
    (∀ n, Integrable (G n) μ) ∧ Summable (fun n => ∫ t, ‖G n t‖ ∂μ) ∧
      Integrable P μ ∧ (∑' n, ∫ t, G n t ∂μ) = ∫ t, P t ∂μ := by
  dsimp only
  let G := fun k (n : Fin 2 → ℤ) t => ∫ x, inner ℝ
    ((planeCarrierTranslation K (AVenhance.latticeShift n) (f t)).toFunction.jet (α k) x)
    (φ.toFunction.jet (β k) x)
  let P := fun k t => ∫ x, inner ℝ ((T t).toFunction.jet (α k) x) (φ.toFunction.jet (β k) x)
  have hdir (k : Fin 2) : (∀ n, Integrable (G k n) μ) ∧
      Summable (fun n => ∫ t, ‖G k n t‖ ∂μ) ∧ Integrable (P k) μ ∧
      (∑' n, ∫ t, G k n t ∂μ) = ∫ t, P k t ∂μ := by
    simpa only [ContinuousLinearMap.id_apply] using
      windowed_scalar_actual_time_transfer μ Set.univ MeasurableSet.univ
        (Filter.Eventually.of_forall (fun _ => Set.mem_univ _))
        U R hR hU (fun _ _ => ContinuousLinearMap.id ℝ E)
        (fun _ _ => continuous_const) measurable_const 1 (by norm_num)
        (fun _ _ _ => ContinuousLinearMap.norm_id_le)
        f hf z (α k) φ (β k) (hφ k) M hM (hw k) (hb k) T (hr k)
  have hsum := finite_pairing_spacetime_readout μ Finset.univ G P
    (fun k _ => (hdir k).1) (fun k _ => (hdir k).2.1)
    (fun k _ => (hdir k).2.2.1) (fun k _ => (hdir k).2.2.2)
  exact pairing_spacetime_readout_const_mul μ
    (fun n t => ∑ k, G k n t) (fun t => ∑ k, P k t)
    hsum.1 hsum.2.1 hsum.2.2.1 hsum.2.2.2 (-ν)
end

/-! The signed drift directions assemble with the genuine torus readout and image price. -/

section
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace X] {K L : ℕ}

theorem drift_actual_time_transfer (μ : Measure X) [IsFiniteMeasure μ]
    (S : Set X) (hS : MeasurableSet S) (hSae : ∀ᵐ t ∂μ, t ∈ S)
    (v : X → Vec 2 → Vec 2) (hv : ∀ t ∈ S, Continuous (v t))
    (hvm : Measurable (Function.uncurry v))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ S, ∀ x, ‖v t x‖ ≤ V)
    (U : Set (Vec 2)) (R : ℝ) (hR : 0 < R) (hU : U ⊆ Metric.ball (0 : Vec 2) R)
    (f : X → PlaneHk Set.univ K E) (hf : MemLp f 2 μ) (z : Vec 2)
    (α : Fin 2 → JetIndex2 K) (φ : PlaneHk Set.univ L E) (β : Fin 2 → JetIndex2 L)
    (hφ : ∀ k, ∀ᵐ x ∂volume, x ∉ U → φ.toFunction.jet (β k) x = 0)
    (M : X → ℝ) (hM : MemLp M 2 μ)
    (hw : ∀ k, ∀ᵐ t ∂μ, AEStronglyMeasurable
      (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet (α k) y) volume)
    (hb : ∀ k, ∀ᵐ t ∂μ, eLpNorm
      (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet (α k) y) 2 volume ≤ ENNReal.ofReal ‖M t‖)
    (T : X → TorusHk K E)
    (hr : ∀ k, ∀ᵐ t ∂μ, (T t).toFunction.jet (α k) =ᵐ[volume]
      periodizeRawJet (f t).toFunction.jet (α k)) :
    let G := fun (n : Fin 2 → ℤ) t => -(∑ k : Fin 2, ∫ x, v t x k * inner ℝ
      ((planeCarrierTranslation K (AVenhance.latticeShift n) (f t)).toFunction.jet (α k) x)
      (φ.toFunction.jet (β k) x))
    let P := fun t => -(∑ k : Fin 2, ∫ x, v t x k * inner ℝ
      ((T t).toFunction.jet (α k) x) (φ.toFunction.jet (β k) x))
    (∀ n, Integrable (G n) μ) ∧ Summable (fun n => ∫ t, ‖G n t‖ ∂μ) ∧
      Integrable P μ ∧ (∑' n, ∫ t, G n t ∂μ) = ∫ t, P t ∂μ := by
  dsimp only
  let G := fun k (n : Fin 2 → ℤ) t => ∫ x, v t x k * inner ℝ
    ((planeCarrierTranslation K (AVenhance.latticeShift n) (f t)).toFunction.jet (α k) x)
    (φ.toFunction.jet (β k) x)
  let P := fun k t => ∫ x, v t x k * inner ℝ ((T t).toFunction.jet (α k) x) (φ.toFunction.jet (β k) x)
  have hdir (k : Fin 2) : (∀ n, Integrable (G k n) μ) ∧
      Summable (fun n => ∫ t, ‖G k n t‖ ∂μ) ∧ Integrable (P k) μ ∧
      (∑' n, ∫ t, G k n t ∂μ) = ∫ t, P k t ∂μ := by
    simpa only [driftPairingCoefficient_inner] using
      windowed_scalar_actual_time_transfer μ S hS hSae U R hR hU
        (fun t x => driftPairingCoefficient (E := E) (v t x) k)
        (fun t ht => driftPairingCoefficient_continuous (v t) (hv t ht) k)
        (driftPairingCoefficient_joint_measurable v hvm k) V hV
        (fun t ht x => (driftPairingCoefficient_norm_le (E := E) (v t x) k).trans (hbv t ht x))
        f hf z (α k) φ (β k) (hφ k) M hM (hw k) (hb k) T (hr k)
  have hsum := finite_pairing_spacetime_readout μ Finset.univ G P
    (fun k _ => (hdir k).1) (fun k _ => (hdir k).2.1)
    (fun k _ => (hdir k).2.2.1) (fun k _ => (hdir k).2.2.2)
  simpa only [neg_one_mul] using pairing_spacetime_readout_const_mul μ
    (fun n t => ∑ k, G k n t) (fun t => ∑ k, P k t)
    hsum.1 hsum.2.1 hsum.2.2.1 hsum.2.2.2 (-1)
end

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleJointProofs

/-! Actual periodic torus lifts supply every localized homogeneous spatial pairing at every time. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem torusHomogeneous_directional_pairings_integrable (K : ι → ℕ) (D : ℕ) (s : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (hv : Continuous (v s)) (hvp : AVenhance.IsZ2Periodic (v s))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ x, ‖v s x‖ ≤ V)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i)) (i : ι)
    (hc : ∀ i' d, Continuous (A i i' d s))
    (M : ∀ i', admissibleOrders K D i i' → ℝ)
    (hM : ∀ i' d, 0 ≤ M i' d) (hb : ∀ i' d x, ‖A i i' d s x‖ ≤ M i' d)
    (hp : ∀ i' d, AVenhance.IsZ2Periodic (A i i' d s))
    (W : ∀ i, ℝ → TorusHk (K i + 1) (h i))
    {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (φ : TorusHk 1 (h i)) :
    let ψ := spatialPatchLocalization hζ 1 (by norm_num) 0 1 φ
    let du := fun k => (W i s).toFunction.jet
      ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩
    (∀ k, Integrable (fun x => v s x k * inner ℝ (du k x)
      (ψ.toFunction.jet (valueIndex2 1) x)) volume) ∧
    (∀ k, Integrable (fun x => inner ℝ (du k x)
      (ψ.toFunction.jet ⟨⟨1, by decide⟩, fun _ => k⟩ x)) volume) ∧
    ∀ k, Integrable (fun x => inner ℝ (torusRawCouplingFlux K D s A (fun j => W j s) i x k)
      (ψ.toFunction.jet ⟨⟨1, by decide⟩, fun _ => k⟩ x)) volume := by
  dsimp only
  let α := fun k : Fin 2 =>
    (⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩ : JetIndex2 (K i + 1))
  constructor
  · intro k
    let f := fun x => driftPairingCoefficient (E := h i) (v s x) k ((W i s).toFunction.jet (α k) x)
    have hf : MemLp f 2 (volume.restrict AVenhance.unitCube) :=
      memLp_operator_mul (driftPairingCoefficient_continuous (v s) hv k)
        (periodicJetRepresentative_memL2 (W i s).val (α k)) hV
        (fun x => (driftPairingCoefficient_norm_le (E := h i) (v s x) k).trans (hbv x))
    have hfp : AVenhance.IsZ2Periodic f := by
      intro n x
      change driftPairingCoefficient (v s (x + AVenhance.latticeShift n)) k
        ((W i s).toFunction.jet (α k) (x + AVenhance.latticeShift n)) = _
      have hjet : (W i s).toFunction.jet (α k) (x + AVenhance.latticeShift n) =
          (W i s).toFunction.jet (α k) x := periodicJetRepresentative_periodic (W i s).val (α k) n x
      rw [hvp n x, hjet]
    simpa only [f, driftPairingCoefficient_inner] using
      (periodic_unitPatch_test_pairings_integrable f hf hfp hζ φ).1
  · constructor
    · intro k
      exact (periodic_unitPatch_test_pairings_integrable ((W i s).toFunction.jet (α k))
        (periodicJetRepresentative_memL2 (W i s).val (α k))
        (periodicJetRepresentative_periodic (W i s).val (α k)) hζ φ).2 k
    · intro k
      have hfp : AVenhance.IsZ2Periodic (fun x => torusRawCouplingFlux K D s A (fun j => W j s) i x k) := by
        intro n x
        exact congrArg (fun y : PiLp 2 (fun _ : Fin 2 => h i) => y k)
          (torusRawCouplingFlux_periodic K D s A i hp (fun j => W j s) n x)
      exact (periodic_unitPatch_test_pairings_integrable _
        (torusRawCouplingFlux_component_memLp K D s A i hc M hM hb (fun j => W j s) k)
        hfp hζ φ).2 k

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! A window-bounded word-array flux transfers to the actual torus lift with its absolute image price. -/

variable {ι X : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  [MeasurableSpace X] {K L : ℕ}

theorem windowed_couplingFlux_actual_time_transfer {r : ℕ} (i i' : ι) (μ : Measure X) [IsFiniteMeasure μ]
    (S : Set X) (hS : MeasurableSet S) (hSae : ∀ᵐ t ∂μ, t ∈ S)
    (U : Set (Vec 2)) (hUm : MeasurableSet U) (R : ℝ) (hR : 0 < R) (hU : U ⊆ Metric.ball (0 : Vec 2) R)
    (A : X → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 r => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i)) (hc : ∀ t ∈ S, Continuous (A t))
    (hj : Measurable (Function.uncurry A)) (MC : ℝ) (hMC : 0 ≤ MC)
    (hA : ∀ t ∈ S, ∀ x, ‖A t x‖ ≤ MC)
    (f : X → PlaneHk Set.univ K (h i')) (hf : MemLp f 2 μ) (z : Vec 2) (α : DerivativeWord2 r → JetIndex2 K)
    (φ : PlaneHk Set.univ L (h i)) (β : JetIndex2 L) (k : Fin 2)
    (hφ : ∀ᵐ x ∂volume, x ∉ U → φ.toFunction.jet β x = 0)
    (M : X → ℝ) (hM : MemLp M 2 μ)
    (hw : ∀ j, ∀ᵐ t ∂μ, AEStronglyMeasurable
      (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet (α j) y) volume)
    (hb : ∀ j, ∀ᵐ t ∂μ, eLpNorm
      (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet (α j) y) 2 volume ≤ ENNReal.ofReal ‖M t‖)
    (T : X → TorusHk K (h i'))
    (hr : ∀ w, ∀ᵐ t ∂μ, (T t).toFunction.jet (α w) =ᵐ[volume]
      periodizeRawJet (f t).toFunction.jet (α w)) :
    let G := fun (n : Fin 2 → ℤ) t => ∫ x, inner ℝ
      (A t x (WithLp.toLp 2 (fun w =>
        (planeCarrierTranslation K (AVenhance.latticeShift n) (f t)).toFunction.jet (α w) x)) k)
      (φ.toFunction.jet β x)
    let P := fun t => ∫ x, inner ℝ
      (A t x (WithLp.toLp 2 (fun w => (T t).toFunction.jet (α w) x)) k)
      (φ.toFunction.jet β x)
    (∀ n, Integrable (G n) μ) ∧ Summable (fun n => ∫ t, ‖G n t‖ ∂μ) ∧
      Integrable P μ ∧ (∑' n, ∫ t, G n t ∂μ) = ∫ t, P t ∂μ := by
  dsimp only
  let Aw := windowedPhysicalCoefficient S A
  have hcW : ∀ t, Continuous (Aw t) := windowedPhysicalCoefficient_continuous S A hc
  have hjW : Measurable (Function.uncurry Aw) := windowedPhysicalCoefficient_joint_measurable S hS A hj
  have hbW : ∀ t x, ‖Aw t x‖ ≤ MC := windowedPhysicalCoefficient_norm_le S A MC hMC hA
  have himage (n : Fin 2 → ℤ) :
      (fun t => ∫ x, inner ℝ (A t x (WithLp.toLp 2 (fun w =>
        (planeCarrierTranslation K (AVenhance.latticeShift n) (f t)).toFunction.jet (α w) x)) k)
        (φ.toFunction.jet β x)) =ᵐ[μ]
      (fun t => ∫ x, inner ℝ (Aw t x (WithLp.toLp 2 (fun w =>
        (planeCarrierTranslation K (AVenhance.latticeShift n) (f t)).toFunction.jet (α w) x)) k)
        (φ.toFunction.jet β x)) := by
    filter_upwards [hSae] with t ht
    rw [show Aw t = A t from windowedPhysicalCoefficient_eq S A t ht]
  have hactual :
      (fun t => ∫ x, inner ℝ (Aw t x (WithLp.toLp 2 (fun w =>
        periodizeRawJet (f t).toFunction.jet (α w) x)) k) (φ.toFunction.jet β x)) =ᵐ[μ]
      (fun t => ∫ x, inner ℝ (A t x (WithLp.toLp 2 (fun w =>
        (T t).toFunction.jet (α w) x)) k) (φ.toFunction.jet β x)) := by
    filter_upwards [hSae, ae_all_iff.mpr hr] with t ht hrt
    rw [show Aw t = A t from windowedPhysicalCoefficient_eq S A t ht]
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hrt] with x hx
    have he : (WithLp.toLp 2 (fun w => periodizeRawJet (f t).toFunction.jet (α w) x)) =
        WithLp.toLp 2 (fun w => (T t).toFunction.jet (α w) x) := by
      apply PiLp.ext
      intro w
      exact (hx w).symm
    rw [he]
  obtain ⟨hi, hs⟩ := couplingFlux_pairing_time_integrable_summable i i' μ U R hR hU
    Aw hcW hjW MC hMC hbW f hf z α φ β k hφ M hM hw hb
  refine ⟨fun n => (hi n).congr (himage n).symm, ?_, ?_, ?_⟩
  · exact hs.congr (fun n => integral_congr_ae
      ((himage n).symm.mono (fun _ hx => congrArg norm hx)))
  · exact (periodized_couplingFlux_pairing_time_integrable i i' μ U hUm R hR hU
      Aw hcW hjW MC hMC hbW f hf z α φ β k hφ M hM hw hb).congr hactual
  · calc
      _ = ∑' n : Fin 2 → ℤ, ∫ t, (∫ x, inner ℝ
          (Aw t x (WithLp.toLp 2 (fun w =>
            (planeCarrierTranslation K (AVenhance.latticeShift n) (f t)).toFunction.jet (α w) x)) k)
          (φ.toFunction.jet β x)) ∂μ := tsum_congr (fun n => integral_congr_ae (himage n))
      _ = ∫ t, (∫ x, inner ℝ
          (Aw t x (WithLp.toLp 2 (fun w => periodizeRawJet (f t).toFunction.jet (α w) x)) k)
          (φ.toFunction.jet β x)) ∂μ :=
        couplingFlux_pairing_spacetime_transfer i i' μ U hUm R hR hU
          Aw hcW hjW MC hMC hbW f hf z α φ β k hφ M hM hw hb
      _ = _ := integral_congr_ae hactual

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance MeasureTheory AVRegularity.Weighted AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! Native coupling fluxes have a genuine bounded inverse-Jacobian material pullback. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

def planeFluxChartPull {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (t s : ℝ) : PlaneFluxL2 E →L[ℝ] PlaneFluxL2 E :=
  let hB := streamFlow_jacMatrix_bounded hφ t s
  let C := hB.choose
  let hc : ∀ k j : Fin 2, Continuous (fun y : Vec 2 => (chartJac hφ s t y)⁻¹ k j) :=
    chartJac_inverse_entry_continuous_slice hφ s t
  let hb := fun k j y => unitDet_inverse_entry_bound (chartJac hφ s t y)
    (streamFlow_jacMatrix_det_one hφ t s y) C (hB.choose_spec.2 y) k j
  (planeScalarDiffusion (fun y => (chartJac hφ s t y)⁻¹) hc hB.choose_spec.1 hb).comp
    (planeFluxFlowPull hφ t s)

theorem planeFluxChartPull_ae {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (t s : ℝ) (F : PlaneFluxL2 E) (k : Fin 2) :
    (planeFluxChartPull hφ t s F k : Vec 2 → E) =ᵐ[volume]
      fun y => ∑ j : Fin 2, (chartJac hφ s t y)⁻¹ k j • F j (AVRegularity.streamFlow φ hφ t y s) := by
  have hc : ∀ i j : Fin 2, Continuous (fun y : Vec 2 => (chartJac hφ s t y)⁻¹ i j) :=
    chartJac_inverse_entry_continuous_slice hφ s t
  have hd := planeScalarDiffusion_ae (E := E)
    (fun y => (chartJac hφ s t y)⁻¹)
    hc
    (streamFlow_jacMatrix_bounded hφ t s).choose_spec.1
    (fun i j y => unitDet_inverse_entry_bound (chartJac hφ s t y)
      (streamFlow_jacMatrix_det_one hφ t s y)
      (streamFlow_jacMatrix_bounded hφ t s).choose
      ((streamFlow_jacMatrix_bounded hφ t s).choose_spec.2 y) i j)
    (planeFluxFlowPull hφ t s F) k
  have hf := ae_all_iff.mpr (fun j => planeFluxFlowPull_ae hφ t s F j)
  unfold planeFluxChartPull
  filter_upwards [hd, hf] with y hdy hfy
  apply hdy.trans
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun z : E => (chartJac hφ s t y)⁻¹ k j • z) (hfy j)

end AVRegularity.CycleJointProofs
end
