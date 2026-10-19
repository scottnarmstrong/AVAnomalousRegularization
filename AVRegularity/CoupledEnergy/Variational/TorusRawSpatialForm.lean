-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CoupledEnergy.Variational.TorusCoefficientCarrierMeasurable
public import AVRegularity.CoupledEnergy.Variational.TorusCoupledFluxValue
import AVRegularity.CoupledEnergy.Galerkin.PlainFamilyMeasurableFromRows
import AVRegularity.CoupledEnergy.Variational.WeightedJetMap
import AVRegularity.CoupledEnergy.Variational.PullbackForm
import Mathlib.CategoryTheory.Countable

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
namespace AVRegularity.CoupledEnergy.Variational

/-! Native velocity-gradient transport converges against the projected value
test, with the original joint measurability and uniform velocity bound. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Each actual coordinate of the drift passes through the common weak limit. -/
theorem torusDrift_projected_test_weak_limit (K : ι → ℕ) {a b s t : ℝ}
    (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t) (i : ι) (k : Fin 2)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hc : ∀ r ∈ Set.Icc a b, Continuous (v r))
    (B : ℝ) (hb : ∀ r ∈ Set.Icc a b, ∀ x, ‖v r x‖ ≤ B)
    (U : ℕ → CoupledHighTime (h := h) K a b) (V : CoupledHighTime (h := h) K a b)
    (Q : ℝ) (hu : ∀ n, ‖U n‖ ≤ Q)
    (hw : ∀ ell : CoupledHighTime (h := h) K a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (U n)) atTop (𝓝 (ell V)))
    (N : ℕ → ℕ) (hN : StrictMono N) (φ : TorusHk 1 (h i)) :
    Tendsto (fun n => ∫ r in s..t, ∫ x in AVenhance.unitCube, v r x k *
      inner ℝ (coupledHighJetCLM K i ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩,
        fun _ => k⟩ (U n r) x) (Galerkin.torusHkValueCLM (Galerkin.galerkinProj (N n) φ) x)) atTop
      (𝓝 (∫ r in s..t, ∫ x in AVenhance.unitCube, v r x k *
        inner ℝ (coupledHighJetCLM K i ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩,
          fun _ => k⟩ (V r) x) (Galerkin.torusHkValueCLM φ x))) := by
  let C := fun r x => (v r x k) • ContinuousLinearMap.id ℝ (h i)
  have hC : Measurable (fun p : Set.Icc a b × Vec 2 => C p.1 p.2) :=
    ((measurable_pi_apply k).comp hv).smul measurable_const
  have hCc (r : ℝ) (hr : r ∈ Set.Icc a b) : Continuous (C r) :=
    ((continuous_apply k).comp (hc r hr)).smul continuous_const
  have hB : 0 ≤ B := (norm_nonneg (v s 0)).trans (hb s hs 0)
  have hCb (r : ℝ) (hr : r ∈ Set.Icc a b) (x : Vec 2) : ‖C r x‖ ≤ B := by
    change ‖(v r x k) • ContinuousLinearMap.id ℝ (h i)‖ ≤ B
    rw [norm_smul]
    calc
      ‖v r x k‖ * ‖ContinuousLinearMap.id ℝ (h i)‖ ≤ ‖v r x k‖ * 1 :=
        mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
      _ = ‖v r x k‖ := mul_one _
      _ ≤ ‖v r x‖ := norm_le_pi_norm (v r x) k
      _ ≤ B := hb r hr x
  have hz := (Galerkin.torusHkValueCLM (E := h i) (K := 1)).continuous.continuousAt.tendsto.comp
    ((Galerkin.galerkinProj_tendsto φ).comp hN.tendsto_atTop)
  have hlim := coupledHighCoefficient_moving_test_weak_limit K hs ht hst U V Q hu hw
    (coupledHighJetCLM K i ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩)
    C hC hCc B hB hCb
    (fun n => Galerkin.torusHkValueCLM (Galerkin.galerkinProj (N n) φ))
    (Galerkin.torusHkValueCLM φ) hz
  simpa only [C, smul_apply, ContinuousLinearMap.id_apply,
    real_inner_smul_left] using hlim

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Variational

/-! The transport of a genuine weak periodic Sobolev field. The scalar
velocity derivative budget is transferred to the fiber coefficient by the
already compiled tensor operator estimate. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- Literal weak transport, formed with the existing weak-jet multiplication carrier. -/
def torusTransportCarrier {K : ℕ} (v : Vec 2 → Vec 2)
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (hp : AVenhance.IsZ2Periodic v)
    (C : Fin (K + 1) → ℝ)
    (hb : ∀ l x, ‖coefficientDerivativeArray (driftCoefficient v) l.val x‖ ≤ C l)
    (w : TorusHk (K + 1) E) : TorusHk K E :=
  (torusGradientTensor w).mulCoefficient (driftFiberCoefficient v)
    ((driftFiberCoefficient_contDiff v hv).of_le (by simp))
    (by intro n x; unfold driftFiberCoefficient driftCoefficient; rw [hp n x])
    (fun l x => (driftFiberCoefficient_array_norm_le v hv l.val x).trans (hb l x))

/-- The weak transport has the expected velocity-gradient value representative. -/
theorem torusTransportCarrier_value_ae {K : ℕ} (v : Vec 2 → Vec 2)
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (hp : AVenhance.IsZ2Periodic v)
    (C : Fin (K + 1) → ℝ)
    (hb : ∀ l x, ‖coefficientDerivativeArray (driftCoefficient v) l.val x‖ ≤ C l)
    (w : TorusHk (K + 1) E) :
    (torusTransportCarrier v hv hp C hb w).val (valueIndex2 K) =ᵐ[
      volume.restrict AVenhance.unitCube] fun x => ∑ k : Fin 2,
        v x k • (w.val ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos K)⟩, fun _ => k⟩ x) := by
  have hm := torusMulCoefficient_value_ae (torusGradientTensor w) (driftFiberCoefficient v)
    ((driftFiberCoefficient_contDiff v hv).of_le (by simp))
    (by intro n x; unfold driftFiberCoefficient driftCoefficient; rw [hp n x])
    (fun l x => (driftFiberCoefficient_array_norm_le v hv l.val x).trans (hb l x))
  have hg := torusFamilyTensor_value_ae (fun k : Fin 2 => derivativeTorusHk (fun _ : Fin 1 => k) w)
  simp only [Galerkin.derivativeTorusHk_value_slot] at hg
  filter_upwards [hm, hg] with x hx hgrad
  change (torusTransportCarrier v hv hp C hb w).val (valueIndex2 K) x = _
  change (torusGradientTensor w).val (valueIndex2 K) x = _ at hgrad
  unfold torusTransportCarrier
  rw [hx, hgrad, driftFiberCoefficient_apply]
end

/-! Ordinary Sobolev norm bounds for the literal weak transport. These
bounds give genuine L² time membership once Fourier-row measurability has
been proved from the original value-level coefficient assumptions. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem torusTransportCarrier_factorialRoot_le {K : ℕ} (ρ : ℝ) (hρ : 0 ≤ ρ)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (hp : AVenhance.IsZ2Periodic v)
    (C : Fin (K + 1) → ℝ)
    (hb : ∀ l x, ‖coefficientDerivativeArray (driftCoefficient v) l.val x‖ ≤ C l)
    (w : TorusHk (K + 1) E) :
    Real.sqrt (factorialNormSq ρ (torusTransportCarrier v hv hp C hb w).val) ≤
      (∑ l : Fin (K + 1), factorialRootWeight ρ l.val * C l) *
        Real.sqrt (gradFactorialNormSq ρ w.val) := by
  have hm := (torusGradientTensor w).mulCoefficient_factorialNorm_le
    ((driftFiberCoefficient_contDiff v hv).of_le (by simp))
    (by intro n x; unfold driftFiberCoefficient driftCoefficient; rw [hp n x])
    (fun l x => (driftFiberCoefficient_array_norm_le v hv l.val x).trans (hb l x)) hρ
  simpa only [torusTransportCarrier, torusGradientTensor_factorialNormSq] using hm

theorem torusTransportCarrier_norm_le {K : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (hp : AVenhance.IsZ2Periodic v)
    (C : Fin (K + 1) → ℝ)
    (hb : ∀ l x, ‖coefficientDerivativeArray (driftCoefficient v) l.val x‖ ≤ C l)
    (w : TorusHk (K + 1) E) :
    ‖torusTransportCarrier v hv hp C hb w‖ ≤
      ((∑ l : Fin (K + 1), factorialRootWeight ρ l.val * C l) *
        Real.sqrt (factorialWeightMax ρ K) / Real.sqrt (factorialWeightMin ρ K)) * ‖w‖ := by
  let L : ℝ := ∑ l : Fin (K + 1), factorialRootWeight ρ l.val * C l
  have hL : 0 ≤ L := by
    apply Finset.sum_nonneg
    intro l _
    have hc : 0 ≤ C l := (norm_nonneg _).trans (hb l 0)
    have hr : 0 ≤ factorialRootWeight ρ l.val := by unfold factorialRootWeight; positivity
    exact mul_nonneg hr hc
  have hn := jetNorm_le_factorialRoot ρ hρ (torusTransportCarrier v hv hp C hb w).val
  have ht := torusTransportCarrier_factorialRoot_le ρ hρ.le v hv hp C hb w
  have hg := gradFactorialRoot_le_jetNorm ρ w.val
  calc
    _ ≤ Real.sqrt (factorialNormSq ρ (torusTransportCarrier v hv hp C hb w).val) /
        Real.sqrt (factorialWeightMin ρ K) := hn
    _ ≤ (L * Real.sqrt (gradFactorialNormSq ρ w.val)) / Real.sqrt (factorialWeightMin ρ K) :=
      div_le_div_of_nonneg_right ht (Real.sqrt_nonneg _)
    _ ≤ (L * (Real.sqrt (factorialWeightMax ρ K) * ‖w.val‖)) /
        Real.sqrt (factorialWeightMin ρ K) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hg hL) (Real.sqrt_nonneg _)
    _ = _ := by change _ = (L * _ / _) * ‖w.val‖; ring
end

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
namespace AVRegularity.CoupledEnergy.Variational

/-! Native admissible coupling terms pass through the actual ambient weak
limit using only the original interval coefficient hypotheses. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [Fintype ι] in
/-- Every admissible derivative tensor is present in the higher-order ambient jet. -/
theorem admissibleOrders_high_readout_bound (K : ι → ℕ) (D : ℕ)
    (i i' : ι) (d : admissibleOrders K D i i') : d.1 - 1 ≤ K i' + 1 := by
  have hr := admissibleOrders_reserve K D i i' d
  omega

/-- One actual higher-order coupling coefficient converges against the projected H¹ gradient test. -/
theorem torusCoupling_projected_test_weak_limit (K : ι → ℕ) (D : ℕ) {a b s t : ℝ}
    (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t)
    (ρ : ℝ) (hρ : 0 < ρ) (i i' : ι) (d : admissibleOrders K D i i')
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : coefficientSeminorm ρ (K i) a b A ≠ ⊤)
    (hm : Measurable (fun p : Set.Icc a b × Vec 2 => A p.1 p.2))
    (hc : ∀ r ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A r))
    (U : ℕ → CoupledHighTime (h := h) K a b) (V : CoupledHighTime (h := h) K a b)
    (Q : ℝ) (hu : ∀ n, ‖U n‖ ≤ Q)
    (hw : ∀ ell : CoupledHighTime (h := h) K a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (U n)) atTop (𝓝 (ell V)))
    (N : ℕ → ℕ) (hN : StrictMono N) (φ : TorusHk 1 (h i)) :
    Tendsto (fun n => ∫ r in s..t, ∫ x in AVenhance.unitCube,
      inner ℝ (A r x (coupledHighTensorCLM (h := h) K i' (d.1 - 1)
        (admissibleOrders_high_readout_bound K D i i' d) (U n r) x))
        (torusH1GradientL2CLM (E := h i) (Galerkin.galerkinProj (N n) φ) x)) atTop
      (𝓝 (∫ r in s..t, ∫ x in AVenhance.unitCube,
        inner ℝ (A r x (coupledHighTensorCLM (h := h) K i' (d.1 - 1)
          (admissibleOrders_high_readout_bound K D i i' d) (V r) x))
          (torusH1GradientL2CLM (E := h i) φ x))) := by
  apply coupledHighCoefficient_moving_test_weak_limit K hs ht hst U V Q hu hw
    (coupledHighTensorCLM (h := h) K i' (d.1 - 1)
      (admissibleOrders_high_readout_bound K D i i' d)) A hm
    (fun r hr => (hc r hr).continuous) (coefficientSeminorm ρ (K i) a b A).toReal
    ENNReal.toReal_nonneg
    (fun r hr x => Galerkin.plainCoefficient_norm_le_seminorm ρ hρ (K i) a b A hA r hr x)
  exact (torusH1Gradient_projected_tendsto φ).comp hN.tendsto_atTop

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CoupledEnergy.Variational

/-! The native transport and coupling carriers commute with subtraction.
These identities identify the Fourier projection residual as actual forcing. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem torusTransportCarrier_sub {K : ℕ} (v : Vec 2 → Vec 2)
    (hv : ContDiff ℝ (↑(⊤ : ℕ∞)) v) (hp : AVenhance.IsZ2Periodic v)
    (C : Fin (K + 1) → ℝ)
    (hb : ∀ l x, ‖coefficientDerivativeArray (driftCoefficient v) l.val x‖ ≤ C l)
    (w z : TorusHk (K + 1) E) :
    torusTransportCarrier v hv hp C hb (w - z) =
      torusTransportCarrier v hv hp C hb w - torusTransportCarrier v hv hp C hb z := by
  unfold torusTransportCarrier
  rw [torusGradientTensor_sub, torusMulCoefficient_sub]

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem torusCoupledFluxTerm_sub (ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ)
    (a b : ℝ) (i i' : ι) (d : admissibleOrders K D i i')
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : coefficientSeminorm ρ (K i) a b A ≠ ⊤)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (hC : ContDiff ℝ (K i : ℕ) (A t))
    (hp : AVenhance.IsZ2Periodic (A t)) (w z : TorusHk (K i' + 1) (h i')) :
    torusCoupledFluxTerm ρ hρ K D a b i i' d A hA t ht hC hp (w - z) =
      torusCoupledFluxTerm ρ hρ K D a b i i' d A hA t ht hC hp w -
        torusCoupledFluxTerm ρ hρ K D a b i i' d A hA t ht hC hp z := by
  unfold torusCoupledFluxTerm torusMultiplyIntervalCoefficient
  rw [torusPositiveDerivativeTensor_sub, torusMulCoefficient_sub]

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Variational

/-! Each literal admissible integrated coupling commutes with subtraction. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem torusCoupling_integral_sub (K : ι → ℕ) (D : ℕ) {a b s t : ℝ}
    (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t)
    (ρ : ℝ) (hρ : 0 < ρ) (i i' : ι) (d : admissibleOrders K D i i')
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : coefficientSeminorm ρ (K i) a b A ≠ ⊤)
    (hm : Measurable (fun p : Set.Icc a b × Vec 2 => A p.1 p.2))
    (hc : ∀ r ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A r))
    (U V : CoupledHighTime (h := h) K a b) (φ : TorusHk 1 (h i)) :
    (∫ r in s..t, ∫ x in AVenhance.unitCube,
      inner ℝ (A r x (coupledHighTensorCLM (h := h) K i' (d.1 - 1)
        (admissibleOrders_high_readout_bound K D i i' d) ((U - V) r) x))
        (torusH1GradientL2CLM (E := h i) φ x)) =
      (∫ r in s..t, ∫ x in AVenhance.unitCube,
        inner ℝ (A r x (coupledHighTensorCLM (h := h) K i' (d.1 - 1)
          (admissibleOrders_high_readout_bound K D i i' d) (U r) x))
          (torusH1GradientL2CLM (E := h i) φ x)) -
      (∫ r in s..t, ∫ x in AVenhance.unitCube,
        inner ℝ (A r x (coupledHighTensorCLM (h := h) K i' (d.1 - 1)
          (admissibleOrders_high_readout_bound K D i i' d) (V r) x))
          (torusH1GradientL2CLM (E := h i) φ x)) := by
  exact coupledHighCoefficient_integral_sub K hs ht hst
    (coupledHighTensorCLM (h := h) K i' (d.1 - 1) (admissibleOrders_high_readout_bound K D i i' d))
    A hm (fun r hr => (hc r hr).continuous) (coefficientSeminorm ρ (K i) a b A).toReal
    ENNReal.toReal_nonneg
    (fun r hr x => Galerkin.plainCoefficient_norm_le_seminorm ρ hρ (K i) a b A hA r hr x)
    U V (torusH1GradientL2CLM (E := h i) φ)
end

/-! Each literal diffusion, drift and admissible coupling pairing is L¹
in time under the original coefficient and Sobolev hypotheses. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem torusDiffusion_test_integrable (K : ι → ℕ) {a b : ℝ} (hab : a ≤ b)
    (U : CoupledHighTime (h := h) K a b) (i : ι) (φ : TorusHk 1 (h i)) :
    Integrable (fun r => ∫ x in AVenhance.unitCube,
      inner ℝ (coupledHighGradientCLM (h := h) K i (U r) x) (torusH1GradientL2CLM (E := h i) φ x))
      (volume.restrict (Set.Icc a b)) := by
  have hi := coupledHighCoefficient_pairing_integrable K hab U (coupledHighGradientCLM (h := h) K i)
    (fun _ _ => ContinuousLinearMap.id ℝ (PiLp 2 (fun _ : Fin 2 => h i))) measurable_const
    (fun _ _ => continuous_const) 1 (by norm_num) (fun _ _ _ => ContinuousLinearMap.norm_id_le)
    (fun _ => torusH1GradientL2CLM (E := h i) φ) (memLp_const _)
  simpa only [ContinuousLinearMap.id_apply] using hi

theorem torusCoupling_test_integrable (K : ι → ℕ) (D : ℕ) {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ) (i i' : ι) (d : admissibleOrders K D i i')
    (A : ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i))
    (hA : coefficientSeminorm ρ (K i) a b A ≠ ⊤)
    (hm : Measurable (fun p : Set.Icc a b × Vec 2 => A p.1 p.2))
    (hc : ∀ r ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A r))
    (U : CoupledHighTime (h := h) K a b) (φ : TorusHk 1 (h i)) :
    Integrable (fun r => ∫ x in AVenhance.unitCube,
      inner ℝ (A r x (coupledHighTensorCLM (h := h) K i' (d.1 - 1)
        (admissibleOrders_high_readout_bound K D i i' d) (U r) x)) (torusH1GradientL2CLM (E := h i) φ x))
      (volume.restrict (Set.Icc a b)) := by
  exact coupledHighCoefficient_pairing_integrable K hab U
    (coupledHighTensorCLM (h := h) K i' (d.1 - 1) (admissibleOrders_high_readout_bound K D i i' d))
    A hm (fun r hr => (hc r hr).continuous) (coefficientSeminorm ρ (K i) a b A).toReal
    ENNReal.toReal_nonneg
    (fun r hr x => Galerkin.plainCoefficient_norm_le_seminorm ρ hρ (K i) a b A hA r hr x)
    (fun _ => torusH1GradientL2CLM (E := h i) φ) (memLp_const _)

theorem torusDrift_test_integrable (K : ι → ℕ) {a b : ℝ} (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hc : ∀ r ∈ Set.Icc a b, Continuous (v r))
    (B : ℝ) (hb : ∀ r ∈ Set.Icc a b, ∀ x, ‖v r x‖ ≤ B)
    (U : CoupledHighTime (h := h) K a b) (i : ι) (k : Fin 2) (φ : TorusHk 1 (h i)) :
    Integrable (fun r => ∫ x in AVenhance.unitCube, v r x k *
      inner ℝ (coupledHighJetCLM K i ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩,
        fun _ => k⟩ (U r) x) (Galerkin.torusHkValueCLM φ x)) (volume.restrict (Set.Icc a b)) := by
  let C := fun r x => (v r x k) • ContinuousLinearMap.id ℝ (h i)
  have hC : Measurable (fun p : Set.Icc a b × Vec 2 => C p.1 p.2) :=
    ((measurable_pi_apply k).comp hv).smul measurable_const
  have hCc (r : ℝ) (hr : r ∈ Set.Icc a b) : Continuous (C r) :=
    ((continuous_apply k).comp (hc r hr)).smul continuous_const
  have hB : 0 ≤ B := (norm_nonneg (v a 0)).trans (hb a ⟨le_rfl, hab⟩ 0)
  have hCb (r : ℝ) (hr : r ∈ Set.Icc a b) (x : Vec 2) : ‖C r x‖ ≤ B := by
    change ‖(v r x k) • ContinuousLinearMap.id ℝ (h i)‖ ≤ B
    rw [norm_smul]
    calc
      ‖v r x k‖ * ‖ContinuousLinearMap.id ℝ (h i)‖ ≤ ‖v r x k‖ * 1 :=
        mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg _)
      _ = ‖v r x k‖ := mul_one _
      _ ≤ ‖v r x‖ := norm_le_pi_norm (v r x) k
      _ ≤ B := hb r hr x
  have hi := coupledHighCoefficient_pairing_integrable K hab U
    (coupledHighJetCLM K i ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩)
    C hC hCc B hB hCb (fun _ => Galerkin.torusHkValueCLM φ) (memLp_const _)
  simpa only [C, smul_apply, ContinuousLinearMap.id_apply, real_inner_smul_left] using hi
end

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
namespace AVRegularity.CoupledEnergy.Variational

/-! Assemble all native terms in the integrated component equation. The
source remains L¹ in time; no extra coefficient regularity is introduced. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The sum of the literal integrated terms of one coupled equation. -/
def coupledIntegratedRhs (K : ι → ℕ) (D : ℕ) (ν a t : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (U : ℝ → CoupledHighHilbert (h := h) K) (i : ι) (φ : TorusHk 1 (h i)) : ℝ :=
  -ν * (∫ r in a..t, ∫ x in AVenhance.unitCube,
    inner ℝ (coupledHighGradientCLM (h := h) K i (U r) x) (torusH1GradientL2CLM (E := h i) φ x))
  - (∑ k : Fin 2, ∫ r in a..t, ∫ x in AVenhance.unitCube, v r x k *
    inner ℝ (coupledHighJetCLM K i ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩,
      fun _ => k⟩ (U r) x) (Galerkin.torusHkValueCLM φ x))
  - (∑ i', ∑ d : admissibleOrders K D i i', ∫ r in a..t, ∫ x in AVenhance.unitCube,
    inner ℝ (A i i' d r x (coupledHighTensorCLM (h := h) K i' (d.1 - 1)
      (admissibleOrders_high_readout_bound K D i i' d) (U r) x)) (torusH1GradientL2CLM (E := h i) φ x))
  - (∫ r in a..t, ∫ x in AVenhance.unitCube,
    inner ℝ (Galerkin.torusHkValueCLM (F i r) x) (torusH1GradientL2CLM (E := h i) φ x))
  + (∫ r in a..t, ∫ x in AVenhance.unitCube,
    inner ℝ (Galerkin.torusHkValueCLM (g i r) x) (Galerkin.torusHkValueCLM φ x))

/-- Every term in the projected component right-hand side passes to the common weak limit. -/
theorem coupledIntegratedRhs_projected_weak_limit (K : ι → ℕ) (D : ℕ) (ν ρ : ℝ)
    (hρ : 0 < ρ) {a b t : ℝ} (hab : a ≤ b) (ht : t ∈ Set.Icc a b)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hvc : ∀ r ∈ Set.Icc a b, Continuous (v r))
    (B : ℝ) (hvb : ∀ r ∈ Set.Icc a b, ∀ x, ‖v r x‖ ≤ B)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hAm : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (hAc : ∀ r ∈ Set.Icc a b, ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d r))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (U : ℕ → CoupledHighTime (h := h) K a b) (V : CoupledHighTime (h := h) K a b)
    (Q : ℝ) (hu : ∀ n, ‖U n‖ ≤ Q)
    (hw : ∀ ell : CoupledHighTime (h := h) K a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (U n)) atTop (𝓝 (ell V)))
    (N : ℕ → ℕ) (hN : StrictMono N) (i : ι) (φ : TorusHk 1 (h i)) :
    Tendsto (fun n => coupledIntegratedRhs K D ν a t v A F g (U n) i (Galerkin.galerkinProj (N n) φ))
      atTop (𝓝 (coupledIntegratedRhs K D ν a t v A F g V i φ)) := by
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hd := torusDiffusion_projected_test_weak_limit K ha ht ht.1 i U V Q hu hw N hN φ
  have hvlim := tendsto_finsetSum Finset.univ (fun k _ =>
    torusDrift_projected_test_weak_limit K ha ht ht.1 i k v hv hvc B hvb U V Q hu hw N hN φ)
  have hAlim := tendsto_finsetSum Finset.univ (fun i' _ =>
    tendsto_finsetSum Finset.univ (fun d _ => torusCoupling_projected_test_weak_limit K D ha ht ht.1
      ρ hρ i i' d (A i i' d) (hA i i' d) (hAm i i' d) (fun r hr => hAc r hr i i' d)
      U V Q hu hw N hN φ))
  have hFlim := (Galerkin.fluxForcing_projected_test_tendsto hab ht (F i) (hF i) φ).comp hN.tendsto_atTop
  have hglim := (Galerkin.valueForcing_projected_test_tendsto hab ht (g i) (hg i) φ).comp hN.tendsto_atTop
  exact (((hd.const_mul (-ν)).sub hvlim).sub hAlim).sub hFlim |>.add hglim
end

/-! Assemble all native terms in the integrated component equation. The
source remains L¹ in time; no extra coefficient regularity is introduced. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem coupledIntegratedRhs_zero (K : ι → ℕ) (D : ℕ) (ν a t : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (U : ℝ → CoupledHighHilbert (h := h) K) (i : ι) :
    coupledIntegratedRhs K D ν a t v A F g U i 0 = 0 := by
  simp only [coupledIntegratedRhs, map_zero, integral_inner_zeroLp, integral_mul_inner_zeroLp, mul_zero, intervalIntegral.integral_zero,
    Finset.sum_const_zero, sub_zero, add_zero]
end

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Variational

/-! Subtracting two native coupled equations with the same forcing gives
the homogeneous native equation, with no new analytic assumptions. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem coupledIntegratedRhs_sub_same_forcing (K : ι → ℕ) (D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ)
    {a b t : ℝ} (hab : a ≤ b) (ht : t ∈ Set.Icc a b) (v : ℝ → Vec 2 → Vec 2)
    (hv : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hvc : ∀ r ∈ Set.Icc a b, Continuous (v r))
    (B : ℝ) (hvb : ∀ r ∈ Set.Icc a b, ∀ x, ‖v r x‖ ≤ B)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hAm : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (hAc : ∀ r ∈ Set.Icc a b, ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d r))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (U V : CoupledHighTime (h := h) K a b) (i : ι) (φ : TorusHk 1 (h i)) :
    coupledIntegratedRhs K D ν a t v A (fun _ _ => 0) (fun _ _ => 0) (U - V : CoupledHighTime (h := h) K a b) i φ =
      coupledIntegratedRhs K D ν a t v A F g U i φ -
        coupledIntegratedRhs K D ν a t v A F g V i φ := by
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hd := torusDiffusion_integral_sub K ha ht ht.1 i U V φ
  have hvs (k : Fin 2) := torusDrift_integral_sub K ha ht ht.1 v hv hvc B hvb i k U V φ
  have hAs (i' : ι) (d : admissibleOrders K D i i') := torusCoupling_integral_sub K D ha ht ht.1
    ρ hρ i i' d (A i i' d) (hA i i' d) (hAm i i' d) (fun r hr => hAc r hr i i' d) U V φ
  have hFz : (∫ x in AVenhance.unitCube,
      inner ℝ (Galerkin.torusHkValueCLM (0 : TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i))) x)
        (torusH1GradientL2CLM (E := h i) φ x)) = 0 := by
    rw [← L2.inner_def]
    simp only [map_zero, inner_zero_left]
  have hgz : (∫ x in AVenhance.unitCube,
      inner ℝ (Galerkin.torusHkValueCLM (0 : TorusHk (K i) (h i)) x)
        (Galerkin.torusHkValueCLM φ x)) = 0 := by
    rw [← L2.inner_def]
    simp only [map_zero, inner_zero_left]
  unfold coupledIntegratedRhs
  rw [hd]
  simp_rw [hvs, hAs, Finset.sum_sub_distrib]
  simp only [hFz, hgz, intervalIntegral.integral_zero]
  ring

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
namespace AVRegularity.CoupledEnergy.Variational

/-! Assemble all native terms in the integrated component equation. The
source remains L¹ in time; no extra coefficient regularity is introduced. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The sum of the literal integrated terms of one coupled equation. -/
def coupledTimeRhs (K : ι → ℕ) (D : ℕ) (ν r : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (U : CoupledHighHilbert (h := h) K) (i : ι) (φ : TorusHk 1 (h i)) : ℝ :=
  -ν * (∫ x in AVenhance.unitCube,
    inner ℝ (coupledHighGradientCLM (h := h) K i U x) (torusH1GradientL2CLM (E := h i) φ x))
  - (∑ k : Fin 2, ∫ x in AVenhance.unitCube, v r x k *
    inner ℝ (coupledHighJetCLM K i ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩,
      fun _ => k⟩ U x) (Galerkin.torusHkValueCLM φ x))
  - (∑ i', ∑ d : admissibleOrders K D i i', ∫ x in AVenhance.unitCube,
    inner ℝ (A i i' d r x (coupledHighTensorCLM (h := h) K i' (d.1 - 1)
      (admissibleOrders_high_readout_bound K D i i' d) U x)) (torusH1GradientL2CLM (E := h i) φ x))
  - (∫ x in AVenhance.unitCube,
    inner ℝ (Galerkin.torusHkValueCLM (F i r) x) (torusH1GradientL2CLM (E := h i) φ x))
  + (∫ x in AVenhance.unitCube,
    inner ℝ (Galerkin.torusHkValueCLM (g i r) x) (Galerkin.torusHkValueCLM φ x))

/-- The actual full coupled component RHS is integrable in time. -/
theorem coupledTimeRhs_integrable (K : ι → ℕ) (D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ)
    {a b : ℝ} (hab : a ≤ b) (v : ℝ → Vec 2 → Vec 2)
    (hv : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hvc : ∀ r ∈ Set.Icc a b, Continuous (v r))
    (B : ℝ) (hvb : ∀ r ∈ Set.Icc a b, ∀ x, ‖v r x‖ ≤ B)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hAm : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (hAc : ∀ r ∈ Set.Icc a b, ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d r))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (U : CoupledHighTime (h := h) K a b) (i : ι) (φ : TorusHk 1 (h i)) :
    Integrable (fun r => coupledTimeRhs K D ν r v A F g (U r) i φ)
      (volume.restrict (Set.Icc a b)) := by
  have hd := torusDiffusion_test_integrable K hab U i φ
  have hvsum := integrable_finsetSum Finset.univ (fun k _ =>
    torusDrift_test_integrable K hab v hv hvc B hvb U i k φ)
  have hAsum := integrable_finsetSum Finset.univ (fun i' _ =>
    integrable_finsetSum Finset.univ (fun d _ => torusCoupling_test_integrable K D hab
      ρ hρ i i' d (A i i' d) (hA i i' d) (hAm i i' d) (fun r hr => hAc r hr i i' d) U φ))
  have hFi := torusFluxSource_test_integrable (K i) a b (F i) (hF i) φ
  have hgi := torusValueSource_test_integrable (K i) a b (g i) (hg i) φ
  simpa only [coupledTimeRhs, Pi.sub_apply, Pi.add_apply] using!
    ((((hd.const_mul (-ν)).sub hvsum).sub hAsum).sub hFi).add hgi

/-- The literal time integral of the full component form is its sum of integrated terms. -/
theorem coupledTimeRhs_integral (K : ι → ℕ) (D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ)
    {a b t : ℝ} (hab : a ≤ b) (ht : t ∈ Set.Icc a b) (v : ℝ → Vec 2 → Vec 2)
    (hv : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hvc : ∀ r ∈ Set.Icc a b, Continuous (v r))
    (B : ℝ) (hvb : ∀ r ∈ Set.Icc a b, ∀ x, ‖v r x‖ ≤ B)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hAm : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (hAc : ∀ r ∈ Set.Icc a b, ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d r))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (U : CoupledHighTime (h := h) K a b) (i : ι) (φ : TorusHk 1 (h i)) :
    (∫ r in a..t, coupledTimeRhs K D ν r v A F g (U r) i φ) =
      coupledIntegratedRhs K D ν a t v A F g U i φ := by
  unfold coupledTimeRhs coupledIntegratedRhs
  exact integratedFiniteForm_split hab ht ν _ _ _ _ _
    (torusDiffusion_test_integrable K hab U i φ)
    (fun k => torusDrift_test_integrable K hab v hv hvc B hvb U i k φ)
    (fun i' d => torusCoupling_test_integrable K D hab ρ hρ i i' d (A i i' d)
      (hA i i' d) (hAm i i' d) (fun r hr => hAc r hr i i' d) U φ)
    (torusFluxSource_test_integrable (K i) a b (F i) (hF i) φ)
    (torusValueSource_test_integrable (K i) a b (g i) (hg i) φ)
end

/-! Assemble all native terms in the integrated component equation. The
source remains L¹ in time; no extra coefficient regularity is introduced. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Assemble the literal time integrals of the whole finite coupled family. -/
theorem coupledTimeRhs_array_integral (K : ι → ℕ) (D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ)
    {a b t : ℝ} (hab : a ≤ b) (ht : t ∈ Set.Icc a b) (v : ℝ → Vec 2 → Vec 2)
    (hv : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hvc : ∀ r ∈ Set.Icc a b, Continuous (v r))
    (B : ℝ) (hvb : ∀ r ∈ Set.Icc a b, ∀ x, ‖v r x‖ ≤ B)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hAm : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (hAc : ∀ r ∈ Set.Icc a b, ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d r))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (U : CoupledHighTime (h := h) K a b) (φ : ∀ i, TorusHk 1 (h i)) :
    (∫ r in a..t, ∑ i, coupledTimeRhs K D ν r v A F g (U r) i (φ i)) =
      ∑ i, coupledIntegratedRhs K D ν a t v A F g U i (φ i) := by
  have hsub : Set.uIcc a t ⊆ Set.uIcc a b := by
    rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le hab]
    exact Set.Icc_subset_Icc le_rfl ht.2
  have hi (i : ι) : IntervalIntegrable
      (fun r => coupledTimeRhs K D ν r v A F g (U r) i (φ i)) volume a t :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (coupledTimeRhs_integrable K D ν ρ hρ hab v hv hvc B hvb A hA hAm hAc F g hF hg U i (φ i))).mono_set hsub
  rw [intervalIntegral.integral_finsetSum (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  exact coupledTimeRhs_integral K D ν ρ hρ hab ht v hv hvc B hvb A hA hAm hAc F g hF hg U i (φ i)
end

/-! Assemble all native terms in the integrated component equation. The
source remains L¹ in time; no extra coefficient regularity is introduced. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The original coupled RHS defines continuous scalar closed-time primitives. -/
theorem coupledIntegratedRhs_continuousOn (K : ι → ℕ) (D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ)
    {a b : ℝ} (hab : a ≤ b) (v : ℝ → Vec 2 → Vec 2)
    (hv : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hvc : ∀ r ∈ Set.Icc a b, Continuous (v r))
    (B : ℝ) (hvb : ∀ r ∈ Set.Icc a b, ∀ x, ‖v r x‖ ≤ B)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hAm : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (hAc : ∀ r ∈ Set.Icc a b, ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d r))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (U : CoupledHighTime (h := h) K a b) (i : ι) (φ : TorusHk 1 (h i)) :
    ContinuousOn (fun t => coupledIntegratedRhs K D ν a t v A F g U i φ) (Set.Icc a b) := by
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    (coupledTimeRhs_integrable K D ν ρ hρ hab v hv hvc B hvb A hA hAm hAc F g hF hg U i φ)
  have hc : ContinuousOn (fun t => ∫ r in a..t, coupledTimeRhs K D ν r v A F g (U r) i φ)
      (Set.Icc a b) := by
    simpa only [Set.uIcc_of_le hab] using
      intervalIntegral.continuousOn_primitive_interval' hi Set.left_mem_uIcc
  apply hc.congr
  intro t ht
  exact (coupledTimeRhs_integral K D ν ρ hρ hab ht v hv hvc B hvb A hA hAm hAc F g hF hg U i φ).symm
end

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CoupledEnergy.Variational

/-! Rewrite the native weak equation in terms of genuine Sobolev transport
and flux carriers. The scalar value source keeps its original L¹ role. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem coupledTimeRhs_carrier_split (K : ι → ℕ) (D : ℕ) (ν r : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (hc : Continuous (v r))
    (V : ℝ) (hV : 0 ≤ V) (hb : ∀ x, ‖v r x‖ ≤ V)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (U : CoupledHighHilbert (h := h) K)
    (T : ∀ i, TorusHk (K i) (h i))
    (G : ∀ i, TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (B : ∀ i i', admissibleOrders K D i i' → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hT : ∀ i, (T i).val (valueIndex2 (K i)) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => ∑ k : Fin 2, v r x k • (U i
        ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩ x))
    (hG : ∀ i, (G i).val (valueIndex2 (K i)) =ᵐ[volume.restrict AVenhance.unitCube]
      coupledHighGradientCLM (h := h) K i U)
    (hB : ∀ i i' d, (B i i' d).val (valueIndex2 (K i)) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => A i i' d r x (coupledHighTensorCLM (h := h) K i' (d.1 - 1)
        (admissibleOrders_high_readout_bound K D i i' d) U x)) (i : ι) (φ : TorusHk 1 (h i)) :
    coupledTimeRhs K D ν r v A F g U i φ =
      inner ℝ (torusHkValueCLM (g i r - T i)) (torusHkValueCLM φ) -
      inner ℝ (torusHkValueCLM (ν • G i + (∑ i', ∑ d, B i i' d) + F i r))
        (torusH1GradientL2CLM (E := h i) φ) := by
  have ht : inner ℝ (torusHkValueCLM (T i)) (torusHkValueCLM φ) =
      ∑ k : Fin 2, ∫ x in AVenhance.unitCube, v r x k *
        inner ℝ (coupledHighJetCLM K i
          ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩ U x) (torusHkValueCLM φ x) := by
    rw [L2.inner_def]
    have he : (fun x => inner ℝ (torusHkValueCLM (T i) x) (torusHkValueCLM φ x)) =ᵐ[
        volume.restrict AVenhance.unitCube] fun x => ∑ k : Fin 2, v r x k *
          inner ℝ (coupledHighJetCLM K i
            ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩ U x) (torusHkValueCLM φ x) := by
      filter_upwards [hT i] with x hx
      change inner ℝ ((T i).val (valueIndex2 (K i)) x) _ = _
      rw [hx, sum_inner]
      simp only [real_inner_smul_left, coupledHighJetCLM_apply]
    rw [integral_congr_ae he]
    exact integral_finsetSum Finset.univ (fun k _ => boundedScalar_inner_integrable
      (fun x => v r x k) ((continuous_apply k).comp hc) V hV
      (fun x => (norm_le_pi_norm (v r x) k).trans (hb x)) _ _)
  have hg : inner ℝ (torusHkValueCLM (G i)) (torusH1GradientL2CLM (E := h i) φ) =
      ∫ x in AVenhance.unitCube, inner ℝ (coupledHighGradientCLM (h := h) K i U x)
        (torusH1GradientL2CLM (E := h i) φ x) := by
    rw [L2.inner_def]
    exact integral_congr_ae ((hG i).mono (fun x hx => congrArg (fun z => inner ℝ z
      (torusH1GradientL2CLM (E := h i) φ x)) hx))
  have hbb (i' : ι) (d : admissibleOrders K D i i') :
      inner ℝ (torusHkValueCLM (B i i' d)) (torusH1GradientL2CLM (E := h i) φ) =
      ∫ x in AVenhance.unitCube, inner ℝ (A i i' d r x (coupledHighTensorCLM (h := h) K i'
        (d.1 - 1) (admissibleOrders_high_readout_bound K D i i' d) U x))
        (torusH1GradientL2CLM (E := h i) φ x) := by
    rw [L2.inner_def]
    exact integral_congr_ae ((hB i i' d).mono (fun x hx => congrArg (fun z => inner ℝ z
      (torusH1GradientL2CLM (E := h i) φ x)) hx))
  simp only [map_sub, map_add, map_smul, map_sum, inner_sub_left, inner_add_left,
    real_inner_smul_left, sum_inner]
  rw [ht, hg]
  simp_rw [hbb]
  simp only [coupledTimeRhs, L2.inner_def]
  ring

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Variational

/-! The native component equation is the integral of a genuinely
integrable spatial scalar form at every time in the closed interval. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

def torusNativeSpatialRhs (K : ι → ℕ) (D : ℕ) (ν r : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (U : CoupledHighHilbert (h := h) K) (i : ι) (φ : TorusHk 1 (h i)) (x : Vec 2) : ℝ :=
  -ν * inner ℝ (coupledHighGradientCLM (h := h) K i U x) (torusH1GradientL2CLM (E := h i) φ x) -
    (∑ k : Fin 2, v r x k * inner ℝ (coupledHighJetCLM K i
      ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩ U x) (Galerkin.torusHkValueCLM φ x)) -
    (∑ i', ∑ d : admissibleOrders K D i i', inner ℝ
      (A i i' d r x (coupledHighTensorCLM (h := h) K i' (d.1 - 1)
        (admissibleOrders_high_readout_bound K D i i' d) U x)) (torusH1GradientL2CLM (E := h i) φ x)) -
    inner ℝ (Galerkin.torusHkValueCLM (F i r) x) (torusH1GradientL2CLM (E := h i) φ x) +
    inner ℝ (Galerkin.torusHkValueCLM (g i r) x) (Galerkin.torusHkValueCLM φ x)

theorem torusNativeSpatialRhs_integrable_and_integral (K : ι → ℕ) (D : ℕ)
    (ν ρ : ℝ) (hρ : 0 < ρ) (a b r : ℝ) (hr : r ∈ Set.Icc a b)
    (v : ℝ → Vec 2 → Vec 2) (hv : Continuous (v r))
    (V : ℝ) (hV : 0 ≤ V) (hb : ∀ x, ‖v r x‖ ≤ V)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hc : ∀ i i' d, Continuous (A i i' d r))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (U : CoupledHighHilbert (h := h) K) (i : ι) (φ : TorusHk 1 (h i)) :
    Integrable (torusNativeSpatialRhs K D ν r v A F g U i φ) (volume.restrict AVenhance.unitCube) ∧
    (∫ x in AVenhance.unitCube, torusNativeSpatialRhs K D ν r v A F g U i φ x) =
      coupledTimeRhs K D ν r v A F g U i φ := by
  have hd := L2.integrable_inner (𝕜 := ℝ) (coupledHighGradientCLM (h := h) K i U)
    (torusH1GradientL2CLM (E := h i) φ)
  have hvi (k : Fin 2) := boundedScalar_inner_integrable (fun x => v r x k)
    ((continuous_apply k).comp hv) V hV (fun x => (norm_le_pi_norm (v r x) k).trans (hb x))
    (coupledHighJetCLM K i ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩ U)
    (Galerkin.torusHkValueCLM φ)
  have hci (i' : ι) (d : admissibleOrders K D i i') := staticCoefficient_pairing_integrable
    (A i i' d r) (hc i i' d) (coefficientSeminorm ρ (K i) a b (A i i' d)).toReal ENNReal.toReal_nonneg
    (fun x => Galerkin.plainCoefficient_norm_le_seminorm ρ hρ (K i) a b (A i i' d) (hA i i' d) r hr x)
    (coupledHighTensorCLM (h := h) K i' (d.1 - 1) (admissibleOrders_high_readout_bound K D i i' d) U)
    (torusH1GradientL2CLM (E := h i) φ)
  have hf := L2.integrable_inner (𝕜 := ℝ) (Galerkin.torusHkValueCLM (F i r)) (torusH1GradientL2CLM (E := h i) φ)
  have hg := L2.integrable_inner (𝕜 := ℝ) (Galerkin.torusHkValueCLM (g i r)) (Galerkin.torusHkValueCLM φ)
  simpa only [torusNativeSpatialRhs, coupledTimeRhs] using!
    finiteSpatialForm_integrable_and_integral (volume.restrict AVenhance.unitCube) ν _ _ _ _ _ hd hvi hci hf hg
end

/-! The actual higher graph readout has a genuine time L² gradient carrier. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem torusGradientTensor_value_ae {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {K : ℕ} (w : TorusHk (K + 1) E) :
    (torusGradientTensor w).val (valueIndex2 K) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => WithLp.toLp 2 (fun k : Fin 2 =>
        w.val ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos K)⟩, fun _ => k⟩ x) := by
  have hh := torusFamilyTensor_value_ae (fun k : Fin 2 => derivativeTorusHk (fun _ : Fin 1 => k) w)
  simpa only [torusGradientTensor, Galerkin.derivativeTorusHk_value_slot] using hh

theorem torusGradientTensor_family_value_ae (K : ι → ℕ) (a b : ℝ)
    (U : CoupledHighTime (h := h) K a b)
    (hU : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j,
      (coupledHighGraphReadout K j (U t)).val = U t j) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ i,
      (torusGradientTensor (coupledHighGraphReadout K i (U t))).val (valueIndex2 (K i)) =ᵐ[
        volume.restrict AVenhance.unitCube] coupledHighGradientCLM (h := h) K i (U t) := by
  filter_upwards [hU] with t ht
  intro i
  have hh := torusGradientTensor_value_ae (coupledHighGraphReadout K i (U t))
  rw [ht i] at hh
  exact hh.trans (coupledHighGradientCLM_ae K i (U t)).symm

theorem torusGradientTensor_memLp (K : ι → ℕ) {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ) (U : CoupledHighTime (h := h) K a b)
    (hU : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j,
      (coupledHighGraphReadout K j (U t)).val = U t j) (i : ι) :
    MemLp (fun t => torusGradientTensor (coupledHighGraphReadout K i (U t)))
      2 (volume.restrict (Set.Icc a b)) := by
  let T := fun t => torusGradientTensor (coupledHighGraphReadout K i (U t))
  have hv : ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      (T t).val (valueIndex2 (K i)) =ᵐ[volume.restrict AVenhance.unitCube]
        fun x => coupledHighGradientCLM (h := h) K i (U t) x := by
    filter_upwards [hU] with t ht
    have hg := torusGradientTensor_value_ae (coupledHighGraphReadout K i (U t))
    have hr := coupledHighGradientCLM_ae K i (U t)
    rw [ht i] at hg
    exact hg.trans hr.symm
  have hm := torusCoefficientCarrier_aestronglyMeasurable K hab U
    (coupledHighGradientCLM (h := h) K i)
    (fun _ _ => ContinuousLinearMap.id ℝ (PiLp 2 (fun _ : Fin 2 => h i)))
    measurable_const (fun _ _ => continuous_const) 1 (by norm_num)
    (fun _ _ _ => ContinuousLinearMap.norm_id_le) (K i) T (by simpa only [ContinuousLinearMap.id_apply] using hv)
  apply (highTimeGraphReadout_memLp K a b U i).of_le_mul hm
    (c := Real.sqrt (factorialWeightMax ρ (K i)) / Real.sqrt (factorialWeightMin ρ (K i)))
  apply Filter.Eventually.of_forall
  intro t
  have hn := jetNorm_le_factorialRoot ρ hρ (T t).val
  rw [torusGradientTensor_factorialNormSq] at hn
  have hg := gradFactorialRoot_le_jetNorm ρ (coupledHighGraphReadout K i (U t)).val
  calc
    _ ≤ Real.sqrt (gradFactorialNormSq ρ (coupledHighGraphReadout K i (U t)).val) /
        Real.sqrt (factorialWeightMin ρ (K i)) := hn
    _ ≤ (Real.sqrt (factorialWeightMax ρ (K i)) * ‖(coupledHighGraphReadout K i (U t)).val‖) /
        Real.sqrt (factorialWeightMin ρ (K i)) := div_le_div_of_nonneg_right hg (Real.sqrt_nonneg _)
    _ = _ := by change _ = (_ / _) * ‖(coupledHighGraphReadout K i (U t)).val‖; ring
end

/-! The literal raw spatial form used in the weak-solution class. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

def torusRawCouplingFlux (K : ι → ℕ) (D : ℕ) (r : ℝ)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (w : ∀ i, TorusHk (K i + 1) (h i)) (i : ι) (x : Vec 2) : PiLp 2 (fun _ : Fin 2 => h i) :=
  ∑ i', ∑ d : admissibleOrders K D i i', A i i' d r x
    (WithLp.toLp 2 (fun word : DerivativeWord2 (d.1 - 1) =>
      (w i').toFunction.jet ⟨⟨d.1 - 1, Nat.lt_succ_of_le (admissibleOrders_high_readout_bound K D i i' d)⟩, word⟩ x))

def torusRawSpatialRhs (K : ι → ℕ) (D : ℕ) (ν r : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (w : ∀ i, TorusHk (K i + 1) (h i)) (i : ι) (φ : TorusHk 1 (h i)) (x : Vec 2) : ℝ :=
  -(∑ k : Fin 2, v r x k * inner ℝ ((w i).toFunction.jet
      ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩ x) (φ.toFunction.jet (valueIndex2 1) x)) -
    ν * ∑ k : Fin 2, inner ℝ ((w i).toFunction.jet
      ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩ x)
      (φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x) -
    (∑ k : Fin 2, inner ℝ (torusRawCouplingFlux K D r A w i x k +
      (F i r).toFunction.jet (valueIndex2 (K i)) x k)
      (φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)) +
    inner ℝ ((g i r).toFunction.jet (valueIndex2 (K i)) x) (φ.toFunction.jet (valueIndex2 1) x)

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem torusRawCouplingFlux_pairing_ae (K : ι → ℕ) (D : ℕ) (r : ℝ)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (w : ∀ i, TorusHk (K i + 1) (h i)) (i : ι) (φ : TorusHk 1 (h i)) :
    (fun x => ∑ k : Fin 2, inner ℝ (torusRawCouplingFlux K D r A w i x k)
      (φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)) =ᵐ[volume.restrict AVenhance.unitCube]
    (fun x => ∑ i', ∑ d : admissibleOrders K D i i', inner ℝ
      (A i i' d r x (coupledHighTensorCLM (h := h) K i' (d.1 - 1)
        (admissibleOrders_high_readout_bound K D i i' d) (coupledCarrierHighJets K w) x))
      (torusH1GradientL2CLM (E := h i) φ x)) := by
  have ht := ae_all_iff.mpr (fun i' => ae_all_iff.mpr (fun d : admissibleOrders K D i i' =>
    torusRawCarrierTensor_ae K w i' (d.1 - 1) (admissibleOrders_high_readout_bound K D i i' d)))
  filter_upwards [ht, torusRawTestGradient_ae φ] with x hx hg
  change inner ℝ (torusRawCouplingFlux K D r A w i x)
    (WithLp.toLp 2 (fun k : Fin 2 => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)) = _
  rw [hg]
  unfold torusRawCouplingFlux
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro i' _
  rw [sum_inner]
  apply Finset.sum_congr rfl
  intro d _
  rw [hx i' d]

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] in
theorem torusRawDiffusion_pairing_ae (K : ι → ℕ) (w : ∀ i, TorusHk (K i + 1) (h i))
    (i : ι) (φ : TorusHk 1 (h i)) :
    (fun x => ∑ k : Fin 2, inner ℝ ((w i).toFunction.jet
      ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩ x)
      (φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)) =ᵐ[volume.restrict AVenhance.unitCube]
    (fun x => inner ℝ (coupledHighGradientCLM (h := h) K i (coupledCarrierHighJets K w) x)
      (torusH1GradientL2CLM (E := h i) φ x)) := by
  filter_upwards [torusRawCarrierGradient_ae K w i, torusRawTestGradient_ae φ] with x hg ht
  change inner ℝ (WithLp.toLp 2 (fun k : Fin 2 => (w i).toFunction.jet
    ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩ x))
    (WithLp.toLp 2 (fun k : Fin 2 => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)) = _
  rw [hg, ht]

theorem torusRawFlux_pairing_ae (K : ι → ℕ) (D : ℕ) (r : ℝ)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (w : ∀ i, TorusHk (K i + 1) (h i)) (i : ι) (φ : TorusHk 1 (h i)) :
    (fun x => ∑ k : Fin 2, inner ℝ (torusRawCouplingFlux K D r A w i x k +
      (F i r).toFunction.jet (valueIndex2 (K i)) x k)
      (φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)) =ᵐ[volume.restrict AVenhance.unitCube]
    (fun x => (∑ i', ∑ d : admissibleOrders K D i i', inner ℝ
      (A i i' d r x (coupledHighTensorCLM (h := h) K i' (d.1 - 1)
        (admissibleOrders_high_readout_bound K D i i' d) (coupledCarrierHighJets K w) x))
      (torusH1GradientL2CLM (E := h i) φ x)) +
      inner ℝ (Galerkin.torusHkValueCLM (F i r) x) (torusH1GradientL2CLM (E := h i) φ x)) := by
  filter_upwards [torusRawCouplingFlux_pairing_ae K D r A w i φ,
    torusRawValue_ae (F i r), torusRawTestGradient_ae φ] with x hc hf ht
  simp only [inner_add_left, Finset.sum_add_distrib]
  rw [hc]
  congr 1
  change inner ℝ ((F i r).toFunction.jet (valueIndex2 (K i)) x)
    (WithLp.toLp 2 (fun k : Fin 2 => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)) = _
  rw [hf, ht]

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] in
theorem torusRawDrift_pairing_ae (K : ι → ℕ) (r : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (w : ∀ i, TorusHk (K i + 1) (h i)) (i : ι) (φ : TorusHk 1 (h i)) :
    (fun x => ∑ k : Fin 2, v r x k * inner ℝ ((w i).toFunction.jet
      ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩ x)
      (φ.toFunction.jet (valueIndex2 1) x)) =ᵐ[volume.restrict AVenhance.unitCube]
    (fun x => ∑ k : Fin 2, v r x k * inner ℝ (coupledHighJetCLM K i
      ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩ (coupledCarrierHighJets K w) x)
      (Galerkin.torusHkValueCLM φ x)) := by
  have hd := ae_all_iff.mpr (fun k : Fin 2 => torusRawJet_ae (w i)
    ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩)
  filter_upwards [hd, torusRawValue_ae φ] with x hd hp
  apply Finset.sum_congr rfl
  intro k _
  rw [hd k, hp]
  rfl

theorem torusRawSpatialRhs_ae_native (K : ι → ℕ) (D : ℕ) (ν r : ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (w : ∀ i, TorusHk (K i + 1) (h i)) (i : ι) (φ : TorusHk 1 (h i)) :
    torusRawSpatialRhs K D ν r v A F g w i φ =ᵐ[volume.restrict AVenhance.unitCube]
      torusNativeSpatialRhs K D ν r v A F g (coupledCarrierHighJets K w) i φ := by
  filter_upwards [torusRawDiffusion_pairing_ae K w i φ, torusRawFlux_pairing_ae K D r A F w i φ,
    torusRawDrift_pairing_ae K r v w i φ, torusRawValue_ae (g i r), torusRawValue_ae φ]
    with x hd hf hv hg hp
  unfold torusRawSpatialRhs torusNativeSpatialRhs
  rw [hd, hf, hv, hg, hp]
  ring
end

end AVRegularity.CoupledEnergy.Variational
end
