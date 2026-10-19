-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CoupledEnergy.Variational.ConstantTimeTest
public import AVRegularity.CoupledEnergyPlane.Fourier.CarrierPairing
public import AVRegularity.Statements.Intermediate.CoupledEnergy.AdmissibleOrders
public import AVRegularity.CoupledEnergy.Variational.FactorialPairing
import AVRegularity.CoupledEnergy.Variational.PullbackForm
public import AVRegularity.CoupledEnergyPlane.Fourier.BandJetOperator
public import AVRegularity.Statements.Intermediate.CoupledEnergy.MassNormSq
import AVRegularity.CoupledEnergy.Variational.MassWeightedCarrierCLM
import AVenhance.Infra.ODE.Linear.Energy

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergyPlane

/-! The factorial jet pairing is exactly the weighted sum of actual ordered tensor pairings. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] {U : Set (Vec 2)} {K : ℕ}

theorem factorialPairing_truncate_eq_order_sum (ρ : ℝ)
    (D : JetL2 (volume.restrict U) K E) (Q : JetL2 (volume.restrict U) (K + 1) E) :
    factorialPairing ρ D (truncateJet (Nat.le_succ K) Q) =
      ∑ j : Fin (K + 1), factorialWeight ρ j.val *
        inner ℝ (orderL2Array D j) (orderL2Array Q ⟨j.val, by omega⟩) := by
  simp only [factorialPairing, PiLp.inner_apply]
  rfl

end AVRegularity.CoupledEnergyPlane
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CoupledEnergyPlane

/-! Actual bounded coefficient multiplication on plane L², with inputwise time measurability. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

/-- Literal bounded spatial multiplication with the univ restriction removed. -/
def planeCoefficientOperator (C : Vec 2 → E →L[ℝ] F) (hc : Continuous C)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, ‖C x‖ ≤ M) :
    Lp E 2 (volume : Measure (Vec 2)) →L[ℝ] Lp F 2 (volume : Measure (Vec 2)) :=
  univToPlane.toContinuousLinearMap.comp
    ((boundedCoefficientL2CLM (U := Set.univ) C hc M hM hb).comp
      planeToUniv.toContinuousLinearMap)

omit [BorelSpace E] [CompleteSpace E] [BorelSpace F] [CompleteSpace F] in
theorem planeCoefficientOperator_ae (C : Vec 2 → E →L[ℝ] F) (hc : Continuous C)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, ‖C x‖ ≤ M)
    (u : Lp E 2 (volume : Measure (Vec 2))) :
    planeCoefficientOperator C hc hM hb u =ᵐ[volume] fun x => C x (u x) := by
  have hm := boundedCoefficientL2_ae (U := Set.univ) C hc M hM hb (planeToUniv u)
  simp only [Measure.restrict_univ] at hm
  filter_upwards [univToPlane_ae
    (boundedCoefficientL2 C hc M hM hb (planeToUniv u)), hm, planeToUniv_ae u]
    with x hx hp hu
  exact hx.trans (hp.trans (congrArg (C x) hu))

omit [BorelSpace E] [CompleteSpace E] [BorelSpace F] [CompleteSpace F] in
theorem planeCoefficientOperator_norm_le (C : Vec 2 → E →L[ℝ] F) (hc : Continuous C)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, ‖C x‖ ≤ M) :
    ‖planeCoefficientOperator C hc hM hb‖ ≤ M := by
  apply ContinuousLinearMap.opNorm_le_bound _ hM
  intro u
  change ‖univToPlane (boundedCoefficientL2 C hc M hM hb (planeToUniv u))‖ ≤ M * ‖u‖
  rw [univToPlane.norm_map]
  exact (boundedCoefficientL2_norm_le C hc M hM hb _).trans_eq
    (by rw [planeToUniv.norm_map])

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

omit [BorelSpace E] [CompleteSpace E] [BorelSpace F] [CompleteSpace F] in
/-- Joint coefficient measurability implies strong measurability on each fixed spatial input. -/
theorem planeCoefficientOperator_stronglyMeasurable {T : Type*} [MeasurableSpace T]
    (C : T → Vec 2 → E →L[ℝ] F) (hc : ∀ t, Continuous (C t))
    (hj : Measurable (Function.uncurry C)) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ t x, ‖C t x‖ ≤ M) (u : Lp E 2 (volume : Measure (Vec 2))) :
    StronglyMeasurable (fun t => planeCoefficientOperator (C t) (hc t) hM (hb t) u) := by
  have heval : Continuous (fun p : (E →L[ℝ] F) × E => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hprod : StronglyMeasurable (fun p : T × Vec 2 => C p.1 p.2 (planeToUniv u p.2)) :=
    heval.comp_stronglyMeasurable
      (hj.stronglyMeasurable.prodMk
        ((Lp.stronglyMeasurable (planeToUniv u)).comp_measurable measurable_snd))
  exact univToPlane.continuous.comp_stronglyMeasurable
    (stronglyMeasurable_toLp_slices hprod
      (fun t => memLp_operator_mul (hc t) (Lp.memLp (planeToUniv u)) hM (hb t)))

omit [BorelSpace E] [CompleteSpace E] [BorelSpace F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem planeCoefficientOperator_inner_eq_integral (C : Vec 2 → E →L[ℝ] F)
    (hc : Continuous C) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, ‖C x‖ ≤ M)
    (u : Lp E 2 (volume : Measure (Vec 2))) (z : Lp F 2 (volume : Measure (Vec 2))) :
    inner ℝ (planeCoefficientOperator C hc hM hb u) z =
      ∫ x, inner ℝ (C x (u x)) (z x) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [planeCoefficientOperator_ae C hc hM hb u] with x hx
  rw [hx]

end AVRegularity.CoupledEnergyPlane
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergyPlane

/-! Each native Galerkin coefficient term has genuine time integrability. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

omit [BorelSpace E] [CompleteSpace E] [BorelSpace F] [CompleteSpace F] in
theorem planeCoefficientAction_memLp (a b : ℝ)
    (C : ℝ → Vec 2 → E →L[ℝ] F) (hc : ∀ t, Continuous (C t))
    (hj : Measurable (Function.uncurry C)) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ t x, ‖C t x‖ ≤ M)
    (u : ℝ → Lp E 2 (volume : Measure (Vec 2))) (hu : Continuous u) :
    MemLp (fun t => planeCoefficientOperator (C t) (hc t) hM (hb t) (u t)) 2
      (volume.restrict (Set.Icc a b)) := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  let : SecondCountableTopology (Lp E 2 (volume : Measure (Vec 2))) := Lp.SecondCountableTopology
  borelize ↥(Lp E 2 (volume : Measure (Vec 2)))
  have hm : MemLp u 2 (volume.restrict (Set.Icc a b)) :=
    (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable.restrict).mpr
      ((hu.norm.pow 2).integrableOn_Icc)
  exact memLp_operator_action (fun t => planeCoefficientOperator (C t) (hc t) hM (hb t))
    (fun x => planeCoefficientOperator_stronglyMeasurable C hc hj hM hb x) hm hM
    (fun t => planeCoefficientOperator_norm_le (C t) (hc t) hM (hb t))

omit [BorelSpace E] [CompleteSpace E] [BorelSpace F] [CompleteSpace F] in
theorem planeCoefficientAction_inner_intervalIntegrable {a b : ℝ} (hab : a ≤ b)
    (C : ℝ → Vec 2 → E →L[ℝ] F) (hc : ∀ t, Continuous (C t))
    (hj : Measurable (Function.uncurry C)) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ t x, ‖C t x‖ ≤ M)
    (u : ℝ → Lp E 2 (volume : Measure (Vec 2))) (hu : Continuous u)
    (z : Lp F 2 (volume : Measure (Vec 2))) :
    IntervalIntegrable (fun t => inner ℝ
      (planeCoefficientOperator (C t) (hc t) hM (hb t) (u t)) z) volume a b := by
  have hm := (innerSL ℝ z).comp_memLp' (planeCoefficientAction_memLp a b C hc hj hM hb u hu)
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
  simpa only [IntegrableOn, Function.comp_def, innerSL_apply_apply, real_inner_comm] using hm.integrable (by norm_num)

end AVRegularity.CoupledEnergyPlane
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CoupledEnergyPlane

/-! Unclamp a coefficient on a tested subinterval and recover its literal spatial integral. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [MeasurableSpace F] [BorelSpace E] [BorelSpace F]
  [CompleteSpace E] [CompleteSpace F]

omit [BorelSpace E] [BorelSpace F] [CompleteSpace E] [CompleteSpace F] in
theorem coefficient_clamped_intervalPairing {a b t : ℝ} (hab : a ≤ b)
    (ht : t ∈ Set.Icc a b) (C : ℝ → Vec 2 → E →L[ℝ] F)
    (hc : ∀ s ∈ Set.Icc a b, Continuous (C s)) {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ s ∈ Set.Icc a b, ∀ x, ‖C s x‖ ≤ M)
    (U : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (z : Lp F 2 (volume : Measure (Vec 2))) :
    (∫ s in a..t, inner ℝ
      (planeCoefficientOperator (C (clampPoint a b hab s))
        (hc _ (clampPoint a b hab s).property) hM
        (hb _ (clampPoint a b hab s).property) (U s)) z) =
      ∫ s in a..t, ∫ x, inner ℝ (C s x (U s x)) (z x) := by
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Set.Icc a b := by
    rw [Set.uIcc_of_le ht.1] at hs
    exact ⟨hs.1, hs.2.trans ht.2⟩
  dsimp only
  rw [planeCoefficientOperator_inner_eq_integral]
  have hp : (clampPoint a b hab s : ℝ) = s := by
    simp only [clampPoint, max_eq_right hs'.1, min_eq_right hs'.2]
  rw [hp]

end AVRegularity.CoupledEnergyPlane
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped Topology
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergyPlane

/-! Native bounded spatial coefficients as fixed temporal operators. These
operators retain the literal coefficient integrals when tested on subintervals. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- The original coefficient field acts as one bounded operator on time L². -/
def coefficientTimeCLM {T : Type*} [MeasurableSpace T]
    (μ : Measure T) (C : T → Vec 2 → E →L[ℝ] F)
    (hC : Measurable (Function.uncurry C)) (hc : ∀ t, Continuous (C t))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ t x, ‖C t x‖ ≤ M) :
    Lp (Lp E 2 (volume : Measure (Vec 2))) 2 μ →L[ℝ]
      Lp (Lp F 2 (volume : Measure (Vec 2))) 2 μ := by
  let : SecondCountableTopology (Lp E 2 (volume : Measure (Vec 2))) :=
    by
      let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
      let : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
      exact Lp.SecondCountableTopology
  borelize ↥(Lp E 2 (volume : Measure (Vec 2)))
  let L := fun t => planeCoefficientOperator (C t) (hc t) hM (hb t)
  exact timeOperatorCLM μ L
    (fun x => planeCoefficientOperator_stronglyMeasurable C hc hC hM hb x)
    M hM (fun t => planeCoefficientOperator_norm_le (C t) (hc t) hM (hb t))

omit [BorelSpace E] [CompleteSpace E] [BorelSpace F] [CompleteSpace F] in
/-- The temporal operator represents the actual spatial multiplication almost everywhere. -/
theorem coefficientTimeCLM_ae {T : Type*} [MeasurableSpace T]
    (μ : Measure T) (C : T → Vec 2 → E →L[ℝ] F)
    (hC : Measurable (Function.uncurry C)) (hc : ∀ t, Continuous (C t))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ t x, ‖C t x‖ ≤ M)
    (U : Lp (Lp E 2 (volume : Measure (Vec 2))) 2 μ) :
    coefficientTimeCLM μ C hC hc M hM hb U =ᵐ[μ]
      fun t => planeCoefficientOperator (C t) (hc t) hM (hb t) (U t) := by
  let : SecondCountableTopology (Lp E 2 (volume : Measure (Vec 2))) :=
    by
      let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
      let : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
      exact Lp.SecondCountableTopology
  borelize ↥(Lp E 2 (volume : Measure (Vec 2)))
  exact timeOperatorValue_ae μ
    (fun t => planeCoefficientOperator (C t) (hc t) hM (hb t))
    (fun x => planeCoefficientOperator_stronglyMeasurable C hc hC hM hb x) M hM
    (fun t => planeCoefficientOperator_norm_le (C t) (hc t) hM (hb t)) U

omit [BorelSpace E] [CompleteSpace E] [BorelSpace F] [CompleteSpace F] in
/-- Testing the native temporal coefficient action gives the literal double integral. -/
theorem coefficientTimeCLM_test_integral {a b s t : ℝ}
    (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t)
    (C : ℝ → Vec 2 → E →L[ℝ] F)
    (hC : Measurable (Function.uncurry C)) (hc : ∀ r, Continuous (C r))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ r x, ‖C r x‖ ≤ M)
    (U : Lp (Lp E 2 (volume : Measure (Vec 2))) 2
      (volume.restrict (Set.Icc a b)))
    (z : ℝ → Lp F 2 (volume : Measure (Vec 2)))
    (hz : MemLp z 2 (volume.restrict (Set.Icc a b))) :
    timeTestIntegralCLM a b s t z hz
      (coefficientTimeCLM (volume.restrict (Set.Icc a b)) C hC hc M hM hb U) =
      ∫ r in s..t, ∫ x, inner ℝ (C r x (U r x)) (z r x) := by
  rw [timeTestIntegralCLM_apply_class hs ht hst]
  apply intervalIntegral.integral_congr_ae_restrict
  have he := coefficientTimeCLM_ae (volume.restrict (Set.Icc a b)) C hC hc M hM hb U
  have hsub : Set.uIoc s t ⊆ Set.Icc a b := by
    rw [Set.uIoc_of_le hst]
    exact Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc hs.1 ht.2)
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub he] with r hr
  rw [hr]
  exact planeCoefficientOperator_inner_eq_integral (C r) (hc r) hM (hb r) (U r) (z r)

end AVRegularity.CoupledEnergyPlane
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CoupledEnergyPlane

/-! Fixed spatial tests of actual coefficient time classes recover literal spatial integrals. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [MeasurableSpace F] [BorelSpace E] [BorelSpace F]
  [CompleteSpace E] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

omit [BorelSpace E] [BorelSpace F] [CompleteSpace E] [CompleteSpace F] in
theorem coefficientTimeCLM_fixed_test_integral {a b t : ℝ} (ht : t ∈ Set.Icc a b)
    (C : ℝ → Vec 2 → E →L[ℝ] F)
    (hC : Measurable (Function.uncurry C)) (hc : ∀ r, Continuous (C r))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ r x, ‖C r x‖ ≤ M)
    (U : Lp (Lp E 2 (volume : Measure (Vec 2))) 2 (volume.restrict (Set.Icc a b)))
    (z : Lp F 2 (volume : Measure (Vec 2))) :
    (∫ s in a..t, inner ℝ
      (coefficientTimeCLM (volume.restrict (Set.Icc a b)) C hC hc M hM hb U s) z) =
      ∫ s in a..t, ∫ x, inner ℝ (C s x (U s x)) (z x) := by
  apply intervalIntegral.integral_congr_ae_restrict
  have hsub : Set.uIoc a t ⊆ Set.Icc a b := by
    rw [Set.uIoc_of_le ht.1]
    exact Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl ht.2)
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub
    (coefficientTimeCLM_ae (volume.restrict (Set.Icc a b)) C hC hc M hM hb U)] with s hs
  rw [hs]
  exact planeCoefficientOperator_inner_eq_integral _ _ _ _ _ _

end AVRegularity.CoupledEnergyPlane
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane

/-! Pass native coefficient integrals through weak trial convergence and
strong convergence of projected spatial tests. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

omit [BorelSpace E] [BorelSpace F] [CompleteSpace F] in
/-- Uniformly bounded weak trials and strongly converging spatial tests pass through literal coefficient rows. -/
theorem coefficient_integral_weak_limit_moving_test {a b s t : ℝ}
    (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t)
    (C : ℝ → Vec 2 → E →L[ℝ] F)
    (hC : Measurable (Function.uncurry C)) (hc : ∀ r, Continuous (C r))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ r x, ‖C r x‖ ≤ M)
    (U : ℕ → Lp (Lp E 2 (volume : Measure (Vec 2))) 2
      (volume.restrict (Set.Icc a b)))
    (V : Lp (Lp E 2 (volume : Measure (Vec 2))) 2
      (volume.restrict (Set.Icc a b)))
    (R : ℝ) (hu : ∀ n, ‖U n‖ ≤ R)
    (hw : ∀ ell : Lp (Lp E 2 (volume : Measure (Vec 2))) 2
        (volume.restrict (Set.Icc a b)) →L[ℝ] ℝ,
      Tendsto (fun n => ell (U n)) atTop (𝓝 (ell V)))
    (z : ℕ → Lp F 2 (volume : Measure (Vec 2)))
    (w : Lp F 2 (volume : Measure (Vec 2))) (hz : Tendsto z atTop (𝓝 w)) :
    Tendsto (fun n => ∫ r in s..t, ∫ x,
      inner ℝ (C r x (U n r x)) (z n x)) atTop
      (𝓝 (∫ r in s..t, ∫ x, inner ℝ (C r x (V r x)) (w x))) := by
  let μ := volume.restrict (Set.Icc a b)
  let B := pullbackInnerCLM
    (constantTimeTestCLM (G := Lp F 2 (volume : Measure (Vec 2)))
      μ (Set.Ioc s t) measurableSet_Ioc (measure_ne_top μ _))
    (coefficientTimeCLM μ C hC hc M hM hb)
  have happly (u : Lp (Lp E 2 (volume : Measure (Vec 2))) 2 μ)
      (q : Lp F 2 (volume : Measure (Vec 2))) :
      B q u = ∫ r in s..t, ∫ x, inner ℝ (C r x (u r x)) (q x) := by
    change timeTestIntegralCLM a b s t (fun _ => q) (memLp_const q)
      (coefficientTimeCLM μ C hC hc M hM hb u) = _
    exact coefficientTimeCLM_test_integral hs ht hst C hC hc M hM hb u (fun _ => q) (memLp_const q)
  simpa only [happly] using bilinear_weak_limit_moving_test B U V R hu hw z w hz
end

/-! Pass native coefficient integrals through weak trial convergence and
strong convergence of projected spatial tests. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

omit [BorelSpace E] [BorelSpace F] [CompleteSpace F] in
/-- Uniformly bounded weak trials and strongly converging spatial tests pass through literal coefficient rows. -/
theorem intervalCoefficient_integral_weak_limit_moving_test {a b s t : ℝ}
    (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t)
    (C : ℝ → Vec 2 → E →L[ℝ] F)
    (hC : Measurable (fun p : Set.Icc a b × Vec 2 => C p.1 p.2))
    (hc : ∀ r ∈ Set.Icc a b, Continuous (C r))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ r ∈ Set.Icc a b, ∀ x, ‖C r x‖ ≤ M)
    (U : ℕ → Lp (Lp E 2 (volume : Measure (Vec 2))) 2
      (volume.restrict (Set.Icc a b)))
    (V : Lp (Lp E 2 (volume : Measure (Vec 2))) 2
      (volume.restrict (Set.Icc a b)))
    (R : ℝ) (hu : ∀ n, ‖U n‖ ≤ R)
    (hw : ∀ ell : Lp (Lp E 2 (volume : Measure (Vec 2))) 2
        (volume.restrict (Set.Icc a b)) →L[ℝ] ℝ,
      Tendsto (fun n => ell (U n)) atTop (𝓝 (ell V)))
    (z : ℕ → Lp F 2 (volume : Measure (Vec 2)))
    (w : Lp F 2 (volume : Measure (Vec 2))) (hz : Tendsto z atTop (𝓝 w)) :
    Tendsto (fun n => ∫ r in s..t, ∫ x,
      inner ℝ (C r x (U n r x)) (z n x)) atTop
      (𝓝 (∫ r in s..t, ∫ x, inner ℝ (C r x (V r x)) (w x))) := by
  have hab : a ≤ b := hs.1.trans hs.2
  let Cp := fun r x => C (Set.projIcc a b hab r) x
  have hmeas : Measurable (Function.uncurry Cp) := by
    exact hC.comp (((continuous_projIcc (a := a) (b := b) (h := hab)).measurable.comp
      measurable_fst).prodMk measurable_snd)
  have hcont (r : ℝ) : Continuous (Cp r) := hc _ (Set.projIcc a b hab r).property
  have hbound (r : ℝ) (x : Vec 2) : ‖Cp r x‖ ≤ M := hb _ (Set.projIcc a b hab r).property x
  have heq (u : Lp (Lp E 2 (volume : Measure (Vec 2))) 2
      (volume.restrict (Set.Icc a b))) (q : Lp F 2 (volume : Measure (Vec 2))) :
      (∫ r in s..t, ∫ x, inner ℝ (Cp r x (u r x)) (q x)) =
      ∫ r in s..t, ∫ x, inner ℝ (C r x (u r x)) (q x) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with r hr
    have hr' : r ∈ Set.Icc a b := by
      rw [Set.uIoc_of_le hst] at hr
      exact ⟨hs.1.trans hr.1.le, hr.2.trans ht.2⟩
    simp only [Cp, Set.projIcc_of_mem hab hr']
  simpa only [heq] using coefficient_integral_weak_limit_moving_test hs ht hst Cp hmeas hcont
    M hM hbound U V R hu hw z w hz
end

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational AVenhance.Infra.ODE
namespace AVRegularity.CoupledEnergyPlane

/-! Integrated factorial energy for actual absolutely continuous Hilbert jet curves. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] {μ : Measure (Vec 2)} {K : ℕ}

theorem factorialPairing_eq_weighted_inner (ρ : ℝ) (D Q : JetL2 μ K E) :
    factorialPairing ρ D Q =
      inner ℝ (factorialWeightedJet ρ D) (factorialWeightedJet ρ Q) := by
  rw [PiLp.inner_apply]
  change _ = ∑ α : JetIndex2 K,
    inner ℝ (factorialRootWeight ρ α.1.val • D α)
      (factorialRootWeight ρ α.1.val • Q α)
  rw [Fintype.sum_sigma]
  simp only [real_inner_smul_left, real_inner_smul_right]
  simp_rw [← mul_assoc, ← pow_two, factorialRootWeight_sq]
  simp only [factorialPairing, Finset.mul_sum]

theorem factorialNormSq_absolutelyContinuous {c : ℝ → JetL2 μ K E} {a b : ℝ}
    (ρ : ℝ) (hc : AbsolutelyContinuousOnInterval c a b) :
    AbsolutelyContinuousOnInterval (fun t => factorialNormSq ρ (c t)) a b := by
  have h := ((factorialWeightedJetCLM (E := E) (μ := μ) ρ K).lipschitzWith.comp_absolutelyContinuousOnInterval hc).norm_sq
  simpa only [Function.comp_def, factorialWeightedJetCLM_apply,
    factorialWeightedJet_normSq] using h

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization
open AVRegularity.CoupledEnergyPlane.Fourier AVenhance.Infra.ODE
namespace AVRegularity.CoupledEnergyPlane

/-! Continuous fixed-frequency traces constructed from the weak solution's integrable native fields. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def fixedBandRhs {a b : ℝ} (N : ℕ) (ν : ℝ)
    (V D : Lp (Lp E 2 (volume : Measure (Vec 2))) 2 (volume.restrict (Set.Icc a b)))
    (F : Lp (Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 (volume : Measure (Vec 2)))
      2 (volume.restrict (Set.Icc a b)))
    (g : ℝ → Lp E 2 (volume : Measure (Vec 2))) (s : ℝ) :
    Lp E 2 (volume : Measure (Vec 2)) :=
  -hilbertProjection (E := E) N (D s) + ν • bandLaplacianOperator (E := E) N (V s) +
    bandDivergenceOperator (E := E) N (F s) + hilbertProjection (E := E) N (g s)

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem fixedBandRhs_intervalIntegrable {a b : ℝ} (hab : a ≤ b) (N : ℕ) (ν : ℝ)
    (V D : Lp (Lp E 2 (volume : Measure (Vec 2))) 2 (volume.restrict (Set.Icc a b)))
    (F : Lp (Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 (volume : Measure (Vec 2)))
      2 (volume.restrict (Set.Icc a b)))
    (g : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (hg : Integrable g (volume.restrict (Set.Icc a b))) :
    IntervalIntegrable (fixedBandRhs N ν V D F g) volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
  have hD := (hilbertProjection (E := E) N).integrable_comp
    ((Lp.memLp D).integrable (by norm_num))
  have hV := (bandLaplacianOperator (E := E) N).integrable_comp
    ((Lp.memLp V).integrable (by norm_num))
  have hF := (bandDivergenceOperator (E := E) N).integrable_comp
    ((Lp.memLp F).integrable (by norm_num))
  have hg' := (hilbertProjection (E := E) N).integrable_comp hg
  change Integrable (fixedBandRhs (E := E) N ν V D F g)
    (volume.restrict (Set.Icc a b))
  exact (((hD.neg.add (hV.smul ν)).add hF).add hg').congr
    (by filter_upwards with s; rfl)

def fixedBandPrimitive {a b : ℝ} (hab : a ≤ b) (N : ℕ) (ν : ℝ)
    (f : Lp E 2 (volume : Measure (Vec 2)))
    (V D : Lp (Lp E 2 (volume : Measure (Vec 2))) 2 (volume.restrict (Set.Icc a b)))
    (F : Lp (Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 (volume : Measure (Vec 2)))
      2 (volume.restrict (Set.Icc a b)))
    (g : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (hg : Integrable g (volume.restrict (Set.Icc a b))) :
    C(Set.Icc a b, Lp E 2 (volume : Measure (Vec 2))) :=
  ⟨fun t => hilbertProjection N f + ∫ s in a..t.1, fixedBandRhs N ν V D F g s, by
    change Continuous (Set.domRestrict (Set.Icc a b) (fun t : ℝ =>
      hilbertProjection (E := E) N f + ∫ s in a..t, fixedBandRhs (E := E) N ν V D F g s))
    apply continuousOn_iff_continuous_domRestrict.mp
    have hp := continuousOn_intervalPrimitive
      (fixedBandRhs_intervalIntegrable hab N ν V D F g hg)
    rw [Set.uIcc_of_le hab] at hp
    convert (continuousOn_const.add hp) using 1⟩

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane

/-! Every bounded spatial observable tests the actual fixed-frequency primitive. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
theorem fixedBandPrimitive_test {a b : ℝ} (hab : a ≤ b) (N : ℕ) (ν : ℝ)
    (f : Lp E 2 (volume : Measure (Vec 2)))
    (V D : Lp (Lp E 2 (volume : Measure (Vec 2))) 2 (volume.restrict (Set.Icc a b)))
    (F : Lp (Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 (volume : Measure (Vec 2)))
      2 (volume.restrict (Set.Icc a b)))
    (g : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (hg : Integrable g (volume.restrict (Set.Icc a b))) (t : Set.Icc a b)
    (ell : Lp E 2 (volume : Measure (Vec 2)) →L[ℝ] ℝ) :
    ell (fixedBandPrimitive hab N ν f V D F g hg t) =
      ell (hilbertProjection N f) + ∫ s in a..t.1, ell (fixedBandRhs N ν V D F g s) := by
  have hsub : Set.uIcc a t.1 ⊆ Set.uIcc a b := by
    rw [Set.uIcc_of_le t.property.1, Set.uIcc_of_le hab]
    exact Set.Icc_subset_Icc le_rfl t.property.2
  have hi := (fixedBandRhs_intervalIntegrable hab N ν V D F g hg).mono_set hsub
  change ell (hilbertProjection N f + ∫ s in a..t.1, fixedBandRhs N ν V D F g s) = _
  rw [map_add, ← ell.intervalIntegral_comp_comm hi]
end

/-! The fixed-frequency primitives remain in their genuine Fourier ranges. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem fixedBandRhs_projection {a b : ℝ} (N : ℕ) (ν : ℝ)
    (V D : Lp (Lp E 2 (volume : Measure (Vec 2))) 2 (volume.restrict (Set.Icc a b)))
    (F : Lp (Lp (PiLp 2 (fun _ : Fin 2 => E)) 2 (volume : Measure (Vec 2)))
      2 (volume.restrict (Set.Icc a b)))
    (g : ℝ → Lp E 2 (volume : Measure (Vec 2))) (s : ℝ) :
    hilbertProjection N (fixedBandRhs N ν V D F g s) = fixedBandRhs N ν V D F g s := by
  simp only [fixedBandRhs, map_add, map_neg, map_smul, hilbertProjection_idempotent,
    hilbertProjection_laplacian, hilbertProjection_divergence]
end

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CoupledEnergyPlane

/-! The complete plane coupled system projected on actual bounded Fourier frequencies.
Construction helpers use ordinary coefficient bounds, subsequently obtained from the data. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- All components evolve simultaneously in the product of actual plane L² spaces. -/
abbrev ProjectedFamily (h : ι → Type*) [∀ i, NormedAddCommGroup (h i)] :=
  PiLp 2 (fun i => Lp (h i) 2 (volume : Measure (Vec 2)))

/-- Bounded smooth coefficients for constructing the cutoff-dependent evolution. -/
structure ProjectedCoefficients (T : Type*) (K : ι → ℕ) (D : ℕ) where
  drift : ∀ i, T → Vec 2 → (PiLp 2 (fun _ : Fin 2 => h i)) →L[ℝ] h i
  drift_continuous : ∀ i t, Continuous (drift i t)
  drift_bound : ι → ℝ
  drift_bound_nonneg : ∀ i, 0 ≤ drift_bound i
  drift_le : ∀ i t x, ‖drift i t x‖ ≤ drift_bound i
  coupling : ∀ i j, ∀ d : AVRegularity.admissibleOrders K D i j,
    T → Vec 2 → (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j)) →L[ℝ]
      (PiLp 2 (fun _ : Fin 2 => h i))
  coupling_continuous : ∀ i j d t, Continuous (coupling i j d t)
  coupling_bound : ∀ i j, AVRegularity.admissibleOrders K D i j → ℝ
  coupling_bound_nonneg : ∀ i j d, 0 ≤ coupling_bound i j d
  coupling_le : ∀ i j d t x, ‖coupling i j d t x‖ ≤ coupling_bound i j d

/-- Projected transport contribution to one row. -/
def projectedDriftRow {T : Type*} {K : ι → ℕ} {D : ℕ}
    (C : ProjectedCoefficients (h := h) T K D) (N : ℕ) (t : T) (i : ι) :
    ProjectedFamily h →L[ℝ] Lp (h i) 2 (volume : Measure (Vec 2)) :=
  -(((hilbertProjection (E := h i) N).comp
      ((planeCoefficientOperator (C.drift i t) (C.drift_continuous i t)
        (C.drift_bound_nonneg i) (C.drift_le i t)).comp (bandGradientOperator (E := h i) N))).comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun j => Lp (h j) 2 (volume : Measure (Vec 2))) i))

/-- Projected diffusion contribution to one row. -/
def projectedDiffusionRow (N : ℕ) (ν : ℝ) (i : ι) :
    ProjectedFamily h →L[ℝ] Lp (h i) 2 (volume : Measure (Vec 2)) :=
  (ν • bandLaplacianOperator (E := h i) N).comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun j => Lp (h j) 2 (volume : Measure (Vec 2))) i)

/-- One literal admissible differential coupling contribution. -/
def projectedEdgeRow {T : Type*} {K : ι → ℕ} {D : ℕ}
    (C : ProjectedCoefficients (h := h) T K D) (N : ℕ) (t : T) (i j : ι)
    (d : AVRegularity.admissibleOrders K D i j) :
    ProjectedFamily h →L[ℝ] Lp (h i) 2 (volume : Measure (Vec 2)) :=
  ((bandDivergenceOperator (E := h i) N).comp
    ((planeCoefficientOperator (C.coupling i j d t) (C.coupling_continuous i j d t)
      (C.coupling_bound_nonneg i j d) (C.coupling_le i j d t)).comp
        (bandTensorOperator (E := h j) N (d.1 - 1)))).comp
          (PiLp.proj (𝕜 := ℝ) 2 (fun j => Lp (h j) 2 (volume : Measure (Vec 2))) j)

/-- One row of the original projected coupled PDE, including every admissible edge. -/
def projectedRow {T : Type*} {K : ι → ℕ} {D : ℕ}
    (C : ProjectedCoefficients (h := h) T K D) (N : ℕ) (ν : ℝ) (t : T) (i : ι) :
    ProjectedFamily h →L[ℝ] Lp (h i) 2 (volume : Measure (Vec 2)) :=
  projectedDriftRow C N t i + projectedDiffusionRow (h := h) N ν i +
    ∑ j : ι, ∑ d : AVRegularity.admissibleOrders K D i j, projectedEdgeRow C N t i j d

/-- The genuine bounded operator for the simultaneous family evolution. -/
def projectedOperator {T : Type*} {K : ι → ℕ} {D : ℕ}
    (C : ProjectedCoefficients (h := h) T K D) (N : ℕ) (ν : ℝ) (t : T) :
    ProjectedFamily h →L[ℝ] ProjectedFamily h :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun i => Lp (h i) 2 (volume : Measure (Vec 2)))).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi (projectedRow C N ν t))

omit [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem projectedOperator_component {T : Type*} {K : ι → ℕ} {D : ℕ}
    (C : ProjectedCoefficients (h := h) T K D) (N : ℕ) (ν : ℝ) (t : T)
    (u : ProjectedFamily h) (i : ι) : projectedOperator C N ν t u i =
      -(hilbertProjection (E := h i) N (planeCoefficientOperator (C.drift i t) (C.drift_continuous i t)
        (C.drift_bound_nonneg i) (C.drift_le i t) (bandGradientOperator (E := h i) N (u i)))) +
      ν • bandLaplacianOperator (E := h i) N (u i) +
      ∑ j : ι, ∑ d : AVRegularity.admissibleOrders K D i j,
        bandDivergenceOperator (E := h i) N (planeCoefficientOperator (C.coupling i j d t)
          (C.coupling_continuous i j d t) (C.coupling_bound_nonneg i j d)
          (C.coupling_le i j d t) (bandTensorOperator (E := h j) N (d.1 - 1) (u j))) := by
  change projectedRow C N ν t i u = _
  simp only [projectedRow, projectedDriftRow, projectedDiffusionRow, projectedEdgeRow, ContinuousLinearMap.comp_apply, PiLp.proj_apply,
    add_apply, neg_apply, smul_apply, sum_apply]
end

/-! Cutoff-dependent bounds used solely for constructing the simultaneous evolution. -/

section
section Abstract
variable {E F G H J : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup J] [NormedSpace ℝ J]

/-- Replace only the coefficient multiplier factor in a bounded operator chain. -/
theorem norm_chain_le (P : H →L[ℝ] J) (C : G →L[ℝ] H)
    (T : F →L[ℝ] G) (R : E →L[ℝ] F) {M : ℝ} (hC : ‖C‖ ≤ M) :
    ‖(P.comp (C.comp T)).comp R‖ ≤ ‖P‖ * (M * ‖T‖) * ‖R‖ := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg R)
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg P)
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right hC (norm_nonneg T))

end Abstract

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

def projectedDriftBound {T : Type*} {K : ι → ℕ} {D : ℕ}
    (C : ProjectedCoefficients (h := h) T K D) (N : ℕ) (i : ι) : ℝ :=
  ‖hilbertProjection (E := h i) N‖ *
    (C.drift_bound i * ‖bandGradientOperator (E := h i) N‖) *
      ‖PiLp.proj (𝕜 := ℝ) 2 (fun j => Lp (h j) 2 (volume : Measure (Vec 2))) i‖

def projectedDiffusionBound (N : ℕ) (ν : ℝ) (i : ι) : ℝ :=
  ‖ν • bandLaplacianOperator (E := h i) N‖ *
    ‖PiLp.proj (𝕜 := ℝ) 2 (fun j => Lp (h j) 2 (volume : Measure (Vec 2))) i‖

def projectedEdgeBound {T : Type*} {K : ι → ℕ} {D : ℕ}
    (C : ProjectedCoefficients (h := h) T K D) (N : ℕ) (i j : ι)
    (d : AVRegularity.admissibleOrders K D i j) : ℝ :=
  ‖bandDivergenceOperator (E := h i) N‖ *
    (C.coupling_bound i j d * ‖bandTensorOperator (E := h j) N (d.1 - 1)‖) *
      ‖PiLp.proj (𝕜 := ℝ) 2 (fun j => Lp (h j) 2 (volume : Measure (Vec 2))) j‖

omit [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem projectedDriftRow_norm_le {T : Type*} {K : ι → ℕ} {D : ℕ}
    (C : ProjectedCoefficients (h := h) T K D) (N : ℕ) (t : T) (i : ι) :
    ‖projectedDriftRow C N t i‖ ≤ projectedDriftBound C N i := by
  have hn (R : ProjectedFamily h →L[ℝ] Lp (h i) 2 (volume : Measure (Vec 2))) :
      ‖-R‖ = ‖R‖ := norm_neg R
  unfold projectedDriftRow projectedDriftBound
  rw [hn]
  exact norm_chain_le _ _ _ _ (planeCoefficientOperator_norm_le _ _ _ _)

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem projectedDiffusionRow_norm_le (N : ℕ) (ν : ℝ) (i : ι) :
    ‖projectedDiffusionRow (h := h) N ν i‖ ≤ projectedDiffusionBound (h := h) N ν i :=
  ContinuousLinearMap.opNorm_comp_le _ _

omit [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem projectedEdgeRow_norm_le {T : Type*} {K : ι → ℕ} {D : ℕ}
    (C : ProjectedCoefficients (h := h) T K D) (N : ℕ) (t : T) (i j : ι)
    (d : AVRegularity.admissibleOrders K D i j) :
    ‖projectedEdgeRow C N t i j d‖ ≤ projectedEdgeBound C N i j d := by
  unfold projectedEdgeRow projectedEdgeBound
  exact norm_chain_le _ _ _ _ (planeCoefficientOperator_norm_le _ _ _ _)

/-- A fixed construction bound for one row. -/
def projectedRowBound {T : Type*} {K : ι → ℕ} {D : ℕ}
    (C : ProjectedCoefficients (h := h) T K D) (N : ℕ) (ν : ℝ) (i : ι) : ℝ :=
  projectedDriftBound C N i + projectedDiffusionBound (h := h) N ν i +
    ∑ j : ι, ∑ d : AVRegularity.admissibleOrders K D i j, projectedEdgeBound C N i j d

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem projectedRowBound_nonneg {T : Type*} {K : ι → ℕ} {D : ℕ}
    (C : ProjectedCoefficients (h := h) T K D) (N : ℕ) (ν : ℝ) (i : ι) :
    0 ≤ projectedRowBound C N ν i := by
  unfold projectedRowBound projectedDriftBound projectedDiffusionBound projectedEdgeBound
  have hd := C.drift_bound_nonneg i
  apply add_nonneg
  · positivity
  · apply Finset.sum_nonneg
    intro j _
    apply Finset.sum_nonneg
    intro d _
    have ha := C.coupling_bound_nonneg i j d
    positivity

omit [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem projectedRow_norm_le {T : Type*} {K : ι → ℕ} {D : ℕ}
    (C : ProjectedCoefficients (h := h) T K D) (N : ℕ) (ν : ℝ) (t : T) (i : ι) :
    ‖projectedRow C N ν t i‖ ≤ projectedRowBound C N ν i := by
  let R := ∑ j : ι, ∑ d : AVRegularity.admissibleOrders K D i j, projectedEdgeRow C N t i j d
  have hr : ‖R‖ ≤ ∑ j : ι, ∑ d : AVRegularity.admissibleOrders K D i j,
      projectedEdgeBound C N i j d := by
    apply (norm_sum_le Finset.univ (fun j : ι =>
      ∑ d : AVRegularity.admissibleOrders K D i j, projectedEdgeRow C N t i j d)).trans
    apply Finset.sum_le_sum
    intro j _
    apply (norm_sum_le Finset.univ
      (fun d : AVRegularity.admissibleOrders K D i j => projectedEdgeRow C N t i j d)).trans
    exact Finset.sum_le_sum (fun d _ => projectedEdgeRow_norm_le C N t i j d)
  exact (norm_add_le (projectedDriftRow C N t i + projectedDiffusionRow (h := h) N ν i) R).trans
    (add_le_add ((norm_add_le (projectedDriftRow C N t i)
      (projectedDiffusionRow (h := h) N ν i)).trans
        (add_le_add (projectedDriftRow_norm_le C N t i)
          (projectedDiffusionRow_norm_le (h := h) N ν i))) hr)

/-- A fixed finite bound on the complete simultaneous operator. -/
def projectedOperatorBound {T : Type*} {K : ι → ℕ} {D : ℕ}
    (C : ProjectedCoefficients (h := h) T K D) (N : ℕ) (ν : ℝ) : ℝ :=
  ‖(PiLp.continuousLinearEquiv 2 ℝ
    (fun i => Lp (h i) 2 (volume : Measure (Vec 2)))).symm.toContinuousLinearMap‖ *
      ∑ i : ι, projectedRowBound C N ν i

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem projectedOperatorBound_nonneg {T : Type*} {K : ι → ℕ} {D : ℕ}
    (C : ProjectedCoefficients (h := h) T K D) (N : ℕ) (ν : ℝ) :
    0 ≤ projectedOperatorBound C N ν :=
  mul_nonneg (norm_nonneg ((PiLp.continuousLinearEquiv 2 ℝ
    (fun i => Lp (h i) 2 (volume : Measure (Vec 2)))).symm.toContinuousLinearMap))
    (Finset.sum_nonneg fun i _ => projectedRowBound_nonneg C N ν i)

omit [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem projectedOperator_norm_le {T : Type*} {K : ι → ℕ} {D : ℕ}
    (C : ProjectedCoefficients (h := h) T K D) (N : ℕ) (ν : ℝ) (t : T) :
    ‖projectedOperator C N ν t‖ ≤ projectedOperatorBound C N ν := by
  unfold projectedOperator projectedOperatorBound
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply ContinuousLinearMap.opNorm_le_bound _
    (Finset.sum_nonneg fun i _ => projectedRowBound_nonneg C N ν i)
  intro u
  apply (pi_norm_le_iff_of_nonneg
    (mul_nonneg (Finset.sum_nonneg fun i _ => projectedRowBound_nonneg C N ν i)
      (norm_nonneg u))).mpr
  intro i
  exact ((projectedRow C N ν t i).le_of_opNorm_le (projectedRow_norm_le C N ν t i) u).trans
    (mul_le_mul_of_nonneg_right (Finset.single_le_sum
      (fun j _ => projectedRowBound_nonneg C N ν j) (Finset.mem_univ i)) (norm_nonneg u))
end

/-! Joint physical coefficient measurability supplies every fixed-input projected action. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem projectedOperator_stronglyMeasurable {T : Type*} [MeasurableSpace T]
    {K : ι → ℕ} {D : ℕ} (C : ProjectedCoefficients (h := h) T K D)
    (hCd : ∀ i, Measurable (Function.uncurry (C.drift i)))
    (hCa : ∀ i j d, Measurable (Function.uncurry (C.coupling i j d)))
    (N : ℕ) (ν : ℝ) (u : ProjectedFamily h) :
    StronglyMeasurable (fun t => projectedOperator C N ν t u) := by
  classical
  have hrow (i : ι) : StronglyMeasurable (fun t => projectedOperator C N ν t u i) := by
    have hd := (hilbertProjection (E := h i) N).continuous.comp_stronglyMeasurable
      (planeCoefficientOperator_stronglyMeasurable (C.drift i) (C.drift_continuous i)
        (hCd i) (C.drift_bound_nonneg i) (C.drift_le i)
        (bandGradientOperator (E := h i) N (u i)))
    have ha : StronglyMeasurable (fun t => ∑ j : ι,
        ∑ d : AVRegularity.admissibleOrders K D i j,
          bandDivergenceOperator (E := h i) N
            (planeCoefficientOperator (C.coupling i j d t) (C.coupling_continuous i j d t)
              (C.coupling_bound_nonneg i j d) (C.coupling_le i j d t)
              (bandTensorOperator (E := h j) N (d.1 - 1) (u j)))) := by
      apply Finset.stronglyMeasurable_fun_sum
      intro j _
      apply Finset.stronglyMeasurable_fun_sum
      intro d _
      exact (bandDivergenceOperator (E := h i) N).continuous.comp_stronglyMeasurable
        (planeCoefficientOperator_stronglyMeasurable (C.coupling i j d)
          (C.coupling_continuous i j d) (hCa i j d) (C.coupling_bound_nonneg i j d)
          (C.coupling_le i j d) (bandTensorOperator (E := h j) N (d.1 - 1) (u j)))
    convert (hd.neg.add (stronglyMeasurable_const
      (b := ν • bandLaplacianOperator (E := h i) N (u i)))).add ha using 1
    funext t
    exact projectedOperator_component C N ν t u i
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  let : ∀ i, SecondCountableTopology (Lp (h i) 2 (volume : Measure (Vec 2))) :=
    fun _ => Lp.SecondCountableTopology
  let : ∀ i, MeasurableSpace (Lp (h i) 2 (volume : Measure (Vec 2))) := fun _ => borel _
  let : ∀ i, BorelSpace (Lp (h i) 2 (volume : Measure (Vec 2))) := fun _ => ⟨rfl⟩
  have hpi : StronglyMeasurable (fun t => fun i => projectedOperator C N ν t u i) :=
    (Measurable.of_eval fun i => (hrow i).measurable).stronglyMeasurable
  exact (PiLp.continuousLinearEquiv 2 ℝ
    (fun i => Lp (h i) 2 (volume : Measure (Vec 2)))).symm.continuous.comp_stronglyMeasurable hpi
end

/-! The simultaneous projected PDE has its output in the actual bounded-frequency range. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]

/-- Actual Fourier projection in every component of the family. -/
def familyProjection (N : ℕ) : ProjectedFamily h →L[ℝ] ProjectedFamily h :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun i => Lp (h i) 2 (volume : Measure (Vec 2)))).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi (fun i => (hilbertProjection (E := h i) N).comp
        (PiLp.proj (𝕜 := ℝ) 2 (fun i => Lp (h i) 2 (volume : Measure (Vec 2))) i)))

omit [Fintype ι] in
@[simp] theorem familyProjection_component (N : ℕ) (u : ProjectedFamily h) (i : ι) :
    familyProjection N u i = hilbertProjection N (u i) := rfl

variable [∀ i, MeasurableSpace (h i)]

theorem familyProjection_operator {T : Type*} {K : ι → ℕ} {D : ℕ}
    (C : ProjectedCoefficients (h := h) T K D) (N : ℕ) (ν : ℝ) (t : T)
    (u : ProjectedFamily h) :
    familyProjection N (projectedOperator C N ν t u) = projectedOperator C N ν t u := by
  apply PiLp.ext
  intro i
  simp only [familyProjection_component, projectedOperator_component, map_add, map_neg,
    map_smul, map_sum, hilbertProjection_idempotent, hilbertProjection_laplacian,
    hilbertProjection_divergence]
end

end AVRegularity.CoupledEnergyPlane
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational AVRegularity.CoupledEnergyPlane.Fourier
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CoupledEnergyPlane

/-! Pointwise coercivity of the true lower-order plane Galerkin jets. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

abbrev PlaneLowerHilbert (K : ι → ℕ) :=
  PiLp 2 (fun i => JetL2 (volume.restrict Set.univ) (K i) (h i))

def lowerBandJetOperator (N : ℕ) (K : ι → ℕ) :
    ProjectedFamily h →L[ℝ] PlaneLowerHilbert (h := h) K :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun i => JetL2 (volume.restrict Set.univ) (K i) (h i))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => (bandJetOperator N (K i)).comp
      (PiLp.proj (𝕜 := ℝ) 2 (fun j => Lp (h j) 2 (volume : Measure (Vec 2))) i)))

omit [Fintype ι] in
@[simp] theorem lowerBandJetOperator_component (N : ℕ) (K : ι → ℕ)
    (u : ProjectedFamily h) (i : ι) :
    lowerBandJetOperator N K u i = (hilbertBandHk N (K i) (u i)).val := rfl

theorem lowerBandJet_normSq_le (N : ℕ) (K : ι → ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (u : ProjectedFamily h) :
    ‖lowerBandJetOperator N K u‖ ^ 2 ≤
      (∑ i, π i / factorialWeightMin ρ (K i)) *
        massNormSq ρ π (fun i => (hilbertBandHk N (K i) (u i)).val) := by
  rw [PiLp.norm_sq_eq_of_L2, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [lowerBandJetOperator_component]
  have hm := componentFactorial_le_mass ρ π hπ
    (fun j => (hilbertBandHk N (K j) (u j)).val) i
  have hl := factorialNormSq_lower ρ (hilbertBandHk N (K i) (u i)).val
  have hl' : ‖(hilbertBandHk N (K i) (u i)).val‖ ^ 2 ≤
      factorialNormSq ρ (hilbertBandHk N (K i) (u i)).val / factorialWeightMin ρ (K i) :=
    (le_div_iff₀ (factorialWeightMin_pos (K := K i) ρ hρ)).mpr (by
    simpa only [mul_comm] using hl)
  exact hl'.trans (by
    have hd := div_le_div_of_nonneg_right hm (factorialWeightMin_pos (K := K i) ρ hρ).le
    convert hd using 1
    ring)

theorem projectedFamily_norm_le_lowerBand (N : ℕ) (K : ι → ℕ)
    (u : ProjectedFamily h) (hu : familyProjection N u = u) :
    ‖u‖ ≤ ‖lowerBandJetOperator N K u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_le_sum
  intro i _
  have hp : hilbertProjection N (u i) = u i := by
    simpa only [familyProjection_component] using congrArg (fun U : ProjectedFamily h => U i) hu
  have hv : ‖u i‖ ≤ ‖(hilbertBandHk N (K i) (u i)).val‖ := by
    calc
      ‖u i‖ = ‖(hilbertBandHk N (K i) (u i)).val (valueIndex2 (K i))‖ := by
        rw [hilbertBandHk_value, planeToUniv.norm_map, hp]
      _ ≤ _ := PiLp.norm_apply_le _ _
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hv


theorem projectedFamily_norm_le_of_massBound (N : ℕ) (K : ι → ℕ)
    (ρ : ℝ) (hρ : 0 < ρ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (u : ProjectedFamily h) (hu : familyProjection N u = u) (C : ℝ)
    (hb : massNormSq ρ π (fun i => (hilbertBandHk N (K i) (u i)).val) ≤ C) :
    ‖u‖ ≤ Real.sqrt ((∑ i, π i / factorialWeightMin ρ (K i)) * C) := by
  have hQ : 0 ≤ ∑ i, π i / factorialWeightMin ρ (K i) :=
    Finset.sum_nonneg (fun i _ => div_nonneg (hπ i).le
      (factorialWeightMin_pos (K := K i) ρ hρ).le)
  exact (projectedFamily_norm_le_lowerBand N K u hu).trans
    (Real.le_sqrt_of_sq_le ((lowerBandJet_normSq_le N K ρ hρ π hπ u).trans
      (mul_le_mul_of_nonneg_left hb hQ)))

end AVRegularity.CoupledEnergyPlane
end
end
