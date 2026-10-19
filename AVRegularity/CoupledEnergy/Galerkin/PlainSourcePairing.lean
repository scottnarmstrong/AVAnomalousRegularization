-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CoupledEnergy.Variational.PullbackForm
public import AVRegularity.CoupledEnergy.Galerkin.PlainVariationalEnergy
public import AVRegularity.CoupledEnergy.Variational.ScalarTensorOperator
public import AVRegularity.CoupledEnergy.Variational.CarrierFiberCLM
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.SpecificCodomains.Pi

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
namespace AVRegularity.CoupledEnergy.Galerkin

/-! The paper's genuine L¹ value source passes through Fourier projection of
arbitrary H¹ tests. This argument does not upgrade the source to L² in time. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- Actual L¹ value forcing converges against the projected weak tests on every subinterval. -/
theorem valueForcing_projected_test_tendsto {K : ℕ} {a b t : ℝ} (hab : a ≤ b)
    (ht : t ∈ Set.Icc a b) (g : ℝ → TorusHk K E)
    (hg : Integrable g (volume.restrict (Set.Icc a b))) (φ : TorusHk 1 E) :
    Tendsto (fun N => ∫ s in a..t, ∫ x in AVenhance.unitCube,
      inner ℝ (torusHkValueCLM (g s) x) (torusHkValueCLM (galerkinProj N φ) x)) atTop
      (𝓝 (∫ s in a..t, ∫ x in AVenhance.unitCube,
        inner ℝ (torusHkValueCLM (g s) x) (torusHkValueCLM φ x))) := by
  have hgv : Integrable (fun s => torusHkValueCLM (g s)) (volume.restrict (Set.Icc a b)) :=
    (torusHkValueCLM (E := E) (K := K)).integrable_comp hg
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hgv
  have hsub : Set.uIcc a t ⊆ Set.uIcc a b := by
    rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le hab]
    exact Set.Icc_subset_Icc le_rfl ht.2
  have hproj := (torusHkValueCLM (E := E) (K := 1)).continuous.continuousAt.tendsto.comp
    (galerkinProj_tendsto φ)
  simpa only [L2.inner_def] using Variational.l1TimeTest_integral_tendsto
    (fun s => torusHkValueCLM (g s)) (hi.mono_set hsub)
    (fun N => torusHkValueCLM (galerkinProj N φ)) (torusHkValueCLM φ) hproj

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Diffusion and forcing forms on the finite coupled Fourier range.
The signs follow the variational energy form: diffusion and forcing fluxes pair negatively with
the test gradient. All trial gradients use the smooth Fourier lift. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*} {K : ι → ℕ}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

attribute [local instance] coupledRangeAddCommGroup coupledRangeModule

/-- The L² gradient in one direction of one finite-range component. -/
def coupledRangeGradient (N : ℕ) (i : ι) (k : Fin 2) :
    CoupledFourierCoordinates (ι := ι) (h := h) (K := K) N →L[ℝ]
      ComponentL2 (volume.restrict AVenhance.unitCube) (h i) :=
  (rangeSmoothDerivativeValueCLM (E := h i) (K := K i) N
    (fun _ : Fin 1 => k)).comp (ContinuousLinearMap.proj i)

/-- A source functional assembled from L² value and componentwise flux forcing. -/
def coupledRangeForcing (N : ℕ)
    (F : ∀ i, Fin 2 → ComponentL2 (volume.restrict AVenhance.unitCube) (h i))
    (g : ∀ i, ComponentL2 (volume.restrict AVenhance.unitCube) (h i)) :
    CoupledFourierCoordinates (ι := ι) (h := h) (K := K) N →ₗ[ℝ] ℝ where
  toFun y := ∑ i, (inner ℝ (g i) (torusHkValueCLM (y i).val) -
    ∑ k : Fin 2, inner ℝ (F i k) (coupledRangeGradient N i k y))
  map_add' := by
    intro y z
    simp [map_add, inner_add_right, Finset.sum_add_distrib, sub_add_sub_comm]
  map_smul' := by
    intro c y
    simp [map_smul, real_inner_smul_right, ← Finset.mul_sum, ← mul_sub]
end

/-! Entrywise measurability of the literal Fourier integral matrix. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
variable {T : Type*} [MeasurableSpace T]

omit [∀ i, CompleteSpace (h i)] in
theorem plainDriftIntegrand_measurable (N : ℕ) (v : T → Vec 2 → Vec 2)
    (hv : Measurable (Function.uncurry v))
    (r c : CoupledFourierModeIndex (h := h) N) :
    Measurable (fun p : T × Vec 2 => plainDriftIntegrand N (v p.1) r c p.2) := by
  have hm (a : CoupledFourierModeIndex (h := h) N) (i : ι) (m : ℕ)
      (w : DerivativeWord2 m) :
      Measurable (fun p : T × Vec 2 => coupledModeJet N a i m w p.2) :=
    (coupledModeJet_contDiff N a i m w).continuous.measurable.comp measurable_snd
  unfold plainDriftIntegrand
  apply Measurable.neg
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro k _
  exact ((measurable_pi_apply k).comp hv).mul
    ((hm c i 1 (fun _ => k)).inner (hm r i 0 Fin.elim0))

omit [∀ i, CompleteSpace (h i)] in
theorem plainCouplingIntegrand_measurable (N D : ℕ) (K : ι → ℕ)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), T → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, Measurable (Function.uncurry (A i i' d)))
    (r c : CoupledFourierModeIndex (h := h) N) :
    Measurable (fun p : T × Vec 2 =>
      plainCouplingIntegrand N D K (fun i i' d => A i i' d p.1) r c p.2) := by
  unfold plainCouplingIntegrand
  apply Measurable.neg
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro i' _
  apply Finset.measurable_sum
  intro d _
  apply Finset.measurable_sum
  intro k _
  have htensor : Measurable (fun p : T × Vec 2 =>
      coupledModeTensor N c i' (d.1 - 1) p.2) :=
    (coupledModeTensor_continuous N c i' (d.1 - 1)).measurable.comp measurable_snd
  have heval : Measurable (fun p : T × Vec 2 =>
      A i i' d p.1 p.2 (coupledModeTensor N c i' (d.1 - 1) p.2)) :=
    (continuous_fst.clm_apply continuous_snd).measurable.comp
      ((hA i i' d).prodMk htensor)
  have hout := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h i) k).continuous.measurable.comp heval
  exact hout.inner
    ((coupledModeJet_contDiff N r i 1 (fun _ => k)).continuous.measurable.comp measurable_snd)

omit [∀ i, CompleteSpace (h i)] in
theorem plainFourierMatrix_stronglyMeasurable (N D : ℕ) (ν : ℝ) (K : ι → ℕ)
    (v : T → Vec 2 → Vec 2) (hv : Measurable (Function.uncurry v))
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), T → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, Measurable (Function.uncurry (A i i' d)))
    (r c : CoupledFourierModeIndex (h := h) N) :
    StronglyMeasurable (fun t => ∫ x in AVenhance.unitCube,
      plainDiffusionIntegrand N ν r c x + plainDriftIntegrand N (v t) r c x +
        plainCouplingIntegrand N D K (fun i i' d => A i i' d t) r c x) := by
  have hdiff : Measurable (fun p : T × Vec 2 => plainDiffusionIntegrand N ν r c p.2) := by
    unfold plainDiffusionIntegrand
    have hm (a : CoupledFourierModeIndex (h := h) N) (i : ι) (k : Fin 2) :
        Measurable (fun p : T × Vec 2 => coupledModeJet N a i 1 (fun _ => k) p.2) :=
      (coupledModeJet_contDiff N a i 1 (fun _ => k)).continuous.measurable.comp measurable_snd
    apply Measurable.mul measurable_const
    apply Finset.measurable_sum
    intro i _
    apply Finset.measurable_sum
    intro k _
    exact (hm c i k).inner (hm r i k)
  exact ((hdiff.add (plainDriftIntegrand_measurable N v hv r c)).add
    (plainCouplingIntegrand_measurable N D K A hA r c)).stronglyMeasurable.integral_prod_right'
end

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVenhance.Infra.Parabolic.WeakUniqueness
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Spatial bounds for the fixed smooth Fourier test and trial modes. -/

/-- Continuous functions are uniformly bounded on the open unit cell via its compact closure. -/
theorem continuous_unitCube_bound {E : Type*} [NormedAddCommGroup E]
    (f : Vec 2 → E) (hf : Continuous f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ AVenhance.unitCube, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := WeakAlgebra.weakSpatialClosedCell_compact.exists_bound_of_continuousOn
    hf.continuousOn
  exact ⟨max C 0, le_max_right _ _, fun x hx =>
    (hC x (WeakAlgebra.weakUnitCube_subset_closedCell hx)).trans (le_max_left _ _)⟩

variable {ι : Type*} [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]

/-- Each fixed ordered Fourier mode derivative has a finite cell bound. -/
theorem coupledModeJet_cell_bound (N : ℕ) (a : CoupledFourierModeIndex (h := h) N)
    (i : ι) (m : ℕ) (w : DerivativeWord2 m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ AVenhance.unitCube,
      ‖coupledModeJet N a i m w x‖ ≤ C :=
  continuous_unitCube_bound _ (coupledModeJet_contDiff N a i m w).continuous

/-- Each fixed tensor trial mode has a finite cell bound. -/
theorem coupledModeTensor_cell_bound (N : ℕ) (a : CoupledFourierModeIndex (h := h) N)
    (i : ι) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ AVenhance.unitCube,
      ‖coupledModeTensor N a i m x‖ ≤ C :=
  continuous_unitCube_bound _ (coupledModeTensor_continuous N a i m)

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Pointwise identification of matrix rows with the reconstructed spatial differential form. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]

/-- Full raw tensor synthesized from the plain vector. -/
def coupledPlainRawTensor (N : ℕ) (c : CoupledPlainCoefficients (h := h) N)
    (i : ι) (m : ℕ) (x : Vec 2) : PiLp 2 (fun _ : DerivativeWord2 m => h i) :=
  WithLp.toLp 2 fun w => coupledPlainRawJet N c i m w x

/-- Tensor synthesis is the same finite sum as scalar-jet synthesis. -/
theorem coupledPlainRawTensor_eq_sum (N : ℕ) (c : CoupledPlainCoefficients (h := h) N)
    (i : ι) (m : ℕ) (x : Vec 2) :
    coupledPlainRawTensor N c i m x = ∑ a, c a • coupledModeTensor N a i m x := by
  apply PiLp.ext
  intro w
  simp [coupledPlainRawTensor, coupledPlainRawJet, coupledModeTensor]

/-- Diffusion entries tested against a coefficient vector give its synthesized gradient form. -/
theorem plainDiffusion_row_synthesis (N : ℕ) (ν : ℝ)
    (r : CoupledFourierModeIndex (h := h) N) (c : CoupledPlainCoefficients (h := h) N)
    (x : Vec 2) :
    (∑ a, c a * plainDiffusionIntegrand N ν r a x) =
      -ν * ∑ i, ∑ k : Fin 2, inner ℝ (coupledPlainRawJet N c i 1 (fun _ => k) x)
        (coupledModeJet N r i 1 (fun _ => k) x) := by
  simp only [plainDiffusionIntegrand, coupledPlainRawJet, sum_inner, real_inner_smul_left]
  simp_rw [mul_left_comm (c _) (-ν), ← mul_assoc, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  simp [mul_assoc]

/-- Drift entries give the velocity contracted with the synthesized gradient. -/
theorem plainDrift_row_synthesis (N : ℕ) (v : Vec 2 → Vec 2)
    (r : CoupledFourierModeIndex (h := h) N) (c : CoupledPlainCoefficients (h := h) N)
    (x : Vec 2) :
    (∑ a, c a * plainDriftIntegrand N v r a x) =
      -∑ i, ∑ k : Fin 2, v x k * inner ℝ (coupledPlainRawJet N c i 1 (fun _ => k) x)
        (coupledModeJet N r i 0 Fin.elim0 x) := by
  simp only [plainDriftIntegrand, coupledPlainRawJet, sum_inner, real_inner_smul_left,
    mul_neg, Finset.sum_neg_distrib]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Coupling entries give the prescribed operator applied to the reconstructed derivative tensor. -/
theorem plainCoupling_row_synthesis (N D : ℕ) (K : ι → ℕ)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (r : CoupledFourierModeIndex (h := h) N) (c : CoupledPlainCoefficients (h := h) N)
    (x : Vec 2) :
    (∑ a, c a * plainCouplingIntegrand N D K A r a x) =
      -∑ i, ∑ i', ∑ d : admissibleOrders K D i i', ∑ k : Fin 2,
        inner ℝ (A i i' d x (coupledPlainRawTensor N c i' (d.1 - 1) x) k)
          (coupledModeJet N r i 1 (fun _ => k) x) := by
  simp only [plainCouplingIntegrand, coupledPlainRawTensor_eq_sum, map_sum, map_smul,
    WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, sum_inner,
    real_inner_smul_left, mul_neg, Finset.sum_neg_distrib]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i' _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm]

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set
open scoped Topology
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Strong traces and compatible Sobolev lifts for a fixed finite coefficient path. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- All order choices in the synthesis map describe the same value and compatible jets. -/
theorem coupledPlainSynthesis_truncate (N : ℕ) (i : ι) {K L : ℕ} (hKL : K ≤ L)
    (c : CoupledPlainCoefficients (h := h) N) :
    truncateTorusHk hKL (coupledPlainSynthesis N i L c) = coupledPlainSynthesis N i K c := by
  apply TorusHk.ext_value
  apply Lp.ext
  exact (coupledPlainSynthesis_jet_ae N i L c (valueIndex2 L)).trans
    (coupledPlainSynthesis_jet_ae N i K c (valueIndex2 K)).symm

/-- Fixed finite coefficient paths synthesize to strongly continuous Sobolev paths. -/
theorem coupledPlainSynthesis_continuous (N : ℕ) (i : ι) (K : ℕ)
    {y : ℝ → CoupledPlainCoefficients (h := h) N} (hy : Continuous y) :
    Continuous (fun t => coupledPlainSynthesis N i K (y t)) :=
  (coupledPlainSynthesis N i K).continuous.comp hy

/-- At each finite stage all synthesized Sobolev orders are time L² on the compact interval. -/
theorem coupledPlainSynthesis_memLp (N : ℕ) (i : ι) (K : ℕ) (a b : ℝ)
    {y : ℝ → CoupledPlainCoefficients (h := h) N} (hy : Continuous y) :
    MemLp (fun t => coupledPlainSynthesis N i K (y t)) 2 (volume.restrict (Icc a b)) := by
  have hc := coupledPlainSynthesis_continuous N i K hy
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hc.continuousOn
  apply MemLp.of_bound ((coupledPlainSynthesis N i K).continuous.comp_aestronglyMeasurable
    hy.aestronglyMeasurable).restrict C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact hC t ht

end AVRegularity.CoupledEnergy.Galerkin
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Finite-test contraction of the complete admissible coupling sum. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]

/-- All admissible coupling rows contract with the gradient of the synthesized test. -/
theorem plainTestCoupling_inner_sum (N D : ℕ) (K : ι → ℕ)
    (z : CoupledPlainCoefficients (h := h) N)
    (S : ∀ i i', admissibleOrders K D i i' → Fin 2 → h i) (x : Vec 2) :
    (∑ r, z r * ∑ i, ∑ i', ∑ d : admissibleOrders K D i i', ∑ k : Fin 2,
      inner ℝ (S i i' d k) (coupledModeJet N r i 1 (fun _ => k) x)) =
    ∑ i, ∑ i', ∑ d : admissibleOrders K D i i', ∑ k : Fin 2,
      inner ℝ (S i i' d k) (coupledPlainRawJet N z i 1 (fun _ => k) x) := by
  simp only [coupledPlainRawJet, inner_sum, real_inner_smul_right]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i' _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm]

/-- Drift rows contract with the value of the synthesized test. -/
theorem plainTestDrift_inner_sum (N : ℕ) (z : CoupledPlainCoefficients (h := h) N)
    (v : Vec 2) (U : ∀ i, Fin 2 → h i) (x : Vec 2) :
    (∑ r, z r * ∑ i, ∑ k : Fin 2,
      v k * inner ℝ (U i k) (coupledModeJet N r i 0 Fin.elim0 x)) =
    ∑ i, ∑ k : Fin 2, v k * inner ℝ (U i k) (coupledPlainRawJet N z i 0 Fin.elim0 x) := by
  simpa only [sum_inner, real_inner_smul_left] using
    plainTestJet_inner_sum N z 0 Fin.elim0 (fun i => ∑ k : Fin 2, v k • U i k) x

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Uniform bounds for scalar Fourier integrands, before any operator construction. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]

/-- A chosen nonnegative spatial bound for one fixed mode derivative. -/
def plainJetBound (N : ℕ) (a : CoupledFourierModeIndex (h := h) N)
    (i : ι) (m : ℕ) (w : DerivativeWord2 m) : ℝ :=
  (coupledModeJet_cell_bound N a i m w).choose

omit [Fintype ι] in
theorem plainJetBound_nonneg (N : ℕ) (a : CoupledFourierModeIndex (h := h) N)
    (i : ι) (m : ℕ) (w : DerivativeWord2 m) : 0 ≤ plainJetBound N a i m w :=
  (coupledModeJet_cell_bound N a i m w).choose_spec.1

omit [Fintype ι] in
theorem plainJetBound_le (N : ℕ) (a : CoupledFourierModeIndex (h := h) N)
    (i : ι) (m : ℕ) (w : DerivativeWord2 m) (x : Vec 2) (hx : x ∈ AVenhance.unitCube) :
    ‖coupledModeJet N a i m w x‖ ≤ plainJetBound N a i m w :=
  (coupledModeJet_cell_bound N a i m w).choose_spec.2 x hx

/-- Fixed Fourier factors in a scalar drift entry. -/
def plainDriftFactor (N : ℕ) (r c : CoupledFourierModeIndex (h := h) N) : ℝ :=
  ∑ i, ∑ k : Fin 2, plainJetBound N c i 1 (fun _ => k) * plainJetBound N r i 0 Fin.elim0

theorem plainDriftIntegrand_norm_le (N : ℕ) (v : Vec 2 → Vec 2) (V : ℝ)
    (hV : 0 ≤ V) (hv : ∀ x, ‖v x‖ ≤ V)
    (r c : CoupledFourierModeIndex (h := h) N) (x : Vec 2) (hx : x ∈ AVenhance.unitCube) :
    ‖plainDriftIntegrand N v r c x‖ ≤ V * plainDriftFactor N r c := by
  unfold plainDriftIntegrand plainDriftFactor
  rw [norm_neg, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  rw [norm_mul]
  have hinner := (norm_inner_le_norm (𝕜 := ℝ) (coupledModeJet N c i 1 (fun _ => k) x)
    (coupledModeJet N r i 0 Fin.elim0 x)).trans
    (mul_le_mul (plainJetBound_le N c i 1 (fun _ => k) x hx)
      (plainJetBound_le N r i 0 Fin.elim0 x hx) (norm_nonneg _)
        (plainJetBound_nonneg N c i 1 (fun _ => k)))
  exact mul_le_mul ((norm_le_pi_norm (v x) k).trans (hv x)) hinner
    (norm_nonneg _) hV

/-- Fixed Fourier factors in a scalar diffusion entry. -/
def plainDiffusionFactor (N : ℕ) (r c : CoupledFourierModeIndex (h := h) N) : ℝ :=
  ∑ i, ∑ k : Fin 2, plainJetBound N c i 1 (fun _ => k) *
    plainJetBound N r i 1 (fun _ => k)

theorem plainDiffusionIntegrand_norm_le (N : ℕ) (ν : ℝ)
    (r c : CoupledFourierModeIndex (h := h) N) (x : Vec 2) (hx : x ∈ AVenhance.unitCube) :
    ‖plainDiffusionIntegrand N ν r c x‖ ≤ |ν| * plainDiffusionFactor N r c := by
  unfold plainDiffusionIntegrand plainDiffusionFactor
  rw [norm_mul, norm_neg, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg ν)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
    (mul_le_mul (plainJetBound_le N c i 1 (fun _ => k) x hx)
      (plainJetBound_le N r i 1 (fun _ => k) x hx) (norm_nonneg _)
        (plainJetBound_nonneg N c i 1 (fun _ => k)))

/-- A chosen nonnegative bound for an ordered tensor mode. -/
def plainTensorBound (N : ℕ) (a : CoupledFourierModeIndex (h := h) N)
    (i : ι) (m : ℕ) : ℝ := (coupledModeTensor_cell_bound N a i m).choose

omit [Fintype ι] in
theorem plainTensorBound_nonneg (N : ℕ) (a : CoupledFourierModeIndex (h := h) N)
    (i : ι) (m : ℕ) : 0 ≤ plainTensorBound N a i m :=
  (coupledModeTensor_cell_bound N a i m).choose_spec.1

omit [Fintype ι] in
theorem plainTensorBound_le (N : ℕ) (a : CoupledFourierModeIndex (h := h) N)
    (i : ι) (m : ℕ) (x : Vec 2) (hx : x ∈ AVenhance.unitCube) :
    ‖coupledModeTensor N a i m x‖ ≤ plainTensorBound N a i m :=
  (coupledModeTensor_cell_bound N a i m).choose_spec.2 x hx

/-- Fourier factors multiplied by individual coupling coefficient bounds. -/
def plainCouplingFactor (N D : ℕ) (K : ι → ℕ)
    (B : ∀ i i', admissibleOrders K D i i' → ℝ)
    (r c : CoupledFourierModeIndex (h := h) N) : ℝ :=
  ∑ i, ∑ i', ∑ d : admissibleOrders K D i i', ∑ k : Fin 2,
    (B i i' d * plainTensorBound N c i' (d.1 - 1)) *
      plainJetBound N r i 1 (fun _ => k)

theorem plainCouplingIntegrand_norm_le (N D : ℕ) (K : ι → ℕ)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (B : ∀ i i', admissibleOrders K D i i' → ℝ)
    (hB : ∀ i i' d, 0 ≤ B i i' d)
    (hA : ∀ i i' d x, ‖A i i' d x‖ ≤ B i i' d)
    (r c : CoupledFourierModeIndex (h := h) N) (x : Vec 2) (hx : x ∈ AVenhance.unitCube) :
    ‖plainCouplingIntegrand N D K A r c x‖ ≤ plainCouplingFactor N D K B r c := by
  unfold plainCouplingIntegrand plainCouplingFactor
  rw [norm_neg]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i' _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro d _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  have heval : ‖A i i' d x (coupledModeTensor N c i' (d.1 - 1) x) k‖ ≤
      B i i' d * plainTensorBound N c i' (d.1 - 1) :=
    (PiLp.norm_apply_le _ k).trans (((A i i' d x).le_opNorm _).trans
      (mul_le_mul (hA i i' d x) (plainTensorBound_le N c i' (d.1 - 1) x hx)
        (norm_nonneg _) (hB i i' d)))
  exact (norm_inner_le_norm (𝕜 := ℝ) _ _).trans
    (mul_le_mul heval (plainJetBound_le N r i 1 (fun _ => k) x hx) (norm_nonneg _)
      (mul_nonneg (hB i i' d) (plainTensorBound_nonneg N c i' (d.1 - 1))))
end

/-! The concrete weak operator and source for the coupled PDE. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*} {K : ι → ℕ}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

attribute [local instance] coupledRangeAddCommGroup coupledRangeModule

/-- Directional projection of the flux forcing at Sobolev order zero. -/
def forcingFluxValue (i : ι) (k : Fin 2) :
    TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)) →L[ℝ]
      ComponentL2 (volume.restrict AVenhance.unitCube) (h i) :=
  ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h i) k).compLpL
    2 (volume.restrict AVenhance.unitCube)).comp (torusHkValueCLM (K := K i))

/-- The flux and value forcing of the coupled PDE on the finite test space. -/
def projectedSource (N : ℕ)
    (F : ∀ i, TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, TorusHk (K i) (h i)) :
    CoupledFourierCoordinates (ι := ι) (h := h) (K := K) N →ₗ[ℝ] ℝ :=
  coupledRangeForcing N (fun i k => forcingFluxValue (K := K) i k (F i))
    (fun i => torusHkValueCLM (g i))
end

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Actual L² flux forcing passes through strongly converging projected H¹
test gradients on every closed-time subinterval. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The original flux source converges against the Fourier-projected weak-test gradient. -/
theorem fluxForcing_projected_test_tendsto {K : ℕ} {a b t : ℝ} (hab : a ≤ b)
    (ht : t ∈ Set.Icc a b) (F : ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => E)))
    (hF : MemLp F 2 (volume.restrict (Set.Icc a b))) (φ : TorusHk 1 E) :
    Tendsto (fun N => ∫ s in a..t, ∫ x in AVenhance.unitCube,
      inner ℝ (torusHkValueCLM (F s) x) (torusH1GradientL2CLM (E := E) (galerkinProj N φ) x)) atTop
      (𝓝 (∫ s in a..t, ∫ x in AVenhance.unitCube,
        inner ℝ (torusHkValueCLM (F s) x) (torusH1GradientL2CLM (E := E) φ x))) := by
  have hfv : Integrable (fun s => torusHkValueCLM (F s)) (volume.restrict (Set.Icc a b)) :=
    (torusHkValueCLM (E := PiLp 2 (fun _ : Fin 2 => E)) (K := K)).integrable_comp
      (hF.integrable (by norm_num))
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hfv
  have hsub : Set.uIcc a t ⊆ Set.uIcc a b := by
    rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le hab]
    exact Set.Icc_subset_Icc le_rfl ht.2
  simpa only [L2.inner_def] using l1TimeTest_integral_tendsto
    (fun s => torusHkValueCLM (F s)) (hi.mono_set hsub)
    (fun N => torusH1GradientL2CLM (E := E) (galerkinProj N φ)) (torusH1GradientL2CLM (E := E) φ)
    (torusH1Gradient_projected_tendsto φ)

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVenhance.Infra.Parabolic.WeakUniqueness
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Scalar entry bounds for the explicit Fourier matrix. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]

/-- A cell integral bound expressed solely in scalar Fourier factors. -/
def plainFourierEntryBound (N D : ℕ) (ν V : ℝ) (K : ι → ℕ)
    (B : ∀ i i', admissibleOrders K D i i' → ℝ)
    (r c : CoupledFourierModeIndex (h := h) N) : ℝ :=
  (|ν| * plainDiffusionFactor N r c + V * plainDriftFactor N r c +
    plainCouplingFactor N D K B r c) * volume.real AVenhance.unitCube

theorem plainFourierEntryBound_nonneg (N D : ℕ) (ν V : ℝ) (hV : 0 ≤ V) (K : ι → ℕ)
    (B : ∀ i i', admissibleOrders K D i i' → ℝ) (hB : ∀ i i' d, 0 ≤ B i i' d)
    (r c : CoupledFourierModeIndex (h := h) N) :
    0 ≤ plainFourierEntryBound N D ν V K B r c := by
  have hd : 0 ≤ plainDiffusionFactor N r c :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ =>
      mul_nonneg (plainJetBound_nonneg N c i 1 (fun _ => k))
        (plainJetBound_nonneg N r i 1 (fun _ => k))
  have hv : 0 ≤ plainDriftFactor N r c :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ =>
      mul_nonneg (plainJetBound_nonneg N c i 1 (fun _ => k))
        (plainJetBound_nonneg N r i 0 Fin.elim0)
  have ha : 0 ≤ plainCouplingFactor N D K B r c :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun i' _ =>
      Finset.sum_nonneg fun d _ => Finset.sum_nonneg fun k _ =>
        mul_nonneg (mul_nonneg (hB i i' d) (plainTensorBound_nonneg N c i' (d.1 - 1)))
          (plainJetBound_nonneg N r i 1 (fun _ => k))
  unfold plainFourierEntryBound
  positivity

theorem plainFourierMatrix_entry_bound (N D : ℕ) (ν V : ℝ) (hV : 0 ≤ V) (K : ι → ℕ)
    (v : ℝ → Vec 2 → Vec 2) (hv : ∀ t x, ‖v t x‖ ≤ V)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (B : ∀ i i', admissibleOrders K D i i' → ℝ)
    (hB : ∀ i i' d, 0 ≤ B i i' d) (hA : ∀ i i' d t x, ‖A i i' d t x‖ ≤ B i i' d)
    (t : ℝ) (r c : CoupledFourierModeIndex (h := h) N) :
    |plainFourierMatrix N D ν K v A t r c| ≤ plainFourierEntryBound N D ν V K B r c := by
  let : IsFiniteMeasure (volume.restrict AVenhance.unitCube) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using WeakAlgebra.weak_unitCube_volume_lt_top⟩
  have hb : ∀ᵐ x ∂volume.restrict AVenhance.unitCube,
      ‖plainDiffusionIntegrand N ν r c x + plainDriftIntegrand N (v t) r c x +
        plainCouplingIntegrand N D K (fun i i' d => A i i' d t) r c x‖ ≤
      |ν| * plainDiffusionFactor N r c + V * plainDriftFactor N r c +
        plainCouplingFactor N D K B r c := by
    filter_upwards [ae_restrict_mem AVenhance.Infra.Parabolic.FourierGalerkin.TestDensityBridge.bridge_unitCube_measurable] with x hx
    exact (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add (plainDiffusionIntegrand_norm_le N ν r c x hx)
        (plainDriftIntegrand_norm_le N (v t) V hV (hv t) r c x hx)))
      (plainCouplingIntegrand_norm_le N D K (fun i i' d => A i i' d t) B hB
        (fun i i' d => hA i i' d t) r c x hx))
  simpa only [plainFourierMatrix, plainFourierEntryBound, Real.norm_eq_abs,
    measureReal_def, Measure.restrict_apply_univ] using norm_integral_le_of_norm_le_const hb
end

/-! Scalar matrix action as the spatial variational form of the synthesized field. -/

section
/-- Every continuous scalar spatial form of finite modes is integrable over the cell. -/
theorem continuous_cell_integrable (f : Vec 2 → ℝ) (hf : Continuous f) :
    Integrable f (volume.restrict AVenhance.unitCube) := by
  let : IsFiniteMeasure (volume.restrict AVenhance.unitCube) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using WeakAlgebra.weak_unitCube_volume_lt_top⟩
  obtain ⟨C, _, hC⟩ := continuous_unitCube_bound f hf
  have hmem : MemLp f 2 (volume.restrict AVenhance.unitCube) := by
    apply MemLp.of_bound hf.aestronglyMeasurable.restrict C
    filter_upwards [ae_restrict_mem
      AVenhance.Infra.Parabolic.FourierGalerkin.TestDensityBridge.bridge_unitCube_measurable]
      with x hx
    exact hC x hx
  exact hmem.integrable (by norm_num)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]

/-- The actual differential form tested against one retained mode. -/
def plainSpatialRowIntegrand (N D : ℕ) (ν : ℝ) (K : ι → ℕ)
    (v : Vec 2 → Vec 2)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (r : CoupledFourierModeIndex (h := h) N) (c : CoupledPlainCoefficients (h := h) N)
    (x : Vec 2) : ℝ :=
  (-ν * ∑ i, ∑ k : Fin 2, inner ℝ (coupledPlainRawJet N c i 1 (fun _ => k) x)
      (coupledModeJet N r i 1 (fun _ => k) x)) +
  (-∑ i, ∑ k : Fin 2, v x k * inner ℝ (coupledPlainRawJet N c i 1 (fun _ => k) x)
      (coupledModeJet N r i 0 Fin.elim0 x)) +
  (-∑ i, ∑ i', ∑ d : admissibleOrders K D i i', ∑ k : Fin 2,
    inner ℝ (A i i' d x (coupledPlainRawTensor N c i' (d.1 - 1) x) k)
      (coupledModeJet N r i 1 (fun _ => k) x))

/-- Pointwise reconstruction of the full Fourier differential row. -/
theorem plainSpatialRowIntegrand_eq_sum (N D : ℕ) (ν : ℝ) (K : ι → ℕ)
    (v : Vec 2 → Vec 2)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (r : CoupledFourierModeIndex (h := h) N) (c : CoupledPlainCoefficients (h := h) N)
    (x : Vec 2) :
    plainSpatialRowIntegrand N D ν K v A r c x =
      ∑ a, c a * (plainDiffusionIntegrand N ν r a x + plainDriftIntegrand N v r a x +
        plainCouplingIntegrand N D K A r a x) := by
  simp only [mul_add, Finset.sum_add_distrib, plainDiffusion_row_synthesis,
    plainDrift_row_synthesis, plainCoupling_row_synthesis, plainSpatialRowIntegrand]

/-- Smooth spatial data make each Fourier matrix entry integrable before the time ODE is used. -/
theorem plainFourierIntegrand_integrable (N D : ℕ) (ν : ℝ) (K : ι → ℕ)
    (v : Vec 2 → Vec 2) (hv : Continuous v)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, Continuous (A i i' d))
    (r c : CoupledFourierModeIndex (h := h) N) :
    Integrable (fun x => plainDiffusionIntegrand N ν r c x + plainDriftIntegrand N v r c x +
      plainCouplingIntegrand N D K A r c x) (volume.restrict AVenhance.unitCube) := by
  apply continuous_cell_integrable
  have hm : ∀ i m w, Continuous (coupledModeJet N c i m w) :=
    fun i m w => (coupledModeJet_contDiff N c i m w).continuous
  have hr : ∀ i m w, Continuous (coupledModeJet N r i m w) :=
    fun i m w => (coupledModeJet_contDiff N r i m w).continuous
  have ht : ∀ i m, Continuous (coupledModeTensor N c i m) :=
    fun i m => coupledModeTensor_continuous N c i m
  unfold plainDiffusionIntegrand plainDriftIntegrand plainCouplingIntegrand
  fun_prop

/-- The matrix acting on coefficients is the literal spatial integral for the synthesized field. -/
theorem plainFourierMatrix_action_eq_spatial_integral (N D : ℕ) (ν : ℝ) (K : ι → ℕ)
    (v : ℝ → Vec 2 → Vec 2)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (t : ℝ) (hv : Continuous (v t)) (hA : ∀ i i' d, Continuous (A i i' d t))
    (r : CoupledFourierModeIndex (h := h) N) (c : CoupledPlainCoefficients (h := h) N) :
    (∑ a, plainFourierMatrix N D ν K v A t r a * c a) =
      ∫ x in AVenhance.unitCube,
        plainSpatialRowIntegrand N D ν K (v t) (fun i i' d => A i i' d t) r c x := by
  simp_rw [plainFourierMatrix, ← integral_mul_const]
  rw [← integral_finsetSum Finset.univ (fun a _ =>
    (plainFourierIntegrand_integrable N D ν K (v t) hv (fun i i' d => A i i' d t) hA r a).mul_const (c a))]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [plainSpatialRowIntegrand_eq_sum]
  exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)
end

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Explicit vanishing budgets for the Fourier-tail representative:
initial tails, L¹ value-source tails, and flux tails against time L² jets. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def torusSourceTailMajorant {K : ℕ} (N : ℕ) (R : ℝ)
    (H : ℝ → TorusHk K E) (S : ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => E)))
    (w : ℝ → TorusHk (K + 1) E) (t : ℝ) : ℝ :=
  4 * R * ‖galerkinProj N (H t) - H t‖ + 4 * ∑ k : Fin 2,
    ‖galerkinProj N (mapTorusHk (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k) (S t)) -
      mapTorusHk (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k) (S t)‖ * ‖w t‖

def torusSourceTailBudget {K : ℕ} (N : ℕ) (a b R : ℝ) (f : TorusHk K E)
    (H : ℝ → TorusHk K E) (S : ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => E)))
    (w : ℝ → TorusHk (K + 1) E) : ℝ :=
  2 * ‖galerkinProj N f - f‖ ^ 2 + ∫ t in Set.Icc a b, torusSourceTailMajorant N R H S w t

theorem torusSourceTailMajorant_integrable {K : ℕ} (N : ℕ) (a b R : ℝ)
    (H : ℝ → TorusHk K E) (S : ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => E)))
    (w : ℝ → TorusHk (K + 1) E)
    (hH : Integrable H (volume.restrict (Set.Icc a b)))
    (hS : MemLp S 2 (volume.restrict (Set.Icc a b)))
    (hw : MemLp w 2 (volume.restrict (Set.Icc a b))) :
    Integrable (torusSourceTailMajorant N R H S w) (volume.restrict (Set.Icc a b)) := by
  have hi := ((galerkinProj N).integrable_comp hH).sub hH |>.norm.const_mul (4 * R)
  have hs := integrable_finsetSum Finset.univ (fun k _ =>
    galerkinProj_time_tail_product_integrable K a b N
      (fun t => mapTorusHk (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k) (S t))
      (mapTorusHk_memLp _ K _ S hS) w hw)
  simpa only [torusSourceTailMajorant, Pi.add_apply, Pi.sub_apply] using! hi.add (hs.const_mul 4)

theorem torusSourceTailBudget_tendsto {K : ℕ} (a b R : ℝ) (f : TorusHk K E)
    (H : ℝ → TorusHk K E) (S : ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => E)))
    (w : ℝ → TorusHk (K + 1) E)
    (hH : Integrable H (volume.restrict (Set.Icc a b)))
    (hS : MemLp S 2 (volume.restrict (Set.Icc a b)))
    (hw : MemLp w 2 (volume.restrict (Set.Icc a b))) :
    Tendsto (fun N => torusSourceTailBudget N a b R f H S w) atTop (𝓝 0) := by
  have hf : Tendsto (fun N => 2 * ‖galerkinProj N f - f‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    have hh := (((galerkinProj_tendsto f).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => f) atTop (𝓝 f))).norm.pow 2).const_mul 2
    simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] using hh
  have hh := (galerkinProj_time_L1_tendsto K a b H hH).const_mul (4 * R)
  have hk (k : Fin 2) := galerkinProj_time_tail_product_tendsto K a b
    (fun t => mapTorusHk (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k) (S t))
    (mapTorusHk_memLp _ K _ S hS) w hw
  have hsum := (tendsto_finsetSum Finset.univ (fun k _ => hk k)).const_mul 4
  have hlim := hf.add (hh.add hsum)
  have he (N : ℕ) : torusSourceTailBudget N a b R f H S w =
      2 * ‖galerkinProj N f - f‖ ^ 2 +
        (4 * R * (∫ t in Set.Icc a b, ‖galerkinProj N (H t) - H t‖) +
          4 * ∑ k : Fin 2, ∫ t in Set.Icc a b,
            ‖galerkinProj N (mapTorusHk (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k) (S t)) -
              mapTorusHk (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k) (S t)‖ * ‖w t‖) := by
    have hi := ((galerkinProj N).integrable_comp hH).sub hH |>.norm.const_mul (4 * R)
    have hki := fun k => galerkinProj_time_tail_product_integrable K a b N
      (fun t => mapTorusHk (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) k) (S t))
      (mapTorusHk_memLp _ K _ S hS) w hw
    simp only [Pi.sub_apply] at hi
    unfold torusSourceTailBudget torusSourceTailMajorant
    rw [integral_add hi ((integrable_finsetSum Finset.univ (fun k _ => hki k)).const_mul 4),
      integral_const_mul, integral_const_mul, integral_finsetSum Finset.univ (fun k _ => hki k)]
  simp only [Finset.sum_const_zero, mul_zero, add_zero] at hlim
  exact hlim.congr (fun N => (he N).symm)

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Integrable scalar forcing coordinates from the L² flux and L¹ value data. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The fixed cell L² class of one mode derivative. -/
def plainModeCellLp (N : ℕ) (r : CoupledFourierModeIndex (h := h) N)
    (i : ι) (m : ℕ) (w : DerivativeWord2 m) :
    ComponentL2 (volume.restrict AVenhance.unitCube) (h i) :=
  (coupledModeJet_memLp N r i m w).toLp (coupledModeJet N r i m w)

/-- Pair the value forcing with a fixed Fourier test mode. -/
def plainValueForcingCLM (N : ℕ) (r : CoupledFourierModeIndex (h := h) N)
    (i : ι) (K₀ : ℕ) : TorusHk K₀ (h i) →L[ℝ] ℝ :=
  (InnerProductSpace.toDual ℝ _ (plainModeCellLp N r i 0 Fin.elim0)).comp torusHkValueCLM

/-- Pair the flux forcing with the gradient of a fixed Fourier test mode. -/
def plainFluxForcingCLM (N : ℕ) (r : CoupledFourierModeIndex (h := h) N)
    (i : ι) (K₀ : ℕ) : TorusHk K₀ (PiLp 2 (fun _ : Fin 2 => h i)) →L[ℝ] ℝ :=
  ∑ k : Fin 2, (InnerProductSpace.toDual ℝ _ (plainModeCellLp N r i 1 (fun _ => k))).comp
    (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h i) k).compLpL
      2 (volume.restrict AVenhance.unitCube)).comp torusHkValueCLM)

/-- The source in plain coefficient coordinates; no mass inversion is involved. -/
def plainSourceCoefficients (N : ℕ) (K : ι → ℕ)
    (F : ∀ i, TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, TorusHk (K i) (h i)) : CoupledPlainCoefficients (h := h) N :=
  fun r => ∑ i, (plainValueForcingCLM N r i (K i) (g i) -
    plainFluxForcingCLM N r i (K i) (F i))

/-- The forcing assumptions imply integrability of the finite coefficient vector. -/
theorem plainSourceCoefficients_integrable (N : ℕ) (K : ι → ℕ) (a b : ℝ)
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b))) :
    Integrable (fun t => plainSourceCoefficients N K (fun i => F i t) (fun i => g i t))
      (volume.restrict (Set.Icc a b)) := by
  apply integrable_pi_iff.mpr
  intro r
  exact integrable_finsetSum _ fun i _ =>
    ((plainValueForcingCLM N r i (K i)).integrable_comp (hg i)).sub
      ((plainFluxForcingCLM N r i (K i)).integrable_comp ((hF i).integrable (by norm_num)))
end

/-! The continuous forcing observables are literal cell Fourier integrals. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [Fintype ι] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem plainModeCellLp_ae (N : ℕ) (r : CoupledFourierModeIndex (h := h) N)
    (i : ι) (m : ℕ) (w : DerivativeWord2 m) :
    plainModeCellLp N r i m w =ᵐ[volume.restrict AVenhance.unitCube]
      coupledModeJet N r i m w :=
  (coupledModeJet_memLp N r i m w).coeFn_toLp

omit [Fintype ι] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- Pairing a cell L² class with a mode reads its explicit Fourier representative. -/
theorem plainModeCellLp_inner_eq_integral (N : ℕ)
    (r : CoupledFourierModeIndex (h := h) N) (i : ι) (m : ℕ) (w : DerivativeWord2 m)
    (u : ComponentL2 (volume.restrict AVenhance.unitCube) (h i)) :
    inner ℝ (plainModeCellLp N r i m w) u =
      ∫ x in AVenhance.unitCube, inner ℝ (u x) (coupledModeJet N r i m w x) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [plainModeCellLp_ae N r i m w] with x hx
  rw [hx, real_inner_comm]

omit [Fintype ι] in
theorem plainValueForcingCLM_eq_integral (N : ℕ)
    (r : CoupledFourierModeIndex (h := h) N) (i : ι) (K₀ : ℕ) (g : TorusHk K₀ (h i)) :
    plainValueForcingCLM N r i K₀ g =
      ∫ x in AVenhance.unitCube, inner ℝ ((torusHkValueCLM g) x)
        (coupledModeJet N r i 0 Fin.elim0 x) := by
  exact plainModeCellLp_inner_eq_integral N r i 0 Fin.elim0 (torusHkValueCLM g)

omit [Fintype ι] in
theorem plainFluxForcingCLM_eq_integrals (N : ℕ)
    (r : CoupledFourierModeIndex (h := h) N) (i : ι) (K₀ : ℕ)
    (F : TorusHk K₀ (PiLp 2 (fun _ : Fin 2 => h i))) :
    plainFluxForcingCLM N r i K₀ F =
      ∑ k : Fin 2, ∫ x in AVenhance.unitCube,
        inner ℝ ((((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h i) k).compLpL
          2 (volume.restrict AVenhance.unitCube)) (torusHkValueCLM F)) x)
            (coupledModeJet N r i 1 (fun _ => k) x) := by
  simp only [plainFluxForcingCLM, sum_apply, ContinuousLinearMap.comp_apply,
    InnerProductSpace.toDual_apply_apply]
  apply Finset.sum_congr rfl
  intro k _
  exact plainModeCellLp_inner_eq_integral N r i 1 (fun _ => k) _
end

/-! Finite source testing is the literal value and flux Hilbert pairing with the synthesized test. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [Fintype ι] in
/-- A mode reads its fixed L² class at every ordered derivative. -/
theorem coupledModeHk_jet_eq_plainCellLp (N : ℕ) (r : CoupledFourierModeIndex (h := h) N)
    (i : ι) (K : ℕ) (a : JetIndex2 K) :
    (coupledModeHk N r i K).val a = plainModeCellLp N r i a.1.val a.2 := rfl

/-- Synthesized tests are explicit mode sums at every Hilbert jet coordinate. -/
theorem coupledPlainSynthesis_jet_eq_sum_modes (N : ℕ) (c : CoupledPlainCoefficients (h := h) N)
    (i : ι) (K : ℕ) (a : JetIndex2 K) :
    (coupledPlainSynthesis N i K c).val a =
      ∑ r, c r • plainModeCellLp N r i a.1.val a.2 := by
  simp [coupledPlainSynthesis, coupledModeHk_jet_eq_plainCellLp]

/-- The forcing vector tested against finite coefficients is its exact weak spatial pairing. -/
theorem plainSourceCoefficients_pairing (N : ℕ) (K : ι → ℕ)
    (F : ∀ i, TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, TorusHk (K i) (h i)) (z : CoupledPlainCoefficients (h := h) N) :
    (∑ r, plainSourceCoefficients N K F g r * z r) =
      (∑ i, inner ℝ ((g i).val (valueIndex2 (K i)))
        ((coupledPlainSynthesis N i 1 z).val (valueIndex2 1))) -
      ∑ i, ∑ k : Fin 2, inner ℝ
        (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h i) k).compLpL
          2 (volume.restrict AVenhance.unitCube)) ((F i).val (valueIndex2 (K i))))
        ((coupledPlainSynthesis N i 1 z).val ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩) := by
  simp only [plainSourceCoefficients, plainValueForcingCLM, plainFluxForcingCLM,
    ContinuousLinearMap.comp_apply, sum_apply, InnerProductSpace.toDual_apply_apply,
    coupledPlainSynthesis_jet_eq_sum_modes, inner_sum, real_inner_smul_right,
    Finset.sum_sub_distrib, sub_mul, Finset.sum_mul]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro r _
    rw [real_inner_comm]
    exact mul_comm _ _
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro r _
    rw [real_inner_comm]
    exact mul_comm _ _

/-- Changing the synthesis order leaves its value class unchanged. -/
theorem coupledPlainSynthesis_value_order_independent (N : ℕ) (i : ι) (L M : ℕ)
    (c : CoupledPlainCoefficients (h := h) N) :
    (coupledPlainSynthesis N i L c).val (valueIndex2 L) =
      (coupledPlainSynthesis N i M c).val (valueIndex2 M) := by
  apply Lp.ext
  exact (coupledPlainSynthesis_jet_ae N i L c (valueIndex2 L)).trans
    (coupledPlainSynthesis_jet_ae N i M c (valueIndex2 M)).symm
end

end AVRegularity.CoupledEnergy.Galerkin
end
