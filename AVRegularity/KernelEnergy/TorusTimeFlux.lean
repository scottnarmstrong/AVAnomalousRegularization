-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.KernelEnergy.TorusMultiplierTime
import AVRegularity.CoupledEnergy.Variational.MassWeightedCarrierCLM
import AVRegularity.CoupledEnergy.Variational.TorusCoefficientCarrierMeasurable
public import AVRegularity.CoupledEnergy.Variational.TorusRawSpatialForm
public import AVRegularity.CoupledEnergy.Galerkin.IntervalCoefficientSub
public import AVRegularity.CoupledEnergy.Galerkin.PlainHigherSynthesis
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.KernelEnergy

/-! Canonical higher kernel inputs, their linearity, and measurable switching.
The lift supplies regularity; Fourier reconstruction supplies
measurability from the value class. -/

variable {G H : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H] [CompleteSpace H]
variable (ρ : ℝ) (k D : ℕ) (hD : 2 ≤ D) (a b : ℝ) (c : ℕ → ℝ) (r : ℝ)
  (C : H →L[ℝ] G)
  (S : ℝ → (Lp G 2 (volume.restrict AVenhance.unitCube)) →L[ℝ]
    Lp G 2 (volume.restrict AVenhance.unitCube))
  (hS : IsSpatialRegularizerTorus ρ k D a b c r S)

theorem torusRegularizedInput_time_stronglyMeasurable
    (V : Set.Icc a b → TorusHk (k + 1) H) (hV : StronglyMeasurable V) :
    StronglyMeasurable (fun t : Set.Icc a b =>
      torusRegularizedInput ρ k D hD a b c r C S hS t t.property (V t)) := by
  have hv := ((C.compLpL 2 (volume.restrict AVenhance.unitCube)).comp
    (AVRegularity.CoupledEnergy.Galerkin.torusHkValueCLM (K := k + 1))).continuous.comp_stronglyMeasurable hV
  have hs := timeOperator_stronglyMeasurable (fun t : Set.Icc a b => S t)
    (fun z => hS.1 z) _ hv
  apply torusCarrier_stronglyMeasurable_of_value (k + D - 1)
  have he : (fun t : Set.Icc a b => S t (C.compLp (AVRegularity.CoupledEnergy.Galerkin.torusHkValueCLM (V t)))) =
      (fun t : Set.Icc a b => AVRegularity.CoupledEnergy.Galerkin.torusHkValueCLM
        (torusRegularizedInput ρ k D hD a b c r C S hS t t.property (V t))) := by
    funext t
    exact (torusRegularizedInput_value ρ k D hD a b c r C S hS t t.property (V t)).symm
  change StronglyMeasurable (fun t : Set.Icc a b => S t
    (C.compLp (AVRegularity.CoupledEnergy.Galerkin.torusHkValueCLM (V t)))) at hs
  rwa [he] at hs

end AVRegularity.KernelEnergy
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.KernelEnergy

/-! Measurable switching of the kernel flux terms. -/

local instance torusTimeFluxTorusNormed {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedAddCommGroup (TorusHk K E) := inferInstance
local instance torusTimeFluxTorusInner {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    InnerProductSpace ℝ (TorusHk K E) := inferInstance
local instance torusTimeFluxTorusSpace {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedSpace ℝ (TorusHk K E) := inferInstance

theorem torusKernelFluxTerm_time_stronglyMeasurable {G H : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    [MeasurableSpace H] [BorelSpace H] [CompleteSpace H]
    {K m r : ℕ} (hr : r = m + 1) (ρ : ℝ) (hρ : 0 < ρ)
    (a b : ℝ)
    (A : ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 r => G)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => H)))
    (hA : coefficientSeminorm ρ K a b A ≠ ⊤)
    (hm : Measurable (fun p : Set.Icc a b × Vec 2 => A p.1 p.2))
    (hC : ∀ t ∈ Set.Icc a b, ContDiff ℝ (K : ℕ) (A t))
    (hp : ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (A t))
    (Y : Set.Icc a b → TorusHk (K + (m + 1)) G) (hY : StronglyMeasurable Y) :
    StronglyMeasurable (fun t : Set.Icc a b =>
      torusKernelFluxTerm hr ρ hρ a b A hA t t.property (hC t t.property) (hp t t.property) (Y t)) := by
  let e : DerivativeWord2 (m + 1) ≃ DerivativeWord2 r :=
    Equiv.cast (congrArg DerivativeWord2 hr.symm)
  let L := derivativeWordArrayIsometry (E := G) e
  have htensor := (torusKernelDerivativeTensorCLM (E := G) K (m + 1)).continuous.comp_stronglyMeasurable hY
  have hmap := (AVRegularity.CoupledEnergy.Variational.mapTorusHkCLM K
    L.toContinuousLinearMap).continuous.comp_stronglyMeasurable htensor
  have hout := torusMultiplier_time_stronglyMeasurable ρ hρ
    (fun t : Set.Icc a b => A t) hm (fun t => hC t t.property) (fun t => hp t t.property)
    (fun l : Fin (K + 1) => (coefficientOrderSup a b A l.val).toReal)
    (fun t l x => coefficientOrderSup_derivative_bound ρ hρ K a b A hA l.val
      (Nat.le_of_lt_succ l.isLt) t t.property x) _ hmap
  simpa only [torusKernelDerivativeTensorCLM_apply, kernelMapTorusHkCLM_apply,
    torusKernelFluxTerm, e, L] using! hout

end AVRegularity.KernelEnergy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.KernelEnergy

/-! Canonical higher kernel inputs, their linearity, and measurable switching.
The lift supplies regularity; Fourier reconstruction supplies
measurability from the value class. -/

section
attribute [local instance] torusTimeFluxTorusNormed torusTimeFluxTorusInner torusTimeFluxTorusSpace
variable {G H : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H] [CompleteSpace H]
variable (ρ : ℝ) (k D : ℕ) (hD : 2 ≤ D) (a b : ℝ) (c : ℕ → ℝ) (r : ℝ)
  (C : H →L[ℝ] G)
  (S : ℝ → (Lp G 2 (volume.restrict AVenhance.unitCube)) →L[ℝ]
    Lp G 2 (volume.restrict AVenhance.unitCube))
  (hS : IsSpatialRegularizerTorus ρ k D a b c r S)

def torusRegularizedInputNormBudget : ℝ :=
  Real.sqrt (((k + (D - 2) + 2 : ℕ) : ℝ) * regularizerGainBudget c r D *
    (‖C‖ ^ 2 * factorialWeightMax ρ k) / factorialWeightMin ρ k)

theorem torusRegularizedInput_norm_bound (hρ : 0 < ρ)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (V : TorusHk (k + 1) H) :
    ‖torusRegularizedInput ρ k D hD a b c r C S hS t ht V‖ ≤
      torusRegularizedInputNormBudget ρ k D c r C * ‖V‖ := by
  have hm : 0 ≤ factorialWeightMax ρ k :=
    (factorialWeight_nonneg ρ 0).trans (factorialWeight_le_max ρ (0 : Fin (k + 1)))
  have hgain := regularizerGainBudget_nonneg c r D
  have hmin := (factorialWeightMin_pos ρ hρ (K := k)).le
  have hB : 0 ≤ ((k + (D - 2) + 2 : ℕ) : ℝ) * regularizerGainBudget c r D *
      (‖C‖ ^ 2 * factorialWeightMax ρ k) / factorialWeightMin ρ k := by positivity
  have hs := Real.abs_le_sqrt (torusRegularizedInput_normSq_bound ρ hρ k D hD a b t ht c r C S hS V)
  simpa only [abs_of_nonneg (norm_nonneg _), Real.sqrt_mul hB, Real.sqrt_sq_eq_abs,
    torusRegularizedInputNormBudget] using hs

def torusRegularizedInputCLM (hρ : 0 < ρ) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    TorusHk (k + 1) H →L[ℝ] TorusHk (k + D - 1) G :=
  (torusRegularizedInputLinearMap ρ k D hD a b c r C S hS t ht).mkContinuous
    (torusRegularizedInputNormBudget ρ k D c r C)
    (torusRegularizedInput_norm_bound ρ k D hD a b c r C S hS hρ t ht)
end

/-! Canonical higher kernel inputs, their linearity, and measurable switching.
The lift supplies regularity; Fourier reconstruction supplies
measurability from the value class. -/

section
attribute [local instance] torusTimeFluxTorusNormed torusTimeFluxTorusInner torusTimeFluxTorusSpace
variable {G H : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [FiniteDimensional ℝ G] [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H] [CompleteSpace H]
variable (ρ : ℝ) (k D : ℕ) (hD : 2 ≤ D) (a b : ℝ) (c : ℕ → ℝ) (r : ℝ)
  (C : H →L[ℝ] G)
  (S : ℝ → (Lp G 2 (volume.restrict AVenhance.unitCube)) →L[ℝ]
    Lp G 2 (volume.restrict AVenhance.unitCube))
  (hS : IsSpatialRegularizerTorus ρ k D a b c r S)

variable (hρ : 0 < ρ) (hab : a ≤ b)

def clampedRegularizedInputCLM (t : ℝ) : TorusHk (k + 1) H →L[ℝ] TorusHk (k + D - 1) G :=
  torusRegularizedInputCLM ρ k D hD a b c r C S hS hρ (Set.projIcc a b hab t)
    (Set.projIcc a b hab t).property

theorem clampedRegularizedInput_stronglyMeasurable (V : TorusHk (k + 1) H) :
    StronglyMeasurable (fun t => clampedRegularizedInputCLM ρ k D hD a b c r C S hS hρ hab t V) := by
  apply torusCarrier_stronglyMeasurable_of_value (k + D - 1)
  have hs := (hS.1 (C.compLp (V.val (valueIndex2 (k + 1))))).comp_measurable
    (continuous_projIcc (a := a) (b := b) (h := hab)).measurable
  convert hs using 1
  funext t
  exact torusRegularizedInput_value ρ k D hD a b c r C S hS
    (Set.projIcc a b hab t) (Set.projIcc a b hab t).property V

theorem clampedRegularizedInput_norm_le (t : ℝ) :
    ‖clampedRegularizedInputCLM ρ k D hD a b c r C S hS hρ hab t‖ ≤
      torusRegularizedInputNormBudget ρ k D c r C := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro V
  exact torusRegularizedInput_norm_bound ρ k D hD a b c r C S hS hρ
    (Set.projIcc a b hab t) (Set.projIcc a b hab t).property V

theorem clampedRegularizedInput_memLp (V : ℝ → TorusHk (k + 1) H)
    (hV : MemLp V 2 (volume.restrict (Set.Icc a b))) :
    MemLp (fun t => clampedRegularizedInputCLM ρ k D hD a b c r C S hS hρ hab t (V t)) 2
      (volume.restrict (Set.Icc a b)) :=
  AVRegularity.KernelEnergy.memLp_operator_action (volume.restrict (Set.Icc a b))
    (clampedRegularizedInputCLM ρ k D hD a b c r C S hS hρ hab)
    (clampedRegularizedInput_stronglyMeasurable ρ k D hD a b c r C S hS hρ hab)
    (torusRegularizedInputNormBudget ρ k D c r C) (Real.sqrt_nonneg _)
    (clampedRegularizedInput_norm_le ρ k D hD a b c r C S hS hρ hab) hV
end

/-! The mass pairing of the canonical kernel flux is bounded. -/

section
attribute [local instance] torusTimeFluxTorusNormed torusTimeFluxTorusInner torusTimeFluxTorusSpace
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

open AVRegularity.CoupledEnergy.Variational

theorem matrix_nonneg (i j : ι) :
    0 ≤ kernelSchurMatrix ν ρ P.π k D a b P.c P.r P.C P.B i j := by
  unfold kernelSchurMatrix
  apply mul_nonneg (Real.sqrt_nonneg _)
  apply Finset.sum_nonneg
  intro α _
  apply mul_nonneg (norm_nonneg _)
  apply Finset.sum_nonneg
  intro d _
  apply div_nonneg
  · exact mul_nonneg ENNReal.toReal_nonneg
      ((P.hS i j α).2.2.1 (d.1 - 2) (by have := Finset.mem_Icc.1 d.2; omega))
  · exact mul_nonneg P.diffusivity_pos.le (pow_nonneg (P.hr i j α).le _)

theorem theta_nonneg_of_component (i : ι) : 0 ≤ P.θ :=
  (Finset.sum_nonneg (fun j _ => P.matrix_nonneg i j)).trans (P.hschur.1 i)

theorem flux_massPairing_abs_le (t : ℝ) (ht : t ∈ Set.Icc a b)
    (V : ∀ i, TorusHk (k + 1) (h i)) :
    |∑ i, (P.π i)⁻¹ * inner ℝ
      (factorialWeightedJet ρ (P.flux t ht V i).val)
      (factorialWeightedJet ρ (AVRegularity.CoupledEnergy.Variational.torusGradientTensor (V i)).val)| ≤
      (ν / 8) * massGradNormSq ρ P.π (fun i => (V i).val) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl he =>
    let _ := he
    simp only [Finset.univ_eq_empty, Finset.sum_empty, abs_zero, massGradNormSq, mul_zero, le_refl]
  | inr he =>
    let _ := he
    have hθ0 := P.theta_nonneg_of_component (Classical.choice he)
    have hνθ : 0 ≤ ν * P.θ := mul_nonneg P.diffusivity_pos.le hθ0
    let R := massGradNormSq ρ P.π (fun i => (V i).val)
    have hR : 0 ≤ R := massGradNormSq_nonneg ρ P.π P.hπ _
    have hg : massNormSq ρ P.π (fun i =>
        (AVRegularity.CoupledEnergy.Variational.torusGradientTensor (V i)).val) = R := by
      unfold massNormSq R massGradNormSq
      apply Finset.sum_congr rfl
      intro i _
      rw [AVRegularity.CoupledEnergy.Variational.torusGradientTensor_factorialNormSq]
    have hq := Real.sqrt_le_sqrt (P.flux_mass_bound t ht V)
    rw [Real.sqrt_mul (sq_nonneg (ν * P.θ)), Real.sqrt_sq_eq_abs, abs_of_nonneg hνθ] at hq
    have hp := massFactorialPairing_abs_le ρ P.π P.hπ
      (fun i => (P.flux t ht V i).val)
      (fun i => (AVRegularity.CoupledEnergy.Variational.torusGradientTensor (V i)).val)
    rw [hg] at hp
    have hh := hp.trans (mul_le_mul_of_nonneg_right hq (Real.sqrt_nonneg R))
    have hs : (ν * P.θ * Real.sqrt R) * Real.sqrt R = (ν * P.θ) * R := by
      rw [mul_assoc, ← pow_two, Real.sq_sqrt hR]
    rw [hs] at hh
    apply hh.trans
    have hb := mul_le_mul_of_nonneg_left P.hθ P.diffusivity_pos.le
    exact mul_le_mul_of_nonneg_right (hb.trans_eq (by ring)) hR

end TorusKernelOperator
end

end AVRegularity.KernelEnergy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergy

/-! Sum of component absolute kernel pairings, for the homogeneous supremum bounds. -/

attribute [local instance] torusTimeFluxTorusNormed torusTimeFluxTorusInner torusTimeFluxTorusSpace

theorem weightedHilbertPairing_sumAbs_le {J : Type*} [Fintype J] {H : J → Type*}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    (ω : J → ℝ) (hω : ∀ i, 0 ≤ ω i) (D Q : ∀ i, H i) :
    (∑ i, ω i * |inner ℝ (D i) (Q i)|) ≤
      Real.sqrt (∑ i, ω i * ‖D i‖ ^ 2) * Real.sqrt (∑ i, ω i * ‖Q i‖ ^ 2) := by
  apply le_trans _ (weighted_sum_mul_le ω (fun i => ‖D i‖) (fun i => ‖Q i‖) hω)
  apply Finset.sum_le_sum
  intro i _
  exact (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm (D i) (Q i)) (hω i)).trans_eq
    (mul_assoc _ _ _).symm

theorem massFactorialPairing_sumAbs_le {J : Type*} [Fintype J] {E : J → Type*}
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, MeasurableSpace (E i)] {μ : Measure (Vec 2)} {K : J → ℕ}
    (ρ : ℝ) (π : J → ℝ) (hπ : ∀ i, 0 < π i)
    (D Q : ∀ i, JetL2 μ (K i) (E i)) :
    (∑ i, (π i)⁻¹ * |inner ℝ (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (D i)) (AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (Q i))|) ≤
      Real.sqrt (massNormSq ρ π D) * Real.sqrt (massNormSq ρ π Q) := by
  have hc := weightedHilbertPairing_sumAbs_le (fun i => (π i)⁻¹)
    (fun i => inv_nonneg.mpr (hπ i).le) (fun i => AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (D i))
    (fun i => AVRegularity.CoupledEnergy.Variational.factorialWeightedJet ρ (Q i))
  simpa only [AVRegularity.CoupledEnergy.Variational.factorialWeightedJet_normSq, massNormSq] using hc
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)
theorem flux_massPairing_sumAbs_le (t : ℝ) (ht : t ∈ Set.Icc a b)
    (V : ∀ i, TorusHk (k + 1) (h i)) :
    (∑ i, (P.π i)⁻¹ * |inner ℝ
      (factorialWeightedJet ρ (P.flux t ht V i).val)
      (factorialWeightedJet ρ (AVRegularity.CoupledEnergy.Variational.torusGradientTensor (V i)).val)|) ≤
      (ν * P.θ) * massGradNormSq ρ P.π (fun i => (V i).val) := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl he =>
    let _ := he
    simp only [Finset.univ_eq_empty, Finset.sum_empty, massGradNormSq, mul_zero, le_refl]
  | inr he =>
    let _ := he
    have hθ0 := P.theta_nonneg_of_component (Classical.choice he)
    have hνθ : 0 ≤ ν * P.θ := mul_nonneg P.diffusivity_pos.le hθ0
    let R := massGradNormSq ρ P.π (fun i => (V i).val)
    have hR : 0 ≤ R := massGradNormSq_nonneg ρ P.π P.hπ _
    have hg : massNormSq ρ P.π (fun i =>
        (AVRegularity.CoupledEnergy.Variational.torusGradientTensor (V i)).val) = R := by
      unfold massNormSq R massGradNormSq
      apply Finset.sum_congr rfl
      intro i _
      rw [AVRegularity.CoupledEnergy.Variational.torusGradientTensor_factorialNormSq]
    have hq := Real.sqrt_le_sqrt (P.flux_mass_bound t ht V)
    rw [Real.sqrt_mul (sq_nonneg (ν * P.θ)), Real.sqrt_sq_eq_abs, abs_of_nonneg hνθ] at hq
    have hp := massFactorialPairing_sumAbs_le ρ P.π P.hπ
      (fun i => (P.flux t ht V i).val)
      (fun i => (AVRegularity.CoupledEnergy.Variational.torusGradientTensor (V i)).val)
    rw [hg] at hp
    have hh := hp.trans (mul_le_mul_of_nonneg_right hq (Real.sqrt_nonneg R))
    have hs : (ν * P.θ * Real.sqrt R) * Real.sqrt R = (ν * P.θ) * R := by
      rw [mul_assoc, ← pow_two, Real.sq_sqrt hR]
    rw [hs] at hh
    simpa only [AVRegularity.CoupledEnergy.Variational.factorialWeightedJet,
      AVRegularity.KernelEnergy.factorialWeightedJet] using! hh

end TorusKernelOperator

end AVRegularity.KernelEnergy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.KernelEnergy

/-! The canonical flux as a continuous linear map, with its gradient budget. -/

attribute [local instance] torusTimeFluxTorusNormed torusTimeFluxTorusInner torusTimeFluxTorusSpace
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

open AVRegularity.CoupledEnergy.Variational

def gradientBudget : ℝ := ∑ i, (P.π i)⁻¹ * factorialWeightMax ρ k

theorem gradientBudget_nonneg : 0 ≤ P.gradientBudget := by
  have hm : 0 ≤ factorialWeightMax ρ k :=
    (factorialWeight_nonneg ρ 0).trans (factorialWeight_le_max ρ (0 : Fin (k + 1)))
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (inv_nonneg.mpr (P.hπ i).le) hm)

theorem gradient_mass_le_normSq (V : ∀ i, TorusHk (k + 1) (h i)) :
    massGradNormSq ρ P.π (fun i => (V i).val) ≤ P.gradientBudget * ‖V‖ ^ 2 := by
  have hm : 0 ≤ factorialWeightMax ρ k :=
    (factorialWeight_nonneg ρ 0).trans (factorialWeight_le_max ρ (0 : Fin (k + 1)))
  unfold massGradNormSq gradientBudget
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  have hi := gradFactorialNormSq_le_jetNormSq ρ (V i).val
  have hn : ‖(V i).val‖ ≤ ‖V‖ := (show ‖(V i).val‖ = ‖V i‖ from rfl).trans_le (norm_le_pi_norm V i)
  have hs := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr hn
  exact (mul_le_mul_of_nonneg_left (hi.trans (mul_le_mul_of_nonneg_left hs hm))
    (inv_nonneg.mpr (P.hπ i).le)).trans_eq (by ring)

theorem flux_component_norm_bound (t : ℝ) (ht : t ∈ Set.Icc a b)
    (V : ∀ i, TorusHk (k + 1) (h i)) (i : ι) :
    ‖P.flux t ht V i‖ ≤
      (Real.sqrt (P.π i * (ν * P.θ) ^ 2 * P.gradientBudget) /
        Real.sqrt (factorialWeightMin ρ k)) * ‖V‖ := by
  have hf := (componentFactorial_le_mass ρ P.π P.hπ
    (fun i => (P.flux t ht V i).val) i).trans
      (mul_le_mul_of_nonneg_left (P.flux_mass_bound t ht V) (P.hπ i).le)
  have hb := hf.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (P.gradient_mass_le_normSq V) (sq_nonneg (ν * P.θ))) (P.hπ i).le)
  have hn := jetNorm_le_factorialRoot ρ P.radius_pos (P.flux t ht V i).val
  have hs := Real.sqrt_le_sqrt hb
  have hc : 0 ≤ P.π i * (ν * P.θ) ^ 2 * P.gradientBudget :=
    mul_nonneg (mul_nonneg (P.hπ i).le (sq_nonneg _)) P.gradientBudget_nonneg
  rw [← mul_assoc, ← mul_assoc, Real.sqrt_mul hc,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] at hs
  have hh := hn.trans (div_le_div_of_nonneg_right hs (Real.sqrt_nonneg _))
  change ‖P.flux t ht V i‖ ≤ _ at hh
  convert hh using 1; ring

def fluxBudget : ℝ := ∑ i,
  Real.sqrt (P.π i * (ν * P.θ) ^ 2 * P.gradientBudget) / Real.sqrt (factorialWeightMin ρ k)

theorem fluxBudget_nonneg : 0 ≤ P.fluxBudget :=
  Finset.sum_nonneg (fun _ _ => div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

theorem flux_norm_bound (t : ℝ) (ht : t ∈ Set.Icc a b)
    (V : ∀ i, TorusHk (k + 1) (h i)) : ‖P.flux t ht V‖ ≤ P.fluxBudget * ‖V‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg P.fluxBudget_nonneg (norm_nonneg _))).mpr
  intro i
  apply (P.flux_component_norm_bound t ht V i).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  unfold fluxBudget
  simpa only using! (Finset.single_le_sum
    (f := fun j : ι => Real.sqrt (P.π j * (ν * P.θ) ^ 2 * P.gradientBudget) /
      Real.sqrt (factorialWeightMin ρ k))
    (fun _ _ => div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (Finset.mem_univ i))

def fluxCLM (t : ℝ) (ht : t ∈ Set.Icc a b) :
    (∀ i, TorusHk (k + 1) (h i)) →L[ℝ] (∀ i, TorusHk k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  (P.fluxLinearMap t ht).mkContinuous P.fluxBudget (P.flux_norm_bound t ht)

end TorusKernelOperator

end AVRegularity.KernelEnergy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergy

/-! Subtracting two native coupled equations with the same forcing gives
the homogeneous native equation, with no new analytic assumptions. -/

attribute [local instance] torusTimeFluxTorusNormed torusTimeFluxTorusInner torusTimeFluxTorusSpace
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem coupledIntegratedRhs_sub_flux_forcing (K : ι → ℕ) (D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ)
    {a b t : ℝ} (hab : a ≤ b) (ht : t ∈ Set.Icc a b) (v : ℝ → Vec 2 → Vec 2)
    (hv : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hvc : ∀ r ∈ Set.Icc a b, Continuous (v r))
    (B : ℝ) (hvb : ∀ r ∈ Set.Icc a b, ∀ x, ‖v r x‖ ≤ B)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hAm : ∀ i i' d, Measurable (fun p : Set.Icc a b × Vec 2 => A i i' d p.1 p.2))
    (hAc : ∀ r ∈ Set.Icc a b, ∀ i i' d, ContDiff ℝ (K i : ℕ) (A i i' d r))
    (F F' : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hF' : ∀ i, MemLp (F' i) 2 (volume.restrict (Set.Icc a b)))
    (U V : CoupledHighTime (h := h) K a b) (i : ι) (φ : TorusHk 1 (h i)) :
    coupledIntegratedRhs K D ν a t v A (fun i r => F i r - F' i r) (fun _ _ => 0) (U - V : CoupledHighTime (h := h) K a b) i φ =
      coupledIntegratedRhs K D ν a t v A F g U i φ -
        coupledIntegratedRhs K D ν a t v A F' g V i φ := by
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hd := torusDiffusion_integral_sub K ha ht ht.1 i U V φ
  have hvs (k : Fin 2) := torusDrift_integral_sub K ha ht ht.1 v hv hvc B hvb i k U V φ
  have hAs (i' : ι) (d : admissibleOrders K D i i') := torusCoupling_integral_sub K D ha ht ht.1
    ρ hρ i i' d (A i i' d) (hA i i' d) (hAm i i' d) (fun r hr => hAc r hr i i' d) U V φ
  have hFs := torusFluxPairing_integral_sub hab ht.1 ht.2 (F i) (F' i) (hF i) (hF' i) φ
  have hgz : (∫ x in AVenhance.unitCube,
      inner ℝ (Galerkin.torusHkValueCLM (0 : TorusHk (K i) (h i)) x)
        (Galerkin.torusHkValueCLM φ x)) = 0 := by
    rw [← L2.inner_def]
    simp only [map_zero, inner_zero_left]
  unfold coupledIntegratedRhs
  rw [hd]
  simp_rw [hvs, hAs, Finset.sum_sub_distrib]
  rw [hFs]
  simp only [hgz, intervalIntegral.integral_zero]
  ring

end AVRegularity.KernelEnergy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.KernelEnergy

/-! Time measurability of the canonical kernel flux under the premises of `kernel_energy_torus`. -/

attribute [local instance] torusTimeFluxTorusNormed torusTimeFluxTorusInner torusTimeFluxTorusSpace
variable
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

theorem lift_time_stronglyMeasurable
    (V : Set.Icc a b → ∀ i, TorusHk (k + 1) (h i)) (hV : StronglyMeasurable V)
    (i j : ι) (α : Γ i j) :
    StronglyMeasurable (fun t : Set.Icc a b => P.lift t t.property (V t) i j α) := by
  exact torusRegularizedInput_time_stronglyMeasurable ρ k D P.order_ge_two a b P.c
    (P.r i j α) (P.C i j α) (P.S i j α) (P.hS i j α) _
    ((continuous_apply j).comp_stronglyMeasurable hV)

theorem fluxTerm_time_stronglyMeasurable
    (V : Set.Icc a b → ∀ i, TorusHk (k + 1) (h i)) (hV : StronglyMeasurable V)
    (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)) :
    StronglyMeasurable (fun t : Set.Icc a b => P.fluxTerm t t.property (V t) i j α d) := by
  have hlow : k + ((d.1 - 2) + 1) ≤ k + D - 1 := by
    have := Finset.mem_Icc.1 d.2
    omega
  have hY := (truncateTorusHk (E := G i j α) hlow).continuous.comp_stronglyMeasurable
    (P.lift_time_stronglyMeasurable V hV i j α)
  exact torusKernelFluxTerm_time_stronglyMeasurable
    (by have := Finset.mem_Icc.1 d.2; omega) ρ P.radius_pos a b
    (P.B i j α d) (P.hB_fin i j α d) (P.hB_meas i j α d)
    (P.hB_smooth i j α d) (P.hB_per i j α d) _ hY

theorem flux_time_stronglyMeasurable
    (V : Set.Icc a b → ∀ i, TorusHk (k + 1) (h i)) (hV : StronglyMeasurable V)
    (i : ι) : StronglyMeasurable (fun t : Set.Icc a b => P.flux t t.property (V t) i) := by
  classical
  have hs : StronglyMeasurable (fun t : Set.Icc a b => P.assembledFlux t t.property (V t) i) :=
    Finset.stronglyMeasurable_fun_sum _ (fun j _ =>
      Finset.stronglyMeasurable_fun_sum _ (fun α _ =>
        Finset.stronglyMeasurable_fun_sum _ (fun d _ => P.fluxTerm_time_stronglyMeasurable V hV i j α d)))
  have he : (fun t : Set.Icc a b => P.assembledFlux t t.property (V t) i) =
      (fun t : Set.Icc a b => P.flux t t.property (V t) i) :=
    funext (fun t => P.assembledFlux_eq_flux t t.property (V t) i)
  rwa [he] at hs

end TorusKernelOperator

end AVRegularity.KernelEnergy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.KernelEnergy

/-! Kernel contributions to the finite scalar Fourier matrix. -/

section
attribute [local instance] torusTimeFluxTorusNormed torusTimeFluxTorusInner torusTimeFluxTorusSpace
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

def coefficientSynthesis (N : ℕ) : CoupledPlainCoefficients (h := h) N →L[ℝ]
    (∀ i, TorusHk (k + 1) (h i)) :=
  ContinuousLinearMap.pi (fun i => coupledPlainSynthesis N i (k + 1))

def fluxCoefficientRow (N : ℕ) (r : CoupledFourierModeIndex (h := h) N) :
    (∀ i, TorusHk k (PiLp 2 (fun _ : Fin 2 => h i))) →L[ℝ] ℝ :=
  -∑ i, (plainFluxForcingCLM N r i k).comp (ContinuousLinearMap.proj i)

def kernelCoefficientRow (N : ℕ) (t : Set.Icc a b)
    (r : CoupledFourierModeIndex (h := h) N) : CoupledPlainCoefficients (h := h) N →L[ℝ] ℝ :=
  (fluxCoefficientRow (h := h) (k := k) N r).comp ((P.fluxCLM t t.property).comp (coefficientSynthesis (h := h) (k := k) N))

def kernelMatrixEntry (N : ℕ) (t : Set.Icc a b)
    (r c : CoupledFourierModeIndex (h := h) N) : ℝ :=
  P.kernelCoefficientRow N t r (Pi.single c 1)

theorem kernelMatrixEntry_stronglyMeasurable (N : ℕ)
    (r c : CoupledFourierModeIndex (h := h) N) :
    StronglyMeasurable (fun t : Set.Icc a b => P.kernelMatrixEntry N t r c) := by
  have hs : StronglyMeasurable (fun t : Set.Icc a b =>
      -∑ i, plainFluxForcingCLM N r i k
        (P.flux t t.property (coefficientSynthesis (h := h) (k := k) N (Pi.single c 1)) i)) :=
    (Finset.stronglyMeasurable_fun_sum _ (fun i _ =>
      (plainFluxForcingCLM N r i k).continuous.comp_stronglyMeasurable
        (P.flux_time_stronglyMeasurable _ stronglyMeasurable_const i))).neg
  simpa only [kernelMatrixEntry, kernelCoefficientRow, fluxCoefficientRow,
    ContinuousLinearMap.comp_apply, neg_apply,
    sum_apply, ContinuousLinearMap.proj_apply, fluxCLM,
    fluxLinearMap, LinearMap.mkContinuous_apply] using! hs

theorem kernelMatrix_action (N : ℕ) (t : Set.Icc a b)
    (x : CoupledPlainCoefficients (h := h) N) (r : CoupledFourierModeIndex (h := h) N) :
    plainMatrixCLM (P.kernelMatrixEntry N t) x r = P.kernelCoefficientRow N t r x := by
  rw [plainMatrixCLM_apply]
  have he : x = ∑ c, x c • Pi.single c (1 : ℝ) := by
    ext c
    simp [Pi.single_apply]
  conv_rhs => rw [he]
  simp only [map_sum, map_smul, smul_eq_mul, kernelMatrixEntry]
  apply Finset.sum_congr rfl
  intro c _
  exact mul_comm _ _

def clampedKernelMatrixEntry (N : ℕ) (t : ℝ)
    (r c : CoupledFourierModeIndex (h := h) N) : ℝ :=
  P.kernelMatrixEntry N (Set.projIcc a b P.htime t) r c

theorem clampedKernelMatrixEntry_stronglyMeasurable (N : ℕ)
    (r c : CoupledFourierModeIndex (h := h) N) :
    StronglyMeasurable (fun t => P.clampedKernelMatrixEntry N t r c) :=
  (P.kernelMatrixEntry_stronglyMeasurable N r c).comp_measurable
    (continuous_projIcc (a := a) (b := b) (h := P.htime)).measurable

end TorusKernelOperator
end

/-! A finite uniform entry budget for the actual kernel Galerkin matrix. -/

section
attribute [local instance] torusTimeFluxTorusNormed torusTimeFluxTorusInner torusTimeFluxTorusSpace
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

def kernelMatrixBudget (N : ℕ) : ℝ :=
  ∑ r : CoupledFourierModeIndex (h := h) N,
    ‖fluxCoefficientRow (h := h) (k := k) N r‖ * P.fluxBudget *
      ‖coefficientSynthesis (h := h) (k := k) N‖

theorem kernelMatrixBudget_nonneg (N : ℕ) : 0 ≤ P.kernelMatrixBudget N :=
  Finset.sum_nonneg (fun r _ => mul_nonneg
    (mul_nonneg (norm_nonneg (fluxCoefficientRow (h := h) (k := k) N r)) P.fluxBudget_nonneg)
      (norm_nonneg (coefficientSynthesis (h := h) (k := k) N)))

theorem kernelMatrixEntry_bound (N : ℕ) (t : Set.Icc a b)
    (r c : CoupledFourierModeIndex (h := h) N) :
    |P.kernelMatrixEntry N t r c| ≤ P.kernelMatrixBudget N := by
  let L := fluxCoefficientRow (h := h) (k := k) N r
  let T := coefficientSynthesis (h := h) (k := k) N
  have hs : ‖(Pi.single c (1 : ℝ) : CoupledPlainCoefficients (h := h) N)‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro j
    by_cases he : j = c
    · subst j
      simp
    · simp [he]
  have ht : ‖T (Pi.single c 1)‖ ≤ ‖T‖ :=
    (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left hs (norm_nonneg T)) |>.trans_eq (mul_one _)
  have hf := (P.flux_norm_bound t t.property (T (Pi.single c 1))).trans
    (mul_le_mul_of_nonneg_left ht P.fluxBudget_nonneg)
  have hr := (L.le_opNorm (P.flux t t.property (T (Pi.single c 1)))).trans
    (mul_le_mul_of_nonneg_left hf (norm_nonneg L))
  have hterm : ‖L‖ * (P.fluxBudget * ‖T‖) ≤ P.kernelMatrixBudget N := by
    unfold kernelMatrixBudget
    rw [← mul_assoc]
    simpa only [L, T] using! (Finset.single_le_sum
      (f := fun r : CoupledFourierModeIndex (h := h) N =>
        ‖fluxCoefficientRow (h := h) (k := k) N r‖ * P.fluxBudget *
          ‖coefficientSynthesis (h := h) (k := k) N‖)
      (fun r _ => mul_nonneg
        (mul_nonneg (norm_nonneg (fluxCoefficientRow (h := h) (k := k) N r)) P.fluxBudget_nonneg)
        (norm_nonneg (coefficientSynthesis (h := h) (k := k) N))) (Finset.mem_univ r))
  exact hr.trans hterm

theorem clampedKernelMatrixEntry_bound (N : ℕ) (t : ℝ)
    (r c : CoupledFourierModeIndex (h := h) N) :
    |P.clampedKernelMatrixEntry N t r c| ≤ P.kernelMatrixBudget N :=
  P.kernelMatrixEntry_bound N _ r c

end TorusKernelOperator
end

/-! The kernel system reuses the existing diffusion and drift Fourier matrix,
with an empty local coupling family. -/

section
attribute [local instance] torusTimeFluxTorusNormed torusTimeFluxTorusInner torusTimeFluxTorusSpace
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

omit [Fintype ι] [DecidableEq ι] in
theorem noLocalOrders (i j : ι) (d : admissibleOrders (fun _ : ι => k) 0 i j) : False := by
  have hd := Finset.mem_filter.1 d.property
  have := Finset.mem_Icc.1 hd.1
  omega

def noLocalCoefficient (i j : ι) (d : admissibleOrders (fun _ : ι => k) 0 i j) :
    ℝ → Vec 2 → PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h i) :=
  (noLocalOrders (k := k) i j d).elim

def projectedMatrix (N : ℕ) (v : ℝ → Vec 2 → Vec 2) (t : ℝ)
    (r c : CoupledFourierModeIndex (h := h) N) : ℝ :=
  plainIntervalMatrix N 0 ν (fun _ => k) a b P.htime v
    (noLocalCoefficient (h := h) (k := k)) t r c + P.clampedKernelMatrixEntry N t r c

theorem projectedMatrix_stronglyMeasurable (N : ℕ) (v : ℝ → Vec 2 → Vec 2)
    (hv : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (r c : CoupledFourierModeIndex (h := h) N) :
    StronglyMeasurable (fun t => P.projectedMatrix N v t r c) := by
  exact (plainIntervalMatrix_stronglyMeasurable N 0 ν (fun _ => k) a b P.htime v hv
    (noLocalCoefficient (h := h) (k := k))
    (fun i j d => (noLocalOrders (k := k) i j d).elim) r c).add
    (P.clampedKernelMatrixEntry_stronglyMeasurable N r c)

theorem projectedMatrix_bounded (N : ℕ) (v : ℝ → Vec 2 → Vec 2)
    (hv : ∃ V : ℝ, ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t r c, |P.projectedMatrix N v t r c| ≤ C := by
  obtain ⟨C, hC, hb⟩ := plainIntervalMatrix_bounded N 0 ν ρ P.radius_pos
    (fun _ => k) a b P.htime v hv (noLocalCoefficient (h := h) (k := k))
    (fun i j d => (noLocalOrders (k := k) i j d).elim)
  refine ⟨C + P.kernelMatrixBudget N, add_nonneg hC (P.kernelMatrixBudget_nonneg N), ?_⟩
  intro t r c
  exact (abs_add_le _ _).trans (add_le_add (hb t r c) (P.clampedKernelMatrixEntry_bound N t r c))

end TorusKernelOperator
end

end AVRegularity.KernelEnergy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set
open AVRegularity.CoupledEnergy.Galerkin
open scoped Topology
namespace AVRegularity.KernelEnergy

/-! Solve the actual kernel Galerkin system on plain finite coefficient vectors. -/

attribute [local instance] torusTimeFluxTorusNormed torusTimeFluxTorusInner torusTimeFluxTorusSpace
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

theorem kernelFourierODE_existsUnique (N : ℕ) (v : ℝ → Vec 2 → Vec 2)
    (hv_bdd : ∃ V : ℝ, ∀ t ∈ Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hv_meas : Measurable (fun p : Icc a b × Vec 2 => v p.1 p.2))
    (f : ∀ i, TorusHk k (h i))
    (F : ∀ i, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk k (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Icc a b))) :
    ∃! y : C(Icc a b, CoupledPlainCoefficients (h := h) N),
      AVenhance.Infra.ODE.IsLinearIntegralSolution
        (fun t => plainMatrixCLM (P.projectedMatrix N v t))
        (fun t => plainSourceCoefficients N (fun _ => k) (fun i => F i t) (fun i => g i t))
        (plainInitialCoefficients N (fun _ => k) f) a b (AVenhance.Infra.ODE.extendCurve P.htime y) ∧
      AbsolutelyContinuousOnInterval (AVenhance.Infra.ODE.extendCurve P.htime y) a b := by
  obtain ⟨C, hC, hb⟩ := P.projectedMatrix_bounded N v hv_bdd
  have hm : ∀ r c, AEStronglyMeasurable (fun t => P.projectedMatrix N v t r c) volume :=
    fun r c => (P.projectedMatrix_stronglyMeasurable N v hv_meas r c).aestronglyMeasurable
  have hf : IntervalIntegrable
      (fun t => plainSourceCoefficients N (fun _ => k) (fun i => F i t) (fun i => g i t)) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le P.htime).mpr
      (plainSourceCoefficients_integrable N (fun _ => k) a b F g hF hg)
  exact plainMatrixODE_existsUnique P.htime _ _ _ C hC hm hb hf

end TorusKernelOperator

end AVRegularity.KernelEnergy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.KernelEnergy

/-! The solved coefficient right-hand side equals the diffusion/drift right-hand side with the
actual kernel flux added to the prescribed flux. -/

attribute [local instance] torusTimeFluxTorusNormed torusTimeFluxTorusInner torusTimeFluxTorusSpace
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

theorem projectedMatrix_rhs (N : ℕ) (v : ℝ → Vec 2 → Vec 2) (t : ℝ)
    (ht : t ∈ Set.Icc a b) (x : CoupledPlainCoefficients (h := h) N)
    (F : ∀ i, TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, TorusHk k (h i)) :
    plainMatrixCLM (P.projectedMatrix N v t) x + plainSourceCoefficients N (fun _ => k) F g =
      plainMatrixCLM (plainFourierMatrix N 0 ν (fun _ => k) v
        (noLocalCoefficient (h := h) (k := k)) t) x +
      plainSourceCoefficients N (fun _ => k)
        (fun i => F i + P.flux t ht (coefficientSynthesis (h := h) (k := k) N x) i) g := by
  have he (r c : CoupledFourierModeIndex (h := h) N) :
      P.projectedMatrix N v t r c =
        plainFourierMatrix N 0 ν (fun _ => k) v (noLocalCoefficient (h := h) (k := k)) t r c +
          P.kernelMatrixEntry N ⟨t, ht⟩ r c := by
    simp only [projectedMatrix, clampedKernelMatrixEntry,
      plainIntervalMatrix_of_mem N 0 ν (fun _ => k) a b P.htime v _ t ht,
      Set.projIcc_of_mem P.htime ht]
  ext r
  have ha := P.kernelMatrix_action N ⟨t, ht⟩ x r
  simp only [plainMatrixCLM_apply] at ha
  simp only [Pi.add_apply, plainMatrixCLM_apply, he, add_mul, Finset.sum_add_distrib]
  rw [ha]
  simp only [kernelCoefficientRow, fluxCoefficientRow, ContinuousLinearMap.comp_apply,
    neg_apply, sum_apply, ContinuousLinearMap.proj_apply, fluxCLM,
    LinearMap.mkContinuous_apply, fluxLinearMap, LinearMap.coe_mk, plainSourceCoefficients, map_add,
    sub_add_eq_sub_sub, Finset.sum_sub_distrib]
  change (∑ c, plainFourierMatrix N 0 ν (fun _ => k) v noLocalCoefficient t r c * x c) +
      -(∑ i, plainFluxForcingCLM N r i k
        (P.flux t ht (coefficientSynthesis (h := h) (k := k) N x) i)) +
      ((∑ i, plainValueForcingCLM N r i k (g i)) - (∑ i, plainFluxForcingCLM N r i k (F i))) =
    (∑ c, plainFourierMatrix N 0 ν (fun _ => k) v noLocalCoefficient t r c * x c) +
      ((∑ i, plainValueForcingCLM N r i k (g i)) - (∑ i, plainFluxForcingCLM N r i k (F i)) -
      (∑ i, plainFluxForcingCLM N r i k
        (P.flux t ht (coefficientSynthesis (h := h) (k := k) N x) i)))
  ring

end TorusKernelOperator

end AVRegularity.KernelEnergy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.KernelEnergy

/-! Extend the actual kernel flux to ambient higher jets after solving the finite ODE. -/

attribute [local instance] torusTimeFluxTorusNormed torusTimeFluxTorusInner torusTimeFluxTorusSpace
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

def ambientCarrierCLM : CoupledHighHilbert (h := h) (fun _ => k) →L[ℝ]
    (∀ i, TorusHk (k + 1) (h i)) :=
  ContinuousLinearMap.pi (fun i => (torusGraphProjection (E := h i) (k + 1)).comp
    (PiLp.proj (𝕜 := ℝ) 2 (fun i => JetL2 (volume.restrict AVenhance.unitCube) (k + 1) (h i)) i))

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] in
@[simp] theorem ambientCarrierCLM_graph (V : ∀ i, TorusHk (k + 1) (h i)) :
    ambientCarrierCLM (h := h) (k := k) (WithLp.toLp 2 (fun i => (V i).val)) = V := by
  funext i
  exact torusGraphProjection_carrier (k + 1) (V i)

theorem ambientCarrierCLM_plainSynthesis (N : ℕ) (x : CoupledPlainCoefficients (h := h) N) :
    ambientCarrierCLM (h := h) (k := k) (plainHigherSynthesisCLM N (fun _ => k) x) =
      coefficientSynthesis (h := h) (k := k) N x := by
  funext i
  exact torusGraphProjection_carrier (k + 1) (coupledPlainSynthesis N i (k + 1) x)

def ambientFluxCLM (t : Set.Icc a b) (i : ι) :
    CoupledHighHilbert (h := h) (fun _ => k) →L[ℝ] TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)) :=
  (ContinuousLinearMap.proj i).comp
    ((P.fluxCLM t t.property).comp (ambientCarrierCLM (h := h) (k := k)))

omit [DecidableEq ι] in
theorem ambientFluxCLM_stronglyMeasurable (i : ι)
    (V : CoupledHighHilbert (h := h) (fun _ => k)) :
    StronglyMeasurable (fun t : Set.Icc a b => P.ambientFluxCLM t i V) :=
  P.flux_time_stronglyMeasurable _ stronglyMeasurable_const i

def ambientFluxBudget : ℝ := P.fluxBudget * ‖ambientCarrierCLM (h := h) (k := k)‖

omit [DecidableEq ι] in
theorem ambientFluxBudget_nonneg : 0 ≤ P.ambientFluxBudget :=
  mul_nonneg P.fluxBudget_nonneg (norm_nonneg (ambientCarrierCLM (h := h) (k := k)))

omit [DecidableEq ι] in
theorem ambientFluxCLM_norm_le (t : Set.Icc a b) (i : ι) :
    ‖P.ambientFluxCLM t i‖ ≤ P.ambientFluxBudget := by
  apply ContinuousLinearMap.opNorm_le_bound _ P.ambientFluxBudget_nonneg
  intro V
  have hf := (norm_le_pi_norm
    (P.flux t t.property (ambientCarrierCLM (h := h) (k := k) V)) i).trans
    (P.flux_norm_bound t t.property _)
  have hp := (ambientCarrierCLM (h := h) (k := k)).le_opNorm V
  exact (hf.trans (mul_le_mul_of_nonneg_left hp P.fluxBudget_nonneg)).trans_eq (mul_assoc _ _ _).symm

end TorusKernelOperator

end AVRegularity.KernelEnergy
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.KernelEnergy

/-! One fixed Bochner operator for the actual switched kernel flux. -/

attribute [local instance] torusTimeFluxTorusNormed torusTimeFluxTorusInner torusTimeFluxTorusSpace
variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

def clampedAmbientFluxCLM (i : ι) (t : ℝ) :
    CoupledHighHilbert (h := h) (fun _ => k) →L[ℝ] TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)) :=
  P.ambientFluxCLM (Set.projIcc a b P.htime t) i

omit [DecidableEq ι] in
theorem clampedAmbientFluxCLM_stronglyMeasurable (i : ι)
    (V : CoupledHighHilbert (h := h) (fun _ => k)) :
    StronglyMeasurable (fun t => P.clampedAmbientFluxCLM i t V) :=
  (P.ambientFluxCLM_stronglyMeasurable i V).comp_measurable
    (continuous_projIcc (a := a) (b := b) (h := P.htime)).measurable

omit [DecidableEq ι] in
theorem clampedAmbientFluxCLM_norm_le (i : ι) (t : ℝ) :
    ‖P.clampedAmbientFluxCLM i t‖ ≤ P.ambientFluxBudget :=
  P.ambientFluxCLM_norm_le _ i

def kernelTimeFluxCLM (i : ι) : CoupledHighTime (h := h) (fun _ => k) a b →L[ℝ]
    Lp (TorusHk k (PiLp 2 (fun _ : Fin 2 => h i))) 2 (volume.restrict (Set.Icc a b)) :=
  AVRegularity.KernelEnergy.timeOperatorCLM (volume.restrict (Set.Icc a b))
    (P.clampedAmbientFluxCLM i) (P.clampedAmbientFluxCLM_stronglyMeasurable i)
    P.ambientFluxBudget P.ambientFluxBudget_nonneg (P.clampedAmbientFluxCLM_norm_le i)

end TorusKernelOperator

end AVRegularity.KernelEnergy
end
end
end
