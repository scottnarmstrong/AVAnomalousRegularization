-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.FullLift.ClassicalFiniteDerivative
public import AVRegularity.CycleComparison.Lift.TransverseModeFactor
import AVRegularity.Construction.Preservation.FullLift.PositiveChartInputJets
public import AVRegularity.Analysis.Convolution.Kernel.PairedSource
import AVRegularity.KernelEnergy.PlaneFluxTerm
public import AVRegularity.Statements.Intermediate.CycleOutput.IsClassicalRep
import AVRegularity.CoupledEnergy.Galerkin.PlainSourcePairing
import AVRegularity.CoupledEnergy.Variational.GradientTensorCLM
import AVRegularity.CycleComparison.Lift.SecondCrossMean
public import AVRegularity.Definitions.Construction.Preparation
import AVRegularity.Construction.InitialValue.Cascade
public import AVRegularity.KernelEnergy.TorusMultiplierCLM
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.Compactness.DeltaGeneratedSpace

section
@[expose] public noncomputable section
open MeasureTheory Homogenization Filter Set
namespace AVRegularity.Construction.Preservation.FullLift

/-! Adapt the dominated parameter integral to the joint slow-fast dimension.
The differentiation argument is that of compact parameter integrals. -/

variable {d : ℕ} {T : Type*} [MeasurableSpace T]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [CompleteSpace E] in
theorem finite_parameter_integral_continuous (μ : Measure T) [IsFiniteMeasure μ]
    (f : T → Vec d → E) (hm : ∀ x, Measurable (fun t => f t x))
    (hc : ∀ t, Continuous (f t)) (C : ℝ) (hb : ∀ t x, ‖f t x‖ ≤ C) :
    Continuous (fun x => ∫ t, f t x ∂μ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply continuousAt_of_dominated
  · exact Eventually.of_forall (fun y => (hm y).aestronglyMeasurable)
  · exact Eventually.of_forall (fun y => ae_of_all μ (fun t => hb t y))
  · exact integrable_const C
  · exact ae_of_all μ (fun t => (hc t).continuousAt)

omit [CompleteSpace E] in
theorem finite_parameter_integral_hasFDerivAt (μ : Measure T) [IsFiniteMeasure μ]
    (f : T → Vec d → E) (hm : ∀ x, Measurable (fun t => f t x))
    (hd : ∀ t, Differentiable ℝ (f t)) (C₀ C₁ : ℝ)
    (hb₀ : ∀ t x, ‖f t x‖ ≤ C₀)
    (hb₁ : ∀ t x, ‖fderiv ℝ (f t) x‖ ≤ C₁) (x : Vec d) :
    HasFDerivAt (fun y => ∫ t, f t y ∂μ)
      (∫ t, fderiv ℝ (f t) x ∂μ) x := by
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ)
    (μ := μ) (F := fun y t => f t y)
    (F' := fun y t => fderiv ℝ (f t) y)
    (bound := fun _ => C₁) (Filter.univ_mem)
  · exact Eventually.of_forall (fun y => (hm y).aestronglyMeasurable)
  · exact (integrable_const C₀).mono' (hm x).aestronglyMeasurable
      (ae_of_all μ (fun t => hb₀ t x))
  · exact (finite_fderiv_parameter_stronglyMeasurable f hm hd x).aestronglyMeasurable
  · exact ae_of_all μ (fun t y _ => hb₁ t y)
  · exact integrable_const C₁
  · exact ae_of_all μ (fun t y _ => (hd t y).hasFDerivAt)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public section
namespace AVRegularity.Construction.Preservation.FullLift

/-! Componentwise parent bounds for keeping time suprema inside the component sum. -/

variable {ι κ : Type*} [Fintype κ] [DecidableEq ι]

theorem parent_component_square_le (p : κ → ι) (i : ι) (β y : κ → ℝ)
    (a C : ℝ) (ha : 0 ≤ a) (hy : ∀ j, 0 ≤ y j) (hβ : ∀ j, p j = i → β j ≤ 1)
    (hbound : a ≤ ∑ j, if p j = i then β j * y j else 0)
    (hfiber : ((Finset.univ : Finset κ).filter fun j => p j = i).card ≤ C) :
    a ^ 2 ≤ C * ∑ j, if p j = i then y j ^ 2 else 0 := by
  classical
  let s := (Finset.univ : Finset κ).filter fun j => p j = i
  have hsum : a ≤ ∑ j ∈ s, y j := by
    apply hbound.trans
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : p j = i
    · simp only [hj, ↓reduceIte]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hβ j hj) (hy j)
    · simp only [hj, ↓reduceIte]
      exact le_rfl
  have hcs : (∑ j ∈ s, y j) ^ 2 ≤ (s.card : ℝ) * ∑ j ∈ s, y j ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) y
  calc
    _ ≤ (∑ j ∈ s, y j) ^ 2 := (sq_le_sq₀ ha (ha.trans hsum)).mpr hsum
    _ ≤ (s.card : ℝ) * ∑ j ∈ s, y j ^ 2 := hcs
    _ ≤ C * ∑ j ∈ s, y j ^ 2 :=
      mul_le_mul_of_nonneg_right hfiber (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ = _ := by rw [Finset.sum_filter]

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

/-! A full joint bound restricts to the scaled mixed envelope without coordinate losses. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem scaled_mixed_parameter_jet_norm_le (r q : ℕ) (f : E → F)
    (hf : ContDiff ℝ (r + q : ℕ∞) f) (Lslow Lfast : Vec 2 →L[ℝ] E)
    (lam B : ℝ) (hlam : 0 ≤ lam) (hB : 0 ≤ B)
    (hs : ‖Lslow‖ ≤ lam) (hz : ‖Lfast‖ ≤ 1)
    (hbound : ∀ W, ‖iteratedFDeriv ℝ (r + q) f W‖ ≤ B) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q
      (fun w => f (Lslow Y + Lfast w)) z) X‖ ≤ B * lam ^ r := by
  have hh := mixed_linear_parameter_jet_norm_le r q f hf Lslow Lfast X z
  have hs' : ‖Lslow‖ ^ r ≤ lam ^ r := pow_le_pow_left₀ (norm_nonneg _) hs r
  have hz' : ‖Lfast‖ ^ q ≤ 1 := by simpa using pow_le_pow_left₀ (norm_nonneg _) hz q
  have hb' : ‖iteratedFDeriv ℝ (r + q) f (Lslow X + Lfast z)‖ * ‖Lslow‖ ^ r ≤
      B * lam ^ r := mul_le_mul (hbound _) hs' (by positivity) hB
  exact hh.trans ((mul_le_mul hb' hz' (by positivity) (by positivity)).trans_eq (mul_one _))

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public section
namespace AVRegularity.Construction.Preservation.FullLift

/-! Diagonal conjugation of the finite amplitude estimate, allowing different source and target
component sets. The diagonal factors are the inverse square root masses, with optional markers. -/

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The chosen diagonal has exactly the inverse-mass square used by the energy estimates. -/
theorem inverse_sqrt_mass_square {π : ℝ} (hπ : 0 ≤ π) (x : ℝ) :
    ((Real.sqrt π)⁻¹ * x) ^ 2 = π⁻¹ * x ^ 2 := by
  rw [mul_pow, inv_pow, Real.sq_sqrt hπ]

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.Construction.Preservation.FullLift

/-! The dominated finite-parameter integral has every reserved classical order. -/

variable {T : Type*} [MeasurableSpace T] {d : ℕ}

theorem finite_parameter_integral_contDiff (μ : Measure T) [IsFiniteMeasure μ] (n : ℕ) :
    ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
      (f : T → Vec d → E),
      (∀ x, Measurable (fun t => f t x)) →
      (∀ t, ContDiff ℝ (n : ℕ∞) (f t)) →
      ∀ C : ℕ → ℝ, (∀ j ≤ n, ∀ t x, ‖iteratedFDeriv ℝ j (f t) x‖ ≤ C j) →
      ContDiff ℝ (n : ℕ∞) (fun x => ∫ t, f t x ∂μ) := by
  induction n with
  | zero =>
    intro E _ _ _ _ _ _ f hm hs C hb
    apply contDiff_zero.mpr
    exact finite_parameter_integral_continuous μ f hm (fun t => (hs t).continuous)
      (C 0) (fun t x => by simpa using hb 0 (Nat.zero_le _) t x)
  | succ n ih =>
    intro E _ _ _ _ _ _ f hm hs C hb
    have hd : ∀ t, Differentiable ℝ (f t) := fun t => (hs t).differentiable (by simp)
    have hb₀ : ∀ t x, ‖f t x‖ ≤ C 0 := fun t x => by
      simpa using hb 0 (Nat.zero_le _) t x
    have hb₁ : ∀ t x, ‖fderiv ℝ (f t) x‖ ≤ C 1 := fun t x => by
      simpa only [norm_iteratedFDeriv_one] using hb 1 (by omega) t x
    have hder := finite_parameter_integral_hasFDerivAt μ f hm hd (C 0) (C 1) hb₀ hb₁
    have hs' : ∀ t, ContDiff ℝ (n : ℕ∞) (fderiv ℝ (f t)) := fun t =>
      (hs t).fderiv_right (by simp)
    have hm' : ∀ x, Measurable (fun t => fderiv ℝ (f t) x) := fun x =>
      (finite_fderiv_parameter_stronglyMeasurable f hm hd x).measurable
    have hhi := ih (Vec d →L[ℝ] E) (fun t x => fderiv ℝ (f t) x) hm' hs'
      (fun j => C (j + 1)) (fun j hj t x => by
        rw [norm_iteratedFDeriv_fderiv]
        exact hb (j + 1) (by omega) t x)
    have he : fderiv ℝ (fun x => ∫ t, f t x ∂μ) =
        fun x => ∫ t, fderiv ℝ (f t) x ∂μ := funext (fun x => (hder x).fderiv)
    have hcast : (((n + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by simp
    rw [hcast, contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hder x).differentiableAt, by simp, ?_⟩
    rw [he]
    exact hhi

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public section
namespace AVRegularity.Construction.Preservation.FullLift

/-! Componentwise square bounds after conjugation by the actual energy diagonals. -/

section
variable {ι κ : Type*} [Fintype κ] [DecidableEq ι]

theorem weighted_parent_component_square_le (p : κ → ι) (i : ι) (β y : κ → ℝ)
    (a w C : ℝ) (z : κ → ℝ) (ha : 0 ≤ a) (hw : 0 ≤ w)
    (hz : ∀ j, 0 < z j) (hy : ∀ j, 0 ≤ y j)
    (hbound : a ≤ ∑ j, if p j = i then β j * y j else 0)
    (hentry : ∀ j, p j = i → w / z j * β j ≤ 1)
    (hfiber : ((Finset.univ : Finset κ).filter fun j => p j = i).card ≤ C) :
    (w * a) ^ 2 ≤ C * ∑ j, if p j = i then (z j * y j) ^ 2 else 0 := by
  classical
  have he : w * (∑ j, if p j = i then β j * y j else 0) =
      ∑ j, if p j = i then (w / z j * β j) * (z j * y j) else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : p j = i
    · simp only [hj, ↓reduceIte]
      field_simp [ne_of_gt (hz j)]
    · simp only [hj, ↓reduceIte, mul_zero]
  apply parent_component_square_le p i (fun j => w / z j * β j)
    (fun j => z j * y j) (w * a) C (mul_nonneg hw ha)
    (fun j => mul_nonneg (hz j).le (hy j)) hentry _ hfiber
  exact (mul_le_mul_of_nonneg_left hbound hw).trans_eq he
end

/-! The original birth price pays every retained native order, for every positive kernel width. -/

theorem constituentPrice_order_bound (r : ConstituentRecord) (m : ℕ) (hm : m ≤ r.birthExcess) :
    max 1 ((r.length / r.width) ^ m) ≤ constituentPrice r := by
  unfold constituentPrice
  apply max_le (le_max_left _ _)
  exact nonnegative_pow_le_max_one_pow (r.length / r.width)
    (div_nonneg r.length_pos.le r.width_pos.le) m r.birthExcess hm

theorem constituentPrice_nonneg (r : ConstituentRecord) : 0 ≤ constituentPrice r :=
  zero_le_one.trans (le_max_left _ _)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.Construction.Preservation.FullLift

/-! Full multilinear jet bounds after dominated integration, without a coordinate loss. -/

variable {T : Type*} [MeasurableSpace T] {d : ℕ}

theorem finite_parameter_integral_jet_norm_le (μ : Measure T) [IsFiniteMeasure μ] (n : ℕ) :
    ∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
      (f : T → Vec d → E),
      (∀ x, Measurable (fun t => f t x)) →
      (∀ t, ContDiff ℝ (n : ℕ∞) (f t)) →
      ∀ C : ℕ → ℝ, (∀ j ≤ n, ∀ t x, ‖iteratedFDeriv ℝ j (f t) x‖ ≤ C j) →
      ∀ x, ‖iteratedFDeriv ℝ n (fun x => ∫ t, f t x ∂μ) x‖ ≤ C n * μ.real Set.univ := by
  induction n with
  | zero =>
    intro E _ _ _ _ _ _ f _hm _hs C hb x
    simp only [norm_iteratedFDeriv_zero]
    exact norm_integral_le_of_norm_le_const (ae_of_all μ (fun t => by
      simpa only [norm_iteratedFDeriv_zero] using hb 0 (Nat.zero_le _) t x))
  | succ n ih =>
    intro E _ _ _ _ _ _ f hm hs C hb x
    have hd : ∀ t, Differentiable ℝ (f t) := fun t => (hs t).differentiable (by simp)
    have hb₀ : ∀ t y, ‖f t y‖ ≤ C 0 := fun t y => by
      simpa only [norm_iteratedFDeriv_zero] using hb 0 (Nat.zero_le _) t y
    have hb₁ : ∀ t y, ‖fderiv ℝ (f t) y‖ ≤ C 1 := fun t y => by
      simpa only [norm_iteratedFDeriv_one] using hb 1 (by omega) t y
    have hder := finite_parameter_integral_hasFDerivAt μ f hm hd (C 0) (C 1) hb₀ hb₁
    have hs' : ∀ t, ContDiff ℝ (n : ℕ∞) (fderiv ℝ (f t)) := fun t =>
      (hs t).fderiv_right (by simp)
    have hm' : ∀ y, Measurable (fun t => fderiv ℝ (f t) y) := fun y =>
      (finite_fderiv_parameter_stronglyMeasurable f hm hd y).measurable
    have he : fderiv ℝ (fun y => ∫ t, f t y ∂μ) =
        fun y => ∫ t, fderiv ℝ (f t) y ∂μ := funext (fun y => (hder y).fderiv)
    rw [← norm_iteratedFDeriv_fderiv, he]
    exact ih (Vec d →L[ℝ] E) (fun t y => fderiv ℝ (f t) y) hm' hs'
      (fun j => C (j + 1)) (fun j hj t y => by
        rw [norm_iteratedFDeriv_fderiv]
        exact hb (j + 1) (by omega) t y) x

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.Construction.Preservation.FullLift

/-! Inverse-mass row estimates retain one positive matrix for later component time suprema. -/

open CycleComparison.Lift
variable {ι : Type*} [Fintype ι]

theorem weighted_positive_row_norm_square_le (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (M : ι → ι → ℝ) (C K : ℝ) (hK : 0 ≤ K)
    (hM : HasRealSchurBudget (massConjugatedMatrix π M) C)
    (x : ι → ℝ) (v : ι) (y : ℝ) (hy : 0 ≤ y)
    (hbound : y ≤ K * ∑ u, M v u * x u) :
    (π v)⁻¹ * y ^ 2 ≤ K ^ 2 * C *
      ∑ u, massConjugatedMatrix π M v u * ((π u)⁻¹ * x u ^ 2) := by
  have he : (Real.sqrt (π v))⁻¹ * (K * ∑ u, M v u * x u) =
      ∑ u, (K * massConjugatedMatrix π M v u) * ((Real.sqrt (π u))⁻¹ * x u) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [massConjugatedMatrix, Real.sqrt_div (hπ u).le]
    field_simp [(Real.sqrt_pos.mpr (hπ u)).ne', (Real.sqrt_pos.mpr (hπ v)).ne']
  have hrow : (∑ u, K * massConjugatedMatrix π M v u) ≤ K * C := by
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hM.row_sum v) hK
  have hb := positive_row_norm_square_le
    (fun u => K * massConjugatedMatrix π M v u)
    (fun u => (Real.sqrt (π u))⁻¹ * x u) (K * C)
    ((Real.sqrt (π v))⁻¹ * y)
    (fun u => mul_nonneg hK (hM.nonneg v u)) hrow
    (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) hy)
    ((mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr (Real.sqrt_nonneg _))).trans_eq he)
  simp only [inverse_sqrt_mass_square (hπ v).le,
    inverse_sqrt_mass_square (hπ _).le] at hb
  have hs : (∑ u, (K * massConjugatedMatrix π M v u) * ((π u)⁻¹ * x u ^ 2)) =
      K * ∑ u, massConjugatedMatrix π M v u * ((π u)⁻¹ * x u ^ 2) := by
    simp only [Finset.mul_sum, mul_assoc]
  rw [hs] at hb
  exact hb.trans_eq (by ring)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.FullLift

/-! Fixed column budgets control component suprema and dissipation before the energy root. -/

variable {ι κ T : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace T]

theorem paired_matrix_component_time_energy_le (μ : Measure T) (I : Set T)
    (A₀ A₁ : ι → κ → ℝ≥0∞) (C₀ C₁ : ℝ≥0∞)
    (hcol₀ : ∀ j, ∑ i, A₀ i j ≤ C₀) (hcol₁ : ∀ j, ∑ i, A₁ i j ≤ C₁)
    (F₀ F₁ : ι → T → ℝ≥0∞) (G₀ G₁ : κ → T → ℝ≥0∞)
    (hG₁ : ∀ j, AEMeasurable (G₁ j) μ)
    (hb₀ : ∀ i, ∀ t ∈ I, F₀ i t ≤ ∑ j, A₀ i j * G₀ j t)
    (hb₁ : ∀ i, ∀ᵐ t ∂μ, F₁ i t ≤ ∑ j, A₁ i j * G₁ j t) :
    (∑ i, ((⨆ t ∈ I, F₀ i t) + ∫⁻ t, F₁ i t ∂μ)) ≤
      (C₀ + C₁) * ∑ j, ((⨆ t ∈ I, G₀ j t) + ∫⁻ t, G₁ j t ∂μ) := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  calc
    _ ≤ C₀ * (∑ j, ⨆ t ∈ I, G₀ j t) + C₁ * (∑ j, ∫⁻ t, G₁ j t ∂μ) :=
      add_le_add (matrix_component_sup_sum_le A₀ C₀ hcol₀ I F₀ G₀ hb₀)
        (matrix_component_integral_sum_le μ A₁ C₁ hcol₁ F₁ G₁ hG₁ hb₁)
    _ ≤ (C₀ + C₁) * (∑ j, ⨆ t ∈ I, G₀ j t) +
        (C₀ + C₁) * (∑ j, ∫⁻ t, G₁ j t ∂μ) :=
      add_le_add (mul_le_mul' le_self_add le_rfl) (mul_le_mul' le_add_self le_rfl)
    _ = _ := (mul_add _ _ _).symm

variable {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem classicalStrongEnergy_le_of_matrix_bounds (rs ν ρ B : ℝ) (π : ι → ℝ)
    (I : Set ℝ) (K Q : ℕ) (a b : ℝ → Vec 2 → ∀ i, h i)
    (A₀ A₁ : ι → ι → ℝ≥0∞) (C₀ C₁ : ℝ≥0∞)
    (hcol₀ : ∀ j, ∑ i, A₀ i j ≤ C₀) (hcol₁ : ∀ j, ∑ i, A₁ i j ≤ C₁)
    (hG₁ : ∀ j, AEMeasurable (fun t => ENNReal.ofReal B *
      (ENNReal.ofReal (π j)⁻¹ * classicalGradFactorialSq ρ Q (fun x => b t x j)))
        (volume.restrict I))
    (hb₀ : ∀ i, ∀ t ∈ I,
      ENNReal.ofReal (π i)⁻¹ * classicalFactorialSq rs K (fun x => a t x i) ≤
        ∑ j, A₀ i j * (ENNReal.ofReal (π j)⁻¹ *
          classicalFactorialSq ρ Q (fun x => b t x j)))
    (hb₁ : ∀ i, ∀ᵐ t ∂volume.restrict I,
      ENNReal.ofReal ν * (ENNReal.ofReal (π i)⁻¹ *
        classicalGradFactorialSq rs K (fun x => a t x i)) ≤
        ∑ j, A₁ i j * (ENNReal.ofReal B * (ENNReal.ofReal (π j)⁻¹ *
          classicalGradFactorialSq ρ Q (fun x => b t x j)))) :
    classicalStrongEnergy rs ν π I K a ≤
      (C₀ + C₁) ^ (1 / 2 : ℝ) * classicalStrongEnergy ρ B π I Q b := by
  rw [classicalStrongEnergy_weighted_components, classicalStrongEnergy_weighted_components]
  have hs := ENNReal.rpow_le_rpow
    (paired_matrix_component_time_energy_le (volume.restrict I) I A₀ A₁ C₀ C₁ hcol₀ hcol₁
      (fun i t => ENNReal.ofReal (π i)⁻¹ * classicalFactorialSq rs K (fun x => a t x i))
      (fun i t => ENNReal.ofReal ν * (ENNReal.ofReal (π i)⁻¹ *
        classicalGradFactorialSq rs K (fun x => a t x i)))
      (fun j t => ENNReal.ofReal (π j)⁻¹ * classicalFactorialSq ρ Q (fun x => b t x j))
      (fun j t => ENNReal.ofReal B * (ENNReal.ofReal (π j)⁻¹ *
        classicalGradFactorialSq ρ Q (fun x => b t x j))) hG₁ hb₀ hb₁)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)] using hs

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.FullLift

/-! A fixed positive matrix controls separate component spatial energies before time suprema. -/

open CycleComparison.Lift
variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]

theorem weighted_matrix_row_lintegral_le (μ : Measure Ω)
    (π : ι → ℝ) (hπ : ∀ u, 0 < π u) (M : ι → ι → ℝ) (C K : ℝ) (hK : 0 ≤ K)
    (hM : HasRealSchurBudget (massConjugatedMatrix π M) C)
    (x : ι → Ω → ℝ) (hx : ∀ u, AEMeasurable (fun z => ENNReal.ofReal (x u z ^ 2)) μ)
    (v : ι) (y : Ω → ℝ) (hy : ∀ z, 0 ≤ y z)
    (hb : ∀ z, y z ≤ K * ∑ u, M v u * x u z) :
    (∫⁻ z, ENNReal.ofReal ((π v)⁻¹ * y z ^ 2) ∂μ) ≤
      ENNReal.ofReal (K ^ 2 * C) *
        ∑ u, ENNReal.ofReal (massConjugatedMatrix π M v u * (π u)⁻¹) *
          ∫⁻ z, ENNReal.ofReal (x u z ^ 2) ∂μ := by
  have hC : 0 ≤ C := (Finset.sum_nonneg (fun u _ => hM.nonneg v u)).trans (hM.row_sum v)
  have hKC : 0 ≤ K ^ 2 * C := mul_nonneg (sq_nonneg K) hC
  have hA (u : ι) : 0 ≤ massConjugatedMatrix π M v u * (π u)⁻¹ :=
    mul_nonneg (hM.nonneg v u) (inv_nonneg.mpr (hπ u).le)
  have hp (z : Ω) : ENNReal.ofReal ((π v)⁻¹ * y z ^ 2) ≤
      ENNReal.ofReal (K ^ 2 * C) *
        ∑ u, ENNReal.ofReal (massConjugatedMatrix π M v u * (π u)⁻¹) *
          ENNReal.ofReal (x u z ^ 2) := by
    simp_rw [← ENNReal.ofReal_mul (hA _)]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun u _ => mul_nonneg (hA u) (sq_nonneg _)),
      ← ENNReal.ofReal_mul hKC]
    have h := ENNReal.ofReal_le_ofReal
      (weighted_positive_row_norm_square_le π hπ M C K hK hM (fun u => x u z) v (y z) (hy z) (hb z))
    simpa only [mul_assoc] using h
  apply (lintegral_mono hp).trans_eq
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_finsetSum' Finset.univ
      (f := fun u z => ENNReal.ofReal (massConjugatedMatrix π M v u * (π u)⁻¹) *
        ENNReal.ofReal (x u z ^ 2)) (fun u _ => aemeasurable_const.mul (hx u))]
  apply congrArg (fun a : ℝ≥0∞ => ENNReal.ofReal (K ^ 2 * C) * a)
  apply Finset.sum_congr rfl
  intro u _
  exact lintegral_const_mul'' _ (hx u)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Extract the regularizer's top derivative gain from the existing paired factorial estimate. -/

section
open AVRegularity.Analysis.Convolution

theorem exists_paired_kernel_top_derivative_gain {κ : Vec 2 → ℝ}
    (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [CompleteSpace E] [MeasurableSpace E] [BorelSpace E],
    ∀ (R S : Vec 2 ≃L[ℝ] Vec 2) (cH cV : Fin 2 → ℝ)
      (hcoeff : ∀ i, cH i • R (basisVec 0) + cV i • S (basisVec 1) = basisVec i)
      (r : ℝ), 0 < r → (∀ i, |cH i| ≤ 2 / r) → (∀ i, |cV i| ≤ 2 / r) →
    ∀ f : L2 E torusMeasure,
      Real.sqrt (derivativeNormSq
        (pairedWeakSmoothingTorus (K := j) R S κ hc hd cH cV hcoeff f).val
        ⟨j, Nat.lt_succ_self j⟩) ≤ C / r ^ j * ‖f‖ := by
  obtain ⟨D, hD, hgain⟩ := exists_paired_L2_factorial_gain_torus hc hd j
  refine ⟨D * (j.factorial : ℝ), mul_nonneg hD (Nat.cast_nonneg _), ?_⟩
  intro E _ _ _ _ _ R S cH cV hcoeff r hr hH hV f
  have hb := hgain E R S cH cV hcoeff r r hr le_rfl hH hV f
  rw [div_self hr.ne', one_pow, mul_one] at hb
  have ht := (top_derivative_factorial_norm_le
    (pairedWeakSmoothingTorus (K := j) R S κ hc hd cH cV hcoeff f).val r hr.le).trans hb
  have hp : 0 < r ^ j / (j.factorial : ℝ) := div_pos (pow_pos hr _) (by positivity)
  have ht' : Real.sqrt (derivativeNormSq
      (pairedWeakSmoothingTorus (K := j) R S κ hc hd cH cV hcoeff f).val
      ⟨j, Nat.lt_succ_self j⟩) ≤ D * ‖f‖ / (r ^ j / (j.factorial : ℝ)) :=
    (le_div_iff₀ hp).mpr (by rw [mul_comm]; exact ht)
  convert ht' using 1
  field_simp
end

/-! Paired convolution gives the squared zero-input-order regularizer gain. -/

section
open AVRegularity.Analysis.Convolution

theorem exists_paired_kernel_zero_gain {κ : Vec 2 → ℝ}
    (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [CompleteSpace E] [MeasurableSpace E] [BorelSpace E],
    ∀ (R S : Vec 2 ≃L[ℝ] Vec 2) (cH cV : Fin 2 → ℝ)
      (hcoeff : ∀ i, cH i • R (basisVec 0) + cV i • S (basisVec 1) = basisVec i)
      (r : ℝ), 0 < r → (∀ i, |cH i| ≤ 2 / r) → (∀ i, |cV i| ≤ 2 / r) →
    ∀ (f : L2 E torusMeasure) (ρ : ℝ),
      derivFactorialNormSq (K := 0) j ρ
        (pairedWeakSmoothingTorus (K := 0 + j) R S κ hc hd cH cV hcoeff f).val ≤
          (C / r ^ j) ^ 2 * ‖f‖ ^ 2 := by
  obtain ⟨C, hC, hgain⟩ := exists_paired_kernel_top_derivative_gain hc hd (0 + j)
  refine ⟨C, hC, ?_⟩
  intro E _ _ _ _ _ R S cH cV hcoeff r hr hH hV f ρ
  have hb := hgain E R S cH cV hcoeff r hr hH hV f
  have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mpr hb
  rw [Real.sq_sqrt (derivativeNormSq_nonneg _ _), mul_pow] at hsq
  simpa only [derivFactorialNormSq, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero,
    factorialWeight, Nat.mul_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, one_pow,
    div_one, one_mul, add_zero, Nat.zero_add, derivativeNormSq] using hsq
end

/-! Classical representatives commute with the native linear carrier maps and finite sums. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

theorem classicalRep_map {K r : ℕ} (W : TorusHk K E) (a : Vec 2 → E)
    (hrep : IsClassicalRep W a r) (L : E →L[ℝ] F) :
    IsClassicalRep (KernelEnergy.mapTorusHk L W) (fun x => L (a x)) r := by
  refine ⟨hrep.1, L.contDiff.comp hrep.2.1, ?_, ?_⟩
  · intro n x
    exact congrArg L (hrep.2.2.1 n x)
  · intro m hm w
    have hmK := hm.trans hrep.1
    have hmap := KernelEnergy.mapTorusHk_toFunction_jet_ae L W
      ⟨⟨m, Nat.lt_succ_of_le hmK⟩, w⟩
    have hr := hrep.2.2.2 m hm w
    have hd := orderedDerivative_clm_comp L w
      (hrep.2.1.of_le (by exact_mod_cast hm))
    unfold torusJetOrder at hr ⊢
    simp only [hmK, ↓reduceDIte] at hr ⊢
    filter_upwards [hmap, hr] with x hx hy
    rw [hx, hy, hd]

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F]
  [BorelSpace F] [CompleteSpace F] in
 theorem classicalRep_sum {ι : Type*} [Fintype ι] {K r : ℕ} (hrK : r ≤ K)
    (W : ι → TorusHk K E) (a : ι → Vec 2 → E)
    (hrep : ∀ i, IsClassicalRep (W i) (a i) r) :
    IsClassicalRep (∑ i, W i) (fun x => ∑ i, a i x) r := by
  refine ⟨hrK, ContDiff.sum (fun i _ => (hrep i).2.1), ?_, ?_⟩
  · intro n x
    exact Finset.sum_congr rfl fun i _ => (hrep i).2.2.1 n x
  · intro m hm w
    have hmK := hm.trans hrK
    have hj := KernelEnergy.torusJet_sum_ae W ⟨⟨m, Nat.lt_succ_of_le hmK⟩, w⟩
    have hr (i : ι) := (hrep i).2.2.2 m hm w
    have hd := orderedDerivative_finite_sum w a
      (fun i => (hrep i).2.1.of_le (by exact_mod_cast hm))
    unfold torusJetOrder at hr ⊢
    simp only [hmK, ↓reduceDIte] at hr ⊢
    filter_upwards [hj, ae_all_iff.mpr hr] with x hx hy
    rw [hx, hd]
    exact Finset.sum_congr rfl fun i _ => hy i
end

/-! Scalar and zero arithmetic of chosen classical periodic representatives. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem classicalRep_smul {K r : ℕ} (W : TorusHk K E) (a : Vec 2 → E)
    (hrep : IsClassicalRep W a r) (q : ℝ) :
    IsClassicalRep (q • W) (fun x => q • a x) r := by
  refine ⟨hrep.1, hrep.2.1.const_smul q, ?_, ?_⟩
  · intro n x
    exact congrArg (fun z => q • z) (hrep.2.2.1 n x)
  · intro m hm w
    have hmK := hm.trans hrep.1
    have hj := KernelEnergy.torusJet_smul_ae q W ⟨⟨m, Nat.lt_succ_of_le hmK⟩, w⟩
    have hr := hrep.2.2.2 m hm w
    have hd := orderedDerivative_clm_comp (q • ContinuousLinearMap.id ℝ E) w
      (hrep.2.1.of_le (by exact_mod_cast hm))
    change orderedDerivative w (fun x => q • a x) = fun x => q • orderedDerivative w a x at hd
    unfold torusJetOrder at hr ⊢
    simp only [hmK, ↓reduceDIte] at hr ⊢
    filter_upwards [hj, hr] with x hx hy
    rw [hx, hy, hd]

theorem classicalRep_zero {K r : ℕ} (hrK : r ≤ K) :
    IsClassicalRep (0 : TorusHk K E) (fun _ => 0) r := by
  refine ⟨hrK, contDiff_const, ?_, ?_⟩
  · intro _ _
    rfl
  · intro m hm w
    have hmK := hm.trans hrK
    unfold torusJetOrder
    simp only [hmK, ↓reduceDIte, orderedDerivative_const_zero]
    have hj := KernelEnergy.torusHk_toFunction_jet_ae (0 : TorusHk K E) ⟨⟨m, Nat.lt_succ_of_le hmK⟩, w⟩
    exact hj.trans (Lp.coeFn_zero E 2 (volume.restrict AVenhance.unitCube))
end

/-! Finite linearity of cellInner for continuous periodic-cell fields. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem cellInner_sum_left {ι : Type*} [Fintype ι] (f : ι → Vec 2 → E) (q : Vec 2 → E)
    (hf : ∀ i, Continuous (f i)) (hq : Continuous q) :
    cellInner (fun x => ∑ i, f i x) q = ∑ i, cellInner (f i) q := by
  unfold cellInner
  simp only [sum_inner]
  exact integral_finsetSum Finset.univ fun i _ =>
    CoupledEnergy.Galerkin.continuous_cell_integrable _ ((hf i).inner hq)

theorem cellInner_sum_right {ι : Type*} [Fintype ι] (f : Vec 2 → E) (q : ι → Vec 2 → E)
    (hf : Continuous f) (hq : ∀ i, Continuous (q i)) :
    cellInner f (fun x => ∑ i, q i x) = ∑ i, cellInner f (q i) := by
  unfold cellInner
  simp only [inner_sum]
  exact integral_finsetSum Finset.univ fun i _ =>
    CoupledEnergy.Galerkin.continuous_cell_integrable _ (hf.inner (hq i))

theorem cellInner_smul_left (c : ℝ) (f q : Vec 2 → E) :
    cellInner (fun x => c • f x) q = c * cellInner f q := by
  unfold cellInner
  simp only [real_inner_smul_left, integral_const_mul]

theorem cellInner_smul_right (c : ℝ) (f q : Vec 2 → E) :
    cellInner f (fun x => c • q x) = c * cellInner f q := by
  unfold cellInner
  simp only [real_inner_smul_right, integral_const_mul]

theorem cellInner_finset_sum_left {ι : Type*} (s : Finset ι) (f : ι → Vec 2 → E) (q : Vec 2 → E)
    (hf : ∀ i ∈ s, Continuous (f i)) (hq : Continuous q) :
    cellInner (fun x => ∑ i ∈ s, f i x) q = ∑ i ∈ s, cellInner (f i) q := by
  unfold cellInner
  simp only [sum_inner]
  exact integral_finsetSum s fun i hi =>
    CoupledEnergy.Galerkin.continuous_cell_integrable _ ((hf i hi).inner hq)

theorem cellInner_finset_sum_right {ι : Type*} (s : Finset ι) (f : Vec 2 → E) (q : ι → Vec 2 → E)
    (hf : Continuous f) (hq : ∀ i ∈ s, Continuous (q i)) :
    cellInner f (fun x => ∑ i ∈ s, q i x) = ∑ i ∈ s, cellInner f (q i) := by
  unfold cellInner
  simp only [inner_sum]
  exact integral_finsetSum s fun i hi =>
    CoupledEnergy.Galerkin.continuous_cell_integrable _ (hf.inner (hq i hi))
end

/-! Exact double integration by parts for finite-regularity periodic Hilbert fields. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem classical_second_partial_adjoint (u q : Vec 2 → E)
    (hu : ContDiff ℝ 2 u) (hq : ContDiff ℝ 2 q)
    (hpu : AVenhance.IsZ2Periodic u) (hpq : AVenhance.IsZ2Periodic q) (i j : Fin 2) :
    (∫ x in AVenhance.unitCube,
      inner ℝ (fderiv ℝ (fun y => fderiv ℝ u y (basisVec j)) x (basisVec i)) (q x)) =
    ∫ x in AVenhance.unitCube,
      inner ℝ (u x) (fderiv ℝ (fun y => fderiv ℝ q y (basisVec i)) x (basisVec j)) := by
  have hdu : ContDiff ℝ 1 (fun x => fderiv ℝ u x (basisVec j)) :=
    (hu.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hdq : ContDiff ℝ 1 (fun x => fderiv ℝ q x (basisVec i)) :=
    (hq.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hDpu := fderiv_isZ2Periodic (hu.differentiable (by norm_num)) hpu
  have hDpq := fderiv_isZ2Periodic (hq.differentiable (by norm_num)) hpq
  have h1 := CoupledEnergy.Variational.periodic_hilbert_partial_ibp
    (fun x => fderiv ℝ u x (basisVec j)) q hdu (hq.of_le (by norm_num))
    (fun n x => congrArg (fun L => L (basisVec j)) (hDpu n x)) hpq i
  have h2 := CoupledEnergy.Variational.periodic_hilbert_partial_ibp
    u (fun x => fderiv ℝ q x (basisVec i)) (hu.of_le (by norm_num)) hdq
    hpu (fun n x => congrArg (fun L => L (basisVec i)) (hDpq n x)) j
  rw [h1, h2, neg_neg]
end

/-! The literal symmetric covariance operator is self-adjoint on periodic classical fields. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem covOperator_cellInner_adjoint (Hc : Matrix (Fin 2) (Fin 2) ℝ)
    (hH : ∀ i j, Hc i j = Hc j i) (u q : Vec 2 → E)
    (hu : ContDiff ℝ 2 u) (hq : ContDiff ℝ 2 q)
    (hpu : AVenhance.IsZ2Periodic u) (hpq : AVenhance.IsZ2Periodic q) :
    cellInner (covOperator Hc u) q = cellInner u (covOperator Hc q) := by
  let D2 (f : Vec 2 → E) (i j : Fin 2) :=
    fun x => fderiv ℝ (fun y => fderiv ℝ f y (basisVec j)) x (basisVec i)
  have hcont (f : Vec 2 → E) (hf : ContDiff ℝ 2 f) (i j : Fin 2) : Continuous (D2 f i j) := by
    have hd : ContDiff ℝ 1 (fun x => fderiv ℝ f x (basisVec j)) :=
      (hf.fderiv_right (by norm_num)).clm_apply contDiff_const
    exact (hd.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hleft : cellInner (covOperator Hc u) q =
      ∑ i : Fin 2, ∑ j : Fin 2, Hc i j * cellInner (D2 u i j) q := by
    change cellInner (fun x => ∑ i : Fin 2, ∑ j : Fin 2, Hc i j • D2 u i j x) q = _
    rw [cellInner_sum_left (fun (i : Fin 2) x => ∑ j : Fin 2, Hc i j • D2 u i j x) q
      (fun i => (continuous_finsetSum Finset.univ (fun j _ => continuous_const.smul (hcont u hu i j))))
      hq.continuous]
    apply Finset.sum_congr rfl
    intro i _
    rw [cellInner_sum_left (fun (j : Fin 2) x => Hc i j • D2 u i j x) q (fun j => continuous_const.smul (hcont u hu i j)) hq.continuous]
    exact Finset.sum_congr rfl fun j _ => cellInner_smul_left (Hc i j) (D2 u i j) q
  have hright : cellInner u (covOperator Hc q) =
      ∑ i : Fin 2, ∑ j : Fin 2, Hc i j * cellInner u (D2 q i j) := by
    change cellInner u (fun x => ∑ i : Fin 2, ∑ j : Fin 2, Hc i j • D2 q i j x) = _
    rw [cellInner_sum_right u (fun (i : Fin 2) x => ∑ j : Fin 2, Hc i j • D2 q i j x) hu.continuous
      (fun i => continuous_finsetSum Finset.univ (fun j _ => continuous_const.smul (hcont q hq i j)))]
    apply Finset.sum_congr rfl
    intro i _
    rw [cellInner_sum_right u (fun (j : Fin 2) x => Hc i j • D2 q i j x) hu.continuous (fun j => continuous_const.smul (hcont q hq i j))]
    exact Finset.sum_congr rfl fun j _ => cellInner_smul_right (Hc i j) u (D2 q i j)
  rw [hleft, hright]
  have hterm (i j : Fin 2) : cellInner (D2 u i j) q = cellInner u (D2 q j i) :=
    classical_second_partial_adjoint u q hu hq hpu hpq i j
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hH j i]
end

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Higher-reserve witnesses supply every requested lower stored lift order. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem liftSequence_order_mono (Q : LiftOperatorData ι h D) {sX sZ rX rZ : ℕ}
    (hX : rX ≤ sX) (hZ : rZ ≤ sZ) (a b : ℝ) (N H : ℕ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hc : IsLiftSequence Q sX sZ a b N H Cc) :
    IsLiftSequence Q rX rZ a b N H Cc := by
  refine ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, ?_, ?_⟩
  · intro hh hhh n m α v u t ht
    have hs := hc.2.2.2.2.2.1 hh hhh n m α v u t ht
    exact ⟨IsBoxSmooth.mono hX hZ hs.1, hs.2⟩
  · intro hh hhh n hn hnN f hf X
    exact CycleComparison.Lift.cellFieldInverse_order_mono _ _ sZ rZ hZ a b 0 _ _
      (hc.2.2.2.2.2.2 hh hhh n hn hnN f hf X)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public section
namespace AVRegularity.Construction.Preservation.FullLift

/-! The retained actual successor uses a subset of the same extended parent-word component set. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

theorem retained_comps_subset_succExt {P : ProvParams} {Mn : SuccMenu}
    {G G' : GenStage D hr Dm b j₀} (hactual : IsActualSuccessor D P Mn G G')
    {m : ℕ} (hlevel : G.level = m) :
    (G'.retained m Mn.H Mn.J).comps ⊆ succExtComps m Mn.A Mn.J G.comps := by
  intro c hc
  change c ∈ G'.comps.filter (IsRetained m Mn.H Mn.J) at hc
  have he := (Finset.mem_filter.mp hc).1
  rw [hactual.2.2.1, hlevel] at he
  exact he

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Change only the initial datum of a native solution along a pointwise equality. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

theorem native_reg_solution_initial_congr (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G : GenStage D hr Dm bw j₀)
    (ν a b : ℝ) (bv : ℝ → Vec 2 → Vec 2) (k : ℕ)
    (f g : ∀ v : CompIn G.comps, TorusHk k (hr v.1.root))
    (U : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root))
    (W : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root))
    (Y : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root))
    (hfg : ∀ v, f v = g v)
    (hsol : G.IsRegSolution P seedK freshK φ₀ hφ₀ ν bv k a b f
      (fun _ _ => 0) (fun _ _ => 0) U W Y) :
    G.IsRegSolution P seedK freshK φ₀ hφ₀ ν bv k a b g
      (fun _ _ => 0) (fun _ _ => 0) U W Y := by
  have hf : f = g := funext hfg
  exact hf ▸ hsol

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Construction.Preservation.FullLift

/-! The literal finite readout preserves time integrability, including its root transports. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]

theorem memLp_rootCast {r r' K : ℕ} (heq : r = r') {μ : Measure ℝ} {p : ℝ≥0∞}
    (u : ℝ → TorusHk K (hr r)) (hu : MemLp u p μ) :
    MemLp (fun t => cast (congrArg (fun s => TorusHk K (hr s)) heq) (u t)) p μ := by
  subst r'
  exact hu

theorem memLp_succReadout {S S' : Finset Comp} {K : ℕ} (m : ℕ) (E η : ℝ)
    {μ : Measure ℝ} {p : ℝ≥0∞}
    (u : ∀ c : CompIn S', ℝ → TorusHk K (hr c.1.root))
    (hu : ∀ c, MemLp (u c) p μ) (v : CompIn S) :
    MemLp (fun t => succReadout m E η K (fun c => u c t) v) p μ := by
  classical
  let : NormedAddCommGroup (TorusHk K (hr v.1.root)) := inferInstance
  let : ESeminormedAddMonoid (TorusHk K (hr v.1.root)) := inferInstance
  let f : CompIn S' → ℝ → TorusHk K (hr v.1.root) := fun c t =>
    if heq : compParent m c.1 = v.1 then
      E ^ (η * (compWord m c.1).length) •
        cast (congrArg (fun r => TorusHk K (hr r))
          ((compParent_root m c.1).symm.trans (congrArg Comp.root heq))) (u c t)
    else 0
  change MemLp (fun t => ∑ c, f c t) p μ
  refine memLp_finsetSum Finset.univ (f := f) ?_
  intro c _
  by_cases h : compParent m c.1 = v.1
  · simp only [f, h, ↓reduceDIte]
    exact (memLp_rootCast ((compParent_root m c.1).symm.trans (congrArg Comp.root h))
      (u c) (hu c)).const_smul (E ^ (η * (compWord m c.1).length) : ℝ)
  · simp only [f, h, ↓reduceDIte]
    exact (MemLp.zero' : MemLp (fun _ : ℝ => (0 : TorusHk K (hr v.1.root))) p μ)

theorem memLp_truncated_succReadout {S S' : Finset Comp} {K L : ℕ}
    (hKL : K ≤ L) (m : ℕ) (E η : ℝ) {μ : Measure ℝ} {p : ℝ≥0∞}
    (u : ∀ c : CompIn S', ℝ → TorusHk L (hr c.1.root))
    (hu : ∀ c, MemLp (u c) p μ) (v : CompIn S) :
    MemLp (fun t => truncateTorusHk hKL (succReadout m E η L (fun c => u c t) v)) p μ :=
  (truncateTorusHk hKL).comp_memLp' (memLp_succReadout m E η u hu v)

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Sobolev truncation commutes with the literal parent readout and its root casts. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]

theorem truncate_rootCast {r r' K L : ℕ} (hKL : K ≤ L) (h : r = r')
    (X : TorusHk L (hr r)) :
    truncateTorusHk hKL (cast (congrArg (fun s => TorusHk L (hr s)) h) X) =
      cast (congrArg (fun s => TorusHk K (hr s)) h) (truncateTorusHk hKL X) := by
  subst r'
  rfl

theorem truncate_succReadout {S S' : Finset Comp} {K L : ℕ} (hKL : K ≤ L)
    (m : ℕ) (E η : ℝ) (X : ∀ c : CompIn S', TorusHk L (hr c.1.root)) (v : CompIn S) :
    truncateTorusHk hKL (succReadout m E η L X v) =
      succReadout m E η K (fun c => truncateTorusHk hKL (X c)) v := by
  classical
  unfold succReadout
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs with h
  · rw [map_smul, truncate_rootCast hKL
      ((compParent_root m c.1).symm.trans (congrArg Comp.root h))]
  · exact map_zero _
end

/-! The original retained gradient representative remains compatible after readout and order restriction. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]

theorem truncateTorusHk_comp_apply {r K L M : ℕ} (hKL : K ≤ L) (hLM : L ≤ M)
    (u : TorusHk M (hr r)) :
    truncateTorusHk hKL (truncateTorusHk hLM u) = truncateTorusHk (hKL.trans hLM) u := by
  apply Subtype.ext
  apply PiLp.ext
  intro a
  rfl

theorem readout_gradient_compatible_ae {S S' : Finset Comp} {K L : ℕ}
    (hKL : K ≤ L) (m : ℕ) (E η : ℝ) (μ : Measure ℝ)
    (u : ∀ c : CompIn S', ℝ → TorusHk L (hr c.1.root))
    (w : ∀ c : CompIn S', ℝ → TorusHk (L + 1) (hr c.1.root))
    (hw : ∀ c, ∀ᵐ t ∂μ, truncateTorusHk (Nat.le_succ L) (w c t) = u c t)
    (v : CompIn S) :
    ∀ᵐ t ∂μ,
      truncateTorusHk (Nat.le_succ K)
        (truncateTorusHk (Nat.succ_le_succ hKL)
          (succReadout m E η (L + 1) (fun c => w c t) v)) =
      truncateTorusHk hKL (succReadout m E η L (fun c => u c t) v) := by
  have hall := Filter.eventually_all.mpr hw
  filter_upwards [hall] with t ht
  rw [truncateTorusHk_comp_apply]
  have he : truncateTorusHk hKL
      (truncateTorusHk (Nat.le_succ L) (succReadout m E η (L + 1) (fun c => w c t) v)) =
      truncateTorusHk hKL (succReadout m E η L (fun c => u c t) v) := by
    rw [truncate_succReadout]
    simp only [ht]
  simpa only [truncateTorusHk_comp_apply] using he
end

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.FullLift

/-! The molecular part makes every sampled reference ellipse nonsingular. -/

theorem diagSqrt_det_ne_zero {J : Matrix (Fin 2) (Fin 2) ℝ}
    (hJ : ∀ i, 0 < J i i) : (diagSqrt J).det ≠ 0 := by
  rw [diagSqrt, Matrix.det_diagonal]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact (Real.sqrt_pos.mpr (hJ i)).ne'

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.FullLift

/-! Native covariance images are uniquely determined by their smooth periodic duality tests. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem cellInner_scalar_coordinate (F : Vec 2 → E) (φ : Vec 2 → ℝ) (e : E) :
    cellInner (fun x => inner ℝ e (F x)) φ = cellInner F (fun x => φ x • e) := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [real_inner_smul_right, RCLike.inner_apply, conj_trivial]
    rw [real_inner_comm (F x) e]

omit [MeasurableSpace E] [BorelSpace E] in
theorem hilbert_ae_eq_of_cellInner_eq {F G : Vec 2 → E}
    (hF : IntegrableOn F AVenhance.unitCube) (hG : IntegrableOn G AVenhance.unitCube)
    (h : ∀ φ : Vec 2 → E, ContDiff ℝ (⊤ : ℕ∞) φ → AVenhance.IsZ2Periodic φ →
      cellInner F φ = cellInner G φ) : F =ᵐ[volume.restrict AVenhance.unitCube] G := by
  have hc (i : Fin (Module.finrank ℝ E)) :
      (fun x => inner ℝ (stdOrthonormalBasis ℝ E i) (F x)) =ᵐ[volume.restrict AVenhance.unitCube]
        fun x => inner ℝ (stdOrthonormalBasis ℝ E i) (G x) := by
    let e := stdOrthonormalBasis ℝ E i
    apply InitialValue.ae_eq_of_cellInner_eq
      ((InnerProductSpace.toDual ℝ E e).integrable_comp hF)
      ((InnerProductSpace.toDual ℝ E e).integrable_comp hG)
    intro φ hφ hpφ
    change cellInner (fun x => inner ℝ e (F x)) φ = cellInner (fun x => inner ℝ e (G x)) φ
    rw [cellInner_scalar_coordinate F φ e, cellInner_scalar_coordinate G φ e]
    exact h (fun x => φ x • e) (hφ.smul contDiff_const)
      (fun n x => congrArg (fun z : ℝ => z • e) (hpφ n x))
  filter_upwards [ae_all_iff.mpr hc] with x hx
  rw [← (stdOrthonormalBasis ℝ E).sum_repr' (F x), ← (stdOrthonormalBasis ℝ E).sum_repr' (G x)]
  exact Finset.sum_congr rfl fun i _ => congrArg
    (fun z : ℝ => z • stdOrthonormalBasis ℝ E i) (hx i)

theorem covImage_unique {K L : ℕ} (P : (Vec 2 → E) → Vec 2 → E)
    (Z : TorusHk K E) (W W' : TorusHk L E) (hW : IsCovImage P Z W) (hW' : IsCovImage P Z W') :
    W = W' := by
  apply InitialValue.torusHk_ext_of_jet_ae
  apply hilbert_ae_eq_of_cellInner_eq
    (InitialValue.torusHk_integrableOn_jet W (valueIndex2 L))
    (InitialValue.torusHk_integrableOn_jet W' (valueIndex2 L))
  intro φ hφ hpφ
  exact (hW φ hφ hpφ).trans (hW' φ hφ hpφ).symm

end AVRegularity.Construction.Preservation.FullLift
end
end

section
@[expose] public section
namespace AVRegularity.Construction.Preservation.FullLift

/-! Every incoming component is retained, with the empty new word, in an actual cascade step. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

theorem incoming_mem_retained {P : ProvParams} {Mn : SuccMenu}
    {G G' : GenStage D hr Dm b j₀} (hactual : IsActualSuccessor D P Mn G G')
    {m : ℕ} (hlevel : G.level = m)
    (hold : ∀ v ∈ G.comps, ∀ e ∈ v.births, m ≤ e.scale)
    (hgrade : ∀ v ∈ G.comps, compGrade v ≤ Mn.H) :
    G.comps ⊆ (G'.retained m Mn.H Mn.J).comps := by
  have hm : 1 ≤ m := hlevel ▸ hactual.1
  intro c hc
  change c ∈ G'.comps.filter (IsRetained m Mn.H Mn.J)
  rw [Finset.mem_filter, hactual.2.2.1, hlevel]
  refine ⟨Finset.mem_union_left _ hc, hgrade c hc, ?_⟩
  rw [(InitialValue.compParent_eq_self hm (hold c hc)).2]
  exact Nat.zero_le _

theorem incoming_mem_retained_of_cascade {P : ProvParams} {Mn : SuccMenu}
    {seed G G' : GenStage D hr Dm b j₀}
    (hseed : ∀ v : CompIn seed.comps, v.1.births = [])
    (hG : IsCascadeStage D P Mn seed G) (hactual : IsActualSuccessor D P Mn G G')
    {m : ℕ} (hlevel : G.level = m) :
    G.comps ⊆ (G'.retained m Mn.H Mn.J).comps := by
  have hinv := InitialValue.cascade_invariant hseed hG
  exact incoming_mem_retained hactual hlevel
    (fun v hv e he => hlevel ▸ (hinv v hv).1 e he) (fun v hv => (hinv v hv).2)
end

/-! A readout fiber is indexed injectively by the fixed finite word menu. Its size does not
increase with the number of roots or with the length of the cascade. -/

theorem succComp_parent_word (m : ℕ) (c : Comp) :
    succComp m (compParent m c) (compWord m c) = c := by
  rcases c with ⟨r, bs⟩
  cases bs with
  | nil => simp [compParent, compWord, succComp]
  | cons e rest =>
    by_cases he : e.scale = m - 1
    · simp only [compParent, compWord, he, ↓reduceIte]
      simp only [succComp, e.word_ne_nil, ↓reduceDIte]
      congr 1
      congr 1
      cases e
      simp_all
    · simp [compParent, compWord, he, succComp]

theorem parent_word_succComp {m : ℕ} (hm : 1 ≤ m) (v : Comp)
    (hold : ∀ e ∈ v.births, m ≤ e.scale) (t : List WordLetter) :
    compParent m (succComp m v t) = v ∧ compWord m (succComp m v t) = t := by
  by_cases ht : t = []
  · subst t
    simpa only [succComp, ↓reduceDIte] using InitialValue.compParent_eq_self hm hold
  · simp [succComp, ht, compParent, compWord]

theorem readout_word_mem {m : ℕ} (hm : 1 ≤ m) {A : Finset WordLetter}
    {J : ℕ} {S : Finset Comp} (hold : ∀ v ∈ S, ∀ e ∈ v.births, m ≤ e.scale)
    {c : Comp} (hc : c ∈ succExtComps m A J S) :
    compWord m c ∈ insert [] (wordsUpTo A (J + 1)) := by
  rcases Finset.mem_union.mp hc with hc | hc
  · rw [(InitialValue.compParent_eq_self hm (hold c hc)).2]
    exact Finset.mem_insert_self _ _
  · obtain ⟨⟨v, t⟩, hvt, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨hv, ht⟩ := Finset.mem_product.mp hvt
    rw [(parent_word_succComp hm v (hold v hv) t).2]
    exact Finset.mem_insert_of_mem ht

/-! The word-menu bound on the actual finite component index type used by the readout. -/

theorem readout_indexed_fiber_card_le {m : ℕ} (hm : 1 ≤ m) {A : Finset WordLetter}
    {J : ℕ} {S S' : Finset Comp} (hold : ∀ v ∈ S, ∀ e ∈ v.births, m ≤ e.scale)
    (hsub : S' ⊆ succExtComps m A J S) (v : Comp) :
    ((Finset.univ : Finset (CompIn S')).filter fun c => compParent m c.1 = v).card ≤
      (wordsUpTo A (J + 1)).card + 1 := by
  have hcard : ((Finset.univ : Finset (CompIn S')).filter fun c => compParent m c.1 = v).card ≤
      (insert [] (wordsUpTo A (J + 1))).card := by
    apply Finset.card_le_card_of_injOn (fun c : CompIn S' => compWord m c.1)
    · intro c _hc
      exact readout_word_mem hm hold (hsub c.2)
    · intro c hc d hd hword
      change compWord m c.1 = compWord m d.1 at hword
      apply Subtype.ext
      have hcp := (Finset.mem_filter.mp hc).2
      have hdp := (Finset.mem_filter.mp hd).2
      calc
        c.1 = succComp m v (compWord m c.1) := by
          rw [← hcp]; exact (succComp_parent_word m c.1).symm
        _ = succComp m v (compWord m d.1) := by rw [hword]
        _ = d.1 := by rw [← hdp]; exact succComp_parent_word m d.1
  exact hcard.trans (Finset.card_insert_le _ _)

end AVRegularity.Construction.Preservation.FullLift
end
end
