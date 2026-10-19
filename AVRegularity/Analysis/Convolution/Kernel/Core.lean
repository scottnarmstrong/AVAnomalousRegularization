-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module
public import Homogenization.Ambient.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

/-! L² convolution operators: composition, adjoints and autocorrelation. -/

@[expose] public section
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.Analysis.Convolution

section General

variable {X E : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure X} [μ.IsAddLeftInvariant]

abbrev L2 (E : Type*) [NormedAddCommGroup E] (μ : Measure X) := Lp E 2 μ

/-- Literal translation `f(y-x)` on the L² equivalence class. -/
def translation (x : X) : L2 E μ →ₗᵢ[ℝ] L2 E μ :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun y : X => -x + y) (measurePreserving_add_left μ (-x))

theorem translation_norm (x : X) (f : L2 E μ) : ‖translation x f‖ = ‖f‖ :=
  (translation x).norm_map f

theorem translation_ae (x : X) (f : L2 E μ) :
    translation x f =ᵐ[μ] fun y => f (y - x) := by
  have h := Lp.coeFn_compMeasurePreserving f (measurePreserving_add_left μ (-x))
  change translation x f =ᵐ[μ] (fun y => f (-x + y)) at h
  filter_upwards [h] with y hy
  simpa only [sub_eq_add_neg, add_comm] using hy

variable [R1Space X] [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]

local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

omit [R1Space X] [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop] in
theorem translation_add (x y : X) (f : L2 E μ) :
    translation (x + y) f = translation x (translation y f) := by
  change (DomAddAct.mk (-(x + y))) +ᵥ f =
    (DomAddAct.mk (-x)) +ᵥ ((DomAddAct.mk (-y)) +ᵥ f)
  rw [neg_add, DomAddAct.mk_add,
    add_comm (DomAddAct.mk (-y)) (DomAddAct.mk (-x)), ← vadd_vadd]

omit [R1Space X] [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop] in
@[simp] theorem translation_zero (f : L2 E μ) : translation (0 : X) f = f := by
  change (DomAddAct.mk (-(0 : X))) +ᵥ f = f
  simp only [neg_zero, DomAddAct.mk_zero, zero_vadd]

theorem continuous_translation (f : L2 E μ) : Continuous fun x : X => translation x f := by
  change Continuous fun x : X => (DomAddAct.mk (-x)) +ᵥ f
  exact (DomAddAct.continuous_mk.comp continuous_neg).vadd continuous_const

/-- Bochner integral in L², taken for each input, rather than in operator norm. -/
def average [CompleteSpace E] (ρ : Homogenization.Vec 2 →+ X) (κ : Homogenization.Vec 2 → ℝ)
    (f : L2 E μ) : L2 E μ :=
  ∫ z : Homogenization.Vec 2, κ z • translation (ρ z) f

variable [CompleteSpace E]

omit [CompleteSpace E] in
theorem integrable_average_integrand (ρ : Homogenization.Vec 2 →+ X) (hρ : Continuous ρ)
    {κ : Homogenization.Vec 2 → ℝ} (hκ : Integrable κ) (f : L2 E μ) :
    Integrable (fun z : Homogenization.Vec 2 => κ z • translation (ρ z) f) := by
  exact hκ.smul_bdd ‖f‖ ((continuous_translation f).comp hρ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => (translation_norm (ρ z) f).le)

omit [R1Space X] [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop] in
theorem average_norm_le (ρ : Homogenization.Vec 2 →+ X)
    (κ : Homogenization.Vec 2 → ℝ) (f : L2 E μ) :
    ‖average ρ κ f‖ ≤ (∫ z : Homogenization.Vec 2, ‖κ z‖) * ‖f‖ := by
  calc
    ‖average ρ κ f‖ ≤ ∫ z : Homogenization.Vec 2, ‖κ z • translation (ρ z) f‖ :=
      norm_integral_le_integral_norm _
    _ = (∫ z : Homogenization.Vec 2, ‖κ z‖) * ‖f‖ := by
      simp only [norm_smul, translation_norm]
      exact integral_mul_const _ _

/-- The bounded linear averaging operator with its literal L² Bochner integral. -/
def averagingOperator (ρ : Homogenization.Vec 2 →+ X) (hρ : Continuous ρ)
    (κ : Homogenization.Vec 2 → ℝ) (hκ : Integrable κ) : L2 E μ →L[ℝ] L2 E μ :=
  LinearMap.mkContinuous
    { toFun := average ρ κ
      map_add' := fun f g => by
        change (∫ z : Homogenization.Vec 2, κ z • translation (ρ z) (f + g)) = _
        simp only [map_add, smul_add]
        exact integral_add (integrable_average_integrand ρ hρ hκ f)
          (integrable_average_integrand ρ hρ hκ g)
      map_smul' := fun c f => by
        change (∫ z : Homogenization.Vec 2, κ z • translation (ρ z) (c • f)) = _
        simp only [map_smul, smul_comm (κ _) c]
        exact integral_smul c _ }
    (∫ z : Homogenization.Vec 2, ‖κ z‖) (average_norm_le ρ κ)

@[simp] theorem averagingOperator_apply (ρ : Homogenization.Vec 2 →+ X) (hρ : Continuous ρ)
    (κ : Homogenization.Vec 2 → ℝ) (hκ : Integrable κ) (f : L2 E μ) :
    averagingOperator ρ hρ κ hκ f = ∫ z : Homogenization.Vec 2, κ z • translation (ρ z) f := rfl

theorem averagingOperator_norm_le (ρ : Homogenization.Vec 2 →+ X) (hρ : Continuous ρ)
    (κ : Homogenization.Vec 2 → ℝ) (hκ : Integrable κ) :
    ‖averagingOperator (E := E) (μ := μ) ρ hρ κ hκ‖ ≤ ∫ z : Homogenization.Vec 2, ‖κ z‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg fun _ => norm_nonneg _)
  exact average_norm_le ρ κ

theorem averagingOperator_contraction (ρ : Homogenization.Vec 2 →+ X) (hρ : Continuous ρ)
    (φ : Homogenization.Vec 2 → ℝ) (hφ : Integrable φ) (hpos : ∀ᵐ z, 0 ≤ φ z)
    (hmass : ∫ z, φ z = 1) : ‖averagingOperator (E := E) (μ := μ) ρ hρ φ hφ‖ ≤ 1 := by
  have hn : (∫ z, ‖φ z‖) = 1 := by
    rw [integral_congr_ae (hpos.mono fun z hz => Real.norm_of_nonneg hz), hmass]
  exact (averagingOperator_norm_le ρ hρ φ hφ).trans_eq hn

omit [CompleteSpace E] in
/-- Absolute integrability for the translated double average, proved from the
scalar L¹ kernels and the actual translation isometry. -/
theorem integrable_double_average (ρ : Homogenization.Vec 2 →+ X) (hρ : Continuous ρ)
    {κ ψ : Homogenization.Vec 2 → ℝ} (hκ : Integrable κ) (hψ : Integrable ψ) (f : L2 E μ) :
    Integrable (fun p : Homogenization.Vec 2 × Homogenization.Vec 2 =>
      κ p.1 • ψ p.2 • translation (ρ (p.1 + p.2)) f) (volume.prod volume) := by
  have ht : Continuous (fun p : Homogenization.Vec 2 × Homogenization.Vec 2 =>
      translation (ρ (p.1 + p.2)) f) :=
    (continuous_translation f).comp (hρ.comp (continuous_fst.add continuous_snd))
  apply ((hκ.norm.mul_prod hψ.norm).mul_const ‖f‖).mono'
    (hκ.aestronglyMeasurable.comp_fst.smul (hψ.aestronglyMeasurable.comp_snd.smul
      ht.aestronglyMeasurable))
  exact Filter.Eventually.of_forall fun p => by
    change ‖κ p.1 • ψ p.2 • translation (ρ (p.1 + p.2)) f‖ ≤
      (‖κ p.1‖ * ‖ψ p.2‖) * ‖f‖
    simp only [norm_smul, translation_norm, mul_assoc, le_refl]

/-- Literal scalar convolution on the Euclidean kernel variable. -/
def kernelConvolution (κ ψ : Homogenization.Vec 2 → ℝ) : Homogenization.Vec 2 → ℝ :=
  convolution κ ψ (ContinuousLinearMap.mul ℝ ℝ) volume

theorem integrable_kernelConvolution {κ ψ : Homogenization.Vec 2 → ℝ}
    (hκ : Integrable κ) (hψ : Integrable ψ) : Integrable (kernelConvolution κ ψ) :=
  hκ.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hψ

theorem kernelConvolution_comm (κ ψ : Homogenization.Vec 2 → ℝ) :
    kernelConvolution κ ψ = kernelConvolution ψ κ := by
  exact convolution_symm (ContinuousLinearMap.mul ℝ ℝ) (by
    simp only [ContinuousLinearMap.flip_mul])

omit [R1Space X] [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop] in
theorem average_average (ρ : Homogenization.Vec 2 →+ X)
    (κ ψ : Homogenization.Vec 2 → ℝ) (f : L2 E μ) :
    average ρ κ (average ρ ψ f) =
      ∫ z : Homogenization.Vec 2, ∫ w : Homogenization.Vec 2,
        κ z • ψ w • translation (ρ (z + w)) f := by
  unfold average
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    change κ z • translation (ρ z)
      (∫ w : Homogenization.Vec 2, ψ w • translation (ρ w) f) = _
    rw [← (translation (ρ z)).integral_comp_comm
      (fun w : Homogenization.Vec 2 => ψ w • translation (ρ w) f), ← integral_smul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun w => by
      change κ z • translation (ρ z) (ψ w • translation (ρ w) f) = _
      rw [map_smul, ← translation_add, ← map_add]

theorem average_kernelConvolution (ρ : Homogenization.Vec 2 →+ X) (hρ : Continuous ρ)
    (κ ψ : Homogenization.Vec 2 → ℝ) (hκ : Integrable κ) (hψ : Integrable ψ) (f : L2 E μ) :
    average ρ (kernelConvolution κ ψ) f = average ρ κ (average ρ ψ f) := by
  have hd := (integrable_double_average ρ hρ hκ hψ f).swap
  have hchange := (measurePreserving_sub_prod
    (volume : Measure (Homogenization.Vec 2)) volume).integrable_comp_of_integrable hd
  have hi : Integrable (fun p : Homogenization.Vec 2 × Homogenization.Vec 2 =>
      κ p.2 • ψ (p.1 - p.2) • translation (ρ p.1) f) (volume.prod volume) := by
    have heq : (fun p : Homogenization.Vec 2 × Homogenization.Vec 2 =>
        κ p.2 • ψ (p.1 - p.2) • translation (ρ p.1) f) =
        ((fun p : Homogenization.Vec 2 × Homogenization.Vec 2 =>
          κ p.1 • ψ p.2 • translation (ρ (p.1 + p.2)) f) ∘ Prod.swap) ∘
          (fun p : Homogenization.Vec 2 × Homogenization.Vec 2 => (p.1 - p.2, p.2)) := by
      funext p
      change κ p.2 • ψ (p.1 - p.2) • translation (ρ p.1) f =
        κ p.2 • ψ (p.1 - p.2) • translation (ρ (p.2 + (p.1 - p.2))) f
      rw [← add_sub_assoc, add_sub_cancel_left]
    rw [← heq] at hchange
    exact hchange
  rw [average_average ρ κ ψ f]
  calc
    average ρ (kernelConvolution κ ψ) f =
        ∫ u : Homogenization.Vec 2, ∫ z : Homogenization.Vec 2,
          κ z • ψ (u - z) • translation (ρ u) f := by
      unfold average kernelConvolution convolution
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun u => by
        change (∫ t : Homogenization.Vec 2, κ t * ψ (u - t)) • translation (ρ u) f = _
        rw [← integral_smul_const]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun z => by
          change (κ z * ψ (u - z)) • translation (ρ u) f = _
          exact mul_smul _ _ _
    _ = ∫ z : Homogenization.Vec 2, ∫ u : Homogenization.Vec 2,
        κ z • ψ (u - z) • translation (ρ u) f := integral_integral_swap hi
    _ = ∫ z : Homogenization.Vec 2, ∫ w : Homogenization.Vec 2,
        κ z • ψ w • translation (ρ (z + w)) f := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        change (∫ u : Homogenization.Vec 2, κ z • ψ (u - z) • translation (ρ u) f) = _
        rw [← integral_add_left_eq_self
          (fun u : Homogenization.Vec 2 => κ z • ψ (u - z) • translation (ρ u) f) z]
        simp only [add_sub_cancel_left]

theorem averagingOperator_comp (ρ : Homogenization.Vec 2 →+ X) (hρ : Continuous ρ)
    (κ ψ : Homogenization.Vec 2 → ℝ) (hκ : Integrable κ) (hψ : Integrable ψ) :
    (averagingOperator (E := E) (μ := μ) ρ hρ κ hκ).comp (averagingOperator ρ hρ ψ hψ) =
      averagingOperator ρ hρ (kernelConvolution κ ψ) (integrable_kernelConvolution hκ hψ) := by
  apply ContinuousLinearMap.ext
  intro f
  exact (average_kernelConvolution ρ hρ κ ψ hκ hψ f).symm

end General

/-- Literal reflection on the Euclidean kernel variable. -/
def reflection (κ : Homogenization.Vec 2 → ℝ) : Homogenization.Vec 2 → ℝ := fun z => κ (-z)

theorem integrable_reflection {κ : Homogenization.Vec 2 → ℝ} (hκ : Integrable κ) :
    Integrable (reflection κ) := by
  change Integrable (fun z : Homogenization.Vec 2 => κ (-z)) volume
  exact hκ.comp_neg

section Hilbert
variable {X E : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [MeasurableSpace X] [BorelSpace X] [R1Space X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {μ : Measure X} [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
  [μ.IsAddLeftInvariant]

omit [R1Space X] [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop] [CompleteSpace E] in
theorem translation_inner (x : X) (f g : L2 E μ) :
    inner ℝ (translation x f) g = inner ℝ f (translation (-x) g) := by
  have h := (translation (E := E) (μ := μ) x).inner_map_map f (translation (-x) g)
  rw [← translation_add, add_neg_cancel, translation_zero] at h
  exact h

/-- Real L² pairing with the literal translated spatial representatives.
This avoids treating evaluation at a point as a continuous L² functional. -/
theorem averagingOperator_inner (ρ : Homogenization.Vec 2 →+ X) (hρ : Continuous ρ)
    (κ : Homogenization.Vec 2 → ℝ) (hκ : Integrable κ) (f g : L2 E μ) :
    inner ℝ (averagingOperator ρ hρ κ hκ f) g =
      ∫ z : Homogenization.Vec 2, κ z *
        (∫ y : X, inner ℝ (f (y - ρ z)) (g y) ∂μ) := by
  rw [averagingOperator_apply, real_inner_comm g,
    ← integral_inner (integrable_average_integrand ρ hρ hκ f)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    change inner ℝ g (κ z • translation (ρ z) f) = _
    rw [inner_smul_right, real_inner_comm (translation (ρ z) f) g, L2.inner_def]
    congr 1
    apply integral_congr_ae
    exact (translation_ae (ρ z) f).mono fun y hy => congrArg (fun a => inner ℝ a (g y)) hy

theorem averagingOperator_adjoint (ρ : Homogenization.Vec 2 →+ X) (hρ : Continuous ρ)
    (κ : Homogenization.Vec 2 → ℝ) (hκ : Integrable κ) :
    (averagingOperator (E := E) (μ := μ) ρ hρ κ hκ).adjoint =
      averagingOperator ρ hρ (reflection κ) (integrable_reflection hκ) := by
  apply Eq.symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f g
  rw [averagingOperator_apply, averagingOperator_apply]
  have hr := integrable_average_integrand ρ hρ (integrable_reflection hκ) f
  have hk := integrable_average_integrand ρ hρ hκ g
  rw [real_inner_comm g (∫ z : Homogenization.Vec 2, reflection κ z • translation (ρ z) f)]
  rw [← integral_inner hr, ← integral_inner hk]
  rw [← integral_neg_eq_self
    (fun z : Homogenization.Vec 2 => inner ℝ g (reflection κ z • translation (ρ z) f)) volume]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    simp only [reflection, neg_neg, map_neg, inner_smul_right]
    rw [real_inner_comm (translation (-(ρ z)) f) g, translation_inner, neg_neg]

/-- Autocorrelation is averaging by precisely `φ * check φ`, in this order of the factors. -/
theorem averagingOperator_autocorrelation (ρ : Homogenization.Vec 2 →+ X) (hρ : Continuous ρ)
    (φ : Homogenization.Vec 2 → ℝ) (hφ : Integrable φ) :
    (averagingOperator (E := E) (μ := μ) ρ hρ φ hφ).adjoint.comp
      (averagingOperator ρ hρ φ hφ) =
      averagingOperator ρ hρ (kernelConvolution φ (reflection φ))
        (integrable_kernelConvolution hφ (integrable_reflection hφ)) := by
  rw [averagingOperator_adjoint, averagingOperator_comp]
  congr 1
  exact kernelConvolution_comm _ _

end Hilbert

end AVRegularity.Analysis.Convolution
