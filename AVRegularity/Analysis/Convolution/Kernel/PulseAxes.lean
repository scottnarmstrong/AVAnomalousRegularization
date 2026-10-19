-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Analysis.Convolution.Kernel.Core
public import AVRegularity.Analysis.Convolution.Kernel.PairedGeometry
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen

@[expose] public section
noncomputable section

section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.Analysis.Convolution

/-! Almost-everywhere realization of an L² average as its spatial integral. -/

section Observation
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  {μ : Measure X} {C : Set X}

/-- The finite-observation L¹ bound from the actual L² norm and an indicator test. -/
theorem integral_norm_observation_le (f : L2 E μ) (hC : MeasurableSet C) (hμC : μ C ≠ ∞) :
    ∫ x in C, ‖f x‖ ∂μ ≤ ‖indicatorConstLp 2 hC hμC (1 : ℝ)‖ * ‖f‖ := by
  let g : L2 ℝ μ := (Lp.memLp f).norm.toLp (fun x => ‖f x‖)
  have hg : g =ᵐ[μ] fun x => ‖f x‖ := (Lp.memLp f).norm.coeFn_toLp
  have hn : ‖g‖ = ‖f‖ := by
    rw [Lp.norm_toLp, eLpNorm_norm _ (Lp.aestronglyMeasurable f)]
    rfl
  calc
    (∫ x in C, ‖f x‖ ∂μ) = ∫ x in C, g x ∂μ :=
      integral_congr_ae (ae_restrict_of_ae hg.symm)
    _ = inner ℝ (indicatorConstLp 2 hC hμC (1 : ℝ)) g :=
      (L2.inner_indicatorConstLp_one hC hμC g).symm
    _ ≤ ‖indicatorConstLp 2 hC hμC (1 : ℝ)‖ * ‖g‖ := real_inner_le_norm _ _
    _ = ‖indicatorConstLp 2 hC hμC (1 : ℝ)‖ * ‖f‖ := by rw [hn]

end Observation

/-- Literal pointwise convolution formula, on either spatial domain. -/
def pointwiseAverage {X E : Type*} [AddCommGroup X] [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {μ : Measure X}
    (ρ : Homogenization.Vec 2 →+ X) (κ : Homogenization.Vec 2 → ℝ)
    (f : L2 E μ) (y : X) : E := ∫ z : Homogenization.Vec 2, κ z • f (y - ρ z)

section Pointwise
variable {X E : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [MeasurableSpace X] [BorelSpace X] [R1Space X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {μ : Measure X} [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]
  [μ.IsAddLeftInvariant] [SigmaFinite μ]

omit [R1Space X] [CompleteSpace E] [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop] in
theorem spatial_integrand_measurable (ρ : Homogenization.Vec 2 →+ X) (hρ : Continuous ρ)
    {κ : Homogenization.Vec 2 → ℝ} (hκ : Integrable κ) (f : L2 E μ) (C : Set X) :
    AEStronglyMeasurable (fun p : Homogenization.Vec 2 × X => κ p.1 • f (p.2 - ρ p.1))
      (volume.prod (μ.restrict C)) := by
  have ht : Measure.QuasiMeasurePreserving (fun p : Homogenization.Vec 2 × X => p.2 - ρ p.1)
      (volume.prod (μ.restrict C)) μ := by
    apply QuasiMeasurePreserving.prod_of_right
    · exact (continuous_snd.sub (hρ.comp continuous_fst)).measurable
    · exact Filter.Eventually.of_forall fun z => by
        have h := (measurePreserving_add_left μ (-(ρ z))).quasiMeasurePreserving.mono_left
          (Measure.absolutelyContinuous_of_le (Measure.restrict_le_self (s := C)))
        convert h using 1
        funext y
        rw [sub_eq_add_neg, add_comm]
  exact hκ.aestronglyMeasurable.comp_fst.smul
    ((Lp.aestronglyMeasurable f).comp_quasiMeasurePreserving ht)

omit [R1Space X] [CompleteSpace E] [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop] in
theorem spatial_integrand_integrable (ρ : Homogenization.Vec 2 →+ X) (hρ : Continuous ρ)
    {κ : Homogenization.Vec 2 → ℝ} (hκ : Integrable κ) (f : L2 E μ)
    {C : Set X} (hC : MeasurableSet C) (hμC : μ C ≠ ∞) :
    Integrable (fun p : Homogenization.Vec 2 × X => κ p.1 • f (p.2 - ρ p.1))
      (volume.prod (μ.restrict C)) := by
  have hm := spatial_integrand_measurable ρ hρ hκ f C
  apply (integrable_prod_iff hm).mpr
  constructor
  · exact Filter.Eventually.of_forall fun z => by
      have ht := integrableOn_Lp_of_measure_ne_top (translation (ρ z) f) (by norm_num) hμC
      have ha := (translation_ae (ρ z) f)
      exact (ht.congr (ae_restrict_of_ae ha)).smul (κ z)
  · apply (hκ.norm.mul_const
      (‖indicatorConstLp 2 hC hμC (1 : ℝ)‖ * ‖f‖)).mono'
      hm.norm.integral_prod_right'
    exact Filter.Eventually.of_forall fun z => by
      change ‖∫ y in C, ‖κ z • f (y - ρ z)‖ ∂μ‖ ≤
        ‖κ z‖ * (‖indicatorConstLp 2 hC hμC (1 : ℝ)‖ * ‖f‖)
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      simp only [norm_smul]
      rw [integral_const_mul]
      have ht := integral_norm_observation_le (translation (ρ z) f) hC hμC
      rw [translation_norm] at ht
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (integral_congr_ae (ae_restrict_of_ae
        ((translation_ae (ρ z) f).fun_comp norm))).symm.le.trans ht

omit [R1Space X] [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop] in
theorem pointwiseAverage_integrableOn (ρ : Homogenization.Vec 2 →+ X) (hρ : Continuous ρ)
    {κ : Homogenization.Vec 2 → ℝ} (hκ : Integrable κ) (f : L2 E μ)
    {C : Set X} (hC : MeasurableSet C) (hμC : μ C ≠ ∞) :
    IntegrableOn (pointwiseAverage ρ κ f) C μ := by
  exact (spatial_integrand_integrable ρ hρ hκ f hC hμC).swap.integral_prod_left

/-- Finite-measure vector indicator tests identify the L² integral locally. -/
theorem averagingOperator_setIntegral (ρ : Homogenization.Vec 2 →+ X) (hρ : Continuous ρ)
    {κ : Homogenization.Vec 2 → ℝ} (hκ : Integrable κ) (f : L2 E μ)
    {C : Set X} (hC : MeasurableSet C) (hμC : μ C ≠ ∞) :
    (∫ y in C, averagingOperator ρ hρ κ hκ f y ∂μ) =
      ∫ z : Homogenization.Vec 2, ∫ y in C, κ z • f (y - ρ z) ∂μ := by
  apply ext_inner_left ℝ
  intro e
  let i : L2 E μ := indicatorConstLp 2 hC hμC e
  have hi := spatial_integrand_integrable ρ hρ hκ f hC hμC
  calc
    inner ℝ e (∫ y in C, averagingOperator ρ hρ κ hκ f y ∂μ) =
        inner ℝ i (averagingOperator ρ hρ κ hκ f) :=
      (L2.inner_indicatorConstLp_eq_inner_setIntegral ℝ hC hμC e _).symm
    _ = ∫ z : Homogenization.Vec 2, inner ℝ i (κ z • translation (ρ z) f) := by
      rw [averagingOperator_apply,
        ← integral_inner (integrable_average_integrand ρ hρ hκ f)]
    _ = ∫ z : Homogenization.Vec 2, inner ℝ e (∫ y in C, κ z • f (y - ρ z) ∂μ) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        change inner ℝ (indicatorConstLp 2 hC hμC e) (κ z • translation (ρ z) f) = _
        rw [L2.inner_indicatorConstLp_eq_inner_setIntegral ℝ hC hμC]
        congr 1
        apply integral_congr_ae
        exact (ae_restrict_of_ae ((Lp.coeFn_smul (κ z) (translation (ρ z) f)).trans
          ((translation_ae (ρ z) f).fun_comp (fun a => κ z • a))))
    _ = inner ℝ e (∫ z : Homogenization.Vec 2, ∫ y in C, κ z • f (y - ρ z) ∂μ) :=
      integral_inner hi.integral_prod_left e

/-- The L² Bochner average has the literal convolution formula almost everywhere
on any sigma-finite translation-invariant spatial domain. -/
theorem averagingOperator_ae (ρ : Homogenization.Vec 2 →+ X) (hρ : Continuous ρ)
    {κ : Homogenization.Vec 2 → ℝ} (hκ : Integrable κ) (f : L2 E μ) :
    averagingOperator ρ hρ κ hκ f =ᵐ[μ] pointwiseAverage ρ κ f := by
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro C _ hμC
    exact integrableOn_Lp_of_measure_ne_top _ (by norm_num) hμC.ne
  · intro C hC hμC
    exact pointwiseAverage_integrableOn ρ hρ hκ f hC hμC.ne
  · intro C hC hμC
    rw [averagingOperator_setIntegral ρ hρ hκ f hC hμC.ne]
    exact integral_integral_swap (spatial_integrand_integrable ρ hρ hκ f hC hμC.ne)

end Pointwise

end AVRegularity.Analysis.Convolution
end

section
open MeasureTheory Homogenization
namespace AVRegularity.Analysis.Convolution

/-! Pulse-axis matrix estimates and radius consequences. -/

/-- The diagonal map in the orthonormal Hilbert coordinates. -/
def pulseDiagonalLinearMap (a b : ℝ) : HilbertTwo →ₗ[ℝ] HilbertTwo where
  toFun x := HilbertVec.ofVec (fun i => (if i = 0 then a else b) * x i)
  map_add' x y := by
    apply HilbertVec.ext
    intro i
    simp [mul_add]
  map_smul' c x := by
    apply HilbertVec.ext
    intro i
    simp [mul_left_comm]

def pulseDiagonalMap (a b : ℝ) : HilbertTwo →L[ℝ] HilbertTwo :=
  LinearMap.toContinuousLinearMap (pulseDiagonalLinearMap a b)

@[simp] theorem pulseDiagonalMap_apply (a b : ℝ) (x : HilbertTwo) (i : Fin 2) :
    pulseDiagonalMap a b x i = (if i = 0 then a else b) * x i := by
  simp [pulseDiagonalMap, pulseDiagonalLinearMap]

/-- The linear map with prescribed first and second columns. -/
def pulseColumnMap (u v : HilbertTwo) : HilbertTwo →L[ℝ] HilbertTwo :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => x 0 • u + x 1 • v
      map_add' := by
        intro x y
        apply HilbertVec.ext
        intro i
        simp only [PiLp.add_apply, PiLp.smul_apply]
        ring
      map_smul' := by
        intro c x
        apply HilbertVec.ext
        intro i
        simp only [PiLp.smul_apply, PiLp.add_apply, smul_add, smul_smul]
        simp only [RingHom.id_apply]
        ring_nf }

@[simp] theorem pulseColumnMap_apply (u v x : HilbertTwo) :
    pulseColumnMap u v x = x 0 • u + x 1 • v := rfl

end AVRegularity.Analysis.Convolution
end
