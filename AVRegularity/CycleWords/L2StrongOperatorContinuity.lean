-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.PlaneBlochCoefficients

@[expose] public noncomputable section

section
open MeasureTheory
namespace AVRegularity.CycleWords

/-! Literal normal-form terms with a measurable time parameter and fixed ordered input derivatives. -/

variable {T I V E F G : Type*} [MeasurableSpace T]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

structure FrequencyParameterNormalTerm (T I V E F : Type*) [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] where
  word : List I
  coefficient : T → V → E →L[ℝ] F

def FrequencyParameterNormalTerm.at (t : FrequencyParameterNormalTerm T I V E F) (a : T) :
    FrequencyNormalTerm I V E F := ⟨t.word, t.coefficient a⟩

def FrequencyParameterNormalTerm.coefficientDerivative
    (t : FrequencyParameterNormalTerm T I V E F) (direction : I → V) (i : I) :
    FrequencyParameterNormalTerm T I V E F :=
  ⟨t.word, fun a x => fderiv ℝ (t.coefficient a) x (direction i)⟩

def FrequencyParameterNormalTerm.inputDerivative
    (t : FrequencyParameterNormalTerm T I V E F) (i : I) : FrequencyParameterNormalTerm T I V E F :=
  ⟨t.word ++ [i], t.coefficient⟩

def FrequencyParameterNormalTerm.leftMultiply
    (t : FrequencyParameterNormalTerm T I V E F) (A : T → V → F →L[ℝ] G) :
    FrequencyParameterNormalTerm T I V E G :=
  ⟨t.word, fun a x => (A a x).comp (t.coefficient a x)⟩

end AVRegularity.CycleWords
end

section
open MeasureTheory Complex Metric
open scoped NNReal ENNReal
namespace AVRegularity.CycleWords

/-! Native boundedness and a holomorphic injective readout imply the actual higher Cauchy series. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [CompleteSpace E] [CompleteSpace F]
  [MeasurableSpace E] [BorelSpace E] [PolishSpace E]
  [MeasurableSpace F] [BorelSpace F]

theorem injectiveBoundedComplex_cauchy_lift (A : E →L[ℂ] F) (hA : Function.Injective A)
    (f : ℂ → E) (c : ℂ) (R : ℝ≥0) (hR : 0 < R) (M : ℝ)
    (hc : ContinuousOn (A ∘ f) (closedBall c R))
    (hd : DifferentiableOn ℂ (A ∘ f) (ball c R))
    (hb : ∀ z ∈ closedBall c R, ‖f z‖ ≤ M) :
    HasFPowerSeriesOnBall f (cauchyPowerSeries f c R) c R := by
  have hcircle : Continuous (fun θ : ℝ => A (f (circleMap c R θ))) :=
    hc.comp_continuous (continuous_circleMap c R) (fun θ => circleMap_mem_closedBall c R.2 θ)
  have hi := injectiveCircleLift_integrable A hA f c R M hcircle
    (fun θ => hb _ (circleMap_mem_closedBall c R.2 θ))
  exact injectiveComplex_cauchy_lift A hA f c R hR hi
    ⟨hd, hc.mono closure_ball_subset_closedBall⟩

end AVRegularity.CycleWords
end

section
open MeasureTheory Filter Topology
namespace AVRegularity.CycleWords

/-! A uniformly bounded strongly continuous operator family acts continuously on L2 fields. -/

theorem L2StrongOperator_continuous {X Z E F 𝕜 : Type*} [MeasurableSpace X]
    [TopologicalSpace Z] [FirstCountableTopology Z]
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (μ : Measure X) (A : Z → E →L[𝕜] F)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ z, ‖A z‖ ≤ C)
    (hc : ∀ e, Continuous (fun z => A z e)) (f : Lp E 2 μ) :
    Continuous (fun z => (A z).compLp f) := by
  apply continuous_iff_continuousAt.mpr
  intro z₀
  let raw := fun z x => A z (f x)
  have hm (z : Z) : MemLp (raw z) 2 μ := (A z).comp_memLp' (Lp.memLp f)
  have hg : MemLp (fun x => C * ‖f x‖) 2 μ := (Lp.memLp f).norm.const_mul C
  have hb (z : Z) : ∀ᵐ x ∂μ, ‖raw z x‖ ≤ ‖C * ‖f x‖‖ := by
    apply Eventually.of_forall
    intro x
    rw [Real.norm_of_nonneg (mul_nonneg hC (norm_nonneg _))]
    exact ((A z).le_opNorm (f x)).trans
      (mul_le_mul_of_nonneg_right (hA z) (norm_nonneg _))
  have ht : ∀ᵐ x ∂μ, Tendsto (fun z => raw z x) (𝓝 z₀) (𝓝 (raw z₀ x)) :=
    Eventually.of_forall (fun x => (hc (f x)).continuousAt.tendsto)
  have hh := tendsto_L2Field_of_dominated raw (raw z₀) (fun x => C * ‖f x‖)
    hm (hm z₀) hg hb (hb z₀) ht
  have he (z : Z) : (hm z).toLp (raw z) = (A z).compLp f := by
    apply Lp.ext
    filter_upwards [(hm z).coeFn_toLp, (A z).coeFn_compLp f] with x hx ha
    exact hx.trans ha.symm
  change Tendsto (fun z => (A z).compLp f) (𝓝 z₀) (𝓝 ((A z₀).compLp f))
  simpa only [he] using hh

theorem L2StrongOperator_continuous_of_bound {X Z E F 𝕜 : Type*} [MeasurableSpace X]
    [TopologicalSpace Z] [FirstCountableTopology Z]
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (μ : Measure X) (A : Z → E →L[𝕜] F)
    (C : ℝ) (hC : 0 ≤ C) (hA : ∀ z e, ‖A z e‖ ≤ C * ‖e‖)
    (hc : ∀ e, Continuous (fun z => A z e)) (f : Lp E 2 μ) :
    Continuous (fun z => (A z).compLp f) :=
  L2StrongOperator_continuous μ A C hC
    (fun z => (A z).opNorm_le_bound hC (hA z)) hc f

end AVRegularity.CycleWords
end
