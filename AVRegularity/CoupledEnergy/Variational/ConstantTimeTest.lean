-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public noncomputable section

section
open MeasureTheory Filter
open scoped Topology
namespace AVRegularity.CoupledEnergy.Variational

/-! Identify a bounded pointwise scalar trace with a weak spacetime limit.
The dominated-convergence passage is the scalar fixed-test mechanism of a
Galerkin limit; no temporal L² assumption on the source is used. -/

variable {T : Type*} [MeasurableSpace T]

/-- Uniformly bounded pointwise limits agree with weak set-integral limits. -/
theorem boundedScalarTrace_eq_ae (μ : Measure T) [IsFiniteMeasure μ]
    (z : ℕ → T → ℝ) (u w : T → ℝ) (B : ℝ)
    (hz : ∀ n, AEStronglyMeasurable (z n) μ)
    (hu : AEStronglyMeasurable u μ) (hw : Integrable w μ)
    (hb : ∀ n, ∀ᵐ t ∂μ, ‖z n t‖ ≤ B)
    (ht : ∀ᵐ t ∂μ, Tendsto (fun n => z n t) atTop (𝓝 (u t)))
    (hweak : ∀ s : Set T, MeasurableSet s →
      Tendsto (fun n => ∫ t in s, z n t ∂μ) atTop (𝓝 (∫ t in s, w t ∂μ))) :
    u =ᵐ[μ] w := by
  have hbound : ∀ᵐ t ∂μ, ‖u t‖ ≤ B := by
    filter_upwards [ht, ae_all_iff.mpr hb] with t hlim hbt
    exact le_of_tendsto hlim.norm (Eventually.of_forall hbt)
  have hui : Integrable u μ := Integrable.of_bound hu B hbound
  apply hui.ae_eq_of_forall_setIntegral_eq u w hw
  intro s hs _
  have hconv : Tendsto (fun n => ∫ t in s, z n t ∂μ) atTop
      (𝓝 (∫ t in s, u t ∂μ)) := by
    exact tendsto_integral_of_dominated_convergence (fun _ => B)
      (fun n => (hz n).restrict) (integrable_const B)
      (fun n => ae_restrict_of_ae (hb n)) (ae_restrict_of_ae ht)
  exact tendsto_nhds_unique hconv (hweak s hs)

end AVRegularity.CoupledEnergy.Variational
end

section
open MeasureTheory Set
open scoped ENNReal
namespace AVRegularity.CoupledEnergy.Variational

/-! Spatial tests extended constantly onto time subintervals. The resulting
bounded map lets strong Fourier test convergence enter temporal dual pairings. -/

variable {T G : Type*} [MeasurableSpace T]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  (μ : Measure T) (s : Set T) (hs : MeasurableSet s) (hμs : μ s ≠ ∞)

/-- The constant supported temporal test, as a linear map. -/
def constantTimeTestLinearMap : G →ₗ[ℝ] Lp G 2 μ where
  toFun := indicatorConstLp 2 hs hμs
  map_add' _ _ := indicatorConstLp_add.symm
  map_smul' c x := by
    apply Lp.ext
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := c • x),
      indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := x),
      Lp.coeFn_smul c (indicatorConstLp 2 hs hμs x)] with t hcx hx hsm
    change indicatorConstLp 2 hs hμs (c • x) t = (c • indicatorConstLp 2 hs hμs x) t
    rw [hcx, hsm]
    simp only [Pi.smul_apply]
    rw [hx]
    by_cases ht : t ∈ s <;> simp [ht]

/-- A supported constant spatial test is bounded in time L². -/
def constantTimeTestCLM : G →L[ℝ] Lp G 2 μ :=
  (constantTimeTestLinearMap μ s hs hμs).mkContinuous (μ.real s ^ (1 / (2 : ℝ))) (by
    intro x
    change ‖indicatorConstLp 2 hs hμs x‖ ≤ (μ.real s ^ (1 / (2 : ℝ))) * ‖x‖
    simpa only [ENNReal.toReal_ofNat, mul_comm] using
      (norm_indicatorConstLp_le (p := 2) (hs := hs) (hμs := hμs) (c := x)))

@[simp] theorem constantTimeTestCLM_apply (x : G) :
    constantTimeTestCLM μ s hs hμs x = indicatorConstLp 2 hs hμs x := rfl

end AVRegularity.CoupledEnergy.Variational
end
