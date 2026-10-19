-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Residual.QuietMean.EpsPoly
public import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Topology.Compactness.DeltaGeneratedSpace
import Mathlib.Topology.Convenient.GeneratedBy

/-! The cell mean of a jointly `C^r` two-scale field is `C^r` in the slow variable
(differentiation under the integral over the compact closed cell). -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization Filter Topology Metric

namespace AVRegularity.Providers.PathDecomp

/-- The closed unit cell. -/
def closedCell : Set (Vec 2) := Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1

theorem isCompact_closedCell : IsCompact closedCell := isCompact_univ_pi fun _ => isCompact_Icc

theorem fieldCellMean_eq_closedCell {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : Vec 2 → E) : fieldCellMean ψ = ∫ z in closedCell, ψ z := by
  unfold fieldCellMean
  refine setIntegral_congr_set ?_
  simpa [volume_pi, AVenhance.unitCube, closedCell] using
    (Measure.univ_pi_Ioo_ae_eq_Icc (f := fun _ : Fin 2 => (0 : ℝ)) (g := fun _ : Fin 2 => (1 : ℝ)))

instance : IsFiniteMeasure (volume.restrict closedCell) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact isCompact_closedCell.measure_lt_top⟩

theorem contDiff_fieldCellMean_aux : ∀ (r : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (Φ : Vec 2 → Vec 2 → E), ContDiff ℝ (r : ℕ∞) (Function.uncurry Φ) →
      ContDiff ℝ (r : ℕ∞) (fun X => ∫ z in closedCell, Φ X z)
  | 0, E, _, _, _, Φ, hΦ => by
      have hc : Continuous (Function.uncurry Φ) := hΦ.continuous
      exact contDiff_zero.2 (continuous_parametric_integral_of_continuous hc isCompact_closedCell)
  | r + 1, E, _, _, _, Φ, hΦ => by
      have hΦ1 : ContDiff ℝ 1 (Function.uncurry Φ) := hΦ.of_le (by exact_mod_cast (by omega : 1 ≤ r + 1))
      let F' : Vec 2 → Vec 2 → (Vec 2 →L[ℝ] E) := fun X z =>
        (fderiv ℝ (Function.uncurry Φ) (X, z)).comp (ContinuousLinearMap.inl ℝ (Vec 2) (Vec 2))
      have hF'c : ContDiff ℝ (r : ℕ∞) (Function.uncurry F') := by
        have h1 : ContDiff ℝ (r : ℕ∞) (fderiv ℝ (Function.uncurry Φ)) :=
          hΦ.fderiv_right (m := (r : ℕ∞)) (by push_cast; exact le_rfl)
        exact ((ContinuousLinearMap.compL ℝ (Vec 2) (Vec 2 × Vec 2) E).flip
          (ContinuousLinearMap.inl ℝ (Vec 2) (Vec 2))).contDiff.comp h1
      have hpart : ∀ X z, HasFDerivAt (fun X' => Φ X' z) (F' X z) X := by
        intro X z
        have h1 : HasFDerivAt (fun X' : Vec 2 => (X', z)) (ContinuousLinearMap.inl ℝ (Vec 2) (Vec 2)) X :=
          ((hasFDerivAt_id X).prodMk (hasFDerivAt_const z X)).congr_fderiv (by ext <;> simp)
        exact (hΦ1.differentiable one_ne_zero (X, z)).hasFDerivAt.comp X h1
      have hderiv : ∀ X₀, HasFDerivAt (fun X => ∫ z in closedCell, Φ X z)
          (∫ z in closedCell, F' X₀ z) X₀ := by
        intro X₀
        obtain ⟨M, hM⟩ := ((isCompact_closedBall X₀ 1).prod isCompact_closedCell).exists_bound_of_continuousOn
          hF'c.continuous.continuousOn
        refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
          (μ := volume.restrict closedCell) (F := fun X z => Φ X z) (F' := F') (bound := fun _ => M)
          (closedBall_mem_nhds X₀ one_pos) (Eventually.of_forall fun X => ?_) ?_ ?_ ?_
          (integrable_const M) (Eventually.of_forall fun z X _ => hpart X z)
        · exact (hΦ.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
        · exact (hΦ.continuous.comp (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_compact
            isCompact_closedCell
        · exact (hF'c.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
        · refine (ae_restrict_iff' isCompact_closedCell.measurableSet).2
            (Eventually.of_forall fun z hz X hX => ?_)
          exact hM (X, z) ⟨hX, hz⟩
      have hfd : fderiv ℝ (fun X => ∫ z in closedCell, Φ X z) =
          fun X => ∫ z in closedCell, F' X z := funext fun X => (hderiv X).fderiv
      rw [show (((r + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) = ((r : ℕ∞) : WithTop ℕ∞) + 1 by norm_cast,
        contDiff_succ_iff_fderiv]
      refine ⟨fun X => (hderiv X).differentiableAt, by simp, ?_⟩
      rw [hfd]
      exact contDiff_fieldCellMean_aux r _ F' hF'c

/-- **Smoothness of cell means.** -/
theorem contDiff_fieldCellMean {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {r : ℕ} {Φ : Vec 2 → Vec 2 → E}
    (hΦ : ContDiff ℝ (r : ℕ∞) (Function.uncurry Φ)) :
    ContDiff ℝ (r : ℕ∞) (fun X => fieldCellMean (Φ X)) := by
  simp only [fieldCellMean_eq_closedCell]
  exact contDiff_fieldCellMean_aux r E Φ hΦ

end AVRegularity.Providers.PathDecomp
