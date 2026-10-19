-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.TrimmedQuietMargin
public import AVRegularity.Statements.Intermediate.CycleComparison.SlowPartial
public import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Topology.Compactness.DeltaGeneratedSpace
import Mathlib.Topology.Convenient.GeneratedBy

/-! Cell means of continuous fields: linearity, and differentiation of the cell mean in the slow
variable under the integral sign. -/

@[expose] public section

open MeasureTheory Homogenization Filter Topology

namespace AVRegularity

theorem measurableSet_unitCube : MeasurableSet AVenhance.unitCube :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

theorem unitCube_subset_closed :
    AVenhance.unitCube ⊆ AVenhance.Infra.Torus.Calculus.closedUnitCell 2 := by
  intro x hx i _
  exact ⟨(hx i (Set.mem_univ _)).1.le, (hx i (Set.mem_univ _)).2.le⟩

theorem volume_unitCube_eq_one : volume AVenhance.unitCube = 1 := by
  unfold AVenhance.unitCube
  rw [volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

instance : IsFiniteMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simp [volume_unitCube_eq_one]⟩

theorem integrableOn_unitCube {E : Type*} [NormedAddCommGroup E] {f : Vec 2 → E}
    (hf : Continuous f) : IntegrableOn f AVenhance.unitCube :=
  (hf.continuousOn.integrableOn_compact
    (AVenhance.Infra.Torus.Calculus.isCompact_closedUnitCell 2)).mono_set unitCube_subset_closed

theorem fieldCellMean_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : Vec 2 → E}
    (hf : Continuous f) (hg : Continuous g) :
    fieldCellMean (fun z => f z + g z) = fieldCellMean f + fieldCellMean g :=
  integral_add (integrableOn_unitCube hf) (integrableOn_unitCube hg)

theorem fieldCellMean_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ)
    (f : Vec 2 → E) : fieldCellMean (fun z => c • f z) = c • fieldCellMean f :=
  integral_smul c f

theorem fieldCellMean_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : Vec 2 → E}
    (hf : Continuous f) (hg : Continuous g) :
    fieldCellMean (fun z => f z - g z) = fieldCellMean f - fieldCellMean g :=
  integral_sub (integrableOn_unitCube hf) (integrableOn_unitCube hg)

theorem fieldCellMean_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Vec 2 → E) :
    fieldCellMean (fun z => -f z) = -fieldCellMean f :=
  integral_neg f

theorem fieldCellMean_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    fieldCellMean (fun _ : Vec 2 => (0 : E)) = 0 := by
  simp [fieldCellMean]

theorem fieldCellMean_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {κ : Type*}
    (s : Finset κ) {f : κ → Vec 2 → E} (hf : ∀ i ∈ s, Continuous (f i)) :
    fieldCellMean (fun z => ∑ i ∈ s, f i z) = ∑ i ∈ s, fieldCellMean (f i) :=
  integral_finsetSum s fun i hi => integrableOn_unitCube (hf i hi)

theorem fieldCellMean_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (L : E →L[ℝ] F) {f : Vec 2 → E}
    (hf : Continuous f) : fieldCellMean (fun z => L (f z)) = L (fieldCellMean f) :=
  by simp only [fieldCellMean]; exact (L.integral_comp_comm (integrableOn_unitCube hf))

theorem fieldCellMean_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (c : E) :
    fieldCellMean (fun _ : Vec 2 => c) = c := by
  rw [fieldCellMean, setIntegral_const]
  simp [Measure.real, volume_unitCube_eq_one]


theorem fderiv_slow_eq_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ψ : Vec 2 → Vec 2 → E} (hΨ : ContDiff ℝ 1 (Function.uncurry Ψ)) (X z : Vec 2) :
    fderiv ℝ (fun X' => Ψ X' z) X =
      (fderiv ℝ (Function.uncurry Ψ) (X, z)).comp (ContinuousLinearMap.inl ℝ (Vec 2) (Vec 2)) := by
  have h1 : HasFDerivAt (fun X' : Vec 2 => (X', z)) (ContinuousLinearMap.inl ℝ (Vec 2) (Vec 2)) X :=
    (hasFDerivAt_id X).prodMk (hasFDerivAt_const z X) |>.congr_fderiv (by ext <;> simp)
  have h2 := (hΨ.differentiable one_ne_zero (X, z)).hasFDerivAt.comp X h1
  exact h2.fderiv

theorem continuous_fderiv_slow_of_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ψ : Vec 2 → Vec 2 → E} (hΨ : ContDiff ℝ 1 (Function.uncurry Ψ)) :
    Continuous fun p : Vec 2 × Vec 2 => fderiv ℝ (fun X' => Ψ X' p.2) p.1 := by
  have : (fun p : Vec 2 × Vec 2 => fderiv ℝ (fun X' => Ψ X' p.2) p.1) = fun p =>
      (fderiv ℝ (Function.uncurry Ψ) (p.1, p.2)).comp (ContinuousLinearMap.inl ℝ (Vec 2) (Vec 2)) := by
    funext p; exact fderiv_slow_eq_comp hΨ p.1 p.2
  rw [this]
  exact (hΨ.continuous_fderiv one_ne_zero).clm_comp continuous_const

theorem fieldCellMean_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {Ψ : Vec 2 → Vec 2 → E} (hΨ : ContDiff ℝ 1 (Function.uncurry Ψ))
    (X : Vec 2) :
    HasFDerivAt (fun X' => fieldCellMean (Ψ X'))
      (∫ z in AVenhance.unitCube, fderiv ℝ (fun X' => Ψ X' z) X) X := by
  have hcont : Continuous (Function.uncurry Ψ) := hΨ.continuous
  have hFcont : ∀ X' : Vec 2, Continuous (Ψ X') := fun X' =>
    hcont.comp (continuous_const.prodMk continuous_id)
  have hF'cont := continuous_fderiv_slow_of_contDiff hΨ
  obtain ⟨C, hC⟩ := ((isCompact_closedBall X 1).prod
      (AVenhance.Infra.Torus.Calculus.isCompact_closedUnitCell 2)).exists_bound_of_continuousOn
    (f := fun p : Vec 2 × Vec 2 => fderiv ℝ (fun X' => Ψ X' p.2) p.1) hF'cont.continuousOn
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun x a => Ψ x a)
    (F' := fun x a => fderiv ℝ (fun X' => Ψ X' a) x) (bound := fun _ => C) (s := Metric.ball X 1)
    (Metric.ball_mem_nhds X one_pos) (Eventually.of_forall fun x => (hFcont x).aestronglyMeasurable)
    (integrableOn_unitCube (hFcont X))
    (hF'cont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable ?_
    (integrable_const C) ?_
  · refine (ae_restrict_iff' measurableSet_unitCube).mpr (Eventually.of_forall fun a ha x hx => ?_)
    exact hC (x, a) ⟨Metric.ball_subset_closedBall hx, unitCube_subset_closed ha⟩
  · refine Eventually.of_forall fun a x _ => ?_
    have hd : Differentiable ℝ (fun X' => Ψ X' a) :=
      (hΨ.differentiable one_ne_zero).comp (differentiable_id.prodMk (differentiable_const a))
    exact (hd x).hasFDerivAt

theorem fieldCellMean_slowPartial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {Ψ : Vec 2 → Vec 2 → E} (hΨ : ContDiff ℝ 1 (Function.uncurry Ψ))
    (X : Vec 2) (i : Fin 2) :
    fieldCellMean (fun z => slowPartial i Ψ X z) =
      fderiv ℝ (fun X' => fieldCellMean (Ψ X')) X (basisVec i) := by
  rw [(fieldCellMean_hasFDerivAt hΨ X).fderiv]
  have hc := continuous_fderiv_slow_of_contDiff hΨ
  have hcz : Continuous fun z => fderiv ℝ (fun X' => Ψ X' z) X :=
    hc.comp (continuous_const.prodMk continuous_id)
  have := (ContinuousLinearMap.apply ℝ E (basisVec i)).integral_comp_comm
    (μ := volume.restrict AVenhance.unitCube) (integrableOn_unitCube hcz)
  simpa [fieldCellMean, slowPartial] using this

end AVRegularity
