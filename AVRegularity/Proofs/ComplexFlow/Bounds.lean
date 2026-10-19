-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.ComplexFlow.ParamCauchy
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.PicardGroup

@[expose] public noncomputable section

section
open MeasureTheory Set Filter Topology Homogenization Metric
open scoped Interval
namespace AVRegularity.Providers.ComplexFlow

/-! **The complex flow is holomorphic in the initial point**.
For a field that is in addition holomorphic on the strip (`HolField`):
* its derivative is bounded by `2Γ` on `S_ℓ` (`norm_fderiv_le`) and is `L₂`-Lipschitz on the
  closed sub-strip `S̄_{ℓ'}` with `L₂ = 6Γ/(ℓ - ℓ')` (`norm_fderiv_sub_le`, Cauchy's estimate on
  balls of radius `(ℓ - ℓ')/3`);
* the derivative iterates `dpic` (`W_{n+1} = I + ∫ Dv(X_n) W_n`) are the derivatives of the
  Picard iterates on the open initial set `|Im z|₁ < (1 - Γ(b - a)) ℓ'` (`hasFDerivAt_pic`), are
  bounded by `5` (`norm_dpic_le`) and converge geometrically (`norm_dpic_succ_sub_le`);
* hence the flow is holomorphic in the initial point, with derivative the limit `cjac` of the
  derivative iterates (`hasFDerivAt_cflow`), and `‖cjac - I‖ ≤ 10 Γ |τ - s|`
  (`norm_cjac_sub_one_le`). -/

open AVRegularity.Providers.GenSem

/-- **A holomorphic velocity field on the strip.** -/
structure HolField (v : ℝ → CVec → CVec) (ℓ Γ V : ℝ) : Prop extends StripField v ℓ Γ V where
  /-- Holomorphy in the space variable on `S_ℓ`. -/
  holo : ∀ t, DifferentiableOn ℂ (v t) (strip ℓ)

variable {v : ℝ → CVec → CVec} {ℓ ℓ' Γ V a b : ℝ}

/-- The open initial set `|Im z|₁ < (1 - Γ(b - a)) ℓ'`. -/
def U0 (ℓ' Γ a b : ℝ) : Set CVec := strip ((1 - Γ * (b - a)) * ℓ')

theorem U0_subset_Z0 : U0 ℓ' Γ a b ⊆ Z0 ℓ' Γ a b := strip_subset_cstrip _

theorem isOpen_U0 : IsOpen (U0 ℓ' Γ a b) := isOpen_strip _

/-! ### Derivative bounds of the field -/

theorem lipschitzOnWith_v (hv : StripField v ℓ Γ V) (t : ℝ) :
    LipschitzOnWith (Real.toNNReal (2 * Γ)) (v t) (strip ℓ) := by
  refine LipschitzOnWith.of_dist_le_mul fun z hz w hw => ?_
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by linarith [hv.hΓ])]
  calc ‖v t z - v t w‖ ≤ l1 (v t z - v t w) := norm_le_l1 _
    _ ≤ Γ * l1 (z - w) := hv.lip t z hz w hw
    _ ≤ Γ * (2 * ‖z - w‖) := mul_le_mul_of_nonneg_left (l1_le_two_mul_norm _) hv.hΓ
    _ = 2 * Γ * ‖z - w‖ := by ring

theorem norm_fderiv_le (hv : StripField v ℓ Γ V) (t : ℝ) {y : CVec} (hy : y ∈ strip ℓ) :
    ‖fderiv ℂ (v t) y‖ ≤ 2 * Γ := by
  have h := norm_fderiv_le_of_lipschitzOn (𝕜 := ℂ) ((isOpen_strip ℓ).mem_nhds hy)
    (lipschitzOnWith_v hv t)
  rwa [Real.coe_toNNReal _ (by linarith [hv.hΓ])] at h

theorem fderiv_apply_coord (hv : HolField v ℓ Γ V) (t : ℝ) {y : CVec} (hy : y ∈ strip ℓ)
    (w : CVec) (c : Fin 2) :
    fderiv ℂ (fun y' => v t y' c) y w = fderiv ℂ (v t) y w c := by
  have hd : HasFDerivAt (v t) (fderiv ℂ (v t) y) y :=
    ((hv.holo t).differentiableAt ((isOpen_strip ℓ).mem_nhds hy)).hasFDerivAt
  have h2 : HasFDerivAt (fun y' => v t y' c)
      ((ContinuousLinearMap.proj c : CVec →L[ℂ] ℂ).comp (fderiv ℂ (v t) y)) y :=
    ((ContinuousLinearMap.proj c : CVec →L[ℂ] ℂ).hasFDerivAt).comp y hd
  rw [h2.fderiv]
  rfl

theorem closedBall_subset_strip (hw : FlowWin ℓ ℓ' Γ a b) {y : CVec} (hy : y ∈ cstrip ℓ') :
    closedBall y ((ℓ - ℓ') / 3) ⊆ strip ℓ := by
  intro z hz
  show imL1 z < ℓ
  have h1 := imL1_le_add_l1 z y
  have h2 : l1 (z - y) ≤ 2 * ‖z - y‖ := l1_le_two_mul_norm _
  rw [mem_closedBall, dist_eq_norm] at hz
  have hy' : imL1 y ≤ ℓ' := hy
  have := hw.hℓℓ
  linarith

/-- **The derivative of the field is Lipschitz on the closed sub-strip.** -/
theorem norm_fderiv_sub_le (hv : HolField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) (t : ℝ) {y y' : CVec}
    (hy : y ∈ cstrip ℓ') (hy' : y' ∈ cstrip ℓ') :
    ‖fderiv ℂ (v t) y - fderiv ℂ (v t) y'‖ ≤ 6 * Γ / (ℓ - ℓ') * ‖y - y'‖ := by
  have hρ : 0 < (ℓ - ℓ') / 3 := by linarith [hw.hℓℓ]
  have hΓ := hv.hΓ
  have hC : 0 ≤ 6 * Γ / (ℓ - ℓ') * ‖y - y'‖ := by
    have : 0 < ℓ - ℓ' := by linarith [hw.hℓℓ]
    positivity
  refine ContinuousLinearMap.opNorm_le_of_unit_norm hC fun w hw1 => ?_
  refine (pi_norm_le_iff_of_nonneg hC).mpr fun c => ?_
  -- the scalar function `G = (Dv · w)_c`
  have hFc : DifferentiableOn ℂ (fun y'' => v t y'' c) (strip ℓ) :=
    fun x hx => ((ContinuousLinearMap.proj c : CVec →L[ℂ] ℂ).differentiableAt.comp_differentiableWithinAt
      x (hv.holo t x hx))
  have hG := differentiableOn_fderiv_apply (isOpen_strip ℓ) hFc w
  have hGeq : ∀ x ∈ strip ℓ, fderiv ℂ (fun y'' => v t y'' c) x w = fderiv ℂ (v t) x w c :=
    fun x hx => fderiv_apply_coord hv t hx w c
  have hbd : ∀ x ∈ cstrip ℓ', ‖fderiv ℂ (fun y'' => fderiv ℂ (fun y''' => v t y''' c) y'' w) x‖ ≤
      2 * Γ / ((ℓ - ℓ') / 3) := by
    intro x hx
    refine norm_fderiv_le_of_closedBall hρ (hG.mono (closedBall_subset_strip hw hx)) fun z hz => ?_
    have hzs := closedBall_subset_strip hw hx hz
    rw [hGeq z hzs]
    calc ‖fderiv ℂ (v t) z w c‖ ≤ ‖fderiv ℂ (v t) z w‖ := norm_le_pi_norm _ c
      _ ≤ ‖fderiv ℂ (v t) z‖ * ‖w‖ := (fderiv ℂ (v t) z).le_opNorm w
      _ ≤ 2 * Γ := by rw [hw1, mul_one]; exact norm_fderiv_le hv.toStripField t hzs
  have hmv := (convex_cstrip ℓ').norm_image_sub_le_of_norm_fderiv_le
    (f := fun y'' => fderiv ℂ (fun y''' => v t y''' c) y'' w)
    (fun x hx => hG.differentiableAt ((isOpen_strip ℓ).mem_nhds (cstrip_subset_strip hw.hℓℓ hx)))
    hbd hy' hy
  rw [hGeq y (cstrip_subset_strip hw.hℓℓ hy), hGeq y' (cstrip_subset_strip hw.hℓℓ hy')] at hmv
  have e : 2 * Γ / ((ℓ - ℓ') / 3) = 6 * Γ / (ℓ - ℓ') := by field_simp; ring
  rw [e] at hmv
  simpa [sub_apply] using hmv

/-! ### Derivative iterates -/

/-- The derivative iterates `W_0 = I`, `W_{n+1} = I + ∫_s^τ Dv(X_n) W_n`. -/
def dpic (v : ℝ → CVec → CVec) (ℓ' : ℝ) : ℕ → ℝ → CVec → ℝ → (CVec →L[ℂ] CVec)
  | 0 => fun _ _ _ => ContinuousLinearMap.id ℂ CVec
  | n + 1 => fun τ z s => ContinuousLinearMap.id ℂ CVec +
      ∫ σ in s..τ, (fderiv ℂ (rf v ℓ' σ) (pic v ℓ' n σ z s)).comp (dpic v ℓ' n σ z s)

theorem dpic_succ (n : ℕ) (τ : ℝ) (z : CVec) (s : ℝ) :
    dpic v ℓ' (n + 1) τ z s = ContinuousLinearMap.id ℂ CVec +
      ∫ σ in s..τ, (fderiv ℂ (rf v ℓ' σ) (pic v ℓ' n σ z s)).comp (dpic v ℓ' n σ z s) := rfl

theorem fderiv_rf_eq (hw : FlowWin ℓ ℓ' Γ a b) (t : ℝ) {y : CVec} (hy : y ∈ strip ℓ') :
    fderiv ℂ (rf v ℓ' t) y = fderiv ℂ (v t) y := by
  refine Filter.EventuallyEq.fderiv_eq ?_
  filter_upwards [(isOpen_strip ℓ').mem_nhds hy] with x hx
  exact rf_eq hw.hℓ' (strip_subset_cstrip ℓ' hx)

theorem hasFDerivAt_rf (hv : HolField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) (t : ℝ) {y : CVec}
    (hy : y ∈ strip ℓ') : HasFDerivAt (rf v ℓ' t) (fderiv ℂ (rf v ℓ' t) y) y := by
  have hd : DifferentiableAt ℂ (v t) y := (hv.holo t).differentiableAt
    ((isOpen_strip ℓ).mem_nhds (cstrip_subset_strip hw.hℓℓ (strip_subset_cstrip ℓ' hy)))
  have he : rf v ℓ' t =ᶠ[𝓝 y] v t := by
    filter_upwards [(isOpen_strip ℓ').mem_nhds hy] with x hx
    exact rf_eq hw.hℓ' (strip_subset_cstrip ℓ' hx)
  exact (hd.congr_of_eventuallyEq he).hasFDerivAt

theorem measurable_fderiv_rf (hv : StripField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) :
    Measurable fun p : ℝ × CVec => fderiv ℂ (rf v ℓ' p.1) p.2 :=
  measurable_fderiv_with_param ℂ (f := fun t z => rf v ℓ' t z) (continuous_rf hv hw)

theorem norm_fderiv_rf_le (hv : StripField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) (t : ℝ)
    {y : CVec} (hy : y ∈ strip ℓ') : ‖fderiv ℂ (rf v ℓ' t) y‖ ≤ 2 * Γ := by
  rw [fderiv_rf_eq hw t hy]
  exact norm_fderiv_le hv t (cstrip_subset_strip hw.hℓℓ (strip_subset_cstrip ℓ' hy))

/-- The integrand of the derivative iterates. -/
def dint (v : ℝ → CVec → CVec) (ℓ' : ℝ) (n : ℕ) (z : CVec) (s σ : ℝ) : CVec →L[ℂ] CVec :=
  (fderiv ℂ (rf v ℓ' σ) (pic v ℓ' n σ z s)).comp (dpic v ℓ' n σ z s)

/-- The derivative iterates are continuous in time on the window, measurable, and bounded by `5`
along the paths of initial points in `U0`. -/
theorem dpic_props (hv : StripField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) {z : CVec}
    (hz : z ∈ U0 ℓ' Γ a b) {s : ℝ} (hs : s ∈ Icc a b) (n : ℕ) :
    ContinuousOn (fun σ => dpic v ℓ' n σ z s) (Icc a b) ∧
      ∀ σ ∈ Icc a b, ‖dpic v ℓ' n σ z s‖ ≤ 5 := by
  have hΓT := hw.hΓT
  have hΓ := hv.hΓ
  have hT0 : 0 ≤ b - a := sub_nonneg.mpr hw.hab
  induction n with
  | zero =>
    refine ⟨continuousOn_const, fun σ _ => ?_⟩
    exact (ContinuousLinearMap.norm_id_le).trans (by norm_num)
  | succ n ih =>
    obtain ⟨hc, hb⟩ := ih
    -- the integrand is a.e.-strongly measurable and bounded by `10 Γ` on the window
    have hmeas : AEStronglyMeasurable (dint v ℓ' n z s) (volume.restrict (Icc a b)) := by
      have h1 : Measurable fun σ : ℝ => fderiv ℂ (rf v ℓ' σ) (pic v ℓ' n σ z s) :=
        (measurable_fderiv_rf hv hw).comp
          (measurable_id.prodMk (continuous_pic_time hv hw n z s).measurable)
      have h2 : AEStronglyMeasurable (fun σ => dpic v ℓ' n σ z s) (volume.restrict (Icc a b)) :=
        hc.aestronglyMeasurable measurableSet_Icc
      exact (continuous_fst.clm_comp continuous_snd).comp_aestronglyMeasurable
        ((h1.aestronglyMeasurable (μ := volume.restrict (Icc a b))).prodMk h2)
    have hbd : ∀ σ ∈ Icc a b, ‖dint v ℓ' n z s σ‖ ≤ 2 * Γ * 5 := by
      intro σ hσ
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      exact mul_le_mul (norm_fderiv_rf_le hv hw σ
        (pic_mem_strip hv hw hz hs n σ hσ)) (hb σ hσ) (norm_nonneg _) (by linarith)
    have hint : IntegrableOn (dint v ℓ' n z s) (Icc a b) volume :=
      IntegrableOn.of_bound measure_Icc_lt_top hmeas (2 * Γ * 5)
        ((ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall hbd))
    refine ⟨?_, fun σ hσ => ?_⟩
    · have hcont := intervalIntegral.continuousOn_primitive_interval' (μ := volume)
        (a := s) (b₁ := a) (b₂ := b) (f := dint v ℓ' n z s)
        (hint.mono_set (uIcc_subset_Icc ⟨le_rfl, hw.hab⟩ ⟨hw.hab, le_rfl⟩)).intervalIntegrable
        (by rw [uIcc_of_le hw.hab]; exact hs)
      rw [uIcc_of_le hw.hab] at hcont
      exact continuousOn_const.add hcont
    · show ‖ContinuousLinearMap.id ℂ CVec + ∫ σ' in s..σ, dint v ℓ' n z s σ'‖ ≤ 5
      have h1 : ‖∫ σ' in s..σ, dint v ℓ' n z s σ'‖ ≤ (2 * Γ * 5) * |σ - s| :=
        intervalIntegral.norm_integral_le_of_norm_le_const fun σ' hσ' =>
          hbd σ' (uIoc_subset_window hσ hs hσ')
      have h2 := abs_sub_le_window hσ hs
      calc ‖ContinuousLinearMap.id ℂ CVec + ∫ σ' in s..σ, dint v ℓ' n z s σ'‖
          ≤ ‖ContinuousLinearMap.id ℂ CVec‖ + ‖∫ σ' in s..σ, dint v ℓ' n z s σ'‖ := norm_add_le _ _
        _ ≤ 1 + (2 * Γ * 5) * (b - a) :=
          add_le_add ContinuousLinearMap.norm_id_le
            (h1.trans (mul_le_mul_of_nonneg_left h2 (by linarith)))
        _ ≤ 5 := by nlinarith

theorem norm_dpic_le (hv : StripField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) {z : CVec}
    (hz : z ∈ U0 ℓ' Γ a b) {s : ℝ} (hs : s ∈ Icc a b) (n : ℕ) {σ : ℝ} (hσ : σ ∈ Icc a b) :
    ‖dpic v ℓ' n σ z s‖ ≤ 5 :=
  (dpic_props hv hw hz hs n).2 σ hσ

theorem norm_dint_le (hv : StripField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) {z : CVec}
    (hz : z ∈ U0 ℓ' Γ a b) {s : ℝ} (hs : s ∈ Icc a b) (n : ℕ) {σ : ℝ} (hσ : σ ∈ Icc a b) :
    ‖dint v ℓ' n z s σ‖ ≤ 2 * Γ * 5 := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  exact mul_le_mul (norm_fderiv_rf_le hv hw σ (pic_mem_strip hv hw hz hs n σ hσ))
    (norm_dpic_le hv hw hz hs n hσ) (norm_nonneg _) (by linarith [hv.hΓ])

theorem intervalIntegrable_dint (hv : StripField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) {z : CVec}
    (hz : z ∈ U0 ℓ' Γ a b) {s : ℝ} (hs : s ∈ Icc a b) (n : ℕ) {τ : ℝ} (hτ : τ ∈ Icc a b) :
    IntervalIntegrable (dint v ℓ' n z s) volume s τ := by
  have hc := (dpic_props hv hw hz hs n).1
  have h1 : Measurable fun σ : ℝ => fderiv ℂ (rf v ℓ' σ) (pic v ℓ' n σ z s) :=
    (measurable_fderiv_rf hv hw).comp
      (measurable_id.prodMk (continuous_pic_time hv hw n z s).measurable)
  have hmeas : AEStronglyMeasurable (dint v ℓ' n z s) (volume.restrict (Icc a b)) :=
    (continuous_fst.clm_comp continuous_snd).comp_aestronglyMeasurable
      ((h1.aestronglyMeasurable (μ := volume.restrict (Icc a b))).prodMk
        (hc.aestronglyMeasurable measurableSet_Icc))
  have hint : IntegrableOn (dint v ℓ' n z s) (Icc a b) volume :=
    IntegrableOn.of_bound measure_Icc_lt_top hmeas (2 * Γ * 5)
      ((ae_restrict_iff' measurableSet_Icc).mpr
        (Eventually.of_forall fun σ hσ => norm_dint_le hv hw hz hs n hσ))
  exact (hint.mono_set (uIcc_subset_Icc hs hτ)).intervalIntegrable

/-- **The derivative iterates are the derivatives of the Picard iterates.** -/
theorem hasFDerivAt_pic (hv : HolField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) {s : ℝ}
    (hs : s ∈ Icc a b) (n : ℕ) :
    ∀ τ ∈ Icc a b, ∀ z ∈ U0 ℓ' Γ a b,
      HasFDerivAt (fun x => pic v ℓ' n τ x s) (dpic v ℓ' n τ z s) z := by
  have hΓ := hv.hΓ
  induction n with
  | zero => exact fun τ _ z _ => hasFDerivAt_id z
  | succ n ih =>
    intro τ hτ z hz
    have hU : U0 ℓ' Γ a b ∈ 𝓝 z := isOpen_U0.mem_nhds hz
    have h := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ)
      (μ := volume) (a := s) (b := τ) (s := U0 ℓ' Γ a b) (x₀ := z)
      (F := fun x σ => rf v ℓ' σ (pic v ℓ' n σ x s)) (F' := fun x σ => dint v ℓ' n x s σ)
      (bound := fun _ => 2 * Γ * 5) hU
      (Eventually.of_forall fun x =>
        ((continuous_rf hv.toStripField hw).comp (continuous_id.prodMk
          (continuous_pic_time hv.toStripField hw n x s))).aestronglyMeasurable)
      (intervalIntegrable_rf_pic hv.toStripField hw n z s s τ)
      (intervalIntegrable_dint hv.toStripField hw hz hs n hτ).def'.aestronglyMeasurable
      (Eventually.of_forall fun σ hσ x hx =>
        norm_dint_le hv.toStripField hw hx hs n (uIoc_subset_window hτ hs hσ))
      intervalIntegrable_const
      (Eventually.of_forall fun σ hσ x hx => by
        have hσW := uIoc_subset_window hτ hs hσ
        have h := (hasFDerivAt_rf hv hw σ (pic_mem_strip hv.toStripField hw hx hs n σ hσW)).comp x
          (ih σ hσW x hx)
        exact h)
    exact (hasFDerivAt_id z).add h

/-! ### Convergence of the derivative iterates -/

/-- The constant of the geometric bound of the derivative iterates. -/
def dpicC (ℓ ℓ' Γ V a b : ℝ) : ℝ :=
  max (2 * Γ * 5 * (b - a)) (10 * (5 * (6 * Γ / (ℓ - ℓ')) * (b - a) * picC ℓ' Γ V a b))

theorem norm_dpic_succ_sub_le (hv : HolField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) {z : CVec}
    (hz : z ∈ U0 ℓ' Γ a b) {s : ℝ} (hs : s ∈ Icc a b) (n : ℕ) :
    ∀ τ ∈ Icc a b, ‖dpic v ℓ' (n + 1) τ z s - dpic v ℓ' n τ z s‖ ≤
      dpicC ℓ ℓ' Γ V a b * (9 / 10) ^ n := by
  have hΓ := hv.hΓ
  have hΓT := hw.hΓT
  have hT0 : 0 ≤ b - a := sub_nonneg.mpr hw.hab
  have hL0 : 0 ≤ 6 * Γ / (ℓ - ℓ') := div_nonneg (by linarith) (by linarith [hw.hℓℓ])
  have hz0 : z ∈ Z0 ℓ' Γ a b := U0_subset_Z0 hz
  have hP0 : 0 ≤ picC ℓ' Γ V a b := by
    have := (l1_nonneg _).trans (l1_pic_succ_sub_le hv.toStripField hw hz0 hs 0 a ⟨le_rfl, hw.hab⟩)
    simpa using this
  induction n with
  | zero =>
    intro τ hτ
    have e : dpic v ℓ' 1 τ z s - dpic v ℓ' 0 τ z s = ∫ σ in s..τ, dint v ℓ' 0 z s σ := by
      simp only [dpic, add_sub_cancel_left, dint]
    rw [e, pow_zero, mul_one]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const fun σ hσ =>
      norm_dint_le hv.toStripField hw hz hs 0 (uIoc_subset_window hτ hs hσ)).trans ?_
    refine (mul_le_mul_of_nonneg_left (abs_sub_le_window hτ hs) (by linarith)).trans ?_
    exact le_max_left _ _
  | succ n ih =>
    intro τ hτ
    have e : dpic v ℓ' (n + 2) τ z s - dpic v ℓ' (n + 1) τ z s =
        ∫ σ in s..τ, (dint v ℓ' (n + 1) z s σ - dint v ℓ' n z s σ) := by
      rw [dpic_succ, dpic_succ (n := n), add_sub_add_left_eq_sub,
        intervalIntegral.integral_sub (intervalIntegrable_dint hv.toStripField hw hz hs _ hτ)
          (intervalIntegrable_dint hv.toStripField hw hz hs _ hτ)]
      rfl
    rw [e]
    have hpt : ∀ σ ∈ Icc a b, ‖dint v ℓ' (n + 1) z s σ - dint v ℓ' n z s σ‖ ≤
        2 * Γ * (dpicC ℓ ℓ' Γ V a b * (9 / 10) ^ n) +
          5 * (6 * Γ / (ℓ - ℓ')) * (picC ℓ' Γ V a b * (Γ * (b - a)) ^ n) := by
      intro σ hσ
      have hm1 := pic_mem_strip hv.toStripField hw hz hs (n + 1) σ hσ
      have hm0 := pic_mem_strip hv.toStripField hw hz hs n σ hσ
      have hsplit : dint v ℓ' (n + 1) z s σ - dint v ℓ' n z s σ =
          (fderiv ℂ (rf v ℓ' σ) (pic v ℓ' (n + 1) σ z s)).comp
            (dpic v ℓ' (n + 1) σ z s - dpic v ℓ' n σ z s) +
          (fderiv ℂ (rf v ℓ' σ) (pic v ℓ' (n + 1) σ z s) -
            fderiv ℂ (rf v ℓ' σ) (pic v ℓ' n σ z s)).comp (dpic v ℓ' n σ z s) := by
        simp only [dint, ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
        abel
      rw [hsplit]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        exact mul_le_mul (norm_fderiv_rf_le hv.toStripField hw σ hm1) (ih σ hσ) (norm_nonneg _)
          (by linarith)
      · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        rw [fderiv_rf_eq hw σ hm1, fderiv_rf_eq hw σ hm0]
        have hL := norm_fderiv_sub_le hv hw σ (strip_subset_cstrip ℓ' hm1)
          (strip_subset_cstrip ℓ' hm0)
        have hd : ‖pic v ℓ' (n + 1) σ z s - pic v ℓ' n σ z s‖ ≤ picC ℓ' Γ V a b * (Γ * (b - a)) ^ n :=
          (norm_le_l1 _).trans (l1_pic_succ_sub_le hv.toStripField hw hz0 hs n σ hσ)
        calc ‖fderiv ℂ (v σ) (pic v ℓ' (n + 1) σ z s) - fderiv ℂ (v σ) (pic v ℓ' n σ z s)‖ *
              ‖dpic v ℓ' n σ z s‖
            ≤ (6 * Γ / (ℓ - ℓ') * (picC ℓ' Γ V a b * (Γ * (b - a)) ^ n)) * 5 :=
              mul_le_mul (hL.trans (mul_le_mul_of_nonneg_left hd hL0))
                (norm_dpic_le hv.toStripField hw hz hs n hσ) (norm_nonneg _) (by positivity)
          _ = 5 * (6 * Γ / (ℓ - ℓ')) * (picC ℓ' Γ V a b * (Γ * (b - a)) ^ n) := by ring
    refine (intervalIntegral.norm_integral_le_of_norm_le_const fun σ hσ =>
      hpt σ (uIoc_subset_window hτ hs hσ)).trans ?_
    have hT := abs_sub_le_window hτ hs
    have hr0 : 0 ≤ Γ * (b - a) := mul_nonneg hΓ hT0
    have hrn : (Γ * (b - a)) ^ n ≤ (9 / 10) ^ n :=
      pow_le_pow_left₀ hr0 (by linarith) n
    have hD0 : 0 ≤ dpicC ℓ ℓ' Γ V a b := le_trans (by positivity) (le_max_left _ _)
    have hD2 : 10 * (5 * (6 * Γ / (ℓ - ℓ')) * (b - a) * picC ℓ' Γ V a b) ≤ dpicC ℓ ℓ' Γ V a b :=
      le_max_right _ _
    have hq0 : (0 : ℝ) ≤ (9 / 10) ^ n := by positivity
    calc (2 * Γ * (dpicC ℓ ℓ' Γ V a b * (9 / 10) ^ n) +
          5 * (6 * Γ / (ℓ - ℓ')) * (picC ℓ' Γ V a b * (Γ * (b - a)) ^ n)) * |τ - s|
        ≤ (2 * Γ * (dpicC ℓ ℓ' Γ V a b * (9 / 10) ^ n) +
          5 * (6 * Γ / (ℓ - ℓ')) * (picC ℓ' Γ V a b * (9 / 10) ^ n)) * (b - a) := by
          refine mul_le_mul (add_le_add le_rfl (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hrn hP0) (by positivity))) hT (abs_nonneg _) ?_
          positivity
      _ = (2 * Γ * (b - a)) * (dpicC ℓ ℓ' Γ V a b * (9 / 10) ^ n) +
          (5 * (6 * Γ / (ℓ - ℓ')) * (b - a) * picC ℓ' Γ V a b) * (9 / 10) ^ n := by ring
      _ ≤ (4 / 5) * (dpicC ℓ ℓ' Γ V a b * (9 / 10) ^ n) +
          (dpicC ℓ ℓ' Γ V a b / 10) * (9 / 10) ^ n := by
          refine add_le_add (mul_le_mul_of_nonneg_right (by linarith) (by positivity)) ?_
          exact mul_le_mul_of_nonneg_right (by linarith) hq0
      _ = dpicC ℓ ℓ' Γ V a b * (9 / 10) ^ (n + 1) := by ring

/-! ### The derivative of the flow -/

/-- **The derivative of the complex flow in the initial point.** -/
def cjac (v : ℝ → CVec → CVec) (ℓ' : ℝ) (τ : ℝ) (z : CVec) (s : ℝ) : CVec →L[ℂ] CVec :=
  limUnder atTop fun n => dpic v ℓ' n τ z s

theorem tendsto_dpic (hv : HolField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) {z : CVec}
    (hz : z ∈ U0 ℓ' Γ a b) {s : ℝ} (hs : s ∈ Icc a b) {τ : ℝ} (hτ : τ ∈ Icc a b) :
    Tendsto (fun n => dpic v ℓ' n τ z s) atTop (𝓝 (cjac v ℓ' τ z s)) :=
  tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric _ _ (by norm_num : (9 / 10 : ℝ) < 1) fun n => by
      rw [dist_comm, dist_eq_norm]
      exact norm_dpic_succ_sub_le hv hw hz hs n τ hτ))

theorem tendstoUniformlyOn_dpic (hv : HolField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) {s : ℝ}
    (hs : s ∈ Icc a b) {τ : ℝ} (hτ : τ ∈ Icc a b) :
    TendstoUniformlyOn (fun n z => dpic v ℓ' n τ z s) (fun z => cjac v ℓ' τ z s) atTop
      (U0 ℓ' Γ a b) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hlim : Tendsto (fun n : ℕ => dpicC ℓ ℓ' Γ V a b * (9 / 10) ^ n / (1 - 9 / 10)) atTop
      (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 9 / 10)
      (by norm_num : (9 / 10 : ℝ) < 1)).const_mul (dpicC ℓ ℓ' Γ V a b)
    rw [mul_zero] at this
    simpa using this.div_const (1 - 9 / 10 : ℝ)
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn
  intro z hz
  rw [dist_comm]
  refine lt_of_le_of_lt ?_ hn
  exact dist_le_of_le_geometric_of_tendsto _ _ (by norm_num : (9 / 10 : ℝ) < 1)
    (fun n => by
      rw [dist_comm, dist_eq_norm]
      exact norm_dpic_succ_sub_le hv hw hz hs n τ hτ) (tendsto_dpic hv hw hz hs hτ) n

/-- **The complex flow is holomorphic in the initial point.** -/
theorem hasFDerivAt_cflow (hv : HolField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) {s : ℝ}
    (hs : s ∈ Icc a b) {τ : ℝ} (hτ : τ ∈ Icc a b) {z : CVec} (hz : z ∈ U0 ℓ' Γ a b) :
    HasFDerivAt (fun x => cflow v ℓ' τ x s) (cjac v ℓ' τ z s) z :=
  hasFDerivAt_of_tendstoUniformlyOn isOpen_U0 (tendstoUniformlyOn_dpic hv hw hs hτ)
    (fun n x hx => hasFDerivAt_pic hv hw hs n τ hτ x hx)
    (fun _ hx => tendsto_pic hv.toStripField hw (U0_subset_Z0 hx) hs hτ) hz

theorem differentiableOn_cflow (hv : HolField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) {s : ℝ}
    (hs : s ∈ Icc a b) {τ : ℝ} (hτ : τ ∈ Icc a b) :
    DifferentiableOn ℂ (fun x => cflow v ℓ' τ x s) (U0 ℓ' Γ a b) :=
  fun _ hz => (hasFDerivAt_cflow hv hw hs hτ hz).differentiableAt.differentiableWithinAt

/-- **The Jacobian of the flow is close to the identity**: `‖cjac - I‖ ≤ 10 Γ |τ - s|`. -/
theorem norm_cjac_sub_one_le (hv : HolField v ℓ Γ V) (hw : FlowWin ℓ ℓ' Γ a b) {z : CVec}
    (hz : z ∈ U0 ℓ' Γ a b) {s : ℝ} (hs : s ∈ Icc a b) {τ : ℝ} (hτ : τ ∈ Icc a b) :
    ‖cjac v ℓ' τ z s - ContinuousLinearMap.id ℂ CVec‖ ≤ 10 * Γ * |τ - s| := by
  have hb : ∀ n, ‖dpic v ℓ' n τ z s - ContinuousLinearMap.id ℂ CVec‖ ≤ 10 * Γ * |τ - s| := by
    intro n
    cases n with
    | zero =>
      simp only [dpic, sub_self, norm_zero]
      exact mul_nonneg (by linarith [hv.hΓ]) (abs_nonneg _)
    | succ n =>
      rw [dpic_succ, add_sub_cancel_left]
      refine (intervalIntegral.norm_integral_le_of_norm_le_const fun σ hσ =>
        norm_dint_le hv.toStripField hw hz hs n (uIoc_subset_window hτ hs hσ)).trans (le_of_eq ?_)
      ring
  exact le_of_tendsto ((continuous_norm.tendsto _).comp
    ((tendsto_dpic hv hw hz hs hτ).sub_const _)) (Eventually.of_forall hb)

end AVRegularity.Providers.ComplexFlow
end

section
open MeasureTheory Set Filter Topology Homogenization Metric
namespace AVRegularity.Providers.ComplexFlow

/-! **Derivative bounds for holomorphic functions on strips.**
* `fderiv_ofRealVec_eq`: at a real point, the complex derivative of a holomorphic function that
  is real-valued on real points is the real derivative of its restriction (complex derivatives at
  real points are real derivatives).
* `norm_fderiv_le_of_strip`, `norm_fderiv_fderiv_le_of_strip`: Cauchy's estimates for the first
  and second derivatives of a function bounded by `K` on `S_ℓ`, at points of `S_{ℓ - 3ρ}` and
  `S_{ℓ - 6ρ}` (balls of radius `ρ` move `|Im|₁` by at most `2ρ`).
* `l1_sub_le_of_entry_le`: entrywise bounds `|∂_k v_i| ≤ M` on a convex open set give the
  `|·|₁`-Lipschitz bound `4M`. -/

open AVRegularity.Providers.GenSem

/-- The standard basis vector of `ℂ²`. -/
def cbasis (k : Fin 2) : CVec := Pi.single k 1

theorem norm_cbasis (k : Fin 2) : ‖cbasis k‖ = 1 := by
  unfold cbasis
  rw [Pi.norm_single, norm_one]

theorem ofRealVec_basisVec (k : Fin 2) : ofRealVec (basisVec k) = cbasis k := by
  funext a
  by_cases h : a = k
  · subst h
    simp [ofRealVec, cbasis, basisVec]
  · simp [ofRealVec, cbasis, basisVec, h]

/-- **At a real point the complex derivative is the real derivative.** -/
theorem fderiv_ofRealVec_eq {U : Set CVec} (hU : IsOpen U) {F : CVec → ℂ}
    (hF : DifferentiableOn ℂ F U) {f : Vec 2 → ℝ} (hFf : ∀ y, F (ofRealVec y) = (f y : ℂ))
    {x : Vec 2} (hx : ofRealVec x ∈ U) (w : Vec 2) :
    fderiv ℂ F (ofRealVec x) (ofRealVec w) = (fderiv ℝ f x w : ℂ) := by
  have hD : HasFDerivAt F (fderiv ℂ F (ofRealVec x)) (ofRealVec x) :=
    (hF.differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  -- the derivative of `y ↦ F (ofRealVec y)`
  have h1 : HasFDerivAt (fun y => F (ofRealVec y))
      (((fderiv ℂ F (ofRealVec x)).restrictScalars ℝ).comp ofRealVecCLM) x :=
    hD.restrictScalars ℝ |>.comp x ofRealVecCLM.hasFDerivAt
  have e1 : (fun y => F (ofRealVec y)) = fun y => ((f y : ℝ) : ℂ) := funext hFf
  rw [e1] at h1
  -- the real part
  have h2 : HasFDerivAt f (Complex.reCLM.comp
      (((fderiv ℂ F (ofRealVec x)).restrictScalars ℝ).comp ofRealVecCLM)) x := by
    have := Complex.reCLM.hasFDerivAt.comp x h1
    simpa [Function.comp_def] using this
  -- the imaginary part vanishes
  have h3 : HasFDerivAt (fun _ : Vec 2 => (0 : ℝ)) (Complex.imCLM.comp
      (((fderiv ℂ F (ofRealVec x)).restrictScalars ℝ).comp ofRealVecCLM)) x := by
    have := Complex.imCLM.hasFDerivAt.comp x h1
    simpa [Function.comp_def] using this
  have hz := h3.unique (hasFDerivAt_const (0 : ℝ) x)
  have him : (fderiv ℂ F (ofRealVec x) (ofRealVec w)).im = 0 := by
    have := congrArg (fun L => L w) hz
    simpa [ofRealVecCLM_apply] using this
  rw [h2.fderiv]
  apply Complex.ext
  · simp [ofRealVecCLM_apply]
  · simp [ofRealVecCLM_apply, him]

theorem closedBall_subset_strip_of {ℓ ρ : ℝ} (hρ : 0 < ρ) {y : CVec}
    (hy : imL1 y ≤ ℓ - 3 * ρ) : closedBall y ρ ⊆ strip ℓ := by
  intro z hz
  show imL1 z < ℓ
  have h1 := imL1_le_add_l1 z y
  have h2 := l1_le_two_mul_norm (z - y)
  rw [mem_closedBall, dist_eq_norm] at hz
  linarith

/-- **Cauchy's estimate for the first derivative on a strip.** -/
theorem norm_fderiv_le_of_strip {ℓ ρ K : ℝ} (hρ : 0 < ρ) {F : CVec → ℂ}
    (hF : DifferentiableOn ℂ F (strip ℓ)) (hK : ∀ z ∈ strip ℓ, ‖F z‖ ≤ K) {y : CVec}
    (hy : imL1 y ≤ ℓ - 3 * ρ) : ‖fderiv ℂ F y‖ ≤ K / ρ :=
  norm_fderiv_le_of_closedBall hρ (hF.mono (closedBall_subset_strip_of hρ hy))
    fun z hz => hK z (closedBall_subset_strip_of hρ hy hz)

/-- **Cauchy's estimate for the second derivatives on a strip.** -/
theorem norm_fderiv_fderiv_le_of_strip {ℓ ρ K : ℝ} (hρ : 0 < ρ) {F : CVec → ℂ}
    (hF : DifferentiableOn ℂ F (strip ℓ)) (hK : ∀ z ∈ strip ℓ, ‖F z‖ ≤ K) {w : CVec}
    (hw : ‖w‖ ≤ 1) {y : CVec} (hy : imL1 y ≤ ℓ - 6 * ρ) :
    ‖fderiv ℂ (fun z => fderiv ℂ F z w) y‖ ≤ K / ρ / ρ := by
  have hK0 : 0 ≤ K := by
    have h0 : imL1 y < ℓ := by
      have := imL1_nonneg y
      linarith
    exact (norm_nonneg _).trans (hK y h0)
  have hG := differentiableOn_fderiv_apply (isOpen_strip ℓ) hF w
  refine norm_fderiv_le_of_closedBall hρ (hG.mono (closedBall_subset_strip_of hρ (by linarith)))
    fun z hz => ?_
  have hz' : imL1 z ≤ ℓ - 3 * ρ := by
    have h1 := imL1_le_add_l1 z y
    have h2 := l1_le_two_mul_norm (z - y)
    rw [mem_closedBall, dist_eq_norm] at hz
    linarith
  calc ‖fderiv ℂ F z w‖ ≤ ‖fderiv ℂ F z‖ * ‖w‖ := (fderiv ℂ F z).le_opNorm w
    _ ≤ K / ρ * 1 :=
        mul_le_mul (norm_fderiv_le_of_strip hρ hF hK hz') hw (norm_nonneg _) (by positivity)
    _ = K / ρ := mul_one _

/-- **Entrywise derivative bounds give a `|·|₁`-Lipschitz bound.** -/
theorem l1_sub_le_of_entry_le {U : Set CVec} (hU : IsOpen U) (hUc : Convex ℝ U) {v : CVec → CVec}
    (hv : DifferentiableOn ℂ v U) {M : ℝ}
    (hM : ∀ y ∈ U, ∀ i k : Fin 2, ‖fderiv ℂ v y (cbasis k) i‖ ≤ M) {z w : CVec} (hz : z ∈ U)
    (hw : w ∈ U) : l1 (v z - v w) ≤ 4 * M * l1 (z - w) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM z hz 0 0)
  have hcomp : ∀ i : Fin 2, ‖v z i - v w i‖ ≤ 2 * M * ‖z - w‖ := by
    intro i
    have hdi : ∀ y ∈ U, DifferentiableAt ℂ (fun y' => v y' i) y := fun y hy =>
      (ContinuousLinearMap.proj i : CVec →L[ℂ] ℂ).differentiableAt.comp y
        ((hv y hy).differentiableAt (hU.mem_nhds hy))
    have hbd : ∀ y ∈ U, ‖fderiv ℂ (fun y' => v y' i) y‖ ≤ 2 * M := by
      intro y hy
      have hD : HasFDerivAt v (fderiv ℂ v y) y :=
        ((hv y hy).differentiableAt (hU.mem_nhds hy)).hasFDerivAt
      have h2 : HasFDerivAt (fun y' => v y' i)
          ((ContinuousLinearMap.proj i : CVec →L[ℂ] ℂ).comp (fderiv ℂ v y)) y :=
        ((ContinuousLinearMap.proj i : CVec →L[ℂ] ℂ).hasFDerivAt).comp y hD
      rw [h2.fderiv]
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
      have hu : u = u 0 • cbasis 0 + u 1 • cbasis 1 := by
        funext a
        fin_cases a <;> simp [cbasis]
      have hlin : (fderiv ℂ v y u) i =
          u 0 * (fderiv ℂ v y (cbasis 0) i) + u 1 * (fderiv ℂ v y (cbasis 1) i) := by
        conv_lhs => rw [hu]
        simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      show ‖(fderiv ℂ v y u) i‖ ≤ 2 * M * ‖u‖
      rw [hlin]
      have hu0 : ‖u 0‖ ≤ ‖u‖ := norm_le_pi_norm u 0
      have hu1 : ‖u 1‖ ≤ ‖u‖ := norm_le_pi_norm u 1
      calc ‖u 0 * (fderiv ℂ v y (cbasis 0) i) + u 1 * (fderiv ℂ v y (cbasis 1) i)‖
          ≤ ‖u 0‖ * M + ‖u 1‖ * M := by
            refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
            · rw [norm_mul]
              exact mul_le_mul_of_nonneg_left (hM y hy i 0) (norm_nonneg _)
            · rw [norm_mul]
              exact mul_le_mul_of_nonneg_left (hM y hy i 1) (norm_nonneg _)
        _ ≤ ‖u‖ * M + ‖u‖ * M :=
            add_le_add (mul_le_mul_of_nonneg_right hu0 hM0) (mul_le_mul_of_nonneg_right hu1 hM0)
        _ = 2 * M * ‖u‖ := by ring
    exact hUc.norm_image_sub_le_of_norm_fderiv_le hdi hbd hw hz
  unfold l1
  calc ∑ i, ‖(v z - v w) i‖ = ∑ i, ‖v z i - v w i‖ := rfl
    _ ≤ ∑ _i : Fin 2, 2 * M * ‖z - w‖ := Finset.sum_le_sum fun i _ => hcomp i
    _ = 4 * M * ‖z - w‖ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
    _ ≤ 4 * M * l1 (z - w) := mul_le_mul_of_nonneg_left (norm_le_l1 _) (by positivity)

end AVRegularity.Providers.ComplexFlow
end
