-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

section
namespace AVRegularity.FastProfile

/-! Smooth transition used in the construction of an admissible fast profile. -/

open Real

/-- A smooth step with a central transition interval of length `1/50`. -/
noncomputable def step (x : ℝ) : ℝ :=
  Real.smoothTransition (50 * x - 49 / 2)

theorem contDiff_step : ContDiff ℝ (⊤ : ℕ∞) step := by
  unfold step
  fun_prop

theorem step_monotone : Monotone step := by
  intro x y hxy
  unfold step
  apply Real.smoothTransition.monotone
  linarith

theorem step_zero_of_le {x : ℝ} (h : x ≤ 49 / 100) : step x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  linarith [h]

theorem step_one_of_ge {x : ℝ} (h : 51 / 100 ≤ x) : step x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  linarith [h]

theorem smoothTransition_add_one_sub (x : ℝ) :
    Real.smoothTransition x + Real.smoothTransition (1 - x) = 1 := by
  unfold Real.smoothTransition
  have hrewrite : expNegInvGlue (1 - (1 - x)) = expNegInvGlue x := by
    congr 1
    ring
  rw [hrewrite]
  have hden : 0 < expNegInvGlue x + expNegInvGlue (1 - x) :=
    Real.smoothTransition.pos_denom x
  rw [show expNegInvGlue (1 - x) + expNegInvGlue x =
      expNegInvGlue x + expNegInvGlue (1 - x) by ring]
  rw [← add_div]
  exact div_self (ne_of_gt hden)

theorem step_add_one_sub (x : ℝ) : step x + step (1 - x) = 1 := by
  unfold step
  rw [show 50 * (1 - x) - 49 / 2 = 1 - (50 * x - 49 / 2) by ring]
  exact smoothTransition_add_one_sub _

theorem step_one_sub (x : ℝ) : step (1 - x) = 1 - step x := by
  linarith [step_add_one_sub x]

end AVRegularity.FastProfile
end

section
open Set MeasureTheory
namespace AVRegularity.FastProfile

/-! A compact smooth partition profile with a tunable exact square integral. -/

/-- The square integral of the sharp smooth step on its unit transition interval. -/
noncomputable def stepSqIntegral : ℝ := ∫ x in (0 : ℝ)..1, step x ^ 2

theorem stepSqIntegral_ge : 49 / 100 ≤ stepSqIntegral := by
  unfold stepSqIntegral
  let f : ℝ → ℝ := fun x => step x ^ 2
  have hf : Continuous f := by
    dsimp [f]
    exact contDiff_step.continuous.pow 2
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ := volume) (0 : ℝ) (51 / 100))
    (hf.intervalIntegrable (μ := volume) (51 / 100) 1)
  have hleft : 0 ≤ ∫ x in (0 : ℝ)..(51 / 100), f x := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    exact sq_nonneg _
  have hright : (∫ x in (51 / 100 : ℝ)..1, f x) = 49 / 100 := by
    rw [intervalIntegral.integral_congr (f := f) (g := fun _ => (1 : ℝ))]
    · simp [intervalIntegral.integral_const]
      norm_num
    · intro x hx
      simp only [mem_uIcc] at hx
      rcases hx with hx | hx
      · change step x ^ 2 = 1
        rw [step_one_of_ge hx.1]
        norm_num
      · have : (1 : ℝ) ≤ 51 / 100 := le_trans hx.1 hx.2
        norm_num at this
  rw [← hsplit]
  dsimp [f] at hleft hright ⊢
  linarith

theorem stepSqIntegral_pos : 0 < stepSqIntegral := by
  linarith [stepSqIntegral_ge]

theorem stepIntegral_eq_half : (∫ x in (0 : ℝ)..1, step x) = 1 / 2 := by
  have hcont : Continuous step := contDiff_step.continuous
  have hint : IntervalIntegrable step volume (0 : ℝ) 1 := hcont.intervalIntegrable _ _
  have hsymm : (∫ x in (0 : ℝ)..1, step (1 - x)) = ∫ x in (0 : ℝ)..1, step x := by
    calc
      (∫ x in (0 : ℝ)..1, step (1 - x)) =
          ∫ x in (0 : ℝ)..1, step ((-1 : ℝ) * x + 1) := by
            congr 1
            funext x
            ring_nf
      _ = ((-1 : ℝ)⁻¹) • ∫ x in (1 : ℝ)..0, step x := by
        simpa using (intervalIntegral.integral_comp_mul_add (a := (0 : ℝ)) (b := 1)
          (c := (-1 : ℝ)) step (by norm_num) 1)
      _ = ∫ x in (0 : ℝ)..1, step x := by
        rw [intervalIntegral.integral_symm]
        simp
  have hsum : (∫ x in (0 : ℝ)..1, step x) +
      (∫ x in (0 : ℝ)..1, step (1 - x)) = 1 := by
    have hadd : (∫ x in (0 : ℝ)..1, (step x + step (1 - x))) =
        (∫ x in (0 : ℝ)..1, step x) + (∫ x in (0 : ℝ)..1, step (1 - x)) := by
      exact intervalIntegral.integral_add hint
        ((hcont.comp (continuous_const.sub continuous_id)).intervalIntegrable _ _)
    calc
      _ = ∫ x in (0 : ℝ)..1, (step x + step (1 - x)) := hadd.symm
      _ = ∫ x in (0 : ℝ)..1, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact step_add_one_sub x
      _ = 1 := by simp [intervalIntegral.integral_const]
  rw [hsymm] at hsum
  linarith

/-- A smooth monotone transition from zero to one, with a constant half-height middle.
The parameter `δ` is the width of each of the two end transitions. -/
noncomputable def rho (δ u : ℝ) : ℝ :=
  1 / 2 - (1 / 2) * step (1 - u / δ) + (1 / 2) * step ((u - (1 - δ)) / δ)

theorem contDiff_rho (δ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (rho δ) := by
  unfold rho step
  fun_prop

theorem rho_mono {δ : ℝ} (hδ : 0 < δ) : Monotone (rho δ) := by
  intro x y hxy
  unfold rho
  have hquot : x / δ ≤ y / δ := (div_le_div_iff_of_pos_right hδ).2 hxy
  have hfirst : 1 - y / δ ≤ 1 - x / δ := by linarith
  have hsecond : (x - (1 - δ)) / δ ≤ (y - (1 - δ)) / δ := by
    rw [div_le_div_iff_of_pos_right hδ]
    linarith
  have hA := step_monotone hfirst
  have hB := step_monotone hsecond
  linarith

theorem rho_eq_zero_of_le_zero {δ u : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hu : u ≤ 0) : rho δ u = 0 := by
  unfold rho
  have hA : 51 / 100 ≤ 1 - u / δ := by
    have : u / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hu hδ.le
    linarith
  have hB : (u - (1 - δ)) / δ ≤ 49 / 100 := by
    have hnum : u - (1 - δ) ≤ 0 := by linarith
    have hdiv : (u - (1 - δ)) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hnum hδ.le
    linarith
  rw [step_one_of_ge hA, step_zero_of_le hB]
  ring

theorem rho_eq_one_of_one_le {δ u : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hu : 1 ≤ u) : rho δ u = 1 := by
  unfold rho
  have hA : 1 - u / δ ≤ 49 / 100 := by
    have hquot : δ / δ ≤ u / δ := (div_le_div_iff_of_pos_right hδ).2 (by linarith)
    have hquot' : 1 ≤ u / δ := by simpa [hδ.ne'] using hquot
    linarith
  have hB : 51 / 100 ≤ (u - (1 - δ)) / δ := by
    have hnum : δ ≤ u - (1 - δ) := by linarith
    have hquot : δ / δ ≤ (u - (1 - δ)) / δ :=
      (div_le_div_iff_of_pos_right hδ).2 hnum
    have hquot' : 1 ≤ (u - (1 - δ)) / δ := by simpa [hδ.ne'] using hquot
    linarith
  rw [step_zero_of_le hA, step_one_of_ge hB]
  ring

theorem rho_one_sub {δ u : ℝ} (hδ : δ ≠ 0) : rho δ (1 - u) = 1 - rho δ u := by
  unfold rho
  have hA : 1 - (1 - u) / δ = (u - (1 - δ)) / δ := by field_simp; ring
  have hB : ((1 - u) - (1 - δ)) / δ = 1 - u / δ := by field_simp; ring
  rw [hA, hB]
  ring

theorem rho_left_eq {δ u : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (huδ : u ≤ δ) : rho δ u = (1 / 2) * step (u / δ) := by
  unfold rho
  have hsecond : (u - (1 - δ)) / δ ≤ 49 / 100 := by
    have hnum : u - (1 - δ) ≤ 2 * δ - 1 := by linarith
    have hquot : (u - (1 - δ)) / δ ≤ (2 * δ - 1) / δ :=
      (div_le_div_iff_of_pos_right hδ).2 hnum
    have hneg : (2 * δ - 1) / δ ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
    linarith
  rw [step_zero_of_le hsecond, step_one_sub (u / δ)]
  ring

theorem rho_middle_eq {δ u : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (huδ : δ ≤ u) (hu1 : u ≤ 1 - δ) : rho δ u = 1 / 2 := by
  unfold rho
  have hfirst : 1 - u / δ ≤ 49 / 100 := by
    have hquot : δ / δ ≤ u / δ := (div_le_div_iff_of_pos_right hδ).2 huδ
    have hquot' : 1 ≤ u / δ := by simpa [hδ.ne'] using hquot
    linarith
  have hsecond : (u - (1 - δ)) / δ ≤ 49 / 100 := by
    have hnum : u - (1 - δ) ≤ 0 := by linarith
    have hquot : (u - (1 - δ)) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hnum hδ.le
    linarith
  rw [step_zero_of_le hfirst, step_zero_of_le hsecond]
  ring

theorem rho_right_eq {δ u : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (hu1 : 1 - δ ≤ u) :
    rho δ u = 1 / 2 + (1 / 2) * step ((u - (1 - δ)) / δ) := by
  unfold rho
  have hfirst : 1 - u / δ ≤ 49 / 100 := by
    have hnum : δ ≤ u := by linarith
    have hquot : δ / δ ≤ u / δ := (div_le_div_iff_of_pos_right hδ).2 hnum
    have hquot' : 1 ≤ u / δ := by simpa [hδ.ne'] using hquot
    linarith
  rw [step_zero_of_le hfirst]
  ring

theorem rhoSqIntegral_eq {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ < 1 / 2) :
    (∫ x in (0 : ℝ)..1, rho δ x ^ 2) = 1 / 4 + (δ / 2) * stepSqIntegral := by
  let f : ℝ → ℝ := fun x => rho δ x ^ 2
  have hf : Continuous f := by
    dsimp [f]
    exact (contDiff_rho δ).continuous.pow 2
  have hleftInt := hf.intervalIntegrable (μ := volume) (0 : ℝ) δ
  have hmidInt := hf.intervalIntegrable (μ := volume) δ (1 - δ)
  have hrightInt := hf.intervalIntegrable (μ := volume) (1 - δ) 1
  have hsplit₂ := intervalIntegral.integral_add_adjacent_intervals hmidInt hrightInt
  have hsplitTotal := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ := volume) (0 : ℝ) δ)
    (hf.intervalIntegrable (μ := volume) δ 1)
  have hleft : (∫ x in (0 : ℝ)..δ, f x) =
      (δ / 4) * stepSqIntegral := by
    have hscale : (∫ x in (0 : ℝ)..δ, step (x / δ) ^ 2) = δ * stepSqIntegral := by
      rw [intervalIntegral.integral_comp_div (fun x => step x ^ 2) hδ.ne']
      simp [stepSqIntegral, hδ.ne']
    calc
      (∫ x in (0 : ℝ)..δ, f x) =
          ∫ x in (0 : ℝ)..δ, (1 / 4) * step (x / δ) ^ 2 := by
            apply intervalIntegral.integral_congr
            intro x hx
            change rho δ x ^ 2 = (1 / 4) * step (x / δ) ^ 2
            simp only [mem_uIcc] at hx
            rcases hx with hx | hx
            · rw [rho_left_eq hδ hδhalf hx.2]
              ring
            · have hbad : δ ≤ 0 := le_trans hx.1 hx.2
              exact (False.elim ((not_le_of_gt hδ) hbad))
      _ = (1 / 4) * ∫ x in (0 : ℝ)..δ, step (x / δ) ^ 2 := by
        rw [intervalIntegral.integral_const_mul]
      _ = (δ / 4) * stepSqIntegral := by rw [hscale]; ring
  have hmid : (∫ x in δ..(1 - δ), f x) = (1 - 2 * δ) / 4 := by
    calc
      (∫ x in δ..(1 - δ), f x) = ∫ x in δ..(1 - δ), (fun _ : ℝ => (1 / 4 : ℝ)) x := by
        apply intervalIntegral.integral_congr
        intro x hx
        change rho δ x ^ 2 = 1 / 4
        simp only [mem_uIcc] at hx
        rcases hx with hx | hx
        · rw [rho_middle_eq hδ hδhalf hx.1 hx.2]
          ring
        · have hbad : (1 : ℝ) ≤ 2 * δ := by linarith
          have : 1 / 2 ≤ δ := by linarith
          exact (False.elim ((not_le_of_gt hδhalf) this))
      _ = (1 - 2 * δ) / 4 := by
        rw [intervalIntegral.integral_const]
        norm_num
        ring
  have hq : (∫ x in (0 : ℝ)..1, (1 / 2 + (1 / 2) * step x) ^ 2) =
      1 / 2 + (1 / 4) * stepSqIntegral := by
    let f₁ : ℝ → ℝ := fun x => (1 / 4 : ℝ) + (1 / 2) * step x
    let f₂ : ℝ → ℝ := fun x => (1 / 4 : ℝ) * step x ^ 2
    have hcont₁ : Continuous (fun x : ℝ => (1 / 4 : ℝ)) := continuous_const
    have hcont₂ : Continuous (fun x : ℝ => (1 / 2 : ℝ) * step x) :=
      continuous_const.mul contDiff_step.continuous
    have hcont₃ : Continuous (fun x : ℝ => (1 / 4 : ℝ) * step x ^ 2) :=
      continuous_const.mul (contDiff_step.continuous.pow 2)
    have hcontF₁ : Continuous f₁ := by
      dsimp [f₁]
      exact hcont₁.add hcont₂
    have hsum₁ : (∫ x in (0 : ℝ)..1, f₁ x) =
        (∫ x in (0 : ℝ)..1, (1 / 4 : ℝ)) +
          (∫ x in (0 : ℝ)..1, (1 / 2 : ℝ) * step x) := by
      dsimp [f₁]
      exact intervalIntegral.integral_add (hcont₁.intervalIntegrable _ _)
        (hcont₂.intervalIntegrable _ _)
    have hsum₂ : (∫ x in (0 : ℝ)..1, f₁ x + f₂ x) =
        (∫ x in (0 : ℝ)..1, f₁ x) + (∫ x in (0 : ℝ)..1, f₂ x) := by
      exact intervalIntegral.integral_add
        (hcontF₁.intervalIntegrable _ _)
        (hcont₃.intervalIntegrable _ _)
    calc
      (∫ x in (0 : ℝ)..1, (1 / 2 + (1 / 2) * step x) ^ 2) =
          ∫ x in (0 : ℝ)..1, f₁ x + f₂ x := by
        apply intervalIntegral.integral_congr
        intro x hx
        dsimp [f₁, f₂]
        ring
      _ = (∫ x in (0 : ℝ)..1, f₁ x) + (∫ x in (0 : ℝ)..1, f₂ x) := hsum₂
      _ = (∫ x in (0 : ℝ)..1, (1 / 4 : ℝ)) +
          (∫ x in (0 : ℝ)..1, (1 / 2 : ℝ) * step x) +
          (∫ x in (0 : ℝ)..1, (1 / 4 : ℝ) * step x ^ 2) := by rw [hsum₁]
      _ = 1 / 2 + (1 / 4) * stepSqIntegral := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
        rw [intervalIntegral.integral_const, stepIntegral_eq_half]
        simp [stepSqIntegral]
        ring
  have hscaleRight :
      (∫ x in (1 - δ)..1, (1 / 2 + (1 / 2) * step ((x - (1 - δ)) / δ)) ^ 2) =
        δ * (1 / 2 + (1 / 4) * stepSqIntegral) := by
    let q : ℝ → ℝ := fun x => (1 / 2 + (1 / 2) * step x) ^ 2
    have hshift : (∫ x in (0 : ℝ)..δ, q (x / δ)) =
        ∫ x in (1 - δ)..1, q ((x - (1 - δ)) / δ) := by
      calc
        (∫ x in (0 : ℝ)..δ, q (x / δ)) =
            ∫ x in (0 : ℝ)..δ,
              (fun y => q ((y - (1 - δ)) / δ)) (x + (1 - δ)) := by
                apply intervalIntegral.integral_congr
                intro x hx
                congr 2; ring
        _ = ∫ x in (1 - δ)..1, q ((x - (1 - δ)) / δ) := by
          have hcomp := intervalIntegral.integral_comp_add_right (a := (0 : ℝ))
            (b := δ) (f := fun y => q ((y - (1 - δ)) / δ)) (1 - δ)
          simpa only [zero_add, show δ + (1 - δ) = (1 : ℝ) by ring] using hcomp
    calc
      (∫ x in (1 - δ)..1, q ((x - (1 - δ)) / δ)) =
          ∫ x in (0 : ℝ)..δ, q (x / δ) := by
        exact hshift.symm
      _ = δ * ∫ x in (0 : ℝ)..1, q x := by
        rw [intervalIntegral.integral_comp_div q hδ.ne']
        simp [hδ.ne']
      _ = δ * (1 / 2 + (1 / 4) * stepSqIntegral) := by rw [hq]
  have hright : (∫ x in (1 - δ)..1, f x) =
      δ * (1 / 2 + (1 / 4) * stepSqIntegral) := by
    calc
      (∫ x in (1 - δ)..1, f x) =
          ∫ x in (1 - δ)..1,
            (1 / 2 + (1 / 2) * step ((x - (1 - δ)) / δ)) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro x hx
        change rho δ x ^ 2 =
          (1 / 2 + (1 / 2) * step ((x - (1 - δ)) / δ)) ^ 2
        simp only [mem_uIcc] at hx
        rcases hx with hx | hx
        · rw [rho_right_eq hδ hδhalf hx.1]
        · have hbad : (1 : ℝ) ≤ 2 * δ := by linarith
          have : 1 / 2 ≤ δ := by linarith
          exact (False.elim ((not_le_of_gt hδhalf) this))
      _ = δ * (1 / 2 + (1 / 4) * stepSqIntegral) := hscaleRight
  rw [← hsplitTotal, ← hsplit₂]
  dsimp [f] at hleft hmid hright ⊢
  rw [hleft, hmid, hright]
  ring

theorem rho_nonneg {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (u : ℝ) : 0 ≤ rho δ u := by
  have hmono := rho_mono hδ
  have hzero : rho δ 0 = 0 := rho_eq_zero_of_le_zero hδ hδ1 le_rfl
  rcases le_total 0 u with hu | hu
  · rw [← hzero]
    exact hmono hu
  · rw [rho_eq_zero_of_le_zero hδ hδ1 hu]

theorem rho_le_one {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (u : ℝ) : rho δ u ≤ 1 := by
  have hmono := rho_mono hδ
  have hval : rho δ 1 = 1 := rho_eq_one_of_one_le hδ hδ1 le_rfl
  rcases le_total u 1 with hu | hu
  · calc
      rho δ u ≤ rho δ 1 := hmono hu
      _ = 1 := hval
  · rw [rho_eq_one_of_one_le hδ hδ1 hu]

/-- The tuned width makes the squared integral of `rho` exactly `3/10`. -/
noncomputable def transitionWidth : ℝ := 1 / (10 * stepSqIntegral)

theorem transitionWidth_pos : 0 < transitionWidth := by
  unfold transitionWidth
  have hA := stepSqIntegral_pos
  positivity

theorem transitionWidth_lt_half : transitionWidth < 1 / 2 := by
  unfold transitionWidth
  have hApos := stepSqIntegral_pos
  have hA := stepSqIntegral_ge
  have hden : 0 < 10 * stepSqIntegral := by positivity
  apply (div_lt_div_iff₀ hden (by norm_num)).2
  norm_num
  nlinarith

/-- A smooth step supported on the short interval `[-1/8, 1/8]`. -/
noncomputable def transition (x : ℝ) : ℝ := rho transitionWidth (4 * x + 1 / 2)

theorem contDiff_transition : ContDiff ℝ (⊤ : ℕ∞) transition := by
  unfold transition
  exact (contDiff_rho transitionWidth).comp (by fun_prop)

theorem transition_mono : Monotone transition := by
  intro x y hxy
  unfold transition
  apply rho_mono transitionWidth_pos
  linarith

theorem transition_eq_zero_of_le {x : ℝ} (hx : x ≤ -(1 / 8)) : transition x = 0 := by
  unfold transition
  apply rho_eq_zero_of_le_zero transitionWidth_pos
  · linarith [transitionWidth_lt_half]
  · linarith

theorem transition_eq_one_of_ge {x : ℝ} (hx : 1 / 8 ≤ x) : transition x = 1 := by
  unfold transition
  apply rho_eq_one_of_one_le transitionWidth_pos
  · linarith [transitionWidth_lt_half]
  · linarith

theorem transition_one_sub (x : ℝ) : transition (-x) = 1 - transition x := by
  unfold transition
  have harg : 4 * -x + 1 / 2 = 1 - (4 * x + 1 / 2) := by ring
  rw [harg, rho_one_sub (δ := transitionWidth) (u := 4 * x + 1 / 2)
    (ne_of_gt transitionWidth_pos)]

theorem transition_nonneg (x : ℝ) : 0 ≤ transition x := by
  unfold transition
  exact rho_nonneg transitionWidth_pos (by linarith [transitionWidth_lt_half]) _

theorem transition_le_one (x : ℝ) : transition x ≤ 1 := by
  unfold transition
  exact rho_le_one transitionWidth_pos (by linarith [transitionWidth_lt_half]) _

/-- The final cardinal partition of unity. -/
noncomputable def fastProfile (t : ℝ) : ℝ := transition (t + 1 / 2) - transition (t - 1 / 2)

theorem contDiff_fastProfile : ContDiff ℝ (⊤ : ℕ∞) fastProfile := by
  unfold fastProfile
  exact (contDiff_transition.comp (by fun_prop)).sub (contDiff_transition.comp (by fun_prop))

theorem fastProfile_even (t : ℝ) : fastProfile (-t) = fastProfile t := by
  unfold fastProfile
  rw [show -t + 1 / 2 = -(t - 1 / 2) by ring,
    show -t - 1 / 2 = -(t + 1 / 2) by ring,
    transition_one_sub (t - 1 / 2), transition_one_sub (t + 1 / 2)]
  ring

theorem fastProfile_nonneg (t : ℝ) : 0 ≤ fastProfile t := by
  unfold fastProfile
  have hmono := transition_mono (show t - 1 / 2 ≤ t + 1 / 2 by linarith)
  linarith

theorem fastProfile_le_one (t : ℝ) : fastProfile t ≤ 1 := by
  unfold fastProfile
  linarith [transition_nonneg (t - 1 / 2), transition_le_one (t + 1 / 2)]

theorem fastProfile_zero_of_ge {t : ℝ} (ht : 5 / 8 ≤ t) : fastProfile t = 0 := by
  unfold fastProfile
  rw [transition_eq_one_of_ge (by linarith : 1 / 8 ≤ t + 1 / 2),
    transition_eq_one_of_ge (by linarith : 1 / 8 ≤ t - 1 / 2)]
  ring

theorem fastProfile_zero_of_le {t : ℝ} (ht : t ≤ -(5 / 8)) : fastProfile t = 0 := by
  unfold fastProfile
  rw [transition_eq_zero_of_le (by linarith : t + 1 / 2 ≤ -(1 / 8)),
    transition_eq_zero_of_le (by linarith : t - 1 / 2 ≤ -(1 / 8))]
  ring

theorem fastProfile_pair {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    fastProfile t + fastProfile (t - 1) = 1 := by
  unfold fastProfile
  rw [transition_eq_one_of_ge (by linarith : 1 / 8 ≤ t + 1 / 2)]
  rw [show t - 1 + 1 / 2 = t - 1 / 2 by ring]
  rw [show t - 1 - 1 / 2 = t - 3 / 2 by ring]
  rw [transition_eq_zero_of_le (by linarith : t - 3 / 2 ≤ -(1 / 8))]
  ring

theorem fastProfile_negTail_eq {x : ℝ}
    (hx : x ∈ Set.uIcc (-(5 / 8)) (-(3 / 8))) :
    fastProfile x = rho transitionWidth (4 * x + 5 / 2) := by
  simp only [mem_uIcc] at hx
  rcases hx with hx | hx
  · unfold fastProfile
    rw [transition_eq_zero_of_le (by linarith : x - 1 / 2 ≤ -(1 / 8))]
    unfold transition
    simp only [sub_zero]
    exact congrArg (rho transitionWidth) (by ring)
  · have hbad : (-(3 / 8) : ℝ) ≤ -(5 / 8) := le_trans hx.1 hx.2
    norm_num at hbad

theorem fastProfile_posTail_eq {x : ℝ}
    (hx : x ∈ Set.uIcc (3 / 8) (5 / 8)) :
    fastProfile x = rho transitionWidth ((-4 : ℝ) * x + 5 / 2) := by
  simp only [mem_uIcc] at hx
  rcases hx with hx | hx
  · unfold fastProfile
    rw [transition_eq_one_of_ge (by linarith : 1 / 8 ≤ x + 1 / 2)]
    unfold transition
    have harg : 4 * (x - 1 / 2) + 1 / 2 = 4 * x - 3 / 2 := by ring
    rw [harg, ← rho_one_sub (δ := transitionWidth) (u := 4 * x - 3 / 2)
      (ne_of_gt transitionWidth_pos)]
    congr 1
    ring
  · have hbad : (5 / 8 : ℝ) ≤ 3 / 8 := le_trans hx.1 hx.2
    norm_num at hbad

theorem fastProfile_mid_eq {x : ℝ}
    (hx : x ∈ Set.uIcc (-(3 / 8)) (3 / 8)) : fastProfile x = 1 := by
  simp only [mem_uIcc] at hx
  rcases hx with hx | hx
  · unfold fastProfile
    rw [transition_eq_one_of_ge (by linarith : 1 / 8 ≤ x + 1 / 2),
      transition_eq_zero_of_le (by linarith : x - 1 / 2 ≤ -(1 / 8))]
    ring
  · have hbad : (3 / 8 : ℝ) ≤ -(3 / 8) := le_trans hx.1 hx.2
    norm_num at hbad

theorem fastProfile_periodization (t : ℝ) : ∑' k : ℤ, fastProfile (t - k) = 1 := by
  classical
  let n : ℤ := ⌊t⌋
  let r : ℝ := t - (n : ℝ)
  have hr0 : 0 ≤ r := by
    change 0 ≤ Int.fract t
    exact Int.fract_nonneg t
  have hr1 : r < 1 := by
    change Int.fract t < 1
    exact Int.fract_lt_one t
  have hzero : ∀ k : ℤ, k ∉ ({n, n + 1} : Finset ℤ) → fastProfile (t - k) = 0 := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    have hcases : k < n ∨ n + 1 < k := by omega
    rcases hcases with hkleft | hkrght
    · have hk' : k ≤ n - 1 := by omega
      have hkreal : (k : ℝ) ≤ (n : ℝ) - 1 := by exact_mod_cast hk'
      have hdist : 5 / 8 ≤ t - (k : ℝ) := by
        have hfloor : (n : ℝ) ≤ t := Int.floor_le t
        linarith
      exact fastProfile_zero_of_ge hdist
    · have hk' : n + 2 ≤ k := by omega
      have hkreal : (n : ℝ) + 2 ≤ (k : ℝ) := by exact_mod_cast hk'
      have hdist : t - (k : ℝ) ≤ -(5 / 8) := by
        have hfloor : t < (n : ℝ) + 1 := by
          dsimp [n]
          exact Int.lt_floor_add_one t
        linarith
      exact fastProfile_zero_of_le hdist
  rw [tsum_eq_sum hzero]
  have harg₁ : t - (n : ℝ) = r := rfl
  have harg₂ : t - ((n + 1 : ℤ) : ℝ) = r - 1 := by
    dsimp [r]
    push_cast
    ring
  rw [Finset.sum_insert (by simp), Finset.sum_singleton, harg₁, harg₂]
  exact fastProfile_pair hr0 hr1

theorem tsupport_fastProfile_subset :
    tsupport fastProfile ⊆ Set.Ioo (-(2 / 3)) (2 / 3) := by
  have hclosed : tsupport fastProfile ⊆ Set.Icc (-(5 / 8)) (5 / 8) := by
    change closure (Function.support fastProfile) ⊆ Set.Icc (-(5 / 8)) (5 / 8)
    apply closure_minimal
    · intro t ht
      simp only [Function.mem_support] at ht
      by_contra hout
      simp only [mem_Icc, not_and_or, not_le] at hout
      rcases hout with hleft | hright
      · exact ht (fastProfile_zero_of_le hleft.le)
      · exact ht (fastProfile_zero_of_ge hright.le)
    · exact isClosed_Icc
  intro t ht
  have ht' := hclosed ht
  simp only [mem_Icc] at ht'
  constructor
  · linarith
  · linarith

/-! Exact square-integral calculation for the compact smooth partition profile. -/

noncomputable def rhoSqBase (u : ℝ) : ℝ := rho transitionWidth u ^ 2

noncomputable def tunedRhoSqIntegral : ℝ := ∫ x in (0 : ℝ)..1, rhoSqBase x

theorem tunedRhoSqIntegral_eq : tunedRhoSqIntegral = 3 / 10 := by
  unfold tunedRhoSqIntegral rhoSqBase
  rw [rhoSqIntegral_eq transitionWidth_pos transitionWidth_lt_half]
  unfold transitionWidth
  have hA := stepSqIntegral_pos
  field_simp [ne_of_gt hA]
  ring

theorem rhoSqBase_left_integral :
    (∫ x in (-(5 / 8))..(-(3 / 8)), rhoSqBase (4 * x + 5 / 2)) =
      (1 / 4) * tunedRhoSqIntegral := by
  have hcomp := intervalIntegral.integral_comp_mul_add
    (a := (-(5 / 8) : ℝ)) (b := (-(3 / 8) : ℝ)) (c := (4 : ℝ))
    (f := rhoSqBase) (by norm_num) (5 / 2)
  convert hcomp using 1
  all_goals norm_num [rhoSqBase, tunedRhoSqIntegral]

theorem rhoSqBase_right_integral :
    (∫ x in (3 / 8)..(5 / 8), rhoSqBase ((-4 : ℝ) * x + 5 / 2)) =
      (1 / 4) * tunedRhoSqIntegral := by
  have hcomp := intervalIntegral.integral_comp_mul_add
    (a := (3 / 8 : ℝ)) (b := (5 / 8 : ℝ)) (c := (-4 : ℝ))
    (f := rhoSqBase) (by norm_num) (5 / 2)
  have hcomp' : (∫ x in (3 / 8)..(5 / 8),
      rhoSqBase ((-4 : ℝ) * x + 5 / 2)) =
        ((-4 : ℝ)⁻¹) • ∫ x in (1 : ℝ)..0, rhoSqBase x := by
    simpa only [show (-4 : ℝ) * (3 / 8) + 5 / 2 = 1 by norm_num,
      show (-4 : ℝ) * (5 / 8) + 5 / 2 = 0 by norm_num] using hcomp
  rw [hcomp', intervalIntegral.integral_symm]
  simp only [smul_eq_mul]
  norm_num
  rw [← tunedRhoSqIntegral]

theorem fastProfile_negSqIntegral :
    (∫ x in (-(5 / 8))..(-(3 / 8)), fastProfile x ^ 2) =
      (1 / 4) * tunedRhoSqIntegral := by
  calc
    (∫ x in (-(5 / 8))..(-(3 / 8)), fastProfile x ^ 2) =
        ∫ x in (-(5 / 8))..(-(3 / 8)), rhoSqBase (4 * x + 5 / 2) := by
      apply intervalIntegral.integral_congr
      intro x hx
      change fastProfile x ^ 2 = rhoSqBase (4 * x + 5 / 2)
      rw [fastProfile_negTail_eq hx]
      rfl
    _ = (1 / 4) * tunedRhoSqIntegral := rhoSqBase_left_integral

theorem fastProfile_midSqIntegral :
    (∫ x in (-(3 / 8))..(3 / 8), fastProfile x ^ 2) = 3 / 4 := by
  calc
    (∫ x in (-(3 / 8))..(3 / 8), fastProfile x ^ 2) =
        ∫ x in (-(3 / 8))..(3 / 8), (fun _ : ℝ => (1 : ℝ)) x := by
      apply intervalIntegral.integral_congr
      intro x hx
      change fastProfile x ^ 2 = 1
      rw [fastProfile_mid_eq hx]
      norm_num
    _ = 3 / 4 := by rw [intervalIntegral.integral_const]; norm_num

theorem fastProfile_posSqIntegral :
    (∫ x in (3 / 8)..(5 / 8), fastProfile x ^ 2) =
      (1 / 4) * tunedRhoSqIntegral := by
  calc
    (∫ x in (3 / 8)..(5 / 8), fastProfile x ^ 2) =
        ∫ x in (3 / 8)..(5 / 8), rhoSqBase ((-4 : ℝ) * x + 5 / 2) := by
      apply intervalIntegral.integral_congr
      intro x hx
      change fastProfile x ^ 2 = rhoSqBase ((-4 : ℝ) * x + 5 / 2)
      rw [fastProfile_posTail_eq hx]
      rfl
    _ = (1 / 4) * tunedRhoSqIntegral := rhoSqBase_right_integral

theorem fastProfile_intervalIntegral_sq :
    (∫ x in (-(5 / 8))..(5 / 8), fastProfile x ^ 2) = 9 / 10 := by
  let f : ℝ → ℝ := fun x => fastProfile x ^ 2
  have hf : Continuous f := by
    dsimp [f]
    exact contDiff_fastProfile.continuous.pow 2
  have hsplit : (∫ x in (-(5 / 8))..(-(3 / 8)), f x) +
      (∫ x in (-(3 / 8))..(5 / 8), f x) =
        ∫ x in (-(5 / 8))..(5 / 8), f x :=
    intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (μ := volume) (-(5 / 8)) (-(3 / 8)))
      (hf.intervalIntegrable (μ := volume) (-(3 / 8)) (5 / 8))
  have hsplitRight : (∫ x in (-(3 / 8))..(3 / 8), f x) +
      (∫ x in (3 / 8)..(5 / 8), f x) =
        ∫ x in (-(3 / 8))..(5 / 8), f x :=
    intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (μ := volume) (-(3 / 8)) (3 / 8))
      (hf.intervalIntegrable (μ := volume) (3 / 8) (5 / 8))
  calc
    (∫ x in (-(5 / 8))..(5 / 8), fastProfile x ^ 2) =
        (∫ x in (-(5 / 8))..(-(3 / 8)), f x) +
          (∫ x in (-(3 / 8))..(5 / 8), f x) := hsplit.symm
    _ = (∫ x in (-(5 / 8))..(-(3 / 8)), f x) +
          ((∫ x in (-(3 / 8))..(3 / 8), f x) +
            (∫ x in (3 / 8)..(5 / 8), f x)) := by rw [hsplitRight]
    _ = 9 / 10 := by
      dsimp [f]
      rw [fastProfile_negSqIntegral, fastProfile_midSqIntegral,
        fastProfile_posSqIntegral, tunedRhoSqIntegral_eq]
      norm_num

theorem fastProfile_globalIntegral_eq_compact :
    (∫ t, fastProfile t ^ 2) =
      ∫ t in Set.Icc (-(5 / 8)) (5 / 8), fastProfile t ^ 2 := by
  let f : ℝ → ℝ := fun t => fastProfile t ^ 2
  have hae : f =ᵐ[volume] (Set.Icc (-(5 / 8)) (5 / 8)).indicator f := by
    filter_upwards [] with t
    by_cases ht : t ∈ Set.Icc (-(5 / 8)) (5 / 8)
    · simp [ht]
    · have ht' : t ≤ -(5 / 8) ∨ 5 / 8 ≤ t := by
        simp only [mem_Icc, not_and_or, not_le] at ht
        rcases ht with hleft | hright
        · exact Or.inl hleft.le
        · exact Or.inr hright.le
      rw [Set.indicator_of_notMem ht]
      rcases ht' with hleft | hright
      · simp [f, fastProfile_zero_of_le hleft]
      · simp [f, fastProfile_zero_of_ge hright]
  calc
    (∫ t, f t) = ∫ t, (Set.Icc (-(5 / 8)) (5 / 8)).indicator f t :=
      MeasureTheory.integral_congr_ae hae
    _ = ∫ t in Set.Icc (-(5 / 8)) (5 / 8), f t :=
      MeasureTheory.integral_indicator measurableSet_Icc

theorem fastProfile_integral_sq : (∫ t, fastProfile t ^ 2) = 9 / 10 := by
  calc
    (∫ t, fastProfile t ^ 2) =
        ∫ t in Set.Icc (-(5 / 8)) (5 / 8), fastProfile t ^ 2 :=
      fastProfile_globalIntegral_eq_compact
    _ = ∫ t in (-(5 / 8))..(5 / 8), fastProfile t ^ 2 := by
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num)]
    _ = 9 / 10 := fastProfile_intervalIntegral_sq

end AVRegularity.FastProfile
end
