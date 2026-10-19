-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Applications.TorusEnergy.With
public import AVRegularity.Wellposed.Existence
import AVenhance.Infra.Parabolic.WeakUniqueness.DivergenceFreeEnergy
public import AVRegularity.Applications.Parabolic.SliceGrad
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section
noncomputable section

section
open MeasureTheory Homogenization AVenhance AVRegularity.Wellposed
namespace AVRegularity.Applications

/-! # The energy identity on a window

Reuses upstream `weak_solution_divFree_energy_identity` (unit window) through the affine
bridge of `Wellposed.Existence` (`isWeakSolutionOn_to_isWeakSolution`), redone here with the
gradient field explicit (`isWeakSolutionOnWith_to_isWeakSolutionGrad`; the bridge of
`Wellposed.Existence` hides the gradient behind an existential). -/

private theorem memLp_unitWindow_of_window {t₁ T : ℝ} (hT : 0 < T)
    {g : ℝ × Vec 2 → ℝ} (hg : MemLp g 2
      (volume.restrict (Set.Ioo t₁ (t₁ + T) ×ˢ unitCube))) :
    MemLp (g ∘ windowForward t₁ T) 2
      (volume.restrict (Set.Ioo (0 : ℝ) 1 ×ˢ unitCube)) := by
  have hc : ENNReal.ofReal T⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
  exact (hg.smul_measure hc).comp_measurePreserving (windowForwardOpenCubeMeasurePreserving hT)

private theorem timeBackward_timeForward' {t₁ T s : ℝ} (hT : 0 < T) :
    timeBackward t₁ T (timeForward t₁ T s) = s := by
  dsimp [timeBackward, timeForward]
  field_simp [ne_of_gt hT]
  ring

theorem isWeakSolutionOnWith_to_isWeakSolutionGrad {b : ℝ → Vec 2 → Vec 2}
    {κ t₁ T : ℝ} (hT : 0 < T) {f : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}
    {Dθ : ℝ → Vec 2 → Vec 2}
    (hθ : IsWeakSolutionOnWith b κ t₁ (t₁ + T) f θ Dθ) :
    IsWeakSolutionGrad (rescaledDrift b t₁ T) (T * κ) f (stateToUnit t₁ T θ)
      (gradientToUnit t₁ T Dθ) := by
  rcases hθ with ⟨hslice, hbound, hstateLP, hgradLP, hH1, hdrift, hcont, hweak⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    exact hslice _ (timeForward_mem_Icc (t₁ := t₁) (T := T) (s := s) hT hs)
  · obtain ⟨C, hC⟩ := hbound
    exact ⟨C, fun s hs => hC _
      (timeForward_mem_Icc (t₁ := t₁) (T := T) (s := s) hT hs)⟩
  · change MemLp (fun p : ℝ × Vec 2 => θ (timeForward t₁ T p.1) p.2) 2
      (volume.restrict (Set.Ioo (0 : ℝ) 1 ×ˢ unitCube))
    exact memLp_unitWindow_of_window hT hstateLP
  · intro i
    change MemLp (fun p : ℝ × Vec 2 => Dθ (timeForward t₁ T p.1) p.2 i) 2
      (volume.restrict (Set.Ioo (0 : ℝ) 1 ×ˢ unitCube))
    exact memLp_unitWindow_of_window hT (hgradLP i)
  · have hscaled : ∀ᵐ t ∂(ENNReal.ofReal T⁻¹ •
        volume.restrict (Set.Ioo t₁ (t₁ + T))),
        IsPeriodicH1With (θ t) (Dθ t) := Measure.ae_smul_measure hH1 (ENNReal.ofReal T⁻¹)
    have hAE := (timeForwardOpenMeasurePreserving (t₁ := t₁) (T := T) hT).quasiMeasurePreserving.ae hscaled
    filter_upwards [hAE] with s hs
    exact hs
  · have hc : ENNReal.ofReal T⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
    have hscaled := hdrift.smul_measure hc
    have hcomp : Integrable
        ((fun p : ℝ × Vec 2 => vecDot (b p.1 p.2) (Dθ p.1 p.2)) ∘ windowForward t₁ T)
        (volume.restrict (Set.Ioo (0 : ℝ) 1 ×ˢ unitCube)) := by
      exact ((windowForwardOpenCubeMeasurePreserving (t₁ := t₁) (T := T) hT).integrable_comp
        hscaled.aestronglyMeasurable).mpr hscaled
    have hmul := hcomp.const_mul T
    have hfun :
        (fun p : ℝ × Vec 2 =>
          vecDot (rescaledDrift b t₁ T p.1 p.2) (gradientToUnit t₁ T Dθ p.1 p.2)) =
        (fun p => T * (fun q : ℝ × Vec 2 => vecDot (b q.1 q.2) (Dθ q.1 q.2))
          (windowForward t₁ T p)) := by
      funext p
      rcases p with ⟨s, x⟩
      change vecDot (T • b (timeForward t₁ T s) x) (Dθ (timeForward t₁ T s) x) =
        T * vecDot (b (timeForward t₁ T s) x) (Dθ (timeForward t₁ T s) x)
      exact Homogenization.vecDot_smul_left T _ _
    rw [hfun]
    exact hmul
  · intro ψ hψ hper
    have hcont' := hcont ψ hψ hper
    have hAcont : ContinuousOn (timeForward t₁ T) (Set.Icc (0 : ℝ) 1) := by
      change ContinuousOn (fun s => t₁ + T * s) (Set.Icc (0 : ℝ) 1)
      exact (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
    have hmaps : Set.MapsTo (timeForward t₁ T) (Set.Icc (0 : ℝ) 1)
        (Set.Icc t₁ (t₁ + T)) := fun s hs =>
          timeForward_mem_Icc (t₁ := t₁) (T := T) (s := s) hT hs
    change ContinuousOn
      ((fun t => ∫ x in unitCube, θ t x * ψ x) ∘ timeForward t₁ T)
      (Set.Icc (0 : ℝ) 1)
    simpa only [Function.comp_apply] using hcont'.comp hAcont hmaps
  · intro ψ hψ
    have htest : IsWindowTestFunction (t₁ + T) (testToWindow t₁ T ψ) :=
      testToWindow_isWindowTestFunction hT hψ
    have hwindow := hweak (testToWindow t₁ T ψ) htest
    let g : ℝ × Vec 2 → ℝ := fun p =>
      (-(θ p.1 p.2) * deriv (fun u => testToWindow t₁ T ψ u p.2) p.1
        + vecDot (b p.1 p.2) (Dθ p.1 p.2) * testToWindow t₁ T ψ p.1 p.2
        + κ * vecDot (Dθ p.1 p.2)
            (spaceGrad (testToWindow t₁ T ψ p.1) p.2))
    have hpoint : ∀ p : ℝ × Vec 2,
        (-(stateToUnit t₁ T θ p.1 p.2) * deriv (fun u => ψ u p.2) p.1
          + vecDot (rescaledDrift b t₁ T p.1 p.2)
              (gradientToUnit t₁ T Dθ p.1 p.2) * ψ p.1 p.2
          + (T * κ) * vecDot (gradientToUnit t₁ T Dθ p.1 p.2)
              (spaceGrad (ψ p.1) p.2)) = T * g (windowForward t₁ T p) := by
      intro p
      rcases p with ⟨s, x⟩
      have htime := timeBackward_timeForward' hT (t₁ := t₁) (T := T) (s := s)
      have hderiv := deriv_testToWindow (t₁ := t₁) (T := T) (t := timeForward t₁ T s)
        ψ hψ.1 x
      rw [htime] at hderiv
      have hsection : testToWindow t₁ T ψ (timeForward t₁ T s) = ψ s := by
        funext y
        simp [testToWindow, htime]
      have hsection' : testToWindow t₁ T ψ (t₁ + T * s) = ψ s := by
        simpa [timeForward] using hsection
      have hderiv' : deriv (fun u => testToWindow t₁ T ψ u x) (t₁ + T * s) =
          T⁻¹ * deriv (fun u => ψ u x) s := by
        simpa [timeForward] using hderiv
      simp only [stateToUnit, gradientToUnit, rescaledDrift, windowForward, timeForward]
      simp only [g]
      rw [hsection']
      rw [hderiv']
      simp_rw [Homogenization.vecDot_smul_left]
      field_simp [ne_of_gt hT]
    calc
      ∫ p in Set.Ioo (0 : ℝ) 1 ×ˢ unitCube,
          (-(stateToUnit t₁ T θ p.1 p.2) * deriv (fun u => ψ u p.2) p.1
            + vecDot (rescaledDrift b t₁ T p.1 p.2)
                (gradientToUnit t₁ T Dθ p.1 p.2) * ψ p.1 p.2
            + (T * κ) * vecDot (gradientToUnit t₁ T Dθ p.1 p.2)
                (spaceGrad (ψ p.1) p.2)) =
          T * ∫ p in Set.Ioo (0 : ℝ) 1 ×ˢ unitCube, g (windowForward t₁ T p) := by
            simp_rw [hpoint]
            rw [integral_const_mul]
      _ = T * (T⁻¹ * ∫ p in Set.Ioo t₁ (t₁ + T) ×ˢ unitCube, g p) := by
            rw [integral_windowForward_scale hT g]
      _ = ∫ p in Set.Ioo t₁ (t₁ + T) ×ˢ unitCube, g p := by
            field_simp [ne_of_gt hT]
      _ = ∫ p in Set.Ioo t₁ (t₁ + T) ×ˢ unitCube,
          (-(θ p.1 p.2) * deriv (fun u => testToWindow t₁ T ψ u p.2) p.1
            + vecDot (b p.1 p.2) (Dθ p.1 p.2) * testToWindow t₁ T ψ p.1 p.2
            + κ * vecDot (Dθ p.1 p.2)
                (spaceGrad (testToWindow t₁ T ψ p.1) p.2)) := by rfl
      _ = ∫ x in unitCube, f x * testToWindow t₁ T ψ t₁ x := hwindow
      _ = ∫ x in unitCube, f x * ψ 0 x := by
            congr 1
            funext x
            simp [testToWindow, timeBackward]

theorem isWeakSolutionOnWith_restrict {b : ℝ → Vec 2 → Vec 2} {κ t₁ t₂ t₃ : ℝ} {f : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2} (h32 : t₃ ≤ t₂)
    (h : IsWeakSolutionOnWith b κ t₁ t₂ f θ Dθ) :
    IsWeakSolutionOnWith b κ t₁ t₃ f θ Dθ := by
  obtain ⟨hslice, ⟨C, hC⟩, hL2, hDL2, hH1, hint, hcont, hweak⟩ := h
  have hIcc : Set.Icc t₁ t₃ ⊆ Set.Icc t₁ t₂ := Set.Icc_subset_Icc le_rfl h32
  have hIoo : Set.Ioo t₁ t₃ ×ˢ unitCube ⊆ Set.Ioo t₁ t₂ ×ˢ unitCube :=
    Set.prod_mono (Set.Ioo_subset_Ioo le_rfl h32) le_rfl
  have hmono : volume.restrict (Set.Ioo t₁ t₃ ×ˢ unitCube) ≤
      volume.restrict (Set.Ioo t₁ t₂ ×ˢ unitCube) := Measure.restrict_mono hIoo le_rfl
  refine ⟨fun t ht => hslice t (hIcc ht), ⟨C, fun t ht => hC t (hIcc ht)⟩,
    hL2.mono_measure hmono, fun i => (hDL2 i).mono_measure hmono, ?_, hint.mono_measure hmono,
    fun ψ hψ hψp => (hcont ψ hψ hψp).mono hIcc, ?_⟩
  · exact ae_restrict_of_ae_restrict_of_subset (Set.Ioo_subset_Ioo le_rfl h32) hH1
  · intro φ hφ
    obtain ⟨hsm, hper, hvan⟩ := hφ
    have hφ2 : IsWindowTestFunction t₂ φ := ⟨hsm, hper, fun t ht x => hvan t (h32.trans ht) x⟩
    have hw := hweak φ hφ2
    have hzero : ∀ p ∈ Set.Ioo t₁ t₂ ×ˢ unitCube \ Set.Ioo t₁ t₃ ×ˢ unitCube,
        (-(θ p.1 p.2) * deriv (fun s => φ s p.2) p.1
          + vecDot (b p.1 p.2) (Dθ p.1 p.2) * φ p.1 p.2
          + κ * vecDot (Dθ p.1 p.2) (spaceGrad (φ p.1) p.2)) = 0 := by
      rintro ⟨t, x⟩ ⟨⟨⟨ht1, ht2⟩, hx⟩, hnot⟩
      have ht3 : t₃ ≤ t := by
        by_contra hlt
        push Not at hlt
        exact hnot ⟨⟨ht1, hlt⟩, hx⟩
      -- `φ` vanishes on the closed half-space `t ≥ t₃`, hence near any `t > t₃`, and its
      -- slice is identically zero there; at `t = t₃` the time derivative is one-sided zero.
      have hφt : φ t = fun _ => 0 := funext fun y => hvan t ht3 y
      have hgrad : spaceGrad (φ t) x = 0 := by
        rw [hφt]
        funext i
        simp [spaceGrad]
      have hderiv : deriv (fun s => φ s x) t = 0 := by
        have hd : HasDerivAt (fun s => φ s x) (deriv (fun s => φ s x) t) t := by
          have hdiff : Differentiable ℝ (fun s => φ s x) :=
            (hsm.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp)
          exact (hdiff t).hasDerivAt
        have hright : HasDerivWithinAt (fun s => φ s x) 0 (Set.Ici t) t := by
          apply (hasDerivWithinAt_const t (Set.Ici t) (0 : ℝ)).congr
          · intro s hs; exact hvan s (ht3.trans hs) x
          · exact hvan t ht3 x
        exact (uniqueDiffWithinAt_Ici t).eq_deriv _ hd.hasDerivWithinAt hright
      simp [hgrad, hderiv, hvan t ht3 x, vecDot]
    have hmeas : MeasurableSet (Set.Ioo t₁ t₂ ×ˢ unitCube) :=
      measurableSet_Ioo.prod (by
        unfold unitCube; exact MeasurableSet.univ_pi fun _ => measurableSet_Ioo)
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeas hIoo hzero] at hw
    exact hw

/-- The drift class for the energy tools on the window `[t₁, t₂]`: jointly measurable, bounded,
`ℤ²`-periodic in space, divergence free on every time slice (distributionally). -/
def IsWindowDrift (b : ℝ → Vec 2 → Vec 2) (t₁ t₂ : ℝ) : Prop :=
  Measurable (fun p : ℝ × Vec 2 => b p.1 p.2) ∧
  (∃ C : ℝ, ∀ t ∈ Set.Icc t₁ t₂, ∀ x, ‖b t x‖ ≤ C) ∧
  (∀ t ∈ Set.Icc t₁ t₂, IsZ2Periodic (b t)) ∧
  ∀ t ∈ Set.Icc t₁ t₂, ∀ φ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    ∫ x, vecDot (b t x) (spaceGrad φ x) = 0

/-- The unit-window energy identity, transported to `[t₁, t₁ + T]` and read at `t₁ + T s`. -/
theorem energy_identity_unit {b : ℝ → Vec 2 → Vec 2} {κ t₁ T : ℝ} (hT : 0 < T)
    (hb : IsWindowDrift b t₁ (t₁ + T)) {f : Vec 2 → ℝ} (hf : MemL2On unitCube f)
    {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2}
    (hθ : IsWeakSolutionOnWith b κ t₁ (t₁ + T) f θ Dθ) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    l2NormSq (θ (t₁ + T * s)) + 2 * (T * κ) * ∫ p in Set.Ioo (0 : ℝ) s ×ˢ unitCube,
      vecNormSq (Dθ (t₁ + T * p.1) p.2) = l2NormSq f := by
  obtain ⟨hbm, ⟨C, hC⟩, hbp, hdiv⟩ := hb
  have hbridge := isWeakSolutionOnWith_to_isWeakSolutionGrad hT hθ
  have hrm : Measurable (fun p : ℝ × Vec 2 => rescaledDrift b t₁ T p.1 p.2) := by
    have h1 : Measurable (fun p : ℝ × Vec 2 => b (timeForward t₁ T p.1) p.2) :=
      hbm.comp (measurable_windowForward t₁ T)
    exact h1.const_smul T
  have hrb : ∃ C' : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖rescaledDrift b t₁ T s x‖ ≤ C' := by
    refine ⟨T * C, fun s hs x => ?_⟩
    have := hC _ (timeForward_mem_Icc (t₁ := t₁) hT hs) x
    change ‖T • b (timeForward t₁ T s) x‖ ≤ T * C
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hT]
    exact mul_le_mul_of_nonneg_left this hT.le
  have hrp : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (rescaledDrift b t₁ T s) := by
    intro s hs k x
    change T • b (timeForward t₁ T s) (x + latticeShift k) = T • b (timeForward t₁ T s) x
    rw [hbp _ (timeForward_mem_Icc (t₁ := t₁) hT hs) k x]
  have hrd : IsDivFree (rescaledDrift b t₁ T) := by
    intro s hs φ hφ hφc
    have h0 := hdiv _ (timeForward_mem_Icc (t₁ := t₁) hT hs) φ hφ hφc
    change ∫ x, vecDot (T • b (timeForward t₁ T s) x) (spaceGrad φ x) = 0
    simp_rw [Homogenization.vecDot_smul_left]
    rw [integral_const_mul, h0, mul_zero]
  exact Infra.Parabolic.WeakUniqueness.weak_solution_divFree_energy_identity hbridge hf
    hrm.aestronglyMeasurable hrb hrp hrd s hs

/-- **Energy identity on a window** (display (8.2) of the paper): for every `t` in the
window, `‖θ(t)‖² + 2κ ∬_{(t₁,t)×𝕋²} |Dθ|² = ‖f‖²`. -/
theorem energy_identity {b : ℝ → Vec 2 → Vec 2} {κ t₁ t₂ : ℝ} (h12 : t₁ < t₂)
    (hb : IsWindowDrift b t₁ t₂) {f : Vec 2 → ℝ} (hf : MemL2On unitCube f)
    {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2}
    (hθ : IsWeakSolutionOnWith b κ t₁ t₂ f θ Dθ) :
    ∀ t ∈ Set.Icc t₁ t₂, l2NormSq (θ t) + 2 * κ * ∫ p in Set.Ioo t₁ t ×ˢ unitCube,
      vecNormSq (Dθ p.1 p.2) = l2NormSq f := by
  intro t ht
  obtain ⟨T, hT, rfl⟩ : ∃ T, 0 < T ∧ t₂ = t₁ + T := ⟨t₂ - t₁, by linarith, by ring⟩
  rcases ht.1.eq_or_lt with rfl | hlt
  · have h0 := energy_identity_unit hT hb hf hθ (s := 0) ⟨le_rfl, zero_le_one⟩
    simpa using h0
  · obtain ⟨T', hT', rfl⟩ : ∃ T', 0 < T' ∧ t = t₁ + T' := ⟨t - t₁, by linarith, by ring⟩
    have hsub : t₁ + T' ≤ t₁ + T := ht.2
    have hθ' := isWeakSolutionOnWith_restrict hsub hθ
    have hb' : IsWindowDrift b t₁ (t₁ + T') := by
      obtain ⟨hbm, ⟨C, hC⟩, hbp, hdiv⟩ := hb
      have hIcc : Set.Icc t₁ (t₁ + T') ⊆ Set.Icc t₁ (t₁ + T) := Set.Icc_subset_Icc le_rfl hsub
      exact ⟨hbm, ⟨C, fun t ht => hC t (hIcc ht)⟩, fun t ht => hbp t (hIcc ht),
        fun t ht => hdiv t (hIcc ht)⟩
    have h1 := energy_identity_unit hT' hb' hf hθ' (s := 1) ⟨zero_le_one, le_rfl⟩
    have hint := integral_windowForward_scale (t₁ := t₁) hT'
      (fun p : ℝ × Vec 2 => vecNormSq (Dθ p.1 p.2))
    have hI : (∫ p in Set.Ioo (0 : ℝ) 1 ×ˢ unitCube, vecNormSq (Dθ (t₁ + T' * p.1) p.2)) =
        T'⁻¹ * ∫ p in Set.Ioo t₁ (t₁ + T') ×ˢ unitCube, vecNormSq (Dθ p.1 p.2) := by
      rw [← hint]; rfl
    rw [hI] at h1
    have hTne : T' ≠ 0 := ne_of_gt hT'
    have e : 2 * (T' * κ) * (T'⁻¹ * ∫ p in Set.Ioo t₁ (t₁ + T') ×ˢ unitCube,
        vecNormSq (Dθ p.1 p.2)) = 2 * κ * ∫ p in Set.Ioo t₁ (t₁ + T') ×ˢ unitCube,
        vecNormSq (Dθ p.1 p.2) := by field_simp
    rw [e] at h1
    simpa using h1

/-- **`L²` energy bound and dissipation bound**: for `κ ≥ 0`, `‖θ(t)‖² ≤ ‖f‖²` and
`2κ ∬ |Dθ|² ≤ ‖f‖²`. -/
theorem l2NormSq_le_of_weakSolutionOnWith {b : ℝ → Vec 2 → Vec 2} {κ t₁ t₂ : ℝ}
    (hκ : 0 ≤ κ) (h12 : t₁ < t₂)
    (hb : IsWindowDrift b t₁ t₂) {f : Vec 2 → ℝ} (hf : MemL2On unitCube f)
    {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2}
    (hθ : IsWeakSolutionOnWith b κ t₁ t₂ f θ Dθ) :
    (∀ t ∈ Set.Icc t₁ t₂, l2NormSq (θ t) ≤ l2NormSq f) ∧
    (∀ t ∈ Set.Icc t₁ t₂, 2 * κ * ∫ p in Set.Ioo t₁ t ×ˢ unitCube,
      vecNormSq (Dθ p.1 p.2) ≤ l2NormSq f) := by
  have hid := energy_identity h12 hb hf hθ
  have hnn : ∀ t, 0 ≤ ∫ p in Set.Ioo t₁ t ×ˢ unitCube, vecNormSq (Dθ p.1 p.2) :=
    fun t => integral_nonneg fun p => vecNormSq_nonneg _
  have hl : ∀ t, 0 ≤ l2NormSq (θ t) := fun t => integral_nonneg fun x => sq_nonneg _
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · have := hid t ht
    have := mul_nonneg (mul_nonneg zero_le_two hκ) (hnn t)
    linarith [hid t ht]
  · have := hid t ht
    linarith [hl t]

section Holder

open Filter Topology

private theorem continuous_vecNormSq : Continuous (fun x : Vec 2 => vecNormSq x) := by
  unfold vecNormSq vecDot
  fun_prop

/-- The Hölder velocity class is a window drift for every window, provided `α > 0`. -/
theorem isWindowDrift_of_isHolderDivFreeVelocity {α : ℝ} (hα : 0 < α)
    {b : ℝ → Vec 2 → Vec 2} (hb : IsHolderDivFreeVelocity α b) (t₁ t₂ : ℝ) :
    IsWindowDrift b t₁ t₂ := by
  obtain ⟨hper, -, ⟨B, hB⟩, ⟨C, hC⟩, hdiv⟩ := hb
  refine ⟨?_, ⟨B, fun t _ x => hB t x⟩, fun t _ => hper t, fun t _ => hdiv t⟩
  have hcont : Continuous (fun p : ℝ × Vec 2 => b p.1 p.2) := by
    rw [continuous_iff_continuousAt]
    rintro ⟨u, y⟩
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have hs : Tendsto (fun p : ℝ × Vec 2 => |p.1 - u| + Real.sqrt (vecNormSq (p.2 - y)))
        (𝓝 (u, y)) (𝓝 0) := by
      have hc : Continuous (fun p : ℝ × Vec 2 =>
          |p.1 - u| + Real.sqrt (vecNormSq (p.2 - y))) := by
        have := continuous_vecNormSq
        fun_prop
      have := hc.tendsto (u, y)
      have h0 : vecNormSq (0 : Vec 2) = 0 := by simp [vecNormSq, vecDot]
      simpa [h0] using this
    have hpow : Tendsto (fun s : ℝ => C * s ^ α) (𝓝[≥] 0) (𝓝 0) := by
      have h1 : Tendsto (fun s : ℝ => s ^ α) (𝓝 0) (𝓝 (0 ^ α)) :=
        (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto
      rw [Real.zero_rpow hα.ne'] at h1
      simpa using (h1.const_mul C).mono_left nhdsWithin_le_nhds
    have hs' : Tendsto (fun p : ℝ × Vec 2 => |p.1 - u| + Real.sqrt (vecNormSq (p.2 - y)))
        (𝓝 (u, y)) (𝓝[≥] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨hs, Eventually.of_forall fun p => add_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)⟩
    refine squeeze_zero (fun p => norm_nonneg _) (fun p => ?_) (hpow.comp hs')
    exact hC p.1 u p.2 y
  exact hcont.measurable

end Holder

/-- **`L²` energy bound and dissipation bound** for the Hölder velocity class (from the energy
identity (8.2) of the paper): `‖θ(t)‖² ≤ ‖f‖²` on the window and the dissipation bound
`2κ ∬_{(t₁,t₂)×𝕋²} |Dθ|² ≤ ‖f‖²` for the gradient field of the solution. -/
theorem l2NormSq_le_of_isHolderDivFreeVelocity {α : ℝ} (hα : 0 < α) {b : ℝ → Vec 2 → Vec 2}
    (hb : IsHolderDivFreeVelocity α b) {κ : ℝ} (hκ : 0 < κ) {t₁ t₂ : ℝ} (h12 : t₁ < t₂)
    {f : Vec 2 → ℝ} (hf : MemL2On unitCube f) {θ : ℝ → Vec 2 → ℝ}
    (hθ : IsWeakSolutionOn b κ t₁ t₂ f θ) :
    (∀ t ∈ Set.Icc t₁ t₂, l2NormSq (θ t) ≤ l2NormSq f) ∧
    ∃ Dθ : ℝ → Vec 2 → Vec 2, IsWeakSolutionOnWith b κ t₁ t₂ f θ Dθ ∧
      2 * κ * ∫ p in Set.Ioo t₁ t₂ ×ˢ unitCube, vecNormSq (Dθ p.1 p.2) ≤ l2NormSq f := by
  have hbw := isWindowDrift_of_isHolderDivFreeVelocity hα hb t₁ t₂
  obtain ⟨Dθ, hD⟩ := hθ
  have h := l2NormSq_le_of_weakSolutionOnWith hκ.le h12 hbw hf hD
  exact ⟨h.1, Dθ, hD, h.2 t₂ ⟨h12.le, le_rfl⟩⟩

end AVRegularity.Applications
end

section
open MeasureTheory Homogenization AVenhance Filter Topology
namespace AVRegularity.Applications

/-! # Compactly supported continuous tests and their periodizations

Wrappers around `integral_unfold` for continuous compactly supported space-time tests `ρ`, and the
dictionary between slice derivatives (`deriv`, `spaceGrad`) and the Fréchet derivative of the
space-time function. -/

/-- The slice function `fun t x => ρ (t, x)` of a space-time function. -/
abbrev slc (ρ : ℝ × Vec 2 → ℝ) : ℝ → Vec 2 → ℝ := fun t x => ρ (t, x)

theorem exists_supBdd_of_hasCompactSupport {ρ : ℝ × Vec 2 → ℝ} (hρ : HasCompactSupport ρ) :
    ∃ R : ℝ, SupBdd R (slc ρ) := by
  obtain ⟨R, hR⟩ := (hρ.isCompact.image continuous_snd).isBounded.exists_norm_le
  exact ⟨R, fun t x hne => hR x ⟨(t, x), subset_tsupport _ hne, rfl⟩⟩

theorem deriv_slc_eq {ρ : ℝ × Vec 2 → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (t : ℝ) (y : Vec 2) :
    deriv (fun r => slc ρ r y) t = fderiv ℝ ρ (t, y) (1, 0) := by
  have hd : DifferentiableAt ℝ ρ (t, y) := (hρ.differentiable (by simp)).differentiableAt
  have hin : HasDerivAt (fun r : ℝ => (r, y)) ((1 : ℝ), (0 : Vec 2)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t y)
  exact (hd.hasFDerivAt.comp_hasDerivAt t hin).deriv

theorem spaceGrad_slc_eq {ρ : ℝ × Vec 2 → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (t : ℝ) (y : Vec 2)
    (i : Fin 2) : spaceGrad (slc ρ t) y i = fderiv ℝ ρ (t, y) (0, basisVec i) :=
  fderiv_slice hρ t y (basisVec i)

theorem stTimeDeriv_eq {ρ : ℝ × Vec 2 → ℝ} (p : ℝ × Vec 2) :
    stTimeDeriv ρ p = fderiv ℝ ρ p (1, 0) := rfl

theorem stSpaceGrad_eq {ρ : ℝ × Vec 2 → ℝ} (p : ℝ × Vec 2) (i : Fin 2) :
    stSpaceGrad ρ p i = fderiv ℝ ρ p (0, basisVec i) := rfl

/-- `perST` of a smooth compactly supported test, as a function on space-time. -/
theorem perST_slc_contDiff {ρ : ℝ × Vec 2 → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hc : HasCompactSupport ρ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => perST (slc ρ) p.1 p.2) := by
  obtain ⟨R, hR⟩ := exists_supBdd_of_hasCompactSupport hc
  exact perST_contDiff hR hρ

theorem exists_perST_bound {R : ℝ} {ρ : ℝ → Vec 2 → ℝ} (hρ : SupBdd R ρ)
    (hb : ∃ B : ℝ, ∀ t x, |ρ t x| ≤ B) :
    ∃ C : ℝ, ∀ t x, ‖x‖ ≤ 1 → |perST ρ t x| ≤ C := by
  obtain ⟨B, hB⟩ := hb
  obtain ⟨M, hM⟩ := exists_nat_ge_add R 1
  refine ⟨(latBox M).card * B, fun t x hx => ?_⟩
  rw [perST_eq_sum hM hρ t hx]
  calc |∑ n ∈ latBox M, ρ t (x + latticeShift n)|
      ≤ ∑ n ∈ latBox M, |ρ t (x + latticeShift n)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ latBox M, B := Finset.sum_le_sum fun n _ => hB _ _
    _ = (latBox M).card * B := by simp

theorem norm_le_one_of_mem_unitCube {x : Vec 2} (hx : x ∈ unitCube) : ‖x‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  have := hx i (Set.mem_univ i)
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [this.1, this.2]

theorem measurableSet_unitCube' : MeasurableSet unitCube :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioo

/-- Unfolding against a continuous compactly supported test. -/
theorem integral_unfold_cs {S : Set ℝ} (hS : MeasurableSet S) {ρ : ℝ × Vec 2 → ℝ}
    (hρs : ContDiff ℝ (⊤ : ℕ∞) ρ) (hc : HasCompactSupport ρ) {G : ℝ → Vec 2 → ℝ}
    (hper : ∀ᵐ t ∂(volume.restrict S), IsZ2Periodic (G t))
    (hG : Integrable (fun p : ℝ × Vec 2 => G p.1 p.2) (volume.restrict (S ×ˢ unitCube))) :
    Integrable (fun p : ℝ × Vec 2 => G p.1 p.2 * ρ p) (volume.restrict (S ×ˢ Set.univ)) ∧
    Integrable (fun p : ℝ × Vec 2 => G p.1 p.2 * perST (slc ρ) p.1 p.2)
      (volume.restrict (S ×ˢ unitCube)) ∧
    ∫ p in S ×ˢ Set.univ, G p.1 p.2 * ρ p =
      ∫ p in S ×ˢ unitCube, G p.1 p.2 * perST (slc ρ) p.1 p.2 := by
  have hρ : Continuous ρ := hρs.continuous
  obtain ⟨R, hR⟩ := exists_supBdd_of_hasCompactSupport hc
  obtain ⟨B, hB⟩ := hρ.bounded_above_of_compact_support hc
  have hρb : ∃ B : ℝ, ∀ t x, |slc ρ t x| ≤ B := ⟨B, fun t x => by simpa using hB (t, x)⟩
  have hρm : Measurable (fun p : ℝ × Vec 2 => slc ρ p.1 p.2) := hρ.measurable
  obtain ⟨hint, heq⟩ := integral_unfold hS hR hρm hρb hper hG
  refine ⟨hint, ?_, heq⟩
  obtain ⟨C, hC⟩ := exists_perST_bound hR hρb
  have hcont : Continuous (fun p : ℝ × Vec 2 => perST (slc ρ) p.1 p.2) :=
    (perST_slc_contDiff hρs hc).continuous
  exact hG.mul_bdd hcont.aestronglyMeasurable (c := C)
    (by
      filter_upwards [ae_restrict_mem (hS.prod measurableSet_unitCube')] with p hp
      simpa using hC p.1 p.2 (norm_le_one_of_mem_unitCube hp.2))

/-! # Unfolding against time-independent tests, and the purely spatial unfolding -/

theorem exists_supBdd_x {ρ : Vec 2 → ℝ} (hρ : HasCompactSupport ρ) :
    ∃ R : ℝ, SupBdd R (fun _ x => ρ x) := by
  obtain ⟨R, hR⟩ := hρ.isCompact.isBounded.exists_norm_le
  exact ⟨R, fun t x hne => hR x (subset_tsupport _ hne)⟩

theorem perX_contDiff {ρ : Vec 2 → ℝ} (hρs : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ) :
    ContDiff ℝ (⊤ : ℕ∞) (perX ρ) := by
  obtain ⟨R, hR⟩ := exists_supBdd_x hρc
  have := (perST_contDiff hR (hρs.comp contDiff_snd)).comp
    (contDiff_const.prodMk contDiff_id : ContDiff ℝ (⊤ : ℕ∞) fun x : Vec 2 => ((0 : ℝ), x))
  exact this

/-- Unfolding against a time-independent smooth compactly supported test. -/
theorem integral_unfold_x {S : Set ℝ} (hS : MeasurableSet S) {ρ : Vec 2 → ℝ}
    (hρs : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ) {G : ℝ → Vec 2 → ℝ}
    (hper : ∀ᵐ t ∂(volume.restrict S), IsZ2Periodic (G t))
    (hG : Integrable (fun p : ℝ × Vec 2 => G p.1 p.2) (volume.restrict (S ×ˢ unitCube))) :
    Integrable (fun p : ℝ × Vec 2 => G p.1 p.2 * ρ p.2) (volume.restrict (S ×ˢ Set.univ)) ∧
    Integrable (fun p : ℝ × Vec 2 => G p.1 p.2 * perX ρ p.2) (volume.restrict (S ×ˢ unitCube)) ∧
    ∫ p in S ×ˢ Set.univ, G p.1 p.2 * ρ p.2 =
      ∫ p in S ×ˢ unitCube, G p.1 p.2 * perX ρ p.2 := by
  obtain ⟨R, hR⟩ := exists_supBdd_x hρc
  obtain ⟨B, hB⟩ := hρs.continuous.bounded_above_of_compact_support hρc
  have hρb : ∃ B : ℝ, ∀ t x, |(fun (_ : ℝ) y => ρ y) t x| ≤ B :=
    ⟨B, fun t x => by simpa using hB x⟩
  have hρm : Measurable (fun p : ℝ × Vec 2 => (fun (_ : ℝ) y => ρ y) p.1 p.2) :=
    hρs.continuous.measurable.comp measurable_snd
  obtain ⟨hint, heq⟩ := integral_unfold hS hR hρm hρb hper hG
  refine ⟨hint, ?_, heq⟩
  obtain ⟨C, hC⟩ := exists_perST_bound hR hρb
  have hcont : Continuous (fun p : ℝ × Vec 2 => perX ρ p.2) :=
    (perX_contDiff hρs hρc).continuous.comp continuous_snd
  exact hG.mul_bdd hcont.aestronglyMeasurable (c := C)
    (by
      filter_upwards [ae_restrict_mem (hS.prod measurableSet_unitCube')] with p hp
      have := hC p.1 p.2 (norm_le_one_of_mem_unitCube hp.2)
      simpa [perX, perST] using this)

theorem integral_prod_snd_eq (h : Vec 2 → ℝ) (A : Set (Vec 2)) :
    ∫ p in Set.Ioo (0 : ℝ) 1 ×ˢ A, h p.2 = ∫ x in A, h x := by
  rw [volume_restrict_prod_eq]
  have := integral_prod_mul (μ := volume.restrict (Set.Ioo (0 : ℝ) 1)) (ν := volume.restrict A)
    (fun _ => (1 : ℝ)) h
  simpa using this

/-- The purely spatial unfolding. -/
theorem integral_unfold_space {G ρ : Vec 2 → ℝ} (hρs : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hρc : HasCompactSupport ρ) (hper : IsZ2Periodic G) (hG : Integrable G (volume.restrict unitCube)) :
    ∫ x, G x * ρ x = ∫ x in unitCube, G x * perX ρ x := by
  have hG' : Integrable (fun p : ℝ × Vec 2 => (fun (_ : ℝ) x => G x) p.1 p.2)
      (volume.restrict (Set.Ioo (0 : ℝ) 1 ×ˢ unitCube)) := by
    rw [volume_restrict_prod_eq]
    have := hG.comp_snd (volume.restrict (Set.Ioo (0 : ℝ) 1))
    simpa using this
  obtain ⟨-, -, h⟩ := integral_unfold_x measurableSet_Ioo hρs hρc
    (G := fun _ x => G x) (Eventually.of_forall fun t => hper) hG'
  have e1 := integral_prod_snd_eq (fun x => G x * ρ x) Set.univ
  have e2 := integral_prod_snd_eq (fun x => G x * perX ρ x) unitCube
  simp only [Measure.restrict_univ] at e1
  rw [← e1, ← e2]
  exact h

/-! # A weak solution on a window is a local weak solution on `(t₁,t₂) × ℝ²`

The periodic lift: the periodic extension of `θ` is a local weak solution in `(t₁,t₂) × ℝ²`.
The key step is that the space-time periodization of a test in `C_c^∞((t₁,t₂) × ℝ²)` is a window
test function vanishing at `t₁` and `t₂`, and that integrals of periodic functions against `φ`
unfold to the cell. -/

theorem unitCube_measure_ne_top : (volume : Measure (Vec 2)) unitCube ≠ ⊤ := by
  unfold unitCube
  rw [volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

instance isFiniteMeasure_window (a b : ℝ) :
    IsFiniteMeasure (volume.restrict (Set.Ioo a b ×ˢ unitCube : Set (ℝ × Vec 2))) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ, Measure.volume_eq_prod, Measure.prod_prod]
  exact ENNReal.mul_lt_top (by simp [Real.volume_Ioo]) unitCube_measure_ne_top.lt_top

theorem memLp_two_integrable_window {a b : ℝ} {g : ℝ × Vec 2 → ℝ}
    (hg : MemLp g 2 (volume.restrict (Set.Ioo a b ×ˢ unitCube))) :
    Integrable g (volume.restrict (Set.Ioo a b ×ˢ unitCube)) := by

  exact hg.integrable (by norm_num)

theorem vecDot_periodic {u v : Vec 2 → Vec 2} (hu : IsZ2Periodic u) (hv : IsZ2Periodic v) :
    IsZ2Periodic (fun x => vecDot (u x) (v x)) := by
  intro k x
  simp only [hu k x, hv k x]

theorem supBall_of_compact {K : Set (ℝ × Vec 2)} (hK : IsCompact K) :
    ∃ R : ℝ, ∀ p ∈ K, ‖p.2‖ ≤ R := by
  obtain ⟨R, hR⟩ := (hK.image continuous_snd).isBounded.exists_norm_le
  exact ⟨R, fun p hp => hR p.2 ⟨p, hp, rfl⟩⟩

theorem hasWeakGradientOn_timeSection {t₁ t₂ : ℝ} {θ : ℝ → Vec 2 → ℝ}
    {Dθ : ℝ → Vec 2 → Vec 2}
    (h : ∀ᵐ t ∂(volume.restrict (Set.Ioo t₁ t₂)), IsPeriodicH1With (θ t) (Dθ t)) :
    ∀ᵐ t ∂(volume : Measure ℝ), HasWeakGradientOn
      (timeSection (Set.Ioo t₁ t₂ ×ˢ (Set.univ : Set (Vec 2))) t) (fun x => θ t x)
      (fun x => Dθ t x) := by
  have h' := (ae_restrict_iff' measurableSet_Ioo).1 h
  filter_upwards [h'] with t ht
  by_cases hmem : t ∈ Set.Ioo t₁ t₂
  · have hsec : timeSection (Set.Ioo t₁ t₂ ×ˢ (Set.univ : Set (Vec 2))) t = Set.univ := by
      ext x; simp [timeSection, hmem]
    rw [hsec]
    exact (ht hmem).2.2.2.2
  · have hsec : timeSection (Set.Ioo t₁ t₂ ×ˢ (Set.univ : Set (Vec 2))) t = ∅ := by
      ext x; simp [timeSection, hmem]
    rw [hsec]
    intro i φ _ _ _
    simp

theorem integral_combo {α : Type*} [MeasurableSpace α] {μ : Measure α} {A B C D : α → ℝ}
    (hA : Integrable A μ) (hB : Integrable B μ) (hC : Integrable C μ) (hD : Integrable D μ)
    (κ : ℝ) :
    ∫ x, (-(A x) + B x + κ * (C x + D x)) ∂μ =
      -∫ x, A x ∂μ + ∫ x, B x ∂μ + κ * (∫ x, C x ∂μ + ∫ x, D x ∂μ) := by
  have hnA : Integrable (fun x => -A x) μ := hA.neg
  have h1 : Integrable (fun x => -A x + B x) μ := hnA.add hB
  have h2 : Integrable (fun x => κ * (C x + D x)) μ := (hC.add hD).const_mul κ
  rw [integral_add h1 h2, integral_add hnA hB, integral_neg, integral_const_mul,
    integral_add hC hD]

theorem supBdd_perST_vanish {t₁ t₂ : ℝ} {φ : ℝ × Vec 2 → ℝ}
    (hφsub : tsupport φ ⊆ Set.Ioo t₁ t₂ ×ˢ (Set.univ : Set (Vec 2))) {t : ℝ}
    (ht : t ∉ Set.Ioo t₁ t₂) (x : Vec 2) : perST (slc φ) t x = 0 := by
  unfold perST
  refine finsum_eq_zero_of_forall_eq_zero fun n => ?_
  by_contra hne
  exact ht (hφsub (subset_tsupport _ hne)).1

/-- **Periodic lift** (explicit gradient form). -/
theorem isLocalWeakSolution_of_weakSolutionOnWith {b : ℝ → Vec 2 → Vec 2} {κ t₁ t₂ : ℝ}
    {f : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2}
    (hbp : ∀ t ∈ Set.Ioo t₁ t₂, IsZ2Periodic (b t))
    (h : IsWeakSolutionOnWith b κ t₁ t₂ f θ Dθ) :
    IsLocalWeakSolution b κ (Set.Ioo t₁ t₂ ×ˢ (Set.univ : Set (Vec 2)))
      (fun p => θ p.1 p.2) (fun p => Dθ p.1 p.2) := by
  obtain ⟨hslice, -, hL2, hDL2, hH1, hint, -, hweak⟩ := h
  have hIoo : MeasurableSet (Set.Ioo t₁ t₂) := measurableSet_Ioo
  have hθper : ∀ᵐ t ∂(volume.restrict (Set.Ioo t₁ t₂)), IsZ2Periodic (θ t) := by
    filter_upwards [ae_restrict_mem hIoo] with t ht
    exact (hslice t (Set.Ioo_subset_Icc_self ht)).1
  have hDper : ∀ᵐ t ∂(volume.restrict (Set.Ioo t₁ t₂)), IsZ2Periodic (Dθ t) := by
    filter_upwards [hH1] with t ht
    exact ht.2.1
  have hDcper : ∀ i : Fin 2, ∀ᵐ t ∂(volume.restrict (Set.Ioo t₁ t₂)),
      IsZ2Periodic (fun x => Dθ t x i) := fun i =>
    hDper.mono fun t ht k x => by simp [ht k x]
  have hbDper : ∀ᵐ t ∂(volume.restrict (Set.Ioo t₁ t₂)),
      IsZ2Periodic (fun x => vecDot (b t x) (Dθ t x)) := by
    filter_upwards [hDper, ae_restrict_mem hIoo] with t ht htm
    exact vecDot_periodic (hbp t htm) ht
  refine ⟨?_, ?_, hasWeakGradientOn_timeSection hH1, ?_⟩
  · intro K hKO hK
    obtain ⟨R, hR⟩ := supBall_of_compact hK
    exact (memLp_two_supBall_of_cell hIoo (G := fun t x => θ t x) hθper hL2 R).mono_measure
      (Measure.restrict_mono (fun p hp => Set.mem_prod.2 ⟨(hKO hp).1, hR p hp⟩) le_rfl)
  · intro K hKO hK i
    obtain ⟨R, hR⟩ := supBall_of_compact hK
    exact (memLp_two_supBall_of_cell hIoo (G := fun t x => Dθ t x i) (hDcper i) (hDL2 i)
      R).mono_measure (Measure.restrict_mono (fun p hp => Set.mem_prod.2 ⟨(hKO hp).1, hR p hp⟩) le_rfl)
  · intro φ hφ
    obtain ⟨hφs, hφc, hφsub⟩ := hφ
    have hvan : ∀ t, t ∉ Set.Ioo t₁ t₂ → ∀ x, perST (slc φ) t x = 0 := fun t ht x =>
      supBdd_perST_vanish hφsub ht x
    have htest : IsWindowTestFunction t₂ (perST (slc φ)) :=
      ⟨perST_slc_contDiff hφs hφc, fun t => perST_periodic _ t, fun t ht x =>
        hvan t (fun hm => absurd hm.2 (not_lt.2 ht)) x⟩
    have hw := hweak _ htest
    have hR := (exists_supBdd_of_hasCompactSupport hφc)
    obtain ⟨R, hR⟩ := hR
    have h0s : ContDiff ℝ (⊤ : ℕ∞) (fun p => fderiv ℝ φ p (1, 0)) :=
      contDiff_fderiv_apply_of_smooth hφs _
    have h0c : HasCompactSupport (fun p => fderiv ℝ φ p (1, 0)) :=
      hasCompactSupport_fderiv_apply hφc _
    have hjs : ∀ i : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun p => fderiv ℝ φ p (0, basisVec i)) :=
      fun i => contDiff_fderiv_apply_of_smooth hφs _
    have hjc : ∀ i : Fin 2, HasCompactSupport (fun p => fderiv ℝ φ p (0, basisVec i)) :=
      fun i => hasCompactSupport_fderiv_apply hφc _
    have hθint := memLp_two_integrable_window hL2
    have hDint := fun i => memLp_two_integrable_window (hDL2 i)
    obtain ⟨i0, j0, e0⟩ := integral_unfold_cs hIoo h0s h0c hθper hθint
    obtain ⟨i1, j1, e1⟩ := integral_unfold_cs hIoo hφs hφc hbDper hint
    obtain ⟨i2, j2, e2⟩ := integral_unfold_cs hIoo (hjs 0) (hjc 0) (hDcper 0) (hDint 0)
    obtain ⟨i3, j3, e3⟩ := integral_unfold_cs hIoo (hjs 1) (hjc 1) (hDcper 1) (hDint 1)
    -- the weak form on the cell, in terms of periodized tests
    have hcell : ∫ p in Set.Ioo t₁ t₂ ×ˢ unitCube,
        (-(θ p.1 p.2 * perST (slc fun q => fderiv ℝ φ q (1, 0)) p.1 p.2)
          + vecDot (b p.1 p.2) (Dθ p.1 p.2) * perST (slc φ) p.1 p.2
          + κ * (Dθ p.1 p.2 0 * perST (slc fun q => fderiv ℝ φ q (0, basisVec 0)) p.1 p.2
            + Dθ p.1 p.2 1 * perST (slc fun q => fderiv ℝ φ q (0, basisVec 1)) p.1 p.2)) = 0 := by
      have hrhs : ∫ x in unitCube, f x * perST (slc φ) t₁ x = 0 := by
        simp [hvan t₁ (by simp)]
      refine Eq.trans ?_ (hw.trans hrhs)
      refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      have hd : deriv (fun s => perST (slc φ) s p.2) p.1 =
          perST (slc fun q => fderiv ℝ φ q (1, 0)) p.1 p.2 := by
        rw [perST_deriv_time hR hφs]
        congr 1
        funext s y
        exact deriv_slc_eq hφs s y
      have hg : ∀ i : Fin 2, spaceGrad (perST (slc φ) p.1) p.2 i =
          perST (slc fun q => fderiv ℝ φ q (0, basisVec i)) p.1 p.2 := by
        intro i
        rw [spaceGrad_perST hR hφs]
        congr 1
        funext s y
        exact spaceGrad_slc_eq hφs s y i
      simp only [vecDot, Fin.sum_univ_two, hd, hg]
      ring
    have hO := integral_combo i0 i1 i2 i3 κ
    have hC' := integral_combo j0 j1 j2 j3 κ
    have hgoal : ∫ p in Set.Ioo t₁ t₂ ×ˢ (Set.univ : Set (Vec 2)),
        (-(θ p.1 p.2 * fderiv ℝ φ p (1, 0))
          + vecDot (b p.1 p.2) (Dθ p.1 p.2) * φ p
          + κ * (Dθ p.1 p.2 0 * fderiv ℝ φ p (0, basisVec 0)
            + Dθ p.1 p.2 1 * fderiv ℝ φ p (0, basisVec 1))) = 0 := by
      rw [hO, e0, e1, e2, e3, ← hC']
      exact hcell
    refine Eq.trans (integral_congr_ae (Eventually.of_forall fun p => ?_)) hgoal
    simp only [vecDot, Fin.sum_univ_two, stTimeDeriv_eq, stSpaceGrad_eq]

/-- **Periodic lift**: the periodic lift of a weak solution on `[t₁,t₂]` is a local weak
solution (display (8.3) of the paper) in `(t₁,t₂) × ℝ²`, with the gradient field `Dθ` of the
definition. Only the spatial periodicity of the drift is used (its integrability against `Dθ` is
part of `IsWeakSolutionOn`). -/
theorem isLocalWeakSolution_of_isWeakSolutionOn {b : ℝ → Vec 2 → Vec 2} {κ t₁ t₂ : ℝ}
    {f : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}
    (hbp : ∀ t ∈ Set.Ioo t₁ t₂, IsZ2Periodic (b t))
    (h : IsWeakSolutionOn b κ t₁ t₂ f θ) :
    ∃ Dθ : ℝ → Vec 2 → Vec 2, IsWeakSolutionOnWith b κ t₁ t₂ f θ Dθ ∧
      IsLocalWeakSolution b κ (Set.Ioo t₁ t₂ ×ˢ (Set.univ : Set (Vec 2)))
        (fun p => θ p.1 p.2) (fun p => Dθ p.1 p.2) := by
  obtain ⟨Dθ, hD⟩ := h
  exact ⟨Dθ, hD, isLocalWeakSolution_of_weakSolutionOnWith hbp hD⟩

/-! # A weak solution attains its initial datum weakly

For `θ` with `IsWeakSolutionOnWith b κ t₁ t₂ f θ Dθ` and `ψ` smooth periodic:
`∫_{𝕋²} θ(t₁) ψ = ∫_{𝕋²} f ψ`. Test the weak form with `η_δ(t) ψ(x)` where `η_δ` is a smooth cutoff
equal to `1` for `t ≤ t₁` and to `0` for `t ≥ t₁ + δ`, and let `δ → 0`. -/

section
/-- Smooth time cutoff: `1` for `t ≤ t₁`, `0` for `t ≥ t₁ + δ`. -/
def etaCut (t₁ δ t : ℝ) : ℝ := 1 - Real.smoothTransition ((t - t₁) / δ)

/-- Minus the derivative of `etaCut`: a smooth kernel of unit mass on `[t₁, t₁ + δ]`. -/
def kerCut (t₁ δ t : ℝ) : ℝ := deriv Real.smoothTransition ((t - t₁) / δ) / δ

section Cut

variable {t₁ δ : ℝ}

theorem etaCut_contDiff : ContDiff ℝ (⊤ : ℕ∞) (etaCut t₁ δ) := by
  unfold etaCut
  exact contDiff_const.sub (Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const δ))

theorem hasDerivAt_etaCut (t : ℝ) :
    HasDerivAt (etaCut t₁ δ) (-(kerCut t₁ δ t)) t := by
  have hS : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition ((t - t₁) / δ))
      ((t - t₁) / δ) :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable (by simp) _).hasDerivAt
  have hin : HasDerivAt (fun t : ℝ => (t - t₁) / δ) (1 / δ) t :=
    ((hasDerivAt_id t).sub_const t₁).div_const δ
  have := (hS.comp t hin).const_sub 1
  show HasDerivAt (fun t => 1 - Real.smoothTransition ((t - t₁) / δ)) _ t
  refine this.congr_deriv ?_
  simp [kerCut, div_eq_mul_inv, mul_comm]

theorem etaCut_of_le {t : ℝ} (ht : t ≤ t₁) (hδ : 0 < δ) : etaCut t₁ δ t = 1 := by
  unfold etaCut
  rw [Real.smoothTransition.zero_of_nonpos]
  · ring
  · exact div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le

theorem etaCut_of_ge {t : ℝ} (ht : t₁ + δ ≤ t) (hδ : 0 < δ) : etaCut t₁ δ t = 0 := by
  unfold etaCut
  rw [Real.smoothTransition.one_of_one_le]
  · ring
  · rw [le_div_iff₀ hδ]; linarith

theorem etaCut_nonneg (t : ℝ) : 0 ≤ etaCut t₁ δ t := by
  unfold etaCut; linarith [Real.smoothTransition.le_one ((t - t₁) / δ)]

theorem etaCut_le_one (t : ℝ) : etaCut t₁ δ t ≤ 1 := by
  unfold etaCut; linarith [Real.smoothTransition.nonneg ((t - t₁) / δ)]

theorem kerCut_nonneg (hδ : 0 < δ) (t : ℝ) : 0 ≤ kerCut t₁ δ t :=
  div_nonneg (Real.smoothTransition.monotone.deriv_nonneg) hδ.le

theorem kerCut_eq_zero_of_gt (hδ : 0 < δ) {t : ℝ} (ht : t₁ + δ < t) : kerCut t₁ δ t = 0 := by
  unfold kerCut
  have h1 : 1 < (t - t₁) / δ := by rw [lt_div_iff₀ hδ]; linarith
  have : Real.smoothTransition =ᶠ[𝓝 ((t - t₁) / δ)] fun _ => (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds h1] with x hx
    exact Real.smoothTransition.one_of_one_le (le_of_lt hx)
  rw [this.deriv_eq]
  simp

theorem kerCut_eq_zero_of_lt (hδ : 0 < δ) {t : ℝ} (ht : t < t₁) : kerCut t₁ δ t = 0 := by
  unfold kerCut
  have h1 : (t - t₁) / δ < 0 := div_neg_of_neg_of_pos (by linarith) hδ
  have : Real.smoothTransition =ᶠ[𝓝 ((t - t₁) / δ)] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds h1] with x hx
    exact Real.smoothTransition.zero_of_nonpos (le_of_lt hx)
  rw [this.deriv_eq]
  simp

theorem kerCut_continuous : Continuous (kerCut t₁ δ) := by
  unfold kerCut
  have h : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  exact (h.comp ((continuous_id.sub continuous_const).div_const δ)).div_const δ

theorem integral_kerCut (hδ : 0 < δ) {t₂ : ℝ} (h : t₁ + δ ≤ t₂) :
    ∫ t in t₁..t₂, kerCut t₁ δ t = 1 := by
  have h1 : ∫ t in t₁..t₂, -(kerCut t₁ δ t) = etaCut t₁ δ t₂ - etaCut t₁ δ t₁ :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_etaCut t)
      (kerCut_continuous.neg.intervalIntegrable _ _)
  rw [intervalIntegral.integral_neg, etaCut_of_ge (by linarith) hδ,
    etaCut_of_le le_rfl hδ] at h1
  linarith

end Cut

theorem exists_bound_cube {g : Vec 2 → ℝ} (hg : Continuous g) :
    ∃ C : ℝ, ∀ x ∈ unitCube, |g x| ≤ C := by
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨C, fun x hx => ?_⟩
  have : x ∈ Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1 := fun i hi =>
    ⟨(hx i hi).1.le, (hx i hi).2.le⟩
  simpa using hC x this

theorem spaceGrad_const_mul {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (c : ℝ) (x : Vec 2) :
    spaceGrad (fun y => c * ψ y) x = c • spaceGrad ψ x := by
  funext i
  have hd : DifferentiableAt ℝ ψ x := (hψ.differentiable (by simp)) x
  simp [spaceGrad, fderiv_const_mul hd]

/-- **Weak attainment of the initial datum.** -/
theorem initial_pairing {b : ℝ → Vec 2 → Vec 2} {κ t₁ t₂ : ℝ} {f : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2} (h12 : t₁ < t₂)
    (h : IsWeakSolutionOnWith b κ t₁ t₂ f θ Dθ) {ψ : Vec 2 → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψp : IsZ2Periodic ψ) :
    ∫ x in unitCube, θ t₁ x * ψ x = ∫ x in unitCube, f x * ψ x := by
  obtain ⟨hslice, -, hL2, hDL2, -, hint, hcont, hweak⟩ := h
  set a : ℝ → ℝ := fun t => ∫ x in unitCube, θ t x * ψ x with ha_def
  have ha : ContinuousOn a (Set.Icc t₁ t₂) := hcont ψ hψ hψp
  obtain ⟨Cψ, hCψ⟩ := exists_bound_cube hψ.continuous
  obtain ⟨C0, hC0⟩ := exists_bound_cube (contDiff_fderiv_apply_of_smooth hψ (basisVec 0)).continuous
  obtain ⟨C1, hC1⟩ := exists_bound_cube (contDiff_fderiv_apply_of_smooth hψ (basisVec 1)).continuous
  set H : ℝ × Vec 2 → ℝ := fun p => vecDot (b p.1 p.2) (Dθ p.1 p.2) * ψ p.2
    + κ * (Dθ p.1 p.2 0 * spaceGrad ψ p.2 0 + Dθ p.1 p.2 1 * spaceGrad ψ p.2 1) with hH
  have hmeasC : MeasurableSet (Set.Ioo t₁ t₂ ×ˢ unitCube : Set (ℝ × Vec 2)) :=
    measurableSet_Ioo.prod measurableSet_unitCube'
  have hbd : ∀ {g : Vec 2 → ℝ} {C : ℝ}, Continuous g → (∀ x ∈ unitCube, |g x| ≤ C) →
      ∀ {F : ℝ × Vec 2 → ℝ}, Integrable F (volume.restrict (Set.Ioo t₁ t₂ ×ˢ unitCube)) →
      Integrable (fun p => F p * g p.2) (volume.restrict (Set.Ioo t₁ t₂ ×ˢ unitCube)) := by
    intro g C hg hC F hF
    refine hF.mul_bdd (hg.comp continuous_snd).aestronglyMeasurable (c := C) ?_
    filter_upwards [ae_restrict_mem hmeasC] with p hp
    simpa using hC p.2 hp.2
  have hθint := memLp_two_integrable_window hL2
  have hDint := fun i => memLp_two_integrable_window (hDL2 i)
  have hHint : Integrable H (volume.restrict (Set.Ioo t₁ t₂ ×ˢ unitCube)) := by
    refine (hbd hψ.continuous hCψ hint).add ?_
    refine Integrable.const_mul ?_ κ
    exact (hbd (contDiff_fderiv_apply_of_smooth hψ (basisVec 0)).continuous hC0 (hDint 0)).add
      (hbd (contDiff_fderiv_apply_of_smooth hψ (basisVec 1)).continuous hC1 (hDint 1))
  -- the identity for each small `δ`
  have hid : ∀ δ : ℝ, 0 < δ → δ ≤ t₂ - t₁ →
      (∫ t in Set.Ioo t₁ t₂, a t * kerCut t₁ δ t)
        + ∫ p in Set.Ioo t₁ t₂ ×ˢ unitCube, etaCut t₁ δ p.1 * H p
        = ∫ x in unitCube, f x * ψ x := by
    intro δ hδ hδ2
    have htest : IsWindowTestFunction t₂ (fun t x => etaCut t₁ δ t * ψ x) := by
      refine ⟨?_, fun t k x => ?_, fun t ht x => ?_⟩
      · exact ((etaCut_contDiff.comp contDiff_fst).mul (hψ.comp contDiff_snd))
      · simp [hψp k x]
      · simp [etaCut_of_ge (t₁ := t₁) (δ := δ) (t := t) (by linarith) hδ]
    have hw := hweak _ htest
    have hder : ∀ p : ℝ × Vec 2, deriv (fun s => etaCut t₁ δ s * ψ p.2) p.1 =
        -(kerCut t₁ δ p.1) * ψ p.2 := fun p =>
      ((hasDerivAt_etaCut p.1).mul_const (ψ p.2)).deriv
    have hpt : ∀ p : ℝ × Vec 2,
        (-(θ p.1 p.2) * deriv (fun s => etaCut t₁ δ s * ψ p.2) p.1
          + vecDot (b p.1 p.2) (Dθ p.1 p.2) * (etaCut t₁ δ p.1 * ψ p.2)
          + κ * vecDot (Dθ p.1 p.2) (spaceGrad (fun y => etaCut t₁ δ p.1 * ψ y) p.2)) =
        θ p.1 p.2 * ψ p.2 * kerCut t₁ δ p.1 + etaCut t₁ δ p.1 * H p := by
      intro p
      rw [hder p, spaceGrad_const_mul hψ]
      simp only [hH, vecDot, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
      ring
    have hk : Integrable (fun p : ℝ × Vec 2 => θ p.1 p.2 * ψ p.2 * kerCut t₁ δ p.1)
        (volume.restrict (Set.Ioo t₁ t₂ ×ˢ unitCube)) := by
      have := hbd hψ.continuous hCψ hθint
      obtain ⟨K, hK⟩ : ∃ K, ∀ t, |kerCut t₁ δ t| ≤ K := by
        have hc : Continuous (kerCut t₁ δ) := kerCut_continuous
        have hcs : HasCompactSupport (kerCut t₁ δ) := by
          refine HasCompactSupport.intro (isCompact_Icc (a := t₁) (b := t₁ + δ)) fun t ht => ?_
          rcases lt_or_gt_of_ne (show t ≠ t₁ + δ by
            intro h; exact ht ⟨by linarith, by linarith⟩) with h1 | h1
          · rcases lt_or_ge t t₁ with h2 | h2
            · exact kerCut_eq_zero_of_lt hδ h2
            · exact absurd ⟨h2, h1.le⟩ ht
          · exact kerCut_eq_zero_of_gt hδ h1
        obtain ⟨K, hK⟩ := hc.bounded_above_of_compact_support hcs
        exact ⟨K, fun t => by simpa using hK t⟩
      exact this.mul_bdd (kerCut_continuous.comp continuous_fst).aestronglyMeasurable (c := K)
        (Eventually.of_forall fun p => by simpa using hK p.1)
    have hη : Integrable (fun p : ℝ × Vec 2 => etaCut t₁ δ p.1 * H p)
        (volume.restrict (Set.Ioo t₁ t₂ ×ˢ unitCube)) := by
      refine hHint.bdd_mul (c := 1) ((etaCut_contDiff.continuous).comp
        continuous_fst).aestronglyMeasurable (Eventually.of_forall fun p => ?_)
      have := etaCut_nonneg (t₁ := t₁) (δ := δ) p.1
      have := etaCut_le_one (t₁ := t₁) (δ := δ) p.1
      rwa [Real.norm_eq_abs, abs_of_nonneg (by assumption)]
    simp_rw [hpt] at hw
    rw [integral_add hk hη] at hw
    have hrhs : ∫ x in unitCube, f x * (etaCut t₁ δ t₁ * ψ x) = ∫ x in unitCube, f x * ψ x := by
      simp [etaCut_of_le le_rfl hδ]
    rw [hrhs] at hw
    rw [← hw]
    congr 1
    have hk' : Integrable (fun p : ℝ × Vec 2 => θ p.1 p.2 * ψ p.2 * kerCut t₁ δ p.1)
        ((volume.restrict (Set.Ioo t₁ t₂)).prod (volume.restrict unitCube)) := by
      rwa [← volume_restrict_prod_eq]
    rw [volume_restrict_prod_eq, integral_prod _ hk']
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [ha_def]
    rw [← integral_mul_const]
  -- the dissipative remainder tends to zero
  have hE : Tendsto (fun δ : ℝ => ∫ p in Set.Ioo t₁ t₂ ×ˢ unitCube, etaCut t₁ δ p.1 * H p)
      (𝓝[>] 0) (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence
      (μ := volume.restrict (Set.Ioo t₁ t₂ ×ˢ unitCube)) (l := 𝓝[>] (0 : ℝ))
      (F := fun δ p => etaCut t₁ δ p.1 * H p) (f := fun _ => (0 : ℝ))
      (bound := fun p => ‖H p‖) ?_ ?_ hHint.norm ?_
    · simpa using this
    · exact Eventually.of_forall fun δ =>
        (((etaCut_contDiff (t₁ := t₁) (δ := δ)).continuous.comp
          continuous_fst).aestronglyMeasurable).mul hHint.aestronglyMeasurable
    · refine Eventually.of_forall fun δ => Eventually.of_forall fun p => ?_
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (etaCut_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (etaCut_le_one _)
    · filter_upwards [ae_restrict_mem hmeasC] with p hp
      have hpos : 0 < p.1 - t₁ := by linarith [hp.1.1]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hpos] with δ hδ
      rw [etaCut_of_ge (t₁ := t₁) (δ := δ) (t := p.1) (by linarith [hδ.1, hδ.2]) hδ.1]
      simp
  -- the kernel term tends to `a t₁`
  have hΛ : Tendsto (fun δ : ℝ => ∫ t in Set.Ioo t₁ t₂, a t * kerCut t₁ δ t) (𝓝[>] 0)
      (𝓝 (a t₁)) := by
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨r, hr, hra⟩ := Metric.continuousWithinAt_iff.1 (ha t₁ ⟨le_rfl, h12.le⟩) (ε / 2)
      (half_pos hε)
    refine ⟨min r (t₂ - t₁), lt_min hr (by linarith), fun δ hδpos hδ => ?_⟩
    have hδ0 : 0 < δ := hδpos
    have hδ' : δ < min r (t₂ - t₁) := by simpa [Real.dist_eq, abs_of_pos hδ0] using hδ
    have hδr : δ < r := lt_of_lt_of_le hδ' (min_le_left _ _)
    have hδt : δ < t₂ - t₁ := lt_of_lt_of_le hδ' (min_le_right _ _)
    have hker1 : ∫ t in Set.Ioo t₁ t₂, kerCut t₁ δ t = 1 := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le h12.le]
      exact integral_kerCut hδ0 (by linarith)
    have hkerInt : IntegrableOn (kerCut t₁ δ) (Set.Ioo t₁ t₂) :=
      (kerCut_continuous.continuousOn.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
    have haInt : IntegrableOn (fun t => a t * kerCut t₁ δ t) (Set.Ioo t₁ t₂) :=
      ((ha.mul kerCut_continuous.continuousOn).integrableOn_Icc).mono_set
        Set.Ioo_subset_Icc_self
    have hdiff : (∫ t in Set.Ioo t₁ t₂, a t * kerCut t₁ δ t) - a t₁ =
        ∫ t in Set.Ioo t₁ t₂, (a t - a t₁) * kerCut t₁ δ t := by
      have : ∫ t in Set.Ioo t₁ t₂, (a t - a t₁) * kerCut t₁ δ t =
          (∫ t in Set.Ioo t₁ t₂, a t * kerCut t₁ δ t) -
            ∫ t in Set.Ioo t₁ t₂, a t₁ * kerCut t₁ δ t := by
        rw [← integral_sub haInt (hkerInt.const_mul (a t₁))]
        exact integral_congr_ae (Eventually.of_forall fun t => by ring)
      rw [this, integral_const_mul, hker1, mul_one]
    rw [Real.dist_eq, hdiff]
    have hle : ‖∫ t in Set.Ioo t₁ t₂, (a t - a t₁) * kerCut t₁ δ t‖ ≤
        ∫ t in Set.Ioo t₁ t₂, (ε / 2) * kerCut t₁ δ t := by
      refine norm_integral_le_of_norm_le (hkerInt.const_mul (ε / 2)) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (kerCut_nonneg hδ0 t)]
      rcases le_or_gt t (t₁ + δ) with h1 | h1
      · have := hra (x := t) ⟨ht.1.le, ht.2.le⟩ (by
          rw [Real.dist_eq, abs_of_pos (by linarith [ht.1])]; linarith)
        rw [Real.dist_eq] at this
        exact mul_le_mul_of_nonneg_right this.le (kerCut_nonneg hδ0 t)
      · simp [kerCut_eq_zero_of_gt hδ0 h1]
    rw [integral_const_mul, hker1, mul_one] at hle
    rw [Real.norm_eq_abs] at hle
    linarith
  -- conclude
  have hconst : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
      (∫ t in Set.Ioo t₁ t₂, a t * kerCut t₁ δ t)
        + ∫ p in Set.Ioo t₁ t₂ ×ˢ unitCube, etaCut t₁ δ p.1 * H p
        = ∫ x in unitCube, f x * ψ x := by
    filter_upwards [Ioo_mem_nhdsGT (show 0 < t₂ - t₁ by linarith)] with δ hδ
    exact hid δ hδ.1 hδ.2.le
  have := tendsto_nhds_unique (hΛ.add hE) (tendsto_const_nhds.congr' (hconst.mono fun δ h => h.symm))
  simpa using this
end

/-! # Integrability of the local weak form

Supplement to `isLocalWeakSolution_of_weakSolutionOnWith`: the integrand of the local weak form is
integrable on `(t₁,t₂) × ℝ²` against every test, so that the local weak forms of two solutions can be
subtracted. -/

theorem localWeak_integrable {b : ℝ → Vec 2 → Vec 2} {κ t₁ t₂ : ℝ} {f : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2}
    (hbp : ∀ t ∈ Set.Ioo t₁ t₂, IsZ2Periodic (b t))
    (h : IsWeakSolutionOnWith b κ t₁ t₂ f θ Dθ) {φ : ℝ × Vec 2 → ℝ}
    (hφ : IsSTTest (Set.Ioo t₁ t₂ ×ˢ (Set.univ : Set (Vec 2))) φ) :
    Integrable (fun p : ℝ × Vec 2 =>
      (-(θ p.1 p.2 * stTimeDeriv φ p) + vecDot (b p.1 p.2) (Dθ p.1 p.2) * φ p
        + κ * vecDot (Dθ p.1 p.2) (stSpaceGrad φ p)))
      (volume.restrict (Set.Ioo t₁ t₂ ×ˢ (Set.univ : Set (Vec 2)))) := by
  obtain ⟨hslice, -, hL2, hDL2, hH1, hint, -, -⟩ := h
  obtain ⟨hφs, hφc, -⟩ := hφ
  have hIoo : MeasurableSet (Set.Ioo t₁ t₂) := measurableSet_Ioo
  have hθper : ∀ᵐ t ∂(volume.restrict (Set.Ioo t₁ t₂)), IsZ2Periodic (θ t) := by
    filter_upwards [ae_restrict_mem hIoo] with t ht
    exact (hslice t (Set.Ioo_subset_Icc_self ht)).1
  have hDper : ∀ᵐ t ∂(volume.restrict (Set.Ioo t₁ t₂)), IsZ2Periodic (Dθ t) := by
    filter_upwards [hH1] with t ht
    exact ht.2.1
  have hDcper : ∀ i : Fin 2, ∀ᵐ t ∂(volume.restrict (Set.Ioo t₁ t₂)),
      IsZ2Periodic (fun x => Dθ t x i) := fun i =>
    hDper.mono fun t ht k x => by simp [ht k x]
  have hbDper : ∀ᵐ t ∂(volume.restrict (Set.Ioo t₁ t₂)),
      IsZ2Periodic (fun x => vecDot (b t x) (Dθ t x)) := by
    filter_upwards [hDper, ae_restrict_mem hIoo] with t ht htm
    exact vecDot_periodic (hbp t htm) ht
  have h0s : ContDiff ℝ (⊤ : ℕ∞) (fun p => fderiv ℝ φ p (1, 0)) :=
    contDiff_fderiv_apply_of_smooth hφs _
  have h0c : HasCompactSupport (fun p => fderiv ℝ φ p (1, 0)) :=
    hasCompactSupport_fderiv_apply hφc _
  have hjs : ∀ i : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun p => fderiv ℝ φ p (0, basisVec i)) :=
    fun i => contDiff_fderiv_apply_of_smooth hφs _
  have hjc : ∀ i : Fin 2, HasCompactSupport (fun p => fderiv ℝ φ p (0, basisVec i)) :=
    fun i => hasCompactSupport_fderiv_apply hφc _
  have hθint := memLp_two_integrable_window hL2
  have hDint := fun i => memLp_two_integrable_window (hDL2 i)
  obtain ⟨i0, -, -⟩ := integral_unfold_cs hIoo h0s h0c hθper hθint
  obtain ⟨i1, -, -⟩ := integral_unfold_cs hIoo hφs hφc hbDper hint
  obtain ⟨i2, -, -⟩ := integral_unfold_cs hIoo (hjs 0) (hjc 0) (hDcper 0) (hDint 0)
  obtain ⟨i3, -, -⟩ := integral_unfold_cs hIoo (hjs 1) (hjc 1) (hDcper 1) (hDint 1)
  have := (i0.neg.add i1).add ((i2.add i3).const_mul κ)
  refine this.congr (Eventually.of_forall fun p => ?_)
  simp only [vecDot, Fin.sum_univ_two, stTimeDeriv_eq, stSpaceGrad_eq, Pi.add_apply, Pi.neg_apply]

end AVRegularity.Applications
end
