-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Applications.Davies.UfEnergy
import AVRegularity.Applications.TorusEnergy.StreamFacts
public import AVRegularity.Applications.Davies.ChartBridge
import AVRegularity.Applications.Construction.StreamTail
import AVRegularity.Applications.LocalEnergy.Caccioppoli
import AVRegularity.Applications.Microscopic.DilationTests
import AVRegularity.Applications.Pipe.LocalEnergy
import AVRegularity.CycleReference.SpacetimeGradientPairing
import AVenhance.Infra.Flow.JointSmoothFromFixedStart
import AVenhance.Infra.Construction.StreamAdmissible
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section
noncomputable section

section
open MeasureTheory Homogenization AVenhance Filter Topology
namespace AVRegularity.Applications.Davies

/-! # Weak attainment of the initial datum for the pulled-back solution

For `ρ ∈ C_c^∞(ℝ²)`, `τ ↦ ∫ u(τ, F_τ y) ρ(y) dy` is continuous (from the right) at the initial time
and its value there is `∫ f(F_{s₀} y) ρ(y) dy`. -/

section
open AVRegularity.Applications AVRegularity.CycleReference

theorem volume_unitCube_eq_one' : (volume : Measure (Vec 2)) unitCube = 1 := by
  simp [unitCube, volume_pi, Measure.pi_pi, Real.volume_Ioo]

section

variable {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) {X : ℝ → Vec 2 → ℝ → Vec 2}
  (hX : IsFlow (streamVel φ) X)

include hφ hX

theorem X_left (τ t₁ : ℝ) (y : Vec 2) : X t₁ (X τ y t₁) τ = y := by
  have := (Infra.Flow.flow_group_law _ hφ.vel_lipschitz hX y t₁ τ t₁)
  exact this.trans (hX.1 y t₁)

theorem X_right (τ t₁ : ℝ) (x : Vec 2) : X τ (X t₁ x τ) t₁ = x := by
  have := (Infra.Flow.flow_group_law _ hφ.vel_lipschitz hX x τ t₁ τ)
  exact this.trans (hX.1 x τ)

theorem X_smooth (t s : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fun y => X t y s) := by
  rw [X_eq_streamFlow hφ hX]
  exact streamFlow_spatial_smooth hφ t s

/-- The pairing of the pulled-back slice with `ρ`, as a cell pairing against a periodized test. -/
theorem pullback_pairing {ρ : Vec 2 → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ)
    (τ t₁ : ℝ) {g : Vec 2 → ℝ} (hper : IsZ2Periodic g) (hg : MemL2On unitCube g) :
    ∫ y, g (X τ y t₁) * ρ y = ∫ x in unitCube, g x * perX (fun x => ρ (X t₁ x τ)) x := by
  have hΘs : ContDiff ℝ (⊤ : ℕ∞) (fun x => ρ (X t₁ x τ)) := hρ.comp (X_smooth hφ hX t₁ τ)
  have hΘc : HasCompactSupport (fun x => ρ (X t₁ x τ)) := by
    have := X_eq_streamFlow hφ hX
    subst this
    exact hρc.comp_homeomorph (streamFlowHomeomorph hφ t₁ τ)
  have hint : Integrable g (volume.restrict unitCube) := hg.integrable (by norm_num)
  rw [← integral_unfold_space hΘs hΘc hper hint]
  have hmp := X_mp hφ hX τ t₁
  have hme : MeasurableEmbedding (fun x => X τ x t₁) := by
    have := X_eq_streamFlow hφ hX
    subst this
    exact (streamFlowHomeomorph hφ τ t₁).measurableEmbedding
  rw [← hmp.integral_comp hme (fun x => g x * ρ (X t₁ x τ))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [X_left hφ hX τ t₁ y]


end

/-- A smooth time cutoff, equal to `1` on `[a, b]` and supported in `[a - 1, b + 1]`. -/
def timeCut (a b τ : ℝ) : ℝ := Real.smoothTransition (τ - a + 1) * Real.smoothTransition (b + 1 - τ)

theorem timeCut_contDiff (a b : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (timeCut a b) :=
  (Real.smoothTransition.contDiff.comp (by fun_prop)).mul
    (Real.smoothTransition.contDiff.comp (by fun_prop))

theorem timeCut_eq_one {a b τ : ℝ} (h : τ ∈ Set.Icc a b) : timeCut a b τ = 1 := by
  unfold timeCut
  rw [Real.smoothTransition.one_of_one_le (by linarith [h.1]),
    Real.smoothTransition.one_of_one_le (by linarith [h.2]), one_mul]

theorem timeCut_ne_zero {a b τ : ℝ} (h : timeCut a b τ ≠ 0) : τ ∈ Set.Icc (a - 1) (b + 1) := by
  unfold timeCut at h
  have h1 : Real.smoothTransition (τ - a + 1) ≠ 0 := left_ne_zero_of_mul h
  have h2 : Real.smoothTransition (b + 1 - τ) ≠ 0 := right_ne_zero_of_mul h
  have h1' : 0 < τ - a + 1 := by
    by_contra hh
    exact h1 (Real.smoothTransition.zero_of_nonpos (not_lt.1 hh))
  have h2' : 0 < b + 1 - τ := by
    by_contra hh
    exact h2 (Real.smoothTransition.zero_of_nonpos (not_lt.1 hh))
  exact ⟨by linarith, by linarith⟩

section

variable {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) {X : ℝ → Vec 2 → ℝ → Vec 2}
  (hX : IsFlow (streamVel φ) X)

include hφ hX

/-- The periodized transported test, as a joint function of time and space. -/
theorem psi_joint_contDiff {ρ : Vec 2 → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hρc : HasCompactSupport ρ) (a b t₁ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 =>
      perST (fun τ x => timeCut a b τ * ρ (X t₁ x τ)) p.1 p.2) := by
  have hb := AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ
  have hflow := AVenhance.Infra.Flow.flow_joint_contDiff_infty hb hX
  have hjoint : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => X t₁ p.2 p.1) :=
    hflow.comp (contDiff_const.prodMk (contDiff_snd.prodMk contDiff_fst))
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => timeCut a b p.1 * ρ (X t₁ p.2 p.1)) :=
    ((timeCut_contDiff a b).comp contDiff_fst).mul (hρ.comp hjoint)
  have hFc : Continuous (fun p : ℝ × Vec 2 => X p.1 p.2 t₁) :=
    (hflow.comp (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const))).continuous
  obtain ⟨R, hR⟩ := ((isCompact_Icc (a := a - 1) (b := b + 1)).prod hρc).image hFc
    |>.isBounded.exists_norm_le
  refine perST_contDiff (R := R) ?_ hs
  intro τ x hne
  have hk : timeCut a b τ ≠ 0 := left_ne_zero_of_mul hne
  have hρne : ρ (X t₁ x τ) ≠ 0 := right_ne_zero_of_mul hne
  apply hR
  refine ⟨(τ, X t₁ x τ), ⟨timeCut_ne_zero hk, subset_tsupport _ hρne⟩, ?_⟩
  simp [X_right hφ hX τ t₁ x]


omit hφ hX in
theorem psi_eq_joint {ρ : Vec 2 → ℝ} (a b t₁ : ℝ) {τ : ℝ} (hτ : τ ∈ Set.Icc a b) (x : Vec 2) :
    perX (fun x => ρ (X t₁ x τ)) x = perST (fun τ x => timeCut a b τ * ρ (X t₁ x τ)) τ x := by
  simp [perX, perST, timeCut_eq_one hτ]

theorem psi_unif {ρ : Vec 2 → ℝ} (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hρc : HasCompactSupport ρ) {a b : ℝ} (hab : a ≤ b) (t₁ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ τ ∈ Set.Icc a b, |τ - a| < δ → ∀ x ∈ unitCube,
      |perX (fun x => ρ (X t₁ x τ)) x - perX (fun x => ρ (X t₁ x a)) x| < ε := by
  have hP := (psi_joint_contDiff hφ hX hρ hρc a b t₁).continuous
  have hK : IsCompact (Set.Icc a b ×ˢ (Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)) :=
    isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)
  have hU := hK.uniformContinuousOn_of_continuous hP.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hU
  obtain ⟨δ, hδ, h⟩ := hU ε hε
  refine ⟨δ, hδ, fun τ hτ hτδ x hx => ?_⟩
  have hxc : x ∈ Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1 := fun i hi =>
    ⟨(hx i hi).1.le, (hx i hi).2.le⟩
  have := h (τ, x) ⟨hτ, hxc⟩ (a, x) ⟨⟨le_rfl, hab⟩, hxc⟩ (by
    rw [Prod.dist_eq]; simp [Real.dist_eq, hτδ])
  rw [psi_eq_joint (X := X) a b t₁ hτ, psi_eq_joint (X := X) a b t₁ ⟨le_rfl, hab⟩]
  simpa [Real.dist_eq] using this


/-- **Initial datum of the pulled-back solution, weakly.** -/
theorem uf_initial {b : ℝ → Vec 2 → Vec 2} {κ s₀ e t₁ : ℝ} {f : Vec 2 → ℝ}
    {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    (hu : IsWeakSolutionOnWith b κ s₀ e f u Du) (hse : s₀ < e) (hst : s₀ ≤ t₁) (hte : t₁ ≤ e)
    (hfp : IsZ2Periodic f) (hf : MemL2On unitCube f) {ρ : Vec 2 → ℝ}
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρc : HasCompactSupport ρ) :
    ContinuousWithinAt (fun τ => ∫ y, u τ (X τ y t₁) * ρ y) (Set.Icc s₀ t₁) s₀ ∧
      ∫ y, u s₀ (X s₀ y t₁) * ρ y = ∫ y, f (X s₀ y t₁) * ρ y := by
  have hu' := hu
  obtain ⟨hslice, ⟨Cb, hCb⟩, -, -, -, -, hcont, -⟩ := hu'
  have hΘ : ∀ τ, ContDiff ℝ (⊤ : ℕ∞) (fun x => ρ (X t₁ x τ)) := fun τ =>
    hρ.comp (X_smooth hφ hX t₁ τ)
  have hΘc : ∀ τ, HasCompactSupport (fun x => ρ (X t₁ x τ)) := fun τ => by
    have := X_eq_streamFlow hφ hX
    subst this
    exact hρc.comp_homeomorph (streamFlowHomeomorph hφ t₁ τ)
  have hψs : ∀ τ, ContDiff ℝ (⊤ : ℕ∞) (perX fun x => ρ (X t₁ x τ)) := fun τ =>
    perX_contDiff (hΘ τ) (hΘc τ)
  have hs₀ : s₀ ∈ Set.Icc s₀ e := ⟨le_rfl, hse.le⟩
  refine ⟨?_, ?_⟩
  · -- continuity
    have hcongr : ∀ τ ∈ Set.Icc s₀ t₁, ∫ y, u τ (X τ y t₁) * ρ y =
        ∫ x in unitCube, u τ x * perX (fun x => ρ (X t₁ x τ)) x := fun τ hτ =>
      pullback_pairing hφ hX hρ hρc τ t₁ (hslice τ ⟨hτ.1, hτ.2.trans hte⟩).1
        (hslice τ ⟨hτ.1, hτ.2.trans hte⟩).2
    refine ContinuousWithinAt.congr (f := fun τ => ∫ x in unitCube,
      u τ x * perX (fun x => ρ (X t₁ x τ)) x) ?_ hcongr (hcongr s₀ ⟨le_rfl, hst⟩)
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    have hK : 0 < (1 + max Cb 0) / 2 + 1 := by positivity
    set ε' := ε / (2 * ((1 + max Cb 0) / 2 + 1)) with hε'
    have hε'0 : 0 < ε' := by positivity
    obtain ⟨δ₁, hδ₁, hu1⟩ := psi_unif hφ hX hρ hρc hst t₁ hε'0
    have hw := (hcont _ (hψs s₀) (perX_periodic _)) s₀ hs₀
    rw [Metric.continuousWithinAt_iff] at hw
    obtain ⟨δ₂, hδ₂, hw2⟩ := hw (ε / 2) (by positivity)
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun τ hτ hdist => ?_⟩
    have hτI : τ ∈ Set.Icc s₀ e := ⟨hτ.1, hτ.2.trans hte⟩
    have hd1 : |τ - s₀| < δ₁ := lt_of_lt_of_le (by simpa [Real.dist_eq] using hdist) (min_le_left _ _)
    have hd2 : dist τ s₀ < δ₂ := lt_of_lt_of_le hdist (min_le_right _ _)
    have h1 := hw2 hτI hd2
    -- the difference of the test functions
    have hint : Integrable (u τ) (volume.restrict unitCube) := (hslice τ hτI).2.integrable (by norm_num)
    have hbd : ∀ g : Vec 2 → ℝ, Continuous g → ∃ C, ∀ x ∈ unitCube, |g x| ≤ C := fun g hg =>
      exists_bound_cube hg
    obtain ⟨C1, hC1⟩ := hbd _ (hψs τ).continuous
    obtain ⟨C0, hC0⟩ := hbd _ (hψs s₀).continuous
    have hmeas : MeasurableSet unitCube := measurableSet_unitCube'
    have iA : Integrable (fun x => u τ x * perX (fun x => ρ (X t₁ x τ)) x)
        (volume.restrict unitCube) :=
      hint.mul_bdd (hψs τ).continuous.aestronglyMeasurable (c := C1)
        ((ae_restrict_iff' hmeas).2 (Filter.Eventually.of_forall fun x hx => by
          simpa using hC1 x hx))
    have iB : Integrable (fun x => u τ x * perX (fun x => ρ (X t₁ x s₀)) x)
        (volume.restrict unitCube) :=
      hint.mul_bdd (hψs s₀).continuous.aestronglyMeasurable (c := C0)
        ((ae_restrict_iff' hmeas).2 (Filter.Eventually.of_forall fun x hx => by
          simpa using hC0 x hx))
    have hsplit : (∫ x in unitCube, u τ x * perX (fun x => ρ (X t₁ x τ)) x) -
        ∫ x in unitCube, u τ x * perX (fun x => ρ (X t₁ x s₀)) x =
        ∫ x in unitCube, u τ x * (perX (fun x => ρ (X t₁ x τ)) x -
          perX (fun x => ρ (X t₁ x s₀)) x) := by
      rw [← integral_sub iA iB]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [mul_sub]
    have hl2 : l2NormSq (u τ) ≤ max Cb 0 := (hCb τ hτI).trans (le_max_left _ _)
    have hgi : Integrable (fun x => ε' * ((1 + u τ x ^ 2) / 2)) (volume.restrict unitCube) := by
      have hfin : IsFiniteMeasure (volume.restrict unitCube : Measure (Vec 2)) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact unitCube_measure_ne_top.lt_top⟩
      exact ((integrable_const (1 : ℝ)).add (hslice τ hτI).2.integrable_sq |>.div_const 2).const_mul ε'
    have hbound : |∫ x in unitCube, u τ x * (perX (fun x => ρ (X t₁ x τ)) x -
          perX (fun x => ρ (X t₁ x s₀)) x)| ≤ ε' * ((1 + max Cb 0) / 2) := by
      have := norm_integral_le_of_norm_le hgi (μ := volume.restrict unitCube)
        (f := fun x => u τ x * (perX (fun x => ρ (X t₁ x τ)) x -
          perX (fun x => ρ (X t₁ x s₀)) x)) ((ae_restrict_iff' hmeas).2
          (Filter.Eventually.of_forall fun x hx => by
            have h := hu1 τ hτ hd1 x hx
            rw [Real.norm_eq_abs, abs_mul]
            have h0 := abs_nonneg (u τ x)
            have h2 : |u τ x| ≤ (1 + u τ x ^ 2) / 2 := by
              nlinarith [sq_nonneg (|u τ x| - 1), sq_abs (u τ x)]
            calc |u τ x| * |perX (fun x => ρ (X t₁ x τ)) x - perX (fun x => ρ (X t₁ x s₀)) x|
                ≤ |u τ x| * ε' := mul_le_mul_of_nonneg_left h.le h0
              _ ≤ (1 + u τ x ^ 2) / 2 * ε' := mul_le_mul_of_nonneg_right h2 hε'0.le
              _ = ε' * ((1 + u τ x ^ 2) / 2) := by ring))
      rw [Real.norm_eq_abs] at this
      refine this.trans ?_
      rw [integral_const_mul, integral_div, integral_add (integrable_const (1 : ℝ))
        (hslice τ hτI).2.integrable_sq]
      simp only [integral_const, Measure.restrict_apply_univ, Measure.real,
        volume_unitCube_eq_one', ENNReal.toReal_one, smul_eq_mul, one_mul]
      have hl2' := hl2
      unfold l2NormSq at hl2'
      nlinarith [hε'0]
    have h1' : |(∫ x in unitCube, u τ x * perX (fun x => ρ (X t₁ x s₀)) x) -
        ∫ x in unitCube, u s₀ x * perX (fun x => ρ (X t₁ x s₀)) x| < ε / 2 := by
      simpa [Real.dist_eq] using h1
    have hKε : ε' * ((1 + max Cb 0) / 2) ≤ ε / 2 := by
      rw [hε']
      have : 0 < 2 * ((1 + max Cb 0) / 2 + 1) := by positivity
      rw [div_mul_eq_mul_div, div_le_iff₀ this]
      nlinarith [le_max_right Cb 0]
    rw [Real.dist_eq]
    have e : (∫ x in unitCube, u τ x * perX (fun x => ρ (X t₁ x τ)) x) -
        ∫ x in unitCube, u s₀ x * perX (fun x => ρ (X t₁ x s₀)) x =
        (∫ x in unitCube, u τ x * (perX (fun x => ρ (X t₁ x τ)) x -
          perX (fun x => ρ (X t₁ x s₀)) x)) +
        ((∫ x in unitCube, u τ x * perX (fun x => ρ (X t₁ x s₀)) x) -
          ∫ x in unitCube, u s₀ x * perX (fun x => ρ (X t₁ x s₀)) x) := by
      rw [← hsplit]; ring
    rw [e]
    calc _ ≤ |∫ x in unitCube, u τ x * (perX (fun x => ρ (X t₁ x τ)) x -
          perX (fun x => ρ (X t₁ x s₀)) x)| + |(∫ x in unitCube, u τ x *
          perX (fun x => ρ (X t₁ x s₀)) x) - ∫ x in unitCube, u s₀ x *
          perX (fun x => ρ (X t₁ x s₀)) x| := abs_add_le _ _
      _ < ε := by linarith
  · -- the value at the initial time
    have h1 := pullback_pairing hφ hX hρ hρc s₀ t₁ (hslice s₀ hs₀).1 (hslice s₀ hs₀).2
    have h2 := pullback_pairing hφ hX hρ hρc s₀ t₁ hfp hf
    rw [h1, h2]
    exact initial_pairing hse hu (hψs s₀) (perX_periodic _)

end
end

/-! # The datum `f = (per v₀) ∘ F_{s₀}⁻¹`

For `v₀ ∈ L²(ℝ²)` vanishing outside the sup-ball of radius `1/4`, the periodization `per v₀` is
square integrable on the cell with `‖per v₀‖² ≤ 625 ‖v₀‖²`, equals `v₀` on the ball `|y| < 1/8`,
and the datum `f = per v₀ ∘ F_{s₀}⁻¹` has the same properties on the torus. -/

section
open AVRegularity.Applications

section Per

variable {v : Vec 2 → ℝ}

theorem perX_eq_sum_cube (hv : ∀ y, v y ≠ 0 → ‖y‖ ≤ 1 / 4) {x : Vec 2} (hx : ‖x‖ ≤ 1) :
    perX v x = ∑ n ∈ latBox 2, v (x + latticeShift n) := by
  unfold perX
  rw [perST_eq_sum (R := 1 / 4) (r := 1) (M := 2) (by norm_num)
    (fun t y hne => hv y hne) 0 hx]

theorem perX_eq_self (hv : ∀ y, v y ≠ 0 → ‖y‖ ≤ 1 / 4) {y : Vec 2} (hy : ‖y‖ ≤ 1 / 8) :
    perX v y = v y := by
  unfold perX perST
  rw [finsum_eq_single _ (0 : Fin 2 → ℤ)]
  · have h00 : latticeShift (0 : Fin 2 → ℤ) = 0 := by funext i; simp [latticeShift]
    simp [h00]
  · intro n hn
    by_contra hne
    have h1 := hv _ hne
    apply hn
    by_contra hn0
    obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hn0 (funext hall)
    have h2 : |(y + latticeShift n) i| ≤ 1 / 4 := (norm_le_pi_norm _ i).trans h1
    have h3 : |y i| ≤ 1 / 8 := (norm_le_pi_norm y i).trans hy
    simp only [Pi.add_apply, latticeShift] at h2
    have h4 : (1 : ℝ) ≤ |(n i : ℝ)| := by
      have : (1 : ℤ) ≤ |n i| := Int.one_le_abs hi
      exact_mod_cast this
    have h5 : |(n i : ℝ)| ≤ |y i + n i| + |y i| := by
      calc |(n i : ℝ)| = |(y i + n i) - y i| := by ring_nf
        _ ≤ _ := abs_sub _ _
    linarith

theorem sq_sum_le_card {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    (∑ i ∈ s, a i) ^ 2 ≤ s.card * ∑ i ∈ s, a i ^ 2 := by
  have := sq_sum_le_card_mul_sum_sq (s := s) (f := a)
  simpa using this



theorem perX_l2 (hv : ∀ y, v y ≠ 0 → ‖y‖ ≤ 1 / 4) (hv2 : MemLp v 2 volume) :
    MemL2On unitCube (perX v) ∧ l2NormSq (perX v) ≤ 625 * ∫ y, v y ^ 2 := by
  have hshift : ∀ n : Fin 2 → ℤ, MemLp (fun x => v (x + latticeShift n)) 2 volume := fun n =>
    hv2.comp_measurePreserving (measurePreserving_add_right volume (latticeShift n))
  have hsum : MemLp (fun x => ∑ n ∈ latBox 2, v (x + latticeShift n)) 2 volume := by
    exact memLp_finsetSum (latBox 2) (fun n _ => hshift n)
  have hae : perX v =ᵐ[volume.restrict unitCube] fun x => ∑ n ∈ latBox 2, v (x + latticeShift n) := by
    filter_upwards [ae_restrict_mem measurableSet_unitCube'] with x hx
    exact perX_eq_sum_cube hv (norm_le_one_of_mem_unitCube hx)
  have hmem : MemLp (perX v) 2 (volume.restrict unitCube) :=
    (hsum.restrict unitCube).ae_eq hae.symm
  refine ⟨hmem, ?_⟩
  have hsqint : ∀ n : Fin 2 → ℤ, Integrable (fun x => v (x + latticeShift n) ^ 2) volume :=
    fun n => (hshift n).integrable_sq
  have hcell : ∀ n : Fin 2 → ℤ, ∫ x in unitCube, v (x + latticeShift n) ^ 2 ≤ ∫ y, v y ^ 2 := by
    intro n
    calc ∫ x in unitCube, v (x + latticeShift n) ^ 2 ≤ ∫ x, v (x + latticeShift n) ^ 2 :=
          setIntegral_le_integral (hsqint n) (Filter.Eventually.of_forall fun x => sq_nonneg _)
      _ = ∫ y, v y ^ 2 := integral_add_right_eq_self (fun y => v y ^ 2) (latticeShift n)
  unfold l2NormSq
  have hc1 : ∫ x in unitCube, perX v x ^ 2 =
      ∫ x in unitCube, (∑ n ∈ latBox 2, v (x + latticeShift n)) ^ 2 :=
    integral_congr_ae (hae.mono fun x hx => by simp only [hx])
  rw [hc1]
  have hcard : (latBox 2).card = 25 := by simp [latBox, Fintype.card_piFinset]
  have hRint : Integrable (fun x => ∑ n ∈ latBox 2, v (x + latticeShift n) ^ 2)
      (volume.restrict unitCube) :=
    integrable_finsetSum _ fun n _ => (hsqint n).integrableOn
  calc ∫ x in unitCube, (∑ n ∈ latBox 2, v (x + latticeShift n)) ^ 2
      ≤ ∫ x in unitCube, 25 * ∑ n ∈ latBox 2, v (x + latticeShift n) ^ 2 := by
        refine integral_mono hsum.integrable_sq.restrict (hRint.const_mul 25) fun x => ?_
        have := sq_sum_le_card (latBox 2) (fun n => v (x + latticeShift n))
        simpa [hcard] using this
    _ = 25 * ∑ n ∈ latBox 2, ∫ x in unitCube, v (x + latticeShift n) ^ 2 := by
        rw [integral_const_mul, integral_finsetSum _ fun n _ => (hsqint n).integrableOn]
    _ ≤ 25 * ∑ n ∈ latBox 2, ∫ y, v y ^ 2 := by
        gcongr with n hn
        exact hcell n
    _ = 625 * ∫ y, v y ^ 2 := by
        rw [Finset.sum_const, hcard]; simp; ring

end Per

/-- The datum `f = (per v) ∘ F_{s₀}⁻¹`. -/
def datumFun (X : ℝ → Vec 2 → ℝ → Vec 2) (t₁ s₀ : ℝ) (v : Vec 2 → ℝ) : Vec 2 → ℝ :=
  fun x => perX v (X t₁ x s₀)

section Datum

variable {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) {X : ℝ → Vec 2 → ℝ → Vec 2}
  (hX : IsFlow (streamVel φ) X) {v : Vec 2 → ℝ}

include hφ hX

theorem datum_periodic (t₁ s₀ : ℝ) : IsZ2Periodic (datumFun X t₁ s₀ v) := fun k x => by
  simp only [datumFun, X_lattice hφ hX t₁ s₀ x k, perX_periodic v k]

theorem datum_apply (t₁ s₀ : ℝ) (y : Vec 2) : datumFun X t₁ s₀ v (X s₀ y t₁) = perX v y := by
  simp [datumFun, X_left hφ hX s₀ t₁ y]

theorem datum_l2 (t₁ s₀ : ℝ) (hv : ∀ y, v y ≠ 0 → ‖y‖ ≤ 1 / 4) (hv2 : MemLp v 2 volume) :
    MemL2On unitCube (datumFun X t₁ s₀ v) ∧
      l2NormSq (datumFun X t₁ s₀ v) ≤ 625 * ∫ y, v y ^ 2 := by
  obtain ⟨h1, h2⟩ := perX_l2 hv hv2
  refine ⟨X_cell_memL2 hφ hX t₁ s₀ (perX_periodic v) h1, ?_⟩
  unfold l2NormSq at h2 ⊢
  have := X_cell_integral hφ hX t₁ s₀ (u := fun x => perX v x ^ 2) (fun k x => by
    simp [perX_periodic v k x])
  simp only [datumFun]
  rw [this]
  exact h2

end Datum
end

end AVRegularity.Applications.Davies
end

section
open MeasureTheory Homogenization Filter Topology
namespace AVRegularity.Applications.Davies

/-! # Identification of the initial trace of the localized difference

The trace `W(s₀)` of `ζ θ χ (U - U_f)` equals `ζ (1 - χ) v₀` where `v₀` is the initial trace of
`χ U`: the weak initial attainment of `U_f` gives `χ U_f(s₀) = χ v₀`. -/

open AVRegularity.Applications

theorem pair_continuousOn {μ : Measure (Vec 2)} {S : Set ℝ} {W : ℝ → Lp ℝ 2 μ}
    (hW : ContinuousOn W S) {ρ : Vec 2 → ℝ} (hρ : MemLp ρ 2 μ) :
    ContinuousOn (fun τ => ∫ x, (W τ : Vec 2 → ℝ) x * ρ x ∂μ) S := by
  have : (fun τ => ∫ x, (W τ : Vec 2 → ℝ) x * ρ x ∂μ) =
      fun τ => inner ℝ (hρ.toLp ρ) (W τ) := funext fun τ => integral_mul_lp_eq_inner (W τ) hρ
  rw [this]
  exact continuousOn_const.inner hW

theorem memLp_two_of_isSpTest {R : ℝ} {ρ : Vec 2 → ℝ} (hρ : IsSpTest (euclidBall 0 R) ρ) :
    MemLp ρ 2 (volume.restrict (euclidBall 0 R)) := by
  have hc : Continuous ρ := hρ.1.continuous
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hρ.2.1
  have hfin : IsFiniteMeasure (volume.restrict (euclidBall (0 : Vec 2) R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact pipe_volume_euclidBall_lt_top R⟩
  exact MemLp.of_bound hc.aestronglyMeasurable C (Filter.Eventually.of_forall hC)


theorem isSpTest_mul' {B : Set (Vec 2)} {a ρ : Vec 2 → ℝ} (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hρ : IsSpTest B ρ) : IsSpTest B (fun y => a y * ρ y) :=
  ⟨ha.mul hρ.1, hρ.2.1.mul_left, (tsupport_mul_subset_right).trans hρ.2.2⟩

theorem trace_init_ident {R s₀ t₁ Λ : ℝ} (hs : s₀ < t₁) {U Uf : ℝ × Vec 2 → ℝ}
    (hU : MemLp U 2 (volume.restrict (Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R)))
    (hUf : MemLp Uf 2 (volume.restrict (Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R)))
    {χ ζ : Vec 2 → ℝ} (hχ : IsSpTest (euclidBall 0 R) χ) (hζ : IsSpTest (euclidBall 0 R) ζ)
    {W Wχ : ℝ → Lp ℝ 2 (volume.restrict (euclidBall 0 R))}
    (hWc : ContinuousOn W (Set.Icc s₀ t₁)) (hWχc : ContinuousOn Wχ (Set.Icc s₀ t₁))
    (hWae : ∀ᵐ τ ∂(volume.restrict (Set.Ioo s₀ t₁)),
      (W τ : Vec 2 → ℝ) =ᵐ[volume.restrict (euclidBall 0 R)]
        fun y => ζ y * Zt Λ s₀ χ (fun p => U p - Uf p) (τ, y))
    (hWχae : ∀ᵐ τ ∂(volume.restrict (Set.Ioo s₀ t₁)),
      (Wχ τ : Vec 2 → ℝ) =ᵐ[volume.restrict (euclidBall 0 R)] fun y => χ y * U (τ, y))
    {v₀ : Vec 2 → ℝ} (hv₀ : v₀ =ᵐ[volume.restrict (euclidBall 0 R)] (Wχ s₀ : Vec 2 → ℝ))
    (hinit : ∀ ρ : Vec 2 → ℝ, IsSpTest (euclidBall 0 R) ρ →
      ContinuousWithinAt (fun τ => ∫ y in euclidBall 0 R, Uf (τ, y) * ρ y) (Set.Icc s₀ t₁) s₀ ∧
        ∫ y in euclidBall 0 R, Uf (s₀, y) * ρ y = ∫ y in euclidBall 0 R, v₀ y * ρ y) :
    (W s₀ : Vec 2 → ℝ) =ᵐ[volume.restrict (euclidBall 0 R)]
      fun y => ζ y * ((1 - χ y) * v₀ y) := by
  have hBo : IsOpen (euclidBall (0 : Vec 2) R) := pipe_isOpen_euclidBall 0 R
  have hBm : MeasurableSet (euclidBall (0 : Vec 2) R) := hBo.measurableSet
  have hfin : IsFiniteMeasure (volume.restrict (euclidBall (0 : Vec 2) R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact pipe_volume_euclidBall_lt_top R⟩
  have hs0 : s₀ ∈ Set.Icc s₀ t₁ := ⟨le_rfl, hs.le⟩
  have hne : (𝓝[Set.Ioo s₀ t₁] s₀ ⊓ ae (volume : Measure ℝ)).NeBot := nhdsIoo_ae_neBot hs hs0
  have hFl1 : 𝓝[Set.Ioo s₀ t₁] s₀ ⊓ ae (volume : Measure ℝ) ≤ 𝓝[Set.Icc s₀ t₁] s₀ :=
    inf_le_left.trans (nhdsWithin_mono _ Set.Ioo_subset_Icc_self)
  have hFl2 : 𝓝[Set.Ioo s₀ t₁] s₀ ⊓ ae (volume : Measure ℝ) ≤ 𝓝 s₀ :=
    inf_le_left.trans nhdsWithin_le_nhds
  have hmemFl : ∀ᶠ τ in 𝓝[Set.Ioo s₀ t₁] s₀ ⊓ ae (volume : Measure ℝ), τ ∈ Set.Ioo s₀ t₁ :=
    (eventually_mem_nhdsWithin).filter_mono inf_le_left
  have hUs := ae_slice_memLp_gen hU
  have hUfs := ae_slice_memLp_gen hUf
  have aeFl : ∀ {P : ℝ → Prop}, (∀ᵐ τ ∂(volume.restrict (Set.Ioo s₀ t₁)), P τ) →
      ∀ᶠ τ in 𝓝[Set.Ioo s₀ t₁] s₀ ⊓ ae (volume : Measure ℝ), P τ := by
    intro P hP
    have h1 := (ae_restrict_iff' measurableSet_Ioo).1 hP
    have h2 : ∀ᶠ τ in ae (volume : Measure ℝ), τ ∈ Set.Ioo s₀ t₁ → P τ := h1
    have h3 : ∀ᶠ τ in 𝓝[Set.Ioo s₀ t₁] s₀ ⊓ ae (volume : Measure ℝ), τ ∈ Set.Ioo s₀ t₁ → P τ :=
      Filter.Eventually.filter_mono inf_le_right h2
    filter_upwards [h3, hmemFl] with τ h4 h5 using h4 h5
  have key : ∀ ρ : Vec 2 → ℝ, IsSpTest (euclidBall (0 : Vec 2) R) ρ →
      ∫ y in euclidBall (0 : Vec 2) R, (W s₀ : Vec 2 → ℝ) y * ρ y =
        ∫ y in euclidBall (0 : Vec 2) R, (ζ y * ((1 - χ y) * v₀ y)) * ρ y := by
    intro ρ hρ
    have hζρ : IsSpTest (euclidBall (0 : Vec 2) R) (fun y => ζ y * ρ y) := isSpTest_mul' hζ.1 hρ
    have hζχρ : IsSpTest (euclidBall (0 : Vec 2) R) (fun y => ζ y * (χ y * ρ y)) :=
      isSpTest_mul' hζ.1 (isSpTest_mul' hχ.1 hρ)
    have hρL := memLp_two_of_isSpTest hρ
    have hζρL := memLp_two_of_isSpTest hζρ
    have hat := ((pair_continuousOn hWc hρL) s₀ hs0).tendsto.mono_left hFl1
    have hbt := ((pair_continuousOn hWχc hζρL) s₀ hs0).tendsto.mono_left hFl1
    obtain ⟨hct, hcv⟩ := hinit _ hζχρ
    have hct' := hct.tendsto.mono_left hFl1
    have htw : Tendsto (fun τ => tw Λ s₀ τ) (𝓝[Set.Ioo s₀ t₁] s₀ ⊓ ae (volume : Measure ℝ))
        (𝓝 (tw Λ s₀ s₀)) := ((tw_contDiff Λ s₀).continuous.tendsto s₀).mono_left hFl2
    have htw1 : tw Λ s₀ s₀ = 1 := by simp [tw]
    have hlim := htw.mul (hbt.sub hct')
    have hev : ∀ᶠ τ in 𝓝[Set.Ioo s₀ t₁] s₀ ⊓ ae (volume : Measure ℝ),
        ∫ y in euclidBall (0 : Vec 2) R, (W τ : Vec 2 → ℝ) y * ρ y =
        tw Λ s₀ τ * ((∫ y in euclidBall (0 : Vec 2) R, (Wχ τ : Vec 2 → ℝ) y * (ζ y * ρ y)) -
          ∫ y in euclidBall (0 : Vec 2) R, Uf (τ, y) * (ζ y * (χ y * ρ y))) := by
      filter_upwards [aeFl hWae, aeFl hWχae, aeFl hUs, aeFl hUfs] with τ h1 h2 h3 h4
      have i1 : IntegrableOn (fun y => U (τ, y) * (χ y * (ζ y * ρ y)))
          (euclidBall (0 : Vec 2) R) volume :=
        integrableOn_mul_cpt h3 (hχ.1.continuous.mul hζρ.1.continuous) (hζρ.2.1.mul_left)
      have i2 : IntegrableOn (fun y => Uf (τ, y) * (ζ y * (χ y * ρ y)))
          (euclidBall (0 : Vec 2) R) volume :=
        integrableOn_mul_cpt h4 hζχρ.1.continuous hζχρ.2.1
      have e1 : ∫ y in euclidBall (0 : Vec 2) R, (W τ : Vec 2 → ℝ) y * ρ y =
          ∫ y in euclidBall (0 : Vec 2) R,
            ζ y * (tw Λ s₀ τ * (χ y * (U (τ, y) - Uf (τ, y)))) * ρ y :=
        integral_congr_ae (h1.mono fun y hy => by
          simp only [Zt] at hy
          show (W τ : Vec 2 → ℝ) y * ρ y = _
          rw [hy])
      have e2 : ∫ y in euclidBall (0 : Vec 2) R, (Wχ τ : Vec 2 → ℝ) y * (ζ y * ρ y) =
          ∫ y in euclidBall (0 : Vec 2) R, U (τ, y) * (χ y * (ζ y * ρ y)) :=
        integral_congr_ae (h2.mono fun y hy => by
          show (Wχ τ : Vec 2 → ℝ) y * (ζ y * ρ y) = _
          rw [hy]; ring)
      rw [e1, e2, ← integral_sub i1 i2, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      show _ = tw Λ s₀ τ * _
      ring
    have hlim' : Tendsto (fun τ => ∫ y in euclidBall (0 : Vec 2) R, (W τ : Vec 2 → ℝ) y * ρ y)
        (𝓝[Set.Ioo s₀ t₁] s₀ ⊓ ae (volume : Measure ℝ))
        (𝓝 (tw Λ s₀ s₀ * ((∫ y in euclidBall (0 : Vec 2) R, (Wχ s₀ : Vec 2 → ℝ) y * (ζ y * ρ y)) -
          ∫ y in euclidBall (0 : Vec 2) R, Uf (s₀, y) * (ζ y * (χ y * ρ y))))) :=
      hlim.congr' (hev.mono fun τ h => h.symm)
    have hu := tendsto_nhds_unique hat hlim'
    rw [hu, htw1, hcv]
    have e3 : ∫ y in euclidBall (0 : Vec 2) R, (Wχ s₀ : Vec 2 → ℝ) y * (ζ y * ρ y) =
        ∫ y in euclidBall (0 : Vec 2) R, v₀ y * (ζ y * ρ y) :=
      integral_congr_ae (hv₀.mono fun y hy => by
        show (Wχ s₀ : Vec 2 → ℝ) y * (ζ y * ρ y) = v₀ y * (ζ y * ρ y)
        rw [← hy])
    rw [e3]
    have i3 : IntegrableOn (fun y => v₀ y * (ζ y * ρ y)) (euclidBall (0 : Vec 2) R) volume :=
      integrableOn_mul_cpt ((Lp.memLp (Wχ s₀)).ae_eq hv₀.symm) hζρ.1.continuous hζρ.2.1
    have i4 : IntegrableOn (fun y => v₀ y * (ζ y * (χ y * ρ y))) (euclidBall (0 : Vec 2) R)
        volume :=
      integrableOn_mul_cpt ((Lp.memLp (Wχ s₀)).ae_eq hv₀.symm) hζχρ.1.continuous hζχρ.2.1
    rw [one_mul, ← integral_sub i3 i4]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show _ = ζ y * ((1 - χ y) * v₀ y) * ρ y
    ring
  -- conclude by the fundamental lemma
  have hv₀L : MemLp v₀ 2 (volume.restrict (euclidBall (0 : Vec 2) R)) :=
    (Lp.memLp (Wχ s₀)).ae_eq hv₀.symm
  have hcoef : Continuous fun y => ζ y * (1 - χ y) := hζ.1.continuous.mul
    (continuous_const.sub hχ.1.continuous)
  have hcoefc : HasCompactSupport fun y => ζ y * (1 - χ y) := by
    refine HasCompactSupport.intro hζ.2.1 (fun y hy => ?_)
    have : ζ y = 0 := image_eq_zero_of_notMem_tsupport hy
    simp [this]
  obtain ⟨Cc, hCc⟩ := hcoef.bounded_above_of_compact_support hcoefc
  have hgL : MemLp (fun y => ζ y * ((1 - χ y) * v₀ y)) 2
      (volume.restrict (euclidBall (0 : Vec 2) R)) :=
    ((memLp_two_mul_bdd hcoef.aestronglyMeasurable (C := Cc)
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hCc y) hv₀L)).ae_eq
      (Filter.Eventually.of_forall fun y => by simp only [mul_assoc])
  have hdiff : MemLp (fun y => (W s₀ : Vec 2 → ℝ) y - ζ y * ((1 - χ y) * v₀ y)) 2
      (volume.restrict (euclidBall (0 : Vec 2) R)) := (Lp.memLp (W s₀)).sub hgL
  have hli : IntegrableOn (fun y => (W s₀ : Vec 2 → ℝ) y - ζ y * ((1 - χ y) * v₀ y))
      (euclidBall (0 : Vec 2) R) volume := hdiff.integrable (by norm_num)
  have hz := hBo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (f := fun y => (W s₀ : Vec 2 → ℝ) y - ζ y * ((1 - χ y) * v₀ y)) (μ := volume)
    hli.locallyIntegrableOn (fun g hgs hgc hgsub => by
      have hg : IsSpTest (euclidBall (0 : Vec 2) R) g := ⟨hgs, hgc, hgsub⟩
      have hgL' := memLp_two_of_isSpTest hg
      have e0 : ∫ x, g x • ((W s₀ : Vec 2 → ℝ) x - ζ x * ((1 - χ x) * v₀ x)) =
          ∫ x in euclidBall (0 : Vec 2) R, g x • ((W s₀ : Vec 2 → ℝ) x -
            ζ x * ((1 - χ x) * v₀ x)) :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
          have : x ∉ tsupport g := fun h => hgsub h |> hx
          simp [image_eq_zero_of_notMem_tsupport this]).symm
      rw [e0]
      simp only [smul_eq_mul]
      have iw : IntegrableOn (fun x => (W s₀ : Vec 2 → ℝ) x * g x) (euclidBall (0 : Vec 2) R)
          volume := integrableOn_mul_cpt (Lp.memLp (W s₀)) hgs.continuous hgc
      have ig : IntegrableOn (fun x => (ζ x * ((1 - χ x) * v₀ x)) * g x)
          (euclidBall (0 : Vec 2) R) volume := integrableOn_mul_cpt hgL hgs.continuous hgc
      have := key g hg
      calc ∫ x in euclidBall (0 : Vec 2) R, g x * ((W s₀ : Vec 2 → ℝ) x -
            ζ x * ((1 - χ x) * v₀ x)) =
          (∫ x in euclidBall (0 : Vec 2) R, (W s₀ : Vec 2 → ℝ) x * g x) -
            ∫ x in euclidBall (0 : Vec 2) R, (ζ x * ((1 - χ x) * v₀ x)) * g x := by
            rw [← integral_sub iw ig]
            refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
            show _ = _
            ring
        _ = 0 := by rw [this]; ring)
  rw [Filter.EventuallyEq, ae_restrict_iff' hBm]
  filter_upwards [hz] with y hy hyB
  have := hy hyB
  exact sub_eq_zero.1 this

end AVRegularity.Applications.Davies
end

section
open MeasureTheory Homogenization Matrix
namespace AVRegularity.Applications.Davies

/-! # Pointwise bounds for the localization sources

`H = -κ D G∇χ` and `g' = κ ∇χ·G∇D - D V·∇χ` are controlled by `|∇χ| ≤ N`, `D` and the
energies of the two solutions, and they vanish unless `∇χ ≠ 0`, where `ψ = -a` and `η = 1`. -/

theorem srcG_alg {G : Matrix (Fin 2) (Fin 2) ℝ} {V g a b : Vec 2} {κ N V₀ D : ℝ}
    (hs : Gᵀ = G) (hell : ∀ x, (1 / 4) * vecNormSq x ≤ vecDot x (G.mulVec x))
    (hbdd : ∀ x, vecNormSq (G.mulVec x) ≤ (9 / 4) ^ 2 * vecNormSq x)
    (hg : vecNormSq g ≤ N ^ 2) (hV : vecNormSq V ≤ V₀ ^ 2) :
    (κ * vecDot g (G.mulVec (a - b)) - D * vecDot V g) ^ 2 ≤
      9 * κ ^ 2 * N ^ 2 * (vecDot a (G.mulVec a) + 9 / 4 * vecNormSq b) +
        2 * V₀ ^ 2 * N ^ 2 * D ^ 2 := by
  have hpsd : ∀ x, 0 ≤ vecDot x (G.mulVec x) := fun x => by
    have := hell x; have := vecNormSq_nonneg x; linarith
  set s := vecDot g (G.mulVec (a - b)) with hsd
  have hs2 : s ^ 2 ≤ vecDot g (G.mulVec g) * vecDot (a - b) (G.mulVec (a - b)) :=
    cauchy_symm hs hpsd g (a - b)
  have hgg : vecDot g (G.mulVec g) ≤ 9 / 4 * N ^ 2 := by
    have := quad_le_gen hbdd g
    nlinarith
  have hsum : vecDot (a - b) (G.mulVec (a - b)) ≤
      2 * vecDot a (G.mulVec a) + 2 * vecDot b (G.mulVec b) := by
    have h1 := hpsd (a + b)
    have e : vecDot (a - b) (G.mulVec (a - b)) + vecDot (a + b) (G.mulVec (a + b)) =
        2 * vecDot a (G.mulVec a) + 2 * vecDot b (G.mulVec b) := by
      simp only [vecDot, Fin.sum_univ_two, Matrix.mulVec_sub, Matrix.mulVec_add, Pi.sub_apply,
        Pi.add_apply]
      ring
    linarith
  have hbb : vecDot b (G.mulVec b) ≤ 9 / 4 * vecNormSq b := quad_le_gen hbdd b
  have hw : vecDot V g ^ 2 ≤ V₀ ^ 2 * N ^ 2 := by
    have := vecDot_sq_le V g
    have h2 : vecNormSq V * vecNormSq g ≤ V₀ ^ 2 * N ^ 2 :=
      mul_le_mul hV hg (vecNormSq_nonneg g) (sq_nonneg _)
    linarith
  have hq0 := hpsd (a - b)
  have hs3 : s ^ 2 ≤ 9 / 4 * N ^ 2 * (2 * vecDot a (G.mulVec a) + 9 / 2 * vecNormSq b) := by
    calc s ^ 2 ≤ vecDot g (G.mulVec g) * vecDot (a - b) (G.mulVec (a - b)) := hs2
      _ ≤ (9 / 4 * N ^ 2) * vecDot (a - b) (G.mulVec (a - b)) :=
          mul_le_mul_of_nonneg_right hgg hq0
      _ ≤ (9 / 4 * N ^ 2) * (2 * vecDot a (G.mulVec a) + 9 / 2 * vecNormSq b) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
  have hexp : (κ * s - D * vecDot V g) ^ 2 ≤ 2 * κ ^ 2 * s ^ 2 + 2 * D ^ 2 * vecDot V g ^ 2 := by
    nlinarith [sq_nonneg (κ * s + D * vecDot V g)]
  have h4 : 2 * κ ^ 2 * s ^ 2 ≤ 2 * κ ^ 2 * (9 / 4 * N ^ 2 *
      (2 * vecDot a (G.mulVec a) + 9 / 2 * vecNormSq b)) :=
    mul_le_mul_of_nonneg_left hs3 (by positivity)
  have h5 : 2 * D ^ 2 * vecDot V g ^ 2 ≤ 2 * D ^ 2 * (V₀ ^ 2 * N ^ 2) :=
    mul_le_mul_of_nonneg_left hw (by positivity)
  nlinarith [h4, h5, hexp]

theorem srcH_alg {G : Matrix (Fin 2) (Fin 2) ℝ} {g : Vec 2} {κ N D : ℝ}
    (hbdd : ∀ x, vecNormSq (G.mulVec x) ≤ (9 / 4) ^ 2 * vecNormSq x)
    (hg : vecNormSq g ≤ N ^ 2) :
    vecNormSq ((-(κ * D)) • G.mulVec g) ≤ κ ^ 2 * (81 / 16) * N ^ 2 * D ^ 2 := by
  rw [vecNormSq_smul]
  have h := hbdd g
  have h2 : vecNormSq (G.mulVec g) ≤ (9 / 4) ^ 2 * N ^ 2 :=
    h.trans (mul_le_mul_of_nonneg_left hg (by norm_num))
  have : (-(κ * D)) ^ 2 * vecNormSq (G.mulVec g) ≤ (κ * D) ^ 2 * ((9 / 4) ^ 2 * N ^ 2) := by
    rw [neg_sq]
    exact mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  nlinarith


variable {G : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {V : ℝ × Vec 2 → Vec 2} {V₀ ta tb : ℝ}

theorem source_pointwise (hc : LabelCoeffs G V V₀ ta tb) {κ lam ℓ ca R N : ℝ} (hκ : 0 < κ)
    (hlam : 0 < lam) {χ η ψ : Vec 2 → ℝ} (hχN : ∀ y, vecNormSq (spGrad χ y) ≤ N ^ 2)
    (hsrc : ∀ y, spGrad χ y ≠ 0 → ψ y = -(ca * R) ∧ η y = 1)
    {D : ℝ × Vec 2 → ℝ} {DU DUf : ℝ × Vec 2 → Vec 2} {p : ℝ × Vec 2}
    (hp : p.1 ∈ Set.Icc ta tb) :
    zeta ℓ ψ η p.2 ^ 2 * (18 / κ * vecNormSq (srcH κ G χ D p) +
        srcG κ G V χ D (fun q => DU q - DUf q) p ^ 2 / lam) ≤
      Real.exp (-(2 * ℓ * (ca * R))) *
        ((729 / 8 * κ * N ^ 2 + (1 / lam) * (2 * V₀ ^ 2 * N ^ 2)) * (η p.2 ^ 2 * D p ^ 2) +
          (1 / lam) * (9 * κ ^ 2 * N ^ 2) *
            (η p.2 ^ 2 * vecDot (DU p) ((G p).mulVec (DU p)) + 9 / 4 * vecNormSq (DUf p))) := by
  have hQ := hc.psd hp (DU p)
  have hnn : 0 ≤ Real.exp (-(2 * ℓ * (ca * R))) *
        ((729 / 8 * κ * N ^ 2 + (1 / lam) * (2 * V₀ ^ 2 * N ^ 2)) * (η p.2 ^ 2 * D p ^ 2) +
          (1 / lam) * (9 * κ ^ 2 * N ^ 2) *
            (η p.2 ^ 2 * vecDot (DU p) ((G p).mulVec (DU p)) + 9 / 4 * vecNormSq (DUf p))) := by
    have := vecNormSq_nonneg (DUf p)
    positivity
  by_cases hg : spGrad χ p.2 = 0
  · have hH : srcH κ G χ D p = 0 := by simp [srcH, hg]
    have hG : srcG κ G V χ D (fun q => DU q - DUf q) p = 0 := by simp [srcG, hg, vecDot]
    have h00 : vecNormSq (0 : Vec 2) = 0 := by simp [vecNormSq, vecDot]
    rw [hH, hG, h00]
    simpa using hnn
  · obtain ⟨hψ, hη⟩ := hsrc _ hg
    have hz : zeta ℓ ψ η p.2 ^ 2 = Real.exp (-(2 * ℓ * (ca * R))) := by
      simp only [zeta, hψ, hη, mul_one]
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [hz, hη]
    have hH := srcH_alg (G := G p) (g := spGrad χ p.2) (κ := κ) (N := N) (D := D p)
      (hc.bdd p hp) (hχN _)
    have hG := srcG_alg (G := G p) (V := V p) (g := spGrad χ p.2) (a := DU p) (b := DUf p)
      (κ := κ) (N := N) (V₀ := V₀) (D := D p) (hc.symm p) (hc.ell p hp) (hc.bdd p hp)
      (hχN _) (hc.Vbd p hp)
    have hH' : 18 / κ * vecNormSq (srcH κ G χ D p) ≤ 729 / 8 * κ * N ^ 2 * D p ^ 2 := by
      have e : vecNormSq (srcH κ G χ D p) ≤ κ ^ 2 * (81 / 16) * N ^ 2 * D p ^ 2 := hH
      calc 18 / κ * vecNormSq (srcH κ G χ D p) ≤ 18 / κ * (κ ^ 2 * (81 / 16) * N ^ 2 * D p ^ 2) :=
            mul_le_mul_of_nonneg_left e (by positivity)
        _ = 729 / 8 * κ * N ^ 2 * D p ^ 2 := by field_simp; ring
    have hG' : srcG κ G V χ D (fun q => DU q - DUf q) p ^ 2 / lam ≤
        (1 / lam) * (9 * κ ^ 2 * N ^ 2 * (vecDot (DU p) ((G p).mulVec (DU p)) +
          9 / 4 * vecNormSq (DUf p)) + 2 * V₀ ^ 2 * N ^ 2 * D p ^ 2) := by
      rw [div_eq_inv_mul, one_div]
      exact mul_le_mul_of_nonneg_left hG (by positivity)
    simp only [one_pow, one_mul]
    calc Real.exp (-(2 * ℓ * (ca * R))) * (18 / κ * vecNormSq (srcH κ G χ D p) +
          srcG κ G V χ D (fun q => DU q - DUf q) p ^ 2 / lam)
        ≤ Real.exp (-(2 * ℓ * (ca * R))) * (729 / 8 * κ * N ^ 2 * D p ^ 2 +
          (1 / lam) * (9 * κ ^ 2 * N ^ 2 * (vecDot (DU p) ((G p).mulVec (DU p)) +
          9 / 4 * vecNormSq (DUf p)) + 2 * V₀ ^ 2 * N ^ 2 * D p ^ 2)) :=
          mul_le_mul_of_nonneg_left (add_le_add hH' hG') (Real.exp_pos _).le
      _ = _ := by ring

end AVRegularity.Applications.Davies
end

section
open MeasureTheory Homogenization Matrix Filter Topology
namespace AVRegularity.Applications.Davies

/-! # The comparison estimate in label coordinates

For two solutions `U`, `U_f` of the label equation on `(s₀,t₁) × B_R` whose cut-off traces agree at
`s₀` up to the cutoff `χ`, the difference decays away from the sources:
`∫_{B_{R/8}} (U - U_f)(τ)² ≤ e^{2Λ(t₁-s₀)} e^{-2ℓ c_a R} (‖v₀‖² + S)`. This is the exponential
separation in the proof of Lemma 8.3 of the paper. -/

open AVRegularity.Applications

variable {G : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {V : ℝ × Vec 2 → Vec 2} {V₀ s₀ t₁ : ℝ}


/-- The source integral of the comparison estimate. -/
def srcBound (G : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (V₀ κ lam N s₀ t₁ R : ℝ)
    (η : Vec 2 → ℝ) (U Uf : ℝ × Vec 2 → ℝ) (DU DUf : ℝ × Vec 2 → Vec 2) : ℝ :=
  (729 / 8 * κ * N ^ 2 + (1 / lam) * (2 * V₀ ^ 2 * N ^ 2)) *
      (∫ p in Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R, η p.2 ^ 2 * (U p - Uf p) ^ 2) +
    (1 / lam) * (9 * κ ^ 2 * N ^ 2) *
      ((∫ p in Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R,
          η p.2 ^ 2 * vecDot (DU p) ((G p).mulVec (DU p))) +
        9 / 4 * ∫ p in Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R, vecNormSq (DUf p))

theorem compare_init_bound {R ℓ ca : ℝ} {χ η ψ : Vec 2 → ℝ} (hχ1 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (hη1 : ∀ y, 0 ≤ η y ∧ η y ≤ 1) (hP12 : ∀ y, χ y ≠ 1 → ψ y = -(ca * R))
    {W Wχ : Lp ℝ 2 (volume.restrict (euclidBall (0 : Vec 2) R))} {v₀ : Vec 2 → ℝ}
    (hv₀ : v₀ =ᵐ[volume.restrict (euclidBall (0 : Vec 2) R)] (Wχ : Vec 2 → ℝ))
    (hident : (W : Vec 2 → ℝ) =ᵐ[volume.restrict (euclidBall (0 : Vec 2) R)]
      fun y => zeta ℓ ψ η y * ((1 - χ y) * v₀ y)) :
    ‖W‖ ^ 2 ≤ Real.exp (-(2 * ℓ * (ca * R))) * ‖Wχ‖ ^ 2 := by
  have hv₀L : MemLp v₀ 2 (volume.restrict (euclidBall (0 : Vec 2) R)) :=
    (Lp.memLp Wχ).ae_eq hv₀.symm
  rw [← LocalEnergy.integral_sq_lp, ← LocalEnergy.integral_sq_lp]
  have e1 : ∫ y in euclidBall (0 : Vec 2) R, ((W : Vec 2 → ℝ) y) ^ 2 =
      ∫ y in euclidBall (0 : Vec 2) R, (zeta ℓ ψ η y * ((1 - χ y) * v₀ y)) ^ 2 :=
    integral_congr_ae (hident.mono fun y hy => by simp only [hy])
  have e2 : ∫ y in euclidBall (0 : Vec 2) R, ((Wχ : Vec 2 → ℝ) y) ^ 2 =
      ∫ y in euclidBall (0 : Vec 2) R, v₀ y ^ 2 :=
    integral_congr_ae (hv₀.mono fun y hy => by simp only [hy])
  rw [e1, e2, ← integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => sq_nonneg _)
    (hv₀L.integrable_sq.const_mul _) (Filter.Eventually.of_forall fun y => ?_)
  have hcoef : zeta ℓ ψ η y ^ 2 * (1 - χ y) ^ 2 ≤ Real.exp (-(2 * ℓ * (ca * R))) := by
    by_cases h1 : χ y = 1
    · rw [h1]; simp only [sub_self]; norm_num; exact (Real.exp_pos _).le
    · have hψy := hP12 y h1
      have hzy : zeta ℓ ψ η y ^ 2 = Real.exp (-(2 * ℓ * (ca * R))) * η y ^ 2 := by
        simp only [zeta, hψy]
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 2
        push_cast; ring
      rw [hzy]
      have h2 : η y ^ 2 ≤ 1 := by nlinarith [(hη1 y).1, (hη1 y).2]
      have h3 : (1 - χ y) ^ 2 ≤ 1 := by nlinarith [(hχ1 y).1, (hχ1 y).2]
      have h4 : 0 ≤ η y ^ 2 := sq_nonneg _
      have h5 : 0 ≤ (1 - χ y) ^ 2 := sq_nonneg _
      have h6 := Real.exp_pos (-(2 * ℓ * (ca * R)))
      calc Real.exp (-(2 * ℓ * (ca * R))) * η y ^ 2 * (1 - χ y) ^ 2
          ≤ Real.exp (-(2 * ℓ * (ca * R))) * 1 * 1 := by gcongr
        _ = _ := by ring
  calc (zeta ℓ ψ η y * ((1 - χ y) * v₀ y)) ^ 2
      = (zeta ℓ ψ η y ^ 2 * (1 - χ y) ^ 2) * v₀ y ^ 2 := by ring
    _ ≤ Real.exp (-(2 * ℓ * (ca * R))) * v₀ y ^ 2 :=
        mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)

theorem compare_source_bound (hc : LabelCoeffs G V V₀ s₀ t₁) {R κ lam ℓ ca N : ℝ}
    (hκ : 0 < κ) (hlam : 0 < lam)
    {U Uf : ℝ × Vec 2 → ℝ} {DU DUf : ℝ × Vec 2 → Vec 2}
    (hU : MemLp U 2 (volume.restrict (Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R)))
    (hUf : MemLp Uf 2 (volume.restrict (Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R)))
    (hDU : ∀ i : Fin 2,
      MemLp (fun p => DU p i) 2 (volume.restrict (Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R)))
    (hDUf : ∀ i : Fin 2,
      MemLp (fun p => DUf p i) 2 (volume.restrict (Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R)))
    {χ η ψ : Vec 2 → ℝ} (hη : IsSpTest (euclidBall 0 R) η) (hη1 : ∀ y, 0 ≤ η y ∧ η y ≤ 1)
    (hχN : ∀ y, vecNormSq (spGrad χ y) ≤ N ^ 2)
    (hP11 : ∀ y, spGrad χ y ≠ 0 → ψ y = -(ca * R) ∧ η y = 1) :
    ∫ p in Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R, zeta ℓ ψ η p.2 ^ 2 *
        (18 / κ * vecNormSq (srcH κ G χ (fun p => U p - Uf p) p) +
          srcG κ G V χ (fun p => U p - Uf p) (fun p => DU p - DUf p) p ^ 2 / lam) ≤
      Real.exp (-(2 * ℓ * (ca * R))) * srcBound G V₀ κ lam N s₀ t₁ R η U Uf DU DUf := by
  have hBm : MeasurableSet (euclidBall (0 : Vec 2) R) := (pipe_isOpen_euclidBall 0 R).measurableSet
  have hae := ae_mem_cyl (ta := s₀) (tb := t₁) hBm
  have hDm : MemLp (fun p => U p - Uf p) 2
      (volume.restrict (Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R)) := hU.sub hUf
  have hηc : Continuous fun p : ℝ × Vec 2 => η p.2 := hη.1.continuous.comp continuous_snd
  have hηD : MemLp (fun p => η p.2 * (U p - Uf p)) 2
      (volume.restrict (Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R)) :=
    memLp_two_mul_bdd hηc.aestronglyMeasurable (C := 1)
      (Filter.Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hη1 _).1]; exact (hη1 _).2) hDm
  have iD : Integrable (fun p => η p.2 ^ 2 * (U p - Uf p) ^ 2)
      (volume.restrict (Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R)) :=
    hηD.integrable_sq.congr (Filter.Eventually.of_forall fun p => by simp only [mul_pow])
  have hη1' : ∀ y, |η y| ≤ 1 := fun y => by rw [abs_of_nonneg (hη1 y).1]; exact (hη1 y).2
  have iQ := integrable_quad hc hDU hη hη1'
  have iDf : Integrable (fun p => vecNormSq (DUf p))
      (volume.restrict (Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R)) := by
    have := ((hDUf 0).integrable_sq).add ((hDUf 1).integrable_sq)
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [vecNormSq_two, sq, Pi.add_apply]
  have hgi : Integrable (fun p : ℝ × Vec 2 => Real.exp (-(2 * ℓ * (ca * R))) *
      ((729 / 8 * κ * N ^ 2 + (1 / lam) * (2 * V₀ ^ 2 * N ^ 2)) *
        (η p.2 ^ 2 * (U p - Uf p) ^ 2) +
      (1 / lam) * (9 * κ ^ 2 * N ^ 2) *
        (η p.2 ^ 2 * vecDot (DU p) ((G p).mulVec (DU p)) + 9 / 4 * vecNormSq (DUf p))))
      (volume.restrict (Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R)) :=
    ((iD.const_mul _).add ((iQ.add (iDf.const_mul (9 / 4))).const_mul _)).const_mul _
  have hmono := integral_mono_of_nonneg
    (μ := volume.restrict (Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R))
    (f := fun p : ℝ × Vec 2 => zeta ℓ ψ η p.2 ^ 2 *
        (18 / κ * vecNormSq (srcH κ G χ (fun p => U p - Uf p) p) +
          srcG κ G V χ (fun p => U p - Uf p) (fun p => DU p - DUf p) p ^ 2 / lam))
    (Filter.Eventually.of_forall fun p => by
      have := vecNormSq_nonneg (srcH κ G χ (fun p => U p - Uf p) p)
      positivity) hgi (by
      filter_upwards [hae] with p hp
      exact source_pointwise (ℓ := ℓ) (ca := ca) (R := R) (N := N) hc hκ hlam hχN hP11
        (D := fun p => U p - Uf p) (DU := DU) (DUf := DUf) hp)
  refine hmono.trans (le_of_eq ?_)
  have ic : Integrable (fun p : ℝ × Vec 2 => η p.2 ^ 2 * vecDot (DU p) ((G p).mulVec (DU p)) +
      9 / 4 * vecNormSq (DUf p)) (volume.restrict (Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R)) :=
    iQ.add (iDf.const_mul (9 / 4))
  have ia : Integrable (fun p : ℝ × Vec 2 => (729 / 8 * κ * N ^ 2 +
      (1 / lam) * (2 * V₀ ^ 2 * N ^ 2)) * (η p.2 ^ 2 * (U p - Uf p) ^ 2))
      (volume.restrict (Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R)) := iD.const_mul _
  have ib : Integrable (fun p : ℝ × Vec 2 => (1 / lam) * (9 * κ ^ 2 * N ^ 2) *
      (η p.2 ^ 2 * vecDot (DU p) ((G p).mulVec (DU p)) + 9 / 4 * vecNormSq (DUf p)))
      (volume.restrict (Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R)) := ic.const_mul _
  rw [integral_const_mul, integral_add ia ib, integral_const_mul, integral_const_mul,
    integral_add iQ (iDf.const_mul (9 / 4)), integral_const_mul]
  simp only [srcBound]


theorem compare_extract {R s₀ t₁ Λ ℓ Y : ℝ} (hΛ : 0 ≤ Λ) {U Uf : ℝ × Vec 2 → ℝ}
    {χ η ψ : Vec 2 → ℝ}
    (hP10 : ∀ y, vecNormSq y ≤ (R / 8) ^ 2 → ψ y = 0 ∧ χ y = 1 ∧ η y = 1)
    {W : ℝ → Lp ℝ 2 (volume.restrict (euclidBall (0 : Vec 2) R))}
    (hWae : ∀ᵐ τ ∂(volume.restrict (Set.Ioo s₀ t₁)),
      (W τ : Vec 2 → ℝ) =ᵐ[volume.restrict (euclidBall (0 : Vec 2) R)]
        fun y => zeta ℓ ψ η y * Zt Λ s₀ χ (fun p => U p - Uf p) (τ, y))
    (hUs : ∀ᵐ τ ∂(volume.restrict (Set.Ioo s₀ t₁)),
      MemLp (fun y => U (τ, y)) 2 (volume.restrict (euclidBall (0 : Vec 2) R)))
    (hUfs : ∀ᵐ τ ∂(volume.restrict (Set.Ioo s₀ t₁)),
      MemLp (fun y => Uf (τ, y)) 2 (volume.restrict (euclidBall (0 : Vec 2) R)))
    (hb0 : ∀ τ ∈ Set.Icc s₀ t₁, ‖W τ‖ ^ 2 ≤ Y) :
    ∀ᵐ τ ∂(volume.restrict (Set.Ioo s₀ t₁)),
      ∫ y in euclidBall (0 : Vec 2) (R / 8), (U (τ, y) - Uf (τ, y)) ^ 2 ≤
        Real.exp (2 * Λ * (t₁ - s₀)) * Y := by
  have hBm : MeasurableSet (euclidBall (0 : Vec 2) R) := (pipe_isOpen_euclidBall 0 R).measurableSet
  have hB'm : MeasurableSet (euclidBall (0 : Vec 2) (R / 8)) :=
    (pipe_isOpen_euclidBall 0 (R / 8)).measurableSet
  have hB' : euclidBall (0 : Vec 2) (R / 8) ⊆ euclidBall (0 : Vec 2) R := by
    intro y hy
    simp only [euclidBall, Set.mem_ofPred_eq, sub_zero] at hy ⊢
    nlinarith [sq_nonneg R]
  filter_upwards [hWae, hUs, hUfs, ae_restrict_mem measurableSet_Ioo] with τ h1 h2 h3 hτm
  have hτI : τ ∈ Set.Icc s₀ t₁ := ⟨hτm.1.le, hτm.2.le⟩
  have hDs : MemLp (fun y => U (τ, y) - Uf (τ, y)) 2 (volume.restrict (euclidBall (0 : Vec 2) R)) :=
    h2.sub h3
  have hWsq : ‖W τ‖ ^ 2 = ∫ y in euclidBall (0 : Vec 2) R,
      (zeta ℓ ψ η y * Zt Λ s₀ χ (fun p => U p - Uf p) (τ, y)) ^ 2 := by
    rw [← LocalEnergy.integral_sq_lp]
    exact integral_congr_ae (h1.mono fun y hy => by simp only [hy])
  have hint : Integrable (fun y => (zeta ℓ ψ η y * Zt Λ s₀ χ (fun p => U p - Uf p) (τ, y)) ^ 2)
      (volume.restrict (euclidBall (0 : Vec 2) R)) :=
    ((Lp.memLp (W τ)).integrable_sq).congr (h1.mono fun y hy => by simp only [hy])
  have h4 : ∫ y in euclidBall (0 : Vec 2) (R / 8),
      (zeta ℓ ψ η y * Zt Λ s₀ χ (fun p => U p - Uf p) (τ, y)) ^ 2 ≤ ‖W τ‖ ^ 2 := by
    rw [hWsq]
    exact setIntegral_mono_set hint (Filter.Eventually.of_forall fun y => sq_nonneg _)
      (Filter.Eventually.of_forall hB')
  have h5 : ∫ y in euclidBall (0 : Vec 2) (R / 8),
      (zeta ℓ ψ η y * Zt Λ s₀ χ (fun p => U p - Uf p) (τ, y)) ^ 2 =
      tw Λ s₀ τ ^ 2 * ∫ y in euclidBall (0 : Vec 2) (R / 8), (U (τ, y) - Uf (τ, y)) ^ 2 := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun hB'm fun y hy => ?_
    have hy' : vecNormSq y ≤ (R / 8) ^ 2 := by
      have : vecNormSq (y - 0) < (R / 8) ^ 2 := by simpa [euclidBall] using hy
      simpa using this.le
    obtain ⟨hψ0, hχ1, hη1⟩ := hP10 y hy'
    simp only [zeta, Zt, hψ0, hχ1, hη1, mul_zero, Real.exp_zero, one_mul, mul_one]
    ring
  have h6 : tw Λ s₀ τ ^ 2 * ∫ y in euclidBall (0 : Vec 2) (R / 8), (U (τ, y) - Uf (τ, y)) ^ 2 ≤
      Y := by
    rw [← h5]; exact h4.trans (hb0 τ hτI)
  have hY0 : 0 ≤ Y := (sq_nonneg _).trans (hb0 s₀ ⟨le_rfl, (hτm.1.trans hτm.2).le⟩)
  have h7 : Real.exp (2 * Λ * (τ - s₀)) * tw Λ s₀ τ ^ 2 = 1 := by
    simp only [tw]
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    simp only [Nat.cast_ofNat]
    rw [← Real.exp_zero]
    congr 1; ring
  have h8 : Real.exp (2 * Λ * (τ - s₀)) ≤ Real.exp (2 * Λ * (t₁ - s₀)) := by
    apply Real.exp_le_exp.2
    nlinarith [hτm.2]
  calc ∫ y in euclidBall (0 : Vec 2) (R / 8), (U (τ, y) - Uf (τ, y)) ^ 2
      = Real.exp (2 * Λ * (τ - s₀)) * (tw Λ s₀ τ ^ 2 *
          ∫ y in euclidBall (0 : Vec 2) (R / 8), (U (τ, y) - Uf (τ, y)) ^ 2) := by
        rw [← mul_assoc, h7, one_mul]
    _ ≤ Real.exp (2 * Λ * (τ - s₀)) * Y :=
        mul_le_mul_of_nonneg_left h6 (Real.exp_pos _).le
    _ ≤ Real.exp (2 * Λ * (t₁ - s₀)) * Y := mul_le_mul_of_nonneg_right h8 hY0

theorem davies_compare (hc : LabelCoeffs G V V₀ s₀ t₁) (hs : s₀ < t₁) {R κ lam ℓ ca N : ℝ}
    (hκ : 0 < κ) (hlam : 0 < lam)
    {U Uf : ℝ × Vec 2 → ℝ} {DU DUf : ℝ × Vec 2 → Vec 2}
    (hU : MemLp U 2 (volume.restrict (Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R)))
    (hDU : ∀ i : Fin 2,
      MemLp (fun p => DU p i) 2 (volume.restrict (Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R)))
    (hgU : ∀ᵐ τ ∂(volume.restrict (Set.Ioo s₀ t₁)),
      HasWeakGradientOn (euclidBall 0 R) (fun y => U (τ, y)) (fun y => DU (τ, y)))
    (hqU : ∀ ξ, IsSTTest (Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R) ξ →
      ∫ p in Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R, (-(U p * stTimeDeriv ξ p) +
        vecDot (V p) (DU p) * ξ p + κ * vecDot ((G p).mulVec (DU p)) (stSpaceGrad ξ p)) = 0)
    (hUf : MemLp Uf 2 (volume.restrict (Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R)))
    (hDUf : ∀ i : Fin 2,
      MemLp (fun p => DUf p i) 2 (volume.restrict (Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R)))
    (hgUf : ∀ᵐ τ ∂(volume.restrict (Set.Ioo s₀ t₁)),
      HasWeakGradientOn (euclidBall 0 R) (fun y => Uf (τ, y)) (fun y => DUf (τ, y)))
    (hqUf : ∀ ξ, IsSTTest (Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R) ξ →
      ∫ p in Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R, (-(Uf p * stTimeDeriv ξ p) +
        vecDot (V p) (DUf p) * ξ p + κ * vecDot ((G p).mulVec (DUf p)) (stSpaceGrad ξ p)) = 0)
    {χ η ψ : Vec 2 → ℝ} (hχ : IsSpTest (euclidBall 0 R) χ) (hχ1 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (hNχ : 0 ≤ N) (hχN : ∀ y, vecNormSq (spGrad χ y) ≤ N ^ 2)
    (hη : IsSpTest (euclidBall 0 R) η) (hη1 : ∀ y, 0 ≤ η y ∧ η y ≤ 1)
    (hηχ : ∀ y, y ∈ tsupport χ → η y = 1 ∧ spGrad η y = 0)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψ1 : ∀ y, vecNormSq (spGrad ψ y) ≤ 1)
    (hP10 : ∀ y, vecNormSq y ≤ (R / 8) ^ 2 → ψ y = 0 ∧ χ y = 1 ∧ η y = 1)
    (hP11 : ∀ y, spGrad χ y ≠ 0 → ψ y = -(ca * R) ∧ η y = 1)
    (hP12 : ∀ y, χ y ≠ 1 → ψ y = -(ca * R))
    {Wχ : ℝ → Lp ℝ 2 (volume.restrict (euclidBall 0 R))}
    (hWχc : ContinuousOn Wχ (Set.Icc s₀ t₁))
    (hWχae : ∀ᵐ τ ∂(volume.restrict (Set.Ioo s₀ t₁)),
      (Wχ τ : Vec 2 → ℝ) =ᵐ[volume.restrict (euclidBall 0 R)] fun y => χ y * U (τ, y))
    {v₀ : Vec 2 → ℝ} (hv₀ : v₀ =ᵐ[volume.restrict (euclidBall 0 R)] (Wχ s₀ : Vec 2 → ℝ))
    (hinit : ∀ ρ : Vec 2 → ℝ, IsSpTest (euclidBall 0 R) ρ →
      ContinuousWithinAt (fun τ => ∫ y in euclidBall 0 R, Uf (τ, y) * ρ y) (Set.Icc s₀ t₁) s₀ ∧
        ∫ y in euclidBall 0 R, Uf (s₀, y) * ρ y = ∫ y in euclidBall 0 R, v₀ y * ρ y) :
    ∀ᵐ τ ∂(volume.restrict (Set.Ioo s₀ t₁)),
      ∫ y in euclidBall 0 (R / 8), (U (τ, y) - Uf (τ, y)) ^ 2 ≤
        Real.exp (2 * decayRate κ ℓ V₀ lam * (t₁ - s₀)) *
          (Real.exp (-(2 * ℓ * (ca * R))) *
            (‖Wχ s₀‖ ^ 2 + srcBound G V₀ κ lam N s₀ t₁ R η U Uf DU DUf)) := by
  have hΛ : 0 ≤ decayRate κ ℓ V₀ lam := by
    have := hc.V0
    unfold decayRate; positivity
  have hDm : MemLp (fun p => U p - Uf p) 2
      (volume.restrict (Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R)) := hU.sub hUf
  have hDDm : ∀ i : Fin 2, MemLp (fun p => (fun p => DU p - DUf p) p i) 2
      (volume.restrict (Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R)) := fun i => by
    have := (hDU i).sub (hDUf i)
    exact this.ae_eq (Filter.Eventually.of_forall fun p => by simp)
  have hUs := ae_slice_memLp_gen hU
  have hUfs := ae_slice_memLp_gen hUf
  have hDUs : ∀ᵐ τ ∂(volume.restrict (Set.Ioo s₀ t₁)), ∀ i : Fin 2,
      MemLp (fun y => DU (τ, y) i) 2 (volume.restrict (euclidBall 0 R)) := by
    rw [Filter.eventually_all]; exact fun i => ae_slice_memLp_gen (hDU i)
  have hDUfs : ∀ᵐ τ ∂(volume.restrict (Set.Ioo s₀ t₁)), ∀ i : Fin 2,
      MemLp (fun y => DUf (τ, y) i) 2 (volume.restrict (euclidBall 0 R)) := by
    rw [Filter.eventually_all]; exact fun i => ae_slice_memLp_gen (hDUf i)
  have hgD : ∀ᵐ τ ∂(volume.restrict (Set.Ioo s₀ t₁)),
      HasWeakGradientOn (euclidBall 0 R) (fun y => (fun p => U p - Uf p) (τ, y))
        (fun y => (fun p => DU p - DUf p) (τ, y)) := by
    filter_upwards [hUs, hUfs, hDUs, hDUfs, hgU, hgUf] with τ a1 a2 a3 a4 a5 a6
    exact hasWeakGradientOn_sub_memLp a1 a2 a3 a4 a5 a6
  have hqD := weakEq_sub (κ := κ) hc hU hDU hUf hDUf hqU hqUf
  have hc1 : ∀ y, |χ y| ≤ 1 := fun y => by
    rw [abs_of_nonneg (hχ1 y).1]; exact (hχ1 y).2
  obtain ⟨W, hWc, hWae, hWb⟩ := local_weighted_energy (ℓ := ℓ) (lam := lam) hc hs hκ hlam
    hDm hDDm hgD hqD hχ hc1 hNχ hχN hη hηχ hψ hψ1
  have hζ := isSpTest_zeta (ℓ := ℓ) hψ hη
  have hident := trace_init_ident (Λ := decayRate κ ℓ V₀ lam) hs hU hUf hχ hζ hWc hWχc hWae
    hWχae hv₀ hinit
  have hinit0 := compare_init_bound hχ1 hη1 hP12 hv₀ hident
  have hS := compare_source_bound hc hκ hlam hU hUf hDU hDUf hη hη1 hχN hP11
    (ℓ := ℓ) (ca := ca)
  refine compare_extract hΛ hP10 hWae hUs hUfs (Y := Real.exp (-(2 * ℓ * (ca * R))) *
    (‖Wχ s₀‖ ^ 2 + srcBound G V₀ κ lam N s₀ t₁ R η U Uf DU DUf)) ?_
  intro τ hτ
  have := hWb τ hτ
  nlinarith [hinit0, hS]

end AVRegularity.Applications.Davies
end

section
open MeasureTheory Homogenization AVenhance Matrix Filter Topology
namespace AVRegularity.Applications.Davies

/-! # The label package of a torus solution

`uf_package`: for a weak solution `u` on the torus window, the pulled-back pair `(U_f, DU_f)` is a
square integrable solution of the non-conservative label equation with the energy bounds
`∬ U_f² ≤ 81 (t₁ - s₀) ‖f‖²`, `κ ∬ |DU_f|² ≤ 162 ‖f‖²`. -/

open AVRegularity.Applications

section

variable {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) {X : ℝ → Vec 2 → ℝ → Vec 2}
  (hX : IsFlow (streamVel φ) X) {t₁ T : ℝ} (ch : IsPipeChart (streamVel φ) X t₁ T) (hT : 0 < T)
  {b : ℝ → Vec 2 → Vec 2} {κ s₀ e : ℝ} (hs : t₁ - 8 * T ≤ s₀) (hs1 : s₀ < t₁) (ht1 : t₁ ≤ e)
  {f : Vec 2 → ℝ} {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
  (hu : IsWeakSolutionOnWith b κ s₀ e f u Du) (hb : IsWindowDrift b s₀ e)
  (hf : MemL2On unitCube f) (hκ : 0 < κ) {R : ℝ} (hR0 : 0 ≤ R) (hR : R ≤ 1)
  {B : ℝ} (hbm : Measurable fun p : ℝ × Vec 2 => b p.1 p.2) (hbB : ∀ t x, ‖b t x‖ ≤ B)
  (hb0s : ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × Vec 2 => streamVel φ p.1 p.2)
  (hb0d : ∀ t x, divSp (streamVel φ t) x = 0)

include hφ hX ch hT hs hs1 ht1 hu hb hf hκ hR0 hR hbm hbB hb0s hb0d

theorem uf_package :
    MemLp (Ufun u X t₁) 2 (volume.restrict (Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R)) ∧
    (∀ i : Fin 2, MemLp (fun p => DUfun Du X t₁ p i) 2
      (volume.restrict (Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R))) ∧
    (∀ᵐ τ ∂(volume.restrict (Set.Ioo s₀ t₁)),
      HasWeakGradientOn (euclidBall 0 R) (fun y => Ufun u X t₁ (τ, y))
        (fun y => DUfun Du X t₁ (τ, y))) ∧
    (∀ ξ, IsSTTest (Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R) ξ →
      ∫ p in Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R, (-(Ufun u X t₁ p * stTimeDeriv ξ p) +
        vecDot (pipeDrift b (streamVel φ) X t₁ p) (DUfun Du X t₁ p) * ξ p +
        κ * vecDot ((pipeMetric X t₁ p).mulVec (DUfun Du X t₁ p)) (stSpaceGrad ξ p)) = 0) ∧
    ∫ p in Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R, Ufun u X t₁ p ^ 2 ≤
      81 * (t₁ - s₀) * l2NormSq f ∧
    κ * ∫ p in Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R, vecNormSq (DUfun Du X t₁ p) ≤
      162 * l2NormSq f := by
  have hu' := hu
  obtain ⟨hslice, -, hL2, hDL2, hH1, -, -, -⟩ := hu'
  have hsub : Set.Ioo s₀ t₁ ×ˢ unitCube ⊆ Set.Ioo s₀ e ×ˢ unitCube :=
    Set.prod_mono (Set.Ioo_subset_Ioo le_rfl ht1) le_rfl
  have hper : ∀ᵐ t ∂(volume.restrict (Set.Ioo s₀ t₁)), IsZ2Periodic (u t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (hslice t ⟨ht.1.le, ht.2.le.trans ht1⟩).1
  have hH1' : ∀ᵐ t ∂(volume.restrict (Set.Ioo s₀ t₁)), IsPeriodicH1With (u t) (Du t) :=
    ae_restrict_of_ae_restrict_of_subset (Set.Ioo_subset_Ioo le_rfl ht1) hH1
  have hDper : ∀ᵐ t ∂(volume.restrict (Set.Ioo s₀ t₁)), IsZ2Periodic (Du t) :=
    hH1'.mono fun t ht => ht.2.1
  have hDL2' : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => Du p.1 p.2 i) 2
      (volume.restrict (Set.Ioo s₀ t₁ ×ˢ unitCube)) := fun i =>
    (hDL2 i).mono_measure (Measure.restrict_mono hsub le_rfl)
  refine ⟨Ufun_memLp ch hT hs le_rfl R hper (hL2.mono_measure (Measure.restrict_mono hsub le_rfl)),
    DUfun_memLp ch hT hs le_rfl R hDper hDL2', ?_, ?_, uf_energy_U hφ hX ch hT hs hs1 ht1 hu hb hf
      hκ hR0 hR, uf_energy_DU hφ hX ch hT hs hs1 ht1 hu hb hf hκ hR0 hR⟩
  · filter_upwards [hH1'] with τ hτ
    exact hasWeakGradientOn_univ_mono (Ufun_slice_grad hφ hX hτ) _
  · have hbp : ∀ t ∈ Set.Ioo s₀ e, IsZ2Periodic (b t) := fun t ht => hb.2.2.1 t ⟨ht.1.le, ht.2.le⟩
    have hloc := isLocalWeakSolution_of_weakSolutionOnWith hbp hu
    exact Ufun_weak ch hT hs hbm hbB hb0s hb0d (O := Set.Ioo s₀ e ×ˢ Set.univ)
      (fun t ht y => ⟨⟨ht.1, ht.2.trans_le ht1⟩, Set.mem_univ _⟩) hloc R

end

end AVRegularity.Applications.Davies
end
