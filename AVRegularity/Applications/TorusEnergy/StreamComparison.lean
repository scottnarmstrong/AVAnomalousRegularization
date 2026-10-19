-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Applications.TorusEnergy.StreamFacts
import AVRegularity.Applications.TorusEnergy.LocalInt
public import AVRegularity.Applications.Global.CompactRangeMain
import AVRegularity.Applications.LocalEnergy.Mollifier
import Mathlib.Algebra.Order.Star.Real

@[expose] public section
noncomputable section

section
open MeasureTheory Homogenization AVenhance Filter Topology
namespace AVRegularity.Applications

/-! # The difference of two weak solutions with different drifts is a forced torus solution

If `u` solves the equation with drift `b` and `v` with drift `bL` (same diffusivity), then
`w = u - v` solves `∂ₜw - κΔw = -(b·∇u - bL·∇v)` weakly, i.e. it satisfies `IsTorusForced` with
`P = κ ∇w`, `g = -(b·∇u - bL·∇v)`. -/

/-- Bounded measurable multipliers preserve `L²` of the window. -/
theorem memLp_mul_bdd_window {a b : ℝ} {m g : ℝ × Vec 2 → ℝ} (hm : Measurable m) {C : ℝ}
    (hb : ∀ p ∈ Set.Ioo a b ×ˢ unitCube, |m p| ≤ C)
    (hg : MemLp g 2 (volume.restrict (Set.Ioo a b ×ˢ unitCube))) :
    MemLp (fun p => m p * g p) 2 (volume.restrict (Set.Ioo a b ×ˢ unitCube)) := by
  have hcm : MemLp m ⊤ (volume.restrict (Set.Ioo a b ×ˢ unitCube)) :=
    MemLp.of_bound hm.aestronglyMeasurable C (by
      filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_unitCube')]
        with p hp using by simpa using hb p hp)
  exact hcm.mul hg

theorem memLp_dot_window {a b : ℝ} {m : ℝ → Vec 2 → Vec 2} {D : ℝ → Vec 2 → Vec 2}
    (hm : Measurable (fun p : ℝ × Vec 2 => m p.1 p.2)) {C : ℝ}
    (hb : ∀ t ∈ Set.Ioo a b, ∀ x, ‖m t x‖ ≤ C)
    (hD : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => D p.1 p.2 i) 2
      (volume.restrict (Set.Ioo a b ×ˢ unitCube))) :
    MemLp (fun p : ℝ × Vec 2 => vecDot (m p.1 p.2) (D p.1 p.2)) 2
      (volume.restrict (Set.Ioo a b ×ˢ unitCube)) := by
  have hi : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => m p.1 p.2 i * D p.1 p.2 i) 2
      (volume.restrict (Set.Ioo a b ×ˢ unitCube)) := fun i =>
    memLp_mul_bdd_window (m := fun p => m p.1 p.2 i) ((measurable_pi_apply i).comp hm) (C := C)
      (fun p hp => by simpa using (norm_le_pi_norm (m p.1 p.2) i).trans (hb p.1 hp.1 p.2)) (hD i)
  have e : (fun p : ℝ × Vec 2 => vecDot (m p.1 p.2) (D p.1 p.2)) =
      fun p => m p.1 p.2 0 * D p.1 p.2 0 + m p.1 p.2 1 * D p.1 p.2 1 := by
    funext p; simp [vecDot, Fin.sum_univ_two]
  rw [e]
  exact (hi 0).add (hi 1)

/-- **The difference of two weak solutions with different drifts is a forced torus solution.** -/
theorem isTorusForced_difference {b bL : ℝ → Vec 2 → Vec 2} {κ t₁ t₂ : ℝ} {f : Vec 2 → ℝ}
    {u v : ℝ → Vec 2 → ℝ} {Du Dv : ℝ → Vec 2 → Vec 2}
    (hbm : Measurable (fun p : ℝ × Vec 2 => b p.1 p.2))
    (hbb : ∃ C : ℝ, ∀ t ∈ Set.Icc t₁ t₂, ∀ x, ‖b t x‖ ≤ C)
    (hbp : ∀ t ∈ Set.Icc t₁ t₂, IsZ2Periodic (b t))
    (hbLm : Measurable (fun p : ℝ × Vec 2 => bL p.1 p.2))
    (hbLb : ∃ C : ℝ, ∀ t ∈ Set.Icc t₁ t₂, ∀ x, ‖bL t x‖ ≤ C)
    (hbLp : ∀ t ∈ Set.Icc t₁ t₂, IsZ2Periodic (bL t))
    (hu : IsWeakSolutionOnWith b κ t₁ t₂ f u Du) (hv : IsWeakSolutionOnWith bL κ t₁ t₂ f v Dv) :
    IsTorusForced (fun t x => u t x - v t x) (fun t x => Du t x - Dv t x)
      (fun t x => κ • (Du t x - Dv t x))
      (fun t x => -(vecDot (b t x) (Du t x) - vecDot (bL t x) (Dv t x))) t₁ t₂ := by
  obtain ⟨Cb, hCb⟩ := hbb
  obtain ⟨CL, hCL⟩ := hbLb
  have hbpo : ∀ t ∈ Set.Ioo t₁ t₂, IsZ2Periodic (b t) := fun t ht =>
    hbp t (Set.Ioo_subset_Icc_self ht)
  have hbLpo : ∀ t ∈ Set.Ioo t₁ t₂, IsZ2Periodic (bL t) := fun t ht =>
    hbLp t (Set.Ioo_subset_Icc_self ht)
  have hIoo : MeasurableSet (Set.Ioo t₁ t₂) := measurableSet_Ioo
  have hu' := hu
  have hv' := hv
  obtain ⟨hus, -, huL2, huDL2, huH1, huint, hucont, -⟩ := hu'
  obtain ⟨hvs, -, hvL2, hvDL2, hvH1, hvint, hvcont, -⟩ := hv'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact ⟨fun n x => by simp [(hus t ht).1 n x, (hvs t ht).1 n x],
      (hus t ht).2.sub (hvs t ht).2⟩
  · exact huL2.sub hvL2
  · intro i
    exact (huDL2 i).sub (hvDL2 i)
  · intro i
    have := ((huDL2 i).sub (hvDL2 i)).const_mul κ
    simpa using this
  · -- `g`
    have h1 := memLp_dot_window (a := t₁) (b := t₂) (m := b) (D := Du) hbm
      (fun t ht x => hCb t (Set.Ioo_subset_Icc_self ht) x) huDL2
    have h2 := memLp_dot_window (a := t₁) (b := t₂) (m := bL) (D := Dv) hbLm
      (fun t ht x => hCL t (Set.Ioo_subset_Icc_self ht) x) hvDL2
    exact (h1.sub h2).neg
  · filter_upwards [huH1, hvH1] with t h1 h2
    exact isPeriodicH1With_sub h1 h2
  · filter_upwards [huH1, hvH1] with t h1 h2
    intro n x
    simp [h1.2.1 n x, h2.2.1 n x]
  · filter_upwards [huH1, hvH1, ae_restrict_mem hIoo] with t h1 h2 ht
    intro n x
    simp only [hbpo t ht n x, hbLpo t ht n x, h1.2.1 n x, h2.2.1 n x]
  · intro φ hφ
    have hA := (isLocalWeakSolution_of_weakSolutionOnWith hbpo hu).2.2.2 φ hφ
    have hB := (isLocalWeakSolution_of_weakSolutionOnWith hbLpo hv).2.2.2 φ hφ
    have hAi := localWeak_integrable hbpo hu hφ
    have hBi := localWeak_integrable hbLpo hv hφ
    have := integral_sub hAi hBi
    rw [hA, hB, sub_zero] at this
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [vecDot, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    ring
  · intro ψ hψ hψp
    have hcu := hucont ψ hψ hψp
    have hcv := hvcont ψ hψ hψp
    refine (hcu.sub hcv).congr fun t ht => ?_
    simp only [Pi.sub_apply]
    have i1 := integrable_mul_memL2 (hus t ht).2 (memL2_continuous hψ.continuous)
    have i2 := integrable_mul_memL2 (hvs t ht).2 (memL2_continuous hψ.continuous)
    rw [← integral_sub i1 i2]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)

/-! # Stream comparison

For streams `φ`, `φL` with `|φ - φL| ≤ κ ϑ`, the solutions `u`, `v` with the same datum satisfy
`‖u(t) - v(t)‖_{L²(𝕋²)} ≤ ϑ ‖f‖_{L²(𝕋²)}` (here with the constant `1/√2` inside, weakened to `1`).
Lemma 8.2 of the paper follows from it. -/

theorem torus_vecNormSq_two (x : Vec 2) : vecNormSq x = x 0 * x 0 + x 1 * x 1 := by
  simp [vecNormSq, vecDot, Fin.sum_univ_two]

theorem young_cross (a b : Vec 2) {ψ κ ϑ : ℝ} (hκ : 0 ≤ κ) (hψ : |ψ| ≤ κ * ϑ) :
    -2 * (ψ * crossDot a b) ≤ κ * vecNormSq b + κ * ϑ ^ 2 * vecNormSq a := by
  set A := vecNormSq a with hA
  set B := vecNormSq b with hB
  have hA0 : 0 ≤ A := vecNormSq_nonneg a
  have hB0 : 0 ≤ B := vecNormSq_nonneg b
  have hc2 : crossDot a b ^ 2 ≤ A * B := by
    simp only [hA, hB, torus_vecNormSq_two, crossDot]
    nlinarith [sq_nonneg (a 0 * b 0 + a 1 * b 1)]
  have h1 : (2 * ϑ * |crossDot a b|) ^ 2 ≤ (ϑ ^ 2 * A + B) ^ 2 := by
    have : (2 * ϑ * |crossDot a b|) ^ 2 = 4 * ϑ ^ 2 * crossDot a b ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs]; ring
    rw [this]
    nlinarith [sq_nonneg (ϑ ^ 2 * A - B), mul_le_mul_of_nonneg_left hc2 (sq_nonneg ϑ),
      sq_nonneg ϑ]
  have h2 : 2 * ϑ * |crossDot a b| ≤ ϑ ^ 2 * A + B :=
    abs_le_of_sq_le_sq' h1 (by positivity) |>.2
  have h3 : -2 * (ψ * crossDot a b) ≤ 2 * (κ * ϑ) * |crossDot a b| := by
    have : |ψ * crossDot a b| ≤ κ * ϑ * |crossDot a b| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right hψ (abs_nonneg _)
    have := neg_abs_le (ψ * crossDot a b)
    nlinarith [abs_nonneg (ψ * crossDot a b)]
  calc -2 * (ψ * crossDot a b) ≤ 2 * (κ * ϑ) * |crossDot a b| := h3
    _ = κ * (2 * ϑ * |crossDot a b|) := by ring
    _ ≤ κ * (ϑ ^ 2 * A + B) := mul_le_mul_of_nonneg_left h2 hκ
    _ = κ * B + κ * ϑ ^ 2 * A := by ring

/-! # Stream energy comparison

For a full stream `φ` and a smooth stream `φL` with
`|φ - φL| ≤ κ ϑ`, two weak solutions `u`, `v` with the same datum `f` satisfy
`‖u(t) - v(t)‖² + κ ∬ |∇(u - v)|² ≤ (ϑ²/2) ‖f‖²` (so in particular `≤ ϑ² ‖f‖²`). -/

theorem integrable_mul_of_memLp_two {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun p => f p * g p) μ := by
  exact hf.integrable_mul hg

theorem integrable_cross_grad_mul {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ 1 ψ) {D : Vec 2 → Vec 2}
    (hD : ∀ i, MemL2On unitCube (fun x => D x i)) {w : Vec 2 → ℝ} (hw : MemL2On unitCube w) :
    Integrable (fun x => crossDot (spaceGrad ψ x) (D x) * w x) (volume.restrict unitCube) := by
  have hg : ∀ i, Continuous fun x => spaceGrad ψ x i := continuous_spaceGrad_apply hψ
  have h0 := integrable_mul_memL2 (memL2_mul_continuous (hg 0) (hD 1)) hw
  have h1 := integrable_mul_memL2 (memL2_mul_continuous (hg 1) (hD 0)) hw
  refine (h0.sub h1).congr (Eventually.of_forall fun x => ?_)
  simp only [crossDot, Pi.sub_apply]
  ring

theorem integrable_coef_cross {c : Vec 2 → ℝ} (hc : Continuous c) {A B : Vec 2 → Vec 2}
    (hA : ∀ i, MemL2On unitCube (fun x => A x i)) (hB : ∀ i, MemL2On unitCube (fun x => B x i)) :
    Integrable (fun x => c x * crossDot (A x) (B x)) (volume.restrict unitCube) := by
  have h0 := integrable_mul_memL2 (memL2_mul_continuous hc (hA 0)) (hB 1)
  have h1 := integrable_mul_memL2 (memL2_mul_continuous hc (hA 1)) (hB 0)
  refine (h0.sub h1).congr (Eventually.of_forall fun x => ?_)
  simp only [crossDot, Pi.sub_apply]
  ring

/-- Slice identity: `∫ (σ∇φ·Du - σ∇φL·Dv)(u - v) = ∫ (φ - φL) (Dv × (Du - Dv))`. -/
theorem slice_skew_diff {φ φL : Vec 2 → ℝ} (hφ : ContDiff ℝ 1 φ) (pφ : IsZ2Periodic φ)
    (hφL : ContDiff ℝ 1 φL) (pφL : IsZ2Periodic φL) {u v : Vec 2 → ℝ} {Du Dv : Vec 2 → Vec 2}
    (hu : IsPeriodicH1With u Du) (hv : IsPeriodicH1With v Dv) :
    ∫ x in unitCube, (vecDot (sigmaMat.mulVec (spaceGrad φ x)) (Du x) -
        vecDot (sigmaMat.mulVec (spaceGrad φL x)) (Dv x)) * (u x - v x) =
      ∫ x in unitCube, (φ x - φL x) * crossDot (Dv x) (Du x - Dv x) := by
  have hw : IsPeriodicH1With (fun x => u x - v x) (fun x => Du x - Dv x) :=
    isPeriodicH1With_sub hu hv
  have e1 := skew_h1 hφ pφ hu hw
  have e2 := skew_h1 hφL pφL hv hw
  have wL : MemL2On unitCube (fun x => u x - v x) := hw.2.2.1
  have i1 := integrable_cross_grad_mul hφ hu.2.2.2.1 wL
  have i2 := integrable_cross_grad_mul hφL hv.2.2.2.1 wL
  have j1 := integrable_coef_cross hφ.continuous hu.2.2.2.1 hw.2.2.2.1
  have j2 := integrable_coef_cross hφL.continuous hv.2.2.2.1 hw.2.2.2.1
  have lhs : ∫ x in unitCube, (vecDot (sigmaMat.mulVec (spaceGrad φ x)) (Du x) -
        vecDot (sigmaMat.mulVec (spaceGrad φL x)) (Dv x)) * (u x - v x) =
      (∫ x in unitCube, crossDot (spaceGrad φ x) (Du x) * (u x - v x)) -
        ∫ x in unitCube, crossDot (spaceGrad φL x) (Dv x) * (u x - v x) := by
    rw [← integral_sub i1 i2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [vecDot_sigma]
    ring
  rw [lhs, e1, e2, ← integral_sub j1 j2]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [crossDot, Pi.sub_apply]
  ring

theorem integral_window_eq_slices {a τ : ℝ} {F : ℝ × Vec 2 → ℝ}
    (hF : Integrable F (volume.restrict (Set.Ioo a τ ×ˢ unitCube))) :
    ∫ p in Set.Ioo a τ ×ˢ unitCube, F p = ∫ t in Set.Ioo a τ, ∫ x in unitCube, F (t, x) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hF ⊢
  exact integral_prod F hF

/-- Space-time version of the slice identity over `(a, τ) × 𝕋²`. -/
theorem window_skew_diff {φ φL : ℝ → Vec 2 → ℝ} (hφ : ∀ t, ContDiff ℝ 1 (φ t))
    (pφ : ∀ t, IsZ2Periodic (φ t)) (hφL : ∀ t, ContDiff ℝ 1 (φL t))
    (pφL : ∀ t, IsZ2Periodic (φL t)) {u v : ℝ → Vec 2 → ℝ} {Du Dv : ℝ → Vec 2 → Vec 2}
    {a τ : ℝ}
    (hae : ∀ᵐ t ∂(volume.restrict (Set.Ioo a τ)), IsPeriodicH1With (u t) (Du t) ∧
      IsPeriodicH1With (v t) (Dv t))
    (h1 : Integrable (fun p : ℝ × Vec 2 =>
      (vecDot (streamVel φ p.1 p.2) (Du p.1 p.2) - vecDot (streamVel φL p.1 p.2) (Dv p.1 p.2)) *
        (u p.1 p.2 - v p.1 p.2)) (volume.restrict (Set.Ioo a τ ×ˢ unitCube)))
    (h2 : Integrable (fun p : ℝ × Vec 2 => (φ p.1 p.2 - φL p.1 p.2) *
      crossDot (Dv p.1 p.2) (Du p.1 p.2 - Dv p.1 p.2))
      (volume.restrict (Set.Ioo a τ ×ˢ unitCube))) :
    ∫ p in Set.Ioo a τ ×ˢ unitCube, (vecDot (streamVel φ p.1 p.2) (Du p.1 p.2) -
        vecDot (streamVel φL p.1 p.2) (Dv p.1 p.2)) * (u p.1 p.2 - v p.1 p.2) =
      ∫ p in Set.Ioo a τ ×ˢ unitCube, (φ p.1 p.2 - φL p.1 p.2) *
        crossDot (Dv p.1 p.2) (Du p.1 p.2 - Dv p.1 p.2) := by
  rw [integral_window_eq_slices h1, integral_window_eq_slices h2]
  refine integral_congr_ae ?_
  filter_upwards [hae] with t ht
  exact slice_skew_diff (hφ t) (pφ t) (hφL t) (pφL t) ht.1 ht.2

theorem torus_integrable_vecNormSq_of_memLp {μ : Measure (ℝ × Vec 2)} {G : ℝ × Vec 2 → Vec 2}
    (h : ∀ i : Fin 2, MemLp (fun p => G p i) 2 μ) :
    Integrable (fun p => vecNormSq (G p)) μ := by
  simp only [torus_vecNormSq_two]
  exact (integrable_mul_of_memLp_two (h 0) (h 0)).add (integrable_mul_of_memLp_two (h 1) (h 1))

theorem contDiff_one_slice {φ : ℝ → Vec 2 → ℝ}
    (h : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2)) (t : ℝ) : ContDiff ℝ 1 (φ t) :=
  contDiff_one_of_top (h.comp (contDiff_const.prodMk contDiff_id))

/-- **Stream energy comparison** (with gradient fields explicit): the energy of the difference plus
`κ` times its dissipation is bounded by `(ϑ²/2) ‖f‖²`. -/
theorem stream_comparison_with {φ φL : ℝ → Vec 2 → ℝ} (hφ : IsFullStream φ)
    (hφL : IsSmoothStream φL) {κ ϑ t₁ t₂ : ℝ} (hκ : 0 < κ) (h12 : t₁ < t₂)
    (hψ : ∀ t x, |φ t x - φL t x| ≤ κ * ϑ) {f : Vec 2 → ℝ} (hf : MemL2On unitCube f)
    {u v : ℝ → Vec 2 → ℝ} {Du Dv : ℝ → Vec 2 → Vec 2}
    (hu : IsWeakSolutionOnWith (streamVel φ) κ t₁ t₂ f u Du)
    (hv : IsWeakSolutionOnWith (streamVel φL) κ t₁ t₂ f v Dv) :
    ∀ τ ∈ Set.Icc t₁ t₂, l2NormSq (fun x => u τ x - v τ x) +
      κ * ∫ p in Set.Ioo t₁ τ ×ˢ unitCube, vecNormSq (Du p.1 p.2 - Dv p.1 p.2) ≤
        ϑ ^ 2 / 2 * l2NormSq f := by
  obtain ⟨hφc, hφ1, hbc, ⟨B, hB⟩, hφp⟩ := hφ
  obtain ⟨hφLs, hφLp⟩ := hφL
  have hφL1 : ∀ t, ContDiff ℝ 1 (φL t) := contDiff_one_slice hφLs
  have hϑ : 0 ≤ ϑ := by
    by_contra h
    push Not at h
    have := mul_neg_of_pos_of_neg hκ h
    linarith [abs_nonneg (φ 0 0 - φL 0 0), hψ 0 0]
  have hbL := continuous_streamVel_smooth hφLs
  have hF := isTorusForced_difference (hbc.measurable) ⟨B, fun t _ x => hB t x⟩
    (fun t _ => streamVel_periodic hφp t) hbL.measurable
    (bounded_streamVel_smooth hφLs hφLp t₁ t₂) (fun t _ => streamVel_periodic hφLp t) hu hv
  have hen := torus_forced_energy_identity h12 hF
  have hinit : l2NormSq (fun x => u t₁ x - v t₁ x) = 0 := by
    refine torus_forced_initial_zero h12 hF (fun ψ hψs hψp => ?_)
    have i1 := integrable_mul_memL2 (hu.1 t₁ ⟨le_rfl, h12.le⟩).2 (memL2_continuous hψs.continuous)
    have i2 := integrable_mul_memL2 (hv.1 t₁ ⟨le_rfl, h12.le⟩).2 (memL2_continuous hψs.continuous)
    show ∫ x in unitCube, (u t₁ x - v t₁ x) * ψ x = 0
    simp_rw [sub_mul]
    rw [integral_sub i1 i2, initial_pairing h12 hu hψs hψp, initial_pairing h12 hv hψs hψp, sub_self]
  -- the dissipation of `v`
  have hbw : IsWindowDrift (streamVel φL) t₁ t₂ :=
    ⟨hbL.measurable, bounded_streamVel_smooth hφLs hφLp t₁ t₂,
      fun t _ => streamVel_periodic hφLp t,
      fun t _ χ hχ hc => streamVel_integral_zero hφL1 t hχ hc⟩
  have hdissv := (l2NormSq_le_of_weakSolutionOnWith hκ.le h12 hbw hf hv).2 t₂ ⟨h12.le, le_rfl⟩
  obtain ⟨-, -, -, huDL2, huH1, -, -, -⟩ := hu
  obtain ⟨-, -, -, hvDL2, hvH1, -, -, -⟩ := hv
  intro τ hτ
  have hsub : (Set.Ioo t₁ τ ×ˢ unitCube : Set (ℝ × Vec 2)) ⊆ Set.Ioo t₁ t₂ ×ˢ unitCube :=
    Set.prod_mono (Set.Ioo_subset_Ioo_right hτ.2) subset_rfl
  have hmono : (volume.restrict (Set.Ioo t₁ τ ×ˢ unitCube) : Measure (ℝ × Vec 2)) ≤
      volume.restrict (Set.Ioo t₁ t₂ ×ˢ unitCube) := Measure.restrict_mono hsub le_rfl
  have hDwi : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => Du p.1 p.2 i - Dv p.1 p.2 i) 2
      (volume.restrict (Set.Ioo t₁ t₂ ×ˢ unitCube)) := fun i => (huDL2 i).sub (hvDL2 i)
  have IA : Integrable (fun p : ℝ × Vec 2 => vecNormSq (Du p.1 p.2 - Dv p.1 p.2))
      (volume.restrict (Set.Ioo t₁ t₂ ×ˢ unitCube)) :=
    torus_integrable_vecNormSq_of_memLp (G := fun p => Du p.1 p.2 - Dv p.1 p.2) hDwi
  have IB : Integrable (fun p : ℝ × Vec 2 => vecNormSq (Dv p.1 p.2))
      (volume.restrict (Set.Ioo t₁ t₂ ×ˢ unitCube)) :=
    torus_integrable_vecNormSq_of_memLp (G := fun p => Dv p.1 p.2) hvDL2
  have hψm : Measurable (fun p : ℝ × Vec 2 => φ p.1 p.2 - φL p.1 p.2) :=
    (hφc.sub hφLs.continuous).measurable
  have hψb : ∀ p ∈ Set.Ioo t₁ t₂ ×ˢ unitCube, |φ p.1 p.2 - φL p.1 p.2| ≤ κ * ϑ :=
    fun p _ => hψ p.1 p.2
  have hψDv : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => (φ p.1 p.2 - φL p.1 p.2) * Dv p.1 p.2 i) 2
      (volume.restrict (Set.Ioo t₁ t₂ ×ˢ unitCube)) := fun i =>
    memLp_mul_bdd_window (m := fun p => φ p.1 p.2 - φL p.1 p.2) hψm hψb (hvDL2 i)
  have IC : Integrable (fun p : ℝ × Vec 2 => (φ p.1 p.2 - φL p.1 p.2) *
      crossDot (Dv p.1 p.2) (Du p.1 p.2 - Dv p.1 p.2))
      (volume.restrict (Set.Ioo t₁ t₂ ×ˢ unitCube)) := by
    have h0 := integrable_mul_of_memLp_two (hψDv 0) (hDwi 1)
    have h1 := integrable_mul_of_memLp_two (hψDv 1) (hDwi 0)
    refine (h0.sub h1).congr (Eventually.of_forall fun p => ?_)
    simp only [crossDot, Pi.sub_apply]
    ring
  have IX : Integrable (fun p : ℝ × Vec 2 =>
      (vecDot (streamVel φ p.1 p.2) (Du p.1 p.2) - vecDot (streamVel φL p.1 p.2) (Dv p.1 p.2)) *
        (u p.1 p.2 - v p.1 p.2)) (volume.restrict (Set.Ioo t₁ t₂ ×ˢ unitCube)) := by
    have := (integrable_mul_of_memLp_two hF.memg hF.memw).neg
    refine this.congr (Eventually.of_forall fun p => ?_)
    simp only [Pi.neg_apply]
    ring
  have hae : ∀ᵐ t ∂(volume.restrict (Set.Ioo t₁ τ)), IsPeriodicH1With (u t) (Du t) ∧
      IsPeriodicH1With (v t) (Dv t) :=
    ae_restrict_of_ae_restrict_of_subset (Set.Ioo_subset_Ioo_right hτ.2) (huH1.and hvH1)
  have hskew := window_skew_diff hφ1 hφp hφL1 hφLp hae (IX.mono_measure hmono)
    (IC.mono_measure hmono)
  have hid := hen t₁ ⟨le_rfl, h12.le⟩ τ hτ hτ.1
  rw [hinit] at hid
  have hI : ∫ p in Set.Ioo t₁ τ ×ˢ unitCube,
      (vecDot (κ • (Du p.1 p.2 - Dv p.1 p.2)) (Du p.1 p.2 - Dv p.1 p.2) -
        -(vecDot (streamVel φ p.1 p.2) (Du p.1 p.2) - vecDot (streamVel φL p.1 p.2) (Dv p.1 p.2)) *
          (u p.1 p.2 - v p.1 p.2)) =
      κ * (∫ p in Set.Ioo t₁ τ ×ˢ unitCube, vecNormSq (Du p.1 p.2 - Dv p.1 p.2)) +
      ∫ p in Set.Ioo t₁ τ ×ˢ unitCube, (φ p.1 p.2 - φL p.1 p.2) *
        crossDot (Dv p.1 p.2) (Du p.1 p.2 - Dv p.1 p.2) := by
    have hadd := integral_add ((IA.mono_measure hmono).const_mul κ) (IX.mono_measure hmono)
    rw [integral_const_mul] at hadd
    rw [← hskew, ← hadd]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [vecDot, vecNormSq, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
    ring
  have hle : ∫ p in Set.Ioo t₁ τ ×ˢ unitCube, -2 * ((φ p.1 p.2 - φL p.1 p.2) *
        crossDot (Dv p.1 p.2) (Du p.1 p.2 - Dv p.1 p.2)) ≤
      ∫ p in Set.Ioo t₁ τ ×ˢ unitCube, (κ * vecNormSq (Du p.1 p.2 - Dv p.1 p.2) +
        κ * ϑ ^ 2 * vecNormSq (Dv p.1 p.2)) := by
    refine integral_mono ((IC.mono_measure hmono).const_mul (-2))
      (((IA.mono_measure hmono).const_mul κ).add ((IB.mono_measure hmono).const_mul _))
      (fun p => ?_)
    exact young_cross (Dv p.1 p.2) (Du p.1 p.2 - Dv p.1 p.2) hκ.le (hψ p.1 p.2)
  rw [integral_const_mul, integral_add ((IA.mono_measure hmono).const_mul κ)
    ((IB.mono_measure hmono).const_mul _), integral_const_mul, integral_const_mul] at hle
  have hmon : ∫ p in Set.Ioo t₁ τ ×ˢ unitCube, vecNormSq (Dv p.1 p.2) ≤
      ∫ p in Set.Ioo t₁ t₂ ×ˢ unitCube, vecNormSq (Dv p.1 p.2) :=
    setIntegral_mono_set IB (Eventually.of_forall fun p => vecNormSq_nonneg _)
      (Eventually.of_forall hsub)
  have hdv := mul_le_mul_of_nonneg_left hmon (mul_nonneg hκ.le (sq_nonneg ϑ))
  have e1 : l2NormSq (fun x => u τ x - v τ x) = -2 * (κ * (∫ p in Set.Ioo t₁ τ ×ˢ unitCube,
      vecNormSq (Du p.1 p.2 - Dv p.1 p.2)) + ∫ p in Set.Ioo t₁ τ ×ˢ unitCube,
        (φ p.1 p.2 - φL p.1 p.2) * crossDot (Dv p.1 p.2) (Du p.1 p.2 - Dv p.1 p.2)) := by
    rw [← hI]
    simpa using hid
  have : κ * ϑ ^ 2 * ∫ p in Set.Ioo t₁ t₂ ×ˢ unitCube, vecNormSq (Dv p.1 p.2) ≤
      ϑ ^ 2 / 2 * l2NormSq f := by
    have h2 := mul_le_mul_of_nonneg_left hdissv (sq_nonneg ϑ)
    nlinarith [h2]
  linarith

/-- **Stream energy comparison, sharp form**: `‖u(t) - v(t)‖² ≤ (ϑ²/2) ‖f‖²` on `[t₁, t₂]`, and
the gradient fields can be chosen with `κ ∬ |D(u - v)|² ≤ (ϑ²/2) ‖f‖²`. -/
theorem stream_comparison_half {φ φL : ℝ → Vec 2 → ℝ} (hφ : IsFullStream φ)
    (hφL : IsSmoothStream φL) {κ ϑ t₁ t₂ : ℝ} (hκ : 0 < κ) (h12 : t₁ < t₂)
    (hψ : ∀ t x, |φ t x - φL t x| ≤ κ * ϑ) {f : Vec 2 → ℝ} (hf : MemL2On unitCube f)
    {u v : ℝ → Vec 2 → ℝ} (hu : IsWeakSolutionOn (streamVel φ) κ t₁ t₂ f u)
    (hv : IsWeakSolutionOn (streamVel φL) κ t₁ t₂ f v) :
    (∀ t ∈ Set.Icc t₁ t₂, l2NormSq (fun x => u t x - v t x) ≤ ϑ ^ 2 / 2 * l2NormSq f) ∧
    ∃ Du Dv : ℝ → Vec 2 → Vec 2, IsWeakSolutionOnWith (streamVel φ) κ t₁ t₂ f u Du ∧
      IsWeakSolutionOnWith (streamVel φL) κ t₁ t₂ f v Dv ∧
      κ * ∫ p in Set.Ioo t₁ t₂ ×ˢ unitCube, vecNormSq (Du p.1 p.2 - Dv p.1 p.2) ≤
        ϑ ^ 2 / 2 * l2NormSq f := by
  obtain ⟨Du, hDu⟩ := hu
  obtain ⟨Dv, hDv⟩ := hv
  have key := stream_comparison_with hφ hφL hκ h12 hψ hf hDu hDv
  have hnn : ∀ τ, 0 ≤ ∫ p in Set.Ioo t₁ τ ×ˢ unitCube, vecNormSq (Du p.1 p.2 - Dv p.1 p.2) :=
    fun τ => integral_nonneg fun p => vecNormSq_nonneg _
  have hl : ∀ t, 0 ≤ l2NormSq (fun x => u t x - v t x) := fun t =>
    integral_nonneg fun x => sq_nonneg _
  refine ⟨fun t ht => ?_, Du, Dv, hDu, hDv, ?_⟩
  · have := mul_nonneg hκ.le (hnn t)
    linarith [key t ht]
  · have := key t₂ ⟨h12.le, le_rfl⟩
    linarith [hl t₂]

/-- **Stream energy comparison**, with the constant `1`; Lemma 8.2 of the paper follows from it. -/
theorem stream_comparison {φ φL : ℝ → Vec 2 → ℝ} (hφ : IsFullStream φ)
    (hφL : IsSmoothStream φL) {κ ϑ t₁ t₂ : ℝ} (hκ : 0 < κ) (h12 : t₁ < t₂)
    (hψ : ∀ t x, |φ t x - φL t x| ≤ κ * ϑ) {f : Vec 2 → ℝ} (hf : MemL2On unitCube f)
    {u v : ℝ → Vec 2 → ℝ} (hu : IsWeakSolutionOn (streamVel φ) κ t₁ t₂ f u)
    (hv : IsWeakSolutionOn (streamVel φL) κ t₁ t₂ f v) :
    ∀ t ∈ Set.Icc t₁ t₂, l2NormSq (fun x => u t x - v t x) ≤ ϑ ^ 2 * l2NormSq f := by
  intro t ht
  have h := (stream_comparison_half hφ hφL hκ h12 hψ hf hu hv).1 t ht
  have h0 : 0 ≤ ϑ ^ 2 * l2NormSq f :=
    mul_nonneg (sq_nonneg ϑ) (integral_nonneg fun x => sq_nonneg _)
  linarith

end AVRegularity.Applications
end
