-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Applications.TorusEnergy.LocalInt
import AVRegularity.Applications.Dissipation.Linear
import AVenhance.Infra.Parabolic.WeakUniqueness.WeakEnergyPassage

/-! # Restarting a weak solution at an interior time

A weak solution on `[t₁, t₂]` is a weak solution on `[t', t₂]` with datum `θ(t')`, for every
`t' ∈ [t₁, t₂]`. With `isWeakSolutionOnWith_restrict` (shorter end time) this lets the decay
estimate be iterated on consecutive windows.

Proof: test the weak form on `[t₁, t₂]` with `(1 - η_δ(t)) φ(t, x)`, where `η_δ = etaCut t' δ`
is `1` for `t ≤ t'` and `0` for `t ≥ t' + δ`; it vanishes at `t₁`. The time derivative of the
cutoff is the unit kernel `kerCut t' δ`, so
`∬ (1 - η_δ) I(φ) = ∫ kerCut(t) ⟨θ(t), φ(t)⟩ dt`. As `δ → 0` the left side tends to the weak form
on `(t', t₂)` and the right side to `⟨θ(t'), φ(t')⟩`, by right continuity of
`t ↦ ⟨θ(t), φ(t)⟩` (weak continuity, the slice bound and uniform continuity of `φ`). -/

public section

open MeasureTheory Filter Topology Homogenization AVenhance

namespace AVRegularity.Applications.Dissipation

/-- The unit cell has finite measure. -/
local instance dissipationRestartFiniteCube : IsFiniteMeasure (volume.restrict unitCube) :=
  isFiniteMeasure_restrict.2 unitCube_measure_ne_top

/-- Continuity of `t ↦ ∫_{𝕋²} θ(t) φ(t)` at `t'` along the window, for a jointly continuous `φ`
whose slice at `t'` is smooth and periodic. -/
theorem continuousWithinAt_pairing_of_isWeakSolutionOnWith {b : ℝ → Vec 2 → Vec 2}
    {κ t₁ t₂ : ℝ} {f : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2}
    (hθ : IsWeakSolutionOnWith b κ t₁ t₂ f θ Dθ) {φ : ℝ → Vec 2 → ℝ}
    (hφc : Continuous (fun p : ℝ × Vec 2 => φ p.1 p.2)) {t' : ℝ} (ht' : t' ∈ Set.Icc t₁ t₂)
    (hφs : ContDiff ℝ (⊤ : ℕ∞) (φ t')) (hφp : IsZ2Periodic (φ t')) :
    ContinuousWithinAt (fun t => ∫ x in unitCube, θ t x * φ t x) (Set.Icc t₁ t₂) t' := by
  obtain ⟨hslice, ⟨C, hC⟩, -, -, -, -, hcont, -⟩ := hθ
  have hb := hcont (φ t') hφs hφp
  have hK : IsCompact (Set.Icc t₁ t₂ ×ˢ Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)
  have huc := hK.uniformContinuousOn_of_continuous hφc.continuousOn
  have hslc : ∀ t, Continuous (φ t) := fun t => hφc.comp (Continuous.prodMk_right t)
  set M : ℝ := Real.sqrt (max C 0) + 1 with hM
  have hM0 : 0 < M := by positivity
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨r₁, hr₁, hb'⟩ := Metric.continuousWithinAt_iff.1 (hb t' ht') (ε / 2) (half_pos hε)
  obtain ⟨ρ, hρ, hρ'⟩ := Metric.uniformContinuousOn_iff.1 huc (ε / (2 * M)) (by positivity)
  refine ⟨min r₁ ρ, lt_min hr₁ hρ, fun {t} ht hdist => ?_⟩
  have hdist1 : dist t t' < r₁ := lt_of_lt_of_le hdist (min_le_left _ _)
  have hdist2 : dist t t' < ρ := lt_of_lt_of_le hdist (min_le_right _ _)
  have hθt := (hslice t ht).2
  have i1 := integrable_mul_continuous_cell hθt ((hslc t).sub (hslc t'))
  have i2 := integrable_mul_continuous_cell hθt (hslc t')
  have i3 := integrable_mul_continuous_cell hθt (hslc t)
  have e : (∫ x in unitCube, θ t x * φ t x) - ∫ x in unitCube, θ t' x * φ t' x =
      (∫ x in unitCube, θ t x * (φ t x - φ t' x)) +
        ((∫ x in unitCube, θ t x * φ t' x) - ∫ x in unitCube, θ t' x * φ t' x) := by
    have e1 : ∫ x in unitCube, θ t x * (φ t x - φ t' x) =
        (∫ x in unitCube, θ t x * φ t x) - ∫ x in unitCube, θ t x * φ t' x := by
      rw [← integral_sub i3 i2]
      congr 1
      funext x
      ring
    rw [e1]
    ring
  -- the first piece is small by uniform continuity and the slice bound
  have hη : ∀ x ∈ unitCube, |φ t x - φ t' x| ≤ ε / (2 * M) := by
    intro x hx
    have hxK : x ∈ Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1 := fun i hi =>
      ⟨(hx i hi).1.le, (hx i hi).2.le⟩
    have h := hρ' (t, x) ⟨ht, hxK⟩ (t', x) ⟨ht', hxK⟩ (by
      rw [Prod.dist_eq, dist_self]
      simpa using hdist2)
    rw [Real.dist_eq] at h
    exact h.le
  have hl1 : ∫ x in unitCube, |θ t x| ≤ Real.sqrt (max C 0) := by
    have h := Infra.Parabolic.WeakUniqueness.WeakEnergyPassage.weakEnergy_l2_pairing_bound hθt.norm (memLp_const (1 : ℝ))
    simp only [Real.norm_eq_abs, mul_one, sq_abs, one_pow] at h
    have h1 : ∫ x in unitCube, (1 : ℝ) = 1 := by
      rw [integral_const, Measure.real, Measure.restrict_apply_univ]
      have hvol : (volume : Measure (Vec 2)) unitCube = 1 := by
        unfold unitCube
        rw [volume_pi, Measure.pi_pi]
        simp [Real.volume_Ioo]
      simp [hvol]
    rw [h1, Real.sqrt_one, mul_one, abs_of_nonneg (integral_nonneg fun x => abs_nonneg _)] at h
    exact h.trans (Real.sqrt_le_sqrt ((hC t ht).trans (le_max_left _ _)))
  have hpiece1 : |∫ x in unitCube, θ t x * (φ t x - φ t' x)| ≤
      ε / (2 * M) * Real.sqrt (max C 0) := by
    refine (abs_integral_le_integral_abs).trans ?_
    have hmono : ∫ x in unitCube, |θ t x * (φ t x - φ t' x)| ≤
        ∫ x in unitCube, ε / (2 * M) * |θ t x| := by
      refine integral_mono_ae i1.abs ((hθt.integrable one_le_two).abs.const_mul _) ?_
      filter_upwards [ae_restrict_mem measurableSet_unitCube'] with x hx
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hη x hx) (abs_nonneg _)
    rw [integral_const_mul] at hmono
    exact hmono.trans (mul_le_mul_of_nonneg_left hl1 (by positivity))
  have hpiece2 := hb' ht hdist1
  rw [Real.dist_eq] at hpiece2 ⊢
  rw [e]
  have hsmall : ε / (2 * M) * Real.sqrt (max C 0) < ε / 2 := by
    rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) two_pos]
    have : Real.sqrt (max C 0) < M := by rw [hM]; linarith
    nlinarith
  calc |(∫ x in unitCube, θ t x * (φ t x - φ t' x)) +
        ((∫ x in unitCube, θ t x * φ t' x) - ∫ x in unitCube, θ t' x * φ t' x)|
      ≤ |∫ x in unitCube, θ t x * (φ t x - φ t' x)| +
        |(∫ x in unitCube, θ t x * φ t' x) - ∫ x in unitCube, θ t' x * φ t' x| :=
        abs_add_le _ _
    _ < ε := by linarith

/-- **Restart.** A weak solution on `[t₁, t₂]` solves on `[t', t₂]` with datum `θ(t')`. -/
theorem isWeakSolutionOnWith_restart {b : ℝ → Vec 2 → Vec 2} {κ t₁ t₂ t' : ℝ}
    {f : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2}
    (ht' : t' ∈ Set.Icc t₁ t₂) (hθ : IsWeakSolutionOnWith b κ t₁ t₂ f θ Dθ) :
    IsWeakSolutionOnWith b κ t' t₂ (θ t') θ Dθ := by
  have hθ' := hθ
  obtain ⟨hslice, ⟨C, hC⟩, hL2, hDL2, hH1, hint, hcont, hweak⟩ := hθ
  have hIcc : Set.Icc t' t₂ ⊆ Set.Icc t₁ t₂ := Set.Icc_subset_Icc ht'.1 le_rfl
  have hIoo : Set.Ioo t' t₂ ⊆ Set.Ioo t₁ t₂ := Set.Ioo_subset_Ioo ht'.1 le_rfl
  have hmono : volume.restrict (Set.Ioo t' t₂ ×ˢ unitCube) ≤
      volume.restrict (Set.Ioo t₁ t₂ ×ˢ unitCube) :=
    Measure.restrict_mono (Set.prod_mono hIoo le_rfl) le_rfl
  refine ⟨fun t ht => hslice t (hIcc ht), ⟨C, fun t ht => hC t (hIcc ht)⟩,
    hL2.mono_measure hmono, fun i => (hDL2 i).mono_measure hmono,
    ae_restrict_of_ae_restrict_of_subset hIoo hH1, hint.mono_measure hmono,
    fun ψ hψ hψp => (hcont ψ hψ hψp).mono hIcc, fun φ hφ => ?_⟩
  obtain ⟨hsm, hper, hvan⟩ := hφ
  rcases eq_or_lt_of_le ht'.2 with heq | hlt
  · -- `t' = t₂`: both sides vanish
    rw [Set.Ioo_eq_empty (not_lt.2 heq.ge), Set.empty_prod, Measure.restrict_empty,
      integral_zero_measure]
    have hz : (fun x => θ t' x * φ t' x) = fun _ => (0 : ℝ) := by
      funext x
      rw [hvan t' heq.ge x, mul_zero]
    rw [hz, integral_zero]
  -- `t' < t₂`
  obtain ⟨I, hI⟩ : ∃ I : ℝ × Vec 2 → ℝ, ∀ p, I p = -(θ p.1 p.2) * deriv (fun s => φ s p.2) p.1
      + vecDot (b p.1 p.2) (Dθ p.1 p.2) * φ p.1 p.2
      + κ * vecDot (Dθ p.1 p.2) (spaceGrad (φ p.1) p.2) := ⟨_, fun _ => rfl⟩
  have hIint : Integrable I (volume.restrict (Set.Ioo t₁ t₂ ×ˢ unitCube)) :=
    (integrable_weakIntegrand_window hθ' ⟨hsm, hper, hvan⟩).congr
      (Filter.Eventually.of_forall fun p => (hI p).symm)
  obtain ⟨a, ha⟩ : ∃ a : ℝ → ℝ, ∀ t, a t = ∫ x in unitCube, θ t x * φ t x := ⟨_, fun _ => rfl⟩
  have hslc : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (φ t) := fun t =>
    hsm.comp (contDiff_const.prodMk contDiff_id)
  have hacont : ContinuousWithinAt a (Set.Icc t₁ t₂) t' := by
    have h := continuousWithinAt_pairing_of_isWeakSolutionOnWith hθ' hsm.continuous ht'
      (hslc t') (hper t')
    exact h.congr (fun t _ => ha t) (ha t')
  have hθint := memLp_two_integrable_window hL2
  obtain ⟨Cφ, hCφ⟩ := exists_bound_window_cell t₁ t₂ hsm.continuous
  have hmeasC : MeasurableSet (Set.Ioo t₁ t₂ ×ˢ unitCube : Set (ℝ × Vec 2)) :=
    measurableSet_Ioo.prod measurableSet_unitCube'
  have hθφ : Integrable (fun p : ℝ × Vec 2 => θ p.1 p.2 * φ p.1 p.2)
      (volume.restrict (Set.Ioo t₁ t₂ ×ˢ unitCube)) := by
    refine hθint.mul_bdd hsm.continuous.aestronglyMeasurable (c := Cφ) ?_
    filter_upwards [ae_restrict_mem hmeasC] with p hp
    exact hCφ p hp
  have haint : IntegrableOn a (Set.Ioo t₁ t₂) := by
    have h := hθφ
    rw [volume_restrict_prod_eq] at h
    exact h.integral_prod_left.congr (Filter.Eventually.of_forall fun t => (ha t).symm)
  have hkerbd : ∀ δ : ℝ, 0 < δ → ∃ K : ℝ, ∀ t, |kerCut t' δ t| ≤ K := by
    intro δ hδ
    have hcs : HasCompactSupport (kerCut t' δ) := by
      refine HasCompactSupport.intro (isCompact_Icc (a := t') (b := t' + δ)) fun t ht => ?_
      rcases lt_or_ge t t' with h2 | h2
      · exact kerCut_eq_zero_of_lt hδ h2
      · have h1 : t' + δ < t := by
          by_contra hc
          exact ht ⟨h2, not_lt.1 hc⟩
        exact kerCut_eq_zero_of_gt hδ h1
    obtain ⟨K, hK⟩ := kerCut_continuous.bounded_above_of_compact_support hcs
    exact ⟨K, fun t => by simpa using hK t⟩
  -- the identity for each small `δ`
  have hid : ∀ δ : ℝ, 0 < δ →
      ∫ p in Set.Ioo t₁ t₂ ×ˢ unitCube, (1 - etaCut t' δ p.1) * I p =
        ∫ t in Set.Ioo t₁ t₂, a t * kerCut t' δ t := by
    intro δ hδ
    have htest : IsWindowTestFunction t₂ (fun t x => (1 - etaCut t' δ t) * φ t x) := by
      refine ⟨(contDiff_const.sub (etaCut_contDiff.comp contDiff_fst)).mul hsm,
        fun t k x => ?_, fun t ht x => ?_⟩
      · simp only [hper t k x]
      · simp only [hvan t ht x, mul_zero]
    have hw := hweak _ htest
    have hder : ∀ p : ℝ × Vec 2, deriv (fun s => (1 - etaCut t' δ s) * φ s p.2) p.1 =
        kerCut t' δ p.1 * φ p.1 p.2 + (1 - etaCut t' δ p.1) * deriv (fun s => φ s p.2) p.1 := by
      intro p
      have h1 : HasDerivAt (fun s => 1 - etaCut t' δ s) (kerCut t' δ p.1) p.1 := by
        simpa using (hasDerivAt_etaCut (t₁ := t') (δ := δ) p.1).const_sub 1
      have h2 : HasDerivAt (fun s => φ s p.2) (deriv (fun s => φ s p.2) p.1) p.1 :=
        ((hsm.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) p.1).hasDerivAt
      exact (h1.mul h2).deriv
    have hpt : ∀ p : ℝ × Vec 2,
        (-(θ p.1 p.2) * deriv (fun s => (1 - etaCut t' δ s) * φ s p.2) p.1
          + vecDot (b p.1 p.2) (Dθ p.1 p.2) * ((1 - etaCut t' δ p.1) * φ p.1 p.2)
          + κ * vecDot (Dθ p.1 p.2) (spaceGrad (fun y => (1 - etaCut t' δ p.1) * φ p.1 y) p.2)) =
        (1 - etaCut t' δ p.1) * I p - θ p.1 p.2 * φ p.1 p.2 * kerCut t' δ p.1 := by
      intro p
      rw [hder p, spaceGrad_const_mul (hslc p.1), hI p]
      simp only [vecDot, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
      ring
    simp_rw [hpt] at hw
    have hη : Integrable (fun p : ℝ × Vec 2 => (1 - etaCut t' δ p.1) * I p)
        (volume.restrict (Set.Ioo t₁ t₂ ×ˢ unitCube)) := by
      refine hIint.bdd_mul (c := 1) ((continuous_const.sub
        ((etaCut_contDiff (t₁ := t') (δ := δ)).continuous.comp continuous_fst))).aestronglyMeasurable
        (Filter.Eventually.of_forall fun p => ?_)
      have h0 := etaCut_nonneg (t₁ := t') (δ := δ) p.1
      have h1 := etaCut_le_one (t₁ := t') (δ := δ) p.1
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    obtain ⟨K, hK⟩ := hkerbd δ hδ
    have hk : Integrable (fun p : ℝ × Vec 2 => θ p.1 p.2 * φ p.1 p.2 * kerCut t' δ p.1)
        (volume.restrict (Set.Ioo t₁ t₂ ×ˢ unitCube)) :=
      hθφ.mul_bdd (kerCut_continuous.comp continuous_fst).aestronglyMeasurable (c := K)
        (Filter.Eventually.of_forall fun p => by simpa using hK p.1)
    rw [integral_sub hη hk] at hw
    have hrhs : ∫ x in unitCube, f x * ((1 - etaCut t' δ t₁) * φ t₁ x) = 0 := by
      simp [etaCut_of_le ht'.1 hδ]
    rw [hrhs, sub_eq_zero] at hw
    rw [hw]
    have hk' : Integrable (fun p : ℝ × Vec 2 => θ p.1 p.2 * φ p.1 p.2 * kerCut t' δ p.1)
        ((volume.restrict (Set.Ioo t₁ t₂)).prod (volume.restrict unitCube)) := by
      rwa [← volume_restrict_prod_eq]
    rw [volume_restrict_prod_eq, integral_prod _ hk']
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [ha]
    rw [← integral_mul_const]
  -- the left side tends to the weak form on `(t', t₂)`
  have hE : Tendsto (fun δ : ℝ => ∫ p in Set.Ioo t₁ t₂ ×ˢ unitCube, (1 - etaCut t' δ p.1) * I p)
      (𝓝[>] 0) (𝓝 (∫ p in Set.Ioo t₁ t₂ ×ˢ unitCube, {q : ℝ × Vec 2 | t' < q.1}.indicator I p)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun p => ‖I p‖) ?_ ?_ hIint.norm ?_
    · exact Filter.Eventually.of_forall fun δ => ((continuous_const.sub
        ((etaCut_contDiff (t₁ := t') (δ := δ)).continuous.comp
          continuous_fst)).aestronglyMeasurable).mul hIint.aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun δ => Filter.Eventually.of_forall fun p => ?_
      have h0 := etaCut_nonneg (t₁ := t') (δ := δ) p.1
      have h1 := etaCut_le_one (t₁ := t') (δ := δ) p.1
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
    · refine Filter.Eventually.of_forall fun p => ?_
      by_cases hp : t' < p.1
      · rw [Set.indicator_of_mem (show p ∈ {q : ℝ × Vec 2 | t' < q.1} from hp)]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 hp)] with δ hδ
        rw [etaCut_of_ge (by linarith [hδ.2]) hδ.1]
        ring
      · rw [Set.indicator_of_notMem (show p ∉ {q : ℝ × Vec 2 | t' < q.1} from hp)]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with δ hδ
        rw [etaCut_of_le (not_lt.1 hp) hδ]
        ring
  -- the kernel term tends to `a t'`
  have hker1 : ∀ δ : ℝ, 0 < δ → δ ≤ t₂ - t' → ∫ t in Set.Ioo t₁ t₂, kerCut t' δ t = 1 := by
    intro δ hδ hδ2
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (ht'.1.trans hlt.le)]
    have h1 : ∫ t in t₁..t₂, -(kerCut t' δ t) = etaCut t' δ t₂ - etaCut t' δ t₁ :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_etaCut t)
        (kerCut_continuous.neg.intervalIntegrable _ _)
    rw [intervalIntegral.integral_neg, etaCut_of_ge (by linarith) hδ, etaCut_of_le ht'.1 hδ] at h1
    linarith
  have hΛ : Tendsto (fun δ : ℝ => ∫ t in Set.Ioo t₁ t₂, a t * kerCut t' δ t) (𝓝[>] 0)
      (𝓝 (a t')) := by
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨r, hr, hra⟩ := Metric.continuousWithinAt_iff.1 hacont (ε / 2) (half_pos hε)
    refine ⟨min r (t₂ - t'), lt_min hr (by linarith), fun {δ} hδpos hδ => ?_⟩
    have hδ0 : 0 < δ := hδpos
    have hδ' : δ < min r (t₂ - t') := by simpa [Real.dist_eq, abs_of_pos hδ0] using hδ
    have hδr : δ < r := lt_of_lt_of_le hδ' (min_le_left _ _)
    have hδt : δ < t₂ - t' := lt_of_lt_of_le hδ' (min_le_right _ _)
    have hk1 := hker1 δ hδ0 hδt.le
    obtain ⟨K, hK⟩ := hkerbd δ hδ0
    have hkerInt : IntegrableOn (kerCut t' δ) (Set.Ioo t₁ t₂) :=
      (kerCut_continuous.continuousOn.integrableOn_Icc).mono_set Set.Ioo_subset_Icc_self
    have haker : IntegrableOn (fun t => a t * kerCut t' δ t) (Set.Ioo t₁ t₂) :=
      haint.mul_bdd kerCut_continuous.aestronglyMeasurable (c := K)
        (Filter.Eventually.of_forall fun t => by simpa using hK t)
    have hdiff : (∫ t in Set.Ioo t₁ t₂, a t * kerCut t' δ t) - a t' =
        ∫ t in Set.Ioo t₁ t₂, (a t - a t') * kerCut t' δ t := by
      have : ∫ t in Set.Ioo t₁ t₂, (a t - a t') * kerCut t' δ t =
          (∫ t in Set.Ioo t₁ t₂, a t * kerCut t' δ t) -
            ∫ t in Set.Ioo t₁ t₂, a t' * kerCut t' δ t := by
        rw [← integral_sub haker (hkerInt.const_mul (a t'))]
        exact integral_congr_ae (Filter.Eventually.of_forall fun t => by ring)
      rw [this, integral_const_mul, hk1, mul_one]
    rw [Real.dist_eq, hdiff]
    have hle : ‖∫ t in Set.Ioo t₁ t₂, (a t - a t') * kerCut t' δ t‖ ≤
        ∫ t in Set.Ioo t₁ t₂, (ε / 2) * kerCut t' δ t := by
      refine norm_integral_le_of_norm_le (hkerInt.const_mul (ε / 2)) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (kerCut_nonneg hδ0 t)]
      rcases lt_or_ge t t' with h0 | h0
      · simp [kerCut_eq_zero_of_lt hδ0 h0]
      rcases le_or_gt t (t' + δ) with h1 | h1
      · have := hra (x := t) ⟨ht.1.le, ht.2.le⟩ (by
          rw [Real.dist_eq, abs_of_nonneg (by linarith)]
          linarith)
        rw [Real.dist_eq] at this
        exact mul_le_mul_of_nonneg_right this.le (kerCut_nonneg hδ0 t)
      · simp [kerCut_eq_zero_of_gt hδ0 h1]
    rw [integral_const_mul, hk1, mul_one, Real.norm_eq_abs] at hle
    linarith
  -- conclude
  have hconst : (fun δ : ℝ => ∫ p in Set.Ioo t₁ t₂ ×ˢ unitCube, (1 - etaCut t' δ p.1) * I p)
      =ᶠ[𝓝[>] (0 : ℝ)] fun δ => ∫ t in Set.Ioo t₁ t₂, a t * kerCut t' δ t := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact hid δ hδ
  have hlim := tendsto_nhds_unique (hE.congr' hconst) hΛ
  have hset : Set.Ioo t₁ t₂ ×ˢ unitCube ∩ {q : ℝ × Vec 2 | t' < q.1} =
      Set.Ioo t' t₂ ×ˢ unitCube := by
    ext q
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioo, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨⟨-, h2⟩, hx⟩, h3⟩
      exact ⟨⟨h3, h2⟩, hx⟩
    · rintro ⟨⟨h1, h2⟩, hx⟩
      exact ⟨⟨⟨lt_of_le_of_lt ht'.1 h1, h2⟩, hx⟩, h1⟩
  rw [setIntegral_indicator (measurableSet_lt measurable_const measurable_fst), hset] at hlim
  rw [show (∫ p in Set.Ioo t' t₂ ×ˢ unitCube,
      (-(θ p.1 p.2) * deriv (fun s => φ s p.2) p.1
        + vecDot (b p.1 p.2) (Dθ p.1 p.2) * φ p.1 p.2
        + κ * vecDot (Dθ p.1 p.2) (spaceGrad (φ p.1) p.2))) =
      ∫ p in Set.Ioo t' t₂ ×ˢ unitCube, I p from
      integral_congr_ae (Filter.Eventually.of_forall fun p => (hI p).symm), hlim, ha]

end AVRegularity.Applications.Dissipation

end
