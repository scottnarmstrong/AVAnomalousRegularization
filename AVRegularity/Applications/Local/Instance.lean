-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Applications.Local.LabelTrace
import AVRegularity.Applications.Torus.TraceIdent
public import AVRegularity.Applications.Tubes.Periodic
import AVRegularity.Applications.Construction.StreamTail
import AVRegularity.Applications.LocalEnergy.Mollifier
import AVRegularity.Applications.Microscopic.Main
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Tactic.Monotonicity.Lemmas

@[expose] public section
noncomputable section

section
open MeasureTheory Filter Topology Homogenization AVenhance AVRegularity Set
namespace AVRegularity.Applications

/-! # The global part of the local estimate (Step 1 of the proof of Theorem C of the paper)

Euclidean forms of the torus Hölder bound, the almost everywhere comparison of periodic
representatives on discs, and the label trace of the torus solution `u` along the chart:
`∫_{B_ρ} (u(σ, F_σ y) - Θ_u(t, F_t y))² dy → 0` as `σ → t⁻`, from the joint continuity of the
representative `Θ_u` and its Hölder bound. -/

section
/-- The amplitude is bounded by the Hölder norm. -/
theorem abs_le_of_csNormLe {s K : ℝ} {g : Vec 2 → ℝ} (hg : CsNormLe s g K) (x : Vec 2) :
    |g x| ≤ K := by
  have hne : torusDist (0 : Vec 2) (fun _ => 1 / 4) ≠ 0 := by
    have hsmall : eNorm ((0 : Vec 2) - fun _ => 1 / 4) ≤ 1 / 2 := by
      unfold eNorm
      rw [Real.sqrt_le_left (by norm_num)]
      simp [vecNormSq, vecDot]
      norm_num
    have hne0 : (0 : Vec 2) ≠ fun _ => 1 / 4 := by
      intro h; have := congrFun h 0; norm_num at this
    exact (torusDist_pos_of_small hne0 hsmall).ne'
  have h := hg x 0 (fun _ => 1 / 4) hne
  have h1 : 0 ≤ |g 0 - g fun _ => 1 / 4| / torusDist 0 (fun _ => 1 / 4) ^ s :=
    div_nonneg (abs_nonneg _) (Real.rpow_nonneg (torusDist_nonneg _ _) _)
  linarith

/-- Euclidean Hölder bound at all distances: `|g y - g z| ≤ 4 K |y - z|^s` for `0 < s ≤ 1`. -/
theorem csNormLe_holder_euclid {s K : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {g : Vec 2 → ℝ}
    (hg : CsNormLe s g K) (y z : Vec 2) :
    |g y - g z| ≤ 4 * K * eNorm (y - z) ^ s := by
  have hK : 0 ≤ K := csNormLe_K_nonneg hg
  by_cases hd : eNorm (y - z) ≤ 1 / 2
  · have := csNormLe_increment_euclid hs hg hd
    have h0 : 0 ≤ eNorm (y - z) ^ s := Real.rpow_nonneg (eNorm_nonneg _) _
    nlinarith
  · push Not at hd
    have h1 : |g y - g z| ≤ 2 * K := by
      have := abs_sub (g y) (g z)
      linarith [abs_le_of_csNormLe hg y, abs_le_of_csNormLe hg z]
    have h2 : (1 / 2 : ℝ) ≤ eNorm (y - z) ^ s := by
      have : (1 / 2 : ℝ) ^ (1 : ℝ) ≤ (1 / 2 : ℝ) ^ s :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hs1
      have h3 : (1 / 2 : ℝ) ^ s ≤ eNorm (y - z) ^ s :=
        Real.rpow_le_rpow (by norm_num) hd.le hs.le
      simp only [Real.rpow_one] at this
      linarith
    nlinarith

/-- A periodic function equal a.e. on the unit cube to another periodic function is equal a.e.
on every translate of the cube. -/
theorem ae_eq_cubeShift {g h : Vec 2 → ℝ} (n : Fin 2 → ℤ)
    (hg : ∀ x, g (x + AVenhance.latticeShift n) = g x)
    (hh : ∀ x, h (x + AVenhance.latticeShift n) = h x)
    (hae : g =ᵐ[volume.restrict unitCube] h) :
    g =ᵐ[volume.restrict (cubeShift n)] h := by
  set e := MeasurableEquiv.addRight (-AVenhance.latticeShift n)
  have hmp : MeasurePreserving e volume volume :=
    measurePreserving_add_right volume (-AVenhance.latticeShift n)
  have hpre : e ⁻¹' unitCube = cubeShift n := by
    ext x; simp [e, cubeShift, sub_eq_add_neg]
  have hmp' : MeasurePreserving e (volume.restrict (cubeShift n)) (volume.restrict unitCube) := by
    have := hmp.restrict_preimage_emb e.measurableEmbedding unitCube
    rwa [hpre] at this
  have hq := hmp'.quasiMeasurePreserving.ae_eq_comp hae
  filter_upwards [hq] with x hx
  have e1 : g (x + -AVenhance.latticeShift n) = g x := by
    simpa using (hg (x + -AVenhance.latticeShift n)).symm
  have e2 : h (x + -AVenhance.latticeShift n) = h x := by
    simpa using (hh (x + -AVenhance.latticeShift n)).symm
  have hx' : g (x + -AVenhance.latticeShift n) = h (x + -AVenhance.latticeShift n) := hx
  rw [← e1, ← e2]; exact hx'

/-- Two periodic functions equal a.e. on the unit cube are equal a.e. on every disc of radius
at most `1/2`. -/
theorem ae_eq_ball_of_periodic {g h : Vec 2 → ℝ}
    (hg : ∀ (n : Fin 2 → ℤ) x, g (x + AVenhance.latticeShift n) = g x)
    (hh : ∀ (n : Fin 2 → ℤ) x, h (x + AVenhance.latticeShift n) = h x)
    (hae : g =ᵐ[volume.restrict unitCube] h) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 1 / 2) (y : Vec 2) :
    ∀ᵐ x ∂(volume : Measure (Vec 2)), x ∈ euclidBall y ρ → g x = h x := by
  have hcov := ball_ae_subset_cubes hρ hρ2 y
  set I : Finset (Fin 2 → Fin 2) := Finset.univ
  set mv : (Fin 2 → Fin 2) → (Fin 2 → ℤ) := fun e i => ⌊y i - ρ⌋ + ((e i : ℕ) : ℤ)
  have hU : MeasurableSet (⋃ e ∈ I, cubeShift (mv e)) :=
    MeasurableSet.biUnion I.countable_toSet fun e _ => measurableSet_cubeShift _
  have hon : ∀ᵐ x ∂(volume.restrict (⋃ e ∈ I, cubeShift (mv e))), g x = h x := by
    rw [ae_restrict_biUnion_finset_iff]
    exact fun e _ => ae_eq_cubeShift _ (hg _) (hh _) hae
  rw [ae_restrict_iff' hU] at hon
  filter_upwards [hon, hcov] with x h1 h2 hx
  exact h1 (h2 hx)

/-- If `G σ y` is uniformly small on `B`, then `∫_B (G σ y)²` tends to zero. -/
theorem tendsto_integral_sq_of_unif_small {l : Filter ℝ} {B : Set (Vec 2)} (hB : volume B ≠ ⊤)
    (hBm : MeasurableSet B) {G : ℝ → Vec 2 → ℝ}
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ σ in l, ∀ y ∈ B, |G σ y| ≤ ε) :
    Tendsto (fun σ => ∫ y in B, G σ y ^ 2) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  set V : ℝ := (volume B).toReal
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  set ε : ℝ := Real.sqrt (η / (V + 1)) with hε
  have hε0 : 0 < ε := Real.sqrt_pos.2 (by positivity)
  have hε2 : ε ^ 2 = η / (V + 1) := Real.sq_sqrt (by positivity)
  filter_upwards [hsmall ε hε0] with σ hσ
  rw [Real.dist_eq, sub_zero]
  have hnn : 0 ≤ ∫ y in B, G σ y ^ 2 := setIntegral_nonneg hBm fun y _ => sq_nonneg _
  rw [abs_of_nonneg hnn]
  have hb : ∀ y ∈ B, ‖G σ y ^ 2‖ ≤ ε ^ 2 := by
    intro y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hσ y hy) 2
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := B)
    (f := fun y => G σ y ^ 2) (C := ε ^ 2) (lt_top_iff_ne_top.2 hB) hb
  have h2 : ∫ y in B, G σ y ^ 2 ≤ V * ε ^ 2 := by
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs]
    simpa [Measure.real, mul_comm] using this
  calc ∫ y in B, G σ y ^ 2 ≤ V * ε ^ 2 := h2
    _ = V * η / (V + 1) := by rw [hε2]; ring
    _ < η := by
        rw [div_lt_iff₀ (by positivity)]
        nlinarith

variable {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T : ℝ}

/-- A periodic `L²(cube)` function composed with the chart is `L²` on a small label ball. -/
theorem memLp_pullback_of_periodic (ch : IsPipeChart b0 X t₁ T) {σ : ℝ}
    (hσ : σ ∈ Icc (t₁ - 8 * T) t₁) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : 2 * ρ ≤ 1 / 2) {v : Vec 2 → ℝ}
    (hper : IsZ2Periodic v) (hv : MemL2On unitCube v) :
    MemLp (fun y => v (X σ y t₁)) 2 (volume.restrict (euclidBall 0 ρ)) := by
  obtain ⟨hmp, hemb⟩ := chart_mp_emb ch hσ
  have himg : (fun y => X σ y t₁) '' euclidBall (0 : Vec 2) ρ ⊆
      euclidBall (X σ 0 t₁) (2 * ρ) := by
    rintro _ ⟨y, hy, rfl⟩
    have h1 := hLip_chart ch hσ y 0
    have hyn : eNorm (y - 0) < ρ := by
      have : vecNormSq (y - 0) < ρ ^ 2 := hy
      exact eNorm_lt_of_vecNormSq_lt hρ.le this
    have : eNorm (X σ y t₁ - X σ 0 t₁) < 2 * ρ := by linarith
    simpa [euclidBall] using vecNormSq_lt_of_eNorm_lt this
  have hD := memLp_ball_of_periodic hper hv (by positivity : 0 < 2 * ρ) hρ2 (X σ 0 t₁)
  have hD' : MemLp v 2 (volume.restrict ((fun y => X σ y t₁) '' euclidBall (0 : Vec 2) ρ)) :=
    hD.mono_measure (Measure.restrict_mono himg le_rfl)
  exact hD'.comp_measurePreserving (hmp.restrict_image_emb hemb _)

/-- **Label trace of the torus solution.** -/
theorem label_trace_u (ch : IsPipeChart b0 X t₁ T) {Cb : ℝ} (hCb : ∀ τ z, ‖b0 τ z‖ ≤ Cb)
    {t : ℝ} (ht : t ∈ Ioc (t₁ - 8 * T) t₁) {σ₁ σ₂ K s : ℝ} (hσ₁ : σ₁ < t) (htσ₂ : t ≤ σ₂)
    (hs : 0 < s) (hs1 : s ≤ 1) {u Θ : ℝ → Vec 2 → ℝ}
    (hΘc : ContinuousOn (fun p : ℝ × Vec 2 => Θ p.1 p.2) (Icc σ₁ σ₂ ×ˢ univ))
    (hΘ : ∀ σ ∈ Icc σ₁ σ₂, IsZ2Periodic (Θ σ) ∧ Θ σ =ᵐ[volume.restrict unitCube] u σ ∧
      CsNormLe s (Θ σ) K)
    (hup : ∀ σ ∈ Icc σ₁ σ₂, IsZ2Periodic (u σ))
    (hum : ∀ σ ∈ Icc σ₁ σ₂, MemL2On unitCube (u σ)) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hρ₀' : ρ₀ ≤ 1 / 4) :
    (∀ᶠ σ in 𝓝[<] t ⊓ ae volume,
      MemLp (fun y => u σ (X σ y t₁)) 2 (volume.restrict (euclidBall 0 ρ₀))) ∧
    (∀ᶠ σ in 𝓝[<] t ⊓ ae volume,
      IntegrableOn (fun y => (u σ (X σ y t₁) - Θ t (X t y t₁)) ^ 2) (euclidBall 0 ρ₀)) ∧
    Tendsto (fun σ => ∫ y in euclidBall 0 ρ₀, (u σ (X σ y t₁) - Θ t (X t y t₁)) ^ 2)
      (𝓝[<] t ⊓ ae volume) (𝓝 0) := by
  set F : Filter ℝ := 𝓝[<] t ⊓ ae volume with hF
  set B₀ : Set (Vec 2) := euclidBall 0 ρ₀ with hB₀
  have htw : t ∈ Icc (t₁ - 8 * T) t₁ := ⟨ht.1.le, ht.2⟩
  have htI : t ∈ Icc σ₁ σ₂ := ⟨hσ₁.le, htσ₂⟩
  have hK : 0 ≤ K := csNormLe_K_nonneg (hΘ t htI).2.2
  have hCb0 : 0 ≤ Cb := (norm_nonneg _).trans (hCb 0 0)
  set Cb' : ℝ := Cb + 1 with hCb'
  have hCb'pos : 0 < Cb' := by positivity
  have hnear : Ioo (max σ₁ (t₁ - 8 * T)) t ∈ 𝓝[<] t := Ioo_mem_nhdsLT (max_lt hσ₁ ht.1)
  have hevt : ∀ᶠ σ in F, σ ∈ Ioo (max σ₁ (t₁ - 8 * T)) t := mem_inf_of_left hnear
  have hgood : ∀ σ ∈ Ioo (max σ₁ (t₁ - 8 * T)) t,
      σ ∈ Icc σ₁ σ₂ ∧ σ ∈ Icc (t₁ - 8 * T) t₁ := by
    intro σ hσ
    have h1 : σ₁ < σ := (le_max_left _ _).trans_lt hσ.1
    have h2 : t₁ - 8 * T < σ := (le_max_right _ _).trans_lt hσ.1
    exact ⟨⟨h1.le, by linarith [hσ.2]⟩, h2.le, by linarith [hσ.2, ht.2]⟩
  have hB₀m : MeasurableSet B₀ := (isOpen_euclidBall' 0 ρ₀).measurableSet
  have hB₀fin : volume B₀ ≠ ⊤ := euclidBall_volume_ne_top 0 ρ₀
  have hFσcont : ∀ σ, Continuous (fun y => X σ y t₁) := fun σ =>
    ch.smoothF.continuous.comp (continuous_const.prodMk continuous_id)
  -- the image of the ball lies in a disc of radius `2 ρ₀`
  have himg : ∀ σ ∈ Icc (t₁ - 8 * T) t₁,
      (fun y => X σ y t₁) '' B₀ ⊆ euclidBall (X σ 0 t₁) (2 * ρ₀) := by
    rintro σ hσ _ ⟨y, hy, rfl⟩
    have h1 := hLip_chart ch hσ y 0
    have hyn : eNorm (y - 0) < ρ₀ := by
      have : vecNormSq (y - 0) < ρ₀ ^ 2 := hy
      exact eNorm_lt_of_vecNormSq_lt hρ₀.le this
    have : eNorm (X σ y t₁ - X σ 0 t₁) < 2 * ρ₀ := by linarith
    simpa [euclidBall] using vecNormSq_lt_of_eNorm_lt this
  -- (a) `L²` on the pulled-back ball
  have hmemLp : ∀ σ ∈ Ioo (max σ₁ (t₁ - 8 * T)) t,
      MemLp (fun y => u σ (X σ y t₁)) 2 (volume.restrict B₀) := by
    intro σ hσ
    obtain ⟨hσI, hσw⟩ := hgood σ hσ
    obtain ⟨hmp, hemb⟩ := chart_mp_emb ch hσw
    have hD := memLp_ball_of_periodic (hup σ hσI) (hum σ hσI) (by positivity : 0 < 2 * ρ₀)
      (by linarith) (X σ 0 t₁)
    have hD' : MemLp (u σ) 2 (volume.restrict ((fun y => X σ y t₁) '' B₀)) :=
      hD.mono_measure (Measure.restrict_mono (himg σ hσw) le_rfl)
    exact hD'.comp_measurePreserving (hmp.restrict_image_emb hemb B₀)
  -- (b) agreement of the representative
  have hagree : ∀ σ ∈ Ioo (max σ₁ (t₁ - 8 * T)) t,
      ∀ᵐ y ∂(volume : Measure (Vec 2)), y ∈ B₀ → u σ (X σ y t₁) = Θ σ (X σ y t₁) := by
    intro σ hσ
    obtain ⟨hσI, hσw⟩ := hgood σ hσ
    obtain ⟨hmp, hemb⟩ := chart_mp_emb ch hσw
    have h1 := ae_eq_ball_of_periodic (hΘ σ hσI).1 (hup σ hσI) (hΘ σ hσI).2.1
      (by positivity : 0 < 2 * ρ₀) (by linarith) (X σ 0 t₁)
    have h2 := hmp.quasiMeasurePreserving.ae h1
    filter_upwards [h2] with y hy hyB
    exact (hy (himg σ hσw ⟨y, hyB, rfl⟩)).symm
  -- (c) uniform smallness
  set e : ℝ → ℝ := fun σ => 4 * K * (2 * Cb' * |σ - t|) ^ s with he
  have hecont : Continuous e := by
    have h1 : Continuous fun σ : ℝ => 2 * Cb' * |σ - t| := by fun_prop
    exact continuous_const.mul ((Real.continuous_rpow_const hs.le).comp h1)
  have he0 : Tendsto e F (𝓝 0) := by
    have h1 : Tendsto e (𝓝 t) (𝓝 (e t)) := hecont.tendsto t
    have h2 : e t = 0 := by simp [he, Real.zero_rpow hs.ne']
    rw [h2] at h1
    exact h1.mono_left (inf_le_left.trans nhdsWithin_le_nhds)
  have hPc : IsCompact ((fun y => X t y t₁) '' Metric.closedBall (0 : Vec 2) ρ₀) :=
    (isCompact_closedBall (0 : Vec 2) ρ₀).image (hFσcont t)
  have hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ σ in F, ∀ y ∈ B₀,
      |Θ σ (X σ y t₁) - Θ t (X t y t₁)| ≤ ε := by
    intro ε hε
    have hS : IsCompact (Icc σ₁ t ×ˢ ((fun y => X t y t₁) '' Metric.closedBall (0 : Vec 2) ρ₀)) :=
      isCompact_Icc.prod hPc
    have hSsub : Icc σ₁ t ×ˢ ((fun y => X t y t₁) '' Metric.closedBall (0 : Vec 2) ρ₀) ⊆
        Icc σ₁ σ₂ ×ˢ univ := fun p hp => ⟨⟨hp.1.1, hp.1.2.trans htσ₂⟩, trivial⟩
    have hUC := hS.uniformContinuousOn_of_continuous (hΘc.mono hSsub)
    obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1 hUC (ε / 2) (by positivity)
    have hδev : ∀ᶠ σ in F, t - δ < σ :=
      mem_inf_of_left (Filter.mem_of_superset (Ioo_mem_nhdsLT (by linarith : t - δ < t))
        fun σ hσ => hσ.1)
    have hev2 : ∀ᶠ σ in F, e σ < ε / 2 := he0.eventually (gt_mem_nhds (by positivity))
    filter_upwards [hevt, hδev, hev2] with σ hσ hσδ hσe y hy
    obtain ⟨hσI, hσw⟩ := hgood σ hσ
    have hyc : y ∈ Metric.closedBall (0 : Vec 2) ρ₀ := by
      have := euclidBall_subset_closedBall 0 ρ₀ hy
      rwa [abs_of_pos hρ₀] at this
    have hmemP : X t y t₁ ∈ (fun y => X t y t₁) '' Metric.closedBall (0 : Vec 2) ρ₀ :=
      ⟨y, hyc, rfl⟩
    -- space increment
    have hsp : |Θ σ (X σ y t₁) - Θ σ (X t y t₁)| ≤ e σ := by
      refine (csNormLe_holder_euclid hs hs1 (hΘ σ hσI).2.2 _ _).trans ?_
      have := chart_time_close' ch hCb y σ t
      have h2 : eNorm (X σ y t₁ - X t y t₁) ^ s ≤ (2 * Cb' * |σ - t|) ^ s :=
        Real.rpow_le_rpow (eNorm_nonneg _) this hs.le
      simp only [he]
      nlinarith
    -- time increment
    have hS1 : (σ, X t y t₁) ∈ Icc σ₁ t ×ˢ ((fun y => X t y t₁) '' Metric.closedBall (0 : Vec 2) ρ₀) :=
      ⟨⟨(le_max_left _ _).trans_lt hσ.1 |>.le, hσ.2.le⟩, hmemP⟩
    have hS2 : (t, X t y t₁) ∈ Icc σ₁ t ×ˢ ((fun y => X t y t₁) '' Metric.closedBall (0 : Vec 2) ρ₀) :=
      ⟨⟨hσ₁.le, le_rfl⟩, hmemP⟩
    have hd : dist (σ, X t y t₁) (t, X t y t₁) < δ := by
      rw [Prod.dist_eq]
      simp only [dist_self, Real.dist_eq]
      rw [max_eq_left (abs_nonneg _), abs_sub_comm, abs_of_nonneg (by linarith [hσ.2])]
      linarith
    have htm := hδ' _ hS1 _ hS2 hd
    simp only [Real.dist_eq] at htm
    have : |Θ σ (X σ y t₁) - Θ t (X t y t₁)| ≤
        |Θ σ (X σ y t₁) - Θ σ (X t y t₁)| + |Θ σ (X t y t₁) - Θ t (X t y t₁)| := abs_sub_le _ _ _
    linarith
  have hcongr : ∀ σ ∈ Ioo (max σ₁ (t₁ - 8 * T)) t,
      ∫ y in B₀, (Θ σ (X σ y t₁) - Θ t (X t y t₁)) ^ 2 =
        ∫ y in B₀, (u σ (X σ y t₁) - Θ t (X t y t₁)) ^ 2 := by
    intro σ hσ
    refine setIntegral_congr_ae hB₀m ?_
    filter_upwards [hagree σ hσ] with y hy hyB
    simp only [hy hyB]
  have hΘt : Continuous (Θ t) := by
    have := hΘc.comp (s := (univ : Set (Vec 2))) (continuous_const.prodMk continuous_id).continuousOn
      (fun x _ => (⟨htI, trivial⟩ : (t, x) ∈ Icc σ₁ σ₂ ×ˢ (univ : Set (Vec 2))))
    exact continuousOn_univ.1 this
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hevt] with σ hσ using hmemLp σ hσ
  · filter_upwards [hevt] with σ hσ
    have hmem := hmemLp σ hσ
    have : IsFiniteMeasure (volume.restrict B₀) := isFiniteMeasure_restrict.mpr hB₀fin
    have hbd : MemLp (fun y => Θ t (X t y t₁)) 2 (volume.restrict B₀) :=
      MemLp.of_bound ((hΘt.comp (hFσcont t)).aestronglyMeasurable) K
        (Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs]; exact abs_le_of_csNormLe (hΘ t htI).2.2 _)
    exact (hmem.sub hbd).integrable_sq
  · refine (tendsto_integral_sq_of_unif_small (l := F) hB₀fin hB₀m
      (G := fun σ y => Θ σ (X σ y t₁) - Θ t (X t y t₁)) hsmall).congr' ?_
    filter_upwards [hevt] with σ hσ using hcongr σ hσ
end

/-! # Uniformly Hölder functions converging in `L²` converge pointwise

Step 5 of the proof of Theorem C of the paper: functions `G_j` on a Euclidean
ball `B` with `|G_j| ≤ M` and `|G_j y - G_j z| ≤ M |y-z|^s`, converging in `L²(B)` to `U`, converge
pointwise (indeed locally uniformly) to a Hölder continuous representative `g` of `U`. We avoid
the Arzelà–Ascoli theorem: averaging over a small disc shows that `(G_j(y))_j` is Cauchy. -/

/-- Pointwise bound from an `L²` bound and a modulus of continuity. -/
theorem sq_le_of_integral_and_modulus {B : Set (Vec 2)} {y : Vec 2} {δ ω : ℝ}
    (hsub : euclidBall y δ ⊆ B) {D : Vec 2 → ℝ} (hD : IntegrableOn (fun z => D z ^ 2) B)
    (hω : ∀ z ∈ euclidBall y δ, |D y - D z| ≤ ω) :
    (volume (euclidBall y δ)).toReal * D y ^ 2 ≤
      2 * (∫ z in B, D z ^ 2) + 2 * ((volume (euclidBall y δ)).toReal * ω ^ 2) := by
  set Bδ := euclidBall y δ with hBδ
  have hm : MeasurableSet Bδ := (isOpen_euclidBall' y δ).measurableSet
  have hfin : volume Bδ ≠ ⊤ := euclidBall_volume_ne_top y δ
  have hDδ : IntegrableOn (fun z => D z ^ 2) Bδ := hD.mono_set hsub
  have hc : IntegrableOn (fun _ : Vec 2 => D y ^ 2) Bδ := integrableOn_const hfin
  have hc2 : IntegrableOn (fun z => 2 * D z ^ 2 + 2 * ω ^ 2) Bδ :=
    (hDδ.const_mul 2).add (integrableOn_const hfin)
  have h1 : ∫ _ in Bδ, D y ^ 2 ≤ ∫ z in Bδ, (2 * D z ^ 2 + 2 * ω ^ 2) := by
    refine setIntegral_mono_on hc hc2 hm fun z hz => ?_
    have := hω z hz
    have h2 : D y = D z + (D y - D z) := by ring
    nlinarith [sq_nonneg (D z - (D y - D z)), abs_nonneg (D y - D z), sq_abs (D y - D z),
      sq_le_sq' (abs_le.1 this).1 (abs_le.1 this).2]
  rw [setIntegral_const, integral_add (hDδ.const_mul 2) (integrableOn_const hfin),
    integral_const_mul, setIntegral_const] at h1
  simp only [smul_eq_mul] at h1
  have h3 : ∫ z in Bδ, D z ^ 2 ≤ ∫ z in B, D z ^ 2 :=
    setIntegral_mono_set hD (Eventually.of_forall fun z => sq_nonneg _)
      (Eventually.of_forall hsub)
  have h4 : volume.real Bδ = (volume Bδ).toReal := rfl
  rw [h4] at h1
  nlinarith


theorem continuous_eNorm_sub (a : Vec 2) : Continuous (fun x : Vec 2 => eNorm (x - a)) := by
  unfold eNorm
  have : Continuous (fun x : Vec 2 => vecNormSq (x - a)) := by
    unfold vecNormSq vecDot; fun_prop
  exact Real.continuous_sqrt.comp this

/-- A function Hölder continuous in the Euclidean distance on a set is continuous there. -/
theorem continuousOn_of_holder_euclid {B : Set (Vec 2)} {f : Vec 2 → ℝ} {M s : ℝ} (hs : 0 < s)
    (h : ∀ y ∈ B, ∀ z ∈ B, |f y - f z| ≤ M * eNorm (y - z) ^ s) : ContinuousOn f B := by
  intro a ha
  have hφ : Continuous fun x : Vec 2 => M * eNorm (x - a) ^ s :=
    continuous_const.mul ((Real.continuous_rpow_const hs.le).comp (continuous_eNorm_sub a))
  have h0 : Tendsto (fun x : Vec 2 => M * eNorm (x - a) ^ s) (𝓝[B] a) (𝓝 0) := by
    have := (hφ.tendsto a).mono_left (nhdsWithin_le_nhds (s := B))
    simpa [eNorm, vecNormSq, vecDot, Real.zero_rpow hs.ne'] using this
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg)
    ?_ h0)
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [Real.dist_eq]
  exact h x hx a ha


theorem euclidBall_subset_ball (y : Vec 2) {δ : ℝ} (hδ : 0 ≤ δ) :
    euclidBall y δ ⊆ Metric.ball y δ := by
  intro z hz
  have h : vecNormSq (z - y) < δ ^ 2 := hz
  rw [Metric.mem_ball, dist_eq_norm]
  have h' : Real.sqrt (vecNormSq (z - y)) < δ := by
    have := Real.sqrt_lt_sqrt (vecNormSq_nonneg _) h
    rwa [Real.sqrt_sq hδ] at this
  exact lt_of_le_of_lt (norm_le_sqrt_vecNormSq _) h'

theorem eNorm_lt_of_mem_euclidBall {y z : Vec 2} {δ : ℝ} (hδ : 0 ≤ δ) (hz : z ∈ euclidBall y δ) :
    eNorm (y - z) < δ := by
  have h : vecNormSq (z - y) < δ ^ 2 := hz
  have h2 : eNorm (z - y) < δ := eNorm_lt_of_vecNormSq_lt hδ h
  rwa [← eNorm_neg, neg_sub] at h2

/-- `(G_j(y))_j` is Cauchy. -/
theorem cauchySeq_of_holder_l2 {ρ₀ M s : ℝ} (hM : 0 ≤ M) (hs : 0 < s)
    {G : ℕ → Vec 2 → ℝ} {U : Vec 2 → ℝ}
    (hbd : ∀ j, ∀ y ∈ euclidBall (0 : Vec 2) ρ₀, |G j y| ≤ M)
    (hhol : ∀ j, ∀ y ∈ euclidBall (0 : Vec 2) ρ₀, ∀ z ∈ euclidBall (0 : Vec 2) ρ₀,
      |G j y - G j z| ≤ M * eNorm (y - z) ^ s)
    (hU : MemLp U 2 (volume.restrict (euclidBall (0 : Vec 2) ρ₀)))
    (hl2 : Tendsto (fun j => ∫ y in euclidBall (0 : Vec 2) ρ₀, (G j y - U y) ^ 2) atTop (𝓝 0))
    {y : Vec 2} (hy : y ∈ euclidBall (0 : Vec 2) ρ₀) : CauchySeq (fun j => G j y) := by
  set B := euclidBall (0 : Vec 2) ρ₀ with hB
  have hBo : IsOpen B := isOpen_euclidBall' 0 ρ₀
  have hBm : MeasurableSet B := hBo.measurableSet
  have hBfin : volume B ≠ ⊤ := euclidBall_volume_ne_top 0 ρ₀
  have hfinB : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hBfin
  have hGc : ∀ j, ContinuousOn (G j) B := fun j => continuousOn_of_holder_euclid hs (hhol j)
  have hGL : ∀ j, MemLp (fun z => G j z - U z) 2 (volume.restrict B) := fun j =>
    (MemLp.of_bound ((hGc j).aestronglyMeasurable hBm) M
      ((ae_restrict_iff' hBm).2 (Eventually.of_forall fun z hz => by
        rw [Real.norm_eq_abs]; exact hbd j z hz))).sub hU
  have hGI : ∀ j, IntegrableOn (fun z => (G j z - U z) ^ 2) B := fun j => (hGL j).integrable_sq
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨r, hr, hrB⟩ := Metric.isOpen_iff.1 hBo y hy
  set δ₂ : ℝ := (ε / (6 * (M + 1))) ^ (1 / s) with hδ₂
  have hδ₂pos : 0 < δ₂ := Real.rpow_pos_of_pos (by positivity) _
  have hδ₂s : δ₂ ^ s = ε / (6 * (M + 1)) := by
    rw [hδ₂, one_div, Real.rpow_inv_rpow (by positivity) hs.ne']
  set δ : ℝ := min r δ₂ with hδ
  have hδpos : 0 < δ := lt_min hr hδ₂pos
  have hsub : euclidBall y δ ⊆ B := fun z hz =>
    hrB (euclidBall_subset_ball y hδpos.le hz |> fun h => Metric.ball_subset_ball (min_le_left _ _) h)
  set V : ℝ := (volume (euclidBall y δ)).toReal with hV
  have hVpos : 0 < V := by
    have hy' : y ∈ euclidBall y δ := mem_euclidBall_self y hδpos
    have h1 : 0 < volume (euclidBall y δ) :=
      (isOpen_euclidBall' y δ).measure_pos volume ⟨y, hy'⟩
    exact ENNReal.toReal_pos h1.ne' (euclidBall_volume_ne_top y δ)
  set ω : ℝ := 2 * M * δ ^ s with hω
  have hωle : ω ≤ ε / 3 := by
    have h1 : δ ^ s ≤ δ₂ ^ s := Real.rpow_le_rpow hδpos.le (min_le_right _ _) hs.le
    rw [hδ₂s] at h1
    have h2 : 2 * M * (ε / (6 * (M + 1))) ≤ ε / 3 := by
      rw [show 2 * M * (ε / (6 * (M + 1))) = ε / 3 * (M / (M + 1)) by field_simp; ring]
      have : M / (M + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      nlinarith
    calc ω = 2 * M * δ ^ s := rfl
      _ ≤ 2 * M * (ε / (6 * (M + 1))) := by gcongr
      _ ≤ ε / 3 := h2
  have hω0 : 0 ≤ ω := by positivity
  -- choose `N`
  have hsmallN := (hl2.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε ^ 2 * V / 32)))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmallN
  refine ⟨N, fun m hm n hn => ?_⟩
  set D : Vec 2 → ℝ := fun z => G m z - G n z with hD
  have hDI : IntegrableOn (fun z => D z ^ 2) B := by
    -- integrable since `D` is bounded and continuous on `B`
    have hDc : ContinuousOn D B := (hGc m).sub (hGc n)
    have hmeas : AEStronglyMeasurable (fun z => D z ^ 2) (volume.restrict B) :=
      (hDc.pow 2).aestronglyMeasurable hBm
    refine Integrable.of_bound (C := (2 * M) ^ 2) (by simpa [hD] using hmeas)
      ((ae_restrict_iff' hBm).2 (Eventually.of_forall fun z hz => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have : |D z| ≤ 2 * M := by
      have := abs_sub (G m z) (G n z)
      have h1 := hbd m z hz; have h2 := hbd n z hz
      simp only [hD]; linarith
    calc _ = |D z| ^ 2 := (sq_abs _).symm
      _ ≤ (2 * M) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
  have hDint : ∫ z in B, D z ^ 2 ≤ 2 * (∫ z in B, (G m z - U z) ^ 2) +
      2 * (∫ z in B, (U z - G n z) ^ 2) := by
    have hfun : (fun z => D z ^ 2) = fun z => ((G m z - U z) + (U z - G n z)) ^ 2 := by
      funext z; simp only [hD]; ring
    rw [hfun]
    exact integral_sq_add_le (hGI m) ((hGI n).congr_fun (fun z _ => by ring) hBm)
  have hUGn : ∫ z in B, (U z - G n z) ^ 2 = ∫ z in B, (G n z - U z) ^ 2 := by
    congr 1; funext z; ring
  rw [hUGn] at hDint
  have hm' := hN m hm
  have hn' := hN n hn
  have hDsmall : ∫ z in B, D z ^ 2 < ε ^ 2 * V / 8 := by linarith
  have hmod : ∀ z ∈ euclidBall y δ, |D y - D z| ≤ ω := by
    intro z hz
    have hzB : z ∈ B := hsub hz
    have hyz := eNorm_lt_of_mem_euclidBall hδpos.le hz
    have hpow : eNorm (y - z) ^ s ≤ δ ^ s := Real.rpow_le_rpow (eNorm_nonneg _) hyz.le hs.le
    have h1 := hhol m y hy z hzB
    have h2 := hhol n y hy z hzB
    have : |D y - D z| ≤ |G m y - G m z| + |G n y - G n z| := by
      simp only [hD]
      have := abs_sub_le (G m y - G m z) 0 (G n y - G n z)
      calc |G m y - G n y - (G m z - G n z)| = |(G m y - G m z) - (G n y - G n z)| := by ring_nf
        _ ≤ |G m y - G m z| + |G n y - G n z| := abs_sub _ _
    calc |D y - D z| ≤ M * eNorm (y - z) ^ s + M * eNorm (y - z) ^ s := by linarith
      _ ≤ 2 * M * δ ^ s := by nlinarith [mul_le_mul_of_nonneg_left hpow hM]
  have key := sq_le_of_integral_and_modulus hsub hDI hmod
  have hD2 : D y ^ 2 < ε ^ 2 := by
    have h3 : V * D y ^ 2 ≤ 2 * (ε ^ 2 * V / 8) + 2 * (V * ω ^ 2) := by
      have := hDsmall.le
      linarith
    have h4 : ω ^ 2 ≤ (ε / 3) ^ 2 := pow_le_pow_left₀ hω0 hωle 2
    have h5 : V * D y ^ 2 < V * ε ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left h4 hVpos.le]
    exact lt_of_mul_lt_mul_left h5 hVpos.le
  rw [Real.dist_eq]
  have : |D y| < ε := by
    have := abs_lt_of_sq_lt_sq' (by simpa using hD2) hε.le
    exact abs_lt.2 this
  simpa [hD] using this


/-- **Limit of uniformly Hölder functions converging in `L²`.** -/
theorem holder_limit_of_l2 {ρ₀ M s : ℝ} (hM : 0 ≤ M) (hs : 0 < s)
    {G : ℕ → Vec 2 → ℝ} {U : Vec 2 → ℝ}
    (hbd : ∀ j, ∀ y ∈ euclidBall (0 : Vec 2) ρ₀, |G j y| ≤ M)
    (hhol : ∀ j, ∀ y ∈ euclidBall (0 : Vec 2) ρ₀, ∀ z ∈ euclidBall (0 : Vec 2) ρ₀,
      |G j y - G j z| ≤ M * eNorm (y - z) ^ s)
    (hU : MemLp U 2 (volume.restrict (euclidBall (0 : Vec 2) ρ₀)))
    (hl2 : Tendsto (fun j => ∫ y in euclidBall (0 : Vec 2) ρ₀, (G j y - U y) ^ 2) atTop (𝓝 0)) :
    ∃ g : Vec 2 → ℝ, (∀ y ∈ euclidBall (0 : Vec 2) ρ₀, Tendsto (fun j => G j y) atTop (𝓝 (g y))) ∧
      (∀ y ∈ euclidBall (0 : Vec 2) ρ₀, |g y| ≤ M) ∧
      (∀ y ∈ euclidBall (0 : Vec 2) ρ₀, ∀ z ∈ euclidBall (0 : Vec 2) ρ₀,
        |g y - g z| ≤ M * eNorm (y - z) ^ s) ∧
      g =ᵐ[volume.restrict (euclidBall (0 : Vec 2) ρ₀)] U := by
  classical
  set B := euclidBall (0 : Vec 2) ρ₀ with hB
  have hBo : IsOpen B := isOpen_euclidBall' 0 ρ₀
  have hBm : MeasurableSet B := hBo.measurableSet
  have hBfin : volume B ≠ ⊤ := euclidBall_volume_ne_top 0 ρ₀
  have hfinB : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hBfin
  have hcauchy : ∀ y ∈ B, ∃ l, Tendsto (fun j => G j y) atTop (𝓝 l) := fun y hy =>
    cauchySeq_tendsto_of_complete (cauchySeq_of_holder_l2 hM hs hbd hhol hU hl2 hy)
  set g : Vec 2 → ℝ := fun y => if h : y ∈ B then (hcauchy y h).choose else 0 with hg
  have hgt : ∀ y ∈ B, Tendsto (fun j => G j y) atTop (𝓝 (g y)) := by
    intro y hy
    simp only [hg, hy, ↓reduceDIte]
    exact (hcauchy y hy).choose_spec
  have hgbd : ∀ y ∈ B, |g y| ≤ M := fun y hy =>
    le_of_tendsto (hgt y hy).abs (Eventually.of_forall fun j => hbd j y hy)
  have hghol : ∀ y ∈ B, ∀ z ∈ B, |g y - g z| ≤ M * eNorm (y - z) ^ s := fun y hy z hz =>
    le_of_tendsto ((hgt y hy).sub (hgt z hz)).abs (Eventually.of_forall fun j => hhol j y hy z hz)
  refine ⟨g, hgt, hgbd, hghol, ?_⟩
  -- identification with `U`
  have hGc : ∀ j, ContinuousOn (G j) B := fun j => continuousOn_of_holder_euclid hs (hhol j)
  have hgc : ContinuousOn g B := continuousOn_of_holder_euclid hs hghol
  have hGL : ∀ j, MemLp (fun z => G j z - U z) 2 (volume.restrict B) := fun j =>
    (MemLp.of_bound ((hGc j).aestronglyMeasurable hBm) M
      ((ae_restrict_iff' hBm).2 (Eventually.of_forall fun z hz => by
        rw [Real.norm_eq_abs]; exact hbd j z hz))).sub hU
  have hGI : ∀ j, IntegrableOn (fun z => (G j z - U z) ^ 2) B := fun j => (hGL j).integrable_sq
  have hgL : MemLp (fun z => g z - U z) 2 (volume.restrict B) :=
    (MemLp.of_bound (hgc.aestronglyMeasurable hBm) M
      ((ae_restrict_iff' hBm).2 (Eventually.of_forall fun z hz => by
        rw [Real.norm_eq_abs]; exact hgbd z hz))).sub hU
  have hgI : IntegrableOn (fun z => (g z - U z) ^ 2) B := hgL.integrable_sq
  -- dominated convergence for `∫ (G j - g)²`
  have hdct : Tendsto (fun j => ∫ z in B, (G j z - g z) ^ 2) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := volume.restrict B)
      (F := fun j z => (G j z - g z) ^ 2) (f := fun _ => (0 : ℝ))
      (bound := fun _ => (2 * M) ^ 2)
      (fun j => (((hGc j).sub hgc).pow 2).aestronglyMeasurable hBm)
      (integrable_const _)
      (fun j => (ae_restrict_iff' hBm).2 (Eventually.of_forall fun z hz => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
        refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
        have := abs_sub (G j z) (g z)
        linarith [hbd j z hz, hgbd z hz]))
      ((ae_restrict_iff' hBm).2 (Eventually.of_forall fun z hz => by
        have := ((hgt z hz).sub_const (g z)).pow 2
        simpa using this))
    simpa using this
  have hGI' : ∀ j, IntegrableOn (fun z => (g z - G j z) ^ 2) B := fun j =>
    (MemLp.of_bound ((hgc.sub (hGc j)).aestronglyMeasurable hBm) (2 * M)
      ((ae_restrict_iff' hBm).2 (Eventually.of_forall fun z hz => by
        rw [Real.norm_eq_abs]
        show |g z - G j z| ≤ 2 * M
        have := abs_sub (g z) (G j z)
        linarith [hbd j z hz, hgbd z hz]))).integrable_sq
  have hle : ∀ j, ∫ z in B, (g z - U z) ^ 2 ≤
      2 * (∫ z in B, (G j z - g z) ^ 2) + 2 * (∫ z in B, (G j z - U z) ^ 2) := by
    intro j
    have hfun : (fun z => (g z - U z) ^ 2) = fun z => ((g z - G j z) + (G j z - U z)) ^ 2 := by
      funext z; ring
    have hsw : ∫ z in B, (g z - G j z) ^ 2 = ∫ z in B, (G j z - g z) ^ 2 := by
      congr 1; funext z; ring
    rw [hfun]
    have := integral_sq_add_le (hGI' j) (hGI j)
    rw [hsw] at this
    exact this
  have hlim : Tendsto (fun j => 2 * (∫ z in B, (G j z - g z) ^ 2) +
      2 * (∫ z in B, (G j z - U z) ^ 2)) atTop (𝓝 0) := by
    have := (hdct.const_mul 2).add (hl2.const_mul 2)
    simpa using this
  have h0 : ∫ z in B, (g z - U z) ^ 2 ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hle
  have hz : ∫ z in B, (g z - U z) ^ 2 = 0 :=
    le_antisymm h0 (setIntegral_nonneg hBm fun z _ => sq_nonneg _)
  have hae := (integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg _) hgI).1 hz
  filter_upwards [hae] with z hz'
  have : (g z - U z) ^ 2 = 0 := hz'
  have := pow_eq_zero_iff (two_ne_zero) |>.1 this
  linarith

/-! # Smoothing of the difference along tubes, and its label trace

The tube estimate `tube_regularity_aux` applied to the difference `w` in the comparison pipe `𝒪`,
with the containment of translating tubes supplied by `closedTube_subset_innerPipeO`, followed by
the transfer of the physical traces to label coordinates. -/

section
/-- The conclusion of `tube_regularity_aux` for fixed `α`, `s`, `a'`, `b`, `c`, `C`. -/
def TubeStmt (α s : ℝ) (b : ℝ → Vec 2 → Vec 2) (c C : ℝ) : Prop :=
  ∀ κ : ℝ, 0 < κ → ∀ O : Set (ℝ × Vec 2), IsOpen O →
      ∀ (w : ℝ × Vec 2 → ℝ) (Dw : ℝ × Vec 2 → Vec 2), IsLocalWeakSolution b κ O w Dw →
      ∀ A : ℝ, 0 ≤ A → ∀ r : ℝ, 0 < r → r ≤ 1 / 8 → r ≤ c * κ ^ (1 / (1 + α)) →
        (∀ᵐ τ ∂(volume : Measure ℝ), ∀ y : Vec 2, euclidBall y r ⊆ timeSection O τ →
          ∫ x in euclidBall y r, w (τ, x) ^ 2 ≤ A ^ 2) →
      ∀ (t : ℝ) (Kt : Set (Vec 2)),
        (∀ x ∈ Kt, ∀ X : ℝ → Vec 2, IsBackwardTrajectory b X t (r ^ 2 / κ) → X t = x →
          closedTube X t r κ ⊆ O) →
        ∃ W : Vec 2 → ℝ,
          ContinuousOn W (⋃ x ∈ Kt, euclidBall x (r / 4)) ∧
          (∀ x ∈ Kt, Tendsto (fun τ => ∫ y in euclidBall x (r / 4), (w (τ, y) - W y) ^ 2)
            (𝓝[<] t ⊓ ae volume) (𝓝 0)) ∧
          (∀ x ∈ Kt, ∀ᶠ σ in 𝓝[<] t ⊓ ae (volume : Measure ℝ),
            IntegrableOn (fun y => (w (σ, y) - W y) ^ 2) (euclidBall x (r / 4))) ∧
          ∀ x ∈ Kt, ∀ y ∈ Kt, ∀ z ∈ Kt, y ≠ z →
            |W x| + |W y - W z| / Real.sqrt (vecNormSq (y - z)) ^ s ≤ C * r ^ (-1 - s) * A

theorem tubeStmt_exists (hcamp : OcMicroscopicStatement) {α : ℝ} (hα₀ : 0 < α)
    {b : ℝ → Vec 2 → Vec 2} (hb : IsHolderDivFreeVelocity α b) {s a' : ℝ} (hs₀ : 0 < s)
    (hsa : s < a') (ha₁ : a' < 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧ TubeStmt α s b c C := by
  obtain ⟨c, C, hc, hC, H⟩ := tube_regularity_aux hcamp hα₀ hb hs₀ hsa ha₁
  exact ⟨c, C, hc, hC, fun κ hκ O hO w Dw hw A hA r hr hr8 hrc hA' t Kt hKt =>
    (by
      obtain ⟨W, h1, h2, h3, h4⟩ := H κ hκ O hO w Dw hw A hA r hr hr8 hrc hA' t Kt hKt
      exact ⟨W, h1, h2, h3, h4⟩)⟩


variable {b b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T : ℝ}

/-- **Tube estimate and label trace for the difference at one time `t < t₁`.** -/
theorem tube_slice {α s : ℝ} (ch : IsPipeChart b0 X t₁ T)
    (hb0 : AVenhance.Infra.Flow.SmoothPeriodicField b0) {Cb0 V₁ : ℝ}
    (hCb : ∀ τ z, ‖b0 τ z‖ ≤ Cb0) (hV : ∀ τ z, ‖b τ z - b0 τ z‖ ≤ V₁) {c C : ℝ} (hs : 0 < s)
    (hc : TubeStmt α s b c C) (hCnn : 0 ≤ C) {κ : ℝ} (hκ : 0 < κ) {s₀ ρ₀ ρ₁ ρout : ℝ}
    (hs₀ : t₁ - 8 * T ≤ s₀) (hρ₀ : 0 < ρ₀) (hρ₀₁ : ρ₀ < ρ₁) {r A : ℝ} (hA : 0 ≤ A)
    (hr : 0 < r) (hr8 : r ≤ 1 / 8) (hrc : r ≤ c * κ ^ (1 / (1 + α)))
    (hd : 2 * r + 6 * V₁ * (r ^ 2 / κ) ≤ ρout - ρ₁) {w : ℝ × Vec 2 → ℝ} {Dw : ℝ × Vec 2 → Vec 2}
    (hloc : IsLocalWeakSolution b κ (innerPipeO X t₁ s₀ ρout) w Dw)
    (hsec : ∀ᵐ τ ∂(volume : Measure ℝ),
      IntegrableOn (fun x => w (τ, x) ^ 2) (timeSection (innerPipeO X t₁ s₀ ρout) τ) ∧
        ∫ x in timeSection (innerPipeO X t₁ s₀ ρout) τ, w (τ, x) ^ 2 ≤ A ^ 2)
    {t : ℝ} (ht1 : t < t₁) (htl : s₀ < t - r ^ 2 / κ)
    (hwm : ∀ᶠ σ in 𝓝[<] t ⊓ ae volume,
      AEStronglyMeasurable (fun y => w (σ, X σ y t₁)) (volume.restrict (euclidBall 0 ρ₀))) :
    ∃ W : Vec 2 → ℝ,
      ContinuousOn W (⋃ x ∈ (fun y => X t y t₁) '' euclidBall 0 ρ₁, euclidBall x (r / 4)) ∧
      (∀ x ∈ (fun y => X t y t₁) '' euclidBall 0 ρ₁, |W x| ≤ C * r ^ (-1 - s) * A) ∧
      (∀ x ∈ (fun y => X t y t₁) '' euclidBall 0 ρ₁,
        ∀ z ∈ (fun y => X t y t₁) '' euclidBall 0 ρ₁,
        |W x - W z| ≤ (C * r ^ (-1 - s) * A) * eNorm (x - z) ^ s) ∧
      Tendsto (fun σ => ∫ y in euclidBall 0 ρ₀, (w (σ, X σ y t₁) - W (X t y t₁)) ^ 2)
        (𝓝[<] t ⊓ ae volume) (𝓝 0) ∧
      ∀ᶠ σ in 𝓝[<] t ⊓ ae volume,
        IntegrableOn (fun y => (w (σ, X σ y t₁) - W (X t y t₁)) ^ 2) (euclidBall 0 ρ₀) := by
  have hρ₁ : 0 ≤ ρ₁ := by linarith
  have hhr : 0 ≤ r ^ 2 / κ := by positivity
  have hs₀' : t₁ - 8 * T < t := by linarith
  set O := innerPipeO X t₁ s₀ ρout with hO
  have hOo : IsOpen O := isOpen_innerPipeO ch hs₀
  have hA' : ∀ᵐ τ ∂(volume : Measure ℝ), ∀ y : Vec 2, euclidBall y r ⊆ timeSection O τ →
      ∫ x in euclidBall y r, w (τ, x) ^ 2 ≤ A ^ 2 := by
    filter_upwards [hsec] with τ ⟨hint, hle⟩ y hy
    exact (setIntegral_mono_set hint (Eventually.of_forall fun _ => sq_nonneg _)
      (Eventually.of_forall hy)).trans hle
  have hKt : ∀ x ∈ (fun y => X t y t₁) '' euclidBall 0 ρ₁, ∀ Xt : ℝ → Vec 2,
      IsBackwardTrajectory b Xt t (r ^ 2 / κ) → Xt t = x → closedTube Xt t r κ ⊆ O := by
    rintro x ⟨y, hy, rfl⟩ Xt hXt hXt0
    have hy' : vecNormSq y < ρ₁ ^ 2 := by simpa [euclidBall] using hy
    exact closedTube_subset_innerPipeO hb0 ch hV hs₀ hκ hr hd htl ht1 hy' hρ₁ hXt hXt0
  obtain ⟨W, hWc, htr, hint, hbound⟩ := hc κ hκ O hOo w Dw hloc A hA r hr hr8 hrc hA' t _ hKt
  have hM : 0 ≤ C * r ^ (-1 - s) * A := by positivity
  have hWh : ∀ x ∈ (fun y => X t y t₁) '' euclidBall 0 ρ₁,
      ∀ z ∈ (fun y => X t y t₁) '' euclidBall 0 ρ₁,
      |W x - W z| ≤ (C * r ^ (-1 - s) * A) * eNorm (x - z) ^ s := by
    intro x hx z hz
    by_cases hxz : x = z
    · subst hxz
      simp [eNorm, vecNormSq, vecDot, Real.zero_rpow hs.ne']
    · have h1 := hbound x hx x hx z hz hxz
      have hpos : 0 < eNorm (x - z) := by
        unfold eNorm
        exact Real.sqrt_pos.2 (vecNormSq_pos_of_ne hxz)
      have hpow : 0 < eNorm (x - z) ^ s := Real.rpow_pos_of_pos hpos s
      have h2 : |W x - W z| / eNorm (x - z) ^ s ≤ C * r ^ (-1 - s) * A := by
        have := abs_nonneg (W x)
        have h3 : Real.sqrt (vecNormSq (x - z)) ^ s = eNorm (x - z) ^ s := rfl
        rw [h3] at h1
        linarith
      rw [div_le_iff₀ hpow] at h2
      linarith
  -- a pair of distinct points of `K`
  have hpair : ∃ y ∈ (fun y => X t y t₁) '' euclidBall 0 ρ₁,
      ∃ z ∈ (fun y => X t y t₁) '' euclidBall 0 ρ₁, y ≠ z := by
    have hρ₁pos : 0 < ρ₁ := by linarith
    set a : Vec 2 := fun i => if i = 0 then ρ₁ / 2 else 0 with ha
    have ha0 : a ≠ 0 := by
      intro h
      have := congrFun h 0
      simp [ha] at this
      linarith
    have haB : a ∈ euclidBall (0 : Vec 2) ρ₁ := by
      simp only [euclidBall, mem_ofPred_eq, sub_zero]
      simp [vecNormSq, vecDot, ha]
      nlinarith
    have h0B : (0 : Vec 2) ∈ euclidBall (0 : Vec 2) ρ₁ := mem_euclidBall_self 0 hρ₁pos
    refine ⟨X t 0 t₁, ⟨0, h0B, rfl⟩, X t a t₁, ⟨a, haB, rfl⟩, fun h => ha0 ?_⟩
    have := congrArg (fun x => X t₁ x t) h
    simp only [ch.left t ⟨hs₀'.le, ht1.le⟩] at this
    exact this.symm
  obtain ⟨y₀, hy₀, z₀, hz₀, hyz₀⟩ := hpair
  have hWb : ∀ x ∈ (fun y => X t y t₁) '' euclidBall 0 ρ₁, |W x| ≤ C * r ^ (-1 - s) * A := by
    intro x hx
    have h1 := hbound x hx y₀ hy₀ z₀ hz₀ hyz₀
    have h2 : 0 ≤ |W y₀ - W z₀| / Real.sqrt (vecNormSq (y₀ - z₀)) ^ s :=
      div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
    linarith
  refine ⟨W, hWc, hWb, hWh, ?_⟩
  have hwm' := label_trace_w ch hCb (t := t) ⟨hs₀', ht1.le⟩ (ρ₀ := ρ₀) (ρ₁ := ρ₁) (r := r)
    (s := s) (M := C * r ^ (-1 - s) * A) hρ₀.le hρ₀₁ hr hs hM (w := fun σ y => w (σ, y)) (W := W)
    hWc hWh htr hint hwm
  exact hwm'


/-- **The slice at time `t < t₁`**: a continuous representative `Θ_t = W + Θ_u(t)` of the trace of
`θ(t)`, with amplitude and Hölder bounds, and the trace in label coordinates. -/
theorem slice_below {α s : ℝ} (ch : IsPipeChart b0 X t₁ T)
    (hb0 : AVenhance.Infra.Flow.SmoothPeriodicField b0) {Cb0 V₁ : ℝ}
    (hCb : ∀ τ z, ‖b0 τ z‖ ≤ Cb0) (hV : ∀ τ z, ‖b τ z - b0 τ z‖ ≤ V₁) {c C : ℝ} (hs : 0 < s)
    (hs1 : s ≤ 1) (hc : TubeStmt α s b c C) (hCnn : 0 ≤ C) {κ : ℝ} (hκ : 0 < κ)
    {s₀ ρ₀ ρ₁ ρout : ℝ} (hs₀ : t₁ - 8 * T ≤ s₀) (hρ₀ : 0 < ρ₀) (hρ₀' : ρ₀ ≤ 1 / 4)
    (hρ₀₁ : ρ₀ < ρ₁) {r A : ℝ} (hA : 0 ≤ A) (hr : 0 < r) (hr8 : r ≤ 1 / 8)
    (hrc : r ≤ c * κ ^ (1 / (1 + α))) (hd : 2 * r + 6 * V₁ * (r ^ 2 / κ) ≤ ρout - ρ₁)
    {θ u : ℝ → Vec 2 → ℝ} {Dw : ℝ × Vec 2 → Vec 2}
    (hloc : IsLocalWeakSolution b κ (innerPipeO X t₁ s₀ ρout)
      (fun p => θ p.1 p.2 - u p.1 p.2) Dw)
    (hsec : ∀ᵐ τ ∂(volume : Measure ℝ),
      IntegrableOn (fun x => (θ τ x - u τ x) ^ 2) (timeSection (innerPipeO X t₁ s₀ ρout) τ) ∧
        ∫ x in timeSection (innerPipeO X t₁ s₀ ρout) τ, (θ τ x - u τ x) ^ 2 ≤ A ^ 2)
    {t : ℝ} (ht1 : t < t₁) (htl : s₀ < t - r ^ 2 / κ)
    (hθm : ∀ᶠ σ in 𝓝[<] t ⊓ ae volume,
      AEStronglyMeasurable (fun y => θ σ (X σ y t₁)) (volume.restrict (euclidBall 0 ρ₀)))
    {σ₁ σ₂ Kg : ℝ} (hσ₁ : σ₁ < t) (htσ₂ : t ≤ σ₂) {Θ : ℝ → Vec 2 → ℝ}
    (hΘc : ContinuousOn (fun p : ℝ × Vec 2 => Θ p.1 p.2) (Icc σ₁ σ₂ ×ˢ univ))
    (hΘ : ∀ σ ∈ Icc σ₁ σ₂, IsZ2Periodic (Θ σ) ∧ Θ σ =ᵐ[volume.restrict unitCube] u σ ∧
      CsNormLe s (Θ σ) Kg)
    (hup : ∀ σ ∈ Icc σ₁ σ₂, IsZ2Periodic (u σ))
    (hum : ∀ σ ∈ Icc σ₁ σ₂, MemL2On unitCube (u σ)) :
    ∃ Θt : Vec 2 → ℝ,
      ContinuousOn Θt ((fun y => X t y t₁) '' euclidBall 0 ρ₁) ∧
      (∀ x ∈ (fun y => X t y t₁) '' euclidBall 0 ρ₁,
        |Θt x| ≤ C * r ^ (-1 - s) * A + 4 * Kg) ∧
      (∀ x ∈ (fun y => X t y t₁) '' euclidBall 0 ρ₁,
        ∀ z ∈ (fun y => X t y t₁) '' euclidBall 0 ρ₁,
        |Θt x - Θt z| ≤ (C * r ^ (-1 - s) * A + 4 * Kg) * eNorm (x - z) ^ s) ∧
      Tendsto (fun σ => ∫ y in euclidBall 0 ρ₀, (θ σ (X σ y t₁) - Θt (X t y t₁)) ^ 2)
        (𝓝[<] t ⊓ ae volume) (𝓝 0) := by
  have hs₀' : t₁ - 8 * T < t := by
    have : 0 ≤ r ^ 2 / κ := by positivity
    linarith
  have ht : t ∈ Ioc (t₁ - 8 * T) t₁ := ⟨hs₀', ht1.le⟩
  have hKg : 0 ≤ Kg := csNormLe_K_nonneg (hΘ t ⟨hσ₁.le, htσ₂⟩).2.2
  obtain ⟨hu1, hu2, hu3⟩ := label_trace_u ch hCb ht hσ₁ htσ₂ hs hs1 hΘc hΘ hup hum hρ₀ hρ₀'
  have hwm : ∀ᶠ σ in 𝓝[<] t ⊓ ae volume,
      AEStronglyMeasurable (fun y => (fun p : ℝ × Vec 2 => θ p.1 p.2 - u p.1 p.2)
        (σ, X σ y t₁)) (volume.restrict (euclidBall 0 ρ₀)) := by
    filter_upwards [hθm, hu1] with σ h1 h2
    exact h1.sub h2.aestronglyMeasurable
  obtain ⟨W, hWc, hWb, hWh, hW3, hW4⟩ := tube_slice ch hb0 hCb hV hs hc hCnn hκ hs₀ hρ₀ hρ₀₁ hA hr
    hr8 hrc hd hloc hsec ht1 htl hwm
  refine ⟨fun x => W x + Θ t x, ?_, ?_, ?_, ?_⟩
  · have hΘt : Continuous (Θ t) := by
      have := hΘc.comp (s := (univ : Set (Vec 2)))
        (continuous_const.prodMk continuous_id).continuousOn
        (fun x _ => (⟨⟨hσ₁.le, htσ₂⟩, trivial⟩ : (t, x) ∈ Icc σ₁ σ₂ ×ˢ (univ : Set (Vec 2))))
      exact continuousOn_univ.1 this
    refine (hWc.mono ?_).add hΘt.continuousOn
    intro x hx
    simp only [mem_iUnion]
    exact ⟨x, hx, mem_euclidBall_self x (by linarith [hr])⟩
  · intro x hx
    have h1 := hWb x hx
    have h2 := abs_le_of_csNormLe (hΘ t ⟨hσ₁.le, htσ₂⟩).2.2 x
    have h3 := abs_add_le (W x) (Θ t x)
    linarith
  · intro x hx z hz
    have h1 := hWh x hx z hz
    have h2 := csNormLe_holder_euclid hs hs1 (hΘ t ⟨hσ₁.le, htσ₂⟩).2.2 x z
    have h3 : |(W x + Θ t x) - (W z + Θ t z)| ≤ |W x - W z| + |Θ t x - Θ t z| := by
      have := abs_add_le (W x - W z) (Θ t x - Θ t z)
      calc _ = |(W x - W z) + (Θ t x - Θ t z)| := by ring_nf
        _ ≤ _ := this
    have h4 : 0 ≤ eNorm (x - z) ^ s := Real.rpow_nonneg (eNorm_nonneg _) _
    nlinarith
  · -- the trace in label coordinates
    have hsum : ∀ᶠ σ in 𝓝[<] t ⊓ ae volume,
        ∫ y in euclidBall 0 ρ₀, (θ σ (X σ y t₁) - (W (X t y t₁) + Θ t (X t y t₁))) ^ 2 ≤
          2 * (∫ y in euclidBall 0 ρ₀, (θ σ (X σ y t₁) - u σ (X σ y t₁) - W (X t y t₁)) ^ 2) +
          2 * (∫ y in euclidBall 0 ρ₀, (u σ (X σ y t₁) - Θ t (X t y t₁)) ^ 2) := by
      filter_upwards [hW4, hu2] with σ h1 h2
      have := integral_sq_add_le (S := euclidBall 0 ρ₀)
        (a := fun y => θ σ (X σ y t₁) - u σ (X σ y t₁) - W (X t y t₁))
        (b := fun y => u σ (X σ y t₁) - Θ t (X t y t₁)) (by simpa using h1) h2
      refine le_of_eq_of_le ?_ this
      congr 1
      funext y; ring
    have hlim : Tendsto (fun σ => 2 * (∫ y in euclidBall 0 ρ₀,
        (θ σ (X σ y t₁) - u σ (X σ y t₁) - W (X t y t₁)) ^ 2) +
        2 * (∫ y in euclidBall 0 ρ₀, (u σ (X σ y t₁) - Θ t (X t y t₁)) ^ 2))
        (𝓝[<] t ⊓ ae volume) (𝓝 0) := by
      have := (hW3.const_mul 2).add (hu3.const_mul 2)
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun σ => setIntegral_nonneg
        (isOpen_euclidBall' 0 ρ₀).measurableSet fun y _ => sq_nonneg _) hsum
end

/-! # The top time `t₁` from below (Step 5 of the proof of Theorem C of the paper)

Let `Θ_t`, `t < t₁`, be the slices with common amplitude and
Hölder bounds, and let `U` be the label trace of `θ` at `t₁` (from below). The functions
`G_j(y) = Θ_{t_j}(F_{t_j} y)` for `t_j ↑ t₁` converge in `L²(B_{ρ₀})` to `U`, since both are limits
of the same slices, so by `holder_limit_of_l2` they converge to a continuous representative
`g` of `U`, which inherits the bounds in physical distance as `F_{t_j} → F_{t₁} = id`. -/

section
/-- Eventual statements along `𝓝[<] t ⊓ ae` are statements on a left interval, a.e. -/
theorem exists_Ioo_of_eventually {t : ℝ} {P : ℝ → Prop}
    (h : ∀ᶠ σ in 𝓝[<] t ⊓ ae (volume : Measure ℝ), P σ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᵐ σ ∂(volume : Measure ℝ), σ ∈ Ioo (t - δ) t → P σ := by
  obtain ⟨s₁, hs₁, s₂, hs₂, hsub⟩ := Filter.mem_inf_iff_superset.1 h
  obtain ⟨l, hl, hIoo⟩ := mem_nhdsLT_iff_exists_Ioo_subset.1 hs₁
  refine ⟨t - l, by linarith [show l < t from hl], ?_⟩
  filter_upwards [hs₂] with σ hσ hσI
  refine hsub ⟨hIoo ?_, hσ⟩
  exact ⟨by simpa using hσI.1, hσI.2⟩

theorem eventually_of_Ioo {t : ℝ} {P : ℝ → Prop} {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ᵐ σ ∂(volume : Measure ℝ), σ ∈ Ioo (t - δ) t → P σ) :
    ∀ᶠ σ in 𝓝[<] t ⊓ ae (volume : Measure ℝ), P σ := by
  have h1 : Ioo (t - δ) t ∈ 𝓝[<] t := Ioo_mem_nhdsLT (by linarith)
  filter_upwards [mem_inf_of_left h1, mem_inf_of_right h] with σ h2 h3
  exact h3 h2


/-- **`L²` convergence of the slice representatives to the top trace.** Abstract version: `Φ σ`
is the pulled-back slice at time `σ`, `G j` the `L²` trace of `Φ` at the time `tj j ↑ t₁`, and `Ut`
the trace at `t₁`. -/
theorem l2_limit_of_traces {B₀ : Set (Vec 2)} (hB₀m : MeasurableSet B₀) {t₁ D : ℝ}
    {Φ : ℝ → Vec 2 → ℝ} {G : ℕ → Vec 2 → ℝ} {Ut : Vec 2 → ℝ} {tj : ℕ → ℝ}
    (hΦL2 : ∀ᵐ σ ∂(volume : Measure ℝ), σ ∈ Ioo (t₁ - D) t₁ →
      MemLp (Φ σ) 2 (volume.restrict B₀))
    (hGL2 : ∀ j, MemLp (G j) 2 (volume.restrict B₀)) (hUtL2 : MemLp Ut 2 (volume.restrict B₀))
    (htj1 : ∀ j, t₁ - D < tj j) (htj2 : ∀ j, tj j < t₁)
    (hΘ3 : ∀ j, Tendsto (fun σ => ∫ y in B₀, (Φ σ y - G j y) ^ 2)
      (𝓝[<] (tj j) ⊓ ae volume) (𝓝 0))
    (hUttr : Tendsto (fun σ => ∫ y in B₀, (Φ σ y - Ut y) ^ 2) (𝓝[<] t₁ ⊓ ae volume) (𝓝 0))
    (htjlim : Tendsto tj atTop (𝓝 t₁)) :
    Tendsto (fun j => ∫ y in B₀, (G j y - Ut y) ^ 2) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := exists_Ioo_of_eventually
    (hUttr.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 4)))
  have hev : ∀ᶠ j in atTop, t₁ - δ < tj j :=
    htjlim.eventually (lt_mem_nhds (by linarith : t₁ - δ < t₁))
  obtain ⟨J, hJ⟩ := eventually_atTop.1 hev
  refine ⟨J, fun j hj => ?_⟩
  have hjδ : t₁ - δ < tj j := hJ j hj
  have := nhdsLT_inf_ae_neBot (tj j)
  have hP : ∀ᶠ σ in 𝓝[<] (tj j) ⊓ ae (volume : Measure ℝ),
      ∫ y in B₀, (Φ σ y - Ut y) ^ 2 < ε / 4 := by
    refine eventually_of_Ioo (δ := tj j - (t₁ - δ)) (by linarith) ?_
    filter_upwards [hδ'] with σ h1 h2
    exact h1 ⟨by linarith [h2.1], by linarith [h2.2, htj2 j]⟩
  have hQ : ∀ᶠ σ in 𝓝[<] (tj j) ⊓ ae (volume : Measure ℝ),
      ∫ y in B₀, (Φ σ y - G j y) ^ 2 < ε / 4 :=
    (hΘ3 j).eventually (gt_mem_nhds (by positivity))
  have hI : ∀ᶠ σ in 𝓝[<] (tj j) ⊓ ae (volume : Measure ℝ), MemLp (Φ σ) 2 (volume.restrict B₀) := by
    refine eventually_of_Ioo (δ := tj j - (t₁ - D)) (by linarith [htj1 j]) ?_
    filter_upwards [hΦL2] with σ h1 h2
    exact h1 ⟨by linarith [h2.1], by linarith [h2.2, htj2 j]⟩
  obtain ⟨σ, h1, h2, h3⟩ := (hP.and (hQ.and hI)).exists
  have hi1 : IntegrableOn (fun y => (Φ σ y - G j y) ^ 2) B₀ :=
    (h3.sub (hGL2 j)).integrable_sq
  have hi2 : IntegrableOn (fun y => (Φ σ y - Ut y) ^ 2) B₀ := (h3.sub hUtL2).integrable_sq
  have hi1' : IntegrableOn (fun y => (G j y - Φ σ y) ^ 2) B₀ :=
    hi1.congr_fun (fun y _ => by ring) hB₀m
  have hsum := integral_sq_add_le (S := B₀) hi1' hi2
  have hfun : (fun y => (G j y - Ut y) ^ 2) = fun y => ((G j y - Φ σ y) + (Φ σ y - Ut y)) ^ 2 := by
    funext y; ring
  have hsw : ∫ y in B₀, (G j y - Φ σ y) ^ 2 = ∫ y in B₀, (Φ σ y - G j y) ^ 2 := by
    congr 1; funext y; ring
  rw [Real.dist_eq, sub_zero]
  have hnn : 0 ≤ ∫ y in B₀, (G j y - Ut y) ^ 2 := setIntegral_nonneg hB₀m fun y _ => sq_nonneg _
  rw [abs_of_nonneg hnn, hfun]
  rw [hsw] at hsum
  linarith

variable {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T : ℝ}

/-- A slice with amplitude and Hölder bounds pulls back to a uniformly Hölder function of the
label. -/
theorem pullback_holder (ch : IsPipeChart b0 X t₁ T) {t ρ₀ s Bd : ℝ} (ht : t ∈ Icc (t₁ - 8 * T) t₁)
    (hs : 0 < s) (hs1 : s ≤ 1) (hBd : 0 ≤ Bd) {Θ : Vec 2 → ℝ}
    (h2 : ∀ x ∈ (fun y => X t y t₁) '' euclidBall 0 ρ₀,
      ∀ z ∈ (fun y => X t y t₁) '' euclidBall 0 ρ₀, |Θ x - Θ z| ≤ Bd * eNorm (x - z) ^ s) :
    ∀ y ∈ euclidBall (0 : Vec 2) ρ₀, ∀ z ∈ euclidBall (0 : Vec 2) ρ₀,
      |Θ (X t y t₁) - Θ (X t z t₁)| ≤ (2 * Bd) * eNorm (y - z) ^ s := by
  intro y hy z hz
  have h1 := h2 _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
  have h2' := hLip_chart ch ht y z
  have h2s : (2 : ℝ) ^ s ≤ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hs1
    simpa using this
  have h3 : eNorm (X t y t₁ - X t z t₁) ^ s ≤ (2 * eNorm (y - z)) ^ s :=
    Real.rpow_le_rpow (eNorm_nonneg _) h2' hs.le
  rw [Real.mul_rpow (by norm_num) (eNorm_nonneg _)] at h3
  have h4 : 0 ≤ eNorm (y - z) ^ s := Real.rpow_nonneg (eNorm_nonneg _) _
  calc |Θ (X t y t₁) - Θ (X t z t₁)| ≤ Bd * eNorm (X t y t₁ - X t z t₁) ^ s := h1
    _ ≤ Bd * (2 ^ s * eNorm (y - z) ^ s) := by gcongr
    _ ≤ (2 * Bd) * eNorm (y - z) ^ s := by nlinarith [mul_le_mul_of_nonneg_right h2s h4]


theorem continuous_eNorm' : Continuous fun v : Vec 2 => eNorm v := by
  unfold eNorm
  have : Continuous fun v : Vec 2 => vecNormSq v := by
    unfold vecNormSq vecDot; fun_prop
  exact Real.continuous_sqrt.comp this

/-- Bounds pass to the pointwise limit, with the chart converging to the identity. -/
theorem limit_bounds_physical {B₀ : Set (Vec 2)} {s Bd : ℝ} (hs : 0 < s) {G : ℕ → Vec 2 → ℝ}
    {g : Vec 2 → ℝ} {Fj : ℕ → Vec 2 → Vec 2}
    (hF : ∀ y, Tendsto (fun j => Fj j y) atTop (𝓝 y))
    (hgt : ∀ y ∈ B₀, Tendsto (fun j => G j y) atTop (𝓝 (g y)))
    (hbd : ∀ j, ∀ y ∈ B₀, |G j y| ≤ Bd)
    (hhol : ∀ j, ∀ y ∈ B₀, ∀ z ∈ B₀, |G j y - G j z| ≤ Bd * eNorm (Fj j y - Fj j z) ^ s) :
    (∀ y ∈ B₀, |g y| ≤ Bd) ∧ ∀ y ∈ B₀, ∀ z ∈ B₀, |g y - g z| ≤ Bd * eNorm (y - z) ^ s := by
  refine ⟨fun y hy => le_of_tendsto (hgt y hy).abs (Eventually.of_forall fun j => hbd j y hy),
    fun y hy z hz => ?_⟩
  have hlim1 : Tendsto (fun j => |G j y - G j z|) atTop (𝓝 |g y - g z|) :=
    ((hgt y hy).sub (hgt z hz)).abs
  have hcont : Continuous fun v : Vec 2 => Bd * eNorm v ^ s :=
    continuous_const.mul ((Real.continuous_rpow_const hs.le).comp continuous_eNorm')
  have hdiff : Tendsto (fun j => Fj j y - Fj j z) atTop (𝓝 (y - z)) := (hF y).sub (hF z)
  have hlim2 : Tendsto (fun j => Bd * eNorm (Fj j y - Fj j z) ^ s) atTop
      (𝓝 (Bd * eNorm (y - z) ^ s)) := (hcont.tendsto (y - z)).comp hdiff
  exact le_of_tendsto_of_tendsto hlim1 hlim2 (Eventually.of_forall fun j => hhol j y hy z hz)

/-- **The top time from below.** -/
theorem slice_top (ch : IsPipeChart b0 X t₁ T) {D ρ₀ s Bd : ℝ} (hD : 0 < D) (hDT : D ≤ 8 * T)
    (hs : 0 < s) (hs1 : s ≤ 1) (hBd : 0 ≤ Bd) {θ : ℝ → Vec 2 → ℝ}
    (hθL2 : ∀ᵐ σ ∂(volume : Measure ℝ), σ ∈ Ioo (t₁ - D) t₁ →
      MemLp (fun y => θ σ (X σ y t₁)) 2 (volume.restrict (euclidBall 0 ρ₀)))
    (hfam : ∀ t ∈ Ico (t₁ - D) t₁, ∃ Θt : Vec 2 → ℝ,
      (∀ x ∈ (fun y => X t y t₁) '' euclidBall 0 ρ₀, |Θt x| ≤ Bd) ∧
      (∀ x ∈ (fun y => X t y t₁) '' euclidBall 0 ρ₀,
        ∀ z ∈ (fun y => X t y t₁) '' euclidBall 0 ρ₀,
        |Θt x - Θt z| ≤ Bd * eNorm (x - z) ^ s) ∧
      Tendsto (fun σ => ∫ y in euclidBall 0 ρ₀, (θ σ (X σ y t₁) - Θt (X t y t₁)) ^ 2)
        (𝓝[<] t ⊓ ae volume) (𝓝 0))
    (hUt : ∃ Ut : Vec 2 → ℝ, MemL2On (euclidBall 0 ρ₀) Ut ∧
      Tendsto (fun σ => ∫ y in euclidBall 0 ρ₀, (θ σ (X σ y t₁) - Ut y) ^ 2)
        (𝓝[<] t₁ ⊓ ae volume) (𝓝 0)) :
    ∃ g : Vec 2 → ℝ, ContinuousOn g (euclidBall 0 ρ₀) ∧
      (∀ y ∈ euclidBall 0 ρ₀, |g y| ≤ Bd) ∧
      (∀ y ∈ euclidBall 0 ρ₀, ∀ z ∈ euclidBall 0 ρ₀, |g y - g z| ≤ Bd * eNorm (y - z) ^ s) ∧
      Tendsto (fun σ => ∫ y in euclidBall 0 ρ₀, (θ σ (X σ y t₁) - g (X t₁ y t₁)) ^ 2)
        (𝓝[<] t₁ ⊓ ae volume) (𝓝 0) := by
  have hB₀m : MeasurableSet (euclidBall (0 : Vec 2) ρ₀) := (isOpen_euclidBall' 0 ρ₀).measurableSet
  have hB₀fin : volume (euclidBall (0 : Vec 2) ρ₀) ≠ ⊤ := euclidBall_volume_ne_top 0 ρ₀
  obtain ⟨Ut, hUtL2, hUttr⟩ := hUt
  -- the sequence of times
  obtain ⟨tj, htjI, htjlim⟩ : ∃ tj : ℕ → ℝ, (∀ j, tj j ∈ Ico (t₁ - D) t₁ ∧ t₁ - D < tj j) ∧
      Tendsto tj atTop (𝓝 t₁) := by
    refine ⟨fun j => t₁ - D / ((j : ℝ) + 2), fun j => ?_, ?_⟩
    · have hpos : 0 < D / ((j : ℝ) + 2) := by positivity
      have hlt : D / ((j : ℝ) + 2) < D := by
        rw [div_lt_iff₀ (by positivity)]
        have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        nlinarith
      exact ⟨⟨by linarith, by linarith⟩, by linarith⟩
    · have h0 : Tendsto (fun j : ℕ => D / ((j : ℝ) + 2)) atTop (𝓝 0) :=
        Tendsto.div_atTop tendsto_const_nhds
          (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
      simpa using (tendsto_const_nhds (x := t₁)).sub h0
  have htjw : ∀ j, tj j ∈ Icc (t₁ - 8 * T) t₁ := fun j =>
    ⟨by linarith [(htjI j).2], (htjI j).1.2.le⟩
  choose Θ hΘ1 hΘ2 hΘ3 using fun j => hfam (tj j) (htjI j).1
  have hGbd : ∀ j, ∀ y ∈ euclidBall (0 : Vec 2) ρ₀, |Θ j (X (tj j) y t₁)| ≤ Bd :=
    fun j y hy => hΘ1 j _ ⟨y, hy, rfl⟩
  have hGhol := fun j => pullback_holder ch (htjw j) hs hs1 hBd (hΘ2 j)
  have hGc : ∀ j, ContinuousOn (fun y => Θ j (X (tj j) y t₁)) (euclidBall (0 : Vec 2) ρ₀) :=
    fun j => continuousOn_of_holder_euclid hs (hGhol j)
  have hfinB : IsFiniteMeasure (volume.restrict (euclidBall (0 : Vec 2) ρ₀)) :=
    isFiniteMeasure_restrict.mpr hB₀fin
  have hGL2 : ∀ j, MemLp (fun y => Θ j (X (tj j) y t₁)) 2
      (volume.restrict (euclidBall (0 : Vec 2) ρ₀)) := fun j =>
    MemLp.of_bound ((hGc j).aestronglyMeasurable hB₀m) Bd
      ((ae_restrict_iff' hB₀m).2 (Eventually.of_forall fun y hy => by
        rw [Real.norm_eq_abs]; exact hGbd j y hy))
  have hl2 := l2_limit_of_traces hB₀m (t₁ := t₁) (D := D) (Φ := fun σ y => θ σ (X σ y t₁))
    (G := fun j y => Θ j (X (tj j) y t₁)) (Ut := Ut) (tj := tj) hθL2 hGL2 hUtL2
    (fun j => (htjI j).2) (fun j => (htjI j).1.2) hΘ3 hUttr htjlim
  obtain ⟨g, hgt, hgbd2, hghol2, hgae⟩ := holder_limit_of_l2 (ρ₀ := ρ₀) (M := 2 * Bd) (s := s)
    (by positivity) hs (fun j y hy => (hGbd j y hy).trans (by linarith)) hGhol hUtL2 hl2
  have hFlim : ∀ y : Vec 2, Tendsto (fun j => X (tj j) y t₁) atTop (𝓝 y) := by
    intro y
    have hc : Continuous fun p : ℝ => X p y t₁ :=
      ch.smoothF.continuous.comp (continuous_id.prodMk continuous_const)
    have := (hc.tendsto t₁).comp htjlim
    rwa [show X t₁ y t₁ = y from ch.flow.1 y t₁] at this
  obtain ⟨hgb, hgh⟩ := limit_bounds_physical hs hFlim hgt hGbd
    (fun j y hy z hz => hΘ2 j _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩)
  refine ⟨g, continuousOn_of_holder_euclid hs hgh, hgb, hgh, ?_⟩
  refine hUttr.congr' (Eventually.of_forall fun σ => ?_)
  refine setIntegral_congr_ae hB₀m ?_
  filter_upwards [(ae_restrict_iff' hB₀m).1 hgae] with y hy hyB
  rw [ch.flow.1 y t₁, hy hyB]
end

/-! # Assembly of the local estimate for one instance

For fixed pipe data and one `(t₁, X, κ, θ)`: the family of slices `Θ_t`, `t < t₁` (`slice_below`),
with the top slice from `slice_top`, gives the representative of the local theorem. -/

section
variable {b b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T : ℝ}

/-- Amplitude and Hölder bounds of `Θ_t` on `F_t(B_ρ)` and its label trace, for all `t` in the
window `[t₁ - D, t₁)`. -/
def SliceFam (X : ℝ → Vec 2 → ℝ → Vec 2) (t₁ : ℝ) (θ : ℝ → Vec 2 → ℝ) (D ρ s Bd : ℝ) : Prop :=
  ∀ t ∈ Ico (t₁ - D) t₁, ∃ Θt : Vec 2 → ℝ,
    ContinuousOn Θt ((fun y => X t y t₁) '' euclidBall 0 ρ) ∧
    (∀ x ∈ (fun y => X t y t₁) '' euclidBall 0 ρ, |Θt x| ≤ Bd) ∧
    (∀ x ∈ (fun y => X t y t₁) '' euclidBall 0 ρ,
      ∀ z ∈ (fun y => X t y t₁) '' euclidBall 0 ρ, |Θt x - Θt z| ≤ Bd * eNorm (x - z) ^ s) ∧
    Tendsto (fun σ => ∫ y in euclidBall 0 ρ, (θ σ (X σ y t₁) - Θt (X t y t₁)) ^ 2)
      (𝓝[<] t ⊓ ae volume) (𝓝 0)

/-- Amplitude plus Hölder quotient from the two separate bounds. -/
theorem sum_bound_of_holder {Θ : Vec 2 → ℝ} {S : Set (Vec 2)} {s Bd : ℝ}
    (h1 : ∀ x ∈ S, |Θ x| ≤ Bd) (h2 : ∀ x ∈ S, ∀ z ∈ S, |Θ x - Θ z| ≤ Bd * eNorm (x - z) ^ s)
    {x y z : Vec 2} (hx : x ∈ S) (hy : y ∈ S) (hz : z ∈ S) (hyz : y ≠ z) :
    |Θ x| + |Θ y - Θ z| / Real.sqrt (vecNormSq (y - z)) ^ s ≤ 2 * Bd := by
  have hpos : 0 < eNorm (y - z) := by
    unfold eNorm
    exact Real.sqrt_pos.2 (vecNormSq_pos_of_ne hyz)
  have hpow : 0 < eNorm (y - z) ^ s := Real.rpow_pos_of_pos hpos s
  have h3 : |Θ y - Θ z| / Real.sqrt (vecNormSq (y - z)) ^ s ≤ Bd := by
    have : Real.sqrt (vecNormSq (y - z)) ^ s = eNorm (y - z) ^ s := rfl
    rw [this, div_le_iff₀ hpow]
    exact h2 y hy z hz
  linarith [h1 x hx]

/-- **From the family of slices to the representative of the local theorem.** -/
theorem instance_final (ch : IsPipeChart b0 X t₁ T) {ϑ ρ₀ s Bd : ℝ} (hϑT : 0 < ϑ * T)
    (hϑ8 : ϑ * T ≤ 8 * T) (hs : 0 < s) (hs1 : s ≤ 1) (hBd : 0 ≤ Bd) {θ : ℝ → Vec 2 → ℝ}
    (hθL2 : ∀ᵐ σ ∂(volume : Measure ℝ), σ ∈ Ioo (t₁ - ϑ * T) t₁ →
      MemLp (fun y => θ σ (X σ y t₁)) 2 (volume.restrict (euclidBall 0 ρ₀)))
    (hF : SliceFam X t₁ θ (ϑ * T) ρ₀ s Bd)
    (hUt : ∃ Ut : Vec 2 → ℝ, MemL2On (euclidBall 0 ρ₀) Ut ∧
      Tendsto (fun σ => ∫ y in euclidBall 0 ρ₀, (θ σ (X σ y t₁) - Ut y) ^ 2)
        (𝓝[<] t₁ ⊓ ae volume) (𝓝 0)) :
    ∃ Θ : ℝ → Vec 2 → ℝ, ∀ t ∈ Icc (t₁ - ϑ * T) t₁,
      ContinuousOn (Θ t) ((fun y => X t y t₁) '' euclidBall 0 ρ₀) ∧
      Tendsto (fun σ => ∫ y in euclidBall 0 ρ₀, (θ σ (X σ y t₁) - Θ t (X t y t₁)) ^ 2)
        (𝓝[<] t ⊓ ae volume) (𝓝 0) ∧
      ∀ x ∈ (fun y => X t y t₁) '' euclidBall 0 ρ₀, ∀ y ∈ (fun y => X t y t₁) '' euclidBall 0 ρ₀,
        ∀ z ∈ (fun y => X t y t₁) '' euclidBall 0 ρ₀, y ≠ z →
        |Θ t x| + |Θ t y - Θ t z| / Real.sqrt (vecNormSq (y - z)) ^ s ≤ 2 * Bd := by
  classical
  obtain ⟨g, hgc, hgb, hgh, hgtr⟩ := slice_top ch hϑT hϑ8 hs hs1 hBd hθL2
    (fun t ht => by
      obtain ⟨Θt, -, h1, h2, h3⟩ := hF t ht
      exact ⟨Θt, h1, h2, h3⟩) hUt
  refine ⟨fun t => if h : t ∈ Ico (t₁ - ϑ * T) t₁ then (hF t h).choose else g, fun t ht => ?_⟩
  by_cases htt : t < t₁
  · have hI : t ∈ Ico (t₁ - ϑ * T) t₁ := ⟨ht.1, htt⟩
    simp only [hI, ↓reduceDIte]
    obtain ⟨hc, h1, h2, h3⟩ := (hF t hI).choose_spec
    exact ⟨hc, h3, fun x hx y hy z hz hyz => sum_bound_of_holder h1 h2 hx hy hz hyz⟩
  · have ht1 : t = t₁ := le_antisymm ht.2 (not_lt.1 htt)
    subst ht1
    have hI : t ∉ Ico (t - ϑ * T) t := fun h => lt_irrefl _ h.2
    simp only [hI, ↓reduceDIte]
    have himg : (fun y => X t y t) '' euclidBall (0 : Vec 2) ρ₀ = euclidBall 0 ρ₀ := by
      have : (fun y => X t y t) = id := funext fun y => ch.flow.1 y t
      rw [this]; simp
    rw [himg]
    refine ⟨hgc, ?_, fun x hx y hy z hz hyz => sum_bound_of_holder hgb hgh hx hy hz hyz⟩
    simpa [ch.flow.1] using hgtr
end

end AVRegularity.Applications
end
