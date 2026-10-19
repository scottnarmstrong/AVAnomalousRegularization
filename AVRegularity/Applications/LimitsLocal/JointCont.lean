-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Applications.LimitsLocal.Kern
import AVRegularity.Applications.Pipe.LocalEnergy
import AVRegularity.Applications.Torus.TraceIdent
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Tactic.Monotonicity.Lemmas

@[expose] public section
noncomputable section

section
open MeasureTheory Filter Topology Homogenization AVenhance Set
namespace AVRegularity.Applications.LimitsLocal

/-! # The increment estimate

`mollify_close`: a function of small oscillation on `B_r(x)` is close to its `mollK r x`-average.
`abs_drift_le`: `|∫_σ^τ G| ≤ MΨ √(τ - σ) (Q₂ + |B|) / 2` for `Q₂ ≥ ∬ θ²` (Cauchy-Schwarz in the
elementary form `|θ| ≤ (λθ² + λ⁻¹)/2`). -/

section
open AVRegularity.Applications

theorem integrable_mul_kern {U : Vec 2 → ℝ} {x : Vec 2} {r : ℝ} (hr : 0 < r)
    (hc : ContinuousOn U (Metric.closedBall x r)) :
    Integrable (fun y => U y * mollK r x y) := by
  have hcont : ContinuousOn (fun y => U y * mollK r x y) (Metric.closedBall x r) :=
    hc.mul (kern_contDiff r x).continuous.continuousOn
  have hint : IntegrableOn (fun y => U y * mollK r x y) (Metric.closedBall x r) :=
    hcont.integrableOn_compact (isCompact_closedBall _ _)
  rw [← integrableOn_iff_integrable_of_support_subset (s := Metric.closedBall x r)]
  · exact hint
  · intro y hy
    have : mollK r x y ≠ 0 := right_ne_zero_of_mul hy
    exact Metric.ball_subset_closedBall (by simpa [Metric.mem_ball] using kern_support hr this)

theorem mollify_close {U : Vec 2 → ℝ} {x : Vec 2} {r ε₀ : ℝ} (hr : 0 < r)
    (hc : ContinuousOn U (Metric.closedBall x r))
    (hε : ∀ y, dist y x < r → |U y - U x| ≤ ε₀) :
    |U x - ∫ y, U y * mollK r x y| ≤ ε₀ := by
  have hi := integrable_mul_kern hr hc
  have hk : Integrable (mollK r x) := (kern_contDiff r x).continuous.integrable_of_hasCompactSupport
    (kern_compact hr x)
  have h1 : U x - ∫ y, U y * mollK r x y = ∫ y, (U x - U y) * mollK r x y := by
    have : ∫ y, (U x - U y) * mollK r x y = (∫ y, U x * mollK r x y) - ∫ y, U y * mollK r x y := by
      simp_rw [sub_mul]
      exact integral_sub (hk.const_mul _) hi
    rw [this, integral_const_mul, kern_integral hr, mul_one]
  rw [h1]
  have hb : ∀ y, ‖(U x - U y) * mollK r x y‖ ≤ ε₀ * mollK r x y := by
    intro y
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (kern_nonneg' (r := r) x y)]
    by_cases hy : mollK r x y = 0
    · simp [hy]
    · have := hε y (kern_support hr hy)
      rw [abs_sub_comm] at this
      exact mul_le_mul_of_nonneg_right this (kern_nonneg' x y)
  have := norm_integral_le_of_norm_le (hk.const_mul ε₀) (Filter.Eventually.of_forall hb)
  rw [integral_const_mul, kern_integral hr, mul_one] at this
  simpa using this

theorem abs_le_half_mul (a l : ℝ) (hl : 0 < l) : |a| ≤ (l * a ^ 2 + 1 / l) / 2 := by
  have h : 0 ≤ (l * |a| - 1) ^ 2 := sq_nonneg _
  have h2 : l * a ^ 2 + 1 / l - 2 * |a| = (l * |a| - 1) ^ 2 / l := by
    have : a ^ 2 = |a| ^ 2 := (sq_abs a).symm
    rw [this]; field_simp; ring
  have h3 : 0 ≤ (l * |a| - 1) ^ 2 / l := div_nonneg h hl.le
  linarith

theorem abs_drift_le {θ : ℝ → Vec 2 → ℝ} {P : Set (ℝ × Vec 2)} {b : ℝ → Vec 2 → Vec 2} {κ : ℝ}
    {ψ : Vec 2 → ℝ} {B : Set (Vec 2)} {σ τ MΨ Q₂ : ℝ} (hστ : σ < τ)
    (hΨ : ∀ t x, |Psi b κ ψ t x| ≤ MΨ) (hΨ0 : ∀ t x, x ∉ B → Psi b κ ψ t x = 0)
    (hΨc : Continuous fun p : ℝ × Vec 2 => Psi b κ ψ p.1 p.2) (hB : MeasurableSet B)
    (hQP : Ioo σ τ ×ˢ B ⊆ P) (hθ : IntegrableOn (fun p : ℝ × Vec 2 => θ p.1 p.2) P)
    (hθ2 : IntegrableOn (fun p : ℝ × Vec 2 => θ p.1 p.2 ^ 2) P)
    (hQ₂ : ∫ p in P, θ p.1 p.2 ^ 2 ≤ Q₂) (hvol : volume B < ⊤) :
    |∫ t in σ..τ, driftG b κ θ ψ t| ≤
      MΨ * (Real.sqrt (τ - σ) * (Q₂ + (volume B).toReal) / 2) := by
  set Q : Set (ℝ × Vec 2) := Ioo σ τ ×ˢ B with hQ
  have hMΨ : 0 ≤ MΨ := (abs_nonneg _).trans (hΨ σ 0)
  have hθQ : IntegrableOn (fun p : ℝ × Vec 2 => θ p.1 p.2) Q := hθ.mono_set hQP
  have hθ2Q : IntegrableOn (fun p : ℝ × Vec 2 => θ p.1 p.2 ^ 2) Q := hθ2.mono_set hQP
  have hfQ : IntegrableOn (fun p : ℝ × Vec 2 => θ p.1 p.2 * Psi b κ ψ p.1 p.2) Q :=
    integrableOn_mul_bdd hθQ hΨc ⟨MΨ, fun p => hΨ _ _⟩
  have hGint : ∫ t in σ..τ, driftG b κ θ ψ t = ∫ p in Q, θ p.1 p.2 * Psi b κ ψ p.1 p.2 := by
    rw [intervalIntegral.integral_of_le hστ.le, integral_Ioc_eq_integral_Ioo]
    have hmeas : MeasurableSet (Ioo σ τ) := measurableSet_Ioo
    rw [hQ, Measure.volume_eq_prod, setIntegral_prod]
    · refine setIntegral_congr_fun hmeas fun t _ => ?_
      simp only [driftG]
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        simp [hΨ0 t x hx]).symm
    · rw [← Measure.volume_eq_prod]; exact hfQ
  rw [hGint]
  have hn1 : |∫ p in Q, θ p.1 p.2 * Psi b κ ψ p.1 p.2| ≤ MΨ * ∫ p in Q, |θ p.1 p.2| := by
    have h1 := norm_integral_le_of_norm_le (hθQ.norm.const_mul MΨ)
      (μ := volume.restrict Q) (f := fun p : ℝ × Vec 2 => θ p.1 p.2 * Psi b κ ψ p.1 p.2)
      (Filter.Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs, abs_mul]
        calc |θ p.1 p.2| * |Psi b κ ψ p.1 p.2| ≤ |θ p.1 p.2| * MΨ :=
              mul_le_mul_of_nonneg_left (hΨ _ _) (abs_nonneg _)
          _ = MΨ * ‖θ p.1 p.2‖ := by rw [Real.norm_eq_abs]; ring)
    rw [integral_const_mul] at h1
    simpa using h1
  refine hn1.trans (mul_le_mul_of_nonneg_left ?_ hMΨ)
  -- the elementary Cauchy-Schwarz
  set h := τ - σ with hh
  have hpos : 0 < h := sub_pos.2 hστ
  set l := Real.sqrt h with hl
  have hl0 : 0 < l := Real.sqrt_pos.2 hpos
  have hQvol : (volume Q).toReal = h * (volume B).toReal := by
    rw [hQ, Measure.volume_eq_prod, Measure.prod_prod, ENNReal.toReal_mul, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by linarith)]
  have hQfin : volume Q < ⊤ := by
    rw [hQ, Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_lt_top (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top) hvol
  have hmono : ∫ p in Q, |θ p.1 p.2| ≤ ∫ p in Q, (l * θ p.1 p.2 ^ 2 + 1 / l) / 2 := by
    refine setIntegral_mono_on hθQ.norm ?_ (measurableSet_Ioo.prod hB) fun p _ => ?_
    · exact ((hθ2Q.const_mul l).add (integrableOn_const hQfin.ne)).div_const 2
    · exact abs_le_half_mul _ _ hl0
  have hrhs : ∫ p in Q, (l * θ p.1 p.2 ^ 2 + 1 / l) / 2 =
      (l * (∫ p in Q, θ p.1 p.2 ^ 2) + (volume Q).toReal * (1 / l)) / 2 := by
    rw [integral_div, integral_add (hθ2Q.const_mul l) (integrableOn_const hQfin.ne),
      integral_const_mul, setIntegral_const]
    simp [Measure.real, smul_eq_mul]
  have hQ2 : ∫ p in Q, θ p.1 p.2 ^ 2 ≤ Q₂ := by
    refine le_trans (setIntegral_mono_set hθ2 ?_ (Filter.Eventually.of_forall hQP)) hQ₂
    exact Filter.Eventually.of_forall fun p => sq_nonneg _
  refine hmono.trans (hrhs.le.trans ?_)
  have hlsq : l * l = h := Real.mul_self_sqrt hpos.le
  have : (volume Q).toReal * (1 / l) = l * (volume B).toReal := by
    rw [hQvol, ← hlsq]; field_simp
  rw [this]
  have hvB : 0 ≤ (volume B).toReal := ENNReal.toReal_nonneg
  nlinarith [mul_le_mul_of_nonneg_left hQ2 hl0.le]
end

/-! # Physical pairings converge along the label `L²` traces

If the pulled-back slices `θ(r, F_r ·)` converge in `L²(B_ρ)` to `Θ_τ ∘ F_τ` as `r → τ⁻` (a.e.),
then for a spatial test `ψ` supported in `F_r(B_ρ)` for all `r` near `τ`, the physical pairings
`∫ θ(r,x) ψ(x) dx` converge to `∫ Θ_τ ψ`. Uses `det DF_r = 1` (measure preservation) and the
continuity of the chart in time. -/

section
open AVRegularity.Applications

theorem tendsto_setIntegral_abs_of_sq {ι : Type*} {l : Filter ι} {B : Set (Vec 2)}
    (hB : volume B < ⊤) {D : ι → Vec 2 → ℝ}
    (hD : ∀ᶠ i in l, MemLp (D i) 2 (volume.restrict B))
    (hlim : Tendsto (fun i => ∫ y in B, D i y ^ 2) l (𝓝 0)) :
    Tendsto (fun i => ∫ y in B, |D i y|) l (𝓝 0) := by
  have : IsFiniteMeasure (volume.restrict B) := ⟨by simpa using hB⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  set V := (volume B).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  set lam : ℝ := 2 * V / ε + 1 with hlam
  have hlam0 : 0 < lam := by positivity
  have hsmall : ∀ᶠ i in l, ∫ y in B, D i y ^ 2 < ε / lam := by
    have := (Metric.tendsto_nhds.1 hlim) (ε / lam) (by positivity)
    filter_upwards [this] with i hi
    rw [Real.dist_eq, sub_zero] at hi
    exact lt_of_le_of_lt (le_abs_self _) hi
  filter_upwards [hD, hsmall] with i hi hs
  have hint1 : Integrable (D i) (volume.restrict B) := hi.integrable (by norm_num)
  have hint2 : Integrable (fun y => D i y ^ 2) (volume.restrict B) := hi.integrable_sq
  have hmono : ∫ y in B, |D i y| ≤ ∫ y in B, (lam * D i y ^ 2 + 1 / lam) / 2 :=
    integral_mono hint1.abs (((hint2.const_mul lam).add (integrable_const _)).div_const 2)
      fun y => abs_le_half_mul _ _ hlam0
  have hrhs : ∫ y in B, (lam * D i y ^ 2 + 1 / lam) / 2 =
      (lam * (∫ y in B, D i y ^ 2) + V * (1 / lam)) / 2 := by
    rw [integral_div, integral_add (hint2.const_mul lam) (integrable_const _), integral_const_mul,
      integral_const]
    simp [Measure.real, hV, smul_eq_mul]
  have h0 : 0 ≤ ∫ y in B, |D i y| := integral_nonneg fun y => abs_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  have h1 : lam * (∫ y in B, D i y ^ 2) < ε := by
    calc lam * (∫ y in B, D i y ^ 2) < lam * (ε / lam) := mul_lt_mul_of_pos_left hs hlam0
      _ = ε := by field_simp
  have h2 : V * (1 / lam) ≤ ε / 2 := by
    rw [mul_one_div, div_le_iff₀ hlam0]
    have : 2 * V / ε * ε = 2 * V := by field_simp
    nlinarith [hlam, this]
  linarith [hmono, hrhs]

theorem trace_transfer {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T : ℝ}
    (ch : IsPipeChart b0 X t₁ T) {ρ τ : ℝ} (hτ : τ ∈ Ioc (t₁ - 8 * T) t₁)
    {θ : ℝ → Vec 2 → ℝ} {Θτ ψ : Vec 2 → ℝ} {M : ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hsupp : ∃ δ : ℝ, 0 < δ ∧ ∀ r ∈ Ioo (τ - δ) τ,
      tsupport ψ ⊆ (fun y => X r y t₁) '' euclidBall 0 ρ)
    (hτsupp : tsupport ψ ⊆ (fun y => X τ y t₁) '' euclidBall 0 ρ)
    (hmem : ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ioo (t₁ - 8 * T) t₁ →
      MemLp (fun y => θ r (X r y t₁)) 2 (volume.restrict (euclidBall 0 ρ)))
    (hΘc : ContinuousOn Θτ ((fun y => X τ y t₁) '' euclidBall 0 ρ))
    (hΘb : ∀ x ∈ (fun y => X τ y t₁) '' euclidBall 0 ρ, |Θτ x| ≤ M)
    (htr : Tendsto (fun r => ∫ y in euclidBall 0 ρ, (θ r (X r y t₁) - Θτ (X τ y t₁)) ^ 2)
      (𝓝[<] τ ⊓ ae (volume : Measure ℝ)) (𝓝 0)) :
    Tendsto (pairG θ ψ) (𝓝[<] τ ⊓ ae (volume : Measure ℝ)) (𝓝 (∫ x, Θτ x * ψ x)) := by
  set B : Set (Vec 2) := euclidBall 0 ρ with hBdef
  have hBm : MeasurableSet B := (pipe_isOpen_euclidBall 0 ρ).measurableSet
  have hBfin : volume B < ⊤ := pipe_volume_euclidBall_lt_top ρ
  have hfin : IsFiniteMeasure (volume.restrict B) := ⟨by simpa using hBfin⟩
  set Fm : ℝ → Vec 2 → Vec 2 := fun r y => X r y t₁ with hFm
  have hFc : Continuous fun p : ℝ × Vec 2 => Fm p.1 p.2 := ch.smoothF.continuous
  obtain ⟨Cψ, hCψ⟩ : ∃ C, ∀ x, |ψ x| ≤ C := by
    obtain ⟨M', hM'⟩ := hψ.continuous.bounded_above_of_compact_support hψc
    exact ⟨M', fun x => by simpa using hM' x⟩
  have hCψ0 : 0 ≤ Cψ := (abs_nonneg _).trans (hCψ 0)
  obtain ⟨δ, hδ, hsub⟩ := hsupp
  set δ' := min δ (τ - (t₁ - 8 * T)) with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ (by linarith [hτ.1])
  -- the sets
  have hFτcont : ContinuousOn (fun y => Θτ (Fm τ y)) B := by
    refine hΘc.comp (ch.smoothF.continuous.comp (by fun_prop : Continuous fun y : Vec 2 => (τ, y))).continuousOn ?_
    intro y hy; exact ⟨y, hy, rfl⟩
  have hFτmeas : AEStronglyMeasurable (fun y => Θτ (Fm τ y)) (volume.restrict B) :=
    hFτcont.aestronglyMeasurable hBm
  have hFτbd : ∀ y ∈ B, |Θτ (Fm τ y)| ≤ M := fun y hy => hΘb _ ⟨y, hy, rfl⟩
  have hFτmem : MemLp (fun y => Θτ (Fm τ y)) 2 (volume.restrict B) :=
    MemLp.of_bound hFτmeas |M| ((ae_restrict_iff' hBm).2 (Filter.Eventually.of_forall fun y hy => by
      rw [Real.norm_eq_abs]; exact (hFτbd y hy).trans (le_abs_self _)))
  have hτI : τ ∈ Icc (t₁ - 8 * T) t₁ := ⟨hτ.1.le, hτ.2⟩
  have hLeq : ∫ x, Θτ x * ψ x = ∫ y in B, Θτ (Fm τ y) * ψ (Fm τ y) := by
    rw [← section_integral_eq ch hτI (fun x => Θτ x * ψ x) B]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      have : x ∉ tsupport ψ := fun h => hx (hτsupp h)
      simp [image_eq_zero_of_notMem_tsupport this]).symm
  -- ae good times
  have hgood : ∀ᶠ r in 𝓝[<] τ ⊓ ae (volume : Measure ℝ), r ∈ Ioo (τ - δ') τ ∧
      MemLp (fun y => θ r (Fm r y)) 2 (volume.restrict B) := by
    have h1 : Ioo (τ - δ') τ ∈ 𝓝[<] τ := Ioo_mem_nhdsLT (by linarith)
    have h2 : ∀ᶠ r in ae (volume : Measure ℝ), r ∈ Ioo (t₁ - 8 * T) t₁ →
        MemLp (fun y => θ r (Fm r y)) 2 (volume.restrict B) := hmem
    filter_upwards [mem_inf_of_left h1, mem_inf_of_right h2] with r hr1 hr2
    refine ⟨hr1, hr2 ⟨?_, ?_⟩⟩
    · have := hr1.1; have := min_le_right δ (τ - (t₁ - 8 * T)); linarith
    · exact lt_of_lt_of_le hr1.2 hτ.2
  -- the two error terms
  set a : ℝ → ℝ := fun r => ∫ y in B, |θ r (Fm r y) - Θτ (Fm τ y)| with ha
  set bb : ℝ → ℝ := fun r => ∫ y in B, |Θτ (Fm τ y)| * |ψ (Fm r y) - ψ (Fm τ y)| with hbb
  have ha0 : Tendsto a (𝓝[<] τ ⊓ ae (volume : Measure ℝ)) (𝓝 0) := by
    refine tendsto_setIntegral_abs_of_sq hBfin (D := fun r y => θ r (Fm r y) - Θτ (Fm τ y)) ?_ htr
    filter_upwards [hgood] with r hr
    exact hr.2.sub hFτmem
  have hslice : ∀ r, Continuous fun y : Vec 2 => Fm r y := fun r =>
    hFc.comp (continuous_const.prodMk continuous_id)
  have hψslice : ∀ r, Continuous fun y : Vec 2 => ψ (Fm r y) := fun r =>
    hψ.continuous.comp (hslice r)
  have hbddB : ∀ r, ∀ y, |ψ (Fm r y) - ψ (Fm τ y)| ≤ 2 * Cψ := fun r y => by
    have := (abs_sub _ _).trans (add_le_add (hCψ (Fm r y)) (hCψ (Fm τ y)))
    linarith
  have hbbint : ∀ r, Integrable (fun y => |Θτ (Fm τ y)| * |ψ (Fm r y) - ψ (Fm τ y)|)
      (volume.restrict B) := by
    intro r
    have := Integrable.bdd_mul (c := 2 * Cψ) (hFτmem.integrable (by norm_num)).abs
      (((hψslice r).sub (hψslice τ)).abs.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_abs]; exact hbddB r y)
    simpa [mul_comm] using this
  have hb0' : Tendsto bb (𝓝[<] τ) (𝓝 0) := by
    have hlim := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict B)
      (l := 𝓝[<] τ)
      (F := fun r y => |Θτ (Fm τ y)| * |ψ (Fm r y) - ψ (Fm τ y)|)
      (f := fun _ => (0 : ℝ)) (bound := fun _ => |M| * (2 * Cψ))
      (Filter.Eventually.of_forall fun r => (hbbint r).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun r => (ae_restrict_iff' hBm).2
        (Filter.Eventually.of_forall fun y hy => by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
          exact mul_le_mul ((hFτbd y hy).trans (le_abs_self _)) (hbddB r y) (abs_nonneg _)
            (abs_nonneg _)))
      (integrable_const _) ?_
    · simpa using hlim
    · refine Filter.Eventually.of_forall fun y => ?_
      have hcr : Tendsto (fun r => Fm r y) (𝓝 τ) (𝓝 (Fm τ y)) :=
        (hFc.comp (continuous_id.prodMk continuous_const)).tendsto τ
      have h1 : Tendsto (fun r => ψ (Fm r y)) (𝓝 τ) (𝓝 (ψ (Fm τ y))) :=
        (hψ.continuous.tendsto _).comp hcr
      have h2 : Tendsto (fun r => |Θτ (Fm τ y)| * |ψ (Fm r y) - ψ (Fm τ y)|) (𝓝 τ) (𝓝 0) := by
        have := ((h1.sub_const (ψ (Fm τ y))).abs).const_mul |Θτ (Fm τ y)|
        simpa using this
      exact h2.mono_left nhdsWithin_le_nhds
  have hb0 : Tendsto bb (𝓝[<] τ ⊓ ae (volume : Measure ℝ)) (𝓝 0) := hb0'.mono_left inf_le_left
  -- the pointwise estimate
  have hdist : ∀ᶠ r in 𝓝[<] τ ⊓ ae (volume : Measure ℝ),
      dist (pairG θ ψ r) (∫ x, Θτ x * ψ x) ≤ Cψ * a r + bb r := by
    filter_upwards [hgood] with r hr
    obtain ⟨hrI, hrm⟩ := hr
    have hrw : r ∈ Icc (t₁ - 8 * T) t₁ := by
      have := hrI.1; have := min_le_right δ (τ - (t₁ - 8 * T))
      exact ⟨by linarith, (hrI.2.trans_le hτ.2).le⟩
    have hrδ : r ∈ Ioo (τ - δ) τ := ⟨by have := min_le_left δ (τ - (t₁ - 8 * T)); linarith [hrI.1], hrI.2⟩
    have hP : pairG θ ψ r = ∫ y in B, θ r (Fm r y) * ψ (Fm r y) := by
      unfold pairG
      rw [← section_integral_eq ch hrw (fun x => θ r x * ψ x) B]
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        have : x ∉ tsupport ψ := fun h => hx (hsub r hrδ h)
        simp [image_eq_zero_of_notMem_tsupport this]).symm
    have hui : Integrable (fun y => θ r (Fm r y) * ψ (Fm r y)) (volume.restrict B) := by
      have := Integrable.bdd_mul (c := Cψ) (hrm.integrable (by norm_num))
        (hψslice r).aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs]; exact hCψ _)
      simpa [mul_comm] using this
    have hvi : Integrable (fun y => Θτ (Fm τ y) * ψ (Fm τ y)) (volume.restrict B) := by
      have := Integrable.bdd_mul (c := Cψ) (hFτmem.integrable (by norm_num))
        (hψslice τ).aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs]; exact hCψ _)
      simpa [mul_comm] using this
    have hDi : Integrable (fun y => θ r (Fm r y) - Θτ (Fm τ y)) (volume.restrict B) :=
      (hrm.sub hFτmem).integrable (by norm_num)
    rw [Real.dist_eq, hP, hLeq, ← integral_sub hui hvi]
    have hbi : Integrable (fun y => Cψ * |θ r (Fm r y) - Θτ (Fm τ y)| +
        |Θτ (Fm τ y)| * |ψ (Fm r y) - ψ (Fm τ y)|) (volume.restrict B) :=
      (hDi.abs.const_mul Cψ).add (hbbint r)
    have := norm_integral_le_of_norm_le hbi (f := fun y => θ r (Fm r y) * ψ (Fm r y) -
        Θτ (Fm τ y) * ψ (Fm τ y)) (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]
      have e : θ r (Fm r y) * ψ (Fm r y) - Θτ (Fm τ y) * ψ (Fm τ y) =
          (θ r (Fm r y) - Θτ (Fm τ y)) * ψ (Fm r y) +
            Θτ (Fm τ y) * (ψ (Fm r y) - ψ (Fm τ y)) := by ring
      rw [e]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hCψ _) (abs_nonneg _) |>.trans (le_of_eq (by ring))
      · rw [abs_mul])
    rw [integral_add (hDi.abs.const_mul Cψ) (hbbint r), integral_const_mul] at this
    simpa [ha, hbb, Real.norm_eq_abs] using this
  have hsq : Tendsto (fun r => Cψ * a r + bb r) (𝓝[<] τ ⊓ ae (volume : Measure ℝ)) (𝓝 0) := by
    simpa using (ha0.const_mul Cψ).add hb0
  refine tendsto_iff_dist_tendsto_zero.2 ?_
  exact squeeze_zero' (Filter.Eventually.of_forall fun r => dist_nonneg) hdist hsq
end

/-! # The increment estimate for the slice representatives

For slice representatives `Θ σ`, `Θ τ` (`SliceOK`) of a local solution `θ`, and a sup-ball
`closedBall x r` which stays inside the sections `F_u(B_ρ)`, `u ∈ [σ - η, τ]`,
`|Θ τ x - Θ σ x| ≤ 2 M (2r)^s + MΨ(r) √(τ - σ) (Q₂ + |B_r|) / 2`. -/

section
open AVRegularity.Applications

theorem euclidBall_subset_of_le {ρ R : ℝ} (hρ0 : 0 ≤ ρ) (hρR : ρ ≤ R) :
    euclidBall (0 : Vec 2) ρ ⊆ euclidBall 0 R := by
  intro y hy
  simp only [euclidBall, mem_ofPred_eq] at hy ⊢
  exact lt_of_lt_of_le hy (pow_le_pow_left₀ hρ0 hρR 2)

theorem tsupport_kern_subset {r : ℝ} (hr : 0 < r) (x : Vec 2) :
    tsupport (mollK r x) ⊆ Metric.closedBall x r := by
  refine closure_minimal (fun y hy => ?_) Metric.isClosed_closedBall
  exact Metric.ball_subset_closedBall (by simpa [Metric.mem_ball] using kern_support hr hy)

variable {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T : ℝ}

theorem increment_est (ch : IsPipeChart b0 X t₁ T) {R : ℝ}
    {b : ℝ → Vec 2 → Vec 2} {κ Bb : ℝ} (hB : ∀ t x, ‖b t x‖ ≤ Bb)
    (hbc : Continuous fun p : ℝ × Vec 2 => b p.1 p.2) {θ : ℝ → Vec 2 → ℝ}
    (hfin : volume (outerPipe (fun t y => X t y t₁) t₁ T R) < ⊤)
    (hθ2 : MemLp (fun p : ℝ × Vec 2 => θ p.1 p.2) 2
      (volume.restrict (outerPipe (fun t y => X t y t₁) t₁ T R)))
    (hweak : ∀ φ : ℝ × Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ outerPipe (fun t y => X t y t₁) t₁ T R →
      ∫ p in outerPipe (fun t y => X t y t₁) t₁ T R, θ p.1 p.2 *
        (fderiv ℝ φ p (1, 0) + ∑ i : Fin 2, b p.1 p.2 i * fderiv ℝ φ p (0, basisVec i)
          + κ * ∑ i : Fin 2,
            fderiv ℝ (fun p' => fderiv ℝ φ p' (0, basisVec i)) p (0, basisVec i)) = 0)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρR : ρ ≤ R)
    (hmem : ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ioo (t₁ - 8 * T) t₁ →
      MemLp (fun y => θ r (X r y t₁)) 2 (volume.restrict (euclidBall 0 ρ)))
    {Q₂ : ℝ} (hQ₂ : ∫ p in outerPipe (fun t y => X t y t₁) t₁ T R, θ p.1 p.2 ^ 2 ≤ Q₂)
    {s M : ℝ} {Θ : ℝ → Vec 2 → ℝ} {σ τ η : ℝ} {x : Vec 2} {r : ℝ}
    (hστ : σ < τ) (hτ₁ : τ ≤ t₁) (hη : 0 < η) (hr : 0 < r)
    (hσ : SliceOK X t₁ s ρ M θ Θ σ) (hτ : SliceOK X t₁ s ρ M θ Θ τ)
    (hC : ∀ u ∈ Icc (σ - η) τ, t₁ - 8 * T < u ∧
      Metric.closedBall x r ⊆ (fun y => X u y t₁) '' euclidBall 0 ρ)
    {D : ℝ} (hD : ∀ r : ℝ, 0 < r → ∀ x y : Vec 2, ∀ j : Fin 2,
      |spaceGrad (mollK r x) y j| ≤ D * r⁻¹ ^ 3 ∧
      |spaceGrad (fun w => spaceGrad (mollK r x) w j) y j| ≤ D * r⁻¹ ^ 4)
    (hs : 0 < s) :
    |Θ τ x - Θ σ x| ≤ 2 * (M * (2 * r) ^ s) +
      (2 * |Bb| * (D * r⁻¹ ^ 3) + 2 * (|κ| * (D * r⁻¹ ^ 4))) *
        (Real.sqrt (τ - σ) * (Q₂ + (volume (Metric.closedBall (0 : Vec 2) r)).toReal) / 2) := by
  set P := outerPipe (fun t y => X t y t₁) t₁ T R with hP
  have : IsFiniteMeasure (volume.restrict P) := ⟨by simpa using hfin⟩
  have hθ : IntegrableOn (fun p : ℝ × Vec 2 => θ p.1 p.2) P := hθ2.integrable (by norm_num)
  have hθsq : IntegrableOn (fun p : ℝ × Vec 2 => θ p.1 p.2 ^ 2) P := hθ2.integrable_sq
  set ψ := mollK r x with hψdef
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := kern_contDiff r x
  have hψc : HasCompactSupport ψ := kern_compact hr x
  set B := tsupport ψ with hBdef
  have hBsub : B ⊆ Metric.closedBall x r := tsupport_kern_subset hr x
  have hBm : MeasurableSet B := (isClosed_tsupport _).measurableSet
  have hBfin : volume B < ⊤ := hψc.isCompact.measure_lt_top
  have hσI : σ ∈ Icc (t₁ - 8 * T) t₁ :=
    ⟨(hC σ ⟨by linarith, hστ.le⟩).1.le, hστ.le.trans hτ₁⟩
  have hτI : τ ∈ Icc (t₁ - 8 * T) t₁ :=
    ⟨(hC τ ⟨by linarith, le_rfl⟩).1.le, hτ₁⟩
  have hρR' := euclidBall_subset_of_le hρ0.le hρR
  -- the cylinder lies in the pipe
  have hcyl : Ico (σ - η) τ ×ˢ B ⊆ P := by
    intro p hp
    obtain ⟨⟨hp1, hp2⟩, hp3⟩ := hp
    obtain ⟨hlo, hball⟩ := hC p.1 ⟨hp1, hp2.le⟩
    obtain ⟨y, hy, hyx⟩ := hball (hBsub hp3)
    exact ⟨hlo, hp2.trans_le hτ₁, y, hρR' hy, hyx.symm⟩
  have hdelta : ∀ u ∈ Icc (σ - η) τ, tsupport ψ ⊆ (fun y => X u y t₁) '' euclidBall 0 ρ :=
    fun u hu => hBsub.trans (hC u hu).2
  have hsuppσ : ∃ δ : ℝ, 0 < δ ∧ ∀ r' ∈ Ioo (σ - δ) σ,
      tsupport ψ ⊆ (fun y => X r' y t₁) '' euclidBall 0 ρ :=
    ⟨η, hη, fun r' hr' => hdelta r' ⟨hr'.1.le, hr'.2.le.trans hστ.le⟩⟩
  have hsuppτ : ∃ δ : ℝ, 0 < δ ∧ ∀ r' ∈ Ioo (τ - δ) τ,
      tsupport ψ ⊆ (fun y => X r' y t₁) '' euclidBall 0 ρ :=
    ⟨η, hη, fun r' hr' => hdelta r' ⟨by linarith [hr'.1], hr'.2.le⟩⟩
  have hxσ : x ∈ (fun y => X σ y t₁) '' euclidBall 0 ρ :=
    (hC σ ⟨by linarith, hστ.le⟩).2 (Metric.mem_closedBall_self hr.le)
  have hxτ : x ∈ (fun y => X τ y t₁) '' euclidBall 0 ρ :=
    (hC τ ⟨by linarith, le_rfl⟩).2 (Metric.mem_closedBall_self hr.le)
  -- traces
  have htrσ := trace_transfer ch ⟨(hC σ ⟨by linarith, hστ.le⟩).1, hστ.le.trans hτ₁⟩ hψ hψc
    hsuppσ (hdelta σ ⟨by linarith, hστ.le⟩) hmem hσ.1
    (fun x' hx' => hσ.abs_le ch hσI hρ0 hx') hσ.2.1
  have htrτ := trace_transfer ch ⟨(hC τ ⟨by linarith, le_rfl⟩).1, hτ₁⟩ hψ hψc
    hsuppτ (hdelta τ ⟨by linarith, le_rfl⟩) hmem hτ.1
    (fun x' hx' => hτ.abs_le ch hτI hρ0 hx') hτ.2.1
  have hid := pairing_limit hB hθ hweak hbc hψ hψc hστ hη hcyl htrσ htrτ
  -- drift bound
  have hQP : Ioo σ τ ×ˢ B ⊆ P := fun p hp => hcyl ⟨⟨by linarith [hp.1.1], hp.1.2⟩, hp.2⟩
  have hΨ := Psi_kern_bound hD hB κ hr x
  have hdr := abs_drift_le hστ (fun t y => hΨ t y) (fun t y hy => Psi_eq_zero_of_notMem hy t)
    (continuous_Psi hbc κ hψ) hBm hQP hθ hθsq hQ₂ hBfin
  have hvolB : (volume B).toReal ≤ (volume (Metric.closedBall (0 : Vec 2) r)).toReal := by
    refine ENNReal.toReal_mono ?_ ?_
    · rw [← Measure.addHaar_closedBall_center (μ := volume) x r]
      exact (isCompact_closedBall x r).measure_lt_top.ne
    · rw [← Measure.addHaar_closedBall_center (μ := volume) x r]
      exact measure_mono hBsub
  -- mollification
  have hε : ∀ t ∈ Icc (σ - η) τ, t ∈ Icc (t₁ - 8 * T) t₁ → SliceOK X t₁ s ρ M θ Θ t →
      ∀ y, dist y x < r → |Θ t y - Θ t x| ≤ M * (2 * r) ^ s := by
    intro t htm htI hok y hy
    have hyK := (hC t htm).2 (Metric.mem_closedBall.2 (le_of_lt hy))
    have hxK := (hC t htm).2 (Metric.mem_closedBall_self hr.le)
    have h1 := hok.holder ch htI hρ0 hyK hxK
    have hM : 0 ≤ M := (abs_nonneg _).trans (hok.abs_le ch htI hρ0 hxK)
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hM)
    have hdist : eNorm (y - x) ≤ 2 * r :=
      (eNorm_le_two_mul_norm _).trans (by
        have : ‖y - x‖ < r := by simpa [dist_eq_norm] using hy
        linarith)
    exact Real.rpow_le_rpow (eNorm_nonneg _) hdist hs.le
  have hσm : σ ∈ Icc (σ - η) τ := ⟨by linarith, hστ.le⟩
  have hτm : τ ∈ Icc (σ - η) τ := ⟨by linarith, le_rfl⟩
  have hcσ : ContinuousOn (Θ σ) (Metric.closedBall x r) := hσ.1.mono (hC σ hσm).2
  have hcτ : ContinuousOn (Θ τ) (Metric.closedBall x r) := hτ.1.mono (hC τ hτm).2
  have hmσ := mollify_close hr hcσ (hε σ hσm hσI hσ)
  have hmτ := mollify_close hr hcτ (hε τ hτm hτI hτ)
  have hMΨ0 : 0 ≤ 2 * |Bb| * (D * r⁻¹ ^ 3) + 2 * (|κ| * (D * r⁻¹ ^ 4)) :=
    (abs_nonneg _).trans (hΨ σ 0)
  have hdr' : |∫ t in σ..τ, driftG b κ θ ψ t| ≤
      (2 * |Bb| * (D * r⁻¹ ^ 3) + 2 * (|κ| * (D * r⁻¹ ^ 4))) *
        (Real.sqrt (τ - σ) * (Q₂ + (volume (Metric.closedBall (0 : Vec 2) r)).toReal) / 2) := by
    refine hdr.trans (mul_le_mul_of_nonneg_left ?_ hMΨ0)
    have := Real.sqrt_nonneg (τ - σ)
    have h2 : Q₂ + (volume B).toReal ≤ Q₂ + (volume (Metric.closedBall (0 : Vec 2) r)).toReal :=
      by linarith
    nlinarith
  rw [← hid] at hdr'
  have e1 : ∫ y, Θ τ y * mollK r x y = ∫ y, Θ τ y * ψ y := rfl
  have e2 : ∫ y, Θ σ y * mollK r x y = ∫ y, Θ σ y * ψ y := rfl
  rw [abs_le] at hmσ hmτ hdr'
  rw [abs_le]
  constructor <;> nlinarith [hmσ.1, hmσ.2, hmτ.1, hmτ.2, hdr'.1, hdr'.2]
end

/-! # Gluing the slice representatives

Slice representatives for different `(ϱ, ϑ)` are `L²` traces of the same function, hence agree on
the common part of their sections (`slice_agree`). Choosing the representative of the exhausting
pairs `(ϱ_k, ϑ_k)` with least `k` glues them into one function that is a slice representative for
every admissible `(ϱ, ϑ)` (`glue_slices`). -/

section
open AVRegularity.Applications

variable {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T R s : ℝ}
  {θ Θ Θ' : ℝ → Vec 2 → ℝ}

theorem SliceOK.congr {ρ M t : ℝ} (h : SliceOK X t₁ s ρ M θ Θ t)
    (heq : ∀ x ∈ (fun y => X t y t₁) '' euclidBall 0 ρ, Θ' t x = Θ t x) :
    SliceOK X t₁ s ρ M θ Θ' t := by
  have hB : MeasurableSet (euclidBall (0 : Vec 2) ρ) := (pipe_isOpen_euclidBall 0 ρ).measurableSet
  refine ⟨h.1.congr heq, ?_, fun x hx y hy z hz hyz => ?_⟩
  · refine h.2.1.congr fun r => ?_
    refine setIntegral_congr_fun hB fun y hy => ?_
    simp only [heq _ ⟨y, hy, rfl⟩]
  · rw [heq x hx, heq y hy, heq z hz]
    exact h.2.2 x hx y hy z hz hyz

theorem memLp_slice (ch : IsPipeChart b0 X t₁ T) {ρ M t : ℝ} (h : SliceOK X t₁ s ρ M θ Θ t)
    (ht : t ∈ Icc (t₁ - 8 * T) t₁) (hρ : 0 < ρ) :
    MemLp (fun y => Θ t (X t y t₁)) 2 (volume.restrict (euclidBall 0 ρ)) := by
  have hBm : MeasurableSet (euclidBall (0 : Vec 2) ρ) := (pipe_isOpen_euclidBall 0 ρ).measurableSet
  have hfin : IsFiniteMeasure (volume.restrict (euclidBall (0 : Vec 2) ρ)) :=
    ⟨by simpa using pipe_volume_euclidBall_lt_top ρ⟩
  have hcont : ContinuousOn (fun y => Θ t (X t y t₁)) (euclidBall 0 ρ) := by
    refine h.1.comp (ch.smoothF.continuous.comp
      (by fun_prop : Continuous fun y : Vec 2 => (t, y))).continuousOn ?_
    intro y hy; exact ⟨y, hy, rfl⟩
  refine MemLp.of_bound (hcont.aestronglyMeasurable hBm) |M| ((ae_restrict_iff' hBm).2
    (Filter.Eventually.of_forall fun y hy => ?_))
  rw [Real.norm_eq_abs]
  exact (h.abs_le ch ht hρ ⟨y, hy, rfl⟩).trans (le_abs_self _)

theorem slice_agree (ch : IsPipeChart b0 X t₁ T) {ρ₁ ρ₂ M₁ M₂ t : ℝ}
    (h₁ : SliceOK X t₁ s ρ₁ M₁ θ Θ t) (h₂ : SliceOK X t₁ s ρ₂ M₂ θ Θ' t)
    (ht : t ∈ Icc (t₁ - 8 * T) t₁) (ht' : t₁ - 8 * T < t) (hρ₁ : 0 < ρ₁) (hρ₁₂ : ρ₁ ≤ ρ₂)
    (hmem : ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ioo (t₁ - 8 * T) t₁ →
      MemLp (fun y => θ r (X r y t₁)) 2 (volume.restrict (euclidBall 0 ρ₂))) :
    ∀ x ∈ (fun y => X t y t₁) '' euclidBall 0 ρ₁, Θ t x = Θ' t x := by
  set B₁ : Set (Vec 2) := euclidBall 0 ρ₁ with hB₁
  set B₂ : Set (Vec 2) := euclidBall 0 ρ₂ with hB₂
  have hρ₂ : 0 < ρ₂ := hρ₁.trans_le hρ₁₂
  have hB₁m : MeasurableSet B₁ := (pipe_isOpen_euclidBall 0 ρ₁).measurableSet
  have hB₂m : MeasurableSet B₂ := (pipe_isOpen_euclidBall 0 ρ₂).measurableSet
  have hsub : B₁ ⊆ B₂ := euclidBall_subset_of_le hρ₁.le hρ₁₂
  have m1 := memLp_slice ch h₁ ht hρ₁
  have m2 := memLp_slice ch h₂ ht hρ₂
  have m2' : MemLp (fun y => Θ' t (X t y t₁)) 2 (volume.restrict B₁) :=
    m2.mono_measure (Measure.restrict_mono hsub le_rfl)
  set Dint : ℝ := ∫ y in B₁, (Θ t (X t y t₁) - Θ' t (X t y t₁)) ^ 2 with hDint
  have hD0 : 0 ≤ Dint := integral_nonneg fun y => sq_nonneg _
  have hI : ∀ᶠ r in 𝓝[<] t ⊓ ae (volume : Measure ℝ), r ∈ Ioo (t₁ - 8 * T) t := by
    have : Ioo (t₁ - 8 * T) t ∈ 𝓝[<] t := Ioo_mem_nhdsLT ht'
    exact (Filter.mem_inf_of_left this)
  have hae : ∀ᶠ r in 𝓝[<] t ⊓ ae (volume : Measure ℝ), r ∈ Ioo (t₁ - 8 * T) t₁ →
      MemLp (fun y => θ r (X r y t₁)) 2 (volume.restrict B₂) :=
    Filter.mem_inf_of_right hmem
  have hbound : ∀ᶠ r in 𝓝[<] t ⊓ ae (volume : Measure ℝ), Dint ≤
      2 * (∫ y in B₂, (θ r (X r y t₁) - Θ' t (X t y t₁)) ^ 2)
      + 2 * (∫ y in B₁, (θ r (X r y t₁) - Θ t (X t y t₁)) ^ 2) := by
    filter_upwards [hI, hae] with r hr1 hr2
    have hmr := hr2 ⟨hr1.1, hr1.2.trans_le ht.2⟩
    have hmr1 : MemLp (fun y => θ r (X r y t₁)) 2 (volume.restrict B₁) :=
      hmr.mono_measure (Measure.restrict_mono hsub le_rfl)
    have ha2 : MemLp (fun y => θ r (X r y t₁) - Θ' t (X t y t₁)) 2 (volume.restrict B₂) :=
      hmr.sub m2
    have ha1 : MemLp (fun y => θ r (X r y t₁) - Θ' t (X t y t₁)) 2 (volume.restrict B₁) :=
      hmr1.sub m2'
    have hb1 : MemLp (fun y => -(θ r (X r y t₁) - Θ t (X t y t₁))) 2 (volume.restrict B₁) :=
      (hmr1.sub m1).neg
    have hsq := integral_sq_add_le ha1.integrable_sq hb1.integrable_sq
    have heq : ∀ y, (θ r (X r y t₁) - Θ' t (X t y t₁)) + -(θ r (X r y t₁) - Θ t (X t y t₁)) =
        Θ t (X t y t₁) - Θ' t (X t y t₁) := fun y => by ring
    simp only [heq, neg_sq] at hsq
    have hmono : ∫ y in B₁, (θ r (X r y t₁) - Θ' t (X t y t₁)) ^ 2 ≤
        ∫ y in B₂, (θ r (X r y t₁) - Θ' t (X t y t₁)) ^ 2 :=
      setIntegral_mono_set ha2.integrable_sq (Filter.Eventually.of_forall fun y => sq_nonneg _)
        (Filter.Eventually.of_forall hsub)
    linarith
  have hlim : Tendsto (fun r => 2 * (∫ y in B₂, (θ r (X r y t₁) - Θ' t (X t y t₁)) ^ 2)
      + 2 * (∫ y in B₁, (θ r (X r y t₁) - Θ t (X t y t₁)) ^ 2))
      (𝓝[<] t ⊓ ae (volume : Measure ℝ)) (𝓝 0) := by
    simpa using (h₂.2.1.const_mul 2).add (h₁.2.1.const_mul 2)
  have := nhdsLT_inf_ae_neBot t
  have hle : Dint ≤ 0 := ge_of_tendsto hlim hbound
  have hzero : Dint = 0 := le_antisymm hle hD0
  have hint : IntegrableOn (fun y => (Θ t (X t y t₁) - Θ' t (X t y t₁)) ^ 2) B₁ :=
    (m1.sub m2').integrable_sq
  have hae0 : (fun y => (Θ t (X t y t₁) - Θ' t (X t y t₁)) ^ 2) =ᵐ[volume.restrict B₁] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg _) hint).1 hzero
  have hcont : ∀ U : ℝ → Vec 2 → ℝ, ∀ ρ : ℝ, ContinuousOn (U t) ((fun y => X t y t₁) '' euclidBall 0 ρ) →
      ContinuousOn (fun y => U t (X t y t₁)) (euclidBall 0 ρ) := by
    intro U ρ hU
    refine hU.comp (ch.smoothF.continuous.comp
      (by fun_prop : Continuous fun y : Vec 2 => (t, y))).continuousOn ?_
    intro y hy; exact ⟨y, hy, rfl⟩
  have hc1 := hcont Θ ρ₁ h₁.1
  have hc2 : ContinuousOn (fun y => Θ' t (X t y t₁)) B₁ :=
    (hcont Θ' ρ₂ h₂.1).mono hsub
  have heqOn := Measure.eqOn_open_of_ae_eq hae0 (pipe_isOpen_euclidBall 0 ρ₁)
    ((hc1.sub hc2).pow 2) continuousOn_const
  rintro x ⟨y, hy, rfl⟩
  have := heqOn hy
  simp only [Pi.zero_apply] at this
  have h0 : Θ t (X t y t₁) - Θ' t (X t y t₁) = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 this
  linarith

/-- The exhausting radii and windows. -/
def ϱk (k : ℕ) : ℝ := (1 - 1 / ((k : ℝ) + 2)) / 8

def ϑk (k : ℕ) : ℝ := 4 * (1 - 1 / ((k : ℝ) + 2))

theorem ϱk_pos (k : ℕ) : 0 < ϱk k := by
  unfold ϱk
  have : 1 / ((k : ℝ) + 2) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num); linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  linarith

theorem ϱk_lt (k : ℕ) : ϱk k < 1 / 8 := by
  unfold ϱk
  have : 0 < 1 / ((k : ℝ) + 2) := by positivity
  linarith

theorem ϑk_pos (k : ℕ) : 0 < ϑk k := by
  unfold ϑk
  have : 1 / ((k : ℝ) + 2) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num); linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  linarith

theorem ϑk_lt (k : ℕ) : ϑk k < 4 := by
  unfold ϑk
  have : 0 < 1 / ((k : ℝ) + 2) := by positivity
  linarith

theorem ϱk_mono {k₀ k : ℕ} (h : k₀ ≤ k) : ϱk k₀ ≤ ϱk k := by
  unfold ϱk
  have : 1 / ((k : ℝ) + 2) ≤ 1 / ((k₀ : ℝ) + 2) := by
    apply one_div_le_one_div_of_le (by positivity)
    have : (k₀ : ℝ) ≤ k := by exact_mod_cast h
    linarith
  linarith

theorem ϑk_mono {k₀ k : ℕ} (h : k₀ ≤ k) : ϑk k₀ ≤ ϑk k := by
  unfold ϑk
  have : 1 / ((k : ℝ) + 2) ≤ 1 / ((k₀ : ℝ) + 2) := by
    apply one_div_le_one_div_of_le (by positivity)
    have : (k₀ : ℝ) ≤ k := by exact_mod_cast h
    linarith
  linarith

theorem exists_index {ϱ ϑ : ℝ} (hϱ : ϱ < 1 / 8) (hϑ : ϑ < 4) :
    ∃ k : ℕ, ϱ ≤ ϱk k ∧ ϑ ≤ ϑk k := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < min (1 - 8 * ϱ) (1 - ϑ / 4) from
    lt_min (by linarith) (by linarith))
  refine ⟨n, ?_, ?_⟩
  · have h1 : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    unfold ϱk
    have := (hn.trans_le' h1).trans_le (min_le_left _ _)
    linarith
  · have h1 : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    unfold ϑk
    have := (hn.trans_le' h1).trans_le (min_le_right _ _)
    linarith

open Classical in
theorem glue_slices (ch : IsPipeChart b0 X t₁ T) (hT : 0 < T) (hR : 0 < R) {θ : ℝ → Vec 2 → ℝ}
    (Mf : ℝ → ℝ → ℝ)
    (hmem : ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ioo (t₁ - 8 * T) t₁ →
      MemLp (fun y => θ r (X r y t₁)) 2 (volume.restrict (euclidBall 0 R)))
    (h : ∀ ϱ ϑ : ℝ, 0 < ϱ → ϱ < 1 / 8 → 0 < ϑ → ϑ < 4 → ∃ Θ : ℝ → Vec 2 → ℝ,
      ∀ t ∈ Icc (t₁ - ϑ * T) t₁, SliceOK X t₁ s (ϱ * R) (Mf ϱ ϑ) θ Θ t) :
    ∃ Θ : ℝ → Vec 2 → ℝ, ∀ ϱ ϑ : ℝ, 0 < ϱ → ϱ < 1 / 8 → 0 < ϑ → ϑ < 4 →
      ∀ t ∈ Icc (t₁ - ϑ * T) t₁, SliceOK X t₁ s (ϱ * R) (Mf ϱ ϑ) θ Θ t := by
  have hk : ∀ k : ℕ, ∃ Θ : ℝ → Vec 2 → ℝ, ∀ t ∈ Icc (t₁ - ϑk k * T) t₁,
      SliceOK X t₁ s (ϱk k * R) (Mf (ϱk k) (ϑk k)) θ Θ t :=
    fun k => h _ _ (ϱk_pos k) (ϱk_lt k) (ϑk_pos k) (ϑk_lt k)
  choose Θk hΘk using hk
  set Pk : ℕ → ℝ → Vec 2 → Prop := fun k t x =>
    t ∈ Icc (t₁ - ϑk k * T) t₁ ∧ X t₁ x t ∈ euclidBall 0 (ϱk k * R) with hPk
  set Θ : ℝ → Vec 2 → ℝ := fun t x =>
    if hex : ∃ k, Pk k t x then Θk (Nat.find hex) t x else 0 with hΘ
  have hmemk : ∀ k, ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ioo (t₁ - 8 * T) t₁ →
      MemLp (fun y => θ r (X r y t₁)) 2 (volume.restrict (euclidBall 0 (ϱk k * R))) := by
    intro k
    filter_upwards [hmem] with r hr hrI
    exact (hr hrI).mono_measure (Measure.restrict_mono (euclidBall_subset_of_le
      (mul_pos (ϱk_pos k) hR).le (by nlinarith [ϱk_lt k])) le_rfl)
  have hwin : ∀ k, ∀ t, t ∈ Icc (t₁ - ϑk k * T) t₁ → t₁ - 8 * T < t ∧ t ∈ Icc (t₁ - 8 * T) t₁ := by
    intro k t ht
    have : t₁ - 8 * T < t₁ - ϑk k * T := by nlinarith [ϑk_lt k]
    exact ⟨by linarith [ht.1], ⟨by linarith [ht.1], ht.2⟩⟩
  have hR8 : ∀ k, ϱk k * R ≤ R := fun k => by nlinarith [ϱk_lt k]
  -- agreement of the chosen representatives
  have hagree : ∀ k₀ k : ℕ, k₀ ≤ k → ∀ t x, Pk k₀ t x → Pk k t x → Θk k₀ t x = Θk k t x := by
    intro k₀ k hkk t x h0 h1
    obtain ⟨hw1, hw2⟩ := hwin k t h1.1
    have := slice_agree ch (hΘk k₀ t h0.1) (hΘk k t h1.1) hw2 hw1
      (mul_pos (ϱk_pos k₀) hR) (mul_le_mul_of_nonneg_right (ϱk_mono hkk) hR.le) (hmemk k)
    exact this x ((mem_sec_iff ch hw2 x).2 h0.2)
  have hglue : ∀ t x k, Pk k t x → Θ t x = Θk k t x := by
    intro t x k hkx
    have hex : ∃ k, Pk k t x := ⟨k, hkx⟩
    simp only [hΘ, hex, ↓reduceDIte]
    exact hagree _ _ (Nat.find_min' hex hkx) t x (Nat.find_spec hex) hkx
  refine ⟨Θ, fun ϱ ϑ hϱ0 hϱ8 hϑ0 hϑ4 t ht => ?_⟩
  obtain ⟨Θ', hΘ'⟩ := h ϱ ϑ hϱ0 hϱ8 hϑ0 hϑ4
  obtain ⟨k, hkϱ, hkϑ⟩ := exists_index hϱ8 hϑ4
  have htI : t ∈ Icc (t₁ - 8 * T) t₁ := ⟨by nlinarith [ht.1], ht.2⟩
  have ht8 : t₁ - 8 * T < t := by nlinarith [ht.1]
  refine (hΘ' t ht).congr fun x hx => ?_
  have hxH : X t₁ x t ∈ euclidBall 0 (ϱ * R) := (mem_sec_iff ch htI x).1 hx
  have hP : Pk k t x := by
    refine ⟨⟨by nlinarith [ht.1], ht.2⟩, ?_⟩
    exact euclidBall_subset_of_le (mul_pos hϱ0 hR).le (mul_le_mul_of_nonneg_right hkϱ hR.le) hxH
  rw [hglue t x k hP]
  have := slice_agree ch (hΘ' t ht) (hΘk k t hP.1) htI ht8 (mul_pos hϱ0 hR)
    (mul_le_mul_of_nonneg_right hkϱ hR.le) (hmemk k)
  exact (this x hx).symm
end

/-! # A local solution together with its slice representatives

`LocSolution` bundles what is used about a local energy solution `θ` and a function `Θ` whose
slices represent the traces of `θ`: the distributional equation, square integrability on the
outer pipe with a bound `Q₂` on `∬ θ²`, `L²` slices on the label ball `B_R`, and the conclusion of
the local theorem at all admissible `(ϱ, ϑ)` with bound `Cf ϱ ϑ * F`. -/

section
open AVRegularity.Applications

structure LocSolution (X : ℝ → Vec 2 → ℝ → Vec 2) (t₁ T R s : ℝ) (b : ℝ → Vec 2 → Vec 2) (κ : ℝ)
    (Cf : ℝ → ℝ → ℝ) (F Q₂ : ℝ) (θ Θ : ℝ → Vec 2 → ℝ) : Prop where
  weak : ∀ φ : ℝ × Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    tsupport φ ⊆ outerPipe (fun t y => X t y t₁) t₁ T R →
    ∫ p in outerPipe (fun t y => X t y t₁) t₁ T R, θ p.1 p.2 *
      (fderiv ℝ φ p (1, 0) + ∑ i : Fin 2, b p.1 p.2 i * fderiv ℝ φ p (0, basisVec i)
        + κ * ∑ i : Fin 2,
          fderiv ℝ (fun p' => fderiv ℝ φ p' (0, basisVec i)) p (0, basisVec i)) = 0
  l2 : MemLp (fun p : ℝ × Vec 2 => θ p.1 p.2) 2
    (volume.restrict (outerPipe (fun t y => X t y t₁) t₁ T R))
  q2 : ∫ p in outerPipe (fun t y => X t y t₁) t₁ T R, θ p.1 p.2 ^ 2 ≤ Q₂
  mem : ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ioo (t₁ - 8 * T) t₁ →
    MemLp (fun y => θ r (X r y t₁)) 2 (volume.restrict (euclidBall 0 R))
  slices : ∀ ϱ ϑ : ℝ, 0 < ϱ → ϱ < 1 / 8 → 0 < ϑ → ϑ < 4 → ∀ t ∈ Icc (t₁ - ϑ * T) t₁,
    SliceOK X t₁ s (ϱ * R) (Cf ϱ ϑ * F) θ Θ t

variable {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T R s : ℝ}
  {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {Cf : ℝ → ℝ → ℝ} {F Q₂ : ℝ} {θ Θ : ℝ → Vec 2 → ℝ}

theorem LocSolution.mem_sub (h : LocSolution X t₁ T R s b κ Cf F Q₂ θ Θ) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρR : ρ ≤ R) :
    ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ioo (t₁ - 8 * T) t₁ →
      MemLp (fun y => θ r (X r y t₁)) 2 (volume.restrict (euclidBall 0 ρ)) := by
  filter_upwards [h.mem] with r hr hrI
  exact (hr hrI).mono_measure (Measure.restrict_mono (euclidBall_subset_of_le hρ0 hρR) le_rfl)
end

/-! # Time modulus and equicontinuity of the slice representatives

`time_est`: for `(t', x')` in a compact `K` inside the slab `{t > t₁ - ϑT, |H| < ϱR}` and `t` near
`t'`, `|Θ t x' - Θ t' x'|` is bounded by the increment estimate `increment_est`.
`modulus_unif`: bound and modulus of continuity of `Θ` on a compact `K ⊆ E`, uniform over all
solutions with `κ ≤ κbar`. -/

section
open AVRegularity.Applications

variable {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T R s : ℝ}
  {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {Cf : ℝ → ℝ → ℝ} {F Q₂ : ℝ} {θ Θ : ℝ → Vec 2 → ℝ}

theorem pipe_volume_lt_top (ch : IsPipeChart b0 X t₁ T) (hT : 0 < T) :
    volume (outerPipe (fun t y => X t y t₁) t₁ T R) < ⊤ := by
  have h := (pipeMap_mp ch hT).measure_preimage_emb (pipeMap_measurableEmbedding ch hT)
    (outerPipe (fun t y => X t y t₁) t₁ T R)
  rw [pipeMap_preimage_outerPipe ch] at h
  rw [← h]
  exact volume_cylinder_lt_top t₁ T R

/-- The increment estimate at a point of the compact set. -/
theorem time_est (ch : IsPipeChart b0 X t₁ T) (hT : 0 < T) (hR : 0 < R) (hs : 0 < s)
    {Bb : ℝ} (hB : ∀ t x, ‖b t x‖ ≤ Bb) (hbc : Continuous fun p : ℝ × Vec 2 => b p.1 p.2)
    (hsol : LocSolution X t₁ T R s b κ Cf F Q₂ θ Θ)
    {ϱ ϑ : ℝ} (hϱ0 : 0 < ϱ) (hϱ8 : ϱ < 1 / 8) (hϑ0 : 0 < ϑ) (hϑ4 : ϑ < 4)
    {μ : ℝ} (hμ : 0 < μ) {x' : Vec 2} {t' : ℝ}
    (hmarg : ∀ q : ℝ × Vec 2, dist q (t', x') < μ →
      t₁ - ϑ * T < q.1 ∧ X t₁ q.2 q.1 ∈ euclidBall 0 (ϱ * R)) (ht' : t' ≤ t₁)
    {D : ℝ} (hD : ∀ r : ℝ, 0 < r → ∀ x y : Vec 2, ∀ j : Fin 2,
      |spaceGrad (mollK r x) y j| ≤ D * r⁻¹ ^ 3 ∧
      |spaceGrad (fun w => spaceGrad (mollK r x) w j) y j| ≤ D * r⁻¹ ^ 4)
    {t r : ℝ} (ht : t ≤ t₁) (htt : |t - t'| < μ / 2) (hr : 0 < r) (hrμ : r ≤ μ / 2) :
    |Θ t x' - Θ t' x'| ≤ 2 * ((Cf ϱ ϑ * F) * (2 * r) ^ s) +
      (2 * |Bb| * (D * r⁻¹ ^ 3) + 2 * (|κ| * (D * r⁻¹ ^ 4))) *
        (Real.sqrt |t - t'| * (Q₂ + (volume (Metric.closedBall (0 : Vec 2) r)).toReal) / 2) := by
  have hfin := pipe_volume_lt_top (R := R) ch hT
  have hρ0 : 0 < ϱ * R := mul_pos hϱ0 hR
  have hρR : ϱ * R ≤ R := by nlinarith
  have hmem := hsol.mem_sub hρ0.le hρR
  -- membership in the slab
  have hslab : ∀ u : ℝ, |u - t'| < μ → ∀ y : Vec 2, dist y x' < μ →
      t₁ - ϑ * T < u ∧ X t₁ y u ∈ euclidBall 0 (ϱ * R) := by
    intro u hu y hy
    refine hmarg (u, y) ?_
    rw [Prod.dist_eq, Real.dist_eq]
    exact max_lt hu hy
  have hlo : t₁ - 8 * T < t₁ - ϑ * T := by nlinarith
  have key : ∀ σ τ : ℝ, σ < τ → τ ≤ t₁ → |σ - t'| < μ / 2 → |τ - t'| < μ / 2 →
      |Θ τ x' - Θ σ x'| ≤ 2 * ((Cf ϱ ϑ * F) * (2 * r) ^ s) +
        (2 * |Bb| * (D * r⁻¹ ^ 3) + 2 * (|κ| * (D * r⁻¹ ^ 4))) *
          (Real.sqrt (τ - σ) * (Q₂ + (volume (Metric.closedBall (0 : Vec 2) r)).toReal) / 2) := by
    intro σ τ hστ hτ₁ hσ hτ
    have hσlo := (hslab σ (by linarith [abs_lt.1 hσ]) x' (by simpa using hμ)).1
    have hτlo := (hslab τ (by linarith [abs_lt.1 hτ]) x' (by simpa using hμ)).1
    refine increment_est ch hB hbc hfin hsol.l2 hsol.weak hρ0 hρR hmem hsol.q2 hστ hτ₁
      (η := μ / 4) (by linarith) hr
      (hsol.slices ϱ ϑ hϱ0 hϱ8 hϑ0 hϑ4 σ ⟨hσlo.le, by linarith⟩)
      (hsol.slices ϱ ϑ hϱ0 hϱ8 hϑ0 hϑ4 τ ⟨hτlo.le, hτ₁⟩) ?_ hD hs
    intro u hu
    have hu1 : |u - t'| < μ := by
      rw [abs_lt] at hσ hτ ⊢
      constructor <;> linarith [hu.1, hu.2]
    have hu2 : t₁ - 8 * T < u := by
      have := (hslab u hu1 x' (by simpa using hμ)).1
      linarith
    refine ⟨hu2, fun y hy => ?_⟩
    have hyd : dist y x' < μ := lt_of_le_of_lt (Metric.mem_closedBall.1 hy) (by linarith)
    have hmb := (hslab u hu1 y hyd).2
    have huI : u ∈ Icc (t₁ - 8 * T) t₁ := ⟨hu2.le, hu.2.trans hτ₁⟩
    exact (mem_sec_iff ch huI y).2 hmb
  rcases lt_trichotomy t t' with h | h | h
  · have := key t t' h ht' htt (by simp [hμ])
    rw [abs_sub_comm, abs_of_neg (sub_neg.2 h), neg_sub]
    exact this
  · subst h
    simp only [sub_self, abs_zero, Real.sqrt_zero, zero_mul, mul_zero, zero_div, add_zero]
    have h0 : dist (t, x') (t, x') < μ := by simpa using hμ
    obtain ⟨hlo', hb'⟩ := hmarg (t, x') h0
    have htI : t ∈ Icc (t₁ - 8 * T) t₁ := ⟨by linarith, ht⟩
    have hx : x' ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R) := (mem_sec_iff ch htI x').2 hb'
    have hM : 0 ≤ Cf ϱ ϑ * F := (abs_nonneg _).trans
      ((hsol.slices ϱ ϑ hϱ0 hϱ8 hϑ0 hϑ4 t ⟨hlo'.le, ht⟩).abs_le ch htI hρ0 hx)
    have : 0 ≤ (2 * r) ^ s := Real.rpow_nonneg (by linarith) _
    positivity
  · have := key t' t h ht (by simp [hμ]) htt
    rw [abs_of_pos (sub_pos.2 h)]
    exact this

theorem small_rpow {s c ε μ' : ℝ} (hs : 0 < s) (hc : 0 ≤ c) (hε : 0 < ε) (hμ' : 0 < μ') :
    ∃ r : ℝ, 0 < r ∧ r ≤ μ' ∧ c * r ^ s < ε := by
  obtain ⟨δ, hδ, -, hδε⟩ := exists_small_rpow_aux (c := c) (e := s) hs hε
  refine ⟨min δ μ', lt_min hδ hμ', min_le_right _ _, ?_⟩
  calc c * (min δ μ') ^ s ≤ c * δ ^ s :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (lt_min hδ hμ').le (min_le_left _ _) hs.le) hc
    _ < ε := hδε

/-- The explicit constant of the time estimate. -/
def timeConst (Bb D κ r Q V : ℝ) : ℝ :=
  (2 * |Bb| * (D * r⁻¹ ^ 3) + 2 * (|κ| * (D * r⁻¹ ^ 4))) * ((Q + V) / 2)

theorem timeConst_nonneg {Bb D κ r Q V : ℝ} (hD : 0 ≤ D) (hr : 0 < r) (hQV : 0 ≤ Q + V) :
    0 ≤ timeConst Bb D κ r Q V := by
  unfold timeConst
  have h1 : 0 ≤ D * r⁻¹ ^ 3 := by positivity
  have h2 : 0 ≤ D * r⁻¹ ^ 4 := by positivity
  positivity

theorem timeConst_mono {Bb D κ κbar r Q V : ℝ} (hD : 0 ≤ D) (hr : 0 < r) (hQV : 0 ≤ Q + V)
    (hκ0 : 0 ≤ κ) (hκb : κ ≤ κbar) : timeConst Bb D κ r Q V ≤ timeConst Bb D κbar r Q V := by
  unfold timeConst
  have h2 : 0 ≤ D * r⁻¹ ^ 4 := by positivity
  have h3 : 0 ≤ (Q + V) / 2 := by positivity
  refine mul_le_mul_of_nonneg_right ?_ h3
  rw [abs_of_nonneg hκ0, abs_of_nonneg (hκ0.trans hκb)]
  nlinarith

theorem time_arith {A ε h : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) (h0 : 0 ≤ h)
    (hh : h < (ε / (3 * (A + 1))) ^ 2) : A * Real.sqrt h < ε / 3 := by
  have hsq0 : Real.sqrt h < ε / (3 * (A + 1)) := by
    have h1 : Real.sqrt h < Real.sqrt ((ε / (3 * (A + 1))) ^ 2) := Real.sqrt_lt_sqrt h0 hh
    rwa [Real.sqrt_sq (by positivity)] at h1
  have h2 : (A + 1) * Real.sqrt h < ε / 3 := by
    have := mul_lt_mul_of_pos_left hsq0 (show 0 < A + 1 by linarith)
    calc (A + 1) * Real.sqrt h < (A + 1) * (ε / (3 * (A + 1))) := this
      _ = ε / 3 := by field_simp
  nlinarith [Real.sqrt_nonneg h]

theorem time_part {M0 Bb D κ κbar Q V r s ε h : ℝ} (hD : 0 ≤ D) (hr : 0 < r) (hQV : 0 ≤ Q + V)
    (hε : 0 < ε) (hκ0 : 0 ≤ κ) (hκb : κ ≤ κbar) (h0 : 0 ≤ h)
    (hM1 : 2 * (M0 * (2 * r) ^ s) < ε / 3)
    (hh : h < (ε / (3 * (timeConst Bb D κbar r Q V + 1))) ^ 2) :
    2 * (M0 * (2 * r) ^ s) + (2 * |Bb| * (D * r⁻¹ ^ 3) + 2 * (|κ| * (D * r⁻¹ ^ 4))) *
      (Real.sqrt h * (Q + V) / 2) < 2 * (ε / 3) := by
  have hA := timeConst_nonneg (Bb := Bb) (κ := κbar) hD hr hQV
  have h1 := time_arith hA hε h0 hh
  have h2 := timeConst_mono (Bb := Bb) hD hr hQV hκ0 hκb
  have h3 : (2 * |Bb| * (D * r⁻¹ ^ 3) + 2 * (|κ| * (D * r⁻¹ ^ 4))) *
      (Real.sqrt h * (Q + V) / 2) = timeConst Bb D κ r Q V * Real.sqrt h := by
    unfold timeConst; ring
  rw [h3]
  have h4 : timeConst Bb D κ r Q V * Real.sqrt h ≤ timeConst Bb D κbar r Q V * Real.sqrt h :=
    mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)
  linarith

theorem spatial_arith {M0 s rs c2 ε d : ℝ} (hs : 0 < s) (hM : 0 ≤ M0) (hrs : 0 < rs)
    (hc2 : c2 = |M0| * 2 ^ s) (hrsε : c2 * rs ^ s < ε) (hd : d < rs) (hd0 : 0 ≤ d) :
    M0 * (2 * d) ^ s < ε := by
  have h1 : (2 * d) ^ s ≤ (2 * rs) ^ s := Real.rpow_le_rpow (by linarith) (by linarith) hs.le
  calc M0 * (2 * d) ^ s ≤ M0 * (2 * rs) ^ s := mul_le_mul_of_nonneg_left h1 hM
    _ = c2 * rs ^ s := by
      rw [Real.mul_rpow (by norm_num) hrs.le, hc2, abs_of_nonneg hM]; ring
    _ < ε := hrsε

theorem first_arith {M0 s r0 c1 ε : ℝ} (hr0 : 0 < r0) (hc1 : c1 = 2 * |M0| * 2 ^ s)
    (hε : c1 * r0 ^ s < ε) : 2 * (M0 * (2 * r0) ^ s) < ε := by
  have : 2 * (M0 * (2 * r0) ^ s) ≤ c1 * r0 ^ s := by
    rw [Real.mul_rpow (by norm_num) hr0.le, hc1]
    have h4 : 0 ≤ 2 ^ s * r0 ^ s := by positivity
    have h5 : M0 ≤ |M0| := le_abs_self _
    nlinarith
  exact this.trans_lt hε

theorem modulus_unif (ch : IsPipeChart b0 X t₁ T) (hT : 0 < T) (hR : 0 < R) (hs : 0 < s)
    {Bb : ℝ} (hB : ∀ t x, ‖b t x‖ ≤ Bb) (hbc : Continuous fun p : ℝ × Vec 2 => b p.1 p.2)
    {Cf : ℝ → ℝ → ℝ} {F Q₂ κbar : ℝ} (hQ : 0 ≤ Q₂)
    {K : Set (ℝ × Vec 2)} (hK : IsCompact K) (hKE : K ⊆ eReg X t₁ T R) :
    ∃ M : ℝ, (∀ (κ : ℝ) (θ Θ : ℝ → Vec 2 → ℝ),
        LocSolution X t₁ T R s b κ Cf F Q₂ θ Θ → ∀ p ∈ K, |Θ p.1 p.2| ≤ M) ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ (κ : ℝ) (θ Θ : ℝ → Vec 2 → ℝ), 0 ≤ κ → κ ≤ κbar →
        LocSolution X t₁ T R s b κ Cf F Q₂ θ Θ → ∀ p ∈ K, ∀ q ∈ K, dist q p < δ →
          |Θ q.1 q.2 - Θ p.1 p.2| < ε := by
  obtain ⟨ϱ, ϑ, hϱ0, hϱ8, hϑ0, hϑ4, hslab⟩ := exists_slab ch hT hR hK hKE
  have hKs : ∀ p ∈ K, t₁ - ϑ * T < p.1 ∧ X t₁ p.2 p.1 ∈ euclidBall 0 (ϱ * R) :=
    fun p hp => ⟨(hslab p hp).1, (hslab p hp).2.2⟩
  obtain ⟨μ, hμ, hmarg⟩ := exists_margin ch hK hKs
  obtain ⟨D, hD0, hD⟩ := exists_kern_bound
  have hρ0 : 0 < ϱ * R := mul_pos hϱ0 hR
  have hlo : t₁ - 8 * T < t₁ - ϑ * T := by nlinarith
  have hsec : ∀ p ∈ K, p.1 ∈ Icc (t₁ - 8 * T) t₁ ∧
      p.2 ∈ (fun y => X p.1 y t₁) '' euclidBall 0 (ϱ * R) := by
    intro p hp
    have hI : p.1 ∈ Icc (t₁ - 8 * T) t₁ := ⟨by linarith [(hKs p hp).1], (hslab p hp).2.1⟩
    exact ⟨hI, (mem_sec_iff ch hI p.2).2 (hKs p hp).2⟩
  refine ⟨Cf ϱ ϑ * F, fun κ θ Θ hsol p hp => ?_, fun ε hε => ?_⟩
  · obtain ⟨hI, hx⟩ := hsec p hp
    exact (hsol.slices ϱ ϑ hϱ0 hϱ8 hϑ0 hϑ4 p.1 ⟨(hKs p hp).1.le, (hslab p hp).2.1⟩).abs_le ch hI
      hρ0 hx
  · obtain ⟨r0, hr0, hr0μ, hr0ε⟩ := small_rpow hs (c := 2 * |Cf ϱ ϑ * F| * 2 ^ s)
      (by positivity) (show 0 < ε / 3 by positivity) (show 0 < μ / 2 by positivity)
    have hV0 : 0 ≤ (volume (Metric.closedBall (0 : Vec 2) r0)).toReal := ENNReal.toReal_nonneg
    have hQV : 0 ≤ Q₂ + (volume (Metric.closedBall (0 : Vec 2) r0)).toReal := by linarith
    obtain ⟨rs, hrs, -, hrsε⟩ := small_rpow hs (μ' := 1) (c := |Cf ϱ ϑ * F| * 2 ^ s)
      (by positivity) (show 0 < ε / 3 by positivity) one_pos
    have hA0 := timeConst_nonneg (Bb := Bb) (κ := κbar) hD0 hr0 hQV
    have hδt0 : 0 < (ε / (3 * (timeConst Bb D κbar r0 Q₂
        (volume (Metric.closedBall (0 : Vec 2) r0)).toReal + 1))) ^ 2 := by positivity
    refine ⟨min (min (μ / 2) ((ε / (3 * (timeConst Bb D κbar r0 Q₂
        (volume (Metric.closedBall (0 : Vec 2) r0)).toReal + 1))) ^ 2)) rs,
      lt_min (lt_min (by positivity) hδt0) hrs, fun κ θ Θ hκ0 hκb hsol p hp q hq hdq => ?_⟩
    have hdq1 : dist q.1 p.1 < _ := lt_of_le_of_lt
      (by rw [Prod.dist_eq]; exact le_max_left _ _) hdq
    have hdq2 : dist q.2 p.2 < _ := lt_of_le_of_lt
      (by rw [Prod.dist_eq]; exact le_max_right _ _) hdq
    have hd1μ : |q.1 - p.1| < μ / 2 := by
      rw [← Real.dist_eq]; exact hdq1.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have hd1δ : |q.1 - p.1| < (ε / (3 * (timeConst Bb D κbar r0 Q₂
        (volume (Metric.closedBall (0 : Vec 2) r0)).toReal + 1))) ^ 2 := by
      rw [← Real.dist_eq]; exact hdq1.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hd2 : dist q.2 p.2 < rs := hdq2.trans_le (min_le_right _ _)
    obtain ⟨hqI, hqx⟩ := hsec q hq
    have hpt : dist (q.1, p.2) p < μ := by
      rw [Prod.dist_eq, Real.dist_eq]
      exact max_lt (by linarith) (by simpa using hμ)
    have hpx' : p.2 ∈ (fun y => X q.1 y t₁) '' euclidBall 0 (ϱ * R) :=
      (mem_sec_iff ch hqI p.2).2 (hmarg p hp (q.1, p.2) hpt).2
    have hslq := hsol.slices ϱ ϑ hϱ0 hϱ8 hϑ0 hϑ4 q.1 ⟨(hKs q hq).1.le, (hslab q hq).2.1⟩
    have hM : 0 ≤ Cf ϱ ϑ * F := (abs_nonneg _).trans (hslq.abs_le ch hqI hρ0 hqx)
    have hsp : |Θ q.1 q.2 - Θ q.1 p.2| < ε / 3 := by
      have h1 := hslq.holder ch hqI hρ0 hqx hpx'
      have hn : ‖q.2 - p.2‖ < rs := by simpa [dist_eq_norm] using hd2
      have h2 : eNorm (q.2 - p.2) ^ s ≤ (2 * ‖q.2 - p.2‖) ^ s :=
        Real.rpow_le_rpow (eNorm_nonneg _) (eNorm_le_two_mul_norm _) hs.le
      have h3 := spatial_arith (M0 := Cf ϱ ϑ * F) hs hM hrs rfl hrsε hn (norm_nonneg _)
      calc |Θ q.1 q.2 - Θ q.1 p.2| ≤ (Cf ϱ ϑ * F) * eNorm (q.2 - p.2) ^ s := h1
        _ ≤ (Cf ϱ ϑ * F) * (2 * ‖q.2 - p.2‖) ^ s := mul_le_mul_of_nonneg_left h2 hM
        _ < ε / 3 := h3
    have htime := time_est ch hT hR hs hB hbc hsol hϱ0 hϱ8 hϑ0 hϑ4 hμ
      (x' := p.2) (t' := p.1) (fun w hw => hmarg p hp w hw) (hslab p hp).2.1 hD
      (hslab q hq).2.1 hd1μ hr0 hr0μ
    have hM1 := first_arith (hc1 := rfl) hr0 hr0ε
    have hT2 := time_part (Bb := Bb) (κbar := κbar) hD0 hr0 hQV (show 0 < ε by exact hε) hκ0 hκb
      (abs_nonneg _) hM1 hd1δ
    have hsplit : Θ q.1 q.2 - Θ p.1 p.2 = (Θ q.1 q.2 - Θ q.1 p.2) + (Θ q.1 p.2 - Θ p.1 p.2) := by
      ring
    rw [hsplit]
    calc |(Θ q.1 q.2 - Θ q.1 p.2) + (Θ q.1 p.2 - Θ p.1 p.2)|
        ≤ |Θ q.1 q.2 - Θ q.1 p.2| + |Θ q.1 p.2 - Θ p.1 p.2| := abs_add_le _ _
      _ < ε := by linarith
end

/-! # Joint continuity of the glued representative on `E` -/

section
open AVRegularity.Applications

variable {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T R s : ℝ}
  {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {Cf : ℝ → ℝ → ℝ} {F Q₂ : ℝ} {θ Θ : ℝ → Vec 2 → ℝ}

theorem LocSolution.q2_nonneg (h : LocSolution X t₁ T R s b κ Cf F Q₂ θ Θ) : 0 ≤ Q₂ :=
  (integral_nonneg fun _ => sq_nonneg _).trans h.q2

/-- A compact neighbourhood of a point of `E` inside `E`. -/
theorem exists_compact_nhds (ch : IsPipeChart b0 X t₁ T) (hT : 0 < T) {p : ℝ × Vec 2}
    (hp : p ∈ eReg X t₁ T R) :
    ∃ η : ℝ, 0 < η ∧ IsCompact {q : ℝ × Vec 2 | dist q p ≤ η ∧ q.1 ≤ t₁} ∧
      {q : ℝ × Vec 2 | dist q p ≤ η ∧ q.1 ≤ t₁} ⊆ eReg X t₁ T R := by
  have hopen : IsOpen {q : ℝ × Vec 2 | t₁ - 4 * T < q.1 ∧ X t₁ q.2 q.1 ∈ euclidBall 0 (R / 8)} :=
    (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_ball_euclid _).preimage (continuous_lab ch))
  have hpm := (mem_eReg_iff ch hT p).1 hp
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen p ⟨hpm.1, hpm.2.2⟩
  refine ⟨ε / 2, by positivity, ?_, fun q hq => ?_⟩
  · exact (isCompact_closedBall p (ε / 2)).inter_right
      (isClosed_le continuous_fst continuous_const : IsClosed {q : ℝ × Vec 2 | q.1 ≤ t₁})
  · have := hball (Metric.mem_ball.2 (lt_of_le_of_lt hq.1 (by linarith)))
    exact (mem_eReg_iff ch hT q).2 ⟨this.1, hq.2, this.2⟩

theorem jointContinuousOn (ch : IsPipeChart b0 X t₁ T) (hT : 0 < T) (hR : 0 < R) (hs : 0 < s)
    {Bb : ℝ} (hB : ∀ t x, ‖b t x‖ ≤ Bb) (hbc : Continuous fun p : ℝ × Vec 2 => b p.1 p.2)
    (hsol : LocSolution X t₁ T R s b κ Cf F Q₂ θ Θ) (hκ0 : 0 ≤ κ) :
    ContinuousOn (fun p : ℝ × Vec 2 => Θ p.1 p.2) (eReg X t₁ T R) := by
  intro p hp
  obtain ⟨η, hη, hK, hKE⟩ := exists_compact_nhds ch hT hp
  obtain ⟨M, -, hmod⟩ := modulus_unif ch hT hR hs hB hbc (Cf := Cf) (F := F)
    (κbar := κ) hsol.q2_nonneg hK hKE
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := hmod ε hε
  refine ⟨min δ η, lt_min hδ hη, fun q hq hdq => ?_⟩
  have hqK : q ∈ {q : ℝ × Vec 2 | dist q p ≤ η ∧ q.1 ≤ t₁} :=
    ⟨(hdq.trans_le (min_le_right _ _)).le, ((mem_eReg_iff ch hT q).1 hq).2.1⟩
  have hpK : p ∈ {q : ℝ × Vec 2 | dist q p ≤ η ∧ q.1 ≤ t₁} :=
    ⟨by simpa using hη.le, ((mem_eReg_iff ch hT p).1 hp).2.1⟩
  have := hδε κ θ Θ hκ0 le_rfl hsol p hpK q hqK (hdq.trans_le (min_le_left _ _))
  rwa [Real.dist_eq]
end

end AVRegularity.Applications.LimitsLocal
end
