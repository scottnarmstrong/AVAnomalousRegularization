-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Applications.LimitsLocal.JointCont
import AVRegularity.External.FourierCarrierParseval
import AVRegularity.Applications.LocalEnergy.Mollifier
import AVRegularity.Applications.Pipe.LocalEnergy
import AVRegularity.Velocity.ExistsLimitVelocity
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.UniformSpace.Uniformizable

section
/-! # Arzelà–Ascoli on `E`

A sequence of functions, continuous on `E`, uniformly bounded and equicontinuous on every compact
subset of `E`, has a subsequence converging uniformly on every compact subset of `E` to a function
continuous on `E`. `E` is locally compact in the relative topology (a compact neighbourhood is the
intersection of a small closed ball with `{t ≤ t₁}`), second countable, hence σ-compact. -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Homogenization AVenhance Set

namespace AVRegularity.Applications.LimitsLocal

open AVRegularity.Applications

variable {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T R : ℝ}

theorem exists_uniform_subseq {E : Set (ℝ × Vec 2)} [WeaklyLocallyCompactSpace E]
    [SigmaCompactSpace E] {g : ℕ → ℝ × Vec 2 → ℝ} (hcont : ∀ n, ContinuousOn (g n) E)
    (hbd : ∀ K : Set (ℝ × Vec 2), K ⊆ E → IsCompact K → ∃ M : ℝ, ∀ n, ∀ p ∈ K, |g n p| ≤ M)
    (hequi : ∀ K : Set (ℝ × Vec 2), K ⊆ E → IsCompact K → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ n, ∀ p ∈ K, ∀ q ∈ K, dist q p < δ → |g n q - g n p| < ε) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ L : ℝ × Vec 2 → ℝ, ContinuousOn L E ∧
      ∀ K : Set (ℝ × Vec 2), K ⊆ E → IsCompact K →
        TendstoUniformlyOn (fun i p => g (σ i) p) L atTop K := by
  classical
  let F : ℕ → C(E, ℝ) := fun n => ⟨fun p => g n p.1, (hcont n).domRestrict⟩
  have hFapp : ∀ n (p : E), F n p = g n p.1 := fun n p => rfl
  have himg : ∀ K : Set E, IsCompact K → IsCompact (Subtype.val '' K) ∧ Subtype.val '' K ⊆ E :=
    fun K hK => ⟨hK.image continuous_subtype_val, by rintro _ ⟨p, -, rfl⟩; exact p.2⟩
  have hbounded : ∀ K : Set E, IsCompact K → ∃ M : ℝ, ∀ n : ℕ, ∀ x, x ∈ K → ‖F n x‖ ≤ M := by
    intro K hK
    obtain ⟨M, hM⟩ := hbd _ (himg K hK).2 (himg K hK).1
    exact ⟨M, fun n x hx => by rw [Real.norm_eq_abs, hFapp]; exact hM n _ ⟨x, hx, rfl⟩⟩
  have hequicont : ∀ K : Set E, IsCompact K → EquicontinuousOn (fun n x => F n x) K := by
    intro K hK
    refine (equicontinuous_restrict_iff _).1 (fun x₀ => ?_)
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := hequi _ (himg K hK).2 (himg K hK).1 ε hε
    refine ⟨δ, hδ, fun x hx n => ?_⟩
    have hdist : dist x.1.1 x₀.1.1 < δ := by simpa [Subtype.dist_eq] using hx
    have := hδ' n x₀.1.1 ⟨x₀.1, x₀.2, rfl⟩ x.1.1 ⟨x.1, x.2, rfl⟩ hdist
    simpa [hFapp, Real.dist_eq, abs_sub_comm] using this
  obtain ⟨φ, L, hφ, hlim⟩ := External.arzelaAscoliDiagonal F hbounded hequicont
  refine ⟨φ, hφ, fun p => if h : p ∈ E then L ⟨p, h⟩ else 0, ?_, ?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    have : (E.domRestrict fun p : ℝ × Vec 2 => if h : p ∈ E then L ⟨p, h⟩ else 0) =
        fun p => L p := by
      funext p
      simp only [Set.domRestrict_apply, p.2, ↓reduceDIte]
    rw [this]
    exact L.continuous
  · intro K hKE hK
    have hKX : IsCompact ((Subtype.val : E → ℝ × Vec 2) ⁻¹' K) := by
      rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
      rwa [Set.image_preimage_eq_of_subset (by simpa using hKE)]
    have hu := (tendstoLocallyUniformly_iff_forall_isCompact.1 hlim) _ hKX
    rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
    intro ε hε
    filter_upwards [hu ε hε] with n hn p hp
    have hpE : p ∈ E := hKE hp
    have := hn ⟨p, hpE⟩ hp
    simpa [hpE, hFapp] using this

theorem weaklyLocallyCompact_eReg (ch : IsPipeChart b0 X t₁ T) (hT : 0 < T) :
    WeaklyLocallyCompactSpace (eReg X t₁ T R) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨η, hη, hK, hKE⟩ := exists_compact_nhds ch hT x.2
  refine ⟨Subtype.val ⁻¹' {q : ℝ × Vec 2 | dist q x.1 ≤ η ∧ q.1 ≤ t₁}, ?_, ?_⟩
  · rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    rwa [Set.image_preimage_eq_of_subset (by simpa using hKE)]
  · have hnhds : {q : eReg X t₁ T R | dist q.1 x.1 ≤ η} ∈ 𝓝 x := by
      have : Metric.closedBall x.1 η ∈ 𝓝 x.1 := Metric.closedBall_mem_nhds _ hη
      exact (continuous_subtype_val.continuousAt).preimage_mem_nhds this
    refine Filter.mem_of_superset hnhds fun q hq => ⟨hq, ((mem_eReg_iff ch hT q.1).1 q.2).2.1⟩

end AVRegularity.Applications.LimitsLocal

namespace AVRegularity.Applications.LimitsLocal

theorem sigmaCompact_eReg {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T R : ℝ}
    (ch : IsPipeChart b0 X t₁ T) (hT : 0 < T) : SigmaCompactSpace (eReg X t₁ T R) := by
  have := weaklyLocallyCompact_eReg (R := R) ch hT
  infer_instance

end AVRegularity.Applications.LimitsLocal
end
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Filter Topology Homogenization AVenhance Set
namespace AVRegularity.Applications.LimitsLocal

/-! # The representative is almost everywhere equal to the solution

For the glued representative `Θ` (jointly continuous on `E`), the label `L²` distance
`φ_k(r) = ∫_{B_{ϱ_k R}} (θ(r,F_r y) - Θ(r,F_r y))² dy` has zero left limits (the left trace of `θ` is
`Θ(t)`, and `Θ` is jointly continuous), hence vanishes for a.e. `r`. Transport by the measure
preserving charts gives `Θ(r,·) = θ(r,·)` a.e. on the sections of `E`. -/

section
open AVRegularity.Applications

variable {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T R s : ℝ}
  {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {Cf : ℝ → ℝ → ℝ} {F Q₂ : ℝ} {θ Θ : ℝ → Vec 2 → ℝ}

theorem ϑk_strict (k : ℕ) : ϑk k < ϑk (k + 1) := by
  unfold ϑk
  have : 1 / (((k + 1 : ℕ) : ℝ) + 2) < 1 / ((k : ℝ) + 2) := by
    apply one_div_lt_one_div_of_lt (by positivity)
    push_cast; linarith
  linarith

theorem SliceOK.contOn_pull (ch : IsPipeChart b0 X t₁ T) {ρ ρ' M t : ℝ}
    (h : SliceOK X t₁ s ρ' M θ Θ t) (hρ : ρ ≤ ρ') (hρ0 : 0 ≤ ρ) :
    ContinuousOn (fun y => Θ t (X t y t₁)) (euclidBall 0 ρ) := by
  have hsub := euclidBall_subset_of_le hρ0 hρ
  refine (h.1.comp (ch.smoothF.continuous.comp
    (by fun_prop : Continuous fun y : Vec 2 => (t, y))).continuousOn ?_)
  intro y hy; exact ⟨y, hsub hy, rfl⟩

/-- The label distance of `θ` and `Θ` on the `k`-th ball. -/
def phiK (X : ℝ → Vec 2 → ℝ → Vec 2) (t₁ R : ℝ) (θ Θ : ℝ → Vec 2 → ℝ) (k : ℕ) (r : ℝ) : ℝ :=
  ∫ y in euclidBall 0 (ϱk k * R), (θ r (X r y t₁) - Θ r (X r y t₁)) ^ 2

theorem phi_tendsto (ch : IsPipeChart b0 X t₁ T) (hT : 0 < T) (hR : 0 < R)
    (hsol : LocSolution X t₁ T R s b κ Cf F Q₂ θ Θ)
    (hjc : ContinuousOn (fun p : ℝ × Vec 2 => Θ p.1 p.2) (eReg X t₁ T R)) {k : ℕ} {t : ℝ}
    (ht : t ∈ Ioc (t₁ - ϑk k * T) t₁) :
    Tendsto (phiK X t₁ R θ Θ k) (𝓝[<] t ⊓ ae (volume : Measure ℝ)) (𝓝 0) := by
  set ρ : ℝ := ϱk k * R with hρ
  set ρ' : ℝ := ϱk (k + 1) * R with hρ'
  have hρ0 : 0 < ρ := mul_pos (ϱk_pos k) hR
  have hρρ' : ρ ≤ ρ' := mul_le_mul_of_nonneg_right (ϱk_mono (Nat.le_succ k)) hR.le
  have hρ'R : ρ' ≤ R := by nlinarith [ϱk_lt (k + 1)]
  set B : Set (Vec 2) := euclidBall 0 ρ with hB
  have hBm : MeasurableSet B := (pipe_isOpen_euclidBall 0 ρ).measurableSet
  have hBfin : volume B < ⊤ := pipe_volume_euclidBall_lt_top ρ
  have hfinB : IsFiniteMeasure (volume.restrict B) := ⟨by simpa using hBfin⟩
  have hρ8 : ρ ≤ R / 8 := by nlinarith [ϱk_lt k]
  have hBsub : B ⊆ euclidBall 0 ρ' := euclidBall_subset_of_le hρ0.le hρρ'
  have htk : t ∈ Icc (t₁ - ϑk k * T) t₁ := ⟨ht.1.le, ht.2⟩
  have hslk := hsol.slices (ϱk k) (ϑk k) (ϱk_pos k) (ϱk_lt k) (ϑk_pos k) (ϑk_lt k) t htk
  have hsl1 : ∀ r ∈ Icc (t₁ - ϑk (k + 1) * T) t₁,
      SliceOK X t₁ s ρ' (Cf (ϱk (k + 1)) (ϑk (k + 1)) * F) θ Θ r := fun r hr =>
    hsol.slices (ϱk (k + 1)) (ϑk (k + 1)) (ϱk_pos _) (ϱk_lt _) (ϑk_pos _) (ϑk_lt _) r hr
  have hwin : ∀ r : ℝ, r ∈ Icc (t₁ - ϑk (k + 1) * T) t₁ →
      r ∈ Icc (t₁ - 8 * T) t₁ ∧ t₁ - 8 * T < r := fun r hr => by
    have : t₁ - 8 * T < t₁ - ϑk (k + 1) * T := by nlinarith [ϑk_lt (k + 1)]
    exact ⟨⟨by linarith [hr.1], hr.2⟩, by linarith [hr.1]⟩
  have htwin : t ∈ Icc (t₁ - ϑk (k + 1) * T) t₁ := by
    have := ϑk_strict k
    exact ⟨by nlinarith [ht.1], ht.2⟩
  set M' : ℝ := Cf (ϱk (k + 1)) (ϑk (k + 1)) * F with hM'
  have hWin : Ioo (t₁ - ϑk (k + 1) * T) t ∈ 𝓝[<] t := Ioo_mem_nhdsLT (by
    have := ϑk_strict k; nlinarith [ht.1])
  have hWin4 : Ioo (t₁ - 4 * T) t ∈ 𝓝[<] t := Ioo_mem_nhdsLT (by
    have := ϑk_lt k; nlinarith [ht.1])
  -- (a) the trace
  have ha := hslk.2.1
  -- (b) joint continuity gives convergence of the slices
  have hc : Tendsto (fun r => ∫ y in B, (Θ r (X r y t₁) - Θ t (X t y t₁)) ^ 2) (𝓝[<] t) (𝓝 0) := by
    have hlim := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict B)
      (l := 𝓝[<] t) (F := fun r y => (Θ r (X r y t₁) - Θ t (X t y t₁)) ^ 2)
      (f := fun _ => (0 : ℝ)) (bound := fun _ => (2 * |M'|) ^ 2) ?_ ?_ (integrable_const _) ?_
    · simpa using hlim
    · filter_upwards [hWin] with r hr
      have hr' := hsl1 r ⟨hr.1.le, hr.2.le.trans ht.2⟩
      have h1 := hr'.contOn_pull ch hρρ' hρ0.le
      have h2 := (hsl1 t htwin).contOn_pull ch hρρ' hρ0.le
      exact ((h1.sub h2).pow 2).aestronglyMeasurable hBm
    · filter_upwards [hWin] with r hr
      have hrI : r ∈ Icc (t₁ - ϑk (k + 1) * T) t₁ := ⟨hr.1.le, hr.2.le.trans ht.2⟩
      have hr' := hsl1 r hrI
      refine (ae_restrict_iff' hBm).2 (Filter.Eventually.of_forall fun y hy => ?_)
      have b1 : |Θ r (X r y t₁)| ≤ M' :=
        hr'.abs_le ch (hwin r hrI).1 (mul_pos (ϱk_pos _) hR) ⟨y, hBsub hy, rfl⟩
      have b2 : |Θ t (X t y t₁)| ≤ M' :=
        (hsl1 t htwin).abs_le ch (hwin t htwin).1 (mul_pos (ϱk_pos _) hR) ⟨y, hBsub hy, rfl⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
      have : |Θ r (X r y t₁) - Θ t (X t y t₁)| ≤ 2 * |M'| := by
        have := abs_sub (Θ r (X r y t₁)) (Θ t (X t y t₁))
        have h3 : M' ≤ |M'| := le_abs_self _
        linarith
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    · refine (ae_restrict_iff' hBm).2 (Filter.Eventually.of_forall fun y hy => ?_)
      have hy8 : y ∈ euclidBall 0 (R / 8) := euclidBall_subset_of_le hρ0.le hρ8 hy
      have hp : (t, X t y t₁) ∈ eReg X t₁ T R :=
        ⟨by have := ϑk_lt k; nlinarith [ht.1], ht.2, y, hy8, rfl⟩
      have hcw := hjc _ hp
      have hcurve : Continuous fun r : ℝ => (r, X r y t₁) :=
        continuous_id.prodMk (ch.smoothF.continuous.comp (continuous_id.prodMk continuous_const))
      have hγ : Tendsto (fun r : ℝ => (r, X r y t₁)) (𝓝[<] t) (𝓝[eReg X t₁ T R] (t, X t y t₁)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨hcurve.tendsto t |>.mono_left nhdsWithin_le_nhds, ?_⟩
        filter_upwards [hWin4] with r hr
        exact ⟨hr.1, hr.2.le.trans ht.2, y, hy8, rfl⟩
      have hg := hcw.tendsto.comp hγ
      have := (hg.sub_const (Θ t (X t y t₁))).pow 2
      simpa using this
  have hmemB : ∀ᶠ r in 𝓝[<] t ⊓ ae (volume : Measure ℝ), r ∈ Ioo (t₁ - ϑk (k + 1) * T) t ∧
      MemLp (fun y => θ r (X r y t₁)) 2 (volume.restrict B) := by
    have h1 : ∀ᶠ r in 𝓝[<] t ⊓ ae (volume : Measure ℝ), r ∈ Ioo (t₁ - ϑk (k + 1) * T) t :=
      Filter.mem_inf_of_left hWin
    have h2 : ∀ᶠ r in 𝓝[<] t ⊓ ae (volume : Measure ℝ), r ∈ Ioo (t₁ - 8 * T) t₁ →
        MemLp (fun y => θ r (X r y t₁)) 2 (volume.restrict B) := by
      refine Filter.mem_inf_of_right ?_
      filter_upwards [hsol.mem_sub hρ0.le (by nlinarith [ϱk_lt k] : ρ ≤ R)] with r hr using hr
    filter_upwards [h1, h2] with r hr1 hr2
    have hrI : r ∈ Icc (t₁ - ϑk (k + 1) * T) t₁ := ⟨hr1.1.le, hr1.2.le.trans ht.2⟩
    exact ⟨hr1, hr2 ⟨(hwin r hrI).2, hr1.2.trans_le ht.2⟩⟩
  have hbound : ∀ᶠ r in 𝓝[<] t ⊓ ae (volume : Measure ℝ), phiK X t₁ R θ Θ k r ≤
      2 * (∫ y in B, (θ r (X r y t₁) - Θ t (X t y t₁)) ^ 2) +
        2 * ∫ y in B, (Θ r (X r y t₁) - Θ t (X t y t₁)) ^ 2 := by
    filter_upwards [hmemB] with r ⟨hr1, hr2⟩
    have hrI : r ∈ Icc (t₁ - ϑk (k + 1) * T) t₁ := ⟨hr1.1.le, hr1.2.le.trans ht.2⟩
    have mt := memLp_slice ch hslk (hwin t htwin).1 hρ0
    have mr := (memLp_slice ch (hsl1 r hrI) (hwin r hrI).1 (mul_pos (ϱk_pos _) hR)).mono_measure
      (Measure.restrict_mono hBsub le_rfl)
    have ha1 : MemLp (fun y => θ r (X r y t₁) - Θ t (X t y t₁)) 2 (volume.restrict B) :=
      hr2.sub mt
    have hb1 : MemLp (fun y => Θ t (X t y t₁) - Θ r (X r y t₁)) 2 (volume.restrict B) :=
      mt.sub mr
    have hsq := integral_sq_add_le ha1.integrable_sq hb1.integrable_sq
    have heq : ∀ y, (θ r (X r y t₁) - Θ t (X t y t₁)) + (Θ t (X t y t₁) - Θ r (X r y t₁)) =
        θ r (X r y t₁) - Θ r (X r y t₁) := fun y => by ring
    simp only [heq] at hsq
    have hc' : ∫ y in B, (Θ t (X t y t₁) - Θ r (X r y t₁)) ^ 2 =
        ∫ y in B, (Θ r (X r y t₁) - Θ t (X t y t₁)) ^ 2 := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only; ring
    rw [hc'] at hsq
    exact hsq
  have hlim : Tendsto (fun r => 2 * (∫ y in B, (θ r (X r y t₁) - Θ t (X t y t₁)) ^ 2) +
      2 * ∫ y in B, (Θ r (X r y t₁) - Θ t (X t y t₁)) ^ 2)
      (𝓝[<] t ⊓ ae (volume : Measure ℝ)) (𝓝 0) := by
    simpa using (ha.const_mul 2).add ((hc.mono_left inf_le_left).const_mul 2)
  exact squeeze_zero' (Filter.Eventually.of_forall fun r =>
    integral_nonneg fun y => sq_nonneg _) hbound hlim

theorem exists_index_window {r t₁ T : ℝ} (hT : 0 < T) (hr : t₁ - 4 * T < r) :
    ∃ k : ℕ, t₁ - ϑk k * T < r := by
  have h1 : (t₁ - r) / T < 4 := by rw [div_lt_iff₀ hT]; linarith
  obtain ⟨k, -, hk⟩ := exists_index (ϱ := 0) (ϑ := ((t₁ - r) / T + 4) / 2) (by norm_num)
    (by linarith)
  refine ⟨k, ?_⟩
  have h2 : (t₁ - r) / T < ϑk k := by linarith
  rw [div_lt_iff₀ hT] at h2
  linarith

theorem slice_ae_k (ch : IsPipeChart b0 X t₁ T) (hT : 0 < T) (hR : 0 < R)
    (hsol : LocSolution X t₁ T R s b κ Cf F Q₂ θ Θ)
    (hjc : ContinuousOn (fun p : ℝ × Vec 2 => Θ p.1 p.2) (eReg X t₁ T R)) (k : ℕ) :
    ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ioc (t₁ - ϑk k * T) t₁ →
      ∀ᵐ x ∂(volume : Measure (Vec 2)), x ∈ (fun y => X r y t₁) '' euclidBall 0 (ϱk k * R) →
        Θ r x = θ r x := by
  set ρ : ℝ := ϱk k * R with hρ
  have hρ0 : 0 < ρ := mul_pos (ϱk_pos k) hR
  have hBm : MeasurableSet (euclidBall (0 : Vec 2) ρ) := (pipe_isOpen_euclidBall 0 ρ).measurableSet
  have hφ := ae_eq_zero_of_left_limits (φ := phiK X t₁ R θ Θ k) (J := Ioc (t₁ - ϑk k * T) t₁)
    (fun r => integral_nonneg fun y => sq_nonneg _) (fun t ht => phi_tendsto ch hT hR hsol hjc ht)
  have hne : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ t₁ := by rw [ae_iff]; simp
  filter_upwards [hφ, hne, hsol.mem_sub hρ0.le (by nlinarith [ϱk_lt k] : ρ ≤ R)] with r h0 h1 h2 hr
  have hrI : r ∈ Icc (t₁ - ϑk k * T) t₁ := ⟨hr.1.le, hr.2⟩
  have hw : t₁ - 8 * T < t₁ - ϑk k * T := by nlinarith [ϑk_lt k]
  have hrw : r ∈ Icc (t₁ - 8 * T) t₁ := ⟨by linarith [hr.1], hr.2⟩
  have hrlt : r ∈ Ioo (t₁ - 8 * T) t₁ := ⟨by linarith [hr.1], lt_of_le_of_ne hr.2 h1⟩
  have hsl := hsol.slices (ϱk k) (ϑk k) (ϱk_pos k) (ϱk_lt k) (ϑk_pos k) (ϑk_lt k) r hrI
  have hmr := memLp_slice ch hsl hrw hρ0
  have hdiff : MemLp (fun y => θ r (X r y t₁) - Θ r (X r y t₁)) 2
      (volume.restrict (euclidBall 0 ρ)) := (h2 hrlt).sub hmr
  have hz := h0 hr
  have hae0 : (fun y => (θ r (X r y t₁) - Θ r (X r y t₁)) ^ 2) =ᵐ[volume.restrict
      (euclidBall 0 ρ)] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg _) hdiff.integrable_sq).1 hz
  have hy : ∀ᵐ y ∂(volume.restrict (euclidBall 0 ρ)), Θ r (X r y t₁) = θ r (X r y t₁) := by
    filter_upwards [hae0] with y hy
    have : θ r (X r y t₁) - Θ r (X r y t₁) = 0 := by
      simpa using hy
    linarith
  obtain ⟨hmp, hemb⟩ := chart_mp_emb ch hrw
  have hmp' := hmp.restrict_image_emb hemb (euclidBall 0 ρ)
  have hx : ∀ᵐ x ∂(volume.restrict ((fun y => X r y t₁) '' euclidBall 0 ρ)),
      Θ r x = θ r x := by
    rw [← hmp'.map_eq]
    exact (hemb.ae_map_iff (p := fun x => Θ r x = θ r x)).2 hy
  exact (ae_restrict_iff' (hemb.measurableSet_image.2 hBm)).1 hx

theorem slice_ae (ch : IsPipeChart b0 X t₁ T) (hT : 0 < T) (hR : 0 < R)
    (hsol : LocSolution X t₁ T R s b κ Cf F Q₂ θ Θ)
    (hjc : ContinuousOn (fun p : ℝ × Vec 2 => Θ p.1 p.2) (eReg X t₁ T R)) :
    ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ioo (t₁ - 4 * T) t₁ →
      ∀ᵐ x ∂(volume : Measure (Vec 2)), x ∈ (fun y => X r y t₁) '' euclidBall 0 (R / 8) →
        Θ r x = θ r x := by
  have hall : ∀ᵐ r ∂(volume : Measure ℝ), ∀ k : ℕ, r ∈ Ioc (t₁ - ϑk k * T) t₁ →
      ∀ᵐ x ∂(volume : Measure (Vec 2)), x ∈ (fun y => X r y t₁) '' euclidBall 0 (ϱk k * R) →
        Θ r x = θ r x := ae_all_iff.2 fun k => slice_ae_k ch hT hR hsol hjc k
  filter_upwards [hall] with r hr hrI
  obtain ⟨k₀, hk₀⟩ := exists_index_window hT hrI.1
  have hrw : r ∈ Icc (t₁ - 8 * T) t₁ := ⟨by linarith [hrI.1], hrI.2.le⟩
  have hk : ∀ k : ℕ, k₀ ≤ k → ∀ᵐ x ∂(volume : Measure (Vec 2)),
      x ∈ (fun y => X r y t₁) '' euclidBall 0 (ϱk k * R) → Θ r x = θ r x := fun k hkk =>
    hr k ⟨lt_of_le_of_lt (by nlinarith [ϑk_mono hkk]) hk₀, hrI.2.le⟩
  have hk' : ∀ᵐ x ∂(volume : Measure (Vec 2)), ∀ k : ℕ, k₀ ≤ k →
      x ∈ (fun y => X r y t₁) '' euclidBall 0 (ϱk k * R) → Θ r x = θ r x :=
    ae_all_iff.2 fun k => by
      by_cases hkk : k₀ ≤ k
      · filter_upwards [hk k hkk] with x hx _ using hx
      · exact Filter.Eventually.of_forall fun x h => absurd h hkk
  filter_upwards [hk'] with x hx hxm
  have hxH : X t₁ x r ∈ euclidBall 0 (R / 8) := (mem_sec_iff ch hrw x).1 hxm
  set m : ℝ := Real.sqrt (vecNormSq (X t₁ x r - 0)) with hm
  have hmlt : m < R / 8 := by
    rw [hm]
    exact (Real.sqrt_lt' (by positivity)).2 hxH
  obtain ⟨k₁, hk₁, -⟩ := exists_index (ϱ := (m / R + 1 / 8) / 2) (ϑ := 0) (by
    have : m / R < 1 / 8 := by rw [div_lt_iff₀ hR]; linarith
    linarith) (by norm_num)
  have hk₂ : m < ϱk (max k₀ k₁) * R := by
    have h1 : (m / R + 1 / 8) / 2 ≤ ϱk (max k₀ k₁) := hk₁.trans (ϱk_mono (le_max_right _ _))
    have h2 : m / R < (m / R + 1 / 8) / 2 := by
      have : m / R < 1 / 8 := by rw [div_lt_iff₀ hR]; linarith
      linarith
    have := h2.trans_le h1
    rwa [div_lt_iff₀ hR] at this
  refine hx (max k₀ k₁) (le_max_left _ _) ?_
  refine (mem_sec_iff ch hrw x).2 ?_
  have hm0 : 0 ≤ m := Real.sqrt_nonneg _
  simp only [euclidBall, mem_ofPred_eq]
  have hmm : m ^ 2 = vecNormSq (X t₁ x r - 0) := Real.sq_sqrt (vecNormSq_nonneg _)
  rw [← hmm]
  exact pow_lt_pow_left₀ hk₂ hm0 two_ne_zero

theorem measurableSet_eReg (ch : IsPipeChart b0 X t₁ T) (hT : 0 < T) :
    MeasurableSet (eReg X t₁ T R) := by
  have : eReg X t₁ T R = {p : ℝ × Vec 2 | t₁ - 4 * T < p.1} ∩ ({p | p.1 ≤ t₁} ∩
      (fun p : ℝ × Vec 2 => X t₁ p.2 p.1) ⁻¹' euclidBall 0 (R / 8)) := by
    ext p
    rw [mem_eReg_iff ch hT]
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage]
  rw [this]
  exact ((isOpen_lt continuous_const continuous_fst).measurableSet).inter
    ((isClosed_le continuous_fst continuous_const).measurableSet.inter
      ((isOpen_ball_euclid _).preimage (continuous_lab ch)).measurableSet)

theorem eReg_subset_pipe (hT : 0 < T) (hR : 0 < R) :
    eReg X t₁ T R ⊆ outerPipe (fun t y => X t y t₁) t₁ T R ∪ {p : ℝ × Vec 2 | p.1 = t₁} := by
  rintro p ⟨h1, h2, y, hy, hp⟩
  rcases lt_or_eq_of_le h2 with h | h
  · left
    refine ⟨by linarith, h, y, ?_, hp⟩
    refine euclidBall_subset_of_le (by positivity) (by linarith) hy
  · right; exact h

/-- **The representative is a.e. equal to `θ` on `E`.** -/
theorem ae_eq_eReg (ch : IsPipeChart b0 X t₁ T) (hT : 0 < T) (hR : 0 < R)
    (hsol : LocSolution X t₁ T R s b κ Cf F Q₂ θ Θ)
    (hjc : ContinuousOn (fun p : ℝ × Vec 2 => Θ p.1 p.2) (eReg X t₁ T R)) :
    (fun p : ℝ × Vec 2 => Θ p.1 p.2) =ᵐ[volume.restrict (eReg X t₁ T R)]
      (fun p : ℝ × Vec 2 => θ p.1 p.2) := by
  set E := eReg X t₁ T R with hE
  have hEm : MeasurableSet E := measurableSet_eReg ch hT
  set f : ℝ × Vec 2 → ℝ := fun p => Θ p.1 p.2 - θ p.1 p.2 with hf
  have hZ : volume {p : ℝ × Vec 2 | p.1 = t₁} = 0 := by
    have : {p : ℝ × Vec 2 | p.1 = t₁} = {t₁} ×ˢ (Set.univ : Set (Vec 2)) := by
      ext p; simp
    rw [this, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have hle : volume.restrict E ≤ volume.restrict (outerPipe (fun t y => X t y t₁) t₁ T R) := by
    calc volume.restrict E ≤ volume.restrict (outerPipe (fun t y => X t y t₁) t₁ T R ∪
          {p : ℝ × Vec 2 | p.1 = t₁}) := Measure.restrict_mono (eReg_subset_pipe hT hR) le_rfl
      _ ≤ volume.restrict (outerPipe (fun t y => X t y t₁) t₁ T R) +
          volume.restrict {p : ℝ × Vec 2 | p.1 = t₁} := Measure.restrict_union_le _ _
      _ = volume.restrict (outerPipe (fun t y => X t y t₁) t₁ T R) := by
        rw [Measure.restrict_eq_zero.2 hZ, add_zero]
  have hθm : AEMeasurable (fun p : ℝ × Vec 2 => θ p.1 p.2) (volume.restrict E) :=
    hsol.l2.aestronglyMeasurable.aemeasurable.mono_measure hle
  have hΘm : AEMeasurable (fun p : ℝ × Vec 2 => Θ p.1 p.2) (volume.restrict E) :=
    hjc.aemeasurable hEm
  have hfm : AEMeasurable f (volume.restrict E) := hΘm.sub hθm
  set g : ℝ × Vec 2 → ℝ := hfm.mk f with hg
  have hgm : Measurable g := hfm.measurable_mk
  have hfg : f =ᵐ[volume.restrict E] g := hfm.ae_eq_mk
  -- the slice statement
  have hA : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ x ∂(volume : Measure (Vec 2)), (t, x) ∈ E →
      f (t, x) = g (t, x) := by
    have h1 : ∀ᵐ z ∂(volume : Measure (ℝ × Vec 2)), z ∈ E → f z = g z :=
      (ae_restrict_iff' hEm).1 hfg
    rw [Measure.volume_eq_prod] at h1
    exact Measure.ae_ae_of_ae_prod h1
  have hB : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ x ∂(volume : Measure (Vec 2)), (t, x) ∈ E →
      f (t, x) = 0 := by
    have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ t₁ := by rw [ae_iff]; simp
    filter_upwards [slice_ae ch hT hR hsol hjc, hne] with t ht hne'
    by_cases htI : t ∈ Ioo (t₁ - 4 * T) t₁
    · filter_upwards [ht htI] with x hx hxE
      obtain ⟨-, -, y, hy, hxy⟩ := hxE
      have := hx ⟨y, hy, hxy.symm⟩
      simp only [hf, this, sub_self]
    · exact Filter.Eventually.of_forall fun x hxE => by
        exfalso
        obtain ⟨h1, h2, -⟩ := hxE
        exact htI ⟨h1, lt_of_le_of_ne h2 hne'⟩
  have hset : MeasurableSet {z : ℝ × Vec 2 | z ∈ E → g z = 0} :=
    (by
      have : {z : ℝ × Vec 2 | z ∈ E → g z = 0} = Eᶜ ∪ g ⁻¹' {0} := by
        ext z; simp [imp_iff_not_or]
      rw [this]
      exact hEm.compl.union (hgm (measurableSet_singleton 0)))
  have hprod : ∀ᵐ z ∂(volume : Measure (ℝ × Vec 2)), z ∈ E → g z = 0 := by
    rw [Measure.volume_eq_prod, Measure.ae_prod_iff_ae_ae hset]
    filter_upwards [hA, hB] with t h1 h2
    filter_upwards [h1, h2] with x hx1 hx2 hxE
    rw [← hx1 hxE]; exact hx2 hxE
  have hg0 : g =ᵐ[volume.restrict E] 0 := by
    filter_upwards [(ae_restrict_iff' hEm).2 hprod] with z hz using hz
  filter_upwards [hfg, hg0] with z h1 h2
  have : f z = 0 := by rw [h1]; exact h2
  simpa [hf, sub_eq_zero] using this
end

/-! # Passing to the limit in the equation

If `Θ_i → L` uniformly on compact subsets of `E`, `κ_i → 0` and each `Θ_i` is a representative of a
local solution, then `∫ L (∂ₜφ + b·∇φ) = 0` for `φ ∈ C_c^∞(int E)`. -/

section
open AVRegularity.Applications

theorem tendsto_integral_of_uniform {E S : Set (ℝ × Vec 2)} (hS : IsCompact S) (hSE : S ⊆ E)
    {Θi : ℕ → ℝ × Vec 2 → ℝ} {L : ℝ × Vec 2 → ℝ} (hc : ∀ i, ContinuousOn (Θi i) E)
    (hL : ContinuousOn L E) (hu : TendstoUniformlyOn Θi L atTop S)
    {H : ℝ × Vec 2 → ℝ} (hH : Continuous H) (hsupp : ∀ p, p ∉ S → H p = 0) :
    Tendsto (fun i => ∫ p, Θi i p * H p) atTop (𝓝 (∫ p, L p * H p)) := by
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  have hHc : HasCompactSupport H :=
    HasCompactSupport.of_support_subset_isCompact hS fun p hp => by
      by_contra hn; exact hp (hsupp p hn)
  have hint : ∀ (U : ℝ × Vec 2 → ℝ), ContinuousOn U E → Integrable (fun p => U p * H p) := by
    intro U hU
    have h1 : IntegrableOn (fun p => U p * H p) S :=
      ((hU.mono hSE).mul hH.continuousOn).integrableOn_compact hS
    rw [← integrableOn_iff_integrable_of_support_subset (s := S)]
    · exact h1
    · intro p hp
      by_contra hn; exact hp (by simp [hsupp p hn])
  obtain ⟨ML, hML⟩ := hS.exists_bound_of_continuousOn (hL.mono hSE)
  have hbound_int : Integrable (fun p => (ML + 1) * |H p|) :=
    (hH.integrable_of_hasCompactSupport hHc).abs.const_mul _
  have hev : ∀ᶠ i in atTop, ∀ p ∈ S, ‖Θi i p‖ ≤ ML + 1 := by
    have := (Metric.tendstoUniformlyOn_iff.1 hu) 1 one_pos
    filter_upwards [this] with i hi p hp
    have h1 := hi p hp
    rw [Real.dist_eq] at h1
    have h2 := hML p hp
    rw [Real.norm_eq_abs] at h2 ⊢
    have := abs_sub_abs_le_abs_sub (Θi i p) (L p)
    rw [abs_sub_comm] at this
    linarith [(abs_lt.1 h1).2, abs_nonneg (Θi i p - L p)]
  refine tendsto_integral_filter_of_dominated_convergence (fun p => (ML + 1) * |H p|)
    (Filter.Eventually.of_forall fun i => (hint (Θi i) (hc i)).aestronglyMeasurable) ?_
    hbound_int ?_
  · filter_upwards [hev] with i hi
    refine Filter.Eventually.of_forall fun p => ?_
    by_cases hp : p ∈ S
    · rw [norm_mul, Real.norm_eq_abs (H p)]
      exact mul_le_mul_of_nonneg_right (hi p hp) (abs_nonneg _)
    · simp [hsupp p hp]
  · refine Filter.Eventually.of_forall fun p => ?_
    by_cases hp : p ∈ S
    · exact (hu.tendsto_at hp).mul_const _
    · simp [hsupp p hp]

variable {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T R s : ℝ}
  {b : ℝ → Vec 2 → Vec 2} {Cf : ℝ → ℝ → ℝ} {F Q₂ : ℝ}

theorem interior_eReg_subset (ch : IsPipeChart b0 X t₁ T) (hT : 0 < T) (hR : 0 < R) :
    interior (eReg X t₁ T R) ⊆ outerPipe (fun t y => X t y t₁) t₁ T R := by
  intro p hp
  have hpE := interior_subset hp
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior p hp
  have hq : (p.1 + ε / 2, p.2) ∈ eReg X t₁ T R :=
    interior_subset (hball (by
      rw [Metric.mem_ball, Prod.dist_eq]
      simp only [dist_self, Real.dist_eq, add_sub_cancel_left]
      refine max_lt ?_ hε
      rw [abs_of_pos (by positivity)]; linarith))
  have hlt : p.1 < t₁ := by
    have := ((mem_eReg_iff ch hT _).1 hq).2.1
    simp only at this; linarith
  rcases eReg_subset_pipe hT hR hpE with h | h
  · exact h
  · exact absurd h (ne_of_lt hlt)

theorem limit_equation (ch : IsPipeChart b0 X t₁ T) (hT : 0 < T) (hR : 0 < R) (hs : 0 < s)
    {Bb : ℝ} (hB : ∀ t x, ‖b t x‖ ≤ Bb) (hbc : Continuous fun p : ℝ × Vec 2 => b p.1 p.2)
    {κ : ℕ → ℝ} {θ Θ : ℕ → ℝ → Vec 2 → ℝ}
    (hsol : ∀ i, LocSolution X t₁ T R s b (κ i) Cf F Q₂ (θ i) (Θ i))
    (hκ0 : ∀ i, 0 ≤ κ i) (hκ : Tendsto κ atTop (𝓝 0)) {σ : ℕ → ℕ} (hσ : StrictMono σ)
    {L : ℝ × Vec 2 → ℝ} (hL : ContinuousOn L (eReg X t₁ T R))
    (hu : ∀ K : Set (ℝ × Vec 2), K ⊆ eReg X t₁ T R → IsCompact K →
      TendstoUniformlyOn (fun i (p : ℝ × Vec 2) => Θ (σ i) p.1 p.2) L atTop K)
    {φ : ℝ × Vec 2 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hts : tsupport φ ⊆ interior (eReg X t₁ T R)) :
    ∫ p, L p * (fderiv ℝ φ p (1, 0) +
      ∑ j : Fin 2, b p.1 p.2 j * fderiv ℝ φ p (0, basisVec j)) = 0 := by
  set E := eReg X t₁ T R with hE
  set S := tsupport φ with hS
  have hSc : IsCompact S := hφc.isCompact
  have hSE : S ⊆ E := hts.trans interior_subset
  have hSP : S ⊆ outerPipe (fun t y => X t y t₁) t₁ T R :=
    hts.trans (interior_eReg_subset ch hT hR)
  have hEm : MeasurableSet E := measurableSet_eReg ch hT
  have hjc : ∀ i, ContinuousOn (fun p : ℝ × Vec 2 => Θ i p.1 p.2) E := fun i =>
    jointContinuousOn ch hT hR hs hB hbc (hsol i) (hκ0 i)
  set A : ℝ × Vec 2 → ℝ := fun p => fderiv ℝ φ p (1, 0) +
    ∑ j : Fin 2, b p.1 p.2 j * fderiv ℝ φ p (0, basisVec j) with hA
  set Bq : ℝ × Vec 2 → ℝ := fun p => ∑ i : Fin 2,
    fderiv ℝ (fun p' => fderiv ℝ φ p' (0, basisVec i)) p (0, basisVec i) with hBq
  have hφ1 : ∀ v, Continuous fun p => fderiv ℝ φ p v := fun v =>
    (contDiff_fderiv_apply_of_smooth hφ v).continuous
  have hAc : Continuous A := by
    refine (hφ1 (1, 0)).add (continuous_finsetSum _ fun j _ => ?_)
    exact (((continuous_apply j).comp hbc)).mul (hφ1 _)
  have hBc : Continuous Bq :=
    continuous_finsetSum _ fun i _ => (contDiff_fderiv_apply_of_smooth
      (contDiff_fderiv_apply_of_smooth hφ (0, basisVec i)) (0, basisVec i)).continuous
  have hA0 : ∀ p, p ∉ S → A p = 0 := by
    intro p hp
    have h1 : ∀ v, fderiv ℝ φ p v = 0 := fun v => by simp [fderiv_of_notMem_tsupport (𝕜 := ℝ) hp]
    simp [hA, h1]
  have hB0 : ∀ p, p ∉ S → Bq p = 0 := by
    intro p hp
    have h2 : ∀ i : Fin 2, p ∉ tsupport (fun p' => fderiv ℝ φ p' (0, basisVec i)) := fun i h =>
      hp (tsupport_fderiv_apply_subset φ _ h)
    simp [hBq, fderiv_of_notMem_tsupport (𝕜 := ℝ) (h2 _)]
  -- the equation for each `i`
  have hid : ∀ i, (∫ p, Θ i p.1 p.2 * A p) + κ i * ∫ p, Θ i p.1 p.2 * Bq p = 0 := by
    intro i
    have hae := ae_eq_eReg ch hT hR (hsol i) (hjc i)
    have hw := (hsol i).weak φ hφ hφc hSP
    have hform : ∀ p : ℝ × Vec 2, θ i p.1 p.2 *
        (fderiv ℝ φ p (1, 0) + ∑ j : Fin 2, b p.1 p.2 j * fderiv ℝ φ p (0, basisVec j)
          + κ i * ∑ j : Fin 2,
            fderiv ℝ (fun p' => fderiv ℝ φ p' (0, basisVec j)) p (0, basisVec j)) =
        θ i p.1 p.2 * (A p + κ i * Bq p) := fun p => rfl
    simp_rw [hform] at hw
    have h1 : ∫ p in outerPipe (fun t y => X t y t₁) t₁ T R, θ i p.1 p.2 * (A p + κ i * Bq p) =
        ∫ p, θ i p.1 p.2 * (A p + κ i * Bq p) := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp => ?_
      have : p ∉ S := fun h => hp (hSP h)
      simp [hA0 p this, hB0 p this]
    have h2 : ∫ p, θ i p.1 p.2 * (A p + κ i * Bq p) =
        ∫ p in E, θ i p.1 p.2 * (A p + κ i * Bq p) := by
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp => ?_).symm
      have : p ∉ S := fun h => hp (hSE h)
      simp [hA0 p this, hB0 p this]
    have h3 : ∫ p in E, θ i p.1 p.2 * (A p + κ i * Bq p) =
        ∫ p in E, Θ i p.1 p.2 * (A p + κ i * Bq p) := by
      refine integral_congr_ae ?_
      filter_upwards [hae] with p hp
      rw [hp]
    have h4 : ∫ p in E, Θ i p.1 p.2 * (A p + κ i * Bq p) =
        ∫ p, Θ i p.1 p.2 * (A p + κ i * Bq p) := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp => ?_
      have : p ∉ S := fun h => hp (hSE h)
      simp [hA0 p this, hB0 p this]
    have hint : ∀ H : ℝ × Vec 2 → ℝ, Continuous H → (∀ p, p ∉ S → H p = 0) →
        Integrable (fun p => Θ i p.1 p.2 * H p) := by
      intro H hH hH0
      have h1 : IntegrableOn (fun p => Θ i p.1 p.2 * H p) S :=
        (((hjc i).mono hSE).mul hH.continuousOn).integrableOn_compact hSc
      rw [← integrableOn_iff_integrable_of_support_subset (s := S)]
      · exact h1
      · intro p hp
        by_contra hn; exact hp (by simp [hH0 p hn])
    have hsplit : ∫ p, Θ i p.1 p.2 * (A p + κ i * Bq p) =
        (∫ p, Θ i p.1 p.2 * A p) + κ i * ∫ p, Θ i p.1 p.2 * Bq p := by
      have e : (fun p : ℝ × Vec 2 => Θ i p.1 p.2 * (A p + κ i * Bq p)) =
          fun p => Θ i p.1 p.2 * A p + κ i * (Θ i p.1 p.2 * Bq p) := by
        funext p; ring
      rw [e, integral_add (hint A hAc hA0) ((hint Bq hBc hB0).const_mul _),
        integral_const_mul]
    rw [← hsplit, ← h4, ← h3, ← h2, ← h1]
    exact hw
  have hlimA := tendsto_integral_of_uniform hSc hSE (Θi := fun i p => Θ (σ i) p.1 p.2)
    (fun i => hjc (σ i)) hL (hu S hSE hSc) hAc hA0
  have hlimB := tendsto_integral_of_uniform hSc hSE (Θi := fun i p => Θ (σ i) p.1 p.2)
    (fun i => hjc (σ i)) hL (hu S hSE hSc) hBc hB0
  have hκσ : Tendsto (fun i => κ (σ i)) atTop (𝓝 0) := hκ.comp hσ.tendsto_atTop
  have hlim := hlimA.add (hκσ.mul hlimB)
  have h0 : Tendsto (fun i => (∫ p, Θ (σ i) p.1 p.2 * A p) +
      κ (σ i) * ∫ p, Θ (σ i) p.1 p.2 * Bq p) atTop (𝓝 0) :=
    tendsto_const_nhds.congr fun i => (hid (σ i)).symm
  have := tendsto_nhds_unique hlim h0
  rw [zero_mul, add_zero] at this
  exact this
end

/-! # From a local energy solution (`IsLocalEnergySolution`) to a `LocSolution` -/

section
open AVRegularity.Applications

variable {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T R s : ℝ}
  {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {Cf : ℝ → ℝ → ℝ} {θ Θ : ℝ → Vec 2 → ℝ}

theorem pipe_volume_pos (ch : IsPipeChart b0 X t₁ T) (hT : 0 < T) (hR : 0 < R) :
    0 < (volume (outerPipe (fun t y => X t y t₁) t₁ T R)).toReal := by
  have h := (pipeMap_mp ch hT).measure_preimage_emb (pipeMap_measurableEmbedding ch hT)
    (outerPipe (fun t y => X t y t₁) t₁ T R)
  rw [pipeMap_preimage_outerPipe ch] at h
  have hfin := pipe_volume_lt_top (R := R) ch hT
  refine ENNReal.toReal_pos ?_ hfin.ne
  rw [← h, Measure.volume_eq_prod, Measure.prod_prod]
  refine mul_ne_zero ?_ ?_
  · rw [Real.volume_Ioo]; exact (ENNReal.ofReal_pos.2 (by linarith)).ne'
  · refine ((pipe_isOpen_euclidBall 0 R).measure_pos volume ⟨0, ?_⟩).ne'
    simp [euclidBall, vecNormSq, vecDot]; positivity

theorem locSolution_of_energy (ch : IsPipeChart b0 X t₁ T) (hT : 0 < T) (hR : 0 < R)
    (hθ : IsLocalEnergySolution b κ (fun t y => X t y t₁) t₁ T R θ) {F : ℝ}
    (hF : Real.sqrt ((volume (outerPipe (fun t y => X t y t₁) t₁ T R)).toReal⁻¹ *
      ∫ p in outerPipe (fun t y => X t y t₁) t₁ T R, θ p.1 p.2 ^ 2) ≤ F)
    (hsl : ∀ ϱ ϑ : ℝ, 0 < ϱ → ϱ < 1 / 8 → 0 < ϑ → ϑ < 4 → ∀ t ∈ Icc (t₁ - ϑ * T) t₁,
      SliceOK X t₁ s (ϱ * R) (Cf ϱ ϑ * F) θ Θ t) :
    LocSolution X t₁ T R s b κ Cf F
      (F ^ 2 * (volume (outerPipe (fun t y => X t y t₁) t₁ T R)).toReal) θ Θ := by
  obtain ⟨hL2, heq, DU, ⟨C, hCae⟩, -, -⟩ := hθ
  refine ⟨heq, hL2, ?_, ?_, hsl⟩
  · have hV := pipe_volume_pos (R := R) ch hT hR
    have h1 := (Real.sqrt_le_iff.1 hF).2
    have h2 : (volume (outerPipe (fun t y => X t y t₁) t₁ T R)).toReal⁻¹ *
        ∫ p in outerPipe (fun t y => X t y t₁) t₁ T R, θ p.1 p.2 ^ 2 ≤ F ^ 2 := h1
    rw [inv_mul_le_iff₀ hV] at h2
    linarith
  · have := (ae_restrict_iff' (measurableSet_Ioo (a := t₁ - 8 * T) (b := t₁))).1 hCae
    filter_upwards [this] with r hr hrI using (hr hrI).1
end

/-! # The compactness core of the local vanishing-diffusivity limits

Given local energy solutions `θ_i` with diffusivities `κ_i ≥ 0`, `κ_i → 0`, bounded normalized
`L²` averages, and slice representatives (the conclusion of the local theorem) with bounds
`Cf ϱ ϑ * F`, glue the representatives, extract a locally uniformly convergent subsequence and
pass to the limit in the equation and the bounds. -/

section
open AVRegularity.Applications

variable {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T R s : ℝ}
  {b : ℝ → Vec 2 → Vec 2}

theorem limits_core (ch : IsPipeChart b0 X t₁ T) (hT : 0 < T) (hR : 0 < R) (hs : 0 < s)
    {Bb : ℝ} (hB : ∀ t x, ‖b t x‖ ≤ Bb) (hbc : Continuous fun p : ℝ × Vec 2 => b p.1 p.2)
    (Cf : ℝ → ℝ → ℝ) (F : ℝ) (κ : ℕ → ℝ) (θ : ℕ → ℝ → Vec 2 → ℝ)
    (hκ0 : ∀ i, 0 ≤ κ i) (hκ : Tendsto κ atTop (𝓝 0))
    (hsol : ∀ i, IsLocalEnergySolution b (κ i) (fun t y => X t y t₁) t₁ T R (θ i))
    (hF : ∀ i, Real.sqrt ((volume (outerPipe (fun t y => X t y t₁) t₁ T R)).toReal⁻¹ *
      ∫ p in outerPipe (fun t y => X t y t₁) t₁ T R, θ i p.1 p.2 ^ 2) ≤ F)
    (hsl : ∀ i, ∀ ϱ ϑ : ℝ, 0 < ϱ → ϱ < 1 / 8 → 0 < ϑ → ϑ < 4 → ∃ Θ : ℝ → Vec 2 → ℝ,
      ∀ t ∈ Icc (t₁ - ϑ * T) t₁, SliceOK X t₁ s (ϱ * R) (Cf ϱ ϑ * F) (θ i) Θ t) :
    ∃ (σ : ℕ → ℕ) (Θ : ℕ → ℝ → Vec 2 → ℝ) (θstar : ℝ → Vec 2 → ℝ),
      StrictMono σ ∧
      (∀ i, ContinuousOn (fun p : ℝ × Vec 2 => Θ i p.1 p.2) (eReg X t₁ T R) ∧
        (fun p : ℝ × Vec 2 => Θ i p.1 p.2) =ᵐ[volume.restrict (eReg X t₁ T R)]
          (fun p : ℝ × Vec 2 => θ i p.1 p.2)) ∧
      (∀ K ⊆ eReg X t₁ T R, IsCompact K →
        TendstoUniformlyOn (fun i (p : ℝ × Vec 2) => Θ (σ i) p.1 p.2)
          (fun p : ℝ × Vec 2 => θstar p.1 p.2) atTop K) ∧
      ContinuousOn (fun p : ℝ × Vec 2 => θstar p.1 p.2) (eReg X t₁ T R) ∧
      (∀ φ : ℝ × Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ interior (eReg X t₁ T R) →
        ∫ p, θstar p.1 p.2 * (fderiv ℝ φ p (1, 0) +
          ∑ j : Fin 2, b p.1 p.2 j * fderiv ℝ φ p (0, basisVec j)) = 0) ∧
      ∀ ϱ ϑ : ℝ, 0 < ϱ → ϱ < 1 / 8 → 0 < ϑ → ϑ < 4 →
        ∀ t ∈ Set.Icc (t₁ - ϑ * T) t₁,
        ∀ x ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R),
        ∀ y ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R),
        ∀ z ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R), y ≠ z →
          |θstar t x| + |θstar t y - θstar t z| / Real.sqrt (vecNormSq (y - z)) ^ s ≤
            Cf ϱ ϑ * F := by
  -- glue the representatives
  have hmem : ∀ i, ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ioo (t₁ - 8 * T) t₁ →
      MemLp (fun y => θ i r (X r y t₁)) 2 (volume.restrict (euclidBall 0 R)) := by
    intro i
    obtain ⟨-, -, DU, ⟨C, hCae⟩, -, -⟩ := hsol i
    have := (ae_restrict_iff' (measurableSet_Ioo (a := t₁ - 8 * T) (b := t₁))).1 hCae
    filter_upwards [this] with r hr hrI using (hr hrI).1
  have hglue : ∀ i, ∃ Θ : ℝ → Vec 2 → ℝ, ∀ ϱ ϑ : ℝ, 0 < ϱ → ϱ < 1 / 8 → 0 < ϑ → ϑ < 4 →
      ∀ t ∈ Icc (t₁ - ϑ * T) t₁, SliceOK X t₁ s (ϱ * R) (Cf ϱ ϑ * F) (θ i) Θ t :=
    fun i => glue_slices ch hT hR (fun ϱ ϑ => Cf ϱ ϑ * F) (hmem i) (hsl i)
  choose Θ hΘ using hglue
  have hLS : ∀ i, LocSolution X t₁ T R s b (κ i) Cf F
      (F ^ 2 * (volume (outerPipe (fun t y => X t y t₁) t₁ T R)).toReal) (θ i) (Θ i) :=
    fun i => locSolution_of_energy ch hT hR (hsol i) (hF i) (hΘ i)
  have hjc : ∀ i, ContinuousOn (fun p : ℝ × Vec 2 => Θ i p.1 p.2) (eReg X t₁ T R) := fun i =>
    jointContinuousOn ch hT hR hs hB hbc (hLS i) (hκ0 i)
  obtain ⟨κbar, hκbar0, hκbar⟩ : ∃ κbar : ℝ, 0 ≤ κbar ∧ ∀ i, κ i ≤ κbar := by
    obtain ⟨M, hM⟩ := hκ.bddAbove_range
    exact ⟨max M 0, le_max_right _ _, fun i => (hM ⟨i, rfl⟩).trans (le_max_left _ _)⟩
  have hQ : 0 ≤ F ^ 2 * (volume (outerPipe (fun t y => X t y t₁) t₁ T R)).toReal :=
    mul_nonneg (sq_nonneg _) ENNReal.toReal_nonneg
  have := weaklyLocallyCompact_eReg (R := R) ch hT
  have := sigmaCompact_eReg (R := R) ch hT
  obtain ⟨σ, hσ, L, hLc, hLu⟩ := exists_uniform_subseq (E := eReg X t₁ T R)
    (g := fun i p => Θ i p.1 p.2) hjc
    (fun K hKE hK => by
      obtain ⟨M, hM, -⟩ := modulus_unif ch hT hR hs hB hbc (Cf := Cf) (F := F)
        (κbar := κbar) hQ hK hKE
      exact ⟨M, fun n p hp => hM (κ n) (θ n) (Θ n) (hLS n) p hp⟩)
    (fun K hKE hK ε hε => by
      obtain ⟨M, -, hM⟩ := modulus_unif ch hT hR hs hB hbc (Cf := Cf) (F := F)
        (κbar := κbar) hQ hK hKE
      obtain ⟨δ, hδ, hδ'⟩ := hM ε hε
      exact ⟨δ, hδ, fun n p hp q hq hd =>
        hδ' (κ n) (θ n) (Θ n) (hκ0 n) (hκbar n) (hLS n) p hp q hq hd⟩)
  refine ⟨σ, Θ, fun t x => L (t, x), hσ, fun i => ⟨hjc i, ae_eq_eReg ch hT hR (hLS i) (hjc i)⟩,
    hLu, hLc, fun φ hφ hφc hts => ?_, ?_⟩
  · exact limit_equation ch hT hR hs hB hbc hLS hκ0 hκ hσ hLc hLu hφ hφc hts
  · intro ϱ ϑ hϱ0 hϱ8 hϑ0 hϑ4 t ht x hx y hy z hz hyz
    have hmemE : ∀ w ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R),
        (t, w) ∈ eReg X t₁ T R := by
      rintro w ⟨y', hy', rfl⟩
      refine ⟨by nlinarith [ht.1], ht.2, y', ?_, rfl⟩
      exact euclidBall_subset_of_le (mul_pos hϱ0 hR).le (by nlinarith) hy'
    have hpt : ∀ w ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R),
        Tendsto (fun i => Θ (σ i) t w) atTop (𝓝 (L (t, w))) := fun w hw =>
      (hLu {(t, w)} (by simpa using hmemE w hw) isCompact_singleton).tendsto_at rfl
    have hlim := ((hpt x hx).abs).add (((hpt y hy).sub (hpt z hz)).abs.div_const
      (Real.sqrt (vecNormSq (y - z)) ^ s))
    refine le_of_tendsto' hlim fun i => ?_
    exact (hΘ (σ i) ϱ ϑ hϱ0 hϱ8 hϑ0 hϑ4 t ht).2.2 x hx y hy z hz hyz
end

end AVRegularity.Applications.LimitsLocal
end
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Filter Topology Homogenization AVenhance AVRegularity
namespace AVRegularity.Applications

/-! # Vanishing-diffusivity limits, local part, conditional on the local theorem

`vanishing_diffusivity_limits_local_of_local` has exactly the conclusion of
`AVRegularity.vanishing_diffusivity_limits_local` (from which Corollary D(b) of the paper
follows), and the local theorem enters only as the explicit hypothesis `OcLocalStatement`. -/

open LimitsLocal

theorem vanishing_diffusivity_limits_local_of_local (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (hloc : OcLocalStatement α s q ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
        ∃ b : ℝ → Vec 2 → Vec 2,
          (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) ∧
          ∀ cT CT : ℝ, 0 < cT → 0 < CT → ∃ C₁ : ℝ, 0 < C₁ ∧
            ∀ (n : ℕ) (T R : ℝ), 2 ≤ n → 0 < T → 0 < R →
              cT * ocTauPP α q Λ (n - 1) ≤ T → T ≤ CT * ocTauPP α q Λ (n - 1) →
              8 * T * ocA α q Λ (n - 2) ≤ ocCStar →
              C₁ * max (ocEpsilon q Λ (n - 1) ^ α * T)
                  (Real.sqrt (sSup (ocBandSet α q Λ) * T)) ≤ R →
              R ≤ 1 / 8 →
              ∃ C : ℝ → ℝ → ℝ, ∀ t₁ : ℝ, ∀ X : ℝ → Vec 2 → ℝ → Vec 2,
                IsFlow (streamVel (Φ (n - 2))) X →
                ∀ (F : ℝ) (κ : ℕ → ℝ) (θ : ℕ → ℝ → Vec 2 → ℝ),
                  (∀ i, κ i ∈ ocBandSet α q Λ) → Tendsto κ atTop (𝓝 0) →
                  (∀ i, IsLocalEnergySolution b (κ i) (fun t y => X t y t₁) t₁ T R (θ i)) →
                  (∀ i, Real.sqrt ((volume (outerPipe (fun t y => X t y t₁) t₁ T R)).toReal⁻¹ *
                      ∫ p in outerPipe (fun t y => X t y t₁) t₁ T R, θ i p.1 p.2 ^ 2) ≤ F) →
                  ∃ (σ : ℕ → ℕ) (Θ : ℕ → ℝ → Vec 2 → ℝ) (θstar : ℝ → Vec 2 → ℝ),
                    StrictMono σ ∧
                    (∀ i, ContinuousOn (fun p : ℝ × Vec 2 => Θ i p.1 p.2)
                        {p | t₁ - 4 * T < p.1 ∧ p.1 ≤ t₁ ∧
                          ∃ y ∈ euclidBall 0 (R / 8), p.2 = X p.1 y t₁} ∧
                      (fun p : ℝ × Vec 2 => Θ i p.1 p.2) =ᵐ[volume.restrict
                        {p | t₁ - 4 * T < p.1 ∧ p.1 ≤ t₁ ∧
                          ∃ y ∈ euclidBall 0 (R / 8), p.2 = X p.1 y t₁}]
                        (fun p : ℝ × Vec 2 => θ i p.1 p.2)) ∧
                    (∀ K ⊆ {p : ℝ × Vec 2 | t₁ - 4 * T < p.1 ∧ p.1 ≤ t₁ ∧
                          ∃ y ∈ euclidBall 0 (R / 8), p.2 = X p.1 y t₁}, IsCompact K →
                      TendstoUniformlyOn (fun i (p : ℝ × Vec 2) => Θ (σ i) p.1 p.2)
                        (fun p : ℝ × Vec 2 => θstar p.1 p.2) atTop K) ∧
                    ContinuousOn (fun p : ℝ × Vec 2 => θstar p.1 p.2)
                      {p | t₁ - 4 * T < p.1 ∧ p.1 ≤ t₁ ∧
                        ∃ y ∈ euclidBall 0 (R / 8), p.2 = X p.1 y t₁} ∧
                    (∀ φ : ℝ × Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
                      tsupport φ ⊆ interior {p : ℝ × Vec 2 | t₁ - 4 * T < p.1 ∧ p.1 ≤ t₁ ∧
                          ∃ y ∈ euclidBall 0 (R / 8), p.2 = X p.1 y t₁} →
                      ∫ p, θstar p.1 p.2 *
                        (fderiv ℝ φ p (1, 0) +
                          ∑ j : Fin 2, b p.1 p.2 j * fderiv ℝ φ p (0, basisVec j)) = 0) ∧
                    ∀ ϱ ϑ : ℝ, 0 < ϱ → ϱ < 1 / 8 → 0 < ϑ → ϑ < 4 →
                    ∀ t ∈ Set.Icc (t₁ - ϑ * T) t₁,
                    ∀ x ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R),
                    ∀ y ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R),
                    ∀ z ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R), y ≠ z →
                      |θstar t x| + |θstar t y - θstar t z| /
                        Real.sqrt (vecNormSq (y - z)) ^ s ≤ C ϱ ϑ * F := by
  classical
  obtain ⟨Λ₀, hΛ₀, H⟩ := hloc
  refine ⟨Λ₀, hΛ₀, fun Λ hΛ Φ hΦ => ?_⟩
  have hΛ128 : 128 ≤ Λ := hΛ₀.trans hΛ
  obtain ⟨b, hb, Hb⟩ := H Λ hΛ Φ hΦ
  refine ⟨b, hb, fun cT CT hcT hCT => ?_⟩
  obtain ⟨C₁, hC₁, HC⟩ := Hb cT CT hcT hCT
  refine ⟨C₁, hC₁, fun n T R h2n hT hR h1 h2 h3 h4 h5 => ?_⟩
  -- properties of the limit velocity
  obtain ⟨b', hb', hholder'⟩ :=
    Velocity.exists_limit_velocity α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ128 Φ hΦ
  have hbb : b = b' := funext fun t => funext fun x => tendsto_nhds_unique (hb t x) (hb' t x)
  have hholder : IsHolderDivFreeVelocity α b := hbb ▸ hholder'
  have hdrift := isContDrift_of_holder hα₀ hholder
  obtain ⟨Bb, -, hBb⟩ := hdrift.bounded
  -- the constants
  set Cf : ℝ → ℝ → ℝ := fun ϱ ϑ => max 0 (if h : 0 < ϱ ∧ ϱ < 1 / 8 ∧ 0 < ϑ ∧ ϑ < 4 then
      Classical.choose (HC n T R ϱ ϑ h2n hT hR h.1 h.2.1 h.2.2.1 h.2.2.2 h1 h2 h3 h4 h5)
    else 0) with hCf
  refine ⟨Cf, fun t₁ X hX F κ θ hκb hκ hsol hF => ?_⟩
  have hq1 : 1 < q := hq.1
  have hκ0 : ∀ i, 0 ≤ κ i := fun i => (band_pos_le_two hα₀ hq1 hΛ128 (hκb i)).1.le
  have ch := isPipeChart_of_construction α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ128 Φ hΦ (n - 2) X hX
    t₁ T hT h3
  have hsl : ∀ i, ∀ ϱ ϑ : ℝ, 0 < ϱ → ϱ < 1 / 8 → 0 < ϑ → ϑ < 4 → ∃ Θ : ℝ → Vec 2 → ℝ,
      ∀ t ∈ Set.Icc (t₁ - ϑ * T) t₁, SliceOK X t₁ s (ϱ * R) (Cf ϱ ϑ * F) (θ i) Θ t := by
    intro i ϱ ϑ hϱ0 hϱ8 hϑ0 hϑ4
    have hr : 0 < ϱ ∧ ϱ < 1 / 8 ∧ 0 < ϑ ∧ ϑ < 4 := ⟨hϱ0, hϱ8, hϑ0, hϑ4⟩
    have hspec := Classical.choose_spec
      (HC n T R ϱ ϑ h2n hT hR hr.1 hr.2.1 hr.2.2.1 hr.2.2.2 h1 h2 h3 h4 h5)
    obtain ⟨Θ, hΘ⟩ := hspec t₁ X hX (κ i) (hκb i) (θ i) (hsol i)
    refine ⟨Θ, fun t ht => ?_⟩
    obtain ⟨c1, c2, c3⟩ := hΘ t ht
    refine ⟨c1, c2, fun x hx y hy z hz hyz => ?_⟩
    refine (c3 x hx y hy z hz hyz).trans ?_
    have hCfe : Cf ϱ ϑ = max 0 (Classical.choose
        (HC n T R ϱ ϑ h2n hT hR hr.1 hr.2.1 hr.2.2.1 hr.2.2.2 h1 h2 h3 h4 h5)) := by
      simp only [hCf, hr, and_self, ↓reduceDIte]
    rw [hCfe]
    have hA0 : 0 ≤ Real.sqrt ((volume (outerPipe (fun t y => X t y t₁) t₁ T R)).toReal⁻¹ *
        ∫ p in outerPipe (fun t y => X t y t₁) t₁ T R, θ i p.1 p.2 ^ 2) := Real.sqrt_nonneg _
    calc _ ≤ max 0 (Classical.choose
          (HC n T R ϱ ϑ h2n hT hR hr.1 hr.2.1 hr.2.2.1 hr.2.2.2 h1 h2 h3 h4 h5)) *
          Real.sqrt ((volume (outerPipe (fun t y => X t y t₁) t₁ T R)).toReal⁻¹ *
            ∫ p in outerPipe (fun t y => X t y t₁) t₁ T R, θ i p.1 p.2 ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hA0
      _ ≤ _ := mul_le_mul_of_nonneg_left (hF i) (le_max_left _ _)
  have hbc : Continuous fun p : ℝ × Vec 2 => b p.1 p.2 := hdrift.continuous
  obtain ⟨σ, Θ, θstar, hσ, hΘc, hu, hLc, heq, hbd⟩ :=
    limits_core ch hT hR hs₀ hBb hbc Cf F κ θ hκ0 hκ hsol hF hsl
  exact ⟨σ, Θ, θstar, hσ, hΘc, hu, hLc, heq, hbd⟩

end AVRegularity.Applications
end
end
end
