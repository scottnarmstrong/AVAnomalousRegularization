-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Applications.Local.LabelTrace
import AVRegularity.Applications.Pipe.LocalEnergy
import AVRegularity.Applications.Local.Instance
public import AVRegularity.Applications.Limits.Equi
import AVRegularity.Applications.LocalEnergy.Mollifier
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.UniformSpace.Uniformizable

section
@[expose] public section
noncomputable section
open MeasureTheory Filter Topology Homogenization AVenhance Set
namespace AVRegularity.Applications.LimitsLocal

/-! # The slice representatives of the local theorem

`SliceOK X t₁ s ρ M θ Θ t` records the conclusion of the local theorem at one time `t`, for the
label radius `ρ` and the bound `M`: `Θ t` is continuous on `K_t = F_t(B_ρ)`, is the left `L²`
trace of the pulled-back slices of `θ`, and its `C^s` norm on `K_t` is at most `M`. -/

section
open AVRegularity.Applications

/-- The conclusion of the local theorem at time `t` (label radius `ρ`, bound `M`). -/
def SliceOK (X : ℝ → Vec 2 → ℝ → Vec 2) (t₁ s ρ M : ℝ) (θ : ℝ → Vec 2 → ℝ)
    (Θ : ℝ → Vec 2 → ℝ) (t : ℝ) : Prop :=
  ContinuousOn (Θ t) ((fun y => X t y t₁) '' euclidBall 0 ρ) ∧
  Tendsto (fun r => ∫ y in euclidBall 0 ρ, (θ r (X r y t₁) - Θ t (X t y t₁)) ^ 2)
    (𝓝[<] t ⊓ ae volume) (𝓝 0) ∧
  ∀ x ∈ (fun y => X t y t₁) '' euclidBall 0 ρ,
  ∀ y ∈ (fun y => X t y t₁) '' euclidBall 0 ρ,
  ∀ z ∈ (fun y => X t y t₁) '' euclidBall 0 ρ, y ≠ z →
    |Θ t x| + |Θ t y - Θ t z| / Real.sqrt (vecNormSq (y - z)) ^ s ≤ M

variable {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T : ℝ}

theorem exists_distinct_sec (ch : IsPipeChart b0 X t₁ T) {t ρ : ℝ}
    (ht : t ∈ Icc (t₁ - 8 * T) t₁) (hρ : 0 < ρ) :
    ∃ y z, y ∈ (fun y => X t y t₁) '' euclidBall 0 ρ ∧
      z ∈ (fun y => X t y t₁) '' euclidBall 0 ρ ∧ y ≠ z := by
  set e : Vec 2 := (ρ / 2) • basisVec 0 with he
  have h0 : (0 : Vec 2) ∈ euclidBall 0 ρ := by
    simp [euclidBall, vecNormSq, vecDot]; positivity
  have h1 : e ∈ euclidBall 0 ρ := by
    simp only [euclidBall, mem_ofPred_eq, he, vecNormSq, vecDot, Fin.sum_univ_two]
    simp [basisVec]
    nlinarith
  refine ⟨_, _, ⟨0, h0, rfl⟩, ⟨e, h1, rfl⟩, fun h => ?_⟩
  have := congrArg (fun w => X t₁ w t) h
  simp only [ch.left t ht] at this
  have h2 := congrFun this 0
  simp [he, basisVec] at h2
  linarith

theorem SliceOK.abs_le (ch : IsPipeChart b0 X t₁ T) {s ρ M t : ℝ} {θ Θ}
    (h : SliceOK X t₁ s ρ M θ Θ t) (ht : t ∈ Icc (t₁ - 8 * T) t₁) (hρ : 0 < ρ)
    {x : Vec 2} (hx : x ∈ (fun y => X t y t₁) '' euclidBall 0 ρ) : |Θ t x| ≤ M := by
  obtain ⟨y, z, hy, hz, hyz⟩ := exists_distinct_sec ch ht hρ
  have := h.2.2 x hx y hy z hz hyz
  have h0 : 0 ≤ |Θ t y - Θ t z| / Real.sqrt (vecNormSq (y - z)) ^ s :=
    div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  linarith

theorem SliceOK.holder (ch : IsPipeChart b0 X t₁ T) {s ρ M t : ℝ} {θ Θ}
    (h : SliceOK X t₁ s ρ M θ Θ t) (ht : t ∈ Icc (t₁ - 8 * T) t₁) (hρ : 0 < ρ)
    {y z : Vec 2} (hy : y ∈ (fun y => X t y t₁) '' euclidBall 0 ρ)
    (hz : z ∈ (fun y => X t y t₁) '' euclidBall 0 ρ) :
    |Θ t y - Θ t z| ≤ M * eNorm (y - z) ^ s := by
  by_cases hyz : y = z
  · subst hyz
    simp only [sub_self, abs_zero]
    have := h.abs_le ch ht hρ hy
    have hM : 0 ≤ M := (abs_nonneg _).trans this
    have h3 : (0 : ℝ) ≤ eNorm 0 ^ s := Real.rpow_nonneg (eNorm_nonneg _) _
    exact mul_nonneg hM h3
  · have h1 := h.2.2 y hy y hy z hz hyz
    have hpos : 0 < eNorm (y - z) :=
      lt_of_lt_of_le (norm_pos_iff.2 (sub_ne_zero.2 hyz)) (norm_le_eNorm' _)
    have hp : 0 < eNorm (y - z) ^ s := Real.rpow_pos_of_pos hpos _
    have h2 : |Θ t y - Θ t z| / eNorm (y - z) ^ s ≤ M := by
      have := abs_nonneg (Θ t y)
      unfold eNorm; linarith
    rw [div_le_iff₀ hp] at h2
    exact h2
end

/-! # The region `E` and its compact subsets

`eReg X t₁ T R = {(t, F_t y) : t₁ - 4T < t ≤ t₁, |y| < R/8}`. In label coordinates
`H(t, x) = X t₁ x t` it is `{t₁ - 4T < t ≤ t₁, |H(t,x)| < R/8}`. Compact subsets of `E` lie in
`{t ≥ t₁ - ϑT, |H| < ϱR}` with `ϑ < 4`, `ϱ < 1/8`, and have a uniform margin there. -/

section
open AVRegularity.Applications

/-- The region `S` of the corollary. -/
def eReg (X : ℝ → Vec 2 → ℝ → Vec 2) (t₁ T R : ℝ) : Set (ℝ × Vec 2) :=
  {p | t₁ - 4 * T < p.1 ∧ p.1 ≤ t₁ ∧ ∃ y ∈ euclidBall 0 (R / 8), p.2 = X p.1 y t₁}

variable {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T R : ℝ}

theorem mem_sec_iff (ch : IsPipeChart b0 X t₁ T) {t ρ : ℝ} (ht : t ∈ Icc (t₁ - 8 * T) t₁)
    (x : Vec 2) : x ∈ (fun y => X t y t₁) '' euclidBall 0 ρ ↔ X t₁ x t ∈ euclidBall 0 ρ := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [ch.left t ht y]; exact hy
  · intro h
    exact ⟨_, h, ch.right t ht x⟩

theorem mem_eReg_iff (ch : IsPipeChart b0 X t₁ T) (hT : 0 < T) (p : ℝ × Vec 2) :
    p ∈ eReg X t₁ T R ↔ t₁ - 4 * T < p.1 ∧ p.1 ≤ t₁ ∧ X t₁ p.2 p.1 ∈ euclidBall 0 (R / 8) := by
  constructor
  · rintro ⟨h1, h2, y, hy, hp⟩
    have ht : p.1 ∈ Icc (t₁ - 8 * T) t₁ := ⟨by linarith, h2⟩
    exact ⟨h1, h2, (mem_sec_iff ch ht p.2).1 ⟨y, hy, hp.symm⟩⟩
  · rintro ⟨h1, h2, h3⟩
    have ht : p.1 ∈ Icc (t₁ - 8 * T) t₁ := ⟨by linarith, h2⟩
    obtain ⟨y, hy, hyp⟩ := (mem_sec_iff ch ht p.2).2 h3
    exact ⟨h1, h2, y, hy, hyp.symm⟩

theorem continuous_lab (ch : IsPipeChart b0 X t₁ T) :
    Continuous fun p : ℝ × Vec 2 => X t₁ p.2 p.1 := ch.smoothH.continuous

theorem isOpen_ball_euclid (ρ : ℝ) : IsOpen (euclidBall (0 : Vec 2) ρ) :=
  pipe_isOpen_euclidBall 0 ρ

/-- A uniform margin around a compact set inside the open slab `{lo < t, |H| < ρ}`. -/
theorem exists_margin (ch : IsPipeChart b0 X t₁ T) {K : Set (ℝ × Vec 2)} (hK : IsCompact K)
    {lo ρ : ℝ} (hKs : ∀ p ∈ K, lo < p.1 ∧ X t₁ p.2 p.1 ∈ euclidBall 0 ρ) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ p ∈ K, ∀ q : ℝ × Vec 2, dist q p < μ →
      lo < q.1 ∧ X t₁ q.2 q.1 ∈ euclidBall 0 ρ := by
  have hopen : IsOpen {q : ℝ × Vec 2 | lo < q.1 ∧ X t₁ q.2 q.1 ∈ euclidBall 0 ρ} :=
    (isOpen_lt continuous_const continuous_fst).inter
      ((isOpen_ball_euclid ρ).preimage (continuous_lab ch))
  obtain ⟨μ, hμ, hth⟩ := hK.exists_thickening_subset_open hopen hKs
  refine ⟨μ, hμ, fun p hp q hq => hth ?_⟩
  exact Metric.mem_thickening_iff.2 ⟨p, hp, hq⟩

/-- A compact subset of `E` lies in a slab with `ϑ < 4`, `ϱ < 1/8`. -/
theorem exists_slab (ch : IsPipeChart b0 X t₁ T) (hT : 0 < T) (hR : 0 < R)
    {K : Set (ℝ × Vec 2)} (hK : IsCompact K) (hKE : K ⊆ eReg X t₁ T R) :
    ∃ ϱ ϑ : ℝ, 0 < ϱ ∧ ϱ < 1 / 8 ∧ 0 < ϑ ∧ ϑ < 4 ∧
      ∀ p ∈ K, t₁ - ϑ * T < p.1 ∧ p.1 ≤ t₁ ∧ X t₁ p.2 p.1 ∈ euclidBall 0 (ϱ * R) := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1 / 16, 2, by norm_num, by norm_num, by norm_num, by norm_num, by simp⟩
  have hKm := fun p hp => (mem_eReg_iff ch hT p).1 (hKE hp)
  obtain ⟨p0, hp0, hmin⟩ := hK.exists_isMinOn hne continuous_fst.continuousOn
  have hH : Continuous fun p : ℝ × Vec 2 => vecNormSq (X t₁ p.2 p.1 - 0) := by
    have hc := continuous_lab ch
    simp only [vecNormSq, vecDot]
    exact continuous_finsetSum _ fun i _ =>
      (((continuous_apply i).comp (hc.sub continuous_const))).mul
        (((continuous_apply i).comp (hc.sub continuous_const)))
  obtain ⟨p1, hp1, hmax⟩ := hK.exists_isMaxOn hne hH.continuousOn
  have hlo : t₁ - 4 * T < p0.1 := (hKm p0 hp0).1
  have hp1m : vecNormSq (X t₁ p1.2 p1.1 - 0) < (R / 8) ^ 2 := (hKm p1 hp1).2.2
  set ϑ : ℝ := ((t₁ - p0.1) / T + 4) / 2 with hϑ
  have hq : 0 ≤ (t₁ - p0.1) / T := div_nonneg (by linarith [(hKm p0 hp0).2.1]) hT.le
  have hq4 : (t₁ - p0.1) / T < 4 := by
    rw [div_lt_iff₀ hT]; linarith
  set m : ℝ := Real.sqrt (vecNormSq (X t₁ p1.2 p1.1 - 0)) with hm
  have hm0 : 0 ≤ m := Real.sqrt_nonneg _
  have hmR : m < R / 8 := by
    rw [hm]
    exact (Real.sqrt_lt' (by positivity)).2 hp1m
  set ϱ : ℝ := (m / R + 1 / 8) / 2 with hϱ
  have hmR' : m / R < 1 / 8 := by
    rw [div_lt_iff₀ hR]; linarith
  refine ⟨ϱ, ϑ, by positivity, by linarith, by linarith, by linarith, fun p hp => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hKm p hp
  refine ⟨?_, h2, ?_⟩
  · have hp0le : p0.1 ≤ p.1 := hmin hp
    have : (t₁ - p0.1) / T < ϑ := by linarith
    rw [div_lt_iff₀ hT] at this
    linarith
  · have hle : vecNormSq (X t₁ p.2 p.1 - 0) ≤ vecNormSq (X t₁ p1.2 p1.1 - 0) := hmax hp
    simp only [euclidBall, mem_ofPred_eq]
    have hmm : m ^ 2 = vecNormSq (X t₁ p1.2 p1.1 - 0) := by
      rw [hm]; exact Real.sq_sqrt (vecNormSq_nonneg _)
    have hmlt : m < ϱ * R := by
      have : m / R < ϱ := by linarith
      rwa [div_lt_iff₀ hR] at this
    calc vecNormSq (X t₁ p.2 p.1 - 0) ≤ m ^ 2 := by rw [hmm]; exact hle
      _ < (ϱ * R) ^ 2 := by gcongr
end

end AVRegularity.Applications.LimitsLocal
end
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Filter Topology Set
namespace AVRegularity.Applications.LimitsLocal

/-! # A function with zero left limits along `𝓝[<] t ⊓ ae` vanishes almost everywhere

If `φ ≥ 0` tends to `0` along `𝓝[<] t ⊓ ae` for every `t` of an interval `J`, then `φ = 0` a.e. on
`J`. The set of points not covered by the left-intervals is countable (it is a set of left-isolated
points), and the covered part is a countable union by Lindelöf. -/

section
open AVRegularity.Applications

theorem ae_lt_of_left_limits {φ : ℝ → ℝ} {J : Set ℝ} {ε : ℝ} (hε : 0 < ε)
    (hlim : ∀ t ∈ J, Tendsto φ (𝓝[<] t ⊓ ae (volume : Measure ℝ)) (𝓝 0)) :
    ∀ᵐ r ∂(volume : Measure ℝ), r ∈ J → φ r < ε := by
  have h1 : ∀ t : J, ∃ δ : ℝ, 0 < δ ∧ ∀ᵐ r ∂(volume : Measure ℝ), r ∈ Ioo (t.1 - δ) t.1 → φ r < ε :=
    fun t => exists_Ioo_of_eventually ((hlim t.1 t.2).eventually (gt_mem_nhds hε))
  choose δ hδ hδae using h1
  set U : J → Set ℝ := fun t => Ioo (t.1 - δ t) t.1 with hU
  obtain ⟨S, hS, hSU⟩ := TopologicalSpace.isOpen_iUnion_countable U (fun t => isOpen_Ioo)
  have hae1 : ∀ᵐ r ∂(volume : Measure ℝ), ∀ t ∈ S, r ∈ U t → φ r < ε :=
    (ae_ball_iff hS).2 fun t _ => hδae t
  -- the uncovered part is countable
  have hcount : (J \ ⋃ t : J, U t).Countable := by
    have hq : ∀ c : ↥(J \ ⋃ t : J, U t), ∃ q : ℚ, c.1 - δ ⟨c.1, c.2.1⟩ < q ∧ (q : ℝ) < c.1 :=
      fun c => exists_rat_btwn (by linarith [hδ ⟨c.1, c.2.1⟩])
    choose q hq1 hq2 using hq
    have hinj : Function.Injective q := by
      intro c c' hcc
      by_contra hne
      have hne' : c.1 ≠ c'.1 := fun h => hne (Subtype.ext h)
      rcases lt_or_gt_of_ne hne' with hlt | hlt
      · -- c < c' and q c = q c'
        have : c.1 ∈ U ⟨c'.1, c'.2.1⟩ := by
          refine ⟨?_, hlt⟩
          have h1 := hq1 c'
          have h2 := hq2 c
          rw [← hcc] at h1
          linarith
        exact c.2.2 (mem_iUnion.2 ⟨_, this⟩)
      · have : c'.1 ∈ U ⟨c.1, c.2.1⟩ := by
          refine ⟨?_, hlt⟩
          have h1 := hq1 c
          have h2 := hq2 c'
          rw [hcc] at h1
          linarith
        exact c'.2.2 (mem_iUnion.2 ⟨_, this⟩)
    have : Countable ↥(J \ ⋃ t : J, U t) := hinj.countable
    exact Set.countable_coe_iff.1 this
  have hnull : volume (J \ ⋃ t : J, U t) = 0 := hcount.measure_zero _
  have hae2 : ∀ᵐ r ∂(volume : Measure ℝ), r ∉ J \ ⋃ t : J, U t := compl_mem_ae_iff.2 hnull
  filter_upwards [hae1, hae2] with r h1 h2 hrJ
  have : r ∈ ⋃ t : J, U t := by
    by_contra hc; exact h2 ⟨hrJ, hc⟩
  rw [← hSU] at this
  obtain ⟨t, htS, hrt⟩ := mem_iUnion₂.1 this
  exact h1 t htS hrt

theorem ae_eq_zero_of_left_limits {φ : ℝ → ℝ} {J : Set ℝ} (h0 : ∀ r, 0 ≤ φ r)
    (hlim : ∀ t ∈ J, Tendsto φ (𝓝[<] t ⊓ ae (volume : Measure ℝ)) (𝓝 0)) :
    ∀ᵐ r ∂(volume : Measure ℝ), r ∈ J → φ r = 0 := by
  have h : ∀ᵐ r ∂(volume : Measure ℝ), ∀ n : ℕ, r ∈ J → φ r < 1 / ((n : ℝ) + 1) :=
    ae_all_iff.2 fun n => ae_lt_of_left_limits (by positivity) hlim
  filter_upwards [h] with r hr hrJ
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (h0 r)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  linarith [hr n hrJ]
end

/-! # Smooth time cutoffs approximating the indicator of `[σ, τ)`

`stepAt a ε` rises smoothly from `0` (at `a - 2ε`) to `1` (at `a - ε`); `bumpAt a ε` is its
derivative, a nonnegative bump of mass one supported in `[a - 2ε, a - ε]`. The cutoff
`cutoff σ τ ε = stepAt σ ε * (1 - stepAt τ ε)` has derivative `bumpAt σ ε - bumpAt τ ε` when
`ε < τ - σ`. Averaging against `bumpAt a ε` recovers the left limit along `𝓝[<] a ⊓ ae`. -/

/-- Smooth step from `0` at `a - 2ε` to `1` at `a - ε`. -/
def stepAt (a ε : ℝ) (t : ℝ) : ℝ := Real.smoothTransition ((t - a) / ε + 2)

theorem contDiff_stepAt (a ε : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (stepAt a ε) :=
  Real.smoothTransition.contDiff.comp (((contDiff_id.sub contDiff_const).div_const ε).add
    contDiff_const)

theorem stepAt_nonneg (a ε t : ℝ) : 0 ≤ stepAt a ε t := Real.smoothTransition.nonneg _

theorem stepAt_le_one (a ε t : ℝ) : stepAt a ε t ≤ 1 := Real.smoothTransition.le_one _

theorem stepAt_eq_zero {a ε t : ℝ} (hε : 0 < ε) (ht : t ≤ a - 2 * ε) : stepAt a ε t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have : (t - a) / ε ≤ -2 := by
    rw [div_le_iff₀ hε]; linarith
  linarith

theorem stepAt_eq_one {a ε t : ℝ} (hε : 0 < ε) (ht : a - ε ≤ t) : stepAt a ε t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have : -1 ≤ (t - a) / ε := by
    rw [le_div_iff₀ hε]; linarith
  linarith

theorem monotone_stepAt {a ε : ℝ} (hε : 0 < ε) : Monotone (stepAt a ε) := by
  intro x y hxy
  apply Real.smoothTransition.monotone
  have : (x - a) / ε ≤ (y - a) / ε := by gcongr
  linarith

/-- The bump `d/dt stepAt a ε`. -/
def bumpAt (a ε : ℝ) (t : ℝ) : ℝ := deriv (stepAt a ε) t

theorem hasDerivAt_stepAt (a ε t : ℝ) : HasDerivAt (stepAt a ε) (bumpAt a ε t) t :=
  (((contDiff_stepAt a ε).differentiable (by simp)) t).hasDerivAt

theorem continuous_bumpAt (a ε : ℝ) : Continuous (bumpAt a ε) := by
  have := (contDiff_stepAt a ε).continuous_deriv (by simp)
  exact this

theorem bumpAt_nonneg {a ε : ℝ} (hε : 0 < ε) (t : ℝ) : 0 ≤ bumpAt a ε t :=
  (monotone_stepAt hε).deriv_nonneg

theorem bumpAt_eq_zero_of_lt {a ε t : ℝ} (hε : 0 < ε) (ht : t < a - 2 * ε) : bumpAt a ε t = 0 := by
  have h : stepAt a ε =ᶠ[𝓝 t] fun _ => 0 := by
    filter_upwards [Iio_mem_nhds ht] with u hu
    exact stepAt_eq_zero hε (le_of_lt hu)
  simpa [bumpAt] using h.deriv_eq

theorem bumpAt_eq_zero_of_gt {a ε t : ℝ} (hε : 0 < ε) (ht : a - ε < t) : bumpAt a ε t = 0 := by
  have h : stepAt a ε =ᶠ[𝓝 t] fun _ => 1 := by
    filter_upwards [Ioi_mem_nhds ht] with u hu
    exact stepAt_eq_one hε (le_of_lt hu)
  simpa [bumpAt] using h.deriv_eq

theorem bumpAt_eq_zero {a ε t : ℝ} (hε : 0 < ε) (ht : t ∉ Icc (a - 2 * ε) (a - ε)) :
    bumpAt a ε t = 0 := by
  by_cases h : t < a - 2 * ε
  · exact bumpAt_eq_zero_of_lt hε h
  · exact bumpAt_eq_zero_of_gt hε (by
      by_contra h'
      exact ht ⟨not_lt.1 h, not_lt.1 h'⟩)

theorem integral_bumpAt {a ε : ℝ} (hε : 0 < ε) : ∫ t, bumpAt a ε t = 1 := by
  have h1 : ∫ t in (a - 2 * ε)..(a - ε), bumpAt a ε t = 1 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := stepAt a ε)
      (fun t _ => hasDerivAt_stepAt a ε t)
      ((continuous_bumpAt a ε).intervalIntegrable _ _)]
    rw [stepAt_eq_one hε le_rfl, stepAt_eq_zero hε le_rfl]; norm_num
  have h2 : ∫ t in Icc (a - 2 * ε) (a - ε), bumpAt a ε t = 1 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
    exact h1
  rw [← h2]
  symm
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => bumpAt_eq_zero hε ht

theorem integrable_bumpAt {a ε : ℝ} (hε : 0 < ε) : Integrable (bumpAt a ε) := by
  have hc : HasCompactSupport (bumpAt a ε) := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := a - 2 * ε)
      (b := a - ε)) ?_
    intro t ht
    by_contra h
    exact ht (bumpAt_eq_zero hε h)
  exact (continuous_bumpAt a ε).integrable_of_hasCompactSupport hc

/-- The cutoff `≈ 1_{[σ, τ)}`. -/
def cutoff (σ τ ε : ℝ) (t : ℝ) : ℝ := stepAt σ ε t * (1 - stepAt τ ε t)

theorem contDiff_cutoff (σ τ ε : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (cutoff σ τ ε) :=
  (contDiff_stepAt σ ε).mul (contDiff_const.sub (contDiff_stepAt τ ε))

theorem cutoff_eq_zero_of_le {σ τ ε t : ℝ} (hε : 0 < ε) (ht : t ≤ σ - 2 * ε) :
    cutoff σ τ ε t = 0 := by
  simp [cutoff, stepAt_eq_zero hε ht]

theorem cutoff_eq_zero_of_ge {σ τ ε t : ℝ} (hε : 0 < ε) (ht : τ - ε ≤ t) :
    cutoff σ τ ε t = 0 := by
  simp [cutoff, stepAt_eq_one hε ht]

theorem cutoff_eq_one {σ τ ε t : ℝ} (hε : 0 < ε) (h1 : σ - ε ≤ t) (h2 : t ≤ τ - 2 * ε) :
    cutoff σ τ ε t = 1 := by
  simp [cutoff, stepAt_eq_one hε h1, stepAt_eq_zero hε h2]

theorem cutoff_nonneg (σ τ ε t : ℝ) : 0 ≤ cutoff σ τ ε t :=
  mul_nonneg (stepAt_nonneg _ _ _) (sub_nonneg.2 (stepAt_le_one _ _ _))

theorem cutoff_le_one (σ τ ε t : ℝ) : cutoff σ τ ε t ≤ 1 := by
  unfold cutoff
  have h1 := stepAt_le_one σ ε t
  have h2 := stepAt_nonneg τ ε t
  have h3 := stepAt_nonneg σ ε t
  nlinarith

theorem tsupport_cutoff_subset {σ τ ε : ℝ} (hε : 0 < ε) :
    tsupport (cutoff σ τ ε) ⊆ Icc (σ - 2 * ε) (τ - ε) := by
  refine closure_minimal ?_ isClosed_Icc
  intro t ht
  by_contra h
  apply ht
  rcases not_and_or.1 h with h | h
  · exact cutoff_eq_zero_of_le hε (le_of_lt (not_le.1 h))
  · exact cutoff_eq_zero_of_ge hε (le_of_lt (not_le.1 h))

theorem hasCompactSupport_cutoff {σ τ ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (cutoff σ τ ε) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := σ - 2 * ε) (b := τ - ε))
    (subset_tsupport _ |>.trans (tsupport_cutoff_subset hε))

theorem deriv_cutoff {σ τ ε : ℝ} (hε : 0 < ε) (hετ : ε ≤ τ - σ) (t : ℝ) :
    deriv (cutoff σ τ ε) t = bumpAt σ ε t - bumpAt τ ε t := by
  have h1 : HasDerivAt (cutoff σ τ ε)
      (bumpAt σ ε t * (1 - stepAt τ ε t) + stepAt σ ε t * (0 - bumpAt τ ε t)) t :=
    (hasDerivAt_stepAt σ ε t).mul ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_stepAt τ ε t))
  rw [h1.deriv]
  have e1 : bumpAt σ ε t * (1 - stepAt τ ε t) = bumpAt σ ε t := by
    by_cases h : t ∈ Icc (σ - 2 * ε) (σ - ε)
    · rw [stepAt_eq_zero hε (by linarith [h.2]), sub_zero, mul_one]
    · rw [bumpAt_eq_zero hε h, zero_mul]
  have e2 : stepAt σ ε t * (0 - bumpAt τ ε t) = - bumpAt τ ε t := by
    by_cases h : t ∈ Icc (τ - 2 * ε) (τ - ε)
    · rw [stepAt_eq_one hε (by linarith [h.1]), zero_sub, one_mul]
    · rw [bumpAt_eq_zero hε h]; simp
  rw [e1, e2]; ring

/-- Pointwise limit of the cutoffs. -/
theorem tendsto_cutoff {σ τ : ℝ} (t : ℝ) (ht : t ≠ σ ∧ t ≠ τ) :
    Tendsto (fun ε => cutoff σ τ ε t) (𝓝[>] 0) (𝓝 (if σ < t ∧ t < τ then 1 else 0)) := by
  by_cases h : σ < t ∧ t < τ
  · rw [show (if σ < t ∧ t < τ then (1 : ℝ) else 0) = 1 from by simp [h]]
    refine tendsto_const_nhds.congr' ?_
    have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < t - σ := by
      exact mem_nhdsGT_iff_exists_Ioo_subset.2 ⟨t - σ, by show (0 : ℝ) < t - σ; linarith [h.1], fun x hx => hx.2⟩
    have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 2 * ε < τ - t := by
      refine mem_nhdsGT_iff_exists_Ioo_subset.2 ⟨(τ - t) / 2, by show (0 : ℝ) < (τ - t) / 2; linarith [h.2], fun x hx => ?_⟩
      have := hx.2; show 2 * x < τ - t; linarith
    filter_upwards [h1, h2, self_mem_nhdsWithin] with ε e1 e2 e3
    have e3' : 0 < ε := e3
    exact (cutoff_eq_one e3' (by linarith) (by linarith)).symm
  · rw [show (if σ < t ∧ t < τ then (1 : ℝ) else 0) = 0 from by simp [h]]
    refine tendsto_const_nhds.congr' ?_
    rcases le_or_gt t σ with h' | h'
    · have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 2 * ε < σ - t := by
        have hlt : t < σ := lt_of_le_of_ne h' ht.1
        refine mem_nhdsGT_iff_exists_Ioo_subset.2 ⟨(σ - t) / 2, by show (0 : ℝ) < (σ - t) / 2; linarith, fun x hx => ?_⟩
        have := hx.2; show 2 * x < σ - t; linarith
      filter_upwards [h1, self_mem_nhdsWithin] with ε e1 e3
      have e3' : 0 < ε := e3
      exact (cutoff_eq_zero_of_le e3' (by linarith)).symm
    · have h2 : τ ≤ t := by
        by_contra hc
        exact h ⟨h', not_le.1 hc⟩
      have hlt : τ < t := lt_of_le_of_ne h2 (Ne.symm ht.2)
      filter_upwards [self_mem_nhdsWithin] with ε e3
      have e3' : 0 < ε := e3
      exact (cutoff_eq_zero_of_ge e3' (by linarith)).symm

/-- The bump times an integrable function is integrable. -/
theorem integrable_bumpAt_mul {g : ℝ → ℝ} {a ε δ₀ : ℝ} (hε0 : 0 < ε) (hδ : 2 * ε < δ₀)
    (hint : IntegrableOn g (Ioo (a - δ₀) a)) : Integrable (fun t => bumpAt a ε t * g t) := by
  have hsub : Icc (a - 2 * ε) (a - ε) ⊆ Ioo (a - δ₀) a := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hg' : IntegrableOn g (Icc (a - 2 * ε) (a - ε)) := hint.mono_set hsub
  have hsupp : ∀ t, t ∉ Icc (a - 2 * ε) (a - ε) → bumpAt a ε t * g t = 0 := fun t ht => by
    rw [bumpAt_eq_zero hε0 ht, zero_mul]
  rw [← integrableOn_iff_integrable_of_support_subset (s := Icc (a - 2 * ε) (a - ε))]
  · have hbd : ∃ M, ∀ t, |bumpAt a ε t| ≤ M := by
      obtain ⟨M, hM⟩ := (continuous_bumpAt a ε).bounded_above_of_compact_support
        (HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := a - 2 * ε)
          (b := a - ε)) fun t ht => by
            by_contra h; exact ht (bumpAt_eq_zero hε0 h))
      exact ⟨M, fun t => by simpa using hM t⟩
    obtain ⟨M, hM⟩ := hbd
    refine Integrable.bdd_mul (c := M) hg' (continuous_bumpAt a ε).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun t => by simpa using hM t
  · intro t ht
    by_contra h
    exact ht (hsupp t h)

/-- Averaging against `bumpAt a ε` recovers the left limit along `𝓝[<] a ⊓ ae`. -/
theorem tendsto_average_bump {g : ℝ → ℝ} {a L δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hint : IntegrableOn g (Ioo (a - δ₀) a))
    (hlim : Tendsto g (𝓝[<] a ⊓ ae (volume : Measure ℝ)) (𝓝 L)) :
    Tendsto (fun ε => ∫ t, bumpAt a ε t * g t) (𝓝[>] 0) (𝓝 L) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  have hev : ∀ᶠ r in 𝓝[<] a ⊓ ae (volume : Measure ℝ), dist (g r) L < η / 2 :=
    (Metric.tendsto_nhds.1 hlim) (η / 2) (by linarith)
  obtain ⟨δ, hδ, hae⟩ := exists_Ioo_of_eventually hev
  have hε : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 2 * ε < min δ δ₀ := by
    refine mem_nhdsGT_iff_exists_Ioo_subset.2 ⟨min δ δ₀ / 2, by show (0 : ℝ) < min δ δ₀ / 2; positivity, fun x hx => ?_⟩
    have := hx.2; show 2 * x < min δ δ₀; linarith
  filter_upwards [hε, self_mem_nhdsWithin] with ε hε1 hε2
  have hε0 : 0 < ε := hε2
  have hδm : 2 * ε < δ := lt_of_lt_of_le hε1 (min_le_left _ _)
  have hδm0 : 2 * ε < δ₀ := lt_of_lt_of_le hε1 (min_le_right _ _)
  have hsub : Icc (a - 2 * ε) (a - ε) ⊆ Ioo (a - δ₀) a := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hρ1 := integrable_bumpAt (a := a) hε0
  have hbg : Integrable (fun t => bumpAt a ε t * g t) := integrable_bumpAt_mul hε0 hδm0 hint
  have hid : (∫ t, bumpAt a ε t * g t) - L = ∫ t, bumpAt a ε t * (g t - L) := by
    have : ∫ t, bumpAt a ε t * (g t - L) = (∫ t, bumpAt a ε t * g t) - L * ∫ t, bumpAt a ε t := by
      have e : (fun t => bumpAt a ε t * (g t - L)) =
          fun t => bumpAt a ε t * g t - L * bumpAt a ε t := by
        funext t; ring
      rw [e, integral_sub hbg (hρ1.const_mul L), integral_const_mul L (bumpAt a ε)]
    rw [this, integral_bumpAt hε0]; ring
  rw [Real.dist_eq, hid]
  have hbd : ∀ᵐ t ∂(volume : Measure ℝ), ‖bumpAt a ε t * (g t - L)‖ ≤ (η / 2) * bumpAt a ε t := by
    filter_upwards [hae] with t ht
    by_cases hI : t ∈ Icc (a - 2 * ε) (a - ε)
    · have hmem : t ∈ Ioo (a - δ) a := ⟨by linarith [hI.1], by linarith [hI.2]⟩
      have := ht hmem
      rw [Real.dist_eq] at this
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (bumpAt_nonneg (a := a) hε0 t)]
      nlinarith [bumpAt_nonneg (a := a) hε0 t]
    · rw [bumpAt_eq_zero hε0 hI]; simp
  have h1 := norm_integral_le_of_norm_le (hρ1.const_mul (η / 2)) hbd
  rw [integral_const_mul, integral_bumpAt hε0] at h1
  have : ‖∫ t, bumpAt a ε t * (g t - L)‖ = |∫ t, bumpAt a ε t * (g t - L)| := Real.norm_eq_abs _
  linarith

end AVRegularity.Applications.LimitsLocal
end
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Filter Topology Homogenization Set
namespace AVRegularity.Applications.LimitsLocal

/-! # The pairing identity from the distributional equation

For a function `θ` integrable on a set `P` of space-time satisfying the distributional equation
`∬ θ (∂ₜφ + b·∇φ + κΔφ) = 0` for tests supported in `P`, and a spatial test `ψ`, the pairing
`g(t) = ∫ θ(t,x) ψ(x) dx` has distributional derivative `G(t) = ∫ θ(t,x) Ψ(t,x) dx`,
`Ψ = b·∇ψ + κΔψ`. Testing with the cutoffs of `TimeTest` and using the left traces of `g`
at `σ < τ` gives `g(τ⁻) - g(σ⁻) = ∫_σ^τ G`. -/

theorem hasFDerivAt_prodTest {χ : ℝ → ℝ} {ψ : Vec 2 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (p : ℝ × Vec 2) :
    HasFDerivAt (fun q : ℝ × Vec 2 => χ q.1 * ψ q.2)
      (χ p.1 • (fderiv ℝ ψ p.2).comp (ContinuousLinearMap.snd ℝ ℝ (Vec 2)) +
        ψ p.2 • (deriv χ p.1 • ContinuousLinearMap.fst ℝ ℝ (Vec 2))) p := by
  have h1 : HasFDerivAt (fun q : ℝ × Vec 2 => χ q.1)
      ((deriv χ p.1) • (ContinuousLinearMap.fst ℝ ℝ (Vec 2))) p := by
    have := (((hχ.differentiable (by simp)) p.1).hasDerivAt).hasFDerivAt.comp p
      (hasFDerivAt_fst (𝕜 := ℝ) (p := p))
    exact this.congr_fderiv (ContinuousLinearMap.ext fun v => by simp [mul_comm])
  have h2 : HasFDerivAt (fun q : ℝ × Vec 2 => ψ q.2)
      ((fderiv ℝ ψ p.2).comp (ContinuousLinearMap.snd ℝ ℝ (Vec 2))) p :=
    (((hψ.differentiable (by simp)) p.2).hasFDerivAt).comp p
      (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
  exact h1.mul h2 |>.congr_fderiv (by rw [add_comm])

theorem fderiv_prodTest_time {χ : ℝ → ℝ} {ψ : Vec 2 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (p : ℝ × Vec 2) :
    fderiv ℝ (fun q : ℝ × Vec 2 => χ q.1 * ψ q.2) p (1, 0) = deriv χ p.1 * ψ p.2 := by
  rw [(hasFDerivAt_prodTest hχ hψ p).fderiv]
  simp [mul_comm]

theorem fderiv_prodTest_space {χ : ℝ → ℝ} {ψ : Vec 2 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (p : ℝ × Vec 2) (v : Vec 2) :
    fderiv ℝ (fun q : ℝ × Vec 2 => χ q.1 * ψ q.2) p (0, v) = χ p.1 * fderiv ℝ ψ p.2 v := by
  rw [(hasFDerivAt_prodTest hχ hψ p).fderiv]
  simp

/-- `Ψ = b·∇ψ + κΔψ` in the form of the distributional equation. -/
def Psi (b : ℝ → Vec 2 → Vec 2) (κ : ℝ) (ψ : Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : ℝ :=
  ∑ i : Fin 2, b t x i * fderiv ℝ ψ x (basisVec i) +
    κ * ∑ i : Fin 2, fderiv ℝ (fun y => fderiv ℝ ψ y (basisVec i)) x (basisVec i)

/-- The pairing `g(t) = ∫ θ(t,x) ψ(x) dx`. -/
def pairG (θ : ℝ → Vec 2 → ℝ) (ψ : Vec 2 → ℝ) (t : ℝ) : ℝ := ∫ x, θ t x * ψ x

/-- The drift pairing `G(t) = ∫ θ(t,x) Ψ(t,x) dx`. -/
def driftG (b : ℝ → Vec 2 → Vec 2) (κ : ℝ) (θ : ℝ → Vec 2 → ℝ) (ψ : Vec 2 → ℝ) (t : ℝ) : ℝ :=
  ∫ x, θ t x * Psi b κ ψ t x

theorem continuous_Psi {b : ℝ → Vec 2 → Vec 2} (hbc : Continuous fun p : ℝ × Vec 2 => b p.1 p.2)
    (κ : ℝ) {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    Continuous fun p : ℝ × Vec 2 => Psi b κ ψ p.1 p.2 := by
  unfold Psi
  have h1 : ∀ i : Fin 2, Continuous fun x : Vec 2 => fderiv ℝ ψ x (basisVec i) := fun i =>
    (contDiff_fderiv_apply_of_smooth hψ (basisVec i)).continuous
  have h2 : ∀ i : Fin 2, Continuous fun x : Vec 2 =>
      fderiv ℝ (fun y => fderiv ℝ ψ y (basisVec i)) x (basisVec i) := fun i =>
    (contDiff_fderiv_apply_of_smooth (contDiff_fderiv_apply_of_smooth hψ (basisVec i))
      (basisVec i)).continuous
  refine (continuous_finsetSum _ fun i _ => ?_).add (continuous_const.mul
    (continuous_finsetSum _ fun i _ => (h2 i).comp continuous_snd))
  exact ((continuous_apply i).comp hbc).mul ((h1 i).comp continuous_snd)

theorem Psi_eq_zero_of_notMem {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {ψ : Vec 2 → ℝ}
    {x : Vec 2} (hx : x ∉ tsupport ψ) (t : ℝ) :
    Psi b κ ψ t x = 0 := by
  have h1 : ∀ i : Fin 2, fderiv ℝ ψ x (basisVec i) = 0 := fun i =>
    by simp [fderiv_of_notMem_tsupport (𝕜 := ℝ) hx]
  have hx' : ∀ i : Fin 2, x ∉ tsupport (fun y => fderiv ℝ ψ y (basisVec i)) := fun i h =>
    hx (tsupport_fderiv_apply_subset ψ (basisVec i) h)
  have h2 : ∀ i : Fin 2, fderiv ℝ (fun y => fderiv ℝ ψ y (basisVec i)) x (basisVec i) = 0 :=
    fun i => by simp [fderiv_of_notMem_tsupport (𝕜 := ℝ) (hx' i)]
  simp [Psi, h1, h2]

theorem exists_Psi_bound {b : ℝ → Vec 2 → Vec 2} {Bb : ℝ} (hB : ∀ t x, ‖b t x‖ ≤ Bb) (κ : ℝ)
    {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∃ M : ℝ, ∀ t x, |Psi b κ ψ t x| ≤ M := by
  have h1 : ∀ i : Fin 2, ∃ M, ∀ x, |fderiv ℝ ψ x (basisVec i)| ≤ M := fun i => by
    obtain ⟨M, hM⟩ := (contDiff_fderiv_apply_of_smooth hψ (basisVec i)).continuous.bounded_above_of_compact_support
      (hasCompactSupport_fderiv_apply hψc (basisVec i))
    exact ⟨M, fun x => by simpa using hM x⟩
  have h2 : ∀ i : Fin 2, ∃ M, ∀ x,
      |fderiv ℝ (fun y => fderiv ℝ ψ y (basisVec i)) x (basisVec i)| ≤ M := fun i => by
    obtain ⟨M, hM⟩ := (contDiff_fderiv_apply_of_smooth (contDiff_fderiv_apply_of_smooth hψ
      (basisVec i)) (basisVec i)).continuous.bounded_above_of_compact_support
      (hasCompactSupport_fderiv_apply (hasCompactSupport_fderiv_apply hψc (basisVec i))
        (basisVec i))
    exact ⟨M, fun x => by simpa using hM x⟩
  choose M1 hM1 using h1
  choose M2 hM2 using h2
  refine ⟨∑ i : Fin 2, (|Bb| * |M1 i|) + |κ| * ∑ i : Fin 2, |M2 i|, fun t x => ?_⟩
  unfold Psi
  have hb : ∀ i : Fin 2, |b t x i| ≤ |Bb| := fun i => by
    have := (norm_le_pi_norm (b t x) i).trans (hB t x)
    simpa using this.trans (le_abs_self _)
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    exact mul_le_mul (hb i) ((hM1 i x).trans (le_abs_self _)) (abs_nonneg _) (abs_nonneg _)
  · rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i _ => (hM2 i x).trans (le_abs_self _))) (abs_nonneg _)

/-! # Testing the distributional equation with `χ(t) ψ(x)`

`test_identity`: `∫ χ' g + ∫ χ G = 0`. `pairing_limit`: with the cutoffs of `TimeTest` and left
traces `Lσ`, `Lτ` of `g`, `Lτ - Lσ = ∫_σ^τ G`. -/

/-- A function integrable on `P` times a continuous function supported in a compact `S ⊆ P`. -/
theorem integrable_mul_compact {f : ℝ × Vec 2 → ℝ} {S P : Set (ℝ × Vec 2)} (hSP : S ⊆ P)
    (hf : IntegrableOn f P) (hS : IsCompact S) {h : ℝ × Vec 2 → ℝ} (hh : Continuous h)
    (hsupp : ∀ p, p ∉ S → h p = 0) : Integrable (fun p => f p * h p) := by
  have hc : HasCompactSupport h :=
    HasCompactSupport.of_support_subset_isCompact hS fun p hp => by
      by_contra hn; exact hp (hsupp p hn)
  obtain ⟨M, hM⟩ := hh.bounded_above_of_compact_support hc
  have h1 : IntegrableOn (fun p => h p * f p) S :=
    Integrable.bdd_mul (c := M) (hf.mono_set hSP) hh.aestronglyMeasurable
      (Filter.Eventually.of_forall hM)
  have h2 : Integrable (fun p => h p * f p) := by
    rw [← integrableOn_iff_integrable_of_support_subset (s := S)]
    · exact h1
    · intro p hp
      by_contra hn; exact hp (by simp [hsupp p hn])
  simpa [mul_comm] using h2

theorem test_identity {θ : ℝ → Vec 2 → ℝ} {P : Set (ℝ × Vec 2)} {b : ℝ → Vec 2 → Vec 2} {κ : ℝ}
    (hθ : IntegrableOn (fun p : ℝ × Vec 2 => θ p.1 p.2) P)
    (hweak : ∀ φ : ℝ × Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ P → ∫ p in P, θ p.1 p.2 *
        (fderiv ℝ φ p (1, 0) + ∑ i : Fin 2, b p.1 p.2 i * fderiv ℝ φ p (0, basisVec i)
          + κ * ∑ i : Fin 2,
            fderiv ℝ (fun p' => fderiv ℝ φ p' (0, basisVec i)) p (0, basisVec i)) = 0)
    (hbc : Continuous fun p : ℝ × Vec 2 => b p.1 p.2)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hsub : tsupport χ ×ˢ tsupport ψ ⊆ P) :
    (∫ t, deriv χ t * pairG θ ψ t) + ∫ t, χ t * driftG b κ θ ψ t = 0 := by
  set S : Set (ℝ × Vec 2) := tsupport χ ×ˢ tsupport ψ with hS
  have hScomp : IsCompact S := hχc.isCompact.prod hψc.isCompact
  set φ : ℝ × Vec 2 → ℝ := fun q => χ q.1 * ψ q.2 with hφdef
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := (hχ.comp contDiff_fst).mul (hψ.comp contDiff_snd)
  have hφS : tsupport φ ⊆ S := by
    refine closure_minimal ?_ (hScomp.isClosed)
    intro p hp
    have hp1 : χ p.1 ≠ 0 := left_ne_zero_of_mul hp
    have hp2 : ψ p.2 ≠ 0 := right_ne_zero_of_mul hp
    exact ⟨subset_tsupport _ hp1, subset_tsupport _ hp2⟩
  have hφc : HasCompactSupport φ := hScomp.of_isClosed_subset (isClosed_tsupport _) hφS
  have hweak' := hweak φ hφ hφc (hφS.trans hsub)
  -- the integrand
  set h1 : ℝ × Vec 2 → ℝ := fun p => deriv χ p.1 * ψ p.2 with hh1
  set h2 : ℝ × Vec 2 → ℝ := fun p => χ p.1 * Psi b κ ψ p.1 p.2 with hh2
  have hint : ∀ p : ℝ × Vec 2, θ p.1 p.2 *
      (fderiv ℝ φ p (1, 0) + ∑ i : Fin 2, b p.1 p.2 i * fderiv ℝ φ p (0, basisVec i)
        + κ * ∑ i : Fin 2,
          fderiv ℝ (fun p' => fderiv ℝ φ p' (0, basisVec i)) p (0, basisVec i)) =
      θ p.1 p.2 * h1 p + θ p.1 p.2 * h2 p := by
    intro p
    have e1 : fderiv ℝ φ p (1, 0) = deriv χ p.1 * ψ p.2 := fderiv_prodTest_time hχ hψ p
    have e2 : ∀ i : Fin 2, fderiv ℝ φ p (0, basisVec i) = χ p.1 * fderiv ℝ ψ p.2 (basisVec i) :=
      fun i => fderiv_prodTest_space hχ hψ p _
    have e3 : ∀ i : Fin 2, fderiv ℝ (fun p' => fderiv ℝ φ p' (0, basisVec i)) p (0, basisVec i) =
        χ p.1 * fderiv ℝ (fun y => fderiv ℝ ψ y (basisVec i)) p.2 (basisVec i) := by
      intro i
      have : (fun p' : ℝ × Vec 2 => fderiv ℝ φ p' (0, basisVec i)) =
          fun p' => χ p'.1 * (fun y => fderiv ℝ ψ y (basisVec i)) p'.2 := by
        funext p'; exact fderiv_prodTest_space hχ hψ p' _
      rw [this]
      exact fderiv_prodTest_space hχ (contDiff_fderiv_apply_of_smooth hψ (basisVec i)) p _
    have sA : ∑ i : Fin 2, b p.1 p.2 i * (χ p.1 * fderiv ℝ ψ p.2 (basisVec i)) =
        χ p.1 * ∑ i : Fin 2, b p.1 p.2 i * fderiv ℝ ψ p.2 (basisVec i) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    have sB : ∑ i : Fin 2, χ p.1 * fderiv ℝ (fun y => fderiv ℝ ψ y (basisVec i)) p.2
        (basisVec i) = χ p.1 * ∑ i : Fin 2,
          fderiv ℝ (fun y => fderiv ℝ ψ y (basisVec i)) p.2 (basisVec i) :=
      (Finset.mul_sum _ _ _).symm
    simp only [e1, e2, e3]
    rw [sA, sB]
    simp only [hh1, hh2, Psi]
    ring
  have hχd : Continuous (deriv χ) := hχ.continuous_deriv (by simp)
  have hc1 : Continuous h1 := (hχd.comp continuous_fst).mul (hψ.continuous.comp continuous_snd)
  have hc2 : Continuous h2 := (hχ.continuous.comp continuous_fst).mul
    (continuous_Psi hbc κ hψ)
  have hs1 : ∀ p, p ∉ S → h1 p = 0 := by
    intro p hp
    by_cases hp1 : p.1 ∈ tsupport χ
    · have hp2 : p.2 ∉ tsupport ψ := fun h => hp ⟨hp1, h⟩
      simp [hh1, image_eq_zero_of_notMem_tsupport hp2]
    · simp [hh1, deriv_of_notMem_tsupport (𝕜 := ℝ) hp1]
  have hs2 : ∀ p, p ∉ S → h2 p = 0 := by
    intro p hp
    by_cases hp1 : p.1 ∈ tsupport χ
    · have hp2 : p.2 ∉ tsupport ψ := fun h => hp ⟨hp1, h⟩
      simp [hh2, Psi_eq_zero_of_notMem hp2]
    · simp [hh2, image_eq_zero_of_notMem_tsupport hp1]
  have hI1 := integrable_mul_compact hsub hθ hScomp hc1 hs1
  have hI2 := integrable_mul_compact hsub hθ hScomp hc2 hs2
  have hall : ∫ p in P, θ p.1 p.2 * h1 p + θ p.1 p.2 * h2 p =
      ∫ p, θ p.1 p.2 * h1 p + θ p.1 p.2 * h2 p := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp => ?_
    have : p ∉ S := fun h => hp (hsub h)
    simp [hs1 p this, hs2 p this]
  simp_rw [hint] at hweak'
  rw [hall, integral_add hI1 hI2] at hweak'
  have hF1 : ∫ p : ℝ × Vec 2, θ p.1 p.2 * h1 p = ∫ t, deriv χ t * pairG θ ψ t := by
    have hi : Integrable (fun p : ℝ × Vec 2 => θ p.1 p.2 * h1 p) (volume.prod volume) := by
      rw [← Measure.volume_eq_prod]; exact hI1
    rw [Measure.volume_eq_prod, integral_prod _ hi]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [pairG, hh1]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only; ring
  have hF2 : ∫ p : ℝ × Vec 2, θ p.1 p.2 * h2 p = ∫ t, χ t * driftG b κ θ ψ t := by
    have hi : Integrable (fun p : ℝ × Vec 2 => θ p.1 p.2 * h2 p) (volume.prod volume) := by
      rw [← Measure.volume_eq_prod]; exact hI2
    rw [Measure.volume_eq_prod, integral_prod _ hi]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [driftG, hh2]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only; ring
  rw [← hF1, ← hF2]
  exact hweak'

theorem integrableOn_marginal {f : ℝ × Vec 2 → ℝ} {A : Set ℝ} {B : Set (Vec 2)}
    (hf : IntegrableOn f (A ×ˢ B)) : IntegrableOn (fun t => ∫ x in B, f (t, x)) A := by
  unfold IntegrableOn at hf ⊢
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hf
  exact hf.integral_prod_left

theorem integrableOn_mul_bdd {f h : ℝ × Vec 2 → ℝ} {S : Set (ℝ × Vec 2)} (hf : IntegrableOn f S)
    (hh : Continuous h) (hb : ∃ M, ∀ p, |h p| ≤ M) : IntegrableOn (fun p => f p * h p) S := by
  obtain ⟨M, hM⟩ := hb
  have := Integrable.bdd_mul (c := M) hf hh.aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => by simpa using hM p)
  show Integrable (fun p => f p * h p) (volume.restrict S)
  simpa [mul_comm] using this

theorem pairing_limit {θ : ℝ → Vec 2 → ℝ} {P : Set (ℝ × Vec 2)} {b : ℝ → Vec 2 → Vec 2} {κ : ℝ}
    {Bb : ℝ} (hB : ∀ t x, ‖b t x‖ ≤ Bb)
    (hθ : IntegrableOn (fun p : ℝ × Vec 2 => θ p.1 p.2) P)
    (hweak : ∀ φ : ℝ × Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ P → ∫ p in P, θ p.1 p.2 *
        (fderiv ℝ φ p (1, 0) + ∑ i : Fin 2, b p.1 p.2 i * fderiv ℝ φ p (0, basisVec i)
          + κ * ∑ i : Fin 2,
            fderiv ℝ (fun p' => fderiv ℝ φ p' (0, basisVec i)) p (0, basisVec i)) = 0)
    (hbc : Continuous fun p : ℝ × Vec 2 => b p.1 p.2)
    {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    {σ τ η : ℝ} (hστ : σ < τ) (hη : 0 < η)
    (hcyl : Ico (σ - η) τ ×ˢ tsupport ψ ⊆ P) {Lσ Lτ : ℝ}
    (hσ : Tendsto (pairG θ ψ) (𝓝[<] σ ⊓ ae (volume : Measure ℝ)) (𝓝 Lσ))
    (hτ : Tendsto (pairG θ ψ) (𝓝[<] τ ⊓ ae (volume : Measure ℝ)) (𝓝 Lτ)) :
    Lτ - Lσ = ∫ t in σ..τ, driftG b κ θ ψ t := by
  set B : Set (Vec 2) := tsupport ψ with hBdef
  set A : Set ℝ := Ioo (σ - η) τ with hAdef
  have hAB : A ×ˢ B ⊆ P := fun p hp => hcyl ⟨⟨hp.1.1.le, hp.1.2⟩, hp.2⟩
  have hθAB : IntegrableOn (fun p : ℝ × Vec 2 => θ p.1 p.2) (A ×ˢ B) := hθ.mono_set hAB
  obtain ⟨Mψ, hMψ⟩ : ∃ M, ∀ x, |ψ x| ≤ M := by
    obtain ⟨M, hM⟩ := hψ.continuous.bounded_above_of_compact_support hψc
    exact ⟨M, fun x => by simpa using hM x⟩
  obtain ⟨MΨ, hMΨ⟩ := exists_Psi_bound hB hψ hψc (κ := κ) (b := b) |> fun h => h
  have hg : IntegrableOn (pairG θ ψ) A := by
    have h1 := integrableOn_marginal (integrableOn_mul_bdd (h := fun p : ℝ × Vec 2 => ψ p.2)
      hθAB (hψ.continuous.comp continuous_snd) ⟨Mψ, fun p => hMψ _⟩)
    refine h1.congr_fun (fun t _ => ?_) measurableSet_Ioo
    simp only [pairG]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      simp [image_eq_zero_of_notMem_tsupport hx]
  have hG : IntegrableOn (driftG b κ θ ψ) A := by
    have h1 := integrableOn_marginal (integrableOn_mul_bdd (h := fun p : ℝ × Vec 2 =>
      Psi b κ ψ p.1 p.2) hθAB (continuous_Psi hbc κ hψ) ⟨MΨ, fun p => hMΨ _ _⟩)
    refine h1.congr_fun (fun t _ => ?_) measurableSet_Ioo
    simp only [driftG]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      simp [Psi_eq_zero_of_notMem hx]
  have hσA : Ioo (σ - η) σ ⊆ A := fun t ht => ⟨ht.1, ht.2.trans hστ⟩
  have hτA : Ioo (τ - η) τ ⊆ A := fun t ht => ⟨by linarith [ht.1], ht.2⟩
  have hf1 := tendsto_average_bump hη (hg.mono_set hσA) hσ
  have hf2 := tendsto_average_bump hη (hg.mono_set hτA) hτ
  -- the identity for small `ε`
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < min (η / 2) (τ - σ) :=
    mem_nhdsGT_iff_exists_Ioo_subset.2 ⟨min (η / 2) (τ - σ), by
      show (0 : ℝ) < _; exact lt_min (by linarith) (by linarith), fun x hx => hx.2⟩
  have heq : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (∫ t, bumpAt σ ε t * pairG θ ψ t) -
      (∫ t, bumpAt τ ε t * pairG θ ψ t) + ∫ t, cutoff σ τ ε t * driftG b κ θ ψ t = 0 := by
    filter_upwards [hsmall, self_mem_nhdsWithin] with ε hε hε0'
    have hε0 : 0 < ε := hε0'
    have hε1 : ε < η / 2 := lt_of_lt_of_le hε (min_le_left _ _)
    have hε2 : ε < τ - σ := lt_of_lt_of_le hε (min_le_right _ _)
    have hsub : tsupport (cutoff σ τ ε) ×ˢ tsupport ψ ⊆ P := by
      intro p hp
      have h1 := tsupport_cutoff_subset (σ := σ) (τ := τ) hε0 hp.1
      exact hcyl ⟨⟨by linarith [h1.1], by linarith [h1.2]⟩, hp.2⟩
    have hid := test_identity hθ hweak hbc (contDiff_cutoff σ τ ε) (hasCompactSupport_cutoff hε0)
      hψ hψc hsub
    have hder : (fun t => deriv (cutoff σ τ ε) t * pairG θ ψ t) =
        fun t => bumpAt σ ε t * pairG θ ψ t - bumpAt τ ε t * pairG θ ψ t := by
      funext t; rw [deriv_cutoff hε0 hε2.le]; ring
    rw [hder, integral_sub (integrable_bumpAt_mul hε0 (by linarith) (hg.mono_set hσA))
      (integrable_bumpAt_mul hε0 (by linarith) (hg.mono_set hτA))] at hid
    exact hid
  have hf3 : Tendsto (fun ε => ∫ t, cutoff σ τ ε t * driftG b κ θ ψ t) (𝓝[>] 0)
      (𝓝 (∫ t in σ..τ, driftG b κ θ ψ t)) := by
    have hrestrict : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∫ t, cutoff σ τ ε t * driftG b κ θ ψ t =
        ∫ t in A, cutoff σ τ ε t * driftG b κ θ ψ t := by
      filter_upwards [hsmall, self_mem_nhdsWithin] with ε hε hε0'
      have hε0 : 0 < ε := hε0'
      have hε1 : ε < η / 2 := lt_of_lt_of_le hε (min_le_left _ _)
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_).symm
      have : t ≤ σ - η ∨ τ ≤ t := by
        by_contra hc
        push Not at hc
        exact ht ⟨hc.1, hc.2⟩
      rcases this with h | h
      · simp [cutoff_eq_zero_of_le hε0 (show t ≤ σ - 2 * ε by linarith)]
      · simp [cutoff_eq_zero_of_ge hε0 (show τ - ε ≤ t by linarith)]
    refine Tendsto.congr' (hrestrict.mono fun ε h => h.symm) ?_
    have hlim := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict A)
      (l := 𝓝[>] (0 : ℝ)) (F := fun ε t => cutoff σ τ ε t * driftG b κ θ ψ t)
      (f := (Ioo σ τ).indicator (driftG b κ θ ψ)) (bound := fun t => ‖driftG b κ θ ψ t‖)
      (Filter.Eventually.of_forall fun ε =>
        ((contDiff_cutoff σ τ ε).continuous.aestronglyMeasurable).mul hG.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ε => Filter.Eventually.of_forall fun t => by
        rw [norm_mul]
        have h0 := cutoff_nonneg σ τ ε t
        have h1 := cutoff_le_one σ τ ε t
        rw [Real.norm_eq_abs, abs_of_nonneg h0]
        exact mul_le_of_le_one_left (norm_nonneg _) h1)
      hG.norm ?_
    · have hAind : ∫ t in A, (Ioo σ τ).indicator (driftG b κ θ ψ) t =
          ∫ t in σ..τ, driftG b κ θ ψ t := by
        rw [setIntegral_indicator measurableSet_Ioo]
        have : A ∩ Ioo σ τ = Ioo σ τ := inter_eq_right.2 fun t ht => ⟨by linarith [ht.1], ht.2⟩
        rw [this, intervalIntegral.integral_of_le hστ.le, integral_Ioc_eq_integral_Ioo]
      rw [hAind] at hlim
      exact hlim
    · have hne : ∀ᵐ t ∂(volume.restrict A), t ≠ σ ∧ t ≠ τ := by
        refine ae_restrict_of_ae ?_
        have h1 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ σ := by rw [ae_iff]; simp
        have h2 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ τ := by rw [ae_iff]; simp
        filter_upwards [h1, h2] with t a b using ⟨a, b⟩
      filter_upwards [hne] with t ht
      have := (tendsto_cutoff (σ := σ) (τ := τ) t ht).mul_const (driftG b κ θ ψ t)
      have e : (if σ < t ∧ t < τ then (1 : ℝ) else 0) * driftG b κ θ ψ t =
          (Ioo σ τ).indicator (driftG b κ θ ψ) t := by
        by_cases h : σ < t ∧ t < τ
        · simp [h]
        · simp [h]
      rw [← e]; exact this
  have hsum := (hf1.sub hf2).add hf3
  have hlim0 : Tendsto (fun ε : ℝ => (0 : ℝ)) (𝓝[>] 0) (𝓝 (Lσ - Lτ + ∫ t in σ..τ, driftG b κ θ ψ t)) :=
    hsum.congr' (heq.mono fun ε h => h)
  have := tendsto_nhds_unique hlim0 tendsto_const_nhds
  linarith

end AVRegularity.Applications.LimitsLocal
end
end
end

section
@[expose] public section
open MeasureTheory Filter Topology Homogenization AVenhance
namespace AVRegularity.Applications

/-! # The statement of the local theorem

`OcLocalStatement α s q ζ` is exactly the conclusion of the theorem
`AVRegularity.local_interior_regularity`, for fixed `α, s`, admissible `q` and fast profile `ζ`. It
is the explicit hypothesis of the conditional local vanishing-diffusivity limits.
`ocLocalStatement_of_global` derives it from the global statement through the assembled theorem
`local_interior_regularity_of_tools`. -/

/-- **The local statement** (the conclusion of `AVRegularity.local_interior_regularity`). -/
def OcLocalStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
        ∃ b : ℝ → Vec 2 → Vec 2,
          (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) ∧
          ∀ cT CT : ℝ, 0 < cT → 0 < CT → ∃ C₁ : ℝ, 0 < C₁ ∧
            ∀ (n : ℕ) (T R ϱ ϑ : ℝ), 2 ≤ n → 0 < T → 0 < R → 0 < ϱ → ϱ < 1 / 8 →
              0 < ϑ → ϑ < 4 →
              cT * ocTauPP α q Λ (n - 1) ≤ T → T ≤ CT * ocTauPP α q Λ (n - 1) →
              8 * T * ocA α q Λ (n - 2) ≤ ocCStar →
              C₁ * max (ocEpsilon q Λ (n - 1) ^ α * T)
                  (Real.sqrt (sSup (ocBandSet α q Λ) * T)) ≤ R →
              R ≤ 1 / 8 →
              ∃ C : ℝ, ∀ t₁ : ℝ, ∀ X : ℝ → Vec 2 → ℝ → Vec 2,
                IsFlow (streamVel (Φ (n - 2))) X →
                ∀ κ ∈ ocBandSet α q Λ, ∀ θ : ℝ → Vec 2 → ℝ,
                  IsLocalEnergySolution b κ (fun t y => X t y t₁) t₁ T R θ →
                  ∃ Θ : ℝ → Vec 2 → ℝ, ∀ t ∈ Set.Icc (t₁ - ϑ * T) t₁,
                    ContinuousOn (Θ t) ((fun y => X t y t₁) '' euclidBall 0 (ϱ * R)) ∧
                    Tendsto (fun r => ∫ y in euclidBall 0 (ϱ * R),
                        (θ r (X r y t₁) - Θ t (X t y t₁)) ^ 2)
                      (𝓝[<] t ⊓ ae volume) (𝓝 0) ∧
                    ∀ x ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R),
                    ∀ y ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R),
                    ∀ z ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R), y ≠ z →
                      |Θ t x| + |Θ t y - Θ t z| / Real.sqrt (vecNormSq (y - z)) ^ s ≤
                        C * Real.sqrt ((volume (outerPipe (fun t y => X t y t₁) t₁ T R)).toReal⁻¹ *
                          ∫ p in outerPipe (fun t y => X t y t₁) t₁ T R, θ p.1 p.2 ^ 2)

end AVRegularity.Applications
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Filter Topology Homogenization AVenhance Set
namespace AVRegularity.Applications.LimitsLocal

/-! # Sup-norm bounds for the scaled mollifier and mollifier averages

`mollK r x` has first and second derivatives bounded by `D r⁻³`, `D r⁻⁴`; hence
`Ψ = b·∇ψ + κΔψ` for `ψ = mollK r x` is bounded by `2 Bb D r⁻³ + 2 |κ| D r⁻⁴`. A function with
oscillation at most `ε₀` on the sup-ball `B_r(x)` differs from its mollifier average at `x` by at
most `ε₀`. -/

open AVRegularity.Applications

theorem exists_kern_bound : ∃ D : ℝ, 0 ≤ D ∧ ∀ r : ℝ, 0 < r → ∀ x y : Vec 2, ∀ j : Fin 2,
    |spaceGrad (mollK r x) y j| ≤ D * r⁻¹ ^ 3 ∧
    |spaceGrad (fun w => spaceGrad (mollK r x) w j) y j| ≤ D * r⁻¹ ^ 4 := by
  have h1 : ∀ j : Fin 2, ∃ M : ℝ, 0 ≤ M ∧ ∀ z, |spaceGrad ω0 z j| ≤ M := fun j => by
    obtain ⟨M, hM⟩ := (contDiff_spaceGrad_apply ω0_contDiff j).continuous.bounded_above_of_compact_support
      (hasCompactSupport_spaceGrad_apply ω0_compact j)
    exact ⟨max M 0, le_max_right _ _, fun z => ((Real.norm_eq_abs _).symm.le.trans (hM z)).trans (le_max_left _ _)⟩
  have h2 : ∀ j : Fin 2, ∃ M : ℝ, 0 ≤ M ∧ ∀ z,
      |spaceGrad (fun w => spaceGrad ω0 w j) z j| ≤ M := fun j => by
    have hg := contDiff_spaceGrad_apply ω0_contDiff j
    obtain ⟨M, hM⟩ := (contDiff_spaceGrad_apply hg j).continuous.bounded_above_of_compact_support
      (hasCompactSupport_spaceGrad_apply (hasCompactSupport_spaceGrad_apply ω0_compact j) j)
    exact ⟨max M 0, le_max_right _ _, fun z => ((Real.norm_eq_abs _).symm.le.trans (hM z)).trans (le_max_left _ _)⟩
  choose M1 hM10 hM1 using h1
  choose M2 hM20 hM2 using h2
  refine ⟨∑ j : Fin 2, (M1 j + M2 j), Finset.sum_nonneg fun j _ => add_nonneg (hM10 j) (hM20 j),
    fun r hr x y j => ?_⟩
  have hr3 : 0 ≤ r⁻¹ ^ 3 := by positivity
  have hr4 : 0 ≤ r⁻¹ ^ 4 := by positivity
  have hjle : M1 j + M2 j ≤ ∑ j : Fin 2, (M1 j + M2 j) :=
    Finset.single_le_sum (f := fun j => M1 j + M2 j) (fun j _ => add_nonneg (hM10 j) (hM20 j))
      (Finset.mem_univ j)
  have hD : 0 ≤ M1 j := hM10 j
  have hD2 : 0 ≤ M2 j := hM20 j
  constructor
  · have := congrFun (spaceGrad_kern (r := r) x j) y
    rw [this, abs_mul, abs_neg, abs_of_nonneg hr3]
    have : |scl r x (fun z => spaceGrad ω0 z j) y| ≤ M1 j := hM1 j _
    calc r⁻¹ ^ 3 * |scl r x (fun z => spaceGrad ω0 z j) y| ≤ r⁻¹ ^ 3 * (M1 j + M2 j) :=
          mul_le_mul_of_nonneg_left (this.trans (by linarith)) hr3
      _ ≤ _ := by nlinarith
  · have := congrFun (spaceGrad_spaceGrad_kern (r := r) x j) y
    rw [this, abs_mul, abs_of_nonneg hr4]
    have : |scl r x (fun z => spaceGrad (fun w => spaceGrad ω0 w j) z j) y| ≤ M2 j := hM2 j _
    calc r⁻¹ ^ 4 * |scl r x (fun z => spaceGrad (fun w => spaceGrad ω0 w j) z j) y|
        ≤ r⁻¹ ^ 4 * (M1 j + M2 j) :=
          mul_le_mul_of_nonneg_left (this.trans (by linarith)) hr4
      _ ≤ _ := by nlinarith

theorem Psi_kern_bound {D : ℝ} (hD : ∀ r : ℝ, 0 < r → ∀ x y : Vec 2, ∀ j : Fin 2,
    |spaceGrad (mollK r x) y j| ≤ D * r⁻¹ ^ 3 ∧
    |spaceGrad (fun w => spaceGrad (mollK r x) w j) y j| ≤ D * r⁻¹ ^ 4)
    {b : ℝ → Vec 2 → Vec 2} {Bb : ℝ} (hB : ∀ t z, ‖b t z‖ ≤ Bb) (κ : ℝ) {r : ℝ} (hr : 0 < r)
    (x : Vec 2) (t : ℝ) (y : Vec 2) :
    |Psi b κ (mollK r x) t y| ≤ 2 * |Bb| * (D * r⁻¹ ^ 3) + 2 * (|κ| * (D * r⁻¹ ^ 4)) := by
  unfold Psi
  have hb : ∀ i : Fin 2, |b t y i| ≤ |Bb| := fun i => by
    have := (norm_le_pi_norm (b t y) i).trans (hB t y)
    simpa using this.trans (le_abs_self _)
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i : Fin 2, |b t y i * fderiv ℝ (mollK r x) y (basisVec i)|
        ≤ ∑ _i : Fin 2, |Bb| * (D * r⁻¹ ^ 3) := Finset.sum_le_sum fun i _ => by
          rw [abs_mul]
          exact mul_le_mul (hb i) (hD r hr x y i).1 (abs_nonneg _) (abs_nonneg _)
      _ = 2 * |Bb| * (D * r⁻¹ ^ 3) := by simp; ring
  · rw [abs_mul]
    have hsum : |∑ i : Fin 2, fderiv ℝ (fun y => fderiv ℝ (mollK r x) y (basisVec i)) y
        (basisVec i)| ≤ 2 * (D * r⁻¹ ^ 4) :=
      calc _ ≤ ∑ i : Fin 2, |fderiv ℝ (fun y => fderiv ℝ (mollK r x) y (basisVec i)) y
            (basisVec i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin 2, (D * r⁻¹ ^ 4) := Finset.sum_le_sum fun i _ => (hD r hr x y i).2
        _ = 2 * (D * r⁻¹ ^ 4) := by simp
    exact mul_le_mul_of_nonneg_left hsum (abs_nonneg _) |>.trans (le_of_eq (by ring))

end AVRegularity.Applications.LimitsLocal
end
end
end
