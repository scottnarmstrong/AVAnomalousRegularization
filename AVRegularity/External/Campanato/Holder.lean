-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.External.Campanato.Representative
import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

noncomputable section

open Filter Homogenization MeasureTheory Set
open scoped ENNReal Topology

namespace AVRegularity.External.Campanato

private theorem vecNormSq_shift_bound {x y : Vec 2} {d : ℝ}
    (hd : 0 ≤ d) (hxy : dist x y ≤ d) : vecNormSq (x - y) ≤ 2 * d ^ 2 := by
  have hcoords : ∀ i : Fin 2, |x i - y i| ≤ d := by
    have h := (dist_pi_le_iff hd).mp hxy
    intro i
    have hi := h i
    rw [Real.dist_eq] at hi
    exact hi
  have hsquares : ∀ i : Fin 2, (x i - y i) ^ 2 ≤ d ^ 2 := by
    intro i
    have hi := hcoords i
    rcases abs_le.mp hi with ⟨hlo, hhi⟩
    nlinarith [sq_nonneg (d - (x i - y i)), sq_nonneg (d + (x i - y i))]
  have hnorm : vecNormSq (x - y) = ∑ i : Fin 2, (x i - y i) ^ 2 := by
    simp [vecNormSq, vecDot, pow_two]
  rw [hnorm]
  calc
    (∑ i : Fin 2, (x i - y i) ^ 2) ≤ ∑ i : Fin 2, d ^ 2 :=
      Finset.sum_le_sum fun i _ => hsquares i
    _ = 2 * d ^ 2 := by simp

theorem cylinder_subset_later_comparable
    {z w : ℝ × Vec 2} {s d R : ℝ}
    (hs : 0 < s) (hd : 0 < d) (hsd : s ≤ d) (hR : 3 * d ≤ R)
    (ht : z.1 ≤ w.1) (hpara : parabolicDist z w ≤ d) :
    cylinder z s ⊆ cylinder w R := by
  intro y hy
  rcases hy with ⟨hyt, hyx⟩
  change y.1 ∈ Set.Ioc (w.1 - R ^ 2) w.1 ∧
    vecNormSq (y.2 - w.2) < R ^ 2
  refine ⟨?_, ?_⟩
  · change w.1 - R ^ 2 < y.1 ∧ y.1 ≤ w.1
    have hparts : Real.sqrt |z.1 - w.1| ≤ d ∧ dist z.2 w.2 ≤ d := by
      simpa [parabolicDist, max_le_iff] using hpara
    have htime : |z.1 - w.1| ≤ d ^ 2 :=
      (Real.sqrt_le_iff.mp hparts.1).2
    constructor
    · have hlo : w.1 - d ^ 2 ≤ z.1 := by
        rw [abs_le] at htime
        linarith
      have hbase : w.1 - 2 * d ^ 2 ≤ z.1 - s ^ 2 := by
        nlinarith [sq_nonneg d, sq_nonneg s]
      have hR2 : 2 * d ^ 2 < R ^ 2 := by nlinarith [sq_nonneg (R - 3 * d)]
      linarith [hyt.1]
    · exact hyt.2.trans ht
  · have hpara' : dist z.2 w.2 ≤ d := by
      have h := hpara
      change max (Real.sqrt |z.1 - w.1|) (dist z.2 w.2) ≤ d at h
      exact (max_le_iff.mp h).2
    have hshift : vecNormSq (z.2 - w.2) ≤ 2 * d ^ 2 :=
      vecNormSq_shift_bound hd.le hpara'
    have hsmall : vecNormSq (y.2 - z.2) < s ^ 2 := by simpa [euclidBall] using hyx
    have hdecomp : y.2 - w.2 = (y.2 - z.2) + (z.2 - w.2) := by
      ext i
      simp
    have hsum := vecNormSq_add_le (y.2 - z.2) (z.2 - w.2)
    have hnorm : vecNormSq (y.2 - w.2) ≤ 2 * (s ^ 2 + 2 * d ^ 2) := by
      rw [hdecomp]
      exact hsum.trans (by nlinarith [hsmall.le, hshift])
    have hR2 : 2 * (s ^ 2 + 2 * d ^ 2) < R ^ 2 := by
      nlinarith [sq_nonneg (R - 3 * d), sq_nonneg d, sq_nonneg s]
    exact lt_of_le_of_lt hnorm hR2

theorem cylinderMean_difference_of_subset
    {f : ℝ × Vec 2 → ℝ} (hf : MemLp f 2 volume)
    {z w : ℝ × Vec 2} {r R a M : ℝ}
    (hr : 0 < r) (hR : 0 < R) (hsubset : cylinder z r ⊆ cylinder w R)
    (hratio : (volume (cylinder w R)).toReal /
        (volume (cylinder z r)).toReal ≤ 5184)
    (hM : 0 ≤ M)
    (hcamp : cylinderExcess f w R ≤ M * R ^ (2 * a)) :
    |cylinderMean f z r - cylinderMean f w R| ≤
      72 * Real.sqrt M * R ^ a := by
  let c := cylinderMean f w R
  let g : ℝ × Vec 2 → ℝ := fun y => f y - c
  have hshift : cylinderMean f z r - c =
      ⨍ y in cylinder z r, g y ∂volume := by
    unfold cylinderMean g
    exact (setAverage_sub_const_of_memLp
      (cylinder_measure_ne_zero z hr) (cylinder_measure_ne_top z hr) f hf c).symm
  have hbigTop : volume (cylinder w R) < ∞ :=
    lt_of_le_of_lt (cylinder_volume_upper w hR) ENNReal.ofReal_lt_top
  let μbig : Measure (ℝ × Vec 2) := volume.restrict (cylinder w R)
  have hμbig : IsFiniteMeasure μbig := by
    refine ⟨?_⟩
    simpa [μbig] using hbigTop
  have hfBig : MemLp f 2 μbig := by
    simpa [μbig] using (MemLp.restrict (cylinder w R) hf)
  have hcBig : MemLp (fun _ : ℝ × Vec 2 => c) 2 μbig :=
    @memLp_const (ℝ × Vec 2) ℝ _ 2 μbig _ c hμbig
  have hgBig : MemLp g 2 μbig := hfBig.sub hcBig
  have hfiBig : IntegrableOn (fun y => g y ^ 2) (cylinder w R) volume := by
    change Integrable (fun y => g y ^ 2) μbig
    exact hgBig.integrable_sq
  have hrestrict : volume.restrict (cylinder z r) ≤ μbig := by
    simpa [μbig] using
      (Measure.restrict_mono_ae (μ := volume)
        (Filter.Eventually.of_forall fun y hy => hsubset hy))
  have hgSmall : MemLp g 2 (volume.restrict (cylinder z r)) :=
    MemLp.mono_measure hrestrict hgBig
  have hratio' := setAverage_le_measure_ratio hsubset
    (cylinder_measureReal_pos z hr) (cylinder_measureReal_pos w hR)
    hfiBig (fun y => sq_nonneg (g y))
  have hsmallSq : (⨍ y in cylinder z r, g y ^ 2 ∂volume) ≤
      5184 * (⨍ y in cylinder w R, g y ^ 2 ∂volume) := by
    calc
      _ ≤ ((volume (cylinder w R)).toReal / (volume (cylinder z r)).toReal) *
          (⨍ y in cylinder w R, g y ^ 2 ∂volume) := hratio'
      _ ≤ 5184 * (⨍ y in cylinder w R, g y ^ 2 ∂volume) := by
        apply mul_le_mul_of_nonneg_right hratio
        exact setAverage_nonneg_of_nonneg (fun y => sq_nonneg (g y))
  have hbig : (⨍ y in cylinder w R, g y ^ 2 ∂volume) = cylinderExcess f w R := by
    simp [g, c, cylinderExcess, cylinderMean]
  have hrpow : 0 ≤ R ^ a := Real.rpow_nonneg (le_of_lt hR) a
  have hdouble : R ^ (2 * a) = (R ^ a) ^ 2 := by
    calc
      R ^ (2 * a) = R ^ (a * 2) := by congr 1; ring
      _ = (R ^ a) ^ (2 : ℝ) := Real.rpow_mul (le_of_lt hR) a 2
      _ = (R ^ a) ^ 2 := Real.rpow_natCast (R ^ a) 2
  have hroot : Real.sqrt (⨍ y in cylinder z r, g y ^ 2 ∂volume) ≤
      72 * Real.sqrt M * R ^ a := by
    have hbound : (⨍ y in cylinder z r, g y ^ 2 ∂volume) ≤
        5184 * (M * R ^ (2 * a)) := by
      calc
        _ ≤ 5184 * (⨍ y in cylinder w R, g y ^ 2 ∂volume) := hsmallSq
        _ = 5184 * cylinderExcess f w R := by rw [hbig]
        _ ≤ 5184 * (M * R ^ (2 * a)) :=
          mul_le_mul_of_nonneg_left hcamp (by norm_num)
    have hroot' := Real.sqrt_le_sqrt hbound
    have hsqrt : Real.sqrt (5184 * (M * R ^ (2 * a))) =
        72 * Real.sqrt M * R ^ a := by
      have hmul : 5184 * (M * (R ^ a) ^ 2) = (5184 * M) * (R ^ a) ^ 2 := by ring
      rw [hdouble, hmul, Real.sqrt_mul (mul_nonneg (by norm_num) hM)]
      rw [Real.sqrt_mul (by norm_num : 0 ≤ (5184 : ℝ))]
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hrpow]
      rw [show Real.sqrt (5184 : ℝ) = 72 by
        exact (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).2 (by norm_num)]
    rw [hsqrt] at hroot'
    exact hroot'
  calc
    |cylinderMean f z r - cylinderMean f w R| =
        |⨍ y in cylinder z r, g y ∂volume| := by rw [hshift]
    _ ≤ Real.sqrt (⨍ y in cylinder z r, g y ^ 2 ∂volume) :=
      setAverage_abs_le_sqrt_setAverage_sq
        (cylinder_measure_ne_zero z hr) (cylinder_measure_ne_top z hr) g hgSmall
    _ ≤ 72 * Real.sqrt M * R ^ a := hroot

def campanatoLocalConstant (a : ℝ) : ℝ :=
  2 * campanatoConstant a + 144 * (3 : ℝ) ^ a

private theorem campanatoScale_between {d : ℝ} (hd : 0 < d) (hsmall : d < 1 / 12) :
    ∃ n : ℕ, d / 2 ≤ campanatoScale n ∧ campanatoScale n ≤ d := by
  have hex : ∃ n : ℕ, campanatoScale n ≤ d := by
    have hIio : Set.Iio d ∈ 𝓝[>] (0 : ℝ) :=
      nhdsWithin_le_nhds (Iio_mem_nhds hd)
    have hev : ∀ᶠ n : ℕ in atTop, campanatoScale n < d :=
      campanatoScale_tendsto.eventually hIio
    rcases eventually_atTop.1 hev with ⟨n, hn⟩
    exact ⟨n, (hn n le_rfl).le⟩
  have hfind : Nat.find hex ≠ 0 := by
    intro hzero
    have hle0 := Nat.find_spec hex
    rw [hzero] at hle0
    have h0 : (1 / 8 : ℝ) ≤ d := by simpa [campanatoScale] using hle0
    nlinarith
  obtain ⟨k, hfind⟩ := Nat.exists_eq_succ_of_ne_zero hfind
  have hle : campanatoScale (k + 1) ≤ d := by
    simpa [hfind] using (Nat.find_spec hex)
  have hprevIndex : k < Nat.find hex := by rw [hfind]; exact Nat.lt_succ_self k
  have hprev : ¬ campanatoScale k ≤ d := Nat.find_min hex hprevIndex
  have hprev' : d < campanatoScale k := lt_of_not_ge hprev
  have hsucc : campanatoScale (k + 1) = campanatoScale k / 2 := campanatoScale_succ k
  refine ⟨k + 1, ?_, hle⟩
  rw [hsucc]
  linarith

private theorem abs_four_sum_le (A B C D : ℝ) :
    |A + B + C + D| ≤ |A| + |B| + |C| + |D| := by
  calc
    |A + B + C + D| = |(A + B) + (C + D)| := by congr 1; ring
    _ ≤ |A + B| + |C + D| := abs_add_le _ _
    _ ≤ (|A| + |B|) + (|C| + |D|) :=
      add_le_add (abs_add_le _ _) (abs_add_le _ _)
    _ = |A| + |B| + |C| + |D| := by ring

private theorem euclidBall_segment {c x y : Vec 2} {r θ : ℝ}
    (hx : x ∈ euclidBall c r) (hy : y ∈ euclidBall c r)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (fun i => (1 - θ) * x i + θ * y i) ∈ euclidBall c r := by
  have hθ₁ : 0 ≤ 1 - θ := by linarith
  have hxnorm : vecNormSq (x - c) < r ^ 2 := hx
  have hynorm : vecNormSq (y - c) < r ^ 2 := hy
  have hform :
      (fun i => (1 - θ) * x i + θ * y i) - c =
        fun i => (1 - θ) * (x i - c i) + θ * (y i - c i) := by
    ext i
    simp
    ring
  change vecNormSq ((fun i => (1 - θ) * x i + θ * y i) - c) < r ^ 2
  rw [hform]
  have hnormsum (v : Vec 2) : vecNormSq v = ∑ i : Fin 2, v i ^ 2 := by
    simp [vecNormSq, vecDot, pow_two]
  have hcoord : ∀ i : Fin 2,
      ((1 - θ) * (x i - c i) + θ * (y i - c i)) ^ 2 ≤
        (1 - θ) * (x i - c i) ^ 2 + θ * (y i - c i) ^ 2 := by
    intro i
    have hprod := mul_nonneg (mul_nonneg hθ₁ hθ0) (sq_nonneg (x i - c i - (y i - c i)))
    nlinarith
  have hsum :
      (∑ i : Fin 2, ((1 - θ) * (x i - c i) + θ * (y i - c i)) ^ 2) ≤
        (1 - θ) * vecNormSq (x - c) + θ * vecNormSq (y - c) := by
    calc
      _ ≤ ∑ i : Fin 2,
          ((1 - θ) * (x i - c i) ^ 2 + θ * (y i - c i) ^ 2) :=
        Finset.sum_le_sum fun i _ => hcoord i
      _ = (1 - θ) * vecNormSq (x - c) + θ * vecNormSq (y - c) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        rw [hnormsum, hnormsum]
        simp only [Pi.sub_apply]
  have hmax : max (vecNormSq (x - c)) (vecNormSq (y - c)) < r ^ 2 :=
    max_lt_iff.mpr ⟨hxnorm, hynorm⟩
  have hconvex :
      (1 - θ) * vecNormSq (x - c) + θ * vecNormSq (y - c) ≤
        max (vecNormSq (x - c)) (vecNormSq (y - c)) := by
    have h1 := le_max_left (vecNormSq (x - c)) (vecNormSq (y - c))
    have h2 := le_max_right (vecNormSq (x - c)) (vecNormSq (y - c))
    have hxn : 0 ≤ vecNormSq (x - c) := by
      rw [hnormsum]
      exact Finset.sum_nonneg fun i _ => sq_nonneg ((x - c) i)
    have hyn : 0 ≤ vecNormSq (y - c) := by
      rw [hnormsum]
      exact Finset.sum_nonneg fun i _ => sq_nonneg ((y - c) i)
    have hp1 := mul_nonneg hθ₁ (sub_nonneg.mpr h1)
    have hp2 := mul_nonneg hθ0 (sub_nonneg.mpr h2)
    nlinarith
  change vecNormSq _ < r ^ 2
  rw [hnormsum]
  exact lt_of_le_of_lt (hsum.trans hconvex) hmax

def campanatoSegment (z w : ℝ × Vec 2) (θ : ℝ) : ℝ × Vec 2 :=
  ((1 - θ) * z.1 + θ * w.1, fun i => (1 - θ) * z.2 i + θ * w.2 i)

theorem halfWindow_segment {z₀ z w : ℝ × Vec 2} {θ : ℝ}
    (hz : z ∈ halfWindow z₀) (hw : w ∈ halfWindow z₀)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    campanatoSegment z w θ ∈ halfWindow z₀ := by
  rcases hz with ⟨hzt, hzx⟩
  rcases hw with ⟨hwt, hwx⟩
  change z₀.1 - (1 / 2 : ℝ) ^ 2 < z.1 ∧ z.1 ≤ z₀.1 at hzt
  change z₀.1 - (1 / 2 : ℝ) ^ 2 < w.1 ∧ w.1 ≤ z₀.1 at hwt
  change z.2 ∈ euclidBall z₀.2 (1 / 2 : ℝ) at hzx
  change w.2 ∈ euclidBall z₀.2 (1 / 2 : ℝ) at hwx
  change ((1 - θ) * z.1 + θ * w.1 ∈
      Set.Ioc (z₀.1 - (1 / 2 : ℝ) ^ 2) z₀.1) ∧
    (fun i => (1 - θ) * z.2 i + θ * w.2 i) ∈ euclidBall z₀.2 (1 / 2 : ℝ)
  constructor
  · constructor
    · rcases le_total z.1 w.1 with hzw | hwz
      · have hp := mul_nonneg hθ0 (sub_nonneg.mpr hzw)
        nlinarith
      · have hp := mul_nonneg (sub_nonneg.mpr hθ1) (sub_nonneg.mpr hwz)
        nlinarith
    · rcases le_total z.1 w.1 with hzw | hwz
      · have hp := mul_nonneg (sub_nonneg.mpr hθ1) (sub_nonneg.mpr (hzw.trans hwt.2))
        nlinarith
      · have hp := mul_nonneg hθ0 (sub_nonneg.mpr (hwz.trans hzt.2))
        nlinarith
  · exact euclidBall_segment hzx hwx hθ0 hθ1

@[simp]
theorem campanatoSegment_zero (z w : ℝ × Vec 2) : campanatoSegment z w 0 = z := by
  ext <;> simp [campanatoSegment]

@[simp]
theorem campanatoSegment_one (z w : ℝ × Vec 2) : campanatoSegment z w 1 = w := by
  ext <;> simp [campanatoSegment]

theorem parabolicDist_nonneg (z w : ℝ × Vec 2) : 0 ≤ parabolicDist z w := by
  unfold parabolicDist
  positivity

theorem parabolicDist_eq_zero_iff {z w : ℝ × Vec 2} :
    parabolicDist z w = 0 ↔ z = w := by
  constructor
  · intro h
    change max (Real.sqrt |z.1 - w.1|) (dist z.2 w.2) = 0 at h
    have ht : Real.sqrt |z.1 - w.1| = 0 := by
      apply le_antisymm
      · have hle := le_max_left (Real.sqrt |z.1 - w.1|) (dist z.2 w.2)
        change Real.sqrt |z.1 - w.1| ≤ max (Real.sqrt |z.1 - w.1|) (dist z.2 w.2) at hle
        simpa [h] using hle
      · exact Real.sqrt_nonneg _
    have hx : dist z.2 w.2 = 0 := by
      apply le_antisymm
      · have hle := le_max_right (Real.sqrt |z.1 - w.1|) (dist z.2 w.2)
        change dist z.2 w.2 ≤ max (Real.sqrt |z.1 - w.1|) (dist z.2 w.2) at hle
        simpa [h] using hle
      · exact dist_nonneg
    have htime0 : |z.1 - w.1| = 0 := by
      exact (Real.sqrt_eq_zero (abs_nonneg _)).1 ht
    have htime : z.1 = w.1 := by
      have := abs_eq_zero.mp htime0
      linarith
    exact Prod.ext htime (dist_eq_zero.mp hx)
  · rintro rfl
    exact parabolicDist_self _

private theorem abs_sub_le_sum_range (f : ℕ → ℝ) (n : ℕ) :
    |f 0 - f n| ≤ ∑ k ∈ Finset.range n, |f k - f (k + 1)| := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        |f 0 - f (n + 1)| = |(f 0 - f n) + (f n - f (n + 1))| := by congr 1; ring
        _ ≤ |f 0 - f n| + |f n - f (n + 1)| := abs_add_le _ _
        _ ≤ (∑ k ∈ Finset.range n, |f k - f (k + 1)|) + |f n - f (n + 1)| :=
          add_le_add ih le_rfl
        _ = ∑ k ∈ Finset.range (n + 1), |f k - f (k + 1)| := by
          simp [Finset.sum_range_succ]

private theorem campanatoSegment_succ_diff_time (z w : ℝ × Vec 2) (k : ℕ) :
    (campanatoSegment z w ((k + 1 : ℕ) / 64)).1 -
      (campanatoSegment z w (k / 64)).1 = (w.1 - z.1) / 64 := by
  simp [campanatoSegment, Nat.cast_add, Nat.cast_one]
  ring

private theorem campanatoSegment_succ_diff_space (z w : ℝ × Vec 2) (k : ℕ) (i : Fin 2) :
    (campanatoSegment z w ((k + 1 : ℕ) / 64)).2 i -
      (campanatoSegment z w (k / 64)).2 i = (w.2 i - z.2 i) / 64 := by
  simp [campanatoSegment, Nat.cast_add, Nat.cast_one]
  ring

private theorem halfWindow_segment_step_dist {z₀ z w : ℝ × Vec 2} {k : ℕ}
    (hz : z ∈ halfWindow z₀) (hw : w ∈ halfWindow z₀) (hk : k < 64) :
    parabolicDist (campanatoSegment z w (k / 64))
      (campanatoSegment z w ((k + 1 : ℕ) / 64)) ≤ 1 / 16 := by
  have hzk : campanatoSegment z w (k / 64) ∈ halfWindow z₀ := by
    apply halfWindow_segment hz hw
    · positivity
    · have hk' : (k : ℝ) ≤ 64 := by exact_mod_cast Nat.le_of_lt hk
      exact div_le_one_of_le₀ hk' (by norm_num)
  have hwk : campanatoSegment z w ((k + 1 : ℕ) / 64) ∈ halfWindow z₀ := by
    apply halfWindow_segment hz hw
    · positivity
    · have hk' : ((k + 1 : ℕ) : ℝ) ≤ 64 := by exact_mod_cast Nat.succ_le_of_lt hk
      exact div_le_one_of_le₀ hk' (by norm_num)
  have htimeZ : z₀.1 - (1 / 2 : ℝ) ^ 2 < z.1 ∧ z.1 ≤ z₀.1 := by
    rcases hz with ⟨ht, _⟩
    exact ht
  have htimeW : z₀.1 - (1 / 2 : ℝ) ^ 2 < w.1 ∧ w.1 ≤ z₀.1 := by
    rcases hw with ⟨ht, _⟩
    exact ht
  have htime : |z.1 - w.1| < (1 / 4 : ℝ) := by
    rw [abs_lt]
    constructor <;> nlinarith [htimeZ.1, htimeZ.2, htimeW.1, htimeW.2]
  have htimeStep :
      Real.sqrt |(campanatoSegment z w ((k + 1 : ℕ) / 64)).1 -
        (campanatoSegment z w (k / 64)).1| < 1 / 16 := by
    rw [campanatoSegment_succ_diff_time]
    apply (Real.sqrt_lt' (by norm_num)).2
    rw [abs_div]
    have : |w.1 - z.1| < (1 / 4 : ℝ) := by simpa [abs_sub_comm] using htime
    norm_num at this ⊢
    nlinarith
  have hspaceCoord : ∀ i : Fin 2, |z.2 i - w.2 i| < 1 := by
    intro i
    rcases hz with ⟨_, hzx⟩
    rcases hw with ⟨_, hwx⟩
    have hzx' : vecNormSq (z.2 - z₀.2) < (1 / 2 : ℝ) ^ 2 := by
      simpa [euclidBall] using hzx
    have hwx' : vecNormSq (w.2 - z₀.2) < (1 / 2 : ℝ) ^ 2 := by
      simpa [euclidBall] using hwx
    have hzcoord := sq_apply_le_vecNormSq (z.2 - z₀.2) i
    have hwcoord := sq_apply_le_vecNormSq (w.2 - z₀.2) i
    have hzabs : |z.2 i - z₀.2 i| < 1 / 2 :=
      abs_lt_of_sq_lt_sq (lt_of_le_of_lt hzcoord hzx') (by norm_num)
    have hwabs : |w.2 i - z₀.2 i| < 1 / 2 :=
      abs_lt_of_sq_lt_sq (lt_of_le_of_lt hwcoord hwx') (by norm_num)
    have hdiff : z.2 i - w.2 i =
        (z.2 i - z₀.2 i) + (z₀.2 i - w.2 i) := by ring
    rw [hdiff]
    calc
      |(z.2 i - z₀.2 i) + (z₀.2 i - w.2 i)| ≤
          |z.2 i - z₀.2 i| + |z₀.2 i - w.2 i| := abs_add_le _ _
      _ < 1 := by rw [abs_sub_comm (z₀.2 i) (w.2 i)]; linarith
  have hspaceStep : dist
      (campanatoSegment z w (k / 64)).2
      (campanatoSegment z w ((k + 1 : ℕ) / 64)).2 ≤ 1 / 16 := by
    apply (dist_pi_le_iff (by norm_num : 0 ≤ (1 / 16 : ℝ))).2
    intro i
    rw [Real.dist_eq, abs_sub_comm]
    rw [campanatoSegment_succ_diff_space]
    rw [abs_div, abs_of_pos (by norm_num : 0 < (64 : ℝ))]
    have hi := hspaceCoord i
    rw [abs_sub_comm] at hi
    norm_num
    linarith
  unfold parabolicDist
  exact max_le (by simpa [abs_sub_comm] using htimeStep.le) hspaceStep

private theorem campanatoSegment_index_mem {z₀ z w : ℝ × Vec 2} {k : ℕ}
    (hz : z ∈ halfWindow z₀) (hw : w ∈ halfWindow z₀) (hk : k ≤ 64) :
    campanatoSegment z w (k / 64) ∈ halfWindow z₀ := by
  apply halfWindow_segment hz hw
  · positivity
  · have hk' : (k : ℝ) ≤ 64 := by exact_mod_cast hk
    exact div_le_one_of_le₀ hk' (by norm_num)

def campanatoHolderConstant (a : ℝ) : ℝ :=
  campanatoLocalConstant a * (1 + 64 * (12 : ℝ) ^ a)

theorem campanatoLocalConstant_pos {a : ℝ} (ha : 0 < a) :
    0 < campanatoLocalConstant a := by
  unfold campanatoLocalConstant
  have h1 := campanatoConstant_pos ha
  have h2 : 0 < (3 : ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num) a
  positivity

theorem campanatoRepresentative_local_holder
    {f : ℝ × Vec 2 → ℝ} (hf : MemLp f 2 volume)
    {z₀ : ℝ × Vec 2} {a M : ℝ} (hM : 0 ≤ M) (ha : 0 < a)
    (hcamp : ∀ z ∈ halfWindow z₀, ∀ r, 0 < r → r < 1 / 4 →
      cylinderExcess f z r ≤ M * r ^ (2 * a))
    {z w : ℝ × Vec 2} (hz : z ∈ halfWindow z₀) (hw : w ∈ halfWindow z₀)
    (hd : 0 < parabolicDist z w) (hsmall : parabolicDist z w < 1 / 12) :
    |campanatoRepresentative f z - campanatoRepresentative f w| ≤
      campanatoLocalConstant a * Real.sqrt M * parabolicDist z w ^ a := by
  let d := parabolicDist z w
  obtain ⟨n, hlow, hhigh⟩ := campanatoScale_between hd hsmall
  let s := campanatoScale n
  let R := 3 * d
  have hs : 0 < s := campanatoScale_pos n
  have hsle : s ≤ d := hhigh
  have hdlow : d / 2 ≤ s := hlow
  have hR : 0 < R := by dsimp [R]; positivity
  have hRquarter : R < 1 / 4 := by dsimp [R]; nlinarith
  have hRratio : R ≤ 6 * s := by dsimp [R]; nlinarith
  have hpara : parabolicDist z w ≤ d := by rfl
  have hcampZ : ∀ r, 0 < r → r < 1 / 4 →
      cylinderExcess f z r ≤ M * r ^ (2 * a) := hcamp z hz
  have hcampW : ∀ r, 0 < r → r < 1 / 4 →
      cylinderExcess f w r ≤ M * r ^ (2 * a) := hcamp w hw
  have htime : z.1 ≤ w.1 ∨ w.1 ≤ z.1 := le_total _ _
  rcases htime with hzw | hwz
  · have hsubsetZ : cylinder z s ⊆ cylinder w R := by
      apply cylinder_subset_later_comparable hs hd hsle
      · dsimp [R]
        linarith
      · exact hzw
      · exact hpara
    have hsubsetW : cylinder w s ⊆ cylinder w R := by
      apply cylinder_subset_same_center hs
      dsimp [R]
      linarith
    have hratioZ := cylinder_volume_ratio_of_le_six (z := w) (w := z) hs hR hRratio
    have hratioW := cylinder_volume_ratio_of_le_six (z := w) (w := w) hs hR hRratio
    have hmeanZ := cylinderMean_difference_of_subset hf hs hR hsubsetZ hratioZ hM
      (hcamp w hw R hR hRquarter)
    have hmeanW := cylinderMean_difference_of_subset hf hs hR hsubsetW hratioW hM
      (hcamp w hw R hR hRquarter)
    have htailZ := campanatoRepresentative_tail hf hM hcampZ ha n
    have htailW := campanatoRepresentative_tail hf hM hcampW ha n
    have hpow : s ^ a ≤ d ^ a := Real.rpow_le_rpow (le_of_lt hs) hsle ha.le
    have hcoef : 0 ≤ campanatoConstant a * Real.sqrt M :=
      mul_nonneg (le_of_lt (campanatoConstant_pos ha)) (Real.sqrt_nonneg M)
    have htailZ' : |campanatoRepresentative f z - cylinderMean f z s| ≤
        campanatoConstant a * Real.sqrt M * d ^ a := by
      calc
        _ ≤ campanatoConstant a * Real.sqrt M * s ^ a := by
          simpa [s, campanatoAverages] using htailZ
        _ ≤ campanatoConstant a * Real.sqrt M * d ^ a :=
          mul_le_mul_of_nonneg_left hpow hcoef
    have htailW' : |cylinderMean f w s - campanatoRepresentative f w| ≤
        campanatoConstant a * Real.sqrt M * d ^ a := by
      calc
        _ = |campanatoRepresentative f w - campanatoAverages f w n| := by
          simp [s, campanatoAverages, abs_sub_comm]
        _ ≤ campanatoConstant a * Real.sqrt M * s ^ a := htailW
        _ ≤ campanatoConstant a * Real.sqrt M * d ^ a :=
          mul_le_mul_of_nonneg_left hpow hcoef
    have hRpow : R ^ a = (3 : ℝ) ^ a * d ^ a := by
      dsimp [R]
      rw [Real.mul_rpow (by norm_num) hd.le]
    have hmeanZ' : |cylinderMean f z s - cylinderMean f w R| ≤
        72 * Real.sqrt M * (3 : ℝ) ^ a * d ^ a := by
      calc
        _ ≤ 72 * Real.sqrt M * R ^ a := hmeanZ
        _ = 72 * Real.sqrt M * (3 : ℝ) ^ a * d ^ a := by rw [hRpow]; ring
    have hmeanW' : |cylinderMean f w R - cylinderMean f w s| ≤
        72 * Real.sqrt M * (3 : ℝ) ^ a * d ^ a := by
      calc
        _ = |cylinderMean f w s - cylinderMean f w R| := abs_sub_comm _ _
        _ ≤ 72 * Real.sqrt M * R ^ a := hmeanW
        _ = 72 * Real.sqrt M * (3 : ℝ) ^ a * d ^ a := by rw [hRpow]; ring
    have hdecomp : campanatoRepresentative f z - campanatoRepresentative f w =
        (campanatoRepresentative f z - cylinderMean f z s) +
          (cylinderMean f z s - cylinderMean f w R) +
          (cylinderMean f w R - cylinderMean f w s) +
          (cylinderMean f w s - campanatoRepresentative f w) := by ring
    rw [hdecomp]
    calc
      |(campanatoRepresentative f z - cylinderMean f z s) +
          (cylinderMean f z s - cylinderMean f w R) +
          (cylinderMean f w R - cylinderMean f w s) +
          (cylinderMean f w s - campanatoRepresentative f w)| ≤
          |campanatoRepresentative f z - cylinderMean f z s| +
            |cylinderMean f z s - cylinderMean f w R| +
            |cylinderMean f w R - cylinderMean f w s| +
            |cylinderMean f w s - campanatoRepresentative f w| :=
        abs_four_sum_le _ _ _ _
      _ ≤ campanatoConstant a * Real.sqrt M * d ^ a +
            72 * Real.sqrt M * (3 : ℝ) ^ a * d ^ a +
            72 * Real.sqrt M * (3 : ℝ) ^ a * d ^ a +
            campanatoConstant a * Real.sqrt M * d ^ a := by
        linarith [htailZ', hmeanZ', hmeanW', htailW']
      _ = campanatoLocalConstant a * Real.sqrt M * d ^ a := by
        unfold campanatoLocalConstant
        ring
  · have hsubsetW : cylinder w s ⊆ cylinder z R := by
      apply cylinder_subset_later_comparable hs hd hsle
      · dsimp [R]
        linarith
      · exact hwz
      · rw [parabolicDist_comm]
    have hsubsetZ : cylinder z s ⊆ cylinder z R := by
      apply cylinder_subset_same_center hs
      dsimp [R]
      linarith
    have hratioW := cylinder_volume_ratio_of_le_six (z := z) (w := w) hs hR hRratio
    have hratioZ := cylinder_volume_ratio_of_le_six (z := z) (w := z) hs hR hRratio
    have hmeanW := cylinderMean_difference_of_subset hf hs hR hsubsetW hratioW hM
      (hcamp z hz R hR hRquarter)
    have hmeanZ := cylinderMean_difference_of_subset hf hs hR hsubsetZ hratioZ hM
      (hcamp z hz R hR hRquarter)
    have htailZ := campanatoRepresentative_tail hf hM hcampZ ha n
    have htailW := campanatoRepresentative_tail hf hM hcampW ha n
    have hpow : s ^ a ≤ d ^ a := Real.rpow_le_rpow (le_of_lt hs) hsle ha.le
    have hcoef : 0 ≤ campanatoConstant a * Real.sqrt M :=
      mul_nonneg (le_of_lt (campanatoConstant_pos ha)) (Real.sqrt_nonneg M)
    have htailZ' : |campanatoRepresentative f z - cylinderMean f z s| ≤
        campanatoConstant a * Real.sqrt M * d ^ a := by
      calc
        _ ≤ campanatoConstant a * Real.sqrt M * s ^ a := by
          simpa [s, campanatoAverages] using htailZ
        _ ≤ campanatoConstant a * Real.sqrt M * d ^ a :=
          mul_le_mul_of_nonneg_left hpow hcoef
    have htailW' : |cylinderMean f w s - campanatoRepresentative f w| ≤
        campanatoConstant a * Real.sqrt M * d ^ a := by
      calc
        _ = |campanatoRepresentative f w - campanatoAverages f w n| := by
          simp [s, campanatoAverages, abs_sub_comm]
        _ ≤ campanatoConstant a * Real.sqrt M * s ^ a := htailW
        _ ≤ campanatoConstant a * Real.sqrt M * d ^ a :=
          mul_le_mul_of_nonneg_left hpow hcoef
    have hRpow : R ^ a = (3 : ℝ) ^ a * d ^ a := by
      dsimp [R]
      rw [Real.mul_rpow (by norm_num) hd.le]
    have hmeanW' : |cylinderMean f z R - cylinderMean f w s| ≤
        72 * Real.sqrt M * (3 : ℝ) ^ a * d ^ a := by
      calc
        _ = |cylinderMean f w s - cylinderMean f z R| := abs_sub_comm _ _
        _ ≤ 72 * Real.sqrt M * R ^ a := hmeanW
        _ = 72 * Real.sqrt M * (3 : ℝ) ^ a * d ^ a := by rw [hRpow]; ring
    have hmeanZ' : |cylinderMean f z s - cylinderMean f z R| ≤
        72 * Real.sqrt M * (3 : ℝ) ^ a * d ^ a := by
      calc
        _ ≤ 72 * Real.sqrt M * R ^ a := hmeanZ
        _ = 72 * Real.sqrt M * (3 : ℝ) ^ a * d ^ a := by rw [hRpow]; ring
    have hdecomp : campanatoRepresentative f z - campanatoRepresentative f w =
        (campanatoRepresentative f z - cylinderMean f z s) +
          (cylinderMean f z s - cylinderMean f z R) +
          (cylinderMean f z R - cylinderMean f w s) +
          (cylinderMean f w s - campanatoRepresentative f w) := by ring
    rw [hdecomp]
    calc
      |(campanatoRepresentative f z - cylinderMean f z s) +
          (cylinderMean f z s - cylinderMean f z R) +
          (cylinderMean f z R - cylinderMean f w s) +
          (cylinderMean f w s - campanatoRepresentative f w)| ≤
          |campanatoRepresentative f z - cylinderMean f z s| +
            |cylinderMean f z s - cylinderMean f z R| +
            |cylinderMean f z R - cylinderMean f w s| +
            |cylinderMean f w s - campanatoRepresentative f w| :=
        abs_four_sum_le _ _ _ _
      _ ≤ campanatoConstant a * Real.sqrt M * d ^ a +
            72 * Real.sqrt M * (3 : ℝ) ^ a * d ^ a +
            72 * Real.sqrt M * (3 : ℝ) ^ a * d ^ a +
            campanatoConstant a * Real.sqrt M * d ^ a := by
        linarith [htailZ', hmeanZ', hmeanW', htailW']
      _ = campanatoLocalConstant a * Real.sqrt M * d ^ a := by
        unfold campanatoLocalConstant
        ring

theorem campanatoRepresentative_holder
    {f : ℝ × Vec 2 → ℝ} (hf : MemLp f 2 volume)
    {z₀ : ℝ × Vec 2} {a M : ℝ} (hM : 0 ≤ M) (ha : 0 < a)
    (hcamp : ∀ z ∈ halfWindow z₀, ∀ r, 0 < r → r < 1 / 4 →
      cylinderExcess f z r ≤ M * r ^ (2 * a))
    {z w : ℝ × Vec 2} (hz : z ∈ halfWindow z₀) (hw : w ∈ halfWindow z₀) :
    |campanatoRepresentative f z - campanatoRepresentative f w| ≤
      campanatoHolderConstant a * Real.sqrt M * parabolicDist z w ^ a := by
  let d := parabolicDist z w
  have hdnonneg : 0 ≤ d := parabolicDist_nonneg z w
  by_cases hd0 : d = 0
  · have hzw : z = w := (parabolicDist_eq_zero_iff).mp hd0
    subst w
    rw [parabolicDist_self, Real.zero_rpow (ne_of_gt ha)]
    simp
  by_cases hdsmall : d < 1 / 12
  · have hdpos : 0 < d := lt_of_le_of_ne hdnonneg (Ne.symm hd0)
    have hlocal := campanatoRepresentative_local_holder hf hM ha hcamp hz hw hdpos hdsmall
    have hcoef : campanatoLocalConstant a ≤ campanatoHolderConstant a := by
      unfold campanatoHolderConstant
      have hpos := campanatoLocalConstant_pos ha
      have h12 : 0 ≤ (12 : ℝ) ^ a := Real.rpow_nonneg (by norm_num) a
      have hfactor : 1 ≤ 1 + 64 * (12 : ℝ) ^ a := by nlinarith
      nlinarith
    have hnonneg : 0 ≤ Real.sqrt M * d ^ a :=
      mul_nonneg (Real.sqrt_nonneg M) (Real.rpow_nonneg hdnonneg a)
    calc
      |campanatoRepresentative f z - campanatoRepresentative f w| ≤
          campanatoLocalConstant a * Real.sqrt M * d ^ a := hlocal
      _ = campanatoLocalConstant a * (Real.sqrt M * d ^ a) := by ring
      _ ≤ campanatoHolderConstant a * (Real.sqrt M * d ^ a) :=
        mul_le_mul_of_nonneg_right hcoef hnonneg
      _ = campanatoHolderConstant a * Real.sqrt M * d ^ a := by ring
  · have hdlarge : 1 / 12 ≤ d := le_of_not_gt hdsmall
    let g := fun k : ℕ =>
      campanatoRepresentative f (campanatoSegment z w (k / 64))
    have hstep : ∀ k ∈ Finset.range 64,
        |g k - g (k + 1)| ≤ campanatoLocalConstant a * Real.sqrt M := by
      intro k hk
      have hklt : k < 64 := Finset.mem_range.mp hk
      have hpk : campanatoSegment z w (k / 64) ∈ halfWindow z₀ :=
        campanatoSegment_index_mem hz hw (Nat.le_of_lt hklt)
      have hpn : campanatoSegment z w ((k + 1 : ℕ) / 64) ∈ halfWindow z₀ := by
        apply campanatoSegment_index_mem hz hw
        exact Nat.succ_le_of_lt hklt
      have hdist := halfWindow_segment_step_dist hz hw hklt
      have hdistnonneg := parabolicDist_nonneg
        (campanatoSegment z w (k / 64))
        (campanatoSegment z w ((k + 1 : ℕ) / 64))
      by_cases hpos : 0 < parabolicDist
          (campanatoSegment z w (k / 64))
          (campanatoSegment z w ((k + 1 : ℕ) / 64))
      · have hlocal := campanatoRepresentative_local_holder hf hM ha hcamp
          hpk hpn hpos (lt_of_le_of_lt hdist (by norm_num : (1 / 16 : ℝ) < 1 / 12))
        have hrpow := Real.rpow_le_rpow hdistnonneg hdist (le_of_lt ha)
        have hsmallpow : (1 / 16 : ℝ) ^ a ≤ 1 := by
          calc
            (1 / 16 : ℝ) ^ a ≤ (1 : ℝ) ^ a :=
              Real.rpow_le_rpow (by norm_num) (by norm_num) ha.le
            _ = 1 := by simp
        have hpow : parabolicDist
            (campanatoSegment z w (k / 64))
            (campanatoSegment z w ((k + 1 : ℕ) / 64)) ^ a ≤ 1 := hrpow.trans hsmallpow
        have hcoef : 0 ≤ campanatoLocalConstant a * Real.sqrt M :=
          mul_nonneg (campanatoLocalConstant_pos ha).le (Real.sqrt_nonneg M)
        calc
          |g k - g (k + 1)| ≤ campanatoLocalConstant a * Real.sqrt M *
              parabolicDist (campanatoSegment z w (k / 64))
                (campanatoSegment z w ((k + 1 : ℕ) / 64)) ^ a := hlocal
          _ ≤ campanatoLocalConstant a * Real.sqrt M := by
            simpa using mul_le_mul_of_nonneg_left hpow hcoef
      · have hzero : parabolicDist
            (campanatoSegment z w (k / 64))
            (campanatoSegment z w ((k + 1 : ℕ) / 64)) = 0 :=
          le_antisymm (le_of_not_gt hpos) hdistnonneg
        have heq := (parabolicDist_eq_zero_iff).mp hzero
        have hc := mul_nonneg (campanatoLocalConstant_pos ha).le (Real.sqrt_nonneg M)
        simpa [g, heq] using hc
    have htel := abs_sub_le_sum_range g 64
    have hsumBound :
        (∑ k ∈ Finset.range 64, |g k - g (k + 1)|) ≤
          ∑ k ∈ Finset.range 64, campanatoLocalConstant a * Real.sqrt M :=
      Finset.sum_le_sum fun k hk => hstep k hk
    have hchain : |campanatoRepresentative f z - campanatoRepresentative f w| ≤
        64 * campanatoLocalConstant a * Real.sqrt M := by
      have htel' : |campanatoRepresentative f z - campanatoRepresentative f w| ≤
          ∑ k ∈ Finset.range 64, |g k - g (k + 1)| := by
        simpa [g, campanatoSegment_zero, campanatoSegment_one] using htel
      calc
        _ ≤ ∑ k ∈ Finset.range 64, |g k - g (k + 1)| := htel'
        _ ≤ ∑ k ∈ Finset.range 64, campanatoLocalConstant a * Real.sqrt M := hsumBound
        _ = 64 * campanatoLocalConstant a * Real.sqrt M := by simp [mul_assoc]
    have hpow12 : 1 ≤ (12 : ℝ) ^ a * d ^ a := by
      have h12d : 1 ≤ 12 * d := by dsimp [d] at hdlarge ⊢; nlinarith
      have hpow := Real.rpow_le_rpow (by norm_num) h12d ha.le
      have hmul : (12 * d) ^ a = (12 : ℝ) ^ a * d ^ a :=
        Real.mul_rpow (by norm_num : 0 ≤ (12 : ℝ)) hdnonneg
      rw [hmul] at hpow
      simpa using hpow
    have hfactor : 64 ≤ (1 + 64 * (12 : ℝ) ^ a) * d ^ a := by
      have hdpow : 0 ≤ d ^ a := Real.rpow_nonneg hdnonneg a
      calc
        64 = 64 * 1 := by ring
        _ ≤ 64 * ((12 : ℝ) ^ a * d ^ a) := by gcongr
        _ ≤ (1 + 64 * (12 : ℝ) ^ a) * d ^ a := by nlinarith
    have hcoef : 0 ≤ campanatoLocalConstant a * Real.sqrt M :=
      mul_nonneg (campanatoLocalConstant_pos ha).le (Real.sqrt_nonneg M)
    have hlargeBound : 64 * campanatoLocalConstant a * Real.sqrt M ≤
        campanatoHolderConstant a * Real.sqrt M * d ^ a := by
      rw [campanatoHolderConstant]
      calc
        64 * campanatoLocalConstant a * Real.sqrt M =
            (campanatoLocalConstant a * Real.sqrt M) * 64 := by ring
        _ ≤ (campanatoLocalConstant a * Real.sqrt M) *
            ((1 + 64 * (12 : ℝ) ^ a) * d ^ a) :=
          mul_le_mul_of_nonneg_left hfactor hcoef
        _ = campanatoLocalConstant a * (1 + 64 * (12 : ℝ) ^ a) *
            Real.sqrt M * d ^ a := by ring
    exact hchain.trans hlargeBound

private theorem continuous_parabolicDist_left (z : ℝ × Vec 2) :
    Continuous (fun w => parabolicDist z w) := by
  unfold parabolicDist
  fun_prop

theorem campanatoRepresentative_continuousOn
    {f : ℝ × Vec 2 → ℝ} (hf : MemLp f 2 volume)
    {z₀ : ℝ × Vec 2} {a M : ℝ} (hM : 0 ≤ M) (ha : 0 < a)
    (hcamp : ∀ z ∈ halfWindow z₀, ∀ r, 0 < r → r < 1 / 4 →
      cylinderExcess f z r ≤ M * r ^ (2 * a)) :
    ContinuousOn (campanatoRepresentative f) (halfWindow z₀) := by
  change ∀ z, z ∈ halfWindow z₀ →
    Tendsto (campanatoRepresentative f) (𝓝[halfWindow z₀] z)
      (𝓝 (campanatoRepresentative f z))
  intro z hz
  have hmod : Tendsto (fun w => parabolicDist z w ^ a) (𝓝 z) (𝓝 0) := by
    have hcontRpow : ContinuousAt (fun x : ℝ => x ^ a) (parabolicDist z z) :=
      (Real.continuous_rpow_const ha.le).continuousAt
    have hcontDist : ContinuousAt (fun w => parabolicDist z w) z :=
      (continuous_parabolicDist_left z).continuousAt
    have hcont := hcontRpow.comp hcontDist
    convert hcont.tendsto using 1
    · funext w
      rfl
    · simp [parabolicDist_self, Real.zero_rpow (ne_of_gt ha)]
  have hmodWithin : Tendsto (fun w => parabolicDist z w ^ a)
      (𝓝[halfWindow z₀] z) (𝓝 0) := hmod.mono_left nhdsWithin_le_nhds
  have hbound : ∀ᶠ w in 𝓝[halfWindow z₀] z,
      |campanatoRepresentative f z - campanatoRepresentative f w| ≤
        campanatoHolderConstant a * Real.sqrt M * parabolicDist z w ^ a := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact campanatoRepresentative_holder hf hM ha hcamp hz hw
  have hupper : Tendsto
      (fun w => campanatoHolderConstant a * Real.sqrt M * parabolicDist z w ^ a)
      (𝓝[halfWindow z₀] z) (𝓝 0) := by
    convert hmodWithin.const_mul (campanatoHolderConstant a * Real.sqrt M) using 1
    simp [mul_comm]
  have habs : Tendsto (fun w =>
      |campanatoRepresentative f z - campanatoRepresentative f w|)
      (𝓝[halfWindow z₀] z) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _)
      hbound hupper
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa [Real.dist_eq, abs_sub_comm] using habs

def parabolicHolderDistance (z w : ℝ × Vec 2) : ℝ :=
  Real.sqrt (vecNormSq (z.2 - w.2)) + Real.sqrt |z.1 - w.1|

private theorem vecDist_le_sqrt_vecNormSq (x y : Vec 2) :
    dist x y ≤ Real.sqrt (vecNormSq (x - y)) := by
  have hnorm0 : 0 ≤ vecNormSq (x - y) := by
    have hnorm : vecNormSq (x - y) = ∑ i : Fin 2, (x i - y i) ^ 2 := by
      simp [vecNormSq, vecDot, pow_two]
    rw [hnorm]
    exact Finset.sum_nonneg fun i _ => sq_nonneg (x i - y i)
  apply (dist_pi_le_iff (Real.sqrt_nonneg _)).2
  intro i
  rw [Real.dist_eq]
  have hcoord := sq_apply_le_vecNormSq (x - y) i
  have hsquares : |x i - y i| ^ 2 ≤ (Real.sqrt (vecNormSq (x - y))) ^ 2 := by
    rw [Real.sq_sqrt hnorm0, sq_abs]
    exact hcoord
  exact (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).1 hsquares

theorem parabolicDist_le_parabolicHolderDistance (z w : ℝ × Vec 2) :
    parabolicDist z w ≤ parabolicHolderDistance z w := by
  unfold parabolicDist parabolicHolderDistance
  apply max_le
  · exact le_add_of_nonneg_left (Real.sqrt_nonneg _)
  · exact (vecDist_le_sqrt_vecNormSq z.2 w.2).trans
      (le_add_of_nonneg_right (Real.sqrt_nonneg _))

theorem campanatoRepresentative_holder_euclidean
    {f : ℝ × Vec 2 → ℝ} (hf : MemLp f 2 volume)
    {z₀ : ℝ × Vec 2} {a M : ℝ} (hM : 0 ≤ M) (ha : 0 < a)
    (hcamp : ∀ z ∈ halfWindow z₀, ∀ r, 0 < r → r < 1 / 4 →
      cylinderExcess f z r ≤ M * r ^ (2 * a))
    {z w : ℝ × Vec 2} (hz : z ∈ halfWindow z₀) (hw : w ∈ halfWindow z₀) :
    |campanatoRepresentative f z - campanatoRepresentative f w| ≤
      campanatoHolderConstant a * Real.sqrt M * parabolicHolderDistance z w ^ a := by
  have hpara := parabolicDist_le_parabolicHolderDistance z w
  have hpow := Real.rpow_le_rpow (parabolicDist_nonneg z w) hpara (le_of_lt ha)
  have hcoef : 0 ≤ campanatoHolderConstant a * Real.sqrt M := by
    unfold campanatoHolderConstant
    have hlocal := campanatoLocalConstant_pos ha
    have h12 : 0 ≤ (12 : ℝ) ^ a := Real.rpow_nonneg (by norm_num) a
    positivity
  calc
    |campanatoRepresentative f z - campanatoRepresentative f w| ≤
        campanatoHolderConstant a * Real.sqrt M * parabolicDist z w ^ a :=
      campanatoRepresentative_holder hf hM ha hcamp hz hw
    _ ≤ campanatoHolderConstant a * Real.sqrt M * parabolicHolderDistance z w ^ a :=
      mul_le_mul_of_nonneg_left hpow hcoef

private theorem cylinderExcess_nonneg (f : ℝ × Vec 2 → ℝ) (z : ℝ × Vec 2) (r : ℝ) :
    0 ≤ cylinderExcess f z r :=
  setAverage_nonneg_of_nonneg fun y => sq_nonneg (f y - cylinderMean f z r)

theorem campanato_morrey_characterization
    {u : ℝ × Vec 2 → ℝ} {z₀ : ℝ × Vec 2} {a M : ℝ}
    (hu : MemLp u 2 (volume.restrict (window z₀)))
    (ha : 0 < a) (_ha1 : a < 1)
    (hcamp : ∀ z ∈ halfWindow z₀, ∀ r, 0 < r → r < 1 / 4 →
      cylinderExcess u z r ≤ M * r ^ (2 * a)) :
    ContinuousOn (campanatoRepresentative ((window z₀).indicator u)) (halfWindow z₀) ∧
      (∀ᵐ z ∂(volume.restrict (halfWindow z₀)),
        campanatoRepresentative ((window z₀).indicator u) z = u z) ∧
      (∀ z ∈ halfWindow z₀, ∀ w ∈ halfWindow z₀,
        |campanatoRepresentative ((window z₀).indicator u) z -
          campanatoRepresentative ((window z₀).indicator u) w| ≤
          campanatoHolderConstant a * Real.sqrt M * parabolicHolderDistance z w ^ a) := by
  let f : ℝ × Vec 2 → ℝ := (window z₀).indicator u
  have hf : MemLp f 2 volume := by
    rw [memLp_indicator_iff_restrict (window_measurable z₀)]
    exact hu
  have hcamp' : ∀ z ∈ halfWindow z₀, ∀ r, 0 < r → r < 1 / 4 →
      cylinderExcess f z r ≤ M * r ^ (2 * a) := by
    intro z hz r hr hrr
    rw [cylinderExcess_indicator_eq z₀ z u (cylinder_subset_window z₀ z hz hr hrr)]
    exact hcamp z hz r hr hrr
  have hz₀ : z₀ ∈ halfWindow z₀ := by
    simp [halfWindow, cylinder, euclidBall, vecNormSq, vecDot]
  have hr0 : 0 < (1 / 8 : ℝ) := by norm_num
  have hrsmall : (1 / 8 : ℝ) < 1 / 4 := by norm_num
  have hM : 0 ≤ M := by
    by_contra hM
    have hMneg : M < 0 := lt_of_not_ge hM
    have hrpow : 0 < (1 / 8 : ℝ) ^ (2 * a) :=
      Real.rpow_pos_of_pos hr0 (2 * a)
    have hnonneg := cylinderExcess_nonneg u z₀ (1 / 8)
    have hupper := hcamp z₀ hz₀ (1 / 8) hr0 hrsmall
    have hneg : M * (1 / 8 : ℝ) ^ (2 * a) < 0 := mul_neg_of_neg_of_pos hMneg hrpow
    linarith
  refine ⟨campanatoRepresentative_continuousOn hf hM ha hcamp', ?_, ?_⟩
  · have haeeq := campanatoRepresentative_ae_eq hf hM ha hcamp'
    filter_upwards [haeeq, ae_restrict_mem (halfWindow_measurable z₀)] with z hrep hz
    have hzw : z ∈ window z₀ := (halfWindow_subset_window z₀) hz
    simpa [f, Set.indicator_of_mem hzw] using hrep
  · intro z hz w hw
    exact campanatoRepresentative_holder_euclidean hf hM ha hcamp' hz hw

end AVRegularity.External.Campanato
