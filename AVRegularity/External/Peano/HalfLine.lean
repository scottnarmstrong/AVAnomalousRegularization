-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Homogenization.Ambient.Basic
import Mathlib.Topology.MetricSpace.UniformConvergence
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Topology.UniformSpace.Ascoli

@[expose] public section
noncomputable section

section
open Filter Finset Homogenization Topology
open scoped BigOperators
namespace AVRegularity.External

/-! Backward Euler polygons for a continuous vector field. -/

/-- Clamp a backward-time parameter to a finite interval. -/
def peanoClamp (T u : ℝ) : ℝ := min T (max 0 u)

private theorem peanoClamp_lipschitz (T : ℝ) : LipschitzWith 1 (peanoClamp T) := by
  change LipschitzWith 1 (fun u : ℝ => min T (max 0 u))
  simpa [min_comm] using (LipschitzWith.id.const_max 0).min_const T

private theorem peanoClamp_mem {T : ℝ} (hT : 0 ≤ T) (u : ℝ) :
    peanoClamp T u ∈ Set.Icc 0 T := by
  constructor
  · exact le_min hT (le_max_left 0 u)
  · exact min_le_left _ _

private theorem peanoClamp_idem {T : ℝ} (hT : 0 ≤ T) (u : ℝ) :
    peanoClamp T (peanoClamp T u) = peanoClamp T u := by
  have hu := peanoClamp_mem hT u
  change min T (max 0 (min T (max 0 u))) = min T (max 0 u)
  change 0 ≤ min T (max 0 u) ∧ min T (max 0 u) ≤ T at hu
  rw [max_eq_right hu.1]
  rw [← min_assoc, min_self]

/-- The amount of the `k`th Euler segment traversed by time `u`. -/
def peanoEulerWeight (h u : ℝ) (k : ℕ) : ℝ := min h (max 0 (u - (k : ℝ) * h))

/-- Values of the backward explicit Euler scheme at its mesh points. -/
def peanoEulerNode (b : ℝ → Vec 2 → Vec 2) (t : ℝ) (x : Vec 2) (h : ℝ) :
    ℕ → Vec 2
  | 0 => x
  | k + 1 => peanoEulerNode b t x h k -
      h • b (t - (k : ℝ) * h) (peanoEulerNode b t x h k)

/-- The continuous, piecewise affine backward Euler polygon, defined on all real `u` by
constant extension outside `[0,T]`. -/
def peanoEulerPolygon (b : ℝ → Vec 2 → Vec 2) (t : ℝ) (x : Vec 2)
    (h T : ℝ) (N : ℕ) (u : ℝ) : Vec 2 :=
  x - ∑ k ∈ Finset.range N,
    peanoEulerWeight h (peanoClamp T u) k •
      b (t - (k : ℝ) * h) (peanoEulerNode b t x h k)

private theorem peanoEulerWeight_eq_min_sub {h u : ℝ} (hh : 0 ≤ h)
    (k : ℕ) :
    peanoEulerWeight h u k =
      min u ((k + 1 : ℕ) * h) - min u (k * h) := by
  have hk : 0 ≤ (k : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hh
  have hk' : (k : ℝ) * h ≤ (k + 1) * h := by
    have : (k : ℝ) ≤ (k + 1 : ℝ) := by exact_mod_cast Nat.le_succ k
    exact mul_le_mul_of_nonneg_right this hh
  by_cases h₁ : u ≤ (k : ℝ) * h
  · simp [peanoEulerWeight, max_eq_left (sub_nonpos.mpr h₁),
      min_eq_left (le_trans h₁ hk'), min_eq_left h₁, min_eq_right hh]
  · have h₁' : (k : ℝ) * h ≤ u := le_of_not_ge h₁
    by_cases h₂ : u ≤ (k + 1) * h
    · have hsub : u - (k : ℝ) * h ≤ h := by linarith
      simp [peanoEulerWeight, max_eq_right (sub_nonneg.mpr h₁'),
        min_eq_left h₂, min_eq_right h₁', min_eq_right hsub]
    · have h₂' : (k + 1 : ℝ) * h ≤ u := le_of_not_ge h₂
      have hsub : h ≤ u - (k : ℝ) * h := by linarith
      simp [peanoEulerWeight, max_eq_right (sub_nonneg.mpr h₁'),
        min_eq_right h₂', min_eq_right h₁', min_eq_left hsub]
      ring

private theorem peanoEulerWeight_sum {h u : ℝ} (hh : 0 ≤ h) (hu : 0 ≤ u)
    (N : ℕ) :
    (∑ k ∈ Finset.range N, peanoEulerWeight h u k) = min u (N * h) := by
  induction N with
  | zero =>
    rw [Finset.sum_range_zero, Nat.cast_zero, zero_mul, min_eq_right hu]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, peanoEulerWeight_eq_min_sub hh]
    have hcast : ((N + 1 : ℕ) : ℝ) * h = N * h + h := by push_cast; ring
    rw [hcast]
    ring

private theorem peanoEulerWeight_at_grid_left {h : ℝ} (hh : 0 ≤ h) {i k : ℕ}
    (hik : i < k) : peanoEulerWeight h ((k : ℝ) * h) i = h := by
  have hik' : (i : ℝ) + 1 ≤ k := by exact_mod_cast Nat.succ_le_of_lt hik
  have hsub : h ≤ (k : ℝ) * h - (i : ℝ) * h := by
    have hmul := mul_le_mul_of_nonneg_right hik' hh
    nlinarith
  unfold peanoEulerWeight
  rw [max_eq_right (le_trans hh hsub)]
  exact min_eq_left hsub

private theorem peanoEulerWeight_at_grid_right {h : ℝ} (hh : 0 ≤ h) {i k : ℕ}
    (hik : k ≤ i) : peanoEulerWeight h ((k : ℝ) * h) i = 0 := by
  have hki : (k : ℝ) * h ≤ (i : ℝ) * h :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hik) hh
  unfold peanoEulerWeight
  rw [max_eq_left (sub_nonpos.mpr (by linarith))]
  exact min_eq_right hh

private theorem peanoEulerNode_eq_sum (b : ℝ → Vec 2 → Vec 2) (t : ℝ) (x : Vec 2)
    (h : ℝ) (k : ℕ) :
    peanoEulerNode b t x h k = x - ∑ i ∈ Finset.range k,
      h • b (t - (i : ℝ) * h) (peanoEulerNode b t x h i) := by
  induction k with
  | zero => simp [peanoEulerNode]
  | succ k ih =>
    change peanoEulerNode b t x h k -
      h • b (t - (k : ℝ) * h) (peanoEulerNode b t x h k) =
      x - ∑ i ∈ Finset.range (k + 1),
        h • b (t - (i : ℝ) * h) (peanoEulerNode b t x h i)
    rw [Finset.sum_range_succ]
    calc
      _ = (x - ∑ i ∈ Finset.range k,
          h • b (t - (i : ℝ) * h) (peanoEulerNode b t x h i)) -
          h • b (t - (k : ℝ) * h) (peanoEulerNode b t x h k) := by rw [ih]
      _ = x - ((∑ i ∈ Finset.range k,
          h • b (t - (i : ℝ) * h) (peanoEulerNode b t x h i)) +
          h • b (t - (k : ℝ) * h) (peanoEulerNode b t x h k)) := by abel

theorem peanoEulerPolygon_at_grid
    (b : ℝ → Vec 2 → Vec 2) (t : ℝ) (x : Vec 2)
    (h T : ℝ) (N k : ℕ) (hh : 0 ≤ h) (hT : T = N * h) (hk : k ≤ N) :
    peanoEulerPolygon b t x h T N ((k : ℝ) * h) = peanoEulerNode b t x h k := by
  have hkh : 0 ≤ (k : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hh
  have hknh : (k : ℝ) * h ≤ N * h :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hh
  have hclamp : peanoClamp T ((k : ℝ) * h) = (k : ℝ) * h := by
    simp [peanoClamp, max_eq_right hkh, min_eq_right (hT ▸ hknh)]
  rw [peanoEulerPolygon, hclamp, ← Nat.add_sub_of_le hk, Finset.sum_range_add]
  have htail : (∑ i ∈ Finset.range (N - k),
      peanoEulerWeight h ((k : ℝ) * h) (k + i) •
        b (t - ((k + i : ℕ) : ℝ) * h)
          (peanoEulerNode b t x h (k + i))) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [peanoEulerWeight_at_grid_right hh (Nat.le_add_right k i)]
    simp
  have hhead : (∑ i ∈ Finset.range k,
      peanoEulerWeight h ((k : ℝ) * h) i •
        b (t - (i : ℝ) * h) (peanoEulerNode b t x h i)) =
      ∑ i ∈ Finset.range k,
        h • b (t - (i : ℝ) * h) (peanoEulerNode b t x h i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [peanoEulerWeight_at_grid_left hh (Finset.mem_range.mp hi)]
  rw [htail, add_zero, hhead, peanoEulerNode_eq_sum]

private theorem peanoEulerPolygon_decrement_eq
    (b : ℝ → Vec 2 → Vec 2) (t : ℝ) (x : Vec 2)
    (h T : ℝ) (N : ℕ)
    {u v : ℝ} (hu : u ∈ Set.Icc 0 T) (hv : v ∈ Set.Icc 0 T) :
    peanoEulerPolygon b t x h T N u - peanoEulerPolygon b t x h T N v =
      ∑ k ∈ Finset.range N,
        (peanoEulerWeight h v k - peanoEulerWeight h u k) •
          b (t - (k : ℝ) * h) (peanoEulerNode b t x h k) := by
  have hcu : peanoClamp T u = u := by simp [peanoClamp, max_eq_right hu.1, min_eq_right hu.2]
  have hcv : peanoClamp T v = v := by simp [peanoClamp, max_eq_right hv.1, min_eq_right hv.2]
  calc
    _ = (∑ k ∈ Finset.range N,
          peanoEulerWeight h v k • b (t - (k : ℝ) * h)
            (peanoEulerNode b t x h k)) -
        (∑ k ∈ Finset.range N,
          peanoEulerWeight h u k • b (t - (k : ℝ) * h)
            (peanoEulerNode b t x h k)) := by
      simp only [peanoEulerPolygon, hcu, hcv]
      abel
    _ = ∑ k ∈ Finset.range N,
        (peanoEulerWeight h v k • b (t - (k : ℝ) * h)
            (peanoEulerNode b t x h k) -
          peanoEulerWeight h u k • b (t - (k : ℝ) * h)
            (peanoEulerNode b t x h k)) := by
      symm
      rw [← Finset.sum_sub_distrib]
    _ = ∑ k ∈ Finset.range N,
        (peanoEulerWeight h v k - peanoEulerWeight h u k) •
          b (t - (k : ℝ) * h) (peanoEulerNode b t x h k) := by
      congr 1
      ext k
      rw [sub_smul]

theorem peanoEulerWeight_diff_pos_support
    {h u v : ℝ} (hh : 0 ≤ h) (huv : u ≤ v) (k : ℕ)
    (hpos : 0 < peanoEulerWeight h v k - peanoEulerWeight h u k) :
    (k : ℝ) * h < v ∧ u < (k + 1 : ℕ) * h := by
  have hk : (k : ℝ) * h ≤ (k + 1 : ℕ) * h := by
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ k) hh
  have hw_nonneg (z : ℝ) : 0 ≤ peanoEulerWeight h z k := by
    unfold peanoEulerWeight
    exact le_min hh (le_max_left 0 (z - (k : ℝ) * h))
  constructor
  · by_contra hv
    have hv' : v ≤ (k : ℝ) * h := le_of_not_gt hv
    have hwv : peanoEulerWeight h v k = 0 := by
      rw [peanoEulerWeight_eq_min_sub hh]
      rw [min_eq_left (le_trans hv' hk), min_eq_left hv']
      ring
    rw [hwv] at hpos
    linarith [hw_nonneg u]
  · by_contra hu
    have hu' : (k + 1 : ℕ) * h ≤ u := le_of_not_gt hu
    have hlow_u : (k : ℝ) * h ≤ u := le_trans hk hu'
    have huper_v : (k + 1 : ℕ) * h ≤ v := le_trans hu' huv
    have hlow_v : (k : ℝ) * h ≤ v := le_trans hk huper_v
    have hgap : ((k + 1 : ℕ) : ℝ) * h - (k : ℝ) * h = h := by
      push_cast
      ring
    have hwu : peanoEulerWeight h u k = h := by
      rw [peanoEulerWeight_eq_min_sub hh, min_eq_right hu', min_eq_right hlow_u, hgap]
    have hwv : peanoEulerWeight h v k = h := by
      rw [peanoEulerWeight_eq_min_sub hh, min_eq_right huper_v, min_eq_right hlow_v, hgap]
    rw [hwv, hwu] at hpos
    linarith

theorem peanoEulerPolygon_increment_error
    (b : ℝ → Vec 2 → Vec 2) (t : ℝ) (x : Vec 2)
    (h T ε r₀ : ℝ) (y₀ : Vec 2) (N : ℕ) (hh : 0 ≤ h) (hT : T = N * h)
    {u v : ℝ} (hu : u ∈ Set.Icc 0 T) (hv : v ∈ Set.Icc 0 T) (huv : u ≤ v)
    (hclose : ∀ k ∈ Finset.range N,
      0 < peanoEulerWeight h v k - peanoEulerWeight h u k →
        ‖b (t - (k : ℝ) * h) (peanoEulerNode b t x h k) - b r₀ y₀‖ ≤ ε) :
    ‖peanoEulerPolygon b t x h T N v - peanoEulerPolygon b t x h T N u +
      (v - u) • b r₀ y₀‖ ≤ (v - u) * ε := by
  have hweight (k : ℕ) :
      0 ≤ peanoEulerWeight h v k - peanoEulerWeight h u k :=
    sub_nonneg.mpr (by
      unfold peanoEulerWeight
      exact min_le_min_left h (max_le_max_left 0 (sub_le_sub_right huv _)))
  have hsum : (∑ k ∈ Finset.range N,
      (peanoEulerWeight h v k - peanoEulerWeight h u k)) = v - u := by
    rw [Finset.sum_sub_distrib, peanoEulerWeight_sum hh hv.1,
      peanoEulerWeight_sum hh hu.1, ← hT, min_eq_left hv.2, min_eq_left hu.2]
  have hdec := peanoEulerPolygon_decrement_eq b t x h T N hu hv
  have hinc : peanoEulerPolygon b t x h T N v - peanoEulerPolygon b t x h T N u =
      -∑ k ∈ Finset.range N,
        (peanoEulerWeight h v k - peanoEulerWeight h u k) •
          b (t - (k : ℝ) * h) (peanoEulerNode b t x h k) := by
    calc
      _ = -(peanoEulerPolygon b t x h T N u - peanoEulerPolygon b t x h T N v) := by abel
      _ = _ := by rw [hdec]
  have heq : peanoEulerPolygon b t x h T N v - peanoEulerPolygon b t x h T N u +
      (v - u) • b r₀ y₀ =
      ∑ k ∈ Finset.range N,
        (peanoEulerWeight h v k - peanoEulerWeight h u k) •
          (b r₀ y₀ - b (t - (k : ℝ) * h) (peanoEulerNode b t x h k)) := by
    calc
      _ = (∑ k ∈ Finset.range N,
          (peanoEulerWeight h v k - peanoEulerWeight h u k) •
            b r₀ y₀) -
          (∑ k ∈ Finset.range N,
          (peanoEulerWeight h v k - peanoEulerWeight h u k) •
            b (t - (k : ℝ) * h) (peanoEulerNode b t x h k)) := by
        rw [hinc, ← hsum, Finset.sum_smul]
        abel
      _ = ∑ k ∈ Finset.range N,
          ((peanoEulerWeight h v k - peanoEulerWeight h u k) •
              b r₀ y₀ -
            (peanoEulerWeight h v k - peanoEulerWeight h u k) •
              b (t - (k : ℝ) * h) (peanoEulerNode b t x h k)) := by
        rw [← Finset.sum_sub_distrib]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [smul_sub]
  rw [heq]
  calc
    ‖∑ k ∈ Finset.range N,
        (peanoEulerWeight h v k - peanoEulerWeight h u k) •
          (b r₀ y₀ -
            b (t - (k : ℝ) * h) (peanoEulerNode b t x h k))‖
        ≤ ∑ k ∈ Finset.range N,
          ‖(peanoEulerWeight h v k - peanoEulerWeight h u k) •
            (b r₀ y₀ -
              b (t - (k : ℝ) * h) (peanoEulerNode b t x h k))‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range N,
          (peanoEulerWeight h v k - peanoEulerWeight h u k) * ε :=
        Finset.sum_le_sum fun k hk => by
          by_cases hzero : peanoEulerWeight h v k - peanoEulerWeight h u k = 0
          · simp [hzero]
          · have hpos : 0 < peanoEulerWeight h v k - peanoEulerWeight h u k :=
              lt_of_le_of_ne (hweight k) (Ne.symm hzero)
            have hnear := hclose k hk hpos
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hweight k)]
            exact mul_le_mul_of_nonneg_left (by simpa [norm_sub_rev] using hnear) (hweight k)
    _ = (v - u) * ε := by rw [← Finset.sum_mul, hsum]

private theorem peanoEulerWeight_mono {h : ℝ} (k : ℕ) :
    Monotone (peanoEulerWeight h · k) := by
  intro u v huv
  unfold peanoEulerWeight
  exact min_le_min_left h (max_le_max_left 0 (sub_le_sub_right huv _))

private theorem peanoEulerPolygon_lipschitzOn_ordered
    (b : ℝ → Vec 2 → Vec 2) (t : ℝ) (x : Vec 2)
    (h T B : ℝ) (N : ℕ) (hh : 0 ≤ h) (hT : T = N * h)
    (hb : ∀ r y, ‖b r y‖ ≤ B)
    {u v : ℝ} (hu : u ∈ Set.Icc 0 T) (hv : v ∈ Set.Icc 0 T) (huv : u ≤ v) :
      ‖peanoEulerPolygon b t x h T N u - peanoEulerPolygon b t x h T N v‖ ≤
        B * (v - u) := by
  have hu0 : 0 ≤ u := hu.1
  have hv0 : 0 ≤ v := hv.1
  have hcu : peanoClamp T u = u := by
    simp [peanoClamp, max_eq_right hu0, min_eq_right hu.2]
  have hcv : peanoClamp T v = v := by
    simp [peanoClamp, max_eq_right hv0, min_eq_right hv.2]
  have hweight (k : ℕ) :
    0 ≤ peanoEulerWeight h v k - peanoEulerWeight h u k :=
      sub_nonneg.mpr ((peanoEulerWeight_mono k) huv)
  have hsum : (∑ k ∈ Finset.range N,
        (peanoEulerWeight h v k - peanoEulerWeight h u k)) = v - u := by
    rw [Finset.sum_sub_distrib,
        peanoEulerWeight_sum hh hv0, peanoEulerWeight_sum hh hu0,
        ← hT, min_eq_left hv.2, min_eq_left hu.2]
  have hdiff : peanoEulerPolygon b t x h T N u -
        peanoEulerPolygon b t x h T N v =
        ∑ k ∈ Finset.range N,
          (peanoEulerWeight h v k - peanoEulerWeight h u k) •
            b (t - (k : ℝ) * h) (peanoEulerNode b t x h k) := by
    calc
      _ = (∑ k ∈ Finset.range N,
          peanoEulerWeight h v k • b (t - (k : ℝ) * h)
            (peanoEulerNode b t x h k)) -
          (∑ k ∈ Finset.range N,
          peanoEulerWeight h u k • b (t - (k : ℝ) * h)
            (peanoEulerNode b t x h k)) := by
        simp only [peanoEulerPolygon, hcu, hcv]
        abel
      _ = ∑ k ∈ Finset.range N,
          (peanoEulerWeight h v k • b (t - (k : ℝ) * h)
            (peanoEulerNode b t x h k) -
          peanoEulerWeight h u k • b (t - (k : ℝ) * h)
            (peanoEulerNode b t x h k)) := by
        symm
        rw [← Finset.sum_sub_distrib]
      _ = ∑ k ∈ Finset.range N,
          (peanoEulerWeight h v k - peanoEulerWeight h u k) •
            b (t - (k : ℝ) * h) (peanoEulerNode b t x h k) := by
        congr 1
        ext k
        rw [sub_smul]
  rw [hdiff]
  calc
      ‖∑ k ∈ Finset.range N,
          (peanoEulerWeight h v k - peanoEulerWeight h u k) •
            b (t - (k : ℝ) * h) (peanoEulerNode b t x h k)‖
          ≤ ∑ k ∈ Finset.range N,
            ‖(peanoEulerWeight h v k - peanoEulerWeight h u k) •
              b (t - (k : ℝ) * h) (peanoEulerNode b t x h k)‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range N,
            (peanoEulerWeight h v k - peanoEulerWeight h u k) * B :=
          Finset.sum_le_sum fun k hk => by
            rw [norm_smul, Real.norm_eq_abs,
              abs_of_nonneg (hweight k)]
            exact mul_le_mul_of_nonneg_left (hb _ _) (hweight k)
      _ = B * (v - u) := by rw [← Finset.sum_mul, hsum]; ring

private theorem peanoEulerPolygon_lipschitzOn
    (b : ℝ → Vec 2 → Vec 2) (t : ℝ) (x : Vec 2)
    (h T B : ℝ) (N : ℕ) (hh : 0 ≤ h) (hT : T = N * h)
    (hb : ∀ r y, ‖b r y‖ ≤ B) :
    ∀ u ∈ Set.Icc 0 T, ∀ v ∈ Set.Icc 0 T,
      ‖peanoEulerPolygon b t x h T N u - peanoEulerPolygon b t x h T N v‖ ≤
        B * |u - v| := by
  intro u hu v hv
  rcases le_total u v with huv | hvu
  · calc
      ‖peanoEulerPolygon b t x h T N u - peanoEulerPolygon b t x h T N v‖ ≤
          B * (v - u) := peanoEulerPolygon_lipschitzOn_ordered
            b t x h T B N hh hT hb hu hv huv
      _ = B * |u - v| := by
        rw [abs_of_nonpos (sub_nonpos.mpr huv)]
        ring
  · have hrev := peanoEulerPolygon_lipschitzOn_ordered
      b t x h T B N hh hT hb (u := v) (v := u) hv hu hvu
    calc
      _ = ‖peanoEulerPolygon b t x h T N v - peanoEulerPolygon b t x h T N u‖ := by
        rw [norm_sub_rev]
      _ ≤ B * (u - v) := hrev
      _ = B * |u - v| := by rw [abs_of_nonneg (sub_nonneg.mpr hvu)]

private theorem peanoEulerPolygon_lipschitz
    (b : ℝ → Vec 2 → Vec 2) (t : ℝ) (x : Vec 2)
    (h T B : ℝ) (N : ℕ) (hh : 0 ≤ h) (hT : T = N * h)
    (hB : 0 ≤ B) (hb : ∀ r y, ‖b r y‖ ≤ B) :
    ∀ u v, ‖peanoEulerPolygon b t x h T N u - peanoEulerPolygon b t x h T N v‖ ≤
      B * |u - v| := by
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  intro u v
  have hu := peanoClamp_mem hT0 u
  have hv := peanoClamp_mem hT0 v
  have hcl : |peanoClamp T u - peanoClamp T v| ≤ |u - v| := by
    have := (peanoClamp_lipschitz T).dist_le_mul u v
    simpa [Real.dist_eq] using this
  have hloc := peanoEulerPolygon_lipschitzOn b t x h T B N hh hT hb
    (peanoClamp T u) hu (peanoClamp T v) hv
  calc
    ‖peanoEulerPolygon b t x h T N u - peanoEulerPolygon b t x h T N v‖ =
      ‖peanoEulerPolygon b t x h T N (peanoClamp T u) -
        peanoEulerPolygon b t x h T N (peanoClamp T v)‖ := by
          simp [peanoEulerPolygon, peanoClamp_idem hT0]
    _ ≤ B * |peanoClamp T u - peanoClamp T v| := hloc
    _ ≤ B * |u - v| := mul_le_mul_of_nonneg_left hcl hB

theorem peanoEulerPolygon_zero
    (b : ℝ → Vec 2 → Vec 2) (t : ℝ) (x : Vec 2)
    (h T : ℝ) (N : ℕ) (hh : 0 ≤ h) (hT : 0 ≤ T) :
    peanoEulerPolygon b t x h T N 0 = x := by
  have hclamp : peanoClamp T 0 = 0 := by
    simp [peanoClamp, hT]
  have hw (k : ℕ) : peanoEulerWeight h 0 k = 0 := by
    unfold peanoEulerWeight
    have hkprod : 0 ≤ (k : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hh
    have hk : 0 - (k : ℝ) * h ≤ 0 := by linarith
    rw [max_eq_left hk, min_eq_right hh]
  change x - ∑ k ∈ Finset.range N,
    peanoEulerWeight h (peanoClamp T 0) k •
      b (t - (k : ℝ) * h) (peanoEulerNode b t x h k) = x
  rw [hclamp]
  simp [hw]

private theorem continuous_peanoEulerPolygon (b : ℝ → Vec 2 → Vec 2) (t : ℝ) (x : Vec 2)
    (h T : ℝ) (N : ℕ) : Continuous (peanoEulerPolygon b t x h T N) := by
  unfold peanoEulerPolygon
  have hclamp : Continuous (peanoClamp T) := by
    exact continuous_const.min (continuous_const.max continuous_id)
  have hweight (k : ℕ) : Continuous (fun u : ℝ =>
      peanoEulerWeight h (peanoClamp T u) k) := by
    unfold peanoEulerWeight
    exact continuous_const.min (continuous_const.max
      (hclamp.sub continuous_const))
  exact continuous_const.sub (continuous_finsetSum _ fun k hk =>
    (hweight k).smul continuous_const)

/-- A polygon on a growing backward interval, with mesh tending to zero. Its `n`th
interval has length `n+1` and `(n+1)^2` Euler steps. -/
def peanoEulerApprox (b : ℝ → Vec 2 → Vec 2) (t : ℝ) (x : Vec 2)
    (n : ℕ) (u : ℝ) : Vec 2 :=
  peanoEulerPolygon b t x (1 / ((n + 1 : ℕ) : ℝ))
    ((n + 1 : ℕ) : ℝ) ((n + 1) * (n + 1)) u

theorem peanoEulerApprox_step_nonneg (n : ℕ) :
    0 ≤ 1 / ((n + 1 : ℕ) : ℝ) := by positivity

theorem peanoEulerApprox_length_eq_steps (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) =
      (((n + 1) * (n + 1) : ℕ) : ℝ) * (1 / ((n + 1 : ℕ) : ℝ)) := by
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

theorem peanoEulerApprox_lipschitz
    (b : ℝ → Vec 2 → Vec 2) (t : ℝ) (x : Vec 2) (B : ℝ)
    (hB : 0 ≤ B) (hb : ∀ r y, ‖b r y‖ ≤ B) :
    ∀ n u v, ‖peanoEulerApprox b t x n u - peanoEulerApprox b t x n v‖ ≤
      B * |u - v| := by
  intro n u v
  exact peanoEulerPolygon_lipschitz b t x
    (1 / ((n + 1 : ℕ) : ℝ)) ((n + 1 : ℕ) : ℝ) B
    ((n + 1) * (n + 1)) (peanoEulerApprox_step_nonneg n)
    (peanoEulerApprox_length_eq_steps n) hB hb u v

private theorem peanoEulerApprox_displacement
    (b : ℝ → Vec 2 → Vec 2) (t : ℝ) (x : Vec 2) (B : ℝ)
    (hB : 0 ≤ B) (hb : ∀ r y, ‖b r y‖ ≤ B) :
    ∀ n u, ‖peanoEulerApprox b t x n u - x‖ ≤ B * |u| := by
  intro n u
  have hzero : peanoEulerApprox b t x n 0 = x := by
    unfold peanoEulerApprox
    exact peanoEulerPolygon_zero b t x _ _ _ (peanoEulerApprox_step_nonneg n) (by positivity)
  have hLip := peanoEulerApprox_lipschitz b t x B hB hb n u 0
  rw [hzero] at hLip
  simpa using hLip

private theorem continuous_peanoEulerApprox (b : ℝ → Vec 2 → Vec 2) (t : ℝ) (x : Vec 2)
    (n : ℕ) : Continuous (peanoEulerApprox b t x n) := by
  exact continuous_peanoEulerPolygon b t x
    (1 / ((n + 1 : ℕ) : ℝ)) ((n + 1 : ℕ) : ℝ) ((n + 1) * (n + 1))

private theorem peanoEulerApprox_pointwiseCompact
    (b : ℝ → Vec 2 → Vec 2) (t : ℝ) (x : Vec 2) (B : ℝ)
    (hB : 0 ≤ B) (hb : ∀ r y, ‖b r y‖ ≤ B)
    (K : Set ℝ) (hK : IsCompact K) :
    ∃ Q : Set (Vec 2), IsCompact Q ∧
      ∀ n u, u ∈ K → peanoEulerApprox b t x n u ∈ Q := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℝ)
  let R' := max R 0
  refine ⟨Metric.closedBall x (B * R'), isCompact_closedBall _ _, ?_⟩
  intro n u hu
  have huR : |u| ≤ R' := by
    have huBall : u ∈ Metric.closedBall (0 : ℝ) R := hR hu
    have hdist : dist u 0 ≤ R := Metric.mem_closedBall.mp huBall
    have habs : |u| ≤ R := by simpa [Real.dist_eq] using hdist
    exact habs.trans (le_max_left R 0)
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact (peanoEulerApprox_displacement b t x B hB hb n u).trans
    (mul_le_mul_of_nonneg_left huR hB)

private theorem peanoEulerApprox_equicontinuousOn
    (b : ℝ → Vec 2 → Vec 2) (t : ℝ) (x : Vec 2) (B : ℝ)
    (hB : 0 ≤ B) (hb : ∀ r y, ‖b r y‖ ≤ B) (K : Set ℝ) :
    EquicontinuousOn (fun n u => peanoEulerApprox b t x n u) K := by
  have hL : ∀ n, LipschitzOnWith (Real.toNNReal B) (peanoEulerApprox b t x n) K := by
    intro n
    apply LipschitzOnWith.of_dist_le'
    intro u hu v hv
    simpa [dist_eq_norm, Real.dist_eq] using
      peanoEulerApprox_lipschitz b t x B hB hb n u v
  have hU : UniformEquicontinuousOn
      (fun n u => peanoEulerApprox b t x n u) K :=
    LipschitzOnWith.uniformEquicontinuousOn
      (fun n u => peanoEulerApprox b t x n u) (Real.toNNReal B) hL
  exact hU.equicontinuousOn

theorem peanoEulerAscoli
    (b : ℝ → Vec 2 → Vec 2) (t : ℝ) (x : Vec 2) (B : ℝ)
    (hB : 0 ≤ B) (hb : ∀ r y, ‖b r y‖ ≤ B) :
    ∃ (φ : ℕ → ℕ) (X : C(ℝ, Vec 2)), StrictMono φ ∧
      TendstoLocallyUniformly (fun n u => peanoEulerApprox b t x (φ n) u) X atTop := by
  let F : ℕ → C(ℝ, Vec 2) := fun n =>
    ⟨peanoEulerApprox b t x n, continuous_peanoEulerApprox b t x n⟩
  let eval (f : C(ℝ, Vec 2)) : ℝ → Vec 2 := fun u => f u
  have hclosed : IsClosedEmbedding
      (UniformOnFun.ofFun {K : Set ℝ | IsCompact K} ∘ eval) := by
    have hclosed' : IsClosedEmbedding
        (ContinuousMap.toUniformOnFunIsCompact (α := ℝ) (β := Vec 2)) := by
      refine ⟨(ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact
        (α := ℝ) (β := Vec 2)).isEmbedding, ?_⟩
      rw [ContinuousMap.range_toUniformOnFunIsCompact]
      exact UniformOnFun.isClosed_setOfPred_continuous
        (CompactlyCoherentSpace.isCoherentWith (X := ℝ))
    have heq : UniformOnFun.ofFun {K : Set ℝ | IsCompact K} ∘ eval =
        ContinuousMap.toUniformOnFunIsCompact := by
      funext f
      rfl
    rw [heq]
    exact hclosed'
  have hfamily : IsCompact (closure (Set.range F)) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (𝔖 := {K : Set ℝ | IsCompact K})
      (𝔖_compact := by intro K hK; exact hK)
      (F_clemb := hclosed)
    · intro K hK
      let chooseIndex : Set.range F → ℕ := fun f => Classical.choose f.property
      have hcomp := (peanoEulerApprox_equicontinuousOn b t x B hB hb K).comp chooseIndex
      have hEq : (fun f : Set.range F => fun u => F (chooseIndex f) u) =
          fun f => eval f.1 := by
        funext f u
        exact congrArg (fun g : C(ℝ, Vec 2) => g u) (Classical.choose_spec f.property)
      change EquicontinuousOn (fun f : Set.range F => fun u => eval f.1 u) K
      rw [← hEq]
      exact hcomp
    · intro K hK u hu
      obtain ⟨Q, hQc, hQF⟩ := peanoEulerApprox_pointwiseCompact b t x B hB hb K hK
      refine ⟨Q, hQc, ?_⟩
      rintro f ⟨n, rfl⟩
      exact hQF n u hu
  obtain ⟨f, hfmem, φ, hφ, hlim⟩ := hfamily.tendsto_subseq fun n =>
    subset_closure ⟨n, rfl⟩
  refine ⟨φ, f, hφ, ?_⟩
  exact (ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hlim)

end AVRegularity.External
end

section
open Filter Homogenization Topology
namespace AVRegularity.External

/-! Existence of a backward Peano trajectory on the whole half-line. -/

private theorem peanoEulerMesh_tendsto_zero (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    Tendsto (fun n => 1 / ((φ n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop
  simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using h

private theorem peanoEulerPoint_tendsto
    {b : ℝ → Vec 2 → Vec 2} {t : ℝ} {x : Vec 2}
    {φ : ℕ → ℕ} {X : C(ℝ, Vec 2)}
    (hlim : TendstoLocallyUniformly (fun n u => peanoEulerApprox b t x (φ n) u) X atTop)
    (u : ℝ) :
    Tendsto (fun n => peanoEulerApprox b t x (φ n) u) atTop (𝓝 (X u)) := by
  exact hlim.tendstoLocallyUniformlyOn.tendsto_at (Set.mem_univ u)

private theorem peanoEulerLimit_lipschitz
    {b : ℝ → Vec 2 → Vec 2} {t : ℝ} {x : Vec 2} {B : ℝ}
    (hB : 0 ≤ B) (hb : ∀ r y, ‖b r y‖ ≤ B)
    {φ : ℕ → ℕ} {X : C(ℝ, Vec 2)}
    (hlim : TendstoLocallyUniformly (fun n u => peanoEulerApprox b t x (φ n) u) X atTop)
    (u v : ℝ) : ‖X u - X v‖ ≤ B * |u - v| := by
  have hpu := peanoEulerPoint_tendsto hlim u
  have hpv := peanoEulerPoint_tendsto hlim v
  have hdiff : Tendsto
      (fun n => peanoEulerApprox b t x (φ n) u - peanoEulerApprox b t x (φ n) v)
      atTop (𝓝 (X u - X v)) := hpu.sub hpv
  have hnorm := continuous_norm.tendsto (X u - X v) |>.comp hdiff
  refine le_of_tendsto_of_tendsto' hnorm tendsto_const_nhds ?_
  intro n
  exact peanoEulerApprox_lipschitz b t x B hB hb (φ n) u v

private theorem peanoEulerLimit_ordered_increment
    {b : ℝ → Vec 2 → Vec 2} {t : ℝ} {x : Vec 2} {B : ℝ}
    (hB : 0 ≤ B) (hb : ∀ r y, ‖b r y‖ ≤ B)
    (hbcont : Continuous (fun p : ℝ × Vec 2 => b p.1 p.2))
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {X : C(ℝ, Vec 2)}
    (hlim : TendstoLocallyUniformly (fun n u => peanoEulerApprox b t x (φ n) u) X atTop)
    (u : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ > 0, ∀ a v, 0 ≤ a → 0 ≤ v → a ≤ v →
      |a - u| < ρ → |v - u| < ρ →
      ‖X v - X a + (v - a) • b (t - u) (X u)‖ ≤ (v - a) * ε := by
  let p : ℝ × Vec 2 := (t - u, X u)
  have hbp : ContinuousAt (fun q : ℝ × Vec 2 => b q.1 q.2) p := hbcont.continuousAt
  obtain ⟨δ, hδ, hcont⟩ :=
    (Metric.continuousAt_iff.mp hbp) (ε / 2) (by positivity)
  let ρ := δ / (8 * (B + 1))
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hscale : (4 * B + 1) * ρ < δ := by
    dsimp [ρ]
    have hden : 0 < 8 * (B + 1) := by positivity
    have hden' : 8 * (B + 1) ≠ 0 := ne_of_gt hden
    field_simp
    nlinarith [hB, hδ]
  have htimeScale : 4 * ρ < δ := by
    dsimp [ρ]
    have hden : 0 < 8 * (B + 1) := by positivity
    have hden' : 8 * (B + 1) ≠ 0 := ne_of_gt hden
    field_simp
    nlinarith [hB, hδ]
  have hmesh := peanoEulerMesh_tendsto_zero φ hφ
  have hmeshEvent : ∀ᶠ j in atTop, 1 / ((φ j + 1 : ℕ) : ℝ) < ρ :=
    (tendsto_order.1 hmesh).2 ρ hρ
  refine ⟨ρ, hρ, ?_⟩
  intro a v ha hv hav hau hvu
  obtain ⟨M, hM⟩ := exists_nat_gt (max a v)
  have hMa : a < (M : ℝ) := (le_max_left a v).trans_lt hM
  have hMv : v < (M : ℝ) := (le_max_right a v).trans_lt hM
  have hindex : ∀ᶠ j in atTop, M ≤ φ j :=
    hφ.tendsto_atTop.eventually (Filter.eventually_atTop.2 ⟨M, fun n hn => hn⟩)
  have hpa := peanoEulerPoint_tendsto hlim a
  have hpaEvent : ∀ᶠ j in atTop,
      ‖peanoEulerApprox b t x (φ j) a - X a‖ < ρ := by
    have hball := hpa.eventually (Metric.ball_mem_nhds (X a) hρ)
    filter_upwards [hball] with j hj
    simpa [Metric.mem_ball, dist_eq_norm] using hj
  have hpolyEvent : ∀ᶠ j in atTop,
      ‖peanoEulerApprox b t x (φ j) v - peanoEulerApprox b t x (φ j) a +
        (v - a) • b (t - u) (X u)‖ ≤ (v - a) * (ε / 2) := by
    filter_upwards [hmeshEvent, hindex, hpaEvent] with j hjmesh hjindex hjpa
    let h := 1 / ((φ j + 1 : ℕ) : ℝ)
    let T : ℝ := ((φ j + 1 : ℕ) : ℝ)
    let N : ℕ := (φ j + 1) * (φ j + 1)
    have hh : 0 ≤ h := by dsimp [h]; positivity
    have hhρ : h < ρ := by simpa [h] using hjmesh
    have hMφ : (M : ℝ) ≤ (φ j : ℝ) := by exact_mod_cast hjindex
    have hTleft : a ≤ T := by
      dsimp [T]
      calc
        a ≤ (M : ℝ) := hMa.le
        _ ≤ (φ j : ℝ) := hMφ
        _ ≤ ((φ j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ (φ j)
    have hTright : v ≤ T := by
      dsimp [T]
      calc
        v ≤ (M : ℝ) := hMv.le
        _ ≤ (φ j : ℝ) := hMφ
        _ ≤ ((φ j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ (φ j)
    have hT_eq : T = N * h := by
      dsimp [T, N, h]
      exact peanoEulerApprox_length_eq_steps (φ j)
    have haIcc : a ∈ Set.Icc 0 T := ⟨ha, hTleft⟩
    have hvIcc : v ∈ Set.Icc 0 T := ⟨hv, hTright⟩
    have hclose : ∀ k ∈ Finset.range N,
      0 < peanoEulerWeight h v k - peanoEulerWeight h a k →
        ‖b (t - (k : ℝ) * h) (peanoEulerNode b t x h k) - b (t - u) (X u)‖ ≤ ε / 2 := by
      intro k hk hpos
      obtain ⟨hkv, hak⟩ := peanoEulerWeight_diff_pos_support hh hav k hpos
      have hkN : k ≤ N := Nat.le_of_lt (Finset.mem_range.mp hk)
      have hnode := peanoEulerPolygon_at_grid b t x h T N k hh hT_eq hkN
      have hgrid : |(k : ℝ) * h - a| ≤ (v - a) + h := by
        have hstep : ((k + 1 : ℕ) : ℝ) * h = (k : ℝ) * h + h := by
          push_cast
          ring
        rw [abs_le]
        constructor
        · have hak' : a < (k : ℝ) * h + h := by rw [← hstep]; exact hak
          linarith
        · linarith
      have hva : v - a ≤ 2 * ρ := by
        have h1 : u - a < ρ := by
          have := (abs_lt.mp hau).1
          linarith
        have h2 : v - u < ρ := by
          have := (abs_lt.mp hvu).2
          linarith
        linarith
      have hgridρ : |(k : ℝ) * h - a| < 3 * ρ := by
        calc
          |(k : ℝ) * h - a| ≤ (v - a) + h := hgrid
          _ < 2 * ρ + ρ := add_lt_add_of_le_of_lt hva hhρ
          _ = 3 * ρ := by ring
      have htime : |(t - (k : ℝ) * h) - (t - u)| < δ := by
        have hku : |(k : ℝ) * h - u| ≤
            |(k : ℝ) * h - a| + |a - u| := abs_sub_le _ _ _
        have hkuρ : |(k : ℝ) * h - u| < 4 * ρ := by
          calc
            |(k : ℝ) * h - u| ≤ |(k : ℝ) * h - a| + |a - u| := hku
            _ < 3 * ρ + ρ := add_lt_add_of_lt_of_lt hgridρ hau
            _ = 4 * ρ := by ring
        rw [show (t - (k : ℝ) * h) - (t - u) = u - (k : ℝ) * h by ring,
          abs_sub_comm]
        exact hkuρ.trans htimeScale
      have htimeDist : dist (t - (k : ℝ) * h) (t - u) < δ := by
        rw [Real.dist_eq]
        convert htime using 1
      have hnodeClose : ‖peanoEulerNode b t x h k - X u‖ < δ := by
        have hnode_a :
            ‖peanoEulerNode b t x h k - peanoEulerApprox b t x (φ j) a‖ ≤
              B * |(k : ℝ) * h - a| := by
          rw [← hnode]
          exact peanoEulerApprox_lipschitz b t x B hB hb (φ j) ((k : ℝ) * h) a
        have hmiddle :
            ‖peanoEulerApprox b t x (φ j) a - X u‖ ≤
              ‖peanoEulerApprox b t x (φ j) a - X a‖ + B * |a - u| := by
          calc
            ‖peanoEulerApprox b t x (φ j) a - X u‖ =
                ‖(peanoEulerApprox b t x (φ j) a - X a) + (X a - X u)‖ := by
                  congr 1; abel
            _ ≤ _ := norm_add_le _ _
            _ ≤ _ := by
              have hlip := peanoEulerLimit_lipschitz hB hb hlim a u
              linarith
        have hnode_bound :
            ‖peanoEulerNode b t x h k - X u‖ ≤
              B * |(k : ℝ) * h - a| +
                ‖peanoEulerApprox b t x (φ j) a - X a‖ + B * |a - u| := by
          calc
            ‖peanoEulerNode b t x h k - X u‖ =
                ‖(peanoEulerNode b t x h k - peanoEulerApprox b t x (φ j) a) +
                  (peanoEulerApprox b t x (φ j) a - X u)‖ := by
                    congr 1; abel
            _ ≤ _ := norm_add_le _ _
            _ ≤ _ := by linarith [hnode_a, hmiddle]
        have hfirst : B * |(k : ℝ) * h - a| ≤ B * (3 * ρ) :=
          mul_le_mul_of_nonneg_left hgridρ.le hB
        have hlast : B * |a - u| ≤ B * ρ :=
          mul_le_mul_of_nonneg_left (le_of_lt hau) hB
        calc
          ‖peanoEulerNode b t x h k - X u‖ ≤
              B * |(k : ℝ) * h - a| +
                ‖peanoEulerApprox b t x (φ j) a - X a‖ + B * |a - u| := hnode_bound
          _ < (4 * B + 1) * ρ := by linarith
          _ < δ := hscale
      have hprod : dist
          (t - (k : ℝ) * h, peanoEulerNode b t x h k) (t - u, X u) < δ := by
        rw [Prod.dist_eq]
        exact max_lt_iff.mpr ⟨htimeDist,
          by simpa [dist_eq_norm] using hnodeClose⟩
      have hfield := hcont hprod
      have hnorm : ‖b (t - (k : ℝ) * h) (peanoEulerNode b t x h k) - b (t - u) (X u)‖ < ε / 2 := by
        simpa [p, dist_eq_norm] using hfield
      exact hnorm.le
    have hpoly := peanoEulerPolygon_increment_error b t x h T (ε / 2) (t - u) (X u)
      N hh hT_eq haIcc hvIcc hav hclose
    simpa [peanoEulerApprox, h, T, N] using hpoly
  have hlimA := peanoEulerPoint_tendsto hlim a
  have hlimV := peanoEulerPoint_tendsto hlim v
  have hsum : Tendsto
      (fun n => peanoEulerApprox b t x (φ n) v - peanoEulerApprox b t x (φ n) a +
        (v - a) • b (t - u) (X u)) atTop
      (𝓝 (X v - X a + (v - a) • b (t - u) (X u))) := by
    exact (hlimV.sub hlimA).add tendsto_const_nhds
  have hnormlim := continuous_norm.tendsto
    (X v - X a + (v - a) • b (t - u) (X u)) |>.comp hsum
  have hbound := le_of_tendsto hnormlim hpolyEvent
  have hfactor : (v - a) * (ε / 2) ≤ (v - a) * ε := by
    apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hav)
    linarith
  exact hbound.trans hfactor

private theorem peanoEulerLimit_local_increment
    {b : ℝ → Vec 2 → Vec 2} {t : ℝ} {x : Vec 2} {B : ℝ}
    (hB : 0 ≤ B) (hb : ∀ r y, ‖b r y‖ ≤ B)
    (hbcont : Continuous (fun p : ℝ × Vec 2 => b p.1 p.2))
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {X : C(ℝ, Vec 2)}
    (hlim : TendstoLocallyUniformly (fun n u => peanoEulerApprox b t x (φ n) u) X atTop)
    (u : ℝ) (hu : 0 ≤ u) (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ > 0, ∀ v, 0 ≤ v → |v - u| < ρ →
      ‖X v - X u + (v - u) • b (t - u) (X u)‖ ≤ ε * |v - u| := by
  obtain ⟨ρ, hρ, hinc⟩ :=
    peanoEulerLimit_ordered_increment hB hb hbcont hφ hlim u ε hε
  refine ⟨ρ, hρ, ?_⟩
  intro v hv hvu
  rcases le_total u v with huv | hvu'
  · have habs : |u - u| < ρ := by simpa using hρ
    have hresult := hinc u v hu hv huv habs hvu
    simpa [sub_self, abs_of_nonneg (sub_nonneg.mpr huv), mul_comm] using hresult
  · have habs : |v - u| < ρ := hvu
    have hresult := hinc v u hv hu hvu' habs (by simpa [abs_sub_comm] using hρ)
    let c := b (t - u) (X u)
    have hneg' : X v - X u + (v - u) • c =
        -(X u - X v + (u - v) • c) := by
      ext i
      simp [smul_eq_mul]
      ring
    have hneg : X v - X u + (v - u) • b (t - u) (X u) =
        -(X u - X v + (u - v) • b (t - u) (X u)) := by
      simpa only [c] using hneg'
    rw [hneg, norm_neg, abs_of_nonpos (sub_nonpos.mpr hvu')]
    simpa [mul_comm] using hresult

private theorem hasDerivWithinAt_of_localSecantBound
    {f : ℝ → Vec 2} {d : ℝ → Vec 2} {S : Set ℝ}
    (hsec : ∀ u, u ∈ S → ∀ ε > 0, ∃ ρ > 0, ∀ v, v ∈ S → |v - u| < ρ →
      ‖f v - f u - (v - u) • d u‖ ≤ ε * |v - u|) :
    ∀ u, u ∈ S → HasDerivWithinAt f (d u) S u := by
  intro u hu
  rw [hasDerivWithinAt_iff_tendsto]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨ρ, hρ, hsec'⟩ := hsec u hu (ε / 2) (by positivity)
  have hnear : ∀ᶠ v in 𝓝[S] u, |v - u| < ρ := by
    have hopen : ∀ᶠ v in 𝓝 u, v ∈ Set.Ioo (u - ρ) (u + ρ) := by
      have hm : Set.Ioo (u - ρ) (u + ρ) ∈ 𝓝 u :=
        IsOpen.mem_nhds isOpen_Ioo ⟨by linarith, by linarith⟩
      exact hm
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hopen] with v hv
    rw [Set.mem_Ioo] at hv
    rw [abs_lt]
    constructor <;> linarith
  filter_upwards [hnear, eventually_mem_nhdsWithin] with v hv hvs
  have hrem := hsec' v hvs hv
  have hratio : |v - u|⁻¹ *
      ‖f v - f u - (v - u) • d u‖ ≤ ε / 2 := by
    by_cases hvu : v = u
    · simp [hvu]
      positivity
    · have hden : 0 < |v - u| := abs_pos.mpr (sub_ne_zero.mpr hvu)
      have hinv : 0 ≤ |v - u|⁻¹ := inv_nonneg.mpr (abs_nonneg (v - u))
      have hmul := mul_le_mul_of_nonneg_left hrem hinv
      have hcancel : |v - u|⁻¹ * |v - u| = 1 :=
        inv_mul_cancel₀ (ne_of_gt hden)
      calc
        _ ≤ |v - u|⁻¹ * ((ε / 2) * |v - u|) := hmul
        _ = ε / 2 := by
          calc
            |v - u|⁻¹ * ((ε / 2) * |v - u|) =
                (ε / 2) * (|v - u|⁻¹ * |v - u|) := by ring
            _ = ε / 2 := by rw [hcancel, mul_one]
  have hnonneg : 0 ≤ |v - u|⁻¹ * ‖f v - f u - (v - u) • d u‖ :=
    mul_nonneg (inv_nonneg.mpr (abs_nonneg _)) (norm_nonneg _)
  have hdist : dist
      (|v - u|⁻¹ * ‖f v - f u - (v - u) • d u‖) 0 < ε := by
    simpa [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using
      (lt_of_le_of_lt hratio (by linarith))
  exact hdist

theorem exists_peanoBackwardTrajectory
    (b : ℝ → Vec 2 → Vec 2)
    (hbcont : Continuous (fun p : ℝ × Vec 2 => b p.1 p.2))
    (hbdd : ∃ B : ℝ, 0 ≤ B ∧ ∀ r y, ‖b r y‖ ≤ B) :
    ∀ t x, ∃ X : ℝ → Vec 2, X t = x ∧
      ∀ s, s ≤ t → HasDerivWithinAt X (b s (X s)) (Set.Iic t) s := by
  obtain ⟨B, hB, hb⟩ := hbdd
  intro t x
  obtain ⟨φ, Y, hφ, hlim⟩ := peanoEulerAscoli b t x B hB hb
  let X : ℝ → Vec 2 := fun s => Y (t - s)
  have hY0 : Y 0 = x := by
    have hzero : ∀ n, peanoEulerApprox b t x (φ n) 0 = x := by
      intro n
      unfold peanoEulerApprox
      exact peanoEulerPolygon_zero b t x _ _ _ (peanoEulerApprox_step_nonneg _) (by positivity)
    have htend := peanoEulerPoint_tendsto hlim 0
    have hconst : Tendsto (fun _ : ℕ => x) atTop (𝓝 x) := tendsto_const_nhds
    exact tendsto_nhds_unique (by simpa [hzero] using htend) hconst
  have hsec : ∀ u, 0 ≤ u → ∀ ε > 0, ∃ ρ > 0, ∀ v, 0 ≤ v → |v - u| < ρ →
      ‖Y v - Y u + (v - u) • b (t - u) (Y u)‖ ≤ ε * |v - u| := by
    intro u hu ε hε
    exact peanoEulerLimit_local_increment hB hb hbcont hφ hlim u hu ε hε
  have hsecX : ∀ s, s ∈ Set.Iic t → ∀ ε > 0, ∃ ρ > 0, ∀ r, r ∈ Set.Iic t →
      |r - s| < ρ →
      ‖X r - X s - (r - s) • b s (X s)‖ ≤ ε * |r - s| := by
    intro s hs ε hε
    obtain ⟨ρ, hρ, hlocal⟩ := hsec (t - s) (sub_nonneg.mpr hs) ε hε
    refine ⟨ρ, hρ, ?_⟩
    intro r hr hrs
    let u := t - s
    let v := t - r
    have hu0 : 0 ≤ u := sub_nonneg.mpr hs
    have hv0 : 0 ≤ v := sub_nonneg.mpr hr
    have hclose : |v - u| < ρ := by
      dsimp [u, v]
      calc
        |(t - r) - (t - s)| = |s - r| := by congr 1; ring
        _ = |r - s| := abs_sub_comm _ _
        _ < ρ := hrs
    have htime : t - u = s := by dsimp [u]; ring
    have hrem :
        X r - X s - (r - s) • b s (X s) =
          Y v - Y u + (v - u) • b (t - u) (Y u) := by
      dsimp [X, u, v]
      rw [htime]
      have hcoeff : (t - r) - (t - s) = -(r - s) := by ring
      rw [hcoeff, neg_smul]
      abel
    have hbound := hlocal v hv0 hclose
    have habs : |v - u| = |r - s| := by
      dsimp [u, v]
      calc
        |(t - r) - (t - s)| = |s - r| := by congr 1; ring
        _ = |r - s| := abs_sub_comm _ _
    have hbound' :
        ‖Y v - Y u + (v - u) • b (t - u) (Y u)‖ ≤ ε * |v - u| := by
      simpa [u] using hbound
    calc
      ‖X r - X s - (r - s) • b s (X s)‖ =
          ‖Y v - Y u + (v - u) • b (t - u) (Y u)‖ := by rw [hrem]
      _ ≤ ε * |r - s| := by
        calc
          _ ≤ ε * |v - u| := hbound'
          _ = ε * |r - s| := by rw [habs]
  have hderivX := hasDerivWithinAt_of_localSecantBound hsecX
  refine ⟨X, ?_, ?_⟩
  · change Y (t - t) = x
    simpa using hY0
  · intro s hs
    exact hderivX s hs

end AVRegularity.External
end
