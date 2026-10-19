-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVenhance.Infra.Section3.SpaceAverages
import AVenhance.Infra.FullTheorem.NoSelectionInputs.CosineIntegral
public import AVRegularity.CycleEvolution.TimeEnergy
import AVRegularity.CycleReference.CorrectorMeanGeometry
public import AVRegularity.Definitions.CycleEvolution.IsFibreGraph
import AVRegularity.CycleReference.ChartTestCalculus
import AVRegularity.CycleReference.CoreFlux
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Intermediate.CycleReference.OcMeanFlux
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.CycleReference.SingleModeFlux
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance
namespace AVRegularity.CycleDamping

/-! Phase-independent averages of the sinusoidal cell shear.
Reuse: the upstream cosine-square integral has exactly an integer frequency,
a positive integer frequency premise, and an arbitrary real phase. We use frequency one. -/

theorem cell_cosine_mean_zero (j : Fin 2) (phase : ℝ) :
    (∫ z in unitCube, Real.cos (2 * Real.pi * (z j + phase))) = 0 := by
  change spaceAvg (fun z : Vec 2 => Real.cos (2 * Real.pi * (z j + phase))) = _
  rw [AVenhance.Infra.Section3.spaceAvg_coordIntegral
    (F := fun s : ℝ => Real.cos (2 * Real.pi * (s + phase))) (by fun_prop) j]
  have hd (s : ℝ) : HasDerivAt
      (fun x : ℝ => Real.sin (2 * Real.pi * (x + phase)) / (2 * Real.pi))
      (Real.cos (2 * Real.pi * (s + phase))) s := by
    have h := (((hasDerivAt_id s).add_const phase).const_mul (2 * Real.pi)).sin.div_const
      (2 * Real.pi)
    simpa only [id_eq, mul_one, mul_div_cancel_right₀ _ (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0)
      Real.pi_ne_zero)] using h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    ((show Continuous (fun s : ℝ => Real.cos (2 * Real.pi * (s + phase))) by
      fun_prop).intervalIntegrable 0 1)]
  have ha : 2 * Real.pi * (1 + phase) = 2 * Real.pi * phase + 2 * Real.pi := by ring
  simp only [zero_add, ha, Real.sin_add_two_pi, sub_self]

/-- A translation of a unit-frequency cell shear keeps its cosine-square average. -/
theorem cell_cosine_sq_mean (j : Fin 2) (phase : ℝ) :
    (∫ z in unitCube, Real.cos (2 * Real.pi * (z j + phase)) ^ 2) = (1 / 2 : ℝ) := by
  have he : (fun z : Vec 2 => Real.cos (2 * Real.pi * (z j + phase)) ^ 2) =
      fun z => Real.cos (2 * Real.pi * z j + 2 * Real.pi * phase) ^ 2 := by
    funext z
    congr 2
    ring
  rw [he]
  change spaceAvg (fun z : Vec 2 => Real.cos (2 * Real.pi * z j + 2 * Real.pi * phase) ^ 2) = _
  rw [AVenhance.Infra.Section3.spaceAvg_coordIntegral
    (F := fun s : ℝ => Real.cos (2 * Real.pi * s + 2 * Real.pi * phase) ^ 2)
    (by fun_prop) j]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo]
  simpa only [Nat.cast_one, mul_one] using
    AVenhance.Infra.FullTheorem.NoSelectionInputs.integral_cos_sq_phase 1 (by omega)
      (2 * Real.pi * phase)

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleDamping

/-! A common cubic remainder budget for every Taylor order and the full series. -/

/-- The geometric prefix bound retains the terminal power, uniformly in truncation order. -/
theorem geometric_prefix_budget {ρ : ℝ} (hρ : 0 ≤ ρ) (hhalf : ρ ≤ 1 / 2) (n : ℕ) :
    (∑ k ∈ Finset.range n, ρ ^ k) + 2 * ρ ^ n ≤ 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hp := pow_nonneg hρ n
    nlinarith only [ih, mul_le_mul_of_nonneg_left hhalf hp]

/-- Every finite Taylor tail shares one cubic budget. -/
theorem geometric_cubic_tail_finset {ρ C : ℝ} (hρ : 0 ≤ ρ) (hhalf : ρ ≤ 1 / 2)
    (hC : 0 ≤ C) (n : ℕ) :
    (∑ k ∈ Finset.range n, C * ρ ^ (k + 3)) ≤ 2 * C * ρ ^ 3 := by
  have hp := geometric_prefix_budget hρ hhalf n
  have hs : (∑ k ∈ Finset.range n, ρ ^ k) ≤ 2 := by
    linarith only [hp, pow_nonneg hρ n]
  calc
    _ = (C * ρ ^ 3) * (∑ k ∈ Finset.range n, ρ ^ k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [pow_add]
      ring
    _ ≤ (C * ρ ^ 3) * 2 := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

/-- The full Taylor tail has the same cubic budget as the finite tails. -/
theorem geometric_cubic_tail_tsum {ρ C : ℝ} (hρ : 0 ≤ ρ) (hhalf : ρ ≤ 1 / 2)
    (hC : 0 ≤ C) :
    Summable (fun k : ℕ => C * ρ ^ (k + 3)) ∧
      (∑' k : ℕ, C * ρ ^ (k + 3)) ≤ 2 * C * ρ ^ 3 := by
  have hlt : ρ < 1 := by linarith
  have hg := summable_geometric_of_lt_one hρ hlt
  have he : (fun k : ℕ => C * ρ ^ (k + 3)) = fun k => (C * ρ ^ 3) * ρ ^ k := by
    funext k
    rw [pow_add]
    ring
  rw [he]
  refine ⟨hg.mul_left _, ?_⟩
  rw [tsum_mul_left, tsum_geometric_of_lt_one hρ hlt]
  have hs : (1 - ρ)⁻¹ ≤ (2 : ℝ) := by
    rw [inv_eq_one_div, div_le_iff₀ (by linarith : 0 < 1 - ρ)]
    linarith
  exact (mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (by ring)

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
open scoped ENNReal
namespace AVRegularity.CycleDamping

/-! Quantitative exponential decay from a lower count of half-norm contractions. -/

theorem half_power_eq_exp (n : ℕ) :
    ((1 / 2 : ℝ≥0∞) ^ n) = ENNReal.ofReal (Real.exp (-Real.log 2 * (n : ℝ))) := by
  have he : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [mul_comm (-Real.log 2), Real.exp_nat_mul, he, ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

theorem half_power_decay (c S d : ℝ) (n : ℕ)
    (hcount : c * S / d ≤ (n : ℝ)) :
    (1 / 2 : ℝ≥0∞) ^ n ≤ ENNReal.ofReal (Real.exp (-(c * Real.log 2 / d) * S)) := by
  rw [half_power_eq_exp]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hcount hlog.le
  have he : -(c * Real.log 2 / d) * S = -Real.log 2 * (c * S / d) := by ring
  rw [he]
  linarith only [hm]

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleDamping

/-! Packing the marked intervals inside a complete pulse core. -/

/-- A core of length at least twice the mark length contains a proportional number of marks.
Adjacent closed marks are allowed to share an endpoint. -/
theorem interval_marks_exist (a b d : ℝ) (hd : 0 < d) (hlength : 2 * d ≤ b - a) :
    ∃ marks : Finset ℝ, (b - a) / (2 * d) ≤ (marks.card : ℝ) ∧
      (∀ x ∈ marks, a ≤ x ∧ x + d ≤ b) ∧
      ∀ x ∈ marks, ∀ y ∈ marks, x ≠ y → x + d ≤ y ∨ y + d ≤ x := by
  classical
  let N := ⌊(b - a) / d⌋₊
  let f : ℕ → ℝ := fun n => a + (n : ℝ) * d
  have hratio : 2 ≤ (b - a) / d := (le_div_iff₀ hd).2 hlength
  have hfloor : (N : ℝ) ≤ (b - a) / d := Nat.floor_le (by linarith)
  have hfloor' : (b - a) / d < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  have hinj : Function.Injective f := by
    intro n k h
    have he : (n : ℝ) * d = (k : ℝ) * d := by dsimp [f] at h; linarith
    have he' := (mul_right_cancel₀ hd.ne' he : (n : ℝ) = (k : ℝ))
    exact_mod_cast he'
  refine ⟨(Finset.range N).image f, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
    have he : (b - a) / (2 * d) = ((b - a) / d) / 2 := by ring
    rw [he]
    linarith
  · intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    have hn' : (n : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.mp hn
    have hN : (N : ℝ) * d ≤ b - a := (le_div_iff₀ hd).mp hfloor
    have hstep := mul_le_mul_of_nonneg_right hn' hd.le
    dsimp [f]
    constructor
    · exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg n) hd.le)
    · linarith
  · intro x hx y hy hxy
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
    have hne : n ≠ k := by intro he; exact hxy (congrArg f he)
    rcases lt_or_gt_of_ne hne with hnk | hkn
    · left
      have hs : (n : ℝ) + 1 ≤ k := by exact_mod_cast hnk
      have hm := mul_le_mul_of_nonneg_right hs hd.le
      dsimp [f]
      linarith
    · right
      have hs : (k : ℝ) + 1 ≤ n := by exact_mod_cast hkn
      have hm := mul_le_mul_of_nonneg_right hs hd.le
      dsimp [f]
      linarith

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
open scoped ENNReal
namespace AVRegularity.CycleDamping

/-! Accumulation of local contractions across finitely many ordered marks. -/

/-- Complementary intervals use only monotonicity; each marked interval contributes one factor. -/
theorem marked_contraction_of_local_bounds (N : ℝ → ℝ≥0∞) (d : ℝ)
    (hd : 0 < d) (ρ : ℝ≥0∞) (marks : Finset ℝ) :
    ∀ a b : ℝ, a ≤ b → AntitoneOn N (Set.Icc a b) →
      (∀ x ∈ marks, a ≤ x ∧ x + d ≤ b) →
      (∀ x ∈ marks, ∀ y ∈ marks, x < y → x + d ≤ y) →
      (∀ x ∈ marks, N (x + d) ≤ ρ * N x) →
      N b ≤ ρ ^ marks.card * N a := by
  classical
  induction marks using Finset.induction_on_max with
  | empty =>
      intro a b hab hN _ _ _
      simpa only [Finset.card_empty, pow_zero, one_mul] using hN ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  | insert x marks hmax ih =>
      intro a b hab hN hinside hsep hdrop
      have hx := hinside x (Finset.mem_insert_self _ _)
      have hxmem : x ∈ Set.Icc a b := ⟨hx.1, by linarith⟩
      have hsub : Set.Icc a x ⊆ Set.Icc a b := fun _ ht => ⟨ht.1, ht.2.trans hxmem.2⟩
      have hi : ∀ y ∈ marks, a ≤ y ∧ y + d ≤ x := by
        intro y hy
        exact ⟨(hinside y (Finset.mem_insert_of_mem hy)).1,
          hsep y (Finset.mem_insert_of_mem hy) x (Finset.mem_insert_self _ _) (hmax y hy)⟩
      have hh := ih a x hx.1 (hN.mono hsub) hi
        (fun y hy z hz => hsep y (Finset.mem_insert_of_mem hy) z (Finset.mem_insert_of_mem hz))
        (fun y hy => hdrop y (Finset.mem_insert_of_mem hy))
      have he := hdrop x (Finset.mem_insert_self _ _)
      have hn := hN ⟨by linarith, hx.2⟩ ⟨hab, le_rfl⟩ hx.2
      have hnot : x ∉ marks := fun hm => (lt_irrefl x) (hmax x hm)
      rw [Finset.card_insert_of_notMem hnot, pow_succ]
      calc
        N b ≤ N (x + d) := hn
        _ ≤ ρ * N x := he
        _ ≤ ρ * (ρ ^ marks.card * N a) := mul_le_mul_right hh ρ
        _ = _ := by ac_rfl

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleDamping

/-! Uniform shear observability constants from a positive lower coupling bound. -/

theorem uniform_shear_constants (K₀ : ℝ) (hK₀ : 0 < K₀) :
    ∃ L d : ℝ, 0 < L ∧ 0 < d ∧ ∀ K : ℝ, K₀ ≤ K →
      28 * Real.pi ^ 2 + K ≤ K * L ∧
      4 * (16 * Real.pi ^ 2 + 4 * K * (10 + 32 * L ^ 2)) ≤ K * Real.pi ^ 2 * d := by
  let L := 1 + 28 * Real.pi ^ 2 / K₀
  let D := 10 + 32 * L ^ 2
  let H := 16 / K₀ + 4 * D / Real.pi ^ 2
  have hπ : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  have hL : 0 < L := by dsimp [L]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hH : 0 < H := by dsimp [H]; positivity
  refine ⟨L, 4 * H, hL, by positivity, ?_⟩
  intro K hK
  have h28 := mul_le_mul_of_nonneg_right hK (by positivity : 0 ≤ 28 * Real.pi ^ 2 / K₀)
  have hc28 : K₀ * (28 * Real.pi ^ 2 / K₀) = 28 * Real.pi ^ 2 := by field_simp
  rw [hc28] at h28
  constructor
  · dsimp [L]
    nlinarith only [h28]
  · have h16 := mul_le_mul_of_nonneg_right hK (by positivity : 0 ≤ 16 / K₀)
    have hc16 : K₀ * (16 / K₀) = 16 := by field_simp
    rw [hc16] at h16
    have hp := mul_le_mul_of_nonneg_left h16 hπ.le
    have hcD : Real.pi ^ 2 * (4 * D / Real.pi ^ 2) = 4 * D := by field_simp
    have he : K * Real.pi ^ 2 * H = K * Real.pi ^ 2 * (16 / K₀) + K * (4 * D) := by
      dsimp [H]
      rw [mul_add]
      simp_rw [mul_assoc]
      rw [hcD]
    change 4 * (16 * Real.pi ^ 2 + 4 * K * D) ≤ K * Real.pi ^ 2 * (4 * H)
    nlinarith only [hp, he]

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleDamping

/-! Absorbing the common cubic remainder after integrating the quadratic coercivity. -/

/-- The real part of a uniformly bounded remainder accumulates only interval length. -/
theorem interval_remainder_real_bound (f : ℝ → ℂ) (a b K : ℝ)
    (hab : a ≤ b) (hf : ∀ t ∈ Set.uIoc a b, ‖f t‖ ≤ K) :
    (∫ t in a..b, f t).re ≤ K * (b - a) := by
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const hf
  rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hn
  exact (Complex.re_le_norm _).trans (by simpa only [mul_comm] using hn)

/-- The same radius absorbs either a full-symbol or finite-Taylor cubic remainder. -/
theorem low_damping_of_quadratic_and_cubic (Q R : ℝ → ℂ) (a b c K x : ℝ)
    (hab : a ≤ b) (hsmall : K * x ≤ c / 4)
    (hQ : IntervalIntegrable Q volume a b) (hR : IntervalIntegrable R volume a b)
    (hquadratic : (∫ t in a..b, Q t).re ≤ -(3 * c / 4) * (b - a) * x ^ 2)
    (hremainder : ∀ t ∈ Set.uIoc a b, ‖R t‖ ≤ K * x ^ 3) :
    (∫ t in a..b, Q t + R t).re ≤ -(c / 2) * (b - a) * x ^ 2 := by
  rw [intervalIntegral.integral_add hQ hR, Complex.add_re]
  have hr := interval_remainder_real_bound R a b (K * x ^ 3) hab hremainder
  have hs := mul_le_mul_of_nonneg_right hsmall
    (mul_nonneg (sub_nonneg.mpr hab) (sq_nonneg x))
  nlinarith only [hquadratic, hr, hs]

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping

/-! Integration by parts for two genuine absolutely continuous complex moments. -/

theorem complex_time_add {a b : ℝ} {u du v dv : ℝ → ℂ}
    (hu : StrongTimeRegularity a b u du) (hv : StrongTimeRegularity a b v dv) :
    StrongTimeRegularity a b (fun t => u t + v t) (fun t => du t + dv t) := by
  refine ⟨hu.ac.fun_add hv.ac, ?_⟩
  filter_upwards [hu.derivative, hv.derivative] with t hut hvt
  simpa only [Pi.add_def] using hut.add hvt

theorem complex_time_inner {a b : ℝ} {u du v dv : ℝ → ℂ}
    (hu : StrongTimeRegularity a b u du) (hv : StrongTimeRegularity a b v dv) :
    StrongTimeRegularity a b (fun t => inner ℝ (u t) (v t))
      (fun t => inner ℝ (du t) (v t) + inner ℝ (u t) (dv t)) := by
  have hs := complex_time_add hu hv
  have ha := ((hs.norm_sq_ac.sub hu.norm_sq_ac).sub hv.norm_sq_ac).const_mul (1 / 2 : ℝ)
  have he (t : ℝ) : (1 / 2 : ℝ) *
      ((‖u t + v t‖ ^ 2 - ‖u t‖ ^ 2) - ‖v t‖ ^ 2) = inner ℝ (u t) (v t) := by
    rw [norm_add_sq_real]; ring
  refine ⟨ha.congr (fun t _ => he t), ?_⟩
  filter_upwards [hu.derivative, hv.derivative] with t hut hvt
  simpa only [add_comm] using hut.inner ℝ hvt

theorem complex_time_inner_increment {a b : ℝ} {u du v dv : ℝ → ℂ}
    (hu : StrongTimeRegularity a b u du) (hv : StrongTimeRegularity a b v dv) :
    inner ℝ (u b) (v b) - inner ℝ (u a) (v a) =
      ∫ t in a..b, inner ℝ (du t) (v t) + inner ℝ (u t) (dv t) := by
  have hh := complex_time_inner hu hv
  have he := hh.ac.integral_deriv_eq_sub
  have hd := hh.derivative.filter_mono
    (ae_mono (Measure.restrict_mono uIoc_subset_uIcc le_rfl))
  have heq : (fun t => deriv (fun s => inner ℝ (u s) (v s)) t) =ᵐ[
      volume.restrict (uIoc a b)] (fun t => inner ℝ (du t) (v t) + inner ℝ (u t) (dv t)) := by
    filter_upwards [hd] with t ht
    exact ht.deriv
  rw [intervalIntegral.integral_congr_ae_restrict heq] at he
  exact he.symm

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleDamping

/-! Assemble separately packed cores without losing marks or their separation. -/

/-- Packing separated cores gives the sum of their mark counts. -/
theorem separated_interval_marks {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a b : ι → ℝ) (d : ℝ) (hd : 0 < d)
    (hlength : ∀ k ∈ S, 2 * d ≤ b k - a k)
    (hsep : ∀ k ∈ S, ∀ j ∈ S, k ≠ j → b k ≤ a j ∨ b j ≤ a k) :
    ∃ marks : Finset ℝ,
      (∑ k ∈ S, (b k - a k) / (2 * d)) ≤ (marks.card : ℝ) ∧
      (∀ x ∈ marks, ∃ k ∈ S, a k ≤ x ∧ x + d ≤ b k) ∧
      ∀ x ∈ marks, ∀ y ∈ marks, x ≠ y → x + d ≤ y ∨ y + d ≤ x := by
  classical
  have hex (k : ι) : ∃ marks : Finset ℝ,
      k ∈ S → (b k - a k) / (2 * d) ≤ (marks.card : ℝ) ∧
        (∀ x ∈ marks, a k ≤ x ∧ x + d ≤ b k) ∧
        ∀ x ∈ marks, ∀ y ∈ marks, x ≠ y → x + d ≤ y ∨ y + d ≤ x := by
    by_cases hk : k ∈ S
    · obtain ⟨marks, hm⟩ := interval_marks_exist (a k) (b k) d hd (hlength k hk)
      exact ⟨marks, fun _ => hm⟩
    · exact ⟨∅, fun h => (hk h).elim⟩
  choose f hf using hex
  have hdis : Set.PairwiseDisjoint (↑S : Set ι) f := by
    intro k hk j hj hne
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    have hkx := (hf k hk).2.1 x hx
    have hjx := (hf j hj).2.1 x hx'
    rcases hsep k hk j hj hne with hs | hs <;> linarith
  refine ⟨S.biUnion f, ?_, ?_, ?_⟩
  · rw [Finset.card_biUnion hdis, Nat.cast_sum]
    exact Finset.sum_le_sum (fun k hk => (hf k hk).1)
  · intro x hx
    obtain ⟨k, hk, hx⟩ := Finset.mem_biUnion.mp hx
    exact ⟨k, hk, (hf k hk).2.1 x hx⟩
  · intro x hx y hy hxy
    obtain ⟨k, hk, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨j, hj, hy⟩ := Finset.mem_biUnion.mp hy
    by_cases hkj : k = j
    · subst j
      exact (hf k hk).2.2 x hx y hy hxy
    · have hkx := (hf k hk).2.1 x hx
      have hjy := (hf j hj).2.1 y hy
      rcases hsep k hk j hj hkj with hs | hs
      · exact Or.inl (hkx.2.trans (hs.trans hjy.1))
      · exact Or.inr (hjy.2.trans (hs.trans hkx.1))

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping

/-! Complex time calculus through the real and imaginary scalar curves. -/

theorem real_time_map_complex {a b : ℝ} {f df : ℝ → ℝ}
    (h : StrongTimeRegularity a b f df) (L : ℝ →L[ℝ] ℂ) :
    StrongTimeRegularity a b (fun t => L (f t)) (fun t => L (df t)) := by
  refine ⟨L.lipschitzWith.comp_absolutelyContinuousOnInterval h.ac, ?_⟩
  filter_upwards [h.derivative] with t ht
  exact L.hasFDerivAt.comp_hasDerivAt t ht

theorem complex_time_from_components {a b : ℝ} {f df : ℝ → ℂ}
    (hr : StrongTimeRegularity a b (fun t => (f t).re) (fun t => (df t).re))
    (hi : StrongTimeRegularity a b (fun t => (f t).im) (fun t => (df t).im)) :
    StrongTimeRegularity a b f df := by
  let L : ℝ →L[ℝ] ℂ := (ContinuousLinearMap.mul ℝ ℂ Complex.I).comp Complex.ofRealCLM
  have hrc := real_time_map_complex hr Complex.ofRealCLM
  have hic := real_time_map_complex hi L
  have he (z : ℂ) : Complex.ofRealCLM z.re + L z.im = z := by
    change (z.re : ℂ) + Complex.I * (z.im : ℂ) = z
    apply Complex.ext <;> simp
  refine ⟨?_, ?_⟩
  · exact (hrc.ac.fun_add hic.ac).congr (fun t _ => he (f t))
  · filter_upwards [hrc.derivative, hic.derivative] with t hrt hit
    have hh := hrt.add hit
    simpa only [Pi.add_def, he] using hh

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance
namespace AVRegularity.CycleDamping

/-! The covariance of an isolated shear on a cell centered at an arbitrary point. -/

/-- The mean square velocity amplitude is exactly the relaxation rate times enhancement. -/
theorem shear_square_amplitude {α q : ℝ} {Λ m : ℕ} {ν : ℝ}
    (hΛ : 1 ≤ Λ) (hν : 0 < ν) :
    (2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) * (ocEpsilon q Λ m)⁻¹) ^ 2 / 2 =
      ocMu q Λ m ν * ocHStar α q Λ m ν := by
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  have hp : ocEpsilon q Λ m ^ (2 * (1 + α)) = (ocEpsilon q Λ m ^ (1 + α)) ^ 2 := by
    rw [show 2 * (1 + α) = (1 + α) * 2 by ring]
    exact Real.rpow_mul_natCast he.le (1 + α) 2
  rw [ocMu, ocHStar, hp]
  field_simp
  ring

/-- The cell shear covariance is independent of the chosen center. -/
theorem cell_shear_covariance {α q : ℝ} {Λ m : ℕ} {ν : ℝ}
    (hΛ : 1 ≤ Λ) (hν : 0 < ν) (k : {k : ℤ // Odd k}) (y₀ : Vec 2) (i j : Fin 2) :
    (∫ z in unitCube,
      ocShearVel α q Λ m k.1 (y₀ + ocEpsilon q Λ m • z) i *
        ocShearVel α q Λ m k.1 (y₀ + ocEpsilon q Λ m • z) j) =
      (ocMu q Λ m ν * ocHStar α q Λ m ν) * ocPi k i j := by
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  have hphase (z : Vec 2) (a : Fin 2) :
      2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * (y₀ + ocEpsilon q Λ m • z) a =
        2 * Real.pi * (z a + (ocEpsilon q Λ m)⁻¹ * y₀ a) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  have hmean (a : Fin 2) :
      (∫ z in unitCube,
        (2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) * (ocEpsilon q Λ m)⁻¹ *
          Real.cos (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ *
            (y₀ + ocEpsilon q Λ m • z) a)) ^ 2) =
        ocMu q Λ m ν * ocHStar α q Λ m ν := by
    simp_rw [hphase, mul_pow]
    rw [integral_const_mul, cell_cosine_sq_mean]
    convert shear_square_amplitude (α := α) (q := q) (m := m) hΛ hν using 1
    ring
  rcases CycleReference.odd_int_mod_four k.2 with h1 | h3
  · fin_cases i <;> fin_cases j <;>
      norm_num [CycleReference.ocShearVel_horizontal h1, ocPi, h1]
    simpa only [← pow_two, mul_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hmean 0
  · have h1 : ¬ k.1 % 4 = 1 := by omega
    fin_cases i <;> fin_cases j <;>
      norm_num [CycleReference.ocShearVel_vertical h3, ocPi, h1]
    simpa only [neg_mul_neg, ← pow_two, mul_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hmean 1

end AVRegularity.CycleDamping
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity.CycleDamping

/-! Numerical spectral gaps for Bloch frequencies in the first Brillouin cell. -/

theorem brillouin_nonzero_coordinate_gap (n : ℤ) (hn : n ≠ 0) (θ : ℝ)
    (hθ : |θ| ≤ Real.pi) :
    Real.pi ≤ |2 * Real.pi * (n : ℝ) + θ| := by
  have hnabs : (1 : ℝ) ≤ |(n : ℝ)| := by
    exact_mod_cast Int.one_le_abs hn
  have htri : |2 * Real.pi * (n : ℝ)| ≤
      |2 * Real.pi * (n : ℝ) + θ| + |θ| := by
    have hh := abs_sub (2 * Real.pi * (n : ℝ) + θ) θ
    simpa only [add_sub_cancel_right] using hh
  rw [abs_mul, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)] at htri
  have hb := mul_le_mul_of_nonneg_left hnabs
    (show 0 ≤ 2 * Real.pi by positivity)
  nlinarith only [htri, hb, hθ]

theorem brillouin_coordinate_sq_bound (n : ℤ) (θ : ℝ) (hθ : |θ| ≤ Real.pi) :
    θ ^ 2 ≤ (2 * Real.pi * (n : ℝ) + θ) ^ 2 := by
  by_cases hn : n = 0
  · subst n; simp
  · have hg := brillouin_nonzero_coordinate_gap n hn θ hθ
    have hle := hθ.trans hg
    nlinarith only [hle, abs_nonneg θ,
      abs_nonneg (2 * Real.pi * (n : ℝ) + θ), sq_abs θ,
      sq_abs (2 * Real.pi * (n : ℝ) + θ)]

theorem brillouin_frequency_sq_bound (n : Fin 2 → ℤ) (θ : Vec 2)
    (hθ : ∀ j, |θ j| ≤ Real.pi) :
    (∑ j, θ j ^ 2) ≤ ∑ j, (2 * Real.pi * (n j : ℝ) + θ j) ^ 2 := by
  apply Finset.sum_le_sum
  intro j _
  exact brillouin_coordinate_sq_bound (n j) (θ j) (hθ j)

theorem brillouin_mean_free_gap (n : Fin 2 → ℤ) (hn : n ≠ 0) (θ : Vec 2)
    (hθ : ∀ j, |θ j| ≤ Real.pi) :
    Real.pi ^ 2 ≤ ∑ j, (2 * Real.pi * (n j : ℝ) + θ j) ^ 2 := by
  have hsome : ∃ j, n j ≠ 0 := by
    by_contra! h
    exact hn (funext h)
  obtain ⟨j, hj⟩ := hsome
  have hg := brillouin_nonzero_coordinate_gap (n j) hj (θ j) (hθ j)
  have hs : Real.pi ^ 2 ≤ (2 * Real.pi * (n j : ℝ) + θ j) ^ 2 := by
    nlinarith only [hg, Real.pi_pos, abs_nonneg (2 * Real.pi * (n j : ℝ) + θ j),
      sq_abs (2 * Real.pi * (n j : ℝ) + θ j)]
  exact hs.trans (Finset.single_le_sum (fun i _ => sq_nonneg (2 * Real.pi * (n i : ℝ) + θ i)) (Finset.mem_univ j))

/-! The identity metric satisfies the actual cell metric predicate. -/

theorem identity_isCellMetric : IsCellMetric (fun _ _ => 1) := by
  refine ⟨measurable_const, (fun _ _ _ => rfl), (fun _ _ => Matrix.isSymm_one), ?_⟩
  intro t x ξ
  have hn : 0 ≤ ∑ i : Fin 2, ξ i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (ξ i))
  have he : (∑ i, ∑ j, ξ i * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j * ξ j) =
      ∑ i : Fin 2, ξ i ^ 2 := by
    simp only [Fin.sum_univ_two, Matrix.one_apply]
    norm_num
    ring
  rw [he]
  constructor <;> linarith only [hn]

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleDamping

/-! The public complex frequency norm on the real slice. -/

theorem real_frequency_eq (ξ : Fin 2 → ℂ) (hξ : ∀ i, (ξ i).im = 0) :
    ξ = fun i => ((ξ i).re : ℂ) := by
  funext i
  apply Complex.ext <;> simp [hξ i]

theorem real_frequency_norm_sq (ξ : Fin 2 → ℂ) (hξ : ∀ i, (ξ i).im = 0) :
    fibreNorm ξ ^ 2 = vecDot (fun i => (ξ i).re) (fun i => (ξ i).re) := by
  rw [real_frequency_eq ξ hξ]
  unfold fibreNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
  simp only [Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs, sq_abs, vecDot, ← sq]

theorem low_radius_budget (ξ₀ Cg c : ℝ) (hξ₀ : 0 < ξ₀) (hCg : 0 < Cg) (hc : 0 < c) :
    ∃ ξmax : ℝ, 0 < ξmax ∧ ξmax < ξ₀ ∧ ξmax ≤ ξ₀ / 4 ∧
      ∀ x : ℝ, x ≤ ξmax → (2 * Cg * (2 / ξ₀) ^ 3) * x ≤ c / 4 := by
  let K : ℝ := 2 * Cg * (2 / ξ₀) ^ 3
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨min (ξ₀ / 8) (c / (4 * K)), lt_min (by positivity) (by positivity), ?_, ?_, ?_⟩
  · exact (min_le_left _ _).trans_lt (by linarith)
  · exact (min_le_left _ _).trans (by linarith)
  · intro x hx
    have he := mul_le_mul_of_nonneg_left (hx.trans (min_le_right _ _)) hK.le
    have hh : K * (c / (4 * K)) = c / 4 := by field_simp
    exact he.trans_eq hh

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance.Infra.Torus
namespace AVRegularity.CycleDamping

/-! Literal Fourier multipliers for smooth shifted derivatives. -/

theorem continuous_integrableOn_unitCell {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : Vec 2 → E) (hf : Continuous f) :
    IntegrableOn f (unitCell 2) := by
  apply (FourierCalculus.continuous_integrableOn_closedCell hf).mono_set
  intro x hx
  simp only [unitCell, unitCellAt, Set.mem_ofPred_eq, zero_add] at hx
  simp only [FourierCalculus.closedCell, Set.mem_pi, Set.mem_univ, forall_true_left]
  intro j
  exact ⟨(hx j).1.le, (hx j).2⟩

theorem smoothFourierCoeff_add_scalar (f g : Vec 2 → ℂ)
    (hf : Continuous f) (hg : Continuous g) (a : ℂ) (k : Fin 2 → ℤ) :
    smoothFourierCoeff (fun x => f x + a * g x) k =
      smoothFourierCoeff f k + a * smoothFourierCoeff g k := by
  have hchar := (torusCharacter_contDiff k).continuous
  have hfi : IntegrableOn (fun x => torusCharacter k x * f x) (unitCell 2) := by
    simpa only [Pi.mul_def] using continuous_integrableOn_unitCell _ (hchar.mul hf)
  have hgi : IntegrableOn (fun x => torusCharacter k x * g x) (unitCell 2) := by
    simpa only [Pi.mul_def] using continuous_integrableOn_unitCell _ (hchar.mul hg)
  have he : (fun x => torusCharacter k x * (f x + a * g x)) =
      (fun x => torusCharacter k x * f x + a * (torusCharacter k x * g x)) := by
    funext x; ring
  rw [smoothFourierCoeff, he, integral_add hfi (hgi.const_mul a), integral_const_mul]
  rfl

def smoothShiftedDerivative (θ : Vec 2) (j : Fin 2) (f : Vec 2 → ℂ) : Vec 2 → ℂ :=
  fun x => coordDeriv j f x + Complex.I * (θ j : ℂ) * f x

theorem smoothShiftedDerivative_continuous (θ : Vec 2) (j : Fin 2)
    {f : Vec 2 → ℂ} (hf : ContDiff ℝ 1 f) :
    Continuous (smoothShiftedDerivative θ j f) :=
  (continuous_coordDeriv j hf).add (continuous_const.mul hf.continuous)

theorem smoothFourierCoeff_shiftedDerivative (θ : Vec 2) (j : Fin 2)
    {f : Vec 2 → ℂ} (hf : ContDiff ℝ 1 f) (hp : AVenhance.IsZ2Periodic f)
    (k : Fin 2 → ℤ) :
    smoothFourierCoeff (smoothShiftedDerivative θ j f) k =
      Complex.I * ((2 * Real.pi * (k j : ℝ) + θ j : ℝ) : ℂ) * smoothFourierCoeff f k := by
  change smoothFourierCoeff (fun x => coordDeriv j f x +
    (Complex.I * (θ j : ℂ)) * f x) k = _
  rw [smoothFourierCoeff_add_scalar _ _
    (continuous_coordDeriv j hf) hf.continuous,
    smoothFourierCoeff_coordDeriv j hf hp]
  push_cast
  ring

/-! Parseval turns Brillouin inequalities into genuine smooth-cell dissipation bounds. -/

theorem smoothShiftedGradient_parseval (θ : Vec 2) {f : Vec 2 → ℂ}
    (hf : ContDiff ℝ 1 f) :
    HasSum (fun k : Fin 2 → ℤ => ∑ j : Fin 2,
      ‖smoothFourierCoeff (smoothShiftedDerivative θ j f) k‖ ^ 2)
      (∑ j : Fin 2, ∫ x in unitCell 2, ‖smoothShiftedDerivative θ j f x‖ ^ 2) := by
  apply FourierCalculus.hasSum_finset_sum Finset.univ
  intro j _
  exact hasSum_sq_smoothFourierCoeff (smoothShiftedDerivative_continuous θ j hf)

theorem smoothShiftedGradient_coefficient_energy (θ : Vec 2) {f : Vec 2 → ℂ}
    (hf : ContDiff ℝ 1 f) (hp : AVenhance.IsZ2Periodic f) (k : Fin 2 → ℤ) :
    (∑ j : Fin 2, ‖smoothFourierCoeff (smoothShiftedDerivative θ j f) k‖ ^ 2) =
      (∑ j : Fin 2, (2 * Real.pi * (k j : ℝ) + θ j) ^ 2) *
        ‖smoothFourierCoeff f k‖ ^ 2 := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [smoothFourierCoeff_shiftedDerivative θ j hf hp]
  rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, sq_abs]

theorem smoothShiftedGradient_frequency_gap (θ : Vec 2)
    (hθ : ∀ j, |θ j| ≤ Real.pi) {f : Vec 2 → ℂ}
    (hf : ContDiff ℝ 1 f) (hp : AVenhance.IsZ2Periodic f) :
    (∑ j, θ j ^ 2) * (∫ x in unitCell 2, ‖f x‖ ^ 2) ≤
      ∑ j : Fin 2, ∫ x in unitCell 2, ‖smoothShiftedDerivative θ j f x‖ ^ 2 := by
  apply hasSum_le _ ((hasSum_sq_smoothFourierCoeff hf.continuous).mul_left (∑ j, θ j ^ 2))
    (smoothShiftedGradient_parseval θ hf)
  intro k
  rw [smoothShiftedGradient_coefficient_energy θ hf hp k]
  exact mul_le_mul_of_nonneg_right (brillouin_frequency_sq_bound k θ hθ) (sq_nonneg _)

theorem smoothShiftedGradient_meanZero_gap (θ : Vec 2)
    (hθ : ∀ j, |θ j| ≤ Real.pi) {f : Vec 2 → ℂ}
    (hf : ContDiff ℝ 1 f) (hp : AVenhance.IsZ2Periodic f)
    (hm : ∫ x in unitCell 2, f x = 0) :
    Real.pi ^ 2 * (∫ x in unitCell 2, ‖f x‖ ^ 2) ≤
      ∑ j : Fin 2, ∫ x in unitCell 2, ‖smoothShiftedDerivative θ j f x‖ ^ 2 := by
  have hz : smoothFourierCoeff f (0 : Fin 2 → ℤ) = 0 := by
    rw [FourierCalculus.smoothFourierCoeff_zero_eq_integral]; exact hm
  apply hasSum_le _ ((hasSum_sq_smoothFourierCoeff hf.continuous).mul_left (Real.pi ^ 2))
    (smoothShiftedGradient_parseval θ hf)
  intro k
  rw [smoothShiftedGradient_coefficient_energy θ hf hp k]
  by_cases hk : k = 0
  · subst k; simp [hz]
  · exact mul_le_mul_of_nonneg_right (brillouin_mean_free_gap k hk θ hθ) (sq_nonneg _)

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.CycleDamping

/-! Spatial chain rules for the translated cell coordinates. -/

theorem affine_coord_derivative (f : Vec 2 → ℝ) (hf : Differentiable ℝ f)
    (e : ℝ) (y₀ x : Vec 2) (i : Fin 2) :
    fderiv ℝ (fun z => f (y₀ + e • z)) x (basisVec i) =
      e * fderiv ℝ f (y₀ + e • x) (basisVec i) := by
  have hi : HasFDerivAt (id : Vec 2 → Vec 2) (ContinuousLinearMap.id ℝ (Vec 2)) x :=
    hasFDerivAt_id x
  have ha := (hi.const_smul e).const_add y₀
  have hh : HasFDerivAt (fun z => f (y₀ + e • z))
      ((fderiv ℝ f (y₀ + e • x)).comp (e • ContinuousLinearMap.id ℝ (Vec 2))) x := by
    simpa only [Function.comp_def, Pi.smul_apply, id_eq] using (hf _).hasFDerivAt.comp x ha
  rw [hh.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]

theorem affine_coord_derivative_fun (f : Vec 2 → ℝ) (hf : Differentiable ℝ f)
    (e : ℝ) (y₀ : Vec 2) (i : Fin 2) :
    (fun x => fderiv ℝ (fun z => f (y₀ + e • z)) x (basisVec i)) =
      fun x => e * fderiv ℝ f (y₀ + e • x) (basisVec i) := by
  funext x
  exact affine_coord_derivative f hf e y₀ x i

theorem affine_second_derivative (f : Vec 2 → ℝ) (hf : ContDiff ℝ 2 f)
    (e : ℝ) (y₀ x : Vec 2) (i : Fin 2) :
    fderiv ℝ (fun z => fderiv ℝ (fun y => f (y₀ + e • y)) z (basisVec i)) x
      (basisVec i) = e ^ 2 * fderiv ℝ (fun z => fderiv ℝ f z (basisVec i))
        (y₀ + e • x) (basisVec i) := by
  rw [affine_coord_derivative_fun f (hf.differentiable (by norm_num)) e y₀ i]
  have hd : Differentiable ℝ (fun z => fderiv ℝ f z (basisVec i)) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) |>.clm_apply
      (differentiable_const _)
  have ha : Differentiable ℝ (fun z => fderiv ℝ f (y₀ + e • z) (basisVec i)) :=
    hd.comp (by fun_prop)
  rw [fderiv_const_mul (ha x)]
  simp only [smul_apply, smul_eq_mul]
  rw [affine_coord_derivative _ hd e y₀ x i]
  ring

theorem affine_laplacian (f : Vec 2 → ℝ) (hf : ContDiff ℝ 2 f)
    (e : ℝ) (y₀ x : Vec 2) :
    (∑ i : Fin 2, fderiv ℝ (fun z => fderiv ℝ (fun y => f (y₀ + e • y)) z
      (basisVec i)) x (basisVec i)) =
      e ^ 2 * ∑ i : Fin 2, fderiv ℝ (fun z => fderiv ℝ f z (basisVec i))
        (y₀ + e • x) (basisVec i) := by
  simp_rw [affine_second_derivative f hf, Finset.mul_sum]

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleDamping

/-! The bilinear quadratic tensor identity used in the damping bridge.
Symmetrization is valid for complex frequencies: no complex conjugate occurs. -/

/-- Expansion of the corrector bridge into its molecular and unsymmetrized terms. -/
theorem fibreBridgeMatrix_quadratic (η : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (χ : Fin 2 → ℝ → RawJet2 1 ℂ) (t : ℝ) (ξ : Fin 2 → ℂ) :
    (∑ i, ∑ j, ξ i * fibreBridgeMatrix η G v χ t i j * ξ j) =
      (η : ℂ) * fibreQuad (G t) ξ +
        ∑ i, ∑ j, ξ i *
          cellMean (fun x => ((Real.sqrt η * v t x i : ℝ) : ℂ) *
            cellValue (χ j) t x) * ξ j := by
  simp only [fibreBridgeMatrix, fibreQuad, Fin.sum_univ_two]
  ring

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleDamping

/-! The quantitative supply of marked intervals in either orientation of a renewal block. -/

/-- Every orientation supplies at least `h/(96 d)` marks when the pulse time is at least `3d`. -/
theorem complete_core_marks {α q : ℝ} {Λ m : ℕ}
    (hΛ : 1 ≤ Λ) (l r : ℤ) (hr : r = 1 ∨ r = 3)
    (d : ℝ) (hd : 0 < d) (hτd : 3 * d ≤ ocTau α q Λ m) :
    ∃ marks : Finset ℝ, ocTauPP α q Λ m / (96 * d) ≤ (marks.card : ℝ) ∧
      (∀ x ∈ marks,
        (((l : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ x ∧
          x + d ≤ ((l : ℝ) + 1 / 2) * ocTauPP α q Λ m) ∧
        ∃ k : ℤ, k % 4 = r ∧ IsOCCompleteCore α q Λ m l k ∧
          ((k : ℝ) - 1 / 3) * ocTau α q Λ m ≤ x ∧
          x + d ≤ ((k : ℝ) + 1 / 3) * ocTau α q Λ m) ∧
      ∀ x ∈ marks, ∀ y ∈ marks, x ≠ y → x + d ≤ y ∨ y + d ≤ x := by
  have hτ := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
  obtain ⟨S, hcard, hS⟩ := CycleReference.complete_cores_exist (α := α) (q := q)
    (m := m) hΛ l r hr
  let a : ℤ → ℝ := fun k => ((k : ℝ) - 1 / 3) * ocTau α q Λ m
  let b : ℤ → ℝ := fun k => ((k : ℝ) + 1 / 3) * ocTau α q Λ m
  have hlength (k : ℤ) : 2 * d ≤ b k - a k := by dsimp [a, b]; linarith
  have hsep (k : ℤ) (_hk : k ∈ S) (j : ℤ) (_hj : j ∈ S) (hne : k ≠ j) :
      b k ≤ a j ∨ b j ≤ a k := by
    rcases lt_or_gt_of_ne hne with hkj | hjk
    · left
      have hs : (k : ℝ) + 1 ≤ j := by exact_mod_cast (show k + 1 ≤ j by omega)
      have hm := mul_le_mul_of_nonneg_right hs hτ.le
      dsimp [a, b]
      linarith
    · right
      have hs : (j : ℝ) + 1 ≤ k := by exact_mod_cast (show j + 1 ≤ k by omega)
      have hm := mul_le_mul_of_nonneg_right hs hτ.le
      dsimp [a, b]
      linarith
  obtain ⟨marks, hn, hm, hs⟩ := separated_interval_marks S a b d hd
    (fun k _ => hlength k) hsep
  refine ⟨marks, ?_, ?_, hs⟩
  · have hscale : (ocL α q Λ m : ℝ) ^ 2 * ocTau α q Λ m = ocTauPP α q Λ m := by
      unfold ocTau
      have hL : (ocL α q Λ m : ℝ) ≠ 0 := by
        have hp : 0 < ocL α q Λ m := by unfold ocL; omega
        exact_mod_cast hp.ne'
      field_simp
    have hsum : (∑ k ∈ S, (b k - a k) / (2 * d)) =
        (S.card : ℝ) * ocTau α q Λ m / (3 * d) := by
      have ht (k : ℤ) : (b k - a k) / (2 * d) = ocTau α q Λ m / (3 * d) := by
        dsimp [a, b]
        ring
      simp only [ht, Finset.sum_const, nsmul_eq_mul]
      ring
    rw [hsum] at hn
    have hc := mul_le_mul_of_nonneg_right hcard
      (show 0 ≤ ocTau α q Λ m / (3 * d) by positivity)
    calc
      _ = ((ocL α q Λ m : ℝ) ^ 2 / 32) * (ocTau α q Λ m / (3 * d)) := by
        rw [← hscale]
        ring
      _ ≤ _ := hc
      _ = (S.card : ℝ) * ocTau α q Λ m / (3 * d) := by ring
      _ ≤ _ := hn
  · intro x hx
    obtain ⟨k, hk, hax, hxb⟩ := hm x hx
    have hcore := (hS k hk).2
    have hxx : x ∈ Set.Icc (a k) (b k) := ⟨hax, by linarith⟩
    have hxd : x + d ∈ Set.Icc (a k) (b k) := ⟨by linarith, hxb⟩
    have hlo := (CycleReference.slowEnvelope_one_inside_block hΛ l x
      (hcore.2.2 x hxx)).1
    have hhi := (CycleReference.slowEnvelope_one_inside_block hΛ l (x + d)
      (hcore.2.2 (x + d) hxd)).2
    exact ⟨⟨hlo, hhi⟩, k, (hS k hk).1, hcore, hax, hxb⟩

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleDamping

/-! Reference-flux coercivity as a quadratic form on every renewal block. -/

/-- The block estimate has three times the admissibility constant. -/
theorem renewal_block_flux_coercivity {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (hrelax : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m) (l : ℤ) (w : Vec 2) :
    (1 - Real.exp (-2)) / 96 * ocMeanFlux α q Λ ζ m ν * ocTauPP α q Λ m * vecDot w w ≤
      ∫ t in (((l : ℝ) - 1 / 2) * ocTauPP α q Λ m)..
        (((l : ℝ) + 1 / 2) * ocTauPP α q Λ m),
        vecDot w ((ocRefFlux α q Λ ζ m ν t).mulVec w) := by
  let c := (1 - Real.exp (-2)) / 96
  let a := ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m
  let b := ((l : ℝ) + 1 / 2) * ocTauPP α q Λ m
  have hc : 0 < c := CycleReference.core_coercivity_constant_range.1
  have hc1 : c ≤ 1 := CycleReference.core_coercivity_constant_range.2
  have hh := AVRegularity.Construction.Stream.ocTauPP_pos (α := α) (q := q) (m := m) hΛ
  have hB := (CycleReference.refFlux_mean_core_bounds hΛ hζ hν hrelax).2
  have hb (i : Fin 2) : c * ocMeanFlux α q Λ ζ m ν * ocTauPP α q Λ m ≤
      ∫ t in a..b, ocRefFlux α q Λ ζ m ν t i i := by
    have hi := CycleReference.refFlux_block_diagonal_lower hΛ hζ hν hrelax l i
    have hcoef : c * ocMeanFlux α q Λ ζ m ν ≤ ν + c * ocHStar α q Λ m ν := by
      have hx := mul_le_mul_of_nonneg_left hB hc.le
      have hy := mul_le_mul_of_nonneg_right hc1 hν.le
      linarith
    exact (mul_le_mul_of_nonneg_right hcoef hh.le).trans hi
  have he : (fun t => vecDot w ((ocRefFlux α q Λ ζ m ν t).mulVec w)) =
      fun t => w 0 ^ 2 * ocRefFlux α q Λ ζ m ν t 0 0 +
        w 1 ^ 2 * ocRefFlux α q Λ ζ m ν t 1 1 := by
    funext t
    have hd := CycleReference.refFlux_diagonal (α := α) (q := q) (m := m) hΛ hζ hν (t := t)
    simp only [vecDot, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hd.1, hd.2,
      zero_mul, add_zero, zero_add]
    ring
  have hi (i : Fin 2) := CycleReference.refFlux_entry_intervalIntegrable
    (α := α) (q := q) (m := m) hΛ hζ hν i i a b
  rw [he, intervalIntegral.integral_add ((hi 0).const_mul _) ((hi 1).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have h0 := mul_le_mul_of_nonneg_left (hb 0) (sq_nonneg (w 0))
  have h1 := mul_le_mul_of_nonneg_left (hb 1) (sq_nonneg (w 1))
  simp only [vecDot, Fin.sum_univ_two]
  dsimp [a, b] at h0 h1
  change c * _ * _ * _ ≤ _
  nlinarith only [h0, h1]

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleDamping

/-! The mean term in the quadratic graph symbol is exactly the corrector tensor. -/

/-- Expansion of the first graph response inside the scalar symbol. -/
theorem quadratic_corrector_mean (w χ : Fin 2 → Vec 2 → ℂ)
    (h : ∀ i j, Integrable (fun x => w i x * χ j x)
      (volume.restrict AVenhance.unitCube)) (ξ : Fin 2 → ℂ) :
    -Complex.I * cellMean (fun x => (∑ i, w i x * ξ i) *
      (-Complex.I * ∑ j, ξ j * χ j x)) =
        -(∑ i, ∑ j, ξ i * cellMean (fun x => w i x * χ j x) * ξ j) := by
  have he : (fun x => (∑ i, w i x * ξ i) *
      (-Complex.I * ∑ j, ξ j * χ j x)) =
      fun x => -Complex.I * ∑ i, ∑ j, ξ i * (w i x * χ j x) * ξ j := by
    funext x
    simp only [Fin.sum_univ_two]
    ring
  have hi (i j : Fin 2) : Integrable (fun x => ξ i * (w i x * χ j x) * ξ j)
      (volume.restrict AVenhance.unitCube) := ((h i j).const_mul _).mul_const _
  have hm : cellMean (fun x => ∑ i, ∑ j, ξ i * (w i x * χ j x) * ξ j) =
      ∑ i, ∑ j, ξ i * cellMean (fun x => w i x * χ j x) * ξ j := by
    unfold cellMean
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => hi i j)]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_mul_const, integral_const_mul]
  rw [he]
  change -Complex.I * (∫ x in AVenhance.unitCube, -Complex.I * _) = _
  rw [integral_const_mul]
  change -Complex.I * (-Complex.I * cellMean _) = _
  rw [hm]
  simp only [← mul_assoc, neg_mul_neg, Complex.I_mul_I, neg_one_mul]

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.CycleDamping

/-! At most one glued reference term has nonzero memory at a given point. -/

theorem reference_term_time_bounds {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (k : ℤ) (t : ℝ) (y : Vec 2)
    (hne : ocCutoff α q Λ m k t • ocPulseCorrector α q Λ ζ m ν k t y ≠ 0) :
    ((k : ℝ) - 2 / 3) * ocTau α q Λ m < t ∧
      t < ((k : ℝ) + 5 / 4) * ocTau α q Λ m := by
  have hc : ocCutoff α q Λ m k t ≠ 0 := by
    intro hz
    exact hne (by rw [hz, zero_smul])
  have hM : ocPulseMemory α q Λ ζ m ν k t ≠ 0 := by
    intro hz
    exact hne (by simp [ocPulseCorrector, hz])
  constructor
  · by_contra ht
    exact hM (CycleReference.pulseMemory_zero_before hΛ hζ ν k t (le_of_not_gt ht))
  · have hd := CycleReference.cutoff_nonzero_distance hΛ k t hc
    have hτ := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
    have hu := (abs_lt.mp hd).2
    linarith

theorem reference_term_unique {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν t : ℝ) (y : Vec 2)
    (k j : {k : ℤ // Odd k})
    (hk : ocCutoff α q Λ m k.1 t • ocPulseCorrector α q Λ ζ m ν k.1 t y ≠ 0)
    (hj : ocCutoff α q Λ m j.1 t • ocPulseCorrector α q Λ ζ m ν j.1 t y ≠ 0) :
    k = j := by
  have hkt := reference_term_time_bounds hΛ hζ ν k.1 t y hk
  have hjt := reference_term_time_bounds hΛ hζ ν j.1 t y hj
  have hτ := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
  have hkj : (k.1 : ℝ) < (j.1 : ℝ) + 2 := by
    apply (mul_lt_mul_iff_of_pos_right hτ).mp
    linarith
  have hjk : (j.1 : ℝ) < (k.1 : ℝ) + 2 := by
    apply (mul_lt_mul_iff_of_pos_right hτ).mp
    linarith
  have hki : k.1 < j.1 + 2 := by exact_mod_cast hkj
  have hji : j.1 < k.1 + 2 := by exact_mod_cast hjk
  rcases k.2 with ⟨a, ha⟩
  rcases j.2 with ⟨b, hb⟩
  apply Subtype.ext
  omega

theorem reference_corrector_single {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν t : ℝ) (y : Vec 2)
    (k : {k : ℤ // Odd k})
    (hk : ocCutoff α q Λ m k.1 t • ocPulseCorrector α q Λ ζ m ν k.1 t y ≠ 0) :
    ocRefCorrector α q Λ ζ m ν t y =
      ocCutoff α q Λ m k.1 t • ocPulseCorrector α q Λ ζ m ν k.1 t y := by
  unfold ocRefCorrector
  apply tsum_eq_single k
  intro j hj
  by_contra hne
  exact hj (reference_term_unique hΛ hζ ν t y j k hne hk)

end AVRegularity.CycleDamping
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleDamping

/-! Conversion of an entrywise bridge error into a real-frequency quadratic error. -/

/-- Entrywise tensor errors cost at most twice their size in two dimensions. -/
theorem quadratic_entry_error (A : Matrix (Fin 2) (Fin 2) ℂ) (x : Vec 2)
    (δ : ℝ) (hδ : 0 ≤ δ) (hA : ∀ i j, ‖A i j‖ ≤ δ) :
    ‖∑ i, ∑ j, (x i : ℂ) * A i j * (x j : ℂ)‖ ≤
      2 * δ * (∑ i, x i ^ 2) := by
  have hterm (i j : Fin 2) : ‖(x i : ℂ) * A i j * (x j : ℂ)‖ ≤
      |x i| * δ * |x j| := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hA i j) (abs_nonneg _)) (abs_nonneg _)
  have hn := (norm_sum_le Finset.univ (fun i =>
    ∑ j : Fin 2, (x i : ℂ) * A i j * (x j : ℂ))).trans
    (Finset.sum_le_sum (fun i _ =>
      (norm_sum_le Finset.univ _).trans (Finset.sum_le_sum (fun j _ => hterm i j))))
  refine hn.trans ?_
  simp only [Fin.sum_univ_two]
  have hs : |x 0| ^ 2 = x 0 ^ 2 := sq_abs _
  have hs' : |x 1| ^ 2 = x 1 ^ 2 := sq_abs _
  have hc : 2 * |x 0| * |x 1| ≤ x 0 ^ 2 + x 1 ^ 2 := by
    nlinarith only [sq_nonneg (|x 0| - |x 1|), hs, hs']
  calc
    _ = δ * (|x 0| + |x 1|) ^ 2 := by ring
    _ ≤ δ * (2 * (x 0 ^ 2 + x 1 ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ hδ
      nlinarith only [hc, hs, hs']
    _ = _ := by ring

end AVRegularity.CycleDamping
end
end
