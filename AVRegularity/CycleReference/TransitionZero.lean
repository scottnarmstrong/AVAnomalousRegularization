-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Definitions.CycleReference.OcAsymp
public import AVRegularity.Definitions.CycleReference.OcRefCorrector
import AVRegularity.Construction.Scales.Times
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Intermediate.CycleReference.OcBand
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Intermediate.CycleReference.JacMatrix
public import AVRegularity.Statements.Intermediate.CycleReference.OcTransition
import AVenhance.Infra.Construction.ExplicitBarNorm
import AVenhance.Statements.FlowDefs.FlowIsFlow
public import AVenhance.Statements.Construction.BarNorm
import AVenhance.Infra.Flow.Laws
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

section
@[expose] public section

section
namespace AVRegularity.CycleReference

/-! Two-sided reciprocal-ceiling bounds for positive powers of a small scale. -/

theorem inv_ceil_neg_rpow_bounds {x p : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) (hp : 0 ≤ p) :
    (1 / 2) * x ^ p ≤ (⌈x ^ (-p)⌉₊ : ℝ)⁻¹ ∧
      (⌈x ^ (-p)⌉₊ : ℝ)⁻¹ ≤ x ^ p := by
  let y := x ^ (-p)
  let n : ℝ := ⌈y⌉₊
  have hyp : 0 < y := Real.rpow_pos_of_pos hx _
  have hy1 : 1 ≤ y := by
    dsimp [y]
    rw [Real.rpow_neg hx.le]
    apply (one_le_inv₀ (Real.rpow_pos_of_pos hx p)).2
    exact Real.rpow_le_one hx.le hx1 hp
  have hn : y ≤ n := Nat.le_ceil _
  have hn2 : n ≤ 2 * y := by
    have h := Nat.ceil_lt_add_one hyp.le
    dsimp [n]
    linarith
  have hnp : 0 < n := hyp.trans_le hn
  have hi : y⁻¹ = x ^ p := by dsimp [y]; rw [Real.rpow_neg hx.le, inv_inv]
  constructor
  · have h := (inv_le_inv₀ (by positivity : 0 < 2 * y) hnp).2 hn2
    simpa only [mul_inv, hi, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num] using h
  · have h := (inv_le_inv₀ hnp hyp).2 hn
    simpa only [hi] using h

/-! A finite collection of estimates can use one enlarged constant. -/

theorem exists_common_constant (cs : List ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ c ∈ cs, c ≤ C := by
  induction cs with
  | nil => exact ⟨1, le_rfl, by simp⟩
  | cons c cs ih =>
    obtain ⟨C, hC, hb⟩ := ih
    refine ⟨max c C, hC.trans (le_max_right _ _), ?_⟩
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact le_max_left _ _
    · exact (hb d hd).trans (le_max_right _ _)

/-! A residue-class family of `N²` centers inside the central plateau of a `4N+1` block. -/

theorem residue_core_slots (N : ℕ) (_hN : 1 ≤ N) (l r : ℤ) (hr : r = 1 ∨ r = 3) :
    ∃ S : Finset ℤ, S.card = N ^ 2 ∧ ∀ k ∈ S,
      k % 4 = r ∧ Odd k ∧
        -2 * (N : ℤ) ^ 2 + 1 ≤ k - l * (4 * (N : ℤ) + 1) ^ 2 ∧
        k - l * (4 * (N : ℤ) + 1) ^ 2 ≤ 2 * (N : ℤ) ^ 2 := by
  classical
  let base : ℤ := l * (4 * (N : ℤ) + 1) ^ 2 - 2 * (N : ℤ) ^ 2 + 1
  let shift : ℤ := (r - base) % 4
  let f : ℕ ↪ ℤ := ⟨fun j => base + shift + 4 * (j : ℤ), by
    intro a b h
    change base + shift + 4 * (a : ℤ) = base + shift + 4 * (b : ℤ) at h
    have hab : (a : ℤ) = (b : ℤ) := by omega
    exact_mod_cast hab⟩
  refine ⟨(Finset.range (N ^ 2)).map f, by simp, ?_⟩
  intro k hk
  obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hk
  have hj' : j < N ^ 2 := Finset.mem_range.mp hj
  have hjZ : (j : ℤ) < (N : ℤ) ^ 2 := by exact_mod_cast hj'
  have hj0 : (0 : ℤ) ≤ j := by exact_mod_cast (Nat.zero_le j)
  have hs0 : 0 ≤ shift := Int.emod_nonneg _ (by norm_num)
  have hs4 : shift < 4 := Int.emod_lt _ (by norm_num)
  have hf : f j = base + shift + 4 * (j : ℤ) := rfl
  have hmod : (f j) % 4 = r := by
    rw [hf]
    dsimp only [shift]
    rcases hr with rfl | rfl <;> omega
  refine ⟨hmod, ?_, ?_, ?_⟩
  · exact Int.odd_iff.mpr (by omega)
  · rw [hf]
    dsimp only [base]
    omega
  · rw [hf]
    dsimp only [base]
    omega

theorem core_count_square_bound (N : ℕ) (hN : 1 ≤ N) :
    (4 * (N : ℝ) + 1) ^ 2 / 32 ≤ (N ^ 2 : ℕ) := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  push_cast
  nlinarith [sq_nonneg ((N : ℝ) - 1)]

end AVRegularity.CycleReference
end

section
open MeasureTheory
namespace AVRegularity.CycleReference

/-! Periodic primitive bounds. Adapted from the generic proof in upstream
`AVenhance.Infra.Section4.IteratesPrimitive`, with interval integrability
instead of continuity and with an explicit one-period integral bound. -/

theorem periodic_primitive_bound_of_cell_bound {f : ℝ → ℝ} {P D : ℝ}
    (hP : 0 < P) (hp : Function.Periodic f P)
    (hi : ∀ a b : ℝ, IntervalIntegrable f volume a b)
    (hz : (∫ u in (0 : ℝ)..P, f u) = 0)
    (hcell : ∀ t ∈ Set.Icc 0 P, |∫ u in (0 : ℝ)..t, f u| ≤ D) :
    (∀ t : ℝ, |∫ u in (0 : ℝ)..t, f u| ≤ D) ∧
      ∀ s t : ℝ, |∫ u in s..t, f u| ≤ 2 * D := by
  let F := fun t : ℝ => ∫ u in (0 : ℝ)..t, f u
  have hper : Function.Periodic F P := by
    intro t
    have hcycle : (∫ u in t..(t + P), f u) = 0 := by
      rw [hp.intervalIntegral_add_eq t 0]
      simpa only [zero_add] using hz
    dsimp [F]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 t) (hi t (t + P)), hcycle, add_zero]
  have hglobal (t : ℝ) : |F t| ≤ D := by
    obtain ⟨r, hr, heq⟩ := hper.exists_mem_Ico₀ hP t
    rw [heq]
    exact hcell r ⟨hr.1, hr.2.le⟩
  refine ⟨hglobal, ?_⟩
  intro s t
  have hsplit : (∫ u in s..t, f u) = F t - F s := by
    have h := intervalIntegral.integral_add_adjacent_intervals (hi 0 s) (hi s t)
    dsimp [F]
    linarith only [h]
  rw [hsplit]
  exact (abs_sub _ _).trans (by linarith only [hglobal s, hglobal t])

theorem periodic_zero_mean_integral_bound {f : ℝ → ℝ} {P B : ℝ}
    (hP : 0 < P) (hB : 0 ≤ B) (hp : Function.Periodic f P)
    (hi : ∀ a b : ℝ, IntervalIntegrable f volume a b)
    (hz : (∫ u in (0 : ℝ)..P, f u) = 0) (hb : ∀ t, |f t| ≤ B) :
    ∀ s t : ℝ, |∫ u in s..t, f u| ≤ 2 * P * B := by
  have hcell : ∀ t ∈ Set.Icc 0 P, |∫ u in (0 : ℝ)..t, f u| ≤ P * B := by
    intro t ht
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := t)
      (f := f) (fun u _ => by simpa only [Real.norm_eq_abs] using hb u)
    simp only [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1] at h
    apply h.trans
    convert mul_le_mul_of_nonneg_right ht.2 hB using 1; ring
  intro s t
  have h := (periodic_primitive_bound_of_cell_bound hP hp hi hz hcell).2 s t
  simpa only [mul_assoc] using h

end AVRegularity.CycleReference
end

section
namespace AVRegularity.CycleReference

/-! Uniform real-power perturbation estimates on a fixed positive interval. -/

theorem rpow_near_one_bound (p : ℝ) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ x : ℝ, 1 / 2 ≤ x → x ≤ 2 → |x ^ p - 1| ≤ K * |x - 1| := by
  have hc : ContDiffOn ℝ 1 (fun x : ℝ => x ^ p) (Set.Icc (1 / 2) 2) := by
    intro x hx
    exact (Real.contDiffAt_rpow_const_of_ne (by linarith [hx.1] : x ≠ 0)).contDiffWithinAt
  obtain ⟨K, hK⟩ := hc.exists_lipschitzOnWith (by norm_num) (convex_Icc _ _) isCompact_Icc
  refine ⟨K, K.coe_nonneg, ?_⟩
  intro x hx0 hx1
  have h := hK.dist_le_mul x (show x ∈ Set.Icc (1 / 2) 2 from ⟨hx0, hx1⟩)
    1 (show (1 : ℝ) ∈ Set.Icc (1 / 2) 2 by norm_num)
  simpa only [Real.dist_eq, Real.one_rpow] using h

theorem rpow_positive_interval_bounds (p : ℝ) : ∃ K : ℝ, 1 ≤ K ∧
    ∀ x : ℝ, 1 / 2 ≤ x → x ≤ 2 → K⁻¹ ≤ x ^ p ∧ x ^ p ≤ K := by
  obtain ⟨A, hA, ha⟩ := rpow_near_one_bound p
  obtain ⟨B, hB, hb⟩ := rpow_near_one_bound (-p)
  let K := max (A + 1) (B + 1)
  have hK1 : 1 ≤ K := (by linarith : 1 ≤ A + 1).trans (le_max_left _ _)
  refine ⟨K, hK1, ?_⟩
  intro x hx0 hx1
  have hx : 0 < x := by linarith
  have herr : |x - 1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have ha' : x ^ p ≤ A + 1 := by
    have h := (ha x hx0 hx1).trans (mul_le_mul_of_nonneg_left herr hA)
    linarith [(le_abs_self (x ^ p - 1))]
  have hb' : (x ^ p)⁻¹ ≤ B + 1 := by
    have h := (hb x hx0 hx1).trans (mul_le_mul_of_nonneg_left herr hB)
    rw [Real.rpow_neg hx.le] at h
    linarith [(le_abs_self ((x ^ p)⁻¹ - 1))]
  have hupper : x ^ p ≤ K := ha'.trans (le_max_left _ _)
  have hinv : (x ^ p)⁻¹ ≤ K := hb'.trans (le_max_right _ _)
  have hKpos : 0 < K := by linarith
  have hl := (inv_le_inv₀ hKpos (inv_pos.mpr (Real.rpow_pos_of_pos hx p))).2 hinv
  exact ⟨by simpa only [inv_inv] using hl, hupper⟩

/-! Real-variable stability of the alternating normalized enhancement map. -/

/-- A value and its reciprocal are controlled simultaneously. -/
noncomputable def reciprocalSize (x : ℝ) : ℝ := max x x⁻¹

theorem reciprocalSize_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ reciprocalSize x :=
  hx.le.trans (le_max_left _ _)

theorem reciprocalSize_mul_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    reciprocalSize (x * y) ≤ reciprocalSize x * reciprocalSize y := by
  apply max_le
  · exact mul_le_mul (le_max_left _ _) (le_max_left _ _) hy.le
      (reciprocalSize_nonneg hx)
  · rw [mul_inv]
    exact mul_le_mul (le_max_right _ _) (le_max_right _ _) (inv_pos.mpr hy).le
      (reciprocalSize_nonneg hx)

theorem reciprocalSize_update_le {x t : ℝ} (hx : 0 < x) (ht : 0 ≤ t) :
    reciprocalSize (t * x + x⁻¹) ≤ (1 + t) * reciprocalSize x := by
  have hR := reciprocalSize_nonneg hx
  have hi : 0 < x⁻¹ := inv_pos.mpr hx
  apply max_le
  · calc
      t * x + x⁻¹ ≤ t * reciprocalSize x + reciprocalSize x :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ht) (le_max_right _ _)
      _ = _ := by ring
  · have hinv : (t * x + x⁻¹)⁻¹ ≤ x := by
      have hbase : x⁻¹ ≤ t * x + x⁻¹ := le_add_of_nonneg_left (mul_nonneg ht hx.le)
      simpa using (inv_le_inv₀ (hi.trans_le hbase) hi).2 hbase
    have hxr : x ≤ reciprocalSize x := le_max_left _ _
    exact hinv.trans (hxr.trans (by nlinarith))

theorem reciprocalSize_near_one {x e : ℝ} (he : 0 ≤ e) (hehalf : e ≤ 1 / 2)
    (hx : |x - 1| ≤ e) : reciprocalSize x ≤ 1 + 2 * e := by
  have hl : 1 - e ≤ x := by linarith [(abs_le.mp hx).1]
  have hu : x ≤ 1 + e := by linarith [(abs_le.mp hx).2]
  have hxpos : 0 < x := by linarith
  apply max_le
  · linarith
  · rw [inv_eq_one_div]
    apply (div_le_iff₀ hxpos).2
    have hprod := mul_le_mul_of_nonneg_left hl (show 0 ≤ 1 + 2 * e by linarith)
    nlinarith

theorem reciprocalSize_perturbed_update {x t r u e d : ℝ}
    (hx : 0 < x) (ht : 0 ≤ t) (he : 0 ≤ e) (hehalf : e ≤ 1 / 2)
    (hd : 0 ≤ d) (hdhalf : d ≤ 1 / 2)
    (hr : |r - 1| ≤ e) (hu : |u - 1| ≤ d) :
    reciprocalSize (r * (t * x + x⁻¹) * u) ≤
      reciprocalSize x * (1 + 2 * e) * (1 + t) * (1 + 2 * d) := by
  have hrpos : 0 < r := by linarith [(abs_le.mp hr).1]
  have hup : 0 < u := by linarith [(abs_le.mp hu).1]
  have hv : 0 < t * x + x⁻¹ := add_pos_of_nonneg_of_pos (mul_nonneg ht hx.le) (inv_pos.mpr hx)
  have hrb := reciprocalSize_near_one he hehalf hr
  have hub := reciprocalSize_near_one hd hdhalf hu
  have hvb := reciprocalSize_update_le hx ht
  calc
    _ ≤ reciprocalSize (r * (t * x + x⁻¹)) * reciprocalSize u :=
      reciprocalSize_mul_le (mul_pos hrpos hv) hup
    _ ≤ (reciprocalSize r * reciprocalSize (t * x + x⁻¹)) * reciprocalSize u :=
      mul_le_mul_of_nonneg_right (reciprocalSize_mul_le hrpos hv) (reciprocalSize_nonneg hup)
    _ ≤ ((1 + 2 * e) * ((1 + t) * reciprocalSize x)) * (1 + 2 * d) := by
      exact mul_le_mul (mul_le_mul hrb hvb (reciprocalSize_nonneg hv) (by positivity)) hub
        (reciprocalSize_nonneg hup) (mul_nonneg (by positivity) (mul_nonneg (by positivity) (reciprocalSize_nonneg hx)))
    _ = _ := by ring

theorem reciprocalSize_of_bounds {x K : ℝ} (hx : 0 < x) (hK : 0 < K)
    (hl : K⁻¹ ≤ x) (hu : x ≤ K) : reciprocalSize x ≤ K := by
  apply max_le hu
  have h := (inv_le_inv₀ hx (inv_pos.mpr hK)).2 hl
  simpa only [inv_inv] using h

/-! Positive scalar algebra for the common diffusivity comparison constant. -/

theorem asymp_mono_constant {C D x y : ℝ} (hC : 0 < C) (hCD : C ≤ D)
    (hy : 0 ≤ y) (h : ocAsymp C x y) : ocAsymp D x y := by
  have hD : 0 < D := hC.trans_le hCD
  exact ⟨(mul_le_mul_of_nonneg_right ((inv_le_inv₀ hD hC).2 hCD) hy).trans h.1,
    h.2.trans (mul_le_mul_of_nonneg_right hCD hy)⟩

theorem asymp_mul {C D x y X Y : ℝ} (hC : 0 < C) (hD : 0 < D)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hx : ocAsymp C x X) (hy : ocAsymp D y Y) :
    ocAsymp (C * D) (x * y) (X * Y) := by
  have hx0 : 0 ≤ x := (mul_nonneg (inv_pos.mpr hC).le hX).trans hx.1
  have hy0 : 0 ≤ y := (mul_nonneg (inv_pos.mpr hD).le hY).trans hy.1
  constructor
  · have h := mul_le_mul hx.1 hy.1 (mul_nonneg (inv_pos.mpr hD).le hY) hx0
    simpa only [mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
  · have h := mul_le_mul hx.2 hy.2 hy0 (mul_nonneg hC.le hX)
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h

theorem asymp_trans {C D x y z : ℝ} (hC : 0 < C) (_hD : 0 < D)
    (hx : ocAsymp C x y) (hy : ocAsymp D y z) : ocAsymp (C * D) x z := by
  constructor
  · have h := (mul_le_mul_of_nonneg_left hy.1 (inv_pos.mpr hC).le).trans hx.1
    simpa only [mul_inv, mul_assoc] using h
  · have h := hx.2.trans (mul_le_mul_of_nonneg_left hy.2 hC.le)
    simpa only [mul_assoc] using h

theorem asymp_symm {C x y : ℝ} (hC : 0 < C) (h : ocAsymp C x y) : ocAsymp C y x := by
  constructor
  · have hu := mul_le_mul_of_nonneg_left h.2 (inv_pos.mpr hC).le
    simpa only [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul] using hu
  · have hl := mul_le_mul_of_nonneg_left h.1 hC.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul] using hl

theorem asymp_div {C D x y X Y : ℝ} (hC : 0 < C) (hD : 0 < D)
    (hX : 0 ≤ X) (hY : 0 < Y) (hy0 : 0 < y)
    (hx : ocAsymp C x X) (hy : ocAsymp D y Y) :
    ocAsymp (C * D) (x / y) (X / Y) := by
  have hx0 : 0 ≤ x := (mul_nonneg (inv_pos.mpr hC).le hX).trans hx.1
  have hlow : C⁻¹ * X / (D * Y) ≤ x / y := by
    exact div_le_div₀ hx0 hx.1 hy0 hy.2
  have hupp : x / y ≤ C * X / (D⁻¹ * Y) := by
    exact div_le_div₀ (mul_nonneg hC.le hX) hx.2 (mul_pos (inv_pos.mpr hD) hY) hy.1
  constructor
  · convert hlow using 1; simp only [div_eq_mul_inv, mul_inv]; ring
  · convert hupp using 1; simp only [div_eq_mul_inv, mul_inv, inv_inv]; ring

theorem asymp_sqrt {C x X : ℝ} (hC : 0 < C) (_hX : 0 ≤ X)
    (h : ocAsymp C x X) : ocAsymp (Real.sqrt C) (Real.sqrt x) (Real.sqrt X) := by
  have hl := Real.sqrt_le_sqrt h.1
  have hu := Real.sqrt_le_sqrt h.2
  rw [Real.sqrt_mul (inv_pos.mpr hC).le, Real.sqrt_inv] at hl
  rw [Real.sqrt_mul hC.le] at hu
  exact ⟨hl, hu⟩

theorem asymp_rpow_nonneg {C x X p : ℝ} (hC : 0 < C) (hX : 0 ≤ X)
    (hp : 0 ≤ p) (h : ocAsymp C x X) : ocAsymp (C ^ p) (x ^ p) (X ^ p) := by
  have hx : 0 ≤ x := (mul_nonneg (inv_pos.mpr hC).le hX).trans h.1
  have hl := Real.rpow_le_rpow (mul_nonneg (inv_pos.mpr hC).le hX) h.1 hp
  have hu := Real.rpow_le_rpow hx h.2 hp
  rw [Real.mul_rpow (inv_pos.mpr hC).le hX, Real.inv_rpow hC.le] at hl
  rw [Real.mul_rpow hC.le hX] at hu
  exact ⟨hl, hu⟩

theorem quotient_upper_bound {A B x y X Y : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hX : 0 ≤ X) (hY : 0 < Y) (_hy : 0 < y)
    (hx : x ≤ A * X) (hyl : B⁻¹ * Y ≤ y) : x / y ≤ (A * B) * (X / Y) := by
  have h := div_le_div₀ (mul_nonneg hA.le hX) hx (mul_pos (inv_pos.mpr hB) hY) hyl
  convert h using 1; simp only [div_eq_mul_inv, mul_inv, inv_inv]; ring

theorem asymp_one_self (x : ℝ) : ocAsymp 1 x x := by
  simp only [ocAsymp, inv_one, one_mul, le_refl, and_self]

theorem quotient_lower_bound {A B x y X Y : ℝ} (_hA : 0 < A) (_hB : 0 < B)
    (_hX : 0 ≤ X) (_hY : 0 < Y) (hx : 0 ≤ x) (hy : 0 < y)
    (hxl : A⁻¹ * X ≤ x) (hyu : y ≤ B * Y) : (A * B)⁻¹ * (X / Y) ≤ x / y := by
  have h := div_le_div₀ hx hxl hy hyu
  convert h using 1; simp only [div_eq_mul_inv, mul_inv]; ring

theorem asymp_scale_left {C x X a : ℝ} (ha : 0 ≤ a) (h : ocAsymp C x X) :
    ocAsymp C (a * x) (a * X) := by
  constructor
  · convert mul_le_mul_of_nonneg_left h.1 ha using 1; ring
  · convert mul_le_mul_of_nonneg_left h.2 ha using 1; ring

end AVRegularity.CycleReference
end

section
open scoped BigOperators
namespace AVRegularity.CycleReference

/-! Finite bootstrap with a summable error budget; no terminal-index dependence. -/

theorem finite_small_error_bootstrap {y e : ℕ → ℝ} {B R : ℝ} {N : ℕ}
    (hR : 0 ≤ R) (hB : B ≤ R / 2) (hstart : y 0 ≤ B)
    (he : ∀ n, 0 ≤ e n)
    (hbudget : ∑ n ∈ Finset.range N, e n ≤ 1 / 2)
    (hstep : ∀ n, n < N → y n ≤ R → y (n + 1) ≤ y n * (1 + e n)) :
    ∀ n, n ≤ N → y n ≤ B + R * (∑ j ∈ Finset.range n, e j) ∧ y n ≤ R := by
  have hpartial (n : ℕ) (hn : n ≤ N) : ∑ j ∈ Finset.range n, e j ≤ 1 / 2 := by
    apply le_trans _ hbudget
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn) (fun j _ _ => he j)
  intro n
  induction n with
  | zero =>
    intro _
    simp only [Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
    exact ⟨hstart, hstart.trans (by linarith)⟩
  | succ n ih =>
    intro hn
    obtain ⟨hy, hyr⟩ := ih (by omega)
    have hs := hstep n (by omega) hyr
    have hnext : y (n + 1) ≤ B + R * (∑ j ∈ Finset.range (n + 1), e j) := by
      rw [Finset.sum_range_succ]
      have hprod := mul_le_mul_of_nonneg_right hyr (he n)
      nlinarith
    refine ⟨hnext, hnext.trans ?_⟩
    have hb := mul_le_mul_of_nonneg_left (hpartial (n + 1) hn) hR
    linarith

theorem three_error_factors_le {e t d : ℝ}
    (he : 0 ≤ e) (_he1 : e ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hd : 0 ≤ d) (hd1 : d ≤ 1) :
    (1 + 2 * e) * (1 + t) * (1 + 2 * d) ≤ 1 + 16 * (e + t + d) := by
  have het : e * t ≤ e := by nlinarith
  have hed : e * d ≤ e := by nlinarith
  have htd : t * d ≤ t := by nlinarith
  have hetd : e * t * d ≤ e :=
    (mul_le_mul_of_nonneg_right het hd).trans hed
  nlinarith

theorem reciprocalSize_perturbed_update_additive {x t r u e d : ℝ}
    (hx : 0 < x) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (he : 0 ≤ e) (hehalf : e ≤ 1 / 2)
    (hd : 0 ≤ d) (hdhalf : d ≤ 1 / 2)
    (hr : |r - 1| ≤ e) (hu : |u - 1| ≤ d) :
    reciprocalSize (r * (t * x + x⁻¹) * u) ≤
      reciprocalSize x * (1 + 16 * (e + t + d)) := by
  apply (reciprocalSize_perturbed_update hx ht he hehalf hd hdhalf hr hu).trans
  have hb := mul_le_mul_of_nonneg_left
    (three_error_factors_le he (by linarith) ht ht1 hd (by linarith))
    (reciprocalSize_nonneg hx)
  convert hb using 1; ring

theorem backward_small_error_bootstrap {y e : ℕ → ℝ} {B R : ℝ} {N : ℕ}
    (hR : 0 ≤ R) (hB : B ≤ R / 2) (hstart : y N ≤ B)
    (he : ∀ n, 0 ≤ e n)
    (hbudget : ∑ n ∈ Finset.range N, e n ≤ 1 / 2)
    (hstep : ∀ m, 1 ≤ m → m ≤ N → y m ≤ R →
      y (m - 1) ≤ y m * (1 + e (m - 1))) :
    ∀ m, m ≤ N → y m ≤ R := by
  let z := fun n => y (N - n)
  let d := fun n => e (N - 1 - n)
  have hzstart : z 0 ≤ B := by simpa only [z, Nat.sub_zero] using hstart
  have hd : ∀ n, 0 ≤ d n := fun n => he _
  have hdbudget : ∑ n ∈ Finset.range N, d n ≤ 1 / 2 := by
    simpa only [d, Finset.sum_range_reflect] using hbudget
  have hzstep : ∀ n, n < N → z n ≤ R → z (n + 1) ≤ z n * (1 + d n) := by
    intro n hn hzn
    have h := hstep (N - n) (by omega) (by omega) hzn
    have h1 : N - n - 1 = N - (n + 1) := by omega
    have h2 : N - 1 - n = N - (n + 1) := by omega
    simpa only [z, d, h1, h2] using h
  have hbound := finite_small_error_bootstrap hR hB hzstart hd hdbudget hzstep
  intro m hm
  have h := (hbound (N - m) (by omega)).2
  simpa only [z, Nat.sub_sub_self hm] using h

end AVRegularity.CycleReference
end

section
open MeasureTheory
namespace AVRegularity.CycleReference

/-! A centered coarse-period primitive controlled by a fast primitive and an L¹ discrepancy. -/

theorem periodic_centered_bound_from_fast_approximation {J F : ℝ → ℝ} {P B b A D : ℝ}
    (hP : 0 < P) (hper : Function.Periodic J P)
    (hJ : ∀ a c, IntervalIntegrable J volume a c)
    (hF : ∀ a c, IntervalIntegrable F volume a c)
    (hmeanJ : (∫ t in (0 : ℝ)..P, J t - B) = 0)
    (hmeanF : (∫ t in (0 : ℝ)..P, F t - b) = 0)
    (hfast : ∀ c, |∫ t in (0 : ℝ)..c, F t - b| ≤ A)
    (herror : (∫ t in (0 : ℝ)..P, |J t - F t|) ≤ D) :
    ∀ s t : ℝ, |∫ u in s..t, J u - B| ≤ 2 * A + 4 * D := by
  have hiJ (a c : ℝ) : IntervalIntegrable (fun t => J t - B) volume a c :=
    (hJ a c).sub intervalIntegrable_const
  have hiF (a c : ℝ) : IntervalIntegrable (fun t => F t - b) volume a c :=
    (hF a c).sub intervalIntegrable_const
  have hiE (a c : ℝ) : IntervalIntegrable (fun t => J t - F t) volume a c := (hJ a c).sub (hF a c)
  have hsplit (c : ℝ) : (∫ t in (0 : ℝ)..c, J t - B) =
      (∫ t in (0 : ℝ)..c, F t - b) + (∫ t in (0 : ℝ)..c, J t - F t) + (b - B) * c := by
    have heq : (fun t => J t - B) = fun t => (F t - b) + (J t - F t) + (b - B) := by
      funext t
      ring
    rw [heq, intervalIntegral.integral_add ((hiF 0 c).add (hiE 0 c)) intervalIntegrable_const,
      intervalIntegral.integral_add (hiF 0 c) (hiE 0 c), intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    ring
  have hmean : (∫ t in (0 : ℝ)..P, J t - F t) = (B - b) * P := by
    have h := hsplit P
    rw [hmeanJ, hmeanF, zero_add] at h
    linarith only [h]
  have hmeanBound : |b - B| * P ≤ D := by
    have h := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
      (f := fun t => J t - F t) hP.le
    simp only [Real.norm_eq_abs, hmean, abs_mul, abs_of_pos hP] at h
    rw [abs_sub_comm b B]
    exact h.trans herror
  have hpartial (c : ℝ) (hc : c ∈ Set.Icc 0 P) : |∫ t in (0 : ℝ)..c, J t - F t| ≤ D := by
    have hnorm := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
      (f := fun t => J t - F t) hc.1
    simp only [Real.norm_eq_abs] at hnorm
    have hmono := intervalIntegral.integral_mono_interval (a := (0 : ℝ)) (b := c)
      (c := (0 : ℝ)) (d := P) (μ := volume) (f := fun t => |J t - F t|)
      (le_refl 0) hc.1 hc.2 (Filter.Eventually.of_forall (fun t => abs_nonneg _)) (hiE 0 P).abs
    exact hnorm.trans (hmono.trans herror)
  have hcell : ∀ c ∈ Set.Icc 0 P, |∫ t in (0 : ℝ)..c, J t - B| ≤ A + 2 * D := by
    intro c hc
    rw [hsplit c]
    have hconst : |(b - B) * c| ≤ D := by
      rw [abs_mul, abs_of_nonneg hc.1]
      exact (mul_le_mul_of_nonneg_left hc.2 (abs_nonneg _)).trans hmeanBound
    exact (abs_add_le _ _).trans ((add_le_add (abs_add_le _ _) (le_refl _)).trans
      (by linarith only [hfast c, hpartial c hc, hconst]))
  have hp : Function.Periodic (fun t => J t - B) P := by
    intro t
    change J (t + P) - B = J t - B
    rw [hper t]
  intro s t
  have h := (periodic_primitive_bound_of_cell_bound hP hp hiJ hmeanJ hcell).2 s t
  convert h using 1; ring

theorem periodic_centered_bound_from_fast_approximation_at_base
    {J F : ℝ → ℝ} {a P B b A D : ℝ}
    (hP : 0 < P) (hper : Function.Periodic J P)
    (hJ : ∀ u v, IntervalIntegrable J volume u v)
    (hF : ∀ u v, IntervalIntegrable F volume u v)
    (hmeanJ : (∫ t in a..(a + P), J t - B) = 0)
    (hmeanF : (∫ t in a..(a + P), F t - b) = 0)
    (hfast : ∀ c, |∫ t in a..c, F t - b| ≤ A)
    (herror : (∫ t in a..(a + P), |J t - F t|) ≤ D) :
    ∀ s t : ℝ, |∫ u in s..t, J u - B| ≤ 2 * A + 4 * D := by
  have hp : Function.Periodic (fun t => J (t + a)) P := by
    intro t
    change J ((t + P) + a) = J (t + a)
    rw [show (t + P) + a = (t + a) + P by ring, hper]
  have hiJ (u v : ℝ) : IntervalIntegrable (fun t => J (t + a)) volume u v := by
    have h := (hJ (u + a) (v + a)).comp_add_right a
    simpa only [add_sub_cancel_right] using h
  have hiF (u v : ℝ) : IntervalIntegrable (fun t => F (t + a)) volume u v := by
    have h := (hF (u + a) (v + a)).comp_add_right a
    simpa only [add_sub_cancel_right] using h
  have hmJ : (∫ t in (0 : ℝ)..P, J (t + a) - B) = 0 := by
    rw [intervalIntegral.integral_comp_add_right (fun t => J t - B) a, zero_add,
      add_comm P a]
    exact hmeanJ
  have hmF : (∫ t in (0 : ℝ)..P, F (t + a) - b) = 0 := by
    rw [intervalIntegral.integral_comp_add_right (fun t => F t - b) a, zero_add,
      add_comm P a]
    exact hmeanF
  have hfa (c : ℝ) : |∫ t in (0 : ℝ)..c, F (t + a) - b| ≤ A := by
    rw [intervalIntegral.integral_comp_add_right (fun t => F t - b) a, zero_add]
    exact hfast (c + a)
  have he : (∫ t in (0 : ℝ)..P, |J (t + a) - F (t + a)|) ≤ D := by
    rw [intervalIntegral.integral_comp_add_right (fun t => |J t - F t|) a, zero_add,
      add_comm P a]
    exact herror
  intro s t
  have h := periodic_centered_bound_from_fast_approximation hP hp hiJ hiF hmJ hmF hfa he
    (s - a) (t - a)
  simpa only [intervalIntegral.integral_comp_add_right (fun t => J t - B) a,
    sub_add_cancel] using h

/-! Bounded periodic functions have a bounded centered primitive. -/

theorem periodic_average_bounds {f : ℝ → ℝ} {P : ℝ} (hP : 0 < P)
    (hi : IntervalIntegrable f volume 0 P) (hf : ∀ t, f t ∈ Set.Icc 0 1) :
    ((∫ t in (0 : ℝ)..P, f t) / P) ∈ Set.Icc 0 1 := by
  have hlo : 0 ≤ ∫ t in (0 : ℝ)..P, f t :=
    intervalIntegral.integral_nonneg hP.le (fun t _ => (hf t).1)
  have hhi : (∫ t in (0 : ℝ)..P, f t) ≤ P := by
    have h := intervalIntegral.integral_mono_on hP.le hi intervalIntegrable_const
      (fun t _ => (hf t).2)
    simpa using h
  exact ⟨div_nonneg hlo hP.le, (div_le_iff₀ hP).mpr (by simpa using hhi)⟩

theorem periodic_centered_average {f : ℝ → ℝ} {P : ℝ} (hP : 0 < P)
    (hp : Function.Periodic f P) (hi : ∀ a b, IntervalIntegrable f volume a b)
    (hf : ∀ t, f t ∈ Set.Icc 0 1) :
    ∃ b ∈ Set.Icc (0 : ℝ) 1,
      (∀ n : ℤ, (∫ t in (0 : ℝ)..((n : ℝ) * P), f t - b) = 0) ∧
      (∀ t : ℝ, |∫ u in (0 : ℝ)..t, f u - b| ≤ 2 * P) := by
  let b := (∫ t in (0 : ℝ)..P, f t) / P
  have hb := periodic_average_bounds hP (hi 0 P) hf
  have hmean : (∫ t in (0 : ℝ)..P, f t - b) = 0 := by
    rw [intervalIntegral.integral_sub (hi 0 P) intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    dsimp [b]
    field_simp
    ring
  have hper : Function.Periodic (fun t => f t - b) P := by
    intro t
    change f (t + P) - b = f t - b
    rw [hp t]
  have hii (a c : ℝ) : IntervalIntegrable (fun t => f t - b) volume a c :=
    (hi a c).sub intervalIntegrable_const
  refine ⟨b, hb, ?_, ?_⟩
  · intro n
    have h := hper.intervalIntegral_add_zsmul_eq n 0 hii
    simpa only [zero_add, hmean, zsmul_eq_mul, mul_zero] using h
  · intro t
    have hbound (u : ℝ) : |f u - b| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith only [(hf u).1, (hf u).2, hb.1, hb.2]
    simpa only [mul_one] using
      periodic_zero_mean_integral_bound hP (by norm_num : (0 : ℝ) ≤ 1)
        hper hii hmean hbound 0 t

end AVRegularity.CycleReference
end

section
namespace AVRegularity.CycleReference

/-! Relative rounding error for two successive reciprocal-ceiling scales. -/

theorem rounded_power_ratio_near_one {q : ℝ} (hq : 1 ≤ q) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 1 ≤ x →
      |(⌈x⌉₊ : ℝ) ^ q / (⌈x ^ q⌉₊ : ℝ) - 1| ≤ K / (⌈x⌉₊ : ℝ) := by
  obtain ⟨K, hK, hb⟩ := rpow_near_one_bound q
  refine ⟨2 * (K + 1), by positivity, ?_⟩
  intro x hx
  let A : ℝ := ⌈x⌉₊
  let B : ℝ := ⌈x ^ q⌉₊
  have hxpos : 0 < x := by linarith
  have hxqpos : 0 < x ^ q := Real.rpow_pos_of_pos hxpos q
  have hA : x ≤ A := Nat.le_ceil x
  have hAu : A ≤ x + 1 := (Nat.ceil_lt_add_one hxpos.le).le
  have hB : x ^ q ≤ B := Nat.le_ceil _
  have hBu : B ≤ x ^ q + 1 := (Nat.ceil_lt_add_one hxqpos.le).le
  have hApos : 0 < A := hxpos.trans_le hA
  have hBpos : 0 < B := hxqpos.trans_le hB
  have hAx : 1 ≤ A / x := (le_div_iff₀ hxpos).2 (by simpa using hA)
  have hAx2 : A / x ≤ 2 := (div_le_iff₀ hxpos).2 (by linarith)
  have hAxerr : |A / x - 1| ≤ 1 / x := by
    rw [abs_of_nonneg (by linarith)]
    apply (le_div_iff₀ hxpos).2
    field_simp
    linarith
  have hpowerr : |(A / x) ^ q - 1| ≤ K / x := by
    exact (hb (A / x) (by linarith) hAx2).trans
      (by simpa only [div_eq_mul_inv, mul_assoc, one_mul] using mul_le_mul_of_nonneg_left hAxerr hK)
  have hxqge : x ≤ x ^ q := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx hq
  have hdiff : |A ^ q - x ^ q| ≤ K / x * x ^ q := by
    have h := mul_le_mul_of_nonneg_right hpowerr hxqpos.le
    have heq : |(A / x) ^ q - 1| * x ^ q = |((A / x) ^ q - 1) * x ^ q| := by
      rw [abs_mul, abs_of_pos hxqpos]
    rw [heq] at h
    convert h using 1
    congr 1
    rw [Real.div_rpow hApos.le hxpos.le]
    field_simp
  have hround : |B - x ^ q| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hB)]
    linarith
  have hdiffB : |A ^ q - B| ≤ K / x * x ^ q + 1 := by
    calc
      _ ≤ |A ^ q - x ^ q| + |x ^ q - B| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add hdiff (by simpa only [abs_sub_comm] using hround)
  have hsmall : |A ^ q / B - 1| ≤ (K + 1) / x := by
    have heq : A ^ q / B - 1 = (A ^ q - B) / B := by
      field_simp
    rw [heq, abs_div, abs_of_pos hBpos]
    apply (div_le_iff₀ hBpos).2
    apply hdiffB.trans
    have hKx : 0 ≤ K / x := div_nonneg hK hxpos.le
    have h1 : K / x * x ^ q ≤ K / x * B := mul_le_mul_of_nonneg_left hB hKx
    have h2 : 1 ≤ B / x := (le_div_iff₀ hxpos).2 (by simpa using hxqge.trans hB)
    calc
      _ ≤ K / x * B + B / x := add_le_add h1 h2
      _ = _ := by ring
  have hfinal : (K + 1) / x ≤ 2 * (K + 1) / A := by
    rw [div_le_div_iff₀ hxpos hApos]
    have hAle : A ≤ 2 * x := by linarith
    nlinarith
  exact hsmall.trans hfinal

/-! Real-power algebra for the four covariance normalizations. -/

theorem covariance_power_normalizations {E β γ δ C Cp Ct X B h P : ℝ}
    (hE : 0 < E) (hC : 0 ≤ C) (hCp : 0 < Cp) (hCt : 0 < Ct)
    (_hX : 0 ≤ X) (hB : 0 < B) (hh : 0 < h) (hP : 0 < P)
    (hx : X ≤ C * B * P) (hBu : B ≤ Cp * E ^ (β + γ))
    (hPu : P ≤ Ct * E ^ (2 - β + 3 * δ))
    (hhl : Ct⁻¹ * E ^ (2 - β + 2 * δ) ≤ h) :
    X / E ^ 2 ≤ (C * Cp * Ct) * E ^ (γ + 3 * δ) ∧
    X / (E ^ (1 + γ / 2)) ^ 2 + E ^ (β - 2) * X / B ≤
      (C * Cp * Ct + C * Ct) * E ^ (3 * δ) ∧
    X / (Real.sqrt (B * h)) ^ 2 ≤ (C * Ct ^ 2) * E ^ δ := by
  have hpow : E ^ (β + γ) * E ^ (2 - β + 3 * δ) = E ^ (2 + γ + 3 * δ) := by
    rw [← Real.rpow_add hE]
    congr 1
    ring
  have hxpow : X ≤ (C * Cp * Ct) * E ^ (2 + γ + 3 * δ) := by
    have hp := mul_le_mul hBu hPu hP.le
      (mul_pos hCp (Real.rpow_pos_of_pos hE _)).le
    have ha := mul_le_mul_of_nonneg_left hp hC
    have he : C * ((Cp * E ^ (β + γ)) * (Ct * E ^ (2 - β + 3 * δ))) =
        (C * Cp * Ct) * (E ^ (β + γ) * E ^ (2 - β + 3 * δ)) := by ring
    rw [he, hpow] at ha
    exact hx.trans (by simpa only [mul_assoc] using ha)
  have hdiv (r : ℝ) : E ^ (2 + γ + 3 * δ) / E ^ r = E ^ (2 + γ + 3 * δ - r) :=
    (Real.rpow_sub hE _ _).symm
  constructor
  · have ha := div_le_div_of_nonneg_right hxpow (Real.rpow_pos_of_pos hE 2).le
    rw [mul_div_assoc, hdiv 2] at ha
    rw [Real.rpow_two] at ha
    convert ha using 1
    congr 2
    ring
  constructor
  · have hr : (E ^ (1 + γ / 2)) ^ 2 = E ^ (2 + γ) := by
      rw [← Real.rpow_two, ← Real.rpow_mul hE.le]
      congr 1
      ring
    have ha := div_le_div_of_nonneg_right hxpow (Real.rpow_pos_of_pos hE (2 + γ)).le
    rw [mul_div_assoc, hdiv (2 + γ)] at ha
    have ha' : X / (E ^ (1 + γ / 2)) ^ 2 ≤ (C * Cp * Ct) * E ^ (3 * δ) := by
      rw [hr]
      convert ha using 1
      congr 2
      ring
    have hb : E ^ (β - 2) * X / B ≤ (C * Ct) * E ^ (3 * δ) := by
      have hb := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hx (Real.rpow_pos_of_pos hE (β - 2)).le) hB.le
      have heq : E ^ (β - 2) * (C * B * P) / B = C * (E ^ (β - 2) * P) := by
        field_simp
      rw [heq] at hb
      have hc := mul_le_mul_of_nonneg_left hPu
        (mul_nonneg hC (Real.rpow_pos_of_pos hE (β - 2)).le)
      have heq' : (C * E ^ (β - 2)) * (Ct * E ^ (2 - β + 3 * δ)) =
          (C * Ct) * E ^ (3 * δ) := by
        rw [show (C * E ^ (β - 2)) * (Ct * E ^ (2 - β + 3 * δ)) =
          (C * Ct) * (E ^ (β - 2) * E ^ (2 - β + 3 * δ)) by ring,
          ← Real.rpow_add hE]
        congr 2
        ring
      rw [heq'] at hc
      exact hb.trans (by convert hc using 1; ring)
    convert add_le_add ha' hb using 1; ring
  · rw [Real.sq_sqrt (mul_pos hB hh).le]
    have hb : X / (B * h) ≤ C * (P / h) := by
      have ha := div_le_div_of_nonneg_right hx (mul_pos hB hh).le
      have heq : C * B * P / (B * h) = C * (P / h) := by field_simp
      exact ha.trans_eq heq
    have hc := quotient_upper_bound hCt hCt (Real.rpow_pos_of_pos hE _).le
      (Real.rpow_pos_of_pos hE _) hh hPu hhl
    rw [← Real.rpow_sub hE] at hc
    have hc' : P / h ≤ Ct ^ 2 * E ^ δ := by
      have hid : (2 - β + 3 * δ) - (2 - β + 2 * δ) = δ := by ring
      rw [hid] at hc
      simpa only [pow_two] using hc
    have hd := mul_le_mul_of_nonneg_left hc' hC
    exact hb.trans (by convert hd using 1; ring)

/-! Free-q exponent identities used in the diffusivity and preparation ledger. -/

theorem enhancement_exponent_identity {α q : ℝ} (hq : 1 < q) :
    q * ((1 + α) - ocGamma α q) = (1 + α) + ocGamma α q := by
  unfold ocGamma
  field_simp
  ring

theorem memory_exponent_identity {α q : ℝ} (hq : 1 < q) :
    q * (2 - (1 + α) - ocGamma α q) = 2 - (1 + α) + 8 * ocDelta α q := by
  unfold ocGamma ocDelta
  field_simp
  ring

theorem cell_length_exponent_identity {α q : ℝ} (hq : 1 < q) :
    q * (1 - ocGamma α q) - 1 = ocGamma α q / 2 + 4 * ocDelta α q := by
  unfold ocGamma ocDelta
  field_simp
  ring

theorem prepared_radius_exponent_identity {α q : ℝ} (hq : 1 < q) :
    q - 1 - ocC α q = q * ocGamma α q + 3 * ocDelta α q := by
  unfold ocC ocGamma ocDelta
  field_simp
  ring

theorem molecular_radius_exponent_identity (α q : ℝ) :
    1 + ocGamma α q / 2 - (1 + ocC α q) = -ocDelta α q := by
  unfold ocC
  ring

/-! Exact real-power algebra of the normalized enhancement update. -/

theorem normalized_leading_update_algebra {e E A ν β γ q : ℝ}
    (he : 0 < e) (hE : 0 < E) (hA : 0 < A) (hν : 0 < ν)
    (hexp : q * (β - γ) = β + γ) :
    (ν + A ^ 2 * e ^ (2 * β) / ν) / (A * E ^ (β + γ)) =
      (e / E ^ q) ^ (β - γ) *
        ((ν / (A * e ^ (β + γ))) * e ^ (2 * γ) + (ν / (A * e ^ (β + γ)))⁻¹) := by
  have hEpow : (E ^ q) ^ (β - γ) = E ^ (β + γ) := by
    rw [← Real.rpow_mul hE.le, hexp]
  have he1 : e ^ (β - γ) * e ^ (2 * γ) = e ^ (β + γ) := by
    rw [← Real.rpow_add he]
    congr 1
    ring
  have he2 : e ^ (β - γ) * e ^ (β + γ) = e ^ (2 * β) := by
    rw [← Real.rpow_add he]
    congr 1
    ring
  rw [Real.div_rpow he.le (Real.rpow_pos_of_pos hE q).le, hEpow, inv_div]
  have hepow := Real.rpow_pos_of_pos he (β + γ)
  have hEpowpos := Real.rpow_pos_of_pos hE (β + γ)
  field_simp
  symm
  calc
    _ = A ^ 2 * (e ^ (β - γ) * e ^ (β + γ)) * e ^ (β + γ) +
        ν ^ 2 * (e ^ (β - γ) * e ^ (2 * γ)) := by ring
    _ = _ := by rw [he1, he2]; ring

end AVRegularity.CycleReference
end

section
open Filter
open scoped Topology
namespace AVRegularity.CycleReference

/-! Uniformly small summable wavelength errors as the separation grows. -/

theorem epsilon_first_le_inv {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ) :
    ocEpsilon q Λ 1 ≤ (Λ : ℝ)⁻¹ := by
  have he := (AVRegularity.Scales.epsilon_basic (m := 1) hq hΛ).1
  have h := AVRegularity.Scales.epsilon_ratio_lower (m := 1) hq hΛ (by norm_num)
  have hzero : ocEpsilon q Λ 0 = 1 := by simp [ocEpsilon]
  simp only [Nat.sub_self, hzero, one_div] at h
  have hΛpos : 0 < (Λ : ℝ) := by exact_mod_cast (by omega : 0 < Λ)
  simpa only [inv_inv] using (inv_le_inv₀ (inv_pos.mpr he) hΛpos).2 h

theorem epsilon_tail_separation_bound {q p : ℝ} {Λ : ℕ}
    (hq : 1 < q) (hp : 0 < p) (hΛ : 128 ≤ Λ) :
    Summable (fun k : ℕ => ocEpsilon q Λ (k + 1) ^ p) ∧
      ∑' k : ℕ, ocEpsilon q Λ (k + 1) ^ p ≤
        (Λ : ℝ) ^ (-p) / (1 - (Λ : ℝ) ^ (-p)) := by
  obtain ⟨hs, hb⟩ := AVRegularity.Scales.epsilon_forward_tail (m := 1) hq hΛ (by norm_num) hp
  have hΛpos : 0 < (Λ : ℝ) := by exact_mod_cast (by omega : 0 < Λ)
  have hΛone : 1 < (Λ : ℝ) := by exact_mod_cast (by omega : 1 < Λ)
  have hd : 0 < 1 - (Λ : ℝ) ^ (-p) := by
    rw [Real.rpow_neg hΛpos.le]
    have hpow := Real.one_lt_rpow hΛone hp
    have hpowpos := Real.rpow_pos_of_pos hΛpos p
    have hi : ((Λ : ℝ) ^ p)⁻¹ < 1 := (inv_lt_one₀ hpowpos).2 hpow
    linarith
  have hnum : ocEpsilon q Λ 1 ^ p ≤ (Λ : ℝ) ^ (-p) := by
    rw [Real.rpow_neg hΛpos.le, ← Real.inv_rpow hΛpos.le]
    exact Real.rpow_le_rpow (AVRegularity.Scales.epsilon_basic hq hΛ).1.le
      (epsilon_first_le_inv hq hΛ) hp.le
  refine ⟨by simpa only [Nat.add_comm] using hs, ?_⟩
  have hb' : ∑' k : ℕ, ocEpsilon q Λ (k + 1) ^ p ≤
      ocEpsilon q Λ 1 ^ p / (1 - (Λ : ℝ) ^ (-p)) := by
    simpa only [Nat.add_comm] using hb
  exact hb'.trans (div_le_div_of_nonneg_right hnum hd.le)

theorem separation_error_budget_tendsto {p : ℝ} (hp : 0 < p) :
    Tendsto (fun Λ : ℕ => (Λ : ℝ) ^ (-p) / (1 - (Λ : ℝ) ^ (-p))) atTop (𝓝 0) := by
  have h : Tendsto (fun Λ : ℕ => (Λ : ℝ) ^ (-p)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hp).comp tendsto_natCast_atTop_atTop
  simpa only [Pi.div_def, Pi.sub_def, Pi.zero_def, sub_zero, zero_div] using h.div (tendsto_const_nhds.sub h) (by norm_num : (1 : ℝ) - 0 ≠ 0)

theorem exists_small_scale_error_budget {q p η : ℝ} (hq : 1 < q) (hp : 0 < p) (hη : 0 < η) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      Summable (fun k : ℕ => ocEpsilon q Λ (k + 1) ^ p) ∧
        ∑' k : ℕ, ocEpsilon q Λ (k + 1) ^ p ≤ η := by
  have he := (separation_error_budget_tendsto hp).eventually (eventually_lt_nhds hη)
  obtain ⟨L, hL⟩ := eventually_atTop.1 he
  refine ⟨max 128 L, le_max_left _ _, ?_⟩
  intro Λ hΛ
  have h128 : 128 ≤ Λ := (le_max_left _ _).trans hΛ
  obtain ⟨hs, hb⟩ := epsilon_tail_separation_bound hq hp h128
  exact ⟨hs, hb.trans (hL Λ ((le_max_right _ _).trans hΛ)).le⟩

theorem epsilon_power_le_tail {q p : ℝ} {Λ m : ℕ}
    (hq : 1 < q) (hp : 0 < p) (hΛ : 128 ≤ Λ) (hm : 1 ≤ m) :
    ocEpsilon q Λ m ^ p ≤ ∑' k : ℕ, ocEpsilon q Λ (k + 1) ^ p := by
  have hs := (epsilon_tail_separation_bound hq hp hΛ).1
  have hb := hs.le_tsum (m - 1) (fun j _ =>
    Real.rpow_nonneg (AVRegularity.Scales.epsilon_basic hq hΛ).1.le p)
  simpa only [Nat.sub_add_cancel hm] using hb

theorem epsilon_succ_le {q : ℝ} {Λ n : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ) :
    ocEpsilon q Λ (n + 1) ≤ ocEpsilon q Λ n := by
  have he := (AVRegularity.Scales.epsilon_basic (m := n + 1) hq hΛ).1
  have hr := AVRegularity.Scales.epsilon_ratio_lower (m := n + 1) hq hΛ (by omega)
  simp only [Nat.add_sub_cancel] at hr
  have hΛ1 : (1 : ℝ) ≤ Λ := by exact_mod_cast (by omega : 1 ≤ Λ)
  have h := (le_div_iff₀ he).1 hr
  have hb := mul_le_mul_of_nonneg_right hΛ1 he.le
  simpa only [one_mul] using hb.trans h

end AVRegularity.CycleReference
end

section
namespace AVRegularity.CycleReference

/-! Explicit two-sided time-power comparisons at the actual rounded scales. -/

theorem ocL_power_bounds {α q : ℝ} {Λ m : ℕ}
    (he : 0 < ocEpsilon q Λ (m - 1)) (he1 : ocEpsilon q Λ (m - 1) ≤ 1)
    (hd : 0 ≤ ocDelta α q) :
    4 * ocEpsilon q Λ (m - 1) ^ (-ocDelta α q) ≤ (ocL α q Λ m : ℝ) ∧
    (ocL α q Λ m : ℝ) ≤ 9 * ocEpsilon q Λ (m - 1) ^ (-ocDelta α q) := by
  let x := ocEpsilon q Λ (m - 1) ^ (-ocDelta α q)
  have hx : 0 < x := Real.rpow_pos_of_pos he _
  have hx1 : 1 ≤ x := by
    dsimp [x]
    rw [Real.rpow_neg he.le]
    apply (one_le_inv₀ (Real.rpow_pos_of_pos he _)).2
    exact Real.rpow_le_one he.le he1 hd
  have hl : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil _
  have hu : (⌈x⌉₊ : ℝ) ≤ x + 1 := (Nat.ceil_lt_add_one hx.le).le
  have hdef : (ocL α q Λ m : ℝ) = 4 * (⌈x⌉₊ : ℝ) + 1 := by
    simp only [ocL, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    rfl
  change 4 * x ≤ _ ∧ _ ≤ 9 * x
  rw [hdef]
  constructor <;> linarith

theorem ocTauPP_power_bounds {α q : ℝ} {Λ m : ℕ}
    (he : 0 < ocEpsilon q Λ (m - 1)) (he1 : ocEpsilon q Λ (m - 1) ≤ 1)
    (hp : 0 ≤ 2 - (1 + α) + 2 * ocDelta α q) :
    (2 : ℝ) ^ (-26 : ℤ) * ocEpsilon q Λ (m - 1) ^
        (2 - (1 + α) + 2 * ocDelta α q) ≤ ocTauPP α q Λ m ∧
    ocTauPP α q Λ m ≤ (2 : ℝ) ^ (-25 : ℤ) * ocEpsilon q Λ (m - 1) ^
        (2 - (1 + α) + 2 * ocDelta α q) := by
  obtain ⟨hl, hu⟩ := inv_ceil_neg_rpow_bounds he he1 hp
  have hnum : 0 ≤ (2 : ℝ) ^ (-25 : ℤ) := by positivity
  have hdef : ocTauPP α q Λ m = (2 : ℝ) ^ (-25 : ℤ) *
      (⌈ocEpsilon q Λ (m - 1) ^ (-(2 - (1 + α) + 2 * ocDelta α q))⌉₊ : ℝ)⁻¹ := by
    rw [ocTauPP, div_eq_mul_inv]
  rw [hdef]
  refine ⟨?_, mul_le_mul_of_nonneg_left hu hnum⟩
  have h := mul_le_mul_of_nonneg_left hl hnum
  convert h using 1
  norm_num [zpow_neg]
  ring

theorem ocTau_power_bounds {α q : ℝ} {Λ m : ℕ}
    (he : 0 < ocEpsilon q Λ (m - 1)) (he1 : ocEpsilon q Λ (m - 1) ≤ 1)
    (hd : 0 ≤ ocDelta α q) (hp : 0 ≤ 2 - (1 + α) + 2 * ocDelta α q) :
    ((2 : ℝ) ^ (-26 : ℤ) / 81) * ocEpsilon q Λ (m - 1) ^
        (2 - (1 + α) + 4 * ocDelta α q) ≤ ocTau α q Λ m ∧
    ocTau α q Λ m ≤ ((2 : ℝ) ^ (-25 : ℤ) / 16) * ocEpsilon q Λ (m - 1) ^
        (2 - (1 + α) + 4 * ocDelta α q) := by
  let E := ocEpsilon q Λ (m - 1)
  let d := ocDelta α q
  let h := 2 - (1 + α) + 2 * d
  let t := 2 - (1 + α) + 4 * d
  obtain ⟨hLl, hLu⟩ := ocL_power_bounds he he1 hd
  obtain ⟨hHl, hHu⟩ := ocTauPP_power_bounds he he1 hp
  have hLpos : 0 < (ocL α q Λ m : ℝ) := by
    exact lt_of_lt_of_le (by positivity) hLl
  have hL2l : 16 * E ^ (-2 * d) ≤ (ocL α q Λ m : ℝ) ^ 2 := by
    have hb := mul_self_le_mul_self (show 0 ≤ 4 * E ^ (-d) by positivity) hLl
    have hx : (E ^ (-d)) ^ 2 = E ^ (-2 * d) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul he.le]
      congr 1
      norm_num
      ring
    nlinarith only [hb, hx]
  have hL2u : (ocL α q Λ m : ℝ) ^ 2 ≤ 81 * E ^ (-2 * d) := by
    have hb := mul_self_le_mul_self hLpos.le hLu
    have hx : (E ^ (-d)) ^ 2 = E ^ (-2 * d) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul he.le]
      congr 1
      norm_num
      ring
    nlinarith only [hb, hx]
  have hcancel : E ^ t * E ^ (-2 * d) = E ^ h := by
    rw [← Real.rpow_add he]
    congr 1
    dsimp [t, h]
    ring
  unfold ocTau
  constructor
  · apply (le_div_iff₀ (sq_pos_of_pos hLpos)).2
    calc
      _ ≤ (((2 : ℝ) ^ (-26 : ℤ) / 81) * E ^ t) * (81 * E ^ (-2 * d)) :=
        mul_le_mul_of_nonneg_left hL2u (by positivity)
      _ = (2 : ℝ) ^ (-26 : ℤ) * E ^ h := by
        calc
          _ = (2 : ℝ) ^ (-26 : ℤ) * (E ^ t * E ^ (-2 * d)) := by ring
          _ = _ := by rw [hcancel]
      _ ≤ _ := hHl
  · apply (div_le_iff₀ (sq_pos_of_pos hLpos)).2
    calc
      _ ≤ (2 : ℝ) ^ (-25 : ℤ) * E ^ h := hHu
      _ = (((2 : ℝ) ^ (-25 : ℤ) / 16) * E ^ t) * (16 * E ^ (-2 * d)) := by
        calc
          _ = (2 : ℝ) ^ (-25 : ℤ) * (E ^ t * E ^ (-2 * d)) := by rw [hcancel]
          _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hL2l (by positivity)

/-! Separation of the original permitted diffusivity bands. -/

theorem band_exponent_gt_half {α s q : ℝ} (hα : 0 < α)
    (hq : IsAdmissibleQ α s q) : 1 / 2 < (1 + α) - ocGamma α q := by
  have hd : 0 < q + 1 := by linarith [hq.1]
  have he : (1 + α) - ocGamma α q = 2 * (1 + α) / (q + 1) := by
    unfold ocGamma
    field_simp
    ring
  rw [he]
  apply (lt_div_iff₀ hd).2
  linarith [hq.2.1]

theorem band_power_step {α s q : ℝ} {Λ n : ℕ} (hα : 0 < α)
    (hq : IsAdmissibleQ α s q) (hΛ : 128 ≤ Λ) :
    4 * ocEpsilon q Λ (n + 1) ^ ((1 + α) - ocGamma α q) <
      ocEpsilon q Λ n ^ ((1 + α) - ocGamma α q) := by
  let p := (1 + α) - ocGamma α q
  have hp : 1 / 2 < p := band_exponent_gt_half hα hq
  have hp0 : 0 < p := by linarith
  have hn := (AVRegularity.Scales.epsilon_basic (m := n) hq.1 hΛ).1
  have hn1 := (AVRegularity.Scales.epsilon_basic (m := n + 1) hq.1 hΛ).1
  have hratio := AVRegularity.Scales.epsilon_ratio_lower (m := n + 1) hq.1 hΛ (by omega)
  simp only [Nat.add_sub_cancel] at hratio
  have hΛr : (128 : ℝ) ≤ Λ := by exact_mod_cast hΛ
  have hpow : (128 : ℝ) ^ p ≤ (ocEpsilon q Λ n / ocEpsilon q Λ (n + 1)) ^ p :=
    Real.rpow_le_rpow (by norm_num) (hΛr.trans hratio) hp0.le
  have hlarge : 4 < (128 : ℝ) ^ p := by
    have hs : 4 < Real.sqrt 128 := by
      apply (Real.lt_sqrt (by norm_num)).2
      norm_num
    rw [Real.sqrt_eq_rpow] at hs
    exact hs.trans_le (Real.rpow_le_rpow_of_exponent_le (by norm_num) hp.le)
  have hdiv : 4 < ocEpsilon q Λ n ^ p / ocEpsilon q Λ (n + 1) ^ p := by
    rw [← Real.div_rpow hn.le hn1.le]
    exact hlarge.trans_le hpow
  exact (lt_div_iff₀ (Real.rpow_pos_of_pos hn1 p)).1 hdiv

theorem bands_disjoint {α s q : ℝ} {Λ : ℕ} (hα : 0 < α)
    (hq : IsAdmissibleQ α s q) (hΛ : 128 ≤ Λ)
    {M M' : ℕ} (hMM' : M ≠ M') : Disjoint (ocBand α q Λ M) (ocBand α q Λ M') := by
  let f := fun n => ocEpsilon q Λ n ^ ((1 + α) - ocGamma α q)
  have hfpos (n : ℕ) : 0 < f n :=
    Real.rpow_pos_of_pos (AVRegularity.Scales.epsilon_basic hq.1 hΛ).1 _
  have hstep (n : ℕ) : 4 * f (n + 1) < f n := band_power_step hα hq hΛ
  have hf : StrictAnti f := strictAnti_nat_of_succ_lt (fun n => by
    have h := hstep n
    linarith [hfpos (n + 1)])
  have hordered (a b : ℕ) (hab : a < b) : Disjoint (ocBand α q Λ a) (ocBand α q Λ b) := by
    have hgap : 4 * f b < f a :=
      (mul_le_mul_of_nonneg_left (hf.antitone (show a + 1 ≤ b by omega)) (by norm_num)).trans_lt (hstep a)
    apply Set.disjoint_left.2
    intro x hxa hxb
    change f a / 2 ≤ x ∧ x ≤ 2 * f a at hxa
    change f b / 2 ≤ x ∧ x ≤ 2 * f b at hxb
    linarith [hxa.1, hxb.2]
  rcases lt_or_gt_of_ne hMM' with h | h
  · exact hordered M M' h
  · exact (hordered M' M h).symm

end AVRegularity.CycleReference
end
end
end

section
@[expose] public section
open Homogenization AVenhance
namespace AVRegularity.CycleReference

/-! The level-zero stream generates the identity flow. -/

theorem streamFlow_of_zero {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (hzero : φ = fun _ _ => 0) : AVRegularity.streamFlow φ hφ = fun _ x _ => x := by
  have hb : streamVel φ = 0 := by
    rw [hzero]
    funext t x i
    fin_cases i <;> simp [streamVel, spaceGrad]
  have hX : IsFlow (streamVel φ) (AVRegularity.streamFlow φ hφ) :=
    flow_isFlow _ hφ.vel_continuous hφ.vel_lipschitz
  have hId : IsFlow (streamVel φ) (fun _ x _ => x) := by
    constructor
    · intro x s; rfl
    · intro x s t
      rw [hb]
      exact hasDerivAt_const t x
  exact Infra.Flow.flow_eq_of_isFlow (streamVel φ) hφ.vel_lipschitz hX hId

theorem ocTransition_level_one {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsOCStreamSeq α q Λ ζ Φ)
    (hφ : IsAdmissibleStream (Φ (1 - 1))) (l₁ l₂ : ℤ) :
    ocTransition α q Λ 1 (Φ (1 - 1)) hφ l₁ l₂ = id := by
  funext y
  unfold ocTransition
  rw [streamFlow_of_zero hφ hseq.1]
  rfl


theorem jacMatrix_identity (x : Vec 2) : jacMatrix (id : Vec 2 → Vec 2) x = 1 := by
  ext i a
  simp [jacMatrix, fderiv_id, basisVec, Matrix.one_apply, Pi.single_apply]

theorem zero_barNorm (n : ℕ) (R : ℝ) : barNorm n R (fun _ : Vec 2 => (0 : ℝ)) = 0 := by
  rw [AVenhance.Infra.Construction.barNorm_eq_pointwise _ n R contDiff_const]
  cases n with
  | zero => simp
  | succ n => simp [iteratedFDeriv_const_of_ne (by omega : n + 1 ≠ 0)]

end AVRegularity.CycleReference
end
end
