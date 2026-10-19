-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Construction.IsFastProfile
import AVRegularity.Construction.Scales.Times
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsOCStreamSeq
import AVRegularity.Construction.Stream.NextAdmissible
import AVenhance.Infra.FullTheorem.LebronStep.VelocityBounds
public import AVRegularity.Statements.Definitions.IsHolderDivFreeVelocity
import AVenhance.Infra.Construction.StreamAdmissible
import AVenhance.Infra.FullTheorem.LebronStep.DivFree
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

@[expose] public section

section
namespace AVRegularity.Velocity

/-! Compact support gives uniform bounds for every time derivative of a fast profile. -/

/-- Differentiation does not enlarge the topological support of a smooth fast profile. -/
theorem iteratedDeriv_tsupport_subset {ζ : ℝ → ℝ} (n : ℕ) :
    tsupport (iteratedDeriv n ζ) ⊆ tsupport ζ := by
  induction n with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
      rw [iteratedDeriv_succ]
      exact tsupport_deriv_subset.trans ih

/-- Each fixed derivative of an admissible fast profile is bounded uniformly in time.
The bound is allowed to depend on the derivative order and on the profile. -/
theorem exists_uniform_fastProfile_iteratedDeriv_bound {ζ : ℝ → ℝ}
    (hζ : IsFastProfile ζ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |iteratedDeriv n ζ t| ≤ C := by
  let K : Set ℝ := Set.Icc (-(2 / 3)) (2 / 3)
  have hcont : Continuous (fun t : ℝ => |iteratedDeriv n ζ t|) := by
    exact (hζ.1.continuous_iteratedDeriv n (by simp)).abs
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hcont.continuousOn
  let C : ℝ := max B 0
  refine ⟨C, le_max_right B 0, ?_⟩
  intro t
  by_cases ht : t ∈ K
  · have hmem : |iteratedDeriv n ζ t| ∈ (fun x : ℝ => |iteratedDeriv n ζ x|) '' K :=
      ⟨t, ht, rfl⟩
    exact (hB hmem).trans (le_max_left B 0)
  · have hnotζ : t ∉ tsupport ζ := by
      intro htζ
      have htIoo : t ∈ Set.Ioo (-(2 / 3)) (2 / 3) := hζ.2.2.1 htζ
      apply ht
      exact ⟨le_of_lt htIoo.1, le_of_lt htIoo.2⟩
    have hnotderiv : t ∉ tsupport (iteratedDeriv n ζ) := by
      intro htderiv
      exact hnotζ (iteratedDeriv_tsupport_subset n htderiv)
    have hevent : (fun x : ℝ => iteratedDeriv n ζ x) =ᶠ[nhds t] 0 :=
      (notMem_tsupport_iff_eventuallyEq).mp hnotderiv
    have hzero : iteratedDeriv n ζ t = 0 := hevent.self_of_nhds
    simp [C, hzero]

/-! Endpoint scale-splitting estimates for velocity increments. -/

section
open Filter Topology

private theorem shifted_range_sum (f : ℕ → ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range (N + 1), f (j + 1)) + f 0 =
      ∑ j ∈ Finset.range (N + 2), f j := by
  induction N with
  | zero =>
      have hleft : (∑ j ∈ Finset.range 1, f (j + 1)) = f 1 := by simp
      have hright : (∑ j ∈ Finset.range 2, f j) = f 0 + f 1 := by
        rw [show 2 = 1 + 1 by rfl, Finset.sum_range_succ]
        simp
      rw [hleft, hright]
      ring
  | succ N ih =>
      have hleft :
          (∑ j ∈ Finset.range (N + 2), f (j + 1)) =
            (∑ j ∈ Finset.range (N + 1), f (j + 1)) + f (N + 2) := by
        rw [show N + 2 = (N + 1) + 1 by omega, Finset.sum_range_succ]
      have hright :
          (∑ j ∈ Finset.range (N + 3), f j) =
            (∑ j ∈ Finset.range (N + 2), f j) + f (N + 2) := by
        rw [show N + 3 = (N + 2) + 1 by omega, Finset.sum_range_succ]
      rw [hleft, hright]
      linarith [ih]

/-- The coarse-scale Lipschitz contribution and fine-scale amplitude tail both have
endpoint order `d^α`. The cutoff index `N` is any one satisfying
`ε_{N+2} ≤ d ≤ ε_{N+1}`. -/
theorem endpoint_scale_split_bound {α s q d : ℝ} {Λ N : ℕ}
    (hα₀ : 0 < α) (hα₁ : α < 1)
    (hq : IsAdmissibleQ α s q) (hΛ : 128 ≤ Λ)
    (hd : 0 < d)
    (hcross₁ : d ≤ ocEpsilon q Λ (N + 1))
    (hcross₂ : ocEpsilon q Λ (N + 2) ≤ d) :
    d * (∑ j ∈ Finset.range (N + 1),
      ocEpsilon q Λ (j + 1) ^ (α - 1)) +
      ∑' k : ℕ, ocEpsilon q Λ (N + 2 + k) ^ α ≤
      ((1 - (Λ : ℝ) ^ (-(1 - α)))⁻¹ +
        (1 - (Λ : ℝ) ^ (-α))⁻¹) * d ^ α := by
  let p : ℝ := 1 - α
  have hp : 0 < p := by dsimp [p]; linarith
  have hΛone : 1 < (Λ : ℝ) := by exact_mod_cast (by omega : 1 < Λ)
  have hΛpos : 0 < (Λ : ℝ) := by linarith
  have hpowp : 1 < (Λ : ℝ) ^ p := Real.one_lt_rpow hΛone hp
  have hpowα : 1 < (Λ : ℝ) ^ α := Real.one_lt_rpow hΛone hα₀
  have hdenp : 0 < 1 - (Λ : ℝ) ^ (-p) := by
    rw [Real.rpow_neg hΛpos.le]
    exact sub_pos.mpr ((inv_lt_one₀ (Real.rpow_pos_of_pos hΛpos p)).2 hpowp)
  have hdenα : 0 < 1 - (Λ : ℝ) ^ (-α) := by
    rw [Real.rpow_neg hΛpos.le]
    exact sub_pos.mpr ((inv_lt_one₀ (Real.rpow_pos_of_pos hΛpos α)).2 hpowα)
  have hEpos₁ : 0 < ocEpsilon q Λ (N + 1) :=
    (Scales.admissible_space_scale_facts hq hΛ (by omega)).1.1
  have hEpos₂ : 0 < ocEpsilon q Λ (N + 2) :=
    (Scales.admissible_space_scale_facts hq hΛ (by omega)).1.1
  have hprefixPower :
      d * ocEpsilon q Λ (N + 1) ^ (-p) ≤ d ^ α := by
    have hinv : (ocEpsilon q Λ (N + 1))⁻¹ ≤ d⁻¹ :=
      (inv_le_inv₀ hEpos₁ hd).2 hcross₁
    have hpow := Real.rpow_le_rpow (by positivity) hinv hp.le
    have hpow' : ocEpsilon q Λ (N + 1) ^ (-p) ≤ d ^ (-p) := by
      calc
        ocEpsilon q Λ (N + 1) ^ (-p) =
            (ocEpsilon q Λ (N + 1))⁻¹ ^ p := by
              rw [Real.inv_rpow hEpos₁.le, Real.rpow_neg hEpos₁.le]
        _ ≤ d⁻¹ ^ p := hpow
        _ = d ^ (-p) := by rw [Real.inv_rpow hd.le, Real.rpow_neg hd.le]
    calc
      d * ocEpsilon q Λ (N + 1) ^ (-p) ≤ d * d ^ (-p) :=
        mul_le_mul_of_nonneg_left hpow' hd.le
      _ = d ^ α := by
        calc
          d * d ^ (-p) = d ^ (1 : ℝ) * d ^ (-p) := by rw [Real.rpow_one]
          _ = d ^ ((1 : ℝ) + (-p)) := by rw [← Real.rpow_add hd]
          _ = d ^ α := by congr 1; dsimp [p]; ring
  have hback := Scales.admissible_epsilon_backward_sum
    (q := q) hq hΛ hp (m := N + 1)
  have hshift := shifted_range_sum
    (fun j => ocEpsilon q Λ j ^ (-p)) N
  have hprefixEq :
      (∑ j ∈ Finset.range (N + 1),
        ocEpsilon q Λ (j + 1) ^ (α - 1)) + 1 =
        ∑ j ∈ Finset.range (N + 2), ocEpsilon q Λ j ^ (-p) := by
    have hpoweq (j : ℕ) :
        ocEpsilon q Λ (j + 1) ^ (α - 1) =
          ocEpsilon q Λ (j + 1) ^ (-p) := by
      congr 1
      dsimp [p]
      ring
    simpa [hpoweq, p, ocEpsilon] using hshift
  have hprefixLe :
      (∑ j ∈ Finset.range (N + 1),
        ocEpsilon q Λ (j + 1) ^ (α - 1)) ≤
        ∑ j ∈ Finset.range (N + 2), ocEpsilon q Λ j ^ (-p) := by
    linarith [hprefixEq]
  have hprefixBound :
      d * (∑ j ∈ Finset.range (N + 1),
        ocEpsilon q Λ (j + 1) ^ (α - 1)) ≤
        (d ^ α) / (1 - (Λ : ℝ) ^ (-p)) := by
    calc
      _ ≤ d * (∑ j ∈ Finset.range (N + 2),
          ocEpsilon q Λ j ^ (-p)) :=
        mul_le_mul_of_nonneg_left hprefixLe hd.le
      _ ≤ d * (ocEpsilon q Λ (N + 1) ^ (-p) /
          (1 - (Λ : ℝ) ^ (-p))) :=
        mul_le_mul_of_nonneg_left hback hd.le
      _ = (d * ocEpsilon q Λ (N + 1) ^ (-p)) /
          (1 - (Λ : ℝ) ^ (-p)) := by ring
      _ ≤ (d ^ α) / (1 - (Λ : ℝ) ^ (-p)) :=
        div_le_div_of_nonneg_right hprefixPower hdenp.le
  have htail := Scales.admissible_epsilon_forward_tail
    (q := q) hq hΛ (by omega : 1 ≤ N + 2) hα₀
  have hsmallPower : ocEpsilon q Λ (N + 2) ^ α ≤ d ^ α :=
    Real.rpow_le_rpow (by positivity) hcross₂ hα₀.le
  have htailBound :
      (∑' k : ℕ, ocEpsilon q Λ (N + 2 + k) ^ α) ≤
        (d ^ α) / (1 - (Λ : ℝ) ^ (-α)) := by
    calc
      _ ≤ ocEpsilon q Λ (N + 2) ^ α /
          (1 - (Λ : ℝ) ^ (-α)) := by
        simpa [Nat.add_assoc] using htail.2
      _ ≤ d ^ α / (1 - (Λ : ℝ) ^ (-α)) :=
        div_le_div_of_nonneg_right hsmallPower hdenα.le
  calc
    _ ≤ (d ^ α) / (1 - (Λ : ℝ) ^ (-p)) +
        (d ^ α) / (1 - (Λ : ℝ) ^ (-α)) := add_le_add hprefixBound htailBound
    _ = ((1 - (Λ : ℝ) ^ (-p))⁻¹ +
        (1 - (Λ : ℝ) ^ (-α))⁻¹) * d ^ α := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    _ = _ := by rfl

/-- Sum the standard two-regime increment envelope at the endpoint exponent. -/
theorem endpoint_increment_envelope_tsum_bound {α s q d : ℝ} {Λ N : ℕ}
    (hα₀ : 0 < α) (hα₁ : α < 1)
    (hq : IsAdmissibleQ α s q) (hΛ : 128 ≤ Λ)
    (hd : 0 < d)
    (hcross₁ : d ≤ ocEpsilon q Λ (N + 1))
    (hcross₂ : ocEpsilon q Λ (N + 2) ≤ d) :
    ∑' n : ℕ,
      min (ocEpsilon q Λ (n + 1) ^ α)
        (d * ocEpsilon q Λ (n + 1) ^ (α - 1)) ≤
      ((1 - (Λ : ℝ) ^ (-(1 - α)))⁻¹ +
        (1 - (Λ : ℝ) ^ (-α))⁻¹) * d ^ α := by
  let f : ℕ → ℝ := fun n =>
    min (ocEpsilon q Λ (n + 1) ^ α)
      (d * ocEpsilon q Λ (n + 1) ^ (α - 1))
  have hpowerSummable : Summable (fun n : ℕ => ocEpsilon q Λ (n + 1) ^ α) := by
    simpa [Nat.add_comm] using
      (Scales.admissible_epsilon_forward_tail (q := q) hq hΛ
        (m := 1) (by norm_num) hα₀).1
  have hnonneg : ∀ n, 0 ≤ f n := by
    intro n
    dsimp [f]
    apply le_min
    · exact Real.rpow_nonneg
        (Scales.admissible_space_scale_facts hq hΛ (by omega)).1.1.le α
    · exact mul_nonneg hd.le (Real.rpow_nonneg
        (Scales.admissible_space_scale_facts hq hΛ (by omega)).1.1.le _)
  have hlePower : ∀ n, f n ≤ ocEpsilon q Λ (n + 1) ^ α := by
    intro n
    dsimp [f]
    exact min_le_left _ _
  have hfsum : Summable f := hpowerSummable.of_nonneg_of_le hnonneg hlePower
  have hprefix :
      (∑ n ∈ Finset.range (N + 1), f n) ≤
        d * (∑ n ∈ Finset.range (N + 1),
          ocEpsilon q Λ (n + 1) ^ (α - 1)) := by
    calc
      _ ≤ ∑ n ∈ Finset.range (N + 1),
          d * ocEpsilon q Λ (n + 1) ^ (α - 1) :=
        Finset.sum_le_sum fun n hn => by
          dsimp [f]
          exact min_le_right _ _
      _ = _ := by rw [Finset.mul_sum]
  have htailScale : Summable
      (fun k : ℕ => ocEpsilon q Λ (k + (N + 1) + 1) ^ α) :=
    (summable_nat_add_iff (N + 1)
      (f := fun n : ℕ => ocEpsilon q Λ (n + 1) ^ α)).2 hpowerSummable
  have htail :
      (∑' k : ℕ, f (k + (N + 1))) ≤
        ∑' k : ℕ, ocEpsilon q Λ (k + (N + 1) + 1) ^ α := by
    apply Summable.tsum_le_tsum
    · intro k
      change min (ocEpsilon q Λ (k + (N + 1) + 1) ^ α)
          (d * ocEpsilon q Λ (k + (N + 1) + 1) ^ (α - 1)) ≤ _
      exact min_le_left _ _
    · exact (summable_nat_add_iff (N + 1) (f := f)).2 hfsum
    · exact htailScale
  have hsplit := hfsum.sum_add_tsum_nat_add (N + 1)
  have htailEq :
      (fun k : ℕ => ocEpsilon q Λ (k + (N + 1) + 1) ^ α) =
        (fun k : ℕ => ocEpsilon q Λ (N + 2 + k) ^ α) := by
    funext k
    congr 2
    omega
  have htailReindex :
      (∑' k : ℕ, ocEpsilon q Λ (k + (N + 1) + 1) ^ α) =
        ∑' k : ℕ, ocEpsilon q Λ (N + 2 + k) ^ α := by
    exact tsum_congr fun k => congrFun htailEq k
  have hsumBound :
      (∑' n : ℕ, f n) ≤
        d * (∑ n ∈ Finset.range (N + 1),
          ocEpsilon q Λ (n + 1) ^ (α - 1)) +
          ∑' k : ℕ, ocEpsilon q Λ (N + 2 + k) ^ α := by
    calc
      _ = (∑ n ∈ Finset.range (N + 1), f n) +
          ∑' k : ℕ, f (k + (N + 1)) := hsplit.symm
      _ ≤ d * (∑ n ∈ Finset.range (N + 1),
          ocEpsilon q Λ (n + 1) ^ (α - 1)) +
          ∑' k : ℕ, ocEpsilon q Λ (k + (N + 1) + 1) ^ α :=
        add_le_add hprefix htail
      _ = d * (∑ n ∈ Finset.range (N + 1),
          ocEpsilon q Λ (n + 1) ^ (α - 1)) +
          ∑' k : ℕ, ocEpsilon q Λ (N + 2 + k) ^ α := by rw [htailReindex]
  have hscale := endpoint_scale_split_bound hα₀ hα₁ hq hΛ hd hcross₁ hcross₂
  exact hsumBound.trans hscale

private theorem epsilon_le_rpow {α x : ℝ}
    (hx : 0 < x) (hx₁ : x ≤ 1) (hα₁ : α < 1) :
    x ≤ x ^ α := by
  have hrem : 0 ≤ 1 - α := by linarith
  have hpow : x ^ (1 - α) ≤ 1 := Real.rpow_le_one hx.le hx₁ hrem
  have heq : x = x ^ α * x ^ (1 - α) := by
    calc
      x = x ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = x ^ (α + (1 - α)) := by congr 1; ring
      _ = x ^ α * x ^ (1 - α) := Real.rpow_add hx _ _
  calc
    x = x ^ α * x ^ (1 - α) := heq
    _ ≤ x ^ α * 1 :=
      mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hx.le α)
    _ = x ^ α := by simp

/-- Every positive distance below the first wavelength is bracketed by two
successive wavelengths. -/
theorem exists_endpoint_scale_split_index {α s q d : ℝ} {Λ : ℕ}
    (hα₀ : 0 < α) (hα₁ : α < 1)
    (hq : IsAdmissibleQ α s q) (hΛ : 128 ≤ Λ)
    (hd : 0 < d) (hd₁ : d ≤ ocEpsilon q Λ 1) :
    ∃ N : ℕ, d ≤ ocEpsilon q Λ (N + 1) ∧
      ocEpsilon q Λ (N + 2) ≤ d := by
  have heps1Facts := Scales.admissible_space_scale_facts (m := 1) hq hΛ (by omega)
  have heps1pos : 0 < ocEpsilon q Λ 1 := heps1Facts.1.1
  have hratio : (Λ : ℝ) ≤ ocEpsilon q Λ 0 / ocEpsilon q Λ 1 := heps1Facts.2.1
  have hΛ128 : (128 : ℝ) ≤ Λ := by exact_mod_cast hΛ
  have hmul : 128 * ocEpsilon q Λ 1 ≤ ocEpsilon q Λ 0 := by
    apply (le_div_iff₀ heps1pos).1
    exact hΛ128.trans hratio
  have heps0 : ocEpsilon q Λ 0 = 1 := by simp [ocEpsilon]
  have heps1small : ocEpsilon q Λ 1 ≤ 1 / 128 := by
    rw [heps0] at hmul
    nlinarith
  have heps1lt : ocEpsilon q Λ 1 < 1 := by
    exact lt_of_le_of_lt heps1small (by norm_num)
  rcases lt_or_eq_of_le hd₁ with hdlt | hdeq
  · have hpowerSum := Scales.admissible_epsilon_forward_tail
      (q := q) hq hΛ (m := 1) (by norm_num) hα₀
    have hpowerTendsto :
        Tendsto (fun k : ℕ => ocEpsilon q Λ (1 + k) ^ α) atTop (𝓝 0) :=
      hpowerSum.1.tendsto_atTop_zero
    have hepsTendsto :
        Tendsto (fun k : ℕ => ocEpsilon q Λ (1 + k)) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hpowerTendsto
        (fun k => (Scales.admissible_space_scale_facts (q := q) hq hΛ
          (m := 1 + k) (by omega)).1.1.le)
        (fun k => epsilon_le_rpow
          (Scales.admissible_space_scale_facts (q := q) hq hΛ
            (m := 1 + k) (by omega)).1.1
          (Scales.admissible_space_scale_facts (q := q) hq hΛ
            (m := 1 + k) (by omega)).1.2.1 hα₁)
    obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.1 hepsTendsto) d hd
    have hsmall : ocEpsilon q Λ (1 + K) < d := by
      have h := hK K le_rfl
      simpa [Real.dist_eq, abs_of_nonneg
        (Scales.admissible_space_scale_facts (q := q) hq hΛ
          (m := 1 + K) (by omega)).1.1.le] using h
    have hExists : ∃ m : ℕ, ocEpsilon q Λ m ≤ d :=
      ⟨1 + K, hsmall.le⟩
    let k := Nat.find hExists
    have hk : ocEpsilon q Λ k ≤ d := Nat.find_spec hExists
    have hk_ne0 : k ≠ 0 := by
      intro hk0
      have hfind0 : Nat.find hExists = 0 := by simpa [k] using hk0
      have hk' : ocEpsilon q Λ (Nat.find hExists) ≤ d := by simpa [k] using hk
      rw [hfind0, heps0] at hk'
      linarith [hdlt, heps1lt]
    have hk_ne1 : k ≠ 1 := by
      intro hk1
      have hfind1 : Nat.find hExists = 1 := by simpa [k] using hk1
      have hk' : ocEpsilon q Λ (Nat.find hExists) ≤ d := by simpa [k] using hk
      rw [hfind1] at hk'
      exact (not_le_of_gt hdlt) hk'
    have hkge2 : 2 ≤ k := by omega
    have hprev : d < ocEpsilon q Λ (k - 1) := by
      have hminimal := Nat.find_min hExists (m := k - 1) (show k - 1 < k by omega)
      exact lt_of_not_ge (by simpa using hminimal)
    refine ⟨k - 2, ?_, ?_⟩
    · have hindex : k - 1 = k - 2 + 1 := by omega
      rw [← hindex]
      exact hprev.le
    · have hindex : k = k - 2 + 2 := by omega
      rw [← hindex]
      exact hk
  · subst d
    refine ⟨0, le_rfl, ?_⟩
    have hstep := (Scales.admissible_space_scale_facts
      (q := q) hq hΛ (m := 2) (by omega)).2.2.1
    have hEpos : 0 < ocEpsilon q Λ 1 :=
      (Scales.admissible_space_scale_facts (q := q) hq hΛ
        (m := 1) (by omega)).1.1
    have hE : ocEpsilon q Λ 2 ≤ ocEpsilon q Λ 1 / 128 := by
      simpa using hstep
    exact hE.trans (by
      apply div_le_self (le_of_lt hEpos)
      norm_num)

/-- The endpoint increment envelope is summable with a Hölder bound for every
positive separation, including distances larger than the first wavelength. -/
theorem endpoint_increment_envelope_tsum_bound_all {α s q d : ℝ} {Λ : ℕ}
    (hα₀ : 0 < α) (hα₁ : α < 1)
    (hq : IsAdmissibleQ α s q) (hΛ : 128 ≤ Λ) (hd : 0 < d) :
    ∑' n : ℕ,
      min (ocEpsilon q Λ (n + 1) ^ α)
        (d * ocEpsilon q Λ (n + 1) ^ (α - 1)) ≤
      ((1 - (Λ : ℝ) ^ (-(1 - α)))⁻¹ +
        (1 - (Λ : ℝ) ^ (-α))⁻¹) * d ^ α := by
  have heps1 := Scales.admissible_space_scale_facts
    (q := q) hq hΛ (m := 1) (by omega)
  by_cases hdle : d ≤ ocEpsilon q Λ 1
  · obtain ⟨N, hcross₁, hcross₂⟩ :=
      exists_endpoint_scale_split_index hα₀ hα₁ hq hΛ hd hdle
    exact endpoint_increment_envelope_tsum_bound hα₀ hα₁ hq hΛ hd
      hcross₁ hcross₂
  · have hdlarger : ocEpsilon q Λ 1 < d := lt_of_not_ge hdle
    have hsmall : ocEpsilon q Λ 1 ≤ d := le_of_lt hdlarger
    have hpowerSummable : Summable
        (fun n : ℕ => ocEpsilon q Λ (n + 1) ^ α) := by
      simpa [Nat.add_comm] using
        (Scales.admissible_epsilon_forward_tail (q := q) hq hΛ
          (m := 1) (by norm_num) hα₀).1
    have henvNonneg : ∀ n, 0 ≤ min
        (ocEpsilon q Λ (n + 1) ^ α)
        (d * ocEpsilon q Λ (n + 1) ^ (α - 1)) := by
      intro n
      have hepsN : 0 < ocEpsilon q Λ (n + 1) :=
        (Scales.admissible_space_scale_facts (q := q) hq hΛ
          (m := n + 1) (by omega)).1.1
      apply le_min
      · exact Real.rpow_nonneg hepsN.le α
      · exact mul_nonneg hd.le (Real.rpow_nonneg hepsN.le _)
    have henvLe : ∀ n, min
        (ocEpsilon q Λ (n + 1) ^ α)
        (d * ocEpsilon q Λ (n + 1) ^ (α - 1)) ≤
          ocEpsilon q Λ (n + 1) ^ α := by
      intro n
      exact min_le_left _ _
    have henvSummable : Summable (fun n : ℕ =>
        min (ocEpsilon q Λ (n + 1) ^ α)
          (d * ocEpsilon q Λ (n + 1) ^ (α - 1))) :=
      hpowerSummable.of_nonneg_of_le henvNonneg henvLe
    have henvBound :
        (∑' n : ℕ,
          min (ocEpsilon q Λ (n + 1) ^ α)
            (d * ocEpsilon q Λ (n + 1) ^ (α - 1))) ≤
          (ocEpsilon q Λ 1 ^ α) / (1 - (Λ : ℝ) ^ (-α)) := by
      calc
        _ ≤ ∑' n : ℕ, ocEpsilon q Λ (n + 1) ^ α :=
          Summable.tsum_le_tsum henvLe henvSummable hpowerSummable
        _ ≤ _ := by
          simpa [Nat.add_comm] using
            (Scales.admissible_epsilon_forward_tail (q := q) hq hΛ
              (m := 1) (by norm_num) hα₀).2
    have hfirstPower : ocEpsilon q Λ 1 ^ α ≤ d ^ α :=
      Real.rpow_le_rpow heps1.1.1.le hsmall hα₀.le
    have hΛone : 1 < (Λ : ℝ) := by exact_mod_cast (by omega : 1 < Λ)
    have hΛpos : 0 < (Λ : ℝ) := by linarith
    have hpowα : 1 < (Λ : ℝ) ^ α := Real.one_lt_rpow hΛone hα₀
    have hdenα : 0 < 1 - (Λ : ℝ) ^ (-α) := by
      rw [Real.rpow_neg hΛpos.le]
      exact sub_pos.mpr
        ((inv_lt_one₀ (Real.rpow_pos_of_pos hΛpos α)).2 hpowα)
    have hdenp : 0 < 1 - (Λ : ℝ) ^ (-(1 - α)) := by
      have hp : 0 < 1 - α := by linarith
      have hpowp : 1 < (Λ : ℝ) ^ (1 - α) := Real.one_lt_rpow hΛone hp
      rw [Real.rpow_neg hΛpos.le]
      exact sub_pos.mpr
        ((inv_lt_one₀ (Real.rpow_pos_of_pos hΛpos (1 - α))).2 hpowp)
    have hinvP : 0 < (1 - (Λ : ℝ) ^ (-(1 - α)))⁻¹ := inv_pos.mpr hdenp
    have hcoefficient :
        (1 - (Λ : ℝ) ^ (-α))⁻¹ ≤
          (1 - (Λ : ℝ) ^ (-(1 - α)))⁻¹ +
            (1 - (Λ : ℝ) ^ (-α))⁻¹ := by linarith
    calc
      _ ≤ (ocEpsilon q Λ 1 ^ α) / (1 - (Λ : ℝ) ^ (-α)) := henvBound
      _ ≤ (d ^ α) / (1 - (Λ : ℝ) ^ (-α)) :=
        div_le_div_of_nonneg_right hfirstPower hdenα.le
      _ ≤ ((1 - (Λ : ℝ) ^ (-(1 - α)))⁻¹ +
          (1 - (Λ : ℝ) ^ (-α))⁻¹) * d ^ α := by
        rw [div_eq_mul_inv]
        calc
          d ^ α * (1 - (Λ : ℝ) ^ (-α))⁻¹ =
              (1 - (Λ : ℝ) ^ (-α))⁻¹ * d ^ α := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hcoefficient
            (Real.rpow_nonneg hd.le α)
end

end AVRegularity.Velocity
end

section
open Filter Topology Homogenization
namespace AVRegularity.Velocity

/-! Conditional assembly of endpoint velocity convergence from one-step increment bounds. -/

/-- The joint distance used by `IsHolderDivFreeVelocity`. -/
noncomputable def jointDistance (p q : ℝ × Vec 2) : ℝ :=
  |p.1 - q.1| + Real.sqrt (vecNormSq (p.2 - q.2))

theorem jointDistance_nonneg (p q : ℝ × Vec 2) : 0 ≤ jointDistance p q := by
  exact add_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)

theorem jointDistance_eq_zero_iff {p q : ℝ × Vec 2} :
    jointDistance p q = 0 ↔ p = q := by
  constructor
  · intro h
    have htime : |p.1 - q.1| = 0 := by
      have hs := Real.sqrt_nonneg (vecNormSq (p.2 - q.2))
      dsimp [jointDistance] at h
      have h₁ : 0 ≤ |p.1 - q.1| := abs_nonneg _
      have h₂ : 0 ≤ Real.sqrt (vecNormSq (p.2 - q.2)) := hs
      exact le_antisymm (by linarith) (by linarith)
    have hx : Real.sqrt (vecNormSq (p.2 - q.2)) = 0 := by
      have hs := abs_nonneg (p.1 - q.1)
      dsimp [jointDistance] at h
      have h₁ : 0 ≤ |p.1 - q.1| := hs
      have h₂ : 0 ≤ Real.sqrt (vecNormSq (p.2 - q.2)) := Real.sqrt_nonneg _
      exact le_antisymm (by linarith) (by linarith)
    have hvec : vecNormSq (p.2 - q.2) = 0 :=
      (Real.sqrt_eq_zero (vecNormSq_nonneg _)).mp hx
    have hxy : p.2 = q.2 := sub_eq_zero.mp (vecNormSq_eq_zero hvec)
    have ht : p.1 = q.1 := sub_eq_zero.mp (abs_eq_zero.mp htime)
    cases p with
    | mk t x =>
      cases q with
      | mk u y =>
        simp only [Prod.mk.injEq]
        exact ⟨ht, hxy⟩
  · rintro rfl
    simp [jointDistance, vecNormSq, vecDot]

private theorem velocityScaleSeriesSummable {α s q : ℝ} {Λ : ℕ}
    (hα : 0 < α) (hq : IsAdmissibleQ α s q) (hΛ : 128 ≤ Λ) :
    Summable (fun n : ℕ => ocEpsilon q Λ (n + 1) ^ α) := by
  simpa [Nat.add_comm] using
    (Scales.admissible_epsilon_forward_tail (q := q) hq hΛ
      (m := 1) (by norm_num) hα).1

/-- If the velocity increments have the standard amplitude and joint Lipschitz
bounds at their own wavelengths, their partial sums converge pointwise and the
limit is jointly `C^α` at the endpoint. The stream-specific proof still has to
derive `hamplitude` and `hincrement` from the recursive flow formula. -/
theorem endpoint_limit_of_increment_bounds {α s q C : ℝ} {Λ : ℕ}
    (hα₀ : 0 < α) (hα₁ : α < 1)
    (hq : IsAdmissibleQ α s q) (hΛ : 128 ≤ Λ)
    (hC : 0 ≤ C)
    (v : ℕ → ℝ → Vec 2 → Vec 2)
    (hamplitude : ∀ n t x,
      ‖v n t x‖ ≤ C * ocEpsilon q Λ (n + 1) ^ α)
    (hincrement : ∀ n t u x y,
      ‖v n t x - v n u y‖ ≤ C * min
        (ocEpsilon q Λ (n + 1) ^ α)
        ((|t - u| + Real.sqrt (vecNormSq (x - y))) *
          ocEpsilon q Λ (n + 1) ^ (α - 1))) :
    ∃ b : ℝ → Vec 2 → Vec 2,
      (∀ t x, Tendsto
        (fun M => ∑ n ∈ Finset.range M, v n t x) atTop (𝓝 (b t x))) ∧
      (∀ t u x y, ‖b t x - b u y‖ ≤
        C * ((1 - (Λ : ℝ) ^ (-(1 - α)))⁻¹ +
          (1 - (Λ : ℝ) ^ (-α))⁻¹) *
          (|t - u| + Real.sqrt (vecNormSq (x - y))) ^ α) := by
  have hscale := velocityScaleSeriesSummable hα₀ hq hΛ
  let b : ℝ → Vec 2 → Vec 2 := fun t x => ∑' n : ℕ, v n t x
  have hsum (t : ℝ) (x : Vec 2) : Summable (fun n : ℕ => v n t x) := by
    apply Summable.of_norm_bounded (hscale.mul_left C)
    intro n
    have heps : 0 < ocEpsilon q Λ (n + 1) :=
      (Scales.admissible_space_scale_facts (q := q) hq hΛ
        (m := n + 1) (by omega)).1.1
    have hmajor : 0 ≤ C * ocEpsilon q Λ (n + 1) ^ α :=
      mul_nonneg hC (Real.rpow_nonneg heps.le α)
    simpa only [Real.norm_of_nonneg hmajor] using hamplitude n t x
  refine ⟨b, ?_, ?_⟩
  · intro t x
    exact (hsum t x).hasSum.tendsto_sum_nat
  · intro t u x y
    let p : ℝ × Vec 2 := (t, x)
    let q' : ℝ × Vec 2 := (u, y)
    let d := jointDistance p q'
    have hdnonneg : 0 ≤ d := jointDistance_nonneg p q'
    have hdiffSummable : Summable (fun n : ℕ =>
        ‖v n t x - v n u y‖) := by
      apply (hscale.mul_left (2 * C)).of_nonneg_of_le
      · intro n
        exact norm_nonneg _
      · intro n
        have hleft := hamplitude n t x
        have hright := hamplitude n u y
        calc
          ‖v n t x - v n u y‖ ≤ ‖v n t x‖ + ‖v n u y‖ := norm_sub_le _ _
          _ ≤ C * ocEpsilon q Λ (n + 1) ^ α +
              C * ocEpsilon q Λ (n + 1) ^ α := add_le_add hleft hright
          _ = (2 * C) * ocEpsilon q Λ (n + 1) ^ α := by ring
    have htsumSub := ((hsum t x).hasSum.sub (hsum u y).hasSum).tsum_eq
    change ‖(∑' n : ℕ, v n t x) - (∑' n : ℕ, v n u y)‖ ≤ _
    rw [← htsumSub]
    by_cases hdzero : d = 0
    · have hpq : p = q' := (jointDistance_eq_zero_iff).mp hdzero
      have hxy : x = y := by
        have := congrArg Prod.snd hpq
        exact this
      have htu : t = u := by
        have := congrArg Prod.fst hpq
        exact this
      simp [hxy, htu, Real.zero_rpow, ne_of_gt hα₀,
        vecNormSq, vecDot]
    · have hdpos : 0 < d := lt_of_le_of_ne hdnonneg (Ne.symm hdzero)
      let env : ℕ → ℝ := fun n => min
        (ocEpsilon q Λ (n + 1) ^ α)
        (d * ocEpsilon q Λ (n + 1) ^ (α - 1))
      have henvNonneg : ∀ n, 0 ≤ env n := by
        intro n
        dsimp [env]
        apply le_min
        · exact Real.rpow_nonneg
            (Scales.admissible_space_scale_facts (q := q) hq hΛ
              (m := n + 1) (by omega)).1.1.le α
        · exact mul_nonneg hdpos.le (Real.rpow_nonneg
            (Scales.admissible_space_scale_facts (q := q) hq hΛ
              (m := n + 1) (by omega)).1.1.le _)
      have henvLe : ∀ n, env n ≤ ocEpsilon q Λ (n + 1) ^ α := by
        intro n
        exact min_le_left _ _
      have henvSummable : Summable env := hscale.of_nonneg_of_le henvNonneg henvLe
      have hpointwise : ∀ n,
          ‖v n t x - v n u y‖ ≤ C * env n := by
        intro n
        have hi := hincrement n t u x y
        simpa [env, d, jointDistance] using hi
      have hmajorSummable : Summable (fun n => C * env n) := henvSummable.mul_left C
      have hnormSum :
          (∑' n : ℕ, ‖v n t x - v n u y‖) ≤ C * (∑' n : ℕ, env n) := by
        calc
          _ ≤ ∑' n : ℕ, C * env n :=
            Summable.tsum_le_tsum hpointwise hdiffSummable hmajorSummable
          _ = C * (∑' n : ℕ, env n) := tsum_mul_left
      have hEnvelope := endpoint_increment_envelope_tsum_bound_all
        hα₀ hα₁ hq hΛ hdpos
      have hfinal := mul_le_mul_of_nonneg_left hEnvelope hC
      calc
        ‖∑' n : ℕ, (v n t x - v n u y)‖ ≤
            ∑' n : ℕ, ‖v n t x - v n u y‖ := norm_tsum_le_tsum_norm hdiffSummable
        _ ≤ C * (∑' n : ℕ, env n) := hnormSum
        _ ≤ C * ((1 - (Λ : ℝ) ^ (-(1 - α)))⁻¹ +
            (1 - (Λ : ℝ) ^ (-α))⁻¹) * d ^ α := by
          calc
            _ ≤ C * (((1 - (Λ : ℝ) ^ (-(1 - α)))⁻¹ +
                (1 - (Λ : ℝ) ^ (-α))⁻¹) * d ^ α) := hfinal
            _ = _ := by ring

end AVRegularity.Velocity
end

section
open MeasureTheory Homogenization AVenhance
namespace AVRegularity.Velocity

/-! Finite-stage periodicity and incompressibility of the velocity sequence. -/

/-- Every term of an OC stream sequence (`IsOCStreamSeq`) is an admissible stream. -/
theorem streamSeq_admissible {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hζ : IsFastProfile ζ) (hΛ : 128 ≤ Λ)
    (hΦ : IsOCStreamSeq α q Λ ζ Φ) (m : ℕ) :
    IsAdmissibleStream (Φ m) := by
  have hΛ' : 1 ≤ Λ := by omega
  induction m with
  | zero =>
      refine ⟨?_, ?_⟩
      · rw [hΦ.1]
        exact contDiff_const
      · intro n k t x
        rw [hΦ.1]
  | succ m ihm =>
      obtain ⟨hprev, hrec⟩ := hΦ.2 (m + 1) (by omega)
      have hprev' : IsAdmissibleStream (Φ m) := ihm
      have heq : hprev = hprev' := Subsingleton.elim _ _
      have hstep := AVRegularity.Construction.Stream.ocNextStream_isAdmissible
        α q Λ ζ hζ hΛ' (m + 1) (by omega) (Φ m) hprev'
      rw [hrec]
      simpa [heq] using hstep

/-- Each finite velocity is spatially periodic. -/
theorem streamSeq_velocity_spatial_periodic {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hζ : IsFastProfile ζ) (hΛ : 128 ≤ Λ)
    (hΦ : IsOCStreamSeq α q Λ ζ Φ) (m : ℕ) (t : ℝ) :
    IsZ2Periodic (streamVel (Φ m) t) := by
  exact AVenhance.Infra.FullTheorem.streamVel_isZ2Periodic
    (streamSeq_admissible hζ hΛ hΦ m) t

/-- Each finite velocity is one-periodic in time. -/
theorem streamSeq_velocity_time_periodic {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hζ : IsFastProfile ζ) (hΛ : 128 ≤ Λ)
    (hΦ : IsOCStreamSeq α q Λ ζ Φ) (m : ℕ) (t : ℝ) (x : Vec 2) :
    streamVel (Φ m) (t + 1) x = streamVel (Φ m) t x := by
  have hstream := streamSeq_admissible hζ hΛ hΦ m
  have hzeroShift : latticeShift (0 : Fin 2 → ℤ) = (0 : Vec 2) := by
    ext i
    simp [latticeShift]
  have htime : Φ m (t + 1) = Φ m t := by
    funext y
    simpa [hzeroShift] using hstream.2 (1 : ℤ) (0 : Fin 2 → ℤ) t y
  simp [AVenhance.streamVel, htime]

/-- Each finite velocity is divergence-free on every time slice. -/
theorem streamSeq_velocity_divFree {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hζ : IsFastProfile ζ) (hΛ : 128 ≤ Λ)
    (hΦ : IsOCStreamSeq α q Λ ζ Φ) (m : ℕ) :
    ∀ t : ℝ, ∀ φ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, vecDot (streamVel (Φ m) t x) (spaceGrad φ x) = 0 := by
  let hm := streamSeq_admissible hζ hΛ hΦ m
  have hdivFree := AVenhance.Infra.FullTheorem.isDivFree_streamVel hm
  intro t φ hφ hφc
  let n : ℤ := ⌊t⌋
  let r : ℝ := t - (n : ℝ)
  have hr₀ : 0 ≤ r := by
    change 0 ≤ t - (n : ℝ)
    exact sub_nonneg.mpr (by dsimp [n]; exact Int.floor_le t)
  have hr₁ : r ≤ 1 := by
    have hf : t < (n : ℝ) + 1 := by
      dsimp [n]
      exact Int.lt_floor_add_one t
    change t - (n : ℝ) ≤ 1
    linarith
  have hperiod : streamVel (Φ m) t = streamVel (Φ m) r := by
    have htime : Φ m t = Φ m r := by
      funext x
      have hzeroShift : latticeShift (0 : Fin 2 → ℤ) = (0 : Vec 2) := by
        ext i
        simp [latticeShift]
      have h := hm.2 n (0 : Fin 2 → ℤ) r x
      have harg : r + (n : ℝ) = t := by
        dsimp [r]
        ring
      simpa [harg, hzeroShift] using h
    funext x
    simp [AVenhance.streamVel, htime]
  have hslice := hdivFree r ⟨hr₀, hr₁⟩ φ hφ hφc
  have hintegrand :
      (fun x => vecDot (streamVel (Φ m) t x) (spaceGrad φ x)) =
      (fun x => vecDot (streamVel (Φ m) r x) (spaceGrad φ x)) := by
    funext x
    rw [congrFun hperiod x]
  rw [hintegrand]
  exact hslice

end AVRegularity.Velocity
end

section
open Homogenization AVenhance MeasureTheory Filter Topology
namespace AVRegularity.Velocity

/-! Bounded pointwise limits preserve the finite velocities' structure. -/

/-- Uniformly bounded continuous divergence-free fields remain distributionally
 divergence-free under pointwise convergence, on every time slice. -/
theorem divFree_of_bounded_pointwise_limit
    {v : ℕ → ℝ → Vec 2 → Vec 2} {b : ℝ → Vec 2 → Vec 2} {B : ℝ}
    (hcont : ∀ m t, Continuous (v m t))
    (hbnd : ∀ m t x, ‖v m t x‖ ≤ B)
    (hconv : ∀ t x, Tendsto (fun m => v m t x) atTop (𝓝 (b t x)))
    (hdiv : ∀ m t φ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, vecDot (v m t x) (spaceGrad φ x) = 0) :
    ∀ t φ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ x, vecDot (b t x) (spaceGrad φ x) = 0 := by
  intro t φ hφ hc
  let g : Vec 2 → ℝ := fun x =>
    B * (|fderiv ℝ φ x (basisVec 0)| + |fderiv ℝ φ x (basisVec 1)|)
  have hpartial (i : Fin 2) : Continuous (fun x => fderiv ℝ φ x (basisVec i)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hint (i : Fin 2) : Integrable (fun x => |fderiv ℝ φ x (basisVec i)|) :=
    ((hpartial i).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ (basisVec i))).abs
  have hgi : Integrable g := ((hint 0).add (hint 1)).const_mul B
  have hmcont (m : ℕ) : Continuous (fun x => vecDot (v m t x) (spaceGrad φ x)) := by
    unfold vecDot spaceGrad
    fun_prop
  have hbound (m : ℕ) : ∀ x, ‖vecDot (v m t x) (spaceGrad φ x)‖ ≤ g x := by
    intro x
    have hcoord (i : Fin 2) : |v m t x i| ≤ B :=
      (show |v m t x i| ≤ ‖v m t x‖ by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm (v m t x) i).trans (hbnd m t x)
    change |∑ i : Fin 2, v m t x i * fderiv ℝ φ x (basisVec i)| ≤ _
    calc
      _ ≤ ∑ i : Fin 2, |v m t x i * fderiv ℝ φ x (basisVec i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin 2, B * |fderiv ℝ φ x (basisVec i)| := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hcoord i) (abs_nonneg _)
      _ = g x := by simp [g, Fin.sum_univ_two]; ring
  have hpoint (x : Vec 2) : Tendsto
      (fun m => vecDot (v m t x) (spaceGrad φ x)) atTop
      (𝓝 (vecDot (b t x) (spaceGrad φ x))) := by
    unfold vecDot
    exact tendsto_finsetSum _ fun i _ =>
      ((continuous_apply i).tendsto _ |>.comp (hconv t x)).mul_const _
  have hi := tendsto_integral_of_dominated_convergence g
    (fun m => (hmcont m).aestronglyMeasurable) hgi
    (fun m => Filter.Eventually.of_forall (hbound m))
    (Filter.Eventually.of_forall hpoint)
  have hz : (fun m => ∫ x, vecDot (v m t x) (spaceGrad φ x)) = fun _ => (0 : ℝ) := by
    funext m
    exact hdiv m t φ hφ hc
  rw [hz] at hi
  exact tendsto_nhds_unique hi tendsto_const_nhds

/-- The finite-stage periodicities and bound pass to the limit; the Hölder
estimate is supplied by the endpoint summation theorem. -/
theorem holderDivFree_of_streamSeq_limit {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} {b : ℝ → Vec 2 → Vec 2}
    (hζ : IsFastProfile ζ) (hΛ : 128 ≤ Λ) (hseq : IsOCStreamSeq α q Λ ζ Φ)
    {B H : ℝ} (hbnd : ∀ m t x, ‖streamVel (Φ m) t x‖ ≤ B)
    (hconv : ∀ t x, Tendsto (fun m => streamVel (Φ m) t x) atTop (𝓝 (b t x)))
    (hh : ∀ t u x y, ‖b t x - b u y‖ ≤
      H * (|t - u| + Real.sqrt (vecNormSq (x - y))) ^ α) :
    IsHolderDivFreeVelocity α b := by
  refine ⟨?_, ?_, ⟨B, ?_⟩, ⟨H, hh⟩, ?_⟩
  · intro t n x
    have hp : Tendsto (fun m => streamVel (Φ m) t (x + latticeShift n))
        atTop (𝓝 (b t x)) := by
      have heq : (fun m => streamVel (Φ m) t (x + latticeShift n)) =
          fun m => streamVel (Φ m) t x := by
        funext m
        exact streamSeq_velocity_spatial_periodic hζ hΛ hseq m t n x
      rw [heq]
      exact hconv t x
    exact tendsto_nhds_unique (hconv t (x + latticeShift n)) hp
  · intro t x
    have hp : Tendsto (fun m => streamVel (Φ m) (t + 1) x) atTop (𝓝 (b t x)) := by
      have heq : (fun m => streamVel (Φ m) (t + 1) x) = fun m => streamVel (Φ m) t x := by
        funext m
        exact streamSeq_velocity_time_periodic hζ hΛ hseq m t x
      rw [heq]
      exact hconv t x
    exact tendsto_nhds_unique (hconv (t + 1) x) hp
  · intro t x
    exact le_of_tendsto (hconv t x |>.norm) (Filter.Eventually.of_forall fun m => hbnd m t x)
  · apply divFree_of_bounded_pointwise_limit (hbnd := hbnd) (hconv := hconv)
    · intro m t
      exact ((AVenhance.Infra.Construction.smoothPeriodic_streamVel
        (streamSeq_admissible hζ hΛ hseq m)).smooth.comp
          (contDiff_const.prodMk contDiff_id)).continuous
    · exact streamSeq_velocity_divFree hζ hΛ hseq

end AVRegularity.Velocity
end

section
open Filter Topology Homogenization AVenhance
namespace AVRegularity.Velocity

/-! The stream-specific endpoint limit theorem, conditional on one-step estimates. -/

private theorem sum_range_sub_sequence {E : Type*} [AddCommGroup E]
    (f : ℕ → E) (M : ℕ) :
    (∑ n ∈ Finset.range M, (f (n + 1) - f n)) = f M - f 0 := by
  induction M with
  | zero => simp
  | succ M ih =>
      simp only [Finset.sum_range_succ]
      rw [ih]
      abel

/-- The velocity limit and endpoint joint Hölder estimate follow from the
per-step amplitude and increment bounds of the stream recursion. -/
theorem exists_limit_velocity_of_increment_bounds
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (q : ℝ) (hq : IsAdmissibleQ α s q)
    (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (ζ : ℝ → ℝ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (hΦ : IsOCStreamSeq α q Λ ζ Φ)
    (C : ℝ) (hC : 0 ≤ C)
    (hamplitude : ∀ m t x,
      ‖streamVel (Φ (m + 1)) t x - streamVel (Φ m) t x‖ ≤
        C * ocEpsilon q Λ (m + 1) ^ α)
    (hincrement : ∀ m t u x y,
      ‖(streamVel (Φ (m + 1)) t x - streamVel (Φ m) t x) -
          (streamVel (Φ (m + 1)) u y - streamVel (Φ m) u y)‖ ≤
        C * min (ocEpsilon q Λ (m + 1) ^ α)
          ((|t - u| + Real.sqrt (vecNormSq (x - y))) *
            ocEpsilon q Λ (m + 1) ^ (α - 1))) :
    ∃ b : ℝ → Vec 2 → Vec 2,
      (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) ∧
      (∀ t u x y, ‖b t x - b u y‖ ≤
        C * ((1 - (Λ : ℝ) ^ (-(1 - α)))⁻¹ +
          (1 - (Λ : ℝ) ^ (-α))⁻¹) *
          (|t - u| + Real.sqrt (vecNormSq (x - y))) ^ α) := by
  let v : ℕ → ℝ → Vec 2 → Vec 2 := fun m t x =>
    streamVel (Φ (m + 1)) t x - streamVel (Φ m) t x
  have hbase : ∀ t x, streamVel (Φ 0) t x = 0 := by
    intro t x
    rw [hΦ.1]
    simp [AVenhance.streamVel, AVenhance.spaceGrad]
  have hpartial : ∀ M t x,
      (∑ m ∈ Finset.range M, v m t x) = streamVel (Φ M) t x := by
    intro M t x
    have htel := sum_range_sub_sequence
      (fun m => streamVel (Φ m) t x) M
    rw [hbase] at htel
    simpa [v] using htel
  have hconditions :
      (∀ m t x, ‖v m t x‖ ≤ C * ocEpsilon q Λ (m + 1) ^ α) ∧
      (∀ m t u x y, ‖v m t x - v m u y‖ ≤ C * min
        (ocEpsilon q Λ (m + 1) ^ α)
        ((|t - u| + Real.sqrt (vecNormSq (x - y))) *
          ocEpsilon q Λ (m + 1) ^ (α - 1))) := by
    constructor
    · exact hamplitude
    · exact hincrement
  obtain ⟨b, hconv, hholder⟩ := endpoint_limit_of_increment_bounds
    hα₀ (by linarith) hq hΛ hC v hconditions.1 hconditions.2
  refine ⟨b, ?_, hholder⟩
  intro t x
  have hsumTendsto := hconv t x
  have heq : (fun M => ∑ m ∈ Finset.range M, v m t x) =
      (fun M => streamVel (Φ M) t x) := by
    funext M
    exact hpartial M t x
  rw [heq] at hsumTendsto
  exact hsumTendsto

end AVRegularity.Velocity
end
