-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.OcEpsilon
public import AVRegularity.Statements.Construction.OcGamma
public import AVRegularity.Statements.Construction.OcDelta
public import AVRegularity.Statements.Construction.OcTau
public import AVRegularity.Statements.Construction.OcTauP
public import AVRegularity.Statements.Intermediate.CycleReference.OcBand
public import AVRegularity.Definitions.CycleReference.OcAsymp
public import AVRegularity.Definitions.Construction.ScheduleFloor
import AVRegularity.Construction.Scales.Times
import AVRegularity.Construction.EntryScales.TerminalCore
import AVRegularity.CycleReference.TorusChartEquation
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Definitions.Iteration.CascadeStatement
import Mathlib.Analysis.SpecificLimits.Basic

/-! Public arithmetic lemmas used by the paper-facing statements.

Each statement is elementary from existing declarations (`epsilon_q_step`, `epsilon_ratio_lower`,
`admissible_time_scale_facts`, `terminal_comparisons`, the definitions of `ocDelta`, `ocGamma`,
`ocMuS`) and the definitions; collected here so that they can be cited by name. -/

@[expose] public section

namespace AVRegularity.PaperFacing

open AVRegularity.Scales

/-! ### The one-step ratio of the wavelengths -/

/-- Lower half of `ε_m ≍ ε_{m-1}^q`: `ε_m ≥ ε_{m-1}^q / 2` for `m ≥ 2` (all `Λ ≥ 128`). -/
theorem epsilon_q_ratio_lower_half {q : ℝ} {Λ m : ℕ}
    (hq : 1 < q) (hΛ : 128 ≤ Λ) (hm : 2 ≤ m) :
    1 / 2 ≤ ocEpsilon q Λ m / ocEpsilon q Λ (m - 1) ^ q := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  have hΛr : (128 : ℝ) ≤ Λ := by exact_mod_cast hΛ
  have hΛ1 : (1 : ℝ) ≤ Λ := by linarith
  have hq0 : 0 < q - 1 := by linarith
  set y : ℝ := (Λ : ℝ) ^ (q ^ (n + 1) / (q - 1)) with hy
  have hy1 : 1 ≤ y := by
    apply Real.one_le_rpow hΛ1
    exact div_nonneg (pow_nonneg (by linarith) _) hq0.le
  have hypos : 0 < y := by linarith
  set x : ℝ := (Λ : ℝ) ^ (q ^ (n + 2) / (q - 1)) with hx
  have hxy : x = y ^ q := by
    rw [hx, hy, ← Real.rpow_mul (by linarith)]
    congr 1
    rw [pow_succ]
    ring
  have hxpos : 0 < x := by rw [hxy]; exact Real.rpow_pos_of_pos hypos q
  have hx1 : 1 ≤ x := by rw [hxy]; exact Real.one_le_rpow hy1 (by linarith)
  have hE1 : ocEpsilon q Λ (n + 2 - 1) = ((⌈y⌉₊ : ℕ) : ℝ)⁻¹ := by
    simp [ocEpsilon, hy]
  have hE2 : ocEpsilon q Λ (n + 2) = ((⌈x⌉₊ : ℕ) : ℝ)⁻¹ := by
    simp [ocEpsilon, hx]
  have hceily : y ≤ (⌈y⌉₊ : ℝ) := Nat.le_ceil y
  have hceilx : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hxpos.le
  have hcxpos : 0 < (⌈x⌉₊ : ℝ) := lt_of_lt_of_le hxpos (Nat.le_ceil x)
  have hEq : ocEpsilon q Λ (n + 2 - 1) ^ q ≤ x⁻¹ := by
    rw [hE1, hxy, ← Real.inv_rpow hypos.le]
    exact Real.rpow_le_rpow (by positivity) (inv_anti₀ hypos hceily) (by linarith)
  have hEqpos : 0 < ocEpsilon q Λ (n + 2 - 1) ^ q := by
    rw [hE1]
    exact Real.rpow_pos_of_pos (inv_pos.mpr (lt_of_lt_of_le hypos hceily)) q
  rw [hE2, le_div_iff₀ hEqpos]
  have h1 : (⌈x⌉₊ : ℝ)⁻¹ ≥ (x + 1)⁻¹ := inv_anti₀ hcxpos hceilx.le
  have h2 : 1 / 2 * x⁻¹ ≤ (x + 1)⁻¹ := by
    rw [← sub_nonneg]
    have h3 : (x + 1)⁻¹ - 1 / 2 * x⁻¹ = (x - 1) / (2 * x * (x + 1)) := by
      field_simp
      ring
    rw [h3]
    exact div_nonneg (by linarith) (by positivity)
  calc 1 / 2 * ocEpsilon q Λ (n + 2 - 1) ^ q ≤ 1 / 2 * x⁻¹ := by linarith
    _ ≤ (x + 1)⁻¹ := h2
    _ ≤ _ := h1

/-- `ε_m ≍ ε_{m-1}^q` for `m ≥ 2` with the explicit constants `1/2` and `2`, for every `Λ ≥ 128`
(`q ∈ (1, 17/16)`). -/
theorem epsilon_q_ratio_bounds {q : ℝ} {Λ m : ℕ}
    (hq : 1 < q) (hq₁₆ : q < 17 / 16) (hΛ : 128 ≤ Λ) (hm : 2 ≤ m) :
    1 / 2 ≤ ocEpsilon q Λ m / ocEpsilon q Λ (m - 1) ^ q ∧
      ocEpsilon q Λ m / ocEpsilon q Λ (m - 1) ^ q ≤ 2 := by
  refine ⟨epsilon_q_ratio_lower_half hq hΛ hm, ?_⟩
  have hbasic := (epsilon_basic (m := m - 1) hq hΛ).1
  have hstep := epsilon_q_step hq hq₁₆ hΛ (by omega : 1 ≤ m)
  rw [div_le_iff₀ (Real.rpow_pos_of_pos hbasic q)]
  exact hstep

/-! ### Existence of `q` and the converses of the positivities -/

/-- An admissible `q` exists as soon as `α < 1/3` and `s < (1-α)/2` (with `α, s > 0`). -/
theorem exists_isAdmissibleQ_of_lt
    {α s : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) :
    ∃ q : ℝ, IsAdmissibleQ α s q := by
  have hαden : 0 < 2 * α := by positivity
  have hsden : 0 < α + s := by positivity
  have hq₂ : 1 < (2 - (1 + α)) / (2 * ((1 + α) - 1)) := by
    rw [show 2 - (1 + α) = 1 - α by ring, show (1 + α) - 1 = α by ring]
    apply (lt_div_iff₀ hαden).2
    linarith
  have hq₃ : 1 < (1 - s) / ((1 + α) - 1 + s) := by
    rw [show (1 + α) - 1 + s = α + s by ring]
    apply (lt_div_iff₀ hsden).2
    linarith
  set U : ℝ := min (17 / 16)
    (min ((2 - (1 + α)) / (2 * ((1 + α) - 1))) ((1 - s) / ((1 + α) - 1 + s))) with hU
  have hU1 : 1 < U := lt_min (by norm_num) (lt_min hq₂ hq₃)
  have hqU : (1 + U) / 2 < U := by linarith
  refine ⟨(1 + U) / 2, by linarith, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le hqU (min_le_left _ _)
  · exact lt_of_lt_of_le hqU (le_trans (min_le_right _ _) (min_le_left _ _))
  · exact lt_of_lt_of_le hqU (le_trans (min_le_right _ _) (min_le_right _ _))

/-- An admissible `q` forces `α < 1/3` and `s < (1-α)/2` (and `α > 0`). -/
theorem lt_of_isAdmissibleQ {α s q : ℝ} (hs₀ : 0 < s) (hq : IsAdmissibleQ α s q) :
    0 < α ∧ α < 1 / 3 ∧ s < (1 - α) / 2 := by
  obtain ⟨hq₀, -, hq₂, hq₃⟩ := hq
  rw [show 2 - (1 + α) = 1 - α by ring, show (1 + α) - 1 = α by ring] at hq₂
  rw [show (1 + α) - 1 + s = α + s by ring] at hq₃
  have hα : 0 < α := by
    by_contra h
    rw [not_lt] at h
    rcases h.eq_or_lt with h | h
    · rw [h] at hq₂; simp at hq₂; linarith
    · have : (1 - α) / (2 * α) < 0 := div_neg_of_pos_of_neg (by linarith) (by linarith)
      linarith
  have hsum : 0 < α + s := by linarith
  have h2 := (lt_div_iff₀ (by linarith : 0 < 2 * α)).1 (lt_trans hq₀ hq₂)
  have h3 := (lt_div_iff₀ hsum).1 (lt_trans hq₀ hq₃)
  refine ⟨hα, by linarith, by linarith⟩

/-- An admissible `q` exists iff `α < 1/3` and `s < (1-α)/2`, for `α, s > 0`. -/
theorem exists_isAdmissibleQ_iff
    {α s : ℝ} (hα₀ : 0 < α) (hs₀ : 0 < s) :
    (∃ q : ℝ, IsAdmissibleQ α s q) ↔ α < 1 / 3 ∧ s < (1 - α) / 2 := by
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨-, h1, h2⟩ := lt_of_isAdmissibleQ hs₀ hq
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact exists_isAdmissibleQ_of_lt hα₀ h1 hs₀ h2

/-- `δ > 0` iff `q < (2-β)/(2(β-1))`, `β = 1 + α` (for `q > 1`, `α > 0`). -/
theorem ocDelta_pos_iff {α q : ℝ} (hα : 0 < α) (hq : 1 < q) :
    0 < ocDelta α q ↔ q < (2 - (1 + α)) / (2 * ((1 + α) - 1)) := by
  rw [show 2 - (1 + α) = 1 - α by ring, show (1 + α) - 1 = α by ring,
    lt_div_iff₀ (by positivity : 0 < 2 * α)]
  have hden : 0 < 2 * q + 2 := by linarith
  have hid : 1 - (2 * q + 1) * (1 + α) / (2 * q + 2) = (1 - α - 2 * α * q) / (2 * q + 2) := by
    field_simp
    ring
  unfold ocDelta
  rw [hid]
  constructor
  · intro h
    have h' := (pos_iff_pos_of_mul_pos (a := (q - 1) / 4) (b := (1 - α - 2 * α * q) / (2 * q + 2))
      (by simpa using h))
    have := h'.mp (by linarith)
    have h3 : 0 < 1 - α - 2 * α * q := by
      by_contra hc
      rw [not_lt] at hc
      have : (1 - α - 2 * α * q) / (2 * q + 2) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hc hden.le
      have h4 : (q - 1) / 4 * ((1 - α - 2 * α * q) / (2 * q + 2)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) this
      linarith
    nlinarith
  · intro h
    apply mul_pos (by linarith)
    apply div_pos _ hden
    nlinarith

/-- `μ_s > 0` iff `q < (1-s)/(β-1+s)` (for `q > 1`, `α + s > 0`). -/
theorem ocMuS_pos_iff {α s q : ℝ} (hαs : 0 < α + s) (hq : 1 < q) :
    0 < ocMuS α q s ↔ q < (1 - s) / ((1 + α) - 1 + s) := by
  rw [show (1 + α) - 1 + s = α + s by ring, lt_div_iff₀ hαs]
  have hden : 0 < q + 1 := by linarith
  have hid : ocMuS α q s = (q - 1) / (q + 1) * (1 - s - q * (α + s)) := by
    unfold ocMuS ocGamma
    field_simp
    ring
  rw [hid]
  have hpos : 0 < (q - 1) / (q + 1) := div_pos (by linarith) hden
  constructor
  · intro h
    have := (pos_iff_pos_of_mul_pos h).mp hpos
    linarith
  · intro h
    exact mul_pos hpos (by linarith)

/-! ### `γ > 3δ` -/

/-- `γ - 3δ = (q-1)(5 + (6q+11)α) / (8(q+1)) > 0`. -/
theorem ocGamma_sub_three_mul_ocDelta {α q : ℝ} (hq : q + 1 ≠ 0) :
    ocGamma α q - 3 * ocDelta α q = (q - 1) * (5 + (6 * q + 11) * α) / (8 * (q + 1)) := by
  unfold ocGamma ocDelta
  have h2 : 2 * q + 2 ≠ 0 := by intro h; apply hq; linarith
  field_simp
  ring

/-- `γ > 3δ` for `α > 0`, `q > 1`. -/
theorem ocDelta_three_mul_lt_ocGamma {α q : ℝ} (hα : 0 < α) (hq : 1 < q) :
    3 * ocDelta α q < ocGamma α q := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  have := ocGamma_sub_three_mul_ocDelta (α := α) (q := q) (by linarith)
  have hp : 0 < ocGamma α q - 3 * ocDelta α q := by
    rw [this]
    apply div_pos
    · exact mul_pos (sub_pos.mpr hq) (by positivity)
    · linarith
  linarith

/-! ### Convergent sums -/

/-- `ε_m ≤ Λ^{-m}`. -/
theorem epsilon_le_inv_pow {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ) (m : ℕ) :
    ocEpsilon q Λ m ≤ ((Λ : ℝ)⁻¹) ^ m := by
  have hΛr : (128 : ℝ) ≤ Λ := by exact_mod_cast hΛ
  have hΛpos : (0 : ℝ) < Λ := by linarith
  induction m with
  | zero => simp [ocEpsilon]
  | succ n ih =>
    have hr := epsilon_ratio_lower (m := n + 1) hq hΛ (by omega)
    have hpos := (epsilon_basic (m := n + 1) hq hΛ).1
    simp only [Nat.add_sub_cancel] at hr
    rw [ge_iff_le, le_div_iff₀ hpos] at hr
    rw [pow_succ]
    have h1 : ocEpsilon q Λ (n + 1) ≤ ocEpsilon q Λ n * (Λ : ℝ)⁻¹ := by
      rw [le_mul_inv_iff₀ hΛpos]
      linarith
    calc ocEpsilon q Λ (n + 1) ≤ ocEpsilon q Λ n * (Λ : ℝ)⁻¹ := h1
      _ ≤ ((Λ : ℝ)⁻¹) ^ n * (Λ : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right ih (inv_nonneg.mpr hΛpos.le)

/-- Partial sums: `∑_{m<n} ε_m^c ≤ (1 - Λ^{-c})⁻¹` for `c > 0`, `Λ ≥ 128`; with `m ↦ m - 1`
this is `∑_{m=1}^{n} ε_{m-1}^c`. -/
theorem sum_range_epsilon_rpow_le {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ)
    {c : ℝ} (hc : 0 < c) (n : ℕ) :
    ∑ m ∈ Finset.range n, ocEpsilon q Λ m ^ c ≤ (1 - (Λ : ℝ) ^ (-c))⁻¹ := by
  have hΛr : (128 : ℝ) ≤ Λ := by exact_mod_cast hΛ
  have hΛpos : (0 : ℝ) < Λ := by linarith
  set r : ℝ := (Λ : ℝ) ^ (-c) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg hΛpos.le _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by linarith)
  have hterm : ∀ m : ℕ, ocEpsilon q Λ m ^ c ≤ r ^ m := by
    intro m
    have hE := (epsilon_basic (m := m) hq hΛ).1
    calc ocEpsilon q Λ m ^ c ≤ (((Λ : ℝ)⁻¹) ^ m) ^ c :=
          Real.rpow_le_rpow hE.le (epsilon_le_inv_pow hq hΛ m) hc.le
      _ = r ^ m := by
          rw [hr, Real.rpow_neg hΛpos.le, ← Real.inv_rpow hΛpos.le,
            ← Real.rpow_natCast_mul (inv_nonneg.mpr hΛpos.le), mul_comm,
            Real.rpow_mul_natCast (inv_nonneg.mpr hΛpos.le)]
  calc ∑ m ∈ Finset.range n, ocEpsilon q Λ m ^ c ≤ ∑ m ∈ Finset.range n, r ^ m :=
        Finset.sum_le_sum fun m _ => hterm m
    _ ≤ (1 - r)⁻¹ := by
        exact sum_le_hasSum (Finset.range n) (fun i _ => pow_nonneg hr0 i)
          (hasSum_geometric_of_lt_one hr0 hr1)

/-- The series `∑_{m ≥ 0} ε_m^c` (that is `∑_{m ≥ 1} ε_{m-1}^c`) is summable with sum at most
`(1 - Λ^{-c})⁻¹`. -/
theorem tsum_epsilon_rpow_le {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ) {c : ℝ} (hc : 0 < c) :
    Summable (fun m : ℕ => ocEpsilon q Λ m ^ c) ∧
      ∑' m : ℕ, ocEpsilon q Λ m ^ c ≤ (1 - (Λ : ℝ) ^ (-c))⁻¹ := by
  have hnn : ∀ m : ℕ, 0 ≤ ocEpsilon q Λ m ^ c := fun m =>
    Real.rpow_nonneg (epsilon_basic (m := m) hq hΛ).1.le c
  exact ⟨summable_of_sum_range_le hnn (sum_range_epsilon_rpow_le hq hΛ hc),
    Real.tsum_le_of_sum_range_le hnn (sum_range_epsilon_rpow_le hq hΛ hc)⟩

/-! ### The time scales -/

/-- Abstract form of the ratio bounds: `h ≍ c P` and `L ≍ u⁻¹` give `h/L ≍ P u`, `h/L² ≍ P u²`. -/
theorem div_two_sided_aux {h L P u c₁ c₂ : ℝ} (hP : 0 < P) (hu : 0 < u) (hc₁ : 0 ≤ c₁)
    (hc₂ : 0 ≤ c₂) (hh₁ : c₁ * P ≤ h) (hh₂ : h ≤ c₂ * P)
    (hL₁ : 4 * u⁻¹ ≤ L) (hL₂ : L ≤ 9 * u⁻¹) :
    c₁ / 9 * (P * u) ≤ h / L ∧ h / L ≤ c₂ / 4 * (P * u) ∧
      c₁ / 81 * (P * u ^ 2) ≤ h / L ^ 2 ∧ h / L ^ 2 ≤ c₂ / 16 * (P * u ^ 2) := by
  have hui : 0 < u⁻¹ := inv_pos.mpr hu
  have hL : 0 < L := by linarith
  have hL2 : 0 < L ^ 2 := by positivity
  have huu : u * u⁻¹ = 1 := mul_inv_cancel₀ hu.ne'
  have hPu : 0 ≤ P * u := by positivity
  have hsq₁ : (4 * u⁻¹) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by positivity) hL₁ 2
  have hsq₂ : L ^ 2 ≤ (9 * u⁻¹) ^ 2 := pow_le_pow_left₀ hL.le hL₂ 2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hL]
    calc c₁ / 9 * (P * u) * L ≤ c₁ / 9 * (P * u) * (9 * u⁻¹) :=
          mul_le_mul_of_nonneg_left hL₂ (by positivity)
      _ = c₁ * P * (u * u⁻¹) := by ring
      _ ≤ h := by rw [huu]; linarith
  · rw [div_le_iff₀ hL]
    calc h ≤ c₂ * P := hh₂
      _ = c₂ / 4 * (P * u) * (4 * u⁻¹) := by
          have : c₂ / 4 * (P * u) * (4 * u⁻¹) = c₂ * P * (u * u⁻¹) := by ring
          rw [this, huu]; ring
      _ ≤ c₂ / 4 * (P * u) * L := mul_le_mul_of_nonneg_left hL₁ (by positivity)
  · rw [le_div_iff₀ hL2]
    calc c₁ / 81 * (P * u ^ 2) * L ^ 2 ≤ c₁ / 81 * (P * u ^ 2) * (9 * u⁻¹) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq₂ (by positivity)
      _ = c₁ * P * (u * u⁻¹) ^ 2 := by ring
      _ ≤ h := by rw [huu]; linarith
  · rw [div_le_iff₀ hL2]
    calc h ≤ c₂ * P := hh₂
      _ = c₂ / 16 * (P * u ^ 2) * (4 * u⁻¹) ^ 2 := by
          have : c₂ / 16 * (P * u ^ 2) * (4 * u⁻¹) ^ 2 = c₂ * P * (u * u⁻¹) ^ 2 := by ring
          rw [this, huu]; ring
      _ ≤ c₂ / 16 * (P * u ^ 2) * L ^ 2 := mul_le_mul_of_nonneg_left hsq₁ (by positivity)

/-- Upper half of the `h_m` bound: `τ''_m ≤ 2^{-25} ε_{m-1}^{2-β+2δ}`. -/
theorem ocTauPP_le_two_pow {α q : ℝ} {Λ m : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ) :
    ocTauPP α q Λ m ≤
      (2 : ℝ) ^ (-25 : ℤ) * ocEpsilon q Λ (m - 1) ^ (2 - (1 + α) + 2 * ocDelta α q) := by
  have hE := (epsilon_basic (m := m - 1) hq hΛ).1
  set a : ℝ := 2 - (1 + α) + 2 * ocDelta α q with ha
  have hx : 0 < ocEpsilon q Λ (m - 1) ^ (-a) := Real.rpow_pos_of_pos hE _
  have hceil := Nat.le_ceil (ocEpsilon q Λ (m - 1) ^ (-a))
  unfold ocTauPP
  rw [← ha, div_le_iff₀ (lt_of_lt_of_le hx hceil)]
  have hmul : ocEpsilon q Λ (m - 1) ^ a * ocEpsilon q Λ (m - 1) ^ (-a) = 1 := by
    rw [← Real.rpow_add hE]; simp
  calc (2 : ℝ) ^ (-25 : ℤ)
      = (2 : ℝ) ^ (-25 : ℤ) * (ocEpsilon q Λ (m - 1) ^ a * ocEpsilon q Λ (m - 1) ^ (-a)) := by
        rw [hmul, mul_one]
    _ = (2 : ℝ) ^ (-25 : ℤ) * ocEpsilon q Λ (m - 1) ^ a * ocEpsilon q Λ (m - 1) ^ (-a) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hceil (by positivity)

/-- Two-sided bounds `τ'_m ≍ ε_{m-1}^{2-β+3δ}` and `τ_m ≍ ε_{m-1}^{2-β+4δ}` for all `m ≥ 1`,
`Λ ≥ 128`, with the explicit constants of `admissible_time_scale_facts` (`2^{-26}/9`, `2^{-27}`,
`2^{-26}/81`, `2^{-25}/16`). -/
theorem time_scales_two_sided {α s q : ℝ} {Λ m : ℕ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (hΛ : 128 ≤ Λ) (hm : 1 ≤ m) :
    (2 : ℝ) ^ (-26 : ℤ) / 9 * ocEpsilon q Λ (m - 1) ^ (2 - (1 + α) + 3 * ocDelta α q) ≤
        ocTauP α q Λ m ∧
      ocTauP α q Λ m ≤
        (2 : ℝ) ^ (-25 : ℤ) / 4 * ocEpsilon q Λ (m - 1) ^ (2 - (1 + α) + 3 * ocDelta α q) ∧
    (2 : ℝ) ^ (-26 : ℤ) / 81 * ocEpsilon q Λ (m - 1) ^ (2 - (1 + α) + 4 * ocDelta α q) ≤
        ocTau α q Λ m ∧
      ocTau α q Λ m ≤
        (2 : ℝ) ^ (-25 : ℤ) / 16 * ocEpsilon q Λ (m - 1) ^ (2 - (1 + α) + 4 * ocDelta α q) := by
  obtain ⟨-, hL₁, hL₂, hh₁, -⟩ := admissible_time_scale_facts hα₀ hα₁ hs₀ hs₁ hq hΛ hm
  have hh₂ := ocTauPP_le_two_pow (α := α) (m := m) hq.1 hΛ
  have hE := (epsilon_basic (m := m - 1) hq.1 hΛ).1
  set a : ℝ := 2 - (1 + α) + 2 * ocDelta α q with ha
  set E := ocEpsilon q Λ (m - 1) with hEdef
  set δ := ocDelta α q with hδ
  have hu : 0 < E ^ δ := Real.rpow_pos_of_pos hE δ
  have hP : 0 < E ^ a := Real.rpow_pos_of_pos hE a
  rw [Real.rpow_neg hE.le] at hL₁ hL₂
  obtain ⟨b1, b2, b3, b4⟩ := div_two_sided_aux hP hu (by positivity) (by positivity) hh₁ hh₂ hL₁ hL₂
  have e3 : E ^ (2 - (1 + α) + 3 * δ) = E ^ a * E ^ δ := by
    rw [← Real.rpow_add hE]; congr 1; rw [ha]; ring
  have e4 : E ^ (2 - (1 + α) + 4 * δ) = E ^ a * (E ^ δ) ^ 2 := by
    rw [sq, ← mul_assoc, ← Real.rpow_add hE, ← Real.rpow_add hE]; congr 1; rw [ha]; ring
  rw [e3, e4]
  exact ⟨b1, b2, b3, b4⟩

/-! ### The terminal level -/

/-- `κ τ'_M ≍ ε_{M-1}^{2+γ+3δ}` and `ε_{M-1}² / (κ τ'_M) ≍ ε_{M-1}^{-(γ+3δ)}` for `κ` in the band of
level `M ≥ 2` and `Λ` large (the hypotheses of `terminal_comparisons`). -/
theorem terminal_diffusivity_time_asymp {α s q : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ M : ℕ, 2 ≤ M →
      ∀ ν : ℝ, ν ∈ ocBand α q Λ M →
        ocAsymp C (ν * ocTauP α q Λ M)
            (ocEpsilon q Λ (M - 1) ^ (2 + ocGamma α q + 3 * ocDelta α q)) ∧
          ocAsymp C (ocEpsilon q Λ (M - 1) ^ 2 / (ν * ocTauP α q Λ M))
            (ocEpsilon q Λ (M - 1) ^ (-(ocGamma α q + 3 * ocDelta α q))) := by
  obtain ⟨K, hK, Λ₀, hΛ₀, h⟩ := AVRegularity.EntryScales.terminal_comparisons hα₀ hα₁ hs₀ hs₁ hq
  have hK0 : 0 < K := by linarith
  refine ⟨K * 603979776, by nlinarith, Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ M hM ν hν
  have h128 : 128 ≤ Λ := hΛ₀.trans hΛ
  obtain ⟨⟨hν₁, hν₂⟩, -⟩ := h Λ hΛ M hM ν hν
  obtain ⟨t₁, t₂, -, -⟩ := time_scales_two_sided hα₀ hα₁ hs₀ hs₁ hq h128 (by omega : 1 ≤ M)
  have hc1 : (2 : ℝ) ^ (-26 : ℤ) = 1 / 67108864 := by norm_num
  have hc2 : (2 : ℝ) ^ (-25 : ℤ) = 1 / 33554432 := by norm_num
  rw [hc1] at t₁
  rw [hc2] at t₂
  have hE := (epsilon_basic (m := M - 1) hq.1 h128).1
  set E := ocEpsilon q Λ (M - 1) with hEdef
  set γ := ocGamma α q
  set δ := ocDelta α q
  set A := E ^ ((1 + α) + γ) with hA
  set B := E ^ (2 - (1 + α) + 3 * δ) with hB
  have hApos : 0 < A := Real.rpow_pos_of_pos hE _
  have hBpos : 0 < B := Real.rpow_pos_of_pos hE _
  have hKA : 0 < K⁻¹ * A := by positivity
  have hy : E ^ (2 + γ + 3 * δ) = A * B := by
    rw [hA, hB, ← Real.rpow_add hE]; congr 1; ring
  have hypos : 0 < A * B := by positivity
  have hC : (K * 603979776)⁻¹ * (A * B) ≤ ν * ocTauP α q Λ M := by
    have h1 : K⁻¹ * A * (1 / 67108864 / 9 * B) ≤ ν * ocTauP α q Λ M :=
      mul_le_mul hν₁ t₁ (by positivity) (by linarith)
    have h2 : (K * 603979776)⁻¹ * (A * B) = K⁻¹ * A * (1 / 67108864 / 9 * B) := by
      field_simp; norm_num
    linarith
  have hC' : ν * ocTauP α q Λ M ≤ K * 603979776 * (A * B) := by
    have h1 : ν * ocTauP α q Λ M ≤ K * A * (1 / 33554432 / 4 * B) :=
      mul_le_mul hν₂ t₂ (le_trans (by positivity) t₁) (by positivity)
    have h2 : K * A * (1 / 33554432 / 4 * B) ≤ K * 603979776 * (A * B) := by
      have : K * 603979776 * (A * B) - K * A * (1 / 33554432 / 4 * B) =
          K * (A * B) * (603979776 - 1 / 33554432 / 4) := by ring
      have h3 : 0 ≤ K * (A * B) * (603979776 - 1 / 33554432 / 4) := by
        apply mul_nonneg (by positivity); norm_num
      linarith
    linarith
  rw [hy]
  refine ⟨⟨hC, hC'⟩, ?_⟩
  have hCpos : 0 < K * 603979776 := by positivity
  have hxpos : 0 < ν * ocTauP α q Λ M := lt_of_lt_of_le (by positivity) hC
  have hsplit : E ^ (2 + γ + 3 * δ) = E ^ 2 * E ^ (γ + 3 * δ) := by
    rw [show 2 + γ + 3 * δ = 2 + (γ + 3 * δ) by ring, Real.rpow_add hE, Real.rpow_two]
  have hz : E ^ (-(γ + 3 * δ)) = E ^ 2 / (A * B) := by
    rw [← hy, hsplit, Real.rpow_neg hE.le]
    have : 0 < E ^ (γ + 3 * δ) := Real.rpow_pos_of_pos hE _
    field_simp
  rw [hz]
  have hE2 : 0 ≤ E ^ 2 := by positivity
  constructor
  · calc (K * 603979776)⁻¹ * (E ^ 2 / (A * B)) = E ^ 2 / (K * 603979776 * (A * B)) := by
          field_simp
      _ ≤ E ^ 2 / (ν * ocTauP α q Λ M) :=
          div_le_div_of_nonneg_left hE2 hxpos hC'
  · calc E ^ 2 / (ν * ocTauP α q Λ M) ≤ E ^ 2 / ((K * 603979776)⁻¹ * (A * B)) :=
          div_le_div_of_nonneg_left hE2 (by positivity) hC
      _ = K * 603979776 * (E ^ 2 / (A * B)) := by field_simp

/-! ### The display (4.2) of the paper -/

/-- Algebra of the display: for `e, E > 0`, `e^{-s} (e √r) E^{s-1} = (e/E)^{1-s} √r`. -/
theorem display_identity {e E s r : ℝ} (he : 0 < e) (hE : 0 < E) :
    e ^ (-s) * (e * Real.sqrt r) * E ^ (s - 1) = (e / E) ^ (1 - s) * Real.sqrt r := by
  have h1 : e ^ (-s) * e = e ^ (1 - s) := by
    rw [show (1 - s) = -s + 1 by ring, Real.rpow_add he, Real.rpow_one]
  have h2 : E ^ (s - 1) = (E ^ (1 - s))⁻¹ := by
    rw [← Real.rpow_neg hE.le]; congr 1; ring
  rw [Real.div_rpow he.le hE.le, div_eq_mul_inv, ← h2, ← h1]
  ring

/-- The bound in the display: `(ε_m/ε_{m-1})^{1-s} ≤ 2 ε_{m-1}^{(q-1)(1-s)}` for `s ≤ 1`,
`m ≥ 2`, from `epsilon_q_step`. -/
theorem epsilon_ratio_rpow_le {q s : ℝ} {Λ m : ℕ} (hq : 1 < q) (hq₁₆ : q < 17 / 16)
    (hΛ : 128 ≤ Λ) (hm : 1 ≤ m) (hs₀ : 0 ≤ s) (hs : s ≤ 1) :
    (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)) ^ (1 - s) ≤
      2 * ocEpsilon q Λ (m - 1) ^ ((q - 1) * (1 - s)) := by
  have hE := (epsilon_basic (m := m - 1) hq hΛ).1
  have hstep := epsilon_q_step hq hq₁₆ hΛ hm
  set E := ocEpsilon q Λ (m - 1)
  have he := (epsilon_basic (m := m) hq hΛ).1
  have hratio : ocEpsilon q Λ m / E ≤ 2 * E ^ (q - 1) := by
    rw [div_le_iff₀ hE, Real.rpow_sub_one hE.ne']
    calc ocEpsilon q Λ m ≤ 2 * E ^ q := hstep
      _ = 2 * (E ^ q / E) * E := by field_simp
  have h1s : 0 ≤ 1 - s := by linarith
  calc (ocEpsilon q Λ m / E) ^ (1 - s) ≤ (2 * E ^ (q - 1)) ^ (1 - s) :=
        Real.rpow_le_rpow (by positivity) hratio h1s
    _ = 2 ^ (1 - s) * (E ^ (q - 1)) ^ (1 - s) :=
        Real.mul_rpow (by norm_num) (Real.rpow_nonneg hE.le _)
    _ ≤ 2 * E ^ ((q - 1) * (1 - s)) := by
        rw [← Real.rpow_mul hE.le]
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hE.le _)
        calc (2 : ℝ) ^ (1 - s) ≤ 2 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 2 := Real.rpow_one 2

/-- The display `ε_m^{-s} ℓ_m ε_{m-1}^{s-1} = (e/E)^{1-s} (κ_{m-1}/κ_m)^{1/2} ≤ C E^{μ_s}` with
`ℓ_m = ε_m (κ_{m-1}/κ_m)^{1/2}` (that is, `ocEll q Λ m κ_m * √κ_{m-1}`), for `2 ≤ m ≤ M` and `κ`
a band chain of level `M`, `Λ` large (the `Λ₀` of `bandChain_uniform_ledger`). -/
theorem display_band_chain {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ M : ℕ, ∀ κ : ℕ → ℝ,
      IsOCBandChain α q Λ ζ M κ → ∀ m : ℕ, 2 ≤ m → m ≤ M →
        ocEpsilon q Λ m ^ (-s) *
            (ocEpsilon q Λ m * Real.sqrt (κ (m - 1) / κ m)) * ocEpsilon q Λ (m - 1) ^ (s - 1) =
          (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)) ^ (1 - s) * Real.sqrt (κ (m - 1) / κ m) ∧
        (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)) ^ (1 - s) * Real.sqrt (κ (m - 1) / κ m) ≤
          C * ocEpsilon q Λ (m - 1) ^ ((q - 1) * (1 - s) - q * ocGamma α q) := by
  obtain ⟨C, hC, Λ₀, hΛ₀, h⟩ := AVRegularity.CycleReference.bandChain_uniform_ledger hα0 hα1 hs0 hs1 hq hζ
  refine ⟨2 * C, by linarith, Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ M κ hκ m hm hmM
  have h128 : 128 ≤ Λ := hΛ₀.trans hΛ
  have hE := (epsilon_basic (m := m - 1) hq.1 h128).1
  have he := (epsilon_basic (m := m) hq.1 h128).1
  refine ⟨display_identity he hE, ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hsq, -⟩ :=
    (h Λ hΛ M (by omega) κ hκ).2 m hm hmM (κ m) (κ (m - 1)) rfl rfl
  have h1 := epsilon_ratio_rpow_le (s := s) hq.1 (by linarith [hq.2.1]) h128 (by omega : 1 ≤ m)
    hs0.le (by linarith)
  have hs' : Real.sqrt (κ (m - 1) / κ m) ≤
      C * ocEpsilon q Λ (m - 1) ^ (-(q * ocGamma α q)) := hsq
  set E := ocEpsilon q Λ (m - 1)
  have hsqrt0 := Real.sqrt_nonneg (κ (m - 1) / κ m)
  have hexp : E ^ ((q - 1) * (1 - s) - q * ocGamma α q) =
      E ^ ((q - 1) * (1 - s)) * E ^ (-(q * ocGamma α q)) := by
    rw [← Real.rpow_add hE]; ring_nf
  rw [hexp]
  calc (ocEpsilon q Λ m / E) ^ (1 - s) * Real.sqrt (κ (m - 1) / κ m)
      ≤ (2 * E ^ ((q - 1) * (1 - s))) * (C * E ^ (-(q * ocGamma α q))) :=
        mul_le_mul h1 hs' hsqrt0 (by positivity)
    _ = 2 * C * (E ^ ((q - 1) * (1 - s)) * E ^ (-(q * ocGamma α q))) := by ring

/-! ### The exponent `χ` of the passage -/

/-- With `χ = min{δ, μ_s}/8`: `χ > 0`, `χ ≤ 5η₀/4`, `χ ≤ μ_s` and `χ ≤ δ - 2σ₀`, `σ₀ = a + σ`,
under `IsCascadeWidths`. -/
theorem passage_exponent_chi_le {α s q lamE a σ : ℝ} {Dstar : ℕ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (hw : IsCascadeWidths α q lamE a σ Dstar) :
    0 < min (ocDelta α q) (ocMuS α q s) / 8 ∧
      min (ocDelta α q) (ocMuS α q s) / 8 ≤ 5 * succEta0 α q s / 4 ∧
      min (ocDelta α q) (ocMuS α q s) / 8 ≤ ocMuS α q s ∧
      min (ocDelta α q) (ocMuS α q s) / 8 ≤ ocDelta α q - 2 * (a + σ) := by
  obtain ⟨-, hδ, hμ, -⟩ := admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq
  have hμ' : 0 < ocMuS α q s := hμ
  obtain ⟨-, haσ, hσ⟩ := hw
  have hσδ : 3 * σ < ocDelta α q / 8 := by
    refine lt_of_lt_of_le hσ ((min_le_right _ _).trans ((min_le_right _ _).trans ?_))
    apply div_le_div_of_nonneg_left hδ.le (by norm_num)
    have : (0 : ℝ) ≤ Dstar := Nat.cast_nonneg Dstar
    linarith
  have hm1 : min (ocDelta α q) (ocMuS α q s) ≤ ocDelta α q := min_le_left _ _
  have hm2 : min (ocDelta α q) (ocMuS α q s) ≤ ocMuS α q s := min_le_right _ _
  have hm0 : 0 < min (ocDelta α q) (ocMuS α q s) := lt_min hδ hμ'
  have hη1 : succEta0 α q s ≤ ocDelta α q / 8 := min_le_left _ _
  refine ⟨by positivity, ?_, by linarith, by linarith⟩
  have hη : min (ocDelta α q) (ocMuS α q s) / 8 ≤ succEta0 α q s := by
    apply le_min <;> linarith
  have : 0 ≤ succEta0 α q s := by
    apply le_min <;> linarith
  linarith

end AVRegularity.PaperFacing
