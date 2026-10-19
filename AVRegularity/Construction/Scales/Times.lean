-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.OcGamma
public import AVRegularity.Statements.Construction.OcA
public import AVRegularity.Statements.Construction.OcTau
public import AVRegularity.Statements.Construction.OcTauP

@[expose] public section

section
namespace AVRegularity.Scales

/-- The exponent called `μ_s` in the construction. -/
noncomputable def ocMu (α s q : ℝ) : ℝ := (q - 1) * (1 - s) - q * ocGamma α q

/-- The exponent called `c` in the construction. -/
noncomputable def ocC (α q : ℝ) : ℝ := ocGamma α q / 2 + ocDelta α q

/-- The scale gap used in the time estimates, written with `β=1+α`. -/
noncomputable def scaleGap (α q : ℝ) : ℝ := q - (2 - (1 + α) + 4 * ocDelta α q)

theorem admissible_exponent_facts
    {α s q : ℝ} (hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) :
    0 < ocGamma α q ∧ 0 < ocDelta α q ∧ 0 < ocMu α s q ∧
      scaleGap α q = α + (q + 1 / 2) * ocGamma α q ∧
      0 < scaleGap α q ∧ 0 < ocC α q := by
  rcases hq with ⟨hq₀, hq₁, hq₂, hq₃⟩
  have hqpos : 0 < q := lt_trans zero_lt_one hq₀
  have hden : 0 < q + 1 := by linarith
  have hβ : 0 < 1 + α := by linarith
  have hαden : 0 < 2 * α := by positivity
  have hq₂' : q < (1 - α) / (2 * α) := by
    calc
      q < (2 - (1 + α)) / (2 * ((1 + α) - 1)) := hq₂
      _ = (1 - α) / (2 * α) := by
        rw [show 2 - (1 + α) = 1 - α by ring,
          show (1 + α) - 1 = α by ring]
  have hq₃' : q < (1 - s) / (α + s) := by
    calc
      q < (1 - s) / ((1 + α) - 1 + s) := hq₃
      _ = (1 - s) / (α + s) := by
        rw [show (1 + α) - 1 = α by ring]
  have hdeltaFactor :
      0 < 1 - (2 * q + 1) * (1 + α) / (2 * q + 2) := by
    have hqineq := (lt_div_iff₀ hαden).1 hq₂'
    have hqineq' : 2 * α * q < 1 - α := by nlinarith [hqineq]
    have hnum : 0 < 1 - α * (2 * q + 1) := by nlinarith
    have hden' : 0 < 2 * q + 2 := by linarith
    rw [sub_pos, div_lt_one hden']
    nlinarith [hnum]
  have hgamma : 0 < ocGamma α q := by
    unfold ocGamma
    exact div_pos (mul_pos (by linarith : 0 < q - 1) hβ) hden
  have hdelta : 0 < ocDelta α q := by
    unfold ocDelta
    exact mul_pos (div_pos (by linarith : 0 < q - 1) (by norm_num)) hdeltaFactor
  have hmu : 0 < ocMu α s q := by
    unfold ocMu ocGamma
    have hsden : 0 < α + s := by positivity
    have hqineq := (lt_div_iff₀ hsden).1 hq₃'
    have hqineq' : q * (α + s) < 1 - s := by nlinarith [hqineq]
    have hnum : 0 < 1 - s - q * (α + s) := by linarith
    have hden' : 0 < q + 1 := by linarith
    have hid :
        (q - 1) * (1 - s) - q * ((q - 1) * (1 + α) / (q + 1)) =
          (q - 1) / (q + 1) * (1 - s - q * (α + s)) := by
      field_simp [ne_of_gt hden]
      ring
    rw [hid]
    exact mul_pos (div_pos (by linarith) hden') hnum
  have hid : scaleGap α q = α + (q + 1 / 2) * ocGamma α q := by
    unfold scaleGap ocDelta ocGamma
    field_simp [ne_of_gt hden]
    ring
  have hgap : 0 < scaleGap α q := by
    rw [hid]
    positivity
  have hc : 0 < ocC α q := by
    unfold ocC
    positivity
  exact ⟨hgamma, hdelta, hmu, hid, hgap, hc⟩

theorem admissible_delta_mu_positive
    {α s q : ℝ} (hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) :
    0 < ocDelta α q ∧ 0 < ocMu α s q := by
  rcases admissible_exponent_facts hα₀ _hα₁ hs₀ _hs₁ hq with
    ⟨_, hδ, hμ, _, _, _⟩
  exact ⟨hδ, hμ⟩

private noncomputable def rawScale (q Λ : ℝ) (j : ℕ) : ℝ :=
  Λ ^ (q ^ j / (q - 1))

private theorem rawScale_pos {q Λ : ℝ} (_hq : 1 < q) (hΛ : 0 < Λ) (j : ℕ) :
    0 < rawScale q Λ j := by
  unfold rawScale
  exact Real.rpow_pos_of_pos hΛ _

private theorem rawScale_succ {q Λ : ℝ} (_hq : 1 < q) (hΛ : 0 < Λ) (j : ℕ) :
    rawScale q Λ (j + 1) = rawScale q Λ j ^ q := by
  unfold rawScale
  rw [pow_succ, ← Real.rpow_mul (le_of_lt hΛ)]
  ring_nf

private theorem rawScale_rpow_gap {q Λ : ℝ} (hq : 1 < q) (hΛ : 0 < Λ) (j : ℕ) :
    rawScale q Λ j ^ (q - 1) = Λ ^ (q ^ j) := by
  unfold rawScale
  rw [← Real.rpow_mul (le_of_lt hΛ)]
  congr 1
  field_simp [ne_of_gt (sub_pos.mpr hq)]

private theorem rawScale_large {q Λ : ℝ} (hq : 1 < q) (hq₁₆ : q < 17 / 16)
    (hΛ : 128 ≤ Λ) (j : ℕ) : 128 ≤ rawScale q Λ (j + 1) := by
  have hΛ1 : 1 ≤ Λ := by linarith
  have hpow : 1 ≤ q ^ (j + 1) := one_le_pow₀ hq.le
  have hexp : 1 ≤ q ^ (j + 1) / (q - 1) := by
    have hr : 0 < q - 1 := by linarith
    rw [le_div_iff₀ hr]
    nlinarith [hq₁₆, hpow]
  have hraw : Λ ≤ rawScale q Λ (j + 1) := by
    unfold rawScale
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hΛ1 hexp
  exact hΛ.trans hraw

private theorem log_scale_lower {Λ : ℝ} (hΛ : 128 ≤ Λ) :
    3 ≤ Real.log Λ := by
  have hlog2 : 1 / 2 ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hlog128 : 3 ≤ Real.log 128 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
    calc
      (3 : ℝ) ≤ 7 * (1 / 2) := by norm_num
      _ ≤ 7 * Real.log 2 := mul_le_mul_of_nonneg_left hlog2 (by norm_num)
  exact le_trans hlog128 (Real.log_le_log (by norm_num) hΛ)

private theorem rawScale_ge_log_div {q Λ : ℝ} (hq : 1 < q)
    (hΛ : 128 ≤ Λ) (j : ℕ) :
    Real.log Λ / (q - 1) ≤ rawScale q Λ (j + 1) := by
  have hr : 0 < q - 1 := by linarith
  have hL : 0 < Real.log Λ := by
    exact lt_of_lt_of_le (by norm_num) (log_scale_lower hΛ)
  have hpow : 1 ≤ q ^ (j + 1) := one_le_pow₀ hq.le
  have hpowdiv : (q - 1)⁻¹ ≤ q ^ (j + 1) / (q - 1) := by
    have h : 1 / (q - 1) ≤ q ^ (j + 1) / (q - 1) :=
      (div_le_div_iff₀ hr hr).2 (by nlinarith [hpow])
    simpa only [one_div] using h
  have hexp : Real.log Λ / (q - 1) ≤
      Real.log Λ * (q ^ (j + 1) / (q - 1)) :=
    calc
      Real.log Λ / (q - 1) = Real.log Λ * (q - 1)⁻¹ := by ring
      _ ≤ Real.log Λ * (q ^ (j + 1) / (q - 1)) :=
        mul_le_mul_of_nonneg_left hpowdiv hL.le
  have hExp := Real.add_one_le_exp (Real.log Λ / (q - 1))
  have hExp0 : Real.log Λ / (q - 1) ≤
      Real.exp (Real.log Λ / (q - 1)) := by linarith
  have hExp' : Real.log Λ / (q - 1) ≤
      Real.exp (Real.log Λ * (q ^ (j + 1) / (q - 1))) := by
    exact le_trans hExp0 (Real.exp_le_exp.mpr hexp)
  rw [rawScale, Real.rpow_def_of_pos (by linarith : 0 < Λ)]
  exact hExp'

private theorem rawScale_gap {q Λ : ℝ}
    (hq : 1 < q) (hΛ : 128 ≤ Λ) (j : ℕ) (hj : 1 ≤ j) :
    Λ ≤ rawScale q Λ (j + 1) - Λ * rawScale q Λ j := by
  have hΛpos : 0 < Λ := by linarith
  have hr : 0 < q - 1 := by linarith
  have hL : 3 ≤ Real.log Λ := log_scale_lower hΛ
  have hLpos : 0 < Real.log Λ := by linarith
  have hqpow : q ≤ q ^ j := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    have hn : 1 ≤ q ^ n := one_le_pow₀ hq.le
    have hqnonneg : 0 ≤ q := by linarith
    calc
      q = 1 * q := by ring
      _ ≤ q ^ n * q := mul_le_mul_of_nonneg_right hn hqnonneg
      _ = q ^ (n + 1) := (pow_succ q n).symm
  have hraw : Real.log Λ / (q - 1) ≤ rawScale q Λ j := by
    have h := rawScale_ge_log_div hq hΛ (j - 1)
    have hj' : j - 1 + 1 = j := by omega
    simpa [hj'] using h
  have hexp_eq : Λ ^ (q ^ j - 1) = Real.exp (Real.log Λ * (q ^ j - 1)) := by
    rw [Real.rpow_def_of_pos hΛpos]
  have hexp_lower : 1 + Real.log Λ * (q ^ j - 1) ≤ Λ ^ (q ^ j - 1) := by
    rw [hexp_eq]
    nlinarith [Real.add_one_le_exp (Real.log Λ * (q ^ j - 1))]
  have hpower_gap : Λ * Real.log Λ * (q - 1) ≤ Λ ^ (q ^ j) - Λ := by
    have hqexp : Λ ^ (q ^ j) = Λ * Λ ^ (q ^ j - 1) := by
      rw [show q ^ j = (q ^ j - 1) + 1 by ring, Real.rpow_add hΛpos,
        Real.rpow_one]
      ring_nf
    rw [hqexp]
    have hqdiff : q - 1 ≤ q ^ j - 1 := by linarith
    have hscaled : Real.log Λ * (q - 1) ≤ Real.log Λ * (q ^ j - 1) :=
      mul_le_mul_of_nonneg_left hqdiff hLpos.le
    nlinarith [mul_le_mul_of_nonneg_left hexp_lower hΛpos.le]
  have hbase_gap : Λ * Real.log Λ * (q - 1) ≤
      rawScale q Λ j ^ (q - 1) - Λ := by
    rw [rawScale_rpow_gap hq hΛpos]
    exact hpower_gap
  have hproduct : Λ * Real.log Λ ^ 2 ≤
      rawScale q Λ j * (rawScale q Λ j ^ (q - 1) - Λ) := by
    have hrawpos : 0 ≤ rawScale q Λ j := (rawScale_pos hq hΛpos j).le
    calc
      Λ * Real.log Λ ^ 2 =
          (Real.log Λ / (q - 1)) * (Λ * Real.log Λ * (q - 1)) := by
            field_simp [ne_of_gt hr]
      _ ≤ rawScale q Λ j * (rawScale q Λ j ^ (q - 1) - Λ) :=
        mul_le_mul hraw hbase_gap (by positivity) hrawpos
  have hpow_identity : rawScale q Λ (j + 1) =
      rawScale q Λ j * rawScale q Λ j ^ (q - 1) := by
    calc
      rawScale q Λ (j + 1) = rawScale q Λ j ^ q := rawScale_succ hq hΛpos j
      _ = rawScale q Λ j ^ ((q - 1) + 1) := by congr 1; ring
      _ = rawScale q Λ j ^ (q - 1) * rawScale q Λ j ^ 1 :=
        Real.rpow_add (rawScale_pos hq hΛpos j) _ _
      _ = rawScale q Λ j * rawScale q Λ j ^ (q - 1) := by
        rw [Real.rpow_one]
        ring
  rw [hpow_identity]
  have hlogsq : 1 ≤ Real.log Λ ^ 2 := by nlinarith
  nlinarith [hproduct]

private theorem ceil_raw_pos {q Λ : ℝ} (hq : 1 < q) (hΛ : 0 < Λ)
    (j : ℕ) : 0 < ⌈rawScale q Λ j⌉₊ := by
  rw [Nat.ceil_pos]
  exact rawScale_pos hq hΛ j

private theorem epsilon_eq_inv_ceil {q : ℝ} {Λ m : ℕ} (hm : 0 < m) :
    ocEpsilon q Λ m = (⌈(Λ : ℝ) ^ (q ^ m / (q - 1))⌉₊ : ℝ)⁻¹ := by
  simp [ocEpsilon, Nat.ne_of_gt hm]

/-- Every wavelength is positive, at most one, and has integral reciprocal. -/
theorem epsilon_basic {q : ℝ} {Λ m : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ) :
    0 < ocEpsilon q Λ m ∧ ocEpsilon q Λ m ≤ 1 ∧
      ∃ n : ℕ, (ocEpsilon q Λ m)⁻¹ = (n : ℝ) := by
  by_cases hm : m = 0
  · subst m
    refine ⟨by simp [ocEpsilon], by simp [ocEpsilon], ⟨1, by simp [ocEpsilon]⟩⟩
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hΛr : (0 : ℝ) < Λ := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num) hΛ)
    let n : ℕ := ⌈(Λ : ℝ) ^ (q ^ m / (q - 1))⌉₊
    have hn : 0 < n := by
      dsimp [n]
      exact ceil_raw_pos hq hΛr m
    have heps : ocEpsilon q Λ m = (n : ℝ)⁻¹ := by
      simp [ocEpsilon, hm, n]
    have hncast : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hncastpos : 0 < (n : ℝ) := by exact_mod_cast hn
    refine ⟨?_, ?_, ⟨n, ?_⟩⟩
    · rw [heps]
      exact inv_pos.mpr hncastpos
    · rw [heps]
      exact (inv_le_one₀ hncastpos).2 hncast
    · rw [heps]
      simp

private theorem rawScale_first_ge {q Λ : ℝ} (hq : 1 < q) (hΛ : 1 ≤ Λ) :
    Λ ≤ rawScale q Λ 1 := by
  have hr : 0 < q - 1 := by linarith
  have hexp : 1 ≤ q / (q - 1) := by
    rw [le_div_iff₀ hr]
    norm_num
  unfold rawScale
  simpa only [pow_one, Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le hΛ hexp

/-- Rounded scales separate by at least the fixed integer factor `Λ`. -/
theorem epsilon_ratio_lower {q : ℝ} {Λ m : ℕ}
    (hq : 1 < q) (hΛ : 128 ≤ Λ) (hm : 1 ≤ m) :
    ocEpsilon q Λ (m - 1) / ocEpsilon q Λ m ≥ (Λ : ℝ) := by
  have hΛr : (128 : ℝ) ≤ Λ := by exact_mod_cast hΛ
  have hΛpos : 0 < (Λ : ℝ) := by linarith
  by_cases hm1 : m = 1
  · subst m
    have hraw := rawScale_first_ge hq (by linarith : (1 : ℝ) ≤ Λ)
    have hceil : (Λ : ℝ) ≤
        (⌈(Λ : ℝ) ^ (q / (q - 1))⌉₊ : ℝ) := by
      simpa [rawScale, pow_one] using
        hraw.trans (Nat.le_ceil (rawScale q Λ 1))
    simpa [ocEpsilon] using hceil
  · have hmge : 2 ≤ m := by omega
    let j : ℕ := m - 2
    have hprev : j + 1 = m - 1 := by dsimp [j]; omega
    have hnext : j + 2 = m := by dsimp [j]; omega
    have hgap := rawScale_gap hq hΛr (j + 1) (by omega)
    have hceilprev := Nat.ceil_lt_add_one (rawScale_pos hq hΛpos (j + 1)).le
    have hceilnext := Nat.le_ceil (rawScale q Λ (j + 2))
    have hnatreal : (Λ : ℝ) * (⌈rawScale q Λ (j + 1)⌉₊ : ℝ) ≤
        (⌈rawScale q Λ (j + 2)⌉₊ : ℝ) := by
      calc
        (Λ : ℝ) * (⌈rawScale q Λ (j + 1)⌉₊ : ℝ) ≤
            (Λ : ℝ) * (rawScale q Λ (j + 1) + 1) :=
          mul_le_mul_of_nonneg_left hceilprev.le hΛpos.le
        _ ≤ rawScale q Λ (j + 2) := by nlinarith [hgap]
        _ ≤ (⌈rawScale q Λ (j + 2)⌉₊ : ℝ) := hceilnext
    have hprevpos : 0 < (⌈rawScale q Λ (j + 1)⌉₊ : ℝ) := by
      exact_mod_cast (Nat.ceil_pos.mpr (rawScale_pos hq hΛpos (j + 1)))
    have hnextpos : 0 < (⌈rawScale q Λ (j + 2)⌉₊ : ℝ) := by
      exact_mod_cast (Nat.ceil_pos.mpr (rawScale_pos hq hΛpos (j + 2)))
    rw [← hprev, ← hnext]
    rw [epsilon_eq_inv_ceil (by omega), epsilon_eq_inv_ceil (by omega)]
    rw [ge_iff_le]
    field_simp [ne_of_gt hprevpos, ne_of_gt hnextpos]
    exact hnatreal

private theorem ceil_rpow_le_two {q x : ℝ}
    (hq₀ : 1 < q) (hq₁₆ : q < 17 / 16) (hx : 128 ≤ x) :
    (⌈x⌉₊ : ℝ) ^ q ≤ 2 * x ^ q := by
  have hxpos : 0 < x := by linarith
  have hceil := Nat.ceil_lt_add_one hxpos.le
  have hceil' : (⌈x⌉₊ : ℝ) ≤ (129 / 128 : ℝ) * x := by
    nlinarith [hceil, hx]
  have hqnonneg : 0 ≤ q := by linarith
  have hpowbase := Real.rpow_le_rpow (by positivity) hceil' hqnonneg
  have hqle2 : q ≤ 2 := by linarith
  have hconst : (129 / 128 : ℝ) ^ q ≤ (129 / 128 : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (x := (129 / 128 : ℝ))
      (by norm_num [div_eq_mul_inv]) hqle2
  have hconst2 : (129 / 128 : ℝ) ^ (2 : ℝ) ≤ 2 := by norm_num
  have hxpow : 0 ≤ x ^ q := Real.rpow_nonneg hxpos.le q
  calc
    (⌈x⌉₊ : ℝ) ^ q ≤ ((129 / 128 : ℝ) * x) ^ q := hpowbase
    _ = (129 / 128 : ℝ) ^ q * x ^ q := Real.mul_rpow (by norm_num) hxpos.le
    _ ≤ 2 * x ^ q := by
      exact mul_le_mul_of_nonneg_right (hconst.trans hconst2) hxpow

/-- Rounded wavelengths obey the one-step `q` power bound `ε_m ≤ 2 ε_{m-1}^q` (Lemma 6.1(a) of the
paper). -/
theorem epsilon_q_step {q : ℝ} {Λ m : ℕ}
    (hq : 1 < q) (hq₁₆ : q < 17 / 16)
    (hΛ : 128 ≤ Λ) (hm : 1 ≤ m) :
    ocEpsilon q Λ m ≤ 2 * ocEpsilon q Λ (m - 1) ^ q := by
  have hΛr : (128 : ℝ) ≤ Λ := by exact_mod_cast hΛ
  have hΛpos : 0 < (Λ : ℝ) := by linarith
  by_cases hm1 : m = 1
  · subst m
    have hε : ocEpsilon q Λ 1 ≤ 1 := (epsilon_basic (m := 1) hq hΛ).2.1
    simpa [ocEpsilon] using le_trans hε (by norm_num : (1 : ℝ) ≤ 2)
  · have hmge : 2 ≤ m := by omega
    let j : ℕ := m - 2
    have hprev : j + 1 = m - 1 := by dsimp [j]; omega
    have hnext : j + 2 = m := by dsimp [j]; omega
    have hxlarge := rawScale_large hq hq₁₆ hΛr j
    have hxpos := rawScale_pos hq hΛpos (j + 1)
    have hrawsucc := rawScale_succ hq hΛpos (j + 1)
    have hceilpow := ceil_rpow_le_two hq hq₁₆ hxlarge
    have hprevpos : 0 < (⌈rawScale q Λ (j + 1)⌉₊ : ℝ) := by
      exact_mod_cast (Nat.ceil_pos.mpr hxpos)
    have hnextpos : 0 < (⌈rawScale q Λ (j + 2)⌉₊ : ℝ) := by
      exact_mod_cast (Nat.ceil_pos.mpr (rawScale_pos hq hΛpos (j + 2)))
    have hxpowpos : 0 < rawScale q Λ (j + 1) ^ q :=
      Real.rpow_pos_of_pos hxpos q
    have hnprevpowpos : 0 < (⌈rawScale q Λ (j + 1)⌉₊ : ℝ) ^ q :=
      Real.rpow_pos_of_pos hprevpos q
    have hceilnext : rawScale q Λ (j + 1) ^ q ≤
        (⌈rawScale q Λ (j + 2)⌉₊ : ℝ) := by
      rw [← hrawsucc]
      exact Nat.le_ceil _
    have hinvnext : (⌈rawScale q Λ (j + 2)⌉₊ : ℝ)⁻¹ ≤
        (rawScale q Λ (j + 1) ^ q)⁻¹ :=
      (inv_le_inv₀ hnextpos hxpowpos).2 hceilnext
    have hinvprev : (rawScale q Λ (j + 1) ^ q)⁻¹ ≤
        2 * ((⌈rawScale q Λ (j + 1)⌉₊ : ℝ)⁻¹) ^ q := by
      rw [Real.inv_rpow hprevpos.le]
      have hratio :
          (rawScale q Λ (j + 1) ^ q)⁻¹ ≤
            2 / ((⌈rawScale q Λ (j + 1)⌉₊ : ℝ) ^ q) := by
        have hratio' : (1 : ℝ) / (rawScale q Λ (j + 1) ^ q) ≤
            2 / ((⌈rawScale q Λ (j + 1)⌉₊ : ℝ) ^ q) := by
          rw [div_le_div_iff₀ hxpowpos hnprevpowpos]
          simpa using hceilpow
        simpa [div_eq_mul_inv] using hratio'
      simpa [div_eq_mul_inv] using hratio
    rw [← hprev, ← hnext]
    rw [epsilon_eq_inv_ceil (by omega), epsilon_eq_inv_ceil (by omega)]
    exact hinvnext.trans hinvprev

private noncomputable def geometricRatio (Λ : ℕ) (p : ℝ) : ℝ :=
  (Λ : ℝ) ^ (-p)

private theorem geometricRatio_bounds {Λ : ℕ} {p : ℝ}
    (hΛ : 128 ≤ Λ) (hp : 0 < p) :
    0 < geometricRatio Λ p ∧ geometricRatio Λ p < 1 := by
  have hΛone : 1 < (Λ : ℝ) := by exact_mod_cast (by omega : 1 < Λ)
  have hpow : 1 < (Λ : ℝ) ^ p := Real.one_lt_rpow hΛone hp
  have hpowpos : 0 < (Λ : ℝ) ^ p := Real.rpow_pos_of_pos (by positivity) p
  constructor
  · unfold geometricRatio
    rw [Real.rpow_neg (by positivity)]
    exact inv_pos.mpr hpowpos
  · unfold geometricRatio
    rw [Real.rpow_neg (by positivity)]
    exact (inv_lt_one₀ hpowpos).2 hpow

private theorem epsilon_forward_rpow_decay {q : ℝ} {Λ m : ℕ} {p : ℝ}
    (hq : 1 < q) (hΛ : 128 ≤ Λ) (hm : 1 ≤ m) (hp : 0 < p) (k : ℕ) :
    ocEpsilon q Λ (m + k) ^ p ≤
      ocEpsilon q Λ m ^ p * geometricRatio Λ p ^ k := by
  have hΛpos : 0 < (Λ : ℝ) := by exact_mod_cast (by omega : 0 < Λ)
  have hratio : 0 < geometricRatio Λ p := (geometricRatio_bounds hΛ hp).1
  induction k with
  | zero => simp [geometricRatio]
  | succ k ih =>
      have hprevpos : 0 < ocEpsilon q Λ (m + k) :=
        (epsilon_basic (m := m + k) hq hΛ).1
      have hnextpos : 0 < ocEpsilon q Λ (m + (k + 1)) :=
        (epsilon_basic (m := m + (k + 1)) hq hΛ).1
      have hsep := epsilon_ratio_lower hq hΛ (by omega : 1 ≤ m + k + 1)
      have hsep' : (Λ : ℝ) ≤
          ocEpsilon q Λ (m + k) / ocEpsilon q Λ (m + (k + 1)) := by
        simpa [Nat.add_assoc, show m + k + 1 - 1 = m + k by omega] using hsep
      have hmul : (Λ : ℝ) * ocEpsilon q Λ (m + (k + 1)) ≤
          ocEpsilon q Λ (m + k) := (le_div_iff₀ hnextpos).1 hsep'
      have hstep : ocEpsilon q Λ (m + (k + 1)) ≤
          ocEpsilon q Λ (m + k) / (Λ : ℝ) := by
        rw [le_div_iff₀ hΛpos]
        nlinarith [hmul]
      have hstepP := Real.rpow_le_rpow (by positivity) hstep hp.le
      rw [Real.div_rpow (by positivity) hΛpos.le] at hstepP
      have hstepEq :
          ocEpsilon q Λ (m + k) ^ p / (Λ : ℝ) ^ p =
            ocEpsilon q Λ (m + k) ^ p * geometricRatio Λ p := by
        unfold geometricRatio
        rw [Real.rpow_neg (by positivity)]
        ring
      calc
        ocEpsilon q Λ (m + (k + 1)) ^ p ≤
            ocEpsilon q Λ (m + k) ^ p / (Λ : ℝ) ^ p := hstepP
        _ = ocEpsilon q Λ (m + k) ^ p * geometricRatio Λ p := hstepEq
        _ ≤ (ocEpsilon q Λ m ^ p * geometricRatio Λ p ^ k) *
            geometricRatio Λ p :=
          mul_le_mul_of_nonneg_right ih hratio.le
        _ = ocEpsilon q Λ m ^ p * geometricRatio Λ p ^ (k + 1) := by
          rw [pow_succ]
          ring

/-- The forward wavelength tail is summable and has the stated geometric bound. -/
theorem epsilon_forward_tail {q : ℝ} {Λ m : ℕ} {p : ℝ}
    (hq : 1 < q) (hΛ : 128 ≤ Λ) (hm : 1 ≤ m) (hp : 0 < p) :
    Summable (fun k : ℕ => ocEpsilon q Λ (m + k) ^ p) ∧
      ∑' k : ℕ, ocEpsilon q Λ (m + k) ^ p ≤
        ocEpsilon q Λ m ^ p / (1 - (Λ : ℝ) ^ (-p)) := by
  let r := geometricRatio Λ p
  have hr := geometricRatio_bounds hΛ hp
  have hrnorm : ‖r‖ < 1 := by
    simpa [r, Real.norm_eq_abs, abs_of_nonneg hr.1.le] using hr.2
  have hgeom : Summable (fun k : ℕ => r ^ k) :=
    summable_geometric_of_norm_lt_one hrnorm
  have hmajor : Summable (fun k : ℕ => ocEpsilon q Λ m ^ p * r ^ k) :=
    hgeom.mul_left (ocEpsilon q Λ m ^ p)
  have hpoint : ∀ k : ℕ,
      ocEpsilon q Λ (m + k) ^ p ≤ ocEpsilon q Λ m ^ p * r ^ k := by
    intro k
    exact epsilon_forward_rpow_decay hq hΛ hm hp k
  have hnonneg : ∀ k : ℕ, 0 ≤ ocEpsilon q Λ (m + k) ^ p := by
    intro k
    exact Real.rpow_nonneg (epsilon_basic (m := m + k) hq hΛ).1.le p
  have hsum : Summable (fun k : ℕ => ocEpsilon q Λ (m + k) ^ p) :=
    hmajor.of_nonneg_of_le hnonneg hpoint
  have hle := Summable.tsum_le_tsum hpoint hsum hmajor
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hrnorm] at hle
  refine ⟨hsum, ?_⟩
  simpa [r, geometricRatio, Real.rpow_neg, div_eq_mul_inv] using hle

private theorem epsilon_inverse_rpow_decay {q : ℝ} {Λ j : ℕ} {p : ℝ}
    (hq : 1 < q) (hΛ : 128 ≤ Λ) (hp : 0 < p) (k : ℕ) :
    (ocEpsilon q Λ j) ^ (-p) ≤
      (ocEpsilon q Λ (j + k)) ^ (-p) * geometricRatio Λ p ^ k := by
  have hΛpos : 0 < (Λ : ℝ) := by exact_mod_cast (by omega : 0 < Λ)
  have hratio : 0 < geometricRatio Λ p := (geometricRatio_bounds hΛ hp).1
  have hpnonneg : 0 ≤ p := hp.le
  induction k with
  | zero => simp [geometricRatio]
  | succ k ih =>
      have hprevpos : 0 < ocEpsilon q Λ (j + k) :=
        (epsilon_basic (m := j + k) hq hΛ).1
      have hnextpos : 0 < ocEpsilon q Λ (j + (k + 1)) :=
        (epsilon_basic (m := j + (k + 1)) hq hΛ).1
      have hsep := epsilon_ratio_lower hq hΛ (by omega : 1 ≤ j + k + 1)
      have hsep' : (Λ : ℝ) ≤
          ocEpsilon q Λ (j + k) / ocEpsilon q Λ (j + (k + 1)) := by
        simpa [Nat.add_assoc, show j + k + 1 - 1 = j + k by omega] using hsep
      have hmul : (Λ : ℝ) * ocEpsilon q Λ (j + (k + 1)) ≤
          ocEpsilon q Λ (j + k) := (le_div_iff₀ hnextpos).1 hsep'
      have hinv : (ocEpsilon q Λ (j + k))⁻¹ ≤
          ((Λ : ℝ) * ocEpsilon q Λ (j + (k + 1)))⁻¹ :=
        (inv_le_inv₀ hprevpos (mul_pos hΛpos hnextpos)).2 hmul
      have hpow := Real.rpow_le_rpow (by positivity) hinv hpnonneg
      rw [mul_inv, Real.mul_rpow (by positivity) (by positivity),
        Real.inv_rpow (by positivity), Real.inv_rpow (by positivity)] at hpow
      have hpow' := hpow
      rw [Real.inv_rpow hnextpos.le] at hpow'
      have hstep : (ocEpsilon q Λ (j + k)) ^ (-p) ≤
          (ocEpsilon q Λ (j + (k + 1))) ^ (-p) * geometricRatio Λ p := by
        rw [Real.rpow_neg hprevpos.le, Real.rpow_neg hnextpos.le]
        simpa [geometricRatio, Real.rpow_neg, mul_comm, mul_left_comm] using hpow'
      calc
        (ocEpsilon q Λ j) ^ (-p) ≤
            (ocEpsilon q Λ (j + k)) ^ (-p) * geometricRatio Λ p ^ k := ih
        _ ≤ ((ocEpsilon q Λ (j + (k + 1))) ^ (-p) * geometricRatio Λ p) *
            geometricRatio Λ p ^ k :=
          mul_le_mul_of_nonneg_right hstep (pow_nonneg hratio.le k)
        _ = (ocEpsilon q Λ (j + (k + 1))) ^ (-p) *
            geometricRatio Λ p ^ (k + 1) := by
          rw [pow_succ]
          ring

/-- The finite inverse-scale sum is bounded by the same geometric tail. -/
theorem epsilon_backward_sum {q : ℝ} {Λ m : ℕ} {p : ℝ}
    (hq : 1 < q) (hΛ : 128 ≤ Λ) (hp : 0 < p) :
    (∑ j ∈ Finset.range (m + 1), (ocEpsilon q Λ j) ^ (-p)) ≤
      (ocEpsilon q Λ m) ^ (-p) / (1 - (Λ : ℝ) ^ (-p)) := by
  let r := geometricRatio Λ p
  have hr := geometricRatio_bounds hΛ hp
  have hrnorm : ‖r‖ < 1 := by
    simpa [r, Real.norm_eq_abs, abs_of_nonneg hr.1.le] using hr.2
  have hgeom : Summable (fun k : ℕ => r ^ k) :=
    summable_geometric_of_norm_lt_one hrnorm
  have hpoint : ∀ k ∈ Finset.range (m + 1),
      (ocEpsilon q Λ (m - k)) ^ (-p) ≤ (ocEpsilon q Λ m) ^ (-p) * r ^ k := by
    intro k hk
    have hk' : k ≤ m := by simp only [Finset.mem_range] at hk; omega
    simpa [r, show m - k + k = m by omega] using
      epsilon_inverse_rpow_decay (j := m - k) hq hΛ hp k
  have hreflect :=
    (Finset.sum_range_reflect (fun j : ℕ => (ocEpsilon q Λ j) ^ (-p)) (m + 1)).symm
  rw [hreflect]
  calc
    (∑ k ∈ Finset.range (m + 1), (ocEpsilon q Λ (m - k)) ^ (-p)) ≤
        ∑ k ∈ Finset.range (m + 1), (ocEpsilon q Λ m) ^ (-p) * r ^ k := by
      exact Finset.sum_le_sum fun k hk => hpoint k hk
    _ ≤ (ocEpsilon q Λ m) ^ (-p) * ∑' k : ℕ, r ^ k := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left
        (hgeom.sum_le_tsum (Finset.range (m + 1))
          (by intro k hk; exact pow_nonneg hr.1.le _))
        (Real.rpow_nonneg (epsilon_basic (m := m) hq hΛ).1.le (-p))
    _ = (ocEpsilon q Λ m) ^ (-p) * (1 - r)⁻¹ := by
      rw [tsum_geometric_of_norm_lt_one hrnorm]

/-- The scale statements with the admissibility hypothesis `IsAdmissibleQ α s q` as input. -/
theorem admissible_space_scale_facts {α s q : ℝ} {Λ m : ℕ}
    (hq : IsAdmissibleQ α s q) (hΛ : 128 ≤ Λ) (hm : 1 ≤ m) :
    (0 < ocEpsilon q Λ m ∧ ocEpsilon q Λ m ≤ 1 ∧
      ∃ n : ℕ, (ocEpsilon q Λ m)⁻¹ = (n : ℝ)) ∧
    ocEpsilon q Λ (m - 1) / ocEpsilon q Λ m ≥ (Λ : ℝ) ∧
    ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1) / 128 ∧
    ocEpsilon q Λ m ≤ 2 * ocEpsilon q Λ (m - 1) ^ q := by
  have hbasic := epsilon_basic (m := m) hq.1 hΛ
  have hratio := epsilon_ratio_lower hq.1 hΛ hm
  have hqstep := epsilon_q_step hq.1 hq.2.1 hΛ hm
  have hcurrentpos : 0 < ocEpsilon q Λ m := hbasic.1
  have hΛr : (128 : ℝ) ≤ Λ := by exact_mod_cast hΛ
  have hratio128 : (128 : ℝ) ≤
      ocEpsilon q Λ (m - 1) / ocEpsilon q Λ m := hΛr.trans hratio
  have hmul : (128 : ℝ) * ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1) :=
    (le_div_iff₀ hcurrentpos).1 hratio128
  have hdiv : ocEpsilon q Λ m ≤ ocEpsilon q Λ (m - 1) / 128 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 128)]
    nlinarith [hmul]
  exact ⟨hbasic, hratio, hdiv, hqstep⟩

/-- The forward tail bound, directly under `IsAdmissibleQ`. -/
theorem admissible_epsilon_forward_tail {α s q : ℝ} {Λ m : ℕ} {p : ℝ}
    (hq : IsAdmissibleQ α s q) (hΛ : 128 ≤ Λ) (hm : 1 ≤ m) (hp : 0 < p) :
    Summable (fun k : ℕ => ocEpsilon q Λ (m + k) ^ p) ∧
      ∑' k : ℕ, ocEpsilon q Λ (m + k) ^ p ≤
        ocEpsilon q Λ m ^ p / (1 - (Λ : ℝ) ^ (-p)) :=
  epsilon_forward_tail hq.1 hΛ hm hp

/-- The finite backward inverse-scale bound, directly under `IsAdmissibleQ`. -/
theorem admissible_epsilon_backward_sum {α s q : ℝ} {Λ m : ℕ} {p : ℝ}
    (hq : IsAdmissibleQ α s q) (hΛ : 128 ≤ Λ) (hp : 0 < p) :
    (∑ j ∈ Finset.range (m + 1), (ocEpsilon q Λ j) ^ (-p)) ≤
      (ocEpsilon q Λ m) ^ (-p) / (1 - (Λ : ℝ) ^ (-p)) :=
  epsilon_backward_sum hq.1 hΛ hp

private theorem one_le_neg_rpow {x p : ℝ} (hxpos : 0 < x) (hxle : x ≤ 1)
    (hp : 0 < p) : 1 ≤ x ^ (-p) := by
  rw [Real.rpow_neg hxpos.le]
  apply (one_le_inv₀ (Real.rpow_pos_of_pos hxpos p)).2
  exact Real.rpow_le_one hxpos.le hxle hp.le

private theorem rpow_cancel {x p : ℝ} (hx : 0 < x) :
    x ^ p * x ^ (-p) = 1 := by
  rw [← Real.rpow_add hx]
  simp

private theorem block_length_bounds {α q : ℝ} {Λ m : ℕ}
    (hδ : 0 < ocDelta α q) (hEpos : 0 < ocEpsilon q Λ (m - 1))
    (hEle : ocEpsilon q Λ (m - 1) ≤ 1) :
    5 ≤ ocL α q Λ m ∧
      4 * ocEpsilon q Λ (m - 1) ^ (-ocDelta α q) ≤ (ocL α q Λ m : ℝ) ∧
      (ocL α q Λ m : ℝ) ≤
        9 * ocEpsilon q Λ (m - 1) ^ (-ocDelta α q) := by
  let E := ocEpsilon q Λ (m - 1)
  let x := E ^ (-ocDelta α q)
  have hxpos : 0 < x := Real.rpow_pos_of_pos hEpos _
  have hxone : 1 ≤ x := one_le_neg_rpow hEpos hEle hδ
  have hceilLower : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have hceilUpper : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hxpos.le
  have hLdef : (ocL α q Λ m : ℝ) = 4 * (⌈x⌉₊ : ℝ) + 1 := by
    simp [ocL, E, x]
  have hLreal : (5 : ℝ) ≤ (ocL α q Λ m : ℝ) := by
    rw [hLdef]
    nlinarith [hxone, hceilLower]
  have hLnat : 5 ≤ ocL α q Λ m := by exact_mod_cast hLreal
  refine ⟨hLnat, ?_, ?_⟩
  · rw [hLdef]
    dsimp [x, E]
    nlinarith [hceilLower]
  · rw [hLdef]
    dsimp [x, E]
    nlinarith [hceilUpper, hxone]

private theorem tauPP_lower_bound {α q : ℝ} {Λ m : ℕ}
    (hκ : 0 < 2 - (1 + α) + 2 * ocDelta α q)
    (hEpos : 0 < ocEpsilon q Λ (m - 1))
    (hEle : ocEpsilon q Λ (m - 1) ≤ 1) :
    (2 : ℝ) ^ (-26 : ℤ) * ocEpsilon q Λ (m - 1) ^
        (2 - (1 + α) + 2 * ocDelta α q) ≤ ocTauPP α q Λ m := by
  let E := ocEpsilon q Λ (m - 1)
  let κ := 2 - (1 + α) + 2 * ocDelta α q
  let y := E ^ (-κ)
  have hypos : 0 < y := Real.rpow_pos_of_pos hEpos _
  have hyone : 1 ≤ y := one_le_neg_rpow hEpos hEle hκ
  have hceilLower : y ≤ (⌈y⌉₊ : ℝ) := Nat.le_ceil y
  have hceilUpper : (⌈y⌉₊ : ℝ) ≤ 2 * y := by
    have h := Nat.ceil_lt_add_one hypos.le
    nlinarith [hyone]
  have hnum : 0 < (2 : ℝ) ^ (-25 : ℤ) := by positivity
  have hden : 0 < (⌈y⌉₊ : ℝ) := lt_of_lt_of_le hypos hceilLower
  have hprod :
      (2 : ℝ) ^ (-26 : ℤ) * E ^ κ * (⌈y⌉₊ : ℝ) ≤ (2 : ℝ) ^ (-25 : ℤ) := by
    calc
      (2 : ℝ) ^ (-26 : ℤ) * E ^ κ * (⌈y⌉₊ : ℝ) ≤
          (2 : ℝ) ^ (-26 : ℤ) * E ^ κ * (2 * y) :=
        mul_le_mul_of_nonneg_left hceilUpper (by positivity)
      _ = (2 : ℝ) ^ (-25 : ℤ) := by
        have hcancel : E ^ κ * y = 1 := by
          dsimp [y]
          exact rpow_cancel hEpos
        calc
          (2 : ℝ) ^ (-26 : ℤ) * E ^ κ * (2 * y) =
              ((2 : ℝ) ^ (-26 : ℤ) * 2) * (E ^ κ * y) := by ring
          _ = (2 : ℝ) ^ (-25 : ℤ) := by rw [hcancel]; norm_num [zpow_neg]
  have htarget :
      (2 : ℝ) ^ (-26 : ℤ) * E ^ κ ≤
        (2 : ℝ) ^ (-25 : ℤ) / (⌈y⌉₊ : ℝ) :=
    (le_div_iff₀ hden).2 hprod
  simpa [ocTauPP, E, κ, y] using htarget

private theorem tauPP_upper_bound {α q : ℝ} {Λ m : ℕ}
    (hEpos : 0 < ocEpsilon q Λ (m - 1)) :
    ocTauPP α q Λ m ≤ (2 : ℝ) ^ (-25 : ℤ) *
      ocEpsilon q Λ (m - 1) ^ (2 - (1 + α) + 2 * ocDelta α q) := by
  let E := ocEpsilon q Λ (m - 1)
  let κ := 2 - (1 + α) + 2 * ocDelta α q
  let y := E ^ (-κ)
  have hypos : 0 < y := Real.rpow_pos_of_pos hEpos _
  have hceilLower : y ≤ (⌈y⌉₊ : ℝ) := Nat.le_ceil y
  have hden : 0 < (⌈y⌉₊ : ℝ) := lt_of_lt_of_le hypos hceilLower
  have hnum : 0 < (2 : ℝ) ^ (-25 : ℤ) := by positivity
  have hdiv : (2 : ℝ) ^ (-25 : ℤ) / (⌈y⌉₊ : ℝ) ≤
      (2 : ℝ) ^ (-25 : ℤ) / y := by
    rw [div_le_div_iff₀ hden hypos]
    exact mul_le_mul_of_nonneg_left hceilLower hnum.le
  have hrecip : y⁻¹ = E ^ κ := by
    dsimp [y]
    rw [Real.rpow_neg hEpos.le, inv_inv]
  change ocTauPP α q Λ m ≤ (2 : ℝ) ^ (-25 : ℤ) * E ^ κ
  calc
    ocTauPP α q Λ m ≤ (2 : ℝ) ^ (-25 : ℤ) / y := by
      simpa [ocTauPP, E, κ, y] using hdiv
    _ = (2 : ℝ) ^ (-25 : ℤ) * E ^ κ := by
      rw [div_eq_mul_inv, hrecip]

private theorem a_tauPP_upper_bound {α q : ℝ} {Λ m : ℕ}
    (hEpos : 0 < ocEpsilon q Λ (m - 1)) :
    ocA α q Λ (m - 1) * ocTauPP α q Λ m ≤
      (2 : ℝ) ^ (-25 : ℤ) * ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q) := by
  let E := ocEpsilon q Λ (m - 1)
  let κ := 2 - (1 + α) + 2 * ocDelta α q
  have hA : ocA α q Λ (m - 1) = E ^ (α - 1) := by
    simp [ocA, E]
    congr 1
    ring
  have hApos : 0 < E ^ (α - 1) := Real.rpow_pos_of_pos hEpos _
  have hτ := tauPP_upper_bound (α := α) hEpos
  rw [hA]
  calc
    E ^ (α - 1) * ocTauPP α q Λ m ≤
        E ^ (α - 1) * ((2 : ℝ) ^ (-25 : ℤ) * E ^ κ) :=
      mul_le_mul_of_nonneg_left hτ hApos.le
    _ = (2 : ℝ) ^ (-25 : ℤ) * E ^ (2 * ocDelta α q) := by
      have hexp : (α - 1) + κ = 2 * ocDelta α q := by dsimp [κ]; ring
      calc
        E ^ (α - 1) * ((2 : ℝ) ^ (-25 : ℤ) * E ^ κ) =
            (2 : ℝ) ^ (-25 : ℤ) * (E ^ (α - 1) * E ^ κ) := by ring
        _ = (2 : ℝ) ^ (-25 : ℤ) * E ^ ((α - 1) + κ) := by
          rw [← Real.rpow_add hEpos (α - 1) κ]
        _ = (2 : ℝ) ^ (-25 : ℤ) * E ^ (2 * ocDelta α q) := by rw [hexp]

private theorem epsilon_over_tau_bound {α s q : ℝ} {Λ m : ℕ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (hΛ : 128 ≤ Λ) (hm : 1 ≤ m) :
    ocEpsilon q Λ m / ocTau α q Λ m ≤ 2 ^ (35 : ℕ) := by
  let E := ocEpsilon q Λ (m - 1)
  let e := ocEpsilon q Λ m
  let δ := ocDelta α q
  let κ := 2 - (1 + α) + 2 * δ
  let g := scaleGap α q
  have hparams := admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq
  have hδ : 0 < δ := by dsimp [δ]; exact hparams.2.1
  have hg : 0 < g := hparams.2.2.2.2.1
  have hκ : 0 < κ := by dsimp [κ]; linarith
  have hspace := admissible_space_scale_facts hq hΛ hm
  have hEpos : 0 < E := (epsilon_basic (m := m - 1) hq.1 hΛ).1
  have hEle : E ≤ 1 := (epsilon_basic (m := m - 1) hq.1 hΛ).2.1
  have hepos : 0 < e := (epsilon_basic (m := m) hq.1 hΛ).1
  have hL := block_length_bounds hδ hEpos hEle
  have hLpos : 0 < (ocL α q Λ m : ℝ) := by
    exact_mod_cast (show 0 < ocL α q Λ m by omega)
  have heupper : e ≤ 2 * E ^ q := by
    simpa [e, E] using hspace.2.2.2
  have hτlower := tauPP_lower_bound hκ hEpos hEle
  have hτpos : 0 < ocTauPP α q Λ m := by
    exact lt_of_lt_of_le (by positivity) hτlower
  have hNum : e * (ocL α q Λ m : ℝ) ^ 2 ≤
      162 * E ^ q * (E ^ (-δ)) ^ 2 := by
    have hLnonneg : 0 ≤ (ocL α q Λ m : ℝ) := by positivity
    have hUnonneg : 0 ≤ 9 * E ^ (-δ) := by positivity
    have hLsq : (ocL α q Λ m : ℝ) ^ 2 ≤ (9 * E ^ (-δ)) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hL.2.2)
        (add_nonneg hLnonneg hUnonneg)]
    calc
      e * (ocL α q Λ m : ℝ) ^ 2 ≤ e * (9 * E ^ (-δ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hLsq hepos.le
      _ ≤ (2 * E ^ q) * (9 * E ^ (-δ)) ^ 2 :=
        mul_le_mul_of_nonneg_right heupper (sq_nonneg (9 * E ^ (-δ)))
      _ = 162 * E ^ q * (E ^ (-δ)) ^ 2 := by ring
  have hDen : (2 : ℝ) ^ (-26 : ℤ) * E ^ κ ≤ ocTauPP α q Λ m := hτlower
  have hDenpos : 0 < (2 : ℝ) ^ (-26 : ℤ) * E ^ κ := by positivity
  have hfrac : (e * (ocL α q Λ m : ℝ) ^ 2) / ocTauPP α q Λ m ≤
      (162 * E ^ q * (E ^ (-δ)) ^ 2) /
        ((2 : ℝ) ^ (-26 : ℤ) * E ^ κ) := by
    rw [div_le_div_iff₀ hτpos hDenpos]
    have hfirst := mul_le_mul_of_nonneg_right hNum hDenpos.le
    have hsecond := mul_le_mul_of_nonneg_left hDen (by positivity :
      0 ≤ 162 * E ^ q * (E ^ (-δ)) ^ 2)
    exact hfirst.trans hsecond
  have hsq : (E ^ (-δ)) ^ (2 : ℕ) = E ^ (-2 * δ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hEpos.le]
    congr 1
    ring
  have hpow : E ^ q * (E ^ (-δ)) ^ 2 / E ^ κ = E ^ g := by
    rw [hsq, ← Real.rpow_add hEpos q (-2 * δ), ← Real.rpow_sub hEpos]
    dsimp [g, scaleGap, κ, δ]
    ring_nf
  have hconst : 162 / (2 : ℝ) ^ (-26 : ℤ) ≤ 2 ^ (35 : ℕ) := by
    norm_num [zpow_neg]
  have hEg : E ^ g ≤ 1 := Real.rpow_le_one hEpos.le hEle hg.le
  have hcoeffpos : 0 ≤ 162 / (2 : ℝ) ^ (-26 : ℤ) := by positivity
  have hpow' : E ^ q * E ^ (-2 * δ) / E ^ κ = E ^ g := by
    simpa [hsq] using hpow
  have hfrac' :
      (162 * E ^ q * (E ^ (-δ)) ^ 2) /
        ((2 : ℝ) ^ (-26 : ℤ) * E ^ κ) =
      (162 / (2 : ℝ) ^ (-26 : ℤ)) * E ^ g := by
    calc
      (162 * E ^ q * (E ^ (-δ)) ^ 2) /
          ((2 : ℝ) ^ (-26 : ℤ) * E ^ κ) =
      (162 / (2 : ℝ) ^ (-26 : ℤ)) *
          (E ^ q * E ^ (-2 * δ) / E ^ κ) := by
            rw [hsq]
            field_simp [ne_of_gt hDenpos,
              ne_of_gt (show 0 < (2 : ℝ) ^ (-26 : ℤ) by positivity)]
      _ = (162 / (2 : ℝ) ^ (-26 : ℤ)) * E ^ g := by rw [hpow']
  have hsmallCoeff : (162 / (2 : ℝ) ^ (-26 : ℤ)) * E ^ g ≤
      162 / (2 : ℝ) ^ (-26 : ℤ) := by
    calc
      (162 / (2 : ℝ) ^ (-26 : ℤ)) * E ^ g ≤
          (162 / (2 : ℝ) ^ (-26 : ℤ)) * 1 :=
        mul_le_mul_of_nonneg_left hEg hcoeffpos
      _ = 162 / (2 : ℝ) ^ (-26 : ℤ) := by ring
  have hfinal : (e * (ocL α q Λ m : ℝ) ^ 2) / ocTauPP α q Λ m ≤ 2 ^ (35 : ℕ) := by
    calc
      (e * (ocL α q Λ m : ℝ) ^ 2) / ocTauPP α q Λ m ≤
          (162 * E ^ q * (E ^ (-δ)) ^ 2) /
            ((2 : ℝ) ^ (-26 : ℤ) * E ^ κ) := hfrac
      _ ≤ (162 / (2 : ℝ) ^ (-26 : ℤ)) * E ^ g := by rw [hfrac']
      _ ≤ 162 / (2 : ℝ) ^ (-26 : ℤ) := hsmallCoeff
      _ ≤ 2 ^ (35 : ℕ) := hconst
  have hquot : e / ocTau α q Λ m =
      (e * (ocL α q Λ m : ℝ) ^ 2) / ocTauPP α q Λ m := by
    simp [ocTau]
    field_simp [ne_of_gt hτpos, ne_of_gt hLpos]
  rw [hquot]
  exact hfinal

private theorem epsilon_a_upper_bound {α s q : ℝ} {Λ m : ℕ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (hΛ : 128 ≤ Λ) (hm : 1 ≤ m) :
    ocEpsilon q Λ m * ocA α q Λ (m - 1) ≤ 4 := by
  let E := ocEpsilon q Λ (m - 1)
  let e := ocEpsilon q Λ m
  let δ := ocDelta α q
  let g := scaleGap α q
  have hparams := admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq
  have hδ : 0 < δ := by dsimp [δ]; exact hparams.2.1
  have hg : 0 < g := hparams.2.2.2.2.1
  have hspace := admissible_space_scale_facts hq hΛ hm
  have hEpos : 0 < E := (epsilon_basic (m := m - 1) hq.1 hΛ).1
  have hEle : E ≤ 1 := (epsilon_basic (m := m - 1) hq.1 hΛ).2.1
  have heupper : e ≤ 2 * E ^ q := by
    simpa [e, E] using hspace.2.2.2
  have hA : ocA α q Λ (m - 1) = E ^ (α - 1) := by
    simp [ocA, E]
    congr 1
    ring
  have hExpo : 0 < q + α - 1 := by
    have hgap : 0 < scaleGap α q := hparams.2.2.2.2.1
    have hexpo_id : q + α - 1 = scaleGap α q + 4 * δ := by
      dsimp [scaleGap, δ]
      ring
    rw [hexpo_id]
    positivity
  have hsmall : E ^ (q + α - 1) ≤ 1 :=
    Real.rpow_le_one hEpos.le hEle hExpo.le
  rw [hA]
  calc
    e * E ^ (α - 1) ≤ 2 * E ^ q * E ^ (α - 1) :=
      mul_le_mul_of_nonneg_right heupper (by positivity)
    _ = 2 * E ^ (q + α - 1) := by
      calc
        2 * E ^ q * E ^ (α - 1) = 2 * (E ^ q * E ^ (α - 1)) := by ring
        _ = 2 * E ^ (q + α - 1) := by
          rw [← Real.rpow_add hEpos q (α - 1)]
          congr 1
          ring_nf
    _ ≤ 2 := by
      calc
        2 * E ^ (q + α - 1) ≤ 2 * 1 :=
          mul_le_mul_of_nonneg_left hsmall (by norm_num : 0 ≤ (2 : ℝ))
        _ = 2 := by ring
    _ ≤ 4 := by norm_num

/-- All time-scale bounds, proved from the definitions of the construction. -/
theorem admissible_time_scale_facts {α s q : ℝ} {Λ m : ℕ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (hΛ : 128 ≤ Λ) (hm : 1 ≤ m) :
    5 ≤ ocL α q Λ m ∧
    4 * ocEpsilon q Λ (m - 1) ^ (-ocDelta α q) ≤ (ocL α q Λ m : ℝ) ∧
    (ocL α q Λ m : ℝ) ≤ 9 * ocEpsilon q Λ (m - 1) ^ (-ocDelta α q) ∧
    (2 : ℝ) ^ (-26 : ℤ) * ocEpsilon q Λ (m - 1) ^
      (2 - (1 + α) + 2 * ocDelta α q) ≤ ocTauPP α q Λ m ∧
    ocA α q Λ (m - 1) * ocTauPP α q Λ m ≤
      (2 : ℝ) ^ (-25 : ℤ) * ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q) ∧
    ocEpsilon q Λ m / ocTau α q Λ m ≤ 2 ^ (35 : ℕ) ∧
    ocEpsilon q Λ m * ocA α q Λ (m - 1) ≤ 4 ∧
    ocTauPP α q Λ m / ocTauP α q Λ m = (ocL α q Λ m : ℝ) ∧
    ocTauP α q Λ m / ocTau α q Λ m = (ocL α q Λ m : ℝ) := by
  have hparams := admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq
  have hδ := hparams.2.1
  have hEpos : 0 < ocEpsilon q Λ (m - 1) :=
    (epsilon_basic (m := m - 1) hq.1 hΛ).1
  have hEle : ocEpsilon q Λ (m - 1) ≤ 1 :=
    (epsilon_basic (m := m - 1) hq.1 hΛ).2.1
  have hκ : 0 < 2 - (1 + α) + 2 * ocDelta α q := by
    nlinarith [hα₁, hδ]
  have hL := block_length_bounds hδ hEpos hEle
  have hτlower := tauPP_lower_bound hκ hEpos hEle
  have hAτ := a_tauPP_upper_bound (α := α) hEpos
  have heτ := epsilon_over_tau_bound hα₀ hα₁ hs₀ hs₁ hq hΛ hm
  have hea := epsilon_a_upper_bound hα₀ hα₁ hs₀ hs₁ hq hΛ hm
  have hr1 : ocTauPP α q Λ m / ocTauP α q Λ m =
      (ocL α q Λ m : ℝ) := by
    have hτpos : 0 < ocTauPP α q Λ m := by
      exact lt_of_lt_of_le (by positivity) hτlower
    have hLpos : 0 < (ocL α q Λ m : ℝ) := by
      exact_mod_cast (show 0 < ocL α q Λ m by omega)
    simp [ocTauP]
    field_simp [ne_of_gt hτpos, ne_of_gt hLpos]
  have hr2 : ocTauP α q Λ m / ocTau α q Λ m =
      (ocL α q Λ m : ℝ) := by
    have hτpos : 0 < ocTauPP α q Λ m := by
      exact lt_of_lt_of_le (by positivity) hτlower
    have hLpos : 0 < (ocL α q Λ m : ℝ) := by
      exact_mod_cast (show 0 < ocL α q Λ m by omega)
    simp [ocTauP, ocTau]
    field_simp [ne_of_gt hτpos, ne_of_gt hLpos]
  exact ⟨hL.1, hL.2.1, hL.2.2, hτlower, hAτ, heτ, hea, hr1, hr2⟩

end AVRegularity.Scales
end
