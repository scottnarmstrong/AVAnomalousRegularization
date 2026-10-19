-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Scales.Times
public import AVRegularity.Definitions.CycleReference.OcRefCorrector
import AVRegularity.Construction.Stream.NextAdmissible
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain
import AVRegularity.CycleReference.ChartTestTransport
import AVRegularity.CycleReference.ChartCorrectionIntegrability
public import AVRegularity.Definitions.CycleReference.OcAsymp
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Construction.OcA
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Monotonicity.Lemmas

@[expose] public section

section
namespace AVRegularity.EntryScales

/-! Power comparisons `x ≍ E^a` with a common base `E`, used by the entry scale ledgers. -/

open AVRegularity.CycleReference

theorem aPow_mul {C D x y E a b : ℝ} (hE : 0 < E) (hC : 0 < C) (hD : 0 < D)
    (hx : ocAsymp C x (E ^ a)) (hy : ocAsymp D y (E ^ b)) :
    ocAsymp (C * D) (x * y) (E ^ (a + b)) := by
  have h := asymp_mul hC hD (Real.rpow_nonneg hE.le a) (Real.rpow_nonneg hE.le b) hx hy
  rwa [← Real.rpow_add hE] at h

theorem aPow_div {C D x y E a b : ℝ} (hE : 0 < E) (hC : 0 < C) (hD : 0 < D)
    (hy0 : 0 < y) (hx : ocAsymp C x (E ^ a)) (hy : ocAsymp D y (E ^ b)) :
    ocAsymp (C * D) (x / y) (E ^ (a - b)) := by
  have h := asymp_div hC hD (Real.rpow_nonneg hE.le a) (Real.rpow_pos_of_pos hE b) hy0 hx hy
  rwa [← Real.rpow_sub hE] at h

theorem aPow_sqrt {C x E a : ℝ} (hE : 0 < E) (hC : 0 < C)
    (hx : ocAsymp C x (E ^ a)) : ocAsymp (Real.sqrt C) (Real.sqrt x) (E ^ (a / 2)) := by
  have h := asymp_sqrt hC (Real.rpow_nonneg hE.le a) hx
  have e1 : Real.sqrt (E ^ a) = E ^ (a / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hE.le]; congr 1; ring
  rwa [e1] at h

theorem aPow_congr {C x E a b : ℝ} (hab : a = b) (hx : ocAsymp C x (E ^ a)) :
    ocAsymp C x (E ^ b) := by
  rwa [hab] at hx

theorem aPow_const_mul {C x X c : ℝ} (hC : 0 < C) (hc : 0 < c) (hX : 0 ≤ X)
    (hx : ocAsymp C x X) : ocAsymp (C * max c c⁻¹) (c * x) X := by
  have h1 : ocAsymp (max c c⁻¹) (c * X) X := by
    constructor
    · have : (max c c⁻¹)⁻¹ ≤ c := by
        have hm : 0 < max c c⁻¹ := lt_max_of_lt_left hc
        rw [inv_le_comm₀ hm hc]
        exact le_max_right _ _
      exact mul_le_mul_of_nonneg_right this hX
    · exact mul_le_mul_of_nonneg_right (le_max_left _ _) hX
  have h2 := asymp_scale_left hc.le hx
  have hm : 0 < max c c⁻¹ := lt_max_of_lt_left hc
  exact asymp_trans hC hm h2 h1

theorem asymp_sandwich {K ν B X : ℝ} (hK : 1 ≤ K) (hX : 0 ≤ X) (hlo : ν ≤ B)
    (hhi : B ≤ 2 * ν) (h : ocAsymp K ν X) : ocAsymp (2 * K) B X := by
  have hKp : 0 < K := by linarith
  constructor
  · have h1 : (2 * K)⁻¹ ≤ K⁻¹ := inv_anti₀ hKp (by linarith)
    exact (mul_le_mul_of_nonneg_right h1 hX).trans (h.1.trans hlo)
  · calc B ≤ 2 * ν := hhi
      _ ≤ 2 * (K * X) := by linarith [h.2]
      _ = 2 * K * X := by ring

theorem pow_bound {E K Y a r : ℝ} (hY : 0 ≤ Y) (hK : 0 ≤ K) (hE : 0 ≤ E)
    (h : E ≤ K * Y ^ a) (hr : 0 ≤ r) : E ^ r ≤ K ^ r * Y ^ (a * r) := by
  refine (Real.rpow_le_rpow hE h hr).trans (le_of_eq ?_)
  rw [Real.mul_rpow hK (Real.rpow_nonneg hY a), ← Real.rpow_mul hY]

/-- The radius `c_r √(B h)` with `B ≍ E^{β+γ}`, `h ≍ E^{2-β+2δ}` is `≍ E^{1+c}`. -/
theorem rho_asymp {α q B h E C D cr : ℝ} (hE : 0 < E) (hC : 0 < C) (hD : 0 < D)
    (hcr : 0 < cr) (hB : ocAsymp C B (E ^ ((1 + α) + ocGamma α q)))
    (hh : ocAsymp D h (E ^ (2 - (1 + α) + 2 * ocDelta α q))) :
    ocAsymp (Real.sqrt (C * D) * max cr cr⁻¹) (cr * Real.sqrt (B * h)) (E ^ (1 + ocC α q)) := by
  have hBh := aPow_mul hE hC hD hB hh
  have hsqrt := aPow_sqrt hE (by positivity) hBh
  have hsqrt' : ocAsymp (Real.sqrt (C * D)) (Real.sqrt (B * h)) (E ^ (1 + ocC α q)) :=
    aPow_congr (by unfold ocC; ring) hsqrt
  exact aPow_const_mul (Real.sqrt_pos.2 (by positivity)) hcr (Real.rpow_nonneg hE.le _) hsqrt'

end AVRegularity.EntryScales
end

section
open Filter Topology
namespace AVRegularity.EntryScales

/-! The renewal ratio `τ''_{m+1}/τ'_m ≤ C ε_{m-1}^{qγ+(2q+5)δ}`. -/

open AVRegularity.CycleReference

theorem tauRatio_bound {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) :
    ∃ C : ℝ, 0 < C ∧ ∀ Λ : ℕ, 128 ≤ Λ → ∀ m : ℕ, 1 ≤ m →
      ocTauPP α q Λ (m + 1) / ocTauP α q Λ m ≤
        C * ocEpsilon q Λ (m - 1) ^ (q * ocGamma α q + (2 * q + 5) * ocDelta α q) := by
  have hδ := (AVRegularity.Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq).2.1
  have ha : 0 ≤ 2 - (1 + α) + 2 * ocDelta α q := by linarith
  refine ⟨2 ^ (26 : ℕ) * 2 ^ (2 - (1 + α) + 2 * ocDelta α q) * (2 ^ (26 : ℕ) * 9), by positivity, ?_⟩
  intro Λ h128 m hm
  have hΛ1 : 1 ≤ Λ := by omega
  have hE := AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 h128
  have hx := AVRegularity.Scales.epsilon_basic (m := m) hq.1 h128
  have h1 := ocTauPP_asymp hα0 hα1 hs0 hs1 hq h128 (m := m + 1)
  rw [Nat.add_sub_cancel] at h1
  have h2 := ocTauP_asymp hα0 hα1 hs0 hs1 hq h128 (m := m)
  have hstep := AVRegularity.Scales.epsilon_q_step hq.1 hq.2.1 h128 hm
  have hxa : ocEpsilon q Λ m ^ (2 - (1 + α) + 2 * ocDelta α q) ≤
      2 ^ (2 - (1 + α) + 2 * ocDelta α q) *
        ocEpsilon q Λ (m - 1) ^ (q * (2 - (1 + α) + 2 * ocDelta α q)) := by
    refine (Real.rpow_le_rpow hx.1.le hstep ha).trans (le_of_eq ?_)
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hE.1.le _),
      ← Real.rpow_mul hE.1.le]
  have hxle : ocTauPP α q Λ (m + 1) ≤
      (2 ^ (26 : ℕ) * 2 ^ (2 - (1 + α) + 2 * ocDelta α q)) *
        ocEpsilon q Λ (m - 1) ^ (q * (2 - (1 + α) + 2 * ocDelta α q)) := by
    refine h1.2.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hxa (by positivity)
  have hy : 0 < ocTauP α q Λ m := by
    unfold ocTauP
    have hL : 0 < (ocL α q Λ m : ℝ) := by
      have : 0 < ocL α q Λ m := by unfold ocL; omega
      exact_mod_cast this
    exact div_pos (AVRegularity.Construction.Stream.ocTauPP_pos hΛ1) hL
  have hq' := quotient_upper_bound (by positivity) (by positivity)
    (Real.rpow_nonneg hE.1.le (q * (2 - (1 + α) + 2 * ocDelta α q)))
    (Real.rpow_pos_of_pos hE.1 (2 - (1 + α) + 3 * ocDelta α q)) hy hxle h2.1
  refine hq'.trans (le_of_eq ?_)
  rw [← Real.rpow_sub hE.1]
  have hmem := memory_exponent_identity (α := α) hq.1
  congr 2
  linarith [hmem]

theorem ocTauP_pos' {α q : ℝ} {Λ m : ℕ} (hΛ : 1 ≤ Λ) : 0 < ocTauP α q Λ m := by
  unfold ocTauP
  have hL : 0 < (ocL α q Λ m : ℝ) := by
    have : 0 < ocL α q Λ m := by unfold ocL; omega
    exact_mod_cast this
  exact div_pos (AVRegularity.Construction.Stream.ocTauPP_pos hΛ) hL

theorem tauRatio_tendsto {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {Λ : ℕ} (h128 : 128 ≤ Λ) :
    Tendsto (fun M : ℕ => ocTauPP α q Λ (M + 1) / ocTauP α q Λ M) atTop (𝓝 0) := by
  obtain ⟨Cr, hCr, hrat⟩ := tauRatio_bound hα0 hα1 hs0 hs1 hq
  have hγ := (AVRegularity.Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq).1
  have hδ := (AVRegularity.Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq).2.1
  have hq1 := hq.1
  have hq0 : 0 < q := by linarith
  have hpe : 0 < q * ocGamma α q + (2 * q + 5) * ocDelta α q := by positivity
  have h1 := (Real.continuousAt_rpow_const 0
    (q * ocGamma α q + (2 * q + 5) * ocDelta α q) (Or.inr hpe.le)).tendsto.comp
    (epsilon_parent_tendsto_zero (Λ := Λ) hq1 h128)
  rw [Real.zero_rpow hpe.ne'] at h1
  have h2 := h1.const_mul Cr
  rw [mul_zero] at h2
  refine squeeze_zero' ?_ ?_ h2
  · exact Eventually.of_forall fun M =>
      div_nonneg (AVRegularity.Construction.Stream.ocTauPP_pos (by omega)).le
        (ocTauP_pos' (by omega)).le
  · filter_upwards [eventually_ge_atTop 1] with M hM
    exact hrat Λ h128 M hM

end AVRegularity.EntryScales
end

section
namespace AVRegularity.EntryScales

/-! The weak scale ledger (the scales of Lemma 14.1(a) of the paper) in plain real variables
(`ν = κ_M` in the permitted band, weak level `i > M`, `E = ε_{i-1}`, `e = ε_i`). -/

section
open AVRegularity.CycleReference

theorem epsilon_antitone {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ) :
    Antitone (fun n : ℕ => ocEpsilon q Λ n) :=
  antitone_nat_of_succ_le fun n => epsilon_succ_le (q := q) (Λ := Λ) (n := n) hq hΛ

theorem ocGamma_mul_identity (α q : ℝ) (hq : 1 < q) :
    (q - 1) * (1 + α) = ocGamma α q * (q + 1) := by
  unfold ocGamma
  field_simp

theorem weak_scales_core {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ Λ : ℕ, 128 ≤ Λ → ∀ M : ℕ, ∀ ν : ℝ, ν ∈ ocBand α q Λ M →
      ∀ i : ℕ, M < i →
      ocEpsilon q Λ i ^ (1 + α) / ν ≤ C * ocEpsilon q Λ (i - 1) ^ ((q + 2) * ocGamma α q) ∧
      ocA α q Λ (i - 1) * ocEpsilon q Λ (i - 1) ^ 2 / ν ≤
        C * ocEpsilon q Λ (i - 1) ^ ocGamma α q ∧
      ocEpsilon q Λ (i - 1) ^ 2 / (ν * ocTauP α q Λ i) ≤
        C * ocEpsilon q Λ (i - 1) ^ (ocGamma α q - 3 * ocDelta α q) ∧
      C⁻¹ * ocEpsilon q Λ (i - 1) ^ (-(2 * (q - 1) + ocGamma α q - 4 * ocDelta α q)) ≤
        ν * ocTau α q Λ i / ocEpsilon q Λ i ^ 2 ∧
      ocTauPP α q Λ (i + 1) / ocTauP α q Λ i ≤
        C * ocEpsilon q Λ (i - 1) ^ (q * ocGamma α q + (2 * q + 5) * ocDelta α q) := by
  obtain ⟨Cr, hCr, hrat⟩ := tauRatio_bound hα0 hα1 hs0 hs1 hq
  have hγ := (AVRegularity.Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq).1
  have hδ := (AVRegularity.Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq).2.1
  have hγβ : ocGamma α q < 1 + α := by
    have h := ocGamma_mul_identity α q hq.1
    have hb : 0 < 1 + α := by linarith
    have h2 : ocGamma α q * (q + 1) < (1 + α) * (q + 1) := by
      rw [← h]; nlinarith only [mul_lt_mul_of_pos_right (show q - 1 < q + 1 by linarith) hb]
    exact lt_of_mul_lt_mul_right h2 (by linarith [hq.1])
  obtain ⟨Cf, hCfdef⟩ : ∃ Cf : ℝ, Cf = 2 * 2 ^ (1 + α) + 2 + 2 * (2 ^ (26 : ℕ) * 9) +
      8 * (2 ^ (26 : ℕ) * 81) + Cr + 1 := ⟨_, rfl⟩
  have hp2 : 0 < (2 : ℝ) ^ (1 + α) := by positivity
  have hp26 : (0 : ℝ) < 2 ^ (26 : ℕ) := by positivity
  have n9 : (0 : ℝ) < 2 ^ (26 : ℕ) * 9 := by positivity
  have n81 : (0 : ℝ) < 2 ^ (26 : ℕ) * 81 := by positivity
  have hcf : 2 * 2 ^ (1 + α) ≤ Cf ∧ 2 ≤ Cf ∧ 2 * (2 ^ (26 : ℕ) * 9) ≤ Cf ∧
      8 * (2 ^ (26 : ℕ) * 81) ≤ Cf ∧ Cr ≤ Cf ∧ 1 ≤ Cf := by
    rw [hCfdef]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith only [hp2, n9, n81, hCr]
  have hCf1 : 1 ≤ Cf := hcf.2.2.2.2.2
  refine ⟨Cf, hCf1, fun Λ h128 M ν hν i hi => ?_⟩
  have hΛ1 : 1 ≤ Λ := by omega
  have hi1 : 1 ≤ i := by omega
  have hE := AVRegularity.Scales.epsilon_basic (m := i - 1) hq.1 h128
  have hx := AVRegularity.Scales.epsilon_basic (m := M) hq.1 h128
  have he := AVRegularity.Scales.epsilon_basic (m := i) hq.1 h128
  set E := ocEpsilon q Λ (i - 1) with hEd
  set e := ocEpsilon q Λ i with hed
  have hEx : E ≤ ocEpsilon q Λ M := epsilon_antitone hq.1 h128 (by omega : M ≤ i - 1)
  have hEn : ∀ r : ℝ, 0 ≤ E ^ r := fun r => Real.rpow_nonneg hE.1.le r
  have hEp : ∀ r : ℝ, 0 < E ^ r := fun r => Real.rpow_pos_of_pos hE.1 r
  set p := (1 + α) - ocGamma α q with hpd
  have hp : 0 < p := by rw [hpd]; linarith
  have hνE : E ^ p / 2 ≤ ν := by
    have h1 : E ^ p ≤ ocEpsilon q Λ M ^ p := Real.rpow_le_rpow hE.1.le hEx hp.le
    have h2 : ocEpsilon q Λ M ^ p / 2 ≤ ν := hν.1
    linarith
  have hν0 : 0 < ν := lt_of_lt_of_le (by have := hEp p; positivity) hνE
  have hestep : e ≤ 2 * E ^ q := AVRegularity.Scales.epsilon_q_step hq.1 hq.2.1 h128 hi1
  have hid := ocGamma_mul_identity α q hq.1
  have hExp : ∀ {a b : ℝ}, E ^ a * E ^ b = E ^ (a + b) := fun {a b} =>
    (Real.rpow_add hE.1 a b).symm
  have hE2 : E ^ 2 = E ^ (2 : ℝ) := (Real.rpow_two E).symm
  have h2ν : E ^ p ≤ 2 * ν := by linarith
  -- (a)
  have h1a : e ^ (1 + α) ≤ 2 ^ (1 + α) * E ^ (q * (1 + α)) := by
    refine (Real.rpow_le_rpow he.1.le hestep (by linarith)).trans (le_of_eq ?_)
    rw [Real.mul_rpow (by norm_num) (hEn _), ← Real.rpow_mul hE.1.le]
  have h3a : E ^ ((q + 2) * ocGamma α q) * E ^ p = E ^ (q * (1 + α)) := by
    rw [hExp]; congr 1; rw [hpd]; linarith [hid]
  have hfa : e ^ (1 + α) / ν ≤ Cf * E ^ ((q + 2) * ocGamma α q) := by
    rw [div_le_iff₀ hν0]
    have hc : 2 * 2 ^ (1 + α) ≤ Cf := hcf.1
    calc e ^ (1 + α) ≤ 2 ^ (1 + α) * (E ^ ((q + 2) * ocGamma α q) * E ^ p) := by
          rw [h3a]; exact h1a
      _ ≤ (2 * 2 ^ (1 + α) * E ^ ((q + 2) * ocGamma α q)) * ν := by
          have := mul_le_mul_of_nonneg_left h2ν
            (mul_nonneg hp2.le (hEn ((q + 2) * ocGamma α q)))
          calc 2 ^ (1 + α) * (E ^ ((q + 2) * ocGamma α q) * E ^ p)
              = (2 ^ (1 + α) * E ^ ((q + 2) * ocGamma α q)) * E ^ p := by ring
            _ ≤ (2 ^ (1 + α) * E ^ ((q + 2) * ocGamma α q)) * (2 * ν) := this
            _ = (2 * 2 ^ (1 + α) * E ^ ((q + 2) * ocGamma α q)) * ν := by ring
      _ ≤ Cf * E ^ ((q + 2) * ocGamma α q) * ν := by
          have := mul_le_mul_of_nonneg_right hc (hEn ((q + 2) * ocGamma α q))
          exact mul_le_mul_of_nonneg_right this hν0.le
  -- (b)
  have hA : ocA α q Λ (i - 1) = E ^ ((1 + α) - 2) := rfl
  have hfb : ocA α q Λ (i - 1) * E ^ 2 / ν ≤ Cf * E ^ ocGamma α q := by
    rw [div_le_iff₀ hν0, hA, hE2, hExp]
    have h0 : E ^ ((1 + α) - 2 + 2) = E ^ ocGamma α q * E ^ p := by
      rw [hExp]; congr 1; rw [hpd]; ring
    rw [h0]
    have hc : 2 ≤ Cf := hcf.2.1
    calc E ^ ocGamma α q * E ^ p ≤ E ^ ocGamma α q * (2 * ν) :=
          mul_le_mul_of_nonneg_left h2ν (hEn _)
      _ ≤ Cf * E ^ ocGamma α q * ν := by
          have := mul_le_mul_of_nonneg_right hc (mul_nonneg (hEn (ocGamma α q)) hν0.le)
          calc E ^ ocGamma α q * (2 * ν) = 2 * (E ^ ocGamma α q * ν) := by ring
            _ ≤ Cf * (E ^ ocGamma α q * ν) := this
            _ = Cf * E ^ ocGamma α q * ν := by ring
  -- (c)
  have hτ' := ocTauP_asymp hα0 hα1 hs0 hs1 hq h128 (m := i)
  have hτ'pos : 0 < ocTauP α q Λ i := by
    unfold ocTauP
    have hL : 0 < (ocL α q Λ i : ℝ) := by
      have : 0 < ocL α q Λ i := by unfold ocL; omega
      exact_mod_cast this
    exact div_pos (AVRegularity.Construction.Stream.ocTauPP_pos hΛ1) hL
  have hbτ' : E ^ (2 - (1 + α) + 3 * ocDelta α q) ≤ (2 ^ (26 : ℕ) * 9) * ocTauP α q Λ i := by
    have := hτ'.1
    rw [inv_mul_le_iff₀ (by positivity)] at this
    exact this
  have hfc : E ^ 2 / (ν * ocTauP α q Λ i) ≤ Cf * E ^ (ocGamma α q - 3 * ocDelta α q) := by
    rw [div_le_iff₀ (mul_pos hν0 hτ'pos)]
    have h0 : E ^ 2 = E ^ (ocGamma α q - 3 * ocDelta α q) *
        (E ^ p * E ^ (2 - (1 + α) + 3 * ocDelta α q)) := by
      rw [hE2, hExp, hExp]; congr 1; rw [hpd]; ring
    rw [h0]
    have hc : 2 * (2 ^ (26 : ℕ) * 9) ≤ Cf := hcf.2.2.1
    have h4 : E ^ p * E ^ (2 - (1 + α) + 3 * ocDelta α q) ≤
        (2 * ν) * ((2 ^ (26 : ℕ) * 9) * ocTauP α q Λ i) :=
      mul_le_mul h2ν hbτ' (hEn _) (by linarith)
    have h5 := mul_le_mul_of_nonneg_left h4 (hEn (ocGamma α q - 3 * ocDelta α q))
    have h6 : 0 ≤ E ^ (ocGamma α q - 3 * ocDelta α q) * (ν * ocTauP α q Λ i) :=
      mul_nonneg (hEn _) (mul_pos hν0 hτ'pos).le
    have h7 := mul_le_mul_of_nonneg_right hc h6
    calc E ^ (ocGamma α q - 3 * ocDelta α q) * (E ^ p * E ^ (2 - (1 + α) + 3 * ocDelta α q))
        ≤ E ^ (ocGamma α q - 3 * ocDelta α q) * ((2 * ν) * ((2 ^ (26 : ℕ) * 9) *
            ocTauP α q Λ i)) := h5
      _ = (2 * (2 ^ (26 : ℕ) * 9)) * (E ^ (ocGamma α q - 3 * ocDelta α q) *
            (ν * ocTauP α q Λ i)) := by ring
      _ ≤ Cf * (E ^ (ocGamma α q - 3 * ocDelta α q) * (ν * ocTauP α q Λ i)) := h7
      _ = Cf * E ^ (ocGamma α q - 3 * ocDelta α q) * (ν * ocTauP α q Λ i) := by ring  -- (d)
  have hτ := ocTau_asymp hα0 hα1 hs0 hs1 hq h128 (m := i)
  have hτpos : 0 < ocTau α q Λ i := AVRegularity.Construction.Stream.ocTau_pos hΛ1
  have hbτ : E ^ (2 - (1 + α) + 4 * ocDelta α q) ≤ (2 ^ (26 : ℕ) * 81) * ocTau α q Λ i := by
    have := hτ.1
    rw [inv_mul_le_iff₀ (by positivity)] at this
    exact this
  have he2 : e ^ 2 ≤ 4 * E ^ (q + q) := by
    have h1 : e ^ 2 ≤ (2 * E ^ q) ^ 2 := pow_le_pow_left₀ he.1.le hestep 2
    refine h1.trans (le_of_eq ?_)
    rw [mul_pow, ← Real.rpow_natCast (E ^ q) 2, ← Real.rpow_mul hE.1.le]
    norm_num
    ring_nf
  have hfd : Cf⁻¹ * E ^ (-(2 * (q - 1) + ocGamma α q - 4 * ocDelta α q)) ≤
      ν * ocTau α q Λ i / e ^ 2 := by
    rw [le_div_iff₀ (pow_pos he.1 2)]
    have h0 : E ^ (-(2 * (q - 1) + ocGamma α q - 4 * ocDelta α q)) * E ^ (q + q) =
        E ^ p * E ^ (2 - (1 + α) + 4 * ocDelta α q) := by
      rw [hExp, hExp]; congr 1; rw [hpd]; ring
    have h1 : E ^ (-(2 * (q - 1) + ocGamma α q - 4 * ocDelta α q)) * e ^ 2 ≤
        8 * (2 ^ (26 : ℕ) * 81) * (ν * ocTau α q Λ i) := by
      calc E ^ (-(2 * (q - 1) + ocGamma α q - 4 * ocDelta α q)) * e ^ 2
          ≤ E ^ (-(2 * (q - 1) + ocGamma α q - 4 * ocDelta α q)) * (4 * E ^ (q + q)) :=
            mul_le_mul_of_nonneg_left he2 (hEn _)
        _ = 4 * (E ^ p * E ^ (2 - (1 + α) + 4 * ocDelta α q)) := by rw [← h0]; ring
        _ ≤ 4 * ((2 * ν) * ((2 ^ (26 : ℕ) * 81) * ocTau α q Λ i)) := by
            have := mul_le_mul h2ν hbτ (hEn _) (by linarith only [hν0])
            linarith only [this]
        _ = 8 * (2 ^ (26 : ℕ) * 81) * (ν * ocTau α q Λ i) := by ring
    have hCfp : 0 < Cf := by linarith only [hCf1]
    rw [mul_assoc, inv_mul_le_iff₀ hCfp]
    have hc : 8 * (2 ^ (26 : ℕ) * 81) ≤ Cf := hcf.2.2.2.1
    have hnn : 0 ≤ ν * ocTau α q Λ i := (mul_pos hν0 hτpos).le
    have h7 := mul_le_mul_of_nonneg_right hc hnn
    linarith only [h1, h7]
  have hfe : ocTauPP α q Λ (i + 1) / ocTauP α q Λ i ≤
      Cf * E ^ (q * ocGamma α q + (2 * q + 5) * ocDelta α q) :=
    (hrat Λ h128 i hi1).trans
      (mul_le_mul_of_nonneg_right (by linarith only [hcf.2.2.2.2.1, hCr]) (hEn _))
  exact ⟨hfa, hfb, hfc, hfd, hfe⟩
end

/-! Comparisons of the terminal scales `ν = κ_M`, `x = ε_M`, `h = τ_M''`, `τ_M` with powers of
`E = ε_{M-1}`. -/

section
open AVRegularity.CycleReference

theorem terminal_comparisons {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) :
    ∃ K : ℝ, 1 ≤ K ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ M : ℕ, 2 ≤ M →
      ∀ ν : ℝ, ν ∈ ocBand α q Λ M →
        ocAsymp K ν (ocEpsilon q Λ (M - 1) ^ ((1 + α) + ocGamma α q)) ∧
        ocAsymp K (ocEpsilon q Λ M) (ocEpsilon q Λ (M - 1) ^ q) ∧
        ocAsymp K (ocTauPP α q Λ M) (ocEpsilon q Λ (M - 1) ^ (2 - (1 + α) + 2 * ocDelta α q)) ∧
        ocAsymp K (ocTau α q Λ M) (ocEpsilon q Λ (M - 1) ^ (2 - (1 + α) + 4 * ocDelta α q)) := by
  obtain ⟨K1, hK1, L1, hL1, h1⟩ := epsilon_power_scale_asymp hq.1 ((1 + α) - ocGamma α q)
  obtain ⟨K2, hK2, L2, hL2, h2⟩ := epsilon_power_scale_asymp hq.1 1
  let K : ℝ := 2 * K1 + K2 + 2 ^ (26 : ℕ) * 81
  have hK : 1 ≤ K := by dsimp [K]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) 26]
  have hKp : 0 < K := by linarith
  refine ⟨K, hK, max L1 L2, hL1.trans (le_max_left _ _), ?_⟩
  intro Λ hΛ M hM ν hν
  have hΛ1 : L1 ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛ2 : L2 ≤ Λ := (le_max_right _ _).trans hΛ
  have h128 : 128 ≤ Λ := hL1.trans hΛ1
  have hx := AVRegularity.Scales.epsilon_basic (m := M) hq.1 h128
  have hE := AVRegularity.Scales.epsilon_basic (m := M - 1) hq.1 h128
  have hband : ocAsymp 2 ν (ocEpsilon q Λ M ^ ((1 + α) - ocGamma α q)) := by
    constructor
    · have := hν.1
      rw [show (2 : ℝ)⁻¹ * ocEpsilon q Λ M ^ ((1 + α) - ocGamma α q) =
        ocEpsilon q Λ M ^ ((1 + α) - ocGamma α q) / 2 by ring]
      exact this
    · exact hν.2
  have hp1 := h1 Λ M hΛ1 hM
  rw [enhancement_exponent_identity hq.1] at hp1
  have hν' : ocAsymp (2 * K1) ν (ocEpsilon q Λ (M - 1) ^ ((1 + α) + ocGamma α q)) :=
    asymp_trans (by norm_num) (by linarith) hband hp1
  have hp2 := h2 Λ M hΛ2 hM
  rw [Real.rpow_one, mul_one] at hp2
  have hK1p : 0 < K1 := by linarith
  have hKe : 0 ≤ ocEpsilon q Λ (M - 1) ^ ((1 + α) + ocGamma α q) :=
    Real.rpow_nonneg hE.1.le _
  refine ⟨asymp_mono_constant (by positivity) (by dsimp [K]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) 26]) hKe hν',
    asymp_mono_constant (by linarith) (by dsimp [K]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) 26])
      (Real.rpow_nonneg hE.1.le _) hp2, ?_, ?_⟩
  · exact asymp_mono_constant (by positivity)
      (by dsimp [K]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) 26])
      (Real.rpow_nonneg hE.1.le _) (ocTauPP_asymp hα0 hα1 hs0 hs1 hq h128)
  · exact asymp_mono_constant (by positivity) (by dsimp [K]; nlinarith)
      (Real.rpow_nonneg hE.1.le _) (ocTau_asymp hα0 hα1 hs0 hs1 hq h128)
end

end AVRegularity.EntryScales
end

section
open Filter Topology
namespace AVRegularity.EntryScales

/-! The terminal passage `B = κ_{M-1} = K̄_M(ν)` satisfies `ν ≤ B ≤ 2ν` for large `M`.
-/

open AVRegularity.CycleReference

theorem epsilon_tendsto_zero {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ) :
    Tendsto (fun M : ℕ => ocEpsilon q Λ M) atTop (𝓝 0) := by
  have h := epsilon_parent_tendsto_zero hq hΛ
  refine squeeze_zero' ?_ ?_ h
  · exact Eventually.of_forall fun M =>
      (AVRegularity.Scales.epsilon_basic (m := M) hq hΛ).1.le
  · filter_upwards [eventually_ge_atTop 1] with M hM
    have := epsilon_succ_le (q := q) (Λ := Λ) (n := M - 1) hq hΛ
    rwa [Nat.sub_add_cancel hM] at this

theorem epsilon_rpow_tendsto_zero {q p : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ)
    (hp : 0 < p) : Tendsto (fun M : ℕ => ocEpsilon q Λ M ^ p) atTop (𝓝 0) := by
  have h := ((Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto.comp
    (epsilon_tendsto_zero hq hΛ))
  rw [Real.zero_rpow hp.ne'] at h
  exact h

theorem terminal_ratio_le_two {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ M₁ : ℕ, 2 ≤ M₁ ∧ ∀ M : ℕ, M₁ ≤ M →
      ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ → κ M ≤ κ (M - 1) ∧ κ (M - 1) ≤ 2 * κ M := by
  obtain ⟨Ce, hCe⟩ := refFlux_mean_enhancement hζ
  obtain ⟨Cm, hCm, Λm, hΛm, hm⟩ := bandChain_memory_scale hα0 hα1 hs0 hs1 hq hζ
  have hγ := (AVRegularity.Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq).1
  have hδ := (AVRegularity.Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq).2.1
  refine ⟨Λm, hΛm, fun Λ hΛ => ?_⟩
  have h128 : 128 ≤ Λ := hΛm.trans hΛ
  have hΛ1 : 1 ≤ Λ := by omega
  let c1 : ℝ := 9 / 80 + |Ce| * (Cm + 1)
  have hc1 : 0 < c1 := by
    have : 0 ≤ |Ce| * (Cm + 1) := mul_nonneg (abs_nonneg _) (by linarith)
    simp only [c1]; linarith
  have hev := (epsilon_rpow_tendsto_zero (p := 2 * ocGamma α q) hq.1 h128
    (by linarith)).eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (4 * c1) by positivity))
  obtain ⟨M₂, hM₂⟩ := eventually_atTop.1 hev
  refine ⟨max M₂ 2, le_max_right _ _, fun M hM κ hκ => ?_⟩
  have hM2 : 2 ≤ M := (le_max_right _ _).trans hM
  have hMM₂ : M₂ ≤ M := (le_max_left _ _).trans hM
  have hν : 0 < κ M := bandChain_pos hΛ1 hζ hκ (le_refl M)
  have hlow := bandChain_step_ge hΛ1 hζ hκ (by omega : 1 ≤ M) (le_refl M)
  refine ⟨hlow, ?_⟩
  have hx := AVRegularity.Scales.epsilon_basic (m := M) hq.1 h128
  have hE := AVRegularity.Scales.epsilon_basic (m := M - 1) hq.1 h128
  set x := ocEpsilon q Λ M with hxdef
  set ν := κ M with hνdef
  have hkM : κ (M - 1) = ocMeanFlux α q Λ ζ M ν := hκ.2 M (by omega) (le_refl M)
  have hmain := hCe α q Λ M hΛ1 ν hν
  have hmem := (hm Λ hΛ M (by omega) κ hκ M hM2 (le_refl M)).1
  rw [ocEll_sq_eq hν] at hmem
  have hEd : ocEpsilon q Λ (M - 1) ^ ocDelta α q ≤ 1 :=
    Real.rpow_le_one hE.1.le hE.2.1 hδ.le
  have hE4 : ocEpsilon q Λ (M - 1) ^ (4 * ocDelta α q) ≤ 1 :=
    Real.rpow_le_one hE.1.le hE.2.1 (by linarith)
  set S := x ^ (2 * (1 + α)) / ν with hS
  have hS0 : 0 ≤ S := (div_pos (Real.rpow_pos_of_pos hx.1 _) hν).le
  have hR : x ^ 2 / (ν * ocTau α q Λ M) ≤ Cm := by
    have h1 : x ^ 2 / ν / ocTau α q Λ M = x ^ 2 / (ν * ocTau α q Λ M) := by
      rw [div_div]
    rw [← h1]
    exact hmem.trans (by simpa using mul_le_mul_of_nonneg_left hE4 (by linarith : 0 ≤ Cm))
  have hb : |ocMeanFlux α q Λ ζ M ν - ν - 9 / 80 * x ^ (2 * (1 + α)) / ν| ≤
      |Ce| * S * (Cm + 1) := by
    refine hmain.trans ?_
    have hCe' : Ce * S ≤ |Ce| * S := mul_le_mul_of_nonneg_right (le_abs_self _) hS0
    have hsum : x ^ 2 / (ν * ocTau α q Λ M) + ocEpsilon q Λ (M - 1) ^ ocDelta α q ≤
        Cm + 1 := add_le_add hR hEd
    have hτ0 := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := M) hΛ1
    have hs0' : 0 ≤ x ^ 2 / (ν * ocTau α q Λ M) + ocEpsilon q Λ (M - 1) ^ ocDelta α q :=
      add_nonneg (div_nonneg (sq_nonneg x) (mul_pos hν hτ0).le)
        (Real.rpow_nonneg hE.1.le _)
    exact mul_le_mul hCe' hsum hs0' (mul_nonneg (abs_nonneg _) hS0)
  have hup : ocMeanFlux α q Λ ζ M ν - ν ≤ c1 * S := by
    have := (abs_le.1 hb).2
    have h9 : 9 / 80 * x ^ (2 * (1 + α)) / ν = 9 / 80 * S := by rw [hS]; ring
    rw [h9] at this
    simp only [c1]
    nlinarith [this]
  -- smallness
  have hsmall : x ^ (2 * ocGamma α q) ≤ 1 / (4 * c1) := (hM₂ M hMM₂).le
  have hbandl : x ^ ((1 + α) - ocGamma α q) / 2 ≤ ν := by simpa [hxdef, hνdef] using hκ.1.1
  have hsplit : x ^ (2 * (1 + α)) =
      x ^ (2 * ((1 + α) - ocGamma α q)) * x ^ (2 * ocGamma α q) := by
    rw [← Real.rpow_add hx.1]; congr 1; ring
  have hsq : x ^ (2 * ((1 + α) - ocGamma α q)) = (x ^ ((1 + α) - ocGamma α q)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.1.le]; congr 1; push_cast; ring
  have hp0 : 0 < x ^ ((1 + α) - ocGamma α q) := Real.rpow_pos_of_pos hx.1 _
  have hν2 : (x ^ ((1 + α) - ocGamma α q)) ^ 2 ≤ 4 * ν ^ 2 := by nlinarith
  have hxg0 : 0 ≤ x ^ (2 * ocGamma α q) := Real.rpow_nonneg hx.1.le _
  -- c1 * S ≤ ν
  have hkey : c1 * x ^ (2 * (1 + α)) ≤ ν ^ 2 := by
    rw [hsplit, hsq]
    have h1 : c1 * x ^ (2 * ocGamma α q) ≤ 1 / 4 := by
      have := mul_le_mul_of_nonneg_left hsmall hc1.le
      refine this.trans (le_of_eq ?_)
      field_simp
    calc c1 * ((x ^ ((1 + α) - ocGamma α q)) ^ 2 * x ^ (2 * ocGamma α q))
        = (x ^ ((1 + α) - ocGamma α q)) ^ 2 * (c1 * x ^ (2 * ocGamma α q)) := by ring
      _ ≤ (4 * ν ^ 2) * (1 / 4) :=
          mul_le_mul hν2 h1 (by positivity) (by positivity)
      _ = ν ^ 2 := by ring
  have hcS : c1 * S ≤ ν := by
    rw [hS, ← mul_div_assoc, div_le_iff₀ hν]
    nlinarith [hkey]
  rw [hkM]
  linarith

end AVRegularity.EntryScales
end

section
namespace AVRegularity.EntryScales

/-! The entry widths in plain real variables. -/

section
open AVRegularity.CycleReference

/-- The exponent inequalities of the entry widths (Proposition 14.11(iv) of the paper). -/
theorem width_exponent_gaps {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {σw tT : ℝ} (hσ : 0 < σw) (ht : 0 < tT) :
    3 * ocDelta α q < q ^ 2 * (1 + σw) - 1 - ocC α q ∧
      4 * ocDelta α q < q * (1 + ocC α q + tT) - 1 - ocC α q := by
  obtain ⟨hγ, hδ, -, -, -, hc⟩ := AVRegularity.Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq
  have hq1 := hq.1
  have hid := ocGamma_mul_identity α q hq1
  have hδ4 : 4 * ocDelta α q < q - 1 := by
    have hf : 0 < (2 * q + 1) * (1 + α) / (2 * q + 2) := by positivity
    unfold ocDelta
    nlinarith
  have hγ2 : 2 * ocGamma α q ≤ 4 / 3 * (q - 1) := by nlinarith
  have hcdef : ocC α q = ocGamma α q / 2 + ocDelta α q := rfl
  constructor
  · have h1 : q ^ 2 * 1 ≤ q ^ 2 * (1 + σw) := by nlinarith [sq_nonneg q]
    nlinarith
  · have h1 : 0 < q * tT := mul_pos (by linarith) ht
    nlinarith

theorem widths_core {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ σw tT c₀ cr : ℝ,
      0 < σw → 0 < tT → 0 < c₀ → 0 < cr →
      ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ, 3 ≤ M → ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
      ocEpsilon q Λ M ^ (1 + σw) /
          (c₀ * min (ocEpsilon q Λ (M - 1))
            (Real.sqrt (κ (M - 1) / ocA α q Λ (M - 1)))) ≤
        C * ocEpsilon q Λ (M - 1) ^ (q * ocGamma α q + 4 * ocDelta α q + q * σw) ∧
      cr * Real.sqrt (κ (M - 1) * ocTauPP α q Λ M) * ocEpsilon q Λ (M - 1) ^ tT /
          (c₀ * min (ocEpsilon q Λ (M - 1))
            (Real.sqrt (κ (M - 1) / ocA α q Λ (M - 1)))) ≤
        C * ocEpsilon q Λ (M - 1) ^ (ocDelta α q + tT) ∧
      ocEpsilon q Λ M ^ (1 + σw) /
          (cr * Real.sqrt (κ (M - 1 - 1) * ocTauPP α q Λ (M - 1))) ≤
        C * ocEpsilon q Λ (M - 1 - 1) ^ (q ^ 2 * (1 + σw) - 1 - ocC α q) ∧
      cr * Real.sqrt (κ (M - 1) * ocTauPP α q Λ M) * ocEpsilon q Λ (M - 1) ^ tT /
          (cr * Real.sqrt (κ (M - 1 - 1) * ocTauPP α q Λ (M - 1))) ≤
        C * ocEpsilon q Λ (M - 1 - 1) ^ (q * (1 + ocC α q + tT) - 1 - ocC α q) := by
  obtain ⟨Ci, hCi, Li, hLi, hi⟩ := bandChain_interior_diffusivities hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨K1, hK1, L1, hL1, h1⟩ := epsilon_power_scale_asymp hq.1 1
  have hγ := (AVRegularity.Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq).1
  have hδ := (AVRegularity.Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq).2.1
  have hCip : 0 < Ci := by linarith
  have hK1p : 0 < K1 := by linarith
  refine ⟨max Li L1, hLi.trans (le_max_left _ _), fun Λ hΛ σw tT c₀ cr hσ ht hc₀ hcr => ?_⟩
  have hΛi : Li ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛ1 : L1 ≤ Λ := (le_max_right _ _).trans hΛ
  have h128 : 128 ≤ Λ := hLi.trans hΛi
  have hΛpos : 1 ≤ Λ := by omega
  -- constants depending only on the data
  set Cρ : ℝ := Real.sqrt (Ci * 2 ^ (26 : ℕ)) * max cr cr⁻¹ with hCρ
  have hCρp : 0 < Cρ := mul_pos (Real.sqrt_pos.2 (by positivity)) (lt_max_of_lt_left hcr)
  set Cm : ℝ := (Real.sqrt (Ci * 1))⁻¹ ⊓ 1 with hCm
  have hCmp : 0 < Cm := lt_min (inv_pos.2 (Real.sqrt_pos.2 (by positivity))) one_pos
  have hmul1 : 0 < c₀ * Cm := mul_pos hc₀ hCmp
  have hsr : 0 < Real.sqrt (Ci * 1) := Real.sqrt_pos.2 (by positivity)
  obtain ⟨Cf, hCfdef⟩ : ∃ Cf : ℝ, Cf =
      (K1 ^ (1 + σw) * (c₀ * Cm)⁻¹) + (Cρ * (c₀ * Cm)⁻¹) +
      (K1 ^ (1 + σw) * K1 ^ (q * (1 + σw)) * Cρ) + (Cρ * K1 ^ (1 + ocC α q + tT) * Cρ) :=
    ⟨_, rfl⟩
  have hp1 : 0 < K1 ^ (1 + σw) := Real.rpow_pos_of_pos hK1p _
  have hp2 : 0 < K1 ^ (q * (1 + σw)) := Real.rpow_pos_of_pos hK1p _
  have hp3 : 0 < K1 ^ (1 + ocC α q + tT) := Real.rpow_pos_of_pos hK1p _
  have hinvp : 0 < (c₀ * Cm)⁻¹ := inv_pos.2 hmul1
  have hCfp : 0 < Cf := by rw [hCfdef]; positivity
  refine ⟨Cf, hCfp, fun M hM κ hκ => ?_⟩
  have hE0 := AVRegularity.Scales.epsilon_basic (m := M - 1) hq.1 h128
  have hY0 := AVRegularity.Scales.epsilon_basic (m := M - 1 - 1) hq.1 h128
  have hx0 := AVRegularity.Scales.epsilon_basic (m := M) hq.1 h128
  have hB0 : 0 < κ (M - 1) := bandChain_pos hΛpos hζ hκ (by omega)
  have hB20 : 0 < κ (M - 1 - 1) := bandChain_pos hΛpos hζ hκ (by omega)
  have hh0 : 0 < ocTauPP α q Λ M := AVRegularity.Construction.Stream.ocTauPP_pos hΛpos
  have hh10 : 0 < ocTauPP α q Λ (M - 1) := AVRegularity.Construction.Stream.ocTauPP_pos hΛpos
  have hx : ocEpsilon q Λ M ≤ K1 * ocEpsilon q Λ (M - 1) ^ q := by
    have := (h1 Λ M hΛ1 (by omega)).2
    simpa using this
  have hEY : ocEpsilon q Λ (M - 1) ≤ K1 * ocEpsilon q Λ (M - 1 - 1) ^ q := by
    have := (h1 Λ (M - 1) hΛ1 (by omega)).2
    simpa using this
  have hB := hi Λ hΛi M (by omega) κ hκ (M - 1) (by omega) (by omega)
  have hB2 := hi Λ hΛi M (by omega) κ hκ (M - 1 - 1) (by omega) (by omega)
  have hhM := ocTauPP_asymp hα0 hα1 hs0 hs1 hq h128 (m := M)
  have hhM1 := ocTauPP_asymp hα0 hα1 hs0 hs1 hq h128 (m := M - 1)
  have hρ := rho_asymp (α := α) (q := q) hE0.1 hCip (by positivity) hcr hB hhM
  have hρn := rho_asymp (α := α) (q := q) hY0.1 hCip (by positivity) hcr hB2 hhM1
  set E := ocEpsilon q Λ (M - 1) with hEd
  set Y := ocEpsilon q Λ (M - 1 - 1) with hYd
  set x := ocEpsilon q Λ M with hxd
  have hEn : ∀ r : ℝ, 0 ≤ E ^ r := fun r => Real.rpow_nonneg hE0.1.le r
  have hYn : ∀ r : ℝ, 0 ≤ Y ^ r := fun r => Real.rpow_nonneg hY0.1.le r
  have hid := prepared_radius_exponent_identity (α := α) hq.1
  have hcdef : ocC α q = ocGamma α q / 2 + ocDelta α q := rfl
  -- molecular radius lower bound
  have hA : ocA α q Λ (M - 1) = E ^ ((1 + α) - 2) := rfl
  have hApos : 0 < ocA α q Λ (M - 1) := by rw [hA]; exact Real.rpow_pos_of_pos hE0.1 _
  have hAas : ocAsymp 1 (ocA α q Λ (M - 1)) (E ^ ((1 + α) - 2)) := by
    rw [hA]; exact asymp_one_self _
  have hBA := aPow_div hE0.1 hCip one_pos hApos hB hAas
  have hS := aPow_sqrt hE0.1 (by positivity) hBA
  have hS' : ocAsymp (Real.sqrt (Ci * 1)) (Real.sqrt (κ (M - 1) / ocA α q Λ (M - 1)))
      (E ^ (1 + ocGamma α q / 2)) := aPow_congr (by ring) hS
  have hEw : E ^ (1 + ocGamma α q / 2) ≤ E := by
    have := Real.rpow_le_rpow_of_exponent_ge hE0.1 hE0.2.1
      (show (1 : ℝ) ≤ 1 + ocGamma α q / 2 by linarith)
    simpa using this
  have hmin : Cm * E ^ (1 + ocGamma α q / 2) ≤
      min E (Real.sqrt (κ (M - 1) / ocA α q Λ (M - 1))) := by
    refine le_min ?_ ?_
    · have hC1 : Cm ≤ 1 := min_le_right _ _
      calc Cm * E ^ (1 + ocGamma α q / 2) ≤ 1 * E ^ (1 + ocGamma α q / 2) :=
            mul_le_mul_of_nonneg_right hC1 (hEn _)
        _ ≤ E := by rw [one_mul]; exact hEw
    · have hC1 : Cm ≤ (Real.sqrt (Ci * 1))⁻¹ := min_le_left _ _
      exact (mul_le_mul_of_nonneg_right hC1 (hEn _)).trans hS'.1
  have hρs : (((c₀ * Cm)⁻¹)⁻¹) * E ^ (1 + ocGamma α q / 2) ≤
      c₀ * min E (Real.sqrt (κ (M - 1) / ocA α q Λ (M - 1))) := by
    rw [inv_inv]
    calc c₀ * Cm * E ^ (1 + ocGamma α q / 2) = c₀ * (Cm * E ^ (1 + ocGamma α q / 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmin hc₀.le
  have hρs0 : 0 < c₀ * min E (Real.sqrt (κ (M - 1) / ocA α q Λ (M - 1))) := by
    refine mul_pos hc₀ (lt_min hE0.1 (Real.sqrt_pos.2 (div_pos hB0 hApos)))
  -- numerators
  have hxσ : x ^ (1 + σw) ≤ K1 ^ (1 + σw) * E ^ (q * (1 + σw)) :=
    pow_bound hE0.1.le hK1p.le hx0.1.le hx (by linarith)
  have t2 : 0 < Cρ * (c₀ * Cm)⁻¹ := mul_pos hCρp hinvp
  have t3 : 0 < K1 ^ (1 + σw) * K1 ^ (q * (1 + σw)) * Cρ := by positivity
  have t4 : 0 < Cρ * K1 ^ (1 + ocC α q + tT) * Cρ := by positivity
  have t1 : 0 < K1 ^ (1 + σw) * (c₀ * Cm)⁻¹ := mul_pos hp1 hinvp
  have hww : ∀ r : ℝ, E ^ r / E ^ (1 + ocGamma α q / 2) = E ^ (r - (1 + ocGamma α q / 2)) :=
    fun r => (Real.rpow_sub hE0.1 _ _).symm
  have hρpos : 0 < cr * Real.sqrt (κ (M - 1 - 1) * ocTauPP α q Λ (M - 1)) :=
    mul_pos hcr (Real.sqrt_pos.2 (mul_pos hB20 hh10))
  -- (1)
  have hq1 := quotient_upper_bound hp1 hinvp (hEn (q * (1 + σw)))
    (Real.rpow_pos_of_pos hE0.1 (1 + ocGamma α q / 2)) hρs0 hxσ hρs
  have e1 : E ^ (q * (1 + σw)) / E ^ (1 + ocGamma α q / 2) =
      E ^ (q * ocGamma α q + 4 * ocDelta α q + q * σw) := by
    rw [hww]; congr 1; rw [hcdef] at hid; linarith [hid]
  rw [e1] at hq1
  -- (2)
  have hn2 : cr * Real.sqrt (κ (M - 1) * ocTauPP α q Λ M) * E ^ tT ≤
      Cρ * E ^ ((1 + ocC α q) + tT) := by
    rw [Real.rpow_add hE0.1, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hρ.2 (hEn _)
  have hq2 := quotient_upper_bound hCρp hinvp (hEn ((1 + ocC α q) + tT))
    (Real.rpow_pos_of_pos hE0.1 (1 + ocGamma α q / 2)) hρs0 hn2 hρs
  have e2 : E ^ ((1 + ocC α q) + tT) / E ^ (1 + ocGamma α q / 2) =
      E ^ (ocDelta α q + tT) := by
    rw [hww]; congr 1; rw [hcdef]; ring
  rw [e2] at hq2
  -- (3)
  have hEq : E ^ (q * (1 + σw)) ≤ K1 ^ (q * (1 + σw)) * Y ^ (q * (q * (1 + σw))) :=
    pow_bound hY0.1.le hK1p.le hE0.1.le hEY (mul_nonneg (by linarith [hq.1]) (by linarith))
  have hn3 : x ^ (1 + σw) ≤
      (K1 ^ (1 + σw) * K1 ^ (q * (1 + σw))) * Y ^ (q * (q * (1 + σw))) := by
    rw [mul_assoc]
    exact hxσ.trans (mul_le_mul_of_nonneg_left hEq hp1.le)
  have hq3 := quotient_upper_bound (by positivity) hCρp (hYn (q * (q * (1 + σw))))
    (Real.rpow_pos_of_pos hY0.1 (1 + ocC α q)) hρpos hn3 hρn.1
  have e3 : Y ^ (q * (q * (1 + σw))) / Y ^ (1 + ocC α q) =
      Y ^ (q ^ 2 * (1 + σw) - 1 - ocC α q) := by
    rw [← Real.rpow_sub hY0.1]; congr 1; ring
  rw [e3] at hq3
  -- (4)
  have hEr : E ^ ((1 + ocC α q) + tT) ≤
      K1 ^ ((1 + ocC α q) + tT) * Y ^ (q * ((1 + ocC α q) + tT)) :=
    pow_bound hY0.1.le hK1p.le hE0.1.le hEY (by rw [hcdef]; linarith)
  have hn4 : cr * Real.sqrt (κ (M - 1) * ocTauPP α q Λ M) * E ^ tT ≤
      (Cρ * K1 ^ ((1 + ocC α q) + tT)) * Y ^ (q * ((1 + ocC α q) + tT)) := by
    exact hn2.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hEr hCρp.le)
  have hq4 := quotient_upper_bound (by positivity) hCρp (hYn (q * ((1 + ocC α q) + tT)))
    (Real.rpow_pos_of_pos hY0.1 (1 + ocC α q)) hρpos hn4 hρn.1
  have e4 : Y ^ (q * ((1 + ocC α q) + tT)) / Y ^ (1 + ocC α q) =
      Y ^ (q * (1 + ocC α q + tT) - 1 - ocC α q) := by
    rw [← Real.rpow_sub hY0.1]; congr 1; ring
  rw [e4] at hq4
  refine ⟨hq1.trans ?_, hq2.trans ?_, hq3.trans ?_, hq4.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right (by rw [hCfdef]; linarith) (hEn _)
  · exact mul_le_mul_of_nonneg_right (by rw [hCfdef]; linarith) (hEn _)
  · exact mul_le_mul_of_nonneg_right (by rw [hCfdef]; linarith) (hYn _)
  · exact mul_le_mul_of_nonneg_right (by rw [hCfdef]; linarith) (hYn _)
end

/-! The terminal scale ledger (the scales of Lemma 14.1(b) of the paper) in plain real
variables: the diffusivity chain `κ` enters only through `ν = κ_M` and `B = κ_{M-1}`. -/

section
open AVRegularity.CycleReference

theorem terminal_scales_core {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ cr : ℝ, 0 < cr →
    ∃ (C : ℝ) (M₀ : ℕ), 1 ≤ C ∧ ∀ M : ℕ, M₀ ≤ M → ∀ κ : ℕ → ℝ,
      IsOCBandChain α q Λ ζ M κ →
      1 ≤ κ (M - 1) / κ M ∧ κ (M - 1) / κ M ≤ 2 ∧
      ocEpsilon q Λ M ^ (1 + α) / κ M ≤ C * ocEpsilon q Λ M ^ ocGamma α q ∧
      C⁻¹ * ocEpsilon q Λ (M - 1) ^ ocC α q ≤
        cr * Real.sqrt (κ (M - 1) * ocTauPP α q Λ M) / ocEpsilon q Λ (M - 1) ∧
      cr * Real.sqrt (κ (M - 1) * ocTauPP α q Λ M) / ocEpsilon q Λ (M - 1) ≤
        C * ocEpsilon q Λ (M - 1) ^ ocC α q ∧
      C⁻¹ * ocEpsilon q Λ (M - 1) ^ (q * ocGamma α q + 3 * ocDelta α q) ≤
        ocEpsilon q Λ M * Real.sqrt (κ (M - 1) / κ M) /
          (cr * Real.sqrt (κ (M - 1) * ocTauPP α q Λ M)) ∧
      ocEpsilon q Λ M * Real.sqrt (κ (M - 1) / κ M) /
          (cr * Real.sqrt (κ (M - 1) * ocTauPP α q Λ M)) ≤
        C * ocEpsilon q Λ (M - 1) ^ (q * ocGamma α q + 3 * ocDelta α q) ∧
      ocA α q Λ (M - 1) * ocTauPP α q Λ M ≤ C * ocEpsilon q Λ (M - 1) ^ (2 * ocDelta α q) ∧
      C⁻¹ * ocEpsilon q Λ (M - 1) ^ (-(2 * (q * ocGamma α q + 3 * ocDelta α q))) ≤
        ocTauPP α q Λ M / (ocEpsilon q Λ M ^ 2 / κ M) ∧
      ocTauPP α q Λ M / (ocEpsilon q Λ M ^ 2 / κ M) ≤
        C * ocEpsilon q Λ (M - 1) ^ (-(2 * (q * ocGamma α q + 3 * ocDelta α q))) ∧
      C⁻¹ * ocEpsilon q Λ (M - 1) ^ (-(2 * q * ocGamma α q + 4 * ocDelta α q)) ≤
        ocTau α q Λ M / (ocEpsilon q Λ M ^ 2 / κ M) := by
  obtain ⟨Λr, hΛr, hr⟩ := terminal_ratio_le_two hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨K, hK, Λc, hΛc, hc⟩ := terminal_comparisons hα0 hα1 hs0 hs1 hq
  have hγ := (AVRegularity.Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq).1
  have hδ := (AVRegularity.Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq).2.1
  have hKp : 0 < K := by linarith
  refine ⟨max Λr Λc, hΛr.trans (le_max_left _ _), fun Λ hΛ cr hcr => ?_⟩
  have hΛ1 : Λr ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛ2 : Λc ≤ Λ := (le_max_right _ _).trans hΛ
  have h128 : 128 ≤ Λ := hΛc.trans hΛ2
  have hΛpos : 1 ≤ Λ := by omega
  obtain ⟨M₁, hM₁, hr'⟩ := hr Λ hΛ1
  have hcrm : 0 < max cr cr⁻¹ := lt_max_of_lt_left hcr
  have hsq : 0 < Real.sqrt (2 * K * K) := Real.sqrt_pos.2 (by positivity)
  have hCr : 0 < Real.sqrt (2 * K * K) * max cr cr⁻¹ := mul_pos hsq hcrm
  obtain ⟨Cr, hCrdef⟩ : ∃ Cr : ℝ, Cr = Real.sqrt (2 * K * K) * max cr cr⁻¹ := ⟨_, rfl⟩
  rw [← hCrdef] at hCr
  obtain ⟨Cf, hCfdef⟩ : ∃ Cf : ℝ, Cf =
      2 * K + Cr * 1 + 2 * K * Cr + K * (K * K * K) + K * (K * K * K) + 3 :=
    ⟨_, rfl⟩
  have p1 : 0 < 2 * K := by positivity
  have p2 : 0 < Cr * 1 := by positivity
  have p3 : 0 < 2 * K * Cr := by positivity
  have p4 : 0 < K * (K * K * K) := by positivity
  have hCf1 : 1 ≤ Cf := by rw [hCfdef]; linarith
  have lift : ∀ {C' x X : ℝ}, 0 < C' → C' ≤ Cf → 0 ≤ X → ocAsymp C' x X → ocAsymp Cf x X :=
    fun h1 h2 hX h => asymp_mono_constant h1 h2 hX h
  refine ⟨Cf, M₁, hCf1, fun M hM κ hκ => ?_⟩
  have hM2 : 2 ≤ M := hM₁.trans hM
  have hν0 : 0 < κ M := bandChain_pos hΛpos hζ hκ (le_refl M)
  have hB0 : 0 < κ (M - 1) := bandChain_pos hΛpos hζ hκ (by omega)
  obtain ⟨hlo, hhi⟩ := hr' M hM κ hκ
  have hband := hκ.1
  obtain ⟨hν', hx, hh, hτ⟩ := hc Λ hΛ2 M hM2 (κ M) hband
  have hx0 := AVRegularity.Scales.epsilon_basic (m := M) hq.1 h128
  have hE0 := AVRegularity.Scales.epsilon_basic (m := M - 1) hq.1 h128
  have hhpos : 0 < ocTauPP α q Λ M := AVRegularity.Construction.Stream.ocTauPP_pos hΛpos
  have hτpos : 0 < ocTau α q Λ M := AVRegularity.Construction.Stream.ocTau_pos hΛpos
  set E := ocEpsilon q Λ (M - 1) with hEd
  set x := ocEpsilon q Λ M with hxd
  set ν := κ M with hνd
  set B := κ (M - 1) with hBd
  set h := ocTauPP α q Λ M with hhd
  have hEn : ∀ r : ℝ, 0 ≤ E ^ r := fun r => Real.rpow_nonneg hE0.1.le r
  have hratio1 : 1 ≤ B / ν := by rw [le_div_iff₀ hν0]; linarith
  have hratio2 : B / ν ≤ 2 := by rw [div_le_iff₀ hν0]; linarith
  -- identities between exponents
  have hid := prepared_radius_exponent_identity (α := α) hq.1
  have hcdef : ocC α q = ocGamma α q / 2 + ocDelta α q := rfl
  -- B comparison
  have hBas : ocAsymp (2 * K) B (E ^ ((1 + α) + ocGamma α q)) :=
    asymp_sandwich hK (hEn _) hlo hhi hν'
  -- radius
  have hBh : ocAsymp (2 * K * K) (B * h)
      (E ^ (((1 + α) + ocGamma α q) + (2 - (1 + α) + 2 * ocDelta α q))) :=
    aPow_mul hE0.1 (by positivity) hKp hBas hh
  have hsqrt := aPow_sqrt hE0.1 (by positivity) hBh
  have hsqrt' : ocAsymp (Real.sqrt (2 * K * K)) (Real.sqrt (B * h)) (E ^ (1 + ocC α q)) :=
    aPow_congr (by rw [hcdef]; ring) hsqrt
  have hρ : ocAsymp Cr (cr * Real.sqrt (B * h)) (E ^ (1 + ocC α q)) := by
    rw [hCrdef]; exact aPow_const_mul hsq hcr (hEn _) hsqrt'
  have hρpos : 0 < cr * Real.sqrt (B * h) := mul_pos hcr (Real.sqrt_pos.2 (mul_pos hB0 hhpos))
  have hE1 : ocAsymp 1 E (E ^ (1 : ℝ)) := by rw [Real.rpow_one]; exact asymp_one_self E
  have hρE : ocAsymp (Cr * 1) (cr * Real.sqrt (B * h) / E) (E ^ ((1 + ocC α q) - 1)) :=
    aPow_div hE0.1 hCr one_pos hE0.1 hρ hE1
  have hρE' : ocAsymp (Cr * 1) (cr * Real.sqrt (B * h) / E) (E ^ ocC α q) :=
    aPow_congr (by ring) hρE
  -- cell ratio
  have hd : ocAsymp 2 (x * Real.sqrt (B / ν)) x := by
    have h1 : 1 ≤ Real.sqrt (B / ν) := Real.one_le_sqrt.2 hratio1
    have h2 : Real.sqrt (B / ν) ≤ 2 :=
      Real.sqrt_le_iff.2 ⟨by norm_num, by nlinarith⟩
    constructor
    · nlinarith [hx0.1]
    · nlinarith [hx0.1]
  have hdE : ocAsymp (2 * K) (x * Real.sqrt (B / ν)) (E ^ q) := asymp_trans (by norm_num) hKp hd hx
  have hcell : ocAsymp (2 * K * Cr) (x * Real.sqrt (B / ν) / (cr * Real.sqrt (B * h)))
      (E ^ (q - (1 + ocC α q))) := aPow_div hE0.1 (by positivity) (by positivity) hρpos hdE hρ
  have hcell' : ocAsymp (2 * K * Cr) (x * Real.sqrt (B / ν) / (cr * Real.sqrt (B * h)))
      (E ^ (q * ocGamma α q + 3 * ocDelta α q)) :=
    aPow_congr (by linarith [hid]) hcell
  -- cell length
  have hxx : ocAsymp (K * K) (x * x) (E ^ (q + q)) := aPow_mul hE0.1 hKp hKp hx hx
  have hν0' : 0 < ν := hν0
  have hell : ocAsymp (K * K * K) (x ^ 2 / ν) (E ^ ((q + q) - ((1 + α) + ocGamma α q))) := by
    rw [sq]; exact aPow_div hE0.1 (by positivity) hKp hν0 hxx hν'
  have hellpos : 0 < x ^ 2 / ν := div_pos (pow_pos hx0.1 2) hν0
  have hhl : ocAsymp (K * (K * K * K)) (h / (x ^ 2 / ν))
      (E ^ ((2 - (1 + α) + 2 * ocDelta α q) - ((q + q) - ((1 + α) + ocGamma α q)))) :=
    aPow_div hE0.1 hKp (by positivity) hellpos hh hell
  have hhl' : ocAsymp (K * (K * K * K)) (h / (x ^ 2 / ν))
      (E ^ (-(2 * (q * ocGamma α q + 3 * ocDelta α q)))) :=
    aPow_congr (by rw [hcdef] at hid; linarith [hid]) hhl
  have hτl : ocAsymp (K * (K * K * K)) (ocTau α q Λ M / (x ^ 2 / ν))
      (E ^ ((2 - (1 + α) + 4 * ocDelta α q) - ((q + q) - ((1 + α) + ocGamma α q)))) :=
    aPow_div hE0.1 hKp (by positivity) hellpos hτ hell
  have hτl' : ocAsymp (K * (K * K * K)) (ocTau α q Λ M / (x ^ 2 / ν))
      (E ^ (-(2 * q * ocGamma α q + 4 * ocDelta α q))) :=
    aPow_congr (by rw [hcdef] at hid; linarith [hid]) hτl
  -- Péclet
  have hPe : x ^ (1 + α) / ν ≤ Cf * x ^ ocGamma α q := by
    have hl : x ^ ((1 + α) - ocGamma α q) / 2 ≤ ν := hband.1
    have hp : 0 < x ^ ((1 + α) - ocGamma α q) := Real.rpow_pos_of_pos hx0.1 _
    have hg : 0 < x ^ ocGamma α q := Real.rpow_pos_of_pos hx0.1 _
    have hsplit : x ^ (1 + α) = x ^ ((1 + α) - ocGamma α q) * x ^ ocGamma α q := by
      rw [← Real.rpow_add hx0.1]; congr 1; ring
    rw [div_le_iff₀ hν0, hsplit]
    have hc : 2 ≤ Cf := by rw [hCfdef]; linarith
    have h2 : x ^ ((1 + α) - ocGamma α q) ≤ 2 * ν := by linarith
    calc x ^ ((1 + α) - ocGamma α q) * x ^ ocGamma α q ≤ (2 * ν) * x ^ ocGamma α q :=
          mul_le_mul_of_nonneg_right h2 hg.le
      _ ≤ (Cf * ν) * x ^ ocGamma α q :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hν0.le) hg.le
      _ = Cf * x ^ ocGamma α q * ν := by ring
  -- time-product
  have hgt := (AVRegularity.Scales.admissible_time_scale_facts hα0 hα1 hs0 hs1 hq h128
    (by omega : 1 ≤ M)).2.2.2.2.1
  have hAh : ocA α q Λ (M - 1) * h ≤ Cf * E ^ (2 * ocDelta α q) := by
    refine hgt.trans ?_
    have h25 : (2 : ℝ) ^ (-25 : ℤ) ≤ 1 := by norm_num
    exact mul_le_mul (h25.trans hCf1) (le_refl _) (hEn _) (by linarith)
  have L : ∀ {C' x' X' : ℝ}, 0 < C' → C' ≤ Cf → 0 ≤ X' → ocAsymp C' x' X' → ocAsymp Cf x' X' :=
    fun h1 h2 hX h => lift h1 h2 hX h
  have f1 := L (by positivity) (by rw [hCfdef]; linarith) (hEn _) hρE'
  have f2 := L (by positivity) (by rw [hCfdef]; linarith) (hEn _) hcell'
  have f3 := L (by positivity) (by rw [hCfdef]; linarith) (hEn _) hhl'
  have f4 := L (by positivity) (by rw [hCfdef]; linarith) (hEn _) hτl'
  exact ⟨hratio1, hratio2, hPe, f1.1, f1.2, f2.1, f2.2, hAh, f3.1, f3.2, f4.1⟩
end

end AVRegularity.EntryScales
end
