-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleReference.TransitionZero
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Definitions.CycleReference.OcRefCorrector
public import AVRegularity.Definitions.CycleReference.OcAsymp
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.OcA
public import AVRegularity.Statements.Intermediate.CycleReference.OcMaterialMetric
public import AVRegularity.Statements.Intermediate.CycleReference.OcTransition
import AVRegularity.Velocity.Port.MaterialGoalSource
import AVenhance.Infra.Flow.JointSmoothFromFixedStart
import AVenhance.Infra.Construction.StreamAdmissible
import AVenhance.Infra.Flow.Laws
import AVenhance.Infra.Flow.SmoothField
import AVenhance.Statements.FlowDefs.FlowIsFlow
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.Monotonicity.Lemmas

section
@[expose] public section

section
open scoped BigOperators
namespace AVRegularity.CycleReference

/-! A common separation threshold for all weighted recurrence errors. -/

theorem exists_recurrence_error_budget {q γ δ A D : ℝ}
    (hq : 1 < q) (hγ : 0 < γ) (hδ : 0 < δ) (hA : 0 ≤ A) (hD : 0 ≤ D) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      (∀ N : ℕ, ∑ k ∈ Finset.range N,
        16 * (A * ocEpsilon q Λ (k + 1) + ocEpsilon q Λ (k + 2) ^ (2 * γ) +
          D * ocEpsilon q Λ (k + 1) ^ δ) ≤ 1 / 2) ∧
      (∀ m : ℕ, 2 ≤ m → A * ocEpsilon q Λ (m - 1) ≤ 1 / 2 ∧
        D * ocEpsilon q Λ (m - 1) ^ δ ≤ 1 / 2) := by
  let S := A + D + 1
  have hS : 0 < S := by dsimp [S]; linarith
  let η := 1 / (64 * S)
  have hη : 0 < η := by dsimp [η]; positivity
  have hcancel : S * η = 1 / 64 := by dsimp [η]; field_simp
  obtain ⟨L1, hL1, hb1⟩ := exists_small_scale_error_budget hq (by norm_num : (0 : ℝ) < 1) hη
  obtain ⟨Lg, hLg, hbg⟩ := exists_small_scale_error_budget hq (show 0 < 2 * γ by linarith) hη
  obtain ⟨Ld, hLd, hbd⟩ := exists_small_scale_error_budget hq hδ hη
  refine ⟨max L1 (max Lg Ld), hL1.trans (le_max_left _ _), ?_⟩
  intro Λ hΛ
  have hΛ1 : L1 ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛg : Lg ≤ Λ := (le_max_left _ _).trans ((le_max_right _ _).trans hΛ)
  have hΛd : Ld ≤ Λ := (le_max_right _ _).trans ((le_max_right _ _).trans hΛ)
  have h128 : 128 ≤ Λ := hL1.trans hΛ1
  obtain ⟨hs1, ht1⟩ := hb1 Λ hΛ1
  obtain ⟨hsg, htg⟩ := hbg Λ hΛg
  obtain ⟨hsd, htd⟩ := hbd Λ hΛd
  have hfinite {p : ℝ} (hs : Summable (fun k : ℕ => ocEpsilon q Λ (k + 1) ^ p))
      (ht : ∑' k : ℕ, ocEpsilon q Λ (k + 1) ^ p ≤ η) (N : ℕ) :
      ∑ k ∈ Finset.range N, ocEpsilon q Λ (k + 1) ^ p ≤ η :=
    (hs.sum_le_tsum _ (fun k _ => Real.rpow_nonneg
      (AVRegularity.Scales.epsilon_basic hq h128).1.le _)).trans ht
  constructor
  · intro N
    have hf1 : ∑ k ∈ Finset.range N, ocEpsilon q Λ (k + 1) ≤ η := by
      simpa only [Real.rpow_one] using hfinite hs1 ht1 N
    have hfg : ∑ k ∈ Finset.range N, ocEpsilon q Λ (k + 2) ^ (2 * γ) ≤ η := by
      apply le_trans (Finset.sum_le_sum (fun k _ => ?_)) (hfinite hsg htg N)
      exact Real.rpow_le_rpow (AVRegularity.Scales.epsilon_basic hq h128).1.le
        (by simpa only [Nat.add_assoc] using epsilon_succ_le (n := k + 1) hq h128)
        (by linarith)
    have hfd := hfinite hsd htd N
    rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum]
    have hsum : A * (∑ k ∈ Finset.range N, ocEpsilon q Λ (k + 1)) +
        (∑ k ∈ Finset.range N, ocEpsilon q Λ (k + 2) ^ (2 * γ)) +
          D * (∑ k ∈ Finset.range N, ocEpsilon q Λ (k + 1) ^ δ) ≤ S * η := by
      have h := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hf1 hA) hfg)
        (mul_le_mul_of_nonneg_left hfd hD)
      convert h using 1; dsimp [S]; ring
    have h := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 16)
    rw [hcancel] at h
    norm_num at h
    nlinarith only [h]
  · intro m hm
    have hE : ocEpsilon q Λ (m - 1) ≤ η := by
      have h := (epsilon_power_le_tail (m := m - 1) hq (by norm_num : (0 : ℝ) < 1) h128 (by omega)).trans ht1
      simpa only [Real.rpow_one] using h
    have hEd := (epsilon_power_le_tail (m := m - 1) hq hδ h128 (by omega)).trans htd
    have hA' : A ≤ S := by dsimp [S]; linarith
    have hD' : D ≤ S := by dsimp [S]; linarith
    have h1 := (mul_le_mul_of_nonneg_left hE hA).trans (mul_le_mul_of_nonneg_right hA' hη.le)
    have h2 := (mul_le_mul_of_nonneg_left hEd hD).trans (mul_le_mul_of_nonneg_right hD' hη.le)
    rw [hcancel] at h1 h2
    constructor <;> linarith

end AVRegularity.CycleReference
end

section
open Filter Topology
namespace AVRegularity.CycleReference

/-! At fixed separation the parent wavelength tends to zero, and exponential memory beats powers. -/

theorem epsilon_parent_tendsto_zero {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ) :
    Tendsto (fun m : ℕ => ocEpsilon q Λ (m - 1)) atTop (𝓝 0) := by
  have hs := (epsilon_tail_separation_bound hq (by norm_num : (0 : ℝ) < 1) hΛ).1
  have ht : Tendsto (fun n : ℕ => ocEpsilon q Λ (n + 1)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using hs.tendsto_atTop_zero
  have hsub : Tendsto (fun m : ℕ => m - 2) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (b + 2)] with m hm
    omega
  have h := ht.comp hsub
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with m hm
  change ocEpsilon q Λ (m - 2 + 1) = ocEpsilon q Λ (m - 1)
  congr 1
  omega

theorem exponential_small_scale_eventually {e : ℕ → ℝ}
    (he : ∀ m, 0 < e m) (ht : Tendsto e atTop (𝓝 0))
    (A N C b p : ℝ) (hb : 0 < b) (hp : 0 < p) :
    ∀ᶠ m : ℕ in atTop,
      C * (e m) ^ (-A) * Real.exp (-b * (e m) ^ (-p)) ≤ (e m) ^ N := by
  have hinv : Tendsto (fun m => (e m)⁻¹) atTop atTop :=
    (tendsto_inv_nhdsGT_zero).comp (tendsto_nhdsWithin_iff.mpr ⟨ht,
      Filter.Eventually.of_forall (fun m => he m)⟩)
  have hpow : Tendsto (fun m => (e m) ^ (-p)) atTop atTop := by
    have h := (tendsto_rpow_atTop hp).comp hinv
    apply h.congr
    intro m
    simp only [Function.comp_def, Real.inv_rpow (he m).le, Real.rpow_neg (he m).le]
  have hdec := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((A + N) / p) b hb).comp hpow
  have htC := (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).mul hdec
  have htC' : Tendsto (fun m => C * (((e m) ^ (-p)) ^ ((A + N) / p) *
      Real.exp (-b * (e m) ^ (-p)))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using htC
  have hnear : ∀ᶠ m : ℕ in atTop,
      C * (((e m) ^ (-p)) ^ ((A + N) / p) * Real.exp (-b * (e m) ^ (-p))) ≤ 1 :=
    htC'.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hnear] with m hm
  have hid : ((e m) ^ (-p)) ^ ((A + N) / p) = (e m) ^ (-A - N) := by
    rw [← Real.rpow_mul (he m).le]
    congr 1
    field_simp
    ring
  rw [hid] at hm
  have hm' := mul_le_mul_of_nonneg_right hm (Real.rpow_pos_of_pos (he m) N).le
  have heq : C * ((e m) ^ (-A - N) * Real.exp (-b * (e m) ^ (-p))) * (e m) ^ N =
      C * (e m) ^ (-A) * Real.exp (-b * (e m) ^ (-p)) := by
    rw [show C * ((e m) ^ (-A - N) * Real.exp (-b * (e m) ^ (-p))) * (e m) ^ N =
      C * ((e m) ^ (-A - N) * (e m) ^ N) * Real.exp (-b * (e m) ^ (-p)) by ring,
      ← Real.rpow_add (he m)]
    congr 3
    ring
  simpa only [heq, one_mul] using hm'

end AVRegularity.CycleReference
end

section
namespace AVRegularity.CycleReference

/-! Summable relative rounding errors for the actual construction wavelengths. -/

theorem epsilon_q_ratio_error {q : ℝ} (hq : 1 < q) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Λ m : ℕ, 128 ≤ Λ → 2 ≤ m →
      |ocEpsilon q Λ m / ocEpsilon q Λ (m - 1) ^ q - 1| ≤
        K * ocEpsilon q Λ (m - 1) := by
  obtain ⟨K, hK, hb⟩ := rounded_power_ratio_near_one hq.le
  refine ⟨K, hK, ?_⟩
  intro Λ m hΛ hm
  let j := m - 1
  let x : ℝ := (Λ : ℝ) ^ (q ^ j / (q - 1))
  have hj : 0 < j := by dsimp [j]; omega
  have hΛone : 1 ≤ (Λ : ℝ) := by exact_mod_cast (by omega : 1 ≤ Λ)
  have hΛpos : 0 < (Λ : ℝ) := by exact_mod_cast (by omega : 0 < Λ)
  have hx : 1 ≤ x := by
    dsimp [x]
    apply Real.one_le_rpow hΛone
    positivity
  have hxpos : 0 < x := by linarith
  have hApos : 0 < (⌈x⌉₊ : ℝ) := hxpos.trans_le (Nat.le_ceil x)
  have hxp : 0 < x ^ q := Real.rpow_pos_of_pos hxpos q
  have hBpos : 0 < (⌈x ^ q⌉₊ : ℝ) := hxp.trans_le (Nat.le_ceil _)
  have hraw : (Λ : ℝ) ^ (q ^ m / (q - 1)) = x ^ q := by
    dsimp [x]
    rw [← Real.rpow_mul hΛpos.le]
    have hmj : m = j + 1 := by dsimp [j]; omega
    rw [hmj, pow_succ]
    congr 1
    ring
  have hprev : ocEpsilon q Λ (m - 1) = (⌈x⌉₊ : ℝ)⁻¹ := by
    simp only [ocEpsilon, show m - 1 ≠ 0 by omega, ite_false]
    rfl
  have hnext : ocEpsilon q Λ m = (⌈x ^ q⌉₊ : ℝ)⁻¹ := by
    simp only [ocEpsilon, show m ≠ 0 by omega, ite_false, hraw]
  rw [hprev, hnext, Real.inv_rpow hApos.le]
  have heq : (⌈x ^ q⌉₊ : ℝ)⁻¹ / ((⌈x⌉₊ : ℝ) ^ q)⁻¹ =
      (⌈x⌉₊ : ℝ) ^ q / (⌈x ^ q⌉₊ : ℝ) := by simp only [div_eq_mul_inv, inv_inv, mul_comm]
  rw [heq]
  simpa only [div_eq_mul_inv] using hb x hx

/-! Uniform positive-interval control of the wavelength ratio and its real powers. -/

theorem epsilon_le_inv_separation {q : ℝ} {Λ m : ℕ}
    (hq : 1 < q) (hΛ : 128 ≤ Λ) (hm : 1 ≤ m) :
    ocEpsilon q Λ m ≤ (Λ : ℝ)⁻¹ := by
  have he := (AVRegularity.Scales.epsilon_basic (m := m) hq hΛ).1
  have hprev := (AVRegularity.Scales.epsilon_basic (m := m - 1) hq hΛ).2.1
  have h := AVRegularity.Scales.epsilon_ratio_lower hq hΛ hm
  have hΛpos : 0 < (Λ : ℝ) := by exact_mod_cast (by omega : 0 < Λ)
  have hmul := (le_div_iff₀ he).1 h
  rw [inv_eq_one_div]
  apply (le_div_iff₀ hΛpos).2
  nlinarith

theorem epsilon_q_ratio_power_error {q : ℝ} (hq : 1 < q) (p : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ m : ℕ, Λ₀ ≤ Λ → 2 ≤ m →
      1 / 2 ≤ ocEpsilon q Λ m / ocEpsilon q Λ (m - 1) ^ q ∧
      ocEpsilon q Λ m / ocEpsilon q Λ (m - 1) ^ q ≤ 2 ∧
      |(ocEpsilon q Λ m / ocEpsilon q Λ (m - 1) ^ q) ^ p - 1| ≤
        K * ocEpsilon q Λ (m - 1) := by
  obtain ⟨Kq, hKq, hqerr⟩ := epsilon_q_ratio_error hq
  obtain ⟨Kp, hKp, hp⟩ := rpow_near_one_bound p
  obtain ⟨L, hL⟩ := exists_nat_gt (2 * Kq)
  refine ⟨Kp * Kq, mul_nonneg hKp hKq, max 128 L, le_max_left _ _, ?_⟩
  intro Λ m hΛ hm
  have h128 : 128 ≤ Λ := (le_max_left _ _).trans hΛ
  have hLΛ : (L : ℝ) ≤ Λ := by exact_mod_cast ((le_max_right _ _).trans hΛ)
  have hΛpos : 0 < (Λ : ℝ) := by exact_mod_cast (by omega : 0 < Λ)
  have hE := epsilon_le_inv_separation hq h128 (show 1 ≤ m - 1 by omega)
  have hsmall : Kq * ocEpsilon q Λ (m - 1) ≤ 1 / 2 := by
    apply (mul_le_mul_of_nonneg_left hE hKq).trans
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ hΛpos).2
    linarith
  have herr := hqerr Λ m h128 hm
  have hhalf : 1 / 2 ≤ ocEpsilon q Λ m / ocEpsilon q Λ (m - 1) ^ q := by
    linarith [(abs_le.mp herr).1]
  have htwo : ocEpsilon q Λ m / ocEpsilon q Λ (m - 1) ^ q ≤ 2 := by
    linarith [(abs_le.mp herr).2]
  refine ⟨hhalf, htwo, (hp _ hhalf htwo).trans ?_⟩
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left herr hKp

/-! Parent strain accumulated over a renewal block. -/

theorem parent_renewal_deformation_bound {α s q : ℝ} {Λ m : ℕ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (hΛ : 128 ≤ Λ) (hm : 1 ≤ m) :
    ocA α q Λ (m - 1) * ocTauPP α q Λ m ≤
      ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q) := by
  have h := (AVRegularity.Scales.admissible_time_scale_facts hα0 hα1 hs0 hs1 hq hΛ hm).2.2.2.2.1
  apply h.trans
  exact mul_le_of_le_one_left (Real.rpow_nonneg (AVRegularity.Scales.epsilon_basic hq.1 hΛ).1.le _)
    (by norm_num [zpow_neg])

/-! Uniform comparison of any fixed real power of successive wavelengths. -/

theorem epsilon_power_scale_asymp {q : ℝ} (hq : 1 < q) (p : ℝ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ m : ℕ, Λ₀ ≤ Λ → 2 ≤ m →
      ocAsymp K (ocEpsilon q Λ m ^ p) (ocEpsilon q Λ (m - 1) ^ (q * p)) := by
  obtain ⟨K, hK, hb⟩ := rpow_positive_interval_bounds p
  obtain ⟨_, _, Λ₀, hΛ₀, hr⟩ := epsilon_q_ratio_power_error hq p
  refine ⟨K, hK, Λ₀, hΛ₀, ?_⟩
  intro Λ m hΛ hm
  have h128 := hΛ₀.trans hΛ
  have he := (AVRegularity.Scales.epsilon_basic (m := m) hq h128).1
  have hE := (AVRegularity.Scales.epsilon_basic (m := m - 1) hq h128).1
  have hratio := hr Λ m hΛ hm
  have hpow := hb _ hratio.1 hratio.2.1
  have heq : ocEpsilon q Λ m ^ p =
      (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1) ^ q) ^ p *
        ocEpsilon q Λ (m - 1) ^ (q * p) := by
    rw [Real.div_rpow he.le (Real.rpow_pos_of_pos hE q).le, Real.rpow_mul hE.le]
    exact (div_mul_cancel₀ _ (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hE q) p).ne').symm
  change K⁻¹ * _ ≤ _ ∧ _ ≤ K * _
  rw [heq]
  exact ⟨mul_le_mul_of_nonneg_right hpow.1 (Real.rpow_pos_of_pos hE _).le,
    mul_le_mul_of_nonneg_right hpow.2 (Real.rpow_pos_of_pos hE _).le⟩

end AVRegularity.CycleReference
end

section
open MeasureTheory
namespace AVRegularity.CycleReference

/-! Pointwise pulse and memory bounds used by the reference-flux estimates. -/

theorem slowEnvelope_range (α q : ℝ) (Λ m : ℕ) (l : ℤ) (t : ℝ) :
    0 ≤ slowEnvelope α q Λ m l t ∧ slowEnvelope α q Λ m l t ≤ 1 := by
  unfold slowEnvelope
  have h₁ := Real.smoothTransition.nonneg
    ((t - ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m - ocTauP α q Λ m) /
      ocTauP α q Λ m)
  have h₂ := Real.smoothTransition.nonneg
    ((((l : ℝ) + 1 / 2) * ocTauPP α q Λ m - ocTauP α q Λ m - t) /
      ocTauP α q Λ m)
  have h₁' := Real.smoothTransition.le_one
    ((t - ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m - ocTauP α q Λ m) /
      ocTauP α q Λ m)
  have h₂' := Real.smoothTransition.le_one
    ((((l : ℝ) + 1 / 2) * ocTauPP α q Λ m - ocTauP α q Λ m - t) /
      ocTauP α q Λ m)
  refine ⟨mul_nonneg h₁ h₂, ?_⟩
  have hleft : 0 ≤ 1 - Real.smoothTransition
      ((t - ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m - ocTauP α q Λ m) /
        ocTauP α q Λ m) := by linarith
  have hright : 0 ≤ 1 - Real.smoothTransition
      ((((l : ℝ) + 1 / 2) * ocTauPP α q Λ m - ocTauP α q Λ m - t) /
        ocTauP α q Λ m) := by linarith
  nlinarith [mul_nonneg hleft hright]

theorem ocPulse_range {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (k : ℤ) (t : ℝ) :
    0 ≤ ocPulse α q Λ ζ m k t ∧ ocPulse α q Λ ζ m k t ≤ 1 := by
  rcases hζ with ⟨_, _, _, hrange, _, _⟩
  rw [ocPulse]
  rcases hrange ((t - (k : ℝ) * ocTau α q Λ m) / ocTau α q Λ m) with ⟨hz₀, hz₁⟩
  have hs := slowEnvelope_range α q Λ m (ocLabel α q Λ m k) t
  refine ⟨mul_nonneg hs.1 hz₀, ?_⟩
  have hslow : 0 ≤ 1 - slowEnvelope α q Λ m (ocLabel α q Λ m k) t := by linarith
  have hz : 0 ≤ 1 - ζ ((t - (k : ℝ) * ocTau α q Λ m) / ocTau α q Λ m) := by linarith
  nlinarith [mul_nonneg hslow hz]

/-- The causal memory of a pulse is nonnegative and its normalized mass is at most one. -/
theorem ocPulseMemory_range {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ)
    (hζ : IsFastProfile ζ) (ν : ℝ) (hν : 0 < ν) (k : ℤ) (t : ℝ) :
    0 ≤ ocPulseMemory α q Λ ζ m ν k t ∧
      ocMu q Λ m ν * ocPulseMemory α q Λ ζ m ν k t ≤ 1 := by
  let μ := ocMu q Λ m ν
  have he : 0 < ocEpsilon q Λ m :=
    AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (Λ := Λ) (n := m) hΛ
  have hμ : 0 < μ := by
    dsimp [μ, ocMu]
    positivity
  have hkernel : IntegrableOn (fun r : ℝ => Real.exp (-μ * r)) (Set.Ioi 0) := by
    exact integrableOn_exp_mul_Ioi (a := -μ) (by linarith) 0
  have hζcont : Continuous ζ := hζ.1.continuous
  have hslowcont : ∀ l : ℤ, Continuous (slowEnvelope α q Λ m l) := by
    intro l
    unfold slowEnvelope
    fun_prop
  have hpulsecont : Continuous (fun r : ℝ => ocPulse α q Λ ζ m k (t - r)) := by
    unfold ocPulse
    apply Continuous.mul
    · exact (hslowcont _).comp (by fun_prop)
    · exact hζcont.comp (by fun_prop)
  have hpcont : Continuous (fun r : ℝ =>
      Real.exp (-μ * r) * ocPulse α q Λ ζ m k (t - r)) := by
    exact (Real.continuous_exp.comp (by fun_prop)).mul hpulsecont
  have hmeas : AEStronglyMeasurable
      (fun r : ℝ => Real.exp (-μ * r) * ocPulse α q Λ ζ m k (t - r))
      (volume.restrict (Set.Ioi 0)) := by
    exact hpcont.aestronglyMeasurable
  have hdom : ∀ᵐ r ∂(volume.restrict (Set.Ioi 0)),
      ‖Real.exp (-μ * r) * ocPulse α q Λ ζ m k (t - r)‖ ≤
        ‖Real.exp (-μ * r)‖ := by
    filter_upwards [] with r
    have hp := ocPulse_range (α := α) (q := q) (Λ := Λ) (m := m) hζ k (t - r)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos (-μ * r)), abs_of_nonneg hp.1]
    have hmul := mul_le_mul_of_nonneg_left hp.2 (Real.exp_pos (-μ * r)).le
    simpa using hmul
  have hint : Integrable (fun r : ℝ =>
      Real.exp (-μ * r) * ocPulse α q Λ ζ m k (t - r))
      (volume.restrict (Set.Ioi 0)) := by
    apply hkernel.mono' hmeas
    filter_upwards [hdom] with r hr
    simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hr
  have hnonneg : 0 ≤ ∫ r in Set.Ioi (0 : ℝ),
      Real.exp (-μ * r) * ocPulse α q Λ ζ m k (t - r) := by
    apply integral_nonneg_of_ae
    filter_upwards [] with r
    exact mul_nonneg (Real.exp_pos _).le (ocPulse_range (α := α) (q := q) (Λ := Λ) (m := m) hζ k (t - r)).1
  have hupper : ∫ r in Set.Ioi (0 : ℝ),
      Real.exp (-μ * r) * ocPulse α q Λ ζ m k (t - r) ≤
        ∫ r in Set.Ioi (0 : ℝ), Real.exp (-μ * r) := by
    apply integral_mono_ae hint hkernel
    filter_upwards [] with r
    have hp := ocPulse_range (α := α) (q := q) (Λ := Λ) (m := m) hζ k (t - r)
    have hexp := Real.exp_pos (-μ * r)
    calc
      Real.exp (-μ * r) * ocPulse α q Λ ζ m k (t - r) ≤ Real.exp (-μ * r) * 1 :=
        mul_le_mul_of_nonneg_left hp.2 hexp.le
      _ = Real.exp (-μ * r) := by ring
  have hmemory : ocPulseMemory α q Λ ζ m ν k t =
      ∫ r in Set.Ioi (0 : ℝ),
        Real.exp (-μ * r) * ocPulse α q Λ ζ m k (t - r) := by
    rw [ocPulseMemory]
  rw [hmemory]
  constructor
  · exact hnonneg
  · calc
      μ * (∫ r in Set.Ioi (0 : ℝ),
          Real.exp (-μ * r) * ocPulse α q Λ ζ m k (t - r)) ≤
        μ * (∫ r in Set.Ioi (0 : ℝ), Real.exp (-μ * r)) :=
          mul_le_mul_of_nonneg_left hupper hμ.le
      _ = 1 := by
        rw [integral_exp_mul_Ioi (a := -μ) (by linarith) 0]
        simp
        field_simp [ne_of_gt hμ]

end AVRegularity.CycleReference
end

section
namespace AVRegularity.CycleReference

/-! One rounding threshold works for every fixed power, with order-dependent constants. -/

theorem epsilon_power_asymp_shared_threshold {q : ℝ} (hq : 1 < q) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ p : ℝ, ∃ K : ℝ, 1 ≤ K ∧
      ∀ Λ m : ℕ, Λ₀ ≤ Λ → 2 ≤ m →
        ocAsymp K (ocEpsilon q Λ m ^ p) (ocEpsilon q Λ (m - 1) ^ (q * p)) := by
  obtain ⟨_, _, Λ₀, hΛ₀, hr⟩ := epsilon_q_ratio_power_error hq 1
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro p
  obtain ⟨K, hK, hb⟩ := rpow_positive_interval_bounds p
  refine ⟨K, hK, ?_⟩
  intro Λ m hΛ hm
  have h128 := hΛ₀.trans hΛ
  have he := (AVRegularity.Scales.epsilon_basic (m := m) hq h128).1
  have hE := (AVRegularity.Scales.epsilon_basic (m := m - 1) hq h128).1
  have hratio := hr Λ m hΛ hm
  have hpow := hb _ hratio.1 hratio.2.1
  have heq : ocEpsilon q Λ m ^ p =
      (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1) ^ q) ^ p *
        ocEpsilon q Λ (m - 1) ^ (q * p) := by
    rw [Real.div_rpow he.le (Real.rpow_pos_of_pos hE q).le, Real.rpow_mul hE.le]
    exact (div_mul_cancel₀ _ (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hE q) p).ne').symm
  change K⁻¹ * _ ≤ _ ∧ _ ≤ K * _
  rw [heq]
  exact ⟨mul_le_mul_of_nonneg_right hpow.1 (Real.rpow_pos_of_pos hE _).le,
    mul_le_mul_of_nonneg_right hpow.2 (Real.rpow_pos_of_pos hE _).le⟩

/-! Uniform two-sided time-scale comparisons with explicit numerical constants. -/

theorem ocTauPP_asymp {α s q : ℝ} {Λ m : ℕ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (hΛ : 128 ≤ Λ) :
    ocAsymp (2 ^ (26 : ℕ)) (ocTauPP α q Λ m)
      (ocEpsilon q Λ (m - 1) ^ (2 - (1 + α) + 2 * ocDelta α q)) := by
  have he := AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 hΛ
  have hd := (AVRegularity.Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq).2.1
  have hp : 0 ≤ 2 - (1 + α) + 2 * ocDelta α q := by linarith
  obtain ⟨hl, hu⟩ := ocTauPP_power_bounds he.1 he.2.1 hp
  constructor
  · convert hl using 1; norm_num [zpow_neg]
  · apply hu.trans
    exact mul_le_mul_of_nonneg_right (by norm_num [zpow_neg]) (Real.rpow_pos_of_pos he.1 _).le

theorem ocL_asymp {α q : ℝ} {Λ m : ℕ}
    (he : 0 < ocEpsilon q Λ (m - 1)) (he1 : ocEpsilon q Λ (m - 1) ≤ 1)
    (hd : 0 ≤ ocDelta α q) :
    ocAsymp 9 (ocL α q Λ m : ℝ) (ocEpsilon q Λ (m - 1) ^ (-ocDelta α q)) := by
  obtain ⟨hl, hu⟩ := ocL_power_bounds he he1 hd
  exact ⟨(mul_le_mul_of_nonneg_right (by norm_num : (9 : ℝ)⁻¹ ≤ 4)
    (Real.rpow_pos_of_pos he _).le).trans hl, hu⟩

theorem ocTau_asymp {α s q : ℝ} {Λ m : ℕ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (hΛ : 128 ≤ Λ) :
    ocAsymp (2 ^ (26 : ℕ) * 81) (ocTau α q Λ m)
      (ocEpsilon q Λ (m - 1) ^ (2 - (1 + α) + 4 * ocDelta α q)) := by
  have he := AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 hΛ
  have hd := (AVRegularity.Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq).2.1
  have hh := ocTauPP_asymp hα0 hα1 hs0 hs1 hq hΛ (m := m)
  have hl := ocL_asymp he.1 he.2.1 hd.le
  have hl2 := asymp_rpow_nonneg (by norm_num : (0 : ℝ) < 9)
    (Real.rpow_pos_of_pos he.1 _).le (by norm_num : (0 : ℝ) ≤ 2) hl
  have hL : 0 < (ocL α q Λ m : ℝ) := by
    have hn : 0 < ocL α q Λ m := by unfold ocL; omega
    exact_mod_cast hn
  have hl2' : ocAsymp 81 ((ocL α q Λ m : ℝ) ^ 2)
      (ocEpsilon q Λ (m - 1) ^ (-2 * ocDelta α q)) := by
    rw [Real.rpow_two, ← Real.rpow_mul he.1.le] at hl2
    have hid : (-ocDelta α q) * (2 : ℝ) = -2 * ocDelta α q := by ring
    simpa only [Real.rpow_two, hid, show (9 : ℝ) ^ (2 : ℕ) = 81 by norm_num] using hl2
  have h := asymp_div (by norm_num : (0 : ℝ) < 2 ^ (26 : ℕ)) (by norm_num : (0 : ℝ) < 81)
    (Real.rpow_pos_of_pos he.1 _).le (Real.rpow_pos_of_pos he.1 _) (sq_pos_of_pos hL) hh hl2'
  unfold ocTau
  convert h using 1
  rw [← Real.rpow_sub he.1]
  congr 1
  ring

theorem ocTauP_asymp {α s q : ℝ} {Λ m : ℕ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (hΛ : 128 ≤ Λ) :
    ocAsymp (2 ^ (26 : ℕ) * 9) (ocTauP α q Λ m)
      (ocEpsilon q Λ (m - 1) ^ (2 - (1 + α) + 3 * ocDelta α q)) := by
  have he := AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 hΛ
  have hd := (AVRegularity.Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq).2.1
  have hh := ocTauPP_asymp hα0 hα1 hs0 hs1 hq hΛ (m := m)
  have hl := ocL_asymp he.1 he.2.1 hd.le
  have hL : 0 < (ocL α q Λ m : ℝ) := by
    have hn : 0 < ocL α q Λ m := by unfold ocL; omega
    exact_mod_cast hn
  have h := asymp_div (by norm_num : (0 : ℝ) < 2 ^ (26 : ℕ)) (by norm_num : (0 : ℝ) < 9)
    (Real.rpow_pos_of_pos he.1 _).le (Real.rpow_pos_of_pos he.1 _) hL hh hl
  unfold ocTauP
  convert h using 1
  rw [← Real.rpow_sub he.1]
  congr 1
  ring

end AVRegularity.CycleReference
end

section
open MeasureTheory
open scoped Convolution
namespace AVRegularity.CycleReference

/-! Continuity of the causal pulse memory, from its convolution structure. -/

noncomputable def causalKernel (μ r : ℝ) : ℝ :=
  (Set.Ioi (0 : ℝ)).indicator (fun r => Real.exp (-μ * r)) r

theorem ocPulseMemory_eq_convolution {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (ν : ℝ) (k : ℤ) (t : ℝ) :
    ocPulseMemory α q Λ ζ m ν (k : ℤ) t =
      (causalKernel (ocMu q Λ m ν) ⋆ (fun s => ocPulse α q Λ ζ m k s)) t := by
  rw [MeasureTheory.convolution_lsmul]
  unfold ocPulseMemory causalKernel
  rw [← integral_indicator (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))]
  apply integral_congr_ae
  filter_upwards [] with r
  by_cases hr : r ∈ Set.Ioi (0 : ℝ) <;> simp [Set.indicator, hr]

theorem ocPulse_continuous {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hζ : IsFastProfile ζ) (k : ℤ) :
    Continuous (ocPulse α q Λ ζ m k) := by
  unfold ocPulse
  apply Continuous.mul
  · unfold slowEnvelope
    fun_prop
  · exact hζ.1.continuous.comp (by fun_prop)

theorem ocPulse_bdd_range {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hζ : IsFastProfile ζ) (k : ℤ) :
    BddAbove (Set.range fun t : ℝ => ‖ocPulse α q Λ ζ m k t‖) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨t, rfl⟩
  have hp := ocPulse_range (α := α) (q := q) (Λ := Λ) (m := m) hζ k t
  change ‖ocPulse α q Λ ζ m k t‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg hp.1]
  exact hp.2

theorem ocPulseMemory_continuous {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν) (k : ℤ) :
    Continuous (ocPulseMemory α q Λ ζ m ν k) := by
  let μ := ocMu q Λ m ν
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos
    (q := q) (Λ := Λ) (n := m) hΛ
  have hμ : 0 < μ := by
    dsimp [μ, ocMu]
    positivity
  have hkernel : IntegrableOn (fun r : ℝ => Real.exp (-μ * r)) (Set.Ioi 0) := by
    exact integrableOn_exp_mul_Ioi (a := -μ) (by linarith) 0
  have hkernelInt : Integrable (causalKernel μ) volume := by
    change Integrable
      ((Set.Ioi (0 : ℝ)).indicator (fun r : ℝ => Real.exp (-μ * r))) volume
    rw [integrable_indicator_iff (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))]
    exact hkernel
  have hconv : Continuous
      (causalKernel μ ⋆ (fun s => ocPulse α q Λ ζ m k s)) :=
    BddAbove.continuous_convolution_right_of_integrable
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (ocPulse_bdd_range hζ k)
      hkernelInt (ocPulse_continuous hζ k)
  rw [show ocPulseMemory α q Λ ζ m ν k =
      (causalKernel μ ⋆ (fun s => ocPulse α q Λ ζ m k s)) by
        funext t
        simpa [μ] using (ocPulseMemory_eq_convolution (α := α) (q := q)
          (Λ := Λ) (m := m) (ζ := ζ) ν k t)]
  exact hconv

end AVRegularity.CycleReference
end

section
namespace AVRegularity.CycleReference

/-! Geometric facts about the compactly supported time pulses. -/

section
open MeasureTheory

theorem profile_ne_support_interval {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) {x : ℝ}
    (hx : ζ x ≠ 0) : -(2 / 3) < x ∧ x < 2 / 3 := by
  have hxmem : x ∈ tsupport ζ := subset_closure hx
  exact hζ.2.2.1 hxmem

theorem pulse_nonzero_center_distance {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {k : ℤ} {t : ℝ}
    (hp : ocPulse α q Λ ζ m k t ≠ 0) :
    (k : ℝ) * ocTau α q Λ m - (2 / 3) * ocTau α q Λ m < t ∧
      t < (k : ℝ) * ocTau α q Λ m + (2 / 3) * ocTau α q Λ m := by
  have htau : 0 < ocTau α q Λ m :=
    AVRegularity.Construction.Stream.ocTau_pos (Λ := Λ) (m := m) hΛ
  have hz : ζ ((t - (k : ℝ) * ocTau α q Λ m) / ocTau α q Λ m) ≠ 0 := by
    intro hzero
    apply hp
    simp [ocPulse, hzero]
  have harg := profile_ne_support_interval hζ hz
  have hlow : -(2 / 3) * ocTau α q Λ m < t - (k : ℝ) * ocTau α q Λ m :=
    (lt_div_iff₀ htau).mp harg.1
  have hhigh : t - (k : ℝ) * ocTau α q Λ m < (2 / 3) * ocTau α q Λ m :=
    (div_lt_iff₀ htau).mp harg.2
  constructor <;> linarith

theorem odd_pulse_support_unique {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {k j : ℤ} {t : ℝ}
    (hk : Odd k) (hj : Odd j)
    (hpk : ocPulse α q Λ ζ m k t ≠ 0) (hpj : ocPulse α q Λ ζ m j t ≠ 0) : k = j := by
  rcases hk with ⟨a, hk⟩
  rcases hj with ⟨b, hj⟩
  by_contra hne
  have hlt : k < j ∨ j < k := lt_or_gt_of_ne hne
  rcases hlt with hlt | hlt
  · have hgapI : k + 2 ≤ j := by omega
    have hgap : (k : ℝ) + 2 ≤ (j : ℝ) := by exact_mod_cast hgapI
    have hdist := pulse_nonzero_center_distance hΛ hζ hpk
    have hjdist := pulse_nonzero_center_distance hΛ hζ hpj
    have htau := AVRegularity.Construction.Stream.ocTau_pos
      (α := α) (q := q) (Λ := Λ) (m := m) hΛ
    have hleft : (k : ℝ) * ocTau α q Λ m + (4 / 3) * ocTau α q Λ m ≤
        (j : ℝ) * ocTau α q Λ m - (2 / 3) * ocTau α q Λ m := by
      have hmul := mul_le_mul_of_nonneg_right hgap htau.le
      nlinarith
    linarith
  · have hgapI : j + 2 ≤ k := by omega
    have hgap : (j : ℝ) + 2 ≤ (k : ℝ) := by exact_mod_cast hgapI
    have hdist := pulse_nonzero_center_distance hΛ hζ hpj
    have hjdist := pulse_nonzero_center_distance hΛ hζ hpk
    have htau := AVRegularity.Construction.Stream.ocTau_pos
      (α := α) (q := q) (Λ := Λ) (m := m) hΛ
    have hleft : (j : ℝ) * ocTau α q Λ m + (4 / 3) * ocTau α q Λ m ≤
        (k : ℝ) * ocTau α q Λ m - (2 / 3) * ocTau α q Λ m := by
      have hmul := mul_le_mul_of_nonneg_right hgap htau.le
      nlinarith
    linarith

theorem pulse_time_shift {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (k K J : ℤ) (t N : ℝ)
    (hKτ : (K : ℝ) * ocTau α q Λ m = N)
    (hJPP : (J : ℝ) * ocTauPP α q Λ m = N) :
    ocPulse α q Λ ζ m (k + K) (t + N) = ocPulse α q Λ ζ m k t := by
  have hlabel := AVRegularity.Construction.Stream.ocLabel_add_time_shift
    α q Λ m k K J hΛ (by rw [hKτ, hJPP])
  rw [ocPulse, ocPulse, hlabel]
  rw [AVRegularity.Construction.Stream.ocSlowEnvelope_add_time_shift
    α q Λ m (ocLabel α q Λ m k) J t N hJPP]
  rw [AVRegularity.Construction.Stream.ocZeta_add_time_shift
    α q Λ m ζ k K t N hKτ]

theorem pulseMemory_time_shift {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (ν : ℝ) (k K J : ℤ) (t N : ℝ)
    (hKτ : (K : ℝ) * ocTau α q Λ m = N)
    (hJPP : (J : ℝ) * ocTauPP α q Λ m = N) :
    ocPulseMemory α q Λ ζ m ν (k + K) (t + N) =
      ocPulseMemory α q Λ ζ m ν k t := by
  unfold ocPulseMemory
  apply integral_congr_ae
  filter_upwards [] with r
  have htime : t + N - r = (t - r) + N := by ring
  rw [htime, pulse_time_shift hΛ k K J (t - r) N hKτ hJPP]
end

/-! Plateau geometry for complete pulse cores. -/

theorem slowEnvelope_eq_one_on_plateau {α q : ℝ} {Λ m : ℕ}
    (hΛ : 1 ≤ Λ) (l : ℤ) (t : ℝ)
    (hlo : ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m + 2 * ocTauP α q Λ m ≤ t)
    (hhi : t ≤ ((l : ℝ) + 1 / 2) * ocTauPP α q Λ m - 2 * ocTauP α q Λ m) :
    slowEnvelope α q Λ m l t = 1 := by
  have hτp : 0 < ocTauP α q Λ m := by
    unfold ocTauP
    have hL : 0 < (ocL α q Λ m : ℝ) := by
      have hLn : 0 < ocL α q Λ m := by unfold ocL; omega
      exact_mod_cast hLn
    exact div_pos (AVRegularity.Construction.Stream.ocTauPP_pos hΛ) hL
  unfold slowEnvelope
  rw [Real.smoothTransition.one_of_one_le
    ((le_div_iff₀ hτp).mpr (by linarith)),
    Real.smoothTransition.one_of_one_le
      ((le_div_iff₀ hτp).mpr (by linarith)), one_mul]

theorem completeCore_of_plateau {α q : ℝ} {Λ m : ℕ}
    (hΛ : 1 ≤ Λ) (l k : ℤ) (hk : Odd k) (hlabel : ocLabel α q Λ m k = l)
    (hlo : ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m + 2 * ocTauP α q Λ m ≤
      ((k : ℝ) - 1 / 3) * ocTau α q Λ m)
    (hhi : ((k : ℝ) + 1 / 3) * ocTau α q Λ m ≤
      ((l : ℝ) + 1 / 2) * ocTauPP α q Λ m - 2 * ocTauP α q Λ m) :
    IsOCCompleteCore α q Λ m l k := by
  refine ⟨hk, hlabel, ?_⟩
  intro t ht
  exact slowEnvelope_eq_one_on_plateau hΛ l t (hlo.trans ht.1) (ht.2.trans hhi)

theorem ocLabel_eq_of_center {α q : ℝ} {Λ m : ℕ}
    (hΛ : 1 ≤ Λ) (l k : ℤ)
    (hlo : (l : ℝ) * ocTauPP α q Λ m -
      (ocTauPP α q Λ m - ocTau α q Λ m) / 2 ≤ (k : ℝ) * ocTau α q Λ m)
    (hhi : (k : ℝ) * ocTau α q Λ m < (l : ℝ) * ocTauPP α q Λ m +
      (ocTauPP α q Λ m + ocTau α q Λ m) / 2) :
    ocLabel α q Λ m k = l := by
  have hτ := AVRegularity.Construction.Stream.ocTauPP_pos
    (α := α) (q := q) (Λ := Λ) (m := m) hΛ
  unfold ocLabel
  apply Int.floor_eq_iff.mpr
  constructor
  · rw [le_div_iff₀ hτ]
    linarith
  · rw [div_lt_iff₀ hτ]
    nlinarith

/-! The glue cutoff is one on its own pulse and vanishes on the other odd slots. -/

theorem ocCutoff_eq_one_of_pulse_ne_zero {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {k : ℤ} {t : ℝ}
    (hp : ocPulse α q Λ ζ m k t ≠ 0) :
    ocCutoff α q Λ m k t = 1 := by
  have htau : 0 < ocTau α q Λ m :=
    AVRegularity.Construction.Stream.ocTau_pos (Λ := Λ) (m := m) hΛ
  have hsupport := pulse_nonzero_center_distance hΛ hζ hp
  have hdist : |t - (k : ℝ) * ocTau α q Λ m| <
      (2 / 3) * ocTau α q Λ m := by
    rw [abs_lt]
    constructor <;> linarith
  have hratio : 2 * |t - (k : ℝ) * ocTau α q Λ m| / ocTau α q Λ m < 4 / 3 :=
    (div_lt_iff₀ htau).2 (by nlinarith)
  have harg : 1 ≤ 5 / 2 -
      2 * |t - (k : ℝ) * ocTau α q Λ m| / ocTau α q Λ m := by linarith
  rw [ocCutoff, Real.smoothTransition.one_of_one_le harg]

theorem ocCutoff_eq_zero_of_other_slot {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {k j : ℤ} {t : ℝ}
    (hk : Odd k) (hj : Odd j) (hkj : j ≠ k)
    (hp : ocPulse α q Λ ζ m k t ≠ 0) :
    ocCutoff α q Λ m j t = 0 := by
  have htau : 0 < ocTau α q Λ m :=
    AVRegularity.Construction.Stream.ocTau_pos (Λ := Λ) (m := m) hΛ
  have hsupport := pulse_nonzero_center_distance hΛ hζ hp
  have hgapInt : (2 : ℤ) ≤ |j - k| := by
    rcases hk with ⟨a, ha⟩
    rcases hj with ⟨b, hb⟩
    have heven : Even (j - k) := by
      refine ⟨b - a, ?_⟩
      rw [ha, hb]
      ring
    rcases heven with ⟨c, hc⟩
    have hne : j - k ≠ 0 := sub_ne_zero.mpr hkj
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [abs_of_neg (by omega)]
      omega
    · rw [abs_of_pos hgt]
      omega
  have hgap : (2 : ℝ) ≤ |(j : ℝ) - (k : ℝ)| := by exact_mod_cast hgapInt
  have hcenters : 2 * ocTau α q Λ m ≤
      |(j : ℝ) * ocTau α q Λ m - (k : ℝ) * ocTau α q Λ m| := by
    rw [show (j : ℝ) * ocTau α q Λ m - (k : ℝ) * ocTau α q Λ m =
      ((j : ℝ) - (k : ℝ)) * ocTau α q Λ m by ring, abs_mul, abs_of_pos htau]
    nlinarith
  have hdist : (5 / 4) * ocTau α q Λ m <
      |t - (j : ℝ) * ocTau α q Λ m| := by
    have hcenterDist : |t - (k : ℝ) * ocTau α q Λ m| <
        (2 / 3) * ocTau α q Λ m := by
      rw [abs_lt]
      constructor <;> linarith [hsupport.1, hsupport.2]
    have htri := abs_sub_le ((j : ℝ) * ocTau α q Λ m) t
      ((k : ℝ) * ocTau α q Λ m)
    rw [abs_sub_comm (a := ((j : ℝ) * ocTau α q Λ m)) (b := t)] at htri
    nlinarith [htau, hcenters, htri, hcenterDist]
  have hratio : 5 / 2 ≤
      2 * |t - (j : ℝ) * ocTau α q Λ m| / ocTau α q Λ m :=
    (le_div_iff₀ htau).2 (by nlinarith [abs_nonneg (t - (j : ℝ) * ocTau α q Λ m)])
  have harg : 5 / 2 -
      2 * |t - (j : ℝ) * ocTau α q Λ m| / ocTau α q Λ m ≤ 0 := by linarith
  rw [ocCutoff, Real.smoothTransition.zero_of_nonpos harg]

theorem ocCutoff_support_finite {α q : ℝ} {Λ m : ℕ} (hΛ : 1 ≤ Λ) {t : ℝ} :
    {k : {k : ℤ // Odd k} | ocCutoff α q Λ m k.1 t ≠ 0}.Finite := by
  classical
  have htau : 0 < ocTau α q Λ m :=
    AVRegularity.Construction.Stream.ocTau_pos (Λ := Λ) (m := m) hΛ
  let lo : ℝ := t / ocTau α q Λ m - 5 / 4
  let hi : ℝ := t / ocTau α q Λ m + 5 / 4
  have hbound (k : {k : ℤ // Odd k}) (hk : ocCutoff α q Λ m k.1 t ≠ 0) :
      lo < (k.1 : ℝ) ∧ (k.1 : ℝ) < hi := by
    have harg : 0 < 5 / 2 -
        2 * |t - (k.1 : ℝ) * ocTau α q Λ m| / ocTau α q Λ m := by
      by_contra h
      have hnonpos : 5 / 2 -
          2 * |t - (k.1 : ℝ) * ocTau α q Λ m| / ocTau α q Λ m ≤ 0 := le_of_not_gt h
      exact hk (Real.smoothTransition.zero_of_nonpos hnonpos)
    have hratio : 2 * |t - (k.1 : ℝ) * ocTau α q Λ m| / ocTau α q Λ m < 5 / 2 := by
      linarith [harg]
    have hmul := (div_lt_iff₀ htau).mp hratio
    have hdist : |t - (k.1 : ℝ) * ocTau α q Λ m| <
        (5 / 4) * ocTau α q Λ m := by linarith
    rw [abs_lt] at hdist
    have hleft : (t / ocTau α q Λ m) - 5 / 4 < (k.1 : ℝ) := by
      have hmul : t < ((k.1 : ℝ) + 5 / 4) * ocTau α q Λ m := by linarith [hdist.2]
      have hdiv := (div_lt_iff₀ htau).2 hmul
      linarith
    have hright : (k.1 : ℝ) < (t / ocTau α q Λ m) + 5 / 4 := by
      have hmul : ((k.1 : ℝ) - 5 / 4) * ocTau α q Λ m < t := by linarith [hdist.1]
      have hdiv := (lt_div_iff₀ htau).2 hmul
      linarith
    exact ⟨hleft, hright⟩
  let I : Set ℤ := Set.Icc (Int.ceil lo) (Int.ceil hi)
  have hfiniteI : I.Finite := Set.finite_Icc _ _
  have hpre : Set.Finite ((fun k : {k : ℤ // Odd k} => k.1) ⁻¹' I) :=
    hfiniteI.preimage (by
        intro a ha b hb hab
        exact Subtype.ext hab)
  apply Set.Finite.subset hpre
  intro k hk
  have hb := hbound k hk
  change k.1 ∈ I
  simp only [I, Set.mem_Icc]
  exact ⟨Int.ceil_le.mpr (le_of_lt hb.1),
    Int.cast_le.mp (le_trans (le_of_lt hb.2) (Int.le_ceil hi))⟩

/-! The partition property forces the fast profile to equal one on a complete core. -/

theorem fastProfile_eq_one_on_core {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (t : ℝ) (ht : -(1 / 3) ≤ t ∧ t ≤ 1 / 3) : ζ t = 1 := by
  have hsum := hζ.2.2.2.2.1 t
  have hsingle : (∑' j : ℤ, ζ (t - j)) = ζ t := by
    simpa using (tsum_eq_single (0 : ℤ) (f := fun j : ℤ => ζ (t - j)) (by
      intro j hj
      by_contra hne
      have hh := profile_ne_support_interval hζ hne
      have hjlo : (-1 : ℝ) < (j : ℝ) := by linarith
      have hjhi : (j : ℝ) < 1 := by linarith
      have hjlo' : (-1 : ℤ) < j := by exact_mod_cast hjlo
      have hjhi' : j < (1 : ℤ) := by exact_mod_cast hjhi
      have hj0 : j = 0 := by omega
      exact hj hj0))
  exact hsingle.symm.trans hsum

theorem pulse_eq_one_on_completeCore {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (l k : ℤ)
    (hcore : IsOCCompleteCore α q Λ m l k) (t : ℝ)
    (ht : t ∈ Set.Icc (((k : ℝ) - 1 / 3) * ocTau α q Λ m)
      (((k : ℝ) + 1 / 3) * ocTau α q Λ m)) :
    ocPulse α q Λ ζ m k t = 1 := by
  have hτ := AVRegularity.Construction.Stream.ocTau_pos
    (α := α) (q := q) (Λ := Λ) (m := m) hΛ
  have harg : -(1 / 3) ≤ (t - (k : ℝ) * ocTau α q Λ m) / ocTau α q Λ m ∧
      (t - (k : ℝ) * ocTau α q Λ m) / ocTau α q Λ m ≤ 1 / 3 := by
    constructor
    · apply (le_div_iff₀ hτ).mpr
      linarith [ht.1]
    · apply (div_le_iff₀ hτ).mpr
      linarith [ht.2]
  rw [ocPulse, hcore.2.1, hcore.2.2 t ht, fastProfile_eq_one_on_core hζ _ harg, one_mul]

end AVRegularity.CycleReference
end

section
open MeasureTheory Filter Topology
namespace AVRegularity.CycleReference

/-! Scalar memory ODE. Adapted from the pinned upstream
`AVenhance/Infra/Section3/CorrTimeRegularity.lean`, with our free construction parameters. -/

theorem ocPulse_hasCompactSupport {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (k : ℤ) :
    HasCompactSupport (ocPulse α q Λ ζ m k) := by
  have hτ := AVRegularity.Construction.Stream.ocTau_pos
    (α := α) (q := q) (Λ := Λ) (m := m) hΛ
  have hz : HasCompactSupport ζ := by
    apply IsCompact.of_isClosed_subset isCompact_Icc isClosed_closure
    intro x hx
    exact ⟨(hζ.2.2.1 hx).1.le, (hζ.2.2.1 hx).2.le⟩
  let e : ℝ ≃ₜ ℝ :=
    (Homeomorph.addRight (-((k : ℝ) * ocTau α q Λ m))).trans
      (Homeomorph.mulRight₀ ((ocTau α q Λ m)⁻¹) (inv_ne_zero (ne_of_gt hτ)))
  have he : (fun t => ζ ((t - (k : ℝ) * ocTau α q Λ m) / ocTau α q Λ m)) =
      ζ ∘ e := by
    funext t
    congr 1
  unfold ocPulse
  apply HasCompactSupport.mul_left
  rw [he]
  exact hz.comp_isClosedEmbedding e.isClosedEmbedding

theorem ocPulseMemory_eq_exp_mul_Iic {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (ν : ℝ) (k : ℤ) :
    ocPulseMemory α q Λ ζ m ν k = fun t =>
      Real.exp (-(ocMu q Λ m ν) * t) *
        ∫ s in Set.Iic t, ocPulse α q Λ ζ m k s * Real.exp (ocMu q Λ m ν * s) := by
  funext t
  let μ := ocMu q Λ m ν
  let f : ℝ → ℝ := fun s => Real.exp (-μ * (t - s)) * ocPulse α q Λ ζ m k s
  have hpre : (fun r : ℝ => t - r) ⁻¹' Set.Iio t = Set.Ioi 0 := by
    ext r
    simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_Ioi]
    constructor <;> intro h <;> linarith
  have hchange := (volume.measurePreserving_sub_left t).setIntegral_preimage_emb
    ((Homeomorph.neg ℝ).trans (Homeomorph.addLeft t)).measurableEmbedding f (Set.Iio t)
  rw [hpre] at hchange
  have hmem : ocPulseMemory α q Λ ζ m ν k t = ∫ s in Set.Iic t, f s := by
    unfold ocPulseMemory
    rw [integral_Iic_eq_integral_Iio]
    refine Eq.trans ?_ hchange
    apply integral_congr_ae
    filter_upwards [] with r
    dsimp [f, μ]
    congr 2
    ring
  rw [hmem]
  have hf : f = fun s => Real.exp (-μ * t) *
      (ocPulse α q Λ ζ m k s * Real.exp (μ * s)) := by
    funext s
    dsimp [f]
    rw [show -μ * (t - s) = -μ * t + μ * s by ring, Real.exp_add]
    ring
  rw [hf, integral_const_mul]

theorem ocPulseMemory_hasDerivAt {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (k : ℤ) (t : ℝ) :
    HasDerivAt (ocPulseMemory α q Λ ζ m ν k)
      (ocPulse α q Λ ζ m k t - ocMu q Λ m ν * ocPulseMemory α q Λ ζ m ν k t) t := by
  let ρ := ocMu q Λ m ν
  let g : ℝ → ℝ := fun s => ocPulse α q Λ ζ m k s * Real.exp (ρ * s)
  have hgcont : Continuous g :=
    (ocPulse_continuous hζ k).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hgcompact : HasCompactSupport g :=
    (ocPulse_hasCompactSupport hΛ hζ k).mul_right
  have hgintegrable : Integrable g := hgcont.integrable_of_hasCompactSupport hgcompact
  have hIic (r : ℝ) : IntegrableOn g (Set.Iic r) := hgintegrable.integrableOn
  have hIic_eq (r : ℝ) :
      (∫ s in Set.Iic r, g s) = (∫ s in Set.Iic 0, g s) + ∫ s in (0 : ℝ)..r, g s := by
    have hsub := intervalIntegral.integral_Iic_sub_Iic (μ := volume) (f := g) (hIic 0) (hIic r)
    linarith only [hsub]
  have hprim : HasDerivAt (fun r : ℝ => ∫ s in (0 : ℝ)..r, g s) (g t) t := by
    apply intervalIntegral.integral_hasDerivAt_right
    · exact hgcont.intervalIntegrable 0 t
    · exact hgcont.stronglyMeasurableAtFilter volume (𝓝 t)
    · exact hgcont.continuousAt
  let E := Real.exp (-ρ * t)
  let H := (∫ s in Set.Iic 0, g s) + ∫ s in (0 : ℝ)..t, g s
  have hcancel : E * Real.exp (ρ * t) = 1 := by
    dsimp [E]
    rw [← Real.exp_add, show -ρ * t + ρ * t = 0 by ring, Real.exp_zero]
  have hFval : ocPulseMemory α q Λ ζ m ν k t = E * H := by
    rw [ocPulseMemory_eq_exp_mul_Iic]
    change E * (∫ s in Set.Iic t, g s) = E * H
    rw [hIic_eq]
  have harg : HasDerivAt (fun r : ℝ => -ρ * r) (-ρ) t := hasDerivAt_const_mul (-ρ)
  have hexp := (Real.hasDerivAt_exp (-ρ * t)).comp t harg
  have hsum := hprim.const_add (∫ s in Set.Iic 0, g s)
  have hprodRaw := hexp.mul hsum
  have hprod : HasDerivAt (fun r : ℝ => Real.exp (-ρ * r) *
      ((∫ s in Set.Iic 0, g s) + ∫ s in (0 : ℝ)..r, g s))
      (E * (-ρ) * H + E * g t) t := by
    convert hprodRaw using 1
    · rfl
    · rfl
  have hval : E * (-ρ) * H + E * g t =
      ocPulse α q Λ ζ m k t - ρ * ocPulseMemory α q Λ ζ m ν k t := by
    rw [hFval, show g t = ocPulse α q Λ ζ m k t * Real.exp (ρ * t) by rfl]
    calc
      _ = (-ρ * E) * H + ocPulse α q Λ ζ m k t * (E * Real.exp (ρ * t)) := by ring
      _ = _ := by rw [hcancel]; ring
  have hbase := hprod.congr_deriv hval
  have hrepr : ocPulseMemory α q Λ ζ m ν k = fun r =>
      Real.exp (-ρ * r) * ((∫ s in Set.Iic 0, g s) + ∫ s in (0 : ℝ)..r, g s) := by
    funext r
    rw [ocPulseMemory_eq_exp_mul_Iic]
    change Real.exp (-ρ * r) * (∫ s in Set.Iic r, g s) = _
    rw [hIic_eq]
  convert hbase using 1

end AVRegularity.CycleReference
end

section
namespace AVRegularity.CycleReference

/-! A smooth product representation removes the apparent cusp in the glue cutoff. -/

theorem smoothTransition_abs_eq_mul (x : ℝ) :
    Real.smoothTransition (5 / 2 - 2 * |x|) =
      Real.smoothTransition (5 / 2 - 2 * x) *
        Real.smoothTransition (5 / 2 + 2 * x) := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, Real.smoothTransition.one_of_one_le (by linarith :
      1 ≤ 5 / 2 + 2 * x), mul_one]
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [abs_of_nonpos hx', Real.smoothTransition.one_of_one_le (by linarith :
      1 ≤ 5 / 2 - 2 * x), one_mul]
    congr 1
    ring

theorem ocCutoff_eq_product {α q : ℝ} {Λ m : ℕ} (hΛ : 1 ≤ Λ) (k : ℤ) :
    ocCutoff α q Λ m k = fun t =>
      Real.smoothTransition (5 / 2 - 2 * ((t - (k : ℝ) * ocTau α q Λ m) / ocTau α q Λ m)) *
        Real.smoothTransition (5 / 2 + 2 * ((t - (k : ℝ) * ocTau α q Λ m) / ocTau α q Λ m)) := by
  funext t
  have hτ := AVRegularity.Construction.Stream.ocTau_pos
    (α := α) (q := q) (Λ := Λ) (m := m) hΛ
  unfold ocCutoff
  rw [show 2 * |t - (k : ℝ) * ocTau α q Λ m| / ocTau α q Λ m =
    2 * |(t - (k : ℝ) * ocTau α q Λ m) / ocTau α q Λ m| by
      rw [abs_div, abs_of_pos hτ]; ring, smoothTransition_abs_eq_mul]

theorem ocCutoff_contDiff {α q : ℝ} {Λ m : ℕ} (hΛ : 1 ≤ Λ) (k : ℤ) :
    ContDiff ℝ (⊤ : ℕ∞) (ocCutoff α q Λ m k) := by
  rw [ocCutoff_eq_product hΛ k]
  fun_prop

end AVRegularity.CycleReference
end
end
end

section
@[expose] public section
open Homogenization AVenhance
open scoped Matrix
namespace AVRegularity.CycleReference

/-! Qualitative renewal identities from the general smooth stream flow. -/

open AVRegularity.Velocity.Port.Section2FlowIdentities

theorem streamFlow_spatial_smooth {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (t s : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => AVRegularity.streamFlow φ hφ t y s) := by
  have hb := AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ
  have hX := AVenhance.flow_isFlow (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz
  have hs := Infra.Flow.flow_joint_contDiff_infty hb hX
  exact hs.comp (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const))

theorem chart_transition_comp (α q : ℝ) (Λ m : ℕ) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (l₁ l₂ : ℤ) (t : ℝ) (y : Vec 2) :
    ocChart α q Λ m φ hφ l₂ t y =
      ocChart α q Λ m φ hφ l₁ t (ocTransition α q Λ m φ hφ l₁ l₂ y) := by
  exact (Infra.Flow.flow_group_law (streamVel φ) hφ.vel_lipschitz
    (AVenhance.flow_isFlow (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz)
    y ((l₂ : ℝ) * ocTauPP α q Λ m) ((l₁ : ℝ) * ocTauPP α q Λ m) t).symm

theorem jacMatrix_comp {f g : Vec 2 → Vec 2} (y : Vec 2)
    (hf : DifferentiableAt ℝ f (g y)) (hg : DifferentiableAt ℝ g y) :
    jacMatrix (f ∘ g) y = jacMatrix f (g y) * jacMatrix g y := by
  ext i j
  rw [jacMatrix, Matrix.of_apply, fderiv_comp y hf hg]
  change (fderiv ℝ f (g y)) ((fderiv ℝ g y) (basisVec j)) i = _
  rw [linearMap_apply_two]
  simp [Matrix.mul_apply, Fin.sum_univ_two, jacMatrix]

theorem streamFlow_jacMatrix_det_one {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (t s : ℝ) (y : Vec 2) :
    (jacMatrix (fun x => AVRegularity.streamFlow φ hφ t x s) y).det = 1 := by
  have hdet := Infra.Flow.flow_spatial_jacobian_det_eq_one_of_divergence_free
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ)
    (AVenhance.flow_isFlow (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz)
    (fun u x => streamVel_spatialDivergence_eq_zero hφ u x) y s t
  rw [continuousLinearMap_det_two] at hdet
  simpa only [Matrix.det_fin_two, jacMatrix, Matrix.of_apply, AVRegularity.streamFlow] using hdet

theorem transition_jacMatrix_det_one (α q : ℝ) (Λ m : ℕ) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (l₁ l₂ : ℤ) (y : Vec 2) :
    (jacMatrix (ocTransition α q Λ m φ hφ l₁ l₂) y).det = 1 :=
  streamFlow_jacMatrix_det_one hφ _ _ y

theorem chart_transition_jacMatrix (α q : ℝ) (Λ m : ℕ) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (l₁ l₂ : ℤ) (t : ℝ) (y : Vec 2) :
    jacMatrix (ocChart α q Λ m φ hφ l₂ t) y =
      jacMatrix (ocChart α q Λ m φ hφ l₁ t) (ocTransition α q Λ m φ hφ l₁ l₂ y) *
        jacMatrix (ocTransition α q Λ m φ hφ l₁ l₂) y := by
  have hcomp : ocChart α q Λ m φ hφ l₂ t =
      ocChart α q Λ m φ hφ l₁ t ∘ ocTransition α q Λ m φ hφ l₁ l₂ :=
    funext (chart_transition_comp α q Λ m hφ l₁ l₂ t)
  rw [hcomp]
  apply jacMatrix_comp
  · exact (streamFlow_spatial_smooth hφ t _).differentiable (by simp) _
  · exact (streamFlow_spatial_smooth hφ _ _).differentiable (by simp) _

theorem metric_transition (α q : ℝ) (Λ m : ℕ) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (l₁ l₂ : ℤ) (t : ℝ) (y : Vec 2) :
    ocMaterialMetric α q Λ m φ hφ l₂ t y =
      (jacMatrix (ocTransition α q Λ m φ hφ l₁ l₂) y)⁻¹ *
        ocMaterialMetric α q Λ m φ hφ l₁ t (ocTransition α q Λ m φ hφ l₁ l₂ y) *
          ((jacMatrix (ocTransition α q Λ m φ hφ l₁ l₂) y)⁻¹)ᵀ := by
  unfold ocMaterialMetric
  rw [chart_transition_jacMatrix α q Λ m hφ l₁ l₂ t y, Matrix.mul_inv_rev,
    Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open Homogenization AVenhance
open AVenhance.Infra.Flow
open scoped NNReal
namespace AVRegularity.CycleReference

/-! A fixed-time chart has globally bounded derivatives by spatial periodicity. -/

theorem streamFlow_lipschitz (φ : ℝ → Vec 2 → ℝ)
    (hφ : IsAdmissibleStream φ) (t s : ℝ) :
    ∃ C : ℝ≥0, LipschitzWith C (fun x => AVRegularity.streamFlow φ hφ t x s) := by
  let F := fun x => AVRegularity.streamFlow φ hφ t x s
  let b : ℝ → Vec 2 → Vec 2 := fun _ x => F x - x
  have hfield := AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ
  have hflow := flow_isFlow _ hφ.vel_continuous hφ.vel_lipschitz
  have hper : ∀ r, IsZ2Periodic (streamVel φ r) := by
    intro r k x
    simpa using hfield.periodic 0 k r x
  have hb : SmoothPeriodicField b := by
    constructor
    · exact ((streamFlow_spatial_smooth hφ t s).comp contDiff_snd).sub contDiff_snd
    · intro n k r x
      change F (x + latticeShift k) - (x + latticeShift k) = F x - x
      have he := flow_lattice_equivariant _ hφ.vel_lipschitz hper hflow x s t k
      change F (x + latticeShift k) = F x + latticeShift k at he
      rw [he]
      abel
  obtain ⟨L, hL, hl⟩ := exists_global_spatial_lipschitz hb
  refine ⟨⟨L + 1, by positivity⟩, LipschitzWith.of_dist_le_mul ?_⟩
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  have he : F x - F y = (b 0 x - b 0 y) + (x - y) := by
    dsimp [b]
    abel
  calc
    _ = ‖(b 0 x - b 0 y) + (x - y)‖ := congrArg norm he
    _ ≤ ‖b 0 x - b 0 y‖ + ‖x - y‖ := norm_add_le _ _
    _ ≤ L * ‖x - y‖ + ‖x - y‖ := add_le_add (hl 0 x y) le_rfl
    _ = _ := by change _ = (L + 1) * ‖x - y‖; ring

theorem streamFlow_jacMatrix_bounded {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (t s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x i j,
      |jacMatrix (fun y => AVRegularity.streamFlow φ hφ t y s) x i j| ≤ C := by
  obtain ⟨C, hC⟩ := streamFlow_lipschitz φ hφ t s
  refine ⟨C, C.coe_nonneg, ?_⟩
  intro x i j
  have hd := norm_fderiv_le_of_lipschitz ℝ (x₀ := x) hC
  have he := (fderiv ℝ (fun y => AVRegularity.streamFlow φ hφ t y s) x).le_opNorm (basisVec j)
  have hi := norm_le_pi_norm (fderiv ℝ (fun y => AVRegularity.streamFlow φ hφ t y s) x (basisVec j)) i
  have hj : ‖basisVec j‖ = 1 := by simp [basisVec, Pi.norm_single]
  rw [hj, mul_one] at he
  have hi' : |jacMatrix (fun y => AVRegularity.streamFlow φ hφ t y s) x i j| ≤
      ‖fderiv ℝ (fun y => AVRegularity.streamFlow φ hφ t y s) x (basisVec j)‖ := by
    simpa only [jacMatrix, Matrix.of_apply, Real.norm_eq_abs] using hi
  exact hi'.trans (he.trans hd)

end AVRegularity.CycleReference
end
end
