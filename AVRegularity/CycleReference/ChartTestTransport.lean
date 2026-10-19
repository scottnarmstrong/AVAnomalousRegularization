-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleReference.ChartCorrectionIntegrability
public import AVRegularity.Statements.Intermediate.CycleReference.OcEll
public import AVRegularity.CycleReference.FluxFastDiscrepancy
import AVenhance.Infra.Parabolic.WeakUniqueness.DivergenceFreeEnergy
public import AVRegularity.Statements.Intermediate.CycleReference.OcDStar
import AVRegularity.CycleReference.MeanEnhancementScale
import AVRegularity.Construction.Scales.Times
import AVRegularity.Construction.Stream.NextAdmissible
import AVenhance.Infra.Classical.Drift
import AVenhance.Infra.Classical.GalerkinGenerator
import AVenhance.Infra.Classical.PeriodicCalculus
import AVenhance.Infra.Construction.StreamAdmissible
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

section
section
@[expose] public section
namespace AVRegularity.CycleReference

/-! Uniform contrast bound, with the separate terminal and interior conclusions. -/

theorem bandChain_contrast_bounds {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ M : ℕ, 1 ≤ M → ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
        ∀ m : ℕ, 2 ≤ m → m ≤ M →
          Real.sqrt (κ (m - 1) / κ m) ≤ C *
            ocEpsilon q Λ (m - 1) ^ (-(q * ocGamma α q)) ∧
          (m < M → ocAsymp C (Real.sqrt (κ (m - 1) / κ m))
            (ocEpsilon q Λ (m - 1) ^ (-(q * ocGamma α q)))) ∧
          (m = M → κ (m - 1) / κ m ≤ C) := by
  obtain ⟨Ci, hCi, Li, hLi, hi⟩ := bandChain_interior_contrast hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Ct, hCt, Lt, hLt, ht⟩ := bandChain_terminal_contrast hα0 hα1 hs0 hs1 hq hζ
  have hCip : 0 < Ci := by linarith
  have hCtp : 0 < Ct := by linarith
  let C := Ci + Ct + 1
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hCiC : Ci ≤ C := by dsimp [C]; linarith
  have hCtC : Ct ≤ C := by dsimp [C]; linarith
  have hCt1C : Ct + 1 ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC, max Li Lt, hLi.trans (le_max_left _ _), ?_⟩
  intro Λ hΛ M hM κ hκ m hm hmM
  have hΛi : Li ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛt : Lt ≤ Λ := (le_max_right _ _).trans hΛ
  have h128 := hLi.trans hΛi
  have he := AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 h128
  have hγ := (AVRegularity.Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq).1
  have hqγ : 0 ≤ q * ocGamma α q := mul_nonneg (by linarith [hq.1]) hγ.le
  have hpow1 : 1 ≤ ocEpsilon q Λ (m - 1) ^ (-(q * ocGamma α q)) := by
    rw [Real.rpow_neg he.1.le]
    apply (one_le_inv₀ (Real.rpow_pos_of_pos he.1 _)).2
    exact Real.rpow_le_one he.1.le he.2.1 hqγ
  have hpow0 := (Real.rpow_pos_of_pos he.1 (-(q * ocGamma α q))).le
  have hterminal (heq : m = M) : κ (m - 1) / κ m ≤ C := by
    subst m
    exact (ht Λ hΛt M (by omega) κ hκ).trans hCtC
  have hinterior (hlt : m < M) : ocAsymp C (Real.sqrt (κ (m - 1) / κ m))
      (ocEpsilon q Λ (m - 1) ^ (-(q * ocGamma α q))) :=
    asymp_mono_constant hCip hCiC hpow0 (hi Λ hΛi M hM κ hκ m hm hlt)
  refine ⟨?_, hinterior, hterminal⟩
  by_cases hlt : m < M
  · exact (hinterior hlt).2
  · have heq : m = M := by omega
    have hratio : κ (m - 1) / κ m ≤ Ct := by
      subst m
      exact ht Λ hΛt M (by omega) κ hκ
    have hs : Real.sqrt Ct ≤ Ct + 1 := by
      have hsq := Real.sq_sqrt hCtp.le
      have hn := Real.sqrt_nonneg Ct
      nlinarith
    have hbound := (Real.sqrt_le_sqrt hratio).trans (hs.trans hCt1C)
    exact hbound.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hpow1 (show 0 ≤ C by linarith))

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open Homogenization AVenhance MeasureTheory
open scoped Matrix ENNReal
namespace AVRegularity.CycleReference

/-! Spatial weak gradients under the inverse fixed-start chart. -/

theorem inverseStreamFlow_ae_weakGradient {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s a b : ℝ)
    {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    (hu : ∀ t ∈ Set.Icc a b, MemL2On Set.univ (u t))
    (hDu : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => Du p.1 p.2 i) 2
      (volume.restrict (Set.Ioo a b ×ˢ Set.univ)))
    (hw : ∀ᵐ t ∂(volume.restrict (Set.Ioo a b)),
      HasWeakGradientOn Set.univ (u t) (Du t)) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioo a b)),
      HasWeakGradientOn Set.univ (fun y => u t (AVRegularity.streamFlow φ hφ s y t))
        (fun y => (jacMatrix (fun x => AVRegularity.streamFlow φ hφ s x t) y)ᵀ.mulVec
          (Du t (AVRegularity.streamFlow φ hφ s y t))) := by
  have hs : ∀ᵐ t ∂(volume.restrict (Set.Ioo a b)),
      ∀ i : Fin 2, MemLp (fun x => Du t x i) 2 volume := by
    rw [Filter.eventually_all]
    intro i
    exact memL2_spatial_sections a b (hDu i)
  filter_upwards [hs, hw, ae_restrict_mem measurableSet_Ioo] with t ht hw htmem
  apply streamFlow_weakGradient hφ s t (hu t ⟨htmem.1.le, htmem.2.le⟩) _ hw
  intro i
  simpa only [MemL2On, Measure.restrict_univ] using ht i

end AVRegularity.CycleReference
end
end

section
@[expose] public section
namespace AVRegularity.CycleReference

/-! Relaxation-length ratios at interior and terminal levels. -/

theorem ocEll_sq_eq {q : ℝ} {Λ m : ℕ} {ν : ℝ} (hν : 0 < ν) :
    ocEll q Λ m ν ^ 2 = ocEpsilon q Λ m ^ 2 / ν := by
  rw [ocEll, div_pow, Real.sq_sqrt hν.le]

theorem bandChain_memory_scale {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ M : ℕ, 1 ≤ M → ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
        ∀ m : ℕ, 2 ≤ m → m ≤ M →
          ocEll q Λ m (κ m) ^ 2 / ocTau α q Λ m ≤
            C * ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q) ∧
          (m < M → ocAsymp C (ocEll q Λ m (κ m) ^ 2 / ocTau α q Λ m)
            (ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q))) := by
  obtain ⟨Ca, hCa, La, hLa, ha⟩ := bandChain_all_level_bounds hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Ci, hCi, Li, hLi, hi⟩ := bandChain_interior_diffusivities hα0 hα1 hs0 hs1 hq hζ
  let D := Ca + Ci
  have hD : 1 ≤ D := by dsimp [D]; linarith
  have hDp : 0 < D := by linarith
  have hCap : 0 < Ca := by linarith
  have hCip : 0 < Ci := by linarith
  have hCaD : Ca ≤ D := by dsimp [D]; linarith
  have hCiD : Ci ≤ D := by dsimp [D]; linarith
  let p := 2 - ((1 + α) + ocGamma α q)
  obtain ⟨K, hK, Lk, hLk, hk⟩ := epsilon_power_scale_asymp hq.1 p
  have hKp : 0 < K := by linarith
  let T : ℝ := 2 ^ (26 : ℕ) * 81
  have hT : 1 ≤ T := by dsimp [T]; norm_num
  have hTp : 0 < T := by linarith
  have hC : 1 ≤ (D * K) * T := by nlinarith
  refine ⟨(D * K) * T, hC, max La (max Li Lk), hLa.trans (le_max_left _ _), ?_⟩
  intro Λ hΛ M hM κ hκ m hm hmM
  have hΛa : La ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛi : Li ≤ Λ := (le_max_left _ _).trans ((le_max_right _ _).trans hΛ)
  have hΛk : Lk ≤ Λ := (le_max_right _ _).trans ((le_max_right _ _).trans hΛ)
  have h128 := hLa.trans hΛa
  have hΛ1 : 1 ≤ Λ := by omega
  have he := (AVRegularity.Scales.epsilon_basic (m := m) hq.1 h128).1
  have hE := (AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 h128).1
  have hν := bandChain_pos hΛ1 hζ hκ hmM
  have hτ := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ1
  have hnuLower : D⁻¹ * ocEpsilon q Λ m ^ ((1 + α) + ocGamma α q) ≤ κ m :=
    (mul_le_mul_of_nonneg_right ((inv_le_inv₀ hDp hCap).2 hCaD)
      (Real.rpow_pos_of_pos he _).le).trans (ha Λ hΛa M hM κ hκ m (by omega) hmM).1
  have hpower : ocEpsilon q Λ m ^ 2 / ocEpsilon q Λ m ^ ((1 + α) + ocGamma α q) =
      ocEpsilon q Λ m ^ p := by
    dsimp [p]
    rw [Real.rpow_sub he, Real.rpow_two]
  have hscale : ocAsymp K (ocEpsilon q Λ m ^ p)
      (ocEpsilon q Λ (m - 1) ^ (2 - (1 + α) + 8 * ocDelta α q)) := by
    have hexp : q * p = 2 - (1 + α) + 8 * ocDelta α q := by
      have h := memory_exponent_identity (α := α) hq.1
      dsimp [p]
      convert h using 1; ring
    simpa only [hexp] using hk Λ m hΛk hm
  have htime := ocTau_asymp hα0 hα1 hs0 hs1 hq h128 (m := m)
  have hparentPower : ocEpsilon q Λ (m - 1) ^ (2 - (1 + α) + 8 * ocDelta α q) /
      ocEpsilon q Λ (m - 1) ^ (2 - (1 + α) + 4 * ocDelta α q) =
        ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q) := by
    rw [← Real.rpow_sub hE]
    congr 1
    ring
  have hupper : ocEpsilon q Λ m ^ 2 / κ m ≤ (D * K) *
      ocEpsilon q Λ (m - 1) ^ (2 - (1 + α) + 8 * ocDelta α q) := by
    have h := quotient_upper_bound (by norm_num : (0 : ℝ) < 1) hDp
      (sq_nonneg (ocEpsilon q Λ m)) (Real.rpow_pos_of_pos he _) hν
      (show ocEpsilon q Λ m ^ 2 ≤ 1 * ocEpsilon q Λ m ^ 2 by simp) hnuLower
    simp only [one_mul, hpower] at h
    have h' := h.trans (mul_le_mul_of_nonneg_left hscale.2 hDp.le)
    simpa only [mul_assoc] using h'
  rw [ocEll_sq_eq hν]
  constructor
  · have h := quotient_upper_bound (mul_pos hDp hKp) hTp (Real.rpow_pos_of_pos hE _).le
      (Real.rpow_pos_of_pos hE _) hτ hupper htime.1
    simpa only [hparentPower] using h
  · intro hlt
    have hnu := asymp_mono_constant hCip hCiD (Real.rpow_pos_of_pos he _).le
      (hi Λ hΛi M hM κ hκ m (by omega) hlt)
    have hquot := asymp_div (by norm_num : (0 : ℝ) < 1) hDp
      (sq_nonneg (ocEpsilon q Λ m)) (Real.rpow_pos_of_pos he _) hν
      (asymp_one_self (ocEpsilon q Λ m ^ 2)) hnu
    simp only [one_mul, hpower] at hquot
    have hscaled := asymp_trans hDp hKp hquot hscale
    have h := asymp_div (mul_pos hDp hKp) hTp (Real.rpow_pos_of_pos hE _).le
      (Real.rpow_pos_of_pos hE _) hτ hscaled htime
    simpa only [hparentPower] using h

/-! The renewal preparation radius at the parent wavelength. -/

theorem bandChain_renewal_radius {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ M : ℕ, 1 ≤ M → ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
        ∀ m : ℕ, 2 ≤ m → m ≤ M →
          ocAsymp C (ocRh α q Λ m (κ (m - 1)))
            (ocEpsilon q Λ (m - 1) ^ (1 + ocC α q)) := by
  obtain ⟨Cp, hCp, Λ₀, hΛ₀, hp⟩ := bandChain_parent_comparisons hα0 hα1 hs0 hs1 hq hζ
  have hCpp : 0 < Cp := by linarith
  have hprod : 1 ≤ Cp * 2 ^ (26 : ℕ) := by nlinarith
  have hC : 1 ≤ Real.sqrt (Cp * 2 ^ (26 : ℕ)) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hprod
  refine ⟨Real.sqrt (Cp * 2 ^ (26 : ℕ)), hC, Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ M hM κ hκ m hm hmM
  have h128 := hΛ₀.trans hΛ
  have he := (AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 h128).1
  have hparent := (hp Λ hΛ M hM κ hκ m hm hmM).1
  have htime := ocTauPP_asymp hα0 hα1 hs0 hs1 hq h128 (m := m)
  have hmul := asymp_mul hCpp (by norm_num : (0 : ℝ) < 2 ^ (26 : ℕ))
    (Real.rpow_pos_of_pos he _).le (Real.rpow_pos_of_pos he _).le hparent htime
  have hexp : ocEpsilon q Λ (m - 1) ^ ((1 + α) + ocGamma α q) *
      ocEpsilon q Λ (m - 1) ^ (2 - (1 + α) + 2 * ocDelta α q) =
        ocEpsilon q Λ (m - 1) ^ (2 * (1 + ocC α q)) := by
    rw [← Real.rpow_add he]
    congr 1
    unfold ocC
    ring
  rw [hexp] at hmul
  have h := asymp_sqrt (mul_pos hCpp (by norm_num : (0 : ℝ) < 2 ^ (26 : ℕ)))
    (Real.rpow_pos_of_pos he _).le hmul
  have hsqrt : Real.sqrt (ocEpsilon q Λ (m - 1) ^ (2 * (1 + ocC α q))) =
      ocEpsilon q Λ (m - 1) ^ (1 + ocC α q) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul he.le]
    congr 1
    ring
  simpa only [ocRh, hsqrt] using h

/-! Fine wavelength relative to the renewal preparation radius. -/

theorem bandChain_fine_renewal_ratio {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ M : ℕ, 1 ≤ M → ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
        ∀ m : ℕ, 2 ≤ m → m ≤ M →
          ocAsymp C (ocEpsilon q Λ m / ocRh α q Λ m (κ (m - 1)))
            (ocEpsilon q Λ (m - 1) ^ (q * ocGamma α q + 3 * ocDelta α q)) := by
  obtain ⟨Cr, hCr, Lr, hLr, hr⟩ := bandChain_renewal_radius hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Ce, hCe, Le, hLe, he⟩ := epsilon_power_scale_asymp hq.1 1
  have hCrp : 0 < Cr := by linarith
  have hCep : 0 < Ce := by linarith
  have hC : 1 ≤ Ce * Cr := by nlinarith
  refine ⟨Ce * Cr, hC, max Lr Le, hLr.trans (le_max_left _ _), ?_⟩
  intro Λ hΛ M hM κ hκ m hm hmM
  have hΛr : Lr ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛe : Le ≤ Λ := (le_max_right _ _).trans hΛ
  have h128 := hLr.trans hΛr
  have hΛ1 : 1 ≤ Λ := by omega
  have hE := (AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 h128).1
  have hB := bandChain_pos hΛ1 hζ hκ (show m - 1 ≤ M by omega)
  have hτ := AVRegularity.Construction.Stream.ocTauPP_pos (α := α) (q := q) (m := m) hΛ1
  have hrpos : 0 < ocRh α q Λ m (κ (m - 1)) := Real.sqrt_pos.2 (mul_pos hB hτ)
  have hepsilon : ocAsymp Ce (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1) ^ q) := by
    simpa only [Real.rpow_one, mul_one] using he Λ m hΛe hm
  have h := asymp_div hCep hCrp (Real.rpow_pos_of_pos hE _).le
    (Real.rpow_pos_of_pos hE _) hrpos hepsilon (hr Λ hΛr M hM κ hκ m hm hmM)
  have hpower : ocEpsilon q Λ (m - 1) ^ q / ocEpsilon q Λ (m - 1) ^ (1 + ocC α q) =
      ocEpsilon q Λ (m - 1) ^ (q * ocGamma α q + 3 * ocDelta α q) := by
    rw [← Real.rpow_sub hE]
    congr 1
    have hid := prepared_radius_exponent_identity (α := α) hq.1
    linarith only [hid]
  simpa only [hpower] using h

/-! Conversion between the relaxation rate and the elliptic cell length. -/

theorem inverse_memory_rate_time_le {q : ℝ} {Λ m : ℕ} {ν τ : ℝ}
    (hΛ : 1 ≤ Λ) (hν : 0 < ν) (hτ : 0 < τ) :
    (ocMu q Λ m ν * τ)⁻¹ ≤ ocEll q Λ m ν ^ 2 / τ := by
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  have hπ : 1 ≤ 4 * Real.pi ^ 2 := by nlinarith only [Real.pi_gt_three]
  have hμ := ocMu_pos (q := q) (m := m) hΛ hν
  rw [ocEll_sq_eq hν]
  rw [inv_eq_one_div]
  apply (div_le_iff₀ (mul_pos hμ hτ)).2
  have he2 : ocEpsilon q Λ m ^ 2 ≠ 0 := pow_ne_zero 2 he.ne'
  have hc : (ocMu q Λ m ν * τ) * (ocEpsilon q Λ m ^ 2 / ν / τ) = 4 * Real.pi ^ 2 := by
    unfold ocMu
    field_simp
  rw [mul_comm _ (ocMu q Λ m ν * τ), hc]
  exact hπ

/-! Renewal duration relative to the molecular relaxation length. -/

theorem bandChain_renewal_relaxation {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ M : ℕ, 1 ≤ M → ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
        ∀ m : ℕ, 2 ≤ m → m ≤ M →
          C⁻¹ * ocEpsilon q Λ (m - 1) ^ (-(6 * ocDelta α q)) ≤
            ocTauPP α q Λ m / ocEll q Λ m (κ m) ^ 2 ∧
          (m < M → ocAsymp C (ocTauPP α q Λ m / ocEll q Λ m (κ m) ^ 2)
            (ocEpsilon q Λ (m - 1) ^ (-(6 * ocDelta α q)))) := by
  obtain ⟨C, hC, Λ₀, hΛ₀, hb⟩ := bandChain_memory_scale hα0 hα1 hs0 hs1 hq hζ
  have hCp : 0 < C := by linarith
  have hCC : 1 ≤ 81 * C := by linarith
  refine ⟨81 * C, hCC, Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ M hM κ hκ m hm hmM
  have h128 := hΛ₀.trans hΛ
  have hΛ1 : 1 ≤ Λ := by omega
  have he := AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 h128
  have hf := (AVRegularity.Scales.epsilon_basic (m := m) hq.1 h128).1
  have hd := (AVRegularity.Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq).2.1
  have hν := bandChain_pos hΛ1 hζ hκ hmM
  have hτ := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ1
  have hH := AVRegularity.Construction.Stream.ocTauPP_pos (α := α) (q := q) (m := m) hΛ1
  have hL : 0 < (ocL α q Λ m : ℝ) := by
    have hn : 0 < ocL α q Λ m := by unfold ocL; omega
    exact_mod_cast hn
  have hell : 0 < ocEll q Λ m (κ m) ^ 2 := by
    rw [ocEll_sq_eq hν]
    exact div_pos (sq_pos_of_pos hf) hν
  have hR : 0 < ocEll q Λ m (κ m) ^ 2 / ocTau α q Λ m := div_pos hell hτ
  have hLcompare := ocL_asymp he.1 he.2.1 hd.le
  have hL2 := asymp_rpow_nonneg (by norm_num : (0 : ℝ) < 9)
    (Real.rpow_pos_of_pos he.1 _).le (by norm_num : (0 : ℝ) ≤ 2) hLcompare
  have hL2' : ocAsymp 81 ((ocL α q Λ m : ℝ) ^ 2)
      (ocEpsilon q Λ (m - 1) ^ (-2 * ocDelta α q)) := by
    rw [Real.rpow_two, ← Real.rpow_mul he.1.le] at hL2
    have hid : (-ocDelta α q) * (2 : ℝ) = -2 * ocDelta α q := by ring
    simpa only [Real.rpow_two, hid, show (9 : ℝ) ^ (2 : ℕ) = 81 by norm_num] using hL2
  have hidentity : ocTauPP α q Λ m / ocEll q Λ m (κ m) ^ 2 =
      (ocL α q Λ m : ℝ) ^ 2 / (ocEll q Λ m (κ m) ^ 2 / ocTau α q Λ m) := by
    rw [ocTau]
    field_simp
  have hpower : ocEpsilon q Λ (m - 1) ^ (-2 * ocDelta α q) /
      ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q) =
        ocEpsilon q Λ (m - 1) ^ (-(6 * ocDelta α q)) := by
    rw [← Real.rpow_sub he.1]
    congr 1
    ring
  have hmemb := hb Λ hΛ M hM κ hκ m hm hmM
  rw [hidentity]
  constructor
  · have h := quotient_lower_bound (by norm_num : (0 : ℝ) < 81) hCp
      (Real.rpow_pos_of_pos he.1 _).le (Real.rpow_pos_of_pos he.1 _)
      (sq_nonneg (ocL α q Λ m : ℝ)) hR hL2'.1 hmemb.1
    simpa only [hpower] using h
  · intro hlt
    have h := asymp_div (by norm_num : (0 : ℝ) < 81) hCp
      (Real.rpow_pos_of_pos he.1 _).le (Real.rpow_pos_of_pos he.1 _) hR hL2' (hmemb.2 hlt)
    simpa only [hpower] using h

end AVRegularity.CycleReference
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Filter Topology
open AVenhance.Infra.Classical
open AVenhance.Infra.Torus AVenhance.Infra.Parabolic.WeakUniqueness
open AVenhance.Infra.Parabolic.FourierGalerkin
namespace AVRegularity.CycleReference

/-! Weak periodic integration by parts, by convergent Fourier projections. -/

 theorem periodicH1_smooth_cell_ibp {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (hu : IsPeriodicH1With u Du) {η : Vec 2 → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hpη : IsZ2Periodic η) (i : Fin 2) :
    (∫ x in unitCube, u x * spaceGrad η x i) =
      -∫ x in unitCube, Du x i * η x := by
  let upath : ℝ → Vec 2 → ℝ := fun _ => u
  let Dpath : ℝ → Vec 2 → Vec 2 := fun _ => Du
  let P (N : ℕ) : Vec 2 → ℝ := weakFourierModeProjection N upath 0
  let GradP (N : ℕ) : Vec 2 → ℝ := fun x => spaceGrad (P N) x i
  have hs (N : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (P N) := by
    exact (realFourierModeAmbientExpansion_contDiff N
      (weakFourierCoefficientPath N upath 0)).of_le (by simp)
  have hp (N : ℕ) : IsZ2Periodic (P N) := realFourierModeAmbientExpansion_periodic N _
  have hpm (N : ℕ) : MemL2On unitCube (P N) := weak_continuous_memL2On (hs N).continuous
  have hgm (N : ℕ) : MemL2On unitCube (GradP N) :=
    weak_continuous_memL2On ((hs N).continuous_fderiv (by simp) |>.clm_apply continuous_const)
  have hηm : MemL2On unitCube η := weak_continuous_memL2On hη.continuous
  have hdηm : MemL2On unitCube (fun x => spaceGrad η x i) :=
    weak_continuous_memL2On (hη.continuous_fderiv (by simp) |>.clm_apply continuous_const)
  have hprojVal : Tendsto (fun N =>
      (weakProjection_realCellToTorus_memLp (hpm N)).toLp (periodicToTorus (P N))) atTop
      (𝓝 ((weakProjection_realCellToTorus_memLp hu.2.2.1).toLp (periodicToTorus u))) := by
    have h := weakFourierProjectionL2_tendsto (u := upath) (t := 0) hu.2.2.1
    simpa [P, weakFourierProjectionL2_eq_expansionTransfer] using h
  have hprojGrad : Tendsto (fun N =>
      (weakProjection_realCellToTorus_memLp (hgm N)).toLp (periodicToTorus (GradP N))) atTop
      (𝓝 ((weakProjection_realCellToTorus_memLp (hu.2.2.2.1 i)).toLp
        (periodicToTorus (fun x => Du x i)))) := by
    have hu' : IsPeriodicH1With (upath 0) (Dpath 0) := hu
    have h := weakFourierProjectionGradientL2_tendsto hu' i
    have h' : Tendsto (fun N => weakFourierProjectionGradientL2 N upath 0 i) atTop
        (𝓝 ((weakProjection_realCellToTorus_memLp (hu.2.2.2.1 i)).toLp
          (periodicToTorus (fun x => Du x i)))) := by
      simpa [weakFourierProjectionGradientL2] using h
    simpa [P, GradP, weakFourierProjectionGradientL2_eq_expansionTransfer] using h'
  have hl := DivergenceFreeEnergy.divFree_cell_pairing_tendsto hpm hu.2.2.1 hdηm hprojVal
  have hr := DivergenceFreeEnergy.divFree_cell_pairing_tendsto hgm (hu.2.2.2.1 i) hηm hprojGrad
  have hfinite (N : ℕ) :
      (∫ x in unitCell 2, P N x * spaceGrad η x i) =
      -∫ x in unitCell 2, GradP N x * η x := by
    exact AVenhance.Infra.Classical.integral_unitCell_coord_ibp_real i
      ((hs N).of_le (by simp)) (hη.of_le (by simp)) (hp N) hpη
  have he := tendsto_nhds_unique hl
    (by simpa only [← hfinite] using hr.neg)
  rw [integral_unitCell_eq_unitCube, integral_unitCell_eq_unitCube] at he
  exact he

 theorem periodicH1_vector_cell_ibp {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (hu : IsPeriodicH1With u Du) (V : Vec 2 → Vec 2)
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hpV : IsZ2Periodic V) :
    (∫ x in unitCube, u x * vecDiv V x) =
      -∫ x in unitCube, Homogenization.vecDot (Du x) (V x) := by
  have hs (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun x => V x i) :=
    (contDiff_apply ℝ ℝ i).comp hV
  have hd (i : Fin 2) : Continuous (fun x => spaceGrad (fun y => V y i) x i) :=
    ((hs i).continuous_fderiv (by simp)).clm_apply continuous_const
  have hi (i : Fin 2) := hu.2.2.1.integrable_mul (weak_continuous_memL2On (hd i))
  have hdi (i : Fin 2) := (hu.2.2.2.1 i).integrable_mul
    (weak_continuous_memL2On (hs i).continuous)
  have he (i : Fin 2) := periodicH1_smooth_cell_ibp hu (hs i)
    (fun k x => congrFun (hpV k x) i) i
  change ∀ i, Integrable (fun x => u x * spaceGrad (fun y => V y i) x i)
    (volume.restrict unitCube) at hi
  change ∀ i, Integrable (fun x => Du x i * V x i) (volume.restrict unitCube) at hdi
  simp only [vecDiv, Finset.mul_sum, Homogenization.vecDot]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [he]
  rw [Finset.sum_neg_distrib]
  congr 1
  exact (integral_finsetSum _ (fun i _ => hdi i)).symm

 theorem periodicH1_divFree_cell_pairing {u η : Vec 2 → ℝ} {Du B : Vec 2 → Vec 2}
    (hu : IsPeriodicH1With u Du)
    (hB : ContDiff ℝ (⊤ : ℕ∞) B) (hpB : IsZ2Periodic B) (hdiv : ∀ x, vecDiv B x = 0)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hpη : IsZ2Periodic η) :
    (∫ x in unitCube, Homogenization.vecDot (B x) (Du x) * η x) =
      -∫ x in unitCube, u x * Homogenization.vecDot (B x) (spaceGrad η x) := by
  have hp : IsZ2Periodic (fun x => η x • B x) := by
    intro k x
    dsimp only
    rw [hpη k x, hpB k x]
  have hz := periodicH1_vector_cell_ibp hu (fun x => η x • B x) (hη.smul hB) hp
  simp_rw [vecDiv_scalar_mul hη hB, hdiv, mul_zero, add_zero] at hz
  have hleft (x : Vec 2) : Homogenization.vecDot (spaceGrad η x) (B x) =
      Homogenization.vecDot (B x) (spaceGrad η x) := by
    simp [Homogenization.vecDot, mul_comm]
  have hright (x : Vec 2) : Homogenization.vecDot (Du x) (η x • B x) =
      Homogenization.vecDot (B x) (Du x) * η x := by
    simp [Homogenization.vecDot, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
    ring
  simp_rw [hleft, hright] at hz
  linarith

 theorem periodicH1_gradient_pair_cell_integrable {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (hu : IsPeriodicH1With u Du) (V : Vec 2 → Vec 2) (hV : Continuous V) :
    Integrable (fun x => Homogenization.vecDot (Du x) (V x)) (volume.restrict unitCube) := by
  have hi (i : Fin 2) : Integrable (fun x => Du x i * V x i) (volume.restrict unitCube) :=
    (hu.2.2.2.1 i).integrable_mul
      (weak_continuous_memL2On ((continuous_apply i).comp hV))
  exact integrable_finsetSum Finset.univ (fun i _ => hi i)

 theorem periodicH1_stream_flux_cell_pairing {u ψ η : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (hu : IsPeriodicH1With u Du)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hpψ : IsZ2Periodic ψ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hpη : IsZ2Periodic η) :
    (∫ x in unitCube, Homogenization.vecDot ((ψ x • sigmaMat).mulVec (Du x)) (spaceGrad η x)) =
      ∫ x in unitCube, Homogenization.vecDot (sigmaMat.mulVec (spaceGrad ψ x)) (Du x) * η x := by
  let g := fun x => ψ x * η x
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := hψ.mul hη
  have hpg : IsZ2Periodic g := by
    intro k x
    dsimp [g]
    rw [hpψ k x, hpη k x]
  have hpV : IsZ2Periodic (fun x => sigmaMat.mulVec (spaceGrad g x)) := by
    intro k x
    have he : spaceGrad g (x + latticeShift k) = spaceGrad g x := by
      funext i
      exact Infra.Classical.periodic_spaceGrad_component hpg i k x
    dsimp only
    rw [he]
  have hz := periodicH1_vector_cell_ibp hu (fun x => sigmaMat.mulVec (spaceGrad g x))
    (rotated_gradient_smooth hg) hpV
  simp_rw [rotated_gradient_div_zero hg] at hz
  simp only [mul_zero, integral_zero] at hz
  have he (x : Vec 2) : Homogenization.vecDot (Du x) (sigmaMat.mulVec (spaceGrad g x)) =
      Homogenization.vecDot (sigmaMat.mulVec (spaceGrad ψ x)) (Du x) * η x -
        Homogenization.vecDot ((ψ x • sigmaMat).mulVec (Du x)) (spaceGrad η x) := by
    rw [show spaceGrad g x = _ from spaceGrad_mul
      (hψ.differentiable (by simp) x) (hη.differentiable (by simp) x)]
    simp [Homogenization.vecDot, Matrix.mulVec, dotProduct, Fin.sum_univ_two, sigmaMat]
    ring
  have hfirst : Integrable
      (fun x => Homogenization.vecDot (sigmaMat.mulVec (spaceGrad ψ x)) (Du x) * η x)
      (volume.restrict unitCube) := by
    have hi := periodicH1_gradient_pair_cell_integrable hu
      (fun x => η x • sigmaMat.mulVec (spaceGrad ψ x))
      (hη.continuous.smul (rotated_gradient_smooth hψ).continuous)
    convert hi using 1
    funext x
    simp [Homogenization.vecDot, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
    ring
  have hsecond : Integrable
      (fun x => Homogenization.vecDot ((ψ x • sigmaMat).mulVec (Du x)) (spaceGrad η x))
      (volume.restrict unitCube) := by
    have hi := periodicH1_gradient_pair_cell_integrable hu
      (fun x => ψ x • sigmaMat.mulVec (spaceGrad η x))
      (hψ.continuous.smul (rotated_gradient_smooth hη).continuous)
    convert hi.neg using 1
    funext x
    simp [Homogenization.vecDot, Fin.sum_univ_two, sigmaMat, Matrix.mulVec, dotProduct]
    ring
  simp_rw [he] at hz
  rw [integral_sub hfirst hsecond] at hz
  linarith

end AVRegularity.CycleReference
end
end

section
@[expose] public section
namespace AVRegularity.CycleReference

/-! The cell-corrector length relative to its parent wavelength. -/

theorem bandChain_cell_length {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ M : ℕ, 1 ≤ M → ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
        ∀ m : ℕ, 2 ≤ m → m ≤ M →
          ocDStar q Λ m (κ m) (κ (m - 1)) / ocEpsilon q Λ (m - 1) ≤
            C * ocEpsilon q Λ (m - 1) ^ (ocGamma α q / 2 + 4 * ocDelta α q) ∧
          (m < M → ocAsymp C
            (ocDStar q Λ m (κ m) (κ (m - 1)) / ocEpsilon q Λ (m - 1))
            (ocEpsilon q Λ (m - 1) ^ (ocGamma α q / 2 + 4 * ocDelta α q))) := by
  obtain ⟨Cc, hCc, Lc, hLc, hc⟩ := bandChain_contrast_bounds hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Ce, hCe, Le, hLe, he⟩ := epsilon_power_scale_asymp hq.1 1
  have hCcp : 0 < Cc := by linarith
  have hCep : 0 < Ce := by linarith
  have hC : 1 ≤ Ce * Cc := by nlinarith
  refine ⟨Ce * Cc, hC, max Lc Le, hLc.trans (le_max_left _ _), ?_⟩
  intro Λ hΛ M hM κ hκ m hm hmM
  have hΛc : Lc ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛe : Le ≤ Λ := (le_max_right _ _).trans hΛ
  have h128 := hLc.trans hΛc
  have hE := (AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 h128).1
  have hf := (AVRegularity.Scales.epsilon_basic (m := m) hq.1 h128).1
  have hepsilon : ocAsymp Ce (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1) ^ q) := by
    simpa only [Real.rpow_one, mul_one] using he Λ m hΛe hm
  have hcontrast := hc Λ hΛc M hM κ hκ m hm hmM
  have hpower : (ocEpsilon q Λ (m - 1) ^ q *
      ocEpsilon q Λ (m - 1) ^ (-(q * ocGamma α q))) / ocEpsilon q Λ (m - 1) =
        ocEpsilon q Λ (m - 1) ^ (ocGamma α q / 2 + 4 * ocDelta α q) := by
    rw [← Real.rpow_add hE]
    have h := Real.rpow_sub hE (q + -(q * ocGamma α q)) 1
    rw [Real.rpow_one] at h
    rw [← h]
    congr 1
    have hid := cell_length_exponent_identity (α := α) hq.1
    linarith only [hid]
  constructor
  · have hmul := mul_le_mul hepsilon.2 hcontrast.1
      (Real.sqrt_nonneg _) (mul_nonneg hCep.le (Real.rpow_pos_of_pos hE q).le)
    have hdiv := div_le_div_of_nonneg_right hmul hE.le
    have heq : (Ce * ocEpsilon q Λ (m - 1) ^ q *
        (Cc * ocEpsilon q Λ (m - 1) ^ (-(q * ocGamma α q)))) / ocEpsilon q Λ (m - 1) =
        (Ce * Cc) * ((ocEpsilon q Λ (m - 1) ^ q *
          ocEpsilon q Λ (m - 1) ^ (-(q * ocGamma α q))) / ocEpsilon q Λ (m - 1)) := by ring
    rw [heq, hpower] at hdiv
    exact hdiv
  · intro hlt
    have hmul := asymp_mul hCep hCcp (Real.rpow_pos_of_pos hE _).le
      (Real.rpow_pos_of_pos hE _).le hepsilon (hcontrast.2.1 hlt)
    have hself : ocAsymp 1 (ocEpsilon q Λ (m - 1)) (ocEpsilon q Λ (m - 1)) := by
      simp only [ocAsymp, inv_one, one_mul, le_refl, and_self]
    have hdiv := asymp_div (mul_pos hCep hCcp) (by norm_num : (0 : ℝ) < 1)
      (mul_nonneg (Real.rpow_pos_of_pos hE _).le (Real.rpow_pos_of_pos hE _).le)
      hE hE hmul hself
    simpa only [mul_one, hpower, ocDStar] using hdiv

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open Homogenization AVenhance
open scoped Matrix
namespace AVRegularity.CycleReference

/-! Exact cancellation of the fixed-start chart and its inverse pullbacks. -/

noncomputable def chartUnpull {E : Type*} {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) (f : ℝ → Vec 2 → E) : ℝ → Vec 2 → E :=
  fun t x => f t (AVRegularity.streamFlow φ hφ s x t)

noncomputable def chartUnpullGradient {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) (D : ℝ → Vec 2 → Vec 2) : ℝ → Vec 2 → Vec 2 :=
  fun t x => (jacMatrix (fun y => AVRegularity.streamFlow φ hφ s y t) x)ᵀ.mulVec
    (chartUnpull hφ s D t x)

theorem chartPull_chartUnpull {E : Type*} {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) (f : ℝ → Vec 2 → E) :
    chartPull hφ s (chartUnpull hφ s f) = f := by
  funext t y
  unfold chartPull chartUnpull
  exact congrArg (f t) ((streamFlowHomeomorph hφ t s).left_inv y)

theorem chartUnpull_chartPull {E : Type*} {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) (f : ℝ → Vec 2 → E) :
    chartUnpull hφ s (chartPull hφ s f) = f := by
  funext t x
  unfold chartPull chartUnpull
  exact congrArg (f t) ((streamFlowHomeomorph hφ t s).right_inv x)

theorem chartGradient_chartUnpullGradient {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) (D : ℝ → Vec 2 → Vec 2) :
    chartGradient hφ s (chartUnpullGradient hφ s D) = D := by
  funext t y
  let X := streamFlowHomeomorph hφ t s
  have hX : Differentiable ℝ (X : Vec 2 → Vec 2) := (streamFlow_spatial_smooth hφ t s).differentiable (by simp)
  have hY : Differentiable ℝ (X.symm : Vec 2 → Vec 2) := (streamFlow_spatial_smooth hφ s t).differentiable (by simp)
  have hcomp := jacMatrix_comp y (hY (X y)) (hX y)
  have he : (X.symm : Vec 2 → Vec 2) ∘ (X : Vec 2 → Vec 2) = id := by
    funext z
    exact X.symm_apply_apply z
  rw [he, jacMatrix_identity] at hcomp
  unfold chartGradient chartUnpullGradient chartPull chartUnpull chartJac
  change (jacMatrix (X : Vec 2 → Vec 2) y)ᵀ.mulVec
    ((jacMatrix (X.symm : Vec 2 → Vec 2) (X y))ᵀ.mulVec (D t (X.symm (X y)))) = D t y
  rw [X.symm_apply_apply, Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
    ← hcomp, Matrix.transpose_one, Matrix.one_mulVec]

end AVRegularity.CycleReference
end
end

section
@[expose] public section
namespace AVRegularity.CycleReference

/-! Polynomial bounds for the relaxation rate, with only actual diffusivity bounds as premises. -/

theorem memory_rate_polynomial_bounds {q : ℝ} {Λ m : ℕ} {ν C p : ℝ}
    (hΛ : 1 ≤ Λ) (hν : 0 < ν) (hC : 0 < C)
    (he1 : ocEpsilon q Λ m ≤ 1)
    (hνu : ν ≤ C) (hνl : C⁻¹ * ocEpsilon q Λ m ^ p ≤ ν) :
    ocMu q Λ m ν ≤ (4 * Real.pi ^ 2 * C) * ocEpsilon q Λ m ^ (-2 : ℝ) ∧
    (ocMu q Λ m ν)⁻¹ ≤ C * ocEpsilon q Λ m ^ (-p) := by
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  have hπ : 1 ≤ 4 * Real.pi ^ 2 := by nlinarith only [Real.pi_gt_three]
  have hνinv : ν⁻¹ ≤ C * ocEpsilon q Λ m ^ (-p) := by
    have h := (inv_le_inv₀ hν (mul_pos (inv_pos.mpr hC) (Real.rpow_pos_of_pos he p))).2 hνl
    rw [mul_inv_rev, inv_inv, ← Real.rpow_neg he.le] at h
    simpa only [mul_comm] using h
  have hμ := ocMu_pos (q := q) (m := m) hΛ hν
  constructor
  · unfold ocMu
    have h := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hνu (by positivity : 0 ≤ 4 * Real.pi ^ 2)) (sq_nonneg (ocEpsilon q Λ m))
    have hid : ocEpsilon q Λ m ^ (-2 : ℝ) = (ocEpsilon q Λ m ^ 2)⁻¹ := by
      rw [Real.rpow_neg he.le, Real.rpow_two]
    rw [hid, ← div_eq_mul_inv]
    exact h
  · have hμν : ν ≤ ocMu q Λ m ν := by
      have he2 : ocEpsilon q Λ m ^ 2 ≤ 1 := by nlinarith only [he.le, he1]
      unfold ocMu
      apply (le_div_iff₀ (sq_pos_of_pos he)).2
      have ha := mul_le_mul_of_nonneg_left he2 hν.le
      have hb := mul_le_mul_of_nonneg_right hπ hν.le
      simp only [one_mul, mul_one] at ha hb
      exact ha.trans hb
    exact ((inv_le_inv₀ hμ hν).2 hμν).trans hνinv

/-! The relaxation ratio gives the exponential tail exponent without an interior restriction. -/

theorem memory_exponential_bound {μ τ E C p : ℝ} (hμ : 0 < μ) (hτ : 0 < τ)
    (hE : 0 < E) (hC : 0 < C) (hR : (μ * τ)⁻¹ ≤ C * E ^ p) :
    Real.exp (-μ * τ / 12) ≤ Real.exp (-(1 / (12 * C)) * E ^ (-p)) := by
  have h := (inv_le_inv₀ (mul_pos hC (Real.rpow_pos_of_pos hE p))
    (inv_pos.mpr (mul_pos hμ hτ))).2 hR
  rw [inv_inv, mul_inv_rev, ← Real.rpow_neg hE.le] at h
  apply Real.exp_le_exp.mpr
  have heq : -(1 / (12 * C)) * E ^ (-p) = -(E ^ (-p) * C⁻¹) / 12 := by ring
  rw [heq]
  linarith only [h]

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open Homogenization AVenhance MeasureTheory
namespace AVRegularity.CycleReference

/-! The antisymmetric stream-flux identity integrated over a time slab. -/

theorem slab_measure_eq_prod (a b : ℝ) :
    (volume.restrict (Set.Ioo a b ×ˢ (Set.univ : Set (Vec 2)))) =
      (volume.restrict (Set.Ioo a b)).prod (volume : Measure (Vec 2)) := by
  rw [Measure.volume_eq_prod ℝ (Vec 2), ← Measure.prod_restrict, Measure.restrict_univ]

theorem slab_integral_eq_iterated {f : ℝ × Vec 2 → ℝ} {a b : ℝ}
    (hf : Integrable f (volume.restrict (Set.Ioo a b ×ˢ Set.univ))) :
    ∫ p in Set.Ioo a b ×ˢ Set.univ, f p = ∫ t in Set.Ioo a b, ∫ x, f (t, x) := by
  rw [slab_measure_eq_prod] at hf ⊢
  exact integral_prod _ hf

theorem spacetime_stream_flux_pairing (a b : ℝ)
    {u ψ η : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    (hu : ∀ t ∈ Set.Icc a b, MemL2On Set.univ (u t))
    (hDu : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => Du p.1 p.2 i) 2
      (volume.restrict (Set.Ioo a b ×ˢ Set.univ)))
    (hw : ∀ᵐ t ∂(volume.restrict (Set.Ioo a b)), HasWeakGradientOn Set.univ (u t) (Du t))
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => ψ p.1 p.2))
    (hη : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => η p.1 p.2))
    (hc : HasCompactSupport (fun p : ℝ × Vec 2 => η p.1 p.2)) :
    Integrable (fun p : ℝ × Vec 2 =>
      vecDot ((ψ p.1 p.2 • sigmaMat).mulVec (Du p.1 p.2)) (spaceGrad (η p.1) p.2))
      (volume.restrict (Set.Ioo a b ×ˢ Set.univ)) ∧
    Integrable (fun p : ℝ × Vec 2 =>
      vecDot (streamVel ψ p.1 p.2) (Du p.1 p.2) * η p.1 p.2)
      (volume.restrict (Set.Ioo a b ×ˢ Set.univ)) ∧
    (∫ p in Set.Ioo a b ×ˢ Set.univ,
      vecDot ((ψ p.1 p.2 • sigmaMat).mulVec (Du p.1 p.2)) (spaceGrad (η p.1) p.2)) =
    ∫ p in Set.Ioo a b ×ˢ Set.univ,
      vecDot (streamVel ψ p.1 p.2) (Du p.1 p.2) * η p.1 p.2 := by
  have hi := spacetime_gradient_pair_integrable hDu
    (fun i => hψ.continuous.mul (joint_rotated_gradient_smooth hη i).continuous)
    (fun i => (joint_rotated_gradient_compact hη hc i).mul_left)
  have hflux : Integrable (fun p : ℝ × Vec 2 =>
      vecDot ((ψ p.1 p.2 • sigmaMat).mulVec (Du p.1 p.2)) (spaceGrad (η p.1) p.2))
      (volume.restrict (Set.Ioo a b ×ˢ Set.univ)) := by
    convert hi.neg using 1
    funext p
    simp [vecDot, Matrix.mulVec, dotProduct, Fin.sum_univ_two, sigmaMat]
    ring
  have hd := spacetime_gradient_pair_integrable hDu
    (fun i => ((joint_rotated_gradient_smooth hψ i).continuous.mul hη.continuous))
    (fun i => hc.mul_left)
  have hdrift : Integrable (fun p : ℝ × Vec 2 =>
      vecDot (streamVel ψ p.1 p.2) (Du p.1 p.2) * η p.1 p.2)
      (volume.restrict (Set.Ioo a b ×ˢ Set.univ)) := by
    convert hd using 1
    funext p
    simp [streamVel, vecDot, Fin.sum_univ_two, Matrix.mulVec, dotProduct]
    ring
  refine ⟨hflux, hdrift, ?_⟩
  rw [slab_integral_eq_iterated hflux, slab_integral_eq_iterated hdrift]
  apply integral_congr_ae
  have hs : ∀ᵐ t ∂(volume.restrict (Set.Ioo a b)),
      ∀ i : Fin 2, MemLp (fun x => Du t x i) 2 volume := by
    rw [Filter.eventually_all]
    intro i
    exact memL2_spatial_sections a b (hDu i)
  filter_upwards [hs, hw, ae_restrict_mem measurableSet_Ioo] with t ht hw htmem
  have hul : LocallyIntegrable (u t) volume := by
    apply MemLp.locallyIntegrable _ (by norm_num : (1 : ENNReal) ≤ 2)
    simpa only [MemL2On, Measure.restrict_univ] using hu t ⟨htmem.1.le, htmem.2.le⟩
  have hDul (i : Fin 2) : LocallyIntegrable (fun x => Du t x i) volume :=
    MemLp.locallyIntegrable (ht i) (by norm_num : (1 : ENNReal) ≤ 2)
  have hψt : ContDiff ℝ (⊤ : ℕ∞) (ψ t) := hψ.comp (contDiff_const.prodMk contDiff_id)
  have hηt : ContDiff ℝ (⊤ : ℕ∞) (η t) := hη.comp (contDiff_const.prodMk contDiff_id)
  have hct : HasCompactSupport (η t) := by
    have he : Topology.IsClosedEmbedding (fun x : Vec 2 => (t, x)) := by
      refine ⟨isEmbedding_prodMkRight t, ?_⟩
      have hr : Set.range (fun x : Vec 2 => (t, x)) = {t} ×ˢ Set.univ := by
        ext p
        rcases p with ⟨r, x⟩
        simp [eq_comm]
      rw [hr]
      exact isClosed_singleton.prod isClosed_univ
    simpa only [Function.comp_def] using hc.comp_isClosedEmbedding he
  exact weak_stream_flux_pairing hul hDul hw hψt hηt hct

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open Homogenization AVenhance MeasureTheory Filter Topology
open scoped Matrix ENNReal
namespace AVRegularity.CycleReference

/-! Transport of the energy-space conditions, including the initial L² trace. -/

theorem inverseStreamFlow_energy_space {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s a b : ℝ)
    {u : ℝ → Vec 2 → ℝ} {u₀ : Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    (hu : ∀ t ∈ Set.Icc a b, MemL2On Set.univ (u t))
    (ht : ∀ t ∈ Set.Icc a b, Tendsto
      (fun r => eLpNorm (fun x => u r x - u t x) 2 volume) (𝓝[Set.Icc a b] t) (𝓝 0))
    (hinit : u a =ᵐ[volume] u₀)
    (hDu : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => Du p.1 p.2 i) 2
      (volume.restrict (Set.Ioo a b ×ˢ Set.univ)))
    (hw : ∀ᵐ t ∂(volume.restrict (Set.Ioo a b)), HasWeakGradientOn Set.univ (u t) (Du t)) :
    (∀ t ∈ Set.Icc a b, MemL2On Set.univ
      (fun x => u t (AVRegularity.streamFlow φ hφ s x t))) ∧
    (∀ t ∈ Set.Icc a b, Tendsto (fun r => eLpNorm
      (fun x => u r (AVRegularity.streamFlow φ hφ s x r) -
        u t (AVRegularity.streamFlow φ hφ s x t)) 2 volume) (𝓝[Set.Icc a b] t) (𝓝 0)) ∧
    ((fun x => u a (AVRegularity.streamFlow φ hφ s x a)) =ᵐ[volume]
      (fun x => u₀ (AVRegularity.streamFlow φ hφ s x a))) ∧
    (∀ j : Fin 2, MemLp (fun p : ℝ × Vec 2 =>
      ((jacMatrix (fun x => AVRegularity.streamFlow φ hφ s x p.1) p.2)ᵀ.mulVec
        (Du p.1 (AVRegularity.streamFlow φ hφ s p.2 p.1))) j) 2
      (volume.restrict (Set.Ioo a b ×ˢ Set.univ))) ∧
    (∀ᵐ t ∂(volume.restrict (Set.Ioo a b)), HasWeakGradientOn Set.univ
      (fun y => u t (AVRegularity.streamFlow φ hφ s y t))
      (fun y => (jacMatrix (fun x => AVRegularity.streamFlow φ hφ s x t) y)ᵀ.mulVec
        (Du t (AVRegularity.streamFlow φ hφ s y t)))) := by
  refine ⟨?_, inverseStreamFlow_L2_trace_on hφ s (Set.Icc a b) u hu ht,
    (streamFlow_measurePreserving hφ s a).quasiMeasurePreserving.ae_eq_comp hinit,
    inverseStreamFlow_joint_gradient_memL2 hφ s a b hDu,
    inverseStreamFlow_ae_weakGradient hφ s a b hu hDu hw⟩
  intro t ht
  have hu' : MemLp (u t) 2 volume := by
    simpa only [MemL2On, Measure.restrict_univ] using hu t ht
  simpa only [MemL2On, Measure.restrict_univ, Function.comp_def] using
    hu'.comp_measurePreserving (streamFlow_measurePreserving hφ s t)

end AVRegularity.CycleReference
end
end

section
@[expose] public section
namespace AVRegularity.CycleReference

/-! Real-power bookkeeping for the polynomial derivative prefactor. -/

theorem quiet_derivative_prefactor_bound {e μ α p C K : ℝ}
    (he : 0 < e) (he1 : e ≤ 1) (hα : 0 ≤ α) (hμ : 0 < μ)
    (hC : 0 < C) (hK : 0 < K)
    (hμu : μ ≤ K * e ^ (-2 : ℝ)) (hμi : μ⁻¹ ≤ C * e ^ (-p)) (a b : ℕ) :
    (2 : ℝ) ^ (b + 1) * (μ ^ a * μ⁻¹ * (2 * Real.pi * e ^ α) *
      (2 * Real.pi * e⁻¹) ^ b) ≤
    ((2 : ℝ) ^ (b + 1) * K ^ a * C * (2 * Real.pi) ^ (b + 1)) *
      e ^ (-(2 * (a : ℝ) + p + (b : ℝ))) := by
  have hAmp : 2 * Real.pi * e ^ α ≤ 2 * Real.pi := by
    have h := mul_le_mul_of_nonneg_left (Real.rpow_le_one he.le he1 hα)
      (by positivity : 0 ≤ 2 * Real.pi)
    simpa only [mul_one] using h
  have hpow := pow_le_pow_left₀ hμ.le hμu a
  have hprod : μ ^ a * μ⁻¹ * (2 * Real.pi * e ^ α) * (2 * Real.pi * e⁻¹) ^ b ≤
      (K * e ^ (-2 : ℝ)) ^ a * (C * e ^ (-p)) * (2 * Real.pi) *
        (2 * Real.pi * e⁻¹) ^ b := by
    gcongr
  have hid : (2 : ℝ) ^ (b + 1) * ((K * e ^ (-2 : ℝ)) ^ a * (C * e ^ (-p)) *
      (2 * Real.pi) * (2 * Real.pi * e⁻¹) ^ b) =
      ((2 : ℝ) ^ (b + 1) * K ^ a * C * (2 * Real.pi) ^ (b + 1)) *
        e ^ (-(2 * (a : ℝ) + p + (b : ℝ))) := by
    rw [mul_pow K, mul_pow (2 * Real.pi), ← Real.rpow_natCast (e ^ (-2 : ℝ)),
      ← Real.rpow_mul he.le, ← Real.rpow_natCast e⁻¹, Real.inv_rpow he.le,
      ← Real.rpow_neg he.le]
    have hp : e ^ ((-2 : ℝ) * (a : ℝ)) * e ^ (-p) * e ^ (-(b : ℝ)) =
        e ^ (-(2 * (a : ℝ) + p + (b : ℝ))) := by
      rw [← Real.rpow_add he, ← Real.rpow_add he]
      congr 1
      ring
    rw [show (2 : ℝ) ^ (b + 1) * (K ^ a * e ^ ((-2 : ℝ) * (a : ℝ)) *
        (C * e ^ (-p)) * (2 * Real.pi) * ((2 * Real.pi) ^ b * e ^ (-(b : ℝ)))) =
        ((2 : ℝ) ^ (b + 1) * K ^ a * C * (2 * Real.pi) ^ (b + 1)) *
          (e ^ ((-2 : ℝ) * (a : ℝ)) * e ^ (-p) * e ^ (-(b : ℝ))) by rw [pow_succ]; ring, hp]
  exact (mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ (2 : ℝ) ^ (b + 1))).trans_eq hid

end AVRegularity.CycleReference
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory
open scoped Matrix ENNReal
namespace AVRegularity.CycleReference

/-! Space-time gradient transport on the periodic cell in both directions. -/

theorem streamFlow_cell_joint_gradient_memL2 {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s a b : ℝ) {Du : ℝ → Vec 2 → Vec 2}
    (hpDu : ∀ᵐ t ∂(volume.restrict (Set.Ioo a b)), IsZ2Periodic (Du t))
    (hDu : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => Du p.1 p.2 i) 2
      (volume.restrict (Set.Ioo a b ×ˢ unitCube))) :
    ∀ j : Fin 2, MemLp (fun p : ℝ × Vec 2 =>
      ((jacMatrix (fun x => AVRegularity.streamFlow φ hφ p.1 x s) p.2)ᵀ.mulVec
        (Du p.1 (AVRegularity.streamFlow φ hφ p.1 p.2 s))) j) 2
      (volume.restrict (Set.Ioo a b ×ˢ unitCube)) := by
  let μ : Measure (ℝ × Vec 2) := volume.restrict (Set.Ioo a b ×ˢ unitCube)
  let J := fun p : ℝ × Vec 2 => jacMatrix (fun x => AVRegularity.streamFlow φ hφ p.1 x s) p.2
  obtain ⟨C, hC, hb⟩ := streamFlow_jacMatrix_bounded_on_compact_time hφ s
    (Set.Icc a b) isCompact_Icc
  have htop (i j : Fin 2) : MemLp (fun p => J p i j) ⊤ μ := by
    have hc := (continuous_apply j).comp ((continuous_apply i).comp
      (streamFlow_jacMatrix_joint_continuous hφ s))
    refine memLp_top_of_bound hc.aestronglyMeasurable C ?_
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo)))] with p hp
    rw [Real.norm_eq_abs]
    exact hb p.1 ⟨hp.1.1.le, hp.1.2.le⟩ p.2 i j
  have hcomp (i : Fin 2) : MemLp
      (fun p : ℝ × Vec 2 => Du p.1 (AVRegularity.streamFlow φ hφ p.1 p.2 s) i) 2 μ :=
    cellSlab_chart_memL2_ae hφ s a b (fun p => Du p.1 p.2 i)
      (hpDu.mono (fun t ht k x => congrFun (ht k x) i)) (hDu i)
  intro j
  have hmul (i : Fin 2) : MemLp
      (fun p : ℝ × Vec 2 => J p i j * Du p.1 (AVRegularity.streamFlow φ hφ p.1 p.2 s) i) 2 μ :=
    (htop i j).mul (hcomp i)
  have he : (fun p : ℝ × Vec 2 => ((J p)ᵀ.mulVec
      (Du p.1 (AVRegularity.streamFlow φ hφ p.1 p.2 s))) j) =
      (fun p => ∑ i : Fin 2, J p i j * Du p.1 (AVRegularity.streamFlow φ hφ p.1 p.2 s) i) := by
    funext p
    simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  change MemLp (fun p => ((J p)ᵀ.mulVec
    (Du p.1 (AVRegularity.streamFlow φ hφ p.1 p.2 s))) j) 2 μ
  rw [he]
  exact memLp_finsetSum _ (fun i _ => hmul i)

theorem inverseStreamFlow_cell_joint_gradient_memL2 {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s a b : ℝ) {Du : ℝ → Vec 2 → Vec 2}
    (hpDu : ∀ᵐ t ∂(volume.restrict (Set.Ioo a b)), IsZ2Periodic (Du t))
    (hDu : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => Du p.1 p.2 i) 2
      (volume.restrict (Set.Ioo a b ×ˢ unitCube))) :
    ∀ j : Fin 2, MemLp (fun p : ℝ × Vec 2 =>
      ((jacMatrix (fun x => AVRegularity.streamFlow φ hφ s x p.1) p.2)ᵀ.mulVec
        (Du p.1 (AVRegularity.streamFlow φ hφ s p.2 p.1))) j) 2
      (volume.restrict (Set.Ioo a b ×ˢ unitCube)) := by
  let μ : Measure (ℝ × Vec 2) := volume.restrict (Set.Ioo a b ×ˢ unitCube)
  let J := fun p : ℝ × Vec 2 => jacMatrix (fun x => AVRegularity.streamFlow φ hφ s x p.1) p.2
  obtain ⟨C, hC, hb⟩ := inverseStreamFlow_jacMatrix_bounded_on_compact_time hφ s
    (Set.Icc a b) isCompact_Icc
  have htop (i j : Fin 2) : MemLp (fun p => J p i j) ⊤ μ := by
    have hc := (continuous_apply j).comp ((continuous_apply i).comp
      (inverseStreamFlow_jacMatrix_joint_continuous hφ s))
    refine memLp_top_of_bound hc.aestronglyMeasurable C ?_
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo)))] with p hp
    rw [Real.norm_eq_abs]
    exact hb p.1 ⟨hp.1.1.le, hp.1.2.le⟩ p.2 i j
  have hcomp (i : Fin 2) : MemLp
      (fun p : ℝ × Vec 2 => Du p.1 (AVRegularity.streamFlow φ hφ s p.2 p.1) i) 2 μ :=
    cellSlab_inverseChart_memL2_ae hφ s a b (fun p => Du p.1 p.2 i)
      (hpDu.mono (fun t ht k x => congrFun (ht k x) i)) (hDu i)
  intro j
  have hmul (i : Fin 2) : MemLp
      (fun p : ℝ × Vec 2 => J p i j * Du p.1 (AVRegularity.streamFlow φ hφ s p.2 p.1) i) 2 μ :=
    (htop i j).mul (hcomp i)
  have he : (fun p : ℝ × Vec 2 => ((J p)ᵀ.mulVec
      (Du p.1 (AVRegularity.streamFlow φ hφ s p.2 p.1))) j) =
      (fun p => ∑ i : Fin 2, J p i j * Du p.1 (AVRegularity.streamFlow φ hφ s p.2 p.1) i) := by
    funext p
    simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  change MemLp (fun p => ((J p)ᵀ.mulVec
    (Du p.1 (AVRegularity.streamFlow φ hφ s p.2 p.1))) j) 2 μ
  rw [he]
  exact memLp_finsetSum _ (fun i _ => hmul i)

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open Homogenization AVenhance MeasureTheory
namespace AVRegularity.CycleReference

/-! The divergence-free weak drift identity on a time slab. -/

theorem spacetime_divFree_drift_pairing_of_integrable (a b : ℝ)
    {u η : ℝ → Vec 2 → ℝ} {Du B : ℝ → Vec 2 → Vec 2}
    (hu : ∀ t ∈ Set.Icc a b, MemL2On Set.univ (u t))
    (hDu : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => Du p.1 p.2 i) 2
      (volume.restrict (Set.Ioo a b ×ˢ Set.univ)))
    (hw : ∀ᵐ t ∂(volume.restrict (Set.Ioo a b)), HasWeakGradientOn Set.univ (u t) (Du t))
    (hB : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => B p.1 p.2))
    (hdiv : ∀ t x, vecDiv (B t) x = 0)
    (hη : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => η p.1 p.2))
    (hc : HasCompactSupport (fun p : ℝ × Vec 2 => η p.1 p.2))
    (hi : Integrable (fun p : ℝ × Vec 2 => u p.1 p.2 * vecDot (B p.1 p.2)
      (spaceGrad (η p.1) p.2)) (volume.restrict (Set.Ioo a b ×ˢ Set.univ))) :
    Integrable (fun p : ℝ × Vec 2 => vecDot (B p.1 p.2) (Du p.1 p.2) * η p.1 p.2)
      (volume.restrict (Set.Ioo a b ×ˢ Set.univ)) ∧
    (∫ p in Set.Ioo a b ×ˢ Set.univ, vecDot (B p.1 p.2) (Du p.1 p.2) * η p.1 p.2) =
      -∫ p in Set.Ioo a b ×ˢ Set.univ, u p.1 p.2 * vecDot (B p.1 p.2)
        (spaceGrad (η p.1) p.2) := by
  have hd := spacetime_gradient_pair_integrable hDu
    (fun i => (((continuous_apply i).comp hB.continuous).mul hη.continuous))
    (fun i => hc.mul_left)
  have hdrift : Integrable (fun p : ℝ × Vec 2 => vecDot (B p.1 p.2) (Du p.1 p.2) * η p.1 p.2)
      (volume.restrict (Set.Ioo a b ×ˢ Set.univ)) := by
    convert hd using 1
    funext p
    simp [vecDot, Fin.sum_univ_two]
    ring
  refine ⟨hdrift, ?_⟩
  rw [slab_integral_eq_iterated hdrift, slab_integral_eq_iterated hi, ← integral_neg]
  apply integral_congr_ae
  have hs : ∀ᵐ t ∂(volume.restrict (Set.Ioo a b)),
      ∀ i : Fin 2, MemLp (fun x => Du t x i) 2 volume := by
    rw [Filter.eventually_all]
    intro i
    exact memL2_spatial_sections a b (hDu i)
  filter_upwards [hs, hw, ae_restrict_mem measurableSet_Ioo] with t ht hw htmem
  have hul : LocallyIntegrable (u t) volume := by
    apply MemLp.locallyIntegrable _ (by norm_num : (1 : ENNReal) ≤ 2)
    simpa only [MemL2On, Measure.restrict_univ] using hu t ⟨htmem.1.le, htmem.2.le⟩
  have hDul (i : Fin 2) : LocallyIntegrable (fun x => Du t x i) volume :=
    MemLp.locallyIntegrable (ht i) (by norm_num : (1 : ENNReal) ≤ 2)
  have hBt : ContDiff ℝ (⊤ : ℕ∞) (B t) := hB.comp (contDiff_const.prodMk contDiff_id)
  have hηt : ContDiff ℝ (⊤ : ℕ∞) (η t) := hη.comp (contDiff_const.prodMk contDiff_id)
  have hct : HasCompactSupport (η t) := by
    have he : Topology.IsClosedEmbedding (fun x : Vec 2 => (t, x)) := by
      refine ⟨isEmbedding_prodMkRight t, ?_⟩
      have hr : Set.range (fun x : Vec 2 => (t, x)) = {t} ×ˢ Set.univ := by
        ext p
        rcases p with ⟨r, x⟩
        simp [eq_comm]
      rw [hr]
      exact isClosed_singleton.prod isClosed_univ
    simpa only [Function.comp_def] using hc.comp_isClosedEmbedding he
  exact weak_divFree_drift_pairing hul hDul hw hBt (hdiv t) hηt hct

end AVRegularity.CycleReference
end
end
end

section
@[expose] public section
open Homogenization AVenhance MeasureTheory
open scoped Matrix
namespace AVRegularity.CycleReference

/-! Transport of a tested equation when its chart drift correction is integrable. -/

theorem chart_test_transport_of_drift_correction_integrable
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (s ν a c : ℝ)
    (b q : ℝ → Vec 2 → Vec 2) (f θ : ℝ → Vec 2 → ℝ) (Dθ : ℝ → Vec 2 → Vec 2)
    (hu : ∀ t ∈ Set.Icc a c, MemL2On Set.univ (θ t))
    (hDu : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => Dθ p.1 p.2 i) 2
      (volume.restrict (Set.Ioo a c ×ˢ Set.univ)))
    (hw : ∀ᵐ t ∂(volume.restrict (Set.Ioo a c)), HasWeakGradientOn Set.univ (θ t) (Dθ t))
    (η : ℝ → Vec 2 → ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => η p.1 p.2))
    (hc : HasCompactSupport (fun p : ℝ × Vec 2 => η p.1 p.2))
    (hi : Integrable (fun p : ℝ × Vec 2 => θ p.1 p.2 * vecDot (streamVel φ p.1 p.2)
      (spaceGrad (η p.1) p.2)) (volume.restrict (Set.Ioo a c ×ˢ Set.univ))) :
    let Ip := planeWeakIntegrand b (fun _ _ => ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)) q f θ Dθ η
    let Im := planeWeakIntegrand (chartVector hφ s (fun t x => b t x - streamVel φ t x))
      (fun t y => ν • chartMetric hφ s t y) (chartVector hφ s q)
      (chartPull hφ s f) (chartPull hφ s θ) (chartGradient hφ s Dθ) (chartPull hφ s η)
    (Integrable Im (volume.restrict (Set.Ioo a c ×ˢ Set.univ)) ↔
      Integrable Ip (volume.restrict (Set.Ioo a c ×ˢ Set.univ))) ∧
    (Integrable Ip (volume.restrict (Set.Ioo a c ×ˢ Set.univ)) →
      ∫ p in Set.Ioo a c ×ˢ Set.univ, Im p = ∫ p in Set.Ioo a c ×ˢ Set.univ, Ip p) := by
  dsimp only
  let μ : Measure (ℝ × Vec 2) := volume.restrict (Set.Ioo a c ×ˢ Set.univ)
  let X := streamFlowTimeHomeomorph hφ s
  let Ip := planeWeakIntegrand b (fun _ _ => ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)) q f θ Dθ η
  let Im := planeWeakIntegrand (chartVector hφ s (fun t x => b t x - streamVel φ t x))
    (fun t y => ν • chartMetric hφ s t y) (chartVector hφ s q)
    (chartPull hφ s f) (chartPull hφ s θ) (chartGradient hφ s Dθ) (chartPull hφ s η)
  let K := fun p : ℝ × Vec 2 => θ p.1 p.2 * vecDot (streamVel φ p.1 p.2)
    (spaceGrad (η p.1) p.2) + vecDot (streamVel φ p.1 p.2) (Dθ p.1 p.2) * η p.1 p.2
  obtain ⟨hd, he⟩ := spacetime_divFree_drift_pairing_of_integrable a c hu hDu hw
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ).smooth
    (Infra.Classical.streamVel_vecDiv_eq_zero φ hφ) hη hc hi
  have hK : Integrable K μ := hi.add hd
  have hK0 : ∫ p, K p ∂μ = 0 := by
    rw [integral_add hi hd, he]
    ring
  have hmp := streamFlowTime_restrict_measurePreserving hφ s a c
  have hKX : Integrable (K ∘ X) μ := hmp.integrable_comp_of_integrable hK
  have hKX0 : ∫ p, K (X p) ∂μ = 0 := by
    rw [hmp.integral_comp X.measurableEmbedding K]
    exact hK0
  have hp : Im = (Ip ∘ X) - (K ∘ X) := by
    funext p
    exact planeWeakIntegrand_chart_pullback hφ s ν b q f θ Dθ η hη p.1 p.2
  have hiff := hmp.integrable_comp_emb X.measurableEmbedding (g := Ip)
  change (Integrable Im μ ↔ Integrable Ip μ) ∧ (Integrable Ip μ → _)
  constructor
  · constructor
    · intro him
      apply hiff.mp
      have he : Ip ∘ X = Im + (K ∘ X) := by rw [hp]; abel
      rw [he]
      exact him.add hKX
    · intro hip
      rw [hp]
      exact (hiff.mpr hip).sub hKX
  · intro hip
    change (∫ p, Im p ∂μ) = ∫ p, Ip p ∂μ
    rw [hp]
    simp only [Pi.sub_apply]
    rw [integral_sub (hiff.mpr hip) hKX]
    change (∫ p, Ip (X p) ∂μ) - (∫ p, K (X p) ∂μ) = _
    rw [hKX0, sub_zero, hmp.integral_comp X.measurableEmbedding Ip]

end AVRegularity.CycleReference
end
end
