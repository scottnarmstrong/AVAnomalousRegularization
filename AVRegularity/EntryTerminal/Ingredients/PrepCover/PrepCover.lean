-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Assembly.Prep.ModelAssembly
public import AVRegularity.Construction.WindowCover.WindowCoverGen
import AVRegularity.Construction.EntryScales.TerminalCore
import Mathlib.Algebra.Ring.IsFormallyReal

/-! **The cover part of the capped preparation** (`PrepCoverPart`). It is the instance of the level-generic window
cover `windowCoverGen` (`Construction/WindowCover/WindowCoverGen.lean`) at `m = M' = M = D.term`,


The frame data:
- `ν = κ_M`, `B = κ_{M-1}`, `Φ = D.Φ` and `t_S = a_M`;
- the constants `c_cov = windowCoverRadiusCap`, `C_b = windowCoverCb`, `C_G = windowCoverCG`,
  `B₀ = 4π` and `λ = 1`;
- `g = windowCoverCg · a_{M-1} τ''_M` and `a = windowCoverCd · a_M ε_M² / κ_M`, the frame's lower
  bounds.

The frame's first block `⌊a_M/h + 1/2⌋` is `prepBlock h a_M`, and its block count does not depend
on the radius.

The smallness premises, at `M ≥ M₀`:
- `g ≤ g₀`: `weak_anchor_product_eventually_small`.
- `ρ_s ≤ √(κ_{M-1} τ''_M)`: `ρ_s ≤ ε_M` (the cap is at most `1`), and
  `ε_M² ≤ C ε_{M-1}^{2(qγ+3δ)} κ_M τ''_M ≤ κ_{M-1} τ''_M` by `terminal_scales_core` at `c_r = 1`.
- The drift smallness: `a = windowCoverCd · ε_M^{1+α}/κ_M ≤ windowCoverCd · C ε_M^γ ≤ 1/4`, and
  `4π · ρ_s/ε_M ≤ 1/2` because the cap is at most `1/(8π)`.

For `ρ_s = c_cov ε_M` the radius equals its cap. If `a_M = (l₀ - 1/2) h` then `P = 2`, and
otherwise `P = 3`. The least level the frame allows is `M = 2`, which lies inside the threshold.
For `q_J = K_max = 0` the constants do not depend on the jet requests. -/

@[expose] public noncomputable section

open Homogenization AVenhance

namespace AVRegularity.EntryTerminal.Ingredients

open AVRegularity.EntryTerminal.Route AVRegularity.Construction.WindowCover

/-- `x^{b-2} x² = x^b`. -/
theorem prepCover_rpow_sub_two_mul_sq {x : ℝ} (hx : 0 < x) (b : ℝ) :
    x ^ (b - 2) * x ^ 2 = x ^ b := by
  rw [Real.rpow_sub hx, Real.rpow_two, div_mul_cancel₀ _ (pow_ne_zero 2 hx.ne')]

/-- The radius premise from the comparison `C⁻¹ y⁻¹ ≤ τ/(x²/κ_M)` and `C y ≤ 1`. -/
theorem prepCover_le_sqrt {x y C τ κM κB : ℝ} (hx : 0 < x) (hy : 0 < y) (hC : 0 < C)
    (hκ : 0 < κM) (hκMB : κM ≤ κB) (hτ : 0 < τ) (h : C⁻¹ * y⁻¹ ≤ τ / (x ^ 2 / κM))
    (hCy : C * y ≤ 1) : x ≤ Real.sqrt (κB * τ) := by
  have h1 : τ / (x ^ 2 / κM) = τ * κM / x ^ 2 := by field_simp
  rw [h1, le_div_iff₀ (by positivity)] at h
  have e : x ^ 2 = (C⁻¹ * y⁻¹ * x ^ 2) * (C * y) := by field_simp
  have h2 : x ^ 2 ≤ κB * τ := by
    calc x ^ 2 = (C⁻¹ * y⁻¹ * x ^ 2) * (C * y) := e
      _ ≤ (τ * κM) * 1 := mul_le_mul h hCy (by positivity) (by positivity)
      _ = τ * κM := mul_one _
      _ ≤ τ * κB := mul_le_mul_of_nonneg_left hκMB hτ.le
      _ = κB * τ := mul_comm _ _
  calc x = Real.sqrt (x ^ 2) := (Real.sqrt_sq hx.le).symm
    _ ≤ Real.sqrt (κB * τ) := Real.sqrt_le_sqrt h2

/-- `B₀ u ≤ 1/2` from `u ≤ cap ≤ 1/(2B₀)`. -/
theorem prepCover_driftScale {B0 cap u : ℝ} (hB0 : 0 < B0) (hcap : cap ≤ 1 / (2 * B0))
    (hu : u ≤ cap) : B0 * u ≤ 1 / 2 := by
  calc B0 * u ≤ B0 * (1 / (2 * B0)) := mul_le_mul_of_nonneg_left (hu.trans hcap) hB0.le
    _ = 1 / 2 := by field_simp

/-- `a B₀ u² ≤ 1/8` from `a ≤ 1/4`, `0 ≤ u ≤ 1` and `B₀ u ≤ 1/2`. -/
theorem prepCover_driftSmall {a B0 u : ℝ} (ha4 : a ≤ 1 / 4) (hu : 0 ≤ u)
    (hu1 : u ≤ 1) (hB0 : 0 ≤ B0) (hBu : B0 * u ≤ 1 / 2) : a * B0 * u ^ 2 ≤ 1 / 8 := by
  have e : a * B0 * u ^ 2 = a * (B0 * u) * u := by ring
  rw [e]
  calc a * (B0 * u) * u ≤ 1 / 4 * (1 / 2) * 1 :=
        mul_le_mul (mul_le_mul ha4 hBu (mul_nonneg hB0 hu) (by norm_num)) hu1 hu (by norm_num)
    _ = 1 / 8 := by norm_num

/-- `C_d · Pe ≤ 1/4` from `Pe ≤ C z` and `z ≤ (4 C_d C)⁻¹`. -/
theorem prepCover_drift_le {Cd C Pe z : ℝ} (hCd : 0 < Cd) (hC : 0 < C) (hPe : Pe ≤ C * z)
    (hz : z ≤ (4 * (Cd * C))⁻¹) : Cd * Pe ≤ 1 / 4 := by
  calc Cd * Pe ≤ Cd * (C * z) := mul_le_mul_of_nonneg_left hPe hCd.le
    _ = (Cd * C) * z := by ring
    _ ≤ (Cd * C) * (4 * (Cd * C))⁻¹ := mul_le_mul_of_nonneg_left hz (by positivity)
    _ = 1 / 4 := by field_simp

theorem windowCoverB0_pos : 0 < windowCoverB0 := by
  unfold windowCoverB0
  positivity

theorem windowCoverRadiusCap_pos : 0 < windowCoverRadiusCap := by
  unfold windowCoverRadiusCap
  have := windowCoverB0_pos
  exact lt_min one_pos (by positivity)

theorem windowCoverCd_pos : 0 < windowCoverCd := by
  unfold windowCoverCd
  exact mul_pos (by positivity) (lt_max_of_lt_left one_pos)

theorem windowCoverCg_pos : 0 < windowCoverCg := by
  unfold windowCoverCg
  have := le_max_left (78000 : ℝ) (2 * CycleComparison.Charts.metricDevConst 0)
  linarith

/-- **The cover of the capped preparation** (`PrepCoverPart`), from `windowCoverGen`. -/
theorem prepCover : PrepCoverPart := by
  intro X
  obtain ⟨ΛW, hΛW, hW⟩ := windowCoverGen X.α X.s X.q X.ζ X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq X.hζ
  obtain ⟨ΛT, -, hT⟩ := EntryScales.terminal_scales_core X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq X.hζ
  refine ⟨max ΛW ΛT, hΛW.trans (le_max_left _ _), fun PA hΛ _ g₀ hg₀ qJ Kmax => ?_⟩
  have hΛW' : ΛW ≤ PA.Λ := (le_max_left _ _).trans hΛ
  have h128 : 128 ≤ PA.Λ := hΛW.trans hΛW'
  have hΛ1 : 1 ≤ PA.Λ := by omega
  have hq1 : 1 < X.q := X.hq.1
  obtain ⟨C, M₁, hC1, hsc⟩ := hT PA.Λ ((le_max_right _ _).trans hΛ) 1 one_pos
  have hC : 0 < C := by linarith
  obtain ⟨Mg, hMg2, hMg⟩ := EntryWeakProofs.weak_anchor_product_eventually_small X.α X.s X.q
    X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq PA.Λ h128 windowCoverCg g₀ hg₀
  have hγ := (Scales.admissible_exponent_facts X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq).1
  have hδ := (Scales.admissible_exponent_facts X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq).2.1
  have hp : 0 < 2 * (X.q * ocGamma X.α X.q + 3 * ocDelta X.α X.q) := by
    have : 0 < X.q := by linarith
    positivity
  obtain ⟨Me, hMe⟩ := EntryWeakProofs.weak_epsilon_rpow_eventually_small hq1 h128 hp
    (inv_pos.mpr hC)
  have hCd := windowCoverCd_pos
  obtain ⟨Mx, hMx⟩ := EntryWeakProofs.weak_epsilon_rpow_eventually_small hq1 h128 hγ
    (c := (4 * (windowCoverCd * C))⁻¹) (by positivity)
  refine ⟨windowCoverRadiusCap, windowCoverCb, windowCoverCG, max (max M₁ Mg) (max (Me + 1) Mx),
    windowCoverRadiusCap_pos, fun M hM => ?_⟩
  have hM₁ : M₁ ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hM
  have hMg' : Mg ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hM
  have hMe' : Me ≤ M - 1 := by
    have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM
    omega
  have hMx' : Mx ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hM
  have hM2 : 2 ≤ M := hMg2.trans hMg'
  intro D hD hφ aM
  obtain ⟨-, -, -, -, hΦ, hband, -⟩ := hD
  obtain ⟨hr1, -, hpe, -, -, -, -, -, hτlo, -, -⟩ := hsc M hM₁ D.κ hband
  have hκM : 0 < D.κ M := CycleReference.bandChain_pos hΛ1 X.hζ hband le_rfl
  have hκMB : D.κ M ≤ D.κ (M - 1) := (one_le_div hκM).mp hr1
  obtain ⟨hε, hε1, -⟩ := Scales.epsilon_basic (m := M) hq1 h128
  obtain ⟨hE, -, -⟩ := Scales.epsilon_basic (m := M - 1) hq1 h128
  have hτ : 0 < ocTauPP X.α X.q PA.Λ M := Construction.Stream.ocTauPP_pos hΛ1
  -- the radius premise at the largest radius `ε_M`
  have hεR : ocEpsilon X.q PA.Λ M ≤ Real.sqrt (D.κ (M - 1) * ocTauPP X.α X.q PA.Λ M) := by
    rw [Real.rpow_neg hE.le] at hτlo
    refine prepCover_le_sqrt hε (Real.rpow_pos_of_pos hE _) hC hκM hκMB hτ hτlo ?_
    calc C * ocEpsilon X.q PA.Λ (M - 1) ^ (2 * (X.q * ocGamma X.α X.q + 3 * ocDelta X.α X.q))
        ≤ C * C⁻¹ := mul_le_mul_of_nonneg_left (hMe (M - 1) hMe') hC.le
      _ = 1 := mul_inv_cancel₀ hC.ne'
  -- the drift amplitude
  have hA : ocA X.α X.q PA.Λ M * ocEpsilon X.q PA.Λ M ^ 2 = ocEpsilon X.q PA.Λ M ^ (1 + X.α) := by
    unfold ocA
    exact prepCover_rpow_sub_two_mul_sq hε (1 + X.α)
  have hA0 : 0 ≤ ocA X.α X.q PA.Λ M := by
    unfold ocA
    exact Real.rpow_nonneg hε.le _
  have ha0 : 0 ≤ windowCoverCd * ocA X.α X.q PA.Λ M * ocEpsilon X.q PA.Λ M ^ 2 / D.κ M := by
    positivity
  have ha4 : windowCoverCd * ocA X.α X.q PA.Λ M * ocEpsilon X.q PA.Λ M ^ 2 / D.κ M ≤ 1 / 4 := by
    have e : windowCoverCd * ocA X.α X.q PA.Λ M * ocEpsilon X.q PA.Λ M ^ 2 / D.κ M =
        windowCoverCd * (ocEpsilon X.q PA.Λ M ^ (1 + X.α) / D.κ M) := by
      rw [← hA]
      ring
    rw [e]
    exact prepCover_drift_le hCd hC hpe (hMx M hMx')
  have hg0 : 0 ≤ windowCoverCg * (ocA X.α X.q PA.Λ (M - 1) * ocTauPP X.α X.q PA.Λ M) := by
    have : 0 ≤ ocA X.α X.q PA.Λ (M - 1) := by
      unfold ocA
      exact Real.rpow_nonneg hE.le _
    have := windowCoverCg_pos
    positivity
  have hB0 := windowCoverB0_pos
  have hcap1 : windowCoverRadiusCap ≤ 1 := min_le_left _ _
  have hcapB : windowCoverRadiusCap ≤ 1 / (2 * windowCoverB0) := min_le_right _ _
  refine ⟨windowCoverCg * (ocA X.α X.q PA.Λ (M - 1) * ocTauPP X.α X.q PA.Λ M),
    windowCoverCd * ocA X.α X.q PA.Λ M * ocEpsilon X.q PA.Λ M ^ 2 / D.κ M, windowCoverB0, 1,
    if aM = ((prepBlock (ocTauPP X.α X.q PA.Λ M) aM : ℝ) - 1 / 2) * ocTauPP X.α X.q PA.Λ M
      then 2 else 3, 0, fun ρs hρ hρc => ?_⟩
  have hu : ρs / ocEpsilon X.q PA.Λ M ≤ windowCoverRadiusCap := (div_le_iff₀ hε).mpr hρc
  have hu0 : 0 ≤ ρs / ocEpsilon X.q PA.Λ M := div_nonneg hρ.le hε.le
  have hBu := prepCover_driftScale hB0 hcapB hu
  let F : WindowCoverFrame X.α X.s X.q X.ζ :=
    { hα₀ := X.hα₀, hα₁ := X.hα₁, hs₀ := X.hs₀, hs₁ := X.hs₁, hq := X.hq, hζ := X.hζ,
      Λ := PA.Λ, hΛ := h128, M' := M, κ := D.κ, hband := hband, m := M, hm2 := hM2,
      hmM := le_rfl, ν := D.κ M, B := D.κ (M - 1), hν := rfl, hB := rfl, Φ := D.Φ, hΦ := hΦ,
      hφ := hφ, tS := aM, ρs := ρs,
      g := windowCoverCg * (ocA X.α X.q PA.Λ (M - 1) * ocTauPP X.α X.q PA.Λ M), g₀ := g₀,
      a := windowCoverCd * ocA X.α X.q PA.Λ M * ocEpsilon X.q PA.Λ M ^ 2 / D.κ M,
      rho_pos := hρ, rho_cap := hρc,
      rho_R := le_trans hρc ((mul_le_of_le_one_left hε.le hcap1).trans hεR),
      g_nonneg := hg0, g_upper := hMg M hMg', g_lower := le_rfl, a_nonneg := ha0,
      a_lower := le_rfl, drift_scale := hBu,
      drift_small := prepCover_driftSmall ha4 hu0 (hu.trans hcap1) hB0.le hBu }
  exact hW F hΛW' qJ Kmax 0

end AVRegularity.EntryTerminal.Ingredients
