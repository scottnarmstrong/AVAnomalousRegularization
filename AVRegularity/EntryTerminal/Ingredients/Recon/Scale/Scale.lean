-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleReference.ChartTestTransport
import AVRegularity.Applications.Global.CompactRangeMain
public import AVRegularity.EntryTerminal.Ingredients.Recon.Coarse
import Mathlib.Algebra.Order.Star.Real

@[expose] public section

section
open AVenhance AVRegularity.EntryTerminal.Route
namespace AVRegularity.EntryTerminal.Ingredients.Recon

/-! **The scales of the terminal level.** For the data of `entry_terminal_of_weak`
at a terminal level `M` large: `0 < κ_M`, `0 < κ_{M-1}` and
`ε_M ≤ √(κ_{M-1} τ''_M) ≤ ε_{M-1}` (the fine wavelength relative to the renewal radius, and the
renewal radius relative to the parent wavelength, past a constant).

Special cases:
- The constants depend only on the construction `X`, never on `Λ` or `M`.
- `M ≥ 2` is part of the threshold. -/

/-- **The scales of the terminal level.** -/
theorem reconScale_levels (X : TermConstruction) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ M₀ : ℕ, 2 ≤ M₀ ∧ ∀ M : ℕ, M₀ ≤ M →
      ∀ D : OCData, IsTermData X Λ M D → 0 < D.κ M ∧ 0 < D.κ (M - 1) ∧
        ocEpsilon D.q D.Λ M ≤ Real.sqrt (D.κ (M - 1) * ocTauPP D.α D.q D.Λ M) ∧
        Real.sqrt (D.κ (M - 1) * ocTauPP D.α D.q D.Λ M) ≤ ocEpsilon D.q D.Λ (M - 1) := by
  obtain ⟨C1, hC1, Λ1, hΛ1, h1⟩ := CycleReference.bandChain_fine_renewal_ratio X.hα₀ X.hα₁
    X.hs₀ X.hs₁ X.hq X.hζ
  obtain ⟨C2, hC2, Λ2, hΛ2, h2⟩ := CycleReference.bandChain_renewal_radius X.hα₀ X.hα₁
    X.hs₀ X.hs₁ X.hq X.hζ
  have hfacts := Scales.admissible_exponent_facts X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq
  have hp : 0 < X.q * ocGamma X.α X.q + 3 * ocDelta X.α X.q := by
    have hq0 : 0 < X.q := lt_trans zero_lt_one X.hq.1
    have := hfacts.1; have := hfacts.2.1
    positivity
  have hc : 0 < ocC X.α X.q := hfacts.2.2.2.2.2
  obtain ⟨η1, hη1, hs1⟩ := Applications.exists_small_pow (K := C1) (by linarith) hp
    (zero_lt_one : (0 : ℝ) < 1)
  obtain ⟨η2, hη2, hs2⟩ := Applications.exists_small_pow (K := C2) (by linarith) hc
    (zero_lt_one : (0 : ℝ) < 1)
  refine ⟨max Λ1 Λ2, le_trans hΛ1 (le_max_left _ _), fun Λ hΛ => ?_⟩
  have hΛ1' : Λ1 ≤ Λ := le_trans (le_max_left _ _) hΛ
  have hΛ2' : Λ2 ≤ Λ := le_trans (le_max_right _ _) hΛ
  have h128 : 128 ≤ Λ := le_trans hΛ1 hΛ1'
  obtain ⟨N, hN⟩ := Applications.eps_eventually_le X.hq.1 h128 (lt_min hη1 hη2)
  refine ⟨N + 3, by omega, fun M hM D hD => ?_⟩
  obtain ⟨hα, hq, hΛD, hζ, -, hchain, -⟩ := hD
  have hΛone : 1 ≤ Λ := by omega
  have hkap : ∀ m, m ≤ M → 0 < D.κ m := fun m hm => by
    exact CycleReference.bandChain_pos (α := X.α) (q := X.q) (Λ := Λ) (M := M) (ζ := X.ζ)
      (κ := D.κ) hΛone X.hζ hchain hm
  have hE : 0 < ocEpsilon X.q Λ (M - 1) := Applications.eps_pos X.hq.1 h128
  have hsmall : ocEpsilon X.q Λ (M - 1) ≤ min η1 η2 := hN (M - 1) (by omega)
  have hchain' : IsOCBandChain X.α X.q Λ X.ζ M D.κ := hchain
  have hB : 0 < D.κ (M - 1) := hkap (M - 1) (by omega)
  have hτ := Construction.Stream.ocTauPP_pos (α := X.α) (q := X.q) (m := M) hΛone
  have hr : 0 < ocRh X.α X.q Λ M (D.κ (M - 1)) :=
    Real.sqrt_pos.2 (mul_pos hB hτ)
  refine ⟨hkap M le_rfl, hB, ?_⟩
  simp only [hα, hq, hΛD]
  have hrh : ocRh X.α X.q Λ M (D.κ (M - 1)) =
      Real.sqrt (D.κ (M - 1) * ocTauPP X.α X.q Λ M) := rfl
  rw [← hrh]
  constructor
  · have ha := (h1 Λ hΛ1' M (by omega) D.κ hchain' M (by omega) le_rfl).2
    have hb := hs1 _ hE.le (le_trans hsmall (min_le_left _ _))
    have : ocEpsilon X.q Λ M / ocRh X.α X.q Λ M (D.κ (M - 1)) ≤ 1 :=
      le_trans ha hb
    rwa [div_le_one hr] at this
  · have ha := (h2 Λ hΛ2' M (by omega) D.κ hchain' M (by omega) le_rfl).2
    have hb := hs2 _ hE.le (le_trans hsmall (min_le_right _ _))
    have hpow : ocEpsilon X.q Λ (M - 1) ^ (1 + ocC X.α X.q) =
        ocEpsilon X.q Λ (M - 1) * ocEpsilon X.q Λ (M - 1) ^ ocC X.α X.q := by
      rw [Real.rpow_add hE, Real.rpow_one]
    calc _ ≤ C2 * ocEpsilon X.q Λ (M - 1) ^ (1 + ocC X.α X.q) := ha
      _ = ocEpsilon X.q Λ (M - 1) * (C2 * ocEpsilon X.q Λ (M - 1) ^ ocC X.α X.q) := by
          rw [hpow]; ring
      _ ≤ ocEpsilon X.q Λ (M - 1) * 1 := mul_le_mul_of_nonneg_left hb hE.le
      _ = _ := mul_one _

end AVRegularity.EntryTerminal.Ingredients.Recon
end

section
open AVenhance AVRegularity.EntryTerminal.Route AVRegularity.Construction.Residual.Presentation
namespace AVRegularity.EntryTerminal.Ingredients.Recon

/-! **The scales of the window and the dominations of the bill.** At a context with
`c_r = 1`, the scale facts of `Scale/Levels.lean` and the deadline `t_p < a + T₀`, the five terms
of the window's bill are dominated termwise by `𝔅_rec` (`reconBill`): `reconBill` is
`ε_T^{N_T}(1 + R) + (√(B/ν) + ε_T²(1 + R)) 𝔱 + G` with `R, 𝔱, G ≥ 0`, and the cleanup power
`(ε_M/ρ)^{A_cl} ≤ (ε_M/ρ)^{A_T}` because `ε_M ≤ ρ`.

Special cases:
- `A_T ≥ 1`: `A_cl = A_T` and the cleanup power is the bill's.
- `C_g = 0`: the gluing term of the bill vanishes. -/

/-- The five dominations of the bill, for abstract nonnegative terms. -/
theorem reconScale_dominations (e s T R Rac G : ℝ) (N : ℕ) (he : 0 ≤ e) (hs : 0 ≤ s)
    (hT : 0 ≤ T) (hR : 0 ≤ R) (hRac : Rac ≤ R) (hG : 0 ≤ G) :
    e ^ N ≤ e ^ N * (1 + R) + (s + e ^ 2 * (1 + R)) * T + G ∧
    s * T ≤ e ^ N * (1 + R) + (s + e ^ 2 * (1 + R)) * T + G ∧
    e ^ 2 * T ≤ e ^ N * (1 + R) + (s + e ^ 2 * (1 + R)) * T + G ∧
    e ^ N * Rac ≤ e ^ N * (1 + R) + (s + e ^ 2 * (1 + R)) * T + G ∧
    e ^ 2 * Rac * T ≤ e ^ N * (1 + R) + (s + e ^ 2 * (1 + R)) * T + G := by
  have hN : 0 ≤ e ^ N := pow_nonneg he N
  have h2 : 0 ≤ e ^ 2 := sq_nonneg e
  have hA : 0 ≤ e ^ N * (1 + R) := mul_nonneg hN (by linarith)
  have hB : 0 ≤ (s + e ^ 2 * (1 + R)) * T := mul_nonneg (by positivity) hT
  have hsT : 0 ≤ s * T := mul_nonneg hs hT
  have h2T : 0 ≤ e ^ 2 * T := mul_nonneg h2 hT
  have h3 : (s + e ^ 2 * (1 + R)) * T = s * T + e ^ 2 * T + e ^ 2 * R * T := by ring
  have h4 : 0 ≤ e ^ 2 * R * T := mul_nonneg (mul_nonneg h2 hR) hT
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · nlinarith [mul_nonneg hN hR]
  · nlinarith
  · nlinarith
  · nlinarith [mul_le_mul_of_nonneg_left hRac hN]
  · nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRac h2) hT]

section Context

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- **The body of the scale statement at a context** from the scale facts of the level. -/
theorem reconScale_body
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw
      Ce cker j₀ M) (x : TermResAux c) (hcK : 0 < cK) (h128 : 128 ≤ A.Λ) (hM2 : 2 ≤ M)
    (hk : 0 < c.D.κ M ∧ 0 < c.D.κ (M - 1) ∧
      ocEpsilon c.D.q c.D.Λ M ≤ Real.sqrt (c.D.κ (M - 1) * ocTauPP c.D.α c.D.q c.D.Λ M) ∧
      Real.sqrt (c.D.κ (M - 1) * ocTauPP c.D.α c.D.q c.D.Λ M) ≤
        ocEpsilon c.D.q c.D.Λ (M - 1))
    (cgap Cg : ℝ) (hCg : 0 ≤ Cg) (hdl : c.tp < c.a + A.T₀) : ReconScaleBody c cgap Cg := by
  obtain ⟨hα, hq, hΛD, hζ, hseq, -, -⟩ := c.data
  obtain ⟨hk1, hk2, hlo, hhi⟩ := hk
  have hone := x.one
  have hΛ : 128 ≤ c.D.Λ := hΛD ▸ h128
  have hqq : 1 < c.D.q := hq ▸ X.hq.1
  have hε : ∀ m, 0 < ocEpsilon c.D.q c.D.Λ m := fun m => Applications.eps_pos hqq hΛ
  have hρ : 0 < rRho c := lt_of_lt_of_le (hε M) hlo
  have hr : ocEpsilon c.D.q c.D.Λ M / rRho c ≤ 1 := (div_le_one hρ).2 hlo
  have hr0 : 0 ≤ ocEpsilon c.D.q c.D.Λ M / rRho c := (div_pos (hε M) hρ).le
  -- the prices
  have hfront : 0 ≤ c.frontPrice := Real.rpow_nonneg (hε (M - 1)).le _
  have hcov : 0 ≤ c.covPrice := Real.rpow_nonneg (hε (M - 1)).le _
  have hRW : 0 ≤ c.D.termRW A.σw M := Real.rpow_nonneg (hε M).le _
  have hRho : c.D.termRho cr M = rRho c := by
    simp only [OCData.termRho, hone, one_mul, OCData.termB, OCData.termH, rRho]
  have hfilter : 0 ≤ c.filterPrice :=
    add_nonneg (Real.rpow_nonneg (hε (M - 1)).le _)
      (mul_nonneg (Real.rpow_nonneg (hε M).le _)
        (pow_nonneg (div_nonneg hRW (hRho ▸ hρ.le)) _))
  have hTT : 0 ≤ rTT c := add_nonneg (add_nonneg hfront hcov) hfilter
  have hell : Real.sqrt (c.D.termEllSq M) = ocEll c.D.q c.D.Λ M (c.D.κ M) := by
    simp only [OCData.termEllSq, OCData.termNu, ocEll, OCData.eps]
    rw [Real.sqrt_div' _ hk1.le, Real.sqrt_sq (hε M).le]
  have hεc : c.D.termEpsCell cr M =
      ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / rRho c := by
    simp only [OCData.termEpsCell, OCData.termDstar, hRho, ocDStar, OCData.termB,
      OCData.termNu, OCData.eps]
  have hobs : 0 ≤ rTobs c := by
    have := hdl; simp only [rTobs]; linarith
  have hRnn : 0 ≤ Real.sqrt (rTobs c) / ocEll c.D.q c.D.Λ M (c.D.κ M) :=
    div_nonneg (Real.sqrt_nonneg _) (hell ▸ Real.sqrt_nonneg _)
  have hRle : (ocEpsilon c.D.q c.D.Λ M / rRho c) ^ rAcl A ≤
      (ocEpsilon c.D.q c.D.Λ M / rRho c) ^ A.AT :=
    pow_le_pow_of_le_one hr0 hr (le_max_right _ _)
  have hdstar : 0 ≤ ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / rRho c :=
    div_nonneg (mul_nonneg (hε M).le (Real.sqrt_nonneg _)) hρ.le
  have hbill : c.reconBill cgap Cg =
      (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / rRho c) ^ A.NT *
        (1 + Real.sqrt (rTobs c) / ocEll c.D.q c.D.Λ M (c.D.κ M) *
          (ocEpsilon c.D.q c.D.Λ M / rRho c) ^ A.AT) +
      (Real.sqrt (c.D.κ (M - 1) / c.D.κ M) +
        (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / rRho c) ^ 2 *
          (1 + Real.sqrt (rTobs c) / ocEll c.D.q c.D.Λ M (c.D.κ M) *
            (ocEpsilon c.D.q c.D.Λ M / rRho c) ^ A.AT)) * rTT c +
      (Cg * c.D.eps (M - 1) ^ (-Cg) * Real.sqrt (c.D.termEllSq M) *
        Real.sqrt ((1 + (c.a + A.T₀ - c.tp) / ocTau c.D.α c.D.q c.D.Λ M) /
          (cgap * ocTau c.D.α c.D.q c.D.Λ M)) *
        Real.exp (-(cgap * ocTau c.D.α c.D.q c.D.Λ M / Real.sqrt (c.D.termEllSq M) ^ 2))) := by
    simp only [TermResCtx.reconBill, hεc, hRho, hell, rTobs, rTT, OCData.termB, OCData.termNu,
      OCData.eps]
  have hG : 0 ≤ Cg * c.D.eps (M - 1) ^ (-Cg) * Real.sqrt (c.D.termEllSq M) *
        Real.sqrt ((1 + (c.a + A.T₀ - c.tp) / ocTau c.D.α c.D.q c.D.Λ M) /
          (cgap * ocTau c.D.α c.D.q c.D.Λ M)) *
        Real.exp (-(cgap * ocTau c.D.α c.D.q c.D.Λ M / Real.sqrt (c.D.termEllSq M) ^ 2)) := by
    have : 0 ≤ c.D.eps (M - 1) ^ (-Cg) := Real.rpow_nonneg (hε (M - 1)).le _
    positivity
  obtain ⟨d1, d2, d3, d4, d5⟩ := reconScale_dominations
    (ocDStar c.D.q c.D.Λ M (c.D.κ M) (c.D.κ (M - 1)) / rRho c)
    (Real.sqrt (c.D.κ (M - 1) / c.D.κ M)) (rTT c)
    (Real.sqrt (rTobs c) / ocEll c.D.q c.D.Λ M (c.D.κ M) *
      (ocEpsilon c.D.q c.D.Λ M / rRho c) ^ A.AT)
    (Real.sqrt (rTobs c) / ocEll c.D.q c.D.Λ M (c.D.κ M) *
      (ocEpsilon c.D.q c.D.Λ M / rRho c) ^ rAcl A) _ A.NT hdstar (Real.sqrt_nonneg _) hTT
    (mul_nonneg hRnn (pow_nonneg hr0 _)) (mul_le_mul_of_nonneg_left hRle hRnn) hG
  have hcK' : 0 < min cK 1 := lt_min hcK one_pos
  have hobs' : 0 ≤ rTT c := hTT
  have hseq' : IsOCStreamSeq c.D.α c.D.q c.D.Λ c.D.ζ c.D.Φ := by
    rw [hα, hq, hΛD, hζ]; exact hseq
  refine ⟨hα ▸ X.hα₀, hα ▸ X.hα₁, X.hs₀, by rw [hα]; exact X.hs₁,
    by rw [hα, hq]; exact X.hq, by rw [hζ]; exact X.hζ, hΛ, hseq', hM2, hk1, hk2, hε M, hlo, hhi,
    mul_pos hcK' (hε M), hobs', ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbill]; exact d1
  · rw [hbill]; exact d2
  · rw [hbill]; exact d3
  · rw [hbill]; exact d4
  · rw [hbill]; exact d5

end Context

/-- **The scales of the window and the dominations of the bill.** -/
theorem termReconScale : TermReconScaleStatement := by
  intro ℓ X
  obtain ⟨Λ₁, hΛ₁, hlev⟩ := reconScale_levels X
  refine ⟨Λ₁, hΛ₁, fun A hΛ hV => ?_⟩
  obtain ⟨M₁, hM₁, hM₁'⟩ := hlev A.Λ hΛ
  refine ⟨0, fun kc _ => ⟨0, 0, 0, fun sXT sZT _ _ Kout _ => ⟨0, ?_⟩⟩⟩
  intro Kw Lt nW hk₀w _ cr kS _ _ _ _ _ _ _ _ _ _ _ _ _ _ cK CK CL Cχ Cread Cid kW hcK _ _
    cP CP cHP Cw Ce cker hcP
  refine ⟨(), 1, 1, le_rfl, one_pos, fun j₀ _ => ⟨M₁, fun M hM c x => ?_⟩⟩
  intro cgap Cg _ hCg hdl
  exact reconScale_body c x hcK (le_trans hΛ₁ hΛ) (le_trans hM₁ hM)
    (hM₁' M hM c.D c.data) cgap Cg hCg hdl

end AVRegularity.EntryTerminal.Ingredients.Recon
end
