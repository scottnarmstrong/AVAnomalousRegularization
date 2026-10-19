-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.EntryTerminal.Ingredients.PrepChart.Chart
import AVRegularity.CycleJoint.ActivePieceDimensionalSmooth
public import AVRegularity.EntryTerminal.Assembly.Prep.ModelAssembly
import AVRegularity.Construction.Scales.Times
import AVRegularity.Construction.Stream.NextAdmissible

/-! **The anchor of the capped preparation** (`PrepAnchorPart`). The endpoint of the window,
`t_p = (l₀ + 3/2) h` with `l₀ = ⌊a_M/h + 1/2⌋` and `h = τ''_M`, is the renewal boundary
`(l₀ + 1 + 1/2) h`. So it is the midpoint of the renewal quiet margin of half-width `τ'_M = h/L_M`, on
which the slow envelope vanishes (`renewal_boundary_quiet_margin`).

From `(l₀ - 1/2) h ≤ a_M < (l₀ + 1/2) h` (`prepBlock_spec`): `h ≤ t_p - a_M ≤ 2h`, so `c = 1` and
`C₁ = 2`.

The quiet margin ends before `a + T₀` at late levels: `a_M ≤ a + 6J_w τ''_{M+1}`, so
`t_p + τ'_M ≤ a + 6J_w τ''_{M+1} + 3τ''_M`, and `τ''_k ≤ 2^{26} ε_{k-1}^{2-β+2δ} → 0`
(`ocTauPP_asymp`).

At the extremes, `a_M = (l₀ - 1/2) h` gives `t_p - a_M = 2h`, while `a_M` just below
`(l₀ + 1/2) h` gives `t_p - a_M` close to `h`. The least weak window is `J_w = 1`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance

namespace AVRegularity.EntryTerminal.Ingredients

open AVRegularity.EntryTerminal.Route

/-- The weak window and the preparation fit before `T₀` at late levels. -/
theorem prepAnchor_deadline (X : TermConstruction) {Λ : ℕ} (hΛ : 128 ≤ Λ) (Jw : ℕ) {T₀ : ℝ}
    (hT : 0 < T₀) : ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      6 * Jw * ocTauPP X.α X.q Λ (M + 1) + 3 * ocTauPP X.α X.q Λ M ≤ T₀ := by
  have hδ := (Scales.admissible_exponent_facts X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq).2.1
  have hp : 0 < 2 - (1 + X.α) + 2 * ocDelta X.α X.q := by linarith only [X.hα₁, hδ]
  have hK : (0 : ℝ) < 2 ^ (26 : ℕ) := by positivity
  have hJ : (0 : ℝ) < 6 * Jw + 3 := by positivity
  obtain ⟨N, hN⟩ := EntryWeakProofs.weak_epsilon_rpow_eventually_small X.hq.1 hΛ hp
    (c := T₀ / ((6 * Jw + 3) * 2 ^ (26 : ℕ))) (by positivity)
  have hτ : ∀ k : ℕ, N + 1 ≤ k → ocTauPP X.α X.q Λ k ≤ T₀ / (6 * Jw + 3) := by
    intro k hk
    have hh := (CycleReference.ocTauPP_asymp X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq hΛ (m := k)).2
    calc ocTauPP X.α X.q Λ k
        ≤ 2 ^ (26 : ℕ) * ocEpsilon X.q Λ (k - 1) ^ (2 - (1 + X.α) + 2 * ocDelta X.α X.q) := hh
      _ ≤ 2 ^ (26 : ℕ) * (T₀ / ((6 * Jw + 3) * 2 ^ (26 : ℕ))) :=
          mul_le_mul_of_nonneg_left (hN (k - 1) (by omega)) hK.le
      _ = T₀ / (6 * Jw + 3) := by field_simp
  refine ⟨N + 1, fun M hM => ?_⟩
  have h1 := hτ (M + 1) (by omega)
  have h2 := hτ M hM
  have hJ0 : (0 : ℝ) ≤ 6 * Jw := by positivity
  calc 6 * Jw * ocTauPP X.α X.q Λ (M + 1) + 3 * ocTauPP X.α X.q Λ M
      ≤ 6 * Jw * (T₀ / (6 * Jw + 3)) + 3 * (T₀ / (6 * Jw + 3)) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hJ0) (mul_le_mul_of_nonneg_left h2 (by norm_num))
    _ = T₀ := by field_simp

/-- **The anchor of the capped preparation.** -/
theorem prepAnchor : PrepAnchorPart := by
  intro X
  refine ⟨128, le_rfl, fun PA hΛ hPA Kout => ⟨0, fun Kw Lt nW hk₀w cr _ _ _ _ _ cK CK CL Cχ kW _ _
    _ _ _ _ _ => ?_⟩⟩
  show ∃ c C₁ : ℝ, 0 < c ∧ ∀ j₀ : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    PrepAnchorAtM PA nW CL Cχ kW c C₁ j₀ M
  have hT : 0 < PA.T₀ := hPA.2.2.2.1.2.1.trans hPA.2.2.2.1.2.2.1
  obtain ⟨M₀, hM₀⟩ := prepAnchor_deadline X hΛ PA.Jw hT
  refine ⟨1, 2, one_pos, fun j₀ => ⟨M₀, fun M hM => ?_⟩⟩
  intro D hD a lawW PW Gw aM hW
  obtain ⟨hDα, hDq, hDΛ, hDζ, -, -, -⟩ := hD
  have haM : aM ≤ a + 6 * PA.Jw * ocTauPP X.α X.q PA.Λ (M + 1) := by
    have h := hW.2.1
    rwa [hDα, hDq, hDΛ] at h
  have hΛ1 : 1 ≤ PA.Λ := by omega
  have hh : 0 < ocTauPP X.α X.q PA.Λ M := Construction.Stream.ocTauPP_pos hΛ1
  have hL : (1 : ℝ) ≤ ocL X.α X.q PA.Λ M := by
    have : 1 ≤ ocL X.α X.q PA.Λ M := by unfold ocL; omega
    exact_mod_cast this
  have hw0 : 0 ≤ ocTauP X.α X.q PA.Λ M := div_nonneg hh.le (by positivity)
  have hwh : ocTauP X.α X.q PA.Λ M ≤ ocTauPP X.α X.q PA.Λ M :=
    div_le_self hh.le hL
  have hcol := CycleJointProofs.renewal_boundary_quiet_margin (α := X.α) (q := X.q) (m := M) hΛ1
    X.ζ (prepBlock (ocTauPP X.α X.q PA.Λ M) aM + 1)
  have hc : ((((prepBlock (ocTauPP X.α X.q PA.Λ M) aM + 1 : ℤ) : ℝ) + 1 / 2) *
      ocTauPP X.α X.q PA.Λ M) = prepEndpoint (ocTauPP X.α X.q PA.Λ M) aM := by
    unfold prepEndpoint
    push_cast
    ring
  rw [hc] at hcol
  obtain ⟨hlo, hhi⟩ := prepBlock_spec (aM := aM) hh
  simp only [OCData.termH, hDα, hDq, hDΛ, hDζ]
  refine ⟨prepEndpoint (ocTauPP X.α X.q PA.Λ M) aM, ocTauP X.α X.q PA.Λ M,
    hcol ⟨by linarith, by linarith⟩, ?_, ?_, hw0, hcol, ?_, rfl, le_rfl⟩
  · unfold prepEndpoint
    linarith
  · unfold prepEndpoint
    linarith
  · have h6 := hM₀ M hM
    unfold prepEndpoint
    linarith

end AVRegularity.EntryTerminal.Ingredients
