-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Assembly.Route.Ingredients
import AVRegularity.Applications.Global.CompactRangeMain
import AVRegularity.CycleReference.ChartDerivativeBounded
import AVRegularity.Construction.Scales.Times
import AVRegularity.Construction.Stream.NextAdmissible

/-! All terminal composition time costs vanish uniformly before choosing construction data. -/

@[expose] public noncomputable section

open AVenhance

namespace AVRegularity.EntryTerminal.Route

/-- Increasing the terminal level absorbs the preparation and both renewal quiet margins. -/
theorem deadline : DeadlineStatement := by
  intro X
  refine ⟨128, le_rfl, ?_⟩
  intro A hΛ hA CP
  let p := 2 - (1 + X.α) + 2 * ocDelta X.α X.q
  let K : ℝ := 2 ^ (26 : ℕ)
  let C : ℝ := (6 * A.Jw + (|CP| + 1) + 3 * 81 + 4) * K
  have hδ := (Scales.admissible_exponent_facts X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq).2.1
  have hp : 0 < p := by dsimp only [p]; linarith only [X.hα₁, hδ]
  have hK : 0 ≤ K := by positivity
  have hC : 0 ≤ C := by positivity
  have hT : 0 < A.T₀ := hA.2.2.2.1.2.1.trans hA.2.2.2.1.2.2.1
  obtain ⟨η, hη, hsmall⟩ := Applications.exists_small_pow hC hp hT
  obtain ⟨N, hN⟩ := Applications.eps_eventually_le X.hq.1 hΛ hη
  refine ⟨N + 2, ?_⟩
  intro M hM D hD a aM tp haM htp
  have hM2 : 2 ≤ M := by omega
  let E := ocEpsilon X.q A.Λ (M - 2)
  have hE : 0 < E := Applications.eps_pos X.hq.1 hΛ
  have hE1 : E ≤ 1 := Applications.eps_le_one X.hq.1 hΛ
  have hsum : C * E ^ p ≤ A.T₀ := hsmall E hE.le (hN (M - 2) (by omega))
  have hpp (k : ℕ) (hk : M - 1 ≤ k) : ocTauPP X.α X.q A.Λ k ≤ K * E ^ p := by
    have hh := (CycleReference.ocTauPP_asymp X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq hΛ (m := k)).2
    have he := Applications.eps_antitone X.hq.1 hΛ (show M - 2 ≤ k - 1 by omega)
    exact hh.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Applications.eps_pos X.hq.1 hΛ).le he hp.le) hK)
  have htau : ocTau X.α X.q A.Λ (M - 1) ≤ (K * 81) * E ^ p := by
    have hh := (CycleReference.ocTau_asymp X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq hΛ (m := M - 1)).2
    rw [show M - 1 - 1 = M - 2 by omega] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hE hE1 (by dsimp only [p]; linarith only [hδ]))
        (mul_nonneg hK (by norm_num)))
  have hppM := hpp M (by omega)
  have hppNext := hpp (M + 1) (by omega)
  have hppPrev := hpp (M - 1) le_rfl
  simp only [OCData.termH, hD.1, hD.2.1, hD.2.2.1] at haM htp ⊢
  have hpp0 := (Construction.Stream.ocTauPP_pos (q := X.q) (α := X.α) (m := M)
    (show 1 ≤ A.Λ by omega)).le
  have hcp : CP * ocTauPP X.α X.q A.Λ M ≤ |CP| * ocTauPP X.α X.q A.Λ M :=
    mul_le_mul_of_nonneg_right (le_abs_self CP) hpp0
  calc
    _ ≤ a + 6 * A.Jw * ocTauPP X.α X.q A.Λ (M + 1) +
        (|CP| + 1) * ocTauPP X.α X.q A.Λ M +
        3 * ocTau X.α X.q A.Λ (M - 1) + 4 * ocTauPP X.α X.q A.Λ (M - 1) := by
      linarith only [htp, haM, hcp]
    _ ≤ a + 6 * A.Jw * (K * E ^ p) + (|CP| + 1) * (K * E ^ p) +
        3 * ((K * 81) * E ^ p) + 4 * (K * E ^ p) := by
      apply add_le_add
      · apply add_le_add
        · apply add_le_add
          · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hppNext (by positivity))
          · exact mul_le_mul_of_nonneg_left hppM (by positivity)
        · exact mul_le_mul_of_nonneg_left htau (by norm_num)
      · exact mul_le_mul_of_nonneg_left hppPrev (by norm_num)
    _ = a + C * E ^ p := by dsimp only [C]; ring
    _ ≤ a + A.T₀ := add_le_add le_rfl hsum

end AVRegularity.EntryTerminal.Route
