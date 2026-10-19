-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Construction.OcEpsilon
public import AVRegularity.Statements.Construction.OcDelta
/-! The renewal time `τ_m′′`, written `h_m` in display (1.4) of the paper. -/

@[expose] public section


namespace AVRegularity

/-- `τ_m′′ = 2^{-25} / ⌈ε_{m-1}^{-(2-β+2δ)}⌉`, `β = 1 + α`, used for `m ≥ 1`
(the renewal time `h_m` of display (1.4) of the paper). -/
noncomputable def ocTauPP (α q : ℝ) (Λ m : ℕ) : ℝ :=
  (2 : ℝ) ^ (-25 : ℤ) /
    (⌈ocEpsilon q Λ (m - 1) ^ (-(2 - (1 + α) + 2 * ocDelta α q))⌉₊ : ℝ)

end AVRegularity
