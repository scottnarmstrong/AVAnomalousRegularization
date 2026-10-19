-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Construction.OcEpsilon
public import AVRegularity.Statements.Construction.OcGamma

/-! The single permitted band `𝒦_M` of display (1.18) of the paper. -/

@[expose] public section

namespace AVRegularity

/-- `𝒦_M = [ε_M^{β-γ}/2, 2ε_M^{β-γ}]`, `β = 1 + α`; the union over `M ≥ 1` is `ocBandSet`. -/
noncomputable def ocBand (α q : ℝ) (Λ M : ℕ) : Set ℝ :=
  Set.Icc (ocEpsilon q Λ M ^ ((1 + α) - ocGamma α q) / 2)
    (2 * ocEpsilon q Λ M ^ ((1 + α) - ocGamma α q))

end AVRegularity
