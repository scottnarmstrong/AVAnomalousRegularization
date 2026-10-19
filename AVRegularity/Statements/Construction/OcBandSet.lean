-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Construction.OcEpsilon
public import AVRegularity.Statements.Construction.OcGamma

/-! The permitted diffusivities `𝒦` of display (1.18) of the paper. -/

@[expose] public section

namespace AVRegularity

/-- `𝒦 = ⋃_{M ≥ 1} 𝒦_M`, `𝒦_M = [ε_M^{β-γ}/2, 2ε_M^{β-γ}]`, `β = 1 + α`. -/
noncomputable def ocBandSet (α q : ℝ) (Λ : ℕ) : Set ℝ :=
  ⋃ M : ℕ, ⋃ (_ : 1 ≤ M),
    Set.Icc (ocEpsilon q Λ M ^ ((1 + α) - ocGamma α q) / 2)
      (2 * ocEpsilon q Λ M ^ ((1 + α) - ocGamma α q))

end AVRegularity
