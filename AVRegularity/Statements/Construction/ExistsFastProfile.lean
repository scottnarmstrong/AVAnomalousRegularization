-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.Construction.ExistsFastProfile
public import AVRegularity.Statements.Construction.IsFastProfile

/-! Existence of a fast time profile: a cutoff function `ζ` as in display (1.2) of the paper. -/

@[expose] public section

namespace AVRegularity

/-- An admissible fast profile `ζ` (display (1.2) of the paper) exists. -/
theorem exists_isFastProfile : ∃ ζ : ℝ → ℝ, IsFastProfile ζ :=
  by exact AVRegularity.Providers.exists_isFastProfile

end AVRegularity
