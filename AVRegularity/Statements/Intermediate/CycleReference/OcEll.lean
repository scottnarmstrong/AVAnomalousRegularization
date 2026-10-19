-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Construction.OcEpsilon

/-! The cell length `ℓ = e/√ν`. -/

@[expose] public section

namespace AVRegularity

/-- `ℓ = e/√ν`, `e = ε_m`. -/
noncomputable def ocEll (q : ℝ) (Λ m : ℕ) (ν : ℝ) : ℝ := ocEpsilon q Λ m / Real.sqrt ν

end AVRegularity
