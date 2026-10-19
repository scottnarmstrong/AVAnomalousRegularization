-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Construction.OcEpsilon

/-! The effective length `d_* = e√(B/ν)`. -/

@[expose] public section

namespace AVRegularity

/-- `d_* = e √(B/ν)`, `e = ε_m`. -/
noncomputable def ocDStar (q : ℝ) (Λ m : ℕ) (ν B : ℝ) : ℝ :=
  ocEpsilon q Λ m * Real.sqrt (B / ν)

end AVRegularity
