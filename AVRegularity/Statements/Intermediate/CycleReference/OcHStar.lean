-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Construction.OcEpsilon

/-! The flux amplitude `H_* = e^{2β}/(2ν)`. -/

@[expose] public section

namespace AVRegularity

/-- `H_* = e^{2β}/(2ν)` with `e = ε_m`, `β = 1 + α`. -/
noncomputable def ocHStar (α q : ℝ) (Λ m : ℕ) (ν : ℝ) : ℝ :=
  ocEpsilon q Λ m ^ (2 * (1 + α)) / (2 * ν)

end AVRegularity
