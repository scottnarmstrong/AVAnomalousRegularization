-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
/-! The exponent `δ` of display (1.3) of the paper. -/

@[expose] public section


namespace AVRegularity

/-- `δ = (q-1)/4 · (1 - (2q+1)β/(2q+2))`, `β = 1 + α` (display (1.3) of the paper). -/
noncomputable def ocDelta (α q : ℝ) : ℝ := (q - 1) / 4 * (1 - (2 * q + 1) * (1 + α) / (2 * q + 2))

end AVRegularity
