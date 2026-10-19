-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
/-! The exponent `γ` of display (1.3) of the paper. -/

@[expose] public section


namespace AVRegularity

/-- `γ = (q-1)β/(q+1)`, `β = 1 + α` (display (1.3) of the paper). -/
noncomputable def ocGamma (α q : ℝ) : ℝ := (q - 1) * (1 + α) / (q + 1)

end AVRegularity
