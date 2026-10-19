-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
/-! The admissible range of `q`, display (1.1) of the paper. -/

@[expose] public section


namespace AVRegularity

/-- `1 < q < min{17/16, (2-β)/(2(β-1)), (1-s)/(β-1+s)}` with `β = 1 + α`
(display (1.1) of the paper). -/
def IsAdmissibleQ (α s q : ℝ) : Prop :=
  1 < q ∧ q < 17 / 16 ∧ q < (2 - (1 + α)) / (2 * ((1 + α) - 1)) ∧
    q < (1 - s) / ((1 + α) - 1 + s)

end AVRegularity
