-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Mathlib.Data.Nat.Notation

/-! The descending Sobolev order of the response `U_{i,h}` of the coarse family,
`K_{i,h} = k + (J + H + 2 - i - h) L`. For `i ≤ J`, `h ≤ H` the factor `J + H + 2 - i - h` is a
genuine (never truncated) difference at least `2`. -/

@[expose] public section

namespace AVRegularity

/-- `K_{i,h} = k + (J + H + 2 - i - h) * L` (natural-number subtraction, exact for `i ≤ J`, `h ≤ H`). -/
def coarseSlot (k J H L i h : ℕ) : ℕ :=
  k + (J + H + 2 - i - h) * L

end AVRegularity
