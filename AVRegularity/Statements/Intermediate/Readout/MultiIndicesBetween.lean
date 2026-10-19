-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Pi

/-! The finite set of two-dimensional multi-indices `α` with `a ≤ |α| ≤ b` (for instance the index
sets `1 ≤ |α| ≤ K` and `|α| ≤ n`). -/

@[expose] public section

namespace AVRegularity

/-- `{α ∈ ℕ² : a ≤ α₀ + α₁ ≤ b}`, as a finset. -/
def multiIndicesBetween (a b : ℕ) : Finset (Fin 2 → ℕ) :=
  (Fintype.piFinset fun _ : Fin 2 => Finset.range (b + 1)).filter
    fun α => a ≤ α 0 + α 1 ∧ α 0 + α 1 ≤ b

end AVRegularity
