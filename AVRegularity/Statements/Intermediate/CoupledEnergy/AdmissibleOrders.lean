-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Mathlib.Data.Finset.Filter
public import Mathlib.Order.Interval.Finset.Nat

/-! The orders `d` for which the coupling coefficient `A_{ii',d}` may be nonzero, as in
Proposition 7.6 of the paper. -/

@[expose] public section

namespace AVRegularity

/-- Orders `d ∈ [2,D]` with the reserve `K_{i'} ≥ K_i + d - 2`, i.e. `K i + d ≤ K i' + 2`.
Pairs `(i,i',d)` outside this set are the zero coefficients of the paper. -/
def admissibleOrders {ι : Type*} (K : ι → ℕ) (D : ℕ) (i i' : ι) : Finset ℕ :=
  (Finset.Icc 2 D).filter fun d => K i + d ≤ K i' + 2

end AVRegularity
