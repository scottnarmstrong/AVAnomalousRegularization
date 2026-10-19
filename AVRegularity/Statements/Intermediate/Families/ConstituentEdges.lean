-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.Constituent
public import Mathlib.Order.Interval.Finset.Nat

/-! The source edges of a family of Hilbert components `𝗁_i`: for each pair `u → v` and each
order `d`, the finite list of scalar flux constituents of that order. The constituents are kept
unmerged (positive sums before cancellation). The family has the edge `u → v` exactly when some
list is nonempty. Orders are `2 ≤ d ≤ D` by the type; the descending slots
`K_u ≥ K_v + d - 2` are a separate premise. -/

@[expose] public section

namespace AVRegularity

/-- `edge v u d`: the list of order-`d` flux constituents of the edge `u → v`, for the
orders `2 ≤ d ≤ D` only (the order range is structural, independent of the slots `K`). -/
abbrev ConstituentEdges (D : ℕ) {ι : Type*} (h : ι → Type*) [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] : Type _ :=
  ∀ (v u : ι) (d : Finset.Icc 2 D), List (Constituent d.1 (h u) (h v))

end AVRegularity
