-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic


/-! The Schur row/column condition on the Schur matrix:
`max{sup_i ∑_{i'} b_{ii'}, sup_{i'} ∑_i b_{ii'}} ≤ 1/8`. -/

@[expose] public noncomputable section

namespace AVRegularity

/-- All row sums and all column sums of `b` are at most `1/8` (equivalent to the
`max`-of-`sup`s form over a finite index type, without `iSup` junk on an empty type). -/
def SchurCondition {ι : Type*} [Fintype ι] (b : ι → ι → ℝ) : Prop :=
  (∀ i, ∑ i', b i i' ≤ 1 / 8) ∧ (∀ i', ∑ i, b i i' ≤ 1 / 8)

end AVRegularity
