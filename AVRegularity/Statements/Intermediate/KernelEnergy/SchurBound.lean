-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic

/-! The row/column bound by `θ` of a Schur matrix: both row and column sums are at most `θ`.
Hypothesis (iii) of Proposition 7.3 of the paper is this bound with `θ = 1/8`. -/

@[expose] public noncomputable section

namespace AVRegularity

/-- All row sums and all column sums of `b` are at most `θ`. -/
def SchurBound {ι : Type*} [Fintype ι] (θ : ℝ) (b : ι → ι → ℝ) : Prop :=
  (∀ i, ∑ i', b i i' ≤ θ) ∧ (∀ i', ∑ i, b i i' ≤ θ)

end AVRegularity
