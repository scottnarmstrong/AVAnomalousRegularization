-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
/-! Admissible fast time profiles `ζ`: the cutoff functions of display (1.2) of the paper. -/

@[expose] public section


namespace AVRegularity

/-- An even `ζ ∈ C_c^∞((-2/3, 2/3))` with `0 ≤ ζ ≤ 1`, `∑_{k ∈ ℤ} ζ(t - k) = 1` and
`∫ ζ² = 9/10` (display (1.2) of the paper). For each `t` at most two terms of the sum are
nonzero. -/
def IsFastProfile (ζ : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) ζ ∧ (∀ t, ζ (-t) = ζ t) ∧ tsupport ζ ⊆ Set.Ioo (-(2 / 3)) (2 / 3) ∧
    (∀ t, 0 ≤ ζ t ∧ ζ t ≤ 1) ∧ (∀ t, ∑' k : ℤ, ζ (t - k) = 1) ∧
    ∫ t, ζ t ^ 2 = 9 / 10

end AVRegularity
