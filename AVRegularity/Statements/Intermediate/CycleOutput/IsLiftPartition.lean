-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-! The time partition `ϖ_l` of the observation window (`∑ϖ_l = 1`, `|ϖ_l'| ≤ C/d_gap` supported
after a fixed fraction of each gap, gap length `d_gap ≍ τ`): the functions `ϖ_k`, `k ∈ kset`, are
nonnegative `C¹`, sum to one on the window `I`, `ϖ_k` is supported in the lift window `win k` of the
pulse, `|ϖ_k'| ≤ Cpart/τ` and `ϖ_k'` is supported in the quiet times (the transitions are inside the
gaps, where the drift vanishes). -/

@[expose] public section

namespace AVRegularity

/-- The partition conditions. -/
def IsLiftPartition (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) (win : ℤ → Set ℝ) (quiet I : Set ℝ)
    (τ Cpart : ℝ) : Prop :=
  (∀ k ∈ kset, ∀ t, 0 ≤ ϖ k t) ∧ (∀ k ∈ kset, ContDiff ℝ 1 (ϖ k)) ∧
  (∀ t ∈ I, ∑ k ∈ kset, ϖ k t = 1) ∧
  (∀ k ∈ kset, ∀ t, ϖ k t ≠ 0 → t ∈ win k) ∧
  (∀ k ∈ kset, ∀ t, |deriv (ϖ k) t| ≤ Cpart / τ) ∧
  (∀ k ∈ kset, ∀ t, deriv (ϖ k) t ≠ 0 → t ∈ quiet)

end AVRegularity
