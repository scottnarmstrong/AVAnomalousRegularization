-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Construction.OcTau
public import AVRegularity.Statements.Intermediate.CycleJoint.OcQuietTimes

/-! The trimmed quiet times of the level-`m` pulses, the times whose closed
`τ_m/24`-neighbourhood consists of quiet times. The fields of an actual stage are fast independent
only away from the ends of a quiet interval (the mollified history of a stage reaches into the
adjacent pulse), so the premise `hquiet` of `cycle_comparison` and the producer clause of the
stage invariant assert fast independence on this set. -/

@[expose] public noncomputable section

namespace AVRegularity

/-- `{t | [t - τ_m/24, t + τ_m/24] ⊆ ocQuietTimes}` with `τ_m = ocTau α q Λ m`. -/
def ocTrimmedQuietTimes (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ) : Set ℝ :=
  {t | Set.Icc (t - ocTau α q Λ m / 24) (t + ocTau α q Λ m / 24) ⊆ ocQuietTimes α q Λ ζ m}

end AVRegularity
