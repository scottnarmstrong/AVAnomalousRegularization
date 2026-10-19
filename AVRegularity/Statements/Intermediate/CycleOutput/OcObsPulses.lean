-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleOutput.OcPulseWindow
public import Mathlib.Algebra.Order.Floor.Ring

/-! The odd slots whose lift window meets the observation window `[tA, tZ]` (the pulses of the local
lifts `𝒯_l` and of the time partition `ϖ_l` of the window `I`). A finite set of integers: an odd `k`
whose window `[(k-61/48)τ, (k+61/48)τ]` meets `[tA,tZ]` satisfies `⌊tA/τ⌋ - 1 ≤ k ≤ ⌈tZ/τ⌉ + 1`. -/

@[expose] public noncomputable section

namespace AVRegularity

open Classical in
/-- `{k odd | ocPulseWindow k ∩ [tA,tZ] ≠ ∅}`. -/
def ocObsPulses (α q : ℝ) (Λ m : ℕ) (tA tZ : ℝ) : Finset ℤ :=
  (Finset.Icc (⌊tA / ocTau α q Λ m⌋ - 1) (⌈tZ / ocTau α q Λ m⌉ + 1)).filter fun k =>
    Odd k ∧ (ocPulseWindow α q Λ m k ∩ Set.Icc tA tZ).Nonempty

end AVRegularity
