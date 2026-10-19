-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Construction.OcTau

/-! The lift window of the pulse `k`, the physical time interval `[(k-61/48)τ_m, (k+61/48)τ_m]`
around its slot (the window of display (9.2) of the paper). The pulse is supported in
`|t-kτ_m| ≤ 2τ_m/3` and the enlarged pulses of `scalar_package_interior` are `|t-kτ_m| ≤ 3τ_m/4`;
the odd slots are `2τ_m` apart. The windows are the enlarged pulse plus a quiet margin of
`25τ_m/48`: they contain no other pulse (neighbours are active only from `(k+4/3)τ_m`) and
neighbouring windows overlap in the quiet interval `[(k+35/48)τ_m, (k+61/48)τ_m]`, where the time
partition transitions. -/

@[expose] public noncomputable section

namespace AVRegularity

/-- `[(k-61/48)τ_m, (k+61/48)τ_m]`. -/
def ocPulseWindow (α q : ℝ) (Λ m : ℕ) (k : ℤ) : Set ℝ :=
  Set.Icc (((k : ℝ) - 61 / 48) * ocTau α q Λ m) (((k : ℝ) + 61 / 48) * ocTau α q Λ m)

end AVRegularity
