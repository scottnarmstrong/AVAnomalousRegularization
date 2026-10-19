-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Construction.OcEpsilon

/-! The factor `a_m = ε_m^{β-2}`. -/

@[expose] public section

namespace AVRegularity

/-- `a_m = ε_m^{β-2}`, `β = 1 + α`; `a_0 = 1` since `ε_0 = 1`. -/
noncomputable def ocA (α q : ℝ) (Λ m : ℕ) : ℝ := ocEpsilon q Λ m ^ ((1 + α) - 2)

end AVRegularity
