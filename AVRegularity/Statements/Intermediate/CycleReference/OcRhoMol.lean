-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Construction.OcA

/-! The molecular error radius `ρ_* = ρ_mol = c_mol √(ν/a_m)`. -/

@[expose] public section

namespace AVRegularity

/-- `ρ_* = c_mol √(ν / a_m)`. -/
noncomputable def ocRhoMol (α q : ℝ) (Λ m : ℕ) (cMol ν : ℝ) : ℝ :=
  cMol * Real.sqrt (ν / ocA α q Λ m)

end AVRegularity
