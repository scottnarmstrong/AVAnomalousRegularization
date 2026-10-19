-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Construction.OcEpsilon

/-! The memory rate `μ = 4π²ν/e²`. -/

@[expose] public section

namespace AVRegularity

/-- `μ = 4π²ν/e²` with `e = ε_m` and `ν > 0` the molecular diffusivity at level `m`. -/
noncomputable def ocMu (q : ℝ) (Λ m : ℕ) (ν : ℝ) : ℝ :=
  4 * Real.pi ^ 2 * ν / ocEpsilon q Λ m ^ 2

end AVRegularity
