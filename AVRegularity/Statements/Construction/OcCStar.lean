-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! The short-chart constant `c_*`. -/

@[expose] public section

namespace AVRegularity

/-- `c_* = (10A)⁻¹`, `A = 2C_r`, `C_r = 4cosh(10πr)/r²`, `r = 1/100`. -/
noncomputable def ocCStar : ℝ :=
  (10 * (2 * (4 * Real.cosh (10 * Real.pi * (1 / 100)) / (1 / 100) ^ 2)))⁻¹

end AVRegularity
