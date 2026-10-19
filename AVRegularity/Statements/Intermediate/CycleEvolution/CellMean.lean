-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! The unit-cell average `P₀`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization

namespace AVRegularity

/-- `⟨u⟩ = ∫_{𝕋²} u`, the cell average of a complex cell function (`P₀ u` is the constant
`⟨u⟩`); `𝕋² = ℝ²/ℤ²` is realized by the open unit cube. For a non-integrable `u` the value is
the Bochner junk value `0`; every use in the statements is on an `L²` function. -/
def cellMean (u : Vec 2 → ℂ) : ℂ := ∫ x in AVenhance.unitCube, u x

end AVRegularity
