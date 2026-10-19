-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! The `L²(𝕋²)` norm of a cell function. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization
open scoped ENNReal

namespace AVRegularity

/-- `‖u‖₂ = (∫_{𝕋²} |u|²)^{1/2}` in `[0, ∞]` (the torus is the open unit cube). The value `∞`
records non-membership in `L²`; there is no junk value. -/
def cellL2Norm {E : Type*} [NormedAddCommGroup E] (u : Vec 2 → E) : ℝ≥0∞ :=
  eLpNorm u 2 (volume.restrict AVenhance.unitCube)

end AVRegularity
