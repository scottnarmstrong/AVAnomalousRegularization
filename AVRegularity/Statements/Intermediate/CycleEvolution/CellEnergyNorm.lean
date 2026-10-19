-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleEvolution.CellUlNorm
public import AVRegularity.Statements.Intermediate.CycleEvolution.CellValue
public import AVRegularity.Statements.Intermediate.CycleEvolution.CellGradient

/-! The energy norm `‖c‖_ℰ`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity

/-- `‖c‖_ℰ = sup_{t ∈ I} ‖c(t)‖₂ + ‖∇c‖_{L²_ul(I)}` in `[0, ∞]` for a cell trajectory
`D : ℝ → RawJet2 1 ℂ` (value and weak gradient representatives). -/
def cellEnergyNorm (I : Set ℝ) (D : ℝ → RawJet2 1 ℂ) : ℝ≥0∞ :=
  (⨆ t ∈ I, cellL2Norm (cellValue D t)) + cellUlNorm I (fun t => cellGradient (D t))

end AVRegularity
