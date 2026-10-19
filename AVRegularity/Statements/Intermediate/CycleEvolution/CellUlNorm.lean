-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleEvolution.CellL2Norm

/-! The uniformly local norm `‖f‖_{L²_ul}`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization
open scoped ENNReal

namespace AVRegularity

/-- `‖f‖_{L²_ul(I)} = sup_a ‖f‖_{L²(([a,a+1] ∩ I) × 𝕋²)}` in `[0, ∞]`. For `I = ℝ` this is the
displayed norm; for a finite-past problem on `I = [s, ∞)` the windows are cut to `I`. -/
def cellUlNorm {E : Type*} [NormedAddCommGroup E] (I : Set ℝ) (f : ℝ → Vec 2 → E) : ℝ≥0∞ :=
  ⨆ a : ℝ, (∫⁻ τ in Set.Icc a (a + 1) ∩ I, cellL2Norm (f τ) ^ 2) ^ (1 / 2 : ℝ)

end AVRegularity
