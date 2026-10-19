-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.ChartedFamily
public import AVRegularity.Sobolev.Basic

/-! The index type of a charted family. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

namespace ChartedFamily

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- The pairs `(piece, context)` over which the envelopes take their suprema. -/
abbrev Index (_ : ChartedFamily ι h D P Ctx) : Type _ := Σ p : P, Ctx p

end ChartedFamily

end AVRegularity
