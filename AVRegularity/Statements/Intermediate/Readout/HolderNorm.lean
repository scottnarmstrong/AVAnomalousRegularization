-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Readout.SupNorm
public import AVRegularity.Statements.Intermediate.Readout.HolderSeminorm

/-! The Hölder norm `‖F‖_{C^s} = ‖F‖_∞ + [F]_{C^s}` on the torus. -/

@[expose] public section

open Homogenization
open scoped ENNReal

namespace AVRegularity

/-- `‖F‖_{C^s} = ‖F‖_∞ + sup_{x ≠ y} ‖F x - F y‖ / d(x,y)^s`, valued in `[0, ∞]`. -/
noncomputable def holderNorm {H : Type*} [NormedAddCommGroup H] (s : ℝ) (F : Vec 2 → H) :
    ℝ≥0∞ :=
  supNorm F + holderSeminorm s F

end AVRegularity
