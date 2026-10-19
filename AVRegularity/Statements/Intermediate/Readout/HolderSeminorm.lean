-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Definitions.TorusDist

/-! The Hölder seminorm `[F]_{C^s}` on the torus `𝕋² = ℝ²/ℤ²` for a field with values in a normed
space, with the torus distance `torusDist`. -/

@[expose] public section

open Homogenization
open scoped ENNReal NNReal

namespace AVRegularity

/-- `[F]_{C^s} = sup_{x ≠ y} ‖F x - F y‖ / d(x,y)^s` with torus distance `d`, valued in `[0, ∞]`;
the supremum runs over pairs at positive torus distance (the convention of `CsNormLe`). -/
noncomputable def holderSeminorm {H : Type*} [NormedAddCommGroup H] (s : ℝ) (F : Vec 2 → H) :
    ℝ≥0∞ :=
  ⨆ (y : Vec 2) (z : Vec 2) (_ : torusDist y z ≠ 0),
    ENNReal.ofReal (‖F y - F z‖ / torusDist y z ^ s)

end AVRegularity
