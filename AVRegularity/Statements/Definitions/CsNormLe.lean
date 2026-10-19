-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Definitions.TorusDist

/-! The torus Hölder-norm bound `‖g‖_{C^s(𝕋²)} ≤ K`, for the norm of display (2.1) of the
paper. -/

@[expose] public section

open Homogenization

namespace AVRegularity

/-- `‖g‖_{C^s} = ‖g‖_∞ + sup_{x ≠ y} |g x - g y| / d(x,y)^s ≤ K`, with torus distance `d`.
Written pointwise: `sup_x A x + sup_{y ≠ z} B y z ≤ K` iff `A x + B y z ≤ K` for all
`x` and all `y, z` at positive torus distance, so no supremum can take a junk value. -/
def CsNormLe (s : ℝ) (g : Vec 2 → ℝ) (K : ℝ) : Prop :=
  ∀ x y z : Vec 2, torusDist y z ≠ 0 →
    |g x| + |g y - g z| / torusDist y z ^ s ≤ K

end AVRegularity
