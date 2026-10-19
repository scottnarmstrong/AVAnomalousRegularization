-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Homogenization.Ambient.Basic

/-! Open Euclidean discs in ℝ² (`Vec 2` carries the sup norm, so
`Metric.ball` would be a square). -/

@[expose] public section

open Homogenization

namespace AVRegularity

/-- `B_r(c) = {y : |y - c| < r}` with the Euclidean norm. -/
def euclidBall (c : Vec 2) (r : ℝ) : Set (Vec 2) := {y | vecNormSq (y - c) < r ^ 2}

end AVRegularity
