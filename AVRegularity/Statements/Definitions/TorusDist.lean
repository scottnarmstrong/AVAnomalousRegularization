-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVenhance.Statements.Roots.LatticeShift
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The Euclidean distance on the torus 𝕋² = ℝ²/ℤ², the distance `d` of the `C^s` norm. -/

@[expose] public section

open Homogenization

namespace AVRegularity

/-- Torus distance `d(x,y) = min_{n ∈ ℤ²} |x - y - n|`, with the Euclidean norm on ℝ². -/
noncomputable def torusDist (x y : Vec 2) : ℝ :=
  ⨅ n : Fin 2 → ℤ, Real.sqrt (vecNormSq (x - y - AVenhance.latticeShift n))

end AVRegularity
