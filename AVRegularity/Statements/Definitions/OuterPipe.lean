-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Definitions.EuclidBall

/-! The outer material pipe. -/

@[expose] public section

open Homogenization

namespace AVRegularity

/-- `𝒫_out = {(t, F_t(y)) : t₁ - 8T < t < t₁, |y| < R}`. -/
def outerPipe (F : ℝ → Vec 2 → Vec 2) (t₁ T R : ℝ) : Set (ℝ × Vec 2) :=
  {p | t₁ - 8 * T < p.1 ∧ p.1 < t₁ ∧ ∃ y ∈ euclidBall 0 R, p.2 = F p.1 y}

end AVRegularity
