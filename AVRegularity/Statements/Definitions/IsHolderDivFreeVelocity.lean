-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVenhance.Statements.Roots.IsZ2Periodic
public import AVenhance.Statements.Roots.SpaceGrad
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! The velocity class of the main statements (such as `interior_regularity`): bounded,
`ℤ × ℤ²`-periodic, distributionally divergence-free, jointly `C^α` in `(t,x)`, the properties
of the velocity field of the construction stated with display (1.15) of the paper. -/

@[expose] public section

open MeasureTheory Homogenization AVenhance

namespace AVRegularity

/-- `b ∈ C^α(ℝ × 𝕋²)` is bounded, `ℤ²`-periodic in space and `1`-periodic in time,
jointly `α`-Hölder for `d = |t - u| + |x - y|` (Euclidean `|x - y|`; an upper bound only,
so smoother fields also qualify), and divergence free in the sense of distributions on every
time slice. -/
def IsHolderDivFreeVelocity (α : ℝ) (b : ℝ → Vec 2 → Vec 2) : Prop :=
  (∀ t, IsZ2Periodic (b t)) ∧
  (∀ t x, b (t + 1) x = b t x) ∧
  (∃ C : ℝ, ∀ t x, ‖b t x‖ ≤ C) ∧
  (∃ C : ℝ, ∀ t u : ℝ, ∀ x y : Vec 2,
    ‖b t x - b u y‖ ≤ C * (|t - u| + Real.sqrt (vecNormSq (x - y))) ^ α) ∧
  (∀ t : ℝ, ∀ φ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    ∫ x, vecDot (b t x) (spaceGrad φ x) = 0)

end AVRegularity
