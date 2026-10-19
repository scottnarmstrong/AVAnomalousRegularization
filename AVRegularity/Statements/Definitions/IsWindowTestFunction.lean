-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVenhance.Statements.Roots.IsZ2Periodic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic

/-! Space-time test functions for a weak solution on `[t₁, t₂] × 𝕋²`. -/

@[expose] public section

open Homogenization AVenhance

namespace AVRegularity

/-- Smooth functions on `ℝ × ℝ²`, `ℤ²`-periodic in space, vanishing for `t ≥ t₂`. -/
def IsWindowTestFunction (t₂ : ℝ) (φ : ℝ → Vec 2 → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2) ∧
  (∀ t, IsZ2Periodic (φ t)) ∧ ∀ t, t₂ ≤ t → ∀ x, φ t x = 0

end AVRegularity
