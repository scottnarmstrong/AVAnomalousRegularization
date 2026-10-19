-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic

/-! The multi-index factorial `α!`. -/

@[expose] public section

namespace AVRegularity

/-- `α! = α₀! α₁!`, as a real number. -/
def multiIndexFactorial (α : Fin 2 → ℕ) : ℝ :=
  ∏ k, ((α k).factorial : ℝ)

end AVRegularity
