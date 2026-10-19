-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Homogenization.Ambient.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The supremum norm `‖F‖_∞` of a field `F : ℝ² → H`.
-/

@[expose] public section

open Homogenization
open scoped ENNReal NNReal

namespace AVRegularity

/-- `‖F‖_∞ = sup_x ‖F x‖`, valued in `[0, ∞]` so that an unbounded field has norm `⊤` rather than
a junk real value. -/
noncomputable def supNorm {H : Type*} [NormedAddCommGroup H] (F : Vec 2 → H) : ℝ≥0∞ :=
  ⨆ x : Vec 2, (‖F x‖₊ : ℝ≥0∞)

end AVRegularity
