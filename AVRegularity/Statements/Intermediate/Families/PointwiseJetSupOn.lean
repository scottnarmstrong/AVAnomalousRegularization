-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Homogenization.Ambient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! The jet supremum `pointwiseJetSupOn` over a declared domain, over every time. -/

@[expose] public noncomputable section

open Homogenization
open scoped ENNReal

namespace AVRegularity

/-- `pointwiseJetSupOn dom r q f`: the supremum, over every time `t` and every `Y` with
`(t, Y) ∈ dom` and every `z`, of the `(r, q)` slow/fast jet of `f t`. It is `jetSupOn` with a
genuine supremum over time in place of the essential supremum. -/
def pointwiseJetSupOn (dom : Set (ℝ × Vec 2)) (r q : ℕ)
    (f : ℝ → Vec 2 → Vec 2 → Vec 2) : ℝ≥0∞ :=
  ⨆ t : ℝ, ⨆ Y ∈ {Y : Vec 2 | (t, Y) ∈ dom}, ⨆ z : Vec 2,
    ‖iteratedFDeriv ℝ r (fun Y' => iteratedFDeriv ℝ q (f t Y') z) Y‖ₑ

end AVRegularity
