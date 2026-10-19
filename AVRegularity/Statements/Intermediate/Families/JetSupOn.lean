-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Homogenization.Ambient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Function.EssSup
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! The supremum of the mixed jet `D_X^r D_z^q f` of an independent coefficient `f(t,X,z)`
(slow variable `X`, fast variable `z`, the other held fixed) over a time window `I` and all
`X, z`. The norm of `D_X^r D_z^q f(t,X,z)` is the operator norm of the multilinear map
(`z`-derivatives taken first, then `X`-derivatives). Valued in `[0, ∞]`: unbounded gives `⊤`.
The value is the true mixed derivative only where `f t` is `C^{r+q}` (every envelope that uses it
asserts this). Norms on `Vec 2` are the sup norm: equal to the Euclidean operator norms up to a
factor depending only on `(r, q)` (and on `D` through the sum over words); all envelope constants
are quantified after these orders. -/

@[expose] public noncomputable section

open Homogenization
open scoped ENNReal

namespace AVRegularity

/-- `N^W_{r,q}(f)`: the essential supremum in time of the supremum over the declared slow-fast
domain `dom ⊆ ℝ × Vec 2` (pairs `(t, Y)`, fast phase `z` arbitrary) of the mixed jet norm.
Only values at pairs of `dom` enter;
values outside are irrelevant. The jets are genuine derivatives only where `f t` is `C^{r+q}`
near `(Y, z)`; every envelope asserts this. A time set of measure zero gives `0`: the windows of
the statements have positive length. -/
def jetSupOn (dom : Set (ℝ × Vec 2)) (r q : ℕ) (f : ℝ → Vec 2 → Vec 2 → Vec 2) : ℝ≥0∞ :=
  essSup (fun t : ℝ => ⨆ Y ∈ {Y : Vec 2 | (t, Y) ∈ dom}, ⨆ z : Vec 2,
    ‖iteratedFDeriv ℝ r (fun Y' => iteratedFDeriv ℝ q (f t Y') z) Y‖ₑ) MeasureTheory.volume

end AVRegularity
