-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Homogenization.Ambient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Function.EssSup
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import AVRegularity.Statements.Intermediate.Families.JetSupOn

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

/-- `N_{r,q}(f)` for an indexed collection `f = (f_i)` with domains `dom i`:
`sup_i jetSupOn (dom i) r q (f i)`. The supremum over the index (pieces and contexts) sits
inside each positive constituent bound, never as a sum of one majorant per index. -/
def jetSupFam {ι : Type*} (dom : ι → Set (ℝ × Vec 2)) (r q : ℕ)
    (f : ι → ℝ → Vec 2 → Vec 2 → Vec 2) : ℝ≥0∞ :=
  ⨆ i, jetSupOn (dom i) r q (f i)

end AVRegularity
