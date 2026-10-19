-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Homogenization.Ambient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import AVRegularity.Statements.Intermediate.Families.PointwiseJetSupOn

/-! The jet supremum `pointwiseJetSupFam` of an indexed collection, over every time of the
domains. -/

@[expose] public noncomputable section

open Homogenization
open scoped ENNReal

namespace AVRegularity

/-- `pointwiseJetSupFam dom r q f`: the supremum over the family index of `pointwiseJetSupOn`.
It is `jetSupFam` with `pointwiseJetSupOn` in place of `jetSupOn`. -/
def pointwiseJetSupFam {ι : Type*} (dom : ι → Set (ℝ × Vec 2)) (r q : ℕ)
    (f : ι → ℝ → Vec 2 → Vec 2 → Vec 2) : ℝ≥0∞ :=
  ⨆ i, pointwiseJetSupOn (dom i) r q (f i)

end AVRegularity
