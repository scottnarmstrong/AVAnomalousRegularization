-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Homogenization.Ambient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import AVRegularity.Statements.Intermediate.Families.PointwiseJetSupFam

/-! The molecular jet `pointwiseMolecularJet`, built on the supremum over every time. -/

@[expose] public noncomputable section

open Homogenization
open scoped ENNReal

namespace AVRegularity

/-- `pointwiseMolecularJet ρ e k j dom a`: the weighted molecular jet sum of `molecularJet`, with
`pointwiseJetSupFam` in place of `jetSupFam`. -/
def pointwiseMolecularJet {ι : Type*} (ρ e : ℝ) (k j : ℕ)
    (dom : ι → Set (ℝ × Vec 2))
    (a : ι → ℝ → Vec 2 → Vec 2 → Vec 2) : ℝ≥0∞ :=
  ∑ r ∈ Finset.range (k + 1), ∑ q ∈ Finset.range (k + 1 - r),
    ENNReal.ofReal (ρ ^ (r + q) / ((r.factorial : ℝ) * (q.factorial : ℝ) * e ^ q)) *
      pointwiseJetSupFam dom (r + j) q a

end AVRegularity
