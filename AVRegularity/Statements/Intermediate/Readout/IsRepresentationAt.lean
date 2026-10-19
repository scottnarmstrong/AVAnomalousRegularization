-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Readout.Representation
public import AVenhance.Statements.Roots.IsZ2Periodic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic

/-! `r` is a representation at wavelength `e` with derivative order `K`, as in display (4.13) of the
paper. -/

@[expose] public section

open Homogenization

namespace AVRegularity

/-- A representation at wavelength `e` (display (4.13) of the paper): `0 < e ≤ 1`; the base and
every profile are `ℤ²`-periodic (fields on `𝕋²`) of class `C^K`, so that every derivative `D^α`,
`|α| ≤ K`, in the norms is a genuine derivative; and every label satisfies `e ≤ λ_l ≤ 1`. -/
def IsRepresentationAt {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (e : ℝ) (K : ℕ) (r : Representation H) : Prop :=
  0 < e ∧ e ≤ 1 ∧ ContDiff ℝ (K : ℕ) r.base ∧ AVenhance.IsZ2Periodic r.base ∧
    ∀ p ∈ r.profiles,
      ContDiff ℝ (K : ℕ) p.1 ∧ AVenhance.IsZ2Periodic p.1 ∧ e ≤ p.2 ∧ p.2 ≤ 1

end AVRegularity
