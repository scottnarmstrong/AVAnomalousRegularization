-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.ConstituentRecord
public import AVRegularity.Sobolev.Basic
public import AVenhance.Statements.Roots.IsZ2Periodic
public import Mathlib.Analysis.Normed.Operator.Basic

/-! A scalar flux constituent of order `d ≥ 2` of the source on an
edge `u → v`: a constant Hilbert map `C_γ : 𝗁_u → 𝗁_v` times scalar coefficients
`a^♭_{γ,α}(t,X,z) ∈ ℝ²`, `α` an ordered derivative word of length `d - 1`, `X` the normalized
slow variable `x/E`, `z` the fast variable `x/e` of period one. The source it defines is
`div[ν e^{d-2} ∑_α a^♭_{γ,α}(t,x/E,x/e) C_γ ∂^α f]` (`physicalCoefficient`). The order `d` is a
parameter so that the word index `DerivativeWord2 (d - 1)` has no cast; edge lists only contain
`2 ≤ d ≤ D` (`ConstituentEdges`). Real-valued: the complex-domain analytic size lives in the
record `size`. -/

@[expose] public section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- A scalar flux constituent of order `d` from `Hu` to `Hv`, with its positive record. -/
structure Constituent (d : ℕ) (Hu Hv : Type*) [NormedAddCommGroup Hu] [NormedSpace ℝ Hu]
    [NormedAddCommGroup Hv] [NormedSpace ℝ Hv] where
  /-- The constant Hilbert map `C_γ`. -/
  map : Hu →L[ℝ] Hv
  /-- The scalar coefficients `a^♭_{γ,α}(t, X, z)` with values in `ℝ²`. -/
  coeff : DerivativeWord2 (d - 1) → ℝ → Vec 2 → Vec 2 → Vec 2
  /-- The coefficients are of period one in the fast variable `z`. -/
  periodic : ∀ α t X, AVenhance.IsZ2Periodic (coeff α t X)
  /-- The positive record. -/
  record : ConstituentRecord
  /-- The original order is at least the current order, `d^birth ≥ d`. -/
  birthExcess_ge : d ≤ record.birthExcess + 2

end AVRegularity
