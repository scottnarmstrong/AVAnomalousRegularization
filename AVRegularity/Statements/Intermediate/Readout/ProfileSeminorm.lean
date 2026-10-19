-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Readout.PartialDerivative
public import AVRegularity.Statements.Intermediate.Readout.MultiIndicesBetween
public import AVRegularity.Statements.Intermediate.Readout.MultiIndexFactorial
public import AVRegularity.Statements.Intermediate.Readout.SupNorm

/-! The profile seminorm `[F]_{λ,K;s} = λ^{-s} [F]_{C^K_λ}`, with the seminorm at the scale `λ`
of display (4.12) of the paper. -/

@[expose] public section

open Homogenization
open scoped ENNReal

namespace AVRegularity

/-- `[F]_{λ,K;s} = ∑_{1 ≤ |α| ≤ K} λ^{|α|-s} / α! · ‖D^α F‖_∞`, valued in `[0, ∞]`. The scale
`λ` is a real number; the paper takes `0 < λ ≤ 1`, which the statements using it impose. -/
noncomputable def profileSeminorm {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (lam : ℝ) (K : ℕ) (s : ℝ) (F : Vec 2 → H) : ℝ≥0∞ :=
  ∑ α ∈ multiIndicesBetween 1 K,
    ENNReal.ofReal (lam ^ (((α 0 + α 1 : ℕ) : ℝ) - s) / multiIndexFactorial α) *
      supNorm (partialDerivative α F)

end AVRegularity
