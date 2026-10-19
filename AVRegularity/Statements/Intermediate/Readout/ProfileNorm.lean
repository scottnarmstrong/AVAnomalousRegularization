-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Readout.ProfileSeminorm

/-! The profile norm `𝓘_{λ,K;s}(G) = λ^{-s} ‖G‖_{C^K_λ}`, with the norm at the scale `λ` of
display (4.12) of the paper. -/

@[expose] public section

open Homogenization
open scoped ENNReal

namespace AVRegularity

/-- `𝓘_{λ,K;s}(G) = λ^{-s} ‖G‖_∞ + [G]_{λ,K;s}`, valued in `[0, ∞]`. -/
noncomputable def profileNorm {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (lam : ℝ) (K : ℕ) (s : ℝ) (G : Vec 2 → H) : ℝ≥0∞ :=
  ENNReal.ofReal (lam ^ (-s)) * supNorm G + profileSeminorm lam K s G

end AVRegularity
