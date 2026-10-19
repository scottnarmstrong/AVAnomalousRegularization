-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Readout.Representation
public import AVRegularity.Statements.Intermediate.Readout.ProfileNorm
public import AVRegularity.Statements.Intermediate.Readout.HolderSeminorm

/-! The size `X_e(U;K)` of a specified representation (display (4.13) of the paper).
-/

@[expose] public section

open Homogenization
open scoped ENNReal

namespace AVRegularity

/-- `X_e(U;K) = ‖F‖_∞ + [F]_{e,K;s} + [F]_{C^s} + ∑_l 𝓘_{λ_l,K;s}(G_l)`, valued in `[0, ∞]`; the
sum runs over the recorded profiles with their recorded labels `λ_l`. -/
noncomputable def representedSize {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (s : ℝ) (K : ℕ) (e : ℝ) (r : Representation H) : ℝ≥0∞ :=
  supNorm r.base + profileSeminorm e K s r.base + holderSeminorm s r.base +
    (r.profiles.map fun p => profileNorm p.2 K s p.1).sum

end AVRegularity
