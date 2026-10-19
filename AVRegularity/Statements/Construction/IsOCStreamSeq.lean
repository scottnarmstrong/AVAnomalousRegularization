-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Construction.OcNextStream
/-! The stream sequence `φ_m` of display (1.12) of the paper. -/

@[expose] public section

open Homogenization AVenhance

namespace AVRegularity

/-- `φ_0 = 0` and, for `m ≥ 1`, `φ_{m-1}` is admissible (smooth, `ℤ × ℤ²`-periodic) and
`φ_m` is obtained from it by `ocNextStream`. The velocities are
`b_m = ∇^⊥ φ_m = streamVel (Φ m)` (display (1.12) of the paper). -/
def IsOCStreamSeq (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (Φ : ℕ → ℝ → Vec 2 → ℝ) : Prop :=
  Φ 0 = (fun _ _ => 0) ∧
    ∀ m : ℕ, 1 ≤ m →
      ∃ h : IsAdmissibleStream (Φ (m - 1)), Φ m = ocNextStream α q Λ ζ m (Φ (m - 1)) h

end AVRegularity
