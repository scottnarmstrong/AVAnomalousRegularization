-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Construction.SlowEnvelope
public import AVRegularity.Statements.Construction.OcLabel

/-! The fast-slow pulse `p_k`. -/

@[expose] public section

namespace AVRegularity

/-- `p_k(t) = ζ̂_{m,l_{m,k}}(t) ζ_{m,k}(t)` with `ζ_{m,k}(t) = ζ((t - kτ_m)/τ_m)`.
Only odd slots `k` enter the cycle. -/
noncomputable def ocPulse (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ) (k : ℤ) (t : ℝ) : ℝ :=
  slowEnvelope α q Λ m (ocLabel α q Λ m k) t *
    ζ ((t - (k : ℝ) * ocTau α q Λ m) / ocTau α q Λ m)

end AVRegularity
