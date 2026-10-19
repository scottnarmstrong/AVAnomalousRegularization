-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Construction.SlowEnvelope
public import AVRegularity.Statements.Construction.OcLabel
public import AVRegularity.Statements.Construction.OcShear
public import AVenhance.Statements.Construction.StreamVelLipschitz
public import AVenhance.Statements.Construction.StreamVelContinuous
public import AVenhance.Statements.FlowDefs.FlowInv
/-! One step of the stream recursion, display (1.12) of the paper. -/

@[expose] public section

open Homogenization AVenhance

namespace AVRegularity

/-- `φ_m(t,x) = φ_{m-1}(t,x) + ∑_{k ∈ ℤ} ζ̂_{m,l_{m,k}}(t) ζ_{m,k}(t) ψ_{m,k}(X_{m-1}(l_{m,k}τ_m′′, x, t))`,
with `ζ_{m,k}(t) = ζ((t - kτ_m)/τ_m)` and `X_{m-1}` the flow of `∇^⊥ φ_{m-1}` (display (1.12) of
the paper, where `τ_m′′` is written `h_m`).
In the `AVenhance` library `flowInv v _ _ t x s = flow v _ _ s x t`, so the
argument is `X_{m-1}(l τ_m′′, x, t)`. For each `t` only finitely many `k` contribute, so the
`tsum` is a finite sum. -/
noncomputable def ocNextStream (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ)
    (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ) : ℝ → Vec 2 → ℝ :=
  fun t x => φ t x + ∑' k : ℤ,
    slowEnvelope α q Λ m (ocLabel α q Λ m k) t *
      ζ ((t - (k : ℝ) * ocTau α q Λ m) / ocTau α q Λ m) *
      ocShear α q Λ m k
        (flowInv (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz t x
          ((ocLabel α q Λ m k : ℝ) * ocTauPP α q Λ m))

end AVRegularity
