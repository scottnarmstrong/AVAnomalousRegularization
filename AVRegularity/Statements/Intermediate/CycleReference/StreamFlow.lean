-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVenhance.Statements.Construction.StreamVelLipschitz
public import AVenhance.Statements.Construction.StreamVelContinuous
public import AVenhance.Statements.FlowDefs.Flow

/-! The flow `X(t,x,s)` of an admissible stream. -/

@[expose] public section

open Homogenization AVenhance

namespace AVRegularity

/-- `X(t,x,s)`: the position at time `t` of the trajectory of `∇^⊥ φ` through `x` at time `s`;
the `flow` of `streamVel φ` from the `AVenhance` library, whose hypotheses are supplied by
admissibility of `φ`. For `φ = Φ (m-1)` this is `X_{m-1}`. -/
noncomputable def streamFlow (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ) :
    ℝ → Vec 2 → ℝ → Vec 2 :=
  flow (streamVel φ) hφ.vel_continuous hφ.vel_lipschitz

end AVRegularity
