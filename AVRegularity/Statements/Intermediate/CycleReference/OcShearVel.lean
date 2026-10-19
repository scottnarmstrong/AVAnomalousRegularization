-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Construction.OcShear
public import AVenhance.Statements.Construction.StreamVel

/-! The shear velocity `𝐮_k = ∇^⊥ψ_{m,k}`. -/

@[expose] public section

open Homogenization AVenhance

namespace AVRegularity

/-- `𝐮_{m,k}(y) = ∇^⊥ ψ_{m,k}(y) = σ ∇ψ_{m,k}(y)`, computed with the `streamVel` of the
`AVenhance` library of the time-independent stream `ψ_{m,k}` (the time argument `0` is
immaterial). -/
noncomputable def ocShearVel (α q : ℝ) (Λ m : ℕ) (k : ℤ) (y : Vec 2) : Vec 2 :=
  streamVel (fun _ => ocShear α q Λ m k) 0 y

end AVRegularity
