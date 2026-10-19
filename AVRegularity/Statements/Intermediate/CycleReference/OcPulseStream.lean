-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleReference.OcPulse
public import AVRegularity.Statements.Construction.OcShear

/-! The level-`m` stream increment in the material coordinate,
`ψ = ∑_k p_k ψ_{m,k}`. -/

@[expose] public section

open Homogenization

namespace AVRegularity

/-- `ψ(t,y) = ∑_{k odd} p_k(t) ψ_{m,k}(y)`. At each `t` at most one odd pulse is active. -/
noncomputable def ocPulseStream (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ) (t : ℝ) (y : Vec 2) : ℝ :=
  ∑' k : {k : ℤ // Odd k}, ocPulse α q Λ ζ m k.1 t * ocShear α q Λ m k.1 y

end AVRegularity
