-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Homogenization.Ambient.Basic

/-! A coefficient `a(t,X,z)` is `fast independent` at the times `S`
when it does not depend on the fast variable `z`. -/

@[expose] public section

open Homogenization

namespace AVRegularity

/-- `a(t,X,z) = a(t,X,z')` for all `t ∈ S`, `X`, `z`, `z'`. -/
def IsFastIndependentOn {E : Type*} (S : Set ℝ) (a : ℝ → Vec 2 → Vec 2 → E) : Prop :=
  ∀ t ∈ S, ∀ X z z' : Vec 2, a t X z = a t X z'

end AVRegularity
