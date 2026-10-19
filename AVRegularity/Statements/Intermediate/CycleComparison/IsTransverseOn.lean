-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Homogenization.Sobolev.WeakDerivatives

/-! A coefficient `a(t,X,z)` is `transverse` for the pulse orientation `e_∥` at the times `S` when
it is independent of the parallel fast coordinate `z_∥`. The cell variable `z ∈ ℝ²` is read modulo
`ℤ²` by the periodicity of the coefficient; translation along `e_∥` by every real `s` is the exact
statement. -/

@[expose] public section

open Homogenization

namespace AVRegularity

/-- `a(t,X,z + s e_∥) = a(t,X,z)` for all `t ∈ S`, `X`, `z`, `s ∈ ℝ`: `a` depends on the fast
variable only through the transverse coordinate. -/
def IsTransverseOn {E : Type*} (e : Fin 2) (S : Set ℝ) (a : ℝ → Vec 2 → Vec 2 → E) : Prop :=
  ∀ t ∈ S, ∀ X z : Vec 2, ∀ s : ℝ, a t X (z + s • basisVec e) = a t X z

end AVRegularity
