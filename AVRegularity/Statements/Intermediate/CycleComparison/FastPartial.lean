-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Homogenization.Sobolev.WeakDerivatives

/-! The partial derivative of a field `Φ(X,z)` in a fast coordinate direction, the slow variable
held fixed. -/

@[expose] public noncomputable section

open Homogenization

namespace AVRegularity

/-- `(∂_{z_i} Φ)(X,z)`, by `fderiv` in `z` (meaningful for `Φ(X,·)` differentiable). -/
def fastPartial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (i : Fin 2)
    (Φ : Vec 2 → Vec 2 → E) : Vec 2 → Vec 2 → E :=
  fun X z => fderiv ℝ (fun z' => Φ X z') z (basisVec i)

end AVRegularity
