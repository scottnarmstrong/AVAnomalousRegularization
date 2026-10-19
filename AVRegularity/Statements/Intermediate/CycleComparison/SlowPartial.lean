-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Homogenization.Sobolev.WeakDerivatives

/-! The partial derivative of a field `Φ(X,z)` of the independent slow variable `X` and fast
variable `z` in a slow coordinate direction, the other variable held fixed (the variables are
differentiated before the field is reconstructed at `(𝗍,X,z) = (t/ℓ²,x/ρ,x/e)`, with `z` held fixed
under the slow derivatives). -/

@[expose] public noncomputable section

open Homogenization

namespace AVRegularity

/-- `(∂_{X_i} Φ)(X,z)`, by `fderiv` in `X` (meaningful for `Φ(·,z)` differentiable). -/
def slowPartial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (i : Fin 2)
    (Φ : Vec 2 → Vec 2 → E) : Vec 2 → Vec 2 → E :=
  fun X z => fderiv ℝ (fun X' => Φ X' z) X (basisVec i)

end AVRegularity
