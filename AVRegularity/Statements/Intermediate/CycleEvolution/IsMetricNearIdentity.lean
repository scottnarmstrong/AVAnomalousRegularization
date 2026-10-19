-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev

/-! The closeness `‖G - I‖_∞ ≤ g` of a cell metric to the identity. -/

@[expose] public section

open Homogenization

namespace AVRegularity

/-- `‖G - I‖_∞ ≤ g`: for a symmetric `G` this is the operator-norm bound
`|ξ·(G - I)ξ| ≤ g|ξ|²` for every real `ξ`, at every `(t,z)`. -/
def IsMetricNearIdentity (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ) : Prop :=
  ∀ t z (ξ : Vec 2),
    |∑ i, ∑ j, ξ i * (G t z - (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j * ξ j| ≤ g * ∑ i, ξ i ^ 2

end AVRegularity
