-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleComparison.OrderedDerivativeRev
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The formal adjoint (on smooth periodic test fields) of the word array `g ↦ (∂^α g)_{|α|=m}`: for
`G` valued in the Euclidean word array, `∫ ⟨∂^α g, G_α⟩ = (-1)^m ∫ ⟨g, ∑_α ∂^{rev α} G_α⟩`. Used to
define the action of the coefficient operators `F_A`, `F_E` on `L²` fields by duality. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- `(-1)^m ∑_α ∂^{rev α} (G · α)`, the dual of the order-`m` word array. -/
def wordAdjoint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (m : ℕ)
    (G : Vec 2 → PiLp 2 (fun _ : DerivativeWord2 m => E)) : Vec 2 → E :=
  fun x => ((-1 : ℝ) ^ m) • ∑ α : DerivativeWord2 m, orderedDerivativeRev α (fun y => G y α) x

end AVRegularity
