-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev.Basic

/-! The classical ordered derivative `∂^α g` of a field `g(X)` for a derivative word `α`, in the
convention of the Sobolev carrier: the jet of the word `Fin.snoc w i` is `∂_i` of the jet of `w`
(`HasOrderedWeakJetOn`), so the last letter is the outermost derivative and
`∂^α g = ∂_{α_{m-1}}(⋯ ∂_{α_0} g)`. For smooth `g` the order is immaterial. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- `∂_{α_{m-1}}(⋯(∂_{α_1}(∂_{α_0} g)))`, by `fderiv`. -/
def orderedDerivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}
    (α : DerivativeWord2 m) (g : Vec 2 → E) : Vec 2 → E :=
  (List.ofFn α).foldl (fun g' i => fun x => fderiv ℝ g' x (basisVec i)) g

end AVRegularity
