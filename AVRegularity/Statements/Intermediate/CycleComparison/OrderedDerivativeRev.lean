-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev.Basic

/-! The classical ordered derivative `∂_{α_0} ⋯ ∂_{α_{m-1}} g` of a field, i.e. the *reversed*
application order of the derivative word `α` (the dual of `∇^{d-1}`). The Sobolev carrier's jet of
the word `α` (`HasOrderedWeakJetOn`) is `∂_{α_{m-1}} ⋯ ∂_{α_0} u`, the last letter being the
outermost derivative; its formal adjoint therefore applies `∂_{α_{m-1}}` first and `∂_{α_0}` last.
It is used only on smooth test fields, where the order is immaterial; it is fixed so that no junk
value of a non-differentiable `fderiv` can enter silently. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- `∂_{α_0}(∂_{α_1}(⋯ ∂_{α_{m-1}} g))`, by `fderiv`. -/
def orderedDerivativeRev {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}
    (α : DerivativeWord2 m) (g : Vec 2 → E) : Vec 2 → E :=
  (List.ofFn α).foldr (fun i g' => fun x => fderiv ℝ g' x (basisVec i)) g

end AVRegularity
