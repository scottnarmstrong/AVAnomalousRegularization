-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleComparison.DEps
public import AVRegularity.Sobolev.Basic

/-! The ordered words `D_ε^α = D_{ε,α_{m-1}} ⋯ D_{ε,α_0}` of the covariant derivative, in the jet
convention of the Sobolev carrier (last letter outermost). -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- `D_ε^α Ψ = D_{ε,α_{m-1}}(⋯ D_{ε,α_0} Ψ)`. -/
def dEpsWord {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (η ε : ℝ) {m : ℕ}
    (α : DerivativeWord2 m) (Ψ : Vec 2 → Vec 2 → E) : Vec 2 → Vec 2 → E :=
  (List.ofFn α).foldl (fun Ψ' i => dEps η ε i Ψ') Ψ

end AVRegularity
