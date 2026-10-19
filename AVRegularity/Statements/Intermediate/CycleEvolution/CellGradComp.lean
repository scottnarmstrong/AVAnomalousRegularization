-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev

/-! The gradient components of a raw order-one jet. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- The representative of the weak derivative `∂ₖ` of a raw order-one jet `D`. -/
def cellGradComp (D : RawJet2 1 ℂ) (k : Fin 2) : Vec 2 → ℂ :=
  D ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩

end AVRegularity
