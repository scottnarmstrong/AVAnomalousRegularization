-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleEvolution.CellGradComp

/-! The gradient field `∇c` of a raw order-one jet. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- `∇c = (∂₀ c, ∂₁ c)` as a `PiLp 2`-valued field (Euclidean pointwise norm). -/
def cellGradient (D : RawJet2 1 ℂ) : Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ) :=
  fun x => WithLp.toLp 2 fun k => cellGradComp D k x

end AVRegularity
