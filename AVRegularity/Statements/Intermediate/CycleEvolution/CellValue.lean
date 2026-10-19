-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev

/-! The value representative of a cell trajectory.
A cell field at one time is a raw order-one weak jet
`D : RawJet2 1 ℂ`; the index `valueIndex2 1` is the value and the index `(1, k)` is `∂ₖ`. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- The value representative `c(t)` of a cell trajectory `D : ℝ → RawJet2 1 ℂ`. -/
def cellValue (D : ℝ → RawJet2 1 ℂ) (t : ℝ) : Vec 2 → ℂ := D t (valueIndex2 1)

end AVRegularity
