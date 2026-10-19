-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev
public import Mathlib.Analysis.Normed.Operator.Basic

/-! A real linear functional `ℓ` of a classical `E`-valued cell field
`c(t,z)` as a complex cell trajectory in the representation of the cell-evolution relation
`IsCellSolution`: the value jet `ℓ c(t)` and the gradient jet `ℓ ∂_k c(t)` (`cellValue` and
`IsCellSolution` read `ℝ → RawJet2 1 ℂ`). -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- Value jet `ℓ (c t x)`, gradient jet `ℓ (∂_k c t x)`, as `ℂ`. -/
def cellJetOfField {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (ℓ : E →L[ℝ] ℝ)
    (c : ℝ → Vec 2 → E) : ℝ → RawJet2 1 ℂ :=
  fun t a x => if h : 0 < a.1.val then ((ℓ (fderiv ℝ (c t) x (basisVec (a.2 ⟨0, h⟩))) : ℝ) : ℂ)
    else ((ℓ (c t x) : ℝ) : ℂ)

end AVRegularity
