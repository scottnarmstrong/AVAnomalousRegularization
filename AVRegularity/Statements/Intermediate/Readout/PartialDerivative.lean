-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Homogenization.Sobolev.WeakDerivatives

/-! The partial derivative `D^α F` of a field `F : ℝ² → H` for a multi-index `α`. -/

@[expose] public noncomputable section

open Homogenization

namespace AVRegularity

/-- `D^α F = ∂₁^{α₁} ∂₂^{α₂} F`, obtained by iterating the directional Fréchet derivative along
the two coordinate vectors (coordinates `0` and `1` of `Vec 2`). For `F` of class `C^{|α|}` this is
the usual mixed partial derivative (the order of differentiation is immaterial). Meaningful (equal
to the classical `D^α`) only for `F` of class `C^{|α|}`; every statement that uses it outside
clause 1 of `iteration_readout` assumes this through `IsRepresentationAt`. -/
def partialDerivative {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (α : Fin 2 → ℕ) (F : Vec 2 → H) : Vec 2 → H :=
  (fun G : Vec 2 → H => fun x => fderiv ℝ G x (basisVec 1))^[α 1]
    ((fun G : Vec 2 → H => fun x => fderiv ℝ G x (basisVec 0))^[α 0] F)

end AVRegularity
