-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev.Basic
public import Homogenization.Sobolev.WeakDerivatives
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-! The Jacobian of a chart transition. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- The Jacobian `J_{ia}(y') = ∂_a Υ_i(y')`. -/
def chartJacobian (Υ : Vec 2 → Vec 2) (y : Vec 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i a => fderiv ℝ Υ y (basisVec a) i

end AVRegularity
