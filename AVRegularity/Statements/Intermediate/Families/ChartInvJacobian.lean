-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.ChartJacobian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! The inverse Jacobian of a chart transition. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- `K = J⁻¹` (the inverse Jacobian; an actual inverse when `det J = 1`). -/
def chartInvJacobian (Υ : Vec 2 → Vec 2) (y : Vec 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  (chartJacobian Υ y)⁻¹

end AVRegularity
