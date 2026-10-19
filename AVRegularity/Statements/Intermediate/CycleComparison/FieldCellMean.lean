-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVenhance.Infra.Torus.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Homogenization.Ambient.Basic

/-! The unit-cell average `P_0 ψ = ∫_{𝕋²} ψ` of a periodic field.
-/

@[expose] public noncomputable section

open MeasureTheory Homogenization

namespace AVRegularity

/-- `P_0 ψ = ∫_{[0,1)²} ψ(z) dz`. -/
def fieldCellMean {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (ψ : Vec 2 → E) : E :=
  ∫ z in AVenhance.unitCube, ψ z

end AVRegularity
