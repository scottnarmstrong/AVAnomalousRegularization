-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVenhance.Infra.Torus.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Homogenization.Ambient.Basic

/-! The `L²` pairing of two periodic fields over the unit cell `[0,1)²`, `∫_{𝕋²} ⟨g₁, g₂⟩`. It pairs
raw representatives of the Sobolev carriers with smooth periodic test fields; used for the dual
(weak) definition of operators applied to `L²` fields. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization

namespace AVRegularity

/-- `∫_{unitCube} ⟨g₁ x, g₂ x⟩ dx`. -/
def cellInner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g₁ g₂ : Vec 2 → E) : ℝ :=
  ∫ x in AVenhance.unitCube, inner ℝ (g₁ x) (g₂ x)

end AVRegularity
