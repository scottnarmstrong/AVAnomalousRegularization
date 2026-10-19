-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleComparison.SlowPartial
public import AVRegularity.Statements.Intermediate.CycleComparison.FastPartial

/-! The covariant derivative `D_ε = ∇_z + √η ε ∇_X`.
-/

@[expose] public noncomputable section

open Homogenization

namespace AVRegularity

/-- `(D_{ε,i} Ψ)(X,z) = ∂_{z_i}Ψ + √η ε ∂_{X_i}Ψ`. -/
def dEps {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (η ε : ℝ) (i : Fin 2)
    (Ψ : Vec 2 → Vec 2 → E) : Vec 2 → Vec 2 → E :=
  fun X z => fastPartial i Ψ X z + (Real.sqrt η * ε) • slowPartial i Ψ X z

end AVRegularity
