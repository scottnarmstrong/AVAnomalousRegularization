-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleComparison.SlowPartial

/-! The second cross operator `ℬ_2 = -η div_X(G∇_X)`.
-/

@[expose] public noncomputable section

open Homogenization

namespace AVRegularity

/-- `(ℬ_2 Φ)(X,z) = -η ∑_{ij} ∂_{X_i}(G_{ij} ∂_{X_j} Φ)(X,z)` at time `t`. -/
def cellB2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (η : ℝ)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (t : ℝ) (Φ : Vec 2 → Vec 2 → E) :
    Vec 2 → Vec 2 → E :=
  fun X z => -(η • ∑ i : Fin 2, ∑ j : Fin 2,
    slowPartial i (fun X' z' => G t X' i j • slowPartial j Φ X' z') X z)

end AVRegularity
