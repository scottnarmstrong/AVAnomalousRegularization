-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleComparison.SlowPartial
public import AVRegularity.Statements.Intermediate.CycleComparison.FastPartial

/-! The first cross operator `ℬ_1 = w·∇_X - √η {div_z(G∇_X) + div_X(G∇_z)}`, `w = √η v`, for the
symmetric cell-independent metric `G(𝗍,X)` and the drift `v(𝗍,z)` independent of `X`. -/

@[expose] public noncomputable section

open Homogenization

namespace AVRegularity

/-- `(ℬ_1 Φ)(X,z) = ∑_k √η v_k(z) ∂_{X_k}Φ - √η ∑_{ij} (G_{ij}(X) ∂_{z_i} ∂_{X_j} Φ + ∂_{X_i}(G_{ij} ∂_{z_j} Φ))`
at time `t`. -/
def cellB1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (η : ℝ)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2) (t : ℝ)
    (Φ : Vec 2 → Vec 2 → E) : Vec 2 → Vec 2 → E :=
  fun X z => (∑ k : Fin 2, (Real.sqrt η * v t z k) • slowPartial k Φ X z)
    - Real.sqrt η • ∑ i : Fin 2, ∑ j : Fin 2,
        (G t X i j • fastPartial i (slowPartial j Φ) X z
          + slowPartial i (fun X' z' => G t X' i j • fastPartial j Φ X' z') X z)

end AVRegularity
