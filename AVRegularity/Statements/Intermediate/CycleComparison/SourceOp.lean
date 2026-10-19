-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleComparison.SourceFlux

/-! The source operator `𝒮_ε = D_ε · ∑_{1≤|α|≤D-1} a_α D_ε^α`, applied to a field: the
`D_ε`-divergence of the source flux. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- `(𝒮_ε Φ)(X,z) = ∑_k (D_{ε,k} flux_k)(X,z)` at time `t`. -/
def sourceOp {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} (edge : ConstituentEdges D h) (η ε t : ℝ)
    (Φ : Vec 2 → Vec 2 → ∀ i, h i) : Vec 2 → Vec 2 → ∀ i, h i :=
  fun X z => ∑ k : Fin 2, dEps η ε k (sourceFlux edge η ε t Φ k) X z

end AVRegularity
