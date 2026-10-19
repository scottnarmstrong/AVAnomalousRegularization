-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev

/-! The assembled preparation operator `P = P_diag I + ∑_{h=1}^H P^{(h)}` of the joint preparation
`cycle_joint`, `(P f)_v = P_diag f_v + ∑_{h=1}^H ∑_u P^{(h)}_{vu} f_u`, from the diagonal block
`Pd v` and the source-degree blocks `Pg h v u` acting on `L²` vectors (`TorusHk 0`). The output
component `v` has the order `max M_out K_v` (the model order `M_out` and the physical slot `K_v`;
see `IsJointModel`). -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- `(P f)_v = Pd v (f v) + ∑_{h' ∈ [1,H]} ∑_u Pg h' v u (f u)`. -/
def jointOperator {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (K : ι → ℕ) (Mout H : ℕ)
    (Pd : ∀ v, TorusHk 0 (h v) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (Pg : ℕ → ∀ v u, TorusHk 0 (h u) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
    (f : ∀ u, TorusHk 0 (h u)) (v : ι) : TorusHk (max Mout (K v)) (h v) :=
  Pd v (f v) + ∑ h' ∈ Finset.Icc 1 H, ∑ u, Pg h' v u (f u)

end AVRegularity
