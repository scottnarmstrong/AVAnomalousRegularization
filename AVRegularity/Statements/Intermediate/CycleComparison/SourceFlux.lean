-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleComparison.DEpsWord
public import AVRegularity.Statements.Intermediate.Families.ConstituentEdges

/-! The source flux of the lift, `(∑_{1≤|α|≤D-1} a_α D_ε^α Φ)_k`, for the source edges of a Hilbert
family (`𝒮_ε = D_ε · flux`). Independent scalar flux constituents `γ.coeff α` are multiplied by the
constant component maps `γ.map` and summed over the constituents and orders of each edge `u → v`;
the sum of constituents is the operator itself (the positive constituent sums only enter the norms).
-/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- `flux_k(X,z)_v = ∑_{u,d} ∑_{γ∈ edge v u d} ∑_α γ.coeff α t X z k • γ.map ((D_ε^α Φ)(X,z)_u)`,
at time `t` and for the parameter `ε`. -/
def sourceFlux {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} (edge : ConstituentEdges D h) (η ε t : ℝ)
    (Φ : Vec 2 → Vec 2 → ∀ i, h i) (k : Fin 2) : Vec 2 → Vec 2 → ∀ i, h i :=
  fun X z v => ∑ u : ι, ∑ d : Finset.Icc 2 D,
    ((edge v u d).map fun γ => ∑ α : DerivativeWord2 (d.1 - 1),
      (γ.coeff α t X z k) • γ.map (dEpsWord η ε α Φ X z u)).sum

end AVRegularity
