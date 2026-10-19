-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleComparison.LiftCoeff
public import AVRegularity.Statements.Intermediate.CycleComparison.OrderedDerivative

/-! The action of a left-coefficient operator of tested order at most `n` on a coarse field
`a(𝗍,X)`. The derivatives act on the slow variable of `a` only; coefficients are evaluated at
`(t,X,z)`. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- `(c a)(t,X,z)_v = ∑_{m ≤ n} ∑_{|α|=m} ∑_u c_{m,α}(t,X,z)_{vu} (∂_X^α a(t,·))(X)_u`. -/
def liftApply {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (n : ℕ) (c : LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i) :
    ℝ → Vec 2 → Vec 2 → ∀ i, h i :=
  fun t X z v => ∑ m ∈ Finset.range (n + 1), ∑ α : DerivativeWord2 m, ∑ u : ι,
    c m α t X z v u (orderedDerivative α (a t) X u)

end AVRegularity
