-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.ConstituentEdges
public import Homogenization.Sobolev.WeakDerivatives

/-! The data of the lift operators: the cell
contrast `η = ν/B`, the symmetric cell-independent metric `G(𝗍,X)` (curried entries), the drift
`v(𝗍,z)` independent of `X` (so `w = √η v`), and the source edges, whose independent coefficients
`a(𝗍,X,z)` are the `Constituent.coeff` fields in the variables `(X,z)` of the lift (`X = x/ρ`).
The data carry no hypothesis; the premises are `IsLiftSetting`. The drift is a general
divergence-free cell field here: the transverse shear form of the enlarged pulse is a premise of
the interior proposition, not of the operators; the same algebra serves the two-dimensional weak
cell with drift `Pe_i v_p`. -/

@[expose] public section

open Homogenization

namespace AVRegularity

/-- `(η, G, v, edge)`. -/
structure LiftOperatorData (ι : Type*) (h : ι → Type*) [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (D : ℕ) where
  /-- The cell contrast `η = ν/B`. -/
  η : ℝ
  /-- The metric `G(𝗍,X)`, entries `G t X i j`. -/
  G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ
  /-- The drift `v(𝗍,z)`; the normalized drift is `w = √η v`. -/
  v : ℝ → Vec 2 → Vec 2
  /-- The source edges, with coefficients `a(𝗍,X,z)`. -/
  edge : ConstituentEdges D h

end AVRegularity
