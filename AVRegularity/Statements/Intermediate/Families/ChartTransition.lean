-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.ChartPiece
public import AVRegularity.Statements.Intermediate.Families.ChartJacobian
public import AVRegularity.Sobolev.Basic
public import Homogenization.Sobolev.WeakDerivatives
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-! The exact transition between two chart descriptions and the order-lowering recursion
(`transitionT`, `transportedCoeff`).
Convention: `y = Υ(y')`, `Φ_q(t,y') = Φ_p(t,Υ(y'))`, `J = DΥ`, `K = J⁻¹`, `det J = 1`.
For `i ∈ {1,2}` put `L_i = ∑_a K_{ai} ∂'_a`; `transitionT` is the scalar function `T_{I,A}` of
`y'` with `(∂_y^I f)∘Υ = ∑_{1≤|A|≤|I|} T_{I,A} ∂_{y'}^A (f∘Υ)`; `transportedCoeff` is the
coefficient array of the divergence-form flux in the new chart: a pure order `d` becomes
orders `2,…,d`, with no total-order-one term. The outer divergence stays outside; the constant
Hilbert maps are unchanged. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- A transition `y = Υ(y')` from the chart of `p` to the chart of `q` on the overlap `overlap`
(pairs of time and the slow label `y'` of `q`): `Υ` is smooth with `det DΥ = 1`, compatible with
the material maps, `Φ_q(t,y') = Φ_p(t,Υ(y'))`. -/
structure ChartTransition (p q : ChartPiece) where
  /-- The transition map `Υ`, `y = Υ(y')`. -/
  Υ : Vec 2 → Vec 2
  /-- `Υ` is smooth. -/
  smooth : ContDiff ℝ (⊤ : ℕ∞) Υ
  /-- `Υ` preserves area. -/
  det_one : ∀ y, (chartJacobian Υ y).det = 1
  /-- Compatibility with the material maps. -/
  compat : ∀ t y', q.material t y' = p.material t (Υ y')
  /-- The valid (trimmed) overlap, in the dimensional slow variable `y'` of `q`. -/
  overlap : Set (ℝ × Vec 2)

end AVRegularity
