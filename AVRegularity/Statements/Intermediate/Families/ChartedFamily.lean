-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.ChartPiece
public import AVRegularity.Statements.Intermediate.Families.CoefficientIdentity
public import AVRegularity.Sobolev.Basic
public import AVenhance.Statements.Roots.IsZ2Periodic

/-! A coefficient family of independent chart representatives. The data are
* the finite component type `ι` with spaces `h v`, and for each edge `u → v` a finite type
  `Γ v u` of original constituent identities, each with its constant map, record and maximal
  current order (`CoefficientIdentity`);
* a type `P` of chart pieces (`piece : P → ChartPiece`), and for each piece `p` the type `Ctx p`
  of its admissible complete contexts (retained histories, anchors, relative phases): the contexts
  are evaluations of the same recorded construction, not freely chosen pasts;
* for each `(p, c, γ, d)` and ordered word `I` of length `d - 1` an independent scalar flux
  field `a♭[p,c,γ,d,I](t, X, z) ∈ ℝ²`, normalized slow label `X = Y/E`, fast variable `z` of
  period one. The dimensional field is `𝔞 = ν e^{d-2} a♭(t, Y/E, z)` (`dimFlux`). Orders outside
  `2 ≤ d ≤ D_γ` carry the zero field (an absent order is an exact zero array);
* the prescribed time partition `weight`: nonnegative, supported in the output times of its
  piece, locally finite, summing to one on the union of the output times.
Time measurability and the spatial regularity are premises of the envelopes (they are stated on
declared domains, `IsAnalyticEnvelope`), not fields: the objects are exact coefficient data. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- A family of independent chart representatives over the finite component type `ι`, edge-order
bound `D`, pieces `P` and contexts `Ctx`. -/
structure ChartedFamily (ι : Type*) (h : ι → Type*) [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (D : ℕ) (P : Type*) (Ctx : P → Type*) where
  /-- The original constituent identities of the edge `u → v`. -/
  Γ : ι → ι → Type
  /-- The identities of an edge form a finite type. -/
  [fintypeΓ : ∀ v u, Fintype (Γ v u)]
  /-- The map, record and maximal current order of each identity. -/
  identity : ∀ v u, Γ v u → CoefficientIdentity D (h u) (h v)
  /-- The chart piece data. -/
  piece : P → ChartPiece
  /-- The independent flux field `a♭[p,c,γ,d,I](t, X, z)`. -/
  flux : ∀ (p : P), Ctx p → ∀ v u, Γ v u → ∀ d : ℕ, DerivativeWord2 (d - 1) →
    ℝ → Vec 2 → Vec 2 → Vec 2
  /-- Every field has period one in the fast variable. -/
  flux_periodic : ∀ p c v u γ d I t X, AVenhance.IsZ2Periodic (flux p c v u γ d I t X)
  /-- An order outside `2 ≤ d ≤ D_γ` has the zero field. -/
  flux_zero : ∀ p c v u γ d I, ¬ (2 ≤ d ∧ d ≤ (identity v u γ).maxOrder) →
    flux p c v u γ d I = fun _ _ _ => 0
  /-- The time partition of the pieces. -/
  weight : P → ℝ → ℝ
  /-- Partition weights are nonnegative. -/
  weight_nonneg : ∀ p t, 0 ≤ weight p t
  /-- A piece has weight only at its output times. -/
  weight_zero : ∀ p t, t ∉ (piece p).output → weight p t = 0
  /-- A bounded window meets finitely many pieces. -/
  locally_finite : ∀ a b : ℝ, {p | ((piece p).output ∩ Set.Icc a b).Nonempty}.Finite
  /-- The weights sum to one on the union of the output times. -/
  weight_sum : ∀ t, (∃ p, t ∈ (piece p).output) → ∑ᶠ p, weight p t = 1

attribute [instance] ChartedFamily.fintypeΓ

end AVRegularity
