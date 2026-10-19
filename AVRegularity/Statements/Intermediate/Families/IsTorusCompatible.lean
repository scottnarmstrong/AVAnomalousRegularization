-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.ChartedFamily
public import AVenhance.Statements.Roots.IsZ2Periodic

/-! The torus compatibility of the selected representatives of a charted family at the slow
scale `E`.

The actual construction has this property, which the family interface does not record. Two
clauses, at **all real times** (so that the complete retained cell histories are covered without a
history-domain convention):
* the material map `Φ_p(t,·)` of every piece commutes with integer translations,
  `Φ_p(t, Y + n) = Φ_p(t, Y) + n` for `n ∈ ℤ²` (`AVenhance.latticeShift`);
* the flux of the selected context `actual p`, read in the dimensional slow label
  `Y = E X` (as in `ChartedFamily.slowFlux`), is `ℤ²`-periodic in `Y` at every time, order,
  word and fast variable: the slow lattice of the normalized variable is `E⁻¹ℤ²`, not `Eℤ²`.
With the fast periodicity of the family and `e⁻¹ ∈ ℕ` these give the periodicity of every
physical and edge coefficient. The predicate is a property of the chosen representatives
(`actual`); it is not implied by the fast periodicity or by any envelope. -/

@[expose] public section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- Torus compatibility of the selected representatives `actual` of the charted family `F`
at the slow scale `E`: integer-translation equivariance of every material chart at every time, and
`ℤ²`-periodicity in `Y` of `F.flux p (actual p) v u γ d I t (E⁻¹ • Y) z`. -/
def IsTorusCompatible {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}
    (F : ChartedFamily ι h D P Ctx) (actual : ∀ p, Ctx p) (E : ℝ) : Prop :=
  (∀ (p : P) (t : ℝ) (n : Fin 2 → ℤ) (Y : Vec 2),
    (F.piece p).material t (Y + AVenhance.latticeShift n) =
      (F.piece p).material t Y + AVenhance.latticeShift n) ∧
  ∀ (p : P) (t : ℝ) (v u : ι) (γ : F.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1)) (z : Vec 2),
    AVenhance.IsZ2Periodic (fun Y => F.flux p (actual p) v u γ d I t (E⁻¹ • Y) z)

end AVRegularity
