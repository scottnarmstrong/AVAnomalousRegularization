-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyDimFlux
public import AVRegularity.Statements.Intermediate.Families.ChartInvJacobian
public import AVRegularity.Statements.Intermediate.Families.TransportedCoeff
public import AVRegularity.Statements.Intermediate.Families.ChartedFamily
public import AVRegularity.Statements.Intermediate.Families.ChartTransition
public import AVRegularity.Statements.Intermediate.CycleComparison.IsTransverseOn
public import AVRegularity.Statements.Intermediate.CycleComparison.IsFastIndependentOn

/-! The structural predicates of a charted family.

* `IsQuietTransition`: on the trimmed quiet overlap of a chart transition `y = Υ(y')`, after
  matching the retained contexts, the independent fields are fast independent and the fields of
  the new chart are the transport (`transportedCoeff`) of the fields of the old chart with the fast
  variable fixed: `ν e^{r-1} a♭_{q,γ,r+1,A}(t,Y'/E,z) = ∑_{d≥r+1} ∑_I ∑_{i₀} K_{a₀i₀}(Y') ν e^{d-2}
  a♭_{p,γ,d,I}(t,Υ(Y')/E,z) T_{I,A}(Y')` (the factor `e^{d-(r+1)}` is explicit in the normalized
  fields), as an identity of operators: both sides are summed over the permutations of the word
  `A` (the fields enter the equations only contracted with symmetric derivative arrays, and the
  first source is stored by its symmetric coefficient, for which the word-by-word identity fails
  under a non-affine chart change). This is asserted **only** on the trimmed quiet overlap; it
  is never imposed on an active overlap, nor is `a_q(X,z) = a_p(Υ(X),Υ(z))` ever used.
* `IsTransverseOnPulses`: on an enlarged pulse with parallel direction `e_∥` the dimensional fields
  are invariant under `z ↦ z + s e_∥`, for every real `s` (vanishing instantaneous drift alone
  does not imply it).
* `IsFastIndependentOn`: fast independence of all fields at the given times, with the
  complete contexts retained. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

namespace ChartedFamily

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- The exact quiet transition from `(p, c)` to `(q, c')` across `tr` (scales `ν, e, E`):
on the overlap both field families are fast independent at the matched points and the new fields
are the transport (`transportedCoeff`) of the old ones, fast variable fixed, summed over the
permutations of the word. -/
def IsQuietTransition (F : ChartedFamily ι h D P Ctx) (ν e E : ℝ) {p q : P}
    (tr : ChartTransition (F.piece p) (F.piece q)) (c : Ctx p) (c' : Ctx q) : Prop :=
  (∀ tY ∈ tr.overlap, ∀ v u (γ : F.Γ v u) d I, ∀ z z' : Vec 2,
      F.flux p c v u γ d I tY.1 (E⁻¹ • tr.Υ tY.2) z = F.flux p c v u γ d I tY.1 (E⁻¹ • tr.Υ tY.2) z' ∧
      F.flux q c' v u γ d I tY.1 (E⁻¹ • tY.2) z = F.flux q c' v u γ d I tY.1 (E⁻¹ • tY.2) z') ∧
  ∀ tY ∈ tr.overlap, ∀ z : Vec 2, ∀ v u (γ : F.Γ v u) (r : ℕ) (A : DerivativeWord2 r),
    ∑ σ : Equiv.Perm (Fin r),
        (ν * e ^ (r - 1)) • F.flux q c' v u γ (r + 1) (A ∘ σ) tY.1 (E⁻¹ • tY.2) z =
      ∑ σ : Equiv.Perm (Fin r),
        transportedCoeff (chartInvJacobian tr.Υ) (F.identity v u γ).maxOrder
          (fun d I => F.dimFlux ν e E p c v u γ d I tY.1 (tr.Υ tY.2) z) r (A ∘ σ) tY.2

end ChartedFamily

end AVRegularity
