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
  fields), summed over the permutations of the word `A`. This is asserted **only** on the trimmed
  quiet overlap; it is never imposed on an active overlap, nor is `a_q(X,z) = a_p(Υ(X),Υ(z))`
  ever used.
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

/-- Transversality on enlarged pulses: for every pulse `k` (time set `pulse k`, parallel
direction `e_∥ = orient k`) every field of every piece and context is invariant under
`z ↦ z + s e_∥` at the output times of the piece lying in the pulse. -/
def IsTransverseOnPulses {κ : Type*} (F : ChartedFamily ι h D P Ctx) (pulse : κ → Set ℝ)
    (orient : κ → Fin 2) : Prop :=
  ∀ k p c v u (γ : F.Γ v u) d I,
    IsTransverseOn (orient k) (pulse k ∩ (F.piece p).output) (F.flux p c v u γ d I)

end ChartedFamily

end AVRegularity
