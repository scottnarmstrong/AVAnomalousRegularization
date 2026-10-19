-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.ChartedFamilySlowFlux
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIndex
public import AVRegularity.Statements.Intermediate.Families.FamilyDomain
public import AVRegularity.Statements.Intermediate.Families.JetSup
public import Mathlib.Analysis.Real.Sqrt

/-! The analytic (independent) envelope of a charted family, uniform over its declared domains.
With `N_{r,q}` the supremum over all pieces and contexts of the essential time supremum over
`dom p c` and all fast phases of `‖D_Y^r D_z^q a♭(t, Y/E, z)‖`, the envelope bounds, for one
positive matrix `b` and one constant `C` fixed before the data,
`√(π_u/π_v) ∑_γ ‖C_γ‖ ∑_{d=2}^{D_γ} ∑_{|I|=d-1} ∑_{r≤Ks} ∑_{q≤Ls} E^r N_{r,q}(a♭_{γ,d,I}) ≤ C b_{vu}`
(the sum runs over the finitely many reserved orders `(r,q)`; `E^r` converts the dimensional
slow derivative to the normalized one, one factor `E^{-1}` per dimensional slow derivative). The
sum over identities, orders and words precedes the comparison, and each identity enters once. The
fields are required `C^{Ks+Ls}` in `(X,z)` near every point of the domain, so the jets are true
derivatives. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity

namespace ChartedFamily

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- Every independent field is measurable in time (at every fixed slow and fast point). -/
def IsTimeMeasurable (F : ChartedFamily ι h D P Ctx) : Prop :=
  ∀ p c v u (γ : F.Γ v u) d I (X z : Vec 2), Measurable fun t => F.flux p c v u γ d I t X z

end ChartedFamily

end AVRegularity
