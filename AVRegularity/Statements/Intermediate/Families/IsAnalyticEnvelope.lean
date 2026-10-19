-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.ChartedFamilySlowFlux
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIndex
public import AVRegularity.Statements.Intermediate.Families.FamilyDomain
public import AVRegularity.Statements.Intermediate.Families.JetSup
public import Mathlib.Analysis.Real.Sqrt
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsSmoothOn
public import AVRegularity.Statements.Intermediate.Families.JetSupFam

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

/-- The analytic envelope of `F` over `dom`, scale `E`, reserve `(Ks, Ls)`, constant `C`,
matrix `b` and masses `π`. -/
def IsAnalyticEnvelope {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*} (F : ChartedFamily ι h D P Ctx) (π : ι → ℝ) (dom : F.Domain) (E : ℝ)
    (C : ℝ) (Ks Ls : ℕ) (b : ι → ι → ℝ) : Prop :=
  F.IsSmoothOn dom E (fun _ => Ks + Ls) ∧
  ∀ v u,
    ENNReal.ofReal (Real.sqrt (π u / π v)) *
      ∑ γ : F.Γ v u, ENNReal.ofReal ‖(F.identity v u γ).map‖ *
        ∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder, ∑ I : DerivativeWord2 (d - 1),
          ∑ r ∈ Finset.range (Ks + 1), ∑ q ∈ Finset.range (Ls + 1),
            ENNReal.ofReal (E ^ r) *
              jetSupFam (fun x : F.Index => dom x.1 x.2) r q
                (fun x => F.slowFlux E x.1 x.2 v u γ d I)
      ≤ ENNReal.ofReal (C * b v u)

end AVRegularity
