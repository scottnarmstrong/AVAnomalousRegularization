-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.ChartedFamilySlowFlux
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIndex
public import AVRegularity.Statements.Intermediate.Families.FamilyDomain
public import AVRegularity.Statements.Intermediate.Families.PointwiseJetSupFam
public import Mathlib.Analysis.Real.Sqrt
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsSmoothOn

/-! The pointwise analytic envelope: `IsAnalyticEnvelope` with the essential time supremum
`jetSupFam` of the slow-flux jets replaced by `pointwiseJetSupFam`, the supremum over every time of
the domain. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity

/-- **Pointwise analytic envelope** of the charted family `F` over `dom`: `F` is smooth on `dom`
to order `Ks + Ls` at scale `E`, and for every pair of components `v, u` the weighted sum over
identities `γ`, orders `d`, derivative words `I`, slow orders `r ≤ Ks` and fast orders `q ≤ Ls` of
`E^r` times the supremum, over every time and every point of `dom`, of the `(r, q)` jets of the
slow flux is at most `C · b v u`.

The reserved constituent-jet majorants hold pointwise in time. The essential-supremum form
`IsAnalyticEnvelope` cannot see a change of the family at a single time. -/
def IsPointwiseAnalyticEnvelope {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}
    (F : ChartedFamily ι h D P Ctx) (π : ι → ℝ) (dom : F.Domain) (E : ℝ)
    (C : ℝ) (Ks Ls : ℕ) (b : ι → ι → ℝ) : Prop :=
  F.IsSmoothOn dom E (fun _ => Ks + Ls) ∧
  ∀ v u,
    ENNReal.ofReal (Real.sqrt (π u / π v)) *
      ∑ γ : F.Γ v u, ENNReal.ofReal ‖(F.identity v u γ).map‖ *
        ∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder, ∑ I : DerivativeWord2 (d - 1),
          ∑ r ∈ Finset.range (Ks + 1), ∑ q ∈ Finset.range (Ls + 1),
            ENNReal.ofReal (E ^ r) *
              pointwiseJetSupFam (fun x : F.Index => dom x.1 x.2) r q
                (fun x => F.slowFlux E x.1 x.2 v u γ d I)
      ≤ ENNReal.ofReal (C * b v u)

end AVRegularity
