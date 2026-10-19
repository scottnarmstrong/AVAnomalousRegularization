-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyDimFlux
public import AVRegularity.Statements.Intermediate.Families.IsAnalyticEnvelope
public import AVRegularity.Statements.Intermediate.Families.MolecularJet
public import Mathlib.Analysis.Real.Sqrt
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsSmoothOn

/-! The forward molecular envelope of a charted family, uniform over its declared domains.
With the dimensional coefficients `𝔞_{γ,d,I}(t,Y,z) = ν e^{d-2} a♭_{γ,d,I}(t, Y/E, z)`:
`√(π_u/π_v) ∑_γ ‖C_γ‖ ∑_{d=2}^{D_γ} ∑_{|I|=d-1}
 𝒥^W_{ρ,K_v}(D_Y^j 𝔞_{γ,d,I})/(ν ρ^{d-2}) · (K_v+d-2)!/K_v! ≤ C_j E^{-j} b_{vu}`
for every `0 ≤ j ≤ J`. The suprema over pieces and contexts are inside `𝒥`. The fields are
required `C^{K_v + J}` near every point of the domain. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity

/-- The forward molecular envelope of `F` over `dom` at radius `ρ`, scales `(ν, e, E)`, slots
`K`, slow orders `j ≤ J` with constants `C j`, matrix `b`. -/
def IsMolecularEnvelope {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*} (F : ChartedFamily ι h D P Ctx) (π : ι → ℝ) (K : ι → ℕ)
    (dom : F.Domain) (ν e E ρ : ℝ) (C : ℕ → ℝ) (J : ℕ) (b : ι → ι → ℝ) : Prop :=
  F.IsSmoothOn dom E (fun v => K v + J) ∧
  ∀ v u, ∀ j ≤ J,
    ENNReal.ofReal (Real.sqrt (π u / π v)) *
      ∑ γ : F.Γ v u, ENNReal.ofReal ‖(F.identity v u γ).map‖ *
        ∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder, ∑ I : DerivativeWord2 (d - 1),
          molecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
              (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I) *
            (ENNReal.ofReal (ν * ρ ^ (d - 2)))⁻¹ *
            ENNReal.ofReal (((K v + d - 2).factorial : ℝ) / ((K v).factorial : ℝ))
      ≤ ENNReal.ofReal (C j * (E ^ j)⁻¹ * b v u)

end AVRegularity
