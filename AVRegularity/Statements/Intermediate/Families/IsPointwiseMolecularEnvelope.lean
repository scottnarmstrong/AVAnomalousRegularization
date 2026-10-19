-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyDimFlux
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsSmoothOn
public import AVRegularity.Statements.Intermediate.Families.PointwiseMolecularJet
public import Mathlib.Analysis.Real.Sqrt

/-! The pointwise molecular envelope: `IsMolecularEnvelope` with the molecular jet `molecularJet`
replaced by `pointwiseMolecularJet`, built on the supremum over every time of the domain. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity

/-- The pointwise forward molecular envelope of `F` on its entire declared domain. It keeps the
spatial regularity, positive sums and normalization of `IsMolecularEnvelope`. -/
def IsPointwiseMolecularEnvelope {ι : Type*} {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
    {D : ℕ} {P : Type*} {Ctx : P → Type*} (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (K : ι → ℕ) (dom : F.Domain)
    (ν e E ρ : ℝ) (C : ℕ → ℝ) (J : ℕ) (b : ι → ι → ℝ) : Prop :=
  F.IsSmoothOn dom E (fun v => K v + J) ∧
  ∀ v u, ∀ j ≤ J,
    ENNReal.ofReal (Real.sqrt (π u / π v)) *
      ∑ γ : F.Γ v u, ENNReal.ofReal ‖(F.identity v u γ).map‖ *
        ∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder, ∑ I : DerivativeWord2 (d - 1),
          pointwiseMolecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
              (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I) *
            (ENNReal.ofReal (ν * ρ ^ (d - 2)))⁻¹ *
            ENNReal.ofReal (((K v + d - 2).factorial : ℝ) / ((K v).factorial : ℝ))
      ≤ ENNReal.ofReal (C j * (E ^ j)⁻¹ * b v u)

end AVRegularity
