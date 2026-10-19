-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.PhysicalCoefficient
public import AVRegularity.Statements.Intermediate.CoupledEnergy.CoefficientSeminorm
public import Mathlib.Analysis.Real.Sqrt
public import AVRegularity.Statements.Intermediate.Families.ConstituentPhysical

/-! The forward envelope of the sampled physical coefficient on the observation window
`[t₀,t₁]`, bounded by the same positive matrix: the sampled factorial norm `𝒜^W_{ρ,k}(B^phys)` of
the forward physical estimate, with the same positive constituent sums and factorial/order
normalization as `IsMolecularEnvelope` at `j = 0`:
`√(π_u/π_v) ∑_γ ∑_{d=2}^{D} 𝒜_{ρ,K_v}(a^phys_{γ,d})/(ν ρ^{d-2}) · (K_v+d-2)!/K_v! ≤ C b_{vu}`.
The constituents are summed after the norms (positive sums before cancellation); the operator
`a^phys_{γ,d}` contains the constant map `C_γ`. The norm is over the whole plane (the global
estimates require coverage of every spatial label), valued in `[0,∞]` so that an infinite norm is
not a junk zero. The physical coefficient is `C^{K_v}` in space at every time of the window. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity

/-- The sampled forward envelope of `physicalCoefficient`'s constituents at radius `ρ`, slots
`K`, on `[t₀,t₁]`, constant `C`, matrix `b`, actual contexts `actual`. -/
def IsSampledEnvelope {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}
    (F : ChartedFamily ι h D P Ctx) (π : ι → ℝ) (K : ι → ℕ) (actual : ∀ p, Ctx p)
    (t₀ t₁ ν e E ρ C : ℝ) (b : ι → ι → ℝ) : Prop :=
  (∀ v u (γ : F.Γ v u) (d : ℕ), ∀ s ∈ Set.Icc t₀ t₁,
      ContDiff ℝ (K v : ℕ) (constituentPhysical F ν e E actual v u γ d s)) ∧
  ∀ v u,
    ENNReal.ofReal (Real.sqrt (π u / π v)) *
      ∑ γ : F.Γ v u, ∑ d ∈ Finset.Icc 2 D,
        coefficientSeminorm ρ (K v) t₀ t₁ (constituentPhysical F ν e E actual v u γ d) *
          (ENNReal.ofReal (ν * ρ ^ (d - 2)))⁻¹ *
          ENNReal.ofReal (((K v + d - 2).factorial : ℝ) / ((K v).factorial : ℝ))
      ≤ ENNReal.ofReal (C * b v u)

end AVRegularity
