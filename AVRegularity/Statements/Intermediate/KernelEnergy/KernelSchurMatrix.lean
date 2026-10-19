-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CoupledEnergy.CoefficientSeminorm
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The kernel-priced Schur matrix `b^S_{vu}(k)`, the coupling matrix of displays (4.9) and (7.4)
of the paper. It prices `d-2` derivatives on the kernel (`c_{d-2}/(ν r_α^{d-2})`), not the
differential-chain factorial ratio. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- `b^S_{ij}(k) = √(π_j/π_i) ∑_{α ∈ Γ_{ij}} ‖C_α‖ ∑_{d=2}^{D} c_{d-2} 𝒜_{ρ,k}(B_{α,d}) / (ν r_α^{d-2})`.
`𝒜` enters through `ENNReal.toReal`; the hypothesis "finite `𝒜_{ρ,k}`" makes this exact.
Constituents `α ∈ Γ_{ij}` have the constant component map `C_α : 𝗁_j → 𝗀_α` and the
coefficients `B_{α,d}`, `2 ≤ d ≤ D`, acting on the `(d-1)`-st derivative array of `𝗀_α`. -/
def kernelSchurMatrix {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)]
    (ν ρ : ℝ) (π : ι → ℝ) (k D : ℕ) (t₀ t₁ : ℝ) (c : ℕ → ℝ) (r : ∀ i j, Γ i j → ℝ)
    (C : ∀ i j (α : Γ i j), h j →L[ℝ] G i j α)
    (B : ∀ (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D)), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => G i j α)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (i j : ι) : ℝ :=
  Real.sqrt (π j / π i) * ∑ α : Γ i j, ‖C i j α‖ * ∑ d : ↥(Finset.Icc 2 D),
    ((coefficientSeminorm ρ k t₀ t₁ (B i j α d)).toReal * c (d.1 - 2)) /
      (ν * r i j α ^ (d.1 - 2))

end AVRegularity
