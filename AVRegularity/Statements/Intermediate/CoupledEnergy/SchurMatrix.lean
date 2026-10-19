-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CoupledEnergy.AdmissibleOrders
public import AVRegularity.Statements.Intermediate.CoupledEnergy.CoefficientSeminorm
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The Schur matrix `b_{ii'}`: the matrix of Proposition 7.6 of the paper whose row and column
sums are at most `1/8`.
-/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- `b_{ii'} = √(π_{i'}/π_i) ∑_{d ∈ admissibleOrders} 𝒜_{ρ,K_i}(A_{ii',d}) / (ν ρ^{d-2}) · (K_i+d-2)!/K_i!`.
`𝒜` enters through `ENNReal.toReal`; the hypothesis "finite `𝒜_{ρ,K_i}`" makes this exact. -/
def schurMatrix {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] (ν ρ : ℝ) (π : ι → ℝ) (K : ι → ℕ) (D : ℕ)
    (t₀ t₁ : ℝ)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (i i' : ι) : ℝ :=
  Real.sqrt (π i' / π i) * ∑ d : admissibleOrders K D i i',
    ((coefficientSeminorm ρ (K i) t₀ t₁ (A i i' d)).toReal / (ν * ρ ^ (d.1 - 2))) *
      (((K i + d.1 - 2).factorial : ℝ) / ((K i).factorial : ℝ))

end AVRegularity
