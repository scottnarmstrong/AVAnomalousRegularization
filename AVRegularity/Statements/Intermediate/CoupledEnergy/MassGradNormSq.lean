-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CoupledEnergy.GradFactorialNormSq

/-! The mass-weighted gradient norm `‖∇u‖²_𝓗 = ∑_i π_i⁻¹ |∇u_i|²_{ρ,K_i}`.
-/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- `‖∇u‖²_𝓗 = ∑_i π_i⁻¹ |∇u_i|²_{ρ,K_i}`, from ambient `H^{K_i+1}` jets. -/
def massGradNormSq {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, MeasurableSpace (E i)] {μ : Measure (Vec 2)} {K : ι → ℕ} (ρ : ℝ) (π : ι → ℝ)
    (D : ∀ i, JetL2 μ (K i + 1) (E i)) : ℝ :=
  ∑ i, (π i)⁻¹ * gradFactorialNormSq ρ (D i)

end AVRegularity
