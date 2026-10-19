-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev.Norms

/-! The mass-weighted component norm `‖u‖²_𝓗 = ∑_i π_i⁻¹ |u_i|²_{ρ,K_i}`, the variable-order
norm of display (7.1) of the paper. The target spaces `E i` are an arbitrary family, so the same
definition measures the unknown (`E i = 𝗁_i`) and the flux forcing (`E i = 𝗁_i ⊗ ℝ²`). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- `‖D‖²_𝓗 = ∑_i π_i⁻¹ |D_i|²_{ρ,K_i}` on a family of ambient jets of orders `K_i`. -/
def massNormSq {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, MeasurableSpace (E i)] {μ : Measure (Vec 2)} {K : ι → ℕ} (ρ : ℝ) (π : ι → ℝ)
    (D : ∀ i, JetL2 μ (K i) (E i)) : ℝ :=
  ∑ i, (π i)⁻¹ * factorialNormSq ρ (D i)

end AVRegularity
