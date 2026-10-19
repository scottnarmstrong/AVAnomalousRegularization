-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleComparison.WordAdjoint
public import AVRegularity.Statements.Intermediate.CycleComparison.TensorFluxAdjoint

/-! The formal adjoint, on a smooth periodic flux test field, of the diagonal mean flux
`F_A u = ∑_{d=2}^D A_d ∇^{d-1} u` with the scalar coefficients `A_d` (the mean operator is
`M = ∂_t + 𝐛·∇ - 𝖩:D² - div F_A`, and the `A_d` are measured by the seminorms `𝒜_{ρ,N}(A_d)`). The
coefficient `A_d(t,x) : ℝ^{words d-1} → ℝ²` acts on each Hilbert component by `A_d ⊗ id`;
`F_A^* ψ = ∑_d wordAdjoint (A_d^* ψ)`. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- `F_A(t)^* ψ (x) = ∑_{d=2}^D wordAdjoint (d-1) (y ↦ (A_d(t,y) ⊗ id)^* ψ(y)) (x)`. -/
def diagonalFluxAdjoint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (D : ℕ)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (t : ℝ) (ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) : Vec 2 → E :=
  fun x => ∑ d : Finset.Icc 2 D,
    wordAdjoint (d.1 - 1) (fun y => tensorFluxAdjoint (AD d t y) (ψ y)) x

end AVRegularity
