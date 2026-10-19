-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The pointwise adjoint of a scalar flux coefficient acting diagonally on a Hilbert-valued word
array, `(A ⊗ id)^* ψ = (α ↦ ∑_k A_{kα} ψ_k)` (`F_A u = ∑_{d=2}^D A_d ∇^{d-1}u` with the scalar
coefficient `A_d`, measured by its operator-norm seminorm `𝒜_{ρ,N}(A_d)`). `A` is the coefficient as
an operator `ℝ^{words} → ℝ²`; `A_{kα} = (A e_α)_k`. -/

@[expose] public noncomputable section

open AVRegularity.Sobolev

namespace AVRegularity

/-- `(α ↦ ∑_k (A e_α)_k ψ_k)`. -/
def tensorFluxAdjoint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}
    (A : PiLp 2 (fun _ : DerivativeWord2 m => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (ψ : PiLp 2 (fun _ : Fin 2 => E)) : PiLp 2 (fun _ : DerivativeWord2 m => E) :=
  WithLp.toLp 2 fun α => ∑ k : Fin 2, (A (WithLp.toLp 2 (Pi.single α (1 : ℝ))) k) • ψ k

end AVRegularity
