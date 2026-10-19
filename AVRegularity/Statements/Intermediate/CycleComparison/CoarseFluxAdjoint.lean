-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleComparison.CommutatorAdjoint
public import AVRegularity.Statements.Intermediate.CycleComparison.DiagonalFluxAdjoint
public import AVRegularity.Statements.Intermediate.CycleComparison.CovPolyP

/-! The formal adjoint, on a smooth periodic flux test field, of the temporal-conjugation flux
`F_p f = ∑_{l=1}^p (1/l!) ∑_{a<l} 𝒞^a 𝒥_H 𝒞^{l-1-a} f - F_A 𝖯_p f`. Since `𝒞` and `𝖯_p` are formally
self-adjoint (constant symmetric coefficients),
`F_p^* ψ = ∑_{l=1}^p (1/l!) ∑_{a<l} 𝒞^{l-1-a} 𝒥_H^* 𝒞^a ψ - 𝖯_p F_A^* ψ`, acting on each component.
-/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- `(F_p(t)^* ψ)(x)` for a vector test field `ψ` valued in `ℝ² ⊗ E`; `Hc = H_cov(t)`. -/
def coarseFluxAdjoint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (D : ℕ)
    (b : ℝ → Vec 2 → Vec 2)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (t : ℝ)
    (ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) : Vec 2 → E :=
  (∑ l ∈ Finset.Icc 1 p, ((l.factorial : ℝ)⁻¹) • ∑ a ∈ Finset.range l,
      (covOperator Hc)^[l - 1 - a]
        (commutatorAdjoint b Hc t ((covOperator Hc)^[a] ψ)))
    - covPolyP Hc p (diagonalFluxAdjoint D AD t ψ)

end AVRegularity
