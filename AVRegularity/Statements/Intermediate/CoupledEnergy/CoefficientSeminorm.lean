-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev.Multiply.Coefficient

/-! The coefficient seminorm `𝒜_{ρ,K}(A) = ∑_{j=0}^K ρ^j/j! · sup_I ‖∇^j A‖_∞`, which measures the
coefficients in the coupling matrix (display (4.9) of the paper). -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev
open scoped ENNReal NNReal

namespace AVRegularity

/-- `𝒜_{ρ,K}(A)` on `I = [t₀, t₁]`, valued in `[0, ∞]` so that an infinite supremum is
`⊤` rather than a junk real value ("finite `𝒜`" is the hypothesis `≠ ⊤`). The norm of
`∇^j A(t,x)` is the operator norm of `coefficientDerivativeArray`: the operator from the
input space into the Euclidean array of ordered derivatives, with the derivative tensor in
the output. -/
def coefficientSeminorm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (ρ : ℝ) (K : ℕ) (t₀ t₁ : ℝ)
    (A : ℝ → Vec 2 → E →L[ℝ] F) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (K + 1), ENNReal.ofReal (ρ ^ j / (j.factorial : ℝ)) *
    ⨆ t ∈ Set.Icc t₀ t₁, ⨆ x : Vec 2, (‖coefficientDerivativeArray (A t) j x‖₊ : ℝ≥0∞)

end AVRegularity
