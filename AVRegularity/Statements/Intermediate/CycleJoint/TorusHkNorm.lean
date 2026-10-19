-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev

/-! The factorial norm `|f|_{ρ,K}` of a periodic Sobolev function
(`|w|_{ρ,K}² = ∑_{j≤K} ρ^{2j}‖∇^j w‖₂²/(j!)²`) of order `K`, of an element of the carrier `H^L` with
`K ≤ L` (truncation to the first `K` jets; the order inequality is an argument, there is no junk
value). With `K = 0` it is the `L²` norm. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- `|f|_{ρ,K} = (factorialNormSq ρ (first K jets of f))^{1/2}` for `f ∈ H^L`, `K ≤ L`. -/
def torusHkNorm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [CompleteSpace E] (ρ : ℝ) {K L : ℕ} (hKL : K ≤ L) (f : TorusHk L E) : ℝ :=
  Real.sqrt (factorialNormSq ρ (truncateTorusHk hKL f).val)

end AVRegularity
