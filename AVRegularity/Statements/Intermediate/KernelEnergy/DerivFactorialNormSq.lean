-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev.Norms

/-! The factorial norm of the order-`j` derivative tensor of a function, `|∇^j z|_{ρ,K}`, the
`j`-fold analogue of `gradFactorialNormSq` (the case `j = 1`). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- `|∇^j z|²_{ρ,K} = ∑_{i=0}^K ρ^{2i} ‖∇^{i+j} z‖₂² / (i!)²`, computed from the ambient
`H^{K+j}` jet: the level-`i` term is the squared `L²` Euclidean tensor norm of the full array
of ordered derivatives of order `i + j`. -/
def derivFactorialNormSq {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    {μ : Measure (Vec 2)} {K : ℕ} (j : ℕ) (ρ : ℝ) (D : JetL2 μ (K + j) E) : ℝ :=
  ∑ i : Fin (K + 1), factorialWeight ρ i.val *
    ∑ w : DerivativeWord2 (i.val + j), ‖D ⟨⟨i.val + j, by have := i.isLt; omega⟩, w⟩‖ ^ 2

end AVRegularity
