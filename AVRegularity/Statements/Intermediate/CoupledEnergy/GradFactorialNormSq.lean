-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev.Norms

/-! The gradient factorial seminorm `|∇w|²_{ρ,K}`: the factorial norm applied to the array
`∇w`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- `|∇w|²_{ρ,K} = ∑_{j=0}^K ρ^{2j} ‖∇^{j+1} w‖₂² / (j!)²`, computed from the ambient
`H^{K+1}` jet: the level-`j` term is the squared `L²` Euclidean tensor norm of the full
array of ordered derivatives of order `j+1`. -/
def gradFactorialNormSq {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    {μ : Measure (Vec 2)} {K : ℕ} (ρ : ℝ) (D : JetL2 μ (K + 1) E) : ℝ :=
  ∑ j : Fin (K + 1), factorialWeight ρ j.val *
    ∑ w : DerivativeWord2 (j.val + 1), ‖D ⟨⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩, w⟩‖ ^ 2

end AVRegularity
