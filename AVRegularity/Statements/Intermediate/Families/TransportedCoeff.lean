-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.TransitionT
public import AVRegularity.Sobolev.Basic

/-! The transported coefficient array of a chart transition. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- The transported coefficient array at `y'`: `B d I` is the old-chart array, already
evaluated at `Υ(y')` (so a function of `(d, I)` valued in `ℝ²`, flux direction `i₀`), of maximal
order `Dγ`. For `|A| = r` the new array of order `r + 1` is
`B̃_{r+1,a₀,A}(y') = ∑_{d=r+1}^{Dγ} ∑_{|I|=d-1} ∑_{i₀} K_{a₀i₀}(y') B_{d,i₀,I} T_{I,A}(y')`. -/
def transportedCoeff (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (Dγ : ℕ)
    (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2) (r : ℕ) (A : DerivativeWord2 r)
    (y : Vec 2) : Vec 2 :=
  fun a₀ => ∑ d ∈ Finset.Icc (r + 1) Dγ, ∑ I : DerivativeWord2 (d - 1), ∑ i₀ : Fin 2,
    K y a₀ i₀ * B d I i₀ * transitionT K (List.ofFn I) (List.ofFn A) y

end AVRegularity
