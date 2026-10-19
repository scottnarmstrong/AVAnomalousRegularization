-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.ChartedFamily
public import AVRegularity.Statements.Intermediate.Families.FamilyDomain

/-! The declared domains of the envelopes. For each piece `p` and context `c`,
`dom p c ⊆ ℝ × Vec 2` is the set of required pairs `(t, Y)` of output time and
**dimensional** slow label for the chosen window `W`; all real fast phases are allowed, so the
norm domain is `dom p c × 𝕋²`. Coverage is part of the interface: the domain must contain the
slow Taylor segments `(t, y₀ + s(Y - y₀))`, `0 ≤ s ≤ 1`, from the common center `y₀`, the
retained history evaluations and the images used in chart compositions; whole-space estimates
take `dom = W ×ˢ univ`. -/

@[expose] public section

open Homogenization

namespace AVRegularity

namespace ChartedFamily

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- The canonical whole-space domain over the window `W` at the output times of each piece:
`(J_p ∩ W) ×ˢ univ`. Coefficients live on `J_p`, so nothing is required of them outside it, and
no bounded patch is singled out: the global estimates cover every spatial label, with all
histories (contexts), anchor paths and slow Taylor segments. -/
def Domain.onWindow (F : ChartedFamily ι h D P Ctx) (W : Set ℝ) : F.Domain :=
  fun p _ => ((F.piece p).output ∩ W) ×ˢ Set.univ

end ChartedFamily

end AVRegularity
