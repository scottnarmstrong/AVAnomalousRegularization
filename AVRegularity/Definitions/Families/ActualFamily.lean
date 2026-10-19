-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Definitions.Construction.DiagLetter

/-! **The actual-context family of a stage**. The propositions `cycle_joint` and
`cycle_comparison` take their envelopes on
`ChartedFamily.Domain.onWindow F W` (every context, every slow label) and the fluxes as measurable
functions of the time on the whole line. A stage family has neither: its fluxes are pinned to zero
off the carrier (`GenStage.IsGenerated`) and are asserted only on the output windows. The two
propositions read the family only at its actual contexts and through the partition weights,
which vanish off the output windows. So they are applied to the family with one context per
piece (the actual one), whose fluxes are those of the actual context on the output window of the
piece and zero outside it. Identities, pieces and weights are those of the stage.

The degenerate cases are included:
- A stage with no identity: the family has no field.
- A time outside every output window: every field is zero there, and so is every weight.
- At the actual context and an output time, the field is the stage's field. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

namespace GenStage

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

open scoped Classical in
/-- **The actual-context family**: one context per piece; the field of the actual context on the
output window of the piece, zero outside it. -/
def actualFamily (G : GenStage D hr Dm b j₀) :
    ChartedFamily (CompIn G.comps) (fun c => hr c.1.root) Dm OddSlot (fun _ => Unit) where
  Γ := G.fam.Γ
  fintypeΓ := G.fam.fintypeΓ
  identity := G.fam.identity
  piece := G.fam.piece
  flux := fun p _ v u γ d I t X z =>
    if t ∈ (G.fam.piece p).output then G.fam.flux p (G.actual p) v u γ d I t X z else 0
  flux_periodic := by
    intro p _ v u γ d I t X n z
    by_cases ht : t ∈ (G.fam.piece p).output
    · simp only [ht, ↓reduceIte]
      exact G.fam.flux_periodic p (G.actual p) v u γ d I t X n z
    · simp only [ht, ↓reduceIte]
  flux_zero := by
    intro p _ v u γ d I hd
    funext t X z
    by_cases ht : t ∈ (G.fam.piece p).output
    · simp only [ht, ↓reduceIte, G.fam.flux_zero p (G.actual p) v u γ d I hd]
    · simp only [ht, ↓reduceIte]
  weight := G.fam.weight
  weight_nonneg := G.fam.weight_nonneg
  weight_zero := G.fam.weight_zero
  locally_finite := G.fam.locally_finite
  weight_sum := G.fam.weight_sum

end GenStage

end AVRegularity
