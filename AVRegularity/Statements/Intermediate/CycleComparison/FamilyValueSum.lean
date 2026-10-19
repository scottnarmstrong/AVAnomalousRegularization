-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev
public import AVRegularity.Statements.Intermediate.CycleComparison.CoarseSlot

/-! A partial sum of the value representatives of the responses of the coarse family,
`∑_{(i,j) ∈ S} U_{i,j}` (the retained flux uses `∑_{i<J,h} U_{i,h}`, `∑_h U_{J,h}` and
`A_sum = ∑_{i,h} U_{i,h}`). The responses have different orders; the sum is read on the `L²` value
representatives. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- `x ↦ ∑_{(i,j) ∈ S} (U i j v s)(x)` on the value jets. -/
def familyValueSum {ι : Type*} {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (k J H L : ℕ) (U : ∀ (i j : ℕ) (v : ι), ℝ → TorusHk (coarseSlot k J H L i j) (h v))
    (S : Finset (ℕ × ℕ)) (v : ι) (s : ℝ) : Vec 2 → h v :=
  fun x => ∑ ij ∈ S,
    (U ij.1 ij.2 v s).toFunction.jet (valueIndex2 (coarseSlot k J H L ij.1 ij.2)) x

end AVRegularity
