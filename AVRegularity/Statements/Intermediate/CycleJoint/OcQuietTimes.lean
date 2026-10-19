-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleReference.OcPulseStream
public import AVenhance.Statements.Construction.StreamVel

/-! The quiet times of the level-`m` pulses, the physical times at which the pulse velocity vanishes
(in cell time this is the characterisation `t ∈ reg.quiet ↔ ∀ z, ocCellDrift … t z = 0` of
`scalar_package_interior`). -/

@[expose] public noncomputable section

open Homogenization AVenhance

namespace AVRegularity

/-- `{t | 𝐮_m(t, y) = 0 ∀ y}` with `𝐮_m = ∇^⊥ψ` the velocity of the pulse stream `ψ` of level `m`. -/
def ocQuietTimes (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ) : Set ℝ :=
  {t | ∀ y : Vec 2, streamVel (ocPulseStream α q Λ ζ m) t y = 0}

end AVRegularity
