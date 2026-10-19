-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleReference.OcPulseStream
public import AVRegularity.Statements.Intermediate.CycleReference.OcEll
public import AVRegularity.Statements.Construction.OcEpsilon
public import AVenhance.Statements.Construction.StreamVel

/-! The normalized cell drift `v = ℓ²𝐮/e` of the constructed pulses
in the cell coordinate `y = y₀ + e z` and cell time `𝗍 = t/ℓ²`. -/

@[expose] public noncomputable section

open Homogenization AVenhance

namespace AVRegularity

/-- `v(𝗍, z) = (ℓ²/e) 𝐮_m(ℓ²𝗍, y₀ + e z)`, `𝐮_m = ∇^⊥ψ`, `ψ = ∑ p_k ψ_{m,k}` the pulse
stream of level `m` (`ocPulseStream`), `ℓ = e/√ν`, `e = ε_m`. -/
def ocCellDrift (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ) (ν : ℝ) (y₀ : Vec 2) :
    ℝ → Vec 2 → Vec 2 :=
  fun s z => (ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m) •
    streamVel (ocPulseStream α q Λ ζ m) (ocEll q Λ m ν ^ 2 * s)
      (y₀ + ocEpsilon q Λ m • z)

end AVRegularity
