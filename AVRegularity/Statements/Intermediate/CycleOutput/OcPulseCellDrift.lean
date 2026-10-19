-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleReference.OcPulse
public import AVRegularity.Statements.Intermediate.CycleReference.OcShearVel
public import AVRegularity.Statements.Intermediate.CycleReference.OcEll
public import AVRegularity.Statements.Construction.OcEpsilon

/-! The normalized cell drift of the single pulse `k` in the label cell variable `y = e z`:
`v_k(𝗍, z) = (ℓ²/e) p_k(ℓ²𝗍) 𝐮_{m,k}(e z)`, the `k`-th summand of `ocCellDrift` at the centre
`y₀ = 0` (the shear `𝐮_{m,k}` is `e`-periodic, so the centre only translates the phase). On the
enlarged pulse `k` the drift of the level is exactly this shear. -/

@[expose] public noncomputable section

open Homogenization

namespace AVRegularity

/-- `v_k(𝗍,z) = (ℓ²/e) p_k(ℓ²𝗍) 𝐮_{m,k}(e z)`, `ℓ = e/√ν`, `e = ε_m`. -/
def ocPulseCellDrift (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ) (ν : ℝ) (k : ℤ) :
    ℝ → Vec 2 → Vec 2 :=
  fun s z => (ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m) •
    (ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * s) •
      ocShearVel α q Λ m k (ocEpsilon q Λ m • z))

end AVRegularity
