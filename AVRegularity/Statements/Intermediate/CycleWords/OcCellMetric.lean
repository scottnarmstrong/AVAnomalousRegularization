-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleReference.OcMaterialMetric
public import AVRegularity.Statements.Construction.OcEpsilon
public import AVRegularity.Statements.Intermediate.CycleReference.OcEll

/-! The material metric `G_l` of the chart `Φ_{m,l}` in the cell
variables of the cell centred at `y₀`:
`G(𝗍,z) = G_l(ℓ²𝗍, y₀ + e z)`, cell time `𝗍 = t/ℓ²`, `ℓ = e/√ν`. -/

@[expose] public noncomputable section

open Homogenization AVenhance

namespace AVRegularity

/-- `(𝗍, z) ↦ G_l(ℓ²𝗍, y₀ + e z)`. -/
def ocCellMetric (α q : ℝ) (Λ m : ℕ) (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ) (l : ℤ)
    (ν : ℝ) (y₀ : Vec 2) : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ :=
  fun τ z => ocMaterialMetric α q Λ m φ hφ l (ocEll q Λ m ν ^ 2 * τ) (y₀ + ocEpsilon q Λ m • z)

end AVRegularity
