-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Construction.OcEpsilon
public import AVenhance.Statements.Ingredients.Psi0
/-! The shear profiles `ψ_{m,k}` of display (1.6) of the paper. -/

@[expose] public section

open Homogenization AVenhance

namespace AVRegularity

/-- `ψ_{m,k}(y) = ε_m^β sin(2π y₁/ε_m)` for `k ∈ 4ℤ+1`, `ε_m^β sin(2π y₂/ε_m)` for
`k ∈ 4ℤ+3`, zero for even `k`; `β = 1 + α` (display (1.6) of the paper). The `AVenhance`
profile `psi0 k x` is `sin(2π x₁)`, `sin(2π x₂)`, `0` on these residue classes (coordinates
`x 0`, `x 1`). -/
noncomputable def ocShear (α q : ℝ) (Λ m : ℕ) (k : ℤ) (y : Vec 2) : ℝ :=
  ocEpsilon q Λ m ^ (1 + α) * psi0 k ((ocEpsilon q Λ m)⁻¹ • y)

end AVRegularity
