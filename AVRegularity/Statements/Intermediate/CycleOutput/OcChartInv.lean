-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleReference.StreamFlow
public import AVRegularity.Statements.Construction.OcTauPP

/-! The label of the particle at position `x` at time `t` in the renewal chart `Φ_{m,l}`: since
`Φ_{m,l}(t, y) = X_{m-1}(t, y, lτ_m'')` (`ocChart`), its inverse is `x ↦ X_{m-1}(lτ_m'', x, t)` (the
flow is volume preserving). Used to pull the Eulerian coarse field back to the labels of the chart
in which a lift is built (the exact Piola transport carries fluxes by `(DΦR)∘Φ⁻¹` and scalars by
composition). -/

@[expose] public noncomputable section

open Homogenization AVenhance

namespace AVRegularity

/-- `Φ_{m,l}(t,·)⁻¹ (x) = X_{m-1}(lτ_m'', x, t)`, `φ = Φ (m-1)`. -/
def ocChartInv (α q : ℝ) (Λ m : ℕ) (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ) (l : ℤ)
    (t : ℝ) (x : Vec 2) : Vec 2 :=
  streamFlow φ hφ ((l : ℝ) * ocTauPP α q Λ m) x t

end AVRegularity
