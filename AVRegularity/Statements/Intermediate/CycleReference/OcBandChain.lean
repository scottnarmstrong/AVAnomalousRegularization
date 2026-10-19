-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleReference.OcBand
public import AVRegularity.Statements.Intermediate.CycleReference.OcMeanFlux

/-! The diffusivity recursion along the bands, display (1.19) of the paper. -/

@[expose] public section

namespace AVRegularity

/-- `κ` is a chain with terminal level `M`: `κ_M ∈ 𝒦_M` and `κ_{m-1} = K̄_m^{κ_m}` for
`1 ≤ m ≤ M` (display (1.19) of the paper). Only `κ_0, …, κ_M` are constrained; the chain is
determined by `κ_M`. -/
def IsOCBandChain (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (M : ℕ) (κ : ℕ → ℝ) : Prop :=
  κ M ∈ ocBand α q Λ M ∧
    ∀ m : ℕ, 1 ≤ m → m ≤ M → κ (m - 1) = ocMeanFlux α q Λ ζ m (κ m)

end AVRegularity
