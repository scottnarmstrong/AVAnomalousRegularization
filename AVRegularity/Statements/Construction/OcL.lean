-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Construction.OcEpsilon
public import AVRegularity.Statements.Construction.OcDelta
/-! The block count `L_m`, the denominator of `τ_m′` in display (1.4) of the paper. -/

@[expose] public section


namespace AVRegularity

/-- `L_m = 4⌈ε_{m-1}^{-δ}⌉ + 1`, used for `m ≥ 1` (display (1.4) of the paper: `τ_m′ = h_m / L_m`
and `τ_m = h_m / L_m²`). -/
noncomputable def ocL (α q : ℝ) (Λ m : ℕ) : ℕ :=
  4 * ⌈ocEpsilon q Λ (m - 1) ^ (-ocDelta α q)⌉₊ + 1

end AVRegularity
