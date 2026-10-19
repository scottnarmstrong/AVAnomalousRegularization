-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.ConstituentRecord
public import Mathlib.Analysis.Normed.Operator.Basic

/-! The original identity of a flux constituent: the constant map `C_γ`, the positive record
(size witness, birth list, birth level, original order, original length, original kernel width)
and the maximal current order `D_γ ≤ d_γ^birth`. One identity carries all its current orders
`2 ≤ d ≤ D_γ`: a chain-rule change of chart lowers the order without a new birth, and the
record (hence the original kernel price) is kept. Identities are summed once, never once per
order. -/

@[expose] public section

namespace AVRegularity

/-- The original identity `γ` of a flux constituent from `Hu` to `Hv`: constant map, positive
record, and the maximal current order `D_γ` with `2 ≤ D_γ ≤ min (D, d^birth_γ)`. -/
structure CoefficientIdentity (D : ℕ) (Hu Hv : Type*) [NormedAddCommGroup Hu] [NormedSpace ℝ Hu]
    [NormedAddCommGroup Hv] [NormedSpace ℝ Hv] where
  /-- The constant Hilbert map `C_γ`. -/
  map : Hu →L[ℝ] Hv
  /-- The positive record (kept through every order lowering). -/
  record : ConstituentRecord
  /-- The maximal current order `D_γ`. -/
  maxOrder : ℕ
  /-- Constituents have order at least two. -/
  two_le : 2 ≤ maxOrder
  /-- The common edge-order bound `D`. -/
  le_D : maxOrder ≤ D
  /-- The current order never exceeds the original order `d^birth_γ = birthExcess + 2`. -/
  le_birth : maxOrder ≤ record.birthExcess + 2

end AVRegularity
