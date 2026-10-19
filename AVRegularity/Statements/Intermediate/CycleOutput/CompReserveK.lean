-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

/-! The coarse field reserve `k` of the comparison proposition `cycle_comparison`:

`D_c = N' + D`, `k = 4D_c + 2A' + 16 + K_* + Δ_*`, with `Δ_* = max_paths ∑(d_{vu} - 2)`.
`K_*` is replaced by the supplied bound `Kmax ≥ max_v K_v` and `Δ_*` by `H(D-2)` (every path has at
most `H` edges of order at most `D`): the reserve is only required to be sufficient, so larger
values serve. -/

@[expose] public section

namespace AVRegularity

/-- `k = 4(N'+D) + 2A' + 16 + K_* + H(D-2)`. -/
def compReserveK (Ac Nc D H Kmax : Nat) : Nat :=
  4 * (Nc + D) + 2 * Ac + 16 + Kmax + H * (D - 2)

end AVRegularity
