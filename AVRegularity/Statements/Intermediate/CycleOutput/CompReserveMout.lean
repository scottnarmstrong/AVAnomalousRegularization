-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleOutput.CompReserveK

/-! The model order `M_out` of the comparison proposition `cycle_comparison`:

`M_out = k + (J' + H + 3)(D_c + 8p' + 10)`, `D_c = N' + D`. -/

@[expose] public section

namespace AVRegularity

/-- `M_out = k + (J'+H+3)(D_c + 8p' + 10)`. -/
def compReserveMout (Ac Nc Jc pc D H Kmax : Nat) : Nat :=
  compReserveK Ac Nc D H Kmax + (Jc + H + 3) * ((Nc + D) + 8 * pc + 10)

end AVRegularity
