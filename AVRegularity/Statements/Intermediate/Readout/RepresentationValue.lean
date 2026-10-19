-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Readout.Representation

/-! The field `U = F + ∑_l G_l` that a representation represents.
-/

@[expose] public section

open Homogenization

namespace AVRegularity

/-- `U x = F x + ∑_l G_l x`, the exact finite sum. -/
def Representation.value {H : Type*} [AddCommGroup H] (r : Representation H) : Vec 2 → H :=
  fun x => r.base x + (r.profiles.map fun p => p.1 x).sum

end AVRegularity
