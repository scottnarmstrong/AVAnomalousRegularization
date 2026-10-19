-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Readout.Representation

/-! The image of a representation under a spatially constant component map. -/

@[expose] public section

open Homogenization

namespace AVRegularity

/-- `R` applied to the base and to every profile, each label unchanged. -/
def Representation.map {H H' : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup H'] [NormedSpace ℝ H'] (R : H →L[ℝ] H') (r : Representation H) :
    Representation H' where
  base := fun x => R (r.base x)
  profiles := r.profiles.map fun p => ((fun x => R (p.1 x)), p.2)

end AVRegularity
