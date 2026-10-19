-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Homogenization.Ambient.Basic

/-! The diagonal sampling `b_diag(t,x) = b(𝗍,x/ρ,x/e)` of a field of the independent variables
`(𝗍,X,z)`, with the cell time `𝗍 = c t` (`c = ℓ^{-2}`). For continuous `b` the sampling is the
composition. No `L²` extension of the sampling is needed: all sampled fields in the statements are
`C^∞`. -/

@[expose] public noncomputable section

open Homogenization

namespace AVRegularity

/-- `b_diag(t,x) = b(c t, ρ⁻¹ x, e⁻¹ x)`. -/
def diagSample {E : Type*} (c ρ e : ℝ) (b : ℝ → Vec 2 → Vec 2 → E) (t : ℝ) (x : Vec 2) : E :=
  b (c * t) (ρ⁻¹ • x) (e⁻¹ • x)

end AVRegularity
