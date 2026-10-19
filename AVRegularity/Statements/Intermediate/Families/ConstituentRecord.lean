-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Mathlib.Basic.Real.Basic

/-! The positive record of a flux constituent, kept separate from its coefficient. `size` is
the tagged size `θ^♭_γ` of the scalar coefficients, of the form
`(ε_i/R_γ)^{d_γ-2} ∑_α q_{μ_{g(v)},L_*}(a^♭_{γ,α})`, the positive witness carried by the
generated expression; it is data of the record, not computed from the real-valued coefficient
field (it measures the complex-domain analytic size). The other fields are the original birth
level `b(γ)`, original order excess `d^birth_γ - 2`, original length `R_γ`, kernel width `r_γ`,
and the levels of the births in the expression. -/

@[expose] public section

namespace AVRegularity

/-- The positive record `(θ^♭, b, d^birth - 2, R, r, birth list)` of a flux constituent. -/
structure ConstituentRecord where
  /-- The tagged size `θ^♭_γ ≥ 0` of the scalar coefficients. -/
  size : ℝ
  size_nonneg : 0 ≤ size
  /-- The birth level `b(γ)`. -/
  birthLevel : ℕ
  /-- The original order excess `d^birth_γ - 2`. -/
  birthExcess : ℕ
  /-- The original length `R_γ > 0`. -/
  length : ℝ
  length_pos : 0 < length
  /-- The kernel width `r_γ > 0`. -/
  width : ℝ
  width_pos : 0 < width
  /-- The scale indices of the births in the expression, with multiplicity. -/
  births : List ℕ

end AVRegularity
