-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
/-! The wavelengths `ε_m` of display (1.4) of the paper. -/

@[expose] public section


namespace AVRegularity

/-- `ε_0 = 1` and `ε_m = ⌈x_m⌉⁻¹` with `x_m = Λ^{q^m/(q-1)}` for `m ≥ 1`
(display (1.4) of the paper). -/
noncomputable def ocEpsilon (q : ℝ) (Λ : ℕ) (m : ℕ) : ℝ :=
  if m = 0 then 1 else ((⌈(Λ : ℝ) ^ (q ^ m / (q - 1))⌉₊ : ℕ) : ℝ)⁻¹

end AVRegularity
