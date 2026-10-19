-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.JetSup
public import Mathlib.Data.Nat.Factorial.Basic
public import AVRegularity.Statements.Intermediate.Families.JetSupFam

/-! The mixed molecular norm of a slow derivative of an independent coefficient,
`𝒥_{ρ,k}(D_X^j a) = ∑_{r+q≤k} ρ^{r+q}/(r! q! e^q) sup ‖D_X^{r+j} D_z^q a‖`, the mixed norm
applied to `D_X^j a` as in the forward molecular envelope `IsMolecularEnvelope`. -/

@[expose] public noncomputable section

open Homogenization
open scoped ENNReal

namespace AVRegularity

/-- `𝒥^W_{ρ,k}(D_Y^j a)` for an indexed collection `a = (a_i)` with domains `dom i`
(the suprema over the index are inside each jet term), fast scale
`e`, dimensional slow variable. -/
def molecularJet {ι : Type*} (ρ e : ℝ) (k j : ℕ) (dom : ι → Set (ℝ × Vec 2))
    (a : ι → ℝ → Vec 2 → Vec 2 → Vec 2) : ℝ≥0∞ :=
  ∑ r ∈ Finset.range (k + 1), ∑ q ∈ Finset.range (k + 1 - r),
    ENNReal.ofReal (ρ ^ (r + q) / ((r.factorial : ℝ) * (q.factorial : ℝ) * e ^ q)) *
      jetSupFam dom (r + j) q a

end AVRegularity
