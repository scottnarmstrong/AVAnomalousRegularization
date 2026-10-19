-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleReference.OcPulse
public import AVRegularity.Statements.Intermediate.CycleReference.OcMu
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! The pulse memory `M_k`. -/

@[expose] public section

open MeasureTheory

namespace AVRegularity

/-- `M_k(t) = ∫_0^∞ exp(-μ r) p_k(t - r) dr`, `μ = 4π²ν/e²`.
The integrand is continuous and supported in a half-line bounded by the compact support of
`p_k`, so the Bochner integral is a genuine integral. -/
noncomputable def ocPulseMemory (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ) (ν : ℝ) (k : ℤ)
    (t : ℝ) : ℝ :=
  ∫ r in Set.Ioi (0 : ℝ), Real.exp (-(ocMu q Λ m ν) * r) * ocPulse α q Λ ζ m k (t - r)

end AVRegularity
