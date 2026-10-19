-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleReference.OcRefFlux
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! The scalar mean `K̄_m^ν` of the reference flux, display (1.17) of the paper. -/

@[expose] public section

open MeasureTheory

namespace AVRegularity

/-- `K̄_m^ν`, the scalar with `K̄_m^ν I` the full mean of `J` over one period `4h`, `h = τ_m''`,
computed as half the trace of the mean over `[0, 4h]` (display (1.17) of the paper). That the full
mean equals `K̄_m^ν I` (diagonal, isotropic, independent of the window) is the identity in (1.17),
not part of this definition. -/
noncomputable def ocMeanFlux (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ) (ν : ℝ) : ℝ :=
  (1 / 2) * ((4 * ocTauPP α q Λ m)⁻¹ *
    ∫ t in (0 : ℝ)..(4 * ocTauPP α q Λ m), Matrix.trace (ocRefFlux α q Λ ζ m ν t))

end AVRegularity
