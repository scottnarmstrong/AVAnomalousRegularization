-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Construction.OcTauP
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
/-! The slow envelope `ζ̂_{m,l}`, the slow cutoff of display (1.9) of the paper. -/

@[expose] public section


namespace AVRegularity

/-- `ζ̂_{m,l}(t) = 𝖧((t - A_l - τ_m′)/τ_m′) 𝖧((B_l - τ_m′ - t)/τ_m′)` (display (1.9) of the
paper, where `τ_m′′` is written `h_m`), with `A_l = (l - 1/2)τ_m′′`, `B_l = (l + 1/2)τ_m′′` and
`𝖧 = Real.smoothTransition`, which is literally `f(t)/(f(t) + f(1-t))` with `f(t) = exp(-1/t)`
for `t > 0`, zero otherwise. -/
noncomputable def slowEnvelope (α q : ℝ) (Λ m : ℕ) (l : ℤ) (t : ℝ) : ℝ :=
  Real.smoothTransition
      ((t - ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m - ocTauP α q Λ m) / ocTauP α q Λ m) *
    Real.smoothTransition
      ((((l : ℝ) + 1 / 2) * ocTauPP α q Λ m - ocTauP α q Λ m - t) / ocTauP α q Λ m)

end AVRegularity
