-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleReference.OcDStar
public import AVRegularity.Statements.Intermediate.CycleReference.OcEll
public import AVRegularity.Statements.Construction.OcDelta
public import AVRegularity.Statements.Construction.OcTau
public import AVRegularity.Statements.Construction.OcTauPP
public import AVRegularity.Statements.Construction.OcEpsilon

/-! The residual bill `𝔅` of the comparison proposition `cycle_comparison`:

`𝔅 = ε_c^{N'}(1+Z) + [√(B/ν) + ε_c²(1+Z)] 𝔱 + ℓ√(B_p/τ) exp(-cτ/ℓ²)`,
`ε_c = d_*/R`, `Z = (√|I|/ℓ)(e/R)^{A'}`, `𝔱 = E^{2δ(J'+1)} + E^{δp'}`, `R = √(Bτ_m'')`,
`τ = τ_m`, `d_* = e√(B/ν)`, `ℓ = e/√ν`; `B_p` is the number of transitions (the number of pulses
of the window, bounded by `C(1+|I|/τ)`), `c` the decay constant, `|I|` the length of the window. -/

@[expose] public noncomputable section

namespace AVRegularity

/-- The bill `𝔅` for the orders `(A', N', J', p')`, window length `Tobs`, decay constant `cb` and
`Bp` transitions. -/
def compBill (α q : ℝ) (Λ m : ℕ) (ν B Tobs cb : ℝ) (Bp Ac Nc Jc pc : ℕ) : ℝ :=
  (ocDStar q Λ m ν B / Real.sqrt (B * ocTauPP α q Λ m)) ^ Nc *
      (1 + Real.sqrt Tobs / ocEll q Λ m ν *
        (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) ^ Ac)
    + (Real.sqrt (B / ν) + (ocDStar q Λ m ν B / Real.sqrt (B * ocTauPP α q Λ m)) ^ 2 *
        (1 + Real.sqrt Tobs / ocEll q Λ m ν *
          (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) ^ Ac)) *
      (ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q * ((Jc : ℝ) + 1)) +
        ocEpsilon q Λ (m - 1) ^ (ocDelta α q * (pc : ℝ)))
    + ocEll q Λ m ν * Real.sqrt ((Bp : ℝ) / ocTau α q Λ m) *
      Real.exp (-(cb * ocTau α q Λ m / ocEll q Λ m ν ^ 2))

end AVRegularity
