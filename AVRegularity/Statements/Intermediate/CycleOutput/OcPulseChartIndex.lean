-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Construction.OcTau
public import AVRegularity.Statements.Construction.OcTauPP

/-! The index `l` of the renewal chart whose block `I_{m,l} = [(l-½)τ_m'', (l+½)τ_m'']` contains the
slot `kτ_m` of the odd pulse `k`. -/

@[expose] public noncomputable section

namespace AVRegularity

/-- `l = ⌊kτ_m/τ_m'' + ½⌋`: `(l-½)τ_m'' ≤ kτ_m < (l+½)τ_m''`. -/
def ocPulseChartIndex (α q : ℝ) (Λ m : ℕ) (k : ℤ) : ℤ :=
  ⌊(k : ℝ) * ocTau α q Λ m / ocTauPP α q Λ m + 1 / 2⌋

end AVRegularity
