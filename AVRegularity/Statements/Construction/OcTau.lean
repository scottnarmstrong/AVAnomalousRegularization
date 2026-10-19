-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Construction.OcTauPP
public import AVRegularity.Statements.Construction.OcL
/-! The pulse time `τ_m` of display (1.4) of the paper. -/

@[expose] public section


namespace AVRegularity

/-- `τ_m = τ_m′′ / L_m²` (display (1.4) of the paper, where `τ_m′′` is written `h_m`). -/
noncomputable def ocTau (α q : ℝ) (Λ m : ℕ) : ℝ := ocTauPP α q Λ m / (ocL α q Λ m : ℝ) ^ 2

end AVRegularity
