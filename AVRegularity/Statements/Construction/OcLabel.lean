-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Construction.OcTau
public import Mathlib.Algebra.Order.Floor.Ring
/-! The slot label `l_{m,k}` of display (1.8) of the paper. -/

@[expose] public section


namespace AVRegularity

/-- `l_{m,k} = ⌊(kτ_m + (τ_m′′ - τ_m)/2) / τ_m′′⌋` (display (1.8) of the paper, where `τ_m′′` is
written `h_m`). -/
noncomputable def ocLabel (α q : ℝ) (Λ m : ℕ) (k : ℤ) : ℤ :=
  ⌊((k : ℝ) * ocTau α q Λ m + (ocTauPP α q Λ m - ocTau α q Λ m) / 2) / ocTauPP α q Λ m⌋

end AVRegularity
