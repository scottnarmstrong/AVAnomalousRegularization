-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleReference.StreamFlow
public import AVRegularity.Statements.Construction.OcTauPP

/-! The renewal chart `Φ_{m,l}`. -/

@[expose] public section

open Homogenization AVenhance

namespace AVRegularity

/-- `Φ_{m,l}(t,y) = X_{m-1}(t, y, l τ_m'')` where `φ = Φ (m-1)` is the stream of level `m-1`. -/
noncomputable def ocChart (α q : ℝ) (Λ m : ℕ) (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ)
    (l : ℤ) (t : ℝ) (y : Vec 2) : Vec 2 :=
  streamFlow φ hφ t y ((l : ℝ) * ocTauPP α q Λ m)

end AVRegularity
