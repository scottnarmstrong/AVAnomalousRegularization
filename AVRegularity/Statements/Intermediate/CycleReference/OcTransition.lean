-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleReference.StreamFlow
public import AVRegularity.Statements.Construction.OcTauPP

/-! The renewal transition maps. -/

@[expose] public section

open Homogenization AVenhance

namespace AVRegularity

/-- `X_{m-1}(l₁ h, y, l₂ h)`, `h = τ_m''`, `φ = Φ (m-1)`. With `l₂ = l₁ + 1` this is the transition
`Υ_{l₁} = X_{m-1}(l₁ h, ·, (l₁+1) h)`; with `l₁ = l₂ + 1` it is the inverse `Υ_{l₂}⁻¹`. -/
noncomputable def ocTransition (α q : ℝ) (Λ m : ℕ) (φ : ℝ → Vec 2 → ℝ)
    (hφ : IsAdmissibleStream φ) (l₁ l₂ : ℤ) (y : Vec 2) : Vec 2 :=
  streamFlow φ hφ ((l₁ : ℝ) * ocTauPP α q Λ m) y ((l₂ : ℝ) * ocTauPP α q Λ m)

end AVRegularity
