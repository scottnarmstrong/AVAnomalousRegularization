-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.Construction.ExistsOCStreamSeq
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Construction.IsOCStreamSeq

/-! The stream recursion of display (1.12) of the paper can be carried out. -/

@[expose] public section

open Homogenization AVenhance

namespace AVRegularity

/-- For every fixed integer `Λ ≥ 128` the recursion (display (1.12) of the paper) gives smooth
`ℤ × ℤ²`-periodic streams: a stream sequence exists. It is unique by construction. -/
theorem exists_isOCStreamSeq (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ) (hΛ : 128 ≤ Λ) :
    ∃ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ :=
  by exact AVRegularity.Providers.exists_isOCStreamSeq α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ

end AVRegularity
