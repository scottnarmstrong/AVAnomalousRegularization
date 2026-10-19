-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleReference.OcTransition

/-! The centres of the successive charts of a preparation cover: the same particle seen from
chart `l₀ + i`. With `Φ_{l+1} = Φ_l∘Υ_l` the label `y'` of chart `l+1` is the label `Υ_l(y')`
of chart `l`, so the centre of chart `l+1` is `Υ_l⁻¹(y_l) = X_{m-1}((l+1)h, y_l, lh)`. -/

@[expose] public noncomputable section

open Homogenization AVenhance

namespace AVRegularity

/-- `y_{l₀} = y₀` and `y_{l₀+i+1} = Υ_{l₀+i}⁻¹(y_{l₀+i})`. -/
def ocCellCentre (α q : ℝ) (Λ m : ℕ) (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ)
    (l₀ : ℤ) (y₀ : Vec 2) : ℕ → Vec 2
  | 0 => y₀
  | i + 1 => ocTransition α q Λ m φ hφ (l₀ + i + 1) (l₀ + i) (ocCellCentre α q Λ m φ hφ l₀ y₀ i)

end AVRegularity
