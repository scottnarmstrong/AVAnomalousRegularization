-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleReference.OcChart
public import AVRegularity.Statements.Intermediate.CycleReference.JacMatrix

/-! The material metric `G_l = F_l⁻¹ F_l⁻ᵀ`. -/

@[expose] public section

open Homogenization AVenhance
open scoped Matrix

namespace AVRegularity

/-- `G_l(t,y) = F⁻¹ F⁻ᵀ` with `F = D_y Φ_{m,l}(t,·)(y)`. The Jacobian `F` has determinant one,
so the matrix inverse is the genuine inverse. -/
noncomputable def ocMaterialMetric (α q : ℝ) (Λ m : ℕ) (φ : ℝ → Vec 2 → ℝ)
    (hφ : IsAdmissibleStream φ) (l : ℤ) (t : ℝ) (y : Vec 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  (jacMatrix (ocChart α q Λ m φ hφ l t) y)⁻¹ * ((jacMatrix (ocChart α q Λ m φ hφ l t) y)⁻¹)ᵀ

end AVRegularity
