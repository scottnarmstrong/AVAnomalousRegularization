-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Basic.Real.Basic

/-! The orientation projections `Π_k`. -/

@[expose] public section

namespace AVRegularity

/-- `Π_k = e₂ ⊗ e₂` for odd `k ≡ 1 (mod 4)` and `Π_k = e₁ ⊗ e₁` for odd `k ≡ 3 (mod 4)`
(for odd `k`, `k % 4 = 3` exactly when `k % 4 ≠ 1`). -/
def ocPi (k : {k : ℤ // Odd k}) : Matrix (Fin 2) (Fin 2) ℝ :=
  if k.1 % 4 = 1 then !![0, 0; 0, 1] else !![1, 0; 0, 0]

end AVRegularity
