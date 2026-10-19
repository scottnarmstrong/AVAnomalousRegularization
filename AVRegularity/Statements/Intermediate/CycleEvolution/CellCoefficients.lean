-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev

/-! The coefficient data of the cell/fibre equation. -/

@[expose] public noncomputable section

open Homogenization

namespace AVRegularity

/-- Coefficients of the cell/fibre equation
`∂ₜ u = D_θ·(G D_θ u) - v·D_θ u + κ u + (source) + D_θ·F`, `D_θ = ∇ + iθ`:
`G` is the real symmetric metric `G(t,z)`, `v` the real drift `v(t,z)`, `θ = √η ξ ∈ ℂ²` the
Bloch shift (so `D_θ = D_ξ`), and `κ(t)` a scalar potential. The cell problem of
the cell inverse (`IsCellFieldInverse`) is `θ = 0`, `κ = 0`; the fibre operator `𝒢_ξ` is
`θ = √η ξ`, `κ = 0` (its zero-order terms are `-iw·ξ - ηξ·Gξ` once expanded); `𝒢̃_ξ = 𝒢_ξ - λ` is
`κ = -λ`. -/
structure CellCoefficients where
  /-- The metric `G(t,z)`. -/
  G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ
  /-- The drift `v(t,z)`. -/
  v : ℝ → Vec 2 → Vec 2
  /-- The Bloch shift `θ = √η ξ`. -/
  θ : Fin 2 → ℂ
  /-- The scalar potential `κ(t)`. -/
  κ : ℝ → ℂ

end AVRegularity
