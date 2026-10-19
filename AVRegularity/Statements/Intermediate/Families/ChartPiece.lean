-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Homogenization.Ambient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Topology.Homeomorph.Defs

/-! A natural chart piece of a coefficient family. A piece records its renewal label,
its output-time domain `J_p`, its geometry-time interval `I_p ⊇ J_p`, its anchor time `s_p`,
and its material map `Φ_p(t,·)` (a smooth diffeomorphism of the plane, natural renewal charts
`Φ_l(t,y) = X_{m-1}(t,y,l h)`). The output interval and the geometry interval are different data
(`J_p = [(k-61/48)τ_i,(k+61/48)τ_i]`, `I_p = hull({s_p} ∪ J_p ∪ ⋃_{p' ≺ p} I_{p'})`):
coefficients live on `J_p`, geometry is available on `I_p`. No assumption of a global finite
number of pieces is made here. -/

@[expose] public section

open Homogenization

namespace AVRegularity

/-- A natural chart piece: renewal label, output interval `J_p`, geometry interval `I_p`
(containing `J_p`, with the anchor), and the smooth material map `Φ_p(t,·)`. -/
structure ChartPiece where
  /-- The renewal label `l` of the natural chart. -/
  label : ℤ
  /-- The output times `J_p` on which the coefficients of the piece are produced. -/
  output : Set ℝ
  /-- The times `I_p` on which the geometry of the piece is available. -/
  geometry : Set ℝ
  /-- The output times lie in the geometry interval. -/
  output_subset : output ⊆ geometry
  /-- The anchor time `s_p`. -/
  anchor : ℝ
  /-- The anchor lies in the geometry interval. -/
  anchor_mem : anchor ∈ geometry
  /-- The material map `Φ_p(t,·)` and its inverse, as a homeomorphism of the plane. -/
  material : ℝ → Vec 2 ≃ₜ Vec 2
  /-- Each `Φ_p(t,·)` is smooth. -/
  material_smooth : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (material t)
  /-- Each `Φ_p(t,·)⁻¹` is smooth. -/
  material_symm_smooth : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (material t).symm

end AVRegularity
