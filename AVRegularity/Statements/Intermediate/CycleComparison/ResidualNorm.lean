-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVenhance.Infra.Torus.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Homogenization.Ambient.Basic

/-! The residual norm `𝔑_ν(R,q) = ν^{-1/2} ‖R‖_{L²(I;L²_π)} + ‖q‖_{L¹(I;L²_π)}` for a flux
`R(t,x) ∈ ℝ² ⊗ 𝗁_π` and a scalar `q(t,x) ∈ 𝗁_π` on the unit torus; `L²_π` is the component sum
`∑_v π_v⁻¹ ‖·_v‖²`, the flux norm Euclidean in the direction. All integrals are lower integrals in
`[0,∞]`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization
open scoped ENNReal

namespace AVRegularity

/-- `ofReal(ν^{-1/2}) (∫⁻_I ∑_v π_v⁻¹ ∫⁻_{𝕋²} ∑_k ‖R_{k,v}‖²)^{1/2} + ∫⁻_I (∑_v π_v⁻¹ ∫⁻_{𝕋²} ‖q_v‖²)^{1/2}`. -/
def residualNorm {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    (ν : ℝ) (π : ι → ℝ) (I : Set ℝ) (R : ℝ → Vec 2 → Fin 2 → ∀ i, h i)
    (q : ℝ → Vec 2 → ∀ i, h i) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt ν)⁻¹ *
      (∫⁻ t in I, ∑ v : ι, ENNReal.ofReal (π v)⁻¹ *
        ∫⁻ x in AVenhance.unitCube, ∑ k : Fin 2, ‖R t x k v‖ₑ ^ 2) ^ (1 / 2 : ℝ)
    + ∫⁻ t in I, (∑ v : ι, ENNReal.ofReal (π v)⁻¹ *
        ∫⁻ x in AVenhance.unitCube, ‖q t x v‖ₑ ^ 2) ^ (1 / 2 : ℝ)

end AVRegularity
