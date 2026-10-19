-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleComparison.SourceOp
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! The coefficient `𝒮_j` of `ε^j` in `𝒮_ε = ∑_{j=0}^D ε^j 𝒮_j`. `𝒮_ε Φ` is a polynomial in `ε` of
degree at most `D` for fixed smooth `Φ`, so `𝒮_j Φ` is its `j`-th Taylor coefficient at `ε = 0`. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- `(𝒮_j Φ)(X,z) = (1/j!) (d/dε)^j|_{ε=0} (𝒮_ε Φ)(X,z)`. -/
def sourceCoeff {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} (edge : ConstituentEdges D h) (η : ℝ) (j : ℕ) (t : ℝ)
    (Φ : Vec 2 → Vec 2 → ∀ i, h i) : Vec 2 → Vec 2 → ∀ i, h i :=
  fun X z => ((j.factorial : ℝ)⁻¹) •
    iteratedDeriv j (fun ε : ℝ => sourceOp edge η ε t Φ X z) 0

end AVRegularity
