-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev
public import AVRegularity.Statements.Intermediate.CoupledEnergy.MassNormSq
public import AVRegularity.Statements.Intermediate.CoupledEnergy.MassGradNormSq

/-! The physical energy error norm of the comparison proposition `cycle_comparison`:

`‖e‖_{L^∞(I;L²_π)} + √ν ‖∇e‖_{L²(I;L²_π)}` for a family of Sobolev trajectories `e_v` of orders `K_v`
with their order-`K_v+1` lifts `ew_v`: the plain `L²_π` norm (`K = 0`, truncation of the jets) of the
trajectory with the supremum of the mass sum, and the `L²_π` norm of the gradient of the lift. In
`[0,∞]`: supremum and lower integral, no junk value. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity

/-- `sup_{t∈I} (∑_v π_v⁻¹‖e_v(t)‖₂²)^{1/2} + √ν (∫_I ∑_v π_v⁻¹‖∇ew_v‖₂²)^{1/2}`. -/
def obsErrorNorm {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] (ν : ℝ) (π : ι → ℝ) (K : ι → ℕ) (t₀ t₁ : ℝ)
    (e : ∀ v, ℝ → TorusHk (K v) (h v)) (ew : ∀ v, ℝ → TorusHk (K v + 1) (h v)) : ℝ≥0∞ :=
  (⨆ t ∈ Set.Icc t₀ t₁, ENNReal.ofReal (Real.sqrt (massNormSq (E := h) (K := fun _ => 0) 1 π
      (fun v => (truncateTorusHk (Nat.zero_le _) (e v t)).val)))) +
    ENNReal.ofReal (Real.sqrt ν) *
      (∫⁻ s in Set.Icc t₀ t₁, ENNReal.ofReal (massGradNormSq (E := h) (K := fun _ => 0) 1 π
        (fun v => (truncateTorusHk (Nat.succ_le_succ (Nat.zero_le _)) (ew v s)).val))) ^ (1 / 2 : ℝ)

end AVRegularity
