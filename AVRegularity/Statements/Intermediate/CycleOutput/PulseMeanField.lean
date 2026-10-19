-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleComparison.LiftMean
public import AVRegularity.Statements.Intermediate.CycleComparison.LiftOperatorData
public import AVRegularity.Statements.Intermediate.CycleComparison.LiftCoeff

/-! The local Eulerian mean of the lift of grade `r` on one pulse,
`ℓ^{-2} ∑_{n=2}^{N+D} ε_c^n L_n^{(r)} a_ρ` (`ℓ^{-2}ε_c^n L_n^{(h)}` is the physical divergence-form
operator; the means are defined through degree `N + D`, `liftMean`), for the Eulerian coarse field
`a` pulled back to the labels of the chart of the pulse and read at the label of the position (see
`pulsePhysicalLift`). Degrees below `2` vanish (`L_0 = L_1 = 0`). -/

@[expose] public noncomputable section

open Homogenization

namespace AVRegularity

/-- `(ℳ_k^{(r)} a)(t,x) = ℓ^{-2} ∑_{n=2}^{N+D} ε_c^n (L_n^{(r)} a_lift)(t/ℓ², label(t,x)/ρ)`, `c = ℓ²`. -/
def pulseMeanField {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} (c ρ εc : ℝ) (N r : ℕ) (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (chart label : ℝ → Vec 2 → Vec 2)
    (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (x : Vec 2) : ∀ i, h i :=
  c⁻¹ • ∑ n ∈ Finset.Icc 2 (N + D), εc ^ n •
    liftMean Q Cc (fun s' X' => a (c * s') (chart (c * s') (ρ • X'))) r n (c⁻¹ * t)
      (ρ⁻¹ • label t x)

end AVRegularity
