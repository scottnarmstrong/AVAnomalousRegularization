-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleOutput.PulseMeanField

/-! The glued mean of grade `r`, `ℳ^{(r)} = ∑_l ϖ_l ℳ_l^{(r)}`, over the finite set `kset` of
pulses of the window; each local mean is `pulseMeanField` for the lift of its pulse. -/

@[expose] public noncomputable section

open Homogenization

namespace AVRegularity

/-- `(ℳ^{(r)} a)(t,x) = ∑_{k ∈ kset} ϖ_k(t) (ℳ_k^{(r)} a)(t,x)`. -/
def gluedMean {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) (c ρ εc : ℝ) (N r : ℕ)
    (Q : ℤ → LiftOperatorData ι h D) (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h)
    (chart label : ℤ → ℝ → Vec 2 → Vec 2) (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (x : Vec 2) :
    ∀ i, h i :=
  ∑ k ∈ kset, ϖ k t • pulseMeanField c ρ εc N r (Q k) (Cc k) (chart k) (label k) a t x

end AVRegularity
