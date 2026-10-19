-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleOutput.PulsePhysicalLift

/-! The glued triangular physical lift `𝒯 = ∑_l ϖ_l 𝒯_l` of the local Eulerian lifts `𝒯_l` with a
time partition `ϖ_l` (the gluing of Definition 9.8 of the paper; the triangular physical lift of a
coarse field `a` is `û = 𝒯a`), over the finite set `kset` of pulses of the window. The lift of each
pulse is `pulsePhysicalLift` with its own chart maps, lift coefficient arrays and partition
function. -/

@[expose] public noncomputable section

open Homogenization

namespace AVRegularity

/-- `(𝒯 a)(t,x) = ∑_{k ∈ kset} ϖ_k(t) (𝒯_k a)(t,x)`. -/
def gluedLift {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) (c ρ e εc : ℝ) (N H : ℕ)
    (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h) (chart label : ℤ → ℝ → Vec 2 → Vec 2)
    (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (x : Vec 2) : ∀ i, h i :=
  ∑ k ∈ kset, ϖ k t • pulsePhysicalLift c ρ e εc N H (Cc k) (chart k) (label k) a t x

end AVRegularity
