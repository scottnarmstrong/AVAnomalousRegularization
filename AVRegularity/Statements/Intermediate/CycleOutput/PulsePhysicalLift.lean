-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleComparison.LiftApply
public import AVRegularity.Statements.Intermediate.CycleComparison.LiftCoeff
public import AVRegularity.Statements.Intermediate.CycleComparison.DiagSample

/-! The local Eulerian physical lift of a coarse field on one pulse,
`𝒯_k a = ∑_{h≤H} [∑_{n=0}^N ε_c^n C_n^{(h)} a_ρ]_diag` (the corrector operator `Corr_{m,k}` of
Definition 9.8 of the paper: the field is reconstructed at `(𝗍,X,z) = (t/ℓ²,x/ρ,x/e)`,
`b_diag(t,x) = b(t,x/ρ,x/e)`, and the sum over `h` collects the physical grade-`h` lifts `𝒯_h` of
`cycle_residual_coarse_flux_presentation`), in the labels of the chart of the pulse: the Eulerian
coarse field `a(t,x)` is pulled back by the chart, `a_lift(𝗍, X) = a(c𝗍, chart(c𝗍, ρX))` (`c = ℓ²`),
and the value at the position `x` is read at the label `label(t,x)` of the particle (the inverse
chart: scalars are transported by composition). `chart`, `label` are the forward and inverse chart
maps of the pulse. -/

@[expose] public noncomputable section

open Homogenization

namespace AVRegularity

/-- `(𝒯_k a)(t,x) = ∑_{hh ≤ H} ∑_{n ≤ N} ε_c^n (C_n^{(hh)} a_lift)(t/ℓ², label_ρ, label_e)` with
`label = label(t,x)`. -/
def pulsePhysicalLift {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (c ρ e εc : ℝ) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (chart label : ℝ → Vec 2 → Vec 2) (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (x : Vec 2) : ∀ i, h i :=
  ∑ hh ∈ Finset.range (H + 1),
    diagSample c⁻¹ ρ e (fun s X z => ∑ n ∈ Finset.range (N + 1),
      εc ^ n • liftApply n (Cc hh n) (fun s' X' => a (c * s') (chart (c * s') (ρ • X'))) s X z)
      t (label t x)

end AVRegularity
