-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.IterationPassage.Passage.Profiles.SmoothRep
import AVRegularity.EntryTerminal.Ingredients.LiftField.LiftField
import AVRegularity.Proofs.WeakGen.Residual.Classical.Presentation
public import AVRegularity.IterationPassage.Passage.Profiles.DiscardedCov

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Readout

/-! **The readout bound, the analytic layer: the profile norm of a classical field**
(statement only).

The readout bound of `IsWeakReadout` (clause 3) reads a family `z` at the order `L_w + 5` through
its classical representatives `a_z` of the order `L_w + 3`. The lift estimate `weak_lift_rep` takes
its input as a `Representation` at the order `L_w + 3` and bounds the output by the
`representedSize` of the input. The input is taken as the representation with zero base and the
single profile `compField π a_z` at the label `ε_M`, whose size is the profile norm of the field.

`WeakReadoutBaseSizeStatement`: for a classical family `a` of the order `n` representing `z` of
the order `n + 2`, `profileNorm e n s (compField π a) ≤ C e^{-(1+s)} |z|_{ce, n+2; π}` for
`0 < e ≤ 1`, `0 < c ≤ 1`, with `C` depending on `(n, c)` only.

It is the case `λ = e`, `ρ = c e` of `SobolevProfileStatement`: `∑_{j ≤ n} λ^{j-s} ρ^{-j-1} = e^{-(1+s)} ∑_{j ≤ n} c^{-j-1}`. The hypotheses of that
statement come from `IsClassicalRep` (`compField_contDiff_periodic`, `weakClassical_value_ae`).

Special cases:
- `z = 0`: `a = 0` almost everywhere, hence everywhere (continuous), and both sides are `0`.
- A constant `a`, one component, `π = 1`: the left side is `e^{-s}|a|`, the right side is
  `C e^{-(1+s)} |a|`; true with `C ≥ 1` because `e ≤ 1`.
- One mode `a(x) = cos(2π k·x)` with `|k| = 1/e`, `c = 1`: the left side is of order `e^{-s}`, the
  right side of order `e^{-(1+s)}`. The loss `e⁻¹` is the two-dimensional Sobolev embedding at
  the scale `e`.
- `n = 0`: the amplitude only, `e^{-s} sup|a| ≤ C e^{-(1+s)} |z|_{ce, 2; π}`.
- Empty component set: both sides are `0`.
- Constant order: `C` depends on `(n, c)`; not on the component set, the masses, `e` or `s`. -/

/-- **The profile norm of a classical field, from its scaled weighted norm two orders higher.** -/
def WeakReadoutBaseSizeStatement : Prop :=
  ∀ (s : ℝ) (n : ℕ) (c : ℝ), 0 < c → c ≤ 1 →
  ∃ C : ℝ, 0 ≤ C ∧
  ∀ {S : Finset Comp} (π : CompIn S → ℝ), (∀ v, 0 < π v) → ∀ (e : ℝ), 0 < e → e ≤ 1 →
  ∀ (z : ∀ v : CompIn S, TorusHk (n + 2) (ScalarH v.1.root)) (az : CompIn S → Vec 2 → ℝ),
    (∀ v, IsClassicalRep (z v) (az v) n) →
    profileNorm e n s (compField π (fun x v => az v x)) ≤
      ENNReal.ofReal (C * e ^ (-(1 + s)) * weightedNorm (c * e) π (fun _ => 1) z)

/-! **The readout bound, the analytic layer, from the scaled Sobolev profile bound.**

`WeakReadoutBaseSizeStatement` is the case `λ = e`, `ρ = c·e` of
`SobolevProfileStatement`, proved as `sobolevProfile`. The weights are `∑_{j ≤ n} e^{j-s} (c e)^{-j-1} =
(∑_{j ≤ n} c^{-j-1}) e^{-(1+s)}` (`profile_weight_sum_eq`), and the hypotheses on the classical
field come from `IsClassicalRep`. -/

/-- The weights of the profile bound at `λ = e`, `ρ = c·e`. -/
theorem profile_weight_sum_eq (n : ℕ) (s : ℝ) {e c : ℝ} (he : 0 < e) (hc : 0 < c) :
    ∑ j ∈ Finset.range (n + 1), e ^ ((j : ℝ) - s) * (c * e) ^ (-(j : ℝ) - 1) =
      (∑ j ∈ Finset.range (n + 1), c ^ (-(j : ℝ) - 1)) * e ^ (-(1 + s)) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Real.mul_rpow hc.le he.le]
  have h : e ^ ((j : ℝ) - s) * e ^ (-(j : ℝ) - 1) = e ^ (-(1 + s)) := by
    rw [← Real.rpow_add he]
    congr 1
    ring
  calc e ^ ((j : ℝ) - s) * (c ^ (-(j : ℝ) - 1) * e ^ (-(j : ℝ) - 1))
      = c ^ (-(j : ℝ) - 1) * (e ^ ((j : ℝ) - s) * e ^ (-(j : ℝ) - 1)) := by ring
    _ = c ^ (-(j : ℝ) - 1) * e ^ (-(1 + s)) := by rw [h]

/-- **The profile norm of a classical field from the scaled Sobolev profile bound.** -/
theorem weak_readout_base_size_of_profile
    (h : IterationPassage.Passage.SobolevProfileStatement) : WeakReadoutBaseSizeStatement := by
  intro s n c hc hc1
  obtain ⟨CK, hCK, hK⟩ := h n
  refine ⟨CK * ∑ j ∈ Finset.range (n + 1), c ^ (-(j : ℝ) - 1),
    mul_nonneg hCK (Finset.sum_nonneg fun j _ => Real.rpow_nonneg hc.le _), ?_⟩
  intro S π hπ e he he1 z az haz
  have hFc := EntryTerminal.Ingredients.compField_contDiff_periodic π n az
    (fun v => (haz v).2.1) (fun v => (haz v).2.2.1)
  have hval : ∀ v, (z v).toFunction.jet (valueIndex2 (n + 2)) =ᵐ[volume.restrict
      AVenhance.unitCube] fun x => az v x :=
    fun v => Residual.weakClassical_value_ae (haz v)
  have hρ : c * e ≤ 1 := by
    have h1 := mul_le_mul hc1 he1 he.le zero_le_one
    rwa [one_mul] at h1
  have hb := hK π hπ (c * e) e s (mul_pos hc he) hρ he z (fun x v => az v x) hFc.1 hFc.2 hval
  refine hb.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  rw [profile_weight_sum_eq n s he hc]
  ring

/-- **The profile norm of a classical field** (`WeakReadoutBaseSizeStatement`), from
`sobolevProfile`. -/
theorem weak_readout_base_size : WeakReadoutBaseSizeStatement :=
  weak_readout_base_size_of_profile IterationPassage.Passage.sobolevProfile

end AVRegularity.Providers.WeakGen.Readout
end
