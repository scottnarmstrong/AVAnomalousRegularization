-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.WeakGen.Comparison.RowsHigh
public import AVRegularity.Proofs.WeakGen.Residual.Window.EmptyWindow
import AVRegularity.CycleComparison.Error.Main
import AVRegularity.EntryWeak.NormalizedSourceFluxMatrixReserve
import AVRegularity.EntryWeakAssembly.Identity.IdentityB1Level
import AVRegularity.Proofs.WeakGen.Residual.LiftedComparison
import AVRegularity.Proofs.WeakGen.Residual.Window.StoredFluxOnPlan

/-! # One weak passage at high order (Lemma 14.7 of the paper)

* `paper_weak_comparison_high`: the high weak comparison `WeakPassageComparisonHighStatement` on
  the passage plan of `entry_weak` (`weakComparisonPassagePlan weakTopSeedPlan`), its residual
  hypothesis discharged as inside `entry_weak` (`weakComparisonResidual_of_lifted`, the lifted
  comparison of the plan `weakLiftedComparison_of_plan weakTopSeedPlan_ok` and the stored-letter
  identity `weakStoredMeanFlux_on_seedPlan`). The error of a comparison input at the stage `i` has
  a representative at the component reserves whose mass norm at the radius `c ε_i` is at most
  `energyC · forceC · ε_M^{P_w + 2q^{J_w} + 1} · Φ`.
* `PaperWeakComparisonOrderStatement`, `paper_weak_comparison_order`: the same at the orders
  `N_i = (M + J_w - i) N_w + 5` of the identity (each component reserve covers `N_i`). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity.PaperFacing

open AVRegularity.WeakEntryProofs AVRegularity.WeakEntryProofs.Assembly
  AVRegularity.Providers.WeakGen.Comparison AVRegularity.Providers.WeakGen.Window

/-- **One weak passage at the component reserves** (Lemma 14.7 of the paper) on the passage plan of
`entry_weak`. -/
theorem paper_weak_comparison_high :
    WeakPassageComparisonHighStatement (weakComparisonPassagePlan weakTopSeedPlan) :=
  weak_passage_comparison_high_passage weakTopSeedPlan
    (Providers.WeakGen.Residual.weakComparisonResidual_of_lifted _
      (weakLiftedComparison_of_plan weakTopSeedPlan_ok weakStoredMeanFlux_on_seedPlan))

/-- **One weak passage at the orders `N_i = (M + J_w - i) N_w + 5`** (Lemma 14.7 of the paper): for
the passage plan of `entry_weak`, every comparison input of the stage `i`, `M < i ≤ M + J_w`, has an
error representative at the order `N_i`, equal to the error after truncation on the window
`[t_q(i), a + T]`, whose mass norm at the radius `c ε_i` is at most
`energyC · forceC · ε_M^{P_w + 2q^{J_w} + 1} · Φ`. -/
def PaperWeakComparisonOrderStatement : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A},
    A.Pw + 2 * B.q ^ A.Jw + 1 + 2 < A.Nw * (B.q - 1) →
    A.Pw + 2 * B.q ^ A.Jw + 1 + B.q ^ A.Jw + 1 < 2 * weakAStar B.α B.q * (A.Rw + 1) →
  ∀ (c : WeakPassageInstance (weakComparisonPassagePlan weakTopSeedPlan) R)
    (r : WeakPassageRun c) (i : ℕ),
    c.M < i → i ≤ c.M + A.Jw → ∀ h : WeakComparisonInput r i,
    ∃ e : ∀ v : CompIn (c.stage i).comps, ℝ →
        TorusHk ((c.M + A.Jw - i) * A.Nw + 5) (ScalarH v.1.root),
      (∀ v t, t ∈ Set.Icc (r.tq i) (r.a + A.T₀) →
        truncateTorusHk (Nat.zero_le _) (e v t) = h.e v t) ∧
      ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀),
        ∑ v, (weakMass c.D A.Nw A.Jw A.η₀ v.1)⁻¹ *
            factorialNormSq ((weakComparisonPassagePlan weakTopSeedPlan).radius R * c.D.eps i)
              (e v t).val ≤
          ((weakComparisonPassagePlan weakTopSeedPlan).energyC R *
            ((weakComparisonPassagePlan weakTopSeedPlan).forceC R *
              c.D.eps c.M ^ (A.Pw + 2 * B.q ^ A.Jw + 1) * h.Φ)) ^ 2

/-- One weak passage at the orders `N_i`, from `paper_weak_comparison_high` and the reserve bound
`N_i ≤ weakComparisonReserve R v`. -/
theorem paper_weak_comparison_order : PaperWeakComparisonOrderStatement := by
  intro B A R hN hR c r i hi hit h
  obtain ⟨ehi, hval, hbound⟩ := paper_weak_comparison_high hN hR c r i hi hit h
  have hNw : 6 ≤ A.Nw := Identity.identityA2_Nw_ge B.hq.1 B.hq.2.1 A.Pw_pos hN
  have hRw : 1 ≤ A.Rw := Identity.identityA2_Rw_pos B.hα₀ B.hα₁ B.hq.1 B.hq.2.1 A.Pw_pos hR
  have hres : ∀ v : CompIn (c.stage i).comps,
      (c.M + A.Jw - i) * A.Nw + 5 ≤ weakComparisonReserve R v.1 := by
    intro v
    have hrank := (EntryWeakProofs.weakConstruction_rank_bounds c.P _ _ _ _ _ _ c.construction i
      hi.le hit).1 v.1 v.2
    exact Identity.identityA2_reserve_ge (by omega) hRw hNw hrank
  have heps : ∀ k, 0 ≤ c.D.eps k := fun k => by
    unfold OCData.eps ocEpsilon
    split_ifs <;> positivity
  refine ⟨fun v t => truncateTorusHk (hres v) (ehi v t), fun v t ht => ?_, fun t ht => ?_⟩
  · rw [truncateTorusHk_trans]
    exact hval v t ht
  · refine le_trans (Finset.sum_le_sum fun v _ => ?_) (hbound t ht)
    exact mul_le_mul_of_nonneg_left
      (CycleComparison.Error.factorialNormSq_truncateTorusHk_le (hres v) _ _)
      (inv_nonneg.mpr (weakMass_nonneg c.D A.Nw A.Jw A.η₀ heps v.1))

end AVRegularity.PaperFacing
