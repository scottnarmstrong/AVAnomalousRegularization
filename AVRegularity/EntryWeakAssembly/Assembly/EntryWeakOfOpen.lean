-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeakAssembly.PairedDifference
public import AVRegularity.EntryWeakAssembly.Identity.IdentityFinal
import AVRegularity.Proofs.Results.EntryWeak.WeakPassageQuietTrace
import AVRegularity.Proofs.WeakGen.Reduction.ScalarIdentification
public import AVRegularity.Proofs.WeakGen.Residual.CoarseEnergy.ReadoutNamed
public import AVRegularity.Proofs.WeakGen.Residual.Gluing.TransitionPlan
import AVRegularity.Proofs.WeakGen.Reduction.PassageEnergy

/-! **The weak entry from the weak residual** (top assembly).

`entry_weak_of_residual : EntryWeakStatement` has one analytic hypothesis, the weak residual
`WeakComparisonResidualStatement` on the passage plan `pp = weakComparisonPassagePlan pp₀`. The
first gluing term, the readout energy with the raw frontier estimate, the comparison and the
comparison at the reserves, the weak identity, the readout bound and linearity, the reduction,
the pair, the schedule, the coefficients and the quiet trace (`weak_passage_quiet_trace`) are
proved and are used here.

**Plan conditions** (the common plan; no analysis):
* `WeakPassageLanePlanOK pp pricesS seed`: the conditions of the readout energy, of the price of the slot residuals and of the first gluing term on
  the passage plan;
* `WeakEntryLanePlanOK plan pp`: the conditions of the entry plan, with `IdentityPlanOK plan pp`
  tying the two plans.
Their joint satisfiability is the common plan. The price floor of the first gluing term
(`priceT`) reads the constant of the readout energy through a choice.

`entry_weak_of_lifted` and `weak_passage_comparison_of_lifted` take instead
`WeakLiftedComparisonStatement pp`, the conclusion of the reconstruction window at a weak
passage, which gives the weak residual (`weakComparisonResidual_of_lifted`).

The assembly is a composition of implications; with `J_w = 1` the hypotheses are at the single
level `M + 1`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance

namespace AVRegularity.WeakEntryProofs.Assembly

open AVRegularity.Providers.WeakGen AVRegularity.Providers.WeakGen.Residual
  AVRegularity.Providers.WeakGen.Reduction AVRegularity.Providers.WeakGen.Comparison
  AVRegularity.WeakEntryProofs.Identity AVRegularity.WeakEntryProofs.ReadoutLinear
  AVRegularity.Providers.WeakGen.Readout

/-- **The plan conditions of the passage side**: (iv) at the two energy orders, the price of the
slot residuals at the named constant of (iv), and the conditions of the first gluing term. -/
structure WeakPassageLanePlanOK (pp : WeakPassagePlan) (pricesS seed : WeakGluingPrices) :
    Prop where
  common : WeakPassageCommonOK pp
  coarseS : WeakCoarseReadoutPlanOK pp pricesS.order
  priceS : WeakGluingPricePlanOK pp pricesS (fun R => weakCoarseReadoutConst (pp.radius R) R)
  coarseT : WeakCoarseReadoutPlanOK pp (weakGluingTimePrices pp seed).order
  time : WeakGluingTimePlanOK pp (weakGluingTimePrices pp seed)
  force : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A),
    0 < pp.forceC R
  priceT : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (j₀ : ℕ),
    weakGluingPriceFloor pp (weakGluingTimePrices pp seed) (weakCoarseReadoutEnergy common coarseT)
      (weak_gluing_time_absorption pp seed) force R ≤ pp.levelFloor R j₀

/-- **The plan conditions of the entry side.** -/
structure WeakEntryLanePlanOK (plan : WeakEntryGluePlan) (pp : WeakPassagePlan) : Prop where
  common : WeakEntryCommonOK plan
  wait : WeakScheduleWaitStatement plan
  rawEnergy : WeakEntryRawEnergyPlanOK plan
  paired : WeakEntryPairedPlanOK plan
  pairedDiff : WeakEntryPairedDiffPlanOK plan
  linear : WeakReadoutLinearPlanOK plan
  bound : WeakReadoutBoundPlanOK weak_readout_base_size plan
  identity : WeakReadoutIdentityPlanOK plan pp

/-- **The readout from its three parts.** -/
theorem weak_entry_readout_of_parts (plan : WeakEntryGluePlan)
    (hlin : WeakReadoutLinearStatement plan) (hbound : WeakReadoutBoundStatement plan)
    (hid : WeakReadoutIdentityStatement plan) : WeakEntryReadoutStatement plan :=
  fun _ _ _ _ _ _ g s law hm hr f θ hθ r p hp =>
    weak_entry_readout_parts plan hlin hbound hid g s law hm hr f θ hθ r p hp

/-- **The weak entry from the weak residual** on the energy refinement of a passage plan, under the plan conditions
of the entry side. -/
theorem entry_weak_of_residual (plan : WeakEntryGluePlan) (pp₀ : WeakPassagePlan)
    (hok : WeakEntryLanePlanOK plan (weakComparisonPassagePlan pp₀))
    (hres : WeakComparisonResidualStatement (weakComparisonPassagePlan pp₀)) :
    EntryWeakStatement :=
  entry_weak_of_ingredients Providers.entry_coefficients weak_passage_quiet_trace_at
    (weak_passage_comparison_at_of_residual pp₀ hres) plan hok.common
    (weak_entry_schedule_of_wait_and_models plan hok.wait (weak_full_readout_models plan))
    (weak_entry_reduction plan hok.common)
    (weak_entry_pair_of_ingredients plan (weak_entry_raw_solution plan)
      (weak_entry_raw_energy_of_ingredients plan hok.common hok.rawEnergy
        (weakEntryPassageEnergy hok.common hok.identity.passageEnergy)
        (weak_entry_quiet_trace_high hok.common hok.identity.quietTrace))
      (weak_entry_paired_solve plan hok.common hok.paired)
      (weak_entry_paired_difference plan hok.common hok.pairedDiff))
    (weak_entry_readout_of_parts plan (weakReadoutLinear plan hok.linear)
      (weak_entry_readout_bound plan hok.bound)
      (weak_readout_identity_final plan _ hok.identity
        (weak_passage_comparison_high_passage pp₀ hres)))

/-- **The weak entry from the lifted comparison**: under the plan conditions of the
entry side, the one analytic hypothesis is `WeakLiftedComparisonStatement` on the
passage plan. -/
theorem entry_weak_of_lifted (plan : WeakEntryGluePlan) (pp₀ : WeakPassagePlan)
    (hentry : WeakEntryLanePlanOK plan (weakComparisonPassagePlan pp₀))
    (hL : WeakLiftedComparisonStatement (weakComparisonPassagePlan pp₀)) : EntryWeakStatement :=
  entry_weak_of_residual plan pp₀ hentry (weakComparisonResidual_of_lifted _ hL)

/-- **The weak passage comparison from the lifted comparison.** -/
theorem weak_passage_comparison_of_lifted (pp₀ : WeakPassagePlan)
    (hL : WeakLiftedComparisonStatement (weakComparisonPassagePlan pp₀)) :
    WeakPassageComparisonStatement :=
  weak_passage_comparison_of_residual pp₀ (weakComparisonResidual_of_lifted _ hL)

end AVRegularity.WeakEntryProofs.Assembly
