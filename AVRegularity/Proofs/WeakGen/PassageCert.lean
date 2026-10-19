-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.WeakGen.WeakStageHistory
public import AVRegularity.EntryWeakAssembly.Assembly.EntryCoefficientsOfIngredients

/-! **Weak entry, the weak certificate of one passage** (`weakPassageCert1`). The carrier calculus at one
level (`weakLevelComplexContext`) and the weak ledger of the passage (`weakPassageLedger`:
inherited and eddy entries), with the high-reserve lifts of the passage (`weakHighReserveLifts`
from `weakPassageLifts`). The constant map is `max Kinh Keddy`. The plan conditions are those of the carrier calculus
and the inherited weight condition. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.WeakEntryProofs.Assembly

namespace AVRegularity.Providers.WeakGen

variable {plan : WeakCoefficientPlan}

/-- The lift plan condition holds for every plan. -/
theorem weakLiftsPlanOK_all : WeakLiftsPlanOK plan :=
  fun B => (show 1 ≤ 128 by omega).trans (plan.baseThreshold_ge B)

/-- **The weak certificate of one passage.** -/
theorem weakPassageCert1 (hplan : WeakComplexContextPlanOK plan) (hLw : WeakInhPlanOK plan) :
    WeakPassageCert1Statement plan (fun R C => max (Kinh plan R C) (Keddy plan R C)) :=
  weakPassageCert_of_ingredients _ (weakLevelComplexContext hplan)
    (weakPassageLedger hplan hLw (weakHighReserveLifts (weakPassageLifts weakLiftsPlanOK_all)))

/-- **The certificate constant of the common plan**: the inherited and eddy ledger constants of
the kernel plan. The price refinement changes only `Cχ`, so these are also the constants of the
common plan. -/
def weakCertConst (basePlan : WeakCoefficientPlan) : WeakConstFn := fun R C =>
  max (Kinh (weakKernelPlan basePlan) R C) (Keddy (weakKernelPlan basePlan) R C)

/-- **The certificate for the common plan of the `entry_coefficients` assembly**, at the constant
`weakCertConst`. -/
theorem weakCommonPlan_cert (basePlan : WeakCoefficientPlan) (hplan : WeakComplexContextPlanOK basePlan)
    (hLw : WeakInhPlanOK (weakKernelPlan basePlan)) :
    WeakPassageCert1Statement (weakCommonPlan basePlan (weakCertConst basePlan))
      (weakCertConst basePlan) :=
  weakPassageCert1 (weakCommonPlan_complexContext basePlan _ hplan) hLw

end AVRegularity.Providers.WeakGen
