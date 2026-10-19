-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Proofs.WeakGen.Residual.CoarseDefect.Setting.Main
import AVRegularity.Proofs.WeakGen.Residual.CoarseDefect.FluxRealization.Realization
import AVRegularity.Proofs.WeakGen.Residual.CoarseDefect.FrontierFlux.Main
public import AVRegularity.Proofs.WeakGen.Residual.Window.EmptyWindow
public import AVRegularity.EntryWeakAssembly.Assembly.EntryWeakOfOpen
import AVRegularity.EntryWeakAssembly.Assembly.EntryPlan.Exists
import AVRegularity.Proofs.WeakGen.Residual.CoarseDefect.Mean.Main

section
section
/-! **The lifted comparison of a weak passage with a window of positive length, under the plan
conditions**.

`weakLifted_top_window`: under `WeakTopPlanOK plan` and the one remaining statement
(`WeakCoarseStoredMeanFluxStatement plan`, the stored-letter identity of the mean presentation),
at a passage with `t_i < a + T₀`, the data of `WeakLiftedComparisonStatement` with the forcing
cost at most `forceC · ε_M^{P_w + 2q^{J_w} + 1} · Φ`. It is `weakLifted_core` at the proved
theorems, in four steps, each its own theorem (each step is elaborated as its own declaration):

* `weakTop_steps`: the four steps of the window (family, lift sequences, lift settings, scales) at
  the slot shift `weakTopK₀ A` and the constants of the slot lifts;
* `weakTop_coarse`: the coarse pieces for the families of the high-reserve energy statement (the
  coarse setting, the coarse defect with the coarse flux, the frontier flux bound, the readout
  representative, the mean presentation, the continuity of the readout);
* `weakTop_analytic`: the edge bounds and the readout energy at the constant `weakTopCs`;
* `weakTop_bill`: the bill `weakReconBill` at the flux price `ε_M^{2a_*(R_w+1)}` and the
  partition term, its five dominations, the partition price and the price of the bill
  at `δ = weakTopDelta`.

The degenerate case `Φ = 0` gives zero cost. The radius factor is `L = max 1 ρ`; the initial datum
is `cdF` at the order `weakTopNhi A`, above the coarse order and the slots. -/

@[expose] public noncomputable section

open MeasureTheory Filter Topology Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Reconstruction AVRegularity.CycleComparison.Lift
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.ChartTransport
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.EntryWeakProofs AVRegularity.Construction.Residual.Presentation
open scoped ENNReal

namespace AVRegularity.Providers.WeakGen.Window

open WeakEntryProofs WeakEntryProofs.Assembly Residual Residual.CoarseDefect
  Residual.CoarseDefect.Mean AVRegularity.Providers.WeakGen.Reduction

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

theorem nat_pred_le_succ_add (a d : ℕ) : a + d - 1 ≤ a + 1 + d := by omega

/-- **The four steps of the window** at the slot shift and the constants of the slot lifts of the
plan. -/
theorem weakTop_steps (hplan : WeakTopPlanOK plan) (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (h : WeakComparisonInput r i)
    (hlt : r.tq i < r.a + A.T₀) :
    ∃ (T : (weakWindowFamily c i hi hit).Atlas) (qs qf : ℕ)
      (bM : CompIn (c.stage i).comps → CompIn (c.stage i).comps → ℝ),
      WeakFamilyBody c r i hi hit (weakTopK₀ A) T weakCpart ∧
      WeakSettingBody c r i hi hit h (weakTopK₀ A) qs qf (weakSlotLiftUParams A (weakTopLr A) R.sX R.sZ).CG (weakSlotLiftUParams A (weakTopLr A) R.sX R.sZ).Cw (weakSettingCa (weakSlotLiftUParams A (weakTopLr A) R.sX R.sZ) (weakSettingQs A (weakTopK₀ A)) (weakSettingQf A (weakTopK₀ A))) (weakSlotLiftUParams A (weakTopLr A) R.sX R.sZ).S (weakGradeConst A (weakTopK₀ A) (weakSlotLiftUParams A (weakTopLr A) R.sX R.sZ).CG (weakSlotLiftUParams A (weakTopLr A) R.sX R.sZ).Cw (weakSettingCa (weakSlotLiftUParams A (weakTopLr A) R.sX R.sZ) (weakSettingQs A (weakTopK₀ A)) (weakSettingQf A (weakTopK₀ A)))) bM ∧
      (∀ k ∈ ocObsPulses c.D.α c.D.q c.D.Λ i (r.tq i) (r.tq i + wTobs c r i),
        IsLiftSequence (wLiftData c i hi hit k) (weakKlift A (weakTopK₀ A) + weakDw A + 2)
          (max (weakLlift A (weakTopK₀ A) + 1) (weakLlift A (weakTopK₀ A) + 2))
          (wSeqStart c r i k) (wSeqEnd c r i k) A.Nw (weakH A) (h.CcR i k)) ∧
      WeakScaleBody c r i := by
  have hcommon := hplan.common
  obtain ⟨hXs, hZs⟩ := weakTop_lift_orders hplan.lift h.sX_ge h.sZ_ge
  have hseqS := weakSeqStep_of_plan ⟨hcommon, hplan.ell⟩ c r i hi hit h (weakTopK₀ A)
  obtain ⟨T, hfam⟩ := weakFamilyStep_of_common hcommon c r i hi hit (weakTopK₀ A) hlt
  obtain ⟨qs, qf, bM, hset⟩ :=
    weakSettingStep_of_plan c r i hi hit hplan.slotLifts h (weakTopK₀ A) le_rfl hXs hZs hseqS hlt
  exact ⟨T, qs, qf, bM, hfam, hset, hseqS hlt hXs hZs,
    weakScaleBody_of c r i hi (weakPassage_two_le_M hcommon c) hlt⟩

/-- **The coarse pieces** for the families of the high-reserve energy statement, in the forms of `weakLifted_core`. -/
theorem weakTop_coarse (hplan : WeakTopPlanOK plan)
    (hflux : WeakCoarseStoredMeanFluxStatement plan)
    (hN : A.Pw + 2 * B.q ^ A.Jw + 1 + 2 < A.Nw * (B.q - 1))
    (hR : A.Pw + 2 * B.q ^ A.Jw + 1 + B.q ^ A.Jw + 1 < 2 * weakAStar B.α B.q * (A.Rw + 1))
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (h : WeakComparisonInput r i) (hle : r.tq i ≤ r.a + A.T₀)
    (Uhi : ∀ j, WeakStageFamily (weakPassageRawSetting c) (weakEntryMmax R) j)
    (Whi : ∀ j, WeakStageLift (weakPassageRawSetting c) (weakEntryMmax R) j)
    (hpass : ∀ j, c.M < j → j ≤ c.M + A.Jw →
      WeakStagePassage (weakPassageRawSetting c) (weakPassageRawClock r) (weakEntryMmax R) Uhi Whi j)
    (hval : ∀ j, c.M < j → j ≤ c.M + A.Jw → ∀ v : CompIn (c.stage (j - 1)).comps,
      ∀ t ∈ Set.Icc (r.tq j) (r.a + A.T₀),
        truncateTorusHk (weakReductionReserve_kw_le R (weakEntryMmax R) v.1) (Uhi (j - 1) v t) =
          r.Ur (j - 1) v t)
    (v₀ : CompIn (c.stage i).comps)
    (hk : (weakTopKc A) + 1 + (A.Nw + weakDw A) ≤ R.Kw + (weakEntryMmax R)) (hN₀ : (weakTopKc A + (0 + weakH A + 3) * ((A.Nw + weakDw A) + 8 * 1 + 4)) ≤ R.Kw + (weakEntryMmax R)) :
    ∃ (aC B₀C lamC : ℝ)
      (Aedge : Matrix (CompIn (c.stage i).comps) (CompIn (c.stage i).comps) ℝ) (Cstar Θc : ℝ)
      (Fc₀ : ∀ v : CompIn (c.stage i).comps, ℝ →
        TorusHk (weakTopKc A) (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))),
      IsCoarseSetting (r.tq i) (r.a + A.T₀) (wRhoC c i) (c.D.κ c.M) aC B₀C lamC
        (streamVel (c.D.Φ (i - 1))) (A.Nw + weakDw A) (weakH A) 1 0 (weakTopKc A) ((A.Nw + weakDw A) + 8 * 1 + 4) (weakTopKc A + (0 + weakH A + 3) * ((A.Nw + weakDw A) + 8 * 1 + 4)) (wJm c) (cdAD c (A.Nw + weakDw A) i v₀) (cdCE c (A.Nw + weakDw A) i hi hit)
        (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1) Aedge Cstar Θc ∧
      IsCoarseDefect (r.tq i) (r.a + A.T₀) (c.D.κ c.M) (streamVel (c.D.Φ (i - 1))) (A.Nw + weakDw A)
        (weakH A) (weakTopKc A) (weakTopKc A + (0 + weakH A + 3) * ((A.Nw + weakDw A) + 8 * 1 + 4)) (cdAD c (A.Nw + weakDw A) i v₀) (cdCE c (A.Nw + weakDw A) i hi hit) (wJm c) (cdF c r (weakEntryMmax R) (weakTopKc A + (0 + weakH A + 3) * ((A.Nw + weakDw A) + 8 * 1 + 4)) (fun w => hN₀.trans (weakReductionReserve_kw R (weakEntryMmax R) w)) i Uhi) (fun v t => cdW c (weakEntryMmax R) (weakTopKc A + 1 + (A.Nw + weakDw A)) (fun w => hk.trans (weakReductionReserve_kw R (weakEntryMmax R) w)) i Uhi v t) Fc₀ ∧
      FluxMassLe (ι := CompIn (c.stage i).comps) (h := fun v => ScalarH v.1.root)
        (K := fun _ => (weakTopKc A)) (c.D.κ c.M) (ocEpsilon c.D.q c.D.Λ (i - 1))
        (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1) (Set.Icc (r.tq i) (r.a + A.T₀)) Fc₀
        (max 1 (plan.radius R)⁻¹ ^ (weakTopKc A) * (weakFrontierFluxConst (plan.radius R) R * (c.D.eps c.M ^ (2 * weakAStar B.α B.q * (A.Rw + 1))) * h.Φ)) ∧
      (∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀), ∀ v,
        IsClassicalRep (cdW c (weakEntryMmax R) (weakTopKc A + 1 + (A.Nw + weakDw A)) (fun w => hk.trans (weakReductionReserve_kw R (weakEntryMmax R) w)) i Uhi v t)
          (fun x => weakReadoutStep i A.η₀ (c.stage i) (c.stage (i - 1)) (h.aU t) v x)
          ((weakTopKc A) + (A.Nw + weakDw A) - 1)) ∧
      (∀ ρ ∈ Finset.range (weakH A + 1),
        IsMeanPresentation (Set.Icc (r.tq i) (r.a + A.T₀)) (A.Nw + weakDw A) ρ (cdAD c (A.Nw + weakDw A) i v₀) (cdCE c (A.Nw + weakDw A) i hi hit) (wJm c)
          (gluedMean (ocObsPulses c.D.α c.D.q c.D.Λ i (r.tq i) (r.a + A.T₀))
            (fun k => (weakWindowFamily c i hi hit).weight (oddSlotOf k))
            (ocEll c.D.q c.D.Λ i (c.D.κ c.M) ^ 2) (ocEpsilon c.D.q c.D.Λ (i - 1))
            (ocDStar c.D.q c.D.Λ i (c.D.κ c.M) (c.D.κ c.M) / ocEpsilon c.D.q c.D.Λ (i - 1))
            A.Nw ρ (fun k => wLiftData c i hi hit k) (h.CcR i)
            (fun k => ocChart c.D.α c.D.q c.D.Λ i (c.D.Φ (i - 1)) (c.D.hΦ (i - 1))
              (ocPulseChartIndex c.D.α c.D.q c.D.Λ i k))
            (fun k => ocChartInv c.D.α c.D.q c.D.Λ i (c.D.Φ (i - 1)) (c.D.hΦ (i - 1))
              (ocPulseChartIndex c.D.α c.D.q c.D.Λ i k)))) ∧
      (∀ v, ContinuousOn (fun t => cdW c (weakEntryMmax R) (weakTopKc A + 1 + (A.Nw + weakDw A)) (fun w => hk.trans (weakReductionReserve_kw R (weakEntryMmax R) w)) i Uhi v t) (Set.Icc (r.tq i) (r.a + A.T₀))) := by
  have hcommon := hplan.common
  have hokR := hplan.coarse
  obtain ⟨hkOf3, -, -, hkOf, -, -⟩ := weakTop_request_orders hokR c
  have hDc : 1 + A.Jw * A.Nw ≤ A.Nw + weakDw A := Nat.le_add_left _ _
  have hRw := weakMenu_one_le_Rw A hR
  obtain ⟨aC, B₀C, lamC, Aedge, Cstar, Θc, hcs⟩ :=
    weakCoarseSetting plan hcommon hokR.1 R c r i hi hit v₀ (weakTopKc A) hle
  obtain ⟨Fc₀, hreal⟩ := weakCoarseFluxExists plan (fun {_B} {A} _ => weakTopKOf A) hcommon R (A.Nw + weakDw A)
    (weakEntryMmax R) (weakTopKc A) hDc le_rfl hk hkOf hkOf3 c r Uhi Whi hpass i hi hit h v₀ (hval i hi hit)
  refine ⟨aC, B₀C, lamC, Aedge, Cstar, Θc, Fc₀, hcs, ?_, ?_, ?_, ?_, ?_⟩
  · exact weakCoarseDefect plan hcommon R (A.Nw + weakDw A) (weakEntryMmax R) (weakTopKc A) (weakTopKc A + (0 + weakH A + 3) * ((A.Nw + weakDw A) + 8 * 1 + 4)) hDc hk hN₀ c r Uhi Whi hpass i hi hit v₀
      Fc₀ hreal
  · exact weakFrontierFluxFinal hcommon hokR R (A.Nw + weakDw A) (weakEntryMmax R) (weakTopKc A) hDc le_rfl hk hkOf hkOf3 hN hR c r Uhi
      Whi hpass i hi hit h v₀ Fc₀ (hval i hi hit) hreal
  · intro t ht v
    exact cdW_isClassicalRep plan (fun {_B} {A} _ => weakTopKOf A) R (weakEntryMmax R) ((weakTopKc A) + 1 + (A.Nw + weakDw A))
      ((weakTopKc A) + (A.Nw + weakDw A) - 1) le_rfl hkOf3 hk (nat_pred_le_succ_add _ _) (Nat.le_succ_of_le hkOf) c r Uhi
      i hi hit h (hval i hi hit) v t ht
  · intro ρ hρ
    exact weakCoarseMean_of_storedFlux hcommon hplan.mean hflux R hRw c r i hi hit h v₀ ρ
      (Nat.lt_succ_iff.1 (Finset.mem_range.1 hρ))
  · intro v
    exact cdW_continuousOn c r (weakEntryMmax R) ((weakTopKc A) + 1 + (A.Nw + weakDw A)) _ i Uhi Whi (hpass i hi hit) v

/-- **The analytic pieces**: the coefficient bounds, and the readout energy bound at the two energy orders with the constant
`weakTopCs`. -/
theorem weakTop_analytic (hplan : WeakTopPlanOK plan) (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (h : WeakComparisonInput r i)
    (Uhi : ∀ j, WeakStageFamily (weakPassageRawSetting c) (weakEntryMmax R) j)
    (Whi : ∀ j, WeakStageLift (weakPassageRawSetting c) (weakEntryMmax R) j)
    (hpass : ∀ j, c.M < j → j ≤ c.M + A.Jw →
      WeakStagePassage (weakPassageRawSetting c) (weakPassageRawClock r) (weakEntryMmax R) Uhi Whi j)
    (hvr : ∀ v : CompIn (c.stage (c.M + A.Jw)).comps,
      ∀ t ∈ Set.Icc (r.tq (c.M + A.Jw + 1)) (r.a + A.T₀),
      truncateTorusHk (weakReductionReserve_kw_le R (weakEntryMmax R) v.1) (Uhi (c.M + A.Jw) v t) =
        r.Ur (c.M + A.Jw) v t)
    (hval : ∀ j, c.M < j → j ≤ c.M + A.Jw → ∀ v : CompIn (c.stage (j - 1)).comps,
      ∀ t ∈ Set.Icc (r.tq j) (r.a + A.T₀),
        truncateTorusHk (weakReductionReserve_kw_le R (weakEntryMmax R) v.1) (Uhi (j - 1) v t) =
          r.Ur (j - 1) v t)
    (hk : (weakTopKc A) + 1 + (A.Nw + weakDw A) ≤ R.Kw + (weakEntryMmax R)) :
    0 ≤ h.Φ ∧
    Residual.WeakReconBoundsAt c r i (weakWindowSlots c i (weakTopK₀ A)) (weakReconDriftBound B A.Λ)
      (weakReconEdgeBound c r i) ∧
    strongEnergyUpTo (ocEpsilon c.D.q c.D.Λ (i - 1)) (c.D.κ c.M) (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
      (r.tq i) (r.a + A.T₀) (weakReconPartitionOrder (weakTopOrders A)) (fun v t => cdW c (weakEntryMmax R) (weakTopKc A + 1 + (A.Nw + weakDw A)) (fun w => hk.trans (weakReductionReserve_kw R (weakEntryMmax R) w)) i Uhi v t) ≤
        ENNReal.ofReal (weakTopCs (plan.radius R) R * h.Φ) ∧
    strongEnergyUpTo (ocEpsilon c.D.q c.D.Λ (i - 1)) (c.D.κ c.M) (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
      (r.tq i) (r.a + A.T₀) (weakMprime A (weakTopK₀ A)) (fun v t => cdW c (weakEntryMmax R) (weakTopKc A + 1 + (A.Nw + weakDw A)) (fun w => hk.trans (weakReductionReserve_kw R (weakEntryMmax R) w)) i Uhi v t) ≤
        ENNReal.ofReal (weakTopCs (plan.radius R) R * h.Φ) := by
  have hcommon := hplan.common
  have hok := hplan.coarse.1
  have hΦ : 0 ≤ h.Φ := (Real.sqrt_nonneg _).trans (h.mass_bound (r.a + A.T₀)
    ⟨(weakRun_tq_succ_le r hi hit).trans (weakRun_tq_le_window r hi hit), le_rfl⟩)
  refine ⟨hΦ, weakReconBounds plan hcommon c r i hi hit _, ?_, ?_⟩
  · exact (weakReadoutWindowEnergy hcommon hok R (A.Nw + weakDw A) (weakEntryMmax R) (weakTopKc A) (weakReconPartitionOrder (weakTopOrders A)) le_rfl hk
      (weakTopKc_ord A) c r h.start Uhi Whi hpass hvr hval i hi hit h).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hΦ))
  · exact (weakReadoutWindowEnergy hcommon hok R (A.Nw + weakDw A) (weakEntryMmax R) (weakTopKc A) (weakMprime A (weakTopK₀ A)) le_rfl hk
      (weakTopKc_mprime A) c r h.start Uhi Whi hpass hvr hval i hi hit h).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_right _ _) hΦ))

theorem weakReconPartitionBillTerm_nonneg (O : WeakReconPartitionOrders A)
    (c : WeakPassageInstance plan R) (i : ℕ) (hΛ : 1 ≤ c.D.Λ) :
    0 ≤ weakReconPartitionBillTerm O c i :=
  mul_nonneg (mul_nonneg (div_nonneg (Construction.Stream.ocEpsilon_pos hΛ).le
    (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)) (Real.exp_pos _).le

/-- **The bill of the weak window**: its sign, the partition price, the five dominations and its
price at `δ = weakTopDelta`. -/
theorem weakTop_bill (hplan : WeakTopPlanOK plan)
    (hN : A.Pw + 2 * B.q ^ A.Jw + 1 + 2 < A.Nw * (B.q - 1))
    (hR : A.Pw + 2 * B.q ^ A.Jw + 1 + B.q ^ A.Jw + 1 < 2 * weakAStar B.α B.q * (A.Rw + 1))
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (hΛ : 1 ≤ c.D.Λ) :
    0 ≤ (c.D.eps c.M ^ (2 * weakAStar B.α B.q * (A.Rw + 1))) ∧ 0 ≤ (weakReconBill c r i (c.D.eps c.M ^ (2 * weakAStar B.α B.q * (A.Rw + 1))) (weakReconPartitionBillTerm (weakTopOrders A) c i)) ∧
    0 ≤ weakReconPartitionBillConstant (weakTopOrders A) R ∧
    0 ≤ weakReconPartitionFactor (weakTopOrders A) c r i ∧
    weakReconPartitionFactor (weakTopOrders A) c r i ≤ weakReconPartitionBillConstant (weakTopOrders A) R * (weakReconBill c r i (c.D.eps c.M ^ (2 * weakAStar B.α B.q * (A.Rw + 1))) (weakReconPartitionBillTerm (weakTopOrders A) c i)) ∧
    ((ocDStar c.D.q c.D.Λ i (c.D.κ c.M) (c.D.κ c.M) /
      ocEpsilon c.D.q c.D.Λ (i - 1)) ^ A.Nw ≤ (weakReconBill c r i (c.D.eps c.M ^ (2 * weakAStar B.α B.q * (A.Rw + 1))) (weakReconPartitionBillTerm (weakTopOrders A) c i))) ∧
    (Real.sqrt (c.D.κ c.M / c.D.κ c.M) * (c.D.eps c.M ^ (2 * weakAStar B.α B.q * (A.Rw + 1))) ≤ (weakReconBill c r i (c.D.eps c.M ^ (2 * weakAStar B.α B.q * (A.Rw + 1))) (weakReconPartitionBillTerm (weakTopOrders A) c i))) ∧
    ((ocDStar c.D.q c.D.Λ i (c.D.κ c.M) (c.D.κ c.M) /
      ocEpsilon c.D.q c.D.Λ (i - 1)) ^ 2 * (c.D.eps c.M ^ (2 * weakAStar B.α B.q * (A.Rw + 1))) ≤ (weakReconBill c r i (c.D.eps c.M ^ (2 * weakAStar B.α B.q * (A.Rw + 1))) (weakReconPartitionBillTerm (weakTopOrders A) c i))) ∧
    ((ocDStar c.D.q c.D.Λ i (c.D.κ c.M) (c.D.κ c.M) /
      ocEpsilon c.D.q c.D.Λ (i - 1)) ^ A.Nw *
      (Real.sqrt (wTobs c r i) / ocEll c.D.q c.D.Λ i (c.D.κ c.M) *
        (ocEpsilon c.D.q c.D.Λ i / ocEpsilon c.D.q c.D.Λ (i - 1)) ^ weakAcl) ≤ (weakReconBill c r i (c.D.eps c.M ^ (2 * weakAStar B.α B.q * (A.Rw + 1))) (weakReconPartitionBillTerm (weakTopOrders A) c i))) ∧
    ((ocDStar c.D.q c.D.Λ i (c.D.κ c.M) (c.D.κ c.M) /
      ocEpsilon c.D.q c.D.Λ (i - 1)) ^ 2 *
      (Real.sqrt (wTobs c r i) / ocEll c.D.q c.D.Λ i (c.D.κ c.M) *
        (ocEpsilon c.D.q c.D.Λ i / ocEpsilon c.D.q c.D.Λ (i - 1)) ^ weakAcl) * (c.D.eps c.M ^ (2 * weakAStar B.α B.q * (A.Rw + 1))) ≤ (weakReconBill c r i (c.D.eps c.M ^ (2 * weakAStar B.α B.q * (A.Rw + 1))) (weakReconPartitionBillTerm (weakTopOrders A) c i))) ∧
    (weakReconBill c r i (c.D.eps c.M ^ (2 * weakAStar B.α B.q * (A.Rw + 1))) (weakReconPartitionBillTerm (weakTopOrders A) c i)) ≤ weakTopDelta (plan.radius R) (plan.forceC R) R *
      c.D.eps c.M ^ (A.Pw + 2 * B.q ^ A.Jw + 1) := by
  have htt : 0 ≤ (c.D.eps c.M ^ (2 * weakAStar B.α B.q * (A.Rw + 1))) := Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ).le _
  have hXt := weakReconPartitionBillTerm_nonneg (weakTopOrders A) c i hΛ
  have hge := weakReconBill_ge_partition c r i hΛ htt (Xp := weakReconPartitionBillTerm (weakTopOrders A) c i)
  have hwin := weak_quiet_window c r i hi hit
  obtain ⟨hCpx, hXp, hPM⟩ := weakReconPartition_pay_bill plan (fun {_B} {A} _ => weakTopOrders A)
    hplan.partitionPrice c r i hi hit hge
  exact ⟨htt, hXt.trans hge, hCpx, hXp, hPM, weakReconBill_ge₁ c r i hΛ htt hXt,
    weakReconBill_ge₂ c r i hΛ htt hXt, weakReconBill_ge₃ c r i hΛ htt hXt,
    weakReconBill_ge₄ c r i hΛ htt hXt, weakReconBill_ge₅ c r i hΛ htt hXt,
    weakReconBill_price (weakTopOrders A) c r i (weakTopDelta_pos (hplan.force R) R) hN hR hi hit
      (hwin.1.trans hwin.2.2.1.le) (hplan.price R c.j₀)⟩

/-- **The lifted comparison of a weak passage with a window of positive length**, under the plan
conditions and the stored-letter identity of the mean presentation. -/
theorem weakLifted_top_window (hplan : WeakTopPlanOK plan)
    (hflux : WeakCoarseStoredMeanFluxStatement plan)
    (hN : A.Pw + 2 * B.q ^ A.Jw + 1 + 2 < A.Nw * (B.q - 1))
    (hR : A.Pw + 2 * B.q ^ A.Jw + 1 + B.q ^ A.Jw + 1 < 2 * weakAStar B.α B.q * (A.Rw + 1))
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (h : WeakComparisonInput r i) (hlt : r.tq i < r.a + A.T₀) :
    ∃ (F : ∀ v : CompIn (c.stage i).comps, ℝ →
        TorusHk (plan.forcingOrder R) (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
      (g : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk (plan.forcingOrder R) (ScalarH v.1.root))
      (uΛ : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk 0 (ScalarH v.1.root))
      (wΛ : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk (0 + 1) (ScalarH v.1.root))
      (YΛ : ∀ v u (_ : (c.stage i).fam.Γ v u), ℝ →
        TorusHk (0 + (1 + A.Jw * A.Nw) - 1) (ScalarH u.1.root)),
      (∀ v, AEStronglyMeasurable (F v) (volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀)))) ∧
      (∀ v, AEStronglyMeasurable (g v) (volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀)))) ∧
      (∀ v, ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀),
        (uΛ v t).toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict unitCube]
          fun x => weakGluedLift i A.Nw (A.Jw * A.Rw) (c.stage i) (h.CcR i) t
            (weakReadoutStep i A.η₀ (c.stage i) (c.stage (i - 1)) (h.aU t)) v x) ∧
      (∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀))),
        truncateTorusHk (Nat.le_succ 0) (wΛ v t) = uΛ v t) ∧
      WeakErrSol c r i (weakIncomingInit r i) (weakNegTruncF c i F) (weakNegTruncG c i g)
        uΛ wΛ YΛ ∧
      weakComparisonForcingCost r i F g ≤
        ENNReal.ofReal (plan.forceC R * c.D.eps c.M ^ (A.Pw + 2 * B.q ^ A.Jw + 1) * h.Φ) := by
  have hcommon := hplan.common
  obtain ⟨hkOf3, hk, hNhi, -, hN₀Nhi, hKmNhi⟩ := weakTop_request_orders hplan.coarse c
  have hN₀ : (weakTopKc A + (0 + weakH A + 3) * ((A.Nw + weakDw A) + 8 * 1 + 4)) ≤ R.Kw + (weakEntryMmax R) := hN₀Nhi.trans hNhi
  obtain ⟨Uhi, Whi, hpass, hvr, hval, -⟩ :=
    weakCoarse_high_energy_at hcommon hplan.coarse.1 R (weakEntryMmax R) le_rfl c r h.start
  obtain ⟨v₀⟩ := weakStage_nonempty c i hi.le hit
  obtain ⟨T, qs, qf, bM, hfam, hset, hseq, hsc⟩ := weakTop_steps hplan c r i hi hit h hlt
  have hsc' := hsc
  obtain ⟨-, -, -, -, -, -, hΛ128, -, -, -, -, -, -, -, hεle, -⟩ := hsc'
  have hΛ : 1 ≤ c.D.Λ := le_trans (by norm_num) hΛ128
  have hεi := Construction.Stream.ocEpsilon_pos (q := c.D.q) (n := i) hΛ
  obtain ⟨aC, B₀C, lamC, Aedge, Cstar, Θc, Fc₀, hcs, hcd₀, hF, hrep, hmean, hWc₀⟩ :=
    weakTop_coarse hplan hflux hN hR c r i hi hit h hlt.le Uhi Whi hpass hval v₀ hk hN₀
  obtain ⟨hΦ, hb, hEn₀, hX₀⟩ := weakTop_analytic hplan c r i hi hit h Uhi Whi hpass hvr hval hk
  obtain ⟨htt, hbill0, hCpx, hXp, hPM, hb1, hb2, hb3, hb4, hb5, hprice⟩ :=
    weakTop_bill hplan hN hR c r i hi hit hΛ
  obtain ⟨hXst, hinit⟩ := weakInit_at_window (weakCoarseInitial plan) R (weakEntryMmax R) (weakTopNhi A) hNhi c r
    Uhi hvr hval i hi hit hlt.le hN₀Nhi
  have hw := weakStage_weight c i hi.le hit
  have hπ : ∀ v : CompIn (c.stage i).comps, 0 < weakMass c.D A.Nw A.Jw A.η₀ v.1 := fun v =>
    weakMass_pos c.D A.Nw A.Jw A.η₀ A.Nw_pos A.Jw_pos
      (fun n => Construction.Stream.ocEpsilon_pos hΛ) v.1
  obtain ⟨F, g, uΛ, wΛ, YΛ, h1, h2, h3, h4, h5, h6⟩ := weakLifted_core c r i hi hit h (weakTopK₀ A)
    (weakTopK₀_ge A) (hplan.forcing R) hΛ hπ hw hfam hset hseq hsc (weakSlotLiftUParams A (weakTopLr A) R.sX R.sZ).S_nonneg
    (weakGradeConst_nonneg A (weakTopK₀ A) _ _ _) (weakTopKc_floor A) hcs hcd₀ hF hrep hmean hWc₀ hb
    (mul_nonneg (weakTopCs_nonneg (plan.radius R) R) hΦ) ((Real.sqrt_nonneg _).trans hF.2) hΦ htt
    (weakTopCs_nonneg (plan.radius R) R) (abs_nonneg _) hCpx (weakTopKc_ord A) hEn₀ hX₀ hεi
    le_rfl hεle hXp
    (fun hcc => weakWindowPartition_of_recon (fun {_B} {A} _ => weakTopOrders A) hplan.partition
      c r i hi hit h hw hεi le_rfl _ hcc)
    le_rfl (weakTop_flux_const hΦ htt) hPM hb1 hb2 hb3 hb4 hb5 (fun _ => weakTopNhi A)
    (fun v => cdF c r (weakEntryMmax R) (weakTopNhi A)
      (fun w => hNhi.trans (weakReductionReserve_kw R (weakEntryMmax R) w)) i Uhi v)
    (fun _ => hN₀Nhi) (fun v => (weakWindowSlots_le c i (weakTopK₀ A) v).trans hKmNhi) hXst hinit
    (L := weakTopL (plan.radius R)) (le_max_left _ _)
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hεi.le)
  exact ⟨F, g, uΛ, wΛ, YΛ, h1, h2, h3, h4, h5, h6.trans
    (weakPrice_close_ofReal (Cb := weakTopBillConst (plan.radius R) R) (weakKmax A (weakTopK₀ A))
      (zero_le_one.trans (le_max_left _ _)) hΦ hbill0 hprice)⟩

end AVRegularity.Providers.WeakGen.Window
end
end

section
/-! **The lifted comparison of the weak passages**.

`weakLiftedComparison_of_plan`: under the plan conditions `WeakTopPlanOK plan` and the
stored-letter identity of the mean presentation (`WeakCoarseStoredMeanFluxStatement plan`, the
one remaining statement), `WeakLiftedComparisonStatement plan`. The window `[t_i, a + T₀]`
has positive length (`weakLifted_top_window`: the physical lift of the reconstruction window at
the weak window, with its price) or length zero (`weakLifted_top_empty`: the constant family at
`U(t_i)` and zero forcing).

`entry_weak_of_plans`: the weak entry from the two plans: an entry plan with
`WeakEntryLanePlanOK`, a passage plan whose comparison refinement has `WeakTopPlanOK`, and the
stored-letter identity on that refinement.

The degenerate cases are included: `i = M + 1` with `t_{M+1} = a + T₀` is the second case; for
`i ≥ M + 2` the window has positive length (`t_{i} + τ'_{i-1} ≤ t_{i-1}`), but the proof does not
use it. -/

@[expose] public noncomputable section

namespace AVRegularity.Providers.WeakGen.Window

open WeakEntryProofs WeakEntryProofs.Assembly Residual Residual.CoarseDefect.Mean
  AVRegularity.Providers.WeakGen.Comparison

variable {plan : WeakPassagePlan}

/-- **The lifted comparison of the weak passages**, from the plan conditions and the stored-letter
identity of the mean presentation. -/
theorem weakLiftedComparison_of_plan (hplan : WeakTopPlanOK plan)
    (hflux : WeakCoarseStoredMeanFluxStatement plan) : WeakLiftedComparisonStatement plan := by
  intro B A R hN hR c r i hi hit h
  rcases (weakRun_tq_le_window r hi hit).lt_or_eq with hlt | heq
  · exact weakLifted_top_window hplan hflux hN hR c r i hi hit h hlt
  · exact weakLifted_top_empty hplan c r i hi hit h heq _

/-- **The weak entry from the two plans** and the stored-letter identity of the mean presentation. -/
theorem entry_weak_of_plans (plan : WeakEntryGluePlan) (pp₀ : WeakPassagePlan)
    (hentry : WeakEntryLanePlanOK plan (weakComparisonPassagePlan pp₀))
    (hplan : WeakTopPlanOK (weakComparisonPassagePlan pp₀))
    (hflux : WeakCoarseStoredMeanFluxStatement (weakComparisonPassagePlan pp₀)) :
    EntryWeakStatement :=
  entry_weak_of_lifted plan pp₀ hentry (weakLiftedComparison_of_plan hplan hflux)

end AVRegularity.Providers.WeakGen.Window
end
end
end

section
section
/-! **The weak entry from the stored-letter identity of the mean presentation**.

`entry_weak_of_storedFlux`: `EntryWeakStatement` follows from ONE statement,
`WeakCoarseStoredMeanFluxStatement` on the plan `weakComparisonPassagePlan weakTopSeedPlan` (the
remaining leaf of the mean presentation: the grade flux of the stored letters is minus the glued
Eulerian flux of the native mean coefficients). Everything else is proved: the lifted comparison
under the plan conditions (`weakLiftedComparison_of_plan`), the passage plan (`weakTopSeedPlan_ok`),
the entry plan on it (`weakEntryLanePlan_exists`).

`weak_passage_comparison_of_storedFlux`: the comparison of the weak passages from the
same statement.

The hypothesis is at one fixed plan; a proof of the stored-letter identity for every plan, or
under plan conditions among those of `WeakTopPlanOK`, applies. -/

@[expose] public noncomputable section

namespace AVRegularity.Providers.WeakGen.Window

open WeakEntryProofs WeakEntryProofs.Assembly Residual.CoarseDefect.Mean
  AVRegularity.Providers.WeakGen.Comparison

/-- **The weak entry from the stored-letter identity of the mean presentation.** -/
theorem entry_weak_of_storedFlux
    (hflux : WeakCoarseStoredMeanFluxStatement (weakComparisonPassagePlan weakTopSeedPlan)) :
    EntryWeakStatement := by
  obtain ⟨plan, hentry⟩ := weakEntryLanePlan_exists weakTopSeedPlan trivial
  exact entry_weak_of_plans plan weakTopSeedPlan hentry weakTopSeedPlan_ok hflux

/-- **The comparison of the weak passages from the stored-letter identity of
the mean presentation.** -/
theorem weak_passage_comparison_of_storedFlux
    (hflux : WeakCoarseStoredMeanFluxStatement (weakComparisonPassagePlan weakTopSeedPlan)) :
    WeakPassageComparisonStatement :=
  weak_passage_comparison_of_lifted weakTopSeedPlan
    (weakLiftedComparison_of_plan weakTopSeedPlan_ok hflux)

end AVRegularity.Providers.WeakGen.Window
end
end

section
/-! **The plan conditions of the reduction of the mean presentation**.

The stored-letter identity `WeakCoarseStoredMeanFluxStatement` is reduced to
`WeakCoarsePhysicalFluxStatement` (the grade flux of the stored letters is the glued native mean
flux in physical variables) by
`weakCoarseStoredMeanFlux_of_physical`, under three plan conditions: `WeakPassageCommonOK`,
`WeakCoarseMeanPlanOK` and `1 + J_wN_w ≤ liftFloor`. All three follow from `WeakTopPlanOK`:

* `WeakTopPlanOK.liftCap`, `WeakTopPlanOK.liftOrder`: the lift floor of a plan with the top
  conditions is above `N_w + 1 + D_w`, hence above `D_w = 1 + J_wN_w` (the orders asked of the
  request by the path decomposition and by the reduction).

So no plan condition is left between the physical flux identity and the stored-letter identity.
`K_lift ≥ D_w (H + 1) N_w ≥ N_w` uses `D_w ≥ 1` only; the three hypotheses of the reduction are
fields of, or follow from, the bundle, for every plan. -/

@[expose] public noncomputable section

namespace AVRegularity.Providers.WeakGen.Window

open WeakEntryProofs WeakEntryProofs.Assembly Residual Residual.CoarseDefect.Mean
  AVRegularity.Providers.WeakGen.Comparison

variable {plan : WeakPassagePlan}

/-- **The lift floor of a plan with the top conditions is above `N_w + 1 + D_w`.** -/
theorem WeakTopPlanOK.liftCap (hplan : WeakTopPlanOK plan) {B : WeakCoefficientBase}
    (A : WeakCoefficientPhysical B) :
    A.Nw + 1 + (1 + A.Jw * A.Nw) ≤ plan.liftFloor A := by
  have hD : 0 < weakDw A := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_add_right 1 _)
  have h1 : A.Nw ≤ weakDw A * (weakH A + 1) * A.Nw :=
    Nat.le_mul_of_pos_left _ (Nat.mul_pos hD (Nat.succ_pos _))
  have h2 : A.Nw + 1 + (1 + A.Jw * A.Nw) ≤ weakKlift A (weakTopK₀ A) + weakDw A + 2 := by
    show A.Nw + 1 + (1 + A.Jw * A.Nw) ≤
      2 * weakAcl + 2 + weakKmax A (weakTopK₀ A) + weakDw A * (weakH A + 1) * A.Nw + 2 +
        (1 + A.Jw * A.Nw) + 2
    generalize weakDw A * (weakH A + 1) * A.Nw = P at h1 ⊢
    generalize weakKmax A (weakTopK₀ A) = K
    generalize A.Jw * A.Nw = JN
    omega
  exact h2.trans ((le_max_left _ _).trans (hplan.lift A))

/-- The lift floor of a plan with the top conditions is above `D_w = 1 + J_wN_w`. -/
theorem WeakTopPlanOK.liftOrder (hplan : WeakTopPlanOK plan) {B : WeakCoefficientBase}
    (A : WeakCoefficientPhysical B) : 1 + A.Jw * A.Nw ≤ plan.liftFloor A :=
  (Nat.le_add_left _ _).trans (hplan.liftCap A)

end AVRegularity.Providers.WeakGen.Window
end
end

section
/-! **The stored-letter identity of the mean presentation on the plan** (the one place where
the weak-entry argument takes the proof of the stored-letter identity,
`Mean.weakCoarseStoredMeanFlux`).

Its three plan hypotheses are the plan's: `WeakPassageCommonOK` (`weakTopSeedPlan_common`),
`WeakCoarseMeanPlanOK` (`weakTopSeedPlan_mean`) and the lift floor
`N_w + 1 + (1 + J_wN_w) ≤ liftFloor` (`weakTopSeedPlan_liftCap`).

The degenerate cases are included: `J_w = 1` (one passage: the floor is `2 N_w + 2`); an empty
pulse set (the glued mean is `0` and the stored sum is empty). -/

@[expose] public noncomputable section

namespace AVRegularity.Providers.WeakGen.Window

open WeakEntryProofs WeakEntryProofs.Assembly Residual.CoarseDefect.Mean
  AVRegularity.Providers.WeakGen.Comparison

/-- **The stored-letter identity on the plan.** -/
theorem weakStoredMeanFlux_on_seedPlan :
    WeakCoarseStoredMeanFluxStatement (weakComparisonPassagePlan weakTopSeedPlan) :=
  weakCoarseStoredMeanFlux weakTopSeedPlan_common weakTopSeedPlan_mean
    (fun A => weakTopSeedPlan_liftCap A)

end AVRegularity.Providers.WeakGen.Window
end
end
end
