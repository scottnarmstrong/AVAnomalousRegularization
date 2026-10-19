-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.WeakGen.Residual.Gluing.TransitionPassage
public import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder

/-! Instantiate the original-window transition at an actual weak passage. All scalar choices
and floors precede the instance and its ambient degree cap. The degenerate cases are included:
zero readout and an empty fibre give zero forcing; at `J_w = 1` there is just one parent scale,
and no passage is asserted at `i = M`. -/

@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance AVRegularity.ChartTransport
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Residual
open Finite.WeakLift CycleComparison.Reconstruction Construction.Preservation.FullLift
open WeakEntryProofs.Assembly EntryWeakProofs

/-- The finite energy reserve of `cycle_residual_partition_differentiated` at `Acl = 1`. -/
def weakGluingTimeEnergyOrder {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B)
    (r : ℕ) : ℕ := 4 * (A.Nw + max 2 (1 + A.Jw * A.Nw)) + 18 + r

/-- The differentiated partition consumer's order. It is fixed before the level floor. -/
def weakGluingTimeReadoutOrder (plan : WeakPassagePlan) {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A) : ℕ :=
  weakGluingReadoutOrder A.Jw A.Nw (A.Jw * A.Rw) 1 (plan.forcingOrder R)

/-- The shared choice of the slot-lift parameters, stable under later increases of `levelFloor`. -/
def weakGluingTimeSlotLiftParams {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B)
    (r : ℕ) (R : WeakPassageRequest A) :
    WeakPositiveParameters A.Nw (A.Jw * A.Rw)
      (weakGluingReadoutOrder A.Jw A.Nw (A.Jw * A.Rw) 1 r + 3) :=
  weakSlotLiftParams A (weakGluingReadoutOrder A.Jw A.Nw (A.Jw * A.Rw) 1 r) R.sX R.sZ

/-- The native chart floor depends only on the coefficient base, separation and finite order. -/
def weakGluingTimeFlowFloor {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B)
    (r : ℕ) : ℕ :=
  if hΛ : 128 ≤ A.Λ then
    Classical.choose (uniform_native_physical_flow_jets B.α B.s B.q B.hα₀ B.hα₁ B.hs₀ B.hs₁
      B.hq A.Λ hΛ B.ζ B.hζ (weakGluingTimeEnergyOrder A r + 2)) else 0

/-- Numerical compatibility with the shared factory and native-flow choices. The slot-lift floor
is exactly the plan condition `WeakSlotLiftPlanOK` at the differentiated consumer's order. -/
def WeakGluingTimePlanOK (plan : WeakPassagePlan) (prices : WeakGluingPrices) : Prop :=
  WeakSlotLiftPlanOK plan (weakGluingTimeReadoutOrder plan) ∧
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A),
    weakGluingTimeEnergyOrder A (plan.forcingOrder R) ≤ prices.order R ∧
    plan.radius R ≤ 1 ∧
    ∀ j₀, weakGluingTimeFlowFloor A (plan.forcingOrder R) ≤ plan.levelFloor R j₀

/-- Both original quiet gaps of a selected slot are quiet for the edges of its slot lift. -/
theorem weak_gluing_slot_lift_original_gaps {plan : WeakPassagePlan}
    (hnative : WeakSlotNativeQuietStatement plan) {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) {i : ℕ} (hi : c.M < i) (hiJ : i ≤ c.M + A.Jw)
    {U : ℕ} {P : WeakPositiveParameters A.Nw (A.Jw * A.Rw) U}
    (slotLifts : ∀ slot : OddSlot, WeakPositiveSlot P i (c.stage i)
      (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1) slot) :
    ∀ slot : OddSlot, ∀ σ : Bool, IsQuietOn (slotLifts slot).Q.edge
      (fun t z => Real.sqrt (slotLifts slot).Q.η • (slotLifts slot).Q.v t z)
      (Set.Icc (weakGluingGapLeft (ocTau c.D.α c.D.q c.D.Λ i) slot.1 σ /
        (c.D.eps i / Real.sqrt (c.D.kap i)) ^ 2)
        (weakGluingGapRight (ocTau c.D.α c.D.q c.D.Λ i) slot.1 σ /
          (c.D.eps i / Real.sqrt (c.D.kap i)) ^ 2)) := by
  intro slot σ
  have hΛ : 1 ≤ c.D.Λ := by rw [c.base_eq]; have := (plan.base_ge B).trans c.base_ge; omega
  have hζ : IsFastProfile c.D.ζ := c.profile_eq.symm ▸ B.hζ
  let τ := ocTau c.D.α c.D.q c.D.Λ i
  let g := weakGluingGapLeft τ slot.1 σ
  let z := weakGluingGapRight τ slot.1 σ
  have hτ : 0 < τ := Construction.Stream.ocTau_pos hΛ
  obtain ⟨hd, _, _, hleft, hright⟩ := weak_gluing_original_gap_geometry hτ slot.1 σ
  have hcs : c.D.cellScaleSq i = (c.D.eps i / Real.sqrt (c.D.kap i)) ^ 2 := by
    dsimp only [OCData.cellScaleSq]
    rw [div_pow, Real.sq_sqrt (slotLifts slot).setting.ν_pos.le]
  have hcspos : 0 < c.D.cellScaleSq i :=
    weakData_cellScaleSq_pos c.D hΛ hζ
      (by rw [c.alpha, c.q_eq, c.base_eq, c.profile_eq, c.terminal]; exact c.band) i
  have hstart : c.D.cellScaleSq i * weakSlotLeft c.D i slot.1 =
      (((slot.1 : ℝ) - 61 / 48) * τ) := by
    dsimp only [weakSlotLeft, OCData.slotStart]
    rw [mul_div_cancel₀ _ hcspos.ne']
  have hend : c.D.cellScaleSq i * weakSlotRight c.D i slot.1 =
      (((slot.1 : ℝ) + 61 / 48) * τ) := by
    dsimp only [weakSlotRight]
    rw [mul_div_cancel₀ _ hcspos.ne']
  have hgdz : g + (z - g) = z := by ring
  have hq := weak_gluing_slot_lift_quiet_of_native hnative c hi hiJ slotLifts slot g (z - g)
    hd (by rw [hstart]; exact hleft) (by rw [hgdz, hend]; exact hright)
    (by rw [hgdz]; exact weak_gluing_original_gap_trimmed hΛ hζ i slot.2 σ)
  rw [hgdz, hcs] at hq
  exact hq

/-- Fix both transition constants before any passage instance. -/
def weakGluingTimeRawConstants {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B)
    (r : ℕ) (R : WeakPassageRequest A) : ℝ × ℝ :=
  let F := weakGluingTimeSlotLiftParams A r R
  let hP := weak_gluing_slot_lift_factory_orders A
    (weakGluingReadoutOrder A.Jw A.Nw (A.Jw * A.Rw) 1 r) (le_max_left _ _) R.sX R.sZ
  let hb := weak_gluing_time_classical_bound F hP le_rfl (by norm_num : 1 ≤ 1)
    (weakChartJetBudget (weakGluingTimeEnergyOrder A r + 2) 0)
    (weakChartJetBudget_ge_one _ _)
  ⟨hb.choose, hb.choose_spec.choose⟩

/-- The signs of both uniform transition constants, independently of any instance or energy. -/
theorem weak_gluing_time_raw_constants_pos {B : WeakCoefficientBase}
    (A : WeakCoefficientPhysical B) (r : ℕ) (R : WeakPassageRequest A) :
    0 ≤ (weakGluingTimeRawConstants A r R).1 ∧ 0 < (weakGluingTimeRawConstants A r R).2 := by
  let F := weakGluingTimeSlotLiftParams A r R
  let hP := weak_gluing_slot_lift_factory_orders A
    (weakGluingReadoutOrder A.Jw A.Nw (A.Jw * A.Rw) 1 r) (le_max_left _ _) R.sX R.sZ
  let gate := weak_gluing_time_classical_bound F hP le_rfl (by norm_num : 1 ≤ 1)
    (weakChartJetBudget (weakGluingTimeEnergyOrder A r + 2) 0) (weakChartJetBudget_ge_one _ _)
  exact ⟨gate.choose_spec.choose_spec.1, gate.choose_spec.choose_spec.2.1⟩

/-- The fixed polynomial and radius loss of the actual passage transition. -/
def weakGluingTimeScalarConstant (plan : WeakPassagePlan) {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A) : ℝ :=
  let K := weakGluingTimeEnergyOrder A (plan.forcingOrder R)
  let cq := (weak_gluing_parent_scale_prices B).choose
  sliceConst (A.Jw * A.Rw) (plan.forcingOrder R) (weakChartJetBudget (K + 2) 0) ^ (1 / 2 : ℝ) *
    2 * (∑ j ∈ Finset.range (plan.forcingOrder R + 1), 2 ^ j * (A.Jw * A.Rw + 1) : ℕ) *
      (weakGluingTimeRawConstants A (plan.forcingOrder R) R).1 *
      ((plan.radius R)⁻¹ ^ (2 * K)) ^ (1 / 2 : ℝ) *
      (5 * (1 + A.T₀ * (2 ^ (26 : ℕ) * 81))) * (1 + cq)

/-- Actual prices, chosen before data and Dm, with the energy reserve enlarged finitely.
The factor is a finite sum over parent levels, each with the weak quiet exponential. -/
def weakGluingTimePrices (plan : WeakPassagePlan) (seed : WeakGluingPrices) : WeakGluingPrices :=
  weakGluingParentPrices
    { seed with order := (fun {_B} {A} R =>
        max (seed.order R) (weakGluingTimeEnergyOrder A (plan.forcingOrder R))) }
    (weakGluingTimeScalarConstant plan)
    (fun {B} {_A} _ => 2 - (1 + B.α) + 4 * ocDelta B.α B.q)
    (fun {B} {A} R => (weakGluingTimeRawConstants A (plan.forcingOrder R) R).2 /
      (weak_gluing_parent_scale_prices B).choose)
    (fun {B} {_A} _ => 2 * (B.q - 1) + ocGamma B.α B.q - 4 * ocDelta B.α B.q)

/-- The chosen passage factors pay every positive forcing budget at a uniform level floor. -/
theorem weak_gluing_time_absorption (plan : WeakPassagePlan) (seed : WeakGluingPrices) :
    WeakGluingAbsorptionStatement (weakGluingTimePrices plan seed) := by
  apply weak_gluing_parent_absorption
  · intro B A R
    exact div_pos (weak_gluing_time_raw_constants_pos A (plan.forcingOrder R) R).2
      (zero_lt_one.trans_le (weak_gluing_parent_scale_prices B).choose_spec.1)
  · intro B A R
    exact weak_gluing_quiet_exponent_pos B.hα₀ B.hq.1

end AVRegularity.Providers.WeakGen.Residual
