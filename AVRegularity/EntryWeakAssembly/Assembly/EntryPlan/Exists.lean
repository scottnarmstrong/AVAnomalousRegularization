-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeakAssembly.Assembly.EntryWeakOfOpen

@[expose] public noncomputable section
section

section
namespace AVRegularity.WeakEntryProofs.Assembly

section
/-! **The plan-free floors of the entry plan**.

Every floor below is a function of the base, the menu and the request only (no plan, no passage
plan, no datum). `weakEntryBaseFloor`, `weakEntryMomentFloor`, `weakEntryLiftFloor`,
`weakEntryLevelFloor` are the maxima of the floors that the conditions of
`WeakEntryLanePlanOK` ask.

Two floors are defined here: the wait floor (`weak_schedule_wait_threshold` made into named floors,
with `weakScheduleWait_of_floors`) and the forcing-cost floor (`ε_M^{σ_w} ≤ 1/2048`).

The degenerate cases are included: `J_w = N_w = 1` (no order appears); `m_max(R) = 0` (the
supremum over `m` has one term); `A.Λ < 128` (the wait and forcing floors are `0` there, never
used). -/

section
open AVRegularity.Providers.WeakGen AVRegularity.Providers.WeakGen.Residual
  AVRegularity.Providers.WeakGen.Reduction AVRegularity.WeakEntryProofs.Identity
  AVRegularity.Providers.WeakGen.Comparison

/-! ### The wait floors -/

/-- The base floor of the wait condition (from `weak_schedule_wait_threshold`). -/
def weakWaitBaseFloor (B : WeakCoefficientBase) : ℕ :=
  (weak_schedule_wait_threshold B).choose

theorem weakWaitBaseFloor_spec (B : WeakCoefficientBase) :
    128 ≤ weakWaitBaseFloor B ∧ ∀ Λ : ℕ, weakWaitBaseFloor B ≤ Λ → ∀ (J : ℕ) (τ : ℝ),
      0 < τ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
        (1 + 2 * (J : ℝ)) * ocTauPP B.α B.q Λ (M + 1) ≤ τ :=
  (weak_schedule_wait_threshold B).choose_spec

/-- The level floor of the wait condition. -/
def weakWaitLevelFloor {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) : ℕ :=
  if h : weakWaitBaseFloor B ≤ A.Λ then
    ((weakWaitBaseFloor_spec B).2 A.Λ h A.Jw A.τ A.τ_pos).choose
  else 0

theorem weakWaitLevelFloor_spec {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B)
    (h : weakWaitBaseFloor B ≤ A.Λ) (M : ℕ) (hM : weakWaitLevelFloor A ≤ M) :
    (1 + 2 * (A.Jw : ℝ)) * ocTauPP B.α B.q A.Λ (M + 1) ≤ A.τ := by
  unfold weakWaitLevelFloor at hM
  rw [dite_eq_left_of_eq_true (eq_true h)] at hM
  exact ((weakWaitBaseFloor_spec B).2 A.Λ h A.Jw A.τ A.τ_pos).choose_spec M hM

/-- **The wait statement from two floors.** -/
theorem weakScheduleWait_of_floors (plan : WeakEntryGluePlan)
    (hb : ∀ B, weakWaitBaseFloor B ≤ plan.baseFloor B)
    (hl : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
      (C : WeakEntryAllocation R (plan.radius R)) (j₀ : ℕ),
      weakWaitLevelFloor A ≤ plan.levelFloor R C j₀) : WeakScheduleWaitStatement plan := by
  intro B A R C x
  have := weakWaitLevelFloor_spec A ((hb B).trans x.base_ge) x.M ((hl R C x.j₀).trans x.level_ge)
  exact_mod_cast this

/-! ### The forcing-cost floor -/

/-- The level floor with `ε_M^{σ_w} ≤ 1/2048` (for `A.Λ ≥ 128`). -/
def weakEntryForcingFloor {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) : ℕ :=
  if h : 128 ≤ A.Λ then
    (EntryWeakProofs.weak_epsilon_rpow_eventually_small B.hq.1 h A.σw_pos
      (c := 1 / 2048) (by norm_num)).choose
  else 0

theorem weakEntryForcingFloor_spec {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B)
    (h : 128 ≤ A.Λ) (M : ℕ) (hM : weakEntryForcingFloor A ≤ M) :
    ocEpsilon B.q A.Λ M ^ A.σw ≤ 1 / 2048 := by
  unfold weakEntryForcingFloor at hM
  rw [dite_eq_left_of_eq_true (eq_true h)] at hM
  exact (EntryWeakProofs.weak_epsilon_rpow_eventually_small B.hq.1 h A.σw_pos
    (c := 1 / 2048) (by norm_num)).choose_spec M hM

/-! ### The maxima -/

/-- The supremum, over the offsets `m ≤ m_max(R)`, of the level floor of the quiet joint plan at
the lifted request. -/
def weakEntryQuietSeed : WeakPassagePlan :=
  weakQuietJointSeed weakQuietBasePlan weakQuietBasePrices

def weakEntryQuietPlan : WeakPassagePlan :=
  weakQuietJointPlan weakQuietBasePlan weakQuietBasePrices

def weakEntryQuietLevelSup {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) (j₀ : ℕ) : ℕ :=
  (Finset.range (weakEntryMmax R + 1)).sup fun m =>
    weakEntryQuietPlan.levelFloor (weakEntryLiftRequest R m) j₀

theorem le_weakEntryQuietLevelSup {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) (j₀ m : ℕ) (hm : m ≤ weakEntryMmax R) :
    weakEntryQuietPlan.levelFloor (weakEntryLiftRequest R m) j₀ ≤ weakEntryQuietLevelSup R j₀ :=
  Finset.le_sup (f := fun m => weakEntryQuietPlan.levelFloor (weakEntryLiftRequest R m) j₀)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hm))

/-- The base floor of the entry plan, without the passage plan. -/
def weakEntryBaseFloor (B : WeakCoefficientBase) : ℕ :=
  max (max (max (weakCommonCoeffPlan.baseThreshold B) (weakWaitBaseFloor B))
      (max (weakReadoutLiftBase B) (identityLiftBase B)))
    (max (weakSlotLiftAtFloor B) (weakEntryQuietPlan.baseFloor B))

/-- The moment floor of the entry plan, without the passage plan. -/
def weakEntryMomentFloor {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) : ℕ :=
  max (weakEntryQuietPlan.momentFloor A) ⌈(A.Pw + 2 * B.q ^ A.Jw) / A.σw⌉₊

/-- The lift floor of the entry plan, without the passage plan. -/
def weakEntryLiftFloor {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) : ℕ :=
  max (max (A.Lw + 3) (weakReadoutLiftSX A)) (max (weakReadoutLiftSZ A)
    (max (identityLiftSX A) (identityLiftSZ A)))

/-- The level floor of the entry plan, without the passage plan. -/
def weakEntryLevelFloor {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) (j₀ : ℕ) : ℕ :=
  max (max (max (max (weakCommonCoeffPlan.levelThreshold (weakCoeffRequestOne R) j₀)
        (weakWaitLevelFloor A)) (max (weakPairedLevelFloor R) (weakEntryPassageCoeffFloor R)))
      (max (max (weakComparisonDriftFloor A) (weakQuietStoredFloor A))
        (max (weakReadoutLiftLevel R j₀) (identityLiftLevel R j₀))))
    (max (max (weakSlotLiftLevel A (A.Jw * A.Nw) R.sX R.sZ j₀) (weakEntryQuietLevelSup R j₀))
      (max (weakEntryForcingFloor A) 1))
end

/-! **The floors of the entry plan dominate each floor of the table**.

One lemma per component of `weakEntryBaseFloor`, `weakEntryMomentFloor`, `weakEntryLiftFloor`,
`weakEntryLevelFloor`; each is a chain of `le_max`.

The degenerate cases are included: `J_w = N_w = 1`; `m_max(R) = 0` (the quiet supremum has one
term). -/

section
open AVRegularity.Providers.WeakGen AVRegularity.Providers.WeakGen.Residual
  AVRegularity.Providers.WeakGen.Reduction AVRegularity.WeakEntryProofs.Identity
  AVRegularity.Providers.WeakGen.Comparison

section Base
variable (B : WeakCoefficientBase)

theorem weakEntryBaseFloor_common : weakCommonCoeffPlan.baseThreshold B ≤ weakEntryBaseFloor B := by
  simp [weakEntryBaseFloor, le_max_iff]
theorem weakEntryBaseFloor_wait : weakWaitBaseFloor B ≤ weakEntryBaseFloor B := by
  simp [weakEntryBaseFloor, le_max_iff]
theorem weakEntryBaseFloor_readout : weakReadoutLiftBase B ≤ weakEntryBaseFloor B := by
  simp [weakEntryBaseFloor, le_max_iff]
theorem weakEntryBaseFloor_identity : identityLiftBase B ≤ weakEntryBaseFloor B := by
  simp [weakEntryBaseFloor, le_max_iff]
theorem weakEntryBaseFloor_slotLift : weakSlotLiftAtFloor B ≤ weakEntryBaseFloor B := by
  simp [weakEntryBaseFloor, le_max_iff]
theorem weakEntryBaseFloor_quiet : weakEntryQuietPlan.baseFloor B ≤ weakEntryBaseFloor B := by
  simp [weakEntryBaseFloor, le_max_iff]
end Base

section Moment
variable {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B)

theorem weakEntryMomentFloor_quiet : weakEntryQuietPlan.momentFloor A ≤ weakEntryMomentFloor A := by
  simp [weakEntryMomentFloor, le_max_iff]

/-- Above the moment floor, `P_w + 2 q^{J_w} ≤ σ_w L`. -/
theorem weakEntryMomentFloor_exp (L : ℕ) (hL : weakEntryMomentFloor A ≤ L) :
    A.Pw + 2 * B.q ^ A.Jw ≤ A.σw * L := by
  have h1 : ⌈(A.Pw + 2 * B.q ^ A.Jw) / A.σw⌉₊ ≤ L :=
    (by simp [weakEntryMomentFloor, le_max_iff] : _ ≤ weakEntryMomentFloor A).trans hL
  have h2 : (A.Pw + 2 * B.q ^ A.Jw) / A.σw ≤ L :=
    (Nat.le_ceil _).trans (by exact_mod_cast h1)
  rw [div_le_iff₀ A.σw_pos] at h2
  linarith
end Moment

section Lift
variable {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B)

theorem weakEntryLiftFloor_Lw : A.Lw + 3 ≤ weakEntryLiftFloor A := by
  simp [weakEntryLiftFloor, le_max_iff]
theorem weakEntryLiftFloor_readoutX : weakReadoutLiftSX A ≤ weakEntryLiftFloor A := by
  simp [weakEntryLiftFloor, le_max_iff]
theorem weakEntryLiftFloor_readoutZ : weakReadoutLiftSZ A ≤ weakEntryLiftFloor A := by
  simp [weakEntryLiftFloor, le_max_iff]
theorem weakEntryLiftFloor_identityX : identityLiftSX A ≤ weakEntryLiftFloor A := by
  simp [weakEntryLiftFloor, le_max_iff]
theorem weakEntryLiftFloor_identityZ : identityLiftSZ A ≤ weakEntryLiftFloor A := by
  simp [weakEntryLiftFloor, le_max_iff]
end Lift

section Level
variable {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A) (j₀ : ℕ)

theorem weakEntryLevelFloor_common :
    weakCommonCoeffPlan.levelThreshold (weakCoeffRequestOne R) j₀ ≤ weakEntryLevelFloor R j₀ := by
  simp [weakEntryLevelFloor, le_max_iff]
theorem weakEntryLevelFloor_wait : weakWaitLevelFloor A ≤ weakEntryLevelFloor R j₀ := by
  simp [weakEntryLevelFloor, le_max_iff]
theorem weakEntryLevelFloor_paired : weakPairedLevelFloor R ≤ weakEntryLevelFloor R j₀ := by
  simp [weakEntryLevelFloor, le_max_iff]
theorem weakEntryLevelFloor_passageCoeff : weakEntryPassageCoeffFloor R ≤ weakEntryLevelFloor R j₀ := by
  simp [weakEntryLevelFloor, le_max_iff]
theorem weakEntryLevelFloor_drift : weakComparisonDriftFloor A ≤ weakEntryLevelFloor R j₀ := by
  simp [weakEntryLevelFloor, le_max_iff]
theorem weakEntryLevelFloor_stored : weakQuietStoredFloor A ≤ weakEntryLevelFloor R j₀ := by
  simp [weakEntryLevelFloor, le_max_iff]
theorem weakEntryLevelFloor_readout : weakReadoutLiftLevel R j₀ ≤ weakEntryLevelFloor R j₀ := by
  simp [weakEntryLevelFloor, le_max_iff]
theorem weakEntryLevelFloor_identity : identityLiftLevel R j₀ ≤ weakEntryLevelFloor R j₀ := by
  simp [weakEntryLevelFloor, le_max_iff]
theorem weakEntryLevelFloor_slotLift :
    weakSlotLiftLevel A (A.Jw * A.Nw) R.sX R.sZ j₀ ≤ weakEntryLevelFloor R j₀ := by
  simp [weakEntryLevelFloor, le_max_iff]
theorem weakEntryLevelFloor_quietSup :
    weakEntryQuietLevelSup R j₀ ≤ weakEntryLevelFloor R j₀ := by
  simp [weakEntryLevelFloor, le_max_iff]
theorem weakEntryLevelFloor_forcing : weakEntryForcingFloor A ≤ weakEntryLevelFloor R j₀ := by
  simp [weakEntryLevelFloor, le_max_iff]
theorem weakEntryLevelFloor_pos : 1 ≤ weakEntryLevelFloor R j₀ := by
  simp [weakEntryLevelFloor, le_max_iff]
end Level
end

/-! **The floor-only fields of the entry plan**.

`weakEntryBasePlan pp` has the radius budget `1/2048`, the dominance floors above (each raised to
the floor of the passage plan `pp`), and the constants `CK = Cread = Cid = 0`.
Every condition of `WeakEntryLanePlanOK` that is a floor or a radius bound is proved here for it,
one lemma per field. The three constants are set in `weakEntryPlan`: they are read from
statements about the plan that mention only the floors, the radius and the data (not `CK`,
`Cread`, `Cid`), so they are chosen after the base plan.

The degenerate cases are included: `J_w = N_w = 1`; `m_max(R) = 0`; `pp` with all floors `0` (the
maxima are then the entry floors). -/

section
open AVRegularity.Providers.WeakGen AVRegularity.Providers.WeakGen.Residual
  AVRegularity.Providers.WeakGen.Reduction AVRegularity.WeakEntryProofs.Identity
  AVRegularity.Providers.WeakGen.Comparison AVRegularity.WeakEntryProofs.ReadoutLinear

/-- The base plan of the entry side: radius `1/2048`, the floors, no constants yet. -/
def weakEntryBasePlan (pp : WeakPassagePlan) : WeakEntryGluePlan where
  baseFloor B := max (weakEntryBaseFloor B) (pp.baseFloor B)
  momentFloor A := max (weakEntryMomentFloor A) (pp.momentFloor A)
  radiusBudget _ := ⟨1 / 2048, by norm_num, 0, le_rfl⟩
  CK _ _ := 0
  Cread _ _ := 0
  Cid _ _ := 0
  levelFloor R _ j₀ := max (weakEntryLevelFloor R j₀) (pp.levelFloor R j₀)
  liftFloor A := max (weakEntryLiftFloor A) (pp.liftFloor A)

variable (pp : WeakPassagePlan)

theorem weakEntryBasePlan_radius {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) : (weakEntryBasePlan pp).radius R = 1 / 2048 := by
  show min 1 (min (1 / 2048 : ℝ) (1 / (8 * (0 + 1)))) = 1 / 2048
  norm_num

theorem weakEntryBasePlan_radius_le {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) : (weakEntryBasePlan pp).radius R ≤ 1 / 2048 :=
  (weakEntryBasePlan_radius pp R).le

/-- Field `common`. -/
theorem weakEntryBasePlan_common : WeakEntryCommonOK (weakEntryBasePlan pp) :=
  ⟨fun B => (weakEntryBaseFloor_common B).trans (le_max_left _ _),
   fun R _ j₀ => (weakEntryLevelFloor_common R j₀).trans (le_max_left _ _)⟩

/-- Field `paired`. -/
theorem weakEntryBasePlan_paired : WeakEntryPairedPlanOK (weakEntryBasePlan pp) :=
  ⟨weakEntryBasePlan_radius_le pp,
   fun R _ j₀ => (weakEntryLevelFloor_paired R j₀).trans (le_max_left _ _)⟩

/-- The plan condition of the passage energy. -/
theorem weakEntryBasePlan_passageEnergy : WeakEntryPassageEnergyPlanOK (weakEntryBasePlan pp) :=
  ⟨weakEntryBasePlan_paired pp, weakEntryBasePlan_radius_le pp,
   fun R _ j₀ => ⟨(weakEntryLevelFloor_passageCoeff R j₀).trans (le_max_left _ _),
     (weakEntryLevelFloor_drift R j₀).trans (le_max_left _ _),
     (weakEntryLevelFloor_stored R j₀).trans (le_max_left _ _)⟩⟩

/-- The plan condition of the quiet trace bound: the witness is the joint quiet plan of the base prices. -/
theorem weakEntryBasePlan_quiet : WeakEntryQuietTraceHighPlanOK (weakEntryBasePlan pp) := by
  obtain ⟨h1, h2, h3, h4⟩ := weak_quiet_joint_spec weakQuietBasePlan weakQuietBasePrices
    (fun _ => le_rfl) (fun _ => le_rfl)
  refine ⟨weakEntryQuietSeed, weakQuietJointPrices weakQuietBasePlan weakQuietBasePrices,
    h1, h2, h3, h4, ?_⟩
  intro B A R C m hm
  exact ⟨(weakEntryBaseFloor_quiet B).trans (le_max_left _ _),
    (weakEntryMomentFloor_quiet A).trans (le_max_left _ _),
    fun j₀ => (le_weakEntryQuietLevelSup R j₀ m hm).trans
      ((weakEntryLevelFloor_quietSup R j₀).trans (le_max_left _ _)),
    (weakEntryBasePlan_radius_le pp R).trans (le_of_eq rfl)⟩

/-- Field `linear`. -/
theorem weakEntryBasePlan_linear : WeakReadoutLinearPlanOK (weakEntryBasePlan pp) :=
  fun A => ((Nat.le_add_right _ 3).trans (weakEntryLiftFloor_Lw A)).trans (le_max_left _ _)

/-- The floors of the readout bound; the constant `Cread` is set later. -/
theorem weakEntryBasePlan_readout_floors :
    (∀ B, weakReadoutLiftBase B ≤ (weakEntryBasePlan pp).baseFloor B) ∧
    (∀ {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B),
      weakReadoutLiftSX A ≤ (weakEntryBasePlan pp).liftFloor A ∧
        weakReadoutLiftSZ A ≤ (weakEntryBasePlan pp).liftFloor A) ∧
    ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
      (C : WeakEntryAllocation R ((weakEntryBasePlan pp).radius R)) (j₀ : ℕ),
      weakReadoutLiftLevel R j₀ ≤ (weakEntryBasePlan pp).levelFloor R C j₀ :=
  ⟨fun B => (weakEntryBaseFloor_readout B).trans (le_max_left _ _),
   fun A => ⟨(weakEntryLiftFloor_readoutX A).trans (le_max_left _ _),
     (weakEntryLiftFloor_readoutZ A).trans (le_max_left _ _)⟩,
   fun R _ j₀ => (weakEntryLevelFloor_readout R j₀).trans (le_max_left _ _)⟩

/-- The plan condition of the lift from a level. -/
theorem weakEntryBasePlan_lift : IdentityLiftPlanOK (weakEntryBasePlan pp) :=
  ⟨fun B => (weakEntryBaseFloor_identity B).trans (le_max_left _ _),
   fun A => ⟨(weakEntryLiftFloor_identityX A).trans (le_max_left _ _),
     (weakEntryLiftFloor_identityZ A).trans (le_max_left _ _)⟩,
   fun R _ j₀ => (weakEntryLevelFloor_identity R j₀).trans (le_max_left _ _)⟩

theorem weakEntryBasePlan_liftFloor : IdentityLiftFloorOK (weakEntryBasePlan pp) :=
  fun A => (weakEntryLiftFloor_Lw A).trans (le_max_left _ _)

theorem weakEntryBasePlan_slotLifts : WeakEntrySlotLiftPlanOK (weakEntryBasePlan pp) :=
  ⟨fun B => (weakEntryBaseFloor_slotLift B).trans (le_max_left _ _),
   fun R _ j₀ => (weakEntryLevelFloor_slotLift R j₀).trans (le_max_left _ _)⟩

theorem weakEntryBasePlan_forcing : WeakEntryPairedForcingCostPlanOK (weakEntryBasePlan pp) := by
  intro B A R C j₀ M h128 hM
  rw [weakEntryBasePlan_radius]
  exact weakEntryForcingFloor_spec A h128 M
    ((weakEntryLevelFloor_forcing R j₀).trans ((le_max_left _ _).trans hM))

/-- The four comparisons with the passage plan, the positivity and the moment exponent. -/
theorem weakEntryBasePlan_passage :
    (∀ B, pp.baseFloor B ≤ (weakEntryBasePlan pp).baseFloor B) ∧
    (∀ {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B),
      pp.momentFloor A ≤ (weakEntryBasePlan pp).momentFloor A) ∧
    (∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
      (C : WeakEntryAllocation R ((weakEntryBasePlan pp).radius R)) (j : ℕ),
      pp.levelFloor R j ≤ (weakEntryBasePlan pp).levelFloor R C j) ∧
    (∀ {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B),
      pp.liftFloor A ≤ (weakEntryBasePlan pp).liftFloor A) ∧
    (∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
      (C : WeakEntryAllocation R ((weakEntryBasePlan pp).radius R)) (j₀ : ℕ),
      1 ≤ (weakEntryBasePlan pp).levelFloor R C j₀) ∧
    (∀ {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) (L : ℕ),
      (weakEntryBasePlan pp).momentFloor A ≤ L → A.Pw + 2 * B.q ^ A.Jw ≤ A.σw * L) :=
  ⟨fun _ => le_max_right _ _, fun _ => le_max_right _ _, fun _ _ _ => le_max_right _ _,
   fun _ => le_max_right _ _,
   fun R _ j₀ => (weakEntryLevelFloor_pos R j₀).trans (le_max_left _ _),
   fun A L hL => weakEntryMomentFloor_exp A L ((le_max_left _ _).trans hL)⟩
end
end

section
/-! **The entry plan, with its three constants**.

`CK`, `Cread`, `Cid` are set after the base plan. `CK` dominates `3 C_raw(R, C, 0)` and
`C_diff(R, C)`; these (and `C_pass`, `C_q`, `C_mom` inside them) are read through `Classical.choose`
from statements about the plan that mention only the floors, the radius and the data, so they are
equal at the base plan and at the final plan (`rfl`). `Cread` is the readout price at the radius
`1/2048`. `Cid` is `identityCidConst` at the plan with `CK` and `Cread` already set.

The degenerate cases are included: `J_w = N_w = 1`. The constants are read after the radius
budget, which does not depend on them. -/

section
open AVRegularity.Providers.WeakGen AVRegularity.Providers.WeakGen.Residual
  AVRegularity.Providers.WeakGen.Reduction AVRegularity.WeakEntryProofs.Identity
  AVRegularity.Providers.WeakGen.Comparison AVRegularity.WeakEntryProofs.ReadoutLinear
  AVRegularity.WeakEntryProofs AVRegularity.Providers.WeakGen.Readout

/-- Replace the three constants of a plan. -/
def weakEntryWithConsts (p : WeakEntryGluePlan)
    (CK Cread Cid : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
      (R : WeakPassageRequest A), WeakEntryAllocation R (p.radius R) → ℝ) : WeakEntryGluePlan :=
  { p with CK := CK, Cread := Cread, Cid := Cid }

variable (pp : WeakPassagePlan)

/-- The constant `CK`. -/
def weakEntryCK {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) (C : WeakEntryAllocation R ((weakEntryBasePlan pp).radius R)) : ℝ :=
  max (3 * weakEntryRawConst (weakEntryBasePlan pp) R C 0)
    (pdConst (weakEntryBasePlan pp) (weakEntryBasePlan_common pp) (weakEntryBasePlan_paired pp) R C)

/-- The constant `Cread`. -/
def weakEntryCread {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) (_C : WeakEntryAllocation R ((weakEntryBasePlan pp).radius R)) : ℝ :=
  3 * (weakReadoutLiftConst R *
    weakReadoutBaseConst weak_readout_base_size B.s (A.Lw + 3) ((weakEntryBasePlan pp).radius R))

/-- The plan with `CK` and `Cread` set. -/
def weakEntryPlan1 : WeakEntryGluePlan :=
  weakEntryWithConsts (weakEntryBasePlan pp) (fun R C => weakEntryCK pp R C)
    (fun R C => weakEntryCread pp R C) (fun _ _ => 0)

/-- **The entry plan** on the passage plan `pq`. -/
def weakEntryPlan (pq : WeakPassagePlan) : WeakEntryGluePlan :=
  weakEntryWithConsts (weakEntryBasePlan pq) (fun R C => weakEntryCK pq R C)
    (fun R C => weakEntryCread pq R C) (fun R C => identityCidConst (weakEntryPlan1 pq) pq R C)
end

/-! **The constants read from the plan do not depend on `CK`, `Cread`, `Cid`**.

`weakEntryPassageConst`, `weakEntryQuietConst`, `pdCmom` are `Classical.choose` of bounds
quantified over `WeakEntryData plan C`, a structure type applied to the whole plan, so they are not
definitionally equal at two plans differing in the constants. They are equal propositionally: the
bounds are logically equivalent, by copying the data (`{x with}`, no field is written), and
`Classical.choose` of equal predicates agrees. This lets `CK` dominate them at the final plan.

The three bounds do not mention `CK`, `Cread`, `Cid`; the degenerate case `m = 0` is included. -/

section
open AVRegularity.Providers.WeakGen AVRegularity.Providers.WeakGen.Reduction
  AVRegularity.WeakEntryProofs AVRegularity.WeakEntryProofs.Identity

variable (p : WeakEntryGluePlan) {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) (C : WeakEntryAllocation R (p.radius R)) (m : ℕ) (c : ℝ)
    (CK Cr Ci : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
      (R : WeakPassageRequest A), WeakEntryAllocation R (p.radius R) → ℝ)

theorem weakEntryTransfer_passageBound :
    WeakEntryPassageEnergyBound (weakEntryWithConsts p CK Cr Ci) R C m c ↔
      WeakEntryPassageEnergyBound p R C m c := by
  constructor
  · intro h x g s Uhi Whi i h1 h2 h3 t ht
    exact h {x with} {g with} {s with} Uhi Whi i h1 h2 h3 t ht
  · intro h x g s Uhi Whi i h1 h2 h3 t ht
    exact h {x with} {g with} {s with} Uhi Whi i h1 h2 h3 t ht

theorem weakEntryTransfer_quietBound :
    WeakEntryQuietTraceHighBound (weakEntryWithConsts p CK Cr Ci) R C m c ↔
      WeakEntryQuietTraceHighBound p R C m c := by
  constructor
  · intro h x g s f θ hsol r Uhi Whi hfam i h1 h2
    exact h {x with} {g with} {s with} f θ hsol {r with} Uhi Whi hfam i h1 h2
  · intro h x g s f θ hsol r Uhi Whi hfam i h1 h2
    exact h {x with} {g with} {s with} f θ hsol {r with} Uhi Whi hfam i h1 h2

open scoped Classical in
theorem weakEntryPlan_chooseDef_congr {P Q : ℝ → Prop} (h : ∀ c, P c ↔ Q c) :
    (if hh : ∃ c, P c then Classical.choose hh else 0) =
      (if hh : ∃ c, Q c then Classical.choose hh else 0) := by
  have : P = Q := funext fun c => propext (h c)
  subst this
  rfl

theorem weakEntryTransfer_passageConst :
    weakEntryPassageConst (weakEntryWithConsts p CK Cr Ci) R C m = weakEntryPassageConst p R C m :=
  weakEntryPlan_chooseDef_congr fun c => and_congr_right fun _ => weakEntryTransfer_passageBound p R C m c CK Cr Ci

theorem weakEntryTransfer_quietConst :
    weakEntryQuietConst (weakEntryWithConsts p CK Cr Ci) R C m = weakEntryQuietConst p R C m :=
  weakEntryPlan_chooseDef_congr fun c => and_congr_right fun _ => weakEntryTransfer_quietBound p R C m c CK Cr Ci

theorem weakEntryTransfer_rawConst :
    weakEntryRawConst (weakEntryWithConsts p CK Cr Ci) R C m = weakEntryRawConst p R C m := by
  unfold weakEntryRawConst
  rw [weakEntryTransfer_passageConst, weakEntryTransfer_quietConst]

theorem weakEntryTransfer_pdBound (hc : WeakEntryCommonOK p) (hok : WeakEntryPairedPlanOK p)
    (hc' : WeakEntryCommonOK (weakEntryWithConsts p CK Cr Ci))
    (hok' : WeakEntryPairedPlanOK (weakEntryWithConsts p CK Cr Ci)) :
    WeakEntryPairedForcingCostBound (weakEntryWithConsts p CK Cr Ci) hc' hok' R C c ↔
      WeakEntryPairedForcingCostBound p hc hok R C c := by
  constructor
  · intro h x g s law hm f θ hsol r Uk hreg Uhi Whi h1 h2
    exact h (x := {x with}) {g with} {s with} law hm f θ hsol {r with} Uk hreg Uhi Whi h1 h2
  · intro h x g s law hm f θ hsol r Uk hreg Uhi Whi h1 h2
    exact h (x := {x with}) {g with} {s with} law hm f θ hsol {r with} Uk hreg Uhi Whi h1 h2

theorem weakEntryTransfer_pdCmom (hc : WeakEntryCommonOK p) (hok : WeakEntryPairedPlanOK p)
    (hc' : WeakEntryCommonOK (weakEntryWithConsts p CK Cr Ci))
    (hok' : WeakEntryPairedPlanOK (weakEntryWithConsts p CK Cr Ci)) :
    pdCmom (weakEntryWithConsts p CK Cr Ci) hc' hok' R C = pdCmom p hc hok R C :=
  weakEntryPlan_chooseDef_congr fun c =>
    and_congr_right fun _ => weakEntryTransfer_pdBound p R C c CK Cr Ci hc hok hc' hok'

theorem weakEntryTransfer_pdConst (hc : WeakEntryCommonOK p) (hok : WeakEntryPairedPlanOK p)
    (hc' : WeakEntryCommonOK (weakEntryWithConsts p CK Cr Ci))
    (hok' : WeakEntryPairedPlanOK (weakEntryWithConsts p CK Cr Ci)) :
    pdConst (weakEntryWithConsts p CK Cr Ci) hc' hok' R C = pdConst p hc hok R C := by
  unfold pdConst
  rw [weakEntryTransfer_pdCmom p R C CK Cr Ci hc hok hc' hok', weakEntryTransfer_rawConst]

theorem weakEntryTransfer_cid (pq : WeakPassagePlan)
    (CK' Cr' Ci' : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
      (R : WeakPassageRequest A), WeakEntryAllocation R (p.radius R) → ℝ)
    (h1 : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
      (C : WeakEntryAllocation R (p.radius R)), CK R C = CK' R C)
    (h2 : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
      (C : WeakEntryAllocation R (p.radius R)), Cr R C = Cr' R C) :
    identityCidConst (weakEntryWithConsts p CK Cr Ci) pq R C =
      identityCidConst (weakEntryWithConsts p CK' Cr' Ci') pq R C := by
  unfold identityCidConst identityMassCoef
  rw [weakEntryTransfer_passageConst, weakEntryTransfer_quietConst,
    weakEntryTransfer_passageConst, weakEntryTransfer_quietConst]
  show _ + 4 * |Cr R C| * |CK R C| = _ + 4 * |Cr' R C| * |CK' R C|
  rw [h1, h2]
end

/-! **The entry plan meets the plan conditions of the entry side**.

One lemma per field of `WeakEntryLanePlanOK`; the assembly `weakEntryLanePlan_exists`, with no
hypothesis about any constant: `CK`, `Cread`, `Cid` dominate constants read from the plan, which
agree with those of the base plan by the transfer lemmas above (`weakEntryTransfer_cid` and the
others).

The degenerate cases are included: `J_w = N_w = 1`; the offsets used are `m = 0` and
`m = m_max(R)`. -/

section
open AVRegularity.Providers.WeakGen AVRegularity.Providers.WeakGen.Residual
  AVRegularity.Providers.WeakGen.Reduction AVRegularity.WeakEntryProofs.Identity
  AVRegularity.Providers.WeakGen.Comparison AVRegularity.WeakEntryProofs.ReadoutLinear
  AVRegularity.WeakEntryProofs AVRegularity.Providers.WeakGen.Readout

variable (pq : WeakPassagePlan)

theorem weakEntryPlan_common : WeakEntryCommonOK (weakEntryPlan pq) :=
  weakEntryBasePlan_common pq

theorem weakEntryPlan_wait : WeakScheduleWaitStatement (weakEntryPlan pq) :=
  weakScheduleWait_of_floors _ (fun B => (weakEntryBaseFloor_wait B).trans (le_max_left _ _))
    (fun R _ j₀ => (weakEntryLevelFloor_wait R j₀).trans (le_max_left _ _))

theorem weakEntryPlan_paired : WeakEntryPairedPlanOK (weakEntryPlan pq) :=
  weakEntryBasePlan_paired pq

theorem weakEntryPlan_rawEnergy : WeakEntryRawEnergyPlanOK (weakEntryPlan pq) :=
  ⟨weakEntryBasePlan_passageEnergy pq, weakEntryBasePlan_quiet pq, fun R C =>
    le_trans (le_of_eq (congrArg (3 * ·) (weakEntryTransfer_rawConst (weakEntryBasePlan pq) R C 0
      (fun R C => weakEntryCK pq R C) (fun R C => weakEntryCread pq R C)
      (fun R C => identityCidConst (weakEntryPlan1 pq) pq R C)))) (le_max_left _ _)⟩

theorem weakEntryPlan_pairedDiff : WeakEntryPairedDiffPlanOK (weakEntryPlan pq) :=
  ⟨weakEntryBasePlan_passageEnergy pq, weakEntryBasePlan_quiet pq, weakEntryBasePlan_forcing pq,
   fun hc hok {_ _} R C =>
    le_trans (le_of_eq (weakEntryTransfer_pdConst (weakEntryBasePlan pq) R C
      (fun R C => weakEntryCK pq R C) (fun R C => weakEntryCread pq R C)
      (fun R C => identityCidConst (weakEntryPlan1 pq) pq R C)
      (weakEntryBasePlan_common pq) (weakEntryBasePlan_paired pq) hc hok)) (le_max_right _ _)⟩

theorem weakEntryPlan_linear : WeakReadoutLinearPlanOK (weakEntryPlan pq) :=
  weakEntryBasePlan_linear pq

theorem weakEntryPlan_bound : WeakReadoutBoundPlanOK weak_readout_base_size (weakEntryPlan pq) :=
  ⟨(weakEntryBasePlan_readout_floors pq).1, (weakEntryBasePlan_readout_floors pq).2.1,
   fun R C j₀ => ⟨(weakEntryBasePlan_readout_floors pq).2.2 R C j₀, le_rfl⟩⟩

theorem weakEntryPlan_cid {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) (C : WeakEntryAllocation R ((weakEntryPlan pq).radius R)) :
    identityCidConst (weakEntryPlan pq) pq R C ≤ (weakEntryPlan pq).Cid R C :=
  le_of_eq (weakEntryTransfer_cid (weakEntryBasePlan pq) R C _ _ _ pq _ _ _
    (fun _ _ => rfl) (fun _ _ => rfl))

theorem weakEntryPlan_identity : WeakReadoutIdentityPlanOK (weakEntryPlan pq) pq :=
  ⟨⟨weakEntryPlan_linear pq, weakEntryPlan_bound pq, weakEntryBasePlan_lift pq,
    (weakEntryBasePlan_passage pq).1, (weakEntryBasePlan_passage pq).2.1,
    (weakEntryBasePlan_passage pq).2.2.1, (weakEntryBasePlan_passage pq).2.2.2.1,
    (weakEntryBasePlan_passage pq).2.2.2.2.1, (weakEntryBasePlan_passage pq).2.2.2.2.2,
    fun R C => weakEntryPlan_cid pq R C⟩,
   weakEntryBasePlan_liftFloor pq, weakEntryBasePlan_slotLifts pq, weakEntryPlan_common pq,
   weakEntryBasePlan_passageEnergy pq, weakEntryBasePlan_quiet pq⟩

/-- The conditions of the passage side under which the entry plan exists: none. The plan reads
`pp` only through the lower bounds `pp.floor ≤ plan.floor` (maxima) and through the numbers
`pp.energyC`, `pp.forceC`, `pp.radius` in `Cid`. -/
def WeakEntryPassageSideOK (_pp : WeakPassagePlan) : Prop := True

/-- **The entry plan exists.** -/
theorem weakEntryLanePlan_exists (pp : WeakPassagePlan) (_h : WeakEntryPassageSideOK pp) :
    ∃ plan : WeakEntryGluePlan, WeakEntryLanePlanOK plan (weakComparisonPassagePlan pp) :=
  ⟨weakEntryPlan (weakComparisonPassagePlan pp),
   { common := weakEntryPlan_common _
     wait := weakEntryPlan_wait _
     rawEnergy := weakEntryPlan_rawEnergy _
     paired := weakEntryPlan_paired _
     pairedDiff := weakEntryPlan_pairedDiff _
     linear := weakEntryPlan_linear _
     bound := weakEntryPlan_bound _
     identity := weakEntryPlan_identity _ }⟩
end
end

end AVRegularity.WeakEntryProofs.Assembly
end
