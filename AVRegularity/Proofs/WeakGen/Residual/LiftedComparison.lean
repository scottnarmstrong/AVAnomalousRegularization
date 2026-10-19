-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.WeakGen.Residual.ForcingCostOfMass
public import AVRegularity.Proofs.WeakGen.Assembly.WeakCommonCase
import AVRegularity.CycleComparison.LiftSetting.Main
public import AVRegularity.Finite.WeakPositive.NativeFacts
import AVRegularity.Proofs.WeakGen.Residual.Equation.IncomingReg
public import AVRegularity.Proofs.WeakGen.Residual.Equation.IncomingPassage
import AVRegularity.Proofs.QuietAtlas.SummedTransition

section
/-! **Fast independence of every passage stage on the trimmed quiet times of its level**
(native quietness). The stage `i`, `M ≤ i ≤ M + J`, of a passage instance
whose plan has the common floors is a stage of a case of the common plan. Its slot transversality
is `weakGen_stage_slot_laws` at the level `i`, and the quiet matching of the transfer stage
(`quietMatching_of_allTransfer`, with the presentation of `weakNativeQuietStagePresentation`) gives
fast independence on the trimmed quiet times of the level `i`. The finest stage has no identity. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev AVRegularity.WeakEntryProofs.Assembly
  AVRegularity.Providers.QuietAtlas

namespace AVRegularity.Providers.WeakGen.Residual

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- **Every flux of a passage stage is fast independent on the trimmed quiet times of its level
inside the pulse window of its piece** (the output times of the natural piece). -/
theorem weakNativeQuietFastIndependent (hplan : WeakPassageCommonOK plan)
    (c : WeakPassageInstance plan R) {i : ℕ} (hMi : c.M ≤ i) (hiJ : i ≤ c.M + A.Jw)
    (p : OddSlot) (ctx : StageCtx c.D A.bw c.j₀ (c.stage i).level p)
    (v u : CompIn (c.stage i).comps) (γ : (c.stage i).fam.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) :
    IsFastIndependentOn (ocTrimmedQuietTimes c.D.α c.D.q c.D.Λ c.D.ζ i ∩
      ocPulseWindow c.D.α c.D.q c.D.Λ i p.1) ((c.stage i).fam.flux p ctx v u γ d I) := by
  have hbase : weakCommonCoeffPlan.baseThreshold B ≤ A.Λ := (hplan.1 B).trans c.base_ge
  have hlev : weakCommonCoeffPlan.levelThreshold (weakCoeffRequestOne R) c.j₀ ≤ c.M :=
    (hplan.2 R c.j₀).trans c.level_ge
  let cs := weakCommonCase R hbase c.j₀ c.carrier c.M hlev c.D c.alpha c.q_eq c.base_eq
    c.profile_eq c.streams c.band c.terminal c.Dm c.order_ge c.P c.stage c.construction
  have hgate := weakCommonPlan_complexContext weakBasePlan (weakCertConst weakBasePlan) weakBasePlan_complexContext
  have hΥ : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
      (R : WeakCoefficientRequest A),
      1 ≤ (weakCommonCoeffPlan.constants R).Υ :=
    fun R => le_trans (by norm_num) ((le_max_left _ _).trans (hgate.1 R).2)
  have hT : (c.stage i).IsSlotTransverse :=
    weakGen_stage_slot_laws weakCommonCoeffPlan hΥ weakBasePlan_gen cs i hMi hiJ
  have h128 : 128 ≤ A.Λ := (weakCommonCoeffPlan.baseThreshold_ge B).trans hbase
  have hΛ : 1 ≤ c.D.Λ := by rw [c.base_eq]; omega
  have hζ : IsFastProfile c.D.ζ := by rw [c.profile_eq]; exact B.hζ
  have hκb : IsOCBandChain c.D.α c.D.q c.D.Λ c.D.ζ c.D.term c.D.κ := by
    rw [c.alpha, c.q_eq, c.base_eq, c.profile_eq, c.terminal]; exact c.band
  have hb := A.bw_pos
  have hcarrier : IsCarrierStart c.D.α c.D.q c.D.Λ A.bw 1 400 c.j₀ := by
    rw [c.alpha, c.q_eq, c.base_eq]; exact c.carrier
  have hstart := GenSem.startBound_of_carrierStart hΛ (le_refl (1 : ℝ)) (by norm_num) hcarrier
  have hcell : ∀ m, 0 < c.D.cellScaleSq m :=
    fun m => EntryWeakProofs.weakData_cellScaleSq_pos c.D hΛ hζ hκb m
  have hJ : 1 ≤ A.Jw := A.Jw_pos
  have hlvl : c.j₀ + 2 ≤ c.M := (hgate.2 (weakCoeffRequestOne R) c.j₀).trans hlev
  have hlv := EntryWeakProofs.weakConstruction_level _ _ _ _ _ _ _ c.construction i hMi hiJ
  by_cases hi : i = c.M + A.Jw
  · subst hi
    exact ((c.construction.2.1).2.2.1 v u).elim γ
  · have hiJ' : i < c.M + A.Jw := by omega
    obtain ⟨Q, hall, hF, hnat⟩ :=
      Providers.WeakGen.weakNativeQuietStagePresentation hΛ hζ hb hstart hcell c.construction
        hMi hiJ'
    have hS := isHistoryQuiet_ocTrimmedQuiet hΛ (le_refl (1 : ℝ)) hcarrier (c.M + A.Jw)
      (c.stage i).level (by omega)
    have hqm := (quietMatching_of_allTransfer hb hΛ hζ (c.stage i) Q hall (c.M + A.Jw)
      (ocTrimmedQuiet c.D (c.stage i).level) Set.univ (by omega) (by omega) 1 400
      (le_refl (1 : ℝ)) hcarrier hnat hS hF hT).2.2
    intro t ht X z z'
    refine hqm p ctx v u γ d I t ⟨⟨?_, trivial⟩, ?_⟩ X z z'
    · change t ∈ ocTrimmedQuietTimes c.D.α c.D.q c.D.Λ c.D.ζ (c.stage i).level
      rw [hlv]
      exact ht.1
    · rw [(hnat.1 p).2.1, hlv]
      exact ht.2

end AVRegularity.Providers.WeakGen.Residual
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.WeakEntryProofs.Assembly
namespace AVRegularity.Providers.WeakGen.Residual

/-! **(ii-q) The native slot data of a passage stage is quiet on trimmed quiet times**.
`weakSlotNativeQuiet` proves `WeakSlotNativeQuietStatement plan` for every plan whose floors
dominate the common plan's (`WeakPassageCommonOK`).
* Drift: the native drift of the slot `k` at the cell time `t` is `(ℓ²/e) p_k(ℓ² t) 𝐮_{i,k}(e z)`,
  and the pulse `p_k` vanishes at the quiet time `ℓ² t` (`ocPulse_eq_zero_of_mem_ocQuietTimes`).
* Edges: a member of the native lift edges is the flux of an identity at the physical time
  `ℓ² t` (`mem_liftEdges_fiber`); `ℓ² t` is a trimmed quiet time in the slot window, where the flux
  is fast independent (`weakNativeQuietFastIndependent`). -/

/-- The native cell drift vanishes at the cell times whose physical time is a quiet time. -/
theorem weakNativeQuietDrift {D : OCData} (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    {i : ℕ} (hk : 0 < D.kap i) {k : ℤ} (hk' : Odd k) {t : ℝ}
    (ht : D.cellScaleSq i * t ∈ ocQuietTimes D.α D.q D.Λ D.ζ i) (z : Vec 2) :
    ocPulseCellDrift D.α D.q D.Λ D.ζ i (D.kap i) k t z = 0 := by
  have hell : ocEll D.q D.Λ i (D.kap i) ^ 2 = D.cellScaleSq i := by
    unfold ocEll OCData.cellScaleSq
    rw [div_pow, Real.sq_sqrt hk.le]; rfl
  unfold ocPulseCellDrift
  rw [hell, QuietAtlas.ocPulse_eq_zero_of_mem_ocQuietTimes hΛ hζ ht hk']
  simp

/-- A cell time of the slot window has its physical time in the pulse window of the slot. -/
theorem weakNativeQuietMemWindow {D : OCData} {i : ℕ} (hcs : 0 < D.cellScaleSq i) {k : ℤ}
    {t : ℝ} (ht : t ∈ Set.Icc (Finite.WeakLift.weakSlotLeft D i k)
      (Finite.WeakLift.weakSlotRight D i k)) :
    D.cellScaleSq i * t ∈ ocPulseWindow D.α D.q D.Λ i k := by
  obtain ⟨h1, h2⟩ := ht
  unfold Finite.WeakLift.weakSlotLeft OCData.slotStart at h1
  unfold Finite.WeakLift.weakSlotRight at h2
  constructor
  · have := mul_le_mul_of_nonneg_left h1 hcs.le
    rwa [mul_div_cancel₀ _ hcs.ne'] at this
  · have := mul_le_mul_of_nonneg_left h2 hcs.le
    rwa [mul_div_cancel₀ _ hcs.ne'] at this

/-- **(ii-q) The native lift data of the stage's fibre at an odd slot is quiet on the cell times of
the slot window whose physical times are trimmed quiet times of the level.** The plan condition
is the common floors of the passage plan. -/
theorem weakSlotNativeQuiet {plan : WeakPassagePlan} (hplan : WeakPassageCommonOK plan) :
    WeakSlotNativeQuietStatement plan := by
  intro B A R c i hMi hiJ slot S hSub htrim
  have hbase : weakCommonCoeffPlan.baseThreshold B ≤ A.Λ := (hplan.1 B).trans c.base_ge
  have h128 : 128 ≤ A.Λ := (weakCommonCoeffPlan.baseThreshold_ge B).trans hbase
  have hΛ : 1 ≤ c.D.Λ := by rw [c.base_eq]; omega
  have hζ : IsFastProfile c.D.ζ := by rw [c.profile_eq]; exact B.hζ
  have hκb : IsOCBandChain c.D.α c.D.q c.D.Λ c.D.ζ c.D.term c.D.κ := by
    rw [c.alpha, c.q_eq, c.base_eq, c.profile_eq, c.terminal]; exact c.band
  have hkap : 0 < c.D.kap i := EntryWeakProofs.weakData_kap_pos c.D hΛ hζ hκb i
  have hcs : 0 < c.D.cellScaleSq i := EntryWeakProofs.weakData_cellScaleSq_pos c.D hΛ hζ hκb i
  refine ⟨fun t ht z => ?_, fun v u d γ hγ α t ht X z z' => ?_⟩
  · change Real.sqrt (c.D.kap i / c.D.kap (i - 1)) •
      ocPulseCellDrift c.D.α c.D.q c.D.Λ c.D.ζ i (c.D.kap i) slot.1 t z = 0
    rw [weakNativeQuietDrift hΛ hζ hkap slot.2
      (QuietAtlas.ocTrimmedQuietTimes_subset hΛ c.D.ζ i (htrim t ht)) z, smul_zero]
  · have hγ' : γ ∈ liftEdges (c.D.cellScaleSq i) (c.D.eps (i - 1) / c.D.eps (i - 1))
        ((c.stage i).fam.fiber slot ((c.stage i).actual slot)) v u d := hγ
    obtain ⟨γ₀, -, -, hc⟩ := CycleComparison.LiftSetting.mem_liftEdges_fiber hγ'
    rw [hc]
    exact weakNativeQuietFastIndependent hplan c hMi.le hiJ slot _ v u γ₀ d.1 α
      (c.D.cellScaleSq i * t) ⟨htrim t ht, weakNativeQuietMemWindow hcs (hSub ht)⟩ _ z z'

end AVRegularity.Providers.WeakGen.Residual
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.Providers.WeakGen.Residual

/-! **(ii)′ The slot lifts at the fixed carrier** from `weak_plateau_parent_setting_at`, and
**their quietness** (`WeakSlotLiftQuietStatement`) from the slot-lift fields `edge_fast`,
`drift_eq` and the native quietness `weakSlotNativeQuiet`.

The plan condition of (ii)′ is the floor `weakSlotLiftAtFloor B ≤ plan.baseFloor B` (the `Λ₀` of
the At-form). Quietness needs in addition `WeakPassageCommonOK plan`. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly Finite.WeakLift

/-- The base floor `Λ₀(B)` of the fixed-carrier weak parent factory. -/
def weakSlotLiftAtFloor (B : WeakCoefficientBase) : ℕ :=
  Classical.choose (weak_plateau_parent_setting_at B.α B.s B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.q B.hq
    B.ζ B.hζ)
end

/-! **The slot lifts with a plan-free choice of parameters and level floor.** The slot-lift
parameters and the level floor are chosen once from `weak_plateau_parent_setting_at`, with no plan
in their arguments; the plan condition `WeakSlotLiftPlanOK` is floors only. The slot lifts at the
fixed carrier are then a corollary (`weakSlotLiftAt_planOK`). -/

section
open WeakEntryProofs WeakEntryProofs.Assembly Finite.WeakLift

/-- The factory read at `Λ = max Λ₀ A.Λ`, for `J_wN_w ≤ Lr`. -/
theorem weakSlotLiftEx {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) (Lr sX sZ : ℕ)
    (h : A.Jw * A.Nw ≤ Lr) :
    ∃ P : WeakPositiveParameters A.Nw (A.Jw * A.Rw) (Lr + 3),
      P.capMax = max 2 (1 + A.Jw * A.Nw) ∧ P.slowOrder = Lr + 3 + (A.Nw + P.capMax) ∧
      P.fastOrder = Lr + 3 ∧
      ∀ j₀ : ℕ, IsCarrierStart B.α B.q (max (weakSlotLiftAtFloor B) A.Λ) A.bw 1 400 j₀ →
        ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
        ∀ (D : OCData), D.α = B.α → D.q = B.q → D.Λ = max (weakSlotLiftAtFloor B) A.Λ →
          D.ζ = B.ζ → IsOCStreamSeq B.α B.q (max (weakSlotLiftAtFloor B) A.Λ) B.ζ D.Φ →
          IsOCBandChain B.α B.q (max (weakSlotLiftAtFloor B) A.Λ) B.ζ M D.κ → D.term = M →
        ∀ (PW : ProvParams) (Dm : ℕ) (stage : ℕ → GenStage D ScalarH Dm A.bw j₀),
          IsWeakConstruction D PW (⟨A.Nw, A.Rw, sX, sZ, A.η₀, M + A.Jw⟩ : WeakMenu)
            M A.Jw (D.termRW A.σw M) 0 stage →
        ∀ i, M < i → i ≤ M + A.Jw →
          WeakPositiveGeometry P i (stage i) ∧
          Nonempty (∀ slot : OddSlot, WeakPositiveSlot P i (stage i)
            (fun v => weakMass D A.Nw A.Jw A.η₀ v.1) slot) := by
  obtain ⟨_, hfac⟩ := Classical.choose_spec
    (weak_plateau_parent_setting_at B.α B.s B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.q B.hq B.ζ B.hζ)
  exact hfac (max (weakSlotLiftAtFloor B) A.Λ) (le_max_left _ _)
    A.bw A.bw_pos A.bw_small A.Jw A.Nw A.Rw A.η₀ A.σw A.Jw_pos A.Nw_pos A.η₀_pos A.η₀_small
    A.σw_pos A.σw_small Lr h sX sZ

/-- A default inhabitant, used when `Lr < J_wN_w`. -/
def weakSlotLiftDefault (N H U : ℕ) : WeakPositiveParameters N H U where
  capMax := 2
  cap_ge := le_rfl
  slowOrder := U + (N + 2)
  fastOrder := U
  slow_reserve := by omega
  fast_reserve := le_rfl
  CG := fun _ => 0
  Cw := fun _ => 0
  Cj := fun _ _ => 0
  S := 0
  S_nonneg := le_rfl
  chartC := 1
  chartC_ge := le_rfl

open scoped Classical in
/-- The slot-lift parameters of the menu at the order `Lr` and the lift orders. -/
def weakSlotLiftParams {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B)
    (Lr sX sZ : ℕ) : WeakPositiveParameters A.Nw (A.Jw * A.Rw) (Lr + 3) :=
  if h : A.Jw * A.Nw ≤ Lr then Classical.choose (weakSlotLiftEx A Lr sX sZ h)
  else weakSlotLiftDefault _ _ _

open scoped Classical in
/-- The level floor of the slot lifts, after the carrier start. -/
def weakSlotLiftLevel {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B)
    (Lr sX sZ j₀ : ℕ) : ℕ :=
  if h : A.Jw * A.Nw ≤ Lr ∧
      IsCarrierStart B.α B.q (max (weakSlotLiftAtFloor B) A.Λ) A.bw 1 400 j₀ then
    Classical.choose ((Classical.choose_spec (weakSlotLiftEx A Lr sX sZ h.1)).2.2.2 j₀ h.2)
  else 0

/-- The plan condition of the slot lifts at the consumer's order `Lr`. Floors only. -/
def WeakSlotLiftPlanOK (plan : WeakPassagePlan)
    (Lr : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B},
      WeakPassageRequest A → ℕ) : Prop :=
  (∀ B, weakSlotLiftAtFloor B ≤ plan.baseFloor B) ∧
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A) (j₀ : ℕ),
    weakSlotLiftLevel A (Lr R) R.sX R.sZ j₀ ≤ plan.levelFloor R j₀

/-- **(ii)′ with plan-free parameters and level floor.** -/
theorem weakSlotLiftAt_planOK {plan : WeakPassagePlan}
    {Lr : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B},
      WeakPassageRequest A → ℕ}
    (hplan : WeakSlotLiftPlanOK plan Lr) {B : WeakCoefficientBase}
    (A : WeakCoefficientPhysical B) (R : WeakPassageRequest A) (hLr : A.Jw * A.Nw ≤ Lr R) :
    (weakSlotLiftParams A (Lr R) R.sX R.sZ).capMax = weakSlotCap A ∧
    (weakSlotLiftParams A (Lr R) R.sX R.sZ).slowOrder = Lr R + 3 + (A.Nw + weakSlotCap A) ∧
    (weakSlotLiftParams A (Lr R) R.sX R.sZ).fastOrder = Lr R + 3 ∧
    ∀ c : WeakPassageInstance plan R, ∀ i, c.M < i → i ≤ c.M + A.Jw →
      WeakPositiveGeometry (weakSlotLiftParams A (Lr R) R.sX R.sZ) i (c.stage i) ∧
      Nonempty (∀ slot : OddSlot, WeakPositiveSlot (weakSlotLiftParams A (Lr R) R.sX R.sZ) i
        (c.stage i) (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1) slot) := by
  have hP : weakSlotLiftParams A (Lr R) R.sX R.sZ =
      Classical.choose (weakSlotLiftEx A (Lr R) R.sX R.sZ hLr) := by
    unfold weakSlotLiftParams; rw [dite_eq_left_of_eq_true (eq_true hLr)]
  obtain ⟨h1, h2, h3, hrest⟩ := Classical.choose_spec (weakSlotLiftEx A (Lr R) R.sX R.sZ hLr)
  rw [hP]
  refine ⟨h1, by rw [h2, h1]; rfl, h3, fun c i hi hiJ => ?_⟩
  have hmax : max (weakSlotLiftAtFloor B) A.Λ = A.Λ :=
    max_eq_right ((hplan.1 B).trans c.base_ge)
  have hcar : IsCarrierStart B.α B.q (max (weakSlotLiftAtFloor B) A.Λ) A.bw 1 400 c.j₀ := by
    rw [hmax]; exact c.carrier
  have hlev : weakSlotLiftLevel A (Lr R) R.sX R.sZ c.j₀ =
      Classical.choose (hrest c.j₀ hcar) := by
    unfold weakSlotLiftLevel; rw [dite_eq_left_of_eq_true (eq_true ⟨hLr, hcar⟩)]
  have hM := Classical.choose_spec (hrest c.j₀ hcar)
  refine hM c.M ?_ c.D c.alpha c.q_eq (c.base_eq.trans hmax.symm) c.profile_eq
    (by rw [hmax]; exact c.streams) (by rw [hmax]; exact c.band) c.terminal c.P c.Dm c.stage
    c.construction i hi hiJ
  rw [← hlev]
  exact (hplan.2 R c.j₀).trans c.level_ge
end

end AVRegularity.Providers.WeakGen.Residual
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Residual

/-! **The lifted comparison of a weak passage, and the comparison residual from it**.

`WeakLiftedComparisonStatement plan`: for every comparison input of a passage, the glued lift
`Λ_i g` of the coarse readout `g = 𝓡_iŪ` is the value of a solution of the capped kernel system of
the stage (`WeakErrSol`) with the initial value `U(t_i)` and the forcing `−(F, g)`, for
some time-measurable `(F, g)` at the forcing order whose cost is at most
`forceC · ε_M^{P_w + 2q^{J_w} + 1} · Φ`. The presentation is existential: it is the constructed
residual of the reconstruction window (tails, partition terms, lifted frontier flux), not a
presentation of an explicit classical source. This is the one analytic statement of this part:
the conclusion of `ReconPhysicalLiftStatement` at a weak passage.

`weakComparisonResidual_of_lifted`: the comparison residual (`WeakComparisonResidualStatement`) from it. The error is
`h.e = trunc U − Λ_i g` (`h.identity`), the incoming family solves the system with zero forcing
(`weakIncomingReg`), and the system is linear on the window (`regSolutionCombine`).

The lifted comparison from the physical lift on the weak
window is obtained from the coupled solution at reserves to the capped kernel system, the residual
`(Rres, qres)` to `(F, g) = −(Rres, qres)` at the forcing order, the bounds in `massNormSq` to the
forcing cost, and the price `C · bill ≤ forceC · ε_M^{P_w + 2q^{J_w} + 1}`.

The degenerate cases are included: `Φ = 0` forces `F = g = 0` up to null sets and the lift solves
the homogeneous system; at the root level the stage has no edge and `YΛ` is vacuous; the statement
does not read `D_m`. -/

open WeakEntryProofs WeakEntryProofs.Assembly

/-- **The lifted comparison of a weak passage**: the glued lift of the coarse readout solves the
capped system of the stage with a forcing `−(F, g)` of small cost. -/
def WeakLiftedComparisonStatement (plan : WeakPassagePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A},
    A.Pw + 2 * B.q ^ A.Jw + 1 + 2 < A.Nw * (B.q - 1) →
    A.Pw + 2 * B.q ^ A.Jw + 1 + B.q ^ A.Jw + 1 < 2 * weakAStar B.α B.q * (A.Rw + 1) →
  ∀ (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ),
    c.M < i → i ≤ c.M + A.Jw → ∀ h : WeakComparisonInput r i,
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
        ENNReal.ofReal (plan.forceC R * c.D.eps c.M ^ (A.Pw + 2 * B.q ^ A.Jw + 1) * h.Φ)

/-- **The weak residual from the lifted comparison.** -/
theorem weakComparisonResidual_of_lifted (plan : WeakPassagePlan)
    (hL : WeakLiftedComparisonStatement plan) : WeakComparisonResidualStatement plan := by
  intro B A R hN hR c r i hi hit h
  obtain ⟨F, g, uΛ, wΛ, YΛ, hFm, hgm, hjet, hwtr, hΛsol, hcost⟩ := hL hN hR c r i hi hit h
  obtain ⟨wU, YU, hUsol⟩ := weakIncomingReg plan c r i hi hit
  have key := weakErrSol_of_parts c r i regSolutionCombine (weakRun_tq_le_window r hi hit) F g
    (weakIncomingInit r i) (weakIncomingVal r i) uΛ h.e wU wΛ h.ew YU YΛ
    (fun v t x => weakGluedLift i A.Nw (A.Jw * A.Rw) (c.stage i) (h.CcR i) t
      (weakReadoutStep i A.η₀ (c.stage i) (c.stage (i - 1)) (h.aU t)) v x)
    hUsol hΛsol h.identity hjet hwtr h.truncation
  exact ⟨F, g, fun v u γ t => YU v u γ t - YΛ v u γ t, hFm, hgm,
    weakErrSol_to_body c r i F g h.e h.ew _ key, hcost⟩

end AVRegularity.Providers.WeakGen.Residual
end
end
