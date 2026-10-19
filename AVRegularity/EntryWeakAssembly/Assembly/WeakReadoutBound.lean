-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Proofs.WeakGen.Residual.Gluing.TransitionPassage
public import AVRegularity.Proofs.WeakGen.Residual.LiftedComparison
import AVRegularity.EntryWeakAssembly.QuietSmoothingPlan
public import AVRegularity.Finite.WeakLift.FixedCarrier
public import AVRegularity.Proofs.WeakGen.Readout.BaseSize
public import AVRegularity.EntryWeakAssembly.QuietScalarPathPrice
import AVRegularity.Applications.Global.CompactRangeMain

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.WeakEntryProofs.Assembly

/-! **Periodicity of the glued lift of the entry schedule**.

The entry stages are the stages of a weak construction on a carrier start at `(1, 400)`
(`WeakEntryData.carrier400`), so the factory of the slot lifts (`weakSlotLiftEx`) applies to
them above its two floors. `WeakEntrySlotLiftPlanOK` is these floors on an entry plan, at the order
`Lr = J_wN_w`. Under it the glued lift `Λ_i` of the schedule, with the schedule's own coefficients
`s.CcR i`, maps periodic fields to periodic fields (`weakEntry_gluedLift_periodic`). This is the
periodicity half of the lift condition of the weak identity.

The degenerate cases are included: `J_w = 1` has the single level `i = M + 1`. The plan
condition is floors only (a base floor and a level floor after the carrier start), with no
condition on the radius. -/

open AVRegularity.Providers.WeakGen.Residual Finite.WeakLift

/-- The slot-lift floors on an entry plan, at the order `Lr = J_wN_w`. -/
def WeakEntrySlotLiftPlanOK (plan : WeakEntryGluePlan) : Prop :=
  (∀ B, weakSlotLiftAtFloor B ≤ plan.baseFloor B) ∧
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (C : WeakEntryAllocation R (plan.radius R)) (j₀ : ℕ),
    weakSlotLiftLevel A (A.Jw * A.Nw) R.sX R.sZ j₀ ≤ plan.levelFloor R C j₀

/-- The slot lifts of the entry stages. -/
theorem weakEntry_slot_lifts {plan : WeakEntryGluePlan} (hplan : WeakEntrySlotLiftPlanOK plan)
    {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    {C : WeakEntryAllocation R (plan.radius R)} {x : WeakEntryData plan C}
    (g : WeakEntryStages x) {i : ℕ} (hMi : x.M < i) (hi : i ≤ x.M + A.Jw) :
    WeakPositiveGeometry (weakSlotLiftParams A (A.Jw * A.Nw) R.sX R.sZ) i (g.stage i) ∧
      Nonempty (∀ slot : OddSlot, WeakPositiveSlot (weakSlotLiftParams A (A.Jw * A.Nw) R.sX R.sZ)
        i (g.stage i) (fun v => weakMass x.D A.Nw A.Jw A.η₀ v.1) slot) := by
  have hLr : A.Jw * A.Nw ≤ A.Jw * A.Nw := le_rfl
  have hP : weakSlotLiftParams A (A.Jw * A.Nw) R.sX R.sZ =
      Classical.choose (weakSlotLiftEx A (A.Jw * A.Nw) R.sX R.sZ hLr) := by
    unfold weakSlotLiftParams; rw [dite_eq_left_of_eq_true (eq_true hLr)]
  obtain ⟨_, _, _, hrest⟩ := Classical.choose_spec (weakSlotLiftEx A (A.Jw * A.Nw) R.sX R.sZ hLr)
  rw [hP]
  have hmax : max (weakSlotLiftAtFloor B) A.Λ = A.Λ :=
    max_eq_right ((hplan.1 B).trans x.base_ge)
  have hcar : IsCarrierStart B.α B.q (max (weakSlotLiftAtFloor B) A.Λ) A.bw 1 400 x.j₀ := by
    rw [hmax]; exact x.carrier400
  have hlev : weakSlotLiftLevel A (A.Jw * A.Nw) R.sX R.sZ x.j₀ =
      Classical.choose (hrest x.j₀ hcar) := by
    unfold weakSlotLiftLevel; rw [dite_eq_left_of_eq_true (eq_true ⟨hLr, hcar⟩)]
  have hM := Classical.choose_spec (hrest x.j₀ hcar)
  refine hM x.M ?_ x.D x.alpha x.q_eq (x.base_eq.trans hmax.symm) x.profile_eq
    (by rw [hmax]; exact x.streams) (by rw [hmax]; exact x.band) x.terminal x.P x.Dm g.stage
    g.construction i hMi hi
  rw [← hlev]
  exact (hplan.2 R C x.j₀).trans x.level_ge

/-- **Periodicity of the glued lift of the entry schedule** on periodic fields. -/
theorem weakEntry_gluedLift_periodic {plan : WeakEntryGluePlan} (hplan : WeakEntrySlotLiftPlanOK plan)
    {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    {C : WeakEntryAllocation R (plan.radius R)} {x : WeakEntryData plan C}
    (g : WeakEntryStages x) (s : WeakEntrySchedule g) {i : ℕ} (hMi : x.M < i)
    (hi : i ≤ x.M + A.Jw) (t : ℝ) (a : CompIn (g.stage i).comps → Vec 2 → ℝ)
    (ha : ∀ v, AVenhance.IsZ2Periodic (a v)) (v : CompIn (g.stage i).comps) :
    AVenhance.IsZ2Periodic (weakGluedLift i A.Nw (A.Jw * A.Rw) (g.stage i) (s.CcR i) t a v) := by
  obtain ⟨hgeo, ⟨slotLifts⟩⟩ := weakEntry_slot_lifts hplan g hMi hi
  exact weakGluedLift_periodic_of_slotLifts slotLifts hgeo (s.CcR i) (s.lifts i hMi hi) t a ha v

end AVRegularity.WeakEntryProofs.Assembly
end

section
namespace AVRegularity.WeakEntryProofs.Assembly

/-! **One plan for both quiet-trace layers.** The coefficient layer (`weak_quiet_coefficient`) holds on
`weakQuietCoefficientPlan pp` for every `pp`, and the smoothing layer (`weak_quiet_smoothing_of_plan_conditions`)
holds on every plan that meets four numerical conditions. The joint plan is
`weakQuietCoefficientPlan` of a seed `pp` chosen so that the four conditions hold on it:
- the seed carries the jet reserve and the level floors of the smoothing layer (`weakQuietRowsPlan`);
- the coefficient refinement keeps the radius, the jet order and the trace constant, and its coefficient
  constant does not read the trace constant;
- so the seed's trace constant is the path polynomial at the coefficient constant.
The order of the choices is: jets, then the coefficient price, then the trace constant. All of
them precede `Dm`, the construction and the datum. -/

/-- The scalar prices of the joint plan: the explicit path prices at the radius and the depth. -/
def weakQuietJointPrices (plan : WeakPassagePlan) (prices : WeakQuietPathPrices) :
    WeakQuietPathPrices :=
  weakQuietScalarPrices (weakQuietRowsPlan plan prices) prices

/-- The seed: the smoothing reserves and floors, with the trace constant priced at the coefficient
constant that the coefficient layer will choose. -/
def weakQuietJointSeed (plan : WeakPassagePlan) (prices : WeakQuietPathPrices) : WeakPassagePlan :=
  { weakQuietRowsPlan plan prices with
    traceC := fun R => (weakQuietJointPrices plan prices).scalar R 0 +
      ∑ n ∈ Finset.range ((weakQuietJointPrices plan prices).depth R),
        (weakQuietJointPrices plan prices).scalar R (n + 1) *
          (weakQuietCoefficientPlan (weakQuietRowsPlan plan prices)).coeffC R ^ (n + 1) }

/-- The joint plan of the quiet trace. -/
def weakQuietJointPlan (plan : WeakPassagePlan) (prices : WeakQuietPathPrices) : WeakPassagePlan :=
  weakQuietCoefficientPlan (weakQuietJointSeed plan prices)

/-- The four numerical conditions of the smoothing layer on the joint plan, from a small radius and a depth
`≥ J_wR_w + 1` of the base plan. This is also the witness of the conditions in the plan condition of
the high-reserve trace. -/
theorem weak_quiet_joint_spec (plan : WeakPassagePlan) (prices : WeakQuietPathPrices)
    (hsmall : ∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A),
      plan.radius R ≤ 1 / 2048)
    (hdepth : ∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A),
      A.Jw * A.Rw + 1 ≤ prices.depth R) :
    WeakQuietRowsPlanOK (weakQuietJointPlan plan prices) (weakQuietJointPrices plan prices) ∧
    (∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A),
      0 ≤ (weakQuietJointPlan plan prices).coeffC R) ∧
    WeakQuietScalarPricesOK (weakQuietJointPlan plan prices) (weakQuietJointPrices plan prices) ∧
    WeakQuietMarginPriceStatement (weakQuietJointPlan plan prices)
      (weakQuietJointPrices plan prices) := by
  have hrows := weak_quiet_rows_plan_spec plan prices hsmall hdepth
  refine ⟨⟨fun R => hrows.depth R, fun R j₀ => ?_, fun R j₀ => ?_, fun R => hrows.small R⟩,
    fun R => ?_, fun R n _ => ?_, fun R => ?_⟩
  · exact (hrows.coeff R j₀).trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact (hrows.drift R j₀).trans ((le_max_left _ _).trans (le_max_left _ _))
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact le_of_eq rfl
  · exact le_of_eq rfl

/-- The coefficient layer on the joint plan. -/
theorem weak_quiet_joint_coefficient (plan : WeakPassagePlan) (prices : WeakQuietPathPrices) :
    WeakQuietCoefficientStatement (weakQuietJointPlan plan prices) :=
  weak_quiet_coefficient (weakQuietJointSeed plan prices)

/-- The smoothing layer on the joint plan. -/
theorem weak_quiet_joint_smoothing (plan : WeakPassagePlan) (prices : WeakQuietPathPrices)
    (hsmall : ∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A),
      plan.radius R ≤ 1 / 2048)
    (hdepth : ∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A),
      A.Jw * A.Rw + 1 ≤ prices.depth R) :
    WeakQuietSmoothingStatement (weakQuietJointPlan plan prices) :=
  have h := weak_quiet_joint_spec plan prices hsmall hdepth
  weak_quiet_smoothing_of_plan_conditions h.1 h.2.1 h.2.2.1 h.2.2.2

/-- A base plan with the radius `1/2048` and no other requirement. -/
def weakQuietBasePlan : WeakPassagePlan where
  baseFloor _ := 128
  base_ge _ := le_rfl
  momentFloor _ := 0
  radius _ := 1 / 2048
  radius_pos _ := by norm_num
  traceC _ := 0
  jetOrder _ := 0
  coeffC _ := 0
  forcingOrder _ := 0
  forceC _ := 0
  energyC _ := 0
  energyC_nonneg _ := le_rfl
  levelFloor _ _ := 0
  liftFloor _ := 0

/-- Base prices at the minimal source depth `J_wR_w + 1`. -/
def weakQuietBasePrices : WeakQuietPathPrices where
  depth {_B} {A} _ := A.Jw * A.Rw + 1
  scalar _ _ := 0
  nonneg _ _ := le_rfl

/-- The quiet trace at the carrier constants `(1, 400)`, with both layers discharged. -/
theorem weak_passage_quiet_trace_at : WeakPassageQuietTraceAt 1 400 :=
  weak_passage_quiet_trace_at_of_ingredients (weakQuietJointPlan weakQuietBasePlan weakQuietBasePrices)
    (weak_quiet_joint_coefficient _ _)
    (weak_quiet_joint_smoothing _ _ (fun _ => le_rfl) (fun _ => le_rfl))

/-- The quiet trace, with both layers discharged. -/
theorem weak_passage_quiet_trace_statement : WeakPassageQuietTraceStatement :=
  weak_passage_quiet_trace_of_ingredients (weakQuietJointPlan weakQuietBasePlan weakQuietBasePrices)
    (weak_quiet_joint_coefficient _ _)
    (weak_quiet_joint_smoothing _ _ (fun _ => le_rfl) (fun _ => le_rfl))

end AVRegularity.WeakEntryProofs.Assembly
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.WeakEntryProofs.Assembly

/-! **The readout bound at the plan level** (`WeakReadoutBoundStatement`), from the base-size
statement and the represented lift at the carrier `(1, 400)`
(`weak_lift_rep_at`).

The constants of the lift are existential in `weak_lift_rep_at`. They are fixed here once, by
choice, as definitions that do not read the plan:
* `weakReadoutLiftBase B`: the base floor `Λ₀`;
* `weakReadoutLiftSX A`, `weakReadoutLiftSZ A`: the floors of the lift orders at `L_r = J_wN_w`;
* `weakReadoutLiftConst R`: the constant `C_w` of the request (it depends on `sX`, `sZ`);
* `weakReadoutLiftLevel R j₀`: the level floor after the carrier start;
* `weakReadoutBaseConst hbase s n c`: the constant of the base-size statement.
`WeakReadoutBoundPlanOK hbase plan` says that the floors of the plan dominate these and that
`3 · C_w · C_B ≤ C_read`. `weak_readout_bound` proves the bound under it, and
`weak_entry_readout_bound` is its form with the proved base size (`weak_readout_base_size`).

The degenerate cases are included:
- A request below the floors of the lift orders: no entry datum exists for it (`x.sX_ge`), and the
  constant is `0` by convention.
- `J_w = 1`: one lift, `L_w = N_w`; the input order is `N_w + 3`.
Every constant depends on the request and the radius; `D_m` enters nowhere. -/

open AVRegularity.Providers.WeakGen.Readout

/-- The base floor of the represented lift at the carrier `(1, 400)`. -/
def weakReadoutLiftBase (B : WeakCoefficientBase) : ℕ :=
  Classical.choose (Finite.WeakLift.weak_lift_rep_at B.α B.s B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.q B.hq
    B.ζ B.hζ)

/-- The level tail of `weak_lift_rep` at the order `L_r = J_wN_w`, with the constant `Cw`, at a
carrier index and a terminal level. -/
def WeakReadoutLiftTail {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) (Λ sX sZ : ℕ)
    (Cw : ℝ) (j₀ M : ℕ) : Prop :=
  ∀ (D : OCData), D.α = B.α → D.q = B.q → D.Λ = Λ → D.ζ = B.ζ →
    IsOCStreamSeq B.α B.q Λ B.ζ D.Φ → IsOCBandChain B.α B.q Λ B.ζ M D.κ → D.term = M →
  ∀ (PW : ProvParams) (Dm : ℕ) (stage : ℕ → GenStage D ScalarH Dm A.bw j₀)
    (Gw : GenStage D ScalarH Dm A.bw j₀) (lawW : BirthLaw)
    (ιw : CompIn (stage M).comps ≃ CompIn Gw.comps)
    (CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root))
    (W : (i : ℕ) → ℝ → (CompIn (stage i).comps → Vec 2 → ℝ) → Vec 2 → ℝ),
    IsWeakConstruction D PW (⟨A.Nw, A.Rw, sX, sZ, A.η₀, M + A.Jw⟩ : WeakMenu) M A.Jw
      (D.termRW A.σw M) 0 stage →
    IsWeakEncoding A.Nw A.Jw A.η₀ lawW.rootMass lawW.rootReadout (stage M) Gw ιw →
    (∀ i, M < i → i ≤ M + A.Jw →
      IsWeakReadoutLifts i A.Nw (A.Jw * A.Rw) sX sZ (stage i) (CcR i)) →
    IsWeakReadoutChain M A.Jw A.Nw 0 A.η₀ (fun _ => A.Jw * A.Rw) stage CcR W →
  ∀ (t : ℝ) (g : Vec 2 → ∀ v : CompIn Gw.comps, ScalarH v.1.root)
    (rT : Representation (CompSpace Gw.comps)),
    IsRepresentationAt (D.eps M) (A.Jw * A.Nw + 3) rT → rT.value = compField (Gw.mass lawW) g →
  ∃ rW : Representation (CompSpace (stage (M + A.Jw)).comps),
    IsRepresentationAt (D.eps (M + A.Jw)) 3 rW ∧
    (∀ y, compReadoutCLM (fun v => weakMass D A.Nw A.Jw A.η₀ v.1) (fun _ => 1) (rW.value y) =
      W M t (fun v y' => g y' (ιw v)) y) ∧
    representedSize B.s 3 (D.eps (M + A.Jw)) rW ≤
      ENNReal.ofReal Cw * representedSize B.s (A.Jw * A.Nw + 3) (D.eps M) rT

/-- `weak_lift_rep_at` at the physical choices `A`, at the base `max Λ₀ Λ` and the order
`J_wN_w`. -/
theorem weakReadoutLift_exists {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) :
    ∃ SX SZ : ℕ, ∀ sX sZ : ℕ, SX ≤ sX → SZ ≤ sZ → ∃ Cw : ℝ, 0 ≤ Cw ∧
      ∀ j₀ : ℕ, IsCarrierStart B.α B.q (max (weakReadoutLiftBase B) A.Λ) A.bw 1 400 j₀ →
      ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
        WeakReadoutLiftTail A (max (weakReadoutLiftBase B) A.Λ) sX sZ Cw j₀ M :=
  (Classical.choose_spec (Finite.WeakLift.weak_lift_rep_at B.α B.s B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.q
    B.hq B.ζ B.hζ)).2 (max (weakReadoutLiftBase B) A.Λ) (le_max_left _ _) A.bw A.bw_pos
    A.bw_small A.Jw A.Nw A.Rw A.η₀ A.σw A.Jw_pos A.Nw_pos A.η₀_pos A.η₀_small A.σw_pos
    A.σw_small (A.Jw * A.Nw) le_rfl

/-- The floor of the slow lift order of the represented lift. -/
def weakReadoutLiftSX {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) : ℕ :=
  (weakReadoutLift_exists A).choose

/-- The floor of the fast lift order of the represented lift. -/
def weakReadoutLiftSZ {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) : ℕ :=
  (weakReadoutLift_exists A).choose_spec.choose

theorem weakReadoutLift_spec {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B)
    (sX sZ : ℕ) (hX : weakReadoutLiftSX A ≤ sX) (hZ : weakReadoutLiftSZ A ≤ sZ) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧
      ∀ j₀ : ℕ, IsCarrierStart B.α B.q (max (weakReadoutLiftBase B) A.Λ) A.bw 1 400 j₀ →
      ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
        WeakReadoutLiftTail A (max (weakReadoutLiftBase B) A.Λ) sX sZ Cw j₀ M :=
  (weakReadoutLift_exists A).choose_spec.choose_spec sX sZ hX hZ

open scoped Classical in
/-- The constant `C_w` of the represented lift at a request (`0` below the floors). -/
def weakReadoutLiftConst {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) : ℝ :=
  if h : weakReadoutLiftSX A ≤ R.sX ∧ weakReadoutLiftSZ A ≤ R.sZ then
    (weakReadoutLift_spec A R.sX R.sZ h.1 h.2).choose else 0

open scoped Classical in
/-- The level floor of the represented lift at a request and a carrier index. -/
def weakReadoutLiftLevel {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) (j₀ : ℕ) : ℕ :=
  if h : (weakReadoutLiftSX A ≤ R.sX ∧ weakReadoutLiftSZ A ≤ R.sZ) ∧
      IsCarrierStart B.α B.q (max (weakReadoutLiftBase B) A.Λ) A.bw 1 400 j₀ then
    ((weakReadoutLift_spec A R.sX R.sZ h.1.1 h.1.2).choose_spec.2 j₀ h.2).choose else 0

theorem weakReadoutLiftConst_nonneg {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) : 0 ≤ weakReadoutLiftConst R := by
  unfold weakReadoutLiftConst
  split_ifs with h
  · exact (weakReadoutLift_spec A R.sX R.sZ h.1 h.2).choose_spec.1
  · exact le_rfl

/-- The level tail of the lift at the chosen constant, above the chosen floors. -/
theorem weakReadoutLift_tail {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) (hX : weakReadoutLiftSX A ≤ R.sX)
    (hZ : weakReadoutLiftSZ A ≤ R.sZ) (j₀ : ℕ)
    (hcar : IsCarrierStart B.α B.q (max (weakReadoutLiftBase B) A.Λ) A.bw 1 400 j₀) (M : ℕ)
    (hM : weakReadoutLiftLevel R j₀ ≤ M) :
    WeakReadoutLiftTail A (max (weakReadoutLiftBase B) A.Λ) R.sX R.sZ (weakReadoutLiftConst R)
      j₀ M := by
  have h1 : weakReadoutLiftSX A ≤ R.sX ∧ weakReadoutLiftSZ A ≤ R.sZ := ⟨hX, hZ⟩
  have hc : weakReadoutLiftConst R = (weakReadoutLift_spec A R.sX R.sZ h1.1 h1.2).choose :=
    dite_eq_left h1
  have hl : weakReadoutLiftLevel R j₀ =
      ((weakReadoutLift_spec A R.sX R.sZ h1.1 h1.2).choose_spec.2 j₀ hcar).choose :=
    dite_eq_left ⟨h1, hcar⟩
  rw [hc]
  exact ((weakReadoutLift_spec A R.sX R.sZ h1.1 h1.2).choose_spec.2 j₀ hcar).choose_spec M
    (hl ▸ hM)

open scoped Classical in
/-- The constant of the base-size statement at `(s, n, c)` (`0` outside `0 < c ≤ 1`). -/
def weakReadoutBaseConst (hbase : WeakReadoutBaseSizeStatement) (s : ℝ) (n : ℕ) (c : ℝ) : ℝ :=
  if h : 0 < c ∧ c ≤ 1 then (hbase s n c h.1 h.2).choose else 0

/-- **The plan condition of the readout bound.** Floors and one constant: the base floor, the
floors of the lift orders and the level floor of the represented lift, and
`3 · C_w · C_B ≤ C_read`. -/
def WeakReadoutBoundPlanOK (hbase : WeakReadoutBaseSizeStatement) (plan : WeakEntryGluePlan) :
    Prop :=
  (∀ B, weakReadoutLiftBase B ≤ plan.baseFloor B) ∧
  (∀ {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B),
    weakReadoutLiftSX A ≤ plan.liftFloor A ∧ weakReadoutLiftSZ A ≤ plan.liftFloor A) ∧
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (C : WeakEntryAllocation R (plan.radius R)) (j₀ : ℕ),
    weakReadoutLiftLevel R j₀ ≤ plan.levelFloor R C j₀ ∧
    3 * (weakReadoutLiftConst R *
      weakReadoutBaseConst hbase B.s (A.Lw + 3) (plan.radius R)) ≤ plan.Cread R C

/-- **The readout bound** (`WeakReadoutBoundStatement`), from the base-size statement, under the
plan condition. -/
theorem weak_readout_bound (hbase : WeakReadoutBaseSizeStatement) (plan : WeakEntryGluePlan)
    (hok : WeakReadoutBoundPlanOK hbase plan) : WeakReadoutBoundStatement plan := by
  intro B A R C x g s law hm hr t z az haz
  obtain ⟨hbaseF, hliftF, hreq⟩ := hok
  obtain ⟨hlev, hC⟩ := hreq R C x.j₀
  have hmax : max (weakReadoutLiftBase B) A.Λ = A.Λ :=
    max_eq_right ((hbaseF B).trans x.base_ge)
  have htail := weakReadoutLift_tail R ((hliftF A).1.trans x.sX_ge) ((hliftF A).2.trans x.sZ_ge)
    x.j₀ (by rw [hmax]; exact x.carrier400) x.M (hlev.trans x.level_ge)
  rw [hmax] at htail
  have hliftAt : WeakEntryLiftRepAt s law (weakReadoutLiftConst R) := by
    intro t' a rT hrT hval
    have hrT' : IsRepresentationAt (x.D.eps x.M) (A.Jw * A.Nw + 3) rT := by
      rw [← x.readout_order]
      exact hrT
    have henc : IsWeakEncoding A.Nw A.Jw A.η₀ law.rootMass law.rootReadout (g.stage x.M) g.Gw
        g.relabel := by
      rw [hm, hr]
      exact g.encoding
    obtain ⟨rW, h1, h2, h3⟩ := htail x.D x.alpha x.q_eq x.base_eq x.profile_eq x.streams x.band
      x.terminal x.P x.Dm g.stage g.Gw law g.relabel s.CcR s.W g.construction henc s.lifts
      s.chain t' a rT hrT' hval
    refine ⟨rW, h1, h2, ?_⟩
    rw [x.readout_order]
    exact h3
  have hrad := weak_entry_radius_spec (plan.radiusBudget R)
  have hCBdef : weakReadoutBaseConst hbase B.s (A.Lw + 3) (plan.radius R) =
      (hbase B.s (A.Lw + 3) (plan.radius R) hrad.1 hrad.2.1).choose :=
    dite_eq_left ⟨hrad.1, hrad.2.1⟩
  obtain ⟨hCB, hsize⟩ := (hbase B.s (A.Lw + 3) (plan.radius R) hrad.1 hrad.2.1).choose_spec
  rw [← hCBdef] at hCB hsize
  have hb := weak_readout_bound_of_lift s law hCB (weakReadoutLiftConst_nonneg R)
    (fun e he he1 z' az' haz' => hsize (g.Gw.mass law) (weakPaired_mass_pos g law hm) e he he1
      z' az' haz') hliftAt t z az haz
  refine Applications.csNormLe_mono hb ?_
  have hΛ1 : 1 ≤ x.D.Λ := by
    rw [x.base_eq]
    exact (by norm_num : 1 ≤ 128).trans x.base128
  have hp : 0 ≤ x.D.eps (x.M + A.Jw) ^ (-(1 + B.s)) :=
    Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ1).le _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC hp) (Real.sqrt_nonneg _)

/-- **The readout bound** (`WeakReadoutBoundStatement`; Lemma 14.13(b) of the paper) with every
analytic input proved: the base size from `sobolevProfile`, the represented lift from
`weak_lift_rep_at`. The plan condition has floors and the constant `3 · C_w · C_B ≤ C_read`. -/
theorem weak_entry_readout_bound (plan : WeakEntryGluePlan)
    (hok : WeakReadoutBoundPlanOK weak_readout_base_size plan) :
    WeakReadoutBoundStatement plan :=
  weak_readout_bound weak_readout_base_size plan hok

end AVRegularity.WeakEntryProofs.Assembly
end
