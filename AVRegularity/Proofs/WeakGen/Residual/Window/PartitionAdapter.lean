-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.WeakGen.Residual.Window.SettingLiftsStep
public import AVRegularity.Proofs.WeakGen.Residual.CoarseDefect.FluxJets
import AVRegularity.Proofs.CascadeInvariants.Scales
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
import AVRegularity.Proofs.WeakGen.Residual.Recon.PartitionPrice
import AVRegularity.Construction.ChildInert.Center
import AVRegularity.CycleComparison.LiftSetting.Main
import AVRegularity.CycleJoint.ActivePieceDimensionalSmooth
import AVRegularity.EntryTerminal.Ingredients.Recon.R2Core.Quiet
import AVRegularity.Proofs.WeakGen.Comparison.RowCoefficients

section
section
/-! **The slot lifts with the uniform price at a plan**, read from
`weak_plateau_parent_setting_uniform_at`: `weakSlotLiftUParams`, `weakSlotLiftULevel`,
`WeakSlotLiftUPlanOK`, `weakSlotLiftU_planOK`; the slot lifts of every instance come with
`WeakUniformSlotLifts`. The proofs are those of the slot lifts at a plan
(`weakSlotLiftAt_planOK`).

The degenerate cases are included: `Lr < J_wN_w` (the default parameters, no slot lifts
claimed). -/

@[expose] public noncomputable section

namespace AVRegularity.Providers.WeakGen.Window

open WeakEntryProofs WeakEntryProofs.Assembly Finite.WeakLift
  AVRegularity.Providers.WeakGen.Residual

/-- The base floor `Λ₀(B)` of the uniform-price factory. -/
def weakSlotLiftUFloor (B : WeakCoefficientBase) : ℕ :=
  Classical.choose (weak_plateau_parent_setting_uniform_at B.α B.s B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.q
    B.hq B.ζ B.hζ)

/-- The factory read at `Λ = max Λ₀ A.Λ`, for `J_wN_w ≤ Lr`. -/
theorem weakSlotLiftUEx {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) (Lr sX sZ : ℕ)
    (h : A.Jw * A.Nw ≤ Lr) :
    ∃ P : WeakPositiveParameters A.Nw (A.Jw * A.Rw) (Lr + 3),
      P.capMax = max 2 (1 + A.Jw * A.Nw) ∧ P.slowOrder = Lr + 3 + (A.Nw + P.capMax) ∧
      P.fastOrder = Lr + 3 ∧
      ∀ j₀ : ℕ, IsCarrierStart B.α B.q (max (weakSlotLiftUFloor B) A.Λ) A.bw 1 400 j₀ →
        ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
        ∀ (D : OCData), D.α = B.α → D.q = B.q → D.Λ = max (weakSlotLiftUFloor B) A.Λ →
          D.ζ = B.ζ → IsOCStreamSeq B.α B.q (max (weakSlotLiftUFloor B) A.Λ) B.ζ D.Φ →
          IsOCBandChain B.α B.q (max (weakSlotLiftUFloor B) A.Λ) B.ζ M D.κ → D.term = M →
        ∀ (PW : ProvParams) (Dm : ℕ) (stage : ℕ → GenStage D ScalarH Dm A.bw j₀),
          IsWeakConstruction D PW (⟨A.Nw, A.Rw, sX, sZ, A.η₀, M + A.Jw⟩ : WeakMenu)
            M A.Jw (D.termRW A.σw M) 0 stage →
        ∀ i, M < i → i ≤ M + A.Jw →
          WeakPositiveGeometry P i (stage i) ∧
          ∃ pk : ∀ slot : OddSlot, WeakPositiveSlot P i (stage i)
            (fun v => weakMass D A.Nw A.Jw A.η₀ v.1) slot,
            ∀ slot, (pk slot).price =
              recordMajorant (fun v => weakMass D A.Nw A.Jw A.η₀ v.1) (stage i).fam := by
  obtain ⟨_, hfac⟩ := Classical.choose_spec
    (weak_plateau_parent_setting_uniform_at B.α B.s B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.q B.hq B.ζ B.hζ)
  exact hfac (max (weakSlotLiftUFloor B) A.Λ) (le_max_left _ _)
    A.bw A.bw_pos A.bw_small A.Jw A.Nw A.Rw A.η₀ A.σw A.Jw_pos A.Nw_pos A.η₀_pos A.η₀_small
    A.σw_pos A.σw_small Lr h sX sZ

open scoped Classical in
/-- The slot-lift parameters of the menu at the order `Lr` and the lift orders. -/
def weakSlotLiftUParams {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B)
    (Lr sX sZ : ℕ) : WeakPositiveParameters A.Nw (A.Jw * A.Rw) (Lr + 3) :=
  if h : A.Jw * A.Nw ≤ Lr then Classical.choose (weakSlotLiftUEx A Lr sX sZ h)
  else weakSlotLiftDefault _ _ _

open scoped Classical in
/-- The level floor of the slot lifts, after the carrier start. -/
def weakSlotLiftULevel {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B)
    (Lr sX sZ j₀ : ℕ) : ℕ :=
  if h : A.Jw * A.Nw ≤ Lr ∧
      IsCarrierStart B.α B.q (max (weakSlotLiftUFloor B) A.Λ) A.bw 1 400 j₀ then
    Classical.choose ((Classical.choose_spec (weakSlotLiftUEx A Lr sX sZ h.1)).2.2.2 j₀ h.2)
  else 0

/-- The plan condition of the slot lifts at the consumer's order `Lr`. Floors only. -/
def WeakSlotLiftUPlanOK (plan : WeakPassagePlan)
    (Lr : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B},
      WeakPassageRequest A → ℕ) : Prop :=
  (∀ B, weakSlotLiftUFloor B ≤ plan.baseFloor B) ∧
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A) (j₀ : ℕ),
    weakSlotLiftULevel A (Lr R) R.sX R.sZ j₀ ≤ plan.levelFloor R j₀

/-- **(ii)′ with plan-free parameters and level floor.** -/
theorem weakSlotLiftU_planOK {plan : WeakPassagePlan}
    {Lr : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B},
      WeakPassageRequest A → ℕ}
    (hplan : WeakSlotLiftUPlanOK plan Lr) {B : WeakCoefficientBase}
    (A : WeakCoefficientPhysical B) (R : WeakPassageRequest A) (hLr : A.Jw * A.Nw ≤ Lr R) :
    (weakSlotLiftUParams A (Lr R) R.sX R.sZ).capMax = weakSlotCap A ∧
    (weakSlotLiftUParams A (Lr R) R.sX R.sZ).slowOrder = Lr R + 3 + (A.Nw + weakSlotCap A) ∧
    (weakSlotLiftUParams A (Lr R) R.sX R.sZ).fastOrder = Lr R + 3 ∧
    ∀ c : WeakPassageInstance plan R, ∀ i, c.M < i → i ≤ c.M + A.Jw →
      WeakPositiveGeometry (weakSlotLiftUParams A (Lr R) R.sX R.sZ) i (c.stage i) ∧
      WeakUniformSlotLifts c i (weakSlotLiftUParams A (Lr R) R.sX R.sZ) := by
  have hP : weakSlotLiftUParams A (Lr R) R.sX R.sZ =
      Classical.choose (weakSlotLiftUEx A (Lr R) R.sX R.sZ hLr) := by
    unfold weakSlotLiftUParams; rw [dite_eq_left_of_eq_true (eq_true hLr)]
  obtain ⟨h1, h2, h3, hrest⟩ := Classical.choose_spec (weakSlotLiftUEx A (Lr R) R.sX R.sZ hLr)
  rw [hP]
  refine ⟨h1, by rw [h2, h1]; rfl, h3, fun c i hi hiJ => ?_⟩
  have hmax : max (weakSlotLiftUFloor B) A.Λ = A.Λ :=
    max_eq_right ((hplan.1 B).trans c.base_ge)
  have hcar : IsCarrierStart B.α B.q (max (weakSlotLiftUFloor B) A.Λ) A.bw 1 400 c.j₀ := by
    rw [hmax]; exact c.carrier
  have hlev : weakSlotLiftULevel A (Lr R) R.sX R.sZ c.j₀ =
      Classical.choose (hrest c.j₀ hcar) := by
    unfold weakSlotLiftULevel; rw [dite_eq_left_of_eq_true (eq_true ⟨hLr, hcar⟩)]
  have hM := Classical.choose_spec (hrest c.j₀ hcar)
  refine hM c.M ?_ c.D c.alpha c.q_eq (c.base_eq.trans hmax.symm) c.profile_eq
    (by rw [hmax]; exact c.streams) (by rw [hmax]; exact c.band) c.terminal c.P c.Dm c.stage
    c.construction i hi hiJ
  rw [← hlev]
  exact (hplan.2 R c.j₀).trans c.level_ge


end AVRegularity.Providers.WeakGen.Window
end
end

section
/-! **The setting step from the plan condition of the slot lifts.**

`weakSettingStep_of_plan`: `WeakSlotLiftUPlanOK plan Lr` (floors only), the order floor
`weakWindowLrFloor A k₀ ≤ Lr R` and the lift sequences (`WeakSeqStep`) give `WeakSettingStep`
 at the named constants of `weakSlotLiftUParams A (Lr R) R.sX R.sZ`: `CG, Cw` its fields,
`Ca = weakSettingCa … (weakSettingQs A k₀) (weakSettingQf A k₀)`, `Sb = S`, `Cg = weakGradeConst …`.
`k₀` is a free parameter; no `R_w`, `Λ` or request enters the constants other than through `A`.

The degenerate cases are included: `Lr R` exactly the floor; no observed pulse (the lifts are
vacuous). -/

@[expose] public noncomputable section

namespace AVRegularity.Providers.WeakGen.Window

open WeakEntryProofs WeakEntryProofs.Assembly Finite.WeakLift
  AVRegularity.Providers.WeakGen.Residual

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}
variable (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ) (hi : c.M < i)
  (hit : i ≤ c.M + A.Jw)

/-- The standing facts of an instance from the base floor of the uniform-price factory. -/
theorem weakLifts_standing_U (hfloor : weakSlotLiftUFloor B ≤ plan.baseFloor B) :
    1 ≤ c.D.Λ ∧ 0 < c.D.κ c.M := by
  have h128 : 128 ≤ weakSlotLiftUFloor B :=
    (Classical.choose_spec (weak_plateau_parent_setting_uniform_at B.α B.s B.hα₀ B.hα₁ B.hs₀
      B.hs₁ B.q B.hq B.ζ B.hζ)).1
  have hΛ : 1 ≤ c.D.Λ := by
    rw [c.base_eq]; have := hfloor.trans c.base_ge; omega
  have hζ : IsFastProfile c.D.ζ := by rw [c.profile_eq]; exact B.hζ
  have hκb : IsOCBandChain c.D.α c.D.q c.D.Λ c.D.ζ c.D.term c.D.κ := by
    rw [c.alpha, c.q_eq, c.base_eq, c.profile_eq, c.terminal]; exact c.band
  refine ⟨hΛ, ?_⟩
  have := EntryWeakProofs.weakData_kap_pos c.D hΛ hζ hκb c.M
  rwa [EntryWeakProofs.weakData_kap_terminal c.D c.M (by rw [c.terminal]), c.terminal] at this

/-- **The setting step from the plan condition of the slot lifts.** -/
theorem weakSettingStep_of_plan
    {Lr : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}, WeakPassageRequest A → ℕ}
    (hplan : WeakSlotLiftUPlanOK plan Lr) (h : WeakComparisonInput r i) (k₀ : ℕ)
    (hLr : weakWindowLrFloor A k₀ ≤ Lr R)
    (hX : weakKlift A k₀ + weakDw A + 2 ≤ R.sX)
    (hZ : max (weakLlift A k₀ + 1) (weakLlift A k₀ + 2) ≤ R.sZ)
    (hseq : WeakSeqStep c r i hi hit h k₀) :
    WeakSettingStep c r i hi hit h k₀ (weakSlotLiftUParams A (Lr R) R.sX R.sZ).CG
      (weakSlotLiftUParams A (Lr R) R.sX R.sZ).Cw
      (weakSettingCa (weakSlotLiftUParams A (Lr R) R.sX R.sZ) (weakSettingQs A k₀)
        (weakSettingQf A k₀)) (weakSlotLiftUParams A (Lr R) R.sX R.sZ).S
      (weakGradeConst A k₀ (weakSlotLiftUParams A (Lr R) R.sX R.sZ).CG
        (weakSlotLiftUParams A (Lr R) R.sX R.sZ).Cw
        (weakSettingCa (weakSlotLiftUParams A (Lr R) R.sX R.sZ) (weakSettingQs A k₀)
          (weakSettingQf A k₀))) := by
  obtain ⟨hΛ1, hκM⟩ := weakLifts_standing_U c (hplan.1 B)
  have hJ : A.Jw * A.Nw ≤ Lr R := (weakWindowLrFloor_ge_JN A k₀).trans hLr
  obtain ⟨h1, h2, h3, hrest⟩ := weakSlotLiftU_planOK hplan A R hJ
  have hfl := weakOrderFloors_of_orders A k₀ (Lr R) _ h1 h2 h3 (Nat.mul_pos A.Jw_pos A.Nw_pos) hLr
  obtain ⟨-, hu⟩ := hrest c i hi hit
  exact weakSettingStep_of_parts c r i hi hit h k₀ _ hX hZ hseq
    (weakLiftsStep_of_uniform c r i hi hit k₀ _ hfl hΛ1 hκM hu)

end AVRegularity.Providers.WeakGen.Window
end
end

section
/-! **The lifted comparison of a weak passage from its reconstruction window**
(the application of the physical lift).

`weakLifted_of_window`: at a passage `M < i ≤ M + J_w`, the physical reconstruction on a window
at a free lift length (`ReconPhysicalLiftStatement`, proved as
`reconPhysicalLift`) applied to the weak window `WeakWindow`, with its hypotheses in the
window's own form (the inputs of the coarse side after their adapters), gives the data of
`WeakLiftedComparisonStatement` at the instance, with the forcing cost at most
`2 L^{K_max} · reconBillConst(…) · bill · M`.

The hypotheses are those of `ReconPhysicalLiftStatement` at the data of `WeakWindow`, in the
same order, and four more: the initial datum `X₀` truncates to the incoming value, the
weights of the stage are the cutoffs (naturality), the radius of the forcing cost is at most
`L r_s`, and `k₀` is above the forcing order with `J_wN_w ≤ k₀ + 1`. The classical
representative of the window is the readout of `h.aU`.

The window writes its end `t_p + T_obs`; the conclusion is on `[t_i, a + T₀]`
(`weakWindow_end`). The proof is one application of the statement, then
`weakLifted_of_output`: the conversion (`weakLifted_value`, `weakLifted_errSol`,
`weakLifted_cost`) stated with the end of the window as a variable `tf = a + T₀`, so that the
end is substituted there and nothing is rewritten after the application. The two are separate
theorems to keep each elaboration small: the application and each rewrite of the end are
elaborated separately.

The degenerate cases are included: `bill = 0` or `M = 0` gives zero forcing cost; `L = 1` when
`plan.radius R · ε_i ≤ r_s`. -/

@[expose] public noncomputable section

open MeasureTheory Filter Topology Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Reconstruction AVRegularity.CycleComparison.Lift
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.ChartTransport
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.EntryWeakProofs AVRegularity.Construction.Residual.Presentation
open scoped ENNReal

namespace AVRegularity.Providers.WeakGen.Window

open WeakEntryProofs WeakEntryProofs.Assembly Residual

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- The end of the window is `a + T₀`. -/
theorem weakWindow_end (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ) :
    r.tq i + wTobs c r i = r.a + A.T₀ := by
  show r.tq i + (r.a + A.T₀ - r.tq i) = r.a + A.T₀
  ring

/-- **The lifted comparison from the output of the physical lift**, on a window written with
any end `tf = a + T₀` (the reconstruction window writes `t_p + T_obs`). -/
theorem weakLifted_of_output (c : WeakPassageInstance plan R) (r : WeakPassageRun c)
    (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw) (h : WeakComparisonInput r i) (k₀ : ℕ)
    (hk₀J : A.Jw * A.Nw ≤ k₀ + 1) (hk₀f : plan.forcingOrder R ≤ k₀)
    (hΛ : 1 ≤ c.D.Λ) (hκ : 0 < c.D.κ c.M)
    (hπ : ∀ v : CompIn (c.stage i).comps, 0 < weakMass c.D A.Nw A.Jw A.η₀ v.1)
    (hw : ∀ (p : OddSlot) (s : ℝ),
      (c.stage i).fam.weight p s = ocCutoff c.D.α c.D.q c.D.Λ i p.1 s)
    {rs L Xb : ℝ} (hL : 1 ≤ L) (hrad : plan.radius R * c.D.eps i ≤ L * rs) (hXb : 0 ≤ Xb)
    {Kmax : ℕ} (hKmax : ∀ v, weakWindowSlots c i k₀ v ≤ Kmax)
    {tf : ℝ} (htf : tf = r.a + A.T₀)
    (û : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk (weakWindowSlots c i k₀ v) (ScalarH v.1.root))
    (ŵ : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk (weakWindowSlots c i k₀ v + 1) (ScalarH v.1.root))
    (Rres : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk (weakWindowSlots c i k₀ v) (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (qres : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk (weakWindowSlots c i k₀ v) (ScalarH v.1.root))
    (hval : ∀ t ∈ Set.Icc (r.tq i) tf, ∀ v,
      (û v t).toFunction.jet (valueIndex2 (weakWindowSlots c i k₀ v))
        =ᵐ[volume.restrict AVenhance.unitCube]
        fun x => gluedLift (ocObsPulses c.D.α c.D.q c.D.Λ i (r.tq i) tf)
          (fun k => (weakWindowFamily c i hi hit).weight (oddSlotOf k))
          (ocEll c.D.q c.D.Λ i (c.D.κ c.M) ^ 2) (ocEpsilon c.D.q c.D.Λ (i - 1))
          (ocEpsilon c.D.q c.D.Λ i)
          (ocDStar c.D.q c.D.Λ i (c.D.κ c.M) (c.D.κ c.M) / ocEpsilon c.D.q c.D.Λ (i - 1))
          A.Nw (A.Jw * A.Rw) (h.CcR i)
          (fun k => ocChart c.D.α c.D.q c.D.Λ i (c.D.Φ (i - 1)) (c.D.hΦ (i - 1))
            (ocPulseChartIndex c.D.α c.D.q c.D.Λ i k))
          (fun k => ocChartInv c.D.α c.D.q c.D.Λ i (c.D.Φ (i - 1)) (c.D.hΦ (i - 1))
            (ocPulseChartIndex c.D.α c.D.q c.D.Λ i k))
          (fun s y w' => weakReadoutStep i A.η₀ (c.stage i) (c.stage (i - 1)) (h.aU s) w' y)
          t x v)
    (hsol : IsCoupledWeakSolutionTorus (c.D.κ c.M) (r.tq i) tf
      (streamVel (c.D.Φ i)) (1 + A.Jw * A.Nw) (weakWindowSlots c i k₀)
      (edgeCoefficient (weakWindowFamily c i hi hit) (c.D.κ c.M) (ocEpsilon c.D.q c.D.Λ i)
        (ocEpsilon c.D.q c.D.Λ (i - 1)) (fun _ => ()) (weakWindowSlots c i k₀))
      (fun v => û v (r.tq i)) Rres qres û ŵ)
    (hinit : ∀ v, truncateTorusHk (Nat.zero_le _) (û v (r.tq i)) = weakIncomingInit r i v)
    (hRm : ∀ v, MemLp (Rres v) 2 (volume.restrict (Set.Icc (r.tq i) tf)))
    (hqi : ∀ v, Integrable (qres v) (volume.restrict (Set.Icc (r.tq i) tf)))
    (hRb : (c.D.κ c.M)⁻¹ * ∫ s in Set.Icc (r.tq i) tf,
        massNormSq (E := fun v : CompIn (c.stage i).comps =>
            PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))
          (K := weakWindowSlots c i k₀) rs (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1)
          (fun v => (Rres v s).val) ≤ Xb ^ 2)
    (hqb : ∫ s in Set.Icc (r.tq i) tf,
        Real.sqrt (massNormSq (E := fun v : CompIn (c.stage i).comps => ScalarH v.1.root)
          (K := weakWindowSlots c i k₀) rs (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1)
          (fun v => (qres v s).val)) ≤ Xb) :
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
      weakComparisonForcingCost r i F g ≤ ENNReal.ofReal (L ^ Kmax * Xb + L ^ Kmax * Xb) := by
  subst htf
  obtain ⟨hFmeas, hgmeas, hcost⟩ := weakLifted_cost c r i k₀ hk₀f hΛ hκ hπ hL hrad hXb hKmax
    Rres qres hRm hqi hRb hqb
  have key := weakLifted_errSol c r i hi hit k₀ hk₀J hk₀f hsol hinit
  exact ⟨weakLiftedF c i k₀ hk₀f Rres, weakLiftedG c i k₀ hk₀f qres, _, _, _, hFmeas, hgmeas,
    fun v t ht => weakLifted_value c r i hi hit h k₀ hΛ hκ hw û hval v t ht,
    fun v => key.2.2.1 v, key, hcost⟩

/-- **The lifted comparison of a weak passage from its reconstruction window.** -/
theorem weakLifted_of_window (hPL : ReconPhysicalLiftStatement)
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (h : WeakComparisonInput r i) (k₀ : ℕ)
    (hk₀J : A.Jw * A.Nw ≤ k₀ + 1) (hk₀f : plan.forcingOrder R ≤ k₀)
    (hΛ : 1 ≤ c.D.Λ) (hκ : 0 < c.D.κ c.M)
    (hπ : ∀ v : CompIn (c.stage i).comps, 0 < weakMass c.D A.Nw A.Jw A.η₀ v.1)
    (hw : ∀ (p : OddSlot) (s : ℝ),
      (c.stage i).fam.weight p s = ocCutoff c.D.α c.D.q c.D.Λ i p.1 s)
    {T : (weakWindowFamily c i hi hit).Atlas} {Cpart : ℝ} {qs qf : ℕ}
    {CGl Cw : ℕ → ℝ} {Ca : ℝ} {bM : CompIn (c.stage i).comps → CompIn (c.stage i).comps → ℝ}
    {Sb : ℝ} {aC B₀C lamC : ℝ} {pc Jc kc : ℕ}
    {AD : ∀ d : Finset.Icc 2 (A.Nw + weakDw A), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : CompIn (c.stage i).comps) (d : Finset.Icc 2 (A.Nw + weakDw A)),
      ℝ → Vec 2 → (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ScalarH u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))}
    {Aedge : Matrix (CompIn (c.stage i).comps) (CompIn (c.stage i).comps) ℝ} {Cstar Θc : ℝ}
    {f0 : ∀ v : CompIn (c.stage i).comps,
      TorusHk (kc + (Jc + weakH A + 3) * ((A.Nw + weakDw A) + 8 * pc + 4)) (ScalarH v.1.root)}
    {W : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk (kc + 1 + (A.Nw + weakDw A)) (ScalarH v.1.root)}
    {Fc : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))} {r₀ : ℕ}
    (w : WeakWindow c r i hi hit h k₀ T Cpart qs qf CGl Cw Ca bM Sb aC B₀C lamC pc Jc kc AD CE
      Aedge Cstar Θc f0 W Fc
      (fun s y w' => weakReadoutStep i A.η₀ (c.stage i) (c.stage (i - 1)) (h.aU s) w' y) r₀)
    {Kmax Acl m' kres Nχ : ℕ}
    (o : ReconOrders (weakDw A) A.Nw (weakH A) (weakKlift A k₀) (weakLlift A k₀) kc Jc pc r₀
      Kmax Acl m' kres Nχ)
    (hKmax : ∀ v, weakWindowSlots c i k₀ v ≤ Kmax) (hSb : 0 ≤ Sb) {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hgr : ∀ k ∈ ocObsPulses c.D.α c.D.q c.D.Λ i (r.tq i) (r.tq i + wTobs c r i), ∀ hh,
      hh ≤ weakH A → ∀ n, 1 ≤ n → n ≤ A.Nw → ∀ m'', 1 ≤ m'' → m'' ≤ n →
      ∀ j, j ≤ Acl + 2 + Kmax →
        schurEnergyJet (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
          (Set.Icc (wSeqStart c r i k) (wSeqEnd c r i k)) (weakLlift A k₀) j
          (h.CcR i k hh n m'') ≤
        ENNReal.ofReal (Cg * Sb ^ hh *
          (ocEpsilon c.D.q c.D.Λ (i - 1) / ocEpsilon c.D.q c.D.Λ (i - 1)) ^ (n - m'' + j)))
    {rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ ocEpsilon c.D.q c.D.Λ i)
    (hrsρ : rs ≤ ocEpsilon c.D.q c.D.Λ (i - 1))
    (hWc : ∀ v, ContinuousOn (W v) (Set.Icc (r.tq i) (r.tq i + wTobs c r i)))
    (hle : r.tq i ≤ r.tq i + wTobs c r i)
    (hFm : ∀ n r', Measurable fun s =>
      coarseModeCoeff n (fun v => Fc v (Set.projIcc (r.tq i) (r.tq i + wTobs c r i) hle s)) r')
    (hFcm : ∀ v, AEStronglyMeasurable (Fc v)
      (volume.restrict (Set.Icc (r.tq i) (r.tq i + wTobs c r i))))
    {Vb : ℝ}
    (hbm : ∀ s ∈ Set.Ioc (r.tq i) (r.tq i + wTobs c r i), ∀ k,
      AEStronglyMeasurable (fun x => streamVel (c.D.Φ i) s x k)
        (volume.restrict AVenhance.unitCube))
    (hVb : ∀ s ∈ Set.Ioc (r.tq i) (r.tq i + wTobs c r i), ∀ x k,
      |streamVel (c.D.Φ i) s x k| ≤ Vb)
    {CA : ℝ} (hCA : 0 ≤ CA)
    (hAb : ∀ s ∈ Set.Icc (r.tq i) (r.tq i + wTobs c r i), ∀ v u d x,
      ‖(edgeCoefficient (weakWindowFamily c i hi hit) (c.D.κ c.M) (ocEpsilon c.D.q c.D.Λ i)
        (ocEpsilon c.D.q c.D.Λ (i - 1)) (fun _ => ()) (weakWindowSlots c i k₀)) v u d s x‖ ≤ CA)
    (hAm : ∀ s ∈ Set.Icc (r.tq i) (r.tq i + wTobs c r i), ∀ v u d,
      AEStronglyMeasurable ((edgeCoefficient (weakWindowFamily c i hi hit) (c.D.κ c.M)
        (ocEpsilon c.D.q c.D.Λ i) (ocEpsilon c.D.q c.D.Λ (i - 1)) (fun _ => ())
        (weakWindowSlots c i k₀)) v u d s) (volume.restrict AVenhance.unitCube))
    {X Y M tt bill Cs Cy Cpx : ℝ} (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y) (hM : 0 ≤ M) (htt : 0 ≤ tt)
    (hCs : 0 ≤ Cs) (hCy : 0 ≤ Cy) (hCpx : 0 ≤ Cpx)
    {ord : ℕ} (hordE : ord + 1 ≤ kc + 1 + (A.Nw + weakDw A)) {Xp : ℝ} (hXp : 0 ≤ Xp)
    (hPB : WeakWindowPartitionAt c r i hi hit h Kmax ord rs Xp W)
    (hEn : strongEnergyUpTo (ocEpsilon c.D.q c.D.Λ (i - 1)) (c.D.κ c.M)
        (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
        (r.tq i) (r.tq i + wTobs c r i) ord W ≤ ENNReal.ofReal X)
    (hX : strongEnergyUpTo (ocEpsilon c.D.q c.D.Λ (i - 1)) (c.D.κ c.M)
        (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
        (r.tq i) (r.tq i + wTobs c r i) m' W ≤ ENNReal.ofReal X)
    (hY : ENNReal.ofReal (Real.sqrt (c.D.κ c.M))⁻¹ *
        (∫⁻ s in Set.Icc (r.tq i) (r.tq i + wTobs c r i), ENNReal.ofReal
          (massNormSq (E := fun v : CompIn (c.stage i).comps =>
              PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)) (K := fun _ => kc)
            (ocEpsilon c.D.q c.D.Λ (i - 1))
            (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
            (fun v => (Fc v s).val))) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal Y)
    (hXM : X ≤ Cs * M) (hYM : Y ≤ Cy * M * tt) (hPM : Xp ≤ Cpx * bill)
    (hb1 : (ocDStar c.D.q c.D.Λ i (c.D.κ c.M) (c.D.κ c.M) /
      ocEpsilon c.D.q c.D.Λ (i - 1)) ^ A.Nw ≤ bill)
    (hb2 : Real.sqrt (c.D.κ c.M / c.D.κ c.M) * tt ≤ bill)
    (hb3 : (ocDStar c.D.q c.D.Λ i (c.D.κ c.M) (c.D.κ c.M) /
      ocEpsilon c.D.q c.D.Λ (i - 1)) ^ 2 * tt ≤ bill)
    (hb4 : (ocDStar c.D.q c.D.Λ i (c.D.κ c.M) (c.D.κ c.M) /
      ocEpsilon c.D.q c.D.Λ (i - 1)) ^ A.Nw *
      (Real.sqrt (wTobs c r i) / ocEll c.D.q c.D.Λ i (c.D.κ c.M) *
        (ocEpsilon c.D.q c.D.Λ i / ocEpsilon c.D.q c.D.Λ (i - 1)) ^ Acl) ≤ bill)
    (hb5 : (ocDStar c.D.q c.D.Λ i (c.D.κ c.M) (c.D.κ c.M) /
      ocEpsilon c.D.q c.D.Λ (i - 1)) ^ 2 *
      (Real.sqrt (wTobs c r i) / ocEll c.D.q c.D.Λ i (c.D.κ c.M) *
        (ocEpsilon c.D.q c.D.Λ i / ocEpsilon c.D.q c.D.Λ (i - 1)) ^ Acl) * tt ≤ bill)
    (Mv : CompIn (c.stage i).comps → ℕ) (X0 : ∀ v, TorusHk (Mv v) (ScalarH v.1.root))
    (hNM : ∀ v, kc + (Jc + weakH A + 3) * ((A.Nw + weakDw A) + 8 * pc + 4) ≤ Mv v)
    (hKM : ∀ v, weakWindowSlots c i k₀ v ≤ Mv v)
    (hXst : ∀ v, truncateTorusHk (hNM v) (X0 v) = f0 v)
    (hinit : ∀ v, truncateTorusHk (Nat.zero_le _) (X0 v) = weakIncomingInit r i v)
    {L : ℝ} (hL : 1 ≤ L) (hrad : plan.radius R * c.D.eps i ≤ L * rs) :
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
      weakComparisonForcingCost r i F g ≤ ENNReal.ofReal
        (L ^ Kmax * (reconBillConst (weakH A) A.Nw (weakDw A) Acl Kmax m' kres Nχ
            (weakKlift A k₀) (weakLlift A k₀) CGl Cw Ca Sb Cg Cs Cy (Cpx * Cs) * bill * M) +
          L ^ Kmax * (reconBillConst (weakH A) A.Nw (weakDw A) Acl Kmax m' kres Nχ
            (weakKlift A k₀) (weakLlift A k₀) CGl Cw Ca Sb Cg Cs Cy (Cpx * Cs) * bill * M)) := by
  obtain ⟨û, ŵ, Rres, qres, hval, hsol, -, hû0, hRm, hqi, hRb, hqb⟩ :=
    hPL w o hKmax hSb hCg hgr hrs hrse hrsρ hWc hFm hFcm hbm hVb hCA hAb hAm hX0 hY0 hM htt
      hCs hCy hCpx hordE hXp hPB hEn hX hY hXM hYM hPM hb1 hb2 hb3 hb4 hb5 Mv X0 hNM hKM hXst
  have hinit' : ∀ v, truncateTorusHk (Nat.zero_le _) (û v (r.tq i)) = weakIncomingInit r i v :=
    fun v => by rw [hû0 v]; exact hinit v
  have hXb : 0 ≤ reconBillConst (weakH A) A.Nw (weakDw A) Acl Kmax m' kres Nχ
      (weakKlift A k₀) (weakLlift A k₀) CGl Cw Ca Sb Cg Cs Cy (Cpx * Cs) * bill * M :=
    le_trans (integral_nonneg fun _ => Real.sqrt_nonneg _) hqb
  exact weakLifted_of_output c r i hi hit h k₀ hk₀J hk₀f hΛ hκ hπ hw hL hrad hXb hKmax
    (weakWindow_end c r i) û ŵ Rres qres hval hsol hinit' hRm hqi hRb hqb

end AVRegularity.Providers.WeakGen.Window
end
end

section
/-! **The coarse side of the weak window from its pieces**.

The pieces of the coarse side are stated on the window `[t_i, a + T₀]`; the reconstruction window writes its
end `t_p + T_obs` (`weakWindow_end`). Two lemmas move the coarse side.

* `weakCoarseBody_of_parts`: the coarse setting, the classical representative of the
  readout (`cdW_isClassicalRep`) and the mean presentations, on `[t_i, a + T₀]`, with
  the coarse defect equation on the window (from `weakFlux_at_window`), give `WeakCoarseBody`
  (the coarse hypotheses of `mkWeakReconWindow`), at `p_c = 1`, `J_c = 0`.
* `weakFlux_at_window`: the coarse defect equation with a flux `Fc₀` and the bound of `Fc₀` in
  the mass form, on `[t_i, a + T₀]`, give a strongly measurable version `Fc` with the
  equation on the window, measurable Galerkin coefficients at the clamped time, and the flux
  bound `hY` of the physical lift (`coarseFlux_version`).

The degenerate cases are included: `t_i = a + T₀` is a one-point window (`T_obs = 0`), on which both
lemmas hold; `Y = 0` forces the flux to vanish almost everywhere. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Reconstruction AVRegularity.CycleComparison.Lift
open AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.EntryWeakProofs AVRegularity.Construction.Residual.Presentation
open scoped ENNReal

namespace AVRegularity.Providers.WeakGen.Window

open WeakEntryProofs WeakEntryProofs.Assembly

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- **The coarse hypotheses of the weak window** from the pieces on `[t_i, a + T₀]`. -/
theorem weakCoarseBody_of_parts (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ)
    (hi : c.M < i) (hit : i ≤ c.M + A.Jw) (h : WeakComparisonInput r i)
    {aC B₀C lamC : ℝ} {kc : ℕ}
    {AD : ∀ d : Finset.Icc 2 (A.Nw + weakDw A), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : CompIn (c.stage i).comps) (d : Finset.Icc 2 (A.Nw + weakDw A)),
      ℝ → Vec 2 → (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ScalarH u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))}
    {Aedge : Matrix (CompIn (c.stage i).comps) (CompIn (c.stage i).comps) ℝ} {Cstar Θc : ℝ}
    {f0 : ∀ v : CompIn (c.stage i).comps,
      TorusHk (kc + (0 + weakH A + 3) * ((A.Nw + weakDw A) + 8 * 1 + 4)) (ScalarH v.1.root)}
    {W : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk (kc + 1 + (A.Nw + weakDw A)) (ScalarH v.1.root)}
    {Fc : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))}
    {aRep : ℝ → Vec 2 → ∀ v : CompIn (c.stage i).comps, ScalarH v.1.root}
    (hcs : IsCoarseSetting (r.tq i) (r.a + A.T₀) (wRhoC c i) (c.D.κ c.M) aC B₀C lamC
      (streamVel (c.D.Φ (i - 1))) (A.Nw + weakDw A) (weakH A) 1 0 kc
      ((A.Nw + weakDw A) + 8 * 1 + 4)
      (kc + (0 + weakH A + 3) * ((A.Nw + weakDw A) + 8 * 1 + 4)) (wJm c) AD CE
      (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1) Aedge Cstar Θc)
    (hcd : IsCoarseDefect (r.tq i) (r.tq i + wTobs c r i) (c.D.κ c.M)
      (streamVel (c.D.Φ (i - 1))) (A.Nw + weakDw A) (weakH A) kc
      (kc + (0 + weakH A + 3) * ((A.Nw + weakDw A) + 8 * 1 + 4)) AD CE (wJm c) f0 W Fc)
    (hrep : ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀), ∀ v,
      IsClassicalRep (W v t) (fun x => aRep t x v) (kc + (A.Nw + weakDw A) - 1))
    (hmean : ∀ ρ ∈ Finset.range (weakH A + 1),
      IsMeanPresentation (Set.Icc (r.tq i) (r.a + A.T₀)) (A.Nw + weakDw A) ρ AD CE (wJm c)
        (gluedMean (ocObsPulses c.D.α c.D.q c.D.Λ i (r.tq i) (r.a + A.T₀))
          (fun k => (weakWindowFamily c i hi hit).weight (oddSlotOf k))
          (ocEll c.D.q c.D.Λ i (c.D.κ c.M) ^ 2) (ocEpsilon c.D.q c.D.Λ (i - 1))
          (ocDStar c.D.q c.D.Λ i (c.D.κ c.M) (c.D.κ c.M) / ocEpsilon c.D.q c.D.Λ (i - 1))
          A.Nw ρ (fun k => wLiftData c i hi hit k) (h.CcR i)
          (fun k => ocChart c.D.α c.D.q c.D.Λ i (c.D.Φ (i - 1)) (c.D.hΦ (i - 1))
            (ocPulseChartIndex c.D.α c.D.q c.D.Λ i k))
          (fun k => ocChartInv c.D.α c.D.q c.D.Λ i (c.D.Φ (i - 1)) (c.D.hΦ (i - 1))
            (ocPulseChartIndex c.D.α c.D.q c.D.Λ i k)))) :
    WeakCoarseBody c r i hi hit h aC B₀C lamC 1 0 kc AD CE Aedge Cstar Θc f0 W Fc aRep := by
  unfold WeakCoarseBody
  refine ⟨?_, hcd, ?_, ?_⟩
  · rw [weakWindow_end c r i]
    exact hcs
  · rw [weakWindow_end c r i]
    exact hrep
  · rw [weakWindow_end c r i]
    exact hmean

/-- **A measurable version of the coarse flux on the weak window**, with its equation and its
bound, from the equation and the mass bound on `[t_i, a + T₀]`. -/
theorem weakFlux_at_window (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ)
    (hle : r.tq i ≤ r.tq i + wTobs c r i) (hκ : 0 < c.D.κ c.M)
    (hπ : ∀ v : CompIn (c.stage i).comps, 0 < weakMass c.D A.Nw A.Jw A.η₀ v.1)
    {kc N₀ D H : ℕ} {b : ℝ → Vec 2 → Vec 2}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : CompIn (c.stage i).comps) (d : Finset.Icc 2 D),
      ℝ → Vec 2 → (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ScalarH u.1.root)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {f0 : ∀ v : CompIn (c.stage i).comps, TorusHk N₀ (ScalarH v.1.root)}
    {W : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk (kc + 1 + D) (ScalarH v.1.root)}
    {Fc₀ : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))} {ρ Y : ℝ}
    (hcd : IsCoarseDefect (r.tq i) (r.a + A.T₀) (c.D.κ c.M) b D H kc N₀ AD CE Jm f0 W Fc₀)
    (hF : FluxMassLe (ι := CompIn (c.stage i).comps) (h := fun v => ScalarH v.1.root)
      (K := fun _ => kc) (c.D.κ c.M) ρ (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1)
      (Set.Icc (r.tq i) (r.a + A.T₀)) Fc₀ Y) :
    ∃ Fc : ∀ v : CompIn (c.stage i).comps, ℝ →
        TorusHk kc (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)),
      IsCoarseDefect (r.tq i) (r.tq i + wTobs c r i) (c.D.κ c.M) b D H kc N₀ AD CE Jm f0 W Fc ∧
      (∀ n r', Measurable fun s => coarseModeCoeff n
        (fun v => Fc v (Set.projIcc (r.tq i) (r.tq i + wTobs c r i) hle s)) r') ∧
      (∀ v, AEStronglyMeasurable (Fc v)
        (volume.restrict (Set.Icc (r.tq i) (r.tq i + wTobs c r i)))) ∧
      ENNReal.ofReal (Real.sqrt (c.D.κ c.M))⁻¹ *
        (∫⁻ s in Set.Icc (r.tq i) (r.tq i + wTobs c r i), ENNReal.ofReal
          (massNormSq (E := fun v : CompIn (c.stage i).comps =>
              PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)) (K := fun _ => kc) ρ
            (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
            (fun v => (Fc v s).val))) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal Y := by
  rw [← weakWindow_end c r i] at hcd hF
  exact coarseFlux_version hle hκ hπ hcd hF

/-- **The analytic hypotheses of the weak window in the window's form**: time continuity of the
readout, the drift and edge bounds (the coefficient bounds through `weakWindow_edge_bounds`) and the two
energies (readout energy bound), from their forms on `[t_i, a + T₀]`. -/
theorem weakAnalytic_at_window (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ)
    (hi : c.M < i) (hit : i ≤ c.M + A.Jw) (k₀ : ℕ) {K' ord m' : ℕ} {X Vb CA : ℝ}
    {W : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk K' (ScalarH v.1.root)}
    (hWc : ∀ v, ContinuousOn (W v) (Set.Icc (r.tq i) (r.a + A.T₀)))
    (hb : Residual.WeakReconBoundsAt c r i (weakWindowSlots c i k₀) Vb CA)
    (hEn : strongEnergyUpTo (ocEpsilon c.D.q c.D.Λ (i - 1)) (c.D.κ c.M)
        (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
        (r.tq i) (r.a + A.T₀) ord W ≤ ENNReal.ofReal X)
    (hX : strongEnergyUpTo (ocEpsilon c.D.q c.D.Λ (i - 1)) (c.D.κ c.M)
        (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
        (r.tq i) (r.a + A.T₀) m' W ≤ ENNReal.ofReal X) :
    (∀ v, ContinuousOn (W v) (Set.Icc (r.tq i) (r.tq i + wTobs c r i))) ∧
    (∀ s ∈ Set.Ioc (r.tq i) (r.tq i + wTobs c r i), ∀ k,
      AEStronglyMeasurable (fun x => streamVel (c.D.Φ i) s x k)
        (volume.restrict AVenhance.unitCube)) ∧
    (∀ s ∈ Set.Ioc (r.tq i) (r.tq i + wTobs c r i), ∀ x k,
      |streamVel (c.D.Φ i) s x k| ≤ Vb) ∧
    (∀ s ∈ Set.Icc (r.tq i) (r.tq i + wTobs c r i), ∀ v u d x,
      ‖(edgeCoefficient (weakWindowFamily c i hi hit) (c.D.κ c.M) (ocEpsilon c.D.q c.D.Λ i)
        (ocEpsilon c.D.q c.D.Λ (i - 1)) (fun _ => ()) (weakWindowSlots c i k₀)) v u d s x‖ ≤
          CA) ∧
    (∀ s ∈ Set.Icc (r.tq i) (r.tq i + wTobs c r i), ∀ v u d,
      AEStronglyMeasurable ((edgeCoefficient (weakWindowFamily c i hi hit) (c.D.κ c.M)
        (ocEpsilon c.D.q c.D.Λ i) (ocEpsilon c.D.q c.D.Λ (i - 1)) (fun _ => ())
        (weakWindowSlots c i k₀)) v u d s) (volume.restrict AVenhance.unitCube)) ∧
    strongEnergyUpTo (ocEpsilon c.D.q c.D.Λ (i - 1)) (c.D.κ c.M)
        (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
        (r.tq i) (r.tq i + wTobs c r i) ord W ≤ ENNReal.ofReal X ∧
    strongEnergyUpTo (ocEpsilon c.D.q c.D.Λ (i - 1)) (c.D.κ c.M)
        (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
        (r.tq i) (r.tq i + wTobs c r i) m' W ≤ ENNReal.ofReal X := by
  have he := weakWindow_edge_bounds c r i hi hit (weakWindowSlots c i k₀) hb
  rw [weakWindow_end c r i]
  exact ⟨hWc, hb.2.1, hb.2.2.1, he.1, he.2, hEn, hX⟩

end AVRegularity.Providers.WeakGen.Window
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Providers.WeakGen.Window

/-! **The initial datum of the weak window**.

The physical lift of the window takes a datum `X₀` at orders `M_v` above the order `N₀` of the
coarse equation and above the slots, with `trunc_{N₀} X₀ = f₀`, and the passage needs
`trunc₀ X₀ = U(t_i)` (`weakIncomingInit`). `weakInit_at_window`: `X₀ = cdF` at one high order
`N_hi ≤ K_w + m` has both, the first by `cdReadout_truncate`, the second by `WeakCoarseInitialStatement`
under the two clauses of the high-reserve energy statement.

The degenerate cases are included: `N₀ = N_hi` is no truncation; `N_hi = 0` forces `N₀ = 0` and both
clauses are `WeakCoarseInitialStatement`; at the root `i = M + J_w` it uses the clause `hvr`
only. -/

open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction
  AVRegularity.Providers.WeakGen.Residual AVRegularity.Providers.WeakGen.Residual.CoarseDefect

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}

/-- **The datum `X₀ = cdF` at the order `N_hi`** truncates to `f₀ = cdF` at the order `N₀` of the
coarse equation and, at order zero, to the incoming value `U(t_i)`. -/
theorem weakInit_at_window (hI : WeakCoarseInitialStatement plan) (R : WeakPassageRequest A)
    (m Nhi : ℕ) (hNhi : Nhi ≤ R.Kw + m) (c : WeakPassageInstance plan R)
    (r : WeakPassageRun c) (Uhi : ∀ j, WeakStageFamily (weakPassageRawSetting c) m j)
    (hvr : ∀ v : CompIn (c.stage (c.M + A.Jw)).comps,
      ∀ t ∈ Set.Icc (r.tq (c.M + A.Jw + 1)) (r.a + A.T₀),
      truncateTorusHk (weakReductionReserve_kw_le R m v.1) (Uhi (c.M + A.Jw) v t) =
        r.Ur (c.M + A.Jw) v t)
    (hval : ∀ j, c.M < j → j ≤ c.M + A.Jw → ∀ v : CompIn (c.stage (j - 1)).comps,
      ∀ t ∈ Set.Icc (r.tq j) (r.a + A.T₀),
        truncateTorusHk (weakReductionReserve_kw_le R m v.1) (Uhi (j - 1) v t) =
          r.Ur (j - 1) v t)
    (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw) (hle : r.tq i ≤ r.a + A.T₀) {N₀ : ℕ}
    (hN₀ : N₀ ≤ Nhi) :
    (∀ v : CompIn (c.stage i).comps,
      truncateTorusHk hN₀
          (cdF c r m Nhi (fun w => hNhi.trans (weakReductionReserve_kw R m w)) i Uhi v) =
        cdF c r m N₀ (fun w => (hN₀.trans hNhi).trans (weakReductionReserve_kw R m w)) i Uhi
          v) ∧
    ∀ v : CompIn (c.stage i).comps,
      truncateTorusHk (Nat.zero_le Nhi)
          (cdF c r m Nhi (fun w => hNhi.trans (weakReductionReserve_kw R m w)) i Uhi v) =
        weakIncomingInit r i v :=
  ⟨fun v => cdReadout_truncate c m N₀ Nhi hN₀ _ i _ _ v,
    fun v => hI R m Nhi hNhi c r Uhi hvr hval i hi hit hle v⟩

end AVRegularity.Providers.WeakGen.Window
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryWeakProofs
namespace AVRegularity.Providers.WeakGen.Window

/-! **The lift sequences and the scale step under the plan conditions**. `WeakSeqStep` is proved from its three parts
(`weakSeqCap_of`, `weakSeqAgree_of`, `weakSeqQuietZero_of`) under `WeakSeqPlanOK plan`
(the common floors and the ellipticity floor); `k₀` stays a free parameter. The scale step
`WeakScaleStep` needs only `WeakPassageCommonOK plan` (`weakPassage_two_le_M`). -/

open WeakEntryProofs WeakEntryProofs.Assembly

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- The plan condition of the sequence step: the common floors and the ellipticity floor. -/
def WeakSeqPlanOK (plan : WeakPassagePlan) : Prop :=
  WeakPassageCommonOK plan ∧ WeakPassageEllOK plan

/-- **The lift sequences, proved**: the lift sequences of the observed pulses on the clipped windows. -/
theorem weakSeqStep_of_plan (hplan : WeakSeqPlanOK plan) (c : WeakPassageInstance plan R)
    (r : WeakPassageRun c) (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw)
    (h : WeakComparisonInput r i) (k₀ : ℕ) : WeakSeqStep c r i hi hit h k₀ :=
  weakSeqStep_of_parts c r i hi hit h k₀ (weakSeqCap_of c r i hi hit h) (weakSeqAgree_of c i hi hit)
    (weakSeqQuietZero_of hplan.1 hplan.2 c r i hi hit h)

end AVRegularity.Providers.WeakGen.Window
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Reconstruction AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs AVRegularity.Construction.Residual.Presentation
namespace AVRegularity.Providers.WeakGen.Window

/-! **At the time `t_i` the glued lift of a passage is the identity**.

The positive lift coefficients of every observed pulse vanish at the cell time of `t_i` (the proof
of `weakSeqQuietZero_of`, which does not use the deadline); grades `≥ 1` at degree `0` vanish by the
lift sequence; the degree-zero coefficient of grade zero reads only the value of the field (clause 1
of `IsLiftSequence` applied to a constant field). Each pulse is then the field composed with a chart
and its inverse, and the cutoffs sum to one. -/

open WeakEntryProofs WeakEntryProofs.Assembly

section Generic

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

/-- **Step 2/3 (generic).** A lift sequence whose positive-degree coefficients vanish at the cell
time `s` evaluates, at `s`, to the value of the field only. -/
theorem gluedStart_liftApply_apart {Q : LiftOperatorData ι h D} {sX sZ : ℕ} {t₀ t₁ : ℝ} {N H : ℕ}
    {Cc : ℕ → ℕ → LiftCoeff ι h} (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) {s : ℝ}
    (hq : ∀ hh ≤ H, ∀ n, 1 ≤ n → ∀ m (α : DerivativeWord2 m) X z v u, Cc hh n m α s X z v u = 0)
    {hh n : ℕ} (hhH : hh ≤ H) (hne : hh ≠ 0 ∨ n ≠ 0) (f : ℝ → Vec 2 → ∀ i, h i) (X z : Vec 2) :
    liftApply n (Cc hh n) f s X z = 0 := by
  funext v
  have hc : ∀ m (α : DerivativeWord2 m) u, Cc hh n m α s X z v u = 0 := by
    intro m α u
    by_cases hn : n = 0
    · subst hn
      have hh0 : hh ≠ 0 := hne.resolve_right (by simp)
      exact hseq.2.1 hh (Nat.one_le_iff_ne_zero.2 hh0) hhH m α s X z v u
    · exact hq hh hhH n (Nat.one_le_iff_ne_zero.2 hn) m α X z v u
  simp [liftApply, hc]

/-- **Step 3 (generic).** At degree `0`, grade `0`, only the value of the field at `X` is read. -/
theorem gluedStart_liftApply_zero {Q : LiftOperatorData ι h D} {sX sZ : ℕ} {t₀ t₁ : ℝ} {N H : ℕ}
    {Cc : ℕ → ℕ → LiftCoeff ι h} (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) {s : ℝ}
    (hs : s ∈ Set.Icc t₀ t₁) (f : ℝ → Vec 2 → ∀ i, h i) (X z : Vec 2) :
    liftApply 0 (Cc 0 0) f s X z = f s X := by
  have h1 := hseq.1 (fun _ => f s X) contDiff_const s hs X z
  have h2 : liftApply 0 (Cc 0 0) f s X z = liftApply 0 (Cc 0 0) (fun _ _ => f s X) s X z := by
    funext v
    simp [liftApply, orderedDerivative]
  rw [h2]
  exact h1

/-- **Step 4 (generic): one pulse.** -/
theorem pulsePhysicalLift_quiet_start {Q : LiftOperatorData ι h D} {sX sZ : ℕ} {t₀ t₁ : ℝ}
    {N H : ℕ} {Cc : ℕ → ℕ → LiftCoeff ι h} (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc)
    {c ρ e εc t : ℝ} (hc : c ≠ 0) (hρ : ρ ≠ 0) (hs : c⁻¹ * t ∈ Set.Icc t₀ t₁)
    (hq : ∀ hh ≤ H, ∀ n, 1 ≤ n → ∀ m (α : DerivativeWord2 m) X z v u,
      Cc hh n m α (c⁻¹ * t) X z v u = 0)
    (chart label : ℝ → Vec 2 → Vec 2) (a : ℝ → Vec 2 → ∀ i, h i) (x : Vec 2) :
    pulsePhysicalLift c ρ e εc N H Cc chart label a t x = a t (chart t (label t x)) := by
  unfold pulsePhysicalLift diagSample
  beta_reduce
  rw [Finset.sum_eq_single 0]
  · rw [Finset.sum_eq_single 0]
    · rw [pow_zero, one_smul, gluedStart_liftApply_zero hseq hs]
      simp [mul_inv_cancel_left₀ hc, smul_inv_smul₀ hρ]
    · intro n _ hn
      rw [gluedStart_liftApply_apart hseq hq (Nat.zero_le _) (Or.inr hn), smul_zero]
    · intro h0
      exact absurd (Finset.mem_range.2 (Nat.succ_pos _)) h0
  · intro hh hhm hh0
    refine Finset.sum_eq_zero fun n _ => ?_
    rw [gluedStart_liftApply_apart hseq hq (Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm))
      (Or.inl hh0), smul_zero]
  · intro h0
    exact absurd (Finset.mem_range.2 (Nat.succ_pos _)) h0

end Generic

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- **Step 1: the positive coefficients vanish at the cell time of `t_i`, without the deadline**
(the proof of `weakSeqQuietZero_of`, which never used it). -/
theorem weakStart_quietZero (hplan : WeakPassageCommonOK plan) (hell : WeakPassageEllOK plan)
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (h : WeakComparisonInput r i) (k : ℤ) (hk : Odd k)
    (hstart : c.D.slotStart i k ≤ r.tq i)
    (hwin : r.tq i ≤ ((k : ℝ) + 61 / 48) * ocTau c.D.α c.D.q c.D.Λ i)
    (hseq : IsLiftSequence (weakCapData c i k hk) R.sX R.sZ
      (c.D.slotStart i k / c.D.cellScaleSq i)
      ((((k : ℝ) + 61 / 48) * ocTau c.D.α c.D.q c.D.Λ i) / c.D.cellScaleSq i) A.Nw (weakH A)
      (h.CcR i k)) :
    ∀ hh ≤ weakH A, ∀ n, 1 ≤ n → ∀ m (α : DerivativeWord2 m) X z v u,
      h.CcR i k hh n m α (r.tq i / c.D.cellScaleSq i) X z v u = 0 := by
  classical
  intro hh hhH n hn m α X' z v u
  obtain ⟨hΛ, -, hζ, hband⟩ := Comparison.weakPassageInstance_base c
  have hΛ1 : 1 ≤ c.D.Λ := by omega
  have hkap : 0 < c.D.kap i := weakData_kap_pos c.D hΛ1 hζ hband i
  have hcs : 0 < c.D.cellScaleSq i := weakData_cellScaleSq_pos c.D hΛ1 hζ hband i
  have hτ : 0 < ocTau c.D.α c.D.q c.D.Λ i := Construction.Stream.ocTau_pos hΛ1
  have hLge := ChildInert.ocL_ge_five c.D.α c.D.q hΛ1 i
  have hTP : ocTauP c.D.α c.D.q c.D.Λ i =
      (ocL c.D.α c.D.q c.D.Λ i : ℝ) * ocTau c.D.α c.D.q c.D.Λ i := by
    have h5 : (0 : ℝ) < ocL c.D.α c.D.q c.D.Λ i := by linarith
    unfold ocTauP ocTau
    field_simp
  obtain ⟨l, hl⟩ := (r.reduction.2.2.2 i hi hit).1
  have hcol : Set.Icc (r.tq i - (ocL c.D.α c.D.q c.D.Λ i : ℝ) * ocTau c.D.α c.D.q c.D.Λ i)
      (r.tq i + (ocL c.D.α c.D.q c.D.Λ i : ℝ) * ocTau c.D.α c.D.q c.D.Λ i) ⊆
      ocQuietTimes c.D.α c.D.q c.D.Λ c.D.ζ i := by
    have := CycleJointProofs.renewal_boundary_quiet_margin (α := c.D.α) (q := c.D.q) (m := i)
      hΛ1 c.D.ζ l
    rw [← hl, hTP] at this
    exact this
  have hss : c.D.slotStart i k = ((k : ℝ) - 61 / 48) * ocTau c.D.α c.D.q c.D.Λ i := rfl
  have hgeo := EntryTerminal.Ingredients.Recon.Seq.seq_geometry hτ hLge hwin
    (aM := r.tq i - (ocL c.D.α c.D.q c.D.Λ i : ℝ) * ocTau c.D.α c.D.q c.D.Λ i) (le_of_eq (by ring))
  have hpt : ∀ t ∈ Set.Icc (c.D.slotStart i k / c.D.cellScaleSq i) (r.tq i / c.D.cellScaleSq i),
      c.D.cellScaleSq i * t ∈ ocTrimmedQuietTimes c.D.α c.D.q c.D.Λ c.D.ζ i ∧
        c.D.cellScaleSq i * t ∈ ocPulseWindow c.D.α c.D.q c.D.Λ i k := by
    intro t ht
    have h1 : c.D.slotStart i k ≤ c.D.cellScaleSq i * t := by
      have := (div_le_iff₀ hcs).1 ht.1
      linarith
    have h2 : c.D.cellScaleSq i * t ≤ r.tq i := by
      have := (le_div_iff₀ hcs).1 ht.2
      linarith
    obtain ⟨hg1, -⟩ := hgeo _ ⟨by rw [← hss]; exact h1, h2⟩
    refine ⟨fun y hy => hcol (hg1 hy), ?_, h2.trans hwin⟩
    rw [hss] at h1; exact h1
  have hsC : c.D.slotStart i k / c.D.cellScaleSq i ≤ r.tq i / c.D.cellScaleSq i :=
    div_le_div_of_nonneg_right hstart hcs.le
  have hend : r.tq i / c.D.cellScaleSq i ≤
      (((k : ℝ) + 61 / 48) * ocTau c.D.α c.D.q c.D.Λ i) / c.D.cellScaleSq i :=
    div_le_div_of_nonneg_right hwin hcs.le
  have hellW := weakCap_ellipticity hell c i hi k hk
  refine EntryTerminal.Ingredients.Recon.r2c_quietZero_core (weakCapData c i k hk) R.sX R.sZ
    A.Nw (weakH A) _ _ _ (h.CcR i k) hseq hsC hend
    (fun t X'' a b => familyLiftData_metric_symmetric c.D i k _ _ _ t X'' a b)
    ⟨3 / 4, 5 / 4, by norm_num, fun t ht X'' ξ => hellW t ⟨ht.1, ht.2.trans hend⟩ X'' ξ⟩
    (fun t ht z => ?_) (fun t ht v' u' d γ hγ w X'' z z' => ?_) hh hhH n hn m α _ ⟨hsC, le_rfl⟩
    X' z v u
  · exact Residual.weakNativeQuietDrift hΛ1 hζ hkap hk
      (CycleComparison.ocTrimmedQuietTimes_subset_quiet hΛ1 c.D.ζ i (hpt t ht).1) z
  · have hγ' : γ ∈ liftEdges (c.D.cellScaleSq i) (c.D.eps (i - 1) / c.D.eps (i - 1))
        ((c.stage i).fam.fiber ⟨k, hk⟩ ((c.stage i).actual ⟨k, hk⟩)) v' u'
        (capOrder c.order_ge d) := hγ
    obtain ⟨γ₀, -, -, hc⟩ := CycleComparison.LiftSetting.mem_liftEdges_fiber hγ'
    rw [hc]
    exact Residual.weakNativeQuietFastIndependent hplan c hi.le hit ⟨k, hk⟩ _ v' u' γ₀ d.1 w
      (c.D.cellScaleSq i * t) ⟨(hpt t ht).1, (hpt t ht).2⟩ _ z z'

/-- **Step 4 (chart part): the flow chart and its inverse cancel.** -/
theorem weakStart_chart_label (c : WeakPassageInstance plan R) (i : ℕ) (hτ'' : 0 < ocTauPP c.D.α c.D.q c.D.Λ i)
    (k : ℤ) (s : ℝ) (x : Vec 2) :
    c.D.flowOf (i - 1) s (c.D.flowOf (i - 1) (c.D.slotAnchor i k) x s) (c.D.slotAnchor i k) = x := by
  have e1 : ocChart c.D.α c.D.q c.D.Λ i (c.D.Φ (i - 1)) (c.D.hΦ (i - 1))
      (ocPulseChartIndex c.D.α c.D.q c.D.Λ i k) =
        fun s' y => c.D.flowOf (i - 1) s' y (c.D.slotAnchor i k) := by
    funext s' y
    unfold ocChart OCData.flowOf OCData.slotAnchor
    rw [ocLabel_eq_ocPulseChartIndex c.D.α c.D.q c.D.Λ i k hτ'']
  have e2 : ocChartInv c.D.α c.D.q c.D.Λ i (c.D.Φ (i - 1)) (c.D.hΦ (i - 1))
      (ocPulseChartIndex c.D.α c.D.q c.D.Λ i k) =
        fun s' y => c.D.flowOf (i - 1) (c.D.slotAnchor i k) y s' := by
    funext s' y
    unfold ocChartInv OCData.flowOf OCData.slotAnchor
    rw [ocLabel_eq_ocPulseChartIndex c.D.α c.D.q c.D.Λ i k hτ'']
  have := AVRegularity.CycleComparison.Charts.ocChart_ocChartInv c.D.α c.D.q c.D.Λ i
    (c.D.Φ (i - 1)) (c.D.hΦ (i - 1)) (ocPulseChartIndex c.D.α c.D.q c.D.Λ i k) s x
  rw [e1, e2] at this
  exact this

/-- **At the time `t_i` the glued lift of a passage is the identity**, on every field. -/
def WeakGluedLiftStartStatement (plan : WeakPassagePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ), c.M < i → i ≤ c.M + A.Jw →
    ∀ (h : WeakComparisonInput r i) (g : CompIn (c.stage i).comps → Vec 2 → ℝ)
      (v : CompIn (c.stage i).comps) (x : Vec 2),
      weakGluedLift i A.Nw (A.Jw * A.Rw) (c.stage i) (h.CcR i) (r.tq i) g v x = g v x

/-- **The glued lift at the start, proved**, under the sequence plan condition. -/
theorem weakGluedLiftStart (hplan : WeakSeqPlanOK plan) : WeakGluedLiftStartStatement plan := by
  classical
  intro B A R c r i hi hit h g v x
  obtain ⟨hΛ, -, hζ, hband⟩ := Comparison.weakPassageInstance_base c
  have hΛ1 : 1 ≤ c.D.Λ := by omega
  have hcs : 0 < c.D.cellScaleSq i := weakData_cellScaleSq_pos c.D hΛ1 hζ hband i
  have hτ : 0 < ocTau c.D.α c.D.q c.D.Λ i := Construction.Stream.ocTau_pos hΛ1
  have hτ'' : 0 < ocTauPP c.D.α c.D.q c.D.Λ i := Construction.Stream.ocTauPP_pos hΛ1
  have hρ : c.D.eps (i - 1) ≠ 0 := by
    unfold OCData.eps
    exact (Construction.Stream.ocEpsilon_pos hΛ1).ne'
  have hcap := weakSeqCap_of c r i hi hit h
  unfold weakGluedLift gluedLift
  have hterm : ∀ k ∈ ocObsPulses c.D.α c.D.q c.D.Λ i (r.tq i) (r.tq i),
      ocCutoff c.D.α c.D.q c.D.Λ i k (r.tq i) •
        pulsePhysicalLift (c.D.cellScaleSq i) (c.D.eps (i - 1)) (c.D.eps i)
          (c.D.eps i / c.D.eps (i - 1)) A.Nw (A.Jw * A.Rw) (h.CcR i k)
          (fun s' y => c.D.flowOf (i - 1) s' y (c.D.slotAnchor i k))
          (fun s' y => c.D.flowOf (i - 1) (c.D.slotAnchor i k) y s')
          (fun _ y w => g w y) (r.tq i) x =
      ocCutoff c.D.α c.D.q c.D.Λ i k (r.tq i) • (fun w => g w x) := by
    intro k hk
    have hodd : Odd k := (Finset.mem_filter.1 hk).2.1
    by_cases hw : ocCutoff c.D.α c.D.q c.D.Λ i k (r.tq i) = 0
    · rw [hw, zero_smul, zero_smul]
    · have hwin := GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hw
      have hwin' : ((k : ℝ) - 61 / 48) * ocTau c.D.α c.D.q c.D.Λ i ≤ r.tq i ∧
          r.tq i ≤ ((k : ℝ) + 61 / 48) * ocTau c.D.α c.D.q c.D.Λ i := hwin
      have hstart : c.D.slotStart i k ≤ r.tq i := hwin'.1
      have hq := weakStart_quietZero hplan.1 hplan.2 c r i hi hit h k hodd hstart hwin'.2
        (hcap k hodd)
      have hs : (c.D.cellScaleSq i)⁻¹ * r.tq i ∈ Set.Icc
          (c.D.slotStart i k / c.D.cellScaleSq i)
          ((((k : ℝ) + 61 / 48) * ocTau c.D.α c.D.q c.D.Λ i) / c.D.cellScaleSq i) := by
        rw [inv_mul_eq_div]
        exact ⟨div_le_div_of_nonneg_right hstart hcs.le,
          div_le_div_of_nonneg_right hwin'.2 hcs.le⟩
      rw [pulsePhysicalLift_quiet_start (hcap k hodd) hcs.ne' hρ hs
        (by rw [inv_mul_eq_div]; exact hq)]
      simp only [weakStart_chart_label c i hτ'']
  rw [Finset.sum_congr rfl hterm]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_mul, CascadeInvariants.sum_ocCutoff_eq_one hτ _ (fun k hk => (Finset.mem_filter.1 hk).2.1),
    one_mul]
  intro k hodd hne
  exact mem_obsPulses_time c.D.α c.D.q c.D.Λ i hτ hodd
    (GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hne)

end AVRegularity.Providers.WeakGen.Window
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Reconstruction AVRegularity.CycleComparison.Lift
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.ChartTransport
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.EntryWeakProofs AVRegularity.Construction.Residual.Presentation
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Window

/-! **The partition hypothesis of the weak window from the partition bound**.

`weakWindowPartition_of_recon`: `weakReconPartition` (on `[t_i, a + T₀]`, with the
cutoffs as weights and any field that is smooth, periodic and jointly measurable on the window)
gives `WeakWindowPartitionAt` (the hypothesis `hPB` of the physical lift at the weak window),
at `K_max = (orders R).Kmax`, the order `weakReconPartitionOrder (orders R)` and the factor
`weakReconPartitionFactor (orders R) c r i`. Three facts:

* the end of the window is `a + T₀` (`weakWindow_end`; the statement at a variable end, then
  substituted);
* on the observed pulses, which are odd, the weights of the window's family are the cutoffs
  (`weakWindow_partitionField`, from `weakStage_weight`);
* a Galerkin approximant `coarseTraj n W` is smooth and periodic, and jointly measurable on the
  window when its coefficients are continuous there (`coarseTraj_measurable_ite`; the
  coefficients of a coarse defect are primitives, `coarseCoeff_prim`).

The degenerate cases are included: no observed pulse gives `0 ≤ …` on both sides of the adapter (the
same sums); `W = 0` gives `coarseTraj n W = 0`; `n = 0` is the approximant of the mean modes
only. -/

open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Residual

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- **A Galerkin approximant cut off outside a window is jointly measurable** when its
coefficients are continuous on the window. -/
theorem coarseTraj_measurable_ite {a b : ℝ} (n : ℕ) {K : ℕ} (W : ∀ v, ℝ → TorusHk K (h v))
    (hcc : ∀ r' : CoupledFourierModeIndex (h := h) n,
      ContinuousOn (coarseCoeff n W r') (Set.Icc a b)) :
    Measurable (fun z : ℝ × Vec 2 =>
      if z.1 ∈ Set.Icc a b then coarseTraj n W z.1 z.2 else 0) := by
  have hc : ∀ r' : CoupledFourierModeIndex (h := h) n,
      Measurable (fun t : ℝ => if t ∈ Set.Icc a b then coarseCoeff n W r' t else 0) := fun r' =>
    (hcc r').measurable_piecewise (g := fun _ => (0 : ℝ)) continuousOn_const measurableSet_Icc
  have heq : (fun z : ℝ × Vec 2 => if z.1 ∈ Set.Icc a b then coarseTraj n W z.1 z.2 else 0) =
      fun z => ∑ r' : CoupledFourierModeIndex (h := h) n,
        (if z.1 ∈ Set.Icc a b then coarseCoeff n W r' z.1 else 0) • coarseMode n r' z.2 := by
    funext z
    by_cases hz : z.1 ∈ Set.Icc a b
    · simp only [hz, ↓reduceIte]
      rfl
    · simp only [hz, ↓reduceIte, zero_smul, Finset.sum_const_zero]
  rw [heq]
  exact Finset.measurable_sum _ fun r' _ => ((hc r').comp measurable_fst).smul
    ((coarseMode_contDiff n r').continuous.measurable.comp measurable_snd)

end Generic

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- **The partition sum of the window is `weakReconPartitionField`**: on the observed
pulses the weights of the window's family are the cutoffs. -/
theorem weakWindow_partitionField (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ)
    (hi : c.M < i) (hit : i ≤ c.M + A.Jw)
    (hw : ∀ (p : OddSlot) (s : ℝ),
      (c.stage i).fam.weight p s = ocCutoff c.D.α c.D.q c.D.Λ i p.1 s)
    (Cc : ℤ → ℕ → ℕ → LiftCoeff (CompIn (c.stage i).comps) (fun v => ScalarH v.1.root))
    (f : WeakField (c.stage i)) (t : ℝ) :
    (fun x' => ∑ k ∈ ocObsPulses c.D.α c.D.q c.D.Λ i (r.tq i) (r.a + A.T₀),
      deriv ((weakWindowFamily c i hi hit).weight (oddSlotOf k)) t •
        pulsePhysicalLift (ocEll c.D.q c.D.Λ i (c.D.κ c.M) ^ 2)
          (ocEpsilon c.D.q c.D.Λ (i - 1)) (ocEpsilon c.D.q c.D.Λ i)
          (ocDStar c.D.q c.D.Λ i (c.D.κ c.M) (c.D.κ c.M) / ocEpsilon c.D.q c.D.Λ (i - 1))
          A.Nw (weakH A) (Cc k)
          (ocChart c.D.α c.D.q c.D.Λ i (c.D.Φ (i - 1)) (c.D.hΦ (i - 1))
            (ocPulseChartIndex c.D.α c.D.q c.D.Λ i k))
          (ocChartInv c.D.α c.D.q c.D.Λ i (c.D.Φ (i - 1)) (c.D.hΦ (i - 1))
            (ocPulseChartIndex c.D.α c.D.q c.D.Λ i k)) f t x') =
      weakReconPartitionField c r i Cc f t := by
  funext x'
  unfold weakReconPartitionField
  refine Finset.sum_congr rfl fun k hk => ?_
  have hodd := CycleComparison.LiftSetting.obsPulse_odd hk
  have hwt : (weakWindowFamily c i hi hit).weight (oddSlotOf k) =
      ocCutoff c.D.α c.D.q c.D.Λ i k := by
    funext s
    rw [oddSlotOf_of_odd hodd]
    exact hw ⟨k, hodd⟩ s
  rw [hwt]
  rfl

/-- **`hPB` at a variable end `t_f = a + T₀`** (the end is substituted before anything else). -/
theorem weakWindowPartition_of_recon_end
    (orders : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B},
      WeakPassageRequest A → WeakReconPartitionOrders A)
    (hok : WeakReconPartitionPlanOK plan orders)
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (h : WeakComparisonInput r i)
    (hw : ∀ (p : OddSlot) (s : ℝ),
      (c.stage i).fam.weight p s = ocCutoff c.D.α c.D.q c.D.Λ i p.1 s)
    {rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ ocEpsilon c.D.q c.D.Λ i) {K' : ℕ}
    (W : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk K' (ScalarH v.1.root))
    {tf : ℝ} (htf : tf = r.a + A.T₀)
    (hcc : ∀ n (r' : CoupledFourierModeIndex
        (h := fun v : CompIn (c.stage i).comps => ScalarH v.1.root) n),
      ContinuousOn (coarseCoeff n W r') (Set.Icc (r.tq i) tf)) (n : ℕ) :
    ∫⁻ t in Set.Icc (r.tq i) tf, (∑ j ∈ Finset.range ((orders R).Kmax + 1),
      ∑ w' : DerivativeWord2 j,
        scalInt (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
          (fun x => rs ^ j • orderedDerivative w' (fun x' =>
            ∑ k ∈ ocObsPulses c.D.α c.D.q c.D.Λ i (r.tq i) tf,
              deriv ((weakWindowFamily c i hi hit).weight (oddSlotOf k)) t •
                pulsePhysicalLift (ocEll c.D.q c.D.Λ i (c.D.κ c.M) ^ 2)
                  (ocEpsilon c.D.q c.D.Λ (i - 1)) (ocEpsilon c.D.q c.D.Λ i)
                  (ocDStar c.D.q c.D.Λ i (c.D.κ c.M) (c.D.κ c.M) /
                    ocEpsilon c.D.q c.D.Λ (i - 1)) A.Nw (weakH A) (h.CcR i k)
                  (ocChart c.D.α c.D.q c.D.Λ i (c.D.Φ (i - 1)) (c.D.hΦ (i - 1))
                    (ocPulseChartIndex c.D.α c.D.q c.D.Λ i k))
                  (ocChartInv c.D.α c.D.q c.D.Λ i (c.D.Φ (i - 1)) (c.D.hΦ (i - 1))
                    (ocPulseChartIndex c.D.α c.D.q c.D.Λ i k))
                  (coarseTraj n W) t x') x)) ^ (1 / 2 : ℝ) ≤
    ENNReal.ofReal (weakReconPartitionFactor (orders R) c r i) *
      classicalStrongEnergy (ocEpsilon c.D.q c.D.Λ (i - 1)) (c.D.κ c.M)
        (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
        (Set.Icc (r.tq i) tf) (weakReconPartitionOrder (orders R)) (coarseTraj n W) := by
  subst htf
  have key := weakReconPartition plan orders hok c r i hi hit R.sX R.sZ (h.CcR i)
    (h.lifts i hi hit) rs hrs hrse (coarseTraj n W)
    (fun t _ => (coarseTraj_contDiff n W t).of_le (by exact_mod_cast le_top))
    (fun t _ => coarseTraj_periodic n W t) (coarseTraj_measurable_ite n W (hcc n))
  refine le_of_eq_of_le (lintegral_congr fun t => ?_) key
  rw [weakWindow_partitionField c r i hi hit hw (h.CcR i) (coarseTraj n W) t]

/-- **`hPB` of the physical lift at the weak window, from the partition price bound.** -/
theorem weakWindowPartition_of_recon
    (orders : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B},
      WeakPassageRequest A → WeakReconPartitionOrders A)
    (hok : WeakReconPartitionPlanOK plan orders)
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (h : WeakComparisonInput r i)
    (hw : ∀ (p : OddSlot) (s : ℝ),
      (c.stage i).fam.weight p s = ocCutoff c.D.α c.D.q c.D.Λ i p.1 s)
    {rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ ocEpsilon c.D.q c.D.Λ i) {K' : ℕ}
    (W : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk K' (ScalarH v.1.root))
    (hcc : ∀ n (r' : CoupledFourierModeIndex
        (h := fun v : CompIn (c.stage i).comps => ScalarH v.1.root) n),
      ContinuousOn (coarseCoeff n W r') (Set.Icc (r.tq i) (r.tq i + wTobs c r i))) :
    WeakWindowPartitionAt c r i hi hit h (orders R).Kmax (weakReconPartitionOrder (orders R)) rs
      (weakReconPartitionFactor (orders R) c r i) W :=
  fun n => weakWindowPartition_of_recon_end orders hok c r i hi hit h hw hrs hrse W
    (weakWindow_end c r i) hcc n

end AVRegularity.Providers.WeakGen.Window
end
end
end
