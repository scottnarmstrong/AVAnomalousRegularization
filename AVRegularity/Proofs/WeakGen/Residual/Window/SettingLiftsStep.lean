-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.WeakGen.Residual.Window.LiftedOfOutput
public import AVRegularity.Proofs.Intermediate.CycleComparison.CycleLiftIdentity
import AVRegularity.EntryTerminal.Ingredients.Recon.R2Core.Quiet
import AVRegularity.CycleJoint.ActivePieceDimensionalSmooth
public import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
import AVRegularity.Construction.ChildInert.Center
import AVRegularity.CycleComparison.LiftSetting.Main
import AVRegularity.CycleReference.ChartTestTransport
import AVRegularity.Families.ActualFamily.MeasurableOfCertified
import AVRegularity.Proofs.QuietAtlas.SummedTransition
import AVRegularity.Proofs.WeakGen.Comparison.RowCoefficients
import AVRegularity.EntryTerminal.Ingredients.Recon.Setting.Main

section
section
section
/-! **The lift settings and the grading of the window: the split.**

`WeakSettingStep` is split into

* the **lifts** (`WeakLiftsStep`: the slot lifts `weakSlotLiftAt_planOK`, the change of cap,
  the transfer to the clipped window, the uniform price), at the NAMED constants
  `CG, Cw` = the fields of a slot-lift parameter set `Pw`, `Ca = weakSettingCa Pw qs qf`,
  `Sb = Pw.S`, `qs = weakSettingQs A k₀`, `qf = weakSettingQf A k₀`;
* the **grading** (`weakSetting_grading`, proved here): from the lifts and the lift sequences
  by `Providers.cycle_lift_grading`, at `Cg = weakGradeConst A k₀ CG Cw Ca`.

`weakSettingStep_of_parts` is the compiled assembly: the lifts and the lift sequences give `WeakSettingStep` at
these constants. `k₀` is a free parameter; the slot-lift parameters `Pw` are an argument (the final
theorem takes `Pw = weakSlotLiftParams A Lr R.sX R.sZ`).

The degenerate cases are included: no observed pulse (both conjuncts empty); `Ca` is a finite sum of
absolute values, so it is `0` for the default slot-lift parameters. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Reconstruction AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs AVRegularity.Construction.Residual.Presentation

namespace AVRegularity.Providers.WeakGen.Window

open WeakEntryProofs WeakEntryProofs.Assembly Finite.WeakLift

/-! ### Named constants -/

/-- The slow cap-reserve of the window, `q_s = K_lift + 4(H+1)(N_w + D_w)^2`. -/
abbrev weakSettingQs {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) (k₀ : ℕ) : ℕ :=
  weakKlift A k₀ + 4 * (weakH A + 1) * (A.Nw + weakDw A) ^ 2

/-- The fast reserve of the window, `q_f = max L_lift (L_lift+2) + H D_w + 2N_w + 2D_w`. -/
abbrev weakSettingQf {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) (k₀ : ℕ) : ℕ :=
  max (weakLlift A k₀) (weakLlift A k₀ + 2) + weakH A * weakDw A + 2 * A.Nw + 2 * weakDw A

/-- The jet constant `C_a`: the finite sum of `|C_j r q|` over `r ≤ q_s`, `q ≤ q_f`. -/
def weakSettingCa {N H U : ℕ} (P : WeakPositiveParameters N H U) (qs qf : ℕ) : ℝ :=
  ∑ r ∈ Finset.range (qs + 1), ∑ q ∈ Finset.range (qf + 1), |P.Cj r q|

theorem le_weakSettingCa {N H U : ℕ} (P : WeakPositiveParameters N H U) (qs qf : ℕ) {r : ℕ}
    (hr : r ≤ qs) {q : ℕ} (hq : q ≤ qf) : P.Cj r q ≤ weakSettingCa P qs qf := by
  refine (le_abs_self _).trans ?_
  refine le_trans ?_ (Finset.single_le_sum (f := fun r => ∑ q ∈ Finset.range (qf + 1), |P.Cj r q|)
    (fun r _ => Finset.sum_nonneg fun q _ => abs_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hr)))
  exact Finset.single_le_sum (f := fun q => |P.Cj r q|) (fun q _ => abs_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hq))

/-- The grading constant `C_g` of `Providers.cycle_lift_grading` at the orders of the window and
the constants `C_G, C_w, C_a`. -/
def weakGradeConst {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) (k₀ : ℕ)
    (CGl Cw : ℕ → ℝ) (Ca : ℝ) : ℝ :=
  Classical.choose (Providers.cycle_lift_grading.{0, 0} A.Nw (weakKlift A k₀) (weakLlift A k₀)
    (weakLlift A k₀) (weakDw A) (weakH A) CGl Cw (fun _ _ => Ca))

theorem weakGradeConst_nonneg {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) (k₀ : ℕ)
    (CGl Cw : ℕ → ℝ) (Ca : ℝ) : 0 ≤ weakGradeConst A k₀ CGl Cw Ca :=
  (Classical.choose_spec (Providers.cycle_lift_grading.{0, 0} A.Nw (weakKlift A k₀)
    (weakLlift A k₀) (weakLlift A k₀) (weakDw A) (weakH A) CGl Cw (fun _ _ => Ca))).1

section Parts

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}
variable (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ) (hi : c.M < i)
  (hit : i ≤ c.M + A.Jw)

/-! ### The lifts (open) -/

/-- The lift settings of the observed pulses on their clipped windows at the orders of the
window (the first conjunct of `WeakSettingBody`). -/
def WeakSettingLifts (k₀ : ℕ) (qs qf : ℕ) (CGl Cw : ℕ → ℝ) (Ca Sb : ℝ)
    (bM : CompIn (c.stage i).comps → CompIn (c.stage i).comps → ℝ) : Prop :=
  ∀ k ∈ ocObsPulses c.D.α c.D.q c.D.Λ i (r.tq i) (r.tq i + wTobs c r i),
    IsLiftSetting (wLiftData c i hi hit k) (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1)
      (wSeqStart c r i k) (wSeqEnd c r i k) (ocEpsilon c.D.q c.D.Λ i) (c.D.κ c.M) (c.D.κ c.M)
      (ocEpsilon c.D.q c.D.Λ (i - 1)) (ocEpsilon c.D.q c.D.Λ (i - 1))
      (ocEll c.D.q c.D.Λ i (c.D.κ c.M)) (ocDStar c.D.q c.D.Λ i (c.D.κ c.M) (c.D.κ c.M))
      (ocDStar c.D.q c.D.Λ i (c.D.κ c.M) (c.D.κ c.M) / ocEpsilon c.D.q c.D.Λ (i - 1))
      (ocEpsilon c.D.q c.D.Λ (i - 1) / ocEpsilon c.D.q c.D.Λ (i - 1))
      (pulseParallel k) (pulseShearProfile c.D.α c.D.q c.D.Λ i c.D.ζ (c.D.κ c.M) k)
      (weakH A) A.Nw (weakKlift A k₀) (weakLlift A k₀) (weakLlift A k₀) qs qf CGl Cw
      (fun _ _ => Ca) bM Sb

/-- **The lift settings**: the lift settings under the deadline, with one price `bM` for all the
pulses. Parts: (1) per pulse, from the slot lift of `weakSlotLiftAt_planOK`, the
change of cap `isLiftSetting_changeCap`, the transfer `isLiftSetting_transfer` to the clipped
window and `isLiftSetting_congr_params` (price `b_k` of the slot lift); (2) one price for all the
pulses (`recordMajorant` of the window family, `weak_source_fixed_cap_envelope`). -/
def WeakLiftsStep (k₀ : ℕ) (CGl Cw : ℕ → ℝ) (Ca Sb : ℝ) : Prop :=
  r.tq i < r.a + A.T₀ → ∃ bM : CompIn (c.stage i).comps → CompIn (c.stage i).comps → ℝ,
    WeakSettingLifts c r i hi hit k₀ (weakSettingQs A k₀) (weakSettingQf A k₀) CGl Cw Ca Sb bM

/-! ### The grading (proved) -/

/-- **The grading of the window**, from the lifts and the lift sequences. -/
theorem weakSetting_grading (h : WeakComparisonInput r i) (k₀ : ℕ) (CGl Cw : ℕ → ℝ) (Ca Sb : ℝ)
    (bM : CompIn (c.stage i).comps → CompIn (c.stage i).comps → ℝ)
    (hl : WeakSettingLifts c r i hi hit k₀ (weakSettingQs A k₀) (weakSettingQf A k₀) CGl Cw Ca Sb
      bM)
    (hseq : ∀ k ∈ ocObsPulses c.D.α c.D.q c.D.Λ i (r.tq i) (r.tq i + wTobs c r i),
      IsLiftSequence (wLiftData c i hi hit k) (weakKlift A k₀ + weakDw A + 2)
        (max (weakLlift A k₀ + 1) (weakLlift A k₀ + 2))
        (wSeqStart c r i k) (wSeqEnd c r i k) A.Nw (weakH A) (h.CcR i k)) :
    ∀ k ∈ ocObsPulses c.D.α c.D.q c.D.Λ i (r.tq i) (r.tq i + wTobs c r i), ∀ hh, hh ≤ weakH A →
      ∀ n, 1 ≤ n → n ≤ A.Nw → ∀ m'', 1 ≤ m'' → m'' ≤ n →
        ∀ j, j ≤ weakAcl + 2 + weakKmax A k₀ →
        schurEnergyJet (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1)
            (Set.Icc (wSeqStart c r i k) (wSeqEnd c r i k)) (weakLlift A k₀) j
            (h.CcR i k hh n m'') ≤
          ENNReal.ofReal (weakGradeConst A k₀ CGl Cw Ca * Sb ^ hh *
            (ocEpsilon c.D.q c.D.Λ (i - 1) / ocEpsilon c.D.q c.D.Λ (i - 1)) ^ (n - m'' + j)) := by
  intro k hk hh hhH n hn1 hnN m hm1 hmn j hj
  have hg := (Classical.choose_spec (Providers.cycle_lift_grading.{0, 0} A.Nw (weakKlift A k₀)
    (weakLlift A k₀) (weakLlift A k₀) (weakDw A) (weakH A) CGl Cw (fun _ _ => Ca))).2
    (wLiftData c i hi hit k) (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1) _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ (hl k hk) (h.CcR i k) (hseq k hk) hh hhH n hn1 hnN m hm1 hmn j
    (by simp only [weakAcl, weakKmax, weakKlift] at hj ⊢; omega)
  exact hg.1

end Parts

/-! ### The compiled assembly -/

section Assembly

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}
variable (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ) (hi : c.M < i)
  (hit : i ≤ c.M + A.Jw)

/-- **The lift settings and the grading from their parts**: the lifts and the lift sequences (`WeakSeqStep`), at the named constants
`CG, Cw` the fields of the slot-lift parameters `Pw`, `Ca = weakSettingCa Pw qs qf`, `Sb = Pw.S`,
`Cg = weakGradeConst …`, with the floors of the lift sequences on the lift orders. -/
theorem weakSettingStep_of_parts (h : WeakComparisonInput r i) (k₀ : ℕ) {Lr : ℕ}
    (Pw : WeakPositiveParameters A.Nw (A.Jw * A.Rw) (Lr + 3))
    (hX : weakKlift A k₀ + weakDw A + 2 ≤ R.sX)
    (hZ : max (weakLlift A k₀ + 1) (weakLlift A k₀ + 2) ≤ R.sZ)
    (hseq : WeakSeqStep c r i hi hit h k₀)
    (hlifts : WeakLiftsStep c r i hi hit k₀ Pw.CG Pw.Cw
      (weakSettingCa Pw (weakSettingQs A k₀) (weakSettingQf A k₀)) Pw.S) :
    WeakSettingStep c r i hi hit h k₀ Pw.CG Pw.Cw
      (weakSettingCa Pw (weakSettingQs A k₀) (weakSettingQf A k₀)) Pw.S
      (weakGradeConst A k₀ Pw.CG Pw.Cw (weakSettingCa Pw (weakSettingQs A k₀)
        (weakSettingQf A k₀))) := by
  intro hdl
  obtain ⟨bM, hl⟩ := hlifts hdl
  exact ⟨weakSettingQs A k₀, weakSettingQf A k₀, bM, hl,
    weakSetting_grading c r i hi hit h k₀ _ _ _ _ bM hl (hseq hdl hX hZ)⟩

end Assembly

end AVRegularity.Providers.WeakGen.Window
end
end

section
/-! **The slot lift's setting at the cap and the orders of the window.**

A `WeakPositiveSlot` carries a lift setting `Q` at its own cap `cap ≤ capMax` and the slot-lift
orders. `weakSlot_cappedSetting` turns it, by `isLiftSetting_changeCap`, into a setting of
`extendData Q` at the cap `D_w` and the orders `(K_lift, L_lift, L_lift)`, under the order floors
`weakSettingQs ≤ slowOrder + 4(H+1)(N+2)^2` and the fast analogue (`WeakOrderFloors`).

The degenerate cases are included: `cap = D_w` (the extension is the identity on edges); `cap = 2`
(the floors are needed in this case). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Lift AVRegularity.EntryWeakProofs
open AVRegularity.Construction.Residual.Presentation

namespace AVRegularity.Providers.WeakGen.Window

open WeakEntryProofs WeakEntryProofs.Assembly Finite.WeakLift
  AVRegularity.Providers.WeakGen.Residual

/-- The order floors of the slot-lift parameters against the window: the reserves of the window at
the cap `D_w` are below those of the slot lift at the smallest cap. -/
def WeakOrderFloors {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) (k₀ : ℕ) {Lr : ℕ}
    (Pw : WeakPositiveParameters A.Nw (weakH A) (Lr + 3)) : Prop :=
  weakSettingQs A k₀ ≤ Pw.slowOrder + 4 * (weakH A + 1) * (A.Nw + 2) ^ 2 ∧
  weakSettingQf A k₀ ≤ max Pw.fastOrder (Pw.fastOrder + 2) + weakH A * 2 + 2 * A.Nw + 2 * 2 ∧
  weakDw A = Pw.capMax

/-- **The slot lift's setting at the cap and the orders of the window.** -/
theorem weakSlot_cappedSetting {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B)
    (k₀ : ℕ) {Lr : ℕ} (Pw : WeakPositiveParameters A.Nw (weakH A) (Lr + 3))
    (hfl : WeakOrderFloors A k₀ Pw)
    {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} (i : ℕ) (G : GenStage D ScalarH Dm bw j₀)
    (π : CompIn G.comps → ℝ) (slot : OddSlot) {ρ : ℝ}
    (S : WeakPositiveSlot Pw i G π slot ρ) :
    IsLiftSetting (extendData (S.cap_le.trans hfl.2.2.ge) S.Q) π
      (weakSlotLeft D i slot.1) (weakSlotRight D i slot.1)
      (D.eps i) (D.kap i) (D.kap (i - 1)) ρ
      (D.eps (i - 1)) (D.eps i / Real.sqrt (D.kap i))
      (ocDStar D.q D.Λ i (D.kap i) (D.kap (i - 1)))
      (ocDStar D.q D.Λ i (D.kap i) (D.kap (i - 1)) / ρ) (ρ / D.eps (i - 1))
      (pulseParallel slot.1) (pulseShearProfile D.α D.q D.Λ i D.ζ (D.kap i) slot.1)
      (weakH A) A.Nw (weakKlift A k₀) (weakLlift A k₀) (weakLlift A k₀)
      (weakSettingQs A k₀) (weakSettingQf A k₀) Pw.CG Pw.Cw Pw.Cj S.price Pw.S := by
  have hcap := S.cap_ge
  have hD : S.cap ≤ weakDw A := S.cap_le.trans hfl.2.2.ge
  refine isLiftSetting_changeCap hD S.setting rfl rfl ?_ ?_
  · refine hfl.1.trans ?_
    have : (A.Nw + 2) ^ 2 ≤ (A.Nw + S.cap) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : 4 * (weakH A + 1) * (A.Nw + 2) ^ 2 ≤ 4 * (weakH A + 1) * (A.Nw + S.cap) ^ 2 :=
      Nat.mul_le_mul_left _ this
    omega
  · refine hfl.2.1.trans ?_
    have : weakH A * 2 ≤ weakH A * S.cap := Nat.mul_le_mul_left _ hcap
    omega
end AVRegularity.Providers.WeakGen.Window
end
end

section
/-! **The window's lift data against the native data of a slot lift.**

The metric, the drift and `η` of `wLiftData c i hi hit k` are those of the native lift data
`weakPositiveNativeData i (c.stage i) ⟨k, hk⟩` of the slot lift at `ρ = ε_{i-1}` (the data the
transfer `isLiftSetting_transfer` needs besides the edges). Model: the same step at terminal entry
(namespace `EntryTerminal.Ingredients.Recon.Setting`).

The degenerate cases are included: `k` odd; at the root `i = M + J_w` the stage has no identity and
the data are those of the empty family. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Lift AVRegularity.EntryWeakProofs
open AVRegularity.Construction.Residual.Presentation

namespace AVRegularity.Providers.WeakGen.Window

open WeakEntryProofs WeakEntryProofs.Assembly Finite.WeakLift

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}
variable (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw)

include hi

theorem wSetting_kap : c.D.kap i = c.D.κ c.M := by
  rw [weakData_kap_terminal c.D i (by rw [c.terminal]; exact hi.le), c.terminal]

theorem wSetting_kap_pred : c.D.kap (i - 1) = c.D.κ c.M := by
  rw [weakData_kap_terminal c.D (i - 1) (by rw [c.terminal]; omega), c.terminal]

theorem wSetting_cell (hκM : 0 < c.D.κ c.M) :
    ocEll c.D.q c.D.Λ i (c.D.κ c.M) ^ 2 = c.D.cellScaleSq i := by
  rw [CycleReference.ocEll_sq_eq hκM]
  unfold OCData.cellScaleSq OCData.eps
  rw [wSetting_kap c i hi]

/-- The metric of the window's lift data is the native metric of the slot lift. -/
theorem wSetting_metric (hΛ1 : 1 ≤ c.D.Λ) (hκM : 0 < c.D.κ c.M) {k : ℤ} (hk : Odd k) :
    (wLiftData c i hi hit k).G =
      (weakPositiveNativeData i (c.stage i) (⟨k, hk⟩ : OddSlot)).G := by
  have hτ : 0 < ocTauPP c.D.α c.D.q c.D.Λ i := Construction.Stream.ocTauPP_pos hΛ1
  funext t X' i' j
  show _ = (familyLiftData c.D i k (nativeChain i k) (c.D.eps (i - 1)) _).G t X' i' j
  rw [EntryWeakProofs.native_familyLiftData_metric c.D i (by omega) k _ _ t X']
  show ocMaterialMetric c.D.α c.D.q c.D.Λ i (c.D.Φ (i - 1)) (c.D.hΦ (i - 1))
      (ocPulseChartIndex c.D.α c.D.q c.D.Λ i k) (ocEll c.D.q c.D.Λ i (c.D.κ c.M) ^ 2 * t)
      (ocEpsilon c.D.q c.D.Λ (i - 1) • X') i' j = _
  unfold ocMaterialMetric ocChart OCData.flowOf OCData.slotAnchor
  rw [wSetting_cell c i hi hκM, ocLabel_eq_ocPulseChartIndex c.D.α c.D.q c.D.Λ i k hτ]
  rfl

/-- The drift of the window's lift data is the native drift of the slot lift. -/
theorem wSetting_drift {k : ℤ} (hk : Odd k) :
    (wLiftData c i hi hit k).v =
      (weakPositiveNativeData i (c.stage i) (⟨k, hk⟩ : OddSlot)).v := by
  show _ = ocPulseCellDrift c.D.α c.D.q c.D.Λ c.D.ζ i (c.D.kap i) k
  rw [wSetting_kap c i hi]
  rfl

/-- `η` of the window's lift data is the native `η` of the slot lift. -/
theorem wSetting_eta {k : ℤ} (hk : Odd k) :
    (wLiftData c i hi hit k).η =
      (weakPositiveNativeData i (c.stage i) (⟨k, hk⟩ : OddSlot)).η := by
  show c.D.κ c.M / c.D.κ c.M = c.D.kap i / c.D.kap (i - 1)
  rw [wSetting_kap c i hi, wSetting_kap_pred c i hi]

end AVRegularity.Providers.WeakGen.Window
end
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.Providers.WeakGen.Window

/-! **The order floors of the window against the slot-lift parameters.**

For the slot-lift parameters `weakSlotLiftParams A Lr sX sZ` (slow order `Lr + 3 + (N_w + D_slot)`,
fast order `Lr + 3`, `capMax = D_slot = max 2 (1 + J_wN_w)`), `WeakOrderFloors` holds as soon as
`Lr` is at least the named floor `weakWindowLrFloor A k₀ = q_s + q_f + J_wN_w` and `1 ≤ J_wN_w`
(so that `D_w = D_slot`).

The degenerate cases are included: `J_wN_w = 0` makes `D_w = 1 ≠ 2 = D_slot`, which is why
`1 ≤ J_wN_w` is a hypothesis; at `Lr` exactly the floor both order inequalities have slack `3`. -/

open WeakEntryProofs WeakEntryProofs.Assembly Finite.WeakLift
  AVRegularity.Providers.WeakGen.Residual

/-- **Plan condition (floor on `Lr R`).** `q_s + q_f + J_wN_w ≤ Lr R`. -/
def weakWindowLrFloor {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) (k₀ : ℕ) : ℕ :=
  weakSettingQs A k₀ + weakSettingQf A k₀ + A.Jw * A.Nw

theorem weakWindowLrFloor_ge_JN {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B)
    (k₀ : ℕ) : A.Jw * A.Nw ≤ weakWindowLrFloor A k₀ := by
  unfold weakWindowLrFloor; omega

/-- The order floors of the window for any slot-lift parameters. -/
theorem weakOrderFloors_of_orders {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B)
    (k₀ Lr : ℕ) (Pw : WeakPositiveParameters A.Nw (weakH A) (Lr + 3))
    (h1 : Pw.capMax = weakSlotCap A) (h2 : Pw.slowOrder = Lr + 3 + (A.Nw + weakSlotCap A))
    (h3 : Pw.fastOrder = Lr + 3) (hJN : 1 ≤ A.Jw * A.Nw) (hLr : weakWindowLrFloor A k₀ ≤ Lr) :
    WeakOrderFloors A k₀ Pw := by
  have hqs : weakSettingQs A k₀ ≤ Lr :=
    le_trans (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)) hLr
  have hqf : weakSettingQf A k₀ ≤ Lr :=
    le_trans (le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _)) hLr
  refine ⟨?_, ?_, ?_⟩
  · rw [h2]; omega
  · rw [h3]
    have := le_max_left (Lr + 3) (Lr + 3 + 2)
    omega
  · rw [h1]
    show 1 + A.Jw * A.Nw = max 2 (1 + A.Jw * A.Nw)
    omega

end AVRegularity.Providers.WeakGen.Window
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Lift AVRegularity.EntryWeakProofs
namespace AVRegularity.Providers.WeakGen.Window

/-! **The clipped window lies in the slot window.**

`[wSeqStart, wSeqEnd]` is a nonempty subinterval of `[weakSlotLeft, weakSlotRight]` for an
observed pulse (the window inequalities of `isLiftSetting_transfer`). Model: the same step at
terminal entry (namespace `EntryTerminal.Ingredients.Recon.Setting`).

The degenerate cases are included: a pulse observed at a single time (the clipped window is a
point). -/

open WeakEntryProofs WeakEntryProofs.Assembly Finite.WeakLift

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}
variable (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ) (hi : c.M < i)

include hi

theorem wSeqStart_ge (hΛ1 : 1 ≤ c.D.Λ) (hκM : 0 < c.D.κ c.M) (k : ℤ) :
    weakSlotLeft c.D i k ≤ wSeqStart c r i k := by
  have hc := wSetting_cell c i hi hκM
  have hcpos : 0 < c.D.cellScaleSq i := by
    unfold OCData.cellScaleSq OCData.eps
    rw [wSetting_kap c i hi]
    exact div_pos (pow_pos (Construction.Stream.ocEpsilon_pos hΛ1) 2) hκM
  show _ ≤ max _ _ / ocEll c.D.q c.D.Λ i (c.D.κ c.M) ^ 2
  rw [hc]
  exact div_le_div_of_nonneg_right (le_max_left _ _) hcpos.le

theorem wSeqEnd_le (hΛ1 : 1 ≤ c.D.Λ) (hκM : 0 < c.D.κ c.M) (k : ℤ) :
    wSeqEnd c r i k ≤ weakSlotRight c.D i k := by
  have hc := wSetting_cell c i hi hκM
  have hcpos : 0 < c.D.cellScaleSq i := by
    unfold OCData.cellScaleSq OCData.eps
    rw [wSetting_kap c i hi]
    exact div_pos (pow_pos (Construction.Stream.ocEpsilon_pos hΛ1) 2) hκM
  show min _ _ / ocEll c.D.q c.D.Λ i (c.D.κ c.M) ^ 2 ≤ _
  rw [hc]
  exact div_le_div_of_nonneg_right (min_le_left _ _) hcpos.le

omit hi in
theorem wSeq_window_nonempty {k : ℤ}
    (hk : k ∈ ocObsPulses c.D.α c.D.q c.D.Λ i (r.tq i) (r.tq i + wTobs c r i)) :
    wSeqStart c r i k ≤ wSeqEnd c r i k :=
  CycleComparison.LiftSetting.window (c.D.κ c.M) hk

end AVRegularity.Providers.WeakGen.Window
end
end

section
section
/-! **The atlas and the fast independence of the window family**, and the step
`WeakFamilyStep` from the common plan floors. The atlas is that of
`quietAtlas_of_allTransfer` on the re-capped stage, with the presentation of the stage `i`
(`weakNativeQuietStagePresentation`, transferred by `recapPresentation`; the root stage has no
identity). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Providers.QuietAtlas

namespace AVRegularity.Providers.WeakGen.Window

open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.EntryWeakProofs
  AVRegularity.Providers.WeakGen.Comparison

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- **Fast independence of the window family** on the trimmed quiet times of its level. -/
theorem weakWindowFamily_fastIndependent (hplan : WeakPassageCommonOK plan)
    (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw)
    (S : Set ℝ) :
    (weakWindowFamily c i hi hit).IsFastIndependentOn
      (ocTrimmedQuietTimes c.D.α c.D.q c.D.Λ c.D.ζ i ∩ S) := by
  have hlv := weakConstruction_level c.P _ c.M A.Jw 0 _ c.stage c.construction i hi.le hit
  have hnat := weakStage_isNatural c i hi hit
  refine GenStage.isFastIndependentOn_actualFamily (weakWindowStage c i hi hit) ?_
  intro p ctx v u γ d I t ht X z z'
  have h := Providers.WeakGen.Residual.weakNativeQuietFastIndependent hplan c hi.le hit p ctx v u
    γ d I t ⟨ht.1.1, ?_⟩ X z z'
  · exact h
  · have := ht.2
    change t ∈ ((c.stage i).fam.piece p).output at this
    rw [(hnat.1 p).2.1, hlv] at this
    exact this

/-- **The atlas of the window family**: the four atlas clauses of `WeakFamilyBody`. -/
theorem weakWindowFamily_atlas (hplan : WeakPassageCommonOK plan)
    (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw)
    (W : Set ℝ) :
    ∃ T : (weakWindowFamily c i hi hit).Atlas,
      T.IsConsecutiveClosed W ∧
      T.CoversQuiet (ocQuietTimes c.D.α c.D.q c.D.Λ c.D.ζ i) W ∧
      T.IsQuiet (c.D.κ c.M) (ocEpsilon c.D.q c.D.Λ i) (ocEpsilon c.D.q c.D.Λ (i - 1)) ∧
      (∀ p q (hpq : T.adjacent p q),
        (((weakWindowFamily c i hi hit).piece p).output ∩
          ((weakWindowFamily c i hi hit).piece q).output ∩ W).Nonempty →
        T.sameCtx p q hpq () ()) := by
  have hbase : weakCommonCoeffPlan.baseThreshold B ≤ A.Λ := (hplan.1 B).trans c.base_ge
  have hlev' : weakCommonCoeffPlan.levelThreshold (weakCoeffRequestOne R) c.j₀ ≤ c.M :=
    (hplan.2 R c.j₀).trans c.level_ge
  have hgate := weakCommonPlan_complexContext weakBasePlan (weakCertConst weakBasePlan) weakBasePlan_complexContext
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
    fun m => weakData_cellScaleSq_pos c.D hΛ hζ hκb m
  have hlvl : c.j₀ + 2 ≤ c.M := (hgate.2 (weakCoeffRequestOne R) c.j₀).trans hlev'
  have hlv := weakConstruction_level c.P _ c.M A.Jw 0 _ c.stage c.construction i hi.le hit
  have hnat := weakStage_isNatural c i hi hit
  -- the presentation of the stage and of its re-cap
  have hQ : ∃ Q : QuietPresentation (c.stage i), Q.AllTransfer ∧
      FinerHistoryInvariant (c.stage i) Q (c.M + A.Jw) := by
    by_cases hiJ : i = c.M + A.Jw
    · subst hiJ
      have hempty : ∀ v u, IsEmpty ((c.stage (c.M + A.Jw)).fam.Γ v u) :=
        c.construction.2.1.2.2.1
      refine ⟨⟨fun v u γ => ((hempty v u).false γ).elim,
        fun p ch v u γ => ((hempty v u).false γ).elim⟩, ?_, ?_⟩
      · intro v u γ; exact ((hempty v u).false γ).elim
      · intro v u γ; exact ((hempty v u).false γ).elim
    · obtain ⟨Q, hall, hF, -⟩ := Providers.WeakGen.weakNativeQuietStagePresentation hΛ hζ hb hstart
        hcell c.construction hi.le (lt_of_le_of_ne hit hiJ)
      exact ⟨Q, hall, hF⟩
  obtain ⟨Q, hall, hF⟩ := hQ
  have hN := weakStage_maxOrder_le c i hi hit
  obtain ⟨T, hTc, hTv, hTq, hTs, -⟩ := quietAtlas_of_allTransfer hb hΛ hζ (weakWindowStage c i hi hit)
    (recapPresentation (1 + A.Jw * A.Nw) hN (c.stage i).exports Q hall) (recapPresentation_allTransfer
      (N := 1 + A.Jw * A.Nw) (hN := hN) (𝒮 := (c.stage i).exports) Q hall) (c.M + A.Jw) W
    (by change 1 ≤ (c.stage i).level; omega) (by change c.j₀ ≤ (c.stage i).level; omega) 1 400
    (le_refl 1) hcarrier
    (recap_isNatural (N := 1 + A.Jw * A.Nw) (hN := hN) (𝒮 := (c.stage i).exports) hnat)
    (recapPresentation_finerHistory (N := 1 + A.Jw * A.Nw) (hN := hN) (𝒮 := (c.stage i).exports)
      Q hall hF)
  refine ⟨(weakWindowStage c i hi hit).actualAtlas T,
    GenStage.actualAtlas_isConsecutiveClosed _ hTc, GenStage.actualAtlas_coversQuiet _ ?_, ?_, ?_⟩
  · have e : ocQuietTimes c.D.α c.D.q c.D.Λ c.D.ζ (weakWindowStage c i hi hit).level =
        ocQuietTimes c.D.α c.D.q c.D.Λ c.D.ζ i := by
      rw [show (weakWindowStage c i hi hit).level = i from hlv]
    rw [e] at hTv
    exact hTv
  · have he : (weakWindowStage c i hi hit).level = i := hlv
    have hk : c.D.kap (weakWindowStage c i hi hit).level = c.D.κ c.M := by
      rw [he, weakData_kap_terminal c.D i (by rw [c.terminal]; exact hi.le), c.terminal]
    have e1 : c.D.eps (weakWindowStage c i hi hit).level = ocEpsilon c.D.q c.D.Λ i := by
      rw [he]; rfl
    have e2 : c.D.eps ((weakWindowStage c i hi hit).level - 1) =
        ocEpsilon c.D.q c.D.Λ (i - 1) := by
      rw [he]; rfl
    rw [hk, e1, e2] at hTq
    exact GenStage.actualAtlas_isQuiet (weakWindowStage c i hi hit) hTq
  · intro p q hpq hne
    exact hTs p q hpq hne

/-- **The family side of the window of a weak passage**, for a plan with the common floors. -/
theorem weakFamilyStep_of_common (hplan : WeakPassageCommonOK plan)
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (k₀ : ℕ) : WeakFamilyStep c r i hi hit k₀ := by
  intro _
  obtain ⟨T, hTc, hTv, hTq, hTs⟩ := weakWindowFamily_atlas hplan c i hi hit
    (Set.Icc (r.tq i) (r.tq i + wTobs c r i))
  obtain ⟨hpp, hinj, hpart⟩ := weakWindowFamily_pieces c r i hi hit
  exact ⟨T, weakWindowFamily_isDescending c i hi hit k₀, weakWindowFamily_isTorusCompatible c i hi hit,
    hTc, hTv, hTq, hTs, hpp, hinj, hpart, weakWindowFamily_fastIndependent hplan c i hi hit _⟩

end AVRegularity.Providers.WeakGen.Window
end
end

section
/-! **Lift sequences, part 3: the positive lifts of the slot vanish at the cell time of `t_i`**.
Model: the same step at terminal entry (`EntryTerminal.Ingredients.Recon.Seq.seq_zero_at_tp`). The
time `t_i = (l + 1/2) τ''_i` is a quiet margin
midpoint (`IsWeakReduction`), so the stretch `[slotStart, t_i]` lies in the trimmed quiet times of
the level (`renewal_boundary_quiet_margin`, `τ'_i = L_i τ_i`, `L_i ≥ 5`), where the native drift
vanishes and the fluxes are fast independent (`weakNativeQuietDrift`,
`weakNativeQuietFastIndependent`); `r2c_quietZero_core` then gives the zero.

The ellipticity of the lift metric on the slot windows holds above the level
`weakEllLevel B Λ` (`uniform_native_lift_ellipticity_all_carriers`): a plan condition
`WeakPassageEllOK plan` (the level floor is above it). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Reconstruction AVRegularity.CycleComparison.Lift
open AVRegularity.EntryWeakProofs AVRegularity.Construction.Residual.Presentation

namespace AVRegularity.Providers.WeakGen.Window

open WeakEntryProofs WeakEntryProofs.Assembly

/-- The level above which the native lift metric is uniformly elliptic on the slot windows, for
the base `B` and the integer `Λ`. -/
def weakEllLevel (B : WeakCoefficientBase) (Λ : ℕ) : ℕ :=
  if h : 128 ≤ Λ then
    Classical.choose
      (Construction.Preservation.FullLift.uniform_native_lift_ellipticity_all_carriers.{0, 0}
      B.α B.s B.q B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq Λ h B.ζ B.hζ)
  else 0

/-- **The ellipticity floor of a passage plan**: the level floor is above `weakEllLevel`. -/
def WeakPassageEllOK (plan : WeakPassagePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A) (j₀ : ℕ),
    weakEllLevel B A.Λ ≤ plan.levelFloor R j₀

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- **Ellipticity of the restricted ambient lift metric on the slot window.** -/
theorem weakCap_ellipticity (hell : WeakPassageEllOK plan) (c : WeakPassageInstance plan R)
    (i : ℕ) (hi : c.M < i) (k : ℤ) (hk : Odd k) :
    ∀ t ∈ Set.Icc (c.D.slotStart i k / c.D.cellScaleSq i)
        ((((k : ℝ) + 61 / 48) * ocTau c.D.α c.D.q c.D.Λ i) / c.D.cellScaleSq i),
      ∀ X ξ : Vec 2,
        (3 / 4) * ∑ a, ξ a ^ 2 ≤ ∑ a, ∑ b, (weakCapData c i k hk).G t X a b * ξ a * ξ b ∧
        ∑ a, ∑ b, (weakCapData c i k hk).G t X a b * ξ a * ξ b ≤ (5 / 4) * ∑ a, ξ a ^ 2 := by
  have hΛ128 : 128 ≤ A.Λ := (plan.base_ge B).trans c.base_ge
  have hM : weakEllLevel B A.Λ ≤ c.M := (hell R c.j₀).trans c.level_ge
  have hspec := (Classical.choose_spec
    (Construction.Preservation.FullLift.uniform_native_lift_ellipticity_all_carriers.{0, 0}
      B.α B.s B.q B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq A.Λ hΛ128 B.ζ B.hζ)).2
  have hM' : Classical.choose
      (Construction.Preservation.FullLift.uniform_native_lift_ellipticity_all_carriers.{0, 0}
      B.α B.s B.q B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq A.Λ hΛ128 B.ζ B.hζ) ≤ c.M := by
    simpa [weakEllLevel, hΛ128] using hM
  intro t ht X ξ
  exact hspec (CompIn (c.stage i).comps) (fun v => ScalarH v.1.root) c.Dm c.D c.alpha c.q_eq
    c.base_eq c.profile_eq c.streams
    (by rw [c.alpha, c.q_eq, c.base_eq, c.profile_eq, c.terminal]; exact c.band) i (by omega) k hk
    (c.D.eps (i - 1))
    ((c.stage i).fam.fiber ⟨k, hk⟩ ((c.stage i).actual ⟨k, hk⟩)) t ht X ξ

/-- **Part 3 proved**: the positive lifts of the slot vanish at the cell time of `t_i`. -/
theorem weakSeqQuietZero_of (hplan : WeakPassageCommonOK plan) (hell : WeakPassageEllOK plan)
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (h : WeakComparisonInput r i) : WeakSeqQuietZero c r i h := by
  classical
  intro k hk _ hstart hwin hseq hh hhH n hn m α X' z v u
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

end AVRegularity.Providers.WeakGen.Window
end
end
end
end

section
@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Providers.WeakGen.Window

/-! **Edge agreement of a slot lift with the window, generic part.**

The edges of a slot lift at its cap, extended to the cap `D_w`, agree on a subinterval of the
slot-lift window with the clamped edges of the ambient native edges restricted to `D_w` (the two
cases of the slot lift's `edge_agree`); the edge relations compose (`weakLifts_forall₂_comp`).

The degenerate cases are included: both edge families empty (first case of `edge_agree`);
`cap = D_w` (the extension is the identity). -/

open AVRegularity.EntryTerminal.Ingredients.Recon.Setting
  AVRegularity.Construction.Preservation.FullLift AVRegularity.Providers.WeakGen.Residual

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- A relation holding for each time of a nonempty set, on lists of the same shape. -/
theorem weakLifts_forall₂_of_forall {α β τ : Type*} (T : Set τ) (R : τ → α → β → Prop) (t₀ : τ)
    (ht₀ : t₀ ∈ T) :
    ∀ (l₁ : List α) (l₂ : List β), (∀ t ∈ T, List.Forall₂ (R t) l₁ l₂) →
      List.Forall₂ (fun x y => ∀ t ∈ T, R t x y) l₁ l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ hh
    have := hh t₀ ht₀
    rw [List.forall₂_nil_left_iff] at this
    rw [this]
    exact List.Forall₂.nil
  | cons x xs ih =>
    intro l₂ hh
    have h0 := hh t₀ ht₀
    cases l₂ with
    | nil => exact absurd h0 (by simp)
    | cons y ys =>
      refine List.Forall₂.cons (fun t ht => ((List.forall₂_cons.1 (hh t ht)).1)) (ih ys ?_)
      exact fun t ht => (List.forall₂_cons.1 (hh t ht)).2

end AVRegularity.Providers.WeakGen.Window
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.EntryTerminal.Ingredients.Recon.Setting
namespace AVRegularity.Providers.WeakGen.Window

/-! **The window's edges against the stage's native edges.**

`weakWindow_native_rel`: positionally, the lifted edge of the window family at the order `d ≤ D_w`
has the map of the lifted native edge of the stage and, as coefficient, the native coefficient
on the output window of the piece and `0` off it (the actual family).

The degenerate cases are included: a degree above every maximal order (both lists empty).  -/

open WeakEntryProofs WeakEntryProofs.Assembly Finite.WeakLift AVRegularity.Providers.WeakGen.Residual

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

open scoped Classical in
theorem weakWindow_native_rel (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (p : OddSlot) (c0 lam : ℝ)
    (v u : CompIn (c.stage i).comps) (d : Finset.Icc 2 (1 + A.Jw * A.Nw)) :
    List.Forall₂ (fun (n w : Constituent d.1 (ScalarH u.1.root) (ScalarH v.1.root)) =>
        w.map = n.map ∧ ∀ α t X z, w.coeff α t X z =
          if c0 * t ∈ ((c.stage i).fam.piece p).output then n.coeff α t X z else 0)
      (liftEdges c0 lam ((c.stage i).fam.fiber p ((c.stage i).actual p)) v u
        ⟨d.1, Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 d.2).1,
          (Finset.mem_Icc.1 d.2).2.trans c.order_ge⟩⟩)
      (liftEdges c0 lam ((weakWindowFamily c i hi hit).fiber p ()) v u d) := by
  simp only [liftEdges, ChartedFamily.fiber]
  refine forall₂_filterMap_map _ Finset.univ.toList _ _ _ _ ?_ ?_
  · intro x
    by_cases hd : (d : ℕ) ≤ ((c.stage i).fam.identity v u x).maxOrder
    · simp [weakWindowFamily, weakWindowStage, GenStage.actualFamily, GenStage.recap, CoefficientIdentity.recap, hd]
    · simp [weakWindowFamily, weakWindowStage, GenStage.actualFamily, GenStage.recap, CoefficientIdentity.recap, hd]
  · intro x y₁ y₂ e1 e2
    by_cases hd : (d : ℕ) ≤ ((c.stage i).fam.identity v u x).maxOrder
    · simp only [hd, ↓reduceDIte, Option.some.injEq] at e1
      simp only [weakWindowFamily, weakWindowStage, GenStage.actualFamily, GenStage.recap, CoefficientIdentity.recap, hd,
        ↓reduceDIte, Option.some.injEq] at e2
      subst e1 e2
      refine ⟨rfl, fun α t X z => ?_⟩
      by_cases ht : c0 * t ∈ ((c.stage i).fam.piece p).output
      · simp [ht]
      · simp [ht]
    · simp [hd] at e1

/-- Composition of positional relations. -/
theorem weakLifts_forall₂_comp {α β γ : Type*} {R : α → β → Prop} {S : β → γ → Prop}
    {T : α → γ → Prop} (hT : ∀ x y z, R x y → S y z → T x z) :
    ∀ {l₁ : List α} {l₂ : List β} {l₃ : List γ}, List.Forall₂ R l₁ l₂ → List.Forall₂ S l₂ l₃ →
      List.Forall₂ T l₁ l₃ := by
  intro l₁ l₂ l₃ a1 a2
  induction a1 generalizing l₃ with
  | nil => cases a2; exact List.Forall₂.nil
  | cons hxy _ ih =>
    cases a2 with
    | cons hyz a2' => exact List.Forall₂.cons (hT _ _ _ hxy hyz) (ih a2')

section Generic

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

open scoped Classical in
/-- **The slot lift's edges against the window's edges**, positionally: the window's coefficient is
the slot lift's on `O` and `0` off it, where `O ⊆ [a, b]` is the part of the slot window seen by the
output window of the piece. -/
theorem weakLifts_rel_slotLift {cap Dw Dm : ℕ} (hcap : cap ≤ Dw) (hDw : Dw ≤ Dm)
    (E : ConstituentEdges Dm h) (Qe : ConstituentEdges cap h) (Wd : ConstituentEdges Dw h)
    {a b : ℝ} (O : Set ℝ) (hO : O ⊆ Set.Icc a b) (hab : a ≤ b)
    (hNW : ∀ v u (d : Finset.Icc 2 Dw), List.Forall₂
      (fun (n w : Constituent d.1 (h u) (h v)) => w.map = n.map ∧
        ∀ α t X z, w.coeff α t X z = if t ∈ O then n.coeff α t X z else 0)
      (E v u ⟨d.1, Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 d.2).1,
        (Finset.mem_Icc.1 d.2).2.trans hDw⟩⟩) (Wd v u d))
    (hag : ((∀ v u d, Qe v u d = []) ∧ ∀ v u d, E v u d = []) ∨
      ∃ hc : cap ≤ Dm, (∀ v u (d : Finset.Icc 2 Dm), cap < d.1 → E v u d = []) ∧
        ∀ t ∈ Set.Icc a b, EntryWeakProofs.SlowOpenEdgeEq Set.univ t
          (EntryWeakProofs.restrictConstituentEdges cap hc E) Qe)
    (v u : ι) (d : Finset.Icc 2 Dw) :
    List.Forall₂ (fun (q w : Constituent d.1 (h u) (h v)) => w.map = q.map ∧
        ∀ α t X z, w.coeff α t X z = if t ∈ O then q.coeff α t X z else 0)
      (extendEdges hcap Qe v u d) (Wd v u d) := by
  have hnil : E v u ⟨d.1, Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 d.2).1,
      (Finset.mem_Icc.1 d.2).2.trans hDw⟩⟩ = [] → Wd v u d = [] := fun he => by
    have := hNW v u d
    rw [he] at this
    exact List.forall₂_nil_left_iff.mp this
  rcases hag with ⟨h1, h2⟩ | ⟨hc, hz, hag⟩
  · by_cases hd : d.1 ≤ cap
    · rw [extendEdges_of_le hcap Qe v u d hd, h1, hnil (h2 _ _ _)]
      exact List.Forall₂.nil
    · rw [extendEdges_eq_nil hcap Qe v u d (not_le.1 hd), hnil (h2 _ _ _)]
      exact List.Forall₂.nil
  · by_cases hd : d.1 ≤ cap
    · rw [extendEdges_of_le hcap Qe v u d hd]
      have hmainE := weakLifts_forall₂_of_forall (Set.Icc a b)
        (fun t (x y : Constituent d.1 (h u) (h v)) => x.map = y.map ∧
          ∀ α X z, x.coeff α t X z = y.coeff α t X z) a ⟨le_rfl, hab⟩
        (E v u ⟨d.1, Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 d.2).1,
          (Finset.mem_Icc.1 d.2).2.trans hDw⟩⟩)
        (Qe v u ⟨d.1, Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 d.2).1, hd⟩⟩) (fun t ht => by
          have := hag t ht v u ⟨d.1, Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 d.2).1, hd⟩⟩
          exact List.Forall₂.imp (fun x y hxy => ⟨hxy.1, fun α X z =>
            hxy.2 α X (Set.mem_univ X) z⟩) this)
      have hflip := List.Forall₂.flip (R := fun (q n : Constituent d.1 (h u) (h v)) =>
        ∀ t ∈ Set.Icc a b, (n.map = q.map ∧ ∀ α X z, n.coeff α t X z = q.coeff α t X z)) hmainE
      refine weakLifts_forall₂_comp (fun q n w hqn hnw => ⟨hnw.1.trans (hqn a ⟨le_rfl, hab⟩).1,
        fun α t X z => ?_⟩) hflip (hNW v u d)
      rw [hnw.2 α t X z]
      by_cases ht : t ∈ O
      · simp only [ht, ite_true]
        exact (hqn t (hO ht)).2 α X z
      · simp only [ht, ite_false]
    · rw [extendEdges_eq_nil hcap Qe v u d (not_le.1 hd),
        hnil (hz _ _ _ (not_le.1 hd))]
      exact List.Forall₂.nil

end Generic

end AVRegularity.Providers.WeakGen.Window
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Lift AVRegularity.EntryWeakProofs
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.EntryTerminal.Ingredients.Recon.Setting
namespace AVRegularity.Providers.WeakGen.Window

/-! **The lift setting of one observed pulse from its slot lift.**

`weakLift_pulse`: a slot lift `WeakPositiveSlot` of the pulse's slot, brought to the cap `D_w` and
the window's orders (`weakSlot_cappedSetting`), is transferred to the clipped window
(`isLiftSetting_transfer`, the edge relation of `weakLifts_rel_slotLift`), the real parameters are
rewritten (`isLiftSetting_congr_params`) and the jet constants raised to `C_a`
(`isLiftSetting_mono_const`). The price is the slot lift's.

The degenerate cases are included: a slot lift at the cap `2` (both orders raised); the root stage
(empty family). -/

open WeakEntryProofs WeakEntryProofs.Assembly Finite.WeakLift
  AVRegularity.Providers.WeakGen.Residual

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- Positional membership: every element of the right list is related to one of the left. -/
theorem weakLifts_forall₂_mem_right {α β : Type*} {Rel : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ Rel l₁ l₂ → ∀ y ∈ l₂, ∃ x ∈ l₁, Rel x y := by
  intro l₁ l₂ hh
  induction hh with
  | nil => intro y hy; simp at hy
  | cons hxy _ ih =>
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact ⟨_, List.mem_cons_self, hxy⟩
    · obtain ⟨x, hx, hr⟩ := ih y hy'
      exact ⟨x, List.mem_cons_of_mem _ hx, hr⟩


section Pulse

variable (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ) (hi : c.M < i)
  (hit : i ≤ c.M + A.Jw)

/-- **The lift setting of an observed pulse from its slot lift.** -/
theorem weakLift_pulse (k₀ : ℕ) {Lr : ℕ} (Pw : WeakPositiveParameters A.Nw (weakH A) (Lr + 3))
    (hfl : WeakOrderFloors A k₀ Pw) (hΛ1 : 1 ≤ c.D.Λ) (hκM : 0 < c.D.κ c.M) {k : ℤ} (hk : Odd k)
    (hkobs : k ∈ ocObsPulses c.D.α c.D.q c.D.Λ i (r.tq i) (r.tq i + wTobs c r i))
    (S : WeakPositiveSlot Pw i (c.stage i) (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1) ⟨k, hk⟩ (c.D.eps (i - 1))) :
    IsLiftSetting (wLiftData c i hi hit k) (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1)
      (wSeqStart c r i k) (wSeqEnd c r i k) (ocEpsilon c.D.q c.D.Λ i) (c.D.κ c.M) (c.D.κ c.M)
      (ocEpsilon c.D.q c.D.Λ (i - 1)) (ocEpsilon c.D.q c.D.Λ (i - 1))
      (ocEll c.D.q c.D.Λ i (c.D.κ c.M)) (ocDStar c.D.q c.D.Λ i (c.D.κ c.M) (c.D.κ c.M))
      (ocDStar c.D.q c.D.Λ i (c.D.κ c.M) (c.D.κ c.M) / ocEpsilon c.D.q c.D.Λ (i - 1))
      (ocEpsilon c.D.q c.D.Λ (i - 1) / ocEpsilon c.D.q c.D.Λ (i - 1))
      (pulseParallel k) (pulseShearProfile c.D.α c.D.q c.D.Λ i c.D.ζ (c.D.κ c.M) k)
      (weakH A) A.Nw (weakKlift A k₀) (weakLlift A k₀) (weakLlift A k₀)
      (weakSettingQs A k₀) (weakSettingQf A k₀) Pw.CG Pw.Cw
      (fun _ _ => weakSettingCa Pw (weakSettingQs A k₀) (weakSettingQf A k₀)) S.price Pw.S := by
  classical
  have hset := weakSlot_cappedSetting A k₀ Pw hfl i (c.stage i)
    (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1) ⟨k, hk⟩ S
  have hD : S.cap ≤ weakDw A := S.cap_le.trans hfl.2.2.ge
  have hcell := wSetting_cell c i hi hκM
  have hcpos : 0 < c.D.cellScaleSq i := by
    rw [← hcell]
    exact pow_pos (div_pos (Construction.Stream.ocEpsilon_pos hΛ1) (Real.sqrt_pos.2 hκM)) 2
  have hs₀ := wSeqStart_ge c r i hi hΛ1 hκM k
  have hs₁ := wSeqEnd_le c r i hi hΛ1 hκM k
  have ht := wSeq_window_nonempty c r i hkobs
  have hout := weakStage_output_eq c i hi hit ⟨k, hk⟩
  have e2 : (wLiftData c i hi hit k).edge = liftEdges (c.D.cellScaleSq i)
      (c.D.eps (i - 1) / c.D.eps (i - 1))
      ((weakWindowFamily c i hi hit).fiber ⟨k, hk⟩ ()) := by
    show liftEdges (ocEll c.D.q c.D.Λ i (c.D.κ c.M) ^ 2)
      (ocEpsilon c.D.q c.D.Λ (i - 1) / ocEpsilon c.D.q c.D.Λ (i - 1))
      ((weakWindowFamily c i hi hit).fiber (oddSlotOf k) ()) = _
    rw [oddSlotOf_of_odd hk, hcell]
    rfl
  let O : Set ℝ := (fun t => c.D.cellScaleSq i * t) ⁻¹' ((c.stage i).fam.piece ⟨k, hk⟩).output
  have hO : O ⊆ Set.Icc (weakSlotLeft c.D i k) (weakSlotRight c.D i k) := by
    intro t htO
    have h1 : c.D.cellScaleSq i * t ∈ ocPulseWindow c.D.α c.D.q c.D.Λ i k := by
      have := htO
      simp only [O, Set.mem_preimage] at this
      rwa [hout] at this
    refine ⟨?_, ?_⟩
    · exact (div_le_iff₀ hcpos).2 (by rw [mul_comm]; exact h1.1)
    · exact (le_div_iff₀ hcpos).2 (by rw [mul_comm]; exact h1.2)
  have hab : weakSlotLeft c.D i k ≤ weakSlotRight c.D i k := ht.trans' hs₀ |>.trans hs₁
  have hrel := fun v u d => weakLifts_rel_slotLift (E := (weakPositiveNativeData i (c.stage i)
      ⟨k, hk⟩).edge) (Qe := S.Q.edge) (Wd := (wLiftData c i hi hit k).edge) hD c.order_ge O hO hab
    (fun v u d => by
      rw [e2]
      exact weakWindow_native_rel c i hi hit ⟨k, hk⟩ _ _ v u d) S.edge_agree v u d
  have hE : EdgeAgree (extendData hD S.Q).edge (wLiftData c i hi hit k).edge
      (wSeqStart c r i k) (wSeqEnd c r i k) := by
    intro v u d
    refine List.Forall₂.imp (fun q w hqw => ⟨hqw.1.symm, fun α t htt => ?_⟩) (hrel v u d)
    funext X z
    rw [hqw.2 α t X z]
    have htO : t ∈ O := by
      simp only [O, Set.mem_preimage]
      rw [hout]
      have := CycleComparison.LiftSetting.mul_mem_pulseWindow_inter
        (by rw [hcell]; exact hcpos : 0 < ocEll c.D.q c.D.Λ i (c.D.κ c.M) ^ 2) htt
      rw [hcell] at this
      exact this.1
    simp only [htO, ite_true]
  have hmeas : ∀ v u d, ∀ γ ∈ (wLiftData c i hi hit k).edge v u d, ∀ α X z,
      Measurable fun t => γ.coeff α t X z := by
    intro v u d γ hγ α X z
    obtain ⟨q, hq, hqw⟩ := weakLifts_forall₂_mem_right (hrel v u d) γ hγ
    have hmq := hset.coeff_meas v u d q hq α X z
    have hOm : MeasurableSet O := by
      show MeasurableSet ((fun t => c.D.cellScaleSq i * t) ⁻¹' _)
      rw [hout]
      exact measurableSet_Icc.preimage (measurable_const.mul measurable_id)
    have : (fun t => γ.coeff α t X z) = fun t => if t ∈ O then q.coeff α t X z else 0 :=
      funext fun t => hqw.2 α t X z
    rw [this]
    exact Measurable.ite hOm hmq measurable_const
  have hη : (wLiftData c i hi hit k).η = (extendData hD S.Q).η :=
    (wSetting_eta c i hi hit hk).trans S.eta_eq.symm
  have hG : (wLiftData c i hi hit k).G = (extendData hD S.Q).G :=
    (wSetting_metric c i hi hit hΛ1 hκM hk).trans S.metric_eq.symm
  have hv : (wLiftData c i hi hit k).v = (extendData hD S.Q).v :=
    (wSetting_drift c i hi hit hk).trans S.drift_eq.symm
  have htr := isLiftSetting_transfer hset hs₀ ht hs₁ (Q₂ := wLiftData c i hi hit k) hη hG hv hE hmeas
  have hkap := wSetting_kap c i hi
  have hkap1 := wSetting_kap_pred c i hi
  have hcg := isLiftSetting_congr_params (e' := ocEpsilon c.D.q c.D.Λ i)
    (ν' := c.D.κ c.M) (B' := c.D.κ c.M) (ρ' := ocEpsilon c.D.q c.D.Λ (i - 1))
    (E' := ocEpsilon c.D.q c.D.Λ (i - 1)) (ℓ' := ocEll c.D.q c.D.Λ i (c.D.κ c.M))
    (dstar' := ocDStar c.D.q c.D.Λ i (c.D.κ c.M) (c.D.κ c.M))
    (εc' := ocDStar c.D.q c.D.Λ i (c.D.κ c.M) (c.D.κ c.M) / ocEpsilon c.D.q c.D.Λ (i - 1))
    (lam' := ocEpsilon c.D.q c.D.Λ (i - 1) / ocEpsilon c.D.q c.D.Λ (i - 1)) htr rfl hkap hkap1
    rfl rfl (by rw [hkap]; rfl) (by rw [hkap, hkap1]) (by rw [hkap, hkap1]; rfl) rfl
  rw [hkap] at hcg
  exact isLiftSetting_mono_const hcg (fun r hr q hq => le_weakSettingCa Pw _ _ hr hq) le_rfl

end Pulse

end AVRegularity.Providers.WeakGen.Window
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Lift AVRegularity.EntryWeakProofs
open AVRegularity.Construction.Residual.Presentation
namespace AVRegularity.Providers.WeakGen.Window

/-! **The lifts: `WeakLiftsStep` from the slot lifts with one price.**

`WeakUniformSlotLifts`: slot lifts of all the slots whose price is the record majorant of the
stage's family (the weak factory's choice, `weakParentPrice`). `weakLiftsStep_of_uniform` proves
`WeakLiftsStep` from them, with `bM = recordMajorant mass (stage i).fam` for every pulse, and
`weakSettingStep_of_plan` is the final theorem of this form: the plan condition
`WeakSlotLiftUPlanOK plan Lr`, the order floor `weakWindowLrFloor A k₀ ≤ Lr R`, the lift sequences
`WeakSeqStep` and the uniform slot lifts give `WeakSettingStep` at the named constants of
`weakSlotLiftUParams A (Lr R) R.sX R.sZ`.

The degenerate cases are included: no observed pulse (the lifts hold vacuously, any `bM`); one pulse
(the price of its slot lift is `bM`); two pulses in different slots (the same `bM`). -/

open WeakEntryProofs WeakEntryProofs.Assembly Finite.WeakLift
  AVRegularity.Providers.WeakGen.Residual

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- **Slot lifts of all the slots of the stage `i`, all with the price of the stage's record
majorant.** -/
def WeakUniformSlotLifts (c : WeakPassageInstance plan R) (i : ℕ) {Lr : ℕ}
    (Pw : WeakPositiveParameters A.Nw (weakH A) (Lr + 3)) : Prop :=
  ∃ slotLifts : ∀ slot : OddSlot, WeakPositiveSlot Pw i (c.stage i)
      (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1) slot (c.D.eps (i - 1)),
    ∀ slot, (slotLifts slot).price =
      recordMajorant (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1) (c.stage i).fam

section Step

variable (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ) (hi : c.M < i)
  (hit : i ≤ c.M + A.Jw)

/-- **`WeakLiftsStep` from the uniform slot lifts.** -/
theorem weakLiftsStep_of_uniform (k₀ : ℕ) {Lr : ℕ}
    (Pw : WeakPositiveParameters A.Nw (weakH A) (Lr + 3)) (hfl : WeakOrderFloors A k₀ Pw)
    (hΛ1 : 1 ≤ c.D.Λ) (hκM : 0 < c.D.κ c.M) (hu : WeakUniformSlotLifts c i Pw) :
    WeakLiftsStep c r i hi hit k₀ Pw.CG Pw.Cw
      (weakSettingCa Pw (weakSettingQs A k₀) (weakSettingQf A k₀)) Pw.S := by
  intro _
  obtain ⟨pk, hpr⟩ := hu
  refine ⟨recordMajorant (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1) (c.stage i).fam, ?_⟩
  intro k hk
  have hodd := CycleComparison.LiftSetting.obsPulse_odd hk
  have h1 := weakLift_pulse c r i hi hit k₀ Pw hfl hΛ1 hκM hodd hk (pk ⟨k, hodd⟩)
  rw [hpr ⟨k, hodd⟩] at h1
  exact h1

end Step

end AVRegularity.Providers.WeakGen.Window
end
end
end
