-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.FullLift.ZeroFreshMetricSliceJets
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
import AVRegularity.Finite.WeakPositive.PositiveInputJets
import AVRegularity.Finite.TerminalLift.CovarianceIdentification
import AVRegularity.Finite.TerminalLift.PositiveGeometry
import AVRegularity.EntryTerminal.Ingredients.LiftField.LiftField
public import AVRegularity.Finite.Assembly.WeakPositiveChartOfIngredients
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
import AVRegularity.Construction.Preservation.FullLift.NativePulseTimeDissipation
import AVRegularity.Construction.TerminalLift.Assembly
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleComparison.Residual.CoarseFluxDiff.FluxTime
import AVRegularity.Families.TorusCompatible.WeakStage
import AVRegularity.Finite.Lift.PositivePhysicalIdentity
import AVRegularity.Finite.WeakLift.IdentitySeparation
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
import Mathlib.Algebra.Order.Star.Real

section
section
/-! Common terminal native slot-lift request. The physical menu determines the source cap and
all derivative orders before the radius multiplier and weak constants. The actual weak stage
and its data come only after the numeric slot-lift parameters have been selected. The same slot
lift serves
positive pointwise bounds and the spatial regularity/periodicity clause. -/

@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev MeasureTheory
namespace AVRegularity.Finite.TerminalLift
open WeakLift Construction.Preservation.FullLift

/-- The relevant fixed terminal physical menu; this is independent of the stage and datum. -/
structure TerminalPositiveRequest (B : WeakParentBase) where
  Λ : ℕ
  hΛ : 128 ≤ Λ
  bw : ℝ
  hbw : 0 < bw
  hbw1 : bw ≤ 1 / 10000
  N : ℕ
  H : ℕ
  DW : ℕ
  p : ℕ
  Lr : ℕ
  hN : 1 ≤ N

def TerminalPositiveRequest.cap {B : WeakParentBase} (R : TerminalPositiveRequest B) : ℕ :=
  termD0bar R.N R.p R.DW R.H

def TerminalPositiveRequest.order {B : WeakParentBase} (R : TerminalPositiveRequest B) : ℕ :=
  R.Lr + 3

def TerminalPositiveRequest.slow {B : WeakParentBase} (R : TerminalPositiveRequest B) : ℕ :=
  R.order + (R.N + R.cap)

/-- Later numeric constants, still fixed before carrier, terminal level and actual stage. -/
structure TerminalPositiveConstants where
  cr : ℝ
  hcr : 0 < cr
  hcr1 : cr ≤ 1
  kW : InvConsts
  hkw : kW.G0 ≤ kW.Hprod + 1
  CL : ℝ
  Cχ : ℝ
  χw : ℝ
  hχw : 0 < χw

/-- The actual weak stage supplied by the terminal profile premises. No field,
representation or realization is included: the slot lift is independent of the datum. -/
structure TerminalPositiveCase {B : WeakParentBase} (R : TerminalPositiveRequest B)
    (C : TerminalPositiveConstants) where
  j₀ : ℕ
  M : ℕ
  D : OCData
  hα : D.α = B.α
  hq : D.q = B.q
  hΛ : D.Λ = R.Λ
  hζ : D.ζ = B.ζ
  stream : IsOCStreamSeq B.α B.q R.Λ B.ζ D.Φ
  band : IsOCBandChain B.α B.q R.Λ B.ζ M D.κ
  term : D.term = M
  Jw : ℕ
  hJw : 1 ≤ Jw
  nW : ℕ+
  PW : ProvParams
  φ₀ : Vec 2 → ℝ
  hφ₀ : Integrable φ₀
  a : ℝ
  T₀ : ℝ
  σw : ℝ
  aM : ℝ
  law : BirthLaw
  G : GenStage D ScalarH R.cap R.bw j₀
  stage : IsWeakStage law PW φ₀ hφ₀ M (M + Jw) Jw R.H R.DW nW C.kW a T₀ σw
    C.CL C.Cχ C.χw G aM

/-- The radius is the literal slow length used by termLiftedRep. -/
def TerminalPositiveCase.radius {B : WeakParentBase} {R : TerminalPositiveRequest B}
    {C : TerminalPositiveConstants} (A : TerminalPositiveCase R C) : ℝ :=
  C.cr * liftLength A.D A.M

/-- Numeric witnesses share the same source and derivative caps for every actual stage. -/
def terminalPositiveParameters {B : WeakParentBase} (R : TerminalPositiveRequest B)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (S chartC : ℝ)
    (hS : 0 ≤ S) (hchart : 1 ≤ chartC) : WeakPositiveParameters R.N R.H R.order where
  capMax := R.cap
  cap_ge := le_max_left _ _
  slowOrder := R.slow
  fastOrder := R.order
  slow_reserve := Nat.le_add_right _ _
  fast_reserve := le_rfl
  CG := CG
  Cw := Cw
  Cj := Cj
  S := S
  S_nonneg := hS
  chartC := chartC
  chartC_ge := hchart

/-- A common original-slot lift and its physical geometry, with all scale side conditions. -/
def TerminalPositiveSlotLiftAt {B : WeakParentBase} {R : TerminalPositiveRequest B}
    {C : TerminalPositiveConstants} (P : WeakPositiveParameters R.N R.H R.order)
    (A : TerminalPositiveCase R C) : Prop :=
  0 < A.radius ∧ A.D.eps A.M ≤ A.radius ∧ A.radius ≤ A.D.eps (A.M - 1) ∧
  ocDStar A.D.q A.D.Λ A.M (A.D.κ A.M) (A.D.κ (A.M - 1)) / A.radius ≤ 1 ∧
  PositivePhysicalGeometry (N := R.N) (U := R.order) P.chartC A.M A.G A.radius ∧
  Nonempty (∀ slot : OddSlot, WeakPositiveSlot P A.M A.G (A.G.mass A.law) slot A.radius)

/-- Reuse terminal_level_lift and StageNativeLiftSourceEnvelope at the actual weak
stage. The slot lift and costs precede j0/M; its derivative caps are fixed by the earlier menu.
NT=0 is handled directly as the identity case before this positive-degree request is formed. -/
def TerminalPositiveSlotLiftStatement : Prop :=
  ∀ B : WeakParentBase, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧
  ∀ R : TerminalPositiveRequest B, Λ₀ ≤ R.Λ → ∀ C : TerminalPositiveConstants,
  ∃ P : WeakPositiveParameters R.N R.H R.order,
    P.capMax = R.cap ∧ P.slowOrder = R.slow ∧ P.fastOrder = R.order ∧
    ∀ j₀ : ℕ, ∃ M₀ : ℕ,
      ∀ A : TerminalPositiveCase R C, A.j₀ = j₀ → M₀ ≤ A.M → TerminalPositiveSlotLiftAt P A

end AVRegularity.Finite.TerminalLift
end
end

section
/-! Original-slot lift assembly. The common terminal lift already produces the setting and
both recurrences; full ambient cap removes the weak case's degree-padding alternative. -/

@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Finite.TerminalLift
open WeakLift Construction.Preservation.FullLift EntryWeakProofs

/-- Bundle the terminal lift's setting and recurrences into the radius-generic slot lift. -/
def terminalOriginalSlotLift {D : OCData} {Dm j₀ : ℕ} {bw : ℝ}
    {N H U : ℕ} (P : WeakPositiveParameters N H U) (i : ℕ)
    (G : GenStage D ScalarH Dm bw j₀) (π : CompIn G.comps → ℝ) (slot : OddSlot) (ρ : ℝ)
    (hDm : 2 ≤ Dm) (hcap : Dm ≤ P.capMax)
    (price : CompIn G.comps → CompIn G.comps → ℝ)
    (Cc : ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root)) :
    let raw := weakPositiveNativeData i G slot ρ
    let a := weakSlotLeft D i slot.1
    let b := weakSlotRight D i slot.1
    let Q := restrictLiftData Dm (le_refl Dm) {raw with edge := windowEdges a b raw.edge}
    IsLiftSetting Q π a b (D.eps i) (D.kap i) (D.kap (i - 1)) ρ
      (D.eps (i - 1)) (D.eps i / Real.sqrt (D.kap i))
      (ocDStar D.q D.Λ i (D.kap i) (D.kap (i - 1)))
      (ocDStar D.q D.Λ i (D.kap i) (D.kap (i - 1)) / ρ) (ρ / D.eps (i - 1))
      (pulseParallel slot.1) (pulseShearProfile D.α D.q D.Λ i D.ζ (D.kap i) slot.1)
      H N P.slowOrder P.fastOrder P.fastOrder
      (P.slowOrder + 4 * (H + 1) * (N + Dm) ^ 2)
      (max P.fastOrder (P.fastOrder + 2) + H * Dm + 2 * N + 2 * Dm)
      P.CG P.Cw P.Cj price P.S →
    IsLiftSequence Q (P.slowOrder + Dm + 2) (max (P.fastOrder + 1) (P.fastOrder + 2))
      a b N H Cc →
    IsLiftSequence raw (P.slowOrder + Dm + 2) (max (P.fastOrder + 1) (P.fastOrder + 2))
      a b N H Cc → WeakPositiveSlot P i G π slot ρ := by
  intro raw a b Q hsetting hsequence hambient
  refine {
    cap := Dm
    cap_ge := hDm
    cap_le := hcap
    Q := Q
    price := price
    metric_eq := rfl
    drift_eq := rfl
    eta_eq := rfl
    edge_agree := Or.inr ⟨le_refl Dm, by
      intro v u d hd
      have hb := (Finset.mem_Icc.mp d.2).2
      omega, by
      intro t ht
      exact windowEdges_agree a b raw.edge t ht⟩
    source_eq := ?_
    edge_fast := by
      intro S hS hn v u d γ hγ α
      exact weakPositive_windowEdges_fast raw.edge a b S hS hn v u d γ hγ α
    setting := hsetting
    coeff := Cc
    sequence := hsequence
    ambient := hambient }
  intro Dc a₀ hh n _hn t ht X z
  have hQ : Q = {raw with edge := windowEdges a b raw.edge} := rfl
  rw [hQ]
  exact (liftCellSource_edge_slow_open_congr isOpen_univ raw (windowEdges a b raw.edge)
    Dc a₀ hh n t (windowEdges_agree a b raw.edge t ht) X (Set.mem_univ X) z).symm

/-- The invariant supplies the whole-slot source envelope at a fixed numeric budget. -/
theorem terminal_positive_case_source {B : WeakParentBase} {R : TerminalPositiveRequest B}
    {C : TerminalPositiveConstants} (A : TerminalPositiveCase R C)
    (qs qf : ℕ) (J : ℕ → ℝ)
    (hsource : ∀ (D : OCData) (Dm j₀ : ℕ) (G : GenStage D ScalarH Dm R.bw j₀)
      (law : BirthLaw) (PW : ProvParams) (K : ℕ → KernelSpec)
      (φ₀ : Vec 2 → ℝ) (hφ₀ : MeasureTheory.Integrable φ₀) (Mnat : ℕ)
      (k : InvConsts) (tA tB S θK : ℝ),
      IsStageInvariant law PW K K φ₀ hφ₀ Mnat k tA tB S θK G →
      1 ≤ G.level → j₀ ≤ G.level → 0 < D.eps (G.level - 1) →
      1 < D.q → 128 ≤ D.Λ → IsFastProfile D.ζ →
      IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
      (∀ v : CompIn G.comps, 0 ≤ compReserve k v.1) →
      (∀ v : CompIn G.comps, compReserve k v.1 ≤ 2) →
      (∀ v u γ, 1 ≤ (G.fam.identity v u γ).record.birthExcess →
        (G.fam.identity v u γ).record.length ≤ D.eps G.level) →
      ∀ slot : OddSlot, ∀ lam : ℝ, 0 ≤ lam →
      IsScaledJetEnvelope (G.mass law)
        (liftEdges (D.cellScaleSq G.level) lam (G.fam.fiber slot (G.actual slot)))
        (Set.Icc (weakSlotLeft D G.level slot.1) (weakSlotRight D G.level slot.1))
        lam (fun r q => (Fintype.card (Finset.Icc 2 Dm) : ℝ) * J (r + q)) qs qf
        (recordMajorant (G.mass law) G.fam) S)
    (hM : 2 ≤ A.M) (hj : A.j₀ ≤ A.M)
    (hlen : |C.CL| * A.D.eps (A.M + 1) ≤ A.D.eps A.M)
    (slot : OddSlot) (lam : ℝ) (hlam : 0 ≤ lam) :
    IsScaledJetEnvelope (A.G.mass A.law)
      (weakPositiveNativeData A.M A.G slot (lam * A.D.eps (A.M - 1))).edge
      (Set.Icc (weakSlotLeft A.D A.M slot.1) (weakSlotRight A.D A.M slot.1))
      lam (fun r q => (Fintype.card (Finset.Icc 2 R.cap) : ℝ) * J (r + q)) qs qf
      (recordMajorant (A.G.mass A.law) A.G.fam) |C.Cχ| := by
  have hlevel : A.G.level = A.M := A.stage.2.2.1
  have hband : IsOCBandChain A.D.α A.D.q A.D.Λ A.D.ζ A.D.term A.D.κ := by
    simpa only [A.hα, A.hq, A.hΛ, A.hζ, A.term] using A.band
  have hζ : IsFastProfile A.D.ζ := A.hζ.symm ▸ B.hζ
  have hΛ : 128 ≤ A.D.Λ := A.hΛ.symm ▸ R.hΛ
  have he (m : ℕ) : 0 < A.D.eps m := by
    change 0 < ocEpsilon A.D.q A.D.Λ m
    rw [A.hq, A.hΛ]
    exact (Scales.epsilon_basic B.hq.1 R.hΛ).1
  have hres := terminal_root_reserve_bounds A.G.comps C.kW C.hkw A.stage.2.2.2.2.1
  let K := fun _ : ℕ => isoPairedKernel (A.D.termRW A.σw A.M) A.nW
  have hinv := A.stage.2.2.2.2.2.2.2.2.2
  have hlength (v u : CompIn A.G.comps) (γ : A.G.fam.Γ v u) :
      (A.G.fam.identity v u γ).record.length ≤ A.D.eps A.G.level := by
    rw [show A.D.eps A.G.level = A.D.eps A.M from congrArg A.D.eps hlevel]
    have hr := (A.stage.2.2.2.2.2.2.1 v u γ).2.2.1
    exact hr.trans ((mul_le_mul_of_nonneg_right (le_abs_self C.CL) (he (A.M + 1)).le).trans hlen)
  have hs := hsource A.D R.cap A.j₀ A.G A.law A.PW K A.φ₀ A.hφ₀ (A.M + A.Jw) C.kW
    A.aM (A.a + A.T₀) (C.Cχ * A.D.eps A.M ^ C.χw)
    (C.Cχ * A.D.eps A.M ^ C.χw) hinv
    (by rw [hlevel]; omega) (by rw [hlevel]; exact hj)
    (by rw [hlevel]; exact he _) (A.hq.symm ▸ B.hq.1) hΛ hζ hband hres.1 hres.2
    (fun v u γ _ => hlength v u γ) slot lam hlam
  have hε1 : A.D.eps A.M ≤ 1 := by
    change ocEpsilon A.D.q A.D.Λ A.M ≤ 1
    rw [A.hq, A.hΛ]
    exact (Scales.epsilon_basic B.hq.1 R.hΛ).2.1
  have hprice : C.Cχ * A.D.eps A.M ^ C.χw ≤ |C.Cχ| :=
    (mul_le_mul_of_nonneg_right (le_abs_self C.Cχ) (Real.rpow_nonneg (he _).le _)).trans
      (mul_le_of_le_one_right (abs_nonneg _) (Real.rpow_le_one (he _).le hε1 C.hχw.le))
  have hrho : (lam * A.D.eps (A.M - 1)) / A.D.eps (A.M - 1) = lam :=
    mul_div_cancel_right₀ lam (he _).ne'
  have hs' : IsScaledJetEnvelope (A.G.mass A.law)
      (weakPositiveNativeData A.M A.G slot (lam * A.D.eps (A.M - 1))).edge
      (Set.Icc (weakSlotLeft A.D A.M slot.1) (weakSlotRight A.D A.M slot.1))
      lam (fun r q => (Fintype.card (Finset.Icc 2 R.cap) : ℝ) * J (r + q)) qs qf
      (recordMajorant (A.G.mass A.law) A.G.fam) (C.Cχ * A.D.eps A.M ^ C.χw) := by
    simpa only [weakPositiveNativeData, familyLiftData, hrho, hlevel] using hs
  exact ⟨hs'.nonneg, fun v => (hs'.row_sum v).trans hprice,
    fun u => (hs'.col_sum u).trans hprice, hs'.jets⟩

/-- Select the terminal slot lift uniformly before the actual weak stage and carrier. -/
theorem terminal_positive_slot_lift : TerminalPositiveSlotLiftStatement := by
  intro B
  obtain ⟨Λ₀, hΛ₀, hscale⟩ := band_enhanced_lift_scale_bounds
    B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq B.hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro R hR C
  obtain ⟨ms, hms, hs⟩ := hscale R.Λ hR C.cr C.hcr
  have hcap : 2 ≤ R.cap := le_max_left _ _
  obtain ⟨CG, Cw, ml, _hCG, _hCw, _hml, hlift⟩ := Construction.TerminalLift.terminal_level_lift
    B.α B.s B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.q B.hq R.Λ R.hΛ B.ζ B.hζ
    R.H R.N R.slow R.order R.order R.cap R.hN hcap
  let qs := R.slow + 4 * (R.H + 1) * (R.N + R.cap) ^ 2
  let qf := max R.order (R.order + 2) + R.H * R.cap + 2 * R.N + 2 * R.cap
  obtain ⟨J, _hJ, hsource⟩ := stage_native_lift_source_exists_envelope R.bw R.hbw qs qf
  obtain ⟨chartC, hchart, mf, hflow⟩ := terminal_positive_physical_geometry
    B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq R.Λ R.hΛ B.ζ B.hζ R.N R.order
  obtain ⟨mr, hlength⟩ := terminal_record_length_floor B.hq.1 B.hq.2.1 R.hΛ C.CL
  let Cj := fun r q => (Fintype.card (Finset.Icc 2 R.cap) : ℝ) * J (r + q)
  let P := terminalPositiveParameters R CG Cw Cj |C.Cχ| chartC (abs_nonneg _) hchart
  refine ⟨P, rfl, rfl, rfl, ?_⟩
  intro j₀
  refine ⟨max (max ms ml) (max (max mf mr) (j₀ + 2)), ?_⟩
  intro A hj₀ hM
  have hmsM : ms ≤ A.M := (le_max_left ms ml).trans ((le_max_left _ _).trans hM)
  have hmlM : ml ≤ A.M := (le_max_right ms ml).trans ((le_max_left _ _).trans hM)
  have hmfM : mf ≤ A.M := (le_max_left mf mr).trans
    ((le_max_left _ _).trans ((le_max_right _ _).trans hM))
  have hmrM : mr ≤ A.M := (le_max_right mf mr).trans
    ((le_max_left _ _).trans ((le_max_right _ _).trans hM))
  have hjM : j₀ + 2 ≤ A.M := (le_max_right _ _).trans ((le_max_right _ _).trans hM)
  have hM2 : 2 ≤ A.M := hms.trans hmsM
  have hlevel : A.G.level = A.M := A.stage.2.2.1
  have hband : IsOCBandChain A.D.α A.D.q A.D.Λ A.D.ζ A.D.term A.D.κ := by
    simpa only [A.hα, A.hq, A.hΛ, A.hζ, A.term] using A.band
  have he (m : ℕ) : 0 < A.D.eps m := by
    change 0 < ocEpsilon A.D.q A.D.Λ m
    rw [A.hq, A.hΛ]
    exact (Scales.epsilon_basic B.hq.1 R.hΛ).1
  have hΛD : 1 ≤ A.D.Λ := by rw [A.hΛ]; omega
  have hζD : IsFastProfile A.D.ζ := A.hζ.symm ▸ B.hζ
  have hsc := hs A.M A.D.κ A.band A.M hmsM le_rfl
  have hradius : A.radius = C.cr * Real.sqrt (A.D.κ (A.M - 1) *
      ocTauPP B.α B.q R.Λ A.M) := by
    simp only [TerminalPositiveCase.radius, liftLength, A.hα, A.hq, A.hΛ]
  have hρ : 0 < A.radius := hradius.symm ▸ hsc.2.1
  have hcell : ocDStar A.D.q A.D.Λ A.M (A.D.kap A.M) (A.D.kap (A.M - 1)) /
      A.radius ≤ 1 := by
    simpa only [hradius, OCData.kap, A.term, Nat.min_self,
      Nat.min_eq_left (Nat.sub_le A.M 1), A.hq, A.hΛ] using hsc.2.2.1
  have hρE : A.radius / A.D.eps (A.M - 1) ≤ 1 := by
    simpa only [hradius, OCData.eps, A.hq, A.hΛ] using hsc.2.2.2
  have hρle : A.radius ≤ A.D.eps (A.M - 1) := (div_le_one (he _)).mp hρE
  have hν : 0 < A.D.kap A.M := weakData_kap_pos A.D hΛD hζD hband _
  have heρ : A.D.eps A.M ≤ A.radius := cell_scale_le_lift_radius (he _).le hν
    (native_kap_step_le A.D hΛD hζD hband _ (by omega)) hρ hcell
  have hinv := A.stage.2.2.2.2.2.2.2.2.2
  have hres := terminal_root_reserve_bounds A.G.comps C.kW C.hkw A.stage.2.2.2.2.1
  have hgeom := hflow A.D A.hα A.hq A.hΛ A.hζ A.stream R.cap A.j₀ R.bw
    A.M (A.M + A.Jw) A.G hlevel hinv.1 hinv.2.2.2.1 A.term hband hmfM
    A.radius hρ hρle
  refine ⟨hρ, heρ, hρle, ?_, hgeom, ⟨?_⟩⟩
  · simpa only [OCData.kap, A.term, Nat.min_self,
      Nat.min_eq_left (Nat.sub_le A.M 1)] using hcell
  · intro slot
    have henv := terminal_positive_case_source A qs qf J (by
      intro D Dm j G law PW K φ hφ Mnat k a b S θ hinv hi hj he hq hΛ hζ hb hm hm2 hlen
        sl lam hlam
      simpa only [one_pow, div_one, weakSlotLeft, weakSlotRight] using
        hsource ScalarH D Dm j G law PW K K φ hφ Mnat k a b S θ hinv hi hj he hq hΛ hζ hb
          hm hm2 hlen sl lam hlam (fun _ => 1) (Or.inl rfl))
      hM2 (by rw [hj₀]; omega)
      (by simpa only [OCData.eps, A.hq, A.hΛ] using hlength A.M hmrM)
      slot (A.radius / A.D.eps (A.M - 1)) (div_nonneg hρ.le (he _).le)
    have hcancel : A.radius / A.D.eps (A.M - 1) * A.D.eps (A.M - 1) = A.radius :=
      div_mul_cancel₀ _ (he _).ne'
    rw [hcancel] at henv
    have hslotLift := hlift ScalarH A.D A.hα A.hq A.hΛ A.hζ A.stream
      hband R.cap A.j₀ (A.M + A.Jw) R.bw A.G C.kW R.hbw
      hinv.2.2.2.2.2.1 hinv.2.2.2.2.1 hinv.1
      (by rw [hlevel]; exact hmlM) (by rw [hlevel, A.term])
      (by rw [hlevel, hj₀]; omega) A.stage.2.2.2.1 hres.1 hres.2
      slot A.radius hρ (by simpa only [hlevel] using hcell)
      (by simpa only [hlevel] using hρE) (A.G.mass A.law)
      (fun v => Construction.Preservation.Buffer.birth_compMass_pos (A.hq.symm ▸ B.hq.1) (A.hΛ.symm ▸ R.hΛ) A.law v.1)
      le_rfl Cj (recordMajorant (A.G.mass A.law) A.G.fam) |C.Cχ|
      (by intro v u d hd; have := (Finset.mem_Icc.mp d.prop).2; omega)
      (by simpa only [hlevel, weakPositiveNativeData, weakSlotLeft, weakSlotRight] using henv)
    exact terminalOriginalSlotLift P A.M A.G (A.G.mass A.law) slot A.radius hcap le_rfl
      (recordMajorant (A.G.mass A.law) A.G.fam) hslotLift.2.choose
      (by simpa only [hlevel, P, terminalPositiveParameters, weakPositiveNativeData,
        weakSlotLeft, weakSlotRight] using hslotLift.1)
      (by simpa only [hlevel, P, terminalPositiveParameters, weakPositiveNativeData,
        weakSlotLeft, weakSlotRight] using hslotLift.2.choose_spec.1)
      (by simpa only [hlevel, P, terminalPositiveParameters, weakPositiveNativeData,
        weakSlotLeft, weakSlotRight] using hslotLift.2.choose_spec.2)

end AVRegularity.Finite.TerminalLift
end
end
end

section
section
/-! Spatial regularity of terminal positive pulses at their literal preparation radius.
The arbitrary supplied sequence is identified with the common slot lift on each active slot. -/

@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
open scoped Classical
namespace AVRegularity.Finite.TerminalLift
open WeakLift Construction.Preservation.FullLift EntryWeakProofs

/-- Actual chart data, after the numerical menu of the radius-generic slot lift has been chosen. -/
structure TerminalPositiveChartCase {B : WeakParentBase} {R : TerminalPositiveRequest B}
    {C : TerminalPositiveConstants} (P : WeakPositiveParameters R.N R.H R.order) where
  A : TerminalPositiveCase R C
  radius_pos : 0 < A.radius
  geometry : PositivePhysicalGeometry (N := R.N) (U := R.order) P.chartC A.M A.G A.radius
  slotLift : ∀ slot : OddSlot, WeakPositiveSlot P A.M A.G (A.G.mass A.law) slot A.radius
  sX : ℕ
  sZ : ℕ
  coeff : ℤ → ℕ → ℕ → LiftCoeff (CompIn A.G.comps) (fun v => ScalarH v.1.root)
  sequence : ∀ slot : OddSlot, IsLiftSequence (weakPositiveNativeData A.M A.G slot A.radius)
    sX sZ (weakSlotLeft A.D A.M slot.1) (weakSlotRight A.D A.M slot.1) R.N R.H (coeff slot.1)
  t : ℝ
  f : Vec 2 → ∀ v : CompIn A.G.comps, ScalarH v.1.root
  regular : ContDiff ℝ (R.order + R.N : ℕ) f
  periodic : IsZ2Periodic f

/-- The positive pulse with the actual terminal scale and frozen physical charts. -/
def terminalPositivePulse {B : WeakParentBase} {R : TerminalPositiveRequest B}
    {C : TerminalPositiveConstants} {P : WeakPositiveParameters R.N R.H R.order}
    (V : TerminalPositiveChartCase (R := R) (C := C) P) (k : ℤ) : Vec 2 → ∀ v : CompIn V.A.G.comps, ScalarH v.1.root :=
  pulsePhysicalLift (V.A.D.cellScaleSq V.A.M) V.A.radius (V.A.D.eps V.A.M)
    (ocDStar V.A.D.q V.A.D.Λ V.A.M (V.A.D.κ V.A.M) (V.A.D.κ (V.A.M - 1)) / V.A.radius)
    R.N R.H (positiveLiftCoefficients V.coeff k)
    (fun _ y => V.A.D.flowOf (V.A.M - 1) V.t y (V.A.D.slotAnchor V.A.M k))
    (fun _ y => V.A.D.flowOf (V.A.M - 1) (V.A.D.slotAnchor V.A.M k) y V.t)
    (fun _ => V.f) V.t

/-- The literal pulse window contains every time with a nonzero cutoff. -/
theorem terminal_positive_active_time {B : WeakParentBase} {R : TerminalPositiveRequest B}
    {C : TerminalPositiveConstants} {P : WeakPositiveParameters R.N R.H R.order}
    (V : TerminalPositiveChartCase (R := R) (C := C) P) (slot : OddSlot)
    (hcut : ocCutoff V.A.D.α V.A.D.q V.A.D.Λ V.A.M slot.1 V.t ≠ 0) :
    (V.A.D.cellScaleSq V.A.M)⁻¹ * V.t ∈
      Set.Icc (weakSlotLeft V.A.D V.A.M slot.1) (weakSlotRight V.A.D V.A.M slot.1) := by
  have hΛ : 1 ≤ V.A.D.Λ := by have := V.geometry.Λ_ge; omega
  have hc := weakData_cellScaleSq_pos V.A.D hΛ V.geometry.fast V.geometry.band V.A.M
  have ht := Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero
    (Construction.Stream.ocTau_pos (α := V.A.D.α) (q := V.A.D.q) (m := V.A.M) hΛ) hcut
  rw [inv_mul_eq_div]
  exact ⟨div_le_div_of_nonneg_right ht.1 hc.le, div_le_div_of_nonneg_right ht.2 hc.le⟩

/-- Positive terminal pulses preserve the requested regularity and physical periodicity. -/
theorem terminal_positive_pulse_regular {B : WeakParentBase} {R : TerminalPositiveRequest B}
    {C : TerminalPositiveConstants} {P : WeakPositiveParameters R.N R.H R.order}
    (V : TerminalPositiveChartCase (R := R) (C := C) P) (slot : OddSlot)
    (hcut : ocCutoff V.A.D.α V.A.D.q V.A.D.Λ V.A.M slot.1 V.t ≠ 0) :
    (∀ v, ContDiff ℝ (R.order : ℕ) (fun x => terminalPositivePulse V slot.1 x v)) ∧
      IsZ2Periodic (terminalPositivePulse V slot.1) := by
  have ht := terminal_positive_active_time V slot hcut
  have hid := (weak_positive_support_identification R.N R.H R.order P V.A.D R.cap V.A.j₀
    R.bw V.A.M V.A.G (V.A.G.mass V.A.law) slot V.A.radius (V.slotLift slot)
    V.sX V.sZ (V.coeff slot.1) (V.sequence slot)).1
  have hg := weak_positive_graded_recurrence R.N R.H R.order P V.A.D R.cap V.A.j₀
    R.bw V.A.M V.A.G (V.A.G.mass V.A.law) slot V.A.radius (V.slotLift slot)
  have hΛ : 1 ≤ V.A.D.Λ := by have := V.geometry.Λ_ge; omega
  let Φ := fun x => V.A.D.flowOf (V.A.M - 1) V.t x (V.A.D.slotAnchor V.A.M slot.1)
  let Ψ := fun x => V.A.D.flowOf (V.A.M - 1) (V.A.D.slotAnchor V.A.M slot.1) x V.t
  have hΦ : ContDiff ℝ (R.order + R.N : ℕ) Φ :=
    (CycleReference.streamFlow_spatial_smooth (V.A.D.hΦ (V.A.M - 1)) V.t
      (V.A.D.slotAnchor V.A.M slot.1)).of_le (by simp)
  have hΨ : ContDiff ℝ (R.order : ℕ) Ψ :=
    (CycleReference.streamFlow_spatial_smooth (V.A.D.hΦ (V.A.M - 1))
      (V.A.D.slotAnchor V.A.M slot.1) V.t).of_le (by simp)
  constructor
  · intro v
    apply pulsePhysicalLift_static_contDiff_of_boxes _ _ _ _ R.N R.H R.order _ Φ Ψ
      V.f V.t V.regular hΦ hΨ
    intro hh hhh n hn m hm α v' u'
    by_cases hn0 : n = 0
    · simp only [positiveLiftCoefficients, hn0, ite_true, Pi.zero_apply]
      exact IsBoxSmooth.zero
    · have he : (fun X z => positiveLiftCoefficients V.coeff slot.1 hh n m α
          ((V.A.D.cellScaleSq V.A.M)⁻¹ * V.t) X z v' u') =
        fun X z => (V.slotLift slot).coeff hh n m α
          ((V.A.D.cellScaleSq V.A.M)⁻¹ * V.t) X z v' u' := by
        funext X z
        exact (by simpa only [positiveLiftCoefficients, hn0, ite_false] using
          (hid hh hhh n m α _ ht X z v' u'))
      rw [he]
      exact (hg hh hhh n hn).box m hm α v' u' _ ht
  · obtain ⟨J, hJ⟩ := TorusCompatible.ocEpsilon_inv_natCast V.A.D.q V.A.D.Λ V.A.M
    apply pulsePhysicalLift_static_periodic _ _ _ _ R.N R.H _ Φ Ψ V.f V.t
      V.radius_pos.ne' hJ
      (fun p Y => native_flow_latticeShift V.A.D _ _ _ p Y)
      (fun p Y => native_flow_latticeShift V.A.D _ _ _ p Y) V.periodic
    · intro hh hhh n _hn m _hm α p X z v u
      by_cases hn0 : n = 0
      · simp only [positiveLiftCoefficients, hn0, ite_true, Pi.zero_apply]
      · simp only [positiveLiftCoefficients, hn0, ite_false]
        rw [hid hh hhh n m α _ ht, hid hh hhh n m α _ ht]
        exact weak_positive_slot_coefficient_slow_shift (V.slotLift slot)
          (weakData_cellScaleSq_pos V.A.D hΛ V.geometry.fast V.geometry.band 1).ne'
          V.geometry.level V.geometry.torus p hh hhh n m α _ ht X z v u
    · intro hh hhh n _hn m _hm α X v u
      by_cases hn0 : n = 0
      · simp only [positiveLiftCoefficients, hn0, ite_true, Pi.zero_apply]
        exact fun _ _ => rfl
      · simp only [positiveLiftCoefficients, hn0, ite_false]
        intro p z
        change V.coeff slot.1 hh n m α ((V.A.D.cellScaleSq V.A.M)⁻¹ * V.t) X
          (z + latticeShift p) v u =
          V.coeff slot.1 hh n m α ((V.A.D.cellScaleSq V.A.M)⁻¹ * V.t) X z v u
        rw [hid hh hhh n m α _ ht, hid hh hhh n m α _ ht]
        exact ((V.slotLift slot).ambient.2.2.2.2.2.1 hh hhh n m α v u _ ht).2 X p z

/-- The normalized positive correction as a finite sum of time-frozen pulses. -/
def terminalPositiveGlue {B : WeakParentBase} {R : TerminalPositiveRequest B}
    {C : TerminalPositiveConstants} {P : WeakPositiveParameters R.N R.H R.order}
    (V : TerminalPositiveChartCase (R := R) (C := C) P) : Vec 2 → CompSpace V.A.G.comps :=
  fun x => ∑ k ∈ ocObsPulses V.A.D.α V.A.D.q V.A.D.Λ V.A.M V.t V.t,
    ocCutoff V.A.D.α V.A.D.q V.A.D.Λ V.A.M k V.t •
      toCompSpace (V.A.G.mass V.A.law) (terminalPositivePulse V k x)

/-- Finite cutoff gluing preserves the regularity and periodicity of active positive pulses. -/
theorem terminal_positive_glue_regular {B : WeakParentBase} {R : TerminalPositiveRequest B}
    {C : TerminalPositiveConstants} {P : WeakPositiveParameters R.N R.H R.order}
    (V : TerminalPositiveChartCase (R := R) (C := C) P) :
    ContDiff ℝ (R.order : ℕ) (terminalPositiveGlue V) ∧ IsZ2Periodic (terminalPositiveGlue V) := by
  let kset := ocObsPulses V.A.D.α V.A.D.q V.A.D.Λ V.A.M V.t V.t
  have hp (k : ℤ) (hk : k ∈ kset)
      (hw : ocCutoff V.A.D.α V.A.D.q V.A.D.Λ V.A.M k V.t ≠ 0) :
      ContDiff ℝ (R.order : ℕ) (fun x => toCompSpace (V.A.G.mass V.A.law)
        (terminalPositivePulse V k x)) ∧
      IsZ2Periodic (fun x => toCompSpace (V.A.G.mass V.A.law) (terminalPositivePulse V k x)) := by
    obtain ⟨hcd, hper⟩ := terminal_positive_pulse_regular V ⟨k, (Finset.mem_filter.mp hk).2.1⟩ hw
    exact EntryTerminal.Ingredients.compField_contDiff_periodic (V.A.G.mass V.A.law) R.order
      (fun v x => terminalPositivePulse V k x v) hcd (fun v p x => congrFun (hper p x) v)
  constructor
  · apply ContDiff.sum
    intro k hk
    by_cases hw : ocCutoff V.A.D.α V.A.D.q V.A.D.Λ V.A.M k V.t = 0
    · simpa only [hw, zero_smul] using
        (contDiff_const : ContDiff ℝ (R.order : ℕ) (fun _ : Vec 2 => (0 : CompSpace V.A.G.comps)))
    · exact (hp k hk hw).1.const_smul _
  · intro p x
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hw : ocCutoff V.A.D.α V.A.D.q V.A.D.Λ V.A.M k V.t = 0
    · simp only [hw, zero_smul]
    · exact congrArg (fun y => ocCutoff V.A.D.α V.A.D.q V.A.D.Λ V.A.M k V.t • y)
        ((hp k hk hw).2 p x)

/-- Freeze the actual time-dependent input and chart at their physical output time. -/
theorem terminal_positive_frozen_pulse {B : WeakParentBase} {R : TerminalPositiveRequest B}
    {C : TerminalPositiveConstants} {P : WeakPositiveParameters R.N R.H R.order}
    (V : TerminalPositiveChartCase (R := R) (C := C) P) (k : ℤ) :
    pulsePhysicalLift (V.A.D.cellScaleSq V.A.M) V.A.radius (V.A.D.eps V.A.M)
      (ocDStar V.A.D.q V.A.D.Λ V.A.M (V.A.D.κ V.A.M) (V.A.D.κ (V.A.M - 1)) / V.A.radius)
      R.N R.H (positiveLiftCoefficients V.coeff k)
      (fun s y => V.A.D.flowOf (V.A.M - 1) s y (V.A.D.slotAnchor V.A.M k))
      (fun s y => V.A.D.flowOf (V.A.M - 1) (V.A.D.slotAnchor V.A.M k) y s)
      (fun _ => V.f) V.t = terminalPositivePulse V k := by
  have hΛ : 1 ≤ V.A.D.Λ := by have := V.geometry.Λ_ge; omega
  have hc := weakData_cellScaleSq_pos V.A.D hΛ V.geometry.fast V.geometry.band V.A.M
  rw [pulsePhysicalLift_freeze_time]
  simp only [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  rfl

/-- The positive glued field is exactly the terminal lift minus its input. -/
theorem terminal_positive_difference_eq_glue {B : WeakParentBase}
    {R : TerminalPositiveRequest B} {C : TerminalPositiveConstants}
    {P : WeakPositiveParameters R.N R.H R.order} (V : TerminalPositiveChartCase (R := R) (C := C) P) :
    compField (V.A.G.mass V.A.law)
        (termLiftedRep V.A.G V.A.M R.N R.H C.cr V.coeff (fun _ => V.f) V.t) -
      compField (V.A.G.mass V.A.law) V.f = terminalPositiveGlue V := by
  have hΛ : 1 ≤ V.A.D.Λ := by have := V.geometry.Λ_ge; omega
  have hc := weakData_cellScaleSq_pos V.A.D hΛ V.geometry.fast V.geometry.band V.A.M
  have hτ := Construction.Stream.ocTau_pos (α := V.A.D.α) (q := V.A.D.q) (m := V.A.M) hΛ
  let F := termLiftedRep V.A.G V.A.M R.N R.H C.cr V.coeff (fun _ => V.f) V.t
  have he (v : CompIn V.A.G.comps) (x : Vec 2) : F x v - V.f x v =
      ∑ k ∈ ocObsPulses V.A.D.α V.A.D.q V.A.D.Λ V.A.M V.t V.t,
        ocCutoff V.A.D.α V.A.D.q V.A.D.Λ V.A.M k V.t • terminalPositivePulse V k x v := by
    have hdiff : F x v -
        (∑ k ∈ ocObsPulses V.A.D.α V.A.D.q V.A.D.Λ V.A.M V.t V.t,
          ocCutoff V.A.D.α V.A.D.q V.A.D.Λ V.A.M k V.t • terminalPositivePulse V k x v) = V.f x v := by
      simp only [F, termLiftedRep, gluedLift, Finset.sum_apply, Pi.smul_apply]
      rw [← Finset.sum_sub_distrib]
      trans ∑ k ∈ ocObsPulses V.A.D.α V.A.D.q V.A.D.Λ V.A.M V.t V.t,
        ocCutoff V.A.D.α V.A.D.q V.A.D.Λ V.A.M k V.t • V.f x v
      · apply Finset.sum_congr rfl
        intro k hk
        by_cases hw : ocCutoff V.A.D.α V.A.D.q V.A.D.Λ V.A.M k V.t = 0
        · simp only [hw, zero_smul, sub_self]
        · rw [← smul_sub, ← terminal_positive_frozen_pulse V k]
          apply congrArg (fun y : ℝ => ocCutoff V.A.D.α V.A.D.q V.A.D.Λ V.A.M k V.t • y)
          exact Finite.pulse_positive_difference_time
            (weakPositiveNativeData V.A.M V.A.G ⟨k, (Finset.mem_filter.mp hk).2.1⟩ V.A.radius)
            V.sX V.sZ _ _ R.N R.H V.coeff k (V.sequence ⟨k, (Finset.mem_filter.mp hk).2.1⟩)
            _ _ _ _ V.t hc.ne' V.radius_pos.ne'
            (terminal_positive_active_time V ⟨k, (Finset.mem_filter.mp hk).2.1⟩ hw)
            _ _ (fun _ => V.f) x
            (weak_chart_inverse V.A.D (V.A.M - 1) V.t (V.A.D.slotAnchor V.A.M k) x) v
      · rw [← Finset.sum_smul, obs_cutoff_sum_one _ _ _ _ _ hτ, one_smul]
    linarith only [hdiff]
  funext x
  apply PiLp.ext
  intro v
  change (Real.sqrt (V.A.G.mass V.A.law v))⁻¹ * F x v -
    (Real.sqrt (V.A.G.mass V.A.law v))⁻¹ * V.f x v = _
  rw [← mul_sub, he]
  simp only [terminalPositiveGlue, WithLp.ofLp_sum, Finset.sum_apply,
    WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  change (Real.sqrt (V.A.G.mass V.A.law v))⁻¹ *
    (ocCutoff V.A.D.α V.A.D.q V.A.D.Λ V.A.M k V.t * terminalPositivePulse V k x v) =
    ocCutoff V.A.D.α V.A.D.q V.A.D.Λ V.A.M k V.t *
      ((Real.sqrt (V.A.G.mass V.A.law v))⁻¹ * terminalPositivePulse V k x v)
  ring

/-- At zero truncation order the literal terminal lift is exactly its input, even when the
schedule permits negative exponents. No positive-order slot lift is needed. -/
theorem terminal_zero_order_lift_eq {D : OCData} {Dm j₀ : ℕ} {bw : ℝ}
    (G : GenStage D ScalarH Dm bw j₀) (M H sX sZ : ℕ) (cr : ℝ)
    (Cc : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (hseq : ∀ slot : OddSlot, IsLiftSequence (weakPositiveNativeData M G slot (cr * liftLength D M))
      sX sZ (weakSlotLeft D M slot.1) (weakSlotRight D M slot.1) 0 H (Cc slot.1))
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (hρ : 0 < cr * liftLength D M)
    (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root) (t : ℝ) :
    termLiftedRep G M 0 H cr Cc g t = g t := by
  have hc := weakData_cellScaleSq_pos D hΛ hζ hband M
  have hτ := Construction.Stream.ocTau_pos (α := D.α) (q := D.q) (m := M) hΛ
  funext x v
  simp only [termLiftedRep, gluedLift, Finset.sum_apply, Pi.smul_apply]
  trans ∑ k ∈ ocObsPulses D.α D.q D.Λ M t t, ocCutoff D.α D.q D.Λ M k t • g t x v
  · apply Finset.sum_congr rfl
    intro k hk
    by_cases hw : ocCutoff D.α D.q D.Λ M k t = 0
    · simp only [hw, zero_smul]
    · have ht := Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hw
      have htcell : (D.cellScaleSq M)⁻¹ * t ∈ Set.Icc
          (weakSlotLeft D M k) (weakSlotRight D M k) := by
        rw [inv_mul_eq_div]
        exact ⟨div_le_div_of_nonneg_right ht.1 hc.le, div_le_div_of_nonneg_right ht.2 hc.le⟩
      have hid := Finite.pulse_positive_difference_time
        (weakPositiveNativeData M G ⟨k, (Finset.mem_filter.mp hk).2.1⟩ (cr * liftLength D M))
        sX sZ _ _ 0 H Cc k (hseq ⟨k, (Finset.mem_filter.mp hk).2.1⟩)
        (D.cellScaleSq M) (cr * liftLength D M) (D.eps M)
        (ocDStar D.q D.Λ M (D.κ M) (D.κ (M - 1)) / (cr * liftLength D M))
        t hc.ne' hρ.ne' htcell
        (fun s y => D.flowOf (M - 1) s y (D.slotAnchor M k))
        (fun s y => D.flowOf (M - 1) (D.slotAnchor M k) y s)
        g x (weak_chart_inverse D (M - 1) t (D.slotAnchor M k) x) v
      have hz : pulsePhysicalLift (D.cellScaleSq M) (cr * liftLength D M) (D.eps M)
          (ocDStar D.q D.Λ M (D.κ M) (D.κ (M - 1)) / (cr * liftLength D M)) 0 H
          (positiveLiftCoefficients Cc k)
          (fun s y => D.flowOf (M - 1) s y (D.slotAnchor M k))
          (fun s y => D.flowOf (M - 1) (D.slotAnchor M k) y s) g t x v = 0 := by
        simp only [pulsePhysicalLift, diagSample, Finset.sum_apply, Pi.smul_apply,
          Nat.zero_add, Finset.sum_range_one, positiveLiftCoefficients, ite_true,
          liftApply, Pi.zero_apply, zero_apply, Finset.sum_const_zero, smul_zero]
      rw [hz, sub_zero] at hid
      exact congrArg (fun y : ℝ => ocCutoff D.α D.q D.Λ M k t • y) hid
  · rw [← Finset.sum_smul, obs_cutoff_sum_one _ _ _ _ _ hτ, one_smul]

/-- Terminal synthesis at one time uses only the input at that time.
Keeping this clean-context calculation separate avoids expanding the full stage in `congr`. -/
theorem terminal_lift_freeze_input {D : OCData} {Dm j₀ : ℕ} {bw : ℝ}
    (G : GenStage D ScalarH Dm bw j₀) (M N H : ℕ) (cr : ℝ)
    (Cc : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => ScalarH v.1.root))
    (g : ℝ → Vec 2 → ∀ v : CompIn G.comps, ScalarH v.1.root) (t : ℝ)
    (hc : 0 < D.cellScaleSq M) :
    termLiftedRep G M N H cr Cc g t = termLiftedRep G M N H cr Cc (fun _ => g t) t := by
  funext x
  unfold termLiftedRep gluedLift
  apply Finset.sum_congr rfl
  intro k _
  apply congrArg (fun y : ∀ v : CompIn G.comps, ScalarH v.1.root =>
    ocCutoff D.α D.q D.Λ M k t • y)
  conv_lhs => rw [pulsePhysicalLift_freeze_time]
  conv_rhs => rw [pulsePhysicalLift_freeze_time]
  simp only [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]

end AVRegularity.Finite.TerminalLift
end
end

section
/-! The actual terminal covariance representative is the finite polynomial of the normalized
constant readout. Uniform matrix and readout prices precede the level and represented datum.
This model does not use the terminal positive lift or the weak certificate reserve. -/

@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Finite.TerminalLift
open Construction.Preservation.FullLift

/-- Normalize a covariance image using only the represented input values and finite smoothness. -/
theorem terminal_covariance_classical_model {S S' : Finset Comp} {K L n kin : ℕ}
    (m : ℕ) (E η : ℝ) (π : CompIn S → ℝ) (π' : CompIn S' → ℝ) (hπ : ∀ v, 0 < π v)
    (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : ∀ i j, A i j = A j i) (p : ℕ)
    (r : Representation (CompSpace S')) (hr : IsRepresentationAt E kin r) (hp : 2 * p ≤ kin)
    (Z : ∀ c : CompIn S', TorusHk K (ScalarH c.1.root))
    (W : ∀ v : CompIn S, TorusHk L (ScalarH v.1.root))
    (a : Vec 2 → ∀ v : CompIn S, ScalarH v.1.root)
    (hZ : IsRepOf π' (fun c => truncateTorusHk (Nat.zero_le K) (Z c)) r.value)
    (hW : ∀ v, IsCovImage (covPolyP A p) (succReadout (hr := ScalarH) m E η K Z v) (W v))
    (ha : ∀ v, IsClassicalRep (W v) (fun x => a x v) n) :
    compField π a = covPolyP A p (fun x => readoutCLM m E η π π' (r.value x)) := by
  let R := readoutCLM m E η π π'
  let g : Vec 2 → CompSpace S := fun x => R (r.value x)
  obtain ⟨hrcd, hrper⟩ := WeakLift.representation_value_contDiff_periodic r hr
  have hg : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) g :=
    (R.contDiff.comp hrcd).of_le (by exact_mod_cast hp)
  have hgp : AVenhance.IsZ2Periodic g := fun k x => congrArg R (hrper k x)
  let V (v : CompIn S) : CompSpace S →L[ℝ] ℝ :=
    Real.sqrt (π v) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : CompIn S => ℝ) v
  have hv (v : CompIn S) : (fun x => a x v) = covPolyP A p (fun x => V v (g x)) := by
    apply terminal_covariance_rep_eq_from_value (E := ℝ) A hA p
      (succReadout (hr := ScalarH) m E η K Z v) (W v)
      (fun x => V v (g x)) (fun x => a x v)
      ((V v).contDiff.comp hg)
      (fun k x => congrArg (V v) (hgp k x)) _ (hW v) (ha v)
    exact terminal_readout_value_of_rep m E η π π' hπ Z r.value hZ v
  funext x
  apply PiLp.ext
  intro v
  change (Real.sqrt (π v))⁻¹ * a x v = WithLp.ofLp (covPolyP A p g x) v
  rw [congrFun (hv v) x]
  have he := terminal_covariance_polynomial_clm A (V v) p g hg x
  change Real.sqrt (π v) * WithLp.ofLp (covPolyP A p g x) v =
    covPolyP A p (fun y => V v (g y)) x at he
  rw [← he, ← mul_assoc, inv_mul_cancel₀ (Real.sqrt_pos.mpr (hπ v)).ne', one_mul]

/-- The terminal covariance model has uniform constants without a terminal lift certificate. -/
theorem terminal_covariance_model : TerminalCovarianceModelStatement := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Bcov, hBcov, Λ₀, hΛ₀, hcov⟩ := terminal_covariance_uniform_matrix_bound
    hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ φ₀ hφ₀ _hφcd _hφnn _hφint _hφsupp bw _hbw _hbw1 Jw Lw dW DW T₀ η₀ σw χw
    _hJ _hT hη _hη1 _hσ _hσ1 _hχ PT QT NT pT RT AT k₀ LcT LoT LfT LpT tT _hsched Lr
  refine ⟨0, 0, ?_⟩
  intro sXT sZT _hsXT _hsZT cr _hcr _hcr1 Kw Kp nW kW CL Cχ c C Cw cH _hc _hcH _hkw
  let Cread := terminalReadoutConstant (termAlphabet NT pT DW dW) RT cH
  let B := max Bcov Cread
  have hB : 0 ≤ B := (zero_le_one.trans hBcov).trans (le_max_left _ _)
  refine ⟨B, hB, fun j₀ => ⟨2, ?_⟩⟩
  intro M hM D hDα hDq hDΛ hDζ _hstream hband _hterm PW a Gw lawW aM hstage tp Pterm _hprep
    lawT Gt' hlaw hactual Kz Z CcT PZ aRep hlift t ht r hr hv
  have hroots : ∀ v ∈ Gw.comps, v.births = [] := fun v hv => hstage.2.2.2.2.1 ⟨v, hv⟩
  have hsub : (Gt'.retained M 1 RT).comps ⊆
      succExtComps M (termAlphabet NT pT DW dW) RT Gw.comps := by
    intro v hv
    have hv' : v ∈ Gt'.comps := (Finset.mem_filter.mp hv).1
    rw [hactual.2.2.1, hstage.2.2.1] at hv'
    exact hv'
  have hR := terminal_readout_bounds D.q D.Λ M (hDq.symm ▸ hq.1)
    (hDΛ.symm ▸ hΛ₀.trans hΛ) (by omega) lawW lawT η₀ (termAlphabet NT pT DW dW)
    RT Gw.comps (Gt'.retained M 1 RT).comps hlaw.1
    (by rw [hlaw.2.2.2.2.2.1]; positivity) hη.le hroots hsub
  rw [hlaw.2.2.1] at hR
  refine ⟨hR.trans (le_max_right _ _), pT, termCovPrimitive D M tp t, by omega,
    EntryTerminal.Ingredients.termCovPrimitive_entry_symm D (by omega)
      (hDζ.symm ▸ hζ) M tp t, ?_, ?_⟩
  · intro i j
    have hband' : IsOCBandChain α q Λ ζ M D.κ := by
      simpa only [hDα, hDq, hDΛ, hDζ] using hband
    have hb := hcov Λ hΛ M hM D.κ hband' tp t i j
    change |ocCovariance D.α D.q D.Λ D.ζ M (D.κ M) (D.κ (M - 1)) tp t i j| ≤
      B * ocEpsilon D.q D.Λ (M - 1) ^ 2
    rw [hDα, hDq, hDΛ, hDζ]
    exact hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
  · apply congrArg (fun f => f - fun x => readoutCLM M (D.eps (M - 1)) η₀
        (Gw.mass lawW) ((Gt'.retained M 1 RT).mass lawT) (r.value x))
    exact terminal_covariance_classical_model M (D.eps (M - 1)) η₀
      (Gw.mass lawW) ((Gt'.retained M 1 RT).mass lawT)
      (fun v => Construction.Preservation.Buffer.birth_compMass_pos
        (hDq.symm ▸ hq.1) (hDΛ.symm ▸ hΛ₀.trans hΛ) lawW v.1)
      (termCovPrimitive D M tp t)
      (EntryTerminal.Ingredients.termCovPrimitive_entry_symm D (by omega)
        (hDζ.symm ▸ hζ) M tp t) pT r hr (by omega)
      (fun v => Z v t) (fun v => PZ v t) (aRep t) hv
      (fun v => (hlift.2 v t ht).1) (fun v => (hlift.2 v t ht).2)

end AVRegularity.Finite.TerminalLift
end
end

section
/-! The identity-free covariance polynomial has only positive input derivatives. The finite
word estimate and the existing representation normalization give its physical profile price,
with no dimension, component-count or terminal lift-certificate factor. -/

@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Finite.TerminalLift
open Construction.Preservation.FullLift

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Remove the sole identity term before estimating any covariance derivative. -/
theorem terminal_covariance_positive_expansion (A : Matrix (Fin 2) (Fin 2) ℝ)
    (p : ℕ) (f : Vec 2 → V) :
    covPolyP A p f - f = fun x => ∑ n ∈ Finset.range p,
      ((n + 1).factorial : ℝ)⁻¹ • (covOperator A)^[n + 1] f x := by
  funext x
  unfold covPolyP
  simp only [Pi.sub_apply]
  rw [Finset.sum_apply, Finset.sum_range_succ']
  simp only [Pi.smul_apply, Nat.factorial_zero, Nat.cast_one, inv_one,
    Function.iterate_zero_apply, one_smul]
  exact add_sub_cancel_right _ _

/-- One constant controls all finite tested words of the covariance correction. -/
theorem terminal_covariance_correction_word_bound (A : Matrix (Fin 2) (Fin 2) ℝ)
    (E B : ℝ) (hE : 0 < E) (hB : 0 ≤ B) (hA : ∀ i j, |A i j| ≤ B * E ^ 2)
    (R : V →L[ℝ] W) (hR : ‖R‖ ≤ B) (k kin p : ℕ) (hp : k + 2 * p ≤ kin)
    (f : Vec 2 → V) (hf : ContDiff ℝ (kin : ℕ∞) f)
    (r : ℕ) (hr : r ≤ k) (β : DerivativeWord2 r) (x : Vec 2) :
    E ^ r * ‖orderedDerivative β
      (covPolyP A p (fun y => R (f y)) - fun y => R (f y)) x‖ ≤
      ((kin : ℝ) * (1 + 4 * B) ^ kin * B * ((2 : ℝ) ^ kin * (kin + 1))) *
        ∑ α ∈ multiIndicesBetween 1 kin, E ^ (α 0 + α 1) * ‖partialDerivative α f x‖ := by
  let F : Vec 2 → W := fun y => R (f y)
  let Y := ∑ α ∈ multiIndicesBetween 1 kin, E ^ (α 0 + α 1) * ‖partialDerivative α f x‖
  have hY : 0 ≤ Y := Finset.sum_nonneg fun α _ =>
    mul_nonneg (pow_nonneg hE.le _) (norm_nonneg _)
  have hcoef (n : ℕ) : 0 ≤ ((n + 1).factorial : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hcoef1 (n : ℕ) : ((n + 1).factorial : ℝ)⁻¹ ≤ 1 := by
    rw [inv_eq_one_div]
    exact (div_le_one (by exact_mod_cast Nat.factorial_pos (n + 1))).mpr
      (by exact_mod_cast Nat.one_le_of_lt (Nat.factorial_pos (n + 1)))
  have hreg (n : ℕ) (hn : n ∈ Finset.range p) :
      ContDiff ℝ (r : ℕ∞) ((covOperator A)^[n + 1] F) := by
    apply covOperator_iterate_contDiff A (n + 1) r F
    exact (R.contDiff.comp hf).of_le (by exact_mod_cast
      (by have := Finset.mem_range.mp hn; omega : r + 2 * (n + 1) ≤ kin))
  have he : orderedDerivative β (covPolyP A p F - F) = fun y => ∑ n ∈ Finset.range p,
      ((n + 1).factorial : ℝ)⁻¹ • orderedDerivative β ((covOperator A)^[n + 1] F) y := by
    rw [terminal_covariance_positive_expansion]
    simpa only [one_smul] using CoarseFluxDiff.orderedDerivative_sum_smul β
      (Finset.range p) 1 (fun n => ((n + 1).factorial : ℝ)⁻¹) hreg
  have hterm (n : ℕ) (hn : n ∈ Finset.range p) : E ^ r *
      ‖((n + 1).factorial : ℝ)⁻¹ • orderedDerivative β ((covOperator A)^[n + 1] F) x‖ ≤
      ((1 + 4 * B) ^ kin * B * ((2 : ℝ) ^ kin * (kin + 1))) * Y := by
    have hnkin : n + 1 ≤ kin := by have := Finset.mem_range.mp hn; omega
    have hj : r + 2 * (n + 1) ≤ kin := by have := Finset.mem_range.mp hn; omega
    have hi := terminal_covariance_iterate_word_bound A E B hE hB hA (n + 1) r F
      ((R.contDiff.comp hf).of_le (by exact_mod_cast hj)) β x
    have hnorm := R.norm_iteratedFDeriv_comp_left (n := r + 2 * (n + 1))
      (hf.contDiffAt (x := x)) (WithTop.coe_le_coe.mpr (by exact_mod_cast hj))
    have hinput := WeakLift.weakPositive_scaled_full_jet_le hE.le
      (by omega : 1 ≤ r + 2 * (n + 1)) hj f hf x
    have hpow : (4 * B) ^ (n + 1) ≤ (1 + 4 * B) ^ kin :=
      (pow_le_pow_left₀ (mul_nonneg (by norm_num) hB) (by linarith only []) _).trans
        (pow_le_pow_right₀ (by linarith only [hB] : 1 ≤ 1 + 4 * B) hnkin)
    have hBn : 0 ≤ (1 + 4 * B) ^ kin := pow_nonneg (by linarith only [hB]) _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hcoef n), mul_left_comm (E ^ r)]
    calc
      _ ≤ E ^ r * ‖orderedDerivative β ((covOperator A)^[n + 1] F) x‖ :=
        mul_le_of_le_one_left (mul_nonneg (pow_nonneg hE.le _) (norm_nonneg _)) (hcoef1 n)
      _ ≤ (4 * B) ^ (n + 1) *
          (E ^ (r + 2 * (n + 1)) * ‖iteratedFDeriv ℝ (r + 2 * (n + 1)) F x‖) := hi
      _ ≤ (1 + 4 * B) ^ kin * (E ^ (r + 2 * (n + 1)) *
          (B * ‖iteratedFDeriv ℝ (r + 2 * (n + 1)) f x‖)) :=
        mul_le_mul hpow
          (mul_le_mul_of_nonneg_left
            (hnorm.trans (mul_le_mul_of_nonneg_right hR (norm_nonneg _))) (pow_nonneg hE.le _))
          (mul_nonneg (pow_nonneg hE.le _) (norm_nonneg _)) hBn
      _ = (1 + 4 * B) ^ kin * B *
          (E ^ (r + 2 * (n + 1)) * ‖iteratedFDeriv ℝ (r + 2 * (n + 1)) f x‖) := by ring
      _ ≤ _ := by
        exact (mul_le_mul_of_nonneg_left hinput (mul_nonneg hBn hB)).trans_eq (by ring)
  change E ^ r * ‖orderedDerivative β (covPolyP A p F - F) x‖ ≤ _
  rw [he]
  calc
    _ ≤ E ^ r * ∑ n ∈ Finset.range p,
        ‖((n + 1).factorial : ℝ)⁻¹ • orderedDerivative β ((covOperator A)^[n + 1] F) x‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg hE.le _)
    _ = ∑ n ∈ Finset.range p, E ^ r *
        ‖((n + 1).factorial : ℝ)⁻¹ • orderedDerivative β ((covOperator A)^[n + 1] F) x‖ :=
      Finset.mul_sum _ _ _
    _ ≤ ∑ _n ∈ Finset.range p,
        ((1 + 4 * B) ^ kin * B * ((2 : ℝ) ^ kin * (kin + 1))) * Y :=
      Finset.sum_le_sum hterm
    _ = (p : ℝ) * (((1 + 4 * B) ^ kin * B * ((2 : ℝ) ^ kin * (kin + 1))) * Y) := by simp
    _ ≤ (kin : ℝ) * (((1 + 4 * B) ^ kin * B * ((2 : ℝ) ^ kin * (kin + 1))) * Y) := by
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : p ≤ kin))
      exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (by linarith only [hB]) _) hB)
        (mul_nonneg (by positivity) (by positivity))) hY
    _ = _ := by ring

/-- The finite constant-coefficient jet ingredient, with its price fixed before all data. -/
theorem terminal_covariance_correction_bounds : TerminalCovarianceCorrectionBoundsStatement := by
  intro B k kin hB
  let C := (kin : ℝ) * (1 + 4 * B) ^ kin * B * ((2 : ℝ) ^ kin * (kin + 1))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C * kin.factorial, mul_nonneg hC (Nat.cast_nonneg _), ?_⟩
  intro H H' _ _ _ _ s E e r R cov osc hs hs1 hE hr hm
  obtain ⟨hR, p, A, hp, _hAsym, hA, hcov⟩ := hm
  obtain ⟨hcd, hper⟩ := WeakLift.representation_value_contDiff_periodic r hr
  let F : Vec 2 → H' := fun x => R (r.value x)
  have hF : ContDiff ℝ ((k + 2 * p : ℕ) : ℕ∞) F :=
    (R.contDiff.comp hcd).of_le (by exact_mod_cast hp)
  have hFp : IsZ2Periodic F := fun n x => congrArg R (hper n x)
  have hcovcd : ContDiff ℝ (k : ℕ∞) cov := by
    rw [hcov, ← covariancePolynomial_eq_P A p]
    exact (covariancePolynomial_contDiff A p k _ F hF).sub
      ((R.contDiff.comp hcd).of_le (by exact_mod_cast (by omega : k ≤ kin)))
  have hcovp : IsZ2Periodic cov := by
    rw [hcov, ← covariancePolynomial_eq_P A p]
    exact fun n x => congrArg₂ (· - ·)
      (covariancePolynomial_periodic A p _ F
        (hF.of_le (by exact_mod_cast Nat.le_add_left (2 * p) k)) hFp n x) (hFp n x)
  have hword (j : ℕ) (hj : j ≤ k) (β : DerivativeWord2 j) (x : Vec 2) :
      E ^ j * ‖orderedDerivative β cov x‖ ≤ C *
        ∑ α ∈ multiIndicesBetween 1 kin, E ^ (α 0 + α 1) * ‖partialDerivative α r.value x‖ := by
    rw [hcov]
    exact terminal_covariance_correction_word_bound A E B hE hB hA R hR k kin p hp r.value hcd
      j hj β x
  have hpoint : WeakLift.PositivePhysicalJetEstimate E E k kin C r.value cov := by
    rw [WeakLift.PositivePhysicalJetEstimate, div_self hE.ne', mul_one]
    constructor
    · intro x
      simpa only [pow_zero, one_mul, AVRegularity.orderedDerivative_zero] using
        hword 0 (Nat.zero_le k) Fin.elim0 x
    · intro α hα x
      let j := α 0 + α 1
      have hj : j ≤ k := (Finset.mem_filter.mp hα).2.2
      have heq : α = ![α 0, α 1] := by ext i; fin_cases i <;> rfl
      have hw := hword j hj (Fin.append (fun _ : Fin (α 0) => (0 : Fin 2))
        (fun _ : Fin (α 1) => (1 : Fin 2))) x
      rw [WeakLift.weakPositive_sorted_word_eq_partial] at hw
      simpa only [j, ← heq] using hw
  have hraw := WeakLift.positive_chart_norm_restoration E E s k kin C hE hE hs hs1 hC r cov hr hpoint
  rw [div_self hE.ne', Real.one_rpow, ENNReal.ofReal_one, mul_one] at hraw
  exact ⟨hcovcd, hcovp, hraw⟩

/-- The complete covariance half of the terminal physical transfer. -/
theorem terminal_covariance_transfer : TerminalCovarianceTransferStatement :=
  terminal_covariance_transfer_of_ingredients terminal_covariance_model terminal_covariance_correction_bounds

end AVRegularity.Finite.TerminalLift
end
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Finite.TerminalLift

/-! Positive derivatives of the terminal covariance input. The polynomial's identity term
is retained here, but a positive tested order still excludes the input amplitude. -/

open Construction.Preservation.FullLift

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A uniform polynomial price for every positive input word at the parent wavelength. -/
theorem terminal_covariance_input_word_bound (A : Matrix (Fin 2) (Fin 2) ℝ)
    (E B : ℝ) (hE : 0 < E) (hB : 0 ≤ B) (hA : ∀ i j, |A i j| ≤ B * E ^ 2)
    (R : V →L[ℝ] W) (hR : ‖R‖ ≤ B) (k kin p : ℕ) (hp : k + 2 * p ≤ kin)
    (f : Vec 2 → V) (hf : ContDiff ℝ (kin : ℕ∞) f)
    (r : ℕ) (hr0 : 1 ≤ r) (hr : r ≤ k) (β : DerivativeWord2 r) (x : Vec 2) :
    E ^ r * ‖orderedDerivative β (covPolyP A p (fun y => R (f y))) x‖ ≤
      (((kin : ℝ) * (1 + 4 * B) ^ kin * B + B) *
        ((2 : ℝ) ^ kin * (kin + 1))) *
        ∑ α ∈ multiIndicesBetween 1 kin, E ^ (α 0 + α 1) * ‖partialDerivative α f x‖ := by
  let F : Vec 2 → W := fun y => R (f y)
  let Y := ∑ α ∈ multiIndicesBetween 1 kin,
    E ^ (α 0 + α 1) * ‖partialDerivative α f x‖
  have hF : ContDiff ℝ (r : ℕ∞) F :=
    (R.contDiff.comp hf).of_le (by exact_mod_cast (by omega : r ≤ kin))
  have hP : ContDiff ℝ (r : ℕ∞) (covPolyP A p F) := by
    rw [← covariancePolynomial_eq_P A p]
    exact covariancePolynomial_contDiff A p r _ F
      ((R.contDiff.comp hf).of_le (by exact_mod_cast (by omega : r + 2 * p ≤ kin)))
  have hdiff := congrFun (orderedDerivative_sub β hP hF) x
  change orderedDerivative β (covPolyP A p F - F) x =
    orderedDerivative β (covPolyP A p F) x - orderedDerivative β F x at hdiff
  have hcor := terminal_covariance_correction_word_bound A E B hE hB hA R hR
    k kin p hp f hf r hr β x
  have hnorm := R.norm_iteratedFDeriv_comp_left (n := r) (hf.contDiffAt (x := x))
    (WithTop.coe_le_coe.mpr (by exact_mod_cast (by omega : r ≤ kin)))
  have hinput := WeakLift.weakPositive_scaled_full_jet_le hE.le hr0 (by omega : r ≤ kin) f hf x
  have hbase : E ^ r * ‖orderedDerivative β F x‖ ≤
      B * ((2 : ℝ) ^ kin * (kin + 1)) * Y := by
    calc
      _ ≤ E ^ r * ‖iteratedFDeriv ℝ r F x‖ :=
        mul_le_mul_of_nonneg_left (norm_orderedDerivative_le hF β x) (pow_nonneg hE.le _)
      _ ≤ E ^ r * (B * ‖iteratedFDeriv ℝ r f x‖) :=
        mul_le_mul_of_nonneg_left
          (hnorm.trans (mul_le_mul_of_nonneg_right hR (norm_nonneg _))) (pow_nonneg hE.le _)
      _ = B * (E ^ r * ‖iteratedFDeriv ℝ r f x‖) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left hinput hB).trans_eq (by ring)
  have hn : ‖orderedDerivative β (covPolyP A p F) x‖ ≤
      ‖orderedDerivative β (covPolyP A p F - F) x‖ + ‖orderedDerivative β F x‖ := by
    rw [hdiff]
    exact norm_le_norm_sub_add _ _
  calc
    _ ≤ E ^ r * (‖orderedDerivative β (covPolyP A p F - F) x‖ +
        ‖orderedDerivative β F x‖) := mul_le_mul_of_nonneg_left hn (pow_nonneg hE.le _)
    _ = E ^ r * ‖orderedDerivative β (covPolyP A p F - F) x‖ +
        E ^ r * ‖orderedDerivative β F x‖ := mul_add _ _ _
    _ ≤ _ := (add_le_add hcor hbase).trans_eq (by dsimp only [Y]; ring)

/-- Every positive derivative supplies one radius ratio when the slow radius is smaller. -/
theorem terminal_positive_radius_power {ρ E : ℝ} (hρ : 0 ≤ ρ) (hE : 0 < E)
    (hρE : ρ ≤ E) {j : ℕ} (hj : 1 ≤ j) : ρ ^ j ≤ (ρ / E) * E ^ j := by
  have hj' : j - 1 + 1 = j := Nat.sub_add_cancel hj
  have hp (a : ℝ) : a ^ j = a ^ (j - 1) * a := by
    conv_lhs => rw [← hj']
    rw [pow_succ]
  calc
    ρ ^ j = ρ * ρ ^ (j - 1) := (hp ρ).trans (mul_comm _ _)
    _ ≤ ρ * E ^ (j - 1) := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ hρE _) hρ
    _ = (ρ / E) * E ^ j := by rw [hp E]; field_simp

/-- The complete positive input jet sum costs one slow-to-parent scale ratio.
The finite sum price depends only on the requested orders and the covariance/readout budget. -/
theorem terminal_covariance_input_partial_sum_bound
    (A : Matrix (Fin 2) (Fin 2) ℝ) (E ρ B : ℝ) (hE : 0 < E) (hρ : 0 ≤ ρ)
    (hρE : ρ ≤ E) (hB : 0 ≤ B) (hA : ∀ i j, |A i j| ≤ B * E ^ 2)
    (R : V →L[ℝ] W) (hR : ‖R‖ ≤ B) (k kin p : ℕ) (hp : k + 2 * p ≤ kin)
    (f : Vec 2 → V) (hf : ContDiff ℝ (kin : ℕ∞) f) (x : Vec 2) :
    ∑ α ∈ multiIndicesBetween 1 k, ρ ^ (α 0 + α 1) *
        ‖partialDerivative α (covPolyP A p (fun y => R (f y))) x‖ ≤
      ((multiIndicesBetween 1 k).card : ℝ) *
        (((kin : ℝ) * (1 + 4 * B) ^ kin * B + B) * ((2 : ℝ) ^ kin * (kin + 1))) *
        (ρ / E) * ∑ α ∈ multiIndicesBetween 1 kin,
          E ^ (α 0 + α 1) * ‖partialDerivative α f x‖ := by
  let Y := ∑ α ∈ multiIndicesBetween 1 kin,
    E ^ (α 0 + α 1) * ‖partialDerivative α f x‖
  let C := ((kin : ℝ) * (1 + 4 * B) ^ kin * B + B) * ((2 : ℝ) ^ kin * (kin + 1))
  have ht (α : Fin 2 → ℕ) (hα : α ∈ multiIndicesBetween 1 k) :
      ρ ^ (α 0 + α 1) * ‖partialDerivative α (covPolyP A p (fun y => R (f y))) x‖ ≤
        C * (ρ / E) * Y := by
    have hj := (Finset.mem_filter.mp hα).2
    have heq : ![α 0, α 1] = α := by ext i; fin_cases i <;> rfl
    have hw := terminal_covariance_input_word_bound A E B hE hB hA R hR k kin p hp f hf
      (α 0 + α 1) hj.1 hj.2
      (Fin.append (fun _ : Fin (α 0) => (0 : Fin 2))
        (fun _ : Fin (α 1) => (1 : Fin 2))) x
    rw [WeakLift.weakPositive_sorted_word_eq_partial, heq] at hw
    calc
      _ ≤ ((ρ / E) * E ^ (α 0 + α 1)) *
          ‖partialDerivative α (covPolyP A p (fun y => R (f y))) x‖ :=
        mul_le_mul_of_nonneg_right (terminal_positive_radius_power hρ hE hρE hj.1) (norm_nonneg _)
      _ = (ρ / E) * (E ^ (α 0 + α 1) *
          ‖partialDerivative α (covPolyP A p (fun y => R (f y))) x‖) := mul_assoc _ _ _
      _ ≤ (ρ / E) * (C * Y) := mul_le_mul_of_nonneg_left hw (div_nonneg hρ hE.le)
      _ = _ := by ring
  calc
    _ ≤ ∑ _α ∈ multiIndicesBetween 1 k, C * (ρ / E) * Y := Finset.sum_le_sum ht
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; dsimp only [C, Y]; ring

/-- Recover a classical component array from its normalized finite-dimensional field. -/
theorem terminal_normalized_input_regular (S : Finset Comp) (π : CompIn S → ℝ)
    (hπ : ∀ v, 0 < π v) (n : ℕ) (f : Vec 2 → ∀ v : CompIn S, ScalarH v.1.root)
    (hc : ContDiff ℝ (n : ℕ) (compField π f)) (hp : IsZ2Periodic (compField π f)) :
    ContDiff ℝ (n : ℕ) f ∧ IsZ2Periodic f := by
  let T := PiLp.continuousLinearEquiv 2 ℝ (fun _ : CompIn S => ℝ)
  have he (x : Vec 2) (v : CompIn S) :
      f x v = Real.sqrt (π v) * T (compField π f x) v := by
    change f x v = Real.sqrt (π v) * ((Real.sqrt (π v))⁻¹ * f x v)
    rw [← mul_assoc, mul_inv_cancel₀ (Real.sqrt_pos.mpr (hπ v)).ne', one_mul]
  constructor
  · apply contDiff_pi.mpr
    intro v
    have hfun : (fun x => f x v) = fun x => Real.sqrt (π v) * T (compField π f x) v :=
      funext (fun x => he x v)
    rw [hfun]
    exact contDiff_const.mul ((contDiff_apply ℝ ℝ v).comp (T.contDiff.comp hc))
  · intro p x
    funext v
    rw [he (x + latticeShift p) v, he x v, hp p x]

/-- Coordinate differentiation preserves the zero field, including derivative order zero. -/
theorem terminal_partial_zero (α : Fin 2 → ℕ) :
    partialDerivative α (0 : Vec 2 → W) = 0 := by
  have hi (j : Fin 2) (n : ℕ) :
      (fun G : Vec 2 → W => fun x => fderiv ℝ G x (basisVec j))^[n] 0 = 0 := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      funext x
      simp only [fderiv_zero, zero_apply, Pi.zero_apply]
  unfold partialDerivative
  rw [hi 0 (α 0), hi 1 (α 1)]

end AVRegularity.Finite.TerminalLift
end
end
