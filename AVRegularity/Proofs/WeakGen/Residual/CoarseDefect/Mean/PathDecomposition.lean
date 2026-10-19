-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.ActualMeans.Main
public import AVRegularity.Proofs.WeakGen.Residual.Window.SettingLiftsStep
import AVRegularity.EntryTerminal.Ingredients.Recon.Defect.MacroSwapLettersReg
public import AVRegularity.CycleComparison.LiftSetting.Metric
import AVRegularity.EntryTerminal.Ingredients.Recon.Setting.Main
public import AVRegularity.Proofs.WeakGen.Residual.CoarseDefect.InitialValueProof
import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofCascadeFluxOrderBound
public import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofCascadeSplitInput
import AVRegularity.Applications.Global.CompactRangeMain
import AVRegularity.Finite.WeakPositive.NativeAdapter

section
@[expose] public noncomputable section

section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect.Mean

/-! Assembly of the mean presentation: the Piola argument is reused from `ActualMeans.Presentation`.
The remaining statements concern pulse geometry, the explicit native mean coefficients,
and their identification with the stored physical letters. They are not alternative
mean presentations.

The degenerate cases are included. Geometry: one observed pulse and either endpoint use its closed
lift window; an empty observation sum is harmless. Coefficients: grade zero includes the molecular
metric at degree two; an edge-free incoming stage has zero positive grades. Letters: Rw=1 contains
every singleton eddy word, including D₂ when Nw=1; Rw=0 is excluded by a positivity premise
(discharged from the comparison menu). Zero calibration gives zero on both sides. Empty component
families have no reference component. The recap fixes every cap before ambient Dm. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly CycleComparison.Lift CycleComparison.ActualMeans
open AVRegularity.Construction.Residual.Presentation Finite.WeakLift

/-- Exactly one application of the mean statement. -/
structure Case (plan : WeakPassagePlan) {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A) where
  response : 1 ≤ A.Rw
  c : WeakPassageInstance plan R
  r : WeakPassageRun c
  i : ℕ
  lower : c.M < i
  upper : i ≤ c.M + A.Jw
  input : WeakComparisonInput r i
  v₀ : CompIn (c.stage i).comps
  grade : ℕ
  grade_le : grade ≤ A.Jw * A.Rw

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

namespace Case
variable (x : Case plan R)
abbrev cap (_x : Case plan R) : ℕ := 1 + A.Jw * A.Nw
abbrev interval : Set ℝ := Set.Icc (x.r.tq x.i) (x.r.a + A.T₀)
abbrev pulses : Finset ℤ := ocObsPulses x.c.D.α x.c.D.q x.c.D.Λ x.i
  (x.r.tq x.i) (x.r.a + A.T₀)
abbrev clock : ℝ := ocEll x.c.D.q x.c.D.Λ x.i (x.c.D.κ x.c.M) ^ 2
abbrev length : ℝ := x.c.D.eps (x.i - 1)
abbrev contrast : ℝ := ocDStar x.c.D.q x.c.D.Λ x.i (x.c.D.κ x.c.M)
  (x.c.D.κ x.c.M) / x.length
abbrev weight (k : ℤ) : ℝ → ℝ :=
  (Window.weakWindowFamily x.c x.i x.lower x.upper).weight (oddSlotOf k)
abbrev data (k : ℤ) := pulseLiftData x.c.D.α x.c.D.q x.c.D.Λ x.i x.c.D.ζ
  (x.c.D.Φ (x.i - 1)) (x.c.D.hΦ (x.i - 1)) (x.c.D.κ x.c.M) (x.c.D.κ x.c.M)
  x.length (x.length / x.length) k
  ((Window.weakWindowFamily x.c x.i x.lower x.upper).fiber (oddSlotOf k) ())
abbrev chart (k : ℤ) := ocChart x.c.D.α x.c.D.q x.c.D.Λ x.i
  (x.c.D.Φ (x.i - 1)) (x.c.D.hΦ (x.i - 1))
  (ocPulseChartIndex x.c.D.α x.c.D.q x.c.D.Λ x.i k)
abbrev label (k : ℤ) := ocChartInv x.c.D.α x.c.D.q x.c.D.Λ x.i
  (x.c.D.Φ (x.i - 1)) (x.c.D.hΦ (x.i - 1))
  (ocPulseChartIndex x.c.D.α x.c.D.q x.c.D.Λ x.i k)
abbrev left (k : ℤ) : ℝ := weakSlotLeft x.c.D x.i k
abbrev right (k : ℤ) : ℝ := weakSlotRight x.c.D x.i k

/-- The actual diagonal/positive mean-flux coefficient, at fast position zero. -/
def coeff (k : ℤ) (r n : ℕ) : MeanCoeff (CompIn (x.c.stage x.i).comps)
    (fun v => ScalarH v.1.root) :=
  fun d α t X l =>
    (if r = 0 then diagonalMeanFluxCoefficient (x.data k) (x.input.CcR x.i k) n l
     else positiveMeanFluxCoefficient (x.data k) (x.input.CcR x.i k) r n l)
      (d - 1) α t X 0
end Case

/-- Geometry of the observed pulses; no information about the mean or its letters. -/
structure PulseGeometry {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    {R : WeakPassageRequest A} (x : Case plan R) : Prop where
  clock_ne : x.clock ≠ 0
  length_ne : x.length ≠ 0
  support : ∀ k ∈ x.pulses, ∀ t ∈ x.interval, x.weight k t ≠ 0 →
    x.clock⁻¹ * t ∈ Set.Icc (x.left k) (x.right k)
  label_chart : ∀ k ∈ x.pulses, ∀ t y, x.label k t (x.chart k t y) = y
  chart_label : ∀ k ∈ x.pulses, ∀ t y, x.chart k t (x.label k t y) = y
  determinant : ∀ k ∈ x.pulses, ∀ t y, (jacMatrix (x.chart k t) y).det = 1
  chart_smooth : ∀ k ∈ x.pulses, ∀ t, ContDiff ℝ (⊤ : ℕ∞) (x.chart k t)
  label_diff : ∀ k ∈ x.pulses, ∀ t, Differentiable ℝ (x.label k t)

/-- The native coefficient array presents each cell mean and is C¹ in slow position. -/
structure NativeCoefficients {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    {R : WeakPassageRequest A} (x : Case plan R) : Prop where
  presents : ∀ k ∈ x.pulses, ∀ n, 2 ≤ n → n ≤ A.Nw + x.cap →
    ∀ a₀ : Vec 2 → ∀ v : CompIn (x.c.stage x.i).comps, ScalarH v.1.root,
      ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ s ∈ Set.Icc (x.left k) (x.right k), ∀ X,
        liftMean (x.data k) (x.input.CcR x.i k) (fun _ => a₀) x.grade n s X =
          meanApply n (x.coeff k x.grade n) (fun _ => a₀) s X
  smooth : ∀ k ∈ x.pulses, ∀ n, 2 ≤ n → n ≤ A.Nw + x.cap → ∀ d, 2 ≤ d → d ≤ n →
    ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2) (v u : CompIn (x.c.stage x.i).comps),
      ∀ s ∈ Set.Icc (x.left k) (x.right k),
        ContDiff ℝ 1 (fun X => x.coeff k x.grade n d α s X l v u)

def WeakCoarsePulseGeometryStatement (plan : WeakPassagePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (x : Case plan R), PulseGeometry x

def WeakCoarseNativeCoefficientsStatement (plan : WeakPassagePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (x : Case plan R), NativeCoefficients x

/-- The stored letters equal the negative glued native Eulerian flux (before divergence). -/
def WeakCoarseStoredMeanFluxStatement (plan : WeakPassagePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (x : Case plan R)
    (a : ℝ → Vec 2 → ∀ v : CompIn (x.c.stage x.i).comps, ScalarH v.1.root),
    (∀ t, ContDiff ℝ (⊤ : ℕ∞) (a t)) → ∀ t ∈ x.interval, ∀ y v l,
    classicalGradeFlux (A.Nw + x.cap) x.grade (cdAD x.c (A.Nw + x.cap) x.i x.v₀)
      (cdCE x.c (A.Nw + x.cap) x.i x.lower x.upper)
      (fun _ => (x.c.D.κ x.c.M) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) a v t y l =
      -∑ k ∈ x.pulses, x.weight k t • eulerFlux x.clock x.length x.contrast (A.Nw + x.cap)
        (x.chart k t) (x.label k t) (x.coeff k x.grade)
        (fun z => a t (x.chart k t z)) (x.clock⁻¹ * t) v y l

/-- The mean statement from the three independent identities, using the generic Piola theorem. -/
theorem weakCoarseMean_of_ingredients
    (hgeometry : WeakCoarsePulseGeometryStatement plan)
    (hcoeff : WeakCoarseNativeCoefficientsStatement plan)
    (hflux : WeakCoarseStoredMeanFluxStatement plan) : WeakCoarseMeanStatement plan := by
  intro B A R hRw c r i hi hit h v₀ ρ hρ
  let x : Case plan R := ⟨hRw, c, r, i, hi, hit, h, v₀, ρ, hρ⟩
  have g := hgeometry x
  have b := hcoeff x
  refine isMeanPresentation_of_flux x.interval x.pulses x.weight x.clock x.length x.contrast
    g.clock_ne g.length_ne A.Nw x.grade x.data (x.input.CcR x.i) x.chart x.label x.left x.right
    x.coeff (cdAD x.c (A.Nw + x.cap) x.i x.v₀)
    (cdCE x.c (A.Nw + x.cap) x.i x.lower x.upper)
    (fun _ => (x.c.D.κ x.c.M) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) g.support g.label_chart
    g.chart_label g.determinant g.chart_smooth g.label_diff b.presents b.smooth ?_
  intro a ha t ht y v l
  rw [hflux x a ha t ht y v l]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [eulerFlux_eq]
end

/-! Pulse geometry for the mean presentation, including the edge-free finest stage. No quiet-time
hypothesis is used: this is support and geometry on each closed native pulse window. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly Finite.WeakLift
open AVRegularity.Construction.Residual.Presentation

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- Naturality is supplied by the incoming passage, or by the root at its endpoint. -/
theorem Case.natural (x : Case plan R) : (x.c.stage x.i).IsNatural (x.c.M + A.Jw) := by
  by_cases heq : x.i = x.c.M + A.Jw
  · rw [heq]
    exact x.c.construction.2.1.2.2.2
  · exact EntryWeakProofs.weakConstruction_output_natural x.c.P _ x.c.M A.Jw 0 _
      x.c.stage x.c.construction x.i x.lower.le (lt_of_le_of_ne x.upper heq)

/-- The cell clock and the length are strictly positive under the common floors. -/
theorem Case.scales (hcommon : WeakPassageCommonOK plan) (x : Case plan R) :
    0 < x.clock ∧ 0 < x.length := by
  have hbase := (weakCommonCoeffPlan.baseThreshold_ge B).trans
    ((hcommon.1 B).trans x.c.base_ge)
  have hΛ : 1 ≤ x.c.D.Λ := by rw [x.c.base_eq]; omega
  have hζ : IsFastProfile x.c.D.ζ := x.c.profile_eq.symm ▸ B.hζ
  have hb : IsOCBandChain x.c.D.α x.c.D.q x.c.D.Λ x.c.D.ζ x.c.D.term x.c.D.κ := by
    rw [x.c.alpha, x.c.q_eq, x.c.base_eq, x.c.profile_eq, x.c.terminal]
    exact x.c.band
  have hk := (Reduction.weakPassageRawSetting x.c).kappa_pos
  constructor
  · change 0 < ocEll x.c.D.q x.c.D.Λ x.i (x.c.D.κ x.c.M) ^ 2
    rw [Window.weakWindow_cellTime x.c x.i x.lower hk]
    exact EntryWeakProofs.weakData_cellScaleSq_pos x.c.D hΛ hζ hb x.i
  · exact Construction.Stream.ocEpsilon_pos hΛ

/-- The three geometric ingredients do not depend on the mean coefficients. -/
theorem weakCoarsePulseGeometry (hcommon : WeakPassageCommonOK plan) :
    WeakCoarsePulseGeometryStatement plan := by
  intro B A R x
  have hs := x.scales hcommon
  have hlevel : (x.c.stage x.i).level = x.i :=
    EntryWeakProofs.weakConstruction_level _ _ _ _ _ _ _ x.c.construction
      x.i x.lower.le x.upper
  have hn := x.natural
  refine ⟨hs.1.ne', hs.2.ne', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk t _ hne
    have hodd := CycleComparison.LiftSetting.obsPulse_odd hk
    have hp : t ∈ ocPulseWindow x.c.D.α x.c.D.q x.c.D.Λ x.i k := by
      by_contra hout
      apply hne
      change (x.c.stage x.i).fam.weight (oddSlotOf k) t = 0
      apply (x.c.stage x.i).fam.weight_zero
      rw [(hn.1 (oddSlotOf k)).2.1, hlevel, oddSlotOf_of_odd hodd]
      exact hout
    have hclock : x.clock = x.c.D.cellScaleSq x.i :=
      Window.weakWindow_cellTime x.c x.i x.lower (Reduction.weakPassageRawSetting x.c).kappa_pos
    change _ ∈ Set.Icc (weakSlotLeft x.c.D x.i k) (weakSlotRight x.c.D x.i k)
    change x.c.D.slotStart x.i k / x.c.D.cellScaleSq x.i ≤ _ ∧ _ ≤ _
    rw [inv_mul_eq_div, hclock]
    have hc : 0 < x.c.D.cellScaleSq x.i := hclock ▸ hs.1
    exact ⟨(div_le_div_iff_of_pos_right hc).mpr hp.1,
      (div_le_div_iff_of_pos_right hc).mpr hp.2⟩
  · intro k _ t y
    exact CycleComparison.Charts.ocChartInv_ocChart _ _ _ _ _ _ _ _ y
  · intro k _ t y
    exact CycleComparison.Charts.ocChart_ocChartInv _ _ _ _ _ _ _ _ y
  · intro k _ t y
    exact CycleComparison.Charts.ocChart_det (x.c.D.hΦ (x.i - 1)) _ _ _ _ _ t y
  · intro k _ t
    exact (CycleComparison.Charts.contDiff_ocChart_joint (x.c.D.hΦ (x.i - 1)) _ _ _ _ _).comp
      (contDiff_const.prodMk contDiff_id)
  · intro k _ t
    exact ((CycleComparison.Charts.contDiff_ocChartInv_joint (x.c.D.hΦ (x.i - 1)) _ _ _ _ _).comp
      (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
end

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect.Mean
end

section
open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect.Mean

/-! Native settings and sequences for the mean presentation. The whole pulse window keeps
the original sequence's initial time, so no restart or strict observation deadline
is needed. All transfer and cap operations are the shared APIs. -/

open WeakEntryProofs WeakEntryProofs.Assembly Finite.WeakLift Window CycleComparison.Lift EntryWeakProofs
open AVRegularity.Construction.Residual.Presentation
open AVRegularity.EntryTerminal.Ingredients.Recon.Setting

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- The window's actual data and the native data agree throughout the whole pulse. -/
theorem Case.sequence (x : Case plan R) {k : ℤ} (hk : Odd k)
    (hclock : x.clock = x.c.D.cellScaleSq x.i) (hpos : 0 < x.clock) :
    IsLiftSequence (x.data k) R.sX R.sZ (x.left k) (x.right k) A.Nw (A.Jw * A.Rw)
      (x.input.CcR x.i k) := by
  have hs := weakSeqCap_of x.c x.r x.i x.lower x.upper x.input k hk
  have hg := weakSeqAgree_of x.c x.i x.lower x.upper k hk
  apply EntryTerminal.Ingredients.Recon.Seq.seq_isLiftSequence_congr _ _ hg.1 _ hs
  intro t ht
  apply hg.2
  exact Residual.weakNativeQuietMemWindow (hclock ▸ hpos) ht

/-- Transfer a slot-lift setting to the actual pulse data on its original closed window. -/
theorem Case.setting (x : Case plan R) {k : ℤ} (hk : Odd k)
    (hΛ : 1 ≤ x.c.D.Λ) (hκ : 0 < x.c.D.κ x.c.M)
    {Lr : ℕ} (Pw : WeakPositiveParameters A.Nw (weakH A) (Lr + 3))
    (hfl : WeakOrderFloors A 0 Pw)
    (S : WeakPositiveSlot Pw x.i (x.c.stage x.i)
      (fun v => weakMass x.c.D A.Nw A.Jw A.η₀ v.1) ⟨k, hk⟩) :
    IsLiftSetting (x.data k) (fun v => weakMass x.c.D A.Nw A.Jw A.η₀ v.1)
      (x.left k) (x.right k) (x.c.D.eps x.i) (x.c.D.kap x.i) (x.c.D.kap (x.i - 1))
      x.length (x.c.D.eps (x.i - 1)) (x.c.D.eps x.i / Real.sqrt (x.c.D.kap x.i))
      (ocDStar x.c.D.q x.c.D.Λ x.i (x.c.D.kap x.i) (x.c.D.kap (x.i - 1)))
      (ocDStar x.c.D.q x.c.D.Λ x.i (x.c.D.kap x.i) (x.c.D.kap (x.i - 1)) / x.length)
      (x.length / x.c.D.eps (x.i - 1)) (pulseParallel k)
      (pulseShearProfile x.c.D.α x.c.D.q x.c.D.Λ x.i x.c.D.ζ (x.c.D.kap x.i) k)
      (weakH A) A.Nw (weakKlift A 0) (weakLlift A 0) (weakLlift A 0)
      (weakSettingQs A 0) (weakSettingQf A 0) Pw.CG Pw.Cw Pw.Cj S.price Pw.S := by
  classical
  have hset := weakSlot_cappedSetting A 0 Pw hfl x.i (x.c.stage x.i)
    (fun v => weakMass x.c.D A.Nw A.Jw A.η₀ v.1) ⟨k, hk⟩ S
  have hD : S.cap ≤ weakDw A := S.cap_le.trans hfl.2.2.ge
  have hcell : x.clock = x.c.D.cellScaleSq x.i :=
    weakWindow_cellTime x.c x.i x.lower hκ
  have hcpos : 0 < x.c.D.cellScaleSq x.i := by
    unfold OCData.cellScaleSq OCData.eps
    rw [wSetting_kap x.c x.i x.lower]
    exact div_pos (pow_pos (Construction.Stream.ocEpsilon_pos hΛ) 2) hκ
  have hab : x.left k ≤ x.right k := S.setting.window
  have hout := weakStage_output_eq x.c x.i x.lower x.upper ⟨k, hk⟩
  have e2 : (x.data k).edge = liftEdges (x.c.D.cellScaleSq x.i)
      (x.length / x.length) ((weakWindowFamily x.c x.i x.lower x.upper).fiber ⟨k, hk⟩ ()) := by
    change liftEdges x.clock _ _ = _
    rw [hcell, oddSlotOf_of_odd hk]
  let O : Set ℝ := (fun t => x.c.D.cellScaleSq x.i * t) ⁻¹'
    ((x.c.stage x.i).fam.piece ⟨k, hk⟩).output
  have hO : O ⊆ Set.Icc (x.left k) (x.right k) := by
    intro t ht
    have hwin : x.c.D.cellScaleSq x.i * t ∈
        ocPulseWindow x.c.D.α x.c.D.q x.c.D.Λ x.i k := by
      dsimp only [O, Set.mem_preimage] at ht
      rwa [hout] at ht
    exact ⟨(div_le_iff₀ hcpos).mpr (by rw [mul_comm]; exact hwin.1),
      (le_div_iff₀ hcpos).mpr (by rw [mul_comm]; exact hwin.2)⟩
  have hsub : Set.Icc (x.left k) (x.right k) ⊆ O := by
    intro t ht
    dsimp only [O, Set.mem_preimage]
    rw [hout]
    exact Residual.weakNativeQuietMemWindow hcpos ht
  have hrel := fun v u d => weakLifts_rel_slotLift hD x.c.order_ge
    (weakPositiveNativeData x.i (x.c.stage x.i) ⟨k, hk⟩).edge S.Q.edge (x.data k).edge
    O hO hab (fun v u d => by
      rw [e2]
      exact weakWindow_native_rel x.c x.i x.lower x.upper ⟨k, hk⟩ _ _ v u d)
    S.edge_agree v u d
  have hE : EdgeAgree (extendData hD S.Q).edge (x.data k).edge (x.left k) (x.right k) := by
    intro v u d
    refine List.Forall₂.imp (fun q w hqw => ⟨hqw.1.symm, fun α t ht => ?_⟩) (hrel v u d)
    funext X z
    rw [hqw.2 α t X z, ite_eq_left (hsub ht)]
  have hmeas : ∀ v u d, ∀ γ ∈ (x.data k).edge v u d, ∀ α X z,
      Measurable fun t => γ.coeff α t X z := by
    intro v u d γ hγ α X z
    obtain ⟨q, hq, hqw⟩ := weakLifts_forall₂_mem_right (hrel v u d) γ hγ
    have hm := hset.coeff_meas v u d q hq α X z
    have hOm : MeasurableSet O := by
      show MeasurableSet ((fun t => x.c.D.cellScaleSq x.i * t) ⁻¹' _)
      rw [hout]
      exact measurableSet_Icc.preimage (measurable_const.mul measurable_id)
    have he : (fun t => γ.coeff α t X z) = fun t => if t ∈ O then q.coeff α t X z else 0 :=
      funext fun t => hqw.2 α t X z
    rw [he]
    exact Measurable.ite hOm hm measurable_const
  exact isLiftSetting_transfer hset le_rfl hab le_rfl
    ((wSetting_eta x.c x.i x.lower x.upper hk).trans S.eta_eq.symm)
    ((wSetting_metric x.c x.i x.lower x.upper hΛ hκ hk).trans S.metric_eq.symm)
    ((wSetting_drift x.c x.i x.lower x.upper hk).trans S.drift_eq.symm) hE hmeas

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect.Mean
end

section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect.Mean

/-! Native cell means for the mean presentation, from the shared slot-lift factory and the proved
mean-coefficient calculus. The only additional lift floor is two; the slot-lift readout
order is fixed by the menu before the instance and its ambient cap.
The degenerate cases are included: the root uses the empty-source slot lift; grade zero retains
the molecular metric at `n = 2`; positive grades and all `n` up to `N_w + D_w` use the same finite
cap. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly Finite.WeakLift Window
open AVRegularity.EntryTerminal.Ingredients.Recon

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- Slot-lift and lift floors for the native mean calculation; no estimate is assumed. -/
def WeakCoarseMeanPlanOK (plan : WeakPassagePlan) : Prop :=
  WeakSlotLiftPlanOK plan (fun {B} {A : WeakCoefficientPhysical B} _ => weakWindowLrFloor A 0) ∧
  ∀ {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B), 2 ≤ plan.liftFloor A

/-- One slot lift supplies both the cell-mean identity and slow `C^1` regularity. -/
theorem Case.coefficients_of_slotLift (x : Case plan R) {k : ℤ} (hk : Odd k)
    (hΛ : 1 ≤ x.c.D.Λ) (hκ : 0 < x.c.D.κ x.c.M)
    (hc : 0 < x.clock) (hX : 2 ≤ R.sX) (hZ : 2 ≤ R.sZ)
    {Lr : ℕ} (Pw : WeakPositiveParameters A.Nw (weakH A) (Lr + 3))
    (hfl : WeakOrderFloors A 0 Pw)
    (S : WeakPositiveSlot Pw x.i (x.c.stage x.i)
      (fun v => weakMass x.c.D A.Nw A.Jw A.η₀ v.1) ⟨k, hk⟩) :
    (∀ n, 2 ≤ n → n ≤ A.Nw + x.cap →
      ∀ a₀ : Vec 2 → ∀ v : CompIn (x.c.stage x.i).comps, ScalarH v.1.root,
        ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ s ∈ Set.Icc (x.left k) (x.right k), ∀ X,
          liftMean (x.data k) (x.input.CcR x.i k) (fun _ => a₀) x.grade n s X =
            meanApply n (x.coeff k x.grade n) (fun _ => a₀) s X) ∧
    (∀ n, 2 ≤ n → n ≤ A.Nw + x.cap → ∀ d, 2 ≤ d → d ≤ n →
      ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2) (v u : CompIn (x.c.stage x.i).comps),
        ∀ s ∈ Set.Icc (x.left k) (x.right k),
          ContDiff ℝ 1 (fun X => x.coeff k x.grade n d α s X l v u)) := by
  classical
  have P := x.setting hk hΛ hκ Pw hfl S
  have hseq := x.sequence hk (weakWindow_cellTime x.c x.i x.lower hκ) hc
  constructor
  · intro n hn hnR a₀ ha₀ s hs X
    exact Cfl_pres P R.sX R.sZ hX hZ (x.input.CcR x.i k) hseq x.grade x.grade_le
      n hn hnR a₀ ha₀ s hs X
  · intro n hn hnR d hd hdn α l v u s hs
    exact Cfl_contDiff P R.sX R.sZ (by omega) (x.input.CcR x.i k) hseq x.grade
      x.grade_le n hn hnR d hd hdn α l v u s hs

/-- The native coefficient ingredient, with all analytic facts discharged by existing lemmas. -/
theorem weakCoarseNativeCoefficients (hcommon : WeakPassageCommonOK plan)
    (hok : WeakCoarseMeanPlanOK plan) : WeakCoarseNativeCoefficientsStatement plan := by
  intro B A R x
  have hLr := weakWindowLrFloor_ge_JN A 0
  obtain ⟨h1, h2, h3, hpk⟩ := weakSlotLiftAt_planOK hok.1 A R hLr
  obtain ⟨_, ⟨pk⟩⟩ := hpk x.c x.i x.lower x.upper
  have hfl := weakOrderFloors_of_orders A 0 (weakWindowLrFloor A 0) _ h1 h2 h3
    (Nat.mul_pos A.Jw_pos A.Nw_pos) le_rfl
  have hΛ : 1 ≤ x.c.D.Λ := by
    rw [x.c.base_eq]
    have hb := (weakCommonCoeffPlan.baseThreshold_ge B).trans
      ((hcommon.1 B).trans x.c.base_ge)
    omega
  have hκ := (Reduction.weakPassageRawSetting x.c).kappa_pos
  have hX : 2 ≤ R.sX := (hok.2 A).trans x.input.sX_ge
  have hZ : 2 ≤ R.sZ := (hok.2 A).trans x.input.sZ_ge
  have hc := (x.scales hcommon).1
  have hp (k : ℤ) (hk : k ∈ x.pulses) :=
    x.coefficients_of_slotLift (CycleComparison.LiftSetting.obsPulse_odd hk) hΛ hκ hc hX hZ _ hfl
      (pk ⟨k, CycleComparison.LiftSetting.obsPulse_odd hk⟩)
  exact ⟨fun k hk => (hp k hk).1, fun k hk => (hp k hk).2⟩

/-- With pulse geometry and native coefficients proved, only the stored-letter identity remains. -/
theorem weakCoarseMean_of_storedFlux (hcommon : WeakPassageCommonOK plan)
    (hok : WeakCoarseMeanPlanOK plan) (hflux : WeakCoarseStoredMeanFluxStatement plan) :
    WeakCoarseMeanStatement plan :=
  weakCoarseMean_of_ingredients (weakCoarsePulseGeometry hcommon)
    (weakCoarseNativeCoefficients hcommon hok) hflux
end

/-! The canonical coefficient flux is the literal physical mean flux.
The remaining stored-letter identity can therefore be proved in the native flux
notation used by path decomposition and transfer. No divergence identity is assumed. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly Finite.WeakLift Window CycleComparison.Lift
open CycleComparison.ActualMeans AVRegularity.EntryTerminal.Ingredients.Recon

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- The native mean flux in physical variables, summed over its finite mean degrees. -/
def Case.pulseFlux (x : Case plan R)
    (a : ℝ → Vec 2 → ∀ v : CompIn (x.c.stage x.i).comps, ScalarH v.1.root)
    (k : ℤ) (t : ℝ) (y : Vec 2) (v : CompIn (x.c.stage x.i).comps) (l : Fin 2) :
    ScalarH v.1.root :=
  ∑ n ∈ Finset.Icc 2 (A.Nw + x.cap),
    pulseMeanFluxEuler x.clock x.length x.contrast n x.grade (x.data k) (x.input.CcR x.i k)
      (x.chart k) (x.label k) a t y v l

/-- The actual physical mean flux at the fixed observation set. -/
def Case.gluedFlux (x : Case plan R)
    (a : ℝ → Vec 2 → ∀ v : CompIn (x.c.stage x.i).comps, ScalarH v.1.root)
    (t : ℝ) (y : Vec 2) (v : CompIn (x.c.stage x.i).comps) (l : Fin 2) : ScalarH v.1.root :=
  ∑ k ∈ x.pulses, x.weight k t • x.pulseFlux a k t y v l

/-- One native pulse has exactly the coefficient-array Eulerian flux, with the mean sign. -/
theorem Case.pulseFlux_eq_of_slotLift (x : Case plan R) {k : ℤ} (hk : k ∈ x.pulses)
    (hgeometry : PulseGeometry x) (hΛ : 1 ≤ x.c.D.Λ) (hκ : 0 < x.c.D.κ x.c.M)
    (hX : x.cap ≤ R.sX) (hZ : x.cap ≤ R.sZ)
    {Lr : ℕ} (Pw : WeakPositiveParameters A.Nw (weakH A) (Lr + 3))
    (hfl : WeakOrderFloors A 0 Pw)
    (S : WeakPositiveSlot Pw x.i (x.c.stage x.i)
      (fun v => weakMass x.c.D A.Nw A.Jw A.η₀ v.1)
      ⟨k, CycleComparison.LiftSetting.obsPulse_odd hk⟩)
    (a : ℝ → Vec 2 → ∀ v : CompIn (x.c.stage x.i).comps, ScalarH v.1.root)
    (ha : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (a t)) (t : ℝ) (ht : t ∈ x.interval)
    (hne : x.weight k t ≠ 0) (y : Vec 2) (v : CompIn (x.c.stage x.i).comps) (l : Fin 2) :
    x.pulseFlux a k t y v l =
      -eulerFlux x.clock x.length x.contrast (A.Nw + x.cap) (x.chart k t) (x.label k t)
        (x.coeff k x.grade) (fun z => a t (x.chart k t z)) (x.clock⁻¹ * t) v y l := by
  classical
  have hodd := CycleComparison.LiftSetting.obsPulse_odd hk
  have P := x.setting hodd hΛ hκ Pw hfl S
  have hc : 0 < x.clock := pow_pos
    (div_pos (Construction.Stream.ocEpsilon_pos hΛ) (Real.sqrt_pos.mpr hκ)) 2
  have hcap : 2 ≤ x.cap := by
    dsimp only [Case.cap]
    have := Nat.mul_pos A.Jw_pos A.Nw_pos
    omega
  have hseq := x.sequence hodd (weakWindow_cellTime x.c x.i x.lower hκ) hc
  have hwin := hgeometry.support k hk t ht hne
  have he (n : ℕ) (hn : n ∈ Finset.Icc 2 (A.Nw + x.cap)) :=
    pulseMeanFluxEuler_eq (x.data k) (x.data k) rfl (x.input.CcR x.i k) x.grade n
      (Finset.mem_Icc.mp hn).1 (coreMeanFluxCoeff (x.data k) (x.input.CcR x.i k) x.grade n)
      x.clock x.length x.contrast hgeometry.clock_ne hgeometry.length_ne (x.chart k) (x.label k)
      a t y (ha t) (hgeometry.chart_smooth k hk t) ⟨rfl, rfl, fun _ _ _ => rfl⟩
      (fun j α v u => Cfl_zero_order P R.sX R.sZ
        (by omega) (x.input.CcR x.i k) hseq x.grade x.grade_le n
        (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2 j _ hwin α _ 0 v u)
      (fun j v => Cfl_hid P R.sX R.sZ hX hZ (x.input.CcR x.i k) hseq x.grade
        x.grade_le n (Finset.mem_Icc.mp hn).1 _
        ((ha t).comp ((hgeometry.chart_smooth k hk t).comp (contDiff_const_smul _)))
        j _ hwin _ v) v l
  unfold Case.pulseFlux
  rw [eulerFlux_eq, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun n hn => he n hn

/-- The stored letters reproduce the actual physical glued mean flux, before taking divergence. -/
def WeakCoarsePhysicalFluxStatement (plan : WeakPassagePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (x : Case plan R)
    (a : ℝ → Vec 2 → ∀ v : CompIn (x.c.stage x.i).comps, ScalarH v.1.root),
    (∀ t, ContDiff ℝ (⊤ : ℕ∞) (a t)) → ∀ t ∈ x.interval, ∀ y v l,
    classicalGradeFlux (A.Nw + x.cap) x.grade (cdAD x.c (A.Nw + x.cap) x.i x.v₀)
      (cdCE x.c (A.Nw + x.cap) x.i x.lower x.upper)
      (fun _ => (x.c.D.κ x.c.M) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) a v t y l =
      x.gluedFlux a t y v l

/-- The physical flux identity supplies the last ingredient of the mean presentation. -/
theorem weakCoarseStoredMeanFlux_of_physical (hcommon : WeakPassageCommonOK plan)
    (hok : WeakCoarseMeanPlanOK plan)
    (horder : ∀ {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B),
      1 + A.Jw * A.Nw ≤ plan.liftFloor A)
    (hphysical : WeakCoarsePhysicalFluxStatement plan) : WeakCoarseStoredMeanFluxStatement plan := by
  intro B A R x a ha t ht y v l
  rw [hphysical x a ha t ht y v l]
  obtain ⟨h1, h2, h3, hpk⟩ := weakSlotLiftAt_planOK hok.1 A R (weakWindowLrFloor_ge_JN A 0)
  obtain ⟨_, ⟨pk⟩⟩ := hpk x.c x.i x.lower x.upper
  have hfl := weakOrderFloors_of_orders A 0 (weakWindowLrFloor A 0) _ h1 h2 h3
    (Nat.mul_pos A.Jw_pos A.Nw_pos) le_rfl
  have hgeometry := weakCoarsePulseGeometry hcommon x
  have hΛ : 1 ≤ x.c.D.Λ := by
    rw [x.c.base_eq]
    have := (weakCommonCoeffPlan.baseThreshold_ge B).trans ((hcommon.1 B).trans x.c.base_ge)
    omega
  unfold Case.gluedFlux
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  by_cases hne : x.weight k t = 0
  · simp only [hne, zero_smul, neg_zero]
  · rw [x.pulseFlux_eq_of_slotLift hk hgeometry hΛ (Reduction.weakPassageRawSetting x.c).kappa_pos
      ((horder A).trans x.input.sX_ge) ((horder A).trans x.input.sZ_ge) _ hfl
      (pk ⟨k, CycleComparison.LiftSetting.obsPulse_odd hk⟩) a ha t ht hne y v l, smul_neg]
end

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect.Mean
end
end
end

section
@[expose] public noncomputable section

section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect.Mean

/-! The path lifts used in the weak mean identity. The source witness is chosen with
exactly `cdEdgeSource`, and its native path lifts restrict to the fixed weak cap.
The native ladder is the whole slow space. No all-cap coefficient estimate is used. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly Finite.WeakLift Window CycleComparison.Lift

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

namespace Case
variable (x : Case plan R)

abbrev menu : WeakMenu := ⟨A.Nw, A.Rw, R.sX, R.sZ, A.η₀, x.c.M + A.Jw⟩
abbrev incomingOrder : ℕ := 1 + (x.c.M + A.Jw - x.i) * A.Nw
abbrev Witness := WeakPassageWitness x.c.P x.menu (x.c.D.termRW A.σw x.c.M)
  x.incomingOrder (x.c.stage x.i) (x.c.stage (x.i - 1))

theorem witness_exists : ∃ w : x.Witness,
    ∀ v u, w.e v u = cdEdgeSource x.c x.i x.lower x.upper v u := by
  have hex := (x.c.construction.2.2 x.i x.lower x.upper).1.2.2.2.2.2
  obtain ⟨idx, Cc, Cc0, hL, hL0, hinj, hall⟩ := Classical.choose_spec hex
  exact ⟨⟨cdEdgeSource x.c x.i x.lower x.upper, idx, Cc, Cc0, hL, hL0, hinj,
    fun v u γ => (hall v u γ).1, fun v u γ => (hall v u γ).2.1,
    fun v u γ => (hall v u γ).2.2⟩, fun _ _ => rfl⟩

/-- A witness compatible with the classification used in the stored letters. -/
def witness : x.Witness := Classical.choose (witness_exists x)

theorem witness_edge (v u : CompIn (x.c.stage (x.i - 1)).comps) :
    x.witness.e v u = cdEdgeSource x.c x.i x.lower x.upper v u :=
  Classical.choose_spec (witness_exists x) v u

/-- A path of the re-capped incoming stage as a path of the original stage. -/
def originalPath {h : ℕ} (π : StagePath (weakWindowStage x.c x.i x.lower x.upper) h) :
    StagePath (x.c.stage x.i) h := ⟨π.step, π.joined⟩

/-- The fixed cap does not change a path's steps. -/
theorem originalPath_recap {h : ℕ}
    (π : StagePath (weakWindowStage x.c x.i x.lower x.upper) h) :
    (x.originalPath π).recap = π := by cases π; rfl

/-- Every slow offset of a native chain is admissible, unlike a chain with children. -/
theorem nativeLadder_univ (k : ℤ) (hk : Odd k)
    (hj : x.c.j₀ ≤ (x.c.stage x.i).level) :
    ladderOmega x.c.D A.bw x.c.j₀ (x.c.stage x.i).level k
      (nativeChain (x.c.stage x.i).level k) x.length = Set.univ := by
  have hlevel := (cd_stage_inv x.c x.i x.lower x.upper).1
  apply Set.eq_univ_of_forall
  intro Y
  change IsAdmissibleChain _ _ _ _ _ _
  rw [nativeChain_recenter]
  exact nativeChain_isCarrier x.c.D A.bw x.c.j₀ (x.c.stage x.i).level k 2
    (by rw [hlevel]; have := x.lower; omega) hj hk (x.length • Y)

/-- Lift data of a capped path on a specified context. -/
abbrev pathData {h : ℕ}
    (π : StagePath (weakWindowStage x.c x.i x.lower x.upper) h) (k : ℤ) (hk : Odd k)
    (c₀ : StageCtx x.c.D A.bw x.c.j₀ (x.c.stage x.i).level ⟨k, hk⟩) :
    LiftOperatorData (Fin (h + 1)) (fun _ => ℝ) x.cap :=
  familyLiftData x.c.D (x.c.stage x.i).level k c₀.1
    (x.c.D.eps ((x.c.stage x.i).level - 1))
    (pathEdges (weakWindowStage x.c x.i x.lower x.upper) π ⟨k, hk⟩ c₀)

/-- A source selects the path lift; its path data do not read the word or degree.
The decomposition uses the empty word and degree two by default. -/
abbrev pathCoefficients {h : ℕ}
    (π : StagePath (weakWindowStage x.c x.i x.lower x.upper) h) (k : ℤ) (hk : Odd k)
    (c₀ : StageCtx x.c.D A.bw x.c.j₀ (x.c.stage x.i).level ⟨k, hk⟩)
    (w : List WordLetter := []) (n : ℕ := 2) :
    ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ) :=
  x.witness.Cc (.inherited w h (x.originalPath π) n) k c₀.1

/-- Re-capping preserves the source's original localized path sequence. -/
theorem pathSequenceOn {h : ℕ}
    (π : StagePath (weakWindowStage x.c x.i x.lower x.upper) h) (k : ℤ) (hk : Odd k)
    (c₀ : StageCtx x.c.D A.bw x.c.j₀ (x.c.stage x.i).level ⟨k, hk⟩)
    (w : List WordLetter := []) (n : ℕ := 2) :
    IsLiftSequenceOn
      (ladderOmega x.c.D A.bw x.c.j₀ (x.c.stage x.i).level k c₀.1
        (x.c.D.eps ((x.c.stage x.i).level - 1)))
      (x.pathData π k hk c₀) R.sX R.sZ
      (x.c.D.slotStart (x.c.stage x.i).level k / x.c.D.cellScaleSq (x.c.stage x.i).level)
      ((((k : ℝ) + 61 / 48) * ocTau x.c.D.α x.c.D.q x.c.D.Λ (x.c.stage x.i).level) /
        x.c.D.cellScaleSq (x.c.stage x.i).level) A.Nw h (x.pathCoefficients π k hk c₀ w n) := by
  have hc := x.witness.lifts (.inherited w h (x.originalPath π) n) k c₀.1 ⟨c₀.2, hk⟩
  have hN : A.Nw ≤ x.cap :=
    (Nat.le_mul_of_pos_left A.Nw A.Jw_pos).trans (Nat.le_add_left _ _)
  have hrec := isLiftSequenceOn_recap (N := x.cap)
    (hN := weakStage_maxOrder_le x.c x.i x.lower x.upper)
    (𝒮 := (x.c.stage x.i).exports) x.c.order_ge (x.originalPath π) ⟨k, hk⟩ c₀
    k c₀.1 (x.c.D.eps ((x.c.stage x.i).level - 1)) hN hc
  rw [x.originalPath_recap π] at hrec
  exact hrec

end Case
end

/-! The carried history and native coefficient smoothness used in the weak mean
identification. The common certificate supplies every finite smoothness order.
This is a qualitative instantiation, with no new coefficient price or Dm-dependent
constant. The quantitative native regularity theorem is reused directly. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly Finite.WeakLift Window
open AVRegularity.Construction.Preservation.Residual.FluxCancellation.CovFluxReg
open AVRegularity.Providers.QuietAtlas

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- The common carrier and the complex-context floor place all native chains above their start. -/
theorem Case.startFloor (hcommon : WeakPassageCommonOK plan) (x : Case plan R) :
    x.c.j₀ + 2 ≤ x.c.M :=
  ((weakCommonPlan_complexContext weakBasePlan (weakCertConst weakBasePlan) weakBasePlan_complexContext).2
    (weakCoeffRequestOne R) x.c.j₀).trans ((hcommon.2 R x.c.j₀).trans x.c.level_ge)

/-- The construction carries its full availability-history invariant, not only quiet-time data. -/
theorem Case.history (x : Case plan R) :
    StageHistoryInvariant (x.c.stage x.i) (x.c.M + A.Jw) ∧
      FluxRecenterCovariant (x.c.stage x.i) := by
  obtain ⟨hΛ0, _, hζ, hband⟩ := Comparison.weakPassageInstance_base x.c
  have hΛ : 1 ≤ x.c.D.Λ := by omega
  have hcarrier : IsCarrierStart x.c.D.α x.c.D.q x.c.D.Λ A.bw 1 400 x.c.j₀ := by
    rw [x.c.alpha, x.c.q_eq, x.c.base_eq]
    exact x.c.carrier
  have hstart := GenSem.startBound_of_carrierStart hΛ le_rfl (by norm_num : (1 : ℝ) ≤ 400)
    hcarrier
  have hh := weakConstruction_history hΛ hζ A.bw_pos hstart
    (fun m => EntryWeakProofs.weakData_cellScaleSq_pos x.c.D hΛ hζ hband m)
    x.c.construction (x.c.M + A.Jw - x.i) (by have := x.lower; omega)
  rwa [show x.c.M + A.Jw - (x.c.M + A.Jw - x.i) = x.i by have := x.upper; omega] at hh

/-- The common certificate's qualitative generation clause, including the root stage. -/
theorem Case.holGen (hcommon : WeakPassageCommonOK plan) (x : Case plan R) :
    WeakHolGen (x.c.stage x.i) := by
  exact weakCommonCase_holGen R
    ((hcommon.1 B).trans x.c.base_ge) x.c.j₀ x.c.carrier x.c.M
    ((hcommon.2 R x.c.j₀).trans x.c.level_ge) x.c.D x.c.alpha x.c.q_eq
    x.c.base_eq x.c.profile_eq x.c.streams x.c.band x.c.terminal x.c.Dm
    x.c.order_ge x.c.P x.c.stage x.c.construction x.i x.lower.le x.upper

/-- The context denotation commutes with slow recentering, including inadmissible offsets. -/
theorem Case.fluxShift (hcommon : WeakPassageCommonOK plan) (x : Case plan R) :
    AVRegularity.Construction.Preservation.Residual.FluxCancellation.FluxRecenterShift
      (x.c.stage x.i) := by
  intro p ch hch y hchy t ht v u γ d I X z
  funext j
  obtain ⟨f, _, _, hf⟩ := x.holGen hcommon v u γ d I j
  obtain ⟨hΛ0, _, hζ, _⟩ := Comparison.weakPassageInstance_base x.c
  have hΛ : 1 ≤ x.c.D.Λ := by omega
  have hε : x.c.D.eps ((x.c.stage x.i).level - 1) ≠ 0 :=
    (Construction.Stream.ocEpsilon_pos hΛ).ne'
  have he : (ch.recenter x.c.D y).recenter x.c.D
      (x.c.D.eps ((x.c.stage x.i).level - 1) • X) =
      ch.recenter x.c.D (x.c.D.eps ((x.c.stage x.i).level - 1) •
        (X + (x.c.D.eps ((x.c.stage x.i).level - 1))⁻¹ • y)) := by
    rw [GenSem.recenter_recenter x.c.D hζ, smul_add, smul_inv_smul₀ hε, add_comm]
  rw [hf p ⟨ch.recenter x.c.D y, hchy⟩ t ht X z,
    hf p ⟨ch, hch⟩ t ht (X + (x.c.D.eps ((x.c.stage x.i).level - 1))⁻¹ • y) z, he]

/-- Every actual native flux of the incoming stage is jointly smooth in the two spatial
variables. The empty finest stage is included, and no cap is charged to a constant. -/
theorem Case.fluxSmooth (hcommon : WeakPassageCommonOK plan) (x : Case plan R) :
    ActualFluxJointSmooth (x.c.stage x.i) := by
  intro p v u γ d I t ht n
  by_cases heq : x.i = x.c.M + A.Jw
  · have hz : ∀ v u, IsEmpty ((x.c.stage x.i).fam.Γ v u) := by
      rw [heq]
      exact x.c.construction.2.1.2.2.1
    exact ((hz v u).false γ).elim
  have hbase : weakCommonCoeffPlan.baseThreshold B ≤ A.Λ := (hcommon.1 B).trans x.c.base_ge
  have hlev : weakCommonCoeffPlan.levelThreshold (weakCoeffRequestOne R) x.c.j₀ ≤ x.c.M :=
    (hcommon.2 R x.c.j₀).trans x.c.level_ge
  let cs := weakCommonCase R hbase x.c.j₀ x.c.carrier x.c.M hlev x.c.D x.c.alpha x.c.q_eq
    x.c.base_eq x.c.profile_eq x.c.streams x.c.band x.c.terminal x.c.Dm x.c.order_ge x.c.P
    x.c.stage x.c.construction
  obtain ⟨cost, hcost, hc⟩ : ∃ cost : ℝ, 0 ≤ cost ∧ WeakCertified cost
      (weakReserve cs.inst x.i) (weakWeight cs.inst x.i) (x.c.stage x.i) := by
    have h := weakCommonCase_certified R hbase x.c.j₀ x.c.carrier x.c.M hlev x.c.D x.c.alpha
      x.c.q_eq x.c.base_eq x.c.profile_eq x.c.streams x.c.band x.c.terminal x.c.Dm
      x.c.order_ge x.c.P x.c.stage x.c.construction (x.c.M + A.Jw - x.i)
      (by have := x.lower; omega)
    rw [show x.c.M + A.Jw - (x.c.M + A.Jw - x.i) = x.i by have := x.upper; omega] at h
    exact ⟨_, h.1, h.2⟩
  obtain ⟨hΛ0, hq, hζ, _⟩ := Comparison.weakPassageInstance_base x.c
  have hΛ : 1 ≤ x.c.D.Λ := by omega
  have hcar : IsCarrierStart x.c.D.α x.c.D.q x.c.D.Λ A.bw 1 400 x.c.j₀ := by
    rw [x.c.alpha, x.c.q_eq, x.c.base_eq]
    exact x.c.carrier
  have hpar := hc.weakHolGen.isSlotTransverse hΛ hζ A.bw_pos
    (GenSem.startBound_of_carrierStart hΛ le_rfl (by norm_num : (1 : ℝ) ≤ 400) hcar)
  have hlevel := (cd_stage_inv x.c x.i x.lower x.upper).1
  have hf := x.startFloor hcommon
  have hm : 0 ≤ weakReserve cs.inst x.i := by
    change 0 ≤ 1 + ((x.i - x.c.M : ℕ) : ℝ) / (A.Jw : ℝ)
    positivity
  have hm2 : weakReserve cs.inst x.i ≤ 2 := by
    change 1 + ((x.i - x.c.M : ℕ) : ℝ) / (A.Jw : ℝ) ≤ 2
    have hJ : (0 : ℝ) < A.Jw := Nat.cast_pos.mpr A.Jw_pos
    have hi : ((x.i - x.c.M : ℕ) : ℝ) ≤ A.Jw := by
      exact_mod_cast (show x.i - x.c.M ≤ A.Jw by have := x.upper; omega)
    have hd := (div_le_one hJ).mpr hi
    linarith only [hd]
  have hlen : ((x.c.stage x.i).fam.identity v u γ).record.length ≤
      x.c.D.eps (x.c.stage x.i).level := by
    have hp := x.c.construction.2.2 (x.i + 1) (by have := x.lower; omega)
      (by have := x.upper; omega)
    have hl := IsWeakPassage.length_eq hp.1 hp.2
    rw [Nat.add_sub_cancel] at hl
    have hnext := EntryWeakProofs.weakConstruction_level x.c.P _ x.c.M A.Jw 0 _ x.c.stage
      x.c.construction (x.i + 1) (by have := x.lower; omega) (by have := x.upper; omega)
    rw [hl v u γ, hnext, hlevel]
    exact Applications.eps_antitone hq (by omega) (Nat.le_succ x.i)
  exact weakCertified_native_flux_joint_contDiff hc hcost hm hm2 (by rw [hlevel]; have := x.lower; omega)
    (by rw [hlevel]; have := x.lower; omega) A.bw_pos
    (Construction.Stream.ocEpsilon_pos hΛ) (Construction.Stream.ocEpsilon_pos hΛ) hpar p
    (x.natural.2.2.1 p) v u γ hlen d I n t ht
end

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect.Mean
end

section
open Homogenization MeasureTheory Set AVenhance AVRegularity.Sobolev
namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect.Mean

/-! The unrestricted path-decomposition setting at a weak passage. This uses
`HLDecomp.Setting` directly: the successor input's terminal-level inequality is
not a hypothesis of that API. Every reserve uses the fixed weak cap. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly Finite.WeakLift Window
open AVRegularity.Construction.Preservation.Residual.FluxCancellation
open AVRegularity.Providers.PathDecomp

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- The native context, at a level above the carrier start. -/
def Case.native (x : Case plan R) (k : ℤ) (hk : Odd k)
    (hj : x.c.j₀ ≤ (x.c.stage x.i).level) :
    StageCtx x.c.D A.bw x.c.j₀ (x.c.stage x.i).level ⟨k, hk⟩ :=
  ⟨nativeChain (x.c.stage x.i).level k, nativeChain_isCarrier x.c.D A.bw x.c.j₀
    (x.c.stage x.i).level k 2
    (by rw [(cd_stage_inv x.c x.i x.lower x.upper).1]; have := x.lower; omega) hj hk 0⟩

/-- The path models used by the decomposition, including its empty path. -/
abbrev Case.nativePaths (x : Case plan R) (k : ℤ) (hk : Odd k)
    (hj : x.c.j₀ ≤ (x.c.stage x.i).level) :=
  fun h (π : StagePath (weakWindowStage x.c x.i x.lower x.upper) h) =>
    x.pathCoefficients π k hk (x.native k hk hj)

/-- The complete hypotheses of the generic decomposition, at the cap `1+Jw*Nw`. -/
theorem Case.pathSetting (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (k : ℤ) (hk : Odd k) (hj : x.c.j₀ ≤ (x.c.stage x.i).level)
    (hX : A.Nw + 1 + x.cap ≤ R.sX) (hZ : A.Nw + 1 + x.cap ≤ R.sZ) :
    HLDecomp.Setting (weakWindowStage x.c x.i x.lower x.upper)
      (x.c.stage x.i).level k (nativeChain (x.c.stage x.i).level k) x.length
      ⟨k, hk⟩ (x.native k hk hj) (x.left k) (x.right k) (A.Jw * A.Rw) A.Nw
      R.sX R.sZ (x.nativePaths k hk hj) := by
  classical
  let G := weakWindowStage x.c x.i x.lower x.upper
  let ctx := x.native k hk hj
  have hlevel := (cd_stage_inv x.c x.i x.lower x.upper).1
  obtain ⟨hΛ0, _, hζ, hband⟩ := Comparison.weakPassageInstance_base x.c
  have hΛ : 1 ≤ x.c.D.Λ := by omega
  have hc : 0 < x.c.D.cellScaleSq (x.c.stage x.i).level :=
    EntryWeakProofs.weakData_cellScaleSq_pos x.c.D hΛ hζ hband _
  have heps : x.c.D.eps ((x.c.stage x.i).level - 1) = x.length := by rw [hlevel]
  have hctx : ctx = (x.c.stage x.i).actual ⟨k, hk⟩ :=
    Subtype.ext (x.natural.2.2.1 ⟨k, hk⟩).symm
  have hab : x.left k ≤ x.right k := by
    have h := EntryWeakProofs.weakData_lift_window x.c.D hΛ hζ hband (x.c.stage x.i).level k
    simpa only [hlevel, Case.left, Case.right, weakSlotLeft, weakSlotRight] using h
  refine ⟨hab, ?_, ?_, ?_, ?_, ?_, hX, hZ⟩
  · intro X
    obtain ⟨lo, hi, hlo, he⟩ := GenSem.familyLiftData_pos_window x.c.D hζ
      (x.c.stage x.i).level k (nativeChain (x.c.stage x.i).level k) x.length
      (G.fam.fiber ⟨k, hk⟩ ctx) (x.left k) (x.right k) X
    obtain ⟨Mv, hMv⟩ := GenSem.familyLiftData_v_bounded x.c.D hζ
      (x.c.stage x.i).level hk (nativeChain (x.c.stage x.i).level k) x.length
      (G.fam.fiber ⟨k, hk⟩ ctx)
    exact ⟨lo, hi, Mv, Uniqueness.windowData_of_elliptic _ _ _ _ lo hi Mv
      (fun t => GenSem.familyLiftData_symm x.c.D (x.c.stage x.i).level k
        (nativeChain (x.c.stage x.i).level k) x.length (G.fam.fiber ⟨k, hk⟩ ctx) t X 0 1)
      hlo he (fun t _ z => hMv t z)⟩
  · intro t _ a b
    exact (EntryWeakProofs.familyLiftData_metric_entry_smooth x.c.D (x.c.stage x.i).level k
      (nativeChain (x.c.stage x.i).level k) rfl x.length (G.fam.fiber ⟨k, hk⟩ ctx) t a b).of_le
      (by exact_mod_cast le_top)
  · intro t _ j
    refine ⟨?_, fun _ n z => ?_⟩
    · exact ((hl_familyLiftData_drift_smooth x.c.D (x.c.stage x.i).level k
        (nativeChain (x.c.stage x.i).level k) x.length (G.fam.fiber ⟨k, hk⟩ ctx) t j).of_le
        (by exact_mod_cast le_top)).comp contDiff_snd
    · exact congrFun (GenSem.ocPulseCellDrift_periodic (x.c.stage x.i).level
        (x.c.D.kap (x.c.stage x.i).level) hk t n z) j
  · intro v u γ t ht d α j
    have ht' : t ∈ HLWindow x.c.D G k := by simpa only [HLWindow, G, weakWindowStage, GenStage.recap, hlevel, Case.left, Case.right, weakSlotLeft, weakSlotRight] using ht
    have hw := hl_window_mem G k hc ht'
    by_cases hd : d ≤ x.cap
    · have hreg := x.fluxSmooth hcommon ⟨k, hk⟩ v u γ d α _ hw (A.Nw + 1 + x.cap)
      have hg : GoodField (A.Nw + 1 + x.cap) (fun X z =>
          G.fam.flux ⟨k, hk⟩ ctx v u γ d α (x.c.D.cellScaleSq (x.c.stage x.i).level * t)
            ((x.length / x.c.D.eps ((x.c.stage x.i).level - 1)) • X) z j) := by
        refine ⟨?_, fun X n z => ?_⟩
        · rw [hctx]
          exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) j).contDiff.comp
            (hreg.comp ((contDiff_fst.const_smul _).prodMk contDiff_snd))
        · dsimp only
          exact congrFun ((x.c.stage x.i).fam.flux_periodic ⟨k, hk⟩ ctx v u γ d α _ _ n z) j
      exact hg.congr fun X z => by simp only [stageDat, hd, ite_true, G, ctx]
    · exact GoodField.zero.congr fun X z => by simp only [stageDat, hd, ite_false, Pi.zero_apply]
  · intro h _hh π
    have hl := x.pathSequenceOn π k hk ctx
    have hctxval : ctx.1 = nativeChain (x.c.stage x.i).level k := rfl
    rw [heps, hctxval, x.nativeLadder_univ k hk hj] at hl
    simpa only [Case.pathData, Case.nativePaths, Case.native, ctx, heps, hlevel, Case.left, Case.right, weakSlotLeft, weakSlotRight] using liftSequence_of_on_univ _ _ _ _ _ _ _ _ hl
end

/-! Recentring of the native weak sources. Path means use the existing path
covariance theorem. The eddy source reads only the scalar empty-path lift; its
translation follows from that same lift uniqueness and `liftApply_slowShift`. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly Finite.WeakLift Window GenSem
open AVRegularity.Construction.Preservation.Residual.FluxCancellation
open CycleComparison.LiftMeanEntrywise CycleComparison.Lift

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- Recentring a native chain remains admissible at every physical label. -/
private theorem native_shift_admissible (x : Case plan R) (k : ℤ) (hk : Odd k)
    (hj : x.c.j₀ ≤ (x.c.stage x.i).level) (y : Vec 2) :
    IsAdmissibleChain x.c.D A.bw x.c.j₀ (x.c.stage x.i).level k
      ((nativeChain (x.c.stage x.i).level k).recenter x.c.D y) := by
  rw [nativeChain_recenter]
  exact nativeChain_isCarrier x.c.D A.bw x.c.j₀ (x.c.stage x.i).level k 2
    (by rw [(cd_stage_inv x.c x.i x.lower x.upper).1]; have := x.lower; omega) hj hk y

/-- The scalar eddy mean commutes with a native slow-label translation. -/
theorem Case.eddyRecenter (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (k : ℤ) (hk : Odd k) (hj : x.c.j₀ ≤ (x.c.stage x.i).level)
    (y : Vec 2) (n : ℕ) (t : ℝ)
    (ht : t ∈ ocPulseWindow x.c.D.α x.c.D.q x.c.D.Λ (x.c.stage x.i).level k)
    (f : Vec 2 → ℝ) :
    weakEddyFlux x.c.D (x.c.stage x.i).level
      (x.c.D.eps ((x.c.stage x.i).level - 1))
      (familyLiftData (Dm := x.c.Dm) (hv := fun _ : Fin 1 => ℝ) x.c.D
        (x.c.stage x.i).level k ((nativeChain (x.c.stage x.i).level k).recenter x.c.D y)
        (x.c.D.eps ((x.c.stage x.i).level - 1)) (fun _ _ _ => []))
      (x.witness.Cc0 k ((nativeChain (x.c.stage x.i).level k).recenter x.c.D y))
      n t (fun z => f (y + z)) 0 =
    weakEddyFlux x.c.D (x.c.stage x.i).level
      (x.c.D.eps ((x.c.stage x.i).level - 1))
      (familyLiftData (Dm := x.c.Dm) (hv := fun _ : Fin 1 => ℝ) x.c.D
        (x.c.stage x.i).level k (nativeChain (x.c.stage x.i).level k)
        (x.c.D.eps ((x.c.stage x.i).level - 1)) (fun _ _ _ => []))
      (x.witness.Cc0 k (nativeChain (x.c.stage x.i).level k)) n t f y := by
  classical
  let G := x.c.stage x.i
  let ch := nativeChain G.level k
  let ρ := x.c.D.eps (G.level - 1)
  let Cc := x.witness.Cc0 k ch
  let Cc' := x.witness.Cc0 k (ch.recenter x.c.D y)
  have hch : IsAdmissibleChain x.c.D A.bw x.c.j₀ G.level k ch :=
    (x.native k hk hj).2
  have hchy := native_shift_admissible x k hk hj y
  obtain ⟨hΛ0, _, hζ, hband⟩ := Comparison.weakPassageInstance_base x.c
  have hΛ : 1 ≤ x.c.D.Λ := by omega
  have hρ : ρ ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  have hc := EntryWeakProofs.weakData_cellScaleSq_pos x.c.D hΛ hζ hband G.level
  let π : StagePath G 0 := ⟨Fin.elim0, fun j hj => by omega⟩
  have he (ctx : StageCtx x.c.D A.bw x.c.j₀ G.level ⟨k, hk⟩) :
      pathEdges G π ⟨k, hk⟩ ctx = fun _ _ _ => [] := by
    funext v u d
    unfold pathEdges
    rw [dite_eq_right (by omega)]
  have hC := Uniqueness.IsLiftSequence.toOn (x.witness.lifts0 k ch hk hch)
    (ladderOmega x.c.D A.bw x.c.j₀ G.level k ch ρ)
  have hC' := Uniqueness.IsLiftSequence.toOn
    (x.witness.lifts0 k (ch.recenter x.c.D y) hk hchy)
    (ladderOmega x.c.D A.bw x.c.j₀ G.level k (ch.recenter x.c.D y) ρ)
  have hcoef := ccov_lift_recenter (G := G) hΛ hζ (x.fluxShift hcommon) hc π k hk
    hch y hchy hρ R.sX R.sZ A.Nw Cc' Cc
    (by simpa only [he] using hC') (by simpa only [he] using hC)
  have htime := ccov_inv_mul_mem_window hc ht
  have hcoef' (m : ℕ) (α : DerivativeWord2 m) :
      Cc' 0 (n - 1) m α ((x.c.D.cellScaleSq G.level)⁻¹ * t) =
      slowShiftCoeff (ρ⁻¹ • y) (Cc 0 (n - 1)) m α ((x.c.D.cellScaleSq G.level)⁻¹ * t) := by
    funext X z v u
    apply hcoef 0 le_rfl (n - 1) m α _ htime X ?_ z v u
    exact native_shift_admissible x k hk hj (ρ • (X + ρ⁻¹ • y))
  let a : ℝ → Vec 2 → Fin 1 → ℝ := fun _ X => Pi.single 0 (f (ρ • X))
  let b : ℝ → Vec 2 → Fin 1 → ℝ := fun _ X => Pi.single 0 (f (y + ρ • X))
  have hb : ∀ Y, b ((x.c.D.cellScaleSq G.level)⁻¹ * t) Y =
      a ((x.c.D.cellScaleSq G.level)⁻¹ * t) (Y + ρ⁻¹ • y) := by
    intro Y
    simp only [a, b, smul_add, smul_inv_smul₀ hρ, add_comm y]
  have hL := Uniqueness.liftApply_congr (n := n - 1) (fun m _ α => hcoef' m α) (a := b) (ha := rfl)
  have hPh : liftApply (n - 1) (Cc' 0 (n - 1)) b
      ((x.c.D.cellScaleSq G.level)⁻¹ * t) 0 =
      liftApply (n - 1) (Cc 0 (n - 1)) a
        ((x.c.D.cellScaleSq G.level)⁻¹ * t) (ρ⁻¹ • y) := by
    funext z
    exact (congrFun (congrFun hL 0) z).trans (by
      simpa only [zero_add] using liftApply_slowShift (n - 1) (Cc 0 (n - 1))
        a b (ρ⁻¹ • y) _ hb 0 z)
  dsimp only [a, b, Cc, Cc', ρ, G, ch] at hPh
  funext j
  simp only [weakEddyFlux, smul_zero, hPh]
  rfl

/-- Every weak finer source has the required native label covariance. -/
theorem Case.sourceRecenter (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (s : WeakSource (x.c.stage x.i)) (k : ℤ) (hk : Odd k)
    (hj : x.c.j₀ ≤ (x.c.stage x.i).level) (y : Vec 2) (t : ℝ)
    (ht : t ∈ ocPulseWindow x.c.D.α x.c.D.q x.c.D.Λ (x.c.stage x.i).level k)
    (f : Vec 2 → ℝ) :
    s.fluxOp x.length (x.witness.Cc s) x.witness.Cc0 k t
        ((nativeChain (x.c.stage x.i).level k).recenter x.c.D y) (fun z => f (y + z)) 0 =
      s.fluxOp x.length (x.witness.Cc s) x.witness.Cc0 k t
        (nativeChain (x.c.stage x.i).level k) f y := by
  have hch : IsAdmissibleChain x.c.D A.bw x.c.j₀ (x.c.stage x.i).level k
      (nativeChain (x.c.stage x.i).level k) := (x.native k hk hj).2
  have hchy := native_shift_admissible x k hk hj y
  have heps : x.c.D.eps ((x.c.stage x.i).level - 1) = x.length := by
    rw [(cd_stage_inv x.c x.i x.lower x.upper).1]
  rw [← heps]
  obtain ⟨hΛ0, _, hζ, hband⟩ := Comparison.weakPassageInstance_base x.c
  have hΛ : 1 ≤ x.c.D.Λ := by omega
  have hc := EntryWeakProofs.weakData_cellScaleSq_pos x.c.D hΛ hζ hband (x.c.stage x.i).level
  have hρ : x.c.D.eps ((x.c.stage x.i).level - 1) ≠ 0 :=
    (Construction.Stream.ocEpsilon_pos hΛ).ne'
  have hchOdd : IsAdmissibleChain x.c.D A.bw x.c.j₀ (x.c.stage x.i).level k
      (nativeChain (x.c.stage x.i).level k) ∧ Odd k := ⟨hch, hk⟩
  have hchyOdd : IsAdmissibleChain x.c.D A.bw x.c.j₀ (x.c.stage x.i).level k
      ((nativeChain (x.c.stage x.i).level k).recenter x.c.D y) ∧ Odd k := ⟨hchy, hk⟩
  cases s with
  | inherited w h π n =>
    simp only [WeakSource.fluxOp, dite_eq_left hchyOdd, dite_eq_left hchOdd]
    have hL := x.witness.lifts (.inherited w h π n)
    have hp := ccov_pathMeanFlux_recenter (G := x.c.stage x.i) hΛ hζ
      (x.fluxShift hcommon) hc π k hk hch y hchy hρ R.sX R.sZ A.Nw
      (x.witness.Cc (.inherited w h π n) k
        ((nativeChain (x.c.stage x.i).level k).recenter x.c.D y))
      (x.witness.Cc (.inherited w h π n) k (nativeChain (x.c.stage x.i).level k))
      (hL k _ ⟨hchy, hk⟩) (hL k _ ⟨hch, hk⟩) n ht f 0 (by simpa only [add_zero] using hchy)
    simpa only [add_zero] using hp
  | eddy v w n =>
    simp only [WeakSource.fluxOp, dite_eq_left hchyOdd, dite_eq_left hchOdd]
    exact x.eddyRecenter hcommon k hk hj y n t ht f
end

/-! The incoming weak lift decomposes over its ordered paths on each native
pulse. The full native interval and the fixed weak cap are retained throughout.
This is the generic Hilbert path decomposition, with its setting supplied by the
weak construction rather than by a terminal successor input. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly Finite.WeakLift Window
open AVRegularity.Construction.Preservation.Residual.FluxCancellation

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

private theorem weakMean_window_comps (x : Case plan R) :
    (weakWindowStage x.c x.i x.lower x.upper).comps = (x.c.stage x.i).comps := rfl

private theorem weakMean_window_level (x : Case plan R) :
    (weakWindowStage x.c x.i x.lower x.upper).level = (x.c.stage x.i).level := rfl

/-- The incoming fibre, read without the actual-family output cutoff. -/
abbrev Case.nativeData (x : Case plan R) (k : ℤ) (hk : Odd k)
    (hj : x.c.j₀ ≤ (x.c.stage x.i).level) :=
  familyLiftData x.c.D (x.c.stage x.i).level k
    (nativeChain (x.c.stage x.i).level k) x.length
    ((weakWindowStage x.c x.i x.lower x.upper).fam.fiber ⟨k, hk⟩ (x.native k hk hj))

/-- Re-capping the incoming fibre preserves the native lift sequence. -/
theorem Case.nativeSequence (x : Case plan R) (k : ℤ) (hk : Odd k)
    (hj : x.c.j₀ ≤ (x.c.stage x.i).level) :
    IsLiftSequence (x.nativeData k hk hj) R.sX R.sZ (x.left k) (x.right k)
      A.Nw (A.Jw * A.Rw) (x.input.CcR x.i k) := by
  have hctx : x.native k hk hj = (x.c.stage x.i).actual ⟨k, hk⟩ :=
    Subtype.ext (x.natural.2.2.1 ⟨k, hk⟩).symm
  have hlevel := (cd_stage_inv x.c x.i x.lower x.upper).1
  have hs := weakSeqCap_of x.c x.r x.i x.lower x.upper x.input k hk
  have he : x.nativeData k hk hj = weakCapData x.c x.i k hk := by
    dsimp only [Case.nativeData]
    rw [hctx, hlevel]
    rfl
  rw [he]
  exact hs

/-- The full fibre and every path lift have the same path-candidate arrays on the native pulse. -/
theorem Case.decomposed (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (k : ℤ) (hk : Odd k) (hj : x.c.j₀ ≤ (x.c.stage x.i).level)
    (hX : A.Nw + 1 + x.cap ≤ R.sX) (hZ : A.Nw + 1 + x.cap ≤ R.sZ) :
    HLDecomp.Decomposed (weakWindowStage x.c x.i x.lower x.upper)
      (x.c.stage x.i).level x.length ⟨k, hk⟩ (x.native k hk hj)
      (x.left k) (x.right k) (A.Jw * A.Rw) (x.input.CcR x.i k)
      (x.nativePaths k hk hj) := by
  have hcap : 2 ≤ x.cap := by
    dsimp only [Case.cap]
    have := Nat.mul_pos A.Jw_pos A.Nw_pos
    omega
  exact (x.pathSetting hcommon k hk hj hX hZ).decomposed hcap (x.nativeSequence k hk hj)

/-- The functional of the native positive flux splits over its ordered paths. -/
theorem Case.nativePointFlux (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (k : ℤ) (hk : Odd k) (hj : x.c.j₀ ≤ (x.c.stage x.i).level)
    (hX : A.Nw + 1 + x.cap ≤ R.sX) (hZ : A.Nw + 1 + x.cap ≤ R.sZ)
    (g : ℕ) (hg : g + 1 ≤ A.Jw * A.Rw) (τ : ℝ) (hτ : τ ∈ Icc (x.left k) (x.right k))
    (a : ℝ → Vec 2 → ∀ v : CompIn (x.c.stage x.i).comps, ScalarH v.1.root)
    (ha : ContDiff ℝ (⊤ : ℕ∞) (a τ)) (n : ℕ) (X z : Vec 2) (j : Fin 2)
    (v : CompIn (x.c.stage x.i).comps) (ℓ : ScalarH v.1.root →L[ℝ] ℝ) :
    ℓ (liftFluxX (x.nativeData k hk hj) (x.input.CcR x.i k) a (g + 1) n τ X z j v) =
      ∑ᶠ π : StagePath (weakWindowStage x.c x.i x.lower x.upper) (g + 1),
        if π.tgt = v.1 ∧ π.src ∈ (x.c.stage x.i).comps then
          liftFluxX (x.pathData π k hk (x.native k hk hj))
            (x.nativePaths k hk hj (g + 1) π)
            (hlIn (weakWindowStage x.c x.i x.lower x.upper) π ℓ a)
            (g + 1) n τ X z j (Fin.last (g + 1))
        else 0 := by
  have hlevel := (cd_stage_inv x.c x.i x.lower x.upper).1
  simpa only [Case.pathData, Case.nativeData, Case.native, Case.length, hlevel, weakMean_window_comps] using
    hl_flux_pointwise_of_decomposed (x.pathSetting hcommon k hk hj hX hZ)
      (x.decomposed hcommon k hk hj hX hZ) hg hτ a ha n X z j v ℓ

/-- Fast continuity needed to integrate the finite path decomposition. -/
theorem Case.nativePathContinuous (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (k : ℤ) (hk : Odd k) (hj : x.c.j₀ ≤ (x.c.stage x.i).level)
    (hX : A.Nw + 1 + x.cap ≤ R.sX) (hZ : A.Nw + 1 + x.cap ≤ R.sZ)
    {g : ℕ} (hg : g ≤ A.Jw * A.Rw)
    (π : StagePath (weakWindowStage x.c x.i x.lower x.upper) g)
    (τ : ℝ) (hτ : τ ∈ Icc (x.left k) (x.right k))
    (a : ℝ → Vec 2 → ∀ v : CompIn (x.c.stage x.i).comps, ScalarH v.1.root)
    (ha : ContDiff ℝ (⊤ : ℕ∞) (a τ)) (r : ℕ) (ℓ : ScalarH r →L[ℝ] ℝ)
    (n : ℕ) (X : Vec 2) (j : Fin 2) :
    Continuous fun z => liftFluxX (x.pathData π k hk (x.native k hk hj))
      (x.nativePaths k hk hj g π) (hlIn (weakWindowStage x.c x.i x.lower x.upper) π ℓ a)
      g n τ X z j := by
  have hlevel := (cd_stage_inv x.c x.i x.lower x.upper).1
  simpa only [Case.pathData, Case.nativeData, Case.native, Case.length, hlevel, weakMean_window_comps] using
    hl_path_continuous_of_decomposed (x.pathSetting hcommon k hk hj hX hZ)
      (x.decomposed hcommon k hk hj hX hZ) hg π hτ a ha ℓ n X j

/-- Each positive native mean is the finite sum of the scalar path means into its component. -/
theorem Case.nativePositiveMean (hcommon : WeakPassageCommonOK plan) (x : Case plan R)
    (k : ℤ) (hk : Odd k) (hj : x.c.j₀ ≤ (x.c.stage x.i).level)
    (hX : A.Nw + 1 + x.cap ≤ R.sX) (hZ : A.Nw + 1 + x.cap ≤ R.sZ)
    (g : ℕ) (hg : g + 1 ≤ A.Jw * A.Rw) (τ : ℝ) (hτ : τ ∈ Icc (x.left k) (x.right k))
    (a : ℝ → Vec 2 → ∀ v : CompIn (x.c.stage x.i).comps, ScalarH v.1.root)
    (ha : ContDiff ℝ (⊤ : ℕ∞) (a τ)) (n : ℕ) (X : Vec 2) (j : Fin 2)
    (v : CompIn (x.c.stage x.i).comps) (ℓ : ScalarH v.1.root →L[ℝ] ℝ) :
    ℓ (fieldCellMean (fun z => liftFluxX (x.nativeData k hk hj)
        (x.input.CcR x.i k) a (g + 1) n τ X z j) v) =
      ∑ᶠ π : StagePath (weakWindowStage x.c x.i x.lower x.upper) (g + 1),
        if π.tgt = v.1 ∧ π.src ∈ (x.c.stage x.i).comps then
          fieldCellMean (fun z => liftFluxX
            (x.pathData π k hk (x.native k hk hj))
            (x.nativePaths k hk hj (g + 1) π)
            (hlIn (weakWindowStage x.c x.i x.lower x.upper) π ℓ a)
            (g + 1) n τ X z j) (Fin.last (g + 1))
        else 0 := by
  classical
  let G := weakWindowStage x.c x.i x.lower x.upper
  have hctx : x.native k hk hj = G.actual ⟨k, hk⟩ :=
    Subtype.ext (x.natural.2.2.1 ⟨k, hk⟩).symm
  have hdata : x.nativeData k hk hj = familyLiftData x.c.D G.level k
      (nativeChain G.level k) x.length (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩)) := by
    dsimp only [Case.nativeData]
    rw [hctx]
    rfl
  have heps : x.c.D.eps ((x.c.stage x.i).level - 1) = x.length := by
    rw [(cd_stage_inv x.c x.i x.lower x.upper).1]
  have hp := hl_cellMean_core (hr := ScalarH) (G := G) x.length (x.input.CcR x.i) k hk
    (x.native k hk hj).2 g (x.nativePaths k hk hj) τ a n X j v ℓ
    (fun v' ℓ' z => by
      have hp := x.nativePointFlux hcommon k hk hj hX hZ g hg τ hτ a ha n X z j v' ℓ'
      simp only [Case.pathData, Case.native, G, weakMean_window_level,
        weakMean_window_comps, heps, hdata, hlPathFlux] at hp ⊢
      with_unfolding_all exact hp)
    (fun r ℓ' π => by
      have hp := x.nativePathContinuous hcommon k hk hj hX hZ hg π τ hτ a ha r ℓ' n X j
      simpa only [Case.pathData, Case.native, G, weakMean_window_level, heps] using hp)
  simp only [← hctx, Case.nativeData, Case.pathData, Case.native, G,
    weakMean_window_level, weakMean_window_comps, heps] at hp ⊢
  with_unfolding_all exact hp
end

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect.Mean
end
end
end
