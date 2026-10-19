-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeakAssembly.LiftCarrierInverse
import AVRegularity.Construction.EntryScales.TerminalCore
import AVRegularity.CycleReference.FluxFastDiscrepancy

section
section
/-! The data and the named ingredient statements of the weak coefficient statement: the passage
context, the coefficient base, request, constants, plan and instance, and the encoding, generation,
certificate and majorant statements, all at one explicit uniform scale plan and encoded-stage
choice; no full invariant is assumed. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs.Assembly
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance AVRegularity.EntryWeakProofs
open AVRegularity.CycleComparison.Lift

/-- One actual previous weak passage, with precisely the hypotheses of the native lift API. -/
structure NativePassageContext where
  D : OCData
  Dm : ℕ
  bw : ℝ
  j₀ : ℕ
  G : GenStage D ScalarH Dm bw j₀
  G' : GenStage D ScalarH Dm bw j₀
  P : ProvParams
  Mn : WeakMenu
  rW : ℝ
  Din : ℕ
  passage : IsWeakPassage D P Mn rW Din G G'
  tags : G'.HasTags P
  q_gt_one : 1 < D.q
  base_ge : 128 ≤ D.Λ
  profile : IsFastProfile D.ζ
  band : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ
  carrier_small : bw ≤ 1 / 10000

/-- Construction data before all thresholds. -/
structure WeakCoefficientBase where
  α : ℝ
  s : ℝ
  hα₀ : 0 < α
  hα₁ : α < 1 / 3
  hs₀ : 0 < s
  hs₁ : s < (1 - α) / 2
  q : ℝ
  hq : IsAdmissibleQ α s q
  ζ : ℝ → ℝ
  hζ : IsFastProfile ζ

/-- Physical choices and the universal weak menu, before the moment threshold. -/
structure WeakCoefficientPhysical (B : WeakCoefficientBase) where
  Λ : ℕ
  φ₀ : Vec 2 → ℝ
  hφ₀ : Integrable φ₀
  smooth : ContDiff ℝ (⊤ : ℕ∞) φ₀
  nonneg : ∀ z, 0 ≤ φ₀ z
  mass : ∫ z, φ₀ z = 1
  support : Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall
  bw : ℝ
  bw_pos : 0 < bw
  bw_small : bw ≤ 1 / 10000
  Jw : ℕ
  τ : ℝ
  T₀ : ℝ
  Pw : ℝ
  η₀ : ℝ
  Jw_pos : 1 ≤ Jw
  τ_pos : 0 < τ
  τ_small : τ < T₀
  Pw_pos : 0 < Pw
  η₀_pos : 0 < η₀
  η₀_small : η₀ ≤ ocDelta B.α B.q / 8
  Nw : ℕ
  Rw : ℕ
  Lw : ℕ
  Nw_pos : 1 ≤ Nw
  Lw_le : Lw ≤ Jw * Nw
  σw : ℝ
  σw_pos : 0 < σw
  σw_small : σw < min (ocC B.α B.q) (B.q - 1)

/-- Requests, including the supplied radius. -/
structure WeakCoefficientRequest {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) where
  L : ℕ
  Kw : ℕ
  sX : ℕ
  sZ : ℕ
  nW : ℕ+
  kReq : InvConsts
  /-- The floor of the requested producer offset. -/
  kReq_G0 : 1 ≤ kReq.G0
  kernel_order : L + 1 ≤ 2 * (nW : ℕ)
  field_order : A.Lw + 5 ≤ Kw
  cK : ℝ
  cK_pos : 0 < cK
  cK_le : cK ≤ 1

/-- Shared constants. All leaves use this same choice, before the carrier and flow data.
The harmless extra bound `1 ≤ CL` permits the existing exact-length lemma to discharge lengths. -/
structure WeakCoefficientConstants {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakCoefficientRequest A) where
  CK : ℝ
  CL : ℝ
  Cχ : ℝ
  Cread : ℝ
  Cid : ℝ
  kW : InvConsts
  radius : kW.c₀ = R.cK
  allocation : IsWeakAllocation kW R.kReq R.L
  length_one_le : 1 ≤ CL
  CH : ℝ
  Υ : ℝ
  history_one_le : 1 ≤ CH
  chain_pos : 0 < Υ

/-- The uniform choices common to the twelve ingredients. This is data, not an invariant assumption.
Ingredients are indexed by one such plan, rather than asserting estimates for arbitrary
allocations or independently choosing incompatible constants. A proof must choose
this plan and prove the leaves together. -/
structure WeakCoefficientPlan where
  baseThreshold : WeakCoefficientBase → ℕ
  baseThreshold_ge : ∀ B, 128 ≤ baseThreshold B
  momentThreshold : ∀ {B}, WeakCoefficientPhysical B → ℕ
  constants : ∀ {B} {A : WeakCoefficientPhysical B},
    (R : WeakCoefficientRequest A) → WeakCoefficientConstants R
  levelThreshold : ∀ {B} {A : WeakCoefficientPhysical B}, WeakCoefficientRequest A → ℕ → ℕ

/-- A large-level data instance of a fixed uniform plan, before a stage is supplied. -/
structure WeakCoefficientInstance (plan : WeakCoefficientPlan) where
  base : WeakCoefficientBase
  physical : WeakCoefficientPhysical base
  request : WeakCoefficientRequest physical
  base_large : plan.baseThreshold base ≤ physical.Λ
  moments_large : plan.momentThreshold physical ≤ request.L
  j₀ : ℕ
  carrier : IsCarrierStart base.α base.q physical.Λ physical.bw
    (plan.constants request).CH (plan.constants request).Υ j₀
  M : ℕ
  level_large : plan.levelThreshold request j₀ ≤ M
  D : OCData
  hα : D.α = base.α
  hq : D.q = base.q
  hΛ : D.Λ = physical.Λ
  hζ : D.ζ = base.ζ
  stream : IsOCStreamSeq base.α base.q physical.Λ base.ζ D.Φ
  band : IsOCBandChain base.α base.q physical.Λ base.ζ M D.κ
  term : D.term = M
  Dm : ℕ
  order : 1 + physical.Jw * physical.Nw ≤ Dm
  P : ProvParams

abbrev WeakCoefficientInstance.menu {plan} (x : WeakCoefficientInstance plan) : WeakMenu :=
  ⟨x.physical.Nw, x.physical.Rw, x.request.sX, x.request.sZ, x.physical.η₀,
    x.M + x.physical.Jw⟩

/-- A stage of an actual construction on this data. -/
structure WeakCoefficientCase (plan : WeakCoefficientPlan) where
  inst : WeakCoefficientInstance plan
  stage : ℕ → GenStage inst.D ScalarH inst.Dm inst.physical.bw inst.j₀
  construction : IsWeakConstruction inst.D inst.P inst.menu inst.M inst.physical.Jw
    (inst.D.termRW inst.physical.σw inst.M) 0 stage

/-- Candidate encoded stages contain no certificates. The encoding ingredient proves the encoding and transports
structure; the generation ingredient certifies their registry; the certificate ingredient proves the complex bounds. -/
structure WeakEncodedCandidate {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
    (G : GenStage D ScalarH Dm bw j₀) where
  stage : GenStage D ScalarH Dm bw j₀
  relabel : CompIn G.comps ≃ CompIn stage.comps

abbrev WeakCoefficientEncodingChoice (plan : WeakCoefficientPlan) :=
  (c : WeakCoefficientCase plan) → WeakEncodedCandidate (c.stage c.inst.M)

def weakCaseRootMass {plan} (c : WeakCoefficientCase plan) : ℕ → ℝ :=
  weakRootWeight (c.stage c.inst.M).comps
    (fun v => weakMass c.inst.D c.inst.physical.Nw c.inst.physical.Jw c.inst.physical.η₀ v.1)

def weakCaseRootReadout {plan} (c : WeakCoefficientCase plan) : ℕ → ℝ :=
  weakRootWeight (c.stage c.inst.M).comps
    (fun v => weakReadoutWeight c.inst.D c.inst.physical.η₀ v.1)

/-- Encoding with a common size factor, and transport of the nonanalytic structure.
Depth, orders, lengths, widths and masses are discharged by the existing lemmas in the assembly. -/
def WeakEncodingTransportStatement (plan : WeakCoefficientPlan)
    (encode : WeakCoefficientEncodingChoice plan) : Prop :=
  ∀ c : WeakCoefficientCase plan,
    IsWeakEncoding c.inst.physical.Nw c.inst.physical.Jw c.inst.physical.η₀
      (weakCaseRootMass c) (weakCaseRootReadout c) (c.stage c.inst.M)
      (encode c).stage (encode c).relabel ∧
    ((c.stage c.inst.M).IsNatural (c.inst.M + c.inst.physical.Jw) →
      (encode c).stage.IsNatural (c.inst.M + c.inst.physical.Jw)) ∧
    ((c.stage c.inst.M).HasTags c.inst.P → (encode c).stage.HasTags c.inst.P) ∧
    ((c.stage c.inst.M).IsShiftInvariant → (encode c).stage.IsShiftInvariant) ∧
    ((c.stage c.inst.M).IsSlotTransverse → (encode c).stage.IsSlotTransverse)

/-- Generation: generated expression/denotation, uniqueness, parallel invariance, and the export floor.
The generated output is selected, never an arbitrary registry supplied by the consumer. -/
def WeakStageExprStatement (plan : WeakCoefficientPlan)
    (encode : WeakCoefficientEncodingChoice plan) : Prop :=
  ∀ c : WeakCoefficientCase plan,
    (encode c).stage.IsGenerated ∧ (encode c).stage.HasCertifiedExports c.inst.M

/-- The quantitative leaf certificate, including the holomorphic/phase clauses and
Wiener bounds, at the common size factor. The complex inverse and Fourier
steps use the carrier premise uniformly in history depth. No whole invariant is assumed. -/
def WeakStageCertificateStatement (plan : WeakCoefficientPlan)
    (encode : WeakCoefficientEncodingChoice plan) : Prop :=
  ∀ c : WeakCoefficientCase plan,
    (encode c).stage.IsContextCertified (plan.constants c.inst.request).kW

/-- A law and observation window after the datum-independent encoded stage has been selected. -/
structure WeakCoefficientWindow {plan : WeakCoefficientPlan} (c : WeakCoefficientCase plan) where
  law : BirthLaw
  rootMass : law.rootMass = weakCaseRootMass c
  rootReadout : law.rootReadout = weakCaseRootReadout c
  a : ℝ
  aM : ℝ
  start_le : a ≤ aM
  start_upper : aM ≤ a + 6 * c.inst.physical.Jw *
    ocTauPP c.inst.base.α c.inst.base.q c.inst.physical.Λ (c.inst.M + 1)

/-- Both row/column budgets of the ordinary and marker-conjugated record majorants. -/
def WeakMajorantBudget {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
    (G : GenStage D ScalarH Dm bw j₀) (law : BirthLaw) (S : ℝ) : Prop :=
  (∀ v u, 0 ≤ recordMajorant (G.mass law) G.fam v u) ∧
  (∀ v, ∑ u, recordMajorant (G.mass law) G.fam v u ≤ S) ∧
  (∀ u, ∑ v, recordMajorant (G.mass law) G.fam v u ≤ S) ∧
  (∀ v u, 0 ≤ G.marker law v / G.marker law u * recordMajorant (G.mass law) G.fam v u) ∧
  (∀ v, ∑ u, G.marker law v / G.marker law u * recordMajorant (G.mass law) G.fam v u ≤ S) ∧
  (∀ u, ∑ v, G.marker law v / G.marker law u * recordMajorant (G.mass law) G.fam v u ≤ S) ∧
  markedLedger (G.mass law) (G.marker law) G.fam ≤ S

/-- Record/ledger counting, including the selected size factor Cθ. -/
def WeakRecordMajorantStatement (plan : WeakCoefficientPlan)
    (encode : WeakCoefficientEncodingChoice plan) : Prop :=
  ∀ (c : WeakCoefficientCase plan) (w : WeakCoefficientWindow c),
    WeakMajorantBudget (encode c).stage w.law
      ((plan.constants c.inst.request).Cχ * c.inst.D.eps c.inst.M ^
        weakChi c.inst.base.α c.inst.base.q c.inst.physical.η₀)

/-- Envelopes: analytic, essential molecular, and pointwise molecular envelopes. The carrier start
and the supplied cK are those of the common plan. Schur sums are supplied separately by the record ingredient. -/
def WeakStageEnvelopesStatement (plan : WeakCoefficientPlan)
    (encode : WeakCoefficientEncodingChoice plan) : Prop :=
  ∀ (c : WeakCoefficientCase plan) (w : WeakCoefficientWindow c),
  let G := (encode c).stage
  let D := c.inst.D
  let k := (plan.constants c.inst.request).kW
  (∀ K : CompIn G.comps → ℕ, (∀ v, K v ≤ k.Ks) →
    (IsAnalyticEnvelope G.fam (G.mass w.law) (G.innerDomain (Set.Icc w.aM (w.a + c.inst.physical.T₀)) k.mEnv)
      (D.eps (G.level - 1)) k.Ca k.Kan k.Lan (recordMajorant (G.mass w.law) G.fam) ∧
    IsMolecularEnvelope G.fam (G.mass w.law) K
      (G.innerDomain (Set.Icc w.aM (w.a + c.inst.physical.T₀)) k.mEnv)
      (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1)) (rhoStar D k.c₀ G.level)
      k.Cm k.Jm (recordMajorant (G.mass w.law) G.fam)) ∧
    (IsAnalyticEnvelope (markerConj (G.marker w.law) G.fam) (G.mass w.law)
      (G.innerDomain (Set.Icc w.aM (w.a + c.inst.physical.T₀)) k.mEnv)
      (D.eps (G.level - 1)) k.Ca k.Kan k.Lan
      (fun v u => G.marker w.law v / G.marker w.law u * recordMajorant (G.mass w.law) G.fam v u) ∧
    IsMolecularEnvelope (markerConj (G.marker w.law) G.fam) (G.mass w.law) K
      (G.innerDomain (Set.Icc w.aM (w.a + c.inst.physical.T₀)) k.mEnv)
      (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1)) (rhoStar D k.c₀ G.level)
      k.Cm k.Jm
      (fun v u => G.marker w.law v / G.marker w.law u * recordMajorant (G.mass w.law) G.fam v u))) ∧
  IsSeedPointwiseMolecular w.law k G w.aM (w.a + c.inst.physical.T₀)

/-- Kernels: admissible paired kernels, exact stored width, scale inequalities and all regularizers. -/
def WeakStageKernelsStatement (plan : WeakCoefficientPlan)
    (encode : WeakCoefficientEncodingChoice plan) : Prop :=
  ∀ (c : WeakCoefficientCase plan) (w : WeakCoefficientWindow c),
  let G := (encode c).stage
  let D := c.inst.D
  let k := (plan.constants c.inst.request).kW
  let tA := w.aM
  let tB := w.a + c.inst.physical.T₀
  let P := c.inst.P
  let seedK : ℕ → KernelSpec := fun _ => isoPairedKernel (D.termRW c.inst.physical.σw c.inst.M) c.inst.request.nW
  let freshK := seedK
  let φ₀ := c.inst.physical.φ₀
  let hφ₀ := c.inst.physical.hφ₀
  (∀ v u (γ : G.fam.Γ v u), (G.kernelOf P seedK freshK v u γ).IsAdmissible k.Γk k.Lker ∧
    (G.kernelOf P seedK freshK v u γ).width = (G.fam.identity v u γ).record.width ∧
    (G.fam.identity v u γ).record.width ≤
      k.Cwid * rhoStar D k.c₀ G.level * D.eps G.level ^ k.σf ∧
    (G.fam.identity v u γ).record.width ≤
      k.Cwid * rhoEnh D k.cr G.level * D.eps (G.level - 1) ^ k.lamC ∧
    ∀ ϱ : ℝ, 0 < ϱ → ∀ kk ≤ k.Ks,
      IsSpatialRegularizerTorus ϱ kk c.inst.Dm tA tB k.cker (G.kernelOf P seedK freshK v u γ).width
        (G.sysS P seedK freshK φ₀ hφ₀ v u γ))

/-- Kernel prices: both kernel-price Schur estimates at the supplied radius. -/
def WeakStageKernelPriceStatement (plan : WeakCoefficientPlan)
    (encode : WeakCoefficientEncodingChoice plan) : Prop :=
  ∀ (c : WeakCoefficientCase plan) (w : WeakCoefficientWindow c),
  let G := (encode c).stage
  let D := c.inst.D
  let k := (plan.constants c.inst.request).kW
  let tA := w.aM
  let tB := w.a + c.inst.physical.T₀
  let P := c.inst.P
  let seedK : ℕ → KernelSpec := fun _ => isoPairedKernel (D.termRW c.inst.physical.σw c.inst.M) c.inst.request.nW
  let freshK := seedK
  let law := w.law
  let θK := (plan.constants c.inst.request).Cχ * D.eps c.inst.M ^
    weakChi c.inst.base.α c.inst.base.q c.inst.physical.η₀
  (∀ kk ≤ k.Ks, ∀ w : CompIn G.comps → ℝ, (w = fun _ => 1) ∨ w = G.marker law →
    SchurBound θK (kernelSchurMatrix (ι := CompIn G.comps) (h := fun v => ScalarH v.1.root)
      (Γ := G.fam.Γ) (G := fun _ u _ => ScalarH u.1.root) (D.kap G.level) (rhoStar D k.c₀ G.level)
      (fun v => G.mass law v / w v ^ 2) kk c.inst.Dm tA tB k.cker
      (fun v u γ => (G.kernelOf P seedK freshK v u γ).width)
      (fun _ u _ => ContinuousLinearMap.id ℝ (ScalarH u.1.root))
      (fun v u γ d => G.physCoeff v u γ d.1)))

/-- Quiet atlas: one consecutive quiet atlas with exactly native matching. -/
def WeakStageQuietAtlasStatement (plan : WeakCoefficientPlan)
    (encode : WeakCoefficientEncodingChoice plan) : Prop :=
  ∀ (c : WeakCoefficientCase plan) (w : WeakCoefficientWindow c),
  let G := (encode c).stage
  let D := c.inst.D
  let tA := w.aM
  let tB := w.a + c.inst.physical.T₀
  (∃ T : G.fam.Atlas,
    T.IsConsecutiveClosed (Set.Icc tA tB) ∧
    T.CoversQuiet (ocQuietTimes D.α D.q D.Λ D.ζ G.level) (Set.Icc tA tB) ∧
    T.IsQuiet (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1)) ∧
    (∀ p q (hpq : T.adjacent p q),
      ((G.fam.piece p).output ∩ (G.fam.piece q).output ∩ Set.Icc tA tB).Nonempty →
      T.sameCtx p q hpq (G.actual p) (G.actual q)) ∧
    (∀ p q (hpq : T.adjacent p q) c c', T.sameCtx p q hpq c c' →
      c = G.actual p ∧ c' = G.actual q))

/-- Quiet independence: enlarged-pulse transversality and fast independence on the trimmed quiet times. -/
def WeakStageIndependenceStatement (plan : WeakCoefficientPlan)
    (encode : WeakCoefficientEncodingChoice plan) : Prop :=
  ∀ (c : WeakCoefficientCase plan) (w : WeakCoefficientWindow c),
  let G := (encode c).stage
  let D := c.inst.D
  let tA := w.aM
  let tB := w.a + c.inst.physical.T₀
G.fam.IsTransverseOnPulses (enlargedPulse D G.level (Set.Icc tA tB)) parallelIndex ∧
  G.fam.IsFastIndependentOn (ocTrimmedQuietTimes D.α D.q D.Λ D.ζ G.level ∩ Set.Icc tA tB)

end AVRegularity.WeakEntryProofs.Assembly
end
end

section
/-! Uniform weak-kernel width bounds, with the molecular radius supplied by the consumer. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs.Assembly
open Filter Topology

/-- A width budget before the flow, terminal level and carrier are chosen. -/
structure WeakKernelWidthBudget (B : WeakCoefficientBase) (Λ : ℕ) (σ cK : ℝ) where
  C : ℝ
  positive : 0 < C
  threshold : ℕ
  bounds : ∀ M, threshold ≤ M → ∀ κ, IsOCBandChain B.α B.q Λ B.ζ M κ →
    ocEpsilon B.q Λ M ^ (1 + σ) ≤
      C * (cK * min (ocEpsilon B.q Λ M) (Real.sqrt (κ M / ocA B.α B.q Λ M))) *
        ocEpsilon B.q Λ M ^ (σ / 2) ∧
    ocEpsilon B.q Λ M ^ (1 + σ) ≤
      C * Real.sqrt (κ (M - 1) * ocTauPP B.α B.q Λ M) *
        ocEpsilon B.q Λ (M - 1) ^ (B.q * (1 + σ) - 1 - ocC B.α B.q)

/-- The terminal scale ledger and weak smallness ledger supply both widths. -/
theorem exists_weak_kernel_width_budget (B : WeakCoefficientBase) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ, Λ₀ ≤ Λ → ∀ σ cK : ℝ, 0 < σ → 0 < cK →
      Nonempty (WeakKernelWidthBudget B Λ σ cK) := by
  obtain ⟨Λ₀, hΛ₀, hterm⟩ := EntryScales.terminal_scales_core
    B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq B.hζ
  obtain ⟨Cw, hCw, hweak⟩ := EntryScales.weak_scales_core
    B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq
  refine ⟨Λ₀, hΛ₀, fun Λ hΛ σ cK hσ hcK => ?_⟩
  have h128 := hΛ₀.trans hΛ
  have hγ := (Scales.admissible_exponent_facts B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq).1
  have hCwp : 0 < Cw := zero_lt_one.trans_le hCw
  obtain ⟨Ct, Mt, hCt, ht⟩ := hterm Λ hΛ 1 zero_lt_one
  have hCtp : 0 < Ct := zero_lt_one.trans_le hCt
  have hevent := (EntryScales.epsilon_rpow_tendsto_zero B.hq.1 h128 hγ).eventually
    (gt_mem_nhds (inv_pos.mpr hCwp))
  obtain ⟨Mf, hMf⟩ := eventually_atTop.mp hevent
  let C : ℝ := max cK⁻¹ (2 ^ (1 + σ) * Ct)
  have hC : 0 < C := lt_max_of_lt_left (inv_pos.mpr hcK)
  refine ⟨⟨C, hC, max Mf (max Mt 1), fun M hM κ hκ => ?_⟩⟩
  have hx := Scales.epsilon_basic (m := M) B.hq.1 h128
  have hE := Scales.epsilon_basic (m := M - 1) B.hq.1 h128
  have hν : 0 < κ M := CycleReference.bandChain_pos (by omega) B.hζ hκ le_rfl
  have hA : 0 < ocA B.α B.q Λ M := by
    change 0 < ocEpsilon B.q Λ M ^ ((1 + B.α) - 2)
    exact Real.rpow_pos_of_pos hx.1 _
  have hsmall : Cw * ocEpsilon B.q Λ M ^ ocGamma B.α B.q ≤ 1 := by
    have hs := (hMf M ((le_max_left _ _).trans hM)).le
    have hh := mul_le_mul_of_nonneg_left hs hCwp.le
    rwa [mul_inv_cancel₀ hCwp.ne'] at hh
  have hweakM := (hweak Λ h128 M (κ M) hκ.1 (M + 1) (by omega)).2.1
  simp only [Nat.add_sub_cancel] at hweakM
  have hcap : ocEpsilon B.q Λ M ≤ Real.sqrt (κ M / ocA B.α B.q Λ M) := by
    apply Real.le_sqrt_of_sq_le
    have hh := (div_le_one hν).mp (hweakM.trans hsmall)
    exact (le_div_iff₀ hA).mpr (by simpa only [mul_comm] using hh)
  have hterminal := ht M ((le_max_left _ _).trans ((le_max_right _ _).trans hM)) κ hκ
  have hcoarse := hterminal.2.2.2.1
  simp only [one_mul] at hcoarse
  have hρ : 0 < Real.sqrt (κ (M - 1) * ocTauPP B.α B.q Λ M) := by
    apply Real.sqrt_pos.mpr
    exact mul_pos (CycleReference.bandChain_pos (by omega) B.hζ hκ (by omega))
      (Construction.Stream.ocTauPP_pos (by omega))
  constructor
  · rw [min_eq_left hcap, Real.rpow_add hx.1, Real.rpow_one]
    have hexp : ocEpsilon B.q Λ M ^ σ ≤ ocEpsilon B.q Λ M ^ (σ / 2) :=
      Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2.1 (by linarith)
    have hmul : 1 ≤ C * cK := by
      have := mul_le_mul_of_nonneg_right (le_max_left cK⁻¹ (2 ^ (1 + σ) * Ct)) hcK.le
      rwa [inv_mul_cancel₀ hcK.ne'] at this
    calc
      ocEpsilon B.q Λ M * ocEpsilon B.q Λ M ^ σ ≤
          ocEpsilon B.q Λ M * ocEpsilon B.q Λ M ^ (σ / 2) :=
        mul_le_mul_of_nonneg_left hexp hx.1.le
      _ ≤ (C * cK) * (ocEpsilon B.q Λ M * ocEpsilon B.q Λ M ^ (σ / 2)) :=
        le_mul_of_one_le_left (mul_nonneg hx.1.le (Real.rpow_nonneg hx.1.le _)) hmul
      _ = _ := by ring
  · have hM₁ : 1 ≤ M := (le_max_right _ _).trans ((le_max_right _ _).trans hM)
    have hstep := Scales.epsilon_q_step B.hq.1 B.hq.2.1 h128 hM₁
    have hrpow := Real.rpow_le_rpow hx.1.le hstep (by linarith : 0 ≤ 1 + σ)
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hE.1.le _),
      ← Real.rpow_mul hE.1.le] at hrpow
    have hrho : ocEpsilon B.q Λ (M - 1) ^ (1 + ocC B.α B.q) ≤
        Ct * Real.sqrt (κ (M - 1) * ocTauPP B.α B.q Λ M) := by
      have hh := (le_div_iff₀ hE.1).mp hcoarse
      have hh' := mul_le_mul_of_nonneg_left hh hCtp.le
      simp only [← mul_assoc, mul_inv_cancel₀ hCtp.ne', one_mul] at hh'
      rw [Real.rpow_add hE.1, Real.rpow_one]
      simpa only [mul_comm] using hh'
    have hsplit : ocEpsilon B.q Λ (M - 1) ^ (B.q * (1 + σ)) =
        ocEpsilon B.q Λ (M - 1) ^ (1 + ocC B.α B.q) *
        ocEpsilon B.q Λ (M - 1) ^ (B.q * (1 + σ) - 1 - ocC B.α B.q) := by
      rw [← Real.rpow_add hE.1]
      congr 1
      ring
    rw [hsplit] at hrpow
    calc
      ocEpsilon B.q Λ M ^ (1 + σ) ≤ _ := hrpow
      _ ≤ (2 ^ (1 + σ) * Ct) * Real.sqrt (κ (M - 1) * ocTauPP B.α B.q Λ M) *
          ocEpsilon B.q Λ (M - 1) ^ (B.q * (1 + σ) - 1 - ocC B.α B.q) := by
        have hh := mul_le_mul_of_nonneg_right hrho
          (Real.rpow_nonneg hE.1.le (B.q * (1 + σ) - 1 - ocC B.α B.q))
        have hh' := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ (2 : ℝ) ^ (1 + σ))
        simpa only [mul_assoc] using hh'
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hρ.le)
        (Real.rpow_nonneg hE.1.le _)

end AVRegularity.WeakEntryProofs.Assembly
end
end

section
/-! I4 at one selected encoding, with freely chosen common size factors and seed registry.
The same selection can therefore be shared with the generated-expression and certificate leaves. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs.Assembly

/-- Reroot the actual bottom stage and choose its common inflation and export registry. -/
def weakRootEncodingChoice (plan : WeakCoefficientPlan)
    (Cθ : WeakCoefficientCase plan → ℝ) (hCθ : ∀ c, 1 ≤ Cθ c)
    (exports : WeakCoefficientCase plan → SeedExports) : WeakCoefficientEncodingChoice plan :=
  fun c =>
    { stage := { weakScaledRootStage (c.stage c.inst.M) (Cθ c) (hCθ c) with
        exports := exports c }
      relabel := weakRootEquiv (c.stage c.inst.M).comps }

/-- I4 holds at any common witness inflation at least one, independently of the registry
chosen by I5. Existing encoding lemmas supply weights, records, depth and mass sums. -/
theorem weak_encoding_transport (plan : WeakCoefficientPlan)
    (Cθ : WeakCoefficientCase plan → ℝ) (hCθ : ∀ c, 1 ≤ Cθ c)
    (exports : WeakCoefficientCase plan → SeedExports) :
    WeakEncodingTransportStatement plan (weakRootEncodingChoice plan Cθ hCθ exports) := by
  intro c
  have he := weakConstruction_scaledRootEncoding c.inst.P c.inst.menu c.inst.M
    c.inst.physical.Jw (c.inst.D.termRW c.inst.physical.σw c.inst.M) 0 c.stage
    c.construction c.inst.physical.Jw_pos (Cθ c) (hCθ c)
  have hl := weakConstruction_scaledRootLaws c.inst.P c.inst.menu c.inst.M
    c.inst.physical.Jw (c.inst.D.termRW c.inst.physical.σw c.inst.M) 0 c.stage
    c.construction c.inst.physical.Jw_pos (Cθ c) (hCθ c)
  exact ⟨he, hl⟩

end AVRegularity.WeakEntryProofs.Assembly
end
end
end

section
section
/-! The original-order dimensional estimate pays every lower-order kernel price.
The finite order budget depends on the weak menu, rather than the ambient cap. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.WeakEntryProofs.Assembly

/-- Between the fine and coarse lengths, lowering the original order cannot increase price. -/
theorem weak_kernel_dimensional_factor (e h r : ℝ) (he : 0 < e) (hh : 0 ≤ h)
    (hr : 0 < r) (hhr : h ≤ r) (hre : r ≤ e) (n d : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) :
    h ^ (n - 2) * e ^ ((d : ℝ) - (n : ℝ)) ≤ r ^ (d - 2) := by
  have hsub : (d : ℝ) - (n : ℝ) = -((n - d : ℕ) : ℝ) := by
    rw [Nat.cast_sub hdn]
    ring
  rw [hsub, Real.rpow_neg he.le, Real.rpow_natCast]
  have hpow : h ^ (n - 2) ≤ r ^ (d - 2) * e ^ (n - d) := by
    rw [show n - 2 = (d - 2) + (n - d) by omega, pow_add]
    exact mul_le_mul (pow_le_pow_left₀ hh hhr _) (pow_le_pow_left₀ hh (hhr.trans hre) _)
      (pow_nonneg hh _) (pow_nonneg hr.le _)
  have hz : e ^ (n - d) ≠ 0 := (pow_pos he _).ne'
  calc
    _ ≤ (r ^ (d - 2) * e ^ (n - d)) * (e ^ (n - d))⁻¹ :=
      mul_le_mul_of_nonneg_right hpow (inv_nonneg.mpr (pow_nonneg he.le _))
    _ = _ := by rw [mul_assoc, mul_inv_cancel₀ hz, mul_one]

/-- Cancel diffusivity after comparing the original-order dimension with the kernel width. -/
theorem weak_kernel_dimensional_price (ν CK S h e r c : ℝ)
    (hν : 0 < ν) (hCK : 0 ≤ CK) (hS : 0 ≤ S) (he : 0 < e) (hh : 0 ≤ h)
    (hr : 0 < r) (hhr : h ≤ r) (hre : r ≤ e) (hc : 0 ≤ c)
    (n d : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) :
    (CK * S * ν * h ^ (n - 2) * e ^ ((d : ℝ) - (n : ℝ))) * c /
      (ν * r ^ (d - 2)) ≤ CK * S * c := by
  have hdim := weak_kernel_dimensional_factor e h r he hh hr hhr hre n d hd hdn
  have hb := mul_le_mul_of_nonneg_left hdim
    (mul_nonneg (mul_nonneg (mul_nonneg hCK hS) hν.le) hc)
  apply (div_le_iff₀ (mul_pos hν (pow_pos hr _))).mpr
  calc
    _ = (CK * S * ν * c) * (h ^ (n - 2) * e ^ ((d : ℝ) - (n : ℝ))) := by ring
    _ ≤ (CK * S * ν * c) * r ^ (d - 2) := hb
    _ = _ := by ring

end AVRegularity.WeakEntryProofs.Assembly
end
end

section
/-! A menu-bounded sum of positive kernel constants pays the physical coefficient price. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.WeakEntryProofs.Assembly

/-- Only orders at most the menu bound contribute, even when the ambient order is larger. -/
theorem weak_kernel_identity_price {E F : ℕ → Type*}
    [∀ d, NormedAddCommGroup (E d)] [∀ d, NormedSpace ℝ (E d)]
    [∀ d, NormedAddCommGroup (F d)] [∀ d, NormedSpace ℝ (F d)]
    (B : ∀ d, ℝ → Vec 2 → E d →L[ℝ] F d)
    (ν CK S h e r ρ : ℝ) (cker : ℕ → ℝ) (n K Dm k : ℕ) (a b : ℝ)
    (hν : 0 < ν) (hCK : 0 ≤ CK) (hS : 0 ≤ S) (he : 0 < e) (hh : 0 ≤ h)
    (hr : 0 < r) (hhr : h ≤ r) (hre : r ≤ e) (hρ : 0 ≤ ρ) (hρe : ρ ≤ e)
    (hnK : n ≤ K)
    (hzero : ∀ d, n < d → B d = fun _ _ => 0)
    (hcoeff : ∀ d, 2 ≤ d → d ≤ n →
      coefficientSeminorm e k a b (B d) ≤
        ENNReal.ofReal (CK * S * ν * h ^ (n - 2) * e ^ ((d : ℝ) - (n : ℝ)))) :
    (∑ d : ↥(Finset.Icc 2 Dm),
      (coefficientSeminorm ρ k a b (B d.1)).toReal * cker (d.1 - 2) /
        (ν * r ^ (d.1 - 2))) ≤
      (CK * ∑ d ∈ Finset.Icc 2 K, max 0 (cker (d - 2))) * S := by
  classical
  let T (d : ℕ) := (coefficientSeminorm ρ k a b (B d)).toReal * cker (d - 2) /
    (ν * r ^ (d - 2))
  have hz (d) (hd : n < d) : T d = 0 := by
    dsimp only [T]
    rw [hzero d hd, CycleJointProofs.coefficientSeminorm_zero_function]
    simp only [ENNReal.toReal_zero, zero_mul, zero_div]
  have hb (d : ℕ) (hd : 2 ≤ d) : T d ≤ CK * S * max 0 (cker (d - 2)) := by
    by_cases hdn : d ≤ n
    · have hdim : 0 ≤ CK * S * ν * h ^ (n - 2) * e ^ ((d : ℝ) - (n : ℝ)) :=
        mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCK hS) hν.le)
          (pow_nonneg hh _)) (Real.rpow_pos_of_pos he _).le
      have hc := (CycleJointProofs.coefficientSeminorm_radius_mono ρ e hρ hρe k a b
        (B d)).trans (hcoeff d hd hdn)
      have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hc
      rw [ENNReal.toReal_ofReal hdim] at hreal
      calc
        T d ≤ (coefficientSeminorm ρ k a b (B d)).toReal * max 0 (cker (d - 2)) /
            (ν * r ^ (d - 2)) := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_max_right _ _) ENNReal.toReal_nonneg)
          (mul_nonneg hν.le (pow_nonneg hr.le _))
        _ ≤ (CK * S * ν * h ^ (n - 2) * e ^ ((d : ℝ) - (n : ℝ))) *
            max 0 (cker (d - 2)) / (ν * r ^ (d - 2)) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hreal (le_max_left _ _))
            (mul_nonneg hν.le (pow_nonneg hr.le _))
        _ ≤ _ := weak_kernel_dimensional_price ν CK S h e r _ hν hCK hS he hh hr hhr hre
          (le_max_left _ _) n d hd hdn
    · rw [hz d (by omega)]
      exact mul_nonneg (mul_nonneg hCK hS) (le_max_left _ _)
  have htrunc : (∑ d ∈ Finset.Icc 2 Dm, T d) =
      ∑ d ∈ (Finset.Icc 2 Dm).filter (fun d => d ≤ K), T d := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hd hnot
    apply hz
    have : ¬ d ≤ K := by simpa only [Finset.mem_filter, hd, true_and] using hnot
    omega
  change (∑ d : ↥(Finset.Icc 2 Dm), T d.1) ≤ _
  rw [← Finset.sum_subtype (Finset.Icc 2 Dm) (fun _ => Iff.rfl) T, htrunc]
  calc
    _ ≤ ∑ d ∈ (Finset.Icc 2 Dm).filter (fun d => d ≤ K), CK * S * max 0 (cker (d - 2)) :=
      Finset.sum_le_sum fun d hd => hb d (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
    _ ≤ ∑ d ∈ Finset.Icc 2 K, CK * S * max 0 (cker (d - 2)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1,
          (Finset.mem_filter.mp hd).2⟩
      · intro d _ _
        exact mul_nonneg (mul_nonneg hCK hS) (le_max_left _ _)
    _ = _ := by rw [← Finset.mul_sum]; ring

end AVRegularity.WeakEntryProofs.Assembly
end
end

section
/-! The mass-normalized eddy factor has exactly the weak Schur exponent χw. -/
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs

private theorem weak_eddy_sqrt_factor {c E η : ℝ} (hc : 0 < c) (hE : 0 < E) :
    Real.sqrt ((c * E ^ (η / 2))⁻¹) = Real.sqrt c⁻¹ * E ^ (-η / 4) := by
  rw [mul_inv, Real.sqrt_mul (inv_nonneg.mpr hc.le)]
  congr 1
  rw [← Real.rpow_neg hE.le, Real.sqrt_eq_rpow, ← Real.rpow_mul hE.le]
  congr 1
  ring

/-- Abstract real arithmetic, separated from the construction data. -/
theorem weak_stored_eddy_rpow_bound {c E p C a η : ℝ}
    (hc : 0 < c) (hE : 0 < E) (hp : 0 ≤ p) (hb : p ≤ C * E ^ a) :
    Real.sqrt ((c * E ^ (η / 2))⁻¹) * (E ^ (-η) * p ^ 2) ≤
      Real.sqrt c⁻¹ * C ^ 2 * E ^ (2 * a - η - η / 4) := by
  rw [weak_eddy_sqrt_factor hc hE]
  have hh := pow_le_pow_left₀ hp hb 2
  rw [mul_pow, ← Real.rpow_natCast (E ^ a) 2, ← Real.rpow_mul hE.le] at hh
  have hm := mul_le_mul_of_nonneg_left hh
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg c⁻¹) (Real.rpow_nonneg hE.le (-η / 4)))
      (Real.rpow_nonneg hE.le (-η)))
  calc
    _ ≤ (Real.sqrt c⁻¹ * E ^ (-η / 4) * E ^ (-η)) * (C ^ 2 * E ^ (a * 2)) := by
      simpa only [mul_assoc, Nat.cast_ofNat] using hm
    _ = Real.sqrt c⁻¹ * C ^ 2 * (E ^ (-η / 4) * (E ^ (-η) * E ^ (a * 2))) := by ring
    _ = _ := by
      rw [← Real.rpow_add hE, ← Real.rpow_add hE]
      congr 2
      ring

namespace Assembly

/-- A uniform eddy constant for every flow and every weak passage level; no stage is involved. -/
theorem exists_weakStoredEddy_constant (B : WeakCoefficientBase) (A : WeakCoefficientPhysical B) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ M (D : OCData), D.α = B.α → D.q = B.q → D.Λ = A.Λ →
      D.term = M → IsOCBandChain B.α B.q A.Λ B.ζ M D.κ → 128 ≤ A.Λ →
      ∀ i, M < i → weakStoredEddyWeight D A.Nw A.Jw A.η₀ i ≤
        C * D.eps M ^ weakChi B.α B.q A.η₀ := by
  obtain ⟨Cw, _hCw, hw⟩ := EntryScales.weak_scales_core B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq
  let C : ℝ := max 1 (Real.sqrt (weakCw A.Nw A.Jw)⁻¹ * Cw ^ 2)
  refine ⟨C, le_max_left _ _, fun M D hα hq hΛ ht hband h128 i hi => ?_⟩
  have hDΛ : 1 ≤ D.Λ := by rw [hΛ]; omega
  have heps (j : ℕ) : 0 < D.eps j := Construction.Stream.ocEpsilon_pos hDΛ
  have hν : 0 < D.κ M := CycleReference.bandChain_pos (by omega) B.hζ hband le_rfl
  have hPe : D.weakPe i ≤ Cw * D.eps (i - 1) ^ weakAStar B.α B.q := by
    have hh := (hw A.Λ h128 M (D.κ M) hband.1 i hi).1
    simpa only [OCData.weakPe, OCData.kap, ht, min_eq_right hi.le, OCData.eps, hα, hq, hΛ,
      weakAStar] using hh
  have hPe0 : 0 ≤ D.weakPe i := by
    unfold OCData.weakPe OCData.kap
    rw [ht, min_eq_right hi.le]
    exact div_nonneg (Real.rpow_nonneg (heps i).le _) hν.le
  have hχ : 0 < weakChi B.α B.q A.η₀ := weakChi_pos B.hα₀ B.hq.1 B.hq.2.1 A.η₀_small
  have hmono : D.eps (i - 1) ^ weakChi B.α B.q A.η₀ ≤ D.eps M ^ weakChi B.α B.q A.η₀ := by
    apply Real.rpow_le_rpow (heps _).le _ hχ.le
    simpa only [OCData.eps, hq, hΛ] using EntryScales.epsilon_antitone B.hq.1 h128 (by omega : M ≤ i - 1)
  have hh := weak_stored_eddy_rpow_bound (η := A.η₀) (weakCw_strict_pos A.Nw A.Jw A.Nw_pos A.Jw_pos)
    (heps (i - 1)) hPe0 hPe
  change weakStoredEddyWeight D A.Nw A.Jw A.η₀ i ≤ _ at hh
  exact hh.trans ((mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (heps _).le _)).trans
    (mul_le_mul_of_nonneg_left hmono (zero_lt_one.trans_le (le_max_left _ _)).le))

end Assembly
end AVRegularity.WeakEntryProofs
end
end

section
/-! Exact passage interfaces and their shared pre-data choices. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.WeakEntryProofs.Assembly

/-- Exact type of `weak_passage_quiet_trace`, before any proof ingredients. -/
def WeakPassageQuietTraceStatement : Prop :=
  ∀ (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ),
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Jw : ℕ) (τ T₀ Pw η₀ : ℝ), 1 ≤ Jw → 0 < τ → τ < T₀ → 0 < Pw → 0 < η₀ →
      η₀ ≤ ocDelta α q / 8 →
    ∀ (Nw Rw Lw : ℕ), 1 ≤ Nw → Lw ≤ Jw * Nw →
    ∀ σw : ℝ, 0 < σw → σw < min (ocC α q) (q - 1) → ∃ L₀ : ℕ,
    ∀ (L Kw sX sZ : ℕ) (nW : ℕ+) (kReq : InvConsts), 1 ≤ kReq.G0 → L₀ ≤ L → L + 1 ≤ 2 * (nW : ℕ) → Lw + 5 ≤ Kw →
    ∃ (cK CK CL Cχ Cread Cid : ℝ) (kW : InvConsts),
      0 < cK ∧ kW.c₀ = cK ∧ IsWeakAllocation kW kReq L ∧
    ∃ (CHw Υw : ℝ), 1 ≤ CHw ∧ 0 < Υw ∧
    ∀ j₀ : ℕ, IsCarrierStart α q Λ bw CHw Υw j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ M D.κ → D.term = M →
    ∀ (Dm : ℕ), 1 + Jw * Nw ≤ Dm →
    ∀ (P : ProvParams) (stage : ℕ → GenStage D ScalarH Dm bw j₀),
      IsWeakConstruction D P (⟨Nw, Rw, sX, sZ, η₀, M + Jw⟩ : WeakMenu) M Jw (D.termRW σw M) 0 stage →
    ∀ (a : ℝ) (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ),
      IsWeakSolutionOn (streamVel (D.Φ (M + Jw))) (D.κ M) a (a + T₀) f θ →
    ∀ (tq : ℕ → ℝ)
      (Ur : (i : ℕ) → ∀ v : CompIn (stage i).comps, ℝ → TorusHk Kw (ScalarH v.1.root))
      (Urw : (i : ℕ) → ∀ v : CompIn (stage i).comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
      (Urk : (i : ℕ) → ∀ v u (_ : (stage i).fam.Γ v u), ℝ → TorusHk (Kw + Dm - 1) (ScalarH u.1.root)),
      IsWeakReduction P φ₀ hφ₀ nW M Jw Kw 0 a (a + T₀) θ stage tq Ur Urw Urk →
    ∀ i : ℕ, M < i → i ≤ M + Jw → ∀ B : ℝ,
      (∀ t ∈ Set.Icc (tq (i + 1)) (tq i),
        weightedNorm 1 (fun v => weakMass D Nw Jw η₀ v.1) (fun _ => 1)
          (fun v => truncateTorusHk (Nat.zero_le Kw) (Ur i v t)) ≤ B) →
      weightedNorm (cK * D.eps (i - 1)) (fun v => weakMass D Nw Jw η₀ v.1) (fun _ => 1)
          (fun v => Ur i v (tq i)) ≤ CK * B

/-- `weak_passage_quiet_trace` at the given carrier constants; the statement
follows by `weakPassageQuietTrace_of_at`. -/
def WeakPassageQuietTraceAt (CHw Υw : ℝ) : Prop :=
  ∀ (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ),
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Jw : ℕ) (τ T₀ Pw η₀ : ℝ), 1 ≤ Jw → 0 < τ → τ < T₀ → 0 < Pw → 0 < η₀ →
      η₀ ≤ ocDelta α q / 8 →
    ∀ (Nw Rw Lw : ℕ), 1 ≤ Nw → Lw ≤ Jw * Nw →
    ∀ σw : ℝ, 0 < σw → σw < min (ocC α q) (q - 1) → ∃ L₀ : ℕ,
    ∀ (L Kw sX sZ : ℕ) (nW : ℕ+) (kReq : InvConsts), 1 ≤ kReq.G0 → L₀ ≤ L → L + 1 ≤ 2 * (nW : ℕ) → Lw + 5 ≤ Kw →
    ∃ (cK CK CL Cχ Cread Cid : ℝ) (kW : InvConsts),
      0 < cK ∧ kW.c₀ = cK ∧ IsWeakAllocation kW kReq L ∧
    ∀ j₀ : ℕ, IsCarrierStart α q Λ bw CHw Υw j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ M D.κ → D.term = M →
    ∀ (Dm : ℕ), 1 + Jw * Nw ≤ Dm →
    ∀ (P : ProvParams) (stage : ℕ → GenStage D ScalarH Dm bw j₀),
      IsWeakConstruction D P (⟨Nw, Rw, sX, sZ, η₀, M + Jw⟩ : WeakMenu) M Jw (D.termRW σw M) 0 stage →
    ∀ (a : ℝ) (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ),
      IsWeakSolutionOn (streamVel (D.Φ (M + Jw))) (D.κ M) a (a + T₀) f θ →
    ∀ (tq : ℕ → ℝ)
      (Ur : (i : ℕ) → ∀ v : CompIn (stage i).comps, ℝ → TorusHk Kw (ScalarH v.1.root))
      (Urw : (i : ℕ) → ∀ v : CompIn (stage i).comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
      (Urk : (i : ℕ) → ∀ v u (_ : (stage i).fam.Γ v u), ℝ → TorusHk (Kw + Dm - 1) (ScalarH u.1.root)),
      IsWeakReduction P φ₀ hφ₀ nW M Jw Kw 0 a (a + T₀) θ stage tq Ur Urw Urk →
    ∀ i : ℕ, M < i → i ≤ M + Jw → ∀ B : ℝ,
      (∀ t ∈ Set.Icc (tq (i + 1)) (tq i),
        weightedNorm 1 (fun v => weakMass D Nw Jw η₀ v.1) (fun _ => 1)
          (fun v => truncateTorusHk (Nat.zero_le Kw) (Ur i v t)) ≤ B) →
      weightedNorm (cK * D.eps (i - 1)) (fun v => weakMass D Nw Jw η₀ v.1) (fun _ => 1)
          (fun v => Ur i v (tq i)) ≤ CK * B

/-- Exact type of `weak_passage_comparison`, before any proof ingredients. -/
def WeakPassageComparisonStatement : Prop :=
  ∀ (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ),
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Jw : ℕ) (τ T₀ Pw η₀ : ℝ), 1 ≤ Jw → 0 < τ → τ < T₀ → 0 < Pw → 0 < η₀ →
      η₀ ≤ ocDelta α q / 8 →
    ∀ (Nw Rw Lw : ℕ), 1 ≤ Nw → Lw ≤ Jw * Nw →
      Pw + 2 * q ^ Jw + 1 + 2 < Nw * (q - 1) →
      Pw + 2 * q ^ Jw + 1 + q ^ Jw + 1 < 2 * weakAStar α q * (Rw + 1) →
    ∀ σw : ℝ, 0 < σw → σw < min (ocC α q) (q - 1) → ∃ L₀ SX SZ : ℕ,
    ∀ (L Kw sX sZ : ℕ) (nW : ℕ+) (kReq : InvConsts), 1 ≤ kReq.G0 → L₀ ≤ L → SX ≤ sX → SZ ≤ sZ →
      L + 1 ≤ 2 * (nW : ℕ) → Lw + 5 ≤ Kw →
    ∃ (cK CK CL Cχ Cread Cid : ℝ) (kW : InvConsts),
      0 < cK ∧ kW.c₀ = cK ∧ IsWeakAllocation kW kReq L ∧
    ∃ (CHw Υw : ℝ), 1 ≤ CHw ∧ 0 < Υw ∧
    ∀ j₀ : ℕ, IsCarrierStart α q Λ bw CHw Υw j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ M D.κ → D.term = M →
    ∀ (Dm : ℕ), 1 + Jw * Nw ≤ Dm →
    ∀ (P : ProvParams) (stage : ℕ → GenStage D ScalarH Dm bw j₀)
      (CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root)),
      IsWeakConstruction D P (⟨Nw, Rw, sX, sZ, η₀, M + Jw⟩ : WeakMenu) M Jw (D.termRW σw M) 0 stage →
      (∀ i, M < i → i ≤ M + Jw → IsWeakReadoutLifts i Nw (Jw * Rw) sX sZ (stage i) (CcR i)) →
    ∀ (a : ℝ) (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ),
      IsWeakSolutionOn (streamVel (D.Φ (M + Jw))) (D.κ M) a (a + T₀) f θ →
    ∀ (tq : ℕ → ℝ)
      (Ur : (i : ℕ) → ∀ v : CompIn (stage i).comps, ℝ → TorusHk Kw (ScalarH v.1.root))
      (Urw : (i : ℕ) → ∀ v : CompIn (stage i).comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
      (Urk : (i : ℕ) → ∀ v u (_ : (stage i).fam.Γ v u), ℝ → TorusHk (Kw + Dm - 1) (ScalarH u.1.root)),
      IsWeakReduction P φ₀ hφ₀ nW M Jw Kw 0 a (a + T₀) θ stage tq Ur Urw Urk →
      a < tq (M + Jw + 1) →
    ∀ i : ℕ, M < i → i ≤ M + Jw → ∀ (Φ : ℝ) (aU : ℝ → CompIn (stage (i - 1)).comps → Vec 2 → ℝ)
      (ê : ∀ v : CompIn (stage i).comps, ℝ → TorusHk 0 (ScalarH v.1.root))
      (êw : ∀ v : CompIn (stage i).comps, ℝ → TorusHk 1 (ScalarH v.1.root)),
      (∀ t ∈ Set.Icc (tq (i + 1)) (a + T₀),
        weightedNorm 1 (fun v => weakMass D Nw Jw η₀ v.1) (fun _ => 1)
          (fun v => truncateTorusHk (Nat.zero_le Kw) (Ur i v t)) ≤ Φ) →
      (∀ v, ∀ t ∈ Set.Icc (tq i) (a + T₀), IsClassicalRep (Ur (i - 1) v t) (aU t v) Lw) →
      (∀ v, ∀ t ∈ Set.Icc (tq i) (a + T₀),
        (ê v t).toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict AVenhance.unitCube]
          fun x => (truncateTorusHk (Nat.zero_le Kw) (Ur i v t)).toFunction.jet (valueIndex2 0) x -
            weakGluedLift i Nw (Jw * Rw) (stage i) (CcR i) t
              (weakReadoutStep i η₀ (stage i) (stage (i - 1)) (aU t)) v x) →
      (∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc (tq i) (a + T₀))),
        truncateTorusHk (Nat.le_succ 0) (êw v t) = ê v t) →
      strongEnergy 1 (D.κ M) (fun v => weakMass D Nw Jw η₀ v.1) (tq i) (a + T₀) ê êw ≤
        ENNReal.ofReal (CK * D.eps M ^ (Pw + 2 * q ^ Jw + 1) * Φ)

/-- `weak_passage_comparison` at the given carrier constants; the statement
follows by `weakPassageComparison_of_at`. -/
def WeakPassageComparisonAt (CHw Υw : ℝ) : Prop :=
  ∀ (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ),
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Jw : ℕ) (τ T₀ Pw η₀ : ℝ), 1 ≤ Jw → 0 < τ → τ < T₀ → 0 < Pw → 0 < η₀ →
      η₀ ≤ ocDelta α q / 8 →
    ∀ (Nw Rw Lw : ℕ), 1 ≤ Nw → Lw ≤ Jw * Nw →
      Pw + 2 * q ^ Jw + 1 + 2 < Nw * (q - 1) →
      Pw + 2 * q ^ Jw + 1 + q ^ Jw + 1 < 2 * weakAStar α q * (Rw + 1) →
    ∀ σw : ℝ, 0 < σw → σw < min (ocC α q) (q - 1) → ∃ L₀ SX SZ : ℕ,
    ∀ (L Kw sX sZ : ℕ) (nW : ℕ+) (kReq : InvConsts), 1 ≤ kReq.G0 → L₀ ≤ L → SX ≤ sX → SZ ≤ sZ →
      L + 1 ≤ 2 * (nW : ℕ) → Lw + 5 ≤ Kw →
    ∃ (cK CK CL Cχ Cread Cid : ℝ) (kW : InvConsts),
      0 < cK ∧ kW.c₀ = cK ∧ IsWeakAllocation kW kReq L ∧
    ∀ j₀ : ℕ, IsCarrierStart α q Λ bw CHw Υw j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ M D.κ → D.term = M →
    ∀ (Dm : ℕ), 1 + Jw * Nw ≤ Dm →
    ∀ (P : ProvParams) (stage : ℕ → GenStage D ScalarH Dm bw j₀)
      (CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root)),
      IsWeakConstruction D P (⟨Nw, Rw, sX, sZ, η₀, M + Jw⟩ : WeakMenu) M Jw (D.termRW σw M) 0 stage →
      (∀ i, M < i → i ≤ M + Jw → IsWeakReadoutLifts i Nw (Jw * Rw) sX sZ (stage i) (CcR i)) →
    ∀ (a : ℝ) (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ),
      IsWeakSolutionOn (streamVel (D.Φ (M + Jw))) (D.κ M) a (a + T₀) f θ →
    ∀ (tq : ℕ → ℝ)
      (Ur : (i : ℕ) → ∀ v : CompIn (stage i).comps, ℝ → TorusHk Kw (ScalarH v.1.root))
      (Urw : (i : ℕ) → ∀ v : CompIn (stage i).comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
      (Urk : (i : ℕ) → ∀ v u (_ : (stage i).fam.Γ v u), ℝ → TorusHk (Kw + Dm - 1) (ScalarH u.1.root)),
      IsWeakReduction P φ₀ hφ₀ nW M Jw Kw 0 a (a + T₀) θ stage tq Ur Urw Urk →
      a < tq (M + Jw + 1) →
    ∀ i : ℕ, M < i → i ≤ M + Jw → ∀ (Φ : ℝ) (aU : ℝ → CompIn (stage (i - 1)).comps → Vec 2 → ℝ)
      (ê : ∀ v : CompIn (stage i).comps, ℝ → TorusHk 0 (ScalarH v.1.root))
      (êw : ∀ v : CompIn (stage i).comps, ℝ → TorusHk 1 (ScalarH v.1.root)),
      (∀ t ∈ Set.Icc (tq (i + 1)) (a + T₀),
        weightedNorm 1 (fun v => weakMass D Nw Jw η₀ v.1) (fun _ => 1)
          (fun v => truncateTorusHk (Nat.zero_le Kw) (Ur i v t)) ≤ Φ) →
      (∀ v, ∀ t ∈ Set.Icc (tq i) (a + T₀), IsClassicalRep (Ur (i - 1) v t) (aU t v) Lw) →
      (∀ v, ∀ t ∈ Set.Icc (tq i) (a + T₀),
        (ê v t).toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict AVenhance.unitCube]
          fun x => (truncateTorusHk (Nat.zero_le Kw) (Ur i v t)).toFunction.jet (valueIndex2 0) x -
            weakGluedLift i Nw (Jw * Rw) (stage i) (CcR i) t
              (weakReadoutStep i η₀ (stage i) (stage (i - 1)) (aU t)) v x) →
      (∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc (tq i) (a + T₀))),
        truncateTorusHk (Nat.le_succ 0) (êw v t) = ê v t) →
      strongEnergy 1 (D.κ M) (fun v => weakMass D Nw Jw η₀ v.1) (tq i) (a + T₀) ê êw ≤
        ENNReal.ofReal (CK * D.eps M ^ (Pw + 2 * q ^ Jw + 1) * Φ)

/-- Requests fixed before any level, data, stage or solution. -/
structure WeakPassageRequest {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) where
  L : ℕ
  Kw : ℕ
  sX : ℕ
  sZ : ℕ
  nW : ℕ+
  kReq : InvConsts
  request_grade : 1 ≤ kReq.G0
  kernel_order : L + 1 ≤ 2 * (nW : ℕ)
  field_order : A.Lw + 5 ≤ Kw

/-- Uniform choices for the passage estimates. Their existence is not asserted here.
A proof must choose the radius and all constants before the ambient cap and stage. -/
structure WeakPassagePlan where
  baseFloor : WeakCoefficientBase → ℕ
  base_ge : ∀ B, 128 ≤ baseFloor B
  momentFloor : ∀ {B}, WeakCoefficientPhysical B → ℕ
  radius : ∀ {B} {A : WeakCoefficientPhysical B}, WeakPassageRequest A → ℝ
  radius_pos : ∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A), 0 < radius R
  traceC : ∀ {B} {A : WeakCoefficientPhysical B}, WeakPassageRequest A → ℝ
  jetOrder : ∀ {B} {A : WeakCoefficientPhysical B}, WeakPassageRequest A → ℕ
  coeffC : ∀ {B} {A : WeakCoefficientPhysical B}, WeakPassageRequest A → ℝ
  forcingOrder : ∀ {B} {A : WeakCoefficientPhysical B}, WeakPassageRequest A → ℕ
  forceC : ∀ {B} {A : WeakCoefficientPhysical B}, WeakPassageRequest A → ℝ
  energyC : ∀ {B} {A : WeakCoefficientPhysical B}, WeakPassageRequest A → ℝ
  energyC_nonneg : ∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A), 0 ≤ energyC R
  levelFloor : ∀ {B} {A : WeakCoefficientPhysical B}, WeakPassageRequest A → ℕ → ℕ
  /-- The floor of the lift orders `sX`, `sZ` of the comparison, chosen with the moment
  floor, before the request. -/
  liftFloor : ∀ {B}, WeakCoefficientPhysical B → ℕ

/-- One actual construction, after all constants and thresholds have been chosen. -/
structure WeakPassageInstance (plan : WeakPassagePlan) {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A) where
  base_ge : plan.baseFloor B ≤ A.Λ
  moment_ge : plan.momentFloor A ≤ R.L
  j₀ : ℕ
  /-- The carrier start at the common plan's constants. -/
  carrier : IsCarrierStart B.α B.q A.Λ A.bw 1 400 j₀
  M : ℕ
  level_ge : plan.levelFloor R j₀ ≤ M
  D : OCData
  alpha : D.α = B.α
  q_eq : D.q = B.q
  base_eq : D.Λ = A.Λ
  profile_eq : D.ζ = B.ζ
  streams : IsOCStreamSeq B.α B.q A.Λ B.ζ D.Φ
  band : IsOCBandChain B.α B.q A.Λ B.ζ M D.κ
  terminal : D.term = M
  Dm : ℕ
  order_ge : 1 + A.Jw * A.Nw ≤ Dm
  P : ProvParams
  stage : ℕ → GenStage D ScalarH Dm A.bw j₀
  construction : IsWeakConstruction D P
    (⟨A.Nw, A.Rw, R.sX, R.sZ, A.η₀, M + A.Jw⟩ : WeakMenu)
    M A.Jw (D.termRW A.σw M) 0 stage

/-- The given scalar solution and actual reduction; none of their estimates is assumed. -/
structure WeakPassageRun {plan : WeakPassagePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A} (c : WeakPassageInstance plan R) where
  a : ℝ
  f : Vec 2 → ℝ
  θ : ℝ → Vec 2 → ℝ
  scalar : IsWeakSolutionOn (streamVel (c.D.Φ (c.M + A.Jw))) (c.D.κ c.M) a (a + A.T₀) f θ
  tq : ℕ → ℝ
  Ur : (i : ℕ) → ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk R.Kw (ScalarH v.1.root)
  Urw : (i : ℕ) → ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk (R.Kw + 1) (ScalarH v.1.root)
  Urk : (i : ℕ) → ∀ v u (_ : (c.stage i).fam.Γ v u),
    ℝ → TorusHk (R.Kw + c.Dm - 1) (ScalarH u.1.root)
  reduction : IsWeakReduction c.P A.φ₀ A.hφ₀ R.nW c.M A.Jw R.Kw 0 a (a + A.T₀)
    θ c.stage tq Ur Urw Urk

/-- The quiet trace statement from its form at fixed carrier constants. -/
theorem weakPassageQuietTrace_of_at {CHw Υw : ℝ} (h1 : 1 ≤ CHw) (h0 : 0 < Υw)
    (h : WeakPassageQuietTraceAt CHw Υw) : WeakPassageQuietTraceStatement := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λ₀, h128, hΛ⟩ := h α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, h128, fun Λ hΛ' φ₀ hφ₀ e1 e2 e3 e4 bw hbw hbw' Jw τ T₀ Pw η₀ hJ hτ hτT hP hη hη'
    Nw Rw Lw hN hL σw hσ hσ' => ?_⟩
  obtain ⟨L₀, hL₀⟩ := hΛ Λ hΛ' φ₀ hφ₀ e1 e2 e3 e4 bw hbw hbw' Jw τ T₀ Pw η₀ hJ hτ hτT hP hη hη'
    Nw Rw Lw hN hL σw hσ hσ'
  refine ⟨L₀, fun L Kw sX sZ nW kReq hG hLL hn hK => ?_⟩
  obtain ⟨cK, CK, CL, Cχ, Cread, Cid, kW, hcK, hc₀, hk, hrest⟩ := hL₀ L Kw sX sZ nW kReq hG hLL hn hK
  exact ⟨cK, CK, CL, Cχ, Cread, Cid, kW, hcK, hc₀, hk, CHw, Υw, h1, h0, hrest⟩

/-- The comparison statement from its form at fixed carrier constants. -/
theorem weakPassageComparison_of_at {CHw Υw : ℝ} (h1 : 1 ≤ CHw) (h0 : 0 < Υw)
    (h : WeakPassageComparisonAt CHw Υw) : WeakPassageComparisonStatement := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λ₀, h128, hΛ⟩ := h α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, h128, fun Λ hΛ' φ₀ hφ₀ e1 e2 e3 e4 bw hbw hbw' Jw τ T₀ Pw η₀ hJ hτ hτT hP hη hη'
    Nw Rw Lw hN hL hNo hRo σw hσ hσ' => ?_⟩
  obtain ⟨L₀, SX, SZ, hL₀⟩ := hΛ Λ hΛ' φ₀ hφ₀ e1 e2 e3 e4 bw hbw hbw' Jw τ T₀ Pw η₀ hJ hτ hτT hP hη hη'
    Nw Rw Lw hN hL hNo hRo σw hσ hσ'
  refine ⟨L₀, SX, SZ, fun L Kw sX sZ nW kReq hG hLL hSX hSZ hn hK => ?_⟩
  obtain ⟨cK, CK, CL, Cχ, Cread, Cid, kW, hcK, hc₀, hk, hrest⟩ :=
    hL₀ L Kw sX sZ nW kReq hG hLL hSX hSZ hn hK
  exact ⟨cK, CK, CL, Cχ, Cread, Cid, kW, hcK, hc₀, hk, CHw, Υw, h1, h0, hrest⟩

end AVRegularity.WeakEntryProofs.Assembly
end
end
end
