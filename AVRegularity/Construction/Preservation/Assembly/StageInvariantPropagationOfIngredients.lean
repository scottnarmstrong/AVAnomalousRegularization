-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.Assembly.FullLiftFromInputs
import AVRegularity.Proofs.Results.Construction.ContextCertified.Assemble
import AVRegularity.Construction.Preservation.FullLift.NativePhysicalAllOrderSeminorm
import AVRegularity.Construction.Preservation.Frontier.GradeRows.ExtendedCertificates
import AVRegularity.Proofs.QuietAtlas.Successor.StageHistory
import AVRegularity.EntryTerminal.Ingredients.SeedQuiet.Proof
public import AVRegularity.Construction.Preservation.Assembly.SuccessorResidualIdentitiesOfIngredients
import AVRegularity.Construction.EntryScales.TerminalCore
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
import AVRegularity.Construction.Preservation.FullLift.UniformNativeNormalizedJointBounds
import AVRegularity.Proofs.QuietAtlas.Successor.QuietMatching

/-! The exact propagation statement from its remaining analytic and geometric clauses.
The common pre-data quantifiers are written once; conjunction chooses common thresholds,
carrier starts and level floors. Structural certificates and the ledger are discharged. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Assembly

/-- A clause evaluated on the propagated stage, window, ledger and kernel-price budgets. -/
abbrev StageInvariantClause :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ},
    BirthLaw → ProvParams → (ℕ → KernelSpec) → (ℕ → KernelSpec) →
    (φ₀ : Vec 2 → ℝ) → Integrable φ₀ → ℕ → InvConsts → ℝ → ℝ → ℝ → ℝ →
    GenStage D hr Dm bw j₀ → Prop

/-- A uniform production clause, under exactly the propagation prefix. -/
def StageProductionStatement (α s q : ℝ) (ζ : ℝ → ℝ) (clause : StageInvariantClause) : Prop :=
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ →
    ∀ (Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ : ℕ), 1 ≤ Ce → 0 < τe →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → 0 < kS.σf → 0 < kS.lamC →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min kS.σf (ocDelta α q + σ₀)) kS.lamC D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sX →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sZ →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∃ mStar : ℕ,
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
      [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
      (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ tA : ℝ, tS ≤ tA →
    ∀ (G G' : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
      clause law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kI (tA + 3 * ocTau α q Λ m) tf (CI * D.eps (m - 1) ^ min (ocDelta α q / 4) τe)
        (CI * D.eps ((m - 1) - 1) ^ (q * min (ocDelta α q / 4) τe)) (G'.retained m H J)

/-- Two uniform clauses admit common thresholds, carrier constants and starting levels. -/
theorem stage_production_and {α s q : ℝ} {ζ : ℝ → ℝ} {A B : StageInvariantClause}
    (ha : StageProductionStatement α s q ζ A) (hb : StageProductionStatement α s q ζ B) :
    StageProductionStatement α s q ζ (fun law P seedK freshK φ₀ hφ₀ M k a b S θ G =>
      A law P seedK freshK φ₀ hφ₀ M k a b S θ G ∧ B law P seedK freshK φ₀ hφ₀ M k a b S θ G) := by
  classical
  obtain ⟨Λa, hΛa, ha⟩ := ha
  obtain ⟨Λb, hΛb, hb⟩ := hb
  refine ⟨max Λa Λb, by omega, ?_⟩
  intro Λ hΛ
  obtain ⟨ca, hca, ha⟩ := ha Λ (by omega)
  obtain ⟨cb, hcb, hb⟩ := hb Λ (by omega)
  refine ⟨min ca cb, lt_min hca hcb, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  obtain ⟨ta, CHa, Υa, hCHa, hΥa, ha⟩ := ha φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ (hc₀upper.trans (min_le_left _ _)) hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  obtain ⟨tb, CHb, Υb, hCHb, hΥb, hb⟩ := hb φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ (hc₀upper.trans (min_le_right _ _)) hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  refine ⟨certificateThresholdJoin ta tb, max CHa CHb, max Υa Υb,
    hCHa.trans (le_max_left _ _), hΥa.trans_le (le_max_left _ _), ?_⟩
  intro kI hkI
  obtain ⟨CIa, Cwa, ha⟩ := ha kI (invariant_admissible_threshold_left hkI)
  obtain ⟨CIb, Cwb, hb⟩ := hb kI (invariant_admissible_threshold_right hkI)
  refine ⟨max CIa CIb, max Cwa Cwb, ?_⟩
  intro CI Cw j₀ hledger hstart
  have hLa : IsLedgerAdmissible Ce CI Cw CIa Cwa :=
    ⟨hledger.1, (le_max_left _ _).trans hledger.2.1,
      (le_max_left _ _).trans hledger.2.2.1, hledger.2.2.2⟩
  have hLb : IsLedgerAdmissible Ce CI Cw CIb Cwb :=
    ⟨hledger.1, (le_max_right _ _).trans hledger.2.1,
      (le_max_right _ _).trans hledger.2.2.1, hledger.2.2.2⟩
  have hA : ∀ i, 0 ≤ ocA α q Λ i := fun _ => (Real.rpow_pos_of_pos
    (Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ Λ)) _).le
  have hT : ∀ i, 0 ≤ ocTauPP α q Λ i := fun _ => (Construction.Stream.ocTauPP_pos (by omega)).le
  obtain ⟨ma, ha⟩ := ha CI Cw j₀ hLa (IsCarrierStart.mono hA hT
    (le_max_left _ _) (le_max_left _ _) (zero_le_one.trans hCHa) hΥa.le hstart)
  obtain ⟨mb, hb⟩ := hb CI Cw j₀ hLb (IsCarrierStart.mono hA hT
    (le_max_right _ _) (le_max_right _ _) (zero_le_one.trans hCHb) hΥb.le hstart)
  refine ⟨max ma mb, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA htA G G' hcascade hlevel hG hactual
  exact ⟨ha D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m (by omega) hn hnM tA htA G G' hcascade hlevel hG hactual, hb D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m (by omega) hn hnM tA htA G G' hcascade hlevel hG hactual⟩

/-- The StageBaseClause conjunct of the propagated invariant. -/
def StageBaseClause : StageInvariantClause := by
  intro hr _ _ _ _ _ _ _ D Dm bw j₀
  exact fun law P seedK freshK _φ₀ _hφ₀ M k _tA _tB S _θK G =>
  G.IsNatural M ∧ G.HasTags P ∧ G.IsGenerated ∧ G.IsShiftInvariant ∧
    G.IsSlotTransverse ∧ G.IsContextCertified k ∧ markedLedger (G.mass law) (G.marker law) G.fam ≤ S ∧
    ∀ v u (γ : G.fam.Γ v u), (G.kernelOf P seedK freshK v u γ).width =
      (G.fam.identity v u γ).record.width

/-- The StageEnvelopesClause conjunct of the propagated invariant. -/
def StageEnvelopesClause : StageInvariantClause := by
  intro hr _ _ _ _ _ _ _ D Dm bw j₀
  exact fun law _P _seedK _freshK _φ₀ _hφ₀ _M k tA tB S _θK G =>
  (∀ K : CompIn G.comps → ℕ, (∀ v, K v ≤ k.Ks) →
    IsEnvelope G.fam (G.mass law) K (G.innerDomain (Set.Icc tA tB) k.mEnv)
        (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1)) (rhoStar D k.c₀ G.level)
        (recordMajorant (G.mass law) G.fam) S k.Ca k.Kan k.Lan k.Cm k.Jm ∧
      IsEnvelope (markerConj (G.marker law) G.fam) (G.mass law) K
        (G.innerDomain (Set.Icc tA tB) k.mEnv)
        (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1)) (rhoStar D k.c₀ G.level)
        (fun v u => G.marker law v / G.marker law u * recordMajorant (G.mass law) G.fam v u)
        S k.Ca k.Kan k.Lan k.Cm k.Jm)

/-- The StageKernelAdmissibilityClause conjunct of the propagated invariant. -/
def StageKernelAdmissibilityClause : StageInvariantClause := by
  intro hr _ _ _ _ _ _ _ D Dm bw j₀
  exact fun _law P seedK freshK _φ₀ _hφ₀ _M k _tA _tB _S _θK G =>
  ∀ v u (γ : G.fam.Γ v u), (G.kernelOf P seedK freshK v u γ).IsAdmissible k.Γk k.Lker

/-- The StageKernelWidthsClause conjunct of the propagated invariant. -/
def StageKernelWidthsClause : StageInvariantClause := by
  intro hr _ _ _ _ _ _ _ D Dm bw j₀
  exact fun _law _P _seedK _freshK _φ₀ _hφ₀ _M k _tA _tB _S _θK G =>
  ∀ v u (γ : G.fam.Γ v u),
    (G.fam.identity v u γ).record.width ≤ k.Cwid * rhoStar D k.c₀ G.level * D.eps G.level ^ k.σf ∧
    (G.fam.identity v u γ).record.width ≤ k.Cwid * rhoEnh D k.cr G.level * D.eps (G.level - 1) ^ k.lamC

/-- The StageKernelRegularizersClause conjunct of the propagated invariant. -/
def StageKernelRegularizersClause : StageInvariantClause := by
  intro hr _ _ _ _ _ _ _ D Dm bw j₀
  exact fun _law P seedK freshK φ₀ hφ₀ _M k tA tB _S _θK G =>
  ∀ v u (γ : G.fam.Γ v u), ∀ ϱ : ℝ, 0 < ϱ → ∀ kk ≤ k.Ks,
    IsSpatialRegularizerTorus ϱ kk Dm tA tB k.cker (G.kernelOf P seedK freshK v u γ).width
      (G.sysS P seedK freshK φ₀ hφ₀ v u γ)

/-- The StageKernelPriceClause conjunct of the propagated invariant. -/
def StageKernelPriceClause : StageInvariantClause := by
  intro hr _ _ _ _ _ _ _ D Dm bw j₀
  exact fun law P seedK freshK _φ₀ _hφ₀ _M k tA tB _S θK G =>
  (∀ kk ≤ k.Ks, ∀ w : CompIn G.comps → ℝ, (w = fun _ => 1) ∨ w = G.marker law →
    SchurBound θK (kernelSchurMatrix (ι := CompIn G.comps) (h := fun v => hr v.1.root)
      (Γ := G.fam.Γ) (G := fun _ u _ => hr u.1.root) (D.kap G.level) (rhoStar D k.c₀ G.level)
      (fun v => G.mass law v / w v ^ 2) kk Dm tA tB k.cker
      (fun v u γ => (G.kernelOf P seedK freshK v u γ).width)
      (fun _ u _ => ContinuousLinearMap.id ℝ (hr u.1.root))
      (fun v u γ d => G.physCoeff v u γ d.1)))

/-- The StageQuietMatchingClause conjunct of the propagated invariant. -/
def StageQuietMatchingClause : StageInvariantClause := by
  intro hr _ _ _ _ _ _ _ D Dm bw j₀
  exact fun _law _P _seedK _freshK _φ₀ _hφ₀ _M _k tA tB _S _θK G =>
  (∃ T : G.fam.Atlas,
    T.IsConsecutiveClosed (Set.Icc tA tB) ∧
    T.CoversQuiet (ocQuietTimes D.α D.q D.Λ D.ζ G.level) (Set.Icc tA tB) ∧
    T.IsQuiet (D.kap G.level) (D.eps G.level) (D.eps (G.level - 1)) ∧
    (∀ p q (hpq : T.adjacent p q),
      ((G.fam.piece p).output ∩ (G.fam.piece q).output ∩ Set.Icc tA tB).Nonempty →
      T.sameCtx p q hpq (G.actual p) (G.actual q)) ∧
    (∀ p q (hpq : T.adjacent p q) c c', T.sameCtx p q hpq c c' →
      c = G.actual p ∧ c' = G.actual q)) ∧
  G.fam.IsTransverseOnPulses (enlargedPulse D G.level (Set.Icc tA tB)) parallelIndex ∧
  G.fam.IsFastIndependentOn (ocTrimmedQuietTimes D.α D.q D.Λ D.ζ G.level ∩ Set.Icc tA tB)

/-- The history locality carried to the next stage.
An empty restriction is vacuous and a seed parent supplies the same invariant; no identity
metric, positive word length or positive solution norm is required. -/
def StageHistoryClause : StageInvariantClause := by
  intro hr _ _ _ _ _ _ _ D Dm bw j₀
  exact fun _law _P _seedK _freshK _φ₀ _hφ₀ M _k _tA _tB _S _θK G =>
    StageHistoryInvariant G M

/-- The certificate proof supplies all structural clauses and the marked ledger. -/
theorem stage_base_of_certificates {α s q : ℝ} {ζ : ℝ → ℝ}
    (hcert : RetainedStageCertificatesStatement α s q ζ) :
    StageProductionStatement α s q ζ StageBaseClause := by
  classical
  obtain ⟨Λ₀, hΛ₀, hc⟩ := hcert
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ
  obtain ⟨cmax, hcmax, hc⟩ := hc Λ hΛ
  refine ⟨cmax, hcmax, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  obtain ⟨thr, CH, Υ, hCH, hΥ, hc⟩ := hc φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  refine ⟨thr, CH, Υ, hCH, hΥ, ?_⟩
  intro kI hkI
  obtain ⟨CIthr, Cwthr, hc⟩ := hc kI hkI
  refine ⟨CIthr, Cwthr, ?_⟩
  intro CI Cw j₀ hledger hstart
  obtain ⟨mStar, hc⟩ := hc CI Cw j₀ hledger hstart
  refine ⟨mStar, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA htA G G' hcascade hlevel hG hactual
  obtain ⟨hnat, hshift, hslot, hctx, hledger', hwidth⟩ := hc D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m hm hn hnM tA htA G G' hcascade hlevel hG hactual
  have htags := Providers.CascadeInvariants.hasTags_restrict hactual.2.2.2.2.1
    (G'.comps.filter (IsRetained m H J)) (Finset.filter_subset _ _)
  exact ⟨hnat, htags, hctx.isGenerated, hshift, hslot, hctx, hledger', fun v u γ => (hwidth v u γ).1⟩

/-- Uniform production of `StageEnvelopesClause` under the propagation prefix. -/
def SuccessorEnvelopesOfContextStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  StageProductionStatement α s q ζ StageEnvelopesClause

/-- Uniform production of `StageKernelAdmissibilityClause` under the propagation prefix. -/
def SuccessorKernelAdmissibilityStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  StageProductionStatement α s q ζ StageKernelAdmissibilityClause

/-- Uniform production of `StageKernelWidthsClause` under the propagation prefix. -/
def SuccessorKernelWidthBoundsStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  StageProductionStatement α s q ζ StageKernelWidthsClause

/-- Uniform production of `StageKernelRegularizersClause` under the propagation prefix. -/
def SuccessorKernelRegularizersStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  StageProductionStatement α s q ζ StageKernelRegularizersClause

/-- Uniform production of `StageKernelPriceClause` under the propagation prefix. -/
def SuccessorKernelPriceStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  StageProductionStatement α s q ζ StageKernelPriceClause

private theorem stage_template_compact {φ₀ : Vec 2 → ℝ}
    (h : Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall) :
    HasCompactSupport φ₀ := by
  let L := (Homogenization.HilbertVec.continuousLinearEquivVec 2).symm
  have heq : Analysis.Convolution.closedEuclideanUnitBall = L ⁻¹' Metric.closedBall 0 1 := by
    ext z
    simp only [Analysis.Convolution.closedEuclideanUnitBall, Set.mem_ofPred_eq, Set.mem_preimage,
      Metric.mem_closedBall, dist_zero_right, Analysis.Convolution.euclideanNorm]
    rfl
  have hc : IsCompact Analysis.Convolution.closedEuclideanUnitBall := by
    rw [heq]
    exact L.toHomeomorph.isCompact_preimage.2 (isCompact_closedBall 0 1)
  exact HasCompactSupport.of_support_subset_isCompact hc h

/-- The kernel regularizers supply every spatial order requested by the propagated invariant. -/
theorem successor_kernel_regularizers (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) : SuccessorKernelRegularizersStatement α s q ζ := by
  classical
  refine ⟨128, le_rfl, ?_⟩
  intro Λ hΛ
  refine ⟨1, zero_lt_one, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  obtain ⟨cf, _hcf, mf, hmf, hf⟩ := FullLift.uniform_cascade_kernel_regularizers φ₀
    (stage_template_compact hφsupport) hφsmooth hφ₀ nk.toPNat' α s q
    hα₀ hα₁ hs₀ hs₁ hq ζ hζ Λ hΛ
  let thr : InvConsts := { kS with cker := cf }
  refine ⟨thr, 1, 1, le_rfl, zero_lt_one, ?_⟩
  intro kI hkI
  have hKs : kI.Ks ≤ kS.Ks := hkI.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨0, 0, ?_⟩
  intro CI Cw j₀ hledger hstart
  refine ⟨mf + 1, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA htA G G' hcascade hlevel hG hactual
  obtain ⟨hseedlevel, _, _, _, _, _, _, hseedInv, _⟩ := hseed
  have hGrCascade : IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
      (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed (G'.retained m H J) := by
    simpa only [hlevel, succMenu] using IsCascadeStage.step hcascade hactual
  have hGrlevel : (G'.retained m H J).level = m - 1 := by
    change G'.level = m - 1
    rw [hactual.2.1, hlevel]
  have hbandD : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    simpa only [hDα, hDq, hDΛ, hDζ, hterm] using hband
  have hreg := hf hr D hDα hDq hDΛ hDζ hseq hbandD _ bw j₀
    (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
    (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) law seedK freshK kS
    kI.cr σ₀ (hkI.2.1.symm ▸ hcr) (by simpa only [hterm] using hfresh)
    Mnat seed (G'.retained m H J) tS tf _ _ (by omega) hseedInv hGrCascade
    (by rw [hGrlevel]; omega) kI.cker (fun j _ => invariant_admissible_kernel_bounds hkI j)
    (tA + 3 * ocTau α q Λ m) tf (by
      intro t ht
      refine ⟨htA.trans (le_trans ?_ ht.1), ht.2⟩
      exact le_add_of_nonneg_right (mul_nonneg (by norm_num)
        (Construction.Stream.ocTau_pos (by omega : 1 ≤ Λ)).le))
  intro v u γ ρ hρ kk hkk
  exact hreg v u γ ρ hρ kk (hkk.trans hKs)

/-- The two quantitative width budgets propagate through original-kernel provenance. -/
theorem successor_kernel_width_bounds (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) : SuccessorKernelWidthBoundsStatement α s q ζ := by
  classical
  obtain ⟨Λ₀, hΛ₀, hw⟩ := FullLift.band_interior_width_ratios hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ
  have h128 := hΛ₀.trans hΛ
  refine ⟨1, zero_lt_one, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  have hσ₀ : 0 < σ₀ := by
    obtain ⟨_, _, _, _, _, hsum, ha, has, _⟩ := hsched
    linarith only [hsum, ha, has]
  obtain ⟨C, hC, hw⟩ := hw Λ hΛ 1 σ₀ kS.c₀ kS.cr zero_lt_one hσ₀ hc₀ hcr
  let thr : InvConsts := { kS with Cwid := max C 1 }
  refine ⟨thr, 1, 1, le_rfl, zero_lt_one, ?_⟩
  intro kI hkI
  have hCwid : C ≤ kI.Cwid := (le_max_left _ _).trans hkI.2.2.2.2.2.1
  have hCwid0 : 0 ≤ kI.Cwid := hC.le.trans hCwid
  have hσf' : kI.σf ≤ ocDelta α q + σ₀ := hkI.2.2.2.2.2.2.1.trans_le (min_le_right _ _)
  have hσf0 : 0 ≤ kI.σf := by
    rw [hkI.2.2.2.2.2.2.1]
    exact (lt_min hσf (add_pos
      (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1 hσ₀)).le
  have hlam : kI.lamC ≤ (q - 1) * (1 + ocC α q) + q * σ₀ := hkI.2.2.2.2.2.2.2.2.2.1
  have hlam0 : 0 ≤ kI.lamC := hσ₀.le.trans hkI.2.2.2.2.2.2.2.1.le
  refine ⟨0, 0, ?_⟩
  intro CI Cw j₀ hledger hstart
  refine ⟨3, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA htA G G' hcascade hlevel hG hactual
  have hbandD : IsOCBandChain α q Λ ζ D.term D.κ := by simpa only [hterm] using hband
  have he : ∀ i, 0 < D.eps i ∧ D.eps i ≤ 1 := by
    intro i
    simpa only [OCData.eps, hDq, hDΛ] using
      ⟨(Scales.epsilon_basic (m := i) hq.1 h128).1,
        (Scales.epsilon_basic (m := i) hq.1 h128).2.1⟩
  have hρ := FullLift.radii_step_le hα₀ hα₁ hs₀ hs₁ hq hζ h128 D hDα hDq hDΛ hbandD
    kI.c₀ kI.cr (hkI.1.symm ▸ hc₀.le) (hkI.2.1.symm ▸ hcr.le) m (by omega) (by omega)
  have hrho0 : 0 ≤ rhoStar D kI.c₀ (m - 1) := mul_nonneg
    (hkI.1.symm ▸ hc₀.le) (le_min (he _).1.le (Real.sqrt_nonneg _))
  have hrhoe0 : 0 ≤ rhoEnh D kI.cr (m - 1) := mul_nonneg (hkI.2.1.symm ▸ hcr.le) (Real.sqrt_nonneg _)
  have hemono : D.eps m ≤ D.eps (m - 1) := by
    simpa only [OCData.eps, hDq, hDΛ] using EntryScales.epsilon_antitone hq.1 h128 (Nat.sub_le m 1)
  have hemono' : D.eps (m - 1) ≤ D.eps (m - 1 - 1) := by
    simpa only [OCData.eps, hDq, hDΛ] using EntryScales.epsilon_antitone hq.1 h128 (Nat.sub_le (m - 1) 1)
  obtain ⟨_, _, _, _, _, _, _, _, hkernels, _⟩ := id hG
  let P := succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p
  let lookup : KernelKey → KernelSpec := fun key => match key with
    | .seed i => seedK i
    | .fresh i => freshK i
  let Qk : KernelKey → Prop := fun key =>
    (lookup key).width ≤ kI.Cwid * rhoStar D kI.c₀ (m - 1) * D.eps (m - 1) ^ kI.σf ∧
    (lookup key).width ≤ kI.Cwid * rhoEnh D kI.cr (m - 1) * D.eps (m - 1 - 1) ^ kI.lamC
  have hold : ∀ v u (γ : G.fam.Γ v u), Qk ((G.prov v u γ).tags P).kernel := by
    intro v u γ
    obtain ⟨_, hmatch, hf, hc, _⟩ := hkernels v u γ
    simp only [hlevel] at hf hc
    change (G.kernelOf P seedK freshK v u γ).width ≤ _ ∧
      (G.kernelOf P seedK freshK v u γ).width ≤ _
    rw [hmatch]
    constructor
    · exact hf.trans (mul_le_mul
        (mul_le_mul_of_nonneg_left hρ.1 hCwid0)
        (Real.rpow_le_rpow (he _).1.le hemono hσf0)
        (Real.rpow_nonneg (he _).1.le _) (mul_nonneg hCwid0 hrho0))
    · exact hc.trans (mul_le_mul
        (mul_le_mul_of_nonneg_left hρ.2 hCwid0)
        (Real.rpow_le_rpow (he _).1.le hemono' hlam0)
        (Real.rpow_nonneg (he _).1.le _) (mul_nonneg hCwid0 hrhoe0))
  have hspec := hfresh (m - 1) (by omega) (by omega)
  have hratios := hw D.term D.κ hbandD m hm (by omega)
  have hrhof : 0 < rhoStar D kS.c₀ (m - 1) := by
    unfold rhoStar OCData.eps
    rw [hDα, hDq, hDΛ]
    exact mul_pos hc₀ (lt_min (Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ Λ))
      (Real.sqrt_pos.2 (div_pos
        (CycleReference.bandChain_pos (by omega : 1 ≤ Λ) hζ hbandD (by omega))
        (Real.rpow_pos_of_pos (Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ Λ)) _))))
  have hrhoc : 0 < rhoEnh D kS.cr (m - 1) := by
    unfold rhoEnh
    rw [hDα, hDq, hDΛ]
    exact mul_pos hcr (Real.sqrt_pos.2 (mul_pos
      (CycleReference.bandChain_pos (by omega : 1 ≤ Λ) hζ hbandD (by omega))
      (Construction.Stream.ocTauPP_pos (by omega : 1 ≤ Λ))))
  have hnewf : (freshK (m - 1)).width / rhoStar D kS.c₀ (m - 1) ≤
      C * D.eps (m - 1) ^ (ocDelta α q + σ₀) := by
    simpa only [hspec.1, freshWidth, freshLength, rhoStar, OCData.eps, hDα, hDq, hDΛ, hkI.2.1,
      show m - 1 + 1 = m by omega] using hratios.2.1
  have hnewc : (freshK (m - 1)).width / rhoEnh D kS.cr (m - 1) ≤
      C * D.eps (m - 1 - 1) ^ (q * (1 + ocC α q + σ₀) - 1 - ocC α q) := by
    simpa only [hspec.1, freshWidth, freshLength, rhoEnh, OCData.eps, hDα, hDq, hDΛ, hkI.2.1,
      show m - 1 + 1 = m by omega] using hratios.2.2.2
  have hnew : Qk (.fresh (G.level - 1)) := by
    dsimp only [Qk, lookup]
    rw [hlevel, hkI.1, hkI.2.1]
    constructor
    · have hpow := Real.rpow_le_rpow_of_exponent_ge (he (m - 1)).1 (he (m - 1)).2 hσf'
      have hbd := hnewf.trans (mul_le_mul hCwid hpow
        (Real.rpow_nonneg (he _).1.le _) hCwid0)
      exact (div_le_iff₀ hrhof).mp hbd |>.trans_eq (by ring)
    · have hexp : kI.lamC ≤ q * (1 + ocC α q + σ₀) - 1 - ocC α q := by
        calc kI.lamC ≤ (q - 1) * (1 + ocC α q) + q * σ₀ := hlam
          _ = _ := by ring
      have hpow := Real.rpow_le_rpow_of_exponent_ge (he (m - 1 - 1)).1 (he (m - 1 - 1)).2 hexp
      have hbd := hnewc.trans (mul_le_mul hCwid hpow
        (Real.rpow_nonneg (he _).1.le _) hCwid0)
      exact (div_le_iff₀ hrhoc).mp hbd |>.trans_eq (by ring)
  have hall := FullLift.actual_successor_kernel_key_property P _ G G' hactual Qk hold hnew
  have hmatch := (FullLift.retained_structural_certificates P _ seedK freshK G G' hG.2.1
    (fun v u γ => (hkernels v u γ).2.1)
    (by simpa only [P, succProvParams, hlevel] using hspec.1) hactual m H J).2
  have hGrlevel : (G'.retained m H J).level = m - 1 := by
    change G'.level = m - 1
    rw [hactual.2.1, hlevel]
  intro v u γ
  have h := hall ⟨v.1, Finset.mem_of_mem_filter _ v.2⟩ ⟨u.1, Finset.mem_of_mem_filter _ u.2⟩ γ
  change (G'.kernelOf P seedK freshK _ _ γ).width ≤ _ ∧
    (G'.kernelOf P seedK freshK _ _ γ).width ≤ _ at h
  have heq := hmatch v u γ
  have hfinal := And.intro (heq.symm.trans_le h.1) (heq.symm.trans_le h.2)
  simpa only [hGrlevel] using hfinal

/-- Fresh bounded axes and the inherited kernel key prove all admissibility clauses. -/
theorem successor_kernel_admissibility (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) : SuccessorKernelAdmissibilityStatement α s q ζ := by
  classical
  obtain ⟨Λ₀, hΛ₀, haxes⟩ := FullLift.uniform_fresh_axes_norm_bound α s q hα₀ hα₁ hs₀ hs₁ hq ζ hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ
  have h128 := hΛ₀.trans hΛ
  obtain ⟨Γ, _hΓ, ma, hma, haxes⟩ := haxes Λ hΛ
  obtain ⟨mi, _hmi, hinv⟩ := FullLift.uniform_fresh_spanning_inverse_bound α s q hα₀ hα₁ hs₀ hs₁ hq ζ hζ Λ h128
  refine ⟨1, zero_lt_one, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  let thr : InvConsts := { kS with Γk := max Γ 2 }
  refine ⟨thr, 1, 1, le_rfl, zero_lt_one, ?_⟩
  intro kI hkI
  have hΓ : Γ ≤ kI.Γk := (le_max_left _ _).trans hkI.2.2.2.1
  have htwo : 2 ≤ kI.Γk := (le_max_right _ _).trans hkI.2.2.2.1
  have hnk : 1 ≤ nk := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hn⟩ := hsched
    exact hn
  have horder : kI.Lker + 1 ≤ 2 * nk := hkI.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨0, 0, ?_⟩
  intro CI Cw j₀ hledger hstart
  refine ⟨max ma mi, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA htA G G' hcascade hlevel hG hactual
  have hm2 : 2 ≤ m := by omega
  have hbandD : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    simpa only [hDα, hDq, hDΛ, hDζ, hterm] using hband
  have hspec := hfresh (m - 1) (by omega) (by omega)
  have hupper := haxes D hDα hDq hDΛ hDζ hseq hbandD (m - 1) (by omega) (by omega) (freshK (m - 1)) hspec.2.2
  have hinverse := hinv D hDα hDq hDΛ hDζ hseq hbandD (m - 1) (by omega) (by omega) (freshK (m - 1)) hspec.2.2
  have hmeas := FullLift.fresh_axes_measurable D (m - 1) (by rw [hDΛ]; omega)
    (freshK (m - 1)).H₁ (freshK (m - 1)).H₂ hspec.2.2
  have hnew : (freshK (m - 1)).IsAdmissible kI.Γk kI.Lker := by
    refine ⟨hmeas.1, hmeas.2, ?_, ?_⟩
    · intro t
      exact ⟨(hupper t).1.trans hΓ, (hupper t).2.trans hΓ,
        (hinverse t).1, (hinverse t).2.trans htwo⟩
    · rw [hspec.2.1]
      have hval : (nk.toPNat' : ℕ) = nk := by
        change nk - 1 + 1 = nk
        omega
      simpa only [hval] using horder
  let lookup : KernelKey → KernelSpec := fun key => match key with
    | .seed i => seedK i
    | .fresh i => freshK i
  have hall := FullLift.actual_successor_kernel_key_property _ _ G G' hactual
    (fun key => (lookup key).IsAdmissible kI.Γk kI.Lker)
    (fun v u γ => (hG.2.2.2.2.2.2.2.2.1 v u γ).1)
    (by simpa only [hlevel, lookup] using hnew)
  intro v u γ
  exact hall ⟨v.1, Finset.mem_of_mem_filter _ v.2⟩ ⟨u.1, Finset.mem_of_mem_filter _ u.2⟩ γ

/-- The actual successor's quiet atlas and carried history, using the shared producer.
The full successor is certified once before restriction. Carrier constants are enlarged
before the stage data, and the history comes from the PARENT's last invariant conjunct.
Empty or singleton restrictions, zero data and seed parents with no edges use exactly the
same shared lemmas. -/
theorem successor_quiet_and_history (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    StageProductionStatement α s q ζ
      (fun law P seedK freshK φ₀ hφ₀ M k a b S θ G =>
        StageQuietMatchingClause law P seedK freshK φ₀ hφ₀ M k a b S θ G ∧
        StageHistoryClause law P seedK freshK φ₀ hφ₀ M k a b S θ G) := by
  classical
  obtain ⟨Λ₀, hΛ₀, hc⟩ := Frontier.extended_successor_context_certified
    α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ
  obtain ⟨cmax, hcmax, hc⟩ := hc Λ hΛ
  refine ⟨cmax, hcmax, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  obtain ⟨thr, CH, Υ, hCH, hΥ, hc⟩ := hc φ₀ hφ₀ hφsmooth hφpos hφint hφsupport
    bw hbw hbwupper Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched hNaux hNout halloc hsX hsZ
  refine ⟨thr, CH, max Υ 1, hCH, zero_lt_one.trans_le (le_max_right _ _), ?_⟩
  intro kI hkI
  obtain ⟨CIthr, Cwthr, hc⟩ := hc kI hkI
  refine ⟨CIthr, Cwthr, ?_⟩
  intro CI Cw j₀ hledger hstart
  have hA : ∀ i, 0 ≤ ocA α q Λ i := fun _ => (Real.rpow_pos_of_pos
    (Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ Λ)) _).le
  have hT : ∀ i, 0 ≤ ocTauPP α q Λ i := fun _ =>
    (Construction.Stream.ocTauPP_pos (by omega)).le
  have hstart₀ := IsCarrierStart.mono hA hT le_rfl (le_max_left Υ 1)
    (zero_le_one.trans hCH) hΥ.le hstart
  obtain ⟨m₀, hc⟩ := hc CI Cw j₀ hledger hstart₀
  refine ⟨max m₀ (j₀ + 3), ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA htA G G' hcascade hlevel hG hactual
  obtain ⟨hslot, _hctx⟩ := hc D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m (by omega) hn hnM G G' hcascade hlevel
    ⟨tA, htA, hG⟩ hactual
  obtain ⟨_hnat, _htags, hgen, _hshift, _hslot, _hctx, _henv, _hledger, _hker,
    _hprice, _hatlas, _htrans, _hfast, hhistory⟩ := hG
  have hΛD : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have hζD : IsFastProfile D.ζ := hDζ.symm ▸ hζ
  have hbandD : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    simpa only [hDα, hDq, hDΛ, hDζ, hterm] using hband
  have hstartD : IsCarrierStart D.α D.q D.Λ bw CH (max Υ 1) j₀ := by
    simpa only [hDα, hDq, hDΛ] using hstart
  have hc2 := EntryWeakProofs.weakData_cellScaleSq_pos D hΛD hζD hbandD G.level
  have hi : 1 ≤ G'.level := by rw [hactual.2.1, hlevel]; omega
  have hj : j₀ ≤ G'.level := by rw [hactual.2.1, hlevel]; omega
  have hlt : G'.level < Mnat := by rw [hactual.2.1, hlevel]; omega
  have hN : 1 ≤ N := by
    have hN := hsched.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    omega
  have hρ : (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)).lenFactor *
      liftLength D G.level ≠ 0 := by
    change 1 * Real.sqrt (D.κ (G.level - 1) * ocTauPP D.α D.q D.Λ G.level) ≠ 0
    rw [one_mul]
    exact (Real.sqrt_pos.mpr (mul_pos
      (CycleReference.bandChain_pos hΛD hζD hbandD (by rw [hlevel, hterm]; omega))
      (Construction.Stream.ocTauPP_pos hΛD))).ne'
  obtain ⟨_hG, _hG', _hcomps, hnat', _htags', _hexports, ⟨w⟩⟩ :=
    (Providers.QuietAtlas.isActualSuccessor_iff_nonempty_witness _ _ G G').mp hactual
  have hS := Providers.QuietAtlas.isHistoryQuiet_ocTrimmedQuiet hΛD hCH hstartD Mnat G'.level hj
  have hquiet := Providers.QuietAtlas.successorQuietMatching_of_generated
    (W := Set.Icc (tA + 3 * ocTau α q Λ m) tf) hactual.1 hactual.2.1
    hζD hΛD hbw hc2 hN (by dsimp only [succMenu]; omega)
    (by dsimp only [succMenu]; omega) hρ hi hj hCH hstartD w hgen hnat' hS hhistory hslot
  have hretquiet := EntryTerminal.Ingredients.quietMatchingOn_retained G' m H J _
    (Set.Icc (tA + 3 * ocTau α q Λ m) tf) hquiet
  have hhist := Providers.QuietAtlas.successor_stageHistoryInvariant_of_carrier hΛD hζD hbw
    hCH (le_max_right Υ 1) hstartD hc2 hactual hgen hlt hhistory
  exact ⟨hretquiet, EntryTerminal.Ingredients.stageHistoryInvariant_retained G' m H J hhist⟩

theorem stage_invariant_propagation_of_ingredients (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (henv : SuccessorEnvelopesOfContextStatement α s q ζ)
    (hprice : SuccessorKernelPriceStatement α s q ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ →
    ∀ (Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ : ℕ), 1 ≤ Ce → 0 < τe →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → 0 < kS.σf → 0 < kS.lamC →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min kS.σf (ocDelta α q + σ₀)) kS.lamC D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sX →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sZ →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∃ mStar : ℕ,
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
      [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
      (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ tA : ℝ, tS ≤ tA →
    ∀ (G G' : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI (tA + 3 * ocTau α q Λ m) tf (CI * D.eps (m - 1) ^ min (ocDelta α q / 4) τe)
        (CI * D.eps ((m - 1) - 1) ^ (q * min (ocDelta α q / 4) τe)) (G'.retained m H J) := by
  have hquiet := successor_quiet_and_history α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  have hadm := successor_kernel_admissibility α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  have hwidth := successor_kernel_width_bounds α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  have hreg := successor_kernel_regularizers α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  have hbase := stage_base_of_certificates (retained_stage_certificates α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)
  have hall := stage_production_and hbase (stage_production_and henv
    (stage_production_and hadm (stage_production_and hwidth
      (stage_production_and hreg (stage_production_and hprice hquiet)))))
  classical
  obtain ⟨Λ₀, hΛ₀, hall⟩ := hall
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ
  obtain ⟨cmax, hcmax, hall⟩ := hall Λ hΛ
  refine ⟨cmax, hcmax, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  obtain ⟨thr, CH, Υ, hCH, hΥ, hall⟩ := hall φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  refine ⟨thr, CH, Υ, hCH, hΥ, ?_⟩
  intro kI hkI
  obtain ⟨CIthr, Cwthr, hall⟩ := hall kI hkI
  refine ⟨CIthr, Cwthr, ?_⟩
  intro CI Cw j₀ hledger hstart
  obtain ⟨mStar, hall⟩ := hall CI Cw j₀ hledger hstart
  refine ⟨mStar, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA htA G G' hcascade hlevel hG hactual
  obtain ⟨hb, he, ha, hw, hr, hp, hq, hh⟩ := hall D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m hm hn hnM tA htA G G' hcascade hlevel hG hactual
  refine ⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2.1,
    hb.2.2.2.2.2.1, he, hb.2.2.2.2.2.2.1, ?_, hp, hq.1, hq.2.1, hq.2.2, hh⟩
  intro v u γ
  exact ⟨ha v u γ, hb.2.2.2.2.2.2.2 v u γ, (hw v u γ).1, (hw v u γ).2, hr v u γ⟩

end AVRegularity.Construction.Preservation.Assembly
