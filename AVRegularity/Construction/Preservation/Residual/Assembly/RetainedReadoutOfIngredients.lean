-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Assembly.SuccessorResidualIdentitiesOfIngredients
public import AVRegularity.Construction.Preservation.Residual.WeakFluxTesting
import AVRegularity.Construction.Stream.NextAdmissible

/-! The retained readout equation split into the kernel weak-system readout and the exact
source cancellation after testing. The assembly preserves the uniform choices.
Both named analytic ingredients remain open; no quiet-atlas identity is consumed. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.Assembly
namespace AVRegularity.Construction.Preservation.Residual

/-- Fixed residual data with the raw kernel readout, tested cancellation, and target equation. -/
def RetainedReadoutBridgeDataStatement (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw Ce τe : ℝ) (kS : InvConsts)
    (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (mStar : ℕ)
    (join : Prop → Prop → Prop → Prop) : Prop :=
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
    ∀ (tA s₀ : ℝ), tS ≤ tA → tA + 3 * ocTau α q Λ m ≤ s₀ → s₀ + 4 * ocTauPP α q Λ m ≤ tf →
      tf - s₀ ≤ T₀ →
    ∀ (G G' : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
    ∀ (tp : ℝ) (Preg : (∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn G.comps, TorusHk Nout (hr v.1.root))),
      IsCommonPreparation law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        G kI.cr Q CQ Cpr p Nout Naux s₀ tf tp Preg →
    ∀ (f : ∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) (Ain : ℝ),
      weightedNorm 1 (G.mass law) (G.marker law) f ≤ Ain →
    ∀ (Y0 : ∀ v' : CompIn (G'.retained m H J).comps, TorusHk Naux (hr v'.1.root))
      (Y : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk Naux (hr v.1.root))
      (Yw : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk (Naux + 1) (hr v.1.root))
      (Yk : ∀ v u (_ : (G'.retained m H J).fam.Γ v u), ℝ → TorusHk (Naux + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root)),
      IsRetainedTrace G (G'.retained m H J) m p tp (Preg f) Y0 →
      (G'.retained m H J).IsRegSolution (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        seedK freshK φ₀ hφ₀ (D.κ (m - 1)) (streamVel (D.Φ (m - 1))) Naux tp tf Y0
        (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
      (PZ : ∀ v : CompIn G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
      (û : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (hr v.1.root)),
      IsLiftedField G (G'.retained m H J) m p Naux N (succSchedR r₀ J H) sX sZ (succEta0 α q s) tp tf Y CcT PZ aRep û →
    ∀ (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
      (aY : ℝ → Vec 2 → ∀ v : CompIn (G'.retained m H J).comps, hr v.1.root),
      (∀ v, ∀ t ∈ Set.Icc tp tf, IsClassicalRep
        (succReadout m (D.eps (m - 1)) (succEta0 α q s) Naux (fun v' => Y v' t) v) (fun x => aZ t x v) Naux) →
      (∀ v', ∀ t ∈ Set.Icc tp tf, IsClassicalRep (Y v' t) (fun x => aY t x v') Naux) →
    join
      (    ∀ v : CompIn G.comps, ∀ t ∈ Set.Icc tp tf, ∀ φ : Vec 2 → hr v.1.root,
      ContDiff ℝ (⊤ : ℕ∞) φ → IsZ2Periodic φ →
      CoupledWeakIdentity (volume.restrict AVenhance.unitCube) (D.κ (m - 1)) tp t
          (streamVel (D.Φ (m - 1))) (fun x => aZ t x v) (fun x => aZ tp x v) φ
          (fun j x => gradE φ x j) (fun s' j x => gradE (fun y => aZ s' y v) x j)
          (fun _ _ => 0)
          (readoutFlux m (D.eps (m - 1)) (succEta0 α q s) (fun _ => True)
            (fun v' s' x => coeffFluxOn (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
              (G'.retained m H J) .kernel aY v' s' x) v)
          (fun _ _ => 0))
      (∀ v : CompIn G.comps, ∀ t ∈ Set.Icc tp tf, ∀ φ : Vec 2 → hr v.1.root,
        ContDiff ℝ (⊤ : ℕ∞) φ → IsZ2Periodic φ →
        TestedFluxAgreement (volume.restrict AVenhance.unitCube) (Set.Ioc tp t)
          (readoutFlux m (D.eps (m - 1)) (succEta0 α q s) (fun _ => True)
            (fun v' s' x => coeffFluxOn (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
              (G'.retained m H J) .kernel aY v' s' x) v)
          (fun s' x => -(toFluxL (covPolyQ (covPrimitive D m s') p
              (fun y => gFlux G m N p (succSchedR r₀ J H) CcT aZ v s' y) x) +
            upsilonFlux (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ G G' (G'.retained m H J)
              m H J (D.eps (m - 1)) (succEta0 α q s) aZ aY v s' x))
          (fun j x => gradE φ x j))
      (    ∀ v : CompIn G.comps, ∀ t ∈ Set.Icc tp tf, ∀ φ : Vec 2 → hr v.1.root,
      ContDiff ℝ (⊤ : ℕ∞) φ → IsZ2Periodic φ →
      CoupledWeakIdentity (volume.restrict AVenhance.unitCube) (D.κ (m - 1)) tp t
          (streamVel (D.Φ (m - 1))) (fun x => aZ t x v) (fun x => aZ tp x v) φ
          (fun j x => gradE φ x j) (fun s' j x => gradE (fun y => aZ s' y v) x j)
          (fun _ _ => 0)
          (fun s' x => -(toFluxL (covPolyQ (covPrimitive D m s') p
              (fun y => gFlux G m N p (succSchedR r₀ J H) CcT aZ v s' y) x) +
            upsilonFlux (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ G G' (G'.retained m H J) m H J (D.eps (m - 1)) (succEta0 α q s) aZ aY v s' x))
          (fun _ _ => 0))

def RetainedReadoutBridgeProductionStatement (α s q : ℝ) (ζ : ℝ → ℝ)
    (join : Prop → Prop → Prop → Prop) : Prop :=
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
    ∀ CQ Cpr : ℝ, ∃ mStar : ℕ,
    RetainedReadoutBridgeDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ mStar join

/-- The finite parent-word sum of the retained kernel weak system, on chosen classical reps.
A singleton family retains its diagonal coefficient;
seed exports remain in the kernel sum; the schedule supplies the smallest derivative reserve. -/
def RetainedReadoutKernelEquationStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  RetainedReadoutBridgeProductionStatement α s q ζ (fun raw _cancel _readout => raw)

/-- Weighted source and word cancellation, with kernel defects and omitted rows, as tested fluxes.
Empty row sums vanish, and one component still includes the fresh diagonal source;
old seed kernels are not removed; minimum scheduled orders cover every applied derivative.
Equality is only after testing, so no divergence-free gauge is fixed. -/
def RetainedReadoutFluxCancellationStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  RetainedReadoutBridgeProductionStatement α s q ζ (fun _raw cancel _readout => cancel)

/-- At fixed uniform choices the two analytic statements give the desired readout equation. -/
theorem retained_readout_bridge_data_conclude
    (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw Ce τe : ℝ) (kS : InvConsts)
    (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (ma mb : ℕ)
    (ha : RetainedReadoutBridgeDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ ma (fun a _b _c => a))
    (hb : RetainedReadoutBridgeDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ mb (fun _a b _c => b)) :
    ResidualDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ (max ma mb) (fun a _b _c => a) := by
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA s₀ htA hs₀ htf hT₀ G G' hcascade hlevel hG hactual
    tp Preg hprep f Ain hAin Y0 Y Yw Yk htrace hsol CcT PZ aRep û hlift aZ aY hZ hY
  have hraw := ha D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m (by omega) hn hnM tA s₀ htA hs₀ htf hT₀ G G' hcascade hlevel hG hactual
    tp Preg hprep f Ain hAin Y0 Y Yw Yk htrace hsol CcT PZ aRep û hlift aZ aY hZ hY
  have hcancel := hb D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m (by omega) hn hnM tA s₀ htA hs₀ htf hT₀ G G' hcascade hlevel hG hactual
    tp Preg hprep f Ain hAin Y0 Y Yw Yk htrace hsol CcT PZ aRep û hlift aZ aY hZ hY
  intro v t ht φ hφ hp
  apply weakIdentity_of_tested_flux_agreement _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ (hraw v t ht φ hφ hp)
  simpa only [zero_add, add_zero] using hcancel v t ht φ hφ hp

/-- Common choices of thresholds and carrier constants preserve both ingredient prefixes. -/
theorem retained_readout_weak_equation_of_ingredients {α s q : ℝ} {ζ : ℝ → ℝ}
    (hread : RetainedReadoutKernelEquationStatement α s q ζ)
    (hcov : RetainedReadoutFluxCancellationStatement α s q ζ) :
    RetainedReadoutWeakEquationStatement α s q ζ := by
  classical
  obtain ⟨Λa, hΛa, ha⟩ := hread
  obtain ⟨Λb, hΛb, hb⟩ := hcov
  refine ⟨max Λa Λb, by omega, ?_⟩
  intro Λ hΛ
  obtain ⟨ca, hca, ha⟩ := ha Λ (by omega)
  obtain ⟨cb, hcb, hb⟩ := hb Λ (by omega)
  refine ⟨min ca cb, lt_min hca hcb, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hfloorX hfloorZ
  obtain ⟨ta, CHa, Υa, hCHa, hΥa, ha⟩ := ha φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ (hc₀upper.trans (min_le_left _ _)) hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hfloorX hfloorZ
  obtain ⟨tb, CHb, Υb, hCHb, hΥb, hb⟩ := hb φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ (hc₀upper.trans (min_le_right _ _)) hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hfloorX hfloorZ
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
  intro CQ Cpr
  obtain ⟨ma, ha⟩ := ha CI Cw j₀ hLa (IsCarrierStart.mono hA hT
    (le_max_left _ _) (le_max_left _ _) (zero_le_one.trans hCHa) hΥa.le hstart) CQ Cpr
  obtain ⟨mb, hb⟩ := hb CI Cw j₀ hLb (IsCarrierStart.mono hA hT
    (le_max_right _ _) (le_max_right _ _) (zero_le_one.trans hCHb) hΥb.le hstart) CQ Cpr
  refine ⟨max ma mb, ?_⟩
  exact retained_readout_bridge_data_conclude α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ ma mb ha hb

end AVRegularity.Construction.Preservation.Residual
