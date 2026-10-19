-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Assembly.SuccessorResidualIdentitiesOfIngredients
import AVRegularity.Construction.Preservation.Assembly.FullLiftFromInputs
import AVRegularity.Construction.Preservation.FullLift.IncomingLedgerBudget
import AVRegularity.Construction.Preservation.Assembly.PreparationJointOfInputs

/-! Exact full-lift statement from the retained stage certificates. Geometry, higher values,
and the readout budget are discharged by the existing uniform analytic lemmas. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.FullLift

private theorem full_lift_assembly_core (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (hproduction : RetainedProductionBundleStatement α s q ζ) :
    SuccessorFullLiftBoundStatement α s q ζ := by
  classical
  obtain ⟨Λa, hΛa, hanalytic⟩ := uniform_full_lift_clauses_of_inputs hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Λ₀, hΛ₀, hbase, hprod⟩ := hproduction Λa hΛa
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ
  obtain ⟨c₀max, hc₀max, hp⟩ := hprod Λ hΛ
  refine ⟨c₀max, hc₀max, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  obtain ⟨thr, CH, Υ, hCH, hΥ, hp⟩ := hp φ₀ hφ₀ hφsmooth hφpos hφint hφsupport
    bw hbw hbwupper Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper
    hσf hlamC H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  refine ⟨thr, CH, Υ, hCH, hΥ, ?_⟩
  intro kI hkI
  obtain ⟨CIthr, Cwthr, hp⟩ := hp kI hkI
  refine ⟨CIthr, Cwthr, ?_⟩
  intro CI Cw j₀ hledger hstart k hk CQ Cpr
  have hcrI : kI.cr = kS.cr := hkI.2.1
  have hcrpos : 0 < kI.cr := hcrI.symm ▸ hcr
  have hcrle : kI.cr ≤ 1 := hcrI.symm ▸ hcrupper
  have hDm : 2 ≤ succSchedD D₀ N p (H + 1) := by
    change 2 ≤ succSchedD D₀ N p H + 2 * N + 4 * p + 4
    omega
  have hN : 1 ≤ N := by
    have hh : 2 ≤ N := hsched.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    omega
  have hCI : 0 ≤ CI := (by linarith : 0 ≤ Ce).trans hledger.1
  obtain ⟨Cenergy, ma, hCenergy, hma, ha⟩ := hanalytic Λ (by omega) bw hbw
    (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H) N k sX sZ p hDm hN
    CI kI.cr hCI hcrpos hcrle
  obtain ⟨Cread, mStar, hCread, hp⟩ := hp CI Cw j₀ hledger hstart k hk CQ Cpr ma ma hma hma
  refine ⟨max Cenergy Cread, mStar, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA s₀ htA hdelay hwindow hT G G' hcascade hlevel hG hactual tp Preg hprep f Ain hf
    Y0 Y Yw Yk htrace hsol
  obtain ⟨hgeom, hhigher, hread⟩ := hp D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat
    law hlaw seedK freshK hfresh seed n tS tf hseed m hm hn hnM tA s₀ htA hdelay hwindow hT
    G G' hcascade hlevel hG hactual tp Preg hprep f Ain hf Y0 Y Yw Yk htrace hsol
  obtain ⟨hge, hgu, htermG, hj, hdepth, hreserve, hreserve2, hlength, hrs, hrse⟩ := hgeom
  obtain ⟨Yhi, hYhi⟩ := hhigher
  have hbandD : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    simpa only [hDα, hDq, hDΛ, hDζ, hterm] using hband
  have hYw := hsol.2.1
  have hcompat := hsol.2.2.1
  have hSbound : CI * D.eps m ^ min (ocDelta α q / 4) τe ≤ CI := by
    have hqD : IsAdmissibleQ D.α s D.q := by simpa only [hDα, hDq] using hq
    simpa only [hDα, hDq] using incoming_ledger_budget_le D (hDα.symm ▸ hα₀) hqD
      (by rw [hDΛ]; omega) hCI hτe.le m
  have hread' : RetainedReadoutBudgetStatement law G (G'.retained m H J) G.level p Naux N k hk
      (succEta0 α q s) kI.cr tp tf Cread Ain Y Yw := by
    simpa only [hlevel] using hread
  have hb := ha hr D hDα hDq hDΛ hDζ hseq hbandD j₀ G law _ seedK freshK φ₀ hφ₀
    Mnat kI tA tf _ _ hG hSbound hge htermG hj hdepth hreserve hreserve2 hlength
    (G'.retained m H J) Naux hk (succEta0 α q s) tp tf Y Yhi hYhi Yw hYw hcompat hrs hrse
    Cread Ain ((Real.sqrt_nonneg _).trans hf) hread'
  simpa only [hlevel] using hb


theorem successor_full_lift_bound_of_ingredients (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (hcertificates : RetainedStageCertificatesStatement α s q ζ) :
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
    ∀ k : ℕ, ∀ hk : k + N + 2 * p ≤ Naux,
    ∀ CQ Cpr : ℝ, ∃ (Ck : ℝ) (mStar : ℕ),
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
    FullLiftClauses law G (G'.retained m H J) m p Naux N (succSchedR r₀ J H) sX sZ k hk (succEta0 α q s) kI.c₀ kI.cr tp tf Ck Ain Y Yw := by
  exact full_lift_assembly_core α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
    (retained_production_bundle_of_certificates hα₀ hα₁ hs₀ hs₁ hq hζ hcertificates)

end AVRegularity.Construction.Preservation.Assembly
