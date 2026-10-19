-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Residual.Presentation.Cascade.CtxBridges
public import AVRegularity.Construction.Residual.Presentation.Cascade.InnerOrderFacts
import AVRegularity.Construction.Residual.Presentation.Cascade.CtxFineTail
import AVRegularity.Construction.Preservation.BillScale.Producer

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The bill residual from its inputs** (cascade side of the bill residual, the last assembly).

`successorBillResidual_of_native`: `SuccessorBillResidualStatement α s q ζ` (the residual
half of the `successor_bill`) from

* the input statement `NativeTemporalRepresentativesStatement` of the covariance leaf (through
  `succPrefix_nativeFacts_of_native`: the coarse equation of `P_pZ`, the joint measurability and
  the regularity of the lifted field at every context);
* the four flux and reconstruction pieces proved elsewhere, in their context forms:
  The covariance G form (`CovGCtxAt`), the frontier inner flux (`FrontierInnerPrefixStatement`), the filter defect
  (`FilterDefectCtxAt`), the reconstruction letters (`ReconLettersCtxAt`) and the reconstruction defect
  (`ReconDefectConvCtxAt`).

The temporal product rule is `temporal_product`, whose cell-scale hypothesis is the clause
`clock_nonzero` of the native regularity; `successorBillResidual_of_facts` is the common
proof, from the native facts at every context (`NativeFactsCtxAt`).

Everything else is proved: the bounds of the residual at every context
(`succPrefix_residualBound`), the comparison clauses from them (`succPrefix_comparison`), the
existence of a lifted field (the full-lift clauses at the order `0`, `succPrefix_fullLift`) and
the classical representatives of the readout and of the retained solution
(`retained_high_and_reps` from the retained production bundle). The constants are
`(C', c_g, m_*)` with `C' = CmpConst p C_Q C`, `C` the constant of the residual bound and
`c_g > 0` the gluing rate of the reconstruction.

The degenerate cases `A_in = 0`, `t_p = t_f` and an empty component family are allowed. -/

/-- **The bill residual from the native facts at every context and the flux and reconstruction pieces.** -/
theorem successorBillResidual_of_facts (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (hNF : SuccPrefix α s q (X := ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk _Lc _Lf _Lpr _Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        NativeFactsCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀
          kI CI Cw j₀ CQ Cpr Q T₀ x))
    (hG : SuccPrefix α s q (X := ℝ × ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk _Lc _Lf _Lpr Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        CovGCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI
          CI Cw j₀ CQ Cpr Q T₀ Acl x.1 x.2))
    (hB : FrontierInnerPrefixStatement α s q ζ)
    (hF : SuccPrefix α s q (X := ℝ × ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc _Lf _Lpr Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        FilterDefectCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI
          CI Cw j₀ CQ Cpr Q T₀ Acl Lc x.1 x.2))
    (hL : SuccPrefix α s q (X := ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk _Lc _Lf _Lpr Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        ReconLettersCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI
          CI Cw j₀ CQ Cpr Q T₀ Acl x))
    (hD : SuccPrefix α s q (X := ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc _Lf _Lpr Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        ReconDefectConvCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ
          σ₀ kI CI Cw j₀ CQ Cpr Q T₀ Acl Lc x)) :
    SuccessorBillResidualStatement α s q ζ := by
  apply successorBillResidual_of_prefix
  have h1 := succPrefix_residualBound α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ hG hB hF
    (succPrefix_reconCoarse_of_parts hL hD)
  have h2 := succPrefix_comparison α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  have h3 := hNF
  have h4 := succPrefix_fullLift α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => 0)
  have h5 := succPrefix_retainedProductionBundle α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => 0)
  refine ((((h1.and h2).and h3).and h4).and h5).imp ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ CQ Cpr hfacts x hx
  obtain ⟨⟨⟨⟨xRB, xK6⟩, xNF⟩, xFL⟩, xRP⟩ := x
  obtain ⟨Cres, cg, mRB⟩ := xRB
  obtain ⟨⟨⟨⟨⟨hcg, hRB⟩, hK6⟩, hNF⟩, hFL⟩, -, hRP⟩ := hx
  have hk15 := hfacts.sched.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hk0 : 0 + N + 2 * p ≤ Naux := by
    have := (le_max_right _ _).trans hk15
    omega
  refine ⟨(CmpConst p CQ Cres, cg, max (max mRB xK6) (max xNF (max xFL.2 xRP.2))), hcg, ?_⟩
  apply successorBillResidualData_of_ctx
  intro hr _ _ _ _ _ _ _ c hm hquietMargin
  replace hm : max (max mRB xK6) (max xNF (max xFL.2 xRP.2)) ≤ c.m := hm
  have hm1 : mRB ≤ c.m := by omega
  have hm2 : xK6 ≤ c.m := by omega
  have hm3 : xNF ≤ c.m := by omega
  have hm4 : xFL.2 ≤ c.m := by omega
  have hm5 : xRP.2 ≤ c.m := by omega
  refine ⟨?_, ?_⟩
  · obtain ⟨CcT, PZ, aRep, û, ŵ, hW⟩ := (hFL hk0 c hm4).1
    exact ⟨CcT, PZ, aRep, û, hW.1⟩
  · intro U Uw Uk hU CcT PZ aRep û hlift
    obtain ⟨-, hhigh, -⟩ := hRP hk0 c hm5
    obtain ⟨Yhi, -, aZ, aY, hZ, hY⟩ := retained_high_and_reps c.G (c.G'.retained c.m H J)
      c.m Naux (succEta0 α q s) c.tp c.tf c.Y hhigh
    obtain ⟨hmacro, hmeas, hreg⟩ := hNF c hm3 CcT PZ aRep û hlift aZ aY hZ hY
    exact hK6 c hm2 hquietMargin CcT PZ aRep û hlift aZ aY hZ hY hreg cg Cres
      (hRB c hm1 hquietMargin CcT PZ aRep û hlift aZ aY hZ hY hmacro hmeas) U Uw Uk hU

/-- **The bill residual from the native representatives and the flux and reconstruction pieces** (the
temporal product rule is `temporal_product`, with the cell-scale clause of the native regularity). -/
theorem successorBillResidual_of_native (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (hNat : NativeTemporalRepresentativesStatement)
    (hG : SuccPrefix α s q (X := ℝ × ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk _Lc _Lf _Lpr Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        CovGCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI
          CI Cw j₀ CQ Cpr Q T₀ Acl x.1 x.2))
    (hB : FrontierInnerPrefixStatement α s q ζ)
    (hF : SuccPrefix α s q (X := ℝ × ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc _Lf _Lpr Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        FilterDefectCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI
          CI Cw j₀ CQ Cpr Q T₀ Acl Lc x.1 x.2))
    (hL : SuccPrefix α s q (X := ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk _Lc _Lf _Lpr Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        ReconLettersCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI
          CI Cw j₀ CQ Cpr Q T₀ Acl x))
    (hD : SuccPrefix α s q (X := ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc _Lf _Lpr Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        ReconDefectConvCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ
          σ₀ kI CI Cw j₀ CQ Cpr Q T₀ Acl Lc x)) :
    SuccessorBillResidualStatement α s q ζ :=
  successorBillResidual_of_facts α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
    (succPrefix_nativeFacts_of_native α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ hNat) hG hB hF hL hD

/-! **The successor bill conditional on one remaining input** (cascade side of the bill
residual).

The one remaining input is the `NativeTemporalRepresentativesStatement` (the native time
representatives of the covariance leaf). Everything else is connected:

* the covariance G form: `succPrefix_covGForm` (with parts 1 and 2), `succPrefix_covGCtx`;
* the frontier inner flux: `succPrefix_frontierInner`;
* the filter defect: `succPrefix_w31FilterForm`, `succPrefix_filterDefectCtx`;
* the reconstruction letters: `frameReconLetters`, `succPrefix_reconLettersCtx`;
* the reconstruction defect: `frameReconDefectConvAt`, `succPrefix_reconDefectConvCtx`;
* the temporal product rule `temporal_product`, with the cell-scale clause of the native regularity
  (`successorBillResidual_of_native`).

* `successorBillResidual_of_open`: `SuccessorBillResidualStatement α s q ζ` from
  `NativeTemporalRepresentativesStatement`.
* `successor_bill_of_open`: the text of the `successor_bill`
  from the same input, by `successor_bill_of_ingredients` with the proved scale half
  `successor_bill_scale`. It is this theorem applied to `successorBillResidual_of_open`.
 -/

/-- **The bill residual from the one remaining input.** -/
theorem successorBillResidual_of_open (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (hNat : NativeTemporalRepresentativesStatement)
 :
    SuccessorBillResidualStatement α s q ζ :=
  successorBillResidual_of_native α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ hNat
    (succPrefix_covGCtx α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)
    (succPrefix_frontierInner α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)
    (succPrefix_filterDefectCtx α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)
    (succPrefix_reconLettersCtx α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)
    (succPrefix_reconDefectConvCtx α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)

/-- **The `successor_bill` from the one remaining input** (the statement is the text
of `successor_bill`). -/
theorem successor_bill_of_open (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (hNat : NativeTemporalRepresentativesStatement)
 :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ →
    ∀ (Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ : ℕ), 1 ≤ Ce → 0 < τe →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → 0 < kS.σf → 0 < kS.lamC →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min kS.σf (ocDelta α q + σ₀)) kS.lamC D₀ H J N p nk Lc Lf
        Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
      succReconFloor r₀ D₀ H J N p Acl Lc ≤ Naux →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sX →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sZ →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∀ CQ Cpr : ℝ, ∃ (C c : ℝ) (mStar : ℕ), 0 < c ∧
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
      IsSeedPointwiseMolecular law kS seed tS tf →
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
      IsCommonPreparation law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀
        G kI.cr Q CQ Cpr p Nout Naux s₀ tf tp Preg →
      Set.Icc (tp - ocTauP α q Λ m) (tp + ocTauP α q Λ m) ⊆
        ocQuietTimes α q Λ ζ m →
    ∀ (f : ∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) (Ain : ℝ),
      weightedNorm 1 (G.mass law) (G.marker law) f ≤ Ain →
    ∀ (Y0 : ∀ v' : CompIn (G'.retained m H J).comps, TorusHk Naux (hr v'.1.root))
      (Y : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk Naux (hr v.1.root))
      (Yw : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk (Naux + 1) (hr v.1.root))
      (Yk : ∀ v u (_ : (G'.retained m H J).fam.Γ v u), ℝ →
        TorusHk (Naux + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root)),
      IsRetainedTrace G (G'.retained m H J) m p tp (Preg f) Y0 →
      (G'.retained m H J).IsRegSolution (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        seedK freshK φ₀ hφ₀ (D.κ (m - 1)) (streamVel (D.Φ (m - 1))) Naux tp tf Y0
        (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk →
      succBill D G m kI.c₀ kI.cr c σ₀ (succEta0 α q s) p N Lc Lf Acl J H tp tf
          (succTheta1 α q s σ₀ (succDstar D₀ N p H)) (succTheta2 α q s σ₀ (succDstar D₀ N p H))
        ≤ C * D.eps (m - 1) ^ Q ∧
      ComparisonClauses law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        G (G'.retained m H J) m p Naux N (succSchedR r₀ J H) sX sZ (succEta0 α q s) s₀ tp tf
        (C * Ain * succBill D G m kI.c₀ kI.cr c σ₀ (succEta0 α q s) p N Lc Lf Acl J H tp tf
          (succTheta1 α q s σ₀ (succDstar D₀ N p H)) (succTheta2 α q s σ₀ (succDstar D₀ N p H)))
        (C * D.eps (m - 1) ^ Q * Ain) f Y :=
  successor_bill_of_ingredients α s q ζ
    (successorBillResidual_of_open α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ hNat)
    (Construction.Preservation.BillScale.successor_bill_scale hα₀ hα₁ hs₀ hs₁ hq hζ)

end AVRegularity.Construction.Residual.Presentation.Cascade
end
