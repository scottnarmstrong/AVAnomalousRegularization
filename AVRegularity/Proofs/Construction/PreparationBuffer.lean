-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.Buffer.PreparationBufferFromScalarBudget
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarCellStrongTime
public import AVRegularity.Definitions.Construction.ScheduleFloor
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain

/-! The molecular buffer at the exact common-preparation statement type. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.Buffer
namespace AVRegularity.Providers

/-- **The molecular buffer of the common preparation**, with the molecular constant `c₀`
allocated beforehand, below a threshold `c₀max` fixed after `Λ` (display (11.1) of the paper). -/
theorem preparation_buffer (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
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
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∀ Jr : ℕ, 2 * Jr + N + 2 * p ≤ Naux → 2 * Jr ≤ kI.Ks →
    ∀ CQ Cpr : ℝ, ∃ (Cb : ℝ) (mStar : ℕ),
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
      [∀ r, CompleteSpace (hr r)]
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
    ∀ f : ∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root),
    ∀ (w : CompIn G.comps → ℝ), (w = fun _ => 1) ∨ w = G.marker law →
    ∀ (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (hr v.1.root))
      (Uw : ∀ v : CompIn G.comps, ℝ → TorusHk 1 (hr v.1.root))
      (Uk : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (0 + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root)),
      G.IsRegSolution (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        (D.κ m) (streamVel (D.Φ m)) 0 s₀ tf f (fun _ _ => 0) (fun _ _ => 0) U Uw Uk →
    ∀ t ∈ Set.Icc tp tf, ∃ Un : ∀ v : CompIn G.comps, TorusHk (2 * Jr) (hr v.1.root),
      (∀ v, truncateTorusHk (Nat.zero_le _) (Un v) = U v t) ∧
      weightedNorm (rhoStar D kI.c₀ m) (G.mass law) w Un ≤ Cb * weightedNorm 1 (G.mass law) w f  := by
  obtain ⟨Λ₀, hΛ₀, hscalar⟩ := preparation_scalar_budgets hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ
  obtain ⟨cmax, hcmax, hbudgets⟩ := hscalar Λ hΛ
  refine ⟨cmax, hcmax, ?_⟩
  intro φ₀ hφ₀ _hφsmooth _hφnonneg _hφmass _hφsupport bw hbw _hbwsmall
    Q T₀ hQ _hT₀ Ce τe kS r₀ D₀ _hCe hτe hc₀ hcmaxS hcr _hcrsmall _hσf _hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    _hNaux _hKres _halloc
  have hNout := preparation_schedule_output_positive hsched
  have hDm := preparation_schedule_order_ge_two D₀ N p H
  refine ⟨kS, 1, 1, le_rfl, zero_lt_one, ?_⟩
  intro kI hkI
  have hkparams := invariantAdmissible_molecular_parameters hkI
  have hcI : 0 < kI.c₀ := by rw [hkparams.1]; exact hc₀
  have hcImax : kI.c₀ ≤ cmax := by rw [hkparams.1]; exact hcmaxS
  have hcrI : 0 < kI.cr := by rw [hkparams.2.1]; exact hcr
  refine ⟨0, 0, ?_⟩
  intro CI Cw j₀ _hledger _hcarrier Jr _hJralloc hJrKs CQ Cpr
  let τ := q * min (ocDelta α q / 4) τe
  have hδ := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  have hτ : 0 < τ := mul_pos (zero_lt_one.trans hq.1)
    (lt_min (div_pos hδ (by norm_num)) hτe)
  obtain ⟨mStar, hmStar2, hmStarj, hbudget⟩ :=
    hbudgets kI.c₀ kI.cr Q τ CI CQ hcI hcImax hcrI hQ hτ j₀
  refine ⟨Real.sqrt (bufferEnergyCost (2 * Jr)), mStar, ?_⟩
  intro D hDα hDq hDΛ hDζ hΦ M hband hDterm Mnat _hMnat law _hlaw
    hr instNorm instInner instFinite instMeas instBorel instComplete seedK freshK _hfresh
    seed n tS tf hseed m hm hmn hnM tA s₀ htSA htAs hs₀tf _hTwindow
    G G' hcascade hlevel hInv _hsucc tp Preg hprep f w hw U Uw Uk hsol t ht
  subst m
  have hlevel2 : 2 ≤ G.level := hmStar2.trans hm
  have hjlevel : j₀ ≤ G.level := hmStarj.trans hm
  have hlevelM : G.level ≤ M := by omega
  have hlevelterm : G.level ≤ D.term := by rw [hDterm]; exact hlevelM
  have hb := hbudget M D.κ hband G.level hm hlevelM
  have hbD : PreparationScalarBudget (D.eps (G.level - 1)) (D.eps G.level)
      (D.κ G.level) (ocA D.α D.q D.Λ G.level) (rhoStar D kI.c₀ G.level)
      (rhoEnh D kI.cr G.level) CQ CI Q τ := by
    simpa only [OCData.eps, rhoStar, rhoEnh, hDα, hDq, hDΛ] using hb
  have h128 : 128 ≤ Λ := hΛ₀.trans hΛ
  have h128D : 128 ≤ D.Λ := by rwa [hDΛ]
  have hqD : 1 < D.q := by rw [hDq]; exact hq.1
  have hα₀D : 0 < D.α := by rw [hDα]; exact hα₀
  have hα₁D : D.α < 1 / 3 := by rw [hDα]; exact hα₁
  have hs₁D : s < (1 - D.α) / 2 := by rw [hDα]; exact hs₁
  have hqAD : IsAdmissibleQ D.α s D.q := by rwa [hDα, hDq]
  have hζD : IsFastProfile D.ζ := by rwa [hDζ]
  have hΦD : IsOCStreamSeq D.α D.q D.Λ D.ζ D.Φ := by
    simpa only [hDα, hDq, hDΛ, hDζ] using hΦ
  have hτpos : 0 < ocTau α q Λ G.level := Construction.Stream.ocTau_pos (by omega)
  have hτPPpos : 0 < ocTauPP α q Λ G.level := Construction.Stream.ocTauPP_pos (by omega)
  have htAs₀ : tA ≤ s₀ := by linarith only [htAs, hτpos]
  have hs₀tf' : s₀ ≤ tf := by linarith only [hs₀tf, hτPPpos]
  have htAtf : tA ≤ tf := htAs₀.trans hs₀tf'
  have htpbound : tp ≤ s₀ + 4 * ocTauPP α q Λ G.level := by
    simpa only [hDα, hDq, hDΛ] using hprep.2.2.1
  have htptf : tp ≤ tf := htpbound.trans hs₀tf
  let P := succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p
  let Mn := succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)
  have hprod : kI.Hprod = kI.G0 + Mn.H + 1 := hkparams.2.2
  have hseedbirths : ∀ v : CompIn seed.comps, v.1.births = [] := hseed.2.1
  have hsolkap : G.IsRegSolution P seedK freshK φ₀ hφ₀ (D.kap G.level)
      (streamVel (D.Φ G.level)) 0 s₀ tf f (fun _ _ => 0) (fun _ _ => 0) U Uw Uk := by
    simpa only [OCData.kap, Nat.min_eq_left hlevelterm] using hsol
  have hbuffer := preparation_buffer_from_scalar_budget law P Mn seedK freshK φ₀ hφ₀
    Mnat kI tA tf (CI * D.eps G.level ^ min (ocDelta α q / 4) τe)
    (CI * D.eps (G.level - 1) ^ τ) seed G hInv hseedbirths hcascade hprod
    hqD h128D (by omega) hjlevel hbw htAtf hlevelterm hDm (2 * Jr) hJrKs
    w hw s₀ htAs₀ hs₀tf' Preg hprep hNout htptf hbD rfl
    s hα₀D hα₁D hs₀ hs₁D hqAD hζD hΦD f U Uw Uk hsolkap
  exact hbuffer (2 * Jr) le_rfl t ht

end AVRegularity.Providers
