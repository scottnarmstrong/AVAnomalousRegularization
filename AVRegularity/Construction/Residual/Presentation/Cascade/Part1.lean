-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Residual.Presentation.Cascade.Budget
import AVRegularity.Definitions.Finite.FiniteLiftBridge
public import AVRegularity.Construction.Residual.Presentation.Cascade.FilterCtx
import AVRegularity.Construction.Residual.Presentation.Cascade.PointwiseEnvelope
import AVRegularity.Proofs.Results.Construction.SuccessorFluxUnique
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
import AVRegularity.CycleComparison.Error.Main
public import AVRegularity.Construction.Residual.Presentation.Cascade.CovGAction
import AVRegularity.CycleComparison.Assembly.OcDiagonal

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.EntryTerminal.Ingredients.Recon
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The family side of the window at every context** (cascade side of the bill residual,
the discharge of `frameReconFamilyBody`).

`succPrefix_reconFamily`: in the common prefix form, at every context of level `≥ m_*` and at the
frame of every lifted field of the context with classical representatives, an atlas `T` with
`FrameReconFamilyBody F 0 T reconCpart` (the absolute partition constant, so that the constants
of the partition step are chosen before the frame): the hypothesis `hR4` of
`frameReconAt_of_steps`. Its inputs: the stage invariant of the context on `[t_A, t_f]`, with
`t_A ≤ t_A + 3τ_m ≤ s₀ ≤ t_p` (the prefix and clause 2 of the preparation), the level
`m ≤ n < M = D.term`, and the depth bound of the incoming lift geometry
(`succPrefix_retainedProductionBundle`).

A stage without identities and `t_p = t_f` are allowed. -/

/-- **The family side at every context of level `≥ m_*`.** -/
def ReconFamilyCtxAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (mStar : ℕ) : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr), mStar ≤ c.m →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn c.G.comps) (fun v => hr v.1.root))
      (PZ : ∀ v : CompIn c.G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
      (hlift : IsLiftedField c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ
        (succEta0 α q s) c.tp c.tf c.Y CcT PZ aRep û)
      (aZ : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (aY : ℝ → Vec 2 → ∀ v : CompIn (c.G'.retained c.m H J).comps, hr v.1.root)
      (hZ : ∀ v, ∀ t ∈ Set.Icc c.tp c.tf, IsClassicalRep
        (succReadout c.m (c.D.eps (c.m - 1)) (succEta0 α q s) Naux (fun v' => c.Y v' t) v)
        (fun x => aZ t x v) Naux)
      (hY : ∀ v', ∀ t ∈ Set.Icc c.tp c.tf,
        IsClassicalRep (c.Y v' t) (fun x => aY t x v') Naux),
      ∃ T : (c.frame CcT PZ aRep û hlift aZ aY hZ hY).G.actualFamily.Atlas,
        FrameReconFamilyBody (c.frame CcT PZ aRep û hlift aZ aY hZ hY) 0 T reconCpart

/-- **The family side in the common prefix form**; the constant is the level `m_*`. -/
theorem succPrefix_reconFamily (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    SuccPrefix α s q (X := ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk _Lc _Lf _Lpr _Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        ReconFamilyCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀
          kI CI Cw j₀ CQ Cpr Q T₀ x) := by
  refine (succPrefix_retainedProductionBundle α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => 0)).imp ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ CQ Cpr hfacts x hx
  obtain ⟨-, hpk⟩ := hx
  refine ⟨x.2, ?_⟩
  intro hr _ _ _ _ _ _ _ c hm CcT PZ aRep û hlift aZ aY hZ hY
  have hk15 := hfacts.sched.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hk0 : 0 + N + 2 * p ≤ Naux := by
    have := (le_max_right _ _).trans hk15
    omega
  obtain ⟨hgeom, -, -⟩ := hpk hk0 c hm
  have hΛ1 : 1 ≤ Λ := le_trans (by norm_num) hfacts.hΛ
  have hΛ1D : 1 ≤ c.D.Λ := by rw [c.hΛ]; exact hΛ1
  have hζD : IsFastProfile c.D.ζ := by rw [c.hζ]; exact hζ
  have hmt : c.m ≤ c.D.term := by rw [c.hterm]; exact le_trans c.hmn c.hnM.le
  have hτ : 0 < ocTau α q Λ c.m := Construction.Stream.ocTau_pos hΛ1
  have htA : c.tA ≤ c.tp := by
    have h1 := c.hs₀
    have h2 : c.s₀ ≤ c.tp := c.hprep.2.1
    linarith
  exact frameReconFamilyBody (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law hφ₀ c.Mnat
    kI c.tA c.tf _ _ c.hinv c.hlevel hmt hΛ1D hζD hgeom.2.2.2.2.1 htA le_rfl 0

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The lift sequences and the lift settings of the window at every context**
(cascade side of the bill residual, the discharge of `frameReconSeqAt` and of
`frameReconSettingBody`).

`succPrefix_reconSetting`: in the common prefix form, constants `(C_G, C_w, C_a, C_g, m_*)` with
`0 ≤ C_g` such that at every context of level `≥ m_*` with the incoming lift geometry and the
quiet margin of the preparation endpoint (a premise of the data statement), at the frame of every
lifted field of the context with classical representatives,

* `FrameReconSeqAt F A_cl 0` (the hypothesis `hR2` of `frameReconAt_of_steps`), and
* a lift setting of the window `FrameReconSettingBody F law A_cl 0 C_G C_w C_a C_I C_g …` with the
  price bound `S_b = C_I` (the hypothesis `hR3`).

The price bound is uniform: the Schur constant of the invariant of the context is
`C_I·ε_m^{min(δ/4, τ_e)} ≤ C_I` (`C_I ≥ C_e ≥ 1`, `ε_m ≤ 1`), and the final constant of the
reconstruction is chosen before the context. The window starts `3τ_m` after `t_A`
(`t_A + 3τ_m ≤ s₀ ≤ t_p`, the prefix and clause 2 of the preparation) and `t_p ≤ s₀ + 4τ''_m ≤ t_f`
(clause 3 and the prefix).

A stage without identities, `t_p = s₀` and `A_cl = 1` are allowed. -/

/-- **The lift sequences and the lift settings at every context of level `≥ m_*`**, at the cleanup order `A_cl`, with the
constants `(C_G, C_w, C_a, C_g)` of the setting and the price bound `C_I`. -/
def ReconSettingCtxAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (Acl : ℕ) (CGl Cwl : ℕ → ℝ)
    (Ca Cg : ℝ) (mStar : ℕ) : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr), mStar ≤ c.m →
    IncomingLiftGeometryStatement c.G kI (succSchedR r₀ J H) 2 2 →
    Set.Icc (c.tp - ocTauP α q Λ c.m) (c.tp + ocTauP α q Λ c.m) ⊆ ocQuietTimes α q Λ ζ c.m →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn c.G.comps) (fun v => hr v.1.root))
      (PZ : ∀ v : CompIn c.G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
      (hlift : IsLiftedField c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ
        (succEta0 α q s) c.tp c.tf c.Y CcT PZ aRep û)
      (aZ : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (aY : ℝ → Vec 2 → ∀ v : CompIn (c.G'.retained c.m H J).comps, hr v.1.root)
      (hZ : ∀ v, ∀ t ∈ Set.Icc c.tp c.tf, IsClassicalRep
        (succReadout c.m (c.D.eps (c.m - 1)) (succEta0 α q s) Naux (fun v' => c.Y v' t) v)
        (fun x => aZ t x v) Naux)
      (hY : ∀ v', ∀ t ∈ Set.Icc c.tp c.tf,
        IsClassicalRep (c.Y v' t) (fun x => aY t x v') Naux),
      FrameReconSeqAt (c.frame CcT PZ aRep û hlift aZ aY hZ hY) Acl 0 ∧
      ∃ (qs qf : ℕ) (par : ℤ → Fin 2) (V : ℤ → ℝ → ℝ → ℝ)
        (bM : CompIn c.G.comps → CompIn c.G.comps → ℝ),
        FrameReconSettingBody (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law Acl 0 CGl Cwl Ca
          CI Cg qs qf par V bM

/-- The Schur constant of the invariant of a context is at most `C_I`. -/
theorem billCtx_ledgerPrice_le {α q τe CI ε : ℝ} (hδ : 0 < ocDelta α q) (hτe : 0 < τe) (hCI : 0 ≤ CI)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) : CI * ε ^ min (ocDelta α q / 4) τe ≤ CI :=
  mul_le_of_le_one_right hCI
    (Real.rpow_le_one hε0 hε1 (le_min (by linarith) hτe.le))

/-- **The lift sequences and the lift settings in the common prefix form**; the constants are `(C_G, C_w, C_a, C_g, m_*)`
with `0 ≤ C_g`. -/
theorem succPrefix_reconSetting (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    SuccPrefix α s q (X := (ℕ → ℝ) × (ℕ → ℝ) × ℝ × ℝ × ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk _Lc _Lf _Lpr Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        0 ≤ x.2.2.2.1 ∧
        ReconSettingCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀
          kI CI Cw j₀ CQ Cpr Q T₀ Acl x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) := by
  obtain ⟨Λ₁, hΛ₁, hseq⟩ := frameReconSeqAt hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Λ₂, hΛ₂, hset⟩ := frameReconSettingBody hα₀ hα₁ hs₀ hs₁ hq hζ
  refine SuccPrefix.of_scale ⟨max Λ₁ Λ₂, le_trans hΛ₁ (le_max_left _ _), fun Λ hΛ =>
    And.intro (hseq Λ (le_trans (le_max_left _ _) hΛ)) (hset Λ (le_trans (le_max_right _ _) hΛ))⟩
    ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ hfacts htail CQ Cpr
  obtain ⟨hseqΛ, hsetΛ⟩ := htail
  have hDm : 2 ≤ succSchedD D₀ N p (H + 1) :=
    Construction.Preservation.Buffer.preparation_schedule_order_ge_two D₀ N p H
  have hN1 : 1 ≤ N := le_trans (by norm_num) (succSchedule_two_le_N hfacts.sched)
  obtain ⟨m₁, -, hseqF⟩ := hseqΛ bw hfacts.hbw (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H) N
    Acl 0 hDm hN1
  obtain ⟨CGl, Cwl, Ca, Cg, m₀, -, hCg, hsetF⟩ := hsetΛ bw hfacts.hbw (succSchedD D₀ N p (H + 1))
    (succSchedR r₀ J H) N Acl 0 hDm hN1
  refine ⟨(CGl, Cwl, Ca, Cg, max m₁ m₀), hCg, ?_⟩
  intro hr _ _ _ _ _ _ _ c hm hgeom hquietMargin CcT PZ aRep û hlift aZ aY hZ hY
  obtain ⟨-, -, -, hj, hdepth, hres, hres2, hlen, -, -⟩ := hgeom
  have hΛ1 : 1 ≤ Λ := le_trans (by norm_num) hfacts.hΛ
  have hband : IsOCBandChain c.D.α c.D.q c.D.Λ c.D.ζ c.D.term c.D.κ := by
    rw [c.hα, c.hq, c.hΛ, c.hζ, c.hterm]
    exact c.hband
  have hmt : c.m < c.D.term := by rw [c.hterm]; exact lt_of_le_of_lt c.hmn c.hnM
  have hj' : j₀ ≤ c.m := by rw [← c.hlevel]; exact hj
  have hentry : c.tA + 3 * ocTau c.D.α c.D.q c.D.Λ c.m ≤ c.tp := by
    rw [c.hα, c.hq, c.hΛ]
    exact le_trans c.hs₀ c.hprep.2.1
  have htp : c.tp ≤ c.tf := by
    have h1 : c.tp ≤ c.s₀ + 4 * ocTauPP c.D.α c.D.q c.D.Λ c.G.level := c.hprep.2.2.1
    rw [c.hα, c.hq, c.hΛ, c.hlevel] at h1
    exact le_trans h1 c.htf
  have hquietMargin' : Set.Icc (c.tp - ocTauP c.D.α c.D.q c.D.Λ c.m)
      (c.tp + ocTauP c.D.α c.D.q c.D.Λ c.m) ⊆ ocQuietTimes c.D.α c.D.q c.D.Λ c.D.ζ c.m := by
    rw [c.hα, c.hq, c.hΛ, c.hζ]
    exact hquietMargin
  have hCI : 0 ≤ CI := by
    obtain ⟨CIthr, Cwthr, hled⟩ := hfacts.ledger
    exact le_trans (le_trans zero_le_one hfacts.hCe) hled.1
  have hS : CI * c.D.eps c.m ^ min (ocDelta α q / 4) τe ≤ CI := by
    have hΛD : 1 ≤ c.D.Λ := by rw [c.hΛ]; exact hΛ1
    exact billCtx_ledgerPrice_le (ocDelta_pos_of_admissible hα₀ hq) hfacts.hτe hCI
      (Construction.Stream.ocEpsilon_pos hΛD).le (ocEpsilon_le_one hΛD c.m)
  have hR2 : FrameReconSeqAt (c.frame CcT PZ aRep û hlift aZ aY hZ hY) Acl 0 :=
    hseqF hr c.D c.hα c.hq c.hΛ c.hζ c.hseq hband j₀ (c.frame CcT PZ aRep û hlift aZ aY hZ hY)
      c.law hφ₀ c.Mnat kI c.tA c.tf _ _ c.hinv rfl rfl c.hlevel
      (le_trans (le_max_left _ _) hm) hmt hj' hdepth hres hres2 hlen rfl hentry htp hquietMargin'
  exact ⟨hR2, _, _, _, _, _,
    hsetF hr c.D c.hα c.hq c.hΛ c.hζ c.hseq hband j₀ (c.frame CcT PZ aRep û hlift aZ aY hZ hY)
      c.law hφ₀ c.Mnat kI c.tA c.tf _ _ c.hinv rfl rfl c.hlevel
      (le_trans (le_max_right _ _) hm) hmt hj' hdepth hres hres2 hlen hR2 CI hS⟩

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Analysis.Convolution
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The defect step of the fine tail at a frame, and the fine tail bound.**

`frameFineDefectAt`: `FrameFineDefectAt F law c₀ L_f K C` from the stage invariant of the
frame's stage `F.G` on `[t_A, t_B] ⊇ [t_p, t_f]` (`stageFineDefect` at `k = 0`, `m = F.m`).
The constant is explicit: any `C ≥ stageFineMconst … · max θ_K 0`. With the lift step
(`fineLiftAt`) and `frameFineTail_of_lift_defect` it gives `FrameFineTailAt` with the constant
`C · (C_k C_k)`.

The degenerate cases are included: no edge (`hasFluxBound_of_zero`: the kernel sums are empty, the
bound holds), an empty window `t_f < t_p` (the realization is `0`), one kernel order (the terminal
statement, `Dm = D_t`). -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **The defect step of the fine tail at a frame.** -/
theorem frameFineDefectAt (F : Frame D hr Dm b j₀) (law : BirthLaw)
    (hφ₀ : Integrable F.φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) F.φ₀) (hnn : ∀ z, 0 ≤ F.φ₀ z)
    (hm : ∫ z, F.φ₀ z = 1) (hs : Function.support F.φ₀ ⊆ closedEuclideanUnitBall)
    (M : ℕ) (kS : InvConsts) (tA tB S θK : ℝ)
    (hI : IsStageInvariant law F.P F.seedK F.freshK F.φ₀ hφ₀ M kS tA tB S θK F.G)
    (hres0 : ∀ v : CompIn F.G.comps, 0 ≤ compReserve kS v.1)
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hi : 1 ≤ F.G.level) (hj : j₀ ≤ F.G.level) (hb : 0 < b)
    (hε1 : 0 < D.eps (F.G.level - 1)) (hκ : 0 < D.kap F.G.level) (hD2 : 2 ≤ Dm)
    (hθ : θK ≤ 1 / 8) (K Lf : ℕ) (c₀ : ℝ)
    (hlev : F.G.level = F.m) (hkap : D.kap F.G.level = D.κ F.m) (hc₀ : kS.c₀ = c₀)
    (hRpos : 0 < rhoStar D c₀ F.m) (hRε : rhoStar D c₀ F.m ≤ D.eps (F.G.level - 1))
    (hLf : Lf ≤ kS.Lker) (hK : (Dm - 2) + Lf ≤ K)
    (hsmall : kS.Cwid * D.eps F.G.level ^ kS.σf ≤ 1)
    (hcpos : ∀ j, j + 2 ≤ Dm → 0 < kS.cker j) (hA : tA ≤ F.tp) (hB : F.tf ≤ tB) (C : ℝ)
    (hC : stageFineMconst F.φ₀ Lf Dm 0 (max kS.Γk 0) kS.cker * max θK 0 ≤ C) :
    FrameFineDefectAt F law c₀ Lf K C :=
  stageFineDefect law F.P F.seedK F.freshK F.φ₀ hφ₀ hd hnn hm hs M kS tA tB S θK F.G hI hres0
    hq hΛ hi hj hb hε1 hκ hD2 hθ F.m 0 K Lf c₀ F.tp F.tf hlev hkap hc₀ hRpos hRε (Nat.zero_le _)
    hLf (by omega) hsmall hcpos hA hB C hC

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The vanishing of the positive lifts at the entrance (`CellVanish`) at every context**
(cascade side of the bill residual, the second input of the initial error).

`succPrefix_cellVanish`: in the common prefix form, a level `m_*` such that at every context of
level `≥ m_*`, under the quiet margin of the preparation endpoint (a premise of the data
statement), for every lifted field `(CcT, PZ, aRep, û)` of the context, `CellVanish c CcT`:
for every observed pulse of the degenerate window `[t_p, t_p]`, the cell time of `t_p` lies in
the window of the slot and the positive lift coefficients vanish there.

It is the `seq_zero_at_tp'` at the frame of the lifted field. The frame needs classical
representatives of the readout and of the retained solution; they exist by
`retained_high_and_reps` (from the retained solution at the order `N_aux + 3` of the
retained production bundle) and do not enter the conclusion. The entrance is three renewal times
(`t_A + 3τ_m ≤ s₀ ≤ t_p`); the ellipticity of the lift metric is the uniform native ellipticity
above a level `M₁`.

With no observed pulse at `t_p` the statement is vacuous; a stage without identities and
`t_p = t_f` are allowed. -/

/-- **`CellVanish` at every context of level `≥ m_*`**, under the quiet margin of the preparation
endpoint, for every lifted field of the context. -/
def CellVanishCtxAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (mStar : ℕ) : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr), mStar ≤ c.m →
    Set.Icc (c.tp - ocTauP α q Λ c.m) (c.tp + ocTauP α q Λ c.m) ⊆ ocQuietTimes α q Λ ζ c.m →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn c.G.comps) (fun v => hr v.1.root))
      (PZ : ∀ v : CompIn c.G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root)),
      IsLiftedField c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ
        (succEta0 α q s) c.tp c.tf c.Y CcT PZ aRep û →
      CellVanish c CcT

/-- **`CellVanish` in the common prefix form**; the constant is the level `m_*`. -/
theorem succPrefix_cellVanish (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    SuccPrefix α s q (X := ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk _Lc _Lf _Lpr _Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        CellVanishCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI
          CI Cw j₀ CQ Cpr Q T₀ x) := by
  refine (succPrefix_retainedProductionBundle α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => 0)).imp ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ CQ Cpr hfacts x hx
  obtain ⟨-, hpk⟩ := hx
  obtain ⟨M₁, -, hell⟩ :=
    Construction.Preservation.FullLift.uniform_native_lift_ellipticity_all_carriers
      α s q hα₀ hα₁ hs₀ hs₁ hq Λ hfacts.hΛ ζ hζ
  have hk15 := hfacts.sched.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hk0 : 0 + N + 2 * p ≤ Naux := by
    have := (le_max_right _ _).trans hk15
    omega
  have hΛ1 : 1 ≤ Λ := le_trans (by norm_num) hfacts.hΛ
  refine ⟨max x.2 (M₁ + 1), ?_⟩
  intro hr _ _ _ _ _ _ _ c hm hquietMargin CcT PZ aRep û hlift
  obtain ⟨-, hhigh, -⟩ := hpk hk0 c (le_trans (le_max_left _ _) hm)
  obtain ⟨Yhi, -, aZ, aY, hZ, hY⟩ := retained_high_and_reps c.G (c.G'.retained c.m H J)
    c.m Naux (succEta0 α q s) c.tp c.tf c.Y hhigh
  have hΛD : 1 ≤ c.D.Λ := le_trans (by norm_num) (c.lambda_ge hfacts.hΛ)
  have hζD : IsFastProfile c.D.ζ := by rw [c.hζ]; exact hζ
  have hentry : c.tA + 3 * ocTau c.D.α c.D.q c.D.Λ c.m ≤ c.tp := by
    rw [c.hα, c.hq, c.hΛ]
    exact c.entrance
  have hquietMargin' : Set.Icc (c.tp - ocTauP c.D.α c.D.q c.D.Λ c.m)
      (c.tp + ocTauP c.D.α c.D.q c.D.Λ c.m) ⊆ ocQuietTimes c.D.α c.D.q c.D.Λ c.D.ζ c.m := by
    rw [c.hα, c.hq, c.hΛ, c.hζ]
    exact hquietMargin
  have hcs : 0 < c.D.cellScaleSq c.m :=
    (cellScale_facts (c.frame CcT PZ aRep û hlift aZ aY hZ hY) hΛD hζD c.bandD
      c.m_le_term).1
  intro k hk hcut
  have hodd : Odd k := CycleComparison.LiftSetting.obsPulse_odd hk
  obtain ⟨y, hy1, hy2⟩ := CycleComparison.LiftSetting.obsPulse_nonempty hk
  have hy : y = c.tp := le_antisymm hy2.2 hy2.1
  have hwin : c.tp ≤ ((k : ℝ) + 61 / 48) * ocTau c.D.α c.D.q c.D.Λ c.m := by
    rw [← hy]
    exact hy1.2
  have hstart : c.D.slotStart c.m k ≤ c.tp := by
    rw [← hy]
    exact hy1.1
  refine ⟨⟨div_le_div_of_nonneg_right hstart hcs.le, div_le_div_of_nonneg_right hwin hcs.le⟩, ?_⟩
  exact seq_zero_at_tp' (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.hinv c.hlevel hΛD hζD
    c.bandD c.m_le_term hentry c.tp_le_tf hquietMargin' hodd hwin hstart
    (fun t ht X' ξ => hell (CompIn c.G.comps) (fun v => hr v.1.root) _ c.D c.hα c.hq c.hΛ c.hζ
      c.hseq c.bandD c.m (le_trans (le_max_right _ _) hm) k hodd _ _ t ht X' ξ)
    ((c.frame CcT PZ aRep û hlift aZ aY hZ hY).lift.1 k hodd)

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.CycleComparison.Coarse AVRegularity.CycleComparison.Error
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The covariance-filter estimate (`FilterEstimate`) at every context** (cascade side of
the bill residual, the first input of the initial error).

* `filter_family`: the estimate `filter_component` for a family of fields, in the
  weighted norms: order `0` and radius `1` on the left (at order `0` the factorial norm does not
  see the radius), radius `ρ` on the right.
* `succPrefix_filterEstimate`: in the common prefix form, at every context of level `≥ m_*` and
  for every lifted field of the context, `FilterEstimate c C_fil ω PZ` with
  `C_fil = cqp((4p)²) p` (a function of `p` alone) and the filter scale `ω` of the bill,
  `ω = (sup_{[t_p,t_f]} ∑|𝖧_m|)/rhoEnh D k_I.c_r m ²` (the single time `t_p` lies in the window).

Inputs: the size of the covariance primitive at the radius `rhoEnh D k_I.c_r m`
(`succPrefix_covSize`: `covBound 𝖧(t) ≤ ω ρ²` on the window and `0 ≤ ω ≤ 1`), stated at the frame
of the lifted field with the classical representatives of `retained_high_and_reps`; the orders `4p ≤ N_out` from the
schedule (`N_aux + 4p ≤ N_out`).

For `A_in = 0` or an empty component family both sides are `0`; `t_p = t_f` is allowed. -/

section Family

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] [∀ i, FiniteDimensional ℝ (h i)]

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- A componentwise bound of the factorial norms gives the bound of the weighted norms, the left
side at order `0` and radius `1`. -/
theorem weighted_le_of_components {Nh : ℕ} {ρ C : ℝ} (hC : 0 ≤ C) (π : ι → ℝ)
    (hπ : ∀ v, 0 ≤ π v) (Dv : ∀ v, TorusHk 0 (h v)) (X : ∀ v, TorusHk Nh (h v))
    (hcomp : ∀ v, Real.sqrt (factorialNormSq ρ (Dv v).val) ≤
      C * Real.sqrt (factorialNormSq ρ (X v).val)) :
    Real.sqrt (massNormSq (E := h) (K := fun _ => 0) 1 π (fun v => (Dv v).val)) ≤
      C * Real.sqrt (massNormSq (E := h) (K := fun _ => Nh) ρ π (fun v => (X v).val)) := by
  have hterm : ∀ v, factorialNormSq 1 (Dv v).val ≤ C ^ 2 * factorialNormSq ρ (X v).val := by
    intro v
    rw [factorialNormSq_order_zero 1 ρ]
    have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hcomp v) 2
    rwa [Real.sq_sqrt (factorialNormSq_nonneg _ _), mul_pow,
      Real.sq_sqrt (factorialNormSq_nonneg _ _)] at h2
  have hsum : massNormSq (E := h) (K := fun _ => 0) 1 π (fun v => (Dv v).val) ≤
      C ^ 2 * massNormSq (E := h) (K := fun _ => Nh) ρ π (fun v => (X v).val) := by
    unfold massNormSq
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun v _ => ?_
    calc (π v)⁻¹ * factorialNormSq 1 (Dv v).val
        ≤ (π v)⁻¹ * (C ^ 2 * factorialNormSq ρ (X v).val) :=
          mul_le_mul_of_nonneg_left (hterm v) (inv_nonneg.2 (hπ v))
      _ = C ^ 2 * ((π v)⁻¹ * factorialNormSq ρ (X v).val) := by ring
  calc Real.sqrt (massNormSq (E := h) (K := fun _ => 0) 1 π (fun v => (Dv v).val))
      ≤ Real.sqrt (C ^ 2 * massNormSq (E := h) (K := fun _ => Nh) ρ π (fun v => (X v).val)) :=
        Real.sqrt_le_sqrt hsum
    _ = C * Real.sqrt (massNormSq (E := h) (K := fun _ => Nh) ρ π (fun v => (X v).val)) := by
        rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC]

/-- **The covariance-filter estimate for a family of fields**, in the weighted norms. -/
theorem filter_family {ρ ω : ℝ} (hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ)
    (hb : covBound Hc ≤ ω * ρ ^ 2) (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1) (p : ℕ) {Nh Nq Np : ℕ}
    (h4 : 4 * p ≤ Nh) (π : ι → ℝ) (hπ : ∀ v, 0 ≤ π v) (X : ∀ v, TorusHk Nh (h v))
    (Qh : ∀ v, TorusHk Nq (h v)) (PZ : ∀ v, TorusHk Np (h v))
    (hQ : ∀ v, IsCovImage (covPolyQ Hc p) (X v) (Qh v))
    (hP : ∀ v, IsCovImage (covPolyP Hc p) (Qh v) (PZ v)) :
    Real.sqrt (massNormSq (E := h) (K := fun _ => 0) 1 π (fun v =>
        (truncateTorusHk (Nat.zero_le Np) (PZ v) - truncateTorusHk (Nat.zero_le Nh) (X v)).val)) ≤
      cqp (((4 * p : ℕ) : ℝ) ^ 2) p * ω ^ (p + 1) *
        Real.sqrt (massNormSq (E := h) (K := fun _ => Nh) ρ π (fun v => (X v).val)) :=
  weighted_le_of_components
    (mul_nonneg (cqp_nonneg' (sq_nonneg _) p) (pow_nonneg hω0 _)) π hπ _ X
    (fun v => filter_component hρ Hc hb hω0 hω1 p h4 (X v) (Qh v) (PZ v) (hQ v) (hP v))

end Family

/-- **`FilterEstimate` at every context of level `≥ m_*`**, for every lifted field of the
context, with `C_fil = cqp((4p)²) p` and the filter scale `ω` of the bill. -/
def FilterEstimateCtxAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (mStar : ℕ) : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr), mStar ≤ c.m →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn c.G.comps) (fun v => hr v.1.root))
      (PZ : ∀ v : CompIn c.G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root)),
      IsLiftedField c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ
        (succEta0 α q s) c.tp c.tf c.Y CcT PZ aRep û →
      FilterEstimate c (cqp (((4 * p : ℕ) : ℝ) ^ 2) p)
        ((⨆ t : Set.Icc c.tp c.tf, ∑ a : Fin 2, ∑ a' : Fin 2, |covPrimitive c.D c.m t a a'|) /
          rhoEnh c.D kI.cr c.m ^ 2) PZ

/-- **`FilterEstimate` in the common prefix form**; the constant is the level `m_*`. -/
theorem succPrefix_filterEstimate (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    SuccPrefix α s q (X := ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk _Lc _Lf _Lpr _Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        FilterEstimateCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀
          kI CI Cw j₀ CQ Cpr Q T₀ x) := by
  have h1 := succPrefix_covSize α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ (fun _ kI => kI.cr)
    (fun _ _ h0 he => he ▸ h0)
  have h2 := succPrefix_retainedProductionBundle α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => 0)
  refine (h1.and h2).imp ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ CQ Cpr hfacts x hx
  obtain ⟨hcs, -, hpk⟩ := hx
  obtain ⟨thr, hkI⟩ := hfacts.admissible
  have hcr : 0 < kI.cr := by rw [hkI.2.1]; exact hfacts.hcr
  have hΛ1 : 1 ≤ Λ := le_trans (by norm_num) hfacts.hΛ
  have hk15 := hfacts.sched.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hk16 : Naux + 4 * p ≤ Nout := hfacts.sched.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hk0 : 0 + N + 2 * p ≤ Naux := by
    have := (le_max_right _ _).trans hk15
    omega
  refine ⟨max x.1 x.2.2, ?_⟩
  intro hr _ _ _ _ _ _ _ c hm CcT PZ aRep û hlift Qh hQ hP
  obtain ⟨-, hhigh, -⟩ := hpk hk0 c (le_trans (le_max_right _ _) hm)
  obtain ⟨Yhi, -, aZ, aY, hZ, hY⟩ := retained_high_and_reps c.G (c.G'.retained c.m H J)
    c.m Naux (succEta0 α q s) c.tp c.tf c.Y hhigh
  obtain ⟨hb, hω0, hω1, -⟩ := hcs c (le_trans (le_max_left _ _) hm) CcT PZ aRep û hlift aZ aY
    hZ hY
  have hρ : 0 < rhoEnh c.D kI.cr c.m :=
    mul_pos hcr (Real.sqrt_pos.2 (mul_pos (c.kappa_pred_pos hΛ1 hζ)
      (Construction.Stream.ocTauPP_pos (le_trans (by norm_num) (c.lambda_ge hfacts.hΛ)))))
  exact filter_family hρ (covPrimitive c.D c.m c.tp) (hb c.tp ⟨le_rfl, c.tp_le_tf⟩) hω0 hω1
    p (by omega) _ (fun v => div_nonneg (c.mass_pos hq.1 hfacts.hΛ v).le (sq_nonneg _))
    (c.Preg c.f) Qh (fun v => PZ v c.tp) hQ hP

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.CycleComparison.Coarse
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! **The initial error at every context** (cascade side of the bill residual).

* `succPrefix_initialValue`: the conclusion of the proved `successor_initial_value`
  (`InitialValueConclusion`: a covariance image `Q h` of `h = P_reg f`, `P Z(t_p) = 𝖯_p(Q h)`,
  and the splitting of `U(t_p) − û(t_p)` in three differences) at every context, in the common
  prefix form. The proof has the prefix without the lift-order floors and without
  the order floor; those premises are not used.
* `succPrefix_initialError`: the initial error at every context of level `≥ m_*`, under the quiet margin of the
  preparation endpoint: for the regularized solution `U` of the incoming system from `s₀` and
  every lifted field `û` of the context,

      ‖U(t_p) − û(t_p)‖_{L²_π} ≤ (C_Q·ε_{m−1}^Q + C_fil·ω^{p+1}·C_Q)·‖f‖_{L²_π},

  with `C_fil = cqp((4p)²) p` and `ω` the filter scale of the bill. It is the
  `initialError` with its three named hypotheses discharged (`succPrefix_initialValue`,
  `succPrefix_cellVanish`, `succPrefix_filterEstimate`) and the scale facts of the context.

For `f = 0` both sides are `0`; `t_p = t_f` and an empty component family are allowed. -/

/-- **The conclusion of `successor_initial_value` at every context of level `≥ m_*`.** -/
def InitialValueCtxAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (mStar : ℕ) : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr), mStar ≤ c.m →
    ∀ (U : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
      (Uw : ∀ v : CompIn c.G.comps, ℝ → TorusHk 1 (hr v.1.root))
      (Uk : ∀ v u (_ : c.G.fam.Γ v u), ℝ →
        TorusHk (0 + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root)),
      c.G.IsRegSolution (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK
        φ₀ hφ₀ (c.D.κ c.m) (streamVel (c.D.Φ c.m)) 0 c.s₀ c.tf c.f (fun _ _ => 0) (fun _ _ => 0)
        U Uw Uk →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn c.G.comps) (fun v => hr v.1.root))
      (PZ : ∀ v : CompIn c.G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root)),
      IsLiftedField c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ
        (succEta0 α q s) c.tp c.tf c.Y CcT PZ aRep û →
      InitialValueConclusion c U PZ û

/-- **`successor_initial_value` in the common prefix form**; the constant is the level `m_*`. -/
theorem succPrefix_initialValue (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    SuccPrefix α s q (X := ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk _Lc _Lf _Lpr _Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        InitialValueCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀
          kI CI Cw j₀ CQ Cpr Q T₀ x) := by
  obtain ⟨Λ₀, hΛ₀, h⟩ := Providers.successor_initial_value α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ
  obtain ⟨c₀max, hc₀max, h⟩ := h Λ hΛ
  refine ⟨c₀max, hc₀max, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout _hrecon halloc _hsX _hsZ
  obtain ⟨thr, CH, Υ, hCH, hΥ, h⟩ := h φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw
    hbwupper Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr
    hcrupper hσf hlamC H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc
  refine ⟨thr, CH, Υ, hCH, hΥ, ?_⟩
  intro kI hkI
  obtain ⟨CIthr, Cwthr, h⟩ := h kI hkI
  refine ⟨CIthr, Cwthr, ?_⟩
  intro CI Cw j₀ hledger hstart CQ Cpr
  obtain ⟨mStar, h⟩ := h CI Cw j₀ hledger hstart CQ Cpr
  refine ⟨mStar, ?_⟩
  intro hr _ _ _ _ _ _ _ c hm U Uw Uk hU CcT PZ aRep û hlift
  exact h c.D c.hα c.hq c.hΛ c.hζ c.hseq c.M c.hband c.hterm c.Mnat c.hMnat c.law c.hlaw
    c.seedK c.freshK c.hfresh c.seed c.n c.tS c.tf c.hseed c.m hm c.hmn c.hnM c.tA c.s₀ c.htA
    c.hs₀ c.htf c.hT₀ c.G c.G' c.hcascade c.hlevel c.hinv c.hactual c.tp c.Preg c.hprep c.f
    c.Ain c.hf c.Y0 c.Y c.Yw c.Yk c.htrace c.hsol U Uw Uk hU CcT PZ aRep û hlift

/-- **The initial error at every context of level `≥ m_*`**, under the quiet margin of the preparation endpoint. -/
def InitialErrorCtxAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (mStar : ℕ) : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr), mStar ≤ c.m →
    Set.Icc (c.tp - ocTauP α q Λ c.m) (c.tp + ocTauP α q Λ c.m) ⊆ ocQuietTimes α q Λ ζ c.m →
    ∀ (U : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
      (Uw : ∀ v : CompIn c.G.comps, ℝ → TorusHk 1 (hr v.1.root))
      (Uk : ∀ v u (_ : c.G.fam.Γ v u), ℝ →
        TorusHk (0 + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root)),
      c.G.IsRegSolution (succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p) c.seedK c.freshK
        φ₀ hφ₀ (c.D.κ c.m) (streamVel (c.D.Φ c.m)) 0 c.s₀ c.tf c.f (fun _ _ => 0) (fun _ _ => 0)
        U Uw Uk →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn c.G.comps) (fun v => hr v.1.root))
      (PZ : ∀ v : CompIn c.G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root)),
      IsLiftedField c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ
        (succEta0 α q s) c.tp c.tf c.Y CcT PZ aRep û →
      weightedNorm 1 (c.G.mass c.law) (fun _ => 1) (fun v => U v c.tp - û v c.tp) ≤
        (CQ * c.D.eps (c.m - 1) ^ Q + cqp (((4 * p : ℕ) : ℝ) ^ 2) p *
          ((⨆ t : Set.Icc c.tp c.tf, ∑ a : Fin 2, ∑ a' : Fin 2, |covPrimitive c.D c.m t a a'|) /
            rhoEnh c.D kI.cr c.m ^ 2) ^ (p + 1) * CQ) *
          weightedNorm 1 (c.G.mass c.law) (fun _ => 1) c.f

/-- **The initial error in the common prefix form**; the constant is the level `m_*`. -/
theorem succPrefix_initialError (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    SuccPrefix α s q (X := ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk _Lc _Lf _Lpr _Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        InitialErrorCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀
          kI CI Cw j₀ CQ Cpr Q T₀ x) := by
  have h1 := succPrefix_initialValue α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  have h2 := succPrefix_cellVanish α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  have h3 := succPrefix_filterEstimate α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ((h1.and h2).and h3).imp ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ CQ Cpr hfacts x hx
  obtain ⟨⟨hiv, hcv⟩, hfe⟩ := hx
  have hΛ1 : 1 ≤ Λ := le_trans (by norm_num) hfacts.hΛ
  refine ⟨max (max x.1.1 x.1.2) x.2, ?_⟩
  intro hr _ _ _ _ _ _ _ c hm hquietMargin U Uw Uk hU CcT PZ aRep û hlift
  have hm1 : x.1.1 ≤ c.m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hm2 : x.1.2 ≤ c.m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hm3 : x.2 ≤ c.m := le_trans (le_max_right _ _) hm
  have hΛD : 1 ≤ c.D.Λ := le_trans (by norm_num) (c.lambda_ge hfacts.hΛ)
  have hκ := c.kappa_pos hΛ1 hζ
  have hcs : c.D.cellScaleSq c.m ≠ 0 := by
    unfold OCData.cellScaleSq OCData.eps OCData.kap
    rw [min_eq_left c.m_le_term]
    exact (div_pos (pow_pos (Construction.Stream.ocEpsilon_pos hΛD) 2) hκ).ne'
  have hρ : liftLength c.D c.m ≠ 0 :=
    (Real.sqrt_pos.2 (mul_pos (c.kappa_pred_pos hΛ1 hζ)
      (Construction.Stream.ocTauPP_pos hΛD))).ne'
  have hQS : QuietScale c :=
    ⟨Construction.Stream.ocTau_pos hΛD, hcs, hρ, c.mass_pos hq.1 hfacts.hΛ⟩
  have hω0 : 0 ≤ (⨆ t : Set.Icc c.tp c.tf, ∑ a : Fin 2, ∑ a' : Fin 2,
      |covPrimitive c.D c.m t a a'|) / rhoEnh c.D kI.cr c.m ^ 2 :=
    div_nonneg (Real.iSup_nonneg fun t => Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => abs_nonneg _) (sq_nonneg _)
  exact initialError c _ _ hQS (cqp_nonneg' (sq_nonneg _) p) hω0 U Uw Uk hU CcT PZ aRep û
    hlift (hcv c hm2 hquietMargin CcT PZ aRep û hlift) (hiv c hm1 U Uw Uk hU CcT PZ aRep û hlift)
    (hfe c hm3 CcT PZ aRep û hlift)

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end

section
@[expose] public noncomputable section
section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! Shared high-order native slot-lift input for the covariance G form. Its producer is shared by
parts 1, 3 and 4: each uses the SAME window, supplied sequences and source envelope.
Only the setting constants and the level threshold are chosen before the context;
the actual Schur matrix and the atlas depend on the context as in the lift settings and the family side.
The cases `p = 0`, empty components, a zero datum and `tp = tf` need no interface change. -/

/-- Uniform setting constants and a starting level; all precede the actual frame. -/
structure CovGSettingConsts where
  CG : ℕ → ℝ
  CW : ℕ → ℝ
  Ca : ℝ
  mStar : ℕ

/-- The high-order slot-lift input at every context, at `ell = kc + 4p` and price `Sb = CI`. -/
def CovGInputsCtxAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw Ce τe : ℝ) (kS : InvConsts)
    (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ) (kI : InvConsts)
    (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (Acl : ℕ)
    (x : CovGSettingConsts) : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr), x.mStar ≤ c.m →
    Set.Icc (c.tp - ocTauP α q Λ c.m) (c.tp + ocTauP α q Λ c.m) ⊆
      ocQuietTimes α q Λ ζ c.m →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn c.G.comps) (fun v => hr v.1.root))
      (PZ : ∀ v : CompIn c.G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
      (hlift : IsLiftedField c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ
        (succEta0 α q s) c.tp c.tf c.Y CcT PZ aRep û)
      (aZ : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (aY : ℝ → Vec 2 → ∀ v : CompIn (c.G'.retained c.m H J).comps, hr v.1.root)
      (hZ : ∀ v, ∀ t ∈ Set.Icc c.tp c.tf, IsClassicalRep
        (succReadout c.m (c.D.eps (c.m - 1)) (succEta0 α q s) Naux (fun v' => c.Y v' t) v)
        (fun x => aZ t x v) Naux)
      (hY : ∀ v', ∀ t ∈ Set.Icc c.tp c.tf,
        IsClassicalRep (c.Y v' t) (fun x => aY t x v') Naux),
      let F := c.frame CcT PZ aRep û hlift aZ aY hZ hY
      Nonempty (CovGNativeWindow F c.law) ∧ Nonempty (CovGNativeAgreement F) ∧
        CovGFamily F ∧ Nonempty (CovGNativePulse F c.law Acl
          (succKc r₀ D₀ H J N p Acl + 4 * p) x.CG x.CW x.Ca CI)

/-- The shared native input in the exact prefix. -/
def CovGInputsStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  SuccPrefix α s q (X := CovGSettingConsts)
    (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk _Lc _Lf _Lpr Acl Naux Nout _Kres npad
        sX sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
      CovGInputsCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad
        sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ Acl x)

/-! High-order settings for the shared covariance-G slot-lift input. -/

/-- **The lift sequences and the lift settings at every context of level `≥ m_*`**, at the cleanup order `A_cl`, with the
constants `(C_G, C_w, C_a, C_g)` of the setting and the price bound `C_I`. -/
def ReconSettingCtxAt' (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (Acl : ℕ) (CGl Cwl : ℕ → ℝ)
    (Ca Cg : ℝ) (mStar : ℕ) : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    (c : BillCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ hr), mStar ≤ c.m →
    IncomingLiftGeometryStatement c.G kI (succSchedR r₀ J H) 2 2 →
    Set.Icc (c.tp - ocTauP α q Λ c.m) (c.tp + ocTauP α q Λ c.m) ⊆ ocQuietTimes α q Λ ζ c.m →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn c.G.comps) (fun v => hr v.1.root))
      (PZ : ∀ v : CompIn c.G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (û : ∀ v : CompIn c.G.comps, ℝ → TorusHk 0 (hr v.1.root))
      (hlift : IsLiftedField c.G (c.G'.retained c.m H J) c.m p Naux N (succSchedR r₀ J H) sX sZ
        (succEta0 α q s) c.tp c.tf c.Y CcT PZ aRep û)
      (aZ : ℝ → Vec 2 → ∀ v : CompIn c.G.comps, hr v.1.root)
      (aY : ℝ → Vec 2 → ∀ v : CompIn (c.G'.retained c.m H J).comps, hr v.1.root)
      (hZ : ∀ v, ∀ t ∈ Set.Icc c.tp c.tf, IsClassicalRep
        (succReadout c.m (c.D.eps (c.m - 1)) (succEta0 α q s) Naux (fun v' => c.Y v' t) v)
        (fun x => aZ t x v) Naux)
      (hY : ∀ v', ∀ t ∈ Set.Icc c.tp c.tf,
        IsClassicalRep (c.Y v' t) (fun x => aY t x v') Naux),
      FrameReconSeqAt (c.frame CcT PZ aRep û hlift aZ aY hZ hY) Acl (succKc r₀ D₀ H J N p Acl + 4 * p) ∧
      ∃ (qs qf : ℕ) (par : ℤ → Fin 2) (V : ℤ → ℝ → ℝ → ℝ)
        (bM : CompIn c.G.comps → CompIn c.G.comps → ℝ),
        FrameReconSettingBody (c.frame CcT PZ aRep û hlift aZ aY hZ hY) c.law Acl (succKc r₀ D₀ H J N p Acl + 4 * p) CGl Cwl Ca
          CI Cg qs qf par V bM

/-- **The lift sequences and the lift settings in the common prefix form**; the constants are `(C_G, C_w, C_a, C_g, m_*)`
with `0 ≤ C_g`. -/
theorem reconSetting (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    SuccPrefix α s q (X := (ℕ → ℝ) × (ℕ → ℝ) × ℝ × ℝ × ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk _Lc _Lf _Lpr Acl Naux Nout _Kres npad sX
          sZ σ₀ _a _σ kI CI Cw j₀ CQ Cpr x =>
        0 ≤ x.2.2.2.1 ∧
        ReconSettingCtxAt' α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀
          kI CI Cw j₀ CQ Cpr Q T₀ Acl x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) := by
  obtain ⟨Λ₁, hΛ₁, hseq⟩ := frameReconSeqAt hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Λ₂, hΛ₂, hset⟩ := frameReconSettingBody hα₀ hα₁ hs₀ hs₁ hq hζ
  refine SuccPrefix.of_scale ⟨max Λ₁ Λ₂, le_trans hΛ₁ (le_max_left _ _), fun Λ hΛ =>
    And.intro (hseq Λ (le_trans (le_max_left _ _) hΛ)) (hset Λ (le_trans (le_max_right _ _) hΛ))⟩
    ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ hfacts htail CQ Cpr
  obtain ⟨hseqΛ, hsetΛ⟩ := htail
  have hDm : 2 ≤ succSchedD D₀ N p (H + 1) :=
    Construction.Preservation.Buffer.preparation_schedule_order_ge_two D₀ N p H
  have hN1 : 1 ≤ N := le_trans (by norm_num) (succSchedule_two_le_N hfacts.sched)
  obtain ⟨m₁, -, hseqF⟩ := hseqΛ bw hfacts.hbw (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H) N
    Acl (succKc r₀ D₀ H J N p Acl + 4 * p) hDm hN1
  obtain ⟨CGl, Cwl, Ca, Cg, m₀, -, hCg, hsetF⟩ := hsetΛ bw hfacts.hbw (succSchedD D₀ N p (H + 1))
    (succSchedR r₀ J H) N Acl (succKc r₀ D₀ H J N p Acl + 4 * p) hDm hN1
  refine ⟨(CGl, Cwl, Ca, Cg, max m₁ m₀), hCg, ?_⟩
  intro hr _ _ _ _ _ _ _ c hm hgeom hquietMargin CcT PZ aRep û hlift aZ aY hZ hY
  obtain ⟨-, -, -, hj, hdepth, hres, hres2, hlen, -, -⟩ := hgeom
  have hΛ1 : 1 ≤ Λ := le_trans (by norm_num) hfacts.hΛ
  have hband : IsOCBandChain c.D.α c.D.q c.D.Λ c.D.ζ c.D.term c.D.κ := by
    rw [c.hα, c.hq, c.hΛ, c.hζ, c.hterm]
    exact c.hband
  have hmt : c.m < c.D.term := by rw [c.hterm]; exact lt_of_le_of_lt c.hmn c.hnM
  have hj' : j₀ ≤ c.m := by rw [← c.hlevel]; exact hj
  have hentry : c.tA + 3 * ocTau c.D.α c.D.q c.D.Λ c.m ≤ c.tp := by
    rw [c.hα, c.hq, c.hΛ]
    exact le_trans c.hs₀ c.hprep.2.1
  have htp : c.tp ≤ c.tf := by
    have h1 : c.tp ≤ c.s₀ + 4 * ocTauPP c.D.α c.D.q c.D.Λ c.G.level := c.hprep.2.2.1
    rw [c.hα, c.hq, c.hΛ, c.hlevel] at h1
    exact le_trans h1 c.htf
  have hquietMargin' : Set.Icc (c.tp - ocTauP c.D.α c.D.q c.D.Λ c.m)
      (c.tp + ocTauP c.D.α c.D.q c.D.Λ c.m) ⊆ ocQuietTimes c.D.α c.D.q c.D.Λ c.D.ζ c.m := by
    rw [c.hα, c.hq, c.hΛ, c.hζ]
    exact hquietMargin
  have hCI : 0 ≤ CI := by
    obtain ⟨CIthr, Cwthr, hled⟩ := hfacts.ledger
    exact le_trans (le_trans zero_le_one hfacts.hCe) hled.1
  have hS : CI * c.D.eps c.m ^ min (ocDelta α q / 4) τe ≤ CI := by
    have hΛD : 1 ≤ c.D.Λ := by rw [c.hΛ]; exact hΛ1
    exact billCtx_ledgerPrice_le (ocDelta_pos_of_admissible hα₀ hq) hfacts.hτe hCI
      (Construction.Stream.ocEpsilon_pos hΛD).le (ocEpsilon_le_one hΛD c.m)
  have hR2 : FrameReconSeqAt (c.frame CcT PZ aRep û hlift aZ aY hZ hY) Acl (succKc r₀ D₀ H J N p Acl + 4 * p) :=
    hseqF hr c.D c.hα c.hq c.hΛ c.hζ c.hseq hband j₀ (c.frame CcT PZ aRep û hlift aZ aY hZ hY)
      c.law hφ₀ c.Mnat kI c.tA c.tf _ _ c.hinv rfl rfl c.hlevel
      (le_trans (le_max_left _ _) hm) hmt hj' hdepth hres hres2 hlen rfl hentry htp hquietMargin'
  exact ⟨hR2, _, _, _, _, _,
    hsetF hr c.D c.hα c.hq c.hΛ c.hζ c.hseq hband j₀ (c.frame CcT PZ aRep û hlift aZ aY hZ hY)
      c.law hφ₀ c.Mnat kI c.tA c.tf _ _ c.hinv rfl rfl c.hlevel
      (le_trans (le_max_right _ _) hm) hmt hj' hdepth hres hres2 hlen hR2 CI hS⟩

/-! Shared native window, agreement, family and high-order pulse for the covariance G form. -/

/-- The shared input, with all constants before the actual context and component carriers. -/
theorem covGInputs (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) : CovGInputsStatement α s q ζ := by
  refine ((reconSetting α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ).and
    ((succPrefix_retainedProductionBundle α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => 0)).and
      (succPrefix_reconFamily α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ))).imp ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ CQ Cpr hfacts x hx
  let mStar := max (max x.1.2.2.2.2 x.2.1.2) (max x.2.2 2)
  refine ⟨⟨x.1.1, x.1.2.1, x.1.2.2.1, mStar⟩, ?_⟩
  intro hr _ _ _ _ _ _ _ c hm hquietMargin CcT PZ aRep û hlift aZ aY hZ hY
  have hmset : x.1.2.2.2.2 ≤ c.m := (le_max_left _ _).trans ((le_max_left _ _).trans hm)
  have hmpk : x.2.1.2 ≤ c.m := (le_max_right _ _).trans ((le_max_left _ _).trans hm)
  have hmfam : x.2.2 ≤ c.m := (le_max_left _ _).trans ((le_max_right _ _).trans hm)
  have hm2 : 2 ≤ c.m := (le_max_right _ _).trans ((le_max_right _ _).trans hm)
  have hk15 := hfacts.sched.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hk0 : 0 + N + 2 * p ≤ Naux := by
    have := (le_max_right _ _).trans hk15
    omega
  have hgeom := (hx.2.1.2 hk0 c hmpk).1
  have hset := hx.1.2 c hmset hgeom hquietMargin CcT PZ aRep û hlift aZ aY hZ hY
  have hfam := hx.2.2 c hmfam CcT PZ aRep û hlift aZ aY hZ hY
  let F := c.frame CcT PZ aRep û hlift aZ aY hZ hY
  have hΛ1 : 1 ≤ Λ := (by norm_num : 1 ≤ 128).trans hfacts.hΛ
  have hΛD : 1 ≤ c.D.Λ := by rw [c.hΛ]; exact hΛ1
  have hζD : IsFastProfile c.D.ζ := by rw [c.hζ]; exact hζ
  have hν := c.kappa_pos hΛ1 hζ
  have hB := c.kappa_pred_pos hΛ1 hζ
  have hcs := cellScale_facts F hΛD hζD c.bandD c.m_le_term
  have hone : F.Mn.lenFactor = 1 := rfl
  refine ⟨⟨{
    window := ?_
    rho_pos := ?_
    B_pos := hB
    current_pos := hν
    mass_pos := c.mass_pos hq.1 hfacts.hΛ
    lambda := c.lambda_ge hfacts.hΛ
    chart_jets := ?_ }⟩, ⟨{
    one := hone
    cell_pos := hcs.1
    scale_eq := hcs.2
    seq_agree := ?_
    weight_eq := ?_ }⟩, hfam, ?_⟩
  · have he : F.tp + fTobs F = c.tf := by
      change F.tp + (F.tf - F.tp) = F.tf
      ring
    rw [he]
    exact c.tp_le_tf
  · exact Real.sqrt_pos.2 (mul_pos hB (Construction.Stream.ocTauPP_pos hΛD))
  · intro k t _ hwin j hj y
    have hℓ : 0 < ocEll c.D.q c.D.Λ c.m (c.D.κ c.m) :=
      div_pos (Construction.Stream.ocEpsilon_pos hΛD) (Real.sqrt_pos.2 hν)
    have ha := CycleComparison.Assembly.abs_sub_anchor_le c.D.α c.D.q hΛD c.m hℓ
      F.tp (F.tp + fTobs F) k hwin
    change _ ∧ _
    have hFm : (c.frame CcT PZ aRep û hlift aZ aY hZ hY).m = c.m := rfl
    simp only [CovGChart, CovGLabel, hFm, c.hα, c.hq, c.hΛ]
    exact CycleComparison.Charts.ocChart_window_jets α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ
      hfacts.hΛ c.D.Φ c.hseq c.m hm2 (c.D.hΦ (c.m - 1)) _ t
      (by simpa only [c.hα, c.hq, c.hΛ] using ha) j hj y
  · intro k hk
    exact seq_agree' F c.hinv.1 c.hlevel hone hΛD hζD c.bandD c.m_le_term
      (le_trans (by norm_num) hm2) hk
  · intro k hk t
    change c.G.fam.weight (oddSlotOf k) t = _
    rw [oddSlotOf_of_odd hk]
    exact c.weight_eq ⟨k, hk⟩ t
  · exact CovGNativePulse_of_setting F c.law Acl
      (succKc r₀ D₀ H J N p Acl + 4 * p) x.1.1 x.1.2.1 x.1.2.2.1 CI x.1.2.2.2.1
      hset.1 hset.2

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.Residual.FluxCancellation.CovFluxReg
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! Spatial regularity of the actual differential action of native coefficients. -/

/-- A finite differential coefficient action preserves the advertised spatial order and period. -/
theorem coefficient_regular {ι : Type} [Fintype ι] {h : ι → Type}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
    [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {K R : ℕ} {a b ρ C : ℝ} {π : ι → ℝ}
    {input target : ∀ v : ι, ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)}
    (P : CovTruncCoefficientData K R a b ρ C π input target)
    (v : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ContDiff ℝ (K : ℕ∞) (target v t) ∧ IsZ2Periodic (target v t) := by
  classical
  have he : target v t = fun x => ∑ u, ∑ r : Fin (R + 1), P.coeff v u r t x
      (WithLp.toLp 2 fun α : DerivativeWord2 r.val => orderedDerivative α (input u t) x) :=
    funext (P.action v t ht)
  rw [he]
  constructor
  · refine ContDiff.sum fun u _ => ContDiff.sum fun r _ => ?_
    refine (P.smooth v u r t ht).clm_apply ((contDiff_piLp 2).2 fun α => ?_)
    exact CycleComparison.Lift.orderedDerivative_contDiff α K (input u t)
      ((P.input_smooth u t ht).of_le (by exact_mod_cast
        (Nat.add_le_add_left (Nat.le_of_lt_succ r.isLt) K)))
  · intro z x
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun r _ => ?_
    rw [P.periodic v u r t ht z x]
    congr 1
    apply PiLp.ext
    intro α
    exact CycleComparison.Lift.orderedDerivative_periodic α (input u t)
      ((P.input_smooth u t ht).of_le (by exact_mod_cast
        ((Nat.le_of_lt_succ r.isLt).trans (Nat.le_add_left R K))))
      (P.input_periodic u t ht) z x


variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- Native coefficients supply both spatial properties of the actual glued grade sum. -/
theorem glued_regular (F : Frame D hr Dm b j₀) (law : BirthLaw)
    {Acl ell K : ℕ} {CG CW : ℕ → ℝ} {Ca Sb : ℝ}
    (p : CovGNativePulse F law Acl ell CG CW Ca Sb) (hA : CovGNativeAgreement F)
    (g : CovGNativeWindow F law) (hN : 1 ≤ F.N)
    (hK : K ≤ wKlift Dm F.depth F.N Acl ell + 1)
    (hfamily : CovGFamily F) (hSb : 0 ≤ Sb)
    (rs : Finset ℕ) (hrs : ∀ hh ∈ rs, hh ≤ F.depth)
    (f : ℝ → Vec 2 → ∀ v : CompIn F.G.comps, hr v.1.root)
    (hf : ∀ v, ∀ t ∈ Set.Icc F.tp (F.tp + fTobs F),
      ContDiff ℝ ((K + (F.N + Dm) + 1 : ℕ) : ℕ∞) (fun y => f t y v))
    (hp : ∀ v, ∀ t ∈ Set.Icc F.tp (F.tp + fTobs F), IsZ2Periodic (fun y => f t y v))
    (v : CompIn F.G.comps) (t : ℝ) (ht : t ∈ Set.Icc F.tp (F.tp + fTobs F)) :
    ContDiff ℝ (K : ℕ∞) (fun y => menuGluedMeanFlux F.Mn F.G F.m rs
      (Finset.Icc 2 (F.N + Dm)) F.CcT f t y v) ∧
    IsZ2Periodic (fun y => menuGluedMeanFlux F.Mn F.G F.m rs
      (Finset.Icc 2 (F.N + Dm)) F.CcT f t y v) := by
  obtain ⟨P⟩ := CovGNativeGrade_data F law p hA K hK g hN hfamily hSb rs hrs f hf hp
  obtain ⟨hc, hp⟩ := coefficient_regular P v t ht
  exact ⟨PiLp.contDiff_ofLp.comp hc, fun z y => congrArg WithLp.ofLp (hp z y)⟩

/-- Spatial regularity of the covariance-G flux from the shared native slot-lift input. -/
theorem native_regular (F : Frame D hr Dm b j₀) (law : BirthLaw)
    {Acl ell K : ℕ} {CG CW : ℕ → ℝ} {Ca Sb : ℝ}
    (p : CovGNativePulse F law Acl ell CG CW Ca Sb) (hA : CovGNativeAgreement F)
    (g : CovGNativeWindow F law) (hN : 1 ≤ F.N) (hDm : 1 ≤ Dm)
    (hK : K ≤ wKlift Dm F.depth F.N Acl ell + 1)
    (hfamily : CovGFamily F) (hSb : 0 ≤ Sb)
    (hf : ∀ v, ∀ t ∈ Set.Icc F.tp F.tf,
      ContDiff ℝ ((K + (F.N + Dm) + 1 + 2 * F.p : ℕ) : ℕ∞) (fun y => F.aZ t y v))
    (hp : ∀ v, ∀ t ∈ Set.Icc F.tp F.tf, IsZ2Periodic (fun y => F.aZ t y v))
    (v : CompIn F.G.comps) (t : ℝ) (ht : t ∈ Set.Icc F.tp F.tf) :
    ContDiff ℝ (K : ℕ∞) (fun y => menuGFlux F.Mn F.G F.m F.N F.p F.depth F.CcT F.aZ v t y) ∧
    IsZ2Periodic (fun y => menuGFlux F.Mn F.G F.m F.N F.p F.depth F.CcT F.aZ v t y) := by
  classical
  let a := menuCovPRep F.Mn D F.m F.p F.aZ
  have he : F.tp + fTobs F = F.tf := by unfold fTobs; ring
  have ha : ∀ u, ∀ s ∈ Set.Icc F.tp (F.tp + fTobs F),
      ContDiff ℝ ((K + (F.N + Dm) + 1 : ℕ) : ℕ∞) (fun y => a s y u) := by
    intro u s hs
    rw [he] at hs
    exact covPolyP_contDiff _ F.p _ (hf u s hs)
  have hpa : ∀ u, ∀ s ∈ Set.Icc F.tp (F.tp + fTobs F), IsZ2Periodic (fun y => a s y u) := by
    intro u s hs
    rw [he] at hs
    exact covTruncReg_covPolyP_periodic _ F.p _ (hf u s hs) (hp u s hs) (by omega)
  have ht' : t ∈ Set.Icc F.tp (F.tp + fTobs F) := he.symm ▸ ht
  have hm := glued_regular F law p hA g hN hK hfamily hSb (Finset.Icc 1 F.depth)
    (fun _ hh => (Finset.mem_Icc.mp hh).2) a ha hpa v t ht'
  have hd := glued_regular F law p hA g hN hK hfamily hSb {0}
    (fun _ hh => by simp only [Finset.mem_singleton] at hh; subst hh; exact Nat.zero_le _)
    a ha hpa v t ht'
  have htail : (fun y => menuGluedMeanFlux F.Mn F.G F.m {0}
      (Finset.Icc 2 (F.N + Dm)) F.CcT a t y v) =
      fun y => menuGluedMeanFlux F.Mn F.G F.m {0}
        (Finset.Icc 2 (F.N + 1)) F.CcT a t y v := by
    funext y
    exact CovGNativeDiag_tail F law p hA g hN hDm a t
      (contDiff_pi.mpr fun u => (ha u t ht').of_le (by exact_mod_cast (by omega :
        F.N + Dm ≤ K + (F.N + Dm) + 1))) ht' y v
  rw [htail] at hd
  have hbv : ContDiff ℝ (⊤ : ℕ∞) (streamVel (D.Φ (F.m - 1)) t) :=
    ((AVenhance.Infra.Construction.smoothPeriodic_streamVel (D.hΦ (F.m - 1))).smooth).comp
      (contDiff_const.prodMk contDiff_id)
  have hpb : IsZ2Periodic (streamVel (D.Φ (F.m - 1)) t) :=
    fun z y => by simpa using (AVenhance.Infra.Construction.smoothPeriodic_streamVel
      (D.hΦ (F.m - 1))).periodic 0 z t y
  have hc := covTruncReg_comm_contDiff _ hbv (menuCovPrimitive D F.Mn F.m t) F.p K _
    (by omega) (hf v t ht)
  have hcp := covTruncReg_comm_periodic _ hbv hpb (menuCovPrimitive D F.Mn F.m t) F.p _
    (by omega) (hf v t ht) (hp v t ht)
  have hag : ContDiff ℝ ((K + 1 : ℕ) : ℕ∞) (fun y => a t y v) :=
    (ha v t ht').of_le (by exact_mod_cast (by omega : K + 1 ≤ K + (F.N + Dm) + 1))
  have hgr : ContDiff ℝ (K : ℕ∞) (fun y => fun j => ∑ l : Fin 2,
      ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m) t j l • gradE (fun z => a t z v) y l) :=
    contDiff_pi.mpr fun _ => ContDiff.sum fun l _ =>
      ContDiff.smul contDiff_const (gradE_contDiff K hag l)
  have hgp : IsZ2Periodic (fun y => fun j => ∑ l : Fin 2,
      ocRefFlux D.α D.q D.Λ D.ζ F.m (D.κ F.m) t j l • gradE (fun z => a t z v) y l) := by
    intro z y
    funext j
    exact Finset.sum_congr rfl fun l _ => congrArg (fun w => _ • w)
      (covTruncReg_gradE_periodic (hag.differentiable (by simp)) (hpa v t ht') l z y)
  change ContDiff ℝ (K : ℕ∞) _ ∧ IsZ2Periodic _
  unfold menuGFlux menuTemporalFlux menuDiagFluxPhys menuMeanFluxE
  refine ⟨(hc.sub (hd.1.sub hgr)).sub hm.1, ?_⟩
  intro z y
  have hc' := hcp z y
  simp only [Finset.sum_apply, Pi.smul_apply] at hc'
  exact congrArg₂ (· - ·)
    (congrArg₂ (· - ·) hc' (congrArg₂ (· - ·) (hd.2 z y) (hgp z y))) (hm.2 z y)

end AVRegularity.Construction.Residual.Presentation.Cascade
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.Construction.Residual.Presentation.Cascade

/-! The regularity and periodicity part of the bill covariance-G form. -/

/-- The order floor supplies the finite scalar input order needed by the native coefficients. -/
theorem input_floor {r₀ D₀ H J N p Acl Lc Naux : ℕ}
    (h : succReconFloor r₀ D₀ H J N p Acl Lc ≤ Naux) :
    succKc r₀ D₀ H J N p Acl + 4 * p + (N + succSchedD D₀ N p (H + 1)) + 1 + 2 * p ≤ Naux := by
  have hc := wKcFloor_le (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H) N Acl
  have hm := le_max_left (succSchedD D₀ N p (H + 1) + Lc + N + 6 * p + 4)
    ((succSchedR r₀ J H + 3) * (N + succSchedD D₀ N p (H + 1) + 12) + 2 * p)
  change wKcFloor _ _ _ _ _ + 4 * p + (N + succSchedD D₀ N p (H + 1)) + 1 + 2 * p ≤ Naux
  unfold succReconFloor at h
  omega

/-- High-order native settings cover their own output order. -/
theorem lift_order (Dm depth N Acl K : ℕ) : K ≤ wKlift Dm depth N Acl K + 1 := by
  unfold wKlift wKmax
  omega

/-- Part 1, with exactly the prefix and its context premises. -/
theorem covGPart1 (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) : CovGPartStatement α s q ζ 1 := by
  refine (covGInputs α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ).imp ?_
  intro Λ φ₀ hφ₀ bw Q T₀ Ce τe kS r₀ D₀ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ
    σ₀ a σ kI CI Cw j₀ CQ Cpr hfacts x hx
  refine ⟨(0, x.mStar), ?_⟩
  intro hr _ _ _ _ _ _ _ c hm hquietMargin CcT PZ aRep û hlift aZ aY hZ hY
  obtain ⟨⟨g⟩, ⟨hA⟩, hfamily, ⟨pulse⟩⟩ := hx c hm hquietMargin CcT PZ aRep û hlift aZ aY hZ hY
  let F := c.frame CcT PZ aRep û hlift aZ aY hZ hY
  have hDm : 1 ≤ succSchedD D₀ N p (H + 1) :=
    (by norm_num : 1 ≤ 2).trans
      (Construction.Preservation.Buffer.preparation_schedule_order_ge_two D₀ N p H)
  have hN : 1 ≤ F.N := (by norm_num : 1 ≤ 2).trans (succSchedule_two_le_N hfacts.sched)
  have hCI : 0 ≤ CI := by
    obtain ⟨CIthr, Cwthr, hled⟩ := hfacts.ledger
    exact (zero_le_one.trans hfacts.hCe).trans hled.1
  have hfloor := input_floor hfacts.recon
  simp only [CovGFrameAt, Fin.isValue, ↓reduceIte]
  intro v t ht
  apply native_regular F c.law pulse hA g hN hDm
    (lift_order _ _ _ _ _) hfamily hCI
  · intro u s hs
    have hh : ContDiff ℝ (Naux : ℕ∞) (fun y => aZ s y u) := by
      exact_mod_cast (hZ u s hs).2.1
    exact hh.of_le (by exact_mod_cast hfloor)
  · intro u s hs
    exact (hZ u s hs).2.2.1
  · exact ht

end AVRegularity.Construction.Residual.Presentation.Cascade
end
end
end
