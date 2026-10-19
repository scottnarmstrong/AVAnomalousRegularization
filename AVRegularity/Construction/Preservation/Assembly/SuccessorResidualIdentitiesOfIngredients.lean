-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Stream.NextAdmissible
public import AVRegularity.Construction.Preservation.Assembly.PreparationJointInputs

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Assembly

/-! Exact seed discharge assembly: admissible constant changes and seed repricing. -/

/-- All non-price invariant clauses survive admissible changes of constants. The separate
kernel-price premise is deliberate: increasing derivative constants increases that price. -/
def StageInvariantConstantsMonoStatement : Prop :=
  ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
    [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)],
  ∀ (D : OCData) (Dm : ℕ) (bw : ℝ) (j₀ : ℕ), 0 < bw → (∀ i, 0 < D.eps i) →
  ∀ (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (M : ℕ) (kS thr kI : InvConsts)
    (H J N p nk Kres Lpr Lc Lf : ℕ) (σ₀ δ q c : ℝ),
    IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ δ q c →
    0 ≤ kS.c₀ → 0 ≤ kS.cr →
  ∀ (G : GenStage D hr Dm bw j₀) (tS tf S θ S' θ' : ℝ),
    D.eps G.level ≤ 1 → D.eps (G.level - 1) ≤ 1 →
    IsStageInvariant law P seedK freshK φ₀ hφ₀ M kS tS tf S θ G → S ≤ S' →
    (∀ kk ≤ kI.Ks, ∀ w : CompIn G.comps → ℝ, (w = fun _ => 1) ∨ w = G.marker law →
      SchurBound θ' (kernelSchurMatrix (ι := CompIn G.comps) (h := fun v => hr v.1.root)
        (Γ := G.fam.Γ) (G := fun _ u _ => hr u.1.root)
        (D.kap G.level) (rhoStar D kI.c₀ G.level) (fun v => G.mass law v / w v ^ 2) kk Dm
        tS tf kI.cker (fun v u γ => (G.kernelOf P seedK freshK v u γ).width)
        (fun _ u _ => ContinuousLinearMap.id ℝ (hr u.1.root))
        (fun v u γ d => G.physCoeff v u γ d.1))) →
    IsStageInvariant law P seedK freshK φ₀ hφ₀ M kI tS tf S' θ' G

/-- Seed ledger decay and its newly priced kernel Schur sums, with the
choice order of the seed invariant. No successor or fresh-birth ledger estimate enters this statement. -/
def SeedLedgerDecayConversionStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 → IsAdmissibleQ α s q → IsFastProfile ζ →
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ →
    ∀ (Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ : ℕ), 1 ≤ Ce → 0 < τe →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → 0 < kS.σf → 0 < kS.lamC →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad _sX _sZ : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min kS.σf (ocDelta α q + σ₀)) kS.lamC D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
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
      [∀ r, CompleteSpace (hr r)]
      (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
      mStar ≤ n → n < M →
      D.eps n ≤ 1 ∧ D.eps (n - 1) ≤ 1 ∧
      Ce * D.eps n ^ τe ≤ CI * D.eps n ^ min (ocDelta α q / 4) τe ∧
      (∀ kk ≤ kI.Ks, ∀ w : CompIn seed.comps → ℝ, (w = fun _ => 1) ∨ w = seed.marker law →
        SchurBound (CI * D.eps (n - 1) ^ (q * min (ocDelta α q / 4) τe))
          (kernelSchurMatrix (ι := CompIn seed.comps) (h := fun v => hr v.1.root)
            (Γ := seed.fam.Γ) (G := fun _ u _ => hr u.1.root)
            (D.kap seed.level) (rhoStar D kI.c₀ seed.level)
            (fun v => seed.mass law v / w v ^ 2) kk (succSchedD D₀ N p (H + 1)) tS tf kI.cker
            (fun v u γ => (seed.kernelOf (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
              seedK freshK v u γ).width)
            (fun _ u _ => ContinuousLinearMap.id ℝ (hr u.1.root))
            (fun v u γ d => seed.physCoeff v u γ d.1)))

theorem seed_invariant_discharge_of_ingredients (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (hmono : StageInvariantConstantsMonoStatement)
    (hdecay : SeedLedgerDecayConversionStatement α s q ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ →
    ∀ (Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ : ℕ), 1 ≤ Ce → 0 < τe →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → 0 < kS.σf → 0 < kS.lamC →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad _sX _sZ : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min kS.σf (ocDelta α q + σ₀)) kS.lamC D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
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
      [∀ r, CompleteSpace (hr r)]
      (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
      mStar ≤ n → n < M →
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tS tf (CI * D.eps n ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (n - 1) ^ (q * min (ocDelta α q / 4) τe)) seed := by
  obtain ⟨Λ₀, hΛ₀, hΛ⟩ := hdecay hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛle
  obtain ⟨c₀max, hc₀max, hc⟩ := hΛ Λ hΛle
  refine ⟨c₀max, hc₀max, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφnonneg hφmass hφsupport bw hbw hbwmax Q T₀ hQ hT
    Ce τe kS r₀ D₀ hCe hτ hcS hcSmax hcr hcrmax hσf hlam H J N p nk Lc Lf Lpr Acl Naux Nout
    Kres npad sX sZ σ₀ a σ hsched haux hres halloc
  obtain ⟨thr, CH, Υ, hCH, hΥ, ht⟩ := hc φ₀ hφ₀ hφsmooth hφnonneg hφmass hφsupport
    bw hbw hbwmax Q T₀ hQ hT Ce τe kS r₀ D₀ hCe hτ hcS hcSmax hcr hcrmax hσf hlam
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched haux hres halloc
  refine ⟨thr, CH, Υ, hCH, hΥ, ?_⟩
  intro kI hadm
  obtain ⟨CIthr, Cwthr, hi⟩ := ht kI hadm
  refine ⟨CIthr, Cwthr, ?_⟩
  intro CI Cw j₀ hled hstart
  obtain ⟨mStar, hm⟩ := hi CI Cw j₀ hled hstart
  refine ⟨mStar, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw hr _ _ _ _ _ _
    seedK freshK hfresh seed n tS tf hseed hn hnM
  obtain ⟨he, hE, hS, hprice⟩ := hm D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat
    law hlaw seedK freshK hfresh seed n tS tf hseed hn hnM
  have hΛD : 1 ≤ D.Λ := by rw [hDΛ]; omega
  have hε : ∀ i, 0 < D.eps i := fun _ => Construction.Stream.ocEpsilon_pos hΛD
  have hI := hseed.2.2.2.2.2.2.2.1
  apply hmono hr D (succSchedD D₀ N p (H + 1)) bw j₀ hbw hε law
    (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀ Mnat
    kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) hadm hcS.le hcr.le
    seed tS tf (Ce * D.eps n ^ τe) (Ce * D.eps (n - 1) ^ (D.q * τe))
    (CI * D.eps n ^ min (ocDelta α q / 4) τe)
    (CI * D.eps (n - 1) ^ (q * min (ocDelta α q / 4) τe))
  · simpa only [hseed.1] using he
  · simpa only [hseed.1] using hE
  · exact hI
  · exact hS
  · exact hprice

/-! The two distinct frontier estimates share the prefix and arbitrary
kernel-lift witnesses. The split is by the two actual discarded-row sets.
The interfaces use explicit lift floors and nontrivial roots.
Empty component families remain allowed in these signatures because nontriviality is
imposed on root spaces. Negative CQ or Cpr are not excluded: the common-preparation premise
retains its actual quantitative content.
-/

/-- Data-dependent part of FrontierProductionStatement; all preceding choices are fixed. -/
def FrontierProductionDataStatement (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw Ce τe : ℝ) (kS : InvConsts)
    (r₀ D₀ H J N p nk Naux Nout Kres npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ C : ℝ) (mStar : ℕ) (grade : Bool) : Prop :=
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
    ∀ k ≤ Kres,
    ∀ (Y0 : ∀ v' : CompIn (G'.retained m H J).comps, TorusHk k (hr v'.1.root))
      (Y : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk k (hr v.1.root))
      (Yw : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk (k + 1) (hr v.1.root))
      (Yk : ∀ v u (_ : (G'.retained m H J).fam.Γ v u), ℝ → TorusHk (k + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root)),
      IsRetainedTrace G (G'.retained m H J) m p tp (Preg f) Y0 →
      (G'.retained m H J).IsRegSolution (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        seedK freshK φ₀ hφ₀ (D.κ (m - 1)) (streamVel (D.Φ (m - 1))) k tp tf Y0
        (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk →
    ∀ yom : ∀ v u (_ : G'.fam.Γ v u), ℝ → TorusHk (k + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root),
      (∀ v u (γ : G'.fam.Γ v u) (hu : IsRetained m H J u.1),
        ∀ᵐ s ∂(volume.restrict (Set.Icc tp tf)),
          (yom v u γ s).val (valueIndex2 (k + succSchedD D₀ N p (H + 1) - 1)) =
            G'.sysS (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀ v u γ s
              ((Yw ⟨u.1, Finset.mem_filter.2 ⟨u.2, hu⟩⟩ s).val (valueIndex2 (k + 1)))) →
    ∀ (sel : Comp → Prop) (expo : ℝ),
      (if grade then ((sel = fun c => compGrade c = H + 1) ∧ expo = (succEta0 α q s) / 8 * succSigmaH q H) else ((sel = fun c => compGrade c ≤ H ∧ (compWord m c).length = J + 1) ∧
          expo = succTheta1 α q s σ₀ (succDstar D₀ N p H) +
            J * succTheta2 α q s σ₀ (succDstar D₀ N p H))) →
    ∃ RF : ∀ v : CompIn G.comps, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => hr v.1.root)),
      (∀ v, ∀ t ∈ Set.Icc tp tf,
        (RF v t).toFunction.jet (valueIndex2 k) =ᵐ[volume.restrict AVenhance.unitCube]
          readoutFlux m (D.eps (m - 1)) (succEta0 α q s) sel
            (omittedFlux G' k (IsRetained m H J) yom) v t) ∧
      (D.κ (m - 1))⁻¹ * ∫ t in Set.Icc tp tf,
          massNormSq (E := fun v : CompIn G.comps => PiLp 2 (fun _ : Fin 2 => hr v.1.root))
            (K := fun _ => k) (rhoEnh D kI.cr m) (G.mass law) (fun v => (RF v t).val)
        ≤ (C * D.eps (m - 1) ^ expo *
            weightedNorm (rhoEnh D kI.cr m) ((G'.retained m H J).mass law) ((G'.retained m H J).marker law) Y0) ^ 2

/-- Uniform frontier production, selecting grade or word-length rows. -/
def FrontierProductionStatement (α s q : ℝ) (ζ : ℝ → ℝ) (grade : Bool) : Prop :=
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
    ∀ CQ Cpr : ℝ, ∃ (C : ℝ) (mStar : ℕ),
    FrontierProductionDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout Kres npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ C mStar grade

/-- The marked dissipative estimate for discarded grade-H+1 rows.
Empty families have zero flux, and an edgeless seed still has fresh letters. -/
def GradeFrontierStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  FrontierProductionStatement α s q ζ true

/-- The finite word-length response recurrence through J+1, with original kernels.
Empty families have zero response, and an edgeless seed retains its diagonal word chain. -/
def LengthFrontierStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  FrontierProductionStatement α s q ζ false

/-- Literal conclusion after the uniform choices. -/
def SuccessorFrontierDataStatement (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw Ce τe : ℝ) (kS : InvConsts)
    (r₀ D₀ H J N p nk Naux Nout Kres npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ C : ℝ) (mStar : ℕ) : Prop :=
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
    ∀ k ≤ Kres,
    ∀ (Y0 : ∀ v' : CompIn (G'.retained m H J).comps, TorusHk k (hr v'.1.root))
      (Y : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk k (hr v.1.root))
      (Yw : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk (k + 1) (hr v.1.root))
      (Yk : ∀ v u (_ : (G'.retained m H J).fam.Γ v u), ℝ → TorusHk (k + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root)),
      IsRetainedTrace G (G'.retained m H J) m p tp (Preg f) Y0 →
      (G'.retained m H J).IsRegSolution (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        seedK freshK φ₀ hφ₀ (D.κ (m - 1)) (streamVel (D.Φ (m - 1))) k tp tf Y0
        (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk →
    ∀ yom : ∀ v u (_ : G'.fam.Γ v u), ℝ → TorusHk (k + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root),
      (∀ v u (γ : G'.fam.Γ v u) (hu : IsRetained m H J u.1),
        ∀ᵐ s ∂(volume.restrict (Set.Icc tp tf)),
          (yom v u γ s).val (valueIndex2 (k + succSchedD D₀ N p (H + 1) - 1)) =
            G'.sysS (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀ v u γ s
              ((Yw ⟨u.1, Finset.mem_filter.2 ⟨u.2, hu⟩⟩ s).val (valueIndex2 (k + 1)))) →
    ∀ (sel : Comp → Prop) (expo : ℝ),
      ((sel = fun c => compGrade c = H + 1) ∧ expo = (succEta0 α q s) / 8 * succSigmaH q H) ∨
        ((sel = fun c => compGrade c ≤ H ∧ (compWord m c).length = J + 1) ∧
          expo = succTheta1 α q s σ₀ (succDstar D₀ N p H) +
            J * succTheta2 α q s σ₀ (succDstar D₀ N p H)) →
    ∃ RF : ∀ v : CompIn G.comps, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => hr v.1.root)),
      (∀ v, ∀ t ∈ Set.Icc tp tf,
        (RF v t).toFunction.jet (valueIndex2 k) =ᵐ[volume.restrict AVenhance.unitCube]
          readoutFlux m (D.eps (m - 1)) (succEta0 α q s) sel
            (omittedFlux G' k (IsRetained m H J) yom) v t) ∧
      (D.κ (m - 1))⁻¹ * ∫ t in Set.Icc tp tf,
          massNormSq (E := fun v : CompIn G.comps => PiLp 2 (fun _ : Fin 2 => hr v.1.root))
            (K := fun _ => k) (rhoEnh D kI.cr m) (G.mass law) (fun v => (RF v t).val)
        ≤ (C * D.eps (m - 1) ^ expo *
            weightedNorm (rhoEnh D kI.cr m) ((G'.retained m H J).mass law) ((G'.retained m H J).marker law) Y0) ^ 2

/-- Literal conclusion, with the data-dependent part named. -/
def SuccessorFrontierStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
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
    ∀ CQ Cpr : ℝ, ∃ (C : ℝ) (mStar : ℕ),
    SuccessorFrontierDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout Kres npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ C mStar

/-! The retained stage certificate ingredient and the analytic bundle derived from it.
Constants in both interfaces are chosen before the data and fields. The bundle is an
internal assembly interface, not an external hypothesis of the full-lift assembly. -/

def RetainedProductionBundleStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
    ∀ Λbase : ℕ, 128 ≤ Λbase → ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ Λbase ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
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
    ∀ CQ Cpr : ℝ, ∀ mExist mEnergy : ℕ, 2 ≤ mExist → 2 ≤ mEnergy →
    ∃ (Cread : ℝ) (mStar : ℕ), 0 ≤ Cread ∧
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
    IncomingLiftGeometryStatement G kI (succSchedR r₀ J H) mExist mEnergy ∧
      RetainedHigherValuesStatement (G'.retained m H J) Naux tp tf Y ∧
      RetainedReadoutBudgetStatement law G (G'.retained m H J) m p Naux N k hk
        (succEta0 α q s) kI.cr tp tf Cread Ain Y Yw

/-- The retained certificate conjunction under the verbatim stage-invariant propagation
binder prefix. This is the sole external ingredient of the revised full-lift assembly. -/
def RetainedStageCertificatesStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
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
      let Gr := G'.retained m H J
      Gr.IsNatural Mnat ∧ Gr.IsShiftInvariant ∧ Gr.IsSlotTransverse ∧
        Gr.IsContextCertified kI ∧
        markedLedger (Gr.mass law) (Gr.marker law) Gr.fam ≤
          CI * D.eps (m - 1) ^ min (ocDelta α q / 4) τe ∧
        (∀ v u (γ : Gr.fam.Γ v u),
          (Gr.kernelOf (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK
            v u γ).width = (Gr.fam.identity v u γ).record.width ∧
          ∀ ρ : ℝ, 0 < ρ → IsSpatialRegularizerTorus ρ 0
            (succSchedD D₀ N p (H + 1)) (tA + 3 * ocTau α q Λ m) tf kI.cker
            (Gr.kernelOf (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK
              v u γ).width
            (Gr.sysS (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK
              φ₀ hφ₀ v u γ))

/-! A named proposition for the exact statement, used to separate statement elaboration from assembly. -/

def SuccessorFullLiftBoundStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
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
    FullLiftClauses law G (G'.retained m H J) m p Naux N (succSchedR r₀ J H) sX sZ k hk (succEta0 α q s) kI.c₀ kI.cr tp tf Ck Ain Y Yw

/-! Exact frontier assembly with common choices for the two discarded-row mechanisms. -/

theorem successor_frontier_bounds_of_ingredients_core (α s q : ℝ) (ζ : ℝ → ℝ)
    (ha0 : GradeFrontierStatement α s q ζ) (hb0 : LengthFrontierStatement α s q ζ) :
    SuccessorFrontierStatement α s q ζ := by
  classical
  obtain ⟨Λa, hΛa, ha⟩ := ha0
  obtain ⟨Λb, hΛb, hb⟩ := hb0
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
  obtain ⟨Ca, ma, ha⟩ := ha CI Cw j₀ hLa (IsCarrierStart.mono hA hT
    (le_max_left _ _) (le_max_left _ _) (zero_le_one.trans hCHa) hΥa.le hstart) CQ Cpr
  obtain ⟨Cb, mb, hb⟩ := hb CI Cw j₀ hLb (IsCarrierStart.mono hA hT
    (le_max_right _ _) (le_max_right _ _) (zero_le_one.trans hCHb) hΥb.le hstart) CQ Cpr
  let C := |Ca| + |Cb| + 1
  have hCa : |Ca| ≤ C := by dsimp [C]; linarith only [abs_nonneg Cb]
  have hCb : |Cb| ≤ C := by dsimp [C]; linarith only [abs_nonneg Ca]
  refine ⟨C, max ma mb, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA s₀ htA hs₀ htf hT₀ G G' hcascade hlevel hG hactual
    tp Preg hprep f Ain hAin k hk Y0 Y Yw Yk htrace hsol yom hyom sel expo hsel
  have hE : 0 ≤ D.eps (m - 1) := by
    rw [OCData.eps, hDq, hDΛ]
    exact (Construction.Stream.ocEpsilon_pos (by omega)).le
  rcases hsel with hsel | hsel
  · obtain ⟨RF, hRF, hbound⟩ := ha D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
      seedK freshK hfresh seed n tS tf hseed m (by omega) hn hnM
      tA s₀ htA hs₀ htf hT₀ G G' hcascade hlevel hG hactual
      tp Preg hprep f Ain hAin k hk Y0 Y Yw Yk htrace hsol yom hyom sel expo (by simpa using hsel)
    refine ⟨RF, hRF, hbound.trans ?_⟩
    simpa only [mul_assoc, weightedNorm] using squared_budget_mono hCa
      (mul_nonneg (Real.rpow_nonneg hE expo) (Real.sqrt_nonneg _))
  · obtain ⟨RF, hRF, hbound⟩ := hb D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
      seedK freshK hfresh seed n tS tf hseed m (by omega) hn hnM
      tA s₀ htA hs₀ htf hT₀ G G' hcascade hlevel hG hactual
      tp Preg hprep f Ain hAin k hk Y0 Y Yw Yk htrace hsol yom hyom sel expo (by simpa using hsel)
    refine ⟨RF, hRF, hbound.trans ?_⟩
    simpa only [mul_assoc, weightedNorm] using squared_budget_mono hCb
      (mul_nonneg (Real.rpow_nonneg hE expo) (Real.sqrt_nonneg _))

theorem successor_frontier_bounds_of_ingredients (α s q : ℝ) (ζ : ℝ → ℝ)
    (ha0 : GradeFrontierStatement α s q ζ) (hb0 : LengthFrontierStatement α s q ζ) :
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
    ∀ CQ Cpr : ℝ, ∃ (C : ℝ) (mStar : ℕ),
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
    ∀ k ≤ Kres,
    ∀ (Y0 : ∀ v' : CompIn (G'.retained m H J).comps, TorusHk k (hr v'.1.root))
      (Y : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk k (hr v.1.root))
      (Yw : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk (k + 1) (hr v.1.root))
      (Yk : ∀ v u (_ : (G'.retained m H J).fam.Γ v u), ℝ → TorusHk (k + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root)),
      IsRetainedTrace G (G'.retained m H J) m p tp (Preg f) Y0 →
      (G'.retained m H J).IsRegSolution (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        seedK freshK φ₀ hφ₀ (D.κ (m - 1)) (streamVel (D.Φ (m - 1))) k tp tf Y0
        (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk →
    ∀ yom : ∀ v u (_ : G'.fam.Γ v u), ℝ → TorusHk (k + succSchedD D₀ N p (H + 1) - 1) (hr u.1.root),
      (∀ v u (γ : G'.fam.Γ v u) (hu : IsRetained m H J u.1),
        ∀ᵐ s ∂(volume.restrict (Set.Icc tp tf)),
          (yom v u γ s).val (valueIndex2 (k + succSchedD D₀ N p (H + 1) - 1)) =
            G'.sysS (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀ v u γ s
              ((Yw ⟨u.1, Finset.mem_filter.2 ⟨u.2, hu⟩⟩ s).val (valueIndex2 (k + 1)))) →
    ∀ (sel : Comp → Prop) (expo : ℝ),
      ((sel = fun c => compGrade c = H + 1) ∧ expo = (succEta0 α q s) / 8 * succSigmaH q H) ∨
        ((sel = fun c => compGrade c ≤ H ∧ (compWord m c).length = J + 1) ∧
          expo = succTheta1 α q s σ₀ (succDstar D₀ N p H) +
            J * succTheta2 α q s σ₀ (succDstar D₀ N p H)) →
    ∃ RF : ∀ v : CompIn G.comps, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => hr v.1.root)),
      (∀ v, ∀ t ∈ Set.Icc tp tf,
        (RF v t).toFunction.jet (valueIndex2 k) =ᵐ[volume.restrict AVenhance.unitCube]
          readoutFlux m (D.eps (m - 1)) (succEta0 α q s) sel
            (omittedFlux G' k (IsRetained m H J) yom) v t) ∧
      (D.κ (m - 1))⁻¹ * ∫ t in Set.Icc tp tf,
          massNormSq (E := fun v : CompIn G.comps => PiLp 2 (fun _ : Fin 2 => hr v.1.root))
            (K := fun _ => k) (rhoEnh D kI.cr m) (G.mass law) (fun v => (RF v t).val)
        ≤ (C * D.eps (m - 1) ^ expo *
            weightedNorm (rhoEnh D kI.cr m) ((G'.retained m H J).mass law) ((G'.retained m H J).marker law) Y0) ^ 2 :=
  successor_frontier_bounds_of_ingredients_core α s q ζ ha0 hb0

/-! Exact successor residual identities from the retained readout weak equation and
its covariance/native-lift transport. Derivative witnesses are chosen jointly for all tests.
The two analytic ingredients enter as hypotheses.
The interfaces use explicit lift floors and nontrivial roots.
Empty component families remain allowed in these signatures because nontriviality is
imposed on root spaces. Negative CQ or Cpr are not excluded: the common-preparation premise
retains its actual quantitative content.
-/

/-- Data-dependent residual clauses with all earlier choices fixed. -/
def ResidualDataStatement (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ)
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
          (fun s' x => -(toFluxL (covPolyQ (covPrimitive D m s') p
              (fun y => gFlux G m N p (succSchedR r₀ J H) CcT aZ v s' y) x) +
            upsilonFlux (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ G G' (G'.retained m H J) m H J (D.eps (m - 1)) (succEta0 α q s) aZ aY v s' x))
          (fun _ _ => 0))
      (    ∃ dRep dUh : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root,
      IsTimeDerivRep (Set.Icc tp tf) aRep dRep ∧
      IsTimeDerivRep (Set.Icc tp tf) (liftedRep G m N (succSchedR r₀ J H) CcT aRep) dUh ∧
    ∀ v : CompIn G.comps, ∀ t ∈ Set.Icc tp tf, ∀ φ : Vec 2 → hr v.1.root,
      ContDiff ℝ (⊤ : ℕ∞) φ → IsZ2Periodic φ →
        CoupledWeakIdentity (volume.restrict AVenhance.unitCube) (D.κ (m - 1)) tp t
          (streamVel (D.Φ (m - 1))) (fun x => aRep t x v) (fun x => aRep tp x v) φ
          (fun j x => gradE φ x j) (fun s' j x => gradE (fun y => aRep s' y v) x j)
          (fun s' x => toFluxL (macroFlux G m N (succSchedR r₀ J H) CcT aRep v s' x))
          (fun s' x => toFluxL (meanFluxF G m N p (succSchedR r₀ J H) CcT aZ
            (fun w s'' y => upsilonFlux (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ G G' (G'.retained m H J) m H J (D.eps (m - 1)) (succEta0 α q s)
              aZ aY w s'' y) v s' x))
          (fun _ _ => 0) ∧
        CoupledWeakIdentity (volume.restrict AVenhance.unitCube) (D.κ m) tp t
          (streamVel (D.Φ m)) (fun x => liftedRep G m N (succSchedR r₀ J H) CcT aRep t x v)
          (fun x => liftedRep G m N (succSchedR r₀ J H) CcT aRep tp x v) φ (fun j x => gradE φ x j)
          (fun s' j x => gradE (fun y => liftedRep G m N (succSchedR r₀ J H) CcT aRep s' y v) x j)
          (fun s' x => coeffFluxOn (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ G .kernel
            (liftedRep G m N (succSchedR r₀ J H) CcT aRep) v s' x)
          (fun s' x => fineFluxF (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ G
            (liftedRep G m N (succSchedR r₀ J H) CcT aRep) v s' x)
          (fun s' x => liftedRep G m N (succSchedR r₀ J H) CcT (fun s'' y w => divE (fun y' =>
              meanFluxF G m N p (succSchedR r₀ J H) CcT aZ
                (fun w' s''' y'' => upsilonFlux (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ G G' (G'.retained m H J) m H J (D.eps (m - 1))
                  (succEta0 α q s) aZ aY w' s''' y'') w s'' y') y) s' x v +
            physRes (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ G m N (succSchedR r₀ J H) CcT aRep dRep dUh v s' x))
      (    ∃ dRep dUh : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root,
      IsTimeDerivRep (Set.Icc tp tf) aRep dRep ∧
      IsTimeDerivRep (Set.Icc tp tf) (liftedRep G m N (succSchedR r₀ J H) CcT aRep) dUh ∧
    ∀ v : CompIn G.comps, ∀ t ∈ Set.Icc tp tf, ∀ φ : Vec 2 → hr v.1.root,
      ContDiff ℝ (⊤ : ℕ∞) φ → IsZ2Periodic φ →
      CoupledWeakIdentity (volume.restrict AVenhance.unitCube) (D.κ (m - 1)) tp t
          (streamVel (D.Φ (m - 1))) (fun x => aZ t x v) (fun x => aZ tp x v) φ
          (fun j x => gradE φ x j) (fun s' j x => gradE (fun y => aZ s' y v) x j)
          (fun _ _ => 0)
          (fun s' x => -(toFluxL (covPolyQ (covPrimitive D m s') p
              (fun y => gFlux G m N p (succSchedR r₀ J H) CcT aZ v s' y) x) +
            upsilonFlux (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ G G' (G'.retained m H J) m H J (D.eps (m - 1)) (succEta0 α q s) aZ aY v s' x))
          (fun _ _ => 0) ∧
        CoupledWeakIdentity (volume.restrict AVenhance.unitCube) (D.κ (m - 1)) tp t
          (streamVel (D.Φ (m - 1))) (fun x => aRep t x v) (fun x => aRep tp x v) φ
          (fun j x => gradE φ x j) (fun s' j x => gradE (fun y => aRep s' y v) x j)
          (fun s' x => toFluxL (macroFlux G m N (succSchedR r₀ J H) CcT aRep v s' x))
          (fun s' x => toFluxL (meanFluxF G m N p (succSchedR r₀ J H) CcT aZ
            (fun w s'' y => upsilonFlux (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ G G' (G'.retained m H J) m H J (D.eps (m - 1)) (succEta0 α q s)
              aZ aY w s'' y) v s' x))
          (fun _ _ => 0) ∧
        CoupledWeakIdentity (volume.restrict AVenhance.unitCube) (D.κ m) tp t
          (streamVel (D.Φ m)) (fun x => liftedRep G m N (succSchedR r₀ J H) CcT aRep t x v)
          (fun x => liftedRep G m N (succSchedR r₀ J H) CcT aRep tp x v) φ (fun j x => gradE φ x j)
          (fun s' j x => gradE (fun y => liftedRep G m N (succSchedR r₀ J H) CcT aRep s' y v) x j)
          (fun s' x => coeffFluxOn (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ G .kernel
            (liftedRep G m N (succSchedR r₀ J H) CcT aRep) v s' x)
          (fun s' x => fineFluxF (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ G
            (liftedRep G m N (succSchedR r₀ J H) CcT aRep) v s' x)
          (fun s' x => liftedRep G m N (succSchedR r₀ J H) CcT (fun s'' y w => divE (fun y' =>
              meanFluxF G m N p (succSchedR r₀ J H) CcT aZ
                (fun w' s''' y'' => upsilonFlux (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ G G' (G'.retained m H J) m H J (D.eps (m - 1))
                  (succEta0 α q s) aZ aY w' s''' y'') w s'' y') y) s' x v +
            physRes (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ G m N (succSchedR r₀ J H) CcT aRep dRep dUh v s' x))

/-- The complete uniform prefix; data are kept behind a named predicate. -/
def ResidualProductionStatement (α s q : ℝ) (ζ : ℝ → ℝ)
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
    ResidualDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ mStar join

/-- The weak equation for the readout of the retained regular solution, with omitted flux. -/
def RetainedReadoutWeakEquationStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  ResidualProductionStatement α s q ζ (fun readout _transported _full => readout)

/-- From the readout equation, covariance transport and the complete native lift yield
both remaining identities, with common a.e. derivative representatives for all tests. -/
def NativeLiftCovarianceResidualIdentityStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  ResidualProductionStatement α s q ζ (fun readout transported _full => readout → transported)

/-- At fixed choices, the covariance ingredient consumes the readout equation. -/
theorem residual_data_of_readout_and_covariance
    (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw Ce τe : ℝ) (kS : InvConsts)
    (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (ma mb : ℕ)
    (ha : ResidualDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ ma (fun a _b _c => a))
    (hb : ResidualDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ mb (fun a b _c => a → b)) :
    ResidualDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ (max ma mb) (fun a b _c => a ∧ b) := by
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA s₀ htA hs₀ htf hT₀ G G' hcascade hlevel hG hactual
    tp Preg hprep f Ain hAin Y0 Y Yw Yk htrace hsol CcT PZ aRep û hlift aZ aY hZ hY
  have hr := ha D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m (by omega) hn hnM tA s₀ htA hs₀ htf hT₀ G G' hcascade hlevel hG hactual
    tp Preg hprep f Ain hAin Y0 Y Yw Yk htrace hsol CcT PZ aRep û hlift aZ aY hZ hY
  exact ⟨hr, hb D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m (by omega) hn hnM tA s₀ htA hs₀ htf hT₀ G G' hcascade hlevel hG hactual
    tp Preg hprep f Ain hAin Y0 Y Yw Yk htrace hsol CcT PZ aRep û hlift aZ aY hZ hY hr⟩

/-- Merge the readout identity with the jointly represented transported identities. -/
theorem residual_data_conclude
    (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw Ce τe : ℝ) (kS : InvConsts)
    (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) (mStar : ℕ)
    (hall : ResidualDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ mStar (fun a b _c => a ∧ b)) :
    ResidualDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ mStar (fun _a _b c => c) := by
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA s₀ htA hs₀ htf hT₀ G G' hcascade hlevel hG hactual
    tp Preg hprep f Ain hAin Y0 Y Yw Yk htrace hsol CcT PZ aRep û hlift aZ aY hZ hY
  obtain ⟨hread, dRep, dUh, hdRep, hdUh, hrest⟩ := hall D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m hm hn hnM tA s₀ htA hs₀ htf hT₀ G G' hcascade hlevel hG hactual
    tp Preg hprep f Ain hAin Y0 Y Yw Yk htrace hsol CcT PZ aRep û hlift aZ aY hZ hY
  refine ⟨dRep, dUh, hdRep, hdUh, ?_⟩
  intro v t ht φ hφ hp
  exact ⟨hread v t ht φ hφ hp, hrest v t ht φ hφ hp⟩

/-- Choose common pre-data constants for the two hard residual ingredients. -/
theorem residual_production_of_readout_and_covariance {α s q : ℝ} {ζ : ℝ → ℝ}
    (hread : RetainedReadoutWeakEquationStatement α s q ζ)
    (hcov : NativeLiftCovarianceResidualIdentityStatement α s q ζ) :
    ResidualProductionStatement α s q ζ (fun _a _b c => c) := by
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
  exact residual_data_conclude α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ (max ma mb)
    (residual_data_of_readout_and_covariance α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ ma mb ha hb)

theorem successor_residual_identities_of_ingredients (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ)
    (hread : RetainedReadoutWeakEquationStatement α s q ζ)
    (hcov : NativeLiftCovarianceResidualIdentityStatement α s q ζ) :
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
    ∃ dRep dUh : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root,
      IsTimeDerivRep (Set.Icc tp tf) aRep dRep ∧
      IsTimeDerivRep (Set.Icc tp tf) (liftedRep G m N (succSchedR r₀ J H) CcT aRep) dUh ∧
    ∀ v : CompIn G.comps, ∀ t ∈ Set.Icc tp tf, ∀ φ : Vec 2 → hr v.1.root,
      ContDiff ℝ (⊤ : ℕ∞) φ → IsZ2Periodic φ →
      CoupledWeakIdentity (volume.restrict AVenhance.unitCube) (D.κ (m - 1)) tp t
          (streamVel (D.Φ (m - 1))) (fun x => aZ t x v) (fun x => aZ tp x v) φ
          (fun j x => gradE φ x j) (fun s' j x => gradE (fun y => aZ s' y v) x j)
          (fun _ _ => 0)
          (fun s' x => -(toFluxL (covPolyQ (covPrimitive D m s') p
              (fun y => gFlux G m N p (succSchedR r₀ J H) CcT aZ v s' y) x) +
            upsilonFlux (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ G G' (G'.retained m H J) m H J (D.eps (m - 1)) (succEta0 α q s) aZ aY v s' x))
          (fun _ _ => 0) ∧
        CoupledWeakIdentity (volume.restrict AVenhance.unitCube) (D.κ (m - 1)) tp t
          (streamVel (D.Φ (m - 1))) (fun x => aRep t x v) (fun x => aRep tp x v) φ
          (fun j x => gradE φ x j) (fun s' j x => gradE (fun y => aRep s' y v) x j)
          (fun s' x => toFluxL (macroFlux G m N (succSchedR r₀ J H) CcT aRep v s' x))
          (fun s' x => toFluxL (meanFluxF G m N p (succSchedR r₀ J H) CcT aZ
            (fun w s'' y => upsilonFlux (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ G G' (G'.retained m H J) m H J (D.eps (m - 1)) (succEta0 α q s)
              aZ aY w s'' y) v s' x))
          (fun _ _ => 0) ∧
        CoupledWeakIdentity (volume.restrict AVenhance.unitCube) (D.κ m) tp t
          (streamVel (D.Φ m)) (fun x => liftedRep G m N (succSchedR r₀ J H) CcT aRep t x v)
          (fun x => liftedRep G m N (succSchedR r₀ J H) CcT aRep tp x v) φ (fun j x => gradE φ x j)
          (fun s' j x => gradE (fun y => liftedRep G m N (succSchedR r₀ J H) CcT aRep s' y v) x j)
          (fun s' x => coeffFluxOn (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ G .kernel
            (liftedRep G m N (succSchedR r₀ J H) CcT aRep) v s' x)
          (fun s' x => fineFluxF (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ G
            (liftedRep G m N (succSchedR r₀ J H) CcT aRep) v s' x)
          (fun s' x => liftedRep G m N (succSchedR r₀ J H) CcT (fun s'' y w => divE (fun y' =>
              meanFluxF G m N p (succSchedR r₀ J H) CcT aZ
                (fun w' s''' y'' => upsilonFlux (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ G G' (G'.retained m H J) m H J (D.eps (m - 1))
                  (succEta0 α q s) aZ aY w' s''' y'') w s'' y') y) s' x v +
            physRes (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ G m N (succSchedR r₀ J H) CcT aRep dRep dUh v s' x) := by
  exact residual_production_of_readout_and_covariance hread hcov

end AVRegularity.Construction.Preservation.Assembly
end
