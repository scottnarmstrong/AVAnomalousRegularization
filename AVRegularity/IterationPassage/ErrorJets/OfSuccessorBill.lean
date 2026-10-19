-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Proofs.Construction.PreparationBuffer
import AVRegularity.Proofs.Results.Construction.SuccessorResidualIdentities
public import AVRegularity.IterationPassage.ErrorJets.LiftIdentification
public import AVRegularity.Construction.Preservation.Assembly.PreparationJointInputs
import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.Construction.Preservation.RetainedEnergy.Producer

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.IterationPassage.ErrorJets

/-! **Named copies of the producers of `passage_error_jets`**.

`BufferStatement` and `FullLiftStatement` are text copies of the statements
`preparation_buffer` and `successor_full_lift_bound`, with the data part after the conclusion
constants split off as `BufferDataStatement` and `FullLiftDataStatement`, so that the assembly of
`passage_error_jets` handles named propositions (the inline statements are expensive to
elaborate and to unify). `buffer_statement` and `fullLift_statement` are the
proofs at these types. -/

/-- Data part of `preparation_buffer`, after its constants `C_b, m_*`. -/
def BufferDataStatement (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw Ce τe : ℝ)
    (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ) (kI : InvConsts)
    (CI Cw : ℝ) (j₀ Jr : ℕ) (CQ Cpr Q T₀ Cb : ℝ) (mStar : ℕ) : Prop :=
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
      weightedNorm (rhoStar D kI.c₀ m) (G.mass law) w Un ≤ Cb * weightedNorm 1 (G.mass law) w f

/-- Text copy of `preparation_buffer` with its data part named. -/
def BufferStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
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
    BufferDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI
      CI Cw j₀ Jr CQ Cpr Q T₀ Cb mStar

/-- Data part of `successor_full_lift_bound`, after its constants `C_k, m_*`. -/
def FullLiftDataStatement (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw Ce τe : ℝ)
    (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ) (kI : InvConsts)
    (CI Cw : ℝ) (j₀ k : ℕ) (hk : k + N + 2 * p ≤ Naux) (CQ Cpr Q T₀ Ck : ℝ) (mStar : ℕ) : Prop :=
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

/-- Text copy of `successor_full_lift_bound` with its data part named. -/
def FullLiftStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
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
    FullLiftDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI
      CI Cw j₀ k hk CQ Cpr Q T₀ Ck mStar

theorem buffer_statement (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) : BufferStatement α s q ζ :=
  Providers.preparation_buffer α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

theorem fullLift_statement (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) : FullLiftStatement α s q ζ :=
  Providers.successor_full_lift_bound α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

end AVRegularity.IterationPassage.ErrorJets
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.Assembly
namespace AVRegularity.IterationPassage.ErrorJets

/-! **The data context of one passage and the producer outputs**.

`PassageCtx` bundles the data of `passage_error_jets` after its constants (the band data, the
law, the kernels, the generated seed, the level and the times, the stage, its actual successor and
the common preparation with its quiet margin). `PassageCtx.toPair` is the `PassagePair` of the datum
part. The conversion lemmas read each producer's named data statement at the context
(`BufferDataStatement` at `J_r = K + 2` and weight `1`, `FullLiftDataStatement` at `k = 2(K + 2)`,
`PreparedRetainedEnergyProductionDataStatement` and `SuccessorBillDataStatement`, and
`PassageLiftIdentificationDataStatement`); each conversion is its own declaration, so its
unifications have their own budget. -/

/-- The data of `passage_error_jets` after its constants. -/
structure PassageCtx (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ : ℝ) where
  D : OCData
  hDα : D.α = α
  hDq : D.q = q
  hDΛ : D.Λ = Λ
  hDζ : D.ζ = ζ
  hseq : IsOCStreamSeq α q Λ ζ D.Φ
  M : ℕ
  hband : IsOCBandChain α q Λ ζ M D.κ
  hterm : D.term = M
  Mnat : ℕ
  hMnat : M ≤ Mnat
  law : BirthLaw
  hlaw : IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law
  seedK : ℕ → KernelSpec
  freshK : ℕ → KernelSpec
  hfresh : ∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')
  seed : GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀
  n : ℕ
  tS : ℝ
  tf : ℝ
  hseed : IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
    hφ₀ Mnat kS seed n tS tf Ce τe r₀ D₀
  hpw : IsSeedPointwiseMolecular law kS seed tS tf
  m : ℕ
  hn : m ≤ n
  hnM : n < M
  tA : ℝ
  s₀ : ℝ
  htA : tS ≤ tA
  hs₀ : tA + 3 * ocTau α q Λ m ≤ s₀
  htf : s₀ + 4 * ocTauPP α q Λ m ≤ tf
  hT₀ : tf - s₀ ≤ T₀
  G : GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀
  G' : GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀
  hcascade : IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
    (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G
  hlevel : G.level = m
  hG : IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
    hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
    (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G
  hactual : IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
    (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G'
  tp : ℝ
  Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
    (∀ v : CompIn G.comps, TorusHk Nout (ScalarH v.1.root))
  hprep : IsCommonPreparation law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK
    φ₀ hφ₀ G kI.cr Q CQ Cpr p Nout Naux s₀ tf tp Preg
  hquietMargin : Set.Icc (tp - ocTauP α q Λ m) (tp + ocTauP α q Λ m) ⊆ ocQuietTimes α q Λ ζ m

namespace PassagePair

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} (X : PassagePair D Dm b j₀)

/-- The comparison clauses of the bill at the pair, for the regenerated solution. -/
def BillCmp (Cbill : ℝ) : Prop :=
  ∀ (f : ∀ v : CompIn X.G.comps, TorusHk 0 (ScalarH v.1.root)) (Ain : ℝ), X.Marked f Ain →
  ∀ (Y0 : ∀ v' : CompIn X.Gr.comps, TorusHk X.Naux (ScalarH v'.1.root))
    (Y : ∀ v : CompIn X.Gr.comps, ℝ → TorusHk X.Naux (ScalarH v.1.root))
    (Yw : ∀ v : CompIn X.Gr.comps, ℝ → TorusHk (X.Naux + 1) (ScalarH v.1.root))
    (Yk : ∀ v u (_ : X.Gr.fam.Γ v u), ℝ → TorusHk (X.Naux + Dm - 1) (ScalarH u.1.root)),
    X.Trace f Y0 → X.RetSol X.Naux Y0 Y Yw Yk →
    ∃ res : ℝ, ComparisonClauses X.law X.P X.seedK X.freshK X.φ₀ X.hφ₀ X.G X.Gr X.m X.p X.Naux X.N
      X.depth X.sX X.sZ X.η₀ X.s₀ X.tp X.tf res (Cbill * D.eps (X.m - 1) ^ X.Q * Ain) f Y

theorem billOut_of_cmp (Cbill : ℝ) (h : X.BillCmp Cbill) : X.BillOut Cbill := by
  intro f Ain hf Y0 Y Yw Yk htr hsol U Uw Uk hU
  obtain ⟨res, ⟨CcT, PZ, aRep, û, hL⟩, hall⟩ := h f Ain hf Y0 Y Yw Yk htr hsol
  obtain ⟨ŵ, -, -, -, -, -, herr⟩ := hall U Uw Uk hU CcT PZ aRep û hL
  exact ⟨CcT, PZ, aRep, û, ŵ, hL, herr⟩

end PassagePair

namespace PassageCtx

variable {α s q : ℝ} {ζ : ℝ → ℝ} {Λ : ℕ} {φ₀ : Vec 2 → ℝ} {hφ₀ : Integrable φ₀}
  {bw Ce τe : ℝ} {kS : InvConsts} {r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ} {σ₀ : ℝ}
  {kI : InvConsts} {CI Cw : ℝ} {j₀ : ℕ} {CQ Cpr Q T₀ : ℝ}
  (c : PassageCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
    j₀ CQ Cpr Q T₀)

/-- The passage pair of the context, at the jet order `K` and the reserve `K_res`. -/
def toPair (K Kres : ℕ) : PassagePair c.D (succSchedD D₀ N p (H + 1)) bw j₀ where
  law := c.law
  P := succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p
  seedK := c.seedK
  freshK := c.freshK
  φ₀ := φ₀
  hφ₀ := hφ₀
  G := c.G
  Gr := c.G'.retained c.m H J
  m := c.m
  p := p
  N := N
  depth := succSchedR r₀ J H
  sX := sX
  sZ := sZ
  K := K
  Naux := Naux
  Kres := Kres
  Nout := Nout
  η₀ := succEta0 α q s
  Q := Q
  c₀ := kI.c₀
  cr := kI.cr
  s₀ := c.s₀
  tp := c.tp
  tf := c.tf
  Preg := c.Preg

theorem bufferOut (K Kres : ℕ) (Cb : ℝ) (mStar : ℕ) (hm : mStar ≤ c.m)
    (h : BufferDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀
      kI CI Cw j₀ (K + 2) CQ Cpr Q T₀ Cb mStar) :
    (c.toPair K Kres).BufferOut Cb := fun f U Uw Uk hU t ht =>
  h c.D c.hDα c.hDq c.hDΛ c.hDζ c.hseq c.M c.hband c.hterm c.Mnat c.hMnat c.law c.hlaw c.seedK
    c.freshK c.hfresh c.seed c.n c.tS c.tf c.hseed c.m hm c.hn c.hnM c.tA c.s₀ c.htA c.hs₀ c.htf
    c.hT₀ c.G c.G' c.hcascade c.hlevel c.hG c.hactual c.tp c.Preg c.hprep f (fun _ => 1)
    (Or.inl rfl) U Uw Uk hU t ht

theorem energyOut (K Kres : ℕ) (Cret : ℝ) (mStar : ℕ) (hm : mStar ≤ c.m)
    (h : PreparedRetainedEnergyProductionDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p
      nk Naux Nout Kres npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ Cret mStar) :
    (c.toPair K Kres).EnergyOut Cret :=
  (h c.D c.hDα c.hDq c.hDΛ c.hDζ c.hseq c.M c.hband c.hterm c.Mnat c.hMnat c.law c.hlaw c.seedK
    c.freshK c.hfresh c.seed c.n c.tS c.tf c.hseed c.m hm c.hn c.hnM c.tA c.s₀ c.htA c.hs₀ c.htf
    c.hT₀ c.G c.G' c.hcascade c.hlevel c.hG c.hactual c.tp c.Preg c.hprep).2

theorem liftOut (K Kres : ℕ) (hk : 2 * (K + 2) + N + 2 * p ≤ Naux) (Ck : ℝ) (mStar : ℕ)
    (hm : mStar ≤ c.m)
    (h : FullLiftDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ
      σ₀ kI CI Cw j₀ (2 * (K + 2)) hk CQ Cpr Q T₀ Ck mStar) :
    (c.toPair K Kres).LiftOut Ck := by
  intro f Ain hf Y0 Y Yw Yk htr hsol
  obtain ⟨⟨CcT, PZ, aRep, û, ŵ, hW⟩, hall⟩ := h c.D c.hDα c.hDq c.hDΛ c.hDζ c.hseq c.M c.hband
    c.hterm c.Mnat c.hMnat c.law c.hlaw c.seedK c.freshK c.hfresh c.seed c.n c.tS c.tf c.hseed c.m
    hm c.hn c.hnM c.tA c.s₀ c.htA c.hs₀ c.htf c.hT₀ c.G c.G' c.hcascade c.hlevel c.hG c.hactual
    c.tp c.Preg c.hprep f Ain hf Y0 Y Yw Yk htr hsol
  have hb := hall CcT PZ aRep û ŵ hW (fun _ => 1) (Or.inl rfl)
  have hch := ofReal_chain_le hb.1 hb.2
  have hw : (fun v => c.G.mass c.law v / (fun _ => (1 : ℝ)) v ^ 2) = c.G.mass c.law := by
    funext v
    simp
  rw [hw] at hch
  exact ⟨CcT, PZ, aRep, û, ŵ, hW.1, hch⟩

theorem billCmp (K Kres Lc Lf Acl : ℕ) (Cbill cB : ℝ) (mStar : ℕ) (hm : mStar ≤ c.m)
    (h : SuccessorBillDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Lc Lf Acl Naux
      Nout npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ Cbill cB mStar) :
    (c.toPair K Kres).BillCmp Cbill := fun f Ain hf Y0 Y Yw Yk htr hsol =>
  ⟨_, (h c.D c.hDα c.hDq c.hDΛ c.hDζ c.hseq c.M c.hband c.hterm c.Mnat c.hMnat c.law c.hlaw c.seedK
    c.freshK c.hfresh c.seed c.n c.tS c.tf c.hseed c.hpw c.m hm c.hn c.hnM c.tA c.s₀ c.htA c.hs₀
    c.htf
    c.hT₀ c.G c.G' c.hcascade c.hlevel c.hG c.hactual c.tp c.Preg c.hprep c.hquietMargin f Ain hf Y0 Y
    Yw Yk htr hsol).2⟩

theorem lidOut (K Kres : ℕ) (mStar : ℕ) (hm : mStar ≤ c.m)
    (h : PassageLiftIdentificationDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux
      Nout npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ mStar) :
    (c.toPair K Kres).LidOut := fun f Ain hf Y0 Y Yw Yk htr hsol Kr hKr aY haY CcT hCcT CcT' PZ
    aRep _ û hL =>
  h c.D c.hDα c.hDq c.hDΛ c.hDζ c.hseq c.M c.hband c.hterm c.Mnat c.hMnat c.law c.hlaw c.seedK
    c.freshK c.hfresh c.seed c.n c.tS c.tf c.hseed c.m hm c.hn c.hnM c.tA c.s₀ c.htA c.hs₀ c.htf
    c.hT₀ c.G c.G' c.hcascade c.hlevel c.hG c.hactual c.tp c.Preg c.hprep f Ain hf Y0 Y Yw Yk htr
    hsol Kr hKr aY haY CcT hCcT CcT' PZ aRep û hL

/-- The scalar facts of the datum part: positive masses, `ρ⋆ ≥ 0`, `E ≥ 0`, and the ordinary
datum bound from the marked one. -/
theorem scalarFacts (K Kres : ℕ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s)
    (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) (hΛ : 128 ≤ Λ) (hc₀ : 0 ≤ kI.c₀) :
    (∀ v, 0 < (c.toPair K Kres).G.mass (c.toPair K Kres).law v) ∧
    0 ≤ rhoStar c.D (c.toPair K Kres).c₀ (c.toPair K Kres).m ∧
    0 ≤ c.D.eps ((c.toPair K Kres).m - 1) ∧
    ∀ (f : ∀ v : CompIn (c.toPair K Kres).G.comps, TorusHk 0 (ScalarH v.1.root)) (A : ℝ),
      (c.toPair K Kres).Marked f A →
      weightedNorm 1 ((c.toPair K Kres).G.mass (c.toPair K Kres).law) (fun _ => 1) f ≤ A := by
  have hqD : 1 < c.D.q := c.hDq.symm ▸ hq.1
  have hΛD : 128 ≤ c.D.Λ := by rw [c.hDΛ]; exact hΛ
  have hη := Construction.Preservation.FullLift.successor_eta0_pos hα₀ hα₁ hs₀ hs₁ hq
  obtain ⟨-, -, -, hiota⟩ := Construction.Preservation.FullLift.successor_readout_law_facts hη c.hlaw
  have heps : ∀ i, 0 ≤ c.D.eps i := fun i => by
    rw [OCData.eps]
    exact (Construction.Stream.ocEpsilon_pos (by omega)).le
  refine ⟨fun v => Construction.Preservation.Buffer.birth_compMass_pos hqD hΛD c.law v.1,
    mul_nonneg hc₀ (le_min (heps _) (Real.sqrt_nonneg _)), heps _, fun f A hf =>
    Construction.Preservation.FullLift.ordinary_input_from_marked c.G hqD hΛD c.law hiota 1 f hf⟩

end PassageCtx

end AVRegularity.IterationPassage.ErrorJets
end
end
end

section
section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.Assembly
namespace AVRegularity.IterationPassage.ErrorJets

/-! **`passage_error_jets` from its ingredients**.

`passage_error_jets_of_ingredients` proves the exact statement `PassageErrorJetsStatement` (the
text copy of the statement `passage_error_jets`, `IterationPassage/Assembly/CascadeInterfaces.lean`)
from three named ingredients:

* `SuccessorBillStatement` (the text copy of the statement `successor_bill`, from the preservation argument);
* `PassageLiftIdentificationStatement` (`ErrorJets/Ingredients.lean`);
* `PassageRegenerationStatement` (proved: `passageRegeneration`,
  `ErrorJets/Regeneration.lean`; `passage_error_jets_of_bill` uses it).

The producers `preparation_buffer` and `successor_full_lift_bound` and the proved
`prepared_retained_energy_production` are applied directly. Quantifier alignment: the lift floors
`S_X = S_Z = max (N + D_H) (2p) + D_{H+1} + 2` (the premise of the full lift, the bill, the
energy and the identification); the thresholds are joined by `certificateThresholdJoin`, the
carrier constants and the ledger thresholds by maxima, `c₀max` by minima, `Λ₀` and `m_*` by
maxima; the buffer is used at `J_r = K + 2` (`2J_r + N + 2p ≤ N_aux` by `IsPassageOrders`,
`2J_r ≤ N_aux ≤ K_res ≤ K_s` by admissibility) and the full lift at `k = 2(K + 2)`. The constant is
`C = C₁ + paidErrorJetConstant (K + 2) |C_bill| C₁`, `C₁ = |C_b| + C_k²`.

The degenerate cases are included: empty component families (vacuous), `p = 0`, the first
admissible level `m = m_*`,
`t_p = s₀ + ρ⋆²/ν` exactly (the buffer premise is not used beyond the producers'). -/

/-- The split form of `passage_error_jets` from the bill, the lift identification and the
regeneration. -/
theorem passageErrorJetsSplit_of_ingredients
    (hbill : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ → SuccessorBillStatement α s q ζ)
    (hlid : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PassageLiftIdentificationStatement α s q ζ)
    (hregen : PassageRegenerationStatement) : PassageErrorJetsSplit := by
  classical
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λu, hΛu, hu⟩ := buffer_statement α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λl, hΛl, hl⟩ := fullLift_statement α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λe, hΛe, he⟩ :=
    Construction.Preservation.RetainedEnergy.prepared_retained_energy_production hα₀ hα₁ hs₀ hs₁
      hq hζ
  obtain ⟨Λb, hΛb, hb⟩ := hbill α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λi, hΛi, hi⟩ := hlid α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨max (max (max Λu Λl) (max Λe Λb)) Λi, by omega, ?_⟩
  intro Λ hΛ
  have h128 : 128 ≤ Λ := by omega
  obtain ⟨cu, hcu, hu⟩ := hu Λ (by omega)
  obtain ⟨cl, hcl, hl⟩ := hl Λ (by omega)
  obtain ⟨ce, hce, he⟩ := he Λ (by omega)
  obtain ⟨cb, hcb, hb⟩ := hb Λ (by omega)
  obtain ⟨ci, hci, hi⟩ := hi Λ (by omega)
  refine ⟨min (min (min cu cl) (min ce cb)) ci,
    lt_min (lt_min (lt_min hcu hcl) (lt_min hce hcb)) hci, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper K Pacc hK hPacc Q T₀ hQ hT₀ hPQ
    r₀ D₀ τe lamE σE hτe hlamE hσE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ
    hsched hNaux hNout hfloor L horders hwidths
  refine ⟨max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2,
    max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2, ?_⟩
  intro sX sZ hSX hSZ Ce kS hCe hc₀ hc₀upper hcr hcrupper hσf hlamC halloc
  have hcu' : kS.c₀ ≤ cu := hc₀upper.trans
    ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hcl' : kS.c₀ ≤ cl := hc₀upper.trans
    ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hce' : kS.c₀ ≤ ce := hc₀upper.trans
    ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hcb' : kS.c₀ ≤ cb := hc₀upper.trans
    ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hci' : kS.c₀ ≤ ci := hc₀upper.trans (min_le_right _ _)
  have hσf' : 0 < kS.σf := hσf.symm ▸ hσE
  have hlamC' : 0 < kS.lamC := hlamC.symm ▸ hlamE
  have hsched' : IsSuccessorSchedule α q s Q σ₀ a σ (min kS.σf (ocDelta α q + σ₀))
      kS.lamC D₀ H J N p nk Lc Lf Lpr Acl Naux Nout := by
    simpa only [hσf, hlamC] using hsched
  obtain ⟨tu, CHu, Υu, hCHu, hΥu, hu⟩ := hu φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper
    Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀ hcu' hcr hcrupper hσf' hlamC'
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched' hNaux hNout halloc
  obtain ⟨tl, CHl, Υl, hCHl, hΥl, hl⟩ := hl φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper
    Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀ hcl' hcr hcrupper hσf' hlamC'
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched' hNaux hNout halloc hSX hSZ
  obtain ⟨te, CHe, Υe, hCHe, hΥe, he⟩ := he φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper
    Q T₀ hQ hT₀ r₀ D₀ τe lamE σE hτe hlamE hσE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ
    hsched hNaux hNout sX sZ hSX hSZ Ce kS hCe hc₀ hce' hcr hcrupper hσf hlamC halloc
  obtain ⟨tb, CHb, Υb, hCHb, hΥb, hb⟩ := hb φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper
    Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀ hcb' hcr hcrupper hσf' hlamC'
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched' hNaux hNout hfloor halloc
    hSX hSZ
  obtain ⟨ti, CHi, Υi, hCHi, hΥi, hi⟩ := hi φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper
    Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀ hci' hcr hcrupper hσf' hlamC'
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched' hNaux hNout halloc hSX hSZ
  refine ⟨certificateThresholdJoin (certificateThresholdJoin (certificateThresholdJoin tu tl)
      (certificateThresholdJoin te tb)) ti,
    max (max (max CHu CHl) (max CHe CHb)) CHi, max (max (max Υu Υl) (max Υe Υb)) Υi,
    hCHu.trans ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))),
    hΥu.trans_le ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))), ?_⟩
  intro kI hkI
  have hk1 := invariant_admissible_threshold_left hkI
  have hkI_i := invariant_admissible_threshold_right hkI
  have hk2 := invariant_admissible_threshold_left hk1
  have hk3 := invariant_admissible_threshold_right hk1
  have hkI_u := invariant_admissible_threshold_left hk2
  have hkI_l := invariant_admissible_threshold_right hk2
  have hkI_e := invariant_admissible_threshold_left hk3
  have hkI_b := invariant_admissible_threshold_right hk3
  obtain ⟨CIu, Cwu, hu⟩ := hu kI hkI_u
  obtain ⟨CIl, Cwl, hl⟩ := hl kI hkI_l
  obtain ⟨CIe, Cwe, he⟩ := he kI hkI_e
  obtain ⟨CIb, Cwb, hb⟩ := hb kI hkI_b
  obtain ⟨CIi, Cwi, hi⟩ := hi kI hkI_i
  refine ⟨max (max (max CIu CIl) (max CIe CIb)) CIi, max (max (max Cwu Cwl) (max Cwe Cwb)) Cwi, ?_⟩
  intro CI Cw j₀ hledger hstart
  have hLu : IsLedgerAdmissible Ce CI Cw CIu Cwu :=
    ⟨hledger.1, ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans
      hledger.2.1, ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans
      hledger.2.2.1, hledger.2.2.2⟩
  have hLl : IsLedgerAdmissible Ce CI Cw CIl Cwl :=
    ⟨hledger.1, ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans
      hledger.2.1, ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans
      hledger.2.2.1, hledger.2.2.2⟩
  have hLe : IsLedgerAdmissible Ce CI Cw CIe Cwe :=
    ⟨hledger.1, ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans
      hledger.2.1, ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans
      hledger.2.2.1, hledger.2.2.2⟩
  have hLb : IsLedgerAdmissible Ce CI Cw CIb Cwb :=
    ⟨hledger.1, ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans
      hledger.2.1, ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans
      hledger.2.2.1, hledger.2.2.2⟩
  have hLi : IsLedgerAdmissible Ce CI Cw CIi Cwi :=
    ⟨hledger.1, (le_max_right _ _).trans hledger.2.1, (le_max_right _ _).trans hledger.2.2.1,
      hledger.2.2.2⟩
  have hA : ∀ i, 0 ≤ ocA α q Λ i := fun _ => (Real.rpow_pos_of_pos
    (Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ Λ)) _).le
  have hT : ∀ i, 0 ≤ ocTauPP α q Λ i := fun _ => (Construction.Stream.ocTauPP_pos (by omega)).le
  have hSu := IsCarrierStart.mono hA hT
    ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
    ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
    (zero_le_one.trans hCHu) hΥu.le hstart
  have hSl := IsCarrierStart.mono hA hT
    ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
    ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
    (zero_le_one.trans hCHl) hΥl.le hstart
  have hSe := IsCarrierStart.mono hA hT
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _)))
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _)))
    (zero_le_one.trans hCHe) hΥe.le hstart
  have hSb := IsCarrierStart.mono hA hT
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _)))
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _)))
    (zero_le_one.trans hCHb) hΥb.le hstart
  have hSi := IsCarrierStart.mono hA hT (le_max_right _ _) (le_max_right _ _)
    (zero_le_one.trans hCHi) hΥi.le hstart
  have hk : 2 * (K + 2) + N + 2 * p ≤ Naux := (Nat.le_add_right _ L).trans horders.1
  have hKs : Kres ≤ kI.Ks := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _⟩ := hkI
    exact h
  intro CQ Cpr
  have hJr : 2 * (K + 2) ≤ kI.Ks :=
    ((Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans hk)).trans (hNaux.trans hKs)
  obtain ⟨Cb, mu, hu⟩ := hu CI Cw j₀ hLu hSu (K + 2) hk hJr CQ Cpr
  obtain ⟨Ck, ml, hl⟩ := hl CI Cw j₀ hLl hSl (2 * (K + 2)) hk CQ Cpr
  obtain ⟨Cret, me, he⟩ := he CI Cw j₀ hLe hSe CQ Cpr
  obtain ⟨Cbill, cB, mb, -, hb⟩ := hb CI Cw j₀ hLb hSb CQ Cpr
  obtain ⟨mi, hi⟩ := hi CI Cw j₀ hLi hSi CQ Cpr
  refine ⟨(|Cb| + Ck ^ 2) + paidErrorJetConstant (K + 2) |Cbill| (|Cb| + Ck ^ 2),
    max (max (max mu ml) (max me mb)) mi, ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw seedK freshK hfresh seed n tS tf
    hseed hpw m hm hn hnM tA s₀ htA hs₀' htf hT₀' G G' hcascade hlevel hG hactual tp Preg hprep
    _hbuffer hquietMargin
  let c : PassageCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
      j₀ CQ Cpr Q T₀ :=
    ⟨D, hDα, hDq, hDΛ, hDζ, hseq, M, hband, hterm, Mnat, hMnat, law, hlaw, seedK, freshK, hfresh,
      seed, n, tS, tf, hseed, hpw, m, hn, hnM, tA, s₀, htA, hs₀', htf, hT₀', G, G', hcascade,
      hlevel,
      hG, hactual, tp, Preg, hprep, hquietMargin⟩
  have hc₀I : 0 ≤ kI.c₀ := (hkI.1.symm ▸ hc₀).le
  have hmu : mu ≤ m := ((le_max_left mu ml).trans ((le_max_left _ _).trans (le_max_left _ _))).trans hm
  have hml : ml ≤ m := ((le_max_right mu ml).trans ((le_max_left _ _).trans (le_max_left _ _))).trans hm
  have hme : me ≤ m := ((le_max_left me mb).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hm
  have hmb : mb ≤ m := ((le_max_right me mb).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hm
  have hmi : mi ≤ m := (le_max_right _ _).trans hm
  obtain ⟨hπ, hρ, hE, hord⟩ := c.scalarFacts K Kres hα₀ hα₁ hs₀ hs₁ hq h128 hc₀I
  exact (c.toPair K Kres).errorOutput Cb Ck Cbill Cret hNaux hπ hρ hE hord
    (c.bufferOut K Kres Cb mu hmu hu)
    (c.energyOut K Kres Cret me hme he)
    (c.liftOut K Kres hk Ck ml hml hl)
    ((c.toPair K Kres).billOut_of_cmp Cbill (c.billCmp K Kres Lc Lf Acl Cbill cB mb hmb hb))
    (c.lidOut K Kres mi hmi hi)
    hregen

/-- **`passage_error_jets` from the bill, the lift identification and the regeneration.** -/
theorem passage_error_jets_of_ingredients
    (hbill : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ → SuccessorBillStatement α s q ζ)
    (hlid : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PassageLiftIdentificationStatement α s q ζ)
    (hregen : PassageRegenerationStatement) :
    IterationPassage.Assembly.PassageErrorJetsStatement :=
  passageErrorJets_of_split (passageErrorJetsSplit_of_ingredients hbill hlid hregen)

/-- **`passage_error_jets` from the bill and the lift identification** (the regeneration is
`passageRegeneration`). -/
theorem passage_error_jets_of_bill
    (hbill : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ → SuccessorBillStatement α s q ζ)
    (hlid : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PassageLiftIdentificationStatement α s q ζ) :
    IterationPassage.Assembly.PassageErrorJetsStatement :=
  passage_error_jets_of_ingredients hbill hlid passageRegeneration

end AVRegularity.IterationPassage.ErrorJets
end
end

section
public section
namespace AVRegularity.IterationPassage.ErrorJets

/-! **`passage_error_jets` from `successor_bill` alone**.

The lift identification is proved (`passageLiftIdentification`,
`ErrorJets/LiftIdentification.lean`) and the regeneration is `passageRegeneration`; the only remaining
ingredient of `passage_error_jets` is the statement `successor_bill` of the preservation argument, used
here as the hypothesis `SuccessorBillStatement` for all admissible parameters. -/

open AVRegularity.Construction.Preservation.Assembly

/-- **`passage_error_jets` from `successor_bill`.** -/
theorem passage_error_jets_of_successor_bill
    (hbill : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ → SuccessorBillStatement α s q ζ) :
    IterationPassage.Assembly.PassageErrorJetsStatement :=
  passage_error_jets_of_bill hbill
    (fun α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ => passageLiftIdentification α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)

end AVRegularity.IterationPassage.ErrorJets
end
end
end
