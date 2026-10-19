-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.IterationPassage.ErrorJets.LiftIdentification
import AVRegularity.Construction.Preservation.Assembly.PreparationJointInputs
import AVRegularity.EntryTerminal.Ingredients.PrepInterp.PrepInterp
import AVRegularity.Construction.Preservation.FullLift.ZeroFreshMetricSliceJets
public import AVRegularity.Construction.Preservation.RetainedEnergy.UniformInputs
public import AVRegularity.CycleJoint.Assembly.MeanNormalizedBlocks
import AVRegularity.EntryTerminal.Ingredients.PrepNorm.PrepNorm
import AVRegularity.Construction.EntryScales.TerminalCore
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarCellStrongTime
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber

section
section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.IterationPassage.Passage

/-! **`stage_invariant_propagation` with its data part named**.

`StageInvariantPropagationTarget` is a text copy of the statement
`stage_invariant_propagation` (with its lift
floor premises on `s_X, s_Z`); `StageInvariantPropagationData` is its data part after the level
threshold and `StageInvariantPropagationSplit` the statement with that part named.
`stageInvariantPropagationSplit_of_target` is the identity (definitional unfolding).

The variant `IterationPassage.Assembly.StageInvariantPropagationStatement` lacks the two lift
floor premises and is not used here. -/

/-- Text copy of the statement `stage_invariant_propagation`. -/
def StageInvariantPropagationTarget : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ),
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
        (CI * D.eps ((m - 1) - 1) ^ (q * min (ocDelta α q / 4) τe)) (G'.retained m H J)

/-- The data part of `stage_invariant_propagation`. -/
def StageInvariantPropagationData (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw Ce τe : ℝ)
    (kS : InvConsts) (r₀ D₀ H J N p nk npad sX sZ : ℕ) (σ₀ : ℝ) (kI : InvConsts) (CI Cw : ℝ)
    (j₀ mStar : ℕ) : Prop :=
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
        (CI * D.eps ((m - 1) - 1) ^ (q * min (ocDelta α q / 4) τe)) (G'.retained m H J)

/-- `StageInvariantPropagationTarget` with its data part named. -/
def StageInvariantPropagationSplit : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ),
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
    StageInvariantPropagationData α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk npad sX sZ σ₀ kI CI Cw
      j₀ mStar

theorem stageInvariantPropagationSplit_of_target (h : StageInvariantPropagationTarget) :
    StageInvariantPropagationSplit := h

end AVRegularity.IterationPassage.Passage
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.IterationPassage.ErrorJets
namespace AVRegularity.IterationPassage.Passage

/-! **Ingredients of `iteration_passage`**.

`iteration_passage` produces the frame of one passage from `preservation_successor` and
`stage_invariant_propagation`, and for every datum the clauses of `PassageDatum`: the marked
amplitude and the regenerated solution with its comparison (from `preservation_successor`), the
jets (from `passage_error_jets`), and three facts stated here.

* `PassageProfilesStatement` (prefix of `iteration_passage` through the carrier start, then
  `∀ C_Q C_pr, ∃ C₀ m_*, ∀ C ≥ C₀`): the exact profile proposition `PassageClauses` for every common preparation with its buffer and quiet margin, every datum, incoming solution
  and retained solution. This is the analytic core of the passage (the five profile estimates and
  the recurrence); it has its own assembly.
* `PassageRetainedStrongEnergyStatement` (prefix of the retained energy producer): the strong
  energy `𝓔^B_{ρ,N_aux;π_-}(d_-Y; W) ≤ C A` of the regenerated solution in the marked weight.
  `RetainedSolutionClauses` only gives the sum form of the energy (the supremum of the sum over
  the components), which does not bound the per-component supremum of `strongEnergy`.
* `PassageReadoutNormStatement` (local): the operator norm of the constant readout `readoutCLM`
  from the order-zero weighted bound of `succReadout` (the readout clause of
  `NextFamilyClauses`), by constant fields.

Special cases. Empty families: all three are vacuous or `0 ≤ B`. `A = 0`: the datum is zero and all
bounds are `0 ≤ 0`. The constants `C₀` come after `C_Q, C_pr` and before the data; the statements
are closed upward in `C`. -/

/-- Data part of `PassageProfilesStatement`: `PassageClauses` with the constant `C` for every
common preparation with its buffer and quiet margin. -/
def PassageProfilesData (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw : ℝ)
    (K : ℕ) (Pacc Q T₀ : ℝ) (r₀ D₀ : ℕ) (τe : ℝ) (H J N p nk Naux Nout npad : ℕ) (σ₀ : ℝ)
    (sX sZ : ℕ) (Ce : ℝ) (kS kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ)
    (CQ Cpr C : ℝ) (mStar : ℕ) : Prop :=
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
      IsSeedPointwiseMolecular law kS seed tS tf →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ (tA s₀ : ℝ), tS ≤ tA → tA + 3 * ocTau α q Λ m ≤ s₀ → s₀ + 4 * ocTauPP α q Λ m ≤ tf →
      tf - s₀ ≤ T₀ →
    ∀ (G G' : GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
    ∀ (tp : ℝ) (Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn G.comps, TorusHk Nout (ScalarH v.1.root))),
      IsCommonPreparation law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        G kI.cr Q CQ Cpr p Nout Naux s₀ tf tp Preg →
      s₀ + rhoStar D kI.c₀ m ^ 2 / D.κ m ≤ tp →
      Set.Icc (tp - ocTauP α q Λ m) (tp + ocTauP α q Λ m) ⊆ ocQuietTimes α q Λ ζ m →
    ∀ (f : ∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) (A : ℝ),
      weightedNorm 1 (G.mass law) (G.marker law) f ≤ A →
    ∀ (U : ∀ v : CompIn G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
      (Uw : ∀ v : CompIn G.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
      (Uk : ∀ v u (_ : G.fam.Γ v u), ℝ →
        TorusHk (0 + succSchedD D₀ N p (H + 1) - 1) (ScalarH u.1.root)),
      HomRegSol (hr := ScalarH) (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK
        φ₀ hφ₀ G (D.κ m) (streamVel (D.Φ m)) 0 s₀ tf f U Uw Uk →
    ∀ (Y0 : ∀ v' : CompIn (G'.retained m H J).comps, TorusHk 0 (ScalarH v'.1.root))
      (Y : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk 0 (ScalarH v.1.root))
      (Yw : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk 1 (ScalarH v.1.root))
      (Yk : ∀ v u (_ : (G'.retained m H J).fam.Γ v u), ℝ →
        TorusHk (0 + succSchedD D₀ N p (H + 1) - 1) (ScalarH u.1.root)),
      IsRetainedTrace G (G'.retained m H J) m p tp (Preg f) Y0 →
      HomRegSol (hr := ScalarH) (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK
        φ₀ hφ₀ (G'.retained m H J) (D.κ (m - 1)) (streamVel (D.Φ (m - 1))) 0 tp tf Y0 Y Yw Yk →
      PassageClauses D law G (G'.retained m H J) m p N (succSchedR r₀ J H) sX sZ K s
        (succEta0 α q s) (ocMuS α q s) (ocDelta α q - 2 * σ₀) Pacc C A tp tf φ₀ (freshK (m - 1))
        U Y

/-- **The exact profile proposition of one passage**, closed upward in `C`. -/
def PassageProfilesStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (K : ℕ) (Pacc : ℝ), 3 ≤ K → 0 < Pacc →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ → Pacc + q * iterZ α q s K + 4 < Q / 2 →
    ∀ (r₀ D₀ : ℕ) (τe lamE σE : ℝ), 0 < τe → 0 < lamE → 0 < σE →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min σE (ocDelta α q + σ₀)) lamE D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
    ∀ L : ℕ, IsPassageOrders α q s K Pacc σ₀ L N p nk Naux →
      IsCascadeWidths α q lamE a σ (succDstar D₀ N p H) →
    ∃ SX SZ Kneed : ℕ, ∀ sX sZ : ℕ, SX ≤ sX → SZ ≤ sZ →
    ∀ (Ce : ℝ) (kS : InvConsts), 1 ≤ Ce →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → kS.σf = σE → kS.lamC = lamE →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
      Kneed ≤ kS.Ks → Kneed ≤ kS.Kan → Kneed ≤ kS.Lan → Kneed ≤ kS.Jm →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∀ CQ Cpr : ℝ, ∃ (C₀ : ℝ) (mStar : ℕ), ∀ C : ℝ, C₀ ≤ C →
    PassageProfilesData α s q ζ Λ φ₀ hφ₀ bw K Pacc Q T₀ r₀ D₀ τe H J N p nk Naux Nout npad σ₀ sX sZ Ce kS
      kI CI Cw j₀ CQ Cpr C mStar

/-- Data part of `PassageRetainedStrongEnergyStatement`. -/
def PassageRetainedStrongEnergyData (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw Ce τe : ℝ) (kS : InvConsts)
    (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr Q T₀ C : ℝ) (mStar : ℕ) : Prop :=
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ (tA s₀ : ℝ), tS ≤ tA → tA + 3 * ocTau α q Λ m ≤ s₀ → s₀ + 4 * ocTauPP α q Λ m ≤ tf →
      tf - s₀ ≤ T₀ →
    ∀ (G G' : GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
    ∀ (tp : ℝ) (Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn G.comps, TorusHk Nout (ScalarH v.1.root))),
      IsCommonPreparation law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        G kI.cr Q CQ Cpr p Nout Naux s₀ tf tp Preg →
    ∀ (f : ∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) (Ain : ℝ),
      weightedNorm 1 (G.mass law) (G.marker law) f ≤ Ain →
    ∀ (Y0 : ∀ v' : CompIn (G'.retained m H J).comps, TorusHk Naux (ScalarH v'.1.root))
      (Y : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk Naux (ScalarH v.1.root))
      (Yw : ∀ v : CompIn (G'.retained m H J).comps, ℝ → TorusHk (Naux + 1) (ScalarH v.1.root))
      (Yk : ∀ v u (_ : (G'.retained m H J).fam.Γ v u), ℝ →
        TorusHk (Naux + succSchedD D₀ N p (H + 1) - 1) (ScalarH u.1.root)),
      IsRetainedTrace G (G'.retained m H J) m p tp (Preg f) Y0 →
      HomRegSol (hr := ScalarH) (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK
        φ₀ hφ₀ (G'.retained m H J) (D.κ (m - 1)) (streamVel (D.Φ (m - 1))) Naux tp tf Y0 Y Yw Yk →
      strongEnergy (rhoEnh D kI.cr m) (D.κ (m - 1))
          (fun v => (G'.retained m H J).mass law v / (G'.retained m H J).marker law v ^ 2)
          tp tf Y Yw ≤ ENNReal.ofReal (C * Ain)

/-- **The strong energy of the regenerated retained solution** in the marked weight
(`𝓔^B_{ρ,N_aux;π_-}(d_-Y; W) ≤ CA`), closed upward in `C`. Route:
`common_preparation_retained_strongEnergy` with the kernel operator and drift data of
`prepared_retained_energy_production`. -/
def PassageRetainedStrongEnergyStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ →
    ∀ (r₀ D₀ : ℕ) (τe lamE σE : ℝ), 0 < τe → 0 < lamE → 0 < σE →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min σE (ocDelta α q + σ₀)) lamE D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
    ∀ sX sZ : ℕ,
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sX →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sZ →
    ∀ (Ce : ℝ) (kS : InvConsts), 1 ≤ Ce →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → kS.σf = σE → kS.lamC = lamE →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∀ CQ Cpr : ℝ, ∃ (C₀ : ℝ) (mStar : ℕ), ∀ C : ℝ, C₀ ≤ C →
    PassageRetainedStrongEnergyData α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad
      sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ C mStar

/-- **The norm of the constant readout from the order-zero weighted bound** (by constant fields).
Special cases: empty `S'` (the readout is `0`, `0 ≤ B`); `B = 0`. -/
def PassageReadoutNormStatement : Prop :=
  ∀ {S S' : Finset Comp} (m : ℕ) (E η₀ ρ B : ℝ) (π : CompIn S → ℝ) (π' : CompIn S' → ℝ),
    (∀ v, 0 < π v) → (∀ v', 0 < π' v') → 0 ≤ B →
    (∀ X : ∀ v' : CompIn S', TorusHk 0 (ScalarH v'.1.root),
      weightedNorm ρ π (fun _ => 1) (succReadout m E η₀ 0 X) ≤
        B * weightedNorm ρ π' (fun _ => 1) X) →
    ‖readoutCLM m E η₀ π π'‖ ≤ B

end AVRegularity.IterationPassage.Passage
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.IterationPassage.Passage

/-! **`iteration_passage` with its data part named**.

`IterationPassageData` is the data part of `IterationPassageStatement` after its constants
`C, C_Q, m_*`, and `IterationPassageSplit` is the statement with that part named;
`iterationPassage_of_split` is the identity (definitional unfolding). The assembly proves the split
form, whose intermediate goals are small. -/

/-- The data part of `iteration_passage`. -/
def IterationPassageData (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw : ℝ)
    (K : ℕ) (Pacc Q T₀ : ℝ) (r₀ D₀ : ℕ) (τe : ℝ) (H J N p nk Naux Nout Kres npad : ℕ) (σ₀ : ℝ)
    (sX sZ : ℕ) (Ce : ℝ) (kS kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (C CQ : ℝ) (mStar : ℕ) : Prop :=
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
      IsSeedPointwiseMolecular law kS seed tS tf →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ (tA s₀ : ℝ), tS ≤ tA → tA + 3 * ocTau α q Λ m ≤ s₀ → s₀ + 4 * ocTauPP α q Λ m ≤ tf →
      tf - s₀ ≤ T₀ →
    ∀ (G G' : GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
    ∃ (tp : ℝ) (Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn G.comps, TorusHk Nout (ScalarH v.1.root))),
      PassageFrame law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seedK freshK φ₀ hφ₀ Mnat kI CI τe
        seed G (G'.retained m H J) m (succEta0 α q s) Kres
        (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card p Nout Naux Q CQ C tA s₀ tf
        tp Preg ∧
      PassageOutput law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀ G
        (G'.retained m H J) m p N (succSchedR r₀ J H) sX sZ K Naux s (succEta0 α q s)
        (ocMuS α q s) (ocDelta α q - 2 * σ₀) Pacc Q C kI.cr kI.c₀ s₀ tp tf (freshK (m - 1)) Preg

/-- `IterationPassageStatement` with its data part named. -/
def IterationPassageSplit : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ),
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (K : ℕ) (Pacc : ℝ), 3 ≤ K → 0 < Pacc →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ → Pacc + q * iterZ α q s K + 4 < Q / 2 →
    ∀ (r₀ D₀ : ℕ) (τe lamE σE : ℝ), 0 < τe → 0 < lamE → 0 < σE →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min σE (ocDelta α q + σ₀)) lamE D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
      succReconFloor r₀ D₀ H J N p Acl Lc ≤ Naux →
    ∀ L : ℕ, IsPassageOrders α q s K Pacc σ₀ L N p nk Naux →
      IsCascadeWidths α q lamE a σ (succDstar D₀ N p H) →
    ∃ SX SZ Kneed : ℕ, ∀ sX sZ : ℕ, SX ≤ sX → SZ ≤ sZ →
    ∀ (Ce : ℝ) (kS : InvConsts), 1 ≤ Ce →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → kS.σf = σE → kS.lamC = lamE →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
      Kneed ≤ kS.Ks → Kneed ≤ kS.Kan → Kneed ≤ kS.Lan → Kneed ≤ kS.Jm →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∃ (C CQ : ℝ) (mStar : ℕ),
    IterationPassageData α s q ζ Λ φ₀ hφ₀ bw K Pacc Q T₀ r₀ D₀ τe H J N p nk Naux Nout Kres npad σ₀ sX sZ Ce kS kI
      CI Cw j₀ C CQ mStar

theorem iterationPassage_of_split (h : IterationPassageSplit) :
    IterationPassage.Assembly.IterationPassageStatement := h

end AVRegularity.IterationPassage.Passage
end
end

section
/-! **The datum part of `iteration_passage` from the producer outputs**.

At a fixed common preparation (`PassagePair`), from the retained energy at the orders `0` and
`N_aux` (`EnergyOut`), the comparison (`CmpOut`), the strong energy (`StrongOut`), the profile
clauses (`ProfOut`) and the jets (`PassageErrorOutput`): the `PassageOutput`, with one
constant `C` above all the producers' constants.

* existence of the order-zero retained solution: `EnergyOut` at `k = 0`;
* the marked amplitude: the third clause of `RetainedSolutionClauses` at order `0`, after trace
  uniqueness;
* the regenerated block: `passageRegeneration`, the pointwise bound from the strong energy, the
  comparison;
* the profiles and the jets are the ingredients.

Special cases: empty families; `A = 0`; `N_aux = 0` (not allowed by the schedule, harmless). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.IterationPassage.ErrorJets
open AVRegularity.Construction.Preservation.Assembly

namespace AVRegularity.IterationPassage.Passage

section Generic

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The datum part of the conclusion of `preservation_successor` at one preparation (the text of
`PreservationSuccessorDataStatement` after the next family clauses), for a generic family type:
the retained energy at every order `k ≤ K_res` and the comparison of the order-`N_aux` solutions. -/
def PreservationRest (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G Gr : GenStage D hr Dm b j₀)
    (m p Naux N depth sX sZ Kres : ℕ) (η₀ s₀ tp tf cr Q C : ℝ) {Nout : ℕ}
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk Nout (hr v.1.root))) : Prop :=
  ∀ (f : ∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) (Ain : ℝ),
    weightedNorm 1 (G.mass law) (G.marker law) f ≤ Ain →
    (∀ k ≤ Kres, ∃ Y0 : ∀ v' : CompIn Gr.comps, TorusHk k (hr v'.1.root),
      IsRetainedTrace G Gr m p tp (Preg f) Y0 ∧
      RetainedSolutionClauses law P seedK freshK φ₀ hφ₀ Gr m k cr C Q Ain tp tf Y0) ∧
    ∀ (Y0 : ∀ v' : CompIn Gr.comps, TorusHk Naux (hr v'.1.root))
      (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (hr v.1.root))
      (Yw : ∀ v : CompIn Gr.comps, ℝ → TorusHk (Naux + 1) (hr v.1.root))
      (Yk : ∀ v u (_ : Gr.fam.Γ v u), ℝ → TorusHk (Naux + Dm - 1) (hr u.1.root)),
      IsRetainedTrace G Gr m p tp (Preg f) Y0 →
      Gr.IsRegSolution P seedK freshK φ₀ hφ₀ (D.κ (m - 1)) (streamVel (D.Φ (m - 1))) Naux tp tf Y0
        (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk →
      ComparisonClauses law P seedK freshK φ₀ hφ₀ G Gr m p Naux N depth sX sZ η₀ s₀ tp tf
        (C * D.eps (m - 1) ^ Q * Ain) (C * D.eps (m - 1) ^ Q * Ain) f Y

end Generic

end AVRegularity.IterationPassage.Passage

namespace AVRegularity.IterationPassage.ErrorJets.PassagePair

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} (X : PassagePair D Dm b j₀)

/-- A retained solution, back in the form of the statements. -/
theorem retSol_to_direct (k : ℕ) (Y0 : ∀ v' : CompIn X.Gr.comps, TorusHk k (ScalarH v'.1.root))
    (Y : ∀ v : CompIn X.Gr.comps, ℝ → TorusHk k (ScalarH v.1.root))
    (Yw : ∀ v : CompIn X.Gr.comps, ℝ → TorusHk (k + 1) (ScalarH v.1.root))
    (Yk : ∀ v u (_ : X.Gr.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (ScalarH u.1.root))
    (h : X.RetSol k Y0 Y Yw Yk) :
    X.Gr.IsRegSolution X.P X.seedK X.freshK X.φ₀ X.hφ₀ (D.κ (X.m - 1))
      (streamVel (D.Φ (X.m - 1))) k X.tp X.tf Y0 (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk := h

/-- The comparison clauses of `preservation_successor` at the pair. -/
def CmpOut (Cc : ℝ) : Prop :=
  ∀ (f : ∀ v : CompIn X.G.comps, TorusHk 0 (ScalarH v.1.root)) (Ain : ℝ), X.Marked f Ain →
  ∀ (Y0 : ∀ v' : CompIn X.Gr.comps, TorusHk X.Naux (ScalarH v'.1.root))
    (Y : ∀ v : CompIn X.Gr.comps, ℝ → TorusHk X.Naux (ScalarH v.1.root))
    (Yw : ∀ v : CompIn X.Gr.comps, ℝ → TorusHk (X.Naux + 1) (ScalarH v.1.root))
    (Yk : ∀ v u (_ : X.Gr.fam.Γ v u), ℝ → TorusHk (X.Naux + Dm - 1) (ScalarH u.1.root)),
    X.Trace f Y0 → X.RetSol X.Naux Y0 Y Yw Yk →
    ComparisonClauses X.law X.P X.seedK X.freshK X.φ₀ X.hφ₀ X.G X.Gr X.m X.p X.Naux X.N X.depth
      X.sX X.sZ X.η₀ X.s₀ X.tp X.tf (Cc * D.eps (X.m - 1) ^ X.Q * Ain)
      (Cc * D.eps (X.m - 1) ^ X.Q * Ain) f Y

/-- The retained energy at the pair from the datum part of `preservation_successor`. -/
theorem energyOut_of_rest (C : ℝ)
    (h : Passage.PreservationRest (hr := ScalarH) X.law X.P X.seedK X.freshK X.φ₀ X.hφ₀ X.G X.Gr
      X.m X.p X.Naux X.N X.depth X.sX X.sZ X.Kres X.η₀ X.s₀ X.tp X.tf X.cr X.Q C X.Preg) :
    X.EnergyOut C := fun f Ain hf => (h f Ain hf).1

/-- The comparison at the pair from the datum part of `preservation_successor`. -/
theorem cmpOut_of_rest (C : ℝ)
    (h : Passage.PreservationRest (hr := ScalarH) X.law X.P X.seedK X.freshK X.φ₀ X.hφ₀ X.G X.Gr
      X.m X.p X.Naux X.N X.depth X.sX X.sZ X.Kres X.η₀ X.s₀ X.tp X.tf X.cr X.Q C X.Preg) :
    X.CmpOut C := fun f Ain hf Y0 Y Yw Yk htr hsol => (h f Ain hf).2 Y0 Y Yw Yk htr hsol

/-- The strong energy of the regenerated solution in the marked weight. -/
def StrongOut (Cs : ℝ) : Prop :=
  ∀ (f : ∀ v : CompIn X.G.comps, TorusHk 0 (ScalarH v.1.root)) (Ain : ℝ), X.Marked f Ain →
  ∀ (Y0 : ∀ v' : CompIn X.Gr.comps, TorusHk X.Naux (ScalarH v'.1.root))
    (Y : ∀ v : CompIn X.Gr.comps, ℝ → TorusHk X.Naux (ScalarH v.1.root))
    (Yw : ∀ v : CompIn X.Gr.comps, ℝ → TorusHk (X.Naux + 1) (ScalarH v.1.root))
    (Yk : ∀ v u (_ : X.Gr.fam.Γ v u), ℝ → TorusHk (X.Naux + Dm - 1) (ScalarH u.1.root)),
    X.Trace f Y0 → X.RetSol X.Naux Y0 Y Yw Yk →
    strongEnergy (rhoEnh D X.cr X.m) (D.κ (X.m - 1))
      (fun v => X.Gr.mass X.law v / X.Gr.marker X.law v ^ 2) X.tp X.tf Y Yw ≤
        ENNReal.ofReal (Cs * Ain)

/-- The profile clauses at the pair. -/
def ProfOut (s mu wexp Pacc : ℝ) (Sr : KernelSpec) (C : ℝ) : Prop :=
  ∀ (f : ∀ v : CompIn X.G.comps, TorusHk 0 (ScalarH v.1.root)) (A : ℝ), X.Marked f A →
  ∀ (U : ∀ v : CompIn X.G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Uw : ∀ v : CompIn X.G.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
    (Uk : ∀ v u (_ : X.G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (ScalarH u.1.root)),
    X.IncSol f U Uw Uk →
  ∀ (Y0 : ∀ v' : CompIn X.Gr.comps, TorusHk 0 (ScalarH v'.1.root))
    (Y : ∀ v : CompIn X.Gr.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Yw : ∀ v : CompIn X.Gr.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
    (Yk : ∀ v u (_ : X.Gr.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (ScalarH u.1.root)),
    X.Trace f Y0 → X.RetSol 0 Y0 Y Yw Yk →
    PassageClauses D X.law X.G X.Gr X.m X.p X.N X.depth X.sX X.sZ X.K s X.η₀ mu wexp Pacc C A
      X.tp X.tf X.φ₀ Sr U Y

/-- The regenerated block of `PassageDatum`. -/
def RegenBlock (C A : ℝ) (f : ∀ v : CompIn X.G.comps, TorusHk 0 (ScalarH v.1.root))
    (Y : ∀ v : CompIn X.Gr.comps, ℝ → TorusHk 0 (ScalarH v.1.root)) : Prop :=
  ∃ (YN0 : ∀ v : CompIn X.Gr.comps, TorusHk X.Naux (ScalarH v.1.root))
    (YN : ∀ v : CompIn X.Gr.comps, ℝ → TorusHk X.Naux (ScalarH v.1.root))
    (YNw : ∀ v : CompIn X.Gr.comps, ℝ → TorusHk (X.Naux + 1) (ScalarH v.1.root))
    (YNk : ∀ v u (_ : X.Gr.fam.Γ v u), ℝ → TorusHk (X.Naux + Dm - 1) (ScalarH u.1.root)),
    X.Trace f YN0 ∧ X.RetSol X.Naux YN0 YN YNw YNk ∧
    (∀ v, ∀ t ∈ Set.Icc X.tp X.tf, truncateTorusHk (Nat.zero_le X.Naux) (YN v t) = Y v t) ∧
    (∀ t ∈ Set.Icc X.tp X.tf,
      weightedNorm (rhoEnh D X.cr X.m) (X.Gr.mass X.law) (X.Gr.marker X.law) (fun v => YN v t) ≤
        C * A) ∧
    strongEnergy (rhoEnh D X.cr X.m) (D.κ (X.m - 1))
        (fun v => X.Gr.mass X.law v / X.Gr.marker X.law v ^ 2) X.tp X.tf YN YNw ≤
      ENNReal.ofReal (C * A) ∧
    ComparisonClauses X.law X.P X.seedK X.freshK X.φ₀ X.hφ₀ X.G X.Gr X.m X.p X.Naux X.N X.depth
      X.sX X.sZ X.η₀ X.s₀ X.tp X.tf (C * D.eps (X.m - 1) ^ X.Q * A)
      (C * D.eps (X.m - 1) ^ X.Q * A) f YN

/-- Existence of the order-zero retained solution, in the form of `PassageOutput`. -/
theorem existsRetained (Cret : ℝ) (henergy : X.EnergyOut Cret)
    (f : ∀ v : CompIn X.G.comps, TorusHk 0 (ScalarH v.1.root)) (A : ℝ) (hfA : X.Marked f A) :
    ∃ (Y0 : ∀ v' : CompIn X.Gr.comps, TorusHk 0 (ScalarH v'.1.root))
      (Y : ∀ v : CompIn X.Gr.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
      (Yw : ∀ v : CompIn X.Gr.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
      (Yk : ∀ v u (_ : X.Gr.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (ScalarH u.1.root)),
      IsRetainedTrace X.G X.Gr X.m X.p X.tp (X.Preg f) Y0 ∧
      X.Gr.IsRegSolution X.P X.seedK X.freshK X.φ₀ X.hφ₀ (D.κ (X.m - 1))
        (streamVel (D.Φ (X.m - 1))) 0 X.tp X.tf Y0 (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk := by
  refine (henergy f A hfA 0 (Nat.zero_le _)).elim fun Y0 hY0 => ?_
  refine hY0.2.1.elim fun Y h1 => h1.elim fun Yw h2 => h2.elim fun Yk hY => ?_
  exact ⟨Y0, Y, Yw, Yk, hY0.1, X.retSol_to_direct 0 Y0 Y Yw Yk hY⟩

/-- The marked amplitude of the retained solution. -/
theorem datumAmplitude (Cret C : ℝ) (hC : Cret ≤ C) (hE : 0 ≤ D.eps (X.m - 1))
    (henergy : X.EnergyOut Cret)
    (f : ∀ v : CompIn X.G.comps, TorusHk 0 (ScalarH v.1.root)) (A : ℝ) (hfA : X.Marked f A)
    (Y0 : ∀ v' : CompIn X.Gr.comps, TorusHk 0 (ScalarH v'.1.root))
    (Y : ∀ v : CompIn X.Gr.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Yw : ∀ v : CompIn X.Gr.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
    (Yk : ∀ v u (_ : X.Gr.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (ScalarH u.1.root))
    (hY0 : X.Trace f Y0) (hY : X.RetSol 0 Y0 Y Yw Yk) :
    ∀ t ∈ Set.Icc X.tp X.tf,
      weightedNorm 1 (X.Gr.mass X.law) (X.Gr.marker X.law) (fun v => Y v t) ≤
        (1 + C * (D.eps (X.m - 1) ^ X.Q + D.eps (X.m - 1) ^ ocDelta D.α D.q)) * A := by
  intro t ht
  have hA : 0 ≤ A := (Real.sqrt_nonneg _).trans hfA
  refine (henergy f A hfA 0 (Nat.zero_le _)).elim fun Y00 h0 => ?_
  have htr0 := h0.1
  have hR0 := h0.2
  obtain rfl : Y0 = Y00 := retainedTrace_unique X.G X.Gr X.m X.p X.tp (X.Preg f) _ _ hY0 htr0
  have h3 := ((hR0.2 Y Y Yw Yw Yk Yk hY hY).2 (X.Gr.marker X.law) (Or.inr rfl) t ht).2.2
  have htr : (fun v => truncateTorusHk (Nat.zero_le 0) (Y v t)) = fun v => Y v t := by
    funext v
    exact torusHk_eq_of_jet_ae (IterationPassage.torus_truncate_value_ae (Nat.zero_le 0) (Y v t))
  rw [htr] at h3
  refine h3.trans (mul_le_mul_of_nonneg_right ?_ hA)
  have hpow : 0 ≤ D.eps (X.m - 1) ^ X.Q + D.eps (X.m - 1) ^ ocDelta D.α D.q :=
    add_nonneg (Real.rpow_nonneg hE _) (Real.rpow_nonneg hE _)
  linarith only [mul_le_mul_of_nonneg_right hC hpow]

/-- The regenerated block from the energy, the strong energy and the comparison. -/
theorem regenBlock (Cret Cs Cc C : ℝ) (hC0 : 0 ≤ C) (hCs : Cs ≤ C) (hCc : Cc ≤ C)
    (hE : 0 ≤ D.eps (X.m - 1)) (hNK : X.Naux ≤ X.Kres)
    (hπ : ∀ v, 0 < X.Gr.mass X.law v / X.Gr.marker X.law v ^ 2)
    (henergy : X.EnergyOut Cret) (hstrong : X.StrongOut Cs) (hcmp : X.CmpOut Cc)
    (f : ∀ v : CompIn X.G.comps, TorusHk 0 (ScalarH v.1.root)) (A : ℝ) (hfA : X.Marked f A)
    (Y0 : ∀ v' : CompIn X.Gr.comps, TorusHk 0 (ScalarH v'.1.root))
    (Y : ∀ v : CompIn X.Gr.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Yw : ∀ v : CompIn X.Gr.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
    (Yk : ∀ v u (_ : X.Gr.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (ScalarH u.1.root))
    (hY0 : X.Trace f Y0) (hY : X.RetSol 0 Y0 Y Yw Yk) : X.RegenBlock C A f Y := by
  have hA : 0 ≤ A := (Real.sqrt_nonneg _).trans hfA
  have hpow : 0 ≤ D.eps (X.m - 1) ^ X.Q := Real.rpow_nonneg hE _
  refine (henergy f A hfA 0 (Nat.zero_le _)).elim fun Y00 h0 => ?_
  refine (henergy f A hfA X.Naux hNK).elim fun YN0 hN => ?_
  have htrN := hN.1
  refine (passageRegeneration X.law X.P X.seedK X.freshK X.φ₀ X.hφ₀
    X.G X.Gr X.m X.p X.Naux X.cr Cret X.Q A X.tp X.tf (X.Preg f) Y00 YN0 h0.1 h0.2 htrN hN.2 Y0 Y Yw
    Yk hY0 hY).elim fun YN h1 => h1.elim fun YNw h2 => h2.elim fun YNk h3 => ?_
  have hYN := h3.1
  have hYNY := h3.2
  have hS := hstrong f A hfA YN0 YN YNw YNk htrN hYN
  have hS' : strongEnergy (rhoEnh D X.cr X.m) (D.κ (X.m - 1))
      (fun v => X.Gr.mass X.law v / X.Gr.marker X.law v ^ 2) X.tp X.tf YN YNw ≤
        ENNReal.ofReal (C * A) :=
    hS.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCs hA))
  refine ⟨YN0, YN, YNw, YNk, htrN, hYN, hYNY, fun t ht => ?_, hS', ?_⟩
  · have hw := EntryTerminal.Ingredients.weightedNorm_le_of_strongEnergy hπ ht
      (mul_nonneg hC0 hA) YN YNw hS'
    have hwe : weightedNorm (rhoEnh D X.cr X.m) (X.Gr.mass X.law) (X.Gr.marker X.law)
        (fun v => YN v t) = weightedNorm (rhoEnh D X.cr X.m)
          (fun v => X.Gr.mass X.law v / X.Gr.marker X.law v ^ 2) (fun _ => 1) (fun v => YN v t) := by
      unfold weightedNorm
      simp only [one_pow, div_one]
    rw [hwe]
    exact hw
  · exact comparisonClauses_mono (h := hcmp f A hfA YN0 YN YNw YNk htrN hYN)
      (hres := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCc hpow) hA)
      (he := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCc hpow) hA)

/-- The regenerated block in the form of `PassageDatum`. -/
theorem regenBlock_to_direct (C A : ℝ)
    (f : ∀ v : CompIn X.G.comps, TorusHk 0 (ScalarH v.1.root))
    (Y : ∀ v : CompIn X.Gr.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (h : X.RegenBlock C A f Y) :
    ∃ (YN0 : ∀ v : CompIn X.Gr.comps, TorusHk X.Naux (ScalarH v.1.root))
      (YN : ∀ v : CompIn X.Gr.comps, ℝ → TorusHk X.Naux (ScalarH v.1.root))
      (YNw : ∀ v : CompIn X.Gr.comps, ℝ → TorusHk (X.Naux + 1) (ScalarH v.1.root))
      (YNk : ∀ v u (_ : X.Gr.fam.Γ v u), ℝ → TorusHk (X.Naux + Dm - 1) (ScalarH u.1.root)),
      IsRetainedTrace X.G X.Gr X.m X.p X.tp (X.Preg f) YN0 ∧
      X.Gr.IsRegSolution X.P X.seedK X.freshK X.φ₀ X.hφ₀ (D.κ (X.m - 1))
        (streamVel (D.Φ (X.m - 1))) X.Naux X.tp X.tf YN0 (fun _ _ => 0) (fun _ _ => 0)
        YN YNw YNk ∧
      (∀ v, ∀ t ∈ Set.Icc X.tp X.tf, truncateTorusHk (Nat.zero_le X.Naux) (YN v t) = Y v t) ∧
      (∀ t ∈ Set.Icc X.tp X.tf,
        weightedNorm (rhoEnh D X.cr X.m) (X.Gr.mass X.law) (X.Gr.marker X.law)
          (fun v => YN v t) ≤ C * A) ∧
      strongEnergy (rhoEnh D X.cr X.m) (D.κ (X.m - 1))
          (fun v => X.Gr.mass X.law v / X.Gr.marker X.law v ^ 2) X.tp X.tf YN YNw ≤
        ENNReal.ofReal (C * A) ∧
      ComparisonClauses X.law X.P X.seedK X.freshK X.φ₀ X.hφ₀ X.G X.Gr X.m X.p X.Naux X.N X.depth
        X.sX X.sZ X.η₀ X.s₀ X.tp X.tf (C * D.eps (X.m - 1) ^ X.Q * A)
        (C * D.eps (X.m - 1) ^ X.Q * A) f YN := by
  exact Exists.elim h fun YN0 h1 => h1.elim fun YN h2 => h2.elim fun YNw h3 => h3.elim fun YNk h4 =>
    ⟨YN0, YN, YNw, YNk, h4.1, X.retSol_to_direct X.Naux YN0 YN YNw YNk h4.2.1, h4.2.2⟩

/-- The jet clauses are monotone in the constant. -/
theorem jetClauses_mono (C C' A : ℝ) (hC : C ≤ C') (hA : 0 ≤ A) (hE : 0 ≤ D.eps (X.m - 1))
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn X.G.comps) (fun v => ScalarH v.1.root))
    (aU : ℝ → Vec 2 → ∀ v : CompIn X.G.comps, ScalarH v.1.root)
    (aY : ℝ → Vec 2 → ∀ v : CompIn X.Gr.comps, ScalarH v.1.root)
    (h : PassageJetClauses X.law X.G X.Gr X.m X.p X.N X.depth X.K X.η₀ X.Q C X.c₀ A X.tp X.tf
      CcT aU aY) :
    PassageJetClauses X.law X.G X.Gr X.m X.p X.N X.depth X.K X.η₀ X.Q C' X.c₀ A X.tp X.tf
      CcT aU aY := by
  intro t ht
  obtain ⟨⟨Un, Uh, hUn, hUh, hb⟩, En, hEn, hbe⟩ := h t ht
  exact ⟨⟨Un, Uh, hUn, hUh, hb.trans (mul_le_mul_of_nonneg_right hC hA)⟩, En, hEn,
    hbe.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hE _)) hA)⟩

/-- **`PassageOutput` from the producer outputs at one common preparation.** -/
theorem passageOutput (s mu wexp Pacc : ℝ) (Sr : KernelSpec) (Cret Cs Cc Cj C : ℝ)
    (hC0 : 0 ≤ C) (hCret : Cret ≤ C) (hCs : Cs ≤ C) (hCc : Cc ≤ C) (hCj : Cj ≤ C)
    (hE : 0 ≤ D.eps (X.m - 1)) (hNK : X.Naux ≤ X.Kres)
    (hπ : ∀ v, 0 < X.Gr.mass X.law v / X.Gr.marker X.law v ^ 2)
    (henergy : X.EnergyOut Cret) (hstrong : X.StrongOut Cs) (hcmp : X.CmpOut Cc)
    (hprof : X.ProfOut s mu wexp Pacc Sr C)
    (hjet : PassageErrorOutput X.law X.P X.seedK X.freshK X.φ₀ X.hφ₀ X.G X.Gr X.m X.p X.N X.depth
      X.sX X.sZ X.K X.η₀ X.Q Cj X.c₀ X.s₀ X.tp X.tf X.Preg) :
    PassageOutput X.law X.P X.seedK X.freshK X.φ₀ X.hφ₀ X.G X.Gr X.m X.p X.N X.depth X.sX X.sZ
      X.K X.Naux s X.η₀ mu wexp Pacc X.Q C X.cr X.c₀ X.s₀ X.tp X.tf Sr X.Preg := by
  intro f A hfA U Uw Uk hU
  have hfA' : X.Marked f A := hfA
  have hA : 0 ≤ A := (Real.sqrt_nonneg _).trans hfA
  have hU' : X.IncSol f U Uw Uk := X.incSol_of_direct f U Uw Uk hU
  refine ⟨X.existsRetained Cret henergy f A hfA', fun Y0 Y Yw Yk hY0 hY => ?_⟩
  have hY' : X.RetSol 0 Y0 Y Yw Yk := X.retSol_of_direct 0 Y0 Y Yw Yk hY
  exact ⟨X.datumAmplitude Cret C hCret hE henergy f A hfA' Y0 Y Yw Yk hY0 hY',
    X.regenBlock_to_direct C A f Y (X.regenBlock Cret Cs Cc C hC0 hCs hCc hE hNK hπ henergy
      hstrong hcmp f A hfA' Y0 Y Yw Yk hY0 hY'),
    hprof f A hfA' U Uw Uk hU' Y0 Y Yw Yk hY0 hY',
    fun aU aY haU haY CcT hCcT => X.jetClauses_mono Cj C A hCj hA hE CcT aU aY
      (hjet f A hfA U Uw Uk hU Y0 Y Yw Yk hY0 hY CcT hCcT aU aY haU haY)⟩

end AVRegularity.IterationPassage.ErrorJets.PassagePair
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.IterationPassage.ErrorJets.PassagePair

/-! **The profile clauses at the pair from the profile proposition with producer outputs**.

* `PassagePair.ClausesOut`: the data part of `PassageProfileClausesStatement`
  (module `Passage.Profiles.ClausesStatement`) at the pair: `PassageClauses` for arbitrary families
  `U(t)`, `Y(t)` with lifts of orders `K + N + 2p + 4` and `N_aux` (the second with marked bound
  `C_r A`) and the jets at `C_j`.
* `PassagePair.BufferAt n`: every incoming solution has, at every time of the window, a lift of
  order `n` (the molecular buffer, truncated).
* `PassagePair.profOut_of_clausesOut`: `ProfOut` at the pair from `ClausesOut` at
  `(C_n, C_reg, |C_j|)`, the buffer, the regenerated block at `C_reg` (`regenBlock`) and the jets.

Special cases: `A = 0`; an empty family. `C_reg` is an intermediate constant: it must not depend on
the profile constant `C`. -/

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} (X : PassagePair D Dm b j₀)

/-- An incoming solution, back in the form of the statements. -/
theorem incSol_to_direct (f : ∀ v : CompIn X.G.comps, TorusHk 0 (ScalarH v.1.root))
    (U : ∀ v : CompIn X.G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Uw : ∀ v : CompIn X.G.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
    (Uk : ∀ v u (_ : X.G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (ScalarH u.1.root))
    (h : X.IncSol f U Uw Uk) :
    X.G.IsRegSolution X.P X.seedK X.freshK X.φ₀ X.hφ₀ (D.κ X.m) (streamVel (D.Φ X.m)) 0 X.s₀
      X.tf f (fun _ _ => 0) (fun _ _ => 0) U Uw Uk := h

/-- The profile proposition at the pair with the producer outputs as hypotheses. -/
def ClausesOut (s mu wexp Pacc : ℝ) (Sr : KernelSpec) (Cr Cj C : ℝ) : Prop :=
  ∀ A : ℝ, 0 ≤ A →
  ∀ (U : ∀ v : CompIn X.G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Y : ∀ v : CompIn X.Gr.comps, ℝ → TorusHk 0 (ScalarH v.1.root)),
    (∀ t ∈ Set.Icc X.tp X.tf, ∃ Un : ∀ v : CompIn X.G.comps,
      TorusHk (X.K + X.N + 2 * X.p + 4) (ScalarH v.1.root),
      ∀ v, truncateTorusHk (Nat.zero_le _) (Un v) = U v t) →
    (∀ t ∈ Set.Icc X.tp X.tf, ∃ Yn : ∀ v : CompIn X.Gr.comps,
      TorusHk X.Naux (ScalarH v.1.root),
      (∀ v, truncateTorusHk (Nat.zero_le _) (Yn v) = Y v t) ∧
      weightedNorm (rhoEnh D X.cr X.m) (X.Gr.mass X.law) (X.Gr.marker X.law) Yn ≤ Cr * A) →
    (∀ (aU : ℝ → Vec 2 → ∀ v : CompIn X.G.comps, ScalarH v.1.root)
        (aY : ℝ → Vec 2 → ∀ v : CompIn X.Gr.comps, ScalarH v.1.root),
      (∀ t ∈ Set.Icc X.tp X.tf,
        IsSmoothRep (fun v => U v t) (aU t) (X.K + X.N + 2 * X.p + 2)) →
      (∀ t ∈ Set.Icc X.tp X.tf,
        IsSmoothRep (fun v => Y v t) (aY t) (X.K + X.N + 2 * X.p + 2)) →
      ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn X.G.comps) (fun v => ScalarH v.1.root)),
        IsPassageLift X.G X.m X.N X.depth X.sX X.sZ CcT →
        PassageJetClauses X.law X.G X.Gr X.m X.p X.N X.depth X.K X.η₀ X.Q Cj X.c₀ A X.tp X.tf
          CcT aU aY) →
    PassageClauses D X.law X.G X.Gr X.m X.p X.N X.depth X.sX X.sZ X.K s X.η₀ mu wexp Pacc C A
      X.tp X.tf X.φ₀ Sr U Y

/-- Every incoming solution has a lift of order `n` at every time of the window. -/
def BufferAt (n : ℕ) : Prop :=
  ∀ (f : ∀ v : CompIn X.G.comps, TorusHk 0 (ScalarH v.1.root))
    (U : ∀ v : CompIn X.G.comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (Uw : ∀ v : CompIn X.G.comps, ℝ → TorusHk 1 (ScalarH v.1.root))
    (Uk : ∀ v u (_ : X.G.fam.Γ v u), ℝ → TorusHk (0 + Dm - 1) (ScalarH u.1.root)),
    X.IncSol f U Uw Uk →
    ∀ t ∈ Set.Icc X.tp X.tf, ∃ Un : ∀ v : CompIn X.G.comps, TorusHk n (ScalarH v.1.root),
      ∀ v, truncateTorusHk (Nat.zero_le _) (Un v) = U v t

/-- **The profile clauses at the pair** from the profile proposition with producer outputs. -/
theorem profOut_of_clausesOut (s mu wexp Pacc : ℝ) (Sr : KernelSpec) (Cret Cs Cc Creg Cj C : ℝ)
    (hR0 : 0 ≤ Creg) (hRs : Cs ≤ Creg) (hRc : Cc ≤ Creg) (hE : 0 ≤ D.eps (X.m - 1))
    (hNK : X.Naux ≤ X.Kres) (hπ : ∀ v, 0 < X.Gr.mass X.law v / X.Gr.marker X.law v ^ 2)
    (henergy : X.EnergyOut Cret) (hstrong : X.StrongOut Cs) (hcmp : X.CmpOut Cc)
    (hbuf : X.BufferAt (X.K + X.N + 2 * X.p + 4))
    (hjet : PassageErrorOutput X.law X.P X.seedK X.freshK X.φ₀ X.hφ₀ X.G X.Gr X.m X.p X.N X.depth
      X.sX X.sZ X.K X.η₀ X.Q Cj X.c₀ X.s₀ X.tp X.tf X.Preg)
    (h : X.ClausesOut s mu wexp Pacc Sr Creg |Cj| C) : X.ProfOut s mu wexp Pacc Sr C := by
  intro f A hf U Uw Uk hU Y0 Y Yw Yk htr hsol
  have hA : 0 ≤ A := (Real.sqrt_nonneg _).trans hf
  refine h A hA U Y (hbuf f U Uw Uk hU) ?_ ?_
  · intro t ht
    obtain ⟨YN0, YN, YNw, YNk, -, -, htrunc, hpt, -, -⟩ :=
      X.regenBlock Cret Cs Cc Creg hR0 hRs hRc hE hNK hπ henergy hstrong hcmp f A hf Y0 Y Yw Yk htr
        hsol
    exact ⟨fun v => YN v t, fun v => htrunc v t ht, hpt t ht⟩
  · intro aU aY haU haY CcT hCcT
    exact X.jetClauses_mono Cj |Cj| A (le_abs_self Cj) hA hE CcT aU aY
      (hjet f A hf U Uw Uk (X.incSol_to_direct f U Uw Uk hU) Y0 Y Yw Yk htr
        (X.retSol_to_direct 0 Y0 Y Yw Yk hsol) CcT hCcT aU aY haU haY)

end AVRegularity.IterationPassage.ErrorJets.PassagePair
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.IterationPassage.ErrorJets
open AVRegularity.Construction.Preservation.FullLift
open AVRegularity.Construction.Preservation.RetainedEnergy
namespace AVRegularity.IterationPassage.Passage

/-! **Stage layer of the retained strong energy**.

At a fixed stage: the native kernel operator of the retained family in the marked weight at order
`N_aux`, the common preparation, and the homogeneous regularized solution from a retained trace
give the strong energy bound `√2 * (C_pr * A_in)` (`common_preparation_retained_strongEnergy`). -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The strong energy of the retained solution from a retained trace, at a fixed stage, in the
marked weight, given the native kernel operator of the retained family at order `N_aux`. -/
theorem passageStrongEnergy_at_stage
    (law : BirthLaw) (P : ProvParams) (seedK freshK : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (G Gr : GenStage D hr Dm bw j₀)
    {cr Q CQ Cpr : ℝ} {p Nout Naux m : ℕ} {s tf tp : ℝ}
    (hlevel : G.level = m) (hST : G.comps ⊆ Gr.comps)
    (Preg : (∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk Nout (hr v.1.root)))
    (hprep : IsCommonPreparation law P seedK freshK φ₀ hφ₀ G cr Q CQ Cpr p Nout Naux s tf tp Preg)
    (f : ∀ v : CompIn G.comps, TorusHk 0 (hr v.1.root)) (Ain : ℝ)
    (hf : weightedNorm 1 (G.mass law) (G.marker law) f ≤ Ain)
    (Y0 : ∀ c : CompIn Gr.comps, TorusHk Naux (hr c.1.root))
    (htrace : IsRetainedTrace G Gr m p tp (Preg f) Y0)
    (hop : NativeEnergyOperatorAt P seedK freshK φ₀ hφ₀ Gr tp tf (rhoEnh D cr m)
      (D.κ (m - 1)) Naux (fun v => Gr.mass law v / Gr.marker law v ^ 2))
    (hφ : IsAdmissibleStream (D.Φ (m - 1)))
    (α B lam : ℝ) (hα : 0 ≤ α) (hBdrift : 1 ≤ B) (hlam : 0 < lam)
    (hsmall : B * rhoEnh D cr m / lam ≤ 1 / 2)
    (hstrain : α * B * rhoEnh D cr m ^ 2 ≤ D.κ (m - 1) / 8)
    (hjets : ∀ t ∈ Set.Icc tp tf, ∀ l, 1 ≤ l → l ≤ Naux → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (streamVel (D.Φ (m - 1)) t)) l x‖ ≤
        α * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (Y : ∀ v : CompIn Gr.comps, ℝ → TorusHk Naux (hr v.1.root))
    (Yw : ∀ v : CompIn Gr.comps, ℝ → TorusHk (Naux + 1) (hr v.1.root))
    (Yk : ∀ v u (_ : Gr.fam.Γ v u), ℝ → TorusHk (Naux + Dm - 1) (hr u.1.root))
    (hsol : HomRegSol P seedK freshK φ₀ hφ₀ Gr (D.κ (m - 1)) (streamVel (D.Φ (m - 1)))
      Naux tp tf Y0 Y Yw Yk) :
    strongEnergy (rhoEnh D cr m) (D.κ (m - 1))
      (fun v => Gr.mass law v / Gr.marker law v ^ 2) tp tf Y Yw ≤
        ENNReal.ofReal (Real.sqrt 2 * (Cpr * Ain)) := by
  subst hlevel
  obtain ⟨R, hB, hC, hS, hπ⟩ := hop
  exact common_preparation_retained_strongEnergy law P seedK freshK φ₀ hφ₀ G Gr rfl hST Preg
    hprep (fun c => compMarker D.q D.Λ law c) (Or.inr rfl) f Ain hf Y0 htrace R hB hC hS hπ hφ
    α B lam hα hBdrift hlam hsmall hstrain hjets Y Yw Yk hsol

end AVRegularity.IterationPassage.Passage
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleJointProofs AVRegularity.CycleJointProofs.Assembly
open AVRegularity.EntryTerminal.Ingredients
namespace AVRegularity.IterationPassage.Passage

/-! **The norm of the constant readout**.

`passageReadoutNorm`: the order-zero weighted bound of `succReadout` on constant fields bounds the
operator norm of `readoutCLM`. The constant fields are `X_{v'} = (√π'_{v'} z_{v'})`. -/

/-- The family of constant order-zero carriers with values `d`. -/
def readoutNormConst {S : Finset Comp} (d : CompIn S → ℝ) :
    ∀ v : CompIn S, TorusHk 0 (ScalarH v.1.root) :=
  fun v => torusConstantCarrier 0 (d v)

/-- The weighted norm of a constant family at order zero. -/
theorem readoutNorm_weightedNorm_const {S : Finset Comp} (ρ : ℝ) (π : CompIn S → ℝ)
    (d : CompIn S → ℝ) :
    weightedNorm (hr := ScalarH) ρ π (fun _ => 1) (readoutNormConst d) =
      Real.sqrt (∑ v, (π v)⁻¹ * d v ^ 2) := by
  rw [weightedNorm_one_eq]
  unfold massNormSq
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  have := constant_factorialNormSq (E := ℝ) 0 ρ (d v)
  simpa only [readoutNormConst, Real.norm_eq_abs, sq_abs] using
    congrArg (fun t => (π v)⁻¹ * t) this

/-- The readout of constant fields is the constant field of the matrix action. -/
theorem readoutNorm_succReadout_const {S S' : Finset Comp} (m : ℕ) (E η₀ : ℝ)
    (c : CompIn S' → ℝ) :
    succReadout (hr := ScalarH) (S := S) m E η₀ 0 (readoutNormConst c) =
      readoutNormConst (fun v : CompIn S => ∑ v' : CompIn S', if compParent m v'.1 = v.1 then
        E ^ (η₀ * ((compWord m v'.1).length : ℝ)) * c v' else 0) := by
  funext v
  unfold succReadout readoutNormConst
  change _ = torusConstantLinearMap (E := ℝ) 0 _
  rw [map_sum]
  refine Finset.sum_congr rfl fun v' _ => ?_
  by_cases h : compParent m v'.1 = v.1
  · simp only [h, dite_true, ite_true]
    change _ • torusConstantCarrier 0 (c v') = torusConstantLinearMap (E := ℝ) 0 _
    generalize E ^ (η₀ * ((compWord m v'.1).length : ℝ)) = a
    exact (map_smul (torusConstantLinearMap (E := ℝ) 0) a (c v')).symm
  · simp only [h, dite_false, ite_false]
    exact (map_zero _).symm

/-- **The norm of the constant readout from the order-zero weighted bound.** -/
theorem passageReadoutNorm : PassageReadoutNormStatement := by
  intro S S' m E η₀ ρ B π π' hπ hπ' hB h
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro z
  have key := h (readoutNormConst (fun v' => Real.sqrt (π' v') * z v'))
  rw [readoutNorm_succReadout_const, readoutNorm_weightedNorm_const,
    readoutNorm_weightedNorm_const] at key
  have hz : ∑ v', (π' v')⁻¹ * (Real.sqrt (π' v') * z v') ^ 2 = ‖z‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_congr rfl fun v' _ => ?_
    have := Real.sq_sqrt (hπ' v').le
    rw [mul_pow, this, Real.norm_eq_abs, sq_abs]
    field_simp [(hπ' v').ne']
  rw [hz, Real.sqrt_sq (norm_nonneg _)] at key
  refine le_trans (le_of_eq ?_) key
  change ‖Matrix.toLpLin 2 2 (readoutMatrix m E η₀ π π') z‖ = _
  rw [PiLp.norm_eq_of_L2]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  have hsq := Real.sq_sqrt (hπ v).le
  have hsp := Real.sqrt_pos.2 (hπ v)
  simp only [Matrix.toLpLin_apply, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct,
    Real.norm_eq_abs, sq_abs, readoutMatrix]
  have e : (∑ v', (if compParent m v'.1 = v.1 then
      (Real.sqrt (π v))⁻¹ * E ^ (η₀ * ((compWord m v'.1).length : ℝ)) * Real.sqrt (π' v') else 0)
        * z v') = (Real.sqrt (π v))⁻¹ * ∑ v', (if compParent m v'.1 = v.1 then
        E ^ (η₀ * ((compWord m v'.1).length : ℝ)) * (Real.sqrt (π' v') * z v') else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v' _ => ?_
    split_ifs <;> ring
  rw [e, mul_pow, inv_pow, hsq]

end AVRegularity.IterationPassage.Passage
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open AVRegularity.IterationPassage.ErrorJets
namespace AVRegularity.IterationPassage.Passage

/-! **Data layer of the retained strong energy**.

The certificates at the data (the same as in `prepared_retained_energy_at_data`) give the native
kernel operator of the retained family at order `K_res`; its restriction to order `N_aux` in the
marked weight and the stage layer give the strong energy bound at scalar families. -/

open AVRegularity.Construction.Preservation.RetainedEnergy
open AVRegularity.Construction.Preservation.FullLift
open CycleComparison.Coarse
open AVRegularity.Construction.Preservation AVRegularity.Construction AVRegularity

/-- The strong energy of the retained solution at the data, with thresholds fixed before
OCData, the law and the component spaces. -/
theorem passage_strongEnergy_at_data {α s q : ℝ}
    (hq : IsAdmissibleQ α s q)
    {ζ : ℝ → ℝ} (Λl Λ : ℕ)
    (hlength : UniformRecordLengths α q ζ Λl) (hΛ : Λl ≤ Λ) (h128 : 128 ≤ Λ)
    (hζ : IsFastProfile ζ)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw : ℝ)
    (Q T₀ Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout Kres npad sX sZ : ℕ)
    (σ₀ : ℝ) (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr : ℝ) (mc : ℕ)
    (hNaux : Naux ≤ Kres)
    (hc : RetainedCertificatesAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS
      r₀ D₀ H J N p nk npad sX sZ σ₀ kI CI Cw j₀ mc)
    (hprod : kI.Hprod = kI.G0 + H + 1) (hc0pos : 0 < kI.c₀) (hc0le : kI.c₀ ≤ 1)
    (_hcrpos : 0 < kI.cr) (hcrle : kI.cr ≤ 1) (mr : ℕ) (hmr : 2 ≤ mr)
    (hradius : EnhancedRadiusAt α q ζ Λ kI.c₀ kI.cr mr) (md : ℕ)
    (hdrift : EnhancedDriftAt α q ζ Λ kI.cr md) (A : ℝ) (mo : ℕ)
    (hop : NativeKernelOperatorsAt α q ζ Λ bw Kres (succSchedD D₀ N p (H + 1)) kI.cker A mo)
    (ma : ℕ)
    (habs : ∀ m, ma ≤ m → A * (CI * ocEpsilon q Λ (m - 1) ^ min (ocDelta α q / 4) τe) < 1 / 8)
    (C : ℝ) (hC : Real.sqrt 2 * |Cpr| ≤ C) :
    PassageRetainedStrongEnergyData α s q ζ Λ φ₀ hφ₀ bw Ce τe kS
      r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ C
      (max mc (max mr (max md (max (mo + 3) (max ma (j₀ + 3)))))) := by
  classical
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA s₀ htA hdelay hwindow _hT G G' hcascade hlevel hG hactual tp Preg hprep
    f Ain hf Y0 Y Yw Yk htrace hsol
  have hmc : mc ≤ m := by omega
  have hmr' : mr ≤ m := by omega
  have hmd' : md ≤ m := by omega
  have hmo' : mo + 1 ≤ m - 1 := by omega
  have hma : ma ≤ m := by omega
  have hjGr' : j₀ ≤ m - 1 := by omega
  have hm2 : 2 ≤ m := by omega
  have hiGr' : 1 ≤ m - 1 := by omega
  have hm1 : 1 ≤ m := by omega
  have hmterm : m ≤ D.term := by rw [hterm]; exact hn.trans hnM.le
  have hqD : 1 < D.q := by rw [hDq]; exact hq.1
  have hΛD : 128 ≤ D.Λ := by rw [hDΛ]; exact h128
  have hζD : IsFastProfile D.ζ := hDζ.symm ▸ hζ
  have hbandD : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    simpa only [hDα, hDq, hDΛ, hDζ, hterm] using hband
  let P := succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p
  let Mn := succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)
  let Gr := G'.retained m H J
  have hGrlevel : Gr.level = m - 1 := by
    change G'.level = m - 1
    rw [hactual.2.1, hlevel]
  have hGrlevelterm : Gr.level ≤ D.term := by omega
  have hGrI := hc D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m hmc hn hnM tA htA G G' hcascade hlevel hG hactual
  obtain ⟨hnat, hshift, hslot, hctx, hled, hker⟩ := hGrI
  have hcGr : IsCascadeStage D P Mn seed Gr := by
    simpa only [hlevel, succMenu, Mn, Gr, P] using IsCascadeStage.step hcascade hactual
  have hprod' : kI.Hprod = kI.G0 + Mn.H + 1 := hprod
  have hmGr v : 0 ≤ compReserve kI (v : CompIn Gr.comps).1 :=
    (Buffer.cascade_component_reserve_pos hseed.2.1 hcGr kI hprod' v).le
  have hm2Gr v : compReserve kI (v : CompIn Gr.comps).1 ≤ 2 :=
    (Buffer.compReserve_le_one kI v.1).trans (by norm_num)
  have hseedI := hseed.2.2.2.2.2.2.2.1
  have hlens : ∀ v u (γ : seed.fam.Γ v u), 1 ≤ (seed.fam.identity v u γ).record.birthExcess →
      (seed.fam.identity v u γ).record.length ≤ D.eps seed.level := by
    intro v u γ hb
    simpa only [hseed.1] using (hseed.2.2.2.2.2.1 v u γ).2.2 hb
  have hlenGr := hlength ScalarH D hDα hDq hDζ (by rw [hDΛ]; omega) hbandD
    _ bw j₀ Mn Cw kI.cr σ₀ (succEta0 α q s) N p hcrle seed Gr hseedI.2.1 hlens
    (by rw [hseed.1, hterm]; exact hnM.le) hcGr (hGrlevel.symm ▸ hiGr')
  have he (l : ℕ) : 0 < D.eps l := Construction.Stream.ocEpsilon_pos (by omega)
  have hκ (l : ℕ) (hl : l ≤ D.term) : 0 < D.κ l :=
    CycleReference.bandChain_pos (by omega) hζD hbandD hl
  have ha (l : ℕ) : 0 < ocA D.α D.q D.Λ l := Real.rpow_pos_of_pos (he l) _
  have hrs (l : ℕ) (hl : l ≤ D.term) :
      0 < rhoStar D kI.c₀ l ∧ rhoStar D kI.c₀ l ≤ D.eps l := by
    have hh := Buffer.molecular_radius_bounds hc0pos (he l) (hκ l hl) (ha l)
    exact ⟨hh.1, hh.2.1.trans (mul_le_of_le_one_left (he l).le hc0le)⟩
  have hrhos := hradius D hDα hDq hDΛ hDζ hbandD m hmr' hmterm
  have hρe : rhoEnh D kI.cr m ≤ D.eps Gr.level := by
    rw [hGrlevel]
    exact hrhos.trans (hrs (m - 1) (by omega)).2
  have hρE : rhoEnh D kI.cr m ≤ D.eps (Gr.level - 1) :=
    hρe.trans (EntryScales.epsilon_antitone hqD (by omega) (Nat.sub_le _ _))
  have hd := hdrift D.Φ hseq M D.κ hband m hmd' (hn.trans hnM.le)
  have hρpos : 0 < rhoEnh D kI.cr m := by
    simpa only [rhoEnh, hDα, hDq, hDΛ] using hd.2.1
  have htptf : tp ≤ tf := by
    have hh := hprep.2.2.1
    rw [hlevel, hDα, hDq, hDΛ] at hh
    exact hh.trans hwindow
  have hsub : Set.Icc tp tf ⊆ Set.Icc (tA + 3 * ocTau α q Λ m) tf := by
    intro t ht
    exact ⟨(hdelay.trans hprep.2.1).trans ht.1, ht.2⟩
  have hSzero : ∀ v u (γ : Gr.fam.Γ v u), IsSpatialRegularizerTorus (rhoEnh D kI.cr m) 0
      (succSchedD D₀ N p (H + 1)) tp tf kI.cker
      (Gr.kernelOf P seedK freshK v u γ).width (Gr.sysS P seedK freshK φ₀ hφ₀ v u γ) := by
    intro v u γ
    exact Buffer.spatialRegularizerTorus_time_restrict ((hker v u γ).2 _ hρpos) hsub
  have hkap : D.kap Gr.level = D.κ (m - 1) := by
    change D.κ (min Gr.level D.term) = _
    rw [Nat.min_eq_left hGrlevelterm, hGrlevel]
  have hsmall : A * (CI * D.eps (m - 1) ^ min (ocDelta α q / 4) τe) < 1 / 8 := by
    simpa only [OCData.eps, hDq, hDΛ] using habs m hma
  have hlengthop : ∀ v u (γ : Gr.fam.Γ v u), 3 ≤ (Gr.fam.identity v u γ).maxOrder →
      (Gr.fam.identity v u γ).record.length ≤ D.eps (Gr.level - 1) := by
    intro v u γ hj
    have hb : 1 ≤ (Gr.fam.identity v u γ).record.birthExcess := by
      have hh := (Gr.fam.identity v u γ).le_birth
      omega
    exact (hlenGr v u γ hb).trans
      (EntryScales.epsilon_antitone hqD (by omega) (Nat.sub_le _ _))
  have hop' := hop ScalarH D hDα hDq hDΛ hDζ hseq j₀ Mnat Gr kI hctx hnat hshift
    (hGrlevel.symm ▸ hmo') (hGrlevel.symm ▸ hiGr') (hGrlevel.symm ▸ hjGr')
    (he _) (he _) (by rw [hkap]; exact hd.1)
    hslot hmGr hm2Gr P seedK freshK (fun v u γ => (hker v u γ).1) φ₀ hφ₀ tp tf
    (rhoEnh D kI.cr m) (CI * D.eps (m - 1) ^ min (ocDelta α q / 4) τe)
    (Gr.mass law) (Gr.marker law) htptf hρpos hρE hρe hlengthop
    (fun v => Buffer.birth_compMass_pos hqD hΛD law v.1)
    (fun v => Buffer.birth_compMarker_pos hqD hΛD law v.1) hled hsmall.le hSzero
  rw [hkap] at hop'
  have hφ : IsAdmissibleStream (D.Φ (m - 1)) := (hseq.2 m hm1).choose
  let αv := Buffer.actualDriftJetConstant * ocA α q Λ (m - 1)
  have hαv : 0 ≤ αv := mul_nonneg Buffer.actualDriftJetConstant_nonneg
    (Real.rpow_pos_of_pos (Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ Λ)) _).le
  have hsmallD : 1024 * rhoEnh D kI.cr m / D.eps (m - 1) ≤ 1 / 2 := by
    simpa only [rhoEnh, OCData.eps, hDα, hDq, hDΛ] using hd.2.2.1
  have hstrain : αv * 1024 * rhoEnh D kI.cr m ^ 2 ≤ D.κ (m - 1) / 8 := by
    simpa only [αv, rhoEnh, hDα, hDq, hDΛ] using hd.2.2.2.1
  have hjets : ∀ t ∈ Set.Icc tp tf, ∀ j, 1 ≤ j → j ≤ Kres → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (streamVel (D.Φ (m - 1)) t)) j x‖ ≤
        αv * 1024 ^ j * (j.factorial : ℝ) * D.eps (m - 1) ^ ((1 : ℤ) - j) := by
    intro t _ j hj _ x
    simpa only [αv, OCData.eps, hDq, hDΛ] using hd.2.2.2.2 t j hj x
  have hST : G.comps ⊆ Gr.comps :=
    incoming_mem_retained_of_cascade hseed.2.1 hcascade hactual hlevel
  have hoplower : NativeEnergyOperatorAt P seedK freshK φ₀ hφ₀ Gr tp tf (rhoEnh D kI.cr m)
      (D.κ (m - 1)) Naux (fun v => Gr.mass law v / Gr.marker law v ^ 2) := by
    obtain ⟨R, hB, hC', hS, hπ, hr', hck, _⟩ := hop' (Gr.marker law) (Or.inr rfl)
    let Rk := kernelOperator_order_restrict R hNaux (fun v u γ => by
      rw [hck, hr', hS]
      exact spatial_regularizer_all_orders _ _ _ _ _ _ _ (hSzero v u γ) Naux)
    exact ⟨Rk, hB, hC', hS, hπ⟩
  have hE := passageStrongEnergy_at_stage law P seedK freshK φ₀ hφ₀ G Gr hlevel hST Preg hprep
    f Ain hf Y0 htrace hoplower hφ αv 1024 (D.eps (m - 1)) hαv (by norm_num) (he _) hsmallD
    hstrain (fun t ht l hl hlk x => hjets t ht l hl (hlk.trans hNaux) x) Y Yw Yk hsol
  refine hE.trans (ENNReal.ofReal_le_ofReal ?_)
  have hA : 0 ≤ Ain := (Real.sqrt_nonneg _).trans hf
  have h2 : Real.sqrt 2 * (Cpr * Ain) ≤ Real.sqrt 2 * (|Cpr| * Ain) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self _) hA) (Real.sqrt_nonneg _)
  calc Real.sqrt 2 * (Cpr * Ain) ≤ Real.sqrt 2 * (|Cpr| * Ain) := h2
    _ = Real.sqrt 2 * |Cpr| * Ain := by ring
    _ ≤ C * Ain := mul_le_mul_of_nonneg_right hC hA

end AVRegularity.IterationPassage.Passage
end
end
end
