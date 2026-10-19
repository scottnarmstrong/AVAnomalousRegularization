-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.PaperFacing.CycleSupplement
public import AVRegularity.Proofs.ComplexChain.Vel
public import AVRegularity.Statements.Intermediate.KernelEnergy.SpatialRegularizerTorus
import AVRegularity.Construction.InitialValue.Cascade
import AVRegularity.Construction.Preservation.Buffer.KernelFluxTruncation
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
import AVRegularity.Construction.Preservation.RetainedEnergy.UniformInputs
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.CycleReference.FluxFastDiscrepancy
import AVRegularity.Definitions.Finite.FiniteLiftBridge
import AVRegularity.IterationPassage.Passage.StrongEnergyData
import AVRegularity.Proofs.ComplexVel.Main
import AVRegularity.Proofs.Results.Iteration.PassageKernelSup

/-! # Admissible families by descent (Section 10 of the paper)

At the parameters `cfg` and a bottom level `m₀`, with the prefix `PRE` of
`PaperStepStatementAt` (the data `D`, the band chain of terminal level `M`, `M ≤ M_nat`, the
successor law, the seed and fresh kernels):

* `PaperSuccessorAdmissibleStatement` (the step): the retained part of an actual successor of an
  admissible family of level `m > m₀` on `[t_A, t_f]`, `t_A + 3τ_m + 4τ''_m ≤ t_f`, is admissible
  of level `m - 1` on `[t_A + 3τ_m, t_f]`.
* `PaperSeedFamilyStatement` (the base case): an admissible seed of level `n > m₀` on
  `[t_S, t_f]`, `t_S + t₀/2 < t_f`, is an admissible family on `[t_S, t_f]`.
* `PaperCascadeChainStatement` (the chain and its windows): an admissible seed has a chain of
  actual successors down to `m₀`, with the windows `t_A^{(j)} = paperDescentStart`.
* `PaperSuccessorWeightsStatement`: the old components of a cascade stage are kept by every actual
  successor, the retained mass is at most twice the seed mass, the readout is near the identity;
  `paper_newcomp_weights`: the mass, marker and readout factor of a new component.
* `PaperAdmissibleByDescent`, `PaperDescentFamilyStatement`: a family admissible by descent is an
  admissible family; `PaperAdmissibleByDescent.extend`: descent extends by one actual successor.
* `PaperFreshInverseStatement`: the spanning matrices of the fresh axes above `m₁` have inverse at
  most `2`; `PaperFreshSmoothingStatement`: at source level, a fresh smoothing of a source of an
  admissible family of level `m ≥ m₀` is born at a level `b ≥ m`, has spanning inverse at most
  `2`, and is a spatial regularizer with constants depending on `(φ₀, n_k)` only.
* `PaperComplexChainStatement`: the complex chain lemma (`chainFam_over`) at the carrier start of
  the parameters.
* `paper_section10_of_parameters`: all of the above at one `m₀ ≥ paperBottom P`.

The statements are monotone in `m₀` (`.mono`). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal

namespace AVRegularity.PaperFacing

open AVRegularity.Finite.Assembly

/-! ### Monotonicity in the bottom level -/

/-- `PaperStepStatementAt` is monotone in the bottom level. -/
theorem PaperStepStatementAt.mono {cfg : FiniteParameters} {m₀ m₀' : ℕ} {C : ℝ}
    (h : PaperStepStatementAt cfg m₀ C) (hle : m₀ ≤ m₀') : PaperStepStatementAt cfg m₀' C :=
  fun D hDα hDq hDΛ hDζ hDΦ M hband hterm Mnat hMnat law hlaw seedK freshK hfresh m hm =>
    h D hDα hDq hDΛ hDζ hDΦ M hband hterm Mnat hMnat law hlaw seedK freshK hfresh m
      (lt_of_le_of_lt hle hm)

/-- `PaperCascadeStatement` is monotone in the bottom level. -/
theorem PaperCascadeStatement.mono {cfg : FiniteParameters} {m₀ m₀' : ℕ} {C : ℝ}
    (h : PaperCascadeStatement cfg m₀ C) (hle : m₀ ≤ m₀') : PaperCascadeStatement cfg m₀' C :=
  fun D hDα hDq hDΛ hDζ hDΦ M hband hterm Mnat hMnat law hlaw seedK freshK hfresh seed n tS tf
      hn =>
    h D hDα hDq hDΛ hDζ hDΦ M hband hterm Mnat hMnat law hlaw seedK freshK hfresh seed n tS tf
      (lt_of_le_of_lt hle hn)

/-! ### The step -/

/-- **The step** (Proposition 4.3(b) of the paper): the retained part of an actual successor of an
admissible family of level `m > m₀` on `[t_A, t_f]` with `t_A + 3τ_m + 4τ''_m ≤ t_f` is an
admissible family of level `m - 1` on `[t_A + 3τ_m, t_f]`. -/
def PaperSuccessorAdmissibleStatement (cfg : FiniteParameters) (m₀ : ℕ) : Prop :=
  ∀ (D : OCData), D.α = cfg.α → D.q = cfg.q → D.Λ = cfg.Λ → D.ζ = cfg.ζ →
    IsOCStreamSeq cfg.α cfg.q cfg.Λ cfg.ζ D.Φ →
  ∀ (M : ℕ), IsOCBandChain cfg.α cfg.q cfg.Λ cfg.ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
  ∀ (law : BirthLaw), IsSuccessorLaw cfg.α cfg.q cfg.s (paperWordCount cfg) law →
  ∀ (seedK freshK : ℕ → KernelSpec),
    (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D cfg.kI.cr cfg.σ₀ cfg.nk.toPNat' b' (freshK b')) →
  ∀ (m : ℕ), m₀ < m →
  ∀ (tA tf : ℝ) (G G' : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀),
    IsPaperFamily cfg M Mnat law seedK freshK G m tA tf →
    tA + 3 * ocTau cfg.α cfg.q cfg.Λ m + 4 * ocTauPP cfg.α cfg.q cfg.Λ m ≤ tf →
    IsActualSuccessor D (paperProv cfg D) (paperMenu cfg Mnat) G G' →
    IsPaperFamily cfg M Mnat law seedK freshK (G'.retained m cfg.H cfg.J) (m - 1)
      (tA + 3 * ocTau cfg.α cfg.q cfg.Λ m) tf

/-- The step from one cycle with a free history start (`t_c = t_A + 3τ_m`). -/
theorem paper_successor_admissible_of_step_at {cfg : FiniteParameters} {m₀ : ℕ} {C : ℝ}
    (h : PaperStepStatementAt cfg m₀ C) : PaperSuccessorAdmissibleStatement cfg m₀ := by
  intro D hDα hDq hDΛ hDζ hDΦ M hband hterm Mnat hMnat law hlaw seedK freshK hfresh m hm tA tf G
    G' hG hwin hsucc
  obtain ⟨tp, Preg, hcyc, -, -⟩ := h D hDα hDq hDΛ hDζ hDΦ M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh m hm tA (tA + 3 * ocTau cfg.α cfg.q cfg.Λ m) tf G G' hG le_rfl hwin hsucc
  exact hcyc.2.1

/-- The step at the parameters `P`, `m₀ = paperBottom P`. -/
theorem paper_successor_admissible_of_parameters {α s q : ℝ} {ζ : ℝ → ℝ} {Λ Jw : ℕ} {t₀ T₀ : ℝ}
    (hs₀ : 0 < s) (hΛ : 128 ≤ Λ) (ht₀ : 0 < t₀) (htT : t₀ < T₀)
    (P : PaperParameters α s q ζ Λ Jw t₀ T₀) :
    PaperSuccessorAdmissibleStatement P.ready.cfg (paperBottom P) := by
  obtain ⟨C, -, -, hstep, -⟩ := paper_cascade_at_of_parameters hs₀ hΛ ht₀ htT P
  exact paper_successor_admissible_of_step_at hstep

/-- The step is monotone in the bottom level. -/
theorem PaperSuccessorAdmissibleStatement.mono {cfg : FiniteParameters} {m₀ m₀' : ℕ}
    (h : PaperSuccessorAdmissibleStatement cfg m₀) (hle : m₀ ≤ m₀') :
    PaperSuccessorAdmissibleStatement cfg m₀' :=
  fun D hDα hDq hDΛ hDζ hDΦ M hband hterm Mnat hMnat law hlaw seedK freshK hfresh m hm =>
    h D hDα hDq hDΛ hDζ hDΦ M hband hterm Mnat hMnat law hlaw seedK freshK hfresh m
      (lt_of_le_of_lt hle hm)

/-! ### The base case -/

/-- **The base case** (Lemma 10.B): an admissible seed of level `n > m₀` on `[t_S, t_f]`,
`t_S + t₀/2 < t_f`, is an admissible family of level `n` on `[t_S, t_f]`. -/
def PaperSeedFamilyStatement (cfg : FiniteParameters) (m₀ : ℕ) : Prop :=
  ∀ (D : OCData), D.α = cfg.α → D.q = cfg.q → D.Λ = cfg.Λ → D.ζ = cfg.ζ →
    IsOCStreamSeq cfg.α cfg.q cfg.Λ cfg.ζ D.Φ →
  ∀ (M : ℕ), IsOCBandChain cfg.α cfg.q cfg.Λ cfg.ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
  ∀ (law : BirthLaw), IsSuccessorLaw cfg.α cfg.q cfg.s (paperWordCount cfg) law →
  ∀ (seedK freshK : ℕ → KernelSpec),
    (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D cfg.kI.cr cfg.σ₀ cfg.nk.toPNat' b' (freshK b')) →
  ∀ (seed : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀) (n : ℕ) (tS tf : ℝ),
    m₀ < n → tS + cfg.t₀ / 2 < tf →
    IsPaperSeed cfg M Mnat law seedK freshK seed n tS tf →
    IsPaperFamily cfg M Mnat law seedK freshK seed n tS tf

/-- The base case at the parameters `P`, `m₀ = paperBottom P`. -/
theorem paper_seed_family_of_parameters {α s q : ℝ} {ζ : ℝ → ℝ} {Λ Jw : ℕ} {t₀ T₀ : ℝ}
    (_hΛ : 128 ≤ Λ) (P : PaperParameters α s q ζ Λ Jw t₀ T₀) :
    PaperSeedFamilyStatement P.ready.cfg (paperBottom P) := by
  intro D hDα hDq hDΛ hDζ hDΦ M hband hterm Mnat hMnat law hlaw seedK freshK hfresh seed n tS tf
    hn htS hseedP
  have hm₀ : P.ready.cfg.m₀ < n :=
    lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hn
  obtain ⟨stage, ext, hist, st, tp, Preg, hframe, -⟩ :=
    P.ready.cascade D hDα hDq hDΛ hDζ hDΦ M hband hterm Mnat hMnat law hlaw seedK freshK hfresh
      seed n tS tf htS hseedP.2.2.2 hseedP.1 hseedP.2.1 hm₀ hseedP.2.2.1
  have hinv := (hframe.2.2.2.2.1 n hm₀.le le_rfl).2.2.1
  rw [hframe.1, hframe.2.1, hDα, hDq] at hinv
  exact ⟨tS, seed, n, le_rfl, hseedP, IsCascadeStage.seed, hseedP.1.1, hinv⟩

/-- The base case is monotone in the bottom level. -/
theorem PaperSeedFamilyStatement.mono {cfg : FiniteParameters} {m₀ m₀' : ℕ}
    (h : PaperSeedFamilyStatement cfg m₀) (hle : m₀ ≤ m₀') : PaperSeedFamilyStatement cfg m₀' :=
  fun D hDα hDq hDΛ hDζ hDΦ M hband hterm Mnat hMnat law hlaw seedK freshK hfresh seed n tS tf
      hn =>
    h D hDα hDq hDΛ hDζ hDΦ M hband hterm Mnat hMnat law hlaw seedK freshK hfresh seed n tS tf
      (lt_of_le_of_lt hle hn)

/-! ### The chain and its windows -/

/-- The start `t_A^{(j)} = t_S + ∑_{j < k ≤ m_S} 3τ_k` of the window of the level-`j` family of a
descent from a seed of level `m_S` on `[t_S, t_f]` ((10.6)). -/
def paperDescentStart (cfg : FiniteParameters) (tS : ℝ) (mS j : ℕ) : ℝ :=
  tS + ∑ k ∈ Finset.Ioc j mS, 3 * ocTau cfg.α cfg.q cfg.Λ k

/-- `t_A^{(m_S)} = t_S`. -/
private theorem paperDescentStart_self (cfg : FiniteParameters) (tS : ℝ) (mS : ℕ) :
    paperDescentStart cfg tS mS mS = tS := by
  simp [paperDescentStart]

/-- `t_A^{(j)} = t_A^{(j+1)} + 3τ_{j+1}` for `j < m_S`. -/
private theorem paperDescentStart_succ (cfg : FiniteParameters) (tS : ℝ) {mS j : ℕ}
    (hj : j < mS) :
    paperDescentStart cfg tS mS j =
      paperDescentStart cfg tS mS (j + 1) + 3 * ocTau cfg.α cfg.q cfg.Λ (j + 1) := by
  unfold paperDescentStart
  rw [← Finset.sum_Ioc_consecutive _ (Nat.le_succ j) (Nat.succ_le_of_lt hj),
    Nat.Ioc_succ_singleton, Finset.sum_singleton]
  ring

/-- A history start with `a_{m_S} = t_S` and `a_{j-1} = a_j + 3τ_j` above `m₀` is the descent
start. -/
private theorem paper_hist_eq_descentStart (cfg : FiniteParameters) (hist : ℕ → ℝ) (tS : ℝ)
    {m₀ n : ℕ} (hn : hist n = tS)
    (hstep : ∀ j, m₀ < j → j ≤ n → hist (j - 1) = hist j + 3 * ocTau cfg.α cfg.q cfg.Λ j) :
    ∀ d j, j + d = n → m₀ ≤ j → hist j = paperDescentStart cfg tS n j := by
  intro d
  induction d with
  | zero =>
    intro j hj _
    obtain rfl : j = n := by omega
    rw [paperDescentStart_self]
    exact hn
  | succ d ih =>
    intro j hj hm
    have h1 := ih (j + 1) (by omega) (by omega)
    have h2 := hstep (j + 1) (by omega) (by omega)
    rw [Nat.add_sub_cancel] at h2
    rw [h2, h1, paperDescentStart_succ cfg tS (by omega : j < n)]

/-- **The chain** (Lemma 10.A(4)): an admissible seed of level `n > m₀` on `[t_S, t_f]`,
`t_S + t₀/2 < t_f`, has a chain `stage n = seed`, `stage (j - 1) = (ext j)` retained, of actual
successors `ext j` of `stage j` for `m₀ < j ≤ n`, with the windows
`t_A^{(j)} + 3τ_j + 4τ''_j ≤ t_f`. -/
def PaperCascadeChainStatement (cfg : FiniteParameters) (m₀ : ℕ) : Prop :=
  ∀ (D : OCData), D.α = cfg.α → D.q = cfg.q → D.Λ = cfg.Λ → D.ζ = cfg.ζ →
    IsOCStreamSeq cfg.α cfg.q cfg.Λ cfg.ζ D.Φ →
  ∀ (M : ℕ), IsOCBandChain cfg.α cfg.q cfg.Λ cfg.ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
  ∀ (law : BirthLaw), IsSuccessorLaw cfg.α cfg.q cfg.s (paperWordCount cfg) law →
  ∀ (seedK freshK : ℕ → KernelSpec),
    (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D cfg.kI.cr cfg.σ₀ cfg.nk.toPNat' b' (freshK b')) →
  ∀ (seed : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀) (n : ℕ) (tS tf : ℝ),
    m₀ < n → tS + cfg.t₀ / 2 < tf →
    IsPaperSeed cfg M Mnat law seedK freshK seed n tS tf →
    ∃ (stage ext : ℕ → GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀),
      stage n = seed ∧
      ∀ j, m₀ < j → j ≤ n →
        IsActualSuccessor D (paperProv cfg D) (paperMenu cfg Mnat) (stage j) (ext j) ∧
        stage (j - 1) = (ext j).retained j cfg.H cfg.J ∧
        paperDescentStart cfg tS n j + 3 * ocTau cfg.α cfg.q cfg.Λ j +
          4 * ocTauPP cfg.α cfg.q cfg.Λ j ≤ tf

/-- The chain at the parameters `P`, `m₀ = paperBottom P`. -/
theorem paper_cascade_chain_of_parameters {α s q : ℝ} {ζ : ℝ → ℝ} {Λ Jw : ℕ} {t₀ T₀ : ℝ}
    (_hΛ : 128 ≤ Λ) (P : PaperParameters α s q ζ Λ Jw t₀ T₀) :
    PaperCascadeChainStatement P.ready.cfg (paperBottom P) := by
  intro D hDα hDq hDΛ hDζ hDΦ M hband hterm Mnat hMnat law hlaw seedK freshK hfresh seed n tS tf
    hn htS hseedP
  have hbot : P.ready.cfg.m₀ ≤ paperBottom P := (le_max_left _ _).trans (le_max_right _ _)
  have hm₀ : P.ready.cfg.m₀ < n := lt_of_le_of_lt hbot hn
  obtain ⟨stage, ext, hist, st, tp, Preg, hframe, -⟩ :=
    P.ready.cascade D hDα hDq hDΛ hDζ hDΦ M hband hterm Mnat hMnat law hlaw seedK freshK hfresh
      seed n tS tf htS hseedP.2.2.2 hseedP.1 hseedP.2.1 hm₀ hseedP.2.2.1
  have hstep : ∀ j, P.ready.cfg.m₀ < j → j ≤ n →
      hist (j - 1) = hist j + 3 * ocTau P.ready.cfg.α P.ready.cfg.q P.ready.cfg.Λ j := by
    intro j hj hjn
    have h := (hframe.2.2.2.2.2 j hj hjn).2.2.1
    rw [hDα, hDq, hDΛ] at h
    exact h
  refine ⟨stage, ext, hframe.1, fun j hj hjn => ?_⟩
  have hcj : P.ready.cfg.m₀ < j := lt_of_le_of_lt hbot hj
  obtain ⟨hsucc, hstage, -, -, hwin, -⟩ := hframe.2.2.2.2.2 j hcj hjn
  have hhist := paper_hist_eq_descentStart P.ready.cfg hist tS hframe.2.1 hstep (n - j) j
    (by omega) hcj.le
  have hr : hist j + 3 * ocTau D.α D.q D.Λ j ≤ cascadeRestart D hist st j := le_max_right _ _
  rw [hDα, hDq, hDΛ] at hr hwin
  refine ⟨hsucc, hstage, ?_⟩
  rw [← hhist]
  linarith

/-- The chain is monotone in the bottom level. -/
theorem PaperCascadeChainStatement.mono {cfg : FiniteParameters} {m₀ m₀' : ℕ}
    (h : PaperCascadeChainStatement cfg m₀) (hle : m₀ ≤ m₀') :
    PaperCascadeChainStatement cfg m₀' := by
  intro D hDα hDq hDΛ hDζ hDΦ M hband hterm Mnat hMnat law hlaw seedK freshK hfresh seed n tS tf
    hn htS hseedP
  obtain ⟨stage, ext, hseed, hlink⟩ := h D hDα hDq hDΛ hDζ hDΦ M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf (lt_of_le_of_lt hle hn) htS hseedP
  exact ⟨stage, ext, hseed, fun j hj hjn => hlink j (lt_of_le_of_lt hle hj) hjn⟩

/-! ### The weights of successors -/

/-- **The weights of successors** (Lemma 10.A(1)-(3)): for a cascade stage `G` of a seed whose
components have no births and an actual successor `G'`: (1) the components of `G` are retained;
(2) the retained mass is at most twice the seed mass; (3) the readout is near the identity,
`‖𝖱‖ ≤ 1 + √N_word E^{5η₀/4}`, `E = ε_{m-1}`. -/
def PaperSuccessorWeightsStatement (cfg : FiniteParameters) : Prop :=
  ∀ (D : OCData), D.α = cfg.α → D.q = cfg.q → D.Λ = cfg.Λ → D.ζ = cfg.ζ →
    IsOCStreamSeq cfg.α cfg.q cfg.Λ cfg.ζ D.Φ →
  ∀ (M : ℕ), IsOCBandChain cfg.α cfg.q cfg.Λ cfg.ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
  ∀ (law : BirthLaw), IsSuccessorLaw cfg.α cfg.q cfg.s (paperWordCount cfg) law →
  ∀ (seed G G' : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀),
    (∀ v : CompIn seed.comps, v.1.births = []) →
    IsCascadeStage D (paperProv cfg D) (paperMenu cfg Mnat) seed G →
    IsActualSuccessor D (paperProv cfg D) (paperMenu cfg Mnat) G G' →
    G.comps ⊆ (G'.retained G.level cfg.H cfg.J).comps ∧
    ∑ v, (G'.retained G.level cfg.H cfg.J).mass law v ≤ 2 * ∑ v, seed.mass law v ∧
    ‖readoutCLM G.level (D.eps (G.level - 1)) (succEta0 cfg.α cfg.q cfg.s) (G.mass law)
        ((G'.retained G.level cfg.H cfg.J).mass law)‖ ≤
      1 + Real.sqrt (paperWordCount cfg : ℝ) *
        D.eps (G.level - 1) ^ (5 * succEta0 cfg.α cfg.q cfg.s / 4)

/-- The weights of successors at the parameters. -/
theorem paper_successor_weights_of_parameters {α s q : ℝ} {ζ : ℝ → ℝ} {Λ Jw : ℕ} {t₀ T₀ : ℝ}
    (hs₀ : 0 < s) (hΛ : 128 ≤ Λ) (P : PaperParameters α s q ζ Λ Jw t₀ T₀) :
    PaperSuccessorWeightsStatement P.ready.cfg := by
  intro D hDα hDq hDΛ hDζ hDΦ M hband hterm Mnat hMnat law hlaw seed G G' hseed hcas hsucc
  have hv := P.ready.valid
  have hΛc : 128 ≤ P.ready.cfg.Λ := by rw [P.ready.base.2.2.2.2.1]; exact hΛ
  have hs₀c : 0 < P.ready.cfg.s := by rw [P.ready.base.2.1]; exact hs₀
  have hq : 1 < D.q := by rw [hDq]; exact hv.hq.1
  have hΛD : 128 ≤ D.Λ := by rw [hDΛ]; exact hΛc
  have hη := succEta0_pos_of_admissible hv.hα₀ hs₀c hv.hq
  obtain ⟨heta0, hetaB, -, hcH, hTw⟩ := hlaw
  have hinv := InitialValue.cascade_invariant hseed hcas
  have hlev1 : 1 ≤ G.level := hsucc.1
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    show c ∈ G'.comps.filter (IsRetained G.level P.ready.cfg.H P.ready.cfg.J)
    rw [Finset.mem_filter, hsucc.2.2.1]
    refine ⟨Finset.mem_union_left _ hc, (hinv c hc).2, ?_⟩
    have hw : compWord G.level c = [] := by
      unfold compWord
      rcases hb : c.births with _ | ⟨e, es⟩
      · rfl
      · have he := (hinv c hc).1 e (by rw [hb]; exact List.mem_cons_self)
        simp only
        rw [ite_eq_right (by omega)]
    rw [hw]
    exact Nat.zero_le _
  · exact Construction.Preservation.RetainedEnergy.cascade_mass_sum_le_twice hq hΛD law
      (by rw [hetaB]; linarith) (by rw [hcH, hetaB]) (paperProv P.ready.cfg D)
      (paperMenu P.ready.cfg Mnat) hTw seed (G'.retained G.level P.ready.cfg.H P.ready.cfg.J)
      (IsCascadeStage.step hcas hsucc)
  · have hcH1 : law.cH ≤ 1 := by
      have h0 := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 128)
        (-(succEta0 P.ready.cfg.α P.ready.cfg.q P.ready.cfg.s / 2))
      rw [hcH]
      linarith
    have hold : ∀ v ∈ G.comps, ∀ e ∈ v.births, G.level ≤ e.scale := fun v hv => (hinv v hv).1
    have hsub : (G'.retained G.level P.ready.cfg.H P.ready.cfg.J).comps ⊆
        succExtComps G.level (paperMenu P.ready.cfg Mnat).A (paperMenu P.ready.cfg Mnat).J
          G.comps := by
      intro c hc
      have hc' : c ∈ G'.comps := (Finset.mem_filter.1 hc).1
      rw [hsucc.2.2.1] at hc'
      exact hc'
    have hE : 0 ≤ D.eps (G.level - 1) ^ (succEta0 P.ready.cfg.α P.ready.cfg.q P.ready.cfg.s +
        succEta0 P.ready.cfg.α P.ready.cfg.q P.ready.cfg.s / 2 / 2) :=
      Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos (by omega)).le _
    have hb := IterationPassage.Passage.passageReadoutNorm G.level (D.eps (G.level - 1))
      (succEta0 P.ready.cfg.α P.ready.cfg.q P.ready.cfg.s) 1
      (1 + Real.sqrt (paperWordCount P.ready.cfg : ℝ) * D.eps (G.level - 1) ^
        (succEta0 P.ready.cfg.α P.ready.cfg.q P.ready.cfg.s +
          succEta0 P.ready.cfg.α P.ready.cfg.q P.ready.cfg.s / 2 / 2))
      (G.mass law) ((G'.retained G.level P.ready.cfg.H P.ready.cfg.J).mass law)
      (fun v => Construction.Preservation.Buffer.birth_compMass_pos hq hΛD law v.1)
      (fun v => Construction.Preservation.Buffer.birth_compMass_pos hq hΛD law v.1)
      (add_nonneg zero_le_one (mul_nonneg (Real.sqrt_nonneg _) hE)) (fun X => by
        have h := Construction.Preservation.RetainedEnergy.birth_readout_near_identity hq hΛD
          hlev1 law hcH1 (by rw [heta0]; exact hη.le) hold hsub 0 1 X
        rw [heta0, hetaB] at h
        exact h)
    have he : succEta0 P.ready.cfg.α P.ready.cfg.q P.ready.cfg.s +
        succEta0 P.ready.cfg.α P.ready.cfg.q P.ready.cfg.s / 2 / 2 =
        5 * succEta0 P.ready.cfg.α P.ready.cfg.q P.ready.cfg.s / 4 := by ring
    rw [he] at hb
    exact hb

/-- **The weights of a new component** `(v, t)`, `t ≠ []`, of the passage `m → m - 1` ((10.5)):
mass `π_v c_H/|𝔚| ε_{m-1}^{η_b}`, marker `d_v ε_{m-1}^{-ι}`, readout factor
`ω_v (ε_{m-1}^{η_0})^{|t|}`, for a component `v` whose births have scales `≥ m ≥ 1`. -/
theorem paper_newcomp_weights (q : ℝ) (Λ : ℕ) (law : BirthLaw) {m : ℕ} {v : Comp}
    {t : List WordLetter} (hm : 1 ≤ m) (ht : t ≠ []) (hv : ∀ e ∈ v.births, m ≤ e.scale) :
    compMass q Λ law (succComp m v t) =
        law.cH / (law.wordCount : ℝ) * ocEpsilon q Λ (m - 1) ^ law.etaB * compMass q Λ law v ∧
      compMarker q Λ law (succComp m v t) =
        ocEpsilon q Λ (m - 1) ^ (-law.iota) * compMarker q Λ law v ∧
      compReadout q Λ law (succComp m v t) =
        (ocEpsilon q Λ (m - 1) ^ law.eta0) ^ t.length * compReadout q Λ law v := by
  have hsc : succComp m v t = ⟨v.root, ⟨m - 1, t, ht⟩ :: v.births⟩ := dite_eq_right ht
  have hnot : m - 1 ∉ compBirthSet v := by
    simp only [compBirthSet, List.mem_toFinset, List.mem_map, not_exists, not_and]
    intro e he hes
    have := hv e he
    omega
  rw [hsc]
  refine ⟨?_, ?_, ?_⟩
  · simp only [compMass, List.map_cons, List.prod_cons]
    ring
  · have hset : compBirthSet ⟨v.root, ⟨m - 1, t, ht⟩ :: v.births⟩ =
        insert (m - 1) (compBirthSet v) := by
      simp [compBirthSet]
    simp only [compMarker]
    rw [hset, Finset.prod_insert hnot]
  · simp only [compReadout, List.map_cons, List.prod_cons]
    ring

/-! ### Admissibility by descent -/

/-- **Admissible by descent** (Definition 10.4 of the paper): `G` of level `m ≥ m₀` on `[t_A, t_f]`
is the level-`m` stage of a chain of actual successors from an admissible seed of level `m_S > m₀`
on `[t_S, t_f]`, `t_S + t₀/2 < t_f`, with `t_A = t_A^{(m)}` and the windows
`t_A^{(j)} + 3τ_j + 4τ''_j ≤ t_f` for `m < j ≤ m_S`. -/
def PaperAdmissibleByDescent (cfg : FiniteParameters) (m₀ : ℕ) {D : OCData} (M Mnat : ℕ)
    (law : BirthLaw) (seedK freshK : ℕ → KernelSpec)
    (G : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀) (m : ℕ) (tA tf : ℝ) : Prop :=
  ∃ (mS : ℕ) (tS : ℝ) (stage ext : ℕ → GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀),
    m₀ ≤ m ∧ m ≤ mS ∧ m₀ < mS ∧ tS + cfg.t₀ / 2 < tf ∧
    IsPaperSeed cfg M Mnat law seedK freshK (stage mS) mS tS tf ∧
    stage m = G ∧ tA = paperDescentStart cfg tS mS m ∧
    ∀ j, m < j → j ≤ mS →
      IsActualSuccessor D (paperProv cfg D) (paperMenu cfg Mnat) (stage j) (ext j) ∧
      stage (j - 1) = (ext j).retained j cfg.H cfg.J ∧
      paperDescentStart cfg tS mS j + 3 * ocTau cfg.α cfg.q cfg.Λ j +
        4 * ocTauPP cfg.α cfg.q cfg.Λ j ≤ tf

/-- **Descent gives admissible families**: a family admissible by descent is an admissible family on
the window of the descent (Proposition 10.5 of the paper follows from it). -/
def PaperDescentFamilyStatement (cfg : FiniteParameters) (m₀ : ℕ) : Prop :=
  ∀ (D : OCData), D.α = cfg.α → D.q = cfg.q → D.Λ = cfg.Λ → D.ζ = cfg.ζ →
    IsOCStreamSeq cfg.α cfg.q cfg.Λ cfg.ζ D.Φ →
  ∀ (M : ℕ), IsOCBandChain cfg.α cfg.q cfg.Λ cfg.ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
  ∀ (law : BirthLaw), IsSuccessorLaw cfg.α cfg.q cfg.s (paperWordCount cfg) law →
  ∀ (seedK freshK : ℕ → KernelSpec),
    (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D cfg.kI.cr cfg.σ₀ cfg.nk.toPNat' b' (freshK b')) →
  ∀ (G : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀) (m : ℕ) (tA tf : ℝ),
    PaperAdmissibleByDescent cfg m₀ M Mnat law seedK freshK G m tA tf →
    IsPaperFamily cfg M Mnat law seedK freshK G m tA tf

/-- Descent gives admissible families, from the base case and the step (downward induction). -/
theorem paper_descent_family_of_steps {cfg : FiniteParameters} {m₀ : ℕ}
    (hseed : PaperSeedFamilyStatement cfg m₀) (hstep : PaperSuccessorAdmissibleStatement cfg m₀) :
    PaperDescentFamilyStatement cfg m₀ := by
  intro D hDα hDq hDΛ hDζ hDΦ M hband hterm Mnat hMnat law hlaw seedK freshK hfresh G m tA tf hdesc
  obtain ⟨mS, tS, stage, ext, hm₀m, hmmS, hm₀S, htS, hseedP, hG, hA, hlink⟩ := hdesc
  have hbase := hseed D hDα hDq hDΛ hDζ hDΦ M hband hterm Mnat hMnat law hlaw seedK freshK hfresh
    (stage mS) mS tS tf hm₀S htS hseedP
  have key : ∀ d, d ≤ mS - m → IsPaperFamily cfg M Mnat law seedK freshK (stage (mS - d)) (mS - d)
      (paperDescentStart cfg tS mS (mS - d)) tf := by
    intro d
    induction d with
    | zero =>
      intro _
      rw [Nat.sub_zero, paperDescentStart_self]
      exact hbase
    | succ d ih =>
      intro hd
      have hprev := ih (by omega)
      obtain ⟨hsucc, hstage, hwin⟩ := hlink (mS - d) (by omega) (by omega)
      have hnew := hstep D hDα hDq hDΛ hDζ hDΦ M hband hterm Mnat hMnat law hlaw seedK freshK
        hfresh (mS - d) (by omega) (paperDescentStart cfg tS mS (mS - d)) tf (stage (mS - d))
        (ext (mS - d)) hprev hwin hsucc
      rw [← hstage] at hnew
      have he1 : mS - d - 1 = mS - (d + 1) := by omega
      have he2 : paperDescentStart cfg tS mS (mS - d) + 3 * ocTau cfg.α cfg.q cfg.Λ (mS - d) =
          paperDescentStart cfg tS mS (mS - (d + 1)) := by
        have h := paperDescentStart_succ cfg tS (mS := mS) (j := mS - (d + 1)) (by omega)
        rw [show mS - (d + 1) + 1 = mS - d by omega] at h
        exact h.symm
      rw [he1, he2] at hnew
      exact hnew
  have h := key (mS - m) le_rfl
  rw [show mS - (mS - m) = m by omega, hG, ← hA] at h
  exact h

/-- Descent gives admissible families at the parameters `P`, `m₀ = paperBottom P`. -/
theorem paper_descent_family_of_parameters {α s q : ℝ} {ζ : ℝ → ℝ} {Λ Jw : ℕ} {t₀ T₀ : ℝ}
    (hs₀ : 0 < s) (hΛ : 128 ≤ Λ) (ht₀ : 0 < t₀) (htT : t₀ < T₀)
    (P : PaperParameters α s q ζ Λ Jw t₀ T₀) :
    PaperDescentFamilyStatement P.ready.cfg (paperBottom P) :=
  paper_descent_family_of_steps (paper_seed_family_of_parameters hΛ P)
    (paper_successor_admissible_of_parameters hs₀ hΛ ht₀ htT P)

/-- **Extension** (used in the proof of Proposition 4.3(b) of the paper): descent extends by one
actual successor of a family of level `m > m₀`, with the window `t_A + 3τ_m + 4τ''_m ≤ t_f`. -/
theorem PaperAdmissibleByDescent.extend {cfg : FiniteParameters} {m₀ : ℕ} {D : OCData}
    {M Mnat : ℕ} {law : BirthLaw} {seedK freshK : ℕ → KernelSpec}
    {G G' : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀} {m : ℕ} {tA tf : ℝ}
    (h : PaperAdmissibleByDescent cfg m₀ M Mnat law seedK freshK G m tA tf) (hm : m₀ < m)
    (hsucc : IsActualSuccessor D (paperProv cfg D) (paperMenu cfg Mnat) G G')
    (hwin : tA + 3 * ocTau cfg.α cfg.q cfg.Λ m + 4 * ocTauPP cfg.α cfg.q cfg.Λ m ≤ tf) :
    PaperAdmissibleByDescent cfg m₀ M Mnat law seedK freshK (G'.retained m cfg.H cfg.J) (m - 1)
      (tA + 3 * ocTau cfg.α cfg.q cfg.Λ m) tf := by
  obtain ⟨mS, tS, stage, ext, hm₀m, hmmS, hm₀S, htS, hseedP, hG, hA, hlink⟩ := h
  have hstart : tA + 3 * ocTau cfg.α cfg.q cfg.Λ m = paperDescentStart cfg tS mS (m - 1) := by
    have h := paperDescentStart_succ cfg tS (mS := mS) (j := m - 1) (by omega)
    rw [show m - 1 + 1 = m by omega] at h
    rw [h, hA]
  refine ⟨mS, tS, Function.update stage (m - 1) (G'.retained m cfg.H cfg.J),
    Function.update ext m G', by omega, by omega, hm₀S, htS, ?_, ?_, hstart, ?_⟩
  · rw [Function.update_of_ne (by omega : mS ≠ m - 1)]
    exact hseedP
  · exact Function.update_self _ _ _
  · intro j hj hjS
    by_cases hjm : j = m
    · rw [hjm, Function.update_of_ne (by omega : m ≠ m - 1), Function.update_self,
        Function.update_self, hG]
      refine ⟨hsucc, rfl, ?_⟩
      rw [← hA]
      exact hwin
    · obtain ⟨h1, h2, h3⟩ := hlink j (by omega) hjS
      rw [Function.update_of_ne (by omega : j ≠ m - 1), Function.update_of_ne hjm,
        Function.update_of_ne (by omega : j - 1 ≠ m - 1)]
      exact ⟨h1, h2, h3⟩

/-- Descent gives admissible families: monotone in the bottom level. -/
theorem PaperDescentFamilyStatement.mono {cfg : FiniteParameters} {m₀ m₀' : ℕ}
    (h : PaperDescentFamilyStatement cfg m₀) (hle : m₀ ≤ m₀') :
    PaperDescentFamilyStatement cfg m₀' := by
  intro D hDα hDq hDΛ hDζ hDΦ M hband hterm Mnat hMnat law hlaw seedK freshK hfresh G m tA tf hdesc
  obtain ⟨mS, tS, stage, ext, hm₀m, hmmS, hm₀S, rest⟩ := hdesc
  exact h D hDα hDq hDΛ hDζ hDΦ M hband hterm Mnat hMnat law hlaw seedK freshK hfresh G m tA tf
    ⟨mS, tS, stage, ext, hle.trans hm₀m, hmmS, lt_of_le_of_lt hle hm₀S, rest⟩

/-- **The seed of a descent** (for Lemma 10.A): a family admissible by descent, of level `m`, is a
cascade stage of the seed of its descent, which is an admissible seed of level `m_S ≥ m` with
empty birth lists. -/
theorem PaperAdmissibleByDescent.exists_cascade {cfg : FiniteParameters} {m₀ : ℕ} {D : OCData}
    {M Mnat : ℕ} {law : BirthLaw} {seedK freshK : ℕ → KernelSpec}
    {G : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀} {m : ℕ} {tA tf : ℝ}
    (h : PaperAdmissibleByDescent cfg m₀ M Mnat law seedK freshK G m tA tf) :
    ∃ (mS : ℕ) (tS : ℝ) (seed : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀),
      m ≤ mS ∧ IsPaperSeed cfg M Mnat law seedK freshK seed mS tS tf ∧
      (∀ v : CompIn seed.comps, v.1.births = []) ∧
      IsCascadeStage D (paperProv cfg D) (paperMenu cfg Mnat) seed G ∧ G.level = m := by
  obtain ⟨mS, tS, stage, ext, -, hmmS, -, -, hseedP, hG, -, hlink⟩ := h
  have key : ∀ d, d ≤ mS - m →
      IsCascadeStage D (paperProv cfg D) (paperMenu cfg Mnat) (stage mS) (stage (mS - d)) ∧
        (stage (mS - d)).level = mS - d := by
    intro d
    induction d with
    | zero =>
      intro _
      rw [Nat.sub_zero]
      exact ⟨IsCascadeStage.seed, hseedP.1.1⟩
    | succ d ih =>
      intro hd
      obtain ⟨hc, hlev⟩ := ih (by omega)
      obtain ⟨hsucc, hstage, -⟩ := hlink (mS - d) (by omega) (by omega)
      have hstep : IsCascadeStage D (paperProv cfg D) (paperMenu cfg Mnat) (stage mS)
          ((ext (mS - d)).retained (mS - d) cfg.H cfg.J) := by
        have h := IsCascadeStage.step hc hsucc
        rw [hlev] at h
        exact h
      have hlev' : ((ext (mS - d)).retained (mS - d) cfg.H cfg.J).level = mS - d - 1 := by
        change (ext (mS - d)).level = mS - d - 1
        rw [hsucc.2.1, hlev]
      rw [← hstage, show mS - d - 1 = mS - (d + 1) by omega] at hstep hlev'
      exact ⟨hstep, hlev'⟩
  obtain ⟨hc, hlev⟩ := key (mS - m) le_rfl
  rw [show mS - (mS - m) = m by omega, hG] at hc hlev
  exact ⟨mS, tS, stage mS, hmmS, hseedP, hseedP.1.2.1, hc, hlev⟩

/-- **The chain gives admissibility by descent** (Definition 10.4 of the paper): every stage
`stage m`, `m₀ ≤ m ≤ n`, of the chain of an admissible seed is admissible by descent on
`[t_A^{(m)}, t_f]`. Lemma 10.6 of the paper follows from it. -/
theorem PaperCascadeChainStatement.admissible {cfg : FiniteParameters} {m₀ : ℕ}
    (h : PaperCascadeChainStatement cfg m₀) {D : OCData} (hDα : D.α = cfg.α) (hDq : D.q = cfg.q)
    (hDΛ : D.Λ = cfg.Λ) (hDζ : D.ζ = cfg.ζ) (hDΦ : IsOCStreamSeq cfg.α cfg.q cfg.Λ cfg.ζ D.Φ)
    {M : ℕ} (hband : IsOCBandChain cfg.α cfg.q cfg.Λ cfg.ζ M D.κ) (hterm : D.term = M)
    {Mnat : ℕ} (hMnat : M ≤ Mnat) {law : BirthLaw}
    (hlaw : IsSuccessorLaw cfg.α cfg.q cfg.s (paperWordCount cfg) law)
    {seedK freshK : ℕ → KernelSpec}
    (hfresh : ∀ b', 1 ≤ b' → b' < M →
      IsFreshKernel D cfg.kI.cr cfg.σ₀ cfg.nk.toPNat' b' (freshK b'))
    {seed : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀} {n : ℕ} {tS tf : ℝ}
    (hn : m₀ < n) (htS : tS + cfg.t₀ / 2 < tf)
    (hseedP : IsPaperSeed cfg M Mnat law seedK freshK seed n tS tf) :
    ∃ stage : ℕ → GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀,
      stage n = seed ∧ ∀ m, m₀ ≤ m → m ≤ n →
        PaperAdmissibleByDescent cfg m₀ M Mnat law seedK freshK (stage m) m
          (paperDescentStart cfg tS n m) tf := by
  obtain ⟨stage, ext, hseed, hlink⟩ := h D hDα hDq hDΛ hDζ hDΦ M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hn htS hseedP
  have hseedP' : IsPaperSeed cfg M Mnat law seedK freshK (stage n) n tS tf := by
    rw [hseed]
    exact hseedP
  exact ⟨stage, hseed, fun m hm hmn => ⟨n, tS, stage, ext, hm, hmn, hn, htS, hseedP', rfl, rfl,
    fun j hj hjn => hlink j (by omega) hjn⟩⟩

/-! ### The fresh smoothings -/

/-- **The fresh inverse bound** above `m₁`: for every fresh birth level `b` with
`m₁ ≤ b + 1 ≤ term`, every kernel with the fresh axes of level `b` has spanning inverse at
most `2`. -/
def PaperFreshInverseStatement (cfg : FiniteParameters) (m₁ : ℕ) : Prop :=
  ∀ (D : OCData), D.α = cfg.α → D.q = cfg.q → D.Λ = cfg.Λ → D.ζ = cfg.ζ →
    IsOCStreamSeq cfg.α cfg.q cfg.Λ cfg.ζ D.Φ → IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
  ∀ (b : ℕ), m₁ ≤ b + 1 → b + 1 ≤ D.term →
  ∀ (S : KernelSpec), IsFreshAxes D b S.H₁ S.H₂ →
  ∀ t : ℝ, IsUnit (S.span t).det ∧ ‖(Matrix.toLin' (S.span t)⁻¹).toContinuousLinearMap‖ ≤ 2

/-- The fresh inverse bound at the parameters, above some `m₁ ≥ 2`. -/
theorem paper_fresh_inverse_of_parameters {α s q : ℝ} {ζ : ℝ → ℝ} {Λ Jw : ℕ} {t₀ T₀ : ℝ}
    (hs₀ : 0 < s) (hΛ : 128 ≤ Λ) (P : PaperParameters α s q ζ Λ Jw t₀ T₀) :
    ∃ m₁ : ℕ, 2 ≤ m₁ ∧ PaperFreshInverseStatement P.ready.cfg m₁ := by
  have hv := P.ready.valid
  have hΛc : 128 ≤ P.ready.cfg.Λ := by rw [P.ready.base.2.2.2.2.1]; exact hΛ
  have hs₀c : 0 < P.ready.cfg.s := by rw [P.ready.base.2.1]; exact hs₀
  obtain ⟨m₁, hm₁, h⟩ := Construction.Preservation.FullLift.uniform_fresh_spanning_inverse_bound
    P.ready.cfg.α P.ready.cfg.s P.ready.cfg.q hv.hα₀ hv.hα₁ hs₀c hv.hs₁ hv.hq P.ready.cfg.ζ hv.hζ
    P.ready.cfg.Λ hΛc
  exact ⟨m₁, hm₁, h⟩

/-- **The fresh smoothings at source level**: there are constants `c_j ≥ 0` (depending on
`(φ₀, n_k)` only) such that for every admissible family `G` of level `m ≥ m₀` on `[t_A, t_f]`
and every source `γ` of `G` whose smoothing is the fresh kernel born at the level `b`: `m ≤ b`,
the spanning matrix of the smoothing has inverse at most `2`, and the smoothing is a spatial
regularizer on `[t_A, t_f]` with the constants `c_j` and its width. -/
def PaperFreshSmoothingStatement (cfg : FiniteParameters) (m₀ : ℕ) : Prop :=
  ∃ c : ℕ → ℝ, (∀ j, 0 ≤ c j) ∧
  ∀ (D : OCData), D.α = cfg.α → D.q = cfg.q → D.Λ = cfg.Λ → D.ζ = cfg.ζ →
    IsOCStreamSeq cfg.α cfg.q cfg.Λ cfg.ζ D.Φ →
  ∀ (M : ℕ), IsOCBandChain cfg.α cfg.q cfg.Λ cfg.ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
  ∀ (law : BirthLaw), IsSuccessorLaw cfg.α cfg.q cfg.s (paperWordCount cfg) law →
  ∀ (seedK freshK : ℕ → KernelSpec),
    (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D cfg.kI.cr cfg.σ₀ cfg.nk.toPNat' b' (freshK b')) →
  ∀ (G : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀) (m : ℕ) (tA tf : ℝ),
    m₀ ≤ m → IsPaperFamily cfg M Mnat law seedK freshK G m tA tf →
  ∀ (v u : CompIn G.comps) (γ : G.fam.Γ v u) (b : ℕ),
    ((G.prov v u γ).tags (paperProv cfg D)).kernel = KernelKey.fresh b →
    m ≤ b ∧
    (∀ t : ℝ, IsUnit ((G.kernelOf (paperProv cfg D) seedK freshK v u γ).span t).det ∧
      ‖(Matrix.toLin'
          ((G.kernelOf (paperProv cfg D) seedK freshK v u γ).span t)⁻¹).toContinuousLinearMap‖ ≤
        2) ∧
    ∀ (ρ : ℝ) (k : ℕ),
      IsSpatialRegularizerTorus ρ k (paperFamilyOrder cfg) tA tf c
        (G.kernelOf (paperProv cfg D) seedK freshK v u γ).width
        (G.sysS (paperProv cfg D) seedK freshK cfg.φ₀ cfg.hφ₀ v u γ)

/-- The fresh smoothings at source level at the parameters, above some `m₁`. -/
theorem paper_fresh_smoothing_of_parameters {α s q : ℝ} {ζ : ℝ → ℝ} {Λ Jw : ℕ} {t₀ T₀ : ℝ}
    (hs₀ : 0 < s) (hΛ : 128 ≤ Λ) (P : PaperParameters α s q ζ Λ Jw t₀ T₀) :
    ∃ m₁ : ℕ, PaperFreshSmoothingStatement P.ready.cfg m₁ := by
  have hv := P.ready.valid
  obtain ⟨m₁, hm₁, hinv⟩ := paper_fresh_inverse_of_parameters hs₀ hΛ P
  obtain ⟨c, hc0, hreg⟩ :=
    Construction.Preservation.FullLift.exists_fresh_kernel_regularizer_constants_of_span_bound
      P.ready.cfg.φ₀ (Providers.hasCompactSupport_of_unitBall P.mollifier.2) P.mollifier.1
      P.ready.cfg.nk.toPNat'
  refine ⟨m₁, c, hc0, ?_⟩
  intro D hDα hDq hDΛ hDζ hDΦ M hband hterm Mnat hMnat law hlaw seedK freshK hfresh G m tA tf hm
    hG v u γ b hkey
  obtain ⟨tS, seed, n, -, hseedP, hcas, hlev, -⟩ := hG
  have hQ := Construction.Preservation.FullLift.cascade_kernel_key_property
    (paperProv P.ready.cfg D) (paperMenu P.ready.cfg Mnat) seed G hcas
    (fun k => ∀ b, k = KernelKey.fresh b → m ≤ b ∧ b < n)
    (fun v' u' γ' => by
      obtain ⟨k, tag, hk⟩ := hseedP.1.2.2.1 v' u' γ'
      intro b' hb'
      rw [hk] at hb'
      exact absurd hb' (by simp [Prov.tags]))
    m (fun b' hb' hbs b'' hb'' => by
      cases hb''
      exact ⟨hb', hseedP.1.1 ▸ hbs⟩) hlev.ge
  obtain ⟨hmb, hbn⟩ := hQ v u γ b hkey
  have hbM : b < M := hbn.trans hseedP.2.2.1
  have hb1 : 1 ≤ b := by omega
  have hfk := hfresh b hb1 hbM
  have hker : G.kernelOf (paperProv P.ready.cfg D) seedK freshK v u γ = freshK b := by
    unfold GenStage.kernelOf
    rw [hkey]
  have hΛD : 1 ≤ D.Λ := by rw [hDΛ, P.ready.base.2.2.2.2.1]; omega
  have hζD : IsFastProfile D.ζ := by rw [hDζ]; exact hv.hζ
  have hΛc1 : 1 ≤ P.ready.cfg.Λ := by rw [P.ready.base.2.2.2.2.1]; omega
  have hκb : 0 < D.κ b := CycleReference.bandChain_pos hΛc1 hv.hζ hband hbM.le
  have hκb1 : 0 < D.κ (b + 1) := CycleReference.bandChain_pos hΛc1 hv.hζ hband hbM
  have hband' : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    rw [hDα, hDq, hDΛ, hDζ, hterm]
    exact hband
  have hspan := hinv D hDα hDq hDΛ hDζ hDΦ hband' b (by omega) (by omega) (freshK b) hfk.2.2
  have hwidth : 0 < (freshK b).width := by
    rw [hfk.1]
    unfold freshWidth freshLength
    exact mul_pos (mul_pos hv.hcr (Real.sqrt_pos.mpr (mul_pos hκb
      (Construction.Stream.ocTauPP_pos hΛD))))
      (Real.rpow_pos_of_pos (Construction.Stream.ocEpsilon_pos hΛD) _)
  refine ⟨hmb, ?_, fun ρ k => ?_⟩
  · rw [hker]
    exact hspan
  · have h := hreg (ScalarH u.1.root) D b hΛD hζD hκb hκb1 (freshK b) hfk.2.1 hwidth hfk.2.2 hspan
      ρ tA tf k (paperFamilyOrder P.ready.cfg)
    unfold GenStage.sysS
    rw [hker]
    exact h

/-- The fresh smoothings at source level: monotone in the bottom level. -/
theorem PaperFreshSmoothingStatement.mono {cfg : FiniteParameters} {m₀ m₀' : ℕ}
    (h : PaperFreshSmoothingStatement cfg m₀) (hle : m₀ ≤ m₀') :
    PaperFreshSmoothingStatement cfg m₀' := by
  obtain ⟨c, hc, h⟩ := h
  exact ⟨c, hc, fun D hDα hDq hDΛ hDζ hDΦ M hband hterm Mnat hMnat law hlaw seedK freshK hfresh G
    m tA tf hm hG => h D hDα hDq hDΛ hDζ hDΦ M hband hterm Mnat hMnat law hlaw seedK freshK hfresh
      G m tA tf (hle.trans hm) hG⟩

/-! ### The complex chain lemma -/

/-- **The complex chain lemma** (Lemma 10.9 of the paper) at the carrier start of the parameters:
the last family of a scheduled chain with base level at least `j₀ - 1` is over its last slot on the
parameter domain `𝔇(2)` (`CFam.Over`: radius `8bε_i`, rate `2^{25}ε_i^{β-2}`, window half-length
`3h_{i+1}/5`, base strip `19ε_i/1000`, base labels `15ε_i/1000`). -/
def PaperComplexChainStatement (cfg : FiniteParameters) : Prop :=
  ∀ (D : OCData), D.α = cfg.α → D.q = cfg.q → D.Λ = cfg.Λ → D.ζ = cfg.ζ →
    IsOCStreamSeq cfg.α cfg.q cfg.Λ cfg.ζ D.Φ →
  ∀ (dd : ChainData) (n : ℕ), Providers.ComplexFlow.ChainOK D cfg.j₀ dd n →
    (Providers.ComplexFlow.chainFam D dd n).Over D cfg.bw (carrierC D cfg.bw dd n 2)
      (dd.baseLevel + n) (dd.slots.getLastD 0)

/-- The complex chain lemma at the parameters. -/
theorem paper_complex_chain_of_parameters {α s q : ℝ} {ζ : ℝ → ℝ} {Λ Jw : ℕ} {t₀ T₀ : ℝ}
    (hs₀ : 0 < s) (hΛ : 128 ≤ Λ) (P : PaperParameters α s q ζ Λ Jw t₀ T₀) :
    PaperComplexChainStatement P.ready.cfg := by
  intro D hDα hDq hDΛ hDζ hDΦ dd n hdd
  have hv := P.ready.valid
  have hΛc : 128 ≤ P.ready.cfg.Λ := by rw [P.ready.base.2.2.2.2.1]; exact hΛ
  have hs₀c : 0 < P.ready.cfg.s := by rw [P.ready.base.2.1]; exact hs₀
  have hq : 1 < D.q := by rw [hDq]; exact hv.hq.1
  have hΛD : 128 ≤ D.Λ := by rw [hDΛ]; exact hΛc
  have hα₀ : 0 < D.α := by rw [hDα]; exact hv.hα₀
  have hα₁ : D.α < 1 / 3 := by rw [hDα]; exact hv.hα₁
  have hs₁ : P.ready.cfg.s < (1 - D.α) / 2 := by rw [hDα]; exact hv.hs₁
  have hζD : IsFastProfile D.ζ := by rw [hDζ]; exact hv.hζ
  have hqa : IsAdmissibleQ D.α P.ready.cfg.s D.q := by rw [hDα, hDq]; exact hv.hq
  have hΦ : IsOCStreamSeq D.α D.q D.Λ D.ζ D.Φ := by rw [hDα, hDq, hDΛ, hDζ]; exact hDΦ
  have hcs : IsCarrierStart D.α D.q D.Λ P.ready.cfg.bw 1 1 P.ready.cfg.j₀ := by
    rw [hDα, hDq, hDΛ]
    exact P.carrier_one
  exact Providers.ComplexFlow.chainFam_over hq hΛD hα₁ hζD
    (fun m => (Providers.ComplexFlow.velC_spec hα₀ hα₁ hs₀c hs₁ hqa hΛD hζD hΦ m).1)
    hv.hbw P.bw_le le_rfl le_rfl hcs hdd

/-- **The complex chain lemma at real parameters** (Lemma 10.C, last bullet): for an admissible
real chain, the complex geometry of its last family at the real parameters agrees with the real
chain geometry ((10.6)): centre points and anchors agree, and the flows agree for times in the
window of the first pulse of the chain. -/
def PaperComplexChainAgreeStatement (cfg : FiniteParameters) : Prop :=
  ∀ (D : OCData), D.α = cfg.α → D.q = cfg.q → D.Λ = cfg.Λ → D.ζ = cfg.ζ →
    IsOCStreamSeq cfg.α cfg.q cfg.Λ cfg.ζ D.Φ →
  ∀ (i : ℕ) (p : ℤ) (ch : RealChain), IsAdmissibleChain D cfg.bw cfg.j₀ i p ch → ∀ ζ : Vec 2,
    Providers.ComplexFlow.CGeomAgree
      (Providers.ComplexFlow.slotWin D (ch.baseLevel + 1) (ch.slots.headD 0))
      ((Providers.ComplexFlow.chainFam D ch.data ch.children.length).toGeom (ch.paramsC ζ))
      (ch.geom D)

/-- The complex chain lemma at real parameters, at the parameters `P`. -/
theorem paper_complex_chain_agree_of_parameters {α s q : ℝ} {ζ : ℝ → ℝ} {Λ Jw : ℕ} {t₀ T₀ : ℝ}
    (hs₀ : 0 < s) (hΛ : 128 ≤ Λ) (P : PaperParameters α s q ζ Λ Jw t₀ T₀) :
    PaperComplexChainAgreeStatement P.ready.cfg := by
  intro D hDα hDq hDΛ hDζ hDΦ i p ch hch z
  have hv := P.ready.valid
  have hΛc : 128 ≤ P.ready.cfg.Λ := by rw [P.ready.base.2.2.2.2.1]; exact hΛ
  have hs₀c : 0 < P.ready.cfg.s := by rw [P.ready.base.2.1]; exact hs₀
  have hΛD : 128 ≤ D.Λ := by rw [hDΛ]; exact hΛc
  have hα₀ : 0 < D.α := by rw [hDα]; exact hv.hα₀
  have hα₁ : D.α < 1 / 3 := by rw [hDα]; exact hv.hα₁
  have hs₁ : P.ready.cfg.s < (1 - D.α) / 2 := by rw [hDα]; exact hv.hs₁
  have hζD : IsFastProfile D.ζ := by rw [hDζ]; exact hv.hζ
  have hqa : IsAdmissibleQ D.α P.ready.cfg.s D.q := by rw [hDα, hDq]; exact hv.hq
  have hΦ : IsOCStreamSeq D.α D.q D.Λ D.ζ D.Φ := by rw [hDα, hDq, hDΛ, hDζ]; exact hDΦ
  have hcs : IsCarrierStart D.α D.q D.Λ P.ready.cfg.bw 1 1 P.ready.cfg.j₀ := by
    rw [hDα, hDq, hDΛ]
    exact P.carrier_one
  have hspec := Providers.ComplexFlow.velC_spec hα₀ hα₁ hs₀c hs₁ hqa hΛD hζD hΦ
  exact Providers.ComplexFlow.chainFam_agree hΛD (fun m => (hspec m).1) (fun m => (hspec m).2)
    P.bw_le le_rfl le_rfl hcs hch z

/-! ### The bundle -/

/-- **The statements of Section 10 of the paper at the parameters `P`**: one bottom level
`m₀ ≥ paperBottom P` for the base case, the step, the chain, descent, and the fresh smoothings; the
weights of successors; the complex chain lemma and its agreement at real parameters; and the Schur
price `C_I ε_{m-1}^{qτ'} ≤ 1/8` for `m ≥ m₀`. -/
theorem paper_section10_of_parameters {α s q : ℝ} {ζ : ℝ → ℝ} {Λ Jw : ℕ} {t₀ T₀ : ℝ}
    (hs₀ : 0 < s) (hΛ : 128 ≤ Λ) (ht₀ : 0 < t₀) (htT : t₀ < T₀)
    (P : PaperParameters α s q ζ Λ Jw t₀ T₀) :
    ∃ m₀ : ℕ, paperBottom P ≤ m₀ ∧
      PaperSeedFamilyStatement P.ready.cfg m₀ ∧
      PaperSuccessorAdmissibleStatement P.ready.cfg m₀ ∧
      PaperCascadeChainStatement P.ready.cfg m₀ ∧
      PaperDescentFamilyStatement P.ready.cfg m₀ ∧
      PaperFreshSmoothingStatement P.ready.cfg m₀ ∧
      PaperSuccessorWeightsStatement P.ready.cfg ∧
      PaperComplexChainStatement P.ready.cfg ∧
      PaperComplexChainAgreeStatement P.ready.cfg ∧
      ∀ m, m₀ ≤ m → P.ready.cfg.CI * ocEpsilon P.ready.cfg.q P.ready.cfg.Λ (m - 1) ^
        (P.ready.cfg.q * paperTauPrime P.ready.cfg) ≤ 1 / 8 := by
  obtain ⟨m₁, hfresh⟩ := paper_fresh_smoothing_of_parameters hs₀ hΛ P
  have hb : paperBottom P ≤ max (paperBottom P) m₁ := le_max_left _ _
  have hE : P.mEnergy + 1 ≤ paperBottom P := (le_max_right _ _).trans (le_max_right _ _)
  exact ⟨max (paperBottom P) m₁, hb,
    (paper_seed_family_of_parameters hΛ P).mono hb,
    (paper_successor_admissible_of_parameters hs₀ hΛ ht₀ htT P).mono hb,
    (paper_cascade_chain_of_parameters hΛ P).mono hb,
    (paper_descent_family_of_parameters hs₀ hΛ ht₀ htT P).mono hb,
    hfresh.mono (le_max_right _ _),
    paper_successor_weights_of_parameters hs₀ hΛ P,
    paper_complex_chain_of_parameters hs₀ hΛ P,
    paper_complex_chain_agree_of_parameters hs₀ hΛ P,
    fun m hm => P.energy_floor (m - 1) (by omega)⟩

end AVRegularity.PaperFacing
