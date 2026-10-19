-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Finite.Assembly.WeakParentSettingOfIngredients

/-! # The paper-facing parameters and the two admissibility predicates

Shared definitions of the entry statement `paper_entry` and of the cascade, one cycle and one
passage (`paper_cascade_cycle_passage`) at the single parameter choice of the finite assembly;
Propositions 4.1–4.4 of the paper follow from these statements.

* `paperFamilyOrder`, `paperDepthBound`, `paperOrderBound`, `paperProv`, `paperMenu`,
  `paperTauPrime`, `paperRepOrder`, `paperWordCount`: the fixed orders, provenance parameters,
  menus and exponents of the cascade at the parameters `cfg` (`D_{H+1}`, `r̄₀`, `D̄₀`, the
  successor provenance, the successor menu with `n_pad = 0`, `τ' = min{δ/4, τ_e}`,
  `K = J N_w + (N_T + 2p_T) + 4`, the word count of the successor alphabet).
* `IsPaperSeed`: an *admissible seed* of level `n` on `[t_S, t_f]` (`t_f - t_S ≤ T`, `n < M`).
* `IsPaperFamily`: an *admissible family* of level `m` on `[t_A, t_f]`: a cascade stage of an
  admissible seed on `[t_S, t_f]` with `t_S ≤ t_A`, of level `m`, with the stage invariant on
  `[t_A, t_f]` at the invariant constants of the parameters (Schur sums `C_I ε_{m-1}^{qτ'}`).
* `PassageLevelStatement cfg C CQ m_*`: the tail of `iteration_passage` after its constants
  `C, C_Q, m_*`, at the parameters, for `K = K_strong`, `P_acc = 2`.
* `PaperParameters`: the finite-assembly parameters `FiniteAssemblyReady` extended by the data they
  are built from: the cascade schedule (`A_cl`, `a`, `σ`, `IsCascadeSchedule`,
  `succReconFloor ≤ N_aux`), the admissibility of the invariant constants `k_I`
  (`IsInvariantAdmissible`) and `c₀ ≤ 1`, the constants `C_pass, C_Q, m_*` of `iteration_passage` at
  the parameters with the passage tail, and a level `m_E ≥ j₀` above which the invariant's Schur
  price `C_I ε_j^{qτ'}` is at most `1/8` (existence and uniqueness of the solutions of admissible
  families, `kernel_energy_torus`); the carrier start with `C_H = Υ = 1`, the bound `b ≤ 10^{-4}` of
  the width parameter, the reserve-plan values of the seed constants (`m_env = 0`,
  `K_an = L_an = J_m = K_s`), and the smoothness and support of the mollifier.
* `paperBottom P = max{m_*, m₀^cas, m_E + 1}`: the bottom level `m₀` of the cascade. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal

namespace AVRegularity.PaperFacing

open AVRegularity.Finite.Assembly

/-- The order `D_{H+1}` of the seed and cascade families of the parameters. -/
abbrev paperFamilyOrder (cfg : FiniteParameters) : ℕ :=
  succSchedD (termD0bar cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw)) cfg.N cfg.p
    (cfg.H + 1)

/-- The a priori seed depth bound `r̄₀` of the parameters. -/
abbrev paperDepthBound (cfg : FiniteParameters) : ℕ := termR0bar cfg.RT (cfg.Jw * cfg.Rw)

/-- The a priori seed order bound `D̄₀` of the parameters. -/
abbrev paperOrderBound (cfg : FiniteParameters) : ℕ :=
  termD0bar cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw)

/-- The successor provenance parameters of the cascade at the parameters `cfg`. -/
abbrev paperProv (cfg : FiniteParameters) (D : OCData) : ProvParams :=
  succProvParams D cfg.CwCas cfg.kI.cr cfg.σ₀ (succEta0 cfg.α cfg.q cfg.s) cfg.N cfg.p

/-- The successor menu of the cascade at the parameters `cfg` (`n_pad = 0`). -/
abbrev paperMenu (cfg : FiniteParameters) (Mnat : ℕ) : SuccMenu :=
  succMenu Mnat (paperDepthBound cfg) (paperOrderBound cfg) cfg.H cfg.J cfg.N cfg.p 0 cfg.sX cfg.sZ
    (succEta0 cfg.α cfg.q cfg.s)

/-- The invariant exponent `τ' = min{δ/4, τ_e}`. -/
abbrev paperTauPrime (cfg : FiniteParameters) : ℝ := min (ocDelta cfg.α cfg.q / 4) cfg.τe

/-- The representation order `K = J N_w + (N_T + 2p_T) + 4` of the finite assembly. -/
abbrev paperRepOrder (cfg : FiniteParameters) : ℕ := cfg.Jw * cfg.Nw + (cfg.NT + 2 * cfg.pT) + 4

/-- The word count of the successor alphabet (words of length at most `J + 1`). -/
abbrev paperWordCount (cfg : FiniteParameters) : ℕ :=
  (wordsUpTo (succAlphabetOf (paperDepthBound cfg) (paperOrderBound cfg) cfg.H cfg.J cfg.N cfg.p 0)
    (cfg.J + 1)).card

/-- **Admissible seed** of level `n` on `[t_S, t_f]` at the parameters `cfg`: a generated seed
with the seed constants `(C_e, k_S, τ_e)` and the a priori bounds `(r̄₀, D̄₀)`, with its
pointwise molecular envelope, below the terminal level `M`, on a window of length at most `T`. -/
def IsPaperSeed (cfg : FiniteParameters) {D : OCData} (M Mnat : ℕ) (law : BirthLaw)
    (seedK freshK : ℕ → KernelSpec)
    (seed : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀) (n : ℕ) (tS tf : ℝ) : Prop :=
  IsGeneratedSeed law (paperProv cfg D) seedK freshK cfg.φ₀ cfg.hφ₀ Mnat cfg.kS seed n tS tf
      cfg.Ce cfg.τe (paperDepthBound cfg) (paperOrderBound cfg) ∧
    IsSeedPointwiseMolecular law cfg.kS seed tS tf ∧ n < M ∧ tf - tS ≤ cfg.T₀

/-- **Admissible family** `G` of level `m` on `[t_A, t_f]`: there are `t_S ≤ t_A` and an
admissible seed on `[t_S, t_f]` of which `G` is a cascade stage, `G` has level `m`, and `G`
satisfies the stage invariant on `[t_A, t_f]` with ledger `C_I ε_m^{τ'}` and Schur price
`C_I ε_{m-1}^{qτ'}`. -/
def IsPaperFamily (cfg : FiniteParameters) {D : OCData} (M Mnat : ℕ) (law : BirthLaw)
    (seedK freshK : ℕ → KernelSpec)
    (G : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀) (m : ℕ) (tA tf : ℝ) : Prop :=
  ∃ (tS : ℝ) (seed : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀) (n : ℕ),
    tS ≤ tA ∧ IsPaperSeed cfg M Mnat law seedK freshK seed n tS tf ∧
    IsCascadeStage D (paperProv cfg D) (paperMenu cfg Mnat) seed G ∧ G.level = m ∧
    IsStageInvariant law (paperProv cfg D) seedK freshK cfg.φ₀ cfg.hφ₀ Mnat cfg.kI tA tf
      (cfg.CI * D.eps m ^ paperTauPrime cfg)
      (cfg.CI * D.eps (m - 1) ^ (cfg.q * paperTauPrime cfg)) G

/-- The tail of `iteration_passage` after its constants `C, C_Q, m_*`, at the parameters `cfg`:
their schedule, `K = K_strong`, `P_acc = 2`, `n_pad = 0`, their lift floors
`s_X, s_Z`, seed constants `(C_e, k_S)`, invariant constants `k_I`, ledger constants
`(C_I, C_w)` and carrier start `j₀`. -/
def PassageLevelStatement (cfg : FiniteParameters) (C CQ : ℝ) (mStar : ℕ) : Prop :=
  ∀ (D : OCData), D.α = cfg.α → D.q = cfg.q → D.Λ = cfg.Λ → D.ζ = cfg.ζ →
    IsOCStreamSeq cfg.α cfg.q cfg.Λ cfg.ζ D.Φ →
  ∀ (M : ℕ), IsOCBandChain cfg.α cfg.q cfg.Λ cfg.ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
  ∀ (law : BirthLaw), IsSuccessorLaw cfg.α cfg.q cfg.s (paperWordCount cfg) law →
  ∀ (seedK freshK : ℕ → KernelSpec),
    (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D cfg.kI.cr cfg.σ₀ cfg.nk.toPNat' b' (freshK b')) →
  ∀ (seed : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀) (n : ℕ) (tS tf : ℝ),
    IsGeneratedSeed law (paperProv cfg D) seedK freshK cfg.φ₀ cfg.hφ₀ Mnat cfg.kS seed n tS tf
      cfg.Ce cfg.τe (paperDepthBound cfg) (paperOrderBound cfg) →
    IsSeedPointwiseMolecular law cfg.kS seed tS tf →
  ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
  ∀ (tA s₀ : ℝ), tS ≤ tA → tA + 3 * ocTau cfg.α cfg.q cfg.Λ m ≤ s₀ →
    s₀ + 4 * ocTauPP cfg.α cfg.q cfg.Λ m ≤ tf → tf - s₀ ≤ cfg.T₀ →
  ∀ (G G' : GenStage D ScalarH (paperFamilyOrder cfg) cfg.bw cfg.j₀),
    IsCascadeStage D (paperProv cfg D) (paperMenu cfg Mnat) seed G → G.level = m →
    IsStageInvariant law (paperProv cfg D) seedK freshK cfg.φ₀ cfg.hφ₀ Mnat cfg.kI tA tf
      (cfg.CI * D.eps m ^ paperTauPrime cfg)
      (cfg.CI * D.eps (m - 1) ^ (cfg.q * paperTauPrime cfg)) G →
    IsActualSuccessor D (paperProv cfg D) (paperMenu cfg Mnat) G G' →
  ∃ (tp : ℝ) (Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn G.comps, TorusHk cfg.Nout (ScalarH v.1.root))),
    PassageFrame law (paperProv cfg D) (paperMenu cfg Mnat) seedK freshK cfg.φ₀ cfg.hφ₀ Mnat
      cfg.kI cfg.CI cfg.τe seed G (G'.retained m cfg.H cfg.J) m (succEta0 cfg.α cfg.q cfg.s)
      cfg.Kres (paperWordCount cfg) cfg.p cfg.Nout cfg.Naux cfg.Q CQ C tA s₀ tf tp Preg ∧
    PassageOutput law (paperProv cfg D) seedK freshK cfg.φ₀ cfg.hφ₀ G (G'.retained m cfg.H cfg.J)
      m cfg.p cfg.N (succSchedR (paperDepthBound cfg) cfg.J cfg.H) cfg.sX cfg.sZ
      (paperRepOrder cfg) cfg.Naux cfg.s (succEta0 cfg.α cfg.q cfg.s) (ocMuS cfg.α cfg.q cfg.s)
      (ocDelta cfg.α cfg.q - 2 * cfg.σ₀) 2 cfg.Q C cfg.kI.cr cfg.kI.c₀ s₀ tp tf (freshK (m - 1))
      Preg

/-- **The floor (14.7) of the terminal system**: Section 12's floor (12.9) at `m = M` with the
terminal orders. In the paper's symbols, with `N_ce = N_T`, `p_e = p_T`, `N_cl,e = A_T`,
`N_le = R_T`, `n = J_w`, `N_cor,w = N_w`, `N_len,w = R_w`:
`N_se = N_ce + nN_cor,w + 4p_e + 1`, `N̄_mom = max{N_mom,w, N_mom,e, N_mom}` (`L_p^T`, `L_c^T`, `L`),
`N_path,e = (N_le + 2)(nN_len,w + 1)`, `N_rec,e = 4(N_ce + N_se) + 2N_cl,e + 16`, and the floor is
`max{N_rec,e + N_se + N̄_mom + 6p_e, N_se - 2 + N̄_mom + N_ce + 2p_e + 1,
N_rec,e + 2N_seN_path,e + max{N_se + N̄_mom + N_ce + 6p_e + 4, (N_path,e + 3)(N_ce + N_se + 12) + 2p_e}}`. -/
def paperTermFloorOf (NT pT AT RT Jw Nw Rw LpT LcT L : ℕ) : ℕ :=
  let Nse := NT + Jw * Nw + 4 * pT + 1
  let Nmom := max LpT (max LcT L)
  let Npath := (RT + 2) * (Jw * Rw + 1)
  let Nrec := 4 * (NT + Nse) + 2 * AT + 16
  max (max (Nrec + Nse + Nmom + 6 * pT) (Nse - 2 + Nmom + NT + 2 * pT + 1))
    (Nrec + 2 * Nse * Npath +
      max (Nse + Nmom + NT + 6 * pT + 4) ((Npath + 3) * (NT + Nse + 12) + 2 * pT))

/-- The floor (14.7) of the paper at the parameters `cfg` (`N_mom,w = L_p^T`, `N_mom,e = L_c^T`,
`N_mom = L`). -/
abbrev paperTermFloor (cfg : FiniteParameters) : ℕ :=
  paperTermFloorOf cfg.NT cfg.pT cfg.AT cfg.RT cfg.Jw cfg.Nw cfg.Rw cfg.LpT cfg.LcT cfg.L

/-- The finite-assembly parameters extended by the data they are built from: the cascade schedule,
the constants and the tail of `iteration_passage` at these parameters, and the level
`m_E` of the invariant's Schur price. -/
structure PaperParameters (α s q : ℝ) (ζ : ℝ → ℝ) (Λ Jw : ℕ) (t₀ T₀ : ℝ) where
  /-- The finite-assembly parameters (`finite_parameters_of_registered_inputs`). -/
  ready : FiniteAssemblyReady α s q ζ Λ Jw t₀ T₀
  /-- The closure order `A_cl` of the cascade schedule. -/
  Acl : ℕ
  /-- The width `a` of the cascade schedule. -/
  schedA : ℝ
  /-- The width `σ` of the cascade schedule (`σ₀ = a + σ`). -/
  schedSigma : ℝ
  /-- The schedule block at `K = K_strong`, `P_acc = 2`, `σ_E = δ`. -/
  schedule : IsCascadeSchedule ready.cfg.α ready.cfg.s ready.cfg.q (paperRepOrder ready.cfg) 2
    ready.cfg.lamE (ocDelta ready.cfg.α ready.cfg.q) (paperOrderBound ready.cfg) ready.cfg.Q
    ready.cfg.H ready.cfg.J ready.cfg.N ready.cfg.p ready.cfg.nk ready.cfg.Lc ready.cfg.Lf
    ready.cfg.Lpr Acl ready.cfg.Naux ready.cfg.Nout ready.cfg.Kres ready.cfg.L ready.cfg.σ₀
    schedA schedSigma
  /-- The reconstruction floor of `cascade_schedule_exists`. -/
  recon : succReconFloor (paperDepthBound ready.cfg) (paperOrderBound ready.cfg) ready.cfg.H
    ready.cfg.J ready.cfg.N ready.cfg.p Acl ready.cfg.Lc ≤ ready.cfg.Naux
  /-- The threshold for which the invariant constants were chosen (`exists_invariantAdmissible`). -/
  invThr : InvConsts
  /-- The invariant constants `k_I` are admissible for the seed constants `k_S`. -/
  invariant : IsInvariantAdmissible ready.cfg.kS invThr ready.cfg.kI ready.cfg.H ready.cfg.J
    ready.cfg.N ready.cfg.p ready.cfg.nk ready.cfg.Kres ready.cfg.Lpr ready.cfg.Lc ready.cfg.Lf
    ready.cfg.σ₀ (ocDelta ready.cfg.α ready.cfg.q) ready.cfg.q (ocC ready.cfg.α ready.cfg.q)
  /-- The molecular radius constant is at most one (`ρ_⋆(m) ≤ ε_{m-1}`). -/
  seed_c₀_le : ready.cfg.kS.c₀ ≤ 1
  /-- The constant `C` of `iteration_passage` at the parameters. -/
  Cpass : ℝ
  /-- The constant `C_Q` of `iteration_passage` at the parameters. -/
  CQpass : ℝ
  /-- The threshold `m_*` of `iteration_passage` at the parameters. -/
  mStar : ℕ
  /-- `iteration_passage` at the parameters. -/
  passage : PassageLevelStatement ready.cfg Cpass CQpass mStar
  /-- A level above which the invariant's Schur price is at most `1/8`. -/
  mEnergy : ℕ
  /-- The level `m_E` is above the carrier start. -/
  energy_start : ready.cfg.j₀ ≤ mEnergy
  /-- The Schur price `C_I ε_j^{qτ'} ≤ 1/8` for `j ≥ m_E`. -/
  energy_floor : ∀ j, mEnergy ≤ j →
    ready.cfg.CI * ocEpsilon ready.cfg.q ready.cfg.Λ j ^ (ready.cfg.q * paperTauPrime ready.cfg) ≤
      1 / 8
  /-- The carrier start also satisfies the carrier smallness with `C_H = Υ = 1` (the complex
  chain lemma, `chainFam_over`). -/
  carrier_one : IsCarrierStart ready.cfg.α ready.cfg.q ready.cfg.Λ ready.cfg.bw 1 1 ready.cfg.j₀
  /-- The carrier start also satisfies the cycle smallness with `C_H = 1`, `Υ = 100`:
  `ε_k^{β-2}h_{k+1} ≤ c_an/(1024π²·100) ≤ 10^{-6}c_an`. -/
  carrier_cycle : IsCarrierStart ready.cfg.α ready.cfg.q ready.cfg.Λ ready.cfg.bw 1 100 ready.cfg.j₀
  /-- The width parameter of the carriers is at most `10^{-4}` (the complex chain lemma). -/
  bw_le : ready.cfg.bw ≤ 1 / 10000
  /-- The seed constants are those of the reserve plan: envelope margin `0`, and the orders
  `K_an = L_an = J_m = K_s`. -/
  seed_plan : ready.cfg.kS.mEnv = 0 ∧ ready.cfg.kS.Kan = ready.cfg.kS.Ks ∧
    ready.cfg.kS.Lan = ready.cfg.kS.Ks ∧ ready.cfg.kS.Jm = ready.cfg.kS.Ks
  /-- The mollifier `φ₀` is smooth and supported in the closed unit ball (`exists_mollifier`). -/
  mollifier : ContDiff ℝ (⊤ : ℕ∞) ready.cfg.φ₀ ∧
    Function.support ready.cfg.φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall
  /-- The entry's readout exponent `η₀ = δ/16`. -/
  eta0_eq : ready.cfg.η₀ = ocDelta ready.cfg.α ready.cfg.q / 16
  /-- The weak width exponent `σ_w = γ/4 + δ/2` (`r_w = ε_M^{1 + σ_w}`). -/
  sigmaw_eq : ready.cfg.σw =
    ocGamma ready.cfg.α ready.cfg.q / 4 + ocDelta ready.cfg.α ready.cfg.q / 2
  /-- The seed's molecular exponent `Θ_mol,seed = σ_f = δ`. -/
  sigmaf_eq : ready.cfg.kS.σf = ocDelta ready.cfg.α ready.cfg.q
  /-- The seed exponent `Θ_seed = τ_e = δ/4`. -/
  taue_eq : ready.cfg.τe = ocDelta ready.cfg.α ready.cfg.q / 4
  /-- The seed preparation exponent `Θ_prep,seed = λ_E = 4δ`. -/
  lamE_eq : ready.cfg.lamE = 4 * ocDelta ready.cfg.α ready.cfg.q
  /-- The fresh width exponent `Θ_e = t_T = δ/(16(s_T + 1))`, `s_T` the excess of the terminal
  alphabet. -/
  tT_eq : ready.cfg.tT = ocDelta ready.cfg.α ready.cfg.q /
    (16 * ((termExcess ready.cfg.NT ready.cfg.pT (termAlphabet ready.cfg.NT ready.cfg.pT
      (1 + ready.cfg.Jw * ready.cfg.Nw) (ready.cfg.Jw * ready.cfg.Rw)) : ℝ) + 1))
  /-- The terminal schedule at the parameters (`IsTerminalSchedule`, with
  `χ_w = weakChi α q η₀` and the terminal alphabet): `L_w + 5 ≤ k₀`, the accuracy `Q_T`, the
  corrector, length, truncation and antidivergence orders `N_T, R_T, p_T, A_T`, the exponents
  `η₀`, `t_T`, and the moment orders `L_c, L_o, L_f, L_p`. -/
  term_schedule : IsTerminalSchedule ready.cfg.α ready.cfg.q ready.cfg.s ready.cfg.PT ready.cfg.QT
    ready.cfg.σw (weakChi ready.cfg.α ready.cfg.q ready.cfg.η₀) ready.cfg.η₀ ready.cfg.tT
    ready.cfg.Jw ready.cfg.Lw ready.cfg.k₀ ready.cfg.NT ready.cfg.pT ready.cfg.RT ready.cfg.AT
    ready.cfg.LcT ready.cfg.LoT ready.cfg.LfT ready.cfg.LpT
    (termAlphabet ready.cfg.NT ready.cfg.pT (1 + ready.cfg.Jw * ready.cfg.Nw)
      (ready.cfg.Jw * ready.cfg.Rw))
  /-- The terminal accuracy `Q_T = 2(P_T + q^{J_w+1}(1+s) + 3)` (`Q_e = 2(5 + q^{n+1}(1+s))` at
  `P_T = 2`). -/
  QT_eq : ready.cfg.QT =
    2 * (ready.cfg.PT + ready.cfg.q ^ (ready.cfg.Jw + 1) * (1 + ready.cfg.s) + 3)
  /-- The three terminal moment orders are equal: `L_o = L_f = L_p`. -/
  moment_orders_eq : ready.cfg.LoT = ready.cfg.LpT ∧ ready.cfg.LfT = ready.cfg.LpT
  /-- The moment order of the weak smoothing kernel is at least the terminal moment order:
  `L_p ≤ L_t`. -/
  LpT_le_Lt : ready.cfg.LpT ≤ ready.cfg.Lt
  /-- The weak readout order is the full composition order `L_w = J_w N_w`
  (`WeakEntryOrders.L_eq`). -/
  Lw_eq : ready.cfg.Lw = ready.cfg.Jw * ready.cfg.Nw
  /-- The weak reserve floor `L_t + J_w N_w + 1 + max{L_w + 5, k₀} ≤ K_w`. -/
  Kw_floor : ready.cfg.Lt + ready.cfg.Jw * ready.cfg.Nw + 1 + max (ready.cfg.Lw + 5) ready.cfg.k₀ ≤
    ready.cfg.Kw
  /-- The seed's coarse width exponent is the schedule's: `Θ_prep,seed = λ_E = 4δ`. -/
  lamC_seed_eq : ready.cfg.kS.lamC = 4 * ocDelta ready.cfg.α ready.cfg.q
  /-- The invariant's coarse width exponent: `Θ_prep = 4δ`. -/
  lamC_inv_eq : ready.cfg.kI.lamC = 4 * ocDelta ready.cfg.α ready.cfg.q
  /-- One approximation and moment order: `N_pr = N_cs = N_fs = N_mom = N_ker`. -/
  orders_eq : ready.cfg.Lpr = ready.cfg.L ∧ ready.cfg.Lc = ready.cfg.L ∧
    ready.cfg.Lf = ready.cfg.L ∧ ready.cfg.kI.Lker = ready.cfg.L
  /-- The terminal successor's birth-radius constant is the cascade's: `c_r = c_sm`. -/
  cr_eq : ready.cfg.cr = ready.cfg.kI.cr
  /-- The kernel orders: the weak kernel order `n_W` covers `L_t` and the terminal moment orders,
  and the fresh kernel order `n_T` covers `L_c^T` and the schedule's approximation orders. -/
  kernel_orders : ready.cfg.Lt + 1 ≤ 2 * (ready.cfg.nW : ℕ) ∧
    IsTerminalKernelOrders ready.cfg.nW ready.cfg.LoT ready.cfg.LfT ready.cfg.LpT ready.cfg.Lpr
      ready.cfg.Lc ready.cfg.Lf ∧
    IsFreshKernelOrder ready.cfg.nT ready.cfg.LcT ready.cfg.Lpr ready.cfg.Lc ready.cfg.Lf
  /-- The terminal successor's birth-radius constant is one: `c_r = 1` (the reserve plan). -/
  cr_one : ready.cfg.cr = 1
  /-- The invariant's birth-radius constant is one: `c_sm = k_I.c_r = 1`. -/
  kI_cr_one : ready.cfg.kI.cr = 1
  /-- The weak orders (14.1): `(q-1)N_w > P_w + 2q^{J_w} + 3` and
  `2a_*(R_w+1) > P_w + 3q^{J_w} + 2` (`WeakEntryOrders.order_N`, `order_R`). -/
  weak_orders : ready.cfg.Pw + 2 * ready.cfg.q ^ ready.cfg.Jw + 1 + 2 <
      (ready.cfg.Nw : ℝ) * (ready.cfg.q - 1) ∧
    ready.cfg.Pw + 2 * ready.cfg.q ^ ready.cfg.Jw + 1 + ready.cfg.q ^ ready.cfg.Jw + 1 <
      2 * weakAStar ready.cfg.α ready.cfg.q * ((ready.cfg.Rw : ℝ) + 1)
  /-- The reading order of the terminal comparison is above the floor (14.7) of the terminal
  system, so the output order `N_oe = max{K_out, 2k₀ + 2, N_T + 2p_T + k₀ + 2}` is too. -/
  term_floor : paperTermFloor ready.cfg ≤ ready.cfg.k₀

/-- **The bottom level** `m₀ = max{m_*, m₀^cas, m_E + 1}` of the cascade. -/
def paperBottom {α s q : ℝ} {ζ : ℝ → ℝ} {Λ Jw : ℕ} {t₀ T₀ : ℝ}
    (P : PaperParameters α s q ζ Λ Jw t₀ T₀) : ℕ :=
  max P.mStar (max P.ready.cfg.m₀ (P.mEnergy + 1))

end AVRegularity.PaperFacing
