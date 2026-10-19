-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.PaperFacing.Basic
import AVRegularity.Proofs.Results.Entry.EntryTerminalFull
import AVRegularity.Proofs.Results.Iteration.IterationCascade
import AVRegularity.Proofs.Results.Iteration.CascadeSchedule
import AVRegularity.Finite.TerminalLift.PositiveTransfer
import AVRegularity.Proofs.Results.Finite.TerminalLiftRep
import AVRegularity.Proofs.Results.Construction.ComparisonLiftPositiveLayer
import AVRegularity.Proofs.Results.Finite.TerminalSeedTransport
import AVRegularity.Proofs.Results.Finite.TraceClosure
import AVRegularity.Finite.StrongEntry.SeedRepresentation
import AVRegularity.IterationPassage.Cascade.RunAssembly
import AVRegularity.Construction.Preservation.Assembly.PreparationJointInputs
import AVRegularity.Construction.EntryScales.TerminalCore
import AVRegularity.Construction.Scales.Times

/-! # The parameters of the paper-facing theorems exist

`paper_parameters_exist`: for `Λ ≥ Λ₀`, `J ≥ 1` and `0 < t₀ < T` there is a `PaperParameters`. The
proof repeats the constant selection of `finite_parameters_of_registered_inputs` and
`finite_ready_from_menus` with three changes:

* the schedule is that of `cascade_schedule_exists` (so `succReconFloor ≤ N_aux` holds) with its
  four moment orders `L_c, L_f, L_pr, L` replaced by their maximum and `N_aux, K_res, N_out` raised
  by it (`paper_one_order_schedule`), and the cascade is `iteration_cascade_of_schedule` at it;
* the reading order `k₀ = N_rd,e` is chosen after the schedule, above the floor (14.7) of the
  paper (`paperTermFloorOf`), so the terminal output order `N_oe ≥ 2k₀ + 2` is too;
* `iteration_passage` is applied at the same schedule; its thresholds are joined with those of
  the cascade (`Λ₀` by max; `c₀max` by min, also with `1`; lift floors and `K_need` by max; the
  invariant thresholds by `certificateThresholdJoin`; carrier constants and ledger thresholds by
  max), so that both tails hold at the selected constants;
* the energy level `m_E = max{m_F, j₀}`, with `C_I ε_j^{qτ'} ≤ 1/8` for `j ≥ m_F` (`scale_floor`).

`paper_parameters_exist_order`: the same, with the four orders of the invariant constants equal and at
least a prescribed function `K_req` of the schedule (`PaperSchedule`, `paperScheduleOf`); the entry
floor is raised to `K_req` and `k_I` takes the order `max K_req K_res`.

The steps: `PaperPassageTail` (the passage tail, verbatim), `paperParametersOfLevels` (the
parameters from the level facts), `paper_ready_from_menus` (constants after the menus, at a
prescribed order), `paper_parameters_exist_order` (the menus), `paper_parameters_exist` (the case
`K_req = 0`). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal

namespace AVRegularity.PaperFacing

open AVRegularity.Finite.Assembly AVRegularity.Construction.Preservation.Assembly

/-- The tail of `iteration_passage` after its schedule block and lift floors (the analogue of
`CascadeTail`), copied verbatim from `IterationPassageStatement`. -/
private def PaperPassageTail (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (c₀max : ℝ) (φ₀ : Vec 2 → ℝ)
    (hφ₀ : Integrable φ₀) (bw : ℝ) (K : ℕ) (Pacc T₀ : ℝ) (r₀ D₀ : ℕ) (τe lamE σE Q : ℝ)
    (H J N p nk Lc Lf Lpr Naux Nout Kres npad sX sZ Kneed : ℕ) (σ₀ : ℝ) : Prop :=
    ∀ (Ce : ℝ) (kS : InvConsts), 1 ≤ Ce →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → kS.σf = σE → kS.lamC = lamE →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
      Kneed ≤ kS.Ks → Kneed ≤ kS.Kan → Kneed ≤ kS.Lan → Kneed ≤ kS.Jm →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∃ (C CQ : ℝ) (mStar : ℕ),
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

/-- The parameters from the level facts, with `ready.cfg = cfg` by construction. -/
private def paperParametersOfLevels (cfg : FiniteParameters) (valid : FiniteLocalValidity cfg)
    (CT CwLift : ℝ) (hCT : 0 ≤ CT) (hCwLift : 0 ≤ CwLift) (hc : 0 < cfg.c) (hCcas : 0 < cfg.Ccas)
    (hPw : cfg.Pw = 2) (hPT : cfg.PT = 2) (hτ : cfg.τ ≤ cfg.t₀)
    (ME MT MW Mwait Mseed : ℕ)
    (hseed : ∀ M, Mseed ≤ M → FiniteSeedBudgetLevel cfg M)
    (hwait : ∀ M, Mwait ≤ M → (|cfg.C| + 1) * ocTauPP cfg.α cfg.q cfg.Λ M +
      6 * cfg.Jw * ocTauPP cfg.α cfg.q cfg.Λ (M + 1) ≤ cfg.t₀ / 4)
    (hE : ∀ M, ME ≤ M → EntryLevelStatement cfg M)
    (hT : ∀ M, MT ≤ M → TerminalLiftLevelStatement cfg CT M)
    (hW : ∀ M, MW ≤ M → WeakLiftLevelStatement cfg CwLift M)
    (hCas : CascadeLevelStatement cfg)
    (hA : ∀ D : OCData, D.α = cfg.α → D.q = cfg.q → D.Λ = cfg.Λ → D.ζ = cfg.ζ →
      IsOCStreamSeq cfg.α cfg.q cfg.Λ cfg.ζ D.Φ → ∀ M,
      IsOCBandChain cfg.α cfg.q cfg.Λ cfg.ζ M D.κ →
      ∀ b', 1 ≤ b' → b' < M → ∃ H₁ H₂ : ℝ → Vec 2 →L[ℝ] Vec 2, IsFreshAxes D b' H₁ H₂)
    (Acl : ℕ) (schedA schedSigma : ℝ)
    (hsched : IsCascadeSchedule cfg.α cfg.s cfg.q (paperRepOrder cfg) 2 cfg.lamE
      (ocDelta cfg.α cfg.q) (paperOrderBound cfg) cfg.Q cfg.H cfg.J cfg.N cfg.p cfg.nk cfg.Lc
      cfg.Lf cfg.Lpr Acl cfg.Naux cfg.Nout cfg.Kres cfg.L cfg.σ₀ schedA schedSigma)
    (hrecon : succReconFloor (paperDepthBound cfg) (paperOrderBound cfg) cfg.H cfg.J cfg.N cfg.p
      Acl cfg.Lc ≤ cfg.Naux)
    (invThr : InvConsts)
    (hinv : IsInvariantAdmissible cfg.kS invThr cfg.kI cfg.H cfg.J cfg.N cfg.p cfg.nk cfg.Kres
      cfg.Lpr cfg.Lc cfg.Lf cfg.σ₀ (ocDelta cfg.α cfg.q) cfg.q (ocC cfg.α cfg.q))
    (hc₀ : cfg.kS.c₀ ≤ 1) (Cpass CQpass : ℝ) (mStar : ℕ)
    (hpass : PassageLevelStatement cfg Cpass CQpass mStar) (mEnergy : ℕ)
    (hstart : cfg.j₀ ≤ mEnergy)
    (hfloor : ∀ j, mEnergy ≤ j →
      cfg.CI * ocEpsilon cfg.q cfg.Λ j ^ (cfg.q * paperTauPrime cfg) ≤ 1 / 8)
    (hone : IsCarrierStart cfg.α cfg.q cfg.Λ cfg.bw 1 1 cfg.j₀)
    (hcyc : IsCarrierStart cfg.α cfg.q cfg.Λ cfg.bw 1 100 cfg.j₀) (hbw1 : cfg.bw ≤ 1 / 10000)
    (hplanS : cfg.kS.mEnv = 0 ∧ cfg.kS.Kan = cfg.kS.Ks ∧ cfg.kS.Lan = cfg.kS.Ks ∧
      cfg.kS.Jm = cfg.kS.Ks)
    (hmoll : ContDiff ℝ (⊤ : ℕ∞) cfg.φ₀ ∧
      Function.support cfg.φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall)
    (hη₀ : cfg.η₀ = ocDelta cfg.α cfg.q / 16)
    (hσw : cfg.σw = ocGamma cfg.α cfg.q / 4 + ocDelta cfg.α cfg.q / 2)
    (hσf : cfg.kS.σf = ocDelta cfg.α cfg.q) (hτe : cfg.τe = ocDelta cfg.α cfg.q / 4)
    (hlamE : cfg.lamE = 4 * ocDelta cfg.α cfg.q)
    (htT : cfg.tT = ocDelta cfg.α cfg.q / (16 * ((termExcess cfg.NT cfg.pT (termAlphabet cfg.NT
      cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw)) : ℝ) + 1)))
    (hsch : IsTerminalSchedule cfg.α cfg.q cfg.s cfg.PT cfg.QT cfg.σw (weakChi cfg.α cfg.q cfg.η₀)
      cfg.η₀ cfg.tT cfg.Jw cfg.Lw cfg.k₀ cfg.NT cfg.pT cfg.RT cfg.AT cfg.LcT cfg.LoT cfg.LfT cfg.LpT
      (termAlphabet cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw)))
    (hQT : cfg.QT = 2 * (cfg.PT + cfg.q ^ (cfg.Jw + 1) * (1 + cfg.s) + 3))
    (hmom : cfg.LoT = cfg.LpT ∧ cfg.LfT = cfg.LpT) (hLpLt : cfg.LpT ≤ cfg.Lt)
    (hLwJ : cfg.Lw = cfg.Jw * cfg.Nw)
    (hKwF : cfg.Lt + cfg.Jw * cfg.Nw + 1 + max (cfg.Lw + 5) cfg.k₀ ≤ cfg.Kw)
    (hlamS : cfg.kS.lamC = 4 * ocDelta cfg.α cfg.q) (hlamI : cfg.kI.lamC = 4 * ocDelta cfg.α cfg.q)
    (hord : cfg.Lpr = cfg.L ∧ cfg.Lc = cfg.L ∧ cfg.Lf = cfg.L ∧ cfg.kI.Lker = cfg.L)
    (hcrI : cfg.cr = cfg.kI.cr)
    (hkern : cfg.Lt + 1 ≤ 2 * (cfg.nW : ℕ) ∧
      IsTerminalKernelOrders cfg.nW cfg.LoT cfg.LfT cfg.LpT cfg.Lpr cfg.Lc cfg.Lf ∧
      IsFreshKernelOrder cfg.nT cfg.LcT cfg.Lpr cfg.Lc cfg.Lf)
    (hcrone : cfg.cr = 1) (hkIcr : cfg.kI.cr = 1)
    (hwo : cfg.Pw + 2 * cfg.q ^ cfg.Jw + 1 + 2 < (cfg.Nw : ℝ) * (cfg.q - 1) ∧
      cfg.Pw + 2 * cfg.q ^ cfg.Jw + 1 + cfg.q ^ cfg.Jw + 1 <
        2 * weakAStar cfg.α cfg.q * ((cfg.Rw : ℝ) + 1))
    (hfloorT : paperTermFloor cfg ≤ cfg.k₀) :
    PaperParameters cfg.α cfg.s cfg.q cfg.ζ cfg.Λ cfg.Jw cfg.t₀ cfg.T₀ where
  ready := {
    cfg := cfg, base := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    valid := valid, CT := CT, CwLift := CwLift, hCT := hCT, hCwLift := hCwLift, hc := hc
    hCcas := hCcas, hPw := hPw, hPT := hPT, hτ := hτ
    Mstar := max ME (max MT (max MW (max Mwait (max Mseed (cfg.m₀ + 2)))))
    levels := fun M hM => ⟨by omega, hseed M (by omega), hwait M (by omega), hE M (by omega),
      hT M (by omega), hW M (by omega)⟩
    cascade := hCas, axes := hA }
  Acl := Acl
  schedA := schedA
  schedSigma := schedSigma
  schedule := hsched
  recon := hrecon
  invThr := invThr
  invariant := hinv
  seed_c₀_le := hc₀
  Cpass := Cpass
  CQpass := CQpass
  mStar := mStar
  passage := hpass
  mEnergy := mEnergy
  energy_start := hstart
  energy_floor := hfloor
  carrier_one := hone
  carrier_cycle := hcyc
  bw_le := hbw1
  seed_plan := hplanS
  mollifier := hmoll
  eta0_eq := hη₀
  sigmaw_eq := hσw
  sigmaf_eq := hσf
  taue_eq := hτe
  lamE_eq := hlamE
  tT_eq := htT
  term_schedule := hsch
  QT_eq := hQT
  moment_orders_eq := hmom
  LpT_le_Lt := hLpLt
  Lw_eq := hLwJ
  Kw_floor := hKwF
  lamC_seed_eq := hlamS
  lamC_inv_eq := hlamI
  orders_eq := hord
  cr_eq := hcrI
  kernel_orders := hkern
  cr_one := hcrone
  kI_cr_one := hkIcr
  weak_orders := hwo
  term_floor := hfloorT

/-- `δ/4 < q χ_w` for `η₀ ≤ δ/8` (in fact `q χ_w ≥ q - 1 ≥ 4δ`). -/
private theorem paper_quarter_delta_lt_qchi {α s q η₀ : ℝ} (hα : 0 < α)
    (hq : IsAdmissibleQ α s q) (hη : η₀ ≤ ocDelta α q / 8) :
    ocDelta α q / 4 < q * weakChi α q η₀ := by
  have hq₁ := hq.1
  have hX : 0 ≤ (2 * q + 1) * (1 + α) / (2 * q + 2) := by positivity
  have hδ : ocDelta α q ≤ (q - 1) / 4 := by
    unfold ocDelta
    have : 0 ≤ (q - 1) / 4 := by linarith
    nlinarith
  have hγ : q - 1 ≤ (q + 2) * ocGamma α q := by
    unfold ocGamma
    rw [← mul_div_assoc, le_div_iff₀ (by linarith)]
    have h1 : q + 1 ≤ (q + 2) * (1 + α) := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ q - 1)
    linarith [show (q + 2) * ((q - 1) * (1 + α)) = (q - 1) * ((q + 2) * (1 + α)) by ring]
  have hχ : q - 1 ≤ weakChi α q η₀ := by
    unfold weakChi weakAStar
    linarith
  have hqχ : weakChi α q η₀ ≤ q * weakChi α q η₀ := by nlinarith
  linarith

/-- The admissible exponents: `4δ < q - 1` and `2γ ≤ 4(q - 1)/3`. -/
private theorem paper_delta_gamma_lt {α s q : ℝ} (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s)
    (hs1 : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) :
    4 * ocDelta α q < q - 1 ∧ 2 * ocGamma α q ≤ 4 / 3 * (q - 1) := by
  obtain ⟨hγ, hδ, -, -, -, -⟩ := AVRegularity.Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq
  have hq1 := hq.1
  have hδ4 : 4 * ocDelta α q < q - 1 := by
    have hf : 0 < (2 * q + 1) * (1 + α) / (2 * q + 2) := by positivity
    unfold ocDelta
    nlinarith
  have hid := EntryScales.ocGamma_mul_identity α q hq1
  exact ⟨hδ4, by nlinarith⟩

/-- `4δ < q²(1 + σ_w) - 1 - c` for `0 < σ_w`. -/
private theorem paper_four_delta_lt_width {α s q σw : ℝ} (hα0 : 0 < α) (hα1 : α < 1 / 3)
    (hs0 : 0 < s) (hs1 : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) (hσ : 0 < σw) :
    4 * ocDelta α q < q ^ 2 * (1 + σw) - 1 - ocC α q := by
  obtain ⟨hδ4, hγ2⟩ := paper_delta_gamma_lt hα0 hα1 hs0 hs1 hq
  have hq1 := hq.1
  have hcdef : ocC α q = ocGamma α q / 2 + ocDelta α q := rfl
  have h1 : q ^ 2 * 1 ≤ q ^ 2 * (1 + σw) := by nlinarith [sq_nonneg q]
  nlinarith

/-- `σ_w = min{c, q - 1}/2 = γ/4 + δ/2`, since `c = γ/2 + δ < q - 1`. -/
private theorem paper_sigmaw_value {α s q : ℝ} (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s)
    (hs1 : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) :
    min (ocC α q) (q - 1) / 2 = ocGamma α q / 4 + ocDelta α q / 2 := by
  obtain ⟨hδ4, hγ2⟩ := paper_delta_gamma_lt hα0 hα1 hs0 hs1 hq
  have hq1 := hq.1
  have hcdef : ocC α q = ocGamma α q / 2 + ocDelta α q := rfl
  rw [min_eq_left (by rw [hcdef]; linarith), hcdef]
  ring

/-- **The order choice at the pinned seed exponents**: `finite_order_choice` with the width exponent
`t_T = δ/(16(s_T + 1))` (`s_T` the excess of the terminal alphabet), the seed exponent
`τ_e = δ/4` and the seed preparation exponent `λ_E = 4δ` (`finite_order_choice` returns
the midpoints of the admissible ranges), one common moment order `L_o = L_f = L_p`, and the value
`Q_T = 2(P_T + q^{J_w+1}(1+s) + 3)`. The schedule holds for every reading order `k₀ ≥ L_w + 5`,
which is chosen later (above the floor (14.7)). -/
private theorem paper_finite_order_choice (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q) :
    ∀ (Jw Nw Rw Lw : ℕ) (η₀ PT : ℝ), 1 ≤ Jw → 0 < η₀ → η₀ ≤ ocDelta α q / 8 → 0 < PT →
    ∀ σw : ℝ, 0 < σw → σw < min (ocC α q) (q - 1) →
    ∃ (QT : ℝ) (NT pT RT AT LcT LoT LfT LpT : ℕ),
      (∀ k₀ : ℕ, Lw + 5 ≤ k₀ → IsTerminalSchedule α q s PT QT σw (weakChi α q η₀) η₀
        (ocDelta α q / (16 * ((termExcess NT pT (termAlphabet NT pT (1 + Jw * Nw) (Jw * Rw)) : ℝ)
          + 1))) Jw Lw k₀ NT pT RT AT LcT LoT LfT LpT
        (termAlphabet NT pT (1 + Jw * Nw) (Jw * Rw))) ∧
      IsEntrySeedExponents α q σw (weakChi α q η₀) η₀
        (ocDelta α q / (16 * ((termExcess NT pT (termAlphabet NT pT (1 + Jw * Nw) (Jw * Rw)) : ℝ)
          + 1))) (ocDelta α q / 4) (4 * ocDelta α q) NT pT (1 + Jw * Nw) (Jw * Rw) ∧
      QT = 2 * (PT + q ^ (Jw + 1) * (1 + s) + 3) ∧ LoT = LpT ∧ LfT = LpT := by
  intro Jw Nw Rw Lw η₀ PT _hJw hη₀ hηδ _hPT σw hσw _hσw₁
  obtain ⟨hγ, hδ, -, -, -, -⟩ := AVRegularity.Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq
  have hq0 : 0 < q := by linarith [hq.1]
  have hτq := paper_quarter_delta_lt_qchi hα₀ hq hηδ
  have hlam4 := paper_four_delta_lt_width hα₀ hα₁ hs₀ hs₁ hq hσw
  set δ := ocDelta α q with hδdef
  set ζ := q * ocGamma α q + 3 * δ with hζdef
  have hζ : 0 < ζ := by positivity
  set χ := weakChi α q η₀ with hχdef
  have hχ : 0 < χ := weakChi_pos hα₀ hq.1 hq.2.1 hηδ
  set QT : ℝ := 2 * (PT + q ^ (Jw + 1) * (1 + s) + 3) with hQT
  obtain ⟨AT, hAT⟩ := Providers.exists_nat_mul_gt hζ 3
  obtain ⟨NT, hNT⟩ := Providers.exists_nat_mul_gt hζ (QT + 2)
  obtain ⟨RT, hRT⟩ := Providers.exists_nat_mul_gt (show 0 < δ / 2 by positivity) (QT + 2)
  obtain ⟨pT, hpT⟩ := Providers.exists_nat_mul_gt hδ (QT + 2)
  set A := termAlphabet NT pT (1 + Jw * Nw) (Jw * Rw) with hA
  set sT : ℝ := (termExcess NT pT A : ℝ) with hsT
  have hsT0 : 0 ≤ sT := Nat.cast_nonneg _
  set tT : ℝ := δ / (16 * (sT + 1)) with htT
  have htT0 : 0 < tT := by positivity
  have htT1 : tT < δ / (8 * (sT + 1)) := by
    rw [htT]; apply div_lt_div_of_pos_left hδ (by positivity); linarith
  have htsT : tT * sT ≤ δ / 16 := by
    rw [htT, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  set bT : ℝ := δ - η₀ - η₀ / 4 - tT * sT with hbT
  have hbT : 0 < bT := by rw [hbT]; linarith
  obtain ⟨LcT, hLc⟩ := Providers.exists_nat_mul_gt htT0 (QT + 2 - bT)
  obtain ⟨LoT, hLo⟩ := Providers.exists_nat_mul_gt (show 0 < ζ + q * σw by positivity)
    (QT + 2 - q * χ)
  obtain ⟨LfT, hLf⟩ := Providers.exists_nat_mul_gt (show 0 < q * σw by positivity)
    (QT + 2 - q * χ)
  obtain ⟨LpT, hLp⟩ := Providers.exists_nat_mul_gt (show 0 < q * σw by positivity)
    (2 * QT + 4 - q * χ)
  -- one common moment order `L_o = L_f = L_p`
  obtain ⟨Lm, hoLm, hfLm, hpLm⟩ : ∃ L : ℕ, LoT ≤ L ∧ LfT ≤ L ∧ LpT ≤ L :=
    ⟨max LoT (max LfT LpT), le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
      (le_max_right _ _).trans (le_max_right _ _)⟩
  have hqσ : 0 ≤ q * σw := by positivity
  have hLo' := mul_le_mul_of_nonneg_left (show (LoT : ℝ) ≤ Lm by exact_mod_cast hoLm)
    (show 0 ≤ ζ + q * σw by positivity)
  have hLf' := mul_le_mul_of_nonneg_left (show (LfT : ℝ) ≤ Lm by exact_mod_cast hfLm) hqσ
  have hLp' := mul_le_mul_of_nonneg_left (show (LpT : ℝ) ≤ Lm by exact_mod_cast hpLm) hqσ
  obtain ⟨-, hw2⟩ := AVRegularity.EntryScales.width_exponent_gaps hα₀ hα₁ hs₀ hs₁ hq hσw htT0
  refine ⟨QT, NT, pT, RT, AT, LcT, Lm, Lm, Lm, fun k₀ hk₀ => ?_, ?_, hQT, rfl, rfl⟩
  · refine ⟨hk₀, ?_, by linarith, by linarith, ?_, by linarith, hη₀, hηδ, htT0, htT1, ?_,
      ?_, ?_, ?_⟩
    · rw [hQT]; linarith
    · linarith
    · show bT + tT * LcT > QT + 2; linarith
    · show q * χ + (ζ + q * σw) * Lm > QT + 2; linarith
    · show q * (χ + σw * Lm) > QT + 2
      have he : q * (χ + σw * Lm) = q * χ + q * σw * Lm := by ring
      linarith
    · show q * (χ + σw * Lm) > 2 * QT + 4
      have he : q * (χ + σw * Lm) = q * χ + q * σw * Lm := by ring
      linarith
  · refine ⟨by positivity, hτq, ?_, by linarith, hlam4, by linarith⟩
    show δ / 4 < bT
    linarith

/-- **The schedule of the parameters**: the orders and exponents of the cascade schedule and of the
entry, all fixed before the invariant order (`N_out = Nout`, `N_ret = Naux`, `K_res`,
`N_pr = Lpr`, …; the source order `N_src = paperFamilyOrder` and the depth bound `paperDepthBound`
are functions of them). -/
structure PaperSchedule where
  /-- The schedule exponent `Q`. -/
  Q : ℝ
  /-- The schedule width `σ₀`. -/
  σ₀ : ℝ
  /-- The weak entry orders `J_w`, `N_w`, `R_w`. -/
  Jw : ℕ
  Nw : ℕ
  Rw : ℕ
  /-- The terminal orders `N_T`, `p_T`, `R_T`. -/
  NT : ℕ
  pT : ℕ
  RT : ℕ
  /-- The cascade orders `H, J, N, p, n_k, L_c, L_f, L_pr, N_aux, N_out, K_res, L`. -/
  H : ℕ
  J : ℕ
  N : ℕ
  p : ℕ
  nk : ℕ
  Lc : ℕ
  Lf : ℕ
  Lpr : ℕ
  Naux : ℕ
  Nout : ℕ
  Kres : ℕ
  L : ℕ

/-- The schedule of the parameters `cfg`. -/
def paperScheduleOf (cfg : FiniteParameters) : PaperSchedule where
  Q := cfg.Q
  σ₀ := cfg.σ₀
  Jw := cfg.Jw
  Nw := cfg.Nw
  Rw := cfg.Rw
  NT := cfg.NT
  pT := cfg.pT
  RT := cfg.RT
  H := cfg.H
  J := cfg.J
  N := cfg.N
  p := cfg.p
  nk := cfg.nk
  Lc := cfg.Lc
  Lf := cfg.Lf
  Lpr := cfg.Lpr
  Naux := cfg.Naux
  Nout := cfg.Nout
  Kres := cfg.Kres
  L := cfg.L

/-- The invariant constants at the order `max K K_res` (`exists_invariantAdmissible` with the four
orders `max K K_res` in place of `K_res`), for seed constants of order at least `max K K_res`. -/
private theorem paper_exists_invariantAdmissible_at (kS thr : InvConsts)
    (r₀ D₀ H J N p nk Kres Lpr Lc Lf K : ℕ) (σ₀ δ q c : ℝ) (hσ₀ : 0 < σ₀)
    (hσl : σ₀ < kS.lamC) (hq : 1 < q) (hc : 0 < c)
    (halloc : IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf)
    (hK : max K Kres ≤ kS.Ks ∧ max K Kres ≤ kS.Kan ∧ max K Kres ≤ kS.Lan ∧ max K Kres ≤ kS.Jm)
    (hnk : max Lpr (max Lc Lf) + 1 ≤ 2 * nk) :
    ∃ kI : InvConsts, IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ δ q c ∧
      K ≤ kI.Ks ∧ kI.Kan = kI.Ks ∧ kI.Lan = kI.Ks ∧ kI.Jm = kI.Ks ∧
      kI.lamC = min kS.lamC ((q - 1) * (1 + c) + q * σ₀) ∧ kI.Lker = max Lpr (max Lc Lf) := by
  obtain ⟨hL, -, -, -, -, hLs, -, -, hHp, hm0, hm1⟩ := halloc
  have hlam : σ₀ < (q - 1) * (1 + c) + q * σ₀ := by nlinarith
  refine ⟨InvConsts.mk kS.c₀ kS.cr (max kS.Γk thr.Γk) (max kS.Cwid thr.Cwid)
    (min kS.σf (δ + σ₀)) (min kS.lamC ((q - 1) * (1 + c) + q * σ₀)) (max kS.Ca thr.Ca) kS.mEnv
    (fun j => max (kS.Cm j) (thr.Cm j)) (fun j => max (kS.cker j) (thr.cker j)) (max K Kres)
    (max K Kres) (max K Kres) (max K Kres) (max Lpr (max Lc Lf)) (succLstar Kres kS.G0 H J N p)
    kS.G0 kS.Hprod, ?_, le_max_left _ _, rfl, rfl, rfl, rfl, rfl⟩
  exact ⟨rfl, rfl, le_max_left _ _, le_max_right _ _, le_max_left _ _, le_max_right _ _, rfl,
    lt_min hσl hlam, min_le_left _ _, min_le_right _ _, le_max_left _ _, le_max_right _ _,
    fun j => ⟨le_max_left _ _, le_max_right _ _⟩, fun j => ⟨le_max_left _ _, le_max_right _ _⟩,
    le_rfl, hL, hnk, le_max_right _ _, hK.1, le_max_right _ _, hK.2.1, le_max_right _ _, hK.2.2.1,
    le_max_right _ _, hK.2.2.2, le_rfl, hLs, rfl, rfl, hHp, hm0, le_rfl, hm1⟩

/-- **One moment order**: a cascade schedule with its four orders `L_c, L_f, L_pr, L` replaced by
their maximum `L*`, and `N_aux, K_res, N_out` raised by `L*`, is again a cascade schedule meeting the
reconstruction floor (every condition on these orders is a lower bound, and the floors grow by at
most `L*`). -/
private theorem paper_one_order_schedule {α s q : ℝ} {K : ℕ} {Pacc lamE σE : ℝ} {r₀ D₀ : ℕ}
    {Q : ℝ} {H J N p nk Lc Lf Lpr Acl Naux Nout Kres L : ℕ} {σ₀ a σ : ℝ}
    (hsched : IsCascadeSchedule α s q K Pacc lamE σE D₀ Q H J N p nk Lc Lf Lpr Acl Naux Nout
      Kres L σ₀ a σ)
    (hrecon : succReconFloor r₀ D₀ H J N p Acl Lc ≤ Naux) :
    ∃ Ls Naux' Nout' Kres' : ℕ,
      IsCascadeSchedule α s q K Pacc lamE σE D₀ Q H J N p nk Ls Ls Ls Acl Naux' Nout' Kres' Ls
        σ₀ a σ ∧
      succReconFloor r₀ D₀ H J N p Acl Ls ≤ Naux' := by
  obtain ⟨hQ, hPQ, hss, hNK, hKN, hpo, hw⟩ := hsched
  obtain ⟨hPa, hPb, hPc⟩ := hpo
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20⟩ := hss
  obtain ⟨Ls, hcLs, hfLs, hpLs, hLLs, hLs⟩ : ∃ Ls : ℕ, Lc ≤ Ls ∧ Lf ≤ Ls ∧ Lpr ≤ Ls ∧ L ≤ Ls ∧
      Ls + 1 ≤ 2 * nk := by
    refine ⟨max (max Lpr (max Lc Lf)) L, ?_, ?_, ?_, le_max_right _ _, ?_⟩
    · exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)
    · exact ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · rcases le_total (max Lpr (max Lc Lf)) L with h | h
      · rw [max_eq_right h]; exact hPc
      · rw [max_eq_left h]; exact h14
  have hσ₀ : 0 < σ₀ := by rw [h6]; linarith
  have hcR : (Lc : ℝ) ≤ Ls := by exact_mod_cast hcLs
  have hfR : (Lf : ℝ) ≤ Ls := by exact_mod_cast hfLs
  have hpR : (Lpr : ℝ) ≤ Ls := by exact_mod_cast hpLs
  have hLR : (L : ℝ) ≤ Ls := by exact_mod_cast hLLs
  have hk : 0 ≤ q * min σE (ocDelta α q + σ₀) := by
    by_contra hneg
    have hneg' : q * min σE (ocDelta α q + σ₀) < 0 := lt_of_not_ge hneg
    have hLf0 : (0 : ℝ) ≤ Lf := Nat.cast_nonneg _
    nlinarith
  have hrec : succReconFloor r₀ D₀ H J N p Acl Ls ≤ succReconFloor r₀ D₀ H J N p Acl Lc + Ls := by
    unfold succReconFloor
    generalize succSchedD D₀ N p (H + 1) = D
    generalize succSchedR r₀ J H = R
    generalize (R + 3) * (N + D + 12) + 2 * p = X
    generalize 2 * D * R = Y
    have hm : max (D + Ls + N + 6 * p + 4) X ≤ max (D + Lc + N + 6 * p + 4) X + Ls :=
      max_le (by have := le_max_left (D + Lc + N + 6 * p + 4) X; omega)
        (by have := le_max_right (D + Lc + N + 6 * p + 4) X; omega)
    omega
  refine ⟨Ls, Naux + Ls, Nout + Ls, Kres + Ls, ⟨hQ, hPQ, ?_, by omega, by omega, ⟨by omega, ?_,
    by omega⟩, hw⟩, by omega⟩
  · refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, ?_, ?_, ?_, ?_, ?_, by omega, h17, h18, h19,
      h20⟩
    · have := mul_le_mul_of_nonneg_left hcR hσ₀.le
      linarith
    · have := mul_le_mul_of_nonneg_left hfR hk
      linarith
    · have := mul_le_mul_of_nonneg_left hpR hk
      linarith
    · simp only [max_self]; exact hLs
    · have h15' := h15
      refine max_le ?_ ?_
      · have := (le_max_left _ _).trans h15'
        omega
      · have := (le_max_right _ _).trans h15'
        omega
  · have := mul_le_mul_of_nonneg_left hLR hσ₀.le
    linarith

private def PaperReadyFromMenusStatement : Prop :=
    ∀ (K : ℕ) (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 → ∀ (q : ℝ), IsAdmissibleQ α s q → ∀ (ζ : ℝ → ℝ),
    IsFastProfile ζ → ∀ (Λ Jw : ℕ) (t₀ T₀ : ℝ), 0 < t₀ → t₀ < T₀ → 128 ≤ Λ → 2 ≤ Λ → 0 < ocC α q → ∀ (c₀max c₀C c₀P : ℝ), c₀max ≤ c₀C → c₀max ≤ c₀P → c₀max ≤ 1 → ∀ (φ₀
    : Vec 2 → ℝ) (hφ₀ : Integrable φ₀ volume), ContDiff ℝ (⊤ : ℕ∞) φ₀ →
    Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall → let bw : ℝ := 1 / 20000; let η₀ : ℝ := ocDelta α q / 16; ∀ (Nw Rw Lw
    : ℕ), let σw : ℝ := min (ocC α q) (q - 1) / 2; ∀ (QT : ℝ) (NT pT RT AT k₀ LcT LoT LfT LpT : ℕ) (tT τe lamE : ℝ), 0 < τe →
    τe = ocDelta α q / 4 → lamE = 4 * ocDelta α q →
    tT = ocDelta α q / (16 * ((termExcess NT pT (termAlphabet NT pT (1 + Jw * Nw) (Jw * Rw)) : ℝ)
      + 1)) →
    Lw = Jw * Nw →
    2 + 2 * q ^ Jw + 1 + 2 < Nw * (q - 1) →
    2 + 2 * q ^ Jw + 1 + q ^ Jw + 1 < 2 * weakAStar α q * (Rw + 1) →
    IsTerminalSchedule α q s 2 QT σw (weakChi α q η₀) η₀ tT Jw Lw k₀ NT pT RT AT LcT LoT LfT LpT
      (termAlphabet NT pT (1 + Jw * Nw) (Jw * Rw)) →
    QT = 2 * (2 + q ^ (Jw + 1) * (1 + s) + 3) → LoT = LpT → LfT = LpT →
    let Kstrong : ℕ := Jw * Nw + (NT + 2 * pT) + 4; ∀ (SXT SZT : ℕ), (∀ sXT sZT : ℕ, SXT ≤ sXT → SZT ≤ sZT →
    ∀ (cr : ℝ), 0 < cr → cr ≤ 1 →
    ∀ (Kw Kp : ℕ) (nW : ℕ+) (kW : InvConsts) (CL Cχ c C Cw cH : ℝ), 0 < c → 0 < cH →
    kW.G0 ≤ kW.Hprod + 1 →
    ∃ CT : ℝ, 0 ≤ CT ∧
    ∀ j₀ : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ M D.κ → D.term = M →
    ∀ (PW : ProvParams) (a : ℝ)
      (Gw : GenStage D ScalarH (termD0bar NT pT (1 + Jw * Nw) (Jw * Rw)) bw j₀) (lawW : BirthLaw)
      (aM : ℝ),
      IsWeakStage lawW PW φ₀ hφ₀ M (M + Jw) Jw (Jw * Rw) (1 + Jw * Nw) nW kW a T₀ σw CL Cχ
        (weakChi α q η₀) Gw aM →
    ∀ (tp : ℝ) (Pterm : (∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn Gw.comps, TorusHk Kp (ScalarH v.1.root))),
      IsTerminalPrepMap M Kw Kp c C Gw aM tp Pterm →
    ∀ (lawT : BirthLaw) (Gt' : GenStage D ScalarH (termD0bar NT pT (1 + Jw * Nw) (Jw * Rw)) bw j₀),
      IsTerminalLaw lawW lawT cH η₀ (wordsUpTo (termAlphabet NT pT (1 + Jw * Nw) (Jw * Rw)) RT).card →
      IsActualSuccessor D (termProvParams D Cw cr tT η₀ NT pT M)
        (termMenu (M + Jw) (termAlphabet NT pT (1 + Jw * Nw) (Jw * Rw)) RT NT pT sXT sZT η₀ tp cr)
        Gw Gt' →
    ∀ (Kz : ℕ) (Z : ∀ v : CompIn (Gt'.retained M 1 RT).comps, ℝ → TorusHk Kz (ScalarH v.1.root))
      (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn Gw.comps) (fun v => ScalarH v.1.root))
      (PZ : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kz - 2 * pT) (ScalarH v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn Gw.comps, ScalarH v.1.root)
      (û : ∀ v : CompIn Gw.comps, ℝ → TorusHk 0 (ScalarH v.1.root)),
      IsTerminalLiftedField Gw (Gt'.retained M 1 RT) M pT Kz NT (Jw * Rw) sXT sZT η₀ tp (a + T₀) cr
        Z CcT PZ aRep û →
    ∀ t ∈ Set.Icc tp (a + T₀),
    ∀ r : Representation (CompSpace (Gt'.retained M 1 RT).comps),
      IsRepresentationAt (D.eps (M - 1)) ((Jw * Nw) + (NT + 2 * pT) + 4) r →
      IsRepOf ((Gt'.retained M 1 RT).mass lawT)
        (fun v => truncateTorusHk (Nat.zero_le Kz) (Z v t)) r.value →
    ∃ rT : Representation (CompSpace Gw.comps),
      IsRepresentationAt (D.eps M) ((Jw * Nw) + 3) rT ∧
      rT.base = (r.map (readoutCLM M (D.eps (M - 1)) η₀ (Gw.mass lawW)
        ((Gt'.retained M 1 RT).mass lawT))).base ∧
      (∃ Lcov Llift : List ((Vec 2 → CompSpace Gw.comps) × ℝ),
        rT.profiles = (r.map (readoutCLM M (D.eps (M - 1)) η₀ (Gw.mass lawW)
          ((Gt'.retained M 1 RT).mass lawT))).profiles ++ Lcov ++ Llift ∧
        (∀ g ∈ Lcov, g.2 = D.eps (M - 1)) ∧ ∀ g ∈ Llift, g.2 = D.eps M) ∧
      rT.value = compField (Gw.mass lawW) (termLiftedRep Gw M NT (Jw * Rw) cr CcT aRep t) ∧
      representedSize s ((Jw * Nw) + 3) (D.eps M) rT ≤
        ENNReal.ofReal CT * representedSize s ((Jw * Nw) + (NT + 2 * pT) + 4) (D.eps (M - 1)) r) → ∀ (SXW SZW : ℕ), (∀ sX sZ : ℕ, SXW ≤ sX → SZW ≤ sZ →
    ∃ Cw : ℝ, 0 ≤ Cw ∧
    ∃ (CHw Υw : ℝ), 1 ≤ CHw ∧ 0 < Υw ∧
    ∀ j₀ : ℕ, IsCarrierStart α q Λ bw CHw Υw j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ M D.κ → D.term = M →
    ∀ (PW : ProvParams) (Dm : ℕ) (stage : ℕ → GenStage D ScalarH Dm bw j₀)
      (Gw : GenStage D ScalarH Dm bw j₀) (lawW : BirthLaw) (ιw : CompIn (stage M).comps ≃ CompIn Gw.comps)
      (CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root))
      (W : (i : ℕ) → ℝ → (CompIn (stage i).comps → Vec 2 → ℝ) → Vec 2 → ℝ),
      IsWeakConstruction D PW (⟨Nw, Rw, sX, sZ, η₀, M + Jw⟩ : WeakMenu) M Jw (D.termRW σw M) 0
        stage →
      IsWeakEncoding Nw Jw η₀ lawW.rootMass lawW.rootReadout (stage M) Gw ιw →
      (∀ i, M < i → i ≤ M + Jw → IsWeakReadoutLifts i Nw (Jw * Rw) sX sZ (stage i) (CcR i)) →
      IsWeakReadoutChain M Jw Nw 0 η₀ (fun _ => Jw * Rw) stage CcR W →
    ∀ (t : ℝ) (g : Vec 2 → ∀ v : CompIn Gw.comps, ScalarH v.1.root)
      (rT : Representation (CompSpace Gw.comps)),
      IsRepresentationAt (D.eps M) ((Jw * Nw) + 3) rT → rT.value = compField (Gw.mass lawW) g →
    ∃ rW : Representation (CompSpace (stage (M + Jw)).comps),
      IsRepresentationAt (D.eps (M + Jw)) 3 rW ∧
      (∀ y, compReadoutCLM (fun v => weakMass D Nw Jw η₀ v.1) (fun _ => 1) (rW.value y) =
        W M t (fun v y' => g y' (ιw v)) y) ∧
      representedSize s 3 (D.eps (M + Jw)) rW ≤
        ENNReal.ofReal Cw * representedSize s ((Jw * Nw) + 3) (D.eps M) rT) → ∀ (Q : ℝ) (H J N p nk Lc Lf Lpr Acl Naux Nout Kres L : ℕ) (σ₀ aexp σ : ℝ), IsCascadeSchedule α s
    q Kstrong 2 lamE (ocDelta α q) (termD0bar NT pT (1 + Jw * Nw) (Jw * Rw)) Q H J N p nk Lc Lf Lpr Acl Naux Nout
    Kres L σ₀ aexp σ → Lpr = L → Lc = L → Lf = L →
    paperTermFloorOf NT pT AT RT Jw Nw Rw LpT LcT L ≤ k₀ →
    succReconFloor (termR0bar RT (Jw * Rw)) (termD0bar NT pT (1 + Jw * Nw) (Jw * Rw)) H J N p Acl Lc ≤ Naux →
    ∀ (SXC SZC Kneed KneedP : ℕ), CascadeTail α s q ζ Λ c₀C φ₀ hφ₀ bw Kstrong 2 (t₀ / 2) T₀ (termR0bar RT
    (Jw * Rw)) (termD0bar NT pT (1 + Jw * Nw) (Jw * Rw)) τe lamE (ocDelta α q) Q H J N p nk Lc Lf Lpr Naux Nout Kres
    0 SXC SZC Kneed σ₀ →
    PaperPassageTail α s q ζ Λ c₀P φ₀ hφ₀ bw Kstrong 2 T₀ (termR0bar RT (Jw * Rw))
      (termD0bar NT pT (1 + Jw * Nw) (Jw * Rw)) τe lamE (ocDelta α q) Q H J N p nk Lc Lf Lpr Naux Nout Kres
      0 SXC SZC KneedP σ₀ → ∀ (nT : ℕ+), IsFreshKernelOrder nT LcT Lpr Lc Lf →
    ∀ (SXE SZE : ℕ), (∀ sXT sZT : ℕ, SXE ≤ sXT → SZE ≤ sZT →
    ∃ (Kw Lt : ℕ) (nW : ℕ+) (hk₀w : k₀ ≤ Kw) (hLw : Lw + 5 ≤ Kw) (cr : ℝ) (kS : InvConsts),
      LpT ≤ Lt ∧ Lt + 1 ≤ 2 * (nW : ℕ) ∧ IsTerminalKernelOrders nW LoT LfT LpT Lpr Lc Lf ∧
      0 < cr ∧ kS.cr = cr ∧ 0 < kS.c₀ ∧ kS.c₀ ≤ c₀max ∧ kS.cr ≤ 1 ∧
      kS.σf = ocDelta α q ∧ kS.lamC = lamE ∧
      IsSeedAllocation kS (termR0bar RT (Jw * Rw)) (termD0bar NT pT (1 + Jw * Nw) (Jw * Rw)) H J N p (max K (max Kres (max Kneed KneedP))) Lpr Lc Lf ∧
      (kS.mEnv = 0 ∧ kS.Kan = kS.Ks ∧ kS.Lan = kS.Ks ∧ kS.Jm = kS.Ks) ∧
      Lt + (1 + Jw * Nw) + max (Lw + 5) k₀ ≤ Kw ∧
      cr = 1 ∧
    ∃ (cK CK CL Cχ Cread Cid : ℝ) (kW : InvConsts),
      0 < cK ∧ kW.c₀ = cK ∧ IsWeakAllocation kW kS Lt ∧
    ∃ (c C Centry cH Ce Cw : ℝ), 0 < c ∧ 0 < cH ∧ 1 ≤ Ce ∧
    ∃ (CHe Υe : ℝ), 1 ≤ CHe ∧ 0 < Υe ∧
    ∀ j₀ : ℕ, IsCarrierStart α q Λ bw CHe Υe j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ M D.κ → D.term = M →
    ∀ (PW : ProvParams) (a : ℝ),
    ∃ (stage : ℕ → GenStage D ScalarH (termD0bar NT pT (1 + Jw * Nw) (Jw * Rw)) bw j₀) (Gw : GenStage D ScalarH (termD0bar NT pT (1 + Jw * Nw) (Jw * Rw)) bw j₀) (lawW : BirthLaw)
      (ιw : CompIn (stage M).comps ≃ CompIn Gw.comps) (aM : ℝ)
      (CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root))
      (W : (i : ℕ) → ℝ → (CompIn (stage i).comps → Vec 2 → ℝ) → Vec 2 → ℝ),
      IsWeakConstruction D PW (⟨Nw, Rw, sXT, sZT, η₀, M + Jw⟩ : WeakMenu) M Jw (D.termRW σw M) 0 stage ∧
      IsWeakEncoding Nw Jw η₀ lawW.rootMass lawW.rootReadout (stage M) Gw ιw ∧
      (∀ i, M < i → i ≤ M + Jw → IsWeakReadoutLifts i Nw (Jw * Rw) sXT sZT (stage i) (CcR i)) ∧
      IsWeakReadoutChain M Jw Nw 0 η₀ (fun _ => (Jw * Rw)) stage CcR W ∧
      IsWeakStage lawW PW φ₀ hφ₀ M (M + Jw) Jw (Jw * Rw) (1 + Jw * Nw) nW kW a T₀ σw CL Cχ (weakChi α q η₀) Gw aM ∧
    ∃ (tp : ℝ) (Pterm : (∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn Gw.comps, TorusHk (max Kstrong (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) (ScalarH v.1.root)))
      (lawT : BirthLaw) (Gt' : GenStage D ScalarH (termD0bar NT pT (1 + Jw * Nw) (Jw * Rw)) bw j₀)
      (seed : GenStage D ScalarH (succSchedD (termD0bar NT pT (1 + Jw * Nw) (Jw * Rw)) N p (H + 1)) bw j₀)
      (rootM rootR : ℕ → ℝ) (seedKc : ℕ → KernelSpec)
      (ι : CompIn (Gt'.retained M 1 RT).comps ≃ CompIn seed.comps),
      IsTerminalPrepMap M Kw (max Kstrong (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) c C Gw aM tp Pterm ∧
      IsTerminalLaw lawW lawT cH η₀ (wordsUpTo (termAlphabet NT pT (1 + Jw * Nw) (Jw * Rw)) RT).card ∧
      IsActualSuccessor D (termProvParams D Cw cr tT η₀ NT pT M) (termMenu (M + Jw) (termAlphabet NT pT (1 + Jw * Nw) (Jw * Rw)) RT NT pT sXT sZT η₀ tp cr) Gw Gt' ∧
      IsSeedEncoding (termProvParams D Cw cr tT η₀ NT pT M) lawT rootM rootR
        (fun _ => isoPairedKernel (D.termRW σw M) nW) (fun _ => isoPairedKernel (D.termRNew cr tT M) nT)
        seedKc (Gt'.retained M 1 RT) seed ι ∧
      TerminalSeedClauses rootM rootR seedKc φ₀ hφ₀ (M + Jw) (M - 1) kS Ce τe (termR0bar RT (Jw * Rw)) (termD0bar NT pT (1 + Jw * Nw) (Jw * Rw)) seed
        (tp + D.termH M) (a + T₀) ∧
      tp + D.termH M + 3 * ocTau α q Λ (M - 1) + 4 * ocTauPP α q Λ (M - 1) ≤ a + T₀ ∧
      ∀ (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ),
        IsWeakSolutionOn (streamVel (D.Φ (M + Jw))) (D.κ M) a (a + T₀) f θ →
      ∃ (tq : ℕ → ℝ)
        (Ur : (i : ℕ) → ∀ v : CompIn (stage i).comps, ℝ → TorusHk Kw (ScalarH v.1.root))
        (Urw : (i : ℕ) → ∀ v : CompIn (stage i).comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
        (Urk : (i : ℕ) → ∀ v u (_ : (stage i).fam.Γ v u), ℝ →
          TorusHk (Kw + (termD0bar NT pT (1 + Jw * Nw) (Jw * Rw)) - 1) (ScalarH u.1.root))
        (U₀ : ∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root))
        (U V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root))
        (Uw Vw : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
        (Uk Vk : ∀ v u (_ : Gw.fam.Γ v u), ℝ → TorusHk (Kw + (termD0bar NT pT (1 + Jw * Nw) (Jw * Rw)) - 1) (ScalarH u.1.root)),
        IsWeakReduction PW φ₀ hφ₀ nW M Jw Kw 0 a (a + T₀) θ stage tq Ur Urw Urk ∧
        tq (M + 1) = aM ∧ (U₀ = fun v => rerootFamily ιw (Ur M) v aM) ∧ U = rerootFamily ιw (Ur M) ∧
        IsWeakPaired PW φ₀ hφ₀ lawW M Kw Lt nW a T₀ σw (weakChi α q η₀) cK CK f Gw aM U₀ U V Uw Vw Uk Vk ∧
        IsWeakReadout lawW M Jw Lw Kw (D.κ M) a (t₀ / 4) T₀ s 2 cK Cread Cid f θ Gw
          (fun t g x => W M t (fun v x' => g (ιw v) x') x) V ∧
        IsTerminalPrepBounds lawW M Kw (max Kstrong (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) k₀ hk₀w (le_trans (by omega : k₀ ≤ 2 * k₀ + 2) (le_trans (le_max_left _ _) (le_max_right Kstrong _))) cr cK C QT f Gw aM tp Pterm V ∧
        ∃ Z : ∀ v : CompIn (Gt'.retained M 1 RT).comps, ℝ → TorusHk (max Kstrong (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) (ScalarH v.1.root),
          TerminalFamilyClauses (termProvParams D Cw cr tT η₀ NT pT M)
            (fun _ => isoPairedKernel (D.termRW σw M) nW)
            (fun _ => isoPairedKernel (D.termRNew cr tT M) nT) φ₀ hφ₀ lawW lawT rootM M (max Kstrong (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) cr C
            Centry tp (tp + D.termH M) (a + T₀) f Gw (Gt'.retained M 1 RT) seed ι
            (Pterm fun v => V v aM) Z ∧
          EntryIdentityClauses Gw (Gt'.retained M 1 RT) M pT (max Kstrong (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) Kw Lw NT (Jw * Rw) sXT sZT η₀ tp a (t₀ / 4) T₀ s
            2 2 C cr f θ (fun t g x => W M t (fun v x' => g (ιw v) x') x) V Z) → let sXT : ℕ := max SXE (max SXT SXW); let sZT : ℕ := max SZE (max SZT SZW); (∀ (D : OCData), D.α = α →
    D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ → ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → ∀ (b' : ℕ), 1
    ≤ b' → b' < M → ∃ (H₁ : ℝ → Vec 2 →L[ℝ] Vec 2) (H₂ : ℝ → Vec 2 →L[ℝ] Vec 2), IsFreshAxes D b' H₁ H₂) →
    ∃ P : PaperParameters α s q ζ Λ Jw t₀ T₀, K ≤ P.ready.cfg.kI.Ks ∧
      P.ready.cfg.kI.Kan = P.ready.cfg.kI.Ks ∧ P.ready.cfg.kI.Lan = P.ready.cfg.kI.Ks ∧
      P.ready.cfg.kI.Jm = P.ready.cfg.kI.Ks ∧
      paperScheduleOf P.ready.cfg =
        ⟨Q, σ₀, Jw, Nw, Rw, NT, pT, RT, H, J, N, p, nk, Lc, Lf, Lpr, Naux, Nout, Kres, L⟩

private theorem paper_ready_from_menus : PaperReadyFromMenusStatement := by
  classical
  intro K α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ Jw t₀ T₀ ht₀ htT hΛ128 hΛ2 hcpos c₀max c₀C c₀P hc₀C hc₀P
    hc₀1 φ₀ hφ₀ hφsmooth hφsupp bw η₀ Nw Rw Lw σw QT NT pT RT AT k₀ LcT LoT LfT LpT tT τe lamE hτe
    hτe4 hlamE4 htTv hLwJ hoN hoR hschedT hQTv hLoT hLfT Kstrong SXT SZT
    hTorders SXW SZW hWorders Q H J N p nk Lc Lf Lpr Acl Naux Nout Kres L σ₀ aexp σ hschedC
    hLprL hLcL hLfL hk₀F hrecon
    SXC SZC Kneed KneedP hCasTail hPassTail nT hnT SXE SZE hEfloor sXT sZT hAxes
  obtain ⟨Kw, Lt, nW, hk₀w, hLw, cr, kS, hplan⟩ :=
    hEfloor sXT sZT (le_max_left _ _) (le_max_left _ _)
  obtain ⟨hLpT, hLt, hkernels, hcr, hkcr, hkc₀, hkc₀max, hcr1, hσf, hlamE, halloc, hplanS, hKwF, hcrone,
    hweakConstants⟩ := hplan
  obtain ⟨cK, CK, CL, Cχ, Cread, Cid, kW, hcK, hkWc₀, hWalloc, hterminalConstants⟩ := hweakConstants
  obtain ⟨c, C, Centry, cH, Ce, Cw, hc, hcH, hCe, CHe, Υe, hCHe, hΥe, hEntryTail⟩ := hterminalConstants
  have hallocK := finite_seedAllocation_mono ((le_max_left _ _).trans (le_max_right _ _)) halloc
  have hKC : Kneed ≤ max K (max Kres (max Kneed KneedP)) :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hKP : KneedP ≤ max K (max Kres (max Kneed KneedP)) :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hKK : max K Kres ≤ max K (max Kres (max Kneed KneedP)) :=
    max_le_max le_rfl (le_max_left _ _)
  obtain ⟨thr, CH, Υ, hCH, hΥ, hCasInv⟩ := hCasTail Ce kS hCe hkc₀ (hkc₀max.trans hc₀C)
    (by rw [hkcr]; exact hcr) hcr1 hσf hlamE hallocK
    (hKC.trans halloc.2.1) (hKC.trans halloc.2.2.1) (hKC.trans halloc.2.2.2.1)
    (hKC.trans halloc.2.2.2.2.1)
  obtain ⟨thrP, CHP, ΥP, hCHP, hΥP, hPassInv⟩ := hPassTail Ce kS hCe hkc₀ (hkc₀max.trans hc₀P)
    (by rw [hkcr]; exact hcr) hcr1 hσf hlamE hallocK
    (hKP.trans halloc.2.1) (hKP.trans halloc.2.2.1) (hKP.trans halloc.2.2.2.1)
    (hKP.trans halloc.2.2.2.2.1)
  have hsuccsched := hschedC.2.2.1
  obtain ⟨_, _, _, _, _, hσ₀, hapos, haσ, hσlam, _, _, _, _, hnk, _⟩ := hsuccsched
  have hσ₀pos : 0 < σ₀ := by linarith
  obtain ⟨kI, hkI, hKIs, hKIan, hKIlan, hKIjm, hkIlam, hkIker⟩ := paper_exists_invariantAdmissible_at kS
    (certificateThresholdJoin thr thrP)
    (termR0bar RT (Jw * Rw)) (termD0bar NT pT (1 + Jw * Nw) (Jw * Rw))
    H J N p nk Kres Lpr Lc Lf K σ₀ (ocDelta α q) q (ocC α q) hσ₀pos
    (by rw [hlamE]; exact hσlam) hq.1 hcpos hallocK
    ⟨hKK.trans halloc.2.1, hKK.trans halloc.2.2.1, hKK.trans halloc.2.2.2.1,
      hKK.trans halloc.2.2.2.2.1⟩ hnk
  have hlamI : kI.lamC = 4 * ocDelta α q := by
    rw [hkIlam, hlamE, hlamE4]
    apply min_eq_left
    obtain ⟨h4δ, -⟩ := paper_delta_gamma_lt hα₀ hα₁ hs₀ hs₁ hq
    have hq1 := hq.1
    have h1 : 0 < (q - 1) * ocC α q := mul_pos (by linarith) hcpos
    have h2 : 0 < q * σ₀ := mul_pos (by linarith) hσ₀pos
    have h3 : (q - 1) * (1 + ocC α q) = (q - 1) + (q - 1) * ocC α q := by ring
    linarith only [h1, h2, h3, h4δ]
  have hkerL : kI.Lker = L := by
    rw [hkIker, hLprL, hLcL, hLfL]
    simp only [max_self]
  obtain ⟨CIthr, Cwthr, hCasLedger⟩ := hCasInv kI (invariant_admissible_threshold_left hkI)
  obtain ⟨CIthrP, CwthrP, hPassLedger⟩ := hPassInv kI (invariant_admissible_threshold_right hkI)
  obtain ⟨CI, CwCas, hledger⟩ := exists_ledgerAdmissible Ce (max CIthr CIthrP) (max Cwthr CwthrP)
  have hledgerC : IsLedgerAdmissible Ce CI CwCas CIthr Cwthr :=
    ⟨hledger.1, (le_max_left _ _).trans hledger.2.1, (le_max_left _ _).trans hledger.2.2.1,
      hledger.2.2.2⟩
  have hledgerP : IsLedgerAdmissible Ce CI CwCas CIthrP CwthrP :=
    ⟨hledger.1, (le_max_right _ _).trans hledger.2.1, (le_max_right _ _).trans hledger.2.2.1,
      hledger.2.2.2⟩
  obtain ⟨CwLift, hCwLift, CHw, Υw, hCHw, hΥw, hWeakTail⟩ := hWorders sXT sZT
    ((le_max_right SXT SXW).trans (le_max_right SXE _))
    ((le_max_right SZT SZW).trans (le_max_right SZE _))
  obtain ⟨j₀, hj₀''⟩ := Providers.carrier_start_exists α s hα₀ hα₁ hs₀ hs₁ q hq Λ hΛ128 bw
    (max 1 (max CH (max CHP (max CHe CHw)))) (max 100 (max 1 (max Υ (max ΥP (max Υe Υw)))))
    (by norm_num [bw])
  have hApos (k : ℕ) : 0 ≤ ocA α q Λ k := by
    unfold ocA
    exact Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ Λ)).le _
  have hTpos (k : ℕ) : 0 ≤ ocTauPP α q Λ k :=
    (Construction.Stream.ocTauPP_pos (by omega : 1 ≤ Λ)).le
  have hj₀' : IsCarrierStart α q Λ bw (max 1 (max CH (max CHP (max CHe CHw))))
      (max 1 (max Υ (max ΥP (max Υe Υw)))) j₀ :=
    IsCarrierStart.mono hApos hTpos le_rfl (le_max_right _ _)
      (zero_le_one.trans (le_max_left _ _)) (zero_le_one.trans (le_max_left _ _)) hj₀''
  have hjCyc : IsCarrierStart α q Λ bw 1 100 j₀ :=
    IsCarrierStart.mono hApos hTpos (le_max_left _ _) (le_max_left _ _) zero_le_one
      (by norm_num) hj₀''
  have hj₀ : IsCarrierStart α q Λ bw (max CH (max CHP (max CHe CHw)))
      (max Υ (max ΥP (max Υe Υw))) j₀ :=
    IsCarrierStart.mono hApos hTpos (le_max_right _ _) (le_max_right _ _)
      ((zero_le_one.trans hCH).trans (le_max_left _ _)) (hΥ.le.trans (le_max_left _ _)) hj₀'
  have hjOne : IsCarrierStart α q Λ bw 1 1 j₀ :=
    IsCarrierStart.mono hApos hTpos (le_max_left _ _) (le_max_left _ _) zero_le_one zero_le_one
      hj₀'
  have hjCas : IsCarrierStart α q Λ bw CH Υ j₀ :=
    IsCarrierStart.mono hApos hTpos (le_max_left _ _) (le_max_left _ _)
      (zero_le_one.trans hCH) hΥ.le hj₀
  have hjPass : IsCarrierStart α q Λ bw CHP ΥP j₀ :=
    IsCarrierStart.mono hApos hTpos
      ((le_max_left _ _).trans (le_max_right _ _))
      ((le_max_left _ _).trans (le_max_right _ _))
      (zero_le_one.trans hCHP) hΥP.le hj₀
  have hjEntry : IsCarrierStart α q Λ bw CHe Υe j₀ :=
    IsCarrierStart.mono hApos hTpos
      (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _))
      (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _))
      (zero_le_one.trans hCHe) hΥe.le hj₀
  have hjWeak : IsCarrierStart α q Λ bw CHw Υw j₀ :=
    IsCarrierStart.mono hApos hTpos
      (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _))
      (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _))
      (zero_le_one.trans hCHw) hΥw.le hj₀
  obtain ⟨Ccas, CQ, Cp, m₀, hCcas, hCascadeLevel⟩ := hCasLedger CI CwCas j₀ hledgerC hjCas
  obtain ⟨Cpass, CQpass, mStar, hPassageLevel⟩ := hPassLedger CI CwCas j₀ hledgerP hjPass
  have hkw : kW.G0 ≤ kW.Hprod + 1 := by
    have hgap := hWalloc.2.2.2.2.2.1
    have hprod := hWalloc.2.2.2.2.2.2.1
    have hseedprod := halloc.2.2.2.2.2.2.2.2.1
    omega
  obtain ⟨CT, hCT, hTermTail⟩ := hTorders sXT sZT
    ((le_max_left SXT SXW).trans (le_max_right SXE _))
    ((le_max_left SZT SZW).trans (le_max_right SZE _)) cr hcr (by rw [← hkcr]; exact hcr1) Kw
    (max Kstrong (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) nW kW CL Cχ c C Cw cH hc hcH hkw
  obtain ⟨ME, hME⟩ := hEntryTail j₀ hjEntry
  obtain ⟨MT, hMT⟩ := hTermTail j₀
  obtain ⟨MW, hMW⟩ := hWeakTail j₀ hjWeak
  obtain ⟨Mwait, hMwait⟩ := exists_entry_wait hα₀ hα₁ hq hΛ2 C Jw (t₀ / 4) (by positivity)
  have hδ := ocDelta_pos_of_admissible hα₀ hq
  obtain ⟨mF, hmF⟩ := IterationPassage.Cascade.scale_floor (q := q) (Λ := Λ)
    (p := q * min (ocDelta α q / 4) τe) (W := CI) (η := 1 / 8) hq.1 hΛ128
    (mul_pos (by linarith [hq.1]) (lt_min (by linarith) hτe)) (by norm_num)
  let cfg : FiniteParameters := {
    α := α, s := s, q := q, ζ := ζ, Λ := Λ, φ₀ := φ₀, hφ₀ := hφ₀, bw := bw
    Jw := Jw, Nw := Nw, Rw := Rw, Lw := Lw, τ := t₀ / 4, T₀ := T₀, Pw := 2, η₀ := η₀
    σw := σw, PT := 2, QT := QT, NT := NT, pT := pT, RT := RT, AT := AT, k₀ := k₀
    LcT := LcT, LoT := LoT, LfT := LfT, LpT := LpT, tT := tT, τe := τe, lamE := lamE
    σ₀ := σ₀, H := H, J := J, N := N, p := p, Kres := Kres, Lpr := Lpr, Lc := Lc, Lf := Lf
    nT := nT, Kout := Kstrong, sXT := sXT, sZT := sZT, Kw := Kw, Lt := Lt, nW := nW
    hk₀w := hk₀w, hLw := hLw, cr := cr, kS := kS, cK := cK, CK := CK, CL := CL, Cχ := Cχ
    Cread := Cread, Cid := Cid, kW := kW, c := c, C := C, Centry := Centry, cH := cH, Ce := Ce
    Cw := Cw, j₀ := j₀, Q := Q, t₀ := t₀, nk := nk, L := L, Naux := Naux, Nout := Nout
    sX := SXC, sZ := SZC, m₀ := m₀, CI := CI, CwCas := CwCas, Ccas := Ccas, CQ := CQ, Cp := Cp,
    kI := kI }
  have hvalid : FiniteLocalValidity cfg := {
    hα₀ := hα₀, hα₁ := hα₁, hs₁ := hs₁, hq := hq, hζ := hζ
    hcr := by change 0 < kI.cr; rw [hkI.2.1, hkcr]; exact hcr
    hσ₀ := hσ₀pos, hnk := by change 1 ≤ nk; omega
    horder := rfl, hτ := rfl
    hbw := by norm_num [cfg, bw]
    hc₀ := hkc₀, hτe := hτe
    hHprod := halloc.2.2.2.2.2.2.2.2.1 }
  obtain ⟨Mseed, hMseed⟩ := exists_finite_seed_budget_level cfg hvalid hΛ128
  have hE' : ∀ M, ME ≤ M → EntryLevelStatement cfg M := by
    dsimp only [EntryLevelStatement, cfg]
    with_reducible exact hME
  have hT' : ∀ M, MT ≤ M → TerminalLiftLevelStatement cfg CT M := by
    dsimp only [TerminalLiftLevelStatement, cfg]
    with_reducible exact hMT
  have hW' : ∀ M, MW ≤ M → WeakLiftLevelStatement cfg CwLift M := by
    dsimp only [WeakLiftLevelStatement, cfg]
    with_reducible exact hMW
  have hCas' : CascadeLevelStatement cfg := by
    dsimp only [CascadeLevelStatement, cfg]
    with_reducible exact hCascadeLevel
  have hPass' : PassageLevelStatement cfg Cpass CQpass mStar := by
    dsimp only [PassageLevelStatement, cfg]
    with_reducible exact hPassageLevel
  exact ⟨paperParametersOfLevels cfg hvalid CT CwLift hCT hCwLift hc hCcas rfl rfl
    (by change t₀ / 4 ≤ t₀; linarith) ME MT MW Mwait Mseed hMseed hMwait hE' hT' hW' hCas' hAxes
    Acl aexp σ hschedC hrecon (certificateThresholdJoin thr thrP) hkI (hkc₀max.trans hc₀1)
    Cpass CQpass mStar hPass' (max mF j₀) (le_max_right _ _)
    (fun j hj => hmF j ((le_max_left _ _).trans hj)) hjOne hjCyc
    (by norm_num [cfg, bw]) hplanS ⟨hφsmooth, hφsupp⟩ rfl
    (paper_sigmaw_value hα₀ hα₁ hs₀ hs₁ hq) hσf hτe4 hlamE4 htTv hschedT hQTv ⟨hLoT, hLfT⟩ hLpT hLwJ
    (by
      change Lt + Jw * Nw + 1 + max (Lw + 5) k₀ ≤ Kw
      generalize max (Lw + 5) k₀ = m at hKwF ⊢
      omega) (hlamE.trans hlamE4) hlamI ⟨hLprL, hLcL, hLfL, hkerL⟩ (hkI.2.1.trans hkcr).symm
    ⟨hLt, hkernels, hnT⟩ hcrone ((hkI.2.1.trans hkcr).trans hcrone) ⟨hoN, hoR⟩ hk₀F,
    hKIs, hKIan, hKIlan, hKIjm, rfl⟩

/-- **The parameters at a prescribed invariant order**: for `Λ ≥ Λ₀`, `J ≥ 1`, `0 < t₀ < T` (the
threshold `Λ₀` of `paper_parameters_exist`, chosen before the order) and every order requirement
`K_req` computed from the schedule, there are parameters whose invariant constants have the single
order `k_I.K_s = k_I.K_an = k_I.L_an = k_I.J_m ≥ K_req(schedule)` (and `≥ K_res`, `≤ k_S.K_s`, by
`IsInvariantAdmissible`). -/
theorem paper_parameters_exist_order (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ Jw : ℕ, 1 ≤ Jw → ∀ t₀ T₀ : ℝ, 0 < t₀ → t₀ < T₀ →
      ∀ Kreq : PaperSchedule → ℕ, ∃ P : PaperParameters α s q ζ Λ Jw t₀ T₀,
        Kreq (paperScheduleOf P.ready.cfg) ≤ P.ready.cfg.kI.Ks ∧
        P.ready.cfg.kI.Kan = P.ready.cfg.kI.Ks ∧ P.ready.cfg.kI.Lan = P.ready.cfg.kI.Ks ∧
        P.ready.cfg.kI.Jm = P.ready.cfg.kI.Ks := by
  classical
  obtain ⟨ΛE, hΛE, hE⟩ := Providers.entry_terminal α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨ΛC, hΛC, hCas⟩ := Providers.iteration_cascade_of_schedule α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨ΛP, hΛP, hPass⟩ := Providers.iteration_passage α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨ΛT, hΛT, hT⟩ := Finite.TerminalLift.terminal_lift_rep_proved α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨ΛW, hΛW, hW⟩ := Providers.weak_lift_rep α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨ΛA, hΛA, hA⟩ := Providers.fresh_axes_exist α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨max ΛE (max ΛC (max ΛP (max ΛT (max ΛW ΛA)))), by omega, ?_⟩
  intro Λ hΛ Jw hJw t₀ T₀ ht₀ htT Kreq
  have hΛ128 : 128 ≤ Λ := by omega
  have hΛ2 : 2 ≤ Λ := by omega
  have hδ := ocDelta_pos_of_admissible hα₀ hq
  have hcpos := ocC_pos_of_admissible hα₀ hq
  have hs1 : s < 1 := by linarith
  obtain ⟨c₀C, hc₀C, hCas0⟩ := hCas Λ (by omega)
  obtain ⟨c₀P, hc₀P, hPass0⟩ := hPass Λ (by omega)
  let c₀max : ℝ := min (min c₀C c₀P) 1
  have hc₀max : 0 < c₀max := lt_min (lt_min hc₀C hc₀P) one_pos
  obtain ⟨φ₀, hφ₀, hφsmooth, hφpos, hφmass, hφsupp⟩ := exists_mollifier
  let bw : ℝ := 1 / 20000
  have hbw : 0 < bw := by norm_num [bw]
  have hbw1 : bw ≤ 1 / 10000 := by norm_num [bw]
  let η₀ : ℝ := ocDelta α q / 16
  have hη₀ : 0 < η₀ := by dsimp [η₀]; positivity
  have hηδ : η₀ ≤ ocDelta α q / 8 := by dsimp [η₀]; linarith
  obtain ⟨Nw, Rw, Lw, hNw, hLwNw, hoN, hoR, hEorders⟩ :=
    hE Λ (by omega) c₀max hc₀max φ₀ hφ₀ hφsmooth hφpos hφmass hφsupp bw hbw hbw1
      Jw (t₀ / 4) T₀ 2 η₀ hJw (by positivity) (by linarith) (by norm_num) hη₀ hηδ
  let σw : ℝ := min (ocC α q) (q - 1) / 2
  have hσw : 0 < σw := by dsimp [σw]; exact div_pos (lt_min hcpos (by linarith [hq.1])) (by norm_num)
  have hσw1 : σw < min (ocC α q) (q - 1) := by dsimp [σw] at *; linarith
  obtain ⟨QT, NT, pT, RT, AT, LcT, LoT, LfT, LpT, hschedTk, hexp, hQTv, hLoT, hLfT⟩ :=
    paper_finite_order_choice α s hα₀ hα₁ hs₀ hs₁ q hq Jw Nw Rw Lw η₀ 2 hJw hη₀ hηδ (by norm_num)
      σw hσw hσw1
  generalize htTv : ocDelta α q / (16 * ((termExcess NT pT (termAlphabet NT pT (1 + Jw * Nw)
    (Jw * Rw)) : ℝ) + 1)) = tT at hschedTk hexp
  generalize hτe4 : ocDelta α q / 4 = τe at hexp
  generalize hlamE4 : 4 * ocDelta α q = lamE at hexp
  let Kstrong := Jw * Nw + (NT + 2 * pT) + 4
  have hKstrong : 3 ≤ Kstrong := by dsimp [Kstrong]; omega
  have hlamE : 0 < lamE := by linarith [hexp.2.2.2.1]
  obtain ⟨SXW, SZW, hWorders⟩ := hW Λ (by omega) bw hbw hbw1 Jw Nw Rw η₀ σw
    hJw hNw hη₀ hηδ hσw hσw1 (Jw * Nw) le_rfl
  obtain ⟨Q, H, J, N, p, nk, Lc₀, Lf₀, Lpr₀, Acl, Naux₀, Nout₀, Kres₀, L₀, σ₀, aexp, σ, hsched₀,
    hrecon₀⟩ := Providers.cascade_schedule_exists α s hα₀ hα₁ hs₀ hs₁ q hq Kstrong 2
    (termR0bar RT (Jw * Rw)) (termD0bar NT pT (1 + Jw * Nw) (Jw * Rw)) lamE (ocDelta α q)
    hKstrong (by norm_num) hlamE hδ
  -- one moment order `L = L_c = L_f = L_pr`
  obtain ⟨L, Naux, Nout, Kres, hsched, hrecon⟩ := paper_one_order_schedule hsched₀ hrecon₀
  -- the reading order `k₀ = N_rd,e`, above the floor (14.7)
  have hk₀L : Lw + 5 ≤ max (Lw + Jw * Nw + 6) (paperTermFloorOf NT pT AT RT Jw Nw Rw LpT LcT L) :=
    le_trans (by omega) (le_max_left _ _)
  have hk₀F : paperTermFloorOf NT pT AT RT Jw Nw Rw LpT LcT L ≤
      max (Lw + Jw * Nw + 6) (paperTermFloorOf NT pT AT RT Jw Nw Rw LpT LcT L) := le_max_right _ _
  generalize max (Lw + Jw * Nw + 6) (paperTermFloorOf NT pT AT RT Jw Nw Rw LpT LcT L) = k₀
    at hk₀L hk₀F
  have hschedT := hschedTk k₀ hk₀L
  obtain ⟨SXT, SZT, hTorders⟩ := hT Λ (by omega) φ₀ hφ₀ hφsmooth hφpos hφmass hφsupp
    bw hbw hbw1 Jw Nw Rw Lw T₀ η₀ σw hJw (by linarith) hη₀ hηδ hσw hσw1
    2 QT NT pT RT AT k₀ LcT LoT LfT LpT tT hschedT (Jw * Nw)
  obtain ⟨SXC, SZC, Kneed, hCasFloors⟩ := hCas0 φ₀ hφ₀ hφsmooth hφpos hφmass hφsupp bw hbw hbw1
    Kstrong 2 (t₀ / 2) T₀ hKstrong (by norm_num) (by positivity) (by linarith)
    (termR0bar RT (Jw * Rw)) (termD0bar NT pT (1 + Jw * Nw) (Jw * Rw))
    τe lamE (ocDelta α q) hexp.1 hlamE hδ Q H J N p nk L L L Acl Naux Nout Kres L σ₀ aexp σ
    hsched hrecon 0
  obtain ⟨hQ, hPQ, hss, hNaux, hNout, horders, hwidths⟩ := hsched
  obtain ⟨SXP, SZP, KneedP, hPassFloors⟩ := hPass0 φ₀ hφ₀ hφsmooth hφpos hφmass hφsupp bw hbw
    hbw1 Kstrong 2 hKstrong (by norm_num) Q T₀ hQ (by linarith) hPQ
    (termR0bar RT (Jw * Rw)) (termD0bar NT pT (1 + Jw * Nw) (Jw * Rw))
    τe lamE (ocDelta α q) hexp.1 hlamE hδ H J N p nk L L L Acl Naux Nout Kres 0 σ₀ aexp σ
    hss hNaux hNout hrecon L horders hwidths
  have hCasTail := hCasFloors (max SXC SXP) (max SZC SZP) (le_max_left _ _) (le_max_left _ _)
  have hPassTail := hPassFloors (max SXC SXP) (max SZC SZP) (le_max_right _ _) (le_max_right _ _)
  obtain ⟨nT, hnT⟩ := exists_freshKernelOrder LcT L L L
  let K := Kreq ⟨Q, σ₀, Jw, Nw, Rw, NT, pT, RT, H, J, N, p, nk, L, L, L, Naux, Nout, Kres, L⟩
  obtain ⟨SXE, SZE, hEfloor⟩ := hEorders σw hσw hσw1 2 (by norm_num)
    NT pT RT AT k₀ LcT LoT LfT LpT tT QT hschedT τe lamE hexp σ₀ H J N p
    (max K (max Kres (max Kneed KneedP))) L L L nT hnT Kstrong
  have hAxes := hA Λ (by omega)
  obtain ⟨P, hKs, hKan, hLan, hJm, hP⟩ := paper_ready_from_menus K α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
    Λ Jw t₀ T₀ ht₀ htT hΛ128 hΛ2 hcpos
    c₀max c₀C c₀P ((min_le_left _ _).trans (min_le_left _ _))
    ((min_le_left _ _).trans (min_le_right _ _)) (min_le_right _ _) φ₀ hφ₀ hφsmooth hφsupp Nw
    Rw Lw QT NT pT RT AT k₀ LcT LoT LfT LpT tT τe lamE hexp.1 hτe4.symm hlamE4.symm htTv.symm
    hLwNw hoN hoR hschedT hQTv hLoT hLfT
    SXT SZT (by with_reducible exact hTorders) SXW SZW (by with_reducible exact hWorders)
    Q H J N p nk L L L Acl Naux Nout Kres L σ₀ aexp σ ⟨hQ, hPQ, hss, hNaux, hNout, horders, hwidths⟩
    rfl rfl rfl hk₀F hrecon
    (max SXC SXP) (max SZC SZP) Kneed KneedP hCasTail hPassTail nT hnT SXE SZE
    (by with_reducible exact hEfloor) hAxes
  refine ⟨P, ?_, hKan, hLan, hJm⟩
  rw [hP]
  exact hKs

/-- **The parameters exist**: for `Λ ≥ Λ₀`, `J ≥ 1` and `0 < t₀ < T` the finite-assembly
constants can be chosen so that, besides the finite assembly, `iteration_passage` holds at them. -/
theorem paper_parameters_exist (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ Jw : ℕ, 1 ≤ Jw → ∀ t₀ T₀ : ℝ, 0 < t₀ → t₀ < T₀ →
      Nonempty (PaperParameters α s q ζ Λ Jw t₀ T₀) := by
  obtain ⟨Λ₀, hΛ₀, h⟩ := paper_parameters_exist_order α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  exact ⟨Λ₀, hΛ₀, fun Λ hΛ Jw hJw t₀ T₀ ht₀ htT =>
    (h Λ hΛ Jw hJw t₀ T₀ ht₀ htT fun _ => 0).elim fun P _ => ⟨P⟩⟩

end AVRegularity.PaperFacing
