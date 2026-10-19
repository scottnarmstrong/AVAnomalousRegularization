-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain
public import AVRegularity.Definitions.Construction.Gen.Majorant
import AVRegularity.Proofs.CascadeInvariants.LedgerAll
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
import AVRegularity.Proofs.Results.Construction.ComparisonLiftPositiveLayer
import AVRegularity.Proofs.Results.Construction.ContextCertified.Assemble
import AVRegularity.Proofs.Torus.FirstSource
import AVRegularity.Construction.StageSuccessor.RealizedFields
public import AVRegularity.Statements.Intermediate.Families.IsTorusCompatible
import AVRegularity.Definitions.Finite.FiniteLiftBridge

section
/-! **The production ledger** (`successor_ledger`). Every identity of the extended next family
has witnesses with the record bound and generated expressions with certified leaves whose weighted
mode majorant is at most the witness (`CascadeInvariants.ledger_all`): the path sources by the
non-diagonal case of the ledger, the first source `𝖣` by the bridge cancellation
(`CascadeInvariants.diag_ledger_case`).

Choices beyond those of the non-diagonal case: `Λ₀` also above the thresholds of the scale
facts of the first source (`exists_diagScales`, `a_{m-1} τ''_m ≤ C_a ε_{m-1}^δ`) and of the drift
bound (`ComplexContext.drift_scale_bound`); the constants of the first source over the carrier
constants (`exists_diagConsts`) at the reserve step `Δ_D = 1/(fsR + 1)`;
`C_w^thr = max ledgerThr diagThr`; `m_* = j₀ + 2`. The chain environment is that of the carrier
calculus (`velC_spec`, `IsCarrierStart`), the coercivity `ownSize m ≤ 1/100` follows from `100 ≤ Υ`
(`ComplexContext.ownSize_le_of_carrierStart`), and the producer reserves of the new components
are nonnegative (`compReserve_nonneg_of_succ`: grades at most `H + 1`, `H_prod = G₀ + H + 1`). -/

@[expose] public section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity.Providers.GenSem
  AVRegularity.Providers.CascadeInvariants
open scoped ENNReal

namespace AVRegularity.Providers

/-- **The production ledger** (Definition 10.3 of the paper). -/
theorem successor_ledger (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
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
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sX →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sZ →
    ∃ thr : InvConsts, ∀ (CH Υ : ℝ), 1 ≤ CH → 100 ≤ Υ → ∀ κ : MajConsts, MajOK bw κ →
    ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ),
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
    ∀ (m : ℕ), LedgerOK Ce CI Cw CIthr Cwthr mStar m → m ≤ n → n < M →
    ∀ (G G' : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      (∃ tA : ℝ, tS ≤ tA ∧
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G) →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
      ∀ v' u' (γ' : G'.fam.Γ v' u'), ∃ θ : (d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ,
        (∀ d α c, 0 ≤ θ d α c) ∧
        (∀ d, 2 ≤ d → d ≤ (G'.fam.identity v' u' γ').maxOrder →
          (D.eps G'.level / (G'.fam.identity v' u' γ').record.length) ^ (d - 2) *
              ∑ α, ∑ c, θ d α c ≤ (G'.fam.identity v' u' γ').record.size) ∧
        ∀ (d : ℕ) (α : DerivativeWord2 (d - 1)) (c : Fin 2),
          ∃ (e : (p : OddSlot) → Gen .ctx G'.level p.1) (Δ : ℝ)
            (leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞)),
            G'.IsExprFor v' u' γ' d α c e ∧ 0 < Δ ∧ LeavesCertified D bw j₀ leaf ∧
            (∀ p, Gen.SolvedFree leaf (e p)) ∧
            ∑' h : ℤ, ENNReal.ofReal (Real.exp (3 * Real.pi * bw * |(h : ℝ)|) *
                (1 + |(h : ℝ)|) ^ kI.Lstar) *
              ⨆ p : OddSlot, ⨆ t ∈ ocPulseWindow D.α D.q D.Λ G'.level p.1,
                genMode D κ Δ leaf (e p) (compReserve kI v'.1) h t
              ≤ ENNReal.ofReal (θ d α c) :=
  by
  obtain ⟨Cu, hCu, Λ₁, hΛ₁, hscales⟩ := exists_passScales hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Ca, hCa, Λ₂, hΛ₂, hdscales⟩ := exists_diagScales hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Λ₃, hΛ₃, hdrift⟩ := ComplexContext.drift_scale_bound hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨max Λ₁ (max Λ₂ Λ₃), le_max_of_le_left hΛ₁, fun Λ hΛ => ⟨1, one_pos, ?_⟩⟩
  have hΛ1' : Λ₁ ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛ2' : Λ₂ ≤ Λ := ((le_max_left _ _).trans (le_max_right _ _)).trans hΛ
  have hΛ3' : Λ₃ ≤ Λ := ((le_max_right _ _).trans (le_max_right _ _)).trans hΛ
  obtain ⟨Cd, -, hCd⟩ := hdrift Λ hΛ3'
  intro _ _ _ _ _ _ bw hbw hbw1 _ _ _ _ _ _ kS r₀ D₀ _ _ _ _ hcrS0 hcrS1 _ _ H J N p _ _ _ _ _ _
    _ _ _ _ _ σ₀ _ _ hsch _ _ hseedA hsX hsZ
  refine ⟨kS, ?_⟩
  intro CH Υ hCH hΥ κ hκ kI hadm
  obtain ⟨-, hcr, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hL, -, hG0, -,
    hHprod, -⟩ := hadm
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hH1, hN, -, -⟩ := hsch
  have hcr0 : 0 < kI.cr := by rw [hcr]; exact hcrS0
  have hcr1 : kI.cr ≤ 1 := by rw [hcr]; exact hcrS1
  have hLst := liftWt_le_Lstar hseedA hG0 hL
  -- the reserve step of the path sources
  have hH0 : (0 : ℝ) < (kI.Hprod : ℝ) + 1 := by positivity
  have hX0 : (0 : ℝ) < ((succSchedD D₀ N p (H + 1) + (4 * (N + succSchedD D₀ N p H) + 10 * p) +
      1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
  obtain ⟨Δ, hΔdef⟩ : ∃ Δ : ℝ, Δ = 1 / (((kI.Hprod : ℝ) + 1) * ((succSchedD D₀ N p (H + 1) +
      (4 * (N + succSchedD D₀ N p H) + 10 * p) + 1 : ℕ) : ℝ)) := ⟨_, rfl⟩
  have hΔ : 0 < Δ := by rw [hΔdef]; positivity
  have hΔD : ((succSchedD D₀ N p (H + 1) : ℕ) : ℝ) * Δ ≤ 1 / ((kI.Hprod : ℝ) + 1) := by
    rw [hΔdef]
    exact step_mul_le hH0 hX0 (by exact_mod_cast (by omega))
  have hΔR : ((4 * (N + succSchedD D₀ N p H) + 10 * p : ℕ) : ℝ) * Δ ≤
      1 / ((kI.Hprod : ℝ) + 1) := by
    rw [hΔdef]
    exact step_mul_le hH0 hX0 (by exact_mod_cast (by omega))
  obtain ⟨ar, K, W, Cold, Wr, S, Kg, Kd, hC⟩ :=
    exists_ledgerConsts hbw hκ (succSchedD D₀ N p (H + 1)) kI.Lstar hΔ
  -- the constants of the first source
  have hΔD0 : (0 : ℝ) < 1 / ((fsR N p (2 * N + 1) : ℝ) + 1) := by positivity
  obtain ⟨aD, a₀D, L₀, sD, Wg, Wc, Wl, KgD, KdD, SD, WrD, ColdD, CslowD, hCD⟩ :=
    exists_diagConsts hbw hκ kI.Lstar N p hΔD0
  have hΔfs : ((fsR N p (2 * N + 1) : ℕ) : ℝ) * (1 / ((fsR N p (2 * N + 1) : ℝ) + 1)) ≤ 1 := by
    rw [mul_one_div, div_le_one (by positivity)]
    linarith
  have hCown : 0 ≤ ComplexFlow.chainK * (6 / 5) * Ca :=
    mul_nonneg (by unfold ComplexFlow.chainK; norm_num) hCa
  refine ⟨0, max (ledgerThr (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H)
    (N + succSchedD D₀ N p H) p K W Cold Wr Δ kI.cr Cu
    (fluxMax κ S Kg Kd (succSchedD D₀ N p (H + 1)) (succSchedR r₀ J H) (N + succSchedD D₀ N p H))
    (covKMax S Kg (N + succSchedD D₀ N p H) p))
    (diagThr (constCtx κ SD KgD KdD) (succSchedD D₀ N p (H + 1)) N p sD Wg Wl Wc Cu Ca Cd
      (ComplexFlow.chainK * (6 / 5) * Ca) WrD kI.cr), ?_⟩
  intro _ Cw j₀ hcs
  refine ⟨j₀ + 2, ?_⟩
  intro D hDα hDq hDΛ hDζ hΦ _ hκb hterm _ _ _ _ _ _ _ _ _ _ _ _ _ _ seed n _ _ hseed _ hLOK hmn
    hnM G G' hcas hlev hinv hSucc v' u' γ'
  subst hDα hDq hDΛ hDζ hterm
  have hΛ128 : 128 ≤ D.Λ := hΛ₁.trans hΛ1'
  have hΛ1 : 1 ≤ D.Λ := by omega
  have hq1 : 1 < D.q := hq.1
  have hΥ1 : 1 ≤ Υ := by linarith
  have hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
      2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ bw / (64 * (8 * Real.pi ^ 2)) :=
    startBound_of_carrierStart hΛ1 hCH hΥ1 hcs
  have hsc : ∀ m' : ℕ, 2 ≤ m' → m' ≤ D.term → PassScales D m' Cu :=
    hscales D rfl rfl rfl hΛ1' hκb
  have hseedlev : seed.level = n := hseed.1
  have hseedB := hseed.2.1
  have hexpS := hseed.2.2.2.2.2.2.2.2.1
  obtain ⟨_, -, hI⟩ := hinv
  obtain ⟨-, hGT, hG, -, hT, hcert, -⟩ := hI
  have hl1 : 1 ≤ G.level := hSucc.1
  have hlev' : G'.level = G.level - 1 := hSucc.2.1
  have hm2 : 2 ≤ G.level := by rw [hlev]; exact le_trans (by omega) hLOK.2
  have hmM : G.level ≤ D.term := by rw [hlev]; exact hmn.trans hnM.le
  have hF : StepFacts kI G G' (succProvParams D Cw kI.cr σ₀ (succEta0 D.α D.q s) N p) Cu :=
    { hζ := hζ
      hΛ := hΛ128
      hq := hq1
      hb := hbw
      hκb := hκb
      hstart := hstart
      hcert := hcert
      hT := hT
      hGen := hG
      hexpU := fun e he f f' hf hf' =>
        (hexpS _ _ e ((exports_iff_of_cascade hcas _ _ e).mp he)).2.2 f f' hf hf'
      hexp := fun e he => (hSucc.2.2.2.2.2.1 _ _ e).mpr he
      hlev := by omega
      hGT := hGT
      hGT' := hSucc.2.2.2.2.1
      hgrade := grade_mono_of_cascade hseedB hcas
      hlen := length_le_eps_of_cascade (hasTags_of_generatedSeed hseed)
        (length_of_generatedSeed hseed) (fun k => eps_succ_le hq1 hΛ128 k) (m₀ := 1)
        (fun b' hb1 hbn => freshLength_le_eps_of_passScales hcr1
          (hsc (b' + 1) (by omega) (by omega))) hcas hl1
      hsc := hsc G.level hm2 hmM
      hCu := hCu
      hδ := ocDelta_pos_of_admissible hα₀ hq }
  -- the first source
  have hvel := ComplexFlow.velC_spec hα₀ hα₁ hs₀ hs₁ hq hΛ128 hζ hΦ
  have env : ComplexFlow.ChainEnv D bw CH Υ j₀ :=
    { hq := hq1
      hΛ := hΛ128
      hα := hα₁
      hζ := hζ
      hvel := fun m => (hvel m).1
      hag := fun m t x => (hvel m).2 t x
      hb0 := hbw
      hb1 := hbw1
      hCH := hCH
      hΥ := hΥ1
      hcs := hcs }
  have hj0 : j₀ ≤ G'.level := by have := hLOK.2; omega
  have hDH := one_le_succSchedD D₀ N p hH1
  have hmax : max (N + 1) (2 * p) ≤ max (N + succSchedD D₀ N p H) (2 * p) :=
    max_le_max (by omega) le_rfl
  obtain ⟨haτ, hown⟩ := hdscales D rfl rfl rfl hΛ2' hκb G.level hm2 hmM
  rw [← hlev'] at haτ hown
  have hCdl : D.eps G.level ^ (1 + D.α) ≤ Cd * Real.sqrt (D.kap G.level * D.kap G'.level) := by
    rw [hlev']
    exact hCd D.term D.κ hκb G.level hl1
  exact ledger_all hN hsX hsZ hF (cascade_depth_of_generatedSeed hseed hcas) hC hΔD hΔR hLst hcr0
    hcr1 ((le_max_left _ _).trans hLOK.1.2.2.1) env hj0 (by omega) (by omega)
    (ComplexContext.ownSize_le_of_carrierStart hΛ1 hbw hbw1 hCH hΥ hcs (by omega) hl1) hCa hCown haτ hown
    hCdl hCD hΔfs ((le_max_right _ _).trans hLOK.1.2.2.1) hSucc γ'
    (compReserve_nonneg_of_succ kI (H := H) hHprod
      (grade_le_of_succ (grade_le_of_cascade hseedB hcas) hSucc v'))

end AVRegularity.Providers
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Providers

/-! **The context certificate of the next family** (`successor_context_certified`, the assembly of
the generation, carrier calculus and ledger statements). Generation (`successor_generated`) gives
the slotwise transversality of the extended next family; the carrier calculus
(`gen_carrier_calculus`) the holomorphic extensions of the generated expressions with mode suprema
below `genMode`; the ledger (`successor_ledger`) the witnesses of every identity with generated
expressions, certified leaves and the weighted mode sum below the witness.
`GenStage.isContextCertified_of_gates` combines the carrier calculus and the ledger into the context
certificate of the extended family, and the certificate, the generation data and the
transversality pass to the retained part (`IsContextCertified.retained`,
`IsSlotTransverse.restrict`).

Choices: `Λ₀` above the thresholds of the three statements, `c₀max` the least of theirs, `thr` that
of the ledger, `C_H = 1` and `Υ = max (max Υ₀ (4 · 8π²)) 100` (the carrier calculus's
`CarrierOK Υ₀` and the ledger's `100 ≤ Υ`), the carrier constants `κ` of the carrier calculus, the
ledger thresholds and `m_* = max m_*^{ledger} (j₀ + 2)`. The producer reserves of the new
components are nonnegative (`CascadeInvariants.compReserve_nonneg_of_succ`). -/

/-- **Context certificate of the next family**. -/
theorem successor_context_certified (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
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
      [∀ r, CompleteSpace (hr r)]
      (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ (G G' : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      (∃ tA : ℝ, tS ≤ tA ∧
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G) →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
      (G'.retained m H J).IsGenerated ∧ (G'.retained m H J).IsSlotTransverse ∧
        (G'.retained m H J).IsContextCertified kI :=
  by
  obtain ⟨Λ₁, hΛ₁, hgen⟩ := successor_generated α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λ₂, -, hled⟩ := successor_ledger α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λ₃, -, hcalc⟩ := gen_carrier_calculus α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨max Λ₁ (max Λ₂ Λ₃), le_max_of_le_left hΛ₁, fun Λ hΛ => ?_⟩
  obtain ⟨c₁, hc₁, hgen⟩ := hgen Λ ((le_max_left _ _).trans hΛ)
  obtain ⟨c₂, hc₂, hled⟩ := hled Λ (((le_max_left _ _).trans (le_max_right _ _)).trans hΛ)
  have hcalc := hcalc Λ (((le_max_right _ _).trans (le_max_right _ _)).trans hΛ)
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, ?_⟩
  intro φ₀ hφ₀ hφs hφn hφi hφsupp bw hbw0 hbw1 Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc0 hc0max
    hcr0 hcr1 hσf hlamC H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsch hNaux hKres
    hseedA hsX hsZ
  have hgen := hgen φ₀ hφ₀ hφs hφn hφi hφsupp bw hbw0 hbw1 Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc0
    (hc0max.trans (min_le_left _ _)) hcr0 hcr1 hσf hlamC H J N p nk Lc Lf Lpr Acl Naux Nout Kres
    npad sX sZ σ₀ a σ hsch hNaux hKres hseedA hsX hsZ
  obtain ⟨thr, hled⟩ := hled φ₀ hφ₀ hφs hφn hφi hφsupp bw hbw0 hbw1 Q T₀ hQ hT₀ Ce τe kS r₀ D₀
    hCe hτe hc0 (hc0max.trans (min_le_right _ _)) hcr0 hcr1 hσf hlamC H J N p nk Lc Lf Lpr Acl
    Naux Nout Kres npad sX sZ σ₀ a σ hsch hNaux hKres hseedA hsX hsZ
  obtain ⟨Υ₀, hcalc⟩ := hcalc bw hbw0 hbw1
  have hΥ100 : (100 : ℝ) ≤ max (max Υ₀ (4 * (8 * Real.pi ^ 2))) 100 := le_max_right _ _
  obtain ⟨κ, hκ, hcalc⟩ := hcalc 1 (max (max Υ₀ (4 * (8 * Real.pi ^ 2))) 100)
    ⟨le_rfl, le_max_left _ _⟩
  refine ⟨thr, 1, max (max Υ₀ (4 * (8 * Real.pi ^ 2))) 100, le_rfl, by linarith,
    fun kI hadm => ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hHprod, -⟩ := id hadm
  obtain ⟨CIthr, Cwthr, hled⟩ := hled 1 _ le_rfl hΥ100 κ hκ kI hadm
  refine ⟨CIthr, Cwthr, fun CI Cw j₀ hLA hcs => ?_⟩
  obtain ⟨mStar, hled⟩ := hled CI Cw j₀ hcs
  refine ⟨max mStar (j₀ + 2), ?_⟩
  intro D hDα hDq hDΛ hDζ hΦ M hκb hterm Mnat hMnat law hlaw hr _ _ _ _ _ _ seedK freshK hfresh
    seed n tS tf hseed m hm hmn hnM G G' hcas hlev hinv hSucc
  have hgen' := (hgen thr 1 _ le_rfl (by linarith) kI hadm CIthr Cwthr CI Cw j₀ hLA hcs
    (max mStar (j₀ + 2)) D hDα hDq hDΛ hDζ hΦ M hκb hterm Mnat hMnat law hlaw seedK freshK hfresh
    seed n tS tf hseed m hm hmn hnM G G' hcas hlev hinv hSucc).2
  have hledG := hled D hDα hDq hDΛ hDζ hΦ M hκb hterm Mnat hMnat law hlaw seedK freshK hfresh
    seed n tS tf hseed m ⟨hLA, (le_max_left _ _).trans hm⟩ hmn hnM G G' hcas hlev hinv hSucc
  have hjm : j₀ + 2 ≤ m := (le_max_right _ _).trans hm
  have hlev' : G'.level = G.level - 1 := hSucc.2.1
  have hj0 : j₀ ≤ G'.level := by omega
  have h1 : 1 ≤ G'.level := by omega
  have hres : ∀ v : CompIn G'.comps, 0 ≤ compReserve kI v.1 := fun v =>
    CascadeInvariants.compReserve_nonneg_of_succ kI (H := H) hHprod
      (CascadeInvariants.grade_le_of_succ (CascadeInvariants.grade_le_of_cascade hseed.2.1 hcas) hSucc v)
  have hcert := GenStage.isContextCertified_of_gates G' kI κ
    (fun p hp Δ hΔ leaf hL e hs hsf f hf => hcalc j₀ hcs D hDα hDq hDΛ hDζ hΦ M hκb hterm
      G'.level p h1 hj0 hp Δ hΔ leaf hL e hs hsf f hf) hres hledG
  exact ⟨(hcert.retained m H J).1, hgen'.restrict _ _, (hcert.retained m H J).2⟩

end AVRegularity.Providers
end
end

section
@[expose] public section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Providers

/-! **The actual successor inherits the torus law** (`successor_torus_compatible`, the
construction induction). The reduction
`successor_torus_compatible_of_ingredients` leaves the base-label invariance of the fluxes of the
extended next family at order `d ≥ 2`, for the non-diagonal identities
(`Torus.nonDiagonalTransferBaseShift`: transferred coefficients of the finer outputs) and for the
diagonal identities (`Torus.diagonalSourceBaseShift`: first-source coefficients). Both rest on
`Torus.Geometry` (the renewal flows are ℤ²-equivariant, so a shifted base label translates the
whole geometry and leaves the chart maps, Jacobians, metrics and strains of every recentered and
appended family unchanged) and `Torus.Lifts` (the lift data do not see the base label, so by lift
uniqueness on the original interval of the slot the lifts on the shifted families agree with the
lifts at every time of nonzero weight). -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]

/-- **The actual successor inherits the torus law**. -/
theorem successor_torus_compatible {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} (P : ProvParams)
    (hζ : IsFastProfile D.ζ) (hκ : ∀ i, 0 < D.κ i)
    (Mn : SuccMenu) (M : ℕ) (G G' : GenStage D hr Dm b j₀) (hnat : G.IsNatural M)
    (hold : ∀ v ∈ G.comps, ∀ e ∈ v.births, G.level ≤ e.scale)
    (hsh : G.IsShiftInvariant) (hsucc : IsActualSuccessor D P Mn G G') :
    G'.IsShiftInvariant ∧ IsTorusCompatible G'.fam G'.actual (D.eps (G'.level - 1)) :=
  Construction.Preservation.Assembly.successor_torus_compatible_of_ingredients
    Torus.nonDiagonalTransferBaseShift Torus.diagonalSourceBaseShift P hζ hκ Mn M G G' hnat hold
    hsh hsucc

end AVRegularity.Providers
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Providers

/-! The cascade successor existence statement, instantiated from the shared qualitative
construction also used by the terminal entry. -/

/-- **Existence of the actual next family** (Definition 10.3 and display (12.20) of the paper). -/
theorem successor_exists (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
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
      [∀ r, CompleteSpace (hr r)]
      (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ G : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀,
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      (∃ tA : ℝ, tS ≤ tA ∧
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G) →
      ∃ G' : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀,
        IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
          (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' := by
  exact (And.intro
    (Construction.StageSuccessor.successor_exists_of_ingredients α s q ζ
      (Construction.StageSuccessor.cascade_successor_inputs α s q ζ hζ)
      Construction.StageSuccessor.stage_successor_exists)
    (And.intro hα₀ (And.intro hα₁ (And.intro hs₀ (And.intro hs₁ hq))))).1

end AVRegularity.Providers
end
end
