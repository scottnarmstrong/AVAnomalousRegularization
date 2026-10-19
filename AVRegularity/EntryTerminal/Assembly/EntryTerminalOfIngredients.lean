-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Definitions.EntryWeak.WeakReduction
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.EntryTerminal.Assembly

/-! Exact statements of the inputs to the terminal-entry composition, stated as definitions
without their proofs. -/

/-- Exact statement of `entry_weak`, without importing its proof. -/
def EntryWeakStatement : Prop :=
  ∀ (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ),
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Jw : ℕ) (τ T₀ Pw η₀ : ℝ), 1 ≤ Jw → 0 < τ → τ < T₀ → 0 < Pw → 0 < η₀ →
      η₀ ≤ ocDelta α q / 8 →
    ∃ (Nw Rw Lw : ℕ), 1 ≤ Nw ∧ Lw = Jw * Nw ∧
      Pw + 2 * q ^ Jw + 1 + 2 < Nw * (q - 1) ∧
      Pw + 2 * q ^ Jw + 1 + q ^ Jw + 1 < 2 * weakAStar α q * (Rw + 1) ∧
    ∀ σw : ℝ, 0 < σw → σw < min (ocC α q) (q - 1) → ∃ L₀ SX SZ : ℕ,
    ∀ (L Kw sX sZ : ℕ) (nW : ℕ+) (kReq : InvConsts), 1 ≤ kReq.G0 → L₀ ≤ L → SX ≤ sX → SZ ≤ sZ →
      L + 1 ≤ 2 * (nW : ℕ) → Lw + 5 ≤ Kw →
    ∃ (cK CK CL Cχ Cread Cid : ℝ) (kW : InvConsts),
      0 < cK ∧ kW.c₀ = cK ∧ IsWeakAllocation kW kReq L ∧
    ∃ (CHw Υw : ℝ), 1 ≤ CHw ∧ 0 < Υw ∧
    ∀ j₀ : ℕ, IsCarrierStart α q Λ bw CHw Υw j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ M D.κ → D.term = M →
    ∀ (Dm : ℕ), 1 + Jw * Nw ≤ Dm →
    ∀ (P : ProvParams) (a : ℝ),
    ∃ (stage : ℕ → GenStage D ScalarH Dm bw j₀) (Gw : GenStage D ScalarH Dm bw j₀) (rootM rootR : ℕ → ℝ)
      (ι : CompIn (stage M).comps ≃ CompIn Gw.comps) (aM : ℝ)
      (CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root))
      (W : (i : ℕ) → ℝ → (CompIn (stage i).comps → Vec 2 → ℝ) → Vec 2 → ℝ),
      IsWeakConstruction D P (⟨Nw, Rw, sX, sZ, η₀, M + Jw⟩ : WeakMenu) M Jw (D.termRW σw M) 0 stage ∧
      IsWeakEncoding Nw Jw η₀ rootM rootR (stage M) Gw ι ∧
      (∀ r, 0 < rootM r) ∧ (∀ r, 0 < rootR r) ∧
      (∀ i, M < i → i ≤ M + Jw → IsWeakReadoutLifts i Nw (Jw * Rw) sX sZ (stage i) (CcR i)) ∧
      IsWeakReadoutChain M Jw Nw 0 η₀ (fun _ => (Jw * Rw)) stage CcR W ∧
      ∀ law : BirthLaw, law.rootMass = rootM → law.rootReadout = rootR →
        IsWeakStage law P φ₀ hφ₀ M (M + Jw) Jw (Jw * Rw) (1 + Jw * Nw) nW kW a T₀ σw CL Cχ (weakChi α q η₀)
          Gw aM ∧
        ∀ (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ),
          IsWeakSolutionOn (streamVel (D.Φ (M + Jw))) (D.κ M) a (a + T₀) f θ →
        ∃ (tq : ℕ → ℝ)
          (Ur : (i : ℕ) → ∀ v : CompIn (stage i).comps, ℝ → TorusHk Kw (ScalarH v.1.root))
          (Urw : (i : ℕ) → ∀ v : CompIn (stage i).comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
          (Urk : (i : ℕ) → ∀ v u (_ : (stage i).fam.Γ v u), ℝ → TorusHk (Kw + Dm - 1) (ScalarH u.1.root))
          (U₀ : ∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root))
          (U V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root))
          (Uw Vw : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
          (Uk Vk : ∀ v u (_ : Gw.fam.Γ v u), ℝ → TorusHk (Kw + Dm - 1) (ScalarH u.1.root)),
          IsWeakReduction P φ₀ hφ₀ nW M Jw Kw 0 a (a + T₀) θ stage tq Ur Urw Urk ∧
          tq (M + 1) = aM ∧ (U₀ = fun v => rerootFamily ι (Ur M) v aM) ∧ U = rerootFamily ι (Ur M) ∧
          IsWeakPaired P φ₀ hφ₀ law M Kw L nW a T₀ σw (weakChi α q η₀) cK CK f Gw aM
            U₀ U V Uw Vw Uk Vk ∧
          IsWeakReadout law M Jw Lw Kw (D.κ M) a τ T₀ s Pw cK Cread Cid f θ Gw
            (fun t g x => W M t (fun v x' => g (ι v) x') x) V

/-- Exact statement of `entry_terminal_of_weak`, without importing its proof. -/
def EntryTerminalOfWeakStatement : Prop :=
  ∀ (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ),
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (c₀max : ℝ), 0 < c₀max →
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Jw Lw dW DW L0w : ℕ) (τ T₀ Pw σw χw η₀ : ℝ),
      1 ≤ Jw → 1 ≤ DW → 0 < τ → τ < T₀ → 0 < Pw → 0 < σw → σw < min (ocC α q) (q - 1) → 0 < χw →
      0 < η₀ → η₀ ≤ ocDelta α q / 8 →
    ∀ PT : ℝ, 0 < PT →
    ∀ (NT pT RT AT k₀ LcT LoT LfT LpT : ℕ) (tT QT : ℝ),
      IsTerminalSchedule α q s PT QT σw χw η₀ tT Jw Lw k₀ NT pT RT AT LcT LoT LfT LpT
        (termAlphabet NT pT DW dW) →
    ∀ τe lamE : ℝ, IsEntrySeedExponents α q σw χw η₀ tT τe lamE NT pT DW dW →
    ∀ (σ₀ : ℝ) (H J N p Kres Lpr Lc Lf : ℕ) (nT : ℕ+), IsFreshKernelOrder nT LcT Lpr Lc Lf →
    ∀ Kout : ℕ,
    ∃ SX SZ : ℕ, ∀ sXT sZT : ℕ, SX ≤ sXT → SZ ≤ sZT →
    ∃ (Kw Lt : ℕ) (nW : ℕ+) (hk₀w : k₀ ≤ Kw) (hLw : Lw + 5 ≤ Kw) (cr : ℝ) (kS : InvConsts),
      L0w ≤ Lt ∧ LpT ≤ Lt ∧ Lt + 1 ≤ 2 * (nW : ℕ) ∧ IsTerminalKernelOrders nW LoT LfT LpT Lpr Lc Lf ∧
      0 < cr ∧ kS.cr = cr ∧ 0 < kS.c₀ ∧ kS.c₀ ≤ c₀max ∧ kS.cr ≤ 1 ∧
      kS.σf = ocDelta α q ∧ kS.lamC = lamE ∧
      IsSeedAllocation kS (termR0bar RT dW) (termD0bar NT pT DW dW) H J N p Kres Lpr Lc Lf ∧
      (kS.mEnv = 0 ∧ kS.Kan = kS.Ks ∧ kS.Lan = kS.Ks ∧ kS.Jm = kS.Ks) ∧
      Lt + DW + max (Lw + 5) k₀ ≤ Kw ∧
      cr = 1 ∧
    ∀ (cK CK CL Cχ Cread Cid : ℝ) (kW : InvConsts), 0 < cK → kW.c₀ = cK →
      IsWeakAllocation kW kS Lt →
    ∃ (c C Centry cH Ce Cw : ℝ), 0 < c ∧ 0 < cH ∧ 1 ≤ Ce ∧
    ∃ (CHt Υt : ℝ), 1 ≤ CHt ∧ 0 < Υt ∧
    ∀ j₀ : ℕ, IsCarrierStart α q Λ bw CHt Υt j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ M D.κ → D.term = M →
    ∀ (a : ℝ) (lawW : BirthLaw) (PW : ProvParams)
      (Gw : GenStage D ScalarH (termD0bar NT pT DW dW) bw j₀) (aM : ℝ)
      (Ww : ℝ → (CompIn Gw.comps → Vec 2 → ℝ) → Vec 2 → ℝ),
      IsWeakStage lawW PW φ₀ hφ₀ M (M + Jw) Jw dW DW nW kW a T₀ σw CL Cχ χw Gw aM →
    ∃ (tp : ℝ) (Pterm : (∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn Gw.comps, TorusHk (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) (ScalarH v.1.root)))
      (lawT : BirthLaw) (Gt' : GenStage D ScalarH (termD0bar NT pT DW dW) bw j₀) (seed : GenStage D ScalarH (succSchedD (termD0bar NT pT DW dW) N p (H + 1)) bw j₀)
      (rootM rootR : ℕ → ℝ) (seedKc : ℕ → KernelSpec)
      (ι : CompIn (Gt'.retained M 1 RT).comps ≃ CompIn seed.comps),
      IsTerminalPrepMap M Kw (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) c C Gw aM tp Pterm ∧
      IsTerminalLaw lawW lawT cH η₀ (wordsUpTo (termAlphabet NT pT DW dW) RT).card ∧
      IsActualSuccessor D (termProvParams D Cw cr tT η₀ NT pT M)
        (termMenu (M + Jw) (termAlphabet NT pT DW dW) RT NT pT sXT sZT η₀ tp cr) Gw Gt' ∧
      IsSeedEncoding (termProvParams D Cw cr tT η₀ NT pT M) lawT rootM rootR
        (fun _ => isoPairedKernel (D.termRW σw M) nW) (fun _ => isoPairedKernel (D.termRNew cr tT M) nT)
        seedKc (Gt'.retained M 1 RT) seed ι ∧
      TerminalSeedClauses rootM rootR seedKc φ₀ hφ₀ (M + Jw) (M - 1) kS Ce τe (termR0bar RT dW) (termD0bar NT pT DW dW) seed
        (tp + D.termH M) (a + T₀) ∧
      tp + D.termH M + 3 * ocTau α q Λ (M - 1) + 4 * ocTauPP α q Λ (M - 1) ≤ a + T₀ ∧
      ∀ (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ)
        (U₀ : ∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root))
        (U V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root))
        (Uw Vw : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
        (Uk Vk : ∀ v u (_ : Gw.fam.Γ v u), ℝ → TorusHk (Kw + (termD0bar NT pT DW dW) - 1) (ScalarH u.1.root)),
        IsWeakPaired PW φ₀ hφ₀ lawW M Kw Lt nW a T₀ σw χw cK CK f Gw aM U₀ U V Uw Vw Uk Vk →
        IsWeakReadout lawW M Jw Lw Kw (D.κ M) a τ T₀ s Pw cK Cread Cid f θ Gw Ww V →
        IsTerminalPrepBounds lawW M Kw (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) k₀ hk₀w (le_trans (by omega : k₀ ≤ 2 * k₀ + 2) (le_trans (le_max_left _ _) (le_max_right Kout _))) cr cK C QT f Gw aM tp Pterm V ∧
        ∃ Z : ∀ v : CompIn (Gt'.retained M 1 RT).comps, ℝ → TorusHk (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) (ScalarH v.1.root),
          TerminalFamilyClauses (termProvParams D Cw cr tT η₀ NT pT M)
            (fun _ => isoPairedKernel (D.termRW σw M) nW)
            (fun _ => isoPairedKernel (D.termRNew cr tT M) nT) φ₀ hφ₀ lawW lawT rootM M (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) cr C
            Centry tp (tp + D.termH M) (a + T₀) f Gw (Gt'.retained M 1 RT) seed ι
            (Pterm fun v => V v aM) Z ∧
          EntryIdentityClauses Gw (Gt'.retained M 1 RT) M pT (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) Kw Lw NT dW sXT sZT η₀ tp a τ T₀ s
            Pw PT C cr f θ Ww V Z

/-- Exact statement of `entry_terminal`, without importing its proof. -/
def EntryTerminalStatement : Prop :=
  ∀ (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ),
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (c₀max : ℝ), 0 < c₀max →
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Jw : ℕ) (τ T₀ Pw η₀ : ℝ), 1 ≤ Jw → 0 < τ → τ < T₀ → 0 < Pw → 0 < η₀ →
      η₀ ≤ ocDelta α q / 8 →
    ∃ (Nw Rw Lw : ℕ), 1 ≤ Nw ∧ Lw = Jw * Nw ∧
      Pw + 2 * q ^ Jw + 1 + 2 < Nw * (q - 1) ∧
      Pw + 2 * q ^ Jw + 1 + q ^ Jw + 1 < 2 * weakAStar α q * (Rw + 1) ∧
    ∀ σw : ℝ, 0 < σw → σw < min (ocC α q) (q - 1) →
    ∀ PT : ℝ, 0 < PT →
    ∀ (NT pT RT AT k₀ LcT LoT LfT LpT : ℕ) (tT QT : ℝ),
      IsTerminalSchedule α q s PT QT σw (weakChi α q η₀) η₀ tT Jw Lw k₀ NT pT RT AT LcT LoT LfT LpT (termAlphabet NT pT (1 + Jw * Nw) (Jw * Rw)) →
    ∀ τe lamE : ℝ, IsEntrySeedExponents α q σw (weakChi α q η₀) η₀ tT τe lamE NT pT (1 + Jw * Nw) (Jw * Rw) →
    ∀ (σ₀ : ℝ) (H J N p Kres Lpr Lc Lf : ℕ) (nT : ℕ+), IsFreshKernelOrder nT LcT Lpr Lc Lf →
    ∀ Kout : ℕ,
    ∃ SX SZ : ℕ, ∀ sXT sZT : ℕ, SX ≤ sXT → SZ ≤ sZT →
    ∃ (Kw Lt : ℕ) (nW : ℕ+) (hk₀w : k₀ ≤ Kw) (hLw : Lw + 5 ≤ Kw) (cr : ℝ) (kS : InvConsts),
      LpT ≤ Lt ∧ Lt + 1 ≤ 2 * (nW : ℕ) ∧ IsTerminalKernelOrders nW LoT LfT LpT Lpr Lc Lf ∧
      0 < cr ∧ kS.cr = cr ∧ 0 < kS.c₀ ∧ kS.c₀ ≤ c₀max ∧ kS.cr ≤ 1 ∧
      kS.σf = ocDelta α q ∧ kS.lamC = lamE ∧
      IsSeedAllocation kS (termR0bar RT (Jw * Rw)) (termD0bar NT pT (1 + Jw * Nw) (Jw * Rw)) H J N p Kres Lpr Lc Lf ∧
      (kS.mEnv = 0 ∧ kS.Kan = kS.Ks ∧ kS.Lan = kS.Ks ∧ kS.Jm = kS.Ks) ∧
      Lt + (1 + Jw * Nw) + max (Lw + 5) k₀ ≤ Kw ∧
      cr = 1 ∧
    ∃ (cK CK CL Cχ Cread Cid : ℝ) (kW : InvConsts),
      0 < cK ∧ kW.c₀ = cK ∧ IsWeakAllocation kW kS Lt ∧
    ∃ (c C Centry cH Ce Cw : ℝ), 0 < c ∧ 0 < cH ∧ 1 ≤ Ce ∧
    ∃ (CHt Υt : ℝ), 1 ≤ CHt ∧ 0 < Υt ∧
    ∀ j₀ : ℕ, IsCarrierStart α q Λ bw CHt Υt j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
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
        (∀ v : CompIn Gw.comps, TorusHk (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) (ScalarH v.1.root)))
      (lawT : BirthLaw) (Gt' : GenStage D ScalarH (termD0bar NT pT (1 + Jw * Nw) (Jw * Rw)) bw j₀)
      (seed : GenStage D ScalarH (succSchedD (termD0bar NT pT (1 + Jw * Nw) (Jw * Rw)) N p (H + 1)) bw j₀)
      (rootM rootR : ℕ → ℝ) (seedKc : ℕ → KernelSpec)
      (ι : CompIn (Gt'.retained M 1 RT).comps ≃ CompIn seed.comps),
      IsTerminalPrepMap M Kw (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) c C Gw aM tp Pterm ∧
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
        IsWeakReadout lawW M Jw Lw Kw (D.κ M) a τ T₀ s Pw cK Cread Cid f θ Gw
          (fun t g x => W M t (fun v x' => g (ιw v) x') x) V ∧
        IsTerminalPrepBounds lawW M Kw (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) k₀ hk₀w (le_trans (by omega : k₀ ≤ 2 * k₀ + 2) (le_trans (le_max_left _ _) (le_max_right Kout _))) cr cK C QT f Gw aM tp Pterm V ∧
        ∃ Z : ∀ v : CompIn (Gt'.retained M 1 RT).comps, ℝ → TorusHk (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) (ScalarH v.1.root),
          TerminalFamilyClauses (termProvParams D Cw cr tT η₀ NT pT M)
            (fun _ => isoPairedKernel (D.termRW σw M) nW)
            (fun _ => isoPairedKernel (D.termRNew cr tT M) nT) φ₀ hφ₀ lawW lawT rootM M (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) cr C
            Centry tp (tp + D.termH M) (a + T₀) f Gw (Gt'.retained M 1 RT) seed ι
            (Pterm fun v => V v aM) Z ∧
          EntryIdentityClauses Gw (Gt'.retained M 1 RT) M pT (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) Kw Lw NT (Jw * Rw) sXT sZT η₀ tp a τ T₀ s
            Pw PT C cr f θ (fun t g x => W M t (fun v x' => g (ιw v) x') x) V Z

/-! Composition of weak entry with the conditional terminal entry. -/

/-- Fixed requests and constants shared by the two entry tails. -/
structure EntryCompositionData where
  α : ℝ
  s : ℝ
  q : ℝ
  Λ : ℕ
  ζ : ℝ → ℝ
  φ₀ : Vec 2 → ℝ
  hφ₀ : Integrable φ₀
  bw : ℝ
  Jw : ℕ
  Nw : ℕ
  Rw : ℕ
  Lw : ℕ
  τ : ℝ
  T₀ : ℝ
  Pw : ℝ
  η₀ : ℝ
  σw : ℝ
  NT : ℕ
  pT : ℕ
  RT : ℕ
  k₀ : ℕ
  sXT : ℕ
  sZT : ℕ
  tT : ℝ
  QT : ℝ
  τe : ℝ
  H : ℕ
  J : ℕ
  N : ℕ
  p : ℕ
  Kout : ℕ
  Kw : ℕ
  Lt : ℕ
  nW : ℕ+
  hk₀w : k₀ ≤ Kw
  cr : ℝ
  kS : InvConsts
  cK : ℝ
  CK : ℝ
  CL : ℝ
  Cχ : ℝ
  Cread : ℝ
  Cid : ℝ
  kW : InvConsts
  c : ℝ
  C : ℝ
  Centry : ℝ
  cH : ℝ
  Ce : ℝ
  Cw : ℝ
  nT : ℕ+
  PT : ℝ

/-- The exact weak-entry tail, after its constants have been selected. -/
def WeakEntryTail (req : EntryCompositionData) : Prop :=
    ∃ (CHw Υw : ℝ), 1 ≤ CHw ∧ 0 < Υw ∧
    ∀ j₀ : ℕ, IsCarrierStart req.α req.q req.Λ req.bw CHw Υw j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = req.α → D.q = req.q → D.Λ = req.Λ → D.ζ = req.ζ → IsOCStreamSeq req.α req.q req.Λ req.ζ D.Φ →
      IsOCBandChain req.α req.q req.Λ req.ζ M D.κ → D.term = M →
    ∀ (Dm : ℕ), 1 + req.Jw * req.Nw ≤ Dm →
    ∀ (P : ProvParams) (a : ℝ),
    ∃ (stage : ℕ → GenStage D ScalarH Dm req.bw j₀) (Gw : GenStage D ScalarH Dm req.bw j₀) (rootM rootR : ℕ → ℝ)
      (ι : CompIn (stage M).comps ≃ CompIn Gw.comps) (aM : ℝ)
      (CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root))
      (W : (i : ℕ) → ℝ → (CompIn (stage i).comps → Vec 2 → ℝ) → Vec 2 → ℝ),
      IsWeakConstruction D P (⟨req.Nw, req.Rw, req.sXT, req.sZT, req.η₀, M + req.Jw⟩ : WeakMenu) M req.Jw (D.termRW req.σw M) 0 stage ∧
      IsWeakEncoding req.Nw req.Jw req.η₀ rootM rootR (stage M) Gw ι ∧
      (∀ r, 0 < rootM r) ∧ (∀ r, 0 < rootR r) ∧
      (∀ i, M < i → i ≤ M + req.Jw → IsWeakReadoutLifts i req.Nw (req.Jw * req.Rw) req.sXT req.sZT (stage i) (CcR i)) ∧
      IsWeakReadoutChain M req.Jw req.Nw 0 req.η₀ (fun _ => (req.Jw * req.Rw)) stage CcR W ∧
      ∀ law : BirthLaw, law.rootMass = rootM → law.rootReadout = rootR →
        IsWeakStage law P req.φ₀ req.hφ₀ M (M + req.Jw) req.Jw (req.Jw * req.Rw) (1 + req.Jw * req.Nw) req.nW req.kW a req.T₀ req.σw req.CL req.Cχ (weakChi req.α req.q req.η₀)
          Gw aM ∧
        ∀ (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ),
          IsWeakSolutionOn (streamVel (D.Φ (M + req.Jw))) (D.κ M) a (a + req.T₀) f θ →
        ∃ (tq : ℕ → ℝ)
          (Ur : (i : ℕ) → ∀ v : CompIn (stage i).comps, ℝ → TorusHk req.Kw (ScalarH v.1.root))
          (Urw : (i : ℕ) → ∀ v : CompIn (stage i).comps, ℝ → TorusHk (req.Kw + 1) (ScalarH v.1.root))
          (Urk : (i : ℕ) → ∀ v u (_ : (stage i).fam.Γ v u), ℝ → TorusHk (req.Kw + Dm - 1) (ScalarH u.1.root))
          (U₀ : ∀ v : CompIn Gw.comps, TorusHk req.Kw (ScalarH v.1.root))
          (U V : ∀ v : CompIn Gw.comps, ℝ → TorusHk req.Kw (ScalarH v.1.root))
          (Uw Vw : ∀ v : CompIn Gw.comps, ℝ → TorusHk (req.Kw + 1) (ScalarH v.1.root))
          (Uk Vk : ∀ v u (_ : Gw.fam.Γ v u), ℝ → TorusHk (req.Kw + Dm - 1) (ScalarH u.1.root)),
          IsWeakReduction P req.φ₀ req.hφ₀ req.nW M req.Jw req.Kw 0 a (a + req.T₀) θ stage tq Ur Urw Urk ∧
          tq (M + 1) = aM ∧ (U₀ = fun v => rerootFamily ι (Ur M) v aM) ∧ U = rerootFamily ι (Ur M) ∧
          IsWeakPaired P req.φ₀ req.hφ₀ law M req.Kw req.Lt req.nW a req.T₀ req.σw (weakChi req.α req.q req.η₀) req.cK req.CK f Gw aM
            U₀ U V Uw Vw Uk Vk ∧
          IsWeakReadout law M req.Jw req.Lw req.Kw (D.κ M) a req.τ req.T₀ req.s req.Pw req.cK req.Cread req.Cid f θ Gw
            (fun t g x => W M t (fun v x' => g (ι v) x') x) V

/-- The exact conditional terminal tail at the same request. -/
def ConditionalTerminalTail (req : EntryCompositionData) : Prop :=
    ∃ (CHt Υt : ℝ), 1 ≤ CHt ∧ 0 < Υt ∧
    ∀ j₀ : ℕ, IsCarrierStart req.α req.q req.Λ req.bw CHt Υt j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = req.α → D.q = req.q → D.Λ = req.Λ → D.ζ = req.ζ → IsOCStreamSeq req.α req.q req.Λ req.ζ D.Φ →
      IsOCBandChain req.α req.q req.Λ req.ζ M D.κ → D.term = M →
    ∀ (a : ℝ) (lawW : BirthLaw) (PW : ProvParams)
      (Gw : GenStage D ScalarH (termD0bar req.NT req.pT (1 + req.Jw * req.Nw) (req.Jw * req.Rw)) req.bw j₀) (aM : ℝ)
      (Ww : ℝ → (CompIn Gw.comps → Vec 2 → ℝ) → Vec 2 → ℝ),
      IsWeakStage lawW PW req.φ₀ req.hφ₀ M (M + req.Jw) req.Jw (req.Jw * req.Rw) (1 + req.Jw * req.Nw) req.nW req.kW a req.T₀ req.σw req.CL req.Cχ (weakChi req.α req.q req.η₀) Gw aM →
    ∃ (tp : ℝ) (Pterm : (∀ v : CompIn Gw.comps, TorusHk req.Kw (ScalarH v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn Gw.comps, TorusHk (max req.Kout (max (2 * req.k₀ + 2) (req.NT + 2 * req.pT + req.k₀ + 2))) (ScalarH v.1.root)))
      (lawT : BirthLaw) (Gt' : GenStage D ScalarH (termD0bar req.NT req.pT (1 + req.Jw * req.Nw) (req.Jw * req.Rw)) req.bw j₀) (seed : GenStage D ScalarH (succSchedD (termD0bar req.NT req.pT (1 + req.Jw * req.Nw) (req.Jw * req.Rw)) req.N req.p (req.H + 1)) req.bw j₀)
      (rootM rootR : ℕ → ℝ) (seedKc : ℕ → KernelSpec)
      (ι : CompIn (Gt'.retained M 1 req.RT).comps ≃ CompIn seed.comps),
      IsTerminalPrepMap M req.Kw (max req.Kout (max (2 * req.k₀ + 2) (req.NT + 2 * req.pT + req.k₀ + 2))) req.c req.C Gw aM tp Pterm ∧
      IsTerminalLaw lawW lawT req.cH req.η₀ (wordsUpTo (termAlphabet req.NT req.pT (1 + req.Jw * req.Nw) (req.Jw * req.Rw)) req.RT).card ∧
      IsActualSuccessor D (termProvParams D req.Cw req.cr req.tT req.η₀ req.NT req.pT M)
        (termMenu (M + req.Jw) (termAlphabet req.NT req.pT (1 + req.Jw * req.Nw) (req.Jw * req.Rw)) req.RT req.NT req.pT req.sXT req.sZT req.η₀ tp req.cr) Gw Gt' ∧
      IsSeedEncoding (termProvParams D req.Cw req.cr req.tT req.η₀ req.NT req.pT M) lawT rootM rootR
        (fun _ => isoPairedKernel (D.termRW req.σw M) req.nW) (fun _ => isoPairedKernel (D.termRNew req.cr req.tT M) req.nT)
        seedKc (Gt'.retained M 1 req.RT) seed ι ∧
      TerminalSeedClauses rootM rootR seedKc req.φ₀ req.hφ₀ (M + req.Jw) (M - 1) req.kS req.Ce req.τe (termR0bar req.RT (req.Jw * req.Rw)) (termD0bar req.NT req.pT (1 + req.Jw * req.Nw) (req.Jw * req.Rw)) seed
        (tp + D.termH M) (a + req.T₀) ∧
      tp + D.termH M + 3 * ocTau req.α req.q req.Λ (M - 1) + 4 * ocTauPP req.α req.q req.Λ (M - 1) ≤ a + req.T₀ ∧
      ∀ (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ)
        (U₀ : ∀ v : CompIn Gw.comps, TorusHk req.Kw (ScalarH v.1.root))
        (U V : ∀ v : CompIn Gw.comps, ℝ → TorusHk req.Kw (ScalarH v.1.root))
        (Uw Vw : ∀ v : CompIn Gw.comps, ℝ → TorusHk (req.Kw + 1) (ScalarH v.1.root))
        (Uk Vk : ∀ v u (_ : Gw.fam.Γ v u), ℝ → TorusHk (req.Kw + (termD0bar req.NT req.pT (1 + req.Jw * req.Nw) (req.Jw * req.Rw)) - 1) (ScalarH u.1.root)),
        IsWeakPaired PW req.φ₀ req.hφ₀ lawW M req.Kw req.Lt req.nW a req.T₀ req.σw (weakChi req.α req.q req.η₀) req.cK req.CK f Gw aM U₀ U V Uw Vw Uk Vk →
        IsWeakReadout lawW M req.Jw req.Lw req.Kw (D.κ M) a req.τ req.T₀ req.s req.Pw req.cK req.Cread req.Cid f θ Gw Ww V →
        IsTerminalPrepBounds lawW M req.Kw (max req.Kout (max (2 * req.k₀ + 2) (req.NT + 2 * req.pT + req.k₀ + 2))) req.k₀ req.hk₀w (le_trans (by omega : req.k₀ ≤ 2 * req.k₀ + 2) (le_trans (le_max_left _ _) (le_max_right req.Kout _))) req.cr req.cK req.C req.QT f Gw aM tp Pterm V ∧
        ∃ Z : ∀ v : CompIn (Gt'.retained M 1 req.RT).comps, ℝ → TorusHk (max req.Kout (max (2 * req.k₀ + 2) (req.NT + 2 * req.pT + req.k₀ + 2))) (ScalarH v.1.root),
          TerminalFamilyClauses (termProvParams D req.Cw req.cr req.tT req.η₀ req.NT req.pT M)
            (fun _ => isoPairedKernel (D.termRW req.σw M) req.nW)
            (fun _ => isoPairedKernel (D.termRNew req.cr req.tT M) req.nT) req.φ₀ req.hφ₀ lawW lawT rootM M (max req.Kout (max (2 * req.k₀ + 2) (req.NT + 2 * req.pT + req.k₀ + 2))) req.cr req.C
            req.Centry tp (tp + D.termH M) (a + req.T₀) f Gw (Gt'.retained M 1 req.RT) seed ι
            (Pterm fun v => V v aM) Z ∧
          EntryIdentityClauses Gw (Gt'.retained M 1 req.RT) M req.pT (max req.Kout (max (2 * req.k₀ + 2) (req.NT + 2 * req.pT + req.k₀ + 2))) req.Kw req.Lw req.NT (req.Jw * req.Rw) req.sXT req.sZT req.η₀ tp a req.τ req.T₀ req.s
            req.Pw req.PT req.C req.cr f θ Ww V Z

/-- The full terminal conclusion below its constant choices. -/
def FullTerminalTail (req : EntryCompositionData) : Prop :=
    ∃ (CHt Υt : ℝ), 1 ≤ CHt ∧ 0 < Υt ∧
    ∀ j₀ : ℕ, IsCarrierStart req.α req.q req.Λ req.bw CHt Υt j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = req.α → D.q = req.q → D.Λ = req.Λ → D.ζ = req.ζ → IsOCStreamSeq req.α req.q req.Λ req.ζ D.Φ →
      IsOCBandChain req.α req.q req.Λ req.ζ M D.κ → D.term = M →
    ∀ (PW : ProvParams) (a : ℝ),
    ∃ (stage : ℕ → GenStage D ScalarH (termD0bar req.NT req.pT (1 + req.Jw * req.Nw) (req.Jw * req.Rw)) req.bw j₀) (Gw : GenStage D ScalarH (termD0bar req.NT req.pT (1 + req.Jw * req.Nw) (req.Jw * req.Rw)) req.bw j₀) (lawW : BirthLaw)
      (ιw : CompIn (stage M).comps ≃ CompIn Gw.comps) (aM : ℝ)
      (CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root))
      (W : (i : ℕ) → ℝ → (CompIn (stage i).comps → Vec 2 → ℝ) → Vec 2 → ℝ),
      IsWeakConstruction D PW (⟨req.Nw, req.Rw, req.sXT, req.sZT, req.η₀, M + req.Jw⟩ : WeakMenu) M req.Jw (D.termRW req.σw M) 0 stage ∧
      IsWeakEncoding req.Nw req.Jw req.η₀ lawW.rootMass lawW.rootReadout (stage M) Gw ιw ∧
      (∀ i, M < i → i ≤ M + req.Jw → IsWeakReadoutLifts i req.Nw (req.Jw * req.Rw) req.sXT req.sZT (stage i) (CcR i)) ∧
      IsWeakReadoutChain M req.Jw req.Nw 0 req.η₀ (fun _ => (req.Jw * req.Rw)) stage CcR W ∧
      IsWeakStage lawW PW req.φ₀ req.hφ₀ M (M + req.Jw) req.Jw (req.Jw * req.Rw) (1 + req.Jw * req.Nw) req.nW req.kW a req.T₀ req.σw req.CL req.Cχ (weakChi req.α req.q req.η₀) Gw aM ∧
    ∃ (tp : ℝ) (Pterm : (∀ v : CompIn Gw.comps, TorusHk req.Kw (ScalarH v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn Gw.comps, TorusHk (max req.Kout (max (2 * req.k₀ + 2) (req.NT + 2 * req.pT + req.k₀ + 2))) (ScalarH v.1.root)))
      (lawT : BirthLaw) (Gt' : GenStage D ScalarH (termD0bar req.NT req.pT (1 + req.Jw * req.Nw) (req.Jw * req.Rw)) req.bw j₀)
      (seed : GenStage D ScalarH (succSchedD (termD0bar req.NT req.pT (1 + req.Jw * req.Nw) (req.Jw * req.Rw)) req.N req.p (req.H + 1)) req.bw j₀)
      (rootM rootR : ℕ → ℝ) (seedKc : ℕ → KernelSpec)
      (ι : CompIn (Gt'.retained M 1 req.RT).comps ≃ CompIn seed.comps),
      IsTerminalPrepMap M req.Kw (max req.Kout (max (2 * req.k₀ + 2) (req.NT + 2 * req.pT + req.k₀ + 2))) req.c req.C Gw aM tp Pterm ∧
      IsTerminalLaw lawW lawT req.cH req.η₀ (wordsUpTo (termAlphabet req.NT req.pT (1 + req.Jw * req.Nw) (req.Jw * req.Rw)) req.RT).card ∧
      IsActualSuccessor D (termProvParams D req.Cw req.cr req.tT req.η₀ req.NT req.pT M) (termMenu (M + req.Jw) (termAlphabet req.NT req.pT (1 + req.Jw * req.Nw) (req.Jw * req.Rw)) req.RT req.NT req.pT req.sXT req.sZT req.η₀ tp req.cr) Gw Gt' ∧
      IsSeedEncoding (termProvParams D req.Cw req.cr req.tT req.η₀ req.NT req.pT M) lawT rootM rootR
        (fun _ => isoPairedKernel (D.termRW req.σw M) req.nW) (fun _ => isoPairedKernel (D.termRNew req.cr req.tT M) req.nT)
        seedKc (Gt'.retained M 1 req.RT) seed ι ∧
      TerminalSeedClauses rootM rootR seedKc req.φ₀ req.hφ₀ (M + req.Jw) (M - 1) req.kS req.Ce req.τe (termR0bar req.RT (req.Jw * req.Rw)) (termD0bar req.NT req.pT (1 + req.Jw * req.Nw) (req.Jw * req.Rw)) seed
        (tp + D.termH M) (a + req.T₀) ∧
      tp + D.termH M + 3 * ocTau req.α req.q req.Λ (M - 1) + 4 * ocTauPP req.α req.q req.Λ (M - 1) ≤ a + req.T₀ ∧
      ∀ (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ),
        IsWeakSolutionOn (streamVel (D.Φ (M + req.Jw))) (D.κ M) a (a + req.T₀) f θ →
      ∃ (tq : ℕ → ℝ)
        (Ur : (i : ℕ) → ∀ v : CompIn (stage i).comps, ℝ → TorusHk req.Kw (ScalarH v.1.root))
        (Urw : (i : ℕ) → ∀ v : CompIn (stage i).comps, ℝ → TorusHk (req.Kw + 1) (ScalarH v.1.root))
        (Urk : (i : ℕ) → ∀ v u (_ : (stage i).fam.Γ v u), ℝ →
          TorusHk (req.Kw + (termD0bar req.NT req.pT (1 + req.Jw * req.Nw) (req.Jw * req.Rw)) - 1) (ScalarH u.1.root))
        (U₀ : ∀ v : CompIn Gw.comps, TorusHk req.Kw (ScalarH v.1.root))
        (U V : ∀ v : CompIn Gw.comps, ℝ → TorusHk req.Kw (ScalarH v.1.root))
        (Uw Vw : ∀ v : CompIn Gw.comps, ℝ → TorusHk (req.Kw + 1) (ScalarH v.1.root))
        (Uk Vk : ∀ v u (_ : Gw.fam.Γ v u), ℝ → TorusHk (req.Kw + (termD0bar req.NT req.pT (1 + req.Jw * req.Nw) (req.Jw * req.Rw)) - 1) (ScalarH u.1.root)),
        IsWeakReduction PW req.φ₀ req.hφ₀ req.nW M req.Jw req.Kw 0 a (a + req.T₀) θ stage tq Ur Urw Urk ∧
        tq (M + 1) = aM ∧ (U₀ = fun v => rerootFamily ιw (Ur M) v aM) ∧ U = rerootFamily ιw (Ur M) ∧
        IsWeakPaired PW req.φ₀ req.hφ₀ lawW M req.Kw req.Lt req.nW a req.T₀ req.σw (weakChi req.α req.q req.η₀) req.cK req.CK f Gw aM U₀ U V Uw Vw Uk Vk ∧
        IsWeakReadout lawW M req.Jw req.Lw req.Kw (D.κ M) a req.τ req.T₀ req.s req.Pw req.cK req.Cread req.Cid f θ Gw
          (fun t g x => W M t (fun v x' => g (ιw v) x') x) V ∧
        IsTerminalPrepBounds lawW M req.Kw (max req.Kout (max (2 * req.k₀ + 2) (req.NT + 2 * req.pT + req.k₀ + 2))) req.k₀ req.hk₀w (le_trans (by omega : req.k₀ ≤ 2 * req.k₀ + 2) (le_trans (le_max_left _ _) (le_max_right req.Kout _))) req.cr req.cK req.C req.QT f Gw aM tp Pterm V ∧
        ∃ Z : ∀ v : CompIn (Gt'.retained M 1 req.RT).comps, ℝ → TorusHk (max req.Kout (max (2 * req.k₀ + 2) (req.NT + 2 * req.pT + req.k₀ + 2))) (ScalarH v.1.root),
          TerminalFamilyClauses (termProvParams D req.Cw req.cr req.tT req.η₀ req.NT req.pT M)
            (fun _ => isoPairedKernel (D.termRW req.σw M) req.nW)
            (fun _ => isoPairedKernel (D.termRNew req.cr req.tT M) req.nT) req.φ₀ req.hφ₀ lawW lawT rootM M (max req.Kout (max (2 * req.k₀ + 2) (req.NT + 2 * req.pT + req.k₀ + 2))) req.cr req.C
            req.Centry tp (tp + D.termH M) (a + req.T₀) f Gw (Gt'.retained M 1 req.RT) seed ι
            (Pterm fun v => V v aM) Z ∧
          EntryIdentityClauses Gw (Gt'.retained M 1 req.RT) M req.pT (max req.Kout (max (2 * req.k₀ + 2) (req.NT + 2 * req.pT + req.k₀ + 2))) req.Kw req.Lw req.NT (req.Jw * req.Rw) req.sXT req.sZT req.η₀ tp a req.τ req.T₀ req.s
            req.Pw req.PT req.C req.cr f θ (fun t g x => W M t (fun v x' => g (ιw v) x') x) V Z

/-- Compose the datum-independent objects and then each datum's reductions and fields. -/
theorem terminal_tail_of_weak_tail (req : EntryCompositionData)
    (hweakM : WeakEntryTail req) (htermM : ConditionalTerminalTail req) : FullTerminalTail req := by
  obtain ⟨CHw, Υw, hCHw, hΥw, hw⟩ := hweakM
  obtain ⟨CHt, Υt, hCHt, hΥt, ht⟩ := htermM
  refine ⟨max CHw CHt, max Υw Υt, hCHw.trans (le_max_left _ _),
    hΥw.trans_le (le_max_left _ _), ?_⟩
  intro j₀ hcarrier
  have hA (k : ℕ) : 0 ≤ ocA req.α req.q req.Λ k := by
    unfold ocA
    apply Real.rpow_nonneg
    unfold ocEpsilon
    split <;> positivity
  have hT (k : ℕ) : 0 ≤ ocTauPP req.α req.q req.Λ k := by
    unfold ocTauPP
    positivity
  have hwcarrier := IsCarrierStart.mono hA hT (le_max_left CHw CHt) (le_max_left Υw Υt)
    ((show (0 : ℝ) ≤ 1 by norm_num).trans hCHw) hΥw.le hcarrier
  have htcarrier := IsCarrierStart.mono hA hT (le_max_right CHw CHt) (le_max_right Υw Υt)
    ((show (0 : ℝ) ≤ 1 by norm_num).trans hCHt) hΥt.le hcarrier
  obtain ⟨Mw, hweakdata⟩ := hw j₀ hwcarrier
  obtain ⟨Mt, htermdata⟩ := ht j₀ htcarrier
  refine ⟨max Mw Mt, ?_⟩
  intro M hM D hDα hDq hDΛ hDζ hstream hband hterm PW a
  have hDm : 1 + req.Jw * req.Nw ≤ termD0bar req.NT req.pT (1 + req.Jw * req.Nw) (req.Jw * req.Rw) :=
    (le_max_left _ _).trans (le_max_right _ _)
  obtain ⟨stage, Gw, rootM, rootR, ιw, aM, CcR, W,
    hconstruction, hencoding, hrootM, hrootR, hlifts, hchain, hweaklaw⟩ :=
    hweakdata M ((le_max_left Mw Mt).trans hM) D hDα hDq hDΛ hDζ hstream hband hterm
      _ hDm PW a
  let lawW : BirthLaw :=
    { cH := 1, cH_pos := zero_lt_one, wordCount := 1, wordCount_pos := Nat.zero_lt_one,
      etaB := req.η₀ / 2, eta0 := req.η₀, iota := 0, rootMass := rootM, rootMass_pos := hrootM,
      rootReadout := rootR, rootReadout_pos := hrootR }
  obtain ⟨hstage, hsolutions⟩ := hweaklaw lawW rfl rfl
  obtain ⟨tp, Pterm, lawT, Gt', seed, seedRootM, seedRootR, seedKc, ι,
    hprep, hlaw, hsucc, hseed, hclauses, hdeadline, hterminalsolutions⟩ :=
    htermdata M ((le_max_right Mw Mt).trans hM) D hDα hDq hDΛ hDζ hstream hband hterm
      a lawW PW Gw aM (fun t g x => W M t (fun v x' => g (ιw v) x') x) hstage
  refine ⟨stage, Gw, lawW, ιw, aM, CcR, W, hconstruction, hencoding, hlifts, hchain,
    hstage, tp, Pterm, lawT, Gt', seed, seedRootM, seedRootR, seedKc, ι,
    hprep, hlaw, hsucc, hseed, hclauses, hdeadline, ?_⟩
  intro f θ hθ
  obtain ⟨tq, Ur, Urw, Urk, U₀, U, V, Uw, Vw, Uk, Vk,
    hred, htq, hU₀, hU, hpaired, hreadout⟩ := hsolutions f θ hθ
  obtain ⟨hprepbounds, Z, hfamily, hidentity⟩ :=
    hterminalsolutions f θ U₀ U V Uw Vw Uk Vk hpaired hreadout
  exact ⟨tq, Ur, Urw, Urk, U₀, U, V, Uw, Vw, Uk, Vk,
    hred, htq, hU₀, hU, hpaired, hreadout, hprepbounds, Z, hfamily, hidentity⟩


/-- A fixed physical request, before choosing the terminal reserve plan. -/
structure EntryRequestData where
  α : ℝ
  s : ℝ
  q : ℝ
  Λ : ℕ
  ζ : ℝ → ℝ
  φ₀ : Vec 2 → ℝ
  hφ₀ : Integrable φ₀
  bw : ℝ
  Jw : ℕ
  Nw : ℕ
  Rw : ℕ
  Lw : ℕ
  τ : ℝ
  T₀ : ℝ
  Pw : ℝ
  η₀ : ℝ
  σw : ℝ
  NT : ℕ
  pT : ℕ
  RT : ℕ
  k₀ : ℕ
  tT : ℝ
  QT : ℝ
  τe : ℝ
  H : ℕ
  J : ℕ
  N : ℕ
  p : ℕ
  Kout : ℕ
  nT : ℕ+
  PT : ℝ
  AT : ℕ
  LcT : ℕ
  LoT : ℕ
  LfT : ℕ
  LpT : ℕ
  lamE : ℝ
  Kres : ℕ
  Lpr : ℕ
  Lc : ℕ
  Lf : ℕ
  c₀max : ℝ
  L₀ : ℕ
  SXw : ℕ
  SZw : ℕ

/-- Weak entry supplies constants and a construction at each reserve request. -/
def WeakEntryRequest (req : EntryRequestData) : Prop :=
    ∀ (L Kw sX sZ : ℕ) (nW : ℕ+) (kReq : InvConsts), 1 ≤ kReq.G0 → req.L₀ ≤ L → req.SXw ≤ sX →
      req.SZw ≤ sZ → L + 1 ≤ 2 * (nW : ℕ) → req.Lw + 5 ≤ Kw →
    ∃ (cK CK CL Cχ Cread Cid : ℝ) (kW : InvConsts),
      0 < cK ∧ kW.c₀ = cK ∧ IsWeakAllocation kW kReq L ∧
    ∃ (CHw Υw : ℝ), 1 ≤ CHw ∧ 0 < Υw ∧
    ∀ j₀ : ℕ, IsCarrierStart req.α req.q req.Λ req.bw CHw Υw j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = req.α → D.q = req.q → D.Λ = req.Λ → D.ζ = req.ζ → IsOCStreamSeq req.α req.q req.Λ req.ζ D.Φ →
      IsOCBandChain req.α req.q req.Λ req.ζ M D.κ → D.term = M →
    ∀ (Dm : ℕ), 1 + req.Jw * req.Nw ≤ Dm →
    ∀ (P : ProvParams) (a : ℝ),
    ∃ (stage : ℕ → GenStage D ScalarH Dm req.bw j₀) (Gw : GenStage D ScalarH Dm req.bw j₀) (rootM rootR : ℕ → ℝ)
      (ι : CompIn (stage M).comps ≃ CompIn Gw.comps) (aM : ℝ)
      (CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root))
      (W : (i : ℕ) → ℝ → (CompIn (stage i).comps → Vec 2 → ℝ) → Vec 2 → ℝ),
      IsWeakConstruction D P (⟨req.Nw, req.Rw, sX, sZ, req.η₀, M + req.Jw⟩ : WeakMenu) M req.Jw (D.termRW req.σw M) 0 stage ∧
      IsWeakEncoding req.Nw req.Jw req.η₀ rootM rootR (stage M) Gw ι ∧
      (∀ r, 0 < rootM r) ∧ (∀ r, 0 < rootR r) ∧
      (∀ i, M < i → i ≤ M + req.Jw → IsWeakReadoutLifts i req.Nw (req.Jw * req.Rw) sX sZ (stage i) (CcR i)) ∧
      IsWeakReadoutChain M req.Jw req.Nw 0 req.η₀ (fun _ => (req.Jw * req.Rw)) stage CcR W ∧
      ∀ law : BirthLaw, law.rootMass = rootM → law.rootReadout = rootR →
        IsWeakStage law P req.φ₀ req.hφ₀ M (M + req.Jw) req.Jw (req.Jw * req.Rw) (1 + req.Jw * req.Nw) nW kW a req.T₀ req.σw CL Cχ (weakChi req.α req.q req.η₀)
          Gw aM ∧
        ∀ (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ),
          IsWeakSolutionOn (streamVel (D.Φ (M + req.Jw))) (D.κ M) a (a + req.T₀) f θ →
        ∃ (tq : ℕ → ℝ)
          (Ur : (i : ℕ) → ∀ v : CompIn (stage i).comps, ℝ → TorusHk Kw (ScalarH v.1.root))
          (Urw : (i : ℕ) → ∀ v : CompIn (stage i).comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
          (Urk : (i : ℕ) → ∀ v u (_ : (stage i).fam.Γ v u), ℝ → TorusHk (Kw + Dm - 1) (ScalarH u.1.root))
          (U₀ : ∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root))
          (U V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root))
          (Uw Vw : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
          (Uk Vk : ∀ v u (_ : Gw.fam.Γ v u), ℝ → TorusHk (Kw + Dm - 1) (ScalarH u.1.root)),
          IsWeakReduction P req.φ₀ req.hφ₀ nW M req.Jw Kw 0 a (a + req.T₀) θ stage tq Ur Urw Urk ∧
          tq (M + 1) = aM ∧ (U₀ = fun v => rerootFamily ι (Ur M) v aM) ∧ U = rerootFamily ι (Ur M) ∧
          IsWeakPaired P req.φ₀ req.hφ₀ law M Kw L nW a req.T₀ req.σw (weakChi req.α req.q req.η₀) cK CK f Gw aM
            U₀ U V Uw Vw Uk Vk ∧
          IsWeakReadout law M req.Jw req.Lw Kw (D.κ M) a req.τ req.T₀ req.s req.Pw cK Cread Cid f θ Gw
            (fun t g x => W M t (fun v x' => g (ι v) x') x) V

/-- The conditional terminal statement supplies a plan followed by its universal weak constants. -/
def ConditionalTerminalPlan (req : EntryRequestData) : Prop :=
    ∃ SX SZ : ℕ, ∀ sXT sZT : ℕ, SX ≤ sXT → SZ ≤ sZT →
    ∃ (Kw Lt : ℕ) (nW : ℕ+) (hk₀w : req.k₀ ≤ Kw) (hLw : req.Lw + 5 ≤ Kw) (cr : ℝ) (kS : InvConsts),
      req.L₀ ≤ Lt ∧ req.LpT ≤ Lt ∧ Lt + 1 ≤ 2 * (nW : ℕ) ∧ IsTerminalKernelOrders nW req.LoT req.LfT req.LpT req.Lpr req.Lc req.Lf ∧
      0 < cr ∧ kS.cr = cr ∧ 0 < kS.c₀ ∧ kS.c₀ ≤ req.c₀max ∧ kS.cr ≤ 1 ∧
      kS.σf = ocDelta req.α req.q ∧ kS.lamC = req.lamE ∧
      IsSeedAllocation kS (termR0bar req.RT (req.Jw * req.Rw)) (termD0bar req.NT req.pT (1 + req.Jw * req.Nw) (req.Jw * req.Rw)) req.H req.J req.N req.p req.Kres req.Lpr req.Lc req.Lf ∧
      (kS.mEnv = 0 ∧ kS.Kan = kS.Ks ∧ kS.Lan = kS.Ks ∧ kS.Jm = kS.Ks) ∧
      Lt + (1 + req.Jw * req.Nw) + max (req.Lw + 5) req.k₀ ≤ Kw ∧
      cr = 1 ∧
    ∀ (cK CK CL Cχ Cread Cid : ℝ) (kW : InvConsts), 0 < cK → kW.c₀ = cK →
      IsWeakAllocation kW kS Lt →
    ∃ (c C Centry cH Ce Cw : ℝ), 0 < c ∧ 0 < cH ∧ 1 ≤ Ce ∧
    ∃ (CHt Υt : ℝ), 1 ≤ CHt ∧ 0 < Υt ∧
    ∀ j₀ : ℕ, IsCarrierStart req.α req.q req.Λ req.bw CHt Υt j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = req.α → D.q = req.q → D.Λ = req.Λ → D.ζ = req.ζ → IsOCStreamSeq req.α req.q req.Λ req.ζ D.Φ →
      IsOCBandChain req.α req.q req.Λ req.ζ M D.κ → D.term = M →
    ∀ (a : ℝ) (lawW : BirthLaw) (PW : ProvParams)
      (Gw : GenStage D ScalarH (termD0bar req.NT req.pT (1 + req.Jw * req.Nw) (req.Jw * req.Rw)) req.bw j₀) (aM : ℝ)
      (Ww : ℝ → (CompIn Gw.comps → Vec 2 → ℝ) → Vec 2 → ℝ),
      IsWeakStage lawW PW req.φ₀ req.hφ₀ M (M + req.Jw) req.Jw (req.Jw * req.Rw) (1 + req.Jw * req.Nw) nW kW a req.T₀ req.σw CL Cχ (weakChi req.α req.q req.η₀) Gw aM →
    ∃ (tp : ℝ) (Pterm : (∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn Gw.comps, TorusHk (max req.Kout (max (2 * req.k₀ + 2) (req.NT + 2 * req.pT + req.k₀ + 2))) (ScalarH v.1.root)))
      (lawT : BirthLaw) (Gt' : GenStage D ScalarH (termD0bar req.NT req.pT (1 + req.Jw * req.Nw) (req.Jw * req.Rw)) req.bw j₀) (seed : GenStage D ScalarH (succSchedD (termD0bar req.NT req.pT (1 + req.Jw * req.Nw) (req.Jw * req.Rw)) req.N req.p (req.H + 1)) req.bw j₀)
      (rootM rootR : ℕ → ℝ) (seedKc : ℕ → KernelSpec)
      (ι : CompIn (Gt'.retained M 1 req.RT).comps ≃ CompIn seed.comps),
      IsTerminalPrepMap M Kw (max req.Kout (max (2 * req.k₀ + 2) (req.NT + 2 * req.pT + req.k₀ + 2))) c C Gw aM tp Pterm ∧
      IsTerminalLaw lawW lawT cH req.η₀ (wordsUpTo (termAlphabet req.NT req.pT (1 + req.Jw * req.Nw) (req.Jw * req.Rw)) req.RT).card ∧
      IsActualSuccessor D (termProvParams D Cw cr req.tT req.η₀ req.NT req.pT M)
        (termMenu (M + req.Jw) (termAlphabet req.NT req.pT (1 + req.Jw * req.Nw) (req.Jw * req.Rw)) req.RT req.NT req.pT sXT sZT req.η₀ tp cr) Gw Gt' ∧
      IsSeedEncoding (termProvParams D Cw cr req.tT req.η₀ req.NT req.pT M) lawT rootM rootR
        (fun _ => isoPairedKernel (D.termRW req.σw M) nW) (fun _ => isoPairedKernel (D.termRNew cr req.tT M) req.nT)
        seedKc (Gt'.retained M 1 req.RT) seed ι ∧
      TerminalSeedClauses rootM rootR seedKc req.φ₀ req.hφ₀ (M + req.Jw) (M - 1) kS Ce req.τe (termR0bar req.RT (req.Jw * req.Rw)) (termD0bar req.NT req.pT (1 + req.Jw * req.Nw) (req.Jw * req.Rw)) seed
        (tp + D.termH M) (a + req.T₀) ∧
      tp + D.termH M + 3 * ocTau req.α req.q req.Λ (M - 1) + 4 * ocTauPP req.α req.q req.Λ (M - 1) ≤ a + req.T₀ ∧
      ∀ (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ)
        (U₀ : ∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root))
        (U V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root))
        (Uw Vw : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
        (Uk Vk : ∀ v u (_ : Gw.fam.Γ v u), ℝ → TorusHk (Kw + (termD0bar req.NT req.pT (1 + req.Jw * req.Nw) (req.Jw * req.Rw)) - 1) (ScalarH u.1.root)),
        IsWeakPaired PW req.φ₀ req.hφ₀ lawW M Kw Lt nW a req.T₀ req.σw (weakChi req.α req.q req.η₀) cK CK f Gw aM U₀ U V Uw Vw Uk Vk →
        IsWeakReadout lawW M req.Jw req.Lw Kw (D.κ M) a req.τ req.T₀ req.s req.Pw cK Cread Cid f θ Gw Ww V →
        IsTerminalPrepBounds lawW M Kw (max req.Kout (max (2 * req.k₀ + 2) (req.NT + 2 * req.pT + req.k₀ + 2))) req.k₀ hk₀w (le_trans (by omega : req.k₀ ≤ 2 * req.k₀ + 2) (le_trans (le_max_left _ _) (le_max_right req.Kout _))) cr cK C req.QT f Gw aM tp Pterm V ∧
        ∃ Z : ∀ v : CompIn (Gt'.retained M 1 req.RT).comps, ℝ → TorusHk (max req.Kout (max (2 * req.k₀ + 2) (req.NT + 2 * req.pT + req.k₀ + 2))) (ScalarH v.1.root),
          TerminalFamilyClauses (termProvParams D Cw cr req.tT req.η₀ req.NT req.pT M)
            (fun _ => isoPairedKernel (D.termRW req.σw M) nW)
            (fun _ => isoPairedKernel (D.termRNew cr req.tT M) req.nT) req.φ₀ req.hφ₀ lawW lawT rootM M (max req.Kout (max (2 * req.k₀ + 2) (req.NT + 2 * req.pT + req.k₀ + 2))) cr C
            Centry tp (tp + D.termH M) (a + req.T₀) f Gw (Gt'.retained M 1 req.RT) seed ι
            (Pterm fun v => V v aM) Z ∧
          EntryIdentityClauses Gw (Gt'.retained M 1 req.RT) M req.pT (max req.Kout (max (2 * req.k₀ + 2) (req.NT + 2 * req.pT + req.k₀ + 2))) Kw req.Lw req.NT (req.Jw * req.Rw) sXT sZT req.η₀ tp a req.τ req.T₀ req.s
            req.Pw req.PT C cr f θ Ww V Z

/-- The full terminal statement below the physical orders. -/
def FullTerminalPlan (req : EntryRequestData) : Prop :=
    ∃ SX SZ : ℕ, ∀ sXT sZT : ℕ, SX ≤ sXT → SZ ≤ sZT →
    ∃ (Kw Lt : ℕ) (nW : ℕ+) (hk₀w : req.k₀ ≤ Kw) (hLw : req.Lw + 5 ≤ Kw) (cr : ℝ) (kS : InvConsts),
      req.LpT ≤ Lt ∧ Lt + 1 ≤ 2 * (nW : ℕ) ∧ IsTerminalKernelOrders nW req.LoT req.LfT req.LpT req.Lpr req.Lc req.Lf ∧
      0 < cr ∧ kS.cr = cr ∧ 0 < kS.c₀ ∧ kS.c₀ ≤ req.c₀max ∧ kS.cr ≤ 1 ∧
      kS.σf = ocDelta req.α req.q ∧ kS.lamC = req.lamE ∧
      IsSeedAllocation kS (termR0bar req.RT (req.Jw * req.Rw)) (termD0bar req.NT req.pT (1 + req.Jw * req.Nw) (req.Jw * req.Rw)) req.H req.J req.N req.p req.Kres req.Lpr req.Lc req.Lf ∧
      (kS.mEnv = 0 ∧ kS.Kan = kS.Ks ∧ kS.Lan = kS.Ks ∧ kS.Jm = kS.Ks) ∧
      Lt + (1 + req.Jw * req.Nw) + max (req.Lw + 5) req.k₀ ≤ Kw ∧
      cr = 1 ∧
    ∃ (cK CK CL Cχ Cread Cid : ℝ) (kW : InvConsts),
      0 < cK ∧ kW.c₀ = cK ∧ IsWeakAllocation kW kS Lt ∧
    ∃ (c C Centry cH Ce Cw : ℝ), 0 < c ∧ 0 < cH ∧ 1 ≤ Ce ∧
    ∃ (CHt Υt : ℝ), 1 ≤ CHt ∧ 0 < Υt ∧
    ∀ j₀ : ℕ, IsCarrierStart req.α req.q req.Λ req.bw CHt Υt j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = req.α → D.q = req.q → D.Λ = req.Λ → D.ζ = req.ζ → IsOCStreamSeq req.α req.q req.Λ req.ζ D.Φ →
      IsOCBandChain req.α req.q req.Λ req.ζ M D.κ → D.term = M →
    ∀ (PW : ProvParams) (a : ℝ),
    ∃ (stage : ℕ → GenStage D ScalarH (termD0bar req.NT req.pT (1 + req.Jw * req.Nw) (req.Jw * req.Rw)) req.bw j₀) (Gw : GenStage D ScalarH (termD0bar req.NT req.pT (1 + req.Jw * req.Nw) (req.Jw * req.Rw)) req.bw j₀) (lawW : BirthLaw)
      (ιw : CompIn (stage M).comps ≃ CompIn Gw.comps) (aM : ℝ)
      (CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root))
      (W : (i : ℕ) → ℝ → (CompIn (stage i).comps → Vec 2 → ℝ) → Vec 2 → ℝ),
      IsWeakConstruction D PW (⟨req.Nw, req.Rw, sXT, sZT, req.η₀, M + req.Jw⟩ : WeakMenu) M req.Jw (D.termRW req.σw M) 0 stage ∧
      IsWeakEncoding req.Nw req.Jw req.η₀ lawW.rootMass lawW.rootReadout (stage M) Gw ιw ∧
      (∀ i, M < i → i ≤ M + req.Jw → IsWeakReadoutLifts i req.Nw (req.Jw * req.Rw) sXT sZT (stage i) (CcR i)) ∧
      IsWeakReadoutChain M req.Jw req.Nw 0 req.η₀ (fun _ => (req.Jw * req.Rw)) stage CcR W ∧
      IsWeakStage lawW PW req.φ₀ req.hφ₀ M (M + req.Jw) req.Jw (req.Jw * req.Rw) (1 + req.Jw * req.Nw) nW kW a req.T₀ req.σw CL Cχ (weakChi req.α req.q req.η₀) Gw aM ∧
    ∃ (tp : ℝ) (Pterm : (∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn Gw.comps, TorusHk (max req.Kout (max (2 * req.k₀ + 2) (req.NT + 2 * req.pT + req.k₀ + 2))) (ScalarH v.1.root)))
      (lawT : BirthLaw) (Gt' : GenStage D ScalarH (termD0bar req.NT req.pT (1 + req.Jw * req.Nw) (req.Jw * req.Rw)) req.bw j₀)
      (seed : GenStage D ScalarH (succSchedD (termD0bar req.NT req.pT (1 + req.Jw * req.Nw) (req.Jw * req.Rw)) req.N req.p (req.H + 1)) req.bw j₀)
      (rootM rootR : ℕ → ℝ) (seedKc : ℕ → KernelSpec)
      (ι : CompIn (Gt'.retained M 1 req.RT).comps ≃ CompIn seed.comps),
      IsTerminalPrepMap M Kw (max req.Kout (max (2 * req.k₀ + 2) (req.NT + 2 * req.pT + req.k₀ + 2))) c C Gw aM tp Pterm ∧
      IsTerminalLaw lawW lawT cH req.η₀ (wordsUpTo (termAlphabet req.NT req.pT (1 + req.Jw * req.Nw) (req.Jw * req.Rw)) req.RT).card ∧
      IsActualSuccessor D (termProvParams D Cw cr req.tT req.η₀ req.NT req.pT M) (termMenu (M + req.Jw) (termAlphabet req.NT req.pT (1 + req.Jw * req.Nw) (req.Jw * req.Rw)) req.RT req.NT req.pT sXT sZT req.η₀ tp cr) Gw Gt' ∧
      IsSeedEncoding (termProvParams D Cw cr req.tT req.η₀ req.NT req.pT M) lawT rootM rootR
        (fun _ => isoPairedKernel (D.termRW req.σw M) nW) (fun _ => isoPairedKernel (D.termRNew cr req.tT M) req.nT)
        seedKc (Gt'.retained M 1 req.RT) seed ι ∧
      TerminalSeedClauses rootM rootR seedKc req.φ₀ req.hφ₀ (M + req.Jw) (M - 1) kS Ce req.τe (termR0bar req.RT (req.Jw * req.Rw)) (termD0bar req.NT req.pT (1 + req.Jw * req.Nw) (req.Jw * req.Rw)) seed
        (tp + D.termH M) (a + req.T₀) ∧
      tp + D.termH M + 3 * ocTau req.α req.q req.Λ (M - 1) + 4 * ocTauPP req.α req.q req.Λ (M - 1) ≤ a + req.T₀ ∧
      ∀ (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ),
        IsWeakSolutionOn (streamVel (D.Φ (M + req.Jw))) (D.κ M) a (a + req.T₀) f θ →
      ∃ (tq : ℕ → ℝ)
        (Ur : (i : ℕ) → ∀ v : CompIn (stage i).comps, ℝ → TorusHk Kw (ScalarH v.1.root))
        (Urw : (i : ℕ) → ∀ v : CompIn (stage i).comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
        (Urk : (i : ℕ) → ∀ v u (_ : (stage i).fam.Γ v u), ℝ →
          TorusHk (Kw + (termD0bar req.NT req.pT (1 + req.Jw * req.Nw) (req.Jw * req.Rw)) - 1) (ScalarH u.1.root))
        (U₀ : ∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root))
        (U V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root))
        (Uw Vw : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
        (Uk Vk : ∀ v u (_ : Gw.fam.Γ v u), ℝ → TorusHk (Kw + (termD0bar req.NT req.pT (1 + req.Jw * req.Nw) (req.Jw * req.Rw)) - 1) (ScalarH u.1.root)),
        IsWeakReduction PW req.φ₀ req.hφ₀ nW M req.Jw Kw 0 a (a + req.T₀) θ stage tq Ur Urw Urk ∧
        tq (M + 1) = aM ∧ (U₀ = fun v => rerootFamily ιw (Ur M) v aM) ∧ U = rerootFamily ιw (Ur M) ∧
        IsWeakPaired PW req.φ₀ req.hφ₀ lawW M Kw Lt nW a req.T₀ req.σw (weakChi req.α req.q req.η₀) cK CK f Gw aM U₀ U V Uw Vw Uk Vk ∧
        IsWeakReadout lawW M req.Jw req.Lw Kw (D.κ M) a req.τ req.T₀ req.s req.Pw cK Cread Cid f θ Gw
          (fun t g x => W M t (fun v x' => g (ιw v) x') x) V ∧
        IsTerminalPrepBounds lawW M Kw (max req.Kout (max (2 * req.k₀ + 2) (req.NT + 2 * req.pT + req.k₀ + 2))) req.k₀ hk₀w (le_trans (by omega : req.k₀ ≤ 2 * req.k₀ + 2) (le_trans (le_max_left _ _) (le_max_right req.Kout _))) cr cK C req.QT f Gw aM tp Pterm V ∧
        ∃ Z : ∀ v : CompIn (Gt'.retained M 1 req.RT).comps, ℝ → TorusHk (max req.Kout (max (2 * req.k₀ + 2) (req.NT + 2 * req.pT + req.k₀ + 2))) (ScalarH v.1.root),
          TerminalFamilyClauses (termProvParams D Cw cr req.tT req.η₀ req.NT req.pT M)
            (fun _ => isoPairedKernel (D.termRW req.σw M) nW)
            (fun _ => isoPairedKernel (D.termRNew cr req.tT M) req.nT) req.φ₀ req.hφ₀ lawW lawT rootM M (max req.Kout (max (2 * req.k₀ + 2) (req.NT + 2 * req.pT + req.k₀ + 2))) cr C
            Centry tp (tp + D.termH M) (a + req.T₀) f Gw (Gt'.retained M 1 req.RT) seed ι
            (Pterm fun v => V v aM) Z ∧
          EntryIdentityClauses Gw (Gt'.retained M 1 req.RT) M req.pT (max req.Kout (max (2 * req.k₀ + 2) (req.NT + 2 * req.pT + req.k₀ + 2))) Kw req.Lw req.NT (req.Jw * req.Rw) sXT sZT req.η₀ tp a req.τ req.T₀ req.s
            req.Pw req.PT C cr f θ (fun t g x => W M t (fun v x' => g (ιw v) x') x) V Z

/-- The seed allocation forces a positive producer offset: at grade `0` its depth schedule
starts at `r₀ ≥ 1`, which the schedule from `0` reaches only at grade `G0 ≥ 1`. -/
theorem one_le_G0_of_seedAllocation {kS : InvConsts} {r₀ D₀ H J N p Kres Lpr Lc Lf : ℕ}
    (h : IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf) (hr : 1 ≤ r₀) : 1 ≤ kS.G0 := by
  by_contra hG
  have hG0 : kS.G0 = 0 := by omega
  have h7 := h.2.2.2.2.2.2.1 0
  rw [hG0] at h7
  simp only [succSchedR] at h7
  omega

/-- Choose weak constants at the terminal reserve plan before composing the level tails. -/
theorem terminal_plan_of_weak_request (req : EntryRequestData)
    (hwreq : WeakEntryRequest req) (hterminalplan : ConditionalTerminalPlan req) :
    FullTerminalPlan req := by
  obtain ⟨SX, SZ, hplan⟩ := hterminalplan
  refine ⟨max SX req.SXw, max SZ req.SZw, ?_⟩
  intro sXT sZT hsX hsZ
  obtain ⟨Kw, Lt, nW, hk₀w, hLwKw, cr, kS, hL₀, hLp, hLt, horders,
    hcr, hkcr, hkc₀, hkc₀max, hkcr1, hσf, hlam, hseedalloc, hplanS, hfloor, hcrone, htweak⟩ :=
      hplan sXT sZT (le_of_max_le_left hsX) (le_of_max_le_left hsZ)
  have hG0 : 1 ≤ kS.G0 := one_le_G0_of_seedAllocation hseedalloc (le_max_left 2 _ |>.trans' (by omega))
  obtain ⟨cK, CK, CL, Cχ, Cread, Cid, kW, hcK, hkcK, hweakalloc, hweakM⟩ :=
    hwreq Lt Kw sXT sZT nW kS hG0 hL₀ (le_of_max_le_right hsX) (le_of_max_le_right hsZ) hLt hLwKw
  obtain ⟨c, C, Centry, cH, Ce, Cw, hc, hcH, hCe, htermM⟩ :=
    htweak cK CK CL Cχ Cread Cid kW hcK hkcK hweakalloc
  refine ⟨Kw, Lt, nW, hk₀w, hLwKw, cr, kS, hLp, hLt, horders, hcr, hkcr,
    hkc₀, hkc₀max, hkcr1, hσf, hlam, hseedalloc, hplanS, hfloor, hcrone,
    cK, CK, CL, Cχ, Cread, Cid, kW, hcK, hkcK, hweakalloc,
    c, C, Centry, cH, Ce, Cw, hc, hcH, hCe, ?_⟩
  let u : EntryCompositionData :=
    { α := req.α, s := req.s, q := req.q, Λ := req.Λ, ζ := req.ζ, φ₀ := req.φ₀, hφ₀ := req.hφ₀, bw := req.bw,
      Jw := req.Jw, Nw := req.Nw, Rw := req.Rw, Lw := req.Lw, τ := req.τ, T₀ := req.T₀, Pw := req.Pw, η₀ := req.η₀,
      σw := req.σw, NT := req.NT, pT := req.pT, RT := req.RT, k₀ := req.k₀, sXT := sXT, sZT := sZT,
      tT := req.tT, QT := req.QT, τe := req.τe, H := req.H, J := req.J, N := req.N, p := req.p, Kout := req.Kout,
      Kw := Kw, Lt := Lt, nW := nW, hk₀w := hk₀w, cr := cr, kS := kS,
      cK := cK, CK := CK, CL := CL, Cχ := Cχ, Cread := Cread, Cid := Cid, kW := kW,
      c := c, C := C, Centry := Centry, cH := cH, Ce := Ce, Cw := Cw, nT := req.nT, PT := req.PT }
  have hw : WeakEntryTail u := by
    dsimp only [WeakEntryTail, u]
    exact hweakM
  have ht : ConditionalTerminalTail u := by
    dsimp only [ConditionalTerminalTail, u]
    exact htermM
  have hout := terminal_tail_of_weak_tail u hw ht
  simpa only [FullTerminalTail, u] using hout


/-- The exact full terminal entry, conditional on the two existing entry statements. -/
theorem entry_terminal_of_ingredients (hweak : EntryWeakStatement)
    (hterminal : EntryTerminalOfWeakStatement) : EntryTerminalStatement := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λw, hΛw, hw⟩ := hweak α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λt, hΛt, ht⟩ := hterminal α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨max Λw Λt, le_trans hΛw (le_max_left _ _), ?_⟩
  intro Λ hΛ c₀max hc₀ φ₀ hφ₀ hφsmooth hφnonneg hφmass hφsupport bw hbw hbwsmall
    Jw τ T₀ Pw η₀ hJw hτ hτT hPw hη hηsmall
  have hwΛ := hw Λ ((le_max_left Λw Λt).trans hΛ) φ₀ hφ₀ hφsmooth hφnonneg hφmass
    hφsupport bw hbw hbwsmall Jw τ T₀ Pw η₀ hJw hτ hτT hPw hη hηsmall
  obtain ⟨Nw, Rw, Lw, hNw, hLw, hoN, hoR, hwσ⟩ := hwΛ
  refine ⟨Nw, Rw, Lw, hNw, hLw, hoN, hoR, ?_⟩
  intro σw hσw hσwupper PT hPT NT pT RT AT k₀ LcT LoT LfT LpT tT QT hsched
    τe lamE hexp σ₀ H J N p Kres Lpr Lc Lf nT hnT Kout
  obtain ⟨L₀, SXw, SZw, hwreq⟩ := hwσ σw hσw hσwupper
  have hχ : 0 < weakChi α q η₀ := weakChi_pos hα₀ hq.1 hq.2.1 hηsmall
  let req : EntryRequestData :=
    { α := α, s := s, q := q, Λ := Λ, ζ := ζ, φ₀ := φ₀, hφ₀ := hφ₀, bw := bw, Jw := Jw, Nw := Nw, Rw := Rw, Lw := Lw, τ := τ, T₀ := T₀, Pw := Pw, η₀ := η₀, σw := σw, NT := NT, pT := pT, RT := RT, k₀ := k₀, tT := tT, QT := QT, τe := τe, H := H, J := J, N := N, p := p, Kout := Kout, nT := nT, PT := PT, AT := AT, LcT := LcT, LoT := LoT, LfT := LfT, LpT := LpT, lamE := lamE, Kres := Kres, Lpr := Lpr, Lc := Lc, Lf := Lf, c₀max := c₀max, L₀ := L₀, SXw := SXw, SZw := SZw }
  have hplan := ht Λ ((le_max_right Λw Λt).trans hΛ) c₀max hc₀
    φ₀ hφ₀ hφsmooth hφnonneg hφmass hφsupport bw hbw hbwsmall
    Jw Lw (Jw * Rw) (1 + Jw * Nw) L₀ τ T₀ Pw σw (weakChi α q η₀) η₀
    hJw (Nat.le_add_right 1 _) hτ hτT hPw hσw hσwupper hχ hη hηsmall PT hPT
    NT pT RT AT k₀ LcT LoT LfT LpT tT QT hsched τe lamE hexp
    σ₀ H J N p Kres Lpr Lc Lf nT hnT Kout
  have hwrequest : WeakEntryRequest req := by
    dsimp only [WeakEntryRequest, req]
    exact hwreq
  have htplan : ConditionalTerminalPlan req := by
    dsimp only [ConditionalTerminalPlan, req]
    exact hplan
  have hout := terminal_plan_of_weak_request req hwrequest htplan
  simpa only [FullTerminalPlan, req] using hout

end AVRegularity.EntryTerminal.Assembly
end
