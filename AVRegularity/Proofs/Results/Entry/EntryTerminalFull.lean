-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.EntryTerminal.Assembly.Route.EntryTerminalOfNative
import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.GluedClosed
public import AVRegularity.Definitions.EntryWeak.WeakReduction
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain

/-! Proof of `entry_terminal` (a full seed for preservation).

`entry_terminal` is `entryTerminal_of_native` (module
`EntryTerminal.Assembly.Route.EntryTerminalOfNative`: `entry_weak` and
`entry_terminal_of_ingredients` with `entry_terminal_of_weak` from the native leaf) at
`nativeTemporalRepresentatives`. The text is the statement's, verbatim. -/

@[expose] public section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance

namespace AVRegularity.Providers

/-- **A full seed for preservation**. -/
theorem entry_terminal (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
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
    ∀ (_σ₀ : ℝ) (H J N p Kres Lpr Lc Lf : ℕ) (nT : ℕ+), IsFreshKernelOrder nT LcT Lpr Lc Lf →
    ∀ Kout : ℕ,
    ∃ SX SZ : ℕ, ∀ sXT sZT : ℕ, SX ≤ sXT → SZ ≤ sZT →
    ∃ (Kw Lt : ℕ) (nW : ℕ+) (hk₀w : k₀ ≤ Kw) (_hLw : Lw + 5 ≤ Kw) (cr : ℝ) (kS : InvConsts),
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
            Pw PT C cr f θ (fun t g x => W M t (fun v x' => g (ιw v) x') x) V Z :=
  by
  -- Elaborated without the expected type, then compared once (as for the error energy bound).
  have h := EntryTerminal.Route.entryTerminal_of_native
    Construction.Preservation.Residual.CovarianceTransport.nativeTemporalRepresentatives
    α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  exact h

end AVRegularity.Providers
