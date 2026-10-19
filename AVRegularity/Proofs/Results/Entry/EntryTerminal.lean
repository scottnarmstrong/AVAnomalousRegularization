-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.EntryTerminal.Assembly.Route.EntryTerminalOfNative
import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.GluedClosed
import AVRegularity.EntryTerminal.Ingredients.ErrorEnergy.ResidualFromNative
public import AVRegularity.Definitions.Entry.TerminalResidualClauses
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain
import AVRegularity.EntryTerminal.Assembly.Prep.Closed

@[expose] public section
section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Providers

/-! Proof of `entry_terminal_error_energy` (the error energy of the terminal entry).

`entry_terminal_error_energy` is `errorEnergyStatement_of_native` (the unbundling of
`errorEnergyBundled_of_native`, module `EntryTerminal.Assembly.Route.EntryTerminalOfNative`) at
`nativeTemporalRepresentatives` (the word operators). The text is the statement's, verbatim. -/

/-- **The whole-window terminal error energy**. Proposition 14.10(c) of the paper follows from
    it. -/
theorem entry_terminal_error_energy (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
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
    ∀ (_σ₀ : ℝ) (H _J N p _Kres Lpr Lc Lf : ℕ) (nT : ℕ+), IsFreshKernelOrder nT LcT Lpr Lc Lf →
    ∃ (SX SZ Kfloor : ℕ),
    ∀ sXT sZT : ℕ, SX ≤ sXT → SZ ≤ sZT →
    ∀ Kout : ℕ, Kfloor ≤ Kout →
    ∃ Kneed : ℕ,
    ∀ (Kw Lt : ℕ) (nW : ℕ+) (hk₀w : k₀ ≤ Kw) (_hLw : Lw + 5 ≤ Kw) (cr : ℝ) (kS : InvConsts),
      Kneed ≤ Kw →
      L0w ≤ Lt → LpT ≤ Lt → Lt + 1 ≤ 2 * (nW : ℕ) → IsTerminalKernelOrders nW LoT LfT LpT Lpr Lc Lf →
      0 < cr → cr ≤ 1 → cr = 1 → kS.cr = cr → 0 < kS.c₀ →
      Kneed ≤ kS.Ks → Kneed ≤ kS.Kan → Kneed ≤ kS.Lan → Kneed ≤ kS.Jm →
    ∀ (cK CK CL Cχ Cread Cid : ℝ) (kW : InvConsts), 0 < cK → kW.c₀ = cK →
      IsWeakAllocation kW kS Lt → kW.G0 ≤ kW.Hprod →
      NT + DW + dW * (termD0bar NT pT DW dW + 1) ≤ kW.Lstar →
    ∀ (cP CP cHP : ℝ), 0 < cP → cHP ≤ 1 → ∃ Cw₀ : ℝ, ∀ (Cw Ce : ℝ) (cker : ℕ → ℝ), Cw₀ ≤ Cw →
    ∃ C : ℝ,
    ∃ (CHt Υt : ℝ), 1 ≤ CHt ∧ 0 < Υt ∧
    ∀ j₀ : ℕ, IsCarrierStart α q Λ bw CHt Υt j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ M D.κ → D.term = M →
    ∀ (a : ℝ) (lawW : BirthLaw) (PW : ProvParams)
      (Gw : GenStage D ScalarH (termD0bar NT pT DW dW) bw j₀) (aM : ℝ)
      (Ww : ℝ → (CompIn Gw.comps → Vec 2 → ℝ) → Vec 2 → ℝ),
      IsWeakStage lawW PW φ₀ hφ₀ M (M + Jw) Jw dW DW nW kW a T₀ σw CL Cχ χw Gw aM →
    ∀ (tp : ℝ) (Pterm : (∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn Gw.comps, TorusHk (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) (ScalarH v.1.root)))
      (lawT : BirthLaw) (Gt' : GenStage D ScalarH (termD0bar NT pT DW dW) bw j₀),
      IsTerminalPrepMap M Kw (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) cP CP Gw aM tp Pterm →
      IsTerminalLaw lawW lawT cHP η₀ (wordsUpTo (termAlphabet NT pT DW dW) RT).card →
      IsActualSuccessor D (termProvParams D Cw cr tT η₀ NT pT M)
        (termMenu (M + Jw) (termAlphabet NT pT DW dW) RT NT pT sXT sZT η₀ tp cr) Gw Gt' →
      TerminalSeedCertificate (termProvParams D Cw cr tT η₀ NT pT M) lawT
        (fun _ => isoPairedKernel (D.termRW σw M) nW) (fun _ => isoPairedKernel (D.termRNew cr tT M) nT)
        φ₀ hφ₀ cker (M + Jw) (M - 1) M (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) kS Ce τe (termR0bar RT dW) (termD0bar NT pT DW dW)
        (succSchedD (termD0bar NT pT DW dW) N p (H + 1)) cr tp (tp + D.termH M) (a + T₀)
        (Gt'.retained M 1 RT) →
      ∀ (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ)
        (U₀ : ∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root))
        (U V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root))
        (Uw Vw : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
        (Uk Vk : ∀ v u (_ : Gw.fam.Γ v u), ℝ → TorusHk (Kw + (termD0bar NT pT DW dW) - 1) (ScalarH u.1.root)),
        IsWeakPaired PW φ₀ hφ₀ lawW M Kw Lt nW a T₀ σw χw cK CK f Gw aM U₀ U V Uw Vw Uk Vk →
        IsWeakReadout lawW M Jw Lw Kw (D.κ M) a τ T₀ s Pw cK Cread Cid f θ Gw Ww V →
        IsTerminalPrepBounds lawW M Kw (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) k₀ hk₀w (le_trans (by omega : k₀ ≤ 2 * k₀ + 2) (le_trans (le_max_left _ _) (le_max_right Kout _))) cr cK CP QT f Gw aM tp Pterm V →
      ∀ (Z₀ : ∀ v : CompIn (Gt'.retained M 1 RT).comps, TorusHk (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) (ScalarH v.1.root))
        (Z : ∀ v : CompIn (Gt'.retained M 1 RT).comps, ℝ → TorusHk (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) (ScalarH v.1.root))
        (Zw : ∀ v : CompIn (Gt'.retained M 1 RT).comps, ℝ → TorusHk ((max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) + 1) (ScalarH v.1.root))
        (Zk : ∀ v u (_ : (Gt'.retained M 1 RT).fam.Γ v u), ℝ → TorusHk ((max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) + (termD0bar NT pT DW dW) - 1) (ScalarH u.1.root)),
        IsTerminalTrace Gw (Gt'.retained M 1 RT) (Pterm fun v => V v aM) Z₀ →
        (Gt'.retained M 1 RT).IsRegSolution (termProvParams D Cw cr tT η₀ NT pT M)
          (fun _ => isoPairedKernel (D.termRW σw M) nW) (fun _ => isoPairedKernel (D.termRNew cr tT M) nT) φ₀ hφ₀
          (D.termB M) (streamVel (D.Φ (M - 1))) (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) tp (a + T₀) Z₀ (fun _ _ => 0) (fun _ _ => 0)
          Z Zw Zk →
      ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn Gw.comps) (fun v => ScalarH v.1.root))
        (PZ : ∀ v : CompIn Gw.comps, ℝ → TorusHk ((max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) - 2 * pT) (ScalarH v.1.root))
        (aRep : ℝ → Vec 2 → ∀ v : CompIn Gw.comps, ScalarH v.1.root)
        (û : ∀ v : CompIn Gw.comps, ℝ → TorusHk k₀ (ScalarH v.1.root))
        (ŵ : ∀ v : CompIn Gw.comps, ℝ → TorusHk (k₀ + 1) (ScalarH v.1.root)),
        IsTerminalLiftedField Gw (Gt'.retained M 1 RT) M pT (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) NT dW sXT sZT η₀ tp (a + T₀) cr Z CcT PZ aRep û →
        (∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc tp (a + T₀))),
          truncateTorusHk (Nat.le_succ k₀) (ŵ v t) = û v t) →
        strongEnergy (D.termRStar cK M) (D.κ M) (Gw.mass lawW) tp (a + T₀)
            (fun v t => truncateTorusHk hk₀w (V v t) - û v t)
            (fun v t => truncateTorusHk (Nat.succ_le_succ hk₀w) (Vw v t) - ŵ v t) ≤
          ENNReal.ofReal (C * D.eps (M - 1) ^ (QT / 2) * Real.sqrt (l2NormSq f)) :=
  by
  -- Elaborated without the expected type, then compared once: elaborating the application against
  -- the expected type is too expensive (the nested proofs of the statement are not abstracted).
  have h := EntryTerminal.Route.errorEnergyStatement_of_native
    Construction.Preservation.Residual.CovarianceTransport.nativeTemporalRepresentatives
    α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  exact h

/-! Proof of `entry_terminal_residual` (the residual of the terminal entry and its bill).

`entry_terminal_residual` is `residualStatement_of_native` (the unbundling of
`residualBundled_of_native`, module `EntryTerminal.Ingredients.ErrorEnergy.ResidualFromNative`) at
`nativeTemporalRepresentatives` (the word operators). The text is the statement's, verbatim. -/

/-- **The terminal residual and its bill**. -/
theorem entry_terminal_residual (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
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
    ∀ (_σ₀ : ℝ) (H _J N p _Kres Lpr Lc Lf : ℕ) (nT : ℕ+), IsFreshKernelOrder nT LcT Lpr Lc Lf →
    ∃ (SX SZ Kfloor : ℕ),
    ∀ sXT sZT : ℕ, SX ≤ sXT → SZ ≤ sZT →
    ∀ Kout : ℕ, Kfloor ≤ Kout →
    ∃ Kneed : ℕ,
    ∀ (Kw Lt : ℕ) (nW : ℕ+) (hk₀w : k₀ ≤ Kw) (_hLw : Lw + 5 ≤ Kw) (cr : ℝ) (kS : InvConsts),
      Kneed ≤ Kw →
      L0w ≤ Lt → LpT ≤ Lt → Lt + 1 ≤ 2 * (nW : ℕ) → IsTerminalKernelOrders nW LoT LfT LpT Lpr Lc Lf →
      0 < cr → cr ≤ 1 → cr = 1 → kS.cr = cr → 0 < kS.c₀ →
      Kneed ≤ kS.Ks → Kneed ≤ kS.Kan → Kneed ≤ kS.Lan → Kneed ≤ kS.Jm →
    ∀ (cK CK CL Cχ Cread Cid : ℝ) (kW : InvConsts), 0 < cK → kW.c₀ = cK →
      IsWeakAllocation kW kS Lt → kW.G0 ≤ kW.Hprod →
      NT + DW + dW * (termD0bar NT pT DW dW + 1) ≤ kW.Lstar →
    ∀ (cP CP cHP : ℝ), 0 < cP → cHP ≤ 1 → ∃ Cw₀ : ℝ, ∀ (Cw Ce : ℝ) (cker : ℕ → ℝ), Cw₀ ≤ Cw →
    ∃ C cgap Cg : ℝ, 0 ≤ C ∧ 0 < cgap ∧
    ∃ (CHt Υt : ℝ), 1 ≤ CHt ∧ 0 < Υt ∧
    ∀ j₀ : ℕ, IsCarrierStart α q Λ bw CHt Υt j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ M D.κ → D.term = M →
    ∀ (a : ℝ) (lawW : BirthLaw) (PW : ProvParams)
      (Gw : GenStage D ScalarH (termD0bar NT pT DW dW) bw j₀) (aM : ℝ)
      (Ww : ℝ → (CompIn Gw.comps → Vec 2 → ℝ) → Vec 2 → ℝ),
      IsWeakStage lawW PW φ₀ hφ₀ M (M + Jw) Jw dW DW nW kW a T₀ σw CL Cχ χw Gw aM →
    ∀ (tp : ℝ) (Pterm : (∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn Gw.comps, TorusHk (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) (ScalarH v.1.root)))
      (lawT : BirthLaw) (Gt' : GenStage D ScalarH (termD0bar NT pT DW dW) bw j₀),
      IsTerminalPrepMap M Kw (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) cP CP Gw aM tp Pterm →
      IsTerminalLaw lawW lawT cHP η₀ (wordsUpTo (termAlphabet NT pT DW dW) RT).card →
      IsActualSuccessor D (termProvParams D Cw cr tT η₀ NT pT M)
        (termMenu (M + Jw) (termAlphabet NT pT DW dW) RT NT pT sXT sZT η₀ tp cr) Gw Gt' →
      TerminalSeedCertificate (termProvParams D Cw cr tT η₀ NT pT M) lawT
        (fun _ => isoPairedKernel (D.termRW σw M) nW) (fun _ => isoPairedKernel (D.termRNew cr tT M) nT)
        φ₀ hφ₀ cker (M + Jw) (M - 1) M (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) kS Ce τe (termR0bar RT dW) (termD0bar NT pT DW dW)
        (succSchedD (termD0bar NT pT DW dW) N p (H + 1)) cr tp (tp + D.termH M) (a + T₀)
        (Gt'.retained M 1 RT) →
      ∀ (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ)
        (U₀ : ∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root))
        (U V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root))
        (Uw Vw : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
        (Uk Vk : ∀ v u (_ : Gw.fam.Γ v u), ℝ → TorusHk (Kw + (termD0bar NT pT DW dW) - 1) (ScalarH u.1.root)),
        IsWeakPaired PW φ₀ hφ₀ lawW M Kw Lt nW a T₀ σw χw cK CK f Gw aM U₀ U V Uw Vw Uk Vk →
        IsWeakReadout lawW M Jw Lw Kw (D.κ M) a τ T₀ s Pw cK Cread Cid f θ Gw Ww V →
        IsTerminalPrepBounds lawW M Kw (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) k₀ hk₀w (le_trans (by omega : k₀ ≤ 2 * k₀ + 2) (le_trans (le_max_left _ _) (le_max_right Kout _))) cr cK CP QT f Gw aM tp Pterm V →
      ∀ (Z₀ : ∀ v : CompIn (Gt'.retained M 1 RT).comps, TorusHk (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) (ScalarH v.1.root))
        (Z : ∀ v : CompIn (Gt'.retained M 1 RT).comps, ℝ → TorusHk (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) (ScalarH v.1.root))
        (Zw : ∀ v : CompIn (Gt'.retained M 1 RT).comps, ℝ → TorusHk ((max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) + 1) (ScalarH v.1.root))
        (Zk : ∀ v u (_ : (Gt'.retained M 1 RT).fam.Γ v u), ℝ → TorusHk ((max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) + (termD0bar NT pT DW dW) - 1) (ScalarH u.1.root)),
        IsTerminalTrace Gw (Gt'.retained M 1 RT) (Pterm fun v => V v aM) Z₀ →
        (Gt'.retained M 1 RT).IsRegSolution (termProvParams D Cw cr tT η₀ NT pT M)
          (fun _ => isoPairedKernel (D.termRW σw M) nW) (fun _ => isoPairedKernel (D.termRNew cr tT M) nT) φ₀ hφ₀
          (D.termB M) (streamVel (D.Φ (M - 1))) (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) tp (a + T₀) Z₀ (fun _ _ => 0) (fun _ _ => 0)
          Z Zw Zk →
      ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn Gw.comps) (fun v => ScalarH v.1.root))
        (PZ : ∀ v : CompIn Gw.comps, ℝ → TorusHk ((max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) - 2 * pT) (ScalarH v.1.root))
        (aRep : ℝ → Vec 2 → ∀ v : CompIn Gw.comps, ScalarH v.1.root)
        (û : ∀ v : CompIn Gw.comps, ℝ → TorusHk k₀ (ScalarH v.1.root))
        (ŵ : ∀ v : CompIn Gw.comps, ℝ → TorusHk (k₀ + 1) (ScalarH v.1.root)),
        IsTerminalLiftedField Gw (Gt'.retained M 1 RT) M pT (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) NT dW sXT sZT η₀ tp (a + T₀) cr Z CcT PZ aRep û →
        (∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc tp (a + T₀))),
          truncateTorusHk (Nat.le_succ k₀) (ŵ v t) = û v t) →
      TerminalResidualClauses PW (fun _ => isoPairedKernel (D.termRW σw M) nW) φ₀ hφ₀ lawW M Kw k₀ hk₀w cK C
        (termBill D M NT pT RT AT LcT LoT LfT (termAlphabet NT pT DW dW) cr σw χw η₀ tT cgap Cg tp (a + T₀))
        tp (a + T₀) f Gw V Vw û ŵ :=
  by
  -- Elaborated without the expected type, then compared once (as for the error energy bound).
  have h := EntryTerminal.Route.residualStatement_of_native
    Construction.Preservation.Residual.CovarianceTransport.nativeTemporalRepresentatives
    α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  exact h

/-! Proof of `entry_terminal_preparation` (the capped preparation of the terminal entry).

`entry_terminal_preparation` is `terminalPreparation` (module `EntryTerminal.Assembly.Prep.Closed`):
`preparation_of_seam` at the proved `cycle_seam`. Its text copy `PreparationStatement` is in the
module `EntryTerminal.Assembly.Route.Ingredients`. -/

/-- **The terminal capped preparation** (Proposition 14.10(a) of the paper). -/
theorem entry_terminal_preparation (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (c₀max : ℝ), 0 < c₀max →
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Jw Lw dW DW : ℕ) (τ T₀ Pw σw χw η₀ : ℝ),
      1 ≤ Jw → 0 < τ → τ < T₀ → 0 < Pw → 0 < σw → σw < min (ocC α q) (q - 1) → 0 < χw →
      0 < η₀ → η₀ ≤ ocDelta α q / 8 →
    ∀ PT : ℝ, 0 < PT →
    ∀ (NT pT RT AT k₀ LcT LoT LfT LpT : ℕ) (tT QT : ℝ),
      IsTerminalSchedule α q s PT QT σw χw η₀ tT Jw Lw k₀ NT pT RT AT LcT LoT LfT LpT
        (termAlphabet NT pT DW dW) →
    ∀ Kout : ℕ,
    ∃ Kneed : ℕ,
    ∀ (Kw Lt : ℕ) (nW : ℕ+) (hk₀w : k₀ ≤ Kw) (cr : ℝ), Kneed ≤ Kw →
      LpT ≤ Lt → Lt + 1 ≤ 2 * (nW : ℕ) →
      0 < cr → cr ≤ 1 →
    ∀ (cK CK CL Cχ : ℝ) (kW : InvConsts), 0 < cK → kW.c₀ = cK →
      Kneed ≤ kW.Ks → Kneed ≤ kW.Kan → Kneed ≤ kW.Lan → Kneed ≤ kW.Jm → Lt ≤ kW.Lker →
    ∃ (c C : ℝ), 0 < c ∧
    ∀ j₀ : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ M D.κ → D.term = M →
    ∀ (a : ℝ) (lawW : BirthLaw) (PW : ProvParams)
      (Gw : GenStage D ScalarH (termD0bar NT pT DW dW) bw j₀) (aM : ℝ)
      (_Ww : ℝ → (CompIn Gw.comps → Vec 2 → ℝ) → Vec 2 → ℝ),
      IsWeakStage lawW PW φ₀ hφ₀ M (M + Jw) Jw dW DW nW kW a T₀ σw CL Cχ χw Gw aM →
    ∃ (tp : ℝ) (Pterm : (∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn Gw.comps, TorusHk (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) (ScalarH v.1.root))),
      IsTerminalPrepMap M Kw (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) c C Gw aM tp Pterm ∧
      ∀ (f : Vec 2 → ℝ)
        (U₀ : ∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root))
        (U V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root))
        (Uw Vw : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
        (Uk Vk : ∀ v u (_ : Gw.fam.Γ v u), ℝ → TorusHk (Kw + (termD0bar NT pT DW dW) - 1) (ScalarH u.1.root)),
        IsWeakPaired PW φ₀ hφ₀ lawW M Kw Lt nW a T₀ σw χw cK CK f Gw aM U₀ U V Uw Vw Uk Vk →
        IsTerminalPrepBounds lawW M Kw (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) k₀ hk₀w (le_trans (by omega : k₀ ≤ 2 * k₀ + 2) (le_trans (le_max_left _ _) (le_max_right Kout _))) cr cK C QT f Gw aM tp Pterm V :=
  EntryTerminal.Route.terminalPreparation α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

/-! Proof of `entry_terminal_of_weak` (the terminal entry, conditional on the weak output
package).

`entry_terminal_of_weak` is `entryTerminalOfWeak_of_native` (module
`EntryTerminal.Assembly.Route.EntryTerminalOfNative`: every ingredient of the terminal route proved,
the error energy from the native leaf) at `nativeTemporalRepresentatives`. The text is the
statement's, verbatim. -/

/-- **A full seed for preservation (conditional on the weak output package)**. -/
theorem entry_terminal_of_weak (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
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
    ∀ (_σ₀ : ℝ) (H J N p Kres Lpr Lc Lf : ℕ) (nT : ℕ+), IsFreshKernelOrder nT LcT Lpr Lc Lf →
    ∀ Kout : ℕ,
    ∃ SX SZ : ℕ, ∀ sXT sZT : ℕ, SX ≤ sXT → SZ ≤ sZT →
    ∃ (Kw Lt : ℕ) (nW : ℕ+) (hk₀w : k₀ ≤ Kw) (_hLw : Lw + 5 ≤ Kw) (cr : ℝ) (kS : InvConsts),
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
            Pw PT C cr f θ Ww V Z :=
  by
  -- Elaborated without the expected type, then compared once (as for the error energy bound).
  have h := EntryTerminal.Route.entryTerminalOfWeak_of_native
    Construction.Preservation.Residual.CovarianceTransport.nativeTemporalRepresentatives
    α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  exact h

end AVRegularity.Providers
end
