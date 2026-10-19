-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Residual.Presentation.Ident
public import AVRegularity.Construction.Preservation.FullLift.KernelStrongEnergy
import AVRegularity.EntryTerminal.Ingredients.Recon.PartitionGate
import AVRegularity.CycleComparison.Reconstruction.ApproxJets
import AVRegularity.Construction.Residual.Presentation.PlainToKernel
import AVRegularity.EntryTerminal.Ingredients.ForcedEnergy.TerminalForced
import AVRegularity.EntryTerminal.Ingredients.BillScale.Main
import AVRegularity.EntryTerminal.Ingredients.SeedCert.SeedCertPart
import AVRegularity.EntryTerminal.Ingredients.Frontier.InnerWrappers
public import AVRegularity.EntryTerminal.Assembly.Route.EntryTerminalOfWeak
import AVRegularity.EntryTerminal.Ingredients.ScaleFacts.ScaleFacts

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.EntryTerminal.Route

/-! **The terminal residual over the bundled data.** `ResidualAtM` is `EnergyAtM` (the premises of
the `entry_terminal_residual` from the data on, verbatim) with the conclusion of the
residual statement: the error `V − û` is a regularized solution with a residual of bill
`C · termBill · ‖f‖₂`. `ResidualBundled` is the residual statement over `TermArgs`, with the constants `C, c_gap, C_g`
before the level (as in the statement), and `0 ≤ C`: the statement does not
say it, and the assembly needs it (the bill has no sign).

For `f = 0` the bill bound is zero. -/

/-- The residual statement at a fixed threshold level `M` (from the data onwards). -/
def ResidualAtM {X : TermConstruction} (A : TermArgs X) (Kout : ℕ) (sXT : ℕ) (sZT : ℕ) (Kw : ℕ) (Lt : ℕ) (nW : ℕ+) (hk₀w : A.k₀ ≤ Kw) (cr : ℝ) (kS : InvConsts) (cK : ℝ) (CK : ℝ) (CL : ℝ) (Cχ : ℝ) (Cread : ℝ) (Cid : ℝ) (kW : InvConsts) (cP : ℝ) (CP : ℝ) (cHP : ℝ) (C cgap Cg : ℝ) (Ce : ℝ) (Cw : ℝ) (cker : ℕ → ℝ) (j₀ : ℕ) (M : ℕ) : Prop :=
  ∀ (D : OCData), D.α = X.α → D.q = X.q → D.Λ = A.Λ → D.ζ = X.ζ → IsOCStreamSeq X.α X.q A.Λ X.ζ D.Φ →
    IsOCBandChain X.α X.q A.Λ X.ζ M D.κ → D.term = M →
  ∀ (a : ℝ) (lawW : BirthLaw) (PW : ProvParams)
    (Gw : GenStage D ScalarH (termD0bar A.NT A.pT A.DW A.dW) A.bw j₀) (aM : ℝ)
    (Ww : ℝ → (CompIn Gw.comps → Vec 2 → ℝ) → Vec 2 → ℝ),
    IsWeakStage lawW PW A.φ₀ A.hφ₀ M (M + A.Jw) A.Jw A.dW A.DW nW kW a A.T₀ A.σw CL Cχ A.χw Gw aM →
  ∀ (tp : ℝ) (Pterm : (∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn Gw.comps, TorusHk (max Kout (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) (ScalarH v.1.root)))
    (lawT : BirthLaw) (Gt' : GenStage D ScalarH (termD0bar A.NT A.pT A.DW A.dW) A.bw j₀),
    IsTerminalPrepMap M Kw (max Kout (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) cP CP Gw aM tp Pterm →
    IsTerminalLaw lawW lawT cHP A.η₀ (wordsUpTo (termAlphabet A.NT A.pT A.DW A.dW) A.RT).card →
    IsActualSuccessor D (termProvParams D Cw cr A.tT A.η₀ A.NT A.pT M)
      (termMenu (M + A.Jw) (termAlphabet A.NT A.pT A.DW A.dW) A.RT A.NT A.pT sXT sZT A.η₀ tp cr) Gw Gt' →
    TerminalSeedCertificate (termProvParams D Cw cr A.tT A.η₀ A.NT A.pT M) lawT
      (fun _ => isoPairedKernel (D.termRW A.σw M) nW) (fun _ => isoPairedKernel (D.termRNew cr A.tT M) A.nT)
      A.φ₀ A.hφ₀ cker (M + A.Jw) (M - 1) M (max Kout (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) kS Ce A.τe (termR0bar A.RT A.dW) (termD0bar A.NT A.pT A.DW A.dW)
      (succSchedD (termD0bar A.NT A.pT A.DW A.dW) A.N A.p (A.H + 1)) cr tp (tp + D.termH M) (a + A.T₀)
      (Gt'.retained M 1 A.RT) →
    ∀ (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ)
      (U₀ : ∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root))
      (U V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root))
      (Uw Vw : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
      (Uk Vk : ∀ v u (_ : Gw.fam.Γ v u), ℝ → TorusHk (Kw + (termD0bar A.NT A.pT A.DW A.dW) - 1) (ScalarH u.1.root)),
      IsWeakPaired PW A.φ₀ A.hφ₀ lawW M Kw Lt nW a A.T₀ A.σw A.χw cK CK f Gw aM U₀ U V Uw Vw Uk Vk →
      IsWeakReadout lawW M A.Jw A.Lw Kw (D.κ M) a A.τ A.T₀ X.s A.Pw cK Cread Cid f θ Gw Ww V →
      IsTerminalPrepBounds lawW M Kw (max Kout (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) A.k₀ hk₀w (le_trans (by omega : A.k₀ ≤ 2 * A.k₀ + 2) (le_trans (le_max_left _ _) (le_max_right Kout _))) cr cK CP A.QT f Gw aM tp Pterm V →
    ∀ (Z₀ : ∀ v : CompIn (Gt'.retained M 1 A.RT).comps, TorusHk (max Kout (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) (ScalarH v.1.root))
      (Z : ∀ v : CompIn (Gt'.retained M 1 A.RT).comps, ℝ → TorusHk (max Kout (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) (ScalarH v.1.root))
      (Zw : ∀ v : CompIn (Gt'.retained M 1 A.RT).comps, ℝ → TorusHk ((max Kout (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) + 1) (ScalarH v.1.root))
      (Zk : ∀ v u (_ : (Gt'.retained M 1 A.RT).fam.Γ v u), ℝ → TorusHk ((max Kout (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) + (termD0bar A.NT A.pT A.DW A.dW) - 1) (ScalarH u.1.root)),
      IsTerminalTrace Gw (Gt'.retained M 1 A.RT) (Pterm fun v => V v aM) Z₀ →
      (Gt'.retained M 1 A.RT).IsRegSolution (termProvParams D Cw cr A.tT A.η₀ A.NT A.pT M)
        (fun _ => isoPairedKernel (D.termRW A.σw M) nW) (fun _ => isoPairedKernel (D.termRNew cr A.tT M) A.nT) A.φ₀ A.hφ₀
        (D.termB M) (streamVel (D.Φ (M - 1))) (max Kout (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) tp (a + A.T₀) Z₀ (fun _ _ => 0) (fun _ _ => 0)
        Z Zw Zk →
    ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn Gw.comps) (fun v => ScalarH v.1.root))
      (PZ : ∀ v : CompIn Gw.comps, ℝ → TorusHk ((max Kout (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) - 2 * A.pT) (ScalarH v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn Gw.comps, ScalarH v.1.root)
      (û : ∀ v : CompIn Gw.comps, ℝ → TorusHk A.k₀ (ScalarH v.1.root))
      (ŵ : ∀ v : CompIn Gw.comps, ℝ → TorusHk (A.k₀ + 1) (ScalarH v.1.root)),
      IsTerminalLiftedField Gw (Gt'.retained M 1 A.RT) M A.pT (max Kout (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) A.NT A.dW sXT sZT A.η₀ tp (a + A.T₀) cr Z CcT PZ aRep û →
      (∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc tp (a + A.T₀))),
        truncateTorusHk (Nat.le_succ A.k₀) (ŵ v t) = û v t) →
      TerminalResidualClauses PW (fun _ => isoPairedKernel (D.termRW A.σw M) nW) A.φ₀ A.hφ₀ lawW M Kw
        A.k₀ hk₀w cK C
        (termBill D M A.NT A.pT A.RT A.AT A.LcT A.LoT A.LfT (termAlphabet A.NT A.pT A.DW A.dW) cr A.σw
          A.χw A.η₀ A.tT cgap Cg tp (a + A.T₀))
        tp (a + A.T₀) f Gw V Vw û ŵ


/-- The residual statement over the bundled data. -/
def ResidualBundled : Prop :=
  ∀ X : TermConstruction, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ A : TermArgs X, Λ₀ ≤ A.Λ → A.Valid →
    ∃ (SX SZ Kfloor : ℕ),
    ∀ sXT sZT : ℕ, SX ≤ sXT → SZ ≤ sZT →
    ∀ Kout : ℕ, Kfloor ≤ Kout →
    ∃ Kneed : ℕ,
    ∀ (Kw Lt : ℕ) (nW : ℕ+) (hk₀w : A.k₀ ≤ Kw) (_hLw : A.Lw + 5 ≤ Kw) (cr : ℝ) (kS : InvConsts),
      Kneed ≤ Kw →
      A.L0w ≤ Lt → A.LpT ≤ Lt → Lt + 1 ≤ 2 * (nW : ℕ) → IsTerminalKernelOrders nW A.LoT A.LfT A.LpT A.Lpr A.Lc A.Lf →
      0 < cr → cr ≤ 1 → cr = 1 → kS.cr = cr → 0 < kS.c₀ →
      Kneed ≤ kS.Ks → Kneed ≤ kS.Kan → Kneed ≤ kS.Lan → Kneed ≤ kS.Jm →
    ∀ (cK CK CL Cχ Cread Cid : ℝ) (kW : InvConsts), 0 < cK → kW.c₀ = cK →
      IsWeakAllocation kW kS Lt → kW.G0 ≤ kW.Hprod →
      A.NT + A.DW + A.dW * (A.Dt + 1) ≤ kW.Lstar →
    ∀ (cP CP cHP : ℝ), 0 < cP → cHP ≤ 1 → ∃ Cw₀ : ℝ, ∀ (Cw Ce : ℝ) (cker : ℕ → ℝ), Cw₀ ≤ Cw →
    ∃ C cgap Cg : ℝ, 0 ≤ C ∧ 0 < cgap ∧
    ∃ (CHt Υt : ℝ), 1 ≤ CHt ∧ 0 < Υt ∧
    ∀ j₀ : ℕ, IsCarrierStart X.α X.q A.Λ A.bw CHt Υt j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ResidualAtM A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP C cgap Cg Ce Cw
      cker j₀ M

/-! **The terminal residual in its stated form: the text copy and the split statements** (as for the error-energy
unbundling).
- `ResidualStatement`: the text of `entry_terminal_residual` verbatim.
- `E8Tail α … nT`: its tail after `IsFreshKernelOrder … →`, every variable explicit;
  `E8Copy` is the residual statement with that tail named, definitionally `ResidualStatement`.
- `E8BundledTail A`: the tail of `ResidualBundled` after `A.Valid →`.

The unbundling then compares two applications of `E8Tail` argument by
argument instead of the two expanded tails. The hypothesis `1 ≤ D_W` is carried by `A.Valid`. -/

/-- The text of `entry_terminal_residual`. -/
def ResidualStatement : Prop :=
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
    ∃ (SX SZ Kfloor : ℕ),
    ∀ sXT sZT : ℕ, SX ≤ sXT → SZ ≤ sZT →
    ∀ Kout : ℕ, Kfloor ≤ Kout →
    ∃ Kneed : ℕ,
    ∀ (Kw Lt : ℕ) (nW : ℕ+) (hk₀w : k₀ ≤ Kw) (hLw : Lw + 5 ≤ Kw) (cr : ℝ) (kS : InvConsts),
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
        tp (a + T₀) f Gw V Vw û ŵ

/-- The tail of the residual statement after `IsFreshKernelOrder … →`, every variable explicit. -/
def E8Tail (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (_c₀max : ℝ) (φ₀ : Vec 2 → ℝ)
    (hφ₀ : Integrable φ₀) (bw : ℝ) (Jw Lw dW DW L0w : ℕ) (τ T₀ Pw σw χw η₀ _PT : ℝ)
    (NT pT RT AT k₀ LcT LoT LfT LpT : ℕ) (tT QT τe _lamE _σ₀ : ℝ) (H _J N p _Kres Lpr Lc Lf : ℕ)
    (nT : ℕ+) : Prop :=
    ∃ (SX SZ Kfloor : ℕ),
    ∀ sXT sZT : ℕ, SX ≤ sXT → SZ ≤ sZT →
    ∀ Kout : ℕ, Kfloor ≤ Kout →
    ∃ Kneed : ℕ,
    ∀ (Kw Lt : ℕ) (nW : ℕ+) (hk₀w : k₀ ≤ Kw) (hLw : Lw + 5 ≤ Kw) (cr : ℝ) (kS : InvConsts),
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
        tp (a + T₀) f Gw V Vw û ŵ

/-- The residual statement with its tail named. -/
def E8Copy : Prop :=
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
    E8Tail α s q ζ Λ c₀max φ₀ hφ₀ bw Jw Lw dW DW L0w τ T₀ Pw σw χw η₀ PT NT pT RT AT k₀ LcT LoT
      LfT LpT tT QT τe lamE σ₀ H J N p Kres Lpr Lc Lf nT

/-- The tail of `ResidualBundled` after `A.Valid →`. -/
def E8BundledTail {X : TermConstruction} (A : TermArgs X) : Prop :=
    ∃ (SX SZ Kfloor : ℕ),
    ∀ sXT sZT : ℕ, SX ≤ sXT → SZ ≤ sZT →
    ∀ Kout : ℕ, Kfloor ≤ Kout →
    ∃ Kneed : ℕ,
    ∀ (Kw Lt : ℕ) (nW : ℕ+) (hk₀w : A.k₀ ≤ Kw) (_hLw : A.Lw + 5 ≤ Kw) (cr : ℝ) (kS : InvConsts),
      Kneed ≤ Kw →
      A.L0w ≤ Lt → A.LpT ≤ Lt → Lt + 1 ≤ 2 * (nW : ℕ) → IsTerminalKernelOrders nW A.LoT A.LfT A.LpT A.Lpr A.Lc A.Lf →
      0 < cr → cr ≤ 1 → cr = 1 → kS.cr = cr → 0 < kS.c₀ →
      Kneed ≤ kS.Ks → Kneed ≤ kS.Kan → Kneed ≤ kS.Lan → Kneed ≤ kS.Jm →
    ∀ (cK CK CL Cχ Cread Cid : ℝ) (kW : InvConsts), 0 < cK → kW.c₀ = cK →
      IsWeakAllocation kW kS Lt → kW.G0 ≤ kW.Hprod →
      A.NT + A.DW + A.dW * (A.Dt + 1) ≤ kW.Lstar →
    ∀ (cP CP cHP : ℝ), 0 < cP → cHP ≤ 1 → ∃ Cw₀ : ℝ, ∀ (Cw Ce : ℝ) (cker : ℕ → ℝ), Cw₀ ≤ Cw →
    ∃ C cgap Cg : ℝ, 0 ≤ C ∧ 0 < cgap ∧
    ∃ (CHt Υt : ℝ), 1 ≤ CHt ∧ 0 < Υt ∧
    ∀ j₀ : ℕ, IsCarrierStart X.α X.q A.Λ A.bw CHt Υt j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ResidualAtM A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP C cgap Cg Ce Cw
      cker j₀ M

/-- The copy is the residual statement. -/
theorem e8_of_copy (h : E8Copy) : ResidualStatement := h

end AVRegularity.EntryTerminal.Route
end

section
namespace AVRegularity.EntryTerminal.Route

/-! **The residual in its stated form from the bundled route: the unbundling** (as for the
error-energy unbundling). `residualStatement_of_bundled : ResidualBundled →
ResidualStatement`, in steps, each its own declaration:
- `e8BundledTail`: `ResidualBundled` with its tail named (`E8BundledTail`);
- `e8Tail_of_bundledTail`: the bundled tail at `A` is `E8Tail` at the projections of `A`
  (forward style);
- `e8Copy_of_bundled`: the prefix of the residual statement builds `X : TermConstruction`, `A : TermArgs X` and
  `A.Valid`; the final step compares `E8Tail` at the projections of the constructed `X`, `A`
  with `E8Tail` at the variables, argument by argument;
- `residualStatement_of_bundled`: through `e8_of_copy`.

The choice `D_W = 1 + J_w N_w` satisfies `1 ≤ D_W`, which `A.Valid` carries last, while
`D_W = 0` is excluded by it; the least floors pass unchanged, since the tail is the same
proposition. -/

/-- `ResidualBundled` with its tail named. -/
theorem e8BundledTail (h : ResidualBundled) (X : TermConstruction) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ A : TermArgs X, Λ₀ ≤ A.Λ → A.Valid → E8BundledTail A :=
  h X

/-- The bundled tail at `A` is the tail of the residual statement at the projections of `A`. -/
theorem e8Tail_of_bundledTail {X : TermConstruction} (A : TermArgs X)
    (h : E8BundledTail A) :
    E8Tail X.α X.s X.q X.ζ A.Λ A.c₀max A.φ₀ A.hφ₀ A.bw A.Jw A.Lw A.dW A.DW A.L0w A.τ A.T₀
      A.Pw A.σw A.χw A.η₀ A.PT A.NT A.pT A.RT A.AT A.k₀ A.LcT A.LoT A.LfT A.LpT A.tT A.QT A.τe
      A.lamE A.σ₀ A.H A.J A.N A.p A.Kres A.Lpr A.Lc A.Lf A.nT :=
  h

/-- **The residual statement with its tail named, from the bundled route.** -/
theorem e8Copy_of_bundled (h : ResidualBundled) : E8Copy := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λ₀, h128, h'⟩ := e8BundledTail h ⟨α, s, q, ζ, hα₀, hα₁, hs₀, hs₁, hq, hζ⟩
  refine ⟨Λ₀, h128, ?_⟩
  intro Λ hΛ c₀max hc0 φ₀ hφ₀ hφs hφn hφm hφsupp bw hbw0 hbw1 Jw Lw dW DW L0w τ T₀ Pw σw χw η₀
    hJw hDW hτ hτT hPw hσw0 hσw1 hχw hη0 hη1 PT hPT NT pT RT AT k₀ LcT LoT LfT LpT tT QT hsched
    τe lamE hexp σ₀ H J N p Kres Lpr Lc Lf nT hfresh
  have hT := e8Tail_of_bundledTail
    ⟨Λ, c₀max, φ₀, hφ₀, bw, Jw, Lw, dW, DW, L0w, τ, T₀, Pw, σw, χw, η₀, PT, NT, pT, RT, AT, k₀,
      LcT, LoT, LfT, LpT, tT, QT, τe, lamE, σ₀, H, J, N, p, Kres, Lpr, Lc, Lf, nT⟩
    (h' _ hΛ ⟨hc0, ⟨hφs, hφn, hφm, hφsupp⟩, ⟨hbw0, hbw1⟩,
      ⟨hJw, hτ, hτT, hPw, hσw0, hσw1, hχw, hη0, hη1⟩, hPT, hsched, hexp, hfresh, hDW⟩)
  exact hT

/-- **The residual in its stated form from the bundled route.** -/
theorem residualStatement_of_bundled (h : ResidualBundled) : ResidualStatement :=
  e8_of_copy (e8Copy_of_bundled h)

end AVRegularity.EntryTerminal.Route
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Residual.Presentation
namespace AVRegularity.EntryTerminal.Route

/-! **From the bounds of the terminal residual to the clauses of the statement**.
At a context, `TermResidualBoundAt c C c_gap C_g` gives:
a reconstruction `(uK, wK, RK, qK)` of the lifted field at descending slots `K ≥ k₀`; a
realization `F_f` of the fine flux; and the residual clause for `(trunc RK, F_f, trunc qK)` with the
bound `C · bill · ‖f‖₂`. `TermResClausesAt` asks the clauses of `entry_terminal_residual`
(`TerminalResidualClauses`) for the error `V − û`, with the same constant.

Route:
- **plain to kernel** (the generic `PlainToKernelStatementR`): the truncations of `uK` solve the
  regularized system of the weak stage with the forcing `(trunc RK + F_f, trunc qK)`;
- **identification**: `trunc uK = û` on the window, from the two value clauses
  (`IsStageRecon.value`, `c.lift`) and `torusHk_jet_eq_of_value`;
- **subtraction**: `V` solves the same system with zero forcing (`c.paired`), so the error
  solves it with `(Rres, qres) = (−trunc RK − F_f, −trunc qK)`. The residual norm is invariant under
  the sign, so the bound is the residual clause.

For `f = 0` we have `V = 0` and the reconstruction of the zero lifted field is zero, so every
clause holds with zero forcing. If no identity has positive width, then `F_f = 0` and the
plain-to-kernel step is `flux_match`. For `C = 0` the residual
clause forces `Rres = 0` and `qres = 0` in norm. If `t_p = a + T₀`, the window is a single time
and the integrals vanish. -/

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- **The conversion at a context.** -/
def TermResClausesAt
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (_x : TermResAux c) (C cgap Cg : ℝ) : Prop :=
  TermResidualBoundAt c C cgap Cg →
    TerminalResidualClauses c.PW (A.Kw_ c.D M nW) A.φ₀ A.hφ₀ c.lawW M Kw A.k₀ hk₀w cK C
      (c.bill cgap Cg) c.tp (c.a + A.T₀) c.f c.Gw c.V c.Vw c.û c.ŵ

/-- **The conversion with the prefix of the statement**. The constants
`C, c_gap, C_g` are universal: the conversion holds for every bound, so it can be applied at the
constants of `TermResidualBoundStatement`. -/
def TermResClausesStatement : Prop :=
  TermResPrefix fun c x _ _ _ _ _ => ∀ C cgap Cg : ℝ, TermResClausesAt c x C cgap Cg

end AVRegularity.EntryTerminal.Route
end
end
end

section
section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Residual.Presentation AVRegularity.Construction.Preservation.FullLift
namespace AVRegularity.EntryTerminal.Route

/-! **The residual at one level from the context statements.** `ResidualAtM` quantifies over the
data and premises of `entry_terminal_residual` at a level `M`. These are the fields of `TermResCtx`
in order, so a context is an anonymous constructor. The auxiliary data `TermResAux` are built by
`termResAux_of`:
- the classical representatives of the readout and of `Z` at `K̂ − 2`
  (`hilbert_classicalRep_exists`);
- the quiet margin (the last clause of `IsTerminalPrepMap`);
- the reserve premises;
- a certificate of `Gt'`.

`residualAtM_of_ctx` then gives `ResidualAtM` from the bounds and their conversion
at every context.

The case `K̂ = 2` is excluded by `K̂ ≥ 2k₀ + 2 ≥ 2`, so the representatives have order `≥ 0`. -/

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

theorem termKhat_two (A : TermArgs X) (Kout : ℕ) : 2 ≤ A.Khat Kout :=
  le_trans (by omega) (le_trans (le_max_left _ _) (le_max_right Kout _))

/-- **The auxiliary data of a context** from the reserve premises and a certificate of `Gt'`. -/
def termResAux_of
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (hcr : cr = 1) (hGH : kW.G0 ≤ kW.Hprod)
    (hLs : A.NT + A.DW + A.dW * (A.Dt + 1) ≤ kW.Lstar) (hcH : cHP ≤ 1)
    (hcert : c.Gt'.IsContextCertified kW) (hCw : 0 ≤ Cw) : TermResAux c where
  aZ t y v := Classical.choose (hilbert_classicalRep_exists (A.Khat Kout) (A.Khat Kout - 2)
    (by have := termKhat_two A Kout; omega)
    (succReadout M (c.D.eps (M - 1)) A.η₀ (A.Khat Kout) (fun v' => c.Z v' t) v)) y
  aY t y v := Classical.choose (hilbert_classicalRep_exists (A.Khat Kout) (A.Khat Kout - 2)
    (by have := termKhat_two A Kout; omega) (c.Z v t)) y
  repZ v t _ := Classical.choose_spec (hilbert_classicalRep_exists (A.Khat Kout) (A.Khat Kout - 2)
    (by have := termKhat_two A Kout; omega)
    (succReadout M (c.D.eps (M - 1)) A.η₀ (A.Khat Kout) (fun v' => c.Z v' t) v))
  repY v t _ := Classical.choose_spec (hilbert_classicalRep_exists (A.Khat Kout) (A.Khat Kout - 2)
    (by have := termKhat_two A Kout; omega) (c.Z v t))
  one := hcr
  quietMargin := c.prep.2.2.2.2
  reserve := le_trans hGH (Nat.le_succ _)
  reserve1 := hGH
  lstar := hLs
  cHle := hcH
  cert := hcert
  cwNonneg := hCw

/-- **The residual at one level**, from the residual bounds and their conversion at every context of the level and a certificate of
every terminal successor of the level. -/
theorem residualAtM_of_ctx {C cgap Cg : ℝ} (hcr : cr = 1) (hGH : kW.G0 ≤ kW.Hprod)
    (hLs : A.NT + A.DW + A.dW * (A.Dt + 1) ≤ kW.Lstar) (hcH : cHP ≤ 1) (hCw : 0 ≤ Cw)
    (hcert : ∀ c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP
      cHP Cw Ce cker j₀ M, c.Gt'.IsContextCertified kW)
    (hB : ∀ (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP
      Cw Ce cker j₀ M) (_x : TermResAux c), TermResidualBoundAt c C cgap Cg)
    (hC : ∀ (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP
      Cw Ce cker j₀ M) (x : TermResAux c), TermResClausesAt c x C cgap Cg) :
    ResidualAtM A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP C cgap Cg Ce
      Cw cker j₀ M := by
  intro D hα hq hΛD hζ hΦ hband hterm a lawW PW Gw aM Ww hweak tp Pterm lawT Gt' hprep hlaw hsucc
    hseed f θ U₀ U V Uw Vw Uk Vk hpaired hread hprepB Z₀ Z Zw Zk htrace hsol CcT PZ aRep û ŵ hlift
    htrunc
  let c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M :=
    ⟨D, ⟨hα, hq, hΛD, hζ, hΦ, hband, hterm⟩, a, lawW, PW, Gw, aM, Ww, hweak, tp, Pterm, lawT, Gt',
      hprep, hlaw, hsucc, hseed, f, θ, U₀, U, V, Uw, Vw, Uk, Vk, hpaired, hread, hprepB, Z₀, Z, Zw,
      Zk, htrace, hsol, CcT, PZ, aRep, û, ŵ, hlift, htrunc⟩
  let x := termResAux_of c hcr hGH hLs hcH (hcert c) hCw
  exact hC c x (hB c x)

end AVRegularity.EntryTerminal.Route
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.EntryTerminal.Route

/-! **The terminal error energy from its parts.** At a level (`energyAtM_of_parts`):
- the residual statement gives the error `e = V − û` as a regularized solution with residual bill
  `C₈ · termBill · ‖f‖₂`;
- the forced energy bound (`TerminalForcedEnergyStatement`) bounds its energy by
  `C_a(‖e(t_p)‖_{r_*} + X_r)`;
- the initial discrepancy is the triangle inequality
  `‖e(t_p)‖ ≤ ‖V(t_p) − g‖ + ‖g − û(t_p)‖`, `g = P_term V(a_M)`: the first term is bound 3 of the
  preparation (`≤ C_P E^{Q_T/2}‖f‖₂`), the second is the quiet entrance
  (`TerminalQuietEntranceStatement`) at `Q = Q_T/2` times bound 1 (`‖g‖_{ρ} ≤ C_P ‖f‖₂`);
- the bill scale (`TermBillScaleStatement`) bounds the bill by `C_d E^{Q_T+2} ≤ C_d E^{Q_T/2}`.
The constant is `C_a (C_P + C_b C_P + C₈ C_d)`. An empty window (`a + T₀ < t_p`) has zero energy.
`errorEnergyBundled_of_parts` joins the parts over the bundled data (the residual statement with
`0 ≤ C₈`; `K_need` is that of the residual statement raised to `k₀`; `M₀` covers the entrance
lemma). The quiet-entrance hypothesis is taken in the expanded form `EntranceAtM` (converted once by
`entranceAtM_of`) and the triangle inequality is its own lemma `initialDiscrepancy_le`: both keep
the at-level proof within the default budget.

Degenerate cases:
- `f = 0`: every bound is `0`.
- `C_b = 0` (the exact entrance): the second term vanishes.
- `t_p = a + T₀`: a one-point window. -/

/-- An empty window has zero strong energy. -/
theorem strongEnergy_eq_zero_of_lt {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (ρ B : ℝ) (π : ι → ℝ) {t₀ t₁ : ℝ} (ht : t₁ < t₀) {K : ℕ}
    (u : ∀ v, ℝ → TorusHk K (h v)) (w : ∀ v, ℝ → TorusHk (K + 1) (h v)) :
    strongEnergy ρ B π t₀ t₁ u w = 0 := by
  have hI : Set.Icc t₀ t₁ = ∅ := Set.Icc_eq_empty (not_le.2 ht)
  unfold strongEnergy
  simp only [hI, Set.mem_empty_iff_false, iSup_false, iSup_bot, Measure.restrict_empty,
    lintegral_zero_measure, mul_zero, add_zero]
  simp

/-- The weak components (roots) are retained components of the actual successor. -/
theorem weak_comps_subset_retained {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
    [∀ r, NormedSpace ℝ (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {P : ProvParams}
    {Mn : SuccMenu} {G G' : GenStage D hr Dm b j₀} (hact : IsActualSuccessor D P Mn G G')
    (hroot : ∀ v : CompIn G.comps, v.1.births = []) (m H : ℕ) :
    G.comps ⊆ (G'.retained m H Mn.J).comps := by
  intro c hc
  change c ∈ G'.comps.filter (IsRetained m H Mn.J)
  have hb : c.births = [] := hroot ⟨c, hc⟩
  refine Finset.mem_filter.2 ⟨?_, ?_, ?_⟩
  · rw [hact.2.2.1]
    exact Finset.mem_union_left _ hc
  · show c.births.length ≤ H
    rw [hb]
    exact Nat.zero_le _
  · unfold compWord
    rw [hb]
    exact Nat.zero_le _

/-- The triangle inequality of the weighted norm (positive masses). -/
theorem weightedNorm_sub_le {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
    [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] {S : Finset Comp} {k : ℕ} (ρ : ℝ) (π : CompIn S → ℝ)
    (hπ : ∀ v, 0 < π v) (X Y Z : ∀ v : CompIn S, TorusHk k (hr v.1.root)) :
    weightedNorm ρ π (fun _ => 1) (fun v => X v - Z v) ≤
      weightedNorm ρ π (fun _ => 1) (fun v => X v - Y v) +
        weightedNorm ρ π (fun _ => 1) (fun v => Y v - Z v) := by
  have hπ' : ∀ v, 0 < π v / (1 : ℝ) ^ 2 := fun v => by simpa using hπ v
  have h := CycleComparison.Reconstruction.sqrt_massNormSq_add_le
    (E := fun v : CompIn S => hr v.1.root) (fun _ => k) ρ (fun v => π v / (1 : ℝ) ^ 2) hπ'
    (fun v => X v - Y v) (fun v => Y v - Z v)
  have he : (fun v => (X v - Y v + (Y v - Z v)).val) = fun v => (X v - Z v).val := by
    funext v
    rw [sub_add_sub_cancel]
  unfold weightedNorm
  rw [he] at h
  exact h

/-- **The initial discrepancy**: the triangle inequality through `g = P_term V(a_M)`, with
bound 3 of the preparation, the quiet entrance and bound 1. -/
theorem initialDiscrepancy_le {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {law : BirthLaw}
    {M Kw Kout k₀ : ℕ} (hk₀w : k₀ ≤ Kw) (hk₀o : k₀ ≤ Kout) {cr cK CP QT Cb : ℝ}
    {f : Vec 2 → ℝ} {Gw : GenStage D ScalarH Dm b j₀} {aM tp : ℝ}
    {Pterm : (∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn Gw.comps, TorusHk Kout (ScalarH v.1.root))}
    {V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root)}
    {û : ∀ v : CompIn Gw.comps, ℝ → TorusHk k₀ (ScalarH v.1.root)}
    (hπ : ∀ v, 0 < Gw.mass law v) (hCb : 0 ≤ Cb) (hP0 : 0 ≤ D.eps (M - 1) ^ (QT / 2))
    (hpb : IsTerminalPrepBounds law M Kw Kout k₀ hk₀w hk₀o cr cK CP QT f Gw aM tp Pterm V)
    (hb : weightedNorm (D.termRStar cK M) (Gw.mass law) (fun _ => 1)
        (fun v => truncateTorusHk hk₀o (Pterm (fun v => V v aM) v) - û v tp) ≤
      Cb * D.eps (M - 1) ^ (QT / 2) *
        weightedNorm (D.termRho cr M) (Gw.mass law) (fun _ => 1) (Pterm fun v => V v aM)) :
    weightedNorm (D.termRStar cK M) (Gw.mass law) (fun _ => 1)
        (fun v => truncateTorusHk hk₀w (V v tp) - û v tp) ≤
      CP * D.eps (M - 1) ^ (QT / 2) * Real.sqrt (l2NormSq f) +
        Cb * D.eps (M - 1) ^ (QT / 2) * (CP * Real.sqrt (l2NormSq f)) := by
  have htri := weightedNorm_sub_le (hr := ScalarH) (S := Gw.comps) (D.termRStar cK M)
    (Gw.mass law) hπ (fun v => truncateTorusHk hk₀w (V v tp))
    (fun v => truncateTorusHk hk₀o (Pterm (fun v => V v aM) v)) (fun v => û v tp)
  exact htri.trans (add_le_add hpb.2.2
    (hb.trans (mul_le_mul_of_nonneg_left hpb.1 (mul_nonneg hCb hP0))))

/-- The quiet entrance at a level at `Q = Q_T/2`, in the expanded forms of the bundled data
(`termD0bar …` for `A.Dt`, `max Kout (…)` for `A.Khat Kout`). -/
def EntranceAtM {X : TermConstruction} (A : TermArgs X) (Kout sXT sZT : ℕ) (nW : ℕ+)
    (cr cK CL Cχ : ℝ) (kW : InvConsts) (Cb : ℝ) (j₀ M : ℕ) : Prop :=
  ∀ D : OCData, IsTermData X A.Λ M D →
        ∀ (a : ℝ) (lawW : BirthLaw) (PW : ProvParams) (Gw : GenStage D ScalarH (termD0bar A.NT A.pT A.DW A.dW) A.bw j₀) (aM : ℝ),
          IsWeakStage lawW PW A.φ₀ A.hφ₀ M (M + A.Jw) A.Jw A.dW A.DW nW kW a A.T₀ A.σw CL Cχ A.χw
            Gw aM →
        ∀ tp : ℝ, aM + ocTauP D.α D.q D.Λ M ≤ tp → tp ≤ a + A.T₀ →
          Set.Icc (tp - ocTauP D.α D.q D.Λ M) (tp + ocTauP D.α D.q D.Λ M) ⊆
            ocQuietTimes D.α D.q D.Λ D.ζ M →
        ∀ (Gt : GenStage D ScalarH (termD0bar A.NT A.pT A.DW A.dW) A.bw j₀), Gw.comps ⊆ Gt.comps →
        ∀ (g : ∀ v : CompIn Gw.comps, TorusHk (max Kout (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) (ScalarH v.1.root))
          (Z₀ : ∀ v : CompIn Gt.comps, TorusHk (max Kout (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) (ScalarH v.1.root))
          (Z : ∀ v : CompIn Gt.comps, ℝ → TorusHk (max Kout (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) (ScalarH v.1.root)),
          IsTerminalTrace Gw Gt g Z₀ → (∀ v, Z v tp = Z₀ v) →
        ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn Gw.comps) (fun v => ScalarH v.1.root))
          (PZ : ∀ v : CompIn Gw.comps, ℝ → TorusHk (max Kout (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2)) - 2 * A.pT) (ScalarH v.1.root))
          (aRep : ℝ → Vec 2 → ∀ v : CompIn Gw.comps, ScalarH v.1.root)
          (û : ∀ v : CompIn Gw.comps, ℝ → TorusHk A.k₀ (ScalarH v.1.root)),
          IsTerminalLiftedField Gw Gt M A.pT (max Kout (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) A.NT A.dW sXT sZT A.η₀ tp (a + A.T₀) cr
            Z CcT PZ aRep û →
          weightedNorm (D.termRStar cK M) (Gw.mass lawW) (fun _ => 1)
              (fun v => truncateTorusHk (le_trans (by omega : A.k₀ ≤ 2 * A.k₀ + 2)
                (le_trans (le_max_left _ _) (le_max_right Kout _))) (g v) - û v tp) ≤
            Cb * D.eps (M - 1) ^ (A.QT / 2) * weightedNorm (D.termRho cr M) (Gw.mass lawW) (fun _ => 1) g

/-- The at-level body of `TerminalQuietEntranceStatement` at `Q = Q_T/2` is `EntranceAtM`. -/
theorem entranceAtM_of {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT : ℕ} {nW : ℕ+}
    {cr cK CL Cχ : ℝ} {kW : InvConsts} {Cb : ℝ} {j₀ M : ℕ}
    (h : ∀ D : OCData, IsTermData X A.Λ M D →
  ∀ (a : ℝ) (lawW : BirthLaw) (PW : ProvParams) (Gw : GenStage D ScalarH A.Dt A.bw j₀) (aM : ℝ),
    IsWeakStage lawW PW A.φ₀ A.hφ₀ M (M + A.Jw) A.Jw A.dW A.DW nW kW a A.T₀ A.σw CL Cχ A.χw
      Gw aM →
  ∀ tp : ℝ, aM + ocTauP D.α D.q D.Λ M ≤ tp → tp ≤ a + A.T₀ →
    Set.Icc (tp - ocTauP D.α D.q D.Λ M) (tp + ocTauP D.α D.q D.Λ M) ⊆
      ocQuietTimes D.α D.q D.Λ D.ζ M →
  ∀ (Gt : GenStage D ScalarH A.Dt A.bw j₀), Gw.comps ⊆ Gt.comps →
  ∀ (g : ∀ v : CompIn Gw.comps, TorusHk (A.Khat Kout) (ScalarH v.1.root))
    (Z₀ : ∀ v : CompIn Gt.comps, TorusHk (A.Khat Kout) (ScalarH v.1.root))
    (Z : ∀ v : CompIn Gt.comps, ℝ → TorusHk (A.Khat Kout) (ScalarH v.1.root)),
    IsTerminalTrace Gw Gt g Z₀ → (∀ v, Z v tp = Z₀ v) →
  ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn Gw.comps) (fun v => ScalarH v.1.root))
    (PZ : ∀ v : CompIn Gw.comps, ℝ → TorusHk (A.Khat Kout - 2 * A.pT) (ScalarH v.1.root))
    (aRep : ℝ → Vec 2 → ∀ v : CompIn Gw.comps, ScalarH v.1.root)
    (û : ∀ v : CompIn Gw.comps, ℝ → TorusHk A.k₀ (ScalarH v.1.root)),
    IsTerminalLiftedField Gw Gt M A.pT (A.Khat Kout) A.NT A.dW sXT sZT A.η₀ tp (a + A.T₀) cr
      Z CcT PZ aRep û →
    weightedNorm (D.termRStar cK M) (Gw.mass lawW) (fun _ => 1)
        (fun v => truncateTorusHk (le_trans (by omega : A.k₀ ≤ 2 * A.k₀ + 2)
          (le_trans (le_max_left _ _) (le_max_right Kout _))) (g v) - û v tp) ≤
      Cb * D.eps (M - 1) ^ (A.QT / 2) * weightedNorm (D.termRho cr M) (Gw.mass lawW) (fun _ => 1) g) :
    EntranceAtM A Kout sXT sZT nW cr cK CL Cχ kW Cb j₀ M := h

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- **The terminal error energy at a level** from the residual statement, the forced energy
bound, the quiet entrance (at `Q = Q_T/2`), the bill scale and the entrance. -/
theorem energyAtM_of_parts (hq : 1 < X.q) (hΛ : 128 ≤ A.Λ) (hQ : A.QT / 2 ≤ A.QT + 2)
    {C₈ cgap Cg Ca Cb Cd : ℝ} (hC₈ : 0 ≤ C₈) (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hCd : 0 ≤ Cd)
    (hcP : 0 < cP)
    (hres : ResidualAtM A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP C₈
      cgap Cg Ce Cw cker j₀ M)
    (hfe : ∀ D : OCData, IsTermData X A.Λ M D →
        ∀ (a : ℝ) (lawW : BirthLaw) (PW : ProvParams) (Gw : GenStage D ScalarH A.Dt A.bw j₀) (aM : ℝ),
          IsWeakStage lawW PW A.φ₀ A.hφ₀ M (M + A.Jw) A.Jw A.dW A.DW nW kW a A.T₀ A.σw CL Cχ A.χw
            Gw aM →
        ∀ tp : ℝ, aM ≤ tp → tp ≤ a + A.T₀ →
        ∀ (e₀ : ∀ v : CompIn Gw.comps, TorusHk A.k₀ (ScalarH v.1.root))
          (F : ∀ v : CompIn Gw.comps, ℝ → TorusHk A.k₀ (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
          (g U : ∀ v : CompIn Gw.comps, ℝ → TorusHk A.k₀ (ScalarH v.1.root))
          (W : ∀ v : CompIn Gw.comps, ℝ → TorusHk (A.k₀ + 1) (ScalarH v.1.root))
          (Y : ∀ v u (_ : Gw.fam.Γ v u), ℝ → TorusHk (A.k₀ + A.Dt - 1) (ScalarH u.1.root)),
          (∀ v, AEStronglyMeasurable (F v) (volume.restrict (Set.Icc tp (a + A.T₀)))) →
          (∀ v, AEStronglyMeasurable (g v) (volume.restrict (Set.Icc tp (a + A.T₀)))) →
          Gw.IsRegSolution PW (A.Kw_ D M nW) (A.Kw_ D M nW) A.φ₀ A.hφ₀ (D.κ M) (streamVel (D.Φ M))
            A.k₀ tp (a + A.T₀) e₀ F g U W Y →
        ∀ Xr : ℝ, 0 ≤ Xr →
          (∀ j, j ≤ A.k₀ → ∀ β : DerivativeWord2 j,
            residualNorm (D.κ M) (Gw.mass lawW) (Set.Icc tp (a + A.T₀))
                (fun t x i v => D.termRStar cK M ^ j • (torusJetOrder (F v t) j β x) i)
                (fun t x v => D.termRStar cK M ^ j • torusJetOrder (g v t) j β x) ≤
              ENNReal.ofReal Xr) →
          strongEnergy (D.termRStar cK M) (D.κ M) (Gw.mass lawW) tp (a + A.T₀) U W ≤
            ENNReal.ofReal (Ca * (weightedNorm (D.termRStar cK M) (Gw.mass lawW) (fun _ => 1) e₀ + Xr)))
    (hqe : EntranceAtM A Kout sXT sZT nW cr cK CL Cχ kW Cb j₀ M)
    (hbill : ∀ D : OCData, IsTermData X A.Λ M D → ∀ tp tf : ℝ, tf - tp ≤ A.T₀ →
      termBill D M A.NT A.pT A.RT A.AT A.LcT A.LoT A.LfT (termAlphabet A.NT A.pT A.DW A.dW)
        cr A.σw A.χw A.η₀ A.tT cgap Cg tp tf ≤ Cd * D.eps (M - 1) ^ (A.QT + 2))
    (hent : ∀ aM tp : ℝ, aM + cP * ocTauPP X.α X.q A.Λ M ≤ tp → aM + ocTauP X.α X.q A.Λ M ≤ tp)
    (hE : ∀ D : OCData, IsTermData X A.Λ M D → 0 < D.eps (M - 1) ∧ D.eps (M - 1) ≤ 1) :
    EnergyAtM A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP
      (Ca * (CP + Cb * CP + C₈ * Cd)) Ce Cw cker j₀ M := by
  intro D hα hq' hΛ' hζ hΦ hκ hterm a lawW PW Gw aM Ww hst tp Pterm lawT Gt' hprep hlaw hact hcert
    f θ U₀ U V Uw Vw Uk Vk hpair hread hpb Z₀ Z Zw Zk htr hZreg CcT PZ aRep û ŵ hlift hŵ
  have hD : IsTermData X A.Λ M D := ⟨hα, hq', hΛ', hζ, hΦ, hκ, hterm⟩
  by_cases hw : tp ≤ a + A.T₀
  swap
  · rw [strongEnergy_eq_zero_of_lt _ _ _ (not_le.1 hw)]
    exact zero_le
  have hob1 := hE D hD
  obtain ⟨hE0, hE1⟩ := hob1
  have hH : 0 < D.termH M := Construction.Stream.ocTauPP_pos (by omega)
  have haM : aM ≤ tp := by
    have h1 := hprep.2.1
    have h2 : 0 < cP * D.termH M := mul_pos hcP hH
    linarith
  -- the residual statement: the error equation and its residual
  have hob2 := hres D hα hq' hΛ' hζ hΦ hκ hterm a lawW PW Gw aM
    Ww hst tp Pterm lawT Gt' hprep hlaw hact hcert f θ U₀ U V Uw Vw Uk Vk hpair hread hpb Z₀ Z Zw Zk
    htr hZreg CcT PZ aRep û ŵ hlift hŵ
  obtain ⟨Rres, qres, ek, hreg, hresn, hRm, hqm⟩ := hob2
  -- the forced energy bound with `X_r = max 0 (C₈ · bill · ‖f‖₂)`
  have hfa := hfe D hD a lawW PW Gw aM hst tp haM hw _ Rres qres _ _ ek hRm hqm hreg
    (max 0 (C₈ * termBill D M A.NT A.pT A.RT A.AT A.LcT A.LoT A.LfT
      (termAlphabet A.NT A.pT A.DW A.dW) cr A.σw A.χw A.η₀ A.tT cgap Cg tp (a + A.T₀) *
        Real.sqrt (l2NormSq f))) (le_max_left _ _)
    (fun j hj β => (hresn j hj β).trans (ENNReal.ofReal_le_ofReal (le_max_right _ _)))
  refine hfa.trans (ENNReal.ofReal_le_ofReal ?_)
  -- the initial discrepancy
  have hπ : ∀ v, 0 < Gw.mass lawW v := fun v => by
    show 0 < compMass D.q D.Λ lawW v.1
    rw [hq', hΛ']
    exact Construction.Preservation.Buffer.birth_compMass_pos hq hΛ lawW v.1
  have hent' : aM + ocTauP D.α D.q D.Λ M ≤ tp := by
    have h1 : aM + cP * ocTauPP X.α X.q A.Λ M ≤ tp := by
      rw [← hα, ← hq', ← hΛ']
      exact hprep.2.1
    have h2 := hent aM tp h1
    rw [← hα, ← hq', ← hΛ'] at h2
    exact h2
  have hb := hqe D hD a lawW PW Gw aM hst tp hent' hw hprep.2.2.2.2 (Gt'.retained M 1 A.RT)
    (weak_comps_subset_retained hact hst.2.2.2.2.1 M 1) (Pterm fun v => V v aM) Z₀ Z htr
    hZreg.2.2.2.1 CcT PZ aRep û hlift
  have hP0 : 0 ≤ D.eps (M - 1) ^ (A.QT / 2) := Real.rpow_nonneg hE0.le _
  have he₀ := initialDiscrepancy_le hk₀w (le_trans (by omega : A.k₀ ≤ 2 * A.k₀ + 2)
    (le_trans (le_max_left _ _) (le_max_right Kout _))) hπ hCb hP0 hpb hb
  -- the bill scale
  have hbl := hbill D hD tp (a + A.T₀) (by linarith [hst.1])
  have hpow : D.eps (M - 1) ^ (A.QT + 2) ≤ D.eps (M - 1) ^ (A.QT / 2) :=
    Real.rpow_le_rpow_of_exponent_ge hE0 hE1 hQ
  have hs : 0 ≤ Real.sqrt (l2NormSq f) := Real.sqrt_nonneg _
  have hXr : max 0 (C₈ * termBill D M A.NT A.pT A.RT A.AT A.LcT A.LoT A.LfT
      (termAlphabet A.NT A.pT A.DW A.dW) cr A.σw A.χw A.η₀ A.tT cgap Cg tp (a + A.T₀) *
        Real.sqrt (l2NormSq f)) ≤ C₈ * Cd * D.eps (M - 1) ^ (A.QT / 2) * Real.sqrt (l2NormSq f) := by
    have h1 : C₈ * Cd * D.eps (M - 1) ^ (A.QT / 2) * Real.sqrt (l2NormSq f) =
        C₈ * (Cd * D.eps (M - 1) ^ (A.QT / 2)) * Real.sqrt (l2NormSq f) := by ring
    rw [h1]
    refine max_le (mul_nonneg (mul_nonneg hC₈ ?_) hs) ?_
    · exact mul_nonneg hCd hP0
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hbl.trans
        (mul_le_mul_of_nonneg_left hpow hCd)) hC₈) hs
  calc Ca * (weightedNorm (D.termRStar cK M) (Gw.mass lawW) (fun _ => 1)
          (fun v => truncateTorusHk hk₀w (V v tp) - û v tp) +
        max 0 (C₈ * termBill D M A.NT A.pT A.RT A.AT A.LcT A.LoT A.LfT
          (termAlphabet A.NT A.pT A.DW A.dW) cr A.σw A.χw A.η₀ A.tT cgap Cg tp (a + A.T₀) *
            Real.sqrt (l2NormSq f)))
      ≤ Ca * (CP * D.eps (M - 1) ^ (A.QT / 2) * Real.sqrt (l2NormSq f) +
          Cb * D.eps (M - 1) ^ (A.QT / 2) * (CP * Real.sqrt (l2NormSq f)) +
          C₈ * Cd * D.eps (M - 1) ^ (A.QT / 2) * Real.sqrt (l2NormSq f)) :=
        mul_le_mul_of_nonneg_left (add_le_add he₀ hXr) hCa
    _ = Ca * (CP + Cb * CP + C₈ * Cd) * D.eps (M - 1) ^ (A.QT / 2) * Real.sqrt (l2NormSq f) := by
        ring

/-- `0 < E ≤ 1` for the parent wavelength of the terminal data. -/
theorem termEps_basic {X : TermConstruction} {Λ M : ℕ} (hq : 1 < X.q) (hΛ : 128 ≤ Λ) {D : OCData}
    (hD : IsTermData X Λ M D) : 0 < D.eps (M - 1) ∧ D.eps (M - 1) ≤ 1 := by
  obtain ⟨-, hDq, hDΛ, -⟩ := hD
  have h := Scales.epsilon_basic (m := M - 1) hq hΛ
  show 0 < ocEpsilon D.q D.Λ (M - 1) ∧ ocEpsilon D.q D.Λ (M - 1) ≤ 1
  rw [hDq, hDΛ]
  exact ⟨h.1, h.2.1⟩

/-- `Q_T/2 ≤ Q_T + 2` from the schedule. -/
theorem termQT_half_le {X : TermConstruction} {A : TermArgs X} (hV : A.Valid) :
    A.QT / 2 ≤ A.QT + 2 := by
  obtain ⟨-, -, -, -, hPT, hsched, -⟩ := hV
  have h := hsched.2.1
  have hq0 : 0 < X.q := lt_trans one_pos X.hq.1
  have hp : 0 < X.q ^ (A.Jw + 1) * (1 + X.s) := mul_pos (pow_pos hq0 _) (by linarith [X.hs₀])
  linarith

/-- **The terminal error energy over the bundled data from its parts**: the residual statement
(with `0 ≤ C`), the forced energy bound, the quiet entrance, the bill scale and the entrance lemma.
Constants: `C = C_a (C_P + C_b C_P + C₈ C_d)`; `K_need` is that of the residual statement raised to
`k₀`. -/
theorem errorEnergyBundled_of_parts (hres : ResidualBundled) (hfe : TerminalForcedEnergyStatement)
    (hqe : TerminalQuietEntranceStatement) (hbill : TermBillScaleStatement) :
    ErrorEnergyBundled := by
  intro X
  have hob3 := hres X
  obtain ⟨Λ₁, h1, hR⟩ := hob3
  have hob4 := hfe X
  obtain ⟨Λ₂, -, hF⟩ := hob4
  have hob5 := hqe X
  obtain ⟨Λ₃, -, hQ⟩ := hob5
  have hob6 := hbill X
  obtain ⟨Λ₄, -, hB⟩ := hob6
  have hq1 : 1 < X.q := X.hq.1
  have hδ : 0 < ocDelta X.α X.q :=
    (Scales.admissible_exponent_facts X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq).2.1
  refine ⟨max (max Λ₁ Λ₂) (max Λ₃ Λ₄), le_trans h1 (le_trans (le_max_left _ _) (le_max_left _ _)),
    fun A hΛ hV => ?_⟩
  have hΛ1 : Λ₁ ≤ A.Λ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hΛ
  have hΛ2 : Λ₂ ≤ A.Λ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hΛ
  have hΛ3 : Λ₃ ≤ A.Λ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hΛ
  have hΛ4 : Λ₄ ≤ A.Λ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hΛ
  have h128 : 128 ≤ A.Λ := le_trans h1 hΛ1
  have hQT := termQT_half_le hV
  have hob7 := hR A hΛ1 hV
  obtain ⟨SX₁, SZ₁, Kf₁, hR⟩ := hob7
  have hob8 := hQ A hΛ3 hV
  obtain ⟨SX₃, SZ₃, Kf₃, hQ⟩ := hob8
  refine ⟨max SX₁ SX₃, max SZ₁ SZ₃, max Kf₁ Kf₃, fun sXT sZT hsX hsZ Kout hK => ?_⟩
  have hob9 := hR sXT sZT (le_trans (le_max_left _ _) hsX)
    (le_trans (le_max_left _ _) hsZ) Kout (le_trans (le_max_left _ _) hK)
  obtain ⟨Kneed, hR⟩ := hob9
  have hQ := hQ sXT sZT (le_trans (le_max_right _ _) hsX) (le_trans (le_max_right _ _) hsZ) Kout
    (le_trans (le_max_right _ _) hK)
  refine ⟨max Kneed A.k₀, fun Kw Lt nW hk₀w hLw cr kS hKw hL0 hLp hLn hord hcr hcr1 hcr' hkScr
    hkSc0 hKs hKan hLan hJm cK CK CL Cχ Cread Cid kW hcK hc0 halloc hG0 hLs cP CP cHP hcP hcH1 => ?_⟩
  have hG0' : kW.G0 ≤ kW.Hprod + 1 := le_trans hG0 (Nat.le_succ _)
  have hKs' : A.k₀ ≤ kW.Ks := le_trans (le_max_right _ _) (le_trans hKs halloc.1)
  have hob10 := hR Kw Lt nW hk₀w hLw cr kS
    (le_trans (le_max_left _ _) hKw) hL0 hLp hLn hord hcr hcr1 hcr' hkScr hkSc0
    (le_trans (le_max_left _ _) hKs) (le_trans (le_max_left _ _) hKan)
    (le_trans (le_max_left _ _) hLan) (le_trans (le_max_left _ _) hJm) cK CK CL Cχ Cread Cid kW hcK
    hc0 halloc hG0 hLs cP CP cHP hcP hcH1
  obtain ⟨Cw₀, hR⟩ := hob10
  refine ⟨Cw₀, fun Cw Ce cker hCw => ?_⟩
  have hob11 := hR Cw Ce cker hCw
  obtain ⟨C, cgap, Cg, hC, hcgap, CHt, Υt, hCHt, hΥt, hRj⟩ := hob11
  have hob12 := hF A hΛ2 hV nW cK CL Cχ kW hcK hc0 hKs' hG0'
  obtain ⟨Ca, hCa, hFj⟩ := hob12
  have hob13 := hQ nW cr cK CL Cχ kW hcr hcr1 hcK hc0 hKs' hG0' (A.QT / 2)
  obtain ⟨Cb, hCb, hQj⟩ := hob13
  have hob14 := hB A hΛ4 hV cr cgap Cg hcr hcr1 hcgap
  obtain ⟨Cd, hCd, MB, hBM⟩ := hob14
  refine ⟨Ca * (CP + Cb * CP + C * Cd), CHt, Υt, hCHt, hΥt, fun j₀ hj₀ => ?_⟩
  have hob15 := hRj j₀ hj₀
  obtain ⟨MR, hRM⟩ := hob15
  have hob16 := hFj j₀
  obtain ⟨MF, hFM⟩ := hob16
  have hob17 := hQj j₀
  obtain ⟨MQ, hQM⟩ := hob17
  have hob18 := Ingredients.Recon.entrance_of_prep_eventually hq1 h128 hδ hcP
  obtain ⟨ME, hEM⟩ := hob18
  refine ⟨max (max MR MF) (max (max MQ MB) ME), fun M hM => ?_⟩
  have hMR : MR ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hM
  have hMF : MF ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hM
  have hMQ : MQ ≤ M :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hM
  have hMB : MB ≤ M :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hM
  have hME : ME ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hM
  exact energyAtM_of_parts hq1 h128 hQT hC hCa hCb hCd hcP (hRM M hMR) (hFM M hMF)
    (entranceAtM_of (hQM M hMQ)) (hBM M hMB) (hEM M hME) fun D hD => termEps_basic hq1 h128 hD

end AVRegularity.EntryTerminal.Route
end
end

section
@[expose] public noncomputable section
open AVRegularity AVRegularity.EntryTerminal.Route
namespace AVRegularity.Construction.Residual.Presentation

/-! **The bounds of the terminal residual from the five bound statements.**
`termResidualBound_of_parts` assembles the residual bound at one context. This module joins the
prefixes:
- the three flux statements (covariance truncation, inner flux, coarse filter tails) by `termFluxPrefix_and`; their common constant becomes
  the flux constant `C_fl` of the reconstruction;
- the reconstruction statement at the offset `ℓ = 0`, which chooses `C₀, c_gap, C_g` after `C_fl`;
- the fine matrix tail.

The constant of the residual bound is `3·k₀!·C` (`termResidualBound_of_parts`), so the statement's `C` is
reached as `3·k₀!·(C / (3·k₀!))`. The masses of the weak stage are positive by
`birth_compMass_pos`. For `k₀ = 0` the factor is `3`, and a statement true for every constant has
threshold `0`. -/

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- The masses of the weak stage are positive. -/
theorem termCtx_mass_pos
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (h128 : 128 ≤ A.Λ) : ∀ v, 0 < c.Gw.mass c.lawW v := by
  obtain ⟨-, hq, hΛD, -, -, -, -⟩ := c.data
  exact fun v => Construction.Preservation.Buffer.birth_compMass_pos (hq ▸ X.hq.1) (hΛD ▸ h128)
    c.lawW v.1

private theorem max3_l {a b c n : ℕ} (h : max a (max b c) ≤ n) : a ≤ n := le_trans (le_max_left _ _) h
private theorem max3_m {a b c n : ℕ} (h : max a (max b c) ≤ n) : b ≤ n :=
  le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h
private theorem max3_r {a b c n : ℕ} (h : max a (max b c) ≤ n) : c ≤ n :=
  le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) h

/-- **The residual bound from the five bound statements.** -/
theorem termResidualBound_of_steps (h2a : TermCovTruncStatement) (h2b : TermFrontierStatement)
    (h3 : TermFilterStatement) (hrec : TermReconStatement) (hfine : TermFineTailStatement) :
    TermResidualBoundStatement := by
  have hF := termFluxPrefix_and (P₁ := fun c x kc C => TermCovTruncAt c x kc C)
    (P₂ := fun c x kc C => TermFrontierAt c x kc C ∧ TermFilterAt c x kc C) h2a
    (termFluxPrefix_and (P₁ := fun c x kc C => TermFrontierAt c x kc C)
      (P₂ := fun c x kc C => TermFilterAt c x kc C) h2b h3)
  have hR := hrec 0
  intro X
  obtain ⟨Λ₁, h128, hF⟩ := hF X
  obtain ⟨Λ₂, -, hR⟩ := hR X
  obtain ⟨Λ₃, -, hT⟩ := hfine X
  refine ⟨max Λ₁ (max Λ₂ Λ₃), le_trans h128 (le_max_left _ _), fun A hΛ hV => ?_⟩
  have hΛA : 128 ≤ A.Λ := le_trans h128 (max3_l hΛ)
  obtain ⟨hAnn, hTnn, -⟩ := scaleFacts X A.Λ hΛA
  obtain ⟨kc₁, hF⟩ := hF A (max3_l hΛ) hV
  obtain ⟨kc₂, hR⟩ := hR A (max3_m hΛ) hV
  obtain ⟨kc₃, hT⟩ := hT A (max3_r hΛ) hV
  refine ⟨max kc₁ (max kc₂ kc₃), fun kc hkc => ?_⟩
  obtain ⟨SX₁, SZ₁, Kf₁, hF⟩ := hF kc (max3_l hkc)
  obtain ⟨SX₂, SZ₂, Kf₂, hR⟩ := hR kc (max3_m hkc)
  obtain ⟨SX₃, SZ₃, Kf₃, hT⟩ := hT kc (max3_r hkc)
  refine ⟨max SX₁ (max SX₂ SX₃), max SZ₁ (max SZ₂ SZ₃), max Kf₁ (max Kf₂ Kf₃),
    fun sXT sZT hX hZ Kout hK => ?_⟩
  obtain ⟨Kn₁, hF⟩ := hF sXT sZT (max3_l hX) (max3_l hZ) Kout (max3_l hK)
  obtain ⟨Kn₂, hR⟩ := hR sXT sZT (max3_m hX) (max3_m hZ) Kout (max3_m hK)
  obtain ⟨Kn₃, hT⟩ := hT sXT sZT (max3_r hX) (max3_r hZ) Kout (max3_r hK)
  refine ⟨max Kn₁ (max Kn₂ Kn₃), ?_⟩
  intro Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hKO hcr0 hcr1 hcr hkS hc0 hKs hKan hLan hJm
    cK CK CL Cχ Cread Cid kW hcK hkW hAl cP CP cHP Cw Ce cker hcP _Cfl
  obtain ⟨CF, _cg₁, _Cg₁, _hcg₁, CH₁, Υ₁, hCH₁, hΥ₁, TF⟩ := hF Kw Lt nW hk₀w hLw cr kS
    (max3_l hKn) hL0 hLp hLt hKO hcr0 hcr1 hcr hkS hc0 (max3_l hKs) (max3_l hKan) (max3_l hLan)
    (max3_l hJm) cK CK CL Cχ Cread Cid kW hcK hkW hAl cP CP cHP Cw Ce cker hcP 0
  obtain ⟨CR, cgap, Cg, hcgap, CH₂, Υ₂, hCH₂, hΥ₂, TR⟩ := hR Kw Lt nW hk₀w hLw cr kS
    (max3_m hKn) hL0 hLp hLt hKO hcr0 hcr1 hcr hkS hc0 (max3_m hKs) (max3_m hKan) (max3_m hLan)
    (max3_m hJm) cK CK CL Cχ Cread Cid kW hcK hkW hAl cP CP cHP Cw Ce cker hcP (max CF 0)
  obtain ⟨CT, _cg₃, _Cg₃, _hcg₃, CH₃, Υ₃, hCH₃, hΥ₃, TT⟩ := hT Kw Lt nW hk₀w hLw cr kS
    (max3_r hKn) hL0 hLp hLt hKO hcr0 hcr1 hcr hkS hc0 (max3_r hKs) (max3_r hKan) (max3_r hLan)
    (max3_r hJm) cK CK CL Cχ Cread Cid kW hcK hkW hAl cP CP cHP Cw Ce cker hcP 0
  have hk0 : (0 : ℝ) < 3 * (A.k₀.factorial : ℝ) := by positivity
  refine ⟨3 * (A.k₀.factorial : ℝ) * max (max CR CT) 0, cgap, Cg, hcgap,
    max CH₁ (max CH₂ CH₃), max Υ₁ (max Υ₂ Υ₃), le_trans hCH₁ (le_max_left _ _),
    lt_of_lt_of_le hΥ₁ (le_max_left _ _), ?_⟩
  intro C hC j₀ hj₀
  have hC' : max (max CR CT) 0 ≤ C / (3 * (A.k₀.factorial : ℝ)) :=
    (le_div_iff₀ hk0).2 (by rw [mul_comm]; exact hC)
  have hj₁ : IsCarrierStart X.α X.q A.Λ A.bw CH₁ Υ₁ j₀ :=
    IsCarrierStart.mono hAnn hTnn (le_max_left _ _) (le_max_left _ _) (zero_le_one.trans hCH₁)
      hΥ₁.le hj₀
  have hj₂ : IsCarrierStart X.α X.q A.Λ A.bw CH₂ Υ₂ j₀ :=
    IsCarrierStart.mono hAnn hTnn (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_trans (le_max_left _ _) (le_max_right _ _)) (zero_le_one.trans hCH₂) hΥ₂.le hj₀
  have hj₃ : IsCarrierStart X.α X.q A.Λ A.bw CH₃ Υ₃ j₀ :=
    IsCarrierStart.mono hAnn hTnn (le_trans (le_max_right _ _) (le_max_right _ _))
      (le_trans (le_max_right _ _) (le_max_right _ _)) (zero_le_one.trans hCH₃) hΥ₃.le hj₀
  obtain ⟨M₁, UF⟩ := TF (max CF 0) (le_max_left _ _) j₀ hj₁
  obtain ⟨M₂, UR⟩ := TR (C / (3 * (A.k₀.factorial : ℝ)))
    (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hC') j₀ hj₂
  obtain ⟨M₃, UT⟩ := TT (C / (3 * (A.k₀.factorial : ℝ)))
    (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hC') j₀ hj₃
  refine ⟨max M₁ (max M₂ M₃), fun M hM c x => ?_⟩
  obtain ⟨ha, hb, hf⟩ := UF M (max3_l hM) c x
  have hres := termResidualBound_of_parts c residualWordsOfMass x (termCtx_mass_pos c hΛA) ha hb hf
    (UR M (max3_m hM) c x) (UT M (max3_r hM) c x)
  have hCC : 3 * (A.k₀.factorial : ℝ) * (C / (3 * (A.k₀.factorial : ℝ))) = C := by
    field_simp
  rw [hCC] at hres
  exact hres

end AVRegularity.Construction.Residual.Presentation
end
end

section
@[expose] public section
namespace AVRegularity.EntryTerminal.Route

/-! **The error energy from the residual and the quiet entrance.** With the forced energy
(`terminalForcedEnergy_of_reserve`) and the bill scale (`termBillScale`) proved, the bundled error
energy needs only the residual (`ResidualBundled`) and the quiet entrance
(`TerminalQuietEntranceStatement`). -/

/-- **The error energy over the bundled data from the residual and the quiet entrance.** -/
theorem errorEnergyBundled_of_residual (hres : ResidualBundled)
    (hqe : TerminalQuietEntranceStatement) : ErrorEnergyBundled :=
  errorEnergyBundled_of_parts hres terminalForcedEnergy_of_reserve hqe BillScale.termBillScale

end AVRegularity.EntryTerminal.Route
end
end

section
@[expose] public noncomputable section
open AVRegularity.Construction.Residual.Presentation
namespace AVRegularity.EntryTerminal.Route

/-! **The residual from its bounds and their conversion.** `ResidualBundled` follows
from two inputs: the bounds of the terminal residual with the prefix
(`TermResidualBoundStatement`, the join of the five flux and reconstruction statements), and their
conversion to the clauses of the statement (`TermResClausesStatement`).

The prefix of `ResidualBundled` differs from `TermResPrefix` in two ways:
- the reserve premises (`G₀ ≤ H_prod`, the weight floor, `c_{H,P} ≤ 1`);
- the threshold `C_w ≥ C_{w,0}`.

Both serve to build `TermResAux` (`termResAux_of`); the certificate of `Gt'` comes from 
`termCertBlock_exists` at `c_H = c_{H,P}`. If `c_{H,P} ≤ 0`, no data exist (the terminal law has
`c_H > 0`), and the statement is vacuous. In particular, for `c_{H,P} ≤ 0` every constant works. -/

/-- **`ResidualBundled` from the residual bounds and their conversion.** -/
theorem residualBundled_of_steps (hB : TermResidualBoundStatement)
    (hC : TermResClausesStatement) : ResidualBundled := by
  intro X
  obtain ⟨Λ₁, h128, hB⟩ := hB X
  obtain ⟨Λ₂, -, hC⟩ := hC X
  obtain ⟨Λc, -, hcertB⟩ := termCertBlock_exists X
  refine ⟨max (max Λ₁ Λ₂) Λc, le_trans h128 (le_trans (le_max_left _ _) (le_max_left _ _)),
    fun A hΛ hV => ?_⟩
  have hΛ1 : Λ₁ ≤ A.Λ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hΛ
  have hΛ2 : Λ₂ ≤ A.Λ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hΛ
  have hΛ3 : Λc ≤ A.Λ := le_trans (le_max_right _ _) hΛ
  have hΛ128 : 128 ≤ A.Λ := le_trans h128 hΛ1
  have hΛone : 1 ≤ A.Λ := le_trans (by norm_num) hΛ128
  obtain ⟨kc₁, hB⟩ := hB A hΛ1 hV
  obtain ⟨kc₂, hC⟩ := hC A hΛ2 hV
  obtain ⟨SX₁, SZ₁, Kf₁, hB⟩ := hB (max kc₁ kc₂) (le_max_left _ _)
  obtain ⟨SX₂, SZ₂, Kf₂, hC⟩ := hC (max kc₁ kc₂) (le_max_right _ _)
  refine ⟨max (max SX₁ SX₂) (max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2),
    max (max SZ₁ SZ₂) (max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2), max Kf₁ Kf₂,
    fun sXT sZT hX hZ Kout hK => ?_⟩
  obtain ⟨Kn₁, hB⟩ := hB sXT sZT (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX)
    (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hZ) Kout (le_trans (le_max_left _ _) hK)
  obtain ⟨Kn₂, hC⟩ := hC sXT sZT (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX)
    (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hZ) Kout
    (le_trans (le_max_right _ _) hK)
  refine ⟨max Kn₁ Kn₂, fun Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hko hcr0 hcr1 hcre hcr hc0
    hKs hKan hLan hJm cK CK CL Cχ Cread Cid kW hcK hkW hwa hGH hLs cP CP cHP hcP hcH1 => ?_⟩
  have m1 : ∀ {n : ℕ}, max Kn₁ Kn₂ ≤ n → Kn₁ ≤ n := fun h => le_trans (le_max_left _ _) h
  have m2 : ∀ {n : ℕ}, max Kn₁ Kn₂ ≤ n → Kn₂ ≤ n := fun h => le_trans (le_max_right _ _) h
  by_cases hcH : 0 < cHP
  · have hplan : TermPlanHyp A sXT sZT nW cr kW :=
      ⟨hV, hΛ128, termPlan_lstar hV hLs, hGH, le_trans (le_max_right _ _) hX,
        le_trans (le_max_right _ _) hZ⟩
    obtain ⟨Cw₀, CHe, Υe, hCw₀, hCHe, hΥe, hrest⟩ :=
      hcertB A hΛ3 sXT sZT nW cr kW CL Cχ cP CP hplan hcr0 hcr1 cHP hcH
    refine ⟨Cw₀, fun Cw Ce cker hCw => ?_⟩
    obtain ⟨C₀, cgap, Cg, hcgap, CH₁, Υ₁, hCH₁, hΥ₁, hB⟩ :=
      hB Kw Lt nW hk₀w hLw cr kS (m1 hKn) hL0 hLp hLt hko hcr0 hcr1 hcre hcr hc0 (m1 hKs)
        (m1 hKan) (m1 hLan) (m1 hJm) cK CK CL Cχ Cread Cid kW hcK hkW hwa cP CP cHP Cw Ce cker hcP 0
    obtain ⟨C₂, _cg₂, _Cg₂, _hcg₂, CH₂, Υ₂, hCH₂, hΥ₂, hC⟩ :=
      hC Kw Lt nW hk₀w hLw cr kS (m2 hKn) hL0 hLp hLt hko hcr0 hcr1 hcre hcr hc0 (m2 hKs)
        (m2 hKan) (m2 hLan) (m2 hJm) cK CK CL Cχ Cread Cid kW hcK hkW hwa cP CP cHP Cw Ce cker hcP 0
    refine ⟨max C₀ 0, cgap, Cg, le_max_right _ _, hcgap, max (max CH₁ CH₂) CHe,
      max (max Υ₁ Υ₂) Υe, le_trans hCH₁ (le_trans (le_max_left _ _) (le_max_left _ _)),
      lt_of_lt_of_le hΥ₁ (le_trans (le_max_left _ _) (le_max_left _ _)), fun j₀ hj₀ => ?_⟩
    have hAnn : ∀ k, 0 ≤ ocA X.α X.q A.Λ k := fun k =>
      Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛone).le _
    have hTnn : ∀ k, 0 ≤ ocTauPP X.α X.q A.Λ k := fun k =>
      (Construction.Stream.ocTauPP_pos hΛone).le
    have hj₁ : IsCarrierStart X.α X.q A.Λ A.bw CH₁ Υ₁ j₀ :=
      IsCarrierStart.mono hAnn hTnn (le_trans (le_max_left _ _) (le_max_left _ _))
        (le_trans (le_max_left _ _) (le_max_left _ _)) (zero_le_one.trans hCH₁) hΥ₁.le hj₀
    have hj₂ : IsCarrierStart X.α X.q A.Λ A.bw CH₂ Υ₂ j₀ :=
      IsCarrierStart.mono hAnn hTnn (le_trans (le_max_right _ _) (le_max_left _ _))
        (le_trans (le_max_right _ _) (le_max_left _ _)) (zero_le_one.trans hCH₂) hΥ₂.le hj₀
    have hj₃ : IsCarrierStart X.α X.q A.Λ A.bw CHe Υe j₀ :=
      IsCarrierStart.mono hAnn hTnn (le_max_right _ _) (le_max_right _ _)
        (zero_le_one.trans hCHe) (le_trans (by norm_num) hΥe) hj₀
    obtain ⟨M₁, hB⟩ := hB (max C₀ 0) (le_max_left _ _) j₀ hj₁
    obtain ⟨M₂, hC⟩ := hC C₂ le_rfl j₀ hj₂
    obtain ⟨M₃, hM₃⟩ := hrest Cw hCw j₀ hj₃
    refine ⟨max (max M₁ M₂) M₃, fun M hM => ?_⟩
    exact residualAtM_of_ctx hcre hGH hLs hcH1 (le_trans hCw₀ hCw)
      (fun c => hM₃ M (le_trans (le_max_right _ _) hM) c.D c.a c.lawW c.PW c.Gw c.aM c.tp c.lawT
        c.Gt' ⟨c.data, c.weak, c.prep.1, c.prep.2.1, c.prep.2.2.1, c.law, c.succ⟩)
      (fun c x => hB M (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hM) c x)
      (fun c x => hC M (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hM) c x _ _ _)
  · refine ⟨0, fun Cw Ce cker _ => ⟨0, 1, 1, le_rfl, one_pos, 1, 1, le_rfl, one_pos,
      fun j₀ _ => ⟨0, fun M _ => ?_⟩⟩⟩
    intro D _ _ _ _ _ _ _ a lawW PW Gw aM Ww _ tp Pterm lawT Gt' _ hlaw
    have h := lawT.cH_pos
    rw [hlaw.2.2.1] at h
    exact absurd h hcH

end AVRegularity.EntryTerminal.Route
end
end
end
