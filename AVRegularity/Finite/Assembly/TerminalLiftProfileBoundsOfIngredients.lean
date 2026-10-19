-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Definitions.EntryWeak.WeakReduction
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Definitions.Finite.FiniteLiftBridge
public import AVRegularity.Statements.Intermediate.Readout.HolderNorm
import AVRegularity.Applications.Torus.JointContinuityMain
import AVRegularity.Statements.Intermediate.Readout.ReadoutLemma
import AVRegularity.Finite.WeakLift.RepresentationAdapters
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.Finite.TerminalLift.CovarianceIdentification
import AVRegularity.CycleReference.TransitionZero
import AVRegularity.Construction.Scales.Times

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Finite.Assembly

/-! Named copies of the input statements used by the finite assembly.
Their telescopes and conclusions are copied verbatim from the corresponding statements. -/

/-- Exact quantified statement of `AVRegularity.Providers.entry_terminal`. -/
def EntryTerminalStatement : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ) ,
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (c₀max : ℝ), 0 < c₀max →
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Jw : ℕ) (τ T₀ Pw η₀ : ℝ), 1 ≤ Jw → 0 < τ → τ < T₀ → 0 < Pw → 0 < η₀ →
      η₀ ≤ ocDelta α q / 8 →
    ∃ (Nw Rw Lw : ℕ), 1 ≤ Nw ∧ Lw ≤ Jw * Nw ∧
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

/-- Exact quantified statement of `AVRegularity.Providers.iteration_cascade`. -/
def IterationCascadeStatement : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ) ,
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (K : ℕ) (Pacc t₀ T₀ : ℝ), 3 ≤ K → 0 < Pacc → 0 < t₀ → t₀ < T₀ →
    ∀ (r₀ D₀ : ℕ) (τe lamE σE : ℝ), 0 < τe → 0 < lamE → 0 < σE →
    ∃ (Q : ℝ) (H J N p nk Lc Lf Lpr Acl Naux Nout Kres L : ℕ) (σ₀ a σ : ℝ),
      IsCascadeSchedule α s q K Pacc lamE σE D₀ Q H J N p nk Lc Lf Lpr Acl Naux Nout Kres L σ₀ a σ ∧
      ∀ npad : ℕ, ∃ SX SZ Kneed : ℕ, ∀ sX sZ : ℕ, SX ≤ sX → SZ ≤ sZ →
      CascadeTail α s q ζ Λ c₀max φ₀ hφ₀ bw K Pacc t₀ T₀ r₀ D₀ τe lamE σE Q H J N p nk Lc Lf Lpr
        Naux Nout Kres npad sX sZ Kneed σ₀

/-- Exact quantified statement of `AVRegularity.Providers.terminal_lift_rep`. -/
def TerminalLiftRepStatement : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ) ,
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Jw Nw Rw Lw : ℕ) (T₀ η₀ σw : ℝ), 1 ≤ Jw → 0 < T₀ → 0 < η₀ → η₀ ≤ ocDelta α q / 8 →
      0 < σw → σw < min (ocC α q) (q - 1) →
    ∀ (PT QT : ℝ) (NT pT RT AT k₀ LcT LoT LfT LpT : ℕ) (tT : ℝ),
      IsTerminalSchedule α q s PT QT σw (weakChi α q η₀) η₀ tT Jw Lw k₀ NT pT RT AT LcT LoT LfT
        LpT (termAlphabet NT pT (1 + Jw * Nw) (Jw * Rw)) →
    ∀ Lr : ℕ,
    ∃ SX SZ : ℕ, ∀ sXT sZT : ℕ, SX ≤ sXT → SZ ≤ sZT →
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
      IsRepresentationAt (D.eps (M - 1)) (Lr + (NT + 2 * pT) + 4) r →
      IsRepOf ((Gt'.retained M 1 RT).mass lawT)
        (fun v => truncateTorusHk (Nat.zero_le Kz) (Z v t)) r.value →
    ∃ rT : Representation (CompSpace Gw.comps),
      IsRepresentationAt (D.eps M) (Lr + 3) rT ∧
      rT.base = (r.map (readoutCLM M (D.eps (M - 1)) η₀ (Gw.mass lawW)
        ((Gt'.retained M 1 RT).mass lawT))).base ∧
      (∃ Lcov Llift : List ((Vec 2 → CompSpace Gw.comps) × ℝ),
        rT.profiles = (r.map (readoutCLM M (D.eps (M - 1)) η₀ (Gw.mass lawW)
          ((Gt'.retained M 1 RT).mass lawT))).profiles ++ Lcov ++ Llift ∧
        (∀ g ∈ Lcov, g.2 = D.eps (M - 1)) ∧ ∀ g ∈ Llift, g.2 = D.eps M) ∧
      rT.value = compField (Gw.mass lawW) (termLiftedRep Gw M NT (Jw * Rw) cr CcT aRep t) ∧
      representedSize s (Lr + 3) (D.eps M) rT ≤
        ENNReal.ofReal CT * representedSize s (Lr + (NT + 2 * pT) + 4) (D.eps (M - 1)) r

/-- Exact quantified statement of `AVRegularity.Providers.weak_lift_rep`. -/
def WeakLiftRepStatement : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ) ,
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Jw Nw Rw : ℕ) (η₀ σw : ℝ), 1 ≤ Jw → 1 ≤ Nw → 0 < η₀ → η₀ ≤ ocDelta α q / 8 →
      0 < σw → σw < min (ocC α q) (q - 1) →
    ∀ Lr : ℕ, Jw * Nw ≤ Lr →
    ∃ SX SZ : ℕ, ∀ sX sZ : ℕ, SX ≤ sX → SZ ≤ sZ →
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
      IsRepresentationAt (D.eps M) (Lr + 3) rT → rT.value = compField (Gw.mass lawW) g →
    ∃ rW : Representation (CompSpace (stage (M + Jw)).comps),
      IsRepresentationAt (D.eps (M + Jw)) 3 rW ∧
      (∀ y, compReadoutCLM (fun v => weakMass D Nw Jw η₀ v.1) (fun _ => 1) (rW.value y) =
        W M t (fun v y' => g y' (ιw v)) y) ∧
      representedSize s 3 (D.eps (M + Jw)) rW ≤
        ENNReal.ofReal Cw * representedSize s (Lr + 3) (D.eps M) rT

/-- Exact quantified statement of `AVRegularity.Providers.terminal_seed_transport`. -/
def TerminalSeedTransportStatement : Prop :=
  ∀ {D : OCData} {Dt Ds : ℕ} {b : ℝ} {j₀ : ℕ}
    (Pt : ProvParams) (lawT : BirthLaw) (rootM rootR : ℕ → ℝ)
    (seedKt freshKt seedKc : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (Gt : GenStage D ScalarH Dt b j₀) (seed : GenStage D ScalarH Ds b j₀)
    (ι : CompIn Gt.comps ≃ CompIn seed.comps)
    (henc : IsSeedEncoding Pt lawT rootM rootR seedKt freshKt seedKc Gt seed ι)
    (M Kout : ℕ) (tp sn tf : ℝ) (htp : tp ≤ sn) (hsn : sn ≤ tf)
    (Z₀ : ∀ v : CompIn Gt.comps, TorusHk Kout (ScalarH v.1.root))
    (Z : ∀ v : CompIn Gt.comps, ℝ → TorusHk Kout (ScalarH v.1.root))
    (Zw : ∀ v : CompIn Gt.comps, ℝ → TorusHk (Kout + 1) (ScalarH v.1.root))
    (Zk : ∀ v u (_ : Gt.fam.Γ v u), ℝ → TorusHk (Kout + Dt - 1) (ScalarH u.1.root))
    (hZ : Gt.IsRegSolution Pt seedKt freshKt φ₀ hφ₀ (D.termB M) (streamVel (D.Φ (M - 1))) Kout tp
      tf Z₀ (fun _ _ => 0) (fun _ _ => 0) Z Zw Zk) ,
    ∀ (P : ProvParams) (freshK : ℕ → KernelSpec)
      (ρ θ : ℝ) (π : CompIn seed.comps → ℝ) (cker : ℕ → ℝ),
      0 < ρ → 0 < D.κ (M - 1) → 2 ≤ Ds → (∀ w, 0 < π w) → θ ≤ 1 / 8 →
      (∀ w u (γ : seed.fam.Γ w u) (d : ↥(Finset.Icc 2 Ds)),
        (Measurable fun q : Set.Icc sn tf × Vec 2 => seed.physCoeff w u γ d.1 q.1 q.2) ∧
        (∀ t ∈ Set.Icc sn tf, ContDiff ℝ (0 : ℕ) (seed.physCoeff w u γ d.1 t)) ∧
        (∀ t ∈ Set.Icc sn tf, AVenhance.IsZ2Periodic (seed.physCoeff w u γ d.1 t)) ∧
        coefficientSeminorm ρ 0 sn tf (seed.physCoeff w u γ d.1) ≠ ⊤) →
      (∀ w u (γ : seed.fam.Γ w u),
        0 < (seed.kernelOf P seedKc freshK w u γ).width ∧
        IsSpatialRegularizerTorus ρ 0 Ds sn tf cker (seed.kernelOf P seedKc freshK w u γ).width
          (seed.sysS P seedKc freshK φ₀ hφ₀ w u γ)) →
      SchurBound θ (kernelSchurMatrix (ι := CompIn seed.comps) (h := fun w => ScalarH w.1.root)
        (Γ := seed.fam.Γ) (G := fun _ u _ => ScalarH u.1.root) (D.κ (M - 1)) ρ π 0 Ds sn tf cker
        (fun w u γ => (seed.kernelOf P seedKc freshK w u γ).width)
        (fun _ u _ => ContinuousLinearMap.id ℝ (ScalarH u.1.root))
        (fun w u γ d => seed.physCoeff w u γ d.1)) →
      (∃ (Uw : ∀ w : CompIn seed.comps, ℝ → TorusHk 1 (ScalarH w.1.root))
          (Uk : ∀ w u (_ : seed.fam.Γ w u), ℝ → TorusHk (0 + Ds - 1) (ScalarH u.1.root)),
        seed.IsRegSolution P seedKc freshK φ₀ hφ₀ (D.κ (M - 1)) (streamVel (D.Φ (M - 1))) 0 sn tf
          (fun w => truncateTorusHk (Nat.zero_le Kout) (Z (ι.symm w) sn))
          (fun _ _ => 0) (fun _ _ => 0)
          (fun w t => truncateTorusHk (Nat.zero_le Kout) (Z (ι.symm w) t)) Uw Uk) ∧
      ∀ (U : ∀ w : CompIn seed.comps, ℝ → TorusHk 0 (ScalarH w.1.root))
        (Uw : ∀ w : CompIn seed.comps, ℝ → TorusHk 1 (ScalarH w.1.root))
        (Uk : ∀ w u (_ : seed.fam.Γ w u), ℝ → TorusHk (0 + Ds - 1) (ScalarH u.1.root)),
        seed.IsRegSolution P seedKc freshK φ₀ hφ₀ (D.κ (M - 1)) (streamVel (D.Φ (M - 1))) 0 sn tf
          (fun w => truncateTorusHk (Nat.zero_le Kout) (Z (ι.symm w) sn))
          (fun _ _ => 0) (fun _ _ => 0) U Uw Uk →
        ∀ w, ∀ t ∈ Set.Icc sn tf, U w t = truncateTorusHk (Nat.zero_le Kout) (Z (ι.symm w) t)

end AVRegularity.Finite.Assembly
end
end

section
@[expose] public noncomputable section
section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.Finite.Assembly

/-! Representation and trace adapters used by the finite assembly. -/

/-- The scalar convention `CsNormLe` follows from the represented Hölder norm. -/
theorem csNormLe_of_holderNorm_le {s B : ℝ} {g : Vec 2 → ℝ} (hB : 0 ≤ B)
    (h : holderNorm s g ≤ ENNReal.ofReal B) : CsNormLe s g B := by
  intro x y z hyz
  have hsup : ENNReal.ofReal |g x| ≤ supNorm g := by
    exact le_iSup_of_le x (by simp [← Real.norm_eq_abs])
  have hinc : ENNReal.ofReal (|g y - g z| / torusDist y z ^ s) ≤ holderSeminorm s g := by
    exact le_iSup_of_le y (le_iSup_of_le z (le_iSup_of_le hyz (by
      simp only [Real.norm_eq_abs]; exact le_rfl)))
  have hi := (add_le_add hsup hinc).trans h
  rw [← ENNReal.ofReal_add (abs_nonneg _) (div_nonneg (abs_nonneg _)
    (Real.rpow_nonneg (Applications.torusDist_nonneg _ _) _))] at hi
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp hi

/-- Adding a scalar error preserves the amplitude-plus-increment convention. -/
theorem csNormLe_add {s A B : ℝ} {g e : Vec 2 → ℝ}
    (hg : CsNormLe s g A) (he : CsNormLe s e B) :
    CsNormLe s (fun x => g x + e x) (A + B) := by
  intro x y z hyz
  have hd : 0 ≤ torusDist y z ^ s :=
    Real.rpow_nonneg (Applications.torusDist_nonneg _ _) _
  have ha := abs_add_le (g x) (e x)
  have hb : |g y + e y - (g z + e z)| ≤ |g y - g z| + |e y - e z| := by
    have hsum : g y + e y - (g z + e z) = (g y - g z) + (e y - e z) := by ring
    rw [hsum]
    exact abs_add_le _ _
  have hc := div_le_div_of_nonneg_right hb hd
  rw [add_div] at hc
  linarith [hg x y z hyz, he x y z hyz]

/-- The physical readout on the actual weak root has norm at most one. -/
theorem weak_root_readout_norm (D : OCData) (N J : ℕ) (η₀ : ℝ)
    (S : Finset Comp) (hc : S = {⟨0, []⟩}) :
    ‖compReadoutCLM (fun v : CompIn S => weakMass D N J η₀ v.1) (fun _ => 1)‖ ≤ 1 := by
  classical
  let v₀ : CompIn S := ⟨⟨0, []⟩, by rw [hc]; simp⟩
  have hv : ∀ v : CompIn S, v = v₀ := by
    intro v
    apply Subtype.ext
    have := v.2
    simp only [hc, Finset.mem_singleton] at this
    exact this
  calc _ ≤ ∑ v : CompIn S,
        |(1 : ℝ)| * Real.sqrt (weakMass D N J η₀ v.1) := compReadoutCLM_norm_le _ _
    _ = Real.sqrt (1 / 2 : ℝ) := by
      rw [Finset.sum_eq_single v₀]
      · simp [v₀, weakMass]
      · intro v _ hne
        exact (hne (hv v)).elim
      · simp
    _ ≤ 1 := (Real.sqrt_le_iff).2 ⟨by norm_num, by norm_num⟩

/-- Mass-preserving reindexing of an identified Sobolev family costs no represented size. -/
theorem reindex_identified_rep {S T : Finset Comp} (ι : CompIn S ≃ CompIn T)
    (π : CompIn S → ℝ) (π' : CompIn T → ℝ) (hmass : ∀ v, π' (ι v) = π v)
    (k : ℕ) (Z : ∀ v : CompIn S, TorusHk k (ScalarH v.1.root))
    (U : ∀ w : CompIn T, TorusHk 0 (ScalarH w.1.root))
    (hU : ∀ v, U (ι v) = truncateTorusHk (Nat.zero_le k) (Z v))
    (s : ℝ) (hs : 0 < s) (hs1 : s < 1) (K : ℕ) (hK : 1 ≤ K) (E : ℝ)
    (r : Representation (CompSpace T)) (hr : IsRepresentationAt E K r)
    (hv : IsRepOf π' U r.value) :
    ∃ rT : Representation (CompSpace S),
      IsRepresentationAt E K rT ∧
      IsRepOf π (fun v => truncateTorusHk (Nat.zero_le k) (Z v)) rT.value ∧
      representedSize s K E rT ≤ representedSize s K E r := by
  obtain ⟨hrep, hvalue, hsize⟩ := compReindex_rep s hs hs1 K hK E ι.symm r hr
  refine ⟨r.map (compReindex ι.symm), hrep, ?_, hsize⟩
  intro v
  have hrval := hv (ι v)
  rw [hU v] at hrval
  filter_upwards [hrval] with x hx
  rw [hvalue]
  change _ = Real.sqrt (π v) * WithLp.ofLp (compReindex ι.symm (r.value x)) v
  rw [compReindex_apply, Equiv.symm_symm, ← hmass v]
  exact hx

/-- Read a represented vector through a norm-one physical scalar map. -/
theorem scalar_rep_readout {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (s : ℝ) (hs : 0 < s) (hs1 : s < 1) (e A : ℝ) (hA : 0 ≤ A)
    (r : Representation H) (hr : IsRepresentationAt e 3 r)
    (R : H →L[ℝ] ℝ) (hR : ‖R‖ ≤ 1)
    (hsize : representedSize s 3 e r ≤ ENNReal.ofReal A) :
    CsNormLe s (fun x => R (r.value x)) (3 * A) := by
  obtain ⟨hm, hv, hb⟩ := (iteration_readout s hs hs1 3 (by omega)
    (H := H) (H' := ℝ)).2.2 e r R hr
  have hmap : representedSize s 3 e (r.map R) ≤ ENNReal.ofReal A := by
    refine (hb.trans ?_).trans hsize
    calc ENNReal.ofReal ‖R‖ * representedSize s 3 e r
        ≤ ENNReal.ofReal 1 * representedSize s 3 e r :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal hR) le_rfl
      _ = _ := by rw [ENNReal.ofReal_one, one_mul]
  have hh := (iteration_readout s hs hs1 3 (by omega)
    (H := ℝ) (H' := ℝ)).2.1 e (r.map R) hm |>.2
  rw [hv] at hh
  apply csNormLe_of_holderNorm_le (mul_nonneg (by norm_num) hA)
  refine hh.trans ((mul_le_mul' le_rfl hmap).trans_eq ?_)
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

/-! Fixed numerical choices and the per-datum finite composition. -/

/-- Increasing the entry reserve can satisfy a cascade floor; the resulting allocation
also supplies every smaller requested reserve. -/
theorem finite_seedAllocation_mono {kS : InvConsts} {r₀ D₀ H J N p Kres Kbig Lpr Lc Lf : ℕ}
    (hK : Kres ≤ Kbig) (h : IsSeedAllocation kS r₀ D₀ H J N p Kbig Lpr Lc Lf) :
    IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf := by
  obtain ⟨hker, hKs, hKan, hLan, hJm, hstar, hr, hd, hprod, henv⟩ := h
  refine ⟨hker, hK.trans hKs, hK.trans hKan, hK.trans hLan, hK.trans hJm,
    ?_, hr, hd, hprod, henv⟩
  exact (Nat.add_le_add_right hK _).trans hstar

/-- All constants selected before the terminal level, phase and datum. -/
structure FiniteParameters where
  α : ℝ
  s : ℝ
  q : ℝ
  ζ : ℝ → ℝ
  Λ : ℕ
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
  PT : ℝ
  QT : ℝ
  NT : ℕ
  pT : ℕ
  RT : ℕ
  AT : ℕ
  k₀ : ℕ
  LcT : ℕ
  LoT : ℕ
  LfT : ℕ
  LpT : ℕ
  tT : ℝ
  τe : ℝ
  lamE : ℝ
  σ₀ : ℝ
  H : ℕ
  J : ℕ
  N : ℕ
  p : ℕ
  Kres : ℕ
  Lpr : ℕ
  Lc : ℕ
  Lf : ℕ
  nT : ℕ+
  Kout : ℕ
  sXT : ℕ
  sZT : ℕ
  Kw : ℕ
  Lt : ℕ
  nW : ℕ+
  hk₀w : k₀ ≤ Kw
  hLw : Lw + 5 ≤ Kw
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
  j₀ : ℕ
  Q : ℝ
  t₀ : ℝ
  nk : ℕ
  L : ℕ
  Naux : ℕ
  Nout : ℕ
  sX : ℕ
  sZ : ℕ
  m₀ : ℕ
  CI : ℝ
  CwCas : ℝ
  Ccas : ℝ
  CQ : ℝ
  Cp : ℝ
  kI : InvConsts

/-- Numerical prerequisites retained from the uniform choices, for the local
seed and fresh-kernel transfer. These are proved by the selector, not open ingredients. -/
structure FiniteLocalValidity (cfg : FiniteParameters) : Prop where
  hα₀ : 0 < cfg.α
  hα₁ : cfg.α < 1 / 3
  hs₁ : cfg.s < (1 - cfg.α) / 2
  hq : IsAdmissibleQ cfg.α cfg.s cfg.q
  hζ : IsFastProfile cfg.ζ
  hcr : 0 < cfg.kI.cr
  hσ₀ : 0 < cfg.σ₀
  hnk : 1 ≤ cfg.nk
  horder : cfg.Kout = cfg.Jw * cfg.Nw + (cfg.NT + 2 * cfg.pT) + 4
  hτ : cfg.τ = cfg.t₀ / 4
  hbw : 0 < cfg.bw
  hc₀ : 0 < cfg.kS.c₀
  hτe : 0 < cfg.τe
  hHprod : cfg.kS.Hprod = cfg.kS.G0 + cfg.H + 1

/-- Uniform numerical seed bounds at the selected terminal level. -/
structure FiniteSeedBudgetLevel (cfg : FiniteParameters) (M : ℕ) : Prop where
  hlevel : 2 ≤ M
  hj₀ : cfg.j₀ ≤ M - 1
  hprice : cfg.Ce * ocEpsilon cfg.q cfg.Λ (M - 2) ^ (cfg.q * cfg.τe) ≤ 1 / 8
  hradius : cfg.kS.c₀ * ocEpsilon cfg.q cfg.Λ (M - 1) ≤ ocEpsilon cfg.q cfg.Λ (M - 2)

/-- The exact level tail of `entry_terminal`, specialized after its carrier-start premise
has been discharged by the uniform selector. The carrier constants precede the selected j₀. -/
def EntryLevelStatement (cfg : FiniteParameters) (M : ℕ) : Prop :=
  ∀ (D : OCData), D.α = cfg.α → D.q = cfg.q → D.Λ = cfg.Λ → D.ζ = cfg.ζ → IsOCStreamSeq cfg.α cfg.q cfg.Λ cfg.ζ D.Φ →
      IsOCBandChain cfg.α cfg.q cfg.Λ cfg.ζ M D.κ → D.term = M →
    ∀ (PW : ProvParams) (a : ℝ),
    ∃ (stage : ℕ → GenStage D ScalarH (termD0bar cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw)) cfg.bw cfg.j₀) (Gw : GenStage D ScalarH (termD0bar cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw)) cfg.bw cfg.j₀) (lawW : BirthLaw)
      (ιw : CompIn (stage M).comps ≃ CompIn Gw.comps) (aM : ℝ)
      (CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root))
      (W : (i : ℕ) → ℝ → (CompIn (stage i).comps → Vec 2 → ℝ) → Vec 2 → ℝ),
      IsWeakConstruction D PW (⟨cfg.Nw, cfg.Rw, cfg.sXT, cfg.sZT, cfg.η₀, M + cfg.Jw⟩ : WeakMenu) M cfg.Jw (D.termRW cfg.σw M) 0 stage ∧
      IsWeakEncoding cfg.Nw cfg.Jw cfg.η₀ lawW.rootMass lawW.rootReadout (stage M) Gw ιw ∧
      (∀ i, M < i → i ≤ M + cfg.Jw → IsWeakReadoutLifts i cfg.Nw (cfg.Jw * cfg.Rw) cfg.sXT cfg.sZT (stage i) (CcR i)) ∧
      IsWeakReadoutChain M cfg.Jw cfg.Nw 0 cfg.η₀ (fun _ => (cfg.Jw * cfg.Rw)) stage CcR W ∧
      IsWeakStage lawW PW cfg.φ₀ cfg.hφ₀ M (M + cfg.Jw) cfg.Jw (cfg.Jw * cfg.Rw) (1 + cfg.Jw * cfg.Nw) cfg.nW cfg.kW a cfg.T₀ cfg.σw cfg.CL cfg.Cχ (weakChi cfg.α cfg.q cfg.η₀) Gw aM ∧
    ∃ (tp : ℝ) (Pterm : (∀ v : CompIn Gw.comps, TorusHk cfg.Kw (ScalarH v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn Gw.comps, TorusHk ((max cfg.Kout (max (2 * cfg.k₀ + 2) (cfg.NT + 2 * cfg.pT + cfg.k₀ + 2)))) (ScalarH v.1.root)))
      (lawT : BirthLaw) (Gt' : GenStage D ScalarH (termD0bar cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw)) cfg.bw cfg.j₀)
      (seed : GenStage D ScalarH (succSchedD (termD0bar cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw)) cfg.N cfg.p (cfg.H + 1)) cfg.bw cfg.j₀)
      (rootM rootR : ℕ → ℝ) (seedKc : ℕ → KernelSpec)
      (ι : CompIn (Gt'.retained M 1 cfg.RT).comps ≃ CompIn seed.comps),
      IsTerminalPrepMap M cfg.Kw ((max cfg.Kout (max (2 * cfg.k₀ + 2) (cfg.NT + 2 * cfg.pT + cfg.k₀ + 2)))) cfg.c cfg.C Gw aM tp Pterm ∧
      IsTerminalLaw lawW lawT cfg.cH cfg.η₀ (wordsUpTo (termAlphabet cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw)) cfg.RT).card ∧
      IsActualSuccessor D (termProvParams D cfg.Cw cfg.cr cfg.tT cfg.η₀ cfg.NT cfg.pT M) (termMenu (M + cfg.Jw) (termAlphabet cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw)) cfg.RT cfg.NT cfg.pT cfg.sXT cfg.sZT cfg.η₀ tp cfg.cr) Gw Gt' ∧
      IsSeedEncoding (termProvParams D cfg.Cw cfg.cr cfg.tT cfg.η₀ cfg.NT cfg.pT M) lawT rootM rootR
        (fun _ => isoPairedKernel (D.termRW cfg.σw M) cfg.nW) (fun _ => isoPairedKernel (D.termRNew cfg.cr cfg.tT M) cfg.nT)
        seedKc (Gt'.retained M 1 cfg.RT) seed ι ∧
      TerminalSeedClauses rootM rootR seedKc cfg.φ₀ cfg.hφ₀ (M + cfg.Jw) (M - 1) cfg.kS cfg.Ce cfg.τe (termR0bar cfg.RT (cfg.Jw * cfg.Rw)) (termD0bar cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw)) seed
        (tp + D.termH M) (a + cfg.T₀) ∧
      tp + D.termH M + 3 * ocTau cfg.α cfg.q cfg.Λ (M - 1) + 4 * ocTauPP cfg.α cfg.q cfg.Λ (M - 1) ≤ a + cfg.T₀ ∧
      ∀ (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ),
        IsWeakSolutionOn (streamVel (D.Φ (M + cfg.Jw))) (D.κ M) a (a + cfg.T₀) f θ →
      ∃ (tq : ℕ → ℝ)
        (Ur : (i : ℕ) → ∀ v : CompIn (stage i).comps, ℝ → TorusHk cfg.Kw (ScalarH v.1.root))
        (Urw : (i : ℕ) → ∀ v : CompIn (stage i).comps, ℝ → TorusHk (cfg.Kw + 1) (ScalarH v.1.root))
        (Urk : (i : ℕ) → ∀ v u (_ : (stage i).fam.Γ v u), ℝ →
          TorusHk (cfg.Kw + (termD0bar cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw)) - 1) (ScalarH u.1.root))
        (U₀ : ∀ v : CompIn Gw.comps, TorusHk cfg.Kw (ScalarH v.1.root))
        (U V : ∀ v : CompIn Gw.comps, ℝ → TorusHk cfg.Kw (ScalarH v.1.root))
        (Uw Vw : ∀ v : CompIn Gw.comps, ℝ → TorusHk (cfg.Kw + 1) (ScalarH v.1.root))
        (Uk Vk : ∀ v u (_ : Gw.fam.Γ v u), ℝ → TorusHk (cfg.Kw + (termD0bar cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw)) - 1) (ScalarH u.1.root)),
        IsWeakReduction PW cfg.φ₀ cfg.hφ₀ cfg.nW M cfg.Jw cfg.Kw 0 a (a + cfg.T₀) θ stage tq Ur Urw Urk ∧
        tq (M + 1) = aM ∧ (U₀ = fun v => rerootFamily ιw (Ur M) v aM) ∧ U = rerootFamily ιw (Ur M) ∧
        IsWeakPaired PW cfg.φ₀ cfg.hφ₀ lawW M cfg.Kw cfg.Lt cfg.nW a cfg.T₀ cfg.σw (weakChi cfg.α cfg.q cfg.η₀) cfg.cK cfg.CK f Gw aM U₀ U V Uw Vw Uk Vk ∧
        IsWeakReadout lawW M cfg.Jw cfg.Lw cfg.Kw (D.κ M) a cfg.τ cfg.T₀ cfg.s cfg.Pw cfg.cK cfg.Cread cfg.Cid f θ Gw
          (fun t g x => W M t (fun v x' => g (ιw v) x') x) V ∧
        IsTerminalPrepBounds lawW M cfg.Kw ((max cfg.Kout (max (2 * cfg.k₀ + 2) (cfg.NT + 2 * cfg.pT + cfg.k₀ + 2)))) cfg.k₀ cfg.hk₀w (le_trans (by omega : cfg.k₀ ≤ 2 * cfg.k₀ + 2) (le_trans (le_max_left _ _) (le_max_right cfg.Kout _))) cfg.cr cfg.cK cfg.C cfg.QT f Gw aM tp Pterm V ∧
        ∃ Z : ∀ v : CompIn (Gt'.retained M 1 cfg.RT).comps, ℝ → TorusHk ((max cfg.Kout (max (2 * cfg.k₀ + 2) (cfg.NT + 2 * cfg.pT + cfg.k₀ + 2)))) (ScalarH v.1.root),
          TerminalFamilyClauses (termProvParams D cfg.Cw cfg.cr cfg.tT cfg.η₀ cfg.NT cfg.pT M)
            (fun _ => isoPairedKernel (D.termRW cfg.σw M) cfg.nW)
            (fun _ => isoPairedKernel (D.termRNew cfg.cr cfg.tT M) cfg.nT) cfg.φ₀ cfg.hφ₀ lawW lawT rootM M ((max cfg.Kout (max (2 * cfg.k₀ + 2) (cfg.NT + 2 * cfg.pT + cfg.k₀ + 2)))) cfg.cr cfg.C
            cfg.Centry tp (tp + D.termH M) (a + cfg.T₀) f Gw (Gt'.retained M 1 cfg.RT) seed ι
            (Pterm fun v => V v aM) Z ∧
          EntryIdentityClauses Gw (Gt'.retained M 1 cfg.RT) M cfg.pT ((max cfg.Kout (max (2 * cfg.k₀ + 2) (cfg.NT + 2 * cfg.pT + cfg.k₀ + 2)))) cfg.Kw cfg.Lw cfg.NT (cfg.Jw * cfg.Rw) cfg.sXT cfg.sZT cfg.η₀ tp a cfg.τ cfg.T₀ cfg.s
            cfg.Pw cfg.PT cfg.C cfg.cr f θ (fun t g x => W M t (fun v x' => g (ιw v) x') x) V Z

/-- The exact level tail of `terminal_lift_rep`, specialized to the chosen parameters. -/
def TerminalLiftLevelStatement (cfg : FiniteParameters) (CT : ℝ) (M : ℕ) : Prop :=
  ∀ (D : OCData), D.α = cfg.α → D.q = cfg.q → D.Λ = cfg.Λ → D.ζ = cfg.ζ → IsOCStreamSeq cfg.α cfg.q cfg.Λ cfg.ζ D.Φ →
      IsOCBandChain cfg.α cfg.q cfg.Λ cfg.ζ M D.κ → D.term = M →
    ∀ (PW : ProvParams) (a : ℝ)
      (Gw : GenStage D ScalarH (termD0bar cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw)) cfg.bw cfg.j₀) (lawW : BirthLaw)
      (aM : ℝ),
      IsWeakStage lawW PW cfg.φ₀ cfg.hφ₀ M (M + cfg.Jw) cfg.Jw (cfg.Jw * cfg.Rw) (1 + cfg.Jw * cfg.Nw) cfg.nW cfg.kW a cfg.T₀ cfg.σw cfg.CL cfg.Cχ
        (weakChi cfg.α cfg.q cfg.η₀) Gw aM →
    ∀ (tp : ℝ) (Pterm : (∀ v : CompIn Gw.comps, TorusHk cfg.Kw (ScalarH v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn Gw.comps, TorusHk (max cfg.Kout (max (2 * cfg.k₀ + 2) (cfg.NT + 2 * cfg.pT + cfg.k₀ + 2))) (ScalarH v.1.root))),
      IsTerminalPrepMap M cfg.Kw (max cfg.Kout (max (2 * cfg.k₀ + 2) (cfg.NT + 2 * cfg.pT + cfg.k₀ + 2))) cfg.c cfg.C Gw aM tp Pterm →
    ∀ (lawT : BirthLaw) (Gt' : GenStage D ScalarH (termD0bar cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw)) cfg.bw cfg.j₀),
      IsTerminalLaw lawW lawT cfg.cH cfg.η₀ (wordsUpTo (termAlphabet cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw)) cfg.RT).card →
      IsActualSuccessor D (termProvParams D cfg.Cw cfg.cr cfg.tT cfg.η₀ cfg.NT cfg.pT M)
        (termMenu (M + cfg.Jw) (termAlphabet cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw)) cfg.RT cfg.NT cfg.pT cfg.sXT cfg.sZT cfg.η₀ tp cfg.cr)
        Gw Gt' →
    ∀ (Kz : ℕ) (Z : ∀ v : CompIn (Gt'.retained M 1 cfg.RT).comps, ℝ → TorusHk Kz (ScalarH v.1.root))
      (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn Gw.comps) (fun v => ScalarH v.1.root))
      (PZ : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kz - 2 * cfg.pT) (ScalarH v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn Gw.comps, ScalarH v.1.root)
      (û : ∀ v : CompIn Gw.comps, ℝ → TorusHk 0 (ScalarH v.1.root)),
      IsTerminalLiftedField Gw (Gt'.retained M 1 cfg.RT) M cfg.pT Kz cfg.NT (cfg.Jw * cfg.Rw) cfg.sXT cfg.sZT cfg.η₀ tp (a + cfg.T₀) cfg.cr
        Z CcT PZ aRep û →
    ∀ t ∈ Set.Icc tp (a + cfg.T₀),
    ∀ r : Representation (CompSpace (Gt'.retained M 1 cfg.RT).comps),
      IsRepresentationAt (D.eps (M - 1)) (cfg.Jw * cfg.Nw + (cfg.NT + 2 * cfg.pT) + 4) r →
      IsRepOf ((Gt'.retained M 1 cfg.RT).mass lawT)
        (fun v => truncateTorusHk (Nat.zero_le Kz) (Z v t)) r.value →
    ∃ rT : Representation (CompSpace Gw.comps),
      IsRepresentationAt (D.eps M) (cfg.Jw * cfg.Nw + 3) rT ∧
      rT.base = (r.map (readoutCLM M (D.eps (M - 1)) cfg.η₀ (Gw.mass lawW)
        ((Gt'.retained M 1 cfg.RT).mass lawT))).base ∧
      (∃ Lcov Llift : List ((Vec 2 → CompSpace Gw.comps) × ℝ),
        rT.profiles = (r.map (readoutCLM M (D.eps (M - 1)) cfg.η₀ (Gw.mass lawW)
          ((Gt'.retained M 1 cfg.RT).mass lawT))).profiles ++ Lcov ++ Llift ∧
        (∀ g ∈ Lcov, g.2 = D.eps (M - 1)) ∧ ∀ g ∈ Llift, g.2 = D.eps M) ∧
      rT.value = compField (Gw.mass lawW) (termLiftedRep Gw M cfg.NT (cfg.Jw * cfg.Rw) cfg.cr CcT aRep t) ∧
      representedSize cfg.s (cfg.Jw * cfg.Nw + 3) (D.eps M) rT ≤
        ENNReal.ofReal CT * representedSize cfg.s (cfg.Jw * cfg.Nw + (cfg.NT + 2 * cfg.pT) + 4) (D.eps (M - 1)) r

/-- The exact level tail of `weak_lift_rep`, specialized to the chosen parameters. -/
def WeakLiftLevelStatement (cfg : FiniteParameters) (CwLift : ℝ) (M : ℕ) : Prop :=
  ∀ (D : OCData), D.α = cfg.α → D.q = cfg.q → D.Λ = cfg.Λ → D.ζ = cfg.ζ → IsOCStreamSeq cfg.α cfg.q cfg.Λ cfg.ζ D.Φ →
      IsOCBandChain cfg.α cfg.q cfg.Λ cfg.ζ M D.κ → D.term = M →
    ∀ (PW : ProvParams) (Dm : ℕ) (stage : ℕ → GenStage D ScalarH Dm cfg.bw cfg.j₀)
      (Gw : GenStage D ScalarH Dm cfg.bw cfg.j₀) (lawW : BirthLaw) (ιw : CompIn (stage M).comps ≃ CompIn Gw.comps)
      (CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root))
      (W : (i : ℕ) → ℝ → (CompIn (stage i).comps → Vec 2 → ℝ) → Vec 2 → ℝ),
      IsWeakConstruction D PW (⟨cfg.Nw, cfg.Rw, cfg.sXT, cfg.sZT, cfg.η₀, M + cfg.Jw⟩ : WeakMenu) M cfg.Jw (D.termRW cfg.σw M) 0
        stage →
      IsWeakEncoding cfg.Nw cfg.Jw cfg.η₀ lawW.rootMass lawW.rootReadout (stage M) Gw ιw →
      (∀ i, M < i → i ≤ M + cfg.Jw → IsWeakReadoutLifts i cfg.Nw (cfg.Jw * cfg.Rw) cfg.sXT cfg.sZT (stage i) (CcR i)) →
      IsWeakReadoutChain M cfg.Jw cfg.Nw 0 cfg.η₀ (fun _ => cfg.Jw * cfg.Rw) stage CcR W →
    ∀ (t : ℝ) (g : Vec 2 → ∀ v : CompIn Gw.comps, ScalarH v.1.root)
      (rT : Representation (CompSpace Gw.comps)),
      IsRepresentationAt (D.eps M) (cfg.Jw * cfg.Nw + 3) rT → rT.value = compField (Gw.mass lawW) g →
    ∃ rW : Representation (CompSpace (stage (M + cfg.Jw)).comps),
      IsRepresentationAt (D.eps (M + cfg.Jw)) 3 rW ∧
      (∀ y, compReadoutCLM (fun v => weakMass D cfg.Nw cfg.Jw cfg.η₀ v.1) (fun _ => 1) (rW.value y) =
        W M t (fun v y' => g y' (ιw v)) y) ∧
      representedSize cfg.s 3 (D.eps (M + cfg.Jw)) rW ≤
        ENNReal.ofReal CwLift * representedSize cfg.s (cfg.Jw * cfg.Nw + 3) (D.eps M) rT

/-- The exact post-constant tail of the cascade, at the finite theorem's strong order. -/
def CascadeLevelStatement (cfg : FiniteParameters) : Prop :=
  ∀ (D : OCData), D.α = cfg.α → D.q = cfg.q → D.Λ = cfg.Λ → D.ζ = cfg.ζ → IsOCStreamSeq cfg.α cfg.q cfg.Λ cfg.ζ D.Φ →
  ∀ (M : ℕ), IsOCBandChain cfg.α cfg.q cfg.Λ cfg.ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
  ∀ (law : BirthLaw),
    IsSuccessorLaw cfg.α cfg.q cfg.s (wordsUpTo (succAlphabetOf (termR0bar cfg.RT (cfg.Jw * cfg.Rw)) (termD0bar cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw)) cfg.H cfg.J cfg.N cfg.p 0) (cfg.J + 1)).card law →
  ∀ (seedK freshK : ℕ → KernelSpec),
    (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D cfg.kI.cr cfg.σ₀ cfg.nk.toPNat' b' (freshK b')) →
  ∀ (seed : GenStage D ScalarH (succSchedD (termD0bar cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw)) cfg.N cfg.p (cfg.H + 1)) cfg.bw cfg.j₀) (n : ℕ) (tS tf : ℝ),
    tS + (cfg.t₀ / 2) < tf → tf - tS ≤ cfg.T₀ →
    IsGeneratedSeed law (succProvParams D cfg.CwCas cfg.kI.cr cfg.σ₀ (succEta0 cfg.α cfg.q cfg.s) cfg.N cfg.p) seedK freshK cfg.φ₀ cfg.hφ₀
      Mnat cfg.kS seed n tS tf cfg.Ce cfg.τe (termR0bar cfg.RT (cfg.Jw * cfg.Rw)) (termD0bar cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw)) →
    IsSeedPointwiseMolecular law cfg.kS seed tS tf →
    cfg.m₀ < n → n < M →
  ∃ (stage ext : ℕ → GenStage D ScalarH (succSchedD (termD0bar cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw)) cfg.N cfg.p (cfg.H + 1)) cfg.bw cfg.j₀) (hist st tp : ℕ → ℝ)
    (Preg : (j : ℕ) → (∀ v : CompIn (stage j).comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn (stage j).comps, TorusHk cfg.Nout (ScalarH v.1.root))),
    CascadeFrame law (succProvParams D cfg.CwCas cfg.kI.cr cfg.σ₀ (succEta0 cfg.α cfg.q cfg.s) cfg.N cfg.p)
      (succMenu Mnat (termR0bar cfg.RT (cfg.Jw * cfg.Rw)) (termD0bar cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw)) cfg.H cfg.J cfg.N cfg.p 0 cfg.sX cfg.sZ (succEta0 cfg.α cfg.q cfg.s)) seedK freshK cfg.φ₀ cfg.hφ₀ Mnat cfg.kI cfg.CI cfg.τe
      (succEta0 cfg.α cfg.q cfg.s) cfg.Kres (wordsUpTo (succAlphabetOf (termR0bar cfg.RT (cfg.Jw * cfg.Rw)) (termD0bar cfg.NT cfg.pT (1 + cfg.Jw * cfg.Nw) (cfg.Jw * cfg.Rw)) cfg.H cfg.J cfg.N cfg.p 0) (cfg.J + 1)).card cfg.p cfg.Nout
      cfg.Naux cfg.Q cfg.CQ cfg.Cp seed n cfg.m₀ tS (cfg.t₀ / 2) tf stage ext hist st tp Preg ∧
    ∀ f : ∀ v : CompIn (stage n).comps, TorusHk 0 (ScalarH v.1.root),
      CascadeOutput law (succProvParams D cfg.CwCas cfg.kI.cr cfg.σ₀ (succEta0 cfg.α cfg.q cfg.s) cfg.N cfg.p) seedK freshK cfg.φ₀ cfg.hφ₀
        cfg.p cfg.N (succSchedR (termR0bar cfg.RT (cfg.Jw * cfg.Rw)) cfg.J cfg.H) cfg.sX cfg.sZ (cfg.Jw * cfg.Nw + (cfg.NT + 2 * cfg.pT) + 4) cfg.Naux cfg.s (succEta0 cfg.α cfg.q cfg.s) (ocMuS cfg.α cfg.q cfg.s)
        (ocDelta cfg.α cfg.q - 2 * cfg.σ₀) 2 cfg.Q cfg.Ccas cfg.kI.cr cfg.kI.c₀ n cfg.m₀ tS (cfg.t₀ / 2) tf stage hist st tp Preg f


/-- Intermediate per-datum interface: an a.e. represented root approximation
with the entry scalar error. `finite_datum_composition_of_strong_entry` proves
this interface from the narrower seed-to-terminal representation ingredient
by applying both lifts. -/
def FiniteDatumCompositionStatement : Prop :=
  ∀ (cfg : FiniteParameters) (_hvalid : FiniteLocalValidity cfg) (_htransport : TerminalSeedTransportStatement)
    (_hs : 0 < cfg.s) (_hs1 : cfg.s < 1) (_hΛ : 128 ≤ cfg.Λ)
    (_hη : 0 < succEta0 cfg.α cfg.q cfg.s) (_ht₀ : 0 < cfg.t₀) (_htT : cfg.t₀ < cfg.T₀)
    (_hτ : cfg.τ ≤ cfg.t₀)
    (_hc : 0 < cfg.c) (_hCcas : 0 < cfg.Ccas) (_hPw : cfg.Pw = 2) (_hPT : cfg.PT = 2)
    (M : ℕ) (_hM : cfg.m₀ + 2 ≤ M) (_hbudget : FiniteSeedBudgetLevel cfg M)
    (_hwait : (|cfg.C| + 1) * ocTauPP cfg.α cfg.q cfg.Λ M +
      6 * cfg.Jw * ocTauPP cfg.α cfg.q cfg.Λ (M + 1) ≤ cfg.t₀ / 4)
    (_hentry : EntryLevelStatement cfg M) (CT CwLift : ℝ) (_hCT : 0 ≤ CT) (_hCw : 0 ≤ CwLift)
    (_hterm : TerminalLiftLevelStatement cfg CT M) (_hweak : WeakLiftLevelStatement cfg CwLift M)
    (_hcas : CascadeLevelStatement cfg)
    (D : OCData) (_hDα : D.α = cfg.α) (_hDq : D.q = cfg.q) (_hDΛ : D.Λ = cfg.Λ)
    (_hDζ : D.ζ = cfg.ζ) (_hDΦ : IsOCStreamSeq cfg.α cfg.q cfg.Λ cfg.ζ D.Φ)
    (_hband : IsOCBandChain cfg.α cfg.q cfg.Λ cfg.ζ M D.κ) (_hDterm : D.term = M)
    (_haxes : ∀ b', 1 ≤ b' → b' < M → ∃ H₁ H₂ : ℝ → Vec 2 →L[ℝ] Vec 2,
      IsFreshAxes D b' H₁ H₂)
    (a : ℝ) (f : Vec 2 → ℝ) (_hf : MemL2On unitCube f) (θ : ℝ → Vec 2 → ℝ)
    (_hθ : IsWeakSolutionOn (streamVel (D.Φ (M + cfg.Jw))) (D.κ M) a (a + cfg.T₀) f θ) ,
    ∀ᵐ t ∂(volume.restrict (Set.Icc (a + cfg.t₀) (a + cfg.T₀))),
      ∃ S : Finset Comp, S = {⟨0, []⟩} ∧
      ∃ r : Representation (CompSpace S),
        IsRepresentationAt (D.eps (M + cfg.Jw)) 3 r ∧
        representedSize cfg.s 3 (D.eps (M + cfg.Jw)) r ≤
          ENNReal.ofReal ((CwLift * CT) * cfg.Ccas * |cfg.Centry| * Real.sqrt (l2NormSq f)) ∧
      ∃ Θt : Vec 2 → ℝ, IsZ2Periodic Θt ∧ Θt =ᵐ[volume.restrict unitCube] θ t ∧
        CsNormLe cfg.s (fun x => Θt x -
          compReadoutCLM (fun v : CompIn S => weakMass D cfg.Nw cfg.Jw cfg.η₀ v.1)
            (fun _ => 1) (r.value x)) (2 * |cfg.C| * Real.sqrt (l2NormSq f))

end AVRegularity.Finite.Assembly
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.Finite.WeakLift

/-! Conditional assembly for the represented weak lift. The uniform analytic leaf is
one passage, with a constant selected before the carrier start and terminal level.
The finite iteration leaf spends N derivatives per passage and multiplies the constants. -/

/-- Local represented transfer for every passage of one actual weak stack. -/
def WeakStackPassageStatement {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (s : ℝ) (M J N Lr : ℕ) (η Cstep : ℝ)
    (stage : ℕ → GenStage D ScalarH Dm b j₀)
    (CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root))
    (depth : ℕ) : Prop :=
  ∀ i : ℕ, M < i → i ≤ M + J → ∀ K : ℕ, K ≤ Lr + 3 →
  ∀ (t : ℝ) (g : CompIn (stage (i - 1)).comps → Vec 2 → ℝ)
    (r : Representation (CompSpace (stage (i - 1)).comps)),
    IsRepresentationAt (D.eps (i - 1)) (K + N) r →
    r.value = compField (fun v => weakMass D N J η v.1) (fun x v => g v x) →
  ∃ r' : Representation (CompSpace (stage i).comps),
    IsRepresentationAt (D.eps i) K r' ∧
    r'.value = compField (fun v => weakMass D N J η v.1)
      (fun x v => weakGluedLift i N depth (stage i) (CcR i) t
        (weakReadoutStep i η (stage i) (stage (i - 1)) g) v x) ∧
    representedSize s K (D.eps i) r' ≤
      ENNReal.ofReal Cstep * representedSize s (K + N) (D.eps (i - 1)) r

/-- The actual weak construction supplies a uniform one-passage represented bound.
No entry existence theorem or weak-envelope producer is proved by this assembly. -/
def WeakLiftPassageBoundsStatement : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ) ,
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Jw Nw Rw : ℕ) (η₀ σw : ℝ), 1 ≤ Jw → 1 ≤ Nw → 0 < η₀ → η₀ ≤ ocDelta α q / 8 →
      0 < σw → σw < min (ocC α q) (q - 1) →
    ∀ Lr : ℕ, Jw * Nw ≤ Lr →
    ∃ SX SZ : ℕ, ∀ sX sZ : ℕ, SX ≤ sX → SZ ≤ sZ →
    ∃ Cstep : ℝ, 0 ≤ Cstep ∧
    ∃ (CHw Υw : ℝ), 1 ≤ CHw ∧ 0 < Υw ∧
    ∀ j₀ : ℕ, IsCarrierStart α q Λ bw CHw Υw j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ M D.κ → D.term = M →
    ∀ (PW : ProvParams) (Dm : ℕ)
      (stage : ℕ → GenStage D ScalarH Dm bw j₀)
      (CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root)),
      IsWeakConstruction D PW (⟨Nw, Rw, sX, sZ, η₀, M + Jw⟩ : WeakMenu) M Jw (D.termRW σw M) 0 stage →
      (∀ i, M < i → i ≤ M + Jw → IsWeakReadoutLifts i Nw (Jw * Rw) sX sZ (stage i) (CcR i)) →
      WeakStackPassageStatement s M Jw Nw Lr η₀ Cstep stage CcR (Jw * Rw)

/-- Finite composition of the local bounds, including the single root readout. -/
def WeakLiftIterationStatement : Prop :=
  ∀ {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (s : ℝ) (M J N Lr depth : ℕ) (η Cstep : ℝ), J * N ≤ Lr → 0 ≤ Cstep →
    (∀ i, 0 < D.eps i) →
  ∀ (stage : ℕ → GenStage D ScalarH Dm b j₀)
    (CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root))
    (W : (i : ℕ) → ℝ → (CompIn (stage i).comps → Vec 2 → ℝ) → Vec 2 → ℝ),
    IsWeakRoot (M + J) 0 (stage (M + J)) →
    IsWeakReadoutChain M J N 0 η (fun _ => depth) stage CcR W →
    WeakStackPassageStatement s M J N Lr η Cstep stage CcR depth →
  ∀ (t : ℝ) (g : CompIn (stage M).comps → Vec 2 → ℝ)
    (r : Representation (CompSpace (stage M).comps)),
    IsRepresentationAt (D.eps M) (Lr + 3) r →
    r.value = compField (fun v => weakMass D N J η v.1) (fun x v => g v x) →
  ∃ r' : Representation (CompSpace (stage (M + J)).comps),
    IsRepresentationAt (D.eps (M + J)) 3 r' ∧
    (∀ y, compReadoutCLM (fun v => weakMass D N J η v.1) (fun _ => 1) (r'.value y) = W M t g y) ∧
    representedSize s 3 (D.eps (M + J)) r' ≤
      ENNReal.ofReal (Cstep ^ J) * representedSize s (Lr + 3) (D.eps M) r

/-- Variable-start composition. The input order may exceed the exact remaining
passage budget, so the original M-start statement is retained as a special case. -/
def WeakLiftIterationFromStatement : Prop :=
  ∀ {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (s : ℝ) (M J N Lr depth : ℕ) (η Cstep : ℝ), J * N ≤ Lr → 0 ≤ Cstep →
    (∀ i, 0 < D.eps i) →
  ∀ (stage : ℕ → GenStage D ScalarH Dm b j₀)
    (CcR : (i : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (stage i).comps) (fun v => ScalarH v.1.root))
    (W : (i : ℕ) → ℝ → (CompIn (stage i).comps → Vec 2 → ℝ) → Vec 2 → ℝ),
    IsWeakRoot (M + J) 0 (stage (M + J)) →
    IsWeakReadoutChain M J N 0 η (fun _ => depth) stage CcR W →
    WeakStackPassageStatement s M J N Lr η Cstep stage CcR depth →
  ∀ (m : ℕ), M ≤ m → m ≤ M + J →
  ∀ (K₀ : ℕ), K₀ ≤ Lr → (M + J - m) * N ≤ K₀ →
  ∀ (t : ℝ) (g : CompIn (stage m).comps → Vec 2 → ℝ)
    (r : Representation (CompSpace (stage m).comps)),
    IsRepresentationAt (D.eps m) (K₀ + 3) r →
    r.value = compField (fun v => weakMass D N J η v.1) (fun x v => g v x) →
  ∃ r' : Representation (CompSpace (stage (M + J)).comps),
    IsRepresentationAt (D.eps (M + J)) 3 r' ∧
    (∀ y, compReadoutCLM (fun v => weakMass D N J η v.1) (fun _ => 1) (r'.value y) = W m t g y) ∧
    representedSize s 3 (D.eps (M + J)) r' ≤
      ENNReal.ofReal (Cstep ^ (M + J - m)) * representedSize s (K₀ + 3) (D.eps m) r

/-- One carrier start supplies two independently selected finite weak requests. -/
theorem weak_carrier_start_pair {α q bw CH₁ CH₂ Υ₁ Υ₂ : ℝ} {Λ j₀ : ℕ}
    (hΛ : 1 ≤ Λ) (hCH₁ : 0 ≤ CH₁) (hCH₂ : 0 ≤ CH₂)
    (hΥ₁ : 0 ≤ Υ₁) (hΥ₂ : 0 ≤ Υ₂)
    (h : IsCarrierStart α q Λ bw (max CH₁ CH₂) (max Υ₁ Υ₂) j₀) :
    IsCarrierStart α q Λ bw CH₁ Υ₁ j₀ ∧ IsCarrierStart α q Λ bw CH₂ Υ₂ j₀ := by
  have hA (k : ℕ) : 0 ≤ ocA α q Λ k := by
    unfold ocA
    exact Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ).le _
  have hT (k : ℕ) : 0 ≤ ocTauPP α q Λ k :=
    (Construction.Stream.ocTauPP_pos hΛ).le
  exact ⟨IsCarrierStart.mono hA hT (le_max_left _ _) (le_max_left _ _) hCH₁ hΥ₁ h,
    IsCarrierStart.mono hA hT (le_max_right _ _) (le_max_right _ _) hCH₂ hΥ₂ h⟩

/-- Exact weak-lift statement, given the analytic passage bound and
finite composition. The encoding adapter is already discharged. -/
theorem weak_lift_rep_of_ingredients (hpass : WeakLiftPassageBoundsStatement)
    (hiter : WeakLiftIterationStatement) : Assembly.WeakLiftRepStatement := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λ₀, hΛ₀, hΛtail⟩ := hpass α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ bw hbw hbw1 Jw Nw Rw η₀ σw hJ hN hη hη1 hσ hσ1 Lr hLr
  obtain ⟨SX, SZ, hreserve⟩ := hΛtail Λ hΛ bw hbw hbw1 Jw Nw Rw η₀ σw hJ hN
    hη hη1 hσ hσ1 Lr hLr
  refine ⟨SX, SZ, ?_⟩
  intro sX sZ hsX hsZ
  obtain ⟨Cstep, hCstep, CHw, Υw, hCHw, hΥw, hstart⟩ := hreserve sX sZ hsX hsZ
  refine ⟨Cstep ^ Jw, pow_nonneg hCstep _, CHw, Υw, hCHw, hΥw, ?_⟩
  intro j₀ hj₀
  obtain ⟨M₀, hMtail⟩ := hstart j₀ hj₀
  refine ⟨M₀, ?_⟩
  intro M hM D hDα hDq hDΛ hDζ hstream hband hterm PW Dm stage Gw lawW ιw CcR W
    hconstruction hencoding hlifts hchain t g rT hrT hvalue
  have hε (i : ℕ) : 0 < D.eps i := by
    change 0 < ocEpsilon D.q D.Λ i
    rw [hDΛ]
    exact Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ Λ)
  have hsteps := hMtail M hM D hDα hDq hDΛ hDζ hstream hband hterm PW Dm stage CcR
    hconstruction hlifts
  obtain ⟨hreindex, hvalreindex, hsize⟩ := weak_encoding_representation hencoding (Lr + 3)
    g rT hrT hvalue (s := s)
  obtain ⟨rW, hrW, hreadout, hbound⟩ := hiter s M Jw Nw Lr (Jw * Rw) η₀ Cstep hLr
    hCstep hε stage CcR W hconstruction.2.1 hchain hsteps t (fun v y => g y (ιw v))
    (rT.map (compReindex ιw.symm)) hreindex hvalreindex
  exact ⟨rW, hrW, hreadout, hbound.trans (mul_le_mul' le_rfl hsize)⟩

end AVRegularity.Finite.WeakLift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.Finite.TerminalLift

/-! Assembly of the represented terminal lift. The copied constant-map
prefix is preserved. Covariance and oscillatory differences are regrouped as one
profile each, respectively at E and x, as allowed by the existence form. -/

/-- Uniform normalized readout and finite covariance/lift profile costs,
with the constants selected in the exact menu order. -/
def TerminalLiftProfileBoundsStatement : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ) ,
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Jw Nw Rw Lw : ℕ) (T₀ η₀ σw : ℝ), 1 ≤ Jw → 0 < T₀ → 0 < η₀ → η₀ ≤ ocDelta α q / 8 →
      0 < σw → σw < min (ocC α q) (q - 1) →
    ∀ (PT QT : ℝ) (NT pT RT AT k₀ LcT LoT LfT LpT : ℕ) (tT : ℝ),
      IsTerminalSchedule α q s PT QT σw (weakChi α q η₀) η₀ tT Jw Lw k₀ NT pT RT AT LcT LoT LfT
        LpT (termAlphabet NT pT (1 + Jw * Nw) (Jw * Rw)) →
    ∀ Lr : ℕ,
    ∃ SX SZ : ℕ, ∀ sXT sZT : ℕ, SX ≤ sXT → SZ ≤ sZT →
    ∀ (cr : ℝ), 0 < cr → cr ≤ 1 →
    ∀ (Kw Kp : ℕ) (nW : ℕ+) (kW : InvConsts) (CL Cχ c C Cw cH : ℝ), 0 < c → 0 < cH →
    kW.G0 ≤ kW.Hprod + 1 →
    ∃ Cbound : ℝ, 0 ≤ Cbound ∧
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
      IsRepresentationAt (D.eps (M - 1)) (Lr + (NT + 2 * pT) + 4) r →
      IsRepOf ((Gt'.retained M 1 RT).mass lawT)
        (fun v => truncateTorusHk (Nat.zero_le Kz) (Z v t)) r.value →
      ‖readoutCLM M (D.eps (M - 1)) η₀ (Gw.mass lawW) ((Gt'.retained M 1 RT).mass lawT)‖ ≤ Cbound ∧
      ContDiff ℝ (Lr + 3 : ℕ) (compField (Gw.mass lawW) (aRep t) - (fun x => (readoutCLM M (D.eps (M - 1)) η₀ (Gw.mass lawW) ((Gt'.retained M 1 RT).mass lawT)) (r.value x))) ∧ IsZ2Periodic (compField (Gw.mass lawW) (aRep t) - (fun x => (readoutCLM M (D.eps (M - 1)) η₀ (Gw.mass lawW) ((Gt'.retained M 1 RT).mass lawT)) (r.value x))) ∧
      ContDiff ℝ (Lr + 3 : ℕ) (compField (Gw.mass lawW) (termLiftedRep Gw M NT (Jw * Rw) cr CcT aRep t) - compField (Gw.mass lawW) (aRep t)) ∧ IsZ2Periodic (compField (Gw.mass lawW) (termLiftedRep Gw M NT (Jw * Rw) cr CcT aRep t) - compField (Gw.mass lawW) (aRep t)) ∧
      profileNorm (D.eps (M - 1)) (Lr + 3) s (compField (Gw.mass lawW) (aRep t) - (fun x => (readoutCLM M (D.eps (M - 1)) η₀ (Gw.mass lawW) ((Gt'.retained M 1 RT).mass lawT)) (r.value x))) +
        profileNorm (D.eps M) (Lr + 3) s (compField (Gw.mass lawW) (termLiftedRep Gw M NT (Jw * Rw) cr CcT aRep t) - compField (Gw.mass lawW) (aRep t)) ≤
          ENNReal.ofReal Cbound * representedSize s (Lr + (NT + 2 * pT) + 4) (D.eps (M - 1)) r

/-- All representation assembly, old labels, base copying, and size summation are
proved; only the uniform actual coefficient/profile bound remains. -/
theorem terminal_lift_rep_of_ingredients (hbounds : TerminalLiftProfileBoundsStatement) :
    Assembly.TerminalLiftRepStatement := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λ₀, hΛ₀, hΛtail⟩ := hbounds α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ φ₀ hφ₀ hφcd hφnn hφint hφsupp bw hbw hbw1 Jw Nw Rw Lw T₀ η₀ σw
    hJ hT hη hη1 hσ hσ1 PT QT NT pT RT AT k₀ LcT LoT LfT LpT tT hsched Lr
  obtain ⟨SX, SZ, hreserve⟩ := hΛtail Λ hΛ φ₀ hφ₀ hφcd hφnn hφint hφsupp bw hbw hbw1
    Jw Nw Rw Lw T₀ η₀ σw hJ hT hη hη1 hσ hσ1 PT QT NT pT RT AT k₀ LcT LoT LfT LpT
    tT hsched Lr
  refine ⟨SX, SZ, ?_⟩
  intro sXT sZT hsXT hsZT cr hcr hcr1 Kw Kp nW kW CL Cχ c C Cw cH hc hcH hkw
  obtain ⟨Cbound, hCbound, hstart⟩ := hreserve sXT sZT hsXT hsZT cr hcr hcr1
    Kw Kp nW kW CL Cχ c C Cw cH hc hcH hkw
  refine ⟨2 * Cbound, mul_nonneg (by norm_num) hCbound, ?_⟩
  intro j₀
  obtain ⟨M₀, hMtail⟩ := hstart j₀
  refine ⟨M₀, ?_⟩
  intro M hM D hDα hDq hDΛ hDζ hstream hband hterm PW a Gw lawW aM hstage tp Pterm hprep
    lawT Gt' hlaw hactual Kz Z CcT PZ aRep û hlift t ht r hr hvalue
  obtain ⟨hR, hcov, hcovp, hosc, hoscp, hcost⟩ := hMtail M hM D hDα hDq hDΛ hDζ hstream
    hband hterm PW a Gw lawW aM hstage tp Pterm hprep lawT Gt' hlaw hactual Kz Z CcT PZ
    aRep û hlift t ht r hr hvalue
  let R := readoutCLM M (D.eps (M - 1)) η₀ (Gw.mass lawW) ((Gt'.retained M 1 RT).mass lawT)
  let cov := compField (Gw.mass lawW) (aRep t) - fun x => R (r.value x)
  let osc := compField (Gw.mass lawW) (termLiftedRep Gw M NT (Jw * Rw) cr CcT aRep t) -
    compField (Gw.mass lawW) (aRep t)
  let rT := appendCorrections r R cov osc (D.eps (M - 1)) (D.eps M)
  have he : 0 < D.eps M := by
    change 0 < ocEpsilon D.q D.Λ M
    rw [hDq, hDΛ]
    exact (Scales.epsilon_basic hq.1 (hΛ₀.trans hΛ)).1
  have heE : D.eps M ≤ D.eps (M - 1) := by
    change ocEpsilon D.q D.Λ M ≤ ocEpsilon D.q D.Λ (M - 1)
    rw [hDq, hDΛ]
    by_cases hMzero : M = 0
    · simpa only [hMzero, Nat.zero_sub] using (le_refl (ocEpsilon q Λ 0))
    · have hsuc : M - 1 + 1 = M := by omega
      simpa only [hsuc] using CycleReference.epsilon_succ_le (n := M - 1) hq.1 (hΛ₀.trans hΛ)
  have hk : Lr + 3 ≤ Lr + (NT + 2 * pT) + 4 := by omega
  have hs1 : s < 1 := hs₁.trans (by linarith only [hα₀] : (1 - α) / 2 < 1)
  refine ⟨rT, appendCorrections_representation he heE hk r R hr cov osc hcov hcovp hosc hoscp,
    rfl, ?_, ?_, ?_⟩
  · refine ⟨[(cov, D.eps (M - 1))], [(osc, D.eps M)], rfl, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
      exact congrArg Prod.snd hg
    · intro g hg
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
      exact congrArg Prod.snd hg
  · rw [appendCorrections_value]
    funext x
    dsimp [cov, osc]
    abel
  · rw [appendCorrections_size, add_assoc]
    have hprefix := prefix_size_le he heE hs1 hk r R hr hR
    calc
      _ ≤ ENNReal.ofReal Cbound * representedSize s (Lr + (NT + 2 * pT) + 4) (D.eps (M - 1)) r +
          ENNReal.ofReal Cbound * representedSize s (Lr + (NT + 2 * pT) + 4) (D.eps (M - 1)) r :=
        add_le_add hprefix hcost
      _ = _ := by
        rw [show (2 : ℝ) * Cbound = Cbound + Cbound by ring,
          ENNReal.ofReal_add hCbound hCbound, add_mul]

end AVRegularity.Finite.TerminalLift
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.Finite.TerminalLift

/-! General weak-depth/order terminal profile assembly. The constant readout is separated
from the actual covariance and nonidentity lift profiles; all choices precede the datum. -/

/-- A word-menu constant, independent of the number of incoming roots. -/
def terminalReadoutConstant (A : Finset WordLetter) (RT : ℕ) (cH : ℝ) : ℝ :=
  (1 + (wordsUpTo A (RT + 1)).card : ℕ) * max 1 (Real.sqrt cH)

/-- Normalized readout on root components and their retained successor words. -/
def TerminalReadoutBoundsStatement : Prop :=
  ∀ (q : ℝ) (Λ m : ℕ), 1 < q → 128 ≤ Λ → 1 ≤ m →
  ∀ (lawW lawT : BirthLaw) (η : ℝ) (A : Finset WordLetter) (RT : ℕ)
    (S S' : Finset Comp), lawT.rootMass = lawW.rootMass → 0 ≤ lawT.etaB → 0 ≤ η →
    (∀ v ∈ S, v.births = []) → S' ⊆ succExtComps m A RT S →
    ‖readoutCLM m (ocEpsilon q Λ (m - 1)) η
      (fun v : CompIn S => compMass q Λ lawW v.1)
      (fun v : CompIn S' => compMass q Λ lawT v.1)‖ ≤
      terminalReadoutConstant A RT lawT.cH

abbrev TerminalProfileProperty := ∀ {H H' : Type}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup H'] [NormedSpace ℝ H']
    (_s _E _e _C : ℝ) (_k _kin : ℕ) (_r : Representation H)
    (_R : H →L[ℝ] H') (_cov _osc : Vec 2 → H'), Prop

/-- The lift sequences and covariance/classical representative of a terminal lift.
This is exactly the first two clauses of `IsTerminalLiftedField`, without a realization. -/
def IsTerminalLiftData {D : OCData} {Dm j₀ : ℕ} {b : ℝ}
    (Gw Gt : GenStage D ScalarH Dm b j₀) (M p Kout N depth sX sZ : ℕ)
    (η₀ tp tf cr : ℝ) (Z : ∀ v : CompIn Gt.comps, ℝ → TorusHk Kout (ScalarH v.1.root))
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn Gw.comps) (fun v => ScalarH v.1.root))
    (PZ : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kout - 2 * p) (ScalarH v.1.root))
    (aRep : ℝ → Vec 2 → ∀ v : CompIn Gw.comps, ScalarH v.1.root) : Prop :=
  (∀ (k : ℤ) (hk : Odd k),
    IsLiftSequence (familyLiftData D M k (nativeChain M k) (cr * liftLength D M)
        (Gw.fam.fiber ⟨k, hk⟩ (Gw.actual ⟨k, hk⟩)))
      sX sZ (D.slotStart M k / D.cellScaleSq M)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ M) / D.cellScaleSq M) N depth (CcT k)) ∧
  (∀ v, ∀ t ∈ Set.Icc tp tf,
    IsCovImage (covPolyP (termCovPrimitive D M tp t) p)
      (succReadout M (D.eps (M - 1)) η₀ Kout (fun v' => Z v' t) v) (PZ v t) ∧
    IsClassicalRep (PZ v t) (fun x => aRep t x v) (Kout - 2 * p))

/-- A realized lifted field supplies its two realization-independent input clauses. -/
theorem terminal_lift_data_of_lifted_field {D : OCData} {Dm j₀ : ℕ} {b : ℝ}
    {Gw Gt : GenStage D ScalarH Dm b j₀} {M p Kout N depth sX sZ K : ℕ}
    {η₀ tp tf cr : ℝ} {Z : ∀ v : CompIn Gt.comps, ℝ → TorusHk Kout (ScalarH v.1.root)}
    {CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn Gw.comps) (fun v => ScalarH v.1.root)}
    {PZ : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kout - 2 * p) (ScalarH v.1.root)}
    {aRep : ℝ → Vec 2 → ∀ v : CompIn Gw.comps, ScalarH v.1.root}
    {û : ∀ v : CompIn Gw.comps, ℝ → TorusHk K (ScalarH v.1.root)}
    (h : IsTerminalLiftedField Gw Gt M p Kout N depth sX sZ η₀ tp tf cr Z CcT PZ aRep û) :
    IsTerminalLiftData Gw Gt M p Kout N depth sX sZ η₀ tp tf cr Z CcT PZ aRep :=
  ⟨h.1, h.2.1⟩

/-- The terminal telescope with independent weak depth dW, order DW and positive χw.
No order-zero realization is assumed; the oscillatory conclusion constructs its regularity. -/
def TerminalUniformProfileStatement (Q : TerminalProfileProperty) : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ) ,
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Jw Lw dW DW : ℕ) (T₀ η₀ σw χw : ℝ), 1 ≤ Jw → 0 < T₀ → 0 < η₀ → η₀ ≤ ocDelta α q / 8 →
      0 < σw → σw < min (ocC α q) (q - 1) → 0 < χw →
    ∀ (PT QT : ℝ) (NT pT RT AT k₀ LcT LoT LfT LpT : ℕ) (tT : ℝ),
      IsTerminalSchedule α q s PT QT σw χw η₀ tT Jw Lw k₀ NT pT RT AT LcT LoT LfT
        LpT (termAlphabet NT pT DW dW) →
    ∀ Lr : ℕ,
    ∃ SX SZ : ℕ, ∀ sXT sZT : ℕ, SX ≤ sXT → SZ ≤ sZT →
    ∀ (cr : ℝ), 0 < cr → cr ≤ 1 →
    ∀ (Kw Kp : ℕ) (nW : ℕ+) (kW : InvConsts) (CL Cχ c C Cw cH : ℝ), 0 < c → 0 < cH →
    kW.G0 ≤ kW.Hprod + 1 →
    ∃ Cbound : ℝ, 0 ≤ Cbound ∧
    ∀ j₀ : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
      IsOCBandChain α q Λ ζ M D.κ → D.term = M →
    ∀ (PW : ProvParams) (a : ℝ)
      (Gw : GenStage D ScalarH (termD0bar NT pT DW dW) bw j₀) (lawW : BirthLaw)
      (aM : ℝ),
      IsWeakStage lawW PW φ₀ hφ₀ M (M + Jw) Jw dW DW nW kW a T₀ σw CL Cχ
        χw Gw aM →
    ∀ (tp : ℝ) (Pterm : (∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn Gw.comps, TorusHk Kp (ScalarH v.1.root))),
      IsTerminalPrepMap M Kw Kp c C Gw aM tp Pterm →
    ∀ (lawT : BirthLaw) (Gt' : GenStage D ScalarH (termD0bar NT pT DW dW) bw j₀),
      IsTerminalLaw lawW lawT cH η₀ (wordsUpTo (termAlphabet NT pT DW dW) RT).card →
      IsActualSuccessor D (termProvParams D Cw cr tT η₀ NT pT M)
        (termMenu (M + Jw) (termAlphabet NT pT DW dW) RT NT pT sXT sZT η₀ tp cr)
        Gw Gt' →
    ∀ (Kz : ℕ) (Z : ∀ v : CompIn (Gt'.retained M 1 RT).comps, ℝ → TorusHk Kz (ScalarH v.1.root))
      (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn Gw.comps) (fun v => ScalarH v.1.root))
      (PZ : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kz - 2 * pT) (ScalarH v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn Gw.comps, ScalarH v.1.root),
      IsTerminalLiftData Gw (Gt'.retained M 1 RT) M pT Kz NT dW sXT sZT η₀ tp (a + T₀) cr
        Z CcT PZ aRep →
    ∀ t ∈ Set.Icc tp (a + T₀),
    ∀ r : Representation (CompSpace (Gt'.retained M 1 RT).comps),
      IsRepresentationAt (D.eps (M - 1)) (Lr + (NT + 2 * pT) + 4) r →
      IsRepOf ((Gt'.retained M 1 RT).mass lawT)
        (fun v => truncateTorusHk (Nat.zero_le Kz) (Z v t)) r.value →
      Q s (D.eps (M - 1)) (D.eps M) Cbound (Lr + 3) (Lr + (NT + 2 * pT) + 4) r
        (readoutCLM M (D.eps (M - 1)) η₀ (Gw.mass lawW) ((Gt'.retained M 1 RT).mass lawT))
        (compField (Gw.mass lawW) (aRep t) - fun x =>
          readoutCLM M (D.eps (M - 1)) η₀ (Gw.mass lawW)
            ((Gt'.retained M 1 RT).mass lawT) (r.value x))
        (compField (Gw.mass lawW) (termLiftedRep Gw M NT dW cr CcT aRep t) -
          compField (Gw.mass lawW) (aRep t))

/-- Both finite-order periodic differences and their sum of physical profile costs. -/
def TerminalDifferenceProperty : TerminalProfileProperty :=
  fun s E e C k kin r _R cov osc =>
    ContDiff ℝ (k : ℕ) cov ∧ IsZ2Periodic cov ∧
    ContDiff ℝ (k : ℕ) osc ∧ IsZ2Periodic osc ∧
    profileNorm E k s cov + profileNorm e k s osc ≤
      ENNReal.ofReal C * representedSize s kin E r

/-- Actual terminal covariance and lift differences, for general dW and DW.
The terminal lift uses the oscillatory regularity at Lr = k₀ - 2; carrier realization is separate. -/
def TerminalDifferenceBoundsGeneralStatement : Prop :=
  TerminalUniformProfileStatement TerminalDifferenceProperty

/-- General-depth/order successor of the complete profile leaf. -/
def TerminalLiftProfileBoundsGeneralStatement : Prop :=
  TerminalUniformProfileStatement (fun s E e C k kin r R cov osc =>
    ‖R‖ ≤ C ∧ TerminalDifferenceProperty s E e C k kin r R cov osc)

/-- Add the uniform word-menu readout constant without changing any constant order. -/
theorem terminal_lift_profile_bounds_general_of_ingredients
    (hread : TerminalReadoutBoundsStatement)
    (hdiff : TerminalDifferenceBoundsGeneralStatement) :
    TerminalLiftProfileBoundsGeneralStatement := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λ₀, hΛ₀, htail⟩ := hdiff α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ φ₀ hφ₀ hφcd hφnn hφint hφsupp bw hbw hbw1 Jw Lw dW DW T₀ η₀ σw χw
    hJ hT hη hη1 hσ hσ1 hχ PT QT NT pT RT AT k₀ LcT LoT LfT LpT tT hsched Lr
  obtain ⟨SX, SZ, hreserve⟩ := htail Λ hΛ φ₀ hφ₀ hφcd hφnn hφint hφsupp bw hbw hbw1
    Jw Lw dW DW T₀ η₀ σw χw hJ hT hη hη1 hσ hσ1 hχ PT QT NT pT RT AT k₀ LcT LoT LfT LpT
    tT hsched Lr
  refine ⟨SX, SZ, ?_⟩
  intro sXT sZT hsXT hsZT cr hcr hcr1 Kw Kp nW kW CL Cχ c C Cw cH hc hcH hkw
  obtain ⟨Cdiff, hCdiff, hstart⟩ := hreserve sXT sZT hsXT hsZT cr hcr hcr1
    Kw Kp nW kW CL Cχ c C Cw cH hc hcH hkw
  let Cread := terminalReadoutConstant (termAlphabet NT pT DW dW) RT cH
  refine ⟨max Cread Cdiff, hCdiff.trans (le_max_right _ _), ?_⟩
  intro j₀
  obtain ⟨M₀, hMt⟩ := hstart j₀
  refine ⟨max 1 M₀, ?_⟩
  intro M hM D hDα hDq hDΛ hDζ hstream hband hterm PW a Gw lawW aM hstage tp Pterm hprep
    lawT Gt' hlaw hactual Kz Z CcT PZ aRep hlift t ht r hr hv
  have hd := hMt M (by omega) D hDα hDq hDΛ hDζ hstream hband hterm PW a Gw lawW aM hstage
    tp Pterm hprep lawT Gt' hlaw hactual Kz Z CcT PZ aRep hlift t ht r hr hv
  have hroots : ∀ v ∈ Gw.comps, v.births = [] := fun v hv => hstage.2.2.2.2.1 ⟨v, hv⟩
  have hsub : (Gt'.retained M 1 RT).comps ⊆
      succExtComps M (termAlphabet NT pT DW dW) RT Gw.comps := by
    intro v hv
    have hv' : v ∈ Gt'.comps := (Finset.mem_filter.mp hv).1
    rw [hactual.2.2.1, hstage.2.2.1] at hv'
    exact hv'
  have hR := hread D.q D.Λ M (hDq.symm ▸ hq.1) (hDΛ.symm ▸ hΛ₀.trans hΛ)
    (by omega) lawW lawT η₀ (termAlphabet NT pT DW dW) RT Gw.comps
    (Gt'.retained M 1 RT).comps hlaw.1 (by rw [hlaw.2.2.2.2.2.1]; positivity)
    hη.le hroots hsub
  rw [hlaw.2.2.1] at hR
  refine ⟨hR.trans (le_max_left _ _), hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1, ?_⟩
  exact hd.2.2.2.2.trans (mul_le_mul'
    (ENNReal.ofReal_le_ofReal (le_max_right Cread Cdiff)) le_rfl)

/-- The finite case is the dW = Jw*Rw, DW = 1+Jw*Nw instance. -/
theorem terminal_lift_profile_bounds_finite_of_general
    (hgen : TerminalLiftProfileBoundsGeneralStatement) : TerminalLiftProfileBoundsStatement := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λ₀, hΛ₀, ht⟩ := hgen α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ φ₀ hφ₀ hφcd hφnn hφint hφsupp bw hbw hbw1 Jw Nw Rw Lw T₀ η₀ σw
    hJ hT hη hη1 hσ hσ1 PT QT NT pT RT AT k₀ LcT LoT LfT LpT tT hsched Lr
  obtain ⟨SX, SZ, hreserve⟩ := ht Λ hΛ φ₀ hφ₀ hφcd hφnn hφint hφsupp bw hbw hbw1
    Jw Lw (Jw * Rw) (1 + Jw * Nw) T₀ η₀ σw (weakChi α q η₀)
    hJ hT hη hη1 hσ hσ1 (weakChi_pos hα₀ hq.1 hq.2.1 hη1)
    PT QT NT pT RT AT k₀ LcT LoT LfT LpT tT hsched Lr
  refine ⟨SX, SZ, ?_⟩
  intro sXT sZT hsXT hsZT cr hcr hcr1 Kw Kp nW kW CL Cχ c C Cw cH hc hcH hkw
  obtain ⟨Cbound, hCbound, hstart⟩ := hreserve sXT sZT hsXT hsZT cr hcr hcr1
    Kw Kp nW kW CL Cχ c C Cw cH hc hcH hkw
  refine ⟨Cbound, hCbound, ?_⟩
  intro j₀
  obtain ⟨M₀, hMt⟩ := hstart j₀
  refine ⟨M₀, ?_⟩
  intro M hM D hDα hDq hDΛ hDζ hstream hband hterm PW a Gw lawW aM hstage tp Pterm hprep
    lawT Gt' hlaw hactual Kz Z CcT PZ aRep û hlift t ht r hr hv
  exact hMt M hM D hDα hDq hDΛ hDζ hstream hband hterm PW a Gw lawW aM hstage
    tp Pterm hprep lawT Gt' hlaw hactual Kz Z CcT PZ aRep
    (terminal_lift_data_of_lifted_field hlift) t ht r hr hv

end AVRegularity.Finite.TerminalLift
end
end
