-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Definitions.Entry.TerminalResidualClauses
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.EntryTerminal.Route

/-! The binder blocks of `entry_terminal_of_weak` as data, and its body after the public order as
one predicate (`TerminalTail`, a verbatim copy). The route's ingredients are stated for these
bundles.

* `TermConstruction`: the construction `(α, s, q, ζ)` with its hypotheses.
* `TermArgs X`: every universally quantified datum of the statement between `Λ` and `K_out` (the
  menus, the weak physical data, the terminal schedule, the seed exponents, the preservation
  menus and the fresh kernel order); `TermArgs.Valid` collects their hypotheses, in the statement's
  order.
* `TerminalTail`: the statement's text after `∀ Kout : ℕ,`, with the prefix as parameters (the three
  prefix data `A_T, L_c^T, σ₀` do not occur in it). `TermArgs.tail` instantiates it.
* `IsTermData`: the hypotheses of the statement on the construction data `D` at level `M`.

The bundles carry no constraint beyond the statement's own hypotheses; `Valid` is their
conjunction in the statement's order, so a datum with `J_w = 0` or `τ = T₀` is excluded exactly as
in the statement. -/

/-- The construction parameters of the terminal entry, with their hypotheses. -/
structure TermConstruction where
  α : ℝ
  s : ℝ
  q : ℝ
  ζ : ℝ → ℝ
  hα₀ : 0 < α
  hα₁ : α < 1 / 3
  hs₀ : 0 < s
  hs₁ : s < (1 - α) / 2
  hq : IsAdmissibleQ α s q
  hζ : IsFastProfile ζ

/-- The data of `entry_terminal_of_weak` between `Λ` and `K_out`. -/
structure TermArgs (X : TermConstruction) where
  Λ : ℕ
  c₀max : ℝ
  φ₀ : Vec 2 → ℝ
  hφ₀ : Integrable φ₀
  bw : ℝ
  Jw : ℕ
  Lw : ℕ
  dW : ℕ
  DW : ℕ
  L0w : ℕ
  τ : ℝ
  T₀ : ℝ
  Pw : ℝ
  σw : ℝ
  χw : ℝ
  η₀ : ℝ
  PT : ℝ
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
  QT : ℝ
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

namespace TermArgs

variable {X : TermConstruction} (A : TermArgs X)

/-- The hypotheses of `entry_terminal_of_weak` on its data, in the statement's order. -/
def Valid : Prop :=
  0 < A.c₀max ∧
  (ContDiff ℝ (⊤ : ℕ∞) A.φ₀ ∧ (∀ z, 0 ≤ A.φ₀ z) ∧ ∫ z, A.φ₀ z = 1 ∧
    Function.support A.φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall) ∧
  (0 < A.bw ∧ A.bw ≤ 1 / 10000) ∧
  (1 ≤ A.Jw ∧ 0 < A.τ ∧ A.τ < A.T₀ ∧ 0 < A.Pw ∧ 0 < A.σw ∧ A.σw < min (ocC X.α X.q) (X.q - 1) ∧
    0 < A.χw ∧ 0 < A.η₀ ∧ A.η₀ ≤ ocDelta X.α X.q / 8) ∧
  0 < A.PT ∧
  IsTerminalSchedule X.α X.q X.s A.PT A.QT A.σw A.χw A.η₀ A.tT A.Jw A.Lw A.k₀ A.NT A.pT A.RT A.AT
    A.LcT A.LoT A.LfT A.LpT (termAlphabet A.NT A.pT A.DW A.dW) ∧
  IsEntrySeedExponents X.α X.q A.σw A.χw A.η₀ A.tT A.τe A.lamE A.NT A.pT A.DW A.dW ∧
  IsFreshKernelOrder A.nT A.LcT A.Lpr A.Lc A.Lf ∧
  -- the weak order floor (the composition `entry_terminal` has `D_W = 1 + J_w N_w`)
  1 ≤ A.DW

/-- The order index `D̄₀` of the weak and terminal stages. -/
abbrev Dt : ℕ := termD0bar A.NT A.pT A.DW A.dW

/-- The order index of the seed. -/
abbrev Ds : ℕ := succSchedD A.Dt A.N A.p (A.H + 1)

/-- The seed depth bound `r̄₀`. -/
abbrev r0 : ℕ := termR0bar A.RT A.dW

/-- The terminal alphabet. -/
abbrev alph : Finset WordLetter := termAlphabet A.NT A.pT A.DW A.dW

/-- The number of terminal words. -/
abbrev nWords : ℕ := (wordsUpTo A.alph A.RT).card

/-- The internal model order `K̂`. -/
abbrev Khat (Kout : ℕ) : ℕ := max Kout (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))

/-- The provenance parameters of the terminal passage. -/
abbrev Pt (D : OCData) (Cw cr : ℝ) (M : ℕ) : ProvParams :=
  termProvParams D Cw cr A.tT A.η₀ A.NT A.pT M

/-- The terminal menu at the anchor `t_p`. -/
abbrev Mt (M sX sZ : ℕ) (tp cr : ℝ) : SuccMenu :=
  termMenu (M + A.Jw) A.alph A.RT A.NT A.pT sX sZ A.η₀ tp cr

/-- The weak paired kernels. -/
abbrev Kw_ (D : OCData) (M : ℕ) (nW : ℕ+) : ℕ → KernelSpec :=
  fun _ => isoPairedKernel (D.termRW A.σw M) nW

/-- The fresh terminal kernels. -/
abbrev Kn_ (D : OCData) (M : ℕ) (cr : ℝ) : ℕ → KernelSpec :=
  fun _ => isoPairedKernel (D.termRNew cr A.tT M) A.nT

end TermArgs

/-- The hypotheses of `entry_terminal_of_weak` on the construction data `D` at level `M`. -/
def IsTermData (X : TermConstruction) (Λ M : ℕ) (D : OCData) : Prop :=
  D.α = X.α ∧ D.q = X.q ∧ D.Λ = Λ ∧ D.ζ = X.ζ ∧ IsOCStreamSeq X.α X.q Λ X.ζ D.Φ ∧
    IsOCBandChain X.α X.q Λ X.ζ M D.κ ∧ D.term = M

/-- The text of `entry_terminal_of_weak` after `∀ Kout : ℕ,` (verbatim). -/
def TerminalTail (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (c₀max : ℝ) (φ₀ : Vec 2 → ℝ)
    (hφ₀ : Integrable φ₀) (bw : ℝ) (Jw Lw dW DW L0w : ℕ) (τ T₀ Pw σw χw η₀ PT : ℝ)
    (NT pT RT k₀ LoT LfT LpT : ℕ) (tT QT τe lamE : ℝ) (H J N p Kres Lpr Lc Lf : ℕ) (nT : ℕ+)
    (Kout : ℕ) : Prop :=
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

/-- The tail of the statement at the bundled data. -/
abbrev TermArgs.tail {X : TermConstruction} (A : TermArgs X) (Kout : ℕ) : Prop :=
  TerminalTail X.α X.s X.q X.ζ A.Λ A.c₀max A.φ₀ A.hφ₀ A.bw A.Jw A.Lw A.dW A.DW A.L0w A.τ A.T₀
    A.Pw A.σw A.χw A.η₀ A.PT A.NT A.pT A.RT A.k₀ A.LoT A.LfT A.LpT A.tT A.QT A.τe A.lamE A.H A.J
    A.N A.p A.Kres A.Lpr A.Lc A.Lf A.nT Kout

/-- The statement's text at a fixed threshold level `M` (from the data onwards), over the bundled
data. -/
def BTailAtM {X : TermConstruction} (A : TermArgs X) (Kout : ℕ) (sXT : ℕ) (sZT : ℕ) (Kw : ℕ) (Lt : ℕ) (nW : ℕ+) (hk₀w : A.k₀ ≤ Kw) (cr : ℝ) (kS : InvConsts) (cK : ℝ) (CK : ℝ) (CL : ℝ) (Cχ : ℝ) (Cread : ℝ) (Cid : ℝ) (kW : InvConsts) (c : ℝ) (C : ℝ) (Centry : ℝ) (cH : ℝ) (Ce : ℝ) (Cw : ℝ) (j₀ : ℕ) (M : ℕ) : Prop :=
  ∀ (D : OCData), D.α = X.α → D.q = X.q → D.Λ = A.Λ → D.ζ = X.ζ → IsOCStreamSeq X.α X.q A.Λ X.ζ D.Φ →
    IsOCBandChain X.α X.q A.Λ X.ζ M D.κ → D.term = M →
  ∀ (a : ℝ) (lawW : BirthLaw) (PW : ProvParams)
    (Gw : GenStage D ScalarH (termD0bar A.NT A.pT A.DW A.dW) A.bw j₀) (aM : ℝ)
    (Ww : ℝ → (CompIn Gw.comps → Vec 2 → ℝ) → Vec 2 → ℝ),
    IsWeakStage lawW PW A.φ₀ A.hφ₀ M (M + A.Jw) A.Jw A.dW A.DW nW kW a A.T₀ A.σw CL Cχ A.χw Gw aM →
  ∃ (tp : ℝ) (Pterm : (∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn Gw.comps, TorusHk (max Kout (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) (ScalarH v.1.root)))
    (lawT : BirthLaw) (Gt' : GenStage D ScalarH (termD0bar A.NT A.pT A.DW A.dW) A.bw j₀) (seed : GenStage D ScalarH (succSchedD (termD0bar A.NT A.pT A.DW A.dW) A.N A.p (A.H + 1)) A.bw j₀)
    (rootM rootR : ℕ → ℝ) (seedKc : ℕ → KernelSpec)
    (ι : CompIn (Gt'.retained M 1 A.RT).comps ≃ CompIn seed.comps),
    IsTerminalPrepMap M Kw (max Kout (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) c C Gw aM tp Pterm ∧
    IsTerminalLaw lawW lawT cH A.η₀ (wordsUpTo (termAlphabet A.NT A.pT A.DW A.dW) A.RT).card ∧
    IsActualSuccessor D (termProvParams D Cw cr A.tT A.η₀ A.NT A.pT M)
      (termMenu (M + A.Jw) (termAlphabet A.NT A.pT A.DW A.dW) A.RT A.NT A.pT sXT sZT A.η₀ tp cr) Gw Gt' ∧
    IsSeedEncoding (termProvParams D Cw cr A.tT A.η₀ A.NT A.pT M) lawT rootM rootR
      (fun _ => isoPairedKernel (D.termRW A.σw M) nW) (fun _ => isoPairedKernel (D.termRNew cr A.tT M) A.nT)
      seedKc (Gt'.retained M 1 A.RT) seed ι ∧
    TerminalSeedClauses rootM rootR seedKc A.φ₀ A.hφ₀ (M + A.Jw) (M - 1) kS Ce A.τe (termR0bar A.RT A.dW) (termD0bar A.NT A.pT A.DW A.dW) seed
      (tp + D.termH M) (a + A.T₀) ∧
    tp + D.termH M + 3 * ocTau X.α X.q A.Λ (M - 1) + 4 * ocTauPP X.α X.q A.Λ (M - 1) ≤ a + A.T₀ ∧
    ∀ (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ)
      (U₀ : ∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root))
      (U V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root))
      (Uw Vw : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
      (Uk Vk : ∀ v u (_ : Gw.fam.Γ v u), ℝ → TorusHk (Kw + (termD0bar A.NT A.pT A.DW A.dW) - 1) (ScalarH u.1.root)),
      IsWeakPaired PW A.φ₀ A.hφ₀ lawW M Kw Lt nW a A.T₀ A.σw A.χw cK CK f Gw aM U₀ U V Uw Vw Uk Vk →
      IsWeakReadout lawW M A.Jw A.Lw Kw (D.κ M) a A.τ A.T₀ X.s A.Pw cK Cread Cid f θ Gw Ww V →
      IsTerminalPrepBounds lawW M Kw (max Kout (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) A.k₀ hk₀w (le_trans (by omega : A.k₀ ≤ 2 * A.k₀ + 2) (le_trans (le_max_left _ _) (le_max_right Kout _))) cr cK C A.QT f Gw aM tp Pterm V ∧
      ∃ Z : ∀ v : CompIn (Gt'.retained M 1 A.RT).comps, ℝ → TorusHk (max Kout (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) (ScalarH v.1.root),
        TerminalFamilyClauses (termProvParams D Cw cr A.tT A.η₀ A.NT A.pT M)
          (fun _ => isoPairedKernel (D.termRW A.σw M) nW)
          (fun _ => isoPairedKernel (D.termRNew cr A.tT M) A.nT) A.φ₀ A.hφ₀ lawW lawT rootM M (max Kout (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) cr C
          Centry tp (tp + D.termH M) (a + A.T₀) f Gw (Gt'.retained M 1 A.RT) seed ι
          (Pterm fun v => V v aM) Z ∧
        EntryIdentityClauses Gw (Gt'.retained M 1 A.RT) M A.pT (max Kout (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) Kw A.Lw A.NT A.dW sXT sZT A.η₀ tp a A.τ A.T₀ X.s
          A.Pw A.PT C cr f θ Ww V Z

/-- The statement's text after the weak constants (the constants, the carrier start, the threshold),
over the bundled data. -/
def BTailConsts {X : TermConstruction} (A : TermArgs X) (Kout : ℕ) (sXT : ℕ) (sZT : ℕ) (Kw : ℕ) (Lt : ℕ) (nW : ℕ+) (hk₀w : A.k₀ ≤ Kw) (cr : ℝ) (kS : InvConsts) (cK : ℝ) (CK : ℝ) (CL : ℝ) (Cχ : ℝ) (Cread : ℝ) (Cid : ℝ) (kW : InvConsts) : Prop :=
  ∃ (c C Centry cH Ce Cw : ℝ), 0 < c ∧ 0 < cH ∧ 1 ≤ Ce ∧
  ∃ (CHt Υt : ℝ), 1 ≤ CHt ∧ 0 < Υt ∧
  ∀ j₀ : ℕ, IsCarrierStart X.α X.q A.Λ A.bw CHt Υt j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
  BTailAtM A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW c C Centry cH Ce Cw j₀ M

/-- The statement's tail over the bundled data, layered (`BTailConsts`, `BTailAtM`). -/
def BTail {X : TermConstruction} (A : TermArgs X) (Kout : ℕ) : Prop :=
  ∃ SX SZ : ℕ, ∀ sXT sZT : ℕ, SX ≤ sXT → SZ ≤ sZT →
  ∃ (Kw Lt : ℕ) (nW : ℕ+) (hk₀w : A.k₀ ≤ Kw) (_hLw : A.Lw + 5 ≤ Kw) (cr : ℝ) (kS : InvConsts),
    A.L0w ≤ Lt ∧ A.LpT ≤ Lt ∧ Lt + 1 ≤ 2 * (nW : ℕ) ∧ IsTerminalKernelOrders nW A.LoT A.LfT A.LpT A.Lpr A.Lc A.Lf ∧
    0 < cr ∧ kS.cr = cr ∧ 0 < kS.c₀ ∧ kS.c₀ ≤ A.c₀max ∧ kS.cr ≤ 1 ∧
    kS.σf = ocDelta X.α X.q ∧ kS.lamC = A.lamE ∧
    IsSeedAllocation kS (termR0bar A.RT A.dW) (termD0bar A.NT A.pT A.DW A.dW) A.H A.J A.N A.p A.Kres A.Lpr A.Lc A.Lf ∧
    (kS.mEnv = 0 ∧ kS.Kan = kS.Ks ∧ kS.Lan = kS.Ks ∧ kS.Jm = kS.Ks) ∧
    Lt + A.DW + max (A.Lw + 5) A.k₀ ≤ Kw ∧
    cr = 1 ∧
  ∀ (cK CK CL Cχ Cread Cid : ℝ) (kW : InvConsts), 0 < cK → kW.c₀ = cK →
    IsWeakAllocation kW kS Lt →
  BTailConsts A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW

/-- The layered bundled tail is the statement's tail. -/
theorem tail_of_bTail {X : TermConstruction} (A : TermArgs X) (Kout : ℕ) (h : BTail A Kout) :
    A.tail Kout := h

end AVRegularity.EntryTerminal.Route
end
end

section
@[expose] public noncomputable section
section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.EntryTerminal.Route

/-! Text copies of the two statements that the top-level assembly of
`entry_terminal_of_weak` consumes, in their capped form: the capped preparation
(`entry_terminal_preparation`) and the first-cycle error energy
(`entry_terminal_error_energy`). The assembly takes them as hypotheses. The residual
(`entry_terminal_residual`) is an ingredient of the error energy only and does not occur here. -/

/-- The capped preparation: the text of `entry_terminal_preparation`. -/
def PreparationStatement : Prop :=
  ∀ (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ),
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
      (Ww : ℝ → (CompIn Gw.comps → Vec 2 → ℝ) → Vec 2 → ℝ),
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
        IsTerminalPrepBounds lawW M Kw (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) k₀ hk₀w (le_trans (by omega : k₀ ≤ 2 * k₀ + 2) (le_trans (le_max_left _ _) (le_max_right Kout _))) cr cK C QT f Gw aM tp Pterm V

/-- The error energy: the text of `entry_terminal_error_energy`. -/
def ErrorEnergyStatement : Prop :=
  ∀ (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ),
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
          ENNReal.ofReal (C * D.eps (M - 1) ^ (QT / 2) * Real.sqrt (l2NormSq f))

/-! The named ingredients of the terminal route other than the capped preparation and the error energy (`Route/TargetCopies`). Each is stated
for the bundled data of `Route/Tail` and is consumed by `Route/Assembly`.

* `SuccessorStatement`: the actual terminal successor exists, at every anchor and witness
  constant (the level-`M` instance of `successor_exists`).
* `SeedEncodingStatement`: every stage has a re-rooting onto a seed at a larger order index,
  keeping its registry.
* `SeedClausesStatement`: the seed clauses and the certificates of the retained family.
* `CoarseFamilyStatement`: the first coarse family from the prepared trace.
* `LiftFieldStatement`: the lifted field exists and every lifted field of order `0` has a
  realization of order `k₀` with a gradient representative and a classical representative.
* `ReadoutGlueStatement`: the energy bound and the weak readout give the terminal identity.
* `TruncationStatement`: the statement's tail at a public order gives it at every smaller one.
* `TruncationPartsStatement`: the preparation, coarse-family and retained clauses at the
  internal order `K̂ + 3` give them at `K̂` for the truncations.
* `PlanStatement`, `DeadlineStatement`, `ReadoutScaleStatement`, `ScaleFactsStatement`,
  `PrepMonotoneStatement`: plan arithmetic, the composition deadline, the readout scale
  inequality, positivity of the scales, and monotonicity of the preparation clauses in their
  constant.

Order of choices (the statement's): menus `→` lift floors `→` plan `→` weak constants `→` constants
`→` carrier start `→` threshold `→` data. Every statement below keeps it; constants that the
statement fixes once (`C`) are reached from above (`∀ C ≥ C₀`) where a statement contributes to them.

Quiet sets: the anchor `t_p` is quiet in sense `ocQuietTimes`, as in
`IsTerminalPrepMap`; the seed clauses inherit the untrimmed quiet clause of `IsStageInvariant`
and are stated for the untrimmed quiet set. -/

section
/-- The constructor steps of the terminal producer on a weak expression before the seed slot:
cell degree `N_T + D_w`, outgoing tested order `D̄₀`, covariance order `2p_T`. -/
abbrev TermArgs.stepCount {X : TermConstruction} (A : TermArgs X) : ℕ :=
  (A.NT + A.DW) + A.Dt + 2 * A.pT

/-- The successor statement at a fixed threshold level `M`. -/
def SuccAtM {X : TermConstruction} (A : TermArgs X) (sXT sZT : ℕ) (nW : ℕ+) (cr CL Cχ : ℝ)
    (kW : InvConsts) (j₀ M : ℕ) : Prop :=
  ∀ D : OCData, IsTermData X A.Λ M D →
  ∀ (a : ℝ) (lawW : BirthLaw) (PW : ProvParams) (Gw : GenStage D ScalarH A.Dt A.bw j₀) (aM : ℝ),
    IsWeakStage lawW PW A.φ₀ A.hφ₀ M (M + A.Jw) A.Jw A.dW A.DW nW kW a A.T₀ A.σw CL Cχ A.χw
      Gw aM →
  ∀ (tp Cw : ℝ), 0 ≤ Cw → ∃ Gt' : GenStage D ScalarH A.Dt A.bw j₀,
    IsActualSuccessor D (A.Pt D Cw cr M) (A.Mt M sXT sZT tp cr) Gw Gt'

/-- **The terminal successor.** For the actual weak stage, every anchor `t_p` and every
witness constant `C_w`, an actual successor at the terminal menu exists (lifts and means by the
triangular cell recursion with transverse inverses). It is the level-`M`
instance of the stage-generic `successor_exists`.

For an empty weak family the successor has only the fresh components that the menu adds to an
empty set. The floor `s_X = S_X` is attained, and `c_r = 1` is allowed. -/
def SuccessorStatement : Prop :=
  ∀ X : TermConstruction, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ A : TermArgs X, Λ₀ ≤ A.Λ → A.Valid →
  ∃ SX SZ : ℕ, ∀ sXT sZT : ℕ, SX ≤ sXT → SZ ≤ sZT →
  ∀ (Lt : ℕ) (nW : ℕ+) (cr : ℝ) (kS : InvConsts), 0 < cr → cr ≤ 1 →
  ∀ (cK CL Cχ : ℝ) (kW : InvConsts), 0 < cK → kW.c₀ = cK → IsWeakAllocation kW kS Lt →
  ∃ (CHe Υe : ℝ), 1 ≤ CHe ∧ 0 < Υe ∧
  ∀ j₀ : ℕ, IsCarrierStart X.α X.q A.Λ A.bw CHe Υe j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    SuccAtM A sXT sZT nW cr CL Cχ kW j₀ M

/-- **The re-rooting.** In the OC regime (`1 < q`, `128 ≤ Λ`, so that every component mass
and readout weight is positive), every stage has a re-rooting onto a seed at a larger order index,
with positive roots, keeping its registry (`IsSeedEncoding` leaves the registry free).
The regime premises are needed because, with `Λ = 0` a born component has
mass zero, which `IsSeedEncoding` must copy to a positive root.

A stage without components has the empty seed and the empty bijection, and `Dt = Ds` is allowed.
In a singleton stage with a born component the mass `compMass q Λ law c` is positive
(`birth_compMass_pos`), so the root mass is positive. Distinct seed components have distinct roots,
since every seed component has `births = []`. -/
def SeedEncodingStatement : Prop :=
  ∀ {D : OCData} {Dt Ds : ℕ} {b : ℝ} {j₀ : ℕ}, Dt ≤ Ds → 1 < D.q → 128 ≤ D.Λ →
  ∀ (Pt : ProvParams) (lawT : BirthLaw) (seedKt freshKt : ℕ → KernelSpec)
    (Gt : GenStage D ScalarH Dt b j₀),
  ∃ (seed : GenStage D ScalarH Ds b j₀) (rootM rootR : ℕ → ℝ) (seedKc : ℕ → KernelSpec)
    (ι : CompIn Gt.comps ≃ CompIn seed.comps),
    IsSeedEncoding Pt lawT rootM rootR seedKt freshKt seedKc Gt seed ι ∧ (∀ r, 0 < rootM r) ∧
      (∀ r, 0 < rootR r) ∧ ∀ (i : ℕ) (p : ℤ) (e : Gen .ctx i p), seed.exports e ↔ Gt.exports e

/-- The skeleton of seed constants: the envelope constants `C_a`, `C_m` set to `0`. The plan
fixes the skeleton first and the envelope constants after it. -/
def seedSkeleton (k : InvConsts) : InvConsts :=
  { k with Ca := 0, Cm := fun _ => 0 }

/-- Floors on the seed constants that the plan must meet, as functions of the weak kernel order
`n_W` (the kernel constants `c_ker`, `Γ_k`, the width constant `C_wid`, the envelope constants
`C_a`, `C_m`): the seed's kernels and envelopes are those of the terminal passage, fixed by `n_W`.
The envelope floors `C_a^O`, `C_m^O` also read the skeleton of the seed constants (its orders and
reserves, `seedSkeleton`): the envelope estimate fixes its constants after the orders and the
reserves (`ContextEnvelopeEstimate`). They default to `0`. -/
structure SeedFloors where
  cker : ℕ+ → ℕ → ℝ
  Γk : ℕ+ → ℝ
  Cwid : ℕ+ → ℝ
  Ca : ℕ+ → ℝ
  Cm : ℕ+ → ℕ → ℝ
  CaO : ℕ+ → InvConsts → ℝ := fun _ _ => 0
  CmO : ℕ+ → InvConsts → ℕ → ℝ := fun _ _ _ => 0

/-- The seed constants meet the floors at the weak kernel order `n_W`; the envelope floors
`C_a^O`, `C_m^O` are read at the skeleton of `k_S`. -/
def SeedFloors.Meets (F : SeedFloors) (nW : ℕ+) (kS : InvConsts) : Prop :=
  (∀ j, F.cker nW j ≤ kS.cker j) ∧ F.Γk nW ≤ kS.Γk ∧ F.Cwid nW ≤ kS.Cwid ∧ F.Ca nW ≤ kS.Ca ∧
    (∀ j, F.Cm nW j ≤ kS.Cm j) ∧ F.CaO nW (seedSkeleton kS) ≤ kS.Ca ∧
    ∀ j, F.CmO nW (seedSkeleton kS) j ≤ kS.Cm j

/-- The plan premises of the seed side: the statement's plan, the reserve floor `K_S`, the offset floor,
the kernel moment cap `L_ker ≤ max{L_pr, L_c, L_f}` (with the kernel orders it gives
`L_ker + 1 ≤ 2n_W` and `≤ 2n_T`, so the seed's paired and fresh kernels are admissible at `L_ker`),
and the floors `F` on the seed constants. The radius constant is capped by `1` as well as by
`c₀max` (the plan takes `c₀ = min 1 c₀max`): the envelope estimate needs `ρ_* ≤ ε` at the seed. -/
def SeedPlan {X : TermConstruction} (A : TermArgs X) (KS : ℕ) (F : SeedFloors) (Lt : ℕ) (nW : ℕ+)
    (cr : ℝ) (kS : InvConsts) : Prop :=
  A.L0w ≤ Lt ∧ A.LpT ≤ Lt ∧ Lt + 1 ≤ 2 * (nW : ℕ) ∧
    IsTerminalKernelOrders nW A.LoT A.LfT A.LpT A.Lpr A.Lc A.Lf ∧
    0 < cr ∧ cr ≤ 1 ∧ kS.cr = cr ∧ 0 < kS.c₀ ∧ kS.c₀ ≤ min 1 A.c₀max ∧ KS ≤ kS.Ks ∧
    max 1 A.stepCount ≤ kS.G0 ∧ kS.σf = ocDelta X.α X.q ∧ kS.lamC = A.lamE ∧
    IsSeedAllocation kS A.r0 A.Dt A.H A.J A.N A.p A.Kres A.Lpr A.Lc A.Lf ∧
    kS.Lker ≤ max A.Lpr (max A.Lc A.Lf) ∧ F.Meets nW kS

/-- The per-level context of the seed side: the data, the weak stage, the quiet anchor placed by the
preparation, the terminal law, an actual successor, a re-rooting of its retained family keeping the
registry, with positive roots. -/
def SeedCtx {X : TermConstruction} (A : TermArgs X) (sXT sZT : ℕ) (nW : ℕ+) (cr CL Cχ : ℝ)
    (kW : InvConsts) (cP CP cH Cw : ℝ) {j₀ : ℕ} (M : ℕ) (D : OCData) (a : ℝ) (lawW : BirthLaw)
    (PW : ProvParams) (Gw : GenStage D ScalarH A.Dt A.bw j₀) (aM tp : ℝ) (lawT : BirthLaw)
    (Gt' : GenStage D ScalarH A.Dt A.bw j₀) (seed : GenStage D ScalarH A.Ds A.bw j₀)
    (rootM rootR : ℕ → ℝ) (seedKc : ℕ → KernelSpec)
    (ι : CompIn (Gt'.retained M 1 A.RT).comps ≃ CompIn seed.comps) : Prop :=
  IsTermData X A.Λ M D ∧
    IsWeakStage lawW PW A.φ₀ A.hφ₀ M (M + A.Jw) A.Jw A.dW A.DW nW kW a A.T₀ A.σw CL Cχ A.χw
      Gw aM ∧
    tp ∈ ocQuietTimes D.α D.q D.Λ D.ζ M ∧ aM + cP * D.termH M ≤ tp ∧ tp ≤ aM + CP * D.termH M ∧
    IsTerminalLaw lawW lawT cH A.η₀ A.nWords ∧
    IsActualSuccessor D (A.Pt D Cw cr M) (A.Mt M sXT sZT tp cr) Gw Gt' ∧
    IsSeedEncoding (A.Pt D Cw cr M) lawT rootM rootR (A.Kw_ D M nW) (A.Kn_ D M cr) seedKc
      (Gt'.retained M 1 A.RT) seed ι ∧
    (∀ (i : ℕ) (p : ℤ) (e : Gen .ctx i p), seed.exports e ↔ (Gt'.retained M 1 A.RT).exports e) ∧
    (∀ r, 0 < rootM r) ∧ (∀ r, 0 < rootR r)

/-- The seed clauses at a fixed threshold level `M`. -/
def SeedAtM {X : TermConstruction} (A : TermArgs X) (Kout sXT sZT : ℕ) (nW : ℕ+) (cr : ℝ)
    (kS : InvConsts) (CL Cχ : ℝ) (kW : InvConsts) (cP CP cH Ce Cw : ℝ) (cker : ℕ → ℝ)
    (j₀ M : ℕ) : Prop :=
  ∀ (D : OCData) (a : ℝ) (lawW : BirthLaw) (PW : ProvParams) (Gw : GenStage D ScalarH A.Dt A.bw j₀)
    (aM tp : ℝ) (lawT : BirthLaw) (Gt' : GenStage D ScalarH A.Dt A.bw j₀)
    (seed : GenStage D ScalarH A.Ds A.bw j₀) (rootM rootR : ℕ → ℝ) (seedKc : ℕ → KernelSpec)
    (ι : CompIn (Gt'.retained M 1 A.RT).comps ≃ CompIn seed.comps),
    SeedCtx A sXT sZT nW cr CL Cχ kW cP CP cH Cw M D a lawW PW Gw aM tp lawT Gt' seed rootM rootR
      seedKc ι →
    TerminalSeedClauses rootM rootR seedKc A.φ₀ A.hφ₀ (M + A.Jw) (M - 1) kS Ce A.τe A.r0 A.Dt
        seed (tp + D.termH M) (a + A.T₀) ∧
      TerminalRetainedClauses lawT (A.Pt D Cw cr M) (A.Kw_ D M nW) (A.Kn_ D M cr) A.φ₀ A.hφ₀
        cker M (A.Khat Kout) cr tp (a + A.T₀) (Gt'.retained M 1 A.RT)

/-- **The seed clauses.** For the actual weak stage, a quiet anchor placed by the preparation, the
terminal law, an actual successor and a re-rooting keeping the registry: the seed clauses of the
statement, and the certificates of the retained family at the internal order `K̂`. The offset floor
`max 1 s_T ≤ k_S.G₀` is the reserve gap. The floors `F` on the seed constants are named before the
plan, which meets them (`PlanStatement`); the roots of the re-rooting are positive
(`SeedEncodingStatement`).

For an empty retained family the mass sums are `0 < 5/6` and the certificates are vacuous. For
`K_out = 0`, `K̂ = max (2k₀+2) (N_T+2p_T+k₀+2)`, and `k_S.G₀ = max 1 s_T` is the smallest offset. -/
def SeedClausesStatement : Prop :=
  ∀ X : TermConstruction, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ A : TermArgs X, Λ₀ ≤ A.Λ → A.Valid →
  ∀ Kout : ℕ, ∃ SX SZ : ℕ, ∀ sXT sZT : ℕ, SX ≤ sXT → SZ ≤ sZT →
  ∃ (KS : ℕ) (F : SeedFloors),
  ∀ (Lt : ℕ) (nW : ℕ+) (cr : ℝ) (kS : InvConsts), SeedPlan A KS F Lt nW cr kS →
  ∀ (cK CL Cχ : ℝ) (kW : InvConsts), 0 < cK → kW.c₀ = cK → IsWeakAllocation kW kS Lt →
  ∀ (cP CP : ℝ), 0 < cP →
  ∃ cH : ℝ, 0 < cH ∧ cH ≤ 1 ∧ ∃ Cw₀ : ℝ, ∀ Cw : ℝ, Cw₀ ≤ Cw →
  ∃ (Ce CHe Υe : ℝ) (cker : ℕ → ℝ), 1 ≤ Ce ∧ 0 ≤ Cw ∧ 1 ≤ CHe ∧ 0 < Υe ∧
  ∀ j₀ : ℕ, IsCarrierStart X.α X.q A.Λ A.bw CHe Υe j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    SeedAtM A Kout sXT sZT nW cr kS CL Cχ kW cP CP cH Ce Cw cker j₀ M

/-- The coarse family at a fixed threshold level `M`. -/
def CoarseAtM {X : TermConstruction} (A : TermArgs X) (Kout : ℕ) (nW : ℕ+) (cr cP CP cH : ℝ)
    (cker : ℕ → ℝ) (C Centry : ℝ) (M : ℕ) : Prop :=
  ∀ (j₀ : ℕ) (D : OCData), IsTermData X A.Λ M D →
  ∀ (sXT sZT : ℕ) (a aM tp Cw : ℝ) (lawW lawT : BirthLaw) (Gw Gt' : GenStage D ScalarH A.Dt A.bw j₀)
    (seed : GenStage D ScalarH A.Ds A.bw j₀) (rootM rootR : ℕ → ℝ) (seedKc : ℕ → KernelSpec)
    (ι : CompIn (Gt'.retained M 1 A.RT).comps ≃ CompIn seed.comps),
    Gw.level = M → (∀ v : CompIn Gw.comps, v.1.births = []) → aM + cP * D.termH M ≤ tp →
    tp + D.termH M + 3 * ocTau X.α X.q A.Λ (M - 1) + 4 * ocTauPP X.α X.q A.Λ (M - 1) ≤ a + A.T₀ →
    IsTerminalLaw lawW lawT cH A.η₀ A.nWords →
    IsActualSuccessor D (A.Pt D Cw cr M) (A.Mt M sXT sZT tp cr) Gw Gt' →
    IsSeedEncoding (A.Pt D Cw cr M) lawT rootM rootR (A.Kw_ D M nW) (A.Kn_ D M cr) seedKc
      (Gt'.retained M 1 A.RT) seed ι →
    TerminalRetainedClauses lawT (A.Pt D Cw cr M) (A.Kw_ D M nW) (A.Kn_ D M cr) A.φ₀ A.hφ₀
      cker M (A.Khat Kout) cr tp (a + A.T₀) (Gt'.retained M 1 A.RT) →
  ∀ (f : Vec 2 → ℝ) (g : ∀ v : CompIn Gw.comps, TorusHk (A.Khat Kout) (ScalarH v.1.root)),
    weightedNorm (D.termRho cr M) (Gw.mass lawW) (fun _ => 1) g ≤ CP * Real.sqrt (l2NormSq f) →
  ∃ Z : ∀ v : CompIn (Gt'.retained M 1 A.RT).comps, ℝ → TorusHk (A.Khat Kout) (ScalarH v.1.root),
    TerminalFamilyClauses (A.Pt D Cw cr M) (A.Kw_ D M nW) (A.Kn_ D M cr) A.φ₀ A.hφ₀ lawW lawT
      rootM M (A.Khat Kout) cr C Centry tp (tp + D.termH M) (a + A.T₀) f Gw
      (Gt'.retained M 1 A.RT) seed ι g Z

/-- **The first coarse family.** From a prepared trace `g` with `|g|_{ρ,K̂;π} ≤ C_P‖f‖₂`, the
retained system has its solution `Z` on `[t_p, a+T₀]` with the energy, the readout norm and the
outgoing datum. It uses
the certificates of the seed clauses, not their proof. The constant is reached from above.

For `g = 0`, `Z = 0`. For an empty retained family every clause is about an empty product. With
`t_p` at the deadline the window `[t_p, a+T₀]` keeps length at least `h`. -/
def CoarseFamilyStatement : Prop :=
  ∀ X : TermConstruction, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ A : TermArgs X, Λ₀ ≤ A.Λ → A.Valid →
  ∀ (Kout : ℕ) (nW : ℕ+) (cr : ℝ), 0 < cr → cr ≤ 1 →
  ∀ (cP CP cH : ℝ) (cker : ℕ → ℝ), 0 < cP → 0 < cH →
  ∃ (C₀ Centry : ℝ), ∀ C : ℝ, C₀ ≤ C → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    CoarseAtM A Kout nW cr cP CP cH cker C Centry M

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The conclusion of the lifted-field statement: a lifted field of `Z` exists, and every lifted field of order `0` has a
realization of order `k₀` (same lifts, covariance image and classical representative) with a
gradient representative and the classical representative `termLiftedRep` of order `L_w + 3`. -/
def TerminalLiftRealization (Gw Gt : GenStage D ScalarH Dm b j₀) (M pT Khat NT depth sX sZ k₀ Lw : ℕ)
    (η₀ tp tf cr : ℝ) (Z : ∀ v : CompIn Gt.comps, ℝ → TorusHk Khat (ScalarH v.1.root)) : Prop :=
  (∃ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn Gw.comps) (fun v => ScalarH v.1.root))
      (PZ : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Khat - 2 * pT) (ScalarH v.1.root))
      (aRep : ℝ → Vec 2 → ∀ v : CompIn Gw.comps, ScalarH v.1.root)
      (û₀ : ∀ v : CompIn Gw.comps, ℝ → TorusHk 0 (ScalarH v.1.root)),
    IsTerminalLiftedField Gw Gt M pT Khat NT depth sX sZ η₀ tp tf cr Z CcT PZ aRep û₀) ∧
  ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn Gw.comps) (fun v => ScalarH v.1.root))
    (PZ : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Khat - 2 * pT) (ScalarH v.1.root))
    (aRep : ℝ → Vec 2 → ∀ v : CompIn Gw.comps, ScalarH v.1.root)
    (û₀ : ∀ v : CompIn Gw.comps, ℝ → TorusHk 0 (ScalarH v.1.root)),
    IsTerminalLiftedField Gw Gt M pT Khat NT depth sX sZ η₀ tp tf cr Z CcT PZ aRep û₀ →
    ∃ (û : ∀ v : CompIn Gw.comps, ℝ → TorusHk k₀ (ScalarH v.1.root))
      (ŵ : ∀ v : CompIn Gw.comps, ℝ → TorusHk (k₀ + 1) (ScalarH v.1.root)),
      IsTerminalLiftedField Gw Gt M pT Khat NT depth sX sZ η₀ tp tf cr Z CcT PZ aRep û ∧
      (∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc tp tf)),
        truncateTorusHk (Nat.le_succ k₀) (ŵ v t) = û v t) ∧
      ∀ v, ∀ t ∈ Set.Icc tp tf,
        IsClassicalRep (û v t) (fun x => termLiftedRep Gw M NT depth cr CcT aRep t x v) (Lw + 3)

/-- The conclusion of the error-energy statement: the first-cycle energy bound for every lifted field of order `k₀` with its
gradient representative (the text of `entry_terminal_error_energy` after its premises). -/
def TerminalEnergyBound (Gw Gt : GenStage D ScalarH Dm b j₀) (M pT Khat NT depth sX sZ k₀ Kw : ℕ)
    (hk₀w : k₀ ≤ Kw) (η₀ tp tf cr cK QT C : ℝ) (lawW : BirthLaw) (f : Vec 2 → ℝ)
    (V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root))
    (Vw : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
    (Z : ∀ v : CompIn Gt.comps, ℝ → TorusHk Khat (ScalarH v.1.root)) : Prop :=
  ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn Gw.comps) (fun v => ScalarH v.1.root))
    (PZ : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Khat - 2 * pT) (ScalarH v.1.root))
    (aRep : ℝ → Vec 2 → ∀ v : CompIn Gw.comps, ScalarH v.1.root)
    (û : ∀ v : CompIn Gw.comps, ℝ → TorusHk k₀ (ScalarH v.1.root))
    (ŵ : ∀ v : CompIn Gw.comps, ℝ → TorusHk (k₀ + 1) (ScalarH v.1.root)),
    IsTerminalLiftedField Gw Gt M pT Khat NT depth sX sZ η₀ tp tf cr Z CcT PZ aRep û →
    (∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc tp tf)),
      truncateTorusHk (Nat.le_succ k₀) (ŵ v t) = û v t) →
    strongEnergy (D.termRStar cK M) (D.κ M) (Gw.mass lawW) tp tf
        (fun v t => truncateTorusHk hk₀w (V v t) - û v t)
        (fun v t => truncateTorusHk (Nat.succ_le_succ hk₀w) (Vw v t) - ŵ v t) ≤
      ENNReal.ofReal (C * D.eps (M - 1) ^ (QT / 2) * Real.sqrt (l2NormSq f))

/-- The lifted-field statement at a fixed threshold level `M`. The premises are those of the lift-profile leaf of the
finite case (`TerminalUniformProfileStatement`): the weak stage, the preparation map, the
terminal law and the actual successor. The family `Z` is, on the window, the truncation of a
family `Zhi` at an order at least `K̂ + 3`, as in the cascade
(`native_liftedFieldW_exists_of_higher_retained_values`): the classical representative of the
covariance image is asked at the full order `K̂ - 2p_T`). -/
def LiftAtM {X : TermConstruction} (A : TermArgs X) (sXT sZT Kout Kw : ℕ) (nW : ℕ+)
    (kW : InvConsts) (CL Cχ cr c C Cw cH : ℝ) (j₀ M : ℕ) : Prop :=
  ∀ D : OCData, IsTermData X A.Λ M D →
  ∀ (a : ℝ) (lawW : BirthLaw) (PW : ProvParams) (Gw : GenStage D ScalarH A.Dt A.bw j₀) (aM : ℝ),
    IsWeakStage lawW PW A.φ₀ A.hφ₀ M (M + A.Jw) A.Jw A.dW A.DW nW kW a A.T₀ A.σw CL Cχ A.χw Gw aM →
  ∀ (tp : ℝ) (Pterm : (∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn Gw.comps, TorusHk (A.Khat Kout) (ScalarH v.1.root))),
    IsTerminalPrepMap M Kw (A.Khat Kout) c C Gw aM tp Pterm →
  ∀ (lawT : BirthLaw) (Gt' : GenStage D ScalarH A.Dt A.bw j₀),
    IsTerminalLaw lawW lawT cH A.η₀ A.nWords →
    IsActualSuccessor D (A.Pt D Cw cr M) (A.Mt M sXT sZT tp cr) Gw Gt' →
  ∀ (Z : ∀ v : CompIn (Gt'.retained M 1 A.RT).comps, ℝ → TorusHk (A.Khat Kout) (ScalarH v.1.root))
    (Khi : ℕ) (hKhi : A.Khat Kout + 3 ≤ Khi)
    (Zhi : ∀ v : CompIn (Gt'.retained M 1 A.RT).comps, ℝ → TorusHk Khi (ScalarH v.1.root)),
    (∀ v, ∀ t ∈ Set.Icc tp (a + A.T₀),
      Z v t = truncateTorusHk (le_trans (Nat.le_add_right _ 3) hKhi) (Zhi v t)) →
  TerminalLiftRealization Gw (Gt'.retained M 1 A.RT) M A.pT (A.Khat Kout) A.NT A.dW sXT sZT A.k₀
    A.Lw A.η₀ tp (a + A.T₀) cr Z

/-- **The lifted field.** For a family that is the truncation of a family of order `K̂ + 3`, a
lifted field exists and every lifted field of order `0` has a realization of order `k₀` (the
analogue of the first conjunct of `ComparisonClauses`). The threshold comes after `j₀` and the
constants of the weak stage, the preparation map, the successor and the law, as in the lift-profile
leaf of the finite case.

For `Z = 0` the lifted field is `0`, and for an empty weak family the realizations are the empty
products. For `L_w + 3 = k₀` the classical representative is at the top order, `Khi = K̂ + 3` is
the least internal order, and `p_T = 1` is the least covariance order (`IsTerminalSchedule` gives
`p_T ≥ 1`). -/
def LiftFieldStatement : Prop :=
  ∀ X : TermConstruction, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ A : TermArgs X, Λ₀ ≤ A.Λ → A.Valid →
  ∃ SX SZ : ℕ, ∀ sXT sZT : ℕ, SX ≤ sXT → SZ ≤ sZT →
  ∀ (Kout Kw : ℕ) (nW : ℕ+) (cr : ℝ), 0 < cr → cr ≤ 1 →
  ∀ (kW : InvConsts) (CL Cχ c C Cw cH : ℝ), 0 < c → 0 < cH → kW.G0 ≤ kW.Hprod + 1 →
  ∀ j₀ : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → LiftAtM A sXT sZT Kout Kw nW kW CL Cχ cr c C Cw cH j₀ M

/-- **The readout glue.** The energy bound for every realization, the realizations, and the
weak readout give the terminal identity and the total scalar error (the scaled Sobolev readout is
clause 3 of `IsWeakReadout`). A lemma over fixed objects.

Premises:
- the constants `C_E` and `C` are nonnegative (the route has them so);
- the window `τ < T₀` (from the statement's data);
- the reserve `L_w + 5 ≤ k₀` (the first clause of `IsTerminalSchedule`), since the readout
  bound reads the order `L_w + 5` and the energy controls the order `k₀`.

For `Z = 0` and `V = 0` both sides vanish, and the bounds are nonnegative. For empty component
families `Ww t` is linear, so `Ww t 0 = 0` and the first clause is `CsNormLe s 0 (C …) ` with
`C ≥ 0`; the nonnegativity premises exclude `C = C_E = C_id = -1`. For `C_read < 0` the norm
clause of `IsWeakReadout` makes the readout of every nonzero input impossible, so only empty
families remain, and no sign premise on `C_read` is needed. At `t = t_p` the first clause is the
one at the anchor; for `t < a + τ` only the first clause is asked. For `L_w + 3 = k₀` the readout
reads the top order of the energy. -/
def ReadoutGlueStatement : Prop :=
  ∀ {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} (Gw Gt : GenStage D ScalarH Dm b j₀) (lawW : BirthLaw)
    (M Jw Lw Kw k₀ pT Khat NT depth sX sZ : ℕ) (hk₀w : k₀ ≤ Kw)
    (κ a τ T₀ s Pw PT QT cK Cread Cid CE C tp η₀ cr : ℝ) (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ)
    (Ww : ℝ → (CompIn Gw.comps → Vec 2 → ℝ) → Vec 2 → ℝ)
    (V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root))
    (Vw : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
    (Z : ∀ v : CompIn Gt.comps, ℝ → TorusHk Khat (ScalarH v.1.root)),
    0 < D.eps M → 0 < D.eps (M - 1) → τ < T₀ → Lw + 5 ≤ k₀ → 0 ≤ CE → 0 ≤ C →
    IsWeakReadout lawW M Jw Lw Kw κ a τ T₀ s Pw cK Cread Cid f θ Gw Ww V →
    Cread * D.eps (M + Jw) ^ (-(1 + s)) * (CE * D.eps (M - 1) ^ (QT / 2)) ≤
      C * D.eps (M - 1) ^ PT →
    Cid ≤ C →
    TerminalLiftRealization Gw Gt M pT Khat NT depth sX sZ k₀ Lw η₀ tp (a + T₀) cr Z →
    TerminalEnergyBound Gw Gt M pT Khat NT depth sX sZ k₀ Kw hk₀w η₀ tp (a + T₀) cr cK QT CE lawW
      f V Vw Z →
    EntryIdentityClauses Gw Gt M pT Khat Kw Lw NT depth sX sZ η₀ tp a τ T₀ s Pw PT C cr f θ Ww V Z

/-- **Truncation to the public order.** The statement's tail at a public order gives it at
every smaller public order: the plan and the constants are kept, the preparation map and the
coarse family are truncated.

For `K_out = K_out'` this is the identity. -/
def TruncationStatement : Prop :=
  ∀ (X : TermConstruction) (A : TermArgs X), A.Valid →
    ∀ Kout Kout' : ℕ, Kout ≤ Kout' → A.tail Kout' → A.tail Kout

/-- **The reserve plan.** A plan meeting the statement's constraints above any floor, with the
seed offset above the terminal step count, the kernel moments at the statement's lower
bound `L_ker = max{L_pr, L_c, L_f}` (an upper bound is needed: the seed kernels have the orders
`n_W` and `n_T`), and the seed constants above the floors `F` of the seed side at the chosen `n_W`
(the plan chooses `n_W` and `k_S` together). The slow-length factor is `c_r = 1` (the
residual and error-energy statements are stated at `c_r = 1`).

For `K_min = 0` the floors are void. For `L₀ = L_p^T = 0`, `L_t = 0` and `n_W = 1` meets
`L_t + 1 ≤ 2n_W` once the kernel orders do. -/
def PlanStatement : Prop :=
  ∀ (X : TermConstruction) (A : TermArgs X), A.Valid → ∀ (Kmin : ℕ) (F : SeedFloors),
  ∃ (Kw Lt : ℕ) (nW : ℕ+) (_hk₀w : A.k₀ ≤ Kw) (_hLw : A.Lw + 5 ≤ Kw) (cr : ℝ) (kS : InvConsts),
    A.L0w ≤ Lt ∧ A.LpT ≤ Lt ∧ Lt + 1 ≤ 2 * (nW : ℕ) ∧
    IsTerminalKernelOrders nW A.LoT A.LfT A.LpT A.Lpr A.Lc A.Lf ∧
    0 < cr ∧ cr = 1 ∧ kS.cr = cr ∧ 0 < kS.c₀ ∧ kS.c₀ ≤ min 1 A.c₀max ∧ kS.cr ≤ 1 ∧
    kS.σf = ocDelta X.α X.q ∧ kS.lamC = A.lamE ∧
    IsSeedAllocation kS A.r0 A.Dt A.H A.J A.N A.p A.Kres A.Lpr A.Lc A.Lf ∧
    kS.Lker ≤ max A.Lpr (max A.Lc A.Lf) ∧ Kmin ≤ Kw ∧ Kmin ≤ kS.Ks ∧ Kmin ≤ kS.Kan ∧ Kmin ≤ kS.Lan ∧ Kmin ≤ kS.Jm ∧
    max 1 A.stepCount ≤ kS.G0 ∧ F.Meets nW kS ∧
    kS.mEnv = 0 ∧ kS.Kan = kS.Ks ∧ kS.Lan = kS.Ks ∧ kS.Jm = kS.Ks ∧
    Lt + A.DW + max (A.Lw + 5) A.k₀ ≤ Kw

/-- The composition deadline at a fixed threshold level `M`. -/
def DeadlineAtM {X : TermConstruction} (A : TermArgs X) (CP : ℝ) (M : ℕ) : Prop :=
  ∀ D : OCData, IsTermData X A.Λ M D →
  ∀ a aM tp : ℝ, aM ≤ a + 6 * A.Jw * ocTauPP D.α D.q D.Λ (M + 1) → tp ≤ aM + CP * D.termH M →
    tp + D.termH M + 3 * ocTau X.α X.q A.Λ (M - 1) + 4 * ocTauPP X.α X.q A.Λ (M - 1) ≤ a + A.T₀

/-- **The composition deadline**.

With `t_p = a_M + C_P h` and `a_M` at its largest, the threshold absorbs both. -/
def DeadlineStatement : Prop :=
  ∀ X : TermConstruction, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ A : TermArgs X, Λ₀ ≤ A.Λ → A.Valid →
  ∀ CP : ℝ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → DeadlineAtM A CP M

/-- The readout scale at a fixed threshold level `M`. -/
def ScaleAtM {X : TermConstruction} (A : TermArgs X) (Cread Cid CE C : ℝ) (M : ℕ) : Prop :=
  ∀ D : OCData, IsTermData X A.Λ M D →
    Cread * D.eps (M + A.Jw) ^ (-(1 + X.s)) * (CE * D.eps (M - 1) ^ (A.QT / 2)) ≤
      C * D.eps (M - 1) ^ A.PT ∧ Cid ≤ C

/-- **The readout scale.** `C_read ε_{M+J_w}^{-(1+s)} C_E E^{Q_T/2} ≤ C E^{P_T}` and
`C_id ≤ C` for every large `C`, past a threshold (`Q_T/2 > P_T + q^{J_w+1}(1+s) + 2`, schedule;
`ε_{M+J_w} ≥ cE^{q^{J_w+1}}`).

For `C_read = 0` the first inequality is `0 ≤ C E^{P_T}`. -/
def ReadoutScaleStatement : Prop :=
  ∀ X : TermConstruction, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ A : TermArgs X, Λ₀ ≤ A.Λ → A.Valid →
  ∀ (Cread Cid CE : ℝ), ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    ScaleAtM A Cread Cid CE C M

/-- **Positivity of the scales** (no threshold).

For `k = 0` these are the first wavelength and the first renewal period. -/
def ScaleFactsStatement : Prop :=
  ∀ (X : TermConstruction) (Λ : ℕ), 128 ≤ Λ →
    (∀ k, 0 ≤ ocA X.α X.q Λ k) ∧ (∀ k, 0 ≤ ocTauPP X.α X.q Λ k) ∧
    ∀ D : OCData, D.q = X.q → D.Λ = Λ → ∀ k, 0 < D.eps k

/-- **Monotonicity of the preparation clauses in their constant** (given nonnegative scales).

For `C = C'` this is the identity, and for `f = 0` every bound is `≤ 0` on both sides. -/
def PrepMonotoneStatement : Prop :=
  ∀ {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} (M Kw Kh k₀ : ℕ) (hk₀w : k₀ ≤ Kw) (hk₀o : k₀ ≤ Kh)
    (c C C' cr cK QT aM tp : ℝ) (law : BirthLaw) (f : Vec 2 → ℝ) (Gw : GenStage D ScalarH Dm b j₀)
    (Pterm : (∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn Gw.comps, TorusHk Kh (ScalarH v.1.root)))
    (V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root)),
    0 ≤ D.termH M → 0 < D.eps (M - 1) → C ≤ C' →
    (IsTerminalPrepMap M Kw Kh c C Gw aM tp Pterm → IsTerminalPrepMap M Kw Kh c C' Gw aM tp Pterm) ∧
    (IsTerminalPrepBounds law M Kw Kh k₀ hk₀w hk₀o cr cK C QT f Gw aM tp Pterm V →
      IsTerminalPrepBounds law M Kw Kh k₀ hk₀w hk₀o cr cK C' QT f Gw aM tp Pterm V)

/-- The componentwise truncation of a family from the order `K₃` to `K`. -/
def famTrunc {S : Finset Comp} {K K₃ : ℕ} (h : K ≤ K₃) :
    (∀ v : CompIn S, TorusHk K₃ (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn S, TorusHk K (ScalarH v.1.root)) :=
  LinearMap.pi fun v => (truncateTorusHk h).toLinearMap ∘ₗ LinearMap.proj v

/-- **Truncation of the preparation clauses.** The map and the bounds at an internal
order `K₃` give them at every smaller order `K ≥ k₀` for the truncated map (nonnegative masses, as
in `TerminalPrepTruncationStatement`, from which it is derived).

For `K = K₃` the truncation is the identity, and for `k₀ = K` the third bound is at the top
order. -/
def PrepTruncStatement : Prop :=
  ∀ {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} (M Kw K K₃ k₀ : ℕ) (hKK : K ≤ K₃) (hk₀w : k₀ ≤ Kw)
    (hk₀o : k₀ ≤ K) (c C cr cK QT aM tp : ℝ) (law : BirthLaw) (f : Vec 2 → ℝ)
    (Gw : GenStage D ScalarH Dm b j₀) (_hmass : ∀ v, 0 ≤ Gw.mass law v)
    (P₃ : (∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn Gw.comps, TorusHk K₃ (ScalarH v.1.root)))
    (V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root)),
    (IsTerminalPrepMap M Kw K₃ c C Gw aM tp P₃ →
      IsTerminalPrepMap M Kw K c C Gw aM tp (famTrunc hKK ∘ₗ P₃)) ∧
    (IsTerminalPrepBounds law M Kw K₃ k₀ hk₀w (hk₀o.trans hKK) cr cK C QT f Gw aM tp P₃ V →
      IsTerminalPrepBounds law M Kw K k₀ hk₀w hk₀o cr cK C QT f Gw aM tp
        (famTrunc hKK ∘ₗ P₃) V)

/-- **Truncation of the coarse-family clauses.** The clauses at `K₃` for the trace `g₃` and
the family `Z₃` give them at `K` for the truncated trace and family (same constants; nonnegative
weak masses, as in `TerminalFamilyTruncationStatement`, from which it is derived).

For `K = K₃` the truncation is the identity; for `g₃ = 0`, `Z₃ = 0` and both sides are about
zero. -/
def FamilyTruncStatement : Prop :=
  ∀ {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} (Pt : ProvParams) (seedKt freshKt : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (lawW lawT : BirthLaw) (rootM : ℕ → ℝ)
    (M K K₃ : ℕ) (hKK : K ≤ K₃) (cr C Centry tp sn tf : ℝ) (f : Vec 2 → ℝ)
    (Gw Gt : GenStage D ScalarH Dm b j₀) (_hmass : ∀ v, 0 ≤ Gw.mass lawW v) {Ds : ℕ}
    (seed : GenStage D ScalarH Ds b j₀) (ι : CompIn Gt.comps ≃ CompIn seed.comps)
    (g₃ : ∀ v : CompIn Gw.comps, TorusHk K₃ (ScalarH v.1.root))
    (Z₃ : ∀ v : CompIn Gt.comps, ℝ → TorusHk K₃ (ScalarH v.1.root)),
    TerminalFamilyClauses Pt seedKt freshKt φ₀ hφ₀ lawW lawT rootM M K₃ cr C Centry tp sn tf f Gw
      Gt seed ι g₃ Z₃ →
    TerminalFamilyClauses Pt seedKt freshKt φ₀ hφ₀ lawW lawT rootM M K cr C Centry tp sn tf f Gw
      Gt seed ι (famTrunc hKK g₃) (fun v t => truncateTorusHk hKK (Z₃ v t))

/-- **Monotonicity of the retained certificate in the order.**

For `K = K₃` the truncation is the identity, and for `K = 0` only order-zero coefficient bounds
remain. -/
def RetainedTruncStatement : Prop :=
  ∀ {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} (lawT : BirthLaw) (Pt : ProvParams)
    (seedKt freshKt : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (cker : ℕ → ℝ)
    (M K K₃ : ℕ), K ≤ K₃ → ∀ (cr tp tf : ℝ) (Gt : GenStage D ScalarH Dm b j₀),
    TerminalRetainedClauses lawT Pt seedKt freshKt φ₀ hφ₀ cker M K₃ cr tp tf Gt →
    TerminalRetainedClauses lawT Pt seedKt freshKt φ₀ hφ₀ cker M K cr tp tf Gt

/-- **Truncation of the internal order**: the route builds the
preparation, the seed certificate and the coarse family at `K̂₃ = K̂ + 3` and states the statement at
`K̂`. Routine; shared with the truncation to the public order. -/
def TruncationPartsStatement : Prop :=
  PrepTruncStatement ∧ FamilyTruncStatement ∧ RetainedTruncStatement
end

end AVRegularity.EntryTerminal.Route
end
end
end
