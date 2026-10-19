-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Assembly.Route.Ingredients
import AVRegularity.Construction.Preservation.Buffer.KernelFluxTruncation
public import AVRegularity.EntryTerminal.Assembly.EntryTerminalOfIngredients
import Mathlib.Data.Int.Star

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.EntryTerminal.Route

/-! The capped preparation and the error-energy statements restated over the bundled data of `Route/Tail` (mechanical renaming
of the prefix variables to the fields of `X : TermConstruction` and `A : TermArgs X`), with the
bridges from the text copies. The bridges keep the large instantiations of the two statements out
of the assembly, which then stays within the default elaboration budget. -/

/-- The capped preparation at a fixed threshold level `M` (from the data onwards). -/
def PrepAtM {X : TermConstruction} (A : TermArgs X) (Kout : ℕ) (Kw : ℕ) (Lt : ℕ) (nW : ℕ+) (hk₀w : A.k₀ ≤ Kw) (cr : ℝ) (cK : ℝ) (CK : ℝ) (CL : ℝ) (Cχ : ℝ) (kW : InvConsts) (c : ℝ) (C : ℝ) (j₀ : ℕ) (M : ℕ) : Prop :=
  ∀ (D : OCData), D.α = X.α → D.q = X.q → D.Λ = A.Λ → D.ζ = X.ζ → IsOCStreamSeq X.α X.q A.Λ X.ζ D.Φ →
    IsOCBandChain X.α X.q A.Λ X.ζ M D.κ → D.term = M →
  ∀ (a : ℝ) (lawW : BirthLaw) (PW : ProvParams)
    (Gw : GenStage D ScalarH (termD0bar A.NT A.pT A.DW A.dW) A.bw j₀) (aM : ℝ)
    (Ww : ℝ → (CompIn Gw.comps → Vec 2 → ℝ) → Vec 2 → ℝ),
    IsWeakStage lawW PW A.φ₀ A.hφ₀ M (M + A.Jw) A.Jw A.dW A.DW nW kW a A.T₀ A.σw CL Cχ A.χw Gw aM →
  ∃ (tp : ℝ) (Pterm : (∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn Gw.comps, TorusHk (max Kout (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) (ScalarH v.1.root))),
    IsTerminalPrepMap M Kw (max Kout (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) c C Gw aM tp Pterm ∧
    ∀ (f : Vec 2 → ℝ)
      (U₀ : ∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root))
      (U V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root))
      (Uw Vw : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
      (Uk Vk : ∀ v u (_ : Gw.fam.Γ v u), ℝ → TorusHk (Kw + (termD0bar A.NT A.pT A.DW A.dW) - 1) (ScalarH u.1.root)),
      IsWeakPaired PW A.φ₀ A.hφ₀ lawW M Kw Lt nW a A.T₀ A.σw A.χw cK CK f Gw aM U₀ U V Uw Vw Uk Vk →
      IsTerminalPrepBounds lawW M Kw (max Kout (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) A.k₀ hk₀w (le_trans (by omega : A.k₀ ≤ 2 * A.k₀ + 2) (le_trans (le_max_left _ _) (le_max_right Kout _))) cr cK C A.QT f Gw aM tp Pterm V

/-- The error-energy statement at a fixed threshold level `M` (from the data onwards). -/
def EnergyAtM {X : TermConstruction} (A : TermArgs X) (Kout : ℕ) (sXT : ℕ) (sZT : ℕ) (Kw : ℕ) (Lt : ℕ) (nW : ℕ+) (hk₀w : A.k₀ ≤ Kw) (cr : ℝ) (kS : InvConsts) (cK : ℝ) (CK : ℝ) (CL : ℝ) (Cχ : ℝ) (Cread : ℝ) (Cid : ℝ) (kW : InvConsts) (cP : ℝ) (CP : ℝ) (cHP : ℝ) (C : ℝ) (Ce : ℝ) (Cw : ℝ) (cker : ℕ → ℝ) (j₀ : ℕ) (M : ℕ) : Prop :=
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
      strongEnergy (D.termRStar cK M) (D.κ M) (Gw.mass lawW) tp (a + A.T₀)
          (fun v t => truncateTorusHk hk₀w (V v t) - û v t)
          (fun v t => truncateTorusHk (Nat.succ_le_succ hk₀w) (Vw v t) - ŵ v t) ≤
        ENNReal.ofReal (C * D.eps (M - 1) ^ (A.QT / 2) * Real.sqrt (l2NormSq f))

/-- The capped preparation over the bundled data. -/
def PreparationBundled : Prop :=
  ∀ X : TermConstruction, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ A : TermArgs X, Λ₀ ≤ A.Λ → A.Valid →
    ∀ Kout : ℕ,
    ∃ Kneed : ℕ,
    ∀ (Kw Lt : ℕ) (nW : ℕ+) (hk₀w : A.k₀ ≤ Kw) (cr : ℝ), Kneed ≤ Kw →
      A.LpT ≤ Lt → Lt + 1 ≤ 2 * (nW : ℕ) →
      0 < cr → cr ≤ 1 →
    ∀ (cK CK CL Cχ : ℝ) (kW : InvConsts), 0 < cK → kW.c₀ = cK →
      Kneed ≤ kW.Ks → Kneed ≤ kW.Kan → Kneed ≤ kW.Lan → Kneed ≤ kW.Jm → Lt ≤ kW.Lker →
    ∃ (c C : ℝ), 0 < c ∧
    ∀ j₀ : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    PrepAtM A Kout Kw Lt nW hk₀w cr cK CK CL Cχ kW c C j₀ M

/-- The error-energy statement over the bundled data. -/
def ErrorEnergyBundled : Prop :=
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
    ∃ C : ℝ,
    ∃ (CHt Υt : ℝ), 1 ≤ CHt ∧ 0 < Υt ∧
    ∀ j₀ : ℕ, IsCarrierStart X.α X.q A.Λ A.bw CHt Υt j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    EnergyAtM A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP C Ce Cw cker j₀ M

theorem preparationBundled_of (h : PreparationStatement) : PreparationBundled := by
  intro X
  obtain ⟨Λ₀, h128, h'⟩ := h X.α X.s X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.q X.hq X.ζ X.hζ
  refine ⟨Λ₀, h128, fun A hΛ hA => ?_⟩
  obtain ⟨hA0, ⟨hφs, hφn, hφm, hφsupp⟩, ⟨hbw0, hbw1⟩,
    ⟨hJw, hτ, hτT, hPw, hσw0, hσw1, hχw, hη0, hη1⟩, hPT, hsched, -, -⟩ := hA
  exact h' A.Λ hΛ A.c₀max hA0 A.φ₀ A.hφ₀ hφs hφn hφm hφsupp A.bw hbw0 hbw1 A.Jw A.Lw A.dW A.DW
    A.τ A.T₀ A.Pw A.σw A.χw A.η₀ hJw hτ hτT hPw hσw0 hσw1 hχw hη0 hη1 A.PT hPT A.NT A.pT A.RT
    A.AT A.k₀ A.LcT A.LoT A.LfT A.LpT A.tT A.QT hsched

theorem errorEnergyBundled_of (h : ErrorEnergyStatement) : ErrorEnergyBundled := by
  intro X
  obtain ⟨Λ₀, h128, h'⟩ := h X.α X.s X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.q X.hq X.ζ X.hζ
  refine ⟨Λ₀, h128, fun A hΛ hA => ?_⟩
  obtain ⟨hA0, ⟨hφs, hφn, hφm, hφsupp⟩, ⟨hbw0, hbw1⟩,
    ⟨hJw, hτ, hτT, hPw, hσw0, hσw1, hχw, hη0, hη1⟩, hPT, hsched, hexp, hfresh, hDW⟩ := hA
  exact h' A.Λ hΛ A.c₀max hA0 A.φ₀ A.hφ₀ hφs hφn hφm hφsupp A.bw hbw0 hbw1 A.Jw A.Lw A.dW A.DW
    A.L0w A.τ A.T₀ A.Pw A.σw A.χw A.η₀ hJw hDW hτ hτT hPw hσw0 hσw1 hχw hη0 hη1 A.PT hPT A.NT A.pT A.RT
    A.AT A.k₀ A.LcT A.LoT A.LfT A.LpT A.tT A.QT hsched A.τe A.lamE hexp A.σ₀ A.H A.J A.N A.p
    A.Kres A.Lpr A.Lc A.Lf A.nT hfresh

/-! **The parts of the error energy** (`entry_terminal_error_energy`; Proposition 14.10(c) of the
paper follows from it). With the terminal residual (`entry_terminal_residual`, the error equation
with its residual presentation and the bill), the whole-window error energy follows from three
parts:

* **Forced energy** (`TerminalForcedEnergyStatement`): a regularized solution of the weak stage
  with forcing `(F, g)` at the reserve `k₀` has strong energy at the capped radius `r_* = c_K x` at
  most `C_a (‖e(t_p)‖_{r_*,k₀;π} + X)`, where `X ≥ 0` bounds the residual norms of every word of
  order `≤ k₀` at `r_*`. This is the error form of the coupled energy estimate, with the
  source-on-error terms on the left.
* **Quiet entrance** (`TerminalQuietEntranceStatement`): at an anchor `t_p` with the quiet
  quiet margin of half-width `τ'_M`, the lifted field at `t_p` differs from the trace `g` by at most
  `C_b E^Q` times the `(ρ, K̂)` norm of `g`, for every `Q` (by the quiet decay
  `C_poly(E⁻¹) exp(-c τ'_M/ℓ²)`).
* **Bill scale** (`TermBillScaleStatement`): `termBill ≤ C_d E^{Q_T + 2}`.

The initial discrepancy `e(t_p) = [V(t_p) - g] - (û(t_p) - g)` is one triangle inequality with
bound 3 of `IsTerminalPrepBounds` and the quiet entrance. It is part of the assembly.

The forced energy and the quiet entrance take the reserve premise `kW.G0 ≤ kW.Hprod + 1` (the weak stage's
components are roots, so it is `0 ≤ compReserve kW`; the weak kernel operator's finiteness and the
terminal lift need it).

With zero forcing and zero initial value the energy is zero (forced energy). For `g = 0` the lifted
field vanishes at `t_p` (quiet entrance). For `t_p = t_f`, `Z_cl = 0` and `B_p = 1` in the bill
(bill scale). -/

/-- **Forced energy on the weak stage.** For the weak stage at level `M`, any regularized
solution at the reserve `k₀` on `[t_p, a + T₀]` with measurable forcing `(F, g)` whose residual
norms at `r_*` are at most `X ≥ 0` has strong energy at most `C_a (‖e₀‖ + X)`. The constant comes
after the weak constants and before `j₀`. -/
def TerminalForcedEnergyStatement : Prop :=
  ∀ X : TermConstruction, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ A : TermArgs X, Λ₀ ≤ A.Λ → A.Valid →
  ∀ (nW : ℕ+) (cK CL Cχ : ℝ) (kW : InvConsts), 0 < cK → kW.c₀ = cK → A.k₀ ≤ kW.Ks →
    kW.G0 ≤ kW.Hprod + 1 →
  ∃ Ca : ℝ, 0 ≤ Ca ∧ ∀ j₀ : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ D : OCData, IsTermData X A.Λ M D →
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
      ENNReal.ofReal (Ca * (weightedNorm (D.termRStar cK M) (Gw.mass lawW) (fun _ => 1) e₀ + Xr))

/-- **Quiet entrance of the terminal lift at `t_p`.** At an anchor with the quiet margin of
half-width `τ'_M`, whose lower half lies in the weak window (`aM + τ'_M ≤ t_p`: the stage
invariant's fast independence holds on `ocTrimmedQuietTimes ∩ [aM, a + T₀]`), the lifted field of
a terminal trace differs from the trace at `t_p` by at most `C_b E^Q` times the trace's `(ρ, K̂)`
norm, for every `Q`. The route supplies `aM + τ'_M ≤ t_p` from the preparation's
`aM + c·τ''_M ≤ t_p` for `M` large (`τ'_M = τ''_M / L_M`, `L_M ≥ 4ε_{M-1}^{-δ} → ∞`). -/
def TerminalQuietEntranceStatement : Prop :=
  ∀ X : TermConstruction, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ A : TermArgs X, Λ₀ ≤ A.Λ → A.Valid →
  ∃ (SX SZ Kfloor : ℕ), ∀ sXT sZT : ℕ, SX ≤ sXT → SZ ≤ sZT → ∀ Kout : ℕ, Kfloor ≤ Kout →
  ∀ (nW : ℕ+) (cr cK CL Cχ : ℝ) (kW : InvConsts), 0 < cr → cr ≤ 1 → 0 < cK → kW.c₀ = cK →
    A.k₀ ≤ kW.Ks → kW.G0 ≤ kW.Hprod + 1 →
  ∀ Q : ℝ, ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ j₀ : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
  ∀ D : OCData, IsTermData X A.Λ M D →
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
      Cb * D.eps (M - 1) ^ Q * weightedNorm (D.termRho cr M) (Gw.mass lawW) (fun _ => 1) g

/-- **The bill scale.** The terminal bill is at most `C_d E^{Q_T + 2}` on windows of length
at most `T₀`, for every large level. -/
def TermBillScaleStatement : Prop :=
  ∀ X : TermConstruction, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ A : TermArgs X, Λ₀ ≤ A.Λ → A.Valid →
  ∀ (cr cgap Cg : ℝ), 0 < cr → cr ≤ 1 → 0 < cgap →
  ∃ Cd : ℝ, 0 ≤ Cd ∧ ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ D : OCData, IsTermData X A.Λ M D →
  ∀ tp tf : ℝ, tf - tp ≤ A.T₀ →
    termBill D M A.NT A.pT A.RT A.AT A.LcT A.LoT A.LfT (termAlphabet A.NT A.pT A.DW A.dW)
        cr A.σw A.χw A.η₀ A.tT cgap Cg tp tf ≤ Cd * D.eps (M - 1) ^ (A.QT + 2)

/-! # The error-energy statement from the bundled route: the split statements

`E9Tail α … nT`: the tail of the error-energy statement (`entry_terminal_error_energy`, text copy
`ErrorEnergyStatement`) after `IsFreshKernelOrder … →`, with every variable explicit.
`E9Copy`: the error-energy statement with that tail named; definitionally `ErrorEnergyStatement`
(`e9_of_copy`). `E9BundledTail X A`: the tail of `ErrorEnergyBundled` after `A.Valid →`.
The unbundling (below) then compares two applications of `E9Tail` argument by argument instead of
the two expanded tails (a single final `exact` over the expanded tails exceeds the default
elaboration budget). The texts are those of `ErrorEnergyStatement` and `ErrorEnergyBundled`,
verbatim. -/

/-- The tail of the error-energy statement after `IsFreshKernelOrder … →`, every variable explicit. -/
def E9Tail (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (_c₀max : ℝ) (φ₀ : Vec 2 → ℝ)
    (hφ₀ : Integrable φ₀) (bw : ℝ) (Jw Lw dW DW L0w : ℕ) (τ T₀ Pw σw χw η₀ _PT : ℝ)
    (NT pT RT _AT k₀ _LcT LoT LfT LpT : ℕ) (tT QT τe _lamE _σ₀ : ℝ) (H _J N p _Kres Lpr Lc Lf : ℕ)
    (nT : ℕ+) : Prop :=
    ∃ (SX SZ Kfloor : ℕ),
    ∀ sXT sZT : ℕ, SX ≤ sXT → SZ ≤ sZT →
    ∀ Kout : ℕ, Kfloor ≤ Kout →
    ∃ Kneed : ℕ,
    ∀ (Kw Lt : ℕ) (nW : ℕ+) (hk₀w : k₀ ≤ Kw) (hLw : Lw + 5 ≤ Kw) (cr : ℝ) (kS : InvConsts),
      Kneed ≤ Kw →
      L0w ≤ Lt → LpT ≤ Lt → Lt + 1 ≤ 2 * (nW : ℕ) → IsTerminalKernelOrders nW LoT LfT LpT Lpr Lc Lf
          →
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
        (∀ v : CompIn Gw.comps, TorusHk (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2)))
            (ScalarH v.1.root)))
      (lawT : BirthLaw) (Gt' : GenStage D ScalarH (termD0bar NT pT DW dW) bw j₀),
      IsTerminalPrepMap M Kw (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) cP CP Gw aM tp
          Pterm →
      IsTerminalLaw lawW lawT cHP η₀ (wordsUpTo (termAlphabet NT pT DW dW) RT).card →
      IsActualSuccessor D (termProvParams D Cw cr tT η₀ NT pT M)
        (termMenu (M + Jw) (termAlphabet NT pT DW dW) RT NT pT sXT sZT η₀ tp cr) Gw Gt' →
      TerminalSeedCertificate (termProvParams D Cw cr tT η₀ NT pT M) lawT
        (fun _ => isoPairedKernel (D.termRW σw M) nW)
            (fun _ => isoPairedKernel (D.termRNew cr tT M) nT)
        φ₀ hφ₀ cker (M + Jw) (M - 1) M (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) kS Ce
            τe (termR0bar RT dW) (termD0bar NT pT DW dW)
        (succSchedD (termD0bar NT pT DW dW) N p (H + 1)) cr tp (tp + D.termH M) (a + T₀)
        (Gt'.retained M 1 RT) →
      ∀ (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ)
        (U₀ : ∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root))
        (U V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root))
        (Uw Vw : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
        (Uk Vk : ∀ v u (_ : Gw.fam.Γ v u), ℝ → TorusHk (Kw + (termD0bar NT pT DW dW) - 1)
            (ScalarH u.1.root)),
        IsWeakPaired PW φ₀ hφ₀ lawW M Kw Lt nW a T₀ σw χw cK CK f Gw aM U₀ U V Uw Vw Uk Vk →
        IsWeakReadout lawW M Jw Lw Kw (D.κ M) a τ T₀ s Pw cK Cread Cid f θ Gw Ww V →
        IsTerminalPrepBounds lawW M Kw (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) k₀ hk₀w
            (le_trans (by omega : k₀ ≤ 2 * k₀ + 2)
            (le_trans (le_max_left _ _) (le_max_right Kout _))) cr cK CP QT f Gw aM tp Pterm V →
      ∀ (Z₀ : ∀ v : CompIn (Gt'.retained M 1 RT).comps, TorusHk
          (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) (ScalarH v.1.root))
        (Z : ∀ v : CompIn (Gt'.retained M 1 RT).comps, ℝ → TorusHk
            (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) (ScalarH v.1.root))
        (Zw : ∀ v : CompIn (Gt'.retained M 1 RT).comps, ℝ → TorusHk
            ((max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) + 1) (ScalarH v.1.root))
        (Zk : ∀ v u (_ : (Gt'.retained M 1 RT).fam.Γ v u), ℝ → TorusHk
            ((max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) + (termD0bar NT pT DW dW) - 1)
            (ScalarH u.1.root)),
        IsTerminalTrace Gw (Gt'.retained M 1 RT) (Pterm fun v => V v aM) Z₀ →
        (Gt'.retained M 1 RT).IsRegSolution (termProvParams D Cw cr tT η₀ NT pT M)
          (fun _ => isoPairedKernel (D.termRW σw M) nW)
              (fun _ => isoPairedKernel (D.termRNew cr tT M) nT) φ₀ hφ₀
          (D.termB M) (streamVel (D.Φ (M - 1)))
              (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) tp (a + T₀) Z₀ (fun _ _ => 0)
              (fun _ _ => 0)
          Z Zw Zk →
      ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn Gw.comps) (fun v => ScalarH v.1.root))
        (PZ : ∀ v : CompIn Gw.comps, ℝ → TorusHk
            ((max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) - 2 * pT) (ScalarH v.1.root))
        (aRep : ℝ → Vec 2 → ∀ v : CompIn Gw.comps, ScalarH v.1.root)
        (û : ∀ v : CompIn Gw.comps, ℝ → TorusHk k₀ (ScalarH v.1.root))
        (ŵ : ∀ v : CompIn Gw.comps, ℝ → TorusHk (k₀ + 1) (ScalarH v.1.root)),
        IsTerminalLiftedField Gw (Gt'.retained M 1 RT) M pT
            (max Kout (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2))) NT dW sXT sZT η₀ tp (a + T₀) cr Z
            CcT PZ aRep û →
        (∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc tp (a + T₀))),
          truncateTorusHk (Nat.le_succ k₀) (ŵ v t) = û v t) →
        strongEnergy (D.termRStar cK M) (D.κ M) (Gw.mass lawW) tp (a + T₀)
            (fun v t => truncateTorusHk hk₀w (V v t) - û v t)
            (fun v t => truncateTorusHk (Nat.succ_le_succ hk₀w) (Vw v t) - ŵ v t) ≤
          ENNReal.ofReal (C * D.eps (M - 1) ^ (QT / 2) * Real.sqrt (l2NormSq f))

/-- The error-energy statement with its tail named. -/
def E9Copy : Prop :=
  ∀ (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ)
      (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ),
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
    E9Tail α s q ζ Λ c₀max φ₀ hφ₀ bw Jw Lw dW DW L0w τ T₀ Pw σw χw η₀ PT NT pT RT AT k₀ LcT LoT
        LfT LpT tT QT τe lamE σ₀ H J N p Kres Lpr Lc Lf nT

/-- The tail of `ErrorEnergyBundled` after `A.Valid →`. -/
def E9BundledTail {X : TermConstruction} (A : TermArgs X) : Prop :=
    ∃ (SX SZ Kfloor : ℕ),
    ∀ sXT sZT : ℕ, SX ≤ sXT → SZ ≤ sZT →
    ∀ Kout : ℕ, Kfloor ≤ Kout →
    ∃ Kneed : ℕ,
    ∀ (Kw Lt : ℕ) (nW : ℕ+) (hk₀w : A.k₀ ≤ Kw) (_hLw : A.Lw + 5 ≤ Kw) (cr : ℝ) (kS : InvConsts),
      Kneed ≤ Kw →
      A.L0w ≤ Lt → A.LpT ≤ Lt → Lt + 1 ≤ 2 * (nW : ℕ) → IsTerminalKernelOrders nW A.LoT A.LfT A.LpT
          A.Lpr A.Lc A.Lf →
      0 < cr → cr ≤ 1 → cr = 1 → kS.cr = cr → 0 < kS.c₀ →
      Kneed ≤ kS.Ks → Kneed ≤ kS.Kan → Kneed ≤ kS.Lan → Kneed ≤ kS.Jm →
    ∀ (cK CK CL Cχ Cread Cid : ℝ) (kW : InvConsts), 0 < cK → kW.c₀ = cK →
      IsWeakAllocation kW kS Lt → kW.G0 ≤ kW.Hprod →
      A.NT + A.DW + A.dW * (A.Dt + 1) ≤ kW.Lstar →
    ∀ (cP CP cHP : ℝ), 0 < cP → cHP ≤ 1 → ∃ Cw₀ : ℝ, ∀ (Cw Ce : ℝ) (cker : ℕ → ℝ), Cw₀ ≤ Cw →
    ∃ C : ℝ,
    ∃ (CHt Υt : ℝ), 1 ≤ CHt ∧ 0 < Υt ∧
    ∀ j₀ : ℕ, IsCarrierStart X.α X.q A.Λ A.bw CHt Υt j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    EnergyAtM A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP C Ce Cw cker j₀
        M

/-- The copy is the error-energy statement. -/
theorem e9_of_copy (h : E9Copy) : ErrorEnergyStatement := h

end AVRegularity.EntryTerminal.Route
end

section
namespace AVRegularity.EntryTerminal.Route

/-! # The error-energy statement from the bundled route: the unbundling

`errorEnergyStatement_of_bundled : ErrorEnergyBundled → ErrorEnergyStatement`, the converse of
`errorEnergyBundled_of`. Split into steps, each its own declaration:
* `e9BundledTail`: `ErrorEnergyBundled` with its tail named (`E9BundledTail`);
* `e9Tail_of_bundledTail`: the bundled tail at `A` is `E9Tail` at the projections of `A`
  (forward style, as `errorEnergyBundled_of`);
* `e9Copy_of_bundled`: the prefix of the error-energy statement builds `X : TermConstruction`, `A : TermArgs X` and
  `A.Valid`; the final step compares `E9Tail` at the projections of the constructed `X`, `A`
  with `E9Tail` at the variables, argument by argument;
* `errorEnergyStatement_of_bundled`: through `e9_of_copy`.
The value `D_W = 1 + J_w N_w` satisfies the premise `1 ≤ D_W`, which `A.Valid` carries last, and
`D_W = 0` is excluded by it; the least floors (`K_out = K_floor`, `s_X = SX`) pass unchanged,
since the tail is the same proposition. -/

/-- `ErrorEnergyBundled` with its tail named. -/
theorem e9BundledTail (h : ErrorEnergyBundled) (X : TermConstruction) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ A : TermArgs X, Λ₀ ≤ A.Λ → A.Valid → E9BundledTail A :=
  h X

/-- The bundled tail at `A` is the tail of the error-energy statement at the projections of `A`. -/
theorem e9Tail_of_bundledTail {X : TermConstruction} (A : TermArgs X)
    (h : E9BundledTail A) :
    E9Tail X.α X.s X.q X.ζ A.Λ A.c₀max A.φ₀ A.hφ₀ A.bw A.Jw A.Lw A.dW A.DW A.L0w A.τ A.T₀
      A.Pw A.σw A.χw A.η₀ A.PT A.NT A.pT A.RT A.AT A.k₀ A.LcT A.LoT A.LfT A.LpT A.tT A.QT A.τe
      A.lamE A.σ₀ A.H A.J A.N A.p A.Kres A.Lpr A.Lc A.Lf A.nT :=
  h

/-- **The error-energy statement with its tail named, from the bundled route.** -/
theorem e9Copy_of_bundled (h : ErrorEnergyBundled) : E9Copy := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λ₀, h128, h'⟩ := e9BundledTail h ⟨α, s, q, ζ, hα₀, hα₁, hs₀, hs₁, hq, hζ⟩
  refine ⟨Λ₀, h128, ?_⟩
  intro Λ hΛ c₀max hc0 φ₀ hφ₀ hφs hφn hφm hφsupp bw hbw0 hbw1 Jw Lw dW DW L0w τ T₀ Pw σw χw η₀
    hJw hDW hτ hτT hPw hσw0 hσw1 hχw hη0 hη1 PT hPT NT pT RT AT k₀ LcT LoT LfT LpT tT QT hsched
    τe lamE hexp σ₀ H J N p Kres Lpr Lc Lf nT hfresh
  have hT := e9Tail_of_bundledTail
    ⟨Λ, c₀max, φ₀, hφ₀, bw, Jw, Lw, dW, DW, L0w, τ, T₀, Pw, σw, χw, η₀, PT, NT, pT, RT, AT, k₀,
      LcT, LoT, LfT, LpT, tT, QT, τe, lamE, σ₀, H, J, N, p, Kres, Lpr, Lc, Lf, nT⟩
    (h' _ hΛ ⟨hc0, ⟨hφs, hφn, hφm, hφsupp⟩, ⟨hbw0, hbw1⟩,
      ⟨hJw, hτ, hτT, hPw, hσw0, hσw1, hχw, hη0, hη1⟩, hPT, hsched, hexp, hfresh, hDW⟩)
  exact hT

/-- **The error-energy statement from the bundled route.** -/
theorem errorEnergyStatement_of_bundled (h : ErrorEnergyBundled) : ErrorEnergyStatement :=
  e9_of_copy (e9Copy_of_bundled h)

end AVRegularity.EntryTerminal.Route
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.EntryTerminal.Route

/-! **The top-level assembly of `entry_terminal_of_weak`.** The statement's tail at every
public order, from the named ingredients: the capped preparation (`PreparationStatement`), the
error energy (`ErrorEnergyStatement`), and the route ingredients (successor, seed encoding, seed
clauses, coarse family, lifted field, readout glue, truncation, plan). The terminal
residual enters only through the error energy.

The proof is layered like the statements (`BTail`, `BTailConsts`, `BTailAtM` and the per-level
residuals `PrepAtM`, …): `route_tail` chooses the lift floors, the plan and the constants of the
preparation, successor, seed clauses, lifted field and error energy; `route_consts` the remaining
constants, the carrier start and the threshold; `route_atM` the objects at one level. Each stays
within the default elaboration budget.

The tail is proved at the public order `max K_out K_floor` (`K_floor` from the error energy) and
truncated by the truncation ingredient. The choices follow the statement's order: lift floors
(maximum over the successor, seed clauses, lifted field and error energy), the plan (above the
reserve floors of the preparation and error energy and the seed floor of the seed clauses), the
weak constants, the constants (`c, C_P` from the preparation; `c_H, C_e, C_w, c_ker` from the seed
clauses; `C_entry` from the coarse family; the common `C = max(C_P, C₆, C₁₀)`), the carrier start
(maximum over the successor, seed clauses and error energy, by `IsCarrierStart.mono`), the
threshold (maximum over all), and the objects (`t_p, 𝐏` from the preparation, the law by
construction, `G_t'` from the successor, the seed from the seed encoding, its clauses from the seed
clauses, the family from the coarse family, the realizations from the lifted field, the energy from
the error energy, the identity from the readout glue). -/

local instance routeAsmTorusNormed {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedAddCommGroup (TorusHk K E) := inferInstance
local instance routeAsmTorusInner {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    InnerProductSpace ℝ (TorusHk K E) := inferInstance
local instance routeAsmTorusSpace {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedSpace ℝ (TorusHk K E) := inferInstance

/-- The seed index dominates the stage index. -/
theorem le_succSchedD (D₀ N p : ℕ) : ∀ g, D₀ ≤ succSchedD D₀ N p g
  | 0 => le_rfl
  | g + 1 => (le_succSchedD D₀ N p g).trans (by simp only [succSchedD]; omega)

/-- The left argument of a maximum below a bound. -/
theorem m2l {a b c : ℕ} (h : max a b ≤ c) : a ≤ c := le_trans (le_max_left _ _) h

/-- The right argument of a maximum below a bound. -/
theorem m2r {a b c : ℕ} (h : max a b ≤ c) : b ≤ c := le_trans (le_max_right _ _) h

/-- The slot `k₀` is below the internal order. -/
theorem k0_le_khat (K k₀ NT pT : ℕ) : k₀ ≤ max K (max (2 * k₀ + 2) (NT + 2 * pT + k₀ + 2)) := by
  omega

/-- The terminal law: the weak roots, one mass per word, no marker. -/
def termLaw (lawW : BirthLaw) (cH η₀ : ℝ) (hcH : 0 < cH) (nWords : ℕ) : BirthLaw where
  cH := cH
  cH_pos := hcH
  wordCount := max 1 nWords
  wordCount_pos := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  etaB := η₀ / 2
  eta0 := η₀
  iota := 0
  rootMass := lawW.rootMass
  rootMass_pos := lawW.rootMass_pos
  rootReadout := lawW.rootReadout
  rootReadout_pos := lawW.rootReadout_pos

theorem termLaw_isTerminalLaw (lawW : BirthLaw) (cH η₀ : ℝ) (hcH : 0 < cH) (nWords : ℕ) :
    IsTerminalLaw lawW (termLaw lawW cH η₀ hcH nWords) cH η₀ nWords :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The internal order `K̂₃ = Khat (K̂ + 3)` lies above `K̂ + 3`. -/
theorem khat3_ge {X : TermConstruction} (A : TermArgs X) (K : ℕ) :
    max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2)) + 3 ≤
      max (max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2)) + 3)
        (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2)) := le_max_left _ _

/-- The statement's order `K̂` lies below the internal order. -/
theorem khat_le_khat3 {X : TermConstruction} (A : TermArgs X) (K : ℕ) :
    max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2)) ≤
      max (max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2)) + 3)
        (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2)) :=
  le_trans (Nat.le_add_right _ 3) (khat3_ge A K)

/-- The energy bound is monotone in its constant. -/
theorem terminalEnergyBound_mono {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    {Gw Gt : GenStage D ScalarH Dm b j₀} {M pT Khat NT depth sX sZ k₀ Kw : ℕ} {hk₀w : k₀ ≤ Kw}
    {η₀ tp tf cr cK QT C C' : ℝ} {lawW : BirthLaw} {f : Vec 2 → ℝ}
    {V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root)}
    {Vw : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root)}
    {Z : ∀ v : CompIn Gt.comps, ℝ → TorusHk Khat (ScalarH v.1.root)}
    (hε : 0 < D.eps (M - 1)) (hCC : C ≤ C')
    (h : TerminalEnergyBound Gw Gt M pT Khat NT depth sX sZ k₀ Kw hk₀w η₀ tp tf cr cK QT C lawW f
      V Vw Z) :
    TerminalEnergyBound Gw Gt M pT Khat NT depth sX sZ k₀ Kw hk₀w η₀ tp tf cr cK QT C' lawW f V Vw
      Z := by
  intro CcT PZ aRep û ŵ hl hw
  refine (h CcT PZ aRep û ŵ hl hw).trans (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC
    (Real.rpow_nonneg hε.le _)) (Real.sqrt_nonneg _)

/-- **The energy and the identity at one level**, for one datum and one family (error energy and readout glue). -/
theorem route_identity_atM (h10 : ReadoutGlueStatement) {X : TermConstruction} (A : TermArgs X)
    (K sXT sZT Kw Lt : ℕ) (nW : ℕ+) (hk₀w : A.k₀ ≤ Kw) (cr : ℝ) (kS : InvConsts)
    (cK CK CL Cχ Cread Cid : ℝ) (kW : InvConsts) (c CP C cH Ce Cw C9 : ℝ)
    (cker : ℕ → ℝ) (j₀ M : ℕ)
    (h9M : EnergyAtM A K sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW c CP cH C9 Ce Cw
      cker j₀ M)
    (hsM : ScaleAtM A Cread Cid (max C9 0) C M) (hτT : A.τ < A.T₀) (hLk : A.Lw + 5 ≤ A.k₀)
    (hC0 : 0 ≤ C) {D : OCData} (hDα : D.α = X.α) (hDq : D.q = X.q)
    (hDΛ : D.Λ = A.Λ) (hDζ : D.ζ = X.ζ) (hstream : IsOCStreamSeq X.α X.q A.Λ X.ζ D.Φ)
    (hband : IsOCBandChain X.α X.q A.Λ X.ζ M D.κ) (hterm : D.term = M)
    (hεM : 0 < D.eps M) (hεM1 : 0 < D.eps (M - 1))
    (a : ℝ) (lawW : BirthLaw) (PW : ProvParams) (Gw : GenStage D ScalarH (termD0bar A.NT A.pT A.DW A.dW) A.bw j₀) (aM : ℝ)
    (Ww : ℝ → (CompIn Gw.comps → Vec 2 → ℝ) → Vec 2 → ℝ)
    (hW : IsWeakStage lawW PW A.φ₀ A.hφ₀ M (M + A.Jw) A.Jw A.dW A.DW nW kW a A.T₀ A.σw CL Cχ A.χw
      Gw aM)
    (tp : ℝ) (Pterm : (∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn Gw.comps, TorusHk (max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) (ScalarH v.1.root)))
    (lawT : BirthLaw) (Gt' : GenStage D ScalarH (termD0bar A.NT A.pT A.DW A.dW) A.bw j₀)
    (hmap : IsTerminalPrepMap M Kw (max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) c CP Gw aM tp Pterm)
    (hlaw : IsTerminalLaw lawW lawT cH A.η₀ (wordsUpTo (termAlphabet A.NT A.pT A.DW A.dW) A.RT).card)
    (hsucc : IsActualSuccessor D (termProvParams D Cw cr A.tT A.η₀ A.NT A.pT M)
      (termMenu (M + A.Jw) (termAlphabet A.NT A.pT A.DW A.dW) A.RT A.NT A.pT sXT sZT A.η₀ tp cr) Gw Gt')
    (hcert : TerminalSeedCertificate (termProvParams D Cw cr A.tT A.η₀ A.NT A.pT M) lawT
      (fun _ => isoPairedKernel (D.termRW A.σw M) nW) (fun _ => isoPairedKernel (D.termRNew cr A.tT M) A.nT)
      A.φ₀ A.hφ₀ cker (M + A.Jw) (M - 1) M (max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) kS Ce A.τe (termR0bar A.RT A.dW) (termD0bar A.NT A.pT A.DW A.dW)
      (succSchedD (termD0bar A.NT A.pT A.DW A.dW) A.N A.p (A.H + 1)) cr tp (tp + D.termH M) (a + A.T₀)
      (Gt'.retained M 1 A.RT))
    (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ) (U₀ : ∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root))
    (U V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root))
    (Uw Vw : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
    (Uk Vk : ∀ v u (_ : Gw.fam.Γ v u), ℝ → TorusHk (Kw + (termD0bar A.NT A.pT A.DW A.dW) - 1) (ScalarH u.1.root))
    (hpaired : IsWeakPaired PW A.φ₀ A.hφ₀ lawW M Kw Lt nW a A.T₀ A.σw A.χw cK CK f Gw aM U₀ U V Uw
      Vw Uk Vk)
    (hread : IsWeakReadout lawW M A.Jw A.Lw Kw (D.κ M) a A.τ A.T₀ X.s A.Pw cK Cread Cid f θ Gw Ww V)
    (hb : IsTerminalPrepBounds lawW M Kw (max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) A.k₀ hk₀w (k0_le_khat K A.k₀ A.NT A.pT) cr cK CP
      A.QT f Gw aM tp Pterm V)
    (Z₀ : ∀ v : CompIn (Gt'.retained M 1 A.RT).comps, TorusHk (max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) (ScalarH v.1.root))
    (Z : ∀ v : CompIn (Gt'.retained M 1 A.RT).comps, ℝ → TorusHk (max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) (ScalarH v.1.root))
    (Zw : ∀ v : CompIn (Gt'.retained M 1 A.RT).comps, ℝ → TorusHk ((max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) + 1) (ScalarH v.1.root))
    (Zk : ∀ v u (_ : (Gt'.retained M 1 A.RT).fam.Γ v u), ℝ →
      TorusHk ((max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) + (termD0bar A.NT A.pT A.DW A.dW) - 1) (ScalarH u.1.root))
    (htrace : IsTerminalTrace Gw (Gt'.retained M 1 A.RT) (Pterm fun v => V v aM) Z₀)
    (hreg : (Gt'.retained M 1 A.RT).IsRegSolution (termProvParams D Cw cr A.tT A.η₀ A.NT A.pT M)
      (fun _ => isoPairedKernel (D.termRW A.σw M) nW) (fun _ => isoPairedKernel (D.termRNew cr A.tT M) A.nT)
      A.φ₀ A.hφ₀ (D.termB M) (streamVel (D.Φ (M - 1))) (max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) tp (a + A.T₀) Z₀ (fun _ _ => 0)
      (fun _ _ => 0) Z Zw Zk)
    (hreal : TerminalLiftRealization Gw (Gt'.retained M 1 A.RT) M A.pT (max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) A.NT A.dW sXT sZT A.k₀
      A.Lw A.η₀ tp (a + A.T₀) cr Z) :
    EntryIdentityClauses Gw (Gt'.retained M 1 A.RT) M A.pT (max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) Kw A.Lw A.NT A.dW sXT sZT
      A.η₀ tp a A.τ A.T₀ X.s A.Pw A.PT C cr f θ Ww V Z := by
  have hD : IsTermData X A.Λ M D := ⟨hDα, hDq, hDΛ, hDζ, hstream, hband, hterm⟩
  have henergy := h9M D hDα hDq hDΛ hDζ hstream hband hterm a lawW PW Gw aM Ww hW tp
    Pterm lawT Gt' hmap hlaw hsucc hcert f θ U₀ U V Uw Vw Uk Vk hpaired hread hb Z₀ Z Zw Zk htrace
    hreg
  obtain ⟨hsc1, hsc2⟩ := hsM D hD
  exact h10 Gw (Gt'.retained M 1 A.RT) lawW M A.Jw A.Lw Kw A.k₀ A.pT (max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) A.NT A.dW sXT sZT
    hk₀w (D.κ M) a A.τ A.T₀ X.s A.Pw A.PT A.QT cK Cread Cid (max C9 0) C tp A.η₀ cr f θ Ww V Vw Z
    hεM hεM1 hτT hLk (le_max_right _ _) hC0 hread hsc1 hsc2 hreal
    (terminalEnergyBound_mono hεM1 (le_max_left _ _) henergy)

/-- **The coarse family at one level**: the coarse family at the internal order `K̂₃` and its
truncation to `K̂`, for one datum. -/
theorem route_coarse_atM (hFT : FamilyTruncStatement) {X : TermConstruction} (A : TermArgs X)
    (K sXT sZT Kw : ℕ) (nW : ℕ+) (cr c CP C Centry cH Cw : ℝ) (cker : ℕ → ℝ) (j₀ M : ℕ)
    (h6M : CoarseAtM A (max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2)) + 3) nW cr c CP cH
      cker C Centry M) {D : OCData} (hD : IsTermData X A.Λ M D)
    (a : ℝ) (lawW : BirthLaw) (Gw : GenStage D ScalarH (termD0bar A.NT A.pT A.DW A.dW) A.bw j₀) (aM : ℝ)
    (hlev : Gw.level = M) (hroots : ∀ v : CompIn Gw.comps, v.1.births = [])
    (hmassW : ∀ v, 0 ≤ Gw.mass lawW v)
    (tp : ℝ) (P₃ : (∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn Gw.comps, TorusHk (max (max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2)) + 3) (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) (ScalarH v.1.root)))
    (lawT : BirthLaw) (Gt' : GenStage D ScalarH (termD0bar A.NT A.pT A.DW A.dW) A.bw j₀)
    (seed : GenStage D ScalarH (succSchedD (termD0bar A.NT A.pT A.DW A.dW) A.N A.p (A.H + 1)) A.bw j₀)
    (rootM rootR : ℕ → ℝ) (seedKc : ℕ → KernelSpec)
    (ι : CompIn (Gt'.retained M 1 A.RT).comps ≃ CompIn seed.comps)
    (Pterm : (∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn Gw.comps, TorusHk (max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) (ScalarH v.1.root)))
    (hlaw : IsTerminalLaw lawW lawT cH A.η₀ (wordsUpTo (termAlphabet A.NT A.pT A.DW A.dW) A.RT).card)
    (hsucc : IsActualSuccessor D (termProvParams D Cw cr A.tT A.η₀ A.NT A.pT M)
      (termMenu (M + A.Jw) (termAlphabet A.NT A.pT A.DW A.dW) A.RT A.NT A.pT sXT sZT A.η₀ tp cr) Gw Gt')
    (henc : IsSeedEncoding (termProvParams D Cw cr A.tT A.η₀ A.NT A.pT M) lawT rootM rootR (fun _ => isoPairedKernel (D.termRW A.σw M) nW) (fun _ => isoPairedKernel (D.termRNew cr A.tT M) A.nT) seedKc (Gt'.retained M 1 A.RT) seed ι)
    (hretained₃ : TerminalRetainedClauses lawT (termProvParams D Cw cr A.tT A.η₀ A.NT A.pT M) (fun _ => isoPairedKernel (D.termRW A.σw M) nW) (fun _ => isoPairedKernel (D.termRNew cr A.tT M) A.nT) A.φ₀ A.hφ₀ cker M (max (max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2)) + 3) (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) cr tp
      (a + A.T₀) (Gt'.retained M 1 A.RT))
    (f : Vec 2 → ℝ) (V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root))
    (hg : (Pterm fun v => V v aM) = famTrunc (khat_le_khat3 A K) (P₃ fun v => V v aM))
    (hloc : aM + c * D.termH M ≤ tp)
    (hdeadM : tp + D.termH M + 3 * ocTau X.α X.q A.Λ (M - 1) + 4 * ocTauPP X.α X.q A.Λ (M - 1) ≤
      a + A.T₀)
    (hbound : weightedNorm (D.termRho cr M) (Gw.mass lawW) (fun _ => 1) (P₃ fun v => V v aM) ≤
      CP * Real.sqrt (l2NormSq f)) :
    ∃ (Z₃ : ∀ v : CompIn (Gt'.retained M 1 A.RT).comps, ℝ → TorusHk (max (max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2)) + 3) (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) (ScalarH v.1.root))
      (Z : ∀ v : CompIn (Gt'.retained M 1 A.RT).comps, ℝ → TorusHk (max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) (ScalarH v.1.root)),
      (∀ v t, Z v t = truncateTorusHk (khat_le_khat3 A K) (Z₃ v t)) ∧
      TerminalFamilyClauses (termProvParams D Cw cr A.tT A.η₀ A.NT A.pT M) (fun _ => isoPairedKernel (D.termRW A.σw M) nW) (fun _ => isoPairedKernel (D.termRNew cr A.tT M) A.nT) A.φ₀ A.hφ₀ lawW lawT rootM M (max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) cr C Centry tp
        (tp + D.termH M) (a + A.T₀) f Gw (Gt'.retained M 1 A.RT) seed ι (Pterm fun v => V v aM) Z := by
  obtain ⟨Z₃, hfam₃⟩ := h6M j₀ D hD sXT sZT a aM tp Cw lawW lawT Gw Gt' seed rootM rootR seedKc ι
    hlev hroots hloc hdeadM hlaw hsucc henc hretained₃ f (P₃ fun v => V v aM) hbound
  refine ⟨Z₃, fun v t => truncateTorusHk (khat_le_khat3 A K) (Z₃ v t), fun _ _ => rfl, ?_⟩
  rw [hg]
  exact hFT (termProvParams D Cw cr A.tT A.η₀ A.NT A.pT M) (fun _ => isoPairedKernel (D.termRW A.σw M) nW) (fun _ => isoPairedKernel (D.termRNew cr A.tT M) A.nT) A.φ₀ A.hφ₀ lawW lawT rootM M (max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) _ (khat_le_khat3 A K) cr C Centry tp
    (tp + D.termH M) (a + A.T₀) f Gw (Gt'.retained M 1 A.RT) hmassW seed ι (P₃ fun v => V v aM) Z₃
    hfam₃

/-- **The family, the lifted field, the energy and the identity at one level**, for one datum:
the statement's family is the truncation of the coarse family of order `K̂₃`. -/
theorem route_family_atM (h10 : ReadoutGlueStatement) (hFT : FamilyTruncStatement)
    (hRT : RetainedTruncStatement) {X : TermConstruction} (A : TermArgs X)
    (K sXT sZT Kw Lt : ℕ) (nW : ℕ+) (hk₀w : A.k₀ ≤ Kw) (cr : ℝ) (kS : InvConsts)
    (cK CK CL Cχ Cread Cid : ℝ) (kW : InvConsts) (c CP C Centry cH Ce Cw C9 : ℝ)
    (cker : ℕ → ℝ) (j₀ M : ℕ)
    (h7M : LiftAtM A sXT sZT K Kw nW kW CL Cχ cr c CP Cw cH j₀ M)
    (h9M : EnergyAtM A K sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW c CP cH C9 Ce Cw
      cker j₀ M)
    (hsM : ScaleAtM A Cread Cid (max C9 0) C M) (hτT : A.τ < A.T₀) (hLk : A.Lw + 5 ≤ A.k₀)
    (hC0 : 0 ≤ C)
    (h6M : CoarseAtM A (max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2)) + 3) nW cr c CP cH
      cker C Centry M) {D : OCData} (hDα : D.α = X.α) (hDq : D.q = X.q)
    (hDΛ : D.Λ = A.Λ) (hDζ : D.ζ = X.ζ) (hstream : IsOCStreamSeq X.α X.q A.Λ X.ζ D.Φ)
    (hband : IsOCBandChain X.α X.q A.Λ X.ζ M D.κ) (hterm : D.term = M)
    (hεM : 0 < D.eps M) (hεM1 : 0 < D.eps (M - 1))
    (a : ℝ) (lawW : BirthLaw) (PW : ProvParams) (Gw : GenStage D ScalarH (termD0bar A.NT A.pT A.DW A.dW) A.bw j₀) (aM : ℝ)
    (Ww : ℝ → (CompIn Gw.comps → Vec 2 → ℝ) → Vec 2 → ℝ)
    (hW : IsWeakStage lawW PW A.φ₀ A.hφ₀ M (M + A.Jw) A.Jw A.dW A.DW nW kW a A.T₀ A.σw CL Cχ A.χw
      Gw aM) (hmassW : ∀ v, 0 ≤ Gw.mass lawW v)
    (tp : ℝ) (P₃ : (∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn Gw.comps, TorusHk ((max (max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2)) + 3) (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2)))) (ScalarH v.1.root)))
    (lawT : BirthLaw) (Gt' : GenStage D ScalarH (termD0bar A.NT A.pT A.DW A.dW) A.bw j₀) (seed : GenStage D ScalarH (succSchedD (termD0bar A.NT A.pT A.DW A.dW) A.N A.p (A.H + 1)) A.bw j₀)
    (rootM rootR : ℕ → ℝ) (seedKc : ℕ → KernelSpec)
    (ι : CompIn (Gt'.retained M 1 A.RT).comps ≃ CompIn seed.comps)
    (Pterm : (∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn Gw.comps, TorusHk ((max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2)))) (ScalarH v.1.root)))
    (hmap : IsTerminalPrepMap M Kw ((max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2)))) c CP Gw aM tp Pterm)
    (hlaw : IsTerminalLaw lawW lawT cH A.η₀ (wordsUpTo (termAlphabet A.NT A.pT A.DW A.dW) A.RT).card)
    (hsucc : IsActualSuccessor D ((termProvParams D Cw cr A.tT A.η₀ A.NT A.pT M)) ((termMenu (M + A.Jw) (termAlphabet A.NT A.pT A.DW A.dW) A.RT A.NT A.pT sXT sZT A.η₀ tp cr)) Gw Gt')
    (henc : IsSeedEncoding ((termProvParams D Cw cr A.tT A.η₀ A.NT A.pT M)) lawT rootM rootR ((fun _ => isoPairedKernel (D.termRW A.σw M) nW)) ((fun _ => isoPairedKernel (D.termRNew cr A.tT M) A.nT)) seedKc
      (Gt'.retained M 1 A.RT) seed ι)
    (hseedcl : TerminalSeedClauses rootM rootR seedKc A.φ₀ A.hφ₀ (M + A.Jw) (M - 1) kS Ce A.τe (termR0bar A.RT A.dW)
      (termD0bar A.NT A.pT A.DW A.dW) seed (tp + D.termH M) (a + A.T₀))
    (hretained₃ : TerminalRetainedClauses lawT ((termProvParams D Cw cr A.tT A.η₀ A.NT A.pT M)) ((fun _ => isoPairedKernel (D.termRW A.σw M) nW)) ((fun _ => isoPairedKernel (D.termRNew cr A.tT M) A.nT)) A.φ₀
      A.hφ₀ cker M ((max (max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2)) + 3) (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2)))) cr tp (a + A.T₀) (Gt'.retained M 1 A.RT))
    (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ) (U₀ : ∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root))
    (U V : ∀ v : CompIn Gw.comps, ℝ → TorusHk Kw (ScalarH v.1.root))
    (Uw Vw : ∀ v : CompIn Gw.comps, ℝ → TorusHk (Kw + 1) (ScalarH v.1.root))
    (Uk Vk : ∀ v u (_ : Gw.fam.Γ v u), ℝ → TorusHk (Kw + (termD0bar A.NT A.pT A.DW A.dW) - 1) (ScalarH u.1.root))
    (hpaired : IsWeakPaired PW A.φ₀ A.hφ₀ lawW M Kw Lt nW a A.T₀ A.σw A.χw cK CK f Gw aM U₀ U V Uw
      Vw Uk Vk)
    (hread : IsWeakReadout lawW M A.Jw A.Lw Kw (D.κ M) a A.τ A.T₀ X.s A.Pw cK Cread Cid f θ Gw Ww V)
    (hb : IsTerminalPrepBounds lawW M Kw ((max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2)))) A.k₀ hk₀w (k0_le_khat K A.k₀ A.NT A.pT) cr cK
      CP A.QT f Gw aM tp Pterm V)
    (hg : (Pterm fun v => V v aM) = famTrunc (khat_le_khat3 A K) (P₃ fun v => V v aM))
    (hloc : aM + c * D.termH M ≤ tp)
    (hdeadM : tp + D.termH M + 3 * ocTau X.α X.q A.Λ (M - 1) + 4 * ocTauPP X.α X.q A.Λ (M - 1) ≤
      a + A.T₀)
    (hbound : weightedNorm (D.termRho cr M) (Gw.mass lawW) (fun _ => 1) (P₃ fun v => V v aM) ≤
      CP * Real.sqrt (l2NormSq f)) :
    ∃ Z : ∀ v : CompIn (Gt'.retained M 1 A.RT).comps, ℝ → TorusHk ((max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2)))) (ScalarH v.1.root),
      TerminalFamilyClauses ((termProvParams D Cw cr A.tT A.η₀ A.NT A.pT M)) ((fun _ => isoPairedKernel (D.termRW A.σw M) nW)) ((fun _ => isoPairedKernel (D.termRNew cr A.tT M) A.nT)) A.φ₀ A.hφ₀ lawW lawT
        rootM M ((max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2)))) cr C Centry tp (tp + D.termH M) (a + A.T₀) f Gw (Gt'.retained M 1 A.RT)
        seed ι (Pterm fun v => V v aM) Z ∧
      EntryIdentityClauses Gw (Gt'.retained M 1 A.RT) M A.pT ((max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2)))) Kw A.Lw A.NT A.dW sXT sZT
        A.η₀ tp a A.τ A.T₀ X.s A.Pw A.PT C cr f θ Ww V Z := by
  have hD : IsTermData X A.Λ M D := ⟨hDα, hDq, hDΛ, hDζ, hstream, hband, hterm⟩
  obtain ⟨Z₃, Z, hZ, hfam⟩ := route_coarse_atM hFT A K sXT sZT Kw nW cr c CP C Centry cH Cw cker j₀
    M h6M hD a lawW Gw aM hW.2.2.1 hW.2.2.2.2.1 hmassW tp P₃ lawT Gt' seed rootM rootR seedKc ι Pterm hlaw
    hsucc henc hretained₃ f V hg hloc hdeadM hbound
  refine ⟨Z, hfam, ?_⟩
  have hreal := h7M D hD a lawW PW Gw aM hW tp Pterm hmap lawT Gt' hlaw hsucc Z _ (khat3_ge A K) Z₃
    (fun v t _ => hZ v t)
  obtain ⟨Z₀, Zw, Zk, htrace, hreg, -⟩ := hfam
  have hcert : TerminalSeedCertificate ((termProvParams D Cw cr A.tT A.η₀ A.NT A.pT M)) lawT ((fun _ => isoPairedKernel (D.termRW A.σw M) nW)) ((fun _ => isoPairedKernel (D.termRNew cr A.tT M) A.nT)) A.φ₀
      A.hφ₀ cker (M + A.Jw) (M - 1) M ((max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2)))) kS Ce A.τe (termR0bar A.RT A.dW) (termD0bar A.NT A.pT A.DW A.dW) (succSchedD (termD0bar A.NT A.pT A.DW A.dW) A.N A.p (A.H + 1)) cr tp (tp + D.termH M)
      (a + A.T₀) (Gt'.retained M 1 A.RT) :=
    ⟨seed, rootM, rootR, seedKc, ι, henc, hseedcl,
      hRT lawT ((termProvParams D Cw cr A.tT A.η₀ A.NT A.pT M)) ((fun _ => isoPairedKernel (D.termRW A.σw M) nW)) ((fun _ => isoPairedKernel (D.termRNew cr A.tT M) A.nT)) A.φ₀ A.hφ₀ cker M ((max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2)))) _
        (khat_le_khat3 A K) cr tp (a + A.T₀) (Gt'.retained M 1 A.RT) hretained₃⟩
  exact route_identity_atM h10 A K sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW c CP C cH
    Ce Cw C9 cker j₀ M h9M hsM hτT hLk hC0 hDα hDq hDΛ hDζ hstream hband hterm hεM hεM1 a lawW PW Gw
    aM Ww hW tp Pterm lawT Gt' hmap hlaw hsucc hcert f θ U₀ U V Uw Vw Uk Vk hpaired hread hb Z₀ Z Zw Zk htrace
    hreg hreal

/-- **The objects at one level `M`.** The preparation, the seed certificate and the coarse family
are built at the internal public order `K₃ = K̂ + 3`; the statement's map and family are their
truncations to `K̂`, and the lifted field reads the family of order `K̂₃`. -/
theorem route_atM (h4 : SeedEncodingStatement) (h10 : ReadoutGlueStatement)
    (hmono : PrepMonotoneStatement) (h13 : TruncationPartsStatement) {X : TermConstruction}
    (A : TermArgs X)
    (K sXT sZT Kw Lt : ℕ) (nW : ℕ+) (hk₀w : A.k₀ ≤ Kw) (cr : ℝ) (kS : InvConsts)
    (cK CK CL Cχ Cread Cid : ℝ) (kW : InvConsts) (c CP C Centry cH Ce Cw C9 : ℝ)
    (cker : ℕ → ℝ) (j₀ M : ℕ) (hcH : 0 < cH) (hCw : 0 ≤ Cw) (hCP : CP ≤ C)
    (hTnn : ∀ k, 0 ≤ ocTauPP X.α X.q A.Λ k)
    (hεpos : ∀ D : OCData, D.q = X.q → D.Λ = A.Λ → ∀ k, 0 < D.eps k)
    (h2M : PrepAtM A ((max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) + 3) Kw Lt nW hk₀w cr cK CK CL Cχ kW c CP j₀ M)
    (h3M : SuccAtM A sXT sZT nW cr CL Cχ kW j₀ M)
    (h5M : SeedAtM A ((max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) + 3) sXT sZT nW cr kS CL Cχ kW c CP cH Ce Cw cker j₀ M)
    (h6M : CoarseAtM A ((max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2))) + 3) nW cr c CP cH cker C Centry M)
    (h7M : LiftAtM A sXT sZT K Kw nW kW CL Cχ cr c CP Cw cH j₀ M)
    (h9M : EnergyAtM A K sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW c CP cH C9 Ce Cw
      cker j₀ M)
    (hsM : ScaleAtM A Cread Cid (max C9 0) C M) (hdM : DeadlineAtM A CP M)
    (hτT : A.τ < A.T₀) (hLk : A.Lw + 5 ≤ A.k₀) (hC0 : 0 ≤ C) (hΛ128 : 128 ≤ A.Λ) :
    BTailAtM A K sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW c C Centry cH Ce Cw j₀ M := by
  intro D hDα hDq hDΛ hDζ hstream hband hterm a lawW PW Gw aM Ww hW
  have hD : IsTermData X A.Λ M D := ⟨hDα, hDq, hDΛ, hDζ, hstream, hband, hterm⟩
  have hεM : 0 < D.eps M := hεpos D hDq hDΛ M
  have hεM1 : 0 < D.eps (M - 1) := hεpos D hDq hDΛ (M - 1)
  have hh : 0 ≤ D.termH M := by
    show 0 ≤ ocTauPP D.α D.q D.Λ M
    rw [hDα, hDq, hDΛ]
    exact hTnn M
  have hKK := khat_le_khat3 A K
  have hmassW : ∀ v, 0 ≤ Gw.mass lawW v := fun v =>
    (Construction.Preservation.Buffer.birth_compMass_pos (hDq ▸ X.hq.1) (hDΛ ▸ hΛ128) lawW v.1).le
  obtain ⟨hPT, hFT, hRT⟩ := h13
  -- the preparation at the internal order, and its truncation
  obtain ⟨tp, P₃, hmap₃, hbounds₃⟩ := h2M D hDα hDq hDΛ hDζ hstream hband hterm a lawW PW Gw aM
    Ww hW
  obtain ⟨Pterm, hPdef⟩ : ∃ Pterm : (∀ v : CompIn Gw.comps, TorusHk Kw (ScalarH v.1.root)) →ₗ[ℝ]
      (∀ v : CompIn Gw.comps, TorusHk ((max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2)))) (ScalarH v.1.root)), Pterm = famTrunc hKK ∘ₗ P₃ :=
    ⟨_, rfl⟩
  have hmapCP : IsTerminalPrepMap M Kw ((max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2)))) c CP Gw aM tp Pterm := by
    rw [hPdef]
    exact (hPT M Kw ((max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2)))) _ A.k₀ hKK hk₀w (k0_le_khat K A.k₀ A.NT A.pT) c CP cr cK A.QT
      aM tp lawW (fun _ => 0) Gw hmassW P₃ (fun _ _ => 0)).1 hmap₃
  have hmap := (hmono M Kw ((max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2)))) A.k₀ hk₀w (k0_le_khat K A.k₀ A.NT A.pT) c CP C cr cK A.QT aM
    tp lawW (fun _ => 0) Gw Pterm (fun _ _ => 0) hh hεM1 hCP).1 hmapCP
  -- the law, the successor, the re-rooting, the seed clauses
  let lawT := termLaw lawW cH A.η₀ hcH (wordsUpTo (termAlphabet A.NT A.pT A.DW A.dW) A.RT).card
  have hlaw : IsTerminalLaw lawW lawT cH A.η₀ (wordsUpTo (termAlphabet A.NT A.pT A.DW A.dW) A.RT).card := termLaw_isTerminalLaw lawW cH A.η₀ hcH _
  obtain ⟨Gt', hsucc⟩ := h3M D hD a lawW PW Gw aM hW tp Cw hCw
  obtain ⟨seed, rootM, rootR, seedKc, ι, henc, hrM, hrR, hexports⟩ :=
    h4 (le_succSchedD (termD0bar A.NT A.pT A.DW A.dW) A.N A.p (A.H + 1)) (hDq ▸ X.hq.1)
      (hDΛ ▸ hΛ128) ((termProvParams D Cw cr A.tT A.η₀ A.NT A.pT M)) lawT ((fun _ => isoPairedKernel (D.termRW A.σw M) nW)) ((fun _ => isoPairedKernel (D.termRNew cr A.tT M) A.nT))
      (Gt'.retained M 1 A.RT)
  obtain ⟨hseedcl, hretained₃⟩ := h5M D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι
    ⟨hD, hW, hmap₃.1, hmap₃.2.1, hmap₃.2.2.1, hlaw, hsucc, henc, hexports, hrM, hrR⟩
  have hdeadM := hdM D hD a aM tp hW.2.1 hmap₃.2.2.1
  refine ⟨tp, Pterm, lawT, Gt', seed, rootM, rootR, seedKc, ι, hmap,
    hlaw, hsucc, henc, hseedcl, hdeadM, ?_⟩
  intro f θ U₀ U V Uw Vw Uk Vk hpaired hread
  have hb₃ := hbounds₃ f U₀ U V Uw Vw Uk Vk hpaired
  have hbCP : IsTerminalPrepBounds lawW M Kw ((max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2)))) A.k₀ hk₀w (k0_le_khat K A.k₀ A.NT A.pT) cr cK
      CP A.QT f Gw aM tp Pterm V := by
    rw [hPdef]
    exact (hPT M Kw ((max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2)))) _ A.k₀ hKK hk₀w (k0_le_khat K A.k₀ A.NT A.pT) c CP cr cK A.QT
      aM tp lawW f Gw hmassW P₃ V).2 hb₃
  have hb := (hmono M Kw ((max K (max (2 * A.k₀ + 2) (A.NT + 2 * A.pT + A.k₀ + 2)))) A.k₀ hk₀w (k0_le_khat K A.k₀ A.NT A.pT) c CP C cr cK A.QT aM
    tp lawW f Gw Pterm V hh hεM1 hCP).2 hbCP
  refine ⟨hb, ?_⟩
  have hg : (Pterm fun v => V v aM) = famTrunc hKK (P₃ fun v => V v aM) := by
    rw [hPdef]
    exact LinearMap.comp_apply (famTrunc hKK) P₃ (fun v => V v aM)
  -- the first coarse family at the internal order, and its truncation
  exact route_family_atM h10 hFT hRT A K sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW c CP C
    Centry cH Ce Cw C9 cker j₀ M h7M h9M hsM hτT hLk hC0 h6M hDα hDq hDΛ hDζ hstream hband hterm hεM hεM1 a lawW PW
    Gw aM Ww hW hmassW tp P₃ lawT Gt' seed rootM rootR seedKc ι Pterm hmapCP hlaw hsucc henc hseedcl
    hretained₃ f θ U₀ U V Uw Vw Uk Vk hpaired hread hbCP hg hmap₃.2.1 hdeadM hb₃.1

/-- **The constants, the carrier start and the threshold.** -/
theorem route_consts (h4 : SeedEncodingStatement) (h10 : ReadoutGlueStatement)
    (hmono : PrepMonotoneStatement) (h13 : TruncationPartsStatement) {X : TermConstruction} (A : TermArgs X)
    (K sXT sZT Kw Lt : ℕ) (nW : ℕ+) (hk₀w : A.k₀ ≤ Kw) (cr : ℝ) (kS : InvConsts)
    (cK CK CL Cχ Cread Cid : ℝ) (kW : InvConsts) (hcr : 0 < cr) (hcr1 : cr ≤ 1)
    (hτT : A.τ < A.T₀) (hLk : A.Lw + 5 ≤ A.k₀) (hΛ128 : 128 ≤ A.Λ)
    (hAnn : ∀ k, 0 ≤ ocA X.α X.q A.Λ k) (hTnn : ∀ k, 0 ≤ ocTauPP X.α X.q A.Λ k)
    (hεpos : ∀ D : OCData, D.q = X.q → D.Λ = A.Λ → ∀ k, 0 < D.eps k)
    (h6A : ∀ (Kout : ℕ) (nW : ℕ+) (cr : ℝ), 0 < cr → cr ≤ 1 →
      ∀ (cP CP cH : ℝ) (cker : ℕ → ℝ), 0 < cP → 0 < cH →
      ∃ (C₀ Centry : ℝ), ∀ C : ℝ, C₀ ≤ C → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
        CoarseAtM A Kout nW cr cP CP cH cker C Centry M)
    (hrsA : ∀ (Cread Cid CE : ℝ), ∃ C₀ : ℝ, ∀ C : ℝ, C₀ ≤ C → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      ScaleAtM A Cread Cid CE C M)
    (hdA : ∀ CP : ℝ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → DeadlineAtM A CP M)
    (c CP : ℝ) (hc : 0 < c)
    (h2c : ∀ j₀ : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      PrepAtM A (A.Khat K + 3) Kw Lt nW hk₀w cr cK CK CL Cχ kW c CP j₀ M)
    (CH3 Υ3 : ℝ) (hCH3 : 1 ≤ CH3) (hΥ3 : 0 < Υ3)
    (h3c : ∀ j₀ : ℕ, IsCarrierStart X.α X.q A.Λ A.bw CH3 Υ3 j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      SuccAtM A sXT sZT nW cr CL Cχ kW j₀ M)
    (cH Ce Cw CHe Υe : ℝ) (cker : ℕ → ℝ) (hcH : 0 < cH) (hCe : 1 ≤ Ce) (hCw : 0 ≤ Cw)
    (hCHe : 1 ≤ CHe)
    (hΥe : 0 < Υe)
    (h5c : ∀ j₀ : ℕ, IsCarrierStart X.α X.q A.Λ A.bw CHe Υe j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      SeedAtM A (A.Khat K + 3) sXT sZT nW cr kS CL Cχ kW c CP cH Ce Cw cker j₀ M)
    (h7b : ∀ (c C Cw cH : ℝ), 0 < c → 0 < cH → ∀ j₀ : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      LiftAtM A sXT sZT K Kw nW kW CL Cχ cr c C Cw cH j₀ M)
    (h9b : ∃ C : ℝ, ∃ (CHt Υt : ℝ),
      1 ≤ CHt ∧ 0 < Υt ∧ ∀ j₀ : ℕ, IsCarrierStart X.α X.q A.Λ A.bw CHt Υt j₀ → ∃ M₀ : ℕ,
      ∀ M : ℕ, M₀ ≤ M → EnergyAtM A K sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW c CP
        cH C Ce Cw cker j₀ M) :
    BTailConsts A K sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW := by
  obtain ⟨C6, Centry, h6c⟩ := h6A (A.Khat K + 3) nW cr hcr hcr1 c CP cH cker hc hcH
  obtain ⟨C9, CH9, Υ9, hCH9, hΥ9, h9c⟩ := h9b
  obtain ⟨C10, h10c⟩ := hrsA Cread Cid (max C9 0)
  obtain ⟨C, hCP, hC6, hC10, hC0⟩ : ∃ C, CP ≤ C ∧ C6 ≤ C ∧ C10 ≤ C ∧ 0 ≤ C :=
    ⟨max (max CP C6) (max C10 0), le_trans (le_max_left _ _) (le_max_left _ _),
      le_trans (le_max_right _ _) (le_max_left _ _), le_trans (le_max_left _ _) (le_max_right _ _),
      le_trans (le_max_right _ _) (le_max_right _ _)⟩
  obtain ⟨M6, h6d⟩ := h6c C hC6
  obtain ⟨M10, h10d⟩ := h10c C hC10
  obtain ⟨Md, hdd⟩ := hdA CP
  refine ⟨c, C, Centry, cH, Ce, Cw, hc, hcH, hCe, max CH3 (max CHe CH9), max Υ3 (max Υe Υ9),
    le_trans hCH3 (le_max_left _ _), lt_of_lt_of_le hΥ3 (le_max_left _ _), fun j₀ hj₀ => ?_⟩
  have hj3 : IsCarrierStart X.α X.q A.Λ A.bw CH3 Υ3 j₀ :=
    IsCarrierStart.mono hAnn hTnn (le_max_left _ _) (le_max_left _ _) (zero_le_one.trans hCH3)
      hΥ3.le hj₀
  have hj5 : IsCarrierStart X.α X.q A.Λ A.bw CHe Υe j₀ :=
    IsCarrierStart.mono hAnn hTnn (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_trans (le_max_left _ _) (le_max_right _ _)) (zero_le_one.trans hCHe) hΥe.le hj₀
  have hj9 : IsCarrierStart X.α X.q A.Λ A.bw CH9 Υ9 j₀ :=
    IsCarrierStart.mono hAnn hTnn (le_trans (le_max_right _ _) (le_max_right _ _))
      (le_trans (le_max_right _ _) (le_max_right _ _)) (zero_le_one.trans hCH9) hΥ9.le hj₀
  obtain ⟨M2, h2d⟩ := h2c j₀
  obtain ⟨M3, h3d⟩ := h3c j₀ hj3
  obtain ⟨M5, h5d⟩ := h5c j₀ hj5
  obtain ⟨M9, h9d⟩ := h9c j₀ hj9
  obtain ⟨M7, h7d⟩ := h7b c CP Cw cH hc hcH j₀
  refine ⟨max (max (max M2 M3) (max M5 M6)) (max (max M7 M9) (max M10 Md)), fun M hM => ?_⟩
  exact route_atM h4 h10 hmono h13 A K sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW c CP C
    Centry cH Ce Cw C9 cker j₀ M hcH hCw hCP hTnn hεpos (h2d M (m2l (m2l (m2l hM))))
    (h3d M (m2r (m2l (m2l hM)))) (h5d M (m2l (m2r (m2l hM)))) (h6d M (m2r (m2r (m2l hM))))
    (h7d M (m2l (m2l (m2r hM)))) (h9d M (m2r (m2l (m2r hM)))) (h10d M (m2l (m2r (m2r hM))))
    (hdd M (m2r (m2r (m2r hM)))) hτT hLk hC0 hΛ128

/-- The repetition schedule does not decrease. -/
theorem route_succSchedR_ge (r J : ℕ) : ∀ g, r ≤ succSchedR r J g
  | 0 => le_rfl
  | g + 1 => by
      have := route_succSchedR_ge r J g
      show r ≤ (J + 2) * (succSchedR r J g + 1) - 1
      have h : succSchedR r J g + 1 ≤ (J + 2) * (succSchedR r J g + 1) :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega

/-- The order schedule does not decrease. -/
theorem route_succSchedD_ge (D₀ N p : ℕ) : ∀ g, D₀ ≤ succSchedD D₀ N p g
  | 0 => le_rfl
  | g + 1 => by
      have := route_succSchedD_ge D₀ N p g
      show D₀ ≤ succSchedD D₀ N p g + 2 * N + 4 * p + 4
      omega

/-- **The strict reserve** of the weak constants from the seed and weak allocations. -/
theorem route_reserve_strict {X : TermConstruction} {A : TermArgs X} {kS kW : InvConsts} {Lt : ℕ}
    (hsa : IsSeedAllocation kS A.r0 A.Dt A.H A.J A.N A.p A.Kres A.Lpr A.Lc A.Lf)
    (hWA : IsWeakAllocation kW kS Lt) : kW.G0 ≤ kW.Hprod := by
  have h1 := hWA.2.2.2.2.2.1
  have h2 := hWA.2.2.2.2.2.2.1
  have h3 := hsa.2.2.2.2.2.2.2.2.1
  omega

/-- **The weight floor** `N_T + D_W + d_W(D_t + 1) ≤ k_W.L_*` from the seed allocation
(`succLstar ≤ k_S.L_*`, the schedule dominations at `g = H + 1` with `r₀ ≥ d_W`, `D₀ = D_t`) and the
weak allocation (`k_S.L_* ≤ k_W.L_*`). -/
theorem route_lstar_floor {X : TermConstruction} {A : TermArgs X} {kS kW : InvConsts} {Lt : ℕ}
    (hsa : IsSeedAllocation kS A.r0 A.Dt A.H A.J A.N A.p A.Kres A.Lpr A.Lc A.Lf)
    (hWA : IsWeakAllocation kW kS Lt) : A.NT + A.DW + A.dW * (A.Dt + 1) ≤ kW.Lstar := by
  have hL := hsa.2.2.2.2.2.1
  have hR := hsa.2.2.2.2.2.2.1 (A.H + 1)
  have hD := hsa.2.2.2.2.2.2.2.1 (A.H + 1)
  have hLW := hWA.2.2.2.2.1
  have hr0 : A.dW ≤ A.r0 := by
    show A.dW ≤ termR0bar A.RT A.dW
    unfold termR0bar
    refine le_trans ?_ (le_max_right _ _)
    have : A.dW + 1 ≤ (A.RT + 2) * (A.dW + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hmem : WordLetter.diag ∈ termAlphabet A.NT A.pT A.DW A.dW := by
    simp [termAlphabet, succAlphabet]
  have hsup := Finset.le_sup (f := letterOrder A.NT A.pT) hmem
  have hNT : A.NT + 1 ≤ A.Dt := by
    have h1 : A.NT + 1 ≤ letterOrder A.NT A.pT WordLetter.diag := by
      simp only [letterOrder]; omega
    exact le_trans h1 (le_trans hsup (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hDW : A.DW ≤ A.Dt := le_trans (le_max_left _ _) (le_max_right _ _)
  have e : kS.G0 + (A.H + 1) = kS.G0 + A.H + 1 := by omega
  rw [e] at hR hD
  have hRb : A.dW ≤ succSchedR 0 A.J (kS.G0 + A.H + 1) :=
    le_trans (le_trans hr0 (route_succSchedR_ge _ _ _)) hR
  have hDb : A.Dt ≤ succSchedD 2 A.N A.p (kS.G0 + A.H + 1) :=
    le_trans (route_succSchedD_ge _ _ _ _) hD
  unfold succLstar at hL
  set R := succSchedR 0 A.J (kS.G0 + A.H + 1)
  set Dd := succSchedD 2 A.N A.p (kS.G0 + A.H + 1)
  have h1 : (A.dW + 1) * (A.Dt + 2) ≤ (R + 1) * (Dd + 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2 : (R + 1) * (Dd + 2) * 2 ≤ (R + 1) * ((2 * A.N + 4) + Dd + 2) * (Dd + 2) := by
    rw [mul_assoc, mul_assoc]
    exact Nat.mul_le_mul_left _ (by nlinarith)
  have h3 : A.NT + A.DW + A.dW * (A.Dt + 1) ≤ (A.dW + 1) * (A.Dt + 2) * 2 := by nlinarith
  nlinarith

/-- **The tail of `entry_terminal_of_weak` at every public order, from the route**, with the error
energy over the bundled data (`ErrorEnergyBundled`, which `errorEnergyBundled_of_residual` gives
directly). -/
theorem route_tail_of_bundled (h2 : PreparationStatement) (h3 : SuccessorStatement)
    (h4 : SeedEncodingStatement) (h5 : SeedClausesStatement) (h6 : CoarseFamilyStatement)
    (h7 : LiftFieldStatement) (h9 : ErrorEnergyBundled) (h10 : ReadoutGlueStatement)
    (h11 : TruncationStatement) (h13 : TruncationPartsStatement) (hplan : PlanStatement)
    (hdead : DeadlineStatement) (hrs : ReadoutScaleStatement) (hsf : ScaleFactsStatement)
    (hmono : PrepMonotoneStatement) :
    ∀ X : TermConstruction, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ A : TermArgs X, Λ₀ ≤ A.Λ → A.Valid →
      ∀ Kout : ℕ, A.tail Kout := by
  intro X
  obtain ⟨Λ2, hΛ2, h2'⟩ := preparationBundled_of h2 X
  obtain ⟨Λ9, hΛ9, h9'⟩ := h9 X
  obtain ⟨Λ3, hΛ3, h3'⟩ := h3 X
  obtain ⟨Λ5, hΛ5, h5'⟩ := h5 X
  obtain ⟨Λ6, hΛ6, h6'⟩ := h6 X
  obtain ⟨Λ7, hΛ7, h7'⟩ := h7 X
  obtain ⟨Λd, hΛd, hdead'⟩ := hdead X
  obtain ⟨Λs, hΛs, hrs'⟩ := hrs X
  refine ⟨max (max (max Λ2 Λ9) (max Λ3 Λ5)) (max (max Λ6 Λ7) (max Λd Λs)),
    le_trans hΛ2 (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))), ?_⟩
  intro A hΛ hA Kout
  have hΛ128 : 128 ≤ A.Λ := le_trans hΛ2 (m2l (m2l (m2l hΛ)))
  obtain ⟨hAnn, hTnn, hεpos⟩ := hsf X A.Λ hΛ128
  obtain ⟨SX9, SZ9, Kfloor, h9a⟩ := h9' A (m2r (m2l (m2l hΛ))) hA
  refine h11 X A hA Kout (max Kout Kfloor) (le_max_left _ _) (tail_of_bTail A _ ?_)
  obtain ⟨K, hKf, hK⟩ : ∃ K, Kfloor ≤ K ∧ K = max Kout Kfloor := ⟨_, le_max_right _ _, rfl⟩
  rw [← hK]
  -- the lift floors
  obtain ⟨SX3, SZ3, h3a⟩ := h3' A (m2l (m2r (m2l hΛ))) hA
  obtain ⟨SX5, SZ5, h5a⟩ := h5' A (m2r (m2r (m2l hΛ))) hA (A.Khat K + 3)
  obtain ⟨SX7, SZ7, h7a⟩ := h7' A (m2r (m2l (m2r hΛ))) hA
  refine ⟨max (max SX3 SX5) (max SX7 SX9), max (max SZ3 SZ5) (max SZ7 SZ9),
    fun sXT sZT hX hZ => ?_⟩
  -- the plan
  obtain ⟨Kneed9, h9b⟩ := h9a sXT sZT (m2r (m2r hX)) (m2r (m2r hZ)) K hKf
  obtain ⟨KS, F, h5b⟩ := h5a sXT sZT (m2r (m2l hX)) (m2r (m2l hZ))
  obtain ⟨Kneed2, h2b⟩ := h2' A (m2l (m2l (m2l hΛ))) hA (A.Khat K + 3)
  obtain ⟨Kw, Lt, nW, hk₀w, hLw, cr, kS, hL0, hLp, hLn, hko, hcr, hcreq, hkcr, hc0, hc0m, hkcr1, hσf,
    hlam, halloc, hLker, hKw, hKs, hKan, hLan, hJm, hG0, hF, hmE, hKanS, hLanS, hJmS, hfloor⟩ :=
    hplan X A hA (max (max Kneed2 Kneed9) KS) F
  have hcr1 : cr ≤ 1 := hkcr ▸ hkcr1
  refine ⟨Kw, Lt, nW, hk₀w, hLw, cr, kS,
    hL0, hLp, hLn, hko, hcr, hkcr, hc0, hc0m.trans (min_le_right _ _), hkcr1, hσf, hlam, halloc,
    ⟨hmE, hKanS, hLanS, hJmS⟩, hfloor, hcreq, ?_⟩
  intro cK CK CL Cχ Cread Cid kW hcK hkW hWA
  -- the constants of the preparation, successor, seed clauses, lifted field and the error-energy residual
  obtain ⟨c, CP, hc, h2c⟩ := h2b Kw Lt nW hk₀w cr (m2l (m2l hKw)) hLp hLn hcr hcr1 cK CK CL Cχ kW
    hcK hkW (le_trans (m2l (m2l hKs)) hWA.1) (le_trans (m2l (m2l hKan)) hWA.2.1)
    (le_trans (m2l (m2l hLan)) hWA.2.2.1) (le_trans (m2l (m2l hJm)) hWA.2.2.2.1)
    hWA.2.2.2.2.2.2.2.2.2
  obtain ⟨cH, hcH, hcH1, Cw₅, h5d⟩ := h5b Lt nW cr kS
    ⟨hL0, hLp, hLn, hko, hcr, hcr1, hkcr, hc0, hc0m, m2r hKs, hG0, hσf, hlam, halloc, hLker, hF⟩
    cK CL Cχ kW hcK hkW hWA c CP hc
  -- the witness constant above the seed's and the error energy's thresholds
  obtain ⟨Cw₉, h9d⟩ := h9b Kw Lt nW hk₀w hLw cr kS (m2r (m2l hKw)) hL0 hLp hLn hko hcr hcr1 hcreq
    hkcr hc0 (m2r (m2l hKs)) (m2r (m2l hKan)) (m2r (m2l hLan)) (m2r (m2l hJm))
    cK CK CL Cχ Cread Cid kW hcK hkW hWA (route_reserve_strict halloc hWA)
    (route_lstar_floor halloc hWA) c CP cH hc hcH1
  obtain ⟨Ce, CHe, Υe, cker, hCe, hCw, hCHe, hΥe, h5c⟩ := h5d (max Cw₅ Cw₉) (le_max_left _ _)
  obtain ⟨CH3, Υ3, hCH3, hΥ3, h3c⟩ := h3a sXT sZT (m2l (m2l hX)) (m2l (m2l hZ)) Lt nW cr kS hcr
    hcr1 cK CL Cχ kW hcK hkW hWA
  -- the weak roots' reserve, from the weak and seed allocations
  have hkw : kW.G0 ≤ kW.Hprod + 1 := by
    have h1 := hWA.2.2.2.2.2.1
    have h2 := hWA.2.2.2.2.2.2.1
    have h3 := halloc.2.2.2.2.2.2.2.2.1
    omega
  have h7b := fun c C Cw cH hc hcH =>
    h7a sXT sZT (m2l (m2r hX)) (m2l (m2r hZ)) K Kw nW cr hcr hcr1 kW CL Cχ c C Cw cH hc hcH hkw
  have hτT : A.τ < A.T₀ := hA.2.2.2.1.2.2.1
  have hLk : A.Lw + 5 ≤ A.k₀ := by
    obtain ⟨h, -⟩ := hA.2.2.2.2.2.1
    exact h
  exact route_consts h4 h10 hmono h13 A K sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW hcr hcr1
    hτT hLk hΛ128 hAnn hTnn hεpos (h6' A (m2l (m2l (m2r hΛ))) hA) (hrs' A (m2r (m2r (m2r hΛ))) hA)
    (hdead' A (m2l (m2r (m2r hΛ))) hA) c CP hc h2c CH3 Υ3 hCH3 hΥ3 h3c cH Ce (max Cw₅ Cw₉) CHe Υe
    cker hcH hCe hCw hCHe hΥe h5c h7b (h9d (max Cw₅ Cw₉) Ce cker (le_max_right _ _))


/-- **The tail of `entry_terminal_of_weak` at every public order, from the route.** -/
theorem route_tail (h2 : PreparationStatement) (h3 : SuccessorStatement)
    (h4 : SeedEncodingStatement) (h5 : SeedClausesStatement) (h6 : CoarseFamilyStatement)
    (h7 : LiftFieldStatement) (h9 : ErrorEnergyStatement) (h10 : ReadoutGlueStatement)
    (h11 : TruncationStatement) (h13 : TruncationPartsStatement) (hplan : PlanStatement)
    (hdead : DeadlineStatement) (hrs : ReadoutScaleStatement) (hsf : ScaleFactsStatement)
    (hmono : PrepMonotoneStatement) :
    ∀ X : TermConstruction, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ A : TermArgs X, Λ₀ ≤ A.Λ → A.Valid →
      ∀ Kout : ℕ, A.tail Kout :=
  route_tail_of_bundled h2 h3 h4 h5 h6 h7 (errorEnergyBundled_of h9) h10 h11 h13 hplan hdead hrs hsf
    hmono

end AVRegularity.EntryTerminal.Route
end

section
namespace AVRegularity.EntryTerminal.Route

/-! **`entry_terminal_of_weak` from its route**: the exact statement of `entry_terminal_of_weak`
(`EntryTerminal.Assembly.EntryTerminalOfWeakStatement`, a text copy of
`Entry/EntryTerminal`; the copy is definitionally equal to it) from the named ingredients of `Route/Ingredients` and the capped preparation and error-energy
statements. Every hypothesis is one of these ingredients.

With `EntryTerminal/Assembly/EntryTerminalOfIngredients`, which composes `entry_weak` with
this statement, `entry_terminal` follows from the same ingredients and
`entry_weak`. -/

/-- **`entry_terminal_of_weak` from the terminal route.** -/
theorem entry_terminal_of_weak_of_route (h2 : PreparationStatement) (h3 : SuccessorStatement)
    (h4 : SeedEncodingStatement) (h5 : SeedClausesStatement) (h6 : CoarseFamilyStatement)
    (h7 : LiftFieldStatement) (h9 : ErrorEnergyStatement) (h10 : ReadoutGlueStatement)
    (h11 : TruncationStatement) (h13 : TruncationPartsStatement) (hplan : PlanStatement)
    (hdead : DeadlineStatement) (hrs : ReadoutScaleStatement) (hsf : ScaleFactsStatement)
    (hmono : PrepMonotoneStatement) :
    Assembly.EntryTerminalOfWeakStatement := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λ₀, h128, h⟩ := route_tail h2 h3 h4 h5 h6 h7 h9 h10 h11 h13 hplan hdead hrs hsf hmono
    ⟨α, s, q, ζ, hα₀, hα₁, hs₀, hs₁, hq, hζ⟩
  refine ⟨Λ₀, h128, ?_⟩
  intro Λ hΛ c₀max hc0 φ₀ hφ₀ hφs hφn hφm hφsupp bw hbw0 hbw1 Jw Lw dW DW L0w τ T₀ Pw σw χw η₀
    hJw hDW hτ hτT hPw hσw0 hσw1 hχw hη0 hη1 PT hPT NT pT RT AT k₀ LcT LoT LfT LpT tT QT hsched τe lamE
    hexp σ₀ H J N p Kres Lpr Lc Lf nT hfresh Kout
  exact (h ⟨Λ, c₀max, φ₀, hφ₀, bw, Jw, Lw, dW, DW, L0w, τ, T₀, Pw, σw, χw, η₀, PT, NT, pT, RT, AT,
      k₀, LcT, LoT, LfT, LpT, tT, QT, τe, lamE, σ₀, H, J, N, p, Kres, Lpr, Lc, Lf, nT⟩ hΛ
    ⟨hc0, ⟨hφs, hφn, hφm, hφsupp⟩, ⟨hbw0, hbw1⟩, ⟨hJw, hτ, hτT, hPw, hσw0, hσw1, hχw, hη0, hη1⟩,
      hPT, hsched, hexp, hfresh, hDW⟩ Kout : _)

end AVRegularity.EntryTerminal.Route
end
