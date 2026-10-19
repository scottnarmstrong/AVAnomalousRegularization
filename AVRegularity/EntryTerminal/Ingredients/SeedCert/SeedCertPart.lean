-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Ingredients.SeedCert.MenuFieldsStmt
import AVRegularity.Proofs.Results.Construction.ComparisonLiftPositiveLayer
import AVRegularity.Proofs.Results.Construction.ContextCertified.Assemble
import AVRegularity.Proofs.ComplexContext.Assemble
import AVRegularity.EntryTerminal.Ingredients.SeedQuiet.Proof
import AVRegularity.Construction.Preservation.FullLift.NativePulseTimeDissipation
import AVRegularity.EntryTerminal.Ingredients.SeedStruct.SeedStruct
public import AVRegularity.EntryTerminal.Assembly.Seed.RetainedGeneric
import AVRegularity.Proofs.GenSem.SuccessorGeneration.Terminal
import Mathlib.Analysis.Real.Pi.Bounds

section
section
/-! **The certificate of the terminal successor `Gt'` at the weak constants `kW`**
(`TermCertBlock`), from the carrier calculus (`gen_carrier_calculus`, menu-free), the ledger of `Gt'`
(`terminal_ledger_concl`, from the generic `ledger_all_menu` and the budgets) and
`GenStage.isContextCertified_of_gates`. No ledger hypothesis.

The constants are chosen in the order of `SeedCertBlock`: `κ_c`, the carrier pair `(1, Υ_e)` with
`Υ_e ≥ max Υ₀ 400` (so `100 ≤ Υ_e`), the thresholds of the two budgets as `C_{w,0}`, then `j₀`, then
`M₀` (the level floor of the menu facts and `j₀ + 1 ≤ M`). The reserves `0 ≤ compReserve kW v` of the
components of `Gt'` (grades at most `2`) follow from `kW.G0 + 1 ≤ kS.G0` and
`kW.Hprod = kS.Hprod = kS.G0 + H + 1` (`IsWeakAllocation`, `IsSeedAllocation`).

Special cases: an empty `Gt'` (everything vacuous); `D_W`, `d_W` as in the budget modules. -/

@[expose] public section

open Homogenization AVRegularity AVRegularity.Sobolev

namespace AVRegularity.EntryTerminal.Route

open AVRegularity.Providers.CascadeInvariants AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant

/-- The certificate of `Gt'` at one level. -/
def TermCertAtM {X : TermConstruction} (A : TermArgs X) (sXT sZT : ℕ) (nW : ℕ+) (cr CL Cχ : ℝ)
    (kW : InvConsts) (cP CP cH Cw : ℝ) (j₀ M : ℕ) : Prop :=
  ∀ (D : OCData) (a : ℝ) (lawW : BirthLaw) (PW : ProvParams) (Gw : GenStage D ScalarH A.Dt A.bw j₀)
    (aM tp : ℝ) (lawT : BirthLaw) (Gt' : GenStage D ScalarH A.Dt A.bw j₀),
    TermPassCtx A sXT sZT nW cr CL Cχ kW cP CP cH Cw M D a lawW PW Gw aM tp lawT Gt' →
    Gt'.IsContextCertified kW

/-- The block of `TermCertAtM`, in the shape of `SeedCertBlock`. -/
def TermCertBlock {X : TermConstruction} (A : TermArgs X) (sXT sZT : ℕ) (nW : ℕ+) (cr CL Cχ : ℝ)
    (kW : InvConsts) (cP CP : ℝ) : Prop :=
  ∀ cH : ℝ, 0 < cH → ∃ (Cw₀ CHe Υe : ℝ), 0 ≤ Cw₀ ∧ 1 ≤ CHe ∧ 100 ≤ Υe ∧ ∀ Cw : ℝ, Cw₀ ≤ Cw →
    ∀ j₀ : ℕ, IsCarrierStart X.α X.q A.Λ A.bw CHe Υe j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      TermCertAtM A sXT sZT nW cr CL Cχ kW cP CP cH Cw j₀ M

theorem termReserve_nonneg {kW : InvConsts} (hGH : kW.G0 ≤ kW.Hprod) {c : Comp}
    (hc : compGrade c ≤ 1) : 0 ≤ compReserve kW c := by
  unfold compReserve
  have h1 : ((kW.G0 + compGrade c : ℕ) : ℝ) ≤ (kW.Hprod : ℝ) + 1 := by
    exact_mod_cast (by omega)
  have h2 : (0 : ℝ) < (kW.Hprod : ℝ) + 1 := by positivity
  have := (div_le_one h2).mpr h1
  linarith

/-- The components of the terminal successor of a weak stage (all grades `0`) have grade at most
`1`. -/
theorem termGrade_le_one {D : OCData} {j₀ : ℕ} {Dm : ℕ} {b : ℝ} {P : ProvParams} {Mn : SuccMenu}
    {G G' : GenStage D ScalarH Dm b j₀} (hG : ∀ v : CompIn G.comps, compGrade v.1 = 0)
    (hS : IsActualSuccessor D P Mn G G') : ∀ v : CompIn G'.comps, compGrade v.1 ≤ 1 := by
  obtain ⟨-, -, hc, -⟩ := hS
  rintro ⟨c, hv⟩
  rw [hc] at hv
  show compGrade c ≤ 1
  rcases Finset.mem_union.mp hv with h | h
  · have : compGrade c = 0 := hG ⟨c, h⟩
    omega
  · obtain ⟨⟨x, t⟩, hx, he⟩ := Finset.mem_image.mp h
    rw [← he]
    have hxG := hG ⟨x, (Finset.mem_product.mp hx).1⟩
    by_cases ht : t = []
    · subst ht
      rw [compGrade_succComp_nil]
      dsimp only at hxG ⊢
      omega
    · rw [compGrade_succComp_ne _ _ ht]
      dsimp only at hxG ⊢
      omega

end AVRegularity.EntryTerminal.Route
end
end

section
/-! **Proof of `TermCertBlock`** (see `Certified`). The threshold `Λ₀` collects those of the
scale constants and of the carrier calculus.

Special case: `c_r = 1`. -/

@[expose] public section

open Homogenization AVRegularity AVRegularity.Sobolev

namespace AVRegularity.EntryTerminal.Route

open AVRegularity.Providers.CascadeInvariants AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant
  AVRegularity.Providers.ComplexContext

theorem termCertBlock_exists (X : TermConstruction) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ (A : TermArgs X), Λ₀ ≤ A.Λ → ∀ (sXT sZT : ℕ) (nW : ℕ+) (cr : ℝ)
      (kW : InvConsts) (CL Cχ cP CP : ℝ),
      TermPlanHyp A sXT sZT nW cr kW → 0 < cr → cr ≤ 1 →
      TermCertBlock A sXT sZT nW cr CL Cχ kW cP CP := by
  obtain ⟨Λs, hΛs, hscS⟩ := termScaleConsts_stmt X
  obtain ⟨Λc, hΛc, hce⟩ := termChainEnv_stmt X
  obtain ⟨Λg, hΛg, hg2⟩ := AVRegularity.Providers.gen_carrier_calculus X.α X.s X.hα₀ X.hα₁ X.hs₀
    X.hs₁ X.q X.hq X.ζ X.hζ
  refine ⟨max Λs (max Λg Λc), le_max_of_le_left hΛs, fun A hA sXT sZT nW cr kW CL Cχ cP CP hP
    hcr0 hcr1 => ?_⟩
  have hAs : Λs ≤ A.Λ := (le_max_left _ _).trans hA
  have hAg : Λg ≤ A.Λ := ((le_max_left _ _).trans (le_max_right _ _)).trans hA
  have hAc : Λc ≤ A.Λ := ((le_max_right _ _).trans (le_max_right _ _)).trans hA
  have hb0 : 0 < A.bw := hP.valid.2.2.1.1
  have hb1 : A.bw ≤ 1 / 10000 := hP.valid.2.2.1.2
  obtain ⟨Cu, hCuC⟩ := hscS A hAs cr hcr0 hcr1
  obtain ⟨Υ₀, hΥ₀⟩ := hg2 A.Λ hAg A.bw hb0 hb1
  have hπ : 4 * (8 * Real.pi ^ 2) ≤ 400 := by
    have := Real.pi_lt_d2
    nlinarith [Real.pi_pos]
  have hCar : CarrierOK Υ₀ 1 (max Υ₀ 400) :=
    ⟨le_rfl, max_le_max le_rfl hπ⟩
  obtain ⟨κ, hκ, hcalcAll⟩ := hΥ₀ 1 (max Υ₀ 400) hCar
  obtain ⟨Ca, Cown, Cd, hCa, hCown, hdiag⟩ := hCuC.diag
  obtain ⟨thr1, h1⟩ := termLedgerBudget_stmt X A kW Cu κ hκ hb0 hCuC.hCu
  obtain ⟨thr2, h2⟩ := termDiagBudget_stmt X A kW Cu Ca Cown Cd κ hκ hb0 hCuC.hCu hCa hCown
  intro cH hcH
  have hΥ100 : 100 ≤ max Υ₀ 400 := le_max_of_le_right (by norm_num)
  refine ⟨max 0 (max thr1 thr2), 1, max Υ₀ 400, le_max_left _ _, le_rfl, hΥ100,
    fun Cw hCw j₀ hcs => ?_⟩
  have hCw1 : thr1 ≤ Cw := ((le_max_left _ _).trans (le_max_right _ _)).trans hCw
  have hCw2 : thr2 ≤ Cw := ((le_max_right _ _).trans (le_max_right _ _)).trans hCw
  obtain ⟨M₁, hM₁⟩ := termStepFacts_stmt X A sXT sZT nW cr kW hP CL Cχ Cu 1
    (max Υ₀ 400) j₀ hCuC le_rfl (by linarith) hcs
  refine ⟨max (max M₁ (j₀ + 1)) 2, fun M hM D a lawW PW Gw aM tp lawT Gt' hctx => ?_⟩
  have hM1 : M₁ ≤ M := ((le_max_left _ _).trans (le_max_left _ _)).trans hM
  have hMj : j₀ + 1 ≤ M := ((le_max_right _ _).trans (le_max_left _ _)).trans hM
  have hM2 : 2 ≤ M := (le_max_right _ _).trans hM
  have hstep := hM₁ M hM1 cP CP cH Cw D a lawW PW Gw aM tp lawT Gt' hctx
  have hfields := termMenuFields_stmt X A sXT sZT nW cr kW hP CL Cχ j₀ M hM2 cP CP cH
    Cw D a lawW PW Gw aM tp lawT Gt' hctx hcr0 hcr1
  have hdata := hctx.1
  have hw := hctx.2.1
  have hSucc := hctx.2.2.2.2.2.2
  have hlev : Gw.level = M := hw.2.2.1
  have hbirth : ∀ v : CompIn Gw.comps, v.1.births = [] := hw.2.2.2.2.1
  have hF := termMenuFacts_of_parts hstep hCuC hdata hM2 hlev hfields
  have hB := h1 (A.Pt D Cw cr M) (A.Mt M sXT sZT tp cr) rfl hCw1
  obtain ⟨eα, eq', eΛ, eζ, hΦ, hκb, eterm⟩ := hdata
  have hcs' : IsCarrierStart D.α D.q D.Λ A.bw 1 (max Υ₀ 400) j₀ := by
    rw [eα, eq', eΛ]; exact hcs
  have hd := hdiag M D ⟨eα, eq', eΛ, eζ, hΦ, hκb, eterm⟩ hM2
  have hown100 : ownSize D Gw.level ≤ 1 / 100 := by
    rw [hlev]
    exact AVRegularity.Providers.ComplexContext.ownSize_le_of_carrierStart (by omega) hb0 hb1 le_rfl hΥ100
      hcs' (by omega) (by omega)
  have hBd := h2 D j₀ Gw (A.Pt D Cw cr M) (A.Mt M sXT sZT tp cr) rfl rfl hcr0 hcr1 hown100
    (by rw [hlev]; exact hd.1) (by rw [hlev]; exact hd.2.1) (by rw [hlev]; exact hd.2.2) hCw2
  have hE := hce A hAc hb0 hb1 1 (max Υ₀ 400) j₀ le_rfl (by linarith) hcs M D
    ⟨eα, eq', eΛ, eζ, hΦ, hκb, eterm⟩
  have hGt : Gt'.level = M - 1 := by rw [hSucc.2.1, hlev]
  have hj : j₀ ≤ Gt'.level := by omega
  have hconcl := terminal_ledger_concl hF hB hBd hE hj hSucc
  have hres : ∀ v : CompIn Gt'.comps, 0 ≤ compReserve kW v.1 := fun v =>
    termReserve_nonneg hP.hGH (termGrade_le_one (fun u => by simp [compGrade, hbirth u]) hSucc v)
  have hcalc := hcalcAll j₀ hcs D eα eq' eΛ eζ hΦ M hκb eterm Gt'.level
  exact AVRegularity.GenStage.isContextCertified_of_gates Gt' kW κ
    (fun p hp Δ hΔ leaf hL e hsch hsf f hden =>
      hcalc p (by omega) hj hp Δ hΔ leaf hL e hsch hsf f hden)
    hres (fun v u γ => hconcl v u γ (hres v))

end AVRegularity.EntryTerminal.Route
end
end
end

section
section
/-! **The context-certified clause of the seed** (`seed.IsContextCertified kS`, the sixth
conjunct of `SeedCertAtM`), from the certificate of `Gt'` at `kW` (`termCertBlock_exists`), its
retained part (`IsContextCertified.retained`, `H = 1`, `J = R_T`) and the transport along the
re-rooting (`isContextCertified_seed_of_encoding`).

The reserves: a retained component has grade at most `1`, a seed component grade `0`; at `kS` its
reserve is `1 - kS.G0/(kS.Hprod + 1)`, at `kW` it is `1 - (kW.G0 + g)/(kW.Hprod + 1)`, and
`kW.G0 + 1 ≤ kS.G0`, `kW.Hprod = kS.Hprod`. The weight: `kS.Lstar ≤ kW.Lstar`.
No ledger hypothesis.

Special case: an empty retained family (vacuous). -/

@[expose] public section

open Homogenization AVRegularity AVRegularity.Sobolev

namespace AVRegularity.EntryTerminal.Route

open AVRegularity.Providers.CascadeInvariants AVRegularity.Providers.GenSem

/-- The context-certified clause of the seed at one level. -/
def SeedContextCertAtM {X : TermConstruction} (A : TermArgs X) (sXT sZT : ℕ) (nW : ℕ+) (cr : ℝ)
    (kS : InvConsts) (CL Cχ : ℝ) (kW : InvConsts) (cP CP cH Cw : ℝ) (j₀ M : ℕ) : Prop :=
  ∀ (D : OCData) (a : ℝ) (lawW : BirthLaw) (PW : ProvParams) (Gw : GenStage D ScalarH A.Dt A.bw j₀)
    (aM tp : ℝ) (lawT : BirthLaw) (Gt' : GenStage D ScalarH A.Dt A.bw j₀)
    (seed : GenStage D ScalarH A.Ds A.bw j₀) (rootM rootR : ℕ → ℝ) (seedKc : ℕ → KernelSpec)
    (ι : CompIn (Gt'.retained M 1 A.RT).comps ≃ CompIn seed.comps),
    SeedCtx A sXT sZT nW cr CL Cχ kW cP CP cH Cw M D a lawW PW Gw aM tp lawT Gt' seed rootM rootR
      seedKc ι → seed.IsContextCertified kS

/-- The block of `SeedContextCertAtM`, in the shape of `SeedCertBlock`. -/
def SeedContextCertBlock {X : TermConstruction} (A : TermArgs X) (sXT sZT : ℕ) (nW : ℕ+) (cr : ℝ)
    (kS : InvConsts) (CL Cχ : ℝ) (kW : InvConsts) (cP CP : ℝ) : Prop :=
  ∀ cH : ℝ, 0 < cH → ∃ (Cw₀ CHe Υe : ℝ), 0 ≤ Cw₀ ∧ 1 ≤ CHe ∧ 100 ≤ Υe ∧ ∀ Cw : ℝ, Cw₀ ≤ Cw →
    ∀ j₀ : ℕ, IsCarrierStart X.α X.q A.Λ A.bw CHe Υe j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      SeedContextCertAtM A sXT sZT nW cr kS CL Cχ kW cP CP cH Cw j₀ M

theorem seedContextCertBlock_exists (X : TermConstruction) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ (A : TermArgs X), Λ₀ ≤ A.Λ → ∀ (sXT sZT : ℕ) (nW : ℕ+) (cr : ℝ)
      (kS kW : InvConsts) (Lt KS : ℕ) (F : SeedFloors) (CL Cχ cP CP : ℝ),
      A.Valid → 128 ≤ A.Λ → SeedPlan A KS F Lt nW cr kS → IsWeakAllocation kW kS Lt →
      max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sXT →
      max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sZT → 0 < cr → cr ≤ 1 →
      SeedContextCertBlock A sXT sZT nW cr kS CL Cχ kW cP CP := by
  obtain ⟨Λ₀, hΛ₀, hblock⟩ := termCertBlock_exists X
  refine ⟨Λ₀, hΛ₀, fun A hA sXT sZT nW cr kS kW Lt KS F CL Cχ cP CP hvalid hΛA hplan halloc hsX hsZ hcr0 hcr1 cH hcH => ?_⟩
  have hP := termPlanHyp_of_plan hvalid hΛA hplan halloc hsX hsZ
  obtain ⟨Cw₀, CHe, Υe, h0, hCHe, hΥe, hrest⟩ :=
    hblock A hA sXT sZT nW cr kW CL Cχ cP CP hP hcr0 hcr1 cH hcH
  refine ⟨Cw₀, CHe, Υe, h0, hCHe, hΥe, fun Cw hCw j₀ hcs => ?_⟩
  obtain ⟨M₀, hM₀⟩ := hrest Cw hCw j₀ hcs
  refine ⟨M₀, fun M hM D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx => ?_⟩
  have hcert := hM₀ M hM D a lawW PW Gw aM tp lawT Gt' (TermPassCtx.of_seedCtx hctx)
  have hret := (hcert.retained M 1 A.RT).2
  obtain ⟨hdata, -, -, -, -, -, -, henc, hexp, -, -⟩ := hctx
  obtain ⟨-, -, -, -, hLst, hG0, hH, -⟩ := halloc
  have hΛ1 : 1 ≤ D.Λ := by
    have h1 := hdata.2.2.1
    have h2 := hP.hΛ
    omega
  have hb0 : 0 ≤ A.bw := hP.valid.2.2.1.1.le
  refine AVRegularity.GenStage.isContextCertified_seed_of_encoding henc hexp hret (fun v => ?_) hLst
    (fun k => (Construction.Stream.ocEpsilon_pos hΛ1).le) hb0
  have hv : compGrade v.1 ≤ 1 := (Finset.mem_filter.mp v.2).2.1
  have h0 : compGrade (ι v).1 = 0 := by simp [compGrade, henc.2.1 v]
  unfold compReserve
  rw [h0, ← hH]
  have hH0 : (0 : ℝ) < (kW.Hprod : ℝ) + 1 := by positivity
  have hle : ((kW.G0 + compGrade v.1 : ℕ) : ℝ) ≤ ((kS.G0 + 0 : ℕ) : ℝ) := by
    exact_mod_cast (by omega)
  have := div_le_div_of_nonneg_right hle hH0.le
  linarith

end AVRegularity.EntryTerminal.Route
end
end

section
/-! **`SeedCertPart` is proved.** At a level, the eight conjuncts of
`SeedCertAtM` come from the following.
- Naturalness, tags, exports: the actual successor `Gt'` is natural at the menu's level `M + J_w`
  and tagged at `A.Pt`, and it has the exports of the weak stage (`IsActualSuccessor`).
- Generatedness and slotwise transversality: the slot-transversality and generation statement at terminal entry
  (`terminalSuccessor_generation`).
- Shift invariance: `successor_shift_invariant_of_cellScaleSq_nonneg`, from the weak invariant.
- These five restrict to the retained family and pass to the seed along the encoding
  (`SeedConjuncts.lean`).
- The context certificate is `seedContextCertBlock_exists`.
- The exports clause and `Above (M−1)`: the seed's exports are those of `Gw` (the encoding keeps
  the registry, the successor keeps the exports), and `Gw.HasCertifiedExports M` holds by the weak
  stage.

The block takes the constants of the context certificate (`C_{w,0}`, the carrier pair with `Υ ≥ 100`). The floors on
`s_X, s_Z` are those of `terminalSuccessor_generation` and the context certificate.

Special cases: an empty retained family (the seed is empty; every clause is vacuous); `R_T = 0`. -/

@[expose] public noncomputable section

open Homogenization AVRegularity AVRegularity.Sobolev

namespace AVRegularity.EntryTerminal.Route

open AVRegularity.EntryTerminal.Ingredients

/-- **The certification of the seed at one level**, given the context certificate. -/
theorem seedCertAtM_of {X : TermConstruction} {A : TermArgs X} {sXT sZT : ℕ} {nW : ℕ+} {cr : ℝ}
    {kS : InvConsts} {CL Cχ : ℝ} {kW : InvConsts} {cP CP cH Cw : ℝ} {j₀ M : ℕ}
    (hA : A.Valid) (hΛ : 128 ≤ A.Λ) {CH Υ : ℝ} (hCH : 1 ≤ CH) (hΥ : 1 ≤ Υ)
    (hcar : IsCarrierStart X.α X.q A.Λ A.bw CH Υ j₀)
    (hX : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sXT)
    (hZ : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sZT) (hcr0 : 0 < cr)
    (hcert : SeedContextCertAtM A sXT sZT nW cr kS CL Cχ kW cP CP cH Cw j₀ M) :
    SeedCertAtM A sXT sZT nW cr kS CL Cχ kW cP CP cH Cw j₀ M := by
  intro D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx
  have hcertS := hcert D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx
  obtain ⟨hD, hW, -, -, -, -, hsucc, henc, hexp, -, -⟩ := hctx
  obtain ⟨hα, hq, hΛD, hζD, -, hband, hterm⟩ := hD
  have hN : 2 ≤ A.NT := two_le_NT_of_valid A hA
  have hDW : 1 ≤ A.DW := hA.2.2.2.2.2.2.2.2
  have hb : 0 < A.bw := hA.2.2.1.1
  have hΛ1 : 1 ≤ D.Λ := by rw [hΛD]; omega
  have hζ : IsFastProfile D.ζ := by rw [hζD]; exact X.hζ
  have hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    rw [hα, hq, hΛD, hζD, hterm]; exact hband
  have hcar' : IsCarrierStart D.α D.q D.Λ A.bw CH Υ j₀ := by rw [hα, hq, hΛD]; exact hcar
  have hgate := Providers.GenSem.terminalSuccessor_generation hΛ1 hζ hκ hb hCH hΥ hcar' hterm hW
    hN hDW hcr0.ne' hX hZ hsucc
  have hcs : 0 ≤ D.cellScaleSq Gw.level :=
    (EntryWeakProofs.weakData_cellScaleSq_pos D hΛ1 hζ hκ _).le
  have hexpW : Gw.HasCertifiedExports M := hW.2.2.2.2.2.1.2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, hinv⟩ := hW
  obtain ⟨hnat, -, -, hsh, -⟩ := hinv
  have hshT : Gt'.IsShiftInvariant :=
    Construction.Preservation.FullLift.successor_shift_invariant_of_cellScaleSq_nonneg hζ hcs
      hnat hsh hsucc
  obtain ⟨-, -, -, hnatT, htagsT, hexpT, -⟩ := hsucc
  have hS := Finset.filter_subset (IsRetained M 1 A.RT) Gt'.comps
  refine ⟨seed_isNatural_of_encoding henc (seedCert_isNatural_restrict hnatT _ hS),
    seed_hasTags_of_encoding henc (seedCert_hasTags_restrict htagsT _ hS),
    seed_isGenerated_of_encoding henc hexp
      (seedCert_isGenerated_restrict (isGenerated_of_exprFor hgate.1) _ hS),
    seed_isShiftInvariant_of_encoding henc (hshT.restrict _ hS),
    seed_isSlotTransverse_of_encoding henc (hgate.2.restrict _ hS), hcertS, ?_, ?_⟩
  · intro i p e hse
    exact hexpW.1 i p e ((hexpT i p e).1 ((hexp i p e).1 hse))
  · intro i p e hse
    have := hexpW.2 e ((hexpT i p e).1 ((hexp i p e).1 hse))
    omega

/-- **The certification of the seed.** -/
theorem seedCertPart : SeedCertPart := by
  intro X
  obtain ⟨Λ₀, h128, hblock⟩ := seedContextCertBlock_exists X
  refine ⟨Λ₀, h128, fun A hΛ hA Kout => ⟨max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2,
    max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2, fun sXT sZT hX hZ => ⟨0, seedStructFloors,
    fun Lt nW cr kS hplan cK CL Cχ kW _ _ hwa cP CP _ => ?_⟩⟩⟩
  have hΛA : 128 ≤ A.Λ := le_trans h128 hΛ
  have hcr0 : 0 < cr := hplan.2.2.2.2.1
  have hcr1 : cr ≤ 1 := hplan.2.2.2.2.2.1
  have hB := hblock A hΛ sXT sZT nW cr kS kW Lt 0 seedStructFloors CL Cχ cP CP hA hΛA hplan hwa
    hX hZ hcr0 hcr1
  intro cH hcH
  obtain ⟨Cw₀, CHe, Υe, h0, hCHe, hΥe, hrest⟩ := hB cH hcH
  refine ⟨Cw₀, CHe, Υe, h0, hCHe, lt_of_lt_of_le (by norm_num) hΥe, fun Cw hCw j₀ hj₀ => ?_⟩
  obtain ⟨M₀, hM₀⟩ := hrest Cw hCw j₀ hj₀
  exact ⟨M₀, fun M hM => seedCertAtM_of hA hΛA hCHe (le_trans (by norm_num) hΥe) hj₀ hX hZ hcr0
    (hM₀ M hM)⟩

end AVRegularity.EntryTerminal.Route
end
end
end
