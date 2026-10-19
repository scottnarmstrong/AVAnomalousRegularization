-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.Ledger.TaggedRecurrence
public import AVRegularity.EntryTerminal.Ingredients.Frontier.InnerStatements
public import AVRegularity.EntryTerminal.Assembly.Seed.RetainedGeneric
import AVRegularity.Construction.StageEnvelopes.SuccessorPreparation
import AVRegularity.Construction.Preservation.FullLift.FactorialWordEnergySum
public import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.Construction.Scales.Times

@[expose] public noncomputable section

section
open Homogenization
namespace AVRegularity.Construction.Preservation.Ledger

/-! **The marked-ledger recurrence for generic provenance parameters.**

`full_tagged_ledger_recurrence` and `tagged_ledger_recurrence` are stated for the cascade's
`succProvParams` and `IsSuccessorLaw`. The proof reads the law only through (i) `1 ≤` the birth
diagonal factor and (ii) the bound of the fresh-letter prefactor, and the provenance parameters only
through `source_record_price_le`. Here both are hypotheses, with `genProvParams` and
`source_record_price_le_gen`, so that the terminal passage (law `IsTerminalLaw`, parameters
`termProvParams`) is an instance.

For `S = 0` the old ledger vanishes and the bound is the fresh part. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {G G' : GenStage D hr Dm bw j₀}

/-- **The recurrence of the marked ledger, generically**: the retained family of the actual
successor has marked ledger at most `|W|(4 C_w S + 2 L C_w R)`, enlarged as in `menu_bound_le`. -/
theorem retained_ledger_recurrence_gen {Cw η σ R S : ℝ} {N p d H J : ℕ} {Rb rb : ℕ → ℝ}
    {Mn : SuccMenu} (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hCw : 0 ≤ Cw) (hσ : 0 ≤ σ)
    (hrb : rb (G.level - 1) = Rb (G.level - 1) * D.eps (G.level - 1) ^ σ)
    (hletters : ∀ l ∈ Mn.A, letterOrder N p l - 2 ≤ d) (law : BirthLaw)
    (hF1 : ∀ marked, 1 ≤ birthDiagonalFactor D.q D.Λ G.level law marked)
    (hbirth : ∀ marked, birthDiagonalFactor D.q D.Λ G.level law marked *
      D.eps (G.level - 1) ^ (ocDelta D.α D.q - η - σ * (d : ℝ)) ≤ R)
    (hG : G.HasTags (genProvParams D Cw η N p Rb rb))
    (hold : ∀ v ∈ G.comps, ∀ e ∈ v.births, G.level ≤ e.scale)
    (hs : IsActualSuccessor D (genProvParams D Cw η N p Rb rb) Mn G G')
    (hS : 0 ≤ S) (hledger : markedLedger (G.mass law) (G.marker law) G.fam ≤ S)
    (hsmall : Assembly.ledgerTransportConstant Cw (wordsUpTo Mn.A (Mn.J + 1)).card * S ≤ 1 / 2) :
    markedLedger ((G'.retained G.level H J).mass law) ((G'.retained G.level H J).marker law)
        (G'.retained G.level H J).fam ≤
      4 * (((wordsUpTo Mn.A (Mn.J + 1)).card : ℝ) + 1) * (Cw + 1) * S +
        2 * (((wordsUpTo Mn.A (Mn.J + 1)).card : ℝ) + 1) * ((Mn.A.card : ℝ) + 1) * (Cw + 1) * R := by
  classical
  have hCw0 : 0 ≤ Cw := hCw
  have hqD : 1 < D.q := hq
  have he := Scales.epsilon_basic (m := G.level - 1) hqD hΛ
  have hA : 1 ≤ Assembly.ledgerTransportConstant Cw (wordsUpTo Mn.A (Mn.J + 1)).card := by
    unfold Assembly.ledgerTransportConstant
    have ht : 0 ≤ ((wordsUpTo Mn.A (Mn.J + 1)).card : ℝ) := Nat.cast_nonneg _
    nlinarith only [hCw, ht]
  have hhalf : S ≤ 1 / 2 := (le_mul_of_one_le_left hS hA).trans hsmall
  let E := Classical.choice (actual_sources hs)
  let B : ℝ := 4 * (((wordsUpTo Mn.A (Mn.J + 1)).card : ℝ) + 1) * (Cw + 1) * S +
    2 * (((wordsUpTo Mn.A (Mn.J + 1)).card : ℝ) + 1) * ((Mn.A.card : ℝ) + 1) * (Cw + 1) * R
  have hbound (marked : Bool) :
      fullLedger (pricedRecordMajorant (G'.mass law)
        (fun c => ledgerMarker D.q D.Λ law marked c.1) G'.fam) ≤ B := by
    let a := ledgerDiagonal D.q D.Λ law marked
    let F := birthDiagonalFactor D.q D.Λ G.level law marked
    let Ffresh := F * D.eps (G.level - 1) ^ (ocDelta D.α D.q - η - σ * (d : ℝ))
    have ha : ∀ v ∈ G.comps, 0 < a v := fun v _ => ledgerDiagonal_pos hqD hΛ law marked v
    have hF : 1 ≤ F := hF1 marked
    have hF0 : 0 ≤ Ffresh := mul_nonneg (le_trans zero_le_one hF) (Real.rpow_nonneg he.1.le _)
    have hFR : Ffresh ≤ R := hbirth marked
    let c := identityPrice G a
    have hc : ∀ e, 0 ≤ c e := identityPrice_nonneg G a ha
    have hrowcol : SchurBound S (fun v u => ∑ γ, c ⟨v, u, γ⟩) := by
      have hh : fullLedger (pricedRecordMajorant (G.mass law)
          (fun c => ledgerMarker D.q D.Λ law marked c.1) G.fam) ≤ S := by
        cases marked with
        | false => exact (le_max_left _ _).trans hledger
        | true => exact (le_max_right _ _).trans hledger
      have hb := FullLift.fullLedger_schur_bound (pricedRecordMajorant (G.mass law)
        (fun c => ledgerMarker D.q D.Λ law marked c.1) G.fam)
      simpa only [c, a, sum_identityPrice_eq hqD hΛ law marked] using
        (show SchurBound S (pricedRecordMajorant (G.mass law)
          (fun c => ledgerMarker D.q D.Λ law marked c.1) G.fam) from
            ⟨fun v => (hb.1 v).trans hh, fun u => (hb.2 u).trans hh⟩)
    have hcost (e : LedgerEdge G') : identityPrice G' a e ≤ sourcePrice Cw Ffresh c (E.source e) := by
      have hratio := source_diagonal_ratio_le a ha hF
        (fun v hv t => ledgerDiagonal_succComp hqD hΛ hs.1 law marked v (hold v hv) t)
        (E.source e) (source_old_mem (E.source e) (E.valid e))
      rw [E.tgt e, E.src e] at hratio
      have hh := source_record_price_le_gen a ha hCw he.1 he.2.1 hσ (le_trans zero_le_one hF)
        rfl hrb hletters hG (E.source e) (E.valid e) (G'.fam.identity e.1 e.2.1 e.2.2).record
        (E.tags e) e.2.1.1.root e.1.1.root (a e.1.1 / a e.2.1.1) hratio
      simpa only [identityPrice, E.map_eq e, Ffresh, c, OCData.eps] using hh
    have hschur := actual_diagonal_schur hs hold a Cw Ffresh hCw hF0 c hc hS hhalf
      hrowcol.1 hrowcol.2 E hcost
    have hmenu := menu_bound_le (L := Mn.A.card) (Finset.card_insert_le [] (wordsUpTo Mn.A (Mn.J + 1)))
      hCw hS hF0 hFR
    have hmenu' : ((insert [] (wordsUpTo Mn.A (Mn.J + 1))).card : ℝ) *
        (4 * Cw * S + 2 * (Mn.A.card : ℝ) * Cw * Ffresh) ≤ B := hmenu
    have hR0 : 0 ≤ R := hF0.trans hFR
    have hB : 0 ≤ B := by
      dsimp only [B]
      positivity
    apply diagonal_fullLedger_le hqD hΛ law marked hB
    exact ⟨fun v => (hschur.1 v).trans hmenu', fun u => (hschur.2 u).trans hmenu'⟩
  have hbound' (marked : Bool) :
      fullLedger (pricedRecordMajorant ((G'.retained G.level H J).mass law)
        (fun c => ledgerMarker D.q D.Λ law marked c.1) (G'.retained G.level H J).fam) ≤ B := by
    have hh : fullLedger (pricedRecordMajorant (G'.mass law)
        (fun c => ledgerMarker D.q D.Λ law marked c.1) G'.fam) ≤ B := hbound marked
    have hR0 : 0 ≤ R := by
      have hF := hF1 marked
      have hF0 : 0 ≤ birthDiagonalFactor D.q D.Λ G.level law marked *
          D.eps (G.level - 1) ^ (ocDelta D.α D.q - η - σ * (d : ℝ)) :=
        mul_nonneg (le_trans zero_le_one hF) (Real.rpow_nonneg he.1.le _)
      exact hF0.trans (hbirth marked)
    have hB : 0 ≤ B := by
      dsimp only [B]
      positivity
    have hb := FullLift.fullLedger_schur_bound (pricedRecordMajorant (G'.mass law)
      (fun c => ledgerMarker D.q D.Λ law marked c.1) G'.fam)
    have hschur : SchurBound B (fun v u => ∑ γ,
        identityPrice G' (ledgerDiagonal D.q D.Λ law marked) ⟨v, u, γ⟩) := by
      simpa only [sum_identityPrice_eq hqD hΛ law marked] using
        (show SchurBound B (pricedRecordMajorant (G'.mass law)
          (fun c => ledgerMarker D.q D.Λ law marked c.1) G'.fam) from
          ⟨fun v => (hb.1 v).trans hh, fun u => (hb.2 u).trans hh⟩)
    apply diagonal_fullLedger_le hqD hΛ law marked hB
    exact restrict_diagonal_schur G' (ledgerDiagonal D.q D.Λ law marked)
      (fun v _ => ledgerDiagonal_pos hqD hΛ law marked v)
      _ (Finset.filter_subset _ _) hschur
  exact max_le (hbound' false) (hbound' true)

end AVRegularity.Construction.Preservation.Ledger
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.StageEnvelopes
namespace AVRegularity.EntryTerminal.Route

/-! **The split of `SeedEnvelopePart`** (part 4 of the seed clauses). At one level, under the
context `SeedCtx` and the seed's naturalness and context certificate, the clauses of
`SeedEnvelopeAtM` come from four pieces:
- `SeedSampledAtM`: the sampled coefficient bound of the seed;
- `SeedLedgerAtM`: the marked ledger `≤ C_e ε_{M-1}^{τ_e}`;
- `SeedSchurAtM`: the kernel Schur bound;
- `SeedEnvInputAtM`: an envelope estimate whose input holds at the seed, with its level floor
  below the seed's level and its constants below `k_S.C_a`, `k_S.C_m`.

The two envelopes and the pointwise molecular envelope follow from the input and the
ledger by `stage_envelopes_with_ledger_of_context` (`seedEnvelopeAtM_of_pieces`). The prefixes and
the per-level blocks combine by maxima (`SeedPartPrefix.and`, `SeedLevelBlock.and`).

For an empty seed every piece is vacuous or trivial and the ledger is `0`. -/

/-- The block shape of a per-level statement `Q c_H C_w C_e j₀ M` of the seed side: the carrier
pair and the floor of `C_e` after `c_H, C_w`, the level threshold after `C_e` and `j₀`. -/
def SeedLevelBlock {X : TermConstruction} (A : TermArgs X) (Q : ℝ → ℝ → ℝ → ℕ → ℕ → Prop) : Prop :=
  ∀ cH Cw : ℝ, 0 < cH → 0 ≤ Cw → ∃ (Ce₀ CHe Υe : ℝ), 1 ≤ CHe ∧ 0 < Υe ∧ ∀ Ce : ℝ, Ce₀ ≤ Ce →
    ∀ j₀ : ℕ, IsCarrierStart X.α X.q A.Λ A.bw CHe Υe j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      Q cH Cw Ce j₀ M

/-- Two per-level blocks combine by maxima. -/
theorem SeedLevelBlock.and {X : TermConstruction} {A : TermArgs X} {Q₁ Q₂ : ℝ → ℝ → ℝ → ℕ → ℕ → Prop}
    (hΛ : 1 ≤ A.Λ) (h₁ : SeedLevelBlock A Q₁) (h₂ : SeedLevelBlock A Q₂) :
    SeedLevelBlock A fun cH Cw Ce j₀ M => Q₁ cH Cw Ce j₀ M ∧ Q₂ cH Cw Ce j₀ M := by
  have hAnn : ∀ k, 0 ≤ ocA X.α X.q A.Λ k :=
    fun _ => Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ).le _
  have hTnn : ∀ k, 0 ≤ ocTauPP X.α X.q A.Λ k := fun _ => (Construction.Stream.ocTauPP_pos hΛ).le
  intro cH Cw hcH hCw
  obtain ⟨C₁, CH₁, Υ₁, hCH₁, hΥ₁, h₁⟩ := h₁ cH Cw hcH hCw
  obtain ⟨C₂, CH₂, Υ₂, hCH₂, hΥ₂, h₂⟩ := h₂ cH Cw hcH hCw
  refine ⟨max C₁ C₂, max CH₁ CH₂, max Υ₁ Υ₂, le_trans hCH₁ (le_max_left _ _),
    lt_of_lt_of_le hΥ₁ (le_max_left _ _), fun Ce hCe j₀ hj₀ => ?_⟩
  obtain ⟨M₁, h₁⟩ := h₁ Ce (le_trans (le_max_left _ _) hCe) j₀
    (IsCarrierStart.mono hAnn hTnn (le_max_left _ _) (le_max_left _ _) (zero_le_one.trans hCH₁)
      hΥ₁.le hj₀)
  obtain ⟨M₂, h₂⟩ := h₂ Ce (le_trans (le_max_right _ _) hCe) j₀
    (IsCarrierStart.mono hAnn hTnn (le_max_right _ _) (le_max_right _ _) (zero_le_one.trans hCH₂)
      hΥ₂.le hj₀)
  exact ⟨max M₁ M₂, fun M hM =>
    ⟨h₁ M (le_trans (le_max_left _ _) hM), h₂ M (le_trans (le_max_right _ _) hM)⟩⟩

/-- A per-level block is monotone in its statement. -/
theorem SeedLevelBlock.mono {X : TermConstruction} {A : TermArgs X} {Q₁ Q₂ : ℝ → ℝ → ℝ → ℕ → ℕ → Prop}
    (hQ : ∀ cH Cw Ce j₀ M, Q₁ cH Cw Ce j₀ M → Q₂ cH Cw Ce j₀ M) (h : SeedLevelBlock A Q₁) :
    SeedLevelBlock A Q₂ := by
  intro cH Cw hcH hCw
  obtain ⟨Ce₀, CHe, Υe, hCHe, hΥe, h⟩ := h cH Cw hcH hCw
  refine ⟨Ce₀, CHe, Υe, hCHe, hΥe, fun Ce hCe j₀ hj₀ => ?_⟩
  obtain ⟨M₀, h⟩ := h Ce hCe j₀ hj₀
  exact ⟨M₀, fun M hM => hQ _ _ _ _ _ (h M hM)⟩

/-- Two part prefixes combine: maxima of the lift floors, the reserve floors and the constant
floors (`SeedFloors.sup`). -/
theorem SeedPartPrefix.and {B₁ B₂ : (X : TermConstruction) → TermArgs X → ℕ → ℕ → ℕ → ℕ → ℕ+ → ℝ →
      InvConsts → ℝ → ℝ → InvConsts → ℝ → ℝ → Prop}
    (h₁ : SeedPartPrefix B₁) (h₂ : SeedPartPrefix B₂) :
    SeedPartPrefix fun X A Kout sXT sZT Lt nW cr kS CL Cχ kW cP CP =>
      B₁ X A Kout sXT sZT Lt nW cr kS CL Cχ kW cP CP ∧
        B₂ X A Kout sXT sZT Lt nW cr kS CL Cχ kW cP CP := by
  intro X
  obtain ⟨Λ₁, hΛ₁, h₁⟩ := h₁ X
  obtain ⟨Λ₂, -, h₂⟩ := h₂ X
  refine ⟨max Λ₁ Λ₂, le_trans hΛ₁ (le_max_left _ _), fun A hΛ hA Kout => ?_⟩
  obtain ⟨SX₁, SZ₁, h₁⟩ := h₁ A (le_trans (le_max_left _ _) hΛ) hA Kout
  obtain ⟨SX₂, SZ₂, h₂⟩ := h₂ A (le_trans (le_max_right _ _) hΛ) hA Kout
  refine ⟨max SX₁ SX₂, max SZ₁ SZ₂, fun sXT sZT hX hZ => ?_⟩
  obtain ⟨KS₁, F₁, h₁⟩ := h₁ sXT sZT (le_trans (le_max_left _ _) hX) (le_trans (le_max_left _ _) hZ)
  obtain ⟨KS₂, F₂, h₂⟩ := h₂ sXT sZT (le_trans (le_max_right _ _) hX)
    (le_trans (le_max_right _ _) hZ)
  exact ⟨max KS₁ KS₂, F₁.sup F₂, fun Lt nW cr kS hplan cK CL Cχ kW hcK hkW hwa cP CP hcP =>
    ⟨h₁ Lt nW cr kS (hplan.weaken (le_max_left _ _) fun h => h.left) cK CL Cχ kW hcK hkW hwa cP CP
      hcP,
    h₂ Lt nW cr kS (hplan.weaken (le_max_right _ _) fun h => h.right) cK CL Cχ kW hcK hkW hwa cP CP
      hcP⟩⟩

/-- A part prefix is monotone in its block, given `128 ≤ Λ`. -/
theorem SeedPartPrefix.mono {B₁ B₂ : (X : TermConstruction) → TermArgs X → ℕ → ℕ → ℕ → ℕ → ℕ+ → ℝ →
      InvConsts → ℝ → ℝ → InvConsts → ℝ → ℝ → Prop}
    (hB : ∀ (X : TermConstruction) (A : TermArgs X), 128 ≤ A.Λ →
      ∀ Kout sXT sZT Lt nW cr kS CL Cχ kW cP CP,
      B₁ X A Kout sXT sZT Lt nW cr kS CL Cχ kW cP CP → B₂ X A Kout sXT sZT Lt nW cr kS CL Cχ kW cP CP)
    (h : SeedPartPrefix B₁) : SeedPartPrefix B₂ := by
  intro X
  obtain ⟨Λ₀, hΛ₀, h⟩ := h X
  refine ⟨Λ₀, hΛ₀, fun A hΛ hA Kout => ?_⟩
  obtain ⟨SX, SZ, h⟩ := h A hΛ hA Kout
  refine ⟨SX, SZ, fun sXT sZT hX hZ => ?_⟩
  obtain ⟨KS, F, h⟩ := h sXT sZT hX hZ
  exact ⟨KS, F, fun Lt nW cr kS hplan cK CL Cχ kW hcK hkW hwa cP CP hcP =>
    hB X A (le_trans hΛ₀ hΛ) _ _ _ _ _ _ _ _ _ _ _ _
      (h Lt nW cr kS hplan cK CL Cχ kW hcK hkW hwa cP CP hcP)⟩

/-- **The sampled bound at one level: the sampled coefficient bound of the seed.** -/
def SeedSampledAtM {X : TermConstruction} (A : TermArgs X) (sXT sZT : ℕ) (nW : ℕ+) (cr : ℝ)
    (kS : InvConsts) (CL Cχ : ℝ) (kW : InvConsts) (cP CP cH Cw Ce : ℝ) (j₀ M : ℕ) : Prop :=
  ∀ (D : OCData) (a : ℝ) (lawW : BirthLaw) (PW : ProvParams) (Gw : GenStage D ScalarH A.Dt A.bw j₀)
    (aM tp : ℝ) (lawT : BirthLaw) (Gt' : GenStage D ScalarH A.Dt A.bw j₀)
    (seed : GenStage D ScalarH A.Ds A.bw j₀) (rootM rootR : ℕ → ℝ) (seedKc : ℕ → KernelSpec)
    (ι : CompIn (Gt'.retained M 1 A.RT).comps ≃ CompIn seed.comps),
    SeedCtx A sXT sZT nW cr CL Cχ kW cP CP cH Cw M D a lawW PW Gw aM tp lawT Gt' seed rootM rootR
      seedKc ι →
    seed.IsNatural (M + A.Jw) → seed.IsContextCertified kS →
    ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ D.eps (M - 1) → ∀ k ≤ kS.Ks, ∀ v u (γ : seed.fam.Γ v u) (d : ℕ), 2 ≤ d →
      d ≤ (seed.fam.identity v u γ).maxOrder →
      coefficientSeminorm ϱ k (tp + D.termH M) (a + A.T₀) (seed.physCoeff v u γ d) ≤
        ENNReal.ofReal (Ce * (seed.fam.identity v u γ).record.size * D.κ (M - 1) *
          (seed.fam.identity v u γ).record.length ^ (d - 2))

/-- **The marked ledger at one level: the marked ledger of the seed.** -/
def SeedLedgerAtM {X : TermConstruction} (A : TermArgs X) (sXT sZT : ℕ) (nW : ℕ+) (cr : ℝ)
    (kS : InvConsts) (CL Cχ : ℝ) (kW : InvConsts) (cP CP cH Cw Ce : ℝ) (j₀ M : ℕ) : Prop :=
  ∀ (D : OCData) (a : ℝ) (lawW : BirthLaw) (PW : ProvParams) (Gw : GenStage D ScalarH A.Dt A.bw j₀)
    (aM tp : ℝ) (lawT : BirthLaw) (Gt' : GenStage D ScalarH A.Dt A.bw j₀)
    (seed : GenStage D ScalarH A.Ds A.bw j₀) (rootM rootR : ℕ → ℝ) (seedKc : ℕ → KernelSpec)
    (ι : CompIn (Gt'.retained M 1 A.RT).comps ≃ CompIn seed.comps),
    SeedCtx A sXT sZT nW cr CL Cχ kW cP CP cH Cw M D a lawW PW Gw aM tp lawT Gt' seed rootM rootR
      seedKc ι →
    seed.IsNatural (M + A.Jw) → seed.IsContextCertified kS →
    ∀ law : BirthLaw, law.rootMass = rootM → law.rootReadout = rootR →
      markedLedger (seed.mass law) (seed.marker law) seed.fam ≤ Ce * D.eps (M - 1) ^ A.τe

/-- **The Schur bound at one level: the kernel Schur bound of the seed.** -/
def SeedSchurAtM {X : TermConstruction} (A : TermArgs X) (sXT sZT : ℕ) (nW : ℕ+) (cr : ℝ)
    (kS : InvConsts) (CL Cχ : ℝ) (kW : InvConsts) (cP CP cH Cw Ce : ℝ) (j₀ M : ℕ) : Prop :=
  ∀ (D : OCData) (a : ℝ) (lawW : BirthLaw) (PW : ProvParams) (Gw : GenStage D ScalarH A.Dt A.bw j₀)
    (aM tp : ℝ) (lawT : BirthLaw) (Gt' : GenStage D ScalarH A.Dt A.bw j₀)
    (seed : GenStage D ScalarH A.Ds A.bw j₀) (rootM rootR : ℕ → ℝ) (seedKc : ℕ → KernelSpec)
    (ι : CompIn (Gt'.retained M 1 A.RT).comps ≃ CompIn seed.comps),
    SeedCtx A sXT sZT nW cr CL Cχ kW cP CP cH Cw M D a lawW PW Gw aM tp lawT Gt' seed rootM rootR
      seedKc ι →
    seed.IsNatural (M + A.Jw) → seed.IsContextCertified kS →
    ∀ law : BirthLaw, law.rootMass = rootM → law.rootReadout = rootR →
    ∀ (P : ProvParams) (freshK : ℕ → KernelSpec), ∀ kk ≤ kS.Ks, ∀ w : CompIn seed.comps → ℝ,
      (w = fun _ => 1) ∨ w = seed.marker law →
      SchurBound (Ce * D.eps (M - 1 - 1) ^ (D.q * A.τe))
        (kernelSchurMatrix (ι := CompIn seed.comps) (h := fun v => ScalarH v.1.root)
          (Γ := seed.fam.Γ) (G := fun _ u _ => ScalarH u.1.root) (D.kap seed.level)
          (rhoStar D kS.c₀ seed.level) (fun v => seed.mass law v / w v ^ 2) kk A.Ds
          (tp + D.termH M) (a + A.T₀) kS.cker
          (fun v u γ => (seed.kernelOf P seedKc freshK v u γ).width)
          (fun _ u _ => ContinuousLinearMap.id ℝ (ScalarH u.1.root))
          (fun v u γ d => seed.physCoeff v u γ d.1))

/-- **The envelope input at one level**: an envelope estimate whose input holds at the seed (with
the inner reserve `k_S.m_env` and the radius `ρ_* = rhoStar c₀`), whose level floor is below the
seed's level and whose constants are below `k_S.C_a`, `k_S.C_m`. -/
def SeedEnvInputAtM {X : TermConstruction} (A : TermArgs X) (sXT sZT : ℕ) (nW : ℕ+) (cr : ℝ)
    (kS : InvConsts) (CL Cχ : ℝ) (kW : InvConsts) (cP CP cH Cw : ℝ) (j₀ M : ℕ) : Prop :=
  ∀ (D : OCData) (a : ℝ) (lawW : BirthLaw) (PW : ProvParams) (Gw : GenStage D ScalarH A.Dt A.bw j₀)
    (aM tp : ℝ) (lawT : BirthLaw) (Gt' : GenStage D ScalarH A.Dt A.bw j₀)
    (seed : GenStage D ScalarH A.Ds A.bw j₀) (rootM rootR : ℕ → ℝ) (seedKc : ℕ → KernelSpec)
    (ι : CompIn (Gt'.retained M 1 A.RT).comps ≃ CompIn seed.comps),
    SeedCtx A sXT sZT nW cr CL Cχ kW cP CP cH Cw M D a lawW PW Gw aM tp lawT Gt' seed rootM rootR
      seedKc ι →
    seed.IsNatural (M + A.Jw) → seed.IsContextCertified kS →
    ∃ (p : ContextEnvelopeParameters) (E : ContextEnvelopeEstimate p),
      ContextEnvelopeInput p seed kS kS.mEnv (rhoStar D kS.c₀ seed.level) ∧
        E.levelFloor ≤ seed.level ∧ E.Ca ≤ kS.Ca ∧ ∀ j, E.Cm j ≤ kS.Cm j

/-- **The envelopes at one level from the four pieces.** -/
theorem seedEnvelopeAtM_of_pieces {X : TermConstruction} {A : TermArgs X} {sXT sZT : ℕ} {nW : ℕ+}
    {cr : ℝ} {kS : InvConsts} {CL Cχ : ℝ} {kW : InvConsts} {cP CP cH Cw Ce : ℝ} {j₀ M : ℕ}
    (h1 : SeedSampledAtM A sXT sZT nW cr kS CL Cχ kW cP CP cH Cw Ce j₀ M)
    (h3 : SeedLedgerAtM A sXT sZT nW cr kS CL Cχ kW cP CP cH Cw Ce j₀ M)
    (h4 : SeedSchurAtM A sXT sZT nW cr kS CL Cχ kW cP CP cH Cw Ce j₀ M)
    (hI : SeedEnvInputAtM A sXT sZT nW cr kS CL Cχ kW cP CP cH Cw j₀ M) :
    SeedEnvelopeAtM A sXT sZT nW cr kS CL Cχ kW cP CP cH Cw Ce j₀ M := by
  intro D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx hnat hcert law hm hr
  obtain ⟨p, E, hin, hlev, hCa, hCm⟩ :=
    hI D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx hnat hcert
  have hled := h3 D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx hnat hcert law hm hr
  obtain ⟨henv, hpt⟩ := stage_envelopes_with_ledger_of_context p E seed kS _ hin hlev hCa hCm law
    (tp + D.termH M) (a + A.T₀) (Ce * D.eps (M - 1) ^ A.τe) hled
  exact ⟨h1 D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx hnat hcert, henv, hled,
    h4 D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx hnat hcert law hm hr, hpt⟩

/-- **The sampled coefficient bound** (it needs the map bound of the weak stage). -/
def SeedSampledPart : Prop :=
  SeedPartPrefix fun _ A _ sXT sZT _ nW cr kS CL Cχ kW cP CP =>
    SeedLevelBlock A fun cH Cw Ce j₀ M => SeedSampledAtM A sXT sZT nW cr kS CL Cχ kW cP CP cH Cw Ce j₀ M

/-- **The marked ledger** (route: the encoding keeps the masses and the records, the
seed's markers are `1`; `termRetained_ledger_le`; smallness for `M` large). -/
def SeedLedgerPart : Prop :=
  SeedPartPrefix fun _ A _ sXT sZT _ nW cr kS CL Cχ kW cP CP =>
    SeedLevelBlock A fun cH Cw Ce j₀ M => SeedLedgerAtM A sXT sZT nW cr kS CL Cχ kW cP CP cH Cw Ce j₀ M

/-- **The kernel Schur bound (route: `kernel_schur_of_identity_prices` with the
identity prices of `uniform_native_identity_kernel_price` at the seed and the priced Schur bound
of the marked ledger, as in `retainedSchurAtM_of_price`). -/
def SeedSchurPart : Prop :=
  SeedPartPrefix fun _ A _ sXT sZT _ nW cr kS CL Cχ kW cP CP =>
    SeedLevelBlock A fun cH Cw Ce j₀ M => SeedSchurAtM A sXT sZT nW cr kS CL Cχ kW cP CP cH Cw Ce j₀ M

/-- **The envelope input** (the template is `successor_context_envelope_preparation`). -/
def SeedEnvInputPart : Prop :=
  SeedPartPrefix fun _ A _ sXT sZT _ nW cr kS CL Cχ kW cP CP =>
    SeedLevelBlock A fun cH Cw _ j₀ M => SeedEnvInputAtM A sXT sZT nW cr kS CL Cχ kW cP CP cH Cw j₀ M

/-- **`SeedEnvelopePart` from its four pieces.** -/
theorem seedEnvelopePart_of_pieces (h1 : SeedSampledPart) (h3 : SeedLedgerPart)
    (h4 : SeedSchurPart) (hI : SeedEnvInputPart) : SeedEnvelopePart :=
  SeedPartPrefix.mono
    (fun X A hΛ _ sXT sZT _ nW cr kS CL Cχ kW cP CP ⟨⟨b1, b3⟩, ⟨b4, bI⟩⟩ =>
      have h1Λ : 1 ≤ A.Λ := le_trans (by norm_num) hΛ
      SeedLevelBlock.mono (fun _ _ _ _ _ ⟨⟨q1, q3⟩, ⟨q4, qI⟩⟩ => seedEnvelopeAtM_of_pieces q1 q3 q4 qI)
        ((b1.and h1Λ b3).and h1Λ (b4.and h1Λ bI)))
    ((h1.and h3).and (h4.and hI))

end AVRegularity.EntryTerminal.Route
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.EntryTerminal.Route

/-! Transport of the ordinary priced ledger through the seed encoding. -/

/-- Re-rooting removes the marker and preserves the ordinary priced matrix. -/
theorem seed_ledger_of_encoding {D : OCData} {b : ℝ} {j₀ Dt Ds : ℕ}
    {Pt : ProvParams} {lawT law : BirthLaw} {rootM rootR : ℕ → ℝ}
    {seedKt freshKt seedKc : ℕ → KernelSpec}
    {Gt : GenStage D ScalarH Dt b j₀} {seed : GenStage D ScalarH Ds b j₀}
    {ι : CompIn Gt.comps ≃ CompIn seed.comps}
    (he : IsSeedEncoding Pt lawT rootM rootR seedKt freshKt seedKc Gt seed ι)
    (hm : law.rootMass = rootM) {B : ℝ} (hB : 0 ≤ B)
    (hb : markedLedger (Gt.mass lawT) (Gt.marker lawT) Gt.fam ≤ B) :
    markedLedger (seed.mass law) (seed.marker law) seed.fam ≤ B := by
  obtain ⟨-, hbirths, hroots, -, -, -, e, idx, _hinj, hdata⟩ := he
  have hmass (v) : seed.mass law (ι v) = Gt.mass lawT v := by
    simp only [GenStage.mass, compMass, hbirths v, List.map_nil, List.prod_nil, mul_one, hm]
    exact (hroots v).1
  have hmark : seed.marker law = fun _ => 1 := by
    funext v
    obtain ⟨v, rfl⟩ := ι.surjective v
    simp [GenStage.marker, compMarker, compBirthSet, hbirths v]
  have hmatrix (v u) :
      pricedRecordMajorant (seed.mass law) (fun _ => 1) seed.fam (ι v) (ι u) =
      pricedRecordMajorant (Gt.mass lawT) (fun _ => 1) Gt.fam v u := by
    simp only [pricedRecordMajorant, hmass]
    congr 1
    rw [← Equiv.sum_comp (e v u)]
    apply Finset.sum_congr rfl
    intro γ _
    rw [(hdata v u γ).2.2.1, (hdata v u γ).2.2.2.1]
  have hs := Construction.Preservation.FullLift.fullLedger_schur_bound
    (pricedRecordMajorant (Gt.mass lawT) (fun _ => 1) Gt.fam)
  have hs' : SchurBound B (pricedRecordMajorant (seed.mass law) (fun _ => 1) seed.fam) := by
    constructor
    · intro v
      obtain ⟨v, rfl⟩ := ι.surjective v
      rw [← Equiv.sum_comp ι]
      simp_rw [hmatrix]
      exact (hs.1 v).trans ((le_max_left _ _).trans hb)
    · intro u
      obtain ⟨u, rfl⟩ := ι.surjective u
      rw [← Equiv.sum_comp ι]
      simp_rw [hmatrix]
      exact (hs.2 u).trans ((le_max_left _ _).trans hb)
  rw [markedLedger, hmark, max_self]
  exact Construction.Preservation.Ledger.fullLedger_le_of_schur hB hs'

/-! the marked ledger assembly: only the quantitative retained ledger decay remains. -/

def RetainedDecayAtM {X : TermConstruction} (A : TermArgs X) (sXT sZT : ℕ) (nW : ℕ+) (cr : ℝ)
    (_kS : InvConsts) (CL Cχ : ℝ) (kW : InvConsts) (cP CP cH Cw Ce : ℝ) (j₀ M : ℕ) : Prop :=
  ∀ (D : OCData) (a : ℝ) (lawW : BirthLaw) (PW : ProvParams) (Gw : GenStage D ScalarH A.Dt A.bw j₀)
    (aM tp : ℝ) (lawT : BirthLaw) (Gt' : GenStage D ScalarH A.Dt A.bw j₀)
    (seed : GenStage D ScalarH A.Ds A.bw j₀) (rootM rootR : ℕ → ℝ) (seedKc : ℕ → KernelSpec)
    (ι : CompIn (Gt'.retained M 1 A.RT).comps ≃ CompIn seed.comps),
    SeedCtx A sXT sZT nW cr CL Cχ kW cP CP cH Cw M D a lawW PW Gw aM tp lawT Gt' seed rootM rootR
      seedKc ι →
    0 ≤ Ce ∧ markedLedger ((Gt'.retained M 1 A.RT).mass lawT)
      ((Gt'.retained M 1 A.RT).marker lawT) (Gt'.retained M 1 A.RT).fam ≤ Ce * D.eps (M - 1) ^ A.τe

def RetainedDecayPart : Prop :=
  SeedPartPrefix fun _ A _ sXT sZT _ nW cr kS CL Cχ kW cP CP =>
    SeedLevelBlock A fun cH Cw Ce j₀ M =>
      RetainedDecayAtM A sXT sZT nW cr kS CL Cχ kW cP CP cH Cw Ce j₀ M

/-- The seed ledger follows from the retained ledger, without extra stage premises. -/
theorem seedLedgerPart_of_retainedDecay (h : RetainedDecayPart) : SeedLedgerPart := by
  apply SeedPartPrefix.mono (h := h)
  intro X A hΛ Kout sXT sZT Lt nW cr kS CL Cχ kW cP CP hb
  apply SeedLevelBlock.mono (h := hb)
  intro cH Cw Ce j₀ M hret D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx _ _ law hm _
  have hr := hret D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx
  have he : 0 < D.eps (M - 1) := by
    apply Construction.Stream.ocEpsilon_pos
    rw [hctx.1.2.2.1]
    omega
  have hB : 0 ≤ Ce * D.eps (M - 1) ^ A.τe :=
    mul_nonneg hr.1 (Real.rpow_nonneg he.le _)
  exact seed_ledger_of_encoding hctx.2.2.2.2.2.2.2.1 hm hB hr.2

end AVRegularity.EntryTerminal.Route
end
