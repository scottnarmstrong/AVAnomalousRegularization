-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.Frontier.LengthPrice.Producer
import AVRegularity.EntryTerminal.Assembly.Seed.RetainedGeneric
public import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.CovCommCont
import AVRegularity.EntryWeakAssembly.CoordinateWordFiniteWindowHigherProduction
import AVRegularity.CycleComparison.Coarse.Defect.DFBound
public import AVRegularity.EntryTerminal.Ingredients.Frontier.InnerStatements
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
import AVRegularity.Construction.Preservation.Ledger.TaggedRecurrence
import AVRegularity.CycleComparison.Coarse.Energy.Zero
import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
import AVRegularity.CycleComparison.Reconstruction.LiftSource
import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.FluxBoundBasic

section
@[expose] public noncomputable section

section
open Homogenization
namespace AVRegularity.Construction.Preservation.Ledger

/-! **The copy-only Schur bound of the actual successor, for a masked edge set.**

For the actual successor `G'` of `G`, the sum over the edges of a mask `p` that only contains
edges whose source is a copy (a direct transport or a quadratic conversion, no fresh letter) of the
unit-marker priced diagonal majorant is at most `|W| (4 C_w S)` with `S` the ledger of `G`
(the fresh-letter prefactor `F` of the full bound does not occur). The input is the cost bound
`identityPrice G' a e ≤ sourcePrice C_w F c (source e)` of `source_record_price_le_gen`, whose
copy cases do not depend on `F`.

Degenerate cases: the empty mask (bound `0 ≤ …`); `S = 0` (then the bound is `0`).
-/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {G G' : GenStage D hr Dm bw j₀}

/-- The cost of a copy source does not depend on the letter prefactor. -/
theorem sourcePrice_copy {C F F' : ℝ} {c : LedgerEdge G → ℝ} (s : SuccSource G)
    (hs : s.letter? = none) : sourcePrice C F c s = sourcePrice C F' c s := by
  cases s <;> simp_all [sourcePrice, SuccSource.letter?]

/-- A cost of a letter source with prefactor `0` vanishes. -/
theorem sourcePrice_letter_zero {C : ℝ} {c : LedgerEdge G → ℝ} (s : SuccSource G)
    (hs : s.letter? ≠ none) : sourcePrice C 0 c s = 0 := by
  cases s <;> simp_all [sourcePrice, SuccSource.letter?]

/-- The sources of an actual successor, with the provenance of the identities identified. -/
theorem sources {P : ProvParams} {Mn : SuccMenu}
    (hs : IsActualSuccessor D P Mn G G') :
    ∃ E : ActualSources P Mn G G',
      ∀ e : LedgerEdge G', G'.prov e.1 e.2.1 e.2.2 = (E.source e).prov G.level := by
  obtain ⟨e, _Cc, _Cc0, _hlift, _hdiag, hall⟩ := hs.2.2.2.2.2.2
  refine ⟨{ source := fun z => (e z.1 z.2.1 z.2.2).1
            valid := fun z => (e z.1 z.2.1 z.2.2).2.1
            src := fun z => (e z.1 z.2.1 z.2.2).2.2.1
            tgt := fun z => (e z.1 z.2.1 z.2.2).2.2.2
            tags := ?_
            map_eq := fun z => (hall z.1 z.2.1 z.2.2).2.1
            injective := ?_ }, fun z => (hall z.1 z.2.1 z.2.2).1⟩
  · rintro ⟨v, u, γ⟩ ⟨v', u', γ'⟩ he
    change (e v u γ).1 = (e v' u' γ').1 at he
    have hv : v = v' := Subtype.ext (by
      rw [← (e v u γ).2.2.2, ← (e v' u' γ').2.2.2, he])
    have hu : u = u' := Subtype.ext (by
      rw [← (e v u γ).2.2.1, ← (e v' u' γ').2.2.1, he])
    cases hv
    cases hu
    have hg : γ = γ' := (e v u).injective (Subtype.ext he)
    cases hg
    rfl
  · intro z
    have hh := (hs.2.2.2.2.1 z.1 z.2.1 z.2.2).1
    rw [(hall z.1 z.2.1 z.2.2).1] at hh
    exact hh

/-- **The copy-only Schur bound for a masked edge set.** -/
theorem masked_copy_schur {Cw η σ S : ℝ} {N p d : ℕ} {Rb rb : ℕ → ℝ} {Mn : SuccMenu}
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hCw : 0 ≤ Cw) (hσ : 0 ≤ σ)
    (hrb : rb (G.level - 1) = Rb (G.level - 1) * D.eps (G.level - 1) ^ σ)
    (hletters : ∀ l ∈ Mn.A, letterOrder N p l - 2 ≤ d) (law : BirthLaw)
    (hF1 : 1 ≤ birthDiagonalFactor D.q D.Λ G.level law false)
    (hG : G.HasTags (genProvParams D Cw η N p Rb rb))
    (hold : ∀ v ∈ G.comps, ∀ e ∈ v.births, G.level ≤ e.scale)
    (hs : IsActualSuccessor D (genProvParams D Cw η N p Rb rb) Mn G G')
    (E : ActualSources (genProvParams D Cw η N p Rb rb) Mn G G')
    (mask : LedgerEdge G' → Prop) (hmask : ∀ e, mask e → (E.source e).letter? = none)
    (hS : 0 ≤ S) (hhalf : S ≤ 1 / 2)
    (hledger : fullLedger (pricedRecordMajorant (G.mass law)
      (fun c => ledgerMarker D.q D.Λ law false c.1) G.fam) ≤ S) :
    SchurBound (((insert [] (wordsUpTo Mn.A (Mn.J + 1))).card : ℝ) * (4 * Cw * S))
      (fun v u => ∑ γ, (open Classical in
        if mask ⟨v, u, γ⟩ then identityPrice G' (ledgerDiagonal D.q D.Λ law false) ⟨v, u, γ⟩
        else 0)) := by
  classical
  have he := Scales.epsilon_basic (m := G.level - 1) hq hΛ
  let a := ledgerDiagonal D.q D.Λ law false
  let F := birthDiagonalFactor D.q D.Λ G.level law false
  let Ffresh := F * D.eps (G.level - 1) ^ (ocDelta D.α D.q - η - σ * (d : ℝ))
  have ha : ∀ v ∈ G.comps, 0 < a v := fun v _ => ledgerDiagonal_pos hq hΛ law false v
  have hF0 : 0 ≤ Ffresh := mul_nonneg (le_trans zero_le_one hF1) (Real.rpow_nonneg he.1.le _)
  let c := identityPrice G a
  have hc : ∀ e, 0 ≤ c e := identityPrice_nonneg G a ha
  have hrowcol : SchurBound S (fun v u => ∑ γ, c ⟨v, u, γ⟩) := by
    have hb := FullLift.fullLedger_schur_bound (pricedRecordMajorant (G.mass law)
      (fun c => ledgerMarker D.q D.Λ law false c.1) G.fam)
    simpa only [c, a, sum_identityPrice_eq hq hΛ law false] using
      (show SchurBound S (pricedRecordMajorant (G.mass law)
        (fun c => ledgerMarker D.q D.Λ law false c.1) G.fam) from
          ⟨fun v => (hb.1 v).trans hledger, fun u => (hb.2 u).trans hledger⟩)
  have hcost (e : LedgerEdge G') :
      (if mask e then identityPrice G' a e else 0) ≤ sourcePrice Cw 0 c (E.source e) := by
    by_cases hm : mask e
    · simp only [hm, ↓reduceIte]
      have hlet := hmask e hm
      have hratio := source_diagonal_ratio_le a ha hF1
        (fun v hv t => ledgerDiagonal_succComp hq hΛ hs.1 law false v (hold v hv) t)
        (E.source e) (source_old_mem (E.source e) (E.valid e))
      rw [E.tgt e, E.src e] at hratio
      have hh := source_record_price_le_gen a ha hCw he.1 he.2.1 hσ (le_trans zero_le_one hF1)
        rfl hrb hletters hG (E.source e) (E.valid e) (G'.fam.identity e.1 e.2.1 e.2.2).record
        (E.tags e) e.2.1.1.root e.1.1.root (a e.1.1 / a e.2.1.1) hratio
      have hid : identityPrice G' a e = a e.1.1 / a e.2.1.1 *
          (‖(G'.fam.identity e.1 e.2.1 e.2.2).map‖ * (G'.fam.identity e.1 e.2.1 e.2.2).record.size *
            constituentPrice (G'.fam.identity e.1 e.2.1 e.2.2).record) := rfl
      have hh' : identityPrice G' a e ≤ sourcePrice Cw Ffresh c (E.source e) := by
        rw [hid]
        simpa only [E.map_eq e, Ffresh, c, OCData.eps] using hh
      exact hh'.trans_eq (sourcePrice_copy (E.source e) hlet)
    · simp only [hm, ↓reduceIte]
      cases hl : (E.source e).letter? with
      | none =>
        cases hse : E.source e <;> simp_all [sourcePrice, SuccSource.letter?]
        all_goals first
          | exact mul_nonneg hCw (hc _)
          | exact mul_nonneg hCw (positivePathWeight_nonneg c hc _)
      | some l =>
        rw [sourcePrice_letter_zero (E.source e) (by simp [hl])]
  have hcode := actual_source_sums_le_of_code hs hold
    (fun e => if mask e then identityPrice G' a e else 0) E (sourcePrice Cw 0 c)
    (fun _ => codePrice Cw 0 c) (fun _ z => codePrice_nonneg Cw 0 hCw le_rfl c hc z)
    (fun R s hv hb => encodeSource_price Cw 0 c Mn.A Mn.J R s hv hb)
    (fun R row v => source_code_sum_le Cw 0 hCw le_rfl c hc hS hhalf hrowcol.1 hrowcol.2 row
      Mn.A Mn.J R v) hcost
  have hB : ((insert [] (wordsUpTo Mn.A (Mn.J + 1))).card : ℝ) *
      (4 * Cw * S + 2 * (Mn.A.card : ℝ) * Cw * 0) =
      ((insert [] (wordsUpTo Mn.A (Mn.J + 1))).card : ℝ) * (4 * Cw * S) := by ring
  constructor
  · intro v
    have hh := hcode true v
    rw [hB] at hh
    simpa [Fintype.sum_sigma] using hh
  · intro u
    have hh := hcode false u
    rw [hB] at hh
    simpa [Fintype.sum_sigma] using hh

end AVRegularity.Construction.Preservation.Ledger
end

section
open Homogenization AVRegularity
namespace AVRegularity.Construction.Preservation.Ledger

/-! **The letter-only Schur bound of the actual successor for a masked edge set, and the
copy sources of a stage with seed provenance carry a seed kernel.**

`masked_letter_schur`: the sum over a mask of edges whose source is a fresh letter of the
unit-marker priced diagonal majorant is at most `|W| · 2 |A| C_w R`, where `R` bounds the
fresh-letter prefactor (`fresh_actual_schur`). `copy_kernel_seed`: if every identity of the old
stage has a seed provenance, every copy source (direct transport, or quadratic conversion of a
nonempty path) has a seed kernel; hence an edge with a non-seed kernel has a letter source.

Degenerate cases: empty mask; `R = 0` (the bound is `0`).
-/

theorem widest_mem : ∀ {ts : List ProvTags} {w : ProvTags}, widestTags ts = some w → w ∈ ts
  | [], w, h => by simp [widestTags] at h
  | t :: ts, w, h => by
    unfold widestTags at h
    cases h' : widestTags ts with
    | none =>
      rw [h'] at h
      simp only [Option.some.injEq] at h
      rw [← h]; exact List.mem_cons_self
    | some t' =>
      rw [h'] at h
      by_cases hlt : t.width < t'.width
      · simp only [hlt, ite_true, Option.some.injEq] at h
        rw [← h]; exact List.mem_cons_of_mem _ (widest_mem h')
      · simp only [hlt, ite_false, Option.some.injEq] at h
        rw [← h]; exact List.mem_cons_self

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {G G' : GenStage D hr Dm bw j₀}

/-- A copy source of a stage with seed provenance has a seed kernel. -/
theorem copy_kernel_seed (P : ProvParams)
    (hseed : ∀ v u (γ : G.fam.Γ v u), ∃ k tag, G.prov v u γ = .seed k tag) (m : ℕ)
    {A : Finset WordLetter} {J : ℕ} (s : SuccSource G) (hv : s.Valid A J)
    (hl : s.letter? = none) : ∃ k, ((s.prov m).tags P).kernel = .seed k := by
  cases s with
  | copyDir t v u γ =>
    obtain ⟨k, tag, hk⟩ := hseed v u γ
    exact ⟨k, by simp [SuccSource.prov, Prov.tags, hk]⟩
  | copyQuad t h π =>
    have hh : 1 ≤ h := hv.2.2
    have hne : π.provList ≠ [] := by
      intro hnil
      have hlen : π.provList.length = h := by
        unfold StagePath.provList
        simp
      rw [hnil] at hlen
      simp at hlen
      omega
    have hsome := Prov.quad_widest_isSome P hne
    show ∃ k, ((Prov.quad m π.provList).tags P).kernel = .seed k
    unfold Prov.tags
    dsimp only
    cases hw : widestTags (Prov.pathTags P π.provList) with
    | none => rw [hw] at hsome; simp at hsome
    | some tw =>
      have hmem := widest_mem hw
      obtain ⟨x, hx, hxt⟩ := pathTags_mem P hmem
      unfold StagePath.provList at hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
      obtain ⟨k, tag, hk⟩ := hseed (π.step j).1 (π.step j).2.1 (π.step j).2.2
      refine ⟨k, ?_⟩
      show tw.kernel = _
      rw [hxt]
      simp [hk, Prov.tags]
  | letterDiag t u => simp [SuccSource.letter?] at hl
  | letterMean t n h π => simp [SuccSource.letter?] at hl
  | letterCov t n h a a' π => simp [SuccSource.letter?] at hl

/-- **The letter-only Schur bound for a masked edge set.** -/
theorem masked_letter_schur {Cw η σ S R : ℝ} {N p d : ℕ} {Rb rb : ℕ → ℝ} {Mn : SuccMenu}
    (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hCw : 0 ≤ Cw) (hσ : 0 ≤ σ)
    (hrb : rb (G.level - 1) = Rb (G.level - 1) * D.eps (G.level - 1) ^ σ)
    (hletters : ∀ l ∈ Mn.A, letterOrder N p l - 2 ≤ d) (law : BirthLaw)
    (hF1 : 1 ≤ birthDiagonalFactor D.q D.Λ G.level law false)
    (hbirth : birthDiagonalFactor D.q D.Λ G.level law false *
      D.eps (G.level - 1) ^ (ocDelta D.α D.q - η - σ * (d : ℝ)) ≤ R)
    (hG : G.HasTags (genProvParams D Cw η N p Rb rb))
    (hold : ∀ v ∈ G.comps, ∀ e ∈ v.births, G.level ≤ e.scale)
    (hs : IsActualSuccessor D (genProvParams D Cw η N p Rb rb) Mn G G')
    (E : ActualSources (genProvParams D Cw η N p Rb rb) Mn G G')
    (mask : LedgerEdge G' → Prop) (hmask : ∀ e, mask e → (E.source e).letter? ≠ none)
    (hS : 0 ≤ S) (hhalf : S ≤ 1 / 2)
    (hledger : fullLedger (pricedRecordMajorant (G.mass law)
      (fun c => ledgerMarker D.q D.Λ law false c.1) G.fam) ≤ S) :
    SchurBound (((insert [] (wordsUpTo Mn.A (Mn.J + 1))).card : ℝ) *
        (2 * (Mn.A.card : ℝ) * Cw * R))
      (fun v u => ∑ γ, (open Classical in
        if mask ⟨v, u, γ⟩ then identityPrice G' (ledgerDiagonal D.q D.Λ law false) ⟨v, u, γ⟩
        else 0)) := by
  classical
  have he := Scales.epsilon_basic (m := G.level - 1) hq hΛ
  let a := ledgerDiagonal D.q D.Λ law false
  let F := birthDiagonalFactor D.q D.Λ G.level law false
  let Ffresh := F * D.eps (G.level - 1) ^ (ocDelta D.α D.q - η - σ * (d : ℝ))
  have ha : ∀ v ∈ G.comps, 0 < a v := fun v _ => ledgerDiagonal_pos hq hΛ law false v
  have hF0 : 0 ≤ Ffresh := mul_nonneg (le_trans zero_le_one hF1) (Real.rpow_nonneg he.1.le _)
  let c := identityPrice G a
  have hc : ∀ e, 0 ≤ c e := identityPrice_nonneg G a ha
  have hrowcol : SchurBound S (fun v u => ∑ γ, c ⟨v, u, γ⟩) := by
    have hb := FullLift.fullLedger_schur_bound (pricedRecordMajorant (G.mass law)
      (fun c => ledgerMarker D.q D.Λ law false c.1) G.fam)
    simpa only [c, a, sum_identityPrice_eq hq hΛ law false] using
      (show SchurBound S (pricedRecordMajorant (G.mass law)
        (fun c => ledgerMarker D.q D.Λ law false c.1) G.fam) from
          ⟨fun v => (hb.1 v).trans hledger, fun u => (hb.2 u).trans hledger⟩)
  have hcost (e : LedgerEdge G') :
      (if mask e then identityPrice G' a e else 0) ≤
        Frontier.LengthPrice.freshSourceCost Cw Ffresh c (E.source e) := by
    by_cases hm : mask e
    · simp only [hm, ↓reduceIte]
      have hlet := hmask e hm
      have hratio := source_diagonal_ratio_le a ha hF1
        (fun v hv t => ledgerDiagonal_succComp hq hΛ hs.1 law false v (hold v hv) t)
        (E.source e) (source_old_mem (E.source e) (E.valid e))
      rw [E.tgt e, E.src e] at hratio
      have hh := source_record_price_le_gen a ha hCw he.1 he.2.1 hσ (le_trans zero_le_one hF1)
        rfl hrb hletters hG (E.source e) (E.valid e) (G'.fam.identity e.1 e.2.1 e.2.2).record
        (E.tags e) e.2.1.1.root e.1.1.root (a e.1.1 / a e.2.1.1) hratio
      have hid : identityPrice G' a e = a e.1.1 / a e.2.1.1 *
          (‖(G'.fam.identity e.1 e.2.1 e.2.2).map‖ * (G'.fam.identity e.1 e.2.1 e.2.2).record.size *
            constituentPrice (G'.fam.identity e.1 e.2.1 e.2.2).record) := rfl
      have hh' : identityPrice G' a e ≤ sourcePrice Cw Ffresh c (E.source e) := by
        rw [hid]
        simpa only [E.map_eq e, Ffresh, c, OCData.eps] using hh
      unfold Frontier.LengthPrice.freshSourceCost
      simp only [hlet, ↓reduceIte]
      exact hh'
    · simp only [hm, ↓reduceIte]
      unfold Frontier.LengthPrice.freshSourceCost
      split_ifs with hl
      · exact le_rfl
      · cases hs' : E.source e <;> simp_all [sourcePrice, SuccSource.letter?]
        all_goals first
          | exact mul_nonneg hCw hF0
          | exact mul_nonneg (mul_nonneg hCw hF0) (positivePathWeight_nonneg c hc _)
  have hfresh := Frontier.LengthPrice.fresh_actual_schur hs hold
    (fun e => if mask e then identityPrice G' a e else 0) E Cw Ffresh hCw hF0 c hc hS hhalf
    hrowcol.1 hrowcol.2 hcost
  have hle : ((insert [] (wordsUpTo Mn.A (Mn.J + 1))).card : ℝ) * (2 * (Mn.A.card : ℝ) * Cw * Ffresh) ≤
      ((insert [] (wordsUpTo Mn.A (Mn.J + 1))).card : ℝ) * (2 * (Mn.A.card : ℝ) * Cw * R) := by
    have h1 : Ffresh ≤ R := hbirth
    have : 0 ≤ 2 * (Mn.A.card : ℝ) * Cw := by positivity
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 this) (Nat.cast_nonneg _)
  exact ⟨fun i => (hfresh.1 i).trans hle, fun i => (hfresh.2 i).trans hle⟩

end AVRegularity.Construction.Preservation.Ledger
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.KernelEnergy AVRegularity.CycleComparison.Coarse
namespace AVRegularity.Construction.Residual.Presentation

/-! The finite mass-weighted bound of the cell-mean operator's actual coefficient operator. Sobolev
multiplication and the exact derivative reserve control each block; Minkowski sums the
orders; the Schur test sums components. The price is independent of their number. -/

variable {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {K R : ℕ} {a b ρ Cb : ℝ} {π : ι → ℝ}
  {input target : ∀ v : ι, ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)}

namespace CovTruncCoefficientData
variable (P : CovTruncCoefficientData K R a b ρ Cb π input target)

/-- The full coefficient matrix acts on the finite family of carriers. -/
def opOnWindow (hρ : 0 < ρ) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    (∀ v, TorusHk (K + R) (PiLp 2 (fun _ : Fin 2 => h v))) →L[ℝ]
      (∀ v, TorusHk K (PiLp 2 (fun _ : Fin 2 => h v))) :=
  ContinuousLinearMap.pi fun v => ∑ u, ∑ r : Fin (R + 1),
    (P.termCLM hρ v u r t ht).comp (ContinuousLinearMap.proj u)

/-- The exact finite row formula of the coefficient operator. -/
theorem opOnWindow_apply (hρ : 0 < ρ) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (U : ∀ v, TorusHk (K + R) (PiLp 2 (fun _ : Fin 2 => h v))) (v : ι) :
    P.opOnWindow hρ t ht U v = ∑ u, ∑ r : Fin (R + 1), P.termCLM hρ v u r t ht (U u) := by
  simp only [opOnWindow, ContinuousLinearMap.pi_apply, sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]

/-- A coefficient block costs its actual seminorm times the exact factorial derivative reserve. -/
theorem term_factorial_le (hρ : 0 < ρ) (v u : ι) (r : Fin (R + 1)) (t : ℝ)
    (ht : t ∈ Set.Icc a b) (U : TorusHk (K + R) (PiLp 2 (fun _ : Fin 2 => h u))) :
    Real.sqrt (factorialNormSq ρ (P.termCLM hρ v u r t ht U).val) ≤
      ((coefficientSeminorm ρ K a b (P.coeff v u r)).toReal *
        derivativeReserveFactor ρ K r.val) * Real.sqrt (factorialNormSq ρ U.val) := by
  let hKR : K + r.val ≤ K + R := Nat.add_le_add_left (Nat.le_of_lt_succ r.isLt) K
  have he : P.termCLM hρ v u r t ht U =
      AVRegularity.WeakEntryProofs.weakQuietSourceFlux le_rfl ρ hρ a b (P.coeff v u r)
        (P.finite v u r) t ht (P.smooth v u r t ht) (P.periodic v u r t ht)
        (truncateTorusHk hKR U) := by
    rw [P.termCLM_apply]
    rfl
  rw [he]
  have hm := AVRegularity.WeakEntryProofs.weak_quiet_positive_flux
    (E := PiLp 2 (fun _ : Fin 2 => h u)) (F := h v) le_rfl hρ hρ le_rfl
    (P.coeff v u r) (P.finite v u r) t ht (P.smooth v u r t ht)
    (P.periodic v u r t ht) (truncateTorusHk hKR U)
  refine hm.trans (mul_le_mul_of_nonneg_left (sqrt_fNSq_torus_truncate_le ρ hKR U) ?_)
  apply mul_nonneg ENNReal.toReal_nonneg
  unfold derivativeReserveFactor
  positivity

/-- Minkowski over derivative orders and components, retaining the given price matrix. -/
theorem opOnWindow_factorial_le (hρ : 0 < ρ) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (U : ∀ v, TorusHk (K + R) (PiLp 2 (fun _ : Fin 2 => h v))) (v : ι) :
    Real.sqrt (factorialNormSq ρ (P.opOnWindow hρ t ht U v).val) ≤
      ∑ u, P.price v u * Real.sqrt (factorialNormSq ρ (U u).val) := by
  rw [P.opOnWindow_apply]
  refine (sqrt_fNSq_torus_sum_le ρ Finset.univ _).trans (Finset.sum_le_sum fun u _ => ?_)
  refine (sqrt_fNSq_torus_sum_le ρ Finset.univ _).trans ?_
  calc
    _ ≤ ∑ r : Fin (R + 1),
        ((coefficientSeminorm ρ K a b (P.coeff v u r)).toReal *
          derivativeReserveFactor ρ K r.val) * Real.sqrt (factorialNormSq ρ (U u).val) :=
      Finset.sum_le_sum fun r _ => P.term_factorial_le hρ v u r t ht (U u)
    _ = (∑ r : Fin (R + 1), (coefficientSeminorm ρ K a b (P.coeff v u r)).toReal *
        derivativeReserveFactor ρ K r.val) * Real.sqrt (factorialNormSq ρ (U u).val) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (P.coefficient_cost v u) (Real.sqrt_nonneg _)

/-- The Schur row and column budgets bound the complete mass norm at one time. -/
theorem opOnWindow_mass_bound (hρ : 0 < ρ) (hπ : ∀ v, 0 < π v) (t : ℝ)
    (ht : t ∈ Set.Icc a b) (U : ∀ v, TorusHk (K + R) (PiLp 2 (fun _ : Fin 2 => h v))) :
    massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => K) ρ π
      (fun v => (P.opOnWindow hρ t ht U v).val) ≤ Cb ^ 2 *
        massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := fun _ => K + R) ρ π
          (fun v => (U v).val) := by
  have hs := schur_mass_sq_le π hπ P.price P.price_nonneg
    (fun u => Real.sqrt (factorialNormSq ρ (U u).val)) Cb P.row P.col
  have hp (v : ι) : factorialNormSq ρ (P.opOnWindow hρ t ht U v).val ≤
      (∑ u, P.price v u * Real.sqrt (factorialNormSq ρ (U u).val)) ^ 2 := by
    have hv := pow_le_pow_left₀ (Real.sqrt_nonneg _)
      (P.opOnWindow_factorial_le hρ t ht U v) 2
    rwa [Real.sq_sqrt (factorialNormSq_nonneg _ _)] at hv
  calc
    _ ≤ ∑ v, (π v)⁻¹ * (∑ u, P.price v u * Real.sqrt (factorialNormSq ρ (U u).val)) ^ 2 :=
      Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (hp v) (inv_nonneg.2 (hπ v).le)
    _ ≤ _ := by
      change _ ≤ Cb ^ 2 * ∑ u, (π u)⁻¹ * factorialNormSq ρ (U u).val
      simpa only [Real.sq_sqrt (factorialNormSq_nonneg _ _)] using hs

end CovTruncCoefficientData

end AVRegularity.Construction.Residual.Presentation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.KernelEnergy AVRegularity.Construction.Preservation.FullLift
namespace AVRegularity.Construction.Residual.Presentation

/-! Exact value realization of the physical coefficient operator. A classical periodic
input value fixes all the stored weak jets; the coefficient multipliers therefore act on
its actual classical derivatives. Finite carrier sums preserve the identity almost everywhere. -/

private theorem covTruncCoefficient_prefix_value {K r : ℕ} (w : DerivativeWord2 r) :
    prefixJetIndex w (valueIndex2 K) = ⟨⟨r, by omega⟩, w⟩ := by
  simp only [prefixJetIndex, valueIndex2, valueIndex]
  congr 1
  funext i
  exact Fin.addCases_left i

variable {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {K R : ℕ} {a b ρ Cb : ℝ} {π : ι → ℝ}
  {input target : ∀ v : ι, ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)}

namespace CovTruncCoefficientData
variable (P : CovTruncCoefficientData K R a b ρ Cb π input target)

/-- A multiplier block realizes its literal differential action on the input. -/
theorem term_value_ae (hρ : 0 < ρ) (v u : ι) (r : Fin (R + 1)) (t : ℝ)
    (ht : t ∈ Set.Icc a b) (U : TorusHk (K + R) (PiLp 2 (fun _ : Fin 2 => h u)))
    (hU : IsClassicalRep U (input u t) (K + R)) :
    (P.termCLM hρ v u r t ht U).toFunction.jet (valueIndex2 K) =ᵐ[
      volume.restrict AVenhance.unitCube] fun x => P.coeff v u r t x
        (WithLp.toLp 2 fun α : DerivativeWord2 r.val => orderedDerivative α (input u t) x) := by
  let hKR : K + r.val ≤ K + R := Nat.add_le_add_left (Nat.le_of_lt_succ r.isLt) K
  let V := truncateTorusHk hKR U
  let W := AVRegularity.KernelEnergy.torusDerivativeTensor (K := K) (r := r.val) V
  have hVr : IsClassicalRep V (input u t) r.val :=
    classicalRep_truncate hKR (by omega) U (input u t)
      (classicalRep_order_mono U (input u t) hU (by omega))
  have hj : ∀ α : DerivativeWord2 r.val,
      V.toFunction.jet (prefixJetIndex α (valueIndex2 K)) =ᵐ[
        volume.restrict AVenhance.unitCube] orderedDerivative α (input u t) := by
    intro α
    rw [covTruncCoefficient_prefix_value]
    rw [← AVRegularity.CycleComparison.Coarse.torusJetOrder_of_le V (by omega) α]
    exact hVr.2.2.2 r.val le_rfl α
  rw [P.termCLM_apply]
  have hmul := torusMulCoefficient_toFunction_value_ae W (P.coeff v u r t)
    (P.smooth v u r t ht) (P.periodic v u r t ht) (P.jetBound_bounds hρ v u r t ht)
  have hten := AVRegularity.KernelEnergy.torusDerivativeTensor_base_ae V
  filter_upwards [hmul, hten, ae_all_iff.mpr hj] with x hxmul hxten hxj
  change (W.mulCoefficient _ _ _ _).toFunction.jet (valueIndex2 K) x = _
  rw [hxmul, hxten]
  apply congrArg (P.coeff v u r t x)
  apply PiLp.ext
  intro α
  exact hxj α

/-- The finite coefficient operator realizes the exact classical flux on the window. -/
theorem opOnWindow_value_ae (hρ : 0 < ρ) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (U : ∀ v, TorusHk (K + R) (PiLp 2 (fun _ : Fin 2 => h v)))
    (hU : ∀ v, (U v).toFunction.jet (valueIndex2 (K + R)) =ᵐ[
      volume.restrict AVenhance.unitCube] input v t) (v : ι) :
    (P.opOnWindow hρ t ht U v).toFunction.jet (valueIndex2 K) =ᵐ[
      volume.restrict AVenhance.unitCube] target v t := by
  have hc : ∀ u, IsClassicalRep (U u) (input u t) (K + R) := fun u =>
    classicalRep_of_smooth_periodic_value_ae (U u) (input u t)
      (P.input_smooth u t ht) (P.input_periodic u t ht) (hU u)
  rw [P.opOnWindow_apply]
  have hs := torusJet_sum_ae_of_eq
    (fun u => ∑ r : Fin (R + 1), P.termCLM hρ v u r t ht (U u)) (valueIndex2 K)
    (fun u x => ∑ r : Fin (R + 1), P.coeff v u r t x
      (WithLp.toLp 2 fun α : DerivativeWord2 r.val => orderedDerivative α (input u t) x))
    (fun u => torusJet_sum_ae_of_eq
      (fun r : Fin (R + 1) => P.termCLM hρ v u r t ht (U u)) (valueIndex2 K)
      (fun r x => P.coeff v u r t x
        (WithLp.toLp 2 fun α : DerivativeWord2 r.val => orderedDerivative α (input u t) x))
      (fun r => P.term_value_ae hρ v u r t ht (U u) (hc u)))
  exact hs.trans (Filter.Eventually.of_forall fun x => (P.action v t ht x).symm)

end CovTruncCoefficientData

end AVRegularity.Construction.Residual.Presentation
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.Construction.Residual.Presentation

/-! **The filter defect from three named parts**.

`FilterDefectStatement` is the readout `𝖱 = filterReadoutDefect` of the root flux defects of the
terminal successor `Gt'` on `x.aZ`. It is assembled from

* `FilterRowSmoothStatement`: every row `rootFluxDefect … v'` (rows of `Gt'`) is
  `C^{k_c+2p_T}` and periodic at each time of the window. Route: the proof of
  `termReconReadoutSmooth_proof` (`rootFluxDefect_smooth`
  with `termCtx_physCoeff` at the order `n`) with `n = k_c + 2p_T` in place of `2p_T`; the floor
  `K_floor` is taken after `k_c`.
* `FilterRowMassStatement`: the rows have a realization of order `k_c + 2p_T` over the
  components of `Gt'`, with mass at most `C · filterPrice · ‖f‖₂`. Route: two `FDData` instances
  (the weak kernels of order `n_W`, price `x^{χ_w}(r_w/ρ)^{L_o}`; the fresh kernels of the
  record widths, price `E^{b_T+t_TL_c}`), `FDData.timeBound` (kernel orders arbitrary),
  Schur bound from `x.cert` (`context_certified_physical_kernel_price`,
  `native_physCoeff_all_order_seminorm_finite`), the record prices from
  `fresh_prefix_price_of_actual_gen`, and the energy of `Z` (as in `CovTruncGStatement`).
* `FilterReadoutMapStatement`: the readout `𝖱` with the weights `E^{η₀|𝔱|}` from the
  rows of `Gt'` to the rows of `Gw` costs a constant depending on `A` and `k_c` only (the birth
  law `IsTerminalLaw`: `etaB = η₀/2`, `wordCount`; Cauchy–Schwarz over the children of a parent).

The assembly: `filterDefect_of_parts`. If `x.aZ = 0`, all parts are trivial. -/

section Terminal

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
  (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
    cker j₀ M)

/-- The rows of the root flux defects of `Gt'` are `C^{k_c+2p_T}` and periodic. -/
def FilterRowSmoothAt (x : TermResAux c) (kc : ℕ) : Prop :=
  ∀ v' : CompIn c.Gt'.comps, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
    ContDiff ℝ ((kc + 2 * A.pT : ℕ) : ℕ∞)
        (fun y => rootFluxDefect (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀
          c.Gw c.Gt' x.aZ v' t y) ∧
      IsZ2Periodic
        (fun y => rootFluxDefect (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀
          c.Gw c.Gt' x.aZ v' t y)

/-- The rows of the root flux defects of `Gt'` have a realization of order `k_c + 2p_T` with
mass at most `C · filterPrice · ‖f‖₂`. -/
def FilterRowMassAt (x : TermResAux c) (kc : ℕ) (C : ℝ) : Prop :=
  HasFluxBound (ι := CompIn c.Gt'.comps) (h := fun v => ScalarH v.1.root) (kc + 2 * A.pT)
    (Set.Icc c.tp (c.a + A.T₀)) (c.D.κ (M - 1)) (c.D.termRho cr M) (c.Gt'.mass c.lawT)
    (fun v' t y => rootFluxDefect (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀
      c.Gw c.Gt' x.aZ v' t y)
    (C * c.filterPrice * c.normF)

/-- The mass clause of `FilterDefectAt`. -/
def FilterReadoutMassAt (x : TermResAux c) (kc : ℕ) (C : ℝ) : Prop :=
  HasFluxBound (ι := CompIn c.Gw.comps) (h := fun v => ScalarH v.1.root) (kc + 2 * A.pT)
    (Set.Icc c.tp (c.a + A.T₀)) (c.D.κ (M - 1)) (c.D.termRho cr M) (c.Gw.mass c.lawW)
    (fun v t y => toFluxL
      (filterReadoutDefect (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀
        c.Gw c.Gt' M (c.D.eps (M - 1)) A.η₀ x.aZ v t y))
    (C * c.filterPrice * c.normF)

/-- Smooth rows give a smooth periodic readout. -/
theorem filterReadout_smooth (x : TermResAux c) (kc : ℕ) (h : FilterRowSmoothAt c x kc) :
    ∀ v, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
    ContDiff ℝ ((kc + 2 * A.pT : ℕ) : ℕ∞)
        (fun y => filterReadoutDefect (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀
          c.Gw c.Gt' M (c.D.eps (M - 1)) A.η₀ x.aZ v t y) ∧
      IsZ2Periodic
        (fun y => filterReadoutDefect (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀
          c.Gw c.Gt' M (c.D.eps (M - 1)) A.η₀ x.aZ v t y) := by
  intro v t ht
  have hro := readoutFlux_smooth (hr := ScalarH) M (c.D.eps (M - 1)) A.η₀
    (S := c.Gw.comps) (S' := c.Gt'.comps) (fun _ => True)
    (fun v' s y' => rootFluxDefect (A.Pt c.D Cw cr M) (A.Kw_ c.D M nW) (A.Kn_ c.D M cr) A.φ₀
      c.Gw c.Gt' x.aZ v' s y') t (kc + 2 * A.pT) (fun v' => h v' t ht) v
  refine ⟨PiLp.contDiff_ofLp.comp hro.1, ?_⟩
  intro k y
  have := hro.2 k y
  unfold filterReadoutDefect
  simp only [this]

end Terminal

/-- **The rows are smooth** (see the module docstring for the route). -/
def FilterRowSmoothStatement : Prop :=
  TermResPrefix fun c x kc _ _ _ _ => FilterRowSmoothAt c x kc

/-- **The mass of the rows** (`FDData.timeBound` for the weak and the fresh kernels). -/
def FilterRowMassStatement : Prop :=
  TermResPrefix fun c x kc _ C _ _ => FilterRowMassAt c x kc C

/-- **The readout of the rows**: a change of the constant, depending on `A` and `k_c`
only. -/
def FilterReadoutMapStatement : Prop :=
  ∀ (X : TermConstruction) (A : TermArgs X) (kc : ℕ) (C₁ : ℝ), 128 ≤ A.Λ → A.Valid → 0 ≤ C₁ →
    ∃ C₂ : ℝ, TermFluxMap A kc C₁ C₂ (fun c x kc C => FilterRowMassAt c x kc C)
      (fun c x kc C => FilterReadoutMassAt c x kc C)

/-- **The defect tails from their three parts.** -/
theorem filterDefect_of_parts (hS : FilterRowSmoothStatement) (hM : FilterRowMassStatement)
    (hR : FilterReadoutMapStatement) : FilterDefectStatement := by
  have hjoin := termFluxPrefix_and
    (P₁ := fun c x kc _ => FilterRowSmoothAt c x kc)
    (P₂ := fun c x kc C => FilterRowMassAt c x kc C) hS hM
  refine termFluxPrefix_map_valid
    (P := fun c x kc C => FilterRowSmoothAt c x kc ∧ FilterRowMassAt c x kc C)
    (R := fun c x kc C => FilterDefectAt c x kc C) ?_ hjoin
  intro X A kc C₁ hΛ hV hC₁
  obtain ⟨C₂, hC₂⟩ := hR X A kc C₁ hΛ hV hC₁
  refine ⟨C₂, ?_⟩
  intro Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce cker j₀ M c x hPr C'
    hC'
  exact ⟨filterReadout_smooth c x kc hPr.1, hC₂ c x hPr.2 C' hC'⟩

end AVRegularity.Construction.Residual.Presentation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route AVRegularity.Construction.Preservation.FullLift
namespace AVRegularity.Construction.Residual.Presentation

/-! **The readout of the filter rows**: `FilterReadoutMapStatement`.

The readout `𝖱` sums the rows of the children `c` of a parent `v` (`compParent M c = v`) with the
weights `E^{η₀|𝔱|}`. In the inverse-mass norm, Cauchy–Schwarz over the children gives
`π_v⁻¹‖(𝖱F)_v‖² ≤ #fiber · ∑_c σ_c⁻¹‖F_c‖²`, provided `√(σ_c/π_v)·E^{η₀|𝔱|} ≤ 1`. Here:
- `σ_c = compMass lawT c ≤ compMass lawT v` (`readout_parent_mass_le`; needs `lawT.c_H ≤ 1`,
  which is `x.cHle`);
- `compMass lawT v = compMass lawW v = π_v`, since the components of `Gw` are roots and the root
  masses agree (`IsTerminalLaw`);
- each fiber has at most `#words(R_T + 1) + 1` children (`readout_root_fiber_card_le`, for roots,
  at any level).

The pieces:
- `readout_massNormSq_le`: the pointwise mass inequality, generic over the readout;
- `readout_fluxMassLe`: its integrated form `FluxMassLe`;
- `readout_isFluxRealization_scalar`: the readout of a realization realizes the readout;
- `filterReadoutMap`: the statement, with `C₂ = √(#words + 1)·C₁`.

Degenerate cases: no child (the readout is `0`); one child per parent (the constant `√2` is not
sharp); `C₁ = 0`. -/

section FluxMass

variable {ι ι' : Type*} [Fintype ι] [Fintype ι'] {h : ι → Type*} {h' : ι' → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  [∀ i, NormedAddCommGroup (h' i)] [∀ i, InnerProductSpace ℝ (h' i)]
  [∀ i, FiniteDimensional ℝ (h' i)] [∀ i, MeasurableSpace (h' i)] [∀ i, BorelSpace (h' i)]
  [∀ i, CompleteSpace (h' i)]

/-- The inverse-mass norm of a square-integrable family is integrable in time. -/
theorem integrable_fluxMassNormSq {K : ι → ℕ} (ρ : ℝ) (π : ι → ℝ) {μ : Measure ℝ}
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 μ) :
    Integrable (fun s => massNormSq (E := fun i => PiLp 2 (fun _ : Fin 2 => h i)) (K := K) ρ π
      (fun i => (F i s).val)) μ := by
  unfold massNormSq
  exact integrable_finsetSum _ fun i _ =>
    (CycleComparison.Coarse.integrable_factorialNormSq_torus (hF i)).const_mul _

/-- **A pointwise comparison of the inverse-mass norms transfers a flux mass bound.** -/
theorem fluxMassLe_of_pointwise {K : ι → ℕ} {K' : ι' → ℕ} (ν ρ C Y : ℝ) (I : Set ℝ)
    (hν : 0 < ν) (hC : 0 ≤ C) (π : ι → ℝ) (σ : ι' → ℝ)
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (G : ∀ i, ℝ → TorusHk (K' i) (PiLp 2 (fun _ : Fin 2 => h' i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict I))
    (hpt : ∀ s, massNormSq (E := fun i => PiLp 2 (fun _ : Fin 2 => h i)) (K := K) ρ π
        (fun i => (F i s).val) ≤
      C * massNormSq (E := fun i => PiLp 2 (fun _ : Fin 2 => h' i)) (K := K') ρ σ
        (fun i => (G i s).val))
    (hG : FluxMassLe (K := K') ν ρ σ I G Y) : FluxMassLe (K := K) ν ρ π I F (Real.sqrt C * Y) := by
  obtain ⟨hmem, hY⟩ := hG
  refine ⟨hF, ?_⟩
  have hle := integral_mono (integrable_fluxMassNormSq ρ π F hF)
    ((integrable_fluxMassNormSq ρ σ G hmem).const_mul C) hpt
  rw [integral_const_mul] at hle
  calc _ ≤ Real.sqrt (ν⁻¹ * (C * ∫ s in I, massNormSq (E := fun i => PiLp 2
          (fun _ : Fin 2 => h' i)) (K := K') ρ σ (fun i => (G i s).val))) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hν.le))
    _ = Real.sqrt C * Real.sqrt (ν⁻¹ * ∫ s in I, massNormSq (E := fun i => PiLp 2
          (fun _ : Fin 2 => h' i)) (K := K') ρ σ (fun i => (G i s).val)) := by
        rw [mul_left_comm, Real.sqrt_mul hC]
    _ ≤ Real.sqrt C * Y := mul_le_mul_of_nonneg_left hY (Real.sqrt_nonneg _)

end FluxMass

section Generic

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)]

omit [∀ r, FiniteDimensional ℝ (hr r)] in
/-- **The inverse-mass norm of a readout** is at most the fiber bound times that of its input. -/
theorem readout_massNormSq_le {S S' : Finset Comp} {K : ℕ} (m : ℕ) (E η ρ C : ℝ)
    (hE : 0 ≤ E) (π : CompIn S → ℝ) (σ : CompIn S' → ℝ)
    (hπ : ∀ v, 0 < π v) (hσ : ∀ c, 0 < σ c) (hparent : ∀ c : CompIn S', compParent m c.1 ∈ S)
    (hentry : ∀ (v : CompIn S) (c : CompIn S'), compParent m c.1 = v.1 →
      (Real.sqrt (π v))⁻¹ / (Real.sqrt (σ c))⁻¹ * E ^ (η * (compWord m c.1).length) ≤ 1)
    (hfiber : ∀ v : CompIn S,
      ((Finset.univ : Finset (CompIn S')).filter fun c => compParent m c.1 = v.1).card ≤ C)
    (X : ∀ c : CompIn S', TorusHk K (hr c.1.root)) :
    massNormSq (E := fun v : CompIn S => hr v.1.root) (K := fun _ => K) ρ π
        (fun v => (succReadout m E η K X v).val) ≤
      C * massNormSq (E := fun c : CompIn S' => hr c.1.root) (K := fun _ => K) ρ σ
        (fun c => (X c).val) := by
  have hσs : ∀ c, (Real.sqrt (σ c))⁻¹ ^ 2 = (σ c)⁻¹ := fun c => by
    rw [inv_pow, Real.sq_sqrt (hσ c).le]
  have hv : ∀ v : CompIn S, (π v)⁻¹ * factorialNormSq ρ (succReadout m E η K X v).val ≤
      C * ∑ c : CompIn S', if compParent m c.1 = v.1 then
        (σ c)⁻¹ * factorialNormSq ρ (X c).val else 0 := by
    intro v
    have h := readout_component_factorial_square_le m E η ρ C (Real.sqrt (π v))⁻¹ hE
      (inv_nonneg.mpr (Real.sqrt_nonneg _)) (fun c => (Real.sqrt (σ c))⁻¹)
      (fun c => inv_pos.mpr (Real.sqrt_pos.mpr (hσ c))) v (hentry v) (hfiber v) X
    rw [inv_pow, Real.sq_sqrt (hπ v).le] at h
    simpa only [hσs] using h
  unfold massNormSq
  calc ∑ v, (π v)⁻¹ * factorialNormSq ρ (succReadout m E η K X v).val
      ≤ ∑ v : CompIn S, C * ∑ c : CompIn S', if compParent m c.1 = v.1 then
          (σ c)⁻¹ * factorialNormSq ρ (X c).val else 0 := Finset.sum_le_sum fun v _ => hv v
    _ = C * ∑ c : CompIn S', ∑ v : CompIn S, if compParent m c.1 = v.1 then
          (σ c)⁻¹ * factorialNormSq ρ (X c).val else 0 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ = C * ∑ c : CompIn S', (σ c)⁻¹ * factorialNormSq ρ (X c).val := by
        congr 1
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_eq_single ⟨compParent m c.1, hparent c⟩]
        · simp
        · intro v _ hv
          exact ite_eq_right_iff.mpr fun h => absurd (Subtype.ext h.symm) hv
        · intro h
          exact absurd (Finset.mem_univ _) h

/-- **The readout of a realized flux bound**, in the inverse-mass norm. -/
theorem readout_fluxMassLe {S S' : Finset Comp} {K : ℕ} (m : ℕ) (E η ν ρ C Y : ℝ) (I : Set ℝ)
    (hν : 0 < ν) (hE : 0 ≤ E) (hC : 0 ≤ C) (π : CompIn S → ℝ) (σ : CompIn S' → ℝ)
    (hπ : ∀ v, 0 < π v) (hσ : ∀ c, 0 < σ c) (hparent : ∀ c : CompIn S', compParent m c.1 ∈ S)
    (hentry : ∀ (v : CompIn S) (c : CompIn S'), compParent m c.1 = v.1 →
      (Real.sqrt (π v))⁻¹ / (Real.sqrt (σ c))⁻¹ * E ^ (η * (compWord m c.1).length) ≤ 1)
    (hfiber : ∀ v : CompIn S,
      ((Finset.univ : Finset (CompIn S')).filter fun c => compParent m c.1 = v.1).card ≤ C)
    (Fk : ∀ c : CompIn S', ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => hr c.1.root)))
    (h : FluxMassLe (ι := CompIn S') (h := fun c => hr c.1.root) (K := fun _ => K) ν ρ σ I Fk Y) :
    FluxMassLe (ι := CompIn S) (h := fun v => hr v.1.root) (K := fun _ => K) ν ρ π I
      (fun v t => succReadout (hr := fun r => PiLp 2 (fun _ : Fin 2 => hr r)) m E η K
        (fun c => Fk c t) v) (Real.sqrt C * Y) := by
  exact fluxMassLe_of_pointwise (h := fun v : CompIn S => hr v.1.root)
    (h' := fun c : CompIn S' => hr c.1.root) ν ρ C Y I hν hC π σ _ Fk
    (fun v => memLp_succReadout (hr := fun r => PiLp 2 (fun _ : Fin 2 => hr r)) m E η Fk h.1 v)
    (fun s => readout_massNormSq_le (hr := fun r => PiLp 2 (fun _ : Fin 2 => hr r)) m E η ρ C hE
      π σ hπ hσ hparent hentry hfiber (fun c => Fk c s)) h

end Generic

/-- **The fiber of a readout over roots** has at most `#words(J + 1) + 1` elements, at every level
(the roots make `1 ≤ m` unnecessary). -/
theorem readout_root_fiber_card_le {m : ℕ} {A : Finset WordLetter} {J : ℕ} {S S' : Finset Comp}
    (hroot : ∀ v ∈ S, v.births = []) (hsub : S' ⊆ succExtComps m A J S) (v : Comp) :
    ((Finset.univ : Finset (CompIn S')).filter fun c => compParent m c.1 = v).card ≤
      (wordsUpTo A (J + 1)).card + 1 := by
  have hword : ∀ c ∈ succExtComps m A J S, compWord m c ∈ insert [] (wordsUpTo A (J + 1)) := by
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · have hb := hroot c hc
      rcases c with ⟨r, bs⟩
      subst hb
      simp [compWord]
    · obtain ⟨⟨u, t⟩, hut, rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨hu, ht⟩ := Finset.mem_product.mp hut
      by_cases ht0 : t = []
      · subst t
        have hb := hroot u hu
        rcases u with ⟨r, bs⟩
        subst hb
        simp [succComp, compWord]
      · simp only [succComp, ht0, ↓reduceDIte, compWord, ↓reduceIte]
        exact Finset.mem_insert_of_mem ht
  have hcard : ((Finset.univ : Finset (CompIn S')).filter fun c => compParent m c.1 = v).card ≤
      (insert [] (wordsUpTo A (J + 1))).card := by
    apply Finset.card_le_card_of_injOn (fun c : CompIn S' => compWord m c.1)
    · intro c _hc
      exact hword c.1 (hsub c.2)
    · intro c hc d hd hw
      change compWord m c.1 = compWord m d.1 at hw
      apply Subtype.ext
      have hcp := (Finset.mem_filter.mp hc).2
      have hdp := (Finset.mem_filter.mp hd).2
      calc
        c.1 = succComp m v (compWord m c.1) := by
          rw [← hcp]; exact (succComp_parent_word m c.1).symm
        _ = succComp m v (compWord m d.1) := by rw [hw]
        _ = d.1 := by rw [← hdp]; exact succComp_parent_word m d.1
  exact hcard.trans (Finset.card_insert_le _ _)

/-- **The parent of a component of the extended set over roots is a root of the set.** -/
theorem readout_root_parent_mem {m : ℕ} {A : Finset WordLetter} {J : ℕ} {S S' : Finset Comp}
    (hroot : ∀ v ∈ S, v.births = []) (hsub : S' ⊆ succExtComps m A J S) (c : CompIn S') :
    compParent m c.1 ∈ S := by
  rcases Finset.mem_union.mp (hsub c.2) with hc | hc
  · have hb := hroot c.1 hc
    have he : compParent m c.1 = c.1 := by simp [compParent, hb]
    rw [he]
    exact hc
  · obtain ⟨⟨u, t⟩, hut, he⟩ := Finset.mem_image.mp hc
    obtain ⟨hu, -⟩ := Finset.mem_product.mp hut
    rw [← he]
    by_cases ht0 : t = []
    · subst t
      have hb := hroot u hu
      simpa [succComp, compParent, hb] using hu
    · simpa [succComp, ht0, compParent] using hu

/-- **The readout of a realization realizes the readout** (scalar roots: the root casts are
trivial). -/
theorem readout_isFluxRealization_scalar {S S' : Finset Comp} {K : ℕ} (m : ℕ) (E η : ℝ)
    (I : Set ℝ) (F : ∀ c : CompIn S', ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ScalarH c.1.root))
    (Fk : ∀ c : CompIn S', ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => ScalarH c.1.root)))
    (hF : IsFluxRealization (ι := CompIn S') (h := fun c => ScalarH c.1.root) K I F Fk) :
    IsFluxRealization (ι := CompIn S) (h := fun v => ScalarH v.1.root) K I
      (readoutFlux (hr := ScalarH) m E η (fun _ => True) F)
      (fun v t => succReadout (hr := fun r => PiLp 2 (fun _ : Fin 2 => ScalarH r)) m E η K
        (fun c => Fk c t) v) := by
  classical
  intro v t ht
  let q (c : CompIn S') : ℝ := E ^ (η * ((compWord m c.1).length : ℝ))
  let T (c : CompIn S') : TorusHk K (PiLp 2 (fun _ : Fin 2 => ℝ)) :=
    if compParent m c.1 = v.1 then q c • Fk c t else 0
  have hread : succReadout (hr := fun r => PiLp 2 (fun _ : Fin 2 => ScalarH r)) m E η K
      (fun c => Fk c t) v = ∑ c, T c := by
    unfold succReadout
    refine Finset.sum_congr rfl fun c _ => ?_
    dsimp only [T, q]
    split_ifs <;> rfl
  have hT (c : CompIn S') : (T c).toFunction.jet (valueIndex2 K) =ᵐ[volume.restrict unitCube]
      fun x => if compParent m c.1 = v.1 then q c • F c t x else 0 := by
    dsimp only [T]
    split_ifs with hc
    · filter_upwards [KernelEnergy.torusJet_smul_ae (q c) (Fk c t) (valueIndex2 K), hF c t ht]
        with x hq hx
      rw [hq, hx]
    · filter_upwards [KernelEnergy.torusHk_toFunction_jet_ae
        (0 : TorusHk K (PiLp 2 (fun _ : Fin 2 => ℝ))) (valueIndex2 K),
        Lp.coeFn_zero (PiLp 2 (fun _ : Fin 2 => ℝ)) 2 (volume.restrict unitCube)] with x hx h0
      rw [hx]
      exact h0
  beta_reduce
  rw [hread]
  filter_upwards [KernelEnergy.torusJet_sum_ae_of_eq T (valueIndex2 K) _ hT] with x hx
  rw [hx]
  unfold readoutFlux
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hc : compParent m c.1 = v.1
  · simp only [hc, and_true, ↓reduceDIte, ↓reduceIte]
    rfl
  · simp only [hc, false_and, ↓reduceDIte, ↓reduceIte]

section Terminal

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- The filter price and `‖f‖₂` are nonnegative. -/
theorem termCtx_filterPrice_normF_nonneg
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (x : TermResAux c) (h128 : 128 ≤ A.Λ) : 0 ≤ c.filterPrice * c.normF := by
  obtain ⟨-, hq, hΛD, -, -, -, -⟩ := c.data
  have hq1 : 1 < c.D.q := hq ▸ X.hq.1
  have hΛ : 128 ≤ c.D.Λ := hΛD ▸ h128
  have he0 : ∀ k, 0 ≤ c.D.eps k := fun k => (Scales.epsilon_basic hq1 hΛ).1.le
  have hcr : (0 : ℝ) ≤ cr := x.one ▸ zero_le_one
  have hrho : 0 ≤ c.D.termRho cr M := by
    unfold OCData.termRho
    exact mul_nonneg hcr (Real.sqrt_nonneg _)
  have hrw : 0 ≤ c.D.termRW A.σw M := by
    unfold OCData.termRW
    exact Real.rpow_nonneg (he0 M) _
  refine mul_nonneg ?_ (Real.sqrt_nonneg _)
  unfold TermResCtx.filterPrice
  exact add_nonneg (Real.rpow_nonneg (he0 _) _)
    (mul_nonneg (Real.rpow_nonneg (he0 M) _) (pow_nonneg (div_nonneg hrw hrho) _))

/-- **The readout map of the filter rows at a context.** -/
theorem filterReadoutMassAt_of_rows
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) (x : TermResAux c) (kc : ℕ) (C₁ : ℝ) (h128 : 128 ≤ A.Λ) (hV : A.Valid)
    (h : FilterRowMassAt c x kc C₁) :
    FilterReadoutMassAt c x kc
      (Real.sqrt (((wordsUpTo (termAlphabet A.NT A.pT A.DW A.dW) (A.RT + 1)).card : ℝ) + 1) * C₁) := by
  obtain ⟨Fk, hreal, hmass⟩ := h
  obtain ⟨-, hq, hΛD, -, -, hband, -⟩ := c.data
  have hq1 : 1 < c.D.q := hq ▸ X.hq.1
  have hΛ : 128 ≤ c.D.Λ := hΛD ▸ h128
  have hroots : ∀ y ∈ c.Gw.comps, y.births = [] := fun y hy => c.weak.2.2.2.2.1 ⟨y, hy⟩
  have hlev : c.Gw.level = M := c.weak.2.2.1
  have hsub : c.Gt'.comps ⊆ succExtComps M (termAlphabet A.NT A.pT A.DW A.dW) A.RT
      c.Gw.comps := by
    have h1 := c.succ.2.2.1
    rw [hlev] at h1
    exact h1.subset
  have hcH : c.lawT.cH ≤ 1 := by rw [c.law.2.2.1]; exact x.cHle
  have hη0 : 0 < A.η₀ := by
    obtain ⟨-, -, -, ⟨-, -, -, -, -, -, -, hη, -⟩, -⟩ := hV
    exact hη
  have hη : 0 ≤ c.lawT.etaB := by rw [c.law.2.2.2.2.2.1]; linarith
  have hE := Scales.epsilon_basic (m := M - 1) hq1 hΛ
  have hν : 0 < c.D.κ (M - 1) :=
    CycleReference.bandChain_pos (by omega) X.hζ hband (Nat.sub_le M 1)
  have hπ : ∀ v : CompIn c.Gw.comps, 0 < c.Gw.mass c.lawW v := fun v =>
    Construction.Preservation.Buffer.birth_compMass_pos hq1 hΛ c.lawW v.1
  have hσ : ∀ v : CompIn c.Gt'.comps, 0 < c.Gt'.mass c.lawT v := fun v =>
    Construction.Preservation.Buffer.birth_compMass_pos hq1 hΛ c.lawT v.1
  have hentry : ∀ (v : CompIn c.Gw.comps) (u : CompIn c.Gt'.comps), compParent M u.1 = v.1 →
      (Real.sqrt (c.Gw.mass c.lawW v))⁻¹ / (Real.sqrt (c.Gt'.mass c.lawT u))⁻¹ *
        c.D.eps (M - 1) ^ (A.η₀ * (compWord M u.1).length) ≤ 1 := by
    intro v u huv
    have hmass : c.Gt'.mass c.lawT u ≤ c.Gw.mass c.lawW v := by
      unfold GenStage.mass
      calc compMass c.D.q c.D.Λ c.lawT u.1
          ≤ compMass c.D.q c.D.Λ c.lawT (compParent M u.1) :=
            readout_parent_mass_le hq1 hΛ c.lawT hcH hη M u.1
        _ = compMass c.D.q c.D.Λ c.lawW v.1 := by
            rw [huv]
            simp [compMass, hroots v.1 v.2, c.law.1]
    have h1 : (Real.sqrt (c.Gw.mass c.lawW v))⁻¹ / (Real.sqrt (c.Gt'.mass c.lawT u))⁻¹ ≤ 1 := by
      rw [inv_div_inv]
      exact (div_le_one (Real.sqrt_pos.mpr (hπ v))).mpr (Real.sqrt_le_sqrt hmass)
    have h2 : c.D.eps (M - 1) ^ (A.η₀ * (compWord M u.1).length) ≤ 1 :=
      Real.rpow_le_one hE.1.le hE.2.1 (mul_nonneg hη0.le (Nat.cast_nonneg _))
    calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (Real.rpow_nonneg hE.1.le _) zero_le_one
      _ = 1 := one_mul 1
  have hfiber : ∀ v : CompIn c.Gw.comps,
      ((Finset.univ : Finset (CompIn c.Gt'.comps)).filter
        fun u => compParent M u.1 = v.1).card ≤
        ((wordsUpTo (termAlphabet A.NT A.pT A.DW A.dW) (A.RT + 1)).card : ℝ) + 1 := fun v => by
    exact_mod_cast readout_root_fiber_card_le hroots hsub v.1
  refine ⟨fun v t => succReadout (hr := fun r => PiLp 2 (fun _ : Fin 2 => ScalarH r)) M
    (c.D.eps (M - 1)) A.η₀ (kc + 2 * A.pT) (fun u => Fk u t) v,
    readout_isFluxRealization_scalar M (c.D.eps (M - 1)) A.η₀ _ _ Fk hreal, ?_⟩
  obtain ⟨hm1, hm2⟩ := readout_fluxMassLe (hr := ScalarH) M (c.D.eps (M - 1)) A.η₀
    (c.D.κ (M - 1)) (c.D.termRho cr M)
    (((wordsUpTo (termAlphabet A.NT A.pT A.DW A.dW) (A.RT + 1)).card : ℝ) + 1)
    (C₁ * c.filterPrice * c.normF) (Set.Icc c.tp (c.a + A.T₀)) hν hE.1.le (by positivity)
    (c.Gw.mass c.lawW) (c.Gt'.mass c.lawT) hπ hσ (readout_root_parent_mem hroots hsub) hentry
    hfiber Fk hmass
  exact ⟨hm1, hm2.trans (le_of_eq (by ring))⟩

end Terminal

/-- **The readout of the rows** (`FilterReadoutMapStatement`): `C₂ = √(#words + 1)·C₁`. -/
theorem filterReadoutMap : FilterReadoutMapStatement := by
  intro X A kc C₁ hΛ hV _hC₁
  refine ⟨Real.sqrt (((wordsUpTo (termAlphabet A.NT A.pT A.DW A.dW) (A.RT + 1)).card : ℝ) + 1) * C₁,
    ?_⟩
  intro Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce cker j₀ M c x
    hrow C' hC'
  refine hasFluxBound_mono_Y (filterReadoutMassAt_of_rows c x kc C₁ hΛ hV hrow) ?_
  have h0 := termCtx_filterPrice_normF_nonneg c x hΛ
  calc Real.sqrt (((wordsUpTo (termAlphabet A.NT A.pT A.DW A.dW) (A.RT + 1)).card : ℝ) + 1) * C₁ *
        c.filterPrice * c.normF
      = Real.sqrt (((wordsUpTo (termAlphabet A.NT A.pT A.DW A.dW) (A.RT + 1)).card : ℝ) + 1) * C₁ *
          (c.filterPrice * c.normF) := by ring
    _ ≤ C' * (c.filterPrice * c.normF) := mul_le_mul_of_nonneg_right hC' h0
    _ = C' * c.filterPrice * c.normF := by ring

end AVRegularity.Construction.Residual.Presentation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

/-! # The factorial norms of a truncation are bounded by the `UpTo` norms

`fNS_truncate_le_upTo`: `‖truncate_n D‖²_ρ ≤ (D)_{≤ n}` (the full norm of the truncation to
order `n` is at most the partial norm up to order `n`); `gradFNS_truncate_le_upTo` is the
gradient version (truncation to order `n + 1`). This is the converse of
`factorialNormSqUpTo_le_truncate`.

Degenerate case: `D = 0`: both sides are `0`. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  {μ : Measure (Vec 2)}

/-- The value norm of a truncation is at most the partial norm. -/
theorem fNS_truncate_le_upTo {K L : ℕ} (hKL : K ≤ L) (ρ : ℝ) (D : JetL2 μ L E) :
    factorialNormSq ρ (truncateJet (E := E) hKL D) ≤ factorialNormSqUpTo ρ K D := by
  classical
  let F : Fin (L + 1) → ℝ := fun j => factorialWeight ρ j.val *
    ∑ w : DerivativeWord2 j.val, ‖D ⟨j, w⟩‖ ^ 2
  let g : Fin (L + 1) → ℝ := fun j => if j.val ≤ K then F j else 0
  have hF : ∀ j, 0 ≤ F j := fun j => mul_nonneg (factorialWeight_nonneg _ _)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hg : ∀ j, 0 ≤ g j := fun j => by
    unfold g; split_ifs
    · exact hF j
    · exact le_rfl
  change ∑ j' : Fin (K + 1), F (Fin.castLE (Nat.succ_le_succ hKL) j') ≤ ∑ j, g j
  calc ∑ j' : Fin (K + 1), F (Fin.castLE (Nat.succ_le_succ hKL) j')
      = ∑ j' : Fin (K + 1), g (Fin.castLE (Nat.succ_le_succ hKL) j') := by
        refine Finset.sum_congr rfl fun j' _ => ?_
        have : (Fin.castLE (Nat.succ_le_succ hKL) j').val ≤ K := by
          simp only [Fin.val_castLE]; omega
        simp only [g]
        split_ifs with h
        · rfl
        · exact absurd this h
    _ = ∑ j ∈ (Finset.univ : Finset (Fin (K + 1))).image (Fin.castLE (Nat.succ_le_succ hKL)),
          g j :=
        (Finset.sum_image (fun a _ b _ h => Fin.castLE_injective _ h)).symm
    _ ≤ ∑ j, g j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => hg j

/-- The gradient norm of a truncation is at most the partial gradient norm. -/
theorem gradFNS_truncate_le_upTo {K L : ℕ} (hKL : K ≤ L) (ρ : ℝ) (D : JetL2 μ (L + 1) E) :
    gradFactorialNormSq ρ (truncateJet (E := E) (Nat.succ_le_succ hKL) D) ≤
      gradFactorialNormSqUpTo ρ K D := by
  classical
  let g : Fin (L + 2) → ℝ := fun j =>
    if 1 ≤ j.val ∧ j.val ≤ K + 1 then factorialWeight ρ (j.val - 1) * derivativeNormSq D j else 0
  have hg : ∀ j, 0 ≤ g j := fun j => by
    unfold g; split_ifs
    · exact mul_nonneg (factorialWeight_nonneg _ _) (derivativeNormSq_nonneg D j)
    · exact le_rfl
  let f : Fin (K + 1) → Fin (L + 2) := fun j => ⟨j.val + 1, by omega⟩
  have hf : Function.Injective f := fun a b h => Fin.ext (by simpa [f] using h)
  change ∑ j : Fin (K + 1), factorialWeight ρ j.val *
    ∑ w : DerivativeWord2 (j.val + 1), ‖D ⟨⟨j.val + 1, by omega⟩, w⟩‖ ^ 2 ≤ ∑ j, g j
  calc _ = ∑ j : Fin (K + 1), g (f j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have : 1 ≤ (f j).val ∧ (f j).val ≤ K + 1 := by simp only [f]; omega
        simp [g, this, f, derivativeNormSq]
    _ = ∑ j ∈ (Finset.univ : Finset (Fin (K + 1))).image f, g j :=
        (Finset.sum_image (fun a _ b _ h => hf h)).symm
    _ ≤ ∑ j, g j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun j _ _ => hg j

section Energy

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- **The strong energy of the truncations to the orders `n, n + 1` is at most the `UpTo` energy
at every order `m ≥ n`.** -/
theorem strongEnergy_truncate_le_upTo {K n m : ℕ} (hn : n + 1 ≤ K) (hnm : n ≤ m)
    (ρ B : ℝ) (π : ι → ℝ) (a b : ℝ) (W : ∀ i, ℝ → TorusHk K (h i)) :
    strongEnergy ρ B π a b (fun i t => truncateTorusHk (Nat.le_of_succ_le hn) (W i t))
      (fun i t => truncateTorusHk hn (W i t)) ≤ strongEnergyUpTo ρ B π a b m W := by
  refine le_trans ?_ (CycleComparison.Reconstruction.strongEnergyUpTo_mono_order hnm ρ B π a b W)
  obtain ⟨L, rfl⟩ : ∃ L, K = L + 1 := ⟨K - 1, by omega⟩
  unfold strongEnergy strongEnergyUpTo
  refine ENNReal.rpow_le_rpow (Finset.sum_le_sum fun i _ => ?_) (by norm_num)
  refine mul_le_mul_right (add_le_add (iSup₂_mono fun t _ => ?_) (mul_le_mul_right
    (lintegral_mono fun t => ?_) _)) _
  · exact ENNReal.ofReal_le_ofReal (fNS_truncate_le_upTo (by omega) ρ (W i t).val)
  · exact ENNReal.ofReal_le_ofReal (gradFNS_truncate_le_upTo (Nat.le_of_succ_le_succ hn) ρ (W i t).val)

end Energy

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end
end
end
