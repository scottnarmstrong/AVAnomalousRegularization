-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Ledger.ActualSourceSums
public import AVRegularity.Construction.Preservation.Assembly.RetainedMarkedLedgerOfIngredients
import AVRegularity.Construction.EntryScales.TerminalCore
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy

section
@[expose] public noncomputable section
namespace AVRegularity.Construction.Preservation.Ledger

/-! Convert source sums to full ledgers and restrict without increasing any row or column. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {G G' : GenStage D hr Dm bw j₀}

theorem identityPrice_nonneg (G : GenStage D hr Dm bw j₀) (a : Comp → ℝ)
    (ha : ∀ v ∈ G.comps, 0 < a v) (e : LedgerEdge G) : 0 ≤ identityPrice G a e :=
  mul_nonneg (div_pos (ha _ e.1.2) (ha _ e.2.1.2)).le
    (mul_nonneg (mul_nonneg (norm_nonneg _) (G.fam.identity _ _ e.2.2).record.size_nonneg)
      (le_trans zero_le_one (le_max_left _ _)))

/-- Source coding bounds both orientations of the extended system. -/
theorem actual_diagonal_schur {P : ProvParams} {Mn : SuccMenu}
    (hs : IsActualSuccessor D P Mn G G')
    (hold : ∀ v ∈ G.comps, ∀ e ∈ v.births, G.level ≤ e.scale)
    (a : Comp → ℝ) (C F : ℝ) (hC : 0 ≤ C) (hF : 0 ≤ F)
    (c : LedgerEdge G → ℝ) (hc : ∀ e, 0 ≤ c e)
    {S : ℝ} (hS : 0 ≤ S) (hhalf : S ≤ 1 / 2)
    (hrow : ∀ v, ∑ u, ∑ γ, c ⟨v, u, γ⟩ ≤ S)
    (hcol : ∀ u, ∑ v, ∑ γ, c ⟨v, u, γ⟩ ≤ S)
    (E : ActualSources P Mn G G')
    (hcost : ∀ e, identityPrice G' a e ≤ sourcePrice C F c (E.source e)) :
    SchurBound (((insert [] (wordsUpTo Mn.A (Mn.J + 1))).card : ℝ) *
        (4 * C * S + 2 * (Mn.A.card : ℝ) * C * F))
      (fun v u => ∑ γ, identityPrice G' a ⟨v, u, γ⟩) := by
  classical
  constructor
  · intro v
    have hh := actual_source_sums_le hs hold a C F hC hF c hc hS hhalf hrow hcol E hcost true v
    simpa [Fintype.sum_sigma] using hh
  · intro u
    have hh := actual_source_sums_le hs hold a C F hC hF c hc hS hhalf hrow hcol E hcost false u
    simpa [Fintype.sum_sigma] using hh

/-- Restriction keeps every record and decreases each nonnegative diagonal row and column. -/
theorem restrict_diagonal_schur (G : GenStage D hr Dm bw j₀) (a : Comp → ℝ)
    (ha : ∀ v ∈ G.comps, 0 < a v) (T : Finset Comp) (hT : T ⊆ G.comps)
    {B : ℝ} (hb : SchurBound B (fun v u => ∑ γ, identityPrice G a ⟨v, u, γ⟩)) :
    SchurBound B (fun v u => ∑ γ, identityPrice (G.restrict T hT) a ⟨v, u, γ⟩) := by
  let emb := fun v : CompIn T => (⟨v.1, hT v.2⟩ : CompIn G.comps)
  have hi : Function.Injective emb := by
    intro x y h
    have hv : (emb x).1 = (emb y).1 := congrArg (fun z : CompIn G.comps => z.1) h
    exact Subtype.ext hv
  constructor
  · intro v
    change (∑ u : CompIn T, ∑ γ, identityPrice G a ⟨emb v, emb u, γ⟩) ≤ B
    exact (sum_comp_le emb hi (fun u => ∑ γ, identityPrice G a ⟨emb v, u, γ⟩)
      (fun u => Finset.sum_nonneg (fun γ _ => identityPrice_nonneg G a ha ⟨emb v, u, γ⟩))).trans
        (hb.1 (emb v))
  · intro u
    change (∑ v : CompIn T, ∑ γ, identityPrice G a ⟨emb v, emb u, γ⟩) ≤ B
    exact (sum_comp_le emb hi (fun v => ∑ γ, identityPrice G a ⟨v, emb u, γ⟩)
      (fun v => Finset.sum_nonneg (fun γ _ => identityPrice_nonneg G a ha ⟨v, emb u, γ⟩))).trans
        (hb.2 (emb u))

/-- The empty full ledger is zero; nonempty full ledgers are bounded by their two sums. -/
theorem fullLedger_le_of_schur {ι : Type*} [Fintype ι] {B : ℝ} (hB : 0 ≤ B)
    {b : ι → ι → ℝ} (hb : SchurBound B b) : fullLedger b ≤ B := by
  by_cases h : Nonempty ι
  · let := h
    exact max_le (ciSup_le hb.1) (ciSup_le hb.2)
  · let : IsEmpty ι := not_nonempty_iff.mp h
    simpa only [fullLedger, iSup_of_empty', Real.sSup_empty, max_self] using hB

/-- A Schur bound for the chosen diagonal is the corresponding ordinary or marked ledger. -/
theorem diagonal_fullLedger_le {G : GenStage D hr Dm bw j₀} (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ)
    (law : BirthLaw) (marked : Bool) {B : ℝ} (hB : 0 ≤ B)
    (hb : SchurBound B (fun v u => ∑ γ,
      identityPrice G (ledgerDiagonal D.q D.Λ law marked) ⟨v, u, γ⟩)) :
    fullLedger (pricedRecordMajorant (G.mass law)
      (fun c => ledgerMarker D.q D.Λ law marked c.1) G.fam) ≤ B := by
  apply fullLedger_le_of_schur hB
  simpa only [sum_identityPrice_eq hq hΛ law marked] using hb

end AVRegularity.Construction.Preservation.Ledger
end
end

section
section
/-! The starting level absorbs the two strictly smaller-scale terms of the ledger step. -/
@[expose] public noncomputable section
open Filter Topology
namespace AVRegularity.Construction.Preservation.Ledger

private theorem eventually_small_power {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ)
    {p : ℝ} (hp : 0 < p) (C : ℝ) {b : ℝ} (hb : 0 < b) :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m → C * ocEpsilon q Λ m ^ p ≤ b := by
  have ht := (EntryScales.epsilon_rpow_tendsto_zero hq hΛ hp).const_mul C
  rw [mul_zero] at ht
  obtain ⟨n, hn⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hb))
  exact ⟨n, fun m hm => (hn m hm).le⟩

/-- Birth decay has a positive margin over the invariant exponent, while the old ledger gains
one scale step. Both gains can be made small with a floor chosen after the finite constants. -/
theorem ledger_scale_absorption : Assembly.LedgerScaleAbsorptionStatement := by
  intro q Λ hq hq16 hΛ τ θ A B CI hτ hθ hA _hB hCI
  have hgap : 0 < θ - τ := sub_pos.mpr hθ
  have hsep : 0 < (q - 1) * τ := mul_pos (sub_pos.mpr hq) hτ
  obtain ⟨n₁, hn₁⟩ := eventually_small_power hq hΛ hτ (A * CI) (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨n₂, hn₂⟩ := eventually_small_power hq hΛ hgap B (half_pos hCI)
  obtain ⟨n₃, hn₃⟩ := eventually_small_power hq hΛ hsep (2 * A * CI * (2 : ℝ) ^ τ) (half_pos hCI)
  refine ⟨max 2 (max n₁ (max (n₂ + 1) (n₃ + 1))), le_max_left _ _, ?_⟩
  intro m hm
  have hm₂ : 2 ≤ m := (le_max_left _ _).trans hm
  have hm₁ : n₁ ≤ m := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hm
  have hmN₂ : n₂ ≤ m - 1 := by omega
  have hmN₃ : n₃ ≤ m - 1 := by omega
  have hcurr := hn₁ m hm₁
  have hbirth := hn₂ (m - 1) hmN₂
  have hcopy := hn₃ (m - 1) hmN₃
  refine ⟨by simpa only [mul_assoc] using hcurr, ?_⟩
  have he := (Scales.epsilon_basic (m := m) hq hΛ).1
  have hE := (Scales.epsilon_basic (m := m - 1) hq hΛ).1
  have hstep := Real.rpow_le_rpow he.le (Scales.epsilon_q_step hq hq16 hΛ (by omega : 1 ≤ m)) hτ.le
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.rpow_nonneg hE.le _),
    ← Real.rpow_mul hE.le] at hstep
  have hsepEq : ocEpsilon q Λ (m - 1) ^ (q * τ) =
      ocEpsilon q Λ (m - 1) ^ ((q - 1) * τ) * ocEpsilon q Λ (m - 1) ^ τ := by
    rw [← Real.rpow_add hE]
    congr 1
    ring
  have hbirthEq : ocEpsilon q Λ (m - 1) ^ θ =
      ocEpsilon q Λ (m - 1) ^ (θ - τ) * ocEpsilon q Λ (m - 1) ^ τ := by
    rw [← Real.rpow_add hE]
    congr 1
    ring
  rw [hsepEq] at hstep
  have hmultip : 0 ≤ 2 * A * CI := mul_nonneg (mul_nonneg (by norm_num) (by linarith only [hA])) hCI.le
  calc
    B * ocEpsilon q Λ (m - 1) ^ θ + 2 * A * (CI * ocEpsilon q Λ m ^ τ)
      ≤ (B * ocEpsilon q Λ (m - 1) ^ (θ - τ)) * ocEpsilon q Λ (m - 1) ^ τ +
        (2 * A * CI * (2 : ℝ) ^ τ * ocEpsilon q Λ (m - 1) ^ ((q - 1) * τ)) *
          ocEpsilon q Λ (m - 1) ^ τ := by
        rw [hbirthEq]
        have hh := mul_le_mul_of_nonneg_left hstep hmultip
        simpa only [mul_assoc] using add_le_add (le_refl (B *
          (ocEpsilon q Λ (m - 1) ^ (θ - τ) * ocEpsilon q Λ (m - 1) ^ τ))) hh
    _ ≤ (CI / 2) * ocEpsilon q Λ (m - 1) ^ τ +
          (CI / 2) * ocEpsilon q Λ (m - 1) ^ τ :=
        add_le_add (mul_le_mul_of_nonneg_right hbirth (Real.rpow_nonneg hE.le _))
          (mul_le_mul_of_nonneg_right hcopy (Real.rpow_nonneg hE.le _))
    _ = CI * ocEpsilon q Λ (m - 1) ^ τ := by ring

end AVRegularity.Construction.Preservation.Ledger
end
end

section
/-! The tagged positive-record recurrence and the retained marked-ledger conclusion under
exactly the stage-invariant binder prefix. The per-identity ledger conclusion remains
an explicit input to that conclusion; the record estimate itself follows from actual provenance. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.Ledger

/-- The fresh-letter prefactor is independent of the late root masses. -/
theorem fresh_diagonal_factor_le {D : OCData} {α q s σ : ℝ} {m Tw d : ℕ} {law : BirthLaw}
    (hDα : D.α = α) (hDq : D.q = q) (hq : 1 < q) (hΛ : 128 ≤ D.Λ)
    (hη : 0 < succEta0 α q s) (hlaw : IsSuccessorLaw α q s Tw law) (marked : Bool) :
    birthDiagonalFactor D.q D.Λ m law marked *
        D.eps (m - 1) ^ (ocDelta D.α D.q - succEta0 α q s - σ * (d : ℝ)) ≤
      Real.sqrt ((Tw : ℝ) / Assembly.successorBirthMass α q s) *
        D.eps (m - 1) ^ succTheta1 α q s σ d := by
  have hf := FullLift.successor_readout_law_facts hη hlaw
  have he := Scales.epsilon_basic (m := m - 1) (hDq.symm ▸ hq) hΛ
  have hh := mul_le_mul_of_nonneg_right
    (birthDiagonalFactor_le (hDq.symm ▸ hq) hΛ m law marked hf.2.2.2)
      (Real.rpow_nonneg he.1.le (ocDelta D.α D.q - succEta0 α q s - σ * (d : ℝ)))
  apply hh.trans_eq
  rw [mul_assoc, ← Real.rpow_add he.1, hlaw.2.2.2.1, hlaw.2.2.2.2]
  congr 2
  rw [hlaw.2.1, hlaw.2.2.1, hDα, hDq]
  unfold succTheta1
  ring

/-- Enlarge fixed finite-menu coefficients once, before choosing the starting level. -/
theorem menu_bound_le {W Tw L : ℕ} {C S F R : ℝ} (hW : W ≤ Tw + 1)
    (hC : 0 ≤ C) (hS : 0 ≤ S) (hF : 0 ≤ F) (hFR : F ≤ R) :
    (W : ℝ) * (4 * C * S + 2 * (L : ℝ) * C * F) ≤
      4 * ((Tw : ℝ) + 1) * (C + 1) * S + 2 * ((Tw : ℝ) + 1) * ((L : ℝ) + 1) * (C + 1) * R := by
  have hC1 : C ≤ C + 1 := by linarith
  have hC1pos : 0 ≤ C + 1 := hC.trans hC1
  have hL1 : (L : ℝ) ≤ (L : ℝ) + 1 := by linarith
  have hL1pos : 0 ≤ (L : ℝ) + 1 := (Nat.cast_nonneg L).trans hL1
  have hCW : (W : ℝ) ≤ (Tw : ℝ) + 1 := by exact_mod_cast hW
  have ht := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC1 (by norm_num : (0 : ℝ) ≤ 4)) hS
  have hLC := mul_le_mul hL1 hC1 hC hL1pos
  have hLC2 := mul_le_mul_of_nonneg_left hLC (by norm_num : (0 : ℝ) ≤ 2)
  have hb := mul_le_mul hLC2 hFR hF (mul_nonneg (by norm_num) (mul_nonneg hL1pos hC1pos))
  have hin := add_le_add ht hb
  have hsum : 0 ≤ 4 * C * S + 2 * (L : ℝ) * C * F := by positivity
  have hh := mul_le_mul hCW hin (by simpa only [mul_assoc] using hsum) (by positivity : 0 ≤ (Tw : ℝ) + 1)
  nlinarith only [hh]

/-- The structural recurrence of the ordinary and marked inflated record ledgers. -/
theorem full_tagged_ledger_recurrence : Assembly.FullTaggedLedgerRecurrenceStatement := by
  classical
  intro hr _ _ D Dm bw j₀ α s q hDα hDq hq hΛ hη Cw cr σ₀ N p d Mn hCw hσ hletters
    law hlaw G G' hG hold hs _hm S hS hledger hsmall
  have hqD : 1 < D.q := hDq.symm ▸ hq
  have he := Scales.epsilon_basic (m := G.level - 1) hqD hΛ
  have hf := FullLift.successor_readout_law_facts hη hlaw
  have hA : 1 ≤ Assembly.ledgerTransportConstant Cw (wordsUpTo Mn.A (Mn.J + 1)).card := by
    unfold Assembly.ledgerTransportConstant
    have ht : 0 ≤ ((wordsUpTo Mn.A (Mn.J + 1)).card : ℝ) := Nat.cast_nonneg _
    nlinarith only [hCw, ht]
  have hhalf : S ≤ 1 / 2 := (le_mul_of_one_le_left hS hA).trans hsmall
  let E := Classical.choice (actual_sources hs)
  let B := Assembly.ledgerBirthConstant α q s Cw (wordsUpTo Mn.A (Mn.J + 1)).card Mn.A.card *
    D.eps (G.level - 1) ^ succTheta1 α q s σ₀ d +
      2 * Assembly.ledgerTransportConstant Cw (wordsUpTo Mn.A (Mn.J + 1)).card * S
  have hE : 0 ≤ D.eps (G.level - 1) := he.1.le
  have hB : 0 ≤ B := by dsimp [B, Assembly.ledgerBirthConstant, Assembly.ledgerTransportConstant]; positivity
  have hbound (marked : Bool) :
      fullLedger (pricedRecordMajorant (G'.mass law)
        (fun c => ledgerMarker D.q D.Λ law marked c.1) G'.fam) ≤ B := by
    let a := ledgerDiagonal D.q D.Λ law marked
    let F := birthDiagonalFactor D.q D.Λ G.level law marked
    let Ffresh := F * D.eps (G.level - 1) ^ (ocDelta D.α D.q - succEta0 α q s - σ₀ * (d : ℝ))
    have ha : ∀ v ∈ G.comps, 0 < a v := fun v _ => ledgerDiagonal_pos hqD hΛ law marked v
    have hF : 1 ≤ F := one_le_birthDiagonalFactor hqD hΛ G.level law marked hf.1 hf.2.1 hf.2.2.2
    have hF0 : 0 ≤ Ffresh := mul_nonneg (le_trans zero_le_one hF) (Real.rpow_nonneg he.1.le _)
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
      have hh := source_record_price_le a ha hCw.le he.1 he.2.1 hσ (le_trans zero_le_one hF)
        rfl hletters hG (E.source e) (E.valid e) (G'.fam.identity e.1 e.2.1 e.2.2).record
        (E.tags e) e.2.1.1.root e.1.1.root (a e.1.1 / a e.2.1.1) hratio
      simpa only [identityPrice, E.map_eq e, Ffresh, c, OCData.eps] using hh
    have hschur := actual_diagonal_schur hs hold a Cw Ffresh hCw.le hF0 c hc hS hhalf
      hrowcol.1 hrowcol.2 E hcost
    have hFR := fresh_diagonal_factor_le (σ := σ₀) (d := d) (m := G.level)
      hDα hDq hq hΛ hη hlaw marked
    have hmenu := menu_bound_le (L := Mn.A.card) (Finset.card_insert_le [] (wordsUpTo Mn.A (Mn.J + 1)))
      hCw.le hS hF0 hFR
    have hmenu' : ((insert [] (wordsUpTo Mn.A (Mn.J + 1))).card : ℝ) *
        (4 * Cw * S + 2 * (Mn.A.card : ℝ) * Cw * Ffresh) ≤ B := by
      apply hmenu.trans_eq
      dsimp only [B, Assembly.ledgerTransportConstant, Assembly.ledgerBirthConstant]
      ring
    apply diagonal_fullLedger_le hqD hΛ law marked hB
    exact ⟨fun v => (hschur.1 v).trans hmenu', fun u => (hschur.2 u).trans hmenu'⟩
  exact max_le (hbound false) (hbound true)

/-- Restrict the full recurrence without repeating the fresh-prefix or source-sum proof. -/
theorem tagged_ledger_recurrence : Assembly.TaggedLedgerRecurrenceStatement := by
  classical
  intro hr _ _ D Dm bw j₀ α s q hDα hDq hq hΛ hη Cw cr σ₀ N p d Mn hCw hσ hletters
    law hlaw G G' hG hold hs hm S hS hledger hsmall H J
  let B := Assembly.ledgerBirthConstant α q s Cw (wordsUpTo Mn.A (Mn.J + 1)).card Mn.A.card *
    D.eps (G.level - 1) ^ succTheta1 α q s σ₀ d +
      2 * Assembly.ledgerTransportConstant Cw (wordsUpTo Mn.A (Mn.J + 1)).card * S
  have hε : 0 ≤ D.eps (G.level - 1) := (Scales.epsilon_basic (hDq.symm ▸ hq) hΛ).1.le
  have hB : 0 ≤ B := by
    dsimp only [B, Assembly.ledgerBirthConstant, Assembly.ledgerTransportConstant]
    positivity
  have hfull := full_tagged_ledger_recurrence hr D Dm bw j₀ α s q hDα hDq hq hΛ hη
    Cw cr σ₀ N p d Mn hCw hσ hletters law hlaw G G' hG hold hs hm S hS hledger hsmall
  have hqD : 1 < D.q := hDq.symm ▸ hq
  have hbound (marked : Bool) :
      fullLedger (pricedRecordMajorant ((G'.retained G.level H J).mass law)
        (fun c => ledgerMarker D.q D.Λ law marked c.1) (G'.retained G.level H J).fam) ≤ B := by
    have hh : fullLedger (pricedRecordMajorant (G'.mass law)
        (fun c => ledgerMarker D.q D.Λ law marked c.1) G'.fam) ≤ B := by
      cases marked with
      | false => exact (le_max_left _ _).trans hfull
      | true => exact (le_max_right _ _).trans hfull
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
  exact max_le (hbound false) (hbound true)

/-- The retained marked-ledger statement, with the successor-ledger conclusion and the
stage-invariant binder prefix. -/
theorem retained_marked_ledger (α s q : ℝ) (ζ : ℝ → ℝ) :
    Assembly.RetainedMarkedLedgerStatement α s q ζ :=
  Assembly.retained_marked_ledger_of_ingredients tagged_ledger_recurrence ledger_scale_absorption α s q ζ

end AVRegularity.Construction.Preservation.Ledger
end
end
end
