-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Ledger.ActualSourceSums
import AVRegularity.Construction.Preservation.Ledger.TaggedRecurrence
public import AVRegularity.Construction.Preservation.Assembly.RetainedMarkedLedgerOfIngredients
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
public import AVRegularity.Construction.Preservation.Frontier.LengthRows.Producer
import AVRegularity.CycleComparison.Coarse.SecondOrderResponse
import AVRegularity.Construction.Preservation.FullLift.NativeHigherRetainedFromSameOrder
public import AVRegularity.Construction.Preservation.Frontier.GradeRows.Producer
import AVRegularity.Construction.EntryScales.TerminalCore
import AVRegularity.Construction.InitialValue.Cascade
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarCellStrongTime
import AVRegularity.Construction.Preservation.Frontier.GradeRows.ExtendedCertificates
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
import AVRegularity.Construction.Preservation.FullLift.NativeChartDiagonalRegularity

@[expose] public noncomputable section
section

section
open Homogenization
namespace AVRegularity.Construction.Preservation.Frontier.LengthPrice

/-! Fresh sources use the existing positive-path sum with no copied-edge contribution.
The endpoint coding and injectivity are shared with the full-ledger recurrence. -/

section
open Ledger
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {G G' : GenStage D hr Dm bw j₀}

/-- The source cost restricted to letter edges.
The degenerate cases are included: copied edges cost zero; a diagonal letter has no old path factor.
-/
def freshSourceCost (C F : ℝ) (c : LedgerEdge G → ℝ) (s : SuccSource G) : ℝ :=
  if s.letter? = none then 0 else sourcePrice C F c s

/-- The same restriction on the overcounting finite codes. -/
def freshCodeCost (C F : ℝ) (c : LedgerEdge G → ℝ) {A : Finset WordLetter} {J R : ℕ}
    (z : SourceCode G A J R) : ℝ :=
  match z.2 with
  | .inl _ => 0
  | .inr _ => codePrice C F c z

theorem fresh_source_cost_nonneg (C F : ℝ) (hC : 0 ≤ C) (hF : 0 ≤ F)
    (c : LedgerEdge G → ℝ) (hc : ∀ e, 0 ≤ c e) (s : SuccSource G) :
    0 ≤ freshSourceCost C F c s := by
  cases s with
  | copyDir => exact le_rfl
  | copyQuad => exact le_rfl
  | letterDiag => exact mul_nonneg hC hF
  | letterMean t n h π | letterCov t n h a a' π =>
    exact mul_nonneg (mul_nonneg hC hF) (positivePathWeight_nonneg c hc π)

private theorem fresh_code_nonneg (C F : ℝ) (hC : 0 ≤ C) (hF : 0 ≤ F)
    (c : LedgerEdge G → ℝ) (hc : ∀ e, 0 ≤ c e) {A : Finset WordLetter} {J R : ℕ}
    (z : SourceCode G A J R) : 0 ≤ freshCodeCost C F c z := by
  rcases z with ⟨t, z⟩
  cases z with
  | inl z => exact le_rfl
  | inr z => exact codePrice_nonneg C F hC hF c hc (t, Sum.inr z)

private theorem fresh_encode_price (C F : ℝ) (c : LedgerEdge G → ℝ)
    (A : Finset WordLetter) (J R : ℕ) (s : SuccSource G)
    (hv : s.Valid A J) (hb : s.pathLen ≤ R) :
    freshCodeCost C F c (encodeSource A J R s hv hb) = freshSourceCost C F c s := by
  cases s <;> simp [freshCodeCost, freshSourceCost, encodeSource, codePrice,
    sourcePrice, SuccSource.letter?, positivePathWeight]

/-- Fresh path menus cost at most twice the diagonal menu per letter, independently of the
number of old components and the maximum path length.
The degenerate cases are included: empty and singleton old families, an edgeless seed, zero old
ledger and an empty alphabet. All sums are nonnegative; no solution norm or ledger is divided by. -/
theorem fresh_code_sum_le (C F : ℝ) (hC : 0 ≤ C) (hF : 0 ≤ F)
    (c : LedgerEdge G → ℝ) (hc : ∀ e, 0 ≤ c e)
    {S : ℝ} (hS : 0 ≤ S) (hhalf : S ≤ 1 / 2)
    (hrow : ∀ v, ∑ u, ∑ γ, c ⟨v, u, γ⟩ ≤ S)
    (hcol : ∀ u, ∑ v, ∑ γ, c ⟨v, u, γ⟩ ≤ S)
    (row : Bool) (A : Finset WordLetter) (J R : ℕ) (v : CompIn G.comps) :
    (∑ z : SourceCode G A J R,
      if codeEndpoint row z = v.1 then freshCodeCost C F c z else 0) ≤
      ((insert [] (wordsUpTo A (J + 1))).card : ℝ) * (2 * (A.card : ℝ) * C * F) := by
  classical
  have hp := positive_path_sum_le c hc hS hhalf hrow hcol row R v
  have hdiag : (∑ u : CompIn G.comps, if u.1 = v.1 then C * F else 0) = C * F := by
    simp only [Subtype.val_inj]
    simp
  have hfresh : (∑ h : Fin (R + 2), ∑ π : StagePath G h.1,
      if pathEndpoint row π = v.1 then C * F * positivePathWeight c π else 0) ≤ C * F := by
    have heq : (∑ h : Fin (R + 2), ∑ π : StagePath G h.1,
        if pathEndpoint row π = v.1 then C * F * positivePathWeight c π else 0) =
        (C * F) * (∑ h : Fin (R + 2), ∑ π : StagePath G h.1,
          if pathEndpoint row π = v.1 then positivePathWeight c π else 0) := by
      simp only [Finset.mul_sum, mul_ite, mul_zero]
    rw [heq]
    exact (mul_le_mul_of_nonneg_left hp (mul_nonneg hC hF)).trans
      (by nlinarith only [hhalf, mul_nonneg hC hF])
  simp only [SourceCode, Fintype.sum_prod_type, Fintype.sum_sum_type, Fintype.sum_sigma]
  refine (Finset.sum_le_sum (s := Finset.univ)
    (g := fun _t : {t : List WordLetter // t ∈ insert [] (wordsUpTo A (J + 1))} =>
      2 * (A.card : ℝ) * C * F) (fun t _ => ?_)).trans ?_
  swap
  · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_coe, le_refl]
  have henddiag (t) (l) (u : CompIn G.comps) :
      codeEndpoint (A := A) (J := J) (R := R) row (t, Sum.inr (l, Sum.inl u)) = u.1 := by
    cases row <;> rfl
  have hendfresh (t) (l) (h : Fin (R + 2)) (π : StagePath G h.1) :
      codeEndpoint (A := A) (J := J) (R := R) row (t, Sum.inr (l, Sum.inr ⟨h, π⟩)) =
        pathEndpoint row π := by cases row <;> rfl
  simp only [freshCodeCost, ite_self, Finset.sum_const_zero, zero_add,
    henddiag, hendfresh, codePrice, hdiag]
  calc
    _ ≤ ∑ _l : {l : WordLetter // l ∈ A}, 2 * C * F := by
      apply Finset.sum_le_sum
      intro l _
      linarith only [hfresh]
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_coe]; ring

/-- Actual fresh source costs satisfy both Schur sums with the same finite-menu constant. -/
theorem fresh_actual_schur {P : ProvParams} {Mn : SuccMenu}
    (hs : IsActualSuccessor D P Mn G G')
    (hold : ∀ v ∈ G.comps, ∀ e ∈ v.births, G.level ≤ e.scale)
    (price : LedgerEdge G' → ℝ) (E : ActualSources P Mn G G')
    (C F : ℝ) (hC : 0 ≤ C) (hF : 0 ≤ F)
    (c : LedgerEdge G → ℝ) (hc : ∀ e, 0 ≤ c e)
    {S : ℝ} (hS : 0 ≤ S) (hhalf : S ≤ 1 / 2)
    (hrow : ∀ v, ∑ u, ∑ γ, c ⟨v, u, γ⟩ ≤ S)
    (hcol : ∀ u, ∑ v, ∑ γ, c ⟨v, u, γ⟩ ≤ S)
    (hcost : ∀ e, price e ≤ freshSourceCost C F c (E.source e)) :
    SchurBound (((insert [] (wordsUpTo Mn.A (Mn.J + 1))).card : ℝ) *
        (2 * (Mn.A.card : ℝ) * C * F)) (fun v u => ∑ γ, price ⟨v, u, γ⟩) := by
  classical
  have hh (row : Bool) (v : CompIn G'.comps) :=
    actual_source_sums_le_of_code hs hold price E (freshSourceCost C F c)
      (fun _ => freshCodeCost C F c) (fun _ z => fresh_code_nonneg C F hC hF c hc z)
      (fun R s hv hb => fresh_encode_price C F c Mn.A Mn.J R s hv hb)
      (fun R row v => fresh_code_sum_le C F hC hF c hc hS hhalf hrow hcol row Mn.A Mn.J R v)
      hcost row v
  constructor
  · intro v
    simpa [Fintype.sum_sigma] using hh true v
  · intro u
    simpa [Fintype.sum_sigma] using hh false u
end

/-! The selected fresh records have the first-prefix exponent only at the empty source word.
Every later prefix cancels the common birth diagonal exactly. -/

section
open Ledger
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {G G' : GenStage D hr Dm bw j₀}

private theorem append_diagonal_ratio (a : Comp → ℝ) {F : ℝ} (hF : 0 < F)
    (hword : ∀ v ∈ G.comps, ∀ t, a (succComp G.level v t) =
      (if t = [] then 1 else F) * a v)
    (v u : CompIn G.comps) (t : List WordLetter) (l : WordLetter) :
    a (succComp G.level v.1 (t ++ [l])) / a (succComp G.level u.1 t) =
      (if t = [] then F else 1) * (a v.1 / a u.1) := by
  rw [hword _ v.2, hword _ u.2]
  have ht : t ++ [l] ≠ [] := by simp
  by_cases he : t = []
  · simp only [ite_eq_right ht, ite_eq_left he, one_mul]
    exact mul_div_assoc _ _ _
  · simp only [ite_eq_right ht, ite_eq_right he, one_mul]
    exact mul_div_mul_left _ _ hF.ne'

/-- The single birth multiplier occurs only at the empty input word. -/
theorem fresh_source_diagonal_ratio (a : Comp → ℝ) {F : ℝ} (hF : 0 < F)
    (hword : ∀ v ∈ G.comps, ∀ t, a (succComp G.level v t) =
      (if t = [] then 1 else F) * a v)
    (s : SuccSource G) (hmem : s.oldTgt ∈ G.comps ∧ s.oldSrc ∈ G.comps)
    (hfresh : s.letter? ≠ none) :
    a (s.tgtComp G.level) / a (s.srcComp G.level) =
      (if s.word = [] then F else 1) * (a s.oldTgt / a s.oldSrc) := by
  cases hl : s.letter? with
  | none => exact (hfresh hl).elim
  | some l =>
    unfold SuccSource.tgtComp SuccSource.srcComp SuccSource.newWord
    rw [hl]
    exact append_diagonal_ratio a hF hword ⟨s.oldTgt, hmem.1⟩ ⟨s.oldSrc, hmem.2⟩ s.word l

/-- Word lengths of the actual endpoints recover the source word and force a fresh letter.
For length one the source word is empty; a later prefix is nonempty. No grade restriction
is needed, so the result applies to every selected submatrix of these endpoints. -/
theorem fresh_source_of_lengths {P : ProvParams} {Mn : SuccMenu}
    (hs : IsActualSuccessor D P Mn G G')
    (hold : ∀ v ∈ G.comps, ∀ e ∈ v.births, G.level ≤ e.scale)
    (E : ActualSources P Mn G G') (e : LedgerEdge G') {l : ℕ} (hl : 1 ≤ l)
    (ht : (compWord G.level e.1.1).length = l)
    (hu : (compWord G.level e.2.1.1).length = l - 1) :
    (E.source e).letter? ≠ none ∧ (E.source e).word.length = l - 1 := by
  have hmem := source_old_mem (E.source e) (E.valid e)
  have hsrc := (FullLift.parent_word_succComp hs.1 _ (hold _ hmem.2) (E.source e).word).2
  have htgt := (FullLift.parent_word_succComp hs.1 _ (hold _ hmem.1) (E.source e).newWord).2
  change compWord G.level ((E.source e).srcComp G.level) = _ at hsrc
  change compWord G.level ((E.source e).tgtComp G.level) = _ at htgt
  rw [E.src e] at hsrc
  rw [E.tgt e] at htgt
  have hlen : (E.source e).word.length = l - 1 := by rw [← hsrc]; exact hu
  refine ⟨?_, hlen⟩
  intro hnone
  have hnew : (E.source e).newWord = (E.source e).word := by
    simp only [SuccSource.newWord, hnone]
  rw [hnew] at htgt
  have hlen' : (E.source e).word.length = l := by rw [← htgt]; exact ht
  omega

/-- Selected fresh identity records at every prefix have the sharp marked Schur price.
The constant is fixed by the finite alphabet, witness constant and birth mass, before
root spaces, stage components and the solution. The incoming marked ledger is used only
through its bound by one half, to sum old positive paths.
No marked norm or old ledger is divided by. -/
theorem fresh_record_schur {α s q Cw cr σ : ℝ} {N p d : ℕ} {Mn : SuccMenu}
    (hDα : D.α = α) (hDq : D.q = q) (hq : 1 < q) (hΛ : 128 ≤ D.Λ)
    (hη : 0 < succEta0 α q s) (hCw : 0 ≤ Cw) (hσ : 0 ≤ σ)
    (hletters : ∀ l ∈ Mn.A, letterOrder N p l - 2 ≤ d)
    (law : BirthLaw) (hlaw : IsSuccessorLaw α q s (wordsUpTo Mn.A (Mn.J + 1)).card law)
    (hG : G.HasTags (succProvParams D Cw cr σ (succEta0 α q s) N p))
    (hold : ∀ v ∈ G.comps, ∀ e ∈ v.births, G.level ≤ e.scale)
    (hs : IsActualSuccessor D (succProvParams D Cw cr σ (succEta0 α q s) N p) Mn G G')
    {S : ℝ} (hS : 0 ≤ S) (hhalf : S ≤ 1 / 2)
    (hledger : markedLedger (G.mass law) (G.marker law) G.fam ≤ S)
    (l : ℕ) (hl : 1 ≤ l) (Q : LedgerEdge G' → Prop) [DecidablePred Q]
    (hQ : ∀ e, Q e → (compWord G.level e.1.1).length = l ∧
      (compWord G.level e.2.1.1).length = l - 1) :
    SchurBound
      ((2 * ((insert [] (wordsUpTo Mn.A (Mn.J + 1))).card : ℝ) * (Mn.A.card : ℝ) * Cw *
          (1 + Real.sqrt (((wordsUpTo Mn.A (Mn.J + 1)).card : ℝ) / Assembly.successorBirthMass α q s))) *
        D.eps (G.level - 1) ^ (if l = 1 then succTheta1 α q s σ d else succTheta2 α q s σ d))
      (fun v u => ∑ γ, if Q ⟨v, u, γ⟩ then
        identityPrice G' (ledgerDiagonal D.q D.Λ law true) ⟨v, u, γ⟩ else 0) := by
  classical
  have hqD : 1 < D.q := hDq.symm ▸ hq
  have he := Scales.epsilon_basic (m := G.level - 1) hqD hΛ
  let a := ledgerDiagonal D.q D.Λ law true
  let c := identityPrice G a
  let F := if l = 1 then birthDiagonalFactor D.q D.Λ G.level law true else 1
  let Ffresh := F * D.eps (G.level - 1) ^ (ocDelta D.α D.q - succEta0 α q s - σ * (d : ℝ))
  let E := Classical.choice (actual_sources hs)
  have ha : ∀ v ∈ G.comps, 0 < a v := fun v _ => ledgerDiagonal_pos hqD hΛ law true v
  have hc : ∀ e, 0 ≤ c e := identityPrice_nonneg G a ha
  have hF : 0 < F := by
    dsimp only [F]
    split <;> [exact birthDiagonalFactor_pos hqD hΛ _ law true; exact zero_lt_one]
  have hFfresh : 0 ≤ Ffresh := mul_nonneg hF.le (Real.rpow_nonneg he.1.le _)
  have hrowcol : SchurBound S (fun v u => ∑ γ, c ⟨v, u, γ⟩) := by
    have hh := (le_max_right _ _).trans hledger
    have hb := FullLift.fullLedger_schur_bound
      (pricedRecordMajorant (G.mass law) (G.marker law) G.fam)
    have hb' : SchurBound S (pricedRecordMajorant (G.mass law) (G.marker law) G.fam) :=
      ⟨fun v => (hb.1 v).trans hh, fun u => (hb.2 u).trans hh⟩
    have heq : (fun v u => ∑ γ, c ⟨v, u, γ⟩) =
        pricedRecordMajorant (G.mass law) (G.marker law) G.fam := by
      funext v u
      rw [show c = identityPrice G (ledgerDiagonal D.q D.Λ law true) from rfl,
        sum_identityPrice_eq hqD hΛ law true]
      rfl
    rw [heq]
    exact hb'
  have hcost (e : LedgerEdge G') : (if Q e then identityPrice G' a e else 0) ≤
      freshSourceCost Cw Ffresh c (E.source e) := by
    by_cases hsel : Q e
    · have hends := hQ e hsel
      obtain ⟨hfresh, hlen⟩ := fresh_source_of_lengths hs hold E e hl hends.1 hends.2
      have hword : ((E.source e).word = []) ↔ l = 1 := by
        rw [← List.length_eq_zero_iff, hlen]
        omega
      have hratio := fresh_source_diagonal_ratio a
        (birthDiagonalFactor_pos hqD hΛ G.level law true)
        (fun v hv t => ledgerDiagonal_succComp hqD hΛ hs.1 law true v (hold v hv) t)
        (E.source e) (source_old_mem (E.source e) (E.valid e)) hfresh
      rw [E.tgt e, E.src e] at hratio
      simp only [hword] at hratio
      have hratio' : a e.1.1 / a e.2.1.1 ≤
          (if (E.source e).letter? = none then 1 else F) *
            (a (E.source e).oldTgt / a (E.source e).oldSrc) := by
        simpa only [hfresh, ite_false, F] using hratio.le
      have hh := source_record_price_le a ha hCw he.1 he.2.1 hσ hF.le rfl hletters hG
        (E.source e) (E.valid e) (G'.fam.identity e.1 e.2.1 e.2.2).record (E.tags e)
        e.2.1.1.root e.1.1.root (a e.1.1 / a e.2.1.1) hratio'
      simpa only [hsel, ite_true, freshSourceCost, hfresh, ite_false, identityPrice,
        E.map_eq e, Ffresh, c, OCData.eps] using hh
    · simpa only [hsel, ite_false] using
        fresh_source_cost_nonneg Cw Ffresh hCw hFfresh c hc (E.source e)
  have hschur := fresh_actual_schur hs hold (fun e => if Q e then identityPrice G' a e else 0)
    E Cw Ffresh hCw hFfresh c hc hS hhalf hrowcol.1 hrowcol.2 hcost
  let R := 1 + Real.sqrt (((wordsUpTo Mn.A (Mn.J + 1)).card : ℝ) / Assembly.successorBirthMass α q s)
  have hR : 1 ≤ R := le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have hFF : Ffresh ≤ R * D.eps (G.level - 1) ^
      (if l = 1 then succTheta1 α q s σ d else succTheta2 α q s σ d) := by
    by_cases hl1 : l = 1
    · simp only [Ffresh, F, hl1, ite_true]
      exact (fresh_diagonal_factor_le hDα hDq hq hΛ hη hlaw true).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one)
          (Real.rpow_nonneg he.1.le _))
    · simp only [Ffresh, F, hl1, ite_false, one_mul]
      have hexp : ocDelta D.α D.q - succEta0 α q s - σ * (d : ℝ) = succTheta2 α q s σ d := by
        rw [hDα, hDq]
        unfold succTheta2
        ring
      rw [hexp]
      exact le_mul_of_one_le_left (Real.rpow_nonneg he.1.le _) hR
  have hb : ((insert [] (wordsUpTo Mn.A (Mn.J + 1))).card : ℝ) *
      (2 * (Mn.A.card : ℝ) * Cw * Ffresh) ≤
        (2 * ((insert [] (wordsUpTo Mn.A (Mn.J + 1))).card : ℝ) * (Mn.A.card : ℝ) * Cw * R) *
          D.eps (G.level - 1) ^
            (if l = 1 then succTheta1 α q s σ d else succTheta2 α q s σ d) := by
    calc
      _ = (2 * ((insert [] (wordsUpTo Mn.A (Mn.J + 1))).card : ℝ) * (Mn.A.card : ℝ) * Cw) * Ffresh := by ring
      _ ≤ (2 * ((insert [] (wordsUpTo Mn.A (Mn.J + 1))).card : ℝ) * (Mn.A.card : ℝ) * Cw) *
          (R * D.eps (G.level - 1) ^
            (if l = 1 then succTheta1 α q s σ d else succTheta2 α q s σ d)) :=
        mul_le_mul_of_nonneg_left hFF (by positivity)
      _ = _ := by ring
  exact ⟨fun v => (hschur.1 v).trans hb, fun u => (hschur.2 u).trans hb⟩
end

end AVRegularity.Construction.Preservation.Frontier.LengthPrice
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Frontier.LengthPrice

/-! Selecting fresh edges preserves the native regularizers and the supplied higher values.
The Schur parameter is the minimum of the native parameter and the sharp prefix price;
thus the construction needs no second smallness threshold. -/

section
open KernelEnergy
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- A sharp Schur bound on the fresh submatrix packages the price required by the length
rows, preserving every kernel and higher-value identity.
The degenerate cases are included: an empty family or empty selection has zero flux; a singleton and
l=1 need no special argument; zero prices and zero data are allowed. No scalar norm is divided by.
-/
theorem fresh_prefix_price_of_schur (F : Frame D hr Dm bw j₀) (l : ℕ) (C : ℝ)
    (P : F.KernelOp)
    (hB : P.B = fun (v u : CompIn F.G'.comps) (γ : F.G'.fam.Γ v u)
      (d : ↥(Finset.Icc 2 Dm)) => F.G'.physCoeff v u γ d.1)
    (hC : P.C = fun (v u : CompIn F.G'.comps) (_ : F.G'.fam.Γ v u) =>
      ContinuousLinearMap.id ℝ (hr u.1.root))
    (hπ : P.π = fun v => F.G'.mass F.law v / F.G'.marker F.law v ^ 2)
    (hc : ∀ d, d + 2 ≤ Dm → 0 ≤ P.c d) (hθ : 0 ≤ P.θ)
    (hg : 0 ≤ C * D.eps (F.m - 1) ^ F.lengthExponent l)
    (hsharp : SchurBound (C * D.eps (F.m - 1) ^ F.lengthExponent l)
      (kernelSchurMatrix (D.κ (F.m - 1)) (rhoEnh D F.cr F.m) P.π F.k Dm F.tp F.tf
        P.c P.r P.C (F.freshCoeff l)))
    (hy : ∀ v u (γ : F.G'.fam.Γ v u) (hu : IsRetained F.m F.H F.J u.1),
      ∀ᵐ t ∂volume.restrict (Set.Icc F.tp F.tf),
        (F.yom v u γ t).val (valueIndex2 (F.k + Dm - 1)) =
          P.S v u γ t ((F.Yw ⟨u.1, Finset.mem_filter.2 ⟨u.2, hu⟩⟩ t).val
            (valueIndex2 (F.k + 1)))) :
    FreshPrefixOperatorStatement F l C := by
  classical
  let b := kernelSchurMatrix (D.κ (F.m - 1)) (rhoEnh D F.cr F.m) P.π F.k Dm F.tp F.tf
    P.c P.r P.C P.B
  let bf := kernelSchurMatrix (D.κ (F.m - 1)) (rhoEnh D F.cr F.m) P.π F.k Dm F.tp F.tf
    P.c P.r P.C (F.freshCoeff l)
  have hb0 (v u) : 0 ≤ b v u := by
    apply mul_nonneg (Real.sqrt_nonneg _)
    apply Finset.sum_nonneg
    intro γ _
    apply mul_nonneg (norm_nonneg _)
    apply Finset.sum_nonneg
    intro d _
    exact div_nonneg (mul_nonneg ENNReal.toReal_nonneg (hc _ (by
      have hd := Finset.mem_Icc.mp d.property
      omega))) (mul_nonneg P.diffusivity_pos.le (pow_nonneg (P.hr v u γ).le _))
  have hbf (v u) : bf v u = if F.IsFreshEdge l v u then b v u else 0 := by
    by_cases he : F.IsFreshEdge l v u
    · simp only [bf, b, kernelSchurMatrix, Frame.freshCoeff, he, ite_true, hB]
    · simp only [bf, kernelSchurMatrix, Frame.freshCoeff, he, ite_false,
        CycleComparison.Coarse.coefficientSeminorm_zero_coefficient, ENNReal.toReal_zero,
        zero_mul, zero_div, Finset.sum_const_zero, mul_zero]
  have hle (v u) : bf v u ≤ b v u := by
    rw [hbf]
    split
    · exact le_rfl
    · exact hb0 v u
  have hnative : SchurBound P.θ bf :=
    ⟨fun v => (Finset.sum_le_sum (fun u _ => hle v u)).trans (P.hschur.1 v),
      fun u => (Finset.sum_le_sum (fun v _ => hle v u)).trans (P.hschur.2 u)⟩
  let R : F.KernelOp := {
    htime := P.htime
    radius_pos := P.radius_pos
    diffusivity_pos := P.diffusivity_pos
    order_ge_two := P.order_ge_two
    π := P.π
    hπ := P.hπ
    B := F.freshCoeff l
    hB_meas := by
      intro v u γ d
      by_cases he : F.IsFreshEdge l v u
      · simpa only [Frame.freshCoeff, he, ite_true, hB] using P.hB_meas v u γ d
      · simpa only [Frame.freshCoeff, he, ite_false, Pi.zero_apply] using
          (measurable_const : Measurable (fun _ : Set.Icc F.tp F.tf × Vec 2 =>
            (0 : (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => hr u.1.root)) →L[ℝ]
              (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))))
    hB_smooth := by
      intro v u γ d t ht
      by_cases he : F.IsFreshEdge l v u
      · simpa only [Frame.freshCoeff, he, ite_true, hB] using P.hB_smooth v u γ d t ht
      · simpa only [Frame.freshCoeff, he, ite_false, Pi.zero_apply, Pi.zero_def] using
          (contDiff_const : ContDiff ℝ (F.k : ℕ) (fun _ : Vec 2 =>
            (0 : (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => hr u.1.root)) →L[ℝ]
              (PiLp 2 (fun _ : Fin 2 => hr v.1.root)))))
    hB_per := by
      intro v u γ d t ht
      by_cases he : F.IsFreshEdge l v u
      · simpa only [Frame.freshCoeff, he, ite_true, hB] using P.hB_per v u γ d t ht
      · intro x z
        simp only [Frame.freshCoeff, he, ite_false, Pi.zero_apply]
    hB_fin := by
      intro v u γ d
      by_cases he : F.IsFreshEdge l v u
      · simpa only [Frame.freshCoeff, he, ite_true, hB] using P.hB_fin v u γ d
      · simp only [Frame.freshCoeff, he, ite_false,
          CycleComparison.Coarse.coefficientSeminorm_zero_coefficient, ne_eq,
          ENNReal.zero_ne_top, not_false_eq_true]
    C := P.C
    S := P.S
    c := P.c
    r := P.r
    hr := P.hr
    hS := P.hS
    θ := min P.θ (C * D.eps (F.m - 1) ^ F.lengthExponent l)
    hθ := (min_le_left _ _).trans P.hθ
    hschur := ⟨fun v => le_min (hnative.1 v) (hsharp.1 v),
      fun u => le_min (hnative.2 u) (hsharp.2 u)⟩ }
  exact ⟨R, rfl, hC, hπ, le_min hθ hg, min_le_right _ _, hy⟩
end

/-! The literal fresh-prefix price, from the existing native identity estimate and the
sharp finite source sum. Constants depend on the finite menu and the native estimate,
never on a root-space dimension, late birth law, stage or solution. -/

section
open Ledger FullLift KernelEnergy AVRegularity.Construction.Preservation.Assembly RetainedEnergy
open scoped Classical
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- The finite fresh-prefix constant. The birth mass is fixed before all stage data. -/
def freshPrefixConstant (α q s Cw A : ℝ) (Mn : SuccMenu) : ℝ :=
  A * (2 * ((insert [] (wordsUpTo Mn.A (Mn.J + 1))).card : ℝ) * (Mn.A.card : ℝ) * Cw *
    (1 + Real.sqrt (((wordsUpTo Mn.A (Mn.J + 1)).card : ℝ) / Assembly.successorBirthMass α q s)))

/-- Actual edges preserve word length or add one letter. Thus no shorter retained
column reaches a fresh row. For `l = 1` or an edgeless stage the
statement is vacuous; no coefficient regularity or nonzero datum is required. -/
theorem fresh_edge_provenance_of_actual (F : Frame D hr Dm bw j₀)
    {P : ProvParams} {Mn : SuccMenu}
    (hs : IsActualSuccessor D P Mn F.G F.G')
    (hold : ∀ v ∈ F.G.comps, ∀ e ∈ v.births, F.G.level ≤ e.scale)
    (hm : F.G.level = F.m) (l : ℕ) : FreshEdgeProvenanceStatement F l := by
  classical
  let E := Classical.choice (actual_sources hs)
  intro v u γ hv hu hne d _hd
  exfalso
  let e : LedgerEdge F.G' := ⟨v, u, γ⟩
  have hmem := source_old_mem (E.source e) (E.valid e)
  have hsrc := (parent_word_succComp hs.1 _ (hold _ hmem.2) (E.source e).word).2
  have htgt := (parent_word_succComp hs.1 _ (hold _ hmem.1) (E.source e).newWord).2
  change compWord F.G.level ((E.source e).srcComp F.G.level) = _ at hsrc
  change compWord F.G.level ((E.source e).tgtComp F.G.level) = _ at htgt
  rw [E.src e, hm] at hsrc
  rw [E.tgt e, hm] at htgt
  have htarget : (E.source e).newWord.length = l := by rw [← htgt]; exact hv.2
  have hsource : (E.source e).word.length ≤ l - 1 := by rw [← hsrc]; exact hu.2
  have hsource_ne : (E.source e).word.length ≠ l - 1 := by rw [← hsrc]; exact hne
  cases he : (E.source e).letter? with
  | none =>
    have hh : (E.source e).newWord = (E.source e).word := by
      simp only [SuccSource.newWord, he]
    rw [hh] at htarget
    omega
  | some a =>
    have hh : (E.source e).newWord.length = (E.source e).word.length + 1 := by
      simp only [SuccSource.newWord, he, List.length_append, List.length_singleton]
    omega

private theorem fresh_kernel_entry_le (F : Frame D hr Dm bw j₀) (l : ℕ) (A : ℝ)
    (P : F.KernelOp)
    (hC : P.C = fun (v u : CompIn F.G'.comps) (_ : F.G'.fam.Γ v u) =>
      ContinuousLinearMap.id ℝ (hr u.1.root))
    (hc : ∀ d, d + 2 ≤ Dm → 0 ≤ P.c d)
    (hprice : ∀ v u (γ : F.G'.fam.Γ v u),
      (∑ d : ↥(Finset.Icc 2 Dm),
        ((coefficientSeminorm (rhoEnh D F.cr F.m) F.k F.tp F.tf
          (F.G'.physCoeff v u γ d.1)).toReal * P.c (d.1 - 2)) /
          (D.κ (F.m - 1) * P.r v u γ ^ (d.1 - 2))) ≤
        A * (‖(F.G'.fam.identity v u γ).map‖ * (F.G'.fam.identity v u γ).record.size *
          constituentPrice (F.G'.fam.identity v u γ).record))
    (v u : CompIn F.G'.comps) :
    kernelSchurMatrix (D.κ (F.m - 1)) (rhoEnh D F.cr F.m) P.π F.k Dm F.tp F.tf
      P.c P.r P.C (F.freshCoeff l) v u ≤
      A * (if F.IsFreshEdge l v u then
        pricedRecordMajorant P.π (fun _ => 1) F.G'.fam v u else 0) := by
  classical
  by_cases he : F.IsFreshEdge l v u
  · simp only [he, ite_true]
    unfold kernelSchurMatrix pricedRecordMajorant
    simp only [Frame.freshCoeff, he, ite_true, hC, div_self (by norm_num : (1 : ℝ) ≠ 0),
      one_mul]
    rw [mul_left_comm A]
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro γ _
    have hn : 0 ≤ ∑ d : ↥(Finset.Icc 2 Dm),
        ((coefficientSeminorm (rhoEnh D F.cr F.m) F.k F.tp F.tf
          (F.G'.physCoeff v u γ d.1)).toReal * P.c (d.1 - 2)) /
          (D.κ (F.m - 1) * P.r v u γ ^ (d.1 - 2)) := by
      apply Finset.sum_nonneg
      intro d _
      exact div_nonneg (mul_nonneg ENNReal.toReal_nonneg (hc _ (by
        have hd := Finset.mem_Icc.mp d.property
        omega))) (mul_nonneg P.diffusivity_pos.le (pow_nonneg (P.hr v u γ).le _))
    exact (mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_id_le (𝕜 := ℝ)) hn).trans
      (by simpa only [one_mul] using hprice v u γ)
  · simp only [he, ite_false, Frame.freshCoeff, kernelSchurMatrix,
      CycleComparison.Coarse.coefficientSeminorm_zero_coefficient, ENNReal.toReal_zero,
      zero_mul, zero_div, Finset.sum_const_zero, mul_zero]
    exact le_rfl

/-- The sharp source price produces the literal fresh-prefix operator interface.
This is the stage-generic adapter of the native per-identity estimate (proved uniformly by
`uniform_native_identity_kernel_price`).
The first prefix has theta1; subsequent births cancel and have
theta2. Neither a marked norm nor the incoming ledger is divided by. -/
theorem fresh_prefix_price_of_actual (F : Frame D hr Dm bw j₀)
    {α s q Cw cr σ A : ℝ} {N p d : ℕ} {Mn : SuccMenu}
    (hDα : D.α = α) (hDq : D.q = q) (hq : 1 < q) (hΛ : 128 ≤ D.Λ)
    (hη : 0 < succEta0 α q s) (hCw : 0 ≤ Cw) (hσ : 0 ≤ σ) (hA : 0 ≤ A)
    (hletters : ∀ l ∈ Mn.A, letterOrder N p l - 2 ≤ d)
    (hlaw : IsSuccessorLaw α q s (wordsUpTo Mn.A (Mn.J + 1)).card F.law)
    (hG : F.G.HasTags (succProvParams D Cw cr σ (succEta0 α q s) N p))
    (hold : ∀ v ∈ F.G.comps, ∀ e ∈ v.births, F.G.level ≤ e.scale)
    (hactual : IsActualSuccessor D (succProvParams D Cw cr σ (succEta0 α q s) N p) Mn F.G F.G')
    (hm : F.G.level = F.m)
    (hθ₁ : F.θ₁ = succTheta1 α q s σ d) (hθ₂ : F.θ₂ = succTheta2 α q s σ d)
    {S : ℝ} (hS : 0 ≤ S) (hhalf : S ≤ 1 / 2)
    (hledger : markedLedger (F.G.mass F.law) (F.G.marker F.law) F.G.fam ≤ S)
    (l : ℕ) (hl : 1 ≤ l) (P : F.KernelOp)
    (hB : P.B = fun (v u : CompIn F.G'.comps) (γ : F.G'.fam.Γ v u)
      (d : ↥(Finset.Icc 2 Dm)) => F.G'.physCoeff v u γ d.1)
    (hC : P.C = fun (v u : CompIn F.G'.comps) (_ : F.G'.fam.Γ v u) =>
      ContinuousLinearMap.id ℝ (hr u.1.root))
    (hπ : P.π = fun v => F.G'.mass F.law v / F.G'.marker F.law v ^ 2)
    (hc : ∀ d, d + 2 ≤ Dm → 0 ≤ P.c d) (hθ : 0 ≤ P.θ)
    (hprice : ∀ v u (γ : F.G'.fam.Γ v u),
      (∑ d : ↥(Finset.Icc 2 Dm),
        ((coefficientSeminorm (rhoEnh D F.cr F.m) F.k F.tp F.tf
          (F.G'.physCoeff v u γ d.1)).toReal * P.c (d.1 - 2)) /
          (D.κ (F.m - 1) * P.r v u γ ^ (d.1 - 2))) ≤
        A * (‖(F.G'.fam.identity v u γ).map‖ * (F.G'.fam.identity v u γ).record.size *
          constituentPrice (F.G'.fam.identity v u γ).record))
    (hy : ∀ v u (γ : F.G'.fam.Γ v u) (hu : IsRetained F.m F.H F.J u.1),
      ∀ᵐ t ∂volume.restrict (Set.Icc F.tp F.tf),
        (F.yom v u γ t).val (valueIndex2 (F.k + Dm - 1)) =
          P.S v u γ t ((F.Yw ⟨u.1, Finset.mem_filter.2 ⟨u.2, hu⟩⟩ t).val
            (valueIndex2 (F.k + 1)))) :
    FreshPrefixPriceStatement F l (freshPrefixConstant α q s Cw A Mn) := by
  classical
  let Cp := 2 * ((insert [] (wordsUpTo Mn.A (Mn.J + 1))).card : ℝ) * (Mn.A.card : ℝ) * Cw *
    (1 + Real.sqrt (((wordsUpTo Mn.A (Mn.J + 1)).card : ℝ) / Assembly.successorBirthMass α q s))
  have hCp : 0 ≤ Cp := by dsimp only [Cp]; positivity
  have heps : 0 < D.eps (F.m - 1) := (Scales.epsilon_basic
    (m := F.m - 1) (hDq.symm ▸ hq) hΛ).1
  let Q : LedgerEdge F.G' → Prop := fun e => F.IsFreshEdge l e.1 e.2.1
  have hrecords := fresh_record_schur hDα hDq hq hΛ hη hCw hσ hletters F.law hlaw
    hG hold hactual hS hhalf hledger l hl Q (fun e he => by
      exact ⟨hm.symm ▸ he.1.2, hm.symm ▸ he.2.2⟩)
  have hexp : (if l = 1 then succTheta1 α q s σ d else succTheta2 α q s σ d) =
      F.lengthExponent l := by rw [Frame.lengthExponent, hθ₁, hθ₂]
  rw [hm, hexp] at hrecords
  have hπpos (v : CompIn F.G'.comps) : 0 < F.G'.mass F.law v :=
    Buffer.birth_compMass_pos (hDq.symm ▸ hq) hΛ F.law v.1
  have hmarkpos (v : CompIn F.G'.comps) : 0 < F.G'.marker F.law v :=
    Buffer.birth_compMarker_pos (hDq.symm ▸ hq) hΛ F.law v.1
  have hsum (v u : CompIn F.G'.comps) :
      (∑ γ, if Q ⟨v, u, γ⟩ then identityPrice F.G'
        (ledgerDiagonal D.q D.Λ F.law true) ⟨v, u, γ⟩ else 0) =
      if F.IsFreshEdge l v u then
        pricedRecordMajorant P.π (fun _ => 1) F.G'.fam v u else 0 := by
    by_cases he : F.IsFreshEdge l v u
    · simp only [Q, he, ite_true]
      rw [sum_identityPrice_eq (hDq.symm ▸ hq) hΛ F.law true, hπ,
        pricedRecordMajorant_effective_mass F.G'.fam _ _ hπpos hmarkpos]
      rfl
    · simp only [Q, he, ite_false, Finset.sum_const_zero]
  have hentry (v u : CompIn F.G'.comps) :
      kernelSchurMatrix (D.κ (F.m - 1)) (rhoEnh D F.cr F.m) P.π F.k Dm F.tp F.tf
        P.c P.r P.C (F.freshCoeff l) v u ≤
      A * (∑ γ, if Q ⟨v, u, γ⟩ then identityPrice F.G'
        (ledgerDiagonal D.q D.Λ F.law true) ⟨v, u, γ⟩ else 0) := by
    rw [hsum]
    exact fresh_kernel_entry_le F l A P hC hc hprice v u
  have hsharp : SchurBound (freshPrefixConstant α q s Cw A Mn *
      D.eps (F.m - 1) ^ F.lengthExponent l)
      (kernelSchurMatrix (D.κ (F.m - 1)) (rhoEnh D F.cr F.m) P.π F.k Dm F.tp F.tf
        P.c P.r P.C (F.freshCoeff l)) := by
    constructor
    · intro v
      calc
        _ ≤ ∑ u, A * (∑ γ, if Q ⟨v, u, γ⟩ then identityPrice F.G'
            (ledgerDiagonal D.q D.Λ F.law true) ⟨v, u, γ⟩ else 0) :=
          Finset.sum_le_sum (fun u _ => hentry v u)
        _ = A * ∑ u, ∑ γ, if Q ⟨v, u, γ⟩ then identityPrice F.G'
            (ledgerDiagonal D.q D.Λ F.law true) ⟨v, u, γ⟩ else 0 := (Finset.mul_sum _ _ _).symm
        _ ≤ A * (Cp * D.eps (F.m - 1) ^ F.lengthExponent l) :=
          mul_le_mul_of_nonneg_left (hrecords.1 v) hA
        _ = _ := by unfold freshPrefixConstant; dsimp only [Cp]; ring
    · intro u
      calc
        _ ≤ ∑ v, A * (∑ γ, if Q ⟨v, u, γ⟩ then identityPrice F.G'
            (ledgerDiagonal D.q D.Λ F.law true) ⟨v, u, γ⟩ else 0) :=
          Finset.sum_le_sum (fun v _ => hentry v u)
        _ = A * ∑ v, ∑ γ, if Q ⟨v, u, γ⟩ then identityPrice F.G'
            (ledgerDiagonal D.q D.Λ F.law true) ⟨v, u, γ⟩ else 0 := (Finset.mul_sum _ _ _).symm
        _ ≤ A * (Cp * D.eps (F.m - 1) ^ F.lengthExponent l) :=
          mul_le_mul_of_nonneg_left (hrecords.2 u) hA
        _ = _ := by unfold freshPrefixConstant; dsimp only [Cp]; ring
  exact ⟨fresh_edge_provenance_of_actual F hactual hold hm l,
    fresh_prefix_price_of_schur F l _ P hB hC hπ hc hθ
      (mul_nonneg (mul_nonneg hA hCp) (Real.rpow_nonneg heps.le _)) hsharp hy⟩

/-- Request-uniform fresh-prefix production. The native inflation is chosen at order n,
then used for every k <= n; no fresh-prefix Cauchy estimate is introduced.
The coefficient finiteness at n is supplied by the native operator built
at the request ceiling, exactly as in the grade-row producer. -/
theorem uniform_fresh_prefix_price (α s q : ℝ)
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (bw : ℝ) (hb : 0 < bw)
    (n Dm : ℕ) (c : ℕ → ℝ) (hc : ∀ j, j + 2 ≤ Dm → 0 ≤ c j) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ m₀ : ℕ, 2 ≤ m₀ ∧
    ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
      [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)],
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCStreamSeq α q Λ ζ D.Φ → ∀ (j₀ M : ℕ) (F : Frame D hr Dm bw j₀) (kI : InvConsts),
      F.G'.IsContextCertified kI → F.G'.IsNatural M → m₀ + 1 ≤ F.G'.level →
      1 ≤ F.G'.level → j₀ ≤ F.G'.level →
      0 < D.eps (F.G'.level - 1) → 0 < D.eps F.G'.level → 0 < D.kap F.G'.level →
      F.G'.IsSlotTransverse → (∀ v : CompIn F.G'.comps, 0 ≤ compReserve kI v.1) →
      (∀ v : CompIn F.G'.comps, compReserve kI v.1 ≤ 2) →
      0 < rhoEnh D F.cr F.m → rhoEnh D F.cr F.m ≤ D.eps (F.G'.level - 1) →
      rhoEnh D F.cr F.m ≤ D.eps F.G'.level →
      (∀ v u (γ : F.G'.fam.Γ v u), 3 ≤ (F.G'.fam.identity v u γ).maxOrder →
        (F.G'.fam.identity v u γ).record.length ≤ D.eps (F.G'.level - 1)) →
      F.k ≤ n →
      (∀ v u (γ : F.G'.fam.Γ v u) (d : ↥(Finset.Icc 2 Dm)),
        coefficientSeminorm (rhoEnh D F.cr F.m) n F.tp F.tf
          (F.G'.physCoeff v u γ d.1) ≠ ⊤) →
      ∀ (Cw cr σ : ℝ) (N p d : ℕ) (Mn : SuccMenu),
      0 ≤ Cw → 0 ≤ σ → 0 < succEta0 α q s →
      (∀ l ∈ Mn.A, letterOrder N p l - 2 ≤ d) →
      IsSuccessorLaw α q s (wordsUpTo Mn.A (Mn.J + 1)).card F.law →
      F.G.HasTags (succProvParams D Cw cr σ (succEta0 α q s) N p) →
      (∀ v ∈ F.G.comps, ∀ e ∈ v.births, F.G.level ≤ e.scale) →
      IsActualSuccessor D (succProvParams D Cw cr σ (succEta0 α q s) N p) Mn F.G F.G' →
      F.G.level = F.m → F.θ₁ = succTheta1 α q s σ d → F.θ₂ = succTheta2 α q s σ d →
      D.kap F.G'.level = D.κ (F.m - 1) →
      ∀ S : ℝ, 0 ≤ S → S ≤ 1 / 2 →
      markedLedger (F.G.mass F.law) (F.G.marker F.law) F.G.fam ≤ S →
      ∀ (seedK freshK : ℕ → KernelSpec) (P : F.KernelOp),
      P.B = (fun (v u : CompIn F.G'.comps) (γ : F.G'.fam.Γ v u)
        (d : ↥(Finset.Icc 2 Dm)) => F.G'.physCoeff v u γ d.1) →
      P.C = (fun (v u : CompIn F.G'.comps) (_ : F.G'.fam.Γ v u) =>
        ContinuousLinearMap.id ℝ (hr u.1.root)) →
      P.π = (fun v => F.G'.mass F.law v / F.G'.marker F.law v ^ 2) →
      P.r = (fun v u γ =>
        (F.G'.kernelOf (succProvParams D Cw cr σ (succEta0 α q s) N p) seedK freshK v u γ).width) →
      (∀ v u γ, (F.G'.kernelOf (succProvParams D Cw cr σ (succEta0 α q s) N p)
        seedK freshK v u γ).width = (F.G'.fam.identity v u γ).record.width) →
      P.c = c → 0 ≤ P.θ →
      (∀ v u (γ : F.G'.fam.Γ v u) (hu : IsRetained F.m F.H F.J u.1),
        ∀ᵐ t ∂volume.restrict (Set.Icc F.tp F.tf),
          (F.yom v u γ t).val (valueIndex2 (F.k + Dm - 1)) =
            P.S v u γ t ((F.Yw ⟨u.1, Finset.mem_filter.2 ⟨u.2, hu⟩⟩ t).val
              (valueIndex2 (F.k + 1)))) →
      ∀ l : ℕ, 1 ≤ l → FreshPrefixPriceStatement F l (freshPrefixConstant α q s Cw A Mn) := by
  obtain ⟨A, hA, m₀, hm₀, hp⟩ := uniform_native_identity_kernel_price
    α s q hα0 hα1 hs0 hs1 hq Λ hΛ ζ hζ bw hb n (n + Dm) Dm le_rfl c hc
  refine ⟨A, hA, m₀, hm₀, ?_⟩
  intro hr _ _ _ _ _ _ D hDα hDq hDΛ hDζ hseq j₀ M F kI hctx hnat hlevel hi hj
    hE he hν hslot hres hres2 hρ hρE hρe hlen hkn hfin Cw cr σ N p d Mn hCw hσ hη hletters hlaw hG hold hactual hm hθ₁ hθ₂ hκ
    S hS hhalf hled seedK freshK P hB hC hπ hRadius hwidth hpc hPθ hy l hl
  apply fresh_prefix_price_of_actual F hDα hDq hq.1 (hDΛ.symm ▸ hΛ) hη hCw hσ hA
    hletters hlaw hG hold hactual hm hθ₁ hθ₂ hS hhalf hled l hl P
    hB hC hπ (fun j hj => hpc.symm ▸ hc j hj) hPθ ?_ hy
  intro v u γ
  have hprice := hp hr D hDα hDq hDΛ hDζ hseq j₀ M F.G' kI hctx hnat hlevel hi hj
    hE he hν hslot F.tp F.tf v u γ (hres v) (hres2 v) (rhoEnh D F.cr F.m)
    hρ hρE hρe (hlen v u γ)
  rw [hκ] at hprice
  apply le_trans ?_ hprice
  apply Finset.sum_le_sum
  intro d _
  simp only [hpc, hRadius, hwidth]
  apply div_le_div_of_nonneg_right _
    (mul_nonneg P.diffusivity_pos.le (pow_nonneg (F.G'.fam.identity v u γ).record.width_pos.le _))
  apply mul_le_mul_of_nonneg_right _ (hc _ (by
    have hd := Finset.mem_Icc.mp d.property
    omega))
  exact ENNReal.toReal_mono (hfin v u γ d)
    (coefficientSeminorm_order_mono _ hkn _ _ _)

/-- Data-level instantiation of the sharp fresh-prefix price. The certificates and native
operator are the same ones used by grade rows; all thresholds precede stage data. -/
theorem length_prefix_prices_at_data {α s q : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q)
    {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (Λl Λ : ℕ)
    (hlength : UniformRecordLengths α q ζ Λl) (hΛ : Λl ≤ Λ) (h128 : 128 ≤ Λ)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw : ℝ) (hbw : 0 < bw)
    (Q T₀ Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout Kres npad sX sZ : ℕ)
    (σ₀ : ℝ) (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (CQ Cpr : ℝ) (hCI : 0 ≤ CI) (hCw : 0 ≤ Cw) (hσ : 0 ≤ σ₀) (hτe : 0 < τe)
    (hcker : ∀ j, j + 2 ≤ succSchedD D₀ N p (H + 1) → 0 ≤ kI.cker j) (mc : ℕ)
    (hc : ExtendedCertificatesAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS
      r₀ D₀ H J N p nk npad sX sZ σ₀ kI CI Cw j₀ mc)
    (hprod : kI.Hprod = kI.G0 + H + 1) (hc0pos : 0 < kI.c₀) (hc0le : kI.c₀ ≤ 1)
    (_hcrpos : 0 < kI.cr) (hcrle : kI.cr ≤ 1) (mr : ℕ) (hmr : 2 ≤ mr)
    (hradius : EnhancedRadiusAt α q ζ Λ kI.c₀ kI.cr mr) (md : ℕ)
    (hdrift : EnhancedDriftAt α q ζ Λ kI.cr md)
    (Cu : ℝ) (hscale : ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ → ∀ m, 2 ≤ m → m ≤ D.term →
        AVRegularity.Providers.CascadeInvariants.PassScales D m Cu)
    (A : ℝ) (hA : 0 ≤ A) (mo : ℕ)
    (hop : NativeKernelOperatorsAt α q ζ Λ bw Kres (succSchedD D₀ N p (H + 1)) kI.cker A mo)
    (ma : ℕ)
    (habs : ∀ m, ma ≤ m → A * (CI * ocEpsilon q Λ (m - 1) ^ min (ocDelta α q / 4) τe) < 1 / 8)
    : ∃ (C : ℝ) (mStar : ℕ),
      LengthFreshProductionDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS
        r₀ D₀ H J N p nk Naux Nout Kres npad sX sZ σ₀ kI CI Cw j₀ CQ Cpr Q T₀ C mStar := by
  classical
  obtain ⟨Ap, _hAp, mp, _hmp, hprefix⟩ := uniform_fresh_prefix_price α s q
    hα₀ hα₁ hs₀ hs₁ hq Λ h128 ζ hζ bw hbw Kres
    (succSchedD D₀ N p (H + 1)) kI.cker hcker
  have hδ : 0 < ocDelta α q := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  have hτ : 0 < min (ocDelta α q / 4) τe := lt_min (div_pos hδ (by norm_num)) hτe
  obtain ⟨mi, hincoming⟩ := retained_absorption_threshold hq.1 h128 hτ 8 CI
  let Mn₀ := succMenu 0 r₀ D₀ H J N p npad sX sZ (succEta0 α q s)
  let C := freshPrefixConstant α q s Cw Ap Mn₀
  refine ⟨C, max mc (max mr (max md (max (mo + 3) (max ma
    (max (mp + 3) (max mi (j₀ + 3))))))), ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA s₀ htA hdelay hwindow _hT G G' hcascade hlevel hG hactual tp Preg hprep
    _f _Ain _hf k hk Y0 _Y Yw _Yk _htrace _hsol yom hyom
  have hmc : mc ≤ m := by omega
  have hmr' : mr ≤ m := by omega
  have hmd' : md ≤ m := by omega
  have hmo' : mo + 1 ≤ m - 1 := by omega
  have hma : ma ≤ m := by omega
  have hmp : mp + 1 ≤ m - 1 := by omega
  have hmi : mi ≤ m := by omega
  have hjGr' : j₀ ≤ m - 1 := by omega
  have hm2 : 2 ≤ m := by omega
  have hiGr' : 1 ≤ m - 1 := by omega
  have hm1 : 1 ≤ m := by omega
  have hmterm : m ≤ D.term := by rw [hterm]; exact hn.trans hnM.le
  have hqD : 1 < D.q := by rw [hDq]; exact hq.1
  have hΛD : 128 ≤ D.Λ := by rw [hDΛ]; exact h128
  have hζD : IsFastProfile D.ζ := hDζ.symm ▸ hζ
  have hbandD : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    simpa only [hDα, hDq, hDΛ, hDζ, hterm] using hband
  let P := succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p
  let Mn := succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)
  let Gr := G'
  have hGrlevel : Gr.level = m - 1 := by
    change G'.level = m - 1
    rw [hactual.2.1, hlevel]
  have hGrlevelterm : Gr.level ≤ D.term := by omega
  have hGrI := hc D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    seedK freshK hfresh seed n tS tf hseed m hmc hn hnM tA htA G G' hcascade hlevel hG hactual
  obtain ⟨hnat, hshift, hslot, hctx, hled, hker⟩ := hGrI
  have hmGr v : 0 ≤ compReserve kI (v : CompIn Gr.comps).1 :=
    AVRegularity.Providers.CascadeInvariants.compReserve_nonneg_of_succ kI (H := H) hprod
      (AVRegularity.Providers.CascadeInvariants.grade_le_of_succ
        (AVRegularity.Providers.CascadeInvariants.grade_le_of_cascade hseed.2.1 hcascade) hactual v)
  have hm2Gr v : compReserve kI (v : CompIn Gr.comps).1 ≤ 2 :=
    (Buffer.compReserve_le_one kI v.1).trans (by norm_num)
  have hseedI := hseed.2.2.2.2.2.2.2.1
  have hlens : ∀ v u (γ : seed.fam.Γ v u), 1 ≤ (seed.fam.identity v u γ).record.birthExcess →
      (seed.fam.identity v u γ).record.length ≤ D.eps seed.level := by
    intro v u γ hb
    simpa only [hseed.1] using (hseed.2.2.2.2.2.1 v u γ).2.2 hb
  have hlenG := hlength hr D hDα hDq hDζ (by rw [hDΛ]; omega) hbandD
    _ bw j₀ Mn Cw kI.cr σ₀ (succEta0 α q s) N p hcrle seed G hseedI.2.1 hlens
    (by rw [hseed.1, hterm]; exact hnM.le) hcascade (hlevel.symm ▸ hm1)
  have hscl := hscale D hDα hDq hDΛ hDζ hbandD m hm2 hmterm
  have hlenGr := extended_successor_record_lengths P Mn G G' hactual hG.2.1 hlenG
    (EntryScales.epsilon_antitone hqD (by omega) (by rw [hactual.2.1]; omega))
    (by
      change freshLength D kI.cr (G.level - 1) ≤ D.eps G'.level
      rw [hactual.2.1, hlevel]
      simpa only [Nat.sub_add_cancel hm1] using
        AVRegularity.Providers.CascadeInvariants.freshLength_le_eps_of_passScales hcrle
          (show AVRegularity.Providers.CascadeInvariants.PassScales D ((m - 1) + 1) Cu from
            (Nat.sub_add_cancel hm1).symm ▸ hscl))
  have he (l : ℕ) : 0 < D.eps l := Construction.Stream.ocEpsilon_pos (by omega)
  have hκ (l : ℕ) (hl : l ≤ D.term) : 0 < D.κ l :=
    CycleReference.bandChain_pos (by omega) hζD hbandD hl
  have ha (l : ℕ) : 0 < ocA D.α D.q D.Λ l := Real.rpow_pos_of_pos (he l) _
  have hrs (l : ℕ) (hl : l ≤ D.term) :
      0 < rhoStar D kI.c₀ l ∧ rhoStar D kI.c₀ l ≤ D.eps l := by
    have hh := Buffer.molecular_radius_bounds hc0pos (he l) (hκ l hl) (ha l)
    exact ⟨hh.1, hh.2.1.trans (mul_le_of_le_one_left (he l).le hc0le)⟩
  have hrhos := hradius D hDα hDq hDΛ hDζ hbandD m hmr' hmterm
  have hρe : rhoEnh D kI.cr m ≤ D.eps Gr.level := by
    rw [hGrlevel]
    exact hrhos.trans (hrs (m - 1) (by omega)).2
  have hρE : rhoEnh D kI.cr m ≤ D.eps (Gr.level - 1) :=
    hρe.trans (EntryScales.epsilon_antitone hqD (by omega) (Nat.sub_le _ _))
  have hd := hdrift D.Φ hseq M D.κ hband m hmd' (hn.trans hnM.le)
  have hρpos : 0 < rhoEnh D kI.cr m := by
    simpa only [rhoEnh, hDα, hDq, hDΛ] using hd.2.1
  have htptf : tp ≤ tf := by
    have hh := hprep.2.2.1
    rw [hlevel, hDα, hDq, hDΛ] at hh
    exact hh.trans hwindow
  have hsub : Set.Icc tp tf ⊆ Set.Icc (tA + 3 * ocTau α q Λ m) tf := by
    intro t ht
    exact ⟨(hdelay.trans hprep.2.1).trans ht.1, ht.2⟩
  have hSzero : ∀ v u (γ : Gr.fam.Γ v u), IsSpatialRegularizerTorus (rhoEnh D kI.cr m) 0
      (succSchedD D₀ N p (H + 1)) tp tf kI.cker
      (Gr.kernelOf P seedK freshK v u γ).width (Gr.sysS P seedK freshK φ₀ hφ₀ v u γ) := by
    intro v u γ
    exact Buffer.spatialRegularizerTorus_time_restrict ((hker v u γ).2 _ hρpos) hsub
  have hkap : D.kap Gr.level = D.κ (m - 1) := by
    change D.κ (min Gr.level D.term) = _
    rw [Nat.min_eq_left hGrlevelterm, hGrlevel]
  have hsmall : A * (CI * D.eps (m - 1) ^ min (ocDelta α q / 4) τe) < 1 / 8 := by
    simpa only [OCData.eps, hDq, hDΛ] using habs m hma
  have hlengthop : ∀ v u (γ : Gr.fam.Γ v u), 3 ≤ (Gr.fam.identity v u γ).maxOrder →
      (Gr.fam.identity v u γ).record.length ≤ D.eps (Gr.level - 1) := by
    intro v u γ hj
    have hb : 1 ≤ (Gr.fam.identity v u γ).record.birthExcess := by
      have hh := (Gr.fam.identity v u γ).le_birth
      omega
    exact (hlenGr v u γ hb).trans
      (EntryScales.epsilon_antitone hqD (by omega) (Nat.sub_le _ _))
  have hop' := hop hr D hDα hDq hDΛ hDζ hseq j₀ Mnat Gr kI hctx hnat hshift
    (hGrlevel.symm ▸ hmo') (hGrlevel.symm ▸ hiGr') (hGrlevel.symm ▸ hjGr')
    (he _) (he _) (by rw [hkap]; exact hd.1)
    hslot hmGr hm2Gr P seedK freshK (fun v u γ => (hker v u γ).1) φ₀ hφ₀ tp tf
    (rhoEnh D kI.cr m) (CI * D.eps (m - 1) ^ min (ocDelta α q / 4) τe)
    (Gr.mass law) (Gr.marker law) htptf hρpos hρE hρe hlengthop
    (fun v => Buffer.birth_compMass_pos hqD hΛD law v.1)
    (fun v => Buffer.birth_compMarker_pos hqD hΛD law v.1) hled hsmall.le hSzero
  rw [hkap] at hop'
  obtain ⟨R, hB, hC, hS, hπ, hRadius, hcR, _hθ⟩ := hop' (Gr.marker law) (Or.inr rfl)
  have hSall : ∀ v u γ, IsSpatialRegularizerTorus (rhoEnh D kI.cr m) k
      (succSchedD D₀ N p (H + 1)) tp tf R.c (R.r v u γ) (R.S v u γ) := by
    intro v u γ
    rw [hRadius, hcR, hS]
    exact spatial_regularizer_all_orders _ _ _ _ _ _ _ (hSzero v u γ) k
  let Rk := kernelOperator_order_restrict R hk hSall
  let F : Frame D hr (succSchedD D₀ N p (H + 1)) bw j₀ :=
    { G := G, G' := G', law := law, m := m, H := H, J := J, k := k,
      cr := kI.cr, η := succEta0 α q s,
      θ₁ := succTheta1 α q s σ₀ (succDstar D₀ N p H),
      θ₂ := succTheta2 α q s σ₀ (succDstar D₀ N p H),
      tp := tp, tf := tf, Y0 := Y0, Yw := Yw, yom := yom }
  have hnativeθ : 0 ≤ Rk.θ := by
    rw [show Rk.θ = A * (CI * D.eps (m - 1) ^ min (ocDelta α q / 4) τe) from _hθ]
    exact mul_nonneg hA (mul_nonneg hCI (Real.rpow_nonneg (he _).le _))
  have hin : CI * D.eps m ^ min (ocDelta α q / 4) τe ≤ 1 / 2 := by
    have hh : 8 * (CI * D.eps (m - 1) ^ min (ocDelta α q / 4) τe) < 1 / 8 := by
      simpa only [OCData.eps, hDq, hDΛ] using hincoming m hmi
    have hmono := Real.rpow_le_rpow (he m).le
      (EntryScales.epsilon_antitone hqD (by omega) (Nat.sub_le m 1)) hτ.le
    have hb : CI * D.eps (m - 1) ^ min (ocDelta α q / 4) τe ≤ 1 / 2 := by
      linarith only [hh]
    exact (mul_le_mul_of_nonneg_left hmono hCI).trans hb
  have hold := InitialValue.cascade_invariant hseed.2.1 hcascade
  have hletter : ∀ l ∈ Mn.A, letterOrder N p l - 2 ≤ succDstar D₀ N p H := by
    intro l hl
    change l ∈ succAlphabetOf r₀ D₀ H J N p npad at hl
    have hnext : succSchedD D₀ N p (H + 1) = succSchedD D₀ N p H + 2 * N + 4 * p + 4 := rfl
    cases l with
    | diag => simp only [letterOrder, succDstar]; omega
    | mean n h =>
      have hn := (Providers.CascadeInvariants.mean_mem_succAlphabet hl).2.1
      simp only [letterOrder, succDstar]
      omega
    | covariance n h a a' =>
      have hf := Providers.CascadeInvariants.cov_mem_succAlphabet hl
      simp only [letterOrder, succDstar]
      omega
    | eddy n => simp [succAlphabetOf, succAlphabet] at hl
    | padding n => simp only [letterOrder]; omega
  have hhy : ∀ v u (γ : F.G'.fam.Γ v u) (hu : IsRetained F.m F.H F.J u.1),
      ∀ᵐ t ∂volume.restrict (Set.Icc F.tp F.tf),
        (F.yom v u γ t).val (valueIndex2 (F.k + succSchedD D₀ N p (H + 1) - 1)) =
          Rk.S v u γ t ((F.Yw ⟨u.1, Finset.mem_filter.2 ⟨u.2, hu⟩⟩ t).val
            (valueIndex2 (F.k + 1))) := by
    intro v u γ hu
    rw [show Rk.S = G'.sysS P seedK freshK φ₀ hφ₀ from hS]
    filter_upwards [hyom v u γ hu] with t ht
    have heq := frontier_sysS_parameters_congr G'
      (succProvParams D Cw kI.cr σ₀ (succEta0 α q t) N p) P rfl seedK freshK φ₀ hφ₀
    simpa only [F, heq] using ht
  change ∀ l : ℕ, 1 ≤ l → l ≤ J + 1 → FreshPrefixPriceStatement F l C
  intro l hl _hlJ
  have hp := hprefix hr D hDα hDq hDΛ hDζ hseq j₀ Mnat F kI hctx hnat
    (hGrlevel.symm ▸ hmp) (hGrlevel.symm ▸ hiGr') (hGrlevel.symm ▸ hjGr')
    (he _) (he _) (hkap.symm ▸ hd.1) hslot hmGr hm2Gr hρpos hρE hρe hlengthop hk
    (by intro v u γ d; simpa only [hB] using R.hB_fin v u γ d)
    Cw kI.cr σ₀ N p (succDstar D₀ N p H) Mn hCw hσ
    (successor_eta0_pos hα₀ hα₁ hs₀ hs₁ hq) hletter hlaw hG.2.1
    (fun v hv => (hold v hv).1) hactual hlevel rfl rfl hkap
    (CI * D.eps m ^ min (ocDelta α q / 4) τe)
    (mul_nonneg hCI (Real.rpow_nonneg (he _).le _)) hin hG.2.2.2.2.2.2.2.1
    seedK freshK Rk hB hC hπ hRadius (fun v u γ => (hker v u γ).1) hcR hnativeθ hhy l hl
  exact hp

/-- The complete named fresh-prefix price ingredient, with all constants before stage data.
Signed preparation constants do not enter the fresh-prefix constant. -/
theorem length_fresh_production {α s q : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    LengthFreshProductionStatement α s q ζ := by
  classical
  obtain ⟨Λc, hΛc, hc⟩ := extended_stage_certificates α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λl, hΛl, hlength⟩ := uniform_cascade_record_length hα₀ hα₁ hs₀ hs₁ hq hζ
  change UniformRecordLengths α q ζ Λl at hlength
  obtain ⟨Λr, hΛr, hradius⟩ := uniform_enhanced_radius_le_parent_molecular hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Λd, hΛd, hdrift⟩ := actual_enhanced_drift_budget hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Cu, _hCu, Λp, hΛp, hscale⟩ := AVRegularity.Providers.CascadeInvariants.exists_passScales
    hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨max Λc (max Λl (max Λr (max Λd Λp))), by omega, ?_⟩
  intro Λ hΛ
  have h128 : 128 ≤ Λ := by omega
  obtain ⟨cmax, hcmax, hc⟩ := hc Λ (by omega)
  refine ⟨min cmax 1, lt_min hcmax zero_lt_one, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  obtain ⟨tc, CH, Υ, hCH, hΥ, hc⟩ := hc φ₀ hφ₀ hφsmooth hφpos hφint hφsupport
    bw hbw hbwupper Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀
    (hc₀upper.trans (min_le_left _ _)) hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  let thr : InvConsts := { tc with cker := fun j => max (tc.cker j) 0 }
  refine ⟨thr, CH, Υ, hCH, hΥ, ?_⟩
  intro kI hkI
  have hkIc := invariant_admissible_of_threshold_bounds (a := tc) (b := thr)
    le_rfl le_rfl le_rfl (fun _ => le_rfl) (fun j => le_max_left _ _) hkI
  obtain ⟨CIthr, Cwthr, hc⟩ := hc kI hkIc
  refine ⟨CIthr, Cwthr, ?_⟩
  intro CI Cw j₀ hledger hstart CQ Cpr
  obtain ⟨mc, hc⟩ := hc CI Cw j₀ hledger hstart
  change ExtendedCertificatesAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk npad sX sZ
    σ₀ kI CI Cw j₀ mc at hc
  obtain ⟨hc0I, hcrI, hprod⟩ := Buffer.invariantAdmissible_molecular_parameters hkI
  have hc0pos : 0 < kI.c₀ := hc0I.symm ▸ hc₀
  have hc0le : kI.c₀ ≤ 1 := hc0I.symm ▸ hc₀upper.trans (min_le_right _ _)
  have hcrpos : 0 < kI.cr := hcrI.symm ▸ hcr
  have hcrle : kI.cr ≤ 1 := hcrI.symm ▸ hcrupper
  have hDm : 2 ≤ succSchedD D₀ N p (H + 1) :=
    Buffer.preparation_schedule_order_ge_two D₀ N p H
  obtain ⟨mr, hmr, hradius⟩ := hradius Λ (by omega) kI.c₀ kI.cr hc0pos hcrpos
  change EnhancedRadiusAt α q ζ Λ kI.c₀ kI.cr mr at hradius
  obtain ⟨md, _hmd, hdrift⟩ := hdrift Λ (by omega) kI.cr hcrpos
  change EnhancedDriftAt α q ζ Λ kI.cr md at hdrift
  have hcker (j : ℕ) (_hj : j + 2 ≤ succSchedD D₀ N p (H + 1)) : 0 ≤ kI.cker j :=
    (le_max_right (tc.cker j) 0).trans (invariant_admissible_kernel_bounds hkI j).2
  obtain ⟨A, hA, mo, _hmo, hop⟩ := uniform_native_kernel_operator_of_certificates
    α s q hα₀ hα₁ hs₀ hs₁ hq Λ h128 ζ hζ bw hbw Kres
    (succSchedD D₀ N p (H + 1)) hDm kI.cker hcker
  change NativeKernelOperatorsAt α q ζ Λ bw Kres (succSchedD D₀ N p (H + 1)) kI.cker A mo at hop
  have hδ : 0 < ocDelta α q := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  have hτ : 0 < min (ocDelta α q / 4) τe := lt_min (div_pos hδ (by norm_num)) hτe
  obtain ⟨ma, habs⟩ := retained_absorption_threshold hq.1 h128 hτ A CI
  have hscale' : ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ → ∀ m, 2 ≤ m → m ≤ D.term →
        AVRegularity.Providers.CascadeInvariants.PassScales D m Cu := by
    intro D hDα hDq hDΛ hDζ hband m hm hmM
    apply hscale D hDα hDq hDζ (by omega) _ m hm hmM
    simpa only [hDα, hDq, hDζ] using hband
  obtain ⟨_, _, _, _, _, hσeq, ha, haσ, _, _, _⟩ := hsched
  have hσ₀ : 0 ≤ σ₀ := by linarith only [hσeq, ha, haσ]
  exact length_prefix_prices_at_data hα₀ hα₁ hs₀ hs₁ hq hζ Λl Λ hlength (by omega) h128
    φ₀ hφ₀ bw hbw Q T₀ Ce τe kS r₀ D₀ H J N p nk Naux Nout Kres npad sX sZ σ₀
    kI CI Cw j₀ CQ Cpr (zero_le_one.trans (hCe.trans hledger.1)) hledger.2.2.2.le
    hσ₀ hτe hcker mc hc hprod hc0pos hc0le hcrpos hcrle mr hmr hradius md hdrift
    Cu hscale' A hA mo hop ma habs

/-- The length rows hold unconditionally, by the stage-level construction and the sharp
fresh-prefix producer. -/
theorem length_rows_production {α s q : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    FrontierAnalyticProductionStatement α s q ζ false (fun rows _readout _source => rows) :=
  length_rows_production_of_price (length_fresh_production hα₀ hα₁ hs₀ hs₁ hq hζ)
end

end AVRegularity.Construction.Preservation.Frontier.LengthPrice
end
