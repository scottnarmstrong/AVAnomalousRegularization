-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Proofs.CascadeInvariants.Scales
public import AVRegularity.Definitions.Construction.ScheduleFloor
import AVRegularity.Construction.Preservation.FullLift.IndependentDiagonalJetBudget
import AVRegularity.Construction.Preservation.Buffer.KernelFluxTruncation
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Combinatorics.SimpleGraph.Basic

section
section
/-! Finite positive path sums retain row and column bounds independent of component count. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.Ledger
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

abbrev LedgerEdge (G : GenStage D hr Dm bw j₀) := Σ v u : CompIn G.comps, G.fam.Γ v u

theorem stagePath_step_injective (G : GenStage D hr Dm bw j₀) (n : ℕ) :
    Function.Injective (StagePath.step (G := G) (h := n)) := by
  intro a b hab
  cases a
  cases b
  cases hab
  rfl

noncomputable instance stagePathFintype (G : GenStage D hr Dm bw j₀) (n : ℕ) :
    Fintype (StagePath G n) := Fintype.ofInjective _ (stagePath_step_injective G n)

/-- Each identity is paid once in a positive path product. -/
def pathWeight {G : GenStage D hr Dm bw j₀} (c : LedgerEdge G → ℝ) {n : ℕ}
    (π : StagePath G n) : ℝ := ∏ i, c (π.step i)

/-- Remove the final edge of a path. -/
def pathPrefix {G : GenStage D hr Dm bw j₀} {n : ℕ} (π : StagePath G (n + 1)) : StagePath G n where
  step i := π.step i.castSucc
  joined j hj := π.joined j (by omega)

private theorem last_prefix_injective (G : GenStage D hr Dm bw j₀) (n : ℕ) :
    Function.Injective (fun π : StagePath G (n + 1) => (π.step (Fin.last n), pathPrefix π)) := by
  intro a b hab
  apply stagePath_step_injective G (n + 1)
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact congrArg Prod.fst hab
  · exact congrFun (congrArg StagePath.step (congrArg Prod.snd hab)) j

/-- A nonnegative finite sum can be enlarged along an injective coding. -/
theorem sum_comp_le {α β : Type*} [Fintype α] [Fintype β] (j : α → β)
    (hj : Function.Injective j) (f : β → ℝ) (hf : ∀ b, 0 ≤ f b) :
    ∑ a, f (j a) ≤ ∑ b, f b := by
  classical
  calc
    ∑ a, f (j a) = ∑ b ∈ Finset.univ.image j, f b :=
      (Finset.sum_image (fun a _ b _ h => hj h)).symm
    _ ≤ ∑ b, f b := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun b _ _ => hf b)

/-- The last edge times the prefix is the complete positive product. -/
theorem pathWeight_last_prefix {G : GenStage D hr Dm bw j₀} (c : LedgerEdge G → ℝ)
    {n : ℕ} (π : StagePath G (n + 1)) :
    pathWeight c π = c (π.step (Fin.last n)) * pathWeight c (pathPrefix π) := by
  unfold pathWeight pathPrefix
  rw [Fin.prod_univ_castSucc, mul_comm]

theorem pathWeight_nonneg {G : GenStage D hr Dm bw j₀} (c : LedgerEdge G → ℝ)
    (hc : ∀ e, 0 ≤ c e) {n : ℕ} (π : StagePath G n) : 0 ≤ pathWeight c π :=
  Finset.prod_nonneg (fun i _ => hc (π.step i))

/-- The last-edge/prefix coding permits independent nonnegative summation over both. -/
theorem path_sum_last_prefix_le {G : GenStage D hr Dm bw j₀} {n : ℕ}
    (f : LedgerEdge G → StagePath G n → ℝ) (hf : ∀ e π, 0 ≤ f e π) :
    ∑ π : StagePath G (n + 1), f (π.step (Fin.last n)) (pathPrefix π) ≤
      ∑ e : LedgerEdge G, ∑ π : StagePath G n, f e π := by
  have hh := sum_comp_le _ (last_prefix_injective G n) (fun z => f z.1 z.2)
    (fun z => hf z.1 z.2)
  simpa only [Fintype.sum_prod_type] using hh


/-- Sum the products of all paths with `n+1` edges ending at `v`. -/
def pathRow {G : GenStage D hr Dm bw j₀} (c : LedgerEdge G → ℝ) (n : ℕ)
    (v : CompIn G.comps) : ℝ :=
  ∑ π : StagePath G (n + 1), if (π.step (Fin.last n)).1 = v then pathWeight c π else 0

/-- Sum the products of all paths with `n+1` edges starting at `u`. -/
def pathCol {G : GenStage D hr Dm bw j₀} (c : LedgerEdge G → ℝ) (n : ℕ)
    (u : CompIn G.comps) : ℝ :=
  ∑ π : StagePath G (n + 1), if (π.step 0).2.1 = u then pathWeight c π else 0

private theorem edge_sum_target {G : GenStage D hr Dm bw j₀} (c : LedgerEdge G → ℝ)
    (v : CompIn G.comps) :
    (∑ e : LedgerEdge G, if e.1 = v then c e else 0) = ∑ u, ∑ γ, c ⟨v, u, γ⟩ := by
  classical
  simp [Fintype.sum_sigma]

private theorem edge_sum_source {G : GenStage D hr Dm bw j₀} (c : LedgerEdge G → ℝ)
    (u : CompIn G.comps) :
    (∑ e : LedgerEdge G, if e.2.1 = u then c e else 0) = ∑ v, ∑ γ, c ⟨v, u, γ⟩ := by
  classical
  simp [Fintype.sum_sigma]

private theorem singleton_path_injective (G : GenStage D hr Dm bw j₀) :
    Function.Injective (fun π : StagePath G 1 => π.step 0) := by
  intro a b h
  apply stagePath_step_injective G 1
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  simpa only [hi] using h

/-- Every positive path product has the same row bound as the corresponding matrix power. -/
theorem path_row_le {G : GenStage D hr Dm bw j₀} (c : LedgerEdge G → ℝ)
    (hc : ∀ e, 0 ≤ c e) {S : ℝ} (hS : 0 ≤ S)
    (hrow : ∀ v, ∑ u, ∑ γ, c ⟨v, u, γ⟩ ≤ S) (n : ℕ) (v : CompIn G.comps) :
    pathRow c n v ≤ S ^ (n + 1) := by
  classical
  induction n generalizing v with
  | zero =>
    have hh := sum_comp_le _ (singleton_path_injective G)
      (fun e => if e.1 = v then c e else 0) (fun e => by split <;> [exact hc e; exact le_rfl])
    have hh' : (∑ π : StagePath G 1, if (π.step 0).1 = v then c (π.step 0) else 0) ≤ S :=
      hh.trans (by simpa only [edge_sum_target] using hrow v)
    have hw : ∀ π : StagePath G 1, pathWeight c π = c (π.step 0) := by
      intro π
      exact Fin.prod_univ_one _
    simpa only [pathRow, Nat.zero_add, hw, Fin.last_zero, pow_one] using hh' 
  | succ n ih =>
    let f := fun (e : LedgerEdge G) (π : StagePath G (n + 1)) =>
      if e.1 = v ∧ e.2.1 = (π.step (Fin.last n)).1 then c e * pathWeight c π else 0
    have hf : ∀ e π, 0 ≤ f e π := by
      intro e π
      dsimp only [f]
      split <;> [exact mul_nonneg (hc e) (pathWeight_nonneg c hc π); exact le_rfl]
    have hcode : pathRow c (n + 1) v =
        ∑ π : StagePath G (n + 2), f (π.step (Fin.last (n + 1))) (pathPrefix π) := by
      apply Finset.sum_congr rfl
      intro π _
      have hj : (π.step (Fin.last (n + 1))).2.1 = ((pathPrefix π).step (Fin.last n)).1 :=
        π.joined n (by omega)
      by_cases hv : (π.step (Fin.last (n + 1))).1 = v
      · simp only [f, hv, hj, and_self, ↓reduceIte, pathWeight_last_prefix]
      · simp only [f, hv, false_and, ↓reduceIte]
    have heq : ∀ e : LedgerEdge G, (∑ π : StagePath G (n + 1), f e π) =
        if e.1 = v then c e * pathRow c n e.2.1 else 0 := by
      intro e
      by_cases he : e.1 = v
      · simp only [f, he, true_and, ↓reduceIte, pathRow, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro π _
        by_cases hp : (π.step (Fin.last n)).1 = e.2.1
        · simp [hp]
        · have hp' : e.2.1 ≠ (π.step (Fin.last n)).1 := Ne.symm hp
          simp only [hp, hp', ↓reduceIte, mul_zero]
      · simp only [f, he, false_and, ↓reduceIte, Finset.sum_const_zero]
    calc
      pathRow c (n + 1) v = _ := hcode
      _ ≤ ∑ e : LedgerEdge G, ∑ π : StagePath G (n + 1), f e π := path_sum_last_prefix_le f hf
      _ = ∑ e : LedgerEdge G, if e.1 = v then c e * pathRow c n e.2.1 else 0 :=
        Finset.sum_congr rfl (fun e _ => heq e)
      _ ≤ ∑ e : LedgerEdge G, if e.1 = v then c e * S ^ (n + 1) else 0 := by
        apply Finset.sum_le_sum
        intro e _
        split <;> [exact mul_le_mul_of_nonneg_left (ih e.2.1) (hc e); exact le_rfl]
      _ = (∑ u, ∑ γ, c ⟨v, u, γ⟩) * S ^ (n + 1) := by
        rw [← edge_sum_target c v, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro e _
        split <;> simp only [zero_mul]
      _ ≤ S * S ^ (n + 1) := mul_le_mul_of_nonneg_right (hrow v) (pow_nonneg hS _)
      _ = S ^ (n + 1 + 1) := (pow_succ' S (n + 1)).symm

/-- The same finite path products retain the column bound. -/
theorem path_col_le {G : GenStage D hr Dm bw j₀} (c : LedgerEdge G → ℝ)
    (hc : ∀ e, 0 ≤ c e) {S : ℝ} (hS : 0 ≤ S)
    (hcol : ∀ u, ∑ v, ∑ γ, c ⟨v, u, γ⟩ ≤ S) (n : ℕ) (u : CompIn G.comps) :
    pathCol c n u ≤ S ^ (n + 1) := by
  classical
  induction n with
  | zero =>
    have hh := sum_comp_le _ (singleton_path_injective G)
      (fun e => if e.2.1 = u then c e else 0) (fun e => by split <;> [exact hc e; exact le_rfl])
    have hh' : (∑ π : StagePath G 1, if (π.step 0).2.1 = u then c (π.step 0) else 0) ≤ S :=
      hh.trans (by simpa only [edge_sum_source] using hcol u)
    have hw : ∀ π : StagePath G 1, pathWeight c π = c (π.step 0) := by
      intro π
      exact Fin.prod_univ_one _
    simpa only [pathCol, Nat.zero_add, hw, pow_one] using hh' 
  | succ n ih =>
    let f := fun (e : LedgerEdge G) (π : StagePath G (n + 1)) =>
      if e.2.1 = (π.step (Fin.last n)).1 ∧ (π.step 0).2.1 = u then c e * pathWeight c π else 0
    have hf : ∀ e π, 0 ≤ f e π := by
      intro e π
      dsimp only [f]
      split <;> [exact mul_nonneg (hc e) (pathWeight_nonneg c hc π); exact le_rfl]
    have hcode : pathCol c (n + 1) u =
        ∑ π : StagePath G (n + 2), f (π.step (Fin.last (n + 1))) (pathPrefix π) := by
      apply Finset.sum_congr rfl
      intro π _
      have hj : (π.step (Fin.last (n + 1))).2.1 = ((pathPrefix π).step (Fin.last n)).1 :=
        π.joined n (by omega)
      have hp0 : ((pathPrefix π).step 0).2.1 = (π.step 0).2.1 := rfl
      by_cases hu : (π.step 0).2.1 = u
      · rw [pathWeight_last_prefix]
        simp only [f, hp0, hu, hj, and_self, ↓reduceIte]
      · simp only [f, hp0, hu, and_false, ↓reduceIte]
    have heq : ∀ π : StagePath G (n + 1), (∑ e : LedgerEdge G, f e π) =
        if (π.step 0).2.1 = u then
          (∑ v, ∑ γ, c ⟨v, (π.step (Fin.last n)).1, γ⟩) * pathWeight c π else 0 := by
      intro π
      by_cases hp : (π.step 0).2.1 = u
      · simp only [f, hp, and_true, ↓reduceIte]
        rw [← edge_sum_source c (π.step (Fin.last n)).1, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro e _
        split <;> simp only [zero_mul]
      · simp only [f, hp, and_false, ↓reduceIte, Finset.sum_const_zero]
    calc
      pathCol c (n + 1) u = _ := hcode
      _ ≤ ∑ e : LedgerEdge G, ∑ π : StagePath G (n + 1), f e π := path_sum_last_prefix_le f hf
      _ = ∑ π : StagePath G (n + 1), ∑ e : LedgerEdge G, f e π := Finset.sum_comm
      _ = ∑ π : StagePath G (n + 1), if (π.step 0).2.1 = u then
          (∑ v, ∑ γ, c ⟨v, (π.step (Fin.last n)).1, γ⟩) * pathWeight c π else 0 :=
        Finset.sum_congr rfl (fun π _ => heq π)
      _ ≤ ∑ π : StagePath G (n + 1), if (π.step 0).2.1 = u then S * pathWeight c π else 0 := by
        apply Finset.sum_le_sum
        intro π _
        split <;> [exact mul_le_mul_of_nonneg_right (hcol _) (pathWeight_nonneg c hc π); exact le_rfl]
      _ = S * pathCol c n u := by
        simp only [pathCol, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro π _
        split <;> simp only [mul_zero]
      _ ≤ S * S ^ (n + 1) := mul_le_mul_of_nonneg_left ih hS
      _ = S ^ (n + 1 + 1) := (pow_succ' S (n + 1)).symm

end AVRegularity.Construction.Preservation.Ledger
end
end

section
/-! A finite source coding counts each actual successor identity once. Unused code entries are
allowed in a nonnegative upper sum; decoding returns none when a code has incompatible data. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.Ledger
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {G : GenStage D hr Dm bw j₀}

/-- The path containing a single prescribed identity. -/
def singletonPath (e : LedgerEdge G) : StagePath G 1 where
  step _ := e
  joined j hj := by omega

/-- Two copied kinds; one fresh kind per alphabet letter; every nonempty path and each trivial
path has its own code. The length cap is one larger than the largest actual source path. -/
abbrev SourceCode (G : GenStage D hr Dm bw j₀) (A : Finset WordLetter) (J R : ℕ) :=
  {t : List WordLetter // t ∈ insert [] (wordsUpTo A (J + 1))} ×
    ((Bool × (Σ h : Fin (R + 2), StagePath G h.1)) ⊕
      ({l : WordLetter // l ∈ A} × (CompIn G.comps ⊕ (Σ h : Fin (R + 2), StagePath G h.1))))

/-- Encode all five source constructors without identifying distinct paths or identities. -/
def encodeSource (A : Finset WordLetter) (J R : ℕ) (s : SuccSource G)
    (hv : s.Valid A J) (hb : s.pathLen ≤ R) : SourceCode G A J R :=
  match s, hv, hb with
  | .copyDir t v u γ, hv, _ =>
      (⟨t, hv.1⟩, .inl (false, ⟨⟨1, by omega⟩, singletonPath ⟨v, u, γ⟩⟩))
  | .copyQuad t h π, hv, hb =>
      (⟨t, hv.1⟩, .inl (true, ⟨⟨h, by change h ≤ R at hb; omega⟩, π⟩))
  | .letterDiag t u, hv, _ =>
      (⟨t, hv.1⟩, .inr (⟨.diag, (hv.2.1 .diag rfl).2⟩, .inl u))
  | .letterMean t n h π, hv, hb =>
      (⟨t, hv.1⟩, .inr (⟨.mean n h, (hv.2.1 (.mean n h) rfl).2⟩,
        .inr ⟨⟨h, by change h ≤ R at hb; omega⟩, π⟩))
  | .letterCov t n h a a' π, hv, hb =>
      (⟨t, hv.1⟩, .inr (⟨.covariance n h a a', (hv.2.1 (.covariance n h a a') rfl).2⟩,
        .inr ⟨⟨h, by change h ≤ R at hb; omega⟩, π⟩))

/-- Decode an overcounting code, rejecting incompatible fresh letters and path lengths. -/
def decodeSource {A : Finset WordLetter} {J R : ℕ} (z : SourceCode G A J R) : Option (SuccSource G) :=
  match z.2 with
  | .inl (false, ⟨h, π⟩) =>
      if hh : 0 < h.1 then some (.copyDir z.1.1 (π.step ⟨0, hh⟩).1
        (π.step ⟨0, hh⟩).2.1 (π.step ⟨0, hh⟩).2.2) else none
  | .inl (true, ⟨h, π⟩) => some (.copyQuad z.1.1 h.1 π)
  | .inr (l, .inl u) => match l.1 with
      | .diag => some (.letterDiag z.1.1 u)
      | _ => none
  | .inr (l, .inr ⟨h, π⟩) => match l.1 with
      | .mean n k => if hk : h.1 = k then some (.letterMean z.1.1 n k (hk ▸ π)) else none
      | .covariance n k a a' =>
          if hk : h.1 = k then some (.letterCov z.1.1 n k a a' (hk ▸ π)) else none
      | _ => none

/-- Decoding recovers every valid source, including its full path and identity choices. -/
theorem decode_encode_source (A : Finset WordLetter) (J R : ℕ) (s : SuccSource G)
    (hv : s.Valid A J) (hb : s.pathLen ≤ R) :
    decodeSource (encodeSource A J R s hv hb) = some s := by
  cases s <;> simp [encodeSource, decodeSource, singletonPath]

/-- The old target of a code, before adding its passage word. -/
def codeOldTgt {A : Finset WordLetter} {J R : ℕ} (z : SourceCode G A J R) : Comp :=
  match z.2 with
  | .inl (_, ⟨_, π⟩) | .inr (_, .inr ⟨_, π⟩) => π.tgt
  | .inr (_, .inl u) => u.1

/-- The old source of a code. -/
def codeOldSrc {A : Finset WordLetter} {J R : ℕ} (z : SourceCode G A J R) : Comp :=
  match z.2 with
  | .inl (_, ⟨_, π⟩) | .inr (_, .inr ⟨_, π⟩) => π.src
  | .inr (_, .inl u) => u.1

/-- Endpoint information is retained by the coding. -/
theorem encodeSource_endpoints (A : Finset WordLetter) (J R : ℕ) (s : SuccSource G)
    (hv : s.Valid A J) (hb : s.pathLen ≤ R) :
    codeOldTgt (encodeSource A J R s hv hb) = s.oldTgt ∧
      codeOldSrc (encodeSource A J R s hv hb) = s.oldSrc := by
  cases s <;> simp [encodeSource, codeOldTgt, codeOldSrc, SuccSource.oldTgt, SuccSource.oldSrc,
    singletonPath, StagePath.tgt, StagePath.src]

end AVRegularity.Construction.Preservation.Ledger
end
end

section
/-! Finite source sums use only the old row and column bounds, never the number of components. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.Ledger
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {G : GenStage D hr Dm bw j₀}

/-- Zero-length copied paths have zero cost; fresh diagonal paths are coded separately. -/
def positivePathWeight (c : LedgerEdge G → ℝ) {h : ℕ} (π : StagePath G h) : ℝ :=
  if h = 0 then 0 else pathWeight c π

/-- Both orientations share the same counting argument. -/
def pathEndpoint (row : Bool) {h : ℕ} (π : StagePath G h) : Comp :=
  if row then π.tgt else π.src

def codeEndpoint (row : Bool) {A : Finset WordLetter} {J R : ℕ}
    (z : SourceCode G A J R) : Comp := if row then codeOldTgt z else codeOldSrc z

/-- Copied and fresh prices on the finite overcounting source codes. -/
def codePrice (C F : ℝ) (c : LedgerEdge G → ℝ) {A : Finset WordLetter} {J R : ℕ}
    (z : SourceCode G A J R) : ℝ :=
  match z.2 with
  | .inl (_, ⟨_, π⟩) => C * positivePathWeight c π
  | .inr (_, .inl _) => C * F
  | .inr (_, .inr ⟨_, π⟩) => C * F * positivePathWeight c π

theorem positivePathWeight_nonneg (c : LedgerEdge G → ℝ) (hc : ∀ e, 0 ≤ c e)
    {h : ℕ} (π : StagePath G h) : 0 ≤ positivePathWeight c π := by
  unfold positivePathWeight
  split <;> [exact le_rfl; exact pathWeight_nonneg c hc π]

theorem codePrice_nonneg (C F : ℝ) (hC : 0 ≤ C) (hF : 0 ≤ F)
    (c : LedgerEdge G → ℝ) (hc : ∀ e, 0 ≤ c e) {A : Finset WordLetter} {J R : ℕ}
    (z : SourceCode G A J R) : 0 ≤ codePrice C F c z := by
  rcases z with ⟨t, (⟨b, h, π⟩ | ⟨l, (u | ⟨h, π⟩)⟩)⟩
  · exact mul_nonneg hC (positivePathWeight_nonneg c hc π)
  · exact mul_nonneg hC hF
  · exact mul_nonneg (mul_nonneg hC hF) (positivePathWeight_nonneg c hc π)

/-- The geometric sum is uniformly bounded once the old ledger is at most one half. -/
theorem finite_geometric_le {S : ℝ} (hS : 0 ≤ S) (hhalf : S ≤ 1 / 2) (n : ℕ) :
    ∑ i : Fin n, S ^ (i.1 + 1) ≤ 2 * S := by
  induction n with
  | zero => simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hS
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    have heq : (∑ i : Fin n, S ^ (i.succ.1 + 1)) = S * ∑ i : Fin n, S ^ (i.1 + 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact pow_succ' S (i.1 + 1)
    rw [heq]
    simp only [Fin.val_zero, zero_add, pow_one]
    have hh := mul_le_mul_of_nonneg_left ih hS
    nlinarith only [hh, hhalf, hS]

/-- Sum all positive paths up to an arbitrary finite cutoff. -/
theorem positive_path_sum_le (c : LedgerEdge G → ℝ) (hc : ∀ e, 0 ≤ c e)
    {S : ℝ} (hS : 0 ≤ S) (hhalf : S ≤ 1 / 2)
    (hrow : ∀ v, ∑ u, ∑ γ, c ⟨v, u, γ⟩ ≤ S)
    (hcol : ∀ u, ∑ v, ∑ γ, c ⟨v, u, γ⟩ ≤ S)
    (row : Bool) (R : ℕ) (v : CompIn G.comps) :
    (∑ h : Fin (R + 2), ∑ π : StagePath G h.1,
      if pathEndpoint row π = v.1 then positivePathWeight c π else 0) ≤ 2 * S := by
  classical
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, positivePathWeight, ↓reduceIte, ite_self, Finset.sum_const_zero,
    zero_add, Fin.val_succ, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false]
  calc
    _ ≤ ∑ h : Fin (R + 1), S ^ (h.1 + 1) := by
      apply Finset.sum_le_sum
      intro h _
      cases row with
      | false =>
        have heq : (∑ π : StagePath G (h.1 + 1),
            if pathEndpoint false π = v.1 then pathWeight c π else 0) = pathCol c h.1 v := by
          simp [pathEndpoint, StagePath.src, pathCol]
        exact heq ▸ path_col_le c hc hS hcol h.1 v
      | true =>
        have heq : (∑ π : StagePath G (h.1 + 1),
            if pathEndpoint true π = v.1 then pathWeight c π else 0) = pathRow c h.1 v := by
          simp [pathEndpoint, StagePath.tgt, pathRow, Fin.last]
        exact heq ▸ path_row_le c hc hS hrow h.1 v
    _ ≤ 2 * S := finite_geometric_le hS hhalf _

/-- Summing all codes gives two copied path menus and one fresh path menu per letter. -/
theorem source_code_sum_le (C F : ℝ) (hC : 0 ≤ C) (hF : 0 ≤ F)
    (c : LedgerEdge G → ℝ) (hc : ∀ e, 0 ≤ c e)
    {S : ℝ} (hS : 0 ≤ S) (hhalf : S ≤ 1 / 2)
    (hrow : ∀ v, ∑ u, ∑ γ, c ⟨v, u, γ⟩ ≤ S)
    (hcol : ∀ u, ∑ v, ∑ γ, c ⟨v, u, γ⟩ ≤ S)
    (row : Bool) (A : Finset WordLetter) (J R : ℕ) (v : CompIn G.comps) :
    (∑ z : SourceCode G A J R,
      if codeEndpoint row z = v.1 then codePrice C F c z else 0) ≤
      ((insert [] (wordsUpTo A (J + 1))).card : ℝ) *
        (4 * C * S + 2 * (A.card : ℝ) * C * F) := by
  classical
  have hp := positive_path_sum_le c hc hS hhalf hrow hcol row R v
  have hdiag : (∑ u : CompIn G.comps, if u.1 = v.1 then C * F else 0) = C * F := by
    simp only [Subtype.val_inj]
    simp
  have hpath : (∑ h : Fin (R + 2), ∑ π : StagePath G h.1,
      if pathEndpoint row π = v.1 then C * positivePathWeight c π else 0) ≤ C * (2 * S) := by
    have heq : (∑ h : Fin (R + 2), ∑ π : StagePath G h.1,
        if pathEndpoint row π = v.1 then C * positivePathWeight c π else 0) =
        C * (∑ h : Fin (R + 2), ∑ π : StagePath G h.1,
          if pathEndpoint row π = v.1 then positivePathWeight c π else 0) := by
      simp only [Finset.mul_sum, mul_ite, mul_zero]
    rw [heq]
    exact mul_le_mul_of_nonneg_left hp hC
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
      4 * C * S + 2 * (A.card : ℝ) * C * F) (fun t _ => ?_)).trans ?_
  swap
  · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_coe, le_refl]
  
  have hendpath (t) (b) (h : Fin (R + 2)) (π : StagePath G h.1) :
      codeEndpoint (A := A) (J := J) (R := R) row (t, Sum.inl (b, ⟨h, π⟩)) = pathEndpoint row π := by cases row <;> rfl
  have henddiag (t) (l) (u : CompIn G.comps) :
      codeEndpoint (A := A) (J := J) (R := R) row (t, Sum.inr (l, Sum.inl u)) = u.1 := by cases row <;> rfl
  have hendfresh (t) (l) (h : Fin (R + 2)) (π : StagePath G h.1) :
      codeEndpoint (A := A) (J := J) (R := R) row (t, Sum.inr (l, Sum.inr ⟨h, π⟩)) = pathEndpoint row π := by cases row <;> rfl
  simp only [hendpath, henddiag, hendfresh, codePrice, Fintype.sum_bool, hdiag]
  have hletters : (∑ _l : {l : WordLetter // l ∈ A}, (C * F +
      (∑ h : Fin (R + 2), ∑ π : StagePath G h.1,
        if pathEndpoint row π = v.1 then C * F * positivePathWeight c π else 0))) ≤
        (A.card : ℝ) * (2 * C * F) := by
    calc
      _ ≤ ∑ _l : {l : WordLetter // l ∈ A}, 2 * C * F := by
        apply Finset.sum_le_sum
        intro l _
        linarith only [hfresh]
      _ = _ := by simp
  linarith only [hpath, hletters]

end AVRegularity.Construction.Preservation.Ledger
end
end
end

section
section
/-! Constant-map norms and diagonal weights telescope in the positive path products. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.Ledger
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- Composition never costs more than the product of the original constant-map norms. -/
theorem norm_rootPathMap_le (a b : ℕ) (fs : List (Σ x y : ℕ, hr x →L[ℝ] hr y)) :
    ‖rootPathMap hr a fs b‖ ≤ (fs.map fun f => ‖f.2.2‖).prod := by
  induction fs generalizing a b with
  | nil =>
    simp only [rootPathMap, List.map_nil, List.prod_nil]
    split
    · next h => subst b; exact ContinuousLinearMap.norm_id_le
    · simp only [norm_zero, zero_le_one]
  | cons f fs ih =>
    obtain ⟨x, y, f⟩ := f
    simp only [rootPathMap]
    split
    · next h =>
      subst a
      calc
        ‖(rootPathMap hr y fs b).comp f‖ ≤ ‖rootPathMap hr y fs b‖ * ‖f‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (fs.map fun f => ‖f.2.2‖).prod * ‖f‖ :=
          mul_le_mul_of_nonneg_right (ih y b) (norm_nonneg _)
        _ = ((⟨x, y, f⟩ :: fs).map fun f => ‖f.2.2‖).prod := by
          simp only [List.map_cons, List.prod_cons]
          exact mul_comm _ _
    · simp only [norm_zero, List.map_cons, List.prod_cons]
      exact mul_nonneg (norm_nonneg _) (List.prod_nonneg (fun _ h => by
        obtain ⟨f, _, rfl⟩ := List.mem_map.mp h
        exact norm_nonneg _))

/-- Positive endpoint ratios cancel at each intermediate component. -/
theorem path_normalization_product {G : GenStage D hr Dm bw j₀}
    (a : CompIn G.comps → ℝ) (ha : ∀ v, 0 < a v) {n : ℕ} (π : StagePath G (n + 1)) :
    pathWeight (fun e : LedgerEdge G => a e.1 / a e.2.1) π =
      a (π.step (Fin.last n)).1 / a (π.step 0).2.1 := by
  induction n with
  | zero => exact Fin.prod_univ_one _
  | succ n ih =>
    rw [pathWeight_last_prefix, ih]
    have hj : (π.step (Fin.last (n + 1))).2.1 = ((pathPrefix π).step (Fin.last n)).1 :=
      π.joined n (by omega)
    have hp0 : ((pathPrefix π).step 0).2.1 = (π.step 0).2.1 := rfl
    rw [hj, hp0]
    exact div_mul_div_cancel₀ (ha _).ne'

/-- An identity's inflated price pays its uninflated norm and record size. -/
theorem identity_uninflated_le {G : GenStage D hr Dm bw j₀}
    (e : LedgerEdge G) :
    ‖(G.fam.identity e.1 e.2.1 e.2.2).map‖ * (G.fam.identity e.1 e.2.1 e.2.2).record.size ≤
      ‖(G.fam.identity e.1 e.2.1 e.2.2).map‖ * (G.fam.identity e.1 e.2.1 e.2.2).record.size *
        constituentPrice (G.fam.identity e.1 e.2.1 e.2.2).record := by
  have hp : 1 ≤ constituentPrice (G.fam.identity e.1 e.2.1 e.2.2).record := le_max_left _ _
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp
    (mul_nonneg (norm_nonneg _) (G.fam.identity e.1 e.2.1 e.2.2).record.size_nonneg)

/-- Multiplying the original map norms and sizes along a path is paid by the original inflated
identity products, including identities whose present order has fallen to two. -/
theorem path_uninflated_le {G : GenStage D hr Dm bw j₀} {n : ℕ} (π : StagePath G n) :
    (∏ i, ‖(G.fam.identity _ _ (π.step i).2.2).map‖) *
        (∏ i, (G.fam.identity _ _ (π.step i).2.2).record.size) ≤
      pathWeight (fun e : LedgerEdge G => ‖(G.fam.identity e.1 e.2.1 e.2.2).map‖ *
        (G.fam.identity e.1 e.2.1 e.2.2).record.size *
          constituentPrice (G.fam.identity e.1 e.2.1 e.2.2).record) π := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod₀ (fun i _ => mul_nonneg (norm_nonneg _)
    (G.fam.identity _ _ (π.step i).2.2).record.size_nonneg)
      (fun i _ => identity_uninflated_le (π.step i))


/-- The inflated identity cost after conjugation by a positive diagonal. -/
def identityPrice (G : GenStage D hr Dm bw j₀) (a : Comp → ℝ) (e : LedgerEdge G) : ℝ :=
  a e.1.1 / a e.2.1.1 * (‖(G.fam.identity e.1 e.2.1 e.2.2).map‖ *
    (G.fam.identity e.1 e.2.1 e.2.2).record.size *
      constituentPrice (G.fam.identity e.1 e.2.1 e.2.2).record)

/-- A composed constant map and all its original record sizes are paid by the conjugated,
inflated identity product. -/
theorem normalized_path_price_le {G : GenStage D hr Dm bw j₀}
    (a : Comp → ℝ) (ha : ∀ v ∈ G.comps, 0 < a v) {n : ℕ} (π : StagePath G (n + 1))
    (r₀ r₁ : ℕ) :
    (a (π.step (Fin.last n)).1.1 / a (π.step 0).2.1.1) *
        (‖rootPathMap hr r₀ π.mapList r₁‖ * ∏ i, (G.fam.identity _ _ (π.step i).2.2).record.size) ≤
      pathWeight (identityPrice G a) π := by
  have hn := norm_rootPathMap_le r₀ r₁ π.mapList
  simp only [StagePath.mapList, List.map_ofFn, List.prod_ofFn] at hn
  have hsize : 0 ≤ ∏ i, (G.fam.identity _ _ (π.step i).2.2).record.size :=
    Finset.prod_nonneg (fun i _ => (G.fam.identity _ _ (π.step i).2.2).record.size_nonneg)
  have hp := mul_le_mul_of_nonneg_right hn hsize
  have hprod := hp.trans (path_uninflated_le π)
  have hnorm := path_normalization_product (fun v : CompIn G.comps => a v.1)
    (fun v => ha v.1 v.2) π
  have hapos : 0 ≤ a (π.step (Fin.last n)).1.1 / a (π.step 0).2.1.1 :=
    (div_pos (ha _ (π.step (Fin.last n)).1.2) (ha _ (π.step 0).2.1.2)).le
  calc
    _ ≤ (a (π.step (Fin.last n)).1.1 / a (π.step 0).2.1.1) *
        pathWeight (fun e : LedgerEdge G => ‖(G.fam.identity e.1 e.2.1 e.2.2).map‖ *
          (G.fam.identity e.1 e.2.1 e.2.2).record.size *
            constituentPrice (G.fam.identity e.1 e.2.1 e.2.2).record) π :=
      mul_le_mul_of_nonneg_left hprod hapos
    _ = pathWeight (identityPrice G a) π := by
      rw [← hnorm]
      exact (Finset.prod_mul_distrib).symm

/-- Fresh width inflation costs at most the reserved slow-order loss. The positive record
length cancels, so the estimate does not impose a separate lower bound on its scale. -/
theorem fresh_constituentPrice_le (r : ConstituentRecord) {E σ : ℝ} {d : ℕ}
    (hE : 0 < E) (hE1 : E ≤ 1) (hσ : 0 ≤ σ)
    (hw : r.width = r.length * E ^ σ) (hd : r.birthExcess ≤ d) :
    constituentPrice r ≤ E ^ (-σ * (d : ℝ)) := by
  have hr : r.length / r.width = E ^ (-σ) := by
    rw [hw, Real.rpow_neg hE.le]
    field_simp [r.length_pos.ne', (Real.rpow_pos_of_pos hE σ).ne']
  have hpow : (r.length / r.width) ^ r.birthExcess = E ^ (-σ * (r.birthExcess : ℝ)) := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hE.le]
  apply max_le
  · have hh := Real.rpow_le_rpow_of_exponent_ge hE hE1
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hσ) (Nat.cast_nonneg d))
    simpa only [Real.rpow_zero] using hh
  · rw [hpow]
    apply Real.rpow_le_rpow_of_exponent_ge hE hE1
    exact mul_le_mul_of_nonpos_left (by exact_mod_cast hd) (neg_nonpos.mpr hσ)

end AVRegularity.Construction.Preservation.Ledger
end
end

section
/-! Provenance supplies the direct, quadratic and fresh record prices used by the finite source
sum. These estimates concern the tagged record, independently of a coefficient decomposition. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.Ledger
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {G : GenStage D hr Dm bw j₀}

/-- A source is paid by a copied path or a fresh letter and path. -/
def sourcePrice (C F : ℝ) (c : LedgerEdge G → ℝ) : SuccSource G → ℝ
  | .copyDir _ v u γ => C * c ⟨v, u, γ⟩
  | .copyQuad _ _ π => C * positivePathWeight c π
  | .letterDiag .. => C * F
  | .letterMean _ _ _ π | .letterCov _ _ _ _ _ π => C * F * positivePathWeight c π

theorem encodeSource_price (C F : ℝ) (c : LedgerEdge G → ℝ) (A : Finset WordLetter)
    (J R : ℕ) (s : SuccSource G) (hv : s.Valid A J) (hb : s.pathLen ≤ R) :
    codePrice C F c (encodeSource A J R s hv hb) = sourcePrice C F c s := by
  cases s <;> simp [codePrice, encodeSource, sourcePrice, positivePathWeight, pathWeight,
    singletonPath]

/-- Convert a path's uninflated record bound into its old conjugated identity product. -/
theorem path_record_price_le (a : Comp → ℝ) (ha : ∀ v ∈ G.comps, 0 < a v)
    {h : ℕ} (π : StagePath G h) (hh : 1 ≤ h) (r₀ r₁ : ℕ) (r : ConstituentRecord)
    (K p : ℝ) (hK : 0 ≤ K) (hp : 0 ≤ p)
    (hs : r.size = K * ∏ i, (G.fam.identity _ _ (π.step i).2.2).record.size)
    (hf : constituentPrice r ≤ p) :
    (a π.tgt / a π.src) * (‖rootPathMap hr r₀ π.mapList r₁‖ * r.size * constituentPrice r) ≤
      K * p * pathWeight (identityPrice G a) π := by
  cases h with
  | zero => omega
  | succ n =>
    have hn := normalized_path_price_le a ha π r₀ r₁
    have hend : a π.tgt / a π.src =
        a (π.step (Fin.last n)).1.1 / a (π.step 0).2.1.1 := by
      simp [StagePath.tgt, StagePath.src, Fin.last]
    rw [← hend] at hn
    have hratio : 0 ≤ a π.tgt / a π.src := by
      rw [hend]
      exact (div_pos (ha _ (π.step (Fin.last n)).1.2) (ha _ (π.step 0).2.1.2)).le
    calc
      _ ≤ (a π.tgt / a π.src) * (‖rootPathMap hr r₀ π.mapList r₁‖ * r.size * p) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hf (mul_nonneg (norm_nonneg _) r.size_nonneg)) hratio
      _ = (K * p) * ((a π.tgt / a π.src) *
          (‖rootPathMap hr r₀ π.mapList r₁‖ * ∏ i, (G.fam.identity _ _ (π.step i).2.2).record.size)) :=
        by rw [hs]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hn (mul_nonneg hK hp)

/-- Fresh tags pay their original-order width inflation once. -/
theorem fresh_tag_price_le {C cr σ η E : ℝ} {N p d m : ℕ} {l : WordLetter}
    {path : List (Comp × Comp × Prov)} (r : ConstituentRecord)
    (hE : 0 < E) (hE1 : E ≤ 1) (hσ : 0 ≤ σ) (hscale : D.eps (m - 1) = E)
    (hd : letterOrder N p l - 2 ≤ d)
    (hm : ((Prov.letter m l path).tags (succProvParams D C cr σ η N p)).Matches r) :
    constituentPrice r ≤ E ^ (-σ * (d : ℝ)) := by
  apply fresh_constituentPrice_le r hE hE1 hσ
  · have hw := hm.2.2.2.2.1
    have hl := hm.2.2.2.1
    change r.width = freshWidth D cr σ (m - 1) at hw
    change r.length = freshLength D cr (m - 1) at hl
    rw [hw, freshWidth, ← hl, hscale]
  · exact (hm.2.2.1 ▸ hd)

/-- A nonnegative edge price is preserved by every source's diagonal normalization. -/
theorem source_record_price_le (a : Comp → ℝ) (ha : ∀ v ∈ G.comps, 0 < a v)
    {C cr σ η E F : ℝ} {N p d m : ℕ} {A : Finset WordLetter} {J : ℕ}
    (hC : 0 ≤ C) (hE : 0 < E) (hE1 : E ≤ 1) (hσ : 0 ≤ σ) (hF : 0 ≤ F)
    (hscale : D.eps (m - 1) = E) (hletters : ∀ l ∈ A, letterOrder N p l - 2 ≤ d)
    (hG : G.HasTags (succProvParams D C cr σ η N p))
    (s : SuccSource G) (hv : s.Valid A J) (r : ConstituentRecord)
    (hm : ((s.prov m).tags (succProvParams D C cr σ η N p)).Matches r)
    (r₀ r₁ : ℕ) (b : ℝ)
    (hratio : b ≤ (if s.letter? = none then 1 else F) * (a s.oldTgt / a s.oldSrc)) :
    b * (‖rootPathMap hr r₀ s.maps r₁‖ * r.size * constituentPrice r) ≤
      sourcePrice C (F * E ^ (ocDelta D.α D.q - η - σ * (d : ℝ))) (identityPrice G a) s := by
  have hmultiply : b * (‖rootPathMap hr r₀ s.maps r₁‖ * r.size * constituentPrice r) ≤
      ((if s.letter? = none then 1 else F) * (a s.oldTgt / a s.oldSrc)) *
        (‖rootPathMap hr r₀ s.maps r₁‖ * r.size * constituentPrice r) :=
    mul_le_mul_of_nonneg_right hratio
      (mul_nonneg (mul_nonneg (norm_nonneg _) r.size_nonneg) (le_trans zero_le_one (le_max_left _ _)))
  apply hmultiply.trans
  cases s with
  | copyDir t v u γ =>
    have hold := (hG v u γ).1
    have hs : r.size = C * (G.fam.identity v u γ).record.size := by
      rw [hm.1]
      change C * ((G.prov v u γ).tags (succProvParams D C cr σ η N p)).witness = _
      rw [← hold.1]
    have hp : constituentPrice r = constituentPrice (G.fam.identity v u γ).record := by
      unfold constituentPrice
      rw [hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2.1]
      change max 1 ((((G.prov v u γ).tags (succProvParams D C cr σ η N p)).length /
        ((G.prov v u γ).tags (succProvParams D C cr σ η N p)).width) ^
          ((G.prov v u γ).tags (succProvParams D C cr σ η N p)).birthExcess) = _
      rw [← hold.2.2.1, ← hold.2.2.2.1, ← hold.2.2.2.2.1]
    have hn := norm_rootPathMap_le r₀ r₁ (.copyDir t v u γ : SuccSource G).maps
    simp only [SuccSource.maps, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one] at hn
    simp only [SuccSource.letter?, ↓reduceIte, one_mul, SuccSource.oldTgt, SuccSource.oldSrc,
      sourcePrice, identityPrice]
    rw [hs, hp]
    have hratio0 : 0 ≤ a v.1 / a u.1 := (div_pos (ha _ v.2) (ha _ u.2)).le
    have hprice0 : 0 ≤ constituentPrice (G.fam.identity v u γ).record :=
      le_trans zero_le_one (le_max_left _ _)
    have hh := mul_le_mul_of_nonneg_right hn
      (mul_nonneg (G.fam.identity v u γ).record.size_nonneg hprice0)
    have hh' := mul_le_mul_of_nonneg_left hh (mul_nonneg hC hratio0)
    simpa only [SuccSource.maps, mul_assoc, mul_left_comm, mul_comm] using hh'
  | copyQuad t h π =>
    have hs : r.size = C * ∏ i, (G.fam.identity _ _ (π.step i).2.2).record.size := by
      rw [hm.1, SuccSource.prov, Providers.CascadeInvariants.Prov.tags_quad_witness,
        Providers.CascadeInvariants.prod_witness_provList hG]
      rfl
    have hp : constituentPrice r = 1 := by
      simp only [constituentPrice, hm.2.2.1, SuccSource.prov,
        Providers.CascadeInvariants.Prov.tags_quad_birthExcess, pow_zero, max_self]
    have hh := path_record_price_le a ha π hv.2.2 r₀ r₁ r C 1 hC zero_le_one hs hp.le
    simpa only [SuccSource.letter?, ↓reduceIte, one_mul, SuccSource.oldTgt, SuccSource.oldSrc,
      SuccSource.maps, sourcePrice, positivePathWeight, Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hv.2.2),
      ↓reduceIte, mul_one] using hh
  | letterDiag t u =>
    have hd := hletters .diag (hv.2.1 .diag rfl).2
    have hp := fresh_tag_price_le r hE hE1 hσ hscale hd hm
    have hs : r.size = C * E ^ (ocDelta D.α D.q - η) := by
      simpa only [SuccSource.prov, Prov.tags, Prov.pathTags, List.map_nil, List.prod_nil,
        succProvParams, one_mul, mul_one, hscale] using hm.1
    have hn : ‖rootPathMap hr r₀ (.letterDiag t u : SuccSource G).maps r₁‖ ≤ 1 := by
      simpa only [SuccSource.maps, List.map_nil, List.prod_nil] using norm_rootPathMap_le r₀ r₁ []
    have hh := mul_le_mul hn hp (le_trans zero_le_one (le_max_left _ _)) zero_le_one
    have he : E ^ (ocDelta D.α D.q - η) * E ^ (-σ * (d : ℝ)) =
        E ^ (ocDelta D.α D.q - η - σ * (d : ℝ)) := by
      rw [← Real.rpow_add hE]; congr 1; ring
    simp only [SuccSource.letter?, Option.some_ne_none, ↓reduceIte, SuccSource.oldTgt,
      SuccSource.oldSrc, div_self (ha _ u.2).ne', mul_one, sourcePrice]
    rw [hs]
    have hh' := mul_le_mul_of_nonneg_left hh (mul_nonneg (mul_nonneg hC hF)
      (Real.rpow_nonneg hE.le (ocDelta D.α D.q - η)))
    calc
      _ ≤ C * F * (E ^ (ocDelta D.α D.q - η) * E ^ (-σ * (d : ℝ))) := by
        nlinarith only [hh']
      _ = _ := by rw [he]; ring
  | letterMean t n h π | letterCov t n h a' a'' π =>
    have hl := (hv.2.1 _ rfl).2
    have hd := hletters _ hl
    have hp := fresh_tag_price_le r hE hE1 hσ hscale hd hm
    have hs : r.size = (C * E ^ (ocDelta D.α D.q - η)) *
        ∏ i, (G.fam.identity _ _ (π.step i).2.2).record.size := by
      rw [hm.1]
      simp only [SuccSource.prov, Prov.tags]
      rw [Providers.CascadeInvariants.prod_witness_provList hG]
      simp only [succProvParams, one_mul, hscale]
    have hh := path_record_price_le a ha π hv.2.2 r₀ r₁ r
      (C * E ^ (ocDelta D.α D.q - η)) (E ^ (-σ * (d : ℝ)))
      (mul_nonneg hC (Real.rpow_nonneg hE.le _)) (Real.rpow_nonneg hE.le _) hs hp
    have he : E ^ (ocDelta D.α D.q - η) * E ^ (-σ * (d : ℝ)) =
        E ^ (ocDelta D.α D.q - η - σ * (d : ℝ)) := by
      rw [← Real.rpow_add hE]; congr 1; ring
    have hh' := mul_le_mul_of_nonneg_left hh hF
    simp only [SuccSource.letter?, Option.some_ne_none, ↓reduceIte, SuccSource.oldTgt,
      SuccSource.oldSrc, SuccSource.maps, sourcePrice, positivePathWeight,
      Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hv.2.2), ↓reduceIte]
    calc
      _ ≤ F * ((C * E ^ (ocDelta D.α D.q - η) * E ^ (-σ * (d : ℝ))) *
          pathWeight (identityPrice G a) π) := by nlinarith only [hh']
      _ = _ := by rw [mul_assoc C, he]; ring

end AVRegularity.Construction.Preservation.Ledger
end
end

section
/-! Ordinary and marked matrices are the same positive identity prices with two diagonal
normalizations. The fresh mass prefactor is fixed before the ledger thresholds. -/
@[expose] public noncomputable section
namespace AVRegularity.Construction.Preservation.Ledger

/-- Choose the ordinary or marked diagonal. -/
def ledgerMarker (q : ℝ) (Λ : ℕ) (law : BirthLaw) (marked : Bool) (v : Comp) : ℝ :=
  if marked then compMarker q Λ law v else 1

def ledgerDiagonal (q : ℝ) (Λ : ℕ) (law : BirthLaw) (marked : Bool) (v : Comp) : ℝ :=
  ledgerMarker q Λ law marked v / Real.sqrt (compMass q Λ law v)

/-- Exact multiplier of a nonempty birth word for the chosen diagonal. -/
def birthDiagonalFactor (q : ℝ) (Λ m : ℕ) (law : BirthLaw) (marked : Bool) : ℝ :=
  (if marked then ocEpsilon q Λ (m - 1) ^ (-law.iota) else 1) /
    Real.sqrt (law.cH / (law.wordCount : ℝ) * ocEpsilon q Λ (m - 1) ^ law.etaB)

theorem ledgerMarker_pos {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ)
    (law : BirthLaw) (marked : Bool) (v : Comp) : 0 < ledgerMarker q Λ law marked v := by
  cases marked
  · exact zero_lt_one
  · exact Buffer.birth_compMarker_pos hq hΛ law v

theorem ledgerDiagonal_pos {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ)
    (law : BirthLaw) (marked : Bool) (v : Comp) : 0 < ledgerDiagonal q Λ law marked v :=
  div_pos (ledgerMarker_pos hq hΛ law marked v)
    (Real.sqrt_pos.mpr (Buffer.birth_compMass_pos hq hΛ law v))

theorem ledgerDiagonal_ratio {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ)
    (law : BirthLaw) (marked : Bool) (v u : Comp) :
    ledgerDiagonal q Λ law marked v / ledgerDiagonal q Λ law marked u =
      ledgerMarker q Λ law marked v / ledgerMarker q Λ law marked u *
        Real.sqrt (compMass q Λ law u / compMass q Λ law v) := by
  have hmv := Buffer.birth_compMass_pos hq hΛ law v
  have hmu := Buffer.birth_compMass_pos hq hΛ law u
  rw [Real.sqrt_div hmu.le]
  unfold ledgerDiagonal
  field_simp [(ledgerMarker_pos hq hΛ law marked u).ne', (Real.sqrt_pos.mpr hmv).ne',
    (Real.sqrt_pos.mpr hmu).ne']

theorem birthDiagonalFactor_pos {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ)
    (m : ℕ) (law : BirthLaw) (marked : Bool) : 0 < birthDiagonalFactor q Λ m law marked := by
  unfold birthDiagonalFactor
  apply div_pos
  · split
    · exact Real.rpow_pos_of_pos (Scales.epsilon_basic hq hΛ).1 _
    · exact zero_lt_one
  · apply Real.sqrt_pos.mpr
    exact mul_pos (div_pos law.cH_pos (by exact_mod_cast law.wordCount_pos))
      (Real.rpow_pos_of_pos (Scales.epsilon_basic hq hΛ).1 _)

/-- A word creates one birth irrespective of the word's length. -/
theorem ledgerDiagonal_succComp {q : ℝ} {Λ m : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ)
    (hm : 1 ≤ m) (law : BirthLaw) (marked : Bool) (v : Comp)
    (hold : ∀ e ∈ v.births, m ≤ e.scale) (t : List WordLetter) :
    ledgerDiagonal q Λ law marked (succComp m v t) =
      (if t = [] then 1 else birthDiagonalFactor q Λ m law marked) *
        ledgerDiagonal q Λ law marked v := by
  by_cases ht : t = []
  · simp [ht, succComp]
  · rw [ite_eq_right ht]
    unfold ledgerDiagonal
    rw [FullLift.succComp_mass law v ht, Real.sqrt_mul
      (mul_nonneg (div_pos law.cH_pos (by exact_mod_cast law.wordCount_pos)).le
        (Real.rpow_nonneg (Scales.epsilon_basic hq hΛ).1.le _))]
    have hw : ledgerMarker q Λ law marked (succComp m v t) =
        (if marked then ocEpsilon q Λ (m - 1) ^ (-law.iota) else 1) *
          ledgerMarker q Λ law marked v := by
      cases marked with
      | false => exact (one_mul 1).symm
      | true => exact FullLift.succComp_marker hm law v hold ht
    rw [hw]
    unfold birthDiagonalFactor
    ring

/-- Both fresh diagonal multipliers are at least one. -/
theorem one_le_birthDiagonalFactor {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ)
    (m : ℕ) (law : BirthLaw) (marked : Bool) (hc : law.cH ≤ 1)
    (hη : 0 ≤ law.etaB) (hi : 0 ≤ law.iota) : 1 ≤ birthDiagonalFactor q Λ m law marked := by
  have he := Scales.epsilon_basic (m := m - 1) hq hΛ
  have hnum : 1 ≤ (if marked then ocEpsilon q Λ (m - 1) ^ (-law.iota) else 1) := by
    split
    · exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos he.1 he.2.1 (neg_nonpos.mpr hi)
    · exact le_rfl
  have hden : Real.sqrt (law.cH / (law.wordCount : ℝ) * ocEpsilon q Λ (m - 1) ^ law.etaB) ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    have hratio : law.cH / (law.wordCount : ℝ) ≤ 1 :=
      (div_le_one₀ (by exact_mod_cast law.wordCount_pos)).mpr
        (hc.trans (by exact_mod_cast law.wordCount_pos))
    exact (mul_le_mul_of_nonneg_left (Real.rpow_le_one he.1.le he.2.1 hη)
      (div_pos law.cH_pos (by exact_mod_cast law.wordCount_pos)).le).trans
        (by simpa only [mul_one] using hratio)
  unfold birthDiagonalFactor
  apply (le_div_iff₀ (Real.sqrt_pos.mpr (mul_pos
    (div_pos law.cH_pos (by exact_mod_cast law.wordCount_pos))
    (Real.rpow_pos_of_pos he.1 _)))).mpr
  simpa only [one_mul] using hden.trans hnum


/-- The reciprocal square-root birth mass has the exact scale exponent. -/
theorem inv_sqrt_birth_mass {c T E η : ℝ} (hc : 0 < c) (hT : 0 < T) (hE : 0 < E) :
    1 / Real.sqrt (c / T * E ^ η) = Real.sqrt (T / c) * E ^ (-η / 2) := by
  rw [Real.sqrt_mul (div_pos hc hT).le, Real.sqrt_div hc.le,
    Real.sqrt_div hT.le]
  have hp : Real.sqrt (E ^ η) = E ^ (η / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hE.le]
    congr 1
    ring
  rw [hp]
  have he : E ^ (-η / 2) = (E ^ (η / 2))⁻¹ := by
    rw [show -η / 2 = -(η / 2) by ring, Real.rpow_neg hE.le]
  rw [he]
  field_simp [(Real.sqrt_pos.mpr hc).ne', (Real.sqrt_pos.mpr hT).ne',
    (Real.rpow_pos_of_pos hE (η / 2)).ne']

/-- The marked birth multiplier bounds the ordinary one and has a fixed prefactor. -/
theorem birthDiagonalFactor_le {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ)
    (m : ℕ) (law : BirthLaw) (marked : Bool) (hi : 0 ≤ law.iota) :
    birthDiagonalFactor q Λ m law marked ≤ Real.sqrt ((law.wordCount : ℝ) / law.cH) *
      ocEpsilon q Λ (m - 1) ^ (-law.etaB / 2 - law.iota) := by
  have he := Scales.epsilon_basic (m := m - 1) hq hΛ
  have hnum : (if marked then ocEpsilon q Λ (m - 1) ^ (-law.iota) else 1) ≤
      ocEpsilon q Λ (m - 1) ^ (-law.iota) := by
    split
    · exact le_rfl
    · exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos he.1 he.2.1 (neg_nonpos.mpr hi)
  unfold birthDiagonalFactor
  calc
    _ ≤ ocEpsilon q Λ (m - 1) ^ (-law.iota) *
        (1 / Real.sqrt (law.cH / (law.wordCount : ℝ) * ocEpsilon q Λ (m - 1) ^ law.etaB)) := by
      simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_right hnum
        (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ = _ := by
      rw [inv_sqrt_birth_mass law.cH_pos (by exact_mod_cast law.wordCount_pos) he.1]
      rw [mul_left_comm, ← Real.rpow_add he.1]
      congr 2
      ring

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {G : GenStage D hr Dm bw j₀}


/-- Equal passage words cancel their common positive diagonal factor. -/
theorem same_word_diagonal_ratio (a : Comp → ℝ) {F : ℝ} (hF : 0 < F)
    (hword : ∀ v ∈ G.comps, ∀ t, a (succComp G.level v t) =
      (if t = [] then 1 else F) * a v)
    (v u : CompIn G.comps) (t : List WordLetter) :
    a (succComp G.level v.1 t) / a (succComp G.level u.1 t) = a v.1 / a u.1 := by
  rw [hword _ v.2, hword _ u.2]
  have hf : (if t = [] then 1 else F) ≠ 0 := by split <;> [exact one_ne_zero; exact hF.ne']
  exact mul_div_mul_left _ _ hf

/-- Appending a letter costs at most one birth diagonal factor. -/
theorem letter_diagonal_ratio_le (a : Comp → ℝ) (ha : ∀ v ∈ G.comps, 0 < a v)
    {F : ℝ} (hF : 1 ≤ F)
    (hword : ∀ v ∈ G.comps, ∀ t, a (succComp G.level v t) =
      (if t = [] then 1 else F) * a v)
    (v u : CompIn G.comps) (t : List WordLetter) (l : WordLetter) :
    a (succComp G.level v.1 (t ++ [l])) / a (succComp G.level u.1 t) ≤ F * (a v.1 / a u.1) := by
  by_cases ht : t = []
  · rw [hword _ v.2, hword _ u.2]
    simp only [List.append_eq_nil_iff, List.cons_ne_self, and_false,
      ↓reduceIte, ht, one_mul]
    exact le_of_eq (mul_div_assoc _ _ _)
  · have he := same_word_diagonal_ratio a (lt_of_lt_of_le zero_lt_one hF) hword v u (t ++ [l])
    have hs : a (succComp G.level u.1 t) = a (succComp G.level u.1 (t ++ [l])) := by
      rw [hword _ u.2, hword _ u.2]
      simp [ht]
    rw [hs, he]
    exact (le_mul_iff_one_le_left (div_pos (ha _ v.2) (ha _ u.2))).mpr hF

/-- Copied sources cancel the word factor; fresh sources pay it once. -/
theorem source_diagonal_ratio_le (a : Comp → ℝ) (ha : ∀ v ∈ G.comps, 0 < a v)
    {F : ℝ} (hF : 1 ≤ F)
    (hword : ∀ v ∈ G.comps, ∀ t, a (succComp G.level v t) =
      (if t = [] then 1 else F) * a v)
    (s : SuccSource G) (hmem : s.oldTgt ∈ G.comps ∧ s.oldSrc ∈ G.comps) :
    a (s.tgtComp G.level) / a (s.srcComp G.level) ≤
      (if s.letter? = none then 1 else F) * (a s.oldTgt / a s.oldSrc) := by
  have hc := same_word_diagonal_ratio a (lt_of_lt_of_le zero_lt_one hF) hword
    ⟨s.oldTgt, hmem.1⟩ ⟨s.oldSrc, hmem.2⟩ s.word
  have hf (l : WordLetter) := letter_diagonal_ratio_le a ha hF hword
    ⟨s.oldTgt, hmem.1⟩ ⟨s.oldSrc, hmem.2⟩ s.word l
  cases s with
  | copyDir => simpa only [SuccSource.tgtComp, SuccSource.srcComp, SuccSource.newWord,
      SuccSource.letter?, SuccSource.oldTgt, SuccSource.oldSrc, SuccSource.word,
      ↓reduceIte, one_mul] using hc.le
  | copyQuad => simpa only [SuccSource.tgtComp, SuccSource.srcComp, SuccSource.newWord,
      SuccSource.letter?, SuccSource.oldTgt, SuccSource.oldSrc, SuccSource.word,
      ↓reduceIte, one_mul] using hc.le
  | letterDiag => simpa only [SuccSource.tgtComp, SuccSource.srcComp, SuccSource.newWord,
      SuccSource.letter?, SuccSource.oldTgt, SuccSource.oldSrc, SuccSource.word,
      Option.some_ne_none, ↓reduceIte] using hf .diag
  | letterMean t n h π => simpa only [SuccSource.tgtComp, SuccSource.srcComp, SuccSource.newWord,
      SuccSource.letter?, SuccSource.oldTgt, SuccSource.oldSrc, SuccSource.word,
      Option.some_ne_none, ↓reduceIte] using hf (.mean n h)
  | letterCov t n h a' a'' π => simpa only [SuccSource.tgtComp, SuccSource.srcComp, SuccSource.newWord,
      SuccSource.letter?, SuccSource.oldTgt, SuccSource.oldSrc, SuccSource.word,
      Option.some_ne_none, ↓reduceIte] using hf (.covariance n h a' a'')

/-- Sum of normalized identity prices equals the inflated majorant. -/
theorem sum_identityPrice_eq {G : GenStage D hr Dm bw j₀} (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ)
    (law : BirthLaw) (marked : Bool) (v u : CompIn G.comps) :
    (∑ γ, identityPrice G (ledgerDiagonal D.q D.Λ law marked) ⟨v, u, γ⟩) =
      pricedRecordMajorant (G.mass law) (fun c => ledgerMarker D.q D.Λ law marked c.1) G.fam v u := by
  unfold identityPrice
  dsimp only
  rw [← Finset.mul_sum, ledgerDiagonal_ratio hq hΛ]
  rfl

end AVRegularity.Construction.Preservation.Ledger
end
end

section
/-! The actual successor equivalences inject its identities into the finite source sum. -/
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Construction.Preservation.Ledger
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} {G G' : GenStage D hr Dm bw j₀}

/-- Only the source enumeration, endpoints, maps and tags are used in the record ledger. -/
structure ActualSources (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm bw j₀) where
  source : LedgerEdge G' → SuccSource G
  valid : ∀ e, (source e).Valid Mn.A Mn.J
  injective : Function.Injective source
  src : ∀ e, (source e).srcComp G.level = e.2.1.1
  tgt : ∀ e, (source e).tgtComp G.level = e.1.1
  tags : ∀ e, (((source e).prov G.level).tags P).Matches
    (G'.fam.identity e.1 e.2.1 e.2.2).record
  map_eq : ∀ e, (G'.fam.identity e.1 e.2.1 e.2.2).map =
    rootPathMap hr e.2.1.1.root (source e).maps e.1.1.root

theorem actual_sources {P : ProvParams} {Mn : SuccMenu}
    (hs : IsActualSuccessor D P Mn G G') : Nonempty (ActualSources P Mn G G') := by
  obtain ⟨e, _Cc, _Cc0, _hlift, _hdiag, hall⟩ := hs.2.2.2.2.2.2
  refine ⟨{ source := fun z => (e z.1 z.2.1 z.2.2).1
            valid := fun z => (e z.1 z.2.1 z.2.2).2.1
            src := fun z => (e z.1 z.2.1 z.2.2).2.2.1
            tgt := fun z => (e z.1 z.2.1 z.2.2).2.2.2
            tags := ?_
            map_eq := fun z => (hall z.1 z.2.1 z.2.2).2.1
            injective := ?_ }⟩
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

theorem source_old_mem {A : Finset WordLetter} {J : ℕ} (s : SuccSource G)
    (hv : s.Valid A J) : s.oldTgt ∈ G.comps ∧ s.oldSrc ∈ G.comps := by
  cases s with
  | copyDir t v u γ => exact ⟨v.2, u.2⟩
  | letterDiag t u => exact ⟨u.2, u.2⟩
  | copyQuad t h π | letterMean t n h π | letterCov t n h a a' π =>
    exact ⟨Providers.CascadeInvariants.stagePath_tgt_mem π hv.2.2,
      Providers.CascadeInvariants.stagePath_src_mem π hv.2.2⟩

/-- Inject actual identities into any nonnegative finite source coding. The counting and
endpoint argument is shared by the whole ledger and its fresh-only submatrix. -/
theorem actual_source_sums_le_of_code {P : ProvParams} {Mn : SuccMenu}
    (hs : IsActualSuccessor D P Mn G G')
    (hold : ∀ v ∈ G.comps, ∀ e ∈ v.births, G.level ≤ e.scale)
    (price : LedgerEdge G' → ℝ) (E : ActualSources P Mn G G')
    (sourceCost : SuccSource G → ℝ)
    (codeCost : ∀ R : ℕ, SourceCode G Mn.A Mn.J R → ℝ)
    (hcode0 : ∀ R z, 0 ≤ codeCost R z)
    (hcode : ∀ R s (hv : s.Valid Mn.A Mn.J) (hb : s.pathLen ≤ R),
      codeCost R (encodeSource Mn.A Mn.J R s hv hb) = sourceCost s)
    {B : ℝ} (hbound : ∀ R row (v : CompIn G.comps),
      (∑ z : SourceCode G Mn.A Mn.J R,
        if codeEndpoint row z = v.1 then codeCost R z else 0) ≤ B)
    (hcost : ∀ e, price e ≤ sourceCost (E.source e))
    (row : Bool) (v' : CompIn G'.comps) :
    (∑ e : LedgerEdge G', if (if row then e.1 else e.2.1) = v' then price e else 0) ≤ B := by
  classical
  let R := Finset.univ.sup (fun e : LedgerEdge G' => (E.source e).pathLen)
  have hb (e : LedgerEdge G') : (E.source e).pathLen ≤ R := by
    exact Finset.le_sup (f := fun e : LedgerEdge G' => (E.source e).pathLen) (Finset.mem_univ e)
  let code (e : LedgerEdge G') := encodeSource Mn.A Mn.J R (E.source e) (E.valid e) (hb e)
  have hinj : Function.Injective code := by
    intro e f hef
    apply E.injective
    have hh := congrArg decodeSource hef
    rw [decode_encode_source, decode_encode_source] at hh
    exact Option.some.inj hh
  have hvext : v'.1 ∈ succExtComps G.level Mn.A Mn.J G.comps := by
    rw [← hs.2.2.1]
    exact v'.2
  have hvparent : compParent G.level v'.1 ∈ G.comps :=
    FullLift.readout_parent_mem hs.1 hold hvext
  let v : CompIn G.comps := ⟨compParent G.level v'.1, hvparent⟩
  have hends (e : LedgerEdge G') : codeEndpoint row (code e) =
      compParent G.level (if row then e.1.1 else e.2.1.1) := by
    have he := encodeSource_endpoints Mn.A Mn.J R (E.source e) (E.valid e) (hb e)
    have hmem := source_old_mem (E.source e) (E.valid e)
    cases row with
    | false =>
      change codeOldSrc (code e) = _
      rw [he.2, ← E.src e, SuccSource.srcComp]
      exact (FullLift.parent_word_succComp hs.1 _ (hold _ hmem.2) _).1.symm
    | true =>
      change codeOldTgt (code e) = _
      rw [he.1, ← E.tgt e, SuccSource.tgtComp]
      exact (FullLift.parent_word_succComp hs.1 _ (hold _ hmem.1) _).1.symm
  let f := fun z : SourceCode G Mn.A Mn.J R =>
    if codeEndpoint row z = v.1 then codeCost R z else 0
  have hf : ∀ z, 0 ≤ f z := by
    intro z
    dsimp only [f]
    split <;> [exact hcode0 R z; exact le_rfl]
  calc
    _ ≤ ∑ e : LedgerEdge G', f (code e) := by
      apply Finset.sum_le_sum
      intro e _
      by_cases hev : (if row then e.1 else e.2.1) = v'
      · have hev' : (if row then e.1.1 else e.2.1.1) = v'.1 := by
          cases row <;> exact congrArg Subtype.val hev
        have hecode : codeEndpoint row (code e) = v.1 := by rw [hends, hev']
        simp only [hev, ↓reduceIte, f, hecode]
        exact (hcost e).trans_eq (hcode R (E.source e) (E.valid e) (hb e)).symm
      · simp only [hev, ↓reduceIte]
        exact hf (code e)
    _ ≤ ∑ z, f z := sum_comp_le code hinj f hf
    _ ≤ _ := hbound R row v


/-- Uniform row and column bounds for the successor from a sourcewise positive majorant. -/
theorem actual_source_sums_le {P : ProvParams} {Mn : SuccMenu}
    (hs : IsActualSuccessor D P Mn G G')
    (hold : ∀ v ∈ G.comps, ∀ e ∈ v.births, G.level ≤ e.scale)
    (a : Comp → ℝ) (C F : ℝ) (hC : 0 ≤ C) (hF : 0 ≤ F)
    (c : LedgerEdge G → ℝ) (hc : ∀ e, 0 ≤ c e)
    {S : ℝ} (hS : 0 ≤ S) (hhalf : S ≤ 1 / 2)
    (hrow : ∀ v, ∑ u, ∑ γ, c ⟨v, u, γ⟩ ≤ S)
    (hcol : ∀ u, ∑ v, ∑ γ, c ⟨v, u, γ⟩ ≤ S)
    (E : ActualSources P Mn G G')
    (hcost : ∀ e, identityPrice G' a e ≤ sourcePrice C F c (E.source e))
    (row : Bool) (v' : CompIn G'.comps) :
    (∑ e : LedgerEdge G', if (if row then e.1 else e.2.1) = v' then identityPrice G' a e else 0) ≤
      ((insert [] (wordsUpTo Mn.A (Mn.J + 1))).card : ℝ) *
        (4 * C * S + 2 * (Mn.A.card : ℝ) * C * F) := by
  exact actual_source_sums_le_of_code hs hold (identityPrice G' a) E (sourcePrice C F c)
    (fun _ => codePrice C F c) (fun _ z => codePrice_nonneg C F hC hF c hc z)
    (fun R s hv hb => encodeSource_price C F c Mn.A Mn.J R s hv hb)
    (fun R row v => source_code_sum_le C F hC hF c hc hS hhalf hrow hcol row Mn.A Mn.J R v)
    hcost row v'

end AVRegularity.Construction.Preservation.Ledger
end
end
end
