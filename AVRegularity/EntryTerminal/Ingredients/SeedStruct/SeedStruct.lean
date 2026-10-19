-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Proofs.CascadeInvariants.Scales
import AVRegularity.Construction.Preservation.FullLift.PositiveChartInputJets
import AVRegularity.Construction.Preservation.Buffer.KernelFluxTruncation
import AVRegularity.Construction.EntryScales.TerminalCore
import AVRegularity.EntryWeak.WeakCarrierAppend
import AVRegularity.CycleReference.TransitionZero
public import AVRegularity.EntryTerminal.Assembly.Seed.RetainedGeneric
import AVRegularity.Construction.Scales.Times
import Mathlib.Algebra.Order.Star.Real

section
section
/-! **The records of one actual successor** (`SeedStructPart`). The orders, the widths and the
higher original lengths of the identities of an actual successor `G'` of `G` are bounded by
those of `G` and by the fresh scales `R_b`, `r_b` of the passage, following the tags:
- a copy keeps the old order, width and length (`Prov.tags` of `.dir`);
- a quadratic conversion has order `2`, no higher length, and the width of the widest path
  record or the fresh width;
- a letter has the letter's order, the fresh length and the fresh width, and its letter is in
  the menu's alphabet (`SuccSource.Valid`).

`hasTags_of_seed`: the tags of seed provenance do not depend on the tag parameters.

Degenerate cases:
- No identities: vacuous.
- Only copies: the old bounds.
- Only letters: the fresh scales and the alphabet's orders. -/

@[expose] public noncomputable section

namespace AVRegularity.EntryTerminal.Ingredients

open AVRegularity.Construction.Preservation.FullLift

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- Seed provenance has the same tags for all tag parameters. -/
theorem hasTags_of_seed {P P' : ProvParams} {G : GenStage D hr Dm b j₀} (hG : G.HasTags P)
    (hseed : ∀ v u (γ : G.fam.Γ v u), ∃ k tag, G.prov v u γ = .seed k tag) : G.HasTags P' := by
  intro v u γ
  obtain ⟨k, tag, h⟩ := hseed v u γ
  have h1 := hG v u γ
  rw [h] at h1 ⊢
  exact h1

/-- **The records of an actual successor.** -/
theorem succ_records_le {P : ProvParams} {Mn : SuccMenu} {G G' : GenStage D hr Dm b j₀}
    (hG : G.HasTags P) (hact : IsActualSuccessor D P Mn G G') {Dt : ℕ} {ρ : ℝ}
    (h2 : 2 ≤ Dt) (hA : ∀ l ∈ Mn.A, letterOrder P.N P.p l ≤ Dt)
    (hoo : ∀ v u (γ : G.fam.Γ v u), (G.fam.identity v u γ).maxOrder ≤ Dt)
    (how : ∀ v u (γ : G.fam.Γ v u), (G.fam.identity v u γ).record.width ≤ ρ)
    (hol : ∀ v u (γ : G.fam.Γ v u), 1 ≤ (G.fam.identity v u γ).record.birthExcess →
      (G.fam.identity v u γ).record.length ≤ ρ)
    (hrb : P.rb (G.level - 1) ≤ ρ) (hRb : P.Rb (G.level - 1) ≤ ρ) :
    ∀ v u (γ : G'.fam.Γ v u), (G'.fam.identity v u γ).maxOrder ≤ Dt ∧
      (G'.fam.identity v u γ).record.width ≤ ρ ∧
      (1 ≤ (G'.fam.identity v u γ).record.birthExcess →
        (G'.fam.identity v u γ).record.length ≤ ρ) := by
  obtain ⟨_, _, _, _, htags, _, e, _, _, _, _, hall⟩ := hact
  have hwold : ∀ v u (γ : G.fam.Γ v u), ((G.prov v u γ).tags P).width ≤ ρ := by
    intro v u γ
    rw [← (hG v u γ).1.2.2.2.2.1]
    exact how v u γ
  have hpath {h : ℕ} (π : StagePath G h) (tw : ProvTags)
      (htw : tw ∈ Prov.pathTags P π.provList) : tw.width ≤ ρ := by
    rw [Providers.CascadeInvariants.pathTags_eq_map] at htw
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp htw
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact hwold _ _ _
  have hdw : ∀ m src, (Prov.tags P (.dir m src)).width = (src.tags P).width := fun _ _ => by
    simp [Prov.tags]
  have hlw : ∀ m l path, (Prov.tags P (.letter m l path)).width = P.rb (m - 1) := fun _ _ _ => by
    simp [Prov.tags]
  intro v u γ
  obtain ⟨hT, hO⟩ := htags v u γ
  obtain ⟨hprov, _⟩ := hall v u γ
  have hval := (e v u γ).2.1
  rw [hO, hT.2.2.2.2.1, hT.2.2.1, hT.2.2.2.1, hprov]
  generalize (e v u γ).1 = s at hval ⊢
  cases s with
  | copyDir t v₀ u₀ γ₀ =>
    obtain ⟨hT₀, hO₀⟩ := hG v₀ u₀ γ₀
    simp only [SuccSource.prov]
    refine ⟨?_, ?_, fun hbe => ?_⟩
    · rw [(Providers.CascadeInvariants.Prov.tags_dir_all P _ _).1, ← hO₀]
      exact hoo v₀ u₀ γ₀
    · rw [hdw]
      exact hwold v₀ u₀ γ₀
    · rw [(Providers.CascadeInvariants.Prov.tags_dir P _ _).2, ← hT₀.2.2.1] at hbe
      rw [(Providers.CascadeInvariants.Prov.tags_dir P _ _).1, ← hT₀.2.2.2.1]
      exact hol v₀ u₀ γ₀ hbe
  | copyQuad t h π =>
    simp only [SuccSource.prov]
    refine ⟨?_, ?_, fun hbe => ?_⟩
    · rw [Providers.CascadeInvariants.Prov.tags_quad_order]
      exact h2
    · cases hw : widestTags (Prov.pathTags P π.provList) with
      | none =>
        have hq : (Prov.tags P (.quad G.level π.provList)).width = P.rb (G.level - 1) := by
          simp [Prov.tags, hw]
        rw [hq]
        exact hrb
      | some tw =>
        have hq : (Prov.tags P (.quad G.level π.provList)).width = tw.width := by
          simp [Prov.tags, hw]
        rw [hq]
        exact hpath π tw (widestTags_mem hw)
    · rw [Providers.CascadeInvariants.Prov.tags_quad_birthExcess] at hbe
      omega
  | letterDiag t u₀ =>
    simp only [SuccSource.prov]
    refine ⟨?_, ?_, fun _ => ?_⟩
    · rw [(Providers.CascadeInvariants.Prov.tags_letter P _ _ _).1]
      exact hA _ (hval.2.1 WordLetter.diag rfl).2
    · rw [hlw]
      exact hrb
    · rw [Providers.CascadeInvariants.Prov.tags_letter_length]
      exact hRb
  | letterMean t n h π =>
    simp only [SuccSource.prov]
    refine ⟨?_, ?_, fun _ => ?_⟩
    · rw [(Providers.CascadeInvariants.Prov.tags_letter P _ _ _).1]
      exact hA _ (hval.2.1 (WordLetter.mean n h) rfl).2
    · rw [hlw]
      exact hrb
    · rw [Providers.CascadeInvariants.Prov.tags_letter_length]
      exact hRb
  | letterCov t n h a a' π =>
    simp only [SuccSource.prov]
    refine ⟨?_, ?_, fun _ => ?_⟩
    · rw [(Providers.CascadeInvariants.Prov.tags_letter P _ _ _).1]
      exact hA _ (hval.2.1 (WordLetter.covariance n h a a') rfl).2
    · rw [hlw]
      exact hrb
    · rw [Providers.CascadeInvariants.Prov.tags_letter_length]
      exact hRb

end AVRegularity.EntryTerminal.Ingredients
end
end

section
/-! **The mass sums of the retained terminal family** (`SeedStructPart`).

The retained components of grade at most one of the passage `m → m-1` from a stage without
births are the old components `v` and their children `(v, 𝔱)` with `1 ≤ |𝔱| ≤ J`. A child has the
mass `π_v · c_H/|𝔚| · ε_{m-1}^{η_b}` and a readout factor `ω_v (ε_{m-1}^{η_0})^{|𝔱|} ≤ ω_v`.
There are at most `|𝔚|` words, so both mass sums grow by at most the factor `1 + c_H`
(`retained_mass_sums_le`).

Degenerate cases:
- No old components: both sums are `0`.
- `J = 0`: no words, and the retained family is the old one.
- `ε_{m-1} = 1`: the children carry the full factor `c_H/|𝔚|`. -/

@[expose] public noncomputable section

namespace AVRegularity.EntryTerminal.Ingredients

open AVRegularity.Providers.CascadeInvariants

theorem compWord_succComp_ne (m : ℕ) (v : Comp) {t : List WordLetter} (ht : t ≠ []) :
    compWord m (succComp m v t) = t := by
  simp [compWord, succComp, ht]

theorem mem_wordsUpTo_of_length_le {A : Finset WordLetter} {L : ℕ} {t : List WordLetter}
    (ht : t ∈ wordsUpTo A (L + 1)) (hl : t.length ≤ L) : t ∈ wordsUpTo A L := by
  simp only [wordsUpTo, Finset.mem_biUnion, Finset.mem_Icc] at ht ⊢
  obtain ⟨k, hk, htk⟩ := ht
  have hkt := length_of_mem_wordsOfLength htk
  exact ⟨k, ⟨hk.1, by omega⟩, htk⟩

theorem ne_nil_of_mem_wordsUpTo {A : Finset WordLetter} {L : ℕ} {t : List WordLetter}
    (ht : t ∈ wordsUpTo A L) : t ≠ [] := by
  intro h
  have := (length_of_mem_wordsUpTo ht).1
  rw [h] at this
  simp at this

/-- The retained components lie in the old components and their children by the words of length
at most `J`. -/
theorem retained_subset {m J : ℕ} {A : Finset WordLetter} {S : Finset Comp} :
    (succExtComps m A J S).filter (IsRetained m 1 J) ⊆
      S ∪ (S ×ˢ wordsUpTo A J).image fun x => succComp m x.1 x.2 := by
  intro c hc
  rw [Finset.mem_filter] at hc
  obtain ⟨hc, hR⟩ := hc
  have hJ := (show compGrade c ≤ 1 ∧ (compWord m c).length ≤ J from hR).2
  simp only [succExtComps, Finset.mem_union, Finset.mem_image, Finset.mem_product] at hc
  rcases hc with hc | ⟨x, ⟨hx1, hx2⟩, rfl⟩
  · exact Finset.mem_union_left _ hc
  · rw [compWord_succComp_ne m x.1 (ne_nil_of_mem_wordsUpTo hx2)] at hJ
    exact Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨x, Finset.mem_product.mpr ⟨hx1, mem_wordsUpTo_of_length_le hx2 hJ⟩, rfl⟩)

/-- **A sum over the retained components** is at most `(1 + |W| r)` times the old sum when a child
weighs at most `r` times its parent. -/
theorem retained_sum_le {m J : ℕ} {A : Finset WordLetter} {S : Finset Comp} (g a : Comp → ℝ)
    (r : ℝ) (hg : ∀ c, 0 ≤ g c) (hgS : ∀ v ∈ S, g v ≤ a v)
    (hgW : ∀ v ∈ S, ∀ t ∈ wordsUpTo A J, g (succComp m v t) ≤ a v * r) :
    ∑ c ∈ (succExtComps m A J S).filter (IsRetained m 1 J), g c ≤
      (∑ v ∈ S, a v) * (1 + (wordsUpTo A J).card * r) := by
  classical
  calc ∑ c ∈ (succExtComps m A J S).filter (IsRetained m 1 J), g c
      ≤ ∑ c ∈ S ∪ (S ×ˢ wordsUpTo A J).image (fun x => succComp m x.1 x.2), g c :=
        Finset.sum_le_sum_of_subset_of_nonneg retained_subset fun c _ _ => hg c
    _ ≤ ∑ c ∈ S, g c + ∑ c ∈ (S ×ˢ wordsUpTo A J).image (fun x => succComp m x.1 x.2), g c := by
        have hi := Finset.sum_union_inter (s₁ := S)
          (s₂ := (S ×ˢ wordsUpTo A J).image (fun x => succComp m x.1 x.2)) (f := g)
        have hn : 0 ≤ ∑ c ∈ S ∩ (S ×ˢ wordsUpTo A J).image (fun x => succComp m x.1 x.2), g c :=
          Finset.sum_nonneg fun c _ => hg c
        linarith
    _ ≤ ∑ v ∈ S, a v + ∑ x ∈ S ×ˢ wordsUpTo A J, g (succComp m x.1 x.2) :=
        add_le_add (Finset.sum_le_sum hgS) (Finset.sum_image_le_of_nonneg fun c _ => hg c)
    _ ≤ ∑ v ∈ S, a v + ∑ x ∈ S ×ˢ wordsUpTo A J, a x.1 * r :=
        add_le_add le_rfl (Finset.sum_le_sum fun x hx =>
          hgW x.1 (Finset.mem_product.mp hx).1 x.2 (Finset.mem_product.mp hx).2)
    _ = (∑ v ∈ S, a v) * (1 + (wordsUpTo A J).card * r) := by
        rw [Finset.sum_product]
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [mul_add, mul_one, Finset.sum_mul]
        congr 1
        exact Finset.sum_congr rfl fun v _ => by ring

/-- `c_H/|𝔚| ε^{η_b}` times the number of words is at most `c_H`. -/
theorem card_mul_birthFactor_le {cH ε η : ℝ} {n w : ℕ} (hcH : 0 < cH) (hw : 0 < w) (hn : n ≤ w)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hη : 0 ≤ η) : (n : ℝ) * (cH / w * ε ^ η) ≤ cH := by
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  have hnw : (n : ℝ) / w ≤ 1 := (div_le_one hw').mpr (by exact_mod_cast hn)
  have he : ε ^ η ≤ 1 := Real.rpow_le_one hε0 hε1 hη
  have he0 : 0 ≤ ε ^ η := Real.rpow_nonneg hε0 η
  calc (n : ℝ) * (cH / w * ε ^ η) = cH * ((n : ℝ) / w) * ε ^ η := by ring
    _ ≤ cH * 1 * 1 := mul_le_mul (mul_le_mul_of_nonneg_left hnw hcH.le) he he0 (by positivity)
    _ = cH := by ring

/-- **The two mass sums of the retained terminal family** grow by at most `1 + c_H`. -/
theorem retained_mass_sums_le {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ) (lawW lawT : BirthLaw)
    (hm : lawT.rootMass = lawW.rootMass) (hr : lawT.rootReadout = lawW.rootReadout)
    (hηb : 0 ≤ lawT.etaB) (hη0 : 0 ≤ lawT.eta0) (m J : ℕ) (A : Finset WordLetter)
    (hW : (wordsUpTo A J).card ≤ lawT.wordCount) (S : Finset Comp)
    (hS : ∀ c ∈ S, c.births = []) :
    ∑ c ∈ (succExtComps m A J S).filter (IsRetained m 1 J), compMass q Λ lawT c ≤
        (1 + lawT.cH) * ∑ v ∈ S, compMass q Λ lawW v ∧
      ∑ c ∈ (succExtComps m A J S).filter (IsRetained m 1 J),
          compReadout q Λ lawT c ^ 2 * compMass q Λ lawT c ≤
        (1 + lawT.cH) * ∑ v ∈ S, compReadout q Λ lawW v ^ 2 * compMass q Λ lawW v := by
  obtain ⟨hε, hε1, -⟩ := Scales.epsilon_basic (m := m - 1) hq hΛ
  set r : ℝ := lawT.cH / lawT.wordCount * ocEpsilon q Λ (m - 1) ^ lawT.etaB with hrdef
  have hcard : ((wordsUpTo A J).card : ℝ) * r ≤ lawT.cH :=
    card_mul_birthFactor_le lawT.cH_pos lawT.wordCount_pos hW hε.le hε1 hηb
  have hmass0 : ∀ v ∈ S, compMass q Λ lawT v = compMass q Λ lawW v := by
    intro v hv
    simp [compMass, hS v hv, hm]
  have hread0 : ∀ v ∈ S, compReadout q Λ lawT v = compReadout q Λ lawW v := by
    intro v hv
    simp [compReadout, hS v hv, hr]
  have hmassW : ∀ v ∈ S, ∀ t ∈ wordsUpTo A J,
      compMass q Λ lawT (succComp m v t) = compMass q Λ lawW v * r := by
    intro v hv t ht
    simp [compMass, succComp, ne_nil_of_mem_wordsUpTo ht, hS v hv, hm, hrdef]
  have hreadW : ∀ v ∈ S, ∀ t ∈ wordsUpTo A J,
      compReadout q Λ lawT (succComp m v t) ^ 2 ≤ compReadout q Λ lawW v ^ 2 := by
    intro v hv t ht
    have hf : compReadout q Λ lawT (succComp m v t) =
        compReadout q Λ lawW v * (ocEpsilon q Λ (m - 1) ^ lawT.eta0) ^ t.length := by
      simp [compReadout, succComp, ne_nil_of_mem_wordsUpTo ht, hS v hv, hr]
    have h0 : 0 ≤ (ocEpsilon q Λ (m - 1) ^ lawT.eta0) ^ t.length :=
      pow_nonneg (Real.rpow_nonneg hε.le _) _
    have h1 : (ocEpsilon q Λ (m - 1) ^ lawT.eta0) ^ t.length ≤ 1 :=
      pow_le_one₀ (Real.rpow_nonneg hε.le _) (Real.rpow_le_one hε.le hε1 hη0)
    rw [hf, mul_pow]
    calc compReadout q Λ lawW v ^ 2 * ((ocEpsilon q Λ (m - 1) ^ lawT.eta0) ^ t.length) ^ 2
        ≤ compReadout q Λ lawW v ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ h0 h1) (sq_nonneg _)
      _ = compReadout q Λ lawW v ^ 2 := mul_one _
  have hpos : ∀ (law : BirthLaw) c, 0 < compMass q Λ law c :=
    fun law c => Construction.Preservation.Buffer.birth_compMass_pos hq hΛ law c
  have hfin {a : Comp → ℝ} (ha : ∀ v ∈ S, 0 ≤ a v) :
      (∑ v ∈ S, a v) * (1 + ((wordsUpTo A J).card : ℝ) * r) ≤ (1 + lawT.cH) * ∑ v ∈ S, a v := by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (by linarith) (Finset.sum_nonneg ha)
  constructor
  · refine (retained_sum_le (compMass q Λ lawT) (compMass q Λ lawW) r
      (fun c => (hpos lawT c).le) (fun v hv => (hmass0 v hv).le)
      (fun v hv t ht => (hmassW v hv t ht).le)).trans (hfin fun v _ => (hpos lawW v).le)
  · refine (retained_sum_le (fun c => compReadout q Λ lawT c ^ 2 * compMass q Λ lawT c)
      (fun v => compReadout q Λ lawW v ^ 2 * compMass q Λ lawW v) r
      (fun c => mul_nonneg (sq_nonneg _) (hpos lawT c).le) (fun v hv => ?_)
      (fun v hv t ht => ?_)).trans (hfin fun v _ => mul_nonneg (sq_nonneg _) (hpos lawW v).le)
    · rw [hread0 v hv, hmass0 v hv]
    · have hr0 : 0 ≤ r := by
        rw [hrdef]
        have := lawT.cH_pos
        have : (0 : ℝ) < lawT.wordCount := by exact_mod_cast lawT.wordCount_pos
        exact mul_nonneg (by positivity) (Real.rpow_nonneg hε.le _)
      rw [hmassW v hv t ht, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hreadW v hv t ht) (hpos lawW v).le) hr0

end AVRegularity.EntryTerminal.Ingredients
end
end
end

section
section
/-! **The seed of a re-rooting** (`SeedStructPart`). `IsSeedEncoding` copies the retained
family `G_t` onto the seed through `ι` and the edge equivalences `e`. Hence:
- the seed has the level of `G_t`, no births and seed provenance;
- it has the depth of `G_t`, and the orders and records of its identities;
- at a law with the seed's roots, its mass sums are those of `G_t` at the terminal law.

Degenerate cases:
- An empty retained family: an empty seed, zero sums.
- A family without identities: depth `0`, no record clauses.
- One root: the seed mass is the root mass. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance

namespace AVRegularity.EntryTerminal.Ingredients

variable {D : OCData} {b : ℝ} {j₀ : ℕ}

/-- **The structure of the seed of an encoding.** -/
theorem seedEncoding_struct {Dt Ds : ℕ} {Pt : ProvParams} {lawT : BirthLaw}
    {rootM rootR : ℕ → ℝ} {seedKt freshKt seedKc : ℕ → KernelSpec}
    {Gt : GenStage D ScalarH Dt b j₀} {seed : GenStage D ScalarH Ds b j₀}
    {ι : CompIn Gt.comps ≃ CompIn seed.comps}
    (he : IsSeedEncoding Pt lawT rootM rootR seedKt freshKt seedKc Gt seed ι) :
    seed.level = Gt.level ∧ (∀ v : CompIn seed.comps, v.1.births = []) ∧
      (∀ v u (γ : seed.fam.Γ v u), ∃ k tag, seed.prov v u γ = .seed k tag) ∧
      (∀ H : ℕ, Gt.fam.HasDepthAtMost H → seed.fam.HasDepthAtMost H) ∧
      (∀ (K : ℕ) (ρ : ℝ), (∀ v u (γ : Gt.fam.Γ v u), (Gt.fam.identity v u γ).maxOrder ≤ K ∧
          (Gt.fam.identity v u γ).record.width ≤ ρ ∧
          (1 ≤ (Gt.fam.identity v u γ).record.birthExcess →
            (Gt.fam.identity v u γ).record.length ≤ ρ)) →
        ∀ v u (γ : seed.fam.Γ v u), (seed.fam.identity v u γ).maxOrder ≤ K ∧
          (seed.fam.identity v u γ).record.width ≤ ρ ∧
          (1 ≤ (seed.fam.identity v u γ).record.birthExcess →
            (seed.fam.identity v u γ).record.length ≤ ρ)) ∧
      ∀ law : BirthLaw, law.rootMass = rootM → law.rootReadout = rootR →
        ∑ v, seed.mass law v = ∑ w, Gt.mass lawT w ∧
          ∑ v, seed.readoutWeight law v ^ 2 * seed.mass law v =
            ∑ w, Gt.readoutWeight lawT w ^ 2 * Gt.mass lawT w := by
  obtain ⟨hlev, hbirths, hroots, -, -, -, e, idx, -, hdata⟩ := he
  refine ⟨hlev, fun v => ?_, fun v u γ => ?_, fun H hG => ?_, fun K ρ hrec v u γ => ?_,
    fun law hm hr => ?_⟩
  · obtain ⟨w, rfl⟩ := ι.surjective v
    exact hbirths w
  · obtain ⟨v₀, rfl⟩ := ι.surjective v
    obtain ⟨u₀, rfl⟩ := ι.surjective u
    obtain ⟨γ₀, rfl⟩ := (e v₀ u₀).surjective γ
    exact ⟨_, _, (hdata v₀ u₀ γ₀).1⟩
  · intro p
    obtain ⟨k, hk⟩ := hG (fun j => ι.symm (p j))
    refine ⟨k, ⟨?_⟩⟩
    intro γ
    have heq : seed.fam.Γ (ι (ι.symm (p k.succ))) (ι (ι.symm (p k.castSucc))) =
        seed.fam.Γ (p k.succ) (p k.castSucc) := by simp only [Equiv.apply_symm_apply]
    exact hk.false ((e (ι.symm (p k.succ)) (ι.symm (p k.castSucc))).symm (cast heq.symm γ))
  · obtain ⟨v₀, rfl⟩ := ι.surjective v
    obtain ⟨u₀, rfl⟩ := ι.surjective u
    obtain ⟨γ₀, rfl⟩ := (e v₀ u₀).surjective γ
    obtain ⟨-, -, -, hrecd, hord, -⟩ := hdata v₀ u₀ γ₀
    rw [hord, hrecd]
    exact hrec v₀ u₀ γ₀
  · have hmass : ∀ w, seed.mass law (ι w) = Gt.mass lawT w := by
      intro w
      simp only [GenStage.mass, compMass, hbirths w, List.map_nil, List.prod_nil, mul_one, hm]
      exact (hroots w).1
    have hread : ∀ w, seed.readoutWeight law (ι w) = Gt.readoutWeight lawT w := by
      intro w
      simp only [GenStage.readoutWeight, compReadout, hbirths w, List.map_nil, List.prod_nil,
        mul_one, hr]
      exact (hroots w).2
    refine ⟨?_, ?_⟩
    · rw [← Equiv.sum_comp ι]
      exact Finset.sum_congr rfl fun w _ => hmass w
    · rw [← Equiv.sum_comp ι]
      exact Finset.sum_congr rfl fun w _ => by rw [hmass w, hread w]

end AVRegularity.EntryTerminal.Ingredients
end
end

section
/-! **The scales of the seed records** (`SeedStructPart`). At late terminal levels `M`, the
weak and fresh scales of the terminal passage are at most `ε_{M-1}`:
- the weak width `r_w = ε_M^{1+σ_w} ≤ ε_M ≤ ε_{M-1}`;
- the fresh length `ρ = c_r√(Bh) ≤ ε_{M-1}`, by `terminal_scales_core`
  (`ρ/ε_{M-1} ≤ C ε_{M-1}^{c}`);
- the fresh width `r_new = ρ ε_{M-1}^{t_T} ≤ ρ`;
- the weak lengths `C_L ε_{M+1} ≤ C_L ε_M ≤ 2 C_L ε_{M-1}^q ≤ ε_{M-1}`.

The `rpow` algebra is in abstract-real lemmas.

Degenerate cases:
- `C_L ≤ 0`: the length bound is trivial.
- `σ_w = 0`, `t_T = 0`: the widths are `ε_M` and `ρ`.
- `c_r = 1`: the largest fresh length allowed. -/

@[expose] public noncomputable section

namespace AVRegularity.EntryTerminal.Ingredients

open AVRegularity.EntryTerminal.Route

/-- `C_L e₁ ≤ E` from `e₁ ≤ y ≤ 2E^q` and `2 max(C_L,0) E^{q-1} ≤ 1`. -/
theorem seedStruct_len_le {CL e1 y E q : ℝ} (hE : 0 < E) (he1 : 0 ≤ e1) (he1y : e1 ≤ y)
    (hy : y ≤ 2 * E ^ q) (hs : 2 * max CL 0 * E ^ (q - 1) ≤ 1) : CL * e1 ≤ E := by
  have hEq : E ^ q = E ^ (q - 1) * E := by
    rw [Real.rpow_sub_one hE.ne', div_mul_cancel₀ _ hE.ne']
  calc CL * e1 ≤ max CL 0 * e1 := mul_le_mul_of_nonneg_right (le_max_left _ _) he1
    _ ≤ max CL 0 * (2 * E ^ q) := mul_le_mul_of_nonneg_left (he1y.trans hy) (le_max_right _ _)
    _ = (2 * max CL 0 * E ^ (q - 1)) * E := by rw [hEq]; ring
    _ ≤ 1 * E := mul_le_mul_of_nonneg_right hs hE.le
    _ = E := one_mul E

/-- `2c z ≤ 1` from `z ≤ (2c + 1)⁻¹`, `c ≥ 0`. -/
theorem seedStruct_small_le {c z : ℝ} (hc : 0 ≤ c) (hz : z ≤ (2 * c + 1)⁻¹) : 2 * c * z ≤ 1 := by
  have h1 : 0 < 2 * c + 1 := by linarith
  calc 2 * c * z ≤ 2 * c * (2 * c + 1)⁻¹ := mul_le_mul_of_nonneg_left hz (by linarith)
    _ = 2 * c / (2 * c + 1) := (div_eq_mul_inv _ _).symm
    _ ≤ 1 := (div_le_one h1).mpr (by linarith)

/-- `C z ≤ 1` from `z ≤ C⁻¹`, `C > 0`. -/
theorem seedStruct_mul_le_one {C z : ℝ} (hC : 0 < C) (hz : z ≤ C⁻¹) : C * z ≤ 1 :=
  (mul_le_mul_of_nonneg_left hz hC.le).trans (mul_inv_cancel₀ hC.ne').le

/-- **The scales of the seed records** at late terminal levels. -/
theorem seedStruct_scales (X : TermConstruction) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ (cr σw tT CL : ℝ), 0 < cr → 0 ≤ σw → 0 ≤ tT →
    ∃ M₀ : ℕ, 2 ≤ M₀ ∧ ∀ M : ℕ, M₀ ≤ M → ∀ D : OCData, D.α = X.α → D.q = X.q → D.Λ = Λ →
      IsOCBandChain X.α X.q Λ X.ζ M D.κ →
      D.termRW σw M ≤ D.eps (M - 1) ∧ D.termRho cr M ≤ D.eps (M - 1) ∧
        D.termRNew cr tT M ≤ D.eps (M - 1) ∧ CL * D.eps (M + 1) ≤ D.eps (M - 1) := by
  obtain ⟨ΛT, hΛT, hT⟩ := EntryScales.terminal_scales_core X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq X.hζ
  refine ⟨ΛT, hΛT, fun Λ hΛ cr σw tT CL hcr hσ htT => ?_⟩
  have h128 : 128 ≤ Λ := hΛT.trans hΛ
  have hq1 : 1 < X.q := X.hq.1
  obtain ⟨C, M₁, hC1, hsc⟩ := hT Λ hΛ cr hcr
  have hC : 0 < C := by linarith
  have hc := (Scales.admissible_exponent_facts X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq).2.2.2.2.2
  obtain ⟨Ma, hMa⟩ := EntryWeakProofs.weak_epsilon_rpow_eventually_small hq1 h128 hc
    (inv_pos.mpr hC)
  have hc0 : 0 ≤ max CL 0 := le_max_right _ _
  obtain ⟨Mb, hMb⟩ := EntryWeakProofs.weak_epsilon_rpow_eventually_small hq1 h128
    (sub_pos.mpr hq1) (c := (2 * max CL 0 + 1)⁻¹) (by positivity)
  refine ⟨max (max 2 M₁) (max (Ma + 1) (Mb + 1)), le_trans (le_max_left _ _) (le_max_left _ _),
    fun M hM D hDα hDq hDΛ hband => ?_⟩
  have hM2 : 2 ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hM
  have hM₁ : M₁ ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hM
  have hMa' : Ma ≤ M - 1 := by
    have := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM
    omega
  have hMb' : Mb ≤ M - 1 := by
    have := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hM
    omega
  obtain ⟨-, -, -, -, hrho, -⟩ := hsc M hM₁ D.κ hband
  simp only [OCData.termRW, OCData.termRho, OCData.termRNew, OCData.termB, OCData.termH,
    OCData.eps, hDα, hDq, hDΛ]
  obtain ⟨hε, hε1, -⟩ := Scales.epsilon_basic (m := M) hq1 h128
  obtain ⟨hE, hE1, -⟩ := Scales.epsilon_basic (m := M - 1) hq1 h128
  have hεE : ocEpsilon X.q Λ M ≤ ocEpsilon X.q Λ (M - 1) := by
    have h := CycleReference.epsilon_succ_le (q := X.q) (Λ := Λ) (n := M - 1) hq1 h128
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ M)] at h
  have hρ : cr * Real.sqrt (D.κ (M - 1) * ocTauPP X.α X.q Λ M) ≤ ocEpsilon X.q Λ (M - 1) :=
    (div_le_one hE).mp (hrho.trans (seedStruct_mul_le_one hC (hMa (M - 1) hMa')))
  have hρ0 : 0 ≤ cr * Real.sqrt (D.κ (M - 1) * ocTauPP X.α X.q Λ M) :=
    mul_nonneg hcr.le (Real.sqrt_nonneg _)
  refine ⟨?_, hρ, ?_, ?_⟩
  · calc ocEpsilon X.q Λ M ^ (1 + σw) ≤ ocEpsilon X.q Λ M ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)
      _ = ocEpsilon X.q Λ M := Real.rpow_one _
      _ ≤ ocEpsilon X.q Λ (M - 1) := hεE
  · calc cr * Real.sqrt (D.κ (M - 1) * ocTauPP X.α X.q Λ M) * ocEpsilon X.q Λ (M - 1) ^ tT
        ≤ cr * Real.sqrt (D.κ (M - 1) * ocTauPP X.α X.q Λ M) * 1 :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_one hE.le hE1 htT) hρ0
      _ ≤ ocEpsilon X.q Λ (M - 1) := (mul_one _).trans_le hρ
  · have h1 := CycleReference.epsilon_succ_le (q := X.q) (Λ := Λ) (n := M) hq1 h128
    have h2 := Scales.epsilon_q_step hq1 X.hq.2.1 h128 (by omega : 1 ≤ M)
    exact seedStruct_len_le hE (Scales.epsilon_basic (m := M + 1) hq1 h128).1.le h1 h2
      (seedStruct_small_le hc0 (hMb (M - 1) hMb'))

end AVRegularity.EntryTerminal.Ingredients
end
end

section
/-! **The structure of the seed** (`SeedStructPart`). The law constant is `c_H = 1/8`. At the
per-level context:
- level: the seed has the level of the retained family, `M - 1`;
- births and seed provenance: from the re-rooting (`seedEncoding_struct`);
- depth `≤ r̄₀`: the retained family is one cascade step from the weak stage (no births, depth
  `≤ d_w`), so its depth is at most `r_1 = (R_T+2)(d_w+1) - 1 ≤ r̄₀` (`cascade_depth`);
- orders `≤ D̄₀`, widths `≤ ε_{M-1}`, higher lengths `≤ ε_{M-1}`: `succ_records_le` with the weak
  records and the fresh scales (`seedStruct_scales`);
- the mass sums: `≤ (1 + 1/8)·2/3 = 3/4 < 5/6` (`retained_mass_sums_le`).

Degenerate cases:
- An empty weak stage: the seed is empty and the sums are `0 < 5/6`.
- A weak stage without identities: depth `0`, and the identities of the seed are letters on the
  first source.
- `R_T = 0`: no words, and the retained family is the weak one. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance

namespace AVRegularity.EntryTerminal.Ingredients

open AVRegularity.EntryTerminal.Route

/-- A depth bound for a larger bound. -/
theorem stage_hasDepthAtMost_mono {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
    [∀ r, NormedSpace ℝ (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    {G : GenStage D hr Dm b j₀} {H H' : ℕ} (hH : H ≤ H') (hG : G.fam.HasDepthAtMost H) :
    G.fam.HasDepthAtMost H' := by
  intro p
  obtain ⟨k, hk⟩ := hG (fun j => p ⟨j.1, by have := j.2; omega⟩)
  exact ⟨⟨k.1, by have := k.2; omega⟩, hk⟩

/-- The zero floors (the structure part constrains no seed constant). -/
def seedStructFloors : SeedFloors where
  cker := fun _ _ => 0
  Γk := fun _ => 0
  Cwid := fun _ => 0
  Ca := fun _ => 0
  Cm := fun _ _ => 0

/-- **The structure of the seed.** -/
theorem seedStruct : SeedStructPart := by
  intro X
  obtain ⟨Λ₀, h128, hsc⟩ := seedStruct_scales X
  refine ⟨Λ₀, h128, fun A hΛ hA Kout => ⟨0, 0, fun sXT sZT _ _ => ⟨0, seedStructFloors,
    fun Lt nW cr kS hplan cK CL Cχ kW _ _ _ cP CP _ => ?_⟩⟩⟩
  show SeedStructBlock A sXT sZT nW cr CL Cχ kW cP CP
  unfold SeedStructBlock
  obtain ⟨-, -, -, ⟨-, -, -, -, hσw, -, -, hη₀, -⟩, -, hsched, -, -⟩ := hA
  obtain ⟨-, -, -, -, -, -, -, -, htT, -⟩ := hsched
  obtain ⟨-, -, -, -, hcr, -⟩ := hplan
  refine ⟨1 / 8, by norm_num, by norm_num, fun Cw _ j₀ => ?_⟩
  obtain ⟨M₀, -, hM₀⟩ := hsc A.Λ hΛ cr A.σw A.tT CL hcr hσw.le htT.le
  refine ⟨M₀, fun M hM => ?_⟩
  intro D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx
  obtain ⟨hD, hW, -, -, -, hlaw, hsucc, henc, -, -, -⟩ := hctx
  obtain ⟨hDα, hDq, hDΛ, -, -, hband, -⟩ := hD
  obtain ⟨-, -, hlevW, hdepthW, hbirthsW, ⟨hseedW, -, -⟩, hrecW, hmassW, hreadW, hinv⟩ := hW
  obtain ⟨hrm, hrr, hcH, -, hwc, hetaB, heta0⟩ := hlaw
  obtain ⟨hslev, hsb, hsprov, hsdepth, hsrec, hsmass⟩ := seedEncoding_struct henc
  obtain ⟨hs1, hs3, hs2, hs4⟩ := hM₀ M hM D hDα hDq hDΛ hband
  -- the records of the retained family
  have hGt := succ_records_le (hasTags_of_seed hinv.2.1 hseedW) hsucc (Dt := A.Dt)
    (ρ := D.eps (M - 1)) (le_max_left _ _)
    (fun l hl => le_trans (Finset.le_sup (f := letterOrder A.NT A.pT) hl)
      (le_trans (le_max_right _ _) (le_max_right _ _)))
    (fun v u γ => (hrecW v u γ).1.trans (le_trans (le_max_left _ _) (le_max_right _ _)))
    (fun v u γ => by rw [(hrecW v u γ).2.1]; exact hs1)
    (fun v u γ _ => (hrecW v u γ).2.2.1.trans hs4) hs2 hs3
  refine ⟨?_, hsb, hsprov, ?_, ?_, fun law hm hr => ?_⟩
  · -- the level
    rw [hslev]
    show Gt'.level = M - 1
    rw [hsucc.2.1, hlevW]
  · -- the depth
    have hcasc := IsCascadeStage.step IsCascadeStage.seed hsucc
    have hd := Providers.CascadeInvariants.cascade_depth hbirthsW hdepthW hcasc
    rw [hlevW] at hd
    apply hsdepth
    refine stage_hasDepthAtMost_mono ?_ hd
    show (A.RT + 2) * (A.dW + 1) - 1 ≤ max 2 ((A.RT + 2) * (A.dW + 1) - 1)
    exact le_max_right _ _
  · -- orders, widths and higher lengths
    exact hsrec A.Dt (D.eps (M - 1)) fun v u γ =>
      hGt ⟨v.1, Finset.filter_subset _ _ v.2⟩ ⟨u.1, Finset.filter_subset _ _ u.2⟩ γ
  · -- the two mass sums
    obtain ⟨h1, h2⟩ := hsmass law hm hr
    rw [h1, h2]
    have hq1 : 1 < D.q := hDq ▸ X.hq.1
    have hΛD : 128 ≤ D.Λ := hDΛ ▸ (h128.trans hΛ)
    have hcomps : (Gt'.retained M 1 A.RT).comps =
        (succExtComps M A.alph A.RT Gw.comps).filter (IsRetained M 1 A.RT) := by
      show Gt'.comps.filter (IsRetained M 1 A.RT) = _
      rw [hsucc.2.2.1, hlevW]
      rfl
    obtain ⟨hb1, hb2⟩ := retained_mass_sums_le hq1 hΛD lawW lawT hrm hrr
      (by rw [hetaB]; positivity) (by rw [heta0]; exact hη₀.le) M A.RT A.alph
      (by rw [hwc]; exact le_max_right _ _) Gw.comps (fun c hc => hbirthsW ⟨c, hc⟩)
    have e1 : ∑ w, (Gt'.retained M 1 A.RT).mass lawT w =
        ∑ c ∈ (succExtComps M A.alph A.RT Gw.comps).filter (IsRetained M 1 A.RT),
          compMass D.q D.Λ lawT c := by
      rw [← hcomps]
      exact Finset.sum_coe_sort _ _
    have e2 : ∑ w, (Gt'.retained M 1 A.RT).readoutWeight lawT w ^ 2 *
          (Gt'.retained M 1 A.RT).mass lawT w =
        ∑ c ∈ (succExtComps M A.alph A.RT Gw.comps).filter (IsRetained M 1 A.RT),
          compReadout D.q D.Λ lawT c ^ 2 * compMass D.q D.Λ lawT c := by
      rw [← hcomps]
      exact Finset.sum_coe_sort _ (fun c => compReadout D.q D.Λ lawT c ^ 2 * compMass D.q D.Λ lawT c)
    have e3 : ∑ v, Gw.mass lawW v = ∑ c ∈ Gw.comps, compMass D.q D.Λ lawW c :=
      Finset.sum_coe_sort _ _
    have e4 : ∑ v, Gw.readoutWeight lawW v ^ 2 * Gw.mass lawW v =
        ∑ c ∈ Gw.comps, compReadout D.q D.Λ lawW c ^ 2 * compMass D.q D.Λ lawW c :=
      Finset.sum_coe_sort _ (fun c => compReadout D.q D.Λ lawW c ^ 2 * compMass D.q D.Λ lawW c)
    refine ⟨?_, ?_⟩
    · rw [e1]
      calc _ ≤ (1 + lawT.cH) * ∑ c ∈ Gw.comps, compMass D.q D.Λ lawW c := hb1
        _ ≤ (1 + 1 / 8) * (2 / 3) := by
          rw [hcH, ← e3]
          exact mul_le_mul_of_nonneg_left hmassW (by norm_num)
        _ < 5 / 6 := by norm_num
    · rw [e2]
      calc _ ≤ (1 + lawT.cH) *
            ∑ c ∈ Gw.comps, compReadout D.q D.Λ lawW c ^ 2 * compMass D.q D.Λ lawW c := hb2
        _ ≤ (1 + 1 / 8) * (2 / 3) := by
          rw [hcH, ← e4]
          exact mul_le_mul_of_nonneg_left hreadW (by norm_num)
        _ < 5 / 6 := by norm_num

end AVRegularity.EntryTerminal.Ingredients
end
end
end
