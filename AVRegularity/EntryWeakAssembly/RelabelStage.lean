-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeakAssembly.StoredSourceCounting

section
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs

/-! All component and source-count constants depend only on the fixed weak menus. -/

open Homogenization
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- One finite count covers empty/nonempty response words and the component extension. -/
def weakStoredWordBudget (N R : ℕ) : ℕ :=
  max (Fintype.card (WeakStoredWords N R)) (1 + (wordsUpTo (weakAlphabet N) R).card)

theorem weakStoredWordBudget_one_le (N R : ℕ) : 1 ≤ weakStoredWordBudget N R :=
  (Nat.le_add_right 1 _).trans (le_max_right _ _)

theorem weakExtComps_card_le (m N R : ℕ) (S : Finset Comp) :
    (weakExtComps m N R S).card ≤ S.card * weakStoredWordBudget N R := by
  classical
  calc
    _ ≤ S.card + ((S ×ˢ wordsUpTo (weakAlphabet N) R).image (fun x => succComp m x.1 x.2)).card :=
      Finset.card_union_le _ _
    _ ≤ S.card + (S ×ˢ wordsUpTo (weakAlphabet N) R).card :=
      Nat.add_le_add_left (Finset.card_image_le) _
    _ = S.card * (1 + (wordsUpTo (weakAlphabet N) R).card) := by
      rw [Finset.card_product]
      ring
    _ ≤ _ := Nat.mul_le_mul_left _ (le_max_right _ _)

/-- The actual construction has a uniform component count, including empty response menus. -/
theorem weakConstruction_card_le (P : ProvParams) (Mn : WeakMenu)
    (M J r : ℕ) (rW : ℝ) (stage : ℕ → GenStage D (fun _ => ℝ) Dm b j₀)
    (hc : IsWeakConstruction D P Mn M J rW r stage)
    (i : ℕ) (hi : M ≤ i) (hit : i ≤ M + J) :
    (stage i).comps.card ≤ weakStoredWordBudget Mn.N Mn.R ^ J := by
  have main : ∀ n, n ≤ J →
      (stage (M + J - n)).comps.card ≤ weakStoredWordBudget Mn.N Mn.R ^ n := by
    intro n
    induction n with
    | zero =>
      intro _
      simp only [Nat.sub_zero, hc.2.1.2.1, Finset.card_singleton, pow_zero, le_refl]
    | succ n ih =>
      intro hn
      have hp := (hc.2.2 (M + J - n) (by omega) (by omega)).1
      have hh : M + J - (n + 1) = M + J - n - 1 := by omega
      rw [hh, hp.2.2.2.1]
      exact (weakExtComps_card_le _ Mn.N Mn.R _).trans
        ((Nat.mul_le_mul_right _ (ih (by omega))).trans_eq (pow_succ _ _).symm)
  have hh : M + J - (M + J - i) = i := by omega
  have hm := main (M + J - i) (by omega)
  rw [hh] at hm
  exact hm.trans (pow_le_pow_right₀ (weakStoredWordBudget_one_le Mn.N Mn.R) (by omega))

/-- Once the incoming total is at most one, all positive path powers cost that total once. -/
theorem weakStoredTotal_passage_linear (P : ProvParams) (Mn : WeakMenu) (J Din H : ℕ)
    (rW : ℝ) (G G' : GenStage D (fun _ => ℝ) Dm b j₀)
    (hp : IsWeakPassage D P Mn rW Din G G') (ht : G.HasTags P) (ht' : G'.HasTags P)
    (hN : 1 ≤ Mn.N) (hJ : 1 ≤ J) (heps : ∀ i, 0 < D.eps i)
    (hpath : ∀ h, StagePath G h → h ≤ H) (hsmall : weakStoredTotal G Mn.N J Mn.η0 ≤ 1) :
    weakStoredTotal G' Mn.N J Mn.η0 ≤
      (Fintype.card (WeakStoredWords Mn.N Mn.R) : ℝ) * (Mn.N + Din + 1) * H *
        weakStoredTotal G Mn.N J Mn.η0 +
      (Fintype.card (CompIn G.comps) : ℝ) * Fintype.card (WeakStoredWords Mn.N Mn.R) *
        (Mn.N + 2) * weakStoredEddyWeight D Mn.N J Mn.η0 G.level := by
  have hnonneg := weakStoredTotal_nonneg G Mn.N J Mn.η0
  have hpow (h : Fin H) : weakStoredTotal G Mn.N J Mn.η0 ^ (h.1 + 1) ≤
      weakStoredTotal G Mn.N J Mn.η0 := by
    rw [pow_succ]
    exact mul_le_of_le_one_left hnonneg (pow_le_one₀ hnonneg hsmall)
  have hh : (∑ h : Fin H, weakStoredTotal G Mn.N J Mn.η0 ^ (h.1 + 1)) ≤
      ∑ _h : Fin H, weakStoredTotal G Mn.N J Mn.η0 := Finset.sum_le_sum (fun h _ => hpow h)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  refine (weakStoredTotal_passage_le P Mn J Din H rW G G' hp ht ht' hN hJ heps hpath).trans ?_
  have hm := mul_le_mul_of_nonneg_left hh
    (by positivity : 0 ≤ (Fintype.card (WeakStoredWords Mn.N Mn.R) : ℝ) * (Mn.N + Din + 1))
  simpa only [mul_assoc] using add_le_add hm
    (le_refl ((Fintype.card (CompIn G.comps) : ℝ) * Fintype.card (WeakStoredWords Mn.N Mn.R) *
      (Mn.N + 2) * weakStoredEddyWeight D Mn.N J Mn.η0 G.level))

/-- A single integer bounds both coefficients in the full-sum recurrence. -/
def weakStoredPassageBudget (N J R : ℕ) : ℕ :=
  1 + weakStoredWordBudget N R * (N + (1 + J * N) + 1) * (J * R) +
    weakStoredWordBudget N R ^ J * weakStoredWordBudget N R * (N + 2)

theorem weakStoredPassageBudget_one_le (N J R : ℕ) : 1 ≤ weakStoredPassageBudget N J R := by
  unfold weakStoredPassageBudget
  omega

/-- The finite menus give one recurrence constant at every stage. -/
theorem weakStoredTotal_passage_uniform (P : ProvParams) (Mn : WeakMenu) (J Din : ℕ)
    (rW : ℝ) (G G' : GenStage D (fun _ => ℝ) Dm b j₀)
    (hp : IsWeakPassage D P Mn rW Din G G') (ht : G.HasTags P) (ht' : G'.HasTags P)
    (hN : 1 ≤ Mn.N) (hJ : 1 ≤ J) (heps : ∀ i, 0 < D.eps i)
    (hpath : ∀ h, StagePath G h → h ≤ J * Mn.R)
    (hsmall : weakStoredTotal G Mn.N J Mn.η0 ≤ 1)
    (hcomp : G.comps.card ≤ weakStoredWordBudget Mn.N Mn.R ^ J)
    (hDin : Din ≤ 1 + J * Mn.N) :
    weakStoredTotal G' Mn.N J Mn.η0 ≤ (weakStoredPassageBudget Mn.N J Mn.R : ℝ) *
      (weakStoredTotal G Mn.N J Mn.η0 + weakStoredEddyWeight D Mn.N J Mn.η0 G.level) := by
  let W := weakStoredWordBudget Mn.N Mn.R
  have hw : Fintype.card (WeakStoredWords Mn.N Mn.R) ≤ W := le_max_left _ _
  have ha : Fintype.card (WeakStoredWords Mn.N Mn.R) * (Mn.N + Din + 1) * (J * Mn.R) ≤
      weakStoredPassageBudget Mn.N J Mn.R := by
    have hh := Nat.mul_le_mul_right (J * Mn.R) (Nat.mul_le_mul hw
      (Nat.add_le_add_right (Nat.add_le_add_left hDin Mn.N) 1))
    exact hh.trans (by unfold weakStoredPassageBudget; dsimp [W] at hh ⊢; omega)
  have hb : G.comps.card * Fintype.card (WeakStoredWords Mn.N Mn.R) * (Mn.N + 2) ≤
      weakStoredPassageBudget Mn.N J Mn.R := by
    have hh := Nat.mul_le_mul_right (Mn.N + 2) (Nat.mul_le_mul hcomp hw)
    exact hh.trans (by unfold weakStoredPassageBudget; dsimp [W] at hh ⊢; omega)
  have ha' : (Fintype.card (WeakStoredWords Mn.N Mn.R) : ℝ) * (Mn.N + Din + 1) *
      (J * Mn.R : ℕ) ≤ (weakStoredPassageBudget Mn.N J Mn.R : ℝ) := by exact_mod_cast ha
  have hb' : (Fintype.card (CompIn G.comps) : ℝ) * Fintype.card (WeakStoredWords Mn.N Mn.R) *
      (Mn.N + 2) ≤ (weakStoredPassageBudget Mn.N J Mn.R : ℝ) := by
    rw [Fintype.card_coe]
    exact_mod_cast hb
  refine (weakStoredTotal_passage_linear P Mn J Din (J * Mn.R) rW G G' hp ht ht'
    hN hJ heps hpath hsmall).trans ?_
  calc
    _ ≤ (weakStoredPassageBudget Mn.N J Mn.R : ℝ) * weakStoredTotal G Mn.N J Mn.η0 +
        (weakStoredPassageBudget Mn.N J Mn.R : ℝ) * weakStoredEddyWeight D Mn.N J Mn.η0 G.level :=
      add_le_add (mul_le_mul_of_nonneg_right ha' (weakStoredTotal_nonneg G Mn.N J Mn.η0))
        (mul_le_mul_of_nonneg_right hb' (weakStoredEddyWeight_nonneg D Mn.N J Mn.η0 G.level))
    _ = _ := by ring

end AVRegularity.WeakEntryProofs
end
end

section
@[expose] public section
namespace AVRegularity.WeakEntryProofs

/-! Rerooting identifies the weak component masses and readout weights exactly. -/

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

theorem weakEncoding_mass (N J : ℕ) (η : ℝ) (rootM rootR : ℕ → ℝ)
    (G Gw : GenStage D ScalarH Dm b j₀) (ι : CompIn G.comps ≃ CompIn Gw.comps)
    (he : IsWeakEncoding N J η rootM rootR G Gw ι)
    (law : BirthLaw) (hm : law.rootMass = rootM) (v : CompIn G.comps) :
    Gw.mass law (ι v) = weakMass D N J η v.1 := by
  unfold GenStage.mass compMass
  rw [he.2.1 v, List.map_nil, List.prod_nil, mul_one, hm]
  exact (he.2.2.1 v).1

theorem weakEncoding_readoutWeight (N J : ℕ) (η : ℝ) (rootM rootR : ℕ → ℝ)
    (G Gw : GenStage D ScalarH Dm b j₀) (ι : CompIn G.comps ≃ CompIn Gw.comps)
    (he : IsWeakEncoding N J η rootM rootR G Gw ι)
    (law : BirthLaw) (hr : law.rootReadout = rootR) (v : CompIn G.comps) :
    Gw.readoutWeight law (ι v) = weakReadoutWeight D η v.1 := by
  unfold GenStage.readoutWeight compReadout
  rw [he.2.1 v, List.map_nil, List.prod_nil, mul_one, hr]
  exact (he.2.2.1 v).2

end AVRegularity.WeakEntryProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs

/-! Relabeling a scalar generated stage preserves its actual coefficient data and seed exports. -/

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

def relabelWeakStage (G : GenStage D ScalarH Dm b j₀) (S : Finset Comp)
    (e : CompIn G.comps ≃ CompIn S) : GenStage D ScalarH Dm b j₀ where
  level := G.level
  comps := S
  fam :=
    { Γ := fun v u => G.fam.Γ (e.symm v) (e.symm u)
      fintypeΓ := fun v u => G.fam.fintypeΓ (e.symm v) (e.symm u)
      identity := fun v u γ => G.fam.identity (e.symm v) (e.symm u) γ
      piece := G.fam.piece
      flux := fun p c v u γ => G.fam.flux p c (e.symm v) (e.symm u) γ
      flux_periodic := fun p c v u γ => G.fam.flux_periodic p c (e.symm v) (e.symm u) γ
      flux_zero := fun p c v u γ => G.fam.flux_zero p c (e.symm v) (e.symm u) γ
      weight := G.fam.weight
      weight_nonneg := G.fam.weight_nonneg
      weight_zero := G.fam.weight_zero
      locally_finite := G.fam.locally_finite
      weight_sum := G.fam.weight_sum }
  prov := fun v u γ => G.prov (e.symm v) (e.symm u) γ
  actual := G.actual
  exports := G.exports

def relabelWeakEdge (G : GenStage D ScalarH Dm b j₀) (S : Finset Comp)
    (e : CompIn G.comps ≃ CompIn S) (v u : CompIn G.comps) :
    G.fam.Γ v u ≃ (relabelWeakStage G S e).fam.Γ (e v) (e u) :=
  Equiv.cast (by simp only [relabelWeakStage, Equiv.symm_apply_apply])

private theorem dependent_relabel_apply {ι : Type*} {Γ : ι → ι → Type*} {α : Type*}
    (F : ∀ v u, Γ v u → α) {v u v' u' : ι} (hv : v = v') (hu : u = u')
    (hΓ : Γ v u = Γ v' u') (γ : Γ v u) : F v' u' (cast hΓ γ) = F v u γ := by
  subst v'
  subst u'
  rfl

@[simp] theorem relabelWeakStage_prov (G : GenStage D ScalarH Dm b j₀) (S : Finset Comp)
    (e : CompIn G.comps ≃ CompIn S) (v u : CompIn G.comps) (γ : G.fam.Γ v u) :
    (relabelWeakStage G S e).prov (e v) (e u) (relabelWeakEdge G S e v u γ) = G.prov v u γ := by
  change G.prov (e.symm (e v)) (e.symm (e u)) (cast _ γ) = G.prov v u γ
  exact dependent_relabel_apply G.prov (e.symm_apply_apply v).symm
    (e.symm_apply_apply u).symm _ γ

@[simp] theorem relabelWeakStage_identity (G : GenStage D ScalarH Dm b j₀) (S : Finset Comp)
    (e : CompIn G.comps ≃ CompIn S) (v u : CompIn G.comps) (γ : G.fam.Γ v u) :
    (relabelWeakStage G S e).fam.identity (e v) (e u) (relabelWeakEdge G S e v u γ) =
      G.fam.identity v u γ := by
  change G.fam.identity (e.symm (e v)) (e.symm (e u)) (cast _ γ) = G.fam.identity v u γ
  exact dependent_relabel_apply (α := CoefficientIdentity Dm ℝ ℝ)
    (fun v u γ => G.fam.identity v u γ) (e.symm_apply_apply v).symm
    (e.symm_apply_apply u).symm _ γ

@[simp] theorem relabelWeakStage_flux (G : GenStage D ScalarH Dm b j₀) (S : Finset Comp)
    (e : CompIn G.comps ≃ CompIn S) (v u : CompIn G.comps) (γ : G.fam.Γ v u)
    (p : OddSlot) (c : StageCtx D b j₀ G.level p) :
    (relabelWeakStage G S e).fam.flux p c (e v) (e u) (relabelWeakEdge G S e v u γ) =
      G.fam.flux p c v u γ := by
  change G.fam.flux p c (e.symm (e v)) (e.symm (e u)) (cast _ γ) = G.fam.flux p c v u γ
  exact dependent_relabel_apply (G.fam.flux p c) (e.symm_apply_apply v).symm
    (e.symm_apply_apply u).symm _ γ

end AVRegularity.WeakEntryProofs
end
end
