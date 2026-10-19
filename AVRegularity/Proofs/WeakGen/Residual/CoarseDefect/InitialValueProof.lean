-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.WeakGen.Residual.CoarseDefect.FluxIdentInteg
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
import AVRegularity.Construction.InitialValue.Cascade
import AVRegularity.Proofs.WeakGen.Residual.CoarseDefect.FrontierFlux.Jets
public import AVRegularity.Proofs.WeakGen.Reduction.QuietTraceHighPassage
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
import AVRegularity.EntryWeakAssembly.NativeFamilyLiftUniqueness
import AVRegularity.Proofs.Torus.FirstSource

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

/-! **`CdFluxIdentityAll` from the three structural statements**.

`cdFluxIdentityAll_of_classes : CdParentMem plan → CdInhClass plan → CdEddClass plan →
CdFluxIdentityAll plan`. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction

/-- **The flux identity (Oc) for all data**, from the parent, inherited and eddy classifications. -/
theorem cdFluxIdentityAll_of_classes (plan : WeakPassagePlan) (hP : CdParentMem plan)
    (hI : CdInhClass plan) (hE : CdEddClass plan) : CdFluxIdentityAll plan := by
  intro B A R Dc m k hDc hk c r Uhi Whi hpass i hi hit v₀ Fc hFc v
  obtain ⟨-, -, hw, -, -⟩ := cdPassage_rewrite c r m Uhi Whi i hi hit (hpass i hi hit)
  exact cdFluxIdentity_of_coef c r Dc m k _ i hi hit v₀ Uhi Whi Fc v hw hFc
    (cdCoefIdentity_of_classes hP hI hE Dc hDc c m i hi hit v₀ v)
end

/-! **`CdParentMem` is proved**: the parent of an extended component is a
component of the stage `i`. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction

/-- **(P) proved**: the parent of a component of the stage `i - 1` is a component of the stage `i`. -/
theorem cdParentMem (plan : WeakPassagePlan) : CdParentMem plan := by
  intro B A R c i hi hit u'
  obtain ⟨hlev, hbirth, -⟩ := partB_stage_invariant c (c.M + A.Jw - i) (by omega)
  have hidx : c.M + A.Jw - (c.M + A.Jw - i) = i := by omega
  rw [hidx] at hlev hbirth
  obtain ⟨⟨-, -, -, hcomps', -⟩, -⟩ := c.construction.2.2 i hi hit
  have key : ∀ x : Comp, x ∈ (c.stage (i - 1)).comps →
      x ∈ weakExtComps i A.Nw A.Rw (c.stage i).comps := by
    intro x hx
    rw [hcomps', hlev] at hx
    exact hx
  have hu := key u'.1 u'.2
  unfold weakExtComps at hu
  rcases Finset.mem_union.1 hu with hu | hu
  · have h := (Construction.Preservation.FullLift.parent_word_succComp (m := i) (by omega) u'.1
      (hbirth u'.1 hu) []).1
    simp only [succComp, ↓reduceDIte] at h
    rw [h]; exact hu
  · obtain ⟨⟨u, t⟩, hut, he⟩ := Finset.mem_image.1 hu
    have hu0 := (Finset.mem_product.1 hut).1
    have h := (Construction.Preservation.FullLift.parent_word_succComp (m := i) (by omega) u
      (hbirth u hu0) t).1
    have he' : succComp i u t = u'.1 := he
    have hp : compParent i u'.1 = u := by rw [← he']; exact h
    rw [hp]
    exact hu0
end

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end

section
namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

/-! **The coarse defect equation from the two edge classifications**.

`weakCoarseDefect_of_classes`: `WeakCoarseDefectStatement plan` from `WeakPassageCommonOK plan`
and the two statements `CdInhClass plan`, `CdEddClass plan` (the classification of the
inherited and of the eddy edges of the passage). -/

open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction

/-- **The coarse defect equation** from the common plan hypothesis and the two edge classifications. -/
theorem weakCoarseDefect_of_classes (plan : WeakPassagePlan) (hcommon : WeakPassageCommonOK plan)
    (hI : CdInhClass plan) (hE : CdEddClass plan) : WeakCoarseDefectStatement plan :=
  weakCoarseDefect_of_parts plan
    (cdFluxIdentityAll_of_classes plan (cdParentMem plan) hI hE)
    (cdIntegrableAll_of_common plan hcommon)

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

/-! **The edges of the stage `i - 1` that are eddy letters**.

The components of the stage `i - 1` are the words over the components of the stage `i`; an eddy
edge `(a, w) → (a, w n)` is determined by its endpoints, and exists for every valid `(a, w, n)`. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- Level and ages of the stage `i`. -/
theorem cd_stage_inv (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) :
    (c.stage i).level = i ∧ ∀ v ∈ (c.stage i).comps, ∀ e ∈ v.births, i ≤ e.scale := by
  obtain ⟨hlev, hbirth, -⟩ := partB_stage_invariant c (c.M + A.Jw - i) (by omega)
  have hidx : c.M + A.Jw - (c.M + A.Jw - i) = i := by omega
  rw [hidx] at hlev hbirth
  exact ⟨hlev, hbirth⟩

/-- The components of the stage `i - 1` are the extended components. -/
theorem cd_comps_eq (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) :
    (c.stage (i - 1)).comps = weakExtComps i A.Nw A.Rw (c.stage i).comps := by
  obtain ⟨⟨-, -, -, hcomps', -⟩, -⟩ := c.construction.2.2 i hi hit
  rw [hcomps', (cd_stage_inv c i hi hit).1]

/-- Parent and word of a component of the stage `i - 1`. -/
theorem cd_comp_decomp (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (u : Comp) (hu : u ∈ (c.stage (i - 1)).comps) :
    compParent i u ∈ (c.stage i).comps ∧
      (compWord i u = [] ∨ compWord i u ∈ wordsUpTo (weakAlphabet A.Nw) A.Rw) := by
  have hb := (cd_stage_inv c i hi hit).2
  rw [cd_comps_eq c i hi hit] at hu
  unfold weakExtComps at hu
  rcases Finset.mem_union.1 hu with hu | hu
  · have h := InitialValue.compParent_eq_self (m := i) (by omega) (hb u hu)
    exact ⟨by rw [h.1]; exact hu, Or.inl h.2⟩
  · obtain ⟨⟨a, t⟩, hat, he⟩ := Finset.mem_image.1 hu
    obtain ⟨ha, ht⟩ := Finset.mem_product.1 hat
    have he' : succComp i a t = u := he
    have h := Construction.Preservation.FullLift.parent_word_succComp (m := i) (by omega) a
      (hb a ha) t
    rw [he'] at h
    exact ⟨by rw [h.1]; exact ha, Or.inr (by rw [h.2]; exact ht)⟩

/-- Membership of `succComp i a t` among the components of the stage `i - 1`. -/
theorem cd_succComp_mem (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (a : CompIn (c.stage i).comps) (t : List WordLetter)
    (ht : t = [] ∨ t ∈ wordsUpTo (weakAlphabet A.Nw) A.Rw) :
    succComp i a.1 t ∈ (c.stage (i - 1)).comps := by
  rw [cd_comps_eq c i hi hit]
  unfold weakExtComps
  rcases ht with ht | ht
  · subst ht
    have : succComp i a.1 [] = a.1 := by simp [succComp]
    rw [this]
    exact Finset.mem_union_left _ a.2
  · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨⟨a.1, t⟩,
      Finset.mem_product.2 ⟨a.2, ht⟩, rfl⟩)

/-- Appending an eddy letter to a word of length `< R`. -/
theorem cd_append_mem (N R : ℕ) (w : List WordLetter) (n : ℕ)
    (hw : w = [] ∨ w ∈ wordsUpTo (weakAlphabet N) R) (hl : w.length < R) (hn2 : 2 ≤ n)
    (hn : n ≤ N + 1) : w ++ [WordLetter.eddy n] ∈ wordsUpTo (weakAlphabet N) R := by
  have hmem : WordLetter.eddy n ∈ weakAlphabet N :=
    Finset.mem_image.2 ⟨n, Finset.mem_Icc.2 ⟨hn2, hn⟩, rfl⟩
  rcases hw with hw | hw
  · subst hw
    simp only [wordsUpTo, Finset.mem_biUnion, Finset.mem_Icc]
    refine ⟨1, ⟨le_rfl, by simp at hl; omega⟩, ?_⟩
    simp only [wordsOfLength, Finset.mem_image, Finset.mem_product, Finset.mem_singleton]
    exact ⟨(WordLetter.eddy n, []), ⟨hmem, rfl⟩, rfl⟩
  · simp only [wordsUpTo, Finset.mem_biUnion, Finset.mem_Icc] at hw ⊢
    obtain ⟨k, hk, hwk⟩ := hw
    have hlen := CascadeInvariants.length_of_mem_wordsOfLength hwk
    refine ⟨k + 1, ⟨by omega, by omega⟩, ?_⟩
    simp only [wordsOfLength, Finset.mem_image, Finset.mem_product]
    exact ⟨(WordLetter.eddy n, w), ⟨hmem, hwk⟩, rfl⟩

/-- Everything an eddy edge `(a, w) → (a, w n)` of the stage `i - 1` records. -/
theorem cd_eddy_facts (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) {v' u' : CompIn (c.stage (i - 1)).comps}
    (γ : (c.stage (i - 1)).fam.Γ v' u') {a : CompIn (c.stage i).comps} {w : List WordLetter}
    {n : ℕ} (h : (cdEdgeSource c i hi hit v' u' γ).1 = WeakSource.eddy a w n) :
    compParent i u'.1 = a.1 ∧ compWord i u'.1 = w ∧ compParent i v'.1 = a.1 ∧
      compWord i v'.1 = w ++ [WordLetter.eddy n] ∧
      (w = [] ∨ w ∈ wordsUpTo (weakAlphabet A.Nw) A.Rw) ∧ w.length < A.Rw ∧ 2 ≤ n ∧
      n ≤ A.Nw + 1 := by
  obtain ⟨hlev, hb⟩ := cd_stage_inv c i hi hit
  have p := (cdEdgeSource c i hi hit v' u' γ).2
  rw [h] at p
  obtain ⟨hv, hs, ht⟩ := p
  obtain ⟨h1, h2, h3, h4⟩ := hv
  have hs' : succComp i a.1 w = u'.1 := by
    simpa only [WeakSource.srcComp, hlev] using hs
  have ht' : succComp i a.1 (w ++ [WordLetter.eddy n]) = v'.1 := by
    simpa only [WeakSource.tgtComp, hlev] using ht
  have e1 := Construction.Preservation.FullLift.parent_word_succComp (m := i) (by omega) a.1
    (hb a.1 a.2) w
  have e2 := Construction.Preservation.FullLift.parent_word_succComp (m := i) (by omega) a.1
    (hb a.1 a.2) (w ++ [WordLetter.eddy n])
  rw [hs'] at e1
  rw [ht'] at e2
  exact ⟨e1.1, e1.2, e2.1, e2.2, h1, h2, h3, h4⟩

/-- An eddy edge is determined by its endpoints. -/
theorem cd_eddy_edge_unique (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) {v' u' : CompIn (c.stage (i - 1)).comps}
    (γ₁ γ₂ : (c.stage (i - 1)).fam.Γ v' u') {a₁ a₂ : CompIn (c.stage i).comps}
    {w₁ w₂ : List WordLetter} {n₁ n₂ : ℕ}
    (h₁ : (cdEdgeSource c i hi hit v' u' γ₁).1 = WeakSource.eddy a₁ w₁ n₁)
    (h₂ : (cdEdgeSource c i hi hit v' u' γ₂).1 = WeakSource.eddy a₂ w₂ n₂) : γ₁ = γ₂ := by
  obtain ⟨p₁, q₁, r₁, s₁, -⟩ := cd_eddy_facts c i hi hit γ₁ h₁
  obtain ⟨p₂, q₂, r₂, s₂, -⟩ := cd_eddy_facts c i hi hit γ₂ h₂
  have ha : a₁ = a₂ := Subtype.ext (p₁.symm.trans p₂)
  have hw : w₁ = w₂ := q₁.symm.trans q₂
  subst ha hw
  have hn : WordLetter.eddy n₁ = WordLetter.eddy n₂ := by
    have := s₁.symm.trans s₂
    simpa using this
  have hn' : n₁ = n₂ := by injection hn
  subst hn'
  apply (cdEdgeSource c i hi hit v' u').injective
  exact Subtype.ext (h₁.trans h₂.symm)

/-- Every valid eddy letter `(a, w, n)` with the right endpoints is an edge of the stage `i - 1`. -/
theorem cd_eddy_edge_exists (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (v' u' : CompIn (c.stage (i - 1)).comps)
    (a : CompIn (c.stage i).comps) (w : List WordLetter) (n : ℕ)
    (hw : w = [] ∨ w ∈ wordsUpTo (weakAlphabet A.Nw) A.Rw) (hl : w.length < A.Rw)
    (hn2 : 2 ≤ n) (hn : n ≤ A.Nw + 1) (hu : succComp i a.1 w = u'.1)
    (hv : succComp i a.1 (w ++ [WordLetter.eddy n]) = v'.1) :
    ∃ γ : (c.stage (i - 1)).fam.Γ v' u',
      (cdEdgeSource c i hi hit v' u' γ).1 = WeakSource.eddy a w n := by
  have hlev := (cd_stage_inv c i hi hit).1
  refine ⟨(cdEdgeSource c i hi hit v' u').symm
    ⟨WeakSource.eddy a w n, ⟨hw, hl, hn2, hn⟩, ?_, ?_⟩, ?_⟩
  · simpa only [WeakSource.srcComp, hlev] using hu
  · simpa only [WeakSource.tgtComp, hlev] using hv
  · exact congrArg Subtype.val ((cdEdgeSource c i hi hit v' u').apply_symm_apply _)

theorem cd_stagePath_mem (c : WeakPassageInstance plan R) (i : ℕ) {h : ℕ}
    (π : StagePath (c.stage i) h) (hh : 1 ≤ h) :
    π.src ∈ (c.stage i).comps ∧ π.tgt ∈ (c.stage i).comps := by
  unfold StagePath.src StagePath.tgt
  have h0 : 0 < h := hh
  simp only [h0, ↓reduceDIte]
  exact ⟨(π.step _).2.1.2, (π.step _).1.2⟩

/-- Everything an inherited edge `(π.src, w) → (π.tgt, w)` of the stage `i - 1` records. -/
theorem cd_inh_facts (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) {v' u' : CompIn (c.stage (i - 1)).comps}
    (γ : (c.stage (i - 1)).fam.Γ v' u') {w : List WordLetter} {h : ℕ}
    {π : StagePath (c.stage i) h} {n : ℕ}
    (hs : (cdEdgeSource c i hi hit v' u' γ).1 = WeakSource.inherited w h π n) :
    compParent i u'.1 = π.src ∧ compWord i u'.1 = w ∧ compParent i v'.1 = π.tgt ∧
      compWord i v'.1 = w ∧ π.src ∈ (c.stage i).comps ∧ π.tgt ∈ (c.stage i).comps ∧
      (w = [] ∨ w ∈ wordsUpTo (weakAlphabet A.Nw) A.Rw) ∧ 1 ≤ h ∧ 2 ≤ n ∧
      n ≤ A.Nw + (1 + (c.M + A.Jw - i) * A.Nw) := by
  obtain ⟨hlev, hb⟩ := cd_stage_inv c i hi hit
  have p := (cdEdgeSource c i hi hit v' u' γ).2
  rw [hs] at p
  obtain ⟨hv, hsr, ht⟩ := p
  obtain ⟨h1, h2, h3, h4⟩ := hv
  obtain ⟨m1, m2⟩ := cd_stagePath_mem c i π h2
  have hs' : succComp i π.src w = u'.1 := by
    simpa only [WeakSource.srcComp, hlev] using hsr
  have ht' : succComp i π.tgt w = v'.1 := by
    simpa only [WeakSource.tgtComp, hlev] using ht
  have e1 := Construction.Preservation.FullLift.parent_word_succComp (m := i) (by omega) π.src
    (hb _ m1) w
  have e2 := Construction.Preservation.FullLift.parent_word_succComp (m := i) (by omega) π.tgt
    (hb _ m2) w
  rw [hs'] at e1
  rw [ht'] at e2
  exact ⟨e1.1, e1.2, e2.1, e2.2, m1, m2, h1, h2, h3, h4⟩

/-- An inherited edge keeps the word. -/
theorem cd_isInh_word (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) {v' u' : CompIn (c.stage (i - 1)).comps}
    (γ : (c.stage (i - 1)).fam.Γ v' u') (h : cdIsInh (cdEdgeSource c i hi hit v' u' γ).1) :
    compWord i v'.1 = compWord i u'.1 := by
  generalize hs : (cdEdgeSource c i hi hit v' u' γ).1 = s at h
  cases s with
  | inherited w h' π n =>
    obtain ⟨-, q1, -, q2, -⟩ := cd_inh_facts c i hi hit γ hs
    rw [q1, q2]
  | eddy a w n => exact h.elim

/-- The sum over the edges of the non-inherited ones is the single eddy edge. -/
theorem cd_eddy_sum_single (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) {v' u' : CompIn (c.stage (i - 1)).comps}
    (γ₀ : (c.stage (i - 1)).fam.Γ v' u') {a : CompIn (c.stage i).comps} {w : List WordLetter}
    {n : ℕ} (h₀ : (cdEdgeSource c i hi hit v' u' γ₀).1 = WeakSource.eddy a w n)
    {X : Type*} [AddCommMonoid X] (F : (c.stage (i - 1)).fam.Γ v' u' → X) :
    (∑ γ : (c.stage (i - 1)).fam.Γ v' u',
      open scoped Classical in
      if cdIsInh (cdEdgeSource c i hi hit v' u' γ).1 then 0 else F γ) = F γ₀ := by
  classical
  rw [Finset.sum_eq_single_of_mem γ₀ (Finset.mem_univ _)]
  · have : ¬ cdIsInh (cdEdgeSource c i hi hit v' u' γ₀).1 := by rw [h₀]; exact id
    simp [this]
  · intro γ _ hne
    by_cases hinh : cdIsInh (cdEdgeSource c i hi hit v' u' γ).1
    · simp [hinh]
    · exfalso
      apply hne
      generalize hs : (cdEdgeSource c i hi hit v' u' γ).1 = s at hinh
      cases s with
      | inherited w' h' π' n' => exact (hinh trivial).elim
      | eddy a' w' n' => exact cd_eddy_edge_unique c i hi hit γ γ₀ hs h₀
end

/-! **`CdEddClass` is proved**.

The eddy part `cdEddy (v', u')` vanishes unless `v' = (parent u', w n)`
for a letter `n ∈ [2, N_w + 1]` and `|w| < R_w`, in which case it is the coefficient of the single
eddy edge `(a, w) → (a, w n)`; this coefficient depends on `n` only (`cd_eddy_coeff_indep`), and
`cdWeight (a, w n) = cdWeight (a, w) ε^{η₀}`. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

theorem cd_smul_zero_clm (r : ℝ) (d : ℕ) :
    r • (0 : PiLp 2 (fun _ : DerivativeWord2 (d - 1) => ℝ) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => ℝ)) = 0 := by
  ext y : 1
  simp

theorem cd_zero_smul_clm (d : ℕ) (T : PiLp 2 (fun _ : DerivativeWord2 (d - 1) => ℝ) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => ℝ)) : (0 : ℝ) • T = 0 := by
  ext y : 1
  simp

/-- If the words of the endpoints differ, every edge is the single eddy edge. -/
theorem cd_eddy_sum_all (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) {v' u' : CompIn (c.stage (i - 1)).comps}
    (hne : compWord i v'.1 ≠ compWord i u'.1)
    (γ₀ : (c.stage (i - 1)).fam.Γ v' u') {a : CompIn (c.stage i).comps} {w : List WordLetter}
    {n : ℕ} (h₀ : (cdEdgeSource c i hi hit v' u' γ₀).1 = WeakSource.eddy a w n)
    {X : Type*} [AddCommMonoid X] (F : (c.stage (i - 1)).fam.Γ v' u' → X) :
    (∑ γ : (c.stage (i - 1)).fam.Γ v' u', F γ) = F γ₀ := by
  rw [Finset.sum_eq_single_of_mem γ₀ (Finset.mem_univ _)]
  intro γ _ hγ
  exfalso
  apply hγ
  generalize hs : (cdEdgeSource c i hi hit v' u' γ).1 = s' at *
  cases s' with
  | inherited w' h' π' n' =>
    exact (hne (cd_isInh_word c i hi hit γ (by rw [hs]; trivial))).elim
  | eddy a' w' n' => exact cd_eddy_edge_unique c i hi hit γ γ₀ hs h₀

/-- The eddy part vanishes unless `v'` is a letter child of `u'`. -/
theorem cd_eddy_eq_zero (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (v' u' : CompIn (c.stage (i - 1)).comps) (d : ℕ) (s : ℝ)
    (x : Vec 2)
    (h : ∀ n, ¬ (2 ≤ n ∧ n ≤ A.Nw + 1 ∧ (compWord i u'.1).length < A.Rw ∧
      v'.1 = succComp i (compParent i u'.1) (compWord i u'.1 ++ [WordLetter.eddy n]))) :
    cdEddy c i hi hit v' u' d s x = 0 := by
  unfold cdEddy
  apply Finset.sum_eq_zero
  intro γ _
  generalize hs : (cdEdgeSource c i hi hit v' u' γ).1 = s'
  cases s' with
  | inherited w h' π n => simp [cdIsInh]
  | eddy a w n =>
    exfalso
    obtain ⟨p1, q1, p2, q2, -, hl, h2, hn⟩ := cd_eddy_facts c i hi hit γ hs
    apply h n
    have sw := Construction.Preservation.FullLift.succComp_parent_word i v'.1
    rw [p2, q2] at sw
    refine ⟨h2, hn, by rw [q1]; exact hl, ?_⟩
    rw [p1, q1]
    exact sw.symm

/-- **`CdEddClass` is proved.** -/
theorem cdEddClass (plan : WeakPassagePlan) : CdEddClass plan := by
  intro B A R Dc c i hi hit v₀ v u' d s x
  classical
  obtain ⟨hlev, hb⟩ := cd_stage_inv c i hi hit
  obtain ⟨hpar, hwd⟩ := cd_comp_decomp c i hi hit u'.1 u'.2
  have hi1 : 1 ≤ i := by omega
  have hwlen : (compWord i u'.1).length ≤ A.Rw := by
    rcases hwd with h | h
    · rw [h]; exact Nat.zero_le _
    · exact (CascadeInvariants.length_of_mem_wordsUpTo h).2
  by_cases hcond : compParent i u'.1 = v.1 ∧ (compWord i u'.1).length ≠ A.Rw
  swap
  · split_ifs
    apply Finset.sum_eq_zero
    intro v' _
    by_cases hp : compParent i v'.1 = v.1
    · have h0 : cdEddy c i hi hit v' u' d.1 s x = 0 := by
        apply cd_eddy_eq_zero
        rintro n ⟨h2, hn, hl, hv⟩
        have e := Construction.Preservation.FullLift.parent_word_succComp (m := i) hi1
          (compParent i u'.1) (hb _ hpar) (compWord i u'.1 ++ [WordLetter.eddy n])
        rw [← hv] at e
        exact hcond ⟨e.1.symm.trans hp, hl.ne⟩
      rw [h0]
      exact cd_smul_zero_clm _ _
    · have : cdLam c i v v' = 0 := by simp [cdLam, hp]
      rw [this]
      exact cd_zero_smul_clm _ _
  obtain ⟨hpv, hwne⟩ := hcond
  simp only [hpv, hwne, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
  have hwl : (compWord i u'.1).length < A.Rw := lt_of_le_of_ne hwlen hwne
  have hRw : 0 < A.Rw := lt_of_le_of_lt (Nat.zero_le _) hwl
  have hu1 := Construction.Preservation.FullLift.succComp_parent_word i u'.1
  set w := compWord i u'.1 with hw
  set p := compParent i u'.1 with hp
  let a : CompIn (c.stage i).comps := ⟨p, hpar⟩
  have hmem : ∀ n ∈ Finset.Icc 2 (A.Nw + 1),
      succComp i p (w ++ [WordLetter.eddy n]) ∈ (c.stage (i - 1)).comps := by
    intro n hn
    obtain ⟨h2, h3⟩ := Finset.mem_Icc.1 hn
    exact cd_succComp_mem c i hi hit a _ (Or.inr (cd_append_mem A.Nw A.Rw w n hwd hwl h2 h3))
  let φ : ℕ → CompIn (c.stage (i - 1)).comps := fun n =>
    if h : succComp i p (w ++ [WordLetter.eddy n]) ∈ (c.stage (i - 1)).comps then ⟨_, h⟩ else u'
  have hφ : ∀ n ∈ Finset.Icc 2 (A.Nw + 1), (φ n).1 = succComp i p (w ++ [WordLetter.eddy n]) := by
    intro n hn
    simp only [φ, hmem n hn, ↓reduceDIte]
  have hinj : Set.InjOn φ ↑(Finset.Icc 2 (A.Nw + 1)) := by
    intro n hn m hm h
    have h' := congrArg Subtype.val h
    rw [hφ n hn, hφ m hm] at h'
    obtain ⟨-, h2⟩ := Uniqueness.succComp_inj (m := i) hi1 (hb p hpar) (hb p hpar) h'
    have h3 := List.append_cancel_left h2
    simpa using h3
  have hsum1 : ∑ v' : CompIn (c.stage (i - 1)).comps,
      cdLam c i v v' • cdEddy c i hi hit v' u' d.1 s x =
      ∑ n ∈ Finset.Icc 2 (A.Nw + 1),
        cdLam c i v (φ n) • cdEddy c i hi hit (φ n) u' d.1 s x := by
    rw [← Finset.sum_image (f := fun v' => cdLam c i v v' • cdEddy c i hi hit v' u' d.1 s x) hinj]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro v' _ hv'
    have h0 : cdEddy c i hi hit v' u' d.1 s x = 0 := by
      apply cd_eddy_eq_zero
      rintro n ⟨h2, hn, hl, hv⟩
      apply hv'
      refine Finset.mem_image.2 ⟨n, Finset.mem_Icc.2 ⟨h2, hn⟩, Subtype.ext ?_⟩
      rw [hφ n (Finset.mem_Icc.2 ⟨h2, hn⟩)]
      exact hv.symm
    rw [h0]
    exact cd_smul_zero_clm _ _
  rw [hsum1]
  unfold cdAD
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  intro n hn
  obtain ⟨h2, h3⟩ := Finset.mem_Icc.1 hn
  have hpn := Construction.Preservation.FullLift.parent_word_succComp (m := i) hi1 p
    (hb _ hpar) (w ++ [WordLetter.eddy n])
  -- the edge of the sum on the left
  obtain ⟨γn, hγn⟩ := cd_eddy_edge_exists c i hi hit (φ n) u' a w n hwd hwl h2 h3
    hu1 (hφ n hn).symm
  have hL : cdEddy c i hi hit (φ n) u' d.1 s x =
      (c.stage (i - 1)).physCoeff (φ n) u' γn d.1 s x := by
    unfold cdEddy
    exact cd_eddy_sum_single c i hi hit γn hγn
      (fun γ => (c.stage (i - 1)).physCoeff (φ n) u' γ d.1 s x)
  have hlam : cdLam c i v (φ n) = cdWeight c i u'.1 * (c.D.eps (i - 1) ^ A.η₀) := by
    unfold cdLam cdWeight
    have hq : compParent i (φ n).1 = v.1 := by rw [hφ n hn, hpn.1]; exact hpv
    simp only [hq, ↓reduceIte]
    rw [hφ n hn, hpn.2, List.length_append, List.length_singleton, pow_succ]
  -- the edge on the right
  have hv0 : v₀.1 ∈ (c.stage (i - 1)).comps ∧
      succComp i v₀.1 [WordLetter.eddy n] ∈ (c.stage (i - 1)).comps := by
    refine ⟨?_, cd_succComp_mem c i hi hit v₀ [WordLetter.eddy n]
      (Or.inr (cd_append_mem A.Nw A.Rw [] n (Or.inl rfl) hRw h2 h3))⟩
    have := cd_succComp_mem c i hi hit v₀ [] (Or.inl rfl)
    simpa [succComp] using this
  obtain ⟨γa, hγa⟩ := cd_eddy_edge_exists c i hi hit ⟨succComp i v₀.1 [WordLetter.eddy n], hv0.2⟩
    ⟨v₀.1, hv0.1⟩ v₀ [] n (Or.inl rfl) hRw h2 h3 (by simp [succComp]) rfl
  have hwa := InitialValue.compParent_eq_self (m := i) hi1 (hb _ v₀.2)
  have hne : compWord i (succComp i v₀.1 [WordLetter.eddy n]) ≠ compWord i v₀.1 := by
    have hwn := (Construction.Preservation.FullLift.parent_word_succComp (m := i) hi1 v₀.1
      (hb _ v₀.2) [WordLetter.eddy n]).2
    rw [hwn, hwa.2]
    simp
  have hcoef := cd_eddy_coeff_indep c i hi hit γn γa a v₀ w [] n hγn hγa d.1
  simp only [hv0, and_self, ↓reduceDIte]
  rw [cd_eddy_sum_all c i hi hit hne γa hγa, hL, hlam, hcoef, smul_smul]
end

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end
end
end

section
section
section
/-! **The coefficient of an inherited edge does not depend on the word**.

Two inherited edges `(π.src, w₁) → (π.tgt, w₁)` and
`(π.src, w₂) → (π.tgt, w₂)` of the same grade `h`, path `π` and degree `n` have the same physical
coefficient. The flux reads the lift coefficients `Cc s` of the source; for the two sources the
coefficients are two lift families of the same path data, equal on the lift window by
`native_family_lift_coefficients_unique`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Lift AVRegularity.Providers.Torus AVRegularity.Providers.GenSem

namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction

/-- The slow flux of two inherited sources of the same path data agrees at every time of nonzero
cutoff, for two lift families of the same path data. -/
theorem cd_inh_fluxCoeff_indep {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
    {G : GenStage D ScalarH Dm bw j₀} (hζ : IsFastProfile D.ζ) (Mn : WeakMenu) (ρ : ℝ)
    (w₁ w₂ : List WordLetter) (h : ℕ) (π : StagePath G h) (n : ℕ)
    (Cc₁ Cc₂ : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ))
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (hLF₁ : (WeakSource.inherited w₁ h π n).IsLiftFamily Mn.sX Mn.sZ Mn.N ρ Cc₁)
    (hLF₂ : (WeakSource.inherited w₂ h π n).IsLiftFamily Mn.sX Mn.sZ Mn.N ρ Cc₂)
    (hτ : 0 < ocTau D.α D.q D.Λ G.level) (hcs : 0 ≤ D.cellScaleSq G.level)
    (k : ℤ) (t : ℝ) (hc : ocCutoff D.α D.q D.Λ G.level k t ≠ 0) (A : RealChain)
    (d : ℕ) (I : DerivativeWord2 (d - 1)) :
    fluxCoeff ((WeakSource.inherited w₁ h π n).fluxOp ρ Cc₁ Cc0 k t A) d I 0 =
      fluxCoeff ((WeakSource.inherited w₂ h π n).fluxOp ρ Cc₂ Cc0 k t A) d I 0 := by
  classical
  by_cases hA : IsAdmissibleChain D bw j₀ G.level k A ∧ Odd k
  · have htime := mem_liftWindow_of_cutoff D hτ hcs hc
    have hab := liftWindow_le D hτ hcs k
    have hCa := hLF₁ k A hA
    have hCb := hLF₂ k A hA
    have hu := native_family_lift_coefficients_unique D hζ G.level k hA.2 A ρ _ _
      (isOpen_ladderOmega _ _ _ _ _ _) _ _ hab Mn.N h Mn.sX Mn.sZ Mn.sX Mn.sZ
      (Cc₁ k A) (Cc₂ k A) hCa hCb
    have hP : ∀ hh ≤ h, ∀ n' l α, ∀ X ∈ ladderOmega D bw j₀ G.level k A ρ,
        Cc₁ k A hh n' l α ((D.cellScaleSq G.level)⁻¹ * t) X =
        Cc₂ k A hh n' l α ((D.cellScaleSq G.level)⁻¹ * t) X := by
      intro hh hhh n' l α X hX
      funext z v u
      exact hu hh hhh n' l α _ htime X hX z v u
    simp only [WeakSource.fluxOp, dite_eq_left hA]
    unfold fluxCoeff
    apply congrArg (fun V : Vec 2 => ((d - 1).factorial : ℝ)⁻¹ • V)
    exact Uniqueness.pathMeanFlux_eq_of_agreeOn D G.level ρ _ _ _ n t
      (isOpen_ladderOmega _ _ _ _ _ _) hP _ 0
      (by rw [smul_zero]; exact zero_mem_ladderOmega hζ hA.1 ρ)
  · simp only [WeakSource.fluxOp, dite_eq_right hA]

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- **(a) The coefficient of an inherited edge does not depend on the word.** -/
theorem cd_inh_coeff_indep (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (hζ : IsFastProfile c.D.ζ) (hτ : 0 < ocTau c.D.α c.D.q c.D.Λ i)
    (hcs : 0 ≤ c.D.cellScaleSq i) {v₁ u₁ v₂ u₂ : CompIn (c.stage (i - 1)).comps}
    (γ₁ : (c.stage (i - 1)).fam.Γ v₁ u₁) (γ₂ : (c.stage (i - 1)).fam.Γ v₂ u₂)
    (w₁ w₂ : List WordLetter) (h : ℕ) (π : StagePath (c.stage i) h) (n : ℕ)
    (h₁ : (cdEdgeSource c i hi hit v₁ u₁ γ₁).1 = WeakSource.inherited w₁ h π n)
    (h₂ : (cdEdgeSource c i hi hit v₂ u₂ γ₂).1 = WeakSource.inherited w₂ h π n) (d : ℕ) :
    (c.stage (i - 1)).physCoeff v₁ u₁ γ₁ d = (c.stage (i - 1)).physCoeff v₂ u₂ γ₂ d := by
  have hlev := (cd_stage_inv c i hi hit).1
  have hex := (c.construction.2.2 i hi hit).1.2.2.2.2.2
  obtain ⟨idx, Cc, Cc0, hLF, -, -, hall⟩ := Classical.choose_spec hex
  have hm₁ := cd_maxOrder_eq_degree c i hi hit v₁ u₁ γ₁
  have hm₂ := cd_maxOrder_eq_degree c i hi hit v₂ u₂ γ₂
  rw [h₁] at hm₁
  rw [h₂] at hm₂
  have h₁' : (Classical.choose hex v₁ u₁ γ₁).1 = WeakSource.inherited w₁ h π n := h₁
  have h₂' : (Classical.choose hex v₂ u₂ γ₂).1 = WeakSource.inherited w₂ h π n := h₂
  refine cd_physCoeff_congr (c.stage (i - 1)) γ₁ γ₂ (hm₁.trans hm₂.symm) ?_ ?_ d
  · rw [cd_edge_map c i hi hit, cd_edge_map c i hi hit]
    obtain ⟨p₁, -, p₂, -, -⟩ := cd_inh_facts c i hi hit γ₁ h₁
    obtain ⟨p₃, -, p₄, -, -⟩ := cd_inh_facts c i hi hit γ₂ h₂
    have ru₁ : u₁.1.root = π.src.root := by rw [← p₁, compParent_root]
    have rv₁ : v₁.1.root = π.tgt.root := by rw [← p₂, compParent_root]
    have ru₂ : u₂.1.root = π.src.root := by rw [← p₃, compParent_root]
    have rv₂ : v₂.1.root = π.tgt.root := by rw [← p₄, compParent_root]
    rw [ru₁, rv₁, ru₂, rv₂]
  · intro p ctx d' I
    by_cases hd : 2 ≤ d'
    · funext t X z
      have e₁ := (hall v₁ u₁ γ₁).2.2 p ctx d' I t X z hd
      have e₂ := (hall v₂ u₂ γ₂).2.2 p ctx d' I t X z hd
      rw [h₁'] at e₁
      rw [h₂'] at e₂
      rw [e₁, e₂]
      split_ifs
      · refine Uniqueness.transferAt_congr_coeff _ _ _ _ _ _ _ _ _ _ _ _ ?_
        intro k hk A' d'' I'
        exact cd_inh_fluxCoeff_indep hζ _ _ w₁ w₂ h π n _ _ Cc0 (hLF _) (hLF _)
          (by rw [hlev]; exact hτ) (by rw [hlev]; exact hcs) k t hk A' d'' I'
      · rfl
    · have z₁ := (c.stage (i - 1)).fam.flux_zero p ctx v₁ u₁ γ₁ d' I (fun hh => hd hh.1)
      have z₂ := (c.stage (i - 1)).fam.flux_zero p ctx v₂ u₂ γ₂ d' I (fun hh => hd hh.1)
      rw [z₁, z₂]

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end
end

section
/-! **The classical representative of the readout of the weak window** (the field `hrep` of the window).

`cdW_isClassicalRep`: on the window `[t_i, a + T₀]` of a passage, the readout `W = cdW` of the
high family, at an order `K' ≤ K_w + m`, has the classical readout `𝓡_i` of the representative
`h.aU` (`weakReadoutStep`) as a classical representative to every order `ρ ≤ K'`, `ρ ≤ k(R) + 1`.
It is `frontierJetsStep` with all the children of the parent in place of the frontier:
the high family has the representative `h.aU` to the order `k(R) + 1` (`weakCoarseFamilyRep`),
truncation keeps it (`classicalRep_truncate`), and jets and ordered derivatives are linear
(`torusJetOrder_wsum_ae`, `odFoldl_sum`).

The degenerate cases are included: a parent without child has the zero readout and the zero
representative; `ρ = 0` is the value alone. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance

namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction
  AVRegularity.Providers.WeakGen.Residual

/-- **The readout `W = cdW` has the classical readout of `h.aU` as a representative.** -/
theorem cdW_isClassicalRep (plan : WeakPassagePlan)
    (kOf : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B},
      WeakPassageRequest A → ℕ)
    {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (m K' ρ : ℕ) (hm : m ≤ weakEntryMmax R) (hkOf3 : kOf R + 3 ≤ R.Kw + m)
    (hK : K' ≤ R.Kw + m) (hρK : ρ ≤ K') (hρk : ρ ≤ kOf R + 1)
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c)
    (Uhi : ∀ j, WeakStageFamily (weakPassageRawSetting c) m j)
    (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw) (h : WeakComparisonInput r i)
    (htrunc : ∀ v : CompIn (c.stage (i - 1)).comps, ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀),
      truncateTorusHk (weakReductionReserve_kw_le R m v.1) (Uhi (i - 1) v t) =
        r.Ur (i - 1) v t)
    (v : CompIn (c.stage i).comps) (t : ℝ) (ht : t ∈ Set.Icc (r.tq i) (r.a + A.T₀)) :
    IsClassicalRep
      (cdW c m K' (fun w => hK.trans (weakReductionReserve_kw R m w)) i Uhi v t)
      (weakReadoutStep i A.η₀ (c.stage i) (c.stage (i - 1)) (h.aU t) v) ρ := by
  classical
  have hrep := weakCoarseFamilyRep plan kOf R m hm hkOf3 c r Uhi i hi hit h htrunc
  let cw : CompIn (c.stage (i - 1)).comps → ℝ := fun v' =>
    if compParent i v'.1 = v.1 then (c.D.eps (i - 1) ^ A.η₀) ^ (compWord i v'.1).length else 0
  have hW : cdW c m K' (fun w => hK.trans (weakReductionReserve_kw R m w)) i Uhi v t =
      ∑ v' : CompIn (c.stage (i - 1)).comps, cw v' •
        truncateTorusHk ((fun w => hK.trans (weakReductionReserve_kw R m w)) v'.1)
          (Uhi (i - 1) v' t) := by
    unfold cdW cdReadout
    refine Finset.sum_congr rfl fun v' _ => ?_
    by_cases h1 : compParent i v'.1 = v.1
    · simp only [cw, h1, and_self, ite_true, cdWeight]
    · simp only [cw, h1, false_and, ite_false, zero_smul]
  have hf : weakReadoutStep i A.η₀ (c.stage i) (c.stage (i - 1)) (h.aU t) v =
      fun x => ∑ v' : CompIn (c.stage (i - 1)).comps, cw v' * h.aU t v' x := by
    funext x
    unfold weakReadoutStep
    refine Finset.sum_congr rfl fun v' _ => ?_
    by_cases h1 : compParent i v'.1 = v.1
    · simp only [cw, h1, ite_true]
    · simp only [cw, h1, ite_false, zero_mul]
  have hdiff : ∀ v' : CompIn (c.stage (i - 1)).comps, ContDiff ℝ (ρ : ℕ) (h.aU t v') :=
    fun v' => (hrep v' t ht).2.1.of_le (by exact_mod_cast hρk)
  refine ⟨hρK, ?_, ?_, fun j hj w => ?_⟩
  · rw [hf]
    exact ContDiff.sum fun v' _ => contDiff_const.mul (hdiff v')
  · rw [hf]
    intro z x
    simp only [(hrep _ t ht).2.2.1 z x]
  · rw [hW]
    have step1 := torusJetOrder_wsum_ae Finset.univ cw
      (fun v' => truncateTorusHk ((fun w => hK.trans (weakReductionReserve_kw R m w)) v'.1)
        (Uhi (i - 1) v' t)) (hj.trans hρK) w
    have step2 : ∀ v' : CompIn (c.stage (i - 1)).comps,
        torusJetOrder (truncateTorusHk
          ((fun w => hK.trans (weakReductionReserve_kw R m w)) v'.1)
          (Uhi (i - 1) v' t)) j w =ᵐ[volume.restrict unitCube]
          orderedDerivative w (h.aU t v') := by
      intro v'
      have hr := hrep v' t ht
      have hKv : K' ≤ weakReductionReserve R m v'.1 :=
        hK.trans (weakReductionReserve_kw R m v'.1)
      have hr' : IsClassicalRep (Uhi (i - 1) v' t) (h.aU t v') ρ :=
        ⟨hρK.trans hKv, hr.2.1.of_le (by exact_mod_cast hρk), hr.2.2.1,
          fun m' hm' w' => hr.2.2.2 m' (hm'.trans hρk) w'⟩
      exact (AVRegularity.Construction.Preservation.FullLift.classicalRep_truncate _ hρK _ _
        hr').2.2.2 j hj w
    have hae := ae_all_iff.2 step2
    have step3 : orderedDerivative w
        (weakReadoutStep i A.η₀ (c.stage i) (c.stage (i - 1)) (h.aU t) v) =
        fun x => ∑ v' : CompIn (c.stage (i - 1)).comps,
          cw v' * orderedDerivative w (h.aU t v') x := by
      rw [hf]
      exact odFoldl_sum Finset.univ cw (List.ofFn w) ρ (fun v' => h.aU t v')
        (by simpa using hj) hdiff
    filter_upwards [step1, hae] with x h1 h2
    rw [h1, step3]
    exact Finset.sum_congr rfl fun v' _ => by rw [h2 v']

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end
end

section
/-! **The inherited sources between words**.

The sources `(w, h, π, n)` of the edges `(q, w) → (v, w)` of the
stage `i - 1` are in bijection with the sources `([], h, π, n)` of the edges `q → v`, by
replacing the word. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance

namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- Replace the word of a source. -/
def cdWordSub {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {G : GenStage D ScalarH Dm b j₀}
    (w' : List WordLetter) : WeakSource G → WeakSource G
  | .inherited _ h π n => .inherited w' h π n
  | .eddy a _ n => .eddy a w' n

/-- The valid sources from `(q, w)` to `(v, w)`. -/
abbrev CdSrcSet (c : WeakPassageInstance plan R) (i : ℕ) (q v : CompIn (c.stage i).comps)
    (w : List WordLetter) : Type _ :=
  {s : WeakSource (c.stage i) //
    s.Valid A.Nw A.Rw (1 + (c.M + A.Jw - i) * A.Nw) ∧
      s.srcComp (c.stage i).level = succComp i q.1 w ∧
      s.tgtComp (c.stage i).level = succComp i v.1 w}

/-- A source from `(q, w)` to `(v, w)` is an inherited mean from `q` to `v` in the word `w`. -/
theorem cd_inh_shape (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (q v : CompIn (c.stage i).comps) (w : List WordLetter)
    (s : WeakSource (c.stage i))
    (hs : s.Valid A.Nw A.Rw (1 + (c.M + A.Jw - i) * A.Nw) ∧
      s.srcComp (c.stage i).level = succComp i q.1 w ∧
      s.tgtComp (c.stage i).level = succComp i v.1 w) :
    ∃ (h : ℕ) (π : StagePath (c.stage i) h) (n : ℕ), s = WeakSource.inherited w h π n ∧
      π.src = q.1 ∧ π.tgt = v.1 ∧ (w = [] ∨ w ∈ wordsUpTo (weakAlphabet A.Nw) A.Rw) ∧
      1 ≤ h ∧ 2 ≤ n ∧ n ≤ A.Nw + (1 + (c.M + A.Jw - i) * A.Nw) := by
  obtain ⟨hlev, hb⟩ := cd_stage_inv c i hi hit
  have hi1 : 1 ≤ i := by omega
  obtain ⟨hv, hsr, ht⟩ := hs
  cases s with
  | inherited w' h π n =>
    obtain ⟨h1, h2, h3, h4⟩ := hv
    obtain ⟨m1, m2⟩ := cd_stagePath_mem c i π h2
    have hsr' : succComp i π.src w' = succComp i q.1 w := by
      simpa only [WeakSource.srcComp, hlev] using hsr
    have ht' : succComp i π.tgt w' = succComp i v.1 w := by
      simpa only [WeakSource.tgtComp, hlev] using ht
    obtain ⟨e1, e2⟩ := Uniqueness.succComp_inj hi1 (hb _ m1) (hb _ q.2) hsr'
    obtain ⟨e3, -⟩ := Uniqueness.succComp_inj hi1 (hb _ m2) (hb _ v.2) ht'
    subst e2
    exact ⟨h, π, n, rfl, e1, e3, h1, h2, h3, h4⟩
  | eddy a w' n =>
    exfalso
    have hsr' : succComp i a.1 w' = succComp i q.1 w := by
      simpa only [WeakSource.srcComp, hlev] using hsr
    have ht' : succComp i a.1 (w' ++ [WordLetter.eddy n]) = succComp i v.1 w := by
      simpa only [WeakSource.tgtComp, hlev] using ht
    obtain ⟨-, e2⟩ := Uniqueness.succComp_inj hi1 (hb _ a.2) (hb _ q.2) hsr'
    obtain ⟨-, e4⟩ := Uniqueness.succComp_inj hi1 (hb _ a.2) (hb _ v.2) ht'
    subst e2
    have := congrArg List.length e4
    simp at this

/-- Replacing the word of a source from `(q, w₁)` to `(v, w₁)` gives a source from `(q, w₂)` to
`(v, w₂)`. -/
theorem cd_subst_mem (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (q v : CompIn (c.stage i).comps) (w₁ w₂ : List WordLetter)
    (hw₂ : w₂ = [] ∨ w₂ ∈ wordsUpTo (weakAlphabet A.Nw) A.Rw) (s : CdSrcSet c i q v w₁) :
    (cdWordSub w₂ s.1).Valid A.Nw A.Rw (1 + (c.M + A.Jw - i) * A.Nw) ∧
      (cdWordSub w₂ s.1).srcComp (c.stage i).level = succComp i q.1 w₂ ∧
      (cdWordSub w₂ s.1).tgtComp (c.stage i).level = succComp i v.1 w₂ := by
  obtain ⟨h, π, n, hs, hsrc, htgt, -, h1, h2, h3⟩ := cd_inh_shape c i hi hit q v w₁ s.1 s.2
  have hlev := (cd_stage_inv c i hi hit).1
  rw [hs]
  refine ⟨⟨hw₂, h1, h2, h3⟩, ?_, ?_⟩
  · simp only [cdWordSub, WeakSource.srcComp, hsrc, hlev]
  · simp only [cdWordSub, WeakSource.tgtComp, htgt, hlev]

/-- **The bijection between the sources at the words `w₁` and `w₂`.** -/
def cdWordEquiv (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (q v : CompIn (c.stage i).comps) (w₁ w₂ : List WordLetter)
    (hw₁ : w₁ = [] ∨ w₁ ∈ wordsUpTo (weakAlphabet A.Nw) A.Rw)
    (hw₂ : w₂ = [] ∨ w₂ ∈ wordsUpTo (weakAlphabet A.Nw) A.Rw) :
    CdSrcSet c i q v w₁ ≃ CdSrcSet c i q v w₂ where
  toFun s := ⟨cdWordSub w₂ s.1, cd_subst_mem c i hi hit q v w₁ w₂ hw₂ s⟩
  invFun s := ⟨cdWordSub w₁ s.1, cd_subst_mem c i hi hit q v w₂ w₁ hw₁ s⟩
  left_inv := by
    rintro ⟨s, hs⟩
    obtain ⟨h, π, n, rfl, -⟩ := cd_inh_shape c i hi hit q v w₁ s hs
    rfl
  right_inv := by
    rintro ⟨s, hs⟩
    obtain ⟨h, π, n, rfl, -⟩ := cd_inh_shape c i hi hit q v w₂ s hs
    rfl

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end
end
end

section
section
/-! **`CdInhClass` is proved**.

For `u'` of parent `q` and word `w`, the children `v'` with an inherited
edge from `u'` reduce to `V0 = (v, w)` (an inherited edge keeps the word); its inherited edges are in
bijection (replace the word `w` by `[]`, `cdWordEquiv`) with the edges `q → v` of the stage
`i - 1`, which are all inherited, of grade `h ∈ [1, J_wR_w]`; the coefficients agree by
`cd_inh_coeff_indep`, and `cdWeight V0 = cdWeight u'`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance

namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

open scoped Classical in
/-- The grade sum of one source. -/
theorem cd_grade_sum {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    {G : GenStage D ScalarH Dm b j₀} (s : WeakSource G) (J : ℕ)
    (hs : ∀ w h π n, s = WeakSource.inherited w h π n → 1 ≤ h ∧ h ≤ J)
    {X : Type*} [AddCommMonoid X] (x : X) :
    (∑ r ∈ Finset.Icc 1 J, if cdIsGrade r s then x else 0) = if cdIsInh s then x else 0 := by
  cases s with
  | inherited w h π n =>
    obtain ⟨h1, h2⟩ := hs w h π n rfl
    simp only [cdIsGrade, cdIsInh, ↓reduceIte]
    rw [Finset.sum_eq_single_of_mem h (Finset.mem_Icc.2 ⟨h1, h2⟩)]
    · simp
    · intro r _ hr
      simp [Ne.symm hr]
  | eddy a w n => simp [cdIsGrade, cdIsInh]

/-- **(b1)** The sum over the children collapses to the child `V0 = (v, w)` with the word of `u'`. -/
theorem cd_inh_collapse (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (v : CompIn (c.stage i).comps) (u' : CompIn (c.stage (i - 1)).comps)
    (V0 : CompIn (c.stage (i - 1)).comps) (hV0 : V0.1 = succComp i v.1 (compWord i u'.1))
    (d : ℕ) (s : ℝ) (x : Vec 2) :
    ∑ v' : CompIn (c.stage (i - 1)).comps, cdLam c i v v' • cdInh c i hi hit v' u' d s x =
      cdWeight c i u'.1 • cdInh c i hi hit V0 u' d s x := by
  classical
  obtain ⟨hlev, hb⟩ := cd_stage_inv c i hi hit
  have hi1 : 1 ≤ i := by omega
  have hpw := Construction.Preservation.FullLift.parent_word_succComp (m := i) hi1 v.1
    (hb _ v.2) (compWord i u'.1)
  rw [Finset.sum_eq_single_of_mem V0 (Finset.mem_univ _)]
  · have hq1 : compParent i V0.1 = v.1 := by rw [hV0]; exact hpw.1
    have hlam : cdLam c i v V0 = cdWeight c i u'.1 := by
      unfold cdLam
      simp only [hq1, ↓reduceIte]
      unfold cdWeight
      rw [hV0, hpw.2]
    rw [hlam]
  · intro v' _ hne
    by_cases hp : compParent i v'.1 = v.1
    · have h0 : cdInh c i hi hit v' u' d s x = 0 := by
        unfold cdInh
        apply Finset.sum_eq_zero
        intro γ _
        by_cases hinh : cdIsInh (cdEdgeSource c i hi hit v' u' γ).1
        · exfalso
          apply hne
          have hw' := cd_isInh_word c i hi hit γ hinh
          have e := Construction.Preservation.FullLift.succComp_parent_word i v'.1
          rw [hp, hw'] at e
          exact Subtype.ext (e.symm.trans hV0.symm)
        · simp only [hinh, ↓reduceIte]
      rw [h0]
      exact cd_smul_zero_clm _ _
    · have : cdLam c i v v' = 0 := by simp [cdLam, hp]
      rw [this]
      exact cd_zero_smul_clm _ _

/-- **(b2)** The inherited edges `(q, w) → (v, w)` are in bijection with the edges `q → v`, with the
same coefficients. -/
theorem cd_inh_V0_sum (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (hζ : IsFastProfile c.D.ζ) (hτ : 0 < ocTau c.D.α c.D.q c.D.Λ i)
    (hcs : 0 ≤ c.D.cellScaleSq i) (v : CompIn (c.stage i).comps)
    (u' : CompIn (c.stage (i - 1)).comps) (hu : compParent i u'.1 ∈ (c.stage i).comps)
    (hvm : v.1 ∈ (c.stage (i - 1)).comps) (hqm : compParent i u'.1 ∈ (c.stage (i - 1)).comps)
    (V0 : CompIn (c.stage (i - 1)).comps) (hV0 : V0.1 = succComp i v.1 (compWord i u'.1))
    (d : ℕ) (s : ℝ) (x : Vec 2) :
    cdInh c i hi hit V0 u' d s x =
      ∑ γ : (c.stage (i - 1)).fam.Γ ⟨v.1, hvm⟩ ⟨compParent i u'.1, hqm⟩,
        (c.stage (i - 1)).physCoeff ⟨v.1, hvm⟩ ⟨compParent i u'.1, hqm⟩ γ d s x := by
  classical
  obtain ⟨hlev, hb⟩ := cd_stage_inv c i hi hit
  obtain ⟨-, hwd⟩ := cd_comp_decomp c i hi hit u'.1 u'.2
  have hu1 : succComp i (compParent i u'.1) (compWord i u'.1) = u'.1 :=
    Construction.Preservation.FullLift.succComp_parent_word i u'.1
  let Q : CompIn (c.stage i).comps := ⟨compParent i u'.1, hu⟩
  let E₁ : (c.stage (i - 1)).fam.Γ V0 u' ≃ CdSrcSet c i Q v (compWord i u'.1) :=
    (cdEdgeSource c i hi hit V0 u').trans (Equiv.subtypeEquivRight (fun s => by
      rw [hV0]; show _ ↔ _; rw [hu1]))
  let E₂ : CdSrcSet c i Q v (compWord i u'.1) ≃ CdSrcSet c i Q v [] :=
    cdWordEquiv c i hi hit Q v _ [] hwd (Or.inl rfl)
  let E₃ : CdSrcSet c i Q v [] ≃
      (c.stage (i - 1)).fam.Γ ⟨v.1, hvm⟩ ⟨compParent i u'.1, hqm⟩ :=
    (Equiv.subtypeEquivRight (fun s => by simp only [succComp, ↓reduceDIte]; exact Iff.rfl)).trans
      (cdEdgeSource c i hi hit ⟨v.1, hvm⟩ ⟨compParent i u'.1, hqm⟩).symm
  let E := E₁.trans (E₂.trans E₃)
  have hsrc : ∀ γ, (cdEdgeSource c i hi hit ⟨v.1, hvm⟩ ⟨compParent i u'.1, hqm⟩ (E γ)).1 =
      cdWordSub [] (cdEdgeSource c i hi hit V0 u' γ).1 := by
    intro γ
    exact congrArg Subtype.val (Equiv.apply_symm_apply
      (cdEdgeSource c i hi hit ⟨v.1, hvm⟩ ⟨compParent i u'.1, hqm⟩) _)
  have hterm : ∀ γ : (c.stage (i - 1)).fam.Γ V0 u',
      (if cdIsInh (cdEdgeSource c i hi hit V0 u' γ).1 then
        (c.stage (i - 1)).physCoeff V0 u' γ d s x else 0) =
      (c.stage (i - 1)).physCoeff ⟨v.1, hvm⟩ ⟨compParent i u'.1, hqm⟩ (E γ) d s x := by
    intro γ
    have hmem := (cdEdgeSource c i hi hit V0 u' γ).2
    have hmem' : (cdEdgeSource c i hi hit V0 u' γ).1.Valid A.Nw A.Rw
        (1 + (c.M + A.Jw - i) * A.Nw) ∧
        (cdEdgeSource c i hi hit V0 u' γ).1.srcComp (c.stage i).level =
          succComp i Q.1 (compWord i u'.1) ∧
        (cdEdgeSource c i hi hit V0 u' γ).1.tgtComp (c.stage i).level =
          succComp i v.1 (compWord i u'.1) := by
      obtain ⟨m1, m2, m3⟩ := hmem
      exact ⟨m1, m2.trans hu1.symm, m3.trans hV0⟩
    obtain ⟨h, π, n, hs1, -⟩ := cd_inh_shape c i hi hit Q v _ _ hmem'
    have hs2 : (cdEdgeSource c i hi hit ⟨v.1, hvm⟩ ⟨compParent i u'.1, hqm⟩ (E γ)).1 =
        WeakSource.inherited [] h π n := by
      rw [hsrc γ, hs1]; rfl
    have hinh : cdIsInh (cdEdgeSource c i hi hit V0 u' γ).1 := by rw [hs1]; trivial
    simp only [hinh, ↓reduceIte]
    rw [cd_inh_coeff_indep c i hi hit hζ hτ hcs γ (E γ) _ [] h π n hs1 hs2 d]
  unfold cdInh
  rw [Finset.sum_congr rfl (fun γ _ => hterm γ)]
  exact Fintype.sum_equiv E _ _ (fun γ => rfl)

/-- **(b3)** The grade sum of the edges `q → v` is the sum of their coefficients. -/
theorem cd_ce_sum (c : WeakPassageInstance plan R) (Dc i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (v : CompIn (c.stage i).comps) (q : Comp)
    (hu : q ∈ (c.stage i).comps) (hvm : v.1 ∈ (c.stage (i - 1)).comps)
    (hqm : q ∈ (c.stage (i - 1)).comps) (d : Finset.Icc 2 Dc) (s : ℝ) (x : Vec 2) :
    ∑ r ∈ Finset.Icc 1 (A.Jw * A.Rw), cdCE c Dc i hi hit r v ⟨q, hu⟩ d s x =
      ∑ γ : (c.stage (i - 1)).fam.Γ ⟨v.1, hvm⟩ ⟨q, hqm⟩,
        (c.stage (i - 1)).physCoeff ⟨v.1, hvm⟩ ⟨q, hqm⟩ γ d.1 s x := by
  classical
  have hce : ∀ r, cdCE c Dc i hi hit r v ⟨q, hu⟩ d s x =
      ∑ γ : (c.stage (i - 1)).fam.Γ ⟨v.1, hvm⟩ ⟨q, hqm⟩,
        if cdIsGrade r (cdEdgeSource c i hi hit ⟨v.1, hvm⟩ ⟨q, hqm⟩ γ).1 then
          (c.stage (i - 1)).physCoeff ⟨v.1, hvm⟩ ⟨q, hqm⟩ γ d.1 s x else 0 := by
    intro r
    unfold cdCE
    simp only [hvm, hqm, and_self, ↓reduceDIte]
  simp only [hce]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun γ _ => ?_)
  rw [cd_grade_sum _ (A.Jw * A.Rw) ?_ ((c.stage (i - 1)).physCoeff ⟨v.1, hvm⟩ ⟨q, hqm⟩ γ d.1 s x)]
  · have hmem := (cdEdgeSource c i hi hit ⟨v.1, hvm⟩ ⟨q, hqm⟩ γ).2
    have hlev := (cd_stage_inv c i hi hit).1
    have hmem' : (cdEdgeSource c i hi hit ⟨v.1, hvm⟩ ⟨q, hqm⟩ γ).1.Valid A.Nw A.Rw
        (1 + (c.M + A.Jw - i) * A.Nw) ∧
        (cdEdgeSource c i hi hit ⟨v.1, hvm⟩ ⟨q, hqm⟩ γ).1.srcComp (c.stage i).level =
          succComp i (⟨q, hu⟩ : CompIn (c.stage i).comps).1 [] ∧
        (cdEdgeSource c i hi hit ⟨v.1, hvm⟩ ⟨q, hqm⟩ γ).1.tgtComp (c.stage i).level =
          succComp i v.1 [] := by
      obtain ⟨m1, m2, m3⟩ := hmem
      refine ⟨m1, ?_, ?_⟩
      · rw [m2]; simp [succComp]
      · rw [m3]; simp [succComp]
    obtain ⟨h, π, n, hs1, -⟩ := cd_inh_shape c i hi hit ⟨q, hu⟩ v _ _ hmem'
    have hinh : cdIsInh (cdEdgeSource c i hi hit ⟨v.1, hvm⟩ ⟨q, hqm⟩ γ).1 := by
      rw [hs1]; trivial
    simp only [hinh, ↓reduceIte]
  · intro w h π n hs1
    obtain ⟨-, -, -, -, -, -, -, h1, -⟩ := cd_inh_facts c i hi hit γ hs1
    exact ⟨h1, EntryWeakProofs.weakConstruction_path_length_bound c.P _ c.M A.Jw 0 _ c.stage
      c.construction i hi.le hit h π⟩

/-- **`CdInhClass` is proved** (from the common plan hypothesis, as every weak statement). -/
theorem cdInhClass (plan : WeakPassagePlan) (hplan : WeakPassageCommonOK plan) :
    CdInhClass plan := by
  intro B A R Dc c i hi hit v u' hu d s x
  classical
  have hbase : weakCommonCoeffPlan.baseThreshold B ≤ A.Λ := (hplan.1 B).trans c.base_ge
  have h128 : 128 ≤ A.Λ := (weakCommonCoeffPlan.baseThreshold_ge B).trans hbase
  have hΛ : 1 ≤ c.D.Λ := by rw [c.base_eq]; omega
  have hζ : IsFastProfile c.D.ζ := by rw [c.profile_eq]; exact B.hζ
  have hκb : IsOCBandChain c.D.α c.D.q c.D.Λ c.D.ζ c.D.term c.D.κ := by
    rw [c.alpha, c.q_eq, c.base_eq, c.profile_eq, c.terminal]; exact c.band
  have hcs : 0 ≤ c.D.cellScaleSq i :=
    (EntryWeakProofs.weakData_cellScaleSq_pos c.D hΛ hζ hκb i).le
  have hτ : 0 < ocTau c.D.α c.D.q c.D.Λ i := Construction.Stream.ocTau_pos hΛ
  obtain ⟨-, hwd⟩ := cd_comp_decomp c i hi hit u'.1 u'.2
  have hvm : v.1 ∈ (c.stage (i - 1)).comps := by
    have := cd_succComp_mem c i hi hit v [] (Or.inl rfl)
    simpa [succComp] using this
  have hqm : compParent i u'.1 ∈ (c.stage (i - 1)).comps := by
    have := cd_succComp_mem c i hi hit ⟨_, hu⟩ [] (Or.inl rfl)
    simpa [succComp] using this
  have hV0m := cd_succComp_mem c i hi hit v _ hwd
  obtain ⟨V0, hV0⟩ : ∃ V0 : CompIn (c.stage (i - 1)).comps,
      V0.1 = succComp i v.1 (compWord i u'.1) := ⟨⟨_, hV0m⟩, rfl⟩
  rw [cd_inh_collapse c i hi hit v u' V0 hV0 d.1 s x,
    cd_inh_V0_sum c i hi hit hζ hτ hcs v u' hu hvm hqm V0 hV0 d.1 s x,
    ← cd_ce_sum c Dc i hi hit v (compParent i u'.1) hu hvm hqm d s x]

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end
end

section
/-! **The coarse defect equation of the readout**: `WeakCoarseDefectStatement plan`
for every plan whose floors dominate the common plan's (`WeakPassageCommonOK`), from the two proved
edge classifications `cdInhClass` and `cdEddClass`. -/

@[expose] public noncomputable section

namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction

/-- **The coarse defect equation of the readout is proved.** -/
theorem weakCoarseDefect (plan : WeakPassagePlan) (hcommon : WeakPassageCommonOK plan) :
    WeakCoarseDefectStatement plan :=
  weakCoarseDefect_of_classes plan hcommon (cdInhClass plan hcommon) (cdEddClass plan)

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end
end

section
/-! **The initial datum of the window, proved**. The trace of the family of stage `i`
vanishes on the new components; the only old child of `v` is `v` with the empty word and weight
`1`; the family of stage `i` truncates to `r.Ur i` at `t_i` (`weakCoarse_zero_values`). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance

namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction
  AVRegularity.Providers.WeakGen.Residual

/-- **At order zero the initial datum of the window is the incoming value.** -/
theorem weakCoarseInitial (plan : WeakPassagePlan) : WeakCoarseInitialStatement plan := by
  classical
  intro B A R m N hN c r Uhi hvr hval i hi hit hwin v
  obtain ⟨-, hb⟩ := cd_stage_inv c i hi hit
  have hold : ∀ w : Comp, w ∈ (c.stage i).comps → compWord i w = [] ∧ compParent i w = w :=
    fun w hw => by
      have h0 := compWord_nil_of_old i (by omega) w (hb _ hw)
      exact ⟨h0, compParent_eq_of_compWord_nil i w h0⟩
  have hmem : v.1 ∈ (c.stage (i - 1)).comps := by
    rw [cd_comps_eq c i hi hit]
    unfold weakExtComps
    exact Finset.mem_union_left _ v.2
  unfold cdF
  rw [cdReadout_truncate c m 0 N (Nat.zero_le N) _ i (fun _ => True)]
  unfold cdReadout
  rw [Finset.sum_eq_single ⟨v.1, hmem⟩]
  · have hp := (hold v.1 v.2).2
    have hw := (hold v.1 v.2).1
    rw [ite_eq_left_of_eq_true _ _ (eq_true (⟨hp, trivial⟩ : _ ∧ True))]
    have hwt : cdWeight c i v.1 = 1 := by unfold cdWeight; rw [hw]; simp
    rw [hwt, one_smul, weakStageTrace_old (weakPassageRawSetting c) m i (Uhi i) (r.tq i) _ v.2]
    have ht : r.tq i ∈ Set.Icc (r.tq (i + 1)) (r.a + A.T₀) :=
      ⟨(weakPassageRawClock r).tq_step i hi hit, hwin⟩
    have hz := weakCoarse_zero_values m c r Uhi hvr hval i hi hit v (r.tq i) ht
    unfold weakIncomingInit
    exact hz
  · intro v' _ hne
    split_ifs with hc
    · by_cases hv' : v'.1 ∈ (c.stage i).comps
      · exfalso
        apply hne
        apply Subtype.ext
        have := (hold v'.1 hv').2
        rw [this] at hc
        exact hc.1
      · rw [weakStageTrace_new (weakPassageRawSetting c) m i (Uhi i) (r.tq i) v' hv']
        simp
    · rfl
  · intro h; exact absurd (Finset.mem_univ _) h

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end
end
end
end
