-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.MixedWords.StageExpansionLetter
public import AVRegularity.CycleWords.Assembly.InteriorScalarIngredients
public import AVRegularity.CycleWords.MixedWords.LetterBlochClauses

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords.Assembly

/-! # The stage expansion of the tested sources

`stageExpansion`: from the letter Bloch identity, the tested source of a stage is the sum over the
stages `i'` of the cell pairings of their values with the test transforms `T_{i,i'}`. -/

universe u v

section Pairing

theorem stageTests_mul_mem {f g : Vec 2 → ℂ} (hf : f ∈ stageTests) (hg : g ∈ stageTests) :
    (fun z => f z * g z) ∈ stageTests :=
  ⟨hf.1.mul hg.1, fun n x => by simp only [hf.2 n x, hg.2 n x]⟩

theorem stageTests_add_mem {f g : Vec 2 → ℂ} (hf : f ∈ stageTests) (hg : g ∈ stageTests) :
    (fun z => f z + g z) ∈ stageTests := stageTests.add_mem hf hg

theorem stageTests_sub_mem {f g : Vec 2 → ℂ} (hf : f ∈ stageTests) (hg : g ∈ stageTests) :
    (fun z => f z - g z) ∈ stageTests := stageTests.sub_mem hf hg

theorem stageTests_neg_mem {f : Vec 2 → ℂ} (hf : f ∈ stageTests) :
    (fun z => -f z) ∈ stageTests := stageTests.neg_mem hf

theorem stagePair_ite_test (θ : Vec 2) (G : Vec 2 → ℝ) {Gi : Integrable G} {C : Prop}
    [Decidable C] (c : ℂ) {f : Vec 2 → ℂ} (hf : f ∈ stageTests) :
    stagePair θ G (fun z => if C then c * f z else 0) =
      if C then c * stagePair θ G f else 0 := by
  by_cases hC : C
  · simp only [hC, ite_true]
    exact stagePair_mul_test θ Gi c hf
  · simp only [hC, ite_false]
    exact stagePair_zero θ G

theorem stagePair_sub_test (θ : Vec 2) {G : Vec 2 → ℝ} (hG : Integrable G) {f₁ f₂ : Vec 2 → ℂ}
    (h₁ : f₁ ∈ stageTests) (h₂ : f₂ ∈ stageTests) :
    stagePair θ G (fun z => f₁ z - f₂ z) = stagePair θ G f₁ - stagePair θ G f₂ := by
  have h := stagePair_add_test θ hG h₁ (stageTests_const_mul_mem (-1) h₂)
  rw [stagePair_mul_test θ hG (-1) h₂] at h
  simp only [neg_one_mul, ← sub_eq_add_neg] at h
  exact h

theorem stagePair_neg_test (θ : Vec 2) {G : Vec 2 → ℝ} (hG : Integrable G) {f : Vec 2 → ℂ}
    (hf : f ∈ stageTests) : stagePair θ G (fun z => -f z) = -stagePair θ G f := by
  have h := stagePair_mul_test θ hG (-1) hf
  simpa using h

end Pairing

section Same

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D Nw m : ℕ}
  {Ks : Fin Nw → ℕ}

omit [Fintype ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- The cell pairing of the same-level transform at the stage `i'`. -/
theorem stageExp_same_pair (θ : Vec 2) (Gm : Matrix (Fin 2) (Fin 2) ℝ) (vf : Vec 2 → Vec 2)
    (i i' : B1WIndex ι h Nw m Ks) (φ : Vec 2 → ℂ) (hφ : φ ∈ stageTests)
    (hD : ∀ k, fibreCovDeriv (-θ) k φ ∈ stageTests)
    (hv : ∀ k, (fun z => (vf z k : ℂ)) ∈ stageTests) {Gs : Vec 2 → ℝ} (hGs : Integrable Gs) :
    stagePair θ Gs (b1wSameTransform θ Gm vf i i' φ) =
      if i'.1 = i.1 then
        (inner ℝ (b1wSameVec i i') (b1wVec i') : ℂ) *
          ((if b1wMom i' = ((b1wMom i).1 - 2, (b1wMom i).2) then
              ((Gm 0 0 * (((b1wMom i).1 : ℝ) * (((b1wMom i).1 : ℝ) - 1)) : ℝ) : ℂ) *
                stagePair θ Gs φ else 0) +
            (if b1wMom i' = ((b1wMom i).1 - 1, (b1wMom i).2 - 1) then
              (((Gm 0 1 + Gm 1 0) * (((b1wMom i).1 : ℝ) * ((b1wMom i).2 : ℝ)) : ℝ) : ℂ) *
                stagePair θ Gs φ else 0) +
            (if b1wMom i' = ((b1wMom i).1, (b1wMom i).2 - 2) then
              ((Gm 1 1 * (((b1wMom i).2 : ℝ) * (((b1wMom i).2 : ℝ) - 1)) : ℝ) : ℂ) *
                stagePair θ Gs φ else 0) +
            (if b1wMom i' = ((b1wMom i).1 - 1, (b1wMom i).2) then
              (((b1wMom i).1 : ℝ) : ℂ) * stagePair θ Gs (fun z => (vf z 0 : ℂ) * φ z +
                ∑ k : Fin 2, ((Gm k 0 + Gm 0 k : ℝ) : ℂ) * fibreCovDeriv (-θ) k φ z) else 0) +
            (if b1wMom i' = ((b1wMom i).1, (b1wMom i).2 - 1) then
              (((b1wMom i).2 : ℝ) : ℂ) * stagePair θ Gs (fun z => (vf z 1 : ℂ) * φ z +
                ∑ k : Fin 2, ((Gm k 1 + Gm 1 k : ℝ) : ℂ) * fibreCovDeriv (-θ) k φ z) else 0))
      else 0 := by
  have hT : ∀ (a : Fin 2) (c : Fin 2 → Fin 2 → ℝ), (fun z => (vf z a : ℂ) * φ z +
      ∑ k : Fin 2, (c k a : ℂ) * fibreCovDeriv (-θ) k φ z) ∈ stageTests := by
    intro a c
    refine stageTests_add_mem (stageTests_mul_mem (hv a) hφ) (stageTests_sum_mem _ _ fun k _ => ?_)
    exact stageTests_const_mul_mem _ (hD k)
  have hm1 := stageTests_ite_mem (C := b1wMom i' = ((b1wMom i).1 - 2, (b1wMom i).2))
    ((Gm 0 0 * (((b1wMom i).1 : ℝ) * (((b1wMom i).1 : ℝ) - 1)) : ℝ) : ℂ) hφ
  have hm2 := stageTests_ite_mem (C := b1wMom i' = ((b1wMom i).1 - 1, (b1wMom i).2 - 1))
    (((Gm 0 1 + Gm 1 0) * (((b1wMom i).1 : ℝ) * ((b1wMom i).2 : ℝ)) : ℝ) : ℂ) hφ
  have hm3 := stageTests_ite_mem (C := b1wMom i' = ((b1wMom i).1, (b1wMom i).2 - 2))
    ((Gm 1 1 * (((b1wMom i).2 : ℝ) * (((b1wMom i).2 : ℝ) - 1)) : ℝ) : ℂ) hφ
  have hm4 := stageTests_ite_mem (C := b1wMom i' = ((b1wMom i).1 - 1, (b1wMom i).2))
    (((b1wMom i).1 : ℝ) : ℂ) (hT 0 fun k a => Gm k a + Gm a k)
  have hm5 := stageTests_ite_mem (C := b1wMom i' = ((b1wMom i).1, (b1wMom i).2 - 1))
    (((b1wMom i).2 : ℝ) : ℂ) (hT 1 fun k a => Gm k a + Gm a k)
  unfold b1wSameTransform
  by_cases hC : i'.1 = i.1
  · simp only [hC, ite_true]
    have hsum := stageTests_add_mem (stageTests_add_mem (stageTests_add_mem
      (stageTests_add_mem hm1 hm2) hm3) hm4) hm5
    rw [stagePair_mul_test θ hGs _ hsum]
    congr 1
    rw [stagePair_add_test θ hGs (stageTests_add_mem (stageTests_add_mem
      (stageTests_add_mem hm1 hm2) hm3) hm4) hm5,
      stagePair_add_test θ hGs (stageTests_add_mem (stageTests_add_mem hm1 hm2) hm3) hm4,
      stagePair_add_test θ hGs (stageTests_add_mem hm1 hm2) hm3, stagePair_add_test θ hGs hm1 hm2]
    rw [stagePair_ite_test θ Gs _ hφ, stagePair_ite_test θ Gs _ hφ, stagePair_ite_test θ Gs _ hφ,
      stagePair_ite_test θ Gs _ (hT 0 fun k a => Gm k a + Gm a k),
      stagePair_ite_test θ Gs _ (hT 1 fun k a => Gm k a + Gm a k)]
    all_goals exact hGs
  · simp only [hC, ite_false]
    exact stagePair_zero θ Gs

omit [Fintype ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- The same-level transform is a continuous periodic test. -/
theorem stageExp_same_mem (θ : Vec 2) (Gm : Matrix (Fin 2) (Fin 2) ℝ) (vf : Vec 2 → Vec 2)
    (i i' : B1WIndex ι h Nw m Ks) (φ : Vec 2 → ℂ) (hφ : φ ∈ stageTests)
    (hD : ∀ k, fibreCovDeriv (-θ) k φ ∈ stageTests)
    (hv : ∀ k, (fun z => (vf z k : ℂ)) ∈ stageTests) :
    b1wSameTransform θ Gm vf i i' φ ∈ stageTests := by
  have hT : ∀ (a : Fin 2) (c : Fin 2 → Fin 2 → ℝ), (fun z => (vf z a : ℂ) * φ z +
      ∑ k : Fin 2, (c k a : ℂ) * fibreCovDeriv (-θ) k φ z) ∈ stageTests := by
    intro a c
    refine stageTests_add_mem (stageTests_mul_mem (hv a) hφ) (stageTests_sum_mem _ _ fun k _ => ?_)
    exact stageTests_const_mul_mem _ (hD k)
  have hm1 := stageTests_ite_mem (C := b1wMom i' = ((b1wMom i).1 - 2, (b1wMom i).2))
    ((Gm 0 0 * (((b1wMom i).1 : ℝ) * (((b1wMom i).1 : ℝ) - 1)) : ℝ) : ℂ) hφ
  have hm2 := stageTests_ite_mem (C := b1wMom i' = ((b1wMom i).1 - 1, (b1wMom i).2 - 1))
    (((Gm 0 1 + Gm 1 0) * (((b1wMom i).1 : ℝ) * ((b1wMom i).2 : ℝ)) : ℝ) : ℂ) hφ
  have hm3 := stageTests_ite_mem (C := b1wMom i' = ((b1wMom i).1, (b1wMom i).2 - 2))
    ((Gm 1 1 * (((b1wMom i).2 : ℝ) * (((b1wMom i).2 : ℝ) - 1)) : ℝ) : ℂ) hφ
  have hm4 := stageTests_ite_mem (C := b1wMom i' = ((b1wMom i).1 - 1, (b1wMom i).2))
    (((b1wMom i).1 : ℝ) : ℂ) (hT 0 fun k a => Gm k a + Gm a k)
  have hm5 := stageTests_ite_mem (C := b1wMom i' = ((b1wMom i).1, (b1wMom i).2 - 1))
    (((b1wMom i).2 : ℝ) : ℂ) (hT 1 fun k a => Gm k a + Gm a k)
  unfold b1wSameTransform
  by_cases hC : i'.1 = i.1
  · simp only [hC, ite_true]
    exact stageTests_const_mul_mem _ (stageTests_add_mem (stageTests_add_mem (stageTests_add_mem
      (stageTests_add_mem hm1 hm2) hm3) hm4) hm5)
  · simp only [hC, ite_false]
    exact stageTests.zero_mem


theorem stageExp_momentIndices_sub {n : ℕ} {β : ℕ × ℕ} (hβ : β ∈ momentIndices n) (a b : ℕ) :
    (β.1 - a, β.2 - b) ∈ momentIndices n := by
  simp only [momentIndices, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hβ ⊢
  omega

theorem stageExp_sum_subtype_ite {S : Finset (ℕ × ℕ)} {τ : ℕ × ℕ} (hτ : τ ∈ S)
    (c : {β // β ∈ S} → Prop) [DecidablePred c] (hc : ∀ β', c β' ↔ β'.1 = τ)
    (f : {β // β ∈ S} → ℂ) :
    ∑ β' : {β // β ∈ S}, (if c β' then f β' else 0) = f ⟨τ, hτ⟩ := by
  rw [Finset.sum_eq_single (⟨τ, hτ⟩ : {β // β ∈ S})]
  · simp [(hc _).2]
  · intro β' _ hne
    have : ¬ c β' := fun h => hne (Subtype.ext ((hc _).1 h))
    simp [this]
  · intro h
    exact absurd (Finset.mem_univ _) h

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
theorem stageExp_sum_index (f : B1WIndex ι h Nw m Ks → ℂ) :
    ∑ i' : B1WIndex ι h Nw m Ks, f i' = ∑ j : Fin (Nw + 1), ∑ x : ι,
      ∑ β : {β // β ∈ momentIndices (b1wLevelMoments m Ks j)},
        ∑ b : Fin (Module.finrank ℝ (h x)), f ⟨j, x, β, b⟩ := by
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type]


omit [Fintype ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem b1wSameVec_self (i : B1WIndex ι h Nw m Ks)
    (β : {β // β ∈ momentIndices (b1wLevelMoments m Ks i.1)}) (b : Fin (Module.finrank ℝ (h i.2.1))) :
    b1wSameVec i (⟨i.1, i.2.1, β, b⟩ : B1WIndex ι h Nw m Ks) = b1wVec i := by
  simp [b1wSameVec]

omit [Fintype ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem b1w_inner_vec (i : B1WIndex ι h Nw m Ks)
    (β : {β // β ∈ momentIndices (b1wLevelMoments m Ks i.1)}) (b : Fin (Module.finrank ℝ (h i.2.1))) :
    inner ℝ (b1wVec i) (b1wVec (⟨i.1, i.2.1, β, b⟩ : B1WIndex ι h Nw m Ks)) =
      if i.2.2.2 = b then (1 : ℝ) else 0 := by
  unfold b1wVec
  exact orthonormal_iff_ite.1 (stdOrthonormalBasis ℝ (h i.2.1)).orthonormal _ _


end Same


section SameSum

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D Nw m : ℕ}
  {Ks : Fin Nw → ℕ} {K : ScalarConstants} {g₁ : ℝ}

/-- **The same-level part of the expansion.** -/
theorem stageExp_same_sum
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (hM : AmplitudeIdMoments F)
    (θ : Vec 2) (i : B1WIndex ι h Nw m Ks) (r : ℝ) (hr : r ∈ Icc F.a F.b) (φ : Vec 2 → ℂ)
    (hφ : φ ∈ stageTests) (hD : ∀ k, fibreCovDeriv (-θ) k φ ∈ stageTests)
    (hv : ∀ k, (fun z => (F.v r z k : ℂ)) ∈ stageTests) :
    ∑ i' : B1WIndex ι h Nw m Ks, stagePair θ (fun y => momentWeight (b1wMom i') y *
        inner ℝ (b1wVec i') (planeValue (F.u i'.1 i'.2.1 r) y))
      (b1wSameTransform θ (F.G r) (F.v r) i i' φ) =
      b1wSameLevel θ (F.G r) (F.v r) (b1wMom i) (b1wVec i) (planeValue (F.u i.1 i.2.1 r)) φ := by
  have hG : ∀ i' : B1WIndex ι h Nw m Ks, Integrable (fun y => momentWeight (b1wMom i') y *
      inner ℝ (b1wVec i') (planeValue (F.u i'.1 i'.2.1 r) y)) :=
    fun i' => stageExp_integrable_moment F hM i'.1 i'.2.1 r hr _ _
  rw [stageExp_sum_index, Finset.sum_eq_single i.1]
  · rw [Finset.sum_eq_single i.2.1]
    · simp only [fun i' => stageExp_same_pair θ (F.G r) (F.v r) i i' φ hφ hD hv (hG i')]
      simp only [ite_true, b1wSameVec_self, b1w_inner_vec]
      simp only [apply_ite Complex.ofReal, Complex.ofReal_one, Complex.ofReal_zero, ite_mul,
        one_mul, zero_mul]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      have hβ := i.2.2.1.2
      have m1 : ((b1wMom i).1 - 2, (b1wMom i).2) ∈
          momentIndices (b1wLevelMoments m Ks i.1) := by
        simpa [b1wMom] using stageExp_momentIndices_sub hβ 2 0
      have m2 : ((b1wMom i).1 - 1, (b1wMom i).2 - 1) ∈
          momentIndices (b1wLevelMoments m Ks i.1) := stageExp_momentIndices_sub hβ 1 1
      have m3 : ((b1wMom i).1, (b1wMom i).2 - 2) ∈
          momentIndices (b1wLevelMoments m Ks i.1) := by
        simpa [b1wMom] using stageExp_momentIndices_sub hβ 0 2
      have m4 : ((b1wMom i).1 - 1, (b1wMom i).2) ∈
          momentIndices (b1wLevelMoments m Ks i.1) := by
        simpa [b1wMom] using stageExp_momentIndices_sub hβ 1 0
      have m5 : ((b1wMom i).1, (b1wMom i).2 - 1) ∈
          momentIndices (b1wLevelMoments m Ks i.1) := by
        simpa [b1wMom] using stageExp_momentIndices_sub hβ 0 1
      simp only [Finset.sum_add_distrib]
      rw [stageExp_sum_subtype_ite m1 _ ?h1, stageExp_sum_subtype_ite m2 _ ?h2,
        stageExp_sum_subtype_ite m3 _ ?h3, stageExp_sum_subtype_ite m4 _ ?h4,
        stageExp_sum_subtype_ite m5 _ ?h5]
      · rfl
      all_goals exact fun _ => Iff.rfl
    · intro x' _ hne
      refine Finset.sum_eq_zero fun β _ => Finset.sum_eq_zero fun b _ => ?_
      rw [stageExp_same_pair θ (F.G r) (F.v r) i _ φ hφ hD hv (hG _)]
      have hne' : ¬ i.2.1 = x' := fun h => hne h.symm
      simp [b1wSameVec, hne']
    · simp
  · intro j' _ hne
    refine Finset.sum_eq_zero fun x' _ => Finset.sum_eq_zero fun β _ =>
      Finset.sum_eq_zero fun b _ => ?_
    rw [stageExp_same_pair θ (F.G r) (F.v r) i _ φ hφ hD hv (hG _)]
    simp [hne]
  · simp

end SameSum

section LetterSum

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D Nw m : ℕ}
  {Ks : Fin Nw → ℕ} {K : ScalarConstants} {g₁ : ℝ}

/-- The letter transform of a stage of level `l + 1`: only the previous level `l` contributes. -/
theorem stageExp_letterTransform_eq
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (l : Fin Nw)
    (x : ι) (β : {β // β ∈ momentIndices (b1wLevelMoments m Ks l.succ)})
    (b : Fin (Module.finrank ℝ (h x))) (i' : B1WIndex ι h Nw m Ks) (r : ℝ) (φ : Vec 2 → ℂ) :
    b1wLetterTransform F θ (⟨l.succ, x, β, b⟩ : B1WIndex ι h Nw m Ks) i' r φ = fun z =>
      if i'.1 = l.castSucc then
        -((((β.1).1 : ℝ) : ℂ) * b1wLetterPart F θ l x (stdOrthonormalBasis ℝ (h x) b)
            ((β.1.1 - 1, β.1.2)) 0 r φ i' z) -
          (((β.1).2 : ℝ) : ℂ) * b1wLetterPart F θ l x (stdOrthonormalBasis ℝ (h x) b)
            (β.1.1, β.1.2 - 1) 1 r φ i' z -
          ∑ k : Fin 2, b1wLetterPart F θ l x (stdOrthonormalBasis ℝ (h x) b) β.1 k r
            (fibreCovDeriv (-θ) k φ) i' z
      else 0 := by
  funext z
  unfold b1wLetterTransform
  rw [Finset.sum_eq_single l]
  · simp
    rfl
  · intro l' _ hne
    refine ite_eq_right_iff.2 ?_
    rintro ⟨h1, _⟩
    exact absurd (Fin.succ_injective _ h1).symm hne
  · intro hl
    exact absurd (Finset.mem_univ _) hl

/-- The cell pairing of the letter transform. -/
theorem stageExp_letter_pair
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁)
    (hord : ∀ l, (F.letters l).order ≤ F.J) (θ : Vec 2) (l : Fin Nw)
    (x : ι) (β : {β // β ∈ momentIndices (b1wLevelMoments m Ks l.succ)})
    (b : Fin (Module.finrank ℝ (h x))) (i' : B1WIndex ι h Nw m Ks) (r : ℝ)
    (hr : r ∈ Icc F.a F.b) (φ : Vec 2 → ℂ)
    (hφ : ContDiff ℝ (Finset.univ.sup fun l => (F.letters l).order) φ)
    (hφp : AVenhance.IsZ2Periodic φ)
    (hD : ∀ k, ContDiff ℝ (Finset.univ.sup fun l => (F.letters l).order)
      (fibreCovDeriv (-θ) k φ)) {Gs : Vec 2 → ℝ} (hGs : Integrable Gs) :
    stagePair θ Gs (b1wLetterTransform F θ (⟨l.succ, x, β, b⟩ : B1WIndex ι h Nw m Ks) i' r φ) =
      if i'.1 = l.castSucc then
        -((((β.1).1 : ℝ) : ℂ) * stagePair θ Gs (b1wLetterPart F θ l x (stdOrthonormalBasis ℝ (h x) b)
            ((β.1.1 - 1, β.1.2)) 0 r φ i')) -
          (((β.1).2 : ℝ) : ℂ) * stagePair θ Gs (b1wLetterPart F θ l x
            (stdOrthonormalBasis ℝ (h x) b) (β.1.1, β.1.2 - 1) 1 r φ i') -
          ∑ k : Fin 2, stagePair θ Gs (b1wLetterPart F θ l x (stdOrthonormalBasis ℝ (h x) b) β.1 k r
            (fibreCovDeriv (-θ) k φ) i')
      else 0 := by
  rw [stageExp_letterTransform_eq]
  by_cases hC : i'.1 = l.castSucc
  · simp only [hC, ite_true]
    have e0 := stageExp_letterPart_mem F hord θ l x (stdOrthonormalBasis ℝ (h x) b)
      (β.1.1 - 1, β.1.2) 0 r hr φ hφ hφp i'
    have e1 := stageExp_letterPart_mem F hord θ l x (stdOrthonormalBasis ℝ (h x) b)
      (β.1.1, β.1.2 - 1) 1 r hr φ hφ hφp i'
    have ek : ∀ k, b1wLetterPart F θ l x (stdOrthonormalBasis ℝ (h x) b) β.1 k r
        (fibreCovDeriv (-θ) k φ) i' ∈ stageTests := fun k =>
      stageExp_letterPart_mem F hord θ l x (stdOrthonormalBasis ℝ (h x) b) β.1 k r hr _ (hD k)
        (isZ2Periodic_fibreCovDeriv hφp _ k) i'
    have hA : (fun z => -((((β.1).1 : ℝ) : ℂ) * b1wLetterPart F θ l x (stdOrthonormalBasis ℝ (h x) b)
            ((β.1.1 - 1, β.1.2)) 0 r φ i' z)) ∈ stageTests :=
      stageTests_neg_mem (stageTests_const_mul_mem _ e0)
    have hB : (fun z => (((β.1).2 : ℝ) : ℂ) * b1wLetterPart F θ l x (stdOrthonormalBasis ℝ (h x) b)
            ((β.1.1, β.1.2 - 1)) 1 r φ i' z) ∈ stageTests := stageTests_const_mul_mem _ e1
    have hAB := stageTests_sub_mem hA hB
    have hS := stageTests_sum_mem (Finset.univ : Finset (Fin 2)) _ fun k _ => ek k
    rw [stagePair_sub_test θ hGs hAB hS, stagePair_sub_test θ hGs hA hB,
      stagePair_neg_test θ hGs (stageTests_const_mul_mem _ e0),
      stagePair_mul_test θ hGs _ e0, stagePair_mul_test θ hGs _ e1,
      stagePair_sum_test θ hGs _ _ fun k _ => ek k]
  · simp only [hC, ite_false]
    exact stagePair_zero θ Gs


/-- **The letter part of the expansion**, for a stage of level `l + 1`. -/
theorem stageExp_letter_sum
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁)
    (hslow : ∀ l, (F.letters l).slow = Ks l) (hord : ∀ l, (F.letters l).order ≤ F.J)
    (hM : AmplitudeIdMoments F) (θ : Vec 2) (l : Fin Nw)
    (x : ι) (β : {β // β ∈ momentIndices (b1wLevelMoments m Ks l.succ)})
    (b : Fin (Module.finrank ℝ (h x))) (r : ℝ)
    (hr : r ∈ Icc F.a F.b) (φ : Vec 2 → ℂ)
    (hφ : ContDiff ℝ (Finset.univ.sup fun l => (F.letters l).order) φ)
    (hφp : AVenhance.IsZ2Periodic φ)
    (hD : ∀ k, ContDiff ℝ (Finset.univ.sup fun l => (F.letters l).order)
      (fibreCovDeriv (-θ) k φ)) :
    ∑ i' : B1WIndex ι h Nw m Ks, stagePair θ (fun y => momentWeight (b1wMom i') y *
        inner ℝ (b1wVec i') (planeValue (F.u i'.1 i'.2.1 r) y))
      (b1wLetterTransform F θ (⟨l.succ, x, β, b⟩ : B1WIndex ι h Nw m Ks) i' r φ) =
      -((((β.1).1 : ℝ) : ℂ) * b1wLetterExpansion F θ l x (stdOrthonormalBasis ℝ (h x) b)
            (β.1.1 - 1, β.1.2) 0 r φ) -
        (((β.1).2 : ℝ) : ℂ) * b1wLetterExpansion F θ l x (stdOrthonormalBasis ℝ (h x) b)
          (β.1.1, β.1.2 - 1) 1 r φ -
        ∑ k : Fin 2, b1wLetterExpansion F θ l x (stdOrthonormalBasis ℝ (h x) b) β.1 k r
          (fibreCovDeriv (-θ) k φ) := by
  have hG : ∀ i' : B1WIndex ι h Nw m Ks, Integrable (fun y => momentWeight (b1wMom i') y *
      inner ℝ (b1wVec i') (planeValue (F.u i'.1 i'.2.1 r) y)) :=
    fun i' => stageExp_integrable_moment F hM i'.1 i'.2.1 r hr _ _
  have hβ := β.2
  have hb1 : ((β.1.1 - 1, β.1.2) : ℕ × ℕ).1 + (β.1.1 - 1, β.1.2).2 ≤ b1wLevelMoments m Ks l.succ := by
    simp only [momentIndices, Finset.mem_filter] at hβ
    simp only
    omega
  have hb2 : ((β.1.1, β.1.2 - 1) : ℕ × ℕ).1 + (β.1.1, β.1.2 - 1).2 ≤ b1wLevelMoments m Ks l.succ := by
    simp only [momentIndices, Finset.mem_filter] at hβ
    simp only
    omega
  have hb3 : β.1.1 + β.1.2 ≤ b1wLevelMoments m Ks l.succ := by
    simp only [momentIndices, Finset.mem_filter] at hβ
    exact hβ.2
  simp only [Fin.sum_univ_two]
  rw [stageExp_letter_key F hslow hord hM θ l x _ _ hb1 0 r hr φ hφ hφp,
    stageExp_letter_key F hslow hord hM θ l x _ _ hb2 1 r hr φ hφ hφp,
    stageExp_letter_key F hslow hord hM θ l x _ _ hb3 0 r hr _ (hD 0)
      (isZ2Periodic_fibreCovDeriv hφp _ 0),
    stageExp_letter_key F hslow hord hM θ l x _ _ hb3 1 r hr _ (hD 1)
      (isZ2Periodic_fibreCovDeriv hφp _ 1)]
  rw [stageExp_sum_index, Finset.sum_eq_single l.castSucc]
  · simp only [fun i' => stageExp_letter_pair F hord θ l x β b i' r hr φ hφ hφp hD (hG i')]
    simp only [ite_true, Fin.sum_univ_two]
    simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    rfl
  · intro j' _ hne
    refine Finset.sum_eq_zero fun x' _ => Finset.sum_eq_zero fun β' _ =>
      Finset.sum_eq_zero fun b' _ => ?_
    rw [stageExp_letter_pair F hord θ l x β b _ r hr φ hφ hφp hD (hG _)]
    simp [hne]
  · simp


/-- The letter transform of a stage of level `l + 1` is a continuous periodic test. -/
theorem stageExp_letterTransform_mem
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁)
    (hord : ∀ l, (F.letters l).order ≤ F.J) (θ : Vec 2) (l : Fin Nw)
    (x : ι) (β : {β // β ∈ momentIndices (b1wLevelMoments m Ks l.succ)})
    (b : Fin (Module.finrank ℝ (h x))) (i' : B1WIndex ι h Nw m Ks) (r : ℝ)
    (hr : r ∈ Icc F.a F.b) (φ : Vec 2 → ℂ)
    (hφ : ContDiff ℝ (Finset.univ.sup fun l => (F.letters l).order) φ)
    (hφp : AVenhance.IsZ2Periodic φ)
    (hD : ∀ k, ContDiff ℝ (Finset.univ.sup fun l => (F.letters l).order)
      (fibreCovDeriv (-θ) k φ)) :
    b1wLetterTransform F θ (⟨l.succ, x, β, b⟩ : B1WIndex ι h Nw m Ks) i' r φ ∈ stageTests := by
  rw [stageExp_letterTransform_eq]
  by_cases hC : i'.1 = l.castSucc
  · simp only [hC, ite_true]
    have e0 := stageExp_letterPart_mem F hord θ l x (stdOrthonormalBasis ℝ (h x) b)
      (β.1.1 - 1, β.1.2) 0 r hr φ hφ hφp i'
    have e1 := stageExp_letterPart_mem F hord θ l x (stdOrthonormalBasis ℝ (h x) b)
      (β.1.1, β.1.2 - 1) 1 r hr φ hφ hφp i'
    have ek : ∀ k, b1wLetterPart F θ l x (stdOrthonormalBasis ℝ (h x) b) β.1 k r
        (fibreCovDeriv (-θ) k φ) i' ∈ stageTests := fun k =>
      stageExp_letterPart_mem F hord θ l x (stdOrthonormalBasis ℝ (h x) b) β.1 k r hr _ (hD k)
        (isZ2Periodic_fibreCovDeriv hφp _ k) i'
    exact stageTests_sub_mem (stageTests_sub_mem (stageTests_neg_mem
      (stageTests_const_mul_mem _ e0)) (stageTests_const_mul_mem _ e1))
      (stageTests_sum_mem _ _ fun k _ => ek k)
  · simp only [hC, ite_false]
    exact stageTests.zero_mem


end LetterSum

section Main

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D Nw m : ℕ}
  {Ks : Fin Nw → ℕ} {K : ScalarConstants} {g₁ : ℝ}

theorem stageExp_contDiff_of
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) {n : ℕ}
    (hn : (Finset.univ.sup fun l => (F.letters l).order) ≤ n) {f : Vec 2 → ℂ}
    (hf : ContDiff ℝ n f) : ContDiff ℝ (Finset.univ.sup fun l => (F.letters l).order) f :=
  hf.of_le (Finset.sup_le fun l _ => Nat.cast_le.2
    ((Finset.le_sup (f := fun l => (F.letters l).order) (Finset.mem_univ l)).trans hn))

/-- The stage expansion at a good time, for a stage of any level. -/
theorem stageExp_at_time
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁)
    (hslow : ∀ l, (F.letters l).slow = Ks l) (hord : ∀ l, (F.letters l).order ≤ F.J)
    (hM : AmplitudeIdMoments F) (θ : Vec 2) (r : ℝ) (hr : r ∈ Icc F.a F.b)
    (hC1 : ∀ (j : Fin (Nw + 1)) (x : ι) (e : h x) (β : ℕ × ℕ) (φ : Vec 2 → ℂ),
      ContDiff ℝ ((Finset.univ.sup fun l => (F.letters l).order) + 1) φ →
        AVenhance.IsZ2Periodic φ →
      b1wTestedSource F θ j x e β r φ =
        b1wSameLevel θ (F.G r) (F.v r) β e (planeValue (F.u j x r)) φ -
          ((β.1 : ℝ) : ℂ) * b1wFluxPair F θ j x e (β.1 - 1, β.2) 0 r φ -
          ((β.2 : ℝ) : ℂ) * b1wFluxPair F θ j x e (β.1, β.2 - 1) 1 r φ -
          ∑ k : Fin 2, b1wFluxPair F θ j x e β k r (fibreCovDeriv (-θ) k φ))
    (hC2 : ∀ (x : ι) (e : h x) (β₀ : ℕ × ℕ) (k : Fin 2) (ψ : Vec 2 → ℂ),
      b1wFluxPair F θ 0 x e β₀ k r ψ = 0)
    (hC3 : ∀ (j : Fin Nw) (x : ι) (e : h x) (β₀ : ℕ × ℕ) (k : Fin 2) (ψ : Vec 2 → ℂ),
      ContDiff ℝ (Finset.univ.sup fun l => (F.letters l).order) ψ →
        AVenhance.IsZ2Periodic ψ →
      b1wFluxPair F θ j.succ x e β₀ k r ψ = b1wLetterExpansion F θ j x e β₀ k r ψ)
    (i : B1WIndex ι h Nw m Ks) (φ : Vec 2 → ℂ)
    (hφ : ContDiff ℝ ((Finset.univ.sup fun l => (F.letters l).order) + 1) φ)
    (hφp : AVenhance.IsZ2Periodic φ) :
    b1wTestedSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r φ =
      ∑ i' : B1WIndex ι h Nw m Ks, ∫ z in AVenhance.unitCube,
        b1wStageVal F θ i' r z * b1wTestTransform F θ i i' r φ z := by
  have hφ1 : ContDiff ℝ ((Finset.univ.sup fun l => (F.letters l).order) + 1 : ℕ) φ := by
    exact_mod_cast hφ
  have hφ0 : ContDiff ℝ (Finset.univ.sup fun l => (F.letters l).order : ℕ) φ :=
    hφ.of_le (by exact_mod_cast Nat.le_succ _)
  have hφψ := stageExp_contDiff_of F le_rfl hφ0
  have hDc : ∀ k, ContDiff ℝ (Finset.univ.sup fun l => (F.letters l).order : ℕ)
      (fibreCovDeriv (-θ) k φ) := fun k => contDiff_fibreCovDeriv hφ1 (-θ) k
  have hD := fun k => stageExp_contDiff_of F le_rfl (hDc k)
  have hφt : φ ∈ stageTests := ⟨hφ0.continuous, hφp⟩
  have hDt : ∀ k, fibreCovDeriv (-θ) k φ ∈ stageTests := fun k =>
    ⟨(hDc k).continuous, isZ2Periodic_fibreCovDeriv hφp _ k⟩
  have hvt : ∀ k, (fun z => (F.v r z k : ℂ)) ∈ stageTests := fun k =>
    ⟨Complex.continuous_ofReal.comp ((continuous_apply k).comp (F.piece.hvs r).continuous),
      fun n z => by simp only [F.piece.hv.2.2.1 r n z]⟩
  have hG : ∀ i' : B1WIndex ι h Nw m Ks, Integrable (fun y => momentWeight (b1wMom i') y *
      inner ℝ (b1wVec i') (planeValue (F.u i'.1 i'.2.1 r) y)) :=
    fun i' => stageExp_integrable_moment F hM i'.1 i'.2.1 r hr _ _
  rcases i with ⟨j, x, β, b⟩
  have hsame := stageExp_same_sum F hM θ ⟨j, x, β, b⟩ r hr φ hφt hDt hvt
  have hTS := fun i' => stageExp_same_mem θ (F.G r) (F.v r) ⟨j, x, β, b⟩ i' φ hφt hDt hvt
  have hrhs : ∀ (hTL : ∀ i', b1wLetterTransform F θ (⟨j, x, β, b⟩ : B1WIndex ι h Nw m Ks) i' r φ ∈
      stageTests), (∑ i' : B1WIndex ι h Nw m Ks, ∫ z in AVenhance.unitCube,
        b1wStageVal F θ i' r z * b1wTestTransform F θ ⟨j, x, β, b⟩ i' r φ z) =
      (∑ i' : B1WIndex ι h Nw m Ks, stagePair θ (fun y => momentWeight (b1wMom i') y *
        inner ℝ (b1wVec i') (planeValue (F.u i'.1 i'.2.1 r) y))
        (b1wSameTransform θ (F.G r) (F.v r) ⟨j, x, β, b⟩ i' φ)) +
      ∑ i' : B1WIndex ι h Nw m Ks, stagePair θ (fun y => momentWeight (b1wMom i') y *
        inner ℝ (b1wVec i') (planeValue (F.u i'.1 i'.2.1 r) y))
        (b1wLetterTransform F θ ⟨j, x, β, b⟩ i' r φ) := by
    intro hTL
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i' _ => ?_
    exact stagePair_add_test θ (hG i') (hTS i') (hTL i')
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨l, rfl⟩
  · have hLz : ∀ i', b1wLetterTransform F θ (⟨0, x, β, b⟩ : B1WIndex ι h Nw m Ks) i' r φ =
        fun _ => 0 := by
      intro i'
      funext z
      unfold b1wLetterTransform
      exact Finset.sum_eq_zero fun l _ => ite_eq_right_iff.2 fun hc =>
        absurd hc.1.symm (Fin.succ_ne_zero l)
    rw [hrhs (fun i' => by rw [hLz i']; exact stageTests.zero_mem)]
    simp only [hLz, stagePair_zero, Finset.sum_const_zero, add_zero]
    rw [hsame]
    have := hC1 0 x (b1wVec ⟨0, x, β, b⟩) (b1wMom ⟨0, x, β, b⟩) φ hφ hφp
    rw [this]
    simp only [hC2, mul_zero, sub_zero, Finset.sum_const_zero]
  · rw [hrhs (fun i' => stageExp_letterTransform_mem F hord θ l x β b i' r hr φ hφψ hφp hD),
      hsame, stageExp_letter_sum F hslow hord hM θ l x β b r hr φ hφψ hφp hD]
    have := hC1 l.succ x (b1wVec ⟨l.succ, x, β, b⟩) (b1wMom ⟨l.succ, x, β, b⟩) φ hφ hφp
    rw [this]
    rw [hC3 l x _ _ 0 φ hφψ hφp, hC3 l x _ _ 1 φ hφψ hφp]
    simp only [hC3 l x _ _ _ _ (hD _) (isZ2Periodic_fibreCovDeriv hφp _ _)]
    unfold b1wVec b1wMom
    ring

end Main

/-- **The stage expansion of the tested sources.** -/
theorem stageExpansion : StageExpansionStatement.{u, v} := by
  intro K g₁ ι _ h _ _ _ _ _ _ D Nw F θ m Ks hslow hord hLB hM
  filter_upwards [hLB K g₁ F θ hord, ae_restrict_mem measurableSet_Icc] with r hLBr hr
  obtain ⟨c1, c2, c3⟩ := hLBr
  intro i φ hφ hφp
  exact stageExp_at_time F hslow hord hM θ r hr c1 c2 c3 i φ hφ hφp

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open AVRegularity.EntryWeakProofs
namespace AVRegularity.CycleWords.Assembly

/-! # Facts for the stage representation

* The source pairing is conjugate-linear in the test (`cellComplexSource_scalar_test`), so a
  weighted sum of sources is a sum of sources against weighted tests.
* The test transform vanishes on the zero test (`b1wTestTransform_zero_test`), and between stages
  that are not at the same or the next level (`b1wTestTransform_zero_of_level`).
* A zero stage scale propagates to the later levels (`b1wScale_eq_zero_of_le`): the amplitudes
  `A_j` are products over the earlier letters.
* The classical representative of `0` is `0` (`torusHigherClassicalValue_zero`). -/

universe u v

/-- **The source pairing is conjugate-linear in the test.** -/
theorem cellComplexSource_scalar_test (θ : Fin 2 → ℂ) (S : ComplexCellL2)
    (F : Fin 2 → ComplexCellL2) (z : TorusHk 1 ℂ) (c : ℂ) :
    cellComplexSource θ S F (cellH1Scalar c z) = star c * cellComplexSource θ S F z := by
  unfold cellComplexSource cellComplexPair
  have hv := cellH1Scalar_jet_ae c z (valueIndex2 1)
  have h1 : (∫ x in AVenhance.unitCube, S x * star (torusHkValueCLM (cellH1Scalar c z) x)) =
      star c * ∫ x in AVenhance.unitCube, S x * star (torusHkValueCLM z x) := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hv] with x hx
    change S x * star ((cellH1Scalar c z).val (valueIndex2 1) x) =
      star c * (S x * star (z.val (valueIndex2 1) x))
    rw [hx, star_mul]
    ring
  have h2 : ∀ j : Fin 2,
      (∫ x in AVenhance.unitCube, F j x *
        star (cellShiftedDerivativeCLM (fun i => star (θ i)) j (cellH1Scalar c z) x)) =
      star c * ∫ x in AVenhance.unitCube, F j x *
        star (cellShiftedDerivativeCLM (fun i => star (θ i)) j z x) := by
    intro j
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [cellH1Scalar_shift_ae (fun i => star (θ i)) c z j] with x hx
    rw [hx, star_mul]
    ring
  rw [h1, Finset.sum_congr rfl fun j _ => h2 j, ← Finset.mul_sum, mul_sub]

/-- The classical representative of `0` is `0`. -/
theorem torusHigherClassicalValue_zero (N : ℕ) (hN : 2 ≤ N) :
    torusHigherClassicalValue N (0 : TorusHk N ℂ) = 0 := by
  have hz : ∀ L : ℂ →L[ℝ] ℝ, mapTorusHk L (0 : TorusHk N ℂ) = 0 := by
    intro L
    rw [← mapTorusHkCLM_apply, map_zero]
  have hl : realClassicalLift N (0 : TorusHk N ℝ) = 0 := by
    have h := realClassicalLift_add N hN (0 : TorusHk N ℝ) 0
    rw [add_zero] at h
    funext x
    have hx := congrFun h x
    simp only [Pi.add_apply] at hx
    simp only [Pi.zero_apply]
    linarith
  funext x
  unfold torusHigherClassicalValue
  rw [hz, hz, hl]
  simp

section Index

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- The covariant derivative of `0` is `0`. -/
theorem fibreCovDeriv_zero (θ : Vec 2) (k : Fin 2) :
    fibreCovDeriv θ k (fun _ => (0 : ℂ)) = fun _ => 0 := by
  funext z
  simp [fibreCovDeriv]

theorem fibreCovPow_zero (θ : Vec 2) (b : ℕ × ℕ) :
    fibreCovPow θ b (fun _ => (0 : ℂ)) = fun _ => 0 := by
  unfold fibreCovPow
  rw [Function.iterate_fixed (fibreCovDeriv_zero θ 1),
    Function.iterate_fixed (fibreCovDeriv_zero θ 0)]

/-- **The test transform of the zero test vanishes.** -/
theorem b1wTestTransform_zero_test {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (i i' : B1WIndex ι h Nw m Ks) (r : ℝ) :
    b1wTestTransform F θ i i' r (fun _ => 0) = 0 := by
  funext z
  have hc : ∀ (c : Vec 2 → ℂ), (fun z' => c z' * (0 : ℂ)) = fun _ => 0 := fun c => by
    funext z'
    simp
  simp only [b1wTestTransform, b1wSameTransform, b1wLetterTransform, b1wLetterPart,
    fibreCovDeriv_zero, hc, fibreCovPow_zero]
  simp

/-- **The test transform vanishes away from the same and the next level.** -/
theorem b1wTestTransform_zero_of_level {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (i i' : B1WIndex ι h Nw m Ks) (hne : i'.1 ≠ i.1)
    (hl : ∀ l : Fin Nw, ¬ (i.1 = l.succ ∧ i'.1 = l.castSucc)) (r : ℝ) (φ : Vec 2 → ℂ) :
    b1wTestTransform F θ i i' r φ = 0 := by
  funext z
  simp only [b1wTestTransform, b1wSameTransform, b1wLetterTransform, hne, hl, ite_false,
    Finset.sum_const_zero, add_zero, Pi.zero_apply]

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- The amplitude of a later level vanishes with that of an earlier one. -/
theorem b1wAmp_eq_zero_of_le (ηg : ℝ) (letters : Fin Nw → CycleLetter ι h D)
    {j j' : Fin (Nw + 1)} (hjj : j' ≤ j) (h0 : b1wAmp ηg letters j' = 0) :
    b1wAmp ηg letters j = 0 := by
  unfold b1wAmp at h0 ⊢
  obtain ⟨l, -, hl⟩ := Finset.prod_eq_zero_iff.1 h0
  refine Finset.prod_eq_zero (Finset.mem_univ l) ?_
  have hlt : l.val < j'.val := by
    by_contra hc
    simp only [hc, ite_false] at hl
    exact one_ne_zero hl
  simp only [hlt, ite_true] at hl
  simp only [lt_of_lt_of_le hlt (Fin.le_iff_val_le_val.1 hjj), ite_true]
  exact hl

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- **A zero stage scale propagates to the later levels.** -/
theorem b1wScale_eq_zero_of_le (π : ι → ℝ) {ϖ : ℝ} (ηg : ℝ)
    (letters : Fin Nw → CycleLetter ι h D) (hπ : ∀ x, 0 < π x) (hϖ : 0 < ϖ)
    (i i' : B1WIndex ι h Nw m Ks) (hjj : i'.1 ≤ i.1)
    (h0 : b1wScale π ϖ ηg letters i' = 0) : b1wScale π ϖ ηg letters i = 0 := by
  unfold b1wScale at h0 ⊢
  rw [Complex.ofReal_eq_zero] at h0 ⊢
  have hA : b1wAmp ηg letters i'.1 = 0 := by
    rcases mul_eq_zero.1 h0 with h1 | h1
    · exfalso
      have hp : 0 < π i'.2.1 ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos (hπ _) _
      have hf : 0 < ((i'.2.2.1.1.1.factorial * i'.2.2.1.1.2.factorial : ℕ) : ℝ) := by positivity
      have : 0 < π i'.2.1 ^ (-(1 / 2 : ℝ)) * ϖ ^ (i'.2.2.1.1.1 + i'.2.2.1.1.2) /
          ((i'.2.2.1.1.1.factorial * i'.2.2.1.1.2.factorial : ℕ) : ℝ) := by positivity
      linarith
    · exact inv_eq_zero.1 h1
  rw [b1wAmp_eq_zero_of_le ηg letters hjj hA, inv_zero, mul_zero]

end Index

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! # The terminal output relation

The output stage `out β` contains the stages `(N_w, x, β, e)` for every component `x` and basis
vector `e`. The cell mean of each is its scale times the phase integral
`∫ e^{-iθ·y} y^β ⟨e, u_N(b)⟩` (`integral_phase_eq_cell_planeBlochC`), and Parseval in `h x` with
`(∫ cos F)² + (∫ sin F)² = |∫ e^{-iθ·y} F|²` identifies the squared moment amplitude with
`(β! A_N)²` times the sum of the squared cell means over these stages. -/

section
universe u v

/-- The cell mean of a rescaled cell trace is the scale times the phase integral. -/
theorem toStage_value (D : ℝ → RawJet2 1 ℂ) (t : ℝ) (θ : Vec 2) {g : Vec 2 → ℝ}
    (hg : Integrable g)
    (hcell : cellValue D t =ᵐ[volume.restrict AVenhance.unitCube] planeBlochC θ g)
    (hmem : MemLp (cellValue D t) 2 (volume.restrict AVenhance.unitCube)) (c : ℂ) :
    cellComplexPair (cellScalarCLM c (cellRawTrace D t)) (cellConstantCLM 1) =
      c * ∫ y, Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) * (g y : ℂ) := by
  rw [cellComplexPair_one, integral_phase_eq_cell_planeBlochC θ hg]
  unfold cellMean
  rw [integral_congr_ae (cellScalarCLM_ae c (cellRawTrace D t)), integral_const_mul]
  congr 1
  exact (integral_congr_ae (cellRawTrace_ae D t hmem)).trans (integral_congr_ae hcell)

theorem toLevelMoments_last {Nw : ℕ} (m : ℕ) (Ks : Fin Nw → ℕ) :
    b1wLevelMoments m Ks (Fin.last Nw) = m := by
  unfold b1wLevelMoments
  rw [Finset.sum_eq_zero fun l _ => by simp [l.isLt], add_zero]

theorem toRpow_neg_half_sq {p : ℝ} (hp : 0 < p) : (p ^ (-(1 / 2 : ℝ))) ^ 2 = p⁻¹ := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]
  norm_num
  exact Real.rpow_neg_one p

theorem toOfReal_comp {p a b : ℝ} (hp : 0 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.ofReal p * (ENNReal.ofReal a + ENNReal.ofReal b) = ENNReal.ofReal (p * (a + b)) := by
  rw [ENNReal.ofReal_mul hp, ENNReal.ofReal_add ha hb]

/-- **The terminal output relation.** -/
theorem terminalOutput : TerminalOutputStatement.{u, v} := by
  intro K g₁ ι _ h _ _ _ _ _ _ D Nw F m Ks θ Dθ hcell hmem hmom hA β hβ
  classical
  set A := b1wAmp F.ηg F.letters (Fin.last Nw) with hAdef
  have hβ' : β ∈ momentIndices (b1wLevelMoments m Ks (Fin.last Nw)) := by
    rw [toLevelMoments_last]; exact hβ
  let φ : (Σ x : ι, Fin (Module.finrank ℝ (h x))) → B1WIndex ι h Nw m Ks :=
    fun p => ⟨Fin.last Nw, p.1, (⟨β, hβ'⟩, p.2)⟩
  let xs : B1WIndex ι h Nw m Ks → ℂ := fun i => cellComplexPair
    (cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i) (cellRawTrace (Dθ i) F.b))
    (cellConstantCLM 1)
  have hb : F.b ∈ Icc F.a F.b := ⟨F.ordered, le_rfl⟩
  have hm : ∀ x, Integrable fun y => momentWeight β y • planeValue (F.u (Fin.last Nw) x F.b) y :=
    fun x => hmom (Fin.last Nw) x F.b hb m β hβ
  have hg : ∀ x (e : Fin (Module.finrank ℝ (h x))), Integrable fun y => momentWeight β y *
      inner ℝ (stdOrthonormalBasis ℝ (h x) e) (planeValue (F.u (Fin.last Nw) x F.b) y) := by
    intro x e
    have := (innerSL ℝ (stdOrthonormalBasis ℝ (h x) e)).integrable_comp (hm x)
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp
  let P : ∀ x, Fin (Module.finrank ℝ (h x)) → ℂ := fun x e =>
    ∫ y, Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) * ((momentWeight β y *
      inner ℝ (stdOrthonormalBasis ℝ (h x) e)
        (planeValue (F.u (Fin.last Nw) x F.b) y) : ℝ) : ℂ)
  let r : ι → ℝ := fun x => F.π x ^ (-(1 / 2 : ℝ)) * F.ϖ ^ (β.1 + β.2) /
    ((β.1.factorial * β.2.factorial : ℕ) : ℝ) * A⁻¹
  have hxs : ∀ p : (Σ x : ι, Fin (Module.finrank ℝ (h x))), xs (φ p) = (r p.1 : ℂ) * P p.1 p.2 :=
    fun p => toStage_value (Dθ (φ p)) F.b θ (hg p.1 p.2) (hcell (φ p)) (hmem (φ p)) _
  have hfac : (((β.1.factorial * β.2.factorial : ℕ) : ℝ)) ≠ 0 := by positivity
  have hA0 : A ≠ 0 := hA.ne'
  have hr : ∀ x, (((β.1.factorial * β.2.factorial : ℕ) : ℝ) * A) ^ 2 * r x ^ 2 =
      (F.π x)⁻¹ * F.ϖ ^ (2 * (β.1 + β.2)) := by
    intro x
    have hp := toRpow_neg_half_sq (F.piece.hπ x)
    have key : (((β.1.factorial * β.2.factorial : ℕ) : ℝ) * A) ^ 2 * r x ^ 2 =
        (F.π x ^ (-(1 / 2 : ℝ))) ^ 2 * (F.ϖ ^ (β.1 + β.2)) ^ 2 *
          ((((β.1.factorial * β.2.factorial : ℕ) : ℝ)) ^ 2 * A ^ 2 *
            ((((β.1.factorial * β.2.factorial : ℕ) : ℝ)) ^ 2)⁻¹ * (A ^ 2)⁻¹) := by
      simp only [r]
      ring
    have h1 : ((((β.1.factorial * β.2.factorial : ℕ) : ℝ)) ^ 2 * A ^ 2 *
        ((((β.1.factorial * β.2.factorial : ℕ) : ℝ)) ^ 2)⁻¹ * (A ^ 2)⁻¹) = 1 := by
      field_simp
    rw [key, h1, hp, mul_one, ← pow_mul, mul_comm (β.1 + β.2) 2]
  have hcomp : ∀ x, (F.π x)⁻¹ *
      (‖∫ y, (Real.cos (vecDot θ y) * (F.ϖ * y 0) ^ β.1 * (F.ϖ * y 1) ^ β.2) •
          planeValue (F.u (Fin.last Nw) x F.b) y‖ ^ 2 +
        ‖∫ y, (Real.sin (vecDot θ y) * (F.ϖ * y 0) ^ β.1 * (F.ϖ * y 1) ^ β.2) •
          planeValue (F.u (Fin.last Nw) x F.b) y‖ ^ 2) =
      (((β.1.factorial * β.2.factorial : ℕ) : ℝ) * A) ^ 2 *
        ∑ e, ‖xs (φ ⟨x, e⟩)‖ ^ 2 := by
    intro x
    rw [toComponent_identity F.ϖ β θ _ (hm x), Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hxs ⟨x, e⟩]
    simp only
    have h2 : (|r x| * ‖P x e‖) ^ 2 = r x ^ 2 * ‖P x e‖ ^ 2 := by rw [mul_pow, sq_abs]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, h2, ← mul_assoc
      ((((β.1.factorial * β.2.factorial : ℕ) : ℝ) * A) ^ 2), hr x]
    change _ = _ * ‖P x e‖ ^ 2
    ring
  have hinj : Function.Injective φ := by
    intro p q hpq
    obtain ⟨x, e⟩ := p
    obtain ⟨y, e'⟩ := q
    simp only [φ, Sigma.mk.injEq, heq_eq_eq, true_and] at hpq
    obtain ⟨rfl, he⟩ := hpq
    rw [(Prod.mk.inj (eq_of_heq he)).2]
  have hsub : ∑ p : (Σ x : ι, Fin (Module.finrank ℝ (h x))), ‖xs (φ p)‖ ^ 2 ≤
      ∑ i ∈ stageSet b1wSt (b1wOut Nw Ks β), ‖xs i‖ ^ 2 := by
    rw [← Finset.sum_image (f := fun i => ‖xs i‖ ^ 2) (s := Finset.univ) (g := φ)
      (fun p _ q _ hpq => hinj hpq)]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hi
      simp only [stageSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (b1wSt_eq_out_iff (φ p) β).mpr ⟨rfl, rfl⟩
    · intro i _ _
      positivity
  have hsig : ∑ x, ∑ e, ‖xs (φ ⟨x, e⟩)‖ ^ 2 =
      ∑ p : (Σ x : ι, Fin (Module.finrank ℝ (h x))), ‖xs (φ p)‖ ^ 2 :=
    (Fintype.sum_sigma (fun p : (Σ x : ι, Fin (Module.finrank ℝ (h x))) => ‖xs (φ p)‖ ^ 2)).symm
  set c : ℝ := (((β.1.factorial * β.2.factorial : ℕ) : ℝ) * A) with hc
  have hc0 : 0 ≤ c := by positivity
  unfold momentAmpNorm
  rw [Finset.sum_congr rfl fun x _ => toOfReal_comp (inv_nonneg.2 (F.piece.hπ x).le)
    (sq_nonneg _) (sq_nonneg _), ← ENNReal.ofReal_sum_of_nonneg (fun x _ =>
      mul_nonneg (inv_nonneg.2 (F.piece.hπ x).le) (add_nonneg (sq_nonneg _) (sq_nonneg _))),
    Finset.sum_congr rfl fun x _ => hcomp x, ← Finset.mul_sum, hsig,
    ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun p _ =>
      sq_nonneg _)) (by norm_num)]
  apply ENNReal.ofReal_le_ofReal
  unfold stageNorm
  rw [← Real.sqrt_eq_rpow]
  calc Real.sqrt (c ^ 2 * ∑ p : (Σ x : ι, Fin (Module.finrank ℝ (h x))), ‖xs (φ p)‖ ^ 2)
      ≤ Real.sqrt (c ^ 2 * ∑ i ∈ stageSet b1wSt (b1wOut Nw Ks β), ‖xs i‖ ^ 2) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hsub (sq_nonneg _))
    _ = c * Real.sqrt (∑ i ∈ stageSet b1wSt (b1wOut Nw Ks β), ‖xs i‖ ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc0]
end

/-! # The data of the stages

At the start `a` of the piece the rescaled stage values are
`W(0, x, β, e)(a) = π_x^{-1/2} ϖ^{|β|}/β! · B_θ(y^β⟨e, φ_x⟩)` at level `0`, and `0` above
(`b1w_level_succ_zero`). Summed over the components and an orthonormal basis,
`∑_{x,e} ‖W(0,x,β,e)(a)‖² = (ϖ^{|β|}/β! · ‖∂^β B φ‖)²` (`b1w_level_zero_norms`, the level-0 identity
through `levelZero_sum_sq`), and the Bloch fibre derivative norm is finite. The data of the stages
are then `b1wDataTerm` (`ϖ^{|β|}/β!` times that norm), and `b1wDd C k` sums the data of the moments
whose level-0 stage is at most `k`. It is monotone, it dominates the stage norm of the values at `a`
(`b1w_stage_data_le`, with `C = 1`), and at the output stage `out β` it is at most
`C · datumJets(|β| + ∑ K_s)` (`b1wDd_out_le`). -/

section
universe u v

/-- The datum term of a moment: `ϖ^{|β|}/β! · ‖∂_θ^β B_θ φ‖`. -/
def b1wDataTerm {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (π : ι → ℝ) (ϖ : ℝ) (φ : ∀ x, Vec 2 → h x) (θ : Vec 2)
    (β : ℕ × ℕ) : ℝ :=
  ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ) *
    (blochFibreDerivNorm π (fun _ => 1) β φ θ).toReal

theorem b1wDataTerm_nonneg {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] (π : ι → ℝ) {ϖ : ℝ} (hϖ : 0 ≤ ϖ)
    (φ : ∀ x, Vec 2 → h x) (θ : Vec 2) (β : ℕ × ℕ) : 0 ≤ b1wDataTerm π ϖ φ θ β := by
  unfold b1wDataTerm
  positivity

/-- The level-0 scale: `|c|² = π_x⁻¹ (ϖ^{|β|}/β!)²`. -/
theorem b1wScale_level_zero_sq {ι : Type u} {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] {D Nw m : ℕ} {Ks : Fin Nw → ℕ} (π : ι → ℝ) (ϖ ηg : ℝ)
    (letters : Fin Nw → CycleLetter ι h D) (i : B1WIndex ι h Nw m Ks) (hi : i.1 = 0)
    (hπ : 0 < π i.2.1) :
    ‖b1wScale π ϖ ηg letters i‖ ^ 2 = (π i.2.1)⁻¹ *
      (ϖ ^ (i.2.2.1.1.1 + i.2.2.1.1.2) /
        ((i.2.2.1.1.1.factorial * i.2.2.1.1.2.factorial : ℕ) : ℝ)) ^ 2 := by
  have hA : b1wAmp ηg letters i.1 = 1 := by
    rw [hi]
    unfold b1wAmp
    exact Finset.prod_eq_one fun l _ => by simp
  unfold b1wScale
  rw [hA, inv_one, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_div_assoc, mul_pow]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hπ.le]
  norm_num
  exact Real.rpow_neg_one _

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D Nw : ℕ}

/-- **The level-0 stage values at the start**, summed over the components and the basis. -/
theorem b1w_level_zero_norms (hL : LevelZeroDataStatement.{v}) {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (m : ℕ)
    (Ks : Fin Nw → ℕ) (θ : Vec 2) (Dθ : B1WIndex ι h Nw m Ks → ℝ → RawJet2 1 ℂ)
    (hval : ∀ i, ∀ t ∈ Icc F.a F.b, cellValue (Dθ i) t =ᵐ[volume.restrict AVenhance.unitCube]
      planeBlochC θ (fun y => momentWeight i.2.2.1.1 y *
        inner ℝ (stdOrthonormalBasis ℝ (h i.2.1) i.2.2.2) (planeValue (F.u i.1 i.2.1 t) y)))
    (hmem : ∀ i, ∀ t ∈ Icc F.a F.b,
      MemLp (cellValue (Dθ i) t) 2 (volume.restrict AVenhance.unitCube))
    (β : ℕ × ℕ) (hβ : β ∈ momentIndices (b1wLevelMoments m Ks 0)) :
    blochFibreDerivNorm F.π (fun _ => 1) β F.φ θ ≠ ⊤ ∧
    ∑ x, ∑ e : Fin (Module.finrank ℝ (h x)),
        ‖cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters
            (⟨0, x, ⟨β, hβ⟩, e⟩ : B1WIndex ι h Nw m Ks))
          (cellRawTrace (Dθ ⟨0, x, ⟨β, hβ⟩, e⟩) F.a)‖ ^ 2 =
      b1wDataTerm F.π F.ϖ F.φ θ β ^ 2 := by
  have ha : F.a ∈ Icc F.a F.b := ⟨le_rfl, F.ordered⟩
  -- each squared trace norm is the cell integral of the datum's Bloch part
  have htr : ∀ x (e : Fin (Module.finrank ℝ (h x))),
      ENNReal.ofReal (‖cellRawTrace (Dθ ⟨0, x, ⟨β, hβ⟩, e⟩) F.a‖ ^ 2) =
        ∫⁻ z in AVenhance.unitCube, ‖planeBlochC θ (fun y => momentWeight β y *
          inner ℝ (stdOrthonormalBasis ℝ (h x) e) (F.φ x y)) z‖ₑ ^ 2 := by
    intro x e
    rw [cellL2_ofReal_norm_sq]
    refine lintegral_congr_ae ?_
    filter_upwards [cellRawTrace_ae _ F.a (hmem _ F.a ha), hval ⟨0, x, ⟨β, hβ⟩, e⟩ F.a ha,
      frame_initial_level_zero F θ x (stdOrthonormalBasis ℝ (h x) e) β] with z h1 h2 h3
    rw [h1, h2, h3]
  have hsum := levelZero_sum_sq hL F.π F.φ F.compact β θ
  -- the weighted sum of the squared trace norms, in `ℝ≥0∞`
  have hE : ∑ x, ENNReal.ofReal ((F.π x)⁻¹) * ∑ e : Fin (Module.finrank ℝ (h x)),
      ENNReal.ofReal (‖cellRawTrace (Dθ ⟨0, x, ⟨β, hβ⟩, e⟩) F.a‖ ^ 2) =
        blochFibreDerivNorm F.π (fun _ => 1) β F.φ θ ^ 2 := by
    rw [← hsum]
    exact Finset.sum_congr rfl fun x _ => by simp only [htr]
  have hR : ∑ x, ENNReal.ofReal ((F.π x)⁻¹) * ∑ e : Fin (Module.finrank ℝ (h x)),
      ENNReal.ofReal (‖cellRawTrace (Dθ ⟨0, x, ⟨β, hβ⟩, e⟩) F.a‖ ^ 2) =
        ENNReal.ofReal (∑ x, (F.π x)⁻¹ * ∑ e : Fin (Module.finrank ℝ (h x)),
          ‖cellRawTrace (Dθ ⟨0, x, ⟨β, hβ⟩, e⟩) F.a‖ ^ 2) := by
    have hπ := F.piece.hπ
    rw [ENNReal.ofReal_sum_of_nonneg fun x _ => by have := hπ x; positivity]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ENNReal.ofReal_mul (by have := hπ x; positivity),
      ENNReal.ofReal_sum_of_nonneg fun e _ => sq_nonneg _]
  have hfin : blochFibreDerivNorm F.π (fun _ => 1) β F.φ θ ≠ ⊤ := by
    intro htop
    rw [hR, htop] at hE
    exact ENNReal.ofReal_ne_top (hE.trans (by simp))
  refine ⟨hfin, ?_⟩
  have hreal : ∑ x, (F.π x)⁻¹ * ∑ e : Fin (Module.finrank ℝ (h x)),
      ‖cellRawTrace (Dθ ⟨0, x, ⟨β, hβ⟩, e⟩) F.a‖ ^ 2 =
        (blochFibreDerivNorm F.π (fun _ => 1) β F.φ θ).toReal ^ 2 := by
    rw [hR] at hE
    have := congrArg ENNReal.toReal hE
    rw [ENNReal.toReal_ofReal (Finset.sum_nonneg fun x _ => by
      have := F.piece.hπ x; positivity), ENNReal.toReal_pow] at this
    exact this
  unfold b1wDataTerm
  rw [mul_pow, ← hreal, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [cellScalarCLM_smul, norm_smul, mul_pow,
    b1wScale_level_zero_sq F.π F.ϖ F.ηg F.letters _ rfl (F.piece.hπ x)]
  ring

/-- **The higher-level stage values vanish at the start.** -/
theorem b1w_level_succ_zero {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (m : ℕ)
    (Ks : Fin Nw → ℕ) (θ : Vec 2) (Dθ : B1WIndex ι h Nw m Ks → ℝ → RawJet2 1 ℂ)
    (hval : ∀ i, ∀ t ∈ Icc F.a F.b, cellValue (Dθ i) t =ᵐ[volume.restrict AVenhance.unitCube]
      planeBlochC θ (fun y => momentWeight i.2.2.1.1 y *
        inner ℝ (stdOrthonormalBasis ℝ (h i.2.1) i.2.2.2) (planeValue (F.u i.1 i.2.1 t) y)))
    (hmem : ∀ i, ∀ t ∈ Icc F.a F.b,
      MemLp (cellValue (Dθ i) t) 2 (volume.restrict AVenhance.unitCube))
    (i : B1WIndex ι h Nw m Ks) (hi : i.1 ≠ 0) : cellRawTrace (Dθ i) F.a = 0 := by
  have ha : F.a ∈ Icc F.a F.b := ⟨le_rfl, F.ordered⟩
  refine Lp.ext ?_
  filter_upwards [cellRawTrace_ae _ F.a (hmem i F.a ha), hval i F.a ha,
    frame_initial_level_succ F θ i.1 hi i.2.1 (stdOrthonormalBasis ℝ (h i.2.1) i.2.2.2)
      i.2.2.1.1, Lp.coeFn_zero ℂ 2 (volume.restrict AVenhance.unitCube)] with z h1 h2 h3 h4
  rw [h1, h2, h3, h4]

end Frame

/-- `∑ a_i² ≤ (∑ a_i)²` for nonnegative terms. -/
theorem sum_sq_le_sq_sum {α : Type*} (s : Finset α) (a : α → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) :
    ∑ i ∈ s, a i ^ 2 ≤ (∑ i ∈ s, a i) ^ 2 := by
  rw [sq, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [sq]
  exact mul_le_mul_of_nonneg_left (Finset.single_le_sum ha hi) (ha i hi)

/-- The stage data: `C` times the data of the moments whose level-0 stage is at most `k`. -/
def b1wDd {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (Nw N : ℕ) (π : ι → ℝ) (ϖ : ℝ) (φ : ∀ x, Vec 2 → h x)
    (θ : Vec 2) (C : ℝ) (k : ℕ) : ℝ :=
  C * ∑ β ∈ momentIndices N,
    if (β.1 + β.2) * (Nw + 1) ≤ k then b1wDataTerm π ϖ φ θ β else 0

section Dd

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

theorem b1wDd_nonneg (Nw N : ℕ) (π : ι → ℝ) {ϖ : ℝ} (hϖ : 0 ≤ ϖ) (φ : ∀ x, Vec 2 → h x)
    (θ : Vec 2) {C : ℝ} (hC : 0 ≤ C) (k : ℕ) : 0 ≤ b1wDd Nw N π ϖ φ θ C k := by
  unfold b1wDd
  refine mul_nonneg hC (Finset.sum_nonneg fun β _ => ?_)
  split_ifs
  · exact b1wDataTerm_nonneg π hϖ φ θ β
  · exact le_rfl

theorem b1wDd_mono (Nw N : ℕ) (π : ι → ℝ) {ϖ : ℝ} (hϖ : 0 ≤ ϖ) (φ : ∀ x, Vec 2 → h x)
    (θ : Vec 2) {C : ℝ} (hC : 0 ≤ C) : Monotone (b1wDd Nw N π ϖ φ θ C) := by
  intro k k' hk
  unfold b1wDd
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun β _ => ?_) hC
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd (h1.trans hk) h2
  · exact b1wDataTerm_nonneg π hϖ φ θ β
  · exact le_rfl

/-- **The data at the output stage** are at most `C · datumJets(|β| + ∑ K_s)`, when the Bloch
fibre derivative norms of the moments up to `N` are finite. -/
theorem b1wDd_out_le {Nw N : ℕ} (Ks : Fin Nw → ℕ) (π : ι → ℝ) {ϖ : ℝ} (hϖ : 0 ≤ ϖ)
    (φ : ∀ x, Vec 2 → h x) (θ : Vec 2) {C : ℝ} (hC : 0 ≤ C) (β : ℕ × ℕ)
    (hβN : β.1 + β.2 + ∑ l, Ks l ≤ N)
    (hfin : ∀ α ∈ momentIndices N, blochFibreDerivNorm π (fun _ => 1) α φ θ ≠ ⊤) :
    ENNReal.ofReal (b1wDd Nw N π ϖ φ θ C (b1wOut Nw Ks β)) ≤
      ENNReal.ofReal C * datumJets π ϖ (β.1 + β.2 + ∑ l, Ks l) φ θ := by
  set n := β.1 + β.2 + ∑ l, Ks l with hn
  -- the moments seen by the output stage have degree at most `n`
  have hdeg : ∀ α ∈ momentIndices N, (α.1 + α.2) * (Nw + 1) ≤ b1wOut Nw Ks β →
      α ∈ momentIndices n := by
    intro α _ hα
    unfold b1wOut at hα
    rw [← hn] at hα
    have hle : α.1 + α.2 ≤ n := by
      by_contra hc
      push Not at hc
      have h1 : (n + 1) * (Nw + 1) ≤ (α.1 + α.2) * (Nw + 1) := Nat.mul_le_mul_right _ hc
      have h2 : (n + 1) * (Nw + 1) = n * (Nw + 1) + Nw + 1 := by ring
      omega
    unfold momentIndices
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  have hsum : ∑ α ∈ momentIndices N,
      (if (α.1 + α.2) * (Nw + 1) ≤ b1wOut Nw Ks β then b1wDataTerm π ϖ φ θ α else 0) ≤
        ∑ α ∈ momentIndices n, b1wDataTerm π ϖ φ θ α := by
    rw [← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun α hα => ?_)
      fun α _ _ => b1wDataTerm_nonneg π hϖ φ θ α
    obtain ⟨hαN, hαk⟩ := Finset.mem_filter.1 hα
    exact hdeg α hαN hαk
  have hnN : ∀ α ∈ momentIndices n, α ∈ momentIndices N := by
    intro α hα
    unfold momentIndices at hα ⊢
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hα ⊢
    omega
  unfold b1wDd
  rw [ENNReal.ofReal_mul hC]
  refine mul_le_mul' le_rfl ?_
  refine (ENNReal.ofReal_le_ofReal hsum).trans (le_of_eq ?_)
  unfold datumJets
  rw [ENNReal.ofReal_sum_of_nonneg fun α _ => b1wDataTerm_nonneg π hϖ φ θ α]
  refine Finset.sum_congr rfl fun α hα => ?_
  unfold b1wDataTerm
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal (hfin α (hnN α hα))]

end Dd

section StageBound

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D Nw : ℕ}

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem b1wSt_level_zero {m : ℕ} {Ks : Fin Nw → ℕ} (x : ι)
    (β : {β : ℕ × ℕ // β ∈ momentIndices (b1wLevelMoments m Ks 0)})
    (e : Fin (Module.finrank ℝ (h x))) :
    b1wSt (⟨0, x, (β, e)⟩ : B1WIndex ι h Nw m Ks) = (β.1.1 + β.1.2) * (Nw + 1) := by
  unfold b1wSt b1wDeg
  simp [b1wPrefix_zero]

/-- **The stage values at the start are dominated by the data**: for every stage `k`,
`(∑_{st i = k} ‖W i(a)‖²)^{1/2} ≤ b1wDd … 1 k`. -/
theorem b1w_stage_data_le (hL : LevelZeroDataStatement.{v}) {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (m : ℕ)
    (Ks : Fin Nw → ℕ) (θ : Vec 2) (Dθ : B1WIndex ι h Nw m Ks → ℝ → RawJet2 1 ℂ)
    (hval : ∀ i, ∀ t ∈ Icc F.a F.b, cellValue (Dθ i) t =ᵐ[volume.restrict AVenhance.unitCube]
      planeBlochC θ (fun y => momentWeight i.2.2.1.1 y *
        inner ℝ (stdOrthonormalBasis ℝ (h i.2.1) i.2.2.2) (planeValue (F.u i.1 i.2.1 t) y)))
    (hmem : ∀ i, ∀ t ∈ Icc F.a F.b,
      MemLp (cellValue (Dθ i) t) 2 (volume.restrict AVenhance.unitCube))
    (hϖ : 0 ≤ F.ϖ) (k : ℕ) :
    Real.sqrt (∑ i ∈ stageSet b1wSt k,
        ‖cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i) (cellRawTrace (Dθ i) F.a)‖ ^ 2) ≤
      b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1 k := by
  set W : B1WIndex ι h Nw m Ks → ComplexCellL2 := fun i =>
    cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i) (cellRawTrace (Dθ i) F.a) with hW
  set N := b1wLevelMoments m Ks 0 with hN
  set a : {β : ℕ × ℕ // β ∈ momentIndices N} → ℝ := fun β =>
    if (β.1.1 + β.1.2) * (Nw + 1) = k then b1wDataTerm F.π F.ϖ F.φ θ β.1 else 0 with ha
  have ha0 : ∀ β, 0 ≤ a β := fun β => by
    simp only [ha]
    split_ifs
    · exact b1wDataTerm_nonneg F.π hϖ F.φ θ β.1
    · exact le_rfl
  -- the higher levels vanish
  have hsucc : ∀ (j : Fin Nw) y, W ⟨j.succ, y⟩ = 0 := by
    intro j y
    simp only [hW]
    rw [b1w_level_succ_zero F m Ks θ Dθ hval hmem ⟨j.succ, y⟩ (Fin.succ_ne_zero j), map_zero]
  -- regroup the stage by moments
  have hgroup : ∑ i ∈ stageSet b1wSt k, ‖W i‖ ^ 2 = ∑ β : {β : ℕ × ℕ // β ∈ momentIndices N},
      a β ^ 2 := by
    unfold stageSet
    rw [Finset.sum_filter, Fintype.sum_sigma, Fin.sum_univ_succ]
    have hz : ∑ j : Fin Nw, ∑ y, (if b1wSt (⟨j.succ, y⟩ : B1WIndex ι h Nw m Ks) = k then
        ‖W ⟨j.succ, y⟩‖ ^ 2 else 0) = 0 :=
      Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun y _ => by
        rw [hsucc j y, norm_zero]
        simp
    rw [hz, add_zero, Fintype.sum_sigma]
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [b1wSt_level_zero]
    by_cases hc : (β.1.1 + β.1.2) * (Nw + 1) = k
    · simp only [hc, ite_true, ha]
      exact (b1w_level_zero_norms hL F m Ks θ Dθ hval hmem β.1 β.2).2
    · simp [hc, ha]
  have hsq : ∑ β : {β : ℕ × ℕ // β ∈ momentIndices N}, a β ^ 2 ≤
      (∑ β : {β : ℕ × ℕ // β ∈ momentIndices N}, a β) ^ 2 :=
    sum_sq_le_sq_sum _ a fun β _ => ha0 β
  rw [hgroup]
  refine (Real.sqrt_le_sqrt hsq).trans ?_
  rw [Real.sqrt_sq (Finset.sum_nonneg fun β _ => ha0 β)]
  unfold b1wDd
  rw [one_mul]
  have hcoe : ∑ β : {β : ℕ × ℕ // β ∈ momentIndices N}, a β = ∑ β ∈ momentIndices N,
      (if (β.1 + β.2) * (Nw + 1) = k then b1wDataTerm F.π F.ϖ F.φ θ β else 0) :=
    Finset.sum_coe_sort (momentIndices N) fun β =>
      if (β.1 + β.2) * (Nw + 1) = k then b1wDataTerm F.π F.ϖ F.φ θ β else 0
  rw [hcoe]
  refine Finset.sum_le_sum fun β _ => ?_
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd h1.le h2
  · exact b1wDataTerm_nonneg F.π hϖ F.φ θ β
  · exact le_rfl

end StageBound
end

end AVRegularity.CycleWords.Assembly
end
