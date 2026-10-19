-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.TransformBoundLetterBlocks
public import AVRegularity.CycleWords.MixedWords.FactorOfMomentsRepresentation
import AVRegularity.CycleWords.MixedWords.AmplitudePlancherel
import AVRegularity.CycleWords.MixedWords.B1WData
import AVRegularity.CycleWords.MixedWords.AfwCrude
import AVRegularity.CycleWords.MixedWords.BlochContinuity

section
/-! # the letter operators and the letter transform bound

`b1wLetterTransform` is rewritten (`ratio_star_letterTransform`) as the family `letterGfam` of
`TransformBoundLetterBlocks`; the block operators `Top` of a pair of components and moments
come from `letterBlock_exists`, and `T i i'` is `Top` at the basis indices of the stages.  The sums
over the stages of a block are reduced to sums over the basis indices (`mk` is injective).  This proves
`LetterOpsStatement` and hence `letterTransformBoundAE`. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
  AVRegularity.CycleEvolution

namespace AVRegularity.CycleWords.Assembly

universe u v

section Reshape

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D Nw m : ℕ}
  {Ks : Fin Nw → ℕ}

theorem list_scale_star {α : Type*} (l : List α) (a : α → ℝ) (g : α → ℂ) (c : ℝ) :
    (c : ℂ) * star (l.map fun γ => ((a γ : ℝ) : ℂ) * g γ).sum =
      (l.map fun γ => ((a γ : ℝ) : ℂ) * ((c : ℂ) * star (g γ))).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, star_add, mul_add, ih]
    congr 1
    simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
    ring

open Classical in
theorem tbLetterPart_eq {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (l : Fin Nw)
    (x : ι) (e : h x) (β₀ : ℕ × ℕ) (k : Fin 2) (r : ℝ) (ψ : Vec 2 → ℂ)
    (i' : B1WIndex ι h Nw m Ks) (z : Vec 2) :
    b1wLetterPart F θ l x e β₀ k r ψ i' z =
      ∑ d ∈ admissibleOrders (fun p : Fin (Nw + 1) × ι => F.κ p.1 p.2) D
          (l.succ, x) (l.castSucc, i'.2.1),
        if hd : d ∈ Finset.Icc 2 D then
          (((F.letters l).edge x i'.2.1 ⟨d, hd⟩).map fun γ =>
            ((inner ℝ (ContinuousLinearMap.adjoint γ.map e) (b1wVec i') : ℝ) : ℂ) *
              letterGam θ (F.letters l).positive (F.letters l).slow (F.ϖ * F.ηg) F.X₀ r d γ.coeff
                β₀ k (b1wMom i') ψ z).sum
        else 0 := by
  unfold b1wLetterPart
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hd : d ∈ Finset.Icc 2 D
  · simp only [hd, dite_true]
    congr 1
    refine List.map_congr_left fun γ _ => ?_
    unfold letterGam b1wMom
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun s _ =>
      Finset.sum_congr rfl fun ω _ => Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> ring
  · simp [hd]


open Classical in
theorem star_letterPart_scaled {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (l : Fin Nw)
    (i i' : B1WIndex ι h Nw m Ks) (β₀ : ℕ × ℕ) (k : Fin 2) (r : ℝ) (ψ : Vec 2 → ℂ) (z : Vec 2)
    (c : ℝ) :
    (c : ℂ) * star (b1wLetterPart F θ l i.2.1 (b1wVec i) β₀ k r ψ i' z) =
      ∑ d ∈ admissibleOrders (fun p : Fin (Nw + 1) × ι => F.κ p.1 p.2) D
          (l.succ, i.2.1) (l.castSucc, i'.2.1),
        if hd : d ∈ Finset.Icc 2 D then
          (((F.letters l).edge i.2.1 i'.2.1 ⟨d, hd⟩).map fun γ =>
            ((letterMat (stdOrthonormalBasis ℝ (h i.2.1)) (stdOrthonormalBasis ℝ (h i'.2.1)) γ.map
              i.2.2.2 i'.2.2.2 : ℝ) : ℂ) *
              ((c : ℂ) * star (letterGam θ (F.letters l).positive (F.letters l).slow
                (F.ϖ * F.ηg) F.X₀ r d γ.coeff β₀ k (b1wMom i') ψ z))).sum
        else 0 := by
  have hl : ∀ (M : h i'.2.1 →L[ℝ] h i.2.1),
      letterMat (stdOrthonormalBasis ℝ (h i.2.1)) (stdOrthonormalBasis ℝ (h i'.2.1)) M
        i.2.2.2 i'.2.2.2 = inner ℝ (ContinuousLinearMap.adjoint M (b1wVec i)) (b1wVec i') :=
    fun M => rfl
  rw [tbLetterPart_eq, star_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hd : d ∈ Finset.Icc 2 D
  · simp only [hd, dite_true, hl]
    have key := list_scale_star ((F.letters l).edge i.2.1 i'.2.1 ⟨d, hd⟩)
      (fun γ => inner ℝ (ContinuousLinearMap.adjoint γ.map (b1wVec i)) (b1wVec i'))
      (fun γ => letterGam θ (F.letters l).positive (F.letters l).slow (F.ϖ * F.ηg)
        F.X₀ r d γ.coeff β₀ k (b1wMom i') ψ z) c
    exact key
  · simp [hd]

theorem ratio_star_letterTransform {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (l : Fin Nw)
    (i i' : B1WIndex ι h Nw m Ks) (hi : i.1 = l.succ) (hi' : i'.1 = l.castSucc) (r : ℝ)
    (f : Vec 2 → ℂ) (z : Vec 2) :
    ((letterRatioReal F.π F.ϖ F.ηg F.letters l i.2.1 i'.2.1 (b1wMom i) (b1wMom i') : ℝ) : ℂ) *
        star (b1wLetterTransform F θ i i' r (fun y => star (f y)) z) =
      letterGfam θ (F.letters l)
        (admissibleOrders (fun p : Fin (Nw + 1) × ι => F.κ p.1 p.2) D (l.succ, i.2.1)
          (l.castSucc, i'.2.1)) (F.ϖ * F.ηg) F.X₀ r i.2.1 i'.2.1 (b1wMom i) (b1wMom i')
        (letterRatioReal F.π F.ϖ F.ηg F.letters l i.2.1 i'.2.1 (b1wMom i) (b1wMom i'))
        i.2.2.2 i'.2.2.2 f z := by
  classical
  set R := letterRatioReal F.π F.ϖ F.ηg F.letters l i.2.1 i'.2.1 (b1wMom i) (b1wMom i') with hR
  have hT : b1wLetterTransform F θ i i' r (fun y => star (f y)) z =
      -((((b1wMom i).1 : ℝ) : ℂ) * b1wLetterPart F θ l i.2.1 (b1wVec i)
        ((b1wMom i).1 - 1, (b1wMom i).2) 0 r (fun y => star (f y)) i' z) -
      (((b1wMom i).2 : ℝ) : ℂ) * b1wLetterPart F θ l i.2.1 (b1wVec i)
        ((b1wMom i).1, (b1wMom i).2 - 1) 1 r (fun y => star (f y)) i' z -
      ∑ k : Fin 2, b1wLetterPart F θ l i.2.1 (b1wVec i) (b1wMom i) k r
        (fibreCovDeriv (-θ) k (fun y => star (f y))) i' z := by
    unfold b1wLetterTransform
    rw [Finset.sum_eq_single l]
    · simp only [hi, hi', and_self, ite_true]
    · intro l' _ hne
      have hn : ¬ (i.1 = l'.succ ∧ i'.1 = l'.castSucc) := by
        rintro ⟨h1, -⟩
        rw [hi] at h1
        exact hne (Fin.succ_injective _ h1.symm)
      simp only [hn, ite_false]
    · intro hl; exact absurd (Finset.mem_univ l) hl
  rw [hT]
  simp only [Fin.sum_univ_two, star_sub, star_neg, star_add, star_mul']
  have k1 := star_letterPart_scaled F θ l i i' ((b1wMom i).1 - 1, (b1wMom i).2) 0 r
    (fun y => star (f y)) z (R * -(((b1wMom i).1 : ℝ)))
  have k2 := star_letterPart_scaled F θ l i i' ((b1wMom i).1, (b1wMom i).2 - 1) 1 r
    (fun y => star (f y)) z (R * -(((b1wMom i).2 : ℝ)))
  have k3 := star_letterPart_scaled F θ l i i' (b1wMom i) 0 r
    (fibreCovDeriv (-θ) 0 (fun y => star (f y))) z (R * -1)
  have k4 := star_letterPart_scaled F θ l i i' (b1wMom i) 1 r
    (fibreCovDeriv (-θ) 1 (fun y => star (f y))) z (R * -1)
  unfold letterGfam
  simp only [letterVars, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    variantFun, Bool.false_eq_true, ↓reduceIte]
  rw [← k1, ← k2, ← k3, ← k4]
  simp only [Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

end Reshape


section Main

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D Nw m : ℕ}
  {Ks : Fin Nw → ℕ}

/-- The chosen family of a `BRealizes`. -/
def BRealizes.op {m₁ m₂ N n : ℕ} {G : Fin m₁ → Fin m₂ → (Vec 2 → ℂ) → Vec 2 → ℂ} {c : ℝ}
    (hh : BRealizes N n G c) : Fin m₁ → Fin m₂ → TorusHk N ℂ →L[ℝ] TorusHk n ℂ :=
  Classical.choose (show ∃ _T : Fin m₁ → Fin m₂ → TorusHk N ℂ →L[ℝ] TorusHk n ℂ, _ from hh)

theorem BRealizes.op_spec {m₁ m₂ N n : ℕ} {G : Fin m₁ → Fin m₂ → (Vec 2 → ℂ) → Vec 2 → ℂ} {c : ℝ}
    (hh : BRealizes N n G c) :
    (∀ b b' ψ, (torusHkValueCLM (hh.op b b' ψ) : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      G b b' (torusHigherClassicalValue N ψ)) ∧ BlockBound c hh.op :=
  Classical.choose_spec (show ∃ _T : Fin m₁ → Fin m₂ → TorusHk N ℂ →L[ℝ] TorusHk n ℂ, _ from hh)

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
theorem stage_mom_le (i : B1WIndex ι h Nw m Ks) : (b1wMom i).1 + (b1wMom i).2 ≤ m + ∑ l, Ks l := by
  have h1 := (Finset.mem_filter.1 i.2.2.1.2).2
  have h2 : b1wLevelMoments m Ks i.1 ≤ m + ∑ l, Ks l := by
    unfold b1wLevelMoments
    refine Nat.add_le_add_left (Finset.sum_le_sum fun l _ => ?_) m
    split_ifs <;> omega
  exact h1.trans h2

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
theorem stage_eq (i : B1WIndex ι h Nw m Ks) (j : Fin (Nw + 1)) (x : ι) (β : ℕ × ℕ)
    (hi : i.1 = j ∧ b1wKey i = (x, β)) :
    ∃ (hβ : β ∈ momentIndices (b1wLevelMoments m Ks j)) (b : Fin (Module.finrank ℝ (h x))),
      i = ⟨j, x, ⟨β, hβ⟩, b⟩ := by
  obtain ⟨j', y, ⟨β2, h2⟩, b⟩ := i
  obtain ⟨h1, h3⟩ := hi
  simp only [b1wKey, Prod.mk.injEq] at h1 h3
  obtain ⟨rfl, rfl⟩ := h3
  subst h1
  exact ⟨h2, b, rfl⟩


end Main

section Reduce

variable {m₁ m₂ N n : ℕ} {I I' : Type*}

open Classical in
/-- **Reduction of the stage blocks to the basis indices.** -/
theorem block_reduce (Top : Fin m₁ → Fin m₂ → TorusHk N ℂ →L[ℝ] TorusHk n ℂ) (c : ℝ)
    (hT : BlockBound c Top) (mk : Fin m₁ → I) (mk' : Fin m₂ → I') (hmk : Function.Injective mk)
    (hmk' : Function.Injective mk') (T : I → I' → TorusHk N ℂ →L[ℝ] TorusHk n ℂ)
    (hTm : ∀ b b', T (mk b) (mk' b') = Top b b') (S : Finset I) (S' : Finset I')
    (hS : ∀ i ∈ S, ∃ b, mk b = i) (hS' : ∀ i' ∈ S', ∃ b', mk' b' = i') (f : I → TorusHk N ℂ) :
    ∑ i' ∈ S', ‖∑ i ∈ S, T i i' (f i)‖ ^ 2 ≤ c ^ 2 * ∑ i ∈ S, ‖f i‖ ^ 2 := by
  set S₀ : Finset (Fin m₁) := Finset.univ.filter fun b => mk b ∈ S with hS₀
  set S₀' : Finset (Fin m₂) := Finset.univ.filter fun b' => mk' b' ∈ S' with hS₀'
  have e1 : S = S₀.image mk := by
    ext i
    constructor
    · intro hi
      obtain ⟨b, rfl⟩ := hS i hi
      exact Finset.mem_image.2 ⟨b, by simp [hS₀, hi], rfl⟩
    · intro hi
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hi
      exact (Finset.mem_filter.1 hb).2
  have e2 : S' = S₀'.image mk' := by
    ext i
    constructor
    · intro hi
      obtain ⟨b, rfl⟩ := hS' i hi
      exact Finset.mem_image.2 ⟨b, by simp [hS₀', hi], rfl⟩
    · intro hi
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hi
      exact (Finset.mem_filter.1 hb).2
  set g : Fin m₁ → TorusHk N ℂ := fun b => if b ∈ S₀ then f (mk b) else 0 with hg
  have inner_eq : ∀ b' : Fin m₂, ∑ i ∈ S, T i (mk' b') (f i) = ∑ b, Top b b' (g b) := by
    intro b'
    rw [e1, Finset.sum_image (fun a _ b _ hab => hmk hab)]
    simp only [hTm]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S₀)]
    have : ∑ b ∈ Finset.univ.filter (fun b => b ∈ S₀), Top b b' (g b) = ∑ b ∈ S₀, Top b b' (f (mk b)) := by
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
      exact Finset.sum_congr rfl fun b hb => by simp [hg, hb]
    rw [this]
    have h0 : ∑ b ∈ Finset.univ.filter (fun b => b ∉ S₀), Top b b' (g b) = 0 :=
      Finset.sum_eq_zero fun b hb => by simp [hg, (Finset.mem_filter.1 hb).2]
    rw [h0, add_zero]
  calc ∑ i' ∈ S', ‖∑ i ∈ S, T i i' (f i)‖ ^ 2
      = ∑ b' ∈ S₀', ‖∑ b, Top b b' (g b)‖ ^ 2 := by
        rw [e2, Finset.sum_image (fun a _ b _ hab => hmk' hab)]
        exact Finset.sum_congr rfl fun b' _ => by rw [inner_eq]
    _ ≤ ∑ b', ‖∑ b, Top b b' (g b)‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => by positivity)
    _ ≤ c ^ 2 * ∑ b, ‖g b‖ ^ 2 := hT.2 g
    _ = c ^ 2 * ∑ i ∈ S, ‖f i‖ ^ 2 := by
        congr 1
        rw [e1, Finset.sum_image (fun a _ b _ hab => hmk hab)]
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S₀)]
        have h1 : ∑ b ∈ Finset.univ.filter (fun b => b ∈ S₀), ‖g b‖ ^ 2 = ∑ b ∈ S₀, ‖f (mk b)‖ ^ 2 := by
          rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
          exact Finset.sum_congr rfl fun b hb => by simp [hg, hb]
        have h0 : ∑ b ∈ Finset.univ.filter (fun b => b ∉ S₀), ‖g b‖ ^ 2 = 0 :=
          Finset.sum_eq_zero fun b hb => by simp [hg, (Finset.mem_filter.1 hb).2]
        rw [h1, h0, add_zero]

end Reduce


open Classical in
/-- **The block letter operators at every frequency of the zone**: `LetterOpsZoneStatement`. -/
theorem letterOpsZone : LetterOpsZoneStatement.{u, v} := by
  intro K Nw D m d Ks pos ρ n
  have hC0 : 0 ≤ 4 * gamCfin D n |ρ| (m + ∑ l, Ks l) (Finset.univ.sup Ks) := by
    unfold gamCfin gamPr
    have h1 := gamCc_nonneg D (m + ∑ l, Ks l) (Finset.univ.sup Ks)
    have h3 : 0 ≤ ∑ K ∈ Finset.range (n + D + 1), |cellDriftNativePrice K| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    positivity
  refine ⟨4 * gamCfin D n |ρ| (m + ∑ l, Ks l) (Finset.univ.sup Ks), hC0, ?_⟩
  intro g₁ ι _ h _ _ _ _ _ _ F θ hlet hJ hρ
  have hη := F.piece.hη
  have hη1 := F.piece.hη1
  have hS := F.piece.hS
  have hϖ := F.piece.hϖ
  have hϖpos : 0 < F.ϖ := by
    rw [hϖ]; exact Real.sqrt_pos.2 (div_pos hη (by linarith))
  have hϖ1 : F.ϖ ≤ 1 := by
    rw [hϖ, ← Real.sqrt_one]
    exact Real.sqrt_le_sqrt ((div_le_self hη.le hS).trans hη1)
  have hθ := fun k => (hρ k).trans (le_abs_self ρ)
  have hgood : ∀ᵐ r ∂(volume.restrict (Icc F.a F.b)),
      ∀ l, LetterGood (F.letters l) (Icc F.a F.b) F.J r := by
    have h1 : ∀ᵐ r ∂(volume : Measure ℝ), ∀ l, r ∈ Icc F.a F.b →
        LetterGood (F.letters l) (Icc F.a F.b) F.J r :=
      ae_all_iff.2 fun l => letterGood_ae F.π F.piece.hπ (F.letters l) (Icc F.a F.b) F.J F.H
        (F.piece.hlet l)
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [h1] with r hr hrI l using hr l hrI
  filter_upwards [hgood, ae_restrict_mem measurableSet_Icc] with r hg hr
  intro l N hN1 hN2
  set M0 := m + ∑ l, Ks l with hM0
  set Sm := Finset.univ.sup Ks with hSm
  set Dmax := Finset.univ.sup d with hDmax
  have hord : (F.letters l).order ≤ Dmax := by
    rw [(hlet l).1]; exact Finset.le_sup (f := d) (Finset.mem_univ l)
  have hslow : (F.letters l).slow ≤ Sm := by
    rw [(hlet l).2.1]; exact Finset.le_sup (f := Ks) (Finset.mem_univ l)
  have hN1' : n + (F.letters l).order ≤ N := by rw [(hlet l).1]; exact hN1
  let A : ι → ι → Finset ℕ := fun x x' => admissibleOrders (fun p : Fin (Nw + 1) × ι => F.κ p.1 p.2) D
    (l.succ, x) (l.castSucc, x')
  have hBR : ∀ (x x' : ι) (β β' : ℕ × ℕ), β.1 + β.2 ≤ M0 → β'.1 + β'.2 ≤ M0 →
      BRealizes (m₁ := Module.finrank ℝ (h x)) (m₂ := Module.finrank ℝ (h x')) N n
        (letterGfam θ (F.letters l) (A x x') (F.ϖ * F.ηg) F.X₀ r x x' β β'
          (letterRatioReal F.π F.ϖ F.ηg F.letters l x x' β β'))
        (4 * gamCfin D n |ρ| M0 Sm * (if LetterMomRel Sm (Dmax + 1) β β' then 1 else 0) *
          letterCompWeight (F.letters l) x x') := fun x x' β β' hβ hβ' =>
    letterBlock_exists F.π F.letters l F.a F.b F.J F.H (F.piece.hlet l) r hr (hg l) F.piece.hπ
      F.ϖ F.ηg hϖpos hϖ1 F.piece.hηg F.piece.hηg1 θ |ρ| hθ F.X₀ (A x x') n N Dmax M0 Sm hord hslow hJ hN1'
      hN2 x x' β β' hβ hβ'
  let Top : ∀ (x x' : ι) (β β' : ℕ × ℕ), Fin (Module.finrank ℝ (h x)) →
      Fin (Module.finrank ℝ (h x')) → TorusHk N ℂ →L[ℝ] TorusHk n ℂ := fun x x' β β' =>
    if hh : β.1 + β.2 ≤ M0 ∧ β'.1 + β'.2 ≤ M0 then (hBR x x' β β' hh.1 hh.2).op
    else fun _ _ => 0
  refine ⟨fun i i' => Top i.2.1 i'.2.1 (b1wMom i) (b1wMom i') i.2.2.2 i'.2.2.2, ?_, ?_⟩
  · intro i i' hi hi' ψ
    have hM : (b1wMom i).1 + (b1wMom i).2 ≤ M0 := stage_mom_le i
    have hM' : (b1wMom i').1 + (b1wMom i').2 ≤ M0 := stage_mom_le i'
    have hspec := (hBR i.2.1 i'.2.1 (b1wMom i) (b1wMom i') hM hM').op_spec.1 i.2.2.2 i'.2.2.2 ψ
    simp only [Top, hM, hM', and_self, dite_true]
    filter_upwards [hspec] with z hz
    rw [hz, b1wScaleRatio_letter F.π F.ϖ F.ηg F.letters l i i' hi hi',
      ratio_star_letterTransform F θ l i i' hi hi' r _ z]
  · intro S S' x x' β β' hS hS' f
    have hnn : 0 ≤ ∑ i ∈ S, ‖f i‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    by_cases hSe : S.Nonempty
    swap
    · rw [Finset.not_nonempty_iff_eq_empty.1 hSe]
      simp
    by_cases hSe' : S'.Nonempty
    swap
    · rw [Finset.not_nonempty_iff_eq_empty.1 hSe']
      simp only [Finset.sum_empty]
      positivity
    obtain ⟨i0, hi0⟩ := hSe
    obtain ⟨i0', hi0'⟩ := hSe'
    obtain ⟨hβ, b0, -⟩ := stage_eq i0 l.succ x β ⟨(hS i0 hi0).1, (hS i0 hi0).2⟩
    obtain ⟨hβ', b0', -⟩ := stage_eq i0' l.castSucc x' β' ⟨(hS' i0' hi0').1, (hS' i0' hi0').2⟩
    let mk : Fin (Module.finrank ℝ (h x)) → B1WIndex ι h Nw m Ks := fun b =>
      ⟨l.succ, x, ⟨β, hβ⟩, b⟩
    let mk' : Fin (Module.finrank ℝ (h x')) → B1WIndex ι h Nw m Ks := fun b =>
      ⟨l.castSucc, x', ⟨β', hβ'⟩, b⟩
    have hM : β.1 + β.2 ≤ M0 := stage_mom_le (mk b0)
    have hM' : β'.1 + β'.2 ≤ M0 := stage_mom_le (mk' b0')
    have hTm : ∀ b b', Top (mk b).2.1 (mk' b').2.1 (b1wMom (mk b)) (b1wMom (mk' b'))
        (mk b).2.2.2 (mk' b').2.2.2 = (hBR x x' β β' hM hM').op b b' := by
      intro b b'
      show Top x x' β β' b b' = _
      simp only [Top, hM, hM', and_self, dite_true]
    have key := block_reduce (hBR x x' β β' hM hM').op _ (hBR x x' β β' hM hM').op_spec.2 mk mk'
      (fun a b hab => by simpa [mk] using hab) (fun a b hab => by simpa [mk'] using hab)
      (fun i i' => Top i.2.1 i'.2.1 (b1wMom i) (b1wMom i') i.2.2.2 i'.2.2.2) hTm S S'
      (fun i hi => by
        obtain ⟨hβi, b, hb⟩ := stage_eq i l.succ x β ⟨(hS i hi).1, (hS i hi).2⟩
        exact ⟨b, hb.symm⟩)
      (fun i hi => by
        obtain ⟨hβi, b, hb⟩ := stage_eq i l.castSucc x' β' ⟨(hS' i hi).1, (hS' i hi).2⟩
        exact ⟨b, hb.symm⟩) f
    exact key


/-- **The block letter operators**: `LetterOpsStatement`, the zone form with `theta_abs_le`. -/
theorem letterOps : LetterOpsStatement.{u, v} := by
  intro K Nw D m d Ks pos ρ n
  obtain ⟨C0, hC0, hZ⟩ := letterOpsZone.{u, v} K Nw D m d Ks pos ρ n
  refine ⟨C0, hC0, ?_⟩
  intro g₁ ι _ h _ _ _ _ _ _ F θ hlet hJ hρ
  exact hZ g₁ F θ hlet hJ (theta_abs_le F.piece.hη F.piece.hη1 θ hρ)

/-- **The letter transform bound at every frequency of the zone**,
at almost every time (the zone bound for `|θ_k| ≤ ρ`). -/
theorem letterTransformBoundAEZone : LetterTransformBoundAEZoneStatement.{u, v} :=
  letterTransformBoundAEZone_of_ops letterOpsZone

/-- **The letter transform bound**, at almost every time: the zone bound with
`theta_abs_le`. -/
theorem letterTransformBoundAE : LetterTransformBoundAEStatement.{u, v} := by
  intro K Nw D m d Ks pos ρ n
  obtain ⟨C, hC, hZ⟩ := letterTransformBoundAEZone.{u, v} K Nw D m d Ks pos ρ n
  refine ⟨C, hC, ?_⟩
  intro g₁ ι _ h _ _ _ _ _ _ F θ hlet hJ hρ
  exact hZ g₁ F θ hlet hJ (theta_abs_le F.piece.hη F.piece.hη1 θ hρ)

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleWords.Assembly

/-! Assembly of the retained amplitude factor (`RetainedAmplitudeFactorStatement`) from the
amplitude identification, the moment amplitudes and the factor calculus
(`FactorMomentCalculusStatement`). -/

universe u v

/-- The exact retained-factor statement follows from Fourier/cutoff calculus and inverse-gauge jets. -/
theorem retainedAmplitudeFactor_of_moments_of_ingredients
    (hI : AmplitudeIdentificationStatement.{u, v}) (hM : MomentAmplitudeStatement.{u, v})
    (hCalc : FactorMomentCalculusStatement.{u, v}) :
    RetainedAmplitudeFactorStatement.{u, v} := by
  intro K
  obtain ⟨gI, hgI, hIK⟩ := hI K
  obtain ⟨gM, hgM, hMK⟩ := hM K
  refine ⟨min gI gM, lt_min hgI hgM, ?_⟩
  intro Nw D H m d Ks pos
  obtain ⟨P, Q, hPQ⟩ := hMK Nw D H m d Ks pos
  refine ⟨P + m, Q, ?_⟩
  intro CH ρ χ ψ hρ hρlo hχ hχsupp hψ hψb χr χ₃ hχr hχrb hχ₃ hχ₃b hrel
  obtain ⟨CM, c, hCM, hc, hMc⟩ := hPQ CH ρ hρ hρlo
  obtain ⟨Bg, hBg, hGc⟩ := factorInverseGauge K m CH ρ hρ
  obtain ⟨L, hL, hLc⟩ := hCalc m (∑ i, Ks i) P K.ξ0 ρ χ ψ hρ hχ hχsupp hψ hψb
    χr χ₃ hχr hχrb hχ₃ hχ₃b hrel
  refine ⟨L * Bg * CM, c, mul_pos (mul_pos hL hBg) hCM, hc, ?_⟩
  intro ι _ h _ _ _ _ _ _ J π letters hletters η S ηg t₀ Sw ϖ a b Dq G v g reg pkg hB
    ha hab hb hba hDq hquiet hJ X₀ κ hκ f u w hf hch
  obtain ⟨φ, hφ, hfφ⟩ := planeDatum_rep f hf
  have hBI : IsWordPiece K gI H J π letters η S ηg ϖ G v g reg a b :=
    { hB with hg₁ := hB.hg₁.trans (min_le_left _ _) }
  have hBM : IsWordPiece K gM H J π letters η S ηg ϖ G v g reg a b :=
    { hB with hg₁ := hB.hg₁.trans (min_le_right _ _) }
  let κ' := cappedWordSlots κ 0 d
  let hle := cappedWordSlots_le_original κ 0 d
  let f' := fun x => truncatePlaneHk (hle 0 x) (f x)
  let u' := fun j x t => truncatePlaneHk (hle j x) (u j x t)
  let w' := fun j x t => truncatePlaneHk (Nat.succ_le_succ (hle j x)) (w j x t)
  have hκ' : IsWordSlots letters κ' := cappedWordSlots_isWordSlots hB.hlet
    (fun i => (hletters i).1) hκ 0
  have ht := wordChainFrom_truncate hB.hD G letters κ κ' hle hκ hκ' X₀ (ϖ * ηg) a b v
    (chainDatum κ f) (fun _ _ _ => 0) u w ((isPlaneChain_iff_from _ κ a b v f _ u w).1 hch)
  have hdata : (fun j x => truncatePlaneHk (hle j x) (chainDatum κ f j x)) = chainDatum κ' f' := by
    funext j x
    by_cases hj : j = 0
    · subst hj
      simp only [chainDatum, dite_true, f']
    · simp only [chainDatum, hj, dite_false, map_zero]
  have hch' : IsPlaneChain (wordChainData G letters X₀ (ϖ * ηg)) κ' a b v f'
      (fun _ _ _ => 0) u' w' := by
    apply (isPlaneChain_iff_from _ κ' a b v f' _ u' w').2
    exact IsPlaneChainFrom.congr_data ht hdata (by funext j x t; exact map_zero _)
  have hvalue (j : Fin (Nw + 1)) (x : ι) (t : ℝ) : planeValue (u' j x t) = planeValue (u j x t) :=
    planeJetOrder_truncate (hle j x) (Nat.zero_le _) (u j x t) _
  have hf' : ∃ R : ℝ, ∀ x, ∀ᵐ z ∂volume, R ^ 2 < z 0 ^ 2 + z 1 ^ 2 →
      planeValue (f' x) z = 0 := by
    obtain ⟨R, hR⟩ := hf
    refine ⟨R, fun x => ?_⟩
    rw [show planeValue (f' x) = planeValue (f x) from
      planeJetOrder_truncate (hle 0 x) (Nat.zero_le _) (f x) _]
    exact hR x
  have hident := hIK H J π letters η S ηg t₀ Sw ϖ a b G v g reg pkg hBI ha hab hb X₀ κ' hκ'
    (fun j x => (cappedWordSlots_le_reserve κ 0 m d Ks j x).trans hJ) f' u' w' hf' hch'
  have hmom (x : ι) (β : ℕ × ℕ) : Integrable
      (fun y => (y 0 ^ β.1 * y 1 ^ β.2) • planeValue (u (Fin.last Nw) x b) y) := by
    simpa only [hvalue] using hident.1 (Fin.last Nw) x b ⟨hab, le_rfl⟩ (β.1 + β.2) β
      (by simp only [momentIndices, Finset.mem_filter, Finset.mem_product, Finset.mem_range]; omega)
  have hϖ : 0 < ϖ := by
    rw [hB.hϖ]
    exact Real.sqrt_pos.mpr (div_pos hB.hη (lt_of_lt_of_le zero_lt_one hB.hS))
  have hϖle : ϖ ≤ Real.sqrt η := by
    rw [hB.hϖ]
    exact Real.sqrt_le_sqrt (div_le_self hB.hη.le hB.hS)
  have hϖ1 : ϖ ≤ 1 := hϖle.trans (Real.sqrt_le_one.mpr hB.hη1)
  have hratio : ϖ / Real.sqrt η ≤ 1 := (div_le_one (Real.sqrt_pos.mpr hB.hη)).mpr hϖle
  have hCw : 0 ≤ K.Cw :=
    (mul_nonneg (Real.sqrt_nonneg η) (Real.sqrt_nonneg _)).trans (hB.hvw 0 0)
  have hG := hGc pkg.actual hB.hη hB.hη1 pkg.consts_pos.2.2.2.1.le hCw
    hB.hGm hB.hv hB.hvw a b S ϖ hab hB.hS hB.hϖ hba
  let E := 1 + peFactor η ^ Q * (1 + S) ^ Q * ((1 + (reg.joins : ℝ)) *
    Real.exp (-c * reg.buffer) + Real.exp (-c * Dq))
  have hpe : 0 ≤ peFactor η := zero_le_one.trans (AVRegularity.CycleWords.Assembly.one_le_peFactor η)
  have hS0 : 0 ≤ S := zero_le_one.trans hB.hS
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  let B := CM * wordTheta ηg letters * E
  have hB0 : 0 ≤ B := mul_nonneg (mul_nonneg hCM.le hB.wordTheta_nonneg) hE
  have hbound := hMc J π letters hletters η S ηg t₀ Sw ϖ a b Dq G v g reg pkg hBM ha hab hb hba
    hDq hquiet hJ X₀ κ hκ f u w hf hch
  have hmoment : ∀ θ : Vec 2, fibreNorm (planeFibreFrequency η θ) ≤ ρ → ∀ β ∈ momentIndices m,
      momentAmpNorm π ϖ β (fun x => planeValue (u (Fin.last Nw) x b)) θ ≤
      ENNReal.ofReal (Real.exp (blockGauge pkg.actual.lam η a b θ).re * B *
        (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ P) * datumJets π ϖ (β.1 + β.2 + ∑ i, Ks i) φ θ := by
    intro θ hθ β hβ
    have he : Real.exp (blockGauge pkg.actual.lam η a b θ).re *
        (CM * wordTheta ηg letters * (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ P * E) =
        Real.exp (blockGauge pkg.actual.lam η a b θ).re * B *
          (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ P := by dsimp only [B]; ring
    rw [← datumJets_congr_ae π ϖ _ hfφ θ]
    simpa only [← he, datumJets, E] using hbound θ hθ β hβ
  have hc := hLc π hB.hπ η ϖ Bg B hB.hη hϖ hϖ1 hratio hBg.le hB0 φ
    (fun x => planeValue (u (Fin.last Nw) x b)) hφ hmom (blockGauge pkg.actual.lam η a b) hG.1 hG.2 hmoment
  refine ⟨hc.1, hc.2.1, hc.2.2.1, ?_⟩
  obtain ⟨Ac, As, hsmooth, hrot, hjet⟩ := hc.2.2.2
  refine ⟨Ac, As, hsmooth, hrot, ?_⟩
  intro θ hθ
  have he : L * Bg * B * (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ (P + m) =
      (L * Bg * CM) * wordTheta ηg letters * (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ (P + m) * E := by
    dsimp only [B]
    ring
  have hj := hjet θ hθ
  simp only [blochFibreDerivNorm_congr_ae (fun x => (hfφ x).symm)] at hj
  simpa only [he, E, wordReserveN] using hj

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # The transform families of every pair of stages

From the two transform bounds, every pair of stages `k' < k` has its test family in the
ladder's spaces, `H^{s_k} → H^{s_{k'}}`, with one constant `B` for all pairs
(`b1w_family_provider`, `B` = the sum of the constants up to the top of the ladder):

* the same level: the same-level bound, since the ladder drops by `≥ 1` (`b1wLadder_same_of_lt`);
* the next level: the letter bound, since the ladder drops by `≥ d_l` (`b1wLadder_letter_of_lt`);
* otherwise the transforms vanish (`b1wTestTransform_zero_of_level`) and the family is `0`.

The letter coefficients need `s_{k'} + d_max ≤ J`, which holds below the top of the ladder
(`b1wLadderTop`). The letter bound holds for almost every time; one null set serves all the orders
up to the top of the ladder, so the families exist at almost every time. -/

universe u v

/-- The top of the regularity ladder. -/
def b1wLadderTop {Nw : ℕ} (s₀ : ℕ) (d Ks : Fin Nw → ℕ) (m : ℕ) : ℕ :=
  s₀ + (∑ l, d l + ∑ l, Ks l) + (m + ∑ l, Ks l)

/-- Below the number of stages the ladder stays below its top. -/
theorem b1wLadderAt_le_top {Nw : ℕ} (s₀ m : ℕ) (d Ks : Fin Nw → ℕ) {k : ℕ}
    (hk : k < b1wM Nw m Ks) : b1wLadderAt Nw s₀ d Ks k ≤ b1wLadderTop s₀ d Ks m := by
  have hdiv : k / (Nw + 1) < m + ∑ l, Ks l + 1 := by
    unfold b1wM at hk
    exact Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hk)
  have hL : b1wLadderLevel d Ks ⟨k % (Nw + 1), Nat.mod_lt _ (Nat.succ_pos Nw)⟩ ≤
      ∑ l, d l + ∑ l, Ks l := by
    unfold b1wLadderLevel
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun l _ => by split_ifs <;> omega
  unfold b1wLadderAt b1wLadderTop
  omega

/-- **The transform families of every pair of stages, at every frequency of the zone**. -/
theorem b1w_family_provider_zone (hSL : SameLevelTransformBoundZoneStatement.{u, v})
    (hLT : LetterTransformBoundAEZoneStatement.{u, v}) (K : ScalarConstants) (Nw D m : ℕ)
    (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool) (ρ : ℝ) (s₀ : ℕ)
    (hs₀ : (Finset.univ.sup d) + 3 ≤ s₀) :
    ∃ B : ℝ, 0 ≤ B ∧
    ∀ (g₁ : ℝ) {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
      [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
      [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
      (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
      (∀ l, (F.letters l).order = d l ∧ (F.letters l).slow = Ks l ∧
        (F.letters l).positive = pos l) →
      b1wLadderTop s₀ d Ks m + (Finset.univ.sup d) ≤ F.J →
      (∀ k, |θ k| ≤ ρ) →
    ∀ᵐ r ∂(volume.restrict (Icc F.a F.b)), ∀ (k k' : ℕ), k' < k →
    ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk (b1wLadderAt Nw s₀ d Ks k) ℂ,
      ∃ Φ : B1WIndex ι h Nw m Ks → TorusHk (b1wLadderAt Nw s₀ d Ks k') ℂ,
        (∀ i' ∈ stageSet b1wSt k', (torusHkValueCLM (Φ i') : Vec 2 → ℂ)
          =ᵐ[volume.restrict AVenhance.unitCube] fun y =>
            ∑ i ∈ stageSet b1wSt k, b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
              star (b1wTestTransform F θ i i' r (fun y => star
                (torusHigherClassicalValue (b1wLadderAt Nw s₀ d Ks k) (ψ i) y)) y)) ∧
        ∑ i' ∈ stageSet b1wSt k', ‖Φ i'‖ ^ 2 ≤ B ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2 := by
  classical
  choose CS hCS hSLn using fun n => hSL K Nw D m d Ks ρ n
  choose CL hCL hLTn using fun n => hLT K Nw D m d Ks pos ρ n
  set top := b1wLadderTop s₀ d Ks m with htop
  set B := ∑ n ∈ Finset.range (top + 1), (CS n + CL n) with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun n _ => add_nonneg (hCS n) (hCL n)
  have hCSB : ∀ n ≤ top, CS n ≤ B := fun n hn =>
    (le_add_of_nonneg_right (hCL n)).trans (Finset.single_le_sum
      (f := fun n => CS n + CL n) (fun n _ => add_nonneg (hCS n) (hCL n))
      (Finset.mem_range.2 (by omega)))
  have hCLB : ∀ n ≤ top, CL n ≤ B := fun n hn =>
    (le_add_of_nonneg_left (hCS n)).trans (Finset.single_le_sum
      (f := fun n => CS n + CL n) (fun n _ => add_nonneg (hCS n) (hCL n))
      (Finset.mem_range.2 (by omega)))
  refine ⟨B, hB0, ?_⟩
  intro g₁ ι _ h _ _ _ _ _ _ F θ hlet hJ hρ
  -- one null set of times for the letter bounds of all orders up to the top of the ladder
  have hae := ae_all_iff.2 fun n : Fin (top + 1) =>
    hLTn n.val g₁ F θ hlet (by have := n.isLt; omega) hρ
  filter_upwards [hae, ae_restrict_mem measurableSet_Icc] with r hrL hr
  intro k k' hkk ψ
  -- the zero family
  have hzero : (∀ i ∈ stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k,
      ∀ i' ∈ stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k',
        b1wTestTransform F θ i i' r (fun y => star
          (torusHigherClassicalValue (b1wLadderAt Nw s₀ d Ks k) (ψ i) y)) = 0) →
      ∃ Φ : B1WIndex ι h Nw m Ks → TorusHk (b1wLadderAt Nw s₀ d Ks k') ℂ,
        (∀ i' ∈ stageSet b1wSt k', (torusHkValueCLM (Φ i') : Vec 2 → ℂ)
          =ᵐ[volume.restrict AVenhance.unitCube] fun y =>
            ∑ i ∈ stageSet b1wSt k, b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
              star (b1wTestTransform F θ i i' r (fun y => star
                (torusHigherClassicalValue (b1wLadderAt Nw s₀ d Ks k) (ψ i) y)) y)) ∧
        ∑ i' ∈ stageSet b1wSt k', ‖Φ i'‖ ^ 2 ≤ B ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2 := by
    intro hT
    refine ⟨fun _ => 0, fun i' hi' => ?_, ?_⟩
    · filter_upwards [Lp.coeFn_zero ℂ 2 (volume.restrict AVenhance.unitCube)] with y hy
      rw [map_zero, hy]
      refine (Finset.sum_eq_zero fun i hi => ?_).symm
      rw [hT i hi i' hi']
      simp
    · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        Finset.sum_const_zero]
      exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  by_cases hk' : (stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k').Nonempty
  swap
  · exact hzero fun i _ i' hi' => absurd ⟨i', hi'⟩ hk'
  by_cases hk : (stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k).Nonempty
  swap
  · exact hzero fun i hi _ _ => absurd ⟨i, hi⟩ hk
  obtain ⟨i₀', hi₀'⟩ := hk'
  obtain ⟨i₀, hi₀⟩ := hk
  have hst₀ : b1wSt i₀ = k := (Finset.mem_filter.1 hi₀).2
  have hst₀' : b1wSt i₀' = k' := (Finset.mem_filter.1 hi₀').2
  -- the levels of the two stages
  have hlev : ∀ i ∈ stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k,
      i.1 = i₀.1 := fun i hi => Fin.ext (by
    rw [b1wSt_level, b1wSt_level i₀, (Finset.mem_filter.1 hi).2, hst₀])
  have hlev' : ∀ i' ∈ stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k',
      i'.1 = i₀'.1 := fun i' hi' => Fin.ext (by
    rw [b1wSt_level, b1wSt_level i₀', (Finset.mem_filter.1 hi').2, hst₀'])
  -- the ladder values
  have hN : b1wLadderAt Nw s₀ d Ks k = b1wLadder s₀ d i₀ := by rw [← hst₀, b1wLadderAt_eq]
  have hn : b1wLadderAt Nw s₀ d Ks k' = b1wLadder s₀ d i₀' := by rw [← hst₀', b1wLadderAt_eq]
  have hntop : b1wLadderAt Nw s₀ d Ks k' ≤ top := by rw [hn]; exact b1wLadder_le s₀ d i₀'
  have hNs : (Finset.univ.sup d) + 3 ≤ b1wLadderAt Nw s₀ d Ks k := by
    rw [hN]; unfold b1wLadder; omega
  have hlt : b1wSt i₀' < b1wSt i₀ := by rw [hst₀, hst₀']; exact hkk
  by_cases hsame : i₀'.1 = i₀.1
  · -- the same level
    have h1 : b1wLadderAt Nw s₀ d Ks k' + 1 ≤ b1wLadderAt Nw s₀ d Ks k := by
      rw [hN, hn]; exact b1wLadder_same_of_lt s₀ d i₀ i₀' hsame hlt
    obtain ⟨Φ, hΦv, hΦb⟩ := hSLn (b1wLadderAt Nw s₀ d Ks k') g₁ F θ hρ r hr k k'
      (fun i hi i' hi' => by rw [hlev i hi, hlev' i' hi', hsame]) _ h1 hNs ψ
    refine ⟨Φ, fun i' hi' => ?_, hΦb.trans ?_⟩
    · filter_upwards [hΦv i' hi'] with y hy
      rw [hy]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hj : i'.1 = i.1 := by rw [hlev i hi, hlev' i' hi', hsame]
      have hL : b1wLetterTransform F θ i i' r (fun y => star
          (torusHigherClassicalValue (b1wLadderAt Nw s₀ d Ks k) (ψ i) y)) = 0 := by
        funext y
        simp only [b1wLetterTransform, Pi.zero_apply]
        refine Finset.sum_eq_zero fun l _ => ?_
        refine ite_eq_right_iff.2 fun hc => absurd ?_ (Fin.castSucc_lt_succ (i := l)).ne
        rw [← hc.1, ← hc.2, hj]
      simp only [b1wTestTransform, hL, Pi.zero_apply, add_zero]
    · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hCS _) (hCSB _ hntop) 2)
        (Finset.sum_nonneg fun i _ => sq_nonneg _)
  by_cases hnext : ∃ l : Fin Nw, i₀.1 = l.succ ∧ i₀'.1 = l.castSucc
  · -- the next level
    obtain ⟨l, hl1, hl2⟩ := hnext
    have h1 : b1wLadderAt Nw s₀ d Ks k' + d l ≤ b1wLadderAt Nw s₀ d Ks k := by
      rw [hN, hn]; exact b1wLadder_letter_of_lt s₀ d l i₀ i₀' hl1 hl2 hlt
    obtain ⟨Φ, hΦv, hΦb⟩ := hrL ⟨b1wLadderAt Nw s₀ d Ks k', by omega⟩ l k k'
      (fun i hi => by rw [hlev i hi, hl1]) (fun i' hi' => by rw [hlev' i' hi', hl2]) _ h1 hNs ψ
    refine ⟨Φ, fun i' hi' => ?_, hΦb.trans ?_⟩
    · filter_upwards [hΦv i' hi'] with y hy
      rw [hy]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hne : i'.1 ≠ i.1 := by
        rw [hlev i hi, hlev' i' hi', hl1, hl2]
        exact (Fin.castSucc_lt_succ (i := l)).ne
      simp only [b1wTestTransform, b1wSameTransform, hne, ite_false, zero_add]
    · exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hCL _) (hCLB _ hntop) 2)
        (Finset.sum_nonneg fun i _ => sq_nonneg _)
  · -- far levels: the transforms vanish
    refine hzero fun i hi i' hi' => ?_
    funext y
    refine congrFun (b1wTestTransform_zero_of_level F θ i i' ?_ ?_ r _) y
    · rw [hlev i hi, hlev' i' hi']
      exact hsame
    · intro l hl
      exact hnext ⟨l, (hlev i hi) ▸ hl.1, (hlev' i' hi') ▸ hl.2⟩


/-- **The transform families of every pair of stages** (frequency hypothesis `|ξ| ≤ ρ`): the zone
form with the proved zone bounds of the transform families and `theta_abs_le`. The two statement hypotheses
are kept for the existing callers. -/
theorem b1w_family_provider (_hSL : SameLevelTransformBoundStatement.{u, v})
    (_hLT : LetterTransformBoundAEStatement.{u, v}) (K : ScalarConstants) (Nw D m : ℕ)
    (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool) (ρ : ℝ) (s₀ : ℕ)
    (hs₀ : (Finset.univ.sup d) + 3 ≤ s₀) :
    ∃ B : ℝ, 0 ≤ B ∧
    ∀ (g₁ : ℝ) {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
      [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
      [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
      (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
      (∀ l, (F.letters l).order = d l ∧ (F.letters l).slow = Ks l ∧
        (F.letters l).positive = pos l) →
      b1wLadderTop s₀ d Ks m + (Finset.univ.sup d) ≤ F.J →
      fibreNorm (planeFibreFrequency F.η θ) ≤ ρ →
    ∀ᵐ r ∂(volume.restrict (Icc F.a F.b)), ∀ (k k' : ℕ), k' < k →
    ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk (b1wLadderAt Nw s₀ d Ks k) ℂ,
      ∃ Φ : B1WIndex ι h Nw m Ks → TorusHk (b1wLadderAt Nw s₀ d Ks k') ℂ,
        (∀ i' ∈ stageSet b1wSt k', (torusHkValueCLM (Φ i') : Vec 2 → ℂ)
          =ᵐ[volume.restrict AVenhance.unitCube] fun y =>
            ∑ i ∈ stageSet b1wSt k, b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
              star (b1wTestTransform F θ i i' r (fun y => star
                (torusHigherClassicalValue (b1wLadderAt Nw s₀ d Ks k) (ψ i) y)) y)) ∧
        ∑ i' ∈ stageSet b1wSt k', ‖Φ i'‖ ^ 2 ≤ B ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2 := by
  obtain ⟨B, hB, hZ⟩ := b1w_family_provider_zone sameLevelTransformBoundZone.{u, v}
    letterTransformBoundAEZone.{u, v} K Nw D m d Ks pos ρ s₀ hs₀
  refine ⟨B, hB, ?_⟩
  intro g₁ ι _ h _ _ _ _ _ _ F θ hlet hJ hρ
  exact hZ g₁ F θ hlet hJ (theta_abs_le F.piece.hη F.piece.hη1 θ hρ)

end AVRegularity.CycleWords.Assembly
end
end
