-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.ConstituentTransposeStep
public import AVRegularity.CycleWords.MixedWords.TransformBoundSchur

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords.Assembly

/-! # The cell pairing against continuous periodic tests

`stageTests` is the space of continuous periodic functions. For an integrable plane function `g`
the cell pairing `stagePair θ g t = ∫_cell B_θ(g) t` of `t ∈ stageTests` equals the plane integral
`∫ e^{-iθ·y} g(y) t(y) dy`, hence is linear in `t` and in `g` (`stagePair_eq_plane` and its
corollaries). `stageExp_atom` is the basis expansion of one term of a letter. `letterBig` is the
nested letter sum of `b1wLetterExpansion` and `b1wLetterPart` on an arbitrary family of summands:
additive, commuting with additive maps (`letterBig_map`), and passing through the cell pairing
against tests (`letterBig_pair`). -/

universe u v

/-- Continuous `ℤ²`-periodic complex functions. -/
def stageTests : Submodule ℂ (Vec 2 → ℂ) where
  carrier := {t | Continuous t ∧ AVenhance.IsZ2Periodic t}
  add_mem' := by
    rintro a b ⟨ha, hpa⟩ ⟨hb, hpb⟩
    exact ⟨ha.add hb, fun n x => by simp only [Pi.add_apply, hpa n x, hpb n x]⟩
  zero_mem' := ⟨continuous_const, fun _ _ => rfl⟩
  smul_mem' := by
    rintro c t ⟨ht, hp⟩
    exact ⟨continuous_const.smul ht, fun n x => by simp only [Pi.smul_apply, hp n x]⟩

theorem stageTests_sum_mem {ι' : Type*} (s : Finset ι') (f : ι' → Vec 2 → ℂ)
    (hf : ∀ a ∈ s, f a ∈ stageTests) : (fun z => ∑ a ∈ s, f a z) ∈ stageTests := by
  have := Submodule.sum_mem stageTests hf
  convert this using 1
  funext z
  simp [Finset.sum_apply]

theorem stageTests_ite_mem {C : Prop} [Decidable C] (c : ℂ) {f : Vec 2 → ℂ}
    (hf : f ∈ stageTests) : (fun z => if C then c * f z else 0) ∈ stageTests := by
  by_cases hC : C
  · simp only [hC, ite_true]
    exact stageTests.smul_mem c hf
  · simp only [hC, ite_false]
    exact stageTests.zero_mem

theorem stageTests_const_mul_mem (c : ℂ) {f : Vec 2 → ℂ} (hf : f ∈ stageTests) :
    (fun z => c * f z) ∈ stageTests := stageTests.smul_mem c hf

/-- The cell pairing of the Bloch part of `g` with `t`. -/
def stagePair (θ : Vec 2) (g : Vec 2 → ℝ) (t : Vec 2 → ℂ) : ℂ :=
  ∫ z in AVenhance.unitCube, planeBlochC θ g z * t z

theorem stageExp_integrable_phase (θ : Vec 2) {g : Vec 2 → ℝ} (hg : Integrable g) {t : Vec 2 → ℂ}
    (ht : t ∈ stageTests) :
    Integrable (fun y => Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) * (g y : ℂ) * t y) := by
  obtain ⟨hc, hp⟩ := ht
  obtain ⟨M, hM⟩ := exists_norm_bound_of_periodic hc hp
  have h := integrable_ofReal_mul_bdd hg ((planePhase_continuous θ).mul hc) (M := M)
    (fun y => by
      simp only [Pi.mul_apply, norm_mul, norm_planePhase, one_mul]
      exact hM y)
  exact h.congr (Filter.Eventually.of_forall fun y => by simp only [Pi.mul_apply]; ring)

/-- The cell pairing as a plane integral. -/
theorem stagePair_eq_plane (θ : Vec 2) {g : Vec 2 → ℝ} (hg : Integrable g) {t : Vec 2 → ℂ}
    (ht : t ∈ stageTests) :
    stagePair θ g t = ∫ y, Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) * (g y : ℂ) * t y := by
  obtain ⟨hc, hp⟩ := ht
  obtain ⟨M, hM⟩ := exists_norm_bound_of_periodic hc hp
  exact (integral_phase_mul_eq_cell_planeBlochC θ hg hc.aestronglyMeasurable hM hp).symm

theorem stagePair_sum_test (θ : Vec 2) {g : Vec 2 → ℝ} (hg : Integrable g) {ι' : Type*}
    (s : Finset ι') (f : ι' → Vec 2 → ℂ) (hf : ∀ a ∈ s, f a ∈ stageTests) :
    stagePair θ g (fun z => ∑ a ∈ s, f a z) = ∑ a ∈ s, stagePair θ g (f a) := by
  rw [stagePair_eq_plane θ hg (stageTests_sum_mem s f hf)]
  rw [Finset.sum_congr rfl fun a ha => stagePair_eq_plane θ hg (hf a ha)]
  rw [← integral_finsetSum _ fun a ha => stageExp_integrable_phase θ hg (hf a ha)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [Finset.mul_sum]

theorem stagePair_mul_test (θ : Vec 2) {g : Vec 2 → ℝ} (hg : Integrable g) (c : ℂ)
    {f : Vec 2 → ℂ} (hf : f ∈ stageTests) :
    stagePair θ g (fun z => c * f z) = c * stagePair θ g f := by
  rw [stagePair_eq_plane θ hg (stageTests_const_mul_mem c hf), stagePair_eq_plane θ hg hf,
    ← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => by simp only; ring)

theorem stagePair_zero (θ : Vec 2) (g : Vec 2 → ℝ) : stagePair θ g (fun _ => 0) = 0 := by
  simp [stagePair]

theorem stagePair_add_test (θ : Vec 2) {g : Vec 2 → ℝ} (hg : Integrable g) {f₁ f₂ : Vec 2 → ℂ}
    (h₁ : f₁ ∈ stageTests) (h₂ : f₂ ∈ stageTests) :
    stagePair θ g (fun z => f₁ z + f₂ z) = stagePair θ g f₁ + stagePair θ g f₂ := by
  have := stagePair_sum_test θ hg (Finset.univ : Finset (Fin 2)) (fun a => if a = 0 then f₁ else f₂)
    (fun a _ => by split_ifs <;> assumption)
  simpa [Fin.sum_univ_two] using this

/-- The cell pairing is linear in the integrable plane function (real coefficients). -/
theorem stagePair_sum_fun (θ : Vec 2) {ι' : Type*} (s : Finset ι') (G : ι' → Vec 2 → ℝ)
    (hG : ∀ a ∈ s, Integrable (G a)) (c : ι' → ℝ) {t : Vec 2 → ℂ} (ht : t ∈ stageTests) :
    stagePair θ (fun y => ∑ a ∈ s, c a * G a y) t = ∑ a ∈ s, (c a : ℂ) * stagePair θ (G a) t := by
  have hI : Integrable (fun y => ∑ a ∈ s, c a * G a y) :=
    integrable_finsetSum _ fun a ha => (hG a ha).const_mul (c a)
  rw [stagePair_eq_plane θ hI ht,
    Finset.sum_congr rfl fun a ha => by rw [stagePair_eq_plane θ (hG a ha) ht]]
  rw [Finset.sum_congr rfl fun a _ => (integral_const_mul (c a : ℂ) _).symm, ← integral_finsetSum]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => by ring
  · intro a ha
    have := (stageExp_integrable_phase θ (hG a ha) ht).const_mul (c a : ℂ)
    exact this

section Atom

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Basis expansion of the vector `e'` in the stage function. -/
theorem stageExp_basis_expand (θ : Vec 2) (τ : ℕ × ℕ) (e' : E) (g : Vec 2 → E)
    (hint : ∀ b : E, Integrable (fun y => momentWeight τ y * inner ℝ b (g y))) {t : Vec 2 → ℂ}
    (ht : t ∈ stageTests) :
    ∑ b : Fin (Module.finrank ℝ E), (inner ℝ e' (stdOrthonormalBasis ℝ E b) : ℂ) *
        stagePair θ (fun y => momentWeight τ y * inner ℝ (stdOrthonormalBasis ℝ E b) (g y)) t =
      stagePair θ (fun y => momentWeight τ y * inner ℝ e' (g y)) t := by
  have h := stagePair_sum_fun θ (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (fun b y => momentWeight τ y * inner ℝ (stdOrthonormalBasis ℝ E b) (g y))
    (fun b _ => hint _) (fun b => inner ℝ e' (stdOrthonormalBasis ℝ E b)) ht
  rw [← h]
  congr 1
  funext y
  rw [← (stdOrthonormalBasis ℝ E).sum_inner_mul_inner e' (g y), Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- Selecting one moment among the indicators. -/
theorem stageExp_select (θ : Vec 2) (N : ℕ) (τ : ℕ × ℕ) (hτ : τ ∈ momentIndices N) (c : ℂ)
    (e' : E) (g : Vec 2 → E)
    (hint : ∀ (β' : ℕ × ℕ) (b : E), Integrable (fun y => momentWeight β' y * inner ℝ b (g y)))
    {t : Vec 2 → ℂ} (ht : t ∈ stageTests) :
    ∑ β' : {β' // β' ∈ momentIndices N}, ∑ b : Fin (Module.finrank ℝ E),
      (if β'.1 = τ then c * (inner ℝ e' (stdOrthonormalBasis ℝ E b) : ℂ) *
        stagePair θ (fun y => momentWeight β'.1 y * inner ℝ (stdOrthonormalBasis ℝ E b) (g y)) t
        else 0) =
      c * stagePair θ (fun y => momentWeight τ y * inner ℝ e' (g y)) t := by
  rw [Finset.sum_eq_single (⟨τ, hτ⟩ : {β' // β' ∈ momentIndices N})]
  · simp only [ite_true]
    rw [← stageExp_basis_expand θ τ e' g (hint τ) ht, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  · intro β' _ hne
    refine Finset.sum_eq_zero fun b _ => ?_
    have : β'.1 ≠ τ := fun h => hne (Subtype.ext h)
    simp [this]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- A linear combination of tested pairings. -/
theorem stageExp_pair_lin (θ : Vec 2) {G : Vec 2 → ℝ} (hG : Integrable G) {ι' : Type*}
    (s : Finset ι') (C : ι' → Prop) [∀ a, Decidable (C a)] (δ : ℂ) (n : ℕ) (k : ι' → ℂ)
    (f : ι' → Vec 2 → ℂ) (hf : ∀ a ∈ s, f a ∈ stageTests) :
    stagePair θ G (fun z => δ * ((-1 : ℂ) ^ n * ∑ a ∈ s, if C a then k a * f a z else 0)) =
      δ * ((-1 : ℂ) ^ n * ∑ a ∈ s, if C a then k a * stagePair θ G (f a) else 0) := by
  have hm : ∀ a ∈ s, (fun z => if C a then k a * f a z else 0) ∈ stageTests :=
    fun a ha => stageTests_ite_mem (k a) (hf a ha)
  have h1 := stagePair_sum_test θ hG s (fun a z => if C a then k a * f a z else 0) hm
  have h2 : (fun z => ∑ a ∈ s, if C a then k a * f a z else 0) ∈ stageTests :=
    stageTests_sum_mem s _ hm
  have h3 := stagePair_mul_test θ hG ((-1 : ℂ) ^ n) h2
  have h4 := stagePair_mul_test θ hG δ (stageTests_const_mul_mem ((-1 : ℂ) ^ n) h2)
  rw [h4, h3, h1]
  congr 2
  refine Finset.sum_congr rfl fun a ha => ?_
  by_cases hC : C a
  · simp only [hC, ite_true]
    exact stagePair_mul_test θ hG (k a) (hf a ha)
  · simp only [hC, ite_false]
    exact stagePair_zero θ G

/-- **The basis expansion of one term of a letter.** -/
theorem stageExp_atom (θ : Vec 2) (N : ℕ) (β : ℕ × ℕ) (hβ : β.1 + β.2 ≤ N) (e' : E)
    (g : Vec 2 → E)
    (hint : ∀ (β' : ℕ × ℕ) (b : E), Integrable (fun y => momentWeight β' y * inner ℝ b (g y)))
    {n : ℕ} (α : DerivativeWord2 n) (c : Vec 2 → ℝ) (ψ : Vec 2 → ℂ)
    (hfp : ∀ b : ℕ × ℕ, b.1 + b.2 ≤ n →
      fibreCovPow (-θ) b (fun z' => (c z' : ℂ) * ψ z') ∈ stageTests) (δ : ℂ) :
    ∑ β' : {β' // β' ∈ momentIndices N}, ∑ b : Fin (Module.finrank ℝ E),
      stagePair θ (fun y => momentWeight β'.1 y * inner ℝ (stdOrthonormalBasis ℝ E b) (g y))
        (fun z => δ * ((-1 : ℂ) ^ n * ∑ a ∈ Finset.range ((wordCount α).1 + 1) ×ˢ
            Finset.range ((wordCount α).2 + 1),
          if β'.1 = (β.1 - a.1, β.2 - a.2) then
            (((wordCount α).1.choose a.1 * (wordCount α).2.choose a.2 *
                β.1.descFactorial a.1 * β.2.descFactorial a.2 : ℕ) : ℂ) *
              (inner ℝ e' (stdOrthonormalBasis ℝ E b) : ℂ) *
              fibreCovPow (-θ) ((wordCount α).1 - a.1, (wordCount α).2 - a.2)
                (fun z' => (c z' : ℂ) * ψ z') z
          else 0)) =
      δ * b1wJetPair θ β e' g c α ψ := by
  have hlin : ∀ (β' : {β' // β' ∈ momentIndices N}) (b : Fin (Module.finrank ℝ E)),
      stagePair θ (fun y => momentWeight β'.1 y * inner ℝ (stdOrthonormalBasis ℝ E b) (g y))
        (fun z => δ * ((-1 : ℂ) ^ n * ∑ a ∈ Finset.range ((wordCount α).1 + 1) ×ˢ
            Finset.range ((wordCount α).2 + 1),
          if β'.1 = (β.1 - a.1, β.2 - a.2) then
            (((wordCount α).1.choose a.1 * (wordCount α).2.choose a.2 *
                β.1.descFactorial a.1 * β.2.descFactorial a.2 : ℕ) : ℂ) *
              (inner ℝ e' (stdOrthonormalBasis ℝ E b) : ℂ) *
              fibreCovPow (-θ) ((wordCount α).1 - a.1, (wordCount α).2 - a.2)
                (fun z' => (c z' : ℂ) * ψ z') z
          else 0)) =
        δ * ((-1 : ℂ) ^ n * ∑ a ∈ Finset.range ((wordCount α).1 + 1) ×ˢ
            Finset.range ((wordCount α).2 + 1),
          if β'.1 = (β.1 - a.1, β.2 - a.2) then
            (((wordCount α).1.choose a.1 * (wordCount α).2.choose a.2 *
                β.1.descFactorial a.1 * β.2.descFactorial a.2 : ℕ) : ℂ) *
              (inner ℝ e' (stdOrthonormalBasis ℝ E b) : ℂ) *
              stagePair θ
                (fun y => momentWeight β'.1 y * inner ℝ (stdOrthonormalBasis ℝ E b) (g y))
                (fibreCovPow (-θ) ((wordCount α).1 - a.1, (wordCount α).2 - a.2)
                  (fun z' => (c z' : ℂ) * ψ z'))
          else 0) := fun β' b =>
    stageExp_pair_lin θ (hint _ _) (Finset.range ((wordCount α).1 + 1) ×ˢ
      Finset.range ((wordCount α).2 + 1)) (fun a => β'.1 = (β.1 - a.1, β.2 - a.2)) δ n
      (fun a => (((wordCount α).1.choose a.1 * (wordCount α).2.choose a.2 *
                β.1.descFactorial a.1 * β.2.descFactorial a.2 : ℕ) : ℂ) *
              (inner ℝ e' (stdOrthonormalBasis ℝ E b) : ℂ))
      (fun a => fibreCovPow (-θ) ((wordCount α).1 - a.1, (wordCount α).2 - a.2)
                (fun z' => (c z' : ℂ) * ψ z')) (fun a ha => hfp _ (by
        simp only [Finset.mem_product, Finset.mem_range] at ha
        have := wordCount_sum α
        omega))
  rw [Finset.sum_congr rfl fun β' _ => Finset.sum_congr rfl fun b _ => hlin β' b]
  simp only [← Finset.mul_sum]
  unfold b1wJetPair
  congr 2
  rw [Finset.sum_congr rfl fun β' _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hmem : (β.1 - a.1, β.2 - a.2) ∈ momentIndices N := by
    simp only [momentIndices, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  have hs := stageExp_select θ N (β.1 - a.1, β.2 - a.2) hmem
    (((wordCount α).1.choose a.1 * (wordCount α).2.choose a.2 *
                β.1.descFactorial a.1 * β.2.descFactorial a.2 : ℕ) : ℂ) e' g hint (hfp
      ((wordCount α).1 - a.1, (wordCount α).2 - a.2) (by
        simp only [Finset.mem_product, Finset.mem_range] at ha
        have := wordCount_sum α
        omega))
  rw [hs]
  rfl

end Atom

section Big

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D Nw : ℕ}
  {K : ScalarConstants} {g₁ : ℝ}

/-- The family of summands of a letter sum, from the component `x'` to the component `x`. -/
abbrev LetterArgs (D : ℕ) (x x' : ι) (M : Type*) : Type _ :=
  (d : ℕ) → d ∈ Finset.Icc 2 D → Constituent d (h x') (h x) → DerivativeWord2 (d - 1) → (s : ℕ) →
    DerivativeWord2 s → M

/-- The nested letter sum of the summand family `Φ`. -/
def letterBig (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (l : Fin Nw)
    (x x' : ι) {M : Type*} [AddCommMonoid M] (Φ : LetterArgs (h := h) D x x' M) : M :=
  ∑ d ∈ admissibleOrders (fun p : Fin (Nw + 1) × ι => F.κ p.1 p.2) D (l.succ, x) (l.castSucc, x'),
    if hd : d ∈ Finset.Icc 2 D then
      (((F.letters l).edge x x' ⟨d, hd⟩).map fun γ =>
        ∑ α : DerivativeWord2 (d - 1),
          ∑ s ∈ Finset.Icc (if (F.letters l).positive then 1 else 0) (F.letters l).slow,
            ∑ ω : DerivativeWord2 s, Φ d hd γ α s ω).sum
    else 0

variable (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (l : Fin Nw) (x x' : ι)

theorem letterBig_zero {M : Type*} [AddCommMonoid M] :
    letterBig F l x x' (fun _ _ _ _ _ _ => (0 : M)) = 0 := by
  unfold letterBig
  refine Finset.sum_eq_zero fun d _ => ?_
  by_cases hd : d ∈ Finset.Icc 2 D
  · simp only [hd, ↓reduceDIte]
    refine List.sum_eq_zero fun a ha => ?_
    obtain ⟨γ, _, rfl⟩ := List.mem_map.1 ha
    simp
  · simp only [hd, ↓reduceDIte]

theorem letterBig_add {M : Type*} [AddCommMonoid M] (Φ Ψ : LetterArgs (h := h) D x x' M) :
    letterBig F l x x' (fun d hd γ α s ω => Φ d hd γ α s ω + Ψ d hd γ α s ω) =
      letterBig F l x x' Φ + letterBig F l x x' Ψ := by
  unfold letterBig
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hd : d ∈ Finset.Icc 2 D
  · simp only [hd, ↓reduceDIte, Finset.sum_add_distrib, List.sum_map_add]
  · simp only [hd, ↓reduceDIte, add_zero]

theorem letterBig_finset_sum {M : Type*} [AddCommMonoid M] {κ : Type*} (S : Finset κ)
    (Φ : κ → LetterArgs (h := h) D x x' M) :
    letterBig F l x x' (fun d hd γ α s ω => ∑ n ∈ S, Φ n d hd γ α s ω) =
      ∑ n ∈ S, letterBig F l x x' (Φ n) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using letterBig_zero F l x x' (M := M)
  | insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    rw [← ih]
    exact letterBig_add F l x x' (Φ a) (fun d hd γ α s ω => ∑ n ∈ S, Φ n d hd γ α s ω)

theorem letterBig_map {M N : Type*} [AddCommMonoid M] [AddCommMonoid N] (f : M →+ N)
    (Φ : LetterArgs (h := h) D x x' M) :
    f (letterBig F l x x' Φ) = letterBig F l x x' (fun d hd γ α s ω => f (Φ d hd γ α s ω)) := by
  unfold letterBig
  rw [map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hd : d ∈ Finset.Icc 2 D
  · simp only [hd, ↓reduceDIte]
    rw [map_list_sum, List.map_map]
    congr 1
    refine List.map_congr_left fun γ _ => ?_
    simp only [Function.comp_apply, map_sum]
  · simp only [hd, ↓reduceDIte, map_zero]

theorem letterBig_congr {M : Type*} [AddCommMonoid M] (Φ Ψ : LetterArgs (h := h) D x x' M)
    (hΦΨ : ∀ d ∈ admissibleOrders (fun p : Fin (Nw + 1) × ι => F.κ p.1 p.2) D
        (l.succ, x) (l.castSucc, x'), ∀ hd : d ∈ Finset.Icc 2 D,
      ∀ γ ∈ (F.letters l).edge x x' ⟨d, hd⟩, ∀ α : DerivativeWord2 (d - 1),
      ∀ s ∈ Finset.Icc (if (F.letters l).positive then 1 else 0) (F.letters l).slow,
      ∀ ω : DerivativeWord2 s, Φ d hd γ α s ω = Ψ d hd γ α s ω) :
    letterBig F l x x' Φ = letterBig F l x x' Ψ := by
  unfold letterBig
  refine Finset.sum_congr rfl fun d hdm => ?_
  by_cases hd : d ∈ Finset.Icc 2 D
  · simp only [hd, ↓reduceDIte]
    congr 1
    refine List.map_congr_left fun γ hγ => ?_
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun s hs =>
      Finset.sum_congr rfl fun ω _ => hΦΨ d hdm hd γ hγ α s hs ω
  · simp only [hd, ↓reduceDIte]

/-- Evaluation at a point, on the continuous periodic tests. -/
def stageEvalHom (z : Vec 2) : stageTests →+ ℂ where
  toFun t := t.1 z
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The cell pairing against a fixed integrable function, on the tests. -/
def stagePairHom (θ : Vec 2) {G : Vec 2 → ℝ} (hG : Integrable G) : stageTests →+ ℂ where
  toFun t := stagePair θ G t.1
  map_zero' := stagePair_zero θ G
  map_add' a b := stagePair_add_test θ hG a.2 b.2

/-- **The cell pairing passes through the letter sum.** -/
theorem letterBig_pair (θ : Vec 2) {G : Vec 2 → ℝ} (hG : Integrable G)
    (Φ : LetterArgs (h := h) D x x' (Vec 2 → ℂ))
    (hΦ : ∀ d ∈ admissibleOrders (fun p : Fin (Nw + 1) × ι => F.κ p.1 p.2) D
        (l.succ, x) (l.castSucc, x'), ∀ hd : d ∈ Finset.Icc 2 D,
      ∀ γ ∈ (F.letters l).edge x x' ⟨d, hd⟩, ∀ α : DerivativeWord2 (d - 1),
      ∀ s ∈ Finset.Icc (if (F.letters l).positive then 1 else 0) (F.letters l).slow,
      ∀ ω : DerivativeWord2 s, Φ d hd γ α s ω ∈ stageTests) :
    (fun z => letterBig F l x x' (fun d hd γ α s ω => Φ d hd γ α s ω z)) ∈ stageTests ∧
      stagePair θ G (fun z => letterBig F l x x' (fun d hd γ α s ω => Φ d hd γ α s ω z)) =
        letterBig F l x x' (fun d hd γ α s ω => stagePair θ G (Φ d hd γ α s ω)) := by
  classical
  let Φ' : LetterArgs (h := h) D x x' stageTests := fun d hd γ α s ω =>
    if hm : Φ d hd γ α s ω ∈ stageTests then ⟨Φ d hd γ α s ω, hm⟩ else 0
  have hΦ' : ∀ d ∈ admissibleOrders (fun p : Fin (Nw + 1) × ι => F.κ p.1 p.2) D
        (l.succ, x) (l.castSucc, x'), ∀ hd : d ∈ Finset.Icc 2 D,
      ∀ γ ∈ (F.letters l).edge x x' ⟨d, hd⟩, ∀ α : DerivativeWord2 (d - 1),
      ∀ s ∈ Finset.Icc (if (F.letters l).positive then 1 else 0) (F.letters l).slow,
      ∀ ω : DerivativeWord2 s, (Φ' d hd γ α s ω).1 = Φ d hd γ α s ω := by
    intro d hdm hd γ hγ α s hs ω
    simp [Φ', hΦ d hdm hd γ hγ α s hs ω]
  set B := letterBig F l x x' Φ' with hB
  have hfun : (fun z => letterBig F l x x' (fun d hd γ α s ω => Φ d hd γ α s ω z)) = B.1 := by
    funext z
    have := letterBig_map F l x x' (stageEvalHom z) Φ'
    refine Eq.trans ?_ this.symm
    exact letterBig_congr F l x x' _ _ fun d hdm hd γ hγ α s hs ω =>
      (congrFun (hΦ' d hdm hd γ hγ α s hs ω) z).symm
  refine ⟨hfun ▸ B.2, ?_⟩
  rw [hfun]
  have := letterBig_map F l x x' (stagePairHom θ hG) Φ'
  refine Eq.trans this ?_
  exact letterBig_congr F l x x' _ _ fun d hdm hd γ hγ α s hs ω => by
    show stagePair θ G (Φ' d hd γ α s ω).1 = _
    rw [hΦ' d hdm hd γ hγ α s hs ω]

end Big

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Filter Topology Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords.Assembly

/-! # The letter Bloch identity: one weak letter

The weak forms `integral_phase_moment_weakDeriv` and `cell_moment_weakDeriv` of the one-letter
integration by parts: the function `g` has a weak partial derivative `gk` in the direction `k`
instead of a classical one. The weighted
field `y^β g` has the weak derivative `y^β gk + β_k y^{β - e_k} g` (weak product rule with the
smooth weight), and `weak_ibp_bdd_complex` pairs it with the bounded `C¹` test `e^{-iθ·y} φ`. -/

/-- **Weak integration by parts against a bounded `C¹` test** (complex form). -/
theorem weak_ibp_bdd_complex {u gi : Vec 2 → ℝ} {k : Fin 2}
    (hw : HasWeakPartialDerivOn univ k u gi) (hu : Integrable u) (hgi : Integrable gi)
    {ψ : Vec 2 → ℂ} (hψ : ContDiff ℝ 1 ψ) {M : ℝ} (hb : ∀ y, ‖ψ y‖ ≤ M)
    (hd : ∀ y, ‖fderiv ℝ ψ y (basisVec k)‖ ≤ M) :
    ∫ y, (u y : ℂ) * fderiv ℝ ψ y (basisVec k) = -∫ y, (gi y : ℂ) * ψ y := by
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hre : ∀ y v, fderiv ℝ (fun y => (ψ y).re) y v = (fderiv ℝ ψ y v).re := fun y v => by
    have h := Complex.reCLM.hasFDerivAt.comp y (hψd y).hasFDerivAt
    rw [show (fun y => (ψ y).re) = Complex.reCLM ∘ ψ from rfl, h.fderiv]
    rfl
  have him : ∀ y v, fderiv ℝ (fun y => (ψ y).im) y v = (fderiv ℝ ψ y v).im := fun y v => by
    have h := Complex.imCLM.hasFDerivAt.comp y (hψd y).hasFDerivAt
    rw [show (fun y => (ψ y).im) = Complex.imCLM ∘ ψ from rfl, h.fderiv]
    rfl
  have hdc : Continuous (fun y => fderiv ℝ ψ y (basisVec k)) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have I1 : Integrable (fun y => (u y : ℂ) * fderiv ℝ ψ y (basisVec k)) :=
    integrable_ofReal_mul_bdd hu hdc hd
  have I2 : Integrable (fun y => (gi y : ℂ) * ψ y) := integrable_ofReal_mul_bdd hgi hψ.continuous hb
  have hreC : ContDiff ℝ 1 (fun y => (ψ y).re) := Complex.reCLM.contDiff.comp hψ
  have himC : ContDiff ℝ 1 (fun y => (ψ y).im) := Complex.imCLM.contDiff.comp hψ
  have e1 := weak_ibp_bdd_real hw hu hgi hreC (M := M) (fun y => (Complex.abs_re_le_norm _).trans (hb y))
    (fun y => by rw [hre]; exact (Complex.abs_re_le_norm _).trans (hd y))
  have e2 := weak_ibp_bdd_real hw hu hgi himC (M := M) (fun y => (Complex.abs_im_le_norm _).trans (hb y))
    (fun y => by rw [him]; exact (Complex.abs_im_le_norm _).trans (hd y))
  simp only [hre, him] at e1 e2
  apply Complex.ext
  · have h1 := integral_re I1
    have h2 := integral_re I2
    simp only [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] at h1 h2
    rw [Complex.neg_re, ← h1, ← h2]
    exact e1
  · have h1 := integral_im I1
    have h2 := integral_im I2
    simp only [RCLike.im_to_complex, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero] at h1 h2
    rw [Complex.neg_im, ← h1, ← h2]
    exact e2

/-- The weighted field `y^β g` has the weak derivative `y^β gk + β_k y^{β - e_k} g`. -/
theorem weak_deriv_momentWeight_mul (β : ℕ × ℕ) (k : Fin 2) {g gk : Vec 2 → ℝ}
    (hw : HasWeakPartialDerivOn univ k g gk) (hi0 : Integrable g) (hk0 : Integrable gk) :
    HasWeakPartialDerivOn univ k (fun y => momentWeight β y * g y)
      (fun y => momentWeight β y * gk y +
        (momentIndex β k : ℝ) * (momentWeight (momentShift β k) y * g y)) := by
  have h := hasWeakPartialDerivOn_mul_contDiff_one hw hi0.locallyIntegrable
    hk0.locallyIntegrable (c := momentWeight β) ((momentWeight_contDiff β).of_le (by simp))
  convert h using 2 with y
  rw [fderiv_momentWeight]
  ring

/-- **One weak letter on the plane.** -/
theorem integral_phase_moment_weakDeriv (θ : Vec 2) (β : ℕ × ℕ) (k : Fin 2) {g gk : Vec 2 → ℝ}
    (hw : HasWeakPartialDerivOn univ k g gk) (hi0 : Integrable g) (hk0 : Integrable gk)
    (hi1 : Integrable (fun y => momentWeight β y * g y))
    (hi2 : Integrable (fun y => momentWeight β y * gk y))
    (hi3 : Integrable (fun y => momentWeight (momentShift β k) y * g y))
    {φ : Vec 2 → ℂ} (hφ : ContDiff ℝ (1 : ℕ) φ) (hp : AVenhance.IsZ2Periodic φ) :
    ∫ y, Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
        ((momentWeight β y * gk y : ℝ) : ℂ) * φ y =
      -(∫ y, Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
          ((momentWeight β y * g y : ℝ) : ℂ) * fibreCovDeriv (-θ) k φ y) -
        (momentIndex β k : ℂ) * ∫ y, Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
          ((momentWeight (momentShift β k) y * g y : ℝ) : ℂ) * φ y := by
  set e : Vec 2 → ℂ := fun y => Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) with he
  set ψ : Vec 2 → ℂ := fun y => e y * φ y with hψ
  have hec : Continuous e := planePhase_continuous θ
  have hφc : Continuous φ := hφ.continuous
  have hφd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  obtain ⟨Mφ, hMφ⟩ := exists_norm_bound_of_periodic hφc hp
  have hDc : Continuous (fibreCovDeriv (-θ) k φ) :=
    (contDiff_fibreCovDeriv (j := 0) (by simpa using hφ) (-θ) k).continuous
  obtain ⟨MD, hMD⟩ := exists_norm_bound_of_periodic hDc (isZ2Periodic_fibreCovDeriv hp (-θ) k)
  have hψc : Continuous ψ := hec.mul hφc
  have hψb : ∀ y, ‖ψ y‖ ≤ Mφ := fun y => by
    simp only [hψ, he, norm_mul, norm_planePhase, one_mul]
    exact hMφ y
  have hψd : ∀ y, fderiv ℝ ψ y (basisVec k) = e y * fibreCovDeriv (-θ) k φ y := fun y =>
    fderiv_phase_mul θ y (hφd y) k
  have hψDb : ∀ y, ‖fderiv ℝ ψ y (basisVec k)‖ ≤ MD := fun y => by
    rw [hψd]
    simp only [he, norm_mul, norm_planePhase, one_mul]
    exact hMD y
  have hψC1 : ContDiff ℝ 1 ψ := by
    have : ContDiff ℝ 1 e := by
      have : ContDiff ℝ 1 fun y : Vec 2 => vecDot θ y := by unfold vecDot; fun_prop
      exact Complex.contDiff_exp.comp
        ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp this)).neg)
    exact this.mul hφ
  have hFw := weak_deriv_momentWeight_mul β k hw hi0 hk0
  have hiF' : Integrable (fun y => momentWeight β y * gk y +
      (momentIndex β k : ℝ) * (momentWeight (momentShift β k) y * g y)) :=
    hi2.add (hi3.const_mul _)
  have hibp := weak_ibp_bdd_complex hFw hi1 hiF' hψC1 (M := max Mφ MD) (fun y => (hψb y).trans (le_max_left _ _))
    (fun y => (hψDb y).trans (le_max_right _ _))
  have hD : Integrable fun y => ((momentWeight (momentShift β k) y * g y : ℝ) : ℂ) * ψ y :=
    integrable_ofReal_mul_bdd hi3 hψc hψb
  have hA : Integrable fun y => ((momentWeight β y * gk y : ℝ) : ℂ) * ψ y :=
    integrable_ofReal_mul_bdd hi2 hψc hψb
  have hI : ∫ y, ((momentWeight β y * g y : ℝ) : ℂ) * fderiv ℝ ψ y (basisVec k) =
      -∫ y, (((momentWeight β y * gk y +
        (momentIndex β k : ℝ) * (momentWeight (momentShift β k) y * g y) : ℝ)) : ℂ) * ψ y :=
    hibp
  have hsplit : ∫ y, (((momentWeight β y * gk y +
        (momentIndex β k : ℝ) * (momentWeight (momentShift β k) y * g y) : ℝ)) : ℂ) * ψ y =
      (∫ y, ((momentWeight β y * gk y : ℝ) : ℂ) * ψ y) + (momentIndex β k : ℂ) *
        ∫ y, ((momentWeight (momentShift β k) y * g y : ℝ) : ℂ) * ψ y := by
    rw [← integral_const_mul, ← integral_add hA (hD.const_mul _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    push_cast
    ring
  have hL : ∫ y, e y * ((momentWeight β y * gk y : ℝ) : ℂ) * φ y =
      ∫ y, ((momentWeight β y * gk y : ℝ) : ℂ) * ψ y :=
    integral_congr_ae (Filter.Eventually.of_forall fun y => by simp only [hψ]; ring)
  have hR1 : ∫ y, e y * ((momentWeight β y * g y : ℝ) : ℂ) * fibreCovDeriv (-θ) k φ y =
      ∫ y, ((momentWeight β y * g y : ℝ) : ℂ) * fderiv ℝ ψ y (basisVec k) :=
    integral_congr_ae (Filter.Eventually.of_forall fun y => by simp only [hψd]; ring)
  have hR2 : ∫ y, e y * ((momentWeight (momentShift β k) y * g y : ℝ) : ℂ) * φ y =
      ∫ y, ((momentWeight (momentShift β k) y * g y : ℝ) : ℂ) * ψ y :=
    integral_congr_ae (Filter.Eventually.of_forall fun y => by simp only [hψ]; ring)
  show ∫ y, e y * ((momentWeight β y * gk y : ℝ) : ℂ) * φ y =
    -(∫ y, e y * ((momentWeight β y * g y : ℝ) : ℂ) * fibreCovDeriv (-θ) k φ y) -
      (momentIndex β k : ℂ) * ∫ y, e y * ((momentWeight (momentShift β k) y * g y : ℝ) : ℂ) * φ y
  rw [hL, hR1, hR2, hI, hsplit]
  ring

/-- **One weak letter in the cell.** -/
theorem cell_moment_weakDeriv (θ : Vec 2) (β : ℕ × ℕ) (k : Fin 2) {g gk : Vec 2 → ℝ}
    (hw : HasWeakPartialDerivOn univ k g gk) (hi0 : Integrable g) (hk0 : Integrable gk)
    (hi1 : Integrable (fun y => momentWeight β y * g y))
    (hi2 : Integrable (fun y => momentWeight β y * gk y))
    (hi3 : Integrable (fun y => momentWeight (momentShift β k) y * g y))
    {φ : Vec 2 → ℂ} (hφ : ContDiff ℝ (1 : ℕ) φ) (hp : AVenhance.IsZ2Periodic φ) :
    ∫ z in AVenhance.unitCube,
        planeBlochC θ (fun y => momentWeight β y * gk y) z * φ z =
      -(∫ z in AVenhance.unitCube, planeBlochC θ (fun y => momentWeight β y * g y) z *
          fibreCovDeriv (-θ) k φ z) -
        (momentIndex β k : ℂ) * ∫ z in AVenhance.unitCube,
          planeBlochC θ (fun y => momentWeight (momentShift β k) y * g y) z * φ z := by
  obtain ⟨Mφ, hMφ⟩ := exists_norm_bound_of_periodic hφ.continuous hp
  have hDc : Continuous (fibreCovDeriv (-θ) k φ) :=
    (contDiff_fibreCovDeriv (j := 0) (by simpa using hφ) (-θ) k).continuous
  obtain ⟨MD, hMD⟩ := exists_norm_bound_of_periodic hDc (isZ2Periodic_fibreCovDeriv hp (-θ) k)
  rw [← integral_phase_mul_eq_cell_planeBlochC θ hi2 hφ.continuous.aestronglyMeasurable hMφ hp,
    ← integral_phase_mul_eq_cell_planeBlochC θ hi1 hDc.aestronglyMeasurable hMD
      (isZ2Periodic_fibreCovDeriv hp (-θ) k),
    ← integral_phase_mul_eq_cell_planeBlochC θ hi3 hφ.continuous.aestronglyMeasurable hMφ hp]
  exact integral_phase_moment_weakDeriv θ β k hw hi0 hk0 hi1 hi2 hi3 hφ hp

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords.Assembly

/-! # The letter Bloch identity: the weak jet-to-value transfer

The jet-to-value transfer with classical derivatives replaced by a family `G m w` of real functions
with weak partial derivatives `∂_i (G m w) = G (m+1) (w·i)` (the ordered weak jets of a `PlaneHk`
function). The induction peels the first letter of the word: `w = a·w'` and the family
`G' m w'' = G (m+1) (a·w'')` is again such a family, whose base is the weak derivative `G 1 (a)` of
`G 0 ()`. -/

/-- One weak letter `k` at weight `β - a` and test `D^{c'-a} φ`. -/
theorem transferInt_weakLetter (θ : Vec 2) {n : ℕ} (c' β a : ℕ × ℕ)
    (hca : a.1 ≤ c'.1 ∧ a.2 ≤ c'.2) (hc' : c'.1 + c'.2 = n) {h gk : Vec 2 → ℝ} (k : Fin 2)
    (hw : HasWeakPartialDerivOn univ k h gk)
    (hh : ∀ γ : ℕ × ℕ, γ ≤ β → Integrable (fun y => momentWeight γ y * h y))
    (hg : ∀ γ : ℕ × ℕ, γ ≤ β → Integrable (fun y => momentWeight γ y * gk y))
    {φ : Vec 2 → ℂ} (hφ : ContDiff ℝ (n + 1 : ℕ) φ) (hp : AVenhance.IsZ2Periodic φ) :
    transferInt θ c' β gk φ a =
      -(∫ z in AVenhance.unitCube,
          planeBlochC θ (fun y => momentWeight (β.1 - a.1, β.2 - a.2) y * h y) z *
            fibreCovPow (-θ) (if k = 0 then (c'.1 - a.1 + 1, c'.2 - a.2)
              else (c'.1 - a.1, c'.2 - a.2 + 1)) φ z) -
        (momentIndex (β.1 - a.1, β.2 - a.2) k : ℂ) * ∫ z in AVenhance.unitCube,
          planeBlochC θ (fun y => momentWeight (momentShift (β.1 - a.1, β.2 - a.2) k) y * h y) z *
            fibreCovPow (-θ) (c'.1 - a.1, c'.2 - a.2) φ z := by
  have hle : ((β.1 - a.1, β.2 - a.2) : ℕ × ℕ) ≤ β :=
    Prod.mk_le_mk.2 ⟨Nat.sub_le _ _, Nat.sub_le _ _⟩
  have hle' : momentShift (β.1 - a.1, β.2 - a.2) k ≤ β := by
    unfold momentShift
    split_ifs
    · exact Prod.mk_le_mk.2 ⟨by omega, Nat.sub_le _ _⟩
    · exact Prod.mk_le_mk.2 ⟨Nat.sub_le _ _, by omega⟩
  have hi0 : Integrable h := by simpa [momentWeight] using hh (0, 0) (Prod.mk_le_mk.2 ⟨by omega, by omega⟩)
  have hk0 : Integrable gk := by simpa [momentWeight] using hg (0, 0) (Prod.mk_le_mk.2 ⟨by omega, by omega⟩)
  have hφb : ContDiff ℝ ((c'.1 - a.1, c'.2 - a.2).1 + (c'.1 - a.1, c'.2 - a.2).2 + 1 : ℕ) φ :=
    hφ.of_le (by norm_cast; dsimp only; omega)
  have hψ : ContDiff ℝ (1 : ℕ) (fibreCovPow (-θ) (c'.1 - a.1, c'.2 - a.2) φ) :=
    contDiff_fibreCovPow (-θ) _ 1 (hφ.of_le (by norm_cast; dsimp only; omega))
  have h1 := cell_moment_weakDeriv θ (β.1 - a.1, β.2 - a.2) k hw hi0 hk0 (hh _ hle) (hg _ hle)
    (hh _ hle') hψ (isZ2Periodic_fibreCovPow (-θ) _ hp)
  rw [fibreCovDeriv_fibreCovPow (-θ) k _ hφb] at h1
  simp only [transferInt]
  exact h1

/-- **A weak letter `0`** in front of the word. -/
theorem transfer_weakStep_zero (θ : Vec 2) {n : ℕ} (c' β : ℕ × ℕ) (hc' : c'.1 + c'.2 = n)
    {h gk : Vec 2 → ℝ} (hw : HasWeakPartialDerivOn univ 0 h gk)
    (hh : ∀ γ : ℕ × ℕ, γ ≤ β → Integrable (fun y => momentWeight γ y * h y))
    (hg : ∀ γ : ℕ × ℕ, γ ≤ β → Integrable (fun y => momentWeight γ y * gk y))
    {φ : Vec 2 → ℂ} (hφ : ContDiff ℝ (n + 1 : ℕ) φ) (hp : AVenhance.IsZ2Periodic φ) :
    (-1 : ℂ) ^ n * transferSum c' β (transferInt θ c' β gk φ) =
      (-1 : ℂ) ^ (n + 1) *
        transferSum (c'.1 + 1, c'.2) β (transferInt θ (c'.1 + 1, c'.2) β h φ) := by
  rw [transferSum_step_zero]
  unfold transferSum
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hca : a.1 ≤ c'.1 ∧ a.2 ≤ c'.2 := by
    simp only [Finset.mem_product, Finset.mem_range] at ha
    omega
  rw [transferInt_weakLetter θ c' β a hca hc' 0 hw hh hg hφ hp]
  have e1 : transferInt θ (c'.1 + 1, c'.2) β h φ a = ∫ z in AVenhance.unitCube,
      planeBlochC θ (fun y => momentWeight (β.1 - a.1, β.2 - a.2) y * h y) z *
        fibreCovPow (-θ) (c'.1 - a.1 + 1, c'.2 - a.2) φ z := by
    show ∫ z in AVenhance.unitCube,
        planeBlochC θ (fun y => momentWeight (β.1 - a.1, β.2 - a.2) y * h y) z *
          fibreCovPow (-θ) (c'.1 + 1 - a.1, c'.2 - a.2) φ z = _
    rw [show c'.1 + 1 - a.1 = c'.1 - a.1 + 1 by omega]
  have e2 : transferInt θ (c'.1 + 1, c'.2) β h φ (a.1 + 1, a.2) = ∫ z in AVenhance.unitCube,
      planeBlochC θ (fun y => momentWeight (momentShift (β.1 - a.1, β.2 - a.2) 0) y * h y) z *
        fibreCovPow (-θ) (c'.1 - a.1, c'.2 - a.2) φ z := by
    show ∫ z in AVenhance.unitCube,
        planeBlochC θ (fun y => momentWeight (β.1 - (a.1 + 1), β.2 - a.2) y * h y) z *
          fibreCovPow (-θ) (c'.1 + 1 - (a.1 + 1), c'.2 - a.2) φ z = _
    have hs : momentShift (β.1 - a.1, β.2 - a.2) 0 = (β.1 - (a.1 + 1), β.2 - a.2) :=
      Prod.ext (by simp [momentShift]; omega) (by simp [momentShift])
    rw [show c'.1 + 1 - (a.1 + 1) = c'.1 - a.1 by omega, hs]
  have e3 : (momentIndex (β.1 - a.1, β.2 - a.2) 0 : ℂ) = ((β.1 - a.1 : ℕ) : ℂ) := by
    simp [momentIndex]
  simp only [↓reduceIte]
  rw [e1, e2, e3]
  ring

/-- **A weak letter `1`** in front of the word. -/
theorem transfer_weakStep_one (θ : Vec 2) {n : ℕ} (c' β : ℕ × ℕ) (hc' : c'.1 + c'.2 = n)
    {h gk : Vec 2 → ℝ} (hw : HasWeakPartialDerivOn univ 1 h gk)
    (hh : ∀ γ : ℕ × ℕ, γ ≤ β → Integrable (fun y => momentWeight γ y * h y))
    (hg : ∀ γ : ℕ × ℕ, γ ≤ β → Integrable (fun y => momentWeight γ y * gk y))
    {φ : Vec 2 → ℂ} (hφ : ContDiff ℝ (n + 1 : ℕ) φ) (hp : AVenhance.IsZ2Periodic φ) :
    (-1 : ℂ) ^ n * transferSum c' β (transferInt θ c' β gk φ) =
      (-1 : ℂ) ^ (n + 1) *
        transferSum (c'.1, c'.2 + 1) β (transferInt θ (c'.1, c'.2 + 1) β h φ) := by
  rw [transferSum_step_one]
  unfold transferSum
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hca : a.1 ≤ c'.1 ∧ a.2 ≤ c'.2 := by
    simp only [Finset.mem_product, Finset.mem_range] at ha
    omega
  rw [transferInt_weakLetter θ c' β a hca hc' 1 hw hh hg hφ hp]
  have e1 : transferInt θ (c'.1, c'.2 + 1) β h φ a = ∫ z in AVenhance.unitCube,
      planeBlochC θ (fun y => momentWeight (β.1 - a.1, β.2 - a.2) y * h y) z *
        fibreCovPow (-θ) (c'.1 - a.1, c'.2 - a.2 + 1) φ z := by
    show ∫ z in AVenhance.unitCube,
        planeBlochC θ (fun y => momentWeight (β.1 - a.1, β.2 - a.2) y * h y) z *
          fibreCovPow (-θ) (c'.1 - a.1, c'.2 + 1 - a.2) φ z = _
    rw [show c'.2 + 1 - a.2 = c'.2 - a.2 + 1 by omega]
  have e2 : transferInt θ (c'.1, c'.2 + 1) β h φ (a.1, a.2 + 1) = ∫ z in AVenhance.unitCube,
      planeBlochC θ (fun y => momentWeight (momentShift (β.1 - a.1, β.2 - a.2) 1) y * h y) z *
        fibreCovPow (-θ) (c'.1 - a.1, c'.2 - a.2) φ z := by
    show ∫ z in AVenhance.unitCube,
        planeBlochC θ (fun y => momentWeight (β.1 - a.1, β.2 - (a.2 + 1)) y * h y) z *
          fibreCovPow (-θ) (c'.1 - a.1, c'.2 + 1 - (a.2 + 1)) φ z = _
    have hs : momentShift (β.1 - a.1, β.2 - a.2) 1 = (β.1 - a.1, β.2 - (a.2 + 1)) :=
      Prod.ext (by simp [momentShift]) (by simp [momentShift]; omega)
    rw [show c'.2 + 1 - (a.2 + 1) = c'.2 - a.2 by omega, hs]
  have e3 : (momentIndex (β.1 - a.1, β.2 - a.2) 1 : ℂ) = ((β.2 - a.2 : ℕ) : ℂ) := by
    simp [momentIndex]
  have hif : ((if (1 : Fin 2) = 0 then (c'.1 - a.1 + 1, c'.2 - a.2)
      else (c'.1 - a.1, c'.2 - a.2 + 1)) : ℕ × ℕ) = (c'.1 - a.1, c'.2 - a.2 + 1) := by
    simp
  rw [hif, e1, e2, e3]
  ring

/-- The weak transfer, by induction on the word, for a weak jet family. -/
theorem weakJet_aux (θ : Vec 2) : ∀ (n : ℕ) (G : ∀ m : ℕ, DerivativeWord2 m → Vec 2 → ℝ)
    (β : ℕ × ℕ),
    (∀ m < n, ∀ (w : DerivativeWord2 m) (i : Fin 2),
      HasWeakPartialDerivOn univ i (G m w) (G (m + 1) (Fin.snoc w i))) →
    (∀ m ≤ n, ∀ (w : DerivativeWord2 m) (γ : ℕ × ℕ), γ ≤ β →
      Integrable (fun y => momentWeight γ y * G m w y)) →
    ∀ (w : DerivativeWord2 n) (φ : Vec 2 → ℂ), ContDiff ℝ (n : ℕ) φ → AVenhance.IsZ2Periodic φ →
      ∫ z in AVenhance.unitCube,
          planeBlochC θ (fun y => momentWeight β y * G n w y) z * φ z =
        (-1 : ℂ) ^ n * transferSum (wordCount w) β
          (transferInt θ (wordCount w) β (G 0 Fin.elim0) φ)
  | 0, G, β, _, _, w, φ, _, _ => by
    have hw : w = Fin.elim0 := Subsingleton.elim _ _
    subst hw
    rw [wordCount_nil]
    simp [transferSum, transferCoef, transferInt, fibreCovPow]
  | n + 1, G, β, hstep, hint, w, φ, hφ, hp => by
    obtain ⟨a, w', rfl⟩ : ∃ a w', w = (Fin.cons a w' : DerivativeWord2 (n + 1)) :=
      ⟨w 0, Fin.tail w, (Fin.cons_self_tail w).symm⟩
    let G' : ∀ m : ℕ, DerivativeWord2 m → Vec 2 → ℝ := fun m w'' => G (m + 1) (Fin.cons a w'')
    have hstep' : ∀ m < n, ∀ (w'' : DerivativeWord2 m) (i : Fin 2),
        HasWeakPartialDerivOn univ i (G' m w'') (G' (m + 1) (Fin.snoc w'' i)) := by
      intro m hm w'' i
      show HasWeakPartialDerivOn univ i (G (m + 1) (Fin.cons a w''))
        (G (m + 1 + 1) (Fin.cons a (Fin.snoc w'' i)))
      rw [Fin.cons_snoc_eq_snoc_cons]
      exact hstep (m + 1) (by omega) (Fin.cons a w'') i
    have hint' : ∀ m ≤ n, ∀ (w'' : DerivativeWord2 m) (γ : ℕ × ℕ), γ ≤ β →
        Integrable (fun y => momentWeight γ y * G' m w'' y) := fun m hm w'' γ hγ =>
      hint (m + 1) (by omega) _ γ hγ
    have IH : ∫ z in AVenhance.unitCube,
        planeBlochC θ (fun y => momentWeight β y * G (n + 1) (Fin.cons a w') y) z * φ z =
        (-1 : ℂ) ^ n * transferSum (wordCount w') β
          (transferInt θ (wordCount w') β (G' 0 Fin.elim0) φ) :=
      weakJet_aux θ n G' β hstep' hint' w' φ (hφ.of_le (by norm_cast; omega)) hp
    have hgk : HasWeakPartialDerivOn univ a (G 0 Fin.elim0) (G' 0 Fin.elim0) := by
      have h0 := hstep 0 (by omega) Fin.elim0 a
      have e : (Fin.snoc Fin.elim0 a : DerivativeWord2 1) = Fin.cons a Fin.elim0 := by
        funext i
        fin_cases i
        rfl
      rw [e] at h0
      exact h0
    have hh : ∀ γ : ℕ × ℕ, γ ≤ β → Integrable (fun y => momentWeight γ y * G 0 Fin.elim0 y) :=
      fun γ hγ => hint 0 (Nat.zero_le _) _ γ hγ
    have hg : ∀ γ : ℕ × ℕ, γ ≤ β → Integrable (fun y => momentWeight γ y * G' 0 Fin.elim0 y) :=
      fun γ hγ => hint' 0 (Nat.zero_le _) _ γ hγ
    rw [IH, wordCount_cons]
    fin_cases a
    · exact transfer_weakStep_zero θ (wordCount w') β (wordCount_sum w') hgk hh hg hφ hp
    · exact transfer_weakStep_one θ (wordCount w') β (wordCount_sum w') hgk hh hg hφ hp

/-! # The letter Bloch identity: `WeakJetToValue`

The ordered weak jets of a `PlaneHk` function, paired with a fixed vector `e'`, form a weak jet
family `G m w = ⟨e', jet_m w⟩` for `m < K`; `weakJet_aux` then gives the transfer, which is
`b1wJetPair` for the test `c ψ`. -/

section
universe v

theorem weakJetToValue : WeakJetToValue.{v} := by
  intro E _ _ _ _ _ _ θ K n hn w β W e' hint c ψ hc hcp hψ hψp
  let G : ∀ m : ℕ, DerivativeWord2 m → Vec 2 → ℝ :=
    fun m w' y => inner ℝ e' (planeJetOrder W m w' y)
  have hstep : ∀ m < n, ∀ (w' : DerivativeWord2 m) (i : Fin 2),
      HasWeakPartialDerivOn univ i (G m w') (G (m + 1) (Fin.snoc w' i)) := by
    intro m hm w' i
    have hmK : m < K := lt_of_lt_of_le hm hn
    have h := W.toFunction.hasWeakJet ⟨m, hmK⟩ w' i e'
    have e1 : planeJetOrder W m w' = W.toFunction.jet (lowerIndex2 ⟨m, hmK⟩ w') := by
      funext y
      simp [planeJetOrder, Nat.le_of_lt hmK, lowerIndex2, lowerIndex]
    have e2 : planeJetOrder W (m + 1) (Fin.snoc w' i) =
        W.toFunction.jet (nextIndex2 ⟨m, hmK⟩ w' i) := by
      funext y
      simp [planeJetOrder, Nat.succ_le_of_lt hmK, nextIndex2, nextIndex]
    show HasWeakPartialDerivOn univ i (fun y => inner ℝ e' (planeJetOrder W m w' y))
      (fun y => inner ℝ e' (planeJetOrder W (m + 1) (Fin.snoc w' i) y))
    rw [e1, e2]
    exact h
  have hint' : ∀ m ≤ n, ∀ (w' : DerivativeWord2 m) (γ : ℕ × ℕ), γ ≤ β →
      Integrable (fun y => momentWeight γ y * G m w' y) := by
    intro m _ w' γ _
    have := (innerSL ℝ e').integrable_comp (hint γ m w')
    simpa [G, real_inner_smul_right] using this
  have hφ : ContDiff ℝ (n : ℕ) (fun z => (c z : ℂ) * ψ z) :=
    (Complex.ofRealCLM.contDiff.comp hc).mul hψ
  have hφp : AVenhance.IsZ2Periodic (fun z => (c z : ℂ) * ψ z) := fun k z => by
    simp only [hcp k z, hψp k z]
  have h := weakJet_aux θ n G β hstep hint' w _ hφ hφp
  unfold b1wJetPair
  rw [h]
  rfl
end

/-! # The letter Bloch identity: periodization algebra, clauses 1 and 3, integrability -/

section
universe u v

section Periodization

/-- A phase pairing of an integrable real function with a continuous periodic test is
integrable. -/
theorem integrable_phase_pairing (θ : Vec 2) {g : Vec 2 → ℝ} (hg : Integrable g) {ψ : Vec 2 → ℂ}
    (hc : Continuous ψ) (hp : AVenhance.IsZ2Periodic ψ) :
    Integrable (fun y => Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) * (g y : ℂ) * ψ y) := by
  obtain ⟨M, hM⟩ := exists_norm_bound_of_periodic hc hp
  have h := integrable_ofReal_mul_bdd hg ((planePhase_continuous θ).mul hc) (M := M)
    (fun y => by
      simp only [Pi.mul_apply, norm_mul, norm_planePhase, one_mul]
      exact hM y)
  exact h.congr (Filter.Eventually.of_forall fun y => by simp only [Pi.mul_apply]; ring)

/-- The cell pairing as a plane integral. -/
theorem cell_pair_eq_plane (θ : Vec 2) {g : Vec 2 → ℝ} (hg : Integrable g) {ψ : Vec 2 → ℂ}
    (hc : Continuous ψ) (hp : AVenhance.IsZ2Periodic ψ) :
    ∫ z in AVenhance.unitCube, planeBlochC θ g z * ψ z =
      ∫ y, Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) * (g y : ℂ) * ψ y := by
  obtain ⟨M, hM⟩ := exists_norm_bound_of_periodic hc hp
  exact (integral_phase_mul_eq_cell_planeBlochC θ hg hc.aestronglyMeasurable hM hp).symm

theorem cell_pair_add (θ : Vec 2) {g₁ g₂ : Vec 2 → ℝ} (h₁ : Integrable g₁) (h₂ : Integrable g₂)
    {ψ : Vec 2 → ℂ} (hc : Continuous ψ) (hp : AVenhance.IsZ2Periodic ψ) :
    ∫ z in AVenhance.unitCube, planeBlochC θ (fun y => g₁ y + g₂ y) z * ψ z =
      (∫ z in AVenhance.unitCube, planeBlochC θ g₁ z * ψ z) +
        ∫ z in AVenhance.unitCube, planeBlochC θ g₂ z * ψ z := by
  have h12 : Integrable (fun y => g₁ y + g₂ y) := h₁.add h₂
  rw [cell_pair_eq_plane θ h12 hc hp, cell_pair_eq_plane θ h₁ hc hp,
    cell_pair_eq_plane θ h₂ hc hp, ← integral_add (integrable_phase_pairing θ h₁ hc hp)
      (integrable_phase_pairing θ h₂ hc hp)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  push_cast
  ring

theorem cell_pair_const_mul (θ : Vec 2) (a : ℝ) {g : Vec 2 → ℝ} {ψ : Vec 2 → ℂ}
    (hc : Continuous ψ) (hp : AVenhance.IsZ2Periodic ψ) (hg : Integrable g) :
    ∫ z in AVenhance.unitCube, planeBlochC θ (fun y => a * g y) z * ψ z =
      (a : ℂ) * ∫ z in AVenhance.unitCube, planeBlochC θ g z * ψ z := by
  rw [cell_pair_eq_plane θ (hg.const_mul a) hc hp, cell_pair_eq_plane θ hg hc hp,
    ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  push_cast
  ring

theorem cell_pair_sub (θ : Vec 2) {g₁ g₂ : Vec 2 → ℝ} (h₁ : Integrable g₁) (h₂ : Integrable g₂)
    {ψ : Vec 2 → ℂ} (hc : Continuous ψ) (hp : AVenhance.IsZ2Periodic ψ) :
    ∫ z in AVenhance.unitCube, planeBlochC θ (fun y => g₁ y - g₂ y) z * ψ z =
      (∫ z in AVenhance.unitCube, planeBlochC θ g₁ z * ψ z) -
        ∫ z in AVenhance.unitCube, planeBlochC θ g₂ z * ψ z := by
  have h := cell_pair_add θ h₁ (h₂.const_mul (-1)) hc hp
  rw [cell_pair_const_mul θ (-1) hc hp h₂] at h
  simp only [neg_mul, one_mul, ← sub_eq_add_neg, Complex.ofReal_neg, Complex.ofReal_one] at h
  exact h

theorem cell_pair_sum (θ : Vec 2) {ι' : Type*} (s : Finset ι') {g : ι' → Vec 2 → ℝ}
    (hg : ∀ i ∈ s, Integrable (g i)) {ψ : Vec 2 → ℂ} (hc : Continuous ψ)
    (hp : AVenhance.IsZ2Periodic ψ) :
    ∫ z in AVenhance.unitCube, planeBlochC θ (fun y => ∑ i ∈ s, g i y) z * ψ z =
      ∑ i ∈ s, ∫ z in AVenhance.unitCube, planeBlochC θ (g i) z * ψ z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [planeBlochC]
  | insert a s ha ih =>
    have h1 : Integrable (g a) := hg a (Finset.mem_insert_self _ _)
    have h2 : Integrable (fun y => ∑ i ∈ s, g i y) :=
      integrable_finsetSum _ fun i hi => hg i (Finset.mem_insert_of_mem hi)
    simp only [Finset.sum_insert ha]
    rw [cell_pair_add θ h1 h2 hc hp, ih fun i hi => hg i (Finset.mem_insert_of_mem hi)]

/-- A continuous periodic real factor passes from the function to the test. -/
theorem cell_pair_periodic_mul (θ : Vec 2) {C : Vec 2 → ℝ} (hCc : Continuous C)
    (hCp : AVenhance.IsZ2Periodic C) {g : Vec 2 → ℝ} (hg : Integrable g) {ψ : Vec 2 → ℂ}
    (hc : Continuous ψ) (hp : AVenhance.IsZ2Periodic ψ) :
    ∫ z in AVenhance.unitCube, planeBlochC θ (fun y => C y * g y) z * ψ z =
      ∫ z in AVenhance.unitCube, planeBlochC θ g z * ((C z : ℂ) * ψ z) := by
  have hCc' : Continuous fun y => (C y : ℂ) := Complex.continuous_ofReal.comp hCc
  have hCp' : AVenhance.IsZ2Periodic fun y => (C y : ℂ) := fun n x => by simp [hCp n x]
  obtain ⟨M, hM⟩ := exists_norm_bound_of_periodic hCc' hCp'
  have hCg : Integrable (fun y => C y * g y) := by
    have := hg.bdd_mul (c := M) hCc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by simpa using hM y)
    exact this
  have hcont : Continuous fun z => (C z : ℂ) * ψ z := hCc'.mul hc
  have hper : AVenhance.IsZ2Periodic fun z => (C z : ℂ) * ψ z := fun n x => by
    simp only [hCp n x, hp n x]
  rw [cell_pair_eq_plane θ hCg hc hp, cell_pair_eq_plane θ hg hcont hper]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  push_cast
  ring

theorem integrable_periodic_mul {C : Vec 2 → ℝ} (hCc : Continuous C)
    (hCp : AVenhance.IsZ2Periodic C) {g : Vec 2 → ℝ} (hg : Integrable g) :
    Integrable (fun y => C y * g y) := by
  have hCc' : Continuous fun y => (C y : ℂ) := Complex.continuous_ofReal.comp hCc
  have hCp' : AVenhance.IsZ2Periodic fun y => (C y : ℂ) := fun n x => by simp [hCp n x]
  obtain ⟨M, hM⟩ := exists_norm_bound_of_periodic hCc' hCp'
  exact hg.bdd_mul (c := M) hCc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by simpa using hM y)

/-- The cell pairing is additive in the test. -/
theorem cell_pair_test_add (θ : Vec 2) {g : Vec 2 → ℝ} (hg : Integrable g) {ψ₁ ψ₂ : Vec 2 → ℂ}
    (hc₁ : Continuous ψ₁) (hp₁ : AVenhance.IsZ2Periodic ψ₁) (hc₂ : Continuous ψ₂)
    (hp₂ : AVenhance.IsZ2Periodic ψ₂) :
    ∫ z in AVenhance.unitCube, planeBlochC θ g z * (ψ₁ z + ψ₂ z) =
      (∫ z in AVenhance.unitCube, planeBlochC θ g z * ψ₁ z) +
        ∫ z in AVenhance.unitCube, planeBlochC θ g z * ψ₂ z := by
  have hc : Continuous fun z => ψ₁ z + ψ₂ z := hc₁.add hc₂
  have hp : AVenhance.IsZ2Periodic fun z => ψ₁ z + ψ₂ z := fun n x => by
    simp only [hp₁ n x, hp₂ n x]
  rw [cell_pair_eq_plane θ hg hc hp, cell_pair_eq_plane θ hg hc₁ hp₁,
    cell_pair_eq_plane θ hg hc₂ hp₂, ← integral_add (integrable_phase_pairing θ hg hc₁ hp₁)
      (integrable_phase_pairing θ hg hc₂ hp₂)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => by simp only; ring)

/-- The cell pairing is homogeneous in the test. -/
theorem cell_pair_test_const_mul (θ : Vec 2) {g : Vec 2 → ℝ} (hg : Integrable g) (a : ℂ)
    {ψ : Vec 2 → ℂ} (hc : Continuous ψ) (hp : AVenhance.IsZ2Periodic ψ) :
    ∫ z in AVenhance.unitCube, planeBlochC θ g z * (a * ψ z) =
      a * ∫ z in AVenhance.unitCube, planeBlochC θ g z * ψ z := by
  have hc' : Continuous fun z => a * ψ z := continuous_const.mul hc
  have hp' : AVenhance.IsZ2Periodic fun z => a * ψ z := fun n x => by simp only [hp n x]
  rw [cell_pair_eq_plane θ hg hc' hp', cell_pair_eq_plane θ hg hc hp, ← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => by simp only; ring)

/-- The test of `b1wSameLevel`: a periodic multiplier times `φ` plus the two covariant
derivatives. -/
theorem cell_pair_sameLevel_test (θ : Vec 2) {T : Vec 2 → ℝ} (hT : Integrable T)
    {a : Vec 2 → ℝ} (hac : Continuous a) (hap : AVenhance.IsZ2Periodic a) (c : Fin 2 → ℝ)
    {φ : Vec 2 → ℂ} (hφc : Continuous φ) (hφp : AVenhance.IsZ2Periodic φ)
    (hDc : ∀ k, Continuous (fibreCovDeriv (-θ) k φ))
    (hDp : ∀ k, AVenhance.IsZ2Periodic (fibreCovDeriv (-θ) k φ)) :
    ∫ z in AVenhance.unitCube, planeBlochC θ T z *
        ((a z : ℂ) * φ z + ∑ k : Fin 2, (c k : ℂ) * fibreCovDeriv (-θ) k φ z) =
      (∫ z in AVenhance.unitCube, planeBlochC θ T z * ((a z : ℂ) * φ z)) +
        ∑ k : Fin 2, (c k : ℂ) *
          ∫ z in AVenhance.unitCube, planeBlochC θ T z * fibreCovDeriv (-θ) k φ z := by
  have hac' : Continuous fun z => (a z : ℂ) := Complex.continuous_ofReal.comp hac
  have hap' : AVenhance.IsZ2Periodic fun z => (a z : ℂ) := fun n x => by simp [hap n x]
  have h1c : Continuous fun z => (a z : ℂ) * φ z := hac'.mul hφc
  have h1p : AVenhance.IsZ2Periodic fun z => (a z : ℂ) * φ z := fun n x => by
    simp only [hap n x, hφp n x]
  have hk : ∀ k : Fin 2, Continuous fun z => (c k : ℂ) * fibreCovDeriv (-θ) k φ z :=
    fun k => continuous_const.mul (hDc k)
  have hkp : ∀ k : Fin 2, AVenhance.IsZ2Periodic fun z => (c k : ℂ) * fibreCovDeriv (-θ) k φ z :=
    fun k n x => by simp only [hDp k n x]
  simp only [Fin.sum_univ_two]
  have h2c : Continuous fun z => (c 0 : ℂ) * fibreCovDeriv (-θ) 0 φ z +
      (c 1 : ℂ) * fibreCovDeriv (-θ) 1 φ z := (hk 0).add (hk 1)
  have h2p : AVenhance.IsZ2Periodic fun z => (c 0 : ℂ) * fibreCovDeriv (-θ) 0 φ z +
      (c 1 : ℂ) * fibreCovDeriv (-θ) 1 φ z := fun n x => by
    simp only [hDp 0 n x, hDp 1 n x]
  rw [cell_pair_test_add θ hT h1c h1p h2c h2p, cell_pair_test_add θ hT (hk 0) (hkp 0) (hk 1) (hkp 1),
    cell_pair_test_const_mul θ hT _ (hDc 0) (hDp 0), cell_pair_test_const_mul θ hT _ (hDc 1) (hDp 1)]

end Periodization

section Clause1

set_option hygiene false in
/-- Close an integrability goal built from the moment hypotheses `hu`, `hf`. -/
local macro "int_tac" : tactic =>
  `(tactic| repeat' first
    | refine Integrable.add ?_ ?_
    | refine Integrable.sub ?_ ?_
    | refine Integrable.neg ?_
    | refine Integrable.const_mul ?_ _
    | refine integrable_periodic_mul (hv _) (hvpi _) ?_
    | exact hu _
    | exact hf _ _)

/-- **Clause 1, pointwise-in-`r` core.** -/
theorem clause1_core {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (θ : Vec 2)
    (G : Matrix (Fin 2) (Fin 2) ℝ) (vf : Vec 2 → Vec 2) (hvc : Continuous vf)
    (hvp : AVenhance.IsZ2Periodic vf) (β : ℕ × ℕ) (e : E) (g : Vec 2 → E)
    (fl : Vec 2 → Fin 2 → ℝ)
    (hu : ∀ β' : ℕ × ℕ, Integrable (fun y => momentWeight β' y * inner ℝ e (g y)))
    (hf : ∀ (β' : ℕ × ℕ) (i : Fin 2), Integrable (fun y => momentWeight β' y * fl y i))
    {φ : Vec 2 → ℂ} (hφc : Continuous φ) (hφp : AVenhance.IsZ2Periodic φ)
    (hDc : ∀ k, Continuous (fibreCovDeriv (-θ) k φ))
    (hDp : ∀ k, AVenhance.IsZ2Periodic (fibreCovDeriv (-θ) k φ)) :
    (∫ z in AVenhance.unitCube, planeBlochC θ (fun y =>
        (momentWeightLap G β y + ∑ i, vf y i * momentWeightGrad β y i) * inner ℝ e (g y) -
          ∑ i, momentWeightGrad β y i * fl y i) z * φ z) -
      ∑ k : Fin 2, ∫ z in AVenhance.unitCube, planeBlochC θ (fun y =>
        momentWeight β y * fl y k -
          (∑ i, (G k i + G i k) * momentWeightGrad β y i) * inner ℝ e (g y)) z *
        fibreCovDeriv (-θ) k φ z =
      b1wSameLevel θ G vf β e g φ -
        ((β.1 : ℝ) : ℂ) * (∫ z in AVenhance.unitCube, planeBlochC θ
          (fun y => momentWeight (β.1 - 1, β.2) y * fl y 0) z * φ z) -
        ((β.2 : ℝ) : ℂ) * (∫ z in AVenhance.unitCube, planeBlochC θ
          (fun y => momentWeight (β.1, β.2 - 1) y * fl y 1) z * φ z) -
        ∑ k : Fin 2, ∫ z in AVenhance.unitCube, planeBlochC θ
          (fun y => momentWeight β y * fl y k) z * fibreCovDeriv (-θ) k φ z := by
  have hv : ∀ i : Fin 2, Continuous fun y => vf y i := fun i => (continuous_apply i).comp hvc
  have hvpi : ∀ i : Fin 2, AVenhance.IsZ2Periodic fun y => vf y i := fun i n x => by
    show vf (x + AVenhance.latticeShift n) i = vf x i
    rw [hvp n x]
  have eS : (fun y => (momentWeightLap G β y + ∑ i, vf y i * momentWeightGrad β y i) *
        inner ℝ e (g y) - ∑ i, momentWeightGrad β y i * fl y i) = fun y =>
      (G 0 0 * ((β.1 : ℝ) * ((β.1 : ℝ) - 1))) *
          (momentWeight (β.1 - 2, β.2) y * inner ℝ e (g y)) +
        ((G 0 1 + G 1 0) * ((β.1 : ℝ) * (β.2 : ℝ))) *
          (momentWeight (β.1 - 1, β.2 - 1) y * inner ℝ e (g y)) +
        (G 1 1 * ((β.2 : ℝ) * ((β.2 : ℝ) - 1))) *
          (momentWeight (β.1, β.2 - 2) y * inner ℝ e (g y)) +
        vf y 0 * ((β.1 : ℝ) * (momentWeight (β.1 - 1, β.2) y * inner ℝ e (g y))) +
        vf y 1 * ((β.2 : ℝ) * (momentWeight (β.1, β.2 - 1) y * inner ℝ e (g y))) -
        (β.1 : ℝ) * (momentWeight (β.1 - 1, β.2) y * fl y 0) -
        (β.2 : ℝ) * (momentWeight (β.1, β.2 - 1) y * fl y 1) := by
    funext y
    simp only [Fin.sum_univ_two, momentWeightLap, momentWeightGrad, momentWeight]
    simp
    ring
  have eK : ∀ k : Fin 2, (fun y => momentWeight β y * fl y k -
        (∑ i, (G k i + G i k) * momentWeightGrad β y i) * inner ℝ e (g y)) = fun y =>
      momentWeight β y * fl y k -
        (((G k 0 + G 0 k) * (β.1 : ℝ)) * (momentWeight (β.1 - 1, β.2) y * inner ℝ e (g y)) +
          ((G k 1 + G 1 k) * (β.2 : ℝ)) * (momentWeight (β.1, β.2 - 1) y * inner ℝ e (g y))) := by
    intro k
    funext y
    simp only [Fin.sum_univ_two, momentWeightGrad, momentWeight]
    simp
    ring
  simp only [eS, eK]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  have hvφc : ∀ i : Fin 2, Continuous fun z => (vf z i : ℂ) * φ z := fun i =>
    (Complex.continuous_ofReal.comp (hv i)).mul hφc
  have hvφp : ∀ i : Fin 2, AVenhance.IsZ2Periodic fun z => (vf z i : ℂ) * φ z := fun i n x => by
    have := hvpi i n x
    have h2 := hφp n x
    simp only at this
    simp only [this, h2]
  rw [cell_pair_sub θ ?_ ?_ hφc hφp, cell_pair_sub θ ?_ ?_ hφc hφp, cell_pair_add θ ?_ ?_ hφc hφp,
    cell_pair_add θ ?_ ?_ hφc hφp, cell_pair_add θ ?_ ?_ hφc hφp, cell_pair_add θ ?_ ?_ hφc hφp,
    cell_pair_periodic_mul θ (hv 0) (hvpi 0) ?_ hφc hφp,
    cell_pair_periodic_mul θ (hv 1) (hvpi 1) ?_ hφc hφp,
    cell_pair_const_mul θ _ (hvφc 0) (hvφp 0) ?_, cell_pair_const_mul θ _ (hvφc 1) (hvφp 1) ?_,
    cell_pair_const_mul θ _ hφc hφp ?_, cell_pair_const_mul θ _ hφc hφp ?_,
    cell_pair_const_mul θ _ hφc hφp ?_, cell_pair_const_mul θ _ hφc hφp ?_,
    cell_pair_const_mul θ _ hφc hφp ?_,
    cell_pair_sub θ ?_ ?_ (hDc 0) (hDp 0), cell_pair_add θ ?_ ?_ (hDc 0) (hDp 0),
    cell_pair_const_mul θ _ (hDc 0) (hDp 0) ?_, cell_pair_const_mul θ _ (hDc 0) (hDp 0) ?_,
    cell_pair_sub θ ?_ ?_ (hDc 1) (hDp 1), cell_pair_add θ ?_ ?_ (hDc 1) (hDp 1),
    cell_pair_const_mul θ _ (hDc 1) (hDp 1) ?_, cell_pair_const_mul θ _ (hDc 1) (hDp 1) ?_]
  · have h0 : (∫ z in AVenhance.unitCube, b1wStageFun θ (β.1 - 1, β.2) e g z *
        ((vf z 0 : ℂ) * φ z + ∑ k : Fin 2, ((G k 0 + G 0 k : ℝ) : ℂ) *
          fibreCovDeriv (-θ) k φ z)) =
        (∫ z in AVenhance.unitCube, b1wStageFun θ (β.1 - 1, β.2) e g z * ((vf z 0 : ℂ) * φ z)) +
        ∑ k : Fin 2, ((G k 0 + G 0 k : ℝ) : ℂ) *
          ∫ z in AVenhance.unitCube, b1wStageFun θ (β.1 - 1, β.2) e g z *
            fibreCovDeriv (-θ) k φ z :=
      cell_pair_sameLevel_test θ (hu (β.1 - 1, β.2)) (hv 0) (hvpi 0) (fun k => G k 0 + G 0 k)
        hφc hφp hDc hDp
    have h1 : (∫ z in AVenhance.unitCube, b1wStageFun θ (β.1, β.2 - 1) e g z *
        ((vf z 1 : ℂ) * φ z + ∑ k : Fin 2, ((G k 1 + G 1 k : ℝ) : ℂ) *
          fibreCovDeriv (-θ) k φ z)) =
        (∫ z in AVenhance.unitCube, b1wStageFun θ (β.1, β.2 - 1) e g z * ((vf z 1 : ℂ) * φ z)) +
        ∑ k : Fin 2, ((G k 1 + G 1 k : ℝ) : ℂ) *
          ∫ z in AVenhance.unitCube, b1wStageFun θ (β.1, β.2 - 1) e g z *
            fibreCovDeriv (-θ) k φ z :=
      cell_pair_sameLevel_test θ (hu (β.1, β.2 - 1)) (hv 1) (hvpi 1) (fun k => G k 1 + G 1 k)
        hφc hφp hDc hDp
    unfold b1wSameLevel
    rw [h0, h1]
    unfold b1wStageFun
    push_cast
    simp only [Fin.sum_univ_two]
    ring
  all_goals int_tac

end Clause1
end

end AVRegularity.CycleWords.Assembly
end
