-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.MixedWords.SharpBlocksSameComm
public import AVRegularity.CycleWords.MixedWords.B1WFamilies
public import AVRegularity.CycleWords.Assembly.MixedWordsB1SharpBlocks
public import AVRegularity.CycleWords.MixedWords.SharpBlocksAssembly
import AVRegularity.CycleWords.MixedWords.B1WData

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleEvolution AVRegularity.CycleWords
namespace AVRegularity.CycleWords.Assembly

/-! # the sharp letter families from sharp block operators

The block-level Schur assembly (`sharp_letter_final`): the block bounds of the sharp families,
with the weights `C₀ κ w_l`, `C₀ ζ κ w_l`, `C₀ ζ² κ w_l`, give the sums over all stages by the
Schur test over the keys `(component, moment)` (`fibre_schur`). -/

universe u v

theorem sum_mul_sq {B : Type*} (s : Finset B) (b : B → ℝ) (e : ℝ) :
    ∑ i ∈ s, (b i * e) ^ 2 = e ^ 2 * ∑ i ∈ s, b i ^ 2 := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The sharp sums from block bounds over the fibres of a key map. -/
theorem sharp_letter_final {B G : Type*} [DecidableEq G] [Fintype B] {N n : ℕ}
    (key : B → G) (stk stk' : Finset B) (T : B → B → TorusHk N ℂ →L[ℝ] TorusHk n ℂ)
    (w0 : G → G → ℝ) (hw0 : ∀ g g', 0 ≤ w0 g g') {cnt : ℝ} (hcnt : 0 ≤ cnt)
    (hrow : ∀ g ∈ stk.image key, ∑ g' ∈ stk'.image key, w0 g g' ≤ cnt)
    (hcol : ∀ g' ∈ stk'.image key, ∑ g ∈ stk.image key, w0 g g' ≤ cnt)
    {C0 ζ x M₀ : ℝ} (hC0 : 0 ≤ C0) (hζ0 : 0 ≤ ζ)
    (hbN : ∀ g ∈ stk.image key, ∀ g' ∈ stk'.image key, ∀ f : B → TorusHk N ℂ,
      ∑ i' ∈ stk'.filter (fun i' => key i' = g'),
        ‖∑ i ∈ stk.filter (fun i => key i = g), T i i' (f i)‖ ^ 2 ≤
          (C0 * w0 g g') ^ 2 * ∑ i ∈ stk.filter (fun i => key i = g), ‖f i‖ ^ 2)
    (hbP : ∀ R : ComplexCellL2, ‖R‖ ≤ |M₀| * x →
      ∀ g ∈ stk.image key, ∀ g' ∈ stk'.image key, ∀ f : B → TorusHk N ℂ,
      ∑ i' ∈ stk'.filter (fun i' => key i' = g'),
        ‖sharpPair R (∑ i ∈ stk.filter (fun i => key i = g), T i i' (f i))‖ ^ 2 ≤
          (C0 * ζ * w0 g g') ^ 2 * ∑ i ∈ stk.filter (fun i => key i = g), ‖f i‖ ^ 2)
    (hbS : ∀ (E : ℂ) (β : B → ℂ) (Dd : TorusHk N ℂ), ‖Dd‖ ≤ M₀ * x * ‖E‖ →
      ∀ g ∈ stk.image key, ∀ g' ∈ stk'.image key, ∀ f : B → TorusHk N ℂ,
      (∀ i ∈ stk.filter (fun i => key i = g),
        f i = torusHigherScalarCLM N (β i) (torusHigherConstant N E + Dd)) →
      ∑ i' ∈ stk'.filter (fun i' => key i' = g'),
        ‖∑ i ∈ stk.filter (fun i => key i = g), T i i' (f i)‖ ^ 2 ≤
          (C0 * ζ * w0 g g') ^ 2 * ‖E‖ ^ 2 *
            ∑ i ∈ stk.filter (fun i => key i = g), ‖β i‖ ^ 2)
    (hbSP : ∀ (E : ℂ) (β : B → ℂ) (Dd : TorusHk N ℂ), ‖Dd‖ ≤ M₀ * x * ‖E‖ →
      ∀ R : ComplexCellL2, ‖R‖ ≤ |M₀| * x →
      ∀ g ∈ stk.image key, ∀ g' ∈ stk'.image key, ∀ f : B → TorusHk N ℂ,
      (∀ i ∈ stk.filter (fun i => key i = g),
        f i = torusHigherScalarCLM N (β i) (torusHigherConstant N E + Dd)) →
      ∑ i' ∈ stk'.filter (fun i' => key i' = g'),
        ‖sharpPair R (∑ i ∈ stk.filter (fun i => key i = g), T i i' (f i))‖ ^ 2 ≤
          (C0 * ζ ^ 2 * w0 g g') ^ 2 * ‖E‖ ^ 2 *
            ∑ i ∈ stk.filter (fun i => key i = g), ‖β i‖ ^ 2)
    (ψ : B → TorusHk N ℂ) :
    (∑ i' ∈ stk', ‖∑ i ∈ stk, T i i' (ψ i)‖ ^ 2 ≤ (C0 * cnt) ^ 2 * ∑ i ∈ stk, ‖ψ i‖ ^ 2) ∧
    (∀ R : ComplexCellL2, ‖R‖ ≤ |M₀| * x →
      ∑ i' ∈ stk', ‖sharpPair R (∑ i ∈ stk, T i i' (ψ i))‖ ^ 2 ≤
        (C0 * cnt) ^ 2 * ζ ^ 2 * ∑ i ∈ stk, ‖ψ i‖ ^ 2) ∧
    (∀ (E : ℂ) (β : B → ℂ) (Dd : TorusHk N ℂ), ‖Dd‖ ≤ M₀ * x * ‖E‖ →
      (∀ i ∈ stk, ψ i = torusHigherScalarCLM N (β i) (torusHigherConstant N E + Dd)) →
      (∀ R : ComplexCellL2, ‖R‖ ≤ |M₀| * x →
        ∑ i' ∈ stk', ‖sharpPair R (∑ i ∈ stk, T i i' (ψ i))‖ ^ 2 ≤
          (C0 * cnt) ^ 2 * ζ ^ 4 * ‖E‖ ^ 2 * ∑ i ∈ stk, ‖β i‖ ^ 2) ∧
      ∑ i' ∈ stk', ‖∑ i ∈ stk, T i i' (ψ i)‖ ^ 2 ≤
        (C0 * cnt) ^ 2 * ζ ^ 2 * ‖E‖ ^ 2 * ∑ i ∈ stk, ‖β i‖ ^ 2) := by
  have hw : ∀ (c : ℝ), 0 ≤ c → ∀ g g', 0 ≤ c * w0 g g' := fun c hc g g' => mul_nonneg hc (hw0 g g')
  have hrow' : ∀ c : ℝ, 0 ≤ c → ∀ g ∈ stk.image key,
      ∑ g' ∈ stk'.image key, c * w0 g g' ≤ c * cnt := fun c hc g hg => by
    rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hrow g hg) hc
  have hcol' : ∀ c : ℝ, 0 ≤ c → ∀ g' ∈ stk'.image key,
      ∑ g ∈ stk.image key, c * w0 g g' ≤ c * cnt := fun c hc g' hg' => by
    rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left (hcol g' hg') hc
  have hCz : 0 ≤ C0 * ζ := mul_nonneg hC0 hζ0
  have hCz2 : 0 ≤ C0 * ζ ^ 2 := mul_nonneg hC0 (sq_nonneg _)
  refine ⟨?_, ?_, ?_⟩
  · refine (fibre_schur key stk stk' (fun i i' => T i i' (ψ i)) (fun i => ‖ψ i‖)
      (fun g g' => C0 * w0 g g') (hw C0 hC0) (hrow' C0 hC0) (hcol' C0 hC0)
      (mul_nonneg hC0 hcnt) (fun g hg g' hg' => hbN g hg g' hg' ψ)).trans (le_of_eq ?_)
    ring
  · intro R hR
    have := fibre_schur (Y := ℂ) key stk stk' (fun i i' => sharpPair R (T i i' (ψ i)))
      (fun i => ‖ψ i‖) (fun g g' => C0 * ζ * w0 g g') (hw _ hCz) (hrow' _ hCz) (hcol' _ hCz)
      (mul_nonneg hCz hcnt) (fun g hg g' hg' => by
        simpa only [sharpPair_sum] using hbP R hR g hg g' hg' ψ)
    simp only [← sharpPair_sum] at this
    refine this.trans (le_of_eq ?_)
    ring
  · intro E β Dd hD hψ
    refine ⟨fun R hR => ?_, ?_⟩
    · have := fibre_schur (Y := ℂ) key stk stk' (fun i i' => sharpPair R (T i i' (ψ i)))
        (fun i => ‖β i‖ * ‖E‖) (fun g g' => C0 * ζ ^ 2 * w0 g g') (hw _ hCz2) (hrow' _ hCz2)
        (hcol' _ hCz2) (mul_nonneg hCz2 hcnt) (fun g hg g' hg' => by
          have h1 := hbSP E β Dd hD R hR g hg g' hg' ψ (fun i hi => hψ i
            (Finset.mem_filter.1 hi).1)
          simp only [sharpPair_sum] at h1
          rw [sum_mul_sq]
          exact h1.trans (le_of_eq (by ring)))
      simp only [← sharpPair_sum] at this
      refine this.trans (le_of_eq ?_)
      rw [sum_mul_sq]
      ring
    · have := fibre_schur key stk stk' (fun i i' => T i i' (ψ i)) (fun i => ‖β i‖ * ‖E‖)
        (fun g g' => C0 * ζ * w0 g g') (hw _ hCz) (hrow' _ hCz) (hcol' _ hCz)
        (mul_nonneg hCz hcnt) (fun g hg g' hg' => by
          have h1 := hbS E β Dd hD g hg g' hg' ψ (fun i hi => hψ i
            (Finset.mem_filter.1 hi).1)
          rw [sum_mul_sq]
          exact h1.trans (le_of_eq (by ring)))
      refine this.trans (le_of_eq ?_)
      rw [sum_mul_sq]
      ring

open Classical in
/-- **Sharp letter block operators.** The operators of `LetterOpsStatement`, with the
block bounds of the sharp families: the weights `C₀ ζ κ w_l` (slow–fast pairing and slow-test
families), `C₀ ζ² κ w_l` (slow–slow pairing), and commutation with the transverse projection.
The mean of the transform has a zero from the divergence form (`LC1 = O(ε²)`,
`LC g = O(ε)‖g‖₂`), and the scale ratio cancels `θ_l` as in the transform bounds. -/
def SharpLetterOpsStatement : Prop :=
  ∀ (K : ScalarConstants) (Nw D m : ℕ) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool) (ρ : ℝ)
    (n : ℕ) (M₀ : ℝ),
  ∃ C0 : ℝ, 0 ≤ C0 ∧
  ∀ (g₁ : ℝ) {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
    (∀ l, (F.letters l).order = d l ∧ (F.letters l).slow = Ks l ∧
      (F.letters l).positive = pos l) →
    n + (Finset.univ.sup d) ≤ F.J →
    fibreNorm (planeFibreFrequency F.η θ) ≤ ρ →
  ∀ᵐ r ∂(volume.restrict (Icc F.a F.b)), ∀ (l : Fin Nw) (N : ℕ), n + d l ≤ N →
    (Finset.univ.sup d) + 3 ≤ N →
  ∃ T : B1WIndex ι h Nw m Ks → B1WIndex ι h Nw m Ks → TorusHk N ℂ →L[ℝ] TorusHk n ℂ,
    (∀ i i' : B1WIndex ι h Nw m Ks, i.1 = l.succ → i'.1 = l.castSucc → ∀ ψ : TorusHk N ℂ,
      (torusHkValueCLM (T i i' ψ) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] fun z =>
          b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
            star (b1wLetterTransform F θ i i' r
              (fun y => star (torusHigherClassicalValue N ψ y)) z)) ∧
    (∀ (S S' : Finset (B1WIndex ι h Nw m Ks)) (x x' : ι) (β β' : ℕ × ℕ),
      (∀ i ∈ S, i.1 = l.succ ∧ b1wKey i = (x, β)) →
      (∀ i' ∈ S', i'.1 = l.castSucc ∧ b1wKey i' = (x', β')) →
      let w0 : ℝ := (if LetterMomRel (Finset.univ.sup Ks) (Finset.univ.sup d + 1) β β'
              then 1 else 0) * letterCompWeight (F.letters l) x x'
      let ζ : ℝ := min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹)
      (∀ f : B1WIndex ι h Nw m Ks → TorusHk N ℂ,
        ∑ i' ∈ S', ‖∑ i ∈ S, T i i' (f i)‖ ^ 2 ≤ (C0 * w0) ^ 2 * ∑ i ∈ S, ‖f i‖ ^ 2) ∧
      (∀ R : ComplexCellL2, ‖R‖ ≤ |M₀| * fibreNorm (planeFibreFrequency F.η θ) →
        ∀ f : B1WIndex ι h Nw m Ks → TorusHk N ℂ,
        ∑ i' ∈ S', ‖sharpPair R (∑ i ∈ S, T i i' (f i))‖ ^ 2 ≤
          (C0 * ζ * w0) ^ 2 * ∑ i ∈ S, ‖f i‖ ^ 2) ∧
      (∀ (E : ℂ) (b : B1WIndex ι h Nw m Ks → ℂ) (Dd : TorusHk N ℂ),
        ‖Dd‖ ≤ M₀ * fibreNorm (planeFibreFrequency F.η θ) * ‖E‖ →
        ∀ f : B1WIndex ι h Nw m Ks → TorusHk N ℂ,
        (∀ i ∈ S, f i = torusHigherScalarCLM N (b i) (torusHigherConstant N E + Dd)) →
        ∑ i' ∈ S', ‖∑ i ∈ S, T i i' (f i)‖ ^ 2 ≤
          (C0 * ζ * w0) ^ 2 * ‖E‖ ^ 2 * ∑ i ∈ S, ‖b i‖ ^ 2 ∧
        ∀ R : ComplexCellL2, ‖R‖ ≤ |M₀| * fibreNorm (planeFibreFrequency F.η θ) →
          ∑ i' ∈ S', ‖sharpPair R (∑ i ∈ S, T i i' (f i))‖ ^ 2 ≤
            (C0 * ζ ^ 2 * w0) ^ 2 * ‖E‖ ^ 2 * ∑ i ∈ S, ‖b i‖ ^ 2)) ∧
    (∀ p, IsLeastWindow F.reg p r →
      ∀ (PN : TorusHk N ℂ →L[ℝ] TorusHk N ℂ) (Pn : TorusHk n ℂ →L[ℝ] TorusHk n ℂ),
      (∀ U, torusHkValueCLM (PN U) =
        cellTransverseProjection (F.reg.orient p) (torusHkValueCLM U)) →
      (∀ U, torusHkValueCLM (Pn U) =
        cellTransverseProjection (F.reg.orient p) (torusHkValueCLM U)) →
      ∀ i i' : B1WIndex ι h Nw m Ks, i.1 = l.succ → i'.1 = l.castSucc →
        ∀ φ : TorusHk N ℂ, Pn (T i i' φ) = T i i' (PN φ))

open Classical in
/-- **Assembly of `sharpLetterAE`** from the sharp block operators. -/
theorem sharpLetterAE_of_ops (hO : SharpLetterOpsStatement.{u, v}) :
    SharpLetterAEStatement.{u, v} := by
  intro K Nw D m d Ks pos ρ n M₀
  obtain ⟨C0, hC0, hC⟩ := hO K Nw D m d Ks pos ρ n M₀
  have hcnt0 : 0 ≤ ((((Finset.univ.sup Ks) + (Finset.univ.sup d + 1) + 1) ^ 2 : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  refine ⟨C0 * ((((Finset.univ.sup Ks) + (Finset.univ.sup d + 1) + 1) ^ 2 : ℕ) : ℝ),
    mul_nonneg hC0 hcnt0, ?_⟩
  intro g₁ ι _ h _ _ _ _ _ _ F θ hlet hJ hρ
  filter_upwards [hC g₁ F θ hlet hJ hρ] with r hr
  intro l k k' hk hk' N hnN hdN ψ
  obtain ⟨T, hTv, hTb, hTc⟩ := hr l N hnN hdN
  have hx0 := fibreNorm_nonneg (planeFibreFrequency F.η θ)
  have hiv : 0 ≤ (Real.sqrt F.S)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  have hζ0 : 0 ≤ min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹) :=
    le_min zero_le_one (by linarith)
  have hL := F.piece.hlet l
  let w0 : ι × (ℕ × ℕ) → ι × (ℕ × ℕ) → ℝ := fun g g' =>
    (if LetterMomRel (Finset.univ.sup Ks) (Finset.univ.sup d + 1) g.2 g'.2 then 1 else 0) *
      letterCompWeight (F.letters l) g.1 g'.1
  have hw0 : ∀ g g', 0 ≤ w0 g g' := fun g g' =>
    mul_nonneg (by split_ifs <;> simp) (letterCompWeight_nonneg hL _ _)
  have hF := fun ψ' : B1WIndex ι h Nw m Ks → TorusHk N ℂ =>
    sharp_letter_final (N := N) (n := n) b1wKey
      (stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k)
      (stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k') T w0 hw0
      (cnt := ((((Finset.univ.sup Ks) + (Finset.univ.sup d + 1) + 1) ^ 2 : ℕ) : ℝ)) hcnt0
      (fun g _ => by
        have h1 := letterMom_row (Finset.univ.sup Ks) (Finset.univ.sup d + 1) g.2
          ((stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k').image b1wKey)
          (letterCompWeight (F.letters l) g.1) (letterCompWeight_nonneg hL _)
        have h2 := letterCompWeight_row hL g.1
        calc _ ≤ _ := h1
          _ ≤ _ * 1 := mul_le_mul_of_nonneg_left h2 hcnt0
          _ = _ := mul_one _)
      (fun g' _ => by
        have h1 := letterMom_col (Finset.univ.sup Ks) (Finset.univ.sup d + 1) g'.2
          ((stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k).image b1wKey)
          (fun x => letterCompWeight (F.letters l) x g'.1)
          (fun x => letterCompWeight_nonneg hL _ _)
        have h2 := letterCompWeight_col hL g'.1
        calc _ ≤ _ := h1
          _ ≤ _ * 1 := mul_le_mul_of_nonneg_left h2 hcnt0
          _ = _ := mul_one _)
      (C0 := C0) (ζ := min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹))
      (x := fibreNorm (planeFibreFrequency F.η θ)) (M₀ := M₀) hC0 hζ0
      (fun g hg g' hg' f => by
        obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.1 hg
        obtain ⟨i₁, hi₁, rfl⟩ := Finset.mem_image.1 hg'
        exact (hTb _ _ (b1wKey i₀).1 (b1wKey i₁).1 (b1wKey i₀).2 (b1wKey i₁).2
          (fun i hi => ⟨hk i (Finset.mem_filter.1 hi).1, (Finset.mem_filter.1 hi).2⟩)
          (fun i' hi' => ⟨hk' i' (Finset.mem_filter.1 hi').1, (Finset.mem_filter.1 hi').2⟩)).1 f)
      (fun R hR g hg g' hg' f => by
        obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.1 hg
        obtain ⟨i₁, hi₁, rfl⟩ := Finset.mem_image.1 hg'
        exact (hTb _ _ (b1wKey i₀).1 (b1wKey i₁).1 (b1wKey i₀).2 (b1wKey i₁).2
          (fun i hi => ⟨hk i (Finset.mem_filter.1 hi).1, (Finset.mem_filter.1 hi).2⟩)
          (fun i' hi' => ⟨hk' i' (Finset.mem_filter.1 hi').1, (Finset.mem_filter.1 hi').2⟩)).2.1
          R hR f)
      (fun E β Dd hD g hg g' hg' f hf => by
        obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.1 hg
        obtain ⟨i₁, hi₁, rfl⟩ := Finset.mem_image.1 hg'
        exact ((hTb _ _ (b1wKey i₀).1 (b1wKey i₁).1 (b1wKey i₀).2 (b1wKey i₁).2
          (fun i hi => ⟨hk i (Finset.mem_filter.1 hi).1, (Finset.mem_filter.1 hi).2⟩)
          (fun i' hi' => ⟨hk' i' (Finset.mem_filter.1 hi').1, (Finset.mem_filter.1 hi').2⟩)).2.2
          E β Dd hD f hf).1)
      (fun E β Dd hD R hR g hg g' hg' f hf => by
        obtain ⟨i₀, hi₀, rfl⟩ := Finset.mem_image.1 hg
        obtain ⟨i₁, hi₁, rfl⟩ := Finset.mem_image.1 hg'
        exact ((hTb _ _ (b1wKey i₀).1 (b1wKey i₁).1 (b1wKey i₀).2 (b1wKey i₁).2
          (fun i hi => ⟨hk i (Finset.mem_filter.1 hi).1, (Finset.mem_filter.1 hi).2⟩)
          (fun i' hi' => ⟨hk' i' (Finset.mem_filter.1 hi').1, (Finset.mem_filter.1 hi').2⟩)).2.2
          E β Dd hD f hf).2 R hR) ψ'
  refine ⟨fun i' => if i' ∈ stageSet b1wSt k' then ∑ i ∈ stageSet b1wSt k, T i i' (ψ i) else 0,
    ?_, ?_, ?_, ?_⟩
  · intro i' hi'
    simp only [hi', ↓reduceIte]
    exact torusHk_value_sum_ae (stageSet b1wSt k) (fun i => T i i' (ψ i)) _
      (fun i hi => hTv i i' (hk i hi) (hk' i' hi') (ψ i))
  · exact le_trans (le_of_eq (Finset.sum_congr rfl fun i' hi' => by
      simp only [hi', ↓reduceIte])) (hF ψ).1
  · have hRle : ∀ R : ComplexCellL2, ‖R‖ ≤ M₀ * fibreNorm (planeFibreFrequency F.η θ) →
        ‖R‖ ≤ |M₀| * fibreNorm (planeFibreFrequency F.η θ) := fun R hR =>
      hR.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hx0)
    refine ⟨fun R hR => ?_, fun E β Dd hD hψ => ⟨fun R hR => ?_, ?_⟩⟩
    · exact le_trans (le_of_eq (Finset.sum_congr rfl fun i' hi' => by
        simp only [hi', ↓reduceIte, sharpPair])) ((hF ψ).2.1 R (hRle R hR))
    · exact le_trans (le_of_eq (Finset.sum_congr rfl fun i' hi' => by
        simp only [hi', ↓reduceIte, sharpPair])) (((hF ψ).2.2 E β Dd hD hψ).1 R (hRle R hR))
    · exact le_trans (le_of_eq (Finset.sum_congr rfl fun i' hi' => by
        simp only [hi', ↓reduceIte])) ((hF ψ).2.2 E β Dd hD hψ).2
  · intro p hp PN Pn h1 h2
    have hF2 := (hF (fun i => ψ i - PN (ψ i))).1
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun i' hi' => ?_)) hF2
    simp only [hi', ↓reduceIte]
    congr 2
    rw [map_sum]
    refine (Finset.sum_sub_distrib (f := fun i => T i i' (ψ i))
      (g := fun i => Pn (T i i' (ψ i)))).symm.trans ?_
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hTc p hp PN Pn h1 h2 i i' (hk i hi) (hk' i' hi') (ψ i), map_sub]

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # Sharp pass: the sharp transform families of every pair of stages

The sharp analogue of `b1w_family_provider`. From the two sharp family statements,
every pair of stages `k' < k` has its test family in the ladder's spaces, with one constant `B`
for all pairs. The family satisfies:
* the value identity and the `ℓ²` bound;
* the sharp facts (`SharpFamilyFacts`): slow pairings and slow tests;
* the transversality defect bound in the least window (`b1w_sharp_family_provider`).

The case split is that of the crude pass: same level, next level, far levels (zero family).
The facts are monotone in the constant (`SharpFamilyFacts.mono`) and hold for the zero family
(`sharpFamilyFacts_zero`). -/

universe u v

section Facts

variable {I : Type*} [Fintype I]

theorem SharpFamilyFacts.mono {st : I → ℕ} {k k' N n : ℕ} {ψ : I → TorusHk N ℂ}
    {Φ : I → TorusHk n ℂ} {C B M₀ ζ x : ℝ} (hC : 0 ≤ C) (hCB : C ≤ B)
    (h : SharpFamilyFacts st k k' ψ Φ C M₀ ζ x) : SharpFamilyFacts st k k' ψ Φ B M₀ ζ x := by
  have h2 : C ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ hC hCB 2
  refine ⟨fun R hR => (h.1 R hR).trans ?_, fun E β Dd hDd hψ => ?_⟩
  · refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (sq_nonneg _))
      (Finset.sum_nonneg fun i _ => sq_nonneg _)
  · obtain ⟨h1, h3⟩ := h.2 E β Dd hDd hψ
    have hS : 0 ≤ ∑ i ∈ stageSet st k, ‖β i‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    refine ⟨fun R hR => (h1 R hR).trans ?_, h3.trans ?_⟩
    · refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h2 (by positivity)) (sq_nonneg _)) hS
    · refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h2 (sq_nonneg _)) (sq_nonneg _)) hS

theorem sharpFamilyFacts_zero (st : I → ℕ) (k k' N n : ℕ) (ψ : I → TorusHk N ℂ)
    (C M₀ ζ x : ℝ) : SharpFamilyFacts st k k' ψ (fun _ => (0 : TorusHk n ℂ)) C M₀ ζ x := by
  have hz : ∀ R : ComplexCellL2, ∑ i' ∈ stageSet st k',
      ‖cellComplexPair (R + cellConstantCLM 1) (torusHkValueCLM (0 : TorusHk n ℂ))‖ ^ 2 = 0 :=
    fun R => by simp [cellComplexPair_zero_right]
  refine ⟨fun R _ => by
    rw [hz]; exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => sq_nonneg _),
    fun E β Dd _ _ => ⟨fun R _ => by
      rw [hz]; exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => sq_nonneg _), ?_⟩⟩
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => sq_nonneg _)

end Facts

/-- The sharp facts of a stage family at time `r` (the conclusion of the sharp pass). -/
def B1WSharpFamily {K : ScalarConstants} {g₁ : ℝ} {ι : Type u} [Fintype ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {D Nw m : ℕ} {Ks : Fin Nw → ℕ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (r : ℝ)
    (k k' N n : ℕ) (ψ : B1WIndex ι h Nw m Ks → TorusHk N ℂ)
    (Φ : B1WIndex ι h Nw m Ks → TorusHk n ℂ) (B M₀ : ℝ) : Prop :=
  (∀ i' ∈ stageSet b1wSt k', (torusHkValueCLM (Φ i') : Vec 2 → ℂ)
    =ᵐ[volume.restrict AVenhance.unitCube] fun y =>
      ∑ i ∈ stageSet b1wSt k, b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
        star (b1wTestTransform F θ i i' r (fun y => star
          (torusHigherClassicalValue N (ψ i) y)) y)) ∧
  ∑ i' ∈ stageSet b1wSt k', ‖Φ i'‖ ^ 2 ≤ B ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2 ∧
  SharpFamilyFacts b1wSt k k' ψ Φ B M₀
    (min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹))
    (fibreNorm (planeFibreFrequency F.η θ)) ∧
  ∀ p, IsLeastWindow F.reg p r →
  ∀ (PN : TorusHk N ℂ →L[ℝ] TorusHk N ℂ) (Pn : TorusHk n ℂ →L[ℝ] TorusHk n ℂ),
    (∀ U, torusHkValueCLM (PN U) =
      cellTransverseProjection (F.reg.orient p) (torusHkValueCLM U)) →
    (∀ U, torusHkValueCLM (Pn U) =
      cellTransverseProjection (F.reg.orient p) (torusHkValueCLM U)) →
    ∑ i' ∈ stageSet b1wSt k', ‖Φ i' - Pn (Φ i')‖ ^ 2 ≤
      B ^ 2 * ∑ i ∈ stageSet b1wSt k, ‖ψ i - PN (ψ i)‖ ^ 2

/-- **The sharp transform families of every pair of stages.** -/
theorem b1w_sharp_family_provider (hSS : SharpSameLevelStatement.{u, v})
    (hSL : SharpLetterAEStatement.{u, v}) (K : ScalarConstants) (Nw D m : ℕ)
    (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool) (ρ : ℝ) (s₀ : ℕ)
    (hs₀ : (Finset.univ.sup d) + 3 ≤ s₀) (M₀ : ℝ) :
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
        B1WSharpFamily F θ r k k' (b1wLadderAt Nw s₀ d Ks k) (b1wLadderAt Nw s₀ d Ks k') ψ Φ
          B M₀ := by
  classical
  choose CS hCS hSSn using fun n => hSS K Nw D m d Ks ρ n M₀
  choose CL hCL hSLn using fun n => hSL K Nw D m d Ks pos ρ n M₀
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
  -- one null set of times for the letter families of all orders up to the top of the ladder
  have hae := ae_all_iff.2 fun n : Fin (top + 1) =>
    hSLn n.val g₁ F θ hlet (by have := n.isLt; omega) hρ
  filter_upwards [hae, ae_restrict_mem measurableSet_Icc] with r hrL hr
  intro k k' hkk ψ
  -- the zero family
  have hzero : (∀ i ∈ stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k,
      ∀ i' ∈ stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k',
        b1wTestTransform F θ i i' r (fun y => star
          (torusHigherClassicalValue (b1wLadderAt Nw s₀ d Ks k) (ψ i) y)) = 0) →
      ∃ Φ : B1WIndex ι h Nw m Ks → TorusHk (b1wLadderAt Nw s₀ d Ks k') ℂ,
        B1WSharpFamily F θ r k k' (b1wLadderAt Nw s₀ d Ks k) (b1wLadderAt Nw s₀ d Ks k') ψ Φ
          B M₀ := by
    intro hT
    refine ⟨fun _ => 0, fun i' hi' => ?_, ?_, sharpFamilyFacts_zero _ _ _ _ _ _ _ _ _ _,
      fun p _ PN Pn _ _ => ?_⟩
    · filter_upwards [Lp.coeFn_zero ℂ 2 (volume.restrict AVenhance.unitCube)] with y hy
      rw [map_zero, hy]
      refine (Finset.sum_eq_zero fun i hi => ?_).symm
      rw [hT i hi i' hi']
      simp
    · simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        Finset.sum_const_zero]
      exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _)
    · simp only [map_zero, sub_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, Finset.sum_const_zero]
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
  have hsq : ∀ {C : ℝ}, 0 ≤ C → C ≤ B → ∀ S : ℝ, 0 ≤ S → C ^ 2 * S ≤ B ^ 2 * S :=
    fun hC hCB S hS => mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hC hCB 2) hS
  have hS0 : ∀ {N : ℕ} (χ : B1WIndex ι h Nw m Ks → TorusHk N ℂ),
      0 ≤ ∑ i ∈ stageSet (b1wSt (ι := ι) (h := h) (Nw := Nw) (m := m) (Ks := Ks)) k,
        ‖χ i‖ ^ 2 := fun χ => Finset.sum_nonneg fun i _ => sq_nonneg _
  by_cases hsame : i₀'.1 = i₀.1
  · -- the same level
    have h1 : b1wLadderAt Nw s₀ d Ks k' + 1 ≤ b1wLadderAt Nw s₀ d Ks k := by
      rw [hN, hn]; exact b1wLadder_same_of_lt s₀ d i₀ i₀' hsame hlt
    obtain ⟨Φ, hΦv, hΦb, hΦs, hΦw⟩ := hSSn (b1wLadderAt Nw s₀ d Ks k') g₁ F θ hρ r hr k k'
      (fun i hi i' hi' => by rw [hlev i hi, hlev' i' hi', hsame]) _ h1 hNs ψ
    have hCB := hCSB _ hntop
    refine ⟨Φ, fun i' hi' => ?_, hΦb.trans (hsq (hCS _) hCB _ (hS0 ψ)),
      hΦs.mono (hCS _) hCB, fun p hp PN Pn hPN hPn =>
        (hΦw p hp PN Pn hPN hPn).trans (hsq (hCS _) hCB _ (hS0 _))⟩
    filter_upwards [hΦv i' hi'] with y hy
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
  by_cases hnext : ∃ l : Fin Nw, i₀.1 = l.succ ∧ i₀'.1 = l.castSucc
  · -- the next level
    obtain ⟨l, hl1, hl2⟩ := hnext
    have h1 : b1wLadderAt Nw s₀ d Ks k' + d l ≤ b1wLadderAt Nw s₀ d Ks k := by
      rw [hN, hn]; exact b1wLadder_letter_of_lt s₀ d l i₀ i₀' hl1 hl2 hlt
    obtain ⟨Φ, hΦv, hΦb, hΦs, hΦw⟩ := hrL ⟨b1wLadderAt Nw s₀ d Ks k', by omega⟩ l k k'
      (fun i hi => by rw [hlev i hi, hl1]) (fun i' hi' => by rw [hlev' i' hi', hl2]) _ h1 hNs ψ
    have hCB := hCLB _ hntop
    refine ⟨Φ, fun i' hi' => ?_, hΦb.trans (hsq (hCL _) hCB _ (hS0 ψ)),
      hΦs.mono (hCL _) hCB, fun p hp PN Pn hPN hPn =>
        (hΦw p hp PN Pn hPN hPn).trans (hsq (hCL _) hCB _ (hS0 _))⟩
    filter_upwards [hΦv i' hi'] with y hy
    rw [hy]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hne : i'.1 ≠ i.1 := by
      rw [hlev i hi, hlev' i' hi', hl1, hl2]
      exact (Fin.castSucc_lt_succ (i := l)).ne
    simp only [b1wTestTransform, b1wSameTransform, hne, ite_false, zero_add]
  · -- far levels: the transforms vanish
    refine hzero fun i hi i' hi' => ?_
    funext y
    refine congrFun (b1wTestTransform_zero_of_level F θ i i' ?_ ?_ r _) y
    · rw [hlev i hi, hlev' i' hi']
      exact hsame
    · intro l hl
      exact hnext ⟨l, (hlev i hi) ▸ hl.1, (hlev' i' hi') ▸ hl.2⟩

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleEvolution AVRegularity.CycleWords
namespace AVRegularity.CycleWords.Assembly

/-! # the sharp letter operators, reduced to four facts about the letter transform

`letterOps` gives operators `T` with the value formula (the conjugated stage letter transform)
and the plain block bound. The operator `T` is unique given the value formula (the value map of
`H^n` is injective), so the remaining clauses of `SharpLetterOpsStatement` are statements about
ANY operator family with that value formula. They are the four named facts below:
the slow-fast pairing, the two slow-test families, and the commutation with the transverse
projection. `sharpLetterOps_of_facts` assembles them (constant: the maximum). -/

section
universe u v

open Classical in
/-- **Open fact (slow-fast pairing).** For every operator family with the value formula of the conjugated
stage letter transform. -/
def SharpLetterPairFact : Prop :=
  ∀ (K : ScalarConstants) (Nw D m : ℕ) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool) (ρ : ℝ)
    (n : ℕ) (M₀ : ℝ),
  ∃ C0 : ℝ, 0 ≤ C0 ∧
  ∀ (g₁ : ℝ) {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
    (∀ l, (F.letters l).order = d l ∧ (F.letters l).slow = Ks l ∧
      (F.letters l).positive = pos l) →
    n + (Finset.univ.sup d) ≤ F.J →
    fibreNorm (planeFibreFrequency F.η θ) ≤ ρ →
  ∀ᵐ r ∂(volume.restrict (Icc F.a F.b)), ∀ (l : Fin Nw) (N : ℕ), n + d l ≤ N →
    (Finset.univ.sup d) + 3 ≤ N →
  ∀ T : B1WIndex ι h Nw m Ks → B1WIndex ι h Nw m Ks → TorusHk N ℂ →L[ℝ] TorusHk n ℂ,
    (∀ i i' : B1WIndex ι h Nw m Ks, i.1 = l.succ → i'.1 = l.castSucc → ∀ ψ : TorusHk N ℂ,
      (torusHkValueCLM (T i i' ψ) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] fun z =>
          b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
            star (b1wLetterTransform F θ i i' r
              (fun y => star (torusHigherClassicalValue N ψ y)) z)) →
    ∀ (S S' : Finset (B1WIndex ι h Nw m Ks)) (x x' : ι) (β β' : ℕ × ℕ),
      (∀ i ∈ S, i.1 = l.succ ∧ b1wKey i = (x, β)) →
      (∀ i' ∈ S', i'.1 = l.castSucc ∧ b1wKey i' = (x', β')) →
      let w0 : ℝ := (if LetterMomRel (Finset.univ.sup Ks) (Finset.univ.sup d + 1) β β'
              then 1 else 0) * letterCompWeight (F.letters l) x x'
      let ζ : ℝ := min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹)
      ∀ R : ComplexCellL2, ‖R‖ ≤ |M₀| * fibreNorm (planeFibreFrequency F.η θ) →
        ∀ f : B1WIndex ι h Nw m Ks → TorusHk N ℂ,
        ∑ i' ∈ S', ‖sharpPair R (∑ i ∈ S, T i i' (f i))‖ ^ 2 ≤
          (C0 * ζ * w0) ^ 2 * ∑ i ∈ S, ‖f i‖ ^ 2

open Classical in
/-- **Open fact (slow tests, norm).** For every operator family with the value formula of the conjugated
stage letter transform. -/
def SharpLetterSlowNormFact : Prop :=
  ∀ (K : ScalarConstants) (Nw D m : ℕ) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool) (ρ : ℝ)
    (n : ℕ) (M₀ : ℝ),
  ∃ C0 : ℝ, 0 ≤ C0 ∧
  ∀ (g₁ : ℝ) {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
    (∀ l, (F.letters l).order = d l ∧ (F.letters l).slow = Ks l ∧
      (F.letters l).positive = pos l) →
    n + (Finset.univ.sup d) ≤ F.J →
    fibreNorm (planeFibreFrequency F.η θ) ≤ ρ →
  ∀ᵐ r ∂(volume.restrict (Icc F.a F.b)), ∀ (l : Fin Nw) (N : ℕ), n + d l ≤ N →
    (Finset.univ.sup d) + 3 ≤ N →
  ∀ T : B1WIndex ι h Nw m Ks → B1WIndex ι h Nw m Ks → TorusHk N ℂ →L[ℝ] TorusHk n ℂ,
    (∀ i i' : B1WIndex ι h Nw m Ks, i.1 = l.succ → i'.1 = l.castSucc → ∀ ψ : TorusHk N ℂ,
      (torusHkValueCLM (T i i' ψ) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] fun z =>
          b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
            star (b1wLetterTransform F θ i i' r
              (fun y => star (torusHigherClassicalValue N ψ y)) z)) →
    ∀ (S S' : Finset (B1WIndex ι h Nw m Ks)) (x x' : ι) (β β' : ℕ × ℕ),
      (∀ i ∈ S, i.1 = l.succ ∧ b1wKey i = (x, β)) →
      (∀ i' ∈ S', i'.1 = l.castSucc ∧ b1wKey i' = (x', β')) →
      let w0 : ℝ := (if LetterMomRel (Finset.univ.sup Ks) (Finset.univ.sup d + 1) β β'
              then 1 else 0) * letterCompWeight (F.letters l) x x'
      let ζ : ℝ := min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹)
      ∀ (E : ℂ) (b : B1WIndex ι h Nw m Ks → ℂ) (Dd : TorusHk N ℂ),
        ‖Dd‖ ≤ M₀ * fibreNorm (planeFibreFrequency F.η θ) * ‖E‖ →
        ∀ f : B1WIndex ι h Nw m Ks → TorusHk N ℂ,
        (∀ i ∈ S, f i = torusHigherScalarCLM N (b i) (torusHigherConstant N E + Dd)) →
        ∑ i' ∈ S', ‖∑ i ∈ S, T i i' (f i)‖ ^ 2 ≤
          (C0 * ζ * w0) ^ 2 * ‖E‖ ^ 2 * ∑ i ∈ S, ‖b i‖ ^ 2

open Classical in
/-- **Open fact (slow tests, pairing).** For every operator family with the value formula of the conjugated
stage letter transform. -/
def SharpLetterSlowPairFact : Prop :=
  ∀ (K : ScalarConstants) (Nw D m : ℕ) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool) (ρ : ℝ)
    (n : ℕ) (M₀ : ℝ),
  ∃ C0 : ℝ, 0 ≤ C0 ∧
  ∀ (g₁ : ℝ) {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
    (∀ l, (F.letters l).order = d l ∧ (F.letters l).slow = Ks l ∧
      (F.letters l).positive = pos l) →
    n + (Finset.univ.sup d) ≤ F.J →
    fibreNorm (planeFibreFrequency F.η θ) ≤ ρ →
  ∀ᵐ r ∂(volume.restrict (Icc F.a F.b)), ∀ (l : Fin Nw) (N : ℕ), n + d l ≤ N →
    (Finset.univ.sup d) + 3 ≤ N →
  ∀ T : B1WIndex ι h Nw m Ks → B1WIndex ι h Nw m Ks → TorusHk N ℂ →L[ℝ] TorusHk n ℂ,
    (∀ i i' : B1WIndex ι h Nw m Ks, i.1 = l.succ → i'.1 = l.castSucc → ∀ ψ : TorusHk N ℂ,
      (torusHkValueCLM (T i i' ψ) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] fun z =>
          b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
            star (b1wLetterTransform F θ i i' r
              (fun y => star (torusHigherClassicalValue N ψ y)) z)) →
    ∀ (S S' : Finset (B1WIndex ι h Nw m Ks)) (x x' : ι) (β β' : ℕ × ℕ),
      (∀ i ∈ S, i.1 = l.succ ∧ b1wKey i = (x, β)) →
      (∀ i' ∈ S', i'.1 = l.castSucc ∧ b1wKey i' = (x', β')) →
      let w0 : ℝ := (if LetterMomRel (Finset.univ.sup Ks) (Finset.univ.sup d + 1) β β'
              then 1 else 0) * letterCompWeight (F.letters l) x x'
      let ζ : ℝ := min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹)
      ∀ (E : ℂ) (b : B1WIndex ι h Nw m Ks → ℂ) (Dd : TorusHk N ℂ),
        ‖Dd‖ ≤ M₀ * fibreNorm (planeFibreFrequency F.η θ) * ‖E‖ →
        ∀ f : B1WIndex ι h Nw m Ks → TorusHk N ℂ,
        (∀ i ∈ S, f i = torusHigherScalarCLM N (b i) (torusHigherConstant N E + Dd)) →
        ∀ R : ComplexCellL2, ‖R‖ ≤ |M₀| * fibreNorm (planeFibreFrequency F.η θ) →
          ∑ i' ∈ S', ‖sharpPair R (∑ i ∈ S, T i i' (f i))‖ ^ 2 ≤
            (C0 * ζ ^ 2 * w0) ^ 2 * ‖E‖ ^ 2 * ∑ i ∈ S, ‖b i‖ ^ 2

open Classical in
/-- **Commutation with the transverse projection** in the least window. -/
def SharpLetterCommFact : Prop :=
  ∀ (K : ScalarConstants) (Nw D m : ℕ) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool) (ρ : ℝ)
    (n : ℕ),
  ∀ (g₁ : ℝ) {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
    (∀ l, (F.letters l).order = d l ∧ (F.letters l).slow = Ks l ∧
      (F.letters l).positive = pos l) →
    n + (Finset.univ.sup d) ≤ F.J →
    fibreNorm (planeFibreFrequency F.η θ) ≤ ρ →
  ∀ᵐ r ∂(volume.restrict (Icc F.a F.b)), ∀ (l : Fin Nw) (N : ℕ), n + d l ≤ N →
    (Finset.univ.sup d) + 3 ≤ N →
  ∀ T : B1WIndex ι h Nw m Ks → B1WIndex ι h Nw m Ks → TorusHk N ℂ →L[ℝ] TorusHk n ℂ,
    (∀ i i' : B1WIndex ι h Nw m Ks, i.1 = l.succ → i'.1 = l.castSucc → ∀ ψ : TorusHk N ℂ,
      (torusHkValueCLM (T i i' ψ) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] fun z =>
          b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
            star (b1wLetterTransform F θ i i' r
              (fun y => star (torusHigherClassicalValue N ψ y)) z)) →
    ∀ p, IsLeastWindow F.reg p r →
      ∀ (PN : TorusHk N ℂ →L[ℝ] TorusHk N ℂ) (Pn : TorusHk n ℂ →L[ℝ] TorusHk n ℂ),
      (∀ U, torusHkValueCLM (PN U) =
        cellTransverseProjection (F.reg.orient p) (torusHkValueCLM U)) →
      (∀ U, torusHkValueCLM (Pn U) =
        cellTransverseProjection (F.reg.orient p) (torusHkValueCLM U)) →
      ∀ i i' : B1WIndex ι h Nw m Ks, i.1 = l.succ → i'.1 = l.castSucc →
        ∀ φ : TorusHk N ℂ, Pn (T i i' φ) = T i i' (PN φ)


theorem sharpLetter_sq_mono (C C' a b : ℝ) (hC : 0 ≤ C) (hCC : C ≤ C') (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (C * a * b) ^ 2 ≤ (C' * a * b) ^ 2 := by
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have h : C * a * b ≤ C' * a * b := by
    rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right hCC hab
  exact pow_le_pow_left₀ (by positivity) h 2

open Classical in
/-- **Assembly of `SharpLetterOpsStatement`** from `letterOps` and the four facts. -/
theorem sharpLetterOps_of_facts (h2 : SharpLetterPairFact.{u, v})
    (h3 : SharpLetterSlowNormFact.{u, v}) (h4 : SharpLetterSlowPairFact.{u, v})
    (h5 : SharpLetterCommFact.{u, v}) : SharpLetterOpsStatement.{u, v} := by
  intro K Nw D m d Ks pos ρ n M₀
  obtain ⟨C1, hC1, k1⟩ := letterOps.{u, v} K Nw D m d Ks pos ρ n
  obtain ⟨C2, hC2, k2⟩ := h2 K Nw D m d Ks pos ρ n M₀
  obtain ⟨C3, hC3, k3⟩ := h3 K Nw D m d Ks pos ρ n M₀
  obtain ⟨C4, hC4, k4⟩ := h4 K Nw D m d Ks pos ρ n M₀
  have k5 := h5 K Nw D m d Ks pos ρ n
  refine ⟨max (max C1 C2) (max C3 C4), le_max_of_le_left (le_max_of_le_left hC1), ?_⟩
  intro g₁ ι _ h _ _ _ _ _ _ F θ hlet hJ hρ
  filter_upwards [k1 g₁ F θ hlet hJ hρ, k2 g₁ F θ hlet hJ hρ, k3 g₁ F θ hlet hJ hρ,
    k4 g₁ F θ hlet hJ hρ, k5 g₁ F θ hlet hJ hρ] with r a1 a2 a3 a4 a5
  intro l N hN1 hN2
  obtain ⟨T, hTv, hTb⟩ := a1 l N hN1 hN2
  have b2 := a2 l N hN1 hN2 T hTv
  have b3 := a3 l N hN1 hN2 T hTv
  have b4 := a4 l N hN1 hN2 T hTv
  refine ⟨T, hTv, ?_, a5 l N hN1 hN2 T hTv⟩
  intro S S' x x' β β' hS hS' w0 ζ
  have hw0 : 0 ≤ w0 := mul_nonneg (by split_ifs <;> simp)
    (letterCompWeight_nonneg (F.piece.hlet l) x x')
  have hx0 := fibreNorm_nonneg (planeFibreFrequency F.η θ)
  have hiv : 0 ≤ (Real.sqrt F.S)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  have hζ : 0 ≤ ζ := le_min zero_le_one (by linarith)
  have hζ2 : 0 ≤ ζ ^ 2 := sq_nonneg _
  have m1 : C1 ≤ max (max C1 C2) (max C3 C4) := le_max_of_le_left (le_max_left _ _)
  have m2 : C2 ≤ max (max C1 C2) (max C3 C4) := le_max_of_le_left (le_max_right _ _)
  have m3 : C3 ≤ max (max C1 C2) (max C3 C4) := le_max_of_le_right (le_max_left _ _)
  have m4 : C4 ≤ max (max C1 C2) (max C3 C4) := le_max_of_le_right (le_max_right _ _)
  have one := sharpLetter_sq_mono C1 _ 1 w0 hC1 m1 zero_le_one hw0
  refine ⟨fun f => ?_, fun R hR f => ?_, fun E b Dd hD f hf => ?_⟩
  · refine (hTb S S' x x' β β' hS hS' f).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => by positivity)
    refine le_trans (le_of_eq ?_) (le_trans one (le_of_eq ?_))
    · simp only [w0, mul_one, mul_assoc]
    · rw [mul_one]
  · refine (b2 S S' x x' β β' hS hS' R hR f).trans ?_
    exact mul_le_mul_of_nonneg_right (sharpLetter_sq_mono C2 _ ζ w0 hC2 m2 hζ hw0)
      (Finset.sum_nonneg fun _ _ => by positivity)
  · refine ⟨(b3 S S' x x' β β' hS hS' E b Dd hD f hf).trans ?_, fun R hR => ?_⟩
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (sharpLetter_sq_mono C3 _ ζ w0 hC3 m3 hζ hw0)
          (sq_nonneg _)) (Finset.sum_nonneg fun _ _ => by positivity)
    · refine (b4 S S' x x' β β' hS hS' E b Dd hD f hf R hR).trans ?_
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (sharpLetter_sq_mono C4 _ (ζ ^ 2) w0 hC4 m4 hζ2 hw0)
          (sq_nonneg _)) (Finset.sum_nonneg fun _ _ => by positivity)
end

/-! # the helper statements for the three letter facts

Once the scale ratio of the families is
counted, every term of the letter transform carries one extra power of `ϖ`, except the derivative
variant with zero moment shift (`a = 0`), whose mean carries a factor `θ`.  The operators are split
accordingly into a gain part `Tg` (norm `O(ϖ)`) and a remainder `T0` (mean `O(|θ|)`, norm `O(|θ|)` on
constants).  `SharpLetterGainFact` states the split; `SharpLetterConstMeanFact` is the mean of the
full family on constants at order `ζ²`. -/

section
universe u v

open Classical in
/-- **The gain helper.** The split `T = Tg + T0` of the letter operators: `Tg` has block norm
`O(ϖ)`, the mean of `T0` is `O(|θ|)` on every family, and `T0` has block norm `O(|θ|)` on constants. -/
def SharpLetterGainFact : Prop :=
  ∀ (K : ScalarConstants) (Nw D m : ℕ) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool) (ρ : ℝ)
    (n : ℕ),
  ∃ C0 : ℝ, 0 ≤ C0 ∧
  ∀ (g₁ : ℝ) {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
    (∀ l, (F.letters l).order = d l ∧ (F.letters l).slow = Ks l ∧
      (F.letters l).positive = pos l) →
    n + (Finset.univ.sup d) ≤ F.J →
    fibreNorm (planeFibreFrequency F.η θ) ≤ ρ →
  ∀ᵐ r ∂(volume.restrict (Icc F.a F.b)), ∀ (l : Fin Nw) (N : ℕ) (hN1 : n + d l ≤ N),
    (Finset.univ.sup d) + 3 ≤ N →
  ∃ Tg T0 : B1WIndex ι h Nw m Ks → B1WIndex ι h Nw m Ks → TorusHk N ℂ →L[ℝ] TorusHk n ℂ,
    (∀ i i' : B1WIndex ι h Nw m Ks, i.1 = l.succ → i'.1 = l.castSucc → ∀ ψ : TorusHk N ℂ,
      (torusHkValueCLM (Tg i i' ψ + T0 i i' ψ) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] fun z =>
          b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
            star (b1wLetterTransform F θ i i' r
              (fun y => star (torusHigherClassicalValue N ψ y)) z)) ∧
    ∀ (S S' : Finset (B1WIndex ι h Nw m Ks)) (x x' : ι) (β β' : ℕ × ℕ),
      (∀ i ∈ S, i.1 = l.succ ∧ b1wKey i = (x, β)) →
      (∀ i' ∈ S', i'.1 = l.castSucc ∧ b1wKey i' = (x', β')) →
      let w0 : ℝ := (if LetterMomRel (Finset.univ.sup Ks) (Finset.univ.sup d + 1) β β'
              then 1 else 0) * letterCompWeight (F.letters l) x x'
      (∀ f : B1WIndex ι h Nw m Ks → TorusHk N ℂ,
        ∑ i' ∈ S', ‖∑ i ∈ S, Tg i i' (f i)‖ ^ 2 ≤
          (C0 * F.ϖ * w0) ^ 2 * ∑ i ∈ S, ‖truncateTorusHk hN1 (f i)‖ ^ 2) ∧
      (∀ f : B1WIndex ι h Nw m Ks → TorusHk N ℂ,
        ∑ i' ∈ S', ‖cellMeanCLM (torusHkValueCLM (∑ i ∈ S, T0 i i' (f i)))‖ ^ 2 ≤
          (C0 * fibreNorm (planeFibreFrequency F.η θ) * w0) ^ 2 * ∑ i ∈ S, ‖f i‖ ^ 2) ∧
      (∀ (E : ℂ) (b : B1WIndex ι h Nw m Ks → ℂ),
        ∑ i' ∈ S', ‖∑ i ∈ S, T0 i i' (torusHigherScalarCLM N (b i) (torusHigherConstant N E))‖ ^ 2 ≤
          (C0 * fibreNorm (planeFibreFrequency F.η θ) * w0) ^ 2 * ‖E‖ ^ 2 * ∑ i ∈ S, ‖b i‖ ^ 2)

open Classical in
/-- **The constant mean helper.** The mean of the full family on constants is of order `ζ²`. -/
def SharpLetterConstMeanFact : Prop :=
  ∀ (K : ScalarConstants) (Nw D m : ℕ) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool) (ρ : ℝ)
    (n : ℕ),
  ∃ C0 : ℝ, 0 ≤ C0 ∧
  ∀ (g₁ : ℝ) {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
    (∀ l, (F.letters l).order = d l ∧ (F.letters l).slow = Ks l ∧
      (F.letters l).positive = pos l) →
    n + (Finset.univ.sup d) ≤ F.J →
    fibreNorm (planeFibreFrequency F.η θ) ≤ ρ →
  ∀ᵐ r ∂(volume.restrict (Icc F.a F.b)), ∀ (l : Fin Nw) (N : ℕ), n + d l ≤ N →
    (Finset.univ.sup d) + 3 ≤ N →
  ∀ T : B1WIndex ι h Nw m Ks → B1WIndex ι h Nw m Ks → TorusHk N ℂ →L[ℝ] TorusHk n ℂ,
    (∀ i i' : B1WIndex ι h Nw m Ks, i.1 = l.succ → i'.1 = l.castSucc → ∀ ψ : TorusHk N ℂ,
      (torusHkValueCLM (T i i' ψ) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] fun z =>
          b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
            star (b1wLetterTransform F θ i i' r
              (fun y => star (torusHigherClassicalValue N ψ y)) z)) →
    ∀ (S S' : Finset (B1WIndex ι h Nw m Ks)) (x x' : ι) (β β' : ℕ × ℕ),
      (∀ i ∈ S, i.1 = l.succ ∧ b1wKey i = (x, β)) →
      (∀ i' ∈ S', i'.1 = l.castSucc ∧ b1wKey i' = (x', β')) →
      let w0 : ℝ := (if LetterMomRel (Finset.univ.sup Ks) (Finset.univ.sup d + 1) β β'
              then 1 else 0) * letterCompWeight (F.letters l) x x'
      let ζ : ℝ := min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹)
      ∀ (E : ℂ) (b : B1WIndex ι h Nw m Ks → ℂ),
        ∑ i' ∈ S', ‖cellMeanCLM (torusHkValueCLM
            (∑ i ∈ S, T i i' (torusHigherScalarCLM N (b i) (torusHigherConstant N E))))‖ ^ 2 ≤
          (C0 * ζ ^ 2 * w0) ^ 2 * ‖E‖ ^ 2 * ∑ i ∈ S, ‖b i‖ ^ 2
end

/-! # algebra for the three letter facts

Minkowski for sums of squares, the comparison of `ϖ` and `|ξ|` with `ζ`, and the uniqueness of the
operators with a given value formula. -/

section
universe u v

theorem sl80_l2_add {α : Type*} (s : Finset α) (x y : α → ℝ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h1 : ∑ i ∈ s, x i ^ 2 ≤ A ^ 2) (h2 : ∑ i ∈ s, y i ^ 2 ≤ B ^ 2) :
    ∑ i ∈ s, (x i + y i) ^ 2 ≤ (A + B) ^ 2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s x y
  have hxy : ∑ i ∈ s, x i * y i ≤ A * B := by
    by_contra hlt
    rw [not_le] at hlt
    have hAB : 0 ≤ A * B := mul_nonneg hA hB
    have h5 : (A * B) ^ 2 < (∑ i ∈ s, x i * y i) ^ 2 := pow_lt_pow_left₀ hlt hAB (by norm_num)
    have h3 : (∑ i ∈ s, x i ^ 2) * (∑ i ∈ s, y i ^ 2) ≤ A ^ 2 * B ^ 2 :=
      mul_le_mul h1 h2 (Finset.sum_nonneg fun i _ => sq_nonneg _) (sq_nonneg _)
    have h4 : (A * B) ^ 2 = A ^ 2 * B ^ 2 := by ring
    linarith
  calc ∑ i ∈ s, (x i + y i) ^ 2
      = ∑ i ∈ s, x i ^ 2 + 2 * ∑ i ∈ s, x i * y i + ∑ i ∈ s, y i ^ 2 := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ A ^ 2 + 2 * (A * B) + B ^ 2 := by linarith
    _ = (A + B) ^ 2 := by ring

theorem sl80_sum3 {α : Type*} (s : Finset α) (a x y z : α → ℝ) (P Q R Sg : ℝ)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hR : 0 ≤ R) (hSg : 0 ≤ Sg)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hle : ∀ i ∈ s, a i ≤ x i + y i + z i)
    (h1 : ∑ i ∈ s, x i ^ 2 ≤ P ^ 2 * Sg) (h2 : ∑ i ∈ s, y i ^ 2 ≤ Q ^ 2 * Sg)
    (h3 : ∑ i ∈ s, z i ^ 2 ≤ R ^ 2 * Sg) :
    ∑ i ∈ s, a i ^ 2 ≤ (P + Q + R) ^ 2 * Sg := by
  have hs := Real.sqrt_nonneg Sg
  have hsq : Real.sqrt Sg ^ 2 = Sg := Real.sq_sqrt hSg
  have e : ∀ T : ℝ, T ^ 2 * Sg = (T * Real.sqrt Sg) ^ 2 := fun T => by rw [mul_pow, hsq]
  rw [e] at h1 h2 h3 ⊢
  have m12 := sl80_l2_add s x y _ _ (mul_nonneg hP hs) (mul_nonneg hQ hs) h1 h2
  have m123 := sl80_l2_add s (fun i => x i + y i) z _ _
    (add_nonneg (mul_nonneg hP hs) (mul_nonneg hQ hs)) (mul_nonneg hR hs) m12 h3
  calc ∑ i ∈ s, a i ^ 2 ≤ ∑ i ∈ s, (x i + y i + z i) ^ 2 :=
        Finset.sum_le_sum fun i hi => pow_le_pow_left₀ (ha i hi) (hle i hi) 2
    _ ≤ _ := m123
    _ = _ := by ring

theorem sl80_sq_le (a b Sg : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hSg : 0 ≤ Sg) :
    a ^ 2 * Sg ≤ b ^ 2 * Sg :=
  mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hab 2) hSg

theorem sl80_eq_of_value {n : ℕ} (U V : TorusHk n ℂ)
    (h : (torusHkValueCLM U : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      (torusHkValueCLM V : Vec 2 → ℂ)) : U = V := by
  apply TorusHk.ext_value
  change torusHkValueCLM U = torusHkValueCLM V
  exact Lp.ext h

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {K : ScalarConstants} {g₁ : ℝ} {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- `ϖ` is nonnegative and at most `ζ`. -/
theorem sl80_varpi (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) :
    0 ≤ F.ϖ ∧ F.ϖ ≤ min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹) := by
  have hη := F.piece.hη
  have hη1 := F.piece.hη1
  have hS := F.piece.hS
  have hϖ := F.piece.hϖ
  have hx0 := fibreNorm_nonneg (planeFibreFrequency F.η θ)
  refine ⟨by rw [hϖ]; exact Real.sqrt_nonneg _, ?_⟩
  rw [hϖ]; exact varpi_le_zeta F.η F.S _ hη hη1 hS hx0

/-- The scale `ζ` is nonnegative and dominates `|ξ|/(1+|ρ|)`. -/
theorem sl80_zeta (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (ρ : ℝ) (hρ : fibreNorm (planeFibreFrequency F.η θ) ≤ ρ) :
    0 ≤ min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹) ∧
    fibreNorm (planeFibreFrequency F.η θ) ≤
      (1 + |ρ|) * min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹) := by
  have hx0 := fibreNorm_nonneg (planeFibreFrequency F.η θ)
  have hiv : 0 ≤ (Real.sqrt F.S)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  exact ⟨le_min zero_le_one (by linarith), zeta_x_le _ F.S ρ hx0 hρ⟩

/-- The value formula of a letter family. -/
def Sl80Val (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (r : ℝ)
    (l : Fin Nw) (N n : ℕ)
    (T : B1WIndex ι h Nw m Ks → B1WIndex ι h Nw m Ks → TorusHk N ℂ →L[ℝ] TorusHk n ℂ) : Prop :=
  ∀ i i' : B1WIndex ι h Nw m Ks, i.1 = l.succ → i'.1 = l.castSucc → ∀ ψ : TorusHk N ℂ,
      (torusHkValueCLM (T i i' ψ) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] fun z =>
          b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
            star (b1wLetterTransform F θ i i' r
              (fun y => star (torusHigherClassicalValue N ψ y)) z)

/-- Two families with the same value formula agree. -/
theorem sl80_val_unique {F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁}
    {θ : Vec 2} {r : ℝ} {l : Fin Nw} {N n : ℕ}
    {T T' : B1WIndex ι h Nw m Ks → B1WIndex ι h Nw m Ks → TorusHk N ℂ →L[ℝ] TorusHk n ℂ}
    (h1 : Sl80Val F θ r l N n T) (h2 : Sl80Val F θ r l N n T')
    (i i' : B1WIndex ι h Nw m Ks) (hi : i.1 = l.succ) (hi' : i'.1 = l.castSucc) (ψ : TorusHk N ℂ) :
    T i i' ψ = T' i i' ψ :=
  sl80_eq_of_value _ _ ((h1 i i' hi hi' ψ).trans (h2 i i' hi hi' ψ).symm)

/-- The split of a family with the value formula. -/
theorem sl80_split {F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁}
    {θ : Vec 2} {r : ℝ} {l : Fin Nw} {N n : ℕ}
    {T Tg T0 : B1WIndex ι h Nw m Ks → B1WIndex ι h Nw m Ks → TorusHk N ℂ →L[ℝ] TorusHk n ℂ}
    (h1 : Sl80Val F θ r l N n T)
    (h2 : ∀ i i' : B1WIndex ι h Nw m Ks, i.1 = l.succ → i'.1 = l.castSucc → ∀ ψ : TorusHk N ℂ,
      (torusHkValueCLM (Tg i i' ψ + T0 i i' ψ) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] fun z =>
          b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
            star (b1wLetterTransform F θ i i' r
              (fun y => star (torusHigherClassicalValue N ψ y)) z))
    (i i' : B1WIndex ι h Nw m Ks) (hi : i.1 = l.succ) (hi' : i'.1 = l.castSucc) (ψ : TorusHk N ℂ) :
    T i i' ψ = Tg i i' ψ + T0 i i' ψ :=
  sl80_eq_of_value _ _ ((h1 i i' hi hi' ψ).trans (h2 i i' hi hi' ψ).symm)

end Frame
end

/-! # `SharpLetterPairFact` from the helper `SharpLetterGainFact` -/

section
universe u v

open Classical in
/-- **The slow-fast pairing fact** from the gain split and the plain letter bound. -/
theorem sharpLetterPair_of_gain (hG : SharpLetterGainFact.{u, v}) : SharpLetterPairFact.{u, v} := by
  intro K Nw D m d Ks pos ρ n M₀
  obtain ⟨C, hC, kG⟩ := hG K Nw D m d Ks pos ρ n
  obtain ⟨C1, hC1, k1⟩ := letterOps.{u, v} K Nw D m d Ks pos ρ n
  refine ⟨C + C * (1 + |ρ|) + |M₀| * (1 + |ρ|) * C1, by positivity, ?_⟩
  intro g₁ ι _ h _ _ _ _ _ _ F θ hlet hJ hρ
  filter_upwards [kG g₁ F θ hlet hJ hρ, k1 g₁ F θ hlet hJ hρ] with r a1 a2
  intro l N hN1 hN2
  obtain ⟨Tg, T0, hv, hb⟩ := a1 l N hN1 hN2
  obtain ⟨T', hT'v, hT'b⟩ := a2 l N hN1 hN2
  intro T hTv S S' x x' β β' hS hS' w0 ζ R hR f
  obtain ⟨hb1, hb2, -⟩ := hb S S' x x' β β' hS hS'
  have hbT := hT'b S S' x x' β β' hS hS' f
  obtain ⟨hϖ0, hϖζ⟩ := sl80_varpi F θ
  obtain ⟨hζ0, hxζ⟩ := sl80_zeta F θ ρ hρ
  have hx0 := fibreNorm_nonneg (planeFibreFrequency F.η θ)
  have hw0 : 0 ≤ w0 := mul_nonneg (by split_ifs <;> simp)
    (letterCompWeight_nonneg (F.piece.hlet l) x x')
  have hSg : 0 ≤ ∑ i ∈ S, ‖f i‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have eqT : ∀ i ∈ S, ∀ i' ∈ S', T i i' = T' i i' := fun i hi i' hi' => by
    exact ContinuousLinearMap.ext fun ψ =>
      sl80_val_unique hTv hT'v i i' (hS i hi).1 (hS' i' hi').1 ψ
  have eqsplit : ∀ i ∈ S, ∀ i' ∈ S', ∀ ψ, T i i' ψ = Tg i i' ψ + T0 i i' ψ :=
    fun i hi i' hi' ψ => sl80_split hTv hv i i' (hS i hi).1 (hS' i' hi').1 ψ
  have hU : ∀ i' ∈ S', ∑ i ∈ S, T i i' (f i) = ∑ i ∈ S, Tg i i' (f i) + ∑ i ∈ S, T0 i i' (f i) :=
    fun i' hi' => by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i hi => eqsplit i hi i' hi' _
  have hUT' : ∀ i' ∈ S', ∑ i ∈ S, T i i' (f i) = ∑ i ∈ S, T' i i' (f i) := fun i' hi' =>
    Finset.sum_congr rfl fun i hi => by rw [eqT i hi i' hi']
  -- the pointwise bound
  have hpt : ∀ i' ∈ S', ‖sharpPair R (∑ i ∈ S, T i i' (f i))‖ ≤
      ‖∑ i ∈ S, Tg i i' (f i)‖ + ‖cellMeanCLM (torusHkValueCLM (∑ i ∈ S, T0 i i' (f i)))‖ +
        ‖R‖ * ‖∑ i ∈ S, T i i' (f i)‖ := by
    intro i' hi'
    refine (sharpPair_le_mean R _).trans ?_
    rw [hU i' hi', map_add, map_add]
    have h1 : ‖cellMeanCLM (torusHkValueCLM (∑ i ∈ S, Tg i i' (f i)))‖ ≤
        ‖∑ i ∈ S, Tg i i' (f i)‖ :=
      (cellMeanCLM_norm_le _).trans (sharp_value_norm_le _)
    have h2 := norm_add_le (cellMeanCLM (torusHkValueCLM (∑ i ∈ S, Tg i i' (f i))))
      (cellMeanCLM (torusHkValueCLM (∑ i ∈ S, T0 i i' (f i))))
    rw [← hU i' hi']
    linarith
  have hnorm1 : ∑ i' ∈ S', ‖∑ i ∈ S, Tg i i' (f i)‖ ^ 2 ≤ (C * ζ * w0) ^ 2 * ∑ i ∈ S, ‖f i‖ ^ 2 := by
    refine hb1 f |>.trans ?_
    have hs : ∑ i ∈ S, ‖truncateTorusHk hN1 (f i)‖ ^ 2 ≤ ∑ i ∈ S, ‖f i‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _)
        (truncateTorusHk_norm_le _ _) 2
    have hm : (C * F.ϖ * w0) ^ 2 ≤ (C * ζ * w0) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by gcongr) 2
    exact mul_le_mul hm hs (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)
  have hnorm2 : ∑ i' ∈ S', ‖cellMeanCLM (torusHkValueCLM (∑ i ∈ S, T0 i i' (f i)))‖ ^ 2 ≤
      (C * (1 + |ρ|) * ζ * w0) ^ 2 * ∑ i ∈ S, ‖f i‖ ^ 2 := by
    have hle : C * fibreNorm (planeFibreFrequency F.η θ) * w0 ≤ C * (1 + |ρ|) * ζ * w0 := by
      calc C * fibreNorm (planeFibreFrequency F.η θ) * w0 ≤ C * ((1 + |ρ|) * ζ) * w0 := by gcongr
        _ = _ := by ring
    exact (hb2 f).trans (sl80_sq_le _ _ _ (by positivity) hle hSg)
  have hUsum : ∑ i' ∈ S', ‖∑ i ∈ S, T i i' (f i)‖ ^ 2 ≤ (C1 * w0) ^ 2 * ∑ i ∈ S, ‖f i‖ ^ 2 := by
    have e : C1 * (if LetterMomRel (Finset.univ.sup Ks) (Finset.univ.sup d + 1) β β'
        then 1 else 0) * letterCompWeight (F.letters l) x x' = C1 * w0 := by
      simp only [w0]; ring
    rw [e] at hbT
    refine le_trans (le_of_eq ?_) hbT
    exact Finset.sum_congr rfl fun i' hi' => by rw [hUT' i' hi']
  have hnorm3 : ∑ i' ∈ S', (‖R‖ * ‖∑ i ∈ S, T i i' (f i)‖) ^ 2 ≤
      (|M₀| * (1 + |ρ|) * C1 * ζ * w0) ^ 2 * ∑ i ∈ S, ‖f i‖ ^ 2 := by
    have hR' : ‖R‖ ≤ |M₀| * ((1 + |ρ|) * ζ) :=
      hR.trans (mul_le_mul_of_nonneg_left hxζ (abs_nonneg _))
    calc ∑ i' ∈ S', (‖R‖ * ‖∑ i ∈ S, T i i' (f i)‖) ^ 2
        = ‖R‖ ^ 2 * ∑ i' ∈ S', ‖∑ i ∈ S, T i i' (f i)‖ ^ 2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
      _ ≤ ‖R‖ ^ 2 * ((C1 * w0) ^ 2 * ∑ i ∈ S, ‖f i‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hUsum (sq_nonneg _)
      _ ≤ (|M₀| * ((1 + |ρ|) * ζ)) ^ 2 * ((C1 * w0) ^ 2 * ∑ i ∈ S, ‖f i‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hR' 2)
            (mul_nonneg (sq_nonneg _) hSg)
      _ = _ := by ring
  have key := sl80_sum3 S' (fun i' => ‖sharpPair R (∑ i ∈ S, T i i' (f i))‖)
    (fun i' => ‖∑ i ∈ S, Tg i i' (f i)‖)
    (fun i' => ‖cellMeanCLM (torusHkValueCLM (∑ i ∈ S, T0 i i' (f i)))‖)
    (fun i' => ‖R‖ * ‖∑ i ∈ S, T i i' (f i)‖) (C * ζ * w0) (C * (1 + |ρ|) * ζ * w0)
    (|M₀| * (1 + |ρ|) * C1 * ζ * w0) (∑ i ∈ S, ‖f i‖ ^ 2) (by positivity) (by positivity)
    (by positivity) hSg (fun _ _ => norm_nonneg _) hpt hnorm1 hnorm2 hnorm3
  refine key.trans (le_of_eq ?_)
  ring
end

end AVRegularity.CycleWords.Assembly
end
