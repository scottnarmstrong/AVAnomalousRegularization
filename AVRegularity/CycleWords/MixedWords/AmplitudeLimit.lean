-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.FibreDuality
import AVRegularity.Analysis.Convolution
import AVRegularity.CycleWords.MixedWords.BlochContinuity
import Mathlib.Combinatorics.SimpleGraph.Basic

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! Integrate the finite-lattice derivative bound, then use Parseval and the physical
moment norm. All constants are independent of the support radius and the component spaces. -/

def blochMomentCoeff (n k : ℕ) (B : ℝ) : ℝ :=
  ((k + 1 : ℕ) * 2 ^ k : ℝ) *
    (∑ l ∈ Finset.range (k + 1), (2 : ℝ) ^ (k - l) * ((k.choose l : ℝ) * B) ^ 2) *
      (2 * Real.pi) ^ 2 * (n.factorial : ℝ) ^ 2

theorem blochMomentCoeff_nonneg (n k : ℕ) (B : ℝ) : 0 ≤ blochMomentCoeff n k B := by
  unfold blochMomentCoeff
  positivity

section Pair
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem pair_bound_point_ennreal {n : ℕ} {χlo : Vec 2 → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χlo) {B : ℝ}
    (hB : ∀ l ≤ n, ∀ θ, ‖iteratedFDeriv ℝ l χlo θ‖ ≤ B)
    {η ϖ : ℝ} (hη : 0 < η) (hϖ : 0 < ϖ) (hϖη : ϖ ≤ Real.sqrt η)
    {G : Vec 2 → E} {R : ℝ} (hG : ∀ y : Vec 2, R < ‖y‖ → G y = 0)
    {N : ℕ} (hN : R + 1 ≤ N) {z : Vec 2} (hz : z ∈ AVenhance.unitCube)
    {α : ℕ × ℕ} (hα : α.1 + α.2 ≤ n) (θ : Vec 2) :
    ENNReal.ofReal (ϖ ^ (2 * (α.1 + α.2))) *
        (ENNReal.ofReal (‖thetaPartial α.1 α.2
          (fun θ' => χlo ((Real.sqrt η)⁻¹ • θ') • blochCos θ' G z) θ‖ ^ 2) +
        ENNReal.ofReal (‖thetaPartial α.1 α.2
          (fun θ' => χlo ((Real.sqrt η)⁻¹ • θ') • blochSin θ' G z) θ‖ ^ 2)) ≤
      ENNReal.ofReal ((α.1 + α.2 + 1 : ℕ) * 2 ^ (α.1 + α.2) : ℝ) *
        ∑ l ∈ Finset.range (α.1 + α.2 + 1), ∑ idx : Fin (α.1 + α.2 - l) → Fin 2,
          ENNReal.ofReal (((α.1 + α.2).choose l : ℝ) * B) ^ 2 *
            latticePair (latticeBox N) (fun y => wordMonomial idx (ϖ • y) • G y) θ z := by
  have h := ENNReal.ofReal_le_ofReal (pair_bound_point hχ hB hη hϖ hϖη hG hN hz hα θ)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le n) 0)
  rw [ENNReal.ofReal_mul (by positivity)] at h
  rw [ENNReal.ofReal_mul (by positivity)] at h
  rw [ENNReal.ofReal_sum_of_nonneg (by intros; positivity)] at h
  conv_rhs at h =>
    enter [2, 2, l]
    rw [ENNReal.ofReal_sum_of_nonneg (by intros; positivity)]
  simpa (disch := positivity) only [latticePair, ENNReal.ofReal_mul,
    ENNReal.ofReal_add, ENNReal.ofReal_pow] using h

end Pair

section Family
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)]

theorem compact_bloch_fibre_sq_le {n : ℕ} {χlo : Vec 2 → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χlo) {B : ℝ}
    (hB : ∀ l ≤ n, ∀ θ, ‖iteratedFDeriv ℝ l χlo θ‖ ≤ B)
    {η ϖ : ℝ} (hη : 0 < η) (hϖ : 0 < ϖ) (hϖη : ϖ ≤ Real.sqrt η)
    (π : ι → ℝ) (F : ∀ x, Vec 2 → h x) (R : ι → ℝ) (N : ι → ℕ)
    (hF : ∀ x, Continuous (F x))
    (hsupp : ∀ x y, R x < ‖y‖ → F x y = 0) (hN : ∀ x, R x + 1 ≤ N x)
    {α : ℕ × ℕ} (hα : α.1 + α.2 ≤ n) (θ : Vec 2) :
    ENNReal.ofReal (ϖ ^ (2 * (α.1 + α.2))) *
        blochFibreDerivNorm π (fun θ' => χlo ((Real.sqrt η)⁻¹ • θ')) α F θ ^ 2 ≤
      ∑ x, ENNReal.ofReal ((π x)⁻¹) *
        (ENNReal.ofReal ((α.1 + α.2 + 1 : ℕ) * 2 ^ (α.1 + α.2) : ℝ) *
          ∑ l ∈ Finset.range (α.1 + α.2 + 1), ∑ idx : Fin (α.1 + α.2 - l) → Fin 2,
            ENNReal.ofReal (((α.1 + α.2).choose l : ℝ) * B) ^ 2 *
              ∫⁻ z in AVenhance.unitCube,
                latticePair (latticeBox (N x)) (fun y => wordMonomial idx (ϖ • y) • F x y) θ z) := by
  unfold blochFibreDerivNorm
  rw [rpow_half_sq, ← lintegral_const_mul' _ _ (by simp)]
  have hcont (x : ι) (l : ℕ) (idx : Fin (α.1 + α.2 - l) → Fin 2) :
      Continuous fun y => wordMonomial idx (ϖ • y) • F x y :=
    ((wordMonomial_contDiff idx).continuous.comp (continuous_const_smul ϖ)).smul (hF x)
  have hQ (x : ι) (l : ℕ) (idx : Fin (α.1 + α.2 - l) → Fin 2) :
      Measurable fun z => latticePair (latticeBox (N x))
        (fun y => wordMonomial idx (ϖ • y) • F x y) θ z :=
    Measurable.of_uncurry_left
      (measurable_latticePair (E := h x) (latticeBox (N x)) (hcont x l idx))
  have hout := lintegral_weighted_sum (volume.restrict AVenhance.unitCube)
    (fun x => ENNReal.ofReal ((π x)⁻¹))
    (ENNReal.ofReal ((α.1 + α.2 + 1 : ℕ) * 2 ^ (α.1 + α.2) : ℝ))
    (Finset.range (α.1 + α.2 + 1))
    (fun l => ENNReal.ofReal (((α.1 + α.2).choose l : ℝ) * B) ^ 2)
    (fun x l (idx : Fin (α.1 + α.2 - l) → Fin 2) z =>
      latticePair (latticeBox (N x)) (fun y => wordMonomial idx (ϖ • y) • F x y) θ z)
    hQ
  rw [← hout]
  have hcell : MeasurableSet AVenhance.unitCube :=
    MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Ioo
  refine lintegral_mono_ae (ae_restrict_of_forall_mem hcell fun z hz => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [mul_left_comm]
  exact mul_le_mul_right
    (pair_bound_point_ennreal hχ hB hη hϖ hϖη (hsupp x) (hN x) hz hα θ) _

theorem compact_bloch_fibre_majorant {n : ℕ} {χlo : Vec 2 → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χlo) {B : ℝ}
    (hB : ∀ l ≤ n, ∀ θ, ‖iteratedFDeriv ℝ l χlo θ‖ ≤ B)
    {η ϖ : ℝ} (hη : 0 < η) (hϖ : 0 < ϖ) (hϖη : ϖ ≤ Real.sqrt η)
    (π : ι → ℝ) (F : ∀ x, Vec 2 → h x)
    (hF : ∀ x, Continuous (F x) ∧ HasCompactSupport (F x))
    {α : ℕ × ℕ} (hα : α.1 + α.2 ≤ n) :
    ∃ P : Vec 2 → ℝ≥0∞, Measurable P ∧
      (∀ θ, ENNReal.ofReal (ϖ ^ (2 * (α.1 + α.2))) *
        blochFibreDerivNorm π (fun θ' => χlo ((Real.sqrt η)⁻¹ • θ')) α F θ ^ 2 ≤ P θ) ∧
      (∫⁻ θ in freqCube, P θ) ≤
        ENNReal.ofReal (blochMomentCoeff n (α.1 + α.2) B) * momentNorm π n ϖ F ^ 2 := by
  choose R hR0 hR using fun x => exists_support_radius (hF x).2
  let N x := ⌈R x + 1⌉₊
  let k := α.1 + α.2
  let C : ℝ≥0∞ := ENNReal.ofReal ((k + 1 : ℕ) * 2 ^ k : ℝ)
  let c (l : ℕ) : ℝ≥0∞ := ENNReal.ofReal ((k.choose l : ℝ) * B) ^ 2
  let H (x : ι) (l : ℕ) (idx : Fin (k - l) → Fin 2) (y : Vec 2) :=
    wordMonomial idx (ϖ • y) • F x y
  have hH x l (idx : Fin (k - l) → Fin 2) : Continuous (H x l idx) :=
    ((wordMonomial_contDiff idx).continuous.comp (continuous_const_smul ϖ)).smul (hF x).1
  have hQ x l (idx : Fin (k - l) → Fin 2) :
      Measurable fun θ => ∫⁻ z in AVenhance.unitCube,
        latticePair (latticeBox (N x)) (H x l idx) θ z :=
    (measurable_latticePair _ (hH x l idx)).lintegral_prod_right'
  let P θ := ∑ x, ENNReal.ofReal ((π x)⁻¹) *
    (C * ∑ l ∈ Finset.range (k + 1), ∑ idx : Fin (k - l) → Fin 2,
      c l * ∫⁻ z in AVenhance.unitCube, latticePair (latticeBox (N x)) (H x l idx) θ z)
  have hPm : Measurable P := by
    refine Finset.measurable_sum _ fun x _ => ?_
    apply Measurable.const_mul
    apply Measurable.const_mul
    refine Finset.measurable_sum _ fun l _ => ?_
    exact Finset.measurable_sum _ fun idx _ => (hQ x l idx).const_mul _
  refine ⟨P, hPm, fun θ => compact_bloch_fibre_sq_le hχ hB hη hϖ hϖη π F R N
    (fun x => (hF x).1) hR (fun x => Nat.le_ceil _) hα θ, ?_⟩
  dsimp only [P]
  rw [lintegral_weighted_sum (volume.restrict freqCube) _ _ _ _ _ hQ]
  calc
    ∑ x, ENNReal.ofReal ((π x)⁻¹) * (C * ∑ l ∈ Finset.range (k + 1),
        ∑ idx : Fin (k - l) → Fin 2, c l *
          ∫⁻ θ in freqCube, ∫⁻ z in AVenhance.unitCube,
            latticePair (latticeBox (N x)) (H x l idx) θ z)
      ≤ ∑ x, ENNReal.ofReal ((π x)⁻¹) * (C * ∑ l ∈ Finset.range (k + 1),
          ∑ idx : Fin (k - l) → Fin 2, c l *
            (ENNReal.ofReal ((2 * Real.pi) ^ 2) * eLpNorm (H x l idx) 2 volume ^ 2)) := by
        gcongr with x hx l hl idx
        exact lintegral_cube_cell_latticePair_le _ (hH x l idx)
    _ = C * ∑ l ∈ Finset.range (k + 1), ∑ idx : Fin (k - l) → Fin 2,
          (c l * ENNReal.ofReal ((2 * Real.pi) ^ 2)) *
            ∑ x, ENNReal.ofReal ((π x)⁻¹) * eLpNorm (H x l idx) 2 volume ^ 2 := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun idx _ => Finset.sum_congr rfl fun x _ => ?_
        ring
    _ ≤ C * ∑ l ∈ Finset.range (k + 1), ∑ _idx : Fin (k - l) → Fin 2,
          (c l * ENNReal.ofReal ((2 * Real.pi) ^ 2)) *
            (ENNReal.ofReal (n.factorial : ℝ) * momentNorm π n ϖ F) ^ 2 := by
        gcongr with l hl idx
        have hidx : idxCount idx ∈ momentIndices n := by
          have hs := idxCount_sum idx
          have hk : k - l ≤ n := (Nat.sub_le k l).trans hα
          simp only [momentIndices, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
          omega
        simpa only [H, wordMonomial_smul_eq] using
          sum_eLpNorm_sq_le_momentNorm π ϖ F hidx
    _ = ENNReal.ofReal (blochMomentCoeff n k B) * momentNorm π n ϖ F ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          nsmul_eq_mul, mul_pow]
        have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le n) 0)
        have hs : ENNReal.ofReal (∑ l ∈ Finset.range (k + 1),
            (2 : ℝ) ^ (k - l) * ((k.choose l : ℝ) * B) ^ 2) =
            ∑ l ∈ Finset.range (k + 1),
              ENNReal.ofReal ((2 : ℝ) ^ (k - l) * ((k.choose l : ℝ) * B) ^ 2) :=
          ENNReal.ofReal_sum_of_nonneg (by intros; positivity)
        have hc : ENNReal.ofReal (blochMomentCoeff n k B) =
            C * (∑ l ∈ Finset.range (k + 1), (2 : ℝ≥0∞) ^ (k - l) * c l) *
              ENNReal.ofReal ((2 * Real.pi) ^ 2) * ENNReal.ofReal (n.factorial : ℝ) ^ 2 := by
          unfold blochMomentCoeff
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul (by positivity), hs]
          simp (disch := positivity) only [C, c, ENNReal.ofReal_mul, ENNReal.ofReal_pow,
            ENNReal.ofReal_ofNat]
        rw [hc]
        simp only [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [Nat.cast_pow, Nat.cast_ofNat]
        dsimp only [c]
        ring_nf

end Family

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public section
open Equiv MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Analysis
namespace AVRegularity.CycleWords.Assembly

/-! # Full derivatives by sorted partials

The `θ`-partial `∂_0^a ∂_1^b` is the `(a+b)`-th derivative on the sorted basis tuple
(`thetaPartial_eq_sortedBasis`). A monotone basis tuple is sorted (`monotone_basis_eq_sorted`), so
by the symmetry of the derivatives of a `C^j` function every value on a basis tuple is a sorted
partial (`exists_thetaPartial_eq`), and `‖D^j f‖ ≤ 2^j ∑_a ‖∂_0^a ∂_1^{j-a} f‖`
(`norm_iteratedFDeriv_le_sum_thetaPartial`). -/

section Sorted

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The sorted basis tuple: `a` copies of `e₀`, then `e₁`. -/
def sortedBasis (j a : ℕ) : Fin j → Vec 2 := fun l => basisVec (if (l : ℕ) < a then 0 else 1)

theorem thetaPartial_eq_sortedBasis (a b : ℕ) (f : Vec 2 → F) (θ : Vec 2) :
    thetaPartial a b f θ = iteratedFDeriv ℝ (a + b) f θ (sortedBasis (a + b) a) := by
  unfold thetaPartial
  congr 1
  funext l
  refine Fin.addCases (fun i => ?_) (fun i => ?_) l
  · rw [Fin.append_left]
    simp [sortedBasis, i.2]
  · rw [Fin.append_right]
    simp [sortedBasis]

theorem iteratedFDeriv_sortedBasis {j : ℕ} (a b : ℕ) (hj : j = a + b) (f : Vec 2 → F)
    (θ : Vec 2) : iteratedFDeriv ℝ j f θ (sortedBasis j a) = thetaPartial a b f θ := by
  subst hj
  exact (thetaPartial_eq_sortedBasis a b f θ).symm

/-- A monotone basis tuple is sorted. -/
theorem monotone_basis_eq_sorted {j : ℕ} {g : Fin j → Fin 2} (hg : Monotone g) :
    (fun l => basisVec (g l)) =
      sortedBasis j (Finset.univ.filter fun l => g l = 0).card := by
  set Z := Finset.univ.filter fun l => g l = 0 with hZ
  have key : ∀ l, g l = 0 ↔ (l : ℕ) < Z.card := by
    intro l
    constructor
    · intro h0
      have hsub : Finset.Iic l ⊆ Z := fun l' hl' => by
        simp only [hZ, Finset.mem_filter, Finset.mem_univ, true_and]
        have := hg (Finset.mem_Iic.1 hl')
        rw [h0] at this
        exact Fin.le_zero_iff.1 this
      have := Finset.card_le_card hsub
      rw [Fin.card_Iic] at this
      omega
    · intro hlt
      by_contra h1
      have hsub : Z ⊆ Finset.Iio l := fun l' hl' => by
        simp only [hZ, Finset.mem_filter, Finset.mem_univ, true_and] at hl'
        rw [Finset.mem_Iio]
        by_contra hge
        have := hg (not_lt.1 hge)
        rw [hl'] at this
        exact h1 (Fin.le_zero_iff.1 this)
      have := Finset.card_le_card hsub
      rw [Fin.card_Iio] at this
      omega
  funext l
  simp only [sortedBasis]
  by_cases h0 : g l = 0
  · simp only [(key l).1 h0, ↓reduceIte, h0]
  · have hlt : ¬ (l : ℕ) < Z.card := fun h => h0 ((key l).2 h)
    have h1 : g l = 1 := by
      have := (g l).2
      ext
      have : (g l : ℕ) ≠ 0 := fun h' => h0 (Fin.ext h')
      omega
    simp only [hlt, ↓reduceIte, h1]

/-- **Every value on a basis tuple is a sorted partial.** -/
theorem exists_thetaPartial_eq {j : ℕ} {f : Vec 2 → F} (hf : ContDiff ℝ j f)
    (idx : Fin j → Fin 2) (θ : Vec 2) : ∃ a b : ℕ, a + b = j ∧
      iteratedFDeriv ℝ j f θ (fun l => basisVec (idx l)) = thetaPartial a b f θ := by
  set σ := Tuple.sort idx with hσ
  have hmono := Tuple.monotone_sort idx
  set a := (Finset.univ.filter fun l => (idx ∘ σ) l = 0).card with ha
  have hale : a ≤ j := (Finset.card_filter_le _ _).trans (by simp)
  obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le hale
  refine ⟨a, b, hb.symm, ?_⟩
  rw [← iteratedFDeriv_comp_perm_of_contDiff j hf θ (fun l => basisVec (idx l)) σ]
  have hc : (fun l => basisVec (idx l)) ∘ ⇑σ = fun l => basisVec ((idx ∘ σ) l) := rfl
  rw [hc, monotone_basis_eq_sorted hmono]
  exact iteratedFDeriv_sortedBasis a b hb f θ

/-- **The full derivative by the sorted partials.** -/
theorem norm_iteratedFDeriv_le_sum_thetaPartial {j : ℕ} {f : Vec 2 → F} (hf : ContDiff ℝ j f)
    (θ : Vec 2) :
    ‖iteratedFDeriv ℝ j f θ‖ ≤
      2 ^ j * ∑ a ∈ Finset.range (j + 1), ‖thetaPartial a (j - a) f θ‖ := by
  refine (norm_le_sum_basis _).trans ?_
  have hterm : ∀ idx : Fin j → Fin 2, ‖iteratedFDeriv ℝ j f θ (fun l => basisVec (idx l))‖ ≤
      ∑ a ∈ Finset.range (j + 1), ‖thetaPartial a (j - a) f θ‖ := by
    intro idx
    obtain ⟨a, b, hab, he⟩ := exists_thetaPartial_eq hf idx θ
    rw [he]
    have hb : b = j - a := by omega
    rw [hb]
    exact Finset.single_le_sum (f := fun a => ‖thetaPartial a (j - a) f θ‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
  refine (Finset.sum_le_sum fun idx _ => hterm idx).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    nsmul_eq_mul]
  push_cast
  ring

end Sorted

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords.Assembly

/-! # Abstract fibre word: stages and stage norms

The abstract fibre-word inequalities (AFW, the analysis of B1.S) work with a finite family of
cell curves indexed by `I`, grouped into stages by `st : I → ℕ`. A stage carries the `ℓ²` norm of
its slow coordinates (`stageNorm`) and a fast seminorm: the supremum of the paired family against
admissible test families of unit size (`fastRaw`). This module has the finite-dimensional
bookkeeping: Cauchy-Schwarz over a stage (`norm_sum_mul_le_stageNorm`), the dual description of
the stage norm (`exists_dual_stageNorm`), and the pairing bound by the fast seminorm
(`norm_sum_pair_le_fastRaw`). -/

variable {I : Type*} [Fintype I]

/-- The members of stage `k`. -/
def stageSet (st : I → ℕ) (k : ℕ) : Finset I := Finset.univ.filter fun i => st i = k

/-- The `ℓ²` norm of a family over stage `k`. -/
def stageNorm (st : I → ℕ) (k : ℕ) (x : I → ℂ) : ℝ :=
  Real.sqrt (∑ i ∈ stageSet st k, ‖x i‖ ^ 2)

theorem stageNorm_nonneg (st : I → ℕ) (k : ℕ) (x : I → ℂ) : 0 ≤ stageNorm st k x :=
  Real.sqrt_nonneg _

/-- Cauchy-Schwarz over a stage. -/
theorem norm_sum_mul_le_stageNorm (st : I → ℕ) (k : ℕ) (β x : I → ℂ) :
    ‖∑ i ∈ stageSet st k, β i * x i‖ ≤ stageNorm st k β * stageNorm st k x := by
  refine (norm_sum_le _ _).trans ?_
  have h := Finset.sum_mul_sq_le_sq_mul_sq (stageSet st k) (fun i => ‖β i‖) (fun i => ‖x i‖)
  have h0 : 0 ≤ ∑ i ∈ stageSet st k, ‖β i‖ * ‖x i‖ :=
    Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  simp only [norm_mul]
  unfold stageNorm
  rw [← Real.sqrt_mul (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  exact Real.le_sqrt_of_sq_le h

/-- The stage norm is attained by a dual family of norm at most one. -/
theorem exists_dual_stageNorm (st : I → ℕ) (k : ℕ) (x : I → ℂ) :
    ∃ β : I → ℂ, stageNorm st k β ≤ 1 ∧
      ((stageNorm st k x : ℝ) : ℂ) = ∑ i ∈ stageSet st k, β i * x i := by
  by_cases hx : stageNorm st k x = 0
  · refine ⟨0, by simp [stageNorm], ?_⟩
    simp [hx]
  · have hpos : 0 < stageNorm st k x := lt_of_le_of_ne (stageNorm_nonneg st k x) (Ne.symm hx)
    refine ⟨fun i => (starRingEnd ℂ) (x i) / (stageNorm st k x : ℂ), ?_, ?_⟩
    · have hsq : ∑ i ∈ stageSet st k,
          ‖(starRingEnd ℂ) (x i) / (stageNorm st k x : ℂ)‖ ^ 2 =
            (∑ i ∈ stageSet st k, ‖x i‖ ^ 2) / stageNorm st k x ^ 2 := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hpos, div_pow]
      have hx2 : stageNorm st k x ^ 2 = ∑ i ∈ stageSet st k, ‖x i‖ ^ 2 :=
        Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
      unfold stageNorm at hsq ⊢
      rw [hsq]
      unfold stageNorm at hx2
      rw [hx2, div_self (by rw [← hx2]; positivity)]
      simp
    · have hx2 : (stageNorm st k x : ℂ) ^ 2 = ∑ i ∈ stageSet st k, ((‖x i‖ ^ 2 : ℝ) : ℂ) := by
        rw [← Complex.ofReal_pow, ← Complex.ofReal_sum]
        congr 1
        exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
      have hne : (stageNorm st k x : ℂ) ≠ 0 := by exact_mod_cast hx
      have hterm : ∀ i, (starRingEnd ℂ) (x i) / (stageNorm st k x : ℂ) * x i =
          ((‖x i‖ ^ 2 : ℝ) : ℂ) / (stageNorm st k x : ℂ) := by
        intro i
        rw [div_mul_eq_mul_div, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      simp_rw [hterm]
      rw [← Finset.sum_div, ← hx2]
      field_simp

/-- The raw fast seminorm of stage `k` at time `r`: the supremum of the paired family against
admissible test families of `ν`-size at most one. -/
def fastRaw (st : I → ℕ) (k : ℕ) (W : I → ComplexCellL2) (Adm : ComplexCellL2 → Prop)
    (ν : ComplexCellL2 → ℝ) : ℝ :=
  sSup {y | ∃ ψ : I → ComplexCellL2, (∀ i ∈ stageSet st k, Adm (ψ i)) ∧
    Real.sqrt (∑ i ∈ stageSet st k, ν (ψ i) ^ 2) ≤ 1 ∧
    y = ‖∑ i ∈ stageSet st k, cellComplexPair (W i) (ψ i)‖}

/-- The pairing of a stage against an admissible family is at most the fast seminorm times the
`ν`-size of the family. The admissible class is a complex cone containing `0`, `ν` is
homogeneous and dominates the `L²` norm. -/
theorem norm_sum_pair_le_fastRaw (st : I → ℕ) (k : ℕ) (W : I → ComplexCellL2)
    (Adm : ComplexCellL2 → Prop) (ν : ComplexCellL2 → ℝ)
    (hAdm : ∀ (c : ℂ) ψ, Adm ψ → Adm (cellScalarCLM c ψ))
    (hν : ∀ (c : ℂ) ψ, ν (cellScalarCLM c ψ) = ‖c‖ * ν ψ)
    (hνL : ∀ ψ, Adm ψ → ‖ψ‖ ≤ ν ψ) (φ : I → ComplexCellL2) (hφ : ∀ i ∈ stageSet st k, Adm (φ i)) :
    ‖∑ i ∈ stageSet st k, cellComplexPair (W i) (φ i)‖ ≤
      fastRaw st k W Adm ν * Real.sqrt (∑ i ∈ stageSet st k, ν (φ i) ^ 2) := by
  set s := Real.sqrt (∑ i ∈ stageSet st k, ν (φ i) ^ 2) with hs
  have hbdd : BddAbove {y | ∃ ψ : I → ComplexCellL2, (∀ i ∈ stageSet st k, Adm (ψ i)) ∧
      Real.sqrt (∑ i ∈ stageSet st k, ν (ψ i) ^ 2) ≤ 1 ∧
      y = ‖∑ i ∈ stageSet st k, cellComplexPair (W i) (ψ i)‖} := by
    refine ⟨∑ i ∈ stageSet st k, ‖W i‖, ?_⟩
    rintro y ⟨ψ, hψ, hψ1, rfl⟩
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    have hν1 : ν (ψ i) ≤ 1 := by
      have h1 : ν (ψ i) ^ 2 ≤ ∑ j ∈ stageSet st k, ν (ψ j) ^ 2 :=
        Finset.single_le_sum (f := fun j => ν (ψ j) ^ 2) (fun j _ => sq_nonneg _) hi
      have h2 : Real.sqrt (ν (ψ i) ^ 2) ≤ 1 := (Real.sqrt_le_sqrt h1).trans hψ1
      rw [Real.sqrt_sq_eq_abs] at h2
      exact (le_abs_self _).trans h2
    have hpair : ‖cellComplexPair (W i) (ψ i)‖ ≤ ‖W i‖ * ‖ψ i‖ :=
      cellComplexPair_norm_le (W i) (ψ i)
    have hψn : ‖ψ i‖ ≤ 1 := (hνL _ (hψ i hi)).trans hν1
    calc ‖cellComplexPair (W i) (ψ i)‖ ≤ ‖W i‖ * ‖ψ i‖ := hpair
      _ ≤ ‖W i‖ * 1 := mul_le_mul_of_nonneg_left hψn (norm_nonneg _)
      _ = ‖W i‖ := mul_one _
  by_cases hs0 : s = 0
  · have hz : ∀ i ∈ stageSet st k, φ i = 0 := by
      intro i hi
      have h1 : ν (φ i) ^ 2 ≤ ∑ j ∈ stageSet st k, ν (φ j) ^ 2 :=
        Finset.single_le_sum (f := fun j => ν (φ j) ^ 2) (fun j _ => sq_nonneg _) hi
      have h2 : ∑ j ∈ stageSet st k, ν (φ j) ^ 2 = 0 := by
        rw [hs] at hs0
        exact (Real.sqrt_eq_zero (Finset.sum_nonneg fun j _ => sq_nonneg _)).1 hs0
      have h3 : ν (φ i) = 0 := by nlinarith [sq_nonneg (ν (φ i))]
      exact norm_le_zero_iff.1 ((hνL _ (hφ i hi)).trans h3.le)
    rw [Finset.sum_congr rfl fun i hi => by rw [hz i hi], hs0]
    simp [cellComplexPair_zero_right]
  · have hspos : 0 < s := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hs0)
    set ψ : I → ComplexCellL2 := fun i => cellScalarCLM ((s⁻¹ : ℝ) : ℂ) (φ i) with hψdef
    have hmem : ‖∑ i ∈ stageSet st k, cellComplexPair (W i) (ψ i)‖ ≤ fastRaw st k W Adm ν := by
      refine le_csSup hbdd ⟨ψ, fun i hi => hAdm _ _ (hφ i hi), ?_, rfl⟩
      have : ∑ i ∈ stageSet st k, ν (ψ i) ^ 2 = s⁻¹ ^ 2 * ∑ i ∈ stageSet st k, ν (φ i) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hψdef, hν, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hspos)]
        ring
      rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_pos.2 hspos).le, ← hs,
        inv_mul_cancel₀ hs0]
    have hscale : ∑ i ∈ stageSet st k, cellComplexPair (W i) (ψ i) =
        ((s⁻¹ : ℝ) : ℂ) * ∑ i ∈ stageSet st k, cellComplexPair (W i) (φ i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hψdef, cellComplexPair_scalar_right, Complex.star_def, Complex.conj_ofReal]
    rw [hscale, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hspos)]
      at hmem
    have := mul_le_mul_of_nonneg_left hmem hspos.le
    rwa [← mul_assoc, mul_inv_cancel₀ hs0, one_mul, mul_comm] at this

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! Summing the measurable lattice majorants gives the squared Bloch moment estimate. -/

def blochMomentTotal (n : ℕ) (B : ℝ) : ℝ :=
  ((momentIndices n).card : ℝ) *
    ∑ α ∈ momentIndices n, blochMomentCoeff n (α.1 + α.2) B

theorem blochMomentTotal_nonneg (n : ℕ) (B : ℝ) : 0 ≤ blochMomentTotal n B :=
  mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ => blochMomentCoeff_nonneg _ _ _)

section Family
variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)]

theorem lintegral_compact_bloch_sum_sq_le {n : ℕ} {χlo : Vec 2 → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χlo) {B : ℝ}
    (hB : ∀ l ≤ n, ∀ θ, ‖iteratedFDeriv ℝ l χlo θ‖ ≤ B)
    {η ϖ : ℝ} (hη : 0 < η) (hϖ : 0 < ϖ) (hϖη : ϖ ≤ Real.sqrt η)
    (π : ι → ℝ) (F : ∀ x, Vec 2 → h x)
    (hF : ∀ x, Continuous (F x) ∧ HasCompactSupport (F x)) :
    (∫⁻ θ in freqCube, (∑ α ∈ momentIndices n,
      ENNReal.ofReal (ϖ ^ (α.1 + α.2) / ((α.1.factorial * α.2.factorial : ℕ) : ℝ)) *
        blochFibreDerivNorm π (fun θ' => χlo ((Real.sqrt η)⁻¹ • θ')) α F θ) ^ 2) ≤
      ENNReal.ofReal (blochMomentTotal n B) * momentNorm π n ϖ F ^ 2 := by
  let S := momentIndices n
  have hα (a : ↥S) : a.val.1 + a.val.2 ≤ n := (Finset.mem_filter.1 a.property).2
  choose P hPm hPl hPi using fun a : ↥S =>
    compact_bloch_fibre_majorant hχ hB hη hϖ hϖη π F hF (hα a)
  let V (a : ℕ × ℕ) θ :=
    blochFibreDerivNorm π (fun θ' => χlo ((Real.sqrt η)⁻¹ • θ')) a F θ
  let w (a : ℕ × ℕ) :=
    ENNReal.ofReal (ϖ ^ (a.1 + a.2) / ((a.1.factorial * a.2.factorial : ℕ) : ℝ))
  have hw (a : ℕ × ℕ) : w a ^ 2 ≤ ENNReal.ofReal (ϖ ^ (2 * (a.1 + a.2))) := by
    have hf : (1 : ℝ) ≤ ((a.1.factorial * a.2.factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (mul_ne_zero (Nat.factorial_ne_zero _)
        (Nat.factorial_ne_zero _))
    calc w a ^ 2 ≤ ENNReal.ofReal (ϖ ^ (a.1 + a.2)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (ENNReal.ofReal_le_ofReal
            (div_le_self (pow_nonneg hϖ.le _) hf)) 2
      _ = _ := by
          rw [← ENNReal.ofReal_pow (pow_nonneg hϖ.le _), ← pow_mul]
          congr 2
          omega
  have hp θ : (∑ a ∈ S, w a * V a θ) ^ 2 ≤ (S.card : ℝ≥0∞) * ∑ a : ↥S, P a θ := by
    rw [← Finset.sum_coe_sort S]
    have hcs := ennreal_sum_mul_sq_le Finset.univ (fun _ : ↥S => 1)
      (fun a => w a.val * V a.val θ)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, Fintype.card_coe] at hcs
    refine hcs.trans (mul_le_mul_right (Finset.sum_le_sum fun a _ => ?_) _)
    rw [mul_pow]
    exact (mul_le_mul_left (hw a.val) _).trans (hPl a θ)
  have hm : Measurable fun θ => ∑ a : ↥S, P a θ :=
    Finset.measurable_sum _ fun a _ => hPm a
  calc
    (∫⁻ θ in freqCube, (∑ a ∈ S, w a * V a θ) ^ 2)
      ≤ ∫⁻ θ in freqCube, (S.card : ℝ≥0∞) * ∑ a : ↥S, P a θ := lintegral_mono hp
    _ = (S.card : ℝ≥0∞) * ∑ a : ↥S, ∫⁻ θ in freqCube, P a θ := by
        rw [lintegral_const_mul _ hm, lintegral_finsetSum _ fun a _ => hPm a]
    _ ≤ (S.card : ℝ≥0∞) * ∑ a : ↥S,
        ENNReal.ofReal (blochMomentCoeff n (a.val.1 + a.val.2) B) * momentNorm π n ϖ F ^ 2 :=
      mul_le_mul_right (Finset.sum_le_sum fun a _ => hPi a) _
    _ = ENNReal.ofReal (blochMomentTotal n B) * momentNorm π n ϖ F ^ 2 := by
        rw [← Finset.sum_mul]
        rw [Finset.sum_coe_sort S (fun a =>
          ENNReal.ofReal (blochMomentCoeff n (a.1 + a.2) B))]
        rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => blochMomentCoeff_nonneg n _ B)]
        unfold blochMomentTotal
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, mul_assoc]

end Family

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.CycleWords.Assembly

/-! # `C^m` limits of uniformly Cauchy sequences

A sequence of `C^m` functions whose derivatives of order `≤ m` are uniformly Cauchy has a `C^m`
limit, and the derivatives converge at every point (`exists_contDiff_limit`): along a fast
subsequence the differences telescope into a series with summable derivatives (`contDiff_tsum`).
-/

section Limit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **A uniformly Cauchy sequence in `C^m` has a `C^m` limit.** -/
theorem exists_contDiff_limit {m : ℕ} {A : ℕ → Vec 2 → E} (hA : ∀ k, ContDiff ℝ m (A k))
    (b : ℕ → ℕ → ℝ)
    (hcau : ∀ k l j θ, j ≤ m →
      ‖iteratedFDeriv ℝ j (A k) θ - iteratedFDeriv ℝ j (A l) θ‖ ≤ b k l)
    (hb : ∀ ε > 0, ∃ N, ∀ k ≥ N, ∀ l ≥ N, b k l < ε) :
    ∃ A₀ : Vec 2 → E, ContDiff ℝ m A₀ ∧ ∀ j ≤ m, ∀ θ,
      Tendsto (fun k => iteratedFDeriv ℝ j (A k) θ) atTop (𝓝 (iteratedFDeriv ℝ j A₀ θ)) := by
  -- a fast subsequence
  have hN0 : ∀ i : ℕ, ∃ N, ∀ k ≥ N, ∀ l ≥ N, b k l < (1 / 2 : ℝ) ^ i := fun i =>
    hb _ (by positivity)
  choose N hN using hN0
  set s : ℕ → ℕ := fun i => i + ∑ t ∈ Finset.range (i + 1), N t with hs
  have hsN : ∀ i, N i ≤ s i := fun i => by
    have := Finset.single_le_sum (f := N) (fun _ _ => Nat.zero_le _)
      (Finset.self_mem_range_succ i)
    simp only [hs]
    omega
  have hsmono : ∀ i, s i ≤ s (i + 1) := fun i => by
    simp only [hs, Finset.sum_range_succ (n := i + 1)]
    omega
  have hsi : ∀ i, i ≤ s i := fun i => Nat.le_add_right _ _
  -- the telescoping series
  set f : ℕ → Vec 2 → E := fun i θ => A (s (i + 1)) θ - A (s i) θ with hf
  have hfC : ∀ i, ContDiff ℝ (m : ℕ∞) (f i) := fun i => (hA _).sub (hA _)
  have hfD : ∀ (j : ℕ) i θ, j ≤ m → iteratedFDeriv ℝ j (f i) θ =
      iteratedFDeriv ℝ j (A (s (i + 1))) θ - iteratedFDeriv ℝ j (A (s i)) θ := fun j i θ hj =>
    iteratedFDeriv_sub_apply ((hA _).contDiffAt.of_le (by exact_mod_cast hj))
      ((hA _).contDiffAt.of_le (by exact_mod_cast hj))
  have hfb : ∀ (j : ℕ) i θ, (j : ℕ∞) ≤ m → ‖iteratedFDeriv ℝ j (f i) θ‖ ≤ (1 / 2 : ℝ) ^ i := by
    intro j i θ hj
    have hj' : j ≤ m := by exact_mod_cast hj
    rw [hfD j i θ hj']
    exact (hcau _ _ j θ hj').trans (hN i _ ((hsN i).trans (hsmono i)) _ (hsN i)).le
  have hv : ∀ j : ℕ, (j : ℕ∞) ≤ m → Summable fun i : ℕ => (1 / 2 : ℝ) ^ i := fun _ _ =>
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  set g : Vec 2 → E := fun θ => ∑' i, f i θ with hg
  have hgC : ContDiff ℝ (m : ℕ∞) g := contDiff_tsum hfC hv fun j i θ hj => hfb j i θ hj
  refine ⟨fun θ => A (s 0) θ + g θ, ((hA _).add hgC), fun j hj θ => ?_⟩
  have hD : iteratedFDeriv ℝ j (fun θ => A (s 0) θ + g θ) θ =
      iteratedFDeriv ℝ j (A (s 0)) θ + ∑' i, iteratedFDeriv ℝ j (f i) θ := by
    show iteratedFDeriv ℝ j (A (s 0) + g) θ = _
    rw [iteratedFDeriv_add_apply ((hA _).contDiffAt.of_le (by exact_mod_cast hj))
      ((hgC.contDiffAt).of_le (by exact_mod_cast hj)),
      iteratedFDeriv_tsum_apply hfC hv hfb (by exact_mod_cast hj)]
  -- the sequence is Cauchy at `θ`
  have hcs : CauchySeq fun k => iteratedFDeriv ℝ j (A k) θ := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨M, hM⟩ := hb ε hε
    exact ⟨M, fun k hk l hl => by
      rw [dist_eq_norm]
      exact (hcau k l j θ hj).trans_lt (hM k hk l hl)⟩
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcs
  -- along the subsequence the limit is the derivative of the sum
  have hsum : Summable fun i => iteratedFDeriv ℝ j (f i) θ :=
    Summable.of_norm_bounded (hv j (by exact_mod_cast hj)) fun i =>
      hfb j i θ (by exact_mod_cast hj)
  have htel : ∀ n, iteratedFDeriv ℝ j (A (s n)) θ =
      iteratedFDeriv ℝ j (A (s 0)) θ + ∑ i ∈ Finset.range n, iteratedFDeriv ℝ j (f i) θ := by
    intro n
    rw [Finset.sum_congr rfl fun i _ => hfD j i θ hj,
      Finset.sum_range_sub (fun i => iteratedFDeriv ℝ j (A (s i)) θ)]
    abel
  have hsub : Tendsto (fun n => iteratedFDeriv ℝ j (A (s n)) θ) atTop
      (𝓝 (iteratedFDeriv ℝ j (fun θ => A (s 0) θ + g θ) θ)) := by
    rw [hD, show (fun n => iteratedFDeriv ℝ j (A (s n)) θ) = fun n =>
      iteratedFDeriv ℝ j (A (s 0)) θ + ∑ i ∈ Finset.range n, iteratedFDeriv ℝ j (f i) θ from
        funext htel]
    exact tendsto_const_nhds.add hsum.hasSum.tendsto_sum_nat
  have hss : Tendsto s atTop atTop := tendsto_atTop_mono hsi tendsto_id
  rw [← tendsto_nhds_unique (hL.comp hss) hsub]
  exact hL

end Limit

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords.Assembly

/-! # Abstract fibre word: the slow inequality

Forward forced cell curves `W_i` (fibre coefficients `C`, sources `S_i`, fluxes `F_i`) and one
genuine adjoint curve `q` (the adjoint of the terminal test). The gauged slow coordinate of stage
`k` is `A_k(t) = ‖(⟨W_i(a+t), q(a+t)⟩)_{st i = k}‖ / |N₀|` (`slowStage`), `N₀` the conserved
pairing of the phased graph with `q`. F1 (`cellWeakAdjointPairing_forced`) transports every slow
coordinate exactly. The block splitting H3s of the tested sources into slow parts
(`|κ| ≤ Θζ²`) and admissible fast tests (`ν ≤ Θζ|N₀|Γ`, Γ the gauge `|e^{-Ξ}|`) then gives
`A_k(t) ≤ A_k(0) + ε_s t + Θ ∑_{k'<k} ∫_0^t (ζ² a_{k'} + ζ b_{k'})` for every pair of continuous
majorants of the earlier slow coordinates and fast seminorms (`afw_slow`), which is the slow
hypothesis of `triangularGronwall_majorant`. -/

variable {I : Type*} [Fintype I]

/-- The gauged slow coordinate of stage `k` at time `a + t`. -/
def slowStage (st : I → ℕ) (k : ℕ) (W : I → ℝ → ComplexCellL2) (q : ℝ → ComplexCellL2) (N₀ : ℂ)
    (a t : ℝ) : ℝ :=
  stageNorm st k (fun i => cellComplexPair (W i (a + t)) (q (a + t))) / ‖N₀‖

/-- The gauged fast seminorm of stage `k` at time `a + t`. -/
def fastStage (st : I → ℕ) (k : ℕ) (W : I → ℝ → ComplexCellL2)
    (Adm : ℕ → ℝ → ComplexCellL2 → Prop) (ν : ℕ → ℝ → ComplexCellL2 → ℝ) (Γ : ℝ → ℝ)
    (a t : ℝ) : ℝ :=
  Γ (a + t) * fastRaw st k (fun i => W i (a + t)) (Adm k (a + t)) (ν k (a + t))

theorem fastRaw_nonneg (st : I → ℕ) (k : ℕ) (W : I → ComplexCellL2) (Adm : ComplexCellL2 → Prop)
    (ν : ComplexCellL2 → ℝ) : 0 ≤ fastRaw st k W Adm ν :=
  Real.sSup_nonneg fun _ ⟨_, _, _, hy⟩ => hy ▸ norm_nonneg _

/-- The tested sources of one stage at one time, bounded through the block splitting. -/
theorem slow_source_le {st : I → ℕ} {k : ℕ} {W : I → ComplexCellL2} {q : ComplexCellL2}
    {Adm : ℕ → ComplexCellL2 → Prop} {ν : ℕ → ComplexCellL2 → ℝ}
    (hAdm : ∀ k' (c : ℂ) ψ, Adm k' ψ → Adm k' (cellScalarCLM c ψ))
    (hν : ∀ k' (c : ℂ) ψ, ν k' (cellScalarCLM c ψ) = ‖c‖ * ν k' ψ)
    (hνL : ∀ k' ψ, Adm k' ψ → ‖ψ‖ ≤ ν k' ψ)
    {N₀ : ℂ} {Γr Θ ζ εs : ℝ} (hΘ : 0 ≤ Θ) (hζ : 0 ≤ ζ) (hΓ : 0 ≤ Γr)
    (β κ : I → ℂ) (φ : I → ComplexCellL2) (hβ : stageNorm st k β ≤ 1) (src : ℂ)
    (hφ : ∀ k' < k, ∀ i' ∈ stageSet st k', Adm k' (φ i'))
    (hκ : ∀ k' < k, stageNorm st k' κ ≤ Θ * ζ ^ 2 * stageNorm st k β)
    (hφn : ∀ k' < k, Real.sqrt (∑ i' ∈ stageSet st k', ν k' (φ i') ^ 2) ≤
      Θ * ζ * (‖N₀‖ * Γr) * stageNorm st k β)
    (hsplit : ‖src - ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet st k',
      (κ i' * cellComplexPair (W i') q + cellComplexPair (W i') (φ i'))‖ ≤
        ‖N₀‖ * εs * stageNorm st k β) (hεs : 0 ≤ εs) :
    ‖src‖ ≤ ‖N₀‖ * εs + ∑ k' ∈ Finset.range k,
      (Θ * ζ ^ 2 * stageNorm st k' (fun i => cellComplexPair (W i) q) +
        Θ * ζ * (‖N₀‖ * Γr) * fastRaw st k' W (Adm k') (ν k')) := by
  have hβ0 := stageNorm_nonneg st k β
  have h1 : ‖src‖ ≤ ‖∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet st k',
      (κ i' * cellComplexPair (W i') q + cellComplexPair (W i') (φ i'))‖ + ‖N₀‖ * εs := by
    have h := norm_le_norm_add_norm_sub' src (∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet st k',
      (κ i' * cellComplexPair (W i') q + cellComplexPair (W i') (φ i')))
    have h2 : ‖N₀‖ * εs * stageNorm st k β ≤ ‖N₀‖ * εs :=
      mul_le_of_le_one_right (by positivity) hβ
    linarith
  refine h1.trans ?_
  rw [add_comm (‖N₀‖ * εs)]
  refine add_le_add ((norm_sum_le _ _).trans (Finset.sum_le_sum fun k' hk' => ?_)) le_rfl
  have hk'k : k' < k := Finset.mem_range.1 hk'
  rw [Finset.sum_add_distrib]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (norm_sum_mul_le_stageNorm st k' κ _).trans ?_
    have := hκ k' hk'k
    have h0 := stageNorm_nonneg st k' (fun i => cellComplexPair (W i) q)
    calc stageNorm st k' κ * stageNorm st k' (fun i => cellComplexPair (W i) q)
        ≤ (Θ * ζ ^ 2 * stageNorm st k β) * stageNorm st k' (fun i => cellComplexPair (W i) q) :=
          mul_le_mul_of_nonneg_right this h0
      _ ≤ (Θ * ζ ^ 2 * 1) * stageNorm st k' (fun i => cellComplexPair (W i) q) := by
          gcongr
      _ = _ := by ring
  · refine (norm_sum_pair_le_fastRaw st k' W (Adm k') (ν k') (hAdm k') (hν k') (hνL k') φ
      (hφ k' hk'k)).trans ?_
    have hf := fastRaw_nonneg st k' W (Adm k') (ν k')
    calc fastRaw st k' W (Adm k') (ν k') * Real.sqrt (∑ i' ∈ stageSet st k', ν k' (φ i') ^ 2)
        ≤ fastRaw st k' W (Adm k') (ν k') * (Θ * ζ * (‖N₀‖ * Γr) * stageNorm st k β) :=
          mul_le_mul_of_nonneg_left (hφn k' hk'k) hf
      _ ≤ fastRaw st k' W (Adm k') (ν k') * (Θ * ζ * (‖N₀‖ * Γr) * 1) := by
          gcongr
      _ = _ := by ring

/-- **AFW, the slow inequality.** -/
theorem afw_slow {a b : ℝ} (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : IsCellDrift C.v) (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (st : I → ℕ) (M : ℕ)
    (W : I → ℝ → ComplexCellL2) (Ws : I → ℝ → TorusHk 1 ℂ) (S : I → ℝ → ComplexCellL2)
    (F : I → ℝ → Fin 2 → ComplexCellL2)
    (hW : ∀ i, CellWeakHilbertCurve a b (W i) (Ws i) (fun t =>
      cellDualDerivative C hG V hv.1 hb t (Ws i t) (S i t) (F i t)))
    (q : ℝ → ComplexCellL2) (qs : ℝ → TorusHk 1 ℂ)
    (hq : CellWeakHilbertCurve a b q qs (fun t =>
      -cellDualDerivative (cellAdjointCoefficients C) hG V (cellDrift_neg hv).1
        (cellDrift_neg_bound hb) t (qs t) 0 0))
    (N₀ : ℂ) (hN₀ : N₀ ≠ 0) (Γ : ℝ → ℝ) (hΓ : ∀ r, 0 ≤ Γ r)
    (Adm : ℕ → ℝ → ComplexCellL2 → Prop) (ν : ℕ → ℝ → ComplexCellL2 → ℝ)
    (hAdm : ∀ k' r (c : ℂ) ψ, Adm k' r ψ → Adm k' r (cellScalarCLM c ψ))
    (hν : ∀ k' r (c : ℂ) ψ, ν k' r (cellScalarCLM c ψ) = ‖c‖ * ν k' r ψ)
    (hνL : ∀ k' r ψ, Adm k' r ψ → ‖ψ‖ ≤ ν k' r ψ)
    {Θ ζ : ℝ} {εs : ℕ → ℝ} (hΘ : 0 ≤ Θ) (hζ : 0 ≤ ζ) (hεs : ∀ k, 0 ≤ εs k)
    (H3s : ∀ r ∈ Icc a b, ∀ k < M, ∀ β : I → ℂ, ∃ κ : I → ℂ, ∃ φ : I → ComplexCellL2,
      (∀ k' < k, ∀ i' ∈ stageSet st k', Adm k' r (φ i')) ∧
      (∀ k' < k, stageNorm st k' κ ≤ Θ * ζ ^ 2 * stageNorm st k β) ∧
      (∀ k' < k, Real.sqrt (∑ i' ∈ stageSet st k', ν k' r (φ i') ^ 2) ≤
        Θ * ζ * (‖N₀‖ * Γ r) * stageNorm st k β) ∧
      ‖∑ i ∈ stageSet st k, β i * cellComplexSource C.θ (S i r) (F i r) (qs r) -
        ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet st k',
          (κ i' * cellComplexPair (W i' r) (q r) + cellComplexPair (W i' r) (φ i'))‖ ≤
        ‖N₀‖ * εs k * stageNorm st k β) :
    ∀ k < M, ∀ t ∈ Icc 0 (b - a), ∀ a' b' : ℕ → ℝ → ℝ,
      (∀ k' < k, Continuous (a' k') ∧ Continuous (b' k') ∧
        ∀ r ∈ Icc 0 t, slowStage st k' W q N₀ a r ≤ a' k' r ∧
          fastStage st k' W Adm ν Γ a r ≤ b' k' r) →
      slowStage st k W q N₀ a t ≤ slowStage st k W q N₀ a 0 + εs k * t +
        Θ * ∑ k' ∈ Finset.range k, ∫ r in (0 : ℝ)..t, (ζ ^ 2 * a' k' r + ζ * b' k' r) := by
  intro k hk t ht a' b' hmaj
  have hN : 0 < ‖N₀‖ := norm_pos_iff.2 hN₀
  have hsub : Icc a (a + t) ⊆ Icc a b := Icc_subset_Icc le_rfl (by linarith [ht.2])
  have hat : a ≤ a + t := by linarith [ht.1]
  -- the dual family of the stage norm at `a + t`
  set x : I → ℂ := fun i => cellComplexPair (W i (a + t)) (q (a + t)) with hx
  set x0 : I → ℂ := fun i => cellComplexPair (W i (a + 0)) (q (a + 0)) with hx0
  obtain ⟨β, hβ1, hβx⟩ := exists_dual_stageNorm st k x
  -- F1 for every member
  have hF1 : ∀ i, x i - x0 i = ∫ r in a..a + t,
      cellComplexSource C.θ (S i r) (F i r) (qs r) := by
    intro i
    have h := cellWeakAdjointPairing_forced hat C hG V hv hb ((hW i).mono hsub) (hq.mono hsub)
    simpa only [hx, hx0, add_zero] using h
  have hint : ∀ i, IntervalIntegrable (fun r => cellComplexSource C.θ (S i r) (F i r) (qs r))
      volume a (a + t) := fun i =>
    cellWeakAdjoint_forced_source_intervalIntegrable hat C hG V hv hb ((hW i).mono hsub)
      (hq.mono hsub)
  have hsum : ∑ i ∈ stageSet st k, β i * x i = ∑ i ∈ stageSet st k, β i * x0 i +
      ∫ r in a..a + t, ∑ i ∈ stageSet st k,
        β i * cellComplexSource C.θ (S i r) (F i r) (qs r) := by
    rw [intervalIntegral.integral_finsetSum fun i _ => (hint i).const_mul _,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_const_mul, ← hF1 i]
    ring
  -- the pointwise bound of the tested sources
  set g : ℝ → ℝ := fun r => εs k + Θ * ∑ k' ∈ Finset.range k, (ζ ^ 2 * a' k' r + ζ * b' k' r)
    with hgdef
  have hpt : ∀ r ∈ Icc a (a + t), ‖∑ i ∈ stageSet st k,
      β i * cellComplexSource C.θ (S i r) (F i r) (qs r)‖ ≤ ‖N₀‖ * g (r - a) := by
    intro r hr
    obtain ⟨κ, φ, hφ, hκ, hφn, hsplit⟩ := H3s r (hsub hr) k hk β
    have h := slow_source_le (W := fun i => W i r) (q := q r) (Adm := fun k' => Adm k' r)
      (ν := fun k' => ν k' r) (fun k' => hAdm k' r) (fun k' => hν k' r) (fun k' => hνL k' r)
      hΘ hζ (hΓ r) β κ φ hβ1 _ hφ hκ hφn hsplit
      (hεs k)
    refine h.trans ?_
    have hterm : ∀ k' ∈ Finset.range k,
        Θ * ζ ^ 2 * stageNorm st k' (fun i => cellComplexPair (W i r) (q r)) +
          Θ * ζ * (‖N₀‖ * Γ r) * fastRaw st k' (fun i => W i r) (Adm k' r) (ν k' r) ≤
        ‖N₀‖ * (Θ * (ζ ^ 2 * a' k' (r - a) + ζ * b' k' (r - a))) := by
      intro k' hk'
      have hk'k : k' < k := Finset.mem_range.1 hk'
      obtain ⟨_, _, hle⟩ := hmaj k' hk'k
      have hra : r - a ∈ Icc 0 t := ⟨by linarith [hr.1], by linarith [hr.2]⟩
      obtain ⟨hA', hB'⟩ := hle (r - a) hra
      have har : a + (r - a) = r := by ring
      rw [slowStage, har] at hA'
      rw [fastStage, har] at hB'
      have h1 : stageNorm st k' (fun i => cellComplexPair (W i r) (q r)) ≤
          ‖N₀‖ * a' k' (r - a) := by
        rwa [div_le_iff₀ hN, mul_comm] at hA'
      have hΘζ : 0 ≤ Θ * ζ ^ 2 := by positivity
      have hΘζ' : 0 ≤ Θ * ζ * ‖N₀‖ := by positivity
      calc Θ * ζ ^ 2 * stageNorm st k' (fun i => cellComplexPair (W i r) (q r)) +
            Θ * ζ * (‖N₀‖ * Γ r) * fastRaw st k' (fun i => W i r) (Adm k' r) (ν k' r)
          = Θ * ζ ^ 2 * stageNorm st k' (fun i => cellComplexPair (W i r) (q r)) +
            Θ * ζ * ‖N₀‖ * (Γ r * fastRaw st k' (fun i => W i r) (Adm k' r) (ν k' r)) := by ring
        _ ≤ Θ * ζ ^ 2 * (‖N₀‖ * a' k' (r - a)) + Θ * ζ * ‖N₀‖ * b' k' (r - a) :=
            add_le_add (mul_le_mul_of_nonneg_left h1 hΘζ) (mul_le_mul_of_nonneg_left hB' hΘζ')
        _ = _ := by ring
    calc ‖N₀‖ * εs k + ∑ k' ∈ Finset.range k,
          (Θ * ζ ^ 2 * stageNorm st k' (fun i => cellComplexPair (W i r) (q r)) +
            Θ * ζ * (‖N₀‖ * Γ r) * fastRaw st k' (fun i => W i r) (Adm k' r) (ν k' r))
        ≤ ‖N₀‖ * εs k + ∑ k' ∈ Finset.range k,
            ‖N₀‖ * (Θ * (ζ ^ 2 * a' k' (r - a) + ζ * b' k' (r - a))) :=
          add_le_add le_rfl (Finset.sum_le_sum hterm)
      _ = ‖N₀‖ * g (r - a) := by
          rw [hgdef, ← Finset.mul_sum, ← Finset.mul_sum]
          ring
  -- integrate
  have hgc : Continuous g := by
    rw [hgdef]
    refine continuous_const.add (continuous_const.mul (continuous_finsetSum _ fun k' hk' => ?_))
    obtain ⟨hac, hbc, _⟩ := hmaj k' (Finset.mem_range.1 hk')
    exact (continuous_const.mul hac).add (continuous_const.mul hbc)
  have hsrcint : IntervalIntegrable (fun r => ∑ i ∈ stageSet st k,
      β i * cellComplexSource C.θ (S i r) (F i r) (qs r)) volume a (a + t) := by
    have := IntervalIntegrable.sum (stageSet st k) (fun i _ => (hint i).const_mul (β i))
    convert this using 1
    funext r
    simp only [Finset.sum_apply]
  have hI : ∫ r in a..a + t, ‖∑ i ∈ stageSet st k,
      β i * cellComplexSource C.θ (S i r) (F i r) (qs r)‖ ≤ ‖N₀‖ * ∫ r in (0 : ℝ)..t, g r := by
    have hmc : Continuous fun r => ‖N₀‖ * g (r - a) :=
      continuous_const.mul (hgc.comp (continuous_sub_right a))
    have h := intervalIntegral.integral_mono_on (g := fun r => ‖N₀‖ * g (r - a)) hat
      hsrcint.norm (hmc.intervalIntegrable _ _) hpt
    refine h.trans (le_of_eq ?_)
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_right
      (fun r => g r) a]
    simp
  have hgint : ∫ r in (0 : ℝ)..t, g r = εs k * t + Θ * ∑ k' ∈ Finset.range k,
      ∫ r in (0 : ℝ)..t, (ζ ^ 2 * a' k' r + ζ * b' k' r) := by
    have hc : ∀ k' ∈ Finset.range k,
        IntervalIntegrable (fun r => ζ ^ 2 * a' k' r + ζ * b' k' r) volume 0 t := fun k' hk' => by
      obtain ⟨hac, hbc, _⟩ := hmaj k' (Finset.mem_range.1 hk')
      exact ((continuous_const.mul hac).add (continuous_const.mul hbc)).intervalIntegrable _ _
    rw [hgdef, intervalIntegral.integral_add intervalIntegrable_const
      ((IntervalIntegrable.sum (Finset.range k) hc).const_mul Θ |>.congr (by
        intro r _; simp [Finset.sum_apply])),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum hc]
    simp [smul_eq_mul, mul_comm]
  -- conclude
  have hmain : stageNorm st k x ≤ stageNorm st k x0 + ‖N₀‖ * ∫ r in (0 : ℝ)..t, g r := by
    have h1 : stageNorm st k x = ‖∑ i ∈ stageSet st k, β i * x i‖ := by
      rw [← hβx, Complex.norm_real, Real.norm_of_nonneg (stageNorm_nonneg _ _ _)]
    rw [h1, hsum]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · refine (norm_sum_mul_le_stageNorm st k β x0).trans ?_
      have := stageNorm_nonneg st k x0
      nlinarith
    · exact (intervalIntegral.norm_integral_le_integral_norm hat).trans hI
  have hfin : stageNorm st k x / ‖N₀‖ ≤ stageNorm st k x0 / ‖N₀‖ + ∫ r in (0 : ℝ)..t, g r := by
    rw [div_le_iff₀ hN]
    calc stageNorm st k x ≤ stageNorm st k x0 + ‖N₀‖ * ∫ r in (0 : ℝ)..t, g r := hmain
      _ = (stageNorm st k x0 / ‖N₀‖ + ∫ r in (0 : ℝ)..t, g r) * ‖N₀‖ := by
          field_simp
  show stageNorm st k x / ‖N₀‖ ≤ stageNorm st k x0 / ‖N₀‖ + εs k * t +
    Θ * ∑ k' ∈ Finset.range k, ∫ r in (0 : ℝ)..t, (ζ ^ 2 * a' k' r + ζ * b' k' r)
  rw [hgint] at hfin
  exact hfin.trans_eq (by ring)

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! # Limits of amplitude pairs in the amplitude jet norm

The amplitude jet norm bounds every `θ`-partial of order `≤ m` (`ofReal_norm_thetaPartial_le`) and,
by the symmetry of derivatives, every full derivative of a `C^m` amplitude
(`ofReal_norm_iteratedFDeriv_le`). A sequence of `C^m` amplitude pairs that is uniformly Cauchy in
the amplitude jet norm has a `C^m` limit with pointwise convergent derivatives
(`exists_amplitude_limit`), and the amplitude jet norm passes to the limit
(`tendsto_amplitudeJetNorm`). -/

section Amp

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- The weight of the `β`-partial in the amplitude jet norm, inverted. -/
noncomputable def partialConst (ϖ : ℝ) (β : ℕ × ℕ) (p : ℝ) : ℝ :=
  ((β.1.factorial * β.2.factorial : ℕ) : ℝ) / ϖ ^ (β.1 + β.2) * Real.sqrt p

theorem partialConst_nonneg {ϖ : ℝ} (hϖ : 0 < ϖ) (β : ℕ × ℕ) (p : ℝ) : 0 ≤ partialConst ϖ β p := by
  unfold partialConst
  positivity

/-- **The amplitude jet norm bounds the `θ`-partials.** -/
theorem ofReal_norm_thetaPartial_le (π : ι → ℝ) (hπ : ∀ x, 0 < π x) {m : ℕ} {ϖ : ℝ}
    (hϖ : 0 < ϖ) (A B : ∀ x, Vec 2 → h x) (θ : Vec 2) {β : ℕ × ℕ} (hβ : β ∈ momentIndices m)
    (x : ι) :
    ENNReal.ofReal ‖thetaPartial β.1 β.2 (A x) θ‖ ≤
        ENNReal.ofReal (partialConst ϖ β (π x)) * amplitudeJetNorm π m ϖ A B θ ∧
      ENNReal.ofReal ‖thetaPartial β.1 β.2 (B x) θ‖ ≤
        ENNReal.ofReal (partialConst ϖ β (π x)) * amplitudeJetNorm π m ϖ A B θ := by
  set T : ℝ≥0∞ := ∑ y, ENNReal.ofReal ((π y)⁻¹) *
    (ENNReal.ofReal (‖thetaPartial β.1 β.2 (A y) θ‖ ^ 2) +
      ENNReal.ofReal (‖thetaPartial β.1 β.2 (B y) θ‖ ^ 2)) with hT
  have hterm : ENNReal.ofReal (ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) *
      T ^ (1 / 2 : ℝ) ≤ amplitudeJetNorm π m ϖ A B θ :=
    Finset.single_le_sum (f := fun β : ℕ × ℕ =>
      ENNReal.ofReal (ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) *
        (∑ y, ENNReal.ofReal ((π y)⁻¹) *
          (ENNReal.ofReal (‖thetaPartial β.1 β.2 (A y) θ‖ ^ 2) +
            ENNReal.ofReal (‖thetaPartial β.1 β.2 (B y) θ‖ ^ 2))) ^ (1 / 2 : ℝ))
      (fun _ _ => zero_le) hβ
  have hx : ENNReal.ofReal ((π x)⁻¹) * (ENNReal.ofReal (‖thetaPartial β.1 β.2 (A x) θ‖ ^ 2) +
      ENNReal.ofReal (‖thetaPartial β.1 β.2 (B x) θ‖ ^ 2)) ≤ T :=
    Finset.single_le_sum (f := fun y => ENNReal.ofReal ((π y)⁻¹) *
      (ENNReal.ofReal (‖thetaPartial β.1 β.2 (A y) θ‖ ^ 2) +
        ENNReal.ofReal (‖thetaPartial β.1 β.2 (B y) θ‖ ^ 2))) (fun _ _ => zero_le)
      (Finset.mem_univ x)
  have hfac : (0 : ℝ) < ((β.1.factorial * β.2.factorial : ℕ) : ℝ) := by positivity
  have hpx := hπ x
  -- one value
  have key : ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal ((π x)⁻¹) * ENNReal.ofReal (t ^ 2) ≤ T →
      ENNReal.ofReal t ≤ ENNReal.ofReal (partialConst ϖ β (π x)) *
        amplitudeJetNorm π m ϖ A B θ := by
    intro t ht hle
    have hs : ENNReal.ofReal (Real.sqrt (π x)⁻¹ * t) ≤ T ^ (1 / 2 : ℝ) := by
      have heq : ENNReal.ofReal (Real.sqrt (π x)⁻¹ * t) =
          (ENNReal.ofReal ((π x)⁻¹) * ENNReal.ofReal (t ^ 2)) ^ (1 / 2 : ℝ) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hpx.le),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
          Real.sqrt_mul (inv_nonneg.2 hpx.le), Real.sqrt_sq ht, Real.sqrt_inv]
      rw [heq]
      exact ENNReal.rpow_le_rpow hle (by norm_num)
    calc ENNReal.ofReal t = ENNReal.ofReal (partialConst ϖ β (π x)) *
          (ENNReal.ofReal (ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) *
            ENNReal.ofReal (Real.sqrt (π x)⁻¹ * t)) := by
          rw [← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul (partialConst_nonneg hϖ β _)]
          congr 1
          have h1 : Real.sqrt (π x) * Real.sqrt (π x)⁻¹ = 1 := by
            rw [← Real.sqrt_mul hpx.le, mul_inv_cancel₀ hpx.ne', Real.sqrt_one]
          have h2 : ((β.1.factorial * β.2.factorial : ℕ) : ℝ) / ϖ ^ (β.1 + β.2) *
              (ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) = 1 := by
            field_simp
          symm
          calc partialConst ϖ β (π x) *
                (ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ) *
                  (Real.sqrt (π x)⁻¹ * t))
              = (((β.1.factorial * β.2.factorial : ℕ) : ℝ) / ϖ ^ (β.1 + β.2) *
                  (ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ))) *
                  (Real.sqrt (π x) * Real.sqrt (π x)⁻¹) * t := by
                unfold partialConst
                ring
            _ = t := by rw [h1, h2, one_mul, one_mul]
      _ ≤ ENNReal.ofReal (partialConst ϖ β (π x)) * amplitudeJetNorm π m ϖ A B θ :=
          mul_le_mul' le_rfl ((mul_le_mul' le_rfl hs).trans hterm)
  refine ⟨key _ (norm_nonneg _) ((mul_le_mul' le_rfl le_self_add).trans hx),
    key _ (norm_nonneg _) ((mul_le_mul' le_rfl le_add_self).trans hx)⟩

/-- The constant of the full derivatives of order `j`. -/
noncomputable def derivConst (ϖ : ℝ) (j : ℕ) (p : ℝ) : ℝ :=
  2 ^ j * ∑ a ∈ Finset.range (j + 1), partialConst ϖ (a, j - a) p

theorem derivConst_nonneg {ϖ : ℝ} (hϖ : 0 < ϖ) (j : ℕ) (p : ℝ) : 0 ≤ derivConst ϖ j p := by
  unfold derivConst
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun a _ => partialConst_nonneg hϖ _ _)

/-- **The amplitude jet norm bounds the full derivatives** of a `C^m` amplitude. -/
theorem ofReal_norm_iteratedFDeriv_le (π : ι → ℝ) (hπ : ∀ x, 0 < π x) {m : ℕ} {ϖ : ℝ}
    (hϖ : 0 < ϖ) (A B : ∀ x, Vec 2 → h x) (θ : Vec 2) (x : ι) {j : ℕ} (hj : j ≤ m)
    (hA : ContDiff ℝ j (A x)) (hB : ContDiff ℝ j (B x)) :
    ENNReal.ofReal ‖iteratedFDeriv ℝ j (A x) θ‖ ≤
        ENNReal.ofReal (derivConst ϖ j (π x)) * amplitudeJetNorm π m ϖ A B θ ∧
      ENNReal.ofReal ‖iteratedFDeriv ℝ j (B x) θ‖ ≤
        ENNReal.ofReal (derivConst ϖ j (π x)) * amplitudeJetNorm π m ϖ A B θ := by
  have hmem : ∀ a ∈ Finset.range (j + 1), (a, j - a) ∈ momentIndices m := fun a ha => by
    have := Finset.mem_range.1 ha
    simp only [momentIndices, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega
  have hsum : ∀ X : Vec 2 → h x, ContDiff ℝ j X →
      (∀ a ∈ Finset.range (j + 1), ENNReal.ofReal ‖thetaPartial a (j - a) X θ‖ ≤
        ENNReal.ofReal (partialConst ϖ (a, j - a) (π x)) * amplitudeJetNorm π m ϖ A B θ) →
      ENNReal.ofReal ‖iteratedFDeriv ℝ j X θ‖ ≤
        ENNReal.ofReal (derivConst ϖ j (π x)) * amplitudeJetNorm π m ϖ A B θ := by
    intro X hX hpart
    refine (ENNReal.ofReal_le_ofReal (norm_iteratedFDeriv_le_sum_thetaPartial hX θ)).trans ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg fun _ _ => norm_nonneg _,
      derivConst, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_sum_of_nonneg fun a _ => partialConst_nonneg hϖ _ _, mul_assoc,
      Finset.sum_mul]
    exact mul_le_mul' le_rfl (Finset.sum_le_sum hpart)
  exact ⟨hsum _ hA fun a ha => (ofReal_norm_thetaPartial_le π hπ hϖ A B θ (hmem a ha) x).1,
    hsum _ hB fun a ha => (ofReal_norm_thetaPartial_le π hπ hϖ A B θ (hmem a ha) x).2⟩

/-- **The amplitude jet norm passes to the limit** under pointwise convergence of the derivatives.
-/
theorem tendsto_amplitudeJetNorm (π : ι → ℝ) (m : ℕ) (ϖ : ℝ) {A B : ℕ → ∀ x, Vec 2 → h x}
    {A₀ B₀ : ∀ x, Vec 2 → h x} (θ : Vec 2)
    (hA : ∀ x, ∀ j ≤ m, Tendsto (fun k => iteratedFDeriv ℝ j (A k x) θ) atTop
      (𝓝 (iteratedFDeriv ℝ j (A₀ x) θ)))
    (hB : ∀ x, ∀ j ≤ m, Tendsto (fun k => iteratedFDeriv ℝ j (B k x) θ) atTop
      (𝓝 (iteratedFDeriv ℝ j (B₀ x) θ))) :
    Tendsto (fun k => amplitudeJetNorm π m ϖ (A k) (B k) θ) atTop
      (𝓝 (amplitudeJetNorm π m ϖ A₀ B₀ θ)) := by
  have htp : ∀ (X : ℕ → ∀ x, Vec 2 → h x) (X₀ : ∀ x, Vec 2 → h x),
      (∀ x, ∀ j ≤ m, Tendsto (fun k => iteratedFDeriv ℝ j (X k x) θ) atTop
        (𝓝 (iteratedFDeriv ℝ j (X₀ x) θ))) →
      ∀ β ∈ momentIndices m, ∀ x, Tendsto (fun k => thetaPartial β.1 β.2 (X k x) θ) atTop
        (𝓝 (thetaPartial β.1 β.2 (X₀ x) θ)) := by
    intro X X₀ hX β hβ x
    have hβm : β.1 + β.2 ≤ m := (Finset.mem_filter.1 hβ).2
    exact ((continuous_eval_const _).tendsto _).comp (hX x _ hβm)
  unfold amplitudeJetNorm
  refine tendsto_finsetSum _ fun β hβ =>
    ENNReal.Tendsto.const_mul ?_ (Or.inr ENNReal.ofReal_ne_top)
  refine ((ENNReal.continuous_rpow_const).tendsto _).comp ?_
  refine tendsto_finsetSum _ fun x _ =>
    ENNReal.Tendsto.const_mul ?_ (Or.inr ENNReal.ofReal_ne_top)
  exact (ENNReal.tendsto_ofReal ((htp A A₀ hA β hβ x).norm.pow 2)).add
    (ENNReal.tendsto_ofReal ((htp B B₀ hB β hβ x).norm.pow 2))

variable [∀ i, CompleteSpace (h i)]

/-- **Limits of amplitude pairs** uniformly Cauchy in the amplitude jet norm. -/
theorem exists_amplitude_limit (π : ι → ℝ) (hπ : ∀ x, 0 < π x) (m : ℕ) {ϖ : ℝ} (hϖ : 0 < ϖ)
    {A B : ℕ → ∀ x, Vec 2 → h x} (hA : ∀ k x, ContDiff ℝ m (A k x))
    (hB : ∀ k x, ContDiff ℝ m (B k x)) (c : ℕ → ℕ → ℝ)
    (hc : ∀ k l θ, amplitudeJetNorm π m ϖ (fun x => A k x - A l x) (fun x => B k x - B l x) θ ≤
      ENNReal.ofReal (c k l))
    (hcN : ∀ ε > 0, ∃ N, ∀ k ≥ N, ∀ l ≥ N, c k l < ε) :
    ∃ A₀ B₀ : ∀ x, Vec 2 → h x, (∀ x, ContDiff ℝ m (A₀ x) ∧ ContDiff ℝ m (B₀ x)) ∧
      ∀ x, ∀ j ≤ m, ∀ θ,
        Tendsto (fun k => iteratedFDeriv ℝ j (A k x) θ) atTop
          (𝓝 (iteratedFDeriv ℝ j (A₀ x) θ)) ∧
        Tendsto (fun k => iteratedFDeriv ℝ j (B k x) θ) atTop
          (𝓝 (iteratedFDeriv ℝ j (B₀ x) θ)) := by
  -- the uniform Cauchy bound of the derivatives, componentwise
  have hcomp : ∀ x, ∀ X : ℕ → ∀ x, Vec 2 → h x, (∀ k x, ContDiff ℝ m (X k x)) →
      (∀ k l j θ, j ≤ m → ENNReal.ofReal ‖iteratedFDeriv ℝ j (fun z => X k x z - X l x z) θ‖ ≤
        ENNReal.ofReal (derivConst ϖ j (π x)) * ENNReal.ofReal (c k l)) →
      ∃ X₀ : Vec 2 → h x, ContDiff ℝ m X₀ ∧ ∀ j ≤ m, ∀ θ,
        Tendsto (fun k => iteratedFDeriv ℝ j (X k x) θ) atTop (𝓝 (iteratedFDeriv ℝ j X₀ θ)) := by
    intro x X hX hbd
    set K : ℝ := ∑ j ∈ Finset.range (m + 1), derivConst ϖ j (π x) with hK
    have hK0 : ∀ j ≤ m, derivConst ϖ j (π x) ≤ K := fun j hj =>
      Finset.single_le_sum (f := fun j => derivConst ϖ j (π x))
        (fun j _ => derivConst_nonneg hϖ j _) (Finset.mem_range.2 (Nat.lt_succ_of_le hj))
    have hKnn : 0 ≤ K := Finset.sum_nonneg fun j _ => derivConst_nonneg hϖ j _
    refine exists_contDiff_limit (fun k => hX k x) (fun k l => K * max (c k l) 0)
      (fun k l j θ hj => ?_) (fun ε hε => ?_)
    · rw [← iteratedFDeriv_sub_apply ((hX k x).contDiffAt.of_le (by exact_mod_cast hj))
        ((hX l x).contDiffAt.of_le (by exact_mod_cast hj))]
      have h2 : ENNReal.ofReal ‖iteratedFDeriv ℝ j (fun z => X k x z - X l x z) θ‖ ≤
          ENNReal.ofReal (K * max (c k l) 0) := by
        refine (hbd k l j θ hj).trans ?_
        rw [← ENNReal.ofReal_mul (derivConst_nonneg hϖ j _)]
        exact ENNReal.ofReal_le_ofReal
          ((mul_le_mul_of_nonneg_left (le_max_left _ _) (derivConst_nonneg hϖ j _)).trans
            (mul_le_mul_of_nonneg_right (hK0 j hj) (le_max_right _ _)))
      exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hKnn (le_max_right _ _))).1 h2
    · obtain ⟨N, hN⟩ := hcN (ε / (K + 1)) (by positivity)
      refine ⟨N, fun k hk l hl => ?_⟩
      have hm : max (c k l) 0 < ε / (K + 1) := max_lt (hN k hk l hl) (by positivity)
      calc K * max (c k l) 0 ≤ K * (ε / (K + 1)) := mul_le_mul_of_nonneg_left hm.le hKnn
        _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith
  have hbdA : ∀ x, ∀ k l j θ, j ≤ m →
      ENNReal.ofReal ‖iteratedFDeriv ℝ j (fun z => A k x z - A l x z) θ‖ ≤
        ENNReal.ofReal (derivConst ϖ j (π x)) * ENNReal.ofReal (c k l) := fun x k l j θ hj =>
    (ofReal_norm_iteratedFDeriv_le π hπ hϖ (fun x => A k x - A l x) (fun x => B k x - B l x) θ x
      hj (((hA k x).sub (hA l x)).of_le (by exact_mod_cast hj))
      (((hB k x).sub (hB l x)).of_le (by exact_mod_cast hj))).1.trans
      (mul_le_mul' le_rfl (hc k l θ))
  have hbdB : ∀ x, ∀ k l j θ, j ≤ m →
      ENNReal.ofReal ‖iteratedFDeriv ℝ j (fun z => B k x z - B l x z) θ‖ ≤
        ENNReal.ofReal (derivConst ϖ j (π x)) * ENNReal.ofReal (c k l) := fun x k l j θ hj =>
    (ofReal_norm_iteratedFDeriv_le π hπ hϖ (fun x => A k x - A l x) (fun x => B k x - B l x) θ x
      hj (((hA k x).sub (hA l x)).of_le (by exact_mod_cast hj))
      (((hB k x).sub (hB l x)).of_le (by exact_mod_cast hj))).2.trans
      (mul_le_mul' le_rfl (hc k l θ))
  have hAx := fun x => hcomp x A hA (hbdA x)
  have hBx := fun x => hcomp x B hB (hbdB x)
  choose A₀ hA₀ using hAx
  choose B₀ hB₀ using hBx
  exact ⟨A₀, B₀, fun x => ⟨(hA₀ x).1, (hB₀ x).1⟩,
    fun x j hj θ => ⟨(hA₀ x).2 j hj θ, (hB₀ x).2 j hj θ⟩⟩

end Amp

end AVRegularity.CycleWords.Assembly
end
end
