-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.Seam.OldScalar.Bessel
import AVRegularity.CycleWords.MixedWords.AdjointExists
import AVRegularity.CycleWords.MixedWords.StageExpansionLetter
import AVRegularity.CycleWords.MixedWords.Discard.BandCoeff
public import AVRegularity.CycleWords.MixedWords.Discard.Combine
import AVRegularity.CycleComparison.Lift.LeftTermsBlockCoefficientBox
import AVRegularity.CycleWords.MixedWords.B1WRepresentation
import AVRegularity.CycleWords.MixedWords.B1WWeightedNormFacts
public import AVRegularity.CycleWords.Seam.FamilyNorm
import AVRegularity.CycleEvolution.CellEnergySpaceRawDirectionalLimit
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

section
section
/-! # the datum (`StageDatumStatement`)

The level-0 stage values at the start are the Bloch parts of the moments of the datum. For one
component and one moment, the sum over an orthonormal basis of the squared cell norms of the
Bloch part is the finite lattice pair `latticePair`, whose integral over the zone is bounded by
`(2π)²` times the squared `L²` norm (`lintegral_cube_cell_latticePair_le_sm`). -/

@[expose] public section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CycleWords.Assembly
open scoped ENNReal

namespace AVRegularity.CycleWords.Discard.BandDatum

universe u v

/-- The cell integral of the squared Bloch parts of the moment `α` of a datum, summed over an
orthonormal basis. -/
noncomputable def datumCellSq {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (g : Vec 2 → E) (α : ℕ × ℕ) (θ : Vec 2) :
    ℝ≥0∞ :=
  ∑ e, ∫⁻ z in AVenhance.unitCube,
    ENNReal.ofReal (‖planeBlochC θ (fun y => momentWeight α y * inner ℝ (b e) (g y)) z‖ ^ 2)

theorem datumCellSq_eq_latticePair {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) {g : Vec 2 → E} (hgm : StronglyMeasurable g)
    (hgc : HasCompactSupport g) (α : ℕ × ℕ) :
    ∃ K : Finset (Fin 2 → ℤ), ∀ θ, datumCellSq b g α θ =
      ∫⁻ z in AVenhance.unitCube,
        latticePair K (fun y => momentWeight α y • g y) θ z := by
  obtain ⟨R, -, hR⟩ := exists_support_radius hgc
  set N : ℕ := ⌈R⌉₊ + 1 with hNdef
  have hN : R + 1 ≤ N := by
    rw [hNdef]; push_cast; linarith [Nat.le_ceil R]
  refine ⟨latticeBox N, fun θ => ?_⟩
  unfold datumCellSq
  have hmeas : ∀ e, Measurable fun z => ENNReal.ofReal
      (‖planeBlochC θ (fun y => momentWeight α y * inner ℝ (b e) (g y)) z‖ ^ 2) := by
    intro e
    have hc : Measurable fun y => momentWeight α y * inner ℝ (b e) (g y) := by
      unfold momentWeight
      exact (by fun_prop : Measurable fun y : Vec 2 => y 0 ^ α.1 * y 1 ^ α.2).mul
        ((continuous_const.inner continuous_id).comp_stronglyMeasurable hgm).measurable
    exact ENNReal.measurable_ofReal.comp ((measurable_planeBlochC θ hc).norm.pow_const 2)
  rw [← lintegral_finsetSum _ fun e _ => hmeas e]
  refine setLIntegral_congr_fun measurableSet_cellCube fun z hz => ?_
  set y : (Fin 2 → ℤ) → Vec 2 := fun k => z + fun i => (k i : ℝ) with hy
  set t : (Fin 2 → ℤ) → ℝ := fun k => vecDot θ (y k) with ht
  set w : (Fin 2 → ℤ) → E := fun k => momentWeight α (y k) • g (y k) with hw
  have hL : ∀ e, ‖planeBlochC θ (fun y => momentWeight α y * inner ℝ (b e) (g y)) z‖ ^ 2 =
      (∑ k ∈ latticeBox N, Real.cos (t k) * inner ℝ (b e) (w k)) ^ 2 +
        (∑ k ∈ latticeBox N, Real.sin (t k) * inner ℝ (b e) (w k)) ^ 2 := by
    intro e
    rw [planeBlochC_eq_box (R := R) (fun y hy => by simp [hR y hy]) hN hz θ]
    have := norm_sq_exp_sum (latticeBox N) t
      (fun k => momentWeight α (y k) * inner ℝ (b e) (g (y k)))
    rw [this]
    simp only [hw, inner_smul_right]
  have hsum : ∑ e, ‖planeBlochC θ (fun y => momentWeight α y * inner ℝ (b e) (g y)) z‖ ^ 2 =
      ‖∑ k ∈ latticeBox N, Real.cos (t k) • w k‖ ^ 2 +
        ‖∑ k ∈ latticeBox N, Real.sin (t k) • w k‖ ^ 2 := by
    rw [Finset.sum_congr rfl fun e _ => hL e, Finset.sum_add_distrib,
      sum_sq_inner_sum b _ _ w, sum_sq_inner_sum b _ _ w]
  rw [← ENNReal.ofReal_sum_of_nonneg fun e _ => sq_nonneg _, hsum,
    ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  unfold latticePair
  rw [ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_pow (norm_nonneg _)]

theorem lintegral_datumCellSq_le {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) {g : Vec 2 → E} (hgm : StronglyMeasurable g)
    (hgc : HasCompactSupport g) (α : ℕ × ℕ) :
    ∫⁻ θ in freqCube, datumCellSq b g α θ ≤
      ENNReal.ofReal ((2 * Real.pi) ^ 2) *
        eLpNorm (fun y => momentWeight α y • g y) 2 volume ^ 2 := by
  obtain ⟨K, hK⟩ := datumCellSq_eq_latticePair b hgm hgc α
  rw [lintegral_congr hK]
  have hH : StronglyMeasurable fun y => momentWeight α y • g y := by
    unfold momentWeight
    exact (by fun_prop : Measurable fun y : Vec 2 => y 0 ^ α.1 * y 1 ^ α.2).stronglyMeasurable.smul
      hgm
  exact lintegral_cube_cell_latticePair_le_sm K hH


section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

theorem stageScaled_lintegral_level_succ {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (i : B1WIndex ι h Nw m Ks) (hi : i.1 ≠ 0) :
    ∫⁻ z in AVenhance.unitCube, ENNReal.ofReal (‖stageScaled F θ i F.a z‖ ^ 2) = 0 := by
  have h0 := frame_initial_level_succ F θ i.1 hi i.2.1 (b1wVec i) (b1wMom i)
  rw [← lintegral_zero (μ := volume.restrict AVenhance.unitCube)]
  refine lintegral_congr_ae ?_
  filter_upwards [h0] with z hz
  have hz' : planeBlochC θ (fun y => momentWeight (b1wMom i) y *
      inner ℝ (b1wVec i) (planeValue (F.u i.1 i.2.1 F.a) y)) z = 0 := hz
  simp [stageScaled, b1wStageVal, b1wStageFun, hz']

theorem rpow_neg_half_sq_le (p : ℝ) :
    ENNReal.ofReal ((p ^ (-(1 / 2 : ℝ))) ^ 2) ≤ ENNReal.ofReal p⁻¹ := by
  rcases lt_trichotomy p 0 with hp | hp | hp
  · have : p ^ (-(1 / 2 : ℝ)) = 0 := by
      rw [Real.rpow_def_of_neg hp,
        show -(1 / 2 : ℝ) * Real.pi = -(Real.pi / 2) by ring, Real.cos_neg, Real.cos_pi_div_two,
        mul_zero]
    rw [this]; simp
  · subst hp
    rw [Real.zero_rpow (by norm_num)]; simp
  · refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]
    norm_num
    exact Real.rpow_neg_one p

theorem stageScaled_level_zero_le {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (x : ι)
    (β : ℕ × ℕ) (hβ : β ∈ momentIndices (b1wLevelMoments m Ks 0)) :
    ∑ e : Fin (Module.finrank ℝ (h x)), ∫⁻ z in AVenhance.unitCube,
        ENNReal.ofReal (‖stageScaled F θ ⟨0, x, ⟨β, hβ⟩, e⟩ F.a z‖ ^ 2) ≤
      ENNReal.ofReal ((F.π x)⁻¹) *
        ENNReal.ofReal ((F.ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) ^ 2) *
        datumCellSq (stdOrthonormalBasis ℝ (h x)) (F.φ x) β θ := by
  unfold datumCellSq
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun e _ => ?_
  set i : B1WIndex ι h Nw m Ks := ⟨0, x, ⟨β, hβ⟩, e⟩ with hi
  have h0 := frame_initial_level_zero F θ x (b1wVec i) (b1wMom i)
  set s : ℝ := (F.π x ^ (-(1 / 2 : ℝ)) * F.ϖ ^ (β.1 + β.2) /
    ((β.1.factorial * β.2.factorial : ℕ) : ℝ) * (b1wAmp F.ηg F.letters 0)⁻¹) with hs
  have hscale : b1wScale F.π F.ϖ F.ηg F.letters i = (s : ℂ) := rfl
  have hamp : b1wAmp F.ηg F.letters (0 : Fin (Nw + 1)) = 1 := by
    simp [b1wAmp]
  have hint : ∫⁻ z in AVenhance.unitCube, ENNReal.ofReal (‖stageScaled F θ i F.a z‖ ^ 2) =
      ENNReal.ofReal (s ^ 2) * ∫⁻ z in AVenhance.unitCube, ENNReal.ofReal (
        ‖planeBlochC θ (fun y => momentWeight β y *
          inner ℝ (stdOrthonormalBasis ℝ (h x) e) (F.φ x y)) z‖ ^ 2) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr_ae ?_
    filter_upwards [h0] with z hz
    have hz' : planeBlochC θ (fun y => momentWeight β y *
        inner ℝ (stdOrthonormalBasis ℝ (h x) e) (planeValue (F.u 0 x F.a) y)) z =
        planeBlochC θ (fun y => momentWeight β y *
          inner ℝ (stdOrthonormalBasis ℝ (h x) e) (F.φ x y)) z := hz
    have hsv : stageScaled F θ i F.a z = (s : ℂ) * planeBlochC θ (fun y => momentWeight β y *
        inner ℝ (stdOrthonormalBasis ℝ (h x) e) (planeValue (F.u 0 x F.a) y)) z := rfl
    rw [hsv, hz', norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      ENNReal.ofReal_mul (sq_nonneg _)]
  rw [hint]
  gcongr
  have hs2 : s ^ 2 = (F.π x ^ (-(1 / 2 : ℝ))) ^ 2 *
      (F.ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) ^ 2 := by
    rw [hs, hamp]; simp only [inv_one, mul_one]; rw [mul_div_assoc, mul_pow]
  rw [hs2, ENNReal.ofReal_mul (sq_nonneg _)]
  exact mul_le_mul_left (rpow_neg_half_sq_le _) _

theorem b1wLevelMoments_zero (m : ℕ) (Ks : Fin Nw → ℕ) :
    b1wLevelMoments m Ks 0 = wordReserveN m Ks := by
  simp [b1wLevelMoments, wordReserveN]

theorem stageDatumSq_le {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) :
    stageDatumSq F m Ks θ ≤
      ∑ β ∈ momentIndices (wordReserveN m Ks), ∑ x : ι, ENNReal.ofReal ((F.π x)⁻¹) *
        ENNReal.ofReal ((F.ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) ^ 2) *
        datumCellSq (stdOrthonormalBasis ℝ (h x)) (F.φ x) β θ := by
  unfold stageDatumSq
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type]
  rw [Fin.sum_univ_succ]
  have hz : ∀ j : Fin Nw, (∑ x : ι, ∑ β : {β : ℕ × ℕ // β ∈ momentIndices
      (b1wLevelMoments m Ks j.succ)}, ∑ e : Fin (Module.finrank ℝ (h x)),
        ∫⁻ z in AVenhance.unitCube, ENNReal.ofReal
          (‖stageScaled F θ (⟨j.succ, x, β, e⟩ : B1WIndex ι h Nw m Ks) F.a z‖ ^ 2)) = 0 := by
    intro j
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun β _ =>
      Finset.sum_eq_zero fun e _ => ?_
    exact stageScaled_lintegral_level_succ F θ ⟨j.succ, x, β, e⟩ (Fin.succ_ne_zero j)
  rw [Finset.sum_eq_zero fun j _ => hz j, add_zero]
  calc _ ≤ ∑ x : ι, ∑ β : {β : ℕ × ℕ // β ∈ momentIndices (b1wLevelMoments m Ks 0)},
        ENNReal.ofReal ((F.π x)⁻¹) *
          ENNReal.ofReal ((F.ϖ ^ (β.1.1 + β.1.2) /
            ((β.1.1.factorial * β.1.2.factorial : ℕ) : ℝ)) ^ 2) *
          datumCellSq (stdOrthonormalBasis ℝ (h x)) (F.φ x) β.1 θ :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun β _ =>
          stageScaled_level_zero_le F θ x β.1 β.2
    _ = ∑ β ∈ momentIndices (b1wLevelMoments m Ks 0), ∑ x : ι, ENNReal.ofReal ((F.π x)⁻¹) *
          ENNReal.ofReal ((F.ϖ ^ (β.1 + β.2) /
            ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) ^ 2) *
          datumCellSq (stdOrthonormalBasis ℝ (h x)) (F.φ x) β θ := by
        rw [Finset.sum_comm]
        exact Finset.sum_coe_sort (momentIndices (b1wLevelMoments m Ks 0))
          (fun β => ∑ x : ι, ENNReal.ofReal ((F.π x)⁻¹) *
            ENNReal.ofReal ((F.ϖ ^ (β.1 + β.2) /
              ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) ^ 2) *
            datumCellSq (stdOrthonormalBasis ℝ (h x)) (F.φ x) β θ)
    _ = _ := by rw [b1wLevelMoments_zero]

theorem measurable_datumCellSq {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) {g : Vec 2 → E} (hgm : StronglyMeasurable g)
    (hgc : HasCompactSupport g) (α : ℕ × ℕ) :
    Measurable fun θ => datumCellSq b g α θ := by
  obtain ⟨K, hK⟩ := datumCellSq_eq_latticePair b hgm hgc α
  have hH : StronglyMeasurable fun y => momentWeight α y • g y := by
    unfold momentWeight
    exact (by fun_prop : Measurable fun y : Vec 2 => y 0 ^ α.1 * y 1 ^ α.2).stronglyMeasurable.smul
      hgm
  have : (fun θ => datumCellSq b g α θ) = fun θ => ∫⁻ z in AVenhance.unitCube,
      latticePair K (fun y => momentWeight α y • g y) θ z := funext hK
  rw [this]
  exact (measurable_latticePair_sm K hH).lintegral_prod_right'

/-- The moment-norm term of one moment, squared. -/
theorem momentNorm_term_sq {ι : Type u} [Fintype ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    (π : ι → ℝ) (ϖ : ℝ) (φ : ∀ x, Vec 2 → h x) (β : ℕ × ℕ) :
    (ENNReal.ofReal (((β.1.factorial * β.2.factorial : ℕ) : ℝ)⁻¹) *
      (∑ v, ENNReal.ofReal ((π v)⁻¹) *
        eLpNorm (fun z => ((ϖ * z 0) ^ β.1 * (ϖ * z 1) ^ β.2) • φ v z) 2 volume ^ 2) ^
          (1 / 2 : ℝ)) ^ 2 =
    ∑ x, ENNReal.ofReal ((π x)⁻¹) *
        ENNReal.ofReal ((ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) ^ 2) *
        eLpNorm (fun y => momentWeight β y • φ x y) 2 volume ^ 2 := by
  rw [mul_pow, rpow_half_sq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hfun : (fun z : Vec 2 => ((ϖ * z 0) ^ β.1 * (ϖ * z 1) ^ β.2) • φ x z) =
      ϖ ^ (β.1 + β.2) • fun y => momentWeight β y • φ x y := by
    funext z
    simp only [Pi.smul_apply, momentWeight, smul_smul]
    congr 1
    rw [mul_pow, mul_pow, pow_add]; ring
  rw [hfun, eLpNorm_const_smul, mul_pow, Real.enorm_eq_ofReal_abs]
  have hq : ENNReal.ofReal ((ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) ^ 2) =
      ENNReal.ofReal (((β.1.factorial * β.2.factorial : ℕ) : ℝ)⁻¹) ^ 2 *
        ENNReal.ofReal |ϖ ^ (β.1 + β.2)| ^ 2 := by
    rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_pow (abs_nonneg _),
      ← ENNReal.ofReal_mul (by positivity), div_eq_inv_mul, mul_pow, sq_abs]
  rw [hq]
  ring

end Frame

/-- **O3, the datum** (`StageDatumStatement`): the integral over the zone of the squared `L²`
norms of the scaled stage values at the start of the frame is at most `(2π)²` times the squared
moment norm of the datum. -/
theorem stageDatumStatement : StageDatumStatement.{u, v} := by
  intro K Nw D m Ks
  refine ⟨(2 * Real.pi) ^ 2, by positivity, ?_⟩
  intro g₁ ι _ h _ _ _ _ _ _ F _
  set n : ℕ := wordReserveN m Ks with hn
  have hmeas : ∀ (β : ℕ × ℕ) (x : ι), Measurable fun θ =>
      datumCellSq (stdOrthonormalBasis ℝ (h x)) (F.φ x) β θ := fun β x =>
    measurable_datumCellSq _ (F.compact x).1 (F.compact x).2 β
  calc ∫⁻ θ in freqCube, stageDatumSq F m Ks θ
      ≤ ∫⁻ θ in freqCube, ∑ β ∈ momentIndices n, ∑ x : ι, ENNReal.ofReal ((F.π x)⁻¹) *
        ENNReal.ofReal ((F.ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) ^ 2) *
        datumCellSq (stdOrthonormalBasis ℝ (h x)) (F.φ x) β θ :=
        lintegral_mono fun θ => stageDatumSq_le F θ
    _ = ∑ β ∈ momentIndices n, ∑ x : ι, ENNReal.ofReal ((F.π x)⁻¹) *
        ENNReal.ofReal ((F.ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) ^ 2) *
        ∫⁻ θ in freqCube, datumCellSq (stdOrthonormalBasis ℝ (h x)) (F.φ x) β θ := by
        rw [lintegral_finsetSum _ fun β _ =>
          Finset.measurable_sum _ fun x _ => (hmeas β x).const_mul _]
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [lintegral_finsetSum _ fun x _ => (hmeas β x).const_mul _]
        exact Finset.sum_congr rfl fun x _ => lintegral_const_mul _ (hmeas β x)
    _ ≤ ∑ β ∈ momentIndices n, ∑ x : ι, ENNReal.ofReal ((F.π x)⁻¹) *
        ENNReal.ofReal ((F.ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) ^ 2) *
        (ENNReal.ofReal ((2 * Real.pi) ^ 2) *
          eLpNorm (fun y => momentWeight β y • F.φ x y) 2 volume ^ 2) :=
        Finset.sum_le_sum fun β _ => Finset.sum_le_sum fun x _ =>
          mul_le_mul_right (lintegral_datumCellSq_le _ (F.compact x).1 (F.compact x).2 β) _
    _ = ENNReal.ofReal ((2 * Real.pi) ^ 2) * ∑ β ∈ momentIndices n,
        (ENNReal.ofReal (((β.1.factorial * β.2.factorial : ℕ) : ℝ)⁻¹) *
      (∑ v, ENNReal.ofReal ((F.π v)⁻¹) *
        eLpNorm (fun z => ((F.ϖ * z 0) ^ β.1 * (F.ϖ * z 1) ^ β.2) • F.φ v z) 2 volume ^ 2) ^
          (1 / 2 : ℝ)) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [momentNorm_term_sq, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring
    _ ≤ ENNReal.ofReal ((2 * Real.pi) ^ 2) * (∑ β ∈ momentIndices n,
        ENNReal.ofReal (((β.1.factorial * β.2.factorial : ℕ) : ℝ)⁻¹) *
      (∑ v, ENNReal.ofReal ((F.π v)⁻¹) *
        eLpNorm (fun z => ((F.ϖ * z 0) ^ β.1 * (F.ϖ * z 1) ^ β.2) • F.φ v z) 2 volume ^ 2) ^
          (1 / 2 : ℝ)) ^ 2 :=
        mul_le_mul_right (Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => zero_le) _
    _ = ENNReal.ofReal ((2 * Real.pi) ^ 2) * momentNorm F.π n F.ϖ F.φ ^ 2 := rfl

end AVRegularity.CycleWords.Discard.BandDatum
end
end

section
/-! # the adjoint curves of a frame, with a kernel

* `IsFibreKernel.restrict`: a kernel on `[a, b]` is a kernel on `[a, t]`, `t ≤ b`.
* `isFibreKernel_shift`, `cellWeakHilbertCurve_shift`: the shift of the coefficients may be
  rewritten (`b1wCoeff F θ` has the shift `√η ξ = θ`, `fibreShift_eq`).
* `frame_drift_jet_le`: the drift jets of a frame are at most `J_l/√η`.
* `adjoint_kernel_frame`: the adjoint propagator bound for a frame. From an `H^j` test at time `t`, the adjoint curve has
  `H^j` representatives of size `C P_e^Q κ(r,t)` on `[a, t]`, with `C, Q` before the frame. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin

namespace AVRegularity.CycleWords.Discard

open AVRegularity.CycleWords.Assembly

universe u v

/-- A kernel on `[a, b]` is a kernel on `[a, t]` for `t ≤ b`. -/
theorem IsFibreKernel.restrict {C : CellCoefficients} {hG : IsCellMetric C.G} {V : ℝ}
    {hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2)}
    {hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2} {a b A : ℝ} {κ : ℝ → ℝ → ℝ}
    (H : IsFibreKernel C hG V hv hb a b A κ) {t : ℝ} (ht : t ≤ b) :
    IsFibreKernel C hG V hv hb a t A κ where
  pos := H.pos
  le_one := H.le_one
  self := H.self
  mul_le r s t' h1 h2 h3 h4 := H.mul_le r s t' h1 h2 h3 (h4.trans ht)
  anti r s t' h1 h2 h3 h4 := H.anti r s t' h1 h2 h3 (h4.trans ht)
  shrink r r' t' t'' h1 h2 h3 h4 h5 h6 h7 := H.shrink r r' t' t'' h1 h2 h3 h4 h5 h6 (h7.trans ht)
  decay r s h1 h2 h3 := H.decay r s h1 h2 (h3.trans ht)

/-- The shift of the coefficients of a kernel may be rewritten. -/
theorem isFibreKernel_shift {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {θ₁ θ₂ : Fin 2 → ℂ} (e : θ₁ = θ₂) {hG : IsCellMetric G} {V : ℝ}
    {hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2)} {hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2}
    {a b A : ℝ} {κ : ℝ → ℝ → ℝ} (H : IsFibreKernel ⟨G, v, θ₁, 0⟩ hG V hv hb a b A κ) :
    IsFibreKernel ⟨G, v, θ₂, 0⟩ hG V hv hb a b A κ := by
  subst e
  exact H

/-- The shift of the coefficients of a forced curve may be rewritten. -/
theorem cellWeakHilbertCurve_shift {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    {v : ℝ → Vec 2 → Vec 2} {θ₁ θ₂ : Fin 2 → ℂ} (e : θ₁ = θ₂) {hG : IsCellMetric G} {V : ℝ}
    {hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2)} {hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2}
    {a b : ℝ} {u : ℝ → ComplexCellL2} {slice : ℝ → TorusHk 1 ℂ} {S : ℝ → ComplexCellL2}
    {Fl : ℝ → Fin 2 → ComplexCellL2}
    (H : CellWeakHilbertCurve a b u slice (fun t =>
      cellDualDerivative ⟨G, v, θ₁, 0⟩ hG V hv hb t (slice t) (S t) (Fl t))) :
    CellWeakHilbertCurve a b u slice (fun t =>
      cellDualDerivative ⟨G, v, θ₂, 0⟩ hG V hv hb t (slice t) (S t) (Fl t)) := by
  subst e
  exact H

/-- `√(θ·θ) ≤ 2π` on the frequency cube. -/
theorem sqrt_vecDot_le_of_freqCube {θ : Vec 2} (hθ : θ ∈ freqCube) :
    Real.sqrt (vecDot θ θ) ≤ 2 * Real.pi := by
  have h0 := abs_le.1 (hθ 0)
  have h1 := abs_le.1 (hθ 1)
  have hπ := Real.pi_pos
  rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  refine Real.sqrt_le_sqrt ?_
  unfold vecDot
  rw [Fin.sum_univ_two]
  nlinarith

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw : ℕ}

/-- The coefficients of a frame with the real shift `θ`. -/
theorem b1wCoeff_eq_real {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) :
    (fun k => (Real.sqrt F.η : ℂ) * planeFibreFrequency F.η θ k) = fun k => ((θ k : ℝ) : ℂ) :=
  fibreShift_eq F.piece.hη θ

/-- The drift jets of a frame: `‖D^l v(t)‖ ≤ J/√η` when `C_{v,l} ≤ J`. -/
theorem frame_drift_jet_le {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) {l : ℕ} {J : ℝ}
    (hJ : K.Cvj l ≤ J) (t : ℝ) (x : Vec 2) :
    ‖iteratedFDeriv ℝ l (F.v t) x‖ ≤ J / Real.sqrt F.η := by
  have hs : 0 < Real.sqrt F.η := Real.sqrt_pos.mpr F.piece.hη
  rw [le_div_iff₀ hs]
  have h := F.piece.hvj l t x
  rw [iteratedFDeriv_const_smul_apply'
    (((F.piece.hvs t).of_le (by exact_mod_cast le_top)).contDiffAt), norm_smul,
    Real.norm_of_nonneg hs.le] at h
  linarith

end Frame

/-- The adjoint propagator bound for a frame. -/
theorem adjoint_kernel_frame (hK2 : CellAdjointKernelHsStatement) (K : ScalarConstants) (j : ℕ)
    {A : ℝ} (hA : 1 ≤ A) :
    ∃ (C : ℝ) (Q : ℕ), 0 < C ∧
    ∀ (g₁ : ℝ) {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
      [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
      [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D Nw : ℕ}
      (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
      θ ∈ freqCube →
    ∀ (V : ℝ) (hb : ∀ t x, ∑ i, F.v t x i ^ 2 ≤ V ^ 2) (κ : ℝ → ℝ → ℝ),
      IsFibreKernel (b1wCoeff F θ) F.piece.hGm V F.piece.hv.1 hb F.a F.b A κ →
    ∀ t ∈ Icc F.a F.b, ∀ ψ : TorusHk j ℂ,
      ∃ (Ψv : ℝ → ComplexCellL2) (Ψs : ℝ → TorusHk 1 ℂ) (U : ℝ → TorusHk j ℂ),
        CellWeakHilbertCurve F.a t Ψv Ψs (fun r =>
          -cellDualDerivative
            (cellAdjointCoefficients ⟨fun s _ => F.G s, F.v, fun k => ((θ k : ℝ) : ℂ), 0⟩)
            F.piece.hGm V (cellDrift_neg F.piece.hv).1 (cellDrift_neg_bound hb) r (Ψs r) 0 0) ∧
        Ψv t = torusHkValueCLM ψ ∧
        ∀ r ∈ Icc F.a t, torusHkValueCLM (U r) = Ψv r ∧
          ‖U r‖ ≤ C * peFactor F.η ^ Q * κ r t * ‖ψ‖ := by
  classical
  obtain ⟨C, Q, hC, hK⟩ := hK2 j (2 * Real.pi) A (by positivity) hA
  obtain ⟨Js, hJs⟩ : ∃ Js : ℝ, Js = ∑ l ∈ Finset.range (j + 2), b1wJets K l := ⟨_, rfl⟩
  have hJs0 : 0 ≤ Js := by
    rw [hJs]
    exact Finset.sum_nonneg fun l _ => le_max_right _ _
  refine ⟨C * (1 + Js) ^ Q, Q, by positivity, ?_⟩
  intro g₁ ι _ h _ _ _ _ _ _ D Nw F θ hθ V hb κ hκ t ht ψ
  have hη := F.piece.hη
  have hs : 0 < Real.sqrt F.η := Real.sqrt_pos.mpr hη
  obtain ⟨Ψv, Ψs, hΨ, hΨt⟩ := adjointCurve_exists ht.1 (fun s _ => F.G s) F.piece.hGm F.piece.hv V
    hb (fun k => ((θ k : ℝ) : ℂ)) (torusHkValueCLM ψ)
  have hκ' : IsFibreKernel ⟨fun s _ => F.G s, F.v, fun k => ((θ k : ℝ) : ℂ), 0⟩ F.piece.hGm V
      F.piece.hv.1 hb F.a t A κ :=
    (isFibreKernel_shift (b1wCoeff_eq_real F θ) hκ).restrict ht.2
  have hjet : ∀ (l : ℕ) t', l ≤ j + 1 → t' ∈ Icc F.a t → ∀ x,
      ‖iteratedFDeriv ℝ l (F.v t') x‖ ≤ Js / Real.sqrt F.η := fun l t' hl _ x =>
    frame_drift_jet_le F ((le_max_left _ _).trans (by
      rw [hJs]
      exact Finset.single_le_sum (f := b1wJets K) (fun l _ => le_max_right _ _)
        (Finset.mem_range.2 (by omega)))) t' x
  obtain ⟨h1, -⟩ := hK F.a t (Js / Real.sqrt F.η) F.G F.piece.hGm F.piece.hv V hb θ ht.1
    (div_nonneg hJs0 hs.le) (sqrt_vecDot_le_of_freqCube hθ) (fun t' _ => F.piece.hvs t') hjet κ
    hκ' Ψv Ψs hΨ
  have hex : ∀ r, ∃ w : TorusHk j ℂ, r ∈ Icc F.a t →
      torusHkValueCLM w = Ψv r ∧ ‖w‖ ≤ C * (1 + Js / Real.sqrt F.η) ^ Q * κ r t * ‖ψ‖ := by
    intro r
    by_cases hr : r ∈ Icc F.a t
    · obtain ⟨w, hw⟩ := h1 ψ hΨt.symm r hr
      exact ⟨w, fun _ => hw⟩
    · exact ⟨0, fun h => absurd h hr⟩
  choose U hU using hex
  refine ⟨Ψv, Ψs, U, hΨ, hΨt, fun r hr => ⟨(hU r hr).1, (hU r hr).2.trans ?_⟩⟩
  have hL : (1 + Js / Real.sqrt F.η) ^ Q ≤ (1 + Js) ^ Q * peFactor F.η ^ Q := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (one_add_div_sqrt_le hη hJs0) Q
  have hκψ : 0 ≤ κ r t * ‖ψ‖ := mul_nonneg (hκ.pos r t).le (norm_nonneg _)
  calc C * (1 + Js / Real.sqrt F.η) ^ Q * κ r t * ‖ψ‖
      = C * (1 + Js / Real.sqrt F.η) ^ Q * (κ r t * ‖ψ‖) := by ring
    _ ≤ C * ((1 + Js) ^ Q * peFactor F.η ^ Q) * (κ r t * ‖ψ‖) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL hC.le) hκψ
    _ = C * (1 + Js) ^ Q * peFactor F.η ^ Q * κ r t * ‖ψ‖ := by ring

end AVRegularity.CycleWords.Discard
end
end
end

section
section
/-! # `TorusHkBandBoundStatement`

Route: real and imaginary parts (`mapTorusHk`), the real band bound `real_band`
(Parseval per jet component), and `‖a + i b‖² ≤ 2‖a‖² + 2‖b‖²`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.EntryWeakProofs
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
open AVRegularity.CycleEvolution AVRegularity.CycleWords.Assembly
open scoped ENNReal

namespace AVRegularity.CycleWords.Discard

/-- The cell coefficients of a complex element are those of its real and imaginary parts. -/
theorem cellCoeff_value (N : ℕ) (w : TorusHk N ℂ) (n : Fin 2 → ℤ) :
    cellFourierCoeff (torusHkValueCLM w : Vec 2 → ℂ) n =
      realJetFourier N (mapTorusHk Complex.reCLM w) (valueIndex2 N) n +
        Complex.I * realJetFourier N (mapTorusHk Complex.imCLM w) (valueIndex2 N) n := by
  have hmem : MemLp (torusHkValueCLM w : Vec 2 → ℂ) 2 (volume.restrict AVenhance.unitCube) :=
    Lp.memLp _
  rw [cellCoeff_split _ hmem n, ← cellCoeff_real, ← cellCoeff_real]
  congr 1
  · apply cellCoeff_congr
    filter_upwards [mapTorusHk_jet_ae Complex.reCLM w (valueIndex2 N)] with x hx
    rw [hx]
    rfl
  · congr 1
    apply cellCoeff_congr
    filter_upwards [mapTorusHk_jet_ae Complex.imCLM w (valueIndex2 N)] with x hx
    rw [hx]
    rfl

theorem norm_sq_le' (a b : ℂ) : ‖a + Complex.I * b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_add_le a (Complex.I * b)
  rw [norm_mul, Complex.norm_I, one_mul] at h
  nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg (a + Complex.I * b),
    sq_nonneg (‖a‖ - ‖b‖)]

theorem vecDot_shift' (θ : Vec 2) (n : Fin 2 → ℤ) :
    vecDot (quietFourierFrequency θ n) (quietFourierFrequency θ n) =
      ∑ i : Fin 2, (2 * Real.pi * (n i : ℝ) + θ i) ^ 2 := by
  simp only [vecDot, quietFourierFrequency, sq]

/-- **`TorusHkBandBoundStatement`.** -/
theorem torusHkBandBound : TorusHkBandBoundStatement := by
  intro k N hk
  set Cc : ℝ := ((1 + 4 * Real.pi ^ 2) * 2) ^ k with hCc
  set Mr : ℝ := ‖mapTorusHkCLM N Complex.reCLM‖ with hMr
  set Mi : ℝ := ‖mapTorusHkCLM N Complex.imCLM‖ with hMi
  refine ⟨2 * Cc * (Mr ^ 2 + Mi ^ 2), by positivity, ?_⟩
  intro w θ hθ
  have hθ' : ∀ i, |θ i| ≤ Real.pi := hθ
  set wr := mapTorusHk Complex.reCLM w with hwr
  set wi := mapTorusHk Complex.imCLM w with hwi
  obtain ⟨hsa, hba⟩ := real_band N k hk wr θ hθ'
  obtain ⟨hsb, hbb⟩ := real_band N k hk wi θ hθ'
  set W : (Fin 2 → ℤ) → ℝ := fun n => (1 + ∑ i : Fin 2, (2 * Real.pi * (n i : ℝ) + θ i) ^ 2) ^ k
    with hW
  have hW0 : ∀ n, 0 ≤ W n := fun n => by
    have : 0 ≤ ∑ i : Fin 2, (2 * Real.pi * (n i : ℝ) + θ i) ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    positivity
  have hterm : ∀ n : Fin 2 → ℤ,
      (if (0 : ℝ) ^ 2 ≤ vecDot (quietFourierFrequency θ n) (quietFourierFrequency θ n) then
        ENNReal.ofReal ((1 + vecDot (quietFourierFrequency θ n) (quietFourierFrequency θ n)) ^ k *
          ‖cellFourierCoeff (torusHkValueCLM w : Vec 2 → ℂ) n‖ ^ 2) else 0) ≤
      ENNReal.ofReal (2 * (W n * ‖realJetFourier N wr (valueIndex2 N) n‖ ^ 2) +
        2 * (W n * ‖realJetFourier N wi (valueIndex2 N) n‖ ^ 2)) := by
    intro n
    have hd : (0 : ℝ) ^ 2 ≤ vecDot (quietFourierFrequency θ n) (quietFourierFrequency θ n) := by
      rw [vecDot_shift']; rw [zero_pow two_ne_zero]
      exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
    simp only [hd, ↓reduceIte]
    rw [vecDot_shift', cellCoeff_value]
    apply ENNReal.ofReal_le_ofReal
    have := norm_sq_le' (realJetFourier N wr (valueIndex2 N) n)
      (realJetFourier N wi (valueIndex2 N) n)
    have h0 := hW0 n
    change W n * _ ≤ _
    nlinarith [mul_le_mul_of_nonneg_left this h0]
  unfold cellBandSq
  calc _ ≤ ∑' n : Fin 2 → ℤ, ENNReal.ofReal (2 * (W n * ‖realJetFourier N wr (valueIndex2 N) n‖ ^ 2) +
        2 * (W n * ‖realJetFourier N wi (valueIndex2 N) n‖ ^ 2)) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' n : Fin 2 → ℤ, (2 * (W n * ‖realJetFourier N wr (valueIndex2 N) n‖ ^ 2) +
        2 * (W n * ‖realJetFourier N wi (valueIndex2 N) n‖ ^ 2))) := by
      rw [ENNReal.ofReal_tsum_of_nonneg]
      · intro n; have := hW0 n; positivity
      · exact (hsa.mul_left 2).add (hsb.mul_left 2)
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      rw [Summable.tsum_add (hsa.mul_left 2) (hsb.mul_left 2), tsum_mul_left, tsum_mul_left]
      have hra : ‖wr‖ ≤ Mr * ‖w‖ := by
        rw [hwr, ← mapTorusHkCLM_apply]; exact (mapTorusHkCLM N Complex.reCLM).le_opNorm w
      have hib : ‖wi‖ ≤ Mi * ‖w‖ := by
        rw [hwi, ← mapTorusHkCLM_apply]; exact (mapTorusHkCLM N Complex.imCLM).le_opNorm w
      have h1 : ‖wr‖ ^ 2 ≤ (Mr * ‖w‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hra 2
      have h2 : ‖wi‖ ^ 2 ≤ (Mi * ‖w‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hib 2
      have hCc0 : 0 ≤ Cc := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h1 hCc0, mul_le_mul_of_nonneg_left h2 hCc0]

end AVRegularity.CycleWords.Discard
end
end

section
/-! # the stage curves of the word chain with the `L²` bounds of the sources in time

A copy of `b1w_stage_curves` that also returns the space-time `L²` membership of the sources
and fluxes (needed for the scalar-source Duhamel equation of a Fourier mode). -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords.Assembly AVRegularity.CycleWords
open scoped ENNReal

namespace AVRegularity.CycleWords.Discard

universe u v

section Curves

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D Nw : ℕ}

theorem b1w_stage_curves_mem {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (m : ℕ)
    (Ks : Fin Nw → ℕ) (θ : Vec 2)
    (hM : ∀ (j : Fin (Nw + 1)) (x : ι) (e : h x) (β : ℕ × ℕ),
      ∃ (Dθ : ℝ → RawJet2 1 ℂ) (src : ℝ → Vec 2 → ℂ)
        (Fl : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)),
        MemLp (Function.uncurry src) 2
          ((volume.restrict (Icc F.a F.b)).prod (volume.restrict AVenhance.unitCube)) ∧
        (∀ k : Fin 2, MemLp (fun p : ℝ × Vec 2 => Fl p.1 p.2 k) 2
          ((volume.restrict (Icc F.a F.b)).prod (volume.restrict AVenhance.unitCube))) ∧
        (∀ᵐ r ∂volume.restrict (Icc F.a F.b),
          src r =ᵐ[volume.restrict AVenhance.unitCube] amplitudeIdLiteralSource F θ j x e β r ∧
          Fl r =ᵐ[volume.restrict AVenhance.unitCube] amplitudeIdLiteralFlux F θ j x e β r) ∧
        IsCellSolution (Icc F.a F.b)
          (fibreCoefficients F.η F.G F.v (planeFibreFrequency F.η θ) (fun _ => 0)) src Fl Dθ ∧
        ∀ t ∈ Icc F.a F.b, cellValue Dθ t =ᵐ[volume.restrict AVenhance.unitCube]
          planeBlochC θ (fun y => momentWeight β y * inner ℝ e (planeValue (F.u j x t) y)))
    (V : ℝ) (hb : ∀ t x, ∑ i, F.v t x i ^ 2 ≤ V ^ 2) (c : B1WIndex ι h Nw m Ks → ℂ) :
    ∃ (Dθ : B1WIndex ι h Nw m Ks → ℝ → RawJet2 1 ℂ) (src : B1WIndex ι h Nw m Ks → ℝ → Vec 2 → ℂ)
      (Fl : B1WIndex ι h Nw m Ks → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)),
      (∀ i, CellWeakHilbertCurve F.a F.b (fun t => cellScalarCLM (c i) (cellRawTrace (Dθ i) t))
        (fun t => cellH1Scalar (c i) (cellH1Slice (Dθ i) t)) (fun t =>
          cellDualDerivative ⟨fun t _ => F.G t, F.v,
            fun k => (Real.sqrt F.η : ℂ) * planeFibreFrequency F.η θ k, 0⟩ F.piece.hGm V
            F.piece.hv.1 hb t (cellH1Scalar (c i) (cellH1Slice (Dθ i) t))
            (cellScalarCLM (c i) (cellSourceSlice (src i) t))
            (fun k => cellScalarCLM (c i) (cellSourceSlice (fun r z => Fl i r z k) t)))) ∧
      (∀ i, ∀ t ∈ Icc F.a F.b, cellValue (Dθ i) t =ᵐ[volume.restrict AVenhance.unitCube]
        planeBlochC θ (fun y => momentWeight i.2.2.1.1 y *
          inner ℝ (stdOrthonormalBasis ℝ (h i.2.1) i.2.2.2) (planeValue (F.u i.1 i.2.1 t) y))) ∧
      (∀ i, ∀ᵐ r ∂volume.restrict (Icc F.a F.b),
        src i r =ᵐ[volume.restrict AVenhance.unitCube] amplitudeIdLiteralSource F θ i.1 i.2.1
          (stdOrthonormalBasis ℝ (h i.2.1) i.2.2.2) i.2.2.1.1 r ∧
        Fl i r =ᵐ[volume.restrict AVenhance.unitCube] amplitudeIdLiteralFlux F θ i.1 i.2.1
          (stdOrthonormalBasis ℝ (h i.2.1) i.2.2.2) i.2.2.1.1 r) ∧
      (∀ i, ∀ t ∈ Icc F.a F.b, MemLp (cellValue (Dθ i) t) 2 (volume.restrict AVenhance.unitCube)) ∧
      (∀ i, ∀ᵐ r ∂volume.restrict (Icc F.a F.b),
        MemLp (src i r) 2 (volume.restrict AVenhance.unitCube) ∧
          ∀ j : Fin 2, MemLp (fun z => Fl i r z j) 2 (volume.restrict AVenhance.unitCube)) ∧
      (∀ i, MemLp (Function.uncurry (src i)) 2
        ((volume.restrict (Icc F.a F.b)).prod (volume.restrict AVenhance.unitCube))) ∧
      (∀ i, ∀ k : Fin 2, MemLp (fun p : ℝ × Vec 2 => Fl i p.1 p.2 k) 2
        ((volume.restrict (Icc F.a F.b)).prod (volume.restrict AVenhance.unitCube))) := by
  have hstage := fun i : B1WIndex ι h Nw m Ks =>
    hM i.1 i.2.1 (stdOrthonormalBasis ℝ (h i.2.1) i.2.2.2) i.2.2.1.1
  choose Dθ src Fl hsrc hFl hlit hsol hval using hstage
  refine ⟨Dθ, src, Fl, fun i => ?_, hval, hlit, fun i t ht => ((hsol i).2.2.1 t ht).1,
    fun i => ?_, hsrc, fun i k => hFl i k⟩
  swap
  · filter_upwards [cellSource_memLp_slices (Icc F.a F.b) (src i) (hsrc i),
      ae_all_iff.2 fun j : Fin 2 => cellSource_memLp_slices (Icc F.a F.b)
        (fun r z => Fl i r z j) (hFl i j)] with r h1 h2
    exact ⟨h1, h2⟩
  have hs := hsol i
  rw [fibreCoefficients_zero_eq] at hs
  have hH := (cellSolution_to_Hilbert F.ordered ⟨fun t _ => F.G t, F.v,
      fun k => (Real.sqrt F.η : ℂ) * planeFibreFrequency F.η θ k, 0⟩ F.piece.hGm V 0
    F.piece.hv.1 hb measurable_const (fun _ => by simp) (src i) (Fl i) (hsrc i)
    (MemLp.of_eval_piLp (q := 2) fun k => hFl i k) (Dθ i) hs).complex_smul (c i)
  refine CellWeakHilbertCurve.dual_congr hH (Filter.Eventually.of_forall fun t => ?_)
  exact cellDualDerivative_complex_scalar _ F.piece.hGm V F.piece.hv.1 hb t _ _ _ (c i)

end Curves

end AVRegularity.CycleWords.Discard
end
end

section
/-! # the tested forcing of a stage at a mode

At a quiet good time the forcing of the mode `n` of the stage `i₀` equals
`∑_{i'} τ_{i₀,i'} c_{i'}`, with `τ` the diagonal coefficient of the test transform
(`quiet_forcing_identity`). -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords.Assembly AVRegularity.CycleWords
open scoped ENNReal

namespace AVRegularity.CycleWords.Discard

theorem star_cellComplexFourierMode (m : Fin 2 → ℤ) (y : Vec 2) :
    star (cellComplexFourierMode m y) = cellComplexFourierMode (-m) y := by
  rw [star_mode]
  simp [cellComplexFourierMode, cellComplexFourierPhase, seamDotPairing_apply, vecDot,
    Fin.sum_univ_two]
  ring_nf

theorem mode_periodic (m : Fin 2 → ℤ) :
    AVenhance.IsZ2Periodic (cellComplexFourierMode m) := by
  intro n x
  have h : cellComplexFourierMode m (x + AVenhance.latticeShift n) =
      cellComplexFourierMode m x * cellComplexFourierMode m (AVenhance.latticeShift n) := by
    simp only [cellComplexFourierMode, ← Complex.exp_add, map_add]
  rw [h]
  have : cellComplexFourierMode m (AVenhance.latticeShift n) = 1 := by
    simp only [cellComplexFourierMode, cellComplexFourierPhase, AVenhance.latticeShift,
      smul_apply, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
      seamDotPairing_apply, vecDot, Fin.sum_univ_two, smul_eq_mul]
    have : (2 * (Real.pi : ℂ) * Complex.I) * (((m 0 : ℝ) * (n 0 : ℝ) + (m 1 : ℝ) * (n 1 : ℝ) : ℝ) : ℂ)
        = ((m 0 * n 0 + m 1 * n 1 : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast; ring
    rw [this]
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [this, mul_one]

local instance F1Measure : MeasureSpace UnitAddCircle := instMeasureSpaceUnitAddCircle

theorem classical_quietHsMode (N : ℕ) (hN : 2 ≤ N) (m : Fin 2 → ℤ) (a : ℂ) :
    torusHigherClassicalValue N (quietHsMode N m a) = fun y => a * cellComplexFourierMode m y := by
  refine AVRegularity.CycleComparison.Lift.periodicContinuous_eq_of_cell_ae _ _
    (torusHigherClassicalValue_contDiff N 0 (by omega) _).continuous ?_
    (torusHigherClassicalValue_periodic N _) ?_ ?_
  · exact continuous_const.mul ((cellComplexFourierMode_contDiff m).continuous)
  · intro n x
    simp only [mode_periodic m n x]
  · refine (torusHigherClassicalValue_ae N hN _).trans ?_
    rw [mode_value, scalarTorusToCell_mode]
    filter_upwards [Lp.coeFn_smul a ((cellComplexFourierMode_memLp m).toLp (cellComplexFourierMode m)),
      (cellComplexFourierMode_memLp m).coeFn_toLp] with x h1 h2
    rw [h1, Pi.smul_apply, h2, smul_eq_mul]

section Force

universe u v

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- The diagonal coefficient of the stage coupling `τ_{i,i'}(r)` at the mode `n`. -/
def quietTau {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (n : Fin 2 → ℤ) (r : ℝ) (i i' : B1WIndex ι h Nw m Ks) : ℂ :=
  if b1wSt i' < b1wSt i then
    b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
      b1wTestTransform F θ i i' r (fun y => 1 * cellComplexFourierMode (-n) y) 0
  else 0

theorem quietTau_zero {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (n : Fin 2 → ℤ) (r : ℝ) (i i' : B1WIndex ι h Nw m Ks) (hi : ¬ b1wSt i' < b1wSt i) :
    quietTau F θ n r i i' = 0 := by
  simp [quietTau, hi]

theorem quiet_transform_star_mode {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (r : ℝ)
    (hr0 : ∀ z, F.v r z = 0)
    (hq : ∀ l, ∀ (v u : ι) (d : Finset.Icc 2 D), ∀ γ ∈ (F.letters l).edge v u d, ∀ α,
      ∀ X z z', γ.coeff α r X z = γ.coeff α r X z')
    (n : Fin 2 → ℤ) (i i' : B1WIndex ι h Nw m Ks) (y : Vec 2) :
    b1wTestTransform F θ i i' r (fun y => star (cellComplexFourierMode n y)) y =
      cellComplexFourierMode (-n) y *
        b1wTestTransform F θ i i' r (fun y => 1 * cellComplexFourierMode (-n) y) 0 := by
  have e : (fun y => star (cellComplexFourierMode n y)) =
      fun y => 1 * cellComplexFourierMode (-n) y := by
    funext y; rw [star_cellComplexFourierMode, one_mul]
  rw [e, b1wTestTransform_mode F θ i i' r hr0 hq (-n) 1 y]
  ring

/-- **The forcing of a mode at a quiet good time.** -/
theorem quiet_forcing_identity {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (r : ℝ)
    (hr0 : ∀ z, F.v r z = 0)
    (hq : ∀ l, ∀ (v u : ι) (d : Finset.Icc 2 D), ∀ γ ∈ (F.letters l).edge v u d, ∀ α,
      ∀ X z z', γ.coeff α r X z = γ.coeff α r X z')
    (hπ : ∀ x, 0 < F.π x) (hϖ : 0 < F.ϖ) (Nd : ℕ) (n : Fin 2 → ℤ)
    (i0 : B1WIndex ι h Nw m Ks)
    (W S : B1WIndex ι h Nw m Ks → ComplexCellL2)
    (Fl : B1WIndex ι h Nw m Ks → Fin 2 → ComplexCellL2)
    (hS : ∀ i, (S i : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun y => b1wScale F.π F.ϖ F.ηg F.letters i *
        amplitudeIdLiteralSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r y)
    (hF : ∀ i j, (Fl i j : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun y => b1wScale F.π F.ϖ F.ηg F.letters i *
        amplitudeIdLiteralFlux F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r y j)
    (hW : ∀ i', (W i' : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun y => b1wScale F.π F.ϖ F.ηg F.letters i' * b1wStageVal F θ i' r y)
    (hExp : ∀ i : B1WIndex ι h Nw m Ks, ∀ φ : Vec 2 → ℂ, ContDiff ℝ Nd φ →
      AVenhance.IsZ2Periodic φ →
      b1wTestedSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r φ =
        ∑ i' : B1WIndex ι h Nw m Ks, ∫ y in AVenhance.unitCube,
          b1wStageVal F θ i' r y * b1wTestTransform F θ i i' r φ y)
    (hearly : ∀ i i' : B1WIndex ι h Nw m Ks, ¬ b1wSt i' < b1wSt i → ∀ φ : Vec 2 → ℂ,
      b1wTestTransform F θ i i' r φ = 0) :
    quietModeForcing θ n (S i0) (Fl i0) =
      ∑ i', quietTau F θ n r i0 i' * cellFourierCoeff (W i' : Vec 2 → ℂ) n := by
  classical
  set k := b1wSt i0 with hk
  have hi0 : i0 ∈ stageSet b1wSt k := by simp [stageSet, hk]
  set σ : B1WIndex ι h Nw m Ks → ℂ := fun i' =>
    b1wTestTransform F θ i0 i' r (fun y => 1 * cellComplexFourierMode (-n) y) 0 with hσ
  set ψ : B1WIndex ι h Nw m Ks → Vec 2 → ℂ := fun i y =>
    if i = i0 then cellComplexFourierMode n y else 0 with hψ
  set z : B1WIndex ι h Nw m Ks → TorusHk 1 ℂ := fun i =>
    if i = i0 then cellComplexFourierModeH1 n else 0 with hz
  set ρ : B1WIndex ι h Nw m Ks → ℂ := fun i' => b1wScaleRatio F.π F.ϖ F.ηg F.letters i0 i' with hρ
  have hρs : ∀ i', star (ρ i') = ρ i' := fun i' => b1wScaleRatio_star _ _ _ _ _ _
  have hmodeC : ∀ m : Fin 2 → ℤ, ContDiff ℝ Nd (cellComplexFourierMode m) := fun m =>
    (cellComplexFourierMode_contDiff m).of_le (by exact_mod_cast le_top)
  have hψc : ∀ i, ContDiff ℝ 1 (ψ i) := by
    intro i
    by_cases hi : i = i0
    · simp only [hψ, hi, ite_true]
      exact (cellComplexFourierMode_contDiff n).of_le (by exact_mod_cast le_top)
    · simp only [hψ, hi, ite_false]; exact contDiff_const
  have hzψ : ∀ i ∈ stageSet b1wSt k, (torusHkValueCLM (z i) : Vec 2 → ℂ)
      =ᵐ[volume.restrict AVenhance.unitCube] ψ i := by
    intro i _
    by_cases hi : i = i0
    · simp only [hz, hψ, hi, ite_true]
      exact cellComplexFourierModeH1_value_ae n
    · simp only [hz, hψ, hi, ite_false, map_zero]
      exact Lp.coeFn_zero ℂ 2 _
  have hstar0 : (fun y : Vec 2 => star ((0 : ℂ))) = fun _ => 0 := by funext y; simp
  have hExp' : ∀ i ∈ stageSet b1wSt k,
      b1wTestedSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r (fun y => star (ψ i y)) =
        ∑ i' : B1WIndex ι h Nw m Ks, ∫ y in AVenhance.unitCube,
          b1wStageVal F θ i' r y * b1wTestTransform F θ i i' r (fun y => star (ψ i y)) y := by
    intro i _
    refine hExp i _ ?_ ?_
    · by_cases hi : i = i0
      · simp only [hψ, hi, ite_true]
        have : (fun y => star (cellComplexFourierMode n y)) = cellComplexFourierMode (-n) := by
          funext y; rw [star_cellComplexFourierMode]
        rw [this]; exact hmodeC _
      · simp only [hψ, hi, ite_false, star_zero]; exact contDiff_const
    · by_cases hi : i = i0
      · simp only [hψ, hi, ite_true]
        have : (fun y => star (cellComplexFourierMode n y)) = cellComplexFourierMode (-n) := by
          funext y; rw [star_cellComplexFourierMode]
        rw [this]; exact mode_periodic _
      · simp only [hψ, hi, ite_false, star_zero]; intro nn x; rfl
  have hTi : ∀ i', b1wTestTransform F θ i0 i' r (fun y => star (ψ i0 y)) =
      fun y => cellComplexFourierMode (-n) y * σ i' := by
    intro i'; funext y
    simp only [hψ, ite_true]
    rw [quiet_transform_star_mode F θ r hr0 hq]
  have hTo : ∀ i i', i ≠ i0 → b1wTestTransform F θ i i' r (fun y => star (ψ i y)) = 0 := by
    intro i i' hi
    have : (fun y => star (ψ i y)) = fun _ => 0 := by
      funext y; simp [hψ, hi]
    rw [this]; exact b1wTestTransform_zero_test F θ i i' r
  set Φ : B1WIndex ι h Nw m Ks → ComplexCellL2 := fun i' =>
    (ρ i' * star (σ i')) • scalarTorusToCell (UnitAddTorus.mFourierLp 2 n) with hΦdef
  have hΦ : ∀ i', b1wSt i' < k → (Φ i' : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun y => ∑ i ∈ stageSet b1wSt k, b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
        star (b1wTestTransform F θ i i' r (fun y => star (ψ i y)) y) := by
    intro i' _
    have hsum : ∀ y, ∑ i ∈ stageSet b1wSt k, b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
        star (b1wTestTransform F θ i i' r (fun y => star (ψ i y)) y) =
        ρ i' * star (σ i') * cellComplexFourierMode n y := by
      intro y
      rw [Finset.sum_eq_single_of_mem i0 hi0]
      · rw [hTi]
        simp only [star_mul', star_cellComplexFourierMode, neg_neg]
        rw [hρ]; ring
      · intro i _ hi
        rw [hTo i i' hi]; simp
    rw [hΦdef, scalarTorusToCell_mode]
    filter_upwards [Lp.coeFn_smul (ρ i' * star (σ i'))
      ((cellComplexFourierMode_memLp n).toLp (cellComplexFourierMode n)),
      (cellComplexFourierMode_memLp n).coeFn_toLp] with y h1 h2
    rw [h1, Pi.smul_apply, h2, smul_eq_mul, hsum y]
  have hint : ∀ i ∈ stageSet b1wSt k, ∀ i', b1wSt i' < k →
      Integrable (fun y => b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' * (W i' y *
        b1wTestTransform F θ i i' r (fun y => star (ψ i y)) y))
        (volume.restrict AVenhance.unitCube) := by
    intro i _ i' _
    by_cases hi : i = i0
    · subst hi
      have hpair := cellComplex_pairing_integrable (W i') (scalarTorusToCell (UnitAddTorus.mFourierLp 2 n))
      refine (hpair.const_mul (ρ i' * σ i')).congr ?_
      rw [scalarTorusToCell_mode]
      filter_upwards [(cellComplexFourierMode_memLp n).coeFn_toLp] with y hy
      rw [hTi, hy, star_cellComplexFourierMode]
      simp only [hρ]
      ring
    · simp only [hTo i i' hi, Pi.zero_apply, mul_zero]
      exact integrable_zero _ _ _
  have hrep := b1w_stage_representation F θ r k hπ hϖ W S Fl z ψ (fun i _ => hψc i) hzψ
    (fun i _ => hS i) (fun i _ j => hF i j) hExp' (fun i hi i' hi' => hearly i i' (by rw [(Finset.mem_filter.1 hi).2]; exact hi') _) hW hint Φ hΦ
  have hL : ∑ i ∈ stageSet b1wSt k, cellComplexSource (fun j => ((θ j : ℝ) : ℂ)) (S i) (Fl i)
      (z i) = quietModeForcing θ n (S i0) (Fl i0) := by
    rw [Finset.sum_eq_single_of_mem i0 hi0]
    · simp only [hz, ite_true]
      exact quietFourier_sourceS θ n (S i0) (Fl i0)
    · intro i _ hi
      simp only [hz, hi, ite_false]
      exact cellComplexSource_zero_test _ _ _
  rw [hL] at hrep
  rw [hrep, sum_eq_sum_stages b1wSt k (fun i' => quietTau F θ n r i0 i' *
    cellFourierCoeff (W i' : Vec 2 → ℂ) n) (fun i' hi' => by
      rw [quietTau_zero F θ n r i0 i' hi', zero_mul])]
  refine Finset.sum_congr rfl fun k' hk' => Finset.sum_congr rfl fun i' hi' => ?_
  have hst : b1wSt i' < k := by
    rw [(Finset.mem_filter.1 hi').2]; exact Finset.mem_range.1 hk'
  rw [hΦdef, pair_mode]
  have : star (ρ i' * star (σ i')) = ρ i' * σ i' := by
    rw [star_mul', star_star, hρs]
  rw [this]
  have hst' : b1wSt i' < b1wSt i0 := hst
  simp only [quietTau, hst', ↓reduceIte]
  rfl

end Force

end AVRegularity.CycleWords.Discard
end
end

section
/-! # `PlaneStatement` from its scalar form

The cutoff `μ(D)` is a convolution with a Schwartz kernel, so `μ(D)U` is smooth and commutes with
the coordinates of `U` along an orthonormal basis; the jets of a coordinate are the coordinates of
the jets. Hence the vector statement follows from `ScalarStatement` (one real component, one
derivative word), with the constant multiplied by `2^{K_f}` (the number of words). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity AVRegularity.Sobolev AVRegularity.CycleWords
  AVRegularity.CycleWords.Assembly AVRegularity.CycleWords.Discard
open AVRegularity.CoupledEnergyPlane AVRegularity.CycleWords.Seam AVRegularity.Analysis.Convolution
open scoped ENNReal

namespace AVRegularity.CycleWords.Discard

universe v

theorem fourierCutoff_eq_conv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Vec 2 → ℝ) (R : ℝ) (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → μ ξ = 0)
    (hs : ContDiff ℝ (⊤ : ℕ∞) μ) (g : Vec 2 → E) :
    fourierCutoff μ g = schwartzConvolution (seamRealCutoffSchwartz μ R hm hs) g := by
  funext y
  unfold fourierCutoff schwartzConvolution
  rw [← seamRealCutoffSchwartz_eq μ R hm hs]
  set k := seamRealCutoffSchwartz μ R hm hs
  calc ∫ x, k x • g (y - x) = ∫ x, (fun x => k (y - x) • g x) (y - x) := by
        simp [sub_sub_cancel]
    _ = _ := integral_sub_left_eq_self (fun x => k (y - x) • g x) volume y

theorem fourierCutoff_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Vec 2 → ℝ) (hs : ContDiff ℝ (⊤ : ℕ∞) μ) (hμc : HasCompactSupport μ) {g : Vec 2 → E}
    (hg : Integrable g) : ContDiff ℝ (⊤ : ℕ∞) (fourierCutoff μ g) := by
  obtain ⟨R, hR⟩ := radius' μ hμc
  rw [fourierCutoff_eq_conv μ R hR hs]
  exact schwartzConvolution_contDiff _ _ hg

theorem jetOrder_coord_ae {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] (e : E) {K : ℕ}
    (u : PlaneHk Set.univ K E) (a : ℕ) (w : DerivativeWord2 a) :
    planeJetOrder (planeHkCoord e u) a w =ᵐ[volume]
      fun z => inner ℝ e (planeJetOrder u a w z) := by
  by_cases ha : a ≤ K
  · have h := (ae_restrict_iff' MeasurableSet.univ).mp
      ((InnerProductSpace.toDual ℝ E e).coeFn_compLpL (μ := volume.restrict Set.univ)
        (u.val ⟨⟨a, Nat.lt_succ_of_le ha⟩, w⟩))
    filter_upwards [h] with z hz
    simp only [planeJetOrder, ha, dite_true]
    change ((planeHkCoord e u).val ⟨⟨a, Nat.lt_succ_of_le ha⟩, w⟩ : Vec 2 → ℝ) z =
      inner ℝ e ((u.val ⟨⟨a, Nat.lt_succ_of_le ha⟩, w⟩ : Vec 2 → E) z)
    rw [planeHkCoord, mapPlaneHk_component, hz (Set.mem_univ z)]
    rfl
  · refine Filter.Eventually.of_forall fun z => ?_
    simp only [planeJetOrder, ha, dite_false, inner_zero_right]

theorem sum_inner_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : Type*} [Fintype n] (B : OrthonormalBasis n ℝ E) (y : E) :
    ∑ e, inner ℝ (B e) y ^ 2 = ‖y‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← B.sum_inner_mul_inner y y]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [sq, real_inner_comm (B e) y]

theorem fourierCutoff_congr_ae' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : Vec 2 → ℝ) {g₁ g₂ : Vec 2 → E} (h : g₁ =ᵐ[volume] g₂) :
    fourierCutoff m g₁ = fourierCutoff m g₂ := by
  funext y
  unfold fourierCutoff
  apply integral_congr_ae
  have ht : (fun x : Vec 2 => g₁ (y - x)) =ᵐ[volume] fun x => g₂ (y - x) :=
    ((volume : Measure (Vec 2)).measurePreserving_sub_left y).quasiMeasurePreserving.ae_eq_comp h
  filter_upwards [ht] with x hx
  rw [hx]

theorem foldl_comp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (l : List (Fin 2)) :
    ∀ {G : Vec 2 → E}, ContDiff ℝ (⊤ : ℕ∞) G →
      l.foldl (fun g' i => fun x => fderiv ℝ g' x (basisVec i)) (fun x => L (G x)) =
        fun x => L (l.foldl (fun g' i => fun x => fderiv ℝ g' x (basisVec i)) G x) := by
  induction l with
  | nil => intro G _; rfl
  | cons i t ih =>
    intro G hG
    simp only [List.foldl_cons]
    have hstep : (fun x => fderiv ℝ (fun x => L (G x)) x (basisVec i)) =
        fun x => L (fderiv ℝ G x (basisVec i)) := by
      funext x
      have := (L.hasFDerivAt.comp x (hG.differentiable (by simp) x).hasFDerivAt).fderiv
      change (fderiv ℝ (L ∘ G) x) (basisVec i) = _
      rw [this]
      rfl
    rw [hstep]
    exact ih ((hG.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const)

theorem orderedDerivative_comp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) {a : ℕ} (w : DerivativeWord2 a)
    {G : Vec 2 → E} (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    orderedDerivative w (fun x => L (G x)) = fun x => L (orderedDerivative w G x) :=
  foldl_comp L _ hG

theorem fourierCutoff_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (μ : Vec 2 → ℝ) (hs : ContDiff ℝ (⊤ : ℕ∞) μ) (hμc : HasCompactSupport μ) {g : Vec 2 → E}
    (hg : Integrable g) (e : E) (z : Vec 2) :
    fourierCutoff μ (fun y => inner ℝ e (g y)) z = inner ℝ e (fourierCutoff μ g z) := by
  obtain ⟨R, hR⟩ := radius' μ hμc
  rw [fourierCutoff_eq_conv μ R hR hs, fourierCutoff_eq_conv μ R hR hs]
  unfold schwartzConvolution
  have hi := schwartzConvolution_integrable (seamRealCutoffSchwartz μ R hR hs) g hg z
  have h := (innerSL ℝ e).integral_comp_comm hi
  simp only [innerSL_apply_apply, inner_smul_right] at h
  simpa using h

theorem Ft_congr_ae {g₁ g₂ : Vec 2 → ℝ} (h : g₁ =ᵐ[volume] g₂) : planeTransform g₁ = planeTransform g₂ := by
  funext ξ
  unfold planeTransform
  refine integral_congr_ae ?_
  filter_upwards [h] with y hy
  rw [hy]

theorem Band_congr_ae (k : ℕ) (ρ : ℝ) {g₁ g₂ : Vec 2 → ℝ} (h : g₁ =ᵐ[volume] g₂) :
    BandIntegrand k ρ g₁ = BandIntegrand k ρ g₂ := by
  unfold BandIntegrand
  rw [Ft_congr_ae h]

/-- The scalar (real-valued) form of `PlaneStatement`, one derivative word at a time. -/
def ScalarStatement : Prop :=
  ∀ (Kf m : ℕ) (ρ Bμ : ℝ), 0 ≤ ρ → 0 ≤ Bμ → ∃ C : ℝ, 0 < C ∧
  ∀ (μ : Vec 2 → ℝ), ContDiff ℝ (⊤ : ℕ∞) μ → HasCompactSupport μ → (∀ θ, μ (-θ) = μ θ) →
    (∀ (l : ℕ) θ, l ≤ m + Kf → ‖iteratedFDeriv ℝ l μ θ‖ ≤ Bμ) →
    (∀ θ, vecDot θ θ < ρ ^ 2 → μ θ = 1) →
  ∀ (κ : ℕ), Kf ≤ κ → ∀ u : PlaneHk Set.univ κ ℝ,
    (∀ β ∈ momentIndices m,
      Integrable (fun y : Vec 2 => (y 0 ^ β.1 * y 1 ^ β.2) • planeValue u y)) →
  ∀ β ∈ momentIndices m, ∀ a ≤ Kf, ∀ w : DerivativeWord2 a,
    ∫⁻ z, ENNReal.ofReal (momentWeight β z ^ 2 *
        (planeJetOrder u a w z - orderedDerivative w (fourierCutoff μ (planeValue u)) z) ^ 2) ≤
      ENNReal.ofReal C *
        ∑ β' ∈ (momentIndices m).filter (fun β' => β'.1 ≤ β.1 ∧ β'.2 ≤ β.2),
          ∫⁻ ξ, BandIntegrand Kf ρ (fun y => momentWeight β' y * planeValue u y) ξ

theorem plane_of_scalar (hS : ScalarStatement) : PlaneStatement.{v} := by
  intro Kf m ρ Bμ hρ hBμ
  obtain ⟨C, hC, hCS⟩ := hS Kf m ρ Bμ hρ hBμ
  refine ⟨2 ^ Kf * C, by positivity, ?_⟩
  intro E _ _ _ _ _ _ μ hμ hμc hμe hμB hμ1 κ hκ U hmom β hβ a ha
  have hg1 : Integrable (planeValue U) := by
    have := hmom (0, 0) (by unfold momentIndices; simp)
    simpa using this
  set e : Fin (Module.finrank ℝ E) → E := fun b => stdOrthonormalBasis ℝ E b with he
  set J : DerivativeWord2 a → Vec 2 → E := fun w z =>
    planeJetOrder U a w z - orderedDerivative w (fourierCutoff μ (planeValue U)) z with hJ
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fourierCutoff μ (planeValue U)) :=
    fourierCutoff_contDiff μ hμ hμc hg1
  -- the scalar difference of a coordinate
  have hcoord : ∀ (b : Fin (Module.finrank ℝ E)) (w : DerivativeWord2 a),
      (fun z => planeJetOrder (planeHkCoord (e b) U) a w z -
        orderedDerivative w (fourierCutoff μ (planeValue (planeHkCoord (e b) U))) z)
        =ᵐ[volume] fun z => inner ℝ (e b) (J w z) := by
    intro b w
    have h1 := jetOrder_coord_ae (e b) U a w
    have h0 : planeValue (planeHkCoord (e b) U) =ᵐ[volume] fun z => inner ℝ (e b) (planeValue U z) :=
      jetOrder_coord_ae (e b) U 0 _
    have h2 : fourierCutoff μ (planeValue (planeHkCoord (e b) U)) =
        fun z => inner ℝ (e b) (fourierCutoff μ (planeValue U) z) := by
      rw [fourierCutoff_congr_ae' μ h0]
      funext z
      exact fourierCutoff_inner μ hμ hμc hg1 (e b) z
    have h3 := orderedDerivative_comp (innerSL ℝ (e b)) w hsm
    filter_upwards [h1] with z hz
    rw [hz, h2]
    have := congrFun h3 z
    simp only [innerSL_apply_apply] at this
    simp only [hJ, inner_sub_right]
    rw [this]
  have hmeas : ∀ (b : Fin (Module.finrank ℝ E)) (w : DerivativeWord2 a),
      AEMeasurable (fun z => ENNReal.ofReal (momentWeight β z ^ 2 *
        (planeJetOrder (planeHkCoord (e b) U) a w z -
          orderedDerivative w (fourierCutoff μ (planeValue (planeHkCoord (e b) U))) z) ^ 2))
        volume := by
    intro b w
    have h1 := jetDiff_aestronglyMeasurable μ hμ hμc (planeHkCoord (e b) U) a w
    have h2 : AEMeasurable (fun z : Vec 2 => momentWeight β z ^ 2) volume := by
      unfold momentWeight
      exact (by fun_prop : Measurable fun z : Vec 2 => (z 0 ^ β.1 * z 1 ^ β.2) ^ 2).aemeasurable
    exact (h2.mul (h1.aemeasurable.pow_const 2)).ennreal_ofReal
  have hband : ∀ (b : Fin (Module.finrank ℝ E)) (β' : ℕ × ℕ),
      BandIntegrand Kf ρ (fun y => momentWeight β' y *
        planeValue (planeHkCoord (e b) U) y) =
      BandIntegrand Kf ρ (fun y => momentWeight β' y *
        inner ℝ (stdOrthonormalBasis ℝ E b) (planeValue U y)) := by
    intro b β'
    have h0 : planeValue (planeHkCoord (e b) U) =ᵐ[volume]
        fun z => inner ℝ (e b) (planeValue U z) := jetOrder_coord_ae (e b) U 0 _
    refine Band_congr_ae Kf ρ ?_
    filter_upwards [h0] with y hy
    rw [hy]
  have hmomc : ∀ (b : Fin (Module.finrank ℝ E)), ∀ β' ∈ momentIndices m,
      Integrable (fun y : Vec 2 => (y 0 ^ β'.1 * y 1 ^ β'.2) •
        planeValue (planeHkCoord (e b) U) y) := by
    intro b β' hβ'
    have h0 : planeValue (planeHkCoord (e b) U) =ᵐ[volume]
        fun z => inner ℝ (e b) (planeValue U z) := jetOrder_coord_ae (e b) U 0 _
    refine ((innerSL ℝ (e b)).integrable_comp (hmom β' hβ')).congr ?_
    filter_upwards [h0] with y hy
    simp [hy]
  set dd : Fin (Module.finrank ℝ E) → DerivativeWord2 a → Vec 2 → ℝ := fun b w z =>
    planeJetOrder (planeHkCoord (e b) U) a w z -
      orderedDerivative w (fourierCutoff μ (planeValue (planeHkCoord (e b) U))) z with hdd
  have hpt : ∀ᵐ z ∂(volume : Measure (Vec 2)), ENNReal.ofReal (momentWeight β z ^ 2 *
      ∑ w : DerivativeWord2 a, ‖planeJetOrder U a w z -
        orderedDerivative w (fourierCutoff μ (planeValue U)) z‖ ^ 2) =
      ∑ w : DerivativeWord2 a, ∑ b : Fin (Module.finrank ℝ E),
        ENNReal.ofReal (momentWeight β z ^ 2 * dd b w z ^ 2) := by
    have hall := ae_all_iff.2 (fun w : DerivativeWord2 a => ae_all_iff.2
      (fun b : Fin (Module.finrank ℝ E) => hcoord b w))
    filter_upwards [hall] with z hz
    have hsum : ∑ w : DerivativeWord2 a, ‖planeJetOrder U a w z -
        orderedDerivative w (fourierCutoff μ (planeValue U)) z‖ ^ 2 =
        ∑ w : DerivativeWord2 a, ∑ b : Fin (Module.finrank ℝ E), dd b w z ^ 2 := by
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [← sum_inner_sq (stdOrthonormalBasis ℝ E) (J w z)]
      exact Finset.sum_congr rfl fun b _ => by rw [← hz w b]
    rw [hsum, Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun w _ => by positivity)]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun b _ => by positivity)]
  have hwc : Fintype.card (DerivativeWord2 a) = 2 ^ a := by
    simp [DerivativeWord2]
  calc _ = ∫⁻ z, ∑ w : DerivativeWord2 a, ∑ b : Fin (Module.finrank ℝ E),
        ENNReal.ofReal (momentWeight β z ^ 2 * dd b w z ^ 2) := lintegral_congr_ae hpt
    _ = ∑ w : DerivativeWord2 a, ∑ b : Fin (Module.finrank ℝ E),
        ∫⁻ z, ENNReal.ofReal (momentWeight β z ^ 2 * dd b w z ^ 2) := by
        rw [lintegral_finsetSum']
        · refine Finset.sum_congr rfl fun w _ => ?_
          rw [lintegral_finsetSum']
          exact fun b _ => hmeas b w
        · exact fun w _ => Finset.aemeasurable_fun_sum _ fun b _ => hmeas b w
    _ ≤ ∑ w : DerivativeWord2 a, ∑ b : Fin (Module.finrank ℝ E),
        ENNReal.ofReal C * ∑ β' ∈ (momentIndices m).filter
          (fun β' => β'.1 ≤ β.1 ∧ β'.2 ≤ β.2), ∫⁻ ξ, BandIntegrand Kf ρ
            (fun y => momentWeight β' y * inner ℝ (stdOrthonormalBasis ℝ E b) (planeValue U y)) ξ := by
        refine Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun b _ => ?_
        refine (hCS μ hμ hμc hμe hμB hμ1 κ hκ (planeHkCoord (e b) U) (hmomc b) β hβ a ha w).trans ?_
        simp_rw [hband]
        exact le_rfl
    _ = ENNReal.ofReal C * (2 ^ a : ℝ≥0∞) * ∑ β' ∈ (momentIndices m).filter
          (fun β' => β'.1 ≤ β.1 ∧ β'.2 ≤ β.2), ∑ b : Fin (Module.finrank ℝ E),
          ∫⁻ ξ, BandIntegrand Kf ρ
            (fun y => momentWeight β' y * inner ℝ (stdOrthonormalBasis ℝ E b) (planeValue U y)) ξ := by
        simp_rw [← Finset.mul_sum]
        rw [Finset.sum_const, Finset.card_univ, hwc, Finset.sum_comm]
        simp [nsmul_eq_mul, Finset.mul_sum, mul_assoc]
    _ ≤ _ := by
        have h2 : (2 : ℝ≥0∞) ^ a ≤ 2 ^ Kf := pow_le_pow_right₀ (by norm_num) ha
        have h3 : ENNReal.ofReal C * (2 : ℝ≥0∞) ^ a ≤ ENNReal.ofReal (2 ^ Kf * C) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
            ENNReal.ofReal_ofNat, mul_comm (ENNReal.ofReal C)]
          gcongr
        exact mul_le_mul' h3 le_rfl

end AVRegularity.CycleWords.Discard
end
end
end
