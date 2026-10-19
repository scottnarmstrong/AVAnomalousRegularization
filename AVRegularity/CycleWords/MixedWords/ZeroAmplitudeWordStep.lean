-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.MixedWords.FactorOfMomentsCutoffJets
public import AVRegularity.CycleWords.MixedWords.FactorOfMomentsRepresentation
import AVRegularity.CycleWords.FibreGraphNativeSeries
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleWords.MixedWords.AdjointExists
import AVRegularity.CycleWords.MixedWords.AmplitudeLimit
import AVRegularity.CycleWords.MixedWords.AmplitudePlancherel
import AVRegularity.CycleWords.MixedWords.BlochContinuity
public import AVRegularity.CycleWords.ConstructedActualWeakNativeGapDecay
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.CategoryTheory.Countable

section
section
/-! Finite weighted pair norms used to pass the cutoff span estimate to the Bloch cell. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set Filter Topology AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-- The square root of a finite sum is at most the sum of the square roots, including infinity. -/
theorem factorRoot_sum_le {κ : Type*} (s : Finset κ) (f : κ → ℝ≥0∞) :
    (∑ i ∈ s, f i) ^ (1 / 2 : ℝ) ≤ ∑ i ∈ s, (f i) ^ (1 / 2 : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    exact le_rfl
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (ENNReal.rpow_add_le_add_rpow _ _ (by norm_num) (by norm_num)).trans (add_le_add le_rfl ih)

/-- Cell norm of a finite weighted family of real pairs. -/
def factorCellPairNorm {X ι : Type*} [MeasurableSpace X] [Fintype ι] (μ : Measure X) (π : ι → ℝ)
    (A B : ι → X → ℝ) : ℝ≥0∞ :=
  (∫⁻ z, ∑ x, ENNReal.ofReal ((π x)⁻¹) *
    (ENNReal.ofReal ((A x z) ^ 2) + ENNReal.ofReal ((B x z) ^ 2)) ∂μ) ^ (1 / 2 : ℝ)

/-- Scaling a pair scales its cell norm by the absolute value of the scalar. -/
theorem factorCellPairNorm_smul {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (π : ι → ℝ) (A B : ι → X → ℝ) (c : ℝ) :
    factorCellPairNorm μ π (fun x z => c * A x z) (fun x z => c * B x z) =
      ENNReal.ofReal |c| * factorCellPairNorm μ π A B := by
  have he : (fun z => ∑ x, ENNReal.ofReal ((π x)⁻¹) *
      (ENNReal.ofReal ((c * A x z) ^ 2) + ENNReal.ofReal ((c * B x z) ^ 2))) =
      fun z => ENNReal.ofReal |c| ^ 2 * ∑ x, ENNReal.ofReal ((π x)⁻¹) *
        (ENNReal.ofReal ((A x z) ^ 2) + ENNReal.ofReal ((B x z) ^ 2)) := by
    funext z
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    simp only [mul_pow, ENNReal.ofReal_mul (sq_nonneg _), sq_abs,
      ← ENNReal.ofReal_pow (abs_nonneg _)]
    ring
  unfold factorCellPairNorm
  rw [he, lintegral_const_mul' _ _ ((ENNReal.pow_lt_top ENNReal.ofReal_lt_top).ne),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), sq_rpow_half]

/-- A finite pointwise pair majorant gives a cell norm bound with an order-only loss. -/
theorem factorCellPairNorm_sum_le {X ι κ : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (π : ι → ℝ) (s : Finset κ) (c : κ → ℝ)
    (hc : ∀ a ∈ s, 0 ≤ c a) (A B : ι → X → ℝ) (P Q : κ → ι → X → ℝ)
    (hA : ∀ x z, 0 ≤ A x z) (hB : ∀ x z, 0 ≤ B x z)
    (hmP : ∀ a ∈ s, ∀ x, AEMeasurable (P a x) μ)
    (hmQ : ∀ a ∈ s, ∀ x, AEMeasurable (Q a x) μ)
    (hAP : ∀ᵐ z ∂μ, ∀ x, A x z ≤ ∑ a ∈ s, c a * P a x z)
    (hBQ : ∀ᵐ z ∂μ, ∀ x, B x z ≤ ∑ a ∈ s, c a * Q a x z) :
    factorCellPairNorm μ π A B ≤ (s.card : ℝ≥0∞) ^ (1 / 2 : ℝ) *
      ∑ a ∈ s, ENNReal.ofReal (c a) * factorCellPairNorm μ π (P a) (Q a) := by
  have hPt : ∀ᵐ z ∂μ, ∀ x, (A x z) ^ 2 + (B x z) ^ 2 ≤
      (s.card : ℝ) * ∑ a ∈ s, (c a) ^ 2 * ((P a x z) ^ 2 + (Q a x z) ^ 2) := by
    filter_upwards [hAP, hBQ] with z hAP hBQ
    intro x
    have hp := (pow_le_pow_left₀ (hA x z) (hAP x) 2).trans
      (sq_sum_le_card_mul_sum_sq (s := s) (f := fun a => c a * P a x z))
    have hq := (pow_le_pow_left₀ (hB x z) (hBQ x) 2).trans
      (sq_sum_le_card_mul_sum_sq (s := s) (f := fun a => c a * Q a x z))
    refine (add_le_add hp hq).trans_eq ?_
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hm (a : κ) (ha : a ∈ s) : AEMeasurable (fun z => ∑ x, ENNReal.ofReal ((π x)⁻¹) *
      (ENNReal.ofReal ((P a x z) ^ 2) + ENNReal.ofReal ((Q a x z) ^ 2))) μ :=
    by
      simpa only [Finset.sum_apply, Pi.mul_apply, Pi.add_apply] using
        Finset.aemeasurable_fun_sum Finset.univ (fun x _ =>
          (((hmP a ha x).pow_const 2).ennreal_ofReal.add
            ((hmQ a ha x).pow_const 2).ennreal_ofReal).const_mul (ENNReal.ofReal ((π x)⁻¹)))
  have hb : ∫⁻ z, ∑ x, ENNReal.ofReal ((π x)⁻¹) *
      (ENNReal.ofReal ((A x z) ^ 2) + ENNReal.ofReal ((B x z) ^ 2)) ∂μ ≤
        (s.card : ℝ≥0∞) * ∑ a ∈ s, ENNReal.ofReal (c a) ^ 2 *
          ∫⁻ z, ∑ x, ENNReal.ofReal ((π x)⁻¹) *
            (ENNReal.ofReal ((P a x z) ^ 2) + ENNReal.ofReal ((Q a x z) ^ 2)) ∂μ := by
    calc
      _ ≤ ∫⁻ z, (s.card : ℝ≥0∞) * ∑ a ∈ s, ENNReal.ofReal (c a) ^ 2 *
            ∑ x, ENNReal.ofReal ((π x)⁻¹) *
              (ENNReal.ofReal ((P a x z) ^ 2) + ENNReal.ofReal ((Q a x z) ^ 2)) ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [hPt] with z hz
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_le_sum
        intro x _
        have hp := ENNReal.ofReal_le_ofReal (hz x)
        rw [ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
          ENNReal.ofReal_sum_of_nonneg (fun a _ => by positivity)] at hp
        refine (mul_le_mul' le_rfl hp).trans_eq ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a ha
        rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
          ENNReal.ofReal_pow (hc a ha)]
        ring
      _ = _ := by
        rw [lintegral_const_mul' _ _ (by simp),
          lintegral_finsetSum' _ (fun a ha => (hm a ha).const_mul (ENNReal.ofReal (c a) ^ 2))]
        congr 1
        exact Finset.sum_congr rfl (fun a _ => lintegral_const_mul' _ _ ((ENNReal.pow_lt_top ENNReal.ofReal_lt_top).ne))
  refine (ENNReal.rpow_le_rpow hb (by norm_num)).trans ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  refine mul_le_mul' le_rfl ?_
  refine (factorRoot_sum_le s _).trans (le_of_eq ?_)
  apply Finset.sum_congr rfl
  intro a _
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), sq_rpow_half]
  rfl

private theorem factorParam_word_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ∀ {k : ℕ} (wd : DerivativeWord2 k) (F : Vec 2 × Vec 2 → E),
    ContDiff ℝ (⊤ : ℕ∞) F → ∃ G : Vec 2 × Vec 2 → E,
      ContDiff ℝ (⊤ : ℕ∞) G ∧ ∀ θ z, G (θ, z) = orderedDerivative wd (fun θ => F (θ, z)) θ
  | 0, wd, F, hF => ⟨F, hF, fun θ z => by rw [AVRegularity.orderedDerivative_zero]⟩
  | k + 1, wd, F, hF => by
    obtain ⟨G, hG, he⟩ := factorParam_word_contDiff (fun i : Fin k => wd i.castSucc) F hF
    let H : Vec 2 × Vec 2 → E := fun p => fderiv ℝ G p (basisVec (wd (Fin.last k)), 0)
    have hH : ContDiff ℝ (⊤ : ℕ∞) H :=
      (hG.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
    refine ⟨H, hH, fun θ z => ?_⟩
    rw [AVRegularity.orderedDerivative_succ]
    have heq : orderedDerivative (fun i : Fin k => wd i.castSucc) (fun θ => F (θ, z)) =
        fun θ => G (θ, z) := funext (fun θ => (he θ z).symm)
    rw [heq]
    have hp : HasFDerivAt (fun θ : Vec 2 => (θ, z))
        ((ContinuousLinearMap.id ℝ (Vec 2)).prod 0) θ := by
      simpa only [id_eq] using (hasFDerivAt_id θ).prodMk (hasFDerivAt_const z θ)
    have hg := (hG.differentiable (by simp) (θ, z)).hasFDerivAt.comp θ hp
    change HasFDerivAt (fun θ => G (θ, z)) _ θ at hg
    change fderiv ℝ G (θ, z) (basisVec (wd (Fin.last k)), 0) =
      fderiv ℝ (fun θ => G (θ, z)) θ (basisVec (wd (Fin.last k)))
    rw [hg.fderiv, ContinuousLinearMap.comp_apply]
    simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
      zero_apply]

/-- Partial frequency derivatives of compact Bloch data are measurable in the cell variable. -/
theorem factorBlochPartial_aemeasurable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : Vec 2 → E} (hφ : StronglyMeasurable φ) (hcφ : HasCompactSupport φ)
    {χ : Vec 2 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (a b : ℕ) (θ : Vec 2) :
    AEMeasurable (fun z => ‖thetaPartial a b (fun θ' => χ θ' • blochPhase ψ θ' φ z) θ‖)
      (volume.restrict AVenhance.unitCube) := by
  classical
  obtain ⟨R, hR, hsupport⟩ := exists_support_radius hcφ
  obtain ⟨N, hN⟩ := exists_nat_ge (R + 1)
  let F : Vec 2 × Vec 2 → (latticeBox N → ℝ) := fun p k =>
    χ p.1 * ψ (vecDot p.1 (p.2 + fun i => ((k : Fin 2 → ℤ) i : ℝ)))
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := by
    refine contDiff_pi.2 fun k => ?_
    apply (hχ.comp contDiff_fst).mul
    exact hψ.comp (by unfold vecDot; fun_prop)
  let T (z : Vec 2) : (latticeBox N → ℝ) →L[ℝ] E :=
    ∑ k : latticeBox N, (ContinuousLinearMap.proj k).smulRight
      (φ (z + fun i => ((k : Fin 2 → ℤ) i : ℝ)))
  have hT (z : Vec 2) (c : latticeBox N → ℝ) :
      T z c = ∑ k : latticeBox N, c k • φ (z + fun i => ((k : Fin 2 → ℤ) i : ℝ)) := by
    simp [T]
  let wd : DerivativeWord2 (a + b) := fun i => if (Fin.rev i : ℕ) < a then 0 else 1
  obtain ⟨G, hG, heG⟩ := factorParam_word_contDiff wd F hF
  have he (z : Vec 2) : G (θ, z) = thetaPartial a b (fun θ' => F (θ', z)) θ := by
    rw [heG]
    have hslice : ContDiff ℝ (a + b : ℕ∞) (fun θ' => F (θ', z)) :=
      (hF.comp (contDiff_id.prodMk contDiff_const)).of_le (by simp)
    rw [AVRegularity.orderedDerivative_eq_iteratedFDeriv wd hslice, thetaPartial_eq_sortedBasis]
    dsimp only
    congr 1
    funext i
    simp only [wd, Fin.rev_rev, sortedBasis]
  have hm : AEMeasurable (fun z => ‖T z (G (θ, z))‖) (volume.restrict AVenhance.unitCube) := by
    have hGc : Continuous fun z => G (θ, z) := hG.continuous.comp (continuous_const.prodMk continuous_id)
    have hs : StronglyMeasurable fun z => T z (G (θ, z)) := by
      simp only [hT]
      apply Finset.stronglyMeasurable_fun_sum
      intro k _
      have hk : Continuous fun z : Vec 2 => G (θ, z) k :=
        (continuous_apply k).comp hGc
      exact hk.stronglyMeasurable.smul
        (hφ.comp_measurable (measurable_id.add_const
          (fun i => ((k : Fin 2 → ℤ) i : ℝ) : Vec 2)))
    exact hs.norm.aemeasurable
  apply hm.congr
  have hcube : MeasurableSet AVenhance.unitCube := by
    unfold AVenhance.unitCube
    exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo)
  filter_upwards [ae_restrict_mem hcube] with z hz
  have hfun : (fun θ' => χ θ' • blochPhase ψ θ' φ z) = fun θ' => T z (F (θ', z)) := by
    funext θ'
    rw [blochPhase_eq_box ψ hsupport hN hz θ', hT, Finset.smul_sum, ← Finset.sum_coe_sort]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [F, smul_smul]
  have hslice : ContDiff ℝ (a + b : ℕ∞) (fun θ' => F (θ', z)) :=
    (hF.comp (contDiff_id.prodMk contDiff_const)).of_le (by simp)
  show ‖T z (G (θ, z))‖ = ‖thetaPartial a b (fun θ' => χ θ' • blochPhase ψ θ' φ z) θ‖
  rw [he, hfun, thetaPartial_eq_sortedBasis, thetaPartial_eq_sortedBasis]
  congr 1
  have := (T z).iteratedFDeriv_comp_left (hslice.contDiffAt (x := θ)) (le_refl ((a + b : ℕ) : WithTop ℕ∞))
  rw [show (fun θ' => T z (F (θ', z))) = (T z) ∘ (fun θ' => F (θ', z)) from rfl, this]
  rfl

/-- For compact data the Bloch sum is a finite smooth trigonometric sum at every cell point. -/
theorem factorBlochPhase_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : Vec 2 → E} (hcφ : HasCompactSupport φ) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {z : Vec 2} (hz : z ∈ AVenhance.unitCube) :
    ContDiff ℝ (⊤ : ℕ∞) (fun θ => blochPhase ψ θ φ z) := by
  obtain ⟨R, _, hsupport⟩ := exists_support_radius hcφ
  obtain ⟨N, hN⟩ := exists_nat_ge (R + 1)
  have he : (fun θ => blochPhase ψ θ φ z) = fun θ => ∑ k ∈ latticeBox N,
      ψ (vecDot θ (z + fun i => (k i : ℝ))) • φ (z + fun i => (k i : ℝ)) := by
    funext θ
    exact blochPhase_eq_box ψ hsupport hN hz θ
  rw [he]
  apply ContDiff.sum
  intro k _
  exact (hψ.comp (by unfold vecDot; fun_prop)).smul contDiff_const

/-- The cutoff span estimate passes through the weighted Bloch cell norm. -/
theorem factorBlochSpan_raw (n : ℕ) {H : ℝ} (hH : 1 ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ x, NormedAddCommGroup (h x)] [∀ x, NormedSpace ℝ (h x)]
    (π : ι → ℝ) (φ : ∀ x, Vec 2 → h x),
    (∀ x, StronglyMeasurable (φ x) ∧ HasCompactSupport (φ x)) →
    ∀ (χ : Vec 2 → ℝ), ContDiff ℝ (⊤ : ℕ∞) χ → ∀ θ {w : ℝ}, 0 < w →
    |χ θ| ≤ H → (∀ i ≤ n, w ^ i * ‖iteratedFDeriv ℝ i χ θ‖ ≤ H) →
    ∀ β : ℕ × ℕ, β.1 + β.2 ≤ n →
    ENNReal.ofReal (w ^ (β.1 + β.2) * |χ θ| ^ (n + 1)) *
        blochFibreDerivNorm π (fun _ => 1) β φ θ ≤
      ((momentIndices n).card : ℝ≥0∞) ^ (1 / 2 : ℝ) * ENNReal.ofReal C *
        ∑ α ∈ momentIndices n, ENNReal.ofReal (w ^ (α.1 + α.2)) *
          blochFibreDerivNorm π χ α φ θ := by
  obtain ⟨C, hC, hs⟩ := factorCutoffSpan_partials n hH
  refine ⟨C, hC, ?_⟩
  intro ι _ h _ _ π φ hφ χ hχ θ w hw hval hjet β hβ
  let T (ψ : ℝ → ℝ) (α : ℕ × ℕ) (x : ι) (z : Vec 2) : ℝ :=
    ‖thetaPartial α.1 α.2 (fun θ' => blochPhase ψ θ' (φ x) z) θ‖
  let R (ψ : ℝ → ℝ) (α : ℕ × ℕ) (x : ι) (z : Vec 2) : ℝ :=
    ‖thetaPartial α.1 α.2 (fun θ' => χ θ' • blochPhase ψ θ' (φ x) z) θ‖
  let a : ℝ := w ^ (β.1 + β.2) * |χ θ| ^ (n + 1)
  have hcube : MeasurableSet AVenhance.unitCube := by
    unfold AVenhance.unitCube
    exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioo)
  have hb (ψ : ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
      ∀ᵐ z ∂volume.restrict AVenhance.unitCube, ∀ x,
      a * T ψ β x z ≤ ∑ α ∈ momentIndices n,
        (C * w ^ (α.1 + α.2)) * R ψ α x z := by
    filter_upwards [ae_restrict_mem hcube] with z hz
    intro x
    have hf := factorBlochPhase_contDiff (hφ x).2 hψ hz
    have hp := hs χ (fun θ' => blochPhase ψ θ' (φ x) z) hχ hf θ hw hval hjet
      (β.1 + β.2) hβ
    refine (mul_le_mul_of_nonneg_left (norm_thetaPartial_le β.1 β.2 _ θ)
      (by dsimp [a]; positivity)).trans (hp.trans_eq ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by dsimp [R]; ring)
  have hn := factorCellPairNorm_sum_le (volume.restrict AVenhance.unitCube) π (momentIndices n)
    (fun α => C * w ^ (α.1 + α.2)) (fun α _ => by positivity)
    (fun x z => a * T Real.cos β x z) (fun x z => a * T Real.sin β x z)
    (R Real.cos) (R Real.sin)
    (fun x z => by dsimp [a, T]; positivity) (fun x z => by dsimp [a, T]; positivity)
    (fun α _ x => factorBlochPartial_aemeasurable (hφ x).1 (hφ x).2 hχ
      Real.contDiff_cos α.1 α.2 θ)
    (fun α _ x => factorBlochPartial_aemeasurable (hφ x).1 (hφ x).2 hχ
      Real.contDiff_sin α.1 α.2 θ)
    (hb Real.cos Real.contDiff_cos) (hb Real.sin Real.contDiff_sin)
  rw [factorCellPairNorm_smul, abs_of_nonneg (by dsimp [a]; positivity)] at hn
  have he0 : factorCellPairNorm (volume.restrict AVenhance.unitCube) π (T Real.cos β) (T Real.sin β) =
      blochFibreDerivNorm π (fun _ => 1) β φ θ := by
    simp only [factorCellPairNorm, blochFibreDerivNorm, T, blochCos, blochSin, blochPhase, one_smul]
  have he (α : ℕ × ℕ) :
      factorCellPairNorm (volume.restrict AVenhance.unitCube) π (R Real.cos α) (R Real.sin α) =
        blochFibreDerivNorm π χ α φ θ := rfl
  rw [he0] at hn
  refine hn.trans_eq ?_
  simp only [he, ENNReal.ofReal_mul hC.le, Finset.mul_sum, mul_assoc]

/-- The Bloch span bound with the factorial normalization used in the statement. -/
theorem factorBlochSpan (n : ℕ) {H : ℝ} (hH : 1 ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ x, NormedAddCommGroup (h x)] [∀ x, NormedSpace ℝ (h x)]
    (π : ι → ℝ) (φ : ∀ x, Vec 2 → h x),
    (∀ x, StronglyMeasurable (φ x) ∧ HasCompactSupport (φ x)) →
    ∀ (χ : Vec 2 → ℝ), ContDiff ℝ (⊤ : ℕ∞) χ → ∀ θ {w : ℝ}, 0 < w →
    |χ θ| ≤ H → (∀ i ≤ n, w ^ i * ‖iteratedFDeriv ℝ i χ θ‖ ≤ H) →
    ENNReal.ofReal (|χ θ| ^ (n + 1)) * datumJets π w n φ θ ≤
      ENNReal.ofReal C * ∑ α ∈ momentIndices n,
        ENNReal.ofReal (w ^ (α.1 + α.2) / ((α.1.factorial * α.2.factorial : ℕ) : ℝ)) *
          blochFibreDerivNorm π χ α φ θ := by
  obtain ⟨C, hC, hb⟩ := factorBlochSpan_raw n hH
  let D : ℝ := ((momentIndices n).card : ℝ) * C * (n.factorial : ℝ) ^ 2
  let L : ℝ := 1 + ((momentIndices n).card : ℝ) * D
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨L, hL, ?_⟩
  intro ι _ h _ _ π φ hφ χ hχ θ w hw hval hjet
  let T : ℝ≥0∞ := ∑ α ∈ momentIndices n,
    ENNReal.ofReal (w ^ (α.1 + α.2) / ((α.1.factorial * α.2.factorial : ℕ) : ℝ)) *
      blochFibreDerivNorm π χ α φ θ
  have hcard : 1 ≤ ((momentIndices n).card : ℝ≥0∞) := by
    have hm : (0, 0) ∈ momentIndices n := by simp [momentIndices]
    exact_mod_cast Finset.card_pos.mpr ⟨(0, 0), hm⟩
  have hroot : ((momentIndices n).card : ℝ≥0∞) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal ((momentIndices n).card : ℝ) := by
    rw [ENNReal.ofReal_natCast]
    simpa only [ENNReal.rpow_one] using ENNReal.rpow_le_rpow_of_exponent_le hcard (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hraw : ∑ α ∈ momentIndices n, ENNReal.ofReal (w ^ (α.1 + α.2)) *
      blochFibreDerivNorm π χ α φ θ ≤ ENNReal.ofReal ((n.factorial : ℝ) ^ 2) * T := by
    dsimp only [T]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro α hα
    have hαn : α.1 + α.2 ≤ n := (Finset.mem_filter.mp hα).2
    have hf : ((α.1.factorial * α.2.factorial : ℕ) : ℝ) ≤ (n.factorial : ℝ) ^ 2 := by
      rw [Nat.cast_mul, pow_two]
      exact mul_le_mul (by exact_mod_cast Nat.factorial_le (by omega : α.1 ≤ n))
        (by exact_mod_cast Nat.factorial_le (by omega : α.2 ≤ n)) (by positivity) (by positivity)
    have hp : w ^ (α.1 + α.2) ≤ (n.factorial : ℝ) ^ 2 *
        (w ^ (α.1 + α.2) / ((α.1.factorial * α.2.factorial : ℕ) : ℝ)) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < ((α.1.factorial * α.2.factorial : ℕ) : ℝ))).mpr
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hf (pow_nonneg hw.le (α.1 + α.2))
    rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg _)]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hp) le_rfl
  have ht (β : ℕ × ℕ) (hβ : β ∈ momentIndices n) :
      ENNReal.ofReal (|χ θ| ^ (n + 1)) *
        (ENNReal.ofReal (w ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) *
          blochFibreDerivNorm π (fun _ => 1) β φ θ) ≤ ENNReal.ofReal D * T := by
    have hj := hb π φ hφ χ hχ θ hw hval hjet β (Finset.mem_filter.mp hβ).2
    have hwβ : w ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ) ≤
        w ^ (β.1 + β.2) := div_le_self (by positivity) (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)))
    calc _ ≤ ENNReal.ofReal (|χ θ| ^ (n + 1)) *
          (ENNReal.ofReal (w ^ (β.1 + β.2)) * blochFibreDerivNorm π (fun _ => 1) β φ θ) :=
        mul_le_mul' le_rfl (mul_le_mul' (ENNReal.ofReal_le_ofReal hwβ) le_rfl)
      _ = ENNReal.ofReal (w ^ (β.1 + β.2) * |χ θ| ^ (n + 1)) *
          blochFibreDerivNorm π (fun _ => 1) β φ θ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_comm (|χ θ| ^ _)]
      _ ≤ ENNReal.ofReal D * T := by
        simpa only [D, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul hC.le, mul_assoc]
          using hj.trans (mul_le_mul' (mul_le_mul' hroot le_rfl) hraw)
  unfold datumJets
  rw [Finset.mul_sum]
  refine (Finset.sum_le_sum ht).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have he : ((momentIndices n).card : ℝ≥0∞) * ENNReal.ofReal D ≤ ENNReal.ofReal L := by
    rw [← ENNReal.ofReal_natCast (momentIndices n).card, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left zero_le_one)
  simpa only [mul_assoc] using mul_le_mul' he (le_rfl : T ≤ T)

/-- Finite weighted pair norm without a cell integration. -/
def factorFamilyPairNorm {ι : Type*} [Fintype ι] (π : ι → ℝ) (A B : ι → ℝ) : ℝ≥0∞ :=
  (∑ x, ENNReal.ofReal ((π x)⁻¹) *
    (ENNReal.ofReal ((A x) ^ 2) + ENNReal.ofReal ((B x) ^ 2))) ^ (1 / 2 : ℝ)

private theorem factorFamilyPairNorm_eq_cell {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (A B : ι → ℝ) :
    factorFamilyPairNorm π A B = factorCellPairNorm (Measure.dirac ()) π
      (fun x (_ : Unit) => A x) (fun x (_ : Unit) => B x) := by
  simp only [factorFamilyPairNorm, factorCellPairNorm, lintegral_const, measure_univ,
    mul_one]

/-- Scaling a finite pair norm pulls out the absolute scalar. -/
theorem factorFamilyPairNorm_smul {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (A B : ι → ℝ) (c : ℝ) :
    factorFamilyPairNorm π (fun x => c * A x) (fun x => c * B x) =
      ENNReal.ofReal |c| * factorFamilyPairNorm π A B := by
  simp only [factorFamilyPairNorm_eq_cell]
  exact factorCellPairNorm_smul _ _ _ _ c

/-- A finite pointwise majorant passes to the weighted family norm. -/
theorem factorFamilyPairNorm_sum_le {ι κ : Type*} [Fintype ι]
    (π : ι → ℝ) (s : Finset κ) (c : κ → ℝ) (hc : ∀ a ∈ s, 0 ≤ c a)
    (A B : ι → ℝ) (P Q : κ → ι → ℝ) (hA : ∀ x, 0 ≤ A x) (hB : ∀ x, 0 ≤ B x)
    (hAP : ∀ x, A x ≤ ∑ a ∈ s, c a * P a x)
    (hBQ : ∀ x, B x ≤ ∑ a ∈ s, c a * Q a x) :
    factorFamilyPairNorm π A B ≤ (s.card : ℝ≥0∞) ^ (1 / 2 : ℝ) *
      ∑ a ∈ s, ENNReal.ofReal (c a) * factorFamilyPairNorm π (P a) (Q a) := by
  simp only [factorFamilyPairNorm_eq_cell]
  exact factorCellPairNorm_sum_le (Measure.dirac ()) π s c hc
    (fun x (_ : Unit) => A x) (fun x (_ : Unit) => B x)
    (fun a x (_ : Unit) => P a x) (fun a x (_ : Unit) => Q a x)
    (fun x _ => hA x) (fun x _ => hB x)
    (fun _ _ _ => aemeasurable_const) (fun _ _ _ => aemeasurable_const)
    (Eventually.of_forall (fun _ => hAP)) (Eventually.of_forall (fun _ => hBQ))

/-- One span constant covers every derivative split occurring in a word of total order `m+s`. -/
theorem factorBlochSpan_uniform (m s : ℕ) {H : ℝ} (hH : 1 ≤ H) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ x, NormedAddCommGroup (h x)] [∀ x, NormedSpace ℝ (h x)]
    (π : ι → ℝ) (φ : ∀ x, Vec 2 → h x),
    (∀ x, StronglyMeasurable (φ x) ∧ HasCompactSupport (φ x)) →
    ∀ (χ : Vec 2 → ℝ), ContDiff ℝ (⊤ : ℕ∞) χ → ∀ θ {w : ℝ}, 0 < w →
    |χ θ| ≤ H → (∀ i ≤ m + s, w ^ i * ‖iteratedFDeriv ℝ i χ θ‖ ≤ H) →
    ∀ j k : ℕ, j + k ≤ m →
    ENNReal.ofReal (|χ θ| ^ (m + s + 1 - k)) * datumJets π w (j + s) φ θ ≤
      ENNReal.ofReal C * ∑ α ∈ momentIndices (m + s),
        ENNReal.ofReal (w ^ (α.1 + α.2) / ((α.1.factorial * α.2.factorial : ℕ) : ℝ)) *
          blochFibreDerivNorm π χ α φ θ := by
  classical
  choose c hc hb using fun n => factorBlochSpan n hH
  let A : ℝ := ∑ j ∈ Finset.range (m + 1), c (j + s)
  have hA : 0 ≤ A := Finset.sum_nonneg (fun j _ => (hc (j + s)).le)
  let C : ℝ := 1 + H ^ m * A
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro ι _ h _ _ π φ hφ χ hχ θ w hw hval hjet j k hjk
  have hjm : j ≤ m := by omega
  have hca : c (j + s) ≤ A := Finset.single_le_sum
    (f := fun j => c (j + s)) (fun j _ => (hc (j + s)).le) (Finset.mem_range.mpr (by omega))
  have hp : |χ θ| ^ (m - j - k) ≤ H ^ m :=
    (pow_le_pow_left₀ (abs_nonneg _) hval _).trans (pow_le_pow_right₀ hH (by omega))
  have hs := hb (j + s) π φ hφ χ hχ θ hw hval (fun i hi => hjet i (by omega))
  have hT : (∑ α ∈ momentIndices (j + s),
      ENNReal.ofReal (w ^ (α.1 + α.2) / ((α.1.factorial * α.2.factorial : ℕ) : ℝ)) *
        blochFibreDerivNorm π χ α φ θ) ≤ ∑ α ∈ momentIndices (m + s),
      ENNReal.ofReal (w ^ (α.1 + α.2) / ((α.1.factorial * α.2.factorial : ℕ) : ℝ)) *
        blochFibreDerivNorm π χ α φ θ := by
    apply Finset.sum_le_sum_of_subset
    intro α hα
    simp only [momentIndices, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hα ⊢
    omega
  rw [show m + s + 1 - k = (m - j - k) + (j + s + 1) by omega, pow_add,
    ENNReal.ofReal_mul (by positivity), mul_assoc]
  refine (mul_le_mul' (ENNReal.ofReal_le_ofReal hp) hs).trans ?_
  have hC : H ^ m * c (j + s) ≤ C :=
    (mul_le_mul_of_nonneg_left hca (pow_nonneg (zero_le_one.trans hH) _)).trans
      (le_add_of_nonneg_left zero_le_one)
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal hC) hT

end AVRegularity.CycleWords.Assembly
end
end

section
/-! Quantitative moment bounds for the retained cutoff Fourier amplitudes. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set Filter AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-- The weighted normalized ordered Fourier pair is the moment amplitude norm. -/
theorem factorFourier_ordered_pair {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ x, NormedAddCommGroup (h x)] [∀ x, NormedSpace ℝ (h x)] [∀ x, CompleteSpace (h x)]
    (π : ι → ℝ) {g : ∀ x, Vec 2 → h x} (hg : ∀ x, FactorHasAllMoments (g x))
    {k : ℕ} (wd : DerivativeWord2 k) (θ : Vec 2) {w : ℝ} (hw : 0 ≤ w) :
    factorFamilyPairNorm π
      (fun x => w ^ k * ‖orderedDerivative wd (fun θ => ∫ y, Real.cos (vecDot θ y) • g x y) θ‖)
      (fun x => w ^ k * ‖orderedDerivative wd (fun θ => ∫ y, Real.sin (vecDot θ y) • g x y) θ‖) =
        momentAmpNorm π w (idxCount wd) g θ := by
  unfold factorFamilyPairNorm momentAmpNorm
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
    ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
    factorFourier_normalized_ordered_sq (hg x) wd θ hw]

/-- Full normalized Fourier jets are bounded by the finite collection of ordered moments. -/
theorem factorFourier_full_pair_le {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ x, NormedAddCommGroup (h x)] [∀ x, NormedSpace ℝ (h x)] [∀ x, CompleteSpace (h x)]
    (π : ι → ℝ) {g : ∀ x, Vec 2 → h x} (hg : ∀ x, FactorHasAllMoments (g x))
    (k : ℕ) (θ : Vec 2) {w : ℝ} (hw : 0 ≤ w) :
    ENNReal.ofReal (w ^ k) * factorFamilyPairNorm π
      (fun x => ‖iteratedFDeriv ℝ k (fun θ => ∫ y, Real.cos (vecDot θ y) • g x y) θ‖)
      (fun x => ‖iteratedFDeriv ℝ k (fun θ => ∫ y, Real.sin (vecDot θ y) • g x y) θ‖) ≤
        ENNReal.ofReal ((2 : ℝ) ^ k) * ∑ wd : DerivativeWord2 k,
          momentAmpNorm π w (idxCount wd) g θ := by
  let A (ψ : ℝ → ℝ) (x : ι) := w ^ k *
    ‖iteratedFDeriv ℝ k (fun θ => ∫ y, ψ (vecDot θ y) • g x y) θ‖
  let P (ψ : ℝ → ℝ) (wd : DerivativeWord2 k) (x : ι) := w ^ k *
    ‖orderedDerivative wd (fun θ => ∫ y, ψ (vecDot θ y) • g x y) θ‖
  have hb (ψ : ℝ → ℝ) (hψ : ∀ x, ContDiff ℝ k (fun θ => ∫ y, ψ (vecDot θ y) • g x y)) :
      ∀ x, A ψ x ≤ ∑ wd : DerivativeWord2 k, (1 : ℝ) * P ψ wd x := by
    intro x
    have hp := mul_le_mul_of_nonneg_left
      (AVRegularity.ChartTransport.norm_iteratedFDeriv_le_sum_words (hψ x) θ) (pow_nonneg hw k)
    simpa only [Finset.mul_sum, one_mul] using hp
  have hc : ∀ x, ContDiff ℝ k (fun θ => ∫ y, Real.cos (vecDot θ y) • g x y) :=
    fun x => factorCos_contDiff (hg x) k
  have hs : ∀ x, ContDiff ℝ k (fun θ => ∫ y, Real.sin (vecDot θ y) • g x y) :=
    fun x => factorSin_contDiff (hg x) k
  have hn := factorFamilyPairNorm_sum_le π (Finset.univ : Finset (DerivativeWord2 k))
    (fun _ => 1) (fun _ _ => zero_le_one) (A Real.cos) (A Real.sin)
    (P Real.cos) (P Real.sin) (fun x => by dsimp [A]; positivity)
    (fun x => by dsimp [A]; positivity) (hb Real.cos hc) (hb Real.sin hs)
  have he : factorFamilyPairNorm π (A Real.cos) (A Real.sin) = ENNReal.ofReal (w ^ k) *
      factorFamilyPairNorm π
      (fun x => ‖iteratedFDeriv ℝ k (fun θ => ∫ y, Real.cos (vecDot θ y) • g x y) θ‖)
      (fun x => ‖iteratedFDeriv ℝ k (fun θ => ∫ y, Real.sin (vecDot θ y) • g x y) θ‖) := by
    dsimp only [A]
    rw [factorFamilyPairNorm_smul, abs_of_nonneg (pow_nonneg hw k)]
  rw [he] at hn
  have hp (wd : DerivativeWord2 k) : factorFamilyPairNorm π (P Real.cos wd) (P Real.sin wd) =
      momentAmpNorm π w (idxCount wd) g θ := factorFourier_ordered_pair π hg wd θ hw
  simp only [hp, ENNReal.ofReal_one, one_mul, AVRegularity.ChartTransport.card_derivativeWord2] at hn
  refine hn.trans (mul_le_mul' ?_ le_rfl)
  rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, Nat.cast_pow, Nat.cast_ofNat]
  simpa only [ENNReal.rpow_one] using ENNReal.rpow_le_rpow_of_exponent_le
    (show (1 : ℝ≥0∞) ≤ 2 ^ k by exact one_le_pow₀ (by norm_num)) (by norm_num : (1 / 2 : ℝ) ≤ 1)

/-- Weighted Leibniz estimate for a scalar multiplier and a family of amplitude pairs. -/
theorem factorProduct_pair_le {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ x, NormedAddCommGroup (h x)] [∀ x, NormedSpace ℝ (h x)]
    (π : ι → ℝ) {mc : Vec 2 → ℝ} {F G : ∀ x, Vec 2 → h x} {m : ℕ}
    (hmc : ContDiff ℝ m mc) (hF : ∀ x, ContDiff ℝ m (F x)) (hG : ∀ x, ContDiff ℝ m (G x))
    {k : ℕ} (hk : k ≤ m) (θ : Vec 2) {w : ℝ} (hw : 0 ≤ w) :
    ENNReal.ofReal (w ^ k) * factorFamilyPairNorm π
      (fun x => ‖iteratedFDeriv ℝ k (fun z => mc z • F x z) θ‖)
      (fun x => ‖iteratedFDeriv ℝ k (fun z => mc z • G x z) θ‖) ≤
    ENNReal.ofReal ((k + 1 : ℕ) : ℝ) * ∑ l ∈ Finset.range (k + 1),
      ENNReal.ofReal ((k.choose l : ℝ) * (w ^ l * ‖iteratedFDeriv ℝ l mc θ‖)) *
      (ENNReal.ofReal (w ^ (k - l)) * factorFamilyPairNorm π
        (fun x => ‖iteratedFDeriv ℝ (k - l) (F x) θ‖)
        (fun x => ‖iteratedFDeriv ℝ (k - l) (G x) θ‖)) := by
  let c (l : ℕ) : ℝ := (k.choose l : ℝ) * (w ^ l * ‖iteratedFDeriv ℝ l mc θ‖)
  let P (V : ∀ x, Vec 2 → h x) (l : ℕ) (x : ι) : ℝ :=
    w ^ (k - l) * ‖iteratedFDeriv ℝ (k - l) (V x) θ‖
  let A (V : ∀ x, Vec 2 → h x) (x : ι) : ℝ :=
    w ^ k * ‖iteratedFDeriv ℝ k (fun z => mc z • V x z) θ‖
  have hb (V : ∀ x, Vec 2 → h x) (hV : ∀ x, ContDiff ℝ m (V x)) (x : ι) :
      A V x ≤ ∑ l ∈ Finset.range (k + 1), c l * P V l x := by
    have hp := mul_le_mul_of_nonneg_left
      (norm_iteratedFDeriv_smul_le hmc (hV x) θ (n := k) (by exact_mod_cast hk)) (pow_nonneg hw k)
    refine hp.trans_eq ?_
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    have hlk : l ≤ k := by have := Finset.mem_range.mp hl; omega
    dsimp only [c, P]
    rw [show w ^ k = w ^ l * w ^ (k - l) by rw [← pow_add, Nat.add_sub_of_le hlk]]
    ring
  have hn := factorFamilyPairNorm_sum_le π (Finset.range (k + 1)) c
    (fun l _ => by dsimp [c]; positivity) (A F) (A G) (P F) (P G)
    (fun x => by dsimp [A]; positivity) (fun x => by dsimp [A]; positivity) (hb F hF) (hb G hG)
  have he : factorFamilyPairNorm π (A F) (A G) = ENNReal.ofReal (w ^ k) *
      factorFamilyPairNorm π
      (fun x => ‖iteratedFDeriv ℝ k (fun z => mc z • F x z) θ‖)
      (fun x => ‖iteratedFDeriv ℝ k (fun z => mc z • G x z) θ‖) := by
    dsimp only [A]
    rw [factorFamilyPairNorm_smul, abs_of_nonneg (pow_nonneg hw k)]
  have heP (l : ℕ) : factorFamilyPairNorm π (P F l) (P G l) = ENNReal.ofReal (w ^ (k - l)) *
      factorFamilyPairNorm π (fun x => ‖iteratedFDeriv ℝ (k - l) (F x) θ‖)
      (fun x => ‖iteratedFDeriv ℝ (k - l) (G x) θ‖) := by
    dsimp only [P]
    rw [factorFamilyPairNorm_smul, abs_of_nonneg (pow_nonneg hw _)]
  rw [he] at hn
  simp only [heP, Finset.card_range] at hn
  refine hn.trans (mul_le_mul' ?_ le_rfl)
  rw [ENNReal.ofReal_natCast]
  simpa only [ENNReal.rpow_one] using ENNReal.rpow_le_rpow_of_exponent_le
    (show (1 : ℝ≥0∞) ≤ (k + 1 : ℕ) by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k))
    (by norm_num : (1 / 2 : ℝ) ≤ 1)

/-- The finite Leibniz and Fourier losses are uniform over the data and the component family. -/
theorem factorCutoff_moment_bound (m s : ℕ) {Cc Cs : ℝ} (hCc : 0 ≤ Cc) (hCs : 0 ≤ Cs) :
    ∃ L : ℝ, 0 < L ∧ ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ x, NormedAddCommGroup (h x)] [∀ x, NormedSpace ℝ (h x)] [∀ x, CompleteSpace (h x)]
    (π : ι → ℝ) (g φ : ∀ x, Vec 2 → h x), (∀ x, FactorHasAllMoments (g x)) →
    ∀ (mc χ : Vec 2 → ℝ), ContDiff ℝ (⊤ : ℕ∞) mc → ∀ θ {w R : ℝ}, 0 < w → 0 ≤ R →
    (∀ l ≤ m, w ^ l * ‖iteratedFDeriv ℝ l mc θ‖ ≤ Cc * |χ θ| ^ (m + s + 1 - l)) →
    (∀ β ∈ momentIndices m, momentAmpNorm π w β g θ ≤
      ENNReal.ofReal R * datumJets π w (β.1 + β.2 + s) φ θ) →
    (∀ j l : ℕ, j + l ≤ m →
      ENNReal.ofReal (|χ θ| ^ (m + s + 1 - l)) * datumJets π w (j + s) φ θ ≤
        ENNReal.ofReal Cs * ∑ α ∈ momentIndices (m + s),
          ENNReal.ofReal (w ^ (α.1 + α.2) / ((α.1.factorial * α.2.factorial : ℕ) : ℝ)) *
            blochFibreDerivNorm π χ α φ θ) →
    ampDerivNorm π m w (fun x z => mc z • ∫ y, Real.cos (vecDot z y) • g x y)
      (fun x z => mc z • ∫ y, Real.sin (vecDot z y) • g x y) θ ≤
      ENNReal.ofReal (L * R) * ∑ α ∈ momentIndices (m + s),
        ENNReal.ofReal (w ^ (α.1 + α.2) / ((α.1.factorial * α.2.factorial : ℕ) : ℝ)) *
          blochFibreDerivNorm π χ α φ θ := by
  classical
  let c (k l : ℕ) : ℝ := (k.choose l : ℝ) * Cc * (2 : ℝ) ^ (2 * (k - l)) * Cs
  have hc (k l : ℕ) : 0 ≤ c k l := by dsimp [c]; positivity
  let b (k : ℕ) : ℝ := ((k + 1 : ℕ) : ℝ) * ∑ l ∈ Finset.range (k + 1), c k l
  have hb (k : ℕ) : 0 ≤ b k := by dsimp [b]; positivity
  let L : ℝ := 1 + ∑ k ∈ Finset.range (m + 1), b k
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨L, hL, ?_⟩
  intro ι _ h _ _ _ π g φ hg mc χ hmc θ w R hw hR hj hm hs
  let T : ℝ≥0∞ := ∑ α ∈ momentIndices (m + s),
    ENNReal.ofReal (w ^ (α.1 + α.2) / ((α.1.factorial * α.2.factorial : ℕ) : ℝ)) *
      blochFibreDerivNorm π χ α φ θ
  let F (ψ : ℝ → ℝ) (x : ι) (z : Vec 2) := ∫ y, ψ (vecDot z y) • g x y
  have hF : ∀ x, ContDiff ℝ m (F Real.cos x) := fun x => factorCos_contDiff (hg x) m
  have hG : ∀ x, ContDiff ℝ m (F Real.sin x) := fun x => factorSin_contDiff (hg x) m
  have hterm (k : ℕ) (hk : k ≤ m) (l : ℕ) (hl : l ∈ Finset.range (k + 1)) :
      ENNReal.ofReal ((k.choose l : ℝ) * (w ^ l * ‖iteratedFDeriv ℝ l mc θ‖)) *
        (ENNReal.ofReal (w ^ (k - l)) * factorFamilyPairNorm π
          (fun x => ‖iteratedFDeriv ℝ (k - l) (F Real.cos x) θ‖)
          (fun x => ‖iteratedFDeriv ℝ (k - l) (F Real.sin x) θ‖)) ≤
        ENNReal.ofReal (c k l) * (ENNReal.ofReal R * T) := by
    have hlk : l ≤ k := by have := Finset.mem_range.mp hl; omega
    have hβ (wd : DerivativeWord2 (k - l)) : idxCount wd ∈ momentIndices m := by
      have he := idxCount_sum wd
      simp only [momentIndices, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      omega
    have hword (wd : DerivativeWord2 (k - l)) :
        ENNReal.ofReal (|χ θ| ^ (m + s + 1 - l)) * momentAmpNorm π w (idxCount wd) g θ ≤
          ENNReal.ofReal R * (ENNReal.ofReal Cs * T) := by
      have hmo := hm (idxCount wd) (hβ wd)
      rw [idxCount_sum] at hmo
      calc _ ≤ ENNReal.ofReal (|χ θ| ^ (m + s + 1 - l)) *
            (ENNReal.ofReal R * datumJets π w (k - l + s) φ θ) := mul_le_mul' le_rfl hmo
        _ = ENNReal.ofReal R * (ENNReal.ofReal (|χ θ| ^ (m + s + 1 - l)) *
            datumJets π w (k - l + s) φ θ) := by ac_rfl
        _ ≤ _ := mul_le_mul' le_rfl (hs (k - l) l (by omega))
    have hsum : ENNReal.ofReal (|χ θ| ^ (m + s + 1 - l)) *
        (∑ wd : DerivativeWord2 (k - l), momentAmpNorm π w (idxCount wd) g θ) ≤
          ENNReal.ofReal ((2 : ℝ) ^ (k - l)) * (ENNReal.ofReal R * (ENNReal.ofReal Cs * T)) := by
      rw [Finset.mul_sum]
      refine (Finset.sum_le_sum (fun wd _ => hword wd)).trans_eq ?_
      rw [Finset.sum_const, AVRegularity.ChartTransport.card_derivativeWord2, nsmul_eq_mul,
        ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat, Nat.cast_pow, Nat.cast_ofNat]
    have hp := factorFourier_full_pair_le π hg (k - l) θ hw.le
    have hcut := ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (hj l (hlk.trans hk)) (Nat.cast_nonneg (k.choose l)))
    refine (mul_le_mul' hcut hp).trans ?_
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul hCc]
    calc _ = (ENNReal.ofReal (k.choose l : ℝ) * ENNReal.ofReal Cc *
          ENNReal.ofReal ((2 : ℝ) ^ (k - l))) *
          (ENNReal.ofReal (|χ θ| ^ (m + s + 1 - l)) *
            ∑ wd : DerivativeWord2 (k - l), momentAmpNorm π w (idxCount wd) g θ) := by ac_rfl
      _ ≤ _ := mul_le_mul' le_rfl hsum
      _ = ENNReal.ofReal (c k l) * (ENNReal.ofReal R * T) := by
        dsimp only [c]
        rw [show (2 : ℝ) ^ (2 * (k - l)) = 2 ^ (k - l) * 2 ^ (k - l) by
          rw [← pow_add]; congr 1; omega]
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_mul (by positivity)]
        ac_rfl
  have hk (k : ℕ) (hkm : k ∈ Finset.range (m + 1)) :
      ENNReal.ofReal (w ^ k / (k.factorial : ℝ)) * factorFamilyPairNorm π
        (fun x => ‖iteratedFDeriv ℝ k (fun z => mc z • F Real.cos x z) θ‖)
        (fun x => ‖iteratedFDeriv ℝ k (fun z => mc z • F Real.sin x z) θ‖) ≤
      ENNReal.ofReal (b k) * (ENNReal.ofReal R * T) := by
    have hkm' : k ≤ m := by have := Finset.mem_range.mp hkm; omega
    have hwk : w ^ k / (k.factorial : ℝ) ≤ w ^ k :=
      div_le_self (pow_nonneg hw.le _) (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k))
    refine (mul_le_mul' (ENNReal.ofReal_le_ofReal hwk) le_rfl).trans ?_
    refine (factorProduct_pair_le π (hmc.of_le (by exact_mod_cast le_top)) hF hG hkm' θ hw.le).trans ?_
    refine (mul_le_mul' le_rfl (Finset.sum_le_sum (hterm k hkm'))).trans_eq ?_
    dsimp only [b]
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ENNReal.ofReal_sum_of_nonneg (fun l _ => hc k l), ← Finset.sum_mul, mul_assoc]
  change (∑ k ∈ Finset.range (m + 1), _) ≤ _
  refine (Finset.sum_le_sum hk).trans ?_
  rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun k _ => hb k)]
  have he : (∑ k ∈ Finset.range (m + 1), b k) ≤ L := le_add_of_nonneg_left zero_le_one
  refine (mul_le_mul' (ENNReal.ofReal_le_ofReal he) le_rfl).trans_eq ?_
  rw [ENNReal.ofReal_mul hL.le, mul_assoc]

end AVRegularity.CycleWords.Assembly
end
end
end

section
section
/-! The closed Fourier calculus ingredient of the moment-to-factor reduction. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set Filter Topology AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly
universe u v

/-- The moment core supplies the complete retained factor calculus, with constants before data. -/
theorem factorMomentCalculus : FactorMomentCalculusStatement.{u, v} := by
  intro m s P ξ0 ρ χ ψ hρ hχ hsupport hψ hbψ χr χ₃ hr hbr h₃ hb₃ hfac
  obtain ⟨H, Cc, hH, hCc, hcut⟩ := factorPieceCutoff_uniform m s hψ hbψ hr hbr h₃ hb₃ hfac
  obtain ⟨Cs, hCs, hspan⟩ := factorBlochSpan_uniform m s hH
  let E : ℝ := (2 * Real.pi)⁻¹ ^ 2
  have hE : 0 < E := by dsimp [E]; positivity
  obtain ⟨L0, hL0, hbound⟩ := factorCutoff_moment_bound m s
    (mul_nonneg (abs_nonneg E) hCc.le) hCs.le
  let L : ℝ := 2 * ((m + 1 : ℕ) : ℝ) * L0
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨L, hL, ?_⟩
  intro ι _ h _ _ _ _ _ _ π hπ η w Bg B hη hw hw1 hscale hBg hB φ g hφ hgm Φ hΦ hΦjet hmoment
  have hg (x : ι) : FactorHasAllMoments (g x) := hgm x
  let mc : Vec 2 → ℝ := pieceCutoff χ ψ η
  let cr : Vec 2 → ℝ := fun z => χr ((Real.sqrt η)⁻¹ • z)
  let mcE : Vec 2 → ℝ := fun z => E * mc z
  have hmc : ContDiff ℝ (⊤ : ℕ∞) mc := (hχ.comp (contDiff_id.const_smul _)).mul hψ
  have hcr : ContDiff ℝ (⊤ : ℕ∞) cr := hr.comp (contDiff_id.const_smul _)
  have hmcE : ContDiff ℝ (⊤ : ℕ∞) mcE := contDiff_const.mul hmc
  have hcχ : HasCompactSupport χ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Vec 2) (max ρ 0)) fun z hz => ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hz
    exact hsupport z ((le_max_left ρ 0).trans (hz.le.trans (norm_le_sqrt_vecDot z)))
  have hcmc : HasCompactSupport mc :=
    (hcχ.comp_smul (inv_ne_zero (Real.sqrt_ne_zero'.mpr hη))).mul_right
  let C : ∀ x, Vec 2 → h x := fun x => cutoffCosAmplitude mc (g x)
  let S : ∀ x, Vec 2 → h x := fun x => cutoffSinAmplitude mc (g x)
  have hCS (x : ι) : ContDiff ℝ m (C x) ∧ ContDiff ℝ m (S x) :=
    factorCutoff_contDiff (hg x) (hmc.of_le (by exact_mod_cast le_top))
  have hs (x : ι) (z : Vec 2) (hz : ρ < fibreNorm (planeFibreFrequency η z)) : C x z = 0 ∧ S x z = 0 := by
    have hmcz : mc z = 0 := by
      dsimp [mc, pieceCutoff]
      rw [hsupport _ (by simpa only [fibreNorm_planeFibreFrequency] using hz.le), zero_mul]
    simp only [C, S, cutoffCosAmplitude, cutoffSinAmplitude, hmcz, mul_zero, zero_smul, and_self]
  let Ac : ∀ x, Vec 2 → h x := fun x => factorGaugeCos η ξ0 Φ (C x) (S x)
  let As : ∀ x, Vec 2 → h x := fun x => factorGaugeSin η ξ0 Φ (C x) (S x)
  have hAcAs (x : ι) : ContDiff ℝ m (Ac x) ∧ ContDiff ℝ m (As x) :=
    factorGauge_contDiff hρ hΦ (hCS x).1 (hCS x).2 (hs x)
  refine ⟨fun x => (hg x).integrable, ?_, hCS, Ac, As, hAcAs, ?_, ?_⟩
  · intro r _ hsr x
    exact factorFourierCutoff_isRetained hmc hcmc (hg x) r hsr
  · intro θ hθ x
    exact factorGauge_rotation η ξ0 Φ (C x) (S x) hθ
  · intro θ hθ
    by_cases hθρ : fibreNorm (planeFibreFrequency η θ) ≤ ρ
    · let X : ℝ := 1 + Real.sqrt (vecDot θ θ) / w
      have hX : 1 ≤ X := le_add_of_nonneg_right (div_nonneg (Real.sqrt_nonneg _) hw.le)
      have hcutθ := hcut η w hη hw hw1 hscale θ
      have hval : |cr θ| ≤ H := by
        have hv := hcutθ.1 0 (by omega)
        simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hv
      have hj (l : ℕ) (hl : l ≤ m) : w ^ l * ‖iteratedFDeriv ℝ l mcE θ‖ ≤
          (|E| * Cc) * |cr θ| ^ (m + s + 1 - l) := by
        change w ^ l * ‖iteratedFDeriv ℝ l (fun z => E • mc z) θ‖ ≤ _
        rw [iteratedFDeriv_const_smul_apply' (hmc.of_le (by exact_mod_cast le_top)).contDiffAt,
          norm_smul, Real.norm_eq_abs]
        calc w ^ l * (|E| * ‖iteratedFDeriv ℝ l mc θ‖) = |E| * (w ^ l * ‖iteratedFDeriv ℝ l mc θ‖) := by ring
          _ ≤ |E| * (Cc * |cr θ| ^ (m + s + 1 - l)) :=
            mul_le_mul_of_nonneg_left (hcutθ.2 l hl) (abs_nonneg E)
          _ = _ := by ring
      have hraw := hbound π g φ hg mcE cr hmcE θ hw
        (show 0 ≤ Real.exp (Φ θ).re * B * X ^ P by positivity) hj
        (hmoment θ hθρ) (hspan π φ hφ cr hcr θ hw hval hcutθ.1)
      change ampDerivNorm π m w C S θ ≤ _ at hraw
      have hU : IsOpen {z | fibreNorm (planeFibreFrequency η z) < ξ0} :=
        isOpen_lt (continuous_fibreNorm_planeFibreFrequency η) continuous_const
      have hInv : ∀ z ∈ {z | fibreNorm (planeFibreFrequency η z) < ξ0}, ∀ x,
          Ac x z = (Complex.exp (-Φ z)).re • C x z + (Complex.exp (-Φ z)).im • S x z ∧
          As x z = (Complex.exp (-Φ z)).re • S x z - (Complex.exp (-Φ z)).im • C x z := by
        intro z hz x
        simp only [Ac, As, factorGaugeCos, factorGaugeSin, indicator_of_mem hz, and_self]
      have hGjet (l : ℕ) (hl : l ≤ m) : w ^ l * ‖iteratedFDeriv ℝ l (fun z => Complex.exp (-Φ z)) θ‖ ≤
          Bg * X ^ m * Real.exp (-(Φ θ).re) :=
        (hΦjet θ hθρ l hl).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX hl) hBg) (Real.exp_nonneg _))
      have hrot := ampDerivNorm_rot_le hU hΦ π hπ (fun x => (hCS x).1) (fun x => (hCS x).2)
        hInv hθ hw.le hGjet
      refine hrot.trans ((mul_le_mul' le_rfl hraw).trans_eq ?_)
      have he : (2 * ((m + 1 : ℕ) : ℝ) * (Bg * X ^ m * Real.exp (-(Φ θ).re))) *
          (L0 * (Real.exp (Φ θ).re * B * X ^ P)) = L * Bg * B * X ^ (P + m) := by
        rw [pow_add]
        have hx : Real.exp (-(Φ θ).re) * Real.exp (Φ θ).re = 1 := by
          rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
        dsimp only [L]
        calc _ = (2 * ((m + 1 : ℕ) : ℝ) * L0 * Bg * B * (X ^ P * X ^ m)) *
            (Real.exp (-(Φ θ).re) * Real.exp (Φ θ).re) := by ring
          _ = _ := by rw [hx, mul_one]
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), he]
    · have hj0 (x : ι) (k : ℕ) := factorGauge_jets_zero (ξ0 := ξ0) Φ (hs x) (lt_of_not_ge hθρ) k
      have hz : ampDerivNorm π m w Ac As θ = 0 := by
        unfold ampDerivNorm
        apply Finset.sum_eq_zero
        intro k _
        have hp (x : ι) : iteratedFDeriv ℝ k (Ac x) θ = 0 ∧ iteratedFDeriv ℝ k (As x) θ = 0 := hj0 x k
        simp only [(hp _).1, (hp _).2, norm_zero, zero_pow (by norm_num : 2 ≠ 0), ENNReal.ofReal_zero,
          add_zero, mul_zero, Finset.sum_const_zero, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      rw [hz]
      exact zero_le

end AVRegularity.CycleWords.Assembly
end
end

section
/-! Integrating factors for the actual divergence-forced quiet mean. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-- Variation of constants for a measurable scalar coefficient and integrable source. -/
theorem quietForced_scalar_evolution {a b : ℝ} (hab : a ≤ b)
    (lam u f : ℝ → ℂ) (hlam : IntervalIntegrable lam volume a b)
    (hf : IntervalIntegrable f volume a b)
    (hu : StrongTimeRegularity a b u (fun t => lam t * u t + f t)) :
    u b = Complex.exp (∫ t in a..b, lam t) * u a +
      ∫ t in a..b, Complex.exp (∫ r in t..b, lam r) * f t := by
  have hphase := complexPrimitivePhase_strongTime hab (fun t => -lam t) hlam.neg
  have hp := hphase.complex_mul hu
  have hz : (fun t => (Complex.exp (∫ r in a..t, -lam r) * -lam t) * u t +
      Complex.exp (∫ r in a..t, -lam r) * (lam t * u t + f t)) =
      (fun t => Complex.exp (∫ r in a..t, -lam r) * f t) := by
    funext t
    ring
  rw [hz] at hp
  have hprod : IntervalIntegrable (fun t => Complex.exp (∫ r in a..t, -lam r) * f t)
      volume a b := by
    simpa only [mul_comm] using hf.mul_continuousOn hphase.ac.continuousOn
  have he := hp.complex_increment hprod
  simp only [intervalIntegral.integral_same, Complex.exp_zero, one_mul,
    intervalIntegral.integral_neg] at he
  have hi : Complex.exp (∫ t in a..b, lam t) * Complex.exp (-(∫ t in a..b, lam t)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have heq : u b = Complex.exp (∫ t in a..b, lam t) * u a +
      Complex.exp (∫ t in a..b, lam t) *
        (∫ t in a..b, Complex.exp (-(∫ r in a..t, lam r)) * f t) := by
    calc
      u b = (Complex.exp (∫ t in a..b, lam t) * Complex.exp (-(∫ t in a..b, lam t))) * u b :=
        by rw [hi, one_mul]
      _ = _ := by rw [mul_assoc, eq_add_of_sub_eq he]; ring
  rw [heq, ← intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hab] at ht
  have hat : IntervalIntegrable lam volume a t := hlam.mono_set (by
    rw [uIcc_of_le ht.1, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl ht.2)
  have htb : IntervalIntegrable lam volume t b := hlam.mono_set (by
    rw [uIcc_of_le ht.2, uIcc_of_le hab]
    exact Icc_subset_Icc ht.1 le_rfl)
  dsimp only
  rw [← mul_assoc, ← Complex.exp_add, ← intervalIntegral.integral_add_adjacent_intervals hat htb]
  congr 2
  ring

end AVRegularity.CycleWords.Assembly
end
end
end

section
section
/-! # Zero-amplitude word, part 1: vanishing of the coefficients and of the preceding-letter flux

If `θ = 0` the majorant of a cycle letter vanishes, so the essential time supremum of every
non-trivial constituent coefficient vanishes: the coefficients are `0` for almost every time. The
preceding-letter flux of the next word level then vanishes at those times, as it does when the
jets of the previous level vanish. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open scoped ENNReal

namespace AVRegularity.CycleWords.Assembly

section Coefficients


variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

/-- A cycle letter with `θ = 0` has the zero majorant. -/
theorem zawMajorant_le_zero (π : ι → ℝ) (L : CycleLetter ι h D) (dom : Set (ℝ × Vec 2))
    (J H : ℕ) (hL : IsCycleLetter π L dom J H) (hθ : L.theta = 0) (v u : ι) :
    L.majorant v u ≤ 0 := by
  have h1 : L.majorant v u ≤ ∑ u', L.majorant v u' :=
    Finset.single_le_sum (f := L.majorant v) (fun u' _ => hL.nonneg v u') (Finset.mem_univ u)
  exact h1.trans (hθ ▸ hL.row_sum v)

/-- **Coefficients of a zero letter vanish almost everywhere in time.** -/
theorem zawCoeff_ae_zero (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (L : CycleLetter ι h D) (I : Set ℝ) (J H : ℕ)
    (hL : IsCycleLetter π L (I ×ˢ Set.univ) J H) (hθ : L.theta = 0)
    (v u : ι) (o : Finset.Icc 2 D) (k : Fin (L.edge v u o).length)
    (hk : ((L.edge v u o).get k).map ≠ 0) (w : DerivativeWord2 (o.1 - 1)) :
    ∀ᵐ t ∂volume, t ∈ I → ∀ X z, ((L.edge v u o).get k).coeff w t X z = 0 := by
  have hh := hL.analytic.2 v u
  simp only [one_pow, ENNReal.ofReal_one, one_mul] at hh
  rw [ENNReal.ofReal_of_nonpos (zawMajorant_le_zero π L _ J H hL hθ v u), nonpos_iff_eq_zero] at hh
  have hmass : ENNReal.ofReal (Real.sqrt (π u / π v)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (div_pos (hπ u) (hπ v)))).ne'
  have hs := (mul_eq_zero.mp hh).resolve_left hmass
  have hg := Finset.sum_eq_zero_iff.mp hs ⟨o, k⟩ (Finset.mem_univ _)
  have hn : ENNReal.ofReal ‖((ChartedFamily.ofFiber L.edge).identity v u ⟨o, k⟩).map‖ ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr (by
      simpa only [ChartedFamily.ofFiber] using hk))).ne'
  have hs' := (mul_eq_zero.mp hg).resolve_left hn
  have hd := Finset.sum_eq_zero_iff.mp hs' o.1
    (by exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp o.2).1, le_rfl⟩)
  have hw := Finset.sum_eq_zero_iff.mp hd w (Finset.mem_univ w)
  have hr := Finset.sum_eq_zero_iff.mp hw 0 (Finset.mem_range.mpr (Nat.succ_pos _))
  have hq := Finset.sum_eq_zero_iff.mp hr 0 (Finset.mem_range.mpr (Nat.succ_pos _))
  have hle := ofFiber_jetSupOn_le_jetSupFam L.edge (I ×ˢ Set.univ) v u o k w 0 0
  have h0 : jetSupOn (I ×ˢ Set.univ) 0 0 (((L.edge v u o).get k).coeff w) = 0 :=
    le_antisymm (hq ▸ hle) bot_le
  filter_upwards [jetSupOn_ae_norm_bound (I ×ˢ Set.univ) 0 0
    (((L.edge v u o).get k).coeff w) (by rw [h0]; exact ENNReal.zero_ne_top)] with t ht
  intro hti X z
  have := ht X ⟨hti, Set.mem_univ X⟩ z
  rw [h0, ENNReal.toReal_zero] at this
  simpa using this

/-- The coefficients of all constituents of a zero letter vanish for almost every time. -/
theorem zawCoeff_ae_all (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (L : CycleLetter ι h D) (I : Set ℝ) (J H : ℕ)
    (hL : IsCycleLetter π L (I ×ˢ Set.univ) J H) (hθ : L.theta = 0) :
    ∀ᵐ t ∂volume, t ∈ I → ∀ (v u : ι) (o : Finset.Icc 2 D) (k : Fin (L.edge v u o).length),
      ((L.edge v u o).get k).map ≠ 0 → ∀ (w : DerivativeWord2 (o.1 - 1)) X z,
        ((L.edge v u o).get k).coeff w t X z = 0 := by
  have hh := ae_all_iff.mpr fun (v : ι) => ae_all_iff.mpr fun (u : ι) =>
    ae_all_iff.mpr fun (o : Finset.Icc 2 D) => ae_all_iff.mpr
      fun (k : Fin (L.edge v u o).length) => ae_all_iff.mpr
      fun (hk : ((L.edge v u o).get k).map ≠ 0) => ae_all_iff.mpr
      fun (w : DerivativeWord2 (o.1 - 1)) => zawCoeff_ae_zero π hπ L I J H hL hθ v u o k hk w
  filter_upwards [hh] with t ht hti v u o k hk w X z
  exact ht v u o k hk w hti X z

end Coefficients

section Flux

open scoped Classical

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

/-- The coefficient operator of an edge list vanishes when every constituent has zero map or zero
coefficients at the time `t`, and the slow evaluation of the zero function is `0`. -/
theorem zawSlowEvalCoefficient_eq_zero {Hu Hv : Type*} [NormedAddCommGroup Hu] [NormedSpace ℝ Hu]
    [NormedAddCommGroup Hv] [NormedSpace ℝ Hv] {d : ℕ} (ev : (Vec 2 → ℝ) → Vec 2 → ℝ)
    (hev : ∀ z, ev (fun _ => 0) z = 0) (edge : List (Constituent d Hu Hv)) (t : ℝ) (z : Vec 2)
    (hc : ∀ γ ∈ edge, γ.map = 0 ∨ ∀ w X z', γ.coeff w t X z' = 0) :
    slowEvalCoefficient ev edge t z = 0 := by
  unfold slowEvalCoefficient
  apply List.sum_eq_zero
  intro A hA
  obtain ⟨γ, hγ, rfl⟩ := List.mem_map.mp hA
  rcases hc γ hγ with hm | hcf
  · ext g
    simp [hm]
  · ext g
    have : ∀ (α : DerivativeWord2 (d - 1)) (k : Fin 2),
        ev (fun X => γ.coeff α t X z k) z = 0 := by
      intro α k
      have hf : (fun X => γ.coeff α t X z k) = fun _ => 0 := by
        funext X
        simp [hcf α X z]
      rw [hf]
      exact hev z
    simp [this]

/-- The slow evaluation of the zero function is `0` for the Taylor evaluation of a word chain. -/
theorem zaw_taylorSlow_zero (lo K : ℕ) (X0 Δ : Vec 2) :
    taylorSlow lo K (fun _ => 0) X0 Δ = 0 := by
  simp [taylorSlow]

/-- If every term of the preceding-letter flux of level `j + 1` vanishes, the flux vanishes. -/
theorem zawPreviousFlux_eq_zero (letters : Fin N → CycleLetter ι h D) (X0 : Vec 2) (δ : ℝ)
    (κ : Fin (N + 1) → ι → ℕ)
    (U : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (j : Fin N) (x : ι) (t : ℝ) (z : Vec 2)
    (hz : ∀ (u : ι) (d : admissibleOrders (fun p => κ p.1 p.2) D (j.succ, x) (j.castSucc, u)),
      slowEvalCoefficient
        (fun f z => taylorSlow (if (letters j).positive then 1 else 0)
          (letters j).slow f X0 (δ • z))
        ((letters j).edge x u ⟨d.1, (Finset.mem_filter.mp d.2).1⟩) t z
        (wordChainJetArray κ U (j.succ, x) (j.castSucc, u) d z) = 0) :
    wordChainPreviousFlux letters X0 δ κ U (j.succ, x) t z = 0 := by
  unfold wordChainPreviousFlux
  apply Finset.sum_eq_zero
  rintro ⟨j', u⟩ -
  apply Finset.sum_eq_zero
  intro d _
  by_cases hs : (j.succ : Fin (N + 1)).val = (j' : Fin (N + 1)).val + 1
  · have hj : j' = j.castSucc := Fin.ext (by simp at hs; simpa using hs.symm)
    subst hj
    simpa [hs] using hz u d
  · have hs' : ¬ ((j.succ, x).1.val = (j', u).1.val + 1) := hs
    simp only [hs', ↓reduceDIte]
    simp

end Flux

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # Zero-amplitude word, part 3: one level of the chain with zero forcing and datum vanishes

A successor level of a plane chain with zero datum whose preceding-letter flux vanishes for almost
every time and space point vanishes at every time of the piece. The Duhamel identity against the
backward Bloch field (`wordChainCoordinateNative_duhamel`) on `[a, t]` gives it; the identity is
restricted from `[a, b]` to `[a, t]` here. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution

namespace AVRegularity.CycleWords.Assembly

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

/-- A chain on `[a, b]` is a chain on `[a, t]` for `t ≤ b`. -/
theorem zawChainFrom_mono {cd : PlaneChainData ι h D N} {κ : Fin (N + 1) → ι → ℕ} {a b t : ℝ}
    {v : ℝ → Vec 2 → Vec 2} {f : ∀ (j : Fin (N + 1)) (x : ι), PlaneHk Set.univ (κ j x) (h x)}
    {F : ∀ (j : Fin (N + 1)) (x : ι), ℝ →
      PlaneHk Set.univ (κ j x) (PiLp 2 (fun _ : Fin 2 => h x))}
    {u : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x)}
    {w : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x)}
    (hsol : IsPlaneChainFrom cd κ a b v f F u w) (ht : t ≤ b) :
    IsPlaneChainFrom cd κ a t v f F u w := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hsol
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht
  refine ⟨fun i => (h1 i).mono hsub, fun i => (h2 i).mono_measure (Measure.restrict_mono hsub le_rfl),
    fun i => ae_restrict_of_ae_restrict_of_subset hsub (h3 i), h4, ?_⟩
  intro i s hs φ
  exact h5 i s (hsub hs) φ

/-- If all coordinates of an `L²` class vanish against every test, the class vanishes. -/
theorem zawLp_ae_zero_of_pairing {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    (V : Lp E 2 (volume : Measure (Vec 2)))
    (hV : ∀ (e : E) (g : Lp ℝ 2 (volume : Measure (Vec 2))),
      inner ℝ (planeFiberCoordinateCLM e V) g = 0) : V =ᵐ[volume] 0 := by
  have hc : ∀ e : E, planeFiberCoordinateCLM e V = 0 := fun e =>
    inner_self_eq_zero.mp (hV e _)
  let b := stdOrthonormalBasis ℝ E
  have hae : ∀ᵐ y ∂(volume : Measure (Vec 2)), ∀ i, inner ℝ (b i) (V y) = 0 := by
    refine ae_all_iff.mpr fun i => ?_
    have h1 := (InnerProductSpace.toDual ℝ E (b i)).coeFn_compLpL V
    have h0 : (InnerProductSpace.toDual ℝ E (b i)).compLpL 2 (volume : Measure (Vec 2)) V = 0 :=
      hc (b i)
    rw [h0] at h1
    filter_upwards [h1, Lp.coeFn_zero ℝ 2 (volume : Measure (Vec 2))] with y hy1 hy2
    have := hy1.symm.trans hy2
    simpa using this
  filter_upwards [hae] with y hy
  have := b.sum_repr' (V y)
  simp only [hy, zero_smul, Finset.sum_const_zero] at this
  simpa using this.symm

/-- **A successor level with zero datum and vanishing forcing vanishes at every time.** -/
theorem zawLevel_succ_zero (hD : 2 ≤ D)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (letters : Fin N → CycleLetter ι h D) (X0 : Vec 2) (δ : ℝ)
    (κ : Fin (N + 1) → ι → ℕ) (a b : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (M : ℝ)
    (hb : ∀ t x, ∑ k, v t x k ^ 2 ≤ M ^ 2)
    (f : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (U : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (Uw : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hsol : IsPlaneChainFrom (wordChainData G letters X0 δ) κ a b v
      (fun j x => f (j, x)) (fun _ _ _ => 0)
      (fun j x => U (j, x)) (fun j x => Uw (j, x)))
    (j : Fin N) (x : ι) (hf : f (j.succ, x) = 0)
    (hflux : ∀ᵐ r ∂volume.restrict (Icc a b), ∀ᵐ z ∂volume,
      wordChainPreviousFlux letters X0 δ κ (fun p => Uw p r) (j.succ, x) r z = 0) :
    ∀ t ∈ Icc a b, planeValue (U (j.succ, x) t) =ᵐ[volume] 0 := by
  intro t ht
  have hsolt := zawChainFrom_mono hsol ht.2
  have hfl := ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc_right ht.2) hflux
  have hS : ∀ᵐ r ∂volume.restrict (Icc a t), ∀ k,
      (fun _ : ℝ => (0 : PlaneFluxL2 (h x))) r k =ᵐ[volume]
        fun z => wordChainPreviousFlux letters X0 δ κ (fun p => Uw p r) (j.succ, x) r z k := by
    filter_upwards [hfl] with r hr k
    filter_upwards [hr] with z hz
    simp [hz]
  have hSl : MemLp (fun _ : ℝ => (0 : PlaneFluxL2 (h x))) 2 (volume.restrict (Icc a t)) :=
    MemLp.zero'
  have key := fun e g => wordChainCoordinateNative_duhamel hD G hG letters X0 δ κ a t ht.1 v hv M hb
    f U Uw hsolt (j.succ, x) (fun _ => 0) hSl hS e g
  have hV := zawLp_ae_zero_of_pairing (planeHkValueOperator (κ j.succ x) (U (j.succ, x) t))
    (fun e g => by
      have := key e g
      simp only [hf] at this
      simpa using this)
  exact (planeValueLp_ae _).symm.trans hV

end AVRegularity.CycleWords.Assembly
end
end
end
