-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Weighted.SourcePairProjectionLimit
import AVRegularity.CycleComparison.Residual.ChartTransport.Piola
import AVRegularity.CycleComparison.Residual.CoarseFluxDiff.SlowJet
import AVRegularity.CycleComparison.Residual.Jets.Lift
public import AVRegularity.Weighted.PlaneIntervalCoefficients
public import AVRegularity.Weighted.JointRegularityBoxSmooth
public import AVRegularity.KernelEnergy.TorusMultiplierCLM
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Combinatorics.SimpleGraph.Basic

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.ChartTransport
namespace AVRegularity.Weighted

/-! The complete fast derivative tensor of each slow Taylor basis coefficient has a mixed-jet bound. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem slow_basis_full_fast_jet_bound {r j : ℕ} (f : Vec 2 → Vec 2 → E)
    (hf : IsBoxSmooth r j f) (w : DerivativeWord2 r) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ j (fun z' => iteratedFDeriv ℝ r (fun X' => f X' z') X
      (fun i => basisVec (w i))) z‖ ≤
      (2 : ℝ) ^ j * ‖iteratedFDeriv ℝ r (fun X' => iteratedFDeriv ℝ j (f X') z) X‖ := by
  have hc : ContDiff ℝ (j : ℕ∞)
      (fun z' => iteratedFDeriv ℝ r (fun X' => f X' z') X (fun i => basisVec (w i))) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin r => Vec 2) E
      (fun i => basisVec (w i))).contDiff.comp (CoarseFluxDiff.contDiff_slowJet hf X)
  calc
    _ ≤ ∑ δ : DerivativeWord2 j, ‖orderedDerivative δ
        (fun z' => iteratedFDeriv ℝ r (fun X' => f X' z') X (fun i => basisVec (w i))) z‖ :=
      norm_iteratedFDeriv_le_sum_words hc z
    _ ≤ ∑ _δ : DerivativeWord2 j,
        ‖iteratedFDeriv ℝ r (fun X' => iteratedFDeriv ℝ j (f X') z) X‖ :=
      Finset.sum_le_sum (fun δ _ => slow_basis_fast_word_bound f hf w δ X z)
    _ = _ := by
      rw [Finset.sum_const, card_derivativeWord2]
      simp

end AVRegularity.Weighted
end
end

section
section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev MeasureTheory
namespace AVRegularity.Weighted

/-! Entrywise linear expansion of the metric acting on the stored length-one words. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

def metricWordEntry {a b : ι} (m : ℕ) (hab : a = b) (hm : m = 1) (k j : Fin 2) :=
  metricFlux (h := h) (Matrix.single k j 1) m hab hm

theorem metricFlux_entry_expansion (M : Matrix (Fin 2) (Fin 2) ℝ)
    {a b : ι} (m : ℕ) (hab : a = b) (hm : m = 1) :
    metricFlux (h := h) M m hab hm =
      ∑ k : Fin 2, ∑ j : Fin 2, M k j • metricWordEntry (h := h) m hab hm k j := by
  subst hab hm
  apply ContinuousLinearMap.ext
  intro U
  apply PiLp.ext
  intro k
  fin_cases k <;> simp [metricFlux, metricWordEntry, Fin.sum_univ_two, Matrix.single]

theorem metricFlux_contDiff {K : ℕ} (M : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hM : ∀ k j, ContDiff ℝ (K : ℕ) (fun x => M x k j))
    {a b : ι} (m : ℕ) (hab : a = b) (hm : m = 1) :
    ContDiff ℝ (K : ℕ) (fun x => metricFlux (h := h) (M x) m hab hm) := by
  simp_rw [metricFlux_entry_expansion]
  apply ContDiff.sum
  intro k _
  apply ContDiff.sum
  intro j _
  exact (hM k j).smul_const _

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Order-zero and order-one coefficient arrays have elementary uniform operator bounds. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem planeH1_coefficient_array_bound
    (C : Vec 2 → E →L[ℝ] E) {M : ℝ} (hM : 0 ≤ M)
    (hc : ∀ x, ‖C x‖ ≤ M) (hd : ∀ x, ‖fderiv ℝ C x‖ ≤ M)
    (l : Fin 2) (x : Vec 2) : ‖coefficientDerivativeArray C l.val x‖ ≤ 2 * M := by
  have hw (w : DerivativeWord2 l.val) : ‖orderedCoefficientDerivative C l.val w x‖ ≤ M := by
    fin_cases l
    · exact hc x
    · change ‖fderiv ℝ C x (basisVec (w (Fin.last 0)))‖ ≤ M
      calc
        _ ≤ ‖fderiv ℝ C x‖ * ‖basisVec (w (Fin.last 0))‖ := (fderiv ℝ C x).le_opNorm _
        _ = ‖fderiv ℝ C x‖ := by simp [basisVec, Pi.norm_single]
        _ ≤ M := hd x
  have hcard : (Fintype.card (DerivativeWord2 l.val) : ℝ) ≤ 2 := by
    fin_cases l <;> norm_num [DerivativeWord2, Fintype.card_fun]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  have hs : ‖coefficientDerivativeArray C l.val x z‖ ^ 2 ≤ 2 * (M * ‖z‖) ^ 2 := by
    rw [coefficientDerivativeArray_normSq]
    calc
      _ ≤ ∑ _w : DerivativeWord2 l.val, (M * ‖z‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro w _
        apply pow_le_pow_left₀ (norm_nonneg _) _ 2
        exact ((orderedCoefficientDerivative C l.val w x).le_opNorm z).trans
          (mul_le_mul_of_nonneg_right (hw w) (norm_nonneg z))
      _ = (Fintype.card (DerivativeWord2 l.val) : ℝ) * (M * ‖z‖) ^ 2 := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
  have hn := norm_nonneg (coefficientDerivativeArray C l.val x z)
  have hm : 0 ≤ M * ‖z‖ := mul_nonneg hM (norm_nonneg z)
  nlinarith [sq_nonneg (M * ‖z‖)]

end AVRegularity.Weighted
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity.Weighted

/-! Relative gradient and flux bounds for bounded truncations of `ChartWeights`. -/

/-- Comparability at the chart center forces every chart comparison constant
to be at least one. -/
theorem chartWeights_constant_ge_one
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {t₀ S ϖ : ℝ} {zc : Vec 2} {M : ℕ} {Cw : ℕ → ℝ}
    (W : ChartWeights G v t₀ S ϖ zc M Cw) (m : ℕ) (hm : m ≤ M)
    (t : ℝ) (ht : t ∈ Set.Icc t₀ (t₀ + S)) :
    1 ≤ Cw m := by
  have hcomp := W.comparable m hm t ht zc
  have hlow : (Cw m)⁻¹ ≤ W.W m t zc := by
    simpa using hcomp.1
  have hupp : W.W m t zc ≤ Cw m := by
    simpa using hcomp.2
  have hCpos : 0 < Cw m := lt_of_lt_of_le (W.pos m hm t zc) hupp
  have hInv : (Cw m)⁻¹ ≤ Cw m := hlow.trans hupp
  have hmul := mul_le_mul_of_nonneg_right hInv hCpos.le
  have hmul' : 1 ≤ Cw m * Cw m := by
    simpa [inv_mul_cancel₀ hCpos.ne'] using hmul
  nlinarith

/-- The polynomial moment is bounded by the chart weight, with its
displayed comparison constant. -/
theorem chartWeights_polynomial_le_comparisonWeight
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {t₀ S ϖ : ℝ} {zc : Vec 2} {M : ℕ} {Cw : ℕ → ℝ}
    (W : ChartWeights G v t₀ S ϖ zc M Cw) (m : ℕ) (hm : m ≤ M)
    (t : ℝ) (ht : t ∈ Set.Icc t₀ (t₀ + S)) (z : Vec 2) :
    (1 + ϖ ^ 2 * ((z 0 - zc 0) ^ 2 + (z 1 - zc 1) ^ 2)) ^ m ≤
      Cw m * W.W m t z := by
  have hcomp := (W.comparable m hm t ht z).1
  have hupperCenter : W.W m t zc ≤ Cw m := by
    simpa using (W.comparable m hm t ht zc).2
  have hCpos : 0 < Cw m := lt_of_lt_of_le (W.pos m hm t zc) hupperCenter
  calc
    (1 + ϖ ^ 2 * ((z 0 - zc 0) ^ 2 + (z 1 - zc 1) ^ 2)) ^ m =
        Cw m * ((Cw m)⁻¹ *
          (1 + ϖ ^ 2 * ((z 0 - zc 0) ^ 2 + (z 1 - zc 1) ^ 2)) ^ m) := by
            field_simp [ne_of_gt hCpos]
    _ ≤ Cw m * W.W m t z := mul_le_mul_of_nonneg_left hcomp hCpos.le

/-- The clipped weight gradient and clipped defect flux retain the logarithmic
square bound required in the energy test. -/
theorem chartWeights_clipped_gradient_flux_bound
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {t₀ S ϖ : ℝ} {zc : Vec 2} {M : ℕ} {Cw : ℕ → ℝ}
    (W : ChartWeights G v t₀ S ϖ zc M Cw) (m : ℕ) (hm : m ≤ M)
    (t : ℝ) (ht : t ∈ Set.Icc t₀ (t₀ + S)) (z : Vec 2) (B : ℝ) (hB : 0 < B) :
    (∑ i : Fin 2,
      (clipWeightDeriv B (W.W m t z) *
        fderiv ℝ (W.W m t) z (basisVec i)) ^ 2) /
        (clipWeight B (W.W m t z)) ^ 2 +
      (∑ i : Fin 2, (clipWeightDeriv B (W.W m t z) * W.Phi m t z i) ^ 2) /
        (clipWeight B (W.W m t z)) ^ 2 ≤ W.lam m := by
  have hpos := W.pos m hm t z
  have hgrad := clipWeight_scaled_vec_sq_le B (W.W m t z) hB hpos
    (fun i : Fin 2 => fderiv ℝ (W.W m t) z (basisVec i))
  have hflux := clipWeight_scaled_vec_sq_le B (W.W m t z) hB hpos
    (fun i : Fin 2 => W.Phi m t z i)
  have hbound := W.bound m hm t ht z
  have hsum := add_le_add hgrad hflux
  have hsum' :
      (∑ i : Fin 2,
        (clipWeightDeriv B (W.W m t z) *
          fderiv ℝ (W.W m t) z (basisVec i)) ^ 2) /
          (clipWeight B (W.W m t z)) ^ 2 +
        (∑ i : Fin 2,
          (clipWeightDeriv B (W.W m t z) * W.Phi m t z i) ^ 2) /
          (clipWeight B (W.W m t z)) ^ 2 ≤
      (∑ i : Fin 2, (fderiv ℝ (W.W m t) z (basisVec i)) ^ 2) /
          (W.W m t z) ^ 2 +
        (∑ i : Fin 2, (W.Phi m t z i) ^ 2) /
          (W.W m t z) ^ 2 := by
    simpa using hsum
  exact hsum'.trans hbound

/-- The preceding estimate with the actual derivative of the composed clipped
weight. -/
theorem chartWeights_clipped_actual_gradient_flux_bound
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {t₀ S ϖ : ℝ} {zc : Vec 2} {M : ℕ} {Cw : ℕ → ℝ}
    (W : ChartWeights G v t₀ S ϖ zc M Cw) (m : ℕ) (hm : m ≤ M)
    (t : ℝ) (ht : t ∈ Set.Icc t₀ (t₀ + S)) (z : Vec 2) (B : ℝ) (hB : 0 < B) :
    (∑ i : Fin 2,
      (fderiv ℝ (fun y => clipWeight B (W.W m t y)) z (basisVec i)) ^ 2) /
        (clipWeight B (W.W m t z)) ^ 2 +
      (∑ i : Fin 2, (clipWeightDeriv B (W.W m t z) * W.Phi m t z i) ^ 2) /
        (clipWeight B (W.W m t z)) ^ 2 ≤ W.lam m := by
  have hslice : ContDiff ℝ 2 (fun y : Vec 2 => W.W m t y) := by
    convert (W.smooth m hm).1.comp (contDiff_const.prodMk contDiff_id) using 1 <;> rfl
  have hdiff : DifferentiableAt ℝ (fun y : Vec 2 => W.W m t y) z :=
    hslice.differentiable (by norm_num) z
  have hwd : HasFDerivAt (fun y : Vec 2 => W.W m t y)
      (fderiv ℝ (fun y : Vec 2 => W.W m t y) z) z := hdiff.hasFDerivAt
  have hcompose := clipWeight_comp_fderiv B hB (W.pos m hm t z) hwd
  have hbase := chartWeights_clipped_gradient_flux_bound W m hm t ht z B hB
  simpa [hcompose] using hbase

/-- The product of the clipped weight's second derivative with the chart
gradient-flux cross term is bounded by the clipped weight defect. -/
theorem chartWeights_clipped_second_cross_bound
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {t₀ S ϖ : ℝ} {zc : Vec 2} {M : ℕ} {Cw : ℕ → ℝ}
    (W : ChartWeights G v t₀ S ϖ zc M Cw) (m : ℕ) (hm : m ≤ M)
    (t : ℝ) (ht : t ∈ Set.Icc t₀ (t₀ + S)) (z : Vec 2) (B : ℝ) (hB : 0 < B) :
    |clipWeightSecondDeriv B (W.W m t z)| *
        |∑ i : Fin 2, fderiv ℝ (W.W m t) z (basisVec i) * W.Phi m t z i| ≤
      W.lam m * clipWeight B (W.W m t z) := by
  have hpos := W.pos m hm t z
  have hlam := (W.lam_bound m hm).1
  exact clipWeight_second_cross_le hB hpos hlam
    (fun i : Fin 2 => fderiv ℝ (W.W m t) z (basisVec i))
    (fun i : Fin 2 => W.Phi m t z i) (W.bound m hm t ht z)

/-- Substituting the chart defect and ellipticity into the clipped-operator
algebra gives a pointwise defect inequality for the truncated weight. -/
theorem chartWeights_clipped_operator_arithmetic
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {t₀ S ϖ : ℝ} {zc : Vec 2} {M : ℕ} {Cw : ℕ → ℝ}
    (W : ChartWeights G v t₀ S ϖ zc M Cw) (m : ℕ) (hm : m ≤ M)
    (t : ℝ) (ht : t ∈ Set.Icc t₀ (t₀ + S)) (z : Vec 2) (B g : ℝ)
    (hB : 0 < B) (hg4 : g ≤ 1 / 4) (hG : IsMetricNearIdentity G g) :
    let grad : Fin 2 → ℝ := fun i => fderiv ℝ (W.W m t) z (basisVec i)
    let defectL : ℝ := deriv (fun s => W.W m s z) t +
      (∑ i : Fin 2, v t z i * grad i) +
      (∑ i : Fin 2, fderiv ℝ (fun z' =>
        ∑ j : Fin 2, G t z' i j * fderiv ℝ (W.W m t) z' (basisVec j)) z (basisVec i))
    let fluxDiv : ℝ := ∑ i : Fin 2,
      fderiv ℝ (fun z' => W.Phi m t z' i) z (basisVec i)
    let ellipticCross : ℝ := ∑ i : Fin 2, ∑ j : Fin 2,
      grad i * G t z i j * grad j
    let fluxCross : ℝ := ∑ i : Fin 2, grad i * W.Phi m t z i
    clipWeightDeriv B (W.W m t z) * defectL +
        clipWeightSecondDeriv B (W.W m t z) * ellipticCross ≤
      2 * W.lam m * clipWeight B (W.W m t z) +
        clipWeightDeriv B (W.W m t z) * fluxDiv +
        clipWeightSecondDeriv B (W.W m t z) * fluxCross := by
  dsimp
  let grad : Fin 2 → ℝ := fun i => fderiv ℝ (W.W m t) z (basisVec i)
  let defectL : ℝ := deriv (fun s => W.W m s z) t +
    (∑ i : Fin 2, v t z i * grad i) +
    (∑ i : Fin 2, fderiv ℝ (fun z' =>
      ∑ j : Fin 2, G t z' i j * fderiv ℝ (W.W m t) z' (basisVec j)) z (basisVec i))
  let fluxDiv : ℝ := ∑ i : Fin 2,
    fderiv ℝ (fun z' => W.Phi m t z' i) z (basisVec i)
  let ellipticCross : ℝ := ∑ i : Fin 2, ∑ j : Fin 2,
    grad i * G t z i j * grad j
  let fluxCross : ℝ := ∑ i : Fin 2, grad i * W.Phi m t z i
  have hpos := W.pos m hm t z
  have hlam := (W.lam_bound m hm).1
  have ha := clipWeightDeriv_nonneg hB hpos
  have hscale := clipWeight_scaled_deriv_le hB hpos
  have hscale' : clipWeightDeriv B (W.W m t z) * W.W m t z ≤
      clipWeight B (W.W m t z) := by nlinarith [hscale]
  have hbase : defectL ≤ W.lam m * W.W m t z + fluxDiv := by
    simpa [defectL, fluxDiv, grad] using W.defect m hm t ht z
  have hmetric := nearIdentity_quadratic_bounds G g hg4 hG t z grad
  have hgradSq : 0 ≤ ∑ i : Fin 2, (grad i) ^ 2 := by positivity
  have helliptic : clipWeightSecondDeriv B (W.W m t z) * ellipticCross ≤ 0 := by
    have hq : 0 ≤ ellipticCross := by
      dsimp [ellipticCross]
      exact le_trans (by positivity : 0 ≤ (3 / 4 : ℝ) * ∑ i : Fin 2, (grad i) ^ 2)
        hmetric.1
    exact mul_nonpos_of_nonpos_of_nonneg
      (clipWeightSecondDeriv_nonpos hB hpos) hq
  have hcross := chartWeights_clipped_second_cross_bound W m hm t ht z B hB
  exact clippedOperator_defect_bound hlam ha hscale' hbase helliptic hcross

/-- Pointwise differential inequality for the actual bounded composition of a
chart weight: the clipping step in rigorous form. -/
theorem chartWeights_clipped_defect
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {t₀ S ϖ : ℝ} {zc : Vec 2} {M : ℕ} {Cw : ℕ → ℝ}
    (W : ChartWeights G v t₀ S ϖ zc M Cw) (m : ℕ) (hm : m ≤ M)
    (t : ℝ) (ht : t ∈ Set.Icc t₀ (t₀ + S)) (z : Vec 2) (B g : ℝ)
    (hB : 0 < B) (hg4 : g ≤ 1 / 4) (hG : IsMetricNearIdentity G g)
    (Kmax : ℕ)
    (hG_smooth : ∀ i j : Fin 2,
      ContDiff ℝ (max Kmax 1 : ℕ) (fun y => G t y i j)) :
    deriv (fun s => clipWeight B (W.W m s z)) t +
      (∑ i : Fin 2, v t z i *
        fderiv ℝ (fun y => clipWeight B (W.W m t y)) z (basisVec i)) +
      (∑ i : Fin 2, fderiv ℝ (fun y =>
        ∑ j : Fin 2, G t y i j *
          fderiv ℝ (fun y' => clipWeight B (W.W m t y')) y (basisVec j)) z (basisVec i)) ≤
      2 * W.lam m * clipWeight B (W.W m t z) +
        (∑ i : Fin 2, fderiv ℝ (fun y =>
          clipWeightDeriv B (W.W m t y) * W.Phi m t y i) z (basisVec i)) := by
  let w : Vec 2 → ℝ := fun y => W.W m t y
  let Gt : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ := fun y => G t y
  let grad : Fin 2 → ℝ := fun i => fderiv ℝ w z (basisVec i)
  let coeff : Vec 2 → ℝ := fun y => clipWeightDeriv B (W.W m t y)
  let fluxDiv : ℝ := ∑ i : Fin 2,
    fderiv ℝ (fun y => W.Phi m t y i) z (basisVec i)
  let fluxCross : ℝ := ∑ i : Fin 2, grad i * W.Phi m t z i
  let ellipticCross : ℝ := ∑ i : Fin 2, ∑ j : Fin 2,
    grad i * G t z i j * grad j
  have hpos := W.pos m hm t z
  have hWspace : ContDiff ℝ 2 w := by
    convert (W.smooth m hm).1.comp (contDiff_const.prodMk contDiff_id) using 1 <;> rfl
  have hWtime : ContDiff ℝ 2 (fun s : ℝ => W.W m s z) := by
    convert (W.smooth m hm).1.comp (contDiff_id.prodMk contDiff_const) using 1 <;> rfl
  have hwd : ∀ y, HasFDerivAt w (fderiv ℝ w y) y := by
    intro y
    exact (hWspace.differentiable (by norm_num) y).hasFDerivAt
  have hclipGrad (i : Fin 2) :
      fderiv ℝ (fun y => clipWeight B (w y)) z (basisVec i) =
        clipWeightDeriv B (w z) * grad i := by
    simpa [grad, w] using congrArg (fun L : Vec 2 →L[ℝ] ℝ => L (basisVec i))
      (clipWeight_comp_fderiv B hB (W.pos m hm t z) (hwd z))
  have htimeDeriv : HasDerivAt (fun s : ℝ => W.W m s z)
      (deriv (fun s => W.W m s z) t) t :=
    (hWtime.differentiable (by norm_num) t).hasDerivAt
  have htimeComp := (hasDerivAt_clipWeight hB hpos).comp t htimeDeriv
  have htimeEq : deriv (fun s => clipWeight B (W.W m s z)) t =
      clipWeightDeriv B (W.W m t z) * deriv (fun s => W.W m s z) t := by
    convert htimeComp.deriv using 1
    rfl
  have htransport :
      (∑ i : Fin 2, v t z i *
        fderiv ℝ (fun y => clipWeight B (w y)) z (basisVec i)) =
      clipWeightDeriv B (W.W m t z) *
        (∑ i : Fin 2, v t z i * grad i) := by
    calc
      _ = ∑ i : Fin 2, clipWeightDeriv B (W.W m t z) * (v t z i * grad i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hclipGrad i]
        ring
      _ = _ := by rw [Finset.mul_sum]
  have hgradCont (j : Fin 2) : ContDiff ℝ 1
      (fun y => fderiv ℝ w y (basisVec j)) := by
    have hWtwo : ContDiff ℝ ((1 + 1 : ℕ) : ℕ∞) w := by
      simpa using hWspace
    have hjoint := hWtwo.contDiff_fderiv_apply (m := 1) le_rfl
    simpa [Function.comp_def] using
      hjoint.comp (contDiff_id.prodMk contDiff_const)
  have hGorder : (1 : WithTop ℕ∞) ≤ ((max Kmax 1 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast (Nat.le_max_right Kmax 1)
  have hrowCont (i : Fin 2) : ContDiff ℝ 1 (weightFluxRow Gt w i) := by
    change ContDiff ℝ 1 (fun y =>
      ∑ j ∈ Finset.univ, G t y i j * fderiv ℝ w y (basisVec j))
    apply ContDiff.sum
    intro j hj
    exact (hG_smooth i j).of_le hGorder |>.mul (hgradCont j)
  have hfluxd (i : Fin 2) : HasFDerivAt (weightFluxRow Gt w i)
      (fderiv ℝ (weightFluxRow Gt w i) z) z :=
    (hrowCont i).differentiable (by norm_num) z |>.hasFDerivAt
  have hdiffusion :
      (∑ i : Fin 2, fderiv ℝ (fun y =>
        ∑ j : Fin 2, G t y i j *
          fderiv ℝ (fun y' => clipWeight B (w y')) y (basisVec j)) z (basisVec i)) =
      clipWeightDeriv B (W.W m t z) *
          (∑ i : Fin 2, fderiv ℝ (weightFluxRow Gt w i) z (basisVec i)) +
        clipWeightSecondDeriv B (W.W m t z) * ellipticCross := by
    have h := clippedWeightMetricDivergence_eq B hB Gt w z
      (fun y => W.pos m hm t y) hwd hfluxd
    have hq :
        (∑ i : Fin 2, fderiv ℝ w z (basisVec i) * weightFluxRow Gt w i z) =
          ellipticCross := by
      simp [weightFluxRow, ellipticCross, Gt, w, grad, Fin.sum_univ_two]
      ring
    change clippedWeightMetricDivergence B Gt w z = _
    rw [hq] at h
    exact h
  have hrowEq (i : Fin 2) : weightFluxRow Gt w i = fun y =>
      ∑ j : Fin 2, G t y i j * fderiv ℝ (W.W m t) y (basisVec j) := by
    funext y
    rfl
  have hdivOldEq :
      (∑ i : Fin 2, fderiv ℝ (weightFluxRow Gt w i) z (basisVec i)) =
        (∑ i : Fin 2, fderiv ℝ (fun y =>
          ∑ j : Fin 2, G t y i j * fderiv ℝ (W.W m t) y (basisVec j)) z (basisVec i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (fun f : Vec 2 → ℝ => fderiv ℝ f z (basisVec i)) (hrowEq i)
  have hdiffusionExpanded := hdiffusion
  rw [hdivOldEq] at hdiffusionExpanded
  have hphiVec : ContDiff ℝ 1 (fun y : Vec 2 => W.Phi m t y) := by
    convert (W.smooth m hm).2.comp (contDiff_const.prodMk contDiff_id) using 1 <;> rfl
  have hphiCont (i : Fin 2) : ContDiff ℝ 1 (fun y => W.Phi m t y i) :=
    (contDiff_apply ℝ ℝ i).comp hphiVec
  have hphiwd (i : Fin 2) : HasFDerivAt (fun y => W.Phi m t y i)
      (fderiv ℝ (fun y => W.Phi m t y i) z) z :=
    (hphiCont i).differentiable (by norm_num) z |>.hasFDerivAt
  have hcoeffd : HasFDerivAt coeff
      (clipWeightSecondDeriv B (W.W m t z) • fderiv ℝ w z) z := by
    simpa [coeff, w] using
      hasFDerivAt_clipWeightDeriv_comp B hB hpos (hwd z)
  have hfluxDiv :
      (∑ i : Fin 2, fderiv ℝ (fun y => coeff y * W.Phi m t y i) z (basisVec i)) =
      clipWeightDeriv B (W.W m t z) * fluxDiv +
        clipWeightSecondDeriv B (W.W m t z) * fluxCross := by
    calc
      _ = ∑ i : Fin 2,
          (clipWeightDeriv B (W.W m t z) *
            fderiv ℝ (fun y => W.Phi m t y i) z (basisVec i) +
           W.Phi m t z i *
            (clipWeightSecondDeriv B (W.W m t z) * grad i)) := by
        apply Finset.sum_congr rfl
        intro i _
        have hmul := hcoeffd.mul (hphiwd i)
        change fderiv ℝ (coeff * (fun y => W.Phi m t y i)) z (basisVec i) = _
        rw [hmul.fderiv]
        simp only [add_apply, smul_apply]
        ring
      _ = clipWeightDeriv B (W.W m t z) * fluxDiv +
          clipWeightSecondDeriv B (W.W m t z) * fluxCross := by
        dsimp [fluxDiv, fluxCross]
        rw [Finset.sum_add_distrib]
        have hfactor :
            (∑ i : Fin 2, W.Phi m t z i *
              (clipWeightSecondDeriv B (W.W m t z) * grad i)) =
            clipWeightSecondDeriv B (W.W m t z) *
              ∑ i : Fin 2, grad i * W.Phi m t z i := by
          calc
            _ = ∑ i : Fin 2, clipWeightSecondDeriv B (W.W m t z) *
                (grad i * W.Phi m t z i) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
            _ = _ := by rw [Finset.mul_sum]
        rw [← Finset.mul_sum, hfactor]
  have harith := chartWeights_clipped_operator_arithmetic W m hm t ht z B g hB hg4 hG
  have hleft :
      deriv (fun s => clipWeight B (W.W m s z)) t +
        (∑ i : Fin 2, v t z i *
          fderiv ℝ (fun y => clipWeight B (W.W m t y)) z (basisVec i)) +
        (∑ i : Fin 2, fderiv ℝ (fun y =>
          ∑ j : Fin 2, G t y i j *
            fderiv ℝ (fun y' => clipWeight B (W.W m t y')) y (basisVec j)) z (basisVec i)) =
      clipWeightDeriv B (W.W m t z) *
        (deriv (fun s => W.W m s z) t +
        (∑ i : Fin 2, v t z i * grad i) +
          (∑ i : Fin 2, fderiv ℝ (fun y =>
            ∑ j : Fin 2, G t y i j * fderiv ℝ (W.W m t) y (basisVec j)) z (basisVec i))) +
        clipWeightSecondDeriv B (W.W m t z) * ellipticCross := by
    rw [htimeEq, htransport, hdiffusionExpanded]
    ring
  have hright :
      2 * W.lam m * clipWeight B (W.W m t z) +
        (∑ i : Fin 2, fderiv ℝ (fun y => coeff y * W.Phi m t y i) z (basisVec i)) =
      2 * W.lam m * clipWeight B (W.W m t z) +
        clipWeightDeriv B (W.W m t z) * fluxDiv +
        clipWeightSecondDeriv B (W.W m t z) * fluxCross := by
    rw [hfluxDiv]
    ring
  calc
    _ = clipWeightDeriv B (W.W m t z) *
          (deriv (fun s => W.W m s z) t +
            (∑ i : Fin 2, v t z i * grad i) +
            (∑ i : Fin 2, fderiv ℝ (fun y =>
              ∑ j : Fin 2, G t y i j * fderiv ℝ (W.W m t) y (basisVec j)) z (basisVec i))) +
        clipWeightSecondDeriv B (W.W m t z) * ellipticCross := hleft
    _ ≤ 2 * W.lam m * clipWeight B (W.W m t z) +
        clipWeightDeriv B (W.W m t z) * fluxDiv +
        clipWeightSecondDeriv B (W.W m t z) * fluxCross := by
      simpa [grad, fluxDiv, fluxCross, ellipticCross, Gt, w] using harith
    _ = _ := hright.symm

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Uniform Sobolev multiplier bounds for compact space-time coefficients. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem compactH1Coefficient_bounds
    (C : ℝ × Vec 2 → E →L[ℝ] E) (hC : ContDiff ℝ 1 C) (hs : HasCompactSupport C) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t l x,
      ‖coefficientDerivativeArray (fun z => C (t, z)) (l : Fin 2).val x‖ ≤ 2 * M := by
  obtain ⟨M0, h0⟩ := hC.continuous.bounded_above_of_compact_support hs
  obtain ⟨M1, h1⟩ := (hC.continuous_fderiv (by norm_num)).bounded_above_of_compact_support
    (hs.fderiv ℝ)
  let M := max 0 (max M0 M1)
  have hM : 0 ≤ M := le_max_left _ _
  have hb0 t x : ‖C (t, x)‖ ≤ M :=
    (h0 (t, x)).trans ((le_max_left M0 M1).trans (le_max_right _ _))
  have hb1 t x : ‖fderiv ℝ (fun z => C (t, z)) x‖ ≤ M := by
    have he := (hasFDerivAt_const (𝕜 := ℝ) (x := x) t).prodMk (hasFDerivAt_id (𝕜 := ℝ) x)
    have hd := (hC.differentiable (by norm_num) (t,x)).hasFDerivAt.comp x he
    have hnorm : ‖(fderiv ℝ C (t,x)).comp
        ((0 : Vec 2 →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (Vec 2)))‖ ≤ M := by
      apply ContinuousLinearMap.opNorm_le_bound _ hM
      intro z
      calc
        _ ≤ ‖fderiv ℝ C (t,x)‖ * ‖(0, z)‖ := (fderiv ℝ C (t,x)).le_opNorm _
        _ ≤ M * ‖z‖ := by
          simp only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg z)]
          exact mul_le_mul_of_nonneg_right
            ((h1 (t,x)).trans ((le_max_right M0 M1).trans (le_max_right _ _))) (norm_nonneg z)
    convert hnorm using 1
    exact congrArg norm hd.fderiv
  exact ⟨M, hM, fun t l x => planeH1_coefficient_array_bound _ hM (hb0 t) (hb1 t) l x⟩

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.Weighted

/-! The pointwise compact-test residual uses only metric entry bounds. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem cutoff_chart_flux_norm_bound
    (G : Matrix (Fin 2) (Fin 2) ℝ) (hG : ∀ i j, |G i j| ≤ 5 / 4)
    (v p Φ : PiLp 2 (fun _ : Fin 2 => ℝ)) {q r M : ℝ}
    (hq : 0 ≤ q) (_hr : 0 ≤ r) (_hM : 0 ≤ M)
    (hv : ‖v‖ ≤ 2 * M) (hp : ‖p‖ ≤ r * q) (hΦ : ‖Φ‖ ≤ r * q) :
    ‖q • v + finiteMetricFlux G p - Φ‖ ≤ q * (2 * M + 6 * r) := by
  calc
    _ ≤ ‖q • v + finiteMetricFlux G p‖ + ‖Φ‖ := norm_sub_le _ _
    _ ≤ ‖q • v‖ + ‖finiteMetricFlux G p‖ + ‖Φ‖ := by
      gcongr; exact norm_add_le _ _
    _ ≤ q * (2 * M) + 5 * (r * q) + r * q := by
      rw [norm_smul, Real.norm_of_nonneg hq]
      gcongr
      exact (finiteMetricFlux_norm_le G hG p).trans (by gcongr)
    _ = _ := by ring

theorem cutoff_residual_bound
    (G : Matrix (Fin 2) (Fin 2) ℝ) (hG : ∀ i j, |G i j| ≤ 5 / 4)
    (v p Φ h : PiLp 2 (fun _ : Fin 2 => ℝ))
    (du F : PiLp 2 (fun _ : Fin 2 => E)) (u : E)
    {q r M χ η : ℝ} (hq : 0 ≤ q) (hr : 0 ≤ r) (hM : 0 ≤ M)
    (hχ : 0 ≤ χ) (hη : 0 ≤ η)
    (hv : ‖v‖ ≤ 2 * M) (hp : ‖p‖ ≤ r * q) (hΦ : ‖Φ‖ ≤ r * q)
    (hh : ‖h‖ ≤ 2 * η) :
    2 * χ * inner ℝ h (q • v + finiteMetricFlux G p - Φ) * ‖u‖ ^ 2 -
      2 * χ ^ 2 * inner ℝ du (scalarHilbertTensor Φ u) -
      4 * χ * q * inner ℝ du (scalarHilbertTensor (finiteMetricFlux G h) u) -
      2 * χ ^ 2 * q * inner ℝ F du -
      2 * χ ^ 2 * inner ℝ F (scalarHilbertTensor p u) -
      4 * χ * q * inner ℝ F (scalarHilbertTensor h u) ≤
    q * (8 * χ * η * M * ‖u‖ ^ 2 + 32 * χ * η * r * ‖u‖ ^ 2 +
      40 * χ * η * ‖du‖ * ‖u‖ + 2 * χ ^ 2 * r * ‖du‖ * ‖u‖ +
      2 * χ ^ 2 * ‖F‖ * ‖du‖ + 2 * χ ^ 2 * r * ‖F‖ * ‖u‖ +
      8 * χ * η * ‖F‖ * ‖u‖) := by
  have ha := inner_le_budgets h (q • v + finiteMetricFlux G p - Φ) hh
    (cutoff_chart_flux_norm_bound G hG v p Φ hq hr hM hv hp hΦ)
  have hb := neg_inner_le_budgets du (scalarHilbertTensor Φ u) le_rfl
    (show ‖scalarHilbertTensor Φ u‖ ≤ (r * q) * ‖u‖ by
      rw [scalarHilbertTensor_norm]; gcongr)
  have hg : ‖finiteMetricFlux G h‖ ≤ 10 * η :=
    (finiteMetricFlux_norm_le G hG h).trans (by linarith only [hh])
  have hc := neg_inner_le_budgets du (scalarHilbertTensor (finiteMetricFlux G h) u) le_rfl
    (show ‖scalarHilbertTensor (finiteMetricFlux G h) u‖ ≤ 10 * η * ‖u‖ by
      rw [scalarHilbertTensor_norm]; gcongr)
  have hd := neg_inner_le_budgets F du le_rfl le_rfl
  have he := neg_inner_le_budgets F (scalarHilbertTensor p u) le_rfl
    (show ‖scalarHilbertTensor p u‖ ≤ r * q * ‖u‖ by
      rw [scalarHilbertTensor_norm]; gcongr)
  have hf := neg_inner_le_budgets F (scalarHilbertTensor h u) le_rfl
    (show ‖scalarHilbertTensor h u‖ ≤ 2 * η * ‖u‖ by
      rw [scalarHilbertTensor_norm]; gcongr)
  have ha' := mul_le_mul_of_nonneg_left ha (show 0 ≤ 2 * χ * ‖u‖ ^ 2 by positivity)
  have hb' := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * χ ^ 2 by positivity)
  have hc' := mul_le_mul_of_nonneg_left hc (show 0 ≤ 4 * χ * q by positivity)
  have hd' := mul_le_mul_of_nonneg_left hd (show 0 ≤ 2 * χ ^ 2 * q by positivity)
  have he' := mul_le_mul_of_nonneg_left he (show 0 ≤ 2 * χ ^ 2 by positivity)
  have hf' := mul_le_mul_of_nonneg_left hf (show 0 ≤ 4 * χ * q by positivity)
  have hs : 0 ≤ χ * η * r * q * ‖u‖ ^ 2 := by positivity
  nlinarith only [ha', hb', hc', hd', he', hf', hs]

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Reducing the common scalar radius preserves the supplied weighted datum budget. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem geometryDataNorm_radius_mono (π : ι → ℝ) (κ : ι → ℕ)
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) {ρ r : ℝ} (hρ : 0 ≤ ρ) (hr : ρ ≤ r)
    (f : ∀ i, PlaneHk Set.univ (κ i) (h i)) :
    geometryDataNorm π κ n ϖ zc ρ f ≤ geometryDataNorm π κ n ϖ zc r f := by
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul' le_rfl (weightedFactorialNormSq_radius_mono n ϖ zc hρ hr (κ i) (f i))

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev MeasureTheory
namespace AVRegularity.Weighted

/-! Joint metric measurability gives measurability of its stored word coefficient. -/

variable {ι T : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [MeasurableSpace T]

theorem metricFlux_measurable (M : T → Matrix (Fin 2) (Fin 2) ℝ) (hM : Measurable M)
    {a b : ι} (m : ℕ) (hab : a = b) (hm : m = 1) :
    Measurable (fun x => metricFlux (h := h) (M x) m hab hm) := by
  have : IsBoundedSMul ℝ ((PiLp 2 (fun _ : DerivativeWord2 m => h b)) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h a)) := NormedSpace.toIsBoundedSMul (𝕜 := ℝ)
        (E := ((PiLp 2 (fun _ : DerivativeWord2 m => h b)) →L[ℝ]
          PiLp 2 (fun _ : Fin 2 => h a)))
  simp_rw [metricFlux_entry_expansion]
  apply Finset.measurable_sum
  intro k _
  apply Finset.measurable_sum
  intro j _
  exact ((measurable_pi_apply j).comp ((measurable_pi_apply k).comp hM)).smul_const _

end AVRegularity.Weighted
end
end

section
@[expose] public section
namespace AVRegularity.Weighted

/-! Young inequalities for the source terms in a clipped-weight energy test. -/

/-- A chart rate bounded by `Cw / S` produces a Gronwall factor controlled
only by the chart constant whenever the time window has length at most `S`. -/
theorem chart_weight_rate_exp_bound {S L Cw lam : ℝ}
    (hS : 0 < S) (hLS : L ≤ S)
    (hlam : 0 ≤ lam) (hrate : lam ≤ Cw / S) :
    Real.exp (lam * L) ≤ Real.exp Cw := by
  apply Real.exp_le_exp.mpr
  have hrateS : lam * S ≤ Cw := by
    have h := mul_le_mul_of_nonneg_right hrate hS.le
    have hcancel : (Cw / S) * S = Cw := by field_simp [ne_of_gt hS]
    rw [hcancel] at h
    exact h
  exact (mul_le_mul_of_nonneg_left hLS hlam).trans hrateS

/-! The chart defect rate produces a window-independent Gronwall factor. -/

theorem chart_interval_rate_exp_bound {t₀ S a b t lam C : ℝ}
    (ha : t₀ ≤ a) (hab : a ≤ b) (hb : b ≤ t₀ + S) (ht : t ∈ Set.Icc a b)
    (hlam : 0 ≤ lam) (hC : 0 ≤ C) (hrate : lam ≤ C / S) :
    Real.exp (18 * lam * (t - a)) ≤ Real.exp (18 * C) := by
  have hS : 0 ≤ S := by linarith only [ha, hab, hb]
  by_cases hzero : S = 0
  · have htime : t = a := by linarith only [ha, hab, hb, ht.1, ht.2, hzero]
    subst t
    simp only [sub_self, mul_zero, Real.exp_zero]
    exact Real.one_le_exp (mul_nonneg (by norm_num) hC)
  · have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hzero)
    apply chart_weight_rate_exp_bound hSpos (by linarith only [ha, hb, ht.2])
      (mul_nonneg (by norm_num) hlam)
    have hh := mul_le_mul_of_nonneg_left hrate (by norm_num : (0 : ℝ) ≤ 18)
    simpa only [mul_div_assoc] using hh

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization Set
namespace AVRegularity.Weighted

/-! Compact smooth square roots of bounded chart weights on a fixed time window. -/

def compactChartWeightRoot
    (τ : ℝ → ℝ) (χ : Vec 2 → ℝ) (B : ℝ) (w : ℝ × Vec 2 → ℝ) : ℝ × Vec 2 → ℝ :=
  fun p => τ p.1 * χ p.2 * Real.sqrt (clipWeight B (w p))

theorem clipped_field_contDiff (B : ℝ) (hB : 0 < B)
    (w : ℝ × Vec 2 → ℝ) (hw : ContDiff ℝ 2 w) (hp : ∀ p, 0 < w p) :
    ContDiff ℝ 2 (fun p => clipWeight B (w p)) :=
  (contDiff_const.mul hw).div (contDiff_const.add hw)
    (fun p => ne_of_gt (add_pos hB (hp p)))

theorem compactChartWeightRoot_contDiff
    (τ : ℝ → ℝ) (hτ : ContDiff ℝ 2 τ) (χ : Vec 2 → ℝ) (hχ : ContDiff ℝ 2 χ)
    (B : ℝ) (hB : 0 < B) (w : ℝ × Vec 2 → ℝ) (hw : ContDiff ℝ 2 w)
    (hp : ∀ p, 0 < w p) : ContDiff ℝ 2 (compactChartWeightRoot τ χ B w) := by
  have hclip : ContDiff ℝ 2 (fun p => clipWeight B (w p)) := by
    exact clipped_field_contDiff B hB w hw hp
  exact ((hτ.comp contDiff_fst).mul (hχ.comp contDiff_snd)).mul
    (hclip.sqrt (fun p => ne_of_gt (clipWeight_pos hB (hp p))))

theorem compactChartWeightRoot_hasCompactSupport
    (τ : ℝ → ℝ) (hτ : HasCompactSupport τ)
    (χ : Vec 2 → ℝ) (hχ : HasCompactSupport χ) (B : ℝ) (w : ℝ × Vec 2 → ℝ) :
    HasCompactSupport (compactChartWeightRoot τ χ B w) := by
  apply HasCompactSupport.of_support_subset_isCompact (hτ.isCompact.prod hχ.isCompact)
  intro p hp
  have hn : compactChartWeightRoot τ χ B w p ≠ 0 := hp
  have ht : τ p.1 ≠ 0 := by
    intro h
    apply hn
    simp only [compactChartWeightRoot, h, zero_mul]
  have hx : χ p.2 ≠ 0 := by
    intro h
    apply hn
    simp only [compactChartWeightRoot, h, mul_zero, zero_mul]
  exact ⟨subset_tsupport τ ht, subset_tsupport χ hx⟩

theorem compactChartWeightRoot_sq
    (τ : ℝ → ℝ) (χ : Vec 2 → ℝ) (B : ℝ) (hB : 0 < B)
    (w : ℝ × Vec 2 → ℝ) (hp : ∀ p, 0 < w p) (p : ℝ × Vec 2) :
    compactChartWeightRoot τ χ B w p ^ 2 = τ p.1 ^ 2 * χ p.2 ^ 2 * clipWeight B (w p) := by
  simp only [compactChartWeightRoot, mul_pow, Real.sq_sqrt (clipWeight_pos hB (hp p)).le]

theorem compactChartWeightRoot_time_production
    (τ : ℝ → ℝ) (hτ : ContDiff ℝ 2 τ) (χ : Vec 2 → ℝ) (hχ : ContDiff ℝ 2 χ)
    (B : ℝ) (hB : 0 < B) (w : ℝ × Vec 2 → ℝ) (hw : ContDiff ℝ 2 w)
    (hp : ∀ p, 0 < w p) (t : ℝ) (x : Vec 2)
    (hτ1 : τ t = 1) (hτ0 : HasDerivAt τ 0 t) :
    2 * compactChartWeightRoot τ χ B w (t,x) *
        fderiv ℝ (compactChartWeightRoot τ χ B w) (t,x) (1,0) =
      χ x ^ 2 * deriv (fun s => clipWeight B (w (s,x))) t := by
  have hpair := (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  have hf := compactChartWeightRoot_contDiff τ hτ χ hχ B hB w hw hp
  have hdF : HasDerivAt (fun s => compactChartWeightRoot τ χ B w (s,x))
      (fderiv ℝ (compactChartWeightRoot τ χ B w) (t,x) (1,0)) t := by
    convert (hf.differentiable (by norm_num) (t,x)).hasFDerivAt.comp_hasDerivAt t hpair using 1
    rfl
  have hdΨ : HasDerivAt (fun s => clipWeight B (w (s,x)))
      (deriv (fun s => clipWeight B (w (s,x))) t) t := by
    have hc : ContDiff ℝ 2 (fun s => clipWeight B (w (s,x))) :=
      (clipped_field_contDiff B hB w hw hp).comp (contDiff_id.prodMk contDiff_const)
    exact (hc.differentiable (by norm_num) t).hasDerivAt
  have hSq : (fun s => compactChartWeightRoot τ χ B w (s,x) ^ 2) =
      (fun s => (τ s ^ 2 * χ x ^ 2) * clipWeight B (w (s,x))) := by
    funext s
    exact compactChartWeightRoot_sq τ χ B hB w hp (s,x)
  have hdSq := ((hτ0.pow 2).mul_const (χ x ^ 2)).mul hdΨ
  have hdSq' : HasDerivAt (fun s => compactChartWeightRoot τ χ B w (s,x) ^ 2)
      (χ x ^ 2 * deriv (fun s => clipWeight B (w (s,x))) t) t := by
    convert hdSq using 1
    simp only [Pi.pow_apply, hτ1, one_pow, mul_zero, zero_mul, zero_add, one_mul]
  have he := (hdF.pow 2).unique hdSq'
  simpa only [show (2 : ℕ) - 1 = 1 from rfl, pow_one, Nat.cast_ofNat] using he

end AVRegularity.Weighted
end
end

section
@[expose] public section
open MeasureTheory Filter Homogenization
open scoped ENNReal Topology
namespace AVRegularity.Weighted

/-! Measurability and monotone-integral passage for clipped chart weights. -/

/-- Every positive rational clip of a chart weight is a continuous spatial function. -/
theorem chartWeights_clipped_continuous
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {t₀ S ϖ : ℝ} {zc : Vec 2} {M : ℕ} {Cw : ℕ → ℝ}
    (W : ChartWeights G v t₀ S ϖ zc M Cw) (m : ℕ) (hm : m ≤ M)
    (t B : ℝ) (hB : 0 < B) :
    Continuous (fun z => clipWeight B (W.W m t z)) := by
  have hW : Continuous (fun z : Vec 2 => W.W m t z) := by
    have hpair : Continuous (fun z : Vec 2 => (t, z)) := continuous_const.prodMk continuous_id
    exact (W.smooth m hm).1.continuous.comp hpair
  apply continuous_iff_continuousAt.mpr
  intro z
  exact (hasDerivAt_clipWeight hB (W.pos m hm t z)).continuousAt.comp (hW.continuousAt)

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Weighted

/-! Relative Hilbert norms of the clipped chart gradient and defect flux. -/

theorem two_log_norm_bounds (p f : Fin 2 → ℝ) {q lam : ℝ}
    (hq : 0 < q) (hlam : 0 ≤ lam)
    (h : (∑ i : Fin 2, (p i) ^ 2) / q ^ 2 +
      (∑ i : Fin 2, (f i) ^ 2) / q ^ 2 ≤ lam) :
    ‖(WithLp.toLp 2 p : PiLp 2 (fun _ : Fin 2 => ℝ))‖ ≤ Real.sqrt lam * q ∧
    ‖(WithLp.toLp 2 f : PiLp 2 (fun _ : Fin 2 => ℝ))‖ ≤ Real.sqrt lam * q := by
  have hs : (∑ i : Fin 2, (p i) ^ 2) + (∑ i : Fin 2, (f i) ^ 2) ≤ lam * q ^ 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hq)).mp
    simpa only [add_div] using h
  have hp := PiLp.norm_sq_eq_of_L2 _ (WithLp.toLp 2 p)
  have hf := PiLp.norm_sq_eq_of_L2 _ (WithLp.toLp 2 f)
  simp only [Real.norm_eq_abs, sq_abs] at hp hf
  have hr : (Real.sqrt lam * q) ^ 2 = lam * q ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hlam]
  have hr0 : 0 ≤ Real.sqrt lam * q := mul_nonneg (Real.sqrt_nonneg _) hq.le
  constructor
  · apply (sq_le_sq₀ (norm_nonneg _) hr0).mp
    rw [hr]
    nlinarith only [hs, hp, hf, sq_nonneg (‖(WithLp.toLp 2 f : PiLp 2 (fun _ : Fin 2 => ℝ))‖)]
  · apply (sq_le_sq₀ (norm_nonneg _) hr0).mp
    rw [hr]
    nlinarith only [hs, hp, hf, sq_nonneg (‖(WithLp.toLp 2 p : PiLp 2 (fun _ : Fin 2 => ℝ))‖)]

theorem chartWeights_clipped_log_norm_bounds
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {t₀ S ϖ : ℝ} {zc : Vec 2} {M : ℕ} {Cw : ℕ → ℝ}
    (W : ChartWeights G v t₀ S ϖ zc M Cw) (m : ℕ) (hm : m ≤ M)
    (t : ℝ) (ht : t ∈ Set.Icc t₀ (t₀ + S)) (z : Vec 2) (B : ℝ) (hB : 0 < B) :
    ‖(WithLp.toLp 2 (fun i => fderiv ℝ (fun y => clipWeight B (W.W m t y)) z
      (basisVec i)) : PiLp 2 (fun _ : Fin 2 => ℝ))‖ ≤
        Real.sqrt (W.lam m) * clipWeight B (W.W m t z) ∧
    ‖(WithLp.toLp 2 (fun i => clipWeightDeriv B (W.W m t z) * W.Phi m t z i) :
      PiLp 2 (fun _ : Fin 2 => ℝ))‖ ≤
        Real.sqrt (W.lam m) * clipWeight B (W.W m t z) :=
  two_log_norm_bounds _ _ (clipWeight_pos hB (W.pos m hm t z))
    (W.lam_bound m hm).1 (chartWeights_clipped_actual_gradient_flux_bound W m hm t ht z B hB)

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Weighted

/-! Ordered metric derivative masks preserve the exact complementary gradient array. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def metricMaskTerm {K j : ℕ} (hj : j ≤ K)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (D : RawJet2 (K + 1) E)
    (m : PositionMask j) (w : DerivativeWord2 j) (x : Vec 2) :
    PiLp 2 (fun _ : Fin 2 => E) :=
  finiteMetricFlux
    (fun k a => orderedScalarDerivative (fun y => G y k a) (maskLeftLength j m)
      (maskWordEquiv 2 j m w).1 x)
    (driftMaskGradient hj D m (maskWordEquiv 2 j m w).2 x)

theorem metricMaskTerm_pointwise_sumSq_le {K j : ℕ} (hj : j ≤ K)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (D : RawJet2 (K + 1) E)
    (m : PositionMask j) (x : Vec 2) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ w : DerivativeWord2 (maskLeftLength j m), ∀ k a,
      |orderedScalarDerivative (fun y => G y k a) (maskLeftLength j m) w x| ≤ M) :
    (∑ w : DerivativeWord2 j, ‖metricMaskTerm hj G D m w x‖ ^ 2) ≤
      (Fintype.card (DerivativeWord2 (maskLeftLength j m)) : ℝ) * (4 * M) ^ 2 *
        ∑ w : DerivativeWord2 (maskRightLength j m + 1),
          ‖D ⟨⟨maskRightLength j m + 1, by have := maskRightLength_le j m; omega⟩, w⟩ x‖ ^ 2 := by
  classical
  let f := fun p : DerivativeWord2 (maskLeftLength j m) × DerivativeWord2 (maskRightLength j m) =>
    ‖finiteMetricFlux
      (fun k a => orderedScalarDerivative (fun y => G y k a) (maskLeftLength j m) p.1 x)
      (driftMaskGradient hj D m p.2 x)‖ ^ 2
  have he : (∑ w : DerivativeWord2 j, ‖metricMaskTerm hj G D m w x‖ ^ 2) = ∑ p, f p :=
    Fintype.sum_equiv (maskWordEquiv 2 j m) _ _ (fun _ => rfl)
  rw [he, Fintype.sum_prod_type, Finset.sum_comm]
  have hs : (∑ b : DerivativeWord2 (maskRightLength j m),
      ∑ a : DerivativeWord2 (maskLeftLength j m), f (a,b)) ≤
      ∑ b : DerivativeWord2 (maskRightLength j m),
        (Fintype.card (DerivativeWord2 (maskLeftLength j m)) : ℝ) * (4 * M) ^ 2 *
          ‖driftMaskGradient hj D m b x‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro b _
    calc
      _ ≤ ∑ _a : DerivativeWord2 (maskLeftLength j m),
          (4 * M) ^ 2 * ‖driftMaskGradient hj D m b x‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro a _
        dsimp only [f]
        have hh := finiteMetricFlux_norm_le_four
          (fun k a' => orderedScalarDerivative (fun y => G y k a') (maskLeftLength j m) a x)
          hM (hb a) (driftMaskGradient hj D m b x)
        simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _)
          (mul_nonneg (mul_nonneg (by norm_num) hM) (norm_nonneg _))).mpr hh
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  refine hs.trans_eq ?_
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [PiLp.norm_sq_eq_of_L2]
  change (∑ b : DerivativeWord2 (maskRightLength j m), ∑ k : Fin 2,
    ‖D ⟨⟨maskRightLength j m + 1, by have := maskRightLength_le j m; omega⟩, Fin.snoc b k⟩ x‖ ^ 2) = _
  rw [← Fintype.sum_prod_type (fun p : DerivativeWord2 (maskRightLength j m) × Fin 2 =>
    ‖D ⟨⟨maskRightLength j m + 1, by have := maskRightLength_le j m; omega⟩, Fin.snoc p.1 p.2⟩ x‖ ^ 2)]
  exact (Fintype.sum_equiv (wordInitLastEquiv 2 (maskRightLength j m))
    (fun w => ‖D ⟨⟨maskRightLength j m + 1, by have := maskRightLength_le j m; omega⟩, w⟩ x‖ ^ 2)
    (fun p => ‖D ⟨⟨maskRightLength j m + 1, by have := maskRightLength_le j m; omega⟩,
      Fin.snoc p.1 p.2⟩ x‖ ^ 2)
    (fun w => by
      dsimp only [wordInitLastEquiv, Equiv.coe_fn_mk]
      rw [Fin.snoc_init_self])).symm

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! The scalar chain contains exactly the diagonal metric deviation and no source edges. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

omit [Fintype ι] in
/-- Every admissible order in a scalar chain is two. -/
theorem scalarChain_order_eq_two (κ : Fin 1 → ι → ℕ) (i i' : Fin 1 × ι)
    (d : admissibleOrders (fun p => κ p.1 p.2) 2 i i') : d.val = 2 := by
  have hd := Finset.mem_Icc.mp (Finset.mem_filter.mp d.property).1
  omega

/-- Off-diagonal component coefficients vanish identically. -/
theorem scalarChainCoefficient_offDiagonal
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (κ : Fin 1 → ι → ℕ)
    (i i' : Fin 1 × ι) (hi : i.2 ≠ i'.2)
    (d : admissibleOrders (fun p => κ p.1 p.2) 2 i i') (t : ℝ) (z : Vec 2) :
    planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i' d t z = 0 := by
  have hlevel : i.1 = i'.1 := Subsingleton.elim _ _
  simp [planeChainCoefficient, geometryScalarData, slowEvalCoefficient, hlevel, hi]

/-- On each scalar diagonal the sole coefficient is exactly `G-I` acting on the gradient. -/
theorem scalarChainCoefficient_diagonal
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (κ : Fin 1 → ι → ℕ)
    (i : Fin 1 × ι) (d : admissibleOrders (fun p => κ p.1 p.2) 2 i i)
    (t : ℝ) (z : Vec 2) :
    planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i d t z =
      metricFlux (h := h) (G t z - 1) (d.val - 1) (a := i.2) rfl
        (by have hd := scalarChain_order_eq_two κ i i d; omega) := by
  have hd := scalarChain_order_eq_two κ i i d
  simp [planeChainCoefficient, geometryScalarData, slowEvalCoefficient, hd]

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Weighted

/-! Continuity of the literal time derivative along a smooth space-time weight. -/

theorem timeSlice_deriv_eq (f : ℝ × Vec 2 → ℝ) (hf : ContDiff ℝ 2 f)
    (t : ℝ) (x : Vec 2) : deriv (fun s => f (s,x)) t = fderiv ℝ f (t,x) (1,0) := by
  have hh := (hf.differentiable (by norm_num) (t,x)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  exact hh.deriv

theorem timeSlice_deriv_continuous (f : ℝ × Vec 2 → ℝ) (hf : ContDiff ℝ 2 f) (t : ℝ) :
    Continuous (fun x => deriv (fun s => f (s,x)) t) := by
  simp_rw [timeSlice_deriv_eq f hf t]
  exact ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).comp
    (continuous_const.prodMk continuous_id)

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
open scoped ENNReal
namespace AVRegularity.Weighted

/-! Finite metric commutator arrays and their exact mask energy envelope. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The differentiated diffusion terms containing a metric derivative. -/
def metricCommutatorTerm {K j : ℕ} (hj : j ≤ K)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (D : RawJet2 (K + 1) E)
    (w : DerivativeWord2 j) (x : Vec 2) : PiLp 2 (fun _ : Fin 2 => E) :=
  ∑ m : PositionMask j, if 1 ≤ maskLeftLength j m then metricMaskTerm hj G D m w x else 0

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.KernelEnergy
namespace AVRegularity.Weighted

/-! The literal metric matrix as a bounded linear coefficient on the finite Hilbert gradient. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def metricFiberCoefficient (G : Matrix (Fin 2) (Fin 2) ℝ) :
    PiLp 2 (fun _ : Fin 2 => E) →L[ℝ] PiLp 2 (fun _ : Fin 2 => E) :=
  ∑ k : Fin 2, ∑ j : Fin 2, G k j •
    (tensorEntryCLM (E := E) k).comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) j)

theorem metricFiberCoefficient_apply (G : Matrix (Fin 2) (Fin 2) ℝ)
    (u : PiLp 2 (fun _ : Fin 2 => E)) :
    metricFiberCoefficient G u = finiteMetricFlux G u := by
  have hin (k : Fin 2) (z : E) : tensorEntryCLM (E := E) k z = PiLp.single 2 k z := rfl
  simp only [metricFiberCoefficient, sum_apply, smul_apply, ContinuousLinearMap.comp_apply,
    PiLp.proj_apply, hin]
  apply PiLp.ext
  intro k
  fin_cases k <;> simp [finiteMetricFlux, Fin.sum_univ_two]

theorem metricFiberCoefficient_norm_le (G : Matrix (Fin 2) (Fin 2) ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ k j, |G k j| ≤ M) :
    ‖metricFiberCoefficient (E := E) G‖ ≤ 4 * M := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  rw [metricFiberCoefficient_apply]
  exact finiteMetricFlux_norm_le_four G hM hb u

theorem metricFiberCoefficient_contDiff {K : ℕ}
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ k j, ContDiff ℝ (K : ℕ) (fun x => G x k j)) :
    ContDiff ℝ (K : ℕ) (fun x => metricFiberCoefficient (E := E) (G x)) := by
  unfold metricFiberCoefficient
  have : IsBoundedSMul ℝ ((PiLp 2 (fun _ : Fin 2 => E)) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => E)) :=
    NormedSpace.toIsBoundedSMul (𝕜 := ℝ)
      (E := ((PiLp 2 (fun _ : Fin 2 => E)) →L[ℝ] PiLp 2 (fun _ : Fin 2 => E)))
  apply ContDiff.sum
  intro k _
  apply ContDiff.sum
  intro j _
  exact (hG k j).smul_const _

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Exact collapse of the scalar chain's dependent coupling sum to the metric flux. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The raw coupling flux appearing verbatim in the scalar weak identity. -/
def scalarChainFlux (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (κ : Fin 1 → ι → ℕ)
    (w : ∀ p : Fin 1 × ι, PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (i : Fin 1 × ι) (t : ℝ) (z : Vec 2) : PiLp 2 (fun _ : Fin 2 => h i.2) :=
  ∑ i' : Fin 1 × ι, ∑ d : admissibleOrders (fun p => κ p.1 p.2) 2 i i',
    planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i' d t z
      (WithLp.toLp 2 fun word : DerivativeWord2 (d.val - 1) =>
        (w i').toFunction.jet
          ⟨⟨d.val - 1, by
            have hd := scalarChain_order_eq_two κ i i' d
            omega⟩, word⟩ z)

omit [∀ i, FiniteDimensional ℝ (h i)] in
/-- The native scalar coupling flux is exactly the diagonal metric deviation times the gradient. -/
theorem scalarChainFlux_eq (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (κ : Fin 1 → ι → ℕ)
    (w : ∀ p : Fin 1 × ι, PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (i : Fin 1 × ι) (t : ℝ) (z : Vec 2) (k : Fin 2) :
    scalarChainFlux G κ w i t z k = ∑ j : Fin 2, (G t z - 1) k j •
      (w i).toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => j⟩ z := by
  classical
  unfold scalarChainFlux
  rw [Finset.sum_eq_single i]
  · have hd2 : 2 ∈ admissibleOrders (fun p => κ p.1 p.2) 2 i i := by
      simp [admissibleOrders]
    let d2 : admissibleOrders (fun p => κ p.1 p.2) 2 i i := ⟨2, hd2⟩
    rw [Finset.sum_eq_single d2]
    · rw [scalarChainCoefficient_diagonal]
      simp [d2, metricFlux]
    · intro d _ hne
      exfalso
      apply hne
      apply Subtype.ext
      exact scalarChain_order_eq_two κ i i d
    · intro hn
      exact False.elim (hn (Finset.mem_univ d2))
  · intro i' _ hne
    have hc : i.2 ≠ i'.2 := by
      intro he
      apply hne
      exact Prod.ext (Subsingleton.elim _ _) he.symm
    apply Finset.sum_eq_zero
    intro d _
    rw [scalarChainCoefficient_offDiagonal G κ i i' hc d t z]
    simp
  · intro hn
    exact False.elim (hn (Finset.mem_univ i))

end AVRegularity.Weighted
end
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Projecting a vector slow Taylor coefficient preserves its reserved fast-jet bounds. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem slow_basis_projection_fast_jet_bound {r j : ℕ} (f : Vec 2 → Vec 2 → E)
    (hf : IsBoxSmooth r j f) (L : E →L[ℝ] F) (w : DerivativeWord2 r) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ j (fun z' => iteratedFDeriv ℝ r (fun X' => L (f X' z')) X
      (fun i => basisVec (w i))) z‖ ≤
      ‖L‖ * ((2 : ℝ) ^ j *
        ‖iteratedFDeriv ℝ r (fun X' => iteratedFDeriv ℝ j (f X') z) X‖) := by
  have he (z' : Vec 2) : iteratedFDeriv ℝ r (fun X' => L (f X' z')) X
      (fun i => basisVec (w i)) = L (iteratedFDeriv ℝ r (fun X' => f X' z') X
        (fun i => basisVec (w i))) := by
    have hh := L.iteratedFDeriv_comp_left (x := X)
      (hf.contDiff_slow z').contDiffAt (by norm_cast : (r : WithTop ℕ∞) ≤ r)
    change (iteratedFDeriv ℝ r (L ∘ (fun X' => f X' z')) X) _ = _
    rw [hh]
    rfl
  simp_rw [he]
  have hc : ContDiff ℝ (j : ℕ∞)
      (fun z' => iteratedFDeriv ℝ r (fun X' => f X' z') X (fun i => basisVec (w i))) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin r => Vec 2) E
      (fun i => basisVec (w i))).contDiff.comp (CoarseFluxDiff.contDiff_slowJet hf X)
  change ‖iteratedFDeriv ℝ j (L ∘ _) z‖ ≤ _
  rw [L.iteratedFDeriv_comp_left hc.contDiffAt (by norm_cast : (j : WithTop ℕ∞) ≤ j)]
  exact (L.norm_compContinuousMultilinearMap_le _).trans
    (mul_le_mul_of_nonneg_left (slow_basis_full_fast_jet_bound f hf w X z) (norm_nonneg L))

end AVRegularity.Weighted
end
end
