-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Analysis.Convolution.Kernel.Definitions
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization
open scoped Pointwise
namespace AVRegularity.Analysis.Convolution

/-! Smoothness, symmetry, integrability and Euclidean support of the kernel. -/

theorem integrable_scaledTemplate {φ₀ : Vec 2 → ℝ} (hφ₀ : Integrable φ₀)
    (n : ℕ+) : Integrable (scaledTemplate φ₀ n) := by
  have hs : 2 * ((n : ℕ) : ℝ) ≠ 0 := mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr n.pos.ne')
  exact (hφ₀.comp_smul hs).const_mul _

 theorem scaledTemplate_nonneg {φ₀ : Vec 2 → ℝ} (hφ₀ : ∀ z, 0 ≤ φ₀ z)
    (n : ℕ+) (z : Vec 2) : 0 ≤ scaledTemplate φ₀ n z :=
  mul_nonneg (sq_nonneg _) (hφ₀ _)

 theorem integral_scaledTemplate {φ₀ : Vec 2 → ℝ} (hφ₀ : ∫ z, φ₀ z = 1)
    (n : ℕ+) : ∫ z, scaledTemplate φ₀ n z = 1 := by
  have hs : 2 * ((n : ℕ) : ℝ) ≠ 0 := mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr n.pos.ne')
  unfold scaledTemplate
  rw [integral_const_mul, Measure.integral_comp_smul, show Module.finrank ℝ (Vec 2) = 2 from Module.finrank_fin_fun ℝ]
  rw [abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _)), hφ₀]
  simp only [smul_eq_mul, mul_one]
  exact mul_inv_cancel₀ (pow_ne_zero 2 hs)

 theorem integrable_positiveConvolutionPower {q : Vec 2 → ℝ} (hq : Integrable q)
    (m : ℕ) : Integrable (positiveConvolutionPower q m) := by
  induction m with
  | zero => exact hq
  | succ m ih => exact integrable_kernelConvolution hq ih

 theorem integral_positiveConvolutionPower {q : Vec 2 → ℝ} (hq : Integrable q)
    (m : ℕ) : ∫ z, positiveConvolutionPower q m z = (∫ z, q z) ^ (m + 1) := by
  induction m with
  | zero => simp only [positiveConvolutionPower, Nat.zero_add, pow_one]
  | succ m ih =>
    change ∫ z, kernelConvolution q (positiveConvolutionPower q m) z = _
    rw [kernelConvolution, integral_convolution _ hq (integrable_positiveConvolutionPower hq m), ih]
    change (∫ z, q z) * (∫ z, q z) ^ (m + 1) = (∫ z, q z) ^ (m + 1 + 1)
    exact (pow_succ' _ _).symm

 theorem hasCompactSupport_positiveConvolutionPower {q : Vec 2 → ℝ}
    (hq : HasCompactSupport q) (m : ℕ) : HasCompactSupport (positiveConvolutionPower q m) := by
  induction m with
  | zero => exact hq
  | succ m ih => exact hq.convolution (ContinuousLinearMap.mul ℝ ℝ) ih

 theorem contDiff_positiveConvolutionPower {q : Vec 2 → ℝ}
    (hc : HasCompactSupport q) (hd : ContDiff ℝ (⊤ : ℕ∞) q) (hq : Integrable q)
    (m : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (positiveConvolutionPower q m) := by
  induction m with
  | zero => exact hd
  | succ m _ =>
    exact hc.contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℝ) hd
      (integrable_positiveConvolutionPower hq m).locallyIntegrable

 theorem integrable_momentKernel {φ₀ : Vec 2 → ℝ} (hφ₀ : Integrable φ₀)
    (n : ℕ+) : Integrable (momentKernel φ₀ n) := by
  unfold momentKernel
  apply integrable_finsetSum'
  intro l _
  exact (integrable_positiveConvolutionPower
    (integrable_kernelConvolution (integrable_scaledTemplate hφ₀ n)
      (integrable_reflection (integrable_scaledTemplate hφ₀ n))) (l - 1)).smul _

theorem hasCompactSupport_scaledTemplate {φ₀ : Vec 2 → ℝ}
    (hc : HasCompactSupport φ₀) (n : ℕ+) : HasCompactSupport (scaledTemplate φ₀ n) := by
  have hs : 2 * ((n : ℕ) : ℝ) ≠ 0 := mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr n.pos.ne')
  have h := hc.comp_homeomorph (Homeomorph.smul (Units.mk0 (2 * ((n : ℕ) : ℝ)) hs))
  exact h.smul_left (f := fun _ : Vec 2 => (2 * ((n : ℕ) : ℝ)) ^ 2)

 theorem contDiff_scaledTemplate {φ₀ : Vec 2 → ℝ}
    (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀) (n : ℕ+) : ContDiff ℝ (⊤ : ℕ∞) (scaledTemplate φ₀ n) := by
  exact (hd.comp (contDiff_id.const_smul (2 * ((n : ℕ) : ℝ)))).const_smul ((2 * ((n : ℕ) : ℝ)) ^ 2)

 theorem hasCompactSupport_reflection {q : Vec 2 → ℝ}
    (hc : HasCompactSupport q) : HasCompactSupport (reflection q) :=
  hc.comp_homeomorph (Homeomorph.neg (Vec 2))

 theorem contDiff_reflection {q : Vec 2 → ℝ}
    (hd : ContDiff ℝ (⊤ : ℕ∞) q) : ContDiff ℝ (⊤ : ℕ∞) (reflection q) :=
  hd.comp contDiff_neg

 theorem hasCompactSupport_momentKernel {φ₀ : Vec 2 → ℝ}
    (hc : HasCompactSupport φ₀) (n : ℕ+) : HasCompactSupport (momentKernel φ₀ n) := by
  unfold momentKernel
  apply HasCompactSupport.finset_sum
  intro l _
  exact (hasCompactSupport_positiveConvolutionPower
    ((hasCompactSupport_scaledTemplate hc n).convolution (ContinuousLinearMap.mul ℝ ℝ)
      (hasCompactSupport_reflection (hasCompactSupport_scaledTemplate hc n))) (l - 1)).smul_left

 theorem contDiff_momentKernel {φ₀ : Vec 2 → ℝ}
    (hc : HasCompactSupport φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀) (n : ℕ+) :
    ContDiff ℝ (⊤ : ℕ∞) (momentKernel φ₀ n) := by
  unfold momentKernel
  rw [show (∑ l ∈ Finset.Icc 1 (n : ℕ),
    ((-1 : ℝ) ^ (l + 1) * ((n : ℕ).choose l : ℝ)) •
      positiveConvolutionPower
        (kernelConvolution (scaledTemplate φ₀ n) (reflection (scaledTemplate φ₀ n))) (l - 1)) =
      (fun z => ∑ l ∈ Finset.Icc 1 (n : ℕ),
        ((-1 : ℝ) ^ (l + 1) * ((n : ℕ).choose l : ℝ)) •
          positiveConvolutionPower
            (kernelConvolution (scaledTemplate φ₀ n) (reflection (scaledTemplate φ₀ n))) (l - 1) z) by
    ext z; simp only [Finset.sum_apply, Pi.smul_apply]]
  apply ContDiff.sum
  intro l _
  apply ContDiff.const_smul
  apply contDiff_positiveConvolutionPower
  · exact (hasCompactSupport_scaledTemplate hc n).convolution (ContinuousLinearMap.mul ℝ ℝ)
      (hasCompactSupport_reflection (hasCompactSupport_scaledTemplate hc n))
  · exact (hasCompactSupport_scaledTemplate hc n).contDiff_convolution_left
      (ContinuousLinearMap.mul ℝ ℝ) (contDiff_scaledTemplate hd n)
      ((contDiff_reflection (contDiff_scaledTemplate hd n)).continuous.integrable_of_hasCompactSupport
        (hasCompactSupport_reflection (hasCompactSupport_scaledTemplate hc n))).locallyIntegrable
  · exact integrable_kernelConvolution
      ((contDiff_scaledTemplate hd n).continuous.integrable_of_hasCompactSupport
        (hasCompactSupport_scaledTemplate hc n))
      ((contDiff_reflection (contDiff_scaledTemplate hd n)).continuous.integrable_of_hasCompactSupport
        (hasCompactSupport_reflection (hasCompactSupport_scaledTemplate hc n)))

theorem reflection_kernelConvolution (q p : Vec 2 → ℝ) :
    reflection (kernelConvolution q p) = kernelConvolution (reflection q) (reflection p) := by
  funext z
  change (∫ t : Vec 2, q t * p (-z - t)) = ∫ t : Vec 2, q (-t) * p (-(z - t))
  rw [← integral_neg_eq_self (fun t : Vec 2 => q t * p (-z - t)) volume]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    change q (-t) * p (-z - -t) = q (-t) * p (-(z - t))
    rw [sub_neg_eq_add, neg_sub, add_comm (-z) t, sub_eq_add_neg]

 theorem reflection_reflection (q : Vec 2 → ℝ) : reflection (reflection q) = q := by
  funext z
  change q (-(-z)) = q z
  rw [neg_neg]

 theorem reflection_autocorrelation (q : Vec 2 → ℝ) :
    reflection (kernelConvolution q (reflection q)) = kernelConvolution q (reflection q) := by
  rw [reflection_kernelConvolution, reflection_reflection, kernelConvolution_comm]

theorem support_kernelConvolution_norm_le {q p : Vec 2 → ℝ} {R S : ℝ}
    (hq : ∀ z ∈ Function.support q, euclideanNorm z ≤ R)
    (hp : ∀ z ∈ Function.support p, euclideanNorm z ≤ S) :
    ∀ z ∈ Function.support (kernelConvolution q p), euclideanNorm z ≤ R + S := by
  intro z hz
  rcases (support_convolution_subset (ContinuousLinearMap.mul ℝ ℝ)) hz with ⟨x, hx, y, hy, rfl⟩
  exact (euclideanNorm_add x y).trans (add_le_add (hq x hx) (hp y hy))

 theorem support_scaledTemplate_norm_le {φ₀ : Vec 2 → ℝ}
    (hφ₀ : ∀ z ∈ Function.support φ₀, euclideanNorm z ≤ 1) (n : ℕ+) :
    ∀ z ∈ Function.support (scaledTemplate φ₀ n),
      euclideanNorm z ≤ 1 / (2 * ((n : ℕ) : ℝ)) := by
  intro z hz
  have hs : 0 < 2 * ((n : ℕ) : ℝ) := mul_pos (by norm_num) (Nat.cast_pos.mpr n.pos)
  have hmem : (2 * ((n : ℕ) : ℝ)) • z ∈ Function.support φ₀ := by
    intro hzero
    apply hz
    change (2 * ((n : ℕ) : ℝ)) ^ 2 * φ₀ ((2 * ((n : ℕ) : ℝ)) • z) = 0
    rw [hzero, mul_zero]
  have h := hφ₀ _ hmem
  rw [euclideanNorm_smul, abs_of_pos hs] at h
  exact (le_div_iff₀ hs).mpr (by rwa [mul_comm] at h)

 theorem support_reflection_norm_le {q : Vec 2 → ℝ} {R : ℝ}
    (hq : ∀ z ∈ Function.support q, euclideanNorm z ≤ R) :
    ∀ z ∈ Function.support (reflection q), euclideanNorm z ≤ R := by
  intro z hz
  have h := hq (-z) hz
  simpa only [euclideanNorm_neg] using h

 theorem support_positiveConvolutionPower_norm_le {q : Vec 2 → ℝ} {R : ℝ}
    (hq : ∀ z ∈ Function.support q, euclideanNorm z ≤ R) (m : ℕ) :
    ∀ z ∈ Function.support (positiveConvolutionPower q m),
      euclideanNorm z ≤ ((m : ℝ) + 1) * R := by
  induction m with
  | zero => simpa only [positiveConvolutionPower, Nat.cast_zero, zero_add, one_mul] using hq
  | succ m ih =>
    have h := support_kernelConvolution_norm_le hq ih
    intro z hz
    calc
      ‖Homogenization.HilbertVec.ofVec z‖ ≤ R + ((m : ℝ) + 1) * R := h z hz
      _ = (((m + 1 : ℕ) : ℝ) + 1) * R := by push_cast; ring

 theorem support_momentKernel_norm_le {φ₀ : Vec 2 → ℝ}
    (hφ₀ : ∀ z ∈ Function.support φ₀, euclideanNorm z ≤ 1) (n : ℕ+) :
    ∀ z ∈ Function.support (momentKernel φ₀ n), euclideanNorm z ≤ 1 := by
  intro z hz
  by_contra hnorm
  have hs : 0 < 2 * ((n : ℕ) : ℝ) := mul_pos (by norm_num) (Nat.cast_pos.mpr n.pos)
  have hscaled := support_scaledTemplate_norm_le hφ₀ n
  have hq := support_kernelConvolution_norm_le hscaled (support_reflection_norm_le hscaled)
  apply hz
  unfold momentKernel
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro l hl
  have hl' := Finset.mem_Icc.mp hl
  have hrad : (((l - 1 : ℕ) : ℝ) + 1) ≤ ((n : ℕ) : ℝ) := by
    rw [Nat.cast_sub hl'.1, Nat.cast_one]
    linarith [Nat.cast_le (α := ℝ).mpr hl'.2]
  have hscale : ((n : ℕ) : ℝ) *
      (1 / (2 * ((n : ℕ) : ℝ)) + 1 / (2 * ((n : ℕ) : ℝ))) = 1 := by
    field_simp
    ring
  have hbound : (((l - 1 : ℕ) : ℝ) + 1) *
      (1 / (2 * ((n : ℕ) : ℝ)) + 1 / (2 * ((n : ℕ) : ℝ))) ≤ 1 :=
    (mul_le_mul_of_nonneg_right hrad (add_nonneg (one_div_nonneg.mpr hs.le)
      (one_div_nonneg.mpr hs.le))).trans_eq hscale
  have hzero : positiveConvolutionPower
      (kernelConvolution (scaledTemplate φ₀ n) (reflection (scaledTemplate φ₀ n))) (l - 1) z = 0 := by
    by_contra hp
    exact hnorm ((support_positiveConvolutionPower_norm_le hq (l - 1) z hp).trans hbound)
  rw [Pi.smul_apply, hzero, smul_zero]

end AVRegularity.Analysis.Convolution
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.Analysis.Convolution

/-! Normalization of the finite signed kernel sum. -/

theorem real_scalar_binomial_regularizer (a : ℝ) (n : ℕ) :
    ∑ l ∈ Finset.Icc 1 n,
      ((-1 : ℝ) ^ (l + 1) * (n.choose l : ℝ)) * a ^ l = 1 - (1 - a) ^ n := by
  have hb : (1 - a)^n = ∑ l ∈ Finset.range (n+1),
      ((-1 : ℝ)^l * (n.choose l : ℝ)) * a^l := by
    rw [sub_eq_add_neg, add_comm, add_pow]
    apply Finset.sum_congr rfl
    intro l _
    rw [one_pow, mul_one, ← neg_one_mul a, mul_pow]
    ring
  have hi : Finset.Icc 1 n = Finset.Ico 1 (n+1) :=
    (Finset.Ico_succ_right_eq_Icc 1 n).symm
  rw [hb, hi,
    Finset.sum_Ico_eq_sub (fun l => ((-1 : ℝ)^(l+1)*(n.choose l : ℝ))*a^l)
      (Nat.succ_le_succ (Nat.zero_le n))]
  simp only [Finset.sum_range_one, Nat.zero_add, pow_one, Nat.choose_zero_right,
    Nat.cast_one, mul_one, pow_zero]
  rw [Finset.sum_congr rfl (fun l _ => show
    ((-1 : ℝ)^(l+1)*(n.choose l : ℝ))*a^l = -(((-1 : ℝ)^l*(n.choose l : ℝ))*a^l) by
      rw [pow_succ]; ring), Finset.sum_neg_distrib]
  ring

theorem momentKernel_binomial_mass (n : ℕ+) :
    ∑ l ∈ Finset.Icc 1 (n : ℕ),
      ((-1 : ℝ) ^ (l + 1) * ((n : ℕ).choose l : ℝ)) = 1 := by
  simpa [n.pos.ne'] using real_scalar_binomial_regularizer (1 : ℝ) (n : ℕ)

theorem integral_reflection (q : Vec 2 → ℝ) :
    ∫ z, reflection q z = ∫ z, q z :=
  integral_neg_eq_self q volume

theorem integral_autocorrelation {q : Vec 2 → ℝ} (hq : Integrable q) :
    ∫ z, kernelConvolution q (reflection q) z = (∫ z, q z) ^ 2 := by
  rw [kernelConvolution, integral_convolution _ hq (integrable_reflection hq),
    integral_reflection]
  change (∫ z, q z) * (∫ z, q z) = (∫ z, q z) ^ 2
  exact (pow_two _).symm

theorem integral_momentKernel {φ₀ : Vec 2 → ℝ} (hφ₀ : Integrable φ₀)
    (hmass : ∫ z, φ₀ z = 1) (n : ℕ+) : ∫ z, momentKernel φ₀ n z = 1 := by
  let q := kernelConvolution (scaledTemplate φ₀ n) (reflection (scaledTemplate φ₀ n))
  have hq : Integrable q := integrable_kernelConvolution
    (integrable_scaledTemplate hφ₀ n)
    (integrable_reflection (integrable_scaledTemplate hφ₀ n))
  have hqmass : ∫ z, q z = 1 := by
    dsimp only [q]
    rw [integral_autocorrelation (integrable_scaledTemplate hφ₀ n),
      integral_scaledTemplate hmass n, one_pow]
  unfold momentKernel
  simp only [Finset.sum_apply]
  rw [integral_finsetSum _ (fun l _ =>
    (integrable_positiveConvolutionPower hq (l - 1)).smul _)]
  simp only [Pi.smul_apply, smul_eq_mul, integral_const_mul]
  have hp (l : ℕ) :
      ∫ z, positiveConvolutionPower q (l - 1) z = 1 := by
    rw [integral_positiveConvolutionPower hq, hqmass, one_pow]
  simp only [hp, mul_one]
  exact momentKernel_binomial_mass n

end AVRegularity.Analysis.Convolution
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.Analysis.Convolution

/-! The signed convolution equals the positive contraction polynomial.
Mass one is derived from the same finite binomial identity. -/

section
section
variable {X E : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [MeasurableSpace X] [BorelSpace X] [R1Space X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure X} [μ.IsAddLeftInvariant] [IsLocallyFiniteMeasure μ]
  [μ.InnerRegularCompactLTTop]

theorem averagingOperator_smul (ρ : Vec 2 →+ X) (hρ : Continuous ρ)
    {q : Vec 2 → ℝ} (hq : Integrable q) (c : ℝ) :
    averagingOperator (E := E) (μ := μ) ρ hρ (c • q) (hq.smul c) =
      c • averagingOperator ρ hρ q hq := by
  apply ContinuousLinearMap.ext
  intro f
  change (∫ z : Vec 2, (c • q) z • translation (ρ z) f) = c • average ρ q f
  simp only [Pi.smul_apply, smul_eq_mul, mul_smul]
  exact integral_smul c (fun z : Vec 2 => q z • translation (ρ z) f)

theorem averagingOperator_sum (ρ : Vec 2 →+ X) (hρ : Continuous ρ)
    {ι : Type*} (s : Finset ι) (q : ι → Vec 2 → ℝ) (hq : ∀ i, Integrable (q i)) :
    averagingOperator (E := E) (μ := μ) ρ hρ (∑ i ∈ s, q i)
      (integrable_finsetSum' s (fun i _ => hq i)) =
      ∑ i ∈ s, averagingOperator ρ hρ (q i) (hq i) := by
  apply ContinuousLinearMap.ext
  intro f
  change (∫ z : Vec 2, (∑ i ∈ s, q i) z • translation (ρ z) f) = _
  simp only [Finset.sum_apply, Finset.sum_smul, sum_apply]
  exact integral_finsetSum s (fun i _ => integrable_average_integrand ρ hρ (hq i) f)

theorem averagingOperator_positiveConvolutionPower (ρ : Vec 2 →+ X) (hρ : Continuous ρ)
    {q : Vec 2 → ℝ} (hq : Integrable q) (m : ℕ) :
    averagingOperator (E := E) (μ := μ) ρ hρ (positiveConvolutionPower q m)
      (integrable_positiveConvolutionPower hq m) =
      (averagingOperator ρ hρ q hq) ^ (m + 1) := by
  induction m with
  | zero => simp only [positiveConvolutionPower, Nat.zero_add, pow_one]
  | succ m ih =>
    change averagingOperator ρ hρ (kernelConvolution q (positiveConvolutionPower q m)) _ = _
    rw [← averagingOperator_comp ρ hρ q _ hq
      (integrable_positiveConvolutionPower hq m), ih]
    exact (pow_succ' _ _).symm

 theorem averagingOperator_momentKernel (ρ : Vec 2 →+ X) (hρ : Continuous ρ)
    {φ₀ : Vec 2 → ℝ} (hφ₀ : Integrable φ₀) (n : ℕ+) :
    averagingOperator (E := E) (μ := μ) ρ hρ (momentKernel φ₀ n)
      (integrable_momentKernel hφ₀ n) =
      ∑ l ∈ Finset.Icc 1 (n : ℕ),
        ((-1 : ℝ) ^ (l + 1) * ((n : ℕ).choose l : ℝ)) •
          (averagingOperator ρ hρ (kernelConvolution (scaledTemplate φ₀ n)
            (reflection (scaledTemplate φ₀ n)))
            (integrable_kernelConvolution (integrable_scaledTemplate hφ₀ n)
              (integrable_reflection (integrable_scaledTemplate hφ₀ n)))) ^ l := by
  unfold momentKernel
  rw [averagingOperator_sum ρ hρ _ _ (fun l =>
    (integrable_positiveConvolutionPower
      (integrable_kernelConvolution (integrable_scaledTemplate hφ₀ n)
        (integrable_reflection (integrable_scaledTemplate hφ₀ n))) (l - 1)).smul _)]
  apply Finset.sum_congr rfl
  intro l hl
  rw [averagingOperator_smul ρ hρ (integrable_positiveConvolutionPower
      (integrable_kernelConvolution (integrable_scaledTemplate hφ₀ n)
        (integrable_reflection (integrable_scaledTemplate hφ₀ n))) (l - 1)),
    averagingOperator_positiveConvolutionPower,
    Nat.sub_add_cancel (Finset.mem_Icc.mp hl).1]
end

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem operator_binomial_expansion (T : E →L[ℝ] E) (n : ℕ) :
    (1 - T) ^ n = ∑ l ∈ Finset.range (n + 1),
      ((-1 : ℝ) ^ l * (n.choose l : ℝ)) • T ^ l := by
  rw [sub_eq_add_neg, add_comm, (Commute.one_right (-T)).add_pow]
  apply Finset.sum_congr rfl
  intro l _
  rw [one_pow, mul_one, ← neg_one_smul ℝ T, smul_pow]
  ext x
  simp only [mul_apply_eq_comp, ContinuousLinearMap.natCast_apply,
    map_nsmul, smul_apply]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  congr 1
  exact mul_comm _ _

theorem operator_binomial_regularizer (T : E →L[ℝ] E) (n : ℕ) :
    ∑ l ∈ Finset.Icc 1 n,
      ((-1 : ℝ) ^ (l + 1) * (n.choose l : ℝ)) • T ^ l =
      1 - (1 - T) ^ n := by
  rw [operator_binomial_expansion]
  have hi : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
    exact (Finset.Ico_succ_right_eq_Icc 1 n).symm
  rw [hi, Finset.sum_Ico_eq_sub (fun l => ((-1 : ℝ) ^ (l + 1) * (n.choose l : ℝ)) • T ^ l)
    (Nat.succ_le_succ (Nat.zero_le n))]
  simp only [Finset.sum_range_one, Nat.zero_add, pow_one, Nat.choose_zero_right,
    Nat.cast_one, mul_one, pow_zero, neg_one_smul]
  rw [Finset.sum_congr rfl (fun l _ => show
    ((-1 : ℝ) ^ (l + 1) * (n.choose l : ℝ)) • T ^ l =
      -(((-1 : ℝ) ^ l * (n.choose l : ℝ)) • T ^ l) by
      rw [pow_succ, mul_neg_one, neg_mul, neg_smul])]
  rw [Finset.sum_neg_distrib]
  abel
end

section
variable {X E : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [MeasurableSpace X] [BorelSpace X] [R1Space X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {μ : Measure X} [μ.IsAddLeftInvariant] [IsLocallyFiniteMeasure μ]
  [μ.InnerRegularCompactLTTop]

 theorem averagingOperator_momentKernel_polynomial (ρ : Vec 2 →+ X) (hρ : Continuous ρ)
    {φ₀ : Vec 2 → ℝ} (hφ₀ : Integrable φ₀) (n : ℕ+) :
    averagingOperator (E := E) (μ := μ) ρ hρ (momentKernel φ₀ n)
      (integrable_momentKernel hφ₀ n) =
      1 - (1 - (averagingOperator (E := E) (μ := μ) ρ hρ (scaledTemplate φ₀ n)
        (integrable_scaledTemplate hφ₀ n)).adjoint *
          averagingOperator (E := E) (μ := μ) ρ hρ (scaledTemplate φ₀ n)
            (integrable_scaledTemplate hφ₀ n)) ^ (n : ℕ) := by
  rw [averagingOperator_momentKernel ρ hρ hφ₀ n, operator_binomial_regularizer,
    ← averagingOperator_autocorrelation ρ hρ (scaledTemplate φ₀ n)
      (integrable_scaledTemplate hφ₀ n)]
  rfl

 theorem averagingOperator_momentKernel_contraction (ρ : Vec 2 →+ X) (hρ : Continuous ρ)
    {φ₀ : Vec 2 → ℝ} (hφ₀ : Integrable φ₀) (hnonneg : ∀ z, 0 ≤ φ₀ z)
    (hmass : ∫ z, φ₀ z = 1) (n : ℕ+) :
    ‖averagingOperator (E := E) (μ := μ) ρ hρ (momentKernel φ₀ n)
      (integrable_momentKernel hφ₀ n)‖ ≤ 1 := by
  rw [averagingOperator_momentKernel_polynomial ρ hρ hφ₀ n]
  exact (AVRegularity.Analysis.Convolution.autocorrelation_regularizer_norm_le
    (averagingOperator (E := E) (μ := μ) ρ hρ (scaledTemplate φ₀ n)
      (integrable_scaledTemplate hφ₀ n))
    (averagingOperator_contraction ρ hρ _ (integrable_scaledTemplate hφ₀ n)
      (Filter.Eventually.of_forall (scaledTemplate_nonneg hnonneg n))
      (integral_scaledTemplate hmass n)) (n : ℕ)).2
end
end

/-! **The defect of the order-`n` regularizer is dominated by the defect of a lower order.**

The signed kernel `𝗄_n` (`momentKernel φ₀ n`) is built from the template scaled by `2n`
(`scaledTemplate φ₀ n z = (2n)² φ₀(2n z)`), and the average with `𝗄_n` along a displacement `ρ` is
`1 - P^n`, `P = 1 - B* B`, where `B` is the average with the scaled template
(`averagingOperator_momentKernel_polynomial`). The change of variables `z = (m/n) w` turns the
scaled template of order `n` into the one of order `m` at the displacement `w ↦ ρ((m/n) w)`
(`averagingOperator_scaledTemplate_rescale`), so `P` is the same operator at both orders, and since
`P` is a contraction (`positive_complement`), for `m ≤ n`

`‖f - S_ρ^{(n)} f‖ = ‖P^{n-m} P^m f‖ ≤ ‖P^m f‖ = ‖f - S_{ρ∘(m/n)}^{(m)} f‖`

(`averagingOperator_momentKernel_defect_le_of_le`). This replaces the Fourier multiplier bound
`(1 - |φ̂₀(η/2n)|²)^n ≤ (1 - |φ̂₀((m/n)η/2m)|²)^m` by the operator statement behind it; no
Plancherel identity is used. Consequence: every bound of the order-`m` defect by derivatives holds
for all orders `n ≥ m` with the same constant and a displacement shrunk by `m/n ≤ 1`. -/

section
/-- The displacement `z ↦ ρ (c z)`. -/
def rescaleDisplacement {X : Type*} [AddCommGroup X] (c : ℝ) (ρ : Vec 2 →+ X) : Vec 2 →+ X where
  toFun z := ρ (c • z)
  map_zero' := by rw [smul_zero, map_zero]
  map_add' x y := by rw [smul_add, map_add]

@[simp] theorem rescaleDisplacement_apply {X : Type*} [AddCommGroup X] (c : ℝ) (ρ : Vec 2 →+ X)
    (z : Vec 2) : rescaleDisplacement c ρ z = ρ (c • z) := rfl

theorem continuous_rescaleDisplacement {X : Type*} [AddCommGroup X] [TopologicalSpace X] (c : ℝ)
    {ρ : Vec 2 →+ X} (hρ : Continuous ρ) : Continuous (rescaleDisplacement c ρ) :=
  hρ.comp (continuous_const_smul c)

/-- The ratio `m / n` of two orders. -/
def orderRatio (m n : ℕ+) : ℝ := ((m : ℕ) : ℝ) / ((n : ℕ) : ℝ)

theorem orderRatio_pos (m n : ℕ+) : 0 < orderRatio m n :=
  div_pos (Nat.cast_pos.mpr m.pos) (Nat.cast_pos.mpr n.pos)

theorem orderRatio_le_one {m n : ℕ+} (hmn : m ≤ n) : orderRatio m n ≤ 1 := by
  have hn : (0 : ℝ) < ((n : ℕ) : ℝ) := Nat.cast_pos.mpr n.pos
  have h : ((m : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) := Nat.cast_le.mpr hmn
  exact (div_le_one hn).mpr h

section Rescale

variable {X E : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [MeasurableSpace X] [BorelSpace X] [R1Space X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure X} [μ.IsAddLeftInvariant] [IsLocallyFiniteMeasure μ]
  [μ.InnerRegularCompactLTTop]

/-- The average with the template scaled by `2n` along `ρ` is the average with the template scaled
by `2m` along `w ↦ ρ((m/n) w)`. -/
theorem averagingOperator_scaledTemplate_rescale (ρ : Vec 2 →+ X) (hρ : Continuous ρ)
    {φ₀ : Vec 2 → ℝ} (hφ₀ : Integrable φ₀) (m n : ℕ+) :
    averagingOperator (E := E) (μ := μ) ρ hρ (scaledTemplate φ₀ n)
        (integrable_scaledTemplate hφ₀ n) =
      averagingOperator (E := E) (μ := μ) (rescaleDisplacement (orderRatio m n) ρ)
        (continuous_rescaleDisplacement _ hρ) (scaledTemplate φ₀ m)
        (integrable_scaledTemplate hφ₀ m) := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [averagingOperator_apply, rescaleDisplacement_apply]
  have hm : ((m : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr m.pos.ne'
  have hn : ((n : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.pos.ne'
  have hc : orderRatio m n ≠ 0 := (orderRatio_pos m n).ne'
  have hpt : ∀ w : Vec 2, scaledTemplate φ₀ n (orderRatio m n • w) •
        translation (μ := μ) (ρ (orderRatio m n • w)) f =
      (orderRatio m n ^ 2)⁻¹ •
        (scaledTemplate φ₀ m w • translation (μ := μ) (ρ (orderRatio m n • w)) f) := by
    intro w
    rw [smul_smul]
    congr 1
    unfold scaledTemplate
    rw [smul_smul, show 2 * ((n : ℕ) : ℝ) * orderRatio m n = 2 * ((m : ℕ) : ℝ) by
      unfold orderRatio; field_simp]
    unfold orderRatio
    field_simp
  have h := Measure.integral_comp_smul (μ := (volume : Measure (Vec 2)))
    (fun z => scaledTemplate φ₀ n z • translation (μ := μ) (ρ z) f) (orderRatio m n)
  rw [show Module.finrank ℝ (Vec 2) = 2 from Module.finrank_fin_fun ℝ] at h
  simp only [hpt] at h
  rw [integral_smul, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _))] at h
  exact (smul_right_injective _ (inv_ne_zero (pow_ne_zero 2 hc)) h).symm

end Rescale

section Contraction

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The powers of a contraction do not increase the norm of a vector. -/
theorem norm_pow_apply_le_of_norm_le_one (P : F →L[ℝ] F) (hP : ‖P‖ ≤ 1) (k : ℕ) (g : F) :
    ‖(P ^ k) g‖ ≤ ‖g‖ := by
  induction k generalizing g with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    change ‖(P ^ k) (P g)‖ ≤ ‖g‖
    calc ‖(P ^ k) (P g)‖ ≤ ‖P g‖ := ih (P g)
      _ ≤ 1 * ‖g‖ := ContinuousLinearMap.le_of_opNorm_le P hP g
      _ = ‖g‖ := one_mul _

end Contraction

section Order

variable {X E : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [MeasurableSpace X] [BorelSpace X] [R1Space X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {μ : Measure X} [μ.IsAddLeftInvariant] [IsLocallyFiniteMeasure μ]
  [μ.InnerRegularCompactLTTop]

/-- **Order reduction.** For `m ≤ n`, the defect of the order-`n` regularizer along `ρ` is at most
the defect of the order-`m` regularizer along `w ↦ ρ((m/n) w)`. -/
theorem averagingOperator_momentKernel_defect_le_of_le (ρ : Vec 2 →+ X) (hρ : Continuous ρ)
    {φ₀ : Vec 2 → ℝ} (hφ₀ : Integrable φ₀) (hnonneg : ∀ z, 0 ≤ φ₀ z)
    (hmass : ∫ z, φ₀ z = 1) {m n : ℕ+} (hmn : m ≤ n) (f : L2 E μ) :
    ‖f - averagingOperator (E := E) (μ := μ) ρ hρ (momentKernel φ₀ n)
        (integrable_momentKernel hφ₀ n) f‖ ≤
      ‖f - averagingOperator (E := E) (μ := μ) (rescaleDisplacement (orderRatio m n) ρ)
        (continuous_rescaleDisplacement _ hρ) (momentKernel φ₀ m)
        (integrable_momentKernel hφ₀ m) f‖ := by
  set B := averagingOperator (E := E) (μ := μ) ρ hρ (scaledTemplate φ₀ n)
    (integrable_scaledTemplate hφ₀ n) with hB
  have hBB : averagingOperator (E := E) (μ := μ) (rescaleDisplacement (orderRatio m n) ρ)
      (continuous_rescaleDisplacement _ hρ) (scaledTemplate φ₀ m)
      (integrable_scaledTemplate hφ₀ m) = B :=
    (averagingOperator_scaledTemplate_rescale ρ hρ hφ₀ m n).symm
  have hBn : ‖B‖ ≤ 1 := averagingOperator_contraction ρ hρ _ (integrable_scaledTemplate hφ₀ n)
    (Filter.Eventually.of_forall (scaledTemplate_nonneg hnonneg n))
    (integral_scaledTemplate hmass n)
  have hnorm : ‖B.adjoint * B‖ ≤ 1 := by
    change ‖B.adjoint.comp B‖ ≤ 1
    rw [ContinuousLinearMap.norm_adjoint_comp_self]
    simpa only [pow_two] using (pow_le_pow_left₀ (norm_nonneg _) hBn 2).trans_eq (one_pow 2)
  set P := 1 - B.adjoint * B with hPdef
  have hP : ‖P‖ ≤ 1 :=
    (positive_complement (B.adjoint * B) (ContinuousLinearMap.isPositive_adjoint_comp_self B)
      hnorm).2
  have hn : averagingOperator (E := E) (μ := μ) ρ hρ (momentKernel φ₀ n)
      (integrable_momentKernel hφ₀ n) = 1 - P ^ (n : ℕ) :=
    averagingOperator_momentKernel_polynomial ρ hρ hφ₀ n
  have hm : averagingOperator (E := E) (μ := μ) (rescaleDisplacement (orderRatio m n) ρ)
      (continuous_rescaleDisplacement _ hρ) (momentKernel φ₀ m)
      (integrable_momentKernel hφ₀ m) = 1 - P ^ (m : ℕ) := by
    rw [averagingOperator_momentKernel_polynomial _ _ hφ₀ m, hBB]
  have hmn' : (m : ℕ) ≤ (n : ℕ) := hmn
  have hdef : ∀ k : ℕ, f - (1 - P ^ k) f = (P ^ k) f := fun k => by
    change f - (f - (P ^ k) f) = (P ^ k) f
    rw [sub_sub_cancel]
  rw [hn, hm, hdef, hdef, ← pow_sub_mul_pow P hmn']
  exact norm_pow_apply_le_of_norm_le_one P hP _ _

end Order
end

end AVRegularity.Analysis.Convolution
end
end
end
