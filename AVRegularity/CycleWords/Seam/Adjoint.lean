-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.Seam.CutoffComplementJetScale
import AVRegularity.CycleComparison.Residual.QuietMean.SourceMean
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

@[expose] public noncomputable section

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleWords.Seam

/-! Scale-sensitive inverse-chart bounds for transport of negative seam norms. -/

/-- The chart data used by the transport estimate, with the scale restrictions retained. -/
structure TransportCharts (CU g0 : ℝ) where
  chart : Vec 2 → Vec 2
  inverse : Vec 2 → Vec 2
  g : ℝ
  δ : ℝ
  s : ℝ
  hg : 0 ≤ g
  hgg0 : g ≤ g0
  hs : 0 < s
  hδ : 0 ≤ δ
  hδs : δ ≤ s
  /-- The order of the transition jets (finite, at least `2`). -/
  order : ℕ
  two_le : 2 ≤ order
  transition : IsCenteredTransition chart inverse g δ CU order
  /-- The inverse chart is smooth (no bounds), so pulled-back smooth tests stay smooth. -/
  inverse_smooth : ContDiff ℝ (⊤ : ℕ∞) inverse

namespace TransportCharts

variable {CU g0 : ℝ} (d : TransportCharts CU g0)

/-- Squared Japanese bracket at the slow scale. -/
def weight (z : Vec 2) : ℝ := 1 + d.s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)

theorem weight_one_le (z : Vec 2) : 1 ≤ d.weight z := by
  exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _)))

def jetBudget (CU g0 : ℝ) (L : ℕ) : ℝ :=
  1 + |CU| * g0 +
    ∑ j ∈ Finset.range (L + 1), |CU| * g0 * ((j - 1).factorial : ℝ) * |CU| ^ (j - 1)

include d in
theorem jetBudget_one_le (L : ℕ) : 1 ≤ jetBudget CU g0 L := by
  have hg0 := d.hg.trans d.hgg0
  have ha : 0 ≤ |CU| * g0 := mul_nonneg (abs_nonneg _) hg0
  have hc : 0 ≤ ∑ j ∈ Finset.range (L + 1),
      |CU| * g0 * ((j - 1).factorial : ℝ) * |CU| ^ (j - 1) := by
    exact Finset.sum_nonneg fun j _ => by positivity
  dsimp [jetBudget]
  linarith only [ha, hc]

/-- The first derivative of the inverse chart is bounded everywhere. -/
theorem inverse_fderiv_norm_le (z : Vec 2) : ‖fderiv ℝ d.inverse z‖ ≤ 1 + |CU| * g0 := by
  have hc : CU * d.g ≤ |CU| * g0 :=
    (mul_le_mul_of_nonneg_right (le_abs_self CU) d.hg).trans
      (mul_le_mul_of_nonneg_left d.hgg0 (abs_nonneg CU))
  calc ‖fderiv ℝ d.inverse z‖ ≤ ‖ContinuousLinearMap.id ℝ (Vec 2)‖ +
        ‖fderiv ℝ d.inverse z - ContinuousLinearMap.id ℝ (Vec 2)‖ :=
        norm_le_norm_add_norm_sub' _ _
    _ ≤ 1 + CU * d.g := add_le_add ContinuousLinearMap.norm_id_le (d.transition.dev.2 z)
    _ ≤ 1 + |CU| * g0 := by linarith only [hc]

theorem inverse_jet_bound (L j : ℕ) (hL : L ≤ d.order) (hj : 1 ≤ j) (hjL : j ≤ L) (z : Vec 2) :
    ‖iteratedFDeriv ℝ j d.inverse z‖ ≤ jetBudget CU g0 L * (d.s⁻¹)⁻¹ ^ (j - 1) := by
  have hg0 := d.hg.trans d.hgg0
  have hc : CU * d.g ≤ |CU| * g0 :=
    (mul_le_mul_of_nonneg_right (le_abs_self CU) d.hg).trans
      (mul_le_mul_of_nonneg_left d.hgg0 (abs_nonneg CU))
  have hsum : 0 ≤ ∑ j ∈ Finset.range (L + 1),
      |CU| * g0 * ((j - 1).factorial : ℝ) * |CU| ^ (j - 1) := by
    exact Finset.sum_nonneg fun j _ => by positivity
  rw [inv_inv]
  by_cases hj1 : j = 1
  · subst j
    rw [Nat.sub_self, pow_zero, mul_one, norm_iteratedFDeriv_one]
    refine (d.inverse_fderiv_norm_le z).trans ?_
    dsimp [jetBudget]
    linarith only [hsum]
  · have hj2 : 2 ≤ j := by omega
    have hco : 0 ≤ CU * d.g := (norm_nonneg _).trans (d.transition.dev.1 0)
    have hpow : (CU * d.δ) ^ (j - 1) ≤ (|CU| * d.s) ^ (j - 1) := by
      calc _ ≤ |(CU * d.δ) ^ (j - 1)| := le_abs_self _
           _ = (|CU| * d.δ) ^ (j - 1) := by rw [abs_pow, abs_mul, abs_of_nonneg d.hδ]
           _ ≤ _ := pow_le_pow_left₀ (mul_nonneg (abs_nonneg CU) d.hδ)
             (mul_le_mul_of_nonneg_left d.hδs (abs_nonneg CU)) _
    have hb : |CU| * g0 * ((j - 1).factorial : ℝ) * |CU| ^ (j - 1) ≤ jetBudget CU g0 L := by
      have ht := Finset.single_le_sum (f := fun j =>
        |CU| * g0 * ((j - 1).factorial : ℝ) * |CU| ^ (j - 1))
        (fun j _ => by positivity) (Finset.mem_range.mpr (by omega : j < L + 1))
      dsimp [jetBudget]
      exact ht.trans (le_add_of_nonneg_left (by positivity))
    calc _ ≤ CU * d.g * ((j - 1).factorial : ℝ) * (CU * d.δ) ^ (j - 1) :=
          (d.transition.jets j hj2 (hjL.trans hL) z).2
         _ ≤ (CU * d.g * ((j - 1).factorial : ℝ)) * (|CU| * d.s) ^ (j - 1) :=
          mul_le_mul_of_nonneg_left hpow (mul_nonneg hco (Nat.cast_nonneg _))
         _ ≤ (|CU| * g0 * ((j - 1).factorial : ℝ)) * (|CU| * d.s) ^ (j - 1) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _))
            (pow_nonneg (mul_nonneg (abs_nonneg CU) d.hs.le) _)
         _ = (|CU| * g0 * ((j - 1).factorial : ℝ) * |CU| ^ (j - 1)) * d.s ^ (j - 1) := by
          rw [mul_pow]; ring
         _ ≤ _ := mul_le_mul_of_nonneg_right hb (pow_nonneg d.hs.le _)

/-- The inverse chart moves the slow weight by a bounded factor. -/
theorem inverse_weight_bound (z : Vec 2) :
    d.weight (d.inverse z) ≤ (2 * (1 + |CU| * g0) ^ 2) * d.weight z := by
  have hg0 := d.hg.trans d.hgg0
  have ha : 0 ≤ |CU| * g0 := mul_nonneg (abs_nonneg _) hg0
  have h0 : d.inverse 0 = 0 := by
    have h := d.transition.left_inv 0
    rwa [d.transition.centered] at h
  have hdiff : Differentiable ℝ d.inverse :=
    d.inverse_smooth.differentiable (by simp)
  have hlip : ‖d.inverse z‖ ≤ (1 + |CU| * g0) * ‖z‖ := by
    have h := convex_univ.norm_image_sub_le_of_norm_fderiv_le
      (fun x _ => hdiff x) (fun x _ => d.inverse_fderiv_norm_le x)
      (Set.mem_univ (0 : Vec 2)) (Set.mem_univ z)
    simpa only [h0, sub_zero] using h
  have hcoord (w : Vec 2) (i : Fin 2) : w i ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _)
      (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm w i) 2
  have hz : ‖z‖ ^ 2 ≤ z 0 ^ 2 + z 1 ^ 2 := by
    have hq : 0 ≤ z 0 ^ 2 + z 1 ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
    have hn : ‖z‖ ≤ Real.sqrt (z 0 ^ 2 + z 1 ^ 2) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
      rw [Real.norm_eq_abs]
      apply Real.abs_le_sqrt
      fin_cases i
      · exact le_add_of_nonneg_right (sq_nonneg _)
      · exact le_add_of_nonneg_left (sq_nonneg _)
    calc ‖z‖ ^ 2 ≤ Real.sqrt (z 0 ^ 2 + z 1 ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ = _ := Real.sq_sqrt hq
  have hw : ‖d.inverse z‖ ^ 2 ≤ (1 + |CU| * g0) ^ 2 * (z 0 ^ 2 + z 1 ^ 2) := by
    calc ‖d.inverse z‖ ^ 2 ≤ ((1 + |CU| * g0) * ‖z‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hlip 2
      _ = (1 + |CU| * g0) ^ 2 * ‖z‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hz (sq_nonneg _)
  have hK : 1 ≤ 2 * (1 + |CU| * g0) ^ 2 := by nlinarith only [ha]
  have hs2 : 0 ≤ d.s ^ 2 := sq_nonneg _
  have hpair : d.inverse z 0 ^ 2 + d.inverse z 1 ^ 2 ≤ 2 * ‖d.inverse z‖ ^ 2 := by
    linarith only [hcoord (d.inverse z) 0, hcoord (d.inverse z) 1]
  have hzq : 0 ≤ z 0 ^ 2 + z 1 ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  dsimp only [weight]
  calc 1 + d.s ^ 2 * (d.inverse z 0 ^ 2 + d.inverse z 1 ^ 2)
      ≤ 1 + d.s ^ 2 * (2 * ((1 + |CU| * g0) ^ 2 * (z 0 ^ 2 + z 1 ^ 2))) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (hpair.trans
          (by linarith only [hw] : 2 * ‖d.inverse z‖ ^ 2 ≤
            2 * ((1 + |CU| * g0) ^ 2 * (z 0 ^ 2 + z 1 ^ 2)))) hs2)
    _ = 1 + 2 * (1 + |CU| * g0) ^ 2 * (d.s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) := by ring
    _ ≤ 2 * (1 + |CU| * g0) ^ 2 +
          2 * (1 + |CU| * g0) ^ 2 * (d.s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) := by
        linarith only [hK]
    _ = _ := by ring

end TransportCharts

/-- A bounded change of the weight is absorbed at the same negative weight. -/
theorem negative_weight_budget {X Y K : ℝ} (hX : 1 ≤ X) (hY : 1 ≤ Y) (hK : 1 ≤ K)
    (hXY : X ≤ K * Y) (p : ℕ) :
    Y ^ (-(p : ℝ) / 2) ≤ K ^ p * X ^ (-(p : ℝ) / 2) := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hYp : 0 < Y := zero_lt_one.trans_le hY
  have hKp : 0 < K := zero_lt_one.trans_le hK
  have hh : X ^ ((p : ℝ) / 2) ≤ K ^ p * Y ^ ((p : ℝ) / 2) := by
    calc X ^ ((p : ℝ) / 2) ≤ (K * Y) ^ ((p : ℝ) / 2) :=
          Real.rpow_le_rpow hXp.le hXY (by positivity)
         _ = K ^ ((p : ℝ) / 2) * Y ^ ((p : ℝ) / 2) := Real.mul_rpow hKp.le hYp.le
         _ ≤ K ^ (p : ℝ) * Y ^ ((p : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hK
            (by have hp := (Nat.cast_nonneg p : (0 : ℝ) ≤ (p : ℝ)); linarith only [hp]))
            (Real.rpow_nonneg hYp.le _)
         _ = _ := by rw [Real.rpow_natCast]
  rw [show -(p : ℝ) / 2 = -((p : ℝ) / 2) by ring, Real.rpow_neg hXp.le, Real.rpow_neg hYp.le]
  apply (le_mul_inv_iff₀ (Real.rpow_pos_of_pos hXp _)).mpr
  apply (inv_mul_le_iff₀ (Real.rpow_pos_of_pos hYp _)).mpr
  simpa only [mul_comm] using hh

end AVRegularity.CycleWords.Seam
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! Pointwise scale-sensitive chain rule for the negative seam test weight. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The scalar integrand defining one summand of the weighted jet norm. -/
def scaledJet (p s r : ℝ) (a : ℕ) (f : Vec 2 → E) (z : Vec 2) : ℝ :=
  (r ^ a / (a.factorial : ℝ)) * (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (p / 2) *
    wordSize a (fun w => orderedDerivative w f z)

def transportWeightConstant (CU g0 : ℝ) : ℝ :=
  2 * (1 + |CU| * g0) ^ 2

def transportCompositionConstant (CU g0 : ℝ) (L p : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 * L) * TransportCharts.jetBudget CU g0 L ^ L *
    transportWeightConstant CU g0 ^ p

theorem transportWeightConstant_one_le {CU g0 : ℝ} (d : TransportCharts CU g0) :
    1 ≤ transportWeightConstant CU g0 := by
  have ha : 0 ≤ |CU| * g0 := mul_nonneg (abs_nonneg _) (d.hg.trans d.hgg0)
  unfold transportWeightConstant
  nlinarith only [ha]

theorem transportCompositionConstant_nonneg {CU g0 : ℝ} (d : TransportCharts CU g0) (L p : ℕ) :
    0 ≤ transportCompositionConstant CU g0 L p := by
  have hb := zero_le_one.trans (d.jetBudget_one_le L)
  unfold transportCompositionConstant transportWeightConstant
  positivity

theorem scaledJet_nonneg (p s : ℝ) {r : ℝ} (hr : 0 ≤ r) (a : ℕ) (f : Vec 2 → E) (z : Vec 2) :
    0 ≤ scaledJet p s r a f z := by
  unfold scaledJet wordSize
  positivity

theorem scaledJet_continuous (p s r : ℝ) (a : ℕ) {f : Vec 2 → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Continuous (scaledJet p s r a f) := by
  apply (continuous_const.mul (Assembly.weight_continuous s p)).mul
  unfold wordSize
  apply Real.continuous_sqrt.comp
  exact continuous_finsetSum _ fun w _ =>
    ((Assembly.orderedDerivative_continuous w (hf.of_le (by simp))).norm.pow 2)

theorem inverse_scaledJet_le {CU g0 : ℝ} (d : TransportCharts CU g0) (L p a : ℕ)
    (hL : L ≤ d.order) (ha : a ≤ L) {r : ℝ} (hr : 0 < r) (hrs : r ≤ d.s⁻¹) {f : Vec 2 → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (z : Vec 2) :
    scaledJet (-(p : ℝ)) d.s r a (f ∘ d.inverse) z ≤
      ∑ i ∈ Finset.range (a + 1),
        (transportCompositionConstant CU g0 L p * (i.factorial : ℝ)) *
          scaledJet (-(p : ℝ)) d.s r i f (d.inverse z) := by
  let B := TransportCharts.jetBudget CU g0 L
  let P := d.weight z
  let Q := d.weight (d.inverse z)
  let K := transportWeightConstant CU g0
  let V := ∑ i ∈ Finset.range (a + 1),
    r ^ i * wordSize i (fun w => orderedDerivative w f (d.inverse z))
  have hB : 1 ≤ B := d.jetBudget_one_le L
  have hP : 1 ≤ P := d.weight_one_le z
  have hQ : 1 ≤ Q := d.weight_one_le (d.inverse z)
  have hK : 1 ≤ K := transportWeightConstant_one_le d
  have hV : 0 ≤ V := Finset.sum_nonneg fun i _ =>
    mul_nonneg (pow_nonneg hr.le _) (Real.sqrt_nonneg _)
  have hcomp := ChartTransport.scaled_comp_bound
    (hf.of_le (by simp) : ContDiff ℝ (a : ℕ∞) f)
    (d.inverse_smooth.of_le (by simp) : ContDiff ℝ (a : ℕ∞) d.inverse)
    (D := B) (Rχ := d.s⁻¹) hB hr hrs z
    (fun j hj hja => d.inverse_jet_bound L j hL hj (hja.trans ha) z)
  have houter : (∑ i ∈ Finset.range (a + 1), r ^ i * ‖iteratedFDeriv ℝ i f (d.inverse z)‖) ≤
      (2 : ℝ) ^ L * V := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hiL : i ≤ L := (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans ha
    have hn : ‖iteratedFDeriv ℝ i f (d.inverse z)‖ ≤
        (2 : ℝ) ^ L * wordSize i (fun w => orderedDerivative w f (d.inverse z)) := by
      apply (ChartTransport.norm_iteratedFDeriv_le_sum_words (hf.of_le (by simp)) _).trans
      calc _ ≤ ∑ _w : DerivativeWord2 i, wordSize i
              (fun w => orderedDerivative w f (d.inverse z)) :=
            Finset.sum_le_sum fun w _ => norm_le_wordSize _ w
           _ = (2 : ℝ) ^ i * wordSize i (fun w => orderedDerivative w f (d.inverse z)) := by
            simp [DerivativeWord2, DerivativeWord]
           _ ≤ _ := mul_le_mul_of_nonneg_right
            (pow_le_pow_right₀ (by norm_num) hiL) (Real.sqrt_nonneg _)
    simpa only [mul_assoc, mul_left_comm, mul_comm] using mul_le_mul_of_nonneg_left hn
      (pow_nonneg hr.le i)
  have hword := wordSize_le_card_mul
    (fun w : DerivativeWord2 a => orderedDerivative w (f ∘ d.inverse) z)
    (norm_nonneg (iteratedFDeriv ℝ a (f ∘ d.inverse) z))
    (fun w => ChartTransport.norm_orderedDerivative_le
      ((hf.of_le (by simp)).comp
        (d.inverse_smooth.of_le (by simp) : ContDiff ℝ (a : ℕ∞) d.inverse)) w z)
  have hjet : r ^ a * wordSize a (fun w => orderedDerivative w (f ∘ d.inverse) z) ≤
      (2 : ℝ) ^ L * ((a.factorial : ℝ) * B ^ a * ((2 : ℝ) ^ L * V)) := by
    calc _ ≤ r ^ a * ((2 : ℝ) ^ a * ‖iteratedFDeriv ℝ a (f ∘ d.inverse) z‖) :=
          mul_le_mul_of_nonneg_left hword (pow_nonneg hr.le a)
         _ = (2 : ℝ) ^ a * (r ^ a * ‖iteratedFDeriv ℝ a (f ∘ d.inverse) z‖) := by ring
         _ ≤ (2 : ℝ) ^ L * ((a.factorial : ℝ) * B ^ a * ((2 : ℝ) ^ L * V)) :=
          mul_le_mul (pow_le_pow_right₀ (by norm_num) ha)
            (hcomp.trans (mul_le_mul_of_nonneg_left houter (by positivity)))
              (mul_nonneg (pow_nonneg hr.le _) (norm_nonneg _)) (by positivity)
  have hweight : P ^ (-(p : ℝ) / 2) ≤ K ^ p * Q ^ (-(p : ℝ) / 2) :=
    negative_weight_budget hQ hP hK (d.inverse_weight_bound z) p
  have hBa : B ^ a ≤ B ^ L := pow_le_pow_right₀ hB ha
  have hfac : (0 : ℝ) < a.factorial := Nat.cast_pos.mpr (Nat.factorial_pos a)
  have hqout : 0 ≤ P ^ (-(p : ℝ) / 2) := Real.rpow_nonneg (zero_le_one.trans hP) _
  have hbudget : (r ^ a / (a.factorial : ℝ)) * P ^ (-(p : ℝ) / 2) *
        wordSize a (fun w => orderedDerivative w (f ∘ d.inverse) z) ≤
      transportCompositionConstant CU g0 L p * (Q ^ (-(p : ℝ) / 2) * V) := by
    calc _ = (P ^ (-(p : ℝ) / 2) / (a.factorial : ℝ)) *
            (r ^ a * wordSize a (fun w => orderedDerivative w (f ∘ d.inverse) z)) := by ring
         _ ≤ (P ^ (-(p : ℝ) / 2) / (a.factorial : ℝ)) *
            ((2 : ℝ) ^ L * ((a.factorial : ℝ) * B ^ a * ((2 : ℝ) ^ L * V))) :=
          mul_le_mul_of_nonneg_left hjet (div_nonneg hqout hfac.le)
         _ = ((2 : ℝ) ^ (2 * L) * B ^ a) * (P ^ (-(p : ℝ) / 2) * V) := by
          rw [show 2 * L = L + L by omega, pow_add]
          field_simp
         _ ≤ ((2 : ℝ) ^ (2 * L) * B ^ L) * ((K ^ p * Q ^ (-(p : ℝ) / 2)) * V) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hBa (by positivity))
            (mul_le_mul_of_nonneg_right hweight hV) (by positivity) (by positivity)
         _ = _ := by unfold transportCompositionConstant; dsimp [B, K]; ring
  change (r ^ a / (a.factorial : ℝ)) * P ^ (-(p : ℝ) / 2) * _ ≤ _
  apply hbudget.trans_eq
  dsimp [V, scaledJet, Q, TransportCharts.weight]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi : (i.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
  field_simp
end

/-! The positive test norm is bounded uniformly under inverse seam composition. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ v, NormedAddCommGroup (h v)] [∀ v, NormedSpace ℝ (h v)]

/-- The definition of the weighted jet norm with the factorial and scale inside the `L²` norm. -/
theorem weightedJetNorm_eq_sum_scaledJet (π : ι → ℝ) (p s : ℝ) {r : ℝ} (hr : 0 ≤ r)
    (L : ℕ) (f : ∀ v, Vec 2 → h v) :
    weightedJetNorm π p L s r (fun v _ w z => orderedDerivative w (f v) z) =
      ∑ a ∈ Finset.range (L + 1),
        familyNorm (fun v => ENNReal.ofReal (π v)⁻¹)
          (fun v => eLpNorm (scaledJet p s r a (f v)) 2 volume) := by
  unfold weightedJetNorm
  apply Finset.sum_congr rfl
  intro a _
  have hcoeff : 0 ≤ r ^ a / (a.factorial : ℝ) := by positivity
  have he (v : ι) : eLpNorm (scaledJet p s r a (f v)) 2 volume =
      ENNReal.ofReal (r ^ a / (a.factorial : ℝ)) *
        eLpNorm (fun z => (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (p / 2) *
          wordSize a (fun w => orderedDerivative w (f v) z)) 2 volume := by
    have hh := eLpNorm_const_smul (r ^ a / (a.factorial : ℝ))
      (fun z => (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (p / 2) *
        wordSize a (fun w => orderedDerivative w (f v) z)) 2 (volume : Measure (Vec 2))
    change eLpNorm (fun z => (r ^ a / (a.factorial : ℝ)) *
      (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (p / 2) *
        wordSize a (fun w => orderedDerivative w (f v) z)) 2 volume = _
    simpa only [Pi.smul_def, smul_eq_mul, mul_assoc, ← ofReal_norm,
      Real.norm_eq_abs, abs_of_nonneg hcoeff] using hh
  simp only [he, familyNorm_mul]
  rfl

def transportTestConstant (CU g0 : ℝ) (L p : ℕ) : ℝ :=
  (L + 1) * (transportCompositionConstant CU g0 L p * (L.factorial : ℝ))

/-- Inverse transport on smooth tests keeps the negative weight. -/
theorem inverse_test_norm_le {CU g0 : ℝ} (d : TransportCharts CU g0) (L p : ℕ) (hL : L ≤ d.order)
    (π : ι → ℝ) {r : ℝ} (hr : 0 < r) (hrs : r ≤ d.s⁻¹)
    (f : ∀ v, Vec 2 → h v) (hf : ∀ v, ContDiff ℝ (⊤ : ℕ∞) (f v)) :
    weightedJetNorm π (-(p : ℝ)) L d.s r
        (fun v _ w z => orderedDerivative w (f v ∘ d.inverse) z) ≤
      ENNReal.ofReal (transportTestConstant CU g0 L p) *
        weightedJetNorm π (-(p : ℝ)) L d.s r
          (fun v _ w z => orderedDerivative w (f v) z) := by
  let c : ι → ℝ≥0∞ := fun v => ENNReal.ofReal (π v)⁻¹
  let A := transportCompositionConstant CU g0 L p
  let U (a : ℕ) := familyNorm c (fun v => eLpNorm (scaledJet (-(p : ℝ)) d.s r a (f v)) 2 volume)
  have hA : 0 ≤ A := transportCompositionConstant_nonneg d L p
  have hi : ContDiff ℝ (⊤ : ℕ∞) d.inverse := d.inverse_smooth
  let H := centeredTransitionHomeomorph d.chart d.inverse d.g d.δ CU (d.transition.mono d.two_le)
  have hmp : MeasurePreserving d.inverse volume volume :=
    MeasurePreserving.symm H.toMeasurableEquiv
      (centeredTransition_measurePreserving _ _ _ _ _ (d.transition.mono d.two_le))
  have hterm (a : ℕ) (ha : a ∈ Finset.range (L + 1)) :
      familyNorm c (fun v => eLpNorm
        (scaledJet (-(p : ℝ)) d.s r a (f v ∘ d.inverse)) 2 volume) ≤
        ENNReal.ofReal (A * (L.factorial : ℝ)) * ∑ i ∈ Finset.range (L + 1), U i := by
    have haL : a ≤ L := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    have hmaj := familyNorm_eLpNorm_majorant c (Finset.range (a + 1))
      (fun i => A * (i.factorial : ℝ)) (fun i _ => mul_nonneg hA (Nat.cast_nonneg _))
      (fun v => scaledJet (-(p : ℝ)) d.s r a (f v ∘ d.inverse))
      (fun v => (scaledJet_continuous _ _ _ _ ((hf v).comp hi)).aestronglyMeasurable)
      (fun i v => scaledJet (-(p : ℝ)) d.s r i (f v) ∘ d.inverse)
      (fun v z => by
        rw [abs_of_nonneg (scaledJet_nonneg _ _ hr.le _ _ _)]
        exact inverse_scaledJet_le d L p a hL haL hr hrs (hf v) z)
    have he (i : ℕ) (v : ι) :
        eLpNorm (scaledJet (-(p : ℝ)) d.s r i (f v) ∘ d.inverse) 2 volume =
          eLpNorm (scaledJet (-(p : ℝ)) d.s r i (f v)) 2 volume :=
      eLpNorm_comp_measurePreserving (scaledJet_continuous _ _ _ _ (hf v)).aestronglyMeasurable hmp
    simp only [he] at hmaj
    refine hmaj.trans ?_
    calc _ ≤ ∑ i ∈ Finset.range (a + 1), ENNReal.ofReal (A * (L.factorial : ℝ)) * U i := by
          apply Finset.sum_le_sum
          intro i hi
          apply mul_le_mul' ?_ le_rfl
          apply ENNReal.ofReal_le_ofReal
          exact mul_le_mul_of_nonneg_left (by
            exact_mod_cast Nat.factorial_le
              ((Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans haL)) hA
         _ ≤ ∑ i ∈ Finset.range (L + 1), ENNReal.ofReal (A * (L.factorial : ℝ)) * U i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.add_le_add_right haL 1))
            (fun _ _ _ => zero_le)
         _ = _ := (Finset.mul_sum _ _ _).symm
  rw [weightedJetNorm_eq_sum_scaledJet π _ _ hr.le,
    weightedJetNorm_eq_sum_scaledJet π _ _ hr.le]
  calc _ ≤ ∑ _a ∈ Finset.range (L + 1), ENNReal.ofReal (A * (L.factorial : ℝ)) *
          ∑ i ∈ Finset.range (L + 1), U i := Finset.sum_le_sum hterm
       _ = ENNReal.ofReal (transportTestConstant CU g0 L p) *
          ∑ i ∈ Finset.range (L + 1), U i := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        simp only [transportTestConstant, A, Nat.cast_add, Nat.cast_one]
end

/-! Exact volume-preserving transport in the weighted negative seam norm. -/

section
universe u v

section Homogeneity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem scaledJet_smul (p s r : ℝ) (a : ℕ) {f : Vec 2 → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {c : ℝ} (hc : 0 ≤ c) :
    scaledJet p s r a (fun z => c • f z) = c • scaledJet p s r a f := by
  have he (w : DerivativeWord2 a) : orderedDerivative w (fun z => c • f z) =
      fun z => c • orderedDerivative w f z := by
    simpa only [smul_apply, ContinuousLinearMap.id_apply] using
      orderedDerivative_clm_comp (c • ContinuousLinearMap.id ℝ E) w (hf.of_le (by simp))
  funext z
  dsimp only [scaledJet, wordSize, Pi.smul_apply, smul_eq_mul]
  simp_rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, mul_pow, ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
  ring

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ x, NormedAddCommGroup (h x)] [∀ x, NormedSpace ℝ (h x)]

private theorem testNorm_smul (π : ι → ℝ) (p s : ℝ) {r : ℝ} (hr : 0 ≤ r)
    (L : ℕ) (f : ∀ x, Vec 2 → h x) (hf : ∀ x, ContDiff ℝ (⊤ : ℕ∞) (f x))
    {c : ℝ} (hc : 0 ≤ c) :
    weightedJetNorm π p L s r (fun x _ w z => orderedDerivative w (fun z => c • f x z) z) =
      ENNReal.ofReal c * weightedJetNorm π p L s r (fun x _ w z => orderedDerivative w (f x) z) := by
  rw [weightedJetNorm_eq_sum_scaledJet π p s hr, weightedJetNorm_eq_sum_scaledJet π p s hr,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [scaledJet_smul p s r a (hf _) hc, eLpNorm_const_smul,
    ← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hc, familyNorm_mul]

end Homogeneity

/-- Weighted negative seam transport at the same weight, with constants uniform in all scales
and finite component Hilbert spaces. -/
theorem seamTransport : Assembly.SeamTransportStatement.{u, v} := by
  intro L p CU g0
  let C := transportTestConstant CU g0 L p + 1
  refine ⟨max 1 C, zero_le_one.trans (le_max_left _ _), ?_⟩
  intro ι _ h _ _ _ _ _ _ π _hπ Υ Υinv gU δ s ηg r hgU hgg0 hΥ hΥs hs _hs1 hηg hηg1 hδ hr hrs g _hg
  let d : TransportCharts CU g0 := {
    chart := Υ
    inverse := Υinv
    g := gU
    δ := δ
    s := s
    hg := hgU
    hgg0 := hgg0
    hs := hs
    hδ := hδ ▸ mul_nonneg hs.le hηg
    hδs := hδ ▸ (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hηg1 hs.le)
    order := max L 2
    two_le := le_max_right L 2
    transition := hΥ
    inverse_smooth := hΥs }
  have hC : 0 < max 1 C := zero_lt_one.trans_le (le_max_left _ _)
  have hbound : transportTestConstant CU g0 L p ≤ max 1 C :=
    (le_add_of_nonneg_right zero_le_one).trans (le_max_right _ _)
  let H := centeredTransitionHomeomorph Υ Υinv gU δ CU (hΥ.mono (le_max_right L 2))
  have hmp := centeredTransition_measurePreserving Υ Υinv gU δ CU (hΥ.mono (le_max_right L 2))
  have hi : ContDiff ℝ (⊤ : ℕ∞) Υinv := hΥs
  unfold Assembly.negJetNorm
  refine iSup_le fun φ => iSup_le fun hφ => iSup_le fun hnorm => ?_
  let ψ : ∀ x, Vec 2 → h x := fun x z => (max 1 C)⁻¹ • φ x (Υinv z)
  have hψ : ∀ x, ContDiff ℝ (⊤ : ℕ∞) (ψ x) ∧ HasCompactSupport (ψ x) := by
    intro x
    refine ⟨((hφ x).1.comp hi).const_smul _, ?_⟩
    exact ((hφ x).2.comp_homeomorph H.symm).smul_left (f := fun _ => (max 1 C)⁻¹)
  have hn : weightedJetNorm π (-(p : ℝ)) L s r
      (fun x _ w z => orderedDerivative w (ψ x) z) ≤ 1 := by
    change weightedJetNorm π (-(p : ℝ)) L s r
      (fun x _ w z => orderedDerivative w (fun z => (max 1 C)⁻¹ • (φ x ∘ Υinv) z) z) ≤ 1
    rw [testNorm_smul π _ s hr.le L (fun x => φ x ∘ Υinv)
      (fun x => (hφ x).1.comp hi) (inv_nonneg.mpr hC.le)]
    have hb := inverse_test_norm_le d L p (le_max_left L 2) π hr hrs φ (fun x => (hφ x).1)
    have hh : weightedJetNorm π (-(p : ℝ)) L s r
        (fun x _ w z => orderedDerivative w (φ x ∘ Υinv) z) ≤ ENNReal.ofReal (max 1 C) :=
      (hb.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hbound) hnorm)).trans_eq (mul_one _)
    apply (mul_le_mul' le_rfl hh).trans_eq
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hC.le), inv_mul_cancel₀ hC.ne', ENNReal.ofReal_one]
  have he (x : ι) : (∫ z, inner ℝ (g x (Υ z)) (φ x z)) =
      (max 1 C) * ∫ z, inner ℝ (g x z) (ψ x z) := by
    have ht := hmp.integral_comp H.measurableEmbedding
      (fun z => inner ℝ (g x z) (φ x (Υinv z)))
    simp only [(hΥ.mono (le_max_right L 2)).left_inv] at ht
    rw [ht]
    simp only [ψ, real_inner_smul_right, integral_const_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul]
  have hpair : (∑ x, (π x)⁻¹ * ∫ z, inner ℝ (g x (Υ z)) (φ x z)) =
      (max 1 C) * ∑ x, (π x)⁻¹ * ∫ z, inner ℝ (g x z) (ψ x z) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [he]
    ring
  rw [hpair, abs_mul, abs_of_pos hC, ENNReal.ofReal_mul hC.le]
  apply mul_le_mul' le_rfl
  exact le_iSup_of_le ψ (le_iSup_of_le hψ (le_iSup_of_le hn le_rfl))
end

end AVRegularity.CycleWords.Seam
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped Convolution
namespace AVRegularity.CycleWords.Seam

/-! Smooth translation pairings of rough `L²` inputs with compact smooth tests. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The exact pairing against a spatially translated test, represented as a convolution. -/
def cutoffComponentPair (g φ : Vec 2 → E) : Vec 2 → ℝ :=
  φ ⋆[innerSL ℝ, volume] (fun z => g (-z))

theorem cutoffComponentPair_eq_integral (g φ : Vec 2 → E) (x : Vec 2) :
    cutoffComponentPair g φ x = ∫ z, inner ℝ (g z) (φ (z + x)) := by
  unfold cutoffComponentPair convolution
  rw [← integral_add_right_eq_self (μ := volume)
    (fun z : Vec 2 => (innerSL ℝ) (φ z) (g (-(x - z)))) x]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    change inner ℝ (φ (z + x)) (g (-(x - (z + x)))) = inner ℝ (g z) (φ (z + x))
    rw [show -(x - (z + x)) = z by abel]
    exact real_inner_comm _ _

theorem cutoffComponentPair_contDiff (g φ : Vec 2 → E) (hg : MemLp g 2 volume)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    ContDiff ℝ (⊤ : ℕ∞) (cutoffComponentPair g φ) := by
  have hgn : LocallyIntegrable (fun z : Vec 2 => g (-z)) volume :=
    (hg.comp_measurePreserving (Measure.measurePreserving_neg volume)).locallyIntegrable (by norm_num)
  exact hc.contDiff_convolution_left (innerSL ℝ) hφ hgn

/-- Differentiating the translation pairing differentiates only the compact test. -/
theorem cutoffComponentPair_fderiv (g φ : Vec 2 → E) (hg : MemLp g 2 volume)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (x y : Vec 2) :
    fderiv ℝ (cutoffComponentPair g φ) x y =
      cutoffComponentPair g (fun z => fderiv ℝ φ z y) x := by
  have hgn : LocallyIntegrable (fun z : Vec 2 => g (-z)) volume :=
    (hg.comp_measurePreserving (Measure.measurePreserving_neg volume)).locallyIntegrable (by norm_num)
  have hd := hc.hasFDerivAt_convolution_left (innerSL ℝ) (hφ.of_le (by simp)) hgn x
  change fderiv ℝ (φ ⋆[innerSL ℝ, volume] (fun z => g (-z))) x y = _
  rw [hd.fderiv]
  have hi := (hc.fderiv ℝ).convolutionExists_left ((innerSL ℝ).precompL (Vec 2))
    (hφ.continuous_fderiv (by simp)) hgn x
  change (∫ z : Vec 2, ((innerSL ℝ).precompL (Vec 2))
    (fderiv ℝ φ z) (g (-(x - z)))) y = _
  rw [ContinuousLinearMap.integral_apply hi]
  rfl

/-- The ordered derivative of the pairing is the pairing with the exact ordered test. -/
theorem cutoffComponentPair_orderedDerivative (g φ : Vec 2 → E) (hg : MemLp g 2 volume)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    {a : ℕ} (w : DerivativeWord2 a) :
    orderedDerivative w (cutoffComponentPair g φ) =
      cutoffComponentPair g (orderedDerivative w φ) := by
  induction a with
  | zero =>
    simp only [orderedDerivative_zero]
  | succ a ih =>
    rw [orderedDerivative_succ, orderedDerivative_succ, ih]
    funext x
    apply cutoffComponentPair_fderiv g _ hg
    · exact AVRegularity.orderedDerivative_contDiff
        (fun i => w i.castSucc) hφ
    · exact orderedDerivative_hasCompactSupport hc _

/-- The translation pairing is the genuine `L²` pairing. -/
theorem cutoffComponentPair_eq_inner (g φ : Vec 2 → E) (hg : MemLp g 2 volume)
    (hφ : MemLp φ 2 volume) (x : Vec 2) :
    cutoffComponentPair g φ x = inner ℝ (hg.toLp g)
      (Analysis.Convolution.translation (-x) (hφ.toLp φ)) := by
  rw [cutoffComponentPair_eq_integral, L2.inner_def]
  apply integral_congr_ae
  have hs := (measurePreserving_add_right volume x).quasiMeasurePreserving.ae_eq_comp hφ.coeFn_toLp
  filter_upwards [hg.coeFn_toLp, Analysis.Convolution.translation_ae (-x) (hφ.toLp φ), hs]
    with z hgz ht hz
  simp only [Function.comp_apply] at hz
  rw [hgz, ht, sub_neg_eq_add, hz]

theorem cutoffComponentPair_abs_le (g φ : Vec 2 → E) (hg : MemLp g 2 volume)
    (hφ : MemLp φ 2 volume) (x : Vec 2) :
    |cutoffComponentPair g φ x| ≤ ‖hg.toLp g‖ * ‖hφ.toLp φ‖ := by
  rw [cutoffComponentPair_eq_inner g φ hg hφ x]
  exact (abs_real_inner_le_norm _ _).trans_eq (by rw [Analysis.Convolution.translation_norm])

theorem cutoff_fourierCutoff_congr_ae (m : Vec 2 → ℝ) {g g' : Vec 2 → E}
    (hg : g =ᵐ[volume] g') : fourierCutoff m g = fourierCutoff m g' := by
  funext y
  unfold fourierCutoff
  apply integral_congr_ae
  have hs := (volume.measurePreserving_sub_left y).quasiMeasurePreserving.ae_eq_comp hg
  filter_upwards [hs] with z hz
  exact congrArg (fun v : E => cutoffKernel m z • v) hz

variable [CompleteSpace E]

/-- Pair the actual cutoff complement by moving its translations onto the compact test. -/
theorem cutoffComponentPair_complement_eq (m : Vec 2 → ℝ) (R : ℝ)
    (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0)
    (hs : ContDiff ℝ (⊤ : ℕ∞) m) (g φ : Vec 2 → E)
    (hg : MemLp g 2 volume) (hφ : MemLp φ 2 volume) :
    (∫ z, inner ℝ (g z - fourierCutoff m g z) (φ z)) =
      cutoffComponentPair g φ 0 - ∫ y, cutoffKernel m y * cutoffComponentPair g φ y := by
  let gL := hg.toLp g
  let φL := hφ.toLp φ
  let Ag := seamCutoffL2 m R hm hs gL
  have hAg : Ag =ᵐ[volume] fourierCutoff m g := by
    have hh := seamCutoffL2_ae m R hm hs gL
    rwa [cutoff_fourierCutoff_congr_ae m hg.coeFn_toLp] at hh
  have hdiff : gL - Ag =ᵐ[volume] fun z => g z - fourierCutoff m g z := by
    filter_upwards [Lp.coeFn_sub gL Ag, hg.coeFn_toLp, hAg] with z hz hg' hA'
    rw [hz, Pi.sub_apply, hg', hA']
  have hpair : (∫ z, inner ℝ (g z - fourierCutoff m g z) (φ z)) =
      inner ℝ (gL - Ag) φL := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hdiff, hφ.coeFn_toLp] with z hz hφz
    rw [hz, hφz]
  have hzero : cutoffComponentPair g φ 0 = inner ℝ gL φL := by
    rw [cutoffComponentPair_eq_inner g φ hg hφ 0, neg_zero, Analysis.Convolution.translation_zero]
  have havg : inner ℝ Ag φL = ∫ y, cutoffKernel m y * cutoffComponentPair g φ y := by
    let ρ := Analysis.Convolution.displacement 1 (ContinuousLinearMap.id ℝ (Vec 2))
    change inner ℝ (Analysis.Convolution.averagingOperator ρ
      (Analysis.Convolution.continuous_displacement _ _) (cutoffKernel m)
      (seamCutoffKernel_integrable m R hm hs) gL) φL = _
    rw [Analysis.Convolution.averagingOperator_inner]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      have hρ : ρ y = y := by
        simp only [ρ, Analysis.Convolution.displacement_apply, ContinuousLinearMap.id_apply, one_smul]
      change cutoffKernel m y * (∫ z, inner ℝ (gL (z - ρ y)) (φL z)) =
        cutoffKernel m y * cutoffComponentPair g φ y
      rw [hρ, cutoffComponentPair_eq_integral]
      congr 1
      have hgshift := (measurePreserving_add_right volume (-y)).quasiMeasurePreserving.ae_eq_comp hg.coeFn_toLp
      have hi : (∫ z, inner ℝ (gL (z - y)) (φL z)) =
          ∫ z, inner ℝ (g (z - y)) (φ z) := by
        apply integral_congr_ae
        filter_upwards [hgshift, hφ.coeFn_toLp] with z hz hφz
        simp only [Function.comp_apply, ← sub_eq_add_neg] at hz
        rw [hz, hφz]
      rw [hi]
      have h := integral_add_right_eq_self (μ := volume)
        (fun z : Vec 2 => inner ℝ (g (z - y)) (φ z)) y
      simpa only [add_sub_cancel_right] using h.symm
  rw [hpair, inner_sub_left, ← hzero, havg]

section Family

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]

/-- The inverse-mass pairing of a whole family with a common translation of its test. -/
def cutoffFamilyPair (π : ι → ℝ) (g φ : ∀ v, Vec 2 → h v) (x : Vec 2) : ℝ :=
  ∑ v, (π v)⁻¹ * cutoffComponentPair (g v) (φ v) x

theorem cutoffFamilyPair_contDiff (π : ι → ℝ) (g φ : ∀ v, Vec 2 → h v)
    (hg : ∀ v, MemLp (g v) 2 volume)
    (hφ : ∀ v, ContDiff ℝ (⊤ : ℕ∞) (φ v) ∧ HasCompactSupport (φ v)) :
    ContDiff ℝ (⊤ : ℕ∞) (cutoffFamilyPair π g φ) := by
  exact ContDiff.sum (fun v _ => contDiff_const.mul
    (cutoffComponentPair_contDiff (g v) (φ v) (hg v) (hφ v).1 (hφ v).2))

theorem cutoffFamilyPair_orderedDerivative (π : ι → ℝ) (g φ : ∀ v, Vec 2 → h v)
    (hg : ∀ v, MemLp (g v) 2 volume)
    (hφ : ∀ v, ContDiff ℝ (⊤ : ℕ∞) (φ v) ∧ HasCompactSupport (φ v))
    {a : ℕ} (w : DerivativeWord2 a) :
    orderedDerivative w (cutoffFamilyPair π g φ) =
      cutoffFamilyPair π g (fun v => orderedDerivative w (φ v)) := by
  let F := fun x : Vec 2 => fun v : ι => cutoffComponentPair (g v) (φ v) x
  let L : (ι → ℝ) →L[ℝ] ℝ := ∑ v, (π v)⁻¹ • ContinuousLinearMap.proj v
  have hF : ContDiff ℝ (a : ℕ∞) F := contDiff_pi.mpr fun v =>
    (cutoffComponentPair_contDiff (g v) (φ v) (hg v) (hφ v).1 (hφ v).2).of_le (by simp)
  have he : cutoffFamilyPair π g φ = fun x => L (F x) := by
    funext x
    simp only [cutoffFamilyPair, L, F, sum_apply, smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [he, orderedDerivative_clm_comp L w hF]
  funext x
  simp only [L, sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    cutoffFamilyPair]
  apply Finset.sum_congr rfl
  intro v _
  congr 1
  have hp := orderedDerivative_clm_comp (ContinuousLinearMap.proj v) w hF
  have hv := cutoffComponentPair_orderedDerivative (g v) (φ v) (hg v) (hφ v).1 (hφ v).2 w
  exact (congrFun hp x).symm.trans (congrFun hv x)

/-- Derivatives commute with translations of compact tests. -/
theorem cutoff_orderedDerivative_translate {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {a : ℕ} (w : DerivativeWord2 a) (φ : Vec 2 → F)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (y : Vec 2) :
    orderedDerivative w (fun z => φ (z + y)) = fun z => orderedDerivative w φ (z + y) := by
  have hshift : ContDiff ℝ (a : ℕ∞) (fun z => φ (z + y)) := by
    exact (hφ.comp (contDiff_id.add contDiff_const)).of_le (by simp)
  rw [orderedDerivative_eq_iteratedFDeriv w hshift,
    orderedDerivative_eq_iteratedFDeriv w (hφ.of_le (by simp))]
  funext z
  rw [iteratedFDeriv_comp_add_right]

/-- The translated derivative tests give a pointwise bound using the old negative norm. -/
theorem cutoff_derivative_pair_le (π : ι → ℝ) (p N k : ℕ) (s R : ℝ) (hR : 1 ≤ R)
    (g φ : ∀ v, Vec 2 → h v)
    (hφ : ∀ v, ContDiff ℝ (⊤ : ℕ∞) (φ v) ∧ HasCompactSupport (φ v))
    (hb : weightedJetNorm π (-(p : ℝ)) (N + k) s R
      (fun v _ w z => orderedDerivative w (φ v) z) ≤ 1)
    (β : DerivativeWord2 N) (x : Vec 2) :
    ENNReal.ofReal |cutoffFamilyPair π g (fun v => orderedDerivative β (φ v)) x| ≤
      ENNReal.ofReal ((2 * cutoffBracket s x) ^ p *
        (((k + 1 : ℕ) : ℝ) * ((N + k).factorial : ℝ) * R⁻¹ ^ N)) *
          Assembly.negJetNorm π p k s 1 g := by
  let ψ := fun v => orderedDerivative β (φ v)
  have hψ (v : ι) : ContDiff ℝ (⊤ : ℕ∞) (ψ v) ∧ HasCompactSupport (ψ v) :=
    ⟨AVRegularity.orderedDerivative_contDiff β (hφ v).1,
      orderedDerivative_hasCompactSupport (hφ v).2 β⟩
  let χ := fun v z => ψ v (z + x)
  have hχ (v : ι) : ContDiff ℝ (⊤ : ℕ∞) (χ v) ∧ HasCompactSupport (χ v) :=
    ⟨(hψ v).1.comp (contDiff_id.add contDiff_const),
      (hψ v).2.comp_homeomorph (Homeomorph.addRight x)⟩
  let A : ℝ := ((k + 1 : ℕ) : ℝ) * ((N + k).factorial : ℝ) * R⁻¹ ^ N
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hfact : 0 < ((N + k).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (N + k)
  have hA : 0 < A := by dsimp only [A]; positivity
  have hx : 0 < 2 * cutoffBracket s x := by linarith only [cutoffBracket_one_le s x]
  have hbase : weightedJetNorm π (-(p : ℝ)) k s 1
      (fun v _ w z => orderedDerivative w (ψ v) z) ≤ ENNReal.ofReal A := by
    exact (cutoff_derivative_test_largeScale_le π (-(p : ℝ)) s R hR N k β φ
      (fun v => (hφ v).1)).trans (by simpa only [mul_one] using mul_le_mul' le_rfl hb)
  have hshift : weightedJetNorm π (-(p : ℝ)) k s 1
      (fun v _ w z => orderedDerivative w (χ v) z) ≤
      ENNReal.ofReal ((2 * cutoffBracket s x) ^ p * A) := by
    have hd (v : ι) (a : ℕ) (w : DerivativeWord2 a) :
        orderedDerivative w (χ v) = fun z => orderedDerivative w (ψ v) (z + x) :=
      cutoff_orderedDerivative_translate w (ψ v) (hψ v).1 x
    simp_rw [hd]
    have hh := cutoff_weightedJetNorm_translation_le π p k s 1 x
      (fun v _ w z => orderedDerivative w (ψ v) z)
      (fun v a w => Assembly.orderedDerivative_continuous w ((hψ v).1.of_le (by simp)))
    exact hh.trans ((mul_le_mul' le_rfl hbase).trans_eq
      (ENNReal.ofReal_mul (pow_nonneg hx.le p)).symm)
  have hh := cutoff_compact_test_pair_le π p k s 1 g χ hχ
    ((2 * cutoffBracket s x) ^ p * A) (mul_pos (pow_pos hx _) hA) hshift
  simpa only [cutoffFamilyPair, cutoffComponentPair_eq_integral] using hh

end Family

section ComplementFamily

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [∀ i, CompleteSpace (h i)]

theorem cutoffFamilyPair_complement_eq (m : Vec 2 → ℝ) (R : ℝ)
    (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0)
    (hs : ContDiff ℝ (⊤ : ℕ∞) m) (π : ι → ℝ) (g φ : ∀ v, Vec 2 → h v)
    (hg : ∀ v, MemLp (g v) 2 volume)
    (hφ : ∀ v, ContDiff ℝ (⊤ : ℕ∞) (φ v) ∧ HasCompactSupport (φ v)) :
    (∑ v, (π v)⁻¹ * ∫ z, inner ℝ (g v z - fourierCutoff m (g v) z) (φ v z)) =
      cutoffFamilyPair π g φ 0 - ∫ y, cutoffKernel m y * cutoffFamilyPair π g φ y := by
  have hp (v : ι) : MemLp (φ v) 2 volume :=
    (hφ v).1.continuous.memLp_of_hasCompactSupport (hφ v).2
  have hi (v : ι) : Integrable (fun y => cutoffKernel m y * cutoffComponentPair (g v) (φ v) y) := by
    apply (seamCutoffKernel_integrable m R hm hs).mul_bdd
    · exact (cutoffComponentPair_contDiff (g v) (φ v) (hg v) (hφ v).1 (hφ v).2).continuous.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun y => by
        simpa only [Real.norm_eq_abs] using cutoffComponentPair_abs_le (g v) (φ v) (hg v) (hp v) y
  simp_rw [cutoffComponentPair_complement_eq m R hm hs _ _ (hg _) (hp _)]
  rw [show (∑ v, (π v)⁻¹ * (cutoffComponentPair (g v) (φ v) 0 -
      ∫ y, cutoffKernel m y * cutoffComponentPair (g v) (φ v) y)) =
    cutoffFamilyPair π g φ 0 - ∑ v, (π v)⁻¹ *
      ∫ y, cutoffKernel m y * cutoffComponentPair (g v) (φ v) y by
        simp only [mul_sub, Finset.sum_sub_distrib, cutoffFamilyPair]]
  congr 1
  simp_rw [cutoffFamilyPair, Finset.mul_sum, mul_left_comm (cutoffKernel m _)]
  rw [integral_finsetSum]
  · simp only [integral_const_mul]
  · intro v _
    exact (hi v).const_mul _

end ComplementFamily

end AVRegularity.CycleWords.Seam
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal Convolution
namespace AVRegularity.CycleWords.Seam.NegLowBand

/-! # convolutions with smooth compactly supported kernels
`conv κ f = κ ⋆ f`; its ordered derivatives are the convolutions with the ordered derivatives of
`κ`, and the weighted `L²` norm of the result is bounded by the weighted `L¹` norm of the kernel
times the weighted `L²` norm of `f` (Young and Peetre).
-/

open AVRegularity.CycleWords.Seam.YoungKernel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `(κ ⋆ f)(y) = ∫ κ(t) f(y - t) dt`. -/
def conv (κ : Vec 2 → ℝ) (f : Vec 2 → E) : Vec 2 → E := fun y => ∫ t, κ t • f (y - t)

theorem conv_contDiff [CompleteSpace E] {κ : Vec 2 → ℝ} (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (hc : HasCompactSupport κ) {f : Vec 2 → E} (hf : LocallyIntegrable f volume) :
    ContDiff ℝ (⊤ : ℕ∞) (conv κ f) :=
  hc.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hκ hf

theorem conv_fderiv [CompleteSpace E] {κ : Vec 2 → ℝ} (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (hc : HasCompactSupport κ) {f : Vec 2 → E} (hf : LocallyIntegrable f volume) (x y : Vec 2) :
    fderiv ℝ (conv κ f) x y = conv (fun z => fderiv ℝ κ z y) f x := by
  have hd := hc.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (hκ.of_le (by simp)) hf x
  change fderiv ℝ (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x y = _
  rw [hd.fderiv]
  have hi := (hc.fderiv ℝ).convolutionExists_left
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Vec 2))
    (hκ.continuous_fderiv (by simp)) hf x
  change (∫ z : Vec 2, ((ContinuousLinearMap.lsmul ℝ ℝ).precompL (Vec 2))
    (fderiv ℝ κ z) (f (x - z))) y = _
  rw [ContinuousLinearMap.integral_apply hi]
  rfl

theorem conv_orderedDerivative [CompleteSpace E] {κ : Vec 2 → ℝ} (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (hc : HasCompactSupport κ) {f : Vec 2 → E} (hf : LocallyIntegrable f volume)
    {a : ℕ} (w : DerivativeWord2 a) :
    orderedDerivative w (conv κ f) = conv (orderedDerivative w κ) f := by
  induction a with
  | zero => simp only [orderedDerivative_zero]
  | succ a ih =>
    rw [orderedDerivative_succ, orderedDerivative_succ, ih]
    funext x
    exact conv_fderiv (AVRegularity.orderedDerivative_contDiff (fun i => w i.castSucc) hκ)
      (orderedDerivative_hasCompactSupport hc _) hf x _

theorem wbase_continuous (s : ℝ) : Continuous (wbase s) := by
  unfold wbase
  fun_prop

/-- The pointwise weighted bound for a convolution (Peetre). -/
theorem conv_weighted_pointwise (κ : Vec 2 → ℝ) (f : Vec 2 → E) (n : ℕ) (ϖ : ℝ) (y : Vec 2) :
    ENNReal.ofReal (wbase ϖ y ^ (-(n : ℝ) / 2) * ‖conv κ f y‖) ≤
      ∫⁻ t, ENNReal.ofReal ((2 * wbase ϖ t) ^ ((n : ℝ) / 2) * ‖κ t‖) *
        ENNReal.ofReal (wbase ϖ (y - t) ^ (-(n : ℝ) / 2) * ‖f (y - t)‖) := by
  have hq : (0 : ℝ) ≤ (n : ℝ) / 2 := by positivity
  have hneg : -(n : ℝ) / 2 = -((n : ℝ) / 2) := by ring
  have hc0 : 0 ≤ wbase ϖ y ^ (-(n : ℝ) / 2) := Real.rpow_nonneg (wbase_pos ϖ y).le _
  calc ENNReal.ofReal (wbase ϖ y ^ (-(n : ℝ) / 2) * ‖conv κ f y‖)
      = ENNReal.ofReal (wbase ϖ y ^ (-(n : ℝ) / 2)) * ‖conv κ f y‖ₑ := by
        rw [ENNReal.ofReal_mul hc0, ofReal_norm]
    _ ≤ ENNReal.ofReal (wbase ϖ y ^ (-(n : ℝ) / 2)) * ∫⁻ t, ‖κ t • f (y - t)‖ₑ :=
        mul_le_mul_right (enorm_integral_le_lintegral_enorm _) _
    _ = ∫⁻ t, ENNReal.ofReal (wbase ϖ y ^ (-(n : ℝ) / 2)) * ‖κ t • f (y - t)‖ₑ :=
        (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ ≤ _ := by
        refine lintegral_mono fun t => ?_
        have hu := wbase_pos ϖ (y - t)
        have hv := wbase_pos ϖ t
        have hx := wbase_pos ϖ y
        have hP := peetre_real hx hu hv (wbase_sub_le ϖ y t) hq
        rw [hneg] at hc0 ⊢
        rw [← ENNReal.ofReal_mul (by positivity), ← ofReal_norm, norm_smul,
          ← ENNReal.ofReal_mul hc0]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : 0 ≤ ‖κ t‖ := norm_nonneg _
        have h2 : 0 ≤ ‖f (y - t)‖ := norm_nonneg _
        calc wbase ϖ y ^ (-((n : ℝ) / 2)) * (‖κ t‖ * ‖f (y - t)‖)
            ≤ ((2 * wbase ϖ t) ^ ((n : ℝ) / 2) * wbase ϖ (y - t) ^ (-((n : ℝ) / 2))) *
              (‖κ t‖ * ‖f (y - t)‖) := mul_le_mul_of_nonneg_right hP (by positivity)
          _ = _ := by ring

theorem conv_weighted_sq_le [MeasurableSpace E] [BorelSpace E] {κ : Vec 2 → ℝ} {f : Vec 2 → E}
    (hκ : Measurable κ) (hf : Measurable f) (n : ℕ) {ϖ : ℝ}
    (hfin : ∫⁻ t, ENNReal.ofReal ((2 * wbase ϖ t) ^ ((n : ℝ) / 2) * ‖κ t‖) ≠ ⊤) :
    ∫⁻ y, ENNReal.ofReal (wbase ϖ y ^ (-(n : ℝ) / 2) * ‖conv κ f y‖) ^ 2 ≤
      (∫⁻ t, ENNReal.ofReal ((2 * wbase ϖ t) ^ ((n : ℝ) / 2) * ‖κ t‖)) ^ 2 *
        ∫⁻ y, ENNReal.ofReal (wbase ϖ y ^ (-(n : ℝ) / 2) * ‖f y‖) ^ 2 := by
  have hwb : Measurable (wbase ϖ) := (wbase_continuous ϖ).measurable
  have ha : Measurable fun t => ENNReal.ofReal ((2 * wbase ϖ t) ^ ((n : ℝ) / 2) * ‖κ t‖) :=
    ENNReal.measurable_ofReal.comp
      (((measurable_const.mul hwb).pow_const _).mul hκ.norm)
  have hh : Measurable fun y => ENNReal.ofReal (wbase ϖ y ^ (-(n : ℝ) / 2) * ‖f y‖) :=
    ENNReal.measurable_ofReal.comp ((hwb.pow_const _).mul hf.norm)
  refine le_trans (lintegral_mono fun y => pow_le_pow_left' (conv_weighted_pointwise κ f n ϖ y) 2) ?_
  exact young2 ha hh hfin

theorem eLpNorm_two_sq''' {α F : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup F] (f : α → F) (hf : AEStronglyMeasurable f μ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ z, ‖f z‖ₑ ^ 2 ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  simp only [ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- One derivative order of the weighted jet norm of a convolution. -/
theorem jet_component_le [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {κ : Vec 2 → ℝ} (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hc : HasCompactSupport κ)
    {f : Vec 2 → E} (hf : Measurable f) (hfl : LocallyIntegrable f volume)
    (n a : ℕ) {ϖ A : ℝ}
    (hA : ∀ w : DerivativeWord2 a, ∫⁻ t, ENNReal.ofReal ((2 * wbase ϖ t) ^ ((n : ℝ) / 2) *
        ‖orderedDerivative w κ t‖) ≤ ENNReal.ofReal A) :
    eLpNorm (fun z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((-(n : ℝ)) / 2) *
        Real.sqrt (∑ w : DerivativeWord2 a, ‖orderedDerivative w (conv κ f) z‖ ^ 2)) 2 volume ≤
      ENNReal.ofReal ((2 : ℝ) ^ a * A) * eLpNorm (fun z => wbase ϖ z ^ (-(n : ℝ) / 2) * ‖f z‖) 2
        volume := by
  have hT := conv_contDiff hκ hc hfl
  have hDc (w : DerivativeWord2 a) : Continuous (orderedDerivative w (conv κ f)) :=
    (AVRegularity.orderedDerivative_contDiff w hT).continuous
  set g : DerivativeWord2 a → Vec 2 → ℝ := fun w z =>
    wbase ϖ z ^ (-(n : ℝ) / 2) * ‖orderedDerivative w (conv κ f) z‖ with hg
  have hgc (w : DerivativeWord2 a) : Continuous (g w) := by
    refine Continuous.mul ?_ (hDc w).norm
    exact Continuous.rpow_const (wbase_continuous ϖ) fun z => Or.inl (wbase_pos ϖ z).ne'
  have hper (w : DerivativeWord2 a) :
      eLpNorm (g w) 2 volume ≤ ENNReal.ofReal A *
        eLpNorm (fun z => wbase ϖ z ^ (-(n : ℝ) / 2) * ‖f z‖) 2 volume := by
    have hκw : ContDiff ℝ (⊤ : ℕ∞) (orderedDerivative w κ) :=
      AVRegularity.orderedDerivative_contDiff w hκ
    have hfin : ∫⁻ t, ENNReal.ofReal ((2 * wbase ϖ t) ^ ((n : ℝ) / 2) *
        ‖orderedDerivative w κ t‖) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hA w)
    have hsq := conv_weighted_sq_le hκw.continuous.measurable hf n hfin
    rw [← conv_orderedDerivative hκ hc hfl w] at hsq
    have hF : AEStronglyMeasurable (fun z => wbase ϖ z ^ (-(n : ℝ) / 2) * ‖f z‖) volume := by
      refine (Measurable.aestronglyMeasurable ?_)
      exact ((wbase_continuous ϖ).measurable.pow_const _).mul hf.norm
    rw [← ENNReal.pow_le_pow_left_iff (n := 2) (by norm_num), mul_pow,
      eLpNorm_two_sq''' _ (hgc w).aestronglyMeasurable, eLpNorm_two_sq''' _ hF]
    have e1 : ∀ z, ‖g w z‖ₑ = ENNReal.ofReal (g w z) := fun z =>
      Real.enorm_of_nonneg (mul_nonneg (Real.rpow_nonneg (wbase_pos ϖ z).le _) (norm_nonneg _))
    have e2 : ∀ z, ‖wbase ϖ z ^ (-(n : ℝ) / 2) * ‖f z‖‖ₑ =
        ENNReal.ofReal (wbase ϖ z ^ (-(n : ℝ) / 2) * ‖f z‖) := fun z =>
      Real.enorm_of_nonneg (mul_nonneg (Real.rpow_nonneg (wbase_pos ϖ z).le _) (norm_nonneg _))
    simp only [e1, e2]
    refine hsq.trans ?_
    exact mul_le_mul' (pow_le_pow_left' (hA w) 2) le_rfl
  have hpt : ∀ z, ‖wbase ϖ z ^ (-(n : ℝ) / 2) *
        Real.sqrt (∑ w : DerivativeWord2 a, ‖orderedDerivative w (conv κ f) z‖ ^ 2)‖ ≤
      ‖(∑ w : DerivativeWord2 a, g w) z‖ := by
    intro z
    have hw0 : 0 ≤ wbase ϖ z ^ (-(n : ℝ) / 2) := Real.rpow_nonneg (wbase_pos ϖ z).le _
    have hsum : Real.sqrt (∑ w : DerivativeWord2 a, ‖orderedDerivative w (conv κ f) z‖ ^ 2) ≤
        ∑ w : DerivativeWord2 a, ‖orderedDerivative w (conv κ f) z‖ := by
      refine Real.sqrt_le_iff.2 ⟨Finset.sum_nonneg fun _ _ => norm_nonneg _, ?_⟩
      exact Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => norm_nonneg _
    rw [Finset.sum_apply, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg hw0 (Real.sqrt_nonneg _)), abs_of_nonneg
      (Finset.sum_nonneg fun w _ => mul_nonneg hw0 (norm_nonneg _))]
    simp only [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hsum hw0
  have hlc : Continuous fun z : Vec 2 => wbase ϖ z ^ (-(n : ℝ) / 2) *
      Real.sqrt (∑ w : DerivativeWord2 a, ‖orderedDerivative w (conv κ f) z‖ ^ 2) := by
    refine Continuous.mul ?_ (Real.continuous_sqrt.comp ?_)
    · exact Continuous.rpow_const (wbase_continuous ϖ) fun z => Or.inl (wbase_pos ϖ z).ne'
    · exact continuous_finsetSum _ fun w _ => (hDc w).norm.pow 2
  calc _ ≤ eLpNorm (∑ w : DerivativeWord2 a, g w) 2 volume :=
        eLpNorm_mono hlc.aestronglyMeasurable hpt
    _ ≤ ∑ w : DerivativeWord2 a, eLpNorm (g w) 2 volume :=
        eLpNorm_sum_le (by norm_num)
    _ ≤ ∑ w : DerivativeWord2 a, ENNReal.ofReal A *
        eLpNorm (fun z => wbase ϖ z ^ (-(n : ℝ) / 2) * ‖f z‖) 2 volume :=
        Finset.sum_le_sum fun w _ => hper w
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc]
        congr 1
        have hcard : Fintype.card (DerivativeWord2 a) = 2 ^ a := by
          simp [DerivativeWord2]
        rw [hcard, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
        simp

end AVRegularity.CycleWords.Seam.NegLowBand
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam.NegLowBand

/-! # the convolution with an even kernel is self-adjoint
`∫ ⟨f, κ ⋆ G⟩ = ∫ ⟨κ ⋆ f, G⟩` for `f, G ∈ L²` and a continuous, compactly supported, even
kernel `κ` (Fubini on the plane, the pairing integrand is integrable by Young and
Cauchy-Schwarz).
-/

open AVRegularity.CycleWords.Seam.YoungKernel

theorem enorm_inner_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a b : E) : ‖inner ℝ a b‖ₑ ≤ ‖a‖ₑ * ‖b‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm a, ← ofReal_norm b,
    ← ENNReal.ofReal_mul (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (by simpa using norm_inner_le_norm (𝕜 := ℝ) a b)

theorem lintegral_sq_ne_top {E : Type*} [NormedAddCommGroup E] {f : Vec 2 → E} (hf : MemLp f 2 volume) :
    ∫⁻ y, ‖f y‖ₑ ^ 2 ≠ ⊤ := by
  rw [← eLpNorm_two_sq''' f hf.aestronglyMeasurable]
  exact ENNReal.pow_ne_top hf.eLpNorm_lt_top.ne

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E]

/-- Convolution does not see the null sets of the function. -/
theorem conv_congr_ae {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] (κ : Vec 2 → ℝ)
    {g g' : Vec 2 → E'} (hg : g =ᵐ[volume] g') : conv κ g = conv κ g' := by
  funext y
  unfold conv
  apply integral_congr_ae
  have hs := (volume.measurePreserving_sub_left y).quasiMeasurePreserving.ae_eq_comp hg
  filter_upwards [hs] with z hz
  exact congrArg (fun v : E' => κ z • v) hz

/-- The pairing integrand on the plane squared. -/
def pairInt (κ : Vec 2 → ℝ) (f G : Vec 2 → E) (p : Vec 2 × Vec 2) : ℝ :=
  κ p.2 * inner ℝ (f p.1) (G (p.1 - p.2))

theorem lintegral_mul_le_two {φ ψ : Vec 2 → ℝ≥0∞} (hφ : Measurable φ) (hψ : Measurable ψ)
    (h1 : ∫⁻ y, φ y ^ 2 ≠ ⊤) (h2 : ∫⁻ y, ψ y ^ 2 ≠ ⊤) : ∫⁻ y, φ y * ψ y ≠ ⊤ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two
    hφ.aemeasurable hψ.aemeasurable
  refine ne_top_of_le_ne_top ?_ h
  refine ENNReal.mul_ne_top ?_ ?_
  · refine ENNReal.rpow_ne_top_of_nonneg (by norm_num) ?_
    simpa using h1
  · refine ENNReal.rpow_ne_top_of_nonneg (by norm_num) ?_
    simpa using h2

theorem pairInt_integrable {κ : Vec 2 → ℝ} (hκm : Measurable κ) (hκ : Integrable κ)
    {f G : Vec 2 → E} (hf : Measurable f) (hG : Measurable G) (hf2 : MemLp f 2 volume)
    (hG2 : MemLp G 2 volume) : Integrable (pairInt κ f G) (volume.prod volume) := by
  have hmeas : Measurable (pairInt κ f G) :=
    (hκm.comp measurable_snd).mul
      ((hf.comp measurable_fst).inner (hG.comp (measurable_fst.sub measurable_snd)))
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have h1 : ∫⁻ p, ‖pairInt κ f G p‖ₑ ∂(volume.prod volume) =
      ∫⁻ y, ∫⁻ t, ‖pairInt κ f G (y, t)‖ₑ := lintegral_prod _ hmeas.enorm.aemeasurable
  rw [h1]
  set a : Vec 2 → ℝ≥0∞ := fun t => ‖κ t‖ₑ with ha
  set g : Vec 2 → ℝ≥0∞ := fun y => ‖G y‖ₑ with hg
  set φ : Vec 2 → ℝ≥0∞ := fun y => ‖f y‖ₑ with hφ
  have ham : Measurable a := hκm.enorm
  have hgm : Measurable g := hG.enorm
  have hφm : Measurable φ := hf.enorm
  have hafin : ∫⁻ t, a t ≠ ⊤ := hκ.2.ne
  have hpt : ∀ y, ∫⁻ t, ‖pairInt κ f G (y, t)‖ₑ ≤ φ y * ∫⁻ t, a t * g (y - t) := by
    intro y
    rw [← lintegral_const_mul' _ _ ?_]
    · refine lintegral_mono fun t => ?_
      unfold pairInt
      simp only
      rw [enorm_mul]
      calc ‖κ t‖ₑ * ‖inner ℝ (f y) (G (y - t))‖ₑ ≤ ‖κ t‖ₑ * (‖f y‖ₑ * ‖G (y - t)‖ₑ) :=
            mul_le_mul' le_rfl (enorm_inner_le _ _)
        _ = _ := by simp only [ha, hg, hφ]; ring
    · simp only [hφ]; exact enorm_ne_top
  have hY : Measurable fun y => ∫⁻ t, a t * g (y - t) := by
    have : Measurable fun p : Vec 2 × Vec 2 => a p.2 * g (p.1 - p.2) :=
      (ham.comp measurable_snd).mul (hgm.comp (measurable_fst.sub measurable_snd))
    exact this.lintegral_prod_right'
  refine lt_of_le_of_lt (lintegral_mono hpt) ?_
  refine lt_top_iff_ne_top.2 (lintegral_mul_le_two hφm hY ?_ ?_)
  · exact lintegral_sq_ne_top hf2
  · refine ne_top_of_le_ne_top ?_ (young2 ham hgm hafin)
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top hafin) (lintegral_sq_ne_top hG2)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem conv_integrand_integrable {κ : Vec 2 → ℝ} (hκ2 : MemLp κ 2 volume)
    {G : Vec 2 → E} (hG2 : MemLp G 2 volume) (y : Vec 2) :
    Integrable (fun t => κ t • G (y - t)) volume := by
  have hGy : MemLp (fun t => G (y - t)) 2 volume :=
    hG2.comp_measurePreserving (volume.measurePreserving_sub_left y)
  have := MemLp.smul (p := 2) (q := 2) (r := 1) hκ2 hGy
  exact memLp_one_iff_integrable.1 this

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem conv_inner_eq_integral {κ : Vec 2 → ℝ} (hκ2 : MemLp κ 2 volume)
    [CompleteSpace E] {G : Vec 2 → E} (hG2 : MemLp G 2 volume) (f : Vec 2 → E) (y : Vec 2) :
    inner ℝ (f y) (conv κ G y) = ∫ t, pairInt κ f G (y, t) := by
  unfold conv
  rw [← integral_inner (conv_integrand_integrable hκ2 hG2 y)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [pairInt, inner_smul_right]

/-- The convolution with an even kernel is self-adjoint on `L²`. -/
theorem conv_self_adjoint {κ : Vec 2 → ℝ} (hκ : Continuous κ) (hc : HasCompactSupport κ)
    (hev : ∀ t, κ (-t) = κ t) [CompleteSpace E] {f G : Vec 2 → E} (hf : Measurable f)
    (hG : Measurable G) (hf2 : MemLp f 2 volume) (hG2 : MemLp G 2 volume) :
    ∫ y, inner ℝ (f y) (conv κ G y) = ∫ z, inner ℝ (conv κ f z) (G z) := by
  have hκ1 : Integrable κ := hκ.integrable_of_hasCompactSupport hc
  have h1 := pairInt_integrable hκ.measurable hκ1 hf hG hf2 hG2
  have h2 := pairInt_integrable hκ.measurable hκ1 hG hf hG2 hf2
  set c : Vec 2 → ℝ := fun t => ∫ y, inner ℝ (f y) (G (y - t)) with hcdef
  have hL : ∫ y, inner ℝ (f y) (conv κ G y) = ∫ t, κ t * c t := by
    simp_rw [conv_inner_eq_integral (hκ.memLp_of_hasCompactSupport hc) hG2]
    rw [← integral_prod (pairInt κ f G) h1, integral_prod_symm _ h1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [pairInt, hcdef]
    rw [integral_const_mul]
  have hR : ∫ z, inner ℝ (conv κ f z) (G z) = ∫ t, κ t * c (-t) := by
    have e1 : ∀ z, inner ℝ (conv κ f z) (G z) = inner ℝ (G z) (conv κ f z) :=
      fun z => real_inner_comm _ _
    simp_rw [e1, conv_inner_eq_integral (hκ.memLp_of_hasCompactSupport hc) hf2]
    rw [← integral_prod (pairInt κ G f) h2, integral_prod_symm _ h2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [pairInt, hcdef]
    rw [integral_const_mul]
    congr 1
    have := integral_add_right_eq_self (μ := volume)
      (fun z : Vec 2 => inner ℝ (G z) (f (z - t))) t
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [add_sub_cancel_right, sub_neg_eq_add]
    exact real_inner_comm _ _
  rw [hL, hR]
  have := integral_neg_eq_self (fun t => κ t * c t) volume
  rw [← this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [hev]

end AVRegularity.CycleWords.Seam.NegLowBand
end
