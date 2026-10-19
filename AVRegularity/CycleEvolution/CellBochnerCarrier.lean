-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.ScalarEnergyDecay
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.MeasureTheory.Measure.SeparableMeasure

section
@[expose] public noncomputable section
open MeasureTheory Set Filter Topology
namespace AVRegularity.CycleEvolution

/-! Forced integrating-factor energy bounds with retained nonnegative dissipation. -/

/-- The actual scalar derivative of an absolutely continuous energy is interval integrable. -/
theorem StrongTimeRegularity.scalar_derivative_intervalIntegrable {a b : ℝ} {E P : ℝ → ℝ}
    (h : StrongTimeRegularity a b E P) : IntervalIntegrable P volume a b := by
  apply h.ac.intervalIntegrable_deriv.congr_ae
  have hd := h.derivative.filter_mono (ae_mono (Measure.restrict_mono uIoc_subset_uIcc le_rfl))
  filter_upwards [hd] with t ht
  exact ht.deriv

/-- The forced differential inequality integrates with the exact exponential weight. -/
theorem StrongTimeRegularity.scalar_weighted_bound {a b : ℝ} (hab : a ≤ b) {E P : ℝ → ℝ}
    (h : StrongTimeRegularity a b E P) (c : ℝ) (f d : ℝ → ℝ)
    (hf : IntervalIntegrable f volume a b) (hd : IntervalIntegrable d volume a b)
    (hg : ∀ᵐ t ∂volume.restrict (Icc a b), P t + c * E t + d t ≤ f t) :
    Real.exp (c * (b - a)) * E b + (∫ t in a..b, Real.exp (c * (t - a)) * d t) ≤
      E a + ∫ t in a..b, Real.exp (c * (t - a)) * f t := by
  let w := fun t : ℝ => Real.exp (c * (t - a))
  have hw : ContinuousOn w (uIcc a b) :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const))).continuousOn
  have hEc : ContinuousOn E (Icc a b) := by
    simpa only [uIcc_of_le hab] using h.ac.continuousOn
  have hEi : IntervalIntegrable (fun t => c * E t) volume a b :=
    (continuousOn_const.mul hEc).intervalIntegrable_of_Icc hab
  have hp := (h.scalar_derivative_intervalIntegrable.add hEi).continuousOn_mul hw
  have hfi := hf.continuousOn_mul hw
  have hdi := hd.continuousOn_mul hw
  have hR : IntervalIntegrable (fun t => w t * (f t - d t)) volume a b :=
    (hf.sub hd).continuousOn_mul hw
  have hm := intervalIntegral.integral_mono_ae_restrict hab hp hR (by
    filter_upwards [hg] with t ht
    exact mul_le_mul_of_nonneg_left (show P t + c * E t ≤ f t - d t by linarith)
      (Real.exp_pos _).le)
  have hs : (∫ t in a..b, w t * (f t - d t)) =
      (∫ t in a..b, w t * f t) - ∫ t in a..b, w t * d t := by
    have he : (fun t => w t * (f t - d t)) = (fun t => w t * f t) - (fun t => w t * d t) := by
      funext t
      simp only [Pi.sub_apply, mul_sub]
    rw [he]
    exact intervalIntegral.integral_sub hfi hdi
  rw [hs, ← h.scalar_weighted_increment c] at hm
  dsimp only [w] at hm
  linarith

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
namespace AVRegularity.CycleEvolution

/-! Restriction of strong variational time equations to subintervals. -/

variable {V H : Type*} [AddCommGroup V] [Module ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Strong variational solutions restrict without new analytic assumptions. -/
theorem StrongVariationalSolution.mono {a b c d : ℝ} {J : V →ₗ[ℝ] H}
    {B : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {q : ℝ → V →ₗ[ℝ] ℝ}
    {u du : ℝ → H} {slice : ℝ → V}
    (h : StrongVariationalSolution a b J B q u du slice)
    (hsub : uIcc c d ⊆ uIcc a b) : StrongVariationalSolution c d J B q u du slice :=
  ⟨h.time.mono hsub,
    h.agrees.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)),
    h.equation.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))⟩

end AVRegularity.CycleEvolution
end
end

section
@[expose] public section
namespace AVRegularity.CycleEvolution

/-! Turning squared energy bounds into the exact polynomial word-norm factors. -/

theorem word_homogeneous_norm_budget (R c q S δ A E U : ℝ)
    (hR : 0 < R) (hc : 0 ≤ c) (hq : 0 ≤ q) (hS : 1 ≤ S) (hδ : δ ≤ S) (hU : 0 ≤ U)
    (hA : A ≤ c * U)
    (hE : E ≤ (144 + 16 * c ^ 2 * (δ + 1) * (q / R) ^ 2 + 4 * c ^ 2 * δ * q ^ 2) * U ^ 2) :
    A + Real.sqrt E ≤ (c + 12 + c * Real.sqrt (32 / R ^ 2 + 4)) * (1 + Real.sqrt S * q) * U := by
  let x := Real.sqrt S * q
  let d := Real.sqrt (32 / R ^ 2 + 4)
  have hx : 0 ≤ x := mul_nonneg (Real.sqrt_nonneg _) hq
  have hd : 0 ≤ d := Real.sqrt_nonneg _
  have hbudget := word_homogeneous_cov_budget_le R c q S δ hR hc hq hS hδ
  have hs : E ≤ ((12 + c * d * x) * U) ^ 2 := by
    exact (hE.trans (mul_le_mul_of_nonneg_right hbudget (sq_nonneg U))).trans_eq (by dsimp only [x, d]; ring)
  have hroot : Real.sqrt E ≤ (12 + c * d * x) * U := by
    apply (Real.sqrt_le_sqrt hs).trans_eq
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  calc
    A + Real.sqrt E ≤ c * U + (12 + c * d * x) * U := add_le_add hA hroot
    _ = (c + 12 + c * d * x) * U := by ring
    _ ≤ (c + 12 + c * d) * (1 + x) * U := by
      apply mul_le_mul_of_nonneg_right _ hU
      nlinarith [mul_nonneg (by positivity : 0 ≤ c + 12) hx, mul_nonneg hc hd]
    _ = _ := rfl

theorem word_forced_norm_budget (R f C q S δ A E Q : ℝ)
    (hR : 0 < R) (hf : 0 ≤ f) (hC : 0 ≤ C) (hq : 0 ≤ q) (hS : 1 ≤ S) (hδ : δ ≤ S) (hQ : 0 ≤ Q)
    (hfbound : f ≤ C * (1 + Real.sqrt S * q)) (hA : A ≤ f * Real.sqrt Q)
    (hE : E ≤ (224 + 16 * (δ + 1) * (q / R) ^ 2 * f ^ 2 + 4 * q ^ 2 * δ * f ^ 2) * Q) :
    A + Real.sqrt E ≤ (15 + C + C * Real.sqrt (32 / R ^ 2 + 4)) * (1 + Real.sqrt S * q) ^ 2 * Real.sqrt Q := by
  let x := Real.sqrt S * q
  let d := Real.sqrt (32 / R ^ 2 + 4)
  let K := 15 + C * d * x * (1 + x)
  have hx : 0 ≤ x := mul_nonneg (Real.sqrt_nonneg _) hq
  have hd : 0 ≤ d := Real.sqrt_nonneg _
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hbudget := word_forced_cov_budget_le R f C q S δ hR hf hC hq hS hδ hfbound
  have hs : E ≤ K ^ 2 * Q := hE.trans (mul_le_mul_of_nonneg_right hbudget hQ)
  have hroot : Real.sqrt E ≤ K * Real.sqrt Q := by
    apply (Real.sqrt_le_sqrt hs).trans_eq
    rw [Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq_eq_abs, abs_of_nonneg hK]
  have hAmp : A ≤ C * (1 + x) * Real.sqrt Q :=
    hA.trans (mul_le_mul_of_nonneg_right hfbound (Real.sqrt_nonneg Q))
  have hp : C * (1 + x) + K ≤ (15 + C + C * d) * (1 + x) ^ 2 := by
    dsimp only [K]
    have h1 : 15 ≤ 15 * (1 + x) ^ 2 := by nlinarith
    have h2 : C * (1 + x) ≤ C * (1 + x) ^ 2 := by
      nlinarith [mul_nonneg hC hx, mul_nonneg hC (sq_nonneg x)]
    have h3 : C * d * x * (1 + x) ≤ C * d * (1 + x) ^ 2 := by
      have hm := mul_nonneg (mul_nonneg hC hd) (by linarith : 0 ≤ 1 + x)
      nlinarith
    nlinarith
  calc
    A + Real.sqrt E ≤ C * (1 + x) * Real.sqrt Q + K * Real.sqrt Q := add_le_add hAmp hroot
    _ = (C * (1 + x) + K) * Real.sqrt Q := by ring
    _ ≤ (15 + C + C * d) * (1 + x) ^ 2 * Real.sqrt Q := mul_le_mul_of_nonneg_right hp (Real.sqrt_nonneg Q)
    _ = _ := rfl

end AVRegularity.CycleEvolution
end
end

section
@[expose] public section
open scoped BigOperators
namespace AVRegularity.CycleEvolution

/-! The positive metric indices inherit Pascal's identity with the differentiated zeroth coefficient. -/

/-- Removing the zeroth coefficient splits the full convolution exactly. -/
theorem binomialConvolution_split_zero {M : Type*} [AddCommMonoid M]
    (u : ℕ × ℕ → ℕ × ℕ → M) (n m : ℕ) :
    (∑ β ∈ (Finset.Iic (n, m)).filter (fun β => β ≠ 0),
      (n.choose β.1 * m.choose β.2) • u β (n - β.1, m - β.2)) + u 0 (n, m) =
    ∑ β ∈ Finset.Iic (n, m), (n.choose β.1 * m.choose β.2) •
      u β (n - β.1, m - β.2) := by
  have hf : (Finset.Iic (n, m)).filter (fun β => β ≠ 0) =
      (Finset.Iic (n, m)).erase 0 := by
    ext β
    simp only [Finset.mem_filter, Finset.mem_erase]
    exact and_comm
  rw [hf]
  simpa only [Prod.fst_zero, Prod.snd_zero, Nat.choose_zero_right, one_mul,
    one_nsmul, Nat.sub_zero] using
    Finset.sum_erase_add (Finset.Iic (n, m))
      (fun β => (n.choose β.1 * m.choose β.2) • u β (n - β.1, m - β.2))
      (show (0 : ℕ × ℕ) ∈ Finset.Iic (n, m) from by
        apply Finset.mem_Iic.mpr
        change 0 ≤ n ∧ 0 ≤ m
        exact ⟨Nat.zero_le _, Nat.zero_le _⟩)

/-- The first derivative of the proper convolution, plus the zeroth metric derivative. -/
theorem binomialConvolution_proper_first {M : Type*} [AddCommGroup M]
    (u : ℕ × ℕ → ℕ × ℕ → M) (n m : ℕ) :
    (∑ β ∈ (Finset.Iic (n, m)).filter (fun β => β ≠ 0),
      (n.choose β.1 * m.choose β.2) •
        (u (β.1 + 1, β.2) (n - β.1, m - β.2) +
          u β (n - β.1 + 1, m - β.2))) + u (1, 0) (n, m) =
    ∑ β ∈ (Finset.Iic (n + 1, m)).filter (fun β => β ≠ 0),
      ((n + 1).choose β.1 * m.choose β.2) • u β (n + 1 - β.1, m - β.2) := by
  have hp := binomialConvolution_pair_first u n m
  rw [← Finset.sum_add_distrib] at hp
  simp only [← nsmul_add] at hp
  have hs := binomialConvolution_split_zero
    (fun β γ => u (β.1 + 1, β.2) γ + u β (γ.1 + 1, γ.2)) n m
  have ht := binomialConvolution_split_zero u (n + 1) m
  simp only [Prod.fst_zero, Prod.snd_zero, zero_add] at hs
  rw [← hs, ← ht] at hp
  apply add_right_cancel (b := u 0 (n + 1, m))
  calc
    _ = (∑ β ∈ (Finset.Iic (n, m)).filter (fun β => β ≠ 0),
      (n.choose β.1 * m.choose β.2) •
        (u (β.1 + 1, β.2) (n - β.1, m - β.2) +
          u β (n - β.1 + 1, m - β.2))) +
      (u (1, 0) (n, m) + u 0 (n + 1, m)) := by abel
    _ = _ := hp

/-- The second derivative of the proper convolution, plus the zeroth metric derivative. -/
theorem binomialConvolution_proper_second {M : Type*} [AddCommGroup M]
    (u : ℕ × ℕ → ℕ × ℕ → M) (n m : ℕ) :
    (∑ β ∈ (Finset.Iic (n, m)).filter (fun β => β ≠ 0),
      (n.choose β.1 * m.choose β.2) •
        (u (β.1, β.2 + 1) (n - β.1, m - β.2) +
          u β (n - β.1, m - β.2 + 1))) + u (0, 1) (n, m) =
    ∑ β ∈ (Finset.Iic (n, m + 1)).filter (fun β => β ≠ 0),
      (n.choose β.1 * (m + 1).choose β.2) • u β (n - β.1, m + 1 - β.2) := by
  have hp := binomialConvolution_pair_second u n m
  rw [← Finset.sum_add_distrib] at hp
  simp only [← nsmul_add] at hp
  have hs := binomialConvolution_split_zero
    (fun β γ => u (β.1, β.2 + 1) γ + u β (γ.1, γ.2 + 1)) n m
  have ht := binomialConvolution_split_zero u n (m + 1)
  simp only [Prod.fst_zero, Prod.snd_zero, zero_add] at hs
  rw [← hs, ← ht] at hp
  apply add_right_cancel (b := u 0 (n, m + 1))
  calc
    _ = (∑ β ∈ (Finset.Iic (n, m)).filter (fun β => β ≠ 0),
      (n.choose β.1 * m.choose β.2) •
        (u (β.1, β.2 + 1) (n - β.1, m - β.2) +
          u β (n - β.1, m - β.2 + 1))) +
      (u (0, 1) (n, m) + u 0 (n, m + 1)) := by abel
    _ = _ := hp

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Separable Hilbert carriers for weak Galerkin limits. -/

noncomputable instance cellH1_secondCountable : SecondCountableTopology (TorusHk 1 ℂ) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  infer_instance

/-- The temporal L² Hilbert space of periodic H¹ states. -/
abbrev CellBochnerH1 (a b : ℝ) := Lp (TorusHk 1 ℂ) 2 (volume.restrict (Icc a b))

noncomputable instance cellBochnerH1_secondCountable (a b : ℝ) :
    SecondCountableTopology (CellBochnerH1 a b) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  infer_instance

/-- A square budget gives a convenient real norm bound without introducing square roots. -/
theorem cellNorm_le_budget_add_one {x W : ℝ} (h : x ^ 2 ≤ W) : x ≤ W + 1 := by
  nlinarith [sq_nonneg (x - 1)]

end AVRegularity.CycleEvolution
end
end
