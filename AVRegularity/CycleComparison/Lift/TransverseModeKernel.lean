-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Mathlib.Analysis.CStarAlgebra.Classes
import AVenhance.Infra.Parabolic.WeakUniqueness.WeakAlgebra
public import AVenhance.Infra.Torus.FourierCalculus
import AVenhance.Infra.Parabolic.FourierGalerkin.TestDensityBridge
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Separation.CompletelyRegular

section
@[expose] public noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace AVRegularity.CycleComparison.Lift

/-! The difference-quotient argument for the measurability of spatial slice derivatives, in
normed real vector spaces.
Time is a measurable parameter; no continuity in time is required. -/

variable {T : Type*} [MeasurableSpace T]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem deriv_parameter_measurable (f : T → ℝ → E)
    (hm : ∀ x, Measurable (fun t => f t x)) (hd : ∀ t, Differentiable ℝ (f t)) (x : ℝ) :
    Measurable (fun t => deriv (f t) x) := by
  let a : ℕ → ℝ := fun n => 1 / ((n + 1 : ℕ) : ℝ)
  have ha_pos (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  have ha : Tendsto a atTop (𝓝 0) := by
    simpa only [Function.comp_def, a] using
      (tendsto_const_div_atTop_nhds_zero_nat 1).comp (tendsto_add_atTop_nat 1)
  have hane : Tendsto a atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨ha, ?_⟩
    filter_upwards with n
    simpa only [Function.comp_def, mem_compl_iff, mem_singleton_iff] using (ha_pos n).ne'
  apply measurable_of_tendsto_metrizable
    (f := fun n t => (a n)⁻¹ • (f t (x + a n) - f t x))
    (fun n => by
      simpa only [Pi.smul_apply, Pi.sub_apply] using!
        ((hm (x + a n)).sub (hm x)).const_smul ((a n)⁻¹)) 
  apply tendsto_pi_nhds.mpr
  intro t
  let g := fun r : ℝ => f t (x + r)
  have hg : HasDerivAt g (deriv (f t) x) 0 := by
    apply HasDerivAt.comp_const_add x 0
    simpa only [add_zero] using (hd t x).hasDerivAt
  have hh := hg.tendsto_slope_zero.comp hane
  apply hh.congr'
  filter_upwards with n
  simp only [Function.comp_def, g, zero_add, add_zero]

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! Bounded measurable parameter fields commute with subtraction under a finite measure integral. -/

variable {T E : Type*} [MeasurableSpace T] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem parameter_integral_sub_eq (μ : Measure T) [IsFiniteMeasure μ]
    (f g : T → Vec 2 → E) (hmf : ∀ X, Measurable (fun t => f t X))
    (hmg : ∀ X, Measurable (fun t => g t X))
    (Cf Cg : ℝ) (hbf : ∀ t X, ‖f t X‖ ≤ Cf) (hbg : ∀ t X, ‖g t X‖ ≤ Cg) :
    (fun X => ∫ t, (f t X - g t X) ∂μ) =
      (fun X => ∫ t, f t X ∂μ) - (fun X => ∫ t, g t X ∂μ) := by
  funext X
  exact integral_sub
    ((integrable_const Cf).mono' (hmf X).aestronglyMeasurable (ae_of_all μ (fun t => hbf t X)))
    ((integrable_const Cg).mono' (hmg X).aestronglyMeasurable (ae_of_all μ (fun t => hbg t X)))

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem parameter_difference_jet_bound (p r : ℕ) (hr : r ≤ p)
    (f g : Vec 2 → E) (hf : ContDiff ℝ (p : ℕ∞) f) (hg : ContDiff ℝ (p : ℕ∞) g)
    (Cf Cg : ℝ) (hbf : ∀ X, ‖iteratedFDeriv ℝ r f X‖ ≤ Cf)
    (hbg : ∀ X, ‖iteratedFDeriv ℝ r g X‖ ≤ Cg) (X : Vec 2) :
    ‖iteratedFDeriv ℝ r (f - g) X‖ ≤ Cf + Cg := by
  have hfr : ContDiff ℝ (r : ℕ∞) f := hf.of_le (by exact_mod_cast hr)
  have hgr : ContDiff ℝ (r : ℕ∞) g := hg.of_le (by exact_mod_cast hr)
  rw [iteratedFDeriv_sub_apply hfr.contDiffAt hgr.contDiffAt]
  exact (norm_sub_le _ _).trans (add_le_add (hbf X) (hbg X))

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open scoped Topology
namespace AVRegularity.CycleComparison.Lift

/-! Banach-valued centered periodic primitives, adapting the existing cycle-reference argument. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def centeredIntervalPrimitive (f : ℝ → E) (r : ℝ) : E :=
  (∫ y in (0 : ℝ)..r, f y) - ∫ s in (0 : ℝ)..1, ∫ y in (0 : ℝ)..s, f y

theorem centeredIntervalPrimitive_hasDerivAt (f : ℝ → E) (hf : Continuous f) (r : ℝ) :
    HasDerivAt (centeredIntervalPrimitive f) (f r) r := by
  exact (intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 r)
    (hf.stronglyMeasurableAtFilter volume (𝓝 r)) hf.continuousAt).sub_const _

theorem centeredIntervalPrimitive_mean_zero (f : ℝ → E) (hf : Continuous f) :
    (∫ r in (0 : ℝ)..1, centeredIntervalPrimitive f r) = 0 := by
  have hc : Continuous (fun r : ℝ => ∫ y in (0 : ℝ)..r, f y) :=
    continuous_iff_continuousAt.mpr (fun r => (intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 r)
      (hf.stronglyMeasurableAtFilter volume (𝓝 r)) hf.continuousAt).continuousAt)
  unfold centeredIntervalPrimitive
  rw [intervalIntegral.integral_sub (hc.intervalIntegrable 0 1) (intervalIntegrable_const),
    intervalIntegral.integral_const]
  simp only [sub_zero, one_smul, sub_self]

omit [CompleteSpace E] in
theorem centeredIntervalPrimitive_periodic (f : ℝ → E) (hf : Continuous f)
    (hp : Function.Periodic f 1) (hz : (∫ y in (0 : ℝ)..1, f y) = 0) :
    Function.Periodic (centeredIntervalPrimitive f) 1 := by
  intro r
  have hcycle : (∫ y in r..(r + 1), f y) = 0 := by
    rw [hp.intervalIntegral_add_eq r 0]
    simpa only [zero_add] using hz
  unfold centeredIntervalPrimitive
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable 0 r) (hf.intervalIntegrable r (r + 1)), hcycle, add_zero]

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! Component primitives reconstruct the finite coefficient vector primitive. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, CompleteSpace (h i)]

theorem pi_time_primitives (R : ℝ → ∀ i, h i) (u : ∀ i, h i) (a b : ℝ)
    (hp : ∀ i, IntervalIntegrable (fun s => R s i) volume a b ∧
      u i = ∫ s in a..b, R s i) :
    IntervalIntegrable R volume a b ∧ u = ∫ s in a..b, R s := by
  have hi : IntervalIntegrable R volume a b :=
    ⟨integrable_pi_iff.mpr (fun i => (hp i).1.1),
      integrable_pi_iff.mpr (fun i => (hp i).1.2)⟩
  refine ⟨hi, ?_⟩
  funext i
  rw [(hp i).2]
  exact (ContinuousLinearMap.proj (R := ℝ) (φ := h) i).intervalIntegral_comp_comm hi

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public section
namespace AVRegularity.CycleComparison.Lift

/-! Polynomial propagator factors are absorbed by half of the exponential damping. -/

theorem pow_mul_exp_neg_le_factorial (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    x ^ n * Real.exp (-x) ≤ n.factorial := by
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hh := (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp x hx n)
  calc
    x ^ n * Real.exp (-x) ≤ (Real.exp x * n.factorial) * Real.exp (-x) :=
      mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le
    _ = n.factorial := by
      rw [mul_right_comm, ← Real.exp_add]
      simp

theorem max_pow_mul_exp_double_neg_le (n : ℕ) (C x : ℝ)
    (hC : 0 ≤ C) (hx : 0 ≤ x) :
    (max 1 (C * x)) ^ n * Real.exp (-2 * x) ≤
      (1 + n.factorial * C ^ n) * Real.exp (-x) := by
  have hp : (max 1 (C * x)) ^ n ≤ 1 + (C * x) ^ n := by
    rcases le_total (C * x) 1 with hh | hh
    · rw [max_eq_left hh, one_pow]
      exact le_add_of_nonneg_right (pow_nonneg (mul_nonneg hC hx) n)
    · rw [max_eq_right hh]
      exact le_add_of_nonneg_left zero_le_one
  have he : Real.exp (-2 * x) = Real.exp (-x) * Real.exp (-x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ (1 + (C * x) ^ n) * Real.exp (-2 * x) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = Real.exp (-2 * x) +
        C ^ n * (x ^ n * Real.exp (-x)) * Real.exp (-x) := by rw [he, mul_pow]; ring
    _ ≤ Real.exp (-x) + C ^ n * n.factorial * Real.exp (-x) := by
      apply add_le_add
      · apply Real.exp_le_exp.mpr
        linarith
      · exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_mul_exp_neg_le_factorial n x hx)
            (pow_nonneg hC n)) (Real.exp_pos _).le
    _ = _ := by ring

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public section
open scoped BigOperators
namespace AVRegularity.CycleComparison.Lift

/-! A polynomial with zero constant coefficient is unchanged by padding positive degrees. -/

section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem polynomial_positive_padding (Q M : ℕ) (hQM : Q ≤ M) (ε : ℝ) (F : ℕ → E)
    (hzero : F 0 = 0) (hz : ∀ n, Q < n → F n = 0) :
    (∑ n ∈ Finset.range (Q + 1), ε ^ n • F n) =
      ∑ n ∈ Finset.Icc 1 M, ε ^ n • F n := by
  have hrange : Finset.range (Q + 1) = insert 0 (Finset.Icc 1 Q) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hrange, Finset.sum_insert (by simp), hzero, smul_zero, zero_add]
  apply Finset.sum_subset
  · intro n hn
    have := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr (by omega)
  · intro n hn hnnot
    have := Finset.mem_Icc.mp hn
    have hnot : ¬(1 ≤ n ∧ n ≤ Q) := by simpa only [Finset.mem_Icc] using hnnot
    rw [hz n (by omega), smul_zero]
end

/-! Rectangular finite products are reindexed by total parameter degree with their literal cutoff. -/

section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem polynomial_rectangular_convolution (N Q : ℕ) (ε : ℝ) (F : ℕ → ℕ → E) :
    (∑ r ∈ Finset.range (N + 1), ∑ l ∈ Finset.Icc 2 Q, ε ^ (r + l) • F r l) =
      ∑ n ∈ Finset.Icc 1 (N + Q), ε ^ n •
        (∑ r ∈ Finset.range (N + 1),
          if r ≤ n ∧ 2 ≤ n - r ∧ n - r ≤ Q then F r (n - r) else 0) := by
  classical
  let S := (Finset.range (N + 1)) ×ˢ (Finset.Icc 2 Q)
  have hmap (p : ℕ × ℕ) (hp : p ∈ S) : p.1 + p.2 ∈ Finset.Icc 1 (N + Q) := by
    obtain ⟨hr, hl⟩ := Finset.mem_product.mp hp
    have := Finset.mem_range.mp hr
    have := Finset.mem_Icc.mp hl
    exact Finset.mem_Icc.mpr (by omega)
  have hgroup := Finset.sum_fiberwise_of_maps_to hmap (fun p : ℕ × ℕ => ε ^ (p.1 + p.2) • F p.1 p.2)
  rw [← Finset.sum_product']
  change (∑ p ∈ S, ε ^ (p.1 + p.2) • F p.1 p.2) = _
  rw [← hgroup]
  apply Finset.sum_congr rfl
  intro n _
  have hfiber : (∑ p ∈ S.filter (fun p => p.1 + p.2 = n), ε ^ (p.1 + p.2) • F p.1 p.2) =
      ∑ r ∈ (Finset.range (N + 1)).filter
        (fun r => r ≤ n ∧ 2 ≤ n - r ∧ n - r ≤ Q), ε ^ n • F r (n - r) := by
    apply Finset.sum_bij (fun p _ => p.1)
    · intro p hp
      obtain ⟨hpS, hpn⟩ := Finset.mem_filter.mp hp
      obtain ⟨hr, hl⟩ := Finset.mem_product.mp hpS
      have := Finset.mem_Icc.mp hl
      exact Finset.mem_filter.mpr ⟨hr, by omega⟩
    · intro p hp q hq hpq
      have hpn := (Finset.mem_filter.mp hp).2
      have hqn := (Finset.mem_filter.mp hq).2
      apply Prod.ext hpq
      omega
    · intro r hr
      obtain ⟨hrange, hcond⟩ := Finset.mem_filter.mp hr
      refine ⟨(r, n - r), Finset.mem_filter.mpr ⟨?_, by omega⟩, rfl⟩
      exact Finset.mem_product.mpr ⟨hrange, Finset.mem_Icc.mpr hcond.2⟩
    · intro p hp
      have hpn := (Finset.mem_filter.mp hp).2
      have hp2 : p.2 = n - p.1 := by omega
      rw [hpn, hp2]
  rw [hfiber]
  rw [Finset.smul_sum]
  simp only [smul_ite, smul_zero]
  exact Finset.sum_filter _ _
end

/-! Multiplication by a fixed parameter power shifts the finite polynomial coefficients exactly. -/

section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem polynomial_shift_sum (N M δ : ℕ) (hδ : 1 ≤ δ) (hM : N + δ ≤ M)
    (ε : ℝ) (F : ℕ → E) (hz : ∀ n, N < n → F n = 0) :
    ε ^ δ • (∑ n ∈ Finset.range (N + 1), ε ^ n • F n) =
      ∑ n ∈ Finset.Icc 1 M, ε ^ n • (if δ ≤ n then F (n - δ) else 0) := by
  have hshift : (∑ n ∈ Finset.range (N + 1), ε ^ δ • (ε ^ n • F n)) =
      ∑ n ∈ Finset.Icc δ (N + δ), ε ^ n • F (n - δ) := by
    apply Finset.sum_bij (fun n _ => n + δ)
    · intro n hn
      have := Finset.mem_range.mp hn
      exact Finset.mem_Icc.mpr (by omega)
    · intro n hn m hm hnm
      omega
    · intro n hn
      have := Finset.mem_Icc.mp hn
      refine ⟨n - δ, Finset.mem_range.mpr (by omega), ?_⟩
      omega
    · intro n _
      simp only [Nat.add_sub_cancel, smul_smul, pow_add]
      rw [mul_comm]
  rw [Finset.smul_sum, hshift]
  have hsub : Finset.Icc δ (N + δ) ⊆ Finset.Icc 1 M := by
    intro n hn
    have := Finset.mem_Icc.mp hn
    exact Finset.mem_Icc.mpr (by omega)
  calc
    (∑ n ∈ Finset.Icc δ (N + δ), ε ^ n • F (n - δ)) =
        ∑ n ∈ Finset.Icc δ (N + δ), ε ^ n • (if δ ≤ n then F (n - δ) else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [ite_eq_left (Finset.mem_Icc.mp hn).1]
    _ = _ := Finset.sum_subset hsub (by
      intro n hn hnnot
      have hn' := Finset.mem_Icc.mp hn
      by_cases hdn : δ ≤ n
      · have hlarge : N < n - δ := by
          have hnot : ¬(δ ≤ n ∧ n ≤ N + δ) := by simpa only [Finset.mem_Icc] using hnnot
          omega
        rw [ite_eq_left hdn, hz (n - δ) hlarge, smul_zero]
      · rw [ite_eq_right hdn, smul_zero])
end

/-! The explicit high-degree tail cancels exactly the high-degree polynomial coefficients. -/

section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem polynomial_tail_cancellation (N M : ℕ) (hNM : N ≤ M)
    (w : ℕ → ℝ) (A B : ℕ → E) :
    -(∑ n ∈ Finset.Icc 1 N, w n • A n) + (∑ n ∈ Finset.Icc 1 N, w n • B n) =
      -(∑ n ∈ Finset.Icc 1 M, w n • A n) + (∑ n ∈ Finset.Icc 1 M, w n • B n) +
        ∑ n ∈ Finset.Icc (N + 1) M, w n • (A n - B n) := by
  have hu : Finset.Icc 1 N ∪ Finset.Icc (N + 1) M = Finset.Icc 1 M := by
    ext n
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hd : Disjoint (Finset.Icc 1 N) (Finset.Icc (N + 1) M) := by
    apply Finset.disjoint_left.mpr
    intro n hn hn'
    have := Finset.mem_Icc.mp hn
    have := Finset.mem_Icc.mp hn'
    omega
  have hsplit (F : ℕ → E) : (∑ n ∈ Finset.Icc 1 M, w n • F n) =
      (∑ n ∈ Finset.Icc 1 N, w n • F n) + (∑ n ∈ Finset.Icc (N + 1) M, w n • F n) := by
    rw [← hu, Finset.sum_union hd]
  simp only [smul_sub, Finset.sum_sub_distrib]
  rw [hsplit A, hsplit B]
  abel
end

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace AVRegularity.CycleComparison.Lift

/-! The difference-quotient argument for the measurability of spatial slice derivatives, for
scalar transverse profiles.
Time is a measurable parameter; no continuity in time is required. -/

variable {T : Type*} [MeasurableSpace T]

theorem profile_deriv_parameter_measurable (f : T → ℝ → ℂ)
    (hm : ∀ x, Measurable (fun t => f t x)) (hd : ∀ t, Differentiable ℝ (f t)) (x : ℝ) :
    Measurable (fun t => deriv (f t) x) := by
  let a : ℕ → ℝ := fun n => 1 / ((n + 1 : ℕ) : ℝ)
  have ha_pos (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  have ha : Tendsto a atTop (𝓝 0) := by
    simpa only [Function.comp_def, a] using
      (tendsto_const_div_atTop_nhds_zero_nat 1).comp (tendsto_add_atTop_nat 1)
  have hane : Tendsto a atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨ha, ?_⟩
    filter_upwards with n
    simpa only [Function.comp_def, mem_compl_iff, mem_singleton_iff] using (ha_pos n).ne'
  apply measurable_of_tendsto_metrizable
    (f := fun n t => (a n)⁻¹ • (f t (x + a n) - f t x))
    (fun n => by
      simpa only [Pi.smul_apply, Pi.sub_apply] using!
        ((hm (x + a n)).sub (hm x)).const_smul ((a n)⁻¹)) 
  apply tendsto_pi_nhds.mpr
  intro t
  let g := fun r : ℝ => f t (x + r)
  have hg : HasDerivAt g (deriv (f t) x) 0 := by
    apply HasDerivAt.comp_const_add x 0
    simpa only [add_zero] using (hd t x).hasDerivAt
  have hh := hg.tendsto_slope_zero.comp hane
  apply hh.congr'
  filter_upwards with n
  simp only [Function.comp_def, g, zero_add, add_zero]

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! One-dimensional Fourier coefficients and integration by parts for transverse cell profiles. -/

def unitProfileFourierCoeff (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f n

theorem unitProfileFourierCoeff_norm_le (f : ℝ → ℂ) (n : ℤ) (C : ℝ)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, ‖f x‖ ≤ C) : ‖unitProfileFourierCoeff f n‖ ≤ C := by
  unfold unitProfileFourierCoeff
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero, div_one, one_smul]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (f := fun x : ℝ => fourier (-n) (x : AddCircle ((1 : ℝ) - 0)) • f x)
    (C := C) (fun x hx => by
      rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
      have hx' : x ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
      exact hf x ⟨hx'.1.le, hx'.2⟩)
  simpa only [sub_zero, abs_one, mul_one] using! hb

theorem unitProfileFourierCoeff_deriv (f : ℝ → ℂ) (hf : ContDiff ℝ 1 f)
    (hp : Function.Periodic f 1) (n : ℤ) (hn : n ≠ 0) :
    unitProfileFourierCoeff (deriv f) n =
      (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) * unitProfileFourierCoeff f n := by
  have he := fourierCoeffOn_of_hasDerivAt (by norm_num : (0 : ℝ) < 1) hn
    (fun x _ => ((hf.differentiable (by norm_num)) x).hasDerivAt)
    (hf.continuous_deriv_one.intervalIntegrable 0 1)
  have hperiod : f 1 = f 0 := by simpa using hp 0
  simp only [hperiod, sub_self, mul_zero, Complex.ofReal_one, Complex.ofReal_zero,
    sub_zero, one_mul, zero_sub] at he
  have hden : (-2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero) (by exact_mod_cast hn)
  change fourierCoeffOn (by norm_num : (0 : ℝ) < 1) (deriv f) n =
    (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)) * fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f n
  rw [he]
  field_simp [hden]

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleComparison.Lift

/-! Exact scalar frequencies of the transverse unit-period Fourier profiles. -/

def profileFourierFrequency (n : ℤ) : ℂ := 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ)

theorem profileFourierFrequency_ne_zero (n : ℤ) (hn : n ≠ 0) :
    profileFourierFrequency n ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero) (by exact_mod_cast hn)

theorem profileFourierFrequency_norm_sq (n : ℤ) :
    ‖profileFourierFrequency n‖ ^ 2 = 4 * Real.pi ^ 2 * (n : ℝ) ^ 2 := by
  rw [Complex.sq_norm]
  simp only [profileFourierFrequency, Complex.normSq_mul]
  norm_num [Complex.normSq_ofReal]
  ring

/-! Total one-dimensional derivatives preserve profile periodicity without adding smoothness premises. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem profile_deriv_periodic (f : ℝ → E) (T : ℝ) (hp : Function.Periodic f T) :
    Function.Periodic (deriv f) T := by
  have he : (fun x => f (x + T)) = f := funext hp
  intro x
  rw [← deriv_comp_add_const f T x, he]

theorem profile_iteratedDeriv_periodic (f : ℝ → E) (T : ℝ) (hp : Function.Periodic f T) (j : ℕ) :
    Function.Periodic (iteratedDeriv j f) T := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero] using hp
  | succ j ih => rw [iteratedDeriv_succ]; exact profile_deriv_periodic _ T ih
end

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Joint L² admissibility of the actual bounded transverse source on the finite time cylinder. -/

theorem transverseSource_measurable (f : ℝ → ℝ → ℂ)
    (hf : Measurable (Function.uncurry f)) (par : Fin 2) :
    Measurable (fun p : ℝ × Vec 2 => f p.1 (p.2 par.rev)) :=
  hf.comp (measurable_fst.prodMk ((measurable_pi_apply par.rev).comp measurable_snd))

theorem transverseSource_memLp (f : ℝ → ℝ → ℂ)
    (hf : Measurable (Function.uncurry f)) (par : Fin 2) (a b C : ℝ)
    (hb : ∀ t ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) 1, ‖f t x‖ ≤ C) :
    MemLp (fun p : ℝ × Vec 2 => f p.1 (p.2 par.rev)) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)) := by
  let : IsFiniteMeasure (volume.restrict AVenhance.unitCube) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      AVenhance.Infra.Parabolic.WeakUniqueness.WeakAlgebra.weak_unitCube_volume_lt_top⟩
  have hm := AVenhance.Infra.Parabolic.FourierGalerkin.TestDensityBridge.bridge_unitCube_measurable
  have ha : ∀ᵐ p : ℝ × Vec 2 ∂(volume.restrict (Icc a b)).prod
      (volume.restrict AVenhance.unitCube), p.1 ∈ Icc a b ∧ p.2 ∈ AVenhance.unitCube := by
    apply (Measure.ae_prod_iff_ae_ae
      ((measurableSet_Icc.preimage measurable_fst).inter (hm.preimage measurable_snd))).mpr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    filter_upwards [ae_restrict_mem hm] with z hz
    exact ⟨ht, hz⟩
  apply MemLp.of_bound (transverseSource_measurable f hf par).aestronglyMeasurable C
  filter_upwards [ha] with p hp
  have hx : p.2 par.rev ∈ Ioo (0 : ℝ) 1 := by
    exact (Set.mem_pi.mp hp.2) par.rev (Set.mem_univ _)
  exact hb p.1 hp.1 (p.2 par.rev) ⟨hx.1.le, hx.2.le⟩

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public section
namespace AVRegularity.CycleComparison.Lift

/-! Genuine continuous real duals separate vectors without choosing quantitative coordinates. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem eq_of_all_real_duals (x y : E) (h : ∀ l : E →L[ℝ] ℝ, l x = l y) : x = y := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply NormedSpace.norm_le_dual_bound (𝕜 := ℝ) (x - y) (le_refl 0)
  intro l
  simp only [map_sub, h l, sub_self, norm_zero, zero_mul, le_refl]
end

/-! A scalar coefficient times a fixed vector has its scalar jet budget times the vector norm. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_iteratedFDeriv_smul_const_le (r : ℕ) (f : E → ℝ)
    (hf : ContDiff ℝ (r : ℕ∞) f) (v : F) (X : E) :
    ‖iteratedFDeriv ℝ r (fun Y => f Y • v) X‖ ≤ ‖iteratedFDeriv ℝ r f X‖ * ‖v‖ := by
  rw [iteratedFDeriv_smul_const_apply hf.contDiffAt]
  have h := ((ContinuousLinearMap.id ℝ ℝ).smulRight v).norm_compContinuousMultilinearMap_le
    (iteratedFDeriv ℝ r f X)
  simpa only [ContinuousLinearMap.norm_smulRight_apply, ContinuousLinearMap.norm_id,
    one_mul, mul_one, mul_comm] using h
end

/-! Rectangular slow jet majorants multiply without losing their scale power. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_iteratedFDeriv_smul_scaled_le (n : ℕ) (f : E → ℝ) (g : E → F)
    (hf : ContDiff ℝ (n : ℕ∞) f) (hg : ContDiff ℝ (n : ℕ∞) g)
    (x : E) (lam : ℝ) (hlam : 0 ≤ lam) (A B : ℕ → ℝ)
    (hA : ∀ j ≤ n, 0 ≤ A j) (hB : ∀ j ≤ n, 0 ≤ B j)
    (hbA : ∀ j ≤ n, ‖iteratedFDeriv ℝ j f x‖ ≤ A j * lam ^ j)
    (hbB : ∀ j ≤ n, ‖iteratedFDeriv ℝ j g x‖ ≤ B j * lam ^ j) :
    ‖iteratedFDeriv ℝ n (fun y => f y • g y) x‖ ≤
      (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * A j * B (n - j)) * lam ^ n := by
  apply (norm_iteratedFDeriv_smul_le hf hg x (by simp)).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hjn : j ≤ n := by have hh := Finset.mem_range.mp hj; omega
  have hAj := hA j hjn
  have hBj := hB (n - j) (Nat.sub_le n j)
  calc
    _ ≤ (n.choose j : ℝ) * (A j * lam ^ j) * (B (n - j) * lam ^ (n - j)) := by
      gcongr
      · exact hbA j hjn
      · exact hbB (n - j) (Nat.sub_le n j)
    _ = ((n.choose j : ℝ) * A j * B (n - j)) * lam ^ n := by
      have hp : lam ^ j * lam ^ (n - j) = lam ^ n := by
        rw [← pow_add, Nat.add_sub_of_le hjn]
      calc
        _ = ((n.choose j : ℝ) * A j * B (n - j)) *
            (lam ^ j * lam ^ (n - j)) := by ring
        _ = _ := by rw [hp]
end

/-! Adding smooth coefficient fields adds their slow-jet budgets. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_iteratedFDeriv_add_le (r : ℕ) (f g : E → F)
    (hf : ContDiff ℝ (r : ℕ∞) f) (hg : ContDiff ℝ (r : ℕ∞) g) (X : E) :
    ‖iteratedFDeriv ℝ r (fun Y => f Y + g Y) X‖ ≤
      ‖iteratedFDeriv ℝ r f X‖ + ‖iteratedFDeriv ℝ r g X‖ := by
  change ‖iteratedFDeriv ℝ r (f + g) X‖ ≤ _
  rw [iteratedFDeriv_add_apply hf.contDiffAt hg.contDiffAt]
  exact norm_add_le _ _
end

/-! Subtracting a scalar multiple of size at most one adds the two slow-jet budgets. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_iteratedFDeriv_sub_smul_le (r : ℕ) (f g : E → F)
    (hf : ContDiff ℝ (r : ℕ∞) f) (hg : ContDiff ℝ (r : ℕ∞) g)
    (a : ℝ) (ha : ‖a‖ ≤ 1) (X : E) :
    ‖iteratedFDeriv ℝ r (fun Y => f Y - a • g Y) X‖ ≤
      ‖iteratedFDeriv ℝ r f X‖ + ‖iteratedFDeriv ℝ r g X‖ := by
  change ‖iteratedFDeriv ℝ r (f - fun Y => a • g Y) X‖ ≤ _
  rw [iteratedFDeriv_sub_apply hf.contDiffAt ((hg.const_smul a).contDiffAt),
    iteratedFDeriv_const_smul_apply' hg.contDiffAt]
  apply (norm_sub_le _ _).trans
  rw [norm_smul]
  exact add_le_add_right
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right ha (norm_nonneg (iteratedFDeriv ℝ r g X)))
    ‖iteratedFDeriv ℝ r f X‖
end

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Spatial dilation and scalar multiplication have their exact jet-norm scale. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_iteratedFDeriv_dilation_smul (j : ℕ) (a c : ℝ) (f : Vec 2 → E)
    (hf : ContDiff ℝ (j : ℕ∞) f) (X : Vec 2) :
    ‖iteratedFDeriv ℝ j (fun Y => c • f (a • Y)) X‖ =
      |c| * |a| ^ j * ‖iteratedFDeriv ℝ j f (a • X)‖ := by
  have hd : ContDiff ℝ (j : ℕ∞) (fun Y : Vec 2 => f (a • Y)) :=
    hf.comp (contDiff_const_smul a)
  rw [iteratedFDeriv_const_smul_apply' hd.contDiffAt]
  have he := congrFun (iteratedFDeriv_comp_const_smul a hf) X
  rw [he, norm_smul, norm_smul]
  simp only [Real.norm_eq_abs, abs_pow, mul_assoc]

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance.Infra.Torus
namespace AVRegularity.CycleComparison.Lift

/-! A transverse two-dimensional character is the literal one-dimensional character. -/

theorem torusCharacter_eq_transverse_fourier (par : Fin 2) (k : Fin 2 → ℤ)
    (hk : k par = 0) (z : Vec 2) :
    torusCharacter k z = fourier (-(k par.rev)) (z par.rev : AddCircle (1 : ℝ)) := by
  fin_cases par
  · change k 0 = 0 at hk
    simp [torusCharacter, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
      toUnitTorus, Fin.prod_univ_two, hk]
  · change k 1 = 0 at hk
    simp [torusCharacter, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
      toUnitTorus, Fin.prod_univ_two, hk]

/-! The compiled Fourier multiplier identity eliminates longitudinal modes. -/

theorem smoothFourierCoeff_zero_of_transverse (par : Fin 2) (f : Vec 2 → ℂ)
    (hf : ContDiff ℝ 1 f) (hp : IsZdPeriodic f)
    (hpar : ∀ z, coordDeriv par f z = 0) (k : Fin 2 → ℤ) (hk : k par ≠ 0) :
    smoothFourierCoeff f k = 0 := by
  have he : coordDeriv par f = fun _ => 0 := funext hpar
  have hh := smoothFourierCoeff_coordDeriv par hf hp k
  rw [he] at hh
  have hz : smoothFourierCoeff (fun _ : Vec 2 => (0 : ℂ)) k = 0 := by
    simp [smoothFourierCoeff]
  rw [hz] at hh
  have hc : (2 * Real.pi * Complex.I * (k par : ℂ)) ≠ 0 := by
    apply mul_ne_zero
    · exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
        Complex.I_ne_zero
    · exact_mod_cast hk
  exact (mul_eq_zero.mp hh.symm).resolve_left hc

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleComparison.Lift

/-! Two integer Fourier coordinates separate the longitudinal and transverse modes. -/

def transverseFrequencyEquiv (par : Fin 2) : (Fin 2 → ℤ) ≃ ℤ × ℤ where
  toFun k := (k par, k par.rev)
  invFun p := fun i => if i = par then p.1 else p.2
  left_inv k := by
    funext i
    fin_cases par <;> fin_cases i <;> simp
  right_inv p := by
    fin_cases par <;> simp

theorem transverseFrequencyEquiv_symm_parallel (par : Fin 2) (p : ℤ × ℤ) :
    (transverseFrequencyEquiv par).symm p par = p.1 := by
  simp [transverseFrequencyEquiv]

theorem transverseFrequencyEquiv_symm_transverse (par : Fin 2) (p : ℤ × ℤ) :
    (transverseFrequencyEquiv par).symm p par.rev = p.2 := by
  fin_cases par <;> simp [transverseFrequencyEquiv]

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! The exact scalar propagator for a transverse Fourier mode with measurable cell metric. -/

def transverseModeKernel (rate : ℝ) (g : ℝ → ℝ) (s t : ℝ) : ℝ :=
  Real.exp (-rate * ∫ r in s..t, g r)

@[simp] theorem transverseModeKernel_same (rate : ℝ) (g : ℝ → ℝ) (s : ℝ) :
    transverseModeKernel rate g s s = 1 := by simp [transverseModeKernel]

theorem transverseModeKernel_pos (rate : ℝ) (g : ℝ → ℝ) (s t : ℝ) :
    0 < transverseModeKernel rate g s t := Real.exp_pos _

theorem transverseModeKernel_le_exp (rate κ : ℝ) (hrate : 0 ≤ rate) (g : ℝ → ℝ)
    (s t : ℝ) (hst : s ≤ t) (hi : IntervalIntegrable g volume s t)
    (hg : ∀ r ∈ Icc s t, κ ≤ g r) :
    transverseModeKernel rate g s t ≤ Real.exp (-(rate * κ) * (t - s)) := by
  have hb := intervalIntegral.integral_mono_on hst (intervalIntegrable_const (μ := volume)) hi hg
  have hb' : κ * (t - s) ≤ ∫ r in s..t, g r := by
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hb
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_left hb' hrate
  calc
    -rate * (∫ r in s..t, g r) = -(rate * (∫ r in s..t, g r)) := by ring
    _ ≤ -(rate * (κ * (t - s))) := neg_le_neg hh
    _ = _ := by ring

end AVRegularity.CycleComparison.Lift
end
end
