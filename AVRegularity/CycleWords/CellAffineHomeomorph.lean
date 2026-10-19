-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Homogenization.Ambient.Basic

section
@[expose] public section
namespace AVRegularity.CycleWords

/-! Adjacent multiplicative interpolation preserves the linear frequency and polynomial contrast prices. -/

theorem adjacent_polynomial_gap_price (j : ℕ) (A B C N B₀ C₀ p x γ D : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hN : 0 ≤ N) (hB₀ : 0 ≤ B₀) (hC₀ : 0 ≤ C₀)
    (hp : 0 ≤ p) (hx : 0 ≤ x)
    (hinterp : A ^ 2 ≤ N * (B * C))
    (hBlow : B ≤ B₀ * p ^ (2 * j) * x * Real.exp (-γ * D))
    (hChigh : C ≤ C₀ * p ^ (2 * (j + 2)) * x) :
    A ≤ Real.sqrt (N * B₀ * C₀) * p ^ (2 * (j + 1)) * x * Real.exp (-γ * D / 2) := by
  have hbudget := hinterp.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul hBlow hChigh hC (by positivity)) hN)
  have hexp : Real.exp (-γ * D / 2) ^ 2 = Real.exp (-γ * D) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hpow : (p ^ (2 * (j + 1))) ^ 2 = p ^ (2 * j) * p ^ (2 * (j + 2)) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  apply (sq_le_sq₀ hA (by positivity)).mp
  rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity), hpow, hexp]
  convert hbudget using 1
  ring

/-! Constants for all polynomial degrees of the adjoint chart weights. -/

def adjointWeightRate (C K : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * (4 * K * (1 + C) + 16 * C) + 2080 * (n : ℝ) ^ 2 * C

def adjointWeightComparison (C : ℝ) (n : ℕ) : ℝ := (2 + 4 * (1 + C) ^ 2) ^ n

def adjointWeightConstant (C K : ℝ) (n : ℕ) : ℝ :=
  1 + adjointWeightComparison C n + adjointWeightRate C K n

theorem adjointWeightRate_nonneg {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) (n : ℕ) :
    0 ≤ adjointWeightRate C K n := by unfold adjointWeightRate; positivity

theorem adjointWeightRate_defect {C K : ℝ} (hC : 0 ≤ C) (_hK : 0 ≤ K) (n : ℕ) :
    (n : ℝ) * (4 * K * (1 + C) + 16 * C) + (n : ℝ) ^ 2 * (32 * C) ≤
      adjointWeightRate C K n := by
  unfold adjointWeightRate
  nlinarith only [mul_nonneg (sq_nonneg (n : ℝ)) hC]

theorem adjointWeightRate_gradient {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) (n : ℕ) :
    65 * ((n : ℝ) ^ 2 * (32 * C)) ≤ adjointWeightRate C K n := by
  unfold adjointWeightRate
  have hh : 0 ≤ (n : ℝ) * (4 * K * (1 + C) + 16 * C) := by positivity
  nlinarith only [hh]

theorem adjointWeightComparison_pos (C : ℝ) (n : ℕ) : 0 < adjointWeightComparison C n := by
  unfold adjointWeightComparison
  positivity

theorem adjointWeightConstant_comparison {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K) (n : ℕ) :
    adjointWeightComparison C n ≤ adjointWeightConstant C K n := by
  have hh := adjointWeightRate_nonneg hC hK n
  unfold adjointWeightConstant
  linarith only [hh]

theorem adjointWeightConstant_rate {C K : ℝ} (_hC : 0 ≤ C) (_hK : 0 ≤ K) (n : ℕ) :
    adjointWeightRate C K n ≤ adjointWeightConstant C K n := by
  have hh := (adjointWeightComparison_pos C n).le
  unfold adjointWeightConstant
  linarith only [hh]

end AVRegularity.CycleWords
end
end

section
public section
open Complex Metric
namespace AVRegularity.CycleWords

/-! A literal circle bound controls every native Cauchy coefficient. -/

theorem boundedCauchyCoefficient_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (f : ℂ → E) (c : ℂ) (R M : ℝ) (hR : 0 ≤ R)
    (hb : ∀ z ∈ sphere c R, ‖f z‖ ≤ M) (n : ℕ) :
    ‖cauchyPowerSeries f c R n‖ ≤ M * R⁻¹ ^ n := by
  have hi : (∫ θ : ℝ in 0..2 * Real.pi, ‖f (circleMap c R θ)‖) ≤
      (2 * Real.pi) * M := by
    have hn := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun θ : ℝ => ‖f (circleMap c R θ)‖)
      (a := 0) (b := 2 * Real.pi) (C := M) (fun θ _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact hb _ (circleMap_mem_sphere c hR θ))
    have hv := le_abs_self (∫ θ : ℝ in 0..2 * Real.pi, ‖f (circleMap c R θ)‖)
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg Real.two_pi_pos.le, mul_comm M]
      using hv.trans hn
  have ha : (2 * Real.pi)⁻¹ * (∫ θ : ℝ in 0..2 * Real.pi, ‖f (circleMap c R θ)‖) ≤ M := by
    calc
      _ ≤ (2 * Real.pi)⁻¹ * ((2 * Real.pi) * M) :=
        mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr Real.two_pi_pos.le)
      _ = M := inv_mul_cancel_left₀ Real.two_pi_pos.ne' M
  exact (norm_cauchyPowerSeries_le f c R n).trans
    (by rw [abs_of_nonneg hR]; exact mul_le_mul_of_nonneg_right ha (pow_nonneg (inv_nonneg.mpr hR) n))

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! A bounded integral extends to all bounded time functions, and agrees on integrable slices. -/

abbrev BoundedComplexTime := lp (fun _ : ℝ => ℂ) ⊤

def boundedTimeIntegrableSubspace (μ : Measure ℝ) : Submodule ℂ BoundedComplexTime where
  carrier := {u | Integrable (fun t => u t) μ}
  zero_mem' := integrable_zero _ _ _
  add_mem' := fun hu hz => hu.add hz
  smul_mem' := fun a _ hu => hu.smul a

def boundedTimeIntegralLinearMap (μ : Measure ℝ) :
    boundedTimeIntegrableSubspace μ →ₗ[ℂ] ℂ where
  toFun u := ∫ t, (u.val t) ∂μ
  map_add' u z := integral_add u.property z.property
  map_smul' a u := integral_smul a (fun t => u.val t)

def boundedTimeIntegralCLM (μ : Measure ℝ) [IsFiniteMeasure μ] :
    boundedTimeIntegrableSubspace μ →L[ℂ] ℂ :=
  (boundedTimeIntegralLinearMap μ).mkContinuous (μ.real Set.univ) (by
    intro u
    have h := norm_integral_le_of_norm_le_const (μ := μ)
      (Filter.Eventually.of_forall (fun t => lp.norm_apply_le_norm ENNReal.top_ne_zero u.val t))
    exact h.trans_eq (mul_comm _ _))

def boundedTimeIntegralExtension (μ : Measure ℝ) [IsFiniteMeasure μ] :
    BoundedComplexTime →L[ℂ] ℂ :=
  Classical.choose (exists_extension_norm_eq (boundedTimeIntegrableSubspace μ)
    (boundedTimeIntegralCLM μ))

theorem boundedTimeIntegralExtension_apply (μ : Measure ℝ) [IsFiniteMeasure μ]
    (u : BoundedComplexTime) (hu : Integrable (fun t => u t) μ) :
    boundedTimeIntegralExtension μ u = ∫ t, u t ∂μ :=
  (Classical.choose_spec (exists_extension_norm_eq (boundedTimeIntegrableSubspace μ)
    (boundedTimeIntegralCLM μ))).1 ⟨u, hu⟩

end AVRegularity.CycleWords
end
end

section
@[expose] public section
open MeasureTheory TopologicalSpace
namespace AVRegularity.CycleWords

/-! Evaluation of a measurable family continuous in its state variable. -/

theorem caratheodoryFamily_stronglyMeasurable
    {X Z F : Type*} [MeasurableSpace X] [TopologicalSpace Z] [MetrizableSpace Z]
    [MeasurableSpace Z] [SecondCountableTopology Z] [BorelSpace Z]
    [TopologicalSpace F] [PseudoMetrizableSpace F]
    (A : X → Z → F) (hC : ∀ x, Continuous (A x))
    (hM : ∀ z, StronglyMeasurable (fun x => A x z))
    (u : X → Z) (hu : StronglyMeasurable u) :
    StronglyMeasurable (fun x => A x (u x)) :=
  (stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hC hM).comp_measurable
    (hu.measurable.prodMk measurable_id)

end AVRegularity.CycleWords
end
end

section
@[expose] public section
namespace AVRegularity.CycleWords

/-! A uniform difference norm estimate transfers the Cauchy property. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

theorem cauchySeq_of_norm_sub_le (u : ℕ → E) (v : ℕ → F) (C : ℝ)
    (hu : CauchySeq u) (hv : ∀ n m, ‖v n - v m‖ ≤ C * ‖u n - u m‖) :
    CauchySeq v := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hC : 0 < |C| + 1 := by positivity
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu (ε / (|C| + 1)) (div_pos hε hC)
  refine ⟨N, fun n hn m hm => ?_⟩
  rw [dist_eq_norm]
  calc
    _ ≤ C * ‖u n - u m‖ := hv n m
    _ ≤ (|C| + 1) * ‖u n - u m‖ :=
      mul_le_mul_of_nonneg_right ((le_abs_self C).trans (le_add_of_nonneg_right (by norm_num)))
        (norm_nonneg _)
    _ < (|C| + 1) * (ε / (|C| + 1)) :=
      mul_lt_mul_of_pos_left (by simpa only [dist_eq_norm] using hN n hn m hm) hC
    _ = ε := mul_div_cancel₀ ε hC.ne'

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleWords

/-! Exact positive-order derivatives under the spatial cell rescaling. -/

theorem cell_rescaled_iteratedFDeriv (F : Vec 2 → Vec 2)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (e : ℝ) (y y' : Vec 2) (j : ℕ) (hj : 1 ≤ j)
    (z : Vec 2) :
    iteratedFDeriv ℝ j (fun z : Vec 2 => e⁻¹ • (F (y' + e • z) - y)) z =
      (e⁻¹ * e ^ j) • iteratedFDeriv ℝ j F (y' + e • z) := by
  have hs : ContDiff ℝ j (fun z : Vec 2 => F (y' + e • z)) :=
    (hF.of_le (by simp)).comp (contDiff_const.add (contDiff_id.const_smul e))
  rw [iteratedFDeriv_const_smul_apply' (hs.contDiffAt.sub contDiffAt_const)]
  change e⁻¹ • iteratedFDeriv ℝ j ((fun z : Vec 2 => F (y' + e • z)) -
    (fun _ : Vec 2 => y)) z = _
  rw [iteratedFDeriv_sub_apply hs.contDiffAt (contDiffAt_const (c := y)),
    iteratedFDeriv_const_of_ne (by omega : j ≠ 0)]
  simp only [Pi.zero_apply, sub_zero]
  have hshift : ContDiff ℝ j (fun z : Vec 2 => F (y' + z)) :=
    (hF.of_le (by simp)).comp ((contDiff_const (c := y')).add contDiff_id)
  have hc := congrFun (iteratedFDeriv_comp_const_smul e hshift) z
  rw [hc, iteratedFDeriv_comp_add_left, smul_smul]

theorem cell_rescaled_iteratedFDeriv_norm (F : Vec 2 → Vec 2)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (e : ℝ) (he : 0 < e) (y y' : Vec 2)
    (j : ℕ) (hj : 1 ≤ j) (z : Vec 2) :
    ‖iteratedFDeriv ℝ j (fun z : Vec 2 => e⁻¹ • (F (y' + e • z) - y)) z‖ =
      e ^ (j - 1) * ‖iteratedFDeriv ℝ j F (y' + e • z)‖ := by
  rw [cell_rescaled_iteratedFDeriv F hF e y y' j hj z, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have heq : e⁻¹ * e ^ j = e ^ (j - 1) := by
    calc
      e⁻¹ * e ^ j = e⁻¹ * (e ^ (j - 1) * e) := by
        conv_lhs => arg 2; rw [show j = j - 1 + 1 by omega, pow_succ]
      _ = e ^ (j - 1) := by field_simp
  rw [heq]

/-! The two affine chart changes surrounding a renewal give a genuine homeomorphism. -/

def cellAffineHomeomorph (e : ℝ) (he : e ≠ 0) (y : Vec 2) : Vec 2 ≃ₜ Vec 2 where
  toFun := fun z => y + e • z
  invFun := fun z => e⁻¹ • (z - y)
  left_inv := by
    intro z
    simp only [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ he, one_smul]
  right_inv := by
    intro z
    simp only [smul_smul, mul_inv_cancel₀ he, one_smul, add_sub_cancel]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def cellRescaledHomeomorph (X : Vec 2 ≃ₜ Vec 2) (e : ℝ) (he : e ≠ 0)
    (y y' : Vec 2) : Vec 2 ≃ₜ Vec 2 :=
  (cellAffineHomeomorph e he y').trans (X.trans (cellAffineHomeomorph e he y).symm)

@[simp] theorem cellRescaledHomeomorph_apply (X : Vec 2 ≃ₜ Vec 2) (e : ℝ) (he : e ≠ 0)
    (y y' z : Vec 2) :
    cellRescaledHomeomorph X e he y y' z = e⁻¹ • (X (y' + e • z) - y) := rfl

@[simp] theorem cellRescaledHomeomorph_symm_apply (X : Vec 2 ≃ₜ Vec 2) (e : ℝ) (he : e ≠ 0)
    (y y' z : Vec 2) :
    (cellRescaledHomeomorph X e he y y').symm z = e⁻¹ • (X.symm (y + e • z) - y') := rfl

end AVRegularity.CycleWords
end
end
