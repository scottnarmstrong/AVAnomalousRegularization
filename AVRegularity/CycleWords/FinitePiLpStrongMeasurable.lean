-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Homogenization.Sobolev.WeakDerivatives
import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.Real.Pi.Bounds
import AVenhance.Infra.FaaDiBruno.Formula
import AVenhance.Infra.Parabolic.FourierGalerkin.MatrixOperator

section
@[expose] public noncomputable section
open Homogenization
open scoped NNReal
namespace AVRegularity.CycleWords

/-! Equal spatial rescalings leave the Lipschitz constant of a renewal unchanged. -/

theorem cell_rescaled_lipschitz (F : Vec 2 → Vec 2) (L : ℝ≥0)
    (hF : LipschitzWith L F) (e : ℝ) (he : 0 < e) (y y' : Vec 2) :
    LipschitzWith L (fun z : Vec 2 => e⁻¹ • (F (y' + e • z) - y)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [dist_eq_norm]
  rw [← smul_sub, sub_sub_sub_cancel_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr he)]
  have hb := hF.dist_le_mul (y' + e • z) (y' + e • w)
  simp only [dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_of_pos he] at hb
  calc
    _ ≤ e⁻¹ * ((L : ℝ) * (e * ‖z - w‖)) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr he.le)
    _ = _ := by field_simp

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Equal spatial rescalings preserve the measure-preserving property of a renewal. -/

theorem map_cell_affine_volume (e : ℝ) (he : e ≠ 0) (y : Vec 2) :
    Measure.map (fun z : Vec 2 => y + e • z) volume =
      ENNReal.ofReal |(e ^ 2)⁻¹| • (volume : Measure (Vec 2)) := by
  have ht := (measurePreserving_add_left (volume : Measure (Vec 2)) y).map_eq
  have hs := Measure.map_addHaar_smul (volume : Measure (Vec 2)) he
  rw [show (fun z : Vec 2 => y + e • z) = (fun z : Vec 2 => y + z) ∘ (fun z => e • z) by rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop), hs, Measure.map_smul _ (by fun_prop), ht]
  simp only [Module.finrank_pi, Fintype.card_fin]

theorem cell_rescaled_measurePreserving (F : Vec 2 → Vec 2)
    (hF : MeasurePreserving F volume volume) (e : ℝ) (he : e ≠ 0) (y y' : Vec 2) :
    MeasurePreserving (fun z : Vec 2 => e⁻¹ • (F (y' + e • z) - y)) volume volume := by
  have hm : Measurable (fun z : Vec 2 => e⁻¹ • (F (y' + e • z) - y)) := by
    have ha : Measurable (fun z : Vec 2 => y' + e • z) := by fun_prop
    exact ((hF.measurable.comp ha).sub_const y).const_smul (e⁻¹ : ℝ)
  refine ⟨hm, ?_⟩
  have heinv : e⁻¹ ≠ 0 := inv_ne_zero he
  have hrev : (fun z : Vec 2 => e⁻¹ • (z - y)) =
      fun z => -(e⁻¹ • y) + e⁻¹ • z := by
    funext z
    rw [smul_sub]
    abel
  rw [show (fun z : Vec 2 => e⁻¹ • (F (y' + e • z) - y)) =
    (fun z : Vec 2 => e⁻¹ • (z - y)) ∘ F ∘ (fun z => y' + e • z) by rfl,
    ← Measure.map_map (by fun_prop) (hF.measurable.comp (by fun_prop)),
    ← Measure.map_map hF.measurable (by fun_prop),
    map_cell_affine_volume e he y', Measure.map_smul _ hF.measurable.aemeasurable,
    hF.map_eq, Measure.map_smul _ (by fun_prop), hrev,
    map_cell_affine_volume e⁻¹ heinv (-(e⁻¹ • y)), smul_smul]
  have hc : ENNReal.ofReal |(e ^ 2)⁻¹| * ENNReal.ofReal |((e⁻¹) ^ 2)⁻¹| = 1 := by
    rw [← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul]
    have heq : (e ^ 2)⁻¹ * ((e⁻¹) ^ 2)⁻¹ = 1 := by
      rw [inv_pow, inv_inv, inv_mul_cancel₀ (pow_ne_zero _ he)]
    rw [heq, abs_one, ENNReal.ofReal_one]
  rw [hc, one_smul]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization
open scoped NNReal ENNReal
namespace AVRegularity.CycleWords

/-! Centred polynomial weights transfer under the inverse chart Lipschitz bound. -/

theorem vec2_norm_le_abs_sum (x : Vec 2) : ‖x‖ ≤ |x 0| + |x 1| := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  fin_cases i
  · change |x 0| ≤ |x 0| + |x 1|
    exact le_add_of_nonneg_right (abs_nonneg (x 1))
  · change |x 1| ≤ |x 0| + |x 1|
    exact le_add_of_nonneg_left (abs_nonneg (x 0))

theorem centred_polynomial_pullback_bound (X : Vec 2 → Vec 2) (L : ℝ)
    (hL : 0 ≤ L) (hX : ∀ z, ‖z‖ ≤ L * ‖X z‖) (ϖ : ℝ) (n : ℕ) (z : Vec 2) :
    (1 + ϖ ^ 2 * ((z 0) ^ 2 + (z 1) ^ 2)) ^ n ≤
      (1 + 4 * L ^ 2) ^ n * (1 + ϖ ^ 2 * ((X z 0) ^ 2 + (X z 1) ^ 2)) ^ n := by
  have hz (i : Fin 2) : |z i| ≤ L * (|X z 0| + |X z 1|) := by
    exact (norm_le_pi_norm z i).trans ((hX z).trans
      (mul_le_mul_of_nonneg_left (vec2_norm_le_abs_sum (X z)) hL))
  have hz0 := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (hz 0)
  have hz1 := (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr (hz 1)
  have hc : (|X z 0| + |X z 1|) ^ 2 ≤ 2 * ((X z 0) ^ 2 + (X z 1) ^ 2) := by
    nlinarith only [sq_nonneg (|X z 0| - |X z 1|), sq_abs (X z 0), sq_abs (X z 1)]
  have hsum : (z 0) ^ 2 + (z 1) ^ 2 ≤ 4 * L ^ 2 * ((X z 0) ^ 2 + (X z 1) ^ 2) := by
    have hh := mul_le_mul_of_nonneg_left hc (sq_nonneg L)
    simp only [mul_pow, sq_abs] at hz0 hz1
    nlinarith only [hz0, hz1, hh]
  have hb := mul_le_mul_of_nonneg_left hsum (sq_nonneg ϖ)
  have ht : 1 + ϖ ^ 2 * ((z 0) ^ 2 + (z 1) ^ 2) ≤
      (1 + 4 * L ^ 2) * (1 + ϖ ^ 2 * ((X z 0) ^ 2 + (X z 1) ^ 2)) := by
    nlinarith only [hb, sq_nonneg L, mul_nonneg (sq_nonneg ϖ)
      (add_nonneg (sq_nonneg (X z 0)) (sq_nonneg (X z 1)))]
  simpa only [mul_pow] using pow_le_pow_left₀ (by positivity) ht n

theorem centred_homeomorph_inverse_norm (X : Vec 2 ≃ₜ Vec 2)
    (L : ℝ≥0) (hL : LipschitzWith L (X.symm : Vec 2 → Vec 2)) (h0 : X 0 = 0)
    (z : Vec 2) : ‖z‖ ≤ (L : ℝ) * ‖X z‖ := by
  have he : X.symm 0 = 0 := (congrArg X.symm h0).symm.trans (X.symm_apply_apply 0)
  have hh := hL.dist_le_mul (X z) 0
  simpa only [X.symm_apply_apply, he, dist_zero_right] using hh

end AVRegularity.CycleWords
end
end

section
@[expose] public section
namespace AVRegularity.CycleWords

/-! Combine the genuine drift and metric word budgets before time integration. -/

theorem compact_source_budget_combine {L R Rc D F U ν M η ε : ℝ}
    (hL : L ≤ 2 * (ε ^ 2 * D) + 2 * F)
    (hR : R ≤ (ν / 4) * D) (hRc : Rc ≤ R) :
    8 * L + (4096 * η ^ 2 + 16 * M * η) * U + 2 * Rc ≤
      16 * F + (16 * ε ^ 2 + ν / 2) * D +
        (4096 * η ^ 2 + 16 * M * η) * U := by
  nlinarith

end AVRegularity.CycleWords
end
end

section
public section
namespace AVRegularity.CycleWords

/-! Complementary past and future forgetting combine to the full buffer length. -/

theorem complementaryExponentialBuffers (γ δ a b D C E x y : ℝ)
    (hγ : 0 ≤ γ) (hδ : γ ≤ δ) (hb : 0 ≤ b) (hD : D ≤ a + b)
    (hC : 0 ≤ C) (hE : 0 ≤ E) (hy : 0 ≤ y)
    (hx : x ≤ C * Real.exp (-γ * a)) (hyb : y ≤ E * Real.exp (-δ * b)) :
    x * y ≤ (C * E) * Real.exp (-γ * D) := by
  have hd : -γ * a + -δ * b ≤ -γ * D := by
    have hdb := mul_le_mul_of_nonneg_right hδ hb
    have hsum := mul_le_mul_of_nonneg_left hD hγ
    linarith only [hdb, hsum]
  calc
    _ ≤ (C * Real.exp (-γ * a)) * (E * Real.exp (-δ * b)) :=
      mul_le_mul hx hyb hy (mul_nonneg hC (Real.exp_pos _).le)
    _ = (C * E) * Real.exp (-γ * a + -δ * b) := by
      rw [Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hd) (mul_nonneg hC hE)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Complex MeasureTheory Metric
namespace AVRegularity.CycleWords

/-! A bounded complex circle gives a geometric bound on the exact Cauchy coefficient. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem complexCauchy_coefficient_norm_le (f : ℂ → E) (R M : ℝ) (hR : 0 < R)
    (hb : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ M) (n : ℕ) :
    ‖cauchyPowerSeries f 0 R n (fun _ => 1)‖ ≤ M * R⁻¹ ^ n := by
  rw [cauchyPowerSeries_apply]
  have he := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le
    (c := (0 : ℂ)) (f := fun z => ((1 : ℂ) / (z - 0)) ^ n • (z - 0)⁻¹ • f z)
    (C := R⁻¹ ^ n * R⁻¹ * M) (by
      intro z hz
      have hn : ‖z‖ = R := by simpa only [mem_sphere, dist_zero_right] using hz
      simp only [sub_zero, one_div, norm_smul, norm_pow, norm_inv, hn]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hb z hz)
        (mul_nonneg (pow_nonneg (inv_nonneg.mpr hR.le) n) (inv_nonneg.mpr hR.le)))
  apply he.trans_eq
  have hi : R * R⁻¹ = 1 := mul_inv_cancel₀ hR.ne'
  calc
    R * (R⁻¹ ^ n * R⁻¹ * M) = (R * R⁻¹) * (M * R⁻¹ ^ n) := by ring
    _ = _ := by rw [hi, one_mul]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Complex
namespace AVRegularity.CycleWords

/-! Complex continuous linear readouts commute with genuine circle integrals. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [CompleteSpace E] [CompleteSpace F]

theorem complexLinearMap_circleIntegral (A : E →L[ℂ] F) (f : ℂ → E)
    (c : ℂ) (R : ℝ) (hf : CircleIntegrable f c R) :
    A (∮ z in C(c, R), f z) = ∮ z in C(c, R), A (f z) := by
  unfold circleIntegral
  calc
    _ = ∫ θ : ℝ in 0..2 * Real.pi, A (deriv (circleMap c R) θ • f (circleMap c R θ)) :=
      (A.intervalIntegral_comp_comm hf.out).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro θ _
      exact A.map_smul (deriv (circleMap c R) θ) (f (circleMap c R θ))

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Set Filter Topology
namespace AVRegularity.CycleWords

/-! Local complex directional jets agree with jets of the corresponding complex line. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem complexLinearLine_iteratedFDeriv (f : E → F) (Ω : Set E) (hΩ : IsOpen Ω)
    (hf : ContDiffOn ℂ (⊤ : ℕ∞) f Ω) (h0 : (0 : E) ∈ Ω) (ν : E) (n : ℕ) :
    iteratedFDeriv ℂ n (fun z : ℂ => f (z • ν)) 0 (fun _ => 1) =
      iteratedFDeriv ℂ n f 0 (fun _ => ν) := by
  let A : ℂ →L[ℂ] E := (ContinuousLinearMap.id ℂ ℂ).smulRight ν
  have hA : IsOpen (A ⁻¹' Ω) := hΩ.preimage A.continuous
  have hx : A (0 : ℂ) ∈ Ω := by simpa only [map_zero] using h0
  have hh := A.iteratedFDerivWithin_comp_right hf hΩ.uniqueDiffOn hA.uniqueDiffOn hx
    (show (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by simp)
  rw [iteratedFDerivWithin_of_isOpen n hA hx,
    iteratedFDerivWithin_of_isOpen n hΩ hx] at hh
  have he := congrArg (fun T => T (fun _ => (1 : ℂ))) hh
  simpa only [Function.comp_def, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    A, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply, one_smul, zero_smul] using he

end AVRegularity.CycleWords
end
end

section
@[expose] public section
namespace AVRegularity.CycleWords

/-! Scalar transport of reciprocal overlap normalizations. -/

theorem complex_normalization_transport (k₀ k₁ d₀ d₁ p q : ℂ)
    (h₀ : k₀ * d₀ = 1) (h₁ : k₁ * d₁ = 1) (hp : p * d₁ = q * d₀) :
    p * k₀ = q * k₁ := by
  calc
    p * k₀ = p * k₀ * (k₁ * d₁) := by rw [h₁, mul_one]
    _ = k₀ * k₁ * (p * d₁) := by ring
    _ = k₀ * k₁ * (q * d₀) := by rw [hp]
    _ = q * k₁ * (k₀ * d₀) := by ring
    _ = q * k₁ := by rw [h₀, mul_one]

end AVRegularity.CycleWords
end
end

section
public section
namespace AVRegularity.CycleWords

/-! Differences of the actual normalization reciprocals. -/

theorem complexReciprocal_difference (a b k l : ℂ)
    (hk : (1 + a) * k = 1) (hl : (1 + b) * l = 1) :
    k - l = k * l * (b - a) := by
  calc
    k - l = k * ((1 + b) * l) - ((1 + a) * k) * l := by rw [hk, hl]; ring
    _ = _ := by ring

theorem complexReciprocal_difference_norm (a b k l : ℂ)
    (hk : (1 + a) * k = 1) (hl : (1 + b) * l = 1)
    (hkn : ‖k‖ ≤ 2) (hln : ‖l‖ ≤ 2) :
    ‖k - l‖ ≤ 4 * ‖a - b‖ := by
  rw [complexReciprocal_difference a b k l hk hl, norm_mul, norm_mul,
    norm_sub_rev b a]
  have hprod : ‖k‖ * ‖l‖ ≤ 4 := by
    calc
      _ ≤ 2 * 2 := mul_le_mul hkn hln (norm_nonneg _) (by norm_num)
      _ = 4 := by norm_num
  exact mul_le_mul_of_nonneg_right hprod (norm_nonneg _)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Complex Metric
namespace AVRegularity.CycleWords

/-! Cauchy's estimate controls every coefficient of a finite vector polynomial without a Vandermonde price. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem complexVectorPolynomial_coefficient_norm_le (N : ℕ) (u : ℕ → E)
    (R M : ℝ) (hR : 0 < R)
    (hb : ∀ z ∈ sphere (0 : ℂ) R, ‖∑ j ∈ Finset.range N, z ^ j • u j‖ ≤ M)
    (i : ℕ) (hi : i < N) : ‖u i‖ ≤ M / R ^ i := by
  let f := fun z : ℂ => ∑ j ∈ Finset.range N, z ^ j • u j
  have hf : ContDiff ℂ (⊤ : ℕ∞) f := by
    apply ContDiff.sum
    intro j _
    fun_prop
  have hd : iteratedDeriv i f 0 = (i.factorial : ℂ) • u i := by
    dsimp only [f]
    simp (disch := fun_prop) only [iteratedDeriv_fun_sum, iteratedDeriv_smul_const,
      iteratedDeriv_fun_pow_zero]
    simp [ite_smul, Finset.sum_ite_eq_of_mem _ _ _ (Finset.mem_range.mpr hi)]
  have hc := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le i hR
    (hf.differentiable (by simp)).diffContOnCl hb
  rw [hd, norm_smul, Complex.norm_natCast] at hc
  have hfac : (0 : ℝ) < i.factorial := by exact_mod_cast i.factorial_pos
  apply (mul_le_mul_iff_right₀ hfac).mp
  simpa only [div_eq_mul_inv, mul_assoc] using hc

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
namespace AVRegularity.CycleWords

/-! A continuous time energy attains a value no larger than its integral average. -/

theorem exists_energy_le_integral_average (f : ℝ → ℝ) (a b C : ℝ)
    (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hi : (∫ t in a..b, f t) ≤ (b - a) * C) :
    ∃ t ∈ Icc a b, f t ≤ C := by
  by_contra hn
  push Not at hn
  have hs := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hab
    (f := fun _ => C) (g := f) continuousOn_const hf
    (fun t ht => (hn t ⟨ht.1.le, ht.2⟩).le)
    ⟨a, ⟨le_rfl, hab.le⟩, hn a ⟨le_rfl, hab.le⟩⟩
  rw [intervalIntegral.integral_const, smul_eq_mul] at hs
  exact (not_lt_of_ge hi) hs

end AVRegularity.CycleWords
end
end

section
public section
open Set
namespace AVRegularity.CycleWords

/-! Closing the endpoint of a nonempty quiet time interval by continuity. -/

theorem continuous_quiet_interval {E : Type*} [TopologicalSpace E] [T2Space E] [Zero E]
    (f : ℝ → E) (hf : Continuous f) (a D : ℝ) (hD : 0 < D)
    (hq : ∀ t ∈ Ico (a - D) a, f t = 0) :
    ∀ t ∈ Icc (a - D) a, f t = 0 := by
  have he : EqOn f (fun _ => (0 : E)) (Ico (a - D) a) := hq
  have hc := he.closure hf continuous_const
  rw [closure_Ico (by linarith only [hD] : a - D ≠ a)] at hc
  exact hc

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory UnitAddTorus
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Continuous torus symbols have genuine bounded linear pullbacks to L infinity. -/

local instance continuousTorusSymbolLInfinityMeasure : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

variable {X : Type*} [MeasurableSpace X]

theorem continuousTorusSymbolPullback_memLp (μ : Measure X)
    (q : X → UnitAddTorus (Fin 2)) (hq : Measurable q)
    (b : C(UnitAddTorus (Fin 2), ℂ)) : MemLp (fun x => b (q x)) ∞ μ :=
  memLp_top_of_bound (b.continuous.measurable.comp hq).aestronglyMeasurable ‖b‖
    (Filter.Eventually.of_forall (fun x => b.norm_coe_le_norm (q x)))

def continuousTorusSymbolPullback (μ : Measure X)
    (q : X → UnitAddTorus (Fin 2)) (hq : Measurable q)
    (b : C(UnitAddTorus (Fin 2), ℂ)) : Lp ℂ ∞ μ :=
  (continuousTorusSymbolPullback_memLp μ q hq b).toLp (fun x => b (q x))

theorem continuousTorusSymbolPullback_ae (μ : Measure X)
    (q : X → UnitAddTorus (Fin 2)) (hq : Measurable q)
    (b : C(UnitAddTorus (Fin 2), ℂ)) :
    continuousTorusSymbolPullback μ q hq b =ᵐ[μ] fun x => b (q x) :=
  (continuousTorusSymbolPullback_memLp μ q hq b).coeFn_toLp

theorem continuousTorusSymbolPullback_add (μ : Measure X)
    (q : X → UnitAddTorus (Fin 2)) (hq : Measurable q)
    (b c : C(UnitAddTorus (Fin 2), ℂ)) :
    continuousTorusSymbolPullback μ q hq (b + c) =
      continuousTorusSymbolPullback μ q hq b + continuousTorusSymbolPullback μ q hq c := by
  apply Lp.ext
  filter_upwards [continuousTorusSymbolPullback_ae μ q hq (b + c),
    continuousTorusSymbolPullback_ae μ q hq b, continuousTorusSymbolPullback_ae μ q hq c,
    Lp.coeFn_add (continuousTorusSymbolPullback μ q hq b) (continuousTorusSymbolPullback μ q hq c)]
    with x h₁ h₂ h₃ h₄
  change (continuousTorusSymbolPullback μ q hq b + continuousTorusSymbolPullback μ q hq c) x =
    continuousTorusSymbolPullback μ q hq b x + continuousTorusSymbolPullback μ q hq c x at h₄
  rw [h₁, h₄, h₂, h₃, ContinuousMap.add_apply]

theorem continuousTorusSymbolPullback_smul (μ : Measure X)
    (q : X → UnitAddTorus (Fin 2)) (hq : Measurable q)
    (c : ℂ) (b : C(UnitAddTorus (Fin 2), ℂ)) :
    continuousTorusSymbolPullback μ q hq (c • b) = c • continuousTorusSymbolPullback μ q hq b := by
  apply Lp.ext
  filter_upwards [continuousTorusSymbolPullback_ae μ q hq (c • b),
    continuousTorusSymbolPullback_ae μ q hq b, Lp.coeFn_smul c (continuousTorusSymbolPullback μ q hq b)]
    with x h₁ h₂ h₃
  change (c • continuousTorusSymbolPullback μ q hq b) x =
    c • continuousTorusSymbolPullback μ q hq b x at h₃
  rw [h₁, h₃, h₂, ContinuousMap.smul_apply]

theorem continuousTorusSymbolPullback_norm_le (μ : Measure X)
    (q : X → UnitAddTorus (Fin 2)) (hq : Measurable q)
    (b : C(UnitAddTorus (Fin 2), ℂ)) : ‖continuousTorusSymbolPullback μ q hq b‖ ≤ ‖b‖ := by
  rw [Lp.norm_def]
  have hbound : eLpNorm (continuousTorusSymbolPullback μ q hq b) ∞ μ ≤ ENNReal.ofReal ‖b‖ := by
    rw [eLpNorm_exponent_top (Lp.aestronglyMeasurable _)]
    apply eLpNormEssSup_le_of_ae_bound
    filter_upwards [continuousTorusSymbolPullback_ae μ q hq b] with x hx
    rw [hx]
    exact b.norm_coe_le_norm (q x)
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq
    (ENNReal.toReal_ofReal (norm_nonneg _))

def continuousTorusSymbolPullbackCLM (μ : Measure X)
    (q : X → UnitAddTorus (Fin 2)) (hq : Measurable q) :
    C(UnitAddTorus (Fin 2), ℂ) →L[ℂ] Lp ℂ ∞ μ :=
  ({ toFun := continuousTorusSymbolPullback μ q hq
     map_add' := continuousTorusSymbolPullback_add μ q hq
     map_smul' := continuousTorusSymbolPullback_smul μ q hq } :
    C(UnitAddTorus (Fin 2), ℂ) →ₗ[ℂ] Lp ℂ ∞ μ).mkContinuous 1 (fun b => by
      change ‖continuousTorusSymbolPullback μ q hq b‖ ≤ 1 * ‖b‖
      rw [one_mul]
      exact continuousTorusSymbolPullback_norm_le μ q hq b)

end AVRegularity.CycleWords
end
end

section
@[expose] public section
open MeasureTheory Filter
open scoped Topology
namespace AVRegularity.CycleWords

/-! Remove bounded approximating tests from a measurable weak dual time pairing. -/

theorem tendsto_contractive_test_time_pairing
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {s t : ℝ} (hst : s ≤ t) (f : ℝ → H)
    (hf : IntervalIntegrable f volume s t) (z : H) (Z : ℕ → H)
    (hZ : ∀ N, ‖Z N‖ ≤ ‖z‖) (hlim : Tendsto Z atTop (𝓝 z)) :
    Tendsto (fun N => ∫ r in s..t, inner ℝ (f r) (Z N)) atTop
      (𝓝 (∫ r in s..t, inner ℝ (f r) z)) := by
  simp only [intervalIntegral.integral_of_le hst]
  apply tendsto_integral_of_dominated_convergence (fun r => ‖f r‖ * ‖z‖)
  · intro N
    exact hf.1.aestronglyMeasurable.inner aestronglyMeasurable_const
  · exact hf.1.norm.mul_const ‖z‖
  · intro N
    exact Eventually.of_forall (fun r => (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hZ N) (norm_nonneg (f r))))
  · exact Eventually.of_forall (fun r => tendsto_const_nhds.inner (𝕜 := ℝ) hlim)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleWords

/-! Coordinate affine additions have the exact expected gradient and Laplacian. -/

theorem coordinate_add_gradient (c : ℝ) (f : Vec 2 → ℝ) (hf : Differentiable ℝ f)
    (j i : Fin 2) (y : Vec 2) :
    fderiv ℝ (fun z => z j + c * f z) y (basisVec i) =
      (if i = j then 1 else 0) + c * fderiv ℝ f y (basisVec i) := by
  rw [fderiv_fun_add (differentiableAt_apply j y) ((hf y).const_mul c),
    fderiv_const_mul (hf y), (hasFDerivAt_apply (𝕜 := ℝ) j y).fderiv]
  simp [basisVec]
  fin_cases i <;> fin_cases j <;> rfl

theorem coordinate_add_secondDerivative (c : ℝ) (f : Vec 2 → ℝ) (hf : ContDiff ℝ 2 f)
    (j i : Fin 2) (y : Vec 2) :
    fderiv ℝ (fun z => fderiv ℝ (fun x => x j + c * f x) z (basisVec i)) y (basisVec i) =
      c * fderiv ℝ (fun z => fderiv ℝ f z (basisVec i)) y (basisVec i) := by
  have he := funext (coordinate_add_gradient c f (hf.differentiable (by norm_num)) j i)
  rw [he]
  have hd : Differentiable ℝ (fun z => fderiv ℝ f z (basisVec i)) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) |>.clm_apply (differentiable_const _)
  rw [fderiv_const_add, fderiv_const_mul (hd y)]
  simp

theorem coordinate_add_laplacian (c : ℝ) (f : Vec 2 → ℝ) (hf : ContDiff ℝ 2 f)
    (j : Fin 2) (y : Vec 2) :
    (∑ i : Fin 2, fderiv ℝ (fun z => fderiv ℝ (fun x => x j + c * f x) z (basisVec i))
      y (basisVec i)) = c * ∑ i : Fin 2,
        fderiv ℝ (fun z => fderiv ℝ f z (basisVec i)) y (basisVec i) := by
  simp_rw [coordinate_add_secondDerivative c f hf j]
  exact (Finset.mul_sum _ _ _).symm

end AVRegularity.CycleWords
end
end

section
public section
namespace AVRegularity.CycleWords

/-! Low correction forcing preserves the frequency-square scale on the unit disc. -/

theorem correction_source_growth_algebra (C L r n s k : ℝ)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hn : 0 ≤ n) (hs : 0 ≤ s) (hsmall : C * r ≤ 1)
    (hk : k ≤ L * r ^ 2)
    (h : s ≤ C * r * n + (C * r + k + 8 * r ^ 2)) :
    s ^ 2 ≤ 2 * n ^ 2 + 2 * (C + L + 8) ^ 2 * r ^ 2 := by
  have hrr : r ^ 2 ≤ r := by
    simpa only [pow_two, mul_one] using mul_le_mul_of_nonneg_left hr1 hr
  have hl := mul_le_mul_of_nonneg_left hrr hL
  have h8 := mul_le_mul_of_nonneg_left hrr (by norm_num : (0 : ℝ) ≤ 8)
  have hCn := mul_le_mul_of_nonneg_right hsmall hn
  have hbound : s ≤ n + (C + L + 8) * r := by
    linarith only [h, hk, hl, h8, hCn]
  have he : 0 ≤ n + (C + L + 8) * r :=
    add_nonneg hn (mul_nonneg (by linarith only [hC, hL]) hr)
  have hsq := (sq_le_sq₀ hs he).2 hbound
  have hcross := sq_nonneg (n - (C + L + 8) * r)
  nlinarith only [hsq, hcross]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! A finite-depth graph admits a dimension-free majorant without smallness of its edge price. -/

variable {ι : Type*} [Fintype ι]

def ennGraphMajorant (b : ι → ι → ℝ≥0∞) (A : ℝ≥0∞) (d : ι → ℝ≥0∞) : ℕ → ι → ℝ≥0∞
  | 0 => d
  | n + 1 => fun v => d v + A * ∑ u, b v u * ennGraphMajorant b A d n u

theorem ennRank_energy_le_majorant (rank : ι → ℕ) (b : ι → ι → ℝ≥0∞)
    (hsupport : ∀ v u, b v u ≠ 0 → rank u < rank v)
    (A : ℝ≥0∞) (e d : ι → ℝ≥0∞)
    (henergy : ∀ v, e v ≤ d v + A * ∑ u, b v u * e u) :
    ∀ n v, rank v ≤ n → e v ≤ ennGraphMajorant b A d n v := by
  intro n
  induction n with
  | zero =>
    intro v hv
    have hz : ∑ u, b v u * e u = 0 := by
      apply Finset.sum_eq_zero
      intro u _
      have hzero : b v u = 0 := by
        by_contra hh
        have hs := hsupport v u hh
        omega
      rw [hzero, zero_mul]
    simpa only [hz, mul_zero, add_zero, ennGraphMajorant] using henergy v
  | succ n ih =>
    intro v hv
    apply (henergy v).trans
    change d v + A * ∑ u, b v u * e u ≤ d v + A * ∑ u, b v u * ennGraphMajorant b A d n u
    apply add_le_add le_rfl
    apply mul_le_mul_right
    apply Finset.sum_le_sum
    intro u _
    by_cases hz : b v u = 0
    · simp only [hz, zero_mul, le_refl]
    · exact mul_le_mul_right (ih u (by have hs := hsupport v u hz; omega)) _


theorem ennGraphMajorant_sum_le (b : ι → ι → ℝ≥0∞)
    (hcol : ∀ u, ∑ v, b v u ≤ 1) (A : ℝ≥0∞) (d : ι → ℝ≥0∞) (n : ℕ) :
    (∑ v, ennGraphMajorant b A d n v) ≤ (1 + A) ^ n * ∑ v, d v := by
  induction n with
  | zero => simp only [ennGraphMajorant, pow_zero, one_mul, le_refl]
  | succ n ih =>
    have hs : (∑ v, ∑ u, b v u * ennGraphMajorant b A d n u) ≤
        ∑ u, ennGraphMajorant b A d n u := by
      rw [Finset.sum_comm]
      apply Finset.sum_le_sum
      intro u _
      rw [← Finset.sum_mul]
      simpa only [one_mul] using mul_le_mul_left (hcol u) (ennGraphMajorant b A d n u)
    have hp : (1 : ℝ≥0∞) ≤ (1 + A) ^ n := one_le_pow₀ (by exact le_self_add)
    calc
      _ = (∑ v, d v) + A * ∑ v, ∑ u, b v u * ennGraphMajorant b A d n u := by
        simp only [ennGraphMajorant, Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ (∑ v, d v) + A * ((1 + A) ^ n * ∑ v, d v) :=
        add_le_add le_rfl (mul_le_mul_right (hs.trans ih) A)
      _ ≤ (1 + A) ^ n * (∑ v, d v) + A * ((1 + A) ^ n * ∑ v, d v) :=
        add_le_add (by simpa only [one_mul] using mul_le_mul_left hp (∑ v, d v)) le_rfl
      _ = (1 + A) ^ (n + 1) * ∑ v, d v := by rw [pow_succ]; ring

theorem ennRank_energy_sum_le (rank : ι → ℕ) (H : ℕ) (hrank : ∀ v, rank v ≤ H)
    (b : ι → ι → ℝ≥0∞) (hcol : ∀ u, ∑ v, b v u ≤ 1)
    (hsupport : ∀ v u, b v u ≠ 0 → rank u < rank v)
    (A : ℝ≥0∞) (e d : ι → ℝ≥0∞)
    (henergy : ∀ v, e v ≤ d v + A * ∑ u, b v u * e u) :
    (∑ v, e v) ≤ (1 + A) ^ H * ∑ v, d v := by
  apply (Finset.sum_le_sum (fun v _ =>
    ennRank_energy_le_majorant rank b hsupport A e d henergy H v (hrank v))).trans
  exact ennGraphMajorant_sum_le b hcol A d H

end AVRegularity.CycleWords
end
end

section
@[expose] public section
namespace AVRegularity.CycleWords

/-! Pure real algebra for the adjoint shear displacement and gradient budgets. -/

theorem squared_one_add_le (x : ℝ) : (1 + x) ^ 2 ≤ 2 * (1 + x ^ 2) := by
  nlinarith only [sq_nonneg (x - 1)]

theorem enhanced_shear_gradient_budget {ν a B C : ℝ} (hν : 0 < ν)
    (he : ν + a ^ 2 / ν ≤ C * B) :
    ν * (1 + a / ν) ^ 2 ≤ 2 * C * B := by
  have hh := mul_le_mul_of_nonneg_left (squared_one_add_le (a / ν)) hν.le
  have hi : ν * (2 * (1 + (a / ν) ^ 2)) = 2 * (ν + a ^ 2 / ν) := by
    field_simp
  rw [hi] at hh
  exact hh.trans (by linarith only [he])

theorem enhanced_shear_displacement_budget {e ν a B C : ℝ}
    (he : 0 < e) (hν : 0 < ν) (_ha : 0 ≤ a) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hen : ν + a ^ 2 / ν ≤ C * B) :
    ((2 * Real.pi * a / e) / (4 * Real.pi ^ 2 * ν / e ^ 2)) ^ 2 ≤ C * B * (e ^ 2 / ν) := by
  have hpi : 1 ≤ 4 * Real.pi ^ 2 := by nlinarith only [Real.pi_gt_three]
  have hi : ((2 * Real.pi * a / e) / (4 * Real.pi ^ 2 * ν / e ^ 2)) ^ 2 =
      (a ^ 2 / ν) * (e ^ 2 / ν) / (4 * Real.pi ^ 2) := by
    field_simp
    ring
  rw [hi]
  have hh : a ^ 2 / ν ≤ C * B := by linarith only [hen, hν]
  calc
    _ ≤ (C * B * (e ^ 2 / ν)) / (4 * Real.pi ^ 2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hh (by positivity)) (by positivity)
    _ ≤ _ := (div_le_iff₀ (by positivity : 0 < 4 * Real.pi ^ 2)).mpr
      (by nlinarith only [hpi, mul_nonneg (mul_nonneg hC hB) (div_nonneg (sq_nonneg e) hν.le)])

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
namespace AVRegularity.CycleWords

/-! An integrating-factor estimate gives propagation and unweighted dissipation on a short window. -/

theorem exponentialWindow_energy_extraction (E D : ℝ → ℝ) (a b A : ℝ)
    (hab : a ≤ b) (hA : 0 ≤ A) (hD : ContinuousOn D (Icc a b))
    (hDn : ∀ t ∈ Icc a b, 0 ≤ D t) (hEb : 0 ≤ E b)
    (he : Real.exp (-A * (b - a)) * E b +
      (∫ t in a..b, Real.exp (-A * (t - a)) * D t) ≤ E a) :
    E b ≤ Real.exp (A * (b - a)) * E a ∧
      (∫ t in a..b, D t) ≤ Real.exp (A * (b - a)) * E a := by
  let w := fun t : ℝ => Real.exp (-A * (t - a))
  have hw : Continuous w := Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const))
  have hDi : IntervalIntegrable D volume a b := hD.intervalIntegrable_of_Icc hab
  have hWi : IntervalIntegrable (fun t => w t * D t) volume a b :=
    (hw.continuousOn.mul hD).intervalIntegrable_of_Icc hab
  have hI : 0 ≤ ∫ t in a..b, w t * D t :=
    intervalIntegral.integral_nonneg hab (fun t ht => mul_nonneg (Real.exp_pos _).le (hDn t ht))
  have hWb : 0 ≤ Real.exp (-A * (b - a)) * E b := mul_nonneg (Real.exp_pos _).le hEb
  have hlow : Real.exp (-A * (b - a)) * (∫ t in a..b, D t) ≤ ∫ t in a..b, w t * D t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hab (hDi.const_mul _) hWi
    intro t ht
    apply mul_le_mul_of_nonneg_right _ (hDn t ht)
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left ht.2 hA
    linarith
  have hcancel : Real.exp (A * (b - a)) * Real.exp (-A * (b - a)) = 1 := by
    rw [← Real.exp_add]
    rw [show A * (b - a) + -A * (b - a) = 0 by ring, Real.exp_zero]
  constructor
  · have hh : Real.exp (-A * (b - a)) * E b ≤ E a := by
      change Real.exp (-A * (b - a)) * E b + (∫ t in a..b, w t * D t) ≤ E a at he
      linarith
    have hm := mul_le_mul_of_nonneg_left hh (Real.exp_pos (A * (b - a))).le
    simpa only [← mul_assoc, hcancel, one_mul] using hm
  · have hh : Real.exp (-A * (b - a)) * (∫ t in a..b, D t) ≤ E a := by
      change Real.exp (-A * (b - a)) * E b + (∫ t in a..b, w t * D t) ≤ E a at he
      linarith
    have hm := mul_le_mul_of_nonneg_left hh (Real.exp_pos (A * (b - a))).le
    simpa only [← mul_assoc, hcancel, one_mul] using hm

theorem exponentialWindow_short_energy_budget (E D : ℝ → ℝ) (a b A : ℝ)
    (hab : a ≤ b) (hA : 0 ≤ A) (hD : ContinuousOn D (Icc a b))
    (hDn : ∀ t ∈ Icc a b, 0 ≤ D t) (hEa : 0 ≤ E a) (hEb : 0 ≤ E b)
    (hshort : A * (b - a) ≤ 1)
    (he : Real.exp (-A * (b - a)) * E b +
      (∫ t in a..b, Real.exp (-A * (t - a)) * D t) ≤ E a) :
    E b ≤ Real.exp 1 * E a ∧ (∫ t in a..b, D t) ≤ Real.exp 1 * E a := by
  obtain ⟨hE, hI⟩ := exponentialWindow_energy_extraction E D a b A hab hA hD hDn hEb he
  have hp := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hshort) hEa
  exact ⟨hE.trans hp, hI.trans hp⟩

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleWords

/-! The finite derivative budget for a renewal pullback uses the actual inner-map derivatives. -/

section
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem iteratedFDeriv_composition_norm_le {n : ℕ} {f : E → F} {g : F → G} {x : E}
    (hg : ContDiffAt ℝ n g (f x)) (hf : ContDiffAt ℝ n f x) :
    ‖iteratedFDeriv ℝ n (g ∘ f) x‖ ≤
      ∑ c : OrderedFinpartition n, ‖iteratedFDeriv ℝ c.length g (f x)‖ *
        ∏ i : Fin c.length, ‖iteratedFDeriv ℝ (c.partSize i) f x‖ := by
  rw [AVenhance.FaaDiBruno.multivariateFaaDiBruno hg hf]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro c _
  simpa only [FormalMultilinearSeries.compAlongOrderedFinpartition, ftaylorSeries] using
    c.norm_compAlongOrderedFinpartition_le (ftaylorSeries ℝ g (f x) c.length)
      (fun i => ftaylorSeries ℝ f x (c.partSize i))
end

/-! A finite nonnegative graph with a uniform row and column budget can be
normalized without introducing its cardinality into the constants. -/

section
variable {ι : Type*} [Fintype ι]

def normalizedFiniteGraph (θ : ℝ) (p : ι → ι → ℝ) (v u : ι) : ℝ := p v u / (1 + θ)

theorem normalizedFiniteGraph_budget (θ : ℝ) (hθ : 0 ≤ θ) (p : ι → ι → ℝ)
    (hp : ∀ v u, 0 ≤ p v u) (hrow : ∀ v, ∑ u, p v u ≤ θ)
    (hcol : ∀ u, ∑ v, p v u ≤ θ) :
    (∀ v u, 0 ≤ normalizedFiniteGraph θ p v u) ∧
    (∀ v, ∑ u, normalizedFiniteGraph θ p v u ≤ 1) ∧
    (∀ u, ∑ v, normalizedFiniteGraph θ p v u ≤ 1) := by
  have ht : 0 < 1 + θ := by linarith
  refine ⟨fun v u => div_nonneg (hp v u) ht.le, ?_, ?_⟩
  · intro v
    simp only [normalizedFiniteGraph, ← Finset.sum_div]
    exact (div_le_one ht).mpr ((hrow v).trans (by linarith))
  · intro u
    simp only [normalizedFiniteGraph, ← Finset.sum_div]
    exact (div_le_one ht).mpr ((hcol u).trans (by linarith))

omit [Fintype ι] in
theorem normalizedFiniteGraph_support (θ : ℝ) (p : ι → ι → ℝ) (rank : ι → ℕ)
    (hs : ∀ v u, p v u ≠ 0 → rank u < rank v) :
    ∀ v u, normalizedFiniteGraph θ p v u ≠ 0 → rank u < rank v := by
  intro v u h
  apply hs v u
  intro hz
  exact h (by simp only [normalizedFiniteGraph, hz, zero_div])
end

end AVRegularity.CycleWords
end
end

section
@[expose] public section
namespace AVRegularity.CycleWords

/-! Sum positive stored-word growth bounds before taking time integrals. -/

theorem finite_weighted_rate_sum {ι : Type*} [Fintype ι]
    (c x : ι → ℝ) (a : ℝ) :
    (∑ i, c i * (a * x i)) = a * ∑ i, c i * x i := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem finite_weighted_growth_sum {ι : Type*} [Fintype ι]
    (c P d e L u R : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (a b : ℝ)
    (h : ∀ i, P i + d i ≤ a * e i + 8 * L i + b * u i + 2 * R i) :
    (∑ i, c i * P i) + (∑ i, c i * d i) ≤
      a * (∑ i, c i * e i) + 8 * (∑ i, c i * L i) +
      b * (∑ i, c i * u i) + 2 * (∑ i, c i * R i) := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_left (h i) (hc i))
  simp_rw [mul_add, Finset.sum_add_distrib, finite_weighted_rate_sum] at hs
  exact hs

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleWords

/-! A simple finite Hilbert norm estimate used to sum the renewal component bounds. -/

theorem finiteHilbert_norm_le_sum {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)] (u : PiLp 2 E) : ‖u‖ ≤ ∑ i, ‖u i‖ := by
  classical
  have hu : u = ∑ i, PiLp.single 2 i (u i) := by
    ext i
    simp
  calc
    ‖u‖ = ‖∑ i, PiLp.single 2 i (u i)‖ := congrArg norm hu
    _ ≤ ∑ i, ‖PiLp.single 2 i (u i)‖ := norm_sum_le _ _
    _ = _ := by simp only [PiLp.norm_single]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Filter
open scoped Topology
namespace AVRegularity.CycleWords

/-! A single smoothing index suffices for finitely many convergent jet classes. -/

theorem exists_finite_diagonal_approximation {ι : Type*} [Finite ι]
    {E : ι → Type*} [∀ i, PseudoMetricSpace (E i)]
    (U : ℕ → ∀ i, E i) (V : ℕ → ℕ → ∀ i, E i) (u : ∀ i, E i)
    (hU : ∀ i, Tendsto (fun n => U n i) atTop (𝓝 (u i)))
    (hV : ∀ n i, Tendsto (fun m => V n m i) atTop (𝓝 (U n i))) :
    ∃ m : ℕ → ℕ, ∀ i, Tendsto (fun n => V n (m n) i) atTop (𝓝 (u i)) := by
  classical
  let ε : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have hε n : 0 < ε n := by dsimp [ε]; positivity
  have hs (n : ℕ) : ∃ m : ℕ, ∀ i, dist (U n i) (V n m i) < ε n := by
    have he : ∀ᶠ m : ℕ in atTop, ∀ i, dist (U n i) (V n m i) < ε n := by
      apply eventually_all.mpr
      intro i
      have hh := (hV n i).eventually (Metric.ball_mem_nhds (U n i) (hε n))
      simpa only [Metric.mem_ball, dist_comm] using hh
    exact he.exists
  choose m hm using hs
  refine ⟨m, ?_⟩
  intro i
  have he : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hd : Tendsto (fun n => dist (U n i) (V n (m n) i)) atTop (𝓝 0) :=
    squeeze_zero (fun _ => dist_nonneg) (fun n => (hm n i).le) he
  exact (hU i).congr_dist hd

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! A finite pointwise norm budget gives the corresponding L2 norm budget. -/

variable {A E F ι : Type*} [MeasurableSpace A] [NormedAddCommGroup E]
  [NormedAddCommGroup F] [Fintype ι]

theorem finite_Lp_norm_majorant (μ : Measure A) (f : A → E) (g : ι → A → F)
    (hf : MemLp f 2 μ) (hg : ∀ i, MemLp (g i) 2 μ)
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hb : ∀ᵐ x ∂μ, ‖f x‖ ≤ ∑ i, c i * ‖g i x‖) :
    ‖hf.toLp f‖ ≤ ∑ i, c i * ‖(hg i).toLp (g i)‖ := by
  let N i : Lp ℝ 2 μ := (hg i).norm.toLp (fun x => ‖g i x‖)
  let M : Lp ℝ 2 μ := ∑ i, c i • N i
  have hn i : ‖N i‖ = ‖(hg i).toLp (g i)‖ := by
    rw [Lp.norm_toLp, Lp.norm_toLp, eLpNorm_norm _ (hg i).aestronglyMeasurable]
  have hna : ∀ᵐ x ∂μ, ∀ i, N i x = ‖g i x‖ :=
    ae_all_iff.mpr (fun i => (hg i).norm.coeFn_toLp)
  have hma : M =ᵐ[μ] fun x => ∑ i, c i * ‖g i x‖ := by
    have hsum := (Lp.coeFn_finsetSum (Finset.univ : Finset ι) (fun i => c i • N i)).trans
      (eventuallyEq_sum (fun i _ => Lp.coeFn_smul (c i) (N i)))
    filter_upwards [hsum, hna] with x hx hn
    simpa only [M, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hn] using hx
  have hnorm : ‖hf.toLp f‖ ≤ ‖M‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hf.coeFn_toLp, hma, hb] with x hf hm hb
    rw [hf, hm, Real.norm_eq_abs]
    exact hb.trans (le_abs_self _)
  calc
    _ ≤ ‖M‖ := hnorm
    _ ≤ ∑ i, ‖c i • N i‖ := norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hc i), hn]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleWords

/-! One normalized row gives a linear recurrence for inverse mass squared energy. -/

variable {ι : Type*} [Fintype ι]

theorem finite_mass_row_square_le (π : ι → ℝ) (hπ : ∀ u, 0 < π u)
    (v : ι) (p : ι → ℝ) (hp : ∀ u, 0 ≤ p u) (θ : ℝ)
    (hrow : (∑ u, Real.sqrt (π u / π v) * p u) ≤ θ)
    (G : ι → ℝ) (hG : ∀ u, 0 ≤ G u) (D : ℝ)
    (hD : D ≤ (∑ u, p u * Real.sqrt (G u)) ^ 2) :
    (π v)⁻¹ * D ≤ θ * ∑ u, (Real.sqrt (π u / π v) * p u) * ((π u)⁻¹ * G u) := by
  classical
  let q := fun u => Real.sqrt (π u / π v) * p u
  let x := fun u => (Real.sqrt (π u))⁻¹ * Real.sqrt (G u)
  have hq (u : ι) : 0 ≤ q u := mul_nonneg (Real.sqrt_nonneg _) (hp u)
  have hx (u : ι) : x u ^ 2 = (π u)⁻¹ * G u := by
    dsimp [x]
    rw [mul_pow, inv_pow, Real.sq_sqrt (hπ u).le, Real.sq_sqrt (hG u)]
  have hsum : (∑ u, q u * x u) =
      (Real.sqrt (π v))⁻¹ * ∑ u, p u * Real.sqrt (G u) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    dsimp [q, x]
    rw [Real.sqrt_div (hπ u).le]
    field_simp [(Real.sqrt_pos.mpr (hπ u)).ne', (Real.sqrt_pos.mpr (hπ v)).ne']
  have hcs : (∑ u, q u * x u) ^ 2 ≤ (∑ u, q u) * ∑ u, q u * x u ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (fun u _ => hq u) (fun u _ => mul_nonneg (hq u) (sq_nonneg _))
    intro u _
    exact le_of_eq (by ring)
  have ht : (∑ u, q u) * (∑ u, q u * x u ^ 2) ≤
      θ * ∑ u, q u * x u ^ 2 :=
    mul_le_mul_of_nonneg_right hrow
      (Finset.sum_nonneg (s := Finset.univ) (fun u _ => mul_nonneg (hq u) (sq_nonneg _)))
  have hh := hcs.trans ht
  rw [hsum, mul_pow, inv_pow, Real.sq_sqrt (hπ v).le] at hh
  simp_rw [hx] at hh
  exact (mul_le_mul_of_nonneg_left hD (inv_nonneg.mpr (hπ v).le)).trans hh

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleWords

/-! Finite operator time measurability follows from genuine basis images. -/

section
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def finiteOperatorBasisRank (b : Module.Basis ι ℝ H) (i j : ι) : H →L[ℝ] H :=
  (b.coord j).toContinuousLinearMap.smulRight (b i)

theorem finiteOperator_eq_basis_sum (b : Module.Basis ι ℝ H) (A : H →L[ℝ] H) :
    A = ∑ i, ∑ j, b.coord i (A (b j)) • finiteOperatorBasisRank b i j := by
  have he : A.toLinearMap = (∑ i, ∑ j, b.coord i (A (b j)) • finiteOperatorBasisRank b i j).toLinearMap := by
    apply b.ext
    intro k
    simp only [ContinuousLinearMap.toLinearMap_sum, ContinuousLinearMap.toLinearMap_smul,
      LinearMap.sum_apply, LinearMap.smul_apply, finiteOperatorBasisRank]
    change A (b k) = ∑ i, ∑ j, b.coord i (A (b j)) • (b.coord j (b k) • b i)
    have hcoord (j : ι) : b.coord j (b k) = if k = j then 1 else 0 := by
      change (b.repr (b k)) j = _
      rw [b.repr_self]
      exact Finsupp.single_apply
    simp [hcoord]
  exact ContinuousLinearMap.ext (fun x => congrArg (fun L : H →ₗ[ℝ] H => L x) he)

theorem finiteOperator_aestronglyMeasurable (b : Module.Basis ι ℝ H)
    (A : ℝ → H →L[ℝ] H) (μ : Measure ℝ)
    (hA : ∀ i, AEStronglyMeasurable (fun t => A t (b i)) μ) :
    AEStronglyMeasurable A μ := by
  have hs : AEStronglyMeasurable (fun t => ∑ i, ∑ j,
      b.coord i (A t (b j)) • finiteOperatorBasisRank b i j) μ := by
    apply AVenhance.Infra.Parabolic.FourierGalerkin.MatrixOperator.aestronglyMeasurable_finset_sum
    intro i _
    apply AVenhance.Infra.Parabolic.FourierGalerkin.MatrixOperator.aestronglyMeasurable_finset_sum
    intro j _
    exact ((b.coord i).toContinuousLinearMap.continuous.comp_aestronglyMeasurable (hA j)).smul
      aestronglyMeasurable_const
  exact hs.congr (Filter.Eventually.of_forall fun t => (finiteOperator_eq_basis_sum b (A t)).symm)
end

/-! Finite Hilbert products of genuine strongly measurable coordinate fields. -/

section
variable {A I F : Type*} [MeasurableSpace A] [Fintype I] [DecidableEq I]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {μ : Measure A}

theorem finitePiLp_aestronglyMeasurable (f : A → PiLp 2 (fun _ : I => F))
    (hf : ∀ i, AEStronglyMeasurable (fun x => f x i) μ) :
    AEStronglyMeasurable f μ := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => F)
  have hc (i : I) : Continuous (fun z : F => e.symm (Pi.single i z)) := by
    apply e.symm.continuous.comp
    apply continuous_pi
    intro j
    by_cases h : j = i
    · subst j
      have he : (fun z : F => (Pi.single i z : I → F) i) = (id : F → F) := by
        funext z
        simp only [Pi.single_eq_same, id_eq]
      rw [he]
      exact continuous_id
    · simpa only [Pi.single_eq_of_ne h] using (continuous_const : Continuous (fun _ : F => (0 : F)))
  have hm : AEStronglyMeasurable
      (fun x => ∑ i : I, e.symm (Pi.single i (f x i))) μ := by
    simpa only [Finset.sum_fn] using Finset.univ.aestronglyMeasurable_sum
      (fun i _ => (hc i).comp_aestronglyMeasurable (hf i))
  have he (x : A) : f x = ∑ i : I, e.symm (Pi.single i (f x i)) := by
    apply e.injective
    rw [map_sum]
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    funext j
    change f x j = (∑ i : I, Pi.single i (f x i)) j
    simp only [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact hm.congr (Filter.Eventually.of_forall (fun x => (he x).symm))
end

end AVRegularity.CycleWords
end
end
