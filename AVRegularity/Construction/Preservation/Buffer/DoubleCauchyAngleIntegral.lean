-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Mathlib.Analysis.Fourier.AddCircle
import AVenhance.Infra.Flow.GradientDeviation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import AVenhance.Infra.Flow.VariationalEquation
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.Analysis.Calculus.DiffContOnCl
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.CauchyIntegral

section
@[expose] public noncomputable section
open Filter Metric
open scoped Topology
namespace AVRegularity.Construction.Preservation.Buffer

/-! Copy-adapt the existing bump localization, preserving germs on a compact set. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_compact_smooth_localization (K : Set E) (hK : IsCompact K)
    (f : E → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ∃ g : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
      ∀ x ∈ K, g =ᶠ[𝓝 x] f := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  let R := max C 0 + 1
  have hR : 0 < R := by dsimp [R]; positivity
  let β : ContDiffBump (0 : E) := ⟨R, R + 1, hR, by linarith⟩
  refine ⟨fun x => β x * f x, β.contDiff.mul hf, β.hasCompactSupport.mul_right, ?_⟩
  intro x hx
  have hball : x ∈ ball (0 : E) R := by
    rw [mem_ball, dist_zero_right]
    have hc : ‖x‖ ≤ C := by simpa only [id_eq] using hC x hx
    have hmax := le_max_left C 0
    dsimp [R]
    linarith
  filter_upwards [β.eventuallyEq_one_of_mem_ball hball] with y hy
  simp only [hy, Pi.one_apply, one_mul]

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Complex Metric
open scoped Real
namespace AVRegularity.Construction.Preservation.Buffer

/-! Two coordinate Cauchy formulas express the base-label dependence by bounded contour data. -/

theorem double_cauchy_representation
    (F : ℂ → ℂ → ℂ) (c₀ c₁ : ℂ) (R : ℝ) (hR : 0 < R)
    (h₀ : ∀ z ∈ closedBall c₁ R, DiffContOnCl ℂ (fun w => F w z) (ball c₀ R))
    (h₁ : ∀ w ∈ closedBall c₀ R, DiffContOnCl ℂ (F w) (ball c₁ R))
    (w z : ℂ) (hw : w ∈ ball c₀ R) (hz : z ∈ ball c₁ R) :
    F w z = (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      (∮ u in C(c₀, R), (u - w)⁻¹ • ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
        (∮ v in C(c₁, R), (v - z)⁻¹ • F u v))) := by
  have he := (h₀ z (ball_subset_closedBall hz)).two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw
  rw [← he]
  congr 1
  apply circleIntegral.integral_congr hR.le
  intro u hu
  dsimp only
  rw [(h₁ u (sphere_subset_closedBall hu)).two_pi_i_inv_smul_circleIntegral_sub_inv_smul hz]

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public section
namespace AVRegularity.Construction.Preservation.Buffer

/-! The drift smallness constants can be chosen before the represented jet order. -/

theorem drift_smallness_of_molecular_radius {ρ e a ν c A B : ℝ}
    (he : 0 < e) (ha : 0 < a) (hν : 0 ≤ ν) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hspace : ρ ≤ c * e) (htime : ρ ^ 2 ≤ c ^ 2 * (ν / a))
    (hgeom : B * c ≤ 1 / 2) (hstrain : A * B * c ^ 2 ≤ 1 / 8) :
    B * ρ / e ≤ 1 / 2 ∧ (A * a) * B * ρ ^ 2 ≤ ν / 8 := by
  constructor
  · apply (div_le_iff₀ he).mpr
    calc
      B * ρ ≤ B * (c * e) := mul_le_mul_of_nonneg_left hspace hB
      _ = (B * c) * e := by ring
      _ ≤ (1 / 2) * e := mul_le_mul_of_nonneg_right hgeom he.le
  · calc
      (A * a) * B * ρ ^ 2 ≤ (A * a) * B * (c ^ 2 * (ν / a)) :=
        mul_le_mul_of_nonneg_left htime (mul_nonneg (mul_nonneg hA ha.le) hB)
      _ = (A * B * c ^ 2) * ν := by
        field_simp [ha.ne']
      _ ≤ (1 / 8) * ν := mul_le_mul_of_nonneg_right hstrain hν
      _ = ν / 8 := by ring

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.Construction.Preservation.Buffer

/-! Choose one Fourier integer at the enhanced preparation scale without an unbounded gap. -/

theorem exists_fourier_integer_at_scale {C r : ℝ} (hC : 0 < C) (hr : 0 < r) :
    ∃ N : ℕ, 1 ≤ N ∧ C / r ≤ (N : ℝ) ∧ (N : ℝ) ≤ C / r + 1 := by
  let N := Nat.ceil (C / r)
  have hN : 0 < N := Nat.ceil_pos.mpr (div_pos hC hr)
  exact ⟨N, hN, Nat.le_ceil _, (Nat.ceil_lt_add_one (div_nonneg hC.le hr.le)).le⟩

/-! Absolute Fourier coefficient bounds control the continuous phase function pointwise. -/

section
open AddCircle

theorem continuous_phase_norm_le_fourier_norm_sum
    {T : ℝ} [Fact (0 < T)] (f : C(AddCircle T, ℂ))
    (hs : Summable (fun n : ℤ => ‖fourierCoeff f n‖)) :
    ‖f‖ ≤ ∑' n : ℤ, ‖fourierCoeff f n‖ := by
  have hh := hasSum_fourier_series_of_summable hs.of_norm
  have hsn : Summable (fun n : ℤ => ‖fourierCoeff f n • (fourier n : C(AddCircle T, ℂ))‖) := by
    simpa only [norm_smul, fourier_norm, mul_one] using hs
  calc
    ‖f‖ = ‖∑' n : ℤ, fourierCoeff f n • (fourier n : C(AddCircle T, ℂ))‖ :=
      congrArg norm hh.tsum_eq.symm
    _ ≤ ∑' n : ℤ, ‖fourierCoeff f n‖ := by
      simpa only [norm_smul, fourier_norm, mul_one] using norm_tsum_le_tsum_norm hsn
end

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Filter Set
open scoped Topology
namespace AVRegularity.Construction.Preservation.Buffer

/-! Real-slice identities continue to the connected complex carrier slice. -/

theorem holomorphic_eqOn_of_real_eq
    {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U) (h0 : (0 : ℂ) ∈ U)
    {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (he : ∀ r : ℝ, (r : ℂ) ∈ U → f r = g r) : EqOn f g U := by
  have hlim : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hu : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), (r : ℂ) ∈ U :=
    hlim.eventually (hU.mem_nhds h0)
  have hcl : (0 : ℂ) ∈ closure ({z : ℂ | f z = g z} \ {(0 : ℂ)}) := by
    apply mem_closure_of_tendsto hlim
    filter_upwards [hu, self_mem_nhdsWithin] with r hr hpos
    refine ⟨he r hr, ?_⟩
    simpa only [mem_singleton_iff, Complex.ofReal_eq_zero] using ne_of_gt hpos
  exact (hf.analyticOnNhd hU).eqOn_of_preconnected_of_mem_closure
    (hg.analyticOnNhd hU) hc h0 hcl

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.Construction.Preservation.Buffer

/-! Restriction to a parameter slice costs no norm factor for the product norm. -/

variable {P E V : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem joint_slice_iteratedFDeriv_norm_le
    (F : P × E → V) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (p : P) (x : E) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y => F (p, y)) x‖ ≤
      ‖iteratedFDeriv ℝ j F (p, x)‖ := by
  let L : E →L[ℝ] P × E := ContinuousLinearMap.inr ℝ P E
  let H : P × E → V := fun y => F ((p, 0) + y)
  have hH : ContDiff ℝ (⊤ : ℕ∞) H :=
    hF.comp (contDiff_const.add contDiff_id)
  have he : (fun y => F (p, y)) = H ∘ L := by
    funext y
    simp only [H, L, Function.comp_apply, ContinuousLinearMap.inr_apply,
      Prod.mk_add_mk, add_zero, zero_add]
  rw [he, L.iteratedFDeriv_comp_right hH x (by simp)]
  have hn := (iteratedFDeriv ℝ j H (L x)).norm_compContinuousLinearMap_le (fun _ => L)
  have hp : ‖L‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg L)
    (ContinuousLinearMap.norm_inr_le_one (𝕜 := ℝ) (E := P) (F := E))
  have hh : ‖iteratedFDeriv ℝ j H (L x)‖ = ‖iteratedFDeriv ℝ j F (p, x)‖ := by
    rw [show iteratedFDeriv ℝ j H (L x) =
      iteratedFDeriv ℝ j F ((p, 0) + L x) from iteratedFDeriv_comp_add_left j (p, 0) (L x)]
    simp only [L, ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add]
  apply (show ‖(iteratedFDeriv ℝ j H (L x)).compContinuousLinearMap (fun _ => L)‖ ≤
      ‖iteratedFDeriv ℝ j H (L x)‖ * ‖L‖ ^ j from by simpa using hn).trans
  exact (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans_eq (by rw [mul_one, hh])

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Filter Metric
open scoped Topology
namespace AVRegularity.Construction.Preservation.Buffer

/-! Localize contour parameters without changing any derivative near the center. -/

theorem exists_smooth_bounded_local_identity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (R : ℝ) (hR : 0 < R) :
    ∃ χ : E → E, ContDiff ℝ (⊤ : ℕ∞) χ ∧ (χ =ᶠ[𝓝 0] id) ∧
      (∀ x, ‖χ x‖ ≤ R) ∧ (∀ x, R ≤ ‖x‖ → χ x = 0) := by
  let β : ContDiffBump (0 : E) := ⟨R / 2, R, by positivity, by linarith⟩
  let χ : E → E := fun x => β x • x
  refine ⟨χ, β.contDiff.smul contDiff_id, ?_, ?_, ?_⟩
  · filter_upwards [β.eventuallyEq_one] with x hx
    change β x • x = x
    rw [hx]
    exact one_smul ℝ x
  · intro x
    by_cases hx : R ≤ ‖x‖
    · have hz : β x = 0 := β.zero_of_le_dist (by simpa only [dist_zero_right] using hx)
      simp only [χ, hz, zero_smul, norm_zero]
      exact hR.le
    · change ‖β x • x‖ ≤ R
      rw [norm_smul, Real.norm_of_nonneg β.nonneg]
      exact (mul_le_mul_of_nonneg_right β.le_one (norm_nonneg x)).trans
        (by simpa only [one_mul] using (le_of_lt (lt_of_not_ge hx)))
  · intro x hx
    have hz : β x = 0 := β.zero_of_le_dist (by simpa only [dist_zero_right] using hx)
    simp only [χ, hz, zero_smul]

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public section
namespace AVRegularity.Construction.Preservation.Buffer

/-! A normalized component datum cancels the inverse mass price in the flux increment. -/

theorem sqrt_inverse_mass_cancel {π : ℝ} (hπ : 0 < π) :
    Real.sqrt π * Real.sqrt π⁻¹ = 1 := by
  rw [← Real.sqrt_mul hπ.le, mul_inv_cancel₀ hπ.ne', Real.sqrt_one]

theorem normalized_preparation_error_price {π : ℝ} (hπ : 0 < π) (C ε : ℝ) :
    Real.sqrt π * (C * ε * Real.sqrt π⁻¹) = C * ε := by
  calc
    _ = (Real.sqrt π * Real.sqrt π⁻¹) * (C * ε) := by ring
    _ = _ := by rw [sqrt_inverse_mass_cancel hπ, one_mul]

theorem normalized_preparation_enhanced_price {π : ℝ} (hπ : 0 < π)
    (A C ρ ell : ℝ) :
    A * Real.sqrt π * (C * Real.sqrt π⁻¹) / (ρ * ell) = A * C / (ρ * ell) := by
  calc
    _ = (Real.sqrt π * Real.sqrt π⁻¹) * (A * C) / (ρ * ell) := by ring
    _ = _ := by rw [sqrt_inverse_mass_cancel hπ, one_mul]

theorem molecular_delay_sqrt_price {ν ρ : ℝ} (hν : 0 < ν) (hρ : 0 ≤ ρ) :
    Real.sqrt ν * Real.sqrt (ρ ^ 2 / ν) = ρ := by
  rw [← Real.sqrt_mul hν.le]
  have he : ν * (ρ ^ 2 / ν) = ρ ^ 2 := by field_simp
  rw [he, Real.sqrt_sq_eq_abs, abs_of_nonneg hρ]

theorem normalized_material_flux_price {π ν θ elapsed : ℝ}
    (hπ : 0 < π) (hν : 0 < ν) (hθ : 0 ≤ 1 + θ) :
    (Real.sqrt π * (ν * (1 + θ))) * Real.sqrt elapsed *
      Real.sqrt (π⁻¹ / (5 * ν / 4)) ≤
      (1 + θ) * Real.sqrt ν * Real.sqrt elapsed := by
  have hp : Real.sqrt π ≠ 0 := (Real.sqrt_pos.2 hπ).ne'
  have hb : 0 < 5 * ν / 4 := by positivity
  have hsb : Real.sqrt (5 * ν / 4) ≠ 0 := (Real.sqrt_pos.2 hb).ne'
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have he : (Real.sqrt π * (ν * (1 + θ))) * Real.sqrt elapsed *
      Real.sqrt (π⁻¹ / (5 * ν / 4)) =
      (1 + θ) * (ν / Real.sqrt (5 * ν / 4)) * Real.sqrt elapsed := by
    rw [Real.sqrt_div (inv_nonneg.mpr hπ.le), Real.sqrt_inv]
    field_simp
  rw [he]
  have hden : Real.sqrt ν ≤ Real.sqrt (5 * ν / 4) :=
    Real.sqrt_le_sqrt (by linarith only [hν])
  have hr : ν / Real.sqrt (5 * ν / 4) ≤ Real.sqrt ν := by
    apply (div_le_iff₀ (Real.sqrt_pos.2 hb)).mpr
    calc
      ν = Real.sqrt ν * Real.sqrt ν := (Real.mul_self_sqrt hν.le).symm
      _ ≤ Real.sqrt ν * Real.sqrt (5 * ν / 4) :=
        mul_le_mul_of_nonneg_left hden hsν.le
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hθ) (Real.sqrt_nonneg _)

/-! The molecular waiting time satisfies the weighted-energy smoothing inequality. -/

theorem molecular_delay_energy {ρ ν : ℝ} (hρ : 0 < ρ) (hν : 0 < ν) :
    0 < ρ ^ 2 / ν ∧ ρ ^ 2 ≤ (5 * ν / 4) * (ρ ^ 2 / ν) := by
  refine ⟨div_pos (sq_pos_of_pos hρ) hν, ?_⟩
  have he : (5 * ν / 4) * (ρ ^ 2 / ν) = (5 / 4 : ℝ) * ρ ^ 2 := by
    field_simp
  rw [he]
  nlinarith [sq_nonneg ρ]

/-! Abstract scalar polynomial frequency factors are absorbed by the exponential mode weight. -/

theorem frequency_pow_le_exp_weight
    (j : ℕ) (ω a x : ℝ) (hω : 0 ≤ ω) (ha : 0 < a) (hx : 0 ≤ x) :
    (ω * x) ^ j ≤ ((j.factorial : ℝ) * (ω / a) ^ j) * Real.exp (a * x) := by
  have hf : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  have hh : (a * x) ^ j ≤ Real.exp (a * x) * j.factorial :=
    (div_le_iff₀ hf).mp (Real.pow_div_factorial_le_exp (a * x) (mul_nonneg ha.le hx) j)
  calc
    (ω * x) ^ j = (ω / a) ^ j * (a * x) ^ j := by
      rw [← mul_pow]
      congr 1
      field_simp [ha.ne']
    _ ≤ (ω / a) ^ j * (Real.exp (a * x) * j.factorial) :=
      mul_le_mul_of_nonneg_left hh (pow_nonneg (div_nonneg hω ha.le) j)
    _ = ((j.factorial : ℝ) * (ω / a) ^ j) * Real.exp (a * x) := by ring

/-! Compare the molecular radius with an enhanced radius using only their power bounds. -/

theorem preparation_radius_ratio_le {E ρ r c C q k : ℝ}
    (hE : 0 < E) (hr : 0 < r) (hc : 0 ≤ c) (hC : 0 < C)
    (hρ : ρ ≤ c * E ^ q) (hlo : C⁻¹ * E ^ (1 + k) ≤ r) :
    ρ / r ≤ c * C * E ^ (q - (1 + k)) := by
  have hlp : 0 < C⁻¹ * E ^ (1 + k) :=
    mul_pos (inv_pos.mpr hC) (Real.rpow_pos_of_pos hE _)
  calc
    _ ≤ (c * E ^ q) / r := div_le_div_of_nonneg_right hρ hr.le
    _ ≤ (c * E ^ q) / (C⁻¹ * E ^ (1 + k)) :=
      div_le_div_of_nonneg_left (mul_nonneg hc (Real.rpow_nonneg hE.le _)) hlp hlo
    _ = c * C * E ^ (q - (1 + k)) := by
      rw [Real.rpow_sub hE]
      field_simp

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.Construction.Preservation.Buffer

/-! Finitely many scalar components and retained orders share one scaled jet budget. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem scalar_component_common_scaled_jet_budget (T : Set ℝ) (n : ℕ)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (g : ℝ → E → Fin 2 → ℝ)
    (h : ∀ i : Fin 2, ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ t ∈ T, ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j (fun y => g t y i) x‖ ≤ C j) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ T, ∀ i j, j ≤ n → ∀ x,
      ρ ^ j * ‖iteratedFDeriv ℝ j (fun y => g t y i) x‖ ≤ M := by
  choose C hC hb using h
  let M := ∑ i : Fin 2, ∑ j : Fin (n + 1), ρ ^ j.1 * C i j.1
  have hterm (i : Fin 2) (j : Fin (n + 1)) : 0 ≤ ρ ^ j.1 * C i j.1 :=
    mul_nonneg (pow_nonneg hρ _) (hC i j.1)
  have hM : 0 ≤ M := Finset.sum_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ => hterm i j))
  refine ⟨M, hM, ?_⟩
  intro t ht i j hj x
  let q : Fin (n + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  have hs : ρ ^ j * C i j ≤ M :=
    (Finset.single_le_sum (fun q _ => hterm i q) (Finset.mem_univ q)).trans
      (Finset.single_le_sum (fun i _ => Finset.sum_nonneg (fun q _ => hterm i q))
        (Finset.mem_univ i))
  exact (mul_le_mul_of_nonneg_left (hb i t ht j hj x) (pow_nonneg hρ _)).trans hs

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public section
namespace AVRegularity.Construction.Preservation.Buffer

/-! Scalar material pairings alone force the minimum preparation wait. -/

theorem scalar_pairing_forces_delay {actual prepared η A B elapsed delay : ℝ}
    (happrox : |actual - prepared| ≤ η) (hprepared : |prepared| ≤ A)
    (hevolution : |actual - 1| ≤ B * Real.sqrt elapsed)
    (hB : 0 ≤ B) (herrors : η + A ≤ 1 / 2)
    (hprice : B * Real.sqrt delay ≤ 1 / 4) : delay ≤ elapsed := by
  by_contra! htime
  have hinc := (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt htime.le) hB).trans hprice
  have hactual : |actual| ≤ η + A := by
    calc
      |actual| = |(actual - prepared) + prepared| := by rw [sub_add_cancel]
      _ ≤ |actual - prepared| + |prepared| := abs_add_le _ _
      _ ≤ η + A := add_le_add happrox hprepared
  have hsum : 1 ≤ |actual - 1| + |actual| := by
    calc
      1 = |(1 - actual) + actual| := by rw [sub_add_cancel, abs_one]
      _ ≤ |1 - actual| + |actual| := abs_add_le _ _
      _ = |actual - 1| + |actual| := by rw [abs_sub_comm 1 actual]
  linarith only [hsum, hactual, hevolution, herrors, hinc]

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance.Infra.Flow
namespace AVRegularity.Construction.Preservation.Buffer

/-! The generic flow deviation estimate gives a uniform bound on the molecular time window.
Only the literal spatial derivative bound is used; no upstream OC construction is substituted. -/

theorem short_time_flow_derivative_le_three {v : ℝ → Vec 2 → Vec 2}
    (hv : SmoothPeriodicField v) {X : ℝ → Vec 2 → ℝ → Vec 2}
    (hX : AVenhance.IsFlow v X) {L : ℝ} (hL : 0 ≤ L)
    (hDv : ∀ t x, ‖jointSpatialFDeriv v t x‖ ≤ L)
    (s t : ℝ) (hsmall : L * |t - s| ≤ 1) (x : Vec 2) :
    ‖fderiv ℝ (fun y => X t y s) x‖ ≤ 3 := by
  have hd := flow_fderiv_deviation_of_small_time hv hX hL hDv s t x hsmall
  have h1 : ‖(1 : Vec 2 →L[ℝ] Vec 2)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  calc
    ‖fderiv ℝ (fun y => X t y s) x‖ =
        ‖(fderiv ℝ (fun y => X t y s) x - 1) + 1‖ := by rw [sub_add_cancel]
    _ ≤ ‖fderiv ℝ (fun y => X t y s) x - 1‖ + ‖(1 : Vec 2 →L[ℝ] Vec 2)‖ := norm_add_le _ _
    _ ≤ 2 * L * |t - s| + 1 := add_le_add hd h1
    _ ≤ 3 := by linarith only [hsmall]

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public section
namespace AVRegularity.Construction.Preservation.Buffer

/-! Pure real algebra converting stream bounds into drift jet majorants. -/

theorem stream_jet_scale_conversion (a e r : ℝ) (he : e ≠ 0) :
    32 * a * e ^ 2 * r = (2097152 * a) * (256 * e⁻¹)⁻¹ ^ 2 * r := by
  field_simp [he]
  ring

theorem drift_scaled_geometric_identity (C a e : ℝ) (he : e ≠ 0) (j : ℕ) :
    C * (8192 * a * e) * (4 * (256 * e⁻¹)) ^ j * (j.factorial : ℝ) =
      (C * 8192 * a) * 1024 ^ j * (j.factorial : ℝ) * e ^ ((1 : ℤ) - j) := by
  rw [zpow_sub₀ he, zpow_one, zpow_natCast]
  rw [show 4 * (256 * e⁻¹) = 1024 * e⁻¹ by ring, mul_pow, inv_pow]
  ring

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.Construction.Preservation.Buffer

/-! Copy-adapt the project's Campanato Cauchy--Schwarz argument without normalizing the measure.
The measure factor supplies the square root of the elapsed time. -/

theorem integral_norm_le_sqrt_mass_mul_sqrt_square {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] (μ : Measure Ω) [IsFiniteMeasure μ]
    (u : Ω → E) (hu : MemLp u 2 μ) :
    (∫ t, ‖u t‖ ∂μ) ≤ Real.sqrt (μ.real Set.univ) * Real.sqrt (∫ t, ‖u t‖ ^ 2 ∂μ) := by
  have hp : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hn : MemLp (fun t => ‖u t‖) (ENNReal.ofReal 2) μ := by simpa using hu.norm
  have h1 : MemLp (fun _ : Ω => (1 : ℝ)) (ENNReal.ofReal 2) μ := memLp_const 1
  have hh := integral_mul_norm_le_Lp_mul_Lq hp hn h1
  have hb : (∫ t, ‖u t‖ ∂μ) ≤
      Real.sqrt (∫ t, ‖u t‖ ^ 2 ∂μ) * Real.sqrt (μ.real Set.univ) := by
    simpa only [norm_norm, norm_one, mul_one, Real.rpow_two, one_pow,
      integral_const, smul_eq_mul, ← Real.sqrt_eq_rpow] using hh
  exact hb.trans_eq (mul_comm _ _)

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public section
open MeasureTheory Set
namespace AVRegularity.Construction.Preservation.Buffer

/-! Translate scalar energy curves by their actual initial time using the integral
representation of absolutely continuous functions. -/

theorem ae_time_translate {a b : ℝ} {p : ℝ → Prop}
    (hp : ∀ᵐ t ∂volume.restrict (Icc a b), p t) :
    ∀ᵐ t ∂volume.restrict (Icc 0 (b - a)), p (a + t) := by
  have hm : MapsTo (fun t : ℝ => a + t) (Icc 0 (b - a)) (Icc a b) := by
    intro t ht
    constructor <;> linarith only [ht.1, ht.2]
  exact ((measurePreserving_add_left volume a).quasiMeasurePreserving.restrict hm).ae hp

theorem absolutelyContinuous_time_translate {E : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hE : AbsolutelyContinuousOnInterval E a b) :
    AbsolutelyContinuousOnInterval (fun t => E (a + t)) 0 (b - a) := by
  have hT : 0 ≤ b - a := sub_nonneg.mpr hab
  have hi : IntervalIntegrable (fun t => deriv E (a + t)) volume 0 (b - a) := by
    simpa only [sub_self] using hE.intervalIntegrable_deriv.comp_add_left a
  have hac := hi.absolutelyContinuousOnInterval_intervalIntegral
    (c := 0) (by simp only [uIcc_of_le hT, mem_Icc, le_refl, hT, and_self])
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => E a) 0 (b - a) :=
    (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => E a)).contDiffOn.absolutelyContinuousOnInterval
  apply (hconst.add hac).congr
  intro t ht
  rw [uIcc_of_le hT] at ht
  have hat : a ≤ a + t := le_add_of_nonneg_right ht.1
  have htb : a + t ≤ b := by linarith only [ht.2]
  have hsub : uIcc a (a + t) ⊆ uIcc a b := by
    rw [uIcc_of_le hat, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl htb
  have hf := (hE.mono hsub).integral_deriv_eq_sub
  change E a + (∫ r in 0..t, deriv E (a + r)) = E (a + t)
  rw [intervalIntegral.integral_comp_add_left, add_zero, hf]
  ring

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public section
namespace AVRegularity.Construction.Preservation.Buffer

/-! Abstract-real two-coordinate estimates for the weak pullback gradient. -/

theorem two_coordinate_column_square_le {a b L : ℝ} (d e : ℝ)
    (ha : |a| ≤ L) (hb : |b| ≤ L) :
    (a * d + b * e) ^ 2 ≤ 2 * L ^ 2 * (d ^ 2 + e ^ 2) := by
  have ha2 : a ^ 2 ≤ L ^ 2 := by
    have h := abs_le.mp ha
    nlinarith [h.1, h.2]
  have hb2 : b ^ 2 ≤ L ^ 2 := by
    have h := abs_le.mp hb
    nlinarith [h.1, h.2]
  have hd := mul_le_mul_of_nonneg_right ha2 (sq_nonneg d)
  have he := mul_le_mul_of_nonneg_right hb2 (sq_nonneg e)
  nlinarith [sq_nonneg (a * d - b * e)]

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.Construction.Preservation.Buffer

/-! Finite derivative budgets compose uniformly without bounding the inner function's value. -/

variable {E F V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem uniform_composition_jet_bounds (T : Set ℝ) (n : ℕ)
    (g : ℝ → F → V) (f : ℝ → E → F)
    (hg : ∀ t ∈ T, ContDiff ℝ (n : ℕ∞) (g t))
    (hf : ∀ t ∈ T, ContDiff ℝ (n : ℕ∞) (f t))
    (C D : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j) (hD : ∀ j, 0 ≤ D j)
    (hgj : ∀ t ∈ T, ∀ j ≤ n, ∀ y, ‖iteratedFDeriv ℝ j (g t) y‖ ≤ C j)
    (hfj : ∀ t ∈ T, ∀ j, 1 ≤ j → j ≤ n → ∀ x,
      ‖iteratedFDeriv ℝ j (f t) x‖ ≤ D j) :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧ ∀ t ∈ T, ∀ j ≤ n, ∀ x,
      ‖iteratedFDeriv ℝ j (g t ∘ f t) x‖ ≤ B j := by
  let C₀ := ∑ i ∈ Finset.range (n + 1), C i
  let D₀ := 1 + ∑ i ∈ Finset.range (n + 1), D i
  have hC₀ : 0 ≤ C₀ := Finset.sum_nonneg (fun i _ => hC i)
  have hD₀ : 1 ≤ D₀ := le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hD i))
  refine ⟨fun j => (j.factorial : ℝ) * C₀ * D₀ ^ j, fun j =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC₀) (pow_nonneg (zero_le_one.trans hD₀) _), ?_⟩
  intro t ht j hj x
  apply norm_iteratedFDeriv_comp_le (hg t ht) (hf t ht) (by exact_mod_cast hj) x
  · intro i hi
    exact (hgj t ht i (hi.trans hj) _).trans
      (Finset.single_le_sum (fun k _ => hC k) (Finset.mem_range.mpr (by omega)))
  · intro i hi hij
    have hd : D i ≤ ∑ k ∈ Finset.range (n + 1), D k :=
      Finset.single_le_sum (fun k _ => hD k) (Finset.mem_range.mpr (by omega))
    exact (hfj t ht i hi (hij.trans hj) x).trans
      (hd.trans ((le_add_of_nonneg_left zero_le_one).trans (le_self_pow₀ hD₀ (by omega))))

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Set Filter Metric
open scoped Topology
namespace AVRegularity.Construction.Preservation.Buffer

/-! Smooth contour kernels constant outside a fixed spatial ball have uniform parameter jets. -/

variable {P E V : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem compact_parameter_exists_slice_jet_bound
    (F : P × E → V) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (S : Set P) (hS : IsCompact S) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ p ∈ S, ∀ x, R ≤ ‖x‖ → F (p, x) = F (p, 0)) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ S, ∀ x,
      ‖iteratedFDeriv ℝ j (fun y => F (p, y)) x‖ ≤ C := by
  have hK : IsCompact (S ×ˢ closedBall (0 : E) (R + 1)) :=
    hS.prod (isCompact_closedBall 0 (R + 1))
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    (hF.continuous_iteratedFDeriv (by simp : (j : WithTop ℕ∞) ≤ (⊤ : ℕ∞))).continuousOn
  refine ⟨max 0 B, le_max_left _ _, ?_⟩
  intro p hp x
  have hinside {y : E} (hy : y ∈ closedBall (0 : E) (R + 1)) :
      ‖iteratedFDeriv ℝ j (fun z => F (p, z)) y‖ ≤ max 0 B :=
    (joint_slice_iteratedFDeriv_norm_le F hF p y j).trans
      ((hB (p, y) ⟨hp, hy⟩).trans (le_max_right _ _))
  by_cases hx : x ∈ closedBall (0 : E) (R + 1)
  · exact hinside hx
  · have hxR : R < ‖x‖ := by
      have hx' : R + 1 < ‖x‖ := by
        simpa only [mem_closedBall, dist_zero_right, not_le] using hx
      linarith only [hx']
    have he : (fun y => F (p, y)) =ᶠ[𝓝 x] (fun _ => F (p, 0)) := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hxR] with y hy
      exact hc p hp y hy.le
    have hd := (he.iteratedFDeriv ℝ j).eq_of_nhds
    by_cases hj : j = 0
    · subst j
      have hz := hinside (y := 0) (by simpa only [mem_closedBall, dist_self] using
        (show 0 ≤ R + 1 by linarith only [hR]))
      simpa only [norm_iteratedFDeriv_zero, hc p hp x hxR.le] using hz
    · rw [hd, iteratedFDeriv_const_of_ne hj, Pi.zero_apply, norm_zero]
      exact le_max_left _ _

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Complex MeasureTheory Set
open scoped Real
namespace AVRegularity.Construction.Preservation.Buffer

/-! The literal two-circle representation as one integral over its finite angle measure. -/

def cauchyAngleMeasure : Measure ℝ := volume.restrict (Icc 0 (2 * Real.pi))

instance cauchyAngleMeasureFinite : IsFiniteMeasure cauchyAngleMeasure := by
  unfold cauchyAngleMeasure
  infer_instance

def cauchyBoundaryCoefficient (R : ℝ) (F : ℂ → ℂ → ℂ) : ℝ × ℝ → ℂ := fun p =>
  (2 * Real.pi * Complex.I : ℂ)⁻¹ * deriv (circleMap 0 R) p.1 *
    (2 * Real.pi * Complex.I : ℂ)⁻¹ * deriv (circleMap 0 R) p.2 *
      F (circleMap 0 R p.1) (circleMap 0 R p.2)

theorem double_cauchy_angle_integral_eq
    (R : ℝ) (F : ℂ → ℂ → ℂ) (w z : ℂ)
    (hi : Integrable (fun p : ℝ × ℝ => cauchyBoundaryCoefficient R F p *
      (circleMap 0 R p.1 - w)⁻¹ * (circleMap 0 R p.2 - z)⁻¹)
        (cauchyAngleMeasure.prod cauchyAngleMeasure)) :
    (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      (∮ u in C(0, R), (u - w)⁻¹ • ((2 * Real.pi * Complex.I : ℂ)⁻¹ •
        (∮ v in C(0, R), (v - z)⁻¹ • F u v))) =
      ∫ p, cauchyBoundaryCoefficient R F p *
        (circleMap 0 R p.1 - w)⁻¹ * (circleMap 0 R p.2 - z)⁻¹
        ∂(cauchyAngleMeasure.prod cauchyAngleMeasure) := by
  rw [integral_prod _ hi]
  simp_rw [circleIntegral_def_Icc, smul_eq_mul]
  change _ = ∫ θ, (∫ φ, _ ∂cauchyAngleMeasure) ∂cauchyAngleMeasure
  simp_rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun θ => by
    dsimp only
    apply integral_congr_ae
    exact ae_of_all _ (fun φ => by dsimp [cauchyBoundaryCoefficient]; ring))

end AVRegularity.Construction.Preservation.Buffer
end
end
