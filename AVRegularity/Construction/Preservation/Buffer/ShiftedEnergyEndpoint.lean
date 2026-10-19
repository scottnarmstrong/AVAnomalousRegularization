-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.Buffer.DoubleCauchyAngleIntegral
public import AVRegularity.CycleEvolution.TimeEnergy
public import AVRegularity.Statements.Intermediate.CycleReference.JacMatrix
import AVRegularity.KernelEnergy.TorusGraphProjection
public import AVRegularity.Statements.Intermediate.CoupledEnergy.CoefficientSeminorm
public import AVRegularity.Sobolev.FactorialShift
public import AVenhance.Statements.Roots.IsPeriodicH1With
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Complex.Convex
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

section
@[expose] public section
namespace AVRegularity.Construction.Preservation.Buffer

/-! One positive radius constant enforces drift smallness at every represented order. -/

theorem exists_drift_radius_constant (A B : ℝ) (hA : 0 ≤ A) (hB : 1 ≤ B) :
    ∃ cmax : ℝ, 0 < cmax ∧ ∀ c : ℝ, 0 < c → c ≤ cmax →
      B * c ≤ 1 / 2 ∧ A * B * c ^ 2 ≤ 1 / 8 := by
  have hAp : 0 < A + 1 := by linarith only [hA]
  have hBp : 0 < B := zero_lt_one.trans_le hB
  let cmax := 1 / (8 * (A + 1) * B)
  have hcmax : 0 < cmax := div_pos zero_lt_one
    (mul_pos (mul_pos (by norm_num) hAp) hBp)
  have hden : 1 ≤ 8 * (A + 1) * B := by
    calc
      1 ≤ 8 := by norm_num
      _ ≤ 8 * (A + 1) := by linarith only [hA]
      _ ≤ 8 * (A + 1) * B := le_mul_of_one_le_right (by positivity) hB
  have hcmax1 : cmax ≤ 1 := (div_le_one
    (mul_pos (mul_pos (by norm_num) hAp) hBp)).mpr hden
  have hid : (A + 1) * B * cmax = 1 / 8 := by
    dsimp only [cmax]
    field_simp [hAp.ne', hBp.ne']
  refine ⟨cmax, hcmax, ?_⟩
  intro c hc hcm
  have hBc : B * c ≤ 1 / 8 := by
    calc
      B * c ≤ (A + 1) * B * c := by
        apply mul_le_mul_of_nonneg_right _ hc.le
        exact (le_mul_of_one_le_left hBp.le (by linarith only [hA]))
      _ ≤ (A + 1) * B * cmax := mul_le_mul_of_nonneg_left hcm (mul_nonneg hAp.le hBp.le)
      _ = 1 / 8 := hid
  refine ⟨hBc.trans (by norm_num), ?_⟩
  calc
    A * B * c ^ 2 ≤ A * B * c := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hA hBp.le)
      rw [pow_two]
      exact (mul_le_mul_of_nonneg_left (hcm.trans hcmax1) hc.le).trans_eq (mul_one c)
    _ ≤ (A + 1) * B * c := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hBp.le) hc.le
    _ ≤ (A + 1) * B * cmax := mul_le_mul_of_nonneg_left hcm (mul_nonneg hAp.le hBp.le)
    _ = 1 / 8 := hid

/-! The ceiling choice has a uniform molecular price when both radius prices are small. -/

theorem frequency_radius_price_le {ρ r C ell U η : ℝ}
    (hρ : 0 ≤ ρ) (hU : 0 ≤ U) (hC : 0 ≤ C)
    (hell : ell ≤ U * (C / r + 1)) (hratio : ρ / r ≤ η) (hsize : ρ ≤ η) :
    ell * ρ ≤ U * (C + 1) * η := by
  calc
    _ ≤ U * (C / r + 1) * ρ := mul_le_mul_of_nonneg_right hell hρ
    _ = U * (C * (ρ / r) + ρ) := by ring
    _ ≤ U * (C * η + η) := mul_le_mul_of_nonneg_left
      (add_le_add (mul_le_mul_of_nonneg_left hratio hC) hsize) hU
    _ = _ := by ring

theorem exists_fourier_integer_with_radius_price {C r ρ δ : ℝ}
    (hC : 0 < C) (hr : 0 < r) (hρ : 0 ≤ ρ)
    (hratio : ρ / r ≤ δ / (2 * Real.pi * (C + 1)))
    (hsize : ρ ≤ δ / (2 * Real.pi * (C + 1))) :
    ∃ N : ℕ, 1 ≤ N ∧ C / r ≤ (N : ℝ) ∧ (N : ℝ) ≤ C / r + 1 ∧
      (2 * Real.pi * (N : ℝ)) * ρ ≤ δ := by
  obtain ⟨N, hN, hlo, hhi⟩ := exists_fourier_integer_at_scale hC hr
  refine ⟨N, hN, hlo, hhi, ?_⟩
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hden : 2 * Real.pi * (C + 1) ≠ 0 :=
    (mul_pos hp (by linarith only [hC])).ne'
  have hb := frequency_radius_price_le hρ hp.le hC.le
    (mul_le_mul_of_nonneg_left hhi hp.le) hratio hsize
  exact hb.trans_eq (mul_div_cancel₀ δ hden)

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Set
namespace AVRegularity.Construction.Preservation.Buffer

/-! Continue real identities across a horizontal complex strip. -/

theorem holomorphic_eqOn_strip_of_real_eq
    (R : ℝ) (hR : 0 < R) {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z : ℂ | |z.im| < R})
    (hg : DifferentiableOn ℂ g {z : ℂ | |z.im| < R})
    (he : ∀ r : ℝ, f r = g r) :
    EqOn f g {z : ℂ | |z.im| < R} := by
  have ho : IsOpen {z : ℂ | |z.im| < R} :=
    isOpen_lt Complex.continuous_im.abs continuous_const
  have hc : Convex ℝ {z : ℂ | |z.im| < R} := by
    have heq : {z : ℂ | |z.im| < R} =
        {z : ℂ | -R < z.im} ∩ {z : ℂ | z.im < R} := by
      ext z
      exact (abs_lt : |z.im| < R ↔ -R < z.im ∧ z.im < R)
    rw [heq]
    exact (convex_halfSpace_im_gt (-R)).inter (convex_halfSpace_im_lt R)
  apply holomorphic_eqOn_of_real_eq ho hc.isPreconnected
    (by simpa only [mem_ofPred_eq, Complex.zero_im, abs_zero] using hR) hf hg
  exact fun r _ => he r

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public section
namespace AVRegularity.Construction.Preservation.Buffer

/-! Abstract-real bounds for the radius used by the molecular buffer. -/

theorem molecular_radius_bounds {c e ν a : ℝ}
    (hc : 0 < c) (he : 0 < e) (hν : 0 < ν) (ha : 0 < a) :
    0 < c * min e (Real.sqrt (ν / a)) ∧
      c * min e (Real.sqrt (ν / a)) ≤ c * e ∧
      (c * min e (Real.sqrt (ν / a))) ^ 2 ≤ c ^ 2 * (ν / a) := by
  have hp : 0 < min e (Real.sqrt (ν / a)) :=
    lt_min he (Real.sqrt_pos.mpr (div_pos hν ha))
  refine ⟨mul_pos hc hp, mul_le_mul_of_nonneg_left (min_le_left _ _) hc.le, ?_⟩
  rw [mul_pow]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg c)
  calc
    (min e (Real.sqrt (ν / a))) ^ 2 ≤ (Real.sqrt (ν / a)) ^ 2 :=
      pow_le_pow_left₀ hp.le (min_le_right _ _) 2
    _ = ν / a := Real.sq_sqrt (div_nonneg hν.le ha.le)

theorem molecular_radius_drift_smallness {c e ν a A B : ℝ}
    (hc : 0 < c) (he : 0 < e) (hν : 0 < ν) (ha : 0 < a)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hgeom : B * c ≤ 1 / 2) (hstrain : A * B * c ^ 2 ≤ 1 / 8) :
    B * (c * min e (Real.sqrt (ν / a))) / e ≤ 1 / 2 ∧
      (A * a) * B * (c * min e (Real.sqrt (ν / a))) ^ 2 ≤ ν / 8 := by
  have hr := molecular_radius_bounds hc he hν ha
  exact drift_smallness_of_molecular_radius he ha hν.le hA hB hr.2.1 hr.2.2 hgeom hstrain

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
namespace AVRegularity.Construction.Preservation.Buffer

/-! Polarization of the reused strong-time energy identity gives moving pairings. -/

open CycleEvolution

theorem strong_time_inner_increment {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {a b : ℝ} {u du z dz : ℝ → H}
    (hu : StrongTimeRegularity a b u du) (hz : StrongTimeRegularity a b z dz) :
    inner ℝ (u b) (z b) - inner ℝ (u a) (z a) =
      ∫ t in a..b, inner ℝ (du t) (z t) + inner ℝ (u t) (dz t) := by
  have hac : AbsolutelyContinuousOnInterval (fun t => inner ℝ (u t) (z t)) a b := by
    have hp := ((hu.norm_sq_ac.add hz.norm_sq_ac).sub (hu.sub hz).norm_sq_ac).const_mul
      (1 / 2 : ℝ)
    apply hp.congr
    intro t _
    change (1 / 2 : ℝ) * (‖u t‖ ^ 2 + ‖z t‖ ^ 2 - ‖u t - z t‖ ^ 2) = _
    rw [norm_sub_sq_real]
    ring
  rw [← hac.integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae_restrict
  have hd := hu.derivative.filter_mono
    (ae_mono (Measure.restrict_mono uIoc_subset_uIcc le_rfl))
  have hz' := hz.derivative.filter_mono
    (ae_mono (Measure.restrict_mono uIoc_subset_uIcc le_rfl))
  filter_upwards [hd, hz'] with t ht hzt
  simpa only [add_comm] using (ht.inner ℝ hzt).deriv

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace AVRegularity.Construction.Preservation.Buffer

/-! Smooth localization on a larger window preserves the actual strong-time curve. -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem strong_time_window_congruence {a b : ℝ} (hab : a ≤ b)
    {u du v dv : ℝ → H} (hu : CycleEvolution.StrongTimeRegularity a b u du)
    (hv : EqOn u v (Ioo (a - 1) (b + 1))) (hd : EqOn du dv (Icc a b)) :
    CycleEvolution.StrongTimeRegularity a b v dv := by
  have hsub : Icc a b ⊆ Ioo (a - 1) (b + 1) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  refine ⟨hu.ac.congr (by simpa only [uIcc_of_le hab] using hv.mono hsub), ?_⟩
  have hder := hu.derivative
  rw [uIcc_of_le hab] at hder ⊢
  filter_upwards [hder, ae_restrict_mem measurableSet_Icc] with t ht htm
  rw [← hd htm]
  apply ht.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds (hsub htm)] with r hr
  exact (hv hr).symm

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
namespace AVRegularity.Construction.Preservation.Buffer

/-! The flux's time integral carries the square root of elapsed time. -/

theorem interval_integral_norm_le_sqrt_length {E : Type*} [NormedAddCommGroup E]
    {a b : ℝ} (hab : a ≤ b) (u : ℝ → E)
    (hu : MemLp u 2 (volume.restrict (Icc a b))) :
    (∫ t in a..b, ‖u t‖) ≤
      Real.sqrt (b - a) * Real.sqrt (∫ t in Icc a b, ‖u t‖ ^ 2) := by
  have hc := integral_norm_le_sqrt_mass_mul_sqrt_square (volume.restrict (Icc a b)) u hu
  have hm : (volume.restrict (Icc a b)).real univ = volume.real (Icc a b) := by
    simp [Measure.real]
  rw [hm, Real.volume_real_Icc_of_le hab, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab] at hc
  exact hc

/-! Fixed-test weak increments give a strong integral curve after the adjoint value map.
This reuses the integral ODE representative and strong-time calculus. -/

section
open CycleEvolution AVenhance.Infra.ODE

variable {F H : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem adjoint_weak_curve_strong_time {a b : ℝ} (hab : a ≤ b)
    (J : F →L[ℝ] H) (u : ℝ → H) (g : ℝ → F)
    (hg : IntervalIntegrable g volume a b)
    (hweak : ∀ t ∈ Icc a b, ∀ z : F,
      inner ℝ (u t) (J z) - inner ℝ (u a) (J z) = ∫ r in a..t, inner ℝ (g r) z) :
    StrongTimeRegularity a b (fun t => J.adjoint (u t)) g := by
  let q : ℝ → F := fun t => J.adjoint (u t)
  have hrep (t : ℝ) (ht : t ∈ Icc a b) : q t = q a + ∫ r in a..t, g r := by
    have hsub : uIcc a t ⊆ uIcc a b := by
      rw [uIcc_of_le ht.1, uIcc_of_le hab]
      exact Icc_subset_Icc le_rfl ht.2
    have hgt : IntervalIntegrable g volume a t := hg.mono_set hsub
    apply ext_inner_right ℝ
    intro z
    have hint : inner ℝ (∫ r in a..t, g r) z = ∫ r in a..t, inner ℝ (g r) z := by
      simpa only [innerSL_apply_apply, real_inner_comm] using
        ((innerSL ℝ z).intervalIntegral_comp_comm hgt).symm
    rw [inner_add_left, hint]
    dsimp only [q]
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left]
    simpa only [add_comm] using eq_add_of_sub_eq (hweak t ht z)
  have hy : IsLinearIntegralSolution (fun _ => (0 : F →L[ℝ] F)) g (q a) a b q := by
    intro t ht
    simpa only [linearRhs, zero_apply, zero_add] using hrep t ht
  have he : linearRhs (fun _ => (0 : F →L[ℝ] F)) g q = g := by
    funext t
    exact zero_add _
  have hint : IntervalIntegrable (linearRhs (fun _ => (0 : F →L[ℝ] F)) g q) volume a b := by
    rw [he]
    exact hg
  refine ⟨hy.absolutelyContinuousOnInterval hab hint, ?_⟩
  apply (ae_restrict_iff' measurableSet_uIcc).mpr
  filter_upwards [hy.ae_hasDerivAt hab hint] with t ht
  simpa only [uIcc_of_le hab, he] using ht

theorem weak_curve_moving_test_increment {a b : ℝ} (hab : a ≤ b)
    (J : F →L[ℝ] H) (u : ℝ → H) (g : ℝ → F)
    (hg : IntervalIntegrable g volume a b)
    (hweak : ∀ t ∈ Icc a b, ∀ z : F,
      inner ℝ (u t) (J z) - inner ℝ (u a) (J z) = ∫ r in a..t, inner ℝ (g r) z)
    (z dz : ℝ → F) (hz : StrongTimeRegularity a b z dz) :
    inner ℝ (u b) (J (z b)) - inner ℝ (u a) (J (z a)) =
      ∫ t in a..b, inner ℝ (g t) (z t) + inner ℝ (u t) (J (dz t)) := by
  have hq := adjoint_weak_curve_strong_time hab J u g hg hweak
  have hp := strong_time_inner_increment hq hz
  simpa only [ContinuousLinearMap.adjoint_inner_left] using hp
end

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Complex MeasureTheory
namespace AVRegularity.Construction.Preservation.Buffer

/-! The angle coefficient inherits the genuine pointwise contour bound. -/

theorem cauchy_boundary_coefficient_measurable
    (R : ℝ) (F : ℂ → ℂ → ℂ)
    (hc : Continuous (fun p : ℝ × ℝ => F (circleMap 0 R p.1) (circleMap 0 R p.2))) :
    Measurable (cauchyBoundaryCoefficient R F) := by
  apply Continuous.measurable
  unfold cauchyBoundaryCoefficient
  simp_rw [deriv_circleMap]
  exact ((((continuous_const.mul
    (((continuous_circleMap 0 R).comp continuous_fst).mul continuous_const)).mul
      continuous_const).mul
        (((continuous_circleMap 0 R).comp continuous_snd).mul continuous_const)).mul hc)

theorem cauchy_boundary_coefficient_norm_le
    (R : ℝ) (hR : 0 < R) (F : ℂ → ℂ → ℂ) (M : ℝ)
    (hb : ∀ θ φ : ℝ, ‖F (circleMap 0 R θ) (circleMap 0 R φ)‖ ≤ M)
    (p : ℝ × ℝ) :
    ‖cauchyBoundaryCoefficient R F p‖ ≤
      (‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ ^ 2 * R ^ 2) * M := by
  have hd (θ : ℝ) : ‖deriv (circleMap 0 R) θ‖ = R := by
    simp only [deriv_circleMap, norm_mul, norm_circleMap_zero, abs_of_pos hR,
      norm_I, mul_one]
  unfold cauchyBoundaryCoefficient
  rw [norm_mul, norm_mul, norm_mul, norm_mul, hd, hd]
  calc
    _ ≤ (‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ * R *
        ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ * R) * M :=
      mul_le_mul_of_nonneg_left (hb p.1 p.2) (by positivity)
    _ = _ := by ring

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
namespace AVRegularity.Construction.Preservation.Buffer

/-! An energy dissipation bound gives the elapsed-time scale of a component flux. -/

theorem flux_integral_le_of_energy {E : Type*} [NormedAddCommGroup E]
    {a b C β M : ℝ} (hab : a ≤ b) (hC : 0 ≤ C) (hβ : 0 < β)
    (flux : ℝ → E) (hflux : MemLp flux 2 (volume.restrict (Icc a b)))
    (R : ℝ → ℝ) (hR : IntegrableOn R (Icc a b))
    (hRnonneg : ∀ t ∈ Icc a b, 0 ≤ R t)
    (hpoint : ∀ t ∈ Icc a b, ‖flux t‖ ≤ C * Real.sqrt (R t))
    (henergy : β * (∫ t in Icc a b, R t) ≤ M) :
    (∫ t in a..b, ‖flux t‖) ≤ C * Real.sqrt (b - a) * Real.sqrt (M / β) := by
  have hsquare : (∫ t in Icc a b, ‖flux t‖ ^ 2) ≤
      C ^ 2 * (∫ t in Icc a b, R t) := by
    rw [← integral_const_mul]
    apply integral_mono_ae hflux.norm.integrable_sq (hR.const_mul _)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (Real.sqrt_nonneg _))).mpr
      (hpoint t ht)
    rwa [mul_pow, Real.sq_sqrt (hRnonneg t ht)] at hs
  have hRM : (∫ t in Icc a b, R t) ≤ M / β := (le_div_iff₀ hβ).mpr (by
    simpa only [mul_comm] using henergy)
  have hroot := Real.sqrt_le_sqrt (hsquare.trans
    (mul_le_mul_of_nonneg_left hRM (sq_nonneg C)))
  rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq_eq_abs, abs_of_nonneg hC] at hroot
  exact (interval_integral_norm_le_sqrt_length hab flux hflux).trans
    ((mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg _)).trans_eq (by ring))

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public section
namespace AVRegularity.Construction.Preservation.Buffer

/-! The molecular radius makes the short-time flow derivative price uniform. -/

theorem molecular_time_window_smallness {c e ν a C s t : ℝ}
    (hc : 0 < c) (he : 0 < e) (hν : 0 < ν) (ha : 0 < a)
    (hC : 0 ≤ C) (hsmall : C * c ^ 2 ≤ 1)
    (htime : |t - s| ≤ (c * min e (Real.sqrt (ν / a))) ^ 2 / ν) :
    (C * a) * |t - s| ≤ 1 := by
  have hr := (molecular_radius_bounds hc he hν ha).2.2
  calc
    _ ≤ (C * a) * ((c * min e (Real.sqrt (ν / a))) ^ 2 / ν) :=
      mul_le_mul_of_nonneg_left htime (mul_nonneg hC ha.le)
    _ ≤ (C * a) * ((c ^ 2 * (ν / a)) / ν) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hr hν.le) (mul_nonneg hC ha.le)
    _ = C * c ^ 2 := by field_simp
    _ ≤ 1 := hsmall

/-! A frequency at the enhanced radius makes the prepared material pairing small. -/

theorem prepared_fourier_pairing_price_le {r C CQ : ℝ} {N : ℕ}
    (hr : 0 < r) (hC : 0 < C) (hN : C / r ≤ (N : ℝ))
    (hprice : 8 * Real.sqrt 18 * CQ ≤ C) :
    Real.sqrt 18 * CQ / (r * (2 * Real.pi * (N : ℝ))) ≤ 1 / 8 := by
  have hNp : 0 < (N : ℝ) := (div_pos hC hr).trans_le hN
  have hpi : 1 ≤ 2 * Real.pi := by linarith only [Real.two_le_pi]
  have hbase : C ≤ r * (N : ℝ) := by
    have h := (div_le_iff₀ hr).mp hN
    simpa only [mul_comm] using h
  have hden : C ≤ r * (2 * Real.pi * (N : ℝ)) := hbase.trans
    (mul_le_mul_of_nonneg_left (by nlinarith only [hpi, hNp]) hr.le)
  apply (div_le_iff₀ (mul_pos hr (mul_pos (mul_pos (by norm_num) Real.pi_pos) hNp))).mpr
  linarith only [hprice.trans hden]

theorem prepared_fourier_choice_constant (CQ : ℝ) :
    0 < 8 * Real.sqrt 18 * (|CQ| + 1) ∧
      8 * Real.sqrt 18 * CQ ≤ 8 * Real.sqrt 18 * (|CQ| + 1) := by
  have hs : 0 < Real.sqrt 18 := Real.sqrt_pos.2 (by norm_num)
  exact ⟨mul_pos (mul_pos (by norm_num) hs) (by positivity),
    mul_le_mul_of_nonneg_left ((le_abs_self CQ).trans (by linarith only [abs_nonneg CQ]))
      (mul_nonneg (by norm_num) hs.le)⟩

theorem molecular_fourier_increment_price_le {ell ρ θ : ℝ}
    (hell : 0 ≤ ell) (hρ : 0 ≤ ρ) (hθ : θ ≤ 1 / 8)
    (hfreq : ell * ρ ≤ 1 / (32 * Real.sqrt 2)) :
    (6 * (ell * Real.sqrt 2)) * (1 + θ) * ρ ≤ 1 / 4 := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  calc
    _ = (6 * Real.sqrt 2) * (ell * ρ) * (1 + θ) := by ring
    _ ≤ (6 * Real.sqrt 2) * (ell * ρ) * (9 / 8) :=
      mul_le_mul_of_nonneg_left (by linarith only [hθ])
        (mul_nonneg (mul_nonneg (by norm_num) hs.le) (mul_nonneg hell hρ))
    _ ≤ (6 * Real.sqrt 2) * (1 / (32 * Real.sqrt 2)) * (9 / 8) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfreq
        (mul_nonneg (by norm_num) hs.le)) (by norm_num)
    _ ≤ 1 / 4 := by
      field_simp
      norm_num

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization
open scoped Matrix
namespace AVRegularity.Construction.Preservation.Buffer

/-! A flow derivative bound controls each weak pullback gradient coordinate. -/

theorem pullback_gradient_coordinate_square_le (X : Vec 2 → Vec 2) (x d : Vec 2)
    {L : ℝ} (hX : ‖fderiv ℝ X x‖ ≤ L) (i : Fin 2) :
    (((jacMatrix X x)ᵀ.mulVec d) i) ^ 2 ≤ 2 * L ^ 2 * ∑ j : Fin 2, d j ^ 2 := by
  have hentry (j : Fin 2) : |jacMatrix X x j i| ≤ L := by
    change ‖fderiv ℝ X x (basisVec i) j‖ ≤ L
    have hcoord := norm_le_pi_norm (fderiv ℝ X x (basisVec i)) j
    have happly := (fderiv ℝ X x).le_opNorm (basisVec i)
    have hb : ‖basisVec i‖ = 1 := by simp [basisVec, Pi.norm_single]
    rw [hb, mul_one] at happly
    exact hcoord.trans (happly.trans hX)
  simpa only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Fin.sum_univ_two] using
    two_coordinate_column_square_le (d 0) (d 1) (hentry 0) (hentry 1)

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
namespace AVRegularity.Construction.Preservation.Buffer

/-! Moving tests for an equation with an integrable value source and divergence flux.
The dual representative is obtained from the actual sources by adjoints. -/

open CycleEvolution

variable {F H V : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem flux_weak_curve_moving_test_increment {a b : ℝ} (hab : a ≤ b)
    (J : F →L[ℝ] H) (G : F →L[ℝ] V)
    (u source : ℝ → H) (flux : ℝ → V)
    (hs : IntervalIntegrable source volume a b)
    (hf : IntervalIntegrable flux volume a b)
    (hweak : ∀ t ∈ Icc a b, ∀ z : F,
      inner ℝ (u t) (J z) - inner ℝ (u a) (J z) =
        ∫ r in a..t, inner ℝ (source r) (J z) - inner ℝ (flux r) (G z))
    (z dz : ℝ → F) (hz : StrongTimeRegularity a b z dz) :
    inner ℝ (u b) (J (z b)) - inner ℝ (u a) (J (z a)) =
      ∫ t in a..b, (inner ℝ (source t) (J (z t)) - inner ℝ (flux t) (G (z t))) +
        inner ℝ (u t) (J (dz t)) := by
  let g : ℝ → F := fun t => J.adjoint (source t) - G.adjoint (flux t)
  have hg : IntervalIntegrable g volume a b := by
    exact ⟨(J.adjoint.integrable_comp hs.1).sub (G.adjoint.integrable_comp hf.1),
      (J.adjoint.integrable_comp hs.2).sub (G.adjoint.integrable_comp hf.2)⟩
  have hw : ∀ t ∈ Icc a b, ∀ q : F,
      inner ℝ (u t) (J q) - inner ℝ (u a) (J q) = ∫ r in a..t, inner ℝ (g r) q := by
    intro t ht q
    simpa only [g, inner_sub_left, ContinuousLinearMap.adjoint_inner_left] using hweak t ht q
  simpa only [g, inner_sub_left, ContinuousLinearMap.adjoint_inner_left] using
    weak_curve_moving_test_increment hab J u g hg hw z dz hz

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization Set
namespace AVRegularity.Construction.Preservation.Buffer

/-! Two successive scalar identity theorems continue a real base-label identity. -/

theorem holomorphic_two_label_eqOn_of_real_eq
    (R : ℝ) (hR : 0 < R) {f g : (Fin 2 → ℂ) → ℂ}
    (hf : DifferentiableOn ℂ f {Z : Fin 2 → ℂ | ∑ a, |(Z a).im| < R})
    (hg : DifferentiableOn ℂ g {Z : Fin 2 → ℂ | ∑ a, |(Z a).im| < R})
    (he : ∀ Y : Vec 2, f (fun a => (Y a : ℂ)) = g (fun a => (Y a : ℂ))) :
    EqOn f g {Z : Fin 2 → ℂ | ∑ a, |(Z a).im| < R} := by
  have hline (c : Fin 2 → ℂ) (i : Fin 2) :
      Differentiable ℂ (fun z => Function.update c i z) := by
    intro z
    exact (hasFDerivAt_update c z).differentiableAt
  have hfirst (y : ℝ) (z : ℂ) (hz : |z.im| < R) :
      f (Function.update (fun _ : Fin 2 => (y : ℂ)) 0 z) =
        g (Function.update (fun _ : Fin 2 => (y : ℂ)) 0 z) := by
    have hm : MapsTo (fun z => Function.update (fun _ : Fin 2 => (y : ℂ)) 0 z)
        {z : ℂ | |z.im| < R} {Z : Fin 2 → ℂ | ∑ a, |(Z a).im| < R} := by
      intro z hz
      simpa only [mem_ofPred_eq, Fin.sum_univ_two, Function.update_self,
        Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0), Complex.ofReal_im,
        abs_zero, add_zero] using hz
    have hfg := holomorphic_eqOn_strip_of_real_eq R hR
      (hf.comp (hline (fun _ => (y : ℂ)) 0).differentiableOn hm)
      (hg.comp (hline (fun _ => (y : ℂ)) 0).differentiableOn hm) (fun r => by
        have hh := he (Function.update (fun _ : Fin 2 => y) 0 r)
        have heq : (fun a => ((Function.update (fun _ : Fin 2 => y) 0 r) a : ℂ)) =
            Function.update (fun _ : Fin 2 => (y : ℂ)) 0 (r : ℂ) := by
          funext a
          by_cases ha : a = 0
          · subst a
            simp only [Function.update_self]
          · simp only [Function.update_of_ne ha]
        rw [heq] at hh
        exact hh)
    exact hfg hz
  intro Z hZ
  have hs : |(Z 0).im| + |(Z 1).im| < R := by
    simpa only [mem_ofPred_eq, Fin.sum_univ_two] using hZ
  have hR' : 0 < R - |(Z 0).im| := by
    linarith only [hs, abs_nonneg (Z 1).im]
  have hm : MapsTo (fun z => Function.update Z 1 z)
      {z : ℂ | |z.im| < R - |(Z 0).im|}
      {Z : Fin 2 → ℂ | ∑ a, |(Z a).im| < R} := by
    intro z hz
    change |z.im| < R - |(Z 0).im| at hz
    change (∑ a, |((Function.update Z 1 z) a).im|) < R
    simp only [Fin.sum_univ_two, Function.update_self,
      Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
    linarith only [hz]
  have hfg := holomorphic_eqOn_strip_of_real_eq (R - |(Z 0).im|) hR'
    (hf.comp (hline Z 1).differentiableOn hm)
    (hg.comp (hline Z 1).differentiableOn hm) (fun r => by
      have hh := hfirst r (Z 0) (by linarith only [hR'])
      have heq : Function.update (fun _ : Fin 2 => (r : ℂ)) 0 (Z 0) =
          Function.update Z 1 (r : ℂ) := by
        funext a
        fin_cases a
        · change Z 0 = Function.update Z 1 (r : ℂ) 0
          rw [Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
        · change Function.update (fun _ : Fin 2 => (r : ℂ)) 0 (Z 0) 1 = (r : ℂ)
          rw [Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
      rw [heq] at hh
      exact hh)
  have hh := hfg (show |(Z 1).im| < R - |(Z 0).im| by linarith only [hs])
  simpa only [Function.comp_apply, Function.update_eq_self] using hh

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization Complex Set
namespace AVRegularity.Construction.Preservation.Buffer

/-! Bounded smooth kernels for the literal two-coordinate Cauchy representation. -/

def localizedCauchyKernel (R : ℝ) (χ : Vec 2 → Vec 2) : (ℝ × ℝ) × Vec 2 → ℂ :=
  fun a => (circleMap 0 R a.1.1 - (χ a.2 0 : ℂ))⁻¹ *
    (circleMap 0 R a.1.2 - (χ a.2 1 : ℂ))⁻¹

theorem localized_cauchy_denominator_ne_zero
    (R : ℝ) (hR : 0 < R) (χ : Vec 2 → Vec 2)
    (hb : ∀ x, ‖χ x‖ ≤ R / 2) (θ : ℝ) (x : Vec 2) (a : Fin 2) :
    circleMap 0 R θ - (χ x a : ℂ) ≠ 0 := by
  intro he
  have heq := sub_eq_zero.mp he
  have hcoord : ‖(χ x a : ℂ)‖ ≤ R / 2 := by
    rw [Complex.norm_real]
    exact (norm_le_pi_norm (χ x) a).trans (hb x)
  have hh : R ≤ R / 2 := by
    calc
      R = ‖circleMap 0 R θ‖ := by rw [norm_circleMap_zero, abs_of_pos hR]
      _ = ‖(χ x a : ℂ)‖ := congrArg norm heq
      _ ≤ R / 2 := hcoord
  linarith only [hh, hR]

theorem localized_cauchy_kernel_contDiff
    (R : ℝ) (hR : 0 < R) (χ : Vec 2 → Vec 2)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hb : ∀ x, ‖χ x‖ ≤ R / 2) :
    ContDiff ℝ (⊤ : ℕ∞) (localizedCauchyKernel R χ) := by
  have hc (a : Fin 2) : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : (ℝ × ℝ) × Vec 2 => (χ x.2 a : ℂ)) := by
    exact Complex.ofRealCLM.contDiff.comp (contDiff_pi.mp (hχ.comp contDiff_snd) a)
  have hd₀ : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : (ℝ × ℝ) × Vec 2 => circleMap 0 R x.1.1 - (χ x.2 0 : ℂ)) :=
    ((contDiff_circleMap 0 R).comp (contDiff_fst.fst)).sub (hc 0)
  have hd₁ : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : (ℝ × ℝ) × Vec 2 => circleMap 0 R x.1.2 - (χ x.2 1 : ℂ)) :=
    ((contDiff_circleMap 0 R).comp (contDiff_fst.snd)).sub (hc 1)
  exact (hd₀.inv (fun x => localized_cauchy_denominator_ne_zero R hR χ hb x.1.1 x.2 0)).mul
    (hd₁.inv (fun x => localized_cauchy_denominator_ne_zero R hR χ hb x.1.2 x.2 1))

theorem localized_cauchy_kernel_exists_uniform_jet_bound
    (R : ℝ) (hR : 0 < R) (χ : Vec 2 → Vec 2)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hb : ∀ x, ‖χ x‖ ≤ R / 2)
    (hzero : χ 0 = 0) (hout : ∀ x, R / 2 ≤ ‖x‖ → χ x = 0) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi),
      ∀ φ ∈ Icc (0 : ℝ) (2 * Real.pi), ∀ x : Vec 2,
        ‖iteratedFDeriv ℝ j (fun y => localizedCauchyKernel R χ ((θ, φ), y)) x‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := compact_parameter_exists_slice_jet_bound
    (localizedCauchyKernel R χ) (localized_cauchy_kernel_contDiff R hR χ hχ hb)
    (Icc (0 : ℝ) (2 * Real.pi) ×ˢ Icc (0 : ℝ) (2 * Real.pi))
    (isCompact_Icc.prod isCompact_Icc) (R / 2) (by positivity)
    (fun p _ x hx => by simp only [localizedCauchyKernel, hout x hx, hzero]) j
  exact ⟨C, hC, fun θ hθ φ hφ x => hbound (θ, φ) ⟨hθ, hφ⟩ x⟩

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public section
open MeasureTheory Set
namespace AVRegularity.Construction.Preservation.Buffer

/-! Integration by parts for the time weights of the molecular buffer. -/

theorem weightedTimeEnergy {T c r M : ℝ} {E D R W : ℝ → ℝ}
    (hT : 0 ≤ T) (hE : AbsolutelyContinuousOnInterval E 0 T)
    (hW : ContDiff ℝ 1 W) (hW₀ : W 0 = 0)
    (hWpos : ∀ t ∈ Icc 0 T, 0 ≤ W t)
    (hDWpos : ∀ t ∈ Icc 0 T, 0 ≤ deriv W t)
    (hD : IntervalIntegrable D volume 0 T) (hR : IntervalIntegrable R volume 0 T)
    (henergy : ∀ᵐ t ∂volume.restrict (Icc 0 T), deriv E t + c * D t ≤ 0)
    (hshift : ∀ t ∈ Icc 0 T, E t ≤ M + r ^ 2 * R t) :
    W T * E T + c * (∫ t in 0..T, W t * D t) ≤
      W T * M + r ^ 2 * (∫ t in 0..T, deriv W t * R t) := by
  have hacW := hW.contDiffOn.absolutelyContinuousOnInterval (a := 0) (b := T)
  have hw : ContinuousOn W (uIcc 0 T) := hW.continuous.continuousOn
  have hdw : ContinuousOn (deriv W) (uIcc 0 T) := (hW.continuous_deriv le_rfl).continuousOn
  have heint := hE.intervalIntegrable_deriv.continuousOn_mul hw
  have hdint := hD.continuousOn_mul hw
  have hineq : ∀ᵐ t ∂volume.restrict (Icc 0 T),
      W t * deriv E t + c * (W t * D t) ≤ 0 := by
    filter_upwards [henergy, ae_restrict_mem measurableSet_Icc] with t ht htI
    have hh := mul_le_mul_of_nonneg_left ht (hWpos t htI)
    simpa only [mul_add, mul_zero, mul_left_comm] using hh
  have hi := intervalIntegral.integral_mono_ae_restrict hT (heint.add (hdint.const_mul c))
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 T) hineq
  rw [intervalIntegral.integral_add heint (hdint.const_mul c),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_zero,
    hacW.integral_mul_deriv_eq_deriv_mul hE, hW₀, zero_mul, sub_zero] at hi
  have hde := (hE.continuousOn.intervalIntegrable (μ := volume)).continuousOn_mul hdw
  have hdr := hR.continuousOn_mul hdw
  have hdc := hacW.intervalIntegrable_deriv.mul_const M
  have hcompare : ∀ᵐ t ∂volume.restrict (Icc 0 T),
      deriv W t * E t ≤ deriv W t * M + r ^ 2 * (deriv W t * R t) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hh := mul_le_mul_of_nonneg_left (hshift t ht) (hDWpos t ht)
    simpa only [mul_add, mul_left_comm] using hh
  have hc := intervalIntegral.integral_mono_ae_restrict hT hde
    (hdc.add (hdr.const_mul (r ^ 2))) hcompare
  rw [intervalIntegral.integral_add hdc (hdr.const_mul (r ^ 2)),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
    hacW.integral_deriv_eq_sub, hW₀, sub_zero] at hc
  linarith only [hi, hc]

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization Set
namespace AVRegularity.Construction.Preservation.Buffer

/-! The native real period continues to every complex base label in its carrier strip. -/

theorem phase_periodic_on_complex_base_of_real_periodic
    (R : ℝ) (hR : 0 < R) (B : (Fin 2 → ℂ) → ℝ → ℂ)
    (hB : ∀ s, DifferentiableOn ℂ (fun Z => B Z s)
      {Z : Fin 2 → ℂ | ∑ a, |(Z a).im| < R})
    (hp : ∀ Y : Vec 2, Function.Periodic (fun s => B (fun a => (Y a : ℂ)) s) 1)
    (Z : Fin 2 → ℂ) (hZ : (∑ a, |(Z a).im|) < R) :
    Function.Periodic (B Z) 1 := by
  intro s
  exact holomorphic_two_label_eqOn_of_real_eq R hR (hB (s + 1)) (hB s)
    (fun Y => hp Y s) hZ

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization Complex Set Metric
namespace AVRegularity.Construction.Preservation.Buffer

/-! Periodicity extends compact-angle kernel bounds to every real angle. -/

theorem circleMap_exists_compact_angle (R θ : ℝ) :
    ∃ φ ∈ Icc (0 : ℝ) (2 * Real.pi), circleMap 0 R φ = circleMap 0 R θ := by
  have hm : circleMap 0 R θ ∈ sphere 0 |R| := by
    rw [← range_circleMap]
    exact mem_range_self θ
  rw [← image_circleMap_Ioc] at hm
  obtain ⟨φ, hφ, he⟩ := hm
  exact ⟨φ, ⟨hφ.1.le, hφ.2⟩, he⟩

theorem localized_cauchy_kernel_exists_global_jet_bound
    (R : ℝ) (hR : 0 < R) (χ : Vec 2 → Vec 2)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hb : ∀ x, ‖χ x‖ ≤ R / 2)
    (hzero : χ 0 = 0) (hout : ∀ x, R / 2 ≤ ‖x‖ → χ x = 0) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ φ : ℝ, ∀ x : Vec 2,
      ‖iteratedFDeriv ℝ j (fun y => localizedCauchyKernel R χ ((θ, φ), y)) x‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := localized_cauchy_kernel_exists_uniform_jet_bound
    R hR χ hχ hb hzero hout j
  refine ⟨C, hC, ?_⟩
  intro θ φ x
  obtain ⟨θ', hθ', heθ⟩ := circleMap_exists_compact_angle R θ
  obtain ⟨φ', hφ', heφ⟩ := circleMap_exists_compact_angle R φ
  have he : (fun y => localizedCauchyKernel R χ ((θ, φ), y)) =
      (fun y => localizedCauchyKernel R χ ((θ', φ'), y)) := by
    funext y
    simp only [localizedCauchyKernel, heθ, heφ]
  rw [he]
  exact hbound θ' hθ' φ' hφ' x

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public section
open MeasureTheory Set
namespace AVRegularity.Construction.Preservation.Buffer

/-! Polynomial time weights erase the initial high derivatives. -/

theorem deriv_power_time (j : ℕ) (t : ℝ) :
    deriv (fun x : ℝ => x ^ (j + 1)) t = (j + 1 : ℕ) * t ^ j := by
  have hd := ((hasDerivAt_id t).pow (j + 1)).deriv
  have he : (id : ℝ → ℝ) ^ (j + 1) = (fun x : ℝ => x ^ (j + 1)) := by
    funext x
    exact Pi.pow_apply id (j + 1) x
  rw [he] at hd
  simpa only [Nat.add_sub_cancel, mul_one, id_eq] using hd

theorem powerTimeEnergy {T c r M : ℝ} {E D R : ℝ → ℝ} (j : ℕ)
    (hT : 0 ≤ T) (hE : AbsolutelyContinuousOnInterval E 0 T)
    (hD : IntervalIntegrable D volume 0 T) (hR : IntervalIntegrable R volume 0 T)
    (henergy : ∀ᵐ t ∂volume.restrict (Icc 0 T), deriv E t + c * D t ≤ 0)
    (hshift : ∀ t ∈ Icc 0 T, E t ≤ M + r ^ 2 * R t) :
    T ^ (j + 1) * E T + c * (∫ t in 0..T, t ^ (j + 1) * D t) ≤
      T ^ (j + 1) * M + (j + 1 : ℕ) * r ^ 2 * (∫ t in 0..T, t ^ j * R t) := by
  have hp : ContDiff ℝ 1 (fun t : ℝ => t ^ (j + 1)) := by fun_prop
  have hi := weightedTimeEnergy hT hE hp (by simp only [zero_pow (Nat.succ_ne_zero j)])
    (fun t ht => pow_nonneg ht.1 _) (fun t ht => by
      rw [deriv_power_time]
      exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ht.1 _)) hD hR henergy hshift
  simp only [deriv_power_time] at hi
  rw [show (fun t : ℝ => (j + 1 : ℕ) * t ^ j * R t) =
      (fun t => (j + 1 : ℕ) * (t ^ j * R t)) by funext t; ring,
    intervalIntegral.integral_const_mul] at hi
  exact hi.trans_eq (by ring)

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
namespace AVRegularity.Construction.Preservation.Buffer

/-! Material cancellation almost everywhere in time suffices for the actual weak evolution. -/

open CycleEvolution
variable {F H V : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem transported_pairing_increment_bound_ae {a b L : ℝ} (hab : a ≤ b)
    (J : F →L[ℝ] H) (G : F →L[ℝ] V)
    (u source : ℝ → H) (flux : ℝ → V)
    (hs : IntervalIntegrable source volume a b)
    (hf : IntervalIntegrable flux volume a b)
    (hweak : ∀ t ∈ Icc a b, ∀ z : F,
      inner ℝ (u t) (J z) - inner ℝ (u a) (J z) =
        ∫ r in a..t, inner ℝ (source r) (J z) - inner ℝ (flux r) (G z))
    (z dz : ℝ → F) (hz : StrongTimeRegularity a b z dz)
    (hcancel : ∀ᵐ t ∂volume.restrict (Icc a b),
      inner ℝ (source t) (J (z t)) + inner ℝ (u t) (J (dz t)) = 0)
    (hgrad : ∀ t ∈ Icc a b, ‖G (z t)‖ ≤ L) :
    |inner ℝ (u b) (J (z b)) - inner ℝ (u a) (J (z a))| ≤
      L * ∫ t in a..b, ‖flux t‖ := by
  rw [flux_weak_curve_moving_test_increment hab J G u source flux hs hf hweak z dz hz]
  have hbnd : ∀ᵐ t ∂volume, t ∈ Ioc a b →
      ‖(inner ℝ (source t) (J (z t)) - inner ℝ (flux t) (G (z t))) +
        inner ℝ (u t) (J (dz t))‖ ≤ L * ‖flux t‖ := by
    have hc := (ae_restrict_iff' measurableSet_Icc).mp hcancel
    filter_upwards [hc] with t hct ht
    have htc : t ∈ Icc a b := ⟨ht.1.le, ht.2⟩
    have he : (inner ℝ (source t) (J (z t)) - inner ℝ (flux t) (G (z t))) +
        inner ℝ (u t) (J (dz t)) = -inner ℝ (flux t) (G (z t)) := by
      linarith [hct htc]
    rw [he, norm_neg, Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans
      ((mul_le_mul_of_nonneg_left (hgrad t htc) (norm_nonneg _)).trans_eq (mul_comm _ _))
  have hb := intervalIntegral.norm_integral_le_of_norm_le hab hbnd (hf.norm.const_mul L)
  simpa only [Real.norm_eq_abs, intervalIntegral.integral_const_mul] using hb

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! The coefficient seminorm reads spatial fields only on its declared time window. -/

variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem coefficientSeminorm_window_congr (ρ : ℝ) (n : ℕ) (a b : ℝ)
    (A B : ℝ → Vec 2 → U →L[ℝ] V)
    (h : ∀ t ∈ Set.Icc a b, A t = B t) :
    coefficientSeminorm ρ n a b A = coefficientSeminorm ρ n a b B := by
  unfold coefficientSeminorm
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply iSup_congr
  intro t
  apply iSup_congr
  intro ht
  rw [h t ht]

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public section
open MeasureTheory Set
namespace AVRegularity.Construction.Preservation.Buffer

/-! Dimension-free constants in the molecular weighted-energy induction. -/

def bufferEnergyCost : ℕ → ℝ
  | 0 => 1
  | j + 1 => 1 + (j + 1 : ℕ) * bufferEnergyCost j

theorem bufferEnergyCost_nonneg (j : ℕ) : 0 ≤ bufferEnergyCost j := by
  induction j with
  | zero => exact zero_le_one
  | succ j hj => exact add_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _) hj)

theorem weighted_energy_induction_step {b t r c M C I X : ℝ} (j : ℕ)
    (hb : 0 ≤ b) (ht : 0 ≤ t) (htb : t ≤ b) (hM : 0 ≤ M) (hI : 0 ≤ I)
    (hr : r ^ 2 ≤ c * b)
    (hprev : c * I ≤ C * b ^ j * M)
    (hnext : X ≤ t ^ (j + 1) * M + (j + 1 : ℕ) * r ^ 2 * I) :
    X ≤ (1 + (j + 1 : ℕ) * C) * b ^ (j + 1) * M := by
  have hbase := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht htb (j + 1)) hM
  have hi : r ^ 2 * I ≤ C * b ^ (j + 1) * M := by
    calc
      r ^ 2 * I ≤ (c * b) * I := mul_le_mul_of_nonneg_right hr hI
      _ = b * (c * I) := by ring
      _ ≤ b * (C * b ^ j * M) := mul_le_mul_of_nonneg_left hprev hb
      _ = C * b ^ (j + 1) * M := by rw [pow_succ]; ring
  have hh := add_le_add hbase (mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg (j + 1)))
  calc
    X ≤ t ^ (j + 1) * M + (j + 1 : ℕ) * r ^ 2 * I := hnext
    _ = t ^ (j + 1) * M + (j + 1 : ℕ) * (r ^ 2 * I) := by ring
    _ ≤ b ^ (j + 1) * M + (j + 1 : ℕ) * (C * b ^ (j + 1) * M) := hh
    _ = (1 + (j + 1 : ℕ) * C) * b ^ (j + 1) * M := by ring

/-! The finite weighted-energy induction for rough initial data. -/

theorem molecular_weighted_energy {K : ℕ} {b c r M : ℝ} {E D : ℕ → ℝ → ℝ}
    (hb : 0 ≤ b) (hc : 0 ≤ c) (hM : 0 ≤ M) (hr : r ^ 2 ≤ c * b)
    (hE : ∀ j ≤ K, AbsolutelyContinuousOnInterval (E j) 0 b)
    (hD : ∀ j ≤ K, IntervalIntegrable (D j) volume 0 b)
    (hEp : ∀ j ≤ K, ∀ t ∈ Icc 0 b, 0 ≤ E j t)
    (hDp : ∀ j ≤ K, ∀ t ∈ Icc 0 b, 0 ≤ D j t)
    (hdiff : ∀ j ≤ K, ∀ᵐ t ∂volume.restrict (Icc 0 b), deriv (E j) t + c * D j t ≤ 0)
    (hshift : ∀ j, j + 1 ≤ K → ∀ t ∈ Icc 0 b, E (j + 1) t ≤ E 0 t + r ^ 2 * D j t)
    (hinit : E 0 0 ≤ M) :
    ∀ j ≤ K, ∀ t ∈ Icc 0 b,
      t ^ j * E j t + c * (∫ τ in 0..t, τ ^ j * D j τ) ≤ bufferEnergyCost j * b ^ j * M := by
  have hzero (t : ℝ) (ht : t ∈ Icc 0 b) :
      E 0 t + c * (∫ τ in 0..t, D 0 τ) ≤ M := by
    have he := KernelEnergy.homogeneousTimeEnergy hb ⟨le_rfl, hb⟩ ht ht.1
      (hE 0 (Nat.zero_le K)) (hD 0 (Nat.zero_le K)) (hdiff 0 (Nat.zero_le K))
    rw [← intervalIntegral.integral_of_le ht.1] at he
    exact he.trans hinit
  have hzero_le (t : ℝ) (ht : t ∈ Icc 0 b) : E 0 t ≤ M := by
    have hi : 0 ≤ ∫ τ in 0..t, D 0 τ := intervalIntegral.integral_nonneg ht.1
      (fun τ hτ => hDp 0 (Nat.zero_le K) τ ⟨hτ.1, hτ.2.trans ht.2⟩)
    exact (le_add_of_nonneg_right (mul_nonneg hc hi)).trans (hzero t ht)
  intro j
  induction j with
  | zero =>
    intro _hj t ht
    simpa only [bufferEnergyCost, pow_zero, one_mul, mul_one] using hzero t ht
  | succ j ih =>
    intro hj t ht
    have hj' : j ≤ K := (Nat.le_succ j).trans hj
    have hsub : uIcc 0 t ⊆ uIcc 0 b := by
      rw [uIcc_of_le ht.1, uIcc_of_le hb]
      exact Icc_subset_Icc le_rfl ht.2
    have hsub' : Icc 0 t ⊆ Icc 0 b := Icc_subset_Icc le_rfl ht.2
    have he := powerTimeEnergy j ht.1 ((hE (j + 1) hj).mono hsub)
      ((hD (j + 1) hj).mono_set hsub) ((hD j hj').mono_set hsub)
      (ae_restrict_of_ae_restrict_of_subset hsub' (hdiff (j + 1) hj))
      (fun τ hτ => (hshift j hj τ (hsub' hτ)).trans
        (add_le_add (hzero_le τ (hsub' hτ)) (le_refl _)))
    have hI : 0 ≤ ∫ τ in 0..t, τ ^ j * D j τ := intervalIntegral.integral_nonneg ht.1
      (fun τ hτ => mul_nonneg (pow_nonneg hτ.1 _) (hDp j hj' τ (hsub' hτ)))
    have hp : c * (∫ τ in 0..t, τ ^ j * D j τ) ≤ bufferEnergyCost j * b ^ j * M :=
      (le_add_of_nonneg_left (mul_nonneg (pow_nonneg ht.1 _) (hEp j hj' t ht))).trans
        (ih hj' t ht)
    have hbudget := weighted_energy_induction_step j hb ht.1 ht.2 hM hI hr hp
      (show t ^ (j + 1) * E (j + 1) t + c * (∫ τ in 0..t, τ ^ (j + 1) * D (j + 1) τ) ≤
        t ^ (j + 1) * M + (j + 1 : ℕ) * r ^ 2 * (∫ τ in 0..t, τ ^ j * D j τ) from he)
    simpa only [bufferEnergyCost] using hbudget

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Buffer

/-! Copy-adapt the existing coarse jet H1 identification for an actual scalar carrier. -/

theorem scalar_first_jet_periodicH1 {K : ℕ} (hK : 1 ≤ K) (U : TorusHk K ℝ) :
    IsPeriodicH1With (U.toFunction.jet (valueIndex2 K))
      (fun x i => U.toFunction.jet
        ⟨⟨1, Nat.lt_succ_of_le hK⟩, fun _ : Fin 1 => i⟩ x) := by
  have hraw := U.toFunction.hasPeriodicWeakJet
  let j : Fin K := ⟨0, by omega⟩
  refine ⟨?_, ?_, hraw.2.1 _, fun i => hraw.2.1 _, ?_⟩
  · exact hraw.1 _
  · intro n x
    funext i
    exact hraw.1 _ n x
  · intro i
    have h := hraw.2.2 j Fin.elim0 i (1 : ℝ)
    have hw : (Fin.snoc Fin.elim0 i : Fin 1 → Fin 2) = fun _ => i := by
      funext z
      fin_cases z
      rfl
    simpa only [Real.inner_apply, one_mul, mul_one, j, lowerIndex2, lowerIndex,
      nextIndex2, nextIndex, valueIndex2, valueIndex, hw, Nat.zero_add, Fin.mk_zero] using h

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public section
open MeasureTheory Set
namespace AVRegularity.Construction.Preservation.Buffer

/-! The weighted induction gives uniform bounds at and after the molecular buffer. -/

theorem molecular_energy_at_buffer {K : ℕ} {b c r M : ℝ} {E D : ℕ → ℝ → ℝ}
    (hb : 0 < b) (hc : 0 ≤ c) (hM : 0 ≤ M) (hr : r ^ 2 ≤ c * b)
    (hE : ∀ j ≤ K, AbsolutelyContinuousOnInterval (E j) 0 b)
    (hD : ∀ j ≤ K, IntervalIntegrable (D j) volume 0 b)
    (hEp : ∀ j ≤ K, ∀ t ∈ Icc 0 b, 0 ≤ E j t)
    (hDp : ∀ j ≤ K, ∀ t ∈ Icc 0 b, 0 ≤ D j t)
    (hdiff : ∀ j ≤ K, ∀ᵐ t ∂volume.restrict (Icc 0 b), deriv (E j) t + c * D j t ≤ 0)
    (hshift : ∀ j, j + 1 ≤ K → ∀ t ∈ Icc 0 b, E (j + 1) t ≤ E 0 t + r ^ 2 * D j t)
    (hinit : E 0 0 ≤ M) : ∀ j ≤ K, E j b ≤ bufferEnergyCost j * M := by
  intro j hj
  have hi := molecular_weighted_energy hb.le hc hM hr hE hD hEp hDp hdiff hshift hinit j hj b
    ⟨hb.le, le_rfl⟩
  have hgrad : 0 ≤ ∫ τ in 0..b, τ ^ j * D j τ := intervalIntegral.integral_nonneg hb.le
    (fun τ hτ => mul_nonneg (pow_nonneg hτ.1 _) (hDp j hj τ hτ))
  have henergy := (le_add_of_nonneg_right (mul_nonneg hc hgrad)).trans hi
  have hp : 0 < b ^ j := pow_pos hb j
  apply (mul_le_mul_iff_right₀ hp).mp
  exact henergy.trans_eq (by ring)

theorem molecular_energy_after_buffer {K : ℕ} {b T c r M : ℝ} {E D : ℕ → ℝ → ℝ}
    (hb : 0 < b) (hbT : b ≤ T) (hc : 0 ≤ c) (hM : 0 ≤ M) (hr : r ^ 2 ≤ c * b)
    (hE : ∀ j ≤ K, AbsolutelyContinuousOnInterval (E j) 0 T)
    (hD : ∀ j ≤ K, IntervalIntegrable (D j) volume 0 T)
    (hEp : ∀ j ≤ K, ∀ t ∈ Icc 0 T, 0 ≤ E j t)
    (hDp : ∀ j ≤ K, ∀ t ∈ Icc 0 T, 0 ≤ D j t)
    (hdiff : ∀ j ≤ K, ∀ᵐ t ∂volume.restrict (Icc 0 T), deriv (E j) t + c * D j t ≤ 0)
    (hshift : ∀ j, j + 1 ≤ K → ∀ t ∈ Icc 0 b, E (j + 1) t ≤ E 0 t + r ^ 2 * D j t)
    (hinit : E 0 0 ≤ M) : ∀ j ≤ K, ∀ t ∈ Icc b T,
      E j t + c * (∫ τ in b..t, D j τ) ≤ bufferEnergyCost j * M := by
  have hT : 0 ≤ T := hb.le.trans hbT
  have hsub : uIcc 0 b ⊆ uIcc 0 T := by
    rw [uIcc_of_le hb.le, uIcc_of_le hT]
    exact Icc_subset_Icc le_rfl hbT
  have hsub' : Icc 0 b ⊆ Icc 0 T := Icc_subset_Icc le_rfl hbT
  have hat := molecular_energy_at_buffer hb hc hM hr
    (fun j hj => (hE j hj).mono hsub) (fun j hj => (hD j hj).mono_set hsub)
    (fun j hj t ht => hEp j hj t (hsub' ht)) (fun j hj t ht => hDp j hj t (hsub' ht))
    (fun j hj => ae_restrict_of_ae_restrict_of_subset hsub' (hdiff j hj)) hshift hinit
  intro j hj t ht
  have he := KernelEnergy.homogeneousTimeEnergy hT ⟨hb.le, hbT⟩ ⟨hb.le.trans ht.1, ht.2⟩ ht.1
    (hE j hj) (hD j hj) (hdiff j hj)
  rw [← intervalIntegral.integral_of_le ht.1] at he
  exact he.trans (hat j hj)

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public noncomputable section
open Homogenization Complex Metric MeasureTheory
namespace AVRegularity.Construction.Preservation.Buffer

/-! The actual holomorphic base function equals the localized contour integral. -/

theorem localized_double_cauchy_representation
    (R : ℝ) (hR : 0 < R) (χ : Vec 2 → Vec 2)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hb : ∀ x, ‖χ x‖ ≤ R / 2)
    (hzero : χ 0 = 0) (hout : ∀ x, R / 2 ≤ ‖x‖ → χ x = 0)
    (F : ℂ → ℂ → ℂ)
    (h₀ : ∀ z ∈ closedBall 0 R, DiffContOnCl ℂ (fun w => F w z) (ball 0 R))
    (h₁ : ∀ w ∈ closedBall 0 R, DiffContOnCl ℂ (F w) (ball 0 R))
    (hc : Continuous (fun p : ℝ × ℝ => F (circleMap 0 R p.1) (circleMap 0 R p.2)))
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ θ φ : ℝ, ‖F (circleMap 0 R θ) (circleMap 0 R φ)‖ ≤ M)
    (x : Vec 2) :
    F (χ x 0 : ℂ) (χ x 1 : ℂ) =
      ∫ p, cauchyBoundaryCoefficient R F p • localizedCauchyKernel R χ (p, x)
        ∂(cauchyAngleMeasure.prod cauchyAngleMeasure) := by
  let μ := cauchyAngleMeasure.prod cauchyAngleMeasure
  let g := cauchyBoundaryCoefficient R F
  have hg : Measurable g := cauchy_boundary_coefficient_measurable R F hc
  have hk := localized_cauchy_kernel_contDiff R hR χ hχ hb
  have hkm : Measurable (fun p : ℝ × ℝ => localizedCauchyKernel R χ (p, x)) :=
    (hk.continuous.comp (continuous_id.prodMk continuous_const)).measurable
  obtain ⟨C, hC, hCb⟩ := localized_cauchy_kernel_exists_global_jet_bound R hR χ hχ hb hzero hout 0
  have hi : Integrable (fun p : ℝ × ℝ => g p • localizedCauchyKernel R χ (p, x)) μ := by
    apply (integrable_const ((‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ ^ 2 * R ^ 2) * M * C)).mono'
      (hg.smul hkm).aestronglyMeasurable
    exact ae_of_all μ (fun p => by
      change ‖g p • localizedCauchyKernel R χ (p, x)‖ ≤ _
      rw [norm_smul]
      apply mul_le_mul (cauchy_boundary_coefficient_norm_le R hR F M hbound p)
        (by simpa only [norm_iteratedFDeriv_zero] using hCb p.1 p.2 x)
        (norm_nonneg _) (by positivity))
  have he : (fun p : ℝ × ℝ => g p *
      (circleMap 0 R p.1 - (χ x 0 : ℂ))⁻¹ * (circleMap 0 R p.2 - (χ x 1 : ℂ))⁻¹) =
      (fun p => g p • localizedCauchyKernel R χ (p, x)) := by
    funext p
    simp only [localizedCauchyKernel, smul_eq_mul, mul_assoc]
  have hw (a : Fin 2) : (χ x a : ℂ) ∈ ball (0 : ℂ) R := by
    rw [mem_ball, dist_zero_right, Complex.norm_real]
    exact ((norm_le_pi_norm (χ x) a).trans (hb x)).trans_lt (by linarith only [hR])
  rw [double_cauchy_representation F 0 0 R hR h₀ h₁ _ _ (hw 0) (hw 1)]
  rw [double_cauchy_angle_integral_eq R F _ _ (by change Integrable _ μ; rw [he]; exact hi)]
  exact congrArg (fun f : (ℝ × ℝ) → ℂ => ∫ p, f p ∂μ) he

end AVRegularity.Construction.Preservation.Buffer
end
end

section
@[expose] public section
open MeasureTheory Set
namespace AVRegularity.Construction.Preservation.Buffer

/-! The molecular scalar estimate on a physical window with arbitrary start time. -/

theorem molecular_energy_after_buffer_from {K : ℕ} {a b T c r M : ℝ}
    {E D : ℕ → ℝ → ℝ}
    (hb : 0 < b) (hbT : a + b ≤ T) (hc : 0 ≤ c) (hM : 0 ≤ M)
    (hr : r ^ 2 ≤ c * b)
    (hE : ∀ j ≤ K, AbsolutelyContinuousOnInterval (E j) a T)
    (hD : ∀ j ≤ K, IntervalIntegrable (D j) volume a T)
    (hEp : ∀ j ≤ K, ∀ t ∈ Icc a T, 0 ≤ E j t)
    (hDp : ∀ j ≤ K, ∀ t ∈ Icc a T, 0 ≤ D j t)
    (hdiff : ∀ j ≤ K, ∀ᵐ t ∂volume.restrict (Icc a T), deriv (E j) t + c * D j t ≤ 0)
    (hshift : ∀ j, j + 1 ≤ K → ∀ t ∈ Icc a (a + b),
      E (j + 1) t ≤ E 0 t + r ^ 2 * D j t)
    (hinit : E 0 a ≤ M) : ∀ j ≤ K, ∀ t ∈ Icc (a + b) T,
      E j t + c * (∫ τ in (a + b)..t, D j τ) ≤ bufferEnergyCost j * M := by
  have haT : a ≤ T := (le_add_of_nonneg_right hb.le).trans hbT
  have hbT' : b ≤ T - a := by linarith only [hbT]
  have hmap (t : ℝ) (ht : t ∈ Icc 0 (T - a)) : a + t ∈ Icc a T := by
    constructor <;> linarith only [ht.1, ht.2]
  have hd (j : ℕ) (hj : j ≤ K) :
      ∀ᵐ t ∂volume.restrict (Icc 0 (T - a)),
        deriv (fun s => E j (a + s)) t + c * D j (a + t) ≤ 0 := by
    simpa only [deriv_comp_const_add] using ae_time_translate (hdiff j hj)
  have hi := molecular_energy_after_buffer (E := fun j t => E j (a + t))
    (D := fun j t => D j (a + t)) hb hbT' hc hM hr
    (fun j hj => absolutelyContinuous_time_translate haT (hE j hj))
    (fun j hj => by simpa only [sub_self] using (hD j hj).comp_add_left a)
    (fun j hj t ht => hEp j hj (a + t) (hmap t ht))
    (fun j hj t ht => hDp j hj (a + t) (hmap t ht)) hd
    (fun j hj t ht => hshift j hj (a + t)
      ⟨le_add_of_nonneg_right ht.1, add_le_add (le_refl a) ht.2⟩)
    (by simpa only [add_zero] using hinit)
  intro j hj t ht
  have hmem : t - a ∈ Icc b (T - a) := by
    constructor <;> linarith only [ht.1, ht.2]
  have hh := hi j hj (t - a) hmem
  rw [intervalIntegral.integral_comp_add_left] at hh
  have heq : a + (t - a) = t := by ring
  rw [heq] at hh
  exact hh

end AVRegularity.Construction.Preservation.Buffer
end
end
