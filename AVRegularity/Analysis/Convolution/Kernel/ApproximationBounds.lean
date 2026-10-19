-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Analysis.Convolution.Kernel.PulseAxes
public import AVRegularity.Analysis.Convolution.Kernel.PairedSmoothing
import AVRegularity.Analysis.Convolution.Kernel.Commutation.Torus
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Tactic.Monotonicity.Lemmas

@[expose] public section
noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVenhance.Infra.Torus AVenhance.Infra.Parabolic.FourierGalerkin
open scoped Topology
namespace AVRegularity.Analysis.Convolution

/-! Differentiation transferred from literal averages to their kernels. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem torus_pullback_locallyIntegrable (f : Lp E 2 torusMeasure) :
    LocallyIntegrable (fun x : Vec 2 => f (torusQuotient x)) volume := by
  intro x
  let b : ContDiffBump x := ⟨1, 2, by norm_num, by norm_num⟩
  have hg : MemLp (fun y : Vec 2 => ‖f (torusQuotient y)‖) 2
      (volume.restrict AVenhance.unitCube) :=
    ((Lp.memLp f).comp_measurePreserving measurePreserving_torusQuotient_cell).norm
  have hp : AVenhance.IsZ2Periodic (fun y : Vec 2 => ‖f (torusQuotient y)‖) := by
    intro n y
    exact congrArg norm (torus_pullback_periodic f n y)
  have hi := AVenhance.Infra.Parabolic.FourierGalerkin.periodic_compact_pairing_integrable
    hg hp b.continuous b.hasCompactSupport
  have hnorm : IntegrableOn (fun y : Vec 2 => ‖f (torusQuotient y)‖)
      (Metric.ball x 1) volume := by
    apply hi.integrableOn.congr
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy), mul_one]
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x (by norm_num), ?_⟩
  apply (integrable_norm_iff _).mp hnorm
  exact ((Lp.stronglyMeasurable f).comp_measurable
    continuous_torusQuotient.measurable).aestronglyMeasurable.restrict

theorem fderiv_transportedKernel_apply (R : Vec 2 ≃L[ℝ] Vec 2)
    {κ : Vec 2 → ℝ} (hd : ContDiff ℝ (⊤ : ℕ∞) κ) (x v : Vec 2) :
    (fderiv ℝ (transportedKernel R κ) x) v =
      transportedKernel R (fun z => (fderiv ℝ κ z) (R.symm v)) x := by
  have h := ((hd.differentiable (by simp)).differentiableAt.hasFDerivAt.comp x
    R.symm.hasFDerivAt).const_mul |LinearMap.det R.toLinearEquiv.toLinearMap|⁻¹
  have hf := congrArg (fun A : Vec 2 →L[ℝ] ℝ => A v) h.fderiv
  exact hf

omit [CompleteSpace E] in
theorem fderiv_convolution_apply {κ : Vec 2 → ℝ} (hc : HasCompactSupport κ)
    (hd : ContDiff ℝ (⊤ : ℕ∞) κ) {f : Vec 2 → E}
    (hf : LocallyIntegrable f volume) (x v : Vec 2) :
    (fderiv ℝ (convolution κ f (ContinuousLinearMap.lsmul ℝ ℝ) volume) x) v =
      convolution (fun z => (fderiv ℝ κ z) v) f
        (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  let L := ContinuousLinearMap.lsmul ℝ ℝ (E := E)
  have h := hc.hasFDerivAt_convolution_right L.flip hf (hd.of_le (by simp)) x
  have hflip : convolution κ f L volume = convolution f κ L.flip volume :=
    (convolution_flip (f := κ) (g := f) L).symm
  rw [hflip, h.fderiv, convolution_precompR_apply L.flip hf (hc.fderiv ℝ)
    (hd.continuous_fderiv (by simp))]
  exact congrFun (convolution_flip
    (f := fun z => (fderiv ℝ κ z) v) (g := f) L) x

omit [CompleteSpace E] in
theorem fderiv_literalAverage_apply (R : Vec 2 ≃L[ℝ] Vec 2)
    {κ : Vec 2 → ℝ} (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ)
    {f : Vec 2 → E} (hf : LocallyIntegrable f volume) (x v : Vec 2) :
    (fderiv ℝ (fun x => ∫ z : Vec 2, κ z • f (x-R z)) x) v =
      ∫ z : Vec 2, (fderiv ℝ κ z) (R.symm v) • f (x-R z) := by
  have heq : (fun x => ∫ z : Vec 2, κ z • f (x-R z)) =
      convolution (transportedKernel R κ) f (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext x
    exact integral_eq_transported_convolution R κ f x
  rw [heq, fderiv_convolution_apply (hasCompactSupport_transportedKernel R hc)
    (contDiff_transportedKernel R hd) hf]
  simp_rw [fderiv_transportedKernel_apply R hd]
  exact (integral_eq_transported_convolution R
    (fun z => (fderiv ℝ κ z) (R.symm v)) f x).symm

omit [CompleteSpace E] in
theorem contDiff_literalAverage (R : Vec 2 ≃L[ℝ] Vec 2)
    {κ : Vec 2 → ℝ} (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ)
    {f : Vec 2 → E} (hf : LocallyIntegrable f volume) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ z : Vec 2, κ z • f (x-R z)) := by
  have heq : (fun x => ∫ z : Vec 2, κ z • f (x-R z)) =
      convolution (transportedKernel R κ) f (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext x
    exact integral_eq_transported_convolution R κ f x
  rw [heq]
  exact (hasCompactSupport_transportedKernel R hc).contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (contDiff_transportedKernel R hd) hf

theorem integrable_fderiv_apply {κ : Vec 2 → ℝ} (hc : HasCompactSupport κ)
    (hd : ContDiff ℝ (⊤ : ℕ∞) κ) (a : Vec 2) :
    Integrable (fun z => (fderiv ℝ κ z) a) :=
  ((hd.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
    (hc.fderiv_apply (𝕜 := ℝ) a)

theorem averagingOperator_plane_literal_ae (R : Vec 2 ≃L[ℝ] Vec 2)
    {κ : Vec 2 → ℝ} (hκ : Integrable κ) (f : Lp E 2 (volume : Measure (Vec 2))) :
    averagingOperator R.toLinearEquiv.toAddHom R.continuous κ hκ f =ᵐ[volume]
      (fun x => ∫ z : Vec 2, κ z • f (x-R z)) := by
  have h := averagingOperator_ae R.toLinearEquiv.toAddHom R.continuous hκ f
  change averagingOperator R.toLinearEquiv.toAddHom R.continuous κ hκ f =ᵐ[volume]
    fun x => ∫ z : Vec 2, κ z • f (x-R.toLinearEquiv.toAddHom z) at h
  filter_upwards [h] with x hx
  apply hx.trans
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    congr 2

theorem averagingOperator_torus_cover_ae (R : Vec 2 ≃L[ℝ] Vec 2)
    {κ : Vec 2 → ℝ} (hκ : Integrable κ) (f : Lp E 2 torusMeasure) :
    (fun x => averagingOperator (torusQuotient.comp R.toLinearEquiv.toAddHom)
      (continuous_torusQuotient.comp R.continuous) κ hκ f (torusQuotient x)) =ᵐ[volume]
      (fun x => ∫ z : Vec 2, κ z • f (torusQuotient (x-R z))) := by
  have h := ae_torusQuotient (averagingOperator_ae
    (torusQuotient.comp R.toLinearEquiv.toAddHom)
    (continuous_torusQuotient.comp R.continuous) hκ f)
  filter_upwards [h] with x hx
  change averagingOperator (torusQuotient.comp R.toLinearEquiv.toAddHom)
    (continuous_torusQuotient.comp R.continuous) κ hκ f (torusQuotient x) =
      ∫ z : Vec 2, κ z • f (torusQuotient x - torusQuotient (R.toLinearEquiv.toAddHom z)) at hx
  apply hx.trans
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    change κ z • f (torusQuotient x - torusQuotient (R.toLinearEquiv.toAddHom z)) =
      κ z • f (torusQuotient (x-R z))
    have hR : R.toLinearEquiv.toAddHom z = R z := rfl
    rw [hR, map_sub]

theorem averagingOperator_hasWeakDirectionalDeriv_kernel (R : Vec 2 ≃L[ℝ] Vec 2)
    {κ : Vec 2 → ℝ} (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ)
    (f : Lp E 2 (volume : Measure (Vec 2))) (v : Vec 2) (e : E) :
    HasWeakDirectionalDeriv v
      (fun x => inner ℝ e (averagingOperator R.toLinearEquiv.toAddHom R.continuous
        κ (hd.continuous.integrable_of_hasCompactSupport hc) f x))
      (fun x => inner ℝ e (averagingOperator R.toLinearEquiv.toAddHom R.continuous
        (fun z => (fderiv ℝ κ z) (R.symm v))
        (integrable_fderiv_apply hc hd _) f x)) := by
  have h := hasWeakDirectionalDeriv_of_contDiff
    ((InnerProductSpace.toDual ℝ E e).contDiff.comp
      ((contDiff_literalAverage R hc hd
        ((Lp.memLp f).locallyIntegrable (by norm_num))).of_le (by simp))) v
  have hderiv (x : Vec 2) :
      (fderiv ℝ (fun x => inner ℝ e (∫ z : Vec 2, κ z • f (x-R z))) x) v =
        inner ℝ e (∫ z : Vec 2, (fderiv ℝ κ z) (R.symm v) • f (x-R z)) := by
    have hh := (InnerProductSpace.toDual ℝ E e).hasFDerivAt.comp x
      ((contDiff_literalAverage R hc hd
        ((Lp.memLp f).locallyIntegrable (by norm_num))).differentiable (by simp) |>.differentiableAt.hasFDerivAt)
    have hh' := congrArg (fun A : Vec 2 →L[ℝ] ℝ => A v) hh.fderiv
    change (fderiv ℝ (fun x => inner ℝ e (∫ z : Vec 2, κ z • f (x-R z))) x) v =
      inner ℝ e ((fderiv ℝ (fun x => ∫ z : Vec 2, κ z • f (x-R z)) x) v) at hh'
    rw [fderiv_literalAverage_apply R hc hd ((Lp.memLp f).locallyIntegrable (by norm_num))] at hh'
    exact hh'
  have h' : HasWeakDirectionalDeriv v
      (fun x => inner ℝ e (∫ z : Vec 2, κ z • f (x-R z)))
      (fun x => inner ℝ e (∫ z : Vec 2, (fderiv ℝ κ z) (R.symm v) • f (x-R z))) := by
    change HasWeakDirectionalDeriv v
      (fun x => inner ℝ e (∫ z : Vec 2, κ z • f (x-R z)))
      (fun x => (fderiv ℝ (fun x => inner ℝ e (∫ z : Vec 2, κ z • f (x-R z))) x) v) at h
    simpa only [hderiv] using h
  apply hasWeakDirectionalDeriv_congr_ae _ _ h'
  · simpa only [Function.comp_def] using
      (averagingOperator_plane_literal_ae R
        (hd.continuous.integrable_of_hasCompactSupport hc) f).symm.fun_comp (inner ℝ e)
  · simpa only [Function.comp_def] using
      (averagingOperator_plane_literal_ae R (integrable_fderiv_apply hc hd (R.symm v)) f).symm.fun_comp
        (inner ℝ e)

theorem averagingOperator_hasWeakDirectionalDeriv_kernel_torus (R : Vec 2 ≃L[ℝ] Vec 2)
    {κ : Vec 2 → ℝ} (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ)
    (f : Lp E 2 torusMeasure) (v : Vec 2) (e : E) :
    HasWeakDirectionalDeriv v
      (fun x => inner ℝ e (averagingOperator (torusQuotient.comp R.toLinearEquiv.toAddHom)
        (continuous_torusQuotient.comp R.continuous)
        κ (hd.continuous.integrable_of_hasCompactSupport hc) f (torusQuotient x)))
      (fun x => inner ℝ e (averagingOperator (torusQuotient.comp R.toLinearEquiv.toAddHom)
        (continuous_torusQuotient.comp R.continuous)
        (fun z => (fderiv ℝ κ z) (R.symm v))
        (integrable_fderiv_apply hc hd _) f (torusQuotient x))) := by
  have hf := torus_pullback_locallyIntegrable f
  have h := hasWeakDirectionalDeriv_of_contDiff
    ((InnerProductSpace.toDual ℝ E e).contDiff.comp
      ((contDiff_literalAverage R hc hd hf).of_le (by simp))) v
  have hderiv (x : Vec 2) :
      (fderiv ℝ (fun x => inner ℝ e (∫ z : Vec 2, κ z • f (torusQuotient (x-R z)))) x) v =
        inner ℝ e (∫ z : Vec 2, (fderiv ℝ κ z) (R.symm v) •
          f (torusQuotient (x-R z))) := by
    have hh := (InnerProductSpace.toDual ℝ E e).hasFDerivAt.comp x
      ((contDiff_literalAverage R hc hd hf).differentiable (by simp) |>.differentiableAt.hasFDerivAt)
    have hh' := congrArg (fun A : Vec 2 →L[ℝ] ℝ => A v) hh.fderiv
    change (fderiv ℝ (fun x => inner ℝ e (∫ z : Vec 2, κ z • f (torusQuotient (x-R z)))) x) v =
      inner ℝ e ((fderiv ℝ (fun x => ∫ z : Vec 2, κ z • f (torusQuotient (x-R z))) x) v) at hh'
    rw [fderiv_literalAverage_apply R hc hd hf] at hh'
    exact hh'
  have h' : HasWeakDirectionalDeriv v
      (fun x => inner ℝ e (∫ z : Vec 2, κ z • f (torusQuotient (x-R z))))
      (fun x => inner ℝ e (∫ z : Vec 2, (fderiv ℝ κ z) (R.symm v) •
        f (torusQuotient (x-R z)))) := by
    change HasWeakDirectionalDeriv v
      (fun x => inner ℝ e (∫ z : Vec 2, κ z • f (torusQuotient (x-R z))))
      (fun x => (fderiv ℝ (fun x => inner ℝ e
        (∫ z : Vec 2, κ z • f (torusQuotient (x-R z)))) x) v) at h
    simpa only [hderiv] using h
  apply hasWeakDirectionalDeriv_congr_ae _ _ h'
  · simpa only [Function.comp_def] using
      (averagingOperator_torus_cover_ae R
        (hd.continuous.integrable_of_hasCompactSupport hc) f).symm.fun_comp (inner ℝ e)
  · simpa only [Function.comp_def] using
      (averagingOperator_torus_cover_ae R (integrable_fderiv_apply hc hd (R.symm v)) f).symm.fun_comp
        (inner ℝ e)

theorem averagingOperator_hasWeakDirectionalDeriv_fast_torus (R : Vec 2 ≃L[ℝ] Vec 2)
    {κ : Vec 2 → ℝ} (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ)
    (f : Lp E 2 torusMeasure) (a : Vec 2) (e : E) :
    HasWeakDirectionalDeriv (R a)
      (fun x => inner ℝ e (averagingOperator (torusQuotient.comp R.toLinearEquiv.toAddHom)
        (continuous_torusQuotient.comp R.continuous)
        κ (hd.continuous.integrable_of_hasCompactSupport hc) f (torusQuotient x)))
      (fun x => inner ℝ e (averagingOperator (torusQuotient.comp R.toLinearEquiv.toAddHom)
        (continuous_torusQuotient.comp R.continuous)
        (fun z => (fderiv ℝ κ z) a) (integrable_fderiv_apply hc hd a) f (torusQuotient x))) := by
  simpa only [R.symm_apply_apply] using
    averagingOperator_hasWeakDirectionalDeriv_kernel_torus R hc hd f (R a) e

end AVRegularity.Analysis.Convolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVenhance.Infra.Torus AVenhance.Infra.Parabolic.FourierGalerkin
namespace AVRegularity.Analysis.Convolution

/-! Linearity and commutation of arbitrary constant weak directions with averages. -/

section

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
 theorem torus_translation_hasWeakDirectionalDeriv {v : Vec 2} {f g : L2 E torusMeasure}
    (h : ∀ e : E, HasWeakDirectionalDeriv v
      (fun x => inner ℝ e (f (torusQuotient x)))
      (fun x => inner ℝ e (g (torusQuotient x)))) (z : Vec 2) :
    ∀ e : E, HasWeakDirectionalDeriv v
      (fun x => inner ℝ e (translation (torusQuotient z) f (torusQuotient x)))
      (fun x => inner ℝ e (translation (torusQuotient z) g (torusQuotient x))) := by
  intro e
  apply hasWeakDirectionalDeriv_congr_ae _ _ (hasWeakDirectionalDeriv_translate (h e) z)
  · filter_upwards [ae_torusQuotient (translation_ae (torusQuotient z) f)] with x hx
    rw [hx, map_sub]
  · filter_upwards [ae_torusQuotient (translation_ae (torusQuotient z) g)] with x hx
    rw [hx, map_sub]

omit [BorelSpace E] in
 theorem averagingOperator_hasWeakDirectionalDeriv_torus {v : Vec 2} {f g : L2 E torusMeasure}
    (h : ∀ e : E, HasWeakDirectionalDeriv v
      (fun x => inner ℝ e (f (torusQuotient x)))
      (fun x => inner ℝ e (g (torusQuotient x))))
    (ρ : Vec 2 →+ Vec 2) (hρ : Continuous ρ)
    {κ : Vec 2 → ℝ} (hκ : Integrable κ) :
    ∀ e : E, HasWeakDirectionalDeriv v
      (fun x => inner ℝ e (averagingOperator (torusQuotient.comp ρ)
        (continuous_torusQuotient.comp hρ) κ hκ f (torusQuotient x)))
      (fun x => inner ℝ e (averagingOperator (torusQuotient.comp ρ)
        (continuous_torusQuotient.comp hρ) κ hκ g (torusQuotient x))) := by
  intro e ψ hs hc
  let φ : WeakTest (Set.univ : Set (Vec 2)) := ⟨ψ, hs, hc, Set.subset_univ _⟩
  let t : L2 E torusMeasure := cellToTorus (periodizedTestVectorL2 φ e)
  let dφ : WeakTest (Set.univ : Set (Vec 2)) :=
    ⟨fun x => (fderiv ℝ ψ x) v,
      (hs.fderiv_right (by simp)).clm_apply contDiff_const, hc.fderiv_apply (𝕜 := ℝ) v, Set.subset_univ _⟩
  let dt : L2 E torusMeasure := cellToTorus (periodizedTestVectorL2 dφ e)
  have htranslated (z : Vec 2) :
      inner ℝ dt (translation (torusQuotient (ρ z)) f) =
        -inner ℝ t (translation (torusQuotient (ρ z)) g) := by
    rw [torus_inner_periodizedTest_eq, torus_inner_periodizedTest_eq]
    exact (by simpa only [φ, dφ] using
      torus_translation_hasWeakDirectionalDeriv h (ρ z) e ψ hs hc )
  change (∫ x, inner ℝ e (averagingOperator (torusQuotient.comp ρ)
      (continuous_torusQuotient.comp hρ) κ hκ f (torusQuotient x)) * dφ.toFun x) =
    -(∫ x, inner ℝ e (averagingOperator (torusQuotient.comp ρ)
      (continuous_torusQuotient.comp hρ) κ hκ g (torusQuotient x)) * φ.toFun x)
  rw [← torus_inner_periodizedTest_eq, ← torus_inner_periodizedTest_eq]
  change inner ℝ dt (average (torusQuotient.comp ρ) κ f) =
    -inner ℝ t (average (torusQuotient.comp ρ) κ g)
  unfold average
  rw [← integral_inner (integrable_average_integrand (torusQuotient.comp ρ)
      (continuous_torusQuotient.comp hρ) hκ f),
    ← integral_inner (integrable_average_integrand (torusQuotient.comp ρ)
      (continuous_torusQuotient.comp hρ) hκ g), ← integral_neg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    change inner ℝ dt (κ z • translation (torusQuotient (ρ z)) f) =
      -inner ℝ t (κ z • translation (torusQuotient (ρ z)) g)
    rw [real_inner_smul_right, real_inner_smul_right, htranslated, mul_neg]
end

end AVRegularity.Analysis.Convolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Analysis.Convolution

/-! Linearity of weak directional derivatives for the finite two-axis expansion. -/

section
theorem locallyIntegrable_mul_compact {u φ : Vec 2 → ℝ}
    (hu : LocallyIntegrable u volume) (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Integrable (fun x => u x * φ x) :=
  hu.integrable_smul_right_of_hasCompactSupport hφ hc

theorem hasWeakDirectionalDeriv_linear_direction {u g h : Vec 2 → ℝ}
    (hu : LocallyIntegrable u volume) (hg : LocallyIntegrable g volume)
    (hh : LocallyIntegrable h volume) {v w : Vec 2}
    (hv : HasWeakDirectionalDeriv v u g) (hw : HasWeakDirectionalDeriv w u h)
    (c d : ℝ) : HasWeakDirectionalDeriv (c • v + d • w) u
      (fun x => c * g x + d * h x) := by
  intro φ hs hc
  have hi := locallyIntegrable_mul_compact hg hs.continuous hc
  have hj := locallyIntegrable_mul_compact hh hs.continuous hc
  have hiv := locallyIntegrable_mul_compact hu
    ((hs.continuous_fderiv (by simp)).clm_apply continuous_const) (hc.fderiv_apply (𝕜 := ℝ) v)
  have hiw := locallyIntegrable_mul_compact hu
    ((hs.continuous_fderiv (by simp)).clm_apply continuous_const) (hc.fderiv_apply (𝕜 := ℝ) w)
  simp_rw [map_add, map_smul, smul_eq_mul, mul_add, add_mul, mul_assoc]
  simp_rw [mul_left_comm (u _) c, mul_left_comm (u _) d]
  rw [integral_add (hiv.const_mul c) (hiw.const_mul d), integral_const_mul, integral_const_mul,
    integral_add (hi.const_mul c) (hj.const_mul d), integral_const_mul, integral_const_mul,
    hv φ hs hc, hw φ hs hc]
  ring

theorem hasWeakDirectionalDeriv_linear_input {u f g h : Vec 2 → ℝ}
    (hu : LocallyIntegrable u volume) (hf : LocallyIntegrable f volume)
    (hg : LocallyIntegrable g volume) (hh : LocallyIntegrable h volume) {v : Vec 2}
    (h0 : HasWeakDirectionalDeriv v u g) (h1 : HasWeakDirectionalDeriv v f h)
    (c d : ℝ) : HasWeakDirectionalDeriv v (fun x => c * u x + d * f x)
      (fun x => c * g x + d * h x) := by
  intro φ hs hc
  have hi := locallyIntegrable_mul_compact hg hs.continuous hc
  have hj := locallyIntegrable_mul_compact hh hs.continuous hc
  have hiu := locallyIntegrable_mul_compact hu
    ((hs.continuous_fderiv (by simp)).clm_apply continuous_const) (hc.fderiv_apply (𝕜 := ℝ) v)
  have hif := locallyIntegrable_mul_compact hf
    ((hs.continuous_fderiv (by simp)).clm_apply continuous_const) (hc.fderiv_apply (𝕜 := ℝ) v)
  simp_rw [add_mul, mul_assoc]
  rw [integral_add (hiu.const_mul c) (hif.const_mul d), integral_const_mul, integral_const_mul,
    integral_add (hi.const_mul c) (hj.const_mul d), integral_const_mul, integral_const_mul,
    h0 φ hs hc, h1 φ hs hc]
  ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem locallyIntegrable_inner {f : Vec 2 → E} (hf : LocallyIntegrable f volume) (e : E) :
    LocallyIntegrable (fun x => inner ℝ e (f x)) volume :=
  fun x => (InnerProductSpace.toDual ℝ E e).integrableAtFilter_comp (hf x)

theorem l2_inner_locallyIntegrable_torus (f : L2 E torusMeasure) (e : E) :
    LocallyIntegrable (fun x => inner ℝ e (f (torusQuotient x))) volume :=
  locallyIntegrable_inner (torus_pullback_locallyIntegrable f) e

omit [CompleteSpace E] in
 theorem l2_linear_ae_torus (c d : ℝ) (f g : L2 E torusMeasure) :
    (fun x => (c • f + d • g) (torusQuotient x)) =ᵐ[volume]
      fun x => c • f (torusQuotient x) + d • g (torusQuotient x) := by
  have h : (c • f + d • g) =ᵐ[torusMeasure] fun x => c • f x + d • g x := by
    filter_upwards [Lp.coeFn_add (c • f) (d • g), Lp.coeFn_smul c f, Lp.coeFn_smul d g] with x ha hc hd
    rw [ha]
    change (c • f) x + (d • g) x = _
    rw [hc, hd]
    rfl
  exact ae_torusQuotient h

theorem hasWeakDirectionalDeriv_l2_linear_direction_torus {v w : Vec 2}
    {f g h : L2 E torusMeasure}
    (h0 : ∀ e, HasWeakDirectionalDeriv v (fun x => inner ℝ e (f (torusQuotient x)))
      (fun x => inner ℝ e (g (torusQuotient x))))
    (h1 : ∀ e, HasWeakDirectionalDeriv w (fun x => inner ℝ e (f (torusQuotient x)))
      (fun x => inner ℝ e (h (torusQuotient x)))) (c d : ℝ) (e : E) :
    HasWeakDirectionalDeriv (c • v + d • w) (fun x => inner ℝ e (f (torusQuotient x)))
      (fun x => inner ℝ e ((c • g + d • h) (torusQuotient x))) := by
  have hw := hasWeakDirectionalDeriv_linear_direction
    (l2_inner_locallyIntegrable_torus f e) (l2_inner_locallyIntegrable_torus g e)
    (l2_inner_locallyIntegrable_torus h e) (h0 e) (h1 e) c d
  apply hasWeakDirectionalDeriv_congr_ae Filter.EventuallyEq.rfl _ hw
  filter_upwards [l2_linear_ae_torus c d g h] with x hx
  rw [hx, inner_add_right, real_inner_smul_right, real_inner_smul_right]

theorem hasWeakDirectionalDeriv_l2_linear_input_torus {v : Vec 2}
    {f g h k : L2 E torusMeasure}
    (h0 : ∀ e, HasWeakDirectionalDeriv v (fun x => inner ℝ e (f (torusQuotient x)))
      (fun x => inner ℝ e (g (torusQuotient x))))
    (h1 : ∀ e, HasWeakDirectionalDeriv v (fun x => inner ℝ e (h (torusQuotient x)))
      (fun x => inner ℝ e (k (torusQuotient x)))) (c d : ℝ) (e : E) :
    HasWeakDirectionalDeriv v (fun x => inner ℝ e ((c • f + d • h) (torusQuotient x)))
      (fun x => inner ℝ e ((c • g + d • k) (torusQuotient x))) := by
  have hw := hasWeakDirectionalDeriv_linear_input
    (l2_inner_locallyIntegrable_torus f e) (l2_inner_locallyIntegrable_torus h e)
    (l2_inner_locallyIntegrable_torus g e) (l2_inner_locallyIntegrable_torus k e) (h0 e) (h1 e) c d
  apply hasWeakDirectionalDeriv_congr_ae _ _ hw
  · filter_upwards [l2_linear_ae_torus c d f h] with x hx
    rw [hx, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  · filter_upwards [l2_linear_ae_torus c d g k] with x hx
    rw [hx, inner_add_right, real_inner_smul_right, real_inner_smul_right]
end

/-! Directional tensors and derivatives of translated compact-kernel averages. -/

section
abbrev euclideanCoordinateEquiv : HilbertVec 2 ≃L[ℝ] Vec 2 :=
  HilbertVec.continuousLinearEquivVec 2

theorem vec_eq_sum_basis (v : Vec 2) : v = ∑ i : Fin 2, v i • basisVec i := by
  funext k
  simp only [Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul, basisVec]
  fin_cases k <;> simp

/-- Evaluate an ordered derivative tensor on the same vector in each slot. -/
def directionalTensorValue {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (m : ℕ) (A : DerivativeWord2 m → E) (v : Vec 2) : E :=
  ∑ w : DerivativeWord2 m, (∏ k : Fin m, v (w k)) • A w

theorem directionalTensorValue_coefficients_sq (m : ℕ) (v : Vec 2) :
    (∑ w : DerivativeWord2 m, (∏ k : Fin m, v (w k))^2) =
      ‖euclideanCoordinateEquiv.symm v‖^(2*m) := by
  simp_rw [← Finset.prod_pow]
  rw [← Fintype.prod_sum (fun (_ : Fin m) (i : Fin 2) => (v i)^2)]
  have hn := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℝ) (euclideanCoordinateEquiv.symm v)
  have hv (i : Fin 2) : (euclideanCoordinateEquiv.symm v) i = v i := rfl
  have hs : (∑ i : Fin 2, (v i)^2) = ‖euclideanCoordinateEquiv.symm v‖^2 := by
    symm
    simpa only [Real.norm_eq_abs, sq_abs, hv] using hn
  simp only [hs, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul]

theorem directionalTensorValue_norm_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (m : ℕ) (A : DerivativeWord2 m → E) (v : Vec 2) :
    ‖directionalTensorValue m A v‖ ≤ ‖euclideanCoordinateEquiv.symm v‖^m *
      Real.sqrt (∑ w : DerivativeWord2 m, ‖A w‖^2) := by
  calc
    ‖directionalTensorValue m A v‖ ≤
        ∑ w : DerivativeWord2 m, |∏ k : Fin m, v (w k)| * ‖A w‖ := by
      unfold directionalTensorValue
      exact (norm_sum_le _ _).trans_eq (by simp only [norm_smul, Real.norm_eq_abs])
    _ ≤ Real.sqrt (∑ w : DerivativeWord2 m, |∏ k : Fin m, v (w k)|^2) *
        Real.sqrt (∑ w : DerivativeWord2 m, ‖A w‖^2) := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = _ := by
      simp only [sq_abs]
      rw [directionalTensorValue_coefficients_sq]
      rw [show 2*m=m*2 by omega, pow_mul, Real.sqrt_sq (pow_nonneg (norm_nonneg _) _)]

theorem iteratedFDeriv_same_direction_eq_tensor {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : Vec 2 → E) (m : ℕ) (x v : Vec 2) :
    iteratedFDeriv ℝ m F x (fun _ => v) =
      directionalTensorValue m
        (fun w => iteratedFDeriv ℝ m F x (fun k => basisVec (w k))) v := by
  let M := iteratedFDeriv ℝ m F x
  calc
    M (fun _ => v) = M (fun _ : Fin m => ∑ i : Fin 2, v i • basisVec i) := by
      rw [← vec_eq_sum_basis]
    _ = ∑ w : DerivativeWord2 m, M (fun k => v (w k) • basisVec (w k)) :=
      M.toMultilinearMap.map_sum (fun (_ : Fin m) (i : Fin 2) => v i • basisVec i)
    _ = directionalTensorValue m (fun w => M (fun k => basisVec (w k))) v := by
      unfold directionalTensorValue
      apply Finset.sum_congr rfl
      intro w _
      exact M.map_smul_univ (fun k => v (w k)) (fun k => basisVec (w k))

section Translation
variable {X E : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [MeasurableSpace X] [BorelSpace X] [R1Space X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  {μ : Measure X} [μ.IsAddLeftInvariant] [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]

omit [MeasurableSpace E] [BorelSpace E] in
theorem translation_average_eq_literal (ρ : Vec 2 →+ X) (hρ : Continuous ρ)
    (R : Vec 2 ≃L[ℝ] Vec 2) (κ : Vec 2 → ℝ) (hκ : Integrable κ) (f : L2 E μ) (x : Vec 2) :
    translation (-ρ x) (averagingOperator (ρ.comp R.toLinearEquiv.toAddHom)
      (hρ.comp R.continuous) κ hκ f) =
      ∫ z : Vec 2, κ z • translation (-ρ (x-R z)) f := by
  rw [averagingOperator_apply]
  calc
    _ = ∫ z : Vec 2, translation (-ρ x)
        (κ z • translation ((ρ.comp R.toLinearEquiv.toAddHom) z) f) :=
      ((translation (-ρ x)).integral_comp_comm
        (fun z : Vec 2 => κ z • translation ((ρ.comp R.toLinearEquiv.toAddHom) z) f)).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        change translation (-ρ x) (κ z • translation (ρ (R z)) f) =
          κ z • translation (-ρ (x-R z)) f
        rw [(translation (-ρ x)).map_smul, ← translation_add]
        congr 2
        rw [map_sub, neg_sub, sub_eq_add_neg, add_comm]

omit [MeasurableSpace E] [BorelSpace E] in
theorem contDiff_translation_average (ρ : Vec 2 →+ X) (hρ : Continuous ρ)
    (R : Vec 2 ≃L[ℝ] Vec 2) {κ : Vec 2 → ℝ}
    (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ) (f : L2 E μ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => translation (-ρ x)
      (averagingOperator (ρ.comp R.toLinearEquiv.toAddHom) (hρ.comp R.continuous)
        κ (hd.continuous.integrable_of_hasCompactSupport hc) f)) := by
  have ht : Continuous (fun x : Vec 2 => translation (-ρ x) f) :=
    (continuous_translation f).comp hρ.neg
  have h := contDiff_literalAverage R hc hd (ht.locallyIntegrable (μ := volume))
  have heq : (fun x : Vec 2 => translation (-ρ x)
      (averagingOperator (ρ.comp R.toLinearEquiv.toAddHom) (hρ.comp R.continuous)
        κ (hd.continuous.integrable_of_hasCompactSupport hc) f)) =
      (fun x : Vec 2 => ∫ z : Vec 2, κ z • translation (-ρ (x-R z)) f) := by
    funext x
    exact translation_average_eq_literal ρ hρ R κ _ f x
  rw [heq]
  exact h

omit [MeasurableSpace E] [BorelSpace E] in
theorem fderiv_translation_average_apply (ρ : Vec 2 →+ X) (hρ : Continuous ρ)
    (R : Vec 2 ≃L[ℝ] Vec 2) {κ : Vec 2 → ℝ}
    (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ) (f : L2 E μ)
    (x v : Vec 2) :
    (fderiv ℝ (fun x : Vec 2 => translation (-ρ x)
      (averagingOperator (ρ.comp R.toLinearEquiv.toAddHom) (hρ.comp R.continuous)
        κ (hd.continuous.integrable_of_hasCompactSupport hc) f)) x) v =
      translation (-ρ x) (averagingOperator (ρ.comp R.toLinearEquiv.toAddHom)
        (hρ.comp R.continuous) (fun z => (fderiv ℝ κ z) (R.symm v))
        (integrable_fderiv_apply hc hd _) f) := by
  have ht : Continuous (fun x : Vec 2 => translation (-ρ x) f) :=
    (continuous_translation f).comp hρ.neg
  have heq : (fun x : Vec 2 => translation (-ρ x)
      (averagingOperator (ρ.comp R.toLinearEquiv.toAddHom) (hρ.comp R.continuous)
        κ (hd.continuous.integrable_of_hasCompactSupport hc) f)) =
      (fun x : Vec 2 => ∫ z : Vec 2, κ z • translation (-ρ (x-R z)) f) := by
    funext x
    exact translation_average_eq_literal ρ hρ R κ _ f x
  rw [heq, fderiv_literalAverage_apply R hc hd (ht.locallyIntegrable (μ := volume))]
  exact (translation_average_eq_literal ρ hρ R _ (integrable_fderiv_apply hc hd _) f x).symm

omit [MeasurableSpace E] [BorelSpace E] in
theorem iteratedFDeriv_translation_average_apply (ρ : Vec 2 →+ X) (hρ : Continuous ρ)
    (R : Vec 2 ≃L[ℝ] Vec 2) {κ : Vec 2 → ℝ}
    (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ) (f : L2 E μ)
    (m : ℕ) (x : Vec 2) (a : Fin m → Vec 2) :
    iteratedFDeriv ℝ m (fun x : Vec 2 => translation (-ρ x)
      (averagingOperator (ρ.comp R.toLinearEquiv.toAddHom) (hρ.comp R.continuous)
        κ (hd.continuous.integrable_of_hasCompactSupport hc) f)) x a =
      translation (-ρ x) (averagingOperator (ρ.comp R.toLinearEquiv.toAddHom)
        (hρ.comp R.continuous)
        (orderedKernelDerivative κ m (fun k => R.symm (a k.rev)))
        (integrable_orderedKernelDerivative hc hd m (fun k => R.symm (a k.rev))) f) := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
      let F : Vec 2 → L2 E μ := fun y => translation (-ρ y)
        (averagingOperator (ρ.comp R.toLinearEquiv.toAddHom) (hρ.comp R.continuous)
          κ (hd.continuous.integrable_of_hasCompactSupport hc) f)
      let G : Vec 2 → L2 E μ := fun y => translation (-ρ y) (averagingOperator
        (ρ.comp R.toLinearEquiv.toAddHom) (hρ.comp R.continuous)
        (orderedKernelDerivative κ m (fun k => R.symm (Fin.tail a k.rev)))
        (integrable_orderedKernelDerivative hc hd m
          (fun k => R.symm (Fin.tail a k.rev))) f)
      have hdiff := (ContDiff.differentiable_iteratedFDeriv (n := (⊤ : ℕ∞)) (m := m)
        (by exact WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top m))
        (contDiff_translation_average ρ hρ R hc hd f)).differentiableAt (x := x)
      rw [hdiff.iteratedFDeriv_succ_apply_left']
      have hfun : (fun y : Vec 2 => iteratedFDeriv ℝ m F y (Fin.tail a)) = G := by
        funext y
        exact ih y (Fin.tail a)
      rw [hfun]
      rw [fderiv_translation_average_apply ρ hρ R
        (hasCompactSupport_orderedKernelDerivative hc m _)
        (contDiff_orderedKernelDerivative hd m _) f]
      have ha : (fun k : Fin (m+1) => R.symm (a k.rev)) =
          Fin.snoc (fun k : Fin m => R.symm (Fin.tail a k.rev)) (R.symm (a 0)) := by
        have hv : a ∘ Fin.rev = Fin.snoc (Fin.tail a ∘ Fin.rev) (a 0) :=
          (congrArg (fun b : Fin (m+1) → Vec 2 => b ∘ Fin.rev)
            (Fin.cons_self_tail a).symm).trans (Fin.cons_comp_rev (a 0) (Fin.tail a))
        have h := Fin.comp_snoc R.symm (Fin.tail a ∘ Fin.rev) (a 0)
        rw [← hv] at h
        exact h
      simp_rw [ha, orderedKernelDerivative_snoc]

end Translation
end

/-! Paired axis averages and derivative transfers along their own axes. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Literal paired plane average with p derivatives on its first kernel and q on its second. -/
def pairedAxisAveragePlane (R S : Vec 2 ≃L[ℝ] Vec 2) (κ : Vec 2 → ℝ)
    (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ)
    (a b : Vec 2) (p q : ℕ) (f : L2 E (volume : Measure (Vec 2))) :
    L2 E (volume : Measure (Vec 2)) :=
  averagingOperator R.toLinearEquiv.toAddHom R.continuous
    (orderedKernelDerivative κ p (fun _ => a))
    (integrable_orderedKernelDerivative hc hd p (fun _ => a))
    (averagingOperator S.toLinearEquiv.toAddHom S.continuous
      (orderedKernelDerivative κ q (fun _ => b))
      (integrable_orderedKernelDerivative hc hd q (fun _ => b)) f)

/-- The identical literal paired average on the normalized probability torus. -/
def pairedAxisAverageTorus (R S : Vec 2 ≃L[ℝ] Vec 2) (κ : Vec 2 → ℝ)
    (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ)
    (a b : Vec 2) (p q : ℕ) (f : L2 E torusMeasure) : L2 E torusMeasure :=
  averagingOperator (torusQuotient.comp R.toLinearEquiv.toAddHom)
    (continuous_torusQuotient.comp R.continuous)
    (orderedKernelDerivative κ p (fun _ => a))
    (integrable_orderedKernelDerivative hc hd p (fun _ => a))
    (averagingOperator (torusQuotient.comp S.toLinearEquiv.toAddHom)
      (continuous_torusQuotient.comp S.continuous)
      (orderedKernelDerivative κ q (fun _ => b))
      (integrable_orderedKernelDerivative hc hd q (fun _ => b)) f)

theorem pairedAxisAverageTorus_first (R S : Vec 2 ≃L[ℝ] Vec 2) {κ : Vec 2 → ℝ}
    (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ)
    (a b : Vec 2) (p q : ℕ) (f : L2 E torusMeasure) (e : E) :
    HasWeakDirectionalDeriv (R a)
      (fun x => inner ℝ e (pairedAxisAverageTorus R S κ hc hd a b p q f (torusQuotient x)))
      (fun x => inner ℝ e (pairedAxisAverageTorus R S κ hc hd a b (p+1) q f (torusQuotient x))) := by
  have h := averagingOperator_hasWeakDirectionalDeriv_fast_torus R
    (hasCompactSupport_orderedKernelDerivative hc p (fun _ => a))
    (contDiff_orderedKernelDerivative hd p (fun _ => a))
    (averagingOperator (torusQuotient.comp S.toLinearEquiv.toAddHom)
      (continuous_torusQuotient.comp S.continuous)
      (orderedKernelDerivative κ q (fun _ => b))
      (integrable_orderedKernelDerivative hc hd q (fun _ => b)) f) a e
  exact h

variable [MeasurableSpace E] [BorelSpace E]
omit [BorelSpace E] in
 theorem pairedAxisAverageTorus_second (R S : Vec 2 ≃L[ℝ] Vec 2) {κ : Vec 2 → ℝ}
    (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ)
    (a b : Vec 2) (p q : ℕ) (f : L2 E torusMeasure) (e : E) :
    HasWeakDirectionalDeriv (S b)
      (fun x => inner ℝ e (pairedAxisAverageTorus R S κ hc hd a b p q f (torusQuotient x)))
      (fun x => inner ℝ e (pairedAxisAverageTorus R S κ hc hd a b p (q+1) f (torusQuotient x))) := by
  have h := fun e : E => averagingOperator_hasWeakDirectionalDeriv_fast_torus S
    (hasCompactSupport_orderedKernelDerivative hc q (fun _ => b))
    (contDiff_orderedKernelDerivative hd q (fun _ => b)) f b e
  exact averagingOperator_hasWeakDirectionalDeriv_torus h R.toLinearEquiv.toAddHom R.continuous
    (integrable_orderedKernelDerivative hc hd p (fun _ => a)) e

omit [MeasurableSpace E] [BorelSpace E] in
 theorem pairedAxisAverageTorus_norm_le (R S : Vec 2 ≃L[ℝ] Vec 2) {κ : Vec 2 → ℝ}
    (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ)
    (a b : Vec 2) (p q : ℕ) (f : L2 E torusMeasure) :
    ‖pairedAxisAverageTorus R S κ hc hd a b p q f‖ ≤
      (∫ z, ‖orderedKernelDerivative κ p (fun _ => a) z‖) *
      (∫ z, ‖orderedKernelDerivative κ q (fun _ => b) z‖) * ‖f‖ := by
  have hp := ContinuousLinearMap.le_of_opNorm_le _
    (averagingOperator_norm_le (E := E) (μ := torusMeasure)
      (torusQuotient.comp R.toLinearEquiv.toAddHom) (continuous_torusQuotient.comp R.continuous)
      _ (integrable_orderedKernelDerivative hc hd p (fun _ => a)))
    (averagingOperator (torusQuotient.comp S.toLinearEquiv.toAddHom)
      (continuous_torusQuotient.comp S.continuous)
      (orderedKernelDerivative κ q (fun _ => b)) (integrable_orderedKernelDerivative hc hd q (fun _ => b)) f)
  have hq := ContinuousLinearMap.le_of_opNorm_le _
    (averagingOperator_norm_le (E := E) (μ := torusMeasure)
      (torusQuotient.comp S.toLinearEquiv.toAddHom) (continuous_torusQuotient.comp S.continuous)
      _ (integrable_orderedKernelDerivative hc hd q (fun _ => b))) f
  exact hp.trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hq (integral_nonneg fun _ => norm_nonneg _))
end

/-! Moment cancellation of actual homogeneous products of linear coordinate functionals. -/

theorem integral_coordinate_word_momentKernel {φ₀ : Vec 2 → ℝ}
    (hc : HasCompactSupport φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hmass : ∫ z, φ₀ z = 1) (n : ℕ+) {m : ℕ} (w : DerivativeWord 2 m)
    (hpos : 0 < m) (hsmall : m < 2*(n:ℕ)) :
    ∫ z : Vec 2, (∏ k : Fin m, z (w k)) * momentKernel φ₀ n z = 0 := by
  let α : Fin 2 → ℕ := fun i => (Finset.univ.filter (fun k : Fin m => w k = i)).card
  have ha : (∑ i : Fin 2, α i) = m := by
    simp only [α, Finset.sum_card_fiberwise_eq_card_filter, Finset.mem_univ, Finset.filter_true,
      Finset.card_univ, Fintype.card_fin]
  have hp (z : Vec 2) : (∏ i : Fin 2, z i ^ α i) = ∏ k : Fin m, z (w k) := by
    have h := Finset.prod_fiberwise_of_maps_to' (s := (Finset.univ : Finset (Fin m)))
      (t := (Finset.univ : Finset (Fin 2))) (g := w) (fun _ _ => Finset.mem_univ _) z
    simpa only [Finset.prod_const, α] using h
  have h := integral_multiindex_momentKernel hc hd hmass n α (by rwa [ha]) (by rwa [ha])
  simpa only [hp] using h

theorem integral_linear_word_momentKernel {φ₀ : Vec 2 → ℝ}
    (hc : HasCompactSupport φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hmass : ∫ z, φ₀ z = 1) (n : ℕ+) {m : ℕ} (L : Fin m → Vec 2 →L[ℝ] ℝ)
    (hpos : 0 < m) (hsmall : m < 2*(n:ℕ)) :
    ∫ z : Vec 2, (∏ k : Fin m, L k z) * momentKernel φ₀ n z = 0 := by
  have hq := contDiff_momentKernel hc hd n
  have hqc := hasCompactSupport_momentKernel hc n
  have hex (z : Vec 2) : (∏ k : Fin m, L k z) =
      ∑ w : DerivativeWord 2 m, (∏ k : Fin m, L k (basisVec (w k))) * (∏ k : Fin m, z (w k)) := by
    have hl (k : Fin m) : L k z = ∑ i : Fin 2, L k (basisVec i) * z i := by
      calc
        L k z = L k (∑ i : Fin 2, z i • basisVec i) := congrArg (L k) (vec_eq_sum_basis z)
        _ = _ := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [map_smul, smul_eq_mul, mul_comm]
    simp_rw [hl]
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro w _
    exact Finset.prod_mul_distrib
  have hi (w : DerivativeWord 2 m) : Integrable (fun z : Vec 2 =>
      (∏ k : Fin m, L k (basisVec (w k))) * ((∏ k : Fin m, z (w k)) * momentKernel φ₀ n z)) := by
    have hp : Continuous (fun z : Vec 2 => ∏ k : Fin m, z (w k)) :=
      continuous_finsetProd _ (fun k _ => continuous_apply (w k))
    exact ((hp.mul hq.continuous).integrable_of_hasCompactSupport hqc.mul_left).const_mul _
  rw [show (fun z : Vec 2 => (∏ k : Fin m, L k z) * momentKernel φ₀ n z) =
    (fun z : Vec 2 => ∑ w : DerivativeWord 2 m, (∏ k : Fin m, L k (basisVec (w k))) *
      ((∏ k : Fin m, z (w k)) * momentKernel φ₀ n z)) by
    funext z
    rw [hex, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro w _
    rw [mul_assoc]]
  rw [integral_finsetSum _ (fun w _ => hi w)]
  simp only [integral_const_mul, integral_coordinate_word_momentKernel hc hd hmass n _ hpos hsmall,
    mul_zero, Finset.sum_const_zero]

/-! The actual source kernel cancels every nonconstant homogeneous ordered tensor coefficient. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem integral_directionalTensorValue_momentKernel {φ₀ : Vec 2 → ℝ}
    (hc : HasCompactSupport φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hmass : ∫ z, φ₀ z = 1) (n : ℕ+) {m : ℕ} (A : DerivativeWord 2 m → E)
    (H : Vec 2 →L[ℝ] Vec 2) (hpos : 0 < m) (hsmall : m < 2*(n:ℕ)) :
    (∫ z : Vec 2, momentKernel φ₀ n z • directionalTensorValue m A (H z)) = 0 := by
  let q := momentKernel φ₀ n
  have hqc := hasCompactSupport_momentKernel hc n
  have hq := (contDiff_momentKernel hc hd n).continuous
  have hi (w : DerivativeWord 2 m) : Integrable (fun z : Vec 2 =>
      ((∏ k : Fin m, H z (w k)) * q z) • A w) := by
    have hp : Continuous (fun z : Vec 2 => ∏ k : Fin m, H z (w k)) :=
      continuous_finsetProd _ (fun k _ => (continuous_apply (w k)).comp H.continuous)
    exact ((hp.mul hq).integrable_of_hasCompactSupport hqc.mul_left).smul_const _
  change (∫ z : Vec 2, q z • ∑ w : DerivativeWord 2 m, (∏ k : Fin m, H z (w k)) • A w) = 0
  simp_rw [Finset.smul_sum, smul_smul]
  rw [integral_finsetSum _ (fun w _ => by simpa only [mul_comm (q _)] using hi w)]
  apply Finset.sum_eq_zero
  intro w _
  have h := integral_linear_word_momentKernel hc hd hmass n
    (fun k : Fin m => (ContinuousLinearMap.proj (w k)).comp H) hpos hsmall
  change (∫ z : Vec 2, (∏ k : Fin m, H z (w k)) * q z) = 0 at h
  rw [integral_smul_const]
  have heq : (∫ z : Vec 2, q z * ∏ k : Fin m, H z (w k)) = 0 := by
    simpa only [mul_comm (q _)] using h
  rw [heq, zero_smul]
end

end AVRegularity.Analysis.Convolution
end

section
open MeasureTheory Homogenization AVRegularity.Analysis.Convolution
namespace AVRegularity.Analysis.Convolution

/-! Sharp Euclidean directional Taylor remainder for a genuinely smooth Banach-valued function. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem norm_taylor_remainder_euclidean_le {F : Vec 2 → E}
    (hd : ContDiff ℝ (⊤ : ℕ∞) F) {K : ℕ} (hK : 0 < K) (C : ℝ)
    (hC : ∀ x v, ‖iteratedFDeriv ℝ K F x (fun _ => v)‖ ≤ ‖euclideanCoordinateEquiv.symm v‖^K * C)
    (y : Vec 2) :
    ‖F y - ∑ k ∈ Finset.range K, (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k F 0 (fun _ => y)‖ ≤
      ‖euclideanCoordinateEquiv.symm y‖^K * C / (K.factorial : ℝ) := by
  cases K with
  | zero => omega
  | succ m =>
    have ht := map_add_eq_sum_add_integral_iteratedFDeriv (f := F) (x := (0 : Vec 2)) (y := y) (n := m)
      (fun t _ => hd.contDiffAt.of_le (by simp))
    simp only [zero_add] at ht
    have hr : F y - ∑ k ∈ Finset.range (m+1), (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k F 0 (fun _ => y) =
        (m.factorial : ℝ)⁻¹ • ∫ t : ℝ in (0 : ℝ)..1, (1-t)^m • iteratedFDeriv ℝ (m+1) F (t • y) (fun _ => y) := by
      rw [ht, add_sub_cancel_left]
    rw [hr, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
    calc
      _ ≤ (m.factorial : ℝ)⁻¹ * ∫ t : ℝ in (0 : ℝ)..1, (1-t)^m * (‖euclideanCoordinateEquiv.symm y‖^(m+1) * C) := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
        apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
        · exact Filter.Eventually.of_forall fun t ht => by
            have hw : 0 ≤ (1-t)^m := pow_nonneg (sub_nonneg.mpr ht.2) _
            rw [norm_smul, Real.norm_of_nonneg hw]
            exact mul_le_mul_of_nonneg_left (hC (t • y) y) hw
        · exact (((continuous_const.sub continuous_id).pow m).mul continuous_const).intervalIntegrable _ _
      _ = _ := by
        rw [intervalIntegral.integral_mul_const, integral_one_sub_pow, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring

end AVRegularity.Analysis.Convolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Analysis.Convolution

/-! Actual rough-input convolution into arbitrary finite ordered weak Sobolev graphs.
Every component is a literal average with a proved compact smooth ordered derivative kernel.
The source value is the existing averaging operator on both domains, explicitly characterized.
No contrast-independent paired quantitative estimate is asserted by this regularity module. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The actual derivative kernel of an appended spatial coordinate word. -/
theorem orderedKernelDerivative_coordinate_snoc (κ : Vec 2 → ℝ) (R : Vec 2 ≃L[ℝ] Vec 2)
    {m : ℕ} (w : DerivativeWord 2 m) (i : Fin 2) :
    orderedKernelDerivative κ (m+1) (fun k => R.symm (basisVec ((Fin.snoc (α := fun _ => Fin 2) w i) k))) =
      fun z => (fderiv ℝ (orderedKernelDerivative κ m (fun k => R.symm (basisVec (w k)))) z)
        (R.symm (basisVec i)) := by
  have ha : (fun k : Fin (m+1) => R.symm (basisVec ((Fin.snoc (α := fun _ => Fin 2) w i) k))) =
      Fin.snoc (fun k => R.symm (basisVec (w k))) (R.symm (basisVec i)) := by
    exact Fin.comp_snoc (fun i : Fin 2 => R.symm (basisVec i)) w i
  rw [ha, orderedKernelDerivative_snoc]

/-- Rough-input smoothing jet: each exact ordered coordinate derivative is a literal kernel average. -/
def planeSmoothingJet {K : ℕ} (R : Vec 2 ≃L[ℝ] Vec 2) (κ : Vec 2 → ℝ)
    (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ)
    (f : L2 E (volume : Measure (Vec 2))) : JetL2 (volume.restrict (Set.univ : Set (Vec 2))) K E :=
  WithLp.toLp 2 (fun a : JetIndex2 K => planeToUniv (averagingOperator R.toLinearEquiv.toAddHom R.continuous
    (orderedKernelDerivative κ a.1.val (fun k => R.symm (basisVec (a.2 k))))
    (integrable_orderedKernelDerivative hc hd a.1.val (fun k => R.symm (basisVec (a.2 k)))) f))

omit [BorelSpace E] in
 theorem planeSmoothingJet_mem_graph {K : ℕ} (R : Vec 2 ≃L[ℝ] Vec 2) {κ : Vec 2 → ℝ}
    (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ)
    (f : L2 E (volume : Measure (Vec 2))) :
    planeSmoothingJet (K := K) R κ hc hd f ∈ planeHkGraph (E := E) Set.univ K := by
  rw [mem_planeHkGraph_iff]
  intro j w i e
  let q := orderedKernelDerivative κ j.val (fun k => R.symm (basisVec (w k)))
  have hq := hasCompactSupport_orderedKernelDerivative hc j.val (fun k => R.symm (basisVec (w k)))
  have hdq := contDiff_orderedKernelDerivative hd j.val (fun k => R.symm (basisVec (w k)))
  have hw := (hasWeakDirectionalDeriv_basis_iff i _ _).mp
    (averagingOperator_hasWeakDirectionalDeriv_kernel R hq hdq f (basisVec i) e)
  have hnext := orderedKernelDerivative_coordinate_snoc κ R w i
  change HasWeakPartialDerivOn Set.univ i
    (fun x => inner ℝ e (planeToUniv (averagingOperator R.toLinearEquiv.toAddHom R.continuous q
      (integrable_orderedKernelDerivative hc hd j.val (fun k => R.symm (basisVec (w k)))) f) x))
    (fun x => inner ℝ e (planeToUniv (averagingOperator R.toLinearEquiv.toAddHom R.continuous
      (orderedKernelDerivative κ (j.val+1) (fun k => R.symm (basisVec ((Fin.snoc (α := fun _ => Fin 2) w i) k))))
      (integrable_orderedKernelDerivative hc hd (j.val+1) (fun k => R.symm (basisVec ((Fin.snoc (α := fun _ => Fin 2) w i) k)))) f) x))
  simp_rw [hnext]
  apply hasWeakPartialDerivOn_congr_ae _ _ hw
  · simpa only [Measure.restrict_univ, Function.comp_def] using
      (planeToUniv_ae (averagingOperator R.toLinearEquiv.toAddHom R.continuous q
        (integrable_orderedKernelDerivative hc hd j.val (fun k => R.symm (basisVec (w k)))) f)).symm.fun_comp (inner ℝ e)
  · simpa only [Measure.restrict_univ, Function.comp_def] using
      (planeToUniv_ae (averagingOperator R.toLinearEquiv.toAddHom R.continuous
        (fun z => (fderiv ℝ q z) (R.symm (basisVec i))) (integrable_fderiv_apply hq hdq _) f)).symm.fun_comp (inner ℝ e)

/-- Rough-input periodic jet, using the actual normalized torus average for every word. -/
def periodicSmoothingJet {K : ℕ} (R : Vec 2 ≃L[ℝ] Vec 2) (κ : Vec 2 → ℝ)
    (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ)
    (f : L2 E torusMeasure) : JetL2 (volume.restrict AVenhance.unitCube) K E :=
  WithLp.toLp 2 (fun a : JetIndex2 K => torusToCell (averagingOperator (torusQuotient.comp R.toLinearEquiv.toAddHom)
    (continuous_torusQuotient.comp R.continuous)
    (orderedKernelDerivative κ a.1.val (fun k => R.symm (basisVec (a.2 k))))
    (integrable_orderedKernelDerivative hc hd a.1.val (fun k => R.symm (basisVec (a.2 k)))) f))

omit [BorelSpace E] in
 theorem periodicSmoothingJet_global_ae {K : ℕ} (R : Vec 2 ≃L[ℝ] Vec 2) {κ : Vec 2 → ℝ}
    (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ) (f : L2 E torusMeasure)
    (a : JetIndex2 K) :
    periodicJetRepresentative (periodicSmoothingJet R κ hc hd f) a =ᵐ[volume]
      fun x => averagingOperator (torusQuotient.comp R.toLinearEquiv.toAddHom)
        (continuous_torusQuotient.comp R.continuous)
        (orderedKernelDerivative κ a.1.val (fun k => R.symm (basisVec (a.2 k))))
        (integrable_orderedKernelDerivative hc hd a.1.val (fun k => R.symm (basisVec (a.2 k)))) f (torusQuotient x) := by
  have h := cellToTorus_global_ae (periodicSmoothingJet R κ hc hd f) a
  change (fun x => cellToTorus (torusToCell (averagingOperator
    (torusQuotient.comp R.toLinearEquiv.toAddHom) (continuous_torusQuotient.comp R.continuous)
    (orderedKernelDerivative κ a.1.val (fun k => R.symm (basisVec (a.2 k))))
    (integrable_orderedKernelDerivative hc hd a.1.val (fun k => R.symm (basisVec (a.2 k)))) f)) (torusQuotient x)) =ᵐ[volume] _ at h
  rw [cellToTorus_torusToCell] at h
  exact h.symm

omit [BorelSpace E] in
 theorem periodicSmoothingJet_mem_graph {K : ℕ} (R : Vec 2 ≃L[ℝ] Vec 2) {κ : Vec 2 → ℝ}
    (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ)
    (f : L2 E torusMeasure) : periodicSmoothingJet (K := K) R κ hc hd f ∈ torusHkGraph (E := E) K := by
  rw [mem_torusHkGraph_iff]
  refine ⟨periodicJetRepresentative_periodic _, periodicJetRepresentative_memL2 _, ?_⟩
  intro j w i e
  have hq := hasCompactSupport_orderedKernelDerivative hc j.val (fun k => R.symm (basisVec (w k)))
  have hdq := contDiff_orderedKernelDerivative hd j.val (fun k => R.symm (basisVec (w k)))
  have hw := (hasWeakDirectionalDeriv_basis_iff i _ _).mp
    (averagingOperator_hasWeakDirectionalDeriv_kernel_torus R hq hdq f (basisVec i) e)
  have hnext := orderedKernelDerivative_coordinate_snoc κ R w i
  simp_rw [← hnext] at hw
  apply hasWeakPartialDerivOn_congr_ae _ _ hw
  · simpa only [Measure.restrict_univ, Function.comp_def, lowerIndex2, lowerIndex] using
      (periodicSmoothingJet_global_ae R hc hd f (lowerIndex2 j w)).symm.fun_comp (inner ℝ e)
  · simpa only [Measure.restrict_univ, Function.comp_def, nextIndex2, nextIndex] using
      (periodicSmoothingJet_global_ae R hc hd f (nextIndex2 j w i)).symm.fun_comp (inner ℝ e)

/-- The literal rough-input convolution, promoted to any finite ordered weak Sobolev graph. -/
def planeSmoothing {K : ℕ} (R : Vec 2 ≃L[ℝ] Vec 2) (κ : Vec 2 → ℝ)
    (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ)
    (f : L2 E (volume : Measure (Vec 2))) : PlaneHk (Set.univ : Set (Vec 2)) K E :=
  ⟨planeSmoothingJet R κ hc hd f, planeSmoothingJet_mem_graph R hc hd f⟩

/-- The literal periodic rough-input convolution, promoted to any finite periodic weak graph. -/
def periodicSmoothing {K : ℕ} (R : Vec 2 ≃L[ℝ] Vec 2) (κ : Vec 2 → ℝ)
    (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ)
    (f : L2 E torusMeasure) : TorusHk K E :=
  ⟨periodicSmoothingJet R κ hc hd f, periodicSmoothingJet_mem_graph R hc hd f⟩

 theorem planeSmoothing_value {K : ℕ} (R : Vec 2 ≃L[ℝ] Vec 2) {κ : Vec 2 → ℝ}
    (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ)
    (f : L2 E (volume : Measure (Vec 2))) :
    (planeSmoothing (K := K) R κ hc hd f).val (valueIndex2 K) =
      planeToUniv (averagingOperator R.toLinearEquiv.toAddHom R.continuous κ
    (hd.continuous.integrable_of_hasCompactSupport hc) f) := by
  change planeToUniv (averagingOperator R.toLinearEquiv.toAddHom R.continuous κ
    (hd.continuous.integrable_of_hasCompactSupport hc) f) = _
  rfl

 theorem periodicSmoothing_value {K : ℕ} (R : Vec 2 ≃L[ℝ] Vec 2) {κ : Vec 2 → ℝ}
    (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ)
    (f : L2 E torusMeasure) :
    (periodicSmoothing (K := K) R κ hc hd f).val (valueIndex2 K) =
      torusToCell (averagingOperator (torusQuotient.comp R.toLinearEquiv.toAddHom)
        (continuous_torusQuotient.comp R.continuous) κ
        (hd.continuous.integrable_of_hasCompactSupport hc) f) := by
  change torusToCell (averagingOperator (torusQuotient.comp R.toLinearEquiv.toAddHom)
    (continuous_torusQuotient.comp R.continuous) κ
    (hd.continuous.integrable_of_hasCompactSupport hc) f) = _
  rfl


/-- The order-zero value identifies rough smoothing with weak-jet averaging. -/
theorem planeSmoothing_eq_weakAverage [FiniteDimensional ℝ E] {K : ℕ}
    (R : Vec 2 ≃L[ℝ] Vec 2) {κ : Vec 2 → ℝ}
    (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ)
    (f : PlaneHk (Set.univ : Set (Vec 2)) K E) :
    planeSmoothing (K := K) R κ hc hd (univToPlane (f.val (valueIndex2 K))) =
      planeWeakAverage R.toLinearEquiv.toAddHom R.continuous κ
        (hd.continuous.integrable_of_hasCompactSupport hc) f := by
  apply PlaneHk.ext_value isOpen_univ
  rw [planeSmoothing_value]
  rfl

theorem periodicSmoothing_eq_weakAverage [FiniteDimensional ℝ E] {K : ℕ}
    (R : Vec 2 ≃L[ℝ] Vec 2) {κ : Vec 2 → ℝ}
    (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ) (f : TorusHk K E) :
    periodicSmoothing (K := K) R κ hc hd (cellToTorus (f.val (valueIndex2 K))) =
      periodicWeakAverage R.toLinearEquiv.toAddHom R.continuous κ
        (hd.continuous.integrable_of_hasCompactSupport hc) f := by
  apply TorusHk.ext_value
  rw [periodicSmoothing_value]
  rfl
end

/-! Moment integration of the actual finite Taylor polynomial. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem integrable_momentKernel_taylor_term {φ₀ : Vec 2 → ℝ}
    (hc : HasCompactSupport φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀) (n : ℕ+)
    (F : Vec 2 → E) (H : Vec 2 →L[ℝ] Vec 2) (k : ℕ) :
    Integrable (fun z : Vec 2 => momentKernel φ₀ n z •
      ((k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k F 0 (fun _ => H z))) := by
  have ht : Continuous (fun z : Vec 2 => iteratedFDeriv ℝ k F 0 (fun _ => H z)) :=
    (iteratedFDeriv ℝ k F 0).cont.comp (continuous_pi (fun _ => H.continuous))
  exact ((contDiff_momentKernel hc hd n).continuous.smul (ht.const_smul _)).integrable_of_hasCompactSupport
    (hasCompactSupport_momentKernel hc n).smul_right

theorem integral_momentKernel_taylor_polynomial {φ₀ : Vec 2 → ℝ}
    (hc : HasCompactSupport φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hmass : ∫ z, φ₀ z = 1) (n : ℕ+) {K : ℕ} (hK : 0 < K) (hKn : K ≤ 2*(n:ℕ))
    (F : Vec 2 → E) (H : Vec 2 →L[ℝ] Vec 2) :
    (∫ z : Vec 2, momentKernel φ₀ n z •
      ∑ k ∈ Finset.range K, (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k F 0 (fun _ => H z)) = F 0 := by
  simp_rw [Finset.smul_sum]
  rw [integral_finsetSum _ (fun k _ => integrable_momentKernel_taylor_term hc hd n F H k)]
  have hk (k : ℕ) (hk : k ∈ Finset.range K) :
      (∫ z : Vec 2, momentKernel φ₀ n z •
        ((k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k F 0 (fun _ => H z))) =
        if k = 0 then F 0 else 0 := by
    by_cases h0 : k = 0
    · subst k
      simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul, iteratedFDeriv_zero_apply, ite_true]
      rw [integral_smul_const, integral_momentKernel (hd.continuous.integrable_of_hasCompactSupport hc) hmass n, one_smul]
    · rw [ite_eq_right h0]
      simp_rw [smul_comm (momentKernel φ₀ n _), iteratedFDeriv_same_direction_eq_tensor]
      rw [integral_smul, integral_directionalTensorValue_momentKernel hc hd hmass n _ H
        (Nat.pos_of_ne_zero h0) ((Finset.mem_range.mp hk).trans_le hKn), smul_zero]
  rw [Finset.sum_congr rfl hk]
  simp only [Finset.sum_ite_eq', Finset.mem_range, hK, ite_true]
end

end AVRegularity.Analysis.Convolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped Topology
namespace AVRegularity.Analysis.Convolution

/-! Strong approximation in the actual ordered weak Sobolev graphs by literal shrinking averages. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]

theorem tendsto_planeWeakAverage_component {K : ℕ}
    (ρ : ℕ → Vec 2 →+ Vec 2) (hρ : ∀ m, Continuous (ρ m))
    (hzero : ∀ z, Tendsto (fun m => ρ m z) atTop (𝓝 0))
    {κ : Vec 2 → ℝ} (hκ : Integrable κ) (hmass : ∫ z, κ z = 1)
    (f : PlaneHk (Set.univ : Set (Vec 2)) K E) (a : JetIndex2 K) :
    Tendsto (fun m => (planeWeakAverage (ρ m) (hρ m) κ hκ f).val a) atTop (𝓝 (f.val a)) := by
  have h := (planeToUniv.continuous.tendsto (univToPlane (f.val a))).comp
    (tendsto_averagingOperator_of_tendsto_zero ρ hρ hzero hκ hmass (univToPlane (f.val a)))
  change Tendsto (fun m => planeToUniv (averagingOperator (ρ m) (hρ m) κ hκ (univToPlane (f.val a)))) atTop (𝓝 (f.val a))
  simpa only [Function.comp_def, planeToUniv_univToPlane] using h

theorem tendsto_periodicWeakAverage_component {K : ℕ}
    (ρ : ℕ → Vec 2 →+ Vec 2) (hρ : ∀ m, Continuous (ρ m))
    (hzero : ∀ z, Tendsto (fun m => ρ m z) atTop (𝓝 0))
    {κ : Vec 2 → ℝ} (hκ : Integrable κ) (hmass : ∫ z, κ z = 1)
    (f : TorusHk K E) (a : JetIndex2 K) :
    Tendsto (fun m => (periodicWeakAverage (ρ m) (hρ m) κ hκ f).val a) atTop (𝓝 (f.val a)) := by
  have hz (z : Vec 2) := (continuous_torusQuotient.tendsto 0).comp (hzero z)
  have h := (torusToCell.continuous.tendsto (cellToTorus (f.val a))).comp
    (tendsto_averagingOperator_of_tendsto_zero (fun m => torusQuotient.comp (ρ m))
      (fun m => continuous_torusQuotient.comp (hρ m))
      (fun z => by
        change Tendsto (fun m => torusQuotient (ρ m z)) atTop (𝓝 0)
        simpa only [Function.comp_def, map_zero] using hz z)
      hκ hmass (cellToTorus (f.val a)))
  change Tendsto (fun m => torusToCell (averagingOperator (torusQuotient.comp (ρ m)) (continuous_torusQuotient.comp (hρ m)) κ hκ (cellToTorus (f.val a)))) atTop (𝓝 (f.val a))
  simpa only [Function.comp_def, torusToCell_cellToTorus] using h

theorem tendsto_planeWeakAverage {K : ℕ}
    (ρ : ℕ → Vec 2 →+ Vec 2) (hρ : ∀ m, Continuous (ρ m))
    (hzero : ∀ z, Tendsto (fun m => ρ m z) atTop (𝓝 0))
    {κ : Vec 2 → ℝ} (hκ : Integrable κ) (hmass : ∫ z, κ z = 1)
    (f : PlaneHk (Set.univ : Set (Vec 2)) K E) :
    Tendsto (fun m => planeWeakAverage (ρ m) (hρ m) κ hκ f) atTop (𝓝 f) := by
  apply tendsto_subtype_rng.mpr
  have hc : Tendsto (fun m => fun a : JetIndex2 K =>
      (planeWeakAverage (ρ m) (hρ m) κ hκ f).val a) atTop (𝓝 (fun a => f.val a)) :=
    tendsto_pi_nhds.mpr (tendsto_planeWeakAverage_component ρ hρ hzero hκ hmass f)
  have h := (PiLp.continuous_toLp 2
    (fun _ : JetIndex2 K => ComponentL2 (volume.restrict (Set.univ : Set (Vec 2))) E)).tendsto
      (fun a => f.val a) |>.comp hc
  simpa only [Function.comp_def, WithLp.toLp_ofLp] using h

theorem tendsto_periodicWeakAverage {K : ℕ}
    (ρ : ℕ → Vec 2 →+ Vec 2) (hρ : ∀ m, Continuous (ρ m))
    (hzero : ∀ z, Tendsto (fun m => ρ m z) atTop (𝓝 0))
    {κ : Vec 2 → ℝ} (hκ : Integrable κ) (hmass : ∫ z, κ z = 1)
    (f : TorusHk K E) :
    Tendsto (fun m => periodicWeakAverage (ρ m) (hρ m) κ hκ f) atTop (𝓝 f) := by
  apply tendsto_subtype_rng.mpr
  have hc : Tendsto (fun m => fun a : JetIndex2 K =>
      (periodicWeakAverage (ρ m) (hρ m) κ hκ f).val a) atTop (𝓝 (fun a => f.val a)) :=
    tendsto_pi_nhds.mpr (tendsto_periodicWeakAverage_component ρ hρ hzero hκ hmass f)
  have h := (PiLp.continuous_toLp 2
    (fun _ : JetIndex2 K => ComponentL2 (volume.restrict AVenhance.unitCube) E)).tendsto
      (fun a => f.val a) |>.comp hc
  simpa only [Function.comp_def, WithLp.toLp_ofLp] using h

theorem tendsto_planeSmoothing [FiniteDimensional ℝ E] {K : ℕ}
    (R : ℕ → Vec 2 ≃L[ℝ] Vec 2)
    (hzero : ∀ z, Tendsto (fun m => R m z) atTop (𝓝 0))
    {κ : Vec 2 → ℝ} (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ)
    (hmass : ∫ z, κ z = 1) (f : PlaneHk (Set.univ : Set (Vec 2)) K E) :
    Tendsto (fun m => planeSmoothing (K := K) (R m) κ hc hd (univToPlane (f.val (valueIndex2 K))))
      atTop (𝓝 f) := by
  simp_rw [planeSmoothing_eq_weakAverage]
  exact tendsto_planeWeakAverage (fun m => (R m).toLinearEquiv.toAddHom)
    (fun m => (R m).continuous) hzero (hd.continuous.integrable_of_hasCompactSupport hc) hmass f

theorem tendsto_periodicSmoothing [FiniteDimensional ℝ E] {K : ℕ}
    (R : ℕ → Vec 2 ≃L[ℝ] Vec 2)
    (hzero : ∀ z, Tendsto (fun m => R m z) atTop (𝓝 0))
    {κ : Vec 2 → ℝ} (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ)
    (hmass : ∫ z, κ z = 1) (f : TorusHk K E) :
    Tendsto (fun m => periodicSmoothing (K := K) (R m) κ hc hd (cellToTorus (f.val (valueIndex2 K))))
      atTop (𝓝 f) := by
  simp_rw [periodicSmoothing_eq_weakAverage]
  exact tendsto_periodicWeakAverage (fun m => (R m).toLinearEquiv.toAddHom)
    (fun m => (R m).continuous) hzero (hd.continuous.integrable_of_hasCompactSupport hc) hmass f

end AVRegularity.Analysis.Convolution
end
