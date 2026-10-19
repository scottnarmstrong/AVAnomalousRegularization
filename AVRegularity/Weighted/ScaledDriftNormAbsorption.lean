-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Weighted.WordMomentSlots
public import AVRegularity.Weighted.PlaneH1SpectralCutoff
import AVRegularity.CycleEvolution.StrongUniqueness
import AVRegularity.CoupledEnergyPlane.Variational.DerivativeTensorOperator
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.Weighted

/-! Exact spatial weighted production for the actual measurable-time scalar equation. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeScalarDual_compact_production
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ 1 v)
    {Mv : ℝ} (hMv : 0 ≤ Mv) (hvb : ∀ k x, |v x k| ≤ Mv)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ k j, ContDiff ℝ 1 (fun x => G x k j))
    {MG : ℝ} (hMG : 0 ≤ MG) (hGb : ∀ k j x, |G x k j| ≤ MG)
    (q : Vec 2 → ℝ) (hq : ContDiff ℝ 2 q) (hs : HasCompactSupport q)
    (hC : ContDiff ℝ 1 (fun x => scalarFiberCoefficient (E := E) (q x)))
    (A : Fin 2 → ℝ) (hb : ∀ l x, ‖coefficientDerivativeArray
      (fun x => scalarFiberCoefficient (E := E) (q x)) l.val x‖ ≤ A l)
    (u : PlaneHk Set.univ 1 E) (F : PlaneFluxL2 E) :
    let z := planeH1CoefficientOperator (fun x => scalarFiberCoefficient (E := E) (q x)) hC A hb u
    let c := fun j x => q x * v x j + ∑ k : Fin 2, G x k j * fderiv ℝ q x (basisVec k)
    2 * inner ℝ (planeWeakDualRepresentative
      (planeScalarTransport v (fun k => (contDiff_pi.mp hv k).continuous) hMv hvb)
      (planeScalarDiffusion G (fun k j => (hG k j).continuous) hMG hGb) u F) z +
      2 * (∫ x, q x * ∑ k : Fin 2, ∑ j : Fin 2, G x k j * inner ℝ
        (planeH1GradientOperator (E := E) u j x) (planeH1GradientOperator (E := E) u k x)) +
      2 * inner ℝ F (planeH1GradientOperator (E := E) z) =
      ∫ x, (∑ j : Fin 2, fderiv ℝ (c j) x (basisVec j)) *
        ‖planeHkValueOperator (E := E) 1 u x‖ ^ 2 := by
  let z := planeH1CoefficientOperator (fun x => scalarFiberCoefficient (E := E) (q x)) hC A hb u
  let c : Fin 2 → Vec 2 → ℝ := fun j x => q x * v x j +
    ∑ k : Fin 2, G x k j * fderiv ℝ q x (basisVec k)
  let du := planeH1GradientOperator (E := E) u
  let U := planeHkValueOperator (E := E) 1 u
  let P := fun x => q x * ∑ k : Fin 2, ∑ j : Fin 2, G x k j * inner ℝ (du j x) (du k x)
  let H := fun x => ∑ k : Fin 2, inner ℝ (F k x) (planeH1GradientOperator (E := E) z k x)
  let T := fun x => inner ℝ (∑ j : Fin 2, c j x • du j x) (U x)
  have hqc : ContDiff ℝ 1 q := hq.of_le (by norm_num)
  have hqdc k : ContDiff ℝ 1 (fun x => fderiv ℝ q x (basisVec k)) :=
    (hq.fderiv_right (m := (1 : ℕ)) (by norm_num)).clm_apply contDiff_const
  have hc j : ContDiff ℝ 1 (c j) := by
    simpa only [c, Fin.sum_univ_two] using
      (hqc.mul (contDiff_pi.mp hv j)).add
        (((hG 0 j).mul (hqdc 0)).add ((hG 1 j).mul (hqdc 1)))
  have hcs j : HasCompactSupport (c j) := by
    convert
      (hs.mul_right (f' := fun x => v x j)).add
        (((hs.fderiv_apply ℝ (basisVec 0)).mul_left (f := fun x => G x 0 j)).add
          ((hs.fderiv_apply ℝ (basisVec 1)).mul_left (f := fun x => G x 1 j))) using 1
    funext x
    simp only [c, Fin.sum_univ_two]
    rfl
  obtain ⟨Mq, hMq⟩ := hq.continuous.bounded_above_of_compact_support hs
  have hP : Integrable P volume := by
    have he : P = fun x => ∑ k : Fin 2, ∑ j : Fin 2,
        (q x * G x k j) * inner ℝ (du j x) (du k x) := by
      funext x
      simp only [P, Finset.mul_sum, mul_assoc]
    rw [he]
    apply integrable_finsetSum
    intro k _
    apply integrable_finsetSum
    intro j _
    apply (L2.integrable_inner (𝕜 := ℝ) (du j) (du k)).bdd_mul (c := Mq * MG)
      (hq.continuous.mul (hG k j).continuous).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => by
      change ‖q x * G x k j‖ ≤ Mq * MG
      rw [norm_mul, Real.norm_eq_abs (G x k j)]
      exact mul_le_mul (hMq x) (hGb k j x) (abs_nonneg _) ((norm_nonneg (q x)).trans (hMq x)))
  have hH : Integrable H volume :=
    integrable_finsetSum _ (fun k _ => L2.integrable_inner (F k) (planeH1GradientOperator (E := E) z k))
  have hT : Integrable T volume := by
    have he : T = fun x => ∑ j : Fin 2, c j x * inner ℝ (du j x) (U x) := by
      funext x
      simp only [T, sum_inner, real_inner_smul_left]
    rw [he]
    apply integrable_finsetSum
    intro j _
    obtain ⟨Mc, hMc⟩ := (hc j).continuous.bounded_above_of_compact_support (hcs j)
    exact (L2.integrable_inner (𝕜 := ℝ) (du j) U).bdd_mul
      (hc j).continuous.aestronglyMeasurable (Filter.Eventually.of_forall hMc)
  have hpair := planeScalarDual_pair_eq_integral v
    (fun k => (contDiff_pi.mp hv k).continuous) hMv hvb G
    (fun k j => (hG k j).continuous) hMG hGb u z F
  have hp : inner ℝ (planeWeakDualRepresentative
      (planeScalarTransport v (fun k => (contDiff_pi.mp hv k).continuous) hMv hvb)
      (planeScalarDiffusion G (fun k j => (hG k j).continuous) hMG hGb) u F) z =
      -(∫ x, P x) - (∫ x, H x) - (∫ x, T x) := by
    rw [hpair]
    have hsplit : -(∫ x, P x) - (∫ x, H x) - (∫ x, T x) =
        ∫ x, -P x - H x - T x := by
      rw [← integral_neg]
      rw [← integral_sub (f := fun x => -P x) (g := H) hP.neg hH]
      rw [← integral_sub (f := fun x => -P x - H x) (g := T) (hP.neg.sub hH) hT]
    rw [hsplit]
    apply integral_congr_ae
    have hz := planeH1ScalarMultiplier_value_ae q hC A hb u
    have hdz : ∀ᵐ x ∂volume, ∀ k : Fin 2,
        planeH1GradientOperator (E := E) z k x = q x • du k x + fderiv ℝ q x (basisVec k) • U x :=
      ae_all_iff.mpr (fun k => planeH1ScalarMultiplier_gradient_ae q hqc hC A hb u k)
    filter_upwards [hz, hdz] with x hx hd
    change planeHkValueOperator (E := E) 1 z x = q x • U x at hx
    change -(∑ k : Fin 2, v x k * inner ℝ (du k x)
      (planeHkValueOperator (E := E) 1 z x)) -
      (∑ k : Fin 2, inner ℝ ((∑ j : Fin 2, G x k j • du j x) + F k x)
        (planeH1GradientOperator (E := E) z k x)) = -P x - H x - T x
    rw [hx]
    dsimp only [P, H, T, c]
    simp_rw [hd]
    simpa only [neg_mul] using weighted_scalar_production_split (v x) (fun k => fderiv ℝ q x (basisVec k))
      (q x) (G x) (U x) (fun k => du k x) (fun k => F k x)
  have hi := planeH1_compact_divergence_identity u c hc hcs
  have hF : inner ℝ F (planeH1GradientOperator (E := E) z) = ∫ x, H x :=
    planeFlux_inner_eq_integral _ _
  change 2 * _ + 2 * (∫ x, P x) + 2 * _ = _
  rw [hF]
  change 2 * (∫ x, T x) = _ at hi
  linarith only [hp, hi]

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Filter Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped Topology
namespace AVRegularity.Weighted

/-! Weighted projected production is controlled by the true `H¹` multiplier action. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The projected weighted dual pairing has the exact twice-cutoff multiplier test. -/
theorem planeMultiplier_projection_pair
    (A : Lp E 2 (volume : Measure (Vec 2)) →L[ℝ] Lp E 2 (volume : Measure (Vec 2)))
    (B : PlaneHk Set.univ 1 E →L[ℝ] PlaneHk Set.univ 1 E)
    (hAB : ∀ z, A.adjoint (A (planeHkValueOperator (E := E) 1 z)) =
      planeHkValueOperator (E := E) 1 (B z))
    (N : ℕ) (z dual : PlaneHk Set.univ 1 E) :
    inner ℝ (A (hilbertProjection N (planeHkValueOperator (E := E) 1 z)))
      (A ((hilbertBandHkOperator (E := E) N 1).adjoint dual)) =
      inner ℝ dual (planeH1SpectralCutoff N (B (planeH1SpectralCutoff N z))) := by
  rw [real_inner_comm, ← ContinuousLinearMap.adjoint_inner_right]
  rw [← planeH1SpectralCutoff_value, hAB]
  rw [ContinuousLinearMap.adjoint_inner_left]
  rfl

/-- A projected weighted energy derivative separates its dual test and multiplier time derivative. -/
theorem planeMultiplier_projected_production
    (A dA : Lp E 2 (volume : Measure (Vec 2)) →L[ℝ] Lp E 2 (volume : Measure (Vec 2)))
    (B : PlaneHk Set.univ 1 E →L[ℝ] PlaneHk Set.univ 1 E)
    (hAB : ∀ z, A.adjoint (A (planeHkValueOperator (E := E) 1 z)) =
      planeHkValueOperator (E := E) 1 (B z))
    (N : ℕ) (z dual : PlaneHk Set.univ 1 E) :
    2 * inner ℝ (A (hilbertProjection N (planeHkValueOperator (E := E) 1 z)))
      (A ((hilbertBandHkOperator (E := E) N 1).adjoint dual) +
        dA (hilbertProjection N (planeHkValueOperator (E := E) 1 z))) =
      2 * inner ℝ dual (planeH1SpectralCutoff N (B (planeH1SpectralCutoff N z))) +
        2 * inner ℝ (A (hilbertProjection N (planeHkValueOperator (E := E) 1 z)))
          (dA (hilbertProjection N (planeHkValueOperator (E := E) 1 z))) := by
  rw [inner_add_right, planeMultiplier_projection_pair A B hAB]
  ring

/-- Both cutoffs are contractions, so the weighted pairing has a uniform energy-space bound. -/
theorem planeMultiplier_cutoff_pair_bound
    (B : PlaneHk Set.univ 1 E →L[ℝ] PlaneHk Set.univ 1 E)
    (N : ℕ) (z dual : PlaneHk Set.univ 1 E) :
    |inner ℝ dual (planeH1SpectralCutoff N (B (planeH1SpectralCutoff N z)))| ≤
      ‖dual‖ * ‖B‖ * ‖z‖ := by
  calc
    _ ≤ ‖dual‖ * ‖planeH1SpectralCutoff N (B (planeH1SpectralCutoff N z))‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ ‖dual‖ * ‖B (planeH1SpectralCutoff N z)‖ :=
      mul_le_mul_of_nonneg_left (planeH1SpectralCutoff_norm_le _ _) (norm_nonneg _)
    _ ≤ ‖dual‖ * (‖B‖ * ‖planeH1SpectralCutoff N z‖) :=
      mul_le_mul_of_nonneg_left (B.le_opNorm _) (norm_nonneg _)
    _ ≤ ‖dual‖ * ‖B‖ * ‖z‖ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left (planeH1SpectralCutoff_norm_le _ _)
        (mul_nonneg (norm_nonneg dual) (norm_nonneg B))

/-- The twice-cutoff weighted test converges in the full `H¹` carrier. -/
theorem tendsto_planeMultiplier_cutoff_test
    (B : PlaneHk Set.univ 1 E →L[ℝ] PlaneHk Set.univ 1 E) (z : PlaneHk Set.univ 1 E) :
    Tendsto (fun N => planeH1SpectralCutoff N (B (planeH1SpectralCutoff N z))) atTop
      (𝓝 (B z)) :=
  tendsto_planeH1SpectralCutoff_moving _ _
    (B.continuous.tendsto z |>.comp (tendsto_planeH1SpectralCutoff z))

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.Weighted

/-! The gradient of the literal compact weighted H1 test, without any derivative premise. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeH1_cutoff_gradient_ae
    (χ q : Vec 2 → ℝ) (hχ : ContDiff ℝ 2 χ) (hq : ContDiff ℝ 2 q)
    (hsχ : HasCompactSupport χ) (u z : PlaneHk Set.univ 1 E)
    (hz : planeHkValueOperator (E := E) 1 z =ᵐ[volume]
      fun x => (χ x ^ 2 * q x) • planeHkValueOperator (E := E) 1 u x) :
    ∀ᵐ x ∂volume,
      (WithLp.toLp 2 (fun i => planeH1GradientOperator (E := E) z i x) :
        PiLp 2 (fun _ : Fin 2 => E)) =
      (χ x ^ 2 * q x) • WithLp.toLp 2 (fun i => planeH1GradientOperator (E := E) u i x) +
      χ x ^ 2 • scalarHilbertTensor
        (WithLp.toLp 2 (fun i => fderiv ℝ q x (basisVec i)))
        (planeHkValueOperator (E := E) 1 u x) +
      (2 * χ x * q x) • scalarHilbertTensor
        (WithLp.toLp 2 (fun i => fderiv ℝ χ x (basisVec i)))
        (planeHkValueOperator (E := E) 1 u x) := by
  let qt := fun x => χ x ^ 2 * q x
  have hqt : ContDiff ℝ 2 qt := (hχ.pow 2).mul hq
  have hst : HasCompactSupport qt := by
    convert (hsχ.mul_right (f' := χ)).mul_right (f' := q) using 1
    funext x
    exact congrArg (fun a => a * q x) (pow_two (χ x))
  let C := fun x => scalarFiberCoefficient (E := E) (qt x)
  have hC : ContDiff ℝ 1 C := (hqt.of_le (by norm_num)).smul contDiff_const
  have hsC : HasCompactSupport C := hst.smul_right (f' := fun _ => ContinuousLinearMap.id ℝ E)
  obtain ⟨A, hb⟩ := compact_spatial_coefficient_bounds C hC hsC
  let z0 := planeH1CoefficientOperator C hC A hb u
  have hz0 : planeHkValueOperator (E := E) 1 z0 =ᵐ[volume]
      fun x => qt x • planeHkValueOperator (E := E) 1 u x :=
    planeH1ScalarMultiplier_value_ae qt hC A hb u
  have he : z = z0 := planeH1_eq_of_value_ae z z0 (hz.trans hz0.symm)
  have hd := ae_all_iff.mpr (fun i : Fin 2 =>
    planeH1ScalarMultiplier_gradient_ae qt (hqt.of_le (by norm_num)) hC A hb u i)
  rw [he]
  filter_upwards [hd] with x hx
  apply PiLp.ext
  intro i
  change planeH1GradientOperator (E := E) z0 i x =
    (χ x ^ 2 * q x) • planeH1GradientOperator (E := E) u i x +
      χ x ^ 2 • (fderiv ℝ q x (basisVec i) • planeHkValueOperator (E := E) 1 u x) +
      (2 * χ x * q x) • (fderiv ℝ χ x (basisVec i) • planeHkValueOperator (E := E) 1 u x)
  rw [hx i, cutoff_weight_fderiv χ q (hχ.differentiable (by norm_num))
    (hq.differentiable (by norm_num)) x i]
  simp only [qt, add_smul, ← mul_smul]
  rw [← add_assoc]
  congr 1
  congr 1
  ring

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Weighted

/-! The compact production divergence is the literal chart-weight operator. -/

theorem scalar_weight_production_divergence
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ 1 v)
    (hdiv : ∀ x, ∑ j : Fin 2, fderiv ℝ v x (basisVec j) j = 0)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ j k, ContDiff ℝ 1 (fun x => G x j k)) (hGs : ∀ x, (G x).IsSymm)
    (q : Vec 2 → ℝ) (hq : ContDiff ℝ 2 q) (x : Vec 2) :
    (∑ j : Fin 2, fderiv ℝ
      (fun y => q y * v y j + ∑ k : Fin 2, G y k j * fderiv ℝ q y (basisVec k)) x (basisVec j)) =
      (∑ j : Fin 2, v x j * fderiv ℝ q x (basisVec j)) +
        ∑ j : Fin 2, fderiv ℝ
          (fun y => ∑ k : Fin 2, G y j k * fderiv ℝ q y (basisVec k)) x (basisVec j) := by
  have hqc : ContDiff ℝ 1 q := hq.of_le (by norm_num)
  have hgrad k : ContDiff ℝ 1 (fun y => fderiv ℝ q y (basisVec k)) :=
    (hq.fderiv_right (m := (1 : ℕ)) (by norm_num)).clm_apply contDiff_const
  have hmetric j : ContDiff ℝ 1
      (fun y => ∑ k : Fin 2, G y j k * fderiv ℝ q y (basisVec k)) := by
    simpa only [Fin.sum_univ_two] using
      ((hG j 0).mul (hgrad 0)).add ((hG j 1).mul (hgrad 1))
  have hvi j : ContDiff ℝ 1 (fun y => v y j) := contDiff_pi.mp hv j
  have hsym j : (fun y => ∑ k : Fin 2, G y k j * fderiv ℝ q y (basisVec k)) =
      (fun y => ∑ k : Fin 2, G y j k * fderiv ℝ q y (basisVec k)) := by
    funext y
    apply Finset.sum_congr rfl
    intro k _
    rw [(hGs y).apply j k]
  have hd j : fderiv ℝ
      (fun y => q y * v y j + ∑ k : Fin 2, G y k j * fderiv ℝ q y (basisVec k)) x (basisVec j) =
      q x * fderiv ℝ (fun y => v y j) x (basisVec j) +
        v x j * fderiv ℝ q x (basisVec j) +
        fderiv ℝ (fun y => ∑ k : Fin 2, G y j k * fderiv ℝ q y (basisVec k)) x (basisVec j) := by
    have he : (fun y => q y * v y j + ∑ k : Fin 2, G y k j * fderiv ℝ q y (basisVec k)) =
        (fun y => q y * v y j + ∑ k : Fin 2, G y j k * fderiv ℝ q y (basisVec k)) := by
      funext y
      exact congrArg (fun r => q y * v y j + r) (congrFun (hsym j) y)
    rw [he]
    rw [fderiv_fun_add ((hqc.mul (hvi j)).differentiable (by norm_num) x)
      ((hmetric j).differentiable (by norm_num) x),
      fderiv_fun_mul (hqc.differentiable (by norm_num) x) ((hvi j).differentiable (by norm_num) x)]
    simp only [add_apply, smul_apply, smul_eq_mul]
  have hdiv' : (∑ j : Fin 2, fderiv ℝ (fun y => v y j) x (basisVec j)) = 0 := by
    simpa only [fderiv_apply (hv.differentiable (by norm_num) x),
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] using hdiv x
  simp_rw [hd]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hdiv', mul_zero, zero_add]

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.Weighted

/-! Bounds for the time-derivative term of a weighted Hilbert energy. -/

/-- A multiplier and its time derivative have the expected quadratic pairing bound. -/
theorem multiplier_time_pair_bound {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A dA : H →L[ℝ] H) (u : H) :
    |inner ℝ (A u) (dA u)| ≤ ‖A‖ * ‖dA‖ * ‖u‖ ^ 2 := by
  calc
    _ ≤ ‖A u‖ * ‖dA u‖ := abs_real_inner_le_norm _ _
    _ ≤ (‖A‖ * ‖u‖) * (‖dA‖ * ‖u‖) :=
      mul_le_mul (A.le_opNorm u) (dA.le_opNorm u) (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- Plane spectral cutoffs preserve the uniform quadratic multiplier bound. -/
theorem planeMultiplier_time_pair_bound {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    (A dA : Lp E 2 (volume : Measure (Vec 2)) →L[ℝ] Lp E 2 (volume : Measure (Vec 2)))
    (N : ℕ) (u : Lp E 2 (volume : Measure (Vec 2))) :
    |inner ℝ (A (hilbertProjection N u)) (dA (hilbertProjection N u))| ≤
      ‖A‖ * ‖dA‖ * ‖u‖ ^ 2 := by
  exact (multiplier_time_pair_bound A dA _).trans
    (mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hilbertProjection_norm_le N u))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)))

end AVRegularity.Weighted
end
end

section
@[expose] public section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
open AVRegularity.Analysis.Convolution
namespace AVRegularity.Weighted

/-! The continuous `L²` trace and `L²_t H¹_x` slice already contained in a plane energy solution. -/

noncomputable section

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

/-- Read the value trace of a plane solution as an ambient spatial `L²` curve. -/
def coupledPlaneL2Trace {K : ι → ℕ}
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (E i)) (i : ι) (t : ℝ) :
    Lp (E i) 2 (volume : Measure (Vec 2)) :=
  planeHkValueOperator (E := E i) (K i) (u i t)

/-- Read the energy solution's `H^{K+1}` lift in the `H¹` carrier used by the weak-time energy lemma. -/
def coupledPlaneH1Slice {K : ι → ℕ}
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (E i)) (i : ι) (t : ℝ) :
    PlaneHk Set.univ 1 (E i) :=
  truncatePlaneHk (E := E i) (by omega) (w i t)

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (E i)] in
/-- The ambient `L²` pairing reads precisely the representatives used by the weak equation. -/
theorem coupledPlaneL2Trace_inner {K : ι → ℕ}
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (E i)) (i : ι) (t : ℝ)
    (z : PlaneHk Set.univ 1 (E i)) :
    inner ℝ (coupledPlaneL2Trace u i t) (planeHkValueOperator (E := E i) 1 z) =
      ∫ x, inner ℝ ((u i t).toFunction.jet (valueIndex2 (K i)) x)
        (z.toFunction.jet (valueIndex2 1) x) := by
  simp only [coupledPlaneL2Trace, planeHkValueOperator_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [univToPlane_ae ((u i t).val (valueIndex2 (K i))),
    univToPlane_ae (z.val (valueIndex2 1))] with x hu hz
  rw [hu, hz]
  rfl

/-- Every plane solution supplies the trace and spatial lift data for the weak energy bridge. -/
theorem coupledWeakSolution_h1_trace_data {ν a b : ℝ}
    {v : ℝ → Vec 2 → Vec 2} {D : ℕ} {K : ι → ℕ}
    {A : ∀ (i i' : ι) (d : AVRegularity.admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => E i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => E i))}
    {f : ∀ i, PlaneHk Set.univ (K i) (E i)}
    {F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => E i))}
    {g : ∀ i, ℝ → PlaneHk Set.univ (K i) (E i)}
    {u : ∀ i, ℝ → PlaneHk Set.univ (K i) (E i)}
    {w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (E i)}
    (h : IsCoupledWeakSolutionPlane ν a b v D K A f F g u w) (i : ι) :
    ContinuousOn (coupledPlaneL2Trace u i) (Icc a b) ∧
      MemLp (coupledPlaneH1Slice w i) 2 (volume.restrict (Icc a b)) ∧
      (∀ᵐ t ∂volume.restrict (Icc a b),
        coupledPlaneL2Trace u i t =
          planeHkValueOperator (E := E i) 1 (coupledPlaneH1Slice w i t)) := by
  refine ⟨?_, ?_, ?_⟩
  · have hu := h.1 i
    exact (planeHkValueOperator (E := E i) (K i)).continuous.comp_continuousOn hu
  · let T : PlaneHk Set.univ (K i + 1) (E i) →L[ℝ] PlaneHk Set.univ 1 (E i) :=
      truncatePlaneHk (E := E i) (by omega)
    exact T.comp_memLp' (h.2.1 i)
  · have htruncate := h.2.2.1 i
    filter_upwards [htruncate] with t ht
    have hvalue : planeHkValueOperator (E := E i) 1
        (coupledPlaneH1Slice w i t) =
        planeHkValueOperator (E := E i) (K i)
          (truncatePlaneHk (E := E i) (by omega) (w i t)) := by
      apply Lp.ext
      simp only [planeHkValueOperator_apply, coupledPlaneH1Slice,
        truncatePlaneHk_apply]
      rfl
    have hvalue' : planeHkValueOperator (E := E i) (K i)
        (truncatePlaneHk (E := E i) (by omega) (w i t)) =
        planeHkValueOperator (E := E i) (K i) (u i t) :=
      congrArg (planeHkValueOperator (E := E i) (K i)) ht
    exact hvalue'.symm.trans hvalue.symm

/-- A plane solution becomes the weak Hilbert curve once its weak RHS is represented in `H¹`. -/
theorem coupledWeakSolution_planeWeakHilbertCurve {ν a b : ℝ}
    {v : ℝ → Vec 2 → Vec 2} {D : ℕ} {K : ι → ℕ}
    {A : ∀ (i i' : ι) (d : AVRegularity.admissibleOrders K D i i'), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => E i')) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => E i))}
    {f : ∀ i, PlaneHk Set.univ (K i) (E i)}
    {F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => E i))}
    {g : ∀ i, ℝ → PlaneHk Set.univ (K i) (E i)}
    {u : ∀ i, ℝ → PlaneHk Set.univ (K i) (E i)}
    {w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (E i)}
    (h : IsCoupledWeakSolutionPlane ν a b v D K A f F g u w) (i : ι)
    (dual : ℝ → PlaneHk Set.univ 1 (E i))
    (hdual : MemLp dual 2 (volume.restrict (Icc a b)))
    (hincrement : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
      ∀ z : PlaneHk Set.univ 1 (E i),
        inner ℝ (coupledPlaneL2Trace u i t)
            (planeHkValueOperator (E := E i) 1 z) -
          inner ℝ (coupledPlaneL2Trace u i s)
            (planeHkValueOperator (E := E i) 1 z) =
          ∫ r in s..t, inner ℝ (dual r) z) :
    PlaneWeakHilbertCurve (E := E i) a b (coupledPlaneL2Trace u i)
      (coupledPlaneH1Slice w i) dual := by
  have hdata := coupledWeakSolution_h1_trace_data h i
  exact ⟨hdata.1, hdata.2.1, hdual, hdata.2.2, hincrement⟩

end

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization Filter
open scoped Topology
namespace AVRegularity.Weighted

/-! Remove compact spatial cutoffs from the time-integrated bounded weighted dissipation. -/

variable {E : Type*} [NormedAddCommGroup E]

theorem value_product_spatial_cutoff_time_tendsto
    (χ : ℕ → Vec 2 → ℝ) (hχc : ∀ n, Continuous (χ n))
    (hχ : ∀ n x, 0 ≤ χ n x ∧ χ n x ≤ 1)
    (hχlim : ∀ x, Tendsto (fun n => χ n x) atTop (𝓝 1))
    (q : ℝ → Vec 2 → ℝ) (hq : ∀ t, Continuous (q t))
    (hqm : Measurable (Function.uncurry q)) {B : ℝ} (hB : 0 ≤ B)
    (hqb : ∀ t x, |q t x| ≤ B) (hq0 : ∀ t x, 0 ≤ q t x)
    (μ : Measure ℝ)
    (U V : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (hU : MemLp U 2 μ) (hV : MemLp V 2 μ) :
    Tendsto (fun n => ∫ t, ∫ x, χ n x ^ 2 * q t x * (‖U t x‖ * ‖V t x‖) ∂volume ∂μ) atTop
      (𝓝 (∫ t, ∫ x, q t x * (‖U t x‖ * ‖V t x‖) ∂volume ∂μ)) := by
  let f := fun t x => q t x * (‖U t x‖ * ‖V t x‖)
  let en := fun n t => ∫ x, χ n x ^ 2 * f t x
  let energy := fun t => ∫ x, f t x
  have hf t : Integrable (f t) volume := bounded_weight_value_product_integrable (U t) (V t) (q t)
    (hq t).aestronglyMeasurable (Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs] using hqb t x))
  have hf0 t x : 0 ≤ f t x := mul_nonneg (hq0 t x) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have henergy : Integrable energy μ := weighted_spatial_value_product_time_integrable q hq hqm hB hqb U V hU hV
  have hen n : Integrable (en n) μ := by
    have hj : Measurable (Function.uncurry (fun t x => χ n x ^ 2 * q t x)) := by
      convert (((hχc n).measurable.comp measurable_snd).pow_const 2).mul hqm using 1
      funext p
      rfl
    have hi := weighted_spatial_value_product_time_integrable (E := E)
      (fun t x => χ n x ^ 2 * q t x) (fun t => ((hχc n).pow 2).mul (hq t)) hj hB
      (fun t x => by
        rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        have hs : χ n x ^ 2 ≤ 1 := by nlinarith only [(hχ n x).1, (hχ n x).2]
        exact (mul_le_mul hs (hqb t x) (abs_nonneg _) (by norm_num)).trans_eq (one_mul B)) U V hU hV
    convert hi using 1
    funext t
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by dsimp only [f]; ring)
  have hlim t : Tendsto (fun n => en n t) atTop (𝓝 (energy t)) :=
    integral_spatial_cutoff_tendsto χ (f t) (fun n => (hχc n).aestronglyMeasurable) hχ hχlim (hf t)
  have hbound n t : ‖en n t‖ ≤ energy t := by
    obtain ⟨_, h0, hle⟩ := spatial_cutoff_integrable_bound (χ n) (f t)
      (hχc n).aestronglyMeasurable (hχ n) (hf t) (hf0 t)
    rw [Real.norm_of_nonneg h0]
    exact hle
  have ht := tendsto_integral_of_dominated_convergence energy
    (fun n => (hen n).aestronglyMeasurable) henergy
    (fun n => Eventually.of_forall (hbound n)) (Eventually.of_forall hlim)
  convert ht using 1
  funext n
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by dsimp only [en, f]; ring))

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.Weighted

/-! Spatial energy production depends only on the literal weighted value of the test. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeScalarDual_compact_production_of_value
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ 1 v)
    {Mv : ℝ} (hMv : 0 ≤ Mv) (hvb : ∀ k x, |v x k| ≤ Mv)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ k j, ContDiff ℝ 1 (fun x => G x k j))
    {MG : ℝ} (hMG : 0 ≤ MG) (hGb : ∀ k j x, |G x k j| ≤ MG)
    (q : Vec 2 → ℝ) (hq : ContDiff ℝ 2 q) (hs : HasCompactSupport q)
    (u z : PlaneHk Set.univ 1 E) (F : PlaneFluxL2 E)
    (hz : planeHkValueOperator (E := E) 1 z =ᵐ[volume]
      fun x => q x • planeHkValueOperator (E := E) 1 u x) :
    let c := fun j x => q x * v x j + ∑ k : Fin 2, G x k j * fderiv ℝ q x (basisVec k)
    2 * inner ℝ (planeWeakDualRepresentative
      (planeScalarTransport v (fun k => (contDiff_pi.mp hv k).continuous) hMv hvb)
      (planeScalarDiffusion G (fun k j => (hG k j).continuous) hMG hGb) u F) z +
      2 * (∫ x, q x * ∑ k : Fin 2, ∑ j : Fin 2, G x k j * inner ℝ
        (planeH1GradientOperator (E := E) u j x) (planeH1GradientOperator (E := E) u k x)) +
      2 * inner ℝ F (planeH1GradientOperator (E := E) z) =
      ∫ x, (∑ j : Fin 2, fderiv ℝ (c j) x (basisVec j)) *
        ‖planeHkValueOperator (E := E) 1 u x‖ ^ 2 := by
  let C := fun x => scalarFiberCoefficient (E := E) (q x)
  have hC : ContDiff ℝ 1 C := (hq.of_le (by norm_num)).smul contDiff_const
  have hsC : HasCompactSupport C := hs.smul_right (f' := fun _ => ContinuousLinearMap.id ℝ E)
  obtain ⟨A, hb⟩ := compact_spatial_coefficient_bounds C hC hsC
  let z0 := planeH1CoefficientOperator C hC A hb u
  have hz0 : planeHkValueOperator (E := E) 1 z0 =ᵐ[volume]
      fun x => q x • planeHkValueOperator (E := E) 1 u x :=
    planeH1ScalarMultiplier_value_ae q hC A hb u
  have he : z = z0 := planeH1_eq_of_value_ae z z0 (hz.trans hz0.symm)
  rw [he]
  exact planeScalarDual_compact_production v hv hMv hvb G hG hMG hGb q hq hs hC A hb u F

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Filter Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CycleEvolution
open scoped Topology
namespace AVRegularity.Weighted

/-! The exact time-dependent multiplier energy identity for any plane weak energy curve. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- Actual strong spatial cutoffs justify the time-dependent weighted energy test. -/
theorem planeWeak_multiplier_energy_increment_integrable {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → Lp E 2 (volume : Measure (Vec 2))}
    {slice dual : ℝ → PlaneHk Set.univ 1 E}
    (h : PlaneWeakHilbertCurve a b u slice dual)
    (A dA : ℝ → Lp E 2 (volume : Measure (Vec 2)) →L[ℝ] Lp E 2 (volume : Measure (Vec 2)))
    (B : ℝ → PlaneHk Set.univ 1 E →L[ℝ] PlaneHk Set.univ 1 E)
    (hA : AbsolutelyContinuousOnInterval A a b)
    (hdA : ∀ᵐ t ∂volume.restrict (uIcc a b), HasDerivAt A (dA t) t)
    (hAB : ∀ t z, (A t).adjoint (A t (planeHkValueOperator (E := E) 1 z)) =
      planeHkValueOperator (E := E) 1 (B t z))
    (MA Md MB : ℝ) (hMA : 0 ≤ MA) (_hMd : 0 ≤ Md) (_hMB : 0 ≤ MB)
    (hbA : ∀ t, ‖A t‖ ≤ MA) (hbdA : ∀ t, ‖dA t‖ ≤ Md) (hbB : ∀ t, ‖B t‖ ≤ MB) :
    (‖A b (u b)‖ ^ 2 - ‖A a (u a)‖ ^ 2 =
      ∫ t in a..b, 2 * inner ℝ (dual t) (B t (slice t)) +
        2 * inner ℝ (A t (u t)) (dA t (u t))) ∧
      IntervalIntegrable (fun t => 2 * inner ℝ (dual t) (B t (slice t)) +
        2 * inner ℝ (A t (u t)) (dA t (u t))) volume a b := by
  let U (N : ℕ) (t : ℝ) := A t (planeWeakProjectedState N u t)
  let D (N : ℕ) (t : ℝ) := A t (planeWeakProjectedDerivative N dual t) +
    dA t (planeWeakProjectedState N u t)
  have htime (N : ℕ) : StrongTimeRegularity a b (U N) (D N) :=
    strongTimeRegularity_clm_apply hA hdA (h.projected_strongTime hab N)
  let bound : ℝ → ℝ := fun t =>
    2 * (MB * (‖dual t‖ * ‖slice t‖) + MA * Md * ‖u t‖ ^ 2)
  have hu : MemLp u 2 (volume.restrict (Icc a b)) :=
    (memLp_congr_ae h.agrees).2 ((planeHkValueOperator (E := E) 1).comp_memLp' h.state)
  have hprod : Integrable (fun t => ‖dual t‖ * ‖slice t‖)
      (volume.restrict (Icc a b)) :=
    memLp_one_iff_integrable.mp (h.dual_mem.norm.mul h.state.norm : MemLp _ 1 _)
  have husq : Integrable (fun t => ‖u t‖ ^ 2) (volume.restrict (Icc a b)) := by
    simpa only [pow_two, Pi.mul_apply] using
      (memLp_one_iff_integrable.mp (hu.norm.fun_mul hu.norm : MemLp _ 1 _))
  have hbound : IntegrableOn bound (Ioc a b) volume :=
    (((hprod.const_mul MB).add (husq.const_mul (MA * Md))).const_mul 2).mono_measure
      (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)
  apply energy_increment_integrable_of_dominated_approximation hab U D htime (A a (u a)) (A b (u b))
    ((A a).continuous.tendsto _ |>.comp (tendsto_hilbertProjection (u a)))
    ((A b).continuous.tendsto _ |>.comp (tendsto_hilbertProjection (u b)))
    _ bound hbound
  · intro N
    have ha := h.agrees.filter_mono
      (ae_mono (Measure.restrict_mono Ioc_subset_Icc_self le_rfl))
    filter_upwards [ha] with t ht
    have hmain : |inner ℝ (dual t)
        (planeH1SpectralCutoff N (B t (planeH1SpectralCutoff N (slice t))))| ≤
        MB * (‖dual t‖ * ‖slice t‖) := by
      calc
        _ ≤ ‖dual t‖ * ‖B t‖ * ‖slice t‖ := planeMultiplier_cutoff_pair_bound _ _ _ _
        _ ≤ MB * (‖dual t‖ * ‖slice t‖) := by
          calc
            _ ≤ ‖dual t‖ * MB * ‖slice t‖ := by gcongr; exact hbB t
            _ = _ := by ring
    have hrem : |inner ℝ (A t (hilbertProjection N (u t)))
        (dA t (hilbertProjection N (u t)))| ≤ MA * Md * ‖u t‖ ^ 2 := by
      calc
        _ ≤ ‖A t‖ * ‖dA t‖ * ‖u t‖ ^ 2 := planeMultiplier_time_pair_bound _ _ _ _
        _ ≤ _ := by gcongr; exact hbA t; exact hbdA t
    change ‖2 * inner ℝ (A t (hilbertProjection N (u t)))
      (A t ((hilbertBandHkOperator (E := E) N 1).adjoint (dual t)) +
        dA t (hilbertProjection N (u t)))‖ ≤ bound t
    rw [Real.norm_eq_abs, ht, planeMultiplier_projected_production (A t) (dA t) (B t) (hAB t)]
    rw [ht] at hrem
    calc
      _ ≤ |2 * inner ℝ (dual t)
          (planeH1SpectralCutoff N (B t (planeH1SpectralCutoff N (slice t))))| +
          |2 * inner ℝ (A t (hilbertProjection N (planeHkValueOperator (E := E) 1 (slice t))))
            (dA t (hilbertProjection N (planeHkValueOperator (E := E) 1 (slice t))))| := abs_add_le _ _
      _ ≤ 2 * (MB * (‖dual t‖ * ‖slice t‖) +
          MA * Md * ‖planeHkValueOperator (E := E) 1 (slice t)‖ ^ 2) := by
        simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        nlinarith [hmain, hrem]
      _ = bound t := by dsimp only [bound]; rw [ht]
  · have ha := h.agrees.filter_mono
      (ae_mono (Measure.restrict_mono Ioc_subset_Icc_self le_rfl))
    filter_upwards [ha] with t ht
    have hm := (Filter.Tendsto.inner (𝕜 := ℝ) (tendsto_const_nhds (x := dual t))
      (tendsto_planeMultiplier_cutoff_test (B t) (slice t))).const_mul (2 : ℝ)
    have hr := (((A t).continuous.tendsto _ |>.comp (tendsto_hilbertProjection (u t))).inner
      ((dA t).continuous.tendsto _ |>.comp (tendsto_hilbertProjection (u t)))).const_mul (2 : ℝ)
    have hseq : (fun N => 2 * inner ℝ (U N t) (D N t)) =
        fun N => 2 * inner ℝ (dual t)
            (planeH1SpectralCutoff N (B t (planeH1SpectralCutoff N (slice t)))) +
          2 * inner ℝ (A t (hilbertProjection N (u t))) (dA t (hilbertProjection N (u t))) := by
      funext N
      change 2 * inner ℝ (A t (hilbertProjection N (u t)))
        (A t ((hilbertBandHkOperator (E := E) N 1).adjoint (dual t)) +
          dA t (hilbertProjection N (u t))) = _
      rw [ht, planeMultiplier_projected_production (A t) (dA t) (B t) (hAB t)]
    rw [hseq]
    exact hm.add hr

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Actual source curves have the principal scalar form with value and flux residuals. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeSourceCurve_scalar_residual {a b : ℝ}
    (T : ℝ → PlaneFluxL2 E →L[ℝ] Lp E 2 (volume : Measure (Vec 2)))
    (D : ℝ → PlaneFluxL2 E →L[ℝ] PlaneFluxL2 E)
    (u : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (slice : ℝ → PlaneHk Set.univ 1 E)
    (H : ℝ → Lp E 2 (volume : Measure (Vec 2))) (S : ℝ → PlaneFluxL2 E)
    (h : PlaneWeakHilbertCurve a b u slice (fun t => planeSourceDual (H t) (S t))) :
    PlaneWeakHilbertCurve a b u slice
      (fun t => planeValueForcedDual (T t) (D t) (slice t)
        (S t - D t (planeH1GradientOperator (slice t)))
        (H t + T t (planeH1GradientOperator (slice t)))) := by
  have he : (fun t => planeSourceDual (H t) (S t)) =
      (fun t => planeValueForcedDual (T t) (D t) (slice t)
        (S t - D t (planeH1GradientOperator (slice t)))
        (H t + T t (planeH1GradientOperator (slice t)))) :=
    funext (fun t => planeSourceDual_scalar_residual (T t) (D t) (slice t) (H t) (S t))
  rw [← he]
  exact h

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Weighted

/-! The chart defect is the divergence of its scalar flux, including after clipping. -/

def scalarChartFlux (v : Vec 2 → Vec 2) (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (q : Vec 2 → ℝ) (Φ : Fin 2 → Vec 2 → ℝ) (i : Fin 2) : Vec 2 → ℝ :=
  fun x => q x * v x i + ∑ j : Fin 2, G x i j * fderiv ℝ q x (basisVec j) - Φ i x

theorem scalarChartFlux_contDiff (v : Vec 2 → Vec 2) (hv : ContDiff ℝ 1 v)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ i j, ContDiff ℝ 1 (fun x => G x i j))
    (q : Vec 2 → ℝ) (hq : ContDiff ℝ 2 q)
    (Φ : Fin 2 → Vec 2 → ℝ) (hΦ : ∀ i, ContDiff ℝ 1 (Φ i)) (i : Fin 2) :
    ContDiff ℝ 1 (scalarChartFlux v G q Φ i) := by
  have hp j : ContDiff ℝ 1 (fun x => fderiv ℝ q x (basisVec j)) :=
    (hq.fderiv_right (m := (1 : ℕ)) (by norm_num)).clm_apply contDiff_const
  convert
    (((hq.of_le (by norm_num)).mul (contDiff_pi.mp hv i)).add
      (((hG i 0).mul (hp 0)).add ((hG i 1).mul (hp 1)))).sub (hΦ i) using 1
  funext x
  simp only [scalarChartFlux, Fin.sum_univ_two]

theorem scalarChartFlux_divergence (v : Vec 2 → Vec 2) (hv : ContDiff ℝ 1 v)
    (hdiv : ∀ x, ∑ j : Fin 2, fderiv ℝ v x (basisVec j) j = 0)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ i j, ContDiff ℝ 1 (fun x => G x i j)) (hGs : ∀ x, (G x).IsSymm)
    (q : Vec 2 → ℝ) (hq : ContDiff ℝ 2 q)
    (Φ : Fin 2 → Vec 2 → ℝ) (hΦ : ∀ i, ContDiff ℝ 1 (Φ i)) (x : Vec 2) :
    (∑ i : Fin 2, fderiv ℝ (scalarChartFlux v G q Φ i) x (basisVec i)) =
      (∑ i : Fin 2, v x i * fderiv ℝ q x (basisVec i)) +
      (∑ i : Fin 2, fderiv ℝ (fun y => ∑ j : Fin 2,
        G y i j * fderiv ℝ q y (basisVec j)) x (basisVec i)) -
      ∑ i : Fin 2, fderiv ℝ (Φ i) x (basisVec i) := by
  have hp i : ContDiff ℝ 1 (fun y => q y * v y i + ∑ j : Fin 2,
      G y i j * fderiv ℝ q y (basisVec j)) := by
    convert scalarChartFlux_contDiff v hv G hG q hq
      (fun _ _ => 0) (fun _ => contDiff_const) i using 1
    funext y
    simp only [scalarChartFlux, sub_zero]
  have hd i : fderiv ℝ (scalarChartFlux v G q Φ i) x (basisVec i) =
      fderiv ℝ (fun y => q y * v y i + ∑ j : Fin 2,
        G y i j * fderiv ℝ q y (basisVec j)) x (basisVec i) -
      fderiv ℝ (Φ i) x (basisVec i) := by
    unfold scalarChartFlux
    rw [fderiv_fun_sub ((hp i).differentiable (by norm_num) x)
      ((hΦ i).differentiable (by norm_num) x)]
    rfl
  simp_rw [hd]
  rw [Finset.sum_sub_distrib]
  congr 1
  have he i : (fun y => q y * v y i + ∑ j : Fin 2,
      G y i j * fderiv ℝ q y (basisVec j)) =
      (fun y => q y * v y i + ∑ j : Fin 2,
      G y j i * fderiv ℝ q y (basisVec j)) := by
    funext y
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [(hGs y).apply i j]
  simp_rw [he]
  exact scalar_weight_production_divergence v hv hdiv G hG hGs q hq x

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization Set
namespace AVRegularity.Weighted

/-! The actual clipped chart flux satisfies the cutoff defect inequality. -/

theorem chartWeights_clipped_flux_defect
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {t₀ S ϖ : ℝ} {zc : Vec 2} {M : ℕ} {Cw : ℕ → ℝ}
    (W : ChartWeights G v t₀ S ϖ zc M Cw) (m : ℕ) (hm : m ≤ M)
    (t : ℝ) (ht : t ∈ Icc t₀ (t₀ + S)) (B g : ℝ) (hB : 0 < B)
    (hg4 : g ≤ 1 / 4) (hGnear : IsMetricNearIdentity G g)
    (hv : ContDiff ℝ 1 (v t))
    (hdiv : ∀ x, ∑ j : Fin 2, fderiv ℝ (v t) x (basisVec j) j = 0)
    (hGs : ∀ x, (G t x).IsSymm)
    (hG : ∀ i j : Fin 2, ContDiff ℝ 1 (fun x => G t x i j)) :
    let q := fun x => clipWeight B (W.W m t x)
    let Φ := fun i x => clipWeightDeriv B (W.W m t x) * W.Phi m t x i
    (∀ i, ContDiff ℝ 1 (scalarChartFlux (v t) (G t) q Φ i)) ∧
    (∀ x, deriv (fun s => clipWeight B (W.W m s x)) t +
      (∑ i : Fin 2, fderiv ℝ (scalarChartFlux (v t) (G t) q Φ i) x (basisVec i)) ≤
        2 * W.lam m * q x) := by
  let q := fun x => clipWeight B (W.W m t x)
  let Φ := fun i x => clipWeightDeriv B (W.W m t x) * W.Phi m t x i
  have hw : ContDiff ℝ 2 (fun x => W.W m t x) := by
    convert (W.smooth m hm).1.comp (contDiff_const.prodMk contDiff_id) using 1 <;> rfl
  have hq : ContDiff ℝ 2 q :=
    (contDiff_const.mul hw).div (contDiff_const.add hw)
      (fun x => ne_of_gt (add_pos hB (W.pos m hm t x)))
  have hΦ i : ContDiff ℝ 1 (Φ i) := by
    have hφ : ContDiff ℝ 1 (fun x => W.Phi m t x i) := by
      have htφ : ContDiff ℝ 1 (fun x => W.Phi m t x) := by
        convert (W.smooth m hm).2.comp (contDiff_const.prodMk contDiff_id) using 1 <;> rfl
      exact contDiff_pi.mp htφ i
    have hc : ContDiff ℝ 1 (fun x => clipWeightDeriv B (W.W m t x)) := by
      exact contDiff_const.div ((contDiff_const.add (hw.of_le (by norm_num))).pow 2)
        (fun x => pow_ne_zero 2 (ne_of_gt (add_pos hB (W.pos m hm t x))))
    exact hc.mul hφ
  refine ⟨fun i => scalarChartFlux_contDiff (v t) hv (G t) hG q hq Φ hΦ i, ?_⟩
  intro x
  rw [scalarChartFlux_divergence (v t) hv hdiv (G t) hG hGs q hq Φ hΦ x]
  have hd := chartWeights_clipped_defect W m hm t ht x B g hB hg4 hGnear 0
    (by simpa using hG)
  change deriv (fun s => clipWeight B (W.W m s x)) t +
    (∑ i : Fin 2, v t x i * fderiv ℝ q x (basisVec i)) +
    (∑ i : Fin 2, fderiv ℝ (fun y => ∑ j : Fin 2,
      G t y i j * fderiv ℝ q y (basisVec j)) x (basisVec i)) ≤
    2 * W.lam m * q x + ∑ i : Fin 2, fderiv ℝ (Φ i) x (basisVec i) at hd
  linarith only [hd]

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev Set
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CycleEvolution
namespace AVRegularity.Weighted

/-! The actual weighted energy has absolute continuity and its exact scalar production. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeWeak_multiplier_energy_strongTime {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → Lp E 2 (volume : Measure (Vec 2))}
    {slice dual : ℝ → PlaneHk Set.univ 1 E}
    (h : PlaneWeakHilbertCurve a b u slice dual)
    (A dA : ℝ → Lp E 2 (volume : Measure (Vec 2)) →L[ℝ] Lp E 2 (volume : Measure (Vec 2)))
    (B : ℝ → PlaneHk Set.univ 1 E →L[ℝ] PlaneHk Set.univ 1 E)
    (hA : AbsolutelyContinuousOnInterval A a b)
    (hdA : ∀ᵐ t ∂volume.restrict (uIcc a b), HasDerivAt A (dA t) t)
    (hAB : ∀ t z, (A t).adjoint (A t (planeHkValueOperator (E := E) 1 z)) =
      planeHkValueOperator (E := E) 1 (B t z))
    (MA Md MB : ℝ) (hMA : 0 ≤ MA) (hMd : 0 ≤ Md) (hMB : 0 ≤ MB)
    (hbA : ∀ t, ‖A t‖ ≤ MA) (hbdA : ∀ t, ‖dA t‖ ≤ Md) (hbB : ∀ t, ‖B t‖ ≤ MB) :
    StrongTimeRegularity a b (fun t => ‖A t (u t)‖ ^ 2)
      (fun t => 2 * inner ℝ (dual t) (B t (slice t)) +
        2 * inner ℝ (A t (u t)) (dA t (u t))) := by
  have hdata := planeWeak_multiplier_energy_increment_integrable hab h A dA B hA hdA hAB
    MA Md MB hMA hMd hMB hbA hbdA hbB
  apply scalarStrongTime_of_primitive hab _ _ hdata.2
  intro t ht
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  have hsub' : uIcc a t ⊆ uIcc a b := by
    simpa only [uIcc_of_le hab, uIcc_of_le ht.1] using hsub
  have hd := hdA.filter_mono (ae_mono (Measure.restrict_mono hsub' le_rfl))
  have he := (planeWeak_multiplier_energy_increment_integrable ht.1 (h.mono hsub)
    A dA B (hA.mono hsub') hd hAB MA Md MB hMA hMd hMB hbA hbdA hbB).1
  linarith only [he]

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.Weighted

/-! Every weighted drift source is L2 from the original velocity and stored jet bounds. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

 theorem scaledDriftMasks_memLp {K : ℕ} {U : Set (Vec 2)}
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (V a B lam : ℝ) (hV : 0 ≤ V) (hvb : ∀ x, ‖v x‖ ≤ V)
    (hjets : ∀ l, 1 ≤ l → l ≤ K → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤
        a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (s : Vec 2 → ℝ) (hs : Continuous s) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x, |s x| ≤ M) (D : RawJet2 (K + 1) E) (hD : JetMemL2On U D) :
    ∀ (j : Fin (K + 1)) (m : PositionMask j.val) (w : DerivativeWord2 j.val),
      MemLp (driftMaskTerm (Nat.le_of_lt_succ j.isLt) v (scaledRawJet s D) m w)
        2 (volume.restrict U) := by
  have hscaled := scaledRawJet_memL2 s hs hM hb D hD
  have hbudget := driftCarrierBudget_bounds K v V a B lam hV hvb hjets
  intro j m w
  let l : Fin (K + 1) := ⟨maskLeftLength j.val m,
    Nat.lt_succ_of_le ((maskLeftLength_le j.val m).trans (Nat.le_of_lt_succ j.isLt))⟩
  exact driftMaskTerm_memLp_of_coefficientBound (Nat.le_of_lt_succ j.isLt)
    v hv (scaledRawJet s D) hscaled m w (driftCarrierBudget K V a B lam l)
    (hbudget l)

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Weighted

/-! Both pieces of the spatial cutoff production flux are genuine compact C1 fields. -/

def cutoffMainFlux (v : Vec 2 → Vec 2) (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (q χ : Vec 2 → ℝ) (Φ : Fin 2 → Vec 2 → ℝ) (i : Fin 2) : Vec 2 → ℝ :=
  fun x => χ x ^ 2 * scalarChartFlux v G q Φ i x

def cutoffCorrectionFlux (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (q χ : Vec 2 → ℝ) (Φ : Fin 2 → Vec 2 → ℝ) (i : Fin 2) : Vec 2 → ℝ :=
  fun x => χ x ^ 2 * Φ i x +
    2 * χ x * q x * ∑ j : Fin 2, G x i j * fderiv ℝ χ x (basisVec j)

theorem cutoff_flux_split_regular
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ 1 v)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ i j, ContDiff ℝ 1 (fun x => G x i j))
    (q χ : Vec 2 → ℝ) (hq : ContDiff ℝ 2 q) (hχ : ContDiff ℝ 2 χ)
    (hsχ : HasCompactSupport χ) (Φ : Fin 2 → Vec 2 → ℝ)
    (hΦ : ∀ i, ContDiff ℝ 1 (Φ i)) :
    (∀ i, ContDiff ℝ 1 (cutoffMainFlux v G q χ Φ i)) ∧
    (∀ i, HasCompactSupport (cutoffMainFlux v G q χ Φ i)) ∧
    (∀ i, ContDiff ℝ 1 (cutoffCorrectionFlux G q χ Φ i)) ∧
    (∀ i, HasCompactSupport (cutoffCorrectionFlux G q χ Φ i)) ∧
    (∀ i x, (χ x ^ 2 * q x) * v x i +
      (∑ j : Fin 2, G x i j * fderiv ℝ (fun y => χ y ^ 2 * q y) x (basisVec j)) =
      cutoffMainFlux v G q χ Φ i x + cutoffCorrectionFlux G q χ Φ i x) := by
  have hχ1 : ContDiff ℝ 1 χ := hχ.of_le (by norm_num)
  have hq1 : ContDiff ℝ 1 q := hq.of_le (by norm_num)
  have hgrad j : ContDiff ℝ 1 (fun x => fderiv ℝ χ x (basisVec j)) :=
    (hχ.fderiv_right (m := (1 : ℕ)) (by norm_num)).clm_apply contDiff_const
  have hrow i : ContDiff ℝ 1 (fun x => ∑ j : Fin 2, G x i j * fderiv ℝ χ x (basisVec j)) := by
    convert ((hG i 0).mul (hgrad 0)).add ((hG i 1).mul (hgrad 1)) using 1
    funext x
    simp only [Fin.sum_univ_two]
  have hsχsq : HasCompactSupport (fun x => χ x ^ 2) := by
    convert hsχ.mul_right (f' := χ) using 1
    funext x
    exact pow_two (χ x)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hχ1.pow 2).mul (scalarChartFlux_contDiff v hv G hG q hq Φ hΦ i)
  · intro i
    exact hsχsq.mul_right
  · intro i
    exact ((hχ1.pow 2).mul (hΦ i)).add
      (((contDiff_const.mul hχ1).mul hq1).mul (hrow i))
  · intro i
    exact (hsχsq.mul_right (f' := Φ i)).add
      (((hsχ.mul_left (f := fun _ => (2 : ℝ))).mul_right (f' := q)).mul_right)
  · intro i x
    exact cutoff_weight_flux_split χ q (hχ.differentiable (by norm_num))
      (hq.differentiable (by norm_num)) v G Φ x i

/-! Spatial regularity of the clipped weight, flux and time derivative. -/

theorem chartWeights_clipped_spatial_regularity
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {t₀ S ϖ : ℝ} {zc : Vec 2} {N : ℕ} {Cw : ℕ → ℝ}
    (W : ChartWeights G v t₀ S ϖ zc N Cw) (m : ℕ) (hm : m ≤ N)
    (t B : ℝ) (hB : 0 < B) :
    ContDiff ℝ 2 (fun x => clipWeight B (W.W m t x)) ∧
    (∀ i : Fin 2, ContDiff ℝ 1 (fun x => clipWeightDeriv B (W.W m t x) * W.Phi m t x i)) ∧
    Continuous (fun x => deriv (fun s => clipWeight B (W.W m s x)) t) := by
  have hw : ContDiff ℝ 2 (fun p : ℝ × Vec 2 => W.W m p.1 p.2) := (W.smooth m hm).1
  have hclip := clipped_field_contDiff B hB _ hw (fun p => W.pos m hm p.1 p.2)
  refine ⟨?_, ?_, timeSlice_deriv_continuous _ hclip t⟩
  · convert hclip.comp (contDiff_const.prodMk contDiff_id) using 1 <;> rfl
  · intro i
    have hw1 : ContDiff ℝ 1 (fun p : ℝ × Vec 2 => W.W m p.1 p.2) := hw.of_le (by norm_num)
    have hws : ContDiff ℝ 1 (fun x => W.W m t x) := by
      convert hw1.comp (contDiff_const.prodMk contDiff_id) using 1 <;> rfl
    have hφ : ContDiff ℝ 1 (fun x => W.Phi m t x i) := by
      have hvec : ContDiff ℝ 1 (fun x => W.Phi m t x) := by
        convert (W.smooth m hm).2.comp (contDiff_const.prodMk contDiff_id) using 1 <;> rfl
      exact contDiff_pi.mp hvec i
    exact (contDiff_const.div ((contDiff_const.add hws).pow 2)
      (fun x => pow_ne_zero 2 (ne_of_gt (add_pos hB (W.pos m hm t x))))).mul hφ

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.Weighted

/-! The exact factorial drift absorption survives multiplication of the raw jets by a weight. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E]

theorem scaledDriftMasks_norm_product_absorption {K Kmax : ℕ} {U : Set (Vec 2)}
    (hK : K ≤ Kmax) (hU : MeasurableSet U)
    (ρ a B lam ν V : ℝ) (hρ : 0 < ρ) (ha : 0 ≤ a) (hB : 1 ≤ B)
    (hlam : 0 < lam) (hν : 0 < ν) (hV : 0 ≤ V)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : a * B * ρ ^ 2 ≤ ν / 8)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hvb : ∀ x, ‖v x‖ ≤ V)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤
        a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (s : Vec 2 → ℝ) (hs : Continuous s) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x, |s x| ≤ M) (D : RawJet2 (K + 1) E) (hD : JetMemL2On U D) :
    let D' := scaledRawJet s D
    let hD' := scaledRawJet_memL2 s hs hM hb D hD
    let hT := scaledDriftMasks_memLp v hv V a B lam hV hvb
      (fun l hl hlK => hjets l hl (hlK.trans hK)) s hs hM hb D hD
    (∑ j : Fin (K + 1), factorialWeight ρ j.val *
      (‖AVRegularity.CoupledEnergyPlane.Variational.driftCommutatorL2Array
        (Nat.le_of_lt_succ j.isLt) v D' (hT j)‖ *
        ‖orderL2Array (jetToL2 D' hD') ⟨j.val, by omega⟩‖)) ≤
      (ν / 4) * gradFactorialNormSq ρ (jetToL2 D' hD') := by
  dsimp only
  exact driftCommutator_norm_product_absorption
    hK ρ a B lam ν hρ ha hB hlam hν hsmall hstrain v hjets (scaledRawJet s D)
    (scaledDriftMasks_memLp v hv V a B lam hV hvb
      (fun l hl hlK => hjets l hl (hlK.trans hK)) s hs hM hb D hD)
    (scaledRawJet_memL2 s hs hM hb D hD) hU

end AVRegularity.Weighted
end
end
