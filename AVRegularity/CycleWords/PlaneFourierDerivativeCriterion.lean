-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.PlaneBlochCoefficients
import AVRegularity.CycleEvolution.CellTimeReverseAdmissibility
public import AVRegularity.Weighted.FluxCoordinateInjection
import AVRegularity.CycleComparison.Residual.ChartTransport.Piola
import AVRegularity.Weighted.SlowBasisProjectionBound
public import AVRegularity.Weighted.PlaneIntervalCoefficients
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Combinatorics.SimpleGraph.Basic

section
@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Datum norms transfer component budgets and are bounded by endpoint energy. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem geometryDataNorm_component_budget (π : ι → ℝ) (Kslot : ι → ℕ)
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (r : ℝ)
    (U V : ∀ i, PlaneHk Set.univ (Kslot i) (h i))
    (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ i, weightedFactorialNormSq n ϖ zc r (Kslot i) (V i) ≤
      ENNReal.ofReal C * weightedFactorialNormSq n ϖ zc r (Kslot i) (U i)) :
    geometryDataNorm π Kslot n ϖ zc r V ≤
      ENNReal.ofReal (C ^ (1 / 2 : ℝ)) * geometryDataNorm π Kslot n ϖ zc r U := by
  unfold geometryDataNorm
  calc
    _ ≤ (ENNReal.ofReal C * ∑ i, ENNReal.ofReal ((π i)⁻¹) *
        weightedFactorialNormSq n ϖ zc r (Kslot i) (U i)) ^ (1 / 2 : ℝ) := by
      apply ENNReal.rpow_le_rpow _ (by norm_num)
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      simpa only [mul_left_comm] using mul_le_mul_right (hb i) (ENNReal.ofReal ((π i)⁻¹))
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
        ENNReal.ofReal_rpow_of_nonneg hC (by norm_num)]

theorem geometryDataNorm_at_time_le_energy (π : ι → ℝ) (Kslot : ι → ℕ)
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (r a b t : ℝ) (ht : t ∈ Set.Icc a b)
    (u : ∀ i, ℝ → PlaneHk Set.univ (Kslot i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (Kslot i + 1) (h i)) :
    geometryDataNorm π Kslot n ϖ zc r (fun i => u i t) ≤
      geometryEnergyNorm π Kslot n ϖ zc r a b u w := by
  unfold geometryDataNorm geometryEnergyNorm
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_right
  apply le_add_right
  exact le_iSup₂_of_le t ht le_rfl

end AVRegularity.CycleWords
end

section
open Homogenization
namespace AVRegularity.CycleWords

/-! The actual quiet set and the finite enlarged pulse regions cover every source time. -/

def interiorPulseQuiet (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ)
    (m : ℕ) (ν : ℝ) (y₀ : Vec 2) : Set ℝ :=
  {t | ∀ z, ocCellDrift α q Λ ζ m ν y₀ t z = 0}

theorem scaled_pulse_window {L τ t k : ℝ} (hL : 0 < L)
    (ht : |t - k * (τ / L)| ≤ 3 / 4 * (τ / L)) :
    |L * t - k * τ| ≤ 3 / 4 * τ := by
  have he : L * t - k * τ = L * (t - k * (τ / L)) := by
    field_simp
  rw [he, abs_mul, abs_of_pos hL]
  calc
    _ ≤ L * (3 / 4 * (τ / L)) := mul_le_mul_of_nonneg_left ht hL.le
    _ = _ := by field_simp

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
open scoped Classical
namespace AVRegularity.CycleWords

/-! The admissible-order diagonal metric sum is exactly the matrix applied to the native gradient. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem metricOrderFlux_sum_eq (D : ℕ) (hD : 2 ≤ D) (K : ι → ℕ)
    (A : Matrix (Fin 2) (Fin 2) ℝ) (U : ∀ u, PlaneHk Set.univ (K u + 1) (h u))
    (v : ι) (z : Vec 2) :
    (∑ u, ∑ d : admissibleOrders K D v u,
      (if hv : v = u ∧ d.1 = 2 then metricFlux A (d.1 - 1) hv.1 (by omega) else 0)
        (WithLp.toLp 2 (fun word : DerivativeWord2 (d.1 - 1) => planeJetOrder (U u) (d.1 - 1) word z))) =
      WithLp.toLp 2 (fun k : Fin 2 => ∑ l : Fin 2, A k l •
        (U v).toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => l⟩ z) := by
  classical
  rw [Finset.sum_eq_single v]
  · have hd2 : 2 ∈ admissibleOrders K D v v := by simp [admissibleOrders, hD]
    let d2 : admissibleOrders K D v v := ⟨2, hd2⟩
    rw [Finset.sum_eq_single d2]
    · apply PiLp.ext
      intro k
      simp only [d2]
      simp [metricFlux, planeJetOrder_eq_stored (show 1 ≤ K v + 1 by omega)]
    · intro d _ hne
      have hd : d.val ≠ 2 := by
        intro he
        exact hne (Subtype.ext he)
      simp only [hd, and_false, dite_false, zero_apply]
    · intro hn
      exact False.elim (hn (Finset.mem_univ d2))
  · intro u _ hne
    apply Finset.sum_eq_zero
    intro d _
    simp only [Ne.symm hne, false_and, dite_false, zero_apply]
  · intro hn
    exact False.elim (hn (Finset.mem_univ v))

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.CoupledEnergyPlane.Fourier
open scoped FourierTransform SchwartzMap
namespace AVRegularity.CycleWords

/-! A genuine Schwartz representative of the literal seam cutoff kernel. -/

def seamFrequencyCoordinate : Vec 2 ≃L[ℝ] HilbertTwo :=
  coordinateHilbertEquiv.symm.trans
    (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := HilbertTwo)
      (Units.mk0 (-(2 * Real.pi)⁻¹) (neg_ne_zero.mpr (inv_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero)))))

theorem seamFrequencyCoordinate_apply (x : Vec 2) :
    seamFrequencyCoordinate x = (-(2 * Real.pi)⁻¹) • WithLp.toLp 2 x := rfl

def seamHilbertCutoffSchwartz (m : Vec 2 → ℝ) (R : ℝ)
    (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0)
    (hs : ContDiff ℝ (⊤ : ℕ∞) m) : 𝓢(HilbertTwo, ℂ) :=
  ((seamCutoff_hasCompactSupport m R hm).comp_homeomorph coordinateHilbertEquiv.toHomeomorph).comp_left
    Complex.ofReal_zero |>.toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp (hs.comp coordinateHilbertEquiv.contDiff))

def seamComplexCutoffSchwartz (m : Vec 2 → ℝ) (R : ℝ)
    (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0)
    (hs : ContDiff ℝ (⊤ : ℕ∞) m) : 𝓢(Vec 2, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ seamFrequencyCoordinate
    (𝓕 (seamHilbertCutoffSchwartz m R hm hs))

theorem seamComplexCutoffSchwartz_eq (m : Vec 2 → ℝ) (R : ℝ)
    (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0)
    (hs : ContDiff ℝ (⊤ : ℕ∞) m) (x : Vec 2) :
    seamComplexCutoffSchwartz m R hm hs x = seamCutoffFourier m x := by
  change (∫ θ : HilbertTwo, 𝐞 (-inner ℝ θ (seamFrequencyCoordinate x)) • (m (WithLp.ofLp θ) : ℂ)) = _
  have hphase (θ : HilbertTwo) :
      inner ℝ θ (seamFrequencyCoordinate x) = seamFourierPairing (WithLp.ofLp θ) x := by
    rw [seamFrequencyCoordinate_apply, inner_smul_right]
    simp only [seamFourierPairing, smul_apply, smul_eq_mul, seamDotPairing_apply,
      PiLp.inner_apply, Real.inner_apply, vecDot]
  simp_rw [hphase]
  exact (PiLp.volume_preserving_ofLp (Fin 2)).integral_comp
    coordinateHilbertEquiv.toHomeomorph.measurableEmbedding
    (fun θ : Vec 2 => 𝐞 (-seamFourierPairing θ x) • (m θ : ℂ))

def seamRealCutoffSchwartz (m : Vec 2 → ℝ) (R : ℝ)
    (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0)
    (hs : ContDiff ℝ (⊤ : ℕ∞) m) : 𝓢(Vec 2, ℝ) :=
  (2 * Real.pi)⁻¹ ^ 2 •
    SchwartzMap.postcompCLM Complex.reCLM (seamComplexCutoffSchwartz m R hm hs)

theorem seamRealCutoffSchwartz_eq (m : Vec 2 → ℝ) (R : ℝ)
    (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0)
    (hs : ContDiff ℝ (⊤ : ℕ∞) m) :
    (seamRealCutoffSchwartz m R hm hs : Vec 2 → ℝ) = cutoffKernel m := by
  funext x
  change (2 * Real.pi)⁻¹ ^ 2 * (seamComplexCutoffSchwartz m R hm hs x).re = _
  rw [seamComplexCutoffSchwartz_eq]
  exact (cutoffKernel_eq_seamCutoffFourier_re m R hm hs.continuous x).symm

end AVRegularity.CycleWords
end

section
namespace AVRegularity.CycleWords

/-! The pointwise compact-test residual uses only metric entry bounds. -/

open AVRegularity.Weighted

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem boundedMetric_cutoff_chart_flux_norm_bound
    (G : Matrix (Fin 2) (Fin 2) ℝ) (hG : ∀ p : PiLp 2 (fun _ : Fin 2 => ℝ), ‖finiteMetricFlux G p‖ ≤ 5 * ‖p‖)
    (v p Φ : PiLp 2 (fun _ : Fin 2 => ℝ)) {q r M : ℝ}
    (hq : 0 ≤ q) (_hr : 0 ≤ r) (_hM : 0 ≤ M)
    (hv : ‖v‖ ≤ 2 * M) (hp : ‖p‖ ≤ r * q) (hΦ : ‖Φ‖ ≤ r * q) :
    ‖q • v + finiteMetricFlux G p - Φ‖ ≤ q * (2 * M + 6 * r) := by
  calc
    _ ≤ ‖q • v + finiteMetricFlux G p‖ + ‖Φ‖ := norm_sub_le _ _
    _ ≤ ‖q • v‖ + ‖finiteMetricFlux G p‖ + ‖Φ‖ := by
      gcongr; exact norm_add_le _ _
    _ ≤ q * (2 * M) + 5 * (r * q) + r * q := by
      rw [norm_smul, Real.norm_of_nonneg hq]
      gcongr
      exact (hG p).trans (by gcongr)
    _ = _ := by ring

theorem boundedMetric_cutoff_residual_bound
    (G : Matrix (Fin 2) (Fin 2) ℝ) (hG : ∀ p : PiLp 2 (fun _ : Fin 2 => ℝ), ‖finiteMetricFlux G p‖ ≤ 5 * ‖p‖)
    (v p Φ h : PiLp 2 (fun _ : Fin 2 => ℝ))
    (du F : PiLp 2 (fun _ : Fin 2 => E)) (u : E)
    {q r M χ η : ℝ} (hq : 0 ≤ q) (hr : 0 ≤ r) (hM : 0 ≤ M)
    (hχ : 0 ≤ χ) (hη : 0 ≤ η)
    (hv : ‖v‖ ≤ 2 * M) (hp : ‖p‖ ≤ r * q) (hΦ : ‖Φ‖ ≤ r * q)
    (hh : ‖h‖ ≤ 2 * η) :
    2 * χ * inner ℝ h (q • v + finiteMetricFlux G p - Φ) * ‖u‖ ^ 2 -
      2 * χ ^ 2 * inner ℝ du (scalarHilbertTensor Φ u) -
      4 * χ * q * inner ℝ du (scalarHilbertTensor (finiteMetricFlux G h) u) -
      2 * χ ^ 2 * q * inner ℝ F du -
      2 * χ ^ 2 * inner ℝ F (scalarHilbertTensor p u) -
      4 * χ * q * inner ℝ F (scalarHilbertTensor h u) ≤
    q * (8 * χ * η * M * ‖u‖ ^ 2 + 32 * χ * η * r * ‖u‖ ^ 2 +
      40 * χ * η * ‖du‖ * ‖u‖ + 2 * χ ^ 2 * r * ‖du‖ * ‖u‖ +
      2 * χ ^ 2 * ‖F‖ * ‖du‖ + 2 * χ ^ 2 * r * ‖F‖ * ‖u‖ +
      8 * χ * η * ‖F‖ * ‖u‖) := by
  have ha := inner_le_budgets h (q • v + finiteMetricFlux G p - Φ) hh
    (boundedMetric_cutoff_chart_flux_norm_bound G hG v p Φ hq hr hM hv hp hΦ)
  have hb := neg_inner_le_budgets du (scalarHilbertTensor Φ u) le_rfl
    (show ‖scalarHilbertTensor Φ u‖ ≤ (r * q) * ‖u‖ by
      rw [scalarHilbertTensor_norm]; gcongr)
  have hg : ‖finiteMetricFlux G h‖ ≤ 10 * η :=
    (hG h).trans (by linarith only [hh])
  have hc := neg_inner_le_budgets du (scalarHilbertTensor (finiteMetricFlux G h) u) le_rfl
    (show ‖scalarHilbertTensor (finiteMetricFlux G h) u‖ ≤ 10 * η * ‖u‖ by
      rw [scalarHilbertTensor_norm]; gcongr)
  have hd := neg_inner_le_budgets F du le_rfl le_rfl
  have he := neg_inner_le_budgets F (scalarHilbertTensor p u) le_rfl
    (show ‖scalarHilbertTensor p u‖ ≤ r * q * ‖u‖ by
      rw [scalarHilbertTensor_norm]; gcongr)
  have hf := neg_inner_le_budgets F (scalarHilbertTensor h u) le_rfl
    (show ‖scalarHilbertTensor h u‖ ≤ 2 * η * ‖u‖ by
      rw [scalarHilbertTensor_norm]; gcongr)
  have ha' := mul_le_mul_of_nonneg_left ha (show 0 ≤ 2 * χ * ‖u‖ ^ 2 by positivity)
  have hb' := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * χ ^ 2 by positivity)
  have hc' := mul_le_mul_of_nonneg_left hc (show 0 ≤ 4 * χ * q by positivity)
  have hd' := mul_le_mul_of_nonneg_left hd (show 0 ≤ 2 * χ ^ 2 * q by positivity)
  have he' := mul_le_mul_of_nonneg_left he (show 0 ≤ 2 * χ ^ 2 by positivity)
  have hf' := mul_le_mul_of_nonneg_left hf (show 0 ≤ 4 * χ * q by positivity)
  have hs : 0 ≤ χ * η * r * q * ‖u‖ ^ 2 := by positivity
  nlinarith only [ha', hb', hc', hd', he', hf', hs]

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Weighted
namespace AVRegularity.CycleWords

/-! A sharper two-dimensional scalar flux bound for the cell metric. -/

theorem finiteMetricFlux_scalar_norm_le_four (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i j, |A i j| ≤ 2) (p : PiLp 2 (fun _ : Fin 2 => ℝ)) :
    ‖finiteMetricFlux A p‖ ≤ 4 * ‖p‖ := by
  have hp : ‖p‖ ^ 2 = p 0 ^ 2 + p 1 ^ 2 := by
    simpa only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs] using PiLp.norm_sq_eq_of_L2 _ p
  have hb (i j : Fin 2) : A i j ^ 2 ≤ 4 := by
    have hh := abs_le.mp (hA i j)
    nlinarith only [hh.1, hh.2]
  have hr (i : Fin 2) : (A i 0 * p 0 + A i 1 * p 1) ^ 2 ≤
      8 * (p 0 ^ 2 + p 1 ^ 2) := by
    have hc : (A i 0 * p 0 + A i 1 * p 1) ^ 2 ≤
        (A i 0 ^ 2 + A i 1 ^ 2) * (p 0 ^ 2 + p 1 ^ 2) := by
      nlinarith only [sq_nonneg (A i 0 * p 1 - A i 1 * p 0)]
    exact hc.trans (mul_le_mul_of_nonneg_right (by linarith only [hb i 0, hb i 1])
      (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  have hn : ‖finiteMetricFlux A p‖ ^ 2 =
      (A 0 0 * p 0 + A 0 1 * p 1) ^ 2 + (A 1 0 * p 0 + A 1 1 * p 1) ^ 2 := by
    simp only [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, finiteMetricFlux,
      Real.norm_eq_abs, sq_abs, smul_eq_mul]
  nlinarith only [hr 0, hr 1, hp, hn, norm_nonneg (finiteMetricFlux A p), norm_nonneg p]

theorem cellMetric_finiteMetricFlux_scalar_norm_le_five
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric G)
    (t : ℝ) (x : Vec 2) (p : PiLp 2 (fun _ : Fin 2 => ℝ)) :
    ‖finiteMetricFlux (G t x) p‖ ≤ 5 * ‖p‖ :=
  (finiteMetricFlux_scalar_norm_le_four (G t x) (CycleEvolution.cellMetric_entry_bound hG t x) p).trans
    (mul_le_mul_of_nonneg_right (by norm_num : (4 : ℝ) ≤ 5) (norm_nonneg p))

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Larger polynomial moment reserves dominate the exact public data, flux, and energy norms. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem weightedFactorialNormSq_moment_mono {K' n N : ℕ} (hn : n ≤ N)
    (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ) (K : ℕ) (U : PlaneHk Set.univ K' E) :
    weightedFactorialNormSq n ϖ zc ρ K U ≤ weightedFactorialNormSq N ϖ zc ρ K U := by
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul' le_rfl
  apply lintegral_mono
  intro z
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  exact pow_le_pow_right₀ (le_add_of_nonneg_right (by positivity)) hn

theorem weightedGradFactorialNormSq_moment_mono {K' n N : ℕ} (hn : n ≤ N)
    (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ) (K : ℕ) (U : PlaneHk Set.univ K' E) :
    weightedGradFactorialNormSq n ϖ zc ρ K U ≤ weightedGradFactorialNormSq N ϖ zc ρ K U := by
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul' le_rfl
  apply lintegral_mono
  intro z
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  exact pow_le_pow_right₀ (le_add_of_nonneg_right (by positivity)) hn

section Family

end Family

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory
open scoped SchwartzMap
namespace AVRegularity.CycleWords

/-! A Schwartz scalar kernel differentiates against genuine integrable rough data. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def schwartzConvolution (k : 𝓢(Vec 2, ℝ)) (f : Vec 2 → E) : Vec 2 → E :=
  fun x => ∫ y, k (x - y) • f y

theorem schwartzConvolution_integrable (k : 𝓢(Vec 2, ℝ)) (f : Vec 2 → E)
    (hf : Integrable f) (x : Vec 2) : Integrable (fun y => k (x - y) • f y) := by
  exact hf.bdd_smul ((SchwartzMap.seminorm ℝ 0 0) k)
    (k.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun y => SchwartzMap.norm_le_seminorm ℝ k (x - y)))

theorem schwartzConvolution_hasFDerivAt (k : 𝓢(Vec 2, ℝ)) (f : Vec 2 → E)
    (hf : Integrable f) (x : Vec 2) :
    HasFDerivAt (schwartzConvolution k f)
      (∫ y, (fderiv ℝ k (x - y)).smulRight (f y)) x := by
  let kd := SchwartzMap.fderivCLM ℝ (Vec 2) ℝ k
  let C := (SchwartzMap.seminorm ℝ 0 0) kd
  have hA (x : Vec 2) : AEStronglyMeasurable (fun y => fderiv ℝ k (x - y)) volume := by
    exact (kd.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hD (x : Vec 2) : AEStronglyMeasurable
      (fun y => (fderiv ℝ k (x - y)).smulRight (f y)) volume := by
    exact (ContinuousLinearMap.smulRightL ℝ (Vec 2) E).continuous₂.comp_aestronglyMeasurable
      ((hA x).prodMk hf.aestronglyMeasurable)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x y => k (x - y) • f y)
    (F' := fun x y => (fderiv ℝ k (x - y)).smulRight (f y))
    (bound := fun y => C * ‖f y‖) (s := Set.univ) (Filter.univ_mem)
  · exact Filter.Eventually.of_forall (fun x => (schwartzConvolution_integrable k f hf x).aestronglyMeasurable)
  · exact schwartzConvolution_integrable k f hf x
  · exact hD x
  · filter_upwards [] with y z _
    rw [ContinuousLinearMap.norm_smulRight_apply]
    exact mul_le_mul_of_nonneg_right (SchwartzMap.norm_le_seminorm ℝ kd (z - y)) (norm_nonneg _)
  · exact hf.norm.const_mul C
  · filter_upwards [] with y z _
    simpa only [ContinuousLinearMap.comp_id, Function.comp_apply, id_eq] using
      ((k.differentiableAt.hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const y)).smul_const (f y))

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.CoupledEnergyPlane.Fourier
open scoped FourierTransform SchwartzMap
namespace AVRegularity.CycleWords

/-! The literal cutoff kernel has the exact mass dictated by its multiplier at zero. -/

theorem schwartz_fourier_integral (f : 𝓢(HilbertTwo, ℂ)) :
    (∫ x, (𝓕 f) x) = f 0 := by
  have hh := congrArg (fun g : 𝓢(HilbertTwo, ℂ) => g 0)
    (FourierTransform.fourierInv_fourier_eq (F := 𝓢(HilbertTwo, ℂ)) f)
  change (∫ x : HilbertTwo, 𝐞 (-inner ℝ x (-0)) • (𝓕 f) x) = f 0 at hh
  simpa only [neg_zero, inner_zero_right, Real.fourierChar.map_zero_eq_one, one_smul] using hh

theorem seamComplexCutoffSchwartz_integral (m : Vec 2 → ℝ) (R : ℝ)
    (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0)
    (hs : ContDiff ℝ (⊤ : ℕ∞) m) :
    (∫ x, seamComplexCutoffSchwartz m R hm hs x) =
      (2 * Real.pi) ^ 2 • (m 0 : ℂ) := by
  let f := seamHilbertCutoffSchwartz m R hm hs
  have ht := (PiLp.volume_preserving_ofLp (Fin 2)).integral_comp
    coordinateHilbertEquiv.toHomeomorph.measurableEmbedding
    (fun x : Vec 2 => seamComplexCutoffSchwartz m R hm hs x)
  have he : (fun θ : HilbertTwo => seamComplexCutoffSchwartz m R hm hs (WithLp.ofLp θ)) =
      fun θ => (𝓕 f) ((-(2 * Real.pi)⁻¹) • θ) := by
    funext θ
    change (𝓕 f) (seamFrequencyCoordinate (WithLp.ofLp θ)) = _
    rw [seamFrequencyCoordinate_apply]
  rw [← ht, he, Measure.integral_comp_smul, schwartz_fourier_integral]
  have hdim : Module.finrank ℝ HilbertTwo = 2 := by simp [HilbertTwo]
  rw [hdim]
  have hscale : |((-(2 * Real.pi)⁻¹) ^ 2)⁻¹| = (2 * Real.pi) ^ 2 := by
    rw [neg_sq, inv_pow, inv_inv, abs_of_nonneg (sq_nonneg _)]
  rw [hscale]
  rfl

theorem seamCutoffKernel_integral (m : Vec 2 → ℝ) (R : ℝ)
    (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0)
    (hs : ContDiff ℝ (⊤ : ℕ∞) m) : (∫ x, cutoffKernel m x) = m 0 := by
  rw [← seamRealCutoffSchwartz_eq m R hm hs]
  change (∫ x, (2 * Real.pi)⁻¹ ^ 2 * (seamComplexCutoffSchwartz m R hm hs x).re) = _
  have hRe := integral_re ((seamComplexCutoffSchwartz m R hm hs).integrable (μ := volume))
  change (∫ x, (seamComplexCutoffSchwartz m R hm hs x).re) =
    (∫ x, seamComplexCutoffSchwartz m R hm hs x).re at hRe
  rw [integral_const_mul, hRe, seamComplexCutoffSchwartz_integral]
  simp only [Complex.smul_re, Complex.ofReal_re, smul_eq_mul]
  rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ (mul_ne_zero two_ne_zero Real.pi_ne_zero)]
  simp

end AVRegularity.CycleWords
end

section
open Homogenization
namespace AVRegularity.CycleWords

/-! Removing slots with no non-quiet time permits endpoint clipping without creating empty pulse
regions. The quiet times are the trimmed ones: every time within `τ/24` is drift-free. -/

/-- The trimmed quiet times: every time within `τ/24` is drift-free. -/
def interiorTrimmedQuiet (τ : ℝ) (v : ℝ → Vec 2 → Vec 2) : Set ℝ :=
  {t | ∀ s ∈ Set.Icc (t - τ / 24) (t + τ / 24), ∀ z, v s z = 0}

theorem interiorTrimmedQuiet_drift {τ : ℝ} (hτ : 0 ≤ τ) {v : ℝ → Vec 2 → Vec 2} {t : ℝ}
    (ht : t ∈ interiorTrimmedQuiet τ v) : ∀ z, v t z = 0 :=
  ht t ⟨by linarith, by linarith⟩

def interiorActivePulseIndices (τ a b : ℝ) (v : ℝ → Vec 2 → Vec 2) : Finset ℤ :=
  by
    classical
    exact (interiorPulseIndices τ a b).filter fun n =>
      ∃ t ∈ Set.Icc a b, t ∈ Set.Icc (interiorPulseRegionLo τ a n)
        (interiorPulseRegionHi τ b n) ∧ t ∉ interiorTrimmedQuiet τ v

theorem interiorActivePulseIndices_join_bound {τ a b : ℝ} (hτ : 0 < τ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) :
    2 * ((interiorActivePulseIndices τ a b v).card : ℝ) ≤ (b - a) / τ + 4 := by
  classical
  have hc : (interiorActivePulseIndices τ a b v).card ≤ (interiorPulseIndices τ a b).card :=
    Finset.card_filter_le _ _
  exact (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hc) (by norm_num : (0 : ℝ) ≤ 2)).trans
    (interiorPulseIndices_join_bound hτ hab)

theorem interiorActivePulseRegion_contains (τ a b D : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (hleft : Set.Ico a (a + D) ⊆ interiorTrimmedQuiet τ v)
    (hright : Set.Ioc (b - D) b ⊆ interiorTrimmedQuiet τ v)
    {n : ℤ} (hn : n ∈ interiorPulseIndices τ a b) {t : ℝ}
    (ht : t ∈ Set.Icc a b)
    (hwide : t ∈ Set.Icc (interiorPulseRegionLo τ a n) (interiorPulseRegionHi τ b n))
    (hz : t ∉ interiorTrimmedQuiet τ v) :
    n ∈ interiorActivePulseIndices τ a b v ∧
      t ∈ Set.Icc (interiorBufferedPulseLo τ a D n) (interiorBufferedPulseHi τ b D n) := by
  classical
  have hlo : a + D ≤ t := by
    by_contra he
    exact hz (hleft ⟨ht.1, lt_of_not_ge he⟩)
  have hhi : t ≤ b - D := by
    by_contra he
    exact hz (hright ⟨lt_of_not_ge he, ht.2⟩)
  refine ⟨Finset.mem_filter.mpr ⟨hn, t, ht, hwide, hz⟩, ?_⟩
  exact ⟨max_le hlo ((le_max_right _ _).trans hwide.1),
    le_min hhi (hwide.2.trans (min_le_right _ _))⟩

theorem interiorActivePulseRegion_nonempty (τ a b D : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (hleft : Set.Ico a (a + D) ⊆ interiorTrimmedQuiet τ v)
    (hright : Set.Ioc (b - D) b ⊆ interiorTrimmedQuiet τ v)
    {n : ℤ} (hn : n ∈ interiorActivePulseIndices τ a b v) :
    interiorBufferedPulseLo τ a D n ≤ interiorBufferedPulseHi τ b D n := by
  classical
  obtain ⟨hn', t, ht, hwide, hz⟩ := Finset.mem_filter.mp hn
  have hc := (interiorActivePulseRegion_contains τ a b D v hleft hright hn' ht hwide hz).2
  exact hc.1.trans hc.2

def interiorActivePulseRegionIndex (τ a b : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (p : Fin (interiorActivePulseIndices τ a b v).card) : ℤ :=
  ((interiorActivePulseIndices τ a b v).equivFin.symm p).val

theorem interiorActivePulseRegionIndex_mem (τ a b : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (p : Fin (interiorActivePulseIndices τ a b v).card) :
    interiorActivePulseRegionIndex τ a b v p ∈ interiorActivePulseIndices τ a b v :=
  ((interiorActivePulseIndices τ a b v).equivFin.symm p).property

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Coordinate metric forcing is exactly the matrix applied to the stored native gradient. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem metricCoordinateFlux_eq_matrix (A : Matrix (Fin 2) (Fin 2) ℝ) (g : Fin 2 → E) :
    (∑ kl : Fin 2 × Fin 2, A kl.1 kl.2 •
      Weighted.fluxCoordinateInjection kl.1 (ContinuousLinearMap.id ℝ E) (g kl.2)) =
      WithLp.toLp 2 (fun k : Fin 2 => ∑ l : Fin 2, A k l • g l) := by
  classical
  apply PiLp.ext
  intro k
  simp only [Fintype.sum_prod_type, WithLp.ofLp_sum, Finset.sum_apply,
    PiLp.smul_apply, Weighted.fluxCoordinateInjection_apply, ContinuousLinearMap.id_apply]
  rw [Finset.sum_eq_single k]
  · simp only [ite_true]
  · intro l _ hne
    apply Finset.sum_eq_zero
    intro j _
    simp only [Ne.symm hne, ite_false, smul_zero]
  · simp

theorem metricCoordinateFlux_eq_stored {K : ℕ}
    (A : Matrix (Fin 2) (Fin 2) ℝ) (U : PlaneHk Set.univ (K + 1) E) (z : Vec 2) :
    (∑ kl : Fin 2 × Fin 2, A kl.1 kl.2 •
      Weighted.fluxCoordinateInjection kl.1 (ContinuousLinearMap.id ℝ E)
        (planeJetOrder U 1 (fun _ => kl.2) z)) =
      WithLp.toLp 2 (fun k : Fin 2 => ∑ l : Fin 2, A k l •
        U.toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => l⟩ z) := by
  apply (metricCoordinateFlux_eq_matrix A
    (fun l => planeJetOrder U 1 (fun _ => l) z)).trans
  apply PiLp.ext
  intro k
  change (∑ l : Fin 2, A k l • planeJetOrder U 1 (fun _ => l) z) =
    ∑ l : Fin 2, A k l • U.toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => l⟩ z
  apply Finset.sum_congr rfl
  intro l _
  rw [planeJetOrder_eq_stored (show 1 ≤ K + 1 by omega)]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! The actual component energy, before the inverse mass sum and square root. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def nativeComponentEnergy {K : ℕ} (n : ℕ) (ϖ ρ a b : ℝ)
    (U : ℝ → PlaneHk Set.univ K E) (Uw : ℝ → PlaneHk Set.univ (K + 1) E) : ℝ≥0∞ :=
  (⨆ t ∈ Set.Icc a b, weightedFactorialNormSq n ϖ 0 ρ K (U t)) +
    ∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq n ϖ 0 ρ K (Uw t)

theorem nativeComponentEnergy_moment_mono {K n N : ℕ} (hn : n ≤ N) (ϖ ρ a b : ℝ)
    (U : ℝ → PlaneHk Set.univ K E) (Uw : ℝ → PlaneHk Set.univ (K + 1) E) :
    nativeComponentEnergy n ϖ ρ a b U Uw ≤ nativeComponentEnergy N ϖ ρ a b U Uw := by
  apply add_le_add
  · exact iSup₂_mono (fun t _ => weightedFactorialNormSq_moment_mono hn ϖ 0 ρ K (U t))
  · exact lintegral_mono (fun t => weightedGradFactorialNormSq_moment_mono hn ϖ 0 ρ K (Uw t))

theorem nativeComponentEnergy_gradient_ne_top {K : ℕ} (n : ℕ) (ϖ ρ a b : ℝ)
    (U : ℝ → PlaneHk Set.univ K E) (Uw : ℝ → PlaneHk Set.univ (K + 1) E)
    (he : nativeComponentEnergy n ϖ ρ a b U Uw ≠ ⊤) :
    (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq n ϖ 0 ρ K (Uw t)) ≠ ⊤ :=
  (ENNReal.add_ne_top.mp he).2

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.CoupledEnergyPlane.Fourier LineDeriv
open scoped FourierTransform SchwartzMap
namespace AVRegularity.CycleWords

/-! The actual plane Fourier derivative multiplier in the project coordinates. -/

theorem coordinateVector_inner (ξ : HilbertTwo) (i : Fin 2) :
    inner ℝ ξ (coordinateVector i) = WithLp.ofLp ξ i := by
  simp [coordinateVector, PiLp.inner_apply]

theorem planeFourier_distribution_derivative_ae
    (f g : Lp ℂ 2 (volume : Measure (Vec 2))) (i : Fin 2)
    (hfg : ∂_{coordinateVector i} ((coordinateL2Equiv f : Lp ℂ 2 volume) :
      𝓢'(HilbertTwo, ℂ)) = ((coordinateL2Equiv g : Lp ℂ 2 volume) : 𝓢'(HilbertTwo, ℂ))) :
    fourierL2 g =ᵐ[volume] fun ξ =>
      (2 * (Real.pi : ℂ) * Complex.I) * (ξ i : ℂ) * fourierL2 f ξ := by
  have hh := fourier_derivative_ae (coordinateL2Equiv f) (coordinateL2Equiv g) (coordinateVector i) hfg
  rw [← coordinate_fourierL2 f, ← coordinate_fourierL2 g] at hh
  have he : ∀ᵐ ξ : HilbertTwo ∂volume,
      fourierL2 g (WithLp.ofLp ξ) =
        (2 * (Real.pi : ℂ) * Complex.I) * (WithLp.ofLp ξ i : ℂ) * fourierL2 f (WithLp.ofLp ξ) := by
    filter_upwards [hh, coordinateL2Equiv_ae (fourierL2 f), coordinateL2Equiv_ae (fourierL2 g)]
      with ξ hξ hf hg
    rw [hf, hg, coordinateVector_inner] at hξ
    exact hξ
  exact (PiLp.volume_preserving_toLp (Fin 2)).quasiMeasurePreserving.ae he

theorem planeFourier_real_weakDerivative_ae
    (f g : Lp ℝ 2 (volume : Measure (Vec 2))) (i : Fin 2)
    (hfg : HasWeakPartialDerivOn Set.univ i f g) :
    fourierL2 (ofRealL2 volume g) =ᵐ[volume] fun ξ =>
      (2 * (Real.pi : ℂ) * Complex.I) * (ξ i : ℂ) * fourierL2 (ofRealL2 volume f) ξ :=
  planeFourier_distribution_derivative_ae _ _ i (coordinate_lineDerivOp_of_weakPartial f g i hfg)

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory
open scoped SchwartzMap LineDeriv
namespace AVRegularity.CycleWords

/-! Scalar Schwartz smoothing of rough integrable vector data at every finite order. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem schwartzConvolution_directional_deriv (k : 𝓢(Vec 2, ℝ)) (f : Vec 2 → E)
    (hf : Integrable f) (x v : Vec 2) :
    fderiv ℝ (schwartzConvolution k f) x v = schwartzConvolution (∂_{v} k) f x := by
  let kd := SchwartzMap.fderivCLM ℝ (Vec 2) ℝ k
  let C := (SchwartzMap.seminorm ℝ 0 0) kd
  have hA : AEStronglyMeasurable (fun y => fderiv ℝ k (x - y)) volume :=
    (kd.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hD : AEStronglyMeasurable (fun y => (fderiv ℝ k (x - y)).smulRight (f y)) volume :=
    (ContinuousLinearMap.smulRightL ℝ (Vec 2) E).continuous₂.comp_aestronglyMeasurable
      (hA.prodMk hf.aestronglyMeasurable)
  have hi : Integrable (fun y => (fderiv ℝ k (x - y)).smulRight (f y)) := by
    apply (hf.norm.const_mul C).mono' hD
    filter_upwards [] with y
    rw [ContinuousLinearMap.norm_smulRight_apply]
    exact mul_le_mul_of_nonneg_right (SchwartzMap.norm_le_seminorm ℝ kd (x - y)) (norm_nonneg _)
  rw [(schwartzConvolution_hasFDerivAt k f hf x).fderiv, ContinuousLinearMap.integral_apply hi v]
  unfold schwartzConvolution
  apply integral_congr_ae
  filter_upwards [] with y
  rw [ContinuousLinearMap.smulRight_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]

theorem schwartzConvolution_contDiff_nat (n : ℕ) (k : 𝓢(Vec 2, ℝ)) (f : Vec 2 → E)
    (hf : Integrable f) : ContDiff ℝ n (schwartzConvolution k f) := by
  induction n generalizing k with
  | zero =>
    change ContDiff ℝ 0 (schwartzConvolution k f)
    rw [contDiff_zero]
    exact (show Differentiable ℝ (schwartzConvolution k f) from
      fun x => (schwartzConvolution_hasFDerivAt k f hf x).differentiableAt).continuous
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one]
    apply contDiff_succ_iff_fderiv_apply.mpr
    refine ⟨fun x => (schwartzConvolution_hasFDerivAt k f hf x).differentiableAt, ?_, ?_⟩
    · intro hω
      exact False.elim (by simp at hω)
    · intro v
      have he : (fun x => fderiv ℝ (schwartzConvolution k f) x v) =
          schwartzConvolution (∂_{v} k) f := funext (fun x => schwartzConvolution_directional_deriv k f hf x v)
      rw [he]
      exact ih (∂_{v} k)

theorem schwartzConvolution_contDiff (k : 𝓢(Vec 2, ℝ)) (f : Vec 2 → E)
    (hf : Integrable f) : ContDiff ℝ (⊤ : ℕ∞) (schwartzConvolution k f) :=
  contDiff_infty.mpr (fun n => schwartzConvolution_contDiff_nat n k f hf)

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleWords

/-! Exact dilation of the physical scalar cutoff kernel and its L1 price. -/

theorem seamCutoffKernel_dilation (m : Vec 2 → ℝ) (a : ℝ) (ha : a ≠ 0) (x : Vec 2) :
    cutoffKernel (fun ξ => m (a • ξ)) x =
      |(a ^ 2)⁻¹| * cutoffKernel m (a⁻¹ • x) := by
  have hp (ξ : Vec 2) : vecDot (a • ξ) (a⁻¹ • x) = vecDot ξ x := by
    unfold vecDot
    simp only [Pi.smul_apply, smul_eq_mul]
    congr 1
    funext i
    field_simp
  have hh := Measure.integral_comp_smul (volume : Measure (Vec 2))
    (fun ξ : Vec 2 => m ξ * Real.cos (vecDot ξ (a⁻¹ • x))) a
  have hdim : Module.finrank ℝ (Vec 2) = 2 := by simp [Vec]
  simp_rw [hp] at hh
  rw [hdim] at hh
  unfold cutoffKernel
  rw [hh]
  simp only [smul_eq_mul]
  ring

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory
open scoped Pointwise
namespace AVRegularity.CycleWords

/-! A literal smooth average of almost-everywhere compactly supported data has genuine compact support. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem literalAverage_eq_zero_of_outside_support
    (R : Vec 2 ≃L[ℝ] Vec 2) (κ : Vec 2 → ℝ) (f : Vec 2 → E)
    (A : Set (Vec 2)) (hf : ∀ᵐ y ∂volume, y ∉ A → f y = 0)
    (x : Vec 2) (hx : x ∉ A + R '' tsupport κ) :
    (∫ z, κ z • f (x - R z)) = 0 := by
  apply integral_eq_zero_of_ae
  have ha := (Analysis.Convolution.affineDisplacement_quasiMeasurePreserving R x).ae hf
  filter_upwards [ha] with z hz
  change κ z • f (x - R z) = (0 : E)
  by_cases hk : κ z = 0
  · simp only [hk, zero_smul]
  · have hzκ : z ∈ tsupport κ := subset_tsupport κ hk
    have hzA : x - R z ∉ A := by
      intro hmem
      apply hx
      exact Set.mem_add.mpr ⟨x - R z, hmem, R z, ⟨z, hzκ, rfl⟩, sub_add_cancel x (R z)⟩
    rw [hz hzA, smul_zero]

omit [CompleteSpace E] in
theorem literalAverage_hasCompactSupport
    (R : Vec 2 ≃L[ℝ] Vec 2) (κ : Vec 2 → ℝ) (hκ : HasCompactSupport κ)
    (f : Vec 2 → E) (A : Set (Vec 2)) (hA : IsCompact A)
    (hf : ∀ᵐ y ∂volume, y ∉ A → f y = 0) :
    HasCompactSupport (fun x => ∫ z, κ z • f (x - R z)) := by
  apply HasCompactSupport.of_support_subset_isCompact (hA.add (hκ.image R.continuous))
  intro x hx
  by_contra hout
  exact hx (literalAverage_eq_zero_of_outside_support R κ f A hf x hout)

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! A smooth value representative determines every stored plane weak derivative. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeHk_smooth_jet_readout {K : ℕ} (U : PlaneHk Set.univ K E)
    {f : Vec 2 → E} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hu : planeValue U =ᵐ[volume] f)
    (j : ℕ) (hj : j ≤ K) (w : DerivativeWord2 j) :
    planeJetOrder U j w =ᵐ[volume] orderedDerivative w f := by
  have hlevel : ∀ j, ∀ hj : j ≤ K, ∀ w : DerivativeWord2 j,
      U.toFunction.jet ⟨⟨j, Nat.lt_succ_of_le hj⟩, w⟩ =ᵐ[volume] orderedDerivative w f := by
    intro j
    induction j with
    | zero =>
      intro hj w
      have hw : w = Fin.elim0 := by funext i; exact Fin.elim0 i
      rw [orderedDerivative_zero]
      have hv : planeValue U = U.toFunction.jet ⟨⟨0, Nat.lt_succ_of_le hj⟩, w⟩ := by
        funext x
        simp only [planeValue, planeJetOrder, Nat.zero_le, dite_true]
        rw [hw]
      rw [hv] at hu
      exact hu
    | succ j ih =>
      intro hj w
      let k : Fin K := ⟨j, by omega⟩
      let v := Fin.init w
      let i := w (Fin.last j)
      have hn : nextIndex2 k v i = ⟨⟨j + 1, Nat.lt_succ_of_le hj⟩, w⟩ := by
        simp [nextIndex2, nextIndex, k, v, i]
      have hp : U.toFunction.jet (lowerIndex2 k v) =ᵐ[volume] orderedDerivative v f :=
        ih (by omega) v
      have hs : ContDiff ℝ 2 (orderedDerivative v f) :=
        ChartTransport.contDiff_orderedDerivative v (hf.of_le (by simp))
      have hh : Continuous (orderedDerivative w f) := by
        rw [orderedDerivative_succ]
        exact (hs.continuous_fderiv (by norm_num)).clm_apply continuous_const
      rw [← hn]
      apply weakDerivative_unique_continuous
        (by simpa only [Measure.restrict_univ] using U.toFunction.memL2 (nextIndex2 k v i)) hh
        (u := orderedDerivative v f)
      · intro e
        apply hasWeakPartialDerivOn_congr_ae _ (Filter.Eventually.of_forall (fun _ => rfl))
          (U.toFunction.hasWeakJet k v i e)
        simpa only [Measure.restrict_univ, Function.comp_def] using hp.fun_comp (inner ℝ e)
      · intro e
        have he := smoothVector_weak_coordinate (hs.of_le (by norm_num)) i e
        rw [orderedDerivative_succ]
        rw [show (fun k : Fin j => w k.castSucc) = v by funext k; rfl]
        exact he
  have he : planeJetOrder U j w = U.toFunction.jet ⟨⟨j, Nat.lt_succ_of_le hj⟩, w⟩ := by
    funext x
    simp only [planeJetOrder, dite_eq_left hj]
  rw [he]
  exact hlevel j hj w

end AVRegularity.CycleWords
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleWords

/-! Clipping the genuine chart weight requires only cell ellipticity. -/

theorem cellMetric_chartWeights_clipped_operator_arithmetic
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {t₀ S ϖ : ℝ} {zc : Vec 2} {M : ℕ} {Cw : ℕ → ℝ}
    (W : ChartWeights G v t₀ S ϖ zc M Cw) (m : ℕ) (hm : m ≤ M)
    (t : ℝ) (ht : t ∈ Set.Icc t₀ (t₀ + S)) (z : Vec 2) (B : ℝ)
    (hB : 0 < B) (hCell : IsCellMetric G) :
    let grad : Fin 2 → ℝ := fun i => fderiv ℝ (W.W m t) z (basisVec i)
    let defectL : ℝ := deriv (fun s => W.W m s z) t +
      (∑ i : Fin 2, v t z i * grad i) +
      (∑ i : Fin 2, fderiv ℝ (fun z' =>
        ∑ j : Fin 2, G t z' i j * fderiv ℝ (W.W m t) z' (basisVec j)) z (basisVec i))
    let fluxDiv : ℝ := ∑ i : Fin 2,
      fderiv ℝ (fun z' => W.Phi m t z' i) z (basisVec i)
    let ellipticCross : ℝ := ∑ i : Fin 2, ∑ j : Fin 2,
      grad i * G t z i j * grad j
    let fluxCross : ℝ := ∑ i : Fin 2, grad i * W.Phi m t z i
    clipWeightDeriv B (W.W m t z) * defectL +
        clipWeightSecondDeriv B (W.W m t z) * ellipticCross ≤
      2 * W.lam m * clipWeight B (W.W m t z) +
        clipWeightDeriv B (W.W m t z) * fluxDiv +
        clipWeightSecondDeriv B (W.W m t z) * fluxCross := by
  dsimp
  let grad : Fin 2 → ℝ := fun i => fderiv ℝ (W.W m t) z (basisVec i)
  let defectL : ℝ := deriv (fun s => W.W m s z) t +
    (∑ i : Fin 2, v t z i * grad i) +
    (∑ i : Fin 2, fderiv ℝ (fun z' =>
      ∑ j : Fin 2, G t z' i j * fderiv ℝ (W.W m t) z' (basisVec j)) z (basisVec i))
  let fluxDiv : ℝ := ∑ i : Fin 2,
    fderiv ℝ (fun z' => W.Phi m t z' i) z (basisVec i)
  let ellipticCross : ℝ := ∑ i : Fin 2, ∑ j : Fin 2,
    grad i * G t z i j * grad j
  let fluxCross : ℝ := ∑ i : Fin 2, grad i * W.Phi m t z i
  have hpos := W.pos m hm t z
  have hlam := (W.lam_bound m hm).1
  have ha := clipWeightDeriv_nonneg hB hpos
  have hscale := clipWeight_scaled_deriv_le hB hpos
  have hscale' : clipWeightDeriv B (W.W m t z) * W.W m t z ≤
      clipWeight B (W.W m t z) := by nlinarith [hscale]
  have hbase : defectL ≤ W.lam m * W.W m t z + fluxDiv := by
    simpa [defectL, fluxDiv, grad] using W.defect m hm t ht z
  have hmetric := hCell.2.2.2 t z grad
  have hgradSq : 0 ≤ ∑ i : Fin 2, (grad i) ^ 2 := by positivity
  have helliptic : clipWeightSecondDeriv B (W.W m t z) * ellipticCross ≤ 0 := by
    have hq : 0 ≤ ellipticCross := by
      dsimp [ellipticCross]
      exact le_trans (by positivity : 0 ≤ (1 / 2 : ℝ) * ∑ i : Fin 2, (grad i) ^ 2)
        hmetric.1
    exact mul_nonpos_of_nonpos_of_nonneg
      (clipWeightSecondDeriv_nonpos hB hpos) hq
  have hcross := chartWeights_clipped_second_cross_bound W m hm t ht z B hB
  exact clippedOperator_defect_bound hlam ha hscale' hbase helliptic hcross

/-- Pointwise differential inequality for the actual bounded composition of a
chart weight. This is the rigorous form of the clipping step. -/
theorem cellMetric_chartWeights_clipped_defect
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {t₀ S ϖ : ℝ} {zc : Vec 2} {M : ℕ} {Cw : ℕ → ℝ}
    (W : ChartWeights G v t₀ S ϖ zc M Cw) (m : ℕ) (hm : m ≤ M)
    (t : ℝ) (ht : t ∈ Set.Icc t₀ (t₀ + S)) (z : Vec 2) (B : ℝ)
    (hB : 0 < B) (hCell : IsCellMetric G)
    (Kmax : ℕ)
    (hG_smooth : ∀ i j : Fin 2,
      ContDiff ℝ (max Kmax 1 : ℕ) (fun y => G t y i j)) :
    deriv (fun s => clipWeight B (W.W m s z)) t +
      (∑ i : Fin 2, v t z i *
        fderiv ℝ (fun y => clipWeight B (W.W m t y)) z (basisVec i)) +
      (∑ i : Fin 2, fderiv ℝ (fun y =>
        ∑ j : Fin 2, G t y i j *
          fderiv ℝ (fun y' => clipWeight B (W.W m t y')) y (basisVec j)) z (basisVec i)) ≤
      2 * W.lam m * clipWeight B (W.W m t z) +
        (∑ i : Fin 2, fderiv ℝ (fun y =>
          clipWeightDeriv B (W.W m t y) * W.Phi m t y i) z (basisVec i)) := by
  let w : Vec 2 → ℝ := fun y => W.W m t y
  let Gt : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ := fun y => G t y
  let grad : Fin 2 → ℝ := fun i => fderiv ℝ w z (basisVec i)
  let coeff : Vec 2 → ℝ := fun y => clipWeightDeriv B (W.W m t y)
  let fluxDiv : ℝ := ∑ i : Fin 2,
    fderiv ℝ (fun y => W.Phi m t y i) z (basisVec i)
  let fluxCross : ℝ := ∑ i : Fin 2, grad i * W.Phi m t z i
  let ellipticCross : ℝ := ∑ i : Fin 2, ∑ j : Fin 2,
    grad i * G t z i j * grad j
  have hpos := W.pos m hm t z
  have hWspace : ContDiff ℝ 2 w := by
    convert (W.smooth m hm).1.comp (contDiff_const.prodMk contDiff_id) using 1 <;> rfl
  have hWtime : ContDiff ℝ 2 (fun s : ℝ => W.W m s z) := by
    convert (W.smooth m hm).1.comp (contDiff_id.prodMk contDiff_const) using 1 <;> rfl
  have hwd : ∀ y, HasFDerivAt w (fderiv ℝ w y) y := by
    intro y
    exact (hWspace.differentiable (by norm_num) y).hasFDerivAt
  have hclipGrad (i : Fin 2) :
      fderiv ℝ (fun y => clipWeight B (w y)) z (basisVec i) =
        clipWeightDeriv B (w z) * grad i := by
    simpa [grad, w] using congrArg (fun L : Vec 2 →L[ℝ] ℝ => L (basisVec i))
      (clipWeight_comp_fderiv B hB (W.pos m hm t z) (hwd z))
  have htimeDeriv : HasDerivAt (fun s : ℝ => W.W m s z)
      (deriv (fun s => W.W m s z) t) t :=
    (hWtime.differentiable (by norm_num) t).hasDerivAt
  have htimeComp := (hasDerivAt_clipWeight hB hpos).comp t htimeDeriv
  have htimeEq : deriv (fun s => clipWeight B (W.W m s z)) t =
      clipWeightDeriv B (W.W m t z) * deriv (fun s => W.W m s z) t := by
    convert htimeComp.deriv using 1
    rfl
  have htransport :
      (∑ i : Fin 2, v t z i *
        fderiv ℝ (fun y => clipWeight B (w y)) z (basisVec i)) =
      clipWeightDeriv B (W.W m t z) *
        (∑ i : Fin 2, v t z i * grad i) := by
    calc
      _ = ∑ i : Fin 2, clipWeightDeriv B (W.W m t z) * (v t z i * grad i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hclipGrad i]
        ring
      _ = _ := by rw [Finset.mul_sum]
  have hgradCont (j : Fin 2) : ContDiff ℝ 1
      (fun y => fderiv ℝ w y (basisVec j)) := by
    have hWtwo : ContDiff ℝ ((1 + 1 : ℕ) : ℕ∞) w := by
      simpa using hWspace
    have hjoint := hWtwo.contDiff_fderiv_apply (m := 1) le_rfl
    simpa [Function.comp_def] using
      hjoint.comp (contDiff_id.prodMk contDiff_const)
  have hGorder : (1 : WithTop ℕ∞) ≤ ((max Kmax 1 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast (Nat.le_max_right Kmax 1)
  have hrowCont (i : Fin 2) : ContDiff ℝ 1 (weightFluxRow Gt w i) := by
    change ContDiff ℝ 1 (fun y =>
      ∑ j ∈ Finset.univ, G t y i j * fderiv ℝ w y (basisVec j))
    apply ContDiff.sum
    intro j hj
    exact (hG_smooth i j).of_le hGorder |>.mul (hgradCont j)
  have hfluxd (i : Fin 2) : HasFDerivAt (weightFluxRow Gt w i)
      (fderiv ℝ (weightFluxRow Gt w i) z) z :=
    (hrowCont i).differentiable (by norm_num) z |>.hasFDerivAt
  have hdiffusion :
      (∑ i : Fin 2, fderiv ℝ (fun y =>
        ∑ j : Fin 2, G t y i j *
          fderiv ℝ (fun y' => clipWeight B (w y')) y (basisVec j)) z (basisVec i)) =
      clipWeightDeriv B (W.W m t z) *
          (∑ i : Fin 2, fderiv ℝ (weightFluxRow Gt w i) z (basisVec i)) +
        clipWeightSecondDeriv B (W.W m t z) * ellipticCross := by
    have h := clippedWeightMetricDivergence_eq B hB Gt w z
      (fun y => W.pos m hm t y) hwd hfluxd
    have hq :
        (∑ i : Fin 2, fderiv ℝ w z (basisVec i) * weightFluxRow Gt w i z) =
          ellipticCross := by
      simp [weightFluxRow, ellipticCross, Gt, w, grad, Fin.sum_univ_two]
      ring
    change clippedWeightMetricDivergence B Gt w z = _
    rw [hq] at h
    exact h
  have hrowEq (i : Fin 2) : weightFluxRow Gt w i = fun y =>
      ∑ j : Fin 2, G t y i j * fderiv ℝ (W.W m t) y (basisVec j) := by
    funext y
    rfl
  have hdivOldEq :
      (∑ i : Fin 2, fderiv ℝ (weightFluxRow Gt w i) z (basisVec i)) =
        (∑ i : Fin 2, fderiv ℝ (fun y =>
          ∑ j : Fin 2, G t y i j * fderiv ℝ (W.W m t) y (basisVec j)) z (basisVec i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (fun f : Vec 2 → ℝ => fderiv ℝ f z (basisVec i)) (hrowEq i)
  have hdiffusionExpanded := hdiffusion
  rw [hdivOldEq] at hdiffusionExpanded
  have hphiVec : ContDiff ℝ 1 (fun y : Vec 2 => W.Phi m t y) := by
    convert (W.smooth m hm).2.comp (contDiff_const.prodMk contDiff_id) using 1 <;> rfl
  have hphiCont (i : Fin 2) : ContDiff ℝ 1 (fun y => W.Phi m t y i) :=
    (contDiff_apply ℝ ℝ i).comp hphiVec
  have hphiwd (i : Fin 2) : HasFDerivAt (fun y => W.Phi m t y i)
      (fderiv ℝ (fun y => W.Phi m t y i) z) z :=
    (hphiCont i).differentiable (by norm_num) z |>.hasFDerivAt
  have hcoeffd : HasFDerivAt coeff
      (clipWeightSecondDeriv B (W.W m t z) • fderiv ℝ w z) z := by
    simpa [coeff, w] using
      hasFDerivAt_clipWeightDeriv_comp B hB hpos (hwd z)
  have hfluxDiv :
      (∑ i : Fin 2, fderiv ℝ (fun y => coeff y * W.Phi m t y i) z (basisVec i)) =
      clipWeightDeriv B (W.W m t z) * fluxDiv +
        clipWeightSecondDeriv B (W.W m t z) * fluxCross := by
    calc
      _ = ∑ i : Fin 2,
          (clipWeightDeriv B (W.W m t z) *
            fderiv ℝ (fun y => W.Phi m t y i) z (basisVec i) +
           W.Phi m t z i *
            (clipWeightSecondDeriv B (W.W m t z) * grad i)) := by
        apply Finset.sum_congr rfl
        intro i _
        have hmul := hcoeffd.mul (hphiwd i)
        change fderiv ℝ (coeff * (fun y => W.Phi m t y i)) z (basisVec i) = _
        rw [hmul.fderiv]
        simp only [add_apply, smul_apply]
        ring
      _ = clipWeightDeriv B (W.W m t z) * fluxDiv +
          clipWeightSecondDeriv B (W.W m t z) * fluxCross := by
        dsimp [fluxDiv, fluxCross]
        rw [Finset.sum_add_distrib]
        have hfactor :
            (∑ i : Fin 2, W.Phi m t z i *
              (clipWeightSecondDeriv B (W.W m t z) * grad i)) =
            clipWeightSecondDeriv B (W.W m t z) *
              ∑ i : Fin 2, grad i * W.Phi m t z i := by
          calc
            _ = ∑ i : Fin 2, clipWeightSecondDeriv B (W.W m t z) *
                (grad i * W.Phi m t z i) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
            _ = _ := by rw [Finset.mul_sum]
        rw [← Finset.mul_sum, hfactor]
  have harith := cellMetric_chartWeights_clipped_operator_arithmetic W m hm t ht z B hB hCell
  have hleft :
      deriv (fun s => clipWeight B (W.W m s z)) t +
        (∑ i : Fin 2, v t z i *
          fderiv ℝ (fun y => clipWeight B (W.W m t y)) z (basisVec i)) +
        (∑ i : Fin 2, fderiv ℝ (fun y =>
          ∑ j : Fin 2, G t y i j *
            fderiv ℝ (fun y' => clipWeight B (W.W m t y')) y (basisVec j)) z (basisVec i)) =
      clipWeightDeriv B (W.W m t z) *
        (deriv (fun s => W.W m s z) t +
        (∑ i : Fin 2, v t z i * grad i) +
          (∑ i : Fin 2, fderiv ℝ (fun y =>
            ∑ j : Fin 2, G t y i j * fderiv ℝ (W.W m t) y (basisVec j)) z (basisVec i))) +
        clipWeightSecondDeriv B (W.W m t z) * ellipticCross := by
    rw [htimeEq, htransport, hdiffusionExpanded]
    ring
  have hright :
      2 * W.lam m * clipWeight B (W.W m t z) +
        (∑ i : Fin 2, fderiv ℝ (fun y => coeff y * W.Phi m t y i) z (basisVec i)) =
      2 * W.lam m * clipWeight B (W.W m t z) +
        clipWeightDeriv B (W.W m t z) * fluxDiv +
        clipWeightSecondDeriv B (W.W m t z) * fluxCross := by
    rw [hfluxDiv]
    ring
  calc
    _ = clipWeightDeriv B (W.W m t z) *
          (deriv (fun s => W.W m s z) t +
            (∑ i : Fin 2, v t z i * grad i) +
            (∑ i : Fin 2, fderiv ℝ (fun y =>
              ∑ j : Fin 2, G t y i j * fderiv ℝ (W.W m t) y (basisVec j)) z (basisVec i))) +
        clipWeightSecondDeriv B (W.W m t z) * ellipticCross := hleft
    _ ≤ 2 * W.lam m * clipWeight B (W.W m t z) +
        clipWeightDeriv B (W.W m t z) * fluxDiv +
        clipWeightSecondDeriv B (W.W m t z) * fluxCross := by
      simpa [grad, fluxDiv, fluxCross, ellipticCross, Gt, w] using harith
    _ = _ := hright.symm

end AVRegularity.CycleWords
end
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleWords

/-! Finite buffered block regions, with pulse slots that have no non-quiet time removed. The
quiet times are the trimmed quiet times. -/

def interiorBufferedBlockRegions (τ a b D : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (marks : Fin 2 → Finset ℝ) : BlockRegions :=
  { P := (interiorActivePulseIndices τ a b v).card
    lo := fun p => interiorBufferedPulseLo τ a D (interiorActivePulseRegionIndex τ a b v p)
    hi := fun p => interiorBufferedPulseHi τ b D (interiorActivePulseRegionIndex τ a b v p)
    orient := fun p => if (2 * interiorActivePulseRegionIndex τ a b v p + 1) % 4 = 3 then 0 else 1
    quiet := interiorTrimmedQuiet τ v
    marks := marks
    joins := 2 * (interiorActivePulseIndices τ a b v).card
    buffer := D }

theorem interiorBufferedBlockRegions_inside (τ a b D : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (marks : Fin 2 → Finset ℝ) :
    let reg := interiorBufferedBlockRegions τ a b D v marks
    ∀ p, Set.Icc (reg.lo p - reg.buffer) (reg.hi p + reg.buffer) ⊆ Set.Icc a b := by
  dsimp only
  intro p
  exact interiorBufferedPulse_inside τ a b D (interiorActivePulseRegionIndex τ a b v p)

theorem interiorBufferedBlockRegions_joins (τ a b D : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (marks : Fin 2 → Finset ℝ) :
    let reg := interiorBufferedBlockRegions τ a b D v marks
    2 * reg.P = reg.joins := rfl

theorem interiorBufferedBlockRegions_join_bound {τ a b : ℝ} (hτ : 0 < τ) (hab : a ≤ b)
    (D : ℝ) (v : ℝ → Vec 2 → Vec 2) (marks : Fin 2 → Finset ℝ) :
    ((interiorBufferedBlockRegions τ a b D v marks).joins : ℝ) ≤ (b - a) / τ + 4 := by
  simpa only [interiorBufferedBlockRegions, Nat.cast_mul, Nat.cast_ofNat] using
    interiorActivePulseIndices_join_bound hτ hab v

theorem interiorBufferedBlockRegions_nonempty (τ a b D : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (marks : Fin 2 → Finset ℝ)
    (hleft : Set.Ico a (a + D) ⊆ interiorTrimmedQuiet τ v)
    (hright : Set.Ioc (b - D) b ⊆ interiorTrimmedQuiet τ v) :
    let reg := interiorBufferedBlockRegions τ a b D v marks
    ∀ p, reg.lo p ≤ reg.hi p := by
  dsimp only
  intro p
  exact interiorActivePulseRegion_nonempty τ a b D v hleft hright
    (interiorActivePulseRegionIndex_mem τ a b v p)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.CoupledEnergyPlane.Fourier LineDeriv
open scoped FourierTransform SchwartzMap
namespace AVRegularity.CycleWords

/-! The genuine Fourier multiplier criterion for a plane L2 distributional derivative. -/

theorem planeFourier_distribution_derivative_of_ae
    (f g : Lp ℂ 2 (volume : Measure (Vec 2))) (i : Fin 2)
    (hfg : fourierL2 g =ᵐ[volume] fun ξ =>
      (2 * (Real.pi : ℂ) * Complex.I) * (ξ i : ℂ) * fourierL2 f ξ) :
    ∂_{coordinateVector i} ((coordinateL2Equiv f : Lp ℂ 2 volume) :
      𝓢'(HilbertTwo, ℂ)) = ((coordinateL2Equiv g : Lp ℂ 2 volume) : 𝓢'(HilbertTwo, ℂ)) := by
  have hm : coordinateL2Equiv (fourierL2 g) =ᵐ[volume] fun ξ : HilbertTwo =>
      (2 * (Real.pi : ℂ) * Complex.I) * (inner ℝ ξ (coordinateVector i) : ℂ) *
        coordinateL2Equiv (fourierL2 f) ξ := by
    have ht := (PiLp.volume_preserving_ofLp (Fin 2)).quasiMeasurePreserving.ae hfg
    filter_upwards [ht, coordinateL2Equiv_ae (fourierL2 g),
      coordinateL2Equiv_ae (fourierL2 f)] with ξ hξ hg hf
    rw [hg, hf, coordinateVector_inner]
    exact hξ
  have hh := lineDerivOp_fourierInv_L2 (coordinateL2Equiv (fourierL2 f))
    (coordinateL2Equiv (fourierL2 g)) (coordinateVector i) hm
  rwa [coordinate_fourierL2 f, coordinate_fourierL2 g,
    FourierTransform.fourierInv_fourier_eq, FourierTransform.fourierInv_fourier_eq] at hh

end AVRegularity.CycleWords
end
end
