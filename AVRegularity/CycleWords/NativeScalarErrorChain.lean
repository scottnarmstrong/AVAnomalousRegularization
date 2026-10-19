-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.GeometryActualFluxSplit
import AVRegularity.CycleWords.PlaneScalarBlochSurjective
import AVRegularity.CycleReference.CoreFlux
import AVRegularity.CycleEvolution.CellDriftSmoothEnergy
import AVRegularity.CycleReference.CorrectorMeanGeometry
import AVRegularity.CycleReference.SingleModeFlux
import AVRegularity.CycleReference.MeanEnhancementScale
import AVRegularity.Velocity.Port.MaterialGoalSource
import AVRegularity.CycleComparison.Residual.Jets.Lift
import AVRegularity.CycleComparison.Residual.QuietMean.FastIndep
public import AVRegularity.CycleWords.GeometryScalarCoefficient
public import Mathlib.Analysis.CStarAlgebra.lpSpace
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

@[expose] public noncomputable section

section
open Homogenization
namespace AVRegularity.CycleWords

/-! The actual quiet pulse annulus is unchanged by conversion to cell time. -/

theorem scaled_pulse_distance {L τ t k : ℝ} (hL : 0 < L) :
    |L * t - k * τ| = L * |t - k * (τ / L)| := by
  have he : L * t - k * τ = L * (t - k * (τ / L)) := by field_simp
  rw [he, abs_mul, abs_of_pos hL]

theorem scaled_pulse_annulus {L τ t k : ℝ} (hL : 0 < L)
    (hlo : 3 / 4 * (τ / L) ≤ |t - k * (τ / L)|)
    (hhi : |t - k * (τ / L)| ≤ τ / L) :
    3 / 4 * τ ≤ |L * t - k * τ| ∧ |L * t - k * τ| ≤ τ := by
  rw [scaled_pulse_distance hL]
  constructor
  · convert mul_le_mul_of_nonneg_left hlo hL.le using 1
    field_simp
  · convert mul_le_mul_of_nonneg_left hhi hL.le using 1
    field_simp

theorem interior_cell_quiet_annulus {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (y₀ : Vec 2)
    (hL : 0 < ocEll q Λ m ν ^ 2) (n : ℤ) {t : ℝ}
    (hlo : 3 / 4 * (ocTau α q Λ m / ocEll q Λ m ν ^ 2) ≤
      |t - (2 * (n : ℝ) + 1) * (ocTau α q Λ m / ocEll q Λ m ν ^ 2)|)
    (hhi : |t - (2 * (n : ℝ) + 1) * (ocTau α q Λ m / ocEll q Λ m ν ^ 2)| ≤
      ocTau α q Λ m / ocEll q Λ m ν ^ 2) (z : Vec 2) :
    ocCellDrift α q Λ ζ m ν y₀ t z = 0 := by
  obtain ⟨hl, hh⟩ := scaled_pulse_annulus hL hlo hhi
  apply ocCellDrift_zero_in_pulse_quiet_annulus hΛ hζ ν y₀
    (show Odd (2 * n + 1) from ⟨n, by ring⟩) _ _ z
  · simpa only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one] using hl
  · simpa only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_one] using hh

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! The genuine single-pulse extension agrees with the full drift on its enlarged pulse window. -/

def interiorSinglePulseDrift (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ)
    (m : ℕ) (ν : ℝ) (y₀ : Vec 2) (k : ℤ) : ℝ → Vec 2 → Vec 2 :=
  fun t z => (ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m) •
    (ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t) •
      ocShearVel α q Λ m k (y₀ + ocEpsilon q Λ m • z))

theorem ocCellDrift_nonzero_has_active_pulse {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (ν t : ℝ) (y₀ z : Vec 2)
    (h : ocCellDrift α q Λ ζ m ν y₀ t z ≠ 0) :
    ∃ k : ℤ, Odd k ∧ ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t) ≠ 0 := by
  by_contra hn
  push Not at hn
  apply h
  simp only [ocCellDrift, CycleReference.pulseStreamVel_eq_zero_of_quiet hn, smul_zero]

theorem interiorSinglePulseDrift_agrees {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (y₀ : Vec 2)
    {k : ℤ} (hk : Odd k) {t : ℝ}
    (ht : |ocEll q Λ m ν ^ 2 * t - (k : ℝ) * ocTau α q Λ m| ≤
      3 / 4 * ocTau α q Λ m) (z : Vec 2) :
    interiorSinglePulseDrift α q Λ ζ m ν y₀ k t z =
      ocCellDrift α q Λ ζ m ν y₀ t z := by
  classical
  by_cases hp : ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t) = 0
  · have hz : ∀ j : ℤ, Odd j → ocPulse α q Λ ζ m j (ocEll q Λ m ν ^ 2 * t) = 0 := by
      intro j hj
      by_cases he : j = k
      · simpa only [he] using hp
      · exact pulse_other_zero_on_enlarged hΛ hζ hk hj he ht
    simp only [interiorSinglePulseDrift, ocCellDrift, hp, zero_smul, smul_zero,
      CycleReference.pulseStreamVel_eq_zero_of_quiet hz]
  · simp only [interiorSinglePulseDrift, ocCellDrift,
      CycleReference.pulseStreamVel_eq_active hΛ hζ hk hp]

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance Filter Topology
namespace AVRegularity.CycleWords

/-! Smoothness of the literal cell drift follows from the locally finite pulse sum. -/

theorem pulseVelocity_component_joint_contDiff {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 => streamVel (ocPulseStream α q Λ ζ m) p.1 p.2 j) := by
  classical
  apply contDiff_iff_contDiffAt.mpr
  intro p
  obtain ⟨S, hS⟩ := CycleReference.cutoff_locally_finite
    (α := α) (q := q) (m := m) hΛ p.1
  let f := fun r : ℝ × Vec 2 =>
    ∑ k ∈ S, ocPulse α q Λ ζ m k.1 r.1 * ocShearVel α q Λ m k.1 r.2 j
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := by
    apply ContDiff.sum
    intro k _
    exact ((CycleReference.ocPulse_contDiff hζ k.1).comp contDiff_fst).mul
      ((ocShearVel_component_contDiff (α := α) (q := q) (Λ := Λ) (m := m) k.2 j).comp contDiff_snd)
  have he : (fun r : ℝ × Vec 2 => streamVel (ocPulseStream α q Λ ζ m) r.1 r.2 j)
      =ᶠ[𝓝 p] f := by
    filter_upwards [continuous_fst.continuousAt.eventually hS] with r hr
    rw [pulseVelocity_eq_shear_sum hΛ hζ]
    apply tsum_eq_sum
    intro k hk
    have hz : ocPulse α q Λ ζ m k.1 r.1 = 0 := by
      by_contra hn
      have h1 := CycleReference.ocCutoff_eq_one_of_pulse_ne_zero hΛ hζ hn
      rw [hr k hk] at h1
      exact zero_ne_one h1
    rw [hz, zero_mul]
  exact hf.contDiffAt.congr_of_eventuallyEq he

theorem cellDrift_joint_contDiff {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (yc : Vec 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => ocCellDrift α q Λ ζ m ν yc p.1 p.2) := by
  apply contDiff_pi.mpr
  intro j
  have ha : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 =>
      (ocEll q Λ m ν ^ 2 * p.1, yc + ocEpsilon q Λ m • p.2)) := by fun_prop
  have hh := (pulseVelocity_component_joint_contDiff (α := α) (q := q) (m := m) hΛ hζ j).comp ha
  simpa only [ocCellDrift, Pi.smul_apply, smul_eq_mul, Function.comp_def] using
    contDiff_const.mul hh

theorem cellDrift_spatial_contDiff {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν t : ℝ) (yc : Vec 2) :
    ContDiff ℝ (⊤ : ℕ∞) (ocCellDrift α q Λ ζ m ν yc t) := by
  have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec 2 => (t, z)) :=
    contDiff_const.prodMk contDiff_id
  have hh := (cellDrift_joint_contDiff (α := α) (q := q) (m := m) hΛ hζ ν yc).comp hmap
  simpa only [Function.comp_def] using hh

end AVRegularity.CycleWords
end

section
open MeasureTheory AVRegularity.CycleEvolution
open scoped ENNReal NNReal BigOperators
namespace AVRegularity.CycleWords

/-! Analytic bounded-time series and their actual integrals on integrable slices. -/

def fibreBoundedTimeSeries (a : ℕ × ℕ → ℝ → ℂ)
    (R : ℝ≥0) (hR : 0 < R)
    (ha : (∑' p, fibreCoefficientWeight (R : ENNReal) p * ⨆ t, ‖a p t‖ₑ) < ⊤)
    (ξ : Fin 2 → ℂ) : BoundedComplexTime :=
  ∑' p, fibreMonomial ξ p • fibreBoundedTimeCoefficient a R hR ha p

theorem fibreBoundedTimeSeries_apply (a : ℕ × ℕ → ℝ → ℂ)
    (R : ℝ≥0) (hR : 0 < R)
    (ha : (∑' p, fibreCoefficientWeight (R : ENNReal) p * ⨆ t, ‖a p t‖ₑ) < ⊤)
    (ξ : Fin 2 → ℂ) (hξ : ‖ξ‖ ≤ R) (t : ℝ) :
    fibreBoundedTimeSeries a R hR ha ξ t = fibreSeriesC a ξ t := by
  have hs := fibreBivariateSum_summable (fibreBoundedTimeCoefficient a R hR ha) R
    (fibreBoundedTimeCoefficient_weighted_summable a R hR ha) ξ hξ
  have he := (lp.evalCLM ℂ (fun _ : ℝ => ℂ) ⊤ t).map_tsum hs
  exact he

theorem fibreBoundedTimeSeries_analyticOnNhd (a : ℕ × ℕ → ℝ → ℂ)
    (R : ℝ≥0) (hR : 0 < R)
    (ha : (∑' p, fibreCoefficientWeight (R : ENNReal) p * ⨆ t, ‖a p t‖ₑ) < ⊤) :
    AnalyticOnNhd ℂ (fibreBoundedTimeSeries a R hR ha) (Metric.ball 0 (R : ℝ)) :=
  fibreBivariateSum_analyticOnNhd (fibreBoundedTimeCoefficient a R hR ha) R hR
    (fibreBoundedTimeCoefficient_weighted_summable a R hR ha)

def fibreBoundedTimeIntegratedSeries (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a : ℕ × ℕ → ℝ → ℂ) (R : ℝ≥0) (hR : 0 < R)
    (ha : (∑' p, fibreCoefficientWeight (R : ENNReal) p * ⨆ t, ‖a p t‖ₑ) < ⊤)
    (ξ : Fin 2 → ℂ) : ℂ :=
  boundedTimeIntegralExtension μ (fibreBoundedTimeSeries a R hR ha ξ)

theorem fibreBoundedTimeIntegratedSeries_eq_integral (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a : ℕ × ℕ → ℝ → ℂ) (R : ℝ≥0) (hR : 0 < R)
    (ha : (∑' p, fibreCoefficientWeight (R : ENNReal) p * ⨆ t, ‖a p t‖ₑ) < ⊤)
    (ξ : Fin 2 → ℂ) (hξ : ‖ξ‖ ≤ R) (hi : Integrable (fibreSeriesC a ξ) μ) :
    fibreBoundedTimeIntegratedSeries μ a R hR ha ξ = ∫ t, fibreSeriesC a ξ t ∂μ := by
  have he : (fun t => fibreBoundedTimeSeries a R hR ha ξ t) = fibreSeriesC a ξ :=
    funext (fibreBoundedTimeSeries_apply a R hR ha ξ hξ)
  rw [fibreBoundedTimeIntegratedSeries, boundedTimeIntegralExtension_apply μ _ (he.symm ▸ hi), he]

theorem fibreBoundedTimeIntegratedSeries_analyticOnNhd (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a : ℕ × ℕ → ℝ → ℂ) (R : ℝ≥0) (hR : 0 < R)
    (ha : (∑' p, fibreCoefficientWeight (R : ENNReal) p * ⨆ t, ‖a p t‖ₑ) < ⊤) :
    AnalyticOnNhd ℂ (fibreBoundedTimeIntegratedSeries μ a R hR ha)
      (Metric.ball 0 (R : ℝ)) := by
  intro ξ hξ
  exact ((boundedTimeIntegralExtension μ).analyticAt _).comp
    (fibreBoundedTimeSeries_analyticOnNhd a R hR ha ξ hξ)

end AVRegularity.CycleWords
end

section
open Homogenization
namespace AVRegularity.CycleWords

/-! The extension has exactly the orientation dictated by the odd slot modulo four. -/

theorem interiorSinglePulseDrift_shear (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ)
    (m : ℕ) (ν : ℝ) (y₀ : Vec 2) {k : ℤ} (hk : Odd k) :
    ∃ V : ℝ → ℝ → ℝ, ∀ t z,
      interiorSinglePulseDrift α q Λ ζ m ν y₀ k t z =
        V t (z (if k % 4 = 3 then (0 : Fin 2) else 1).rev) •
          basisVec (if k % 4 = 3 then (0 : Fin 2) else 1) := by
  rcases CycleReference.odd_int_mod_four hk with h1 | h3
  · have hnot : ¬ k % 4 = 3 := by omega
    refine ⟨fun t x => (ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m) *
      (ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t) *
        ((2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) * (ocEpsilon q Λ m)⁻¹) *
          Real.cos (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * (y₀ 0 + ocEpsilon q Λ m * x)))), ?_⟩
    intro t z
    ext i
    fin_cases i <;> simp [interiorSinglePulseDrift, CycleReference.ocShearVel_horizontal h1,
      hnot, basisVec_apply, Fin.rev]
  · refine ⟨fun t x => (ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m) *
      (ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t) *
        (-(2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) * (ocEpsilon q Λ m)⁻¹) *
          Real.cos (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * (y₀ 1 + ocEpsilon q Λ m * x)))), ?_⟩
    intro t z
    ext i
    fin_cases i <;> simp [interiorSinglePulseDrift, CycleReference.ocShearVel_vertical h3,
      h3, basisVec_apply, Fin.rev]

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance
open AVRegularity.Velocity.Port.Section2FlowIdentities
open scoped NNReal
namespace AVRegularity.CycleWords

/-! Componentwise Jacobian budgets imply a global inverse-chart Lipschitz constant. -/

theorem fderiv_norm_le_jacMatrix_entries (F : Vec 2 → Vec 2) (x : Vec 2)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ i j, |jacMatrix F x i j| ≤ B) :
    ‖fderiv ℝ F x‖ ≤ 2 * B := by
  apply ContinuousLinearMap.opNorm_le_bound (fderiv ℝ F x) (by positivity)
  intro z
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [linearMap_apply_two]
  change |jacMatrix F x i 0 * z 0 + jacMatrix F x i 1 * z 1| ≤ _
  rw [mul_comm (jacMatrix F x i 0), mul_comm (jacMatrix F x i 1)]
  calc
    _ ≤ |z 0 * jacMatrix F x i 0| + |z 1 * jacMatrix F x i 1| := abs_add_le _ _
    _ = |z 0| * |jacMatrix F x i 0| + |z 1| * |jacMatrix F x i 1| := by rw [abs_mul, abs_mul]
    _ ≤ ‖z‖ * B + ‖z‖ * B := by
      apply add_le_add
      · exact mul_le_mul (norm_le_pi_norm z 0) (hb i 0) (abs_nonneg _) (norm_nonneg _)
      · exact mul_le_mul (norm_le_pi_norm z 1) (hb i 1) (abs_nonneg _) (norm_nonneg _)
    _ = _ := by ring

theorem jacobian_bar_lipschitz {F : Vec 2 → Vec 2}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) {R B : ℝ} (hR : 0 < R) (hB : 0 ≤ B)
    (hb : ∀ n i a, barNorm n R
      (fun x => jacMatrix F x i a - (1 : Matrix (Fin 2) (Fin 2) ℝ) i a) ≤ ENNReal.ofReal B) :
    LipschitzWith ⟨2 * (B + 1), by positivity⟩ F := by
  apply lipschitzWith_of_nnnorm_fderiv_le (hF.differentiable (by simp))
  intro x
  apply fderiv_norm_le_jacMatrix_entries F x (B + 1) (by positivity)
  intro i j
  have hh := CycleReference.jacMatrix_displacement_entry_bound hF hR hB hb x i j
  calc
    |jacMatrix F x i j| = |(jacMatrix F x i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j) +
        (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| := by rw [sub_add_cancel]
    _ ≤ |jacMatrix F x i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| +
        |(1 : Matrix (Fin 2) (Fin 2) ℝ) i j| := abs_add_le _ _
    _ ≤ B + 1 := add_le_add hh (by simp only [Matrix.one_apply]; split_ifs <;> norm_num)

end AVRegularity.CycleWords
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Finite slow regularity of a time integral from measurable sections and bounded jets. -/

theorem orderedDerivative_one_literal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : DerivativeWord2 1) (f : Vec 2 → E) :
    orderedDerivative α f = fun X => fderiv ℝ f X (basisVec (α 0)) := by
  simp [orderedDerivative, List.ofFn_succ]

open AVRegularity.CycleComparison.Lift
variable {T : Type*} [MeasurableSpace T]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [CompleteSpace E] in
theorem parameter_integral_continuous_growth (μ : Measure T) [IsFiniteMeasure μ]
    (f : T → Vec 2 → E) (hm : ∀ x, Measurable (fun t => f t x))
    (hc : ∀ t, Continuous (f t)) (C : ℝ) (hC : 0 ≤ C) (p : ℕ)
    (hb : ∀ t x, ‖f t x‖ ≤ C * (1 + ‖x‖) ^ p) :
    Continuous (fun x => ∫ t, f t x ∂μ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply continuousAt_of_dominated (bound := fun _ => C * (2 + ‖x‖) ^ p)
  · exact Filter.Eventually.of_forall (fun y => (hm y).aestronglyMeasurable)
  · filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1)] with y hy
    apply ae_of_all
    intro t
    have hn : ‖y‖ ≤ 1 + ‖x‖ := by
      have hd : ‖y - x‖ ≤ 1 := by simpa only [dist_eq_norm] using (Metric.mem_ball.mp hy).le
      calc
        ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by simpa only [sub_add_cancel] using norm_add_le (y - x) x
        _ ≤ _ := add_le_add hd le_rfl
    exact (hb t y).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith : 1 + ‖y‖ ≤ 2 + ‖x‖) p) hC)
  · exact integrable_const _
  · exact ae_of_all μ (fun t => (hc t).continuousAt)

omit [CompleteSpace E] in
theorem parameter_integral_contDiff_growth (μ : Measure T) [IsFiniteMeasure μ]
    (n : ℕ) (f : T → Vec 2 → E)
    (hm : ∀ x, Measurable (fun t => f t x))
    (hs : ∀ t, ContDiff ℝ (n : ℕ∞) (f t))
    (C : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j) (p : ℕ) (hb : ∀ j ≤ n, ∀ t x, ‖iteratedFDeriv ℝ j (f t) x‖ ≤ C j * (1 + ‖x‖) ^ p) :
    ContDiff ℝ (n : ℕ∞) (fun x => ∫ t, f t x ∂μ) := by
  induction n generalizing f C with
  | zero =>
    apply contDiff_zero.mpr
    apply parameter_integral_continuous_growth μ f hm (fun t => (hs t).continuous) (C 0) (hC 0) p
    intro t x
    simpa using hb 0 (by omega) t x
  | succ n ih =>
    have hd : ∀ t, Differentiable ℝ (f t) :=
      fun t => (hs t).differentiable (by simp)
    have hb₀ : ∀ t x, ‖f t x‖ ≤ C 0 * (1 + ‖x‖) ^ p := by
      intro t x
      simpa using hb 0 (by omega) t x
    have hb₁ : ∀ t x, ‖fderiv ℝ (f t) x‖ ≤ C 1 * (1 + ‖x‖) ^ p := by
      intro t x
      simpa only [norm_iteratedFDeriv_one] using hb 1 (by omega) t x
    have hder := parameter_integral_hasFDerivAt_growth μ f hm hd (C 0) (C 1) (hC 1) p hb₀ hb₁
    have hcoord : ∀ q : Fin 2, ContDiff ℝ (n : ℕ∞)
        (fun x => ∫ t, fderiv ℝ (f t) x (basisVec q) ∂μ) := by
      intro q
      let α : DerivativeWord2 1 := fun _ => q
      have he : ∀ t, (fun x => fderiv ℝ (f t) x (basisVec q)) =
          orderedDerivative α (f t) := by
        intro t
        funext x
        simp [α, orderedDerivative_one_literal]
      refine ih (fun t x => fderiv ℝ (f t) x (basisVec q))
        (fun x => fderiv_apply_parameter_measurable f hm hd x (basisVec q))
        ?_ (fun j => C (j + 1)) (fun j => hC (j + 1)) ?_
      · intro t
        rw [he t]
        exact contDiff_orderedDerivative α (hs t)
      · intro j hj t x
        rw [he t]
        exact (norm_iteratedFDeriv_orderedDerivative_le α
          ((hs t).of_le (by exact_mod_cast Nat.add_le_add_right hj 1)) x).trans
          (hb (j + 1) (by omega) t x)
    have hcast : (((n + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) =
        (n : WithTop ℕ∞) + 1 := by simp
    rw [hcast]
    apply (contDiff_succ_iff_fderiv_apply (n := (n : WithTop ℕ∞))).mpr
    refine ⟨fun x => (hder x).differentiableAt, ?_, ?_⟩
    · simp
    · intro y
      have he : (fun x => fderiv ℝ (fun x => ∫ t, f t x ∂μ) x y) =
          fun x => ∑ q : Fin 2, y q • (∫ t, fderiv ℝ (f t) x (basisVec q) ∂μ) := by
        funext x
        rw [(hder x).fderiv]
        have hi : Integrable (fun t => fderiv ℝ (f t) x) μ :=
          (integrable_const (C 1 * (1 + ‖x‖) ^ p)).mono'
            (fderiv_parameter_stronglyMeasurable f hm hd x).aestronglyMeasurable
            (MeasureTheory.ae_of_all μ (fun t => hb₁ t x))
        conv_lhs => arg 2; rw [vec_eq_sum_basis y]
        simp only [map_sum, map_smul]
        congr 1
        funext q
        rw [ContinuousLinearMap.integral_apply hi]
      rw [he]
      exact ContDiff.sum (fun q _ => (hcoord q).const_smul (y q))

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance Filter Topology
namespace AVRegularity.CycleWords

/-! The actual locally finite adjoint coordinate sum on the spatial lift. -/

def adjointCoordinate (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ)
    (ν t : ℝ) (y : Vec 2) (j : Fin 2) : ℝ :=
  y j + ∑' k : {k : ℤ // Odd k},
    ocCutoff α q Λ m k.1 t * adjointPulseMemory α q Λ ζ m ν k.1 t *
      ocShearVel α q Λ m k.1 y j

theorem adjointCoordinate_locally_finite {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (ν t : ℝ) :
    ∃ S : Finset {k : ℤ // Odd k}, ∀ᶠ s in 𝓝 t, ∀ y j,
      adjointCoordinate α q Λ ζ m ν s y j = y j +
        ∑ k ∈ S, ocCutoff α q Λ m k.1 s * adjointPulseMemory α q Λ ζ m ν k.1 s *
          ocShearVel α q Λ m k.1 y j := by
  classical
  obtain ⟨S, hS⟩ := CycleReference.cutoff_locally_finite hΛ t
  refine ⟨S, hS.mono ?_⟩
  intro s hs y j
  unfold adjointCoordinate
  congr 1
  apply tsum_eq_sum
  intro k hk
  rw [hs k hk, zero_mul, zero_mul]

theorem adjointCoordinate_joint_contDiff {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (j : Fin 2) (n : ℕ) :
    ContDiff ℝ n (fun p : ℝ × Vec 2 => adjointCoordinate α q Λ ζ m ν p.1 p.2 j) := by
  classical
  apply contDiff_iff_contDiffAt.mpr
  intro p
  obtain ⟨S, hS⟩ := adjointCoordinate_locally_finite (α := α) (q := q) (m := m) (ζ := ζ) hΛ ν p.1
  let f := fun p : ℝ × Vec 2 => p.2 j +
    ∑ k ∈ S, ocCutoff α q Λ m k.1 p.1 * adjointPulseMemory α q Λ ζ m ν k.1 p.1 *
      ocShearVel α q Λ m k.1 p.2 j
  have hf : ContDiff ℝ n f := by
    apply ContDiff.add (by fun_prop)
    apply ContDiff.sum
    intro k _
    exact (((CycleReference.ocCutoff_contDiff hΛ k.1).of_le (by simp)).comp contDiff_fst).mul
      ((adjointPulseMemory_contDiff hΛ hζ ν k.1 n).comp contDiff_fst) |>.mul
        (((ocShearVel_component_contDiff (α := α) (q := q) (Λ := Λ) (m := m) k.2 j).of_le
          (by simp)).comp contDiff_snd)
  have he : (fun p : ℝ × Vec 2 => adjointCoordinate α q Λ ζ m ν p.1 p.2 j)
      =ᶠ[𝓝 p] f := by
    exact (continuous_fst.continuousAt.eventually hS).mono (fun q hq => hq q.2 j)
  exact hf.contDiffAt.congr_of_eventuallyEq he

end AVRegularity.CycleWords
end

section
open Homogenization
namespace AVRegularity.CycleWords

/-! Classical regularity of the literal coordinate along time and space slices. -/

theorem adjointCoordinate_space_contDiff {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν t : ℝ) (j : Fin 2) (n : ℕ) :
    ContDiff ℝ n (fun y => adjointCoordinate α q Λ ζ m ν t y j) := by
  exact (adjointCoordinate_joint_contDiff hΛ hζ ν j n).comp
    (contDiff_const.prodMk contDiff_id)

theorem adjointCoordinate_time_contDiff {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (y : Vec 2) (j : Fin 2) (n : ℕ) :
    ContDiff ℝ n (fun t => adjointCoordinate α q Λ ζ m ν t y j) := by
  exact (adjointCoordinate_joint_contDiff hΛ hζ ν j n).comp
    (contDiff_id.prodMk contDiff_const)

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Scalar chain packaging of a native finite error and its weak equation. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]
  {L : Type*} [Fintype L]

theorem nativeScalarError_chain (D K : ℕ) (a b : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (f : PlaneHk Set.univ K E) (fz : L → PlaneHk Set.univ K E)
    (U : ℝ → PlaneHk Set.univ K E) (Z : L → ℝ → PlaneHk Set.univ K E)
    (Uw : ℝ → PlaneHk Set.univ (K + 1) E) (Zw : L → ℝ → PlaneHk Set.univ (K + 1) E)
    (V : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (hk : ContinuousOn (nativeErrorCurve U Z) (Set.Icc a b) ∧
      MemLp (nativeErrorCurve Uw Zw) 2 (volume.restrict (Set.Icc a b)) ∧
      (∀ᵐ t ∂volume.restrict (Set.Icc a b),
        truncatePlaneHk (Nat.le_succ K) (nativeErrorCurve Uw Zw t) = nativeErrorCurve U Z t) ∧
      nativeErrorCurve U Z a = nativeErrorDatum f fz)
    (hw : ∀ t ∈ Set.Icc a b, ∀ ψ : PlaneHk Set.univ 1 E,
      CoupledWeakIdentity volume 1 a t v
        ((nativeErrorCurve U Z t).toFunction.jet (valueIndex2 K))
        ((nativeErrorDatum f fz).toFunction.jet (valueIndex2 K))
        (ψ.toFunction.jet (valueIndex2 1))
        (fun k => ψ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩)
        (fun r k => (nativeErrorCurve Uw Zw r).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩)
        (fun r => geometryScalarFlux (h := fun _ : Unit => E) D G (fun (_ : Fin 1) (_ : Unit) => K)
          (fun _ => nativeErrorCurve Uw Zw r) (0, ()) r)
        (fun r => (V r).toFunction.jet (valueIndex2 K))
        (fun _ => (0 : PlaneHk Set.univ K E).toFunction.jet (valueIndex2 K))) :
    IsPlaneChainFrom (ι := Unit) (h := fun _ => E) (geometryScalarData D G)
      (fun _ _ => K) a b v (fun _ _ => nativeErrorDatum f fz) (fun _ _ => V)
      (fun _ _ => nativeErrorCurve U Z) (fun _ _ => nativeErrorCurve Uw Zw) := by
  refine ⟨fun _ => hk.1, fun _ => hk.2.1, fun _ => hk.2.2.1, fun _ => hk.2.2.2, ?_⟩
  intro i t ht ψ
  rcases i with ⟨j, u⟩
  have hj := Fin.eq_zero j
  subst j
  cases u
  simp only [Measure.restrict_univ]
  change CoupledWeakIdentity volume 1 a t v _ _ _ _ _
    (fun r => geometryScalarFlux (h := fun _ : Unit => E) D G (fun _ _ => K)
      (fun _ => nativeErrorCurve Uw Zw r) (0, ()) r) _ _
  exact hw t ht ψ

end AVRegularity.CycleWords
end
