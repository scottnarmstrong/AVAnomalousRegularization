-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleJoint.WeightedGradientLiftComparison
import AVRegularity.CycleJoint.ScalarWeightedJetSumMemL2
public import AVRegularity.CycleWords.CellMetricStoredWordResidualTimeIntegrability
import AVRegularity.CycleJoint.ReferencePhysicalSpatialSmooth
public import AVRegularity.CycleJoint.PlaneScalarWeightedEnergyHomogeneity
import AVRegularity.CycleWords.PlaneScalarBlochSurjective
import Mathlib.Algebra.Order.Star.Real

section
section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Finite actual geometry energy places every trajectory value in the radial periodization domain. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Every actual retained trajectory value has the genuine radial L² moments used by periodization. -/
theorem finite_geometry_trajectory_radial_moments (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (K : ι → ℕ) (ϖ : ℝ) (hϖ : 0 < ϖ) (z : Vec 2) (ρ a b : ℝ) (hρ : 0 < ρ)
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (he : geometryEnergyNorm π K 4 ϖ z ρ a b u w < ⊤)
    (i : ι) (t : ℝ) (ht : t ∈ Set.Icc a b) : HasRadialPlaneMoments (u i t) z := by
  obtain ⟨C, _, hb, _⟩ := finite_geometry_energy_component π hπ K 4 ϖ z ρ a b u w he i
  exact hasRadialPlaneMoments_of_finite_polynomial (u i t) ϖ hϖ z ρ hρ
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hb t ht))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Finite integrated public energy produces the actual weighted component L2 time curves. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem polynomialMomentLpReadout_time_memLp (ϖ : ℝ) (z : Vec 2) (ρ : ℝ) (hρ : 0 < ρ)
    (μ : Measure ℝ) (f : ℝ → PlaneHk Set.univ K E) (hf : MemLp f 2 μ)
    (he : (∫⁻ t, weightedFactorialNormSq 4 ϖ z ρ K (f t) ∂μ) ≠ ⊤) (a : JetIndex2 K) :
    MemLp (fun t => weightedPlaneLpReadout (planeMomentSquareRoot 4 ϖ z)
      (planeMomentSquareRoot_continuous 4 ϖ z) (planeJetReadoutOperator K a (f t))) 2 μ := by
  have hs : (fun y => planeMomentSquareRoot 4 ϖ z y ^ 2) = planeMomentPolynomial 4 ϖ z :=
    funext (planeMomentSquareRoot_sq 4 ϖ z)
  have hc : (∫⁻ t, chartScalarEnergy (planeMomentPolynomial 4 ϖ z)
      (planeJetReadoutOperator K a (f t)) ∂μ) ≠ ⊤ := by
    simp only [weightedFactorialNormSq_stored_readout, storedChartFactorialEnergy] at he
    exact finite_integrated_weighted_sum_component μ
      (fun a : JetIndex2 K => factorialWeight ρ a.1.val)
      (fun a => factorialWeight_pos_of_radius_pos ρ hρ a.1.val) _ he a
  have hr : MemLp (fun t => planeJetReadoutOperator (E := E) K a (f t)) 2 μ :=
    (planeJetReadoutOperator (E := E) K a).comp_memLp' hf
  have hcs : (∫⁻ t, chartScalarEnergy (fun y => planeMomentSquareRoot 4 ϖ z y ^ 2)
      (planeJetReadoutOperator K a (f t)) ∂μ) ≠ ⊤ := by
    simpa only [hs] using hc
  exact weightedPlaneLpReadout_time_memLp (E := E) (planeMomentSquareRoot 4 ϖ z)
    (planeMomentSquareRoot_continuous 4 ϖ z) (planeMomentSquareRoot_pos 4 ϖ z) μ
    (fun t => planeJetReadoutOperator (E := E) K a (f t)) hr hcs

theorem polynomialMoment_energy_ae_finite (ϖ : ℝ) (z : Vec 2) (ρ : ℝ)
    (μ : Measure ℝ) (f : ℝ → PlaneHk Set.univ K E) (hf : MemLp f 2 μ)
    (he : (∫⁻ t, weightedFactorialNormSq 4 ϖ z ρ K (f t) ∂μ) ≠ ⊤) :
    ∀ᵐ t ∂μ, weightedFactorialNormSq 4 ϖ z ρ K (f t) ≠ ⊤ :=
  (ae_lt_top' (weightedFactorialNormSq_time_aemeasurable 4 ϖ z ρ μ f hf) he).mono
    (fun _ ht => ht.ne)
end

/-! A finite dimension-independent radius price controls every periodized component moment. -/

section
def polynomialPeriodizationMomentBudget (K : ℕ) (ϖ ρ C : ℝ) : ℝ :=
  (Real.sqrt (2 + 4 / ϖ ^ 2)) ^ 4 *
    ∑ a : JetIndex2 K, Real.sqrt (C / factorialWeight ρ a.1.val)

theorem polynomialPeriodizationMomentBudget_nonneg (K : ℕ) (ϖ ρ C : ℝ) :
    0 ≤ polynomialPeriodizationMomentBudget K ϖ ρ C :=
  mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem polynomial_energy_radial_component_budget (f : PlaneHk Set.univ K E)
    (ϖ : ℝ) (hϖ : 0 < ϖ) (z : Vec 2) (ρ : ℝ) (hρ : 0 < ρ)
    (C : ℝ) (hC : 0 ≤ C)
    (he : weightedFactorialNormSq 4 ϖ z ρ K f ≤ ENNReal.ofReal C) (a : JetIndex2 K) :
    eLpNorm (fun y => (1 + ‖y - z‖) ^ 4 • f.toFunction.jet a y) 2 volume ≤
      ENNReal.ofReal (polynomialPeriodizationMomentBudget K ϖ ρ C) := by
  have hs : Real.sqrt (C / factorialWeight ρ a.1.val) ≤
      ∑ b : JetIndex2 K, Real.sqrt (C / factorialWeight ρ b.1.val) :=
    Finset.single_le_sum (f := fun b : JetIndex2 K => Real.sqrt (C / factorialWeight ρ b.1.val))
      (fun _ _ => Real.sqrt_nonneg _) (Finset.mem_univ a)
  calc
    _ ≤ ENNReal.ofReal ((Real.sqrt (2 + 4 / ϖ ^ 2)) ^ 4) *
        eLpNorm (fun y => planeMomentSquareRoot 4 ϖ z y • f.toFunction.jet a y) 2 volume :=
      radialMoment_eLpNorm_le_polynomial ϖ hϖ z _
        (by simpa only [Measure.restrict_univ] using (f.toFunction.memL2 a).aestronglyMeasurable)
    _ ≤ ENNReal.ofReal ((Real.sqrt (2 + 4 / ϖ ^ 2)) ^ 4) *
        ENNReal.ofReal (Real.sqrt (C / factorialWeight ρ a.1.val)) :=
      mul_le_mul' le_rfl (polynomialMoment_component_eLpNorm_le f ϖ z ρ hρ C hC he a)
    _ ≤ _ := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hs (by positivity))
end

/-! The public integrated polynomial energy supplies the common radial image price for all jets. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem exists_polynomialCarrier_radial_time_budget
    (ϖ : ℝ) (hϖ : 0 < ϖ) (z : Vec 2) (ρ : ℝ) (hρ : 0 < ρ)
    (μ : Measure ℝ) (f : ℝ → PlaneHk Set.univ K E) (hf : MemLp f 2 μ)
    (he : (∫⁻ t, weightedFactorialNormSq 4 ϖ z ρ K (f t) ∂μ) ≠ ⊤) :
    ∃ M : ℝ → ℝ, MemLp M 2 μ ∧
      (∀ a, ∀ᵐ t ∂μ, AEStronglyMeasurable
        (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet a y) volume) ∧
      ∀ᵐ t ∂μ, ∀ a, eLpNorm
        (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet a y) 2 volume ≤ ENNReal.ofReal ‖M t‖ := by
  classical
  let W := fun (a : JetIndex2 K) t => weightedPlaneLpReadout (planeMomentSquareRoot 4 ϖ z)
    (planeMomentSquareRoot_continuous 4 ϖ z) (planeJetReadoutOperator K a (f t))
  have hW (a : JetIndex2 K) : MemLp (W a) 2 μ :=
    polynomialMomentLpReadout_time_memLp ϖ z ρ hρ μ f hf he a
  let C := (Real.sqrt (2 + 4 / ϖ ^ 2)) ^ 4
  have hC : 0 ≤ C := by positivity
  let M : ℝ → ℝ := fun t => C * ∑ a : JetIndex2 K, ‖W a t‖
  have hsum : MemLp (fun t => ∑ a : JetIndex2 K, ‖W a t‖) 2 μ := by
    simpa only using
      memLp_finsetSum Finset.univ (fun a _ => (hW a).norm)
  have hM : MemLp M 2 μ := hsum.const_mul C
  have hfinite := polynomialMoment_energy_ae_finite ϖ z ρ μ f hf he
  refine ⟨M, hM, ?_, ?_⟩
  · intro a
    exact Filter.Eventually.of_forall (fun t =>
      (show Continuous (fun y : Vec 2 => (1 + ‖y - z‖) ^ 4) by fun_prop).aestronglyMeasurable.smul
        (by simpa only [Measure.restrict_univ] using ((f t).toFunction.memL2 a).aestronglyMeasurable))
  filter_upwards [hfinite] with t ht
  intro a
  have hs : ‖W a t‖ ≤ ∑ b : JetIndex2 K, ‖W b t‖ :=
    Finset.single_le_sum (f := fun b => ‖W b t‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ a)
  have hMn : 0 ≤ M t := mul_nonneg hC (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  calc
    _ ≤ ENNReal.ofReal C *
        eLpNorm (fun y => planeMomentSquareRoot 4 ϖ z y • (f t).toFunction.jet a y) 2 volume :=
      radialMoment_eLpNorm_le_polynomial ϖ hϖ z _
        (by simpa only [Measure.restrict_univ] using ((f t).toFunction.memL2 a).aestronglyMeasurable)
    _ = ENNReal.ofReal (C * ‖W a t‖) := by
      rw [polynomialMoment_eLpNorm_eq_readout_norm (f t) ϖ z ρ hρ ht a,
        ← ENNReal.ofReal_mul hC]
    _ ≤ ENNReal.ofReal ‖M t‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg hMn]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hs hC)
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Literal weighted Sobolev flux rows inherit both original-mass Schur sums without a vertex count. -/

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

theorem scalarWeightedFactorialRow_schur_budget
    (K : ι → ℕ) (ρ : ℝ) (q : Vec 2 → ℝ)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (A : Matrix ι ι ℝ) (hA : ∀ v u, 0 ≤ A v u)
    (C θ : ℝ) (hC : 0 ≤ C)
    (hrow : ∀ v, ∑ u, massConjugatedMatrix π A v u ≤ θ)
    (hcol : ∀ u, ∑ v, massConjugatedMatrix π A v u ≤ θ)
    (U : ∀ v _u : ι, PlaneHk Set.univ (K v) (E v)) (x : ι → ℝ) (hx : ∀ u, 0 ≤ x u)
    (hD : ∀ v u, JetMemL2On Set.univ (fun β z => q z • (U v u).toFunction.jet β z))
    (hS : ∀ v, JetMemL2On Set.univ (fun β z => q z • (∑ u, U v u).toFunction.jet β z))
    (hb : ∀ v u, storedChartFactorialEnergy ρ (fun z => q z ^ 2) (U v u) ≤
      ENNReal.ofReal ((C * A v u * x u) ^ 2)) :
    (∑ v, ENNReal.ofReal ((π v)⁻¹) *
      storedChartFactorialEnergy ρ (fun z => q z ^ 2) (∑ u, U v u)) ≤
      ENNReal.ofReal ((C * θ) ^ 2) *
        ∑ u, ENNReal.ofReal ((π u)⁻¹) * ENNReal.ofReal (x u ^ 2) := by
  let Y := fun v u => scalarWeightedFactorialJet ρ q (U v u) (hD v u)
  have hn (v u : ι) : ‖Y v u‖ ≤ C * A v u * x u := by
    have he := hb v u
    rw [← scalarWeightedFactorialJet_normSq ρ q (U v u) (hD v u)] at he
    have hs := (ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).mp he
    exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (mul_nonneg hC (hA v u)) (hx u))).mp hs
  have hbudget := massRowSchur_norm_sq π hπ A hA C θ hC hrow hcol Y x hn
  have hp (i : ι) : 0 ≤ (π i)⁻¹ := inv_nonneg.mpr (hπ i).le
  have hread (v : ι) : storedChartFactorialEnergy ρ (fun z => q z ^ 2) (∑ u, U v u) =
      ENNReal.ofReal (‖∑ u, Y v u‖ ^ 2) := by
    rw [← scalarWeightedFactorialJet_normSq ρ q _ (hS v),
      scalarWeightedFactorialJet_sum]
  simp_rw [hread, ← ENNReal.ofReal_mul (hp _)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hp i) (sq_nonneg _)),
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hp i) (sq_nonneg _)),
    ← ENNReal.ofReal_mul (sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hbudget

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Gradient moment energies obey the same quadratic addition bound as the native scalar energies. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance gradientEnergyAdditionNativeNormed (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k E) := inferInstance
local instance gradientEnergyAdditionNativeModule (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k E) := inferInstance

theorem weightedGradFactorialNormSq_add_le {K : ℕ} (n : ℕ) (ϖ : ℝ) (zc : Vec 2)
    (ρ : ℝ) (U V : PlaneHk Set.univ (K + 1) E) :
    weightedGradFactorialNormSq n ϖ zc ρ K (U + V) ≤
      2 * (weightedGradFactorialNormSq n ϖ zc ρ K U +
        weightedGradFactorialNormSq n ϖ zc ρ K V) := by
  rw [← planeGradientTensor_weightedFactorialNormSq n ϖ zc ρ (U + V),
    ← planeGradientTensor_weightedFactorialNormSq n ϖ zc ρ U,
    ← planeGradientTensor_weightedFactorialNormSq n ϖ zc ρ V]
  have hg : planeGradientTensor (U + V) = planeGradientTensor U + planeGradientTensor V := by
    rw [← planeGradientTensorOperator_apply K (U + V), map_add,
      planeGradientTensorOperator_apply, planeGradientTensorOperator_apply]
  rw [hg]
  exact weightedFactorialNormSq_add_le n ϖ zc ρ _ _

theorem integrated_weightedGradFactorialNormSq_add_le {K : ℕ}
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ) (μ : Measure ℝ)
    (U V : ℝ → PlaneHk Set.univ (K + 1) E) (hU : MemLp U 2 μ) :
    (∫⁻ t, weightedGradFactorialNormSq n ϖ zc ρ K (U t + V t) ∂μ) ≤
      2 * ((∫⁻ t, weightedGradFactorialNormSq n ϖ zc ρ K (U t) ∂μ) +
        ∫⁻ t, weightedGradFactorialNormSq n ϖ zc ρ K (V t) ∂μ) := by
  have hm := weightedGradFactorialNormSq_time_aemeasurable (E := E) n ϖ zc ρ μ U hU
  rw [← lintegral_add_left' hm _, ← lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  exact lintegral_mono (fun t => weightedGradFactorialNormSq_add_le n ϖ zc ρ (U t) (V t))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Adding the actual external and coupling fluxes preserves original masses. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeFamily_forcing_energy_add_le
    (K : ι → ℕ) (n : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ) (π : ι → ℝ)
    (F R : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 μ) :
    (∫⁻ t, ∑ i, ENNReal.ofReal ((π i)⁻¹) *
      weightedFactorialNormSq n ϖ zc ρ (K i) (F i t + R i t) ∂μ) ≤
      2 * ((∫⁻ t, ∑ i, ENNReal.ofReal ((π i)⁻¹) *
        weightedFactorialNormSq n ϖ zc ρ (K i) (F i t) ∂μ) +
        ∫⁻ t, ∑ i, ENNReal.ofReal ((π i)⁻¹) *
          weightedFactorialNormSq n ϖ zc ρ (K i) (R i t) ∂μ) := by
  classical
  have hm : AEMeasurable (fun t => ∑ i, ENNReal.ofReal ((π i)⁻¹) *
      weightedFactorialNormSq n ϖ zc ρ (K i) (F i t)) μ :=
    Finset.aemeasurable_fun_sum _ (fun i _ =>
      (weightedFactorialNormSq_time_aemeasurable n ϖ zc ρ μ _ (hF i)).const_mul _)
  rw [← lintegral_add_left' hm _,
    ← lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  apply lintegral_mono
  intro t
  calc
    _ ≤ ∑ i, ENNReal.ofReal ((π i)⁻¹) *
        (2 * (weightedFactorialNormSq n ϖ zc ρ (K i) (F i t) +
          weightedFactorialNormSq n ϖ zc ρ (K i) (R i t))) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (weightedFactorialNormSq_add_le n ϖ zc ρ (F i t) (R i t)) zero_le)
    _ = _ := by
      have he (i : ι) (x y : ℝ≥0∞) :
          ENNReal.ofReal ((π i)⁻¹) * (2 * (x + y)) =
            2 * (ENNReal.ofReal ((π i)⁻¹) * x + ENNReal.ofReal ((π i)⁻¹) * y) := by
        rw [mul_left_comm, mul_add]
      simp_rw [he]
      rw [← Finset.mul_sum, Finset.sum_add_distrib]

end AVRegularity.CycleJointProofs
end
end

section
public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Static native family energies satisfy the quadratic inequalities used in
 chronological operator composition, even when some moments are infinite. -/

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

theorem planeFamily_polynomial_energy_add_le
    (K : ι → ℕ) (π : ι → ℝ) (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ)
    (U V : ∀ i, PlaneHk Set.univ (K i) (E i)) :
    (∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ zc ρ (K i) (U i + V i)) ≤
      2 * ((∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ zc ρ (K i) (U i)) +
        ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ zc ρ (K i) (V i)) := by
  calc
    _ ≤ ∑ i, ENNReal.ofReal ((π i)⁻¹) *
        (2 * (weightedFactorialNormSq n ϖ zc ρ (K i) (U i) +
          weightedFactorialNormSq n ϖ zc ρ (K i) (V i))) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_right (weightedFactorialNormSq_add_le n ϖ zc ρ (U i) (V i)) _
    _ = ∑ i, 2 * (ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ zc ρ (K i) (U i) +
        ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ zc ρ (K i) (V i)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_add_distrib]

/-- The retained endpoint energy is bounded by the true endpoint and its error. -/
theorem planeFamily_polynomial_energy_of_approximation_le
    (K : ι → ℕ) (π : ι → ℝ) (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ)
    (U V : ∀ i, PlaneHk Set.univ (K i) (E i)) :
    (∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ zc ρ (K i) (V i)) ≤
      2 * ((∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ zc ρ (K i) (U i)) +
        ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ zc ρ (K i) (U i - V i)) := by
  have hh := planeFamily_polynomial_energy_add_le K π n ϖ zc ρ U (fun i => -(U i - V i))
  have heq (i : ι) : U i + -(U i - V i) = V i := by
    rw [neg_sub, ← add_sub_assoc, add_sub_cancel_left]
  simpa only [heq, weightedFactorialNormSq_neg] using hh

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Genuine finite polynomial-moment time curves form a linear domain for causal native response operators. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance momentTimeNativeNormed (k : ℕ) : NormedAddCommGroup (PlaneHk Set.univ k E) :=
  inferInstance
local instance momentTimeNativeModule (k : ℕ) : Module ℝ (PlaneHk Set.univ k E) := inferInstance
local instance momentTimeLpAdd (k : ℕ) (μ : Measure ℝ) :
    AddCommGroup (Lp (PlaneHk Set.univ k E) 2 μ) := inferInstance
local instance momentTimeLpModule (k : ℕ) (μ : Measure ℝ) :
    Module ℝ (Lp (PlaneHk Set.univ k E) 2 μ) := inferInstance

def planeTimeMomentSubmodule (K N : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ) :
    Submodule ℝ (Lp (PlaneHk Set.univ K E) 2 μ) where
  carrier := {f | ∀ n ≤ N, (∫⁻ t, weightedFactorialNormSq n ϖ zc ρ K (f t) ∂μ) ≠ ⊤}
  zero_mem' := by
    intro n _
    have he : (fun t => weightedFactorialNormSq n ϖ zc ρ K
        ((0 : Lp (PlaneHk Set.univ K E) 2 μ) t)) =ᵐ[μ] fun _ => 0 := by
      filter_upwards [Lp.coeFn_zero (E := PlaneHk Set.univ K E) (p := 2) (μ := μ)] with t ht
      simp only [ht, Pi.zero_apply, weightedFactorialNormSq_zero_carrier]
    rw [lintegral_congr_ae he, lintegral_zero]
    exact ENNReal.zero_ne_top
  add_mem' := by
    intro f g hf hg n hn
    have hi := integrated_weightedFactorialNormSq_add_ne_top n ϖ zc ρ μ
      (fun t => f t) (fun t => g t) (Lp.memLp f) (hf n hn) (hg n hn)
    have he : (fun t => weightedFactorialNormSq n ϖ zc ρ K ((f + g) t)) =ᵐ[μ]
        fun t => weightedFactorialNormSq n ϖ zc ρ K (f t + g t) := by
      filter_upwards [Lp.coeFn_add f g] with t ht
      simp only [ht, Pi.add_apply]
    rw [lintegral_congr_ae he]
    exact hi
  smul_mem' := by
    intro c f hf n hn
    have hi := integrated_weightedFactorialNormSq_smul_ne_top n ϖ zc ρ c μ
      (fun t => f t) (hf n hn)
    have he : (fun t => weightedFactorialNormSq n ϖ zc ρ K ((c • f) t)) =ᵐ[μ]
        fun t => weightedFactorialNormSq n ϖ zc ρ K (c • f t) := by
      filter_upwards [Lp.coeFn_smul c f] with t ht
      simp only [ht, Pi.smul_apply]
    rw [lintegral_congr_ae he]
    exact hi

theorem mem_planeTimeMomentSubmodule (K N : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ)
    (f : Lp (PlaneHk Set.univ K E) 2 μ) :
    f ∈ planeTimeMomentSubmodule K N ϖ ρ zc μ ↔
      ∀ n ≤ N, (∫⁻ t, weightedFactorialNormSq n ϖ zc ρ K (f t) ∂μ) ≠ ⊤ := Iff.rfl

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set Filter AVRegularity.Sobolev AVRegularity.CycleWords
open scoped Topology
namespace AVRegularity.CycleJointProofs

/-! Arbitrary native plane Sobolev data have genuine compact smooth approximations in their full stored norm. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeHk_exists_compact_smooth_approximation {K : ℕ} (U : PlaneHk univ K E) :
    ∃ UN : ℕ → PlaneHk univ K E, ∃ fN : ℕ → Vec 2 → E,
      Tendsto UN atTop (𝓝 U) ∧
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (fN n) ∧ HasCompactSupport (fN n)) ∧
      (∀ n, planeValue (UN n) =ᵐ[volume] fN n) := by
  have hw : JetMemL2On univ (fun a x => (1 : ℝ) • U.toFunction.jet a x) := by
    simpa only [one_smul] using U.toFunction.memL2
  obtain ⟨UN, fN, hs, hv, hj⟩ := exists_weighted_compact_smooth_approximation U (fun _ => 1)
    continuous_const hw
  choose hm hmU ht using hj
  let RN (n : ℕ) : PiLp 2 (fun _ : JetIndex2 K => Lp E 2 (volume : Measure (Vec 2))) :=
    WithLp.toLp 2 (fun a => (hm a n).toLp (fun x => (1 : ℝ) • (UN n).toFunction.jet a x))
  let R : PiLp 2 (fun _ : JetIndex2 K => Lp E 2 (volume : Measure (Vec 2))) :=
    WithLp.toLp 2 (fun a => (hmU a).toLp (fun x => (1 : ℝ) • U.toFunction.jet a x))
  have hRN n a : RN n a =ᵐ[volume] fun x => (1 : ℝ) • (UN n).toFunction.jet a x :=
    (hm a n).coeFn_toLp
  have hR a : R a =ᵐ[volume] fun x => (1 : ℝ) • U.toFunction.jet a x := (hmU a).coeFn_toLp
  have hlim : Tendsto RN atTop (𝓝 R) :=
    ((PiLp.continuous_toLp 2 (fun _ : JetIndex2 K => Lp E 2 (volume : Measure (Vec 2)))).tendsto _).comp
      (tendsto_pi_nhds.mpr ht)
  exact ⟨UN, fN, weightedJetArray_tendsto_native UN U (fun _ => 1) (fun _ => le_rfl)
    RN R hRN hR hlim, hs, hv⟩

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! Bounded smooth volume-preserving charts pull back arbitrary native Sobolev data. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeHk_smooth_pullback_exists {K : ℕ} (U : PlaneHk univ K E)
    (X : Vec 2 ≃ₜ Vec 2) (hX : ContDiff ℝ (⊤ : ℕ∞) (X : Vec 2 → Vec 2))
    (hμ : MeasurePreserving (X : Vec 2 → Vec 2) volume volume)
    (B : ℕ → ℝ) (hB : ∀ j, 1 ≤ j → j ≤ K → 0 ≤ B j)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ x, ‖iteratedFDeriv ℝ j (X : Vec 2 → Vec 2) x‖ ≤ B j) :
    ∃ V : PlaneHk univ K E, planeValue V =ᵐ[volume] planeValue U ∘ X := by
  have hw : JetMemL2On univ (fun a x => (1 : ℝ) • U.toFunction.jet a x) := by
    simpa only [one_smul] using U.toFunction.memL2
  obtain ⟨V, hv, _⟩ := weighted_plane_pullback_exists U X hX hμ
    (fun _ => 1) (fun _ => 1) (fun _ => 1) continuous_const continuous_const
    (fun _ => le_rfl) (fun _ => le_rfl) B 1 zero_le_one (fun _ => le_rfl) hB
    (fun j hj hjK x => by simpa only [mul_one] using hb j hj hjK x)
    (fun _ => by simp only [one_pow, mul_one, le_refl]) hw
  exact ⟨V, hv⟩

def planeHkSmoothPullback {K : ℕ} (X : Vec 2 ≃ₜ Vec 2)
    (hX : ContDiff ℝ (⊤ : ℕ∞) (X : Vec 2 → Vec 2))
    (hμ : MeasurePreserving (X : Vec 2 → Vec 2) volume volume)
    (B : ℕ → ℝ) (hB : ∀ j, 1 ≤ j → j ≤ K → 0 ≤ B j)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ x, ‖iteratedFDeriv ℝ j (X : Vec 2 → Vec 2) x‖ ≤ B j)
    (U : PlaneHk univ K E) : PlaneHk univ K E :=
  (planeHk_smooth_pullback_exists U X hX hμ B hB hb).choose

theorem planeHkSmoothPullback_value_ae {K : ℕ} (X : Vec 2 ≃ₜ Vec 2)
    (hX : ContDiff ℝ (⊤ : ℕ∞) (X : Vec 2 → Vec 2))
    (hμ : MeasurePreserving (X : Vec 2 → Vec 2) volume volume)
    (B : ℕ → ℝ) (hB : ∀ j, 1 ≤ j → j ≤ K → 0 ≤ B j)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ x, ‖iteratedFDeriv ℝ j (X : Vec 2 → Vec 2) x‖ ≤ B j)
    (U : PlaneHk univ K E) :
    planeValue (planeHkSmoothPullback X hX hμ B hB hb U) =ᵐ[volume] planeValue U ∘ X :=
  (planeHk_smooth_pullback_exists U X hX hμ B hB hb).choose_spec

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The all-moment native time domain lets finite Taylor insertions compose without changing their underlying carrier; quantitative estimates still spend only finite reserves. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance allMomentTimeNativeNormed (k : ℕ) : NormedAddCommGroup (PlaneHk Set.univ k E) :=
  inferInstance
local instance allMomentTimeNativeModule (k : ℕ) : Module ℝ (PlaneHk Set.univ k E) := inferInstance
local instance allMomentTimeLpAdd (k : ℕ) (μ : Measure ℝ) :
    AddCommGroup (Lp (PlaneHk Set.univ k E) 2 μ) := inferInstance
local instance allMomentTimeLpModule (k : ℕ) (μ : Measure ℝ) :
    Module ℝ (Lp (PlaneHk Set.univ k E) 2 μ) := inferInstance

def planeTimeAllMomentSubmodule (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ) :
    Submodule ℝ (Lp (PlaneHk Set.univ K E) 2 μ) :=
  ⨅ N : ℕ, planeTimeMomentSubmodule K N ϖ ρ zc μ

theorem mem_planeTimeAllMomentSubmodule (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ)
    (f : Lp (PlaneHk Set.univ K E) 2 μ) :
    f ∈ planeTimeAllMomentSubmodule K ϖ ρ zc μ ↔
      ∀ n, (∫⁻ t, weightedFactorialNormSq n ϖ zc ρ K (f t) ∂μ) ≠ ⊤ := by
  simp only [planeTimeAllMomentSubmodule, Submodule.mem_iInf, mem_planeTimeMomentSubmodule]
  exact ⟨fun h n => h n n (le_refl n), fun h _ n _ => h n⟩

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! The exact public geometry energy supplies every source's common radial time price. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem exists_finiteGeometry_radial_lift_budget (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (K : ι → ℕ) (a b ϖ : ℝ) (hϖ : 0 < ϖ) (z : Vec 2) (ρ : ℝ) (hρ : 0 < ρ)
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b)))
    (hlift : ∀ i, ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      truncatePlaneHk (Nat.le_succ (K i)) (w i t) = u i t)
    (he : geometryEnergyNorm π K 4 ϖ z ρ a b u w < ⊤) :
    ∃ M : ι → ℝ → ℝ, ∀ i,
      MemLp (M i) 2 (volume.restrict (Set.Icc a b)) ∧
      (∀ α, ∀ᵐ t ∂volume.restrict (Set.Icc a b), AEStronglyMeasurable
        (fun y => (1 + ‖y - z‖) ^ 4 • (w i t).toFunction.jet α y) volume) ∧
      ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ α, eLpNorm
        (fun y => (1 + ‖y - z‖) ^ 4 • (w i t).toFunction.jet α y) 2 volume ≤
          ENNReal.ofReal ‖M i t‖ := by
  have hex (i : ι) : ∃ M : ℝ → ℝ,
      MemLp M 2 (volume.restrict (Set.Icc a b)) ∧
      (∀ α, ∀ᵐ t ∂volume.restrict (Set.Icc a b), AEStronglyMeasurable
        (fun y => (1 + ‖y - z‖) ^ 4 • (w i t).toFunction.jet α y) volume) ∧
      ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ α, eLpNorm
        (fun y => (1 + ‖y - z‖) ^ 4 • (w i t).toFunction.jet α y) 2 volume ≤
          ENNReal.ofReal ‖M t‖ := by
    obtain ⟨C, _, hb, hg⟩ := finite_geometry_energy_component π hπ K 4 ϖ z ρ a b u w he i
    have hbAE : ∀ᵐ t ∂volume.restrict (Set.Icc a b),
        weightedFactorialNormSq 4 ϖ z ρ (K i) (u i t) ≤ ENNReal.ofReal C :=
      (ae_restrict_mem measurableSet_Icc).mono (fun t ht => hb t ht)
    have hfull := polynomial_production_lift_energy_ne_top 4 ϖ z ρ hρ
      (volume.restrict (Set.Icc a b)) (u i) (w i) (hw i) (hlift i) C hbAE hg
    exact exists_polynomialCarrier_radial_time_budget ϖ hϖ z ρ hρ
      (volume.restrict (Set.Icc a b)) (w i) (hw i) hfull
  choose M hM using hex
  exact ⟨M, hM⟩

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The zero native carrier has zero literal polynomial gradient energy. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem weightedGradFactorialNormSq_zero_native (K n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ) :
    weightedGradFactorialNormSq n ϖ zc ρ K (0 : PlaneHk Set.univ (K + 1) E) = 0 := by
  rw [← planeGradientTensor_weightedFactorialNormSq n ϖ zc ρ,
    ← planeGradientTensorOperator_apply K, map_zero]
  exact AVRegularity.Weighted.weightedFactorialNormSq_zero_carrier n ϖ zc ρ K

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set Filter AVRegularity.Sobolev AVRegularity.CycleWords
open scoped Topology
namespace AVRegularity.CycleJointProofs

/-! Genuine smooth compact native carriers determine every continuous linear Sobolev operator. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem planeHkOperator_eq_of_compact_smooth {K : ℕ}
    (L R : PlaneHk univ K E →L[ℝ] Y)
    (he : ∀ U : PlaneHk univ K E, ∀ f : Vec 2 → E,
      ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      planeValue U =ᵐ[volume] f → L U = R U) : L = R := by
  ext U
  obtain ⟨UN, fN, hUN, hfN, hvN⟩ := planeHk_exists_compact_smooth_approximation U
  have hL := (L.continuous.tendsto U).comp hUN
  have hR := (R.continuous.tendsto U).comp hUN
  have hseq : (fun N => L (UN N)) = (fun N => R (UN N)) := by
    funext N
    exact he (UN N) (fN N) (hfN N).1 (hfN N).2 (hvN N)
  change Tendsto (fun N => L (UN N)) atTop (𝓝 (L U)) at hL
  change Tendsto (fun N => R (UN N)) atTop (𝓝 (R U)) at hR
  rw [hseq] at hL
  exact tendsto_nhds_unique hL hR

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! The higher native pullback is linear and isometric on its value trace. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

variable {K : ℕ} (X : Vec 2 ≃ₜ Vec 2)
    (hX : ContDiff ℝ (⊤ : ℕ∞) (X : Vec 2 → Vec 2))
    (hμ : MeasurePreserving (X : Vec 2 → Vec 2) volume volume)
    (B : ℕ → ℝ) (hB : ∀ j, 1 ≤ j → j ≤ K → 0 ≤ B j)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ x, ‖iteratedFDeriv ℝ j (X : Vec 2 → Vec 2) x‖ ≤ B j)

theorem planeHkSmoothPullback_value_eq (U : PlaneHk univ K E) :
    planeHkValueOperator K (planeHkSmoothPullback X hX hμ B hB hb U) =
      Lp.compMeasurePreservingₗᵢ ℝ (X : Vec 2 → Vec 2) hμ (planeHkValueOperator K U) :=
  planeValueLp_transport_eq U _ X hμ (planeHkSmoothPullback_value_ae X hX hμ B hB hb U)

theorem planeHk_eq_of_value {U V : PlaneHk univ K E}
    (h : planeHkValueOperator K U = planeHkValueOperator K V) : U = V := by
  apply planeHk_eq_of_planeValue_ae
  exact (planeValueLp_ae U).symm.trans (h ▸ planeValueLp_ae V)

def planeHkSmoothPullbackLinearMap : PlaneHk univ K E →ₗ[ℝ] PlaneHk univ K E where
  toFun := planeHkSmoothPullback X hX hμ B hB hb
  map_add' := by
    intro U V
    apply planeHk_eq_of_value
    simp only [planeHkSmoothPullback_value_eq, map_add]
  map_smul' := by
    intro c U
    apply planeHk_eq_of_value
    simp only [planeHkSmoothPullback_value_eq, map_smul, RingHom.id_apply]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Actual response representatives with every finite moment restrict their linear time-L2 map to the all-moment native domain. -/

section
variable {X E : Type*} [AddCommGroup X] [Module ℝ X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance allMomentMapNativeNormed (k : ℕ) : NormedAddCommGroup (PlaneHk Set.univ k E) :=
  inferInstance
local instance allMomentMapNativeModule (k : ℕ) : Module ℝ (PlaneHk Set.univ k E) := inferInstance
local instance allMomentMapLpAdd (k : ℕ) (μ : Measure ℝ) :
    AddCommGroup (Lp (PlaneHk Set.univ k E) 2 μ) := inferInstance
local instance allMomentMapLpModule (k : ℕ) (μ : Measure ℝ) :
    Module ℝ (Lp (PlaneHk Set.univ k E) 2 μ) := inferInstance

def planeTimeAllMomentLinearMap (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ)
    (T : X →ₗ[ℝ] Lp (PlaneHk Set.univ K E) 2 μ)
    (w : X → ℝ → PlaneHk Set.univ K E) (hw : ∀ x, MemLp (w x) 2 μ)
    (heq : ∀ x, (hw x).toLp (w x) = T x)
    (he : ∀ x n, (∫⁻ t, weightedFactorialNormSq n ϖ zc ρ K (w x t) ∂μ) ≠ ⊤) :
    X →ₗ[ℝ] planeTimeAllMomentSubmodule (E := E) K ϖ ρ zc μ :=
  LinearMap.codRestrict (planeTimeAllMomentSubmodule K ϖ ρ zc μ) T (by
    intro x
    apply (mem_planeTimeAllMomentSubmodule K ϖ ρ zc μ (T x)).mpr
    intro n
    rw [← heq x]
    have hAE : (fun t => weightedFactorialNormSq n ϖ zc ρ K (((hw x).toLp (w x)) t)) =ᵐ[μ]
        fun t => weightedFactorialNormSq n ϖ zc ρ K (w x t) := by
      filter_upwards [(hw x).coeFn_toLp] with t ht
      rw [ht]
    rw [lintegral_congr_ae hAE]
    exact he x n)
end

/-! Canonical representatives of the native all-moment time domain retain the moments and are linear almost everywhere. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance allMomentRepNativeNormed (k : ℕ) : NormedAddCommGroup (PlaneHk Set.univ k E) :=
  inferInstance
local instance allMomentRepNativeModule (k : ℕ) : Module ℝ (PlaneHk Set.univ k E) := inferInstance
local instance allMomentRepLpAdd (k : ℕ) (μ : Measure ℝ) :
    AddCommGroup (Lp (PlaneHk Set.univ k E) 2 μ) := inferInstance
local instance allMomentRepLpModule (k : ℕ) (μ : Measure ℝ) :
    Module ℝ (Lp (PlaneHk Set.univ k E) 2 μ) := inferInstance

variable (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ)

theorem planeTimeAllMoment_representative_moment
    (f : planeTimeAllMomentSubmodule (E := E) K ϖ ρ zc μ) (n : ℕ) :
    (∫⁻ t, weightedFactorialNormSq n ϖ zc ρ K (f.val t) ∂μ) ≠ ⊤ :=
  (mem_planeTimeAllMomentSubmodule K ϖ ρ zc μ f.val).mp f.property n
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Subtracting the retained trajectory preserves finite polynomial gradient energy. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance gradientEnergySubtractionNativeNormed (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k E) := inferInstance
local instance gradientEnergySubtractionNativeModule (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k E) := inferInstance

local instance gradientEnergySubtractionNativeAdd (k : ℕ) :
    AddCommGroup (PlaneHk Set.univ k E) :=
  (gradientEnergySubtractionNativeNormed k).toAddCommGroup

local instance gradientEnergySubtractionNativeNeg (k : ℕ) :
    Neg (PlaneHk Set.univ k E) :=
  (gradientEnergySubtractionNativeAdd k).toAddGroup.toSubNegMonoid.toNeg

theorem weightedGradFactorialNormSq_neg {K : ℕ} (n : ℕ) (ϖ : ℝ) (zc : Vec 2)
    (ρ : ℝ) (U : PlaneHk Set.univ (K + 1) E) :
    weightedGradFactorialNormSq n ϖ zc ρ K (-U) = weightedGradFactorialNormSq n ϖ zc ρ K U := by
  rw [← planeGradientTensor_weightedFactorialNormSq n ϖ zc ρ (-U),
    ← planeGradientTensor_weightedFactorialNormSq n ϖ zc ρ U]
  have hg : planeGradientTensor (-U) = -planeGradientTensor U := by
    rw [← planeGradientTensorOperator_apply K (-U), map_neg, planeGradientTensorOperator_apply]
  rw [hg, weightedFactorialNormSq_neg]

theorem integrated_weightedGradFactorialNormSq_sub_ne_top {K : ℕ}
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ) (μ : Measure ℝ)
    (U V : ℝ → PlaneHk Set.univ (K + 1) E) (hU : MemLp U 2 μ)
    (heU : (∫⁻ t, weightedGradFactorialNormSq n ϖ zc ρ K (U t) ∂μ) ≠ ⊤)
    (heV : (∫⁻ t, weightedGradFactorialNormSq n ϖ zc ρ K (V t) ∂μ) ≠ ⊤) :
    (∫⁻ t, weightedGradFactorialNormSq n ϖ zc ρ K (U t - V t) ∂μ) ≠ ⊤ := by
  have hb := integrated_weightedGradFactorialNormSq_add_le n ϖ zc ρ μ U (fun t => -V t) hU
  simp only [weightedGradFactorialNormSq_neg, ← sub_eq_add_neg] at hb
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (by norm_num) (ENNReal.add_ne_top.mpr ⟨heU, heV⟩)) hb

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set Filter AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped Topology
namespace AVRegularity.CycleJointProofs

/-! The native higher pullback is continuous by its exact value readout and the closed graph theorem. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

variable {K : ℕ} (X : Vec 2 ≃ₜ Vec 2)
    (hX : ContDiff ℝ (⊤ : ℕ∞) (X : Vec 2 → Vec 2))
    (hμ : MeasurePreserving (X : Vec 2 → Vec 2) volume volume)
    (B : ℕ → ℝ) (hB : ∀ j, 1 ≤ j → j ≤ K → 0 ≤ B j)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ x, ‖iteratedFDeriv ℝ j (X : Vec 2 → Vec 2) x‖ ≤ B j)

theorem planeHkSmoothPullback_continuous :
    Continuous (planeHkSmoothPullback (E := E) X hX hμ B hB hb) := by
  let T := planeHkSmoothPullbackLinearMap (E := E) X hX hμ B hB hb
  let L := planeHkValueOperator (E := E) K
  let P : Lp E 2 (volume : Measure (Vec 2)) →ₗᵢ[ℝ] Lp E 2 (volume : Measure (Vec 2)) :=
    Lp.compMeasurePreservingₗᵢ ℝ (X : Vec 2 → Vec 2) hμ
  apply T.continuous_of_seq_closed_graph
  intro U V W hU hT
  apply planeHk_eq_of_value
  have hW : Tendsto (fun n => L (T (U n))) atTop (𝓝 (L W)) :=
    (L.continuous.tendsto W).comp hT
  have hV : Tendsto (fun n => P (L (U n))) atTop (𝓝 (P (L V))) :=
    (P.continuous.tendsto (L V)).comp ((L.continuous.tendsto V).comp hU)
  have he : (fun n => L (T (U n))) = (fun n => P (L (U n))) := by
    funext n
    exact planeHkSmoothPullback_value_eq X hX hμ B hB hb (U n)
  rw [he] at hW
  exact (tendsto_nhds_unique hW hV).trans
    (planeHkSmoothPullback_value_eq X hX hμ B hB hb V).symm

def planeHkSmoothPullbackOperator : PlaneHk univ K E →L[ℝ] PlaneHk univ K E :=
  { planeHkSmoothPullbackLinearMap X hX hμ B hB hb with
    cont := planeHkSmoothPullback_continuous X hX hμ B hB hb }

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.CycleJointProofs

/-! Actual transformed chains use the periodic pulse drift on the corresponding natural block. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Replacing the actual material drift by the cell drift `ocCellDrift` preserves the entire weak
chain. -/
theorem planeWeakSolution_naturalBlock_cell_drift {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsOCStreamSeq α q Λ ζ Φ)
    (hm : 1 ≤ m) (hφ : IsAdmissibleStream (Φ (m - 1)))
    (hΨ : IsAdmissibleStream (Φ m)) {ν : ℝ} (hν : 0 < ν)
    (l : ℤ) (yc : Vec 2) {D : ℕ} (K : ι → ℕ)
    (A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (a b : ℝ)
    (hblock : ∀ t ∈ Set.Icc a b,
      ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ ocEll q Λ m ν ^ 2 * t ∧
      ocEll q Λ m ν ^ 2 * t ≤ ((l : ℝ) + 1 / 2) * ocTauPP α q Λ m)
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane 1 a b
      (fun t z => ocEpsilon q Λ m • normalizedMaterialVelocity hφ
        ((l : ℝ) * ocTauPP α q Λ m) ν (streamVel (Φ m))
        (ocEpsilon q Λ m ^ 2 * t) (yc + ocEpsilon q Λ m • z)) D K A f F g u w) :
    IsCoupledWeakSolutionPlane 1 a b (ocCellDrift α q Λ ζ m ν yc) D K A f F g u w := by
  apply planeWeakSolution_drift_window_congr _ hs
  intro t ht
  funext z
  exact naturalBlock_normalized_cell_drift hΛ hseq hm hφ hΨ hν l t yc z (hblock t ht)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Reverse charts invert the actual native higher Sobolev pullback. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeHkSmoothPullback_inverse {K : ℕ} (X : Vec 2 ≃ₜ Vec 2)
    (hX : ContDiff ℝ (⊤ : ℕ∞) (X : Vec 2 → Vec 2))
    (hY : ContDiff ℝ (⊤ : ℕ∞) (X.symm : Vec 2 → Vec 2))
    (hμ : MeasurePreserving (X : Vec 2 → Vec 2) volume volume)
    (hμY : MeasurePreserving (X.symm : Vec 2 → Vec 2) volume volume)
    (B C : ℕ → ℝ)
    (hB : ∀ j, 1 ≤ j → j ≤ K → 0 ≤ B j) (hC : ∀ j, 1 ≤ j → j ≤ K → 0 ≤ C j)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ x, ‖iteratedFDeriv ℝ j (X : Vec 2 → Vec 2) x‖ ≤ B j)
    (hc : ∀ j, 1 ≤ j → j ≤ K → ∀ x, ‖iteratedFDeriv ℝ j (X.symm : Vec 2 → Vec 2) x‖ ≤ C j)
    (U : PlaneHk univ K E) :
    planeHkSmoothPullback X.symm hY hμY C hC hc (planeHkSmoothPullback X hX hμ B hB hb U) = U := by
  apply planeHk_eq_of_planeValue_ae
  have he := hμY.quasiMeasurePreserving.ae_eq_comp
    (planeHkSmoothPullback_value_ae X hX hμ B hB hb U)
  filter_upwards [planeHkSmoothPullback_value_ae X.symm hY hμY C hC hc
    (planeHkSmoothPullback X hX hμ B hB hb U), he] with x hx hex
  change planeValue (planeHkSmoothPullback X hX hμ B hB hb U) (X.symm x) =
    planeValue U (X (X.symm x)) at hex
  exact hx.trans (hex.trans (congrArg (planeValue U) (X.apply_symm_apply x)))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set Filter AVRegularity.Sobolev AVRegularity.CycleWords
open scoped Topology
namespace AVRegularity.CycleJointProofs

/-! The explicit finite derivative budget controls the pullback of arbitrary native data. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

variable {K : ℕ} (X : Vec 2 ≃ₜ Vec 2)
    (hX : ContDiff ℝ (⊤ : ℕ∞) (X : Vec 2 → Vec 2))
    (hμ : MeasurePreserving (X : Vec 2 → Vec 2) volume volume)
    (B : ℕ → ℝ) (hB : ∀ j, 1 ≤ j → j ≤ K → 0 ≤ B j)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ x, ‖iteratedFDeriv ℝ j (X : Vec 2 → Vec 2) x‖ ≤ B j)

theorem planeHkSmoothPullback_eq_smooth (U : PlaneHk univ K E)
    (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hu : planeValue U =ᵐ[volume] f) :
    planeHkSmoothPullback X hX hμ B hB hb U = smoothPlanePullback U f hf hu X hX hμ B hb := by
  apply planeHk_eq_of_planeValue_ae
  exact ((planeHkSmoothPullback_value_ae X hX hμ B hB hb U).trans
    (hμ.quasiMeasurePreserving.ae_eq_comp hu)).trans
      (smoothPlanePullback_value_ae U f hf hu X hX hμ B hb).symm

theorem planeHkSmoothPullback_norm_le (U : PlaneHk univ K E) :
    ‖planeHkSmoothPullback X hX hμ B hB hb U‖ ≤ smoothPullbackNormBound B K * ‖U‖ := by
  obtain ⟨UN, fN, hUN, hfN, hvN⟩ := exists_smooth_planeHk_approximation U
  have hl := ((planeHkSmoothPullback_continuous X hX hμ B hB hb).tendsto U).comp hUN
  have hn n : ‖planeHkSmoothPullback X hX hμ B hB hb (UN n)‖ ≤
      smoothPullbackNormBound B K * ‖UN n‖ := by
    rw [planeHkSmoothPullback_eq_smooth X hX hμ B hB hb (UN n) (fN n) (hfN n) (hvN n)]
    exact smoothPlanePullback_norm_le (UN n) (fN n) (hfN n) (hvN n) X hX hμ B hb
  exact le_of_tendsto_of_tendsto' hl.norm (hUN.norm.const_mul (smoothPullbackNormBound B K)) hn

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! Native chart pullbacks commute with the stored Sobolev truncations. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeHkSmoothPullback_truncate {K L : ℕ} (hKL : K ≤ L)
    (X : Vec 2 ≃ₜ Vec 2) (hX : ContDiff ℝ (⊤ : ℕ∞) (X : Vec 2 → Vec 2))
    (hμ : MeasurePreserving (X : Vec 2 → Vec 2) volume volume)
    (B : ℕ → ℝ) (hB : ∀ j, 1 ≤ j → j ≤ L → 0 ≤ B j)
    (hb : ∀ j, 1 ≤ j → j ≤ L → ∀ x, ‖iteratedFDeriv ℝ j (X : Vec 2 → Vec 2) x‖ ≤ B j)
    (U : PlaneHk univ L E) :
    truncatePlaneHk hKL (planeHkSmoothPullback X hX hμ B hB hb U) =
      planeHkSmoothPullback X hX hμ B (fun j hj hjK => hB j hj (hjK.trans hKL))
        (fun j hj hjK => hb j hj (hjK.trans hKL)) (truncatePlaneHk hKL U) := by
  apply planeHk_eq_of_value
  rw [planeHkValueOperator_truncate,
    planeHkSmoothPullback_value_eq X hX hμ B hB hb U,
    planeHkSmoothPullback_value_eq, planeHkValueOperator_truncate]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The actual value readout determines measurability of the native Sobolev time state. -/

variable {E T : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace T]

theorem planeHk_time_aestronglyMeasurable_of_value {K : ℕ} (μ : Measure T)
    (u : T → PlaneHk univ K E)
    (hv : AEStronglyMeasurable (fun t => planeHkValueOperator K (u t)) μ) :
    AEStronglyMeasurable u μ := by
  let : TopologicalSpace.SeparableSpace (PlaneHk univ K E) := planeHkSeparableSpace K
  let : MeasurableSpace (PlaneHk univ K E) := borel _
  let : BorelSpace (PlaneHk univ K E) := ⟨rfl⟩
  let : MeasurableSpace (Lp E 2 (volume : Measure (Vec 2))) := borel _
  let : BorelSpace (Lp E 2 (volume : Measure (Vec 2))) := ⟨rfl⟩
  have he : MeasurableEmbedding (planeHkValueOperator (E := E) K) :=
    (planeHkValueOperator (E := E) K).continuous.measurableEmbedding
      (fun _ _ h => planeHk_eq_of_value h)
  exact (he.aemeasurable_comp_iff.mp hv.aemeasurable).aestronglyMeasurable

end AVRegularity.CycleJointProofs
end
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! A named carrier keeps the native all-moment domain and its linear projection explicit. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance momentCarrierNativeNormed (k : ℕ) : NormedAddCommGroup (PlaneHk Set.univ k E) :=
  allMomentTimeNativeNormed k
local instance momentCarrierNativeModule (k : ℕ) : Module ℝ (PlaneHk Set.univ k E) :=
  allMomentTimeNativeModule k
local instance momentCarrierLpAdd (k : ℕ) (μ : Measure ℝ) :
    AddCommGroup (Lp (PlaneHk Set.univ k E) 2 μ) := allMomentTimeLpAdd k μ
local instance momentCarrierLpModule (k : ℕ) (μ : Measure ℝ) :
    Module ℝ (Lp (PlaneHk Set.univ k E) 2 μ) := allMomentTimeLpModule k μ

def PlaneTimeAllMomentCarrier (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ) : Type _ :=
  ↥(planeTimeAllMomentSubmodule (E := E) K ϖ ρ zc μ)

instance instAddCommGroupPlaneTimeAllMomentCarrier (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ) :
    AddCommGroup (PlaneTimeAllMomentCarrier (E := E) K ϖ ρ zc μ) :=
  inferInstanceAs (AddCommGroup (planeTimeAllMomentSubmodule (E := E) K ϖ ρ zc μ))
instance instModuleRealPlaneTimeAllMomentCarrier (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ) :
    Module ℝ (PlaneTimeAllMomentCarrier (E := E) K ϖ ρ zc μ) :=
  inferInstanceAs (Module ℝ (planeTimeAllMomentSubmodule (E := E) K ϖ ρ zc μ))

def planeTimeAllMomentCarrierToLp (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ) :
    PlaneTimeAllMomentCarrier (E := E) K ϖ ρ zc μ →ₗ[ℝ] Lp (PlaneHk Set.univ K E) 2 μ :=
  (planeTimeAllMomentSubmodule K ϖ ρ zc μ).subtype

theorem planeTimeAllMomentCarrier_memLp (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ)
    (f : PlaneTimeAllMomentCarrier (E := E) K ϖ ρ zc μ) :
    MemLp (planeTimeAllMomentCarrierToLp K ϖ ρ zc μ f) 2 μ :=
  Lp.memLp _

theorem planeTimeAllMomentCarrier_moment (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ)
    (f : PlaneTimeAllMomentCarrier (E := E) K ϖ ρ zc μ) (n : ℕ) :
    (∫⁻ t, weightedFactorialNormSq n ϖ zc ρ K
      (planeTimeAllMomentCarrierToLp K ϖ ρ zc μ f t) ∂μ) ≠ ⊤ :=
  planeTimeAllMoment_representative_moment K ϖ ρ zc μ f n

theorem planeTimeAllMomentCarrier_add (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ)
    (f g : PlaneTimeAllMomentCarrier (E := E) K ϖ ρ zc μ) :
    (fun t => planeTimeAllMomentCarrierToLp K ϖ ρ zc μ (f + g) t) =ᵐ[μ]
      fun t => planeTimeAllMomentCarrierToLp K ϖ ρ zc μ f t +
        planeTimeAllMomentCarrierToLp K ϖ ρ zc μ g t := by
  rw [map_add]
  exact Lp.coeFn_add _ _

theorem planeTimeAllMomentCarrier_smul (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ)
    (c : ℝ) (f : PlaneTimeAllMomentCarrier (E := E) K ϖ ρ zc μ) :
    (fun t => planeTimeAllMomentCarrierToLp K ϖ ρ zc μ (c • f) t) =ᵐ[μ]
      fun t => c • planeTimeAllMomentCarrierToLp K ϖ ρ zc μ f t := by
  rw [map_smul]
  exact Lp.coeFn_smul _ _

def planeTimeAllMomentCarrierLinearMap
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ)
    (T : X →ₗ[ℝ] Lp (PlaneHk Set.univ K E) 2 μ)
    (w : X → ℝ → PlaneHk Set.univ K E) (hw : ∀ x, MemLp (w x) 2 μ)
    (heq : ∀ x, (hw x).toLp (w x) = T x)
    (he : ∀ x n, (∫⁻ t, weightedFactorialNormSq n ϖ zc ρ K (w x t) ∂μ) ≠ ⊤) :
    X →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := E) K ϖ ρ zc μ :=
  planeTimeAllMomentLinearMap K ϖ ρ zc μ T w hw heq he

def PlaneTimeAllMomentRepresents (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ)
    (f : PlaneTimeAllMomentCarrier (E := E) K ϖ ρ zc μ)
    (w : ℝ → PlaneHk Set.univ K E) : Prop :=
  (fun t => planeTimeAllMomentCarrierToLp K ϖ ρ zc μ f t) =ᵐ[μ] w

theorem planeTimeAllMomentCarrierLinearMap_represents
    {X : Type*} [AddCommGroup X] [Module ℝ X]
    (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ)
    (T : X →ₗ[ℝ] Lp (PlaneHk Set.univ K E) 2 μ)
    (w : X → ℝ → PlaneHk Set.univ K E) (hw : ∀ x, MemLp (w x) 2 μ)
    (heq : ∀ x, (hw x).toLp (w x) = T x)
    (he : ∀ x n, (∫⁻ t, weightedFactorialNormSq n ϖ zc ρ K (w x t) ∂μ) ≠ ⊤)
    (x : X) :
    PlaneTimeAllMomentRepresents K ϖ ρ zc μ
      (planeTimeAllMomentCarrierLinearMap K ϖ ρ zc μ T w hw heq he x) (w x) := by
  change (fun t => T x t) =ᵐ[μ] w x
  rw [← heq x]
  exact (hw x).coeFn_toLp

end AVRegularity.CycleJointProofs
end
end
