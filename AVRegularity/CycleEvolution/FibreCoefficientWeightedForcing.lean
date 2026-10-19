-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.CellPeriodicSliceGraphFluxSlice
public import AVRegularity.CycleEvolution.FibreCoefficientConvolutionSum
import AVRegularity.CycleEvolution.CellTimeFourierConvergence
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Drift-independent forced energy inequality retaining both a value gap and gradient energy. -/

/-- The zero-shift source functional pairs scalar data with the value and flux with the gradient. -/
theorem cellSourceFunctional_unshifted (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2)
    (u : TorusHk 1 ℂ) :
    cellSourceFunctional 0 S F u = inner ℝ S (torusHkValueCLM u) -
      ∑ j : Fin 2, inner ℝ (F j) (cellDerivativeCLM j u) := by
  simp only [cellSourceFunctional, Pi.zero_apply, star_zero,
    show (fun _ : Fin 2 => (0 : ℂ)) = 0 from rfl, cellShiftedDerivative_zero,
    sub_apply, sum_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply]

/-- The actual mean-zero cell equation has a uniform forced spectral energy inequality. -/
theorem cellUnshifted_source_energy_bound {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : IsCellMetric G) {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (u : TorusHk 1 ℂ)
    (hm : cellMean (torusHkValueCLM u) = 0) (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    2 * (cellGeneratorForm ⟨G, v, 0, 0⟩ hG V hv.1 hb t u u + cellSourceFunctional 0 S F u) +
      Real.pi ^ 2 * ‖torusHkValueCLM u‖ ^ 2 + (1 / 2) * ∑ j, ‖cellDerivativeCLM j u‖ ^ 2 ≤
      ‖S‖ ^ 2 + 8 * ∑ j, ‖F j‖ ^ 2 := by
  have hg := cellMetricEnergy_coercive hG t u
  have hs := hilbertScalarSource_young S (torusHkValueCLM u)
  have hf := hilbertFluxSource_young F (fun j => cellDerivativeCLM j u)
  have hvsmall := cellMeanZero_value_small_gradient u hm
  have hgap := cellMeanZero_gradient_gap u hm
  rw [cellUnshiftedGenerator_drift_neutral hG hv, cellSourceFunctional_unshifted]
  linarith

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Genuine time integrability of complex pairings of the H1 dual and state curves. -/

theorem cellDualComplexPair_cross_intervalIntegrable {a b : ℝ} (hab : a ≤ b)
    {g z : ℝ → TorusHk 1 ℂ}
    (hg : MemLp g 2 (volume.restrict (Icc a b)))
    (hz : MemLp z 2 (volume.restrict (Icc a b))) :
    IntervalIntegrable (fun t => cellDualComplexPair (g t) (z t)) volume a b := by
  have hzi : MemLp (fun t => cellH1Scalar Complex.I (z t)) 2 (volume.restrict (Icc a b)) := by
    simpa only [Function.comp_def, cellH1ScalarCLM_apply] using
      (cellH1ScalarCLM Complex.I).comp_memLp' hz
  have h₁ := cellH1Pair_intervalIntegrable hab hg hz
  have h₂ := cellH1Pair_intervalIntegrable hab hg hzi
  apply intervalIntegrable_iff.mpr
  have he₁ := Complex.ofRealCLM.integrable_comp (intervalIntegrable_iff.mp h₁)
  have he₂ := (Complex.ofRealCLM.integrable_comp (intervalIntegrable_iff.mp h₂)).const_mul Complex.I
  exact he₁.add he₂

end AVRegularity.CycleEvolution
end

section
open Homogenization
namespace AVRegularity.CycleEvolution

/-! Complex linearity of the literal integrated cell integrand. -/

/-- Complex scaling commutes with the literal weak integrand. -/
theorem cellLiteralRHS_complex_smul (C : CellCoefficients) (t : ℝ) (r : ℂ)
    (u : Vec 2 → ℂ) (du : Fin 2 → Vec 2 → ℂ)
    (ψ : Vec 2 → ℂ) (dψ : Fin 2 → Vec 2 → ℂ)
    (src : Vec 2 → ℂ) (F : Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) (x : Vec 2) :
    cellLiteralRHS C t (r • u) (r • du) ψ dψ (r • src) (r • F) x =
      r • cellLiteralRHS C t u du ψ dψ src F x := by
  simp only [cellLiteralRHS, Fin.sum_univ_two, Pi.smul_apply, PiLp.smul_apply,
    smul_eq_mul]
  ring

/-! Actual weak integrands commute with absolutely convergent trial-data series. -/

/-- Summable pointwise trial data commute with the literal cell weak integrand. -/
theorem cellLiteralRHS_tsum_state {J : Type*} [Countable J]
    (C : CellCoefficients) (t : ℝ) (ψ : Vec 2 → ℂ) (dψ : Fin 2 → Vec 2 → ℂ)
    (x : Vec 2) (z : J → CellRHSState) (hs : Summable z) :
    cellLiteralRHS C t (fun _ => (∑' j, z j).1)
      (fun k _ => (∑' j, z j).2.1 k) ψ dψ
      (fun _ => (∑' j, z j).2.2.1) (fun _ => (∑' j, z j).2.2.2) x =
      ∑' j, cellLiteralRHS C t (fun _ => (z j).1) (fun k _ => (z j).2.1 k)
        ψ dψ (fun _ => (z j).2.2.1) (fun _ => (z j).2.2.2) x := by
  rw [← cellLiteralRHSCLM_apply]
  exact ((cellLiteralRHSCLM C t ψ dψ x).map_tsum hs).trans
    (tsum_congr (fun j => cellLiteralRHSCLM_apply C t ψ dψ x (z j)))

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The genuine mean-free projection preserves product-space L² source regularity. -/

/-- Mean-free source classes have the mean-free raw representatives on every L² slice. -/
theorem cellQ0_sourceSlice_ae (f : ℝ → Vec 2 → ℂ) (t : ℝ)
    (hf : MemLp (f t) 2 (volume.restrict AVenhance.unitCube)) :
    cellQ0CLM (cellSourceSlice f t) =ᵐ[volume.restrict AVenhance.unitCube] cellQ0 (f t) := by
  have hr := cellSourceSlice_ae f t hf
  have hm : cellMean (cellSourceSlice f t) = cellMean (f t) := integral_congr_ae hr
  filter_upwards [cellQ0CLM_ae (cellSourceSlice f t), hr] with x hx hf
  rw [hx]
  dsimp only [cellQ0]
  rw [hf, hm]

/-- Joint measurability and product L² membership survive the actual mean subtraction. -/
theorem cellQ0_memLp_product (I : Set ℝ) (f : ℝ → Vec 2 → ℂ)
    (hm : Measurable (Function.uncurry f))
    (hf : MemLp (Function.uncurry f) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    MemLp (Function.uncurry (fun t => cellQ0 (f t))) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) := by
  apply cellJoint_memLp_of_slices I (fun t => cellQ0 (f t))
    (cellQ0_measurable hm).aestronglyMeasurable
    (fun t => cellQ0CLM (cellSourceSlice f t))
    (cellQ0CLM.comp_memLp' (cellSourceSlice_memLp I f hf))
  filter_upwards [cellSource_memLp_slices I f hf] with t ht
  exact cellQ0_sourceSlice_ae f t ht

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Reconstructing the gradient from the actual mean and graph remainder. -/

theorem cellMeanRemainder_gradient_point_le (u ρ : TorusHk 1 ℂ) (A : ℂ)
    (M : ℝ) (hM : 0 ≤ M) (hA : ‖A‖ ≤ M) :
    (∑ j, ‖cellDerivativeCLM j u‖ ^ 2) ≤
      2 * M ^ 2 * (∑ j, ‖cellDerivativeCLM j ρ‖ ^ 2) +
        2 * ∑ j, ‖cellDerivativeCLM j (u - cellH1Scalar A (ρ + cellH1One))‖ ^ 2 := by
  have hj (j : Fin 2) : ‖cellDerivativeCLM j u‖ ^ 2 ≤
      2 * M ^ 2 * ‖cellDerivativeCLM j ρ‖ ^ 2 +
        2 * ‖cellDerivativeCLM j (u - cellH1Scalar A (ρ + cellH1One))‖ ^ 2 := by
    let z := u - cellH1Scalar A (ρ + cellH1One)
    have he : cellDerivativeCLM j u = cellScalarCLM A (cellDerivativeCLM j ρ) + cellDerivativeCLM j z := by
      dsimp only [z]
      rw [map_sub, cellH1Scalar_derivative, map_add, cellH1One_derivative, add_zero]
      abel
    have hn := norm_add_le (cellScalarCLM A (cellDerivativeCLM j ρ)) (cellDerivativeCLM j z)
    rw [← he, cellScalarCLM_norm] at hn
    have hsq := sq_le_sq₀ (norm_nonneg A) hM |>.mpr hA
    have hm := mul_le_mul_of_nonneg_right hsq (sq_nonneg ‖cellDerivativeCLM j ρ‖)
    have hnorm := norm_nonneg (cellDerivativeCLM j u)
    have ha := norm_nonneg A
    have hr := norm_nonneg (cellDerivativeCLM j ρ)
    have hz := norm_nonneg (cellDerivativeCLM j z)
    change ‖cellDerivativeCLM j u‖ ^ 2 ≤ 2 * M ^ 2 * ‖cellDerivativeCLM j ρ‖ ^ 2 +
      2 * ‖cellDerivativeCLM j z‖ ^ 2
    nlinarith [sq_nonneg (‖A‖ * ‖cellDerivativeCLM j ρ‖ - ‖cellDerivativeCLM j z‖)]
  calc
    _ ≤ ∑ j, (2 * M ^ 2 * ‖cellDerivativeCLM j ρ‖ ^ 2 +
        2 * ‖cellDerivativeCLM j (u - cellH1Scalar A (ρ + cellH1One))‖ ^ 2) :=
      Finset.sum_le_sum (fun j _ => hj j)
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

theorem cellMeanRemainder_gradient_integral_le {a b : ℝ} (hab : a ≤ b)
    (u ρ : ℝ → TorusHk 1 ℂ) (A : ℝ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hA : ∀ t ∈ Icc a b, ‖A t‖ ≤ M)
    (hu : MemLp u 2 (volume.restrict (Icc a b)))
    (hρ : MemLp ρ 2 (volume.restrict (Icc a b)))
    (hz : MemLp (fun t => u t - cellH1Scalar (A t) (ρ t + cellH1One)) 2
      (volume.restrict (Icc a b))) :
    (∫ t in a..b, ∑ j, ‖cellDerivativeCLM j (u t)‖ ^ 2) ≤
      2 * M ^ 2 * (∫ t in a..b, ∑ j, ‖cellDerivativeCLM j (ρ t)‖ ^ 2) +
        2 * ∫ t in a..b, ∑ j, ‖cellDerivativeCLM j
          (u t - cellH1Scalar (A t) (ρ t + cellH1One))‖ ^ 2 := by
  have hiu := cellTime_gradientSq_intervalIntegrable hab u hu
  have hiρ := cellTime_gradientSq_intervalIntegrable hab ρ hρ
  have hiz := cellTime_gradientSq_intervalIntegrable hab _ hz
  have hi := intervalIntegral.integral_mono_on hab hiu
    ((hiρ.const_mul (2 * M ^ 2)).add (hiz.const_mul 2))
    (fun t ht => cellMeanRemainder_gradient_point_le (u t) (ρ t) (A t) M hM (hA t ht))
  rw [intervalIntegral.integral_add (hiρ.const_mul _) (hiz.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
  exact hi

/-! Coordinate-uniform derivative identities and admissibility for literal metric-jet fluxes. -/

/-- The proper differentiated flux and principal coefficient derivative form the literal next flux. -/
theorem cellMetricJetFluxDerivative_add_principal
    (Gj : ℕ × ℕ → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (cj : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (α : ℕ × ℕ) (j : Fin 2) :
    cellMetricJetFluxDerivative Gj cj α (cellJetDirection j) +
      cellMetricFlux (Gj (cellJetDirection j)) (cj α) =
      cellMetricJetFlux Gj cj (α + cellJetDirection j) := by
  fin_cases j
  · simpa [cellJetDirection, Prod.add_def] using
      cellMetricJetFluxDerivative_first Gj cj α
  · simpa [cellJetDirection, Prod.add_def] using cellMetricJetFluxDerivative_second Gj cj α

/-- The differentiated proper flux inherits actual source admissibility from the next flux. -/
theorem cellMetricJetFluxDerivative_admissible
    (Gj : ℕ × ℕ → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (cj : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (α : ℕ × ℕ) (j : Fin 2)
    (hnext : cellUlNorm univ (cellMetricJetFlux Gj cj (α + cellJetDirection j)) < ⊤ ∧
      AEStronglyMeasurable (Function.uncurry (cellMetricJetFlux Gj cj (α + cellJetDirection j)))
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hG : cellMetricSupNorm (Gj (cellJetDirection j)) < ⊤ ∧
      Measurable (Function.uncurry (Gj (cellJetDirection j))))
    (hc : cellEnergyNorm univ (cj α) < ⊤)
    (hcm : ∀ a, AEStronglyMeasurable (fun p : ℝ × Vec 2 => cj α p.1 a p.2)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube))) :
    cellUlNorm univ (cellMetricJetFluxDerivative Gj cj α (cellJetDirection j)) < ⊤ ∧
      AEStronglyMeasurable (Function.uncurry (cellMetricJetFluxDerivative Gj cj α (cellJetDirection j)))
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) := by
  have he := eq_sub_iff_add_eq.mpr (cellMetricJetFluxDerivative_add_principal Gj cj α j)
  rw [he]
  have hm := cellMetricFlux_aestronglyMeasurable univ (Gj (cellJetDirection j)) (cj α) hG.2 hcm
  have hf := (cellMetricFlux_ul_bound univ (Gj (cellJetDirection j)) hG.1 hG.2 (cj α) hcm).trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) hG.1) hc)
  exact ⟨(cellUlNorm_sub univ _ _ hnext.2 hm).trans_lt
    (ENNReal.add_lt_top.mpr ⟨hnext.1, hf⟩), hnext.2.sub hm⟩

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Uniform control of finite weak-time primitives by Bochner Fourier differences. -/

/-- Average-time control of two finite primitives without assuming a full Hilbert trace. -/
theorem CellWeakTimeData.primitive_difference_average {a b : ℝ} (hab : a ≤ b)
    {slice g : ℝ → TorusHk 1 ℂ}
    {initial : Lp ℂ 2 (volume.restrict AVenhance.unitCube)}
    (h : CellWeakTimeData a b slice g initial) (N M : ℕ) :
    ∀ t ∈ Icc a b,
      (b - a) * ‖cellGalerkinValue N (cellDualPrimitive N a initial g t) -
        cellGalerkinValue M (cellDualPrimitive M a initial g t)‖ ^ 2 ≤
      ‖torusHkValueCLM (E := ℂ) (K := 1)‖ ^ 2 *
        (∫ s in a..b, ‖galerkinProj N (slice s) - galerkinProj M (slice s)‖ ^ 2) +
      4 * (b - a) * ∫ s in a..b, ‖g s‖ *
        ‖galerkinProj N (slice s) - galerkinProj M (slice s)‖ := by
  let u := fun t => cellGalerkinValue N (cellDualPrimitive N a initial g t) -
    cellGalerkinValue M (cellDualPrimitive M a initial g t)
  let du := fun t => cellGalerkinValue N (cellGalerkinDualMomentCLM N (g t)) -
    cellGalerkinValue M (cellGalerkinDualMomentCLM M (g t))
  let w := fun t => galerkinProj N (slice t) - galerkinProj M (slice t)
  have hw : MemLp w 2 (volume.restrict (Icc a b)) :=
    ((galerkinProj N).comp_memLp' h.state).sub ((galerkinProj M).comp_memLp' h.state)
  have hu := ((cellDualPrimitive_strongTime hab N initial g h.dual).map (cellGalerkinValue N)).sub
    ((cellDualPrimitive_strongTime hab M initial g h.dual).map (cellGalerkinValue M))
  have hwint := cellTime_normSq_intervalIntegrable hab hw
  have hprod : Integrable (fun t => ‖g t‖ * ‖w t‖) (volume.restrict (Icc a b)) :=
    memLp_one_iff_integrable.mp (h.dual.norm.mul hw.norm : MemLp _ 1 _)
  have hprodint : IntervalIntegrable (fun t => ‖g t‖ * ‖w t‖) volume a b := by
    apply intervalIntegrable_iff.mpr
    rw [uIoc_of_le hab]
    exact hprod.mono_measure (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)
  have hup : ∀ᵐ t ∂volume.restrict (Icc a b), u t = torusHkValueCLM (w t) := by
    filter_upwards [h.primitive_ae hab N, h.primitive_ae hab M] with t htN htM
    dsimp only [u, w]
    rw [htN, htM, map_sub]
    rfl
  have huc : ContinuousOn (fun t => ‖u t‖ ^ 2) (Icc a b) := by
    simpa only [uIcc_of_le hab] using hu.norm_sq_ac.continuousOn
  have hvbound : (∫ s in a..b, ‖u s‖ ^ 2) ≤
      ‖torusHkValueCLM (E := ℂ) (K := 1)‖ ^ 2 * ∫ s in a..b, ‖w s‖ ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_ae_restrict hab
      (huc.intervalIntegrable_of_Icc hab) (hwint.const_mul _)
    filter_upwards [hup] with t ht
    rw [ht]
    have hn := (torusHkValueCLM (E := ℂ) (K := 1)).le_opNorm (w t)
    nlinarith [norm_nonneg (torusHkValueCLM (w t)), norm_nonneg (w t),
      norm_nonneg (torusHkValueCLM (E := ℂ) (K := 1))]
  have hpbound : (∫ s in a..b, ‖2 * inner ℝ (u s) (du s)‖) ≤
      4 * ∫ s in a..b, ‖g s‖ * ‖w s‖ := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_ae_restrict hab hu.energy_integrable.norm
      (hprodint.const_mul 4)
    filter_upwards [h.primitive_difference_production hab N M] with t ht
    change ‖2 * inner ℝ (u t) (du t)‖ ≤ 4 * (‖g t‖ * ‖w t‖)
    simpa only [u, du, w, mul_assoc] using ht
  intro t ht
  have ha := hu.norm_sq_le_average hab t ht
  have hp := mul_le_mul_of_nonneg_left hpbound (sub_nonneg.mpr hab)
  dsimp only [u, du, w] at ha hvbound hp
  nlinarith

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Filter
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Product-space and Bochner distances of joint Fourier representatives agree. -/

/-- Joint finite Fourier realizations preserve their temporal L² distances exactly. -/
theorem cellJointFourier_distance (I : Set ℝ) (u : ℝ → ComplexCellL2)
    (hu : MemLp u 2 (volume.restrict I)) (N M : ℕ) :
    dist ((cellJointFourier_memLp I N u hu).toLp (Function.uncurry (cellJointFourier N u)))
      ((cellJointFourier_memLp I M u hu).toLp (Function.uncurry (cellJointFourier M u))) =
    dist (((cellVectorFourierProjection N).comp_memLp' hu).toLp
      (fun t => cellVectorFourierProjection N (u t)))
      (((cellVectorFourierProjection M).comp_memLp' hu).toLp
        (fun t => cellVectorFourierProjection M (u t))) := by
  rw [dist_eq_norm, dist_eq_norm]
  apply cellNorm_eq_of_square_eq
  rw [cellProduct_distance_sq_of_slices I _ _
    (cellJointFourier_memLp I N u hu) (cellJointFourier_memLp I M u hu)
    (fun t => cellVectorFourierProjection N (u t)) (fun t => cellVectorFourierProjection M (u t))
    (Filter.Eventually.of_forall (cellJointFourier_ae N u))
    (Filter.Eventually.of_forall (cellJointFourier_ae M u))]
  rw [← MemLp.toLp_sub, cellTimeL2_norm_sq_integral]
  rfl

end AVRegularity.CycleEvolution
end

section
open Homogenization
namespace AVRegularity.CycleEvolution

/-! The literal weak integrand commutes with summable value, gradient, source, and flux components. -/

/-- Absolute convergence of the four trial-data series identifies the summed weak integrand. -/
theorem cellLiteralRHS_tsum_components {J : Type*} [Countable J]
    (C : CellCoefficients) (t : ℝ) (ψ : Vec 2 → ℂ) (dψ : Fin 2 → Vec 2 → ℂ)
    (x : Vec 2) (u src : J → ℂ)
    (du F : J → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hu : Summable u) (hdu : Summable du) (hsrc : Summable src) (hF : Summable F) :
    cellLiteralRHS C t (fun _ => ∑' j, u j) (fun k _ => (∑' j, du j) k)
      ψ dψ (fun _ => ∑' j, src j) (fun _ => ∑' j, F j) x =
      ∑' j, cellLiteralRHS C t (fun _ => u j) (fun k _ => du j k)
        ψ dψ (fun _ => src j) (fun _ => F j) x := by
  let z := fun j => (u j, (du j, (src j, F j)))
  have hz : HasSum z ((∑' j, u j), ((∑' j, du j), ((∑' j, src j), (∑' j, F j)))) :=
    hu.hasSum.prodMk (hdu.hasSum.prodMk (hsrc.hasSum.prodMk hF.hasSum))
  have he := cellLiteralRHS_tsum_state C t ψ dψ x z hz.summable
  rw [hz.tsum_eq] at he
  exact he

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CycleEvolution

/-! The actual mean-free scalar source and its bounded Hilbert projection coincide. -/

/-- On every L² slice, the mean-free raw source class is the genuine Hilbert mean-free projection. -/
theorem cellQ0_sourceSlice_eq (f : ℝ → Vec 2 → ℂ) (t : ℝ)
    (hf : MemLp (f t) 2 (volume.restrict AVenhance.unitCube)) :
    cellSourceSlice (fun r => cellQ0 (f r)) t = cellQ0CLM (cellSourceSlice f t) := by
  apply Lp.ext
  exact (cellSourceSlice_ae (fun r => cellQ0 (f r)) t (cellQ0_memLp hf)).trans
    (cellQ0_sourceSlice_ae f t hf).symm

/-- The actual source classes satisfy the projection norm bound almost everywhere on L² intervals. -/
theorem cellQ0_sourceSlice_normSq_ae (I : Set ℝ) (f : ℝ → Vec 2 → ℂ)
    (hf : MemLp (Function.uncurry f) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    ∀ᵐ t ∂volume.restrict I,
      ‖cellSourceSlice (fun r => cellQ0 (f r)) t‖ ^ 2 ≤ 4 * ‖cellSourceSlice f t‖ ^ 2 := by
  filter_upwards [cellSource_memLp_slices I f hf] with t ht
  rw [cellQ0_sourceSlice_eq f t ht]
  have hn := cellQ0CLM_norm_le (cellSourceSlice f t)
  have hsq := mul_self_le_mul_self (norm_nonneg _) hn
  nlinarith [norm_nonneg (cellQ0CLM (cellSourceSlice f t)), norm_nonneg (cellSourceSlice f t)]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Spatial form identities for the literal raw cell jet and public H¹ tests. -/

/-- A raw trial jet representing an H¹ class has the exact integrable literal weak integrand. -/
theorem cellRawSpatial_equation (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (t : ℝ) (u : TorusHk 1 ℂ) (D : RawJet2 1 ℂ)
    (hD : ∀ a, (u.val a : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] D a)
    (ψ : TorusHkFunction 1 ℂ) (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2)
    (src : Vec 2 → ℂ) (flux : Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hS : (S : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] src)
    (hF : ∀ j, (F j : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] fun x => flux x j) :
    Integrable (cellLiteralRHS C t (D (valueIndex2 1)) (cellGradComp D)
      (ψ.jet (valueIndex2 1)) (fun j => ψ.jet ⟨⟨1, by decide⟩, fun _ => j⟩) src flux)
      (volume.restrict AVenhance.unitCube) ∧
    (∫ x in AVenhance.unitCube, cellLiteralRHS C t (D (valueIndex2 1)) (cellGradComp D)
      (ψ.jet (valueIndex2 1)) (fun j => ψ.jet ⟨⟨1, by decide⟩, fun _ => j⟩) src flux x) =
      cellDualComplexPair (cellDualDerivative C hG V hv hb t u S F) (cellRawTest ψ) := by
  have he := cellComplexSpatial_literal_ae C hG V hv hb t u (cellRawTest ψ) S F
    (D (valueIndex2 1)) (cellGradComp D) (ψ.jet (valueIndex2 1))
    (fun j => ψ.jet ⟨⟨1, by decide⟩, fun _ => j⟩) src flux (hD (valueIndex2 1))
    (fun j => hD ⟨⟨1, by decide⟩, fun _ => j⟩) (cellRawTest_value_ae ψ)
    (cellRawTest_derivative_ae ψ) hS hF
  refine ⟨(cellComplexSpatial_integrable C hG V hv hb t u _ S F).congr he, ?_⟩
  rw [← integral_congr_ae he, cellComplexSpatial_integral, ← cellDualComplexPair_actual]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization
namespace AVRegularity.CycleEvolution

/-! Addition of the public integrated weak equations. -/

/-- Addition preserves the integrated weak identity with summed forcing. -/
theorem cellWeakIdentity_add (C : CellCoefficients) (s t : ℝ)
    (u0 u1 w0 w1 ψ : Vec 2 → ℂ) (dψ : Fin 2 → Vec 2 → ℂ)
    (u w : ℝ → Vec 2 → ℂ) (du dw : ℝ → Fin 2 → Vec 2 → ℂ)
    (src src' : ℝ → Vec 2 → ℂ) (F F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (h : CellWeakIdentity C s t u0 u1 ψ dψ u du src F)
    (h' : CellWeakIdentity C s t w0 w1 ψ dψ w dw src' F') :
    CellWeakIdentity C s t (u0 + w0) (u1 + w1) ψ dψ (u + w) (du + dw) (src + src') (F + F') := by
  let μ := volume.restrict AVenhance.unitCube
  let R1 := fun r => cellLiteralRHS C r (u r) (du r) ψ dψ (src r) (F r)
  let R2 := fun r => cellLiteralRHS C r (w r) (dw r) ψ dψ (src' r) (F' r)
  let R0 := fun r => cellLiteralRHS C r (u r + w r) (du r + dw r) ψ dψ (src r + src' r) (F r + F' r)
  change Integrable (fun x => u1 x * ψ x) μ ∧ Integrable (fun x => u0 x * ψ x) μ ∧
    (∀ᵐ r ∂volume.restrict (Ioc s t), Integrable (R1 r) μ) ∧
    Integrable (fun r => ∫ x, R1 r x ∂μ) (volume.restrict (Ioc s t)) ∧
    (∫ x, u1 x * ψ x ∂μ) - (∫ x, u0 x * ψ x ∂μ) =
      ∫ r in Ioc s t, ∫ x, R1 r x ∂μ at h
  change Integrable (fun x => w1 x * ψ x) μ ∧ Integrable (fun x => w0 x * ψ x) μ ∧
    (∀ᵐ r ∂volume.restrict (Ioc s t), Integrable (R2 r) μ) ∧
    Integrable (fun r => ∫ x, R2 r x ∂μ) (volume.restrict (Ioc s t)) ∧
    (∫ x, w1 x * ψ x ∂μ) - (∫ x, w0 x * ψ x ∂μ) =
      ∫ r in Ioc s t, ∫ x, R2 r x ∂μ at h'
  change Integrable (fun x => (u1 x + w1 x) * ψ x) μ ∧
    Integrable (fun x => (u0 x + w0 x) * ψ x) μ ∧
    (∀ᵐ r ∂volume.restrict (Ioc s t), Integrable (R0 r) μ) ∧
    Integrable (fun r => ∫ x, R0 r x ∂μ) (volume.restrict (Ioc s t)) ∧
    (∫ x, (u1 x + w1 x) * ψ x ∂μ) - (∫ x, (u0 x + w0 x) * ψ x ∂μ) =
      ∫ r in Ioc s t, ∫ x, R0 r x ∂μ
  have heq (r : ℝ) : R0 r = R1 r + R2 r := by
    funext x
    exact cellLiteralRHS_add C r (u r) (w r) (du r) (dw r) ψ dψ (src r) (src' r) (F r) (F' r) x
  have hi0 : ∀ᵐ r ∂volume.restrict (Ioc s t), Integrable (R0 r) μ := by
    filter_upwards [h.2.2.1, h'.2.2.1] with r hr hr'
    rw [heq]
    exact hr.add hr'
  have hint : (fun r => ∫ x, R0 r x ∂μ) =ᵐ[volume.restrict (Ioc s t)]
      fun r => (∫ x, R1 r x ∂μ) + ∫ x, R2 r x ∂μ := by
    filter_upwards [h.2.2.1, h'.2.2.1] with r hr hr'
    rw [heq]
    exact integral_add hr hr'
  have ht0 := (h.2.2.2.1.add h'.2.2.2.1).congr hint.symm
  refine ⟨?_, ?_, hi0, ht0, ?_⟩
  · simpa only [Pi.add_def, add_mul] using h.1.add h'.1
  · simpa only [Pi.add_def, add_mul] using h.2.1.add h'.2.1
  · simp_rw [add_mul]
    rw [integral_add h.1 h'.1, integral_add h.2.1 h'.2.1, integral_congr_ae hint,
      integral_add h.2.2.2.1 h'.2.2.2.1, ← h.2.2.2.2, ← h'.2.2.2.2]
    ring

/-! Subtraction of public weak identities cancels arbitrary common forcing without separate L² assumptions. -/

/-- Common forcing cancels in the public integrated weak identity, using its actual integrability clauses. -/
theorem cellWeakIdentity_sub_same_source (C : CellCoefficients) (s t : ℝ)
    (u0 u1 w0 w1 ψ : Vec 2 → ℂ) (dψ : Fin 2 → Vec 2 → ℂ)
    (u w : ℝ → Vec 2 → ℂ) (du dw : ℝ → Fin 2 → Vec 2 → ℂ)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (h : CellWeakIdentity C s t u0 u1 ψ dψ u du src F)
    (h' : CellWeakIdentity C s t w0 w1 ψ dψ w dw src F) :
    CellWeakIdentity C s t (u0 - w0) (u1 - w1) ψ dψ (u - w) (du - dw) 0 0 := by
  let μ := volume.restrict AVenhance.unitCube
  let R1 := fun r => cellLiteralRHS C r (u r) (du r) ψ dψ (src r) (F r)
  let R2 := fun r => cellLiteralRHS C r (w r) (dw r) ψ dψ (src r) (F r)
  let R0 := fun r => cellLiteralRHS C r (u r - w r) (du r - dw r) ψ dψ 0 0
  change Integrable (fun x => u1 x * ψ x) μ ∧ Integrable (fun x => u0 x * ψ x) μ ∧
    (∀ᵐ r ∂volume.restrict (Ioc s t), Integrable (R1 r) μ) ∧
    Integrable (fun r => ∫ x, R1 r x ∂μ) (volume.restrict (Ioc s t)) ∧
    (∫ x, u1 x * ψ x ∂μ) - (∫ x, u0 x * ψ x ∂μ) =
      ∫ r in Ioc s t, ∫ x, R1 r x ∂μ at h
  change Integrable (fun x => w1 x * ψ x) μ ∧ Integrable (fun x => w0 x * ψ x) μ ∧
    (∀ᵐ r ∂volume.restrict (Ioc s t), Integrable (R2 r) μ) ∧
    Integrable (fun r => ∫ x, R2 r x ∂μ) (volume.restrict (Ioc s t)) ∧
    (∫ x, w1 x * ψ x ∂μ) - (∫ x, w0 x * ψ x ∂μ) =
      ∫ r in Ioc s t, ∫ x, R2 r x ∂μ at h'
  change Integrable (fun x => (u1 x - w1 x) * ψ x) μ ∧
    Integrable (fun x => (u0 x - w0 x) * ψ x) μ ∧
    (∀ᵐ r ∂volume.restrict (Ioc s t), Integrable (R0 r) μ) ∧
    Integrable (fun r => ∫ x, R0 r x ∂μ) (volume.restrict (Ioc s t)) ∧
    (∫ x, (u1 x - w1 x) * ψ x ∂μ) - (∫ x, (u0 x - w0 x) * ψ x ∂μ) =
      ∫ r in Ioc s t, ∫ x, R0 r x ∂μ
  have heq (r : ℝ) : R0 r = R1 r - R2 r := by
    funext x
    exact (cellLiteralRHS_sub_same_source C r (u r) (w r) (du r) (dw r) ψ dψ (src r) (F r) x).symm
  have hi0 : ∀ᵐ r ∂volume.restrict (Ioc s t), Integrable (R0 r) μ := by
    filter_upwards [h.2.2.1, h'.2.2.1] with r hr hr'
    rw [heq]
    exact hr.sub hr'
  have hint : (fun r => ∫ x, R0 r x ∂μ) =ᵐ[volume.restrict (Ioc s t)]
      fun r => (∫ x, R1 r x ∂μ) - ∫ x, R2 r x ∂μ := by
    filter_upwards [h.2.2.1, h'.2.2.1] with r hr hr'
    rw [heq]
    exact integral_sub hr hr'
  have ht0 := (h.2.2.2.1.sub h'.2.2.2.1).congr hint.symm
  refine ⟨?_, ?_, hi0, ht0, ?_⟩
  · simpa only [Pi.sub_def, sub_mul] using h.1.sub h'.1
  · simpa only [Pi.sub_def, sub_mul] using h.2.1.sub h'.2.1
  · simp_rw [sub_mul]
    rw [integral_sub h.1 h'.1, integral_sub h.2.1 h'.2.1, integral_congr_ae hint,
      integral_sub h.2.2.2.1 h'.2.2.2.1, ← h.2.2.2.2, ← h'.2.2.2.2]
    ring

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization Set
namespace AVRegularity.CycleEvolution

/-! Real scaling of the public integrated weak equation. -/

/-- Real scaling preserves the integrated weak identity with scaled forcing. -/
theorem cellWeakIdentity_smul (C : CellCoefficients) (s t r : ℝ)
    (u0 u1 ψ : Vec 2 → ℂ) (dψ : Fin 2 → Vec 2 → ℂ)
    (u : ℝ → Vec 2 → ℂ) (du : ℝ → Fin 2 → Vec 2 → ℂ)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (h : CellWeakIdentity C s t u0 u1 ψ dψ u du src F) :
    CellWeakIdentity C s t (r • u0) (r • u1) ψ dψ (r • u) (r • du) (r • src) (r • F) := by
  let μ := volume.restrict AVenhance.unitCube
  let R := fun τ => cellLiteralRHS C τ (u τ) (du τ) ψ dψ (src τ) (F τ)
  let R' := fun τ => cellLiteralRHS C τ (r • u τ) (r • du τ) ψ dψ (r • src τ) (r • F τ)
  change Integrable (fun x => u1 x * ψ x) μ ∧ Integrable (fun x => u0 x * ψ x) μ ∧
    (∀ᵐ τ ∂volume.restrict (Ioc s t), Integrable (R τ) μ) ∧
    Integrable (fun τ => ∫ x, R τ x ∂μ) (volume.restrict (Ioc s t)) ∧
    (∫ x, u1 x * ψ x ∂μ) - (∫ x, u0 x * ψ x ∂μ) =
      ∫ τ in Ioc s t, ∫ x, R τ x ∂μ at h
  change Integrable (fun x => (r • u1 x) * ψ x) μ ∧
    Integrable (fun x => (r • u0 x) * ψ x) μ ∧
    (∀ᵐ τ ∂volume.restrict (Ioc s t), Integrable (R' τ) μ) ∧
    Integrable (fun τ => ∫ x, R' τ x ∂μ) (volume.restrict (Ioc s t)) ∧
    (∫ x, (r • u1 x) * ψ x ∂μ) - (∫ x, (r • u0 x) * ψ x ∂μ) =
      ∫ τ in Ioc s t, ∫ x, R' τ x ∂μ
  have he (τ : ℝ) : R' τ = r • R τ := by
    funext x
    exact cellLiteralRHS_smul C τ r (u τ) (du τ) ψ dψ (src τ) (F τ) x
  have hi : ∀ᵐ τ ∂volume.restrict (Ioc s t), Integrable (R' τ) μ := by
    filter_upwards [h.2.2.1] with τ hτ
    rw [he]
    exact hτ.smul r
  have hint : (fun τ => ∫ x, R' τ x ∂μ) = fun τ => r • ∫ x, R τ x ∂μ := by
    funext τ
    rw [he]
    simp only [Pi.smul_apply, integral_smul]
  refine ⟨?_, ?_, hi, ?_, ?_⟩
  · simpa only [Pi.smul_def, smul_mul_assoc] using h.1.smul r
  · simpa only [Pi.smul_def, smul_mul_assoc] using h.2.1.smul r
  · rw [hint]
    exact h.2.2.2.1.smul r
  · simp_rw [smul_mul_assoc]
    rw [integral_smul, integral_smul, hint, integral_smul, ← h.2.2.2.2, smul_sub]

end AVRegularity.CycleEvolution
end

section
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! A quadratic majorant for weighted finite prefixes of the coefficient energies. -/

/-- The weighted energy in all Taylor coefficients of order at most `K`. -/
def fibreCoefficientWeightedPrefix (ρ : ℝ≥0∞) (E : ℕ × ℕ → ℝ≥0∞) (K : ℕ) : ℝ≥0∞ :=
  ∑ p ∈ jetIndices K, fibreCoefficientWeight ρ p * E p

/-- The triangular energy recurrence gives a scalar quadratic prefix majorant. -/
theorem fibreCoefficient_weighted_prefix_recurrence (ρ B : ℝ≥0∞)
    (E : ℕ × ℕ → ℝ≥0∞)
    (hE : ∀ p, E p ≤ 13 *
      ((∑ j ∈ fibreCoefficientDirections p, B *
        ((if p = cellJetDirection j then 1 else 0) + E (fibreCoefficientPrevious p j))) +
       (∑ j ∈ fibreCoefficientDirections p,
        ∑ a ∈ fibreCoefficientPairs (fibreCoefficientPrevious p j), B *
          E (fibreCoefficientComplement (fibreCoefficientPrevious p j) a) * E a) +
       (∑ j ∈ fibreCoefficientDirections p, 8 * E (fibreCoefficientPrevious p j))))
    (K : ℕ) :
    fibreCoefficientWeightedPrefix ρ E (K + 1) ≤
      (26 * ρ) * (B + (B + 8) * fibreCoefficientWeightedPrefix ρ E K +
        B * fibreCoefficientWeightedPrefix ρ E K ^ 2) := by
  let A := ∑ p ∈ jetIndices (K + 1), ∑ j ∈ fibreCoefficientDirections p,
    fibreCoefficientWeight ρ p * (if p = cellJetDirection j then 1 else 0)
  let L := ∑ p ∈ jetIndices (K + 1), ∑ j ∈ fibreCoefficientDirections p,
    fibreCoefficientWeight ρ p * E (fibreCoefficientPrevious p j)
  let Q := ∑ p ∈ jetIndices (K + 1), ∑ j ∈ fibreCoefficientDirections p,
    ∑ a ∈ fibreCoefficientPairs (fibreCoefficientPrevious p j),
      fibreCoefficientWeight ρ p * E (fibreCoefficientComplement (fibreCoefficientPrevious p j) a) * E a
  have hA : A ≤ 2 * ρ := fibreCoefficient_weighted_constant_le K ρ
  have hL : L ≤ (2 * ρ) * fibreCoefficientWeightedPrefix ρ E K :=
    fibreCoefficient_weighted_shift_le K ρ E
  have hQ : Q ≤ (2 * ρ) * fibreCoefficientWeightedPrefix ρ E K ^ 2 :=
    fibreCoefficient_weighted_convolution_le K ρ E
  calc
    _ ≤ ∑ p ∈ jetIndices (K + 1), fibreCoefficientWeight ρ p * (13 *
        ((∑ j ∈ fibreCoefficientDirections p, B *
          ((if p = cellJetDirection j then 1 else 0) + E (fibreCoefficientPrevious p j))) +
         (∑ j ∈ fibreCoefficientDirections p,
          ∑ a ∈ fibreCoefficientPairs (fibreCoefficientPrevious p j), B *
            E (fibreCoefficientComplement (fibreCoefficientPrevious p j) a) * E a) +
         (∑ j ∈ fibreCoefficientDirections p, 8 * E (fibreCoefficientPrevious p j)))) := by
      exact Finset.sum_le_sum (fun p _ => mul_le_mul' le_rfl (hE p))
    _ = 13 * (B * A + (B + 8) * L + B * Q) := by
      dsimp only [A, L, Q]
      simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add, add_mul]
      simp only [mul_assoc, mul_left_comm, mul_comm]
      ring
    _ ≤ 13 * (B * (2 * ρ) + (B + 8) * ((2 * ρ) * fibreCoefficientWeightedPrefix ρ E K) +
        B * ((2 * ρ) * fibreCoefficientWeightedPrefix ρ E K ^ 2)) := by
      exact mul_le_mul' le_rfl (add_le_add
        (add_le_add (mul_le_mul' le_rfl hA) (mul_le_mul' le_rfl hL))
        (mul_le_mul' le_rfl hQ))
    _ = _ := by ring

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The literal weak Bloch generator and its complex Hilbert adjoint. -/

theorem cellComplexGenerator_decomposition (C : CellCoefficients) (hG : IsCellMetric C.G)
    (V : ℝ) (hv : IsCellDrift C.v)
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (u z : TorusHk 1 ℂ) :
    cellComplexGenerator C hG V hv.1 hb t u z =
      cellComplexDiffusionForm hG C.θ t u z -
      cellComplexShiftedDriftForm C.v V hv hb C.θ t u z +
      cellComplexPair (cellScalarCLM (C.κ t) (torusHkValueCLM u)) (torusHkValueCLM z) := by
  rw [cellComplexShiftedDriftForm_eq_sum]
  rfl

theorem cellComplexGenerator_adjoint (C : CellCoefficients) (hG : IsCellMetric C.G)
    (V : ℝ) (hv : IsCellDrift C.v)
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (u z : TorusHk 1 ℂ) :
    cellComplexGenerator C hG V hv.1 hb t u z = star (
      cellComplexDiffusionForm hG (fun i => star (C.θ i)) t z u +
      cellComplexShiftedDriftForm C.v V hv hb (fun i => star (C.θ i)) t z u +
      cellComplexPair (cellScalarCLM (star (C.κ t)) (torusHkValueCLM z)) (torusHkValueCLM u)) := by
  rw [cellComplexGenerator_decomposition C hG V hv hb t u z, cellComplexDiffusionForm_adjoint,
    cellComplexShiftedDriftForm_adjoint, cellComplexPotential_adjoint]
  simp only [star_add, sub_neg_eq_add]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The Riesz time derivative represents the literal complex generator and forcing. -/

theorem cellDualComplexPair_derivative (C : CellCoefficients) (hG : IsCellMetric C.G)
    (V : ℝ) (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (u z : TorusHk 1 ℂ)
    (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    cellDualComplexPair (cellDualDerivative C hG V hv hb t u S F) z =
      cellComplexGenerator C hG V hv hb t u z + cellComplexSource C.θ S F z := by
  apply Complex.ext
  · rw [cellDualComplexPair_re, Complex.add_re, cellComplexGenerator_re,
      cellComplexSource_re, cellDualDerivative_pairing]
  · rw [cellDualComplexPair_im, Complex.add_im, cellComplexGenerator_im,
      cellComplexSource_im, cellDualDerivative_pairing]

theorem cellDualComplexPair_neg (g z : TorusHk 1 ℂ) :
    cellDualComplexPair (-g) z = -cellDualComplexPair g z := by
  apply Complex.ext
  · simp only [Complex.neg_re, cellDualComplexPair_re, inner_neg_left]
  · simp only [Complex.neg_im, cellDualComplexPair_im, inner_neg_left]

theorem cellComplexSource_zero (θ : Fin 2 → ℂ) (z : TorusHk 1 ℂ) :
    cellComplexSource θ 0 (fun _ => 0) z = 0 := by
  simp only [cellComplexSource, cellComplexPair_zero_left, Finset.sum_const_zero, sub_self]

end AVRegularity.CycleEvolution
end

section
open AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Complex scalar multiplication of the genuine H¹ Riesz representative has the expected dual action. -/

theorem cellH1Scalar_neg_one (u : TorusHk 1 ℂ) : cellH1Scalar (-1) u = -u := by
  rw [cellH1Scalar_real_imag]
  simp only [Complex.neg_re, Complex.one_re, Complex.neg_im, Complex.one_im, neg_zero,
    zero_smul, add_zero, neg_one_smul]

theorem cellDualComplexPair_scalar_left (c : ℂ) (g z : TorusHk 1 ℂ) :
    cellDualComplexPair (cellH1Scalar c g) z = c * cellDualComplexPair g z := by
  have hI : inner ℝ (cellH1Scalar Complex.I g) z = -inner ℝ g (cellH1Scalar Complex.I z) := by
    rw [cellH1Scalar_inner, show star Complex.I = -Complex.I from Complex.conj_I,
      cellH1Scalar_neg, inner_neg_right]
  have hII : inner ℝ (cellH1Scalar Complex.I g) (cellH1Scalar Complex.I z) = inner ℝ g z := by
    rw [cellH1Scalar_inner, show star Complex.I = -Complex.I from Complex.conj_I,
      cellH1Scalar_neg, cellH1Scalar_mul, Complex.I_mul_I, cellH1Scalar_neg_one, neg_neg]
  apply Complex.ext
  · rw [cellDualComplexPair_re, Complex.mul_re, cellDualComplexPair_re, cellDualComplexPair_im,
      cellH1Scalar_real_imag, inner_add_left, real_inner_smul_left, real_inner_smul_left, hI]
    ring
  · rw [cellDualComplexPair_im, Complex.mul_im, cellDualComplexPair_re, cellDualComplexPair_im,
      cellH1Scalar_real_imag, inner_add_left, real_inner_smul_left, real_inner_smul_left, hII]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Filter Homogenization
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Distances between joint Fourier representatives and arbitrary joint L² fields. -/

/-- A product field and its Bochner slices have the same distance from any finite cutoff. -/
theorem cellJointFourier_slice_distance (I : Set ℝ) (u : ℝ → ComplexCellL2)
    (hu : MemLp u 2 (volume.restrict I)) (N : ℕ)
    (P : Lp ℂ 2 ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    dist ((cellJointFourier_memLp I N u hu).toLp (Function.uncurry (cellJointFourier N u))) P =
    dist (((cellVectorFourierProjection N).comp_memLp' hu).toLp
      (fun t => cellVectorFourierProjection N (u t)))
      ((cellSourceSlice_memLp I (fun t x => P (t, x)) (Lp.memLp P)).toLp
        (cellSourceSlice (fun t x => P (t, x)))) := by
  rw [dist_eq_norm, dist_eq_norm]
  apply cellNorm_eq_of_square_eq
  have he := cellProduct_distance_sq_of_slices I (cellJointFourier N u) (fun t x => P (t, x))
    (cellJointFourier_memLp I N u hu)
    (Lp.memLp P) (fun t => cellVectorFourierProjection N (u t))
    (cellSourceSlice (fun t x => P (t, x)))
    (Filter.Eventually.of_forall (cellJointFourier_ae N u)) (by
      filter_upwards [cellSource_memLp_slices I (fun t x => P (t, x)) (Lp.memLp P)] with t ht
      exact cellSourceSlice_ae _ t ht)
  have hP : Function.uncurry (fun t x => P (t, x)) = (P : ℝ × Vec 2 → ℂ) := by
    funext p
    rfl
  simp only [hP, Lp.toLp_coeFn] at he
  rw [he, ← MemLp.toLp_sub, cellTimeL2_norm_sq_integral]
  rfl

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! A vanishing-tail bound uniform in time for finite weak-time primitives. -/

/-- Uniform finite-primitive differences are controlled by four vanishing temporal tails. -/
theorem CellWeakTimeData.primitive_difference_tail_bound {a b : ℝ} (hab : a ≤ b)
    {slice g : ℝ → TorusHk 1 ℂ}
    {initial : Lp ℂ 2 (volume.restrict AVenhance.unitCube)}
    (h : CellWeakTimeData a b slice g initial) (N M : ℕ) :
    ∀ t ∈ Icc a b,
      (b - a) * ‖cellGalerkinValue N (cellDualPrimitive N a initial g t) -
        cellGalerkinValue M (cellDualPrimitive M a initial g t)‖ ^ 2 ≤
      2 * ‖torusHkValueCLM (E := ℂ) (K := 1)‖ ^ 2 *
        ((∫ s in Icc a b, ‖galerkinProj N (slice s) - slice s‖ ^ 2) +
         (∫ s in Icc a b, ‖galerkinProj M (slice s) - slice s‖ ^ 2)) +
      4 * (b - a) *
        ((∫ s in Icc a b, ‖g s‖ * ‖galerkinProj N (slice s) - slice s‖) +
         (∫ s in Icc a b, ‖g s‖ * ‖galerkinProj M (slice s) - slice s‖)) := by
  obtain ⟨hs, hp⟩ := cellTime_fourier_difference_integrals h.state h.dual N M
  have hsb : (∫ s in a..b, ‖galerkinProj N (slice s) - galerkinProj M (slice s)‖ ^ 2) ≤
      2 * (∫ s in Icc a b, ‖galerkinProj N (slice s) - slice s‖ ^ 2) +
      2 * (∫ s in Icc a b, ‖galerkinProj M (slice s) - slice s‖ ^ 2) := by
    simpa only [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc] using hs
  have hpb : (∫ s in a..b, ‖g s‖ * ‖galerkinProj N (slice s) - galerkinProj M (slice s)‖) ≤
      (∫ s in Icc a b, ‖g s‖ * ‖galerkinProj N (slice s) - slice s‖) +
      (∫ s in Icc a b, ‖g s‖ * ‖galerkinProj M (slice s) - slice s‖) := by
    simpa only [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc] using hp
  intro t ht
  apply (h.primitive_difference_average hab N M t ht).trans
  have hs' := mul_le_mul_of_nonneg_left hsb (sq_nonneg
    ‖torusHkValueCLM (E := ℂ) (K := 1)‖)
  have hp' := mul_le_mul_of_nonneg_left hpb (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
    (sub_nonneg.mpr hab))
  convert add_le_add hs' hp' using 1; ring

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization Set
namespace AVRegularity.CycleEvolution

/-! Complex scaling of the public integrated weak equation. -/

/-- Complex scaling preserves the integrated weak identity with scaled forcing. -/
theorem cellWeakIdentity_complex_smul (C : CellCoefficients) (s t : ℝ) (r : ℂ)
    (u0 u1 ψ : Vec 2 → ℂ) (dψ : Fin 2 → Vec 2 → ℂ)
    (u : ℝ → Vec 2 → ℂ) (du : ℝ → Fin 2 → Vec 2 → ℂ)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (h : CellWeakIdentity C s t u0 u1 ψ dψ u du src F) :
    CellWeakIdentity C s t (r • u0) (r • u1) ψ dψ (r • u) (r • du) (r • src) (r • F) := by
  let μ := volume.restrict AVenhance.unitCube
  let R := fun τ => cellLiteralRHS C τ (u τ) (du τ) ψ dψ (src τ) (F τ)
  let R' := fun τ => cellLiteralRHS C τ (r • u τ) (r • du τ) ψ dψ (r • src τ) (r • F τ)
  change Integrable (fun x => u1 x * ψ x) μ ∧ Integrable (fun x => u0 x * ψ x) μ ∧
    (∀ᵐ τ ∂volume.restrict (Ioc s t), Integrable (R τ) μ) ∧
    Integrable (fun τ => ∫ x, R τ x ∂μ) (volume.restrict (Ioc s t)) ∧
    (∫ x, u1 x * ψ x ∂μ) - (∫ x, u0 x * ψ x ∂μ) =
      ∫ τ in Ioc s t, ∫ x, R τ x ∂μ at h
  change Integrable (fun x => (r • u1 x) * ψ x) μ ∧
    Integrable (fun x => (r • u0 x) * ψ x) μ ∧
    (∀ᵐ τ ∂volume.restrict (Ioc s t), Integrable (R' τ) μ) ∧
    Integrable (fun τ => ∫ x, R' τ x ∂μ) (volume.restrict (Ioc s t)) ∧
    (∫ x, (r • u1 x) * ψ x ∂μ) - (∫ x, (r • u0 x) * ψ x ∂μ) =
      ∫ τ in Ioc s t, ∫ x, R' τ x ∂μ
  have he (τ : ℝ) : R' τ = r • R τ := by
    funext x
    exact cellLiteralRHS_complex_smul C τ r (u τ) (du τ) ψ dψ (src τ) (F τ) x
  have hi : ∀ᵐ τ ∂volume.restrict (Ioc s t), Integrable (R' τ) μ := by
    filter_upwards [h.2.2.1] with τ hτ
    rw [he]
    exact hτ.smul r
  have hint : (fun τ => ∫ x, R' τ x ∂μ) = fun τ => r • ∫ x, R τ x ∂μ := by
    funext τ
    rw [he]
    simp only [Pi.smul_apply, integral_smul]
  refine ⟨?_, ?_, hi, ?_, ?_⟩
  · simpa only [Pi.smul_def, smul_mul_assoc] using h.1.smul r
  · simpa only [Pi.smul_def, smul_mul_assoc] using h.2.1.smul r
  · rw [hint]
    exact h.2.2.2.1.smul r
  · simp_rw [smul_mul_assoc]
    rw [integral_smul, integral_smul, hint, integral_smul, ← h.2.2.2.2, smul_sub]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Public cell solutions are invariant under joint null modifications of their forcing. -/

/-- Null changes in the forcing preserve the integrated weak identity. -/
theorem cellWeakIdentity_source_congr_sections (C : CellCoefficients) (s t : ℝ)
    (u0 u1 ψ : Vec 2 → ℂ) (dψ : Fin 2 → Vec 2 → ℂ)
    (u : ℝ → Vec 2 → ℂ) (du : ℝ → Fin 2 → Vec 2 → ℂ)
    (src src' : ℝ → Vec 2 → ℂ)
    (F F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hs : ∀ᵐ r ∂volume.restrict (Ioc s t),
      src r =ᵐ[volume.restrict AVenhance.unitCube] src' r)
    (hF : ∀ᵐ r ∂volume.restrict (Ioc s t),
      F r =ᵐ[volume.restrict AVenhance.unitCube] F' r)
    (h : CellWeakIdentity C s t u0 u1 ψ dψ u du src F) :
    CellWeakIdentity C s t u0 u1 ψ dψ u du src' F' := by
  let μ := volume.restrict AVenhance.unitCube
  let R := fun r => cellLiteralRHS C r (u r) (du r) ψ dψ (src r) (F r)
  let R' := fun r => cellLiteralRHS C r (u r) (du r) ψ dψ (src' r) (F' r)
  change Integrable (fun x => u1 x * ψ x) μ ∧ Integrable (fun x => u0 x * ψ x) μ ∧
    (∀ᵐ r ∂volume.restrict (Ioc s t), Integrable (R r) μ) ∧
    Integrable (fun r => ∫ x, R r x ∂μ) (volume.restrict (Ioc s t)) ∧
    (∫ x, u1 x * ψ x ∂μ) - (∫ x, u0 x * ψ x ∂μ) =
      ∫ r in Ioc s t, ∫ x, R r x ∂μ at h
  change Integrable (fun x => u1 x * ψ x) μ ∧ Integrable (fun x => u0 x * ψ x) μ ∧
    (∀ᵐ r ∂volume.restrict (Ioc s t), Integrable (R' r) μ) ∧
    Integrable (fun r => ∫ x, R' r x ∂μ) (volume.restrict (Ioc s t)) ∧
    (∫ x, u1 x * ψ x ∂μ) - (∫ x, u0 x * ψ x ∂μ) =
      ∫ r in Ioc s t, ∫ x, R' r x ∂μ
  have he : ∀ᵐ r ∂volume.restrict (Ioc s t), R r =ᵐ[μ] R' r := by
    filter_upwards [hs, hF]
      with r hsr hFr
    filter_upwards [hsr, hFr] with x hx hxF
    simp only [R, R', cellLiteralRHS, hx, hxF]
  have hint : (fun r => ∫ x, R r x ∂μ) =ᵐ[volume.restrict (Ioc s t)]
      fun r => ∫ x, R' r x ∂μ := he.mono fun r hr => integral_congr_ae hr
  refine ⟨h.1, h.2.1, ?_, h.2.2.2.1.congr hint, ?_⟩
  · filter_upwards [h.2.2.1, he] with r hr her
    exact hr.congr her
  · exact h.2.2.2.2.trans (integral_congr_ae hint)

/-- The full public solution predicate is invariant under null modifications of the sources. -/
theorem cellSolution_source_congr_sections (I : Set ℝ) (C : CellCoefficients)
    (src src' : ℝ → Vec 2 → ℂ)
    (F F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D : ℝ → RawJet2 1 ℂ)
    (hs : ∀ᵐ r ∂volume.restrict I,
      src r =ᵐ[volume.restrict AVenhance.unitCube] src' r)
    (hF : ∀ᵐ r ∂volume.restrict I,
      F r =ᵐ[volume.restrict AVenhance.unitCube] F' r)
    (h : IsCellSolution I C src F D) : IsCellSolution I C src' F' D := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2.1, ?_⟩
  intro s hsI t htI hst ψ
  have hsub : Ioc s t ⊆ I := fun r hr => h.1.out hsI htI ⟨hr.1.le, hr.2⟩
  have hm : volume.restrict (Ioc s t) ≤ volume.restrict I :=
    Measure.restrict_mono hsub le_rfl
  exact cellWeakIdentity_source_congr_sections C s t _ _ _ _ _ _ src src' F F'
    (ae_mono hm hs) (ae_mono hm hF) (h.2.2.2.2.2.2 s hsI t htI hst ψ)

end AVRegularity.CycleEvolution
end

section
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Induction for the scalar quadratic majorant of weighted Taylor energies. -/

/-- A small quadratic recurrence preserves the unit bound on every finite prefix. -/
theorem fibreCoefficient_prefix_majorant (ρ B : ℝ≥0∞)
    (S : ℕ → ℝ≥0∞) (hzero : S 0 = 0)
    (hstep : ∀ K, S (K + 1) ≤ (26 * ρ) * (B + (B + 8) * S K + B * S K ^ 2))
    (hsmall : (26 * ρ) * (3 * B + 8) ≤ 1) : ∀ K, S K ≤ 1 := by
  intro K
  induction K with
  | zero => rw [hzero]; exact zero_le
  | succ K ih =>
    apply (hstep K).trans
    calc
      _ ≤ (26 * ρ) * (B + (B + 8) * 1 + B * 1 ^ 2) := by
        exact mul_le_mul' le_rfl (add_le_add
          (add_le_add le_rfl (mul_le_mul' le_rfl ih))
          (mul_le_mul' le_rfl (pow_le_pow_left' ih 2)))
      _ = (26 * ρ) * (3 * B + 8) := by ring
      _ ≤ 1 := hsmall

end AVRegularity.CycleEvolution
end

section
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! The zeroth weighted prefix contains only the constant coefficient. -/

/-- A vanishing constant coefficient makes the zeroth weighted prefix vanish. -/
theorem fibreCoefficientWeightedPrefix_zero (ρ : ℝ≥0∞) (E : ℕ × ℕ → ℝ≥0∞)
    (hzero : E 0 = 0) : fibreCoefficientWeightedPrefix ρ E 0 = 0 := by
  unfold fibreCoefficientWeightedPrefix
  apply Finset.sum_eq_zero
  intro p hp
  have ho := (mem_jetIndices_iff 0 p).mp hp
  have he : p = 0 := by apply Prod.ext <;> simp only [Prod.fst_zero, Prod.snd_zero] <;> omega
  rw [he, hzero, mul_zero]

/-! Weighted coefficient forcing bounds from the actual state energy majorant. -/

/-- The linear and quadratic forcing coefficients have a weighted prefix bound. -/
theorem fibreCoefficient_weighted_forcing_prefix_le (ρ B : ℝ≥0∞)
    (E U : ℕ × ℕ → ℝ≥0∞)
    (hE : ∀ p, U p ≤
      ((∑ j ∈ fibreCoefficientDirections p, B *
        ((if p = cellJetDirection j then 1 else 0) + E (fibreCoefficientPrevious p j))) +
       (∑ j ∈ fibreCoefficientDirections p,
        ∑ a ∈ fibreCoefficientPairs (fibreCoefficientPrevious p j), B *
          E (fibreCoefficientComplement (fibreCoefficientPrevious p j) a) * E a) +
       (∑ j ∈ fibreCoefficientDirections p, 8 * E (fibreCoefficientPrevious p j))))
    (K : ℕ) :
    fibreCoefficientWeightedPrefix ρ U (K + 1) ≤
      (2 * ρ) * (B + (B + 8) * fibreCoefficientWeightedPrefix ρ E K +
        B * fibreCoefficientWeightedPrefix ρ E K ^ 2) := by
  let A := ∑ p ∈ jetIndices (K + 1), ∑ j ∈ fibreCoefficientDirections p,
    fibreCoefficientWeight ρ p * (if p = cellJetDirection j then 1 else 0)
  let L := ∑ p ∈ jetIndices (K + 1), ∑ j ∈ fibreCoefficientDirections p,
    fibreCoefficientWeight ρ p * E (fibreCoefficientPrevious p j)
  let Q := ∑ p ∈ jetIndices (K + 1), ∑ j ∈ fibreCoefficientDirections p,
    ∑ a ∈ fibreCoefficientPairs (fibreCoefficientPrevious p j),
      fibreCoefficientWeight ρ p * E (fibreCoefficientComplement (fibreCoefficientPrevious p j) a) * E a
  have hA : A ≤ 2 * ρ := fibreCoefficient_weighted_constant_le K ρ
  have hL : L ≤ (2 * ρ) * fibreCoefficientWeightedPrefix ρ E K :=
    fibreCoefficient_weighted_shift_le K ρ E
  have hQ : Q ≤ (2 * ρ) * fibreCoefficientWeightedPrefix ρ E K ^ 2 :=
    fibreCoefficient_weighted_convolution_le K ρ E
  calc
    _ ≤ ∑ p ∈ jetIndices (K + 1), fibreCoefficientWeight ρ p *
        ((∑ j ∈ fibreCoefficientDirections p, B *
          ((if p = cellJetDirection j then 1 else 0) + E (fibreCoefficientPrevious p j))) +
         (∑ j ∈ fibreCoefficientDirections p,
          ∑ a ∈ fibreCoefficientPairs (fibreCoefficientPrevious p j), B *
            E (fibreCoefficientComplement (fibreCoefficientPrevious p j) a) * E a) +
         (∑ j ∈ fibreCoefficientDirections p, 8 * E (fibreCoefficientPrevious p j))) := by
      exact Finset.sum_le_sum (fun p _ => mul_le_mul' le_rfl (hE p))
    _ = (B * A + (B + 8) * L + B * Q) := by
      dsimp only [A, L, Q]
      simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add, add_mul]
      simp only [mul_assoc, mul_left_comm, mul_comm]
      ring
    _ ≤ (B * (2 * ρ) + (B + 8) * ((2 * ρ) * fibreCoefficientWeightedPrefix ρ E K) +
        B * ((2 * ρ) * fibreCoefficientWeightedPrefix ρ E K ^ 2)) := by
      exact (add_le_add
        (add_le_add (mul_le_mul' le_rfl hA) (mul_le_mul' le_rfl hL))
        (mul_le_mul' le_rfl hQ))
    _ = _ := by ring

end AVRegularity.CycleEvolution
end
