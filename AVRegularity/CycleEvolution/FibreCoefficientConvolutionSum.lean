-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.CellMetricJetFluxDerivative
public import AVRegularity.CycleEvolution.FibreCoefficientLinearSeries
import AVRegularity.CoupledEnergy.Galerkin.PlainVariationalEnergy
import AVRegularity.CoupledEnergy.Variational.GradientTensorCLM
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Actual metric coercivity for arbitrary complex L² vector fields, including shifted gradients. -/

def cellMetricVectorEnergy {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : IsCellMetric G) (t : ℝ) (w : Fin 2 → ComplexCellL2) : ℝ :=
  ∑ j : Fin 2, ∑ k : Fin 2, inner ℝ (cellMetricEntryCLM hG t j k (w j)) (w k)

theorem cellMetricVectorEnergy_coercive {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : IsCellMetric G) (t : ℝ) (w : Fin 2 → ComplexCellL2) :
    (1 / 2) * ∑ j, ‖w j‖ ^ 2 ≤ cellMetricVectorEnergy hG t w := by
  let f := fun j k x => ((G t x j k : ℂ) * w j x *
    star (w k x)).re
  have hf (j k : Fin 2) := cellMetric_pairing_integrable hG t j k
    (w j) (w k)
  have hfs (j : Fin 2) : Integrable (fun x => ∑ k : Fin 2, f j k x)
      (volume.restrict AVenhance.unitCube) := by
    simpa only [Finset.sum_fn] using integrable_finsetSum' Finset.univ (fun k _ => hf j k)
  have hfss : Integrable (fun x => ∑ j : Fin 2, ∑ k : Fin 2, f j k x)
      (volume.restrict AVenhance.unitCube) := by
    simpa only [Finset.sum_fn] using integrable_finsetSum' Finset.univ (fun j _ => hfs j)
  have hd (j : Fin 2) := integrable_normSq_of_memLp (Lp.memLp (w j))
  have hds : Integrable (fun x => ∑ j : Fin 2, ‖w j x‖ ^ 2)
      (volume.restrict AVenhance.unitCube) := by
    simpa only [Finset.sum_fn] using integrable_finsetSum' Finset.univ (fun j _ => hd j)
  have h := integral_mono_ae (hds.const_mul (1 / 2)) hfss (Filter.Eventually.of_forall (fun x => by
    simpa only [f, Fin.sum_univ_two, Complex.add_re] using
      cellMetric_complex_coercive hG t x (fun j => w j x)))
  have hE : (∫ x in AVenhance.unitCube, ∑ j : Fin 2, ∑ k : Fin 2, f j k x) =
      cellMetricVectorEnergy hG t w := by
    rw [integral_finsetSum Finset.univ (fun j _ => hfs j)]
    unfold cellMetricVectorEnergy
    apply Finset.sum_congr rfl
    intro j _
    change (∫ x in AVenhance.unitCube, ∑ k : Fin 2, f j k x) = _
    rw [integral_finsetSum Finset.univ (fun k _ => hf j k)]
    apply Finset.sum_congr rfl
    intro k _
    exact (cellMetric_pairing_eq_integral hG t j k _ _).symm
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun j _ => hd j), hE] at h
  simp_rw [cellL2_norm_sq_integral] at h
  exact h

end AVRegularity.CycleEvolution
end

section
namespace AVRegularity.CycleEvolution

/-! Normalizing a small reversed graph loses only a fixed factor in its distance to the mean row. -/

theorem cellNormalizedRow_distance (A ρ : ComplexCellL2) (k : ℂ)
    (hk : ‖k‖ ≤ 2) (hρ : ‖ρ‖ ≤ 1)
    (hn : (1 + cellComplexPair ρ
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap A)) * k = 1) :
    ‖cellScalarCLM k (A + cellConstantCLM 1) - cellConstantCLM 1‖ ≤ 4 * ‖A‖ := by
  let d := cellComplexPair ρ (cellFiberCLM Complex.conjCLE.toContinuousLinearMap A)
  have hd : ‖d‖ ≤ ‖ρ‖ * ‖A‖ := by
    simpa only [cellFiberConj_norm] using cellComplexPair_norm_le ρ
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap A)
  have hkd : k - 1 = -d * k := by
    calc
      _ = k - (1 + d) * k := by rw [hn]
      _ = _ := by ring
  have hkm : ‖k - 1‖ ≤ 2 * ‖A‖ := by
    rw [hkd, norm_mul, norm_neg]
    calc
      _ ≤ (‖ρ‖ * ‖A‖) * 2 := mul_le_mul hd hk (norm_nonneg _) (by positivity)
      _ ≤ (1 * ‖A‖) * 2 := by gcongr
      _ = _ := by ring
  have he : cellScalarCLM k (A + cellConstantCLM 1) - cellConstantCLM 1 =
      k • A + (k - 1) • cellConstantCLM 1 := by
    simp only [cellScalarCLM_smul, smul_add, sub_smul, one_smul]
    abel
  rw [he]
  calc
    _ ≤ ‖k • A‖ + ‖(k - 1) • cellConstantCLM 1‖ := norm_add_le _ _
    _ = ‖k‖ * ‖A‖ + ‖k - 1‖ := by
      rw [norm_smul, norm_smul, cellConstantCLM_norm, norm_one, mul_one]
    _ ≤ 2 * ‖A‖ + 2 * ‖A‖ := add_le_add
      (mul_le_mul_of_nonneg_right hk (norm_nonneg _)) hkm
    _ = _ := by ring

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The sharp cell spectral gap loses only the explicitly quantified small mean. -/

theorem cellSmallMean_gradient_gap (u : TorusHk 1 ℂ) (δ : ℝ) (hδ : δ ≤ 1)
    (hm : ‖cellMeanCLM (torusHkValueCLM u)‖ ≤ δ * ‖torusHkValueCLM u‖) :
    (4 * Real.pi ^ 2) * (1 - δ) ^ 2 * ‖torusHkValueCLM u‖ ^ 2 ≤
      ∑ j, ‖cellDerivativeCLM j u‖ ^ 2 := by
  have hp := cellH1_meanFree_poincare u
  rw [← div_eq_inv_mul] at hp
  have hπ : 0 < 4 * Real.pi ^ 2 := by positivity
  have hgap := (le_div_iff₀ hπ).mp hp
  have hm2 := cellMeanFree_norm_sq_lower (torusHkValueCLM u) δ hδ hm
  have hmul := mul_le_mul_of_nonneg_left hm2 (le_of_lt hπ)
  nlinarith

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The constant-one graph mode has zero unshifted transport derivative. -/

theorem cellComplexDriftForm_add_one {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (u z : TorusHk 1 ℂ) :
    cellComplexDriftForm v V hv hb t (u + cellH1One) z = cellComplexDriftForm v V hv hb t u z := by
  rw [cellComplexDriftForm_eq_sum, cellComplexDriftForm_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_add, cellH1One_derivative, add_zero]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleEvolution

/-! Periodic weak derivative integration by parts on arbitrary H¹ cell classes. -/

theorem cellDerivative_projection_skew (j : Fin 2) (u z : TorusHk 1 ℂ) (N : ℕ) :
    inner ℝ (cellDerivativeCLM j (galerkinProj N u)) (torusHkValueCLM (galerkinProj N z)) =
      -inner ℝ (torusHkValueCLM (galerkinProj N u)) (cellDerivativeCLM j (galerkinProj N z)) := by
  let q := smoothFourierJet (L := 1) N u (valueIndex2 1)
  let r := smoothFourierJet (L := 1) N z (valueIndex2 1)
  have hi := periodic_hilbert_partial_ibp q r ((smoothFourierJet_contDiff N u _).of_le (by simp))
    ((smoothFourierJet_contDiff N z _).of_le (by simp)) (smoothFourierJet_periodic N u _)
    (smoothFourierJet_periodic N z _) j
  rw [L2.inner_def, L2.inner_def]
  have hl : (∫ x in AVenhance.unitCube,
      inner ℝ (cellDerivativeCLM j (galerkinProj N u) x)
        (torusHkValueCLM (galerkinProj N z) x)) =
      ∫ x in AVenhance.unitCube, inner ℝ (fderiv ℝ q x (basisVec j)) (r x) := by
    apply integral_congr_ae
    filter_upwards [galerkinProj_jet_ae_smooth N u ⟨⟨1, by decide⟩, fun _ => j⟩,
      galerkinProj_jet_ae_smooth N z (valueIndex2 1)] with x hu hz
    change cellDerivativeCLM j (galerkinProj N u) x = _ at hu
    change torusHkValueCLM (galerkinProj N z) x = _ at hz
    rw [hu, hz]
    have hd := smoothFourierJet_fderiv (L := 1) N u (0 : Fin 1) Fin.elim0 j x
    change fderiv ℝ q x (basisVec j) = _ at hd
    rw [hd]
    congr 1
  have hr : (∫ x in AVenhance.unitCube,
      inner ℝ (torusHkValueCLM (galerkinProj N u) x)
        (cellDerivativeCLM j (galerkinProj N z) x)) =
      ∫ x in AVenhance.unitCube, inner ℝ (q x) (fderiv ℝ r x (basisVec j)) := by
    apply integral_congr_ae
    filter_upwards [galerkinProj_jet_ae_smooth N u (valueIndex2 1),
      galerkinProj_jet_ae_smooth N z ⟨⟨1, by decide⟩, fun _ => j⟩] with x hu hz
    change torusHkValueCLM (galerkinProj N u) x = _ at hu
    change cellDerivativeCLM j (galerkinProj N z) x = _ at hz
    rw [hu, hz]
    have hd := smoothFourierJet_fderiv (L := 1) N z (0 : Fin 1) Fin.elim0 j x
    change fderiv ℝ r x (basisVec j) = _ at hd
    rw [hd]
    congr 1
  rw [hl, hr]
  exact hi

theorem cellDerivative_skew (j : Fin 2) (u z : TorusHk 1 ℂ) :
    inner ℝ (cellDerivativeCLM j u) (torusHkValueCLM z) =
      -inner ℝ (torusHkValueCLM u) (cellDerivativeCLM j z) := by
  have hu := galerkinProj_tendsto u
  have hz := galerkinProj_tendsto z
  have hl := ((cellDerivativeCLM j).continuous.continuousAt.tendsto.comp hu).inner (𝕜 := ℝ)
    (torusHkValueCLM.continuous.continuousAt.tendsto.comp hz)
  have hr := ((torusHkValueCLM.continuous.continuousAt.tendsto.comp hu).inner (𝕜 := ℝ)
    ((cellDerivativeCLM j).continuous.continuousAt.tendsto.comp hz)).neg
  have he : (fun N => inner ℝ (cellDerivativeCLM j (galerkinProj N u))
      (torusHkValueCLM (galerkinProj N z))) =
      (fun N => -inner ℝ (torusHkValueCLM (galerkinProj N u))
        (cellDerivativeCLM j (galerkinProj N z))) := by
    funext N
    exact cellDerivative_projection_skew j u z N
  change Tendsto (fun N => inner ℝ (cellDerivativeCLM j (galerkinProj N u))
    (torusHkValueCLM (galerkinProj N z))) atTop
    (𝓝 (inner ℝ (cellDerivativeCLM j u) (torusHkValueCLM z))) at hl
  rw [he] at hl
  exact tendsto_nhds_unique hl hr

end AVRegularity.CycleEvolution
end

section
open MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Fixed-test dual pairings preserve temporal L² on the genuine H¹ Riesz carrier. -/

def cellDualComplexPairCLM (z : TorusHk 1 ℂ) : TorusHk 1 ℂ →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (innerSL ℝ z) +
    (ContinuousLinearMap.lsmul ℝ ℂ Complex.I).comp
      (Complex.ofRealCLM.comp (innerSL ℝ (cellH1Scalar Complex.I z)))

theorem cellDualComplexPairCLM_apply (g z : TorusHk 1 ℂ) :
    cellDualComplexPairCLM z g = cellDualComplexPair g z := by
  simp only [cellDualComplexPairCLM, cellDualComplexPair, add_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, Complex.ofRealCLM_apply,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul, real_inner_comm]

theorem cellDualComplexPair_memLp {μ : Measure ℝ} (g : ℝ → TorusHk 1 ℂ)
    (hg : MemLp g 2 μ) (z : TorusHk 1 ℂ) :
    MemLp (fun t => cellDualComplexPair (g t) z) 2 μ := by
  simpa only [Function.comp_def, cellDualComplexPairCLM_apply] using
    (cellDualComplexPairCLM z).comp_memLp' hg

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.CycleEvolution

/-! The bilinear product rule in the actual uniformly local norm, without a Banach-space carrier. -/

/-- Norm-convergent coefficient and state quotients give the metric-gradient product derivative. -/
theorem cellMetricFlux_productRule_tendsto {P : Type*} (l : Filter P) (r : P → ℝ)
    (A : P → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (B C : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (E : P → ℝ → RawJet2 1 ℂ) (D T : ℝ → RawJet2 1 ℂ)
    (hA : ∀ p, cellMetricSupNorm (A p) < ⊤ ∧ Measurable (Function.uncurry (A p)))
    (hB : cellMetricSupNorm B < ⊤ ∧ Measurable (Function.uncurry B))
    (hC : cellMetricSupNorm C < ⊤ ∧ Measurable (Function.uncurry C))
    (hD : cellEnergyNorm univ D < ⊤)
    (hEm : ∀ p a, AEStronglyMeasurable (fun z : ℝ × Vec 2 => E p z.1 a z.2)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hDm : ∀ a, AEStronglyMeasurable (fun z : ℝ × Vec 2 => D z.1 a z.2)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hTm : ∀ a, AEStronglyMeasurable (fun z : ℝ × Vec 2 => T z.1 a z.2)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hAc : Tendsto (fun p => cellMetricSupNorm (r p • (A p - B) - C)) l (𝓝 0))
    (hEc : Tendsto (fun p => cellEnergyNorm univ (E p - D)) l (𝓝 0))
    (hEd : Tendsto (fun p => cellEnergyNorm univ (r p • (E p - D) - T)) l (𝓝 0)) :
    Tendsto (fun p => cellUlNorm univ
      (r p • (cellMetricFlux (A p) (E p) - cellMetricFlux B D) -
        (cellMetricFlux C D + cellMetricFlux B T))) l (𝓝 0) := by
  let Q := fun p => r p • (A p - B) - C
  let V := fun p => E p - D
  let W := fun p => r p • (E p - D) - T
  have hQ (p : P) : cellMetricSupNorm (Q p) < ⊤ ∧ Measurable (Function.uncurry (Q p)) := by
    have hsub := cellMetricSupNorm_sub_finite (A p) B (hA p).1 hB.1
    have hsmul := (cellMetricSupNorm_smul (r p) (A p - B)).trans_lt
      (ENNReal.mul_lt_top enorm_lt_top hsub)
    refine ⟨cellMetricSupNorm_sub_finite _ C hsmul hC.1, ?_⟩
    exact cellMetric_measurable_sub _ C
      (cellMetric_measurable_smul (r p) _
        (cellMetric_measurable_sub _ B (hA p).2 hB.2)) hC.2
  have hVm := fun p a => (hEm p a).sub (hDm a)
  have hWm := fun p a => ((hVm p a).const_smul (r p)).sub (hTm a)
  let S1 := fun p => cellMetricFlux (Q p) (E p)
  let S2 := fun p => cellMetricFlux C (V p)
  let S3 := fun p => cellMetricFlux B (W p)
  have h1 := cellMetricFlux_tendsto_zero_metric l Q E D hQ hD hEm hDm hAc hEc
  have h2 := cellMetricFlux_tendsto_zero_state l C V hC hVm hEc
  have h3 := cellMetricFlux_tendsto_zero_state l B W hB hWm hEd
  have hm1 := fun p => cellMetricFlux_aestronglyMeasurable univ (Q p) (E p) (hQ p).2 (hEm p)
  have hm2 := fun p => cellMetricFlux_aestronglyMeasurable univ C (V p) hC.2 (hVm p)
  have hm3 := fun p => cellMetricFlux_aestronglyMeasurable univ B (W p) hB.2 (hWm p)
  have h12 : Tendsto (fun p => cellUlNorm univ (S1 p + S2 p)) l (𝓝 0) := by
    simpa only [sub_zero, zero_add] using cellUlNorm_add_tendsto l S1 S2 0 0
      hm1 hm2 aestronglyMeasurable_zero aestronglyMeasurable_zero
      (by simpa only [sub_zero] using h1) (by simpa only [sub_zero] using h2)
  have h123 : Tendsto (fun p => cellUlNorm univ (S1 p + S2 p + S3 p)) l (𝓝 0) := by
    simpa only [sub_zero, zero_add] using cellUlNorm_add_tendsto l
      (fun p => S1 p + S2 p) S3 0 0 (fun p => (hm1 p).add (hm2 p)) hm3
      aestronglyMeasurable_zero aestronglyMeasurable_zero
      (by simpa only [sub_zero] using h12) (by simpa only [sub_zero] using h3)
  simpa only [cellMetricFlux_productRule_error, S1, S2, S3, Q, V, W] using h123

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Admissibility of every literal flux in a finite triangular raw jet family. -/

/-- Finite-order coefficient bounds and state regularity make every corresponding jet flux admissible. -/
theorem cellMetricJetFlux_admissible_of_order (K : ℕ)
    (Gj : ℕ × ℕ → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (cj : ℕ × ℕ → ℝ → RawJet2 1 ℂ)
    (hG : ∀ β : ℕ × ℕ, β.1 + β.2 ≤ K →
      cellMetricSupNorm (Gj β) < ⊤ ∧ Measurable (Function.uncurry (Gj β)))
    (hc : ∀ γ : ℕ × ℕ, γ.1 + γ.2 ≤ K →
      cellEnergyNorm univ (cj γ) < ⊤ ∧ ∀ a,
        AEStronglyMeasurable (fun p : ℝ × Vec 2 => cj γ p.1 a p.2)
          ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (α : ℕ × ℕ) (hα : α.1 + α.2 ≤ K) :
    cellUlNorm univ (cellMetricJetFlux Gj cj α) < ⊤ ∧
      AEStronglyMeasurable (Function.uncurry (cellMetricJetFlux Gj cj α))
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) := by
  have hβ (β : ℕ × ℕ) (hb : β ∈ cellJetFluxIndices α) :=
    (cellJetFluxIndices_metric_order hb).trans hα
  have hγ (β : ℕ × ℕ) (hb : β ∈ cellJetFluxIndices α) :=
    (Nat.le_of_lt (cellJetFluxIndices_lower_order hb)).trans hα
  exact ⟨cellMetricJetFlux_ul_lt_top Gj cj α
    (fun β hb => (hG β (hβ β hb)).1) (fun β hb => (hG β (hβ β hb)).2)
    (fun β hb => (hc (α.1 - β.1, α.2 - β.2) (hγ β hb)).1)
    (fun β hb => (hc (α.1 - β.1, α.2 - β.2) (hγ β hb)).2),
    cellMetricJetFlux_aestronglyMeasurable Gj cj α
      (fun β hb => (hG β (hβ β hb)).2)
      (fun β hb => (hc (α.1 - β.1, α.2 - β.2) (hγ β hb)).2)⟩

end AVRegularity.CycleEvolution
end

section
namespace AVRegularity.CycleEvolution

/-! A row close to the cell mean controls the mean of every element of its actual kernel. -/

theorem cellComplexPair_const_one (u : ComplexCellL2) :
    cellComplexPair u (cellConstantCLM 1) = cellMeanCLM u := by
  rw [cellComplexPair_eq_inner]
  rfl

theorem cellComplexPair_sub_right (u v z : ComplexCellL2) :
    cellComplexPair u (v - z) = cellComplexPair u v - cellComplexPair u z := by
  simp only [cellComplexPair_eq_inner, inner_sub_left]

theorem cellRow_kernel_mean_bound (ell u : ComplexCellL2) (δ : ℝ)
    (hδ : ‖ell - cellConstantCLM 1‖ ≤ δ)
    (hker : cellComplexPair u (cellFiberCLM Complex.conjCLE.toContinuousLinearMap ell) = 0) :
    ‖cellMeanCLM u‖ ≤ δ * ‖u‖ := by
  have hp : cellComplexPair u
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (ell - cellConstantCLM 1)) =
      -cellMeanCLM u := by
    rw [map_sub, cellFiberConj_constant, star_one, cellComplexPair_sub_right,
      hker, cellComplexPair_const_one, zero_sub]
  have hn := cellComplexPair_norm_le u
    (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (ell - cellConstantCLM 1))
  rw [hp, norm_neg, cellFiberConj_norm] at hn
  exact hn.trans (by
    rw [mul_comm δ ‖u‖]
    exact mul_le_mul_of_nonneg_left hδ (norm_nonneg u))

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Genuine constant weak Hilbert curves and addition of the constant-one graph mode. -/

theorem cellWeakHilbert_constant (a b : ℝ) (z : TorusHk 1 ℂ) :
    CellWeakHilbertCurve a b (fun _ => torusHkValueCLM z) (fun _ => z) (fun _ => 0) := by
  refine ⟨continuousOn_const, memLp_const z, memLp_const 0,
    Filter.Eventually.of_forall (fun _ => rfl), ?_⟩
  intro s hs t ht hst w
  simp only [sub_self, inner_zero_left, intervalIntegral.integral_zero]

theorem CellWeakHilbertCurve.add_one {a b : ℝ} {u : ℝ → ComplexCellL2}
    {slice g : ℝ → TorusHk 1 ℂ} (h : CellWeakHilbertCurve a b u slice g) :
    CellWeakHilbertCurve a b (fun t => u t + cellConstantCLM 1)
      (fun t => slice t + cellH1One) g := by
  have ha := h.add (cellWeakHilbert_constant a b cellH1One)
  simpa only [cellH1One_value, add_zero] using ha

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Genuine weak homogeneous trajectories reverse to backward trajectories of the pulled-back coefficients. -/

theorem CellWeakHilbertCurve.reverse_homogeneous {a b : ℝ}
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    {u : ℝ → ComplexCellL2} {slice : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice (fun t =>
      cellDualDerivative C hG V hv hb t (slice t) 0 0)) :
    CellWeakHilbertCurve (-b) (-a) (fun t => u (-t)) (fun t => slice (-t))
      (fun t => -cellDualDerivative (cellReverseTimeCoefficients C) (cellMetric_timeReverse hG) V
        (hv.comp ((measurable_neg.comp measurable_fst).prodMk measurable_snd))
        (fun s x => hb (-s) x) t (slice (-t)) 0 0) := by
  apply h.timeReverse.dual_congr
  exact Filter.Eventually.of_forall (fun t => congrArg Neg.neg
    (cellDualDerivative_reverse_time C hG V hv hb t (slice (-t)) 0 0).symm)

end AVRegularity.CycleEvolution
end

section
open AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Complex integration by parts for periodic H¹ cell fields. -/

theorem cellComplexDerivative_skew (j : Fin 2) (u z : TorusHk 1 ℂ) :
    cellComplexPair (cellDerivativeCLM j u) (torusHkValueCLM z) =
      -cellComplexPair (torusHkValueCLM u) (cellDerivativeCLM j z) := by
  apply Complex.ext
  · rw [Complex.neg_re, cellComplexPair_re, cellComplexPair_re]
    exact cellDerivative_skew j u z
  · rw [Complex.neg_im, cellComplexPair_im, cellComplexPair_im,
      ← cellH1Scalar_value, cellDerivative_skew j u (cellH1Scalar Complex.I z),
      cellH1Scalar_derivative]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Identification of the complex dual derivative with the actual cell forms. -/

/-- Real and imaginary fixed-test equations reconstruct the actual complex cell equation. -/
theorem cellDualComplexPair_actual (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (t : ℝ) (u z : TorusHk 1 ℂ) (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    cellDualComplexPair (cellDualDerivative C hG V hv hb t u S F) z =
      cellComplexGenerator C hG V hv hb t u z + cellComplexSource C.θ S F z := by
  apply Complex.ext
  · rw [cellDualComplexPair_re, Complex.add_re, cellComplexGenerator_re,
      cellComplexSource_re, cellDualDerivative_pairing]
  · rw [cellDualComplexPair_im, Complex.add_im, cellComplexGenerator_im,
      cellComplexSource_im, cellDualDerivative_pairing]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The actual near-identity metric gives sharp H¹ diffusion coercivity after spatial integration. -/

theorem cellMetricEnergy_near_identity_coercive {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : IsCellMetric G) {g : ℝ} (hg : IsMetricNearIdentity G g) (t : ℝ) (u : TorusHk 1 ℂ) :
    (1 - g) * ∑ j, ‖cellDerivativeCLM j u‖ ^ 2 ≤ cellMetricEnergy hG t u := by
  let f := fun j k x => ((G t x j k : ℂ) * cellDerivativeCLM j u x *
    star (cellDerivativeCLM k u x)).re
  have hf (j k : Fin 2) := cellMetric_pairing_integrable hG t j k
    (cellDerivativeCLM j u) (cellDerivativeCLM k u)
  have hfs (j : Fin 2) : Integrable (fun x => ∑ k : Fin 2, f j k x)
      (volume.restrict AVenhance.unitCube) := by
    simpa only [Finset.sum_fn] using integrable_finsetSum' Finset.univ (fun k _ => hf j k)
  have hfss : Integrable (fun x => ∑ j : Fin 2, ∑ k : Fin 2, f j k x)
      (volume.restrict AVenhance.unitCube) := by
    simpa only [Finset.sum_fn] using integrable_finsetSum' Finset.univ (fun j _ => hfs j)
  have hd (j : Fin 2) := integrable_normSq_of_memLp (Lp.memLp (cellDerivativeCLM j u))
  have hds : Integrable (fun x => ∑ j : Fin 2, ‖cellDerivativeCLM j u x‖ ^ 2)
      (volume.restrict AVenhance.unitCube) := by
    simpa only [Finset.sum_fn] using integrable_finsetSum' Finset.univ (fun j _ => hd j)
  have h := integral_mono_ae (hds.const_mul (1 - g)) hfss (Filter.Eventually.of_forall (fun x => by
    simpa only [f, cellMetricPairing, Fin.sum_univ_two, Complex.add_re] using
      cellMetric_complex_near_identity_coercive hg t x (fun j => cellDerivativeCLM j u x)))
  have hE : (∫ x in AVenhance.unitCube, ∑ j : Fin 2, ∑ k : Fin 2, f j k x) =
      cellMetricEnergy hG t u := by
    rw [integral_finsetSum Finset.univ (fun j _ => hfs j)]
    unfold cellMetricEnergy
    apply Finset.sum_congr rfl
    intro j _
    change (∫ x in AVenhance.unitCube, ∑ k : Fin 2, f j k x) = _
    rw [integral_finsetSum Finset.univ (fun k _ => hf j k)]
    apply Finset.sum_congr rfl
    intro k _
    exact (cellMetric_pairing_eq_integral hG t j k _ _).symm
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun j _ => hd j), hE] at h
  simp_rw [cellL2_norm_sq_integral] at h
  exact h

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization
namespace AVRegularity.CycleEvolution

/-! Fubini norm identities for jointly L² cell representatives. -/

/-- The norm-square identity for a Hilbert-valued L² function on an arbitrary measure space. -/
theorem cellL2_normSq_generic {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure α}
    (f : α → E) (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

/-- The product L² norm equals the norm of its Bochner spatial-class curve. -/
theorem cellProduct_norm_sq (I : Set ℝ) (f : ℝ → Vec 2 → ℂ)
    (hf : MemLp (Function.uncurry f) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    ‖hf.toLp (Function.uncurry f)‖ ^ 2 =
      ‖(cellSourceSlice_memLp I f hf).toLp (cellSourceSlice f)‖ ^ 2 := by
  rw [cellL2_normSq_generic _ hf,
    cellTimeL2_norm_sq_integral]
  have hi : Integrable (fun p : ℝ × Vec 2 => ‖f p.1 p.2‖ ^ 2)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) := by
    simpa only [Function.uncurry_def] using hf.norm.integrable_sq
  simp only [Function.uncurry_def]
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [cellSource_memLp_slices I f hf] with t ht
  simp only [cellSourceSlice, dite_eq_left ht]
  exact (AVRegularity.Sobolev.normSq_toLp_eq_integral ht).symm

/-- For any prescribed spatial classes represented by a joint L² field, Fubini reads their norm. -/
theorem cellProduct_norm_sq_of_slices (I : Set ℝ) (f : ℝ → Vec 2 → ℂ)
    (hf : MemLp (Function.uncurry f) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)))
    (u : ℝ → ComplexCellL2)
    (hu : ∀ᵐ t ∂volume.restrict I, (u t : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] f t) :
    ‖hf.toLp (Function.uncurry f)‖ ^ 2 = ∫ t in I, ‖u t‖ ^ 2 := by
  rw [cellProduct_norm_sq I f hf, cellTimeL2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [cellSource_memLp_slices I f hf, hu] with t ht hut
  have he : cellSourceSlice f t = u t := Lp.ext ((cellSourceSlice_ae f t ht).trans hut.symm)
  rw [he]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! A continuous trace budget and the actual gradient energy control the full Bochner H1 state. -/

theorem cellWeakH1_integral_budget {a b : ℝ} (hab : a ≤ b)
    (u : ℝ → ComplexCellL2) (slice g : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice g) (W G : ℝ)
    (htrace : ∀ t ∈ Icc a b, ‖u t‖ ^ 2 ≤ W)
    (hgradient : (∫ t in a..b, ∑ j, ‖cellDerivativeCLM j (slice t)‖ ^ 2) ≤ G) :
    (∫ t in a..b, ‖slice t‖ ^ 2) ≤ (b - a) * W + G := by
  have hv : MemLp (fun t => torusHkValueCLM (slice t)) 2 (volume.restrict (Icc a b)) :=
    (torusHkValueCLM (K := 1) (E := ℂ)).comp_memLp' h.state
  have hi := cellTime_normSq_intervalIntegrable hab hv
  have hg := cellTime_gradientSq_intervalIntegrable hab slice h.state
  have hval : (∫ t in a..b, ‖torusHkValueCLM (slice t)‖ ^ 2) ≤ (b - a) * W := by
    have hl := intervalIntegral.integral_mono_ae_restrict hab hi
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => W) volume a b) (by
        filter_upwards [h.agrees, ae_restrict_mem measurableSet_Icc] with t ht hI
        rw [← ht]
        exact htrace t hI)
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using hl
  simp_rw [cellH1_norm_sq]
  rw [intervalIntegral.integral_add hi hg]
  exact add_le_add hval hgradient

end AVRegularity.CycleEvolution
end

section
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! Extended-real factorial weights preserve the exact positive convolution identity. -/

/-- Factorial weights are nonnegative for nonnegative radii. -/
theorem cellJetWeightReal_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) (α : ℕ × ℕ) :
    0 ≤ cellJetWeightReal ρ α := by
  unfold cellJetWeightReal
  positivity

/-- The positive extended-real factorial weights cancel the binomial factors exactly. -/
theorem cellJetWeight_choose {ρ : ℝ} (hρ : 0 ≤ ρ) (α β : ℕ × ℕ) (hβ : β ≤ α) :
    ENNReal.ofReal (cellJetWeightReal ρ α) * (cellJetChoose α β : ℝ≥0∞) =
      ENNReal.ofReal (cellJetWeightReal ρ β) *
        ENNReal.ofReal (cellJetWeightReal ρ (α.1 - β.1, α.2 - β.2)) := by
  calc
    _ = ENNReal.ofReal (cellJetWeightReal ρ α * (cellJetChoose α β : ℝ)) := by
      rw [ENNReal.ofReal_mul (cellJetWeightReal_nonneg hρ α), ENNReal.ofReal_natCast]
    _ = ENNReal.ofReal (cellJetWeightReal ρ β * cellJetWeightReal ρ (α.1 - β.1, α.2 - β.2)) :=
      congrArg ENNReal.ofReal (cellJetWeightReal_choose ρ α β hβ)
    _ = _ := ENNReal.ofReal_mul (cellJetWeightReal_nonneg hρ β)

/-- Summed binomial factorial convolutions obey the product of the two literal factorial sums. -/
theorem factorialJetConvolution_le_product {ρ : ℝ} (hρ : 0 ≤ ρ)
    (K : ℕ) (a b : ℕ × ℕ → ℝ≥0∞) :
    (∑ α ∈ jetIndices K, ENNReal.ofReal (cellJetWeightReal ρ α) *
      ∑ β ∈ cellJetFluxIndices α, (cellJetChoose α β : ℝ≥0∞) * a β *
        b (α.1 - β.1, α.2 - β.2)) ≤
      factorialJetSum ((jetIndices K).erase 0) ρ a * factorialJetSum (jetIndices K) ρ b := by
  have heq (α : ℕ × ℕ) : ENNReal.ofReal (cellJetWeightReal ρ α) *
      (∑ β ∈ cellJetFluxIndices α, (cellJetChoose α β : ℝ≥0∞) * a β *
        b (α.1 - β.1, α.2 - β.2)) =
      ∑ β ∈ cellJetFluxIndices α,
        (ENNReal.ofReal (cellJetWeightReal ρ β) * a β) *
          (ENNReal.ofReal (cellJetWeightReal ρ (α.1 - β.1, α.2 - β.2)) *
            b (α.1 - β.1, α.2 - β.2)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro β hb
    have hm := cellJetFluxIndices_mem hb
    have hle : β ≤ α := ⟨hm.1, hm.2.1⟩
    rw [← mul_assoc, ← mul_assoc, cellJetWeight_choose hρ α β hle]
    ac_rfl
  simp_rw [heq]
  exact cellJetConvolution_le_product K
    (fun β => ENNReal.ofReal (cellJetWeightReal ρ β) * a β)
    (fun γ => ENNReal.ofReal (cellJetWeightReal ρ γ) * b γ)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Literal conjugation symmetry of the actual Bloch generator at minus conjugate frequency. -/

def cellConjugateCoefficients (C : CellCoefficients) : CellCoefficients :=
  ⟨C.G, C.v, fun j => -star (C.θ j), fun t => star (C.κ t)⟩

theorem cellH1Conj_shift_star (θ : Fin 2 → ℂ) (u : TorusHk 1 ℂ) (j : Fin 2) :
    cellShiftedDerivativeCLM (fun k => -θ k) j (cellH1Conj u) =
      cellFiberCLM Complex.conjCLE.toContinuousLinearMap
        (cellShiftedDerivativeCLM (fun k => star (θ k)) j u) := by
  simpa only [star_star] using cellH1Conj_shift (fun k => star (θ k)) u j

theorem cellComplexGenerator_conjugate (C : CellCoefficients) (hG : IsCellMetric C.G)
    (V : ℝ) (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (u z : TorusHk 1 ℂ) :
    cellComplexGenerator (cellConjugateCoefficients C) hG V hv hb t
      (cellH1Conj u) (cellH1Conj z) = star (cellComplexGenerator C hG V hv hb t u z) := by
  simp only [cellComplexGenerator, cellConjugateCoefficients, star_neg, star_star,
    cellH1Conj_shift, cellH1Conj_shift_star, cellH1Conj_value,
    cellMetricEntryCLM_conjugate, cellDriftEntryCLM_conjugate,
    ← cellFiberConj_scalar, cellComplexPair_conjugate, Fin.sum_univ_two,
    star_add, star_sub]
  rfl

/-! Actual conjugation is an isometry and its own real Hilbert adjoint on periodic H¹. -/

theorem cellH1Conj_jet (u : TorusHk 1 ℂ) (a : JetIndex2 1) :
    (cellH1Conj u).val a = cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u.val a) := by
  apply Lp.ext
  exact (cellH1Conj_jet_ae u a).trans (cellFiberConj_ae _).symm

theorem cellH1Conj_inner_both (u z : TorusHk 1 ℂ) :
    inner ℝ (cellH1Conj u) (cellH1Conj z) = inner ℝ u z := by
  change inner ℝ (cellH1Conj u).val (cellH1Conj z).val = inner ℝ u.val z.val
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [cellH1Conj_jet, cellH1Conj_jet, ← cellComplexPair_re, cellComplexPair_conjugate]
  simp only [Complex.star_def, Complex.conj_re, cellComplexPair_re]

theorem cellH1Conj_inner (u z : TorusHk 1 ℂ) :
    inner ℝ (cellH1Conj u) z = inner ℝ u (cellH1Conj z) := by
  have h := cellH1Conj_inner_both u (cellH1Conj z)
  rwa [cellH1Conj_involutive] at h

theorem cellH1Conj_scalar (c : ℂ) (u : TorusHk 1 ℂ) :
    cellH1Conj (cellH1Scalar c u) = cellH1Scalar (star c) (cellH1Conj u) := by
  apply TorusHk.ext_value
  change torusHkValueCLM (cellH1Conj (cellH1Scalar c u)) =
    torusHkValueCLM (cellH1Scalar (star c) (cellH1Conj u))
  simp only [cellH1Conj_value, cellH1Scalar_value, cellFiberConj_scalar]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Time readouts of the complete carrier coincide with actual solution representatives almost everywhere. -/

theorem cellFiniteEnergyTimeStateCLM_ae {a b : ℝ} (hab : a ≤ b)
    (u : ℝ → ComplexCellL2) (slice g : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice g) (z : CellFiniteEnergyCarrier a b)
    (hz : ∀ t : CellCompactTime a b, z.val.1 t = u t.val) :
    ∀ᵐ t ∂volume.restrict (Icc a b),
      cellComplexH1RealEquiv (cellFiniteEnergyTimeStateCLM hab z t) = slice t := by
  have hp := cellCompactTimeProjection_measurePreserving hab
  have hs := cellFiniteEnergyCarrier_state_eq u slice g h z hz
  have hr := Lp.coeFn_compMeasurePreserving z.val.2 hp
  filter_upwards [hr, hp.quasiMeasurePreserving.ae hs, ae_restrict_mem measurableSet_Icc]
    with t ht hs' hmem
  change cellComplexH1RealEquiv (Lp.compMeasurePreserving (projIcc a b hab) hp z.val.2 t) = slice t
  rw [ht]
  change cellComplexH1RealEquiv (z.val.2 (projIcc a b hab t)) = slice t
  simpa only [projIcc_of_mem hab hmem] using hs'

theorem cellFiniteEnergyTimeValueCLM_ae {a b : ℝ} (hab : a ≤ b)
    (u : ℝ → ComplexCellL2) (slice g : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice g) (z : CellFiniteEnergyCarrier a b)
    (hz : ∀ t : CellCompactTime a b, z.val.1 t = u t.val) :
    cellFiniteEnergyTimeValueCLM hab z =ᵐ[volume.restrict (Icc a b)] u := by
  have hv := cellComplexH1ValueCLM.coeFn_compLpL (cellFiniteEnergyTimeStateCLM hab z)
  have hs := cellFiniteEnergyTimeStateCLM_ae hab u slice g h z hz
  filter_upwards [hv, hs, h.agrees] with t hv' hs' ha
  change cellComplexH1ValueCLM.compLpL 2 (volume.restrict (Icc a b))
    (cellFiniteEnergyTimeStateCLM hab z) t = u t
  rw [hv', cellComplexH1ValueCLM_eq, hs']
  exact ha.symm

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Filter Homogenization
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Jointly L² finite Fourier representatives of Bochner spatial-class curves. -/

/-- A finite separated-variable representative of the cell Fourier cutoff. -/
def cellJointFourier (N : ℕ) (u : ℝ → ComplexCellL2) (t : ℝ) (x : Vec 2) : ℂ :=
  ∑ i : VectorFourierIndex N ℂ, inner ℝ (u t) (cellFourierMode N i) • cellFourierMode N i x

/-- Every finite Fourier field is jointly square integrable. -/
theorem cellJointFourier_memLp (I : Set ℝ) (N : ℕ) (u : ℝ → ComplexCellL2)
    (hu : MemLp u 2 (volume.restrict I)) :
    MemLp (Function.uncurry (cellJointFourier N u)) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) := by
  apply memLp_finsetSum Finset.univ
  intro i _
  apply cellTensor_memLp (E := ℂ) (μ := volume.restrict I)
    (ν := volume.restrict AVenhance.unitCube)
    (f := fun t => inner ℝ (u t) (cellFourierMode N i))
    (g := fun x => cellFourierMode N i x)
  · have hm := (innerSL ℝ (cellFourierMode N i)).comp_memLp' hu
    convert hm using 1
    funext t
    exact real_inner_comm _ _
  · exact Lp.memLp _

/-- Each time slice represents precisely the Fourier projection of the spatial class. -/
theorem cellJointFourier_ae (N : ℕ) (u : ℝ → ComplexCellL2) (t : ℝ) :
    (cellVectorFourierProjection N (u t) : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      cellJointFourier N u t := by
  rw [cellFourierProjection_eq_sum]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
      (fun i => inner ℝ (u t) (cellFourierMode N i) • cellFourierMode N i),
    ae_all_iff.mpr (fun i : VectorFourierIndex N ℂ =>
      Lp.coeFn_smul (inner ℝ (u t) (cellFourierMode N i)) (cellFourierMode N i))]
    with x hx hs
  rw [hx]
  simp only [Finset.sum_apply, cellJointFourier]
  exact Finset.sum_congr rfl (fun i _ => hs i)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization
namespace AVRegularity.CycleEvolution

/-! Recover product-space L² membership from joint measurability and Bochner slice classes. -/

/-- A jointly measurable field whose spatial classes form a Bochner L² curve is jointly L². -/
theorem cellJoint_memLp_of_slices (I : Set ℝ) (f : ℝ → Vec 2 → ℂ)
    (hm : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)))
    (u : ℝ → ComplexCellL2) (hu : MemLp u 2 (volume.restrict I))
    (he : ∀ᵐ t ∂volume.restrict I,
      (u t : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] f t) :
    MemLp (Function.uncurry f) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) := by
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  apply (integrable_prod_iff (hm.norm.pow 2)).mpr
  refine ⟨?_, ?_⟩
  · filter_upwards [he] with t ht
    exact ((Lp.memLp (u t)).ae_eq ht).norm.integrable_sq
  · apply hu.norm.integrable_sq.congr
    filter_upwards [he] with t ht
    change ‖u t‖ ^ 2 = ∫ x in AVenhance.unitCube, ‖‖f t x‖ ^ 2‖
    calc
      _ = ∫ x in AVenhance.unitCube, ‖u t x‖ ^ 2 := (cellL2_norm_sq_integral _).symm
      _ = ∫ x in AVenhance.unitCube, ‖f t x‖ ^ 2 := integral_congr_ae (ht.fun_comp (fun z => ‖z‖ ^ 2))
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]))

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
open scoped BigOperators
namespace AVRegularity.CycleEvolution

/-! The finite weighted bilinear product rule in the actual uniformly local source norm. -/

/-- Summing finitely many actual metric-gradient product derivatives preserves norm differentiation. -/
theorem cellMetricFlux_finset_productRule_tendsto {P J : Type*}
    (l : Filter P) (r : P → ℝ) (S : Finset J) (w : J → ℝ)
    (A : J → P → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (B C : J → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (E : J → P → ℝ → RawJet2 1 ℂ) (D T : J → ℝ → RawJet2 1 ℂ)
    (hA : ∀ j ∈ S, ∀ p, cellMetricSupNorm (A j p) < ⊤ ∧
      Measurable (Function.uncurry (A j p)))
    (hB : ∀ j ∈ S, cellMetricSupNorm (B j) < ⊤ ∧ Measurable (Function.uncurry (B j)))
    (hC : ∀ j ∈ S, cellMetricSupNorm (C j) < ⊤ ∧ Measurable (Function.uncurry (C j)))
    (hD : ∀ j ∈ S, cellEnergyNorm univ (D j) < ⊤)
    (hEm : ∀ j ∈ S, ∀ p a, AEStronglyMeasurable (fun z : ℝ × Vec 2 => E j p z.1 a z.2)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hDm : ∀ j ∈ S, ∀ a, AEStronglyMeasurable (fun z : ℝ × Vec 2 => D j z.1 a z.2)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hTm : ∀ j ∈ S, ∀ a, AEStronglyMeasurable (fun z : ℝ × Vec 2 => T j z.1 a z.2)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hAc : ∀ j ∈ S, Tendsto (fun p => cellMetricSupNorm (r p • (A j p - B j) - C j)) l (𝓝 0))
    (hEc : ∀ j ∈ S, Tendsto (fun p => cellEnergyNorm univ (E j p - D j)) l (𝓝 0))
    (hEd : ∀ j ∈ S, Tendsto (fun p => cellEnergyNorm univ (r p • (E j p - D j) - T j)) l (𝓝 0)) :
    Tendsto (fun p => cellUlNorm univ
      (r p • ((∑ j ∈ S, w j • cellMetricFlux (A j p) (E j p)) -
        ∑ j ∈ S, w j • cellMetricFlux (B j) (D j)) -
        ∑ j ∈ S, w j • (cellMetricFlux (C j) (D j) + cellMetricFlux (B j) (T j))))
      l (𝓝 0) := by
  let f := fun j p => r p • (cellMetricFlux (A j p) (E j p) - cellMetricFlux (B j) (D j))
  let f0 := fun j => cellMetricFlux (C j) (D j) + cellMetricFlux (B j) (T j)
  have hfm j (hj : j ∈ S) p : AEStronglyMeasurable (Function.uncurry (f j p))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) :=
    ((cellMetricFlux_aestronglyMeasurable univ (A j p) (E j p) (hA j hj p).2 (hEm j hj p)).sub
      (cellMetricFlux_aestronglyMeasurable univ (B j) (D j) (hB j hj).2 (hDm j hj))).const_smul (r p)
  have hf0m j (hj : j ∈ S) : AEStronglyMeasurable (Function.uncurry (f0 j))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) :=
    (cellMetricFlux_aestronglyMeasurable univ (C j) (D j) (hC j hj).2 (hDm j hj)).add
      (cellMetricFlux_aestronglyMeasurable univ (B j) (T j) (hB j hj).2 (hTm j hj))
  have hd j (hj : j ∈ S) := cellMetricFlux_productRule_tendsto l r (A j) (B j) (C j)
    (E j) (D j) (T j) (hA j hj) (hB j hj) (hC j hj) (hD j hj)
    (hEm j hj) (hDm j hj) (hTm j hj) (hAc j hj) (hEc j hj) (hEd j hj)
  have hs := cellUlNorm_finset_sum_tendsto l S
    (fun j p => w j • f j p) (fun j => w j • f0 j)
    (fun j hj p => (hfm j hj p).const_smul (w j))
    (fun j hj => (hf0m j hj).const_smul (w j))
    (fun j hj => cellUlNorm_smul_tendsto l (w j) (f j) (f0 j)
      (hfm j hj) (hf0m j hj) (hd j hj))
  have heq p : r p • ((∑ j ∈ S, w j • cellMetricFlux (A j p) (E j p)) -
      ∑ j ∈ S, w j • cellMetricFlux (B j) (D j)) = ∑ j ∈ S, w j • f j p := by
    rw [← Finset.sum_sub_distrib, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [f]
    rw [← smul_sub, smul_comm (r p) (w j)]
  simpa only [heq, f0] using hs

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The actual normalized source class at the sqrt-contrast frequency. -/

theorem cellNormalizedGraphSourceClass_bloch_ae (η : ℝ) (hη : 0 ≤ η)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v) (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (lam : ℝ → ℂ) (t : ℝ) (u : TorusHk 1 ℂ) :
    cellNormalizedGraphSourceClass G v V hv hb
      (fun j => (Real.sqrt η : ℂ) * ξ j) (fun s => -lam s) t u
      =ᵐ[volume.restrict AVenhance.unitCube]
        fun x => -Complex.I * fibreDriftCoupling η v ξ t x *
          (1 + torusHkValueCLM u x) -
          ((η : ℂ) * fibreQuad (G t) ξ + lam t) * (1 + torusHkValueCLM u x) := by
  filter_upwards [cellNormalizedGraphSourceClass_ae G hv V hb
    (fun j => (Real.sqrt η : ℂ) * ξ j) (fun s => -lam s) t u] with x hx
  rw [hx, fibreBloch_drift_coupling, fibreBloch_metric_quadratic η hη]
  ring

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Filter Homogenization
namespace AVRegularity.CycleEvolution

/-! Algebra of the spatial L² classes of joint cell fields. -/

/-- Joint almost-everywhere equality preserves the spatial classes at almost every time. -/
theorem cellSourceSlice_congr_ae (I : Set ℝ) (f g : ℝ → Vec 2 → ℂ)
    (hf : MemLp (Function.uncurry f) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)))
    (hg : MemLp (Function.uncurry g) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)))
    (he : Function.uncurry f =ᵐ[(volume.restrict I).prod
      (volume.restrict AVenhance.unitCube)] Function.uncurry g) :
    cellSourceSlice f =ᵐ[volume.restrict I] cellSourceSlice g := by
  have hsections : ∀ᵐ t ∂volume.restrict I,
      f t =ᵐ[volume.restrict AVenhance.unitCube] g t := Measure.ae_ae_of_ae_prod he
  filter_upwards [cellSource_memLp_slices I f hf, cellSource_memLp_slices I g hg,
    hsections] with t hft hgt ht
  apply Lp.ext
  exact (cellSourceSlice_ae f t hft).trans (ht.trans (cellSourceSlice_ae g t hgt).symm)

/-- Product convergence can be read using any prescribed spatial classes. -/
theorem cellProduct_distance_sq_of_slices (I : Set ℝ) (f g : ℝ → Vec 2 → ℂ)
    (hf : MemLp (Function.uncurry f) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)))
    (hg : MemLp (Function.uncurry g) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)))
    (u v : ℝ → ComplexCellL2)
    (hu : ∀ᵐ t ∂volume.restrict I, (u t : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] f t)
    (hv : ∀ᵐ t ∂volume.restrict I, (v t : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] g t) :
    ‖hf.toLp (Function.uncurry f) - hg.toLp (Function.uncurry g)‖ ^ 2 =
      ∫ t in I, ‖u t - v t‖ ^ 2 := by
  rw [← MemLp.toLp_sub hf hg]
  apply cellProduct_norm_sq_of_slices I (fun t x => f t x - g t x) (hf.sub hg)
  filter_upwards [hu, hv] with t hut hvt
  exact (Lp.coeFn_sub _ _).trans (hut.sub hvt)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Actual energy-summable cell trajectories have globally almost-everywhere absolutely convergent values. -/

/-- The value series of actual energy-summable solutions converges absolutely jointly almost everywhere. -/
theorem cellSolutionSeries_value_summable_norm_ae {J : Type*} [Countable J]
    (C : J → CellCoefficients) (src : J → ℝ → Vec 2 → ℂ)
    (F : J → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D : J → ℝ → RawJet2 1 ℂ)
    (hD : ∀ j, IsCellSolution Set.univ (C j) (src j) (F j) (D j))
    (hs : (∑' j, cellEnergyNorm Set.univ (D j)) < ⊤) :
    ∀ᵐ p ∂((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)),
      Summable (fun j => ‖cellValue (D j) p.1 p.2‖) := by
  simp only [Measure.restrict_univ]
  apply cellProduct_ae_of_integer_windows (volume.restrict AVenhance.unitCube)
  intro n
  exact (cellLpSeries_memLp_bound _ (fun j => Function.uncurry (cellValue (D j)))
    (cellSolutionSeries_value_interval_L2 C src F D hD hs (n : ℝ) ((n : ℝ) + 1))).2.2

end AVRegularity.CycleEvolution
end

section
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! Full unweighted fibre coefficient convolutions are bounded by finite prefix products. -/

/-- Full triangular coefficient convolution injects into the complete lower prefix rectangle. -/
theorem fibreCoefficient_convolution_le_product (K : ℕ) (a b : ℕ × ℕ → ℝ≥0∞) :
    (∑ p ∈ jetIndices K, ∑ q ∈ fibreCoefficientPairs p,
      a q * b (fibreCoefficientComplement p q)) ≤
      (∑ q ∈ jetIndices K, a q) * (∑ q ∈ jetIndices K, b q) := by
  classical
  let S := (jetIndices K).sigma fibreCoefficientPairs
  let f : (Σ _ : ℕ × ℕ, ℕ × ℕ) → (ℕ × ℕ) × (ℕ × ℕ) :=
    fun p => (p.2, fibreCoefficientComplement p.1 p.2)
  have hf : Set.InjOn f (↑S : Set (Σ _ : ℕ × ℕ, ℕ × ℕ)) := by
    intro p hp q hq he
    have hp' := Finset.mem_sigma.mp hp
    have hq' := Finset.mem_sigma.mp hq
    have hfirst : p.2 = q.2 := congrArg Prod.fst he
    have hsecond : fibreCoefficientComplement p.1 p.2 = fibreCoefficientComplement q.1 q.2 :=
      congrArg Prod.snd he
    have hindex : p.1 = q.1 := by
      rw [← fibreCoefficientPairs_recover hp'.2, ← fibreCoefficientPairs_recover hq'.2]
      exact congrArg₂ (fun x y : ℕ × ℕ => x + y) hfirst hsecond
    cases p
    cases q
    dsimp at hindex hfirst
    cases hindex
    cases hfirst
    rfl
  have hsub : S.image f ⊆ jetIndices K ×ˢ jetIndices K := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hindex, hpairs⟩ := Finset.mem_sigma.mp hq
    have horder := (mem_jetIndices_iff K q.1).mp hindex
    have hbounds := fibreCoefficientPairs_bounds hpairs
    apply Finset.mem_product.mpr
    constructor <;> apply (mem_jetIndices_iff K _).mpr
    · dsimp only [f]
      omega
    · dsimp only [f, fibreCoefficientComplement]
      omega
  calc
    _ = ∑ p ∈ S, a (f p).1 * b (f p).2 := by rw [Finset.sum_sigma]
    _ = ∑ p ∈ S.image f, a p.1 * b p.2 :=
      (Finset.sum_image (f := fun p : (ℕ × ℕ) × (ℕ × ℕ) => a p.1 * b p.2) hf).symm
    _ ≤ ∑ p ∈ jetIndices K ×ˢ jetIndices K, a p.1 * b p.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => bot_le)
    _ = _ := by rw [Finset.sum_product, Finset.sum_mul_sum]

end AVRegularity.CycleEvolution
end
