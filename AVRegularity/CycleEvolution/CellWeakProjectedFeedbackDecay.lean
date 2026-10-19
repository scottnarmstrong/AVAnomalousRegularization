-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleEvolution.CellLimitMoments
import AVRegularity.CycleEvolution.CellEnergySpaceRawJetCauchyBound
import AVRegularity.CycleEvolution.CellEnergySpaceRawDirectionalLimit
public import AVRegularity.CycleEvolution.CellEnergySpaceRawSmul
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Absolute energy and forcing series of actual cell solutions solve the literal summed equation. -/

/-- Actual zero-frequency cell energy solutions are closed under absolutely summable energy and forcing series. -/
theorem cellSolutionSeries_isCellSolution {J : Type*} [Countable J]
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric G)
    (v : ℝ → Vec 2 → Vec 2) (hvm : Measurable (Function.uncurry v))
    (V : ℝ) (hvb : ∀ t x, ∑ k, v t x k ^ 2 ≤ V ^ 2)
    (src : J → ℝ → Vec 2 → ℂ)
    (F : J → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D : J → ℝ → RawJet2 1 ℂ)
    (hD : ∀ j, IsCellSolution Set.univ ⟨G, v, 0, 0⟩ (src j) (F j) (D j))
    (hsD : (∑' j, cellEnergyNorm Set.univ (D j)) < ⊤)
    (hsm : ∀ j, AEStronglyMeasurable (Function.uncurry (src j))
      ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)))
    (hFm : ∀ j, AEStronglyMeasurable (Function.uncurry (F j))
      ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)))
    (hss : (∑' j, cellUlNorm Set.univ (src j)) < ⊤)
    (hFs : (∑' j, cellUlNorm Set.univ (F j)) < ⊤) :
    IsCellSolution Set.univ ⟨G, v, 0, 0⟩ (fun t x => ∑' j, src j t x)
      (fun t x => ∑' j, F j t x) (fun t a x => ∑' j, D j t a x) := by
  let R := fun t a x => ∑' j, D j t a x
  have hm j := (hD j).2.2.2.1
  have htrace := cellSolutionSeries_continuous_trace (fun _ => ⟨G, v, 0, 0⟩) src F D hD hsD
  have henergy : cellEnergyNorm Set.univ R < ⊤ :=
    (cellEnergyNorm_tsum_le D hm hsD).trans_lt (ENNReal.mul_lt_top (by simp) hsD)
  have hgrad : cellUlNorm Set.univ (fun t => cellGradient (R t)) < ⊤ :=
    (le_add_left le_rfl).trans_lt henergy
  refine ⟨Set.ordConnected_univ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Measure.restrict_univ] using
      cellSolutionSeries_periodicWeakJet_ae (fun _ => ⟨G, v, 0, 0⟩) src F D hD hsD
  · intro t _
    exact cellSolutionSeries_value_regular (fun _ => ⟨G, v, 0, 0⟩) src F D hD hsD t
  · exact cellJetSeries_aestronglyMeasurable Set.univ D hm
  · exact cellRaw_trace_continuous Set.univ (fun t => ∑' j, cellRawTrace (D j) t)
      htrace.1.continuousOn (cellValue R) (fun t _ => (htrace.2 t).1)
  · intro a _ b _
    simpa only [Set.inter_univ] using
      cellUl_interval_integral_lt_top Set.univ (fun t => cellGradient (R t)) hgrad a b
  · intro s _ t _ hst ψ
    exact cellSolutionSeries_weak_identity G hG v hvm V hvb src F D hD hsD hsm hFm hss hFs s t hst ψ

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Subtracting the graph times the actual scalar mean is valid for L² forcing at weak time regularity. -/

theorem cellWeakGraph_mean_remainder {a b : ℝ} (hab : a ≤ b)
    {u R : ℝ → ComplexCellL2} {slice Rslice g gR : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice g)
    (hR : CellWeakHilbertCurve a b R Rslice gR) :
    CellWeakHilbertCurve a b
      (fun t => u t - cellScalarCLM (cellMean (u t)) (R t))
      (fun t => slice t - cellH1Scalar (cellMean (u t)) (Rslice t))
      (fun t => g t - (cellH1Scalar (cellMean (u t)) (gR t) +
        cellPivotDualCLM (cellScalarCLM (cellDualComplexPair (g t) cellH1One) (R t)))) := by
  have hc := h.mean_strongTime hab
  have hd := cellDualComplexPair_memLp g h.dual cellH1One
  exact h.sub (hR.variable_complex_scalar_L2 hab _ _ hc hd)

theorem cellMean_graph_mean_remainder_zero (u R : ComplexCellL2)
    (hR : cellMean R = 1) :
    cellMean ((u - cellScalarCLM (cellMean u) R : ComplexCellL2)) = 0 := by
  rw [← cellMeanCLM_apply (u - cellScalarCLM (cellMean u) R), map_sub, cellMeanCLM_complex_scalar,
    cellMeanCLM_apply, cellMeanCLM_apply, hR, mul_one, sub_self]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Existence of public raw cell solutions under the actual data premises. -/

/-- Arbitrary L² initial data and measurable L² sources produce a public cell energy solution. -/
theorem cellActual_exists_raw {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hvb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (hκ : Measurable C.κ) (hκb : ∀ t, ‖C.κ t‖ ≤ k)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrcm : Measurable (Function.uncurry src)) (hFm : Measurable (Function.uncurry F))
    (hsrc : ∫⁻ t in Icc a b, cellL2Norm (src t) ^ 2 < ⊤)
    (hF : ∫⁻ t in Icc a b, cellL2Norm (F t) ^ 2 < ⊤)
    (initial : ComplexCellL2) :
    ∃ D : ℝ → RawJet2 1 ℂ, IsCellSolution (Icc a b) C src F D ∧
      cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] initial := by
  obtain ⟨u, slice, h, hi⟩ := cellActual_exists_Hilbert hab C hG V k hv hvb hκ hκb
    src F hsrcm hFm hsrc hF initial
  obtain ⟨D, hD, he⟩ := cellWeakHilbert_exists_raw_solution C hG V hv hvb src F
    (cellSource_memLp_product (Icc a b) src hsrcm hsrc)
    (cellSource_memLp_product (Icc a b) F hFm hF) u slice h
  refine ⟨D, hD, ?_⟩
  exact (he a).symm.trans (Filter.EventuallyEq.of_eq (congrArg
    (fun z : ComplexCellL2 => (z : Vec 2 → ℂ)) hi))

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Absolute series of actual bounded mean-zero inverses solve the literal summed equation. -/

/-- Actual zero-frequency inverse trajectories are closed under absolute energy and forcing series. -/
theorem cellInverseSeries_isInverse {J : Type*} [Countable J]
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric G)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v)
    (src : J → ℝ → Vec 2 → ℂ)
    (F : J → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D : J → ℝ → RawJet2 1 ℂ)
    (hD : ∀ j, IsCellInverseValue ⟨G, v, 0, 0⟩ (src j) (F j) (D j))
    (hsD : (∑' j, cellEnergyNorm Set.univ (D j)) < ⊤)
    (hsm : ∀ j, AEStronglyMeasurable (Function.uncurry (src j))
      ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)))
    (hFm : ∀ j, AEStronglyMeasurable (Function.uncurry (F j))
      ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)))
    (hss : (∑' j, cellUlNorm Set.univ (src j)) < ⊤)
    (hFs : (∑' j, cellUlNorm Set.univ (F j)) < ⊤) :
    IsCellInverseValue ⟨G, v, 0, 0⟩ (fun t x => ∑' j, src j t x)
      (fun t x => ∑' j, F j t x) (fun t a x => ∑' j, D j t a x) := by
  obtain ⟨V, hV⟩ := hv.2.1
  refine ⟨cellSolutionSeries_isCellSolution G hG v hv.1 V hV src F D
    (fun j => (hD j).1) hsD hsm hFm hss hFs, ?_, ?_⟩
  · exact cellInverseSeries_mean_zero (fun _ => ⟨G, v, 0, 0⟩) src F D hD hsD
  · exact (cellEnergyNorm_tsum_le D (fun j => (hD j).1.2.2.2.1) hsD).trans_lt
      (ENNReal.mul_lt_top (by simp) hsD)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The actual forced graph remainder solves the exact linear generator equation with its mean-feedback source. -/

theorem cellWeakForcedGraph_mean_remainder {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    {u R : ℝ → ComplexCellL2} {slice Rslice : ℝ → TorusHk 1 ℂ}
    (S : ℝ → ComplexCellL2) (F : ℝ → Fin 2 → ComplexCellL2)
    (h : CellWeakHilbertCurve a b u slice
      (fun t => cellDualDerivative C hG V hv hb t (slice t) (S t) (F t)))
    (hR : CellWeakHilbertCurve a b R Rslice
      (fun t => cellDualDerivative C hG V hv hb t (Rslice t) 0 0)) :
    CellWeakHilbertCurve a b
      (fun t => u t - cellScalarCLM (cellMean (u t)) (R t))
      (fun t => slice t - cellH1Scalar (cellMean (u t)) (Rslice t))
      (fun t => cellDualDerivative C hG V hv hb t
        (slice t - cellH1Scalar (cellMean (u t)) (Rslice t)) (S t) (F t) -
        cellPivotDualCLM (cellScalarCLM
          (cellDualComplexPair (cellDualDerivative C hG V hv hb t (slice t) (S t) (F t))
            cellH1One) (R t))) := by
  apply (cellWeakGraph_mean_remainder hab h hR).dual_congr
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  rw [sub_add_eq_sub_sub, cellDualDerivative_sub_homogeneous_scalar]

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Uniform Bloch energy production with a quantified small loss of gradient dissipation. -/

theorem cellBlochLinear_energy_bound (η Cw : ℝ) (hη0 : 0 ≤ η)
    (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (t : ℝ) (u : TorusHk 1 ℂ) :
    cellGeneratorForm ⟨fun t _ => G t, v, (fun j => (Real.sqrt η : ℂ) * ξ j), 0⟩
        hG V hv.1 hb t u u ≤
      -(1 - g - 1 / 32) * ∑ j, ‖cellDerivativeCLM j u‖ ^ 2 +
      (Cw * fibreNorm ξ + 1032 * fibreNorm ξ ^ 2) * ‖torusHkValueCLM u‖ ^ 2 := by
  let θ := fun j => (Real.sqrt η : ℂ) * ξ j
  let S := cellBlochLinearSourceClass G v V hv hb θ t u
  let F := cellNormalizedGraphFluxClass G θ t u
  have hs : inner ℝ S (torusHkValueCLM u) ≤
      (Cw * fibreNorm ξ + 8 * fibreNorm ξ ^ 2) * ‖torusHkValueCLM u‖ ^ 2 := by
    calc
      _ ≤ ‖S‖ * ‖torusHkValueCLM u‖ :=
        (le_abs_self _).trans (abs_real_inner_le_norm _ _)
      _ ≤ ((Cw * fibreNorm ξ + 8 * fibreNorm ξ ^ 2) * ‖torusHkValueCLM u‖) *
          ‖torusHkValueCLM u‖ := mul_le_mul_of_nonneg_right
        (cellBlochLinearSourceClass_norm_le η Cw hη0 hη hCw G hG hv hw V hb ξ t u)
        (norm_nonneg _)
      _ = _ := by ring
  have hf := hilbertSmallFlux_young F (fun j => cellDerivativeCLM j u)
    (8 * fibreNorm ξ) ‖torusHkValueCLM u‖
    (fun j => cellNormalizedGraphFluxClass_norm_le η hη G hG ξ t u j)
  have he := cellMetricEnergy_near_identity_coercive hG hg t u
  rw [cellBlochLinear_generator_real G hG hv V hb]
  change -cellMetricEnergy hG t u + inner ℝ S (torusHkValueCLM u) -
    ∑ j, inner ℝ (F j) (cellDerivativeCLM j u) ≤ _
  nlinarith

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The actual Fourier construction for arbitrary scalar and flux Bochner L2 Hilbert data. -/

theorem cellActual_exists_Hilbert_sources {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (hκ : AEStronglyMeasurable C.κ (volume.restrict (Icc a b)))
    (hκb : ∀ t, ‖C.κ t‖ ≤ k) (S : ℝ → ComplexCellL2)
    (hS : MemLp S 2 (volume.restrict (Icc a b))) (F : ℝ → Fin 2 → ComplexCellL2)
    (hF : ∀ j, MemLp (fun t => F t j) 2 (volume.restrict (Icc a b))) (initial : ComplexCellL2) :
    ∃ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ),
      CellWeakHilbertCurve a b u slice (fun t => cellDualDerivative C hG V hv hb t
        (slice t) (S t) (F t)) ∧ u a = initial := by
  obtain ⟨src, hm, hs, he⟩ := cellBochner_exists_measurable_realization (Icc a b) S hS
  have hsrc := cellSource_product_energy_lt_top (Icc a b) src hm hs
  have hex j := cellBochner_exists_measurable_realization (Icc a b) (fun t => F t j) (hF j)
  choose fj hjm hjs hje using hex
  let rawF := fun t x => WithLp.toLp 2 (fun j : Fin 2 => fj j t x)
  have hrawm : Measurable (Function.uncurry rawF) :=
    (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 2 => ℂ)).measurable.comp
      (Measurable.of_eval (fun j => hjm j))
  have hraw : MemLp (Function.uncurry rawF) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)) :=
    cellFiniteArray_memLp (fun p : ℝ × Vec 2 => fun j => fj j p.1 p.2) hjs
  have henergy := cellSource_product_energy_lt_top (Icc a b) rawF hrawm hraw
  obtain ⟨u, slice, h, hi⟩ := cellActual_exists_Hilbert_aePotential hab C hG V k hv hb hκ hκb
    src rawF hm hrawm hsrc henergy initial
  refine ⟨u, slice, h.dual_congr ?_, hi⟩
  filter_upwards [he, ae_all_iff.mpr hje] with t ht htF
  have hc : (fun j => cellSourceSlice (fun τ x => rawF τ x j) t) = F t := by
    funext j
    exact htF j
  rw [ht, hc]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The exact scalar derivative of a normalized graph remainder is its drift mean plus the source mean. -/

theorem cellBloch_normalized_mean_identity (η Cw : ℝ) (hη0 : 0 ≤ η) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) (u : TorusHk 1 ℂ) (ρ z : ComplexCellL2)
    (hκ : κ t = (η : ℂ) * fibreQuad (G t) ξ +
      Complex.I * cellBlochDriftMeanCLM η Cw hCw hv hw ξ t ρ)
    (hdecomp : torusHkValueCLM u =
      cellScalarCLM (cellMean (torusHkValueCLM u)) (ρ + cellConstantCLM 1) + z)
    (F : Fin 2 → ComplexCellL2) :
    cellDualComplexPair (cellDualDerivative
      ⟨fun t _ => G t, v, (fun j => (Real.sqrt η : ℂ) * ξ j), κ⟩
      hG V hv.1 hb t u 0 F) cellH1One =
      -Complex.I * cellBlochDriftMeanCLM η Cw hCw hv hw ξ t z +
      ∑ j : Fin 2, Complex.I * ((Real.sqrt η : ℂ) * ξ j) * cellMean (F j) := by
  have ht := cellBloch_normalized_mean_triangular η Cw hη0 hCw G hv hw hm V hb ξ t u ρ z hdecomp
  have hz : cellMean (0 : ComplexCellL2) = 0 := by
    rw [← cellMeanCLM_apply (0 : ComplexCellL2), map_zero]
  rw [cellDualComplexPair_bloch_potential_one G hG hv V hb, hκ, hz, add_zero]
  have he : cellMean (cellBlochLinearSourceClass G v V hv hb
      (fun j => (Real.sqrt η : ℂ) * ξ j) t u) +
      ((η : ℂ) * fibreQuad (G t) ξ +
        Complex.I * cellBlochDriftMeanCLM η Cw hCw hv hw ξ t ρ) * cellMean (torusHkValueCLM u) =
      -Complex.I * cellBlochDriftMeanCLM η Cw hCw hv hw ξ t z := by
    calc
      _ = cellMean (cellBlochLinearSourceClass G v V hv hb
          (fun j => (Real.sqrt η : ℂ) * ξ j) t u) -
          (-(η : ℂ) * fibreQuad (G t) ξ -
            Complex.I * cellBlochDriftMeanCLM η Cw hCw hv hw ξ t ρ) *
          cellMean (torusHkValueCLM u) := by ring
      _ = _ := ht
  rw [he]

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Actual small-frequency Bloch dissipation for H¹ states with a small cell mean. -/

theorem cellBlochSmallMean_dissipation (η Cw : ℝ) (hη0 : 0 ≤ η)
    (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : Cw * fibreNorm ξ + 1032 * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2 / 16)
    (t : ℝ) (u : TorusHk 1 ℂ)
    (hm : ‖cellMeanCLM (torusHkValueCLM u)‖ ≤ (1 / 16) * ‖torusHkValueCLM u‖) :
    cellGeneratorForm ⟨fun t _ => G t, v, (fun j => (Real.sqrt η : ℂ) * ξ j), 0⟩
      hG V hv.1 hb t u u ≤ -3 * Real.pi ^ 2 * ‖torusHkValueCLM u‖ ^ 2 := by
  have he := cellBlochLinear_energy_bound η Cw hη0 hη hCw G hG hg hv hw V hb ξ t u
  have hp := cellSmallMean_gradient_gap u (1 / 16) (by norm_num) hm
  have hd : 0 ≤ ∑ j, ‖cellDerivativeCLM j u‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hc := mul_le_mul_of_nonneg_right hgsmall hd
  have hfreq := mul_le_mul_of_nonneg_right hξ (sq_nonneg ‖torusHkValueCLM u‖)
  have hπ := sq_nonneg Real.pi
  have hmass := mul_nonneg hπ (sq_nonneg ‖torusHkValueCLM u‖)
  nlinarith

/-! The normalized Bloch generator retains a mean-zero gap after its scalar gauge and graph feedback. -/

theorem cellScalarCLM_inner_abs_le (c : ℂ) (u z : ComplexCellL2) :
    |inner ℝ (cellScalarCLM c u) z| ≤ ‖c‖ * ‖u‖ * ‖z‖ := by
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (cellScalarCLM_norm c u).le (norm_nonneg z))

theorem cellBloch_normalized_feedback_energy (η Cw : ℝ) (hη0 : 0 ≤ η)
    (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (L B : ℝ)
    (hsmall : Cw * fibreNorm ξ + (1032 + L + B) * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2)
    (t : ℝ) (u : TorusHk 1 ℂ) (hm : cellMean (torusHkValueCLM u) = 0)
    (lam : ℂ) (hlam : ‖lam‖ ≤ L * fibreNorm ξ ^ 2)
    (feedback : ComplexCellL2)
    (hfeedback : ‖feedback‖ ≤ B * fibreNorm ξ ^ 2 * ‖torusHkValueCLM u‖) :
    inner ℝ (cellDualDerivative
      ⟨fun t _ => G t, v, (fun j => (Real.sqrt η : ℂ) * ξ j), 0⟩
      hG V hv.1 hb t u 0 0 -
      cellPivotDualCLM (cellScalarCLM lam (torusHkValueCLM u)) -
      cellPivotDualCLM feedback) u ≤
      -(1 / 4) * ∑ j, ‖cellDerivativeCLM j u‖ ^ 2 -
        Real.pi ^ 2 * ‖torusHkValueCLM u‖ ^ 2 := by
  have he := cellBlochLinear_energy_bound η Cw hη0 hη hCw G hG hg hv hw V hb ξ t u
  have hp := cellMeanZero_gradient_gap u hm
  have hd : 0 ≤ ∑ j, ‖cellDerivativeCLM j u‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hc := mul_le_mul_of_nonneg_right hgsmall hd
  have hl : |inner ℝ (cellScalarCLM lam (torusHkValueCLM u))
      (torusHkValueCLM u)| ≤
      L * fibreNorm ξ ^ 2 * ‖torusHkValueCLM u‖ * ‖torusHkValueCLM u‖ :=
    (cellScalarCLM_inner_abs_le lam (torusHkValueCLM u)
      (torusHkValueCLM u)).trans (by gcongr)
  have hf := (abs_real_inner_le_norm feedback (torusHkValueCLM u)).trans
    (mul_le_mul_of_nonneg_right hfeedback (norm_nonneg _))
  have hln := neg_le_abs (inner ℝ (cellScalarCLM lam (torusHkValueCLM u))
    (torusHkValueCLM u))
  have hfn := neg_le_abs (inner ℝ feedback (torusHkValueCLM u))
  have hs := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖torusHkValueCLM u‖)
  rw [inner_sub_left, inner_sub_left, cellDualDerivative_pairing]
  have hz : cellSourceFunctional (fun j => (Real.sqrt η : ℂ) * ξ j) 0 0 u = 0 := by
    simp [cellSourceFunctional]
  rw [hz, add_zero]
  simp only [cellPivotDualCLM, ContinuousLinearMap.adjoint_inner_left]
  nlinarith

/-! Forced mean-zero normalized Bloch energy retains a uniform value and gradient gap. -/

theorem cellBloch_normalized_feedback_forced_energy (η Cw : ℝ) (hη0 : 0 ≤ η)
    (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (L B : ℝ)
    (hsmall : Cw * fibreNorm ξ + (1032 + L + B) * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2)
    (t : ℝ) (u : TorusHk 1 ℂ) (hm : cellMean (torusHkValueCLM u) = 0)
    (lam : ℂ) (hlam : ‖lam‖ ≤ L * fibreNorm ξ ^ 2)
    (feedback : ComplexCellL2)
    (hfeedback : ‖feedback‖ ≤ B * fibreNorm ξ ^ 2 * ‖torusHkValueCLM u‖)
    (hθ : ∀ j, ‖(Real.sqrt η : ℂ) * ξ j‖ ≤ 1)
    (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    2 * inner ℝ (cellDualDerivative
      ⟨fun t _ => G t, v, (fun j => (Real.sqrt η : ℂ) * ξ j), 0⟩
      hG V hv.1 hb t u S F -
      cellPivotDualCLM (cellScalarCLM lam (torusHkValueCLM u)) -
      cellPivotDualCLM feedback) u +
      Real.pi ^ 2 * ‖torusHkValueCLM u‖ ^ 2 +
      (1 / 4) * ∑ j, ‖cellDerivativeCLM j u‖ ^ 2 ≤
      4 * ‖S‖ ^ 2 + 12 * ∑ j, ‖F j‖ ^ 2 := by
  have he := cellBloch_normalized_feedback_energy η Cw hη0 hη hCw G hG hg hgsmall
    hv hw V hb ξ L B hsmall t u hm lam hlam feedback hfeedback
  have hs := cellBloch_smallShift_source_energy (fun j => (Real.sqrt η : ℂ) * ξ j) hθ S F u
  have hz : cellSourceFunctional (fun j => (Real.sqrt η : ℂ) * ξ j) 0 0 u = 0 := by
    simp [cellSourceFunctional]
  rw [inner_sub_left, inner_sub_left, cellDualDerivative_pairing, hz, add_zero] at he
  rw [inner_sub_left, inner_sub_left, cellDualDerivative_pairing]
  linarith

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The actual finite-time cell evolution as an existence-and-uniqueness relation on complete complex carriers. -/

abbrev CellFiniteEnergyDatum (a b : ℝ) := ComplexCellL2 ×
  (Lp ComplexCellL2 2 (volume.restrict (Icc a b)) ×
    (Fin 2 → Lp ComplexCellL2 2 (volume.restrict (Icc a b))))

def IsCellFiniteEnergyEvolution {a b : ℝ} (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (data : CellFiniteEnergyDatum a b) (z : CellFiniteEnergyCarrier a b) : Prop :=
  ∃ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ),
    CellWeakHilbertCurve a b u slice (fun t => cellDualDerivative C hG V hv hb t
      (slice t) (data.2.1 t) (fun j => data.2.2 j t)) ∧
    u a = data.1 ∧ (∀ t : CellCompactTime a b, z.val.1 t = u t.val)

theorem cellFiniteEnergyEvolution_exists {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (hκ : AEStronglyMeasurable C.κ (volume.restrict (Icc a b)))
    (hκb : ∀ t, ‖C.κ t‖ ≤ k) (data : CellFiniteEnergyDatum a b) :
    ∃ z : CellFiniteEnergyCarrier a b, IsCellFiniteEnergyEvolution C hG V hv hb data z := by
  obtain ⟨u, slice, h, hi⟩ := cellActual_exists_Hilbert_sources hab C hG V k hv hb hκ hκb
    data.2.1 (Lp.memLp _) (fun t j => data.2.2 j t) (fun j => Lp.memLp _) data.1
  obtain ⟨z, ht, _⟩ := cellWeakHilbertCurve_exists_energyCarrier a b u slice
    (fun t => cellDualDerivative C hG V hv hb t (slice t) (data.2.1 t) (fun j => data.2.2 j t)) h
  exact ⟨z, u, slice, h, hi, ht⟩

theorem cellFiniteEnergyEvolution_unique {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (hκb : ∀ t, ‖C.κ t‖ ≤ k) (data : CellFiniteEnergyDatum a b)
    (z w : CellFiniteEnergyCarrier a b)
    (hz : IsCellFiniteEnergyEvolution C hG V hv hb data z)
    (hw : IsCellFiniteEnergyEvolution C hG V hv hb data w) : z = w := by
  obtain ⟨u, slice, hu, hiu, htu⟩ := hz
  obtain ⟨v, other, hv', hiv, htv⟩ := hw
  have ht := cellActualWeak_unique hab C hG V k hv hb hκb data.2.1
    (fun t j => data.2.2 j t) u v slice other hu hv' (hiu.trans hiv.symm)
  apply cellFiniteEnergyCarrier_trace_injective a b
  apply ContinuousMap.ext
  intro t
  exact (htu t).trans ((ht t.val t.property).trans (htv t).symm)

end AVRegularity.CycleEvolution
end

section
namespace AVRegularity.CycleEvolution

/-! The external forcing datum after moving a Bloch-frequency change to the source. -/

def cellBlochExternalDatum {a b : ℝ} (δ : Fin 2 → ℂ) (d : CellFiniteEnergyDatum a b) :
    CellFiniteEnergyDatum a b :=
  (d.1, d.2.1 + ∑ j : Fin 2, (Complex.I * δ j) • d.2.2 j, d.2.2)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization
namespace AVRegularity.CycleEvolution

/-! Almost-everywhere equality of actual time potentials preserves the complete weak evolution relation. -/

theorem cellDualDerivative_potential_congr (C : CellCoefficients) (hG : IsCellMetric C.G)
    (V : ℝ) (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (q r : ℝ → ℂ) (t : ℝ) (ht : q t = r t)
    (u : AVRegularity.Sobolev.TorusHk 1 ℂ) (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    cellDualDerivative { C with κ := q } hG V hv hb t u S F =
      cellDualDerivative { C with κ := r } hG V hv hb t u S F := by
  have he : cellGeneratorForm { C with κ := q } hG V hv hb t =
      cellGeneratorForm { C with κ := r } hG V hv hb t := by
    unfold cellGeneratorForm
    dsimp only
    rw [ht]
    rfl
  unfold cellDualDerivative
  rw [he]

theorem cellFiniteEnergyEvolution_potential_congr {a b : ℝ}
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (q r : ℝ → ℂ) (hqr : q =ᵐ[volume.restrict (Icc a b)] r)
    (d : CellFiniteEnergyDatum a b) (z : CellFiniteEnergyCarrier a b)
    (hz : IsCellFiniteEnergyEvolution { C with κ := q } hG V hv hb d z) :
    IsCellFiniteEnergyEvolution { C with κ := r } hG V hv hb d z := by
  obtain ⟨u, slice, hu, hi, ht⟩ := hz
  refine ⟨u, slice, hu.dual_congr ?_, hi, ht⟩
  filter_upwards [hqr] with t he
  exact cellDualDerivative_potential_congr C hG V hv hb q r t he _ _ _

end AVRegularity.CycleEvolution
end

section
namespace AVRegularity.CycleEvolution

/-! External forcing remains analytic under the literal frequency-source adjustment. -/

theorem cellBlochExternalDatum_analyticAt {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] {a b : ℝ}
    (δ : X → Fin 2 → ℂ) (x : X) (hδ : AnalyticAt ℂ δ x)
    (d : CellFiniteEnergyDatum a b) :
    AnalyticAt ℂ (fun y => cellBlochExternalDatum (δ y) d) x := by
  have hd (j : Fin 2) : AnalyticAt ℂ (fun y => δ y j) x :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) j).analyticAt (δ x)).comp hδ
  have hj (j : Fin 2) : AnalyticAt ℂ (fun y => (Complex.I * δ y j) • d.2.2 j) x :=
    (analyticAt_const.mul (hd j)).smul analyticAt_const
  have hs : AnalyticAt ℂ (fun y => d.2.1 + ∑ j : Fin 2, (Complex.I * δ y j) • d.2.2 j) x := by
    simpa only [Fin.sum_univ_two, Pi.add_def] using analyticAt_const.add ((hj 0).add (hj 1))
  exact analyticAt_const.prod (hs.prod analyticAt_const)

/-! Named complex normed space of bounded actual cell forcing operators. -/

def CellEnergyForcingOperator (a b : ℝ) := CellFiniteEnergyCarrier a b →L[ℂ] CellFiniteEnergyDatum a b

instance cellEnergyForcingOperator_normedAddCommGroup (a b : ℝ) :
    NormedAddCommGroup (CellEnergyForcingOperator a b) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℂ) (𝕜₂ := ℂ)
    (E := CellFiniteEnergyCarrier a b) (F := CellFiniteEnergyDatum a b) (σ₁₂ := RingHom.id ℂ)

instance cellEnergyForcingOperator_normedSpace (a b : ℝ) :
    NormedSpace ℂ (CellEnergyForcingOperator a b) :=
  ContinuousLinearMap.toNormedSpace (𝕜' := ℂ) (𝕜 := ℂ) (𝕜₂ := ℂ)
    (E := CellFiniteEnergyCarrier a b) (F := CellFiniteEnergyDatum a b) (σ₁₂ := RingHom.id ℂ)

def cellEnergyForcingOperatorOfCLM (a b : ℝ) :
    (CellFiniteEnergyCarrier a b →L[ℂ] CellFiniteEnergyDatum a b) →L[ℂ] CellEnergyForcingOperator a b :=
  ContinuousLinearMap.id ℂ (CellEnergyForcingOperator a b)

end AVRegularity.CycleEvolution
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory
open scoped BigOperators
namespace AVRegularity.CycleEvolution

/-! The literal initial and forcing energy is bounded by the complete complex datum norm. -/

theorem cellFiniteEnergyDatum_budget_le {a b : ℝ} (hab : a ≤ b) (d : CellFiniteEnergyDatum a b) :
    ‖d.1‖ ^ 2 + (∫ t in a..b, ‖d.2.1 t‖ ^ 2 + 9 * ∑ j, ‖d.2.2 j t‖ ^ 2) ≤ 20 * ‖d‖ ^ 2 := by
  have hi := pow_le_pow_left₀ (norm_nonneg d.1) (norm_fst_le d) 2
  have hs := pow_le_pow_left₀ (norm_nonneg d.2.1) ((norm_fst_le d.2).trans (norm_snd_le d)) 2
  have hf j := pow_le_pow_left₀ (norm_nonneg (d.2.2 j))
    ((norm_le_pi_norm d.2.2 j).trans ((norm_snd_le d.2).trans (norm_snd_le d))) 2
  have hsi := cellTime_normSq_intervalIntegrable hab (Lp.memLp d.2.1)
  have hfi j := cellTime_normSq_intervalIntegrable hab (Lp.memLp (d.2.2 j))
  have he : (∫ t in a..b, ‖d.2.1 t‖ ^ 2 + 9 * ∑ j, ‖d.2.2 j t‖ ^ 2) =
      ‖d.2.1‖ ^ 2 + 9 * (‖d.2.2 0‖ ^ 2 + ‖d.2.2 1‖ ^ 2) := by
    simp only [Fin.sum_univ_two]
    rw [intervalIntegral.integral_add hsi (((hfi 0).add (hfi 1)).const_mul 9),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hfi 0) (hfi 1),
      cellLpTime_norm_sq_intervalIntegral hab, cellLpTime_norm_sq_intervalIntegral hab,
      cellLpTime_norm_sq_intervalIntegral hab]
  rw [he]
  linarith [hf 0, hf 1]

end AVRegularity.CycleEvolution
end

section
namespace AVRegularity.CycleEvolution

/-! Bounded evaluation and extensionality for the named forcing operator space. -/

def cellEnergyForcingOperatorEvalCLM (a b : ℝ) (z : CellFiniteEnergyCarrier a b) :
    CellEnergyForcingOperator a b →L[ℂ] CellFiniteEnergyDatum a b :=
  ContinuousLinearMap.apply ℂ (CellFiniteEnergyDatum a b) z

theorem cellEnergyForcingOperatorEval_ofCLM (a b : ℝ) (z : CellFiniteEnergyCarrier a b)
    (T : CellFiniteEnergyCarrier a b →L[ℂ] CellFiniteEnergyDatum a b) :
    cellEnergyForcingOperatorEvalCLM a b z (cellEnergyForcingOperatorOfCLM a b T) = T z := rfl

theorem cellEnergyForcingOperator_ext {a b : ℝ} (T U : CellEnergyForcingOperator a b)
    (h : ∀ z, cellEnergyForcingOperatorEvalCLM a b z T = cellEnergyForcingOperatorEvalCLM a b z U) :
    T = U := by
  apply ContinuousLinearMap.ext
  exact h

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set
namespace AVRegularity.CycleEvolution

/-! Source representatives of actual sums and frequency shifts of finite energy data. -/

theorem cellFiniteEnergyDatum_add_scalar_ae {a b : ℝ} (d e : CellFiniteEnergyDatum a b) :
    (d + e).2.1 =ᵐ[volume.restrict (Icc a b)] fun t => d.2.1 t + e.2.1 t := by
  filter_upwards [Lp.coeFn_add d.2.1 e.2.1] with t ht
  exact ht

theorem cellFiniteEnergyDatum_add_flux_ae {a b : ℝ} (d e : CellFiniteEnergyDatum a b) :
    ∀ᵐ t ∂volume.restrict (Icc a b), ∀ j : Fin 2,
      (d + e).2.2 j t = d.2.2 j t + e.2.2 j t := by
  rw [ae_all_iff]
  intro j
  filter_upwards [Lp.coeFn_add (d.2.2 j) (e.2.2 j)] with t ht
  exact ht

theorem cellBlochExternalDatum_scalar_ae {a b : ℝ} (δ : Fin 2 → ℂ)
    (d : CellFiniteEnergyDatum a b) :
    (cellBlochExternalDatum δ d).2.1 =ᵐ[volume.restrict (Icc a b)]
      fun t => d.2.1 t + ∑ j : Fin 2, (Complex.I * δ j) • d.2.2 j t := by
  have he := lpFiniteLinearCombination_ae (fun j => Complex.I * δ j) d.2.2
    (fun j t => d.2.2 j t) (fun _ => Filter.EventuallyEq.rfl)
  filter_upwards [Lp.coeFn_add d.2.1 (∑ j : Fin 2, (Complex.I * δ j) • d.2.2 j), he]
    with t ht he'
  change (d.2.1 + ∑ j : Fin 2, (Complex.I * δ j) • d.2.2 j) t = _
  rw [ht]
  simp only [Pi.add_apply]
  rw [he']

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CycleEvolution

/-! Actual evolution is additive on the complete complex energy and forcing carriers. -/

theorem IsCellFiniteEnergyEvolution.add {a b : ℝ}
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    {d e : CellFiniteEnergyDatum a b} {z w : CellFiniteEnergyCarrier a b}
    (hz : IsCellFiniteEnergyEvolution C hG V hv hb d z)
    (hw : IsCellFiniteEnergyEvolution C hG V hv hb e w) :
    IsCellFiniteEnergyEvolution C hG V hv hb (d + e) (z + w) := by
  obtain ⟨u, slice, hu, hiu, htu⟩ := hz
  obtain ⟨v, other, hv', hiv, htv⟩ := hw
  refine ⟨fun t => u t + v t, fun t => slice t + other t, (hu.add hv').dual_congr ?_, ?_, ?_⟩
  · have hf j := Lp.coeFn_add (d.2.2 j) (e.2.2 j)
    filter_upwards [Lp.coeFn_add d.2.1 e.2.1, ae_all_iff.mpr hf] with t hS hF
    have hs : d.2.1 t + e.2.1 t = (d + e).2.1 t := hS.symm
    have hh : (fun j => d.2.2 j t + e.2.2 j t) = (fun j => (d + e).2.2 j t) := by
      funext j
      exact (hF j).symm
    rw [← cellDualDerivative_add]
    change cellDualDerivative C hG V hv hb t (slice t + other t)
      (d.2.1 t + e.2.1 t) (fun j => d.2.2 j t + e.2.2 j t) = _
    rw [hs, hh]
  · change u a + v a = d.1 + e.1
    rw [hiu, hiv]
  · intro t
    change z.val.1 t + w.val.1 t = u t.val + v t.val
    rw [htu, htv]

end AVRegularity.CycleEvolution
end

section
namespace AVRegularity.CycleEvolution

/-! A bounded actual solution map sends bounded forcing operators into the complete cell operator algebra. -/

def cellEnergyEvolutionForcingLiftCLM (a b : ℝ)
    (sol : CellFiniteEnergyDatum a b →L[ℂ] CellFiniteEnergyCarrier a b) :
    CellEnergyForcingOperator a b →L[ℂ] CellEnergyOperator a b :=
  (cellEnergyOperatorOfCLM a b).comp
    (ContinuousLinearMap.compL ℂ (CellFiniteEnergyCarrier a b) (CellFiniteEnergyDatum a b)
      (CellFiniteEnergyCarrier a b) sol)

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Sharp actual Riesz energy dissipation on the kernel of any row close to the cell mean. -/

theorem cellBlochRowKernel_dual_dissipation (η Cw : ℝ) (hη0 : 0 ≤ η)
    (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : Cw * fibreNorm ξ + 1032 * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2 / 16)
    (t : ℝ) (u : TorusHk 1 ℂ) (ell : ComplexCellL2)
    (hell : ‖ell - cellConstantCLM 1‖ ≤ 1 / 16)
    (hker : cellComplexPair (torusHkValueCLM u)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap ell) = 0) :
    inner ℝ (cellDualDerivative
      ⟨fun t _ => G t, v, (fun j => (Real.sqrt η : ℂ) * ξ j), 0⟩
      hG V hv.1 hb t u 0 0) u ≤ -3 * Real.pi ^ 2 * ‖torusHkValueCLM u‖ ^ 2 := by
  have he := cellDualComplexPair_derivative
    ⟨fun t _ => G t, v, (fun j => (Real.sqrt η : ℂ) * ξ j), 0⟩
    hG V hv.1 hb t u u 0 (fun _ => 0)
  rw [cellComplexSource_zero, add_zero] at he
  have hr := congrArg Complex.re he
  rw [cellDualComplexPair_re, cellComplexGenerator_re] at hr
  have hm := cellRow_kernel_mean_bound ell (torusHkValueCLM u) (1 / 16) hell hker
  simpa only [show (fun _ : Fin 2 => (0 : ComplexCellL2)) = 0 from rfl] using
    hr.le.trans (cellBlochSmallMean_dissipation η Cw hη0 hη hCw G hG hg hgsmall
      hv hw V hb ξ hξ t u hm)

/-! Projecting the mean equation from a normalized graph preserves a uniform forced gap. -/

theorem cellBloch_projected_feedback_forced_energy (η Cw : ℝ) (hη0 : 0 ≤ η)
    (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (L Cr : ℝ)
    (hsmall : Cw * fibreNorm ξ + (1032 + L + Cr * Cw) * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2)
    (t : ℝ) (u : TorusHk 1 ℂ) (hm : cellMean (torusHkValueCLM u) = 0)
    (lam : ℂ) (hlam : ‖lam‖ ≤ L * fibreNorm ξ ^ 2)
    (ρ : ComplexCellL2) (hρ : ‖ρ‖ ≤ Cr * fibreNorm ξ) (hρsmall : ‖ρ‖ ≤ 1)
    (hξsmall : fibreNorm ξ ≤ 1)
    (hθ : ∀ j, ‖(Real.sqrt η : ℂ) * ξ j‖ ≤ fibreNorm ξ)
    (F : Fin 2 → ComplexCellL2) :
    2 * inner ℝ (cellDualDerivative
      ⟨fun t _ => G t, v, (fun j => (Real.sqrt η : ℂ) * ξ j), 0⟩
      hG V hv.1 hb t u 0 F -
      cellPivotDualCLM (cellScalarCLM lam (torusHkValueCLM u)) -
      cellPivotDualCLM (cellScalarCLM
        (-Complex.I * cellBlochDriftMeanCLM η Cw hCw hv hw ξ t (torusHkValueCLM u) +
          ∑ j : Fin 2, Complex.I * ((Real.sqrt η : ℂ) * ξ j) * cellMean (F j))
        (ρ + cellConstantCLM 1))) u +
      (Real.pi ^ 2 / 2) * ‖torusHkValueCLM u‖ ^ 2 +
      (1 / 4) * ∑ j, ‖cellDerivativeCLM j u‖ ^ 2 ≤
      14 * ∑ j, ‖F j‖ ^ 2 := by
  let c := -Complex.I * cellBlochDriftMeanCLM η Cw hCw hv hw ξ t (torusHkValueCLM u)
  let f := ∑ j : Fin 2, Complex.I * ((Real.sqrt η : ℂ) * ξ j) * cellMean (F j)
  have hbnd := cellBlochDriftMean_feedback_norm_le η Cw hCw hv hw ξ t (torusHkValueCLM u) ρ Cr hρ
  have he := cellBloch_normalized_feedback_forced_energy η Cw hη0 hη hCw G hG hg hgsmall
    hv hw V hb ξ L (Cr * Cw) hsmall t u hm lam hlam (cellScalarCLM c ρ) hbnd
    (fun j => (hθ j).trans hξsmall) 0 F
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add] at he
  have hnorm := cellBloch_flux_mean_graph_source_norm_le
    (fun j => (Real.sqrt η : ℂ) * ξ j) (fibreNorm ξ) hθ F ρ hρsmall hξsmall
  have hsplit : cellScalarCLM (c + f) (ρ + cellConstantCLM 1) =
      cellScalarCLM c ρ + cellScalarCLM f ρ + cellScalarCLM (c + f) (cellConstantCLM 1) := by
    simp only [cellScalarCLM_smul, smul_add, add_smul]
  have hinner : inner ℝ (cellPivotDualCLM (cellScalarCLM (c + f) (ρ + cellConstantCLM 1))) u =
      inner ℝ (cellPivotDualCLM (cellScalarCLM c ρ)) u +
        inner ℝ (cellPivotDualCLM (cellScalarCLM f ρ)) u := by
    rw [hsplit, map_add, map_add, inner_add_left, inner_add_left,
      cellMeanZero_constant_pivot_inner_zero (c + f) u hm, add_zero]
  have hy := hilbertScalarSource_young (-cellScalarCLM f ρ) (torusHkValueCLM u)
  simp only [inner_neg_left, norm_neg] at hy
  have hp : 2 ≤ Real.pi ^ 2 := by nlinarith [Real.two_le_pi]
  have hp' := mul_le_mul_of_nonneg_right hp (sq_nonneg ‖torusHkValueCLM u‖)
  change 2 * inner ℝ (cellDualDerivative
    ⟨fun t _ => G t, v, (fun j => (Real.sqrt η : ℂ) * ξ j), 0⟩
    hG V hv.1 hb t u 0 F - cellPivotDualCLM (cellScalarCLM lam (torusHkValueCLM u)) -
    cellPivotDualCLM (cellScalarCLM (c + f) (ρ + cellConstantCLM 1))) u + _ + _ ≤ _
  rw [inner_sub_left, inner_sub_left, hinner]
  rw [inner_sub_left, inner_sub_left] at he
  simp only [cellPivotDualCLM, ContinuousLinearMap.adjoint_inner_left] at he ⊢
  change ‖cellScalarCLM f ρ‖ ^ 2 ≤ _ at hnorm
  linarith

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization
namespace AVRegularity.CycleEvolution

/-! A finite operator bound for the actual cell evolution in the complete energy carrier. -/

theorem cellFiniteEnergyEvolution_norm_bound {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (hκb : ∀ t, ‖C.κ t‖ ≤ k)
    (d : CellFiniteEnergyDatum a b) (z : CellFiniteEnergyCarrier a b)
    (hz : IsCellFiniteEnergyEvolution C hG V hv hb d z) :
    ‖z‖ ≤ Real.sqrt (20 * (b - a + 2) *
      Real.exp (300 * (1 + ∑ j, ‖C.θ j‖ ^ 2 + V ^ 2 + k) * (b - a))) * ‖d‖ := by
  obtain ⟨u, slice, hu, hi, ht⟩ := hz
  let E := Real.exp (300 * (1 + ∑ j, ‖C.θ j‖ ^ 2 + V ^ 2 + k) * (b - a))
  let W := (‖d.1‖ ^ 2 + ∫ s in a..b, ‖d.2.1 s‖ ^ 2 + 9 * ∑ j, ‖d.2.2 j s‖ ^ 2) * E
  have he := cellActualWeak_state_energy_bound hab C hG V k hv hb hκb
    (fun t => d.2.1 t) (fun t j => d.2.2 j t) (Lp.memLp _) (fun j => Lp.memLp _)
    u slice hu
  dsimp only at he
  rw [hi] at he
  change (∀ t ∈ Icc a b, ‖u t‖ ^ 2 ≤ W) ∧ (∫ t in a..b, ‖slice t‖ ^ 2) ≤ (b - a + 2) * W at he
  have hW : 0 ≤ W := (sq_nonneg ‖u a‖).trans (he.1 a ⟨le_rfl, hab⟩)
  have hL : 1 ≤ b - a + 2 := by linarith
  have hn := cellFiniteEnergyCarrier_norm_sq_le hab u slice _ hu z ht W ((b - a + 2) * W)
    hW he.1 he.2
  rw [max_eq_right (le_mul_of_one_le_left hW hL)] at hn
  have hbudget := cellFiniteEnergyDatum_budget_le hab d
  have hWE : W ≤ 20 * ‖d‖ ^ 2 * E := mul_le_mul_of_nonneg_right hbudget (Real.exp_pos _).le
  have hsq : ‖z‖ ^ 2 ≤ (20 * (b - a + 2) * E) * ‖d‖ ^ 2 := by
    calc
      ‖z‖ ^ 2 ≤ (b - a + 2) * W := hn
      _ ≤ (b - a + 2) * (20 * ‖d‖ ^ 2 * E) := mul_le_mul_of_nonneg_left hWE (by linarith)
      _ = _ := by ring
  have hK : 0 ≤ 20 * (b - a + 2) * E := mul_nonneg (by linarith) (Real.exp_pos _).le
  have hr : 0 ≤ Real.sqrt (20 * (b - a + 2) * E) * ‖d‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hr2 : (Real.sqrt (20 * (b - a + 2) * E) * ‖d‖) ^ 2 =
      (20 * (b - a + 2) * E) * ‖d‖ ^ 2 := by rw [mul_pow, Real.sq_sqrt hK]
  change ‖z‖ ≤ Real.sqrt (20 * (b - a + 2) * E) * ‖d‖
  exact (sq_le_sq₀ (norm_nonneg _) hr).mp (hsq.trans_eq hr2.symm)

end AVRegularity.CycleEvolution
end

section
namespace AVRegularity.CycleEvolution

/-! Lifted energy operators evaluate as the actual bounded solution map applied to forcing. -/

theorem cellEnergyEvolutionForcingLift_apply (a b : ℝ)
    (sol : CellFiniteEnergyDatum a b →L[ℂ] CellFiniteEnergyCarrier a b)
    (T : CellEnergyForcingOperator a b) (z : CellEnergySpace a b) :
    cellEnergyOperatorApplyCLM a b (cellEnergyEvolutionForcingLiftCLM a b sol T) z =
      sol (cellEnergyForcingOperatorEvalCLM a b z T) := rfl

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Any raw representative of the actual carrier solution satisfies the cell equation
`IsCellSolution`. -/

theorem cellEnergySpaceRaw_isCellSolution {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (d : CellFiniteEnergyDatum a b) (z : CellEnergySpace a b)
    (hS : d.2.1 =ᵐ[volume.restrict (Icc a b)] fun t => cellSourceSlice src t)
    (hflux : ∀ j : Fin 2, d.2.2 j =ᵐ[volume.restrict (Icc a b)]
      fun t => cellSourceSlice (fun s x => F s x j) t)
    (hz : IsCellFiniteEnergyEvolution C hG V hv hb d z)
    (D : ℝ → RawJet2 1 ℂ) (hD : IsCellEnergySpaceRawRepresentative hab z D) :
    IsCellSolution (Icc a b) C src F D := by
  obtain ⟨u, slice, hu, _, ht⟩ := hz
  have hr := cellFiniteEnergyTimeStateCLM_ae hab u slice _ hu z ht
  have hj : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ j,
      ((slice t).val j : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] D t j := by
    filter_upwards [hr, hD.2.2.2.1] with t hr' hd
    simpa only [cellEnergySpaceState, hr'] using hd
  have htr : ∀ t ∈ Icc a b, (u t : Vec 2 → ℂ)
      =ᵐ[volume.restrict AVenhance.unitCube] cellValue D t := by
    intro t hmem
    have he : cellEnergySpaceTrace hab z t = u t := by
      unfold cellEnergySpaceTrace
      rw [projIcc_of_mem hab hmem]
      exact ht ⟨t, hmem⟩
    exact he ▸ hD.2.1 t
  have hw : CellWeakHilbertCurve a b u slice (fun t => cellDualDerivative C hG V hv hb t
      (slice t) (cellSourceSlice src t) (fun j => cellSourceSlice (fun s x => F s x j) t)) := by
    apply hu.dual_congr
    filter_upwards [hS, ae_all_iff.mpr hflux] with t hs hf
    rw [hs]
    congr 1
    funext j
    exact hf j
  refine ⟨ordConnected_Icc, hD.1, ?_, ?_, ?_, ?_, ?_⟩
  · intro t hmem
    exact ⟨(Lp.memLp (u t)).ae_eq (htr t hmem), hD.2.2.2.2 t _⟩
  · intro j
    exact (hD.2.2.1 j).aestronglyMeasurable
  · exact cellRaw_trace_continuous (Icc a b) u hu.trace (cellValue D) htr
  · intro s hs t ht'
    exact cellRawGradient_energy_finite D hD.2.2.1 s hs t ht'
  · intro s hs t ht' hst ψ
    exact cellWeakHilbert_raw_identity C hG V hv hb src F hsrc hF u slice hw D htr hj s hs t ht' hst ψ

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Sharp squared-energy decay for every actual homogeneous weak Bloch curve in a small row kernel. -/

theorem cellWeakBloch_rowKernel_decay {a b : ℝ} (hab : a ≤ b)
    (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : Cw * fibreNorm ξ + 1032 * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2 / 16)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice (fun t => cellDualDerivative
      ⟨fun t _ => G t, v, (fun j => (Real.sqrt η : ℂ) * ξ j), 0⟩
      hG V hv.1 hb t (slice t) 0 0))
    (ell : ℝ → ComplexCellL2) (hell : ∀ t ∈ Icc a b,
      ‖ell t - cellConstantCLM 1‖ ≤ 1 / 16)
    (hker : ∀ t ∈ Icc a b, cellComplexPair (u t)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (ell t)) = 0) :
    ∀ t ∈ Icc a b, ‖u t‖ ^ 2 ≤
      Real.exp (-(6 * Real.pi ^ 2) * (t - a)) * ‖u a‖ ^ 2 := by
  apply (h.energy_strongTime hab).scalar_decay hab (6 * Real.pi ^ 2)
  filter_upwards [h.agrees, ae_restrict_mem measurableSet_Icc] with t ht hti
  have hk := hker t hti
  rw [ht] at hk
  have hd := cellBlochRowKernel_dual_dissipation η Cw hη0 hη hCw G hG hg hgsmall
    hv hw V hb ξ hξ t (slice t) (ell t) (hell t hti) hk
  rw [ht]
  linarith

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Raw representatives preserve the literal initial L2 trace of actual complete-energy evolution. -/

theorem cellEnergySpaceRaw_initial_ae {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (d : CellFiniteEnergyDatum a b) (z : CellEnergySpace a b)
    (hz : IsCellFiniteEnergyEvolution C hG V hv hb d z)
    (D : ℝ → RawJet2 1 ℂ) (hD : IsCellEnergySpaceRawRepresentative hab z D) :
    cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] d.1 := by
  obtain ⟨u, _, _, hi, ht⟩ := hz
  have he : cellEnergySpaceTrace hab z a = d.1 := by
    unfold cellEnergySpaceTrace
    rw [projIcc_of_mem hab ⟨le_rfl, hab⟩]
    exact (ht ⟨a, le_rfl, hab⟩).trans hi
  have ha := (hD.2.1 a).symm
  rw [he] at ha
  exact ha

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Homogeneous projected normalized curves have a uniform exponential gap. -/

theorem cellWeak_projected_feedback_decay {a b : ℝ} (hab : a ≤ b)
    (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (L Cr : ℝ)
    (hsmall : Cw * fibreNorm ξ + (1032 + L + Cr * Cw) * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2)
    (hξsmall : fibreNorm ξ ≤ 1)
    (hθ : ∀ j, ‖(Real.sqrt η : ℂ) * ξ j‖ ≤ fibreNorm ξ)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (lam : ℝ → ℂ) (hlam : ∀ t, ‖lam t‖ ≤ L * fibreNorm ξ ^ 2)
    (ρ : ℝ → ComplexCellL2) (hρ : ∀ t, ‖ρ t‖ ≤ Cr * fibreNorm ξ)
    (hρsmall : ∀ t, ‖ρ t‖ ≤ 1)
    (h : CellWeakHilbertCurve a b u slice (fun t => cellDualDerivative
      ⟨fun t _ => G t, v, (fun j => (Real.sqrt η : ℂ) * ξ j), 0⟩
      hG V hv.1 hb t (slice t) 0 (fun _ => 0) -
      cellPivotDualCLM (cellScalarCLM (lam t) (torusHkValueCLM (slice t))) -
      cellPivotDualCLM (cellScalarCLM
        (-Complex.I * cellBlochDriftMeanCLM η Cw hCw hv hw ξ t (torusHkValueCLM (slice t)) +
          ∑ j : Fin 2, Complex.I * ((Real.sqrt η : ℂ) * ξ j) * cellMean (0 : ComplexCellL2))
        (ρ t + cellConstantCLM 1))))
    (hm : ∀ t ∈ Icc a b, cellMean (u t) = 0) :
    ∀ t ∈ Icc a b,
      ‖u t‖ ^ 2 ≤ Real.exp (-(Real.pi ^ 2 / 2) * (t - a)) * ‖u a‖ ^ 2 := by
  apply (h.energy_strongTime hab).scalar_decay hab (Real.pi ^ 2 / 2)
  filter_upwards [h.agrees, ae_restrict_mem measurableSet_Icc] with t ht hti
  have hmean := hm t hti
  rw [ht] at hmean
  have hbnd := cellBloch_projected_feedback_forced_energy η Cw hη0 hη hCw G hG hg hgsmall
    hv hw V hb ξ L Cr hsmall t (slice t) hmean (lam t) (hlam t) (ρ t) (hρ t)
    (hρsmall t) hξsmall hθ (fun _ => 0)
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, mul_zero] at hbnd
  have hgrad : 0 ≤ (1 / 4 : ℝ) * ∑ j, ‖cellDerivativeCLM j (slice t)‖ ^ 2 := by positivity
  rw [ht]
  linarith

end AVRegularity.CycleEvolution
end
end
end
