-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleEvolution.FibreCoefficientGraphModeRatio
import AVRegularity.CycleEvolution.CellInverseJetFactorialBound
import AVRegularity.CycleEvolution.CellEnergySpaceRawDirectionalLimit
public import AVRegularity.CycleEvolution.FibreCoefficientFamilyMajorant
import AVRegularity.CycleEvolution.CellEnergySpaceRawJetCauchyBound
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Time measurability of the actual symbol follows from its metric and spatial-mean formula. -/

theorem fibreQuad_time_measurable {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : IsCellMetric (fun t _ => G t)) (ξ : Fin 2 → ℂ) :
    Measurable (fun t => fibreQuad (G t) ξ) := by
  unfold fibreQuad
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  have hm : Measurable (fun t => G t i j) :=
    (cellMetric_entry_measurable hG i j).comp (measurable_id.prodMk (measurable_const : Measurable (fun _ : ℝ => (0 : Vec 2))))
  exact (measurable_const.mul (Complex.continuous_ofReal.measurable.comp hm)).mul_const (ξ j)

theorem fibreCoefficientFamily_symbol_aestronglyMeasurable (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    AEStronglyMeasurable (fibreSeriesC (fibreCoefficientSymbol η G v r) ξ)
      (volume.restrict Set.univ) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  have hi := fibreCoefficientFamily_graph_isInverse η Cw hη hCw G hG hv hw ξ hξ
  have hp : AEStronglyMeasurable (fun p : ℝ × Vec 2 =>
      fibreDriftCoupling η v ξ p.1 p.2 * cellValue (fibreSeriesJet r ξ) p.1 p.2)
      ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)) :=
    (fibreDriftCoupling_measurable η hv ξ).aestronglyMeasurable.mul
      (hi.1.2.2.2.1 (valueIndex2 1))
  have hm := cellMean_aestronglyMeasurable (I := Set.univ)
    (f := fun t x => fibreDriftCoupling η v ξ t x * cellValue (fibreSeriesJet r ξ) t x) hp
  have hq : AEStronglyMeasurable (fun t => fibreQuad (G t) ξ) (volume.restrict Set.univ) :=
    (fibreQuad_time_measurable hG ξ).aestronglyMeasurable
  have hs : AEStronglyMeasurable (fun t => -(η : ℂ) * fibreQuad (G t) ξ -
      Complex.I * cellMean (fun x => fibreDriftCoupling η v ξ t x *
        cellValue (fibreSeriesJet r ξ) t x)) (volume.restrict Set.univ) :=
    (aestronglyMeasurable_const.mul hq).sub (aestronglyMeasurable_const.mul hm)
  apply hs.congr
  exact Filter.Eventually.of_forall (fun t =>
    (fibreCoefficientFamily_symbol_series η Cw hη hCw G hG hv hw ξ hξ t).symm)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The constructed graph is an actual mean-zero flux evolution throughout a quiet interval. -/

theorem fibreCoefficientFamily_quiet_weak_evolution (η Cw : ℝ)
    (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw)
    {a b : ℝ} (hab : a ≤ b)
    (hquiet : ∀ t ∈ Icc a b, ∀ x, v t x = 0) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let D := fibreSeriesJet r ξ
    CellWeakHilbertCurve a b (cellRawTrace D) (cellH1Slice D)
      (fun t => cellDualDerivative ⟨fun t _ => G t, v, 0, 0⟩ hG V hv.1 hb t
        (cellH1Slice D t) 0
        (cellNormalizedGraphFluxClass G (fun j => (Real.sqrt η : ℂ) * ξ j) t
          (cellH1Slice D t))) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let D := fibreSeriesJet r ξ
  have hi := fibreCoefficientFamily_graph_isInverse η Cw hη hCw G hG hv hw ξ hξ
  have hGm : Measurable G := hG.1.comp
    (measurable_id.prodMk (measurable_const (a := (0 : Vec 2))))
  have he (t : ℝ) (i j : Fin 2) : |G t i j| ≤ 2 :=
    cellMetric_entry_bound hG t 0 i j
  have hs := fibreGraphSource_interval_memLp η Cw hv hw ξ hi a b
  have hF := fibreGraphFlux_interval_memLp η hη G hGm he ξ hi a b
  have hr := cellSolution_restrict (Set.subset_univ (Icc a b)) ordConnected_Icc hi.1
  have hh := cellSolution_to_Hilbert hab ⟨fun t _ => G t, v, 0, 0⟩ hG V 0 hv.1 hb
    measurable_const (fun _ => by simp) _ _ hs hF D hr
  apply hh.dual_congr
  have ht := hi.1.2.1.filter_mono (ae_mono
    (Measure.restrict_mono (Set.subset_univ (Icc a b)) le_rfl))
  filter_upwards [ht, ae_restrict_mem measurableSet_Icc] with t ht hti
  change cellDualDerivative _ hG V hv.1 hb t (cellH1Slice D t) _ _ = _
  have hsrc : cellSourceSlice (fibreGraphSource η v ξ (cellValue D)) t = 0 := by
    apply cellSourceSlice_eq_of_ae
    have hz := fibreGraphSource_quiet η v ξ (cellValue D) t (hquiet t hti)
    rw [hz]
    exact Lp.coeFn_zero (E := ℂ) (p := 2) (μ := volume.restrict AVenhance.unitCube)
  have hflux : (fun j => cellSourceSlice
      (fun s x => fibreGraphFlux η G ξ (cellValue D) s x j) t) =
      cellNormalizedGraphFluxClass G (fun j => (Real.sqrt η : ℂ) * ξ j) t
        (cellH1Slice D t) := by
    funext j
    exact cellH1Slice_graph_flux_slice η G ξ D t ht j
  rw [hsrc, hflux]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped BigOperators
namespace AVRegularity.CycleEvolution

/-! Each actual symbol coefficient is almost strongly measurable in time. -/

theorem fibreCoefficientFamily_symbol_coefficient_aestronglyMeasurable
    (η Cw : ℝ) (hη : η ≤ 1) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) (p : ℕ × ℕ) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    AEStronglyMeasurable (fibreCoefficientSymbol η G v r p)
      (volume.restrict Set.univ) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  have hmetric : Measurable (fibreCoefficientMetricSymbol η G p) := by
    unfold fibreCoefficientMetricSymbol
    apply measurable_const.mul
    apply Finset.measurable_sum
    intro i _
    apply Finset.measurable_sum
    intro j _
    split_ifs
    · exact Complex.continuous_ofReal.measurable.comp
        ((cellMetric_entry_measurable hG i j).comp
          (measurable_id.prodMk (measurable_const : Measurable (fun _ : ℝ => (0 : Vec 2)))))
    · exact measurable_const
  have hdrift : AEStronglyMeasurable (fibreCoefficientDriftSymbol η v r p)
      (volume.restrict Set.univ) := by
    have hj (j : Fin 2) : AEStronglyMeasurable (fun t => -Complex.I *
        cellMean (fun x => fibreDriftCoupling η v (fibreCoordinateFrequency j) t x *
          cellValue (r (fibreCoefficientPrevious p j)) t x)) (volume.restrict Set.univ) := by
      apply aestronglyMeasurable_const.mul
      apply cellMean_aestronglyMeasurable
      have hi := fibreCoefficientFamily_isInverse η Cw hη G hG hv hw
        (fibreCoefficientPrevious p j)
      exact (fibreDriftCoupling_measurable η hv (fibreCoordinateFrequency j)).aestronglyMeasurable.mul
        (hi.1.2.2.2.1 (valueIndex2 1))
    apply (Finset.aestronglyMeasurable_sum (fibreCoefficientDirections p)
      (fun j _ => hj j)).congr
    exact Filter.Eventually.of_forall (fun t => by
      simp only [fibreCoefficientDriftSymbol, Finset.sum_apply])
  exact hmetric.aestronglyMeasurable.add hdrift

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The actual scalar symbol is the quadratic metric term plus the drift mean of the genuine graph correction class. -/

theorem fibreCoefficientFamily_symbol_class (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) (t : ℝ) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    fibreSeriesC (fibreCoefficientSymbol η G v r) ξ t =
      -(η : ℂ) * fibreQuad (G t) ξ -
      Complex.I * cellBlochDriftMeanCLM η Cw hCw hv hw ξ t (cellRawTrace (fibreSeriesJet r ξ) t) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let D := fibreSeriesJet r ξ
  have hi := fibreCoefficientFamily_graph_isInverse η Cw hη hCw G hG hv hw ξ hξ
  have hp := cellRawTrace_ae D t (hi.1.2.2.1 t (mem_univ t)).1
  have hm : cellBlochDriftMeanCLM η Cw hCw hv hw ξ t (cellRawTrace D t) =
      cellMean (fun x => fibreDriftCoupling η v ξ t x * cellValue D t x) := by
    rw [cellBlochDriftMeanCLM_apply]
    unfold cellMean
    apply integral_congr_ae
    filter_upwards [hp] with x hx
    rw [hx]
  change fibreSeriesC (fibreCoefficientSymbol η G v r) ξ t = _
  rw [fibreCoefficientFamily_symbol_series η Cw hη hCw G hG hv hw ξ hξ t, hm]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The constructed graph source has the exact scalar part of the normalized Bloch equation. -/

theorem fibreCoefficientFamily_graph_source_equation (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v) (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) (t : ℝ) (x : Vec 2) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let ρ := cellValue (fibreSeriesJet r ξ)
    fibreGraphSource η v ξ ρ t x =
      -Complex.I * fibreDriftCoupling η v ξ t x * (1 + ρ t x) -
        ((η : ℂ) * fibreQuad (G t) ξ + fibreSeriesC (fibreCoefficientSymbol η G v r) ξ t) *
          (1 + ρ t x) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let ρ := cellValue (fibreSeriesJet r ξ)
  have hi := fibreCoefficientFamily_graph_isInverse η Cw hη hCw G hG hv hw ξ hξ
  have hr : MemLp (ρ t) 2 (volume.restrict AVenhance.unitCube) :=
    (hi.1.2.2.1 t (Set.mem_univ t)).1
  have hl : fibreSeriesC (fibreCoefficientSymbol η G v r) ξ t =
      -(η : ℂ) * fibreQuad (G t) ξ - Complex.I *
        cellMean (fun y => fibreDriftCoupling η v ξ t y * ρ t y) :=
    fibreCoefficientFamily_symbol_series η Cw hη hCw G hG hv hw ξ hξ t
  change fibreGraphSource η v ξ ρ t x =
    -Complex.I * fibreDriftCoupling η v ξ t x * (1 + ρ t x) -
      ((η : ℂ) * fibreQuad (G t) ξ + fibreSeriesC (fibreCoefficientSymbol η G v r) ξ t) *
        (1 + ρ t x)
  rw [fibreGraphSource_normalized η Cw hv hw hm ξ ρ t hr x, hl]
  ring

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped BigOperators NNReal ENNReal
namespace AVRegularity.CycleEvolution

/-! The actual graph symbol supplies every analytic-majorant premise. -/

def fibreCoefficientMajorantNNRadius (Cw : ℝ) (hCw : 0 ≤ Cw) : ℝ≥0 :=
  ⟨fibreCoefficientMajorantRadius Cw, (fibreCoefficientMajorantRadius_pos hCw).le⟩

theorem fibreCoefficientFamily_symbol_analytic_majorant (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) :
    let a := fibreCoefficientSymbol η G v (fibreCoefficientFamily η Cw hη G hG hv hw)
    let R := fibreCoefficientMajorantNNRadius Cw hCw
    (∀ p, AEStronglyMeasurable (a p) volume) ∧
    (∑' p, fibreCoefficientWeight (R : ENNReal) p * ⨆ τ, ‖a p τ‖ₑ) ≤
      ENNReal.ofReal (6 * Cw + 24) ∧
    (∀ p, p.1 + p.2 = 1 → ∀ τ, a p τ = 0) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro p
    simpa only [Measure.restrict_univ] using
      fibreCoefficientFamily_symbol_coefficient_aestronglyMeasurable η Cw hη G hG hv hw p
  · have he : (fibreCoefficientMajorantNNRadius Cw hCw : ENNReal) =
        ENNReal.ofReal (fibreCoefficientMajorantRadius Cw) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      rfl
    rw [he]
    exact fibreCoefficientFamily_weighted_symbol_le η Cw hη0 hη hCw G hG hv hw
  · intro p hp τ
    exact fibreCoefficientFamily_symbol_low_order η Cw hη G hG hv hw p hp.le τ

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The normalized graph source class represents the constructed graph forcing. -/

theorem fibreCoefficientFamily_graph_source_class_ae (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw)
    (t : ℝ)
    (ht : HasPeriodicOrderedWeakJet
      (fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hw) ξ t)) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let D := fibreSeriesJet r ξ
    cellNormalizedGraphSourceClass G v V hv hb
      (fun j => (Real.sqrt η : ℂ) * ξ j)
      (fun s => -fibreSeriesC (fibreCoefficientSymbol η G v r) ξ s) t (cellH1Slice D t)
      =ᵐ[volume.restrict AVenhance.unitCube]
        fibreGraphSource η v ξ (cellValue D) t := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let D := fibreSeriesJet r ξ
  filter_upwards [cellNormalizedGraphSourceClass_bloch_ae η hη0 G hv V hb ξ
    (fibreSeriesC (fibreCoefficientSymbol η G v r) ξ) t (cellH1Slice D t),
    cellH1Slice_value_ae D t ht] with x hs hx
  rw [hs, hx]
  exact (fibreCoefficientFamily_graph_source_equation η Cw hη hCw G hG hv hm hw ξ hξ t x).symm

/-! Identification of the constructed graph source as the actual total L² source slice. -/

theorem fibreCoefficientFamily_graph_source_slice (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw)
    (t : ℝ)
    (ht : HasPeriodicOrderedWeakJet
      (fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hw) ξ t)) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let D := fibreSeriesJet r ξ
    cellSourceSlice (fibreGraphSource η v ξ (cellValue D)) t =
      cellNormalizedGraphSourceClass G v V hv hb
        (fun j => (Real.sqrt η : ℂ) * ξ j)
        (fun s => -fibreSeriesC (fibreCoefficientSymbol η G v r) ξ s) t (cellH1Slice D t) := by
  apply cellSourceSlice_eq_of_ae
  exact fibreCoefficientFamily_graph_source_class_ae η Cw hη0 hη hCw G hG
    hv hm hw V hb ξ hξ t ht

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.CycleEvolution

/-! The constructed scalar symbol is an actual bounded measurable potential on every finite interval. -/

theorem fibreCoefficientFamily_symbol_memLp_top (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) (a b : ℝ) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    MemLp (fibreSeriesC (fibreCoefficientSymbol η G v r) ξ) ⊤ (volume.restrict (Icc a b)) := by
  have hm := fibreCoefficientFamily_symbol_aestronglyMeasurable η Cw hη hCw G hG hv hw ξ hξ
  have hm' := hm.mono_measure (Measure.restrict_mono (subset_univ (Icc a b)) le_rfl)
  exact MemLp.of_bound hm' ((6 * Cw + 24) * (fibreNorm ξ / fibreCoefficientMajorantRadius Cw) ^ 2)
    (Filter.Eventually.of_forall (fibreCoefficientFamily_symbol_quadratic_bound
      η Cw hη0 hη hCw G hG hv hw ξ hξ))

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! An actual convergent fibre graph and symbol constructed from the literal inverse coefficients. -/

/-- A graph bound depending only on the scaled drift bound. -/
def fibreCoefficientGraphBound (Cw : ℝ) : ℝ :=
  2 * (fibreCoefficientMajorantRadius Cw)⁻¹ + (6 * Cw + 24) + 2

/-- The literal coefficient construction gives the complete public fibre graph predicate. -/
theorem fibreCoefficientFamily_isFibreGraph (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    IsFibreGraph η G v (fibreCoefficientMajorantRadius Cw) (fibreCoefficientGraphBound Cw)
      r (fibreCoefficientSymbol η G v r) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let R := fibreCoefficientMajorantRadius Cw
  let C := fibreCoefficientGraphBound Cw
  have hR : 0 < R := fibreCoefficientMajorantRadius_pos hCw
  have hRi : 0 ≤ R⁻¹ := (inv_pos.mpr hR).le
  have hK : 0 ≤ 6 * Cw + 24 := by positivity
  have heC : C = 2 * R⁻¹ + (6 * Cw + 24) + 2 := rfl
  have h2 : 2 ≤ C := by rw [heC]; linarith
  have hC0 : 2 * R⁻¹ ≤ C := by rw [heC]; linarith
  have hCK : 6 * Cw + 24 ≤ C := by rw [heC]; linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fibreCoefficientFamily_symbol_low_order η Cw hη G hG hv hw
  · intro ξ hξ
    have hξ' : fibreNorm ξ ≤ R := hξ.le
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact ((fibreMonomial_weighted_energy_le R ξ hξ' _).trans
        (fibreCoefficientFamily_weighted_energy_le η Cw hη hCw G hG hv hw)).trans_lt (by simp)
    · exact fibreCoefficientFamily_symbol_series_absolute η Cw hη0 hη hCw G hG hv hw ξ hξ'
    · exact fibreCoefficientFamily_graph_isInverse η Cw hη hCw G hG hv hw ξ hξ'
    · intro t
      exact fibreCoefficientFamily_symbol_series η Cw hη hCw G hG hv hw ξ hξ' t
    · apply (fibreCoefficientFamily_summed_energy_le η Cw hη hCw G hG hv hw ξ hξ').trans
      have ht : (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) := by norm_num
      rw [ht, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      apply ENNReal.ofReal_le_ofReal
      change 2 * (fibreNorm ξ / R) ≤ C * fibreNorm ξ
      have he : 2 * (fibreNorm ξ / R) = (2 * R⁻¹) * fibreNorm ξ := by
        rw [div_eq_mul_inv]
        ring
      rw [he]
      exact mul_le_mul_of_nonneg_right hC0 (fibreNorm_nonneg ξ)
  · intro n ξ
    apply (fibreCoefficientFamily_homogeneous_energy_le η Cw hη hCw G hG hv hw n ξ).trans
    apply ENNReal.ofReal_le_ofReal
    change 2 * (2 * R⁻¹) ^ n * fibreNorm ξ ^ n ≤ C * (2 / R) ^ n * fibreNorm ξ ^ n
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right h2 (by positivity)) (pow_nonneg (fibreNorm_nonneg ξ) n)
  · intro n ξ t
    apply (fibreCoefficientFamily_symbol_homogeneous_le η Cw hη0 hη hCw G hG hv hw n ξ t).trans
    change (6 * Cw + 24) * (2 * R⁻¹) ^ n * fibreNorm ξ ^ n ≤ C * (2 / R) ^ n * fibreNorm ξ ^ n
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCK (by positivity)) (pow_nonneg (fibreNorm_nonneg ξ) n)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! A literal quantitative quiet-past buffer for the actual constructed graph. -/

theorem fibreCoefficientFamily_quiet_past (η Cw : ℝ) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 1024)
    (s a : ℝ) (ha : 0 ≤ a) (hquiet : ∀ t ∈ Icc (s - a) s, ∀ x, v t x = 0) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    cellL2Norm (cellValue (fibreSeriesJet r ξ) s) ≤
      ENNReal.ofReal ((2 / fibreCoefficientMajorantRadius Cw) * fibreNorm ξ *
        Real.exp (-(2 * Real.pi ^ 2) * a)) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let D := fibreSeriesJet r ξ
  have hR := fibreCoefficientMajorantRadius_pos hCw
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := by linarith
  have hi := fibreCoefficientFamily_graph_isInverse η Cw hη hCw G hG hv hw ξ hξR
  obtain ⟨V, hb⟩ := hv.2.1
  have hab : s - a ≤ s := by linarith
  have hh := fibreCoefficientFamily_quiet_weak_evolution η Cw hη hCw G hG hv hw
    V hb ξ hξR hab hquiet
  have hfreq : 1024 * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2 / 16 := by
    have hf := fibreKernel_frequency_small hCw ξ hξ
    have hp := mul_nonneg hCw (fibreNorm_nonneg ξ)
    nlinarith [sq_nonneg (fibreNorm ξ)]
  have hmean : ∀ t ∈ Icc (s - a) s, cellMean (cellRawTrace D t) = 0 := by
    intro t _
    exact (integral_congr_ae (cellRawTrace_ae D t (hi.1.2.2.1 t (mem_univ t)).1)).trans
      (hi.2.1 t)
  have hd := cellWeakGraphFlux_meanZero_decay hab η hη G hG hg hgsmall hv V hb ξ hfreq
    (cellRawTrace D) (cellH1Slice D) hh hmean s ⟨hab, le_rfl⟩
  rw [show s - (s - a) = a by ring] at hd
  have hsqt : ‖cellRawTrace D s‖ ^ 2 ≤
      Real.exp (-(2 * (3 * Real.pi ^ 2)) * a) * ‖cellRawTrace D (s - a)‖ ^ 2 := by
    simpa only [show (2 : ℝ) * (3 * Real.pi ^ 2) = 6 * Real.pi ^ 2 by ring] using hd
  have hn := scalar_sharp_norm_decay (norm_nonneg (cellRawTrace D s))
    (norm_nonneg (cellRawTrace D (s - a))) hsqt
  have hcmp : -(3 * Real.pi ^ 2) * a ≤ -(2 * Real.pi ^ 2) * a := by
    have hp := mul_nonneg (sq_nonneg Real.pi) ha
    linarith
  have hnorm : ‖cellRawTrace D s‖ ≤ Real.exp (-(2 * Real.pi ^ 2) * a) *
      ‖cellRawTrace D (s - a)‖ := hn.trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hcmp) (norm_nonneg _))
  have he0 := fibreCoefficientFamily_summed_energy_le η Cw hη hCw G hG hv hw ξ hξR
  have hinit : ENNReal.ofReal ‖cellRawTrace D (s - a)‖ ≤
      2 * ENNReal.ofReal (fibreNorm ξ / fibreCoefficientMajorantRadius Cw) := by
    rw [← cellL2Norm_eq_of_class (cellValue D (s - a)) (cellRawTrace D (s - a))
      (cellRawTrace_ae D (s - a) (hi.1.2.2.1 (s - a) (mem_univ _)).1)]
    exact (cellValue_cellL2Norm_le_energy D (s - a)).trans he0
  change cellL2Norm (cellValue D s) ≤ _
  rw [cellL2Norm_eq_of_class (cellValue D s) (cellRawTrace D s)
    (cellRawTrace_ae D s (hi.1.2.2.1 s (mem_univ s)).1)]
  calc
    _ ≤ ENNReal.ofReal (Real.exp (-(2 * Real.pi ^ 2) * a) *
        ‖cellRawTrace D (s - a)‖) := ENNReal.ofReal_le_ofReal hnorm
    _ = ENNReal.ofReal (Real.exp (-(2 * Real.pi ^ 2) * a)) *
        ENNReal.ofReal ‖cellRawTrace D (s - a)‖ :=
      ENNReal.ofReal_mul (Real.exp_pos _).le
    _ ≤ ENNReal.ofReal (Real.exp (-(2 * Real.pi ^ 2) * a)) *
        (2 * ENNReal.ofReal (fibreNorm ξ / fibreCoefficientMajorantRadius Cw)) :=
      mul_le_mul' le_rfl hinit
    _ = _ := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      ring

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Actual normalized forced raw curves have the genuine weak Hilbert equation for L² fluxes. -/

theorem fibreCoefficient_raw_forced_to_Hilbert {a b : ℝ} (hab : a ≤ b)
    (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let C := fibreCoefficients η G v ξ (fibreSeriesC (fibreCoefficientSymbol η G v r) ξ)
    ∀ F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ),
      MemLp (Function.uncurry F) 2 ((volume.restrict (Icc a b)).prod
        (volume.restrict AVenhance.unitCube)) →
      ∀ D : ℝ → RawJet2 1 ℂ,
      IsCellSolution (Icc a b) C (fun _ _ => 0) F D →
      CellWeakHilbertCurve a b (cellRawTrace D) (cellH1Slice D)
        (fun t => cellDualDerivative C hG V hv.1 hb t (cellH1Slice D t) 0
          (fun j => cellSourceSlice (fun r x => F r x j) t)) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let lam := fibreSeriesC (fibreCoefficientSymbol η G v r) ξ
  let C := fibreCoefficients η G v ξ lam
  let k := (6 * Cw + 24) * (fibreNorm ξ / fibreCoefficientMajorantRadius Cw) ^ 2
  dsimp only
  intro F hF D h
  have hl := fibreCoefficientFamily_symbol_memLp_top η Cw hη0 hη hCw G hG hv hw ξ hξ a b
  have hκ : AEStronglyMeasurable C.κ (volume.restrict (Icc a b)) :=
    hl.aestronglyMeasurable.neg
  have hκb : ∀ t, ‖C.κ t‖ ≤ k := by
    intro t
    change ‖-lam t‖ ≤ k
    rw [norm_neg]
    exact fibreCoefficientFamily_symbol_quadratic_bound η Cw hη0 hη hCw G hG hv hw ξ hξ t
  have hh := cellSolution_to_Hilbert_aePotential hab C hG V k hv.1 hb hκ hκb
    (fun _ _ => 0) F MemLp.zero hF D h
  change CellWeakHilbertCurve a b (cellRawTrace D) (cellH1Slice D)
    (fun t => cellDualDerivative C hG V hv.1 hb t (cellH1Slice D t)
      (cellSourceSlice (fun _ _ => 0) t) (fun j => cellSourceSlice (fun r x => F r x j) t)) at hh
  simpa only [cellSourceSlice_zero] using hh

/-! Every actual normalized homogeneous raw curve has the genuine weak Hilbert equation. -/

theorem fibreCoefficient_raw_homogeneous_to_Hilbert {a b : ℝ} (hab : a ≤ b)
    (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let C := fibreCoefficients η G v ξ (fibreSeriesC (fibreCoefficientSymbol η G v r) ξ)
    ∀ D : ℝ → RawJet2 1 ℂ,
      IsCellSolution (Icc a b) C (fun _ _ => 0) (fun _ _ => 0) D →
      CellWeakHilbertCurve a b (cellRawTrace D) (cellH1Slice D)
        (fun t => cellDualDerivative C hG V hv.1 hb t (cellH1Slice D t) 0 (fun _ => 0)) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let lam := fibreSeriesC (fibreCoefficientSymbol η G v r) ξ
  let C := fibreCoefficients η G v ξ lam
  let k := (6 * Cw + 24) * (fibreNorm ξ / fibreCoefficientMajorantRadius Cw) ^ 2
  dsimp only
  intro D h
  have hl := fibreCoefficientFamily_symbol_memLp_top η Cw hη0 hη hCw G hG hv hw ξ hξ a b
  have hκ : AEStronglyMeasurable C.κ (volume.restrict (Icc a b)) :=
    hl.aestronglyMeasurable.neg
  have hκb : ∀ t, ‖C.κ t‖ ≤ k := by
    intro t
    change ‖-lam t‖ ≤ k
    rw [norm_neg]
    exact fibreCoefficientFamily_symbol_quadratic_bound η Cw hη0 hη hCw G hG hv hw ξ hξ t
  exact cellRawHomogeneous_to_Hilbert_aePotential hab C hG V k hv.1 hb hκ hκb D h

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped BigOperators NNReal ENNReal
namespace AVRegularity.CycleEvolution

/-! Actual symbol coefficients in L-infinity time, and their Banach-valued analytic family. -/

theorem fibreCoefficientFamily_symbol_coefficient_memLp_top (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) (p : ℕ × ℕ) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    MemLp (fibreCoefficientSymbol η G v r p) ⊤ volume := by
  have hdata := fibreCoefficientFamily_symbol_analytic_majorant η Cw hη0 hη hCw G hG hv hw
  have hR := fibreCoefficientMajorantRadius_pos hCw
  apply memLp_top_of_bound (hdata.1 p)
    ((6 * Cw + 24) * (fibreCoefficientMajorantRadius Cw)⁻¹ ^ (p.1 + p.2))
  apply Filter.Eventually.of_forall
  intro t
  have he := (le_iSup (fun τ => ‖fibreCoefficientSymbol η G v
      (fibreCoefficientFamily η Cw hη G hG hv hw) p τ‖ₑ) t).trans
    (fibreCoefficientFamily_symbol_individual_le η Cw hη0 hη hCw G hG hv hw p)
  rw [← ofReal_norm] at he
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp he

theorem fibreCoefficientFamily_symbol_lpTop_analyticOnNhd (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) :
    let a := fibreCoefficientSymbol η G v (fibreCoefficientFamily η Cw hη G hG hv hw)
    let hm := fibreCoefficientFamily_symbol_coefficient_memLp_top η Cw hη0 hη hCw G hG hv hw
    AnalyticOnNhd ℂ (fun ξ : Fin 2 → ℂ => ∑' p, fibreMonomial ξ p • (hm p).toLp (a p))
      (Metric.ball 0 (fibreCoefficientMajorantRadius Cw)) := by
  dsimp only
  let R := fibreCoefficientMajorantNNRadius Cw hCw
  have hR : 0 < R := fibreCoefficientMajorantRadius_pos hCw
  have hdata := fibreCoefficientFamily_symbol_analytic_majorant η Cw hη0 hη hCw G hG hv hw
  have ha := fibreLpTopSeries_analyticOnNhd
    (fibreCoefficientSymbol η G v (fibreCoefficientFamily η Cw hη G hG hv hw)) R hR
    (hdata.2.1.trans_lt ENNReal.ofReal_lt_top)
    (fibreCoefficientFamily_symbol_coefficient_memLp_top η Cw hη0 hη hCw G hG hv hw)
  have hreal : (R : ℝ) = fibreCoefficientMajorantRadius Cw := rfl
  rw [hreal] at ha
  exact ha

/-! Identification of the actual analytic L-infinity normalization potential with the literal graph symbol. -/

theorem fibreCoefficientFamily_symbol_lpTop_ae (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) :
    let a := fibreCoefficientSymbol η G v (fibreCoefficientFamily η Cw hη G hG hv hw)
    let hm := fibreCoefficientFamily_symbol_coefficient_memLp_top η Cw hη0 hη hCw G hG hv hw
    (⇑(∑' p, fibreMonomial ξ p • (hm p).toLp (a p)) : ℝ → ℂ) =ᵐ[volume] fibreSeriesC a ξ := by
  dsimp only
  have hdata := fibreCoefficientFamily_symbol_analytic_majorant η Cw hη0 hη hCw G hG hv hw
  let R := fibreCoefficientMajorantNNRadius Cw hCw
  have hreal : (R : ℝ) = fibreCoefficientMajorantRadius Cw := rfl
  apply fibreLpTopSeries_ae _ R (hdata.2.1.trans_lt ENNReal.ofReal_lt_top)
    (fibreCoefficientFamily_symbol_coefficient_memLp_top η Cw hη0 hη hCw G hG hv hw) ξ
  rw [hreal]
  exact (fibrePiNorm_le ξ).trans hξ

/-! Actual phase derivative bounds, uniform in contrast, metric and drift data. -/

theorem fibreCoefficientFamily_phase_iteratedFDeriv_le (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (s t : ℝ) (hst : s ≤ t) (n : ℕ) (ξ : Fin 2 → ℂ)
    (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 2) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    ‖iteratedFDeriv ℂ n (fun ξ' : Fin 2 → ℂ =>
      ∫ τ in s..t, fibreSeriesC (fibreCoefficientSymbol η G v r) ξ' τ) ξ‖ ≤
      analyticBallDerivativeConstant n * ((6 * Cw + 24) * (t - s)) /
        (fibreCoefficientMajorantRadius Cw / 2) ^ n := by
  have hdata := fibreCoefficientFamily_symbol_analytic_majorant η Cw hη0 hη hCw G hG hv hw
  let R := fibreCoefficientMajorantNNRadius Cw hCw
  have hR : 0 < R := fibreCoefficientMajorantRadius_pos hCw
  have hreal : (R : ℝ) = fibreCoefficientMajorantRadius Cw := rfl
  have hξ' : ‖ξ‖ ≤ (R : ℝ) / 2 := by rw [hreal]; exact (fibrePiNorm_le ξ).trans hξ
  have hn := fibreUniformMajorant_phase_iteratedFDeriv_le
    (fibreCoefficientSymbol η G v (fibreCoefficientFamily η Cw hη G hG hv hw)) R hR
    (6 * Cw + 24) (by positivity) hdata.1 hdata.2.1 s t hst n ξ hξ'
  rw [hreal] at hn
  exact hn

theorem fibreCoefficientFamily_phase_first_derivative_le (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (s t : ℝ) (hst : s ≤ t) (ξ : Fin 2 → ℂ)
    (hξ : fibreNorm ξ < fibreCoefficientMajorantRadius Cw / 2) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    ‖fderiv ℂ (fun ξ' : Fin 2 → ℂ =>
      ∫ τ in s..t, fibreSeriesC (fibreCoefficientSymbol η G v r) ξ' τ) ξ‖ ≤
      (8 * ((6 * Cw + 24) * (t - s)) / fibreCoefficientMajorantRadius Cw ^ 2) * fibreNorm ξ := by
  have hdata := fibreCoefficientFamily_symbol_analytic_majorant η Cw hη0 hη hCw G hG hv hw
  let R := fibreCoefficientMajorantNNRadius Cw hCw
  have hR : 0 < R := fibreCoefficientMajorantRadius_pos hCw
  have hreal : (R : ℝ) = fibreCoefficientMajorantRadius Cw := rfl
  have hξ' : ‖ξ‖ < (R : ℝ) / 2 := by rw [hreal]; exact (fibrePiNorm_le ξ).trans_lt hξ
  have hn := fibreUniformMajorant_phase_first_derivative_le
    (fibreCoefficientSymbol η G v (fibreCoefficientFamily η Cw hη G hG hv hw)) R hR
    (6 * Cw + 24) (by positivity) hdata.1 hdata.2.1 hdata.2.2 s t hst ξ hξ'
  rw [hreal] at hn
  apply hn.trans
  apply mul_le_mul_of_nonneg_left (fibrePiNorm_le ξ)
  positivity

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! The literal normalization symbol as an analytic bounded time coefficient class. -/

def fibreCoefficientSymbolTimeClass (I : Set ℝ) (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) : Lp ℂ ∞ (volume.restrict I) :=
  lpComplexMeasureRestriction ∞ Measure.restrict_le_self
    (∑' p, fibreMonomial ξ p •
      (fibreCoefficientFamily_symbol_coefficient_memLp_top η Cw hη0 hη hCw G hG hv hw p).toLp
        (fibreCoefficientSymbol η G v (fibreCoefficientFamily η Cw hη G hG hv hw) p))

theorem fibreCoefficientSymbolTimeClass_analyticAt (I : Set ℝ) (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : ‖ξ‖ < fibreCoefficientMajorantRadius Cw) :
    AnalyticAt ℂ (fibreCoefficientSymbolTimeClass I η Cw hη0 hη hCw G hG hv hw) ξ := by
  apply lpComplexMeasureRestriction_analyticAt
  apply fibreCoefficientFamily_symbol_lpTop_analyticOnNhd η Cw hη0 hη hCw G hG hv hw
  simpa only [Metric.mem_ball, dist_zero_right] using hξ

theorem fibreCoefficientSymbolTimeClass_ae (I : Set ℝ) (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw) :
    fibreCoefficientSymbolTimeClass I η Cw hη0 hη hCw G hG hv hw ξ
      =ᵐ[volume.restrict I] fibreSeriesC
        (fibreCoefficientSymbol η G v (fibreCoefficientFamily η Cw hη G hG hv hw)) ξ := by
  exact (lpComplexMeasureRestriction_ae ∞ Measure.restrict_le_self _).trans
    ((Measure.absolutelyContinuous_of_le Measure.restrict_le_self).ae_eq
      (fibreCoefficientFamily_symbol_lpTop_ae η Cw hη0 hη hCw G hG hv hw ξ hξ))

/-! Actual changes of the normalization potential are analytic and vanish at the base frequency. -/

theorem fibreCoefficientSymbolTimeDifference_analyticAt (I : Set ℝ) (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : ‖ξ‖ < fibreCoefficientMajorantRadius Cw) :
    AnalyticAt ℂ (fun ζ => -fibreCoefficientSymbolTimeClass I η Cw hη0 hη hCw G hG hv hw ζ +
      fibreCoefficientSymbolTimeClass I η Cw hη0 hη hCw G hG hv hw ξ) ξ :=
  (fibreCoefficientSymbolTimeClass_analyticAt I η Cw hη0 hη hCw G hG hv hw ξ hξ).neg.add
    analyticAt_const

theorem fibreBlochFrequencyDifference_analyticAt (η : ℝ) (ξ : Fin 2 → ℂ) :
    AnalyticAt ℂ (fun ζ : Fin 2 → ℂ => (Real.sqrt η : ℂ) • (ζ - ξ)) ξ := by
  simpa only [Pi.smul_def, Pi.sub_def, id_eq] using
    (analyticAt_id.sub (analyticAt_const (v := ξ))).const_smul (c := (Real.sqrt η : ℂ))

theorem fibreBlochFrequencyDifference_zero (η : ℝ) (ξ : Fin 2 → ℂ) :
    (Real.sqrt η : ℂ) • (ξ - ξ) = 0 := by rw [sub_self, smul_zero]

/-! The analytic potential difference class has exactly the literal normalization-symbol difference as representative. -/

theorem fibreCoefficientSymbolTimeDifference_ae (I : Set ℝ) (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ ζ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw)
    (hζ : fibreNorm ζ ≤ fibreCoefficientMajorantRadius Cw) :
    let Q := fibreCoefficientSymbolTimeClass I η Cw hη0 hη hCw G hG hv hw
    let lam := fibreCoefficientSymbol η G v (fibreCoefficientFamily η Cw hη G hG hv hw)
    (-Q ζ + Q ξ : Lp ℂ ∞ (volume.restrict I)) =ᵐ[volume.restrict I]
      fun t => -fibreSeriesC lam ζ t + fibreSeriesC lam ξ t := by
  dsimp only
  let Q := fibreCoefficientSymbolTimeClass I η Cw hη0 hη hCw G hG hv hw
  filter_upwards [Lp.coeFn_add (-Q ζ) (Q ξ), Lp.coeFn_neg (Q ζ),
    fibreCoefficientSymbolTimeClass_ae I η Cw hη0 hη hCw G hG hv hw ξ hξ,
    fibreCoefficientSymbolTimeClass_ae I η Cw hη0 hη hCw G hG hv hw ζ hζ]
    with t ht hn hx hz
  rw [ht]
  simp only [Pi.add_apply]
  rw [hn]
  simp only [Pi.neg_apply]
  rw [hx, hz]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped BigOperators
namespace AVRegularity.CycleEvolution

/-! The actual phase satisfies the frequency-word estimate with the prescribed time normalization. -/

theorem fibreCoefficientFamily_phase_word_bound (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (S : ℝ) (hS : 1 ≤ S) (s₀ s t : ℝ) (hs : s₀ ≤ s) (hst : s ≤ t) (ht : t ≤ s₀ + S)
    (n : ℕ) (j : Fin n → Fin 2) (hn : 1 ≤ n) (ξ : Fin 2 → ℂ)
    (hξ : fibreNorm ξ < fibreCoefficientMajorantRadius Cw / 2) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    ‖iteratedFDeriv ℂ n (fun ξ' : Fin 2 → ℂ =>
        ∫ τ in s..t, fibreSeriesC (fibreCoefficientSymbol η G v r) ξ' τ) ξ
        (fun i => Pi.single (j i) (1 : ℂ))‖ ≤
      fibrePhaseJetConstant Cw n * Real.sqrt S ^ n *
        (if n = 1 then Real.sqrt S * fibreNorm ξ else 1) := by
  dsimp only
  let f : (Fin 2 → ℂ) → ℂ := fun ξ' => ∫ τ in s..t,
    fibreSeriesC (fibreCoefficientSymbol η G v (fibreCoefficientFamily η Cw hη G hG hv hw)) ξ' τ
  have hδ : t - s ≤ S := by linarith
  have hR := fibreCoefficientMajorantRadius_pos hCw
  have hK : 0 ≤ fibrePhaseJetConstant Cw n := (fibrePhaseJetConstant_pos hCw n).le
  have heval : ‖iteratedFDeriv ℂ n f ξ (fun i => Pi.single (j i) (1 : ℂ))‖ ≤
      ‖iteratedFDeriv ℂ n f ξ‖ := by
    simpa only [Finset.prod_const_one, mul_one] using
      (iteratedFDeriv ℂ n f ξ).le_opNorm_mul_prod_of_le (b := fun _ => (1 : ℝ))
        (fun _ => by simp only [Pi.norm_single, norm_one]; exact le_rfl)
  by_cases h1 : n = 1
  · subst n
    simp only [pow_one, ite_true]
    rw [norm_iteratedFDeriv_one] at heval
    have hb := fibreCoefficientFamily_phase_first_derivative_le
      η Cw hη0 hη hCw G hG hv hw s t hst ξ hξ
    have heq : (8 * ((6 * Cw + 24) * (t - s)) / fibreCoefficientMajorantRadius Cw ^ 2) *
        fibreNorm ξ = fibrePhaseJetConstant Cw 1 * (t - s) * fibreNorm ξ := by
      simp only [fibrePhaseJetConstant, ite_true]
      ring
    rw [heq] at hb
    exact (heval.trans hb).trans
      (phase_time_first_order_scaling S (t - s) (fibrePhaseJetConstant Cw 1) (fibreNorm ξ)
        (by linarith) hδ hK (fibreNorm_nonneg ξ))
  · simp only [h1, ite_false, mul_one]
    have h2 : 2 ≤ n := by omega
    have hb := fibreCoefficientFamily_phase_iteratedFDeriv_le
      η Cw hη0 hη hCw G hG hv hw s t hst n ξ hξ.le
    have heq : analyticBallDerivativeConstant n * ((6 * Cw + 24) * (t - s)) /
        (fibreCoefficientMajorantRadius Cw / 2) ^ n = fibrePhaseJetConstant Cw n * (t - s) := by
      simp only [fibrePhaseJetConstant, h1, ite_false]
      ring
    rw [heq] at hb
    exact (heval.trans hb).trans
      (phase_time_high_order_scaling S (t - s) (fibrePhaseJetConstant Cw n) hS hδ hK n h2)

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! The constructed graph is stable against every small identity-metric graph in the public predicate. -/

theorem fibreCoefficientFamily_metric_stability (η Cw : ℝ) (hη0 : 0 ≤ η)
    (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (g : ℝ) (hg0 : 0 ≤ g) (hg : IsMetricNearIdentity (fun t _ => G t) g)
    (ξ₀ C : ℝ) (r' : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (lam' : ℕ × ℕ → ℝ → ℂ)
    (hgraph : IsFibreGraph η (fun _ => 1) v ξ₀ C r' lam')
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ < ξ₀)
    (hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 2)
    (hξ1 : fibreNorm ξ ≤ 1) (hCξ : C * fibreNorm ξ ≤ 1)
    (hsmall : 13 * (4 * Cw + 8) * fibreNorm ξ ≤ 1 / 2) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreCoefficientSymbol η G v r
    cellEnergyNorm Set.univ (fibreSeriesJet r ξ - fibreSeriesJet r' ξ) ≤
        ENNReal.ofReal ((312 / fibreCoefficientMajorantRadius Cw) * g * fibreNorm ξ) ∧
      ∀ t, ‖fibreSeriesC lam ξ t - fibreSeriesC lam' ξ t‖ ≤
        (4 + Cw * (312 / fibreCoefficientMajorantRadius Cw)) * g * fibreNorm ξ ^ 2 := by
  let R := fibreCoefficientMajorantRadius Cw
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let D := fibreSeriesJet r ξ
  let E := fibreSeriesJet r' ξ
  have hξ0 := fibreNorm_nonneg ξ
  have hR : 0 < R := fibreCoefficientMajorantRadius_pos hCw
  have hξR' : fibreNorm ξ ≤ R := hξR.trans (by linarith)
  have hD := fibreCoefficientFamily_graph_isInverse η Cw hη hCw G hG hv hw ξ hξR'
  have hh := hgraph.2.1 ξ hξ
  have hE := hh.2.2.1
  have hde : cellEnergyNorm Set.univ D ≤ ENNReal.ofReal ((2 / R) * fibreNorm ξ) := by
    have hn := fibreCoefficientFamily_summed_energy_le η Cw hη hCw G hG hv hw ξ hξR'
    have he : 2 * ENNReal.ofReal (fibreNorm ξ / R) =
        ENNReal.ofReal ((2 / R) * fibreNorm ξ) := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      ring
    exact hn.trans_eq he
  have hnum : (2 / R) * fibreNorm ξ ≤ 1 := by
    have h : 2 * fibreNorm ξ / R ≤ 1 := (div_le_iff₀ hR).mpr (by linarith)
    convert h using 1
    ring
  have hd1 : cellEnergyNorm Set.univ D ≤ 1 :=
    hde.trans ((ENNReal.ofReal_le_ofReal hnum).trans_eq (by norm_num))
  have he1 : cellEnergyNorm Set.univ E ≤ 1 :=
    hh.2.2.2.2.trans ((ENNReal.ofReal_le_ofReal hCξ).trans_eq (by norm_num))
  have hentries : ∀ t i j, |(G t - 1) i j| ≤ g :=
    fun t i j => cellMetric_near_identity_entry_bound hG hg t 0 i j
  have hb := fibreGraph_metric_stability η Cw hη G (fun _ => 1) hG cellIdentityMetric
    hv hw g hg0 hentries ξ D E hD hE hCw hξ1 hd1 he1 hsmall
  have hdist : cellEnergyNorm Set.univ (D - E) ≤
      ENNReal.ofReal ((312 / R) * g * fibreNorm ξ) := by
    apply hb.trans
    calc
      _ ≤ 156 * ENNReal.ofReal g * ENNReal.ofReal ((2 / R) * fibreNorm ξ) := by gcongr
      _ = _ := by
        rw [show (156 : ℝ≥0∞) = ENNReal.ofReal 156 by norm_num,
          ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
  refine ⟨hdist, ?_⟩
  intro t
  rw [fibreCoefficientFamily_symbol_series η Cw hη hCw G hG hv hw ξ hξR' t,
    hh.2.2.2.1 t]
  exact fibreSymbol_metric_stability η Cw hη0 hη hCw G (fun _ => 1) hv hw
    g (312 / R) hg0 (by positivity) hentries ξ hD hE hdist t

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The actual constructed graph raw derivative is the normalized Bloch derivative almost everywhere. -/

theorem fibreCoefficientFamily_graph_raw_dual_ae (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw)
    (a b : ℝ) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let D := fibreSeriesJet r ξ
    cellRawSolutionDual ⟨fun t _ => G t, v, 0, 0⟩ hG V hv.1 hb
      (fibreGraphSource η v ξ (cellValue D)) (fibreGraphFlux η G ξ (cellValue D)) D
      =ᵐ[volume.restrict (Icc a b)]
      fun t => cellDualDerivative
        ⟨fun t _ => G t, v, fun j => (Real.sqrt η : ℂ) * ξ j,
          fun s => -fibreSeriesC (fibreCoefficientSymbol η G v r) ξ s⟩ hG V hv.1 hb t
        (cellH1Slice D t + cellH1One) 0 0 := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let D := fibreSeriesJet r ξ
  have hi := fibreCoefficientFamily_graph_isInverse η Cw hη hCw G hG hv hw ξ hξ
  have ht := hi.1.2.1.filter_mono (ae_mono
    (Measure.restrict_mono (Set.subset_univ (Icc a b)) le_rfl))
  filter_upwards [ht] with t ht
  change cellDualDerivative _ hG V hv.1 hb t (cellH1Slice D t) _ _ = _
  rw [fibreCoefficientFamily_graph_source_slice η Cw hη0 hη hCw G hG
    hv hm hw V hb ξ hξ t ht]
  have hf : (fun j => cellSourceSlice
      (fun s x => fibreGraphFlux η G ξ (cellValue D) s x j) t) =
      cellNormalizedGraphFluxClass G (fun j => (Real.sqrt η : ℂ) * ξ j)
        t (cellH1Slice D t) := by
    funext j
    exact cellH1Slice_graph_flux_slice η G ξ D t ht j
  rw [hf]
  exact (cellNormalizedGraph_dual G hG hv V hb _ _ t (cellH1Slice D t)).symm

end AVRegularity.CycleEvolution
end
