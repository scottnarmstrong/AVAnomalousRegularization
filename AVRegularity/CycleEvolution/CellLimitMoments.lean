-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.CellEnergySeriesRegularity
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Literal fibre X bounds follow from actual trace and shifted-gradient Hilbert budgets. -/

theorem cellSolution_fibreXNorm_le_of_state_bounds {a b : ℝ} (hab : a ≤ b)
    {C : CellCoefficients} {src : ℝ → Vec 2 → ℂ}
    {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {D : ℝ → RawJet2 1 ℂ}
    (h : IsCellSolution (Icc a b) C src F D) (θ : Fin 2 → ℂ)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (hu : ∀ t ∈ Icc a b, (u t : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] cellValue D t)
    (hs : MemLp slice 2 (volume.restrict (Icc a b)))
    (hj : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ j,
      ((slice t).val j : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] D t j)
    (A E : ℝ) (hA : 0 ≤ A) (hb : ∀ t ∈ Icc a b, ‖u t‖ ≤ A)
    (he : (∫ t in a..b, ∑ j, ‖cellShiftedDerivativeCLM θ j (slice t)‖ ^ 2) ≤ E) :
    fibreXNorm θ (Icc a b) D ≤ ENNReal.ofReal (A + Real.sqrt E) := by
  rw [cellSolution_fibreXNorm_of_state hab h θ u slice hu hs hj]
  calc
    _ ≤ ENNReal.ofReal A + ENNReal.ofReal (Real.sqrt E) := by
      apply add_le_add
      · apply iSup_le
        intro t
        apply iSup_le
        intro ht
        exact ENNReal.ofReal_le_ofReal (hb t ht)
      · exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt he)
    _ = _ := (ENNReal.ofReal_add hA (Real.sqrt_nonneg _)).symm

/-! Raw solution dual integrability for the almost measurable gauges of normalized fibres. -/

theorem cellSolution_dual_memLp_aePotential {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (hκ : AEStronglyMeasurable C.κ (volume.restrict (Icc a b))) (hκb : ∀ t, ‖C.κ t‖ ≤ k)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (D : ℝ → RawJet2 1 ℂ) (h : IsCellSolution (Icc a b) C src F D) :
    MemLp (cellRawSolutionDual C hG V hv hb src F D) 2 (volume.restrict (Icc a b)) :=
  cellDualDerivative_memLp_aePotential C hG V k hv hb hκ hκb (cellH1Slice D) (cellSolution_slice_memLp hab h)
    _ (cellSourceSlice_memLp (Icc a b) src hsrc) _
    (fun j => cellSourceSlice_memLp (Icc a b) (fun r x => F r x j)
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).comp_memLp' hF))

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Lower-order trace reality gives actual quadratic mean-multiplier forcing reality. -/

theorem fibreCoefficientQuadraticTerm_reality (η : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (D E : ℝ → RawJet2 1 ℂ) (p a : ℕ × ℕ) (j : Fin 2)
    (hj : j ∈ fibreCoefficientDirections p)
    (ha : a ∈ fibreCoefficientPairs (fibreCoefficientPrevious p j)) (t : ℝ)
    (hD : (fun x => star (cellValue D t x)) =ᵐ[volume.restrict AVenhance.unitCube]
      (fun x => fibreRealitySign a * cellValue D t x))
    (hE : (fun x => star (cellValue E t x)) =ᵐ[volume.restrict AVenhance.unitCube]
      (fun x => fibreRealitySign (fibreCoefficientComplement (fibreCoefficientPrevious p j) a) *
        cellValue E t x)) :
    (fun x => star (fibreCoefficientQuadraticTerm η v D E j t x)) =ᵐ[
      volume.restrict AVenhance.unitCube]
      (fun x => fibreRealitySign p * fibreCoefficientQuadraticTerm η v D E j t x) := by
  have hm := fibreCoordinateFrequency_mean_reality η v j t
    (fibreRealitySign (fibreCoefficientComplement (fibreCoefficientPrevious p j) a))
    (cellValue E t) hE
  have hs : fibreRealitySign p = -(fibreRealitySign a *
      fibreRealitySign (fibreCoefficientComplement (fibreCoefficientPrevious p j) a)) := by
    rw [fibreRealitySign_pair ha]
    exact fibreRealitySign_previous hj
  filter_upwards [hD] with x hx
  change star (Complex.I * cellValue D t x *
    cellMean (fun y => fibreDriftCoupling η v (fibreCoordinateFrequency j) t y * cellValue E t y)) =
    fibreRealitySign p * (Complex.I * cellValue D t x *
    cellMean (fun y => fibreDriftCoupling η v (fibreCoordinateFrequency j) t y * cellValue E t y))
  rw [star_mul, star_mul, show star Complex.I = -Complex.I from Complex.conj_I, hx, hm, hs]
  ring

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization
namespace AVRegularity.CycleEvolution

/-! Uniformly local bounds for the actual mean-free scalar and divergence forcing. -/

/-- The actual scalar and flux forcing budget on each unit window is controlled by the stated norms. -/
theorem cellUl_meanFree_forcing_window (I : Set ℝ) (f : ℝ → Vec 2 → ℂ)
    (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hfm : Measurable (Function.uncurry f)) (hFm : Measurable (Function.uncurry F))
    (hf : cellUlNorm I f < ⊤) (hF : cellUlNorm I F < ⊤) (a : ℝ) :
    (∫ t in Icc a (a + 1) ∩ I,
      ‖cellSourceSlice (fun r => cellQ0 (f r)) t‖ ^ 2 +
        8 * ∑ j, ‖cellSourceSlice (fun r x => F r x j) t‖ ^ 2) ≤
      4 * (cellUlNorm I f).toReal ^ 2 + 8 * (cellUlNorm I F).toReal ^ 2 := by
  let J := Icc a (a + 1) ∩ I
  have hp := cellSource_memLp_product J f hfm (cellUl_window_integral_lt_top I f hf a)
  have hq := cellSourceSlice_memLp J (fun r => cellQ0 (f r)) (cellQ0_memLp_product J f hfm hp)
  have hs := cellSourceSlice_memLp J f hp
  have hscalar : (∫ t in J, ‖cellSourceSlice (fun r => cellQ0 (f r)) t‖ ^ 2) ≤
      4 * (cellUlNorm I f).toReal ^ 2 := by
    have he := integral_mono_ae hq.norm.integrable_sq (hs.norm.integrable_sq.const_mul 4)
      (cellQ0_sourceSlice_normSq_ae J f hp)
    rw [integral_const_mul] at he
    exact he.trans (mul_le_mul_of_nonneg_left (cellUl_scalar_hilbert_window I f hfm hf a) (by norm_num))
  have hFP := cellSource_memLp_product J F hFm (cellUl_window_integral_lt_top I F hF a)
  have hj (j : Fin 2) := cellSourceSlice_memLp J (fun r x => F r x j)
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).comp_memLp' hFP)
  have hi : Integrable (fun t => ∑ j, ‖cellSourceSlice (fun r x => F r x j) t‖ ^ 2)
      (volume.restrict J) := by
    simpa only [Fin.sum_univ_two, Pi.add_def] using
      (hj 0).norm.integrable_sq.add (hj 1).norm.integrable_sq
  rw [integral_add hq.norm.integrable_sq (hi.const_mul 8), integral_const_mul]
  exact add_le_add hscalar
    (mul_le_mul_of_nonneg_left (cellUl_flux_hilbert_window I F hFm hF a) (by norm_num))

/-! The actual scalar mean forcing has the required square-root time cost. -/

theorem cellBloch_triangular_source_integral_bound {a b : ℝ} (hab : a ≤ b)
    (η Cw : ℝ) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (z : ℝ → ComplexCellL2)
    (hz : MemLp z 2 (volume.restrict (Icc a b)))
    (F : ℝ → Fin 2 → ComplexCellL2)
    (hF : ∀ j, MemLp (fun t => F t j) 2 (volume.restrict (Icc a b))) :
    ‖∫ t in a..b, -Complex.I * cellBlochDriftMeanCLM η Cw hCw hv hw ξ t (z t) +
      ∑ j : Fin 2, Complex.I * ((Real.sqrt η : ℂ) * ξ j) * cellMean (F t j)‖ ≤
      fibreNorm ξ * Real.sqrt (b - a) *
        (Cw * Real.sqrt (∫ t in a..b, ‖z t‖ ^ 2) +
          Real.sqrt (∫ t in a..b, ‖F t 0‖ ^ 2) + Real.sqrt (∫ t in a..b, ‖F t 1‖ ^ 2)) := by
  have hq := fibreNorm_nonneg ξ
  have hzint : IntervalIntegrable (fun t => ‖z t‖) volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    exact hz.norm.integrable (by norm_num)
  have hFint (j : Fin 2) : IntervalIntegrable (fun t => ‖F t j‖) volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    exact (hF j).norm.integrable (by norm_num)
  have hg : IntervalIntegrable (fun t => Cw * fibreNorm ξ * ‖z t‖ +
      fibreNorm ξ * (‖F t 0‖ + ‖F t 1‖)) volume a b :=
    (hzint.const_mul _).add (((hFint 0).add (hFint 1)).const_mul _)
  have hpoint (t : ℝ) :
      ‖-Complex.I * cellBlochDriftMeanCLM η Cw hCw hv hw ξ t (z t) +
        ∑ j : Fin 2, Complex.I * ((Real.sqrt η : ℂ) * ξ j) * cellMean (F t j)‖ ≤
          Cw * fibreNorm ξ * ‖z t‖ + fibreNorm ξ * (‖F t 0‖ + ‖F t 1‖) := by
    apply (norm_add_le _ _).trans
    apply add_le_add
    · simp only [norm_mul, norm_neg, Complex.norm_I, one_mul]
      exact cellBlochDriftMeanCLM_norm_le η Cw hCw hv hw ξ t (z t)
    · exact cellBloch_flux_mean_norm_le _ _ (fibreScaledFrequency_coordinate_le η hη ξ) (F t)
  have hbnd := intervalIntegral.norm_integral_le_of_norm_le hab
    (Filter.Eventually.of_forall (fun t _ => hpoint t)) hg
  apply hbnd.trans
  rw [intervalIntegral.integral_add (hzint.const_mul _) (((hFint 0).add (hFint 1)).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (hFint 0) (hFint 1)]
  calc
    _ ≤ Cw * fibreNorm ξ * (Real.sqrt (b - a) * Real.sqrt (∫ t in a..b, ‖z t‖ ^ 2)) +
        fibreNorm ξ * (Real.sqrt (b - a) * Real.sqrt (∫ t in a..b, ‖F t 0‖ ^ 2) +
          Real.sqrt (b - a) * Real.sqrt (∫ t in a..b, ‖F t 1‖ ^ 2)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (cellTime_integral_norm_le_sqrt hab z hz) (mul_nonneg hCw hq)
      · exact mul_le_mul_of_nonneg_left (add_le_add
          (cellTime_integral_norm_le_sqrt hab (fun t => F t 0) (hF 0))
          (cellTime_integral_norm_le_sqrt hab (fun t => F t 1) (hF 1))) hq
    _ = _ := by ring

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Conservation of the cell pairing for genuine forward and backward adjoint solutions. -/

theorem cellWeakAdjointPairing {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ) (hv : IsCellDrift C.v)
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    {u v : ℝ → ComplexCellL2} {slice other : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice (fun t =>
      cellDualDerivative C hG V hv.1 hb t (slice t) 0 (fun _ => 0)))
    (h' : CellWeakHilbertCurve a b v other (fun t =>
      -cellDualDerivative (cellAdjointCoefficients C) hG V (cellDrift_neg hv).1
        (cellDrift_neg_bound hb) t (other t) 0 (fun _ => 0))) :
    cellComplexPair (u b) (v b) = cellComplexPair (u a) (v a) := by
  have he := h.complex_pairing_increment hab h'
  have hz : (fun t =>
      cellDualComplexPair (cellDualDerivative C hG V hv.1 hb t (slice t) 0 (fun _ => 0))
        (other t) + star (cellDualComplexPair
          (-cellDualDerivative (cellAdjointCoefficients C) hG V (cellDrift_neg hv).1
            (cellDrift_neg_bound hb) t (other t) 0 (fun _ => 0)) (slice t))) =
      (fun _ : ℝ => (0 : ℂ)) := by
    funext t
    rw [cellDualComplexPair_neg,
      cellDualComplexPair_derivative C hG V hv.1 hb t (slice t) (other t) 0 (fun _ => 0),
      cellDualComplexPair_derivative (cellAdjointCoefficients C) hG V (cellDrift_neg hv).1
        (cellDrift_neg_bound hb) t (other t) (slice t) 0 (fun _ => 0), cellComplexSource_zero, cellComplexSource_zero,
      add_zero, add_zero, star_neg, cellComplexGenerator_opposite_drift C hG V hv hb]
    exact add_neg_cancel _
  rw [hz, intervalIntegral.integral_zero] at he
  exact sub_eq_zero.mp he

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Actual triangular scalar forcing has the coefficient parity dictated by minus-conjugate frequency. -/

theorem fibreCoefficientLinearSource_reality (η : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (D : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (p : ℕ × ℕ) (t : ℝ)
    (hD : ∀ a, a.1 + a.2 < p.1 + p.2 →
      (fun x => star (cellValue (D a) t x)) =ᵐ[volume.restrict AVenhance.unitCube]
        (fun x => fibreRealitySign a * cellValue (D a) t x)) :
    (fun x => star (fibreCoefficientLinearSource η v D p t x)) =ᵐ[
      volume.restrict AVenhance.unitCube]
      (fun x => fibreRealitySign p * fibreCoefficientLinearSource η v D p t x) := by
  have he : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ j ∈ fibreCoefficientDirections p,
      star (fibreCoefficientLinearTerm η v (D (fibreCoefficientPrevious p j)) p j t x) =
        fibreRealitySign p * fibreCoefficientLinearTerm η v (D (fibreCoefficientPrevious p j)) p j t x := by
    apply ae_all_iff.mpr
    intro j
    by_cases hj : j ∈ fibreCoefficientDirections p
    · have ho := fibreCoefficientPrevious_order hj
      exact (fibreCoefficientLinearTerm_reality η v _ p j hj t
        (hD _ (by omega))).mono (fun _ hx _ => hx)
    · exact Filter.Eventually.of_forall (fun _ h => (hj h).elim)
  filter_upwards [he] with x hx
  simp only [fibreCoefficientLinearSource, star_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact hx j hj

theorem fibreCoefficientQuadraticSource_reality (η : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (D : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (p : ℕ × ℕ) (t : ℝ)
    (hD : ∀ a, a.1 + a.2 < p.1 + p.2 →
      (fun x => star (cellValue (D a) t x)) =ᵐ[volume.restrict AVenhance.unitCube]
        (fun x => fibreRealitySign a * cellValue (D a) t x)) :
    (fun x => star (fibreCoefficientQuadraticSource η v D p t x)) =ᵐ[
      volume.restrict AVenhance.unitCube]
      (fun x => fibreRealitySign p * fibreCoefficientQuadraticSource η v D p t x) := by
  have he : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ j a,
      j ∈ fibreCoefficientDirections p → a ∈ fibreCoefficientPairs (fibreCoefficientPrevious p j) →
      star (fibreCoefficientQuadraticTerm η v (D a)
        (D (fibreCoefficientComplement (fibreCoefficientPrevious p j) a)) j t x) =
      fibreRealitySign p * fibreCoefficientQuadraticTerm η v (D a)
        (D (fibreCoefficientComplement (fibreCoefficientPrevious p j) a)) j t x := by
    apply ae_all_iff.mpr
    intro j
    apply ae_all_iff.mpr
    intro a
    by_cases hj : j ∈ fibreCoefficientDirections p
    · by_cases ha : a ∈ fibreCoefficientPairs (fibreCoefficientPrevious p j)
      · have ho := fibreCoefficientPairs_lower_orders hj ha
        exact (fibreCoefficientQuadraticTerm_reality η v _ _ p a j hj ha t
          (hD _ ho.1) (hD _ ho.2)).mono (fun _ hx _ _ => hx)
      · exact Filter.Eventually.of_forall (fun _ _ h => (ha h).elim)
    · exact Filter.Eventually.of_forall (fun _ h _ => (hj h).elim)
  filter_upwards [he] with x hx
  simp only [fibreCoefficientQuadraticSource, star_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro a ha
  exact hx j a hj ha

theorem fibreCoefficientSource_reality (η : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (D : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (p : ℕ × ℕ) (t : ℝ)
    (hD : ∀ a, a.1 + a.2 < p.1 + p.2 →
      (fun x => star (cellValue (D a) t x)) =ᵐ[volume.restrict AVenhance.unitCube]
        (fun x => fibreRealitySign a * cellValue (D a) t x)) :
    (fun x => star (fibreCoefficientSource η v D p t x)) =ᵐ[
      volume.restrict AVenhance.unitCube]
      (fun x => fibreRealitySign p * fibreCoefficientSource η v D p t x) := by
  filter_upwards [fibreCoefficientLinearSource_reality η v D p t hD,
    fibreCoefficientQuadraticSource_reality η v D p t hD] with x hl hq
  change star (fibreCoefficientLinearSource η v D p t x +
    fibreCoefficientQuadraticSource η v D p t x) = _
  rw [star_add, hl, hq]
  change _ = fibreRealitySign p * (fibreCoefficientLinearSource η v D p t x +
    fibreCoefficientQuadraticSource η v D p t x)
  ring

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! Admissibility of the literal vector graph source with a contrast-uniform bound. -/

/-- The coordinate coefficient of the actual graph flux is measurable in time. -/
theorem fibreGraphFlux_coefficient_measurable (η : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : Measurable G)
    (ξ : Fin 2 → ℂ) (k : Fin 2) :
    Measurable (fun t => 2 * Complex.I * (Real.sqrt η : ℂ) *
      ∑ j, (G t k j : ℂ) * ξ j) := by
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro j _
  exact (Complex.continuous_ofReal.measurable.comp
    ((measurable_pi_apply j).comp ((measurable_pi_apply k).comp hG))).mul_const (ξ j)

/-- The actual graph vector forcing is jointly almost measurable and bounded by the cell energy. -/
theorem fibreGraphFlux_ul_bound (η : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hGm : Measurable G)
    (hG : ∀ t i j, |G t i j| ≤ 2) (ξ : Fin 2 → ℂ)
    {C : CellCoefficients} {src : ℝ → Vec 2 → ℂ}
    {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {D : ℝ → RawJet2 1 ℂ}
    (hD : IsCellSolution univ C src F D) :
    cellUlNorm univ (fibreGraphFlux η G ξ (cellValue D)) ≤
      ENNReal.ofReal (8 * fibreNorm ξ) * cellEnergyNorm univ D ∧
    AEStronglyMeasurable (Function.uncurry (fibreGraphFlux η G ξ (cellValue D)))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) := by
  have hcoef := fibreGraphFlux_coefficient_measurable η G hGm ξ
  have hm (t : ℝ) : AEStronglyMeasurable (fibreGraphFlux η G ξ (cellValue D) t)
      (volume.restrict AVenhance.unitCube) := by
    apply cellFiniteArray_aestronglyMeasurable
    intro k
    exact aestronglyMeasurable_const.mul (hD.2.2.1 t (mem_univ t)).1.aestronglyMeasurable
  refine ⟨cellUlNorm_le_uniform_cellL2Norm _ _ (fun t => ?_), ?_⟩
  · apply (eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hm t)
      (Filter.Eventually.of_forall (fun x => fibreGraphFlux_norm_le η hη G hG ξ (cellValue D) t x)) 2).trans
    gcongr
    exact cellValue_cellL2Norm_le_energy D t
  · apply cellFiniteArray_aestronglyMeasurable
    intro k
    exact ((hcoef k).comp measurable_fst).aestronglyMeasurable.mul
      (hD.2.2.2.1 (valueIndex2 1))

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Every actual Bloch divergence-flux coordinate is uniformly bounded in contrast. -/

theorem cellNormalizedGraphFluxClass_norm_le (η : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (ξ : Fin 2 → ℂ) (t : ℝ) (u : TorusHk 1 ℂ) (j : Fin 2) :
    ‖cellNormalizedGraphFluxClass G (fun k => (Real.sqrt η : ℂ) * ξ k) t u j‖ ≤
      (8 * fibreNorm ξ) * ‖torusHkValueCLM u‖ := by
  apply cellL2Class_norm_le_of_ae_le_mul _ (mul_nonneg (by norm_num) (fibreNorm_nonneg ξ))
  filter_upwards [cellNormalizedGraphFluxClass_ae η G ξ t u j] with x hx
  rw [hx]
  calc
    _ ≤ ‖fibreGraphFlux η G ξ (fun _ y => torusHkValueCLM u y) t x‖ :=
      PiLp.norm_apply_le _ j
    _ ≤ _ := fibreGraphFlux_norm_le η hη G
      (fun s k l => cellMetric_entry_bound hG s 0 k l) ξ
      (fun _ y => torusHkValueCLM u y) t x

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization
namespace AVRegularity.CycleEvolution

/-! Local integrability and short-window bounds for the actual mean-free forcing budget. -/

/-- Squared scalar and flux norms appearing in the actual dissipative energy inequality. -/
def cellMeanFreeForcingBudget (f : ℝ → Vec 2 → ℂ)
    (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) (t : ℝ) : ℝ :=
  ‖cellSourceSlice (fun r => cellQ0 (f r)) t‖ ^ 2 +
    8 * ∑ j, ‖cellSourceSlice (fun r x => F r x j) t‖ ^ 2

/-- The actual forcing budget is nonnegative at every time, including exceptional slices. -/
theorem cellMeanFreeForcingBudget_nonneg (f : ℝ → Vec 2 → ℂ)
    (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) (t : ℝ) :
    0 ≤ cellMeanFreeForcingBudget f F t := by
  unfold cellMeanFreeForcingBudget
  positivity

/-- Product L² sources make the actual forcing budget genuinely integrable. -/
theorem cellMeanFreeForcingBudget_integrable (I : Set ℝ) (f : ℝ → Vec 2 → ℂ)
    (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hm : Measurable (Function.uncurry f))
    (hf : MemLp (Function.uncurry f) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    IntegrableOn (cellMeanFreeForcingBudget f F) I := by
  have hs := cellSourceSlice_memLp I (fun r => cellQ0 (f r)) (cellQ0_memLp_product I f hm hf)
  have hj (j : Fin 2) := cellSourceSlice_memLp I (fun r x => F r x j)
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).comp_memLp' hF)
  have hi : Integrable (fun t => ∑ j, ‖cellSourceSlice (fun r x => F r x j) t‖ ^ 2)
      (volume.restrict I) := by
    simpa only [Fin.sum_univ_two, Pi.add_def] using
      (hj 0).norm.integrable_sq.add (hj 1).norm.integrable_sq
  change Integrable (fun t => ‖cellSourceSlice (fun r => cellQ0 (f r)) t‖ ^ 2 +
    8 * ∑ j, ‖cellSourceSlice (fun r x => F r x j) t‖ ^ 2) (volume.restrict I)
  simpa only [Pi.add_def, Pi.mul_def] using hs.norm.integrable_sq.add (hi.const_mul 8)

/-- Every short interval in the time domain obeys the same uniform forcing bound. -/
theorem cellMeanFreeForcingBudget_short_bound (I : Set ℝ) (f : ℝ → Vec 2 → ℂ)
    (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hfm : Measurable (Function.uncurry f)) (hFm : Measurable (Function.uncurry F))
    (hf : cellUlNorm I f < ⊤) (hF : cellUlNorm I F < ⊤)
    {s t : ℝ} (hst : s ≤ t) (hl : t - s ≤ 1) (hI : Icc s t ⊆ I) :
    (∫ r in s..t, cellMeanFreeForcingBudget f F r) ≤
      4 * (cellUlNorm I f).toReal ^ 2 + 8 * (cellUlNorm I F).toReal ^ 2 := by
  let J := Icc s (s + 1) ∩ I
  have hi := cellMeanFreeForcingBudget_integrable J f F hfm
    (cellSource_memLp_product J f hfm (cellUl_window_integral_lt_top I f hf s))
    (cellSource_memLp_product J F hFm (cellUl_window_integral_lt_top I F hF s))
  exact (scalar_short_interval_le_window I _ hst hl hI hi
    (Filter.Eventually.of_forall (cellMeanFreeForcingBudget_nonneg f F))).trans
      (cellUl_meanFree_forcing_window I f F hfm hFm hf hF s)

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The actual homogeneous Riesz derivative has nonpositive real energy for real frequencies. -/

theorem cellDualDerivative_real_nonpos
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (θ : Fin 2 → ℂ) (hθ : ∀ j, star (θ j) = θ j) (t : ℝ) (u : TorusHk 1 ℂ) :
    inner ℝ (cellDualDerivative ⟨G, v, θ, 0⟩ hG V hv.1 hb t u 0 0) u ≤ 0 := by
  have he := cellDualComplexPair_derivative ⟨G, v, θ, 0⟩ hG V hv.1 hb t u u 0 (fun _ => 0)
  rw [cellComplexSource_zero, add_zero] at he
  have hr := congrArg Complex.re he
  rw [cellDualComplexPair_re] at hr
  simpa only [show (fun _ : Fin 2 => (0 : ComplexCellL2)) = 0 from rfl] using
    hr.le.trans (cellComplexGenerator_real_nonpos hG hv V hb θ hθ t u)

/-! A common genuine backward adjoint mode preserves normalized ratios of forward solution pairings. -/

theorem cellWeakAdjointPairing_ratio {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ) (hv : IsCellDrift C.v)
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    {u R q : ℝ → ComplexCellL2} {slice graph other : ℝ → TorusHk 1 ℂ}
    (hu : CellWeakHilbertCurve a b u slice (fun t =>
      cellDualDerivative C hG V hv.1 hb t (slice t) 0 (fun _ => 0)))
    (hR : CellWeakHilbertCurve a b R graph (fun t =>
      cellDualDerivative C hG V hv.1 hb t (graph t) 0 (fun _ => 0)))
    (hq : CellWeakHilbertCurve a b q other (fun t =>
      -cellDualDerivative (cellAdjointCoefficients C) hG V (cellDrift_neg hv).1
        (cellDrift_neg_bound hb) t (other t) 0 (fun _ => 0))) :
    cellComplexPair (u b) (q b) / cellComplexPair (R b) (q b) =
      cellComplexPair (u a) (q a) / cellComplexPair (R a) (q a) := by
  rw [cellWeakAdjointPairing hab C hG V hv hb hu hq,
    cellWeakAdjointPairing hab C hG V hv hb hR hq]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Integral-phase multiplication removes the actual bounded scalar potential. -/

theorem CellWeakHilbertCurve.remove_potential {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric G)
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Fin 2 → ℂ)
    (lam : ℝ → ℂ) (hlam : MemLp lam ⊤ (volume.restrict (Icc a b)))
    {u : ℝ → ComplexCellL2} {slice : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice (fun t =>
      cellDualDerivative ⟨G, v, θ, fun s => -lam s⟩ hG V hv hb t (slice t) 0 0)) :
    CellWeakHilbertCurve a b
      (fun t => cellScalarCLM (Complex.exp (∫ r in a..t, lam r)) (u t))
      (fun t => cellH1Scalar (Complex.exp (∫ r in a..t, lam r)) (slice t))
      (fun t => cellDualDerivative ⟨G, v, θ, 0⟩ hG V hv hb t
        (cellH1Scalar (Complex.exp (∫ r in a..t, lam r)) (slice t)) 0 0) := by
  apply (h.multiply_integral_phase hab lam hlam).dual_congr
  filter_upwards [h.agrees] with t ht
  rw [ht]
  have he := cellDualDerivative_remove_potential ⟨G, v, θ, fun s => -lam s⟩
    hG V hv hb t (slice t) (Complex.exp (∫ r in a..t, lam r))
  simpa only [neg_mul_neg, show (fun _ : ℝ => (0 : ℂ)) = 0 from rfl] using he

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Bounds for a graph flux with an arbitrary entrywise metric size. -/

/-- The fibre graph vector source has size controlled independently of the contrast. -/
theorem fibreGraphFlux_norm_le_entry_size (η : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (B : ℝ) (hB : 0 ≤ B) (hG : ∀ t i j, |G t i j| ≤ B)
    (ξ : Fin 2 → ℂ) (r : ℝ → Vec 2 → ℂ) (t : ℝ) (x : Vec 2) :
    ‖fibreGraphFlux η G ξ r t x‖ ≤ 4 * B * fibreNorm ξ * ‖r t x‖ := by
  rw [fibreGraphFlux_eq_metricVector, norm_smul]
  have hroot : Real.sqrt η ≤ 1 := Real.sqrt_le_one.mpr hη
  have hscalar : ‖2 * Complex.I * (Real.sqrt η : ℂ) * r t x‖ ≤ 2 * ‖r t x‖ := by
    simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg η)]
    norm_num
    gcongr
    linarith
  have hvec : ‖cellMetricFluxVector (G t) (WithLp.toLp 2 ξ)‖ ≤ 2 * B * fibreNorm ξ := by
    rw [fibreNorm_eq_piLp_norm]
    exact cellMetricFluxVector_norm_le (G t) B hB (hG t) (WithLp.toLp 2 ξ)
  calc
    _ ≤ (2 * ‖r t x‖) * (2 * B * fibreNorm ξ) := by gcongr
    _ = _ := by ring


theorem fibreGraphFlux_ul_bound_entry_size (η : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hG : ∀ t i j, |G t i j| ≤ B) (ξ : Fin 2 → ℂ)
    {C : CellCoefficients} {src : ℝ → Vec 2 → ℂ}
    {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {D : ℝ → RawJet2 1 ℂ}
    (hD : IsCellSolution univ C src F D) :
    cellUlNorm univ (fibreGraphFlux η G ξ (cellValue D)) ≤
      ENNReal.ofReal (4 * B * fibreNorm ξ) * cellEnergyNorm univ D := by
  have hm (t : ℝ) : AEStronglyMeasurable (fibreGraphFlux η G ξ (cellValue D) t)
      (volume.restrict AVenhance.unitCube) := by
    apply cellFiniteArray_aestronglyMeasurable
    intro k
    exact aestronglyMeasurable_const.mul (hD.2.2.1 t (mem_univ t)).1.aestronglyMeasurable
  apply cellUlNorm_le_uniform_cellL2Norm _ _ (fun t => ?_)
  apply (eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hm t)
    (Filter.Eventually.of_forall (fun x =>
      fibreGraphFlux_norm_le_entry_size η hη G B hB hG ξ (cellValue D) t x)) 2).trans
  gcongr
  exact cellValue_cellL2Norm_le_energy D t

/-! Every genuine homogeneous weak Bloch curve contracts in L² at real frequencies. -/

theorem CellWeakHilbertCurve.real_shift_contraction {a b : ℝ} (hab : a ≤ b)
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (θ : Fin 2 → ℂ) (hθ : ∀ j, star (θ j) = θ j)
    {u : ℝ → ComplexCellL2} {slice : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice (fun t =>
      cellDualDerivative ⟨G, v, θ, 0⟩ hG V hv.1 hb t (slice t) 0 0)) :
    ‖u b‖ ≤ ‖u a‖ := by
  have he := h.energy_increment hab
  have hn : (∫ t in a..b, 2 * inner ℝ
      (cellDualDerivative ⟨G, v, θ, 0⟩ hG V hv.1 hb t (slice t) 0 0) (slice t)) ≤ 0 := by
    rw [intervalIntegral.integral_of_le hab]
    apply integral_nonpos_of_ae
    exact Filter.Eventually.of_forall (fun t => mul_nonpos_of_nonneg_of_nonpos
      (by norm_num : (0 : ℝ) ≤ 2) (cellDualDerivative_real_nonpos hG hv V hb θ hθ t (slice t)))
  have ha := norm_nonneg (u a)
  have hb' := norm_nonneg (u b)
  nlinarith

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The actual Bloch scalar source is controlled by the scaled drift bound uniformly in contrast. -/

theorem cellBlochLinearSourceClass_norm_le (η Cw : ℝ) (hη0 : 0 ≤ η)
    (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (t : ℝ) (u : TorusHk 1 ℂ) :
    ‖cellBlochLinearSourceClass G v V hv hb (fun j => (Real.sqrt η : ℂ) * ξ j) t u‖ ≤
      (Cw * fibreNorm ξ + 8 * fibreNorm ξ ^ 2) * ‖torusHkValueCLM u‖ := by
  have hfn := fibreNorm_nonneg ξ
  have hq : ‖(η : ℂ) * fibreQuad (G t) ξ‖ ≤ 8 * fibreNorm ξ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hη0]
    calc
      _ ≤ 1 * (8 * fibreNorm ξ ^ 2) := by
        gcongr
        exact fibreQuad_norm_le_eight (G t) (fun j k => cellMetric_entry_bound hG t 0 j k) ξ
      _ = _ := one_mul _
  apply cellL2Class_norm_le_of_ae_le_mul _ (by positivity)
  filter_upwards [cellBlochLinearSourceClass_ae G hv V hb
    (fun j => (Real.sqrt η : ℂ) * ξ j) t u] with x hx
  rw [fibreBloch_drift_coupling, fibreBloch_metric_quadratic η hη0] at hx
  rw [hx]
  calc
    _ ≤ ‖-Complex.I * fibreDriftCoupling η v ξ t x * torusHkValueCLM u x‖ +
        ‖((η : ℂ) * fibreQuad (G t) ξ) * torusHkValueCLM u x‖ := norm_sub_le _ _
    _ = (‖fibreDriftCoupling η v ξ t x‖ + ‖(η : ℂ) * fibreQuad (G t) ξ‖) *
        ‖torusHkValueCLM u x‖ := by
      simp only [norm_mul, norm_neg, Complex.norm_I, one_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (add_le_add (fibreDriftCoupling_norm_le η Cw v hw ξ t x) hq) (norm_nonneg _)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Construct public raw cell solutions from the actual weak Hilbert equation. -/

/-- A solution of the actual Hilbert cell equation produces the public raw energy solution. -/
theorem cellWeakHilbert_exists_raw_solution {a b : ℝ}
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice (fun r => cellDualDerivative C hG V hv hb r
      (slice r) (cellSourceSlice src r) (fun j => cellSourceSlice (fun t x => F t x j) r))) :
    ∃ D : ℝ → RawJet2 1 ℂ, IsCellSolution (Icc a b) C src F D ∧
      (∀ t, (u t : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] cellValue D t) := by
  obtain ⟨D, hweak, htrace, hjoint, hjet, hper⟩ :=
    cellWeak_exists_raw_realization (Icc a b) u slice h.state h.agrees
  refine ⟨D, ⟨ordConnected_Icc, hweak, ?_, ?_, ?_, ?_, ?_⟩, htrace⟩
  · intro t _
    exact ⟨(Lp.memLp (u t)).ae_eq (htrace t), hper t _⟩
  · intro j
    exact (hjoint j).aestronglyMeasurable
  · exact cellRaw_trace_continuous (Icc a b) u h.trace (cellValue D) (fun t _ => htrace t)
  · intro s hs t ht
    exact cellRawGradient_energy_finite D hjoint s hs t ht
  · intro s hs t ht hst ψ
    exact cellWeakHilbert_raw_identity C hG V hv hb src F hsrc hF u slice h D
      (fun t _ => htrace t) hjet s hs t ht hst ψ

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Actual absolute-energy solution series satisfy the summed cell weak equation. -/

/-- All series interchange premises in the actual zero-frequency cell equation follow from energy and forcing bounds. -/
theorem cellSolutionSeries_weak_identity {J : Type*} [Countable J]
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
    (hFs : (∑' j, cellUlNorm Set.univ (F j)) < ⊤)
    (s t : ℝ) (hst : s ≤ t) (ψ : TorusHkFunction 1 ℂ) :
    CellWeakIdentity ⟨G, v, 0, 0⟩ s t
      (cellValue (fun r a x => ∑' j, D j r a x) s)
      (cellValue (fun r a x => ∑' j, D j r a x) t) (ψ.jet (valueIndex2 1))
      (fun k => ψ.jet ⟨⟨1, by decide⟩, fun _ => k⟩)
      (cellValue (fun r a x => ∑' j, D j r a x))
      (fun r k => cellGradComp (fun a x => ∑' j, D j r a x) k)
      (fun r x => ∑' j, src j r x) (fun r x => ∑' j, F j r x) := by
  have hm : (volume.restrict (Set.Ioc s t)).prod (volume.restrict AVenhance.unitCube) ≤
      (volume.restrict (Set.Icc s t)).prod (volume.restrict AVenhance.unitCube) :=
    Measure.prod_mono (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl) le_rfl
  have hr := cellSolutionSeries_rhs_L1 G hG v hvm V hvb src F D hD hsD hsm hFm hss hFs s t ψ
  have hr' := (ENNReal.tsum_le_tsum (fun j => eLpNorm_mono_measure
    (fun p : ℝ × Vec 2 => cellLiteralRHS ⟨G, v, 0, 0⟩ p.1
      (cellValue (D j) p.1) (cellGradComp (D j p.1)) (ψ.jet (valueIndex2 1))
      (fun k => ψ.jet ⟨⟨1, by decide⟩, fun _ => k⟩) (src j p.1) (F j p.1) p.2) hm)).trans_lt hr
  have he := ae_mono hm (cellSolutionSeries_rhs_ae ⟨G, v, 0, 0⟩ src F D hD hsD
    hsm hFm hss hFs s t (ψ.jet (valueIndex2 1)) (fun k => ψ.jet ⟨⟨1, by decide⟩, fun _ => k⟩))
  exact cellWeakIdentity_series_of_absolute_rhs ⟨G, v, 0, 0⟩ s t
    (ψ.jet (valueIndex2 1)) (fun k => ψ.jet ⟨⟨1, by decide⟩, fun _ => k⟩)
    (fun j => cellValue (D j) s) (fun j => cellValue (D j) t) (fun j => cellValue (D j)) src
    (fun j r => cellGradComp (D j r)) F
    (cellValue (fun r a x => ∑' j, D j r a x)) (fun r x => ∑' j, src j r x)
    (fun r k => cellGradComp (fun a x => ∑' j, D j r a x) k) (fun r x => ∑' j, F j r x)
    (ψ.hasPeriodicWeakJet.2.1 (valueIndex2 1))
    ((ENNReal.tsum_le_tsum (fun j => cellValue_cellL2Norm_le_energy (D j) s)).trans_lt hsD)
    ((ENNReal.tsum_le_tsum (fun j => cellValue_cellL2Norm_le_energy (D j) t)).trans_lt hsD)
    (fun j => (hD j).2.2.2.2.2.2 s (Set.mem_univ s) t (Set.mem_univ t) hst ψ) hr' he

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Subtracting a scalar multiple of a homogeneous graph leaves the actual forced generator of the difference. -/

theorem cellDualDerivative_sub_homogeneous_scalar (C : CellCoefficients)
    (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (t : ℝ)
    (u R : TorusHk 1 ℂ) (c : ℂ) (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    cellDualDerivative C hG V hv hb t u S F -
      cellH1Scalar c (cellDualDerivative C hG V hv hb t R 0 0) =
      cellDualDerivative C hG V hv hb t (u - cellH1Scalar c R) S F := by
  rw [cellDualDerivative_homogeneous_complex_scalar]
  apply ext_inner_right ℝ
  intro z
  have hz : cellSourceFunctional C.θ 0 0 z = 0 := by
    simp [cellSourceFunctional]
  rw [inner_sub_left, cellDualDerivative_pairing, cellDualDerivative_pairing,
    cellDualDerivative_pairing, hz, add_zero]
  simp only [map_sub, sub_apply]
  ring

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The bounded Bloch flux readout represents the literal weak PDE perturbation. -/

theorem cellBlochPerturbationFluxCLM_ae {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (δ : Fin 2 → ℂ) (k : Fin 2)
    (u : ℝ → ComplexCellL2) (slice g : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice g) (z : CellFiniteEnergyCarrier a b)
    (hz : ∀ t : CellCompactTime a b, z.val.1 t = u t.val) :
    cellBlochPerturbationFluxCLM hab C hG δ k z =ᵐ[volume.restrict (Icc a b)]
      fun t => cellBlochPerturbationFlux C hG δ t (slice t) k := by
  have hv := cellFiniteEnergyTimeValueCLM_ae hab u slice g h z hz
  have hm : ∀ j : Fin 2,
      cellTimeMetricEntryCLM (Icc a b) hG j k (cellFiniteEnergyTimeValueCLM hab z)
        =ᵐ[volume.restrict (Icc a b)]
        fun t => cellMetricEntryCLM hG t j k
          (AVRegularity.CoupledEnergy.Galerkin.torusHkValueCLM (slice t)) := by
    intro j
    filter_upwards [cellTimeMetricEntryCLM_ae (Icc a b) hG j k
      (cellFiniteEnergyTimeValueCLM hab z), hv, h.agrees] with t ht hv' ha
    rw [ht, hv', ha]
  have he := lpFiniteLinearCombination_ae (fun j => Complex.I * δ j)
    (fun j => cellTimeMetricEntryCLM (Icc a b) hG j k (cellFiniteEnergyTimeValueCLM hab z))
    (fun j t => cellMetricEntryCLM hG t j k
      (AVRegularity.CoupledEnergy.Galerkin.torusHkValueCLM (slice t))) hm
  simp only [cellBlochPerturbationFluxCLM, sum_apply, smul_apply,
    ContinuousLinearMap.comp_apply] 
  refine he.trans ?_
  filter_upwards [] with t
  unfold cellBlochPerturbationFlux
  apply Finset.sum_congr rfl
  intro j _
  simpa only [cellScalarCLM_smul] using
    (cellMetricEntryCLM_scalar hG t j k (Complex.I * δ j)
      (AVRegularity.CoupledEnergy.Galerkin.torusHkValueCLM (slice t))).symm

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The literal homogeneous Bloch generator is the unshifted generator with its actual linear source and divergence flux. -/

theorem cellBlochLinear_generator (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v) (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (θ : Fin 2 → ℂ) (t : ℝ) (u z : TorusHk 1 ℂ) :
    cellComplexGenerator ⟨fun t _ => G t, v, θ, 0⟩ hG V hv.1 hb t u z =
      cellComplexGenerator ⟨fun t _ => G t, v, 0, 0⟩ hG V hv.1 hb t u z +
        cellComplexSource 0 (cellBlochLinearSourceClass G v V hv hb θ t u)
          (cellNormalizedGraphFluxClass G θ t u) z := by
  rw [cellComplexGenerator_decomposition ⟨fun t _ => G t, v, θ, 0⟩ hG V hv hb,
    cellConstantMetric_bloch_expansion, cellComplexGenerator_plain hG hv V hb]
  simp only [show (0 : Fin 2 → ℂ) = (fun _ => 0) from rfl,
    cellComplexDiffusionForm_zero_shift, cellConstantMetricEntryCLM,
    cellComplexShiftedDriftForm, cellBlochLinearSourceClass, cellNormalizedGraphFluxClass,
    cellComplexSource, Pi.zero_apply, star_zero, cellShiftedDerivative_zero_apply,
    Fin.sum_univ_two, cellComplexPair_add_left, cellComplexPair_scalar_left]
  ring

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Public raw cell solutions on a time domain from compatible local weak Hilbert curves. -/

/-- Locally L² weak Hilbert solutions have one public raw energy solution on their interval domain. -/
theorem cellDomainLocalHilbert_exists_raw_solution (I : Set ℝ) (hI : I.OrdConnected)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrc : ∀ a ∈ I, ∀ b ∈ I, a ≤ b → MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : ∀ a ∈ I, ∀ b ∈ I, a ≤ b → MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ) (hu : ContinuousOn u I)
    (hs : ∀ n : ℕ, MemLp slice 2 (volume.restrict (Icc (-(n : ℝ)) n ∩ I)))
    (ha : ∀ n : ℕ, ∀ᵐ t ∂volume.restrict (Icc (-(n : ℝ)) n ∩ I),
      u t = AVRegularity.CoupledEnergy.Galerkin.torusHkValueCLM (slice t))
    (h : ∀ a ∈ I, ∀ b ∈ I, a ≤ b → CellWeakHilbertCurve a b u slice
      (fun t => cellDualDerivative C hG V hv hb t (slice t)
        (cellSourceSlice src t) (fun j => cellSourceSlice (fun r x => F r x j) t))) :
    ∃ D : ℝ → RawJet2 1 ℂ, IsCellSolution I C src F D ∧
      (∀ t, (u t : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] cellValue D t) ∧
      (∀ᵐ t ∂volume.restrict I, ∀ j, ((slice t).val j : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] D t j) := by
  obtain ⟨D, hweak, htrace, hjoint, hjet, hper⟩ :=
    cellDomainLocalWeak_exists_raw_realization I u slice hs ha
  have hjlocal (a b : ℝ) (hai : a ∈ I) (hbi : b ∈ I) (hab' : a ≤ b) :
      ∀ j, MemLp (fun p : ℝ × Vec 2 => D p.1 j p.2) 2
        ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)) := by
    intro j
    have hm : volume.restrict (Icc a b) ≤ volume.restrict I :=
      Measure.restrict_mono (hI.out hai hbi) le_rfl
    apply cellJoint_memLp_of_slices (Icc a b) (fun t x => D t j x)
      ((hjoint j).mono_measure (Measure.prod_mono hm le_rfl))
      (fun t => cellJetCoordinateCLM j (slice t))
      ((cellJetCoordinateCLM j).comp_memLp' (h a hai b hbi hab').state)
    have hr := hjet.filter_mono (ae_mono hm)
    filter_upwards [hr] with t ht
    exact ht j
  refine ⟨D, ⟨hI, ?_, ?_, ?_, ?_, ?_, ?_⟩, htrace, hjet⟩
  · exact hweak
  · intro t _
    exact ⟨(Lp.memLp (u t)).ae_eq (htrace t), hper t _⟩
  · exact hjoint
  · exact cellRaw_trace_continuous I u hu (cellValue D) (fun t _ => htrace t)
  · intro a hai b hbi
    rcases le_or_gt a b with hab' | hba
    · exact cellProduct_cellNormSq_finite (Icc a b) (fun r => cellGradient (D r))
        (cellRawGradient_memLp (Icc a b) D (hjlocal a b hai hbi hab'))
    · simp only [Icc_eq_empty_of_lt hba, Measure.restrict_empty, lintegral_zero_measure]
      exact ENNReal.zero_lt_top
  · intro s hsi t hti hst ψ
    exact cellWeakHilbert_raw_identity C hG V hv hb src F (hsrc s hsi t hti hst) (hF s hsi t hti hst)
      u slice (h s hsi t hti hst) D (fun r _ => htrace r)
      (hjet.filter_mono (ae_mono (Measure.restrict_mono (hI.out hsi hti) (le_rfl : volume ≤ volume))))
      s ⟨le_rfl, hst⟩ t ⟨hst, le_rfl⟩ hst ψ

/-! Public all-time raw cell solutions from actual weak Hilbert curves on every finite interval. -/

/-- Locally L² weak Hilbert solutions have one public raw energy solution on the whole time line. -/
theorem cellLocalHilbert_exists_raw_solution
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrc : ∀ a b : ℝ, a ≤ b → MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : ∀ a b : ℝ, a ≤ b → MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ) (hu : Continuous u)
    (h : ∀ a b : ℝ, a ≤ b → CellWeakHilbertCurve a b u slice
      (fun t => cellDualDerivative C hG V hv hb t (slice t)
        (cellSourceSlice src t) (fun j => cellSourceSlice (fun r x => F r x j) t))) :
    ∃ D : ℝ → RawJet2 1 ℂ, IsCellSolution univ C src F D ∧
      (∀ t, (u t : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] cellValue D t) ∧
      (∀ᵐ t ∂volume, ∀ j, ((slice t).val j : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] D t j) := by
  have hab (n : ℕ) : -(n : ℝ) ≤ n := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  obtain ⟨D, hweak, htrace, hjoint, hjet, hper⟩ := cellLocalWeak_exists_raw_realization u slice
    (fun n => (h _ _ (hab n)).state) (fun n => (h _ _ (hab n)).agrees)
  have hjlocal (a b : ℝ) (hab' : a ≤ b) :
      ∀ j, MemLp (fun p : ℝ × Vec 2 => D p.1 j p.2) 2
        ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)) := by
    intro j
    apply cellJoint_memLp_of_slices (Icc a b) (fun t x => D t j x)
      ((hjoint j).mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl))
      (fun t => cellJetCoordinateCLM j (slice t))
      ((cellJetCoordinateCLM j).comp_memLp' (h a b hab').state)
    have hr := hjet.filter_mono (ae_mono (Measure.restrict_le_self (μ := volume) (s := Icc a b)))
    filter_upwards [hr] with t ht
    exact ht j
  refine ⟨D, ⟨ordConnected_univ, ?_, ?_, ?_, ?_, ?_, ?_⟩, htrace, hjet⟩
  · simpa only [Measure.restrict_univ] using hweak
  · intro t _
    exact ⟨(Lp.memLp (u t)).ae_eq (htrace t), hper t _⟩
  · intro j
    simpa only [Measure.restrict_univ] using hjoint j
  · exact cellRaw_trace_continuous univ u hu.continuousOn (cellValue D) (fun t _ => htrace t)
  · intro a _ b _
    rcases le_or_gt a b with hab' | hba
    · exact cellProduct_cellNormSq_finite (Icc a b) (fun r => cellGradient (D r))
        (cellRawGradient_memLp (Icc a b) D (hjlocal a b hab'))
    · simp only [Icc_eq_empty_of_lt hba, Measure.restrict_empty, lintegral_zero_measure]
      exact ENNReal.zero_lt_top
  · intro s _ t _ hst ψ
    exact cellWeakHilbert_raw_identity C hG V hv hb src F (hsrc s t hst) (hF s t hst)
      u slice (h s t hst) D (fun r _ => htrace r)
      (hjet.filter_mono (ae_mono (Measure.restrict_le_self (μ := volume) (s := Icc s t))))
      s ⟨le_rfl, hst⟩ t ⟨hst, le_rfl⟩ hst ψ

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Filter Homogenization AVRegularity.Sobolev
open scoped Topology
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.CycleEvolution

/-! Pointwise limits of actual finite weak cell test moments. -/

variable {a b : ℝ} {hab : a ≤ b} {C : CellCoefficients} {hG : IsCellMetric C.G} {V : ℝ}
  {hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2)}
  {hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2}
  {src : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
  {initial : ComplexCellL2}

/-- Each full H¹ test moment of the finite traces converges pointwise to the PDE primitive. -/
theorem CellGalerkinLimitData.moment_primitive_tendsto
    (D : CellGalerkinLimitData a b hab C hG V hv hb src F initial)
    (k : ℝ) (hκ : Measurable C.κ) (hκb : ∀ r, ‖C.κ r‖ ≤ k)
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (z : TorusHk 1 ℂ) (t : ℝ) (ht : t ∈ Icc a b) :
    Tendsto (fun n => inner ℝ
      (cellGalerkinValue (D.subsequence n) (extendCurve hab (D.curve (D.subsequence n)) t))
      (torusHkValueCLM z)) atTop
      (𝓝 (inner ℝ initial (torusHkValueCLM z) + ∫ r in a..t,
        cellGeneratorForm C hG V hv hb r (D.limit r) z + cellRawSourceFunctional C.θ src F r z)) := by
  have hgen := D.generator_integral_tendsto k hκ hκb z t ht
  have hq := cellRawSource_integral_fourier_tendsto ⟨le_rfl, hab⟩ ht ht.1 C.θ src F hsrc hF
    D.subsequence D.monotone z
  have hinit : Tendsto (fun n => inner ℝ initial
      (torusHkValueCLM (galerkinProj (D.subsequence n) z))) atTop
      (𝓝 (inner ℝ initial (torusHkValueCLM z))) :=
    (tendsto_const_nhds (x := initial)).inner
      (((torusHkValueCLM (E := ℂ) (K := 1)).continuous.tendsto z).comp
        ((galerkinProj_tendsto z).comp D.monotone.tendsto_atTop))
  have hlim := hinit.add (hgen.add hq)
  have hgint := cellGenerator_pairing_intervalIntegrable ⟨le_rfl, hab⟩ ht ht.1 C hG V k hv hb
    hκ hκb z D.limit (Lp.memLp D.limit)
  have hqint := cellRawSourceFunctional_intervalIntegrable ⟨le_rfl, hab⟩ ht ht.1 C.θ src F hsrc hF z
  rw [← intervalIntegral.integral_add hgint hqint] at hlim
  apply hlim.congr'
  filter_upwards with n
  let N := D.subsequence n
  have he := cellGalerkin_full_test_primitive hab N (cellGeneratorB C hG V hv hb)
    (cellRawSourceFunctional C.θ src F) _ _ (D.variational N) initial (D.initial_value N) z t ht
  change inner ℝ (cellGalerkinValue N (extendCurve hab (D.curve N) t)) (torusHkValueCLM z) =
    inner ℝ initial (torusHkValueCLM (galerkinProj N z)) + ∫ r in a..t,
      cellGeneratorForm C hG V hv hb r (D.state N r) (galerkinProj N z) +
        cellRawSourceFunctional C.θ src F r (galerkinProj N z) at he
  rw [intervalIntegral.integral_add
    (cellGenerator_pairing_intervalIntegrable ⟨le_rfl, hab⟩ ht ht.1 C hG V k hv hb hκ hκb
      (galerkinProj N z) (D.state N) (D.stateLp N))
    (cellRawSourceFunctional_intervalIntegrable ⟨le_rfl, hab⟩ ht ht.1 C.θ src F hsrc hF
      (galerkinProj N z))] at he
  exact he.symm

end AVRegularity.CycleEvolution
end
