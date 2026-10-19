-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleEvolution.CellWeakForcedGapEnergy
public import AVRegularity.CycleEvolution.CellTimeMetricDriftCLM
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Local gradient energy bounds for actual mean-zero cell solutions. -/

/-- The mean-zero forced equation bounds its local gradient energy independently of the drift. -/
theorem cellWeakActual_local_energy {a b : ℝ} (hab : a ≤ b)
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (S : ℝ → ComplexCellL2) (F : ℝ → Fin 2 → ComplexCellL2)
    (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (hF : ∀ j, MemLp (fun t => F t j) 2 (volume.restrict (Icc a b)))
    (h : CellWeakHilbertCurve a b u slice
      (fun t => cellDualDerivative ⟨G, v, 0, 0⟩ hG V hv.1 hb t (slice t) (S t) (F t)))
    (hm : ∀ t ∈ Icc a b, cellMean (u t) = 0) :
    ‖u b‖ ^ 2 + (1 / 2) * (∫ t in a..b, ∑ j, ‖cellDerivativeCLM j (slice t)‖ ^ 2) ≤
      ‖u a‖ ^ 2 + ∫ t in a..b, ‖S t‖ ^ 2 + 8 * ∑ j, ‖F t j‖ ^ 2 := by
  have hsumF := (cellTime_normSq_intervalIntegrable hab (hF 0)).add
    (cellTime_normSq_intervalIntegrable hab (hF 1))
  have hf : IntervalIntegrable (fun t => ‖S t‖ ^ 2 + 8 * ∑ j, ‖F t j‖ ^ 2) volume a b := by
    simpa only [Fin.sum_univ_two, Pi.add_apply] using
      (cellTime_normSq_intervalIntegrable hab hS).add (hsumF.const_mul 8)
  have hd := (cellTime_gradientSq_intervalIntegrable hab slice h.state).const_mul (1 / 2)
  have he := (h.energy_strongTime hab).scalar_weighted_bound hab 0
    (fun t => ‖S t‖ ^ 2 + 8 * ∑ j, ‖F t j‖ ^ 2)
    (fun t => (1 / 2) * ∑ j, ‖cellDerivativeCLM j (slice t)‖ ^ 2) hf hd
  simp only [zero_mul, Real.exp_zero, one_mul, intervalIntegral.integral_const_mul] at he
  apply he
  filter_upwards [h.agrees, ae_restrict_mem measurableSet_Icc] with t ht hti
  have hmean := hm t hti
  rw [ht] at hmean
  rw [cellDualDerivative_pairing]
  have hbound := cellUnshifted_source_energy_bound hG hv V hb t (slice t) hmean (S t) (F t)
  have hgap : 0 ≤ Real.pi ^ 2 * ‖torusHkValueCLM (slice t)‖ ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  linarith

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Exact cancellation of the scalar potential in the genuine Riesz derivative. -/

theorem cellDualDerivative_remove_potential (C : CellCoefficients) (hG : IsCellMetric C.G)
    (V : ℝ) (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (t : ℝ) (u : TorusHk 1 ℂ) (c : ℂ) :
    cellH1Scalar c (cellDualDerivative C hG V hv hb t u 0 0) +
      cellPivotDualCLM (cellScalarCLM (-c * C.κ t) (torusHkValueCLM u)) =
        cellDualDerivative {C with κ := fun _ => 0} hG V hv hb t (cellH1Scalar c u) 0 0 := by
  apply ext_inner_right ℝ
  intro z
  have hz (θ : Fin 2 → ℂ) : cellComplexSource θ 0 0 z = 0 := by
    change cellComplexSource θ 0 (fun _ => 0) z = 0
    exact cellComplexSource_zero θ z
  have hp : cellDualComplexPair
      (cellH1Scalar c (cellDualDerivative C hG V hv hb t u 0 0) +
        cellPivotDualCLM (cellScalarCLM (-c * C.κ t) (torusHkValueCLM u))) z =
      cellDualComplexPair
        (cellDualDerivative {C with κ := fun _ => 0} hG V hv hb t (cellH1Scalar c u) 0 0) z := by
    rw [cellDualComplexPair_add_left, cellDualComplexPair_scalar_left,
      cellPivotDual_complex_pair, cellComplexPair_scalar_left,
      cellDualComplexPair_derivative C hG V hv hb t u z 0 0,
      cellDualComplexPair_derivative {C with κ := fun _ => 0} hG V hv hb t
        (cellH1Scalar c u) z 0 0,
      hz]
    simp only [add_zero]
    rw [
      cellComplexGenerator_scalar, cellComplexGenerator_potential C]
    ring
  simpa only [cellDualComplexPair_re] using congrArg Complex.re hp

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The full actual Riesz derivative, including arbitrary scalar and flux sources, is complex linear. -/

theorem cellDualDerivative_complex_scalar (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (t : ℝ) (u : TorusHk 1 ℂ) (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) (c : ℂ) :
    cellH1Scalar c (cellDualDerivative C hG V hv hb t u S F) =
      cellDualDerivative C hG V hv hb t (cellH1Scalar c u)
        (cellScalarCLM c S) (fun j => cellScalarCLM c (F j)) := by
  apply ext_inner_right ℝ
  intro z
  have he : cellDualComplexPair (cellH1Scalar c (cellDualDerivative C hG V hv hb t u S F)) z =
      cellDualComplexPair (cellDualDerivative C hG V hv hb t (cellH1Scalar c u)
        (cellScalarCLM c S) (fun j => cellScalarCLM c (F j))) z := by
    rw [cellDualComplexPair_scalar_left, cellDualComplexPair_actual,
      cellDualComplexPair_actual, cellComplexGenerator_scalar, cellComplexSource_scalar]
    exact mul_add _ _ _
  simpa only [cellDualComplexPair_re] using congrArg Complex.re he

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Bochner regularity follows from the public raw cell solution predicate. -/

/-- Public raw solutions have continuous Hilbert trace classes. -/
theorem IsCellSolution.trace_continuous {a b : ℝ} {C : CellCoefficients}
    {src : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    {D : ℝ → RawJet2 1 ℂ} (h : IsCellSolution (Icc a b) C src F D) :
    ContinuousOn (cellRawTrace D) (Icc a b) :=
  cellRawTrace_continuous _ D (fun t ht => (h.2.2.1 t ht).1) h.2.2.2.2.1

/-- The public raw gradient has product-space L² membership on the finite interval. -/
theorem IsCellSolution.gradient_memLp {a b : ℝ} (hab : a ≤ b) {C : CellCoefficients}
    {src : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    {D : ℝ → RawJet2 1 ℂ} (h : IsCellSolution (Icc a b) C src F D) :
    MemLp (fun p : ℝ × Vec 2 => cellGradient (D p.1) p.2) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)) := by
  have hm := cellFiniteArray_aestronglyMeasurable
    (fun (p : ℝ × Vec 2) (j : Fin 2) => cellGradComp (D p.1) j p.2)
    (fun j => h.2.2.2.1 ⟨⟨1, by decide⟩, fun _ => j⟩)
  exact cellJoint_memLp_of_cellNorm (Icc a b) (fun t => cellGradient (D t)) hm
    (h.2.2.2.2.2.1 a ⟨le_rfl, hab⟩ b ⟨hab, le_rfl⟩)

/-- Every raw jet coordinate of a public solution is product-space L². -/
theorem IsCellSolution.jet_memLp {a b : ℝ} (hab : a ≤ b) {C : CellCoefficients}
    {src : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    {D : ℝ → RawJet2 1 ℂ} (h : IsCellSolution (Icc a b) C src F D) :
    ∀ j, MemLp (fun p : ℝ × Vec 2 => D p.1 j p.2) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)) := by
  have hval := cellJoint_memLp_of_slices (Icc a b) (cellValue D)
    (h.2.2.2.1 (valueIndex2 1)) (cellRawTrace D)
    (cellContinuous_trace_memLp _ (IsCellSolution.trace_continuous h)) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact cellRawTrace_ae D t (h.2.2.1 t ht).1)
  have hgrad := IsCellSolution.gradient_memLp hab h
  rintro ⟨j, w⟩
  fin_cases j
  · have hw : w = Fin.elim0 := Subsingleton.elim _ _
    subst w
    exact hval
  · let k := w 0
    have hw : w = fun _ => k := by
      funext x
      have hx : x = 0 := Subsingleton.elim _ _
      rw [hx]
    rw [hw]
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) k).comp_memLp' hgrad

/-! Mean conservation for the actual unshifted weak Hilbert cell equation. -/

/-- Testing against the genuine constant H¹ test gives the scalar mean increment. -/
theorem cellWeakActual_mean_increment {a b : ℝ}
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (S : ℝ → ComplexCellL2) (F : ℝ → Fin 2 → ComplexCellL2)
    (h : CellWeakHilbertCurve a b u slice
      (fun t => cellDualDerivative ⟨G, v, 0, 0⟩ hG V hv.1 hb t (slice t) (S t) (F t)))
    (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    cellMean (u t) - cellMean (u s) = ∫ r in s..t, cellMean (S r) := by
  have he := h.complex_increment s hs t ht hst cellH1One
  rw [cellH1One_value, cellComplexPair_one, cellComplexPair_one] at he
  simp_rw [cellDualComplexPair_one hG hv] at he
  exact he

/-- A mean-zero scalar source preserves the initial mean at every continuous trace time. -/
theorem cellWeakActual_mean_conserved {a b : ℝ} (hab : a ≤ b)
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (S : ℝ → ComplexCellL2) (F : ℝ → Fin 2 → ComplexCellL2)
    (h : CellWeakHilbertCurve a b u slice
      (fun t => cellDualDerivative ⟨G, v, 0, 0⟩ hG V hv.1 hb t (slice t) (S t) (F t)))
    (hS : ∀ᵐ t ∂volume.restrict (Icc a b), cellMean (S t) = 0) :
    ∀ t ∈ Icc a b, cellMean (u t) = cellMean (u a) := by
  intro t ht
  have he := cellWeakActual_mean_increment hG hv V hb u slice S F h a ⟨le_rfl, hab⟩ t ht ht.1
  have hz : (∫ r in a..t, cellMean (S r)) = 0 := by
    rw [intervalIntegral.integral_of_le ht.1]
    have hr := hS.filter_mono (ae_mono (Measure.restrict_mono
      (show Ioc a t ⊆ Icc a b from fun r hr => ⟨hr.1.le, hr.2.trans ht.2⟩) le_rfl))
    calc
      _ = ∫ _ in Ioc a t, (0 : ℂ) := integral_congr_ae hr
      _ = 0 := integral_zero ℝ ℂ
  rw [hz] at he
  exact sub_eq_zero.mp he

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The actual homogeneous Riesz dual derivative respects minus-conjugate Bloch symmetry. -/

theorem cellDualDerivative_conjugate (C : CellCoefficients) (hG : IsCellMetric C.G)
    (V : ℝ) (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (u : TorusHk 1 ℂ) :
    cellH1Conj (cellDualDerivative C hG V hv hb t u 0 0) =
      cellDualDerivative (cellConjugateCoefficients C) hG V hv hb t (cellH1Conj u) 0 0 := by
  have hz (θ : Fin 2 → ℂ) (w : TorusHk 1 ℂ) : cellComplexSource θ 0 0 w = 0 := by
    change cellComplexSource θ 0 (fun _ => 0) w = 0
    exact cellComplexSource_zero θ w
  have hp (w : TorusHk 1 ℂ) :
      cellDualComplexPair (cellH1Conj (cellDualDerivative C hG V hv hb t u 0 0)) (cellH1Conj w) =
      cellDualComplexPair (cellDualDerivative (cellConjugateCoefficients C) hG V hv hb t
        (cellH1Conj u) 0 0) (cellH1Conj w) := by
    rw [cellDualComplexPair_conjugate,
      cellDualComplexPair_derivative C hG V hv hb t u w 0 0,
      cellDualComplexPair_derivative (cellConjugateCoefficients C) hG V hv hb t
        (cellH1Conj u) (cellH1Conj w) 0 0,
      cellComplexGenerator_conjugate]
    simp only [hz, add_zero]
  apply ext_inner_right ℝ
  intro z
  have he := hp (cellH1Conj z)
  rw [cellH1Conj_involutive] at he
  simpa only [cellDualComplexPair_re] using congrArg Complex.re he

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Every complete energy carrier has raw periodic representatives preserving its trace at every time. -/

def cellEnergySpaceTrace {a b : ℝ} (hab : a ≤ b) (z : CellEnergySpace a b) (t : ℝ) : ComplexCellL2 :=
  (show CellFiniteEnergyCarrier a b from z).val.1 (projIcc a b hab t)

def cellEnergySpaceState {a b : ℝ} (hab : a ≤ b) (z : CellEnergySpace a b) (t : ℝ) : TorusHk 1 ℂ :=
  cellComplexH1RealEquiv (cellFiniteEnergyTimeStateCLM hab z t)

theorem cellEnergySpaceState_memLp {a b : ℝ} (hab : a ≤ b) (z : CellEnergySpace a b) :
    MemLp (cellEnergySpaceState hab z) 2 (volume.restrict (Icc a b)) :=
  cellComplexH1RealEquiv.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp' (Lp.memLp (cellFiniteEnergyTimeStateCLM hab z))

theorem cellEnergySpaceTrace_agrees {a b : ℝ} (hab : a ≤ b) (z : CellEnergySpace a b) :
    cellEnergySpaceTrace hab z =ᵐ[volume.restrict (Icc a b)]
      fun t => torusHkValueCLM (cellEnergySpaceState hab z t) := by
  have hp := cellCompactTimeProjection_measurePreserving hab
  have hr := Lp.coeFn_compMeasurePreserving (show CellFiniteEnergyCarrier a b from z).val.2 hp
  have ha := hp.quasiMeasurePreserving.ae (cellFiniteEnergyCarrier_agrees a b z)
  filter_upwards [hr, ha] with t hr' ha'
  change (show CellFiniteEnergyCarrier a b from z).val.1 (projIcc a b hab t) =
    cellComplexH1ValueCLM (Lp.compMeasurePreserving (projIcc a b hab) hp
      (show CellFiniteEnergyCarrier a b from z).val.2 t)
  rw [hr']
  exact ha'

theorem cellEnergySpace_exists_raw_realization {a b : ℝ} (hab : a ≤ b) (z : CellEnergySpace a b) :
    ∃ D : ℝ → RawJet2 1 ℂ,
      (∀ᵐ t ∂volume.restrict (Icc a b), HasPeriodicOrderedWeakJet (D t)) ∧
      (∀ t, (cellEnergySpaceTrace hab z t : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] cellValue D t) ∧
      (∀ j, MemLp (fun p : ℝ × Vec 2 => D p.1 j p.2) 2
        ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube))) ∧
      (∀ᵐ t ∂volume.restrict (Icc a b), ∀ j,
        ((cellEnergySpaceState hab z t).val j : Vec 2 → ℂ)
          =ᵐ[volume.restrict AVenhance.unitCube] D t j) ∧
      (∀ t j, AVenhance.IsZ2Periodic (D t j)) :=
  cellWeak_exists_raw_realization (Icc a b) (cellEnergySpaceTrace hab z)
    (cellEnergySpaceState hab z) (cellEnergySpaceState_memLp hab z) (cellEnergySpaceTrace_agrees hab z)

/-! The Sobolev slices and their agreement with raw public cell solutions. -/

section
variable {a b : ℝ} {C : CellCoefficients} {src : ℝ → Vec 2 → ℂ}
  {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {D : ℝ → RawJet2 1 ℂ}

/-- The public solution predicate implies Bochner L² membership of its Sobolev slices. -/
theorem cellSolution_slice_memLp (hab : a ≤ b) (h : IsCellSolution (Icc a b) C src F D) :
    MemLp (cellH1Slice D) 2 (volume.restrict (Icc a b)) :=
  cellH1Slice_memLp _ D (IsCellSolution.jet_memLp hab h)

/-- At almost every time all Sobolev slice coordinates represent the raw jet coordinates. -/
theorem cellSolution_slice_ae (h : IsCellSolution (Icc a b) C src F D) :
    ∀ᵐ t ∂volume.restrict (Icc a b), ∀ j,
      ((cellH1Slice D t).val j : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] D t j := by
  filter_upwards [h.2.1] with t ht
  rw [cellH1Slice_eq_toHk D t ht]
  intro j
  exact torusJetToL2_ae (D t) ht.2.1 j

/-- The total raw value trace and the Bochner H¹ slice agree at almost every time. -/
theorem cellSolution_trace_agrees (h : IsCellSolution (Icc a b) C src F D) :
    ∀ᵐ t ∂volume.restrict (Icc a b), cellRawTrace D t = torusHkValueCLM (cellH1Slice D t) := by
  filter_upwards [h.2.1] with t ht
  rw [cellH1Slice_eq_toHk D t ht]
  apply Lp.ext
  exact (cellRawTrace_ae D t (ht.2.1 (valueIndex2 1))).trans
    (torusJetToL2_ae (D t) ht.2.1 (valueIndex2 1)).symm
end

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The actual normalized raw graph trace represents the literal constant-one graph mode. -/

theorem cellRawTrace_add_one_ae (D : ℝ → RawJet2 1 ℂ) (t : ℝ)
    (hD : MemLp (cellValue D t) 2 (volume.restrict AVenhance.unitCube)) :
    cellRawTrace D t + cellConstantCLM 1 =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => 1 + cellValue D t x := by
  filter_upwards [Lp.coeFn_add (cellRawTrace D t) (cellConstantCLM 1),
    cellRawTrace_ae D t hD, cellConstantCLM_ae 1] with x ha hr hc
  rw [ha]
  change cellRawTrace D t x + cellConstantCLM 1 x = _
  rw [hr, hc, add_comm]

theorem cellL2Norm_normalized_raw_trace (D : ℝ → RawJet2 1 ℂ) (t : ℝ)
    (hD : MemLp (cellValue D t) 2 (volume.restrict AVenhance.unitCube)) :
    cellL2Norm (fun x => 1 + cellValue D t x) =
      ENNReal.ofReal ‖cellRawTrace D t + cellConstantCLM 1‖ :=
  cellL2Norm_eq_of_class _ _ (cellRawTrace_add_one_ae D t hD)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Past-forcing convolution bound for actual mean-zero cell solutions. -/

/-- The actual mean-zero forced equation has a drift-independent convolution estimate. -/
theorem cellWeakActual_forced_decay {a b : ℝ} (hab : a ≤ b)
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (S : ℝ → ComplexCellL2) (F : ℝ → Fin 2 → ComplexCellL2)
    (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (hF : ∀ j, MemLp (fun t => F t j) 2 (volume.restrict (Icc a b)))
    (h : CellWeakHilbertCurve a b u slice
      (fun t => cellDualDerivative ⟨G, v, 0, 0⟩ hG V hv.1 hb t (slice t) (S t) (F t)))
    (hm : ∀ t ∈ Icc a b, cellMean (u t) = 0) :
    ‖u b‖ ^ 2 ≤ Real.exp (-(Real.pi ^ 2) * (b - a)) * ‖u a‖ ^ 2 +
      ∫ t in a..b, Real.exp (-(Real.pi ^ 2) * (b - t)) *
        (‖S t‖ ^ 2 + 8 * ∑ j, ‖F t j‖ ^ 2) := by
  have hsumF := (cellTime_normSq_intervalIntegrable hab (hF 0)).add
    (cellTime_normSq_intervalIntegrable hab (hF 1))
  have hf : IntervalIntegrable (fun t => ‖S t‖ ^ 2 + 8 * ∑ j, ‖F t j‖ ^ 2) volume a b := by
    simpa only [Fin.sum_univ_two, Pi.add_apply] using
      (cellTime_normSq_intervalIntegrable hab hS).add (hsumF.const_mul 8)
  apply (h.energy_strongTime hab).scalar_forced_decay hab (Real.pi ^ 2) _ hf
  filter_upwards [h.agrees, ae_restrict_mem measurableSet_Icc] with t ht hti
  have hmean := hm t hti
  rw [ht] at hmean
  rw [cellDualDerivative_pairing, ht]
  have he := cellUnshifted_source_energy_bound hG hv V hb t (slice t) hmean (S t) (F t)
  have hn : 0 ≤ ∑ j : Fin 2, ‖cellDerivativeCLM j (slice t)‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  linarith

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Raw representatives of the actual complete energy carrier, without prescribing a PDE. -/

def IsCellEnergySpaceRawRepresentative {a b : ℝ} (hab : a ≤ b)
    (z : CellEnergySpace a b) (D : ℝ → RawJet2 1 ℂ) : Prop :=
  (∀ᵐ t ∂volume.restrict (Icc a b), HasPeriodicOrderedWeakJet (D t)) ∧
  (∀ t, (cellEnergySpaceTrace hab z t : Vec 2 → ℂ)
    =ᵐ[volume.restrict AVenhance.unitCube] cellValue D t) ∧
  (∀ j, MemLp (fun p : ℝ × Vec 2 => D p.1 j p.2) 2
    ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube))) ∧
  (∀ᵐ t ∂volume.restrict (Icc a b), ∀ j,
    ((cellEnergySpaceState hab z t).val j : Vec 2 → ℂ)
      =ᵐ[volume.restrict AVenhance.unitCube] D t j) ∧
  (∀ t j, AVenhance.IsZ2Periodic (D t j))

def cellEnergySpaceRawRepresentative {a b : ℝ} (hab : a ≤ b) (z : CellEnergySpace a b) :
    ℝ → RawJet2 1 ℂ :=
  Classical.choose (cellEnergySpace_exists_raw_realization hab z)

theorem cellEnergySpaceRawRepresentative_spec {a b : ℝ} (hab : a ≤ b) (z : CellEnergySpace a b) :
    IsCellEnergySpaceRawRepresentative hab z (cellEnergySpaceRawRepresentative hab z) :=
  Classical.choose_spec (cellEnergySpace_exists_raw_realization hab z)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set
namespace AVRegularity.CycleEvolution

/-! Trace and time-state readouts retain their actual carrier norm bounds. -/

theorem cellEnergySpaceTrace_norm_le {a b : ℝ} (hab : a ≤ b) (z : CellEnergySpace a b) (t : ℝ) :
    ‖cellEnergySpaceTrace hab z t‖ ≤ ‖z‖ := by
  have ht := (show CellFiniteEnergyCarrier a b from z).val.1.norm_coe_le_norm (projIcc a b hab t)
  exact ht.trans (norm_fst_le (show CellFiniteEnergyCarrier a b from z).val)

theorem cellEnergySpaceTimeState_norm_le {a b : ℝ} (hab : a ≤ b) (z : CellEnergySpace a b) :
    ‖cellFiniteEnergyTimeStateCLM hab z‖ ≤ ‖z‖ := by
  change ‖Lp.compMeasurePreserving (projIcc a b hab)
    (cellCompactTimeProjection_measurePreserving hab) (show CellFiniteEnergyCarrier a b from z).val.2‖ ≤ ‖z‖
  rw [Lp.norm_compMeasurePreserving]
  exact norm_snd_le (show CellFiniteEnergyCarrier a b from z).val

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Actual mean-zero inverse modes have normalized mass at least one, with an energy-controlled upper bound. -/

theorem cellInverse_normalized_mode_lower {C : CellCoefficients} {src : ℝ → Vec 2 → ℂ}
    {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {D : ℝ → RawJet2 1 ℂ}
    (hD : IsCellInverseValue C src F D) (t : ℝ) :
    1 ≤ ‖cellRawTrace D t + cellConstantCLM 1‖ := by
  have hm : cellMeanCLM (cellRawTrace D t) = 0 := by
    rw [cellMeanCLM_apply]
    exact (integral_congr_ae (cellRawTrace_ae D t (hD.1.2.2.1 t (mem_univ t)).1)).trans
      (hD.2.1 t)
  have hn := cellMeanCLM_norm_le (cellRawTrace D t + cellConstantCLM 1)
  simpa only [map_add, hm, cellMeanCLM_constant, zero_add, norm_one] using hn

theorem cellInverse_normalized_mode_upper {C : CellCoefficients} {src : ℝ → Vec 2 → ℂ}
    {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {D : ℝ → RawJet2 1 ℂ}
    (hD : IsCellInverseValue C src F D) (t : ℝ) :
    ‖cellRawTrace D t + cellConstantCLM 1‖ ≤ 1 + (cellEnergyNorm univ D).toReal := by
  calc
    _ ≤ ‖cellRawTrace D t‖ + ‖cellConstantCLM 1‖ := norm_add_le _ _
    _ ≤ (cellEnergyNorm univ D).toReal + 1 := by
      rw [cellConstantCLM_norm, norm_one]
      exact add_le_add (cellRawTrace_norm_le_energy D hD.1 hD.2.2 t) le_rfl
    _ = _ := add_comm _ _

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Projection of absolutely convergent literal cell series. -/

/-- Absolute L2 convergence and pointwise convergence justify projection term by term. -/
theorem cellQ0_tsum_of_cellL2Norm {J : Type*} [Countable J]
    (f : J → Vec 2 → ℂ) (hs : (∑' j, cellL2Norm (f j)) < ⊤)
    (x : Vec 2) (hx : Summable (fun j => f j x)) :
    cellQ0 (fun y => ∑' j, f j y) x = ∑' j, cellQ0 (f j) x := by
  have hm : (∑' j, ‖cellMean (f j)‖ₑ) < ⊤ :=
    (ENNReal.tsum_le_tsum (fun j => cellMean_enorm_le_cellL2Norm (f j)
      ((ENNReal.le_tsum j).trans_lt hs))).trans_lt hs
  have hms : Summable (fun j => cellMean (f j)) := Summable.of_enorm hm.ne
  simp only [cellQ0]
  rw [cellMean_tsum_of_cellL2Norm f hs]
  exact (hx.tsum_sub hms).symm

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! Actual pointwise cell jet series have H1 regularity at almost every time. -/

/-- Summable value and gradient L2 bounds close H1-in-time-ae raw cell jets under literal series. -/
theorem cellPeriodicTimeJet_tsum_of_slice_bounds {J : Type*} [Countable J]
    (D : J → ℝ → RawJet2 1 ℂ)
    (hD : ∀ j, ∀ᵐ t ∂volume, HasPeriodicOrderedWeakJet (D j t))
    (B : J → ℝ≥0∞) (hB : (∑' j, B j) < ⊤)
    (hv : ∀ j t, cellL2Norm (cellValue (D j) t) ≤ B j)
    (hg : ∀ᵐ t ∂volume, (∑' j, cellL2Norm (cellGradient (D j t))) < ⊤) :
    ∀ᵐ t ∂volume, HasPeriodicOrderedWeakJet (fun a x => ∑' j, D j t a x) := by
  have hall := ae_all_iff.mpr hD
  filter_upwards [hall, hg] with t ht hgt
  apply cellPeriodicWeakJet_tsum (fun j => D j t) ht
  have hc (j : J) (a : JetIndex2 1) : cellL2Norm (D j t a) ≤
      B j + cellL2Norm (cellGradient (D j t)) := by
    rcases cellOrderOneIndex_cases a with ha | ⟨k, ha⟩
    · rw [ha]
      exact (hv j t).trans (le_add_right le_rfl)
    · rw [ha]
      exact (cellGradComp_cellL2Norm_le (D j t) k ((ht j).2.1 _).aestronglyMeasurable).trans
        (le_add_left le_rfl)
  calc
    _ ≤ ∑' j, ∑ _a : JetIndex2 1, (B j + cellL2Norm (cellGradient (D j t))) :=
      ENNReal.tsum_le_tsum (fun j => Finset.sum_le_sum (fun a _ => hc j a))
    _ = (Fintype.card (JetIndex2 1) : ℝ≥0∞) *
        ((∑' j, B j) + ∑' j, cellL2Norm (cellGradient (D j t))) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        ENNReal.tsum_mul_left, ENNReal.tsum_add]
    _ < ⊤ := ENNReal.mul_lt_top (by simp) (ENNReal.add_lt_top.mpr ⟨hB, hgt⟩)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Raw source and gradient norm squares agree with their Bochner class budgets. -/

/-- Scalar source energy is exactly the extended norm square of its spatial class. -/
theorem cellSource_cellNormSq_ae (I : Set ℝ) (src : ℝ → Vec 2 → ℂ)
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    (fun r => cellL2Norm (src r) ^ 2) =ᵐ[volume.restrict I]
      fun r => ENNReal.ofReal (‖cellSourceSlice src r‖ ^ 2) := by
  filter_upwards [cellSource_memLp_slices I src hsrc] with r hr
  rw [cellL2Norm_eq_of_class _ _ (cellSourceSlice_ae src r hr),
    ← ENNReal.ofReal_pow (norm_nonneg _)]

/-- Flux source energy is exactly the sum of its coordinate spatial class norm squares. -/
theorem cellFlux_cellNormSq_ae (I : Set ℝ)
    (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    (fun r => cellL2Norm (F r) ^ 2) =ᵐ[volume.restrict I]
      fun r => ENNReal.ofReal (∑ j, ‖cellSourceSlice (fun t x => F t x j) r‖ ^ 2) := by
  have hc (j : Fin 2) := cellSource_memLp_slices I (fun r x => F r x j)
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).comp_memLp' hF)
  filter_upwards [cellSource_memLp_slices I F hF, ae_all_iff.mpr hc] with r hr hrc
  exact cellArray_cellNormSq (F r) hr _ (fun j => cellSourceSlice_ae (fun t x => F t x j) r (hrc j))

/-- A public raw solution's gradient energy is exactly its Sobolev derivative class budget. -/
theorem cellSolution_gradient_cellNormSq_ae {a b : ℝ} (hab : a ≤ b)
    {C : CellCoefficients} {src : ℝ → Vec 2 → ℂ}
    {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {D : ℝ → RawJet2 1 ℂ}
    (h : IsCellSolution (Icc a b) C src F D) :
    (fun r => cellL2Norm (cellGradient (D r)) ^ 2) =ᵐ[volume.restrict (Icc a b)]
      fun r => ENNReal.ofReal (∑ j, ‖cellDerivativeCLM j (cellH1Slice D r)‖ ^ 2) := by
  filter_upwards [cellSource_memLp_slices (Icc a b) (fun r => cellGradient (D r))
    (IsCellSolution.gradient_memLp hab h), cellSolution_slice_ae h] with r hr hj
  exact cellArray_cellNormSq _ hr (fun j => cellDerivativeCLM j (cellH1Slice D r))
    (fun j => hj ⟨⟨1, by decide⟩, fun _ => j⟩)

/-- A nonnegative integrable real budget reads its extended norm integral without a junk value. -/
theorem cellEnergy_lintegral_of_ae {μ : Measure ℝ} (f : ℝ → ENNReal) (g : ℝ → ℝ)
    (hi : Integrable g μ) (hn : ∀ᵐ r ∂μ, 0 ≤ g r)
    (he : f =ᵐ[μ] fun r => ENNReal.ofReal (g r)) :
    (∫⁻ r, f r ∂μ) = ENNReal.ofReal (∫ r, g r ∂μ) :=
  (lintegral_congr_ae he).trans (ofReal_integral_eq_lintegral_ofReal hi hn).symm

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Constant complex multiples satisfy the same actual homogeneous Bloch equation. -/

theorem cellDualDerivative_homogeneous_scalar
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric G)
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (θ : Fin 2 → ℂ) (t : ℝ) (u : TorusHk 1 ℂ) (c : ℂ) :
    cellH1Scalar c (cellDualDerivative ⟨G, v, θ, 0⟩ hG V hv hb t u 0 0) =
      cellDualDerivative ⟨G, v, θ, 0⟩ hG V hv hb t (cellH1Scalar c u) 0 0 := by
  have h := cellDualDerivative_remove_potential ⟨G, v, θ, 0⟩ hG V hv hb t u c
  have hz (z : ComplexCellL2) : cellScalarCLM 0 z = 0 := by
    change (0 : ℂ) • z = 0
    exact zero_smul ℂ z
  simpa only [Pi.zero_apply, mul_zero, hz, map_zero, add_zero,
    show (fun _ : ℝ => (0 : ℂ)) = 0 from rfl] using h

theorem CellWeakHilbertCurve.homogeneous_complex_scalar {a b : ℝ}
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric G)
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Fin 2 → ℂ)
    {u : ℝ → ComplexCellL2} {slice : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice
      (fun t => cellDualDerivative ⟨G, v, θ, 0⟩ hG V hv hb t (slice t) 0 0)) (c : ℂ) :
    CellWeakHilbertCurve a b (fun t => cellScalarCLM c (u t))
      (fun t => cellH1Scalar c (slice t))
      (fun t => cellDualDerivative ⟨G, v, θ, 0⟩ hG V hv hb t (cellH1Scalar c (slice t)) 0 0) := by
  simpa only [cellDualDerivative_homogeneous_scalar] using h.complex_smul c

/-! Complex scalar multiplication of the full actual weak Hilbert equation. -/

theorem cellActualWeak_complex_smul {a b : ℝ}
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (S : ℝ → ComplexCellL2) (F : ℝ → Fin 2 → ComplexCellL2)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice
      (fun t => cellDualDerivative C hG V hv hb t (slice t) (S t) (F t))) (c : ℂ) :
    CellWeakHilbertCurve a b (fun t => c • u t) (fun t => cellH1Scalar c (slice t))
      (fun t => cellDualDerivative C hG V hv hb t (cellH1Scalar c (slice t))
        (c • S t) (fun j => c • F t j)) := by
  have hs := h.complex_smul c
  simp only [cellScalarCLM_smul] at hs
  apply hs.dual_congr
  exact Filter.Eventually.of_forall (fun t => by
    simpa only [cellScalarCLM_smul] using
      cellDualDerivative_complex_scalar C hG V hv hb t (slice t) (S t) (F t) c)

/-! The scalar coupling from the mean-zero Bloch component to its mean is uniformly bounded by the scaled drift. -/

theorem cellBlochDriftCoupling_aestronglyMeasurable (η : ℝ)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (ξ : Fin 2 → ℂ) (t : ℝ) :
    AEStronglyMeasurable (fibreDriftCoupling η v ξ t)
      (volume.restrict AVenhance.unitCube) := by
  exact ((fibreDriftCoupling_measurable η hv ξ).comp
    (measurable_const.prodMk measurable_id)).aestronglyMeasurable

def cellBlochDriftMeanCLM (η Cw : ℝ) (hCw : 0 ≤ Cw)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (t : ℝ) : ComplexCellL2 →L[ℝ] ℂ :=
  cellMeanCLM.comp (cellCoefficientCLM (fibreDriftCoupling η v ξ t)
    (cellBlochDriftCoupling_aestronglyMeasurable η hv ξ t)
    (Cw * fibreNorm ξ) (mul_nonneg hCw (fibreNorm_nonneg ξ))
    (fibreDriftCoupling_norm_le η Cw v hw ξ t))

theorem cellBlochDriftMeanCLM_apply (η Cw : ℝ) (hCw : 0 ≤ Cw)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (t : ℝ) (u : ComplexCellL2) :
    cellBlochDriftMeanCLM η Cw hCw hv hw ξ t u =
      cellMean (fun x => fibreDriftCoupling η v ξ t x * u x) := by
  rw [cellBlochDriftMeanCLM, ContinuousLinearMap.comp_apply, cellMeanCLM_apply]
  unfold cellMean
  exact integral_congr_ae (cellCoefficientCLM_ae _ _ _ _ _ u)

theorem cellBlochDriftMeanCLM_norm_le (η Cw : ℝ) (hCw : 0 ≤ Cw)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (t : ℝ) (u : ComplexCellL2) :
    ‖cellBlochDriftMeanCLM η Cw hCw hv hw ξ t u‖ ≤ Cw * fibreNorm ξ * ‖u‖ := by
  apply (cellMeanCLM_norm_le _).trans
  let M := cellCoefficientCLM (fibreDriftCoupling η v ξ t)
    (cellBlochDriftCoupling_aestronglyMeasurable η hv ξ t)
    (Cw * fibreNorm ξ) (mul_nonneg hCw (fibreNorm_nonneg ξ))
    (fibreDriftCoupling_norm_le η Cw v hw ξ t)
  change ‖M u‖ ≤ Cw * fibreNorm ξ * ‖u‖
  have he := cellCoefficient_pairing_abs_le (fibreDriftCoupling η v ξ t)
    (cellBlochDriftCoupling_aestronglyMeasurable η hv ξ t)
    (Cw * fibreNorm ξ) (mul_nonneg hCw (fibreNorm_nonneg ξ))
    (fibreDriftCoupling_norm_le η Cw v hw ξ t) u (M u)
  change |inner ℝ (M u) (M u)| ≤ Cw * fibreNorm ξ * ‖u‖ * ‖M u‖ at he
  rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)] at he
  by_cases hz : ‖M u‖ = 0
  · rw [hz]
    exact mul_nonneg (mul_nonneg hCw (fibreNorm_nonneg ξ)) (norm_nonneg u)
  · have hp : 0 < ‖M u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    exact le_of_mul_le_mul_right (by simpa only [pow_two] using he) hp

theorem cellBlochDriftMean_feedback_norm_le (η Cw : ℝ) (hCw : 0 ≤ Cw)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (t : ℝ) (u ρ : ComplexCellL2) (Cr : ℝ)
    (hρ : ‖ρ‖ ≤ Cr * fibreNorm ξ) :
    ‖cellScalarCLM (-Complex.I * cellBlochDriftMeanCLM η Cw hCw hv hw ξ t u) ρ‖ ≤
      Cr * Cw * fibreNorm ξ ^ 2 * ‖u‖ := by
  have hfn := fibreNorm_nonneg ξ
  rw [cellScalarCLM_norm]
  simp only [norm_mul, norm_neg, Complex.norm_I, one_mul]
  calc
    _ ≤ (Cw * fibreNorm ξ * ‖u‖) * (Cr * fibreNorm ξ) :=
      mul_le_mul (cellBlochDriftMeanCLM_norm_le η Cw hCw hv hw ξ t u) hρ
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set
namespace AVRegularity.CycleEvolution

/-! Full-time H1 and gradient budgets are bounded by the actual complete carrier norm. -/

theorem cellEnergySpaceState_normSqIntegral_le {a b : ℝ} (hab : a ≤ b) (z : CellEnergySpace a b) :
    (∫ t in Icc a b, ‖cellEnergySpaceState hab z t‖ ^ 2) ≤ ‖z‖ ^ 2 := by
  let : InnerProductSpace ℝ CellComplexH1 := InnerProductSpace.complexToReal
  change (∫ t in Icc a b, ‖cellComplexH1RealEquiv (cellFiniteEnergyTimeStateCLM hab z t)‖ ^ 2) ≤ ‖z‖ ^ 2
  simp_rw [LinearIsometryEquiv.norm_map]
  rw [← lpTwoHilbert_normSq_integral]
  exact (sq_le_sq₀ (norm_nonneg (cellFiniteEnergyTimeStateCLM hab z)) (norm_nonneg z)).2
    (cellEnergySpaceTimeState_norm_le hab z)

theorem cellEnergySpace_gradientSqIntegral_le {a b : ℝ} (hab : a ≤ b) (z : CellEnergySpace a b) :
    (∫ t in a..b, ∑ j, ‖cellDerivativeCLM j (cellEnergySpaceState hab z t)‖ ^ 2) ≤ ‖z‖ ^ 2 := by
  have hs := cellEnergySpaceState_memLp hab z
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp
    (cellTime_gradientSq_intervalIntegrable hab _ hs)
  have hn := hs.norm.integrable_sq
  have hp (t : ℝ) : (∑ j, ‖cellDerivativeCLM j (cellEnergySpaceState hab z t)‖ ^ 2) ≤
      ‖cellEnergySpaceState hab z t‖ ^ 2 := by
    rw [cellH1_norm_sq]
    exact le_add_of_nonneg_left (sq_nonneg _)
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  exact (integral_mono hi hn hp).trans (cellEnergySpaceState_normSqIntegral_le hab z)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Shifted derivative readouts represent every energy state, without a PDE premise. -/

theorem cellEnergySpaceTimeDerivative_ae {a b : ℝ} (hab : a ≤ b)
    (z : CellEnergySpace a b) (j : Fin 2) :
    cellFiniteEnergyTimeDerivativeCLM hab j z =ᵐ[volume.restrict (Icc a b)]
      fun t => cellDerivativeCLM j (cellEnergySpaceState hab z t) := by
  exact (cellComplexH1DerivativeCLM j).coeFn_compLpL (cellFiniteEnergyTimeStateCLM hab z)

theorem cellEnergySpaceTimeValue_ae {a b : ℝ} (hab : a ≤ b)
    (z : CellEnergySpace a b) :
    cellFiniteEnergyTimeValueCLM hab z =ᵐ[volume.restrict (Icc a b)]
      fun t => torusHkValueCLM (cellEnergySpaceState hab z t) := by
  exact cellComplexH1ValueCLM.coeFn_compLpL (cellFiniteEnergyTimeStateCLM hab z)

theorem cellEnergySpaceTimeShiftedDerivative_ae {a b : ℝ} (hab : a ≤ b)
    (z : CellEnergySpace a b) (θ : Fin 2 → ℂ) (j : Fin 2) :
    cellFiniteEnergyTimeShiftedDerivativeCLM hab θ j z =ᵐ[volume.restrict (Icc a b)]
      fun t => cellShiftedDerivativeCLM θ j (cellEnergySpaceState hab z t) := by
  have hd := cellEnergySpaceTimeDerivative_ae hab z j
  have hv := cellEnergySpaceTimeValue_ae hab z
  have ha := Lp.coeFn_add (cellFiniteEnergyTimeDerivativeCLM hab j z)
    ((Complex.I * θ j) • cellFiniteEnergyTimeValueCLM hab z)
  have hm := Lp.coeFn_smul (Complex.I * θ j) (cellFiniteEnergyTimeValueCLM hab z)
  filter_upwards [hd, hv, ha, hm] with t hd' hv' ha' hm'
  change (cellFiniteEnergyTimeDerivativeCLM hab j z +
    (Complex.I * θ j) • cellFiniteEnergyTimeValueCLM hab z) t = _
  rw [ha']
  simp only [Pi.add_apply]
  rw [hm', hd']
  simp only [Pi.smul_apply]
  rw [hv']
  rfl

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization
namespace AVRegularity.CycleEvolution

/-! The literal finite-time flux norm equals the actual coordinate Hilbert energy. -/

theorem cellFlux_finite_energy_half_norm {a b : ℝ} (hab : a ≤ b)
    (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube))) :
    (∫⁻ t in Icc a b, cellL2Norm (F t) ^ 2) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (Real.sqrt (∫ t in a..b,
        ∑ j, ‖cellSourceSlice (fun r x => F r x j) t‖ ^ 2)) := by
  have hj (j : Fin 2) := cellSourceSlice_memLp (Icc a b) (fun r x => F r x j)
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).comp_memLp' hF)
  have hi (j : Fin 2) := cellTime_normSq_intervalIntegrable hab (hj j)
  have hsum : IntervalIntegrable (fun t => ∑ j, ‖cellSourceSlice (fun r x => F r x j) t‖ ^ 2) volume a b := by
    simpa only [Fin.sum_univ_two, Pi.add_apply] using (hi 0).add (hi 1)
  have hint := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hsum
  have he := cellFlux_cellNormSq_ae (Icc a b) F hF
  rw [cellEnergy_lintegral_of_ae _ _ hint
    (Filter.Eventually.of_forall (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))) he,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  have hn : 0 ≤ ∫ t in a..b, ∑ j, ‖cellSourceSlice (fun r x => F r x j) t‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  rw [ENNReal.ofReal_rpow_of_nonneg (p := (1 / 2 : ℝ)) hn (by norm_num), ← Real.sqrt_eq_rpow]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Exact conversion of raw cell energy integrals to real Bochner energy integrals. -/

/-- A nonnegative real budget on a finite interval reads its extended subinterval integral. -/
theorem cellEnergy_lintegral_interval {a b s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (f : ℝ → ENNReal) (g : ℝ → ℝ) (hg : Integrable g (volume.restrict (Icc a b)))
    (hn : ∀ r, 0 ≤ g r) (he : f =ᵐ[volume.restrict (Icc a b)] fun r => ENNReal.ofReal (g r)) :
    (∫⁻ r in Icc s t, f r) = ENNReal.ofReal (∫ r in s..t, g r) := by
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
  have hgi := hg.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hei := he.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  have hi := cellEnergy_lintegral_of_ae f g hgi (Filter.Eventually.of_forall hn) hei
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hst] at hi
  exact hi

/-- Scalar source energy up to t equals the real integral of its Bochner class norm square. -/
theorem cellSource_energy_integral {a b s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) (src : ℝ → Vec 2 → ℂ)
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube))) :
    (∫⁻ r in Icc s t, cellL2Norm (src r) ^ 2) =
      ENNReal.ofReal (∫ r in s..t, ‖cellSourceSlice src r‖ ^ 2) :=
  cellEnergy_lintegral_interval hs ht hst _ _
    (cellSourceSlice_memLp (Icc a b) src hsrc).norm.integrable_sq
    (fun _ => sq_nonneg _) (cellSource_cellNormSq_ae (Icc a b) src hsrc)

/-- Flux energy up to t equals the sum of the coordinate class norm square integrals. -/
theorem cellFlux_energy_integral {a b s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube))) :
    (∫⁻ r in Icc s t, cellL2Norm (F r) ^ 2) =
      ENNReal.ofReal (∫ r in s..t, ∑ j, ‖cellSourceSlice (fun r x => F r x j) r‖ ^ 2) := by
  have hi (j : Fin 2) := (cellSourceSlice_memLp (Icc a b) (fun r x => F r x j)
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).comp_memLp' hF)).norm.integrable_sq
  apply cellEnergy_lintegral_interval hs ht hst _ _ _
    (fun r => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (cellFlux_cellNormSq_ae (Icc a b) F hF)
  apply integrable_finsetSum Finset.univ
  intro j _
  exact hi j

/-- Raw gradient energy up to t equals the Sobolev class gradient norm square integral. -/
theorem cellSolution_gradient_energy_integral {a b s t : ℝ} (hab : a ≤ b)
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    {C : CellCoefficients} {src : ℝ → Vec 2 → ℂ}
    {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {D : ℝ → RawJet2 1 ℂ}
    (hD : IsCellSolution (Icc a b) C src F D) :
    (∫⁻ r in Icc s t, cellL2Norm (cellGradient (D r)) ^ 2) =
      ENNReal.ofReal (∫ r in s..t, ∑ j, ‖cellDerivativeCLM j (cellH1Slice D r)‖ ^ 2) := by
  have hi (j : Fin 2) := ((cellDerivativeCLM j).comp_memLp'
    (cellSolution_slice_memLp hab hD)).norm.integrable_sq
  apply cellEnergy_lintegral_interval hs ht hst _ _ _
    (fun r => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (cellSolution_gradient_cellNormSq_ae hab hD)
  apply integrable_finsetSum Finset.univ
  intro j _
  exact hi j

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Raw gradient budgets agree with any actual H¹ representative of the same cell solution. -/

/-- The raw gradient norm integral reads the exact Hilbert gradient energy of its H¹ lift. -/
theorem cellSolution_gradient_lintegral_of_state {a b : ℝ} (hab : a ≤ b)
    {C : CellCoefficients} {src : ℝ → Vec 2 → ℂ}
    {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {D : ℝ → RawJet2 1 ℂ}
    (h : IsCellSolution (Icc a b) C src F D) (slice : ℝ → TorusHk 1 ℂ)
    (hs : MemLp slice 2 (volume.restrict (Icc a b)))
    (hj : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ j,
      ((slice t).val j : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] D t j) :
    (∫⁻ t in Icc a b, cellL2Norm (cellGradient (D t)) ^ 2) =
      ENNReal.ofReal (∫ t in a..b, ∑ j, ‖cellDerivativeCLM j (slice t)‖ ^ 2) := by
  have hp := cellSource_memLp_slices (Icc a b) (fun t => cellGradient (D t))
    (IsCellSolution.gradient_memLp hab h)
  have he : (fun t => cellL2Norm (cellGradient (D t)) ^ 2) =ᵐ[volume.restrict (Icc a b)]
      fun t => ENNReal.ofReal (∑ j, ‖cellDerivativeCLM j (slice t)‖ ^ 2) := by
    filter_upwards [hp, hj] with t ht hjt
    exact cellArray_cellNormSq (cellGradient (D t)) ht _
      (fun j => hjt ⟨⟨1, by decide⟩, fun _ => j⟩)
  have hi := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp
    (cellTime_gradientSq_intervalIntegrable hab slice hs)
  rw [cellEnergy_lintegral_of_ae _ _ hi
    (Filter.Eventually.of_forall (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))) he,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization
namespace AVRegularity.CycleEvolution

/-! Bounded complex-linear divergence forcing operators for literal Bloch perturbations. -/

def cellBlochPerturbationFluxCLM {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (δ : Fin 2 → ℂ) (k : Fin 2) :
    CellFiniteEnergyCarrier a b →L[ℂ] Lp ComplexCellL2 2 (volume.restrict (Icc a b)) :=
  ∑ j : Fin 2, (Complex.I * δ j) •
    ((cellTimeMetricEntryCLM (Icc a b) hG j k).comp (cellFiniteEnergyTimeValueCLM hab))

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Addition of raw representatives agrees with addition in the actual complete carrier. -/

theorem cellEnergySpaceRawRepresentative_add {a b : ℝ} (hab : a ≤ b)
    (z w : CellEnergySpace a b) (D E : ℝ → RawJet2 1 ℂ)
    (hD : IsCellEnergySpaceRawRepresentative hab z D)
    (hE : IsCellEnergySpaceRawRepresentative hab w E) :
    IsCellEnergySpaceRawRepresentative hab (z + w) (D + E) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hD.1, hE.1] with t hd he
    exact cellPeriodicWeakJet_add hd he
  · intro t
    change (cellEnergySpaceTrace hab z t + cellEnergySpaceTrace hab w t : ComplexCellL2)
      =ᵐ[volume.restrict AVenhance.unitCube] fun x => cellValue D t x + cellValue E t x
    filter_upwards [Lp.coeFn_add (cellEnergySpaceTrace hab z t) (cellEnergySpaceTrace hab w t),
      hD.2.1 t, hE.2.1 t] with x hx hd he
    simpa only [Pi.add_apply, hd, he] using hx
  · intro j
    change MemLp ((fun p : ℝ × Vec 2 => D p.1 j p.2) + (fun p : ℝ × Vec 2 => E p.1 j p.2)) 2 _
    exact (hD.2.2.1 j).add (hE.2.2.1 j)
  · have ha := Lp.coeFn_add (cellFiniteEnergyTimeStateCLM hab z) (cellFiniteEnergyTimeStateCLM hab w)
    filter_upwards [ha, hD.2.2.2.1, hE.2.2.2.1] with t ht hd he
    have hs : cellEnergySpaceState hab (z + w) t =
        cellEnergySpaceState hab z t + cellEnergySpaceState hab w t := by
      unfold cellEnergySpaceState
      change cellComplexH1RealEquiv (cellFiniteEnergyTimeStateCLM hab
        ((show CellFiniteEnergyCarrier a b from z) + (show CellFiniteEnergyCarrier a b from w)) t) = _
      rw [map_add, ht]
      simp only [Pi.add_apply, map_add]
    intro j
    rw [hs]
    change ((cellEnergySpaceState hab z t).val j + (cellEnergySpaceState hab w t).val j : ComplexCellL2)
      =ᵐ[volume.restrict AVenhance.unitCube] fun x => D t j x + E t j x
    filter_upwards [Lp.coeFn_add ((cellEnergySpaceState hab z t).val j)
      ((cellEnergySpaceState hab w t).val j), hd j, he j] with x hx hdx hex
    simpa only [Pi.add_apply, hdx, hex] using hx
  · intro t j n x
    change D t j (x + AVenhance.latticeShift n) + E t j (x + AVenhance.latticeShift n) = _
    rw [hD.2.2.2.2 t j n x, hE.2.2.2.2 t j n x]
    rfl

/-! Complex scaling of raw representatives agrees with scaling in the complete energy carrier. -/

theorem cellEnergySpaceRawRepresentative_smul {a b : ℝ} (hab : a ≤ b) (c : ℂ)
    (z : CellEnergySpace a b) (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellEnergySpaceRawRepresentative hab z D) :
    IsCellEnergySpaceRawRepresentative hab (c • z) (c • D) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hD.1] with t hd
    exact cellPeriodicWeakJet_complex_smul hd c
  · intro t
    change (c • cellEnergySpaceTrace hab z t : ComplexCellL2)
      =ᵐ[volume.restrict AVenhance.unitCube] fun x => c • cellValue D t x
    filter_upwards [Lp.coeFn_smul c (cellEnergySpaceTrace hab z t), hD.2.1 t] with x hx hd
    simpa only [Pi.smul_apply, hd] using hx
  · intro j
    change MemLp (c • (fun p : ℝ × Vec 2 => D p.1 j p.2)) 2 _
    exact (hD.2.2.1 j).const_smul c
  · have ha := Lp.coeFn_smul c (cellFiniteEnergyTimeStateCLM hab z)
    filter_upwards [ha, hD.2.2.2.1] with t ht hd
    intro j
    have hs : (cellEnergySpaceState hab (c • z) t).val j =
        c • (cellEnergySpaceState hab z t).val j := by
      unfold cellEnergySpaceState
      change (cellComplexH1RealEquiv (cellFiniteEnergyTimeStateCLM hab
        (c • (show CellFiniteEnergyCarrier a b from z)) t)).val j = _
      rw [map_smul, ht]
      rfl
    rw [hs]
    change (c • (cellEnergySpaceState hab z t).val j : ComplexCellL2)
      =ᵐ[volume.restrict AVenhance.unitCube] fun x => c • D t j x
    filter_upwards [Lp.coeFn_smul c ((cellEnergySpaceState hab z t).val j), hd j] with x hx hdx
    simpa only [Pi.smul_apply, hdx] using hx
  · intro t j n x
    change c • D t j (x + AVenhance.latticeShift n) = c • D t j x
    rw [hD.2.2.2.2 t j n x]

end AVRegularity.CycleEvolution
end
