-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleEvolution.CellInverseJetFactorialBound
public import AVRegularity.CycleEvolution.CellInverseJetEquationExistence
import AVRegularity.CycleEvolution.CellLimitMoments
public import AVRegularity.CycleEvolution.FibrePhaseDerivativeBounds

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Uniqueness of all-time inverse solutions in the literal raw energy seminorm. -/

/-- Bounded mean-zero inverse solutions with common forcing differ by zero in energy norm. -/
theorem cellInverse_unique_energy
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D E : ℝ → RawJet2 1 ℂ)
    (hD : IsCellInverseValue ⟨G, v, 0, 0⟩ src F D)
    (hE : IsCellInverseValue ⟨G, v, 0, 0⟩ src F E) :
    cellEnergyNorm univ (E - D) = 0 := by
  have hb := cellInverse_resolvent_bound hG hG hv src F D E hD hE
    (cellMetricSupNorm_sub_lt_top hG hG)
  rw [sub_self, cellMetricSupNorm_zero, mul_zero, zero_mul] at hb
  exact le_antisymm hb bot_le

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Actual quadratic coefficient forcing bounds for certified lower inverse states. -/

/-- Each quadratic Taylor source term is measurable and has the product of the actual lower energy bounds. -/
theorem fibreCoefficientQuadraticTerm_bound (η Cw : ℝ) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (j : Fin 2) {C : CellCoefficients} (A B : CellInverseDatum C) :
    cellUlNorm univ (fibreCoefficientQuadraticTerm η v A.raw B.raw j) ≤
      ENNReal.ofReal Cw * cellEnergyNorm univ B.raw * cellEnergyNorm univ A.raw ∧
    AEStronglyMeasurable (Function.uncurry (fibreCoefficientQuadraticTerm η v A.raw B.raw j))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) := by
  let b := fibreDriftCoupling η v (fibreCoordinateFrequency j)
  have hb := fibreDriftCoupling_measurable η hv (fibreCoordinateFrequency j)
  have hB (t : ℝ) (x : Vec 2) : ‖b t x‖ ≤ Cw := by
    simpa only [fibreCoordinateFrequency_norm, mul_one] using
      fibreDriftCoupling_norm_le η Cw v hw (fibreCoordinateFrequency j) t x
  have hq := cellMeanMultiplier_ul_bound b Cw hb hB B.isInverse A.isInverse
  let q : ℝ → Vec 2 → ℂ := fun t x => cellValue A.raw t x *
    cellMean (fun y => b t y * cellValue B.raw t y)
  have he : fibreCoefficientQuadraticTerm η v A.raw B.raw j = Complex.I • q := by
    funext t x
    simp only [fibreCoefficientQuadraticTerm, Pi.smul_apply, smul_eq_mul, q, b]
    ring
  have hm : AEStronglyMeasurable (Function.uncurry (Complex.I • q))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) :=
    aestronglyMeasurable_const.mul hq.2
  have hi : ‖Complex.I‖ₑ = 1 := by simp [enorm_eq_nnnorm]
  rw [he]
  refine ⟨?_, hm⟩
  have h := cellUlNorm_complex_smul univ Complex.I q hq.2
  rw [hi, one_mul] at h
  exact h.trans hq.1

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Error estimates for inverse solutions forced by parameter-dependent metric-gradient products. -/

/-- Inverse errors split into scalar, vector, coefficient, and lower-order state errors. -/
theorem cellInverse_metricFlux_difference_bound
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (A B : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (E D : ℝ → RawJet2 1 ℂ)
    (f g : ℝ → Vec 2 → ℂ) (F H : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (u w : ℝ → RawJet2 1 ℂ)
    (hA : cellMetricSupNorm A < ⊤) (hB : cellMetricSupNorm B < ⊤)
    (hAm : Measurable (Function.uncurry A)) (hBm : Measurable (Function.uncurry B))
    (hE : cellEnergyNorm univ E < ⊤) (hD : cellEnergyNorm univ D < ⊤)
    (hEm : ∀ a, AEStronglyMeasurable (fun p : ℝ × Vec 2 => E p.1 a p.2)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hDm : ∀ a, AEStronglyMeasurable (fun p : ℝ × Vec 2 => D p.1 a p.2)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hfm : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hgm : AEStronglyMeasurable (Function.uncurry g)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hFm : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hHm : AEStronglyMeasurable (Function.uncurry H)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hf : cellUlNorm univ f < ⊤) (hg : cellUlNorm univ g < ⊤)
    (hF : cellUlNorm univ F < ⊤) (hH : cellUlNorm univ H < ⊤)
    (hu : IsCellInverseValue ⟨G, v, 0, 0⟩ (fun t => cellQ0 (f t)) (F + cellMetricFlux B D) u)
    (hw : IsCellInverseValue ⟨G, v, 0, 0⟩ (fun t => cellQ0 (g t)) (H + cellMetricFlux A E) w) :
    cellEnergyNorm univ (w - u) ≤ ENNReal.ofReal 13 *
      (cellUlNorm univ (g - f) + cellUlNorm univ (H - F) +
        2 * cellMetricSupNorm (A - B) * cellEnergyNorm univ E +
        2 * cellMetricSupNorm B * cellEnergyNorm univ (E - D)) := by
  have hAEm := cellMetricFlux_aestronglyMeasurable univ A E hAm hEm
  have hBDm := cellMetricFlux_aestronglyMeasurable univ B D hBm hDm
  have hAE := cellMetricFlux_ul_bound univ A hA hAm E hEm
  have hBD := cellMetricFlux_ul_bound univ B hB hBm D hDm
  have hAEf := hAE.trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) hA) hE)
  have hBDf := hBD.trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) hB) hD)
  have hR := cellUlNorm_add univ H (cellMetricFlux A E) hHm hAEm
  have hS := cellUlNorm_add univ F (cellMetricFlux B D) hFm hBDm
  have hb := cellInverse_parameter_bound hG hG hv f g
    (F + cellMetricFlux B D) (H + cellMetricFlux A E) u w
    hfm hgm (hFm.add hBDm) (hHm.add hAEm) hf hg
    (hS.trans_lt (ENNReal.add_lt_top.mpr ⟨hF, hBDf⟩))
    (hR.trans_lt (ENNReal.add_lt_top.mpr ⟨hH, hAEf⟩)) hu hw
  have hzero : cellMetricSupNorm (G - G) = 0 := by simp [cellMetricSupNorm]
  rw [hzero, mul_zero, zero_mul, add_zero] at hb
  have he : H + cellMetricFlux A E - (F + cellMetricFlux B D) =
      (H - F) + (cellMetricFlux A E - cellMetricFlux B D) := by abel
  rw [he] at hb
  have hd := cellUlNorm_add univ (H - F) (cellMetricFlux A E - cellMetricFlux B D)
    (hHm.sub hFm) (hAEm.sub hBDm)
  have hd' := hd.trans (add_le_add le_rfl
    (cellMetricFlux_difference_ul_bound univ A B E D hA hB hAm hBm hEm hDm))
  refine hb.trans ?_
  rw [add_assoc, add_assoc]
  gcongr

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Actual scalar Taylor coefficient contributions have the expected linear energy bounds. -/

/-- The coordinate linear forcing is admissible, with its constant term present only at first order. -/
theorem fibreCoefficientLinearTerm_bound (η Cw : ℝ) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (p : ℕ × ℕ) (j : Fin 2) {C : CellCoefficients} (A : CellInverseDatum C) :
    cellUlNorm univ (fibreCoefficientLinearTerm η v A.raw p j) ≤
      ENNReal.ofReal Cw * ((if p = cellJetDirection j then 1 else 0) + cellEnergyNorm univ A.raw) ∧
    AEStronglyMeasurable (Function.uncurry (fibreCoefficientLinearTerm η v A.raw p j))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) := by
  let b := fun t x => -Complex.I * fibreDriftCoupling η v (fibreCoordinateFrequency j) t x
  have hb : Measurable (Function.uncurry b) :=
    (fibreDriftCoupling_measurable η hv (fibreCoordinateFrequency j)).const_mul _
  have hB (t : ℝ) (x : Vec 2) : ‖b t x‖ ≤ Cw := by
    have h := fibreDriftCoupling_norm_le η Cw v hw (fibreCoordinateFrequency j) t x
    simpa only [b, norm_mul, norm_neg, Complex.norm_I, one_mul,
      fibreCoordinateFrequency_norm, mul_one] using h
  by_cases hp : p = cellJetDirection j
  · have h := cellAffineMultiplier_ul_bound b Cw hb hB A.isInverse.1
    have he : fibreCoefficientLinearTerm η v A.raw p j =
        (fun t x => b t x * (1 + cellValue A.raw t x)) := by
      funext t x
      simp only [fibreCoefficientLinearTerm, ite_eq_left hp]
      rfl
    rw [he, ite_eq_left hp]
    exact h
  · have h := cellBoundedMultiplier_ul_bound b Cw hb hB A.isInverse.1
    have he : fibreCoefficientLinearTerm η v A.raw p j =
        (fun t x => b t x * cellValue A.raw t x) := by
      funext t x
      simp only [fibreCoefficientLinearTerm, ite_eq_right hp, zero_add]
      rfl
    rw [he, ite_eq_right hp, zero_add]
    exact h

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! Actual admissibility of the finite vector Taylor coefficient forcing. -/

/-- Every vector coefficient source is measurable and uniformly locally L2. -/
theorem fibreCoefficientFlux_admissible (η : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hGm : Measurable G)
    (hG : ∀ t i j, |G t i j| ≤ 2)
    {C : CellCoefficients} (A : ℕ × ℕ → CellInverseDatum C) (p : ℕ × ℕ) :
    cellUlNorm univ (fibreCoefficientFlux η G (fun a => (A a).raw) p) < ⊤ ∧
    AEStronglyMeasurable (Function.uncurry (fibreCoefficientFlux η G (fun a => (A a).raw) p))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) := by
  let f := fun j => fibreGraphFlux η G (fibreCoordinateFrequency j)
    (cellValue (A (fibreCoefficientPrevious p j)).raw)
  have hm (j : Fin 2) : AEStronglyMeasurable (Function.uncurry (f j))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) :=
    (fibreGraphFlux_ul_bound η hη G hGm hG (fibreCoordinateFrequency j)
      (A (fibreCoefficientPrevious p j)).isInverse.1).2
  have hf (j : Fin 2) : cellUlNorm univ (f j) < ⊤ := by
    have hn := (A (fibreCoefficientPrevious p j)).isInverse.2.2
    exact (fibreGraphFlux_ul_bound η hη G hGm hG (fibreCoordinateFrequency j)
      (A (fibreCoefficientPrevious p j)).isInverse.1).1.trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hn)
  have he : fibreCoefficientFlux η G (fun a => (A a).raw) p =
      ∑ j ∈ fibreCoefficientDirections p, f j := by
    funext t x
    simp only [fibreCoefficientFlux, Finset.sum_apply, f]
  rw [he]
  refine ⟨cellUlNorm_finset_sum_lt_top _ f (fun j _ => hm j) (fun j _ => hf j), ?_⟩
  simpa only [Function.uncurry_def, Finset.sum_apply] using
    cellFinite_sum_aestronglyMeasurable (fibreCoefficientDirections p)
      (fun j (z : ℝ × Vec 2) => f j z.1 z.2) (fun j _ => hm j)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.CycleEvolution

/-! Stability of the inverse under norm-convergent metric-gradient forcing, for arbitrary filters. -/

/-- Norm limits of the differentiated forcing imply the energy-norm limit of the actual inverse. -/
theorem cellInverse_metricFlux_tendsto {P : Type*} (l : Filter P)
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (A : P → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (B : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (E : P → ℝ → RawJet2 1 ℂ) (D : ℝ → RawJet2 1 ℂ)
    (f : P → ℝ → Vec 2 → ℂ) (f0 : ℝ → Vec 2 → ℂ)
    (F : P → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (F0 : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (w : P → ℝ → RawJet2 1 ℂ) (u : ℝ → RawJet2 1 ℂ)
    (hA : ∀ p, cellMetricSupNorm (A p) < ⊤ ∧ Measurable (Function.uncurry (A p)))
    (hB : cellMetricSupNorm B < ⊤ ∧ Measurable (Function.uncurry B))
    (hE : ∀ p, cellEnergyNorm univ (E p) < ⊤ ∧
      ∀ a, AEStronglyMeasurable (fun z : ℝ × Vec 2 => E p z.1 a z.2)
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hD : cellEnergyNorm univ D < ⊤ ∧
      ∀ a, AEStronglyMeasurable (fun z : ℝ × Vec 2 => D z.1 a z.2)
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hf : ∀ p, cellUlNorm univ (f p) < ⊤ ∧
      AEStronglyMeasurable (Function.uncurry (f p))
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hf0 : cellUlNorm univ f0 < ⊤ ∧ AEStronglyMeasurable (Function.uncurry f0)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hF : ∀ p, cellUlNorm univ (F p) < ⊤ ∧
      AEStronglyMeasurable (Function.uncurry (F p))
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hF0 : cellUlNorm univ F0 < ⊤ ∧ AEStronglyMeasurable (Function.uncurry F0)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hw : ∀ p, IsCellInverseValue ⟨G, v, 0, 0⟩ (fun t => cellQ0 (f p t))
      (F p + cellMetricFlux (A p) (E p)) (w p))
    (hu : IsCellInverseValue ⟨G, v, 0, 0⟩ (fun t => cellQ0 (f0 t))
      (F0 + cellMetricFlux B D) u)
    (hAc : Tendsto (fun p => cellMetricSupNorm (A p - B)) l (𝓝 0))
    (hEc : Tendsto (fun p => cellEnergyNorm univ (E p - D)) l (𝓝 0))
    (hfc : Tendsto (fun p => cellUlNorm univ (f p - f0)) l (𝓝 0))
    (hFc : Tendsto (fun p => cellUlNorm univ (F p - F0)) l (𝓝 0)) :
    Tendsto (fun p => cellEnergyNorm univ (w p - u)) l (𝓝 0) := by
  have hb (p : P) : cellEnergyNorm univ (w p - u) ≤ ENNReal.ofReal 13 *
      (cellUlNorm univ (f p - f0) + cellUlNorm univ (F p - F0) +
        2 * cellMetricSupNorm (A p - B) *
          (cellEnergyNorm univ (E p - D) + cellEnergyNorm univ D) +
        2 * cellMetricSupNorm B * cellEnergyNorm univ (E p - D)) := by
    have hh := cellInverse_metricFlux_difference_bound hG hv (A p) B (E p) D
      f0 (f p) F0 (F p) u (w p) (hA p).1 hB.1 (hA p).2 hB.2
      (hE p).1 hD.1 (hE p).2 hD.2 hf0.2 (hf p).2 hF0.2 (hF p).2
      hf0.1 (hf p).1 hF0.1 (hF p).1 hu (hw p)
    have he := cellEnergyNorm_le_sub_add univ (E p) D (hE p).2 hD.2
    exact hh.trans (by gcongr)
  have hlim := ennreal_bilinear_error_tendsto_zero l
    (fun p => cellUlNorm univ (f p - f0)) (fun p => cellUlNorm univ (F p - F0))
    (fun p => cellMetricSupNorm (A p - B)) (fun p => cellEnergyNorm univ (E p - D))
    (cellMetricSupNorm B) (cellEnergyNorm univ D) hB.1.ne hD.1.ne hfc hFc hAc hEc
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) hb

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Every-time spatial bounds for the literal linear coefficient forcing. -/

/-- The linear coefficient forcing has the same majorant on every spatial trace. -/
theorem fibreCoefficientLinearTerm_cellL2Norm_le (η Cw : ℝ) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (p : ℕ × ℕ) (j : Fin 2) {C : CellCoefficients} (A : CellInverseDatum C) (t : ℝ) :
    cellL2Norm (fibreCoefficientLinearTerm η v A.raw p j t) ≤
      ENNReal.ofReal Cw * ((if p = cellJetDirection j then 1 else 0) + cellEnergyNorm univ A.raw) := by
  let b := fun x => -Complex.I * fibreDriftCoupling η v (fibreCoordinateFrequency j) t x
  have hb : Measurable b := ((fibreDriftCoupling_measurable η hv
    (fibreCoordinateFrequency j)).const_mul (-Complex.I)).comp
      ((measurable_const (a := t)).prodMk measurable_id)
  have hB (x : Vec 2) : ‖b x‖ ≤ Cw := by
    simpa only [b, norm_mul, norm_neg, Complex.norm_I, one_mul,
      fibreCoordinateFrequency_norm, mul_one] using
      fibreDriftCoupling_norm_le η Cw v hw (fibreCoordinateFrequency j) t x
  have hf := (A.isInverse.1.2.2.1 t (mem_univ t)).1
  by_cases hp : p = cellJetDirection j
  · have he : fibreCoefficientLinearTerm η v A.raw p j t =
        (fun x => b x * (1 + cellValue A.raw t x)) := by
      funext x
      simp only [fibreCoefficientLinearTerm, ite_eq_left hp]
      rfl
    rw [he, ite_eq_left hp]
    exact (cellAffineMultiplier_cellL2Norm_le b (cellValue A.raw t) Cw hb hB hf).trans
      (mul_le_mul' le_rfl (add_le_add le_rfl (cellValue_cellL2Norm_le_energy A.raw t)))
  · have he : fibreCoefficientLinearTerm η v A.raw p j t =
        (fun x => b x * cellValue A.raw t x) := by
      funext x
      simp only [fibreCoefficientLinearTerm, ite_eq_right hp, zero_add]
      rfl
    rw [he, ite_eq_right hp, zero_add]
    have hm := (cellMultiplier_memLp b (cellValue A.raw t) Cw hb hB hf).aestronglyMeasurable
    exact (cellL2Norm_mul_le b (cellValue A.raw t) Cw hm
      (Filter.Eventually.of_forall hB)).trans
      (mul_le_mul' le_rfl (cellValue_cellL2Norm_le_energy A.raw t))

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! The complete finite quadratic Taylor forcing is an actual admissible source. -/

/-- All quadratic coefficient forcing terms are jointly almost measurable and uniformly locally L2. -/
theorem fibreCoefficientQuadraticSource_admissible (η Cw : ℝ) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    {C : CellCoefficients} (A : ℕ × ℕ → CellInverseDatum C) (p : ℕ × ℕ) :
    cellUlNorm univ (fibreCoefficientQuadraticSource η v (fun a => (A a).raw) p) < ⊤ ∧
    AEStronglyMeasurable
      (Function.uncurry (fibreCoefficientQuadraticSource η v (fun a => (A a).raw) p))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) := by
  let f := fun j a => fibreCoefficientQuadraticTerm η v (A a).raw
    (A (fibreCoefficientComplement (fibreCoefficientPrevious p j) a)).raw j
  have hm (j : Fin 2) (a : ℕ × ℕ) : AEStronglyMeasurable (Function.uncurry (f j a))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) :=
    (fibreCoefficientQuadraticTerm_bound η Cw hv hw j (A a)
      (A (fibreCoefficientComplement (fibreCoefficientPrevious p j) a))).2
  have hf (j : Fin 2) (a : ℕ × ℕ) : cellUlNorm univ (f j a) < ⊤ := by
    have ha := (A a).isInverse.2.2
    have hb := (A (fibreCoefficientComplement (fibreCoefficientPrevious p j) a)).isInverse.2.2
    exact (fibreCoefficientQuadraticTerm_bound η Cw hv hw j (A a)
      (A (fibreCoefficientComplement (fibreCoefficientPrevious p j) a))).1.trans_lt (by finiteness)
  let g := fun j => ∑ a ∈ fibreCoefficientPairs (fibreCoefficientPrevious p j), f j a
  have hgm (j : Fin 2) : AEStronglyMeasurable (Function.uncurry (g j))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) := by
    simpa only [Function.uncurry_def, Finset.sum_apply, g] using
      cellFinite_sum_aestronglyMeasurable (fibreCoefficientPairs (fibreCoefficientPrevious p j))
        (fun a (z : ℝ × Vec 2) => f j a z.1 z.2) (fun a _ => hm j a)
  have hgf (j : Fin 2) : cellUlNorm univ (g j) < ⊤ :=
    cellUlNorm_finset_sum_lt_top _ (f j) (fun a _ => hm j a) (fun a _ => hf j a)
  have he : fibreCoefficientQuadraticSource η v (fun a => (A a).raw) p =
      ∑ j ∈ fibreCoefficientDirections p, g j := by
    funext t x
    simp only [fibreCoefficientQuadraticSource, Finset.sum_apply, f, g]
  rw [he]
  refine ⟨cellUlNorm_finset_sum_lt_top _ g (fun j _ => hgm j) (fun j _ => hgf j), ?_⟩
  simpa only [Function.uncurry_def, Finset.sum_apply] using
    cellFinite_sum_aestronglyMeasurable (fibreCoefficientDirections p)
      (fun j (z : ℝ × Vec 2) => g j z.1 z.2) (fun j _ => hgm j)

/-! Quantitative finite vector source bounds for actual fibre coefficients. -/

/-- The coordinate vector forcing is bounded by eight times the sum of the lower actual energies. -/
theorem fibreCoefficientFlux_ul_bound (η : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hGm : Measurable G)
    (hG : ∀ t i j, |G t i j| ≤ 2)
    {C : CellCoefficients} (A : ℕ × ℕ → CellInverseDatum C) (p : ℕ × ℕ) :
    cellUlNorm univ (fibreCoefficientFlux η G (fun a => (A a).raw) p) ≤
      ∑ j ∈ fibreCoefficientDirections p, 8 * cellEnergyNorm univ (A (fibreCoefficientPrevious p j)).raw := by
  let f := fun j => fibreGraphFlux η G (fibreCoordinateFrequency j)
    (cellValue (A (fibreCoefficientPrevious p j)).raw)
  have hm (j : Fin 2) : AEStronglyMeasurable (Function.uncurry (f j))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) :=
    (fibreGraphFlux_ul_bound η hη G hGm hG (fibreCoordinateFrequency j)
      (A (fibreCoefficientPrevious p j)).isInverse.1).2
  have he : fibreCoefficientFlux η G (fun a => (A a).raw) p =
      ∑ j ∈ fibreCoefficientDirections p, f j := by
    funext t x
    simp only [fibreCoefficientFlux, Finset.sum_apply, f]
  rw [he]
  apply (cellUlNorm_finset_sum_le _ f (fun j _ => hm j)).trans
  apply Finset.sum_le_sum
  intro j _
  simpa only [fibreCoordinateFrequency_norm, mul_one, ENNReal.ofReal_ofNat] using
    (fibreGraphFlux_ul_bound η hη G hGm hG (fibreCoordinateFrequency j)
      (A (fibreCoefficientPrevious p j)).isInverse.1).1

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! The first graph response is an actual cell inverse with a uniform frequency-linear bound. -/

/-- The literal zero trajectory has zero all-time cell energy. -/
theorem cellEnergyNorm_zero : cellEnergyNorm univ (0 : ℝ → RawJet2 1 ℂ) = 0 := by
  have hg : cellGradient (0 : RawJet2 1 ℂ) = 0 := by
    funext x
    apply PiLp.ext
    intro k
    rfl
  simp [cellEnergyNorm, cellValue, cellUlNorm, cellL2Norm, hg]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! Quantitative quadratic source bounds for the actual triangular fibre coefficients. -/

/-- The quadratic coefficient source has the complete finite convolution of the actual energy bounds. -/
theorem fibreCoefficientQuadraticSource_ul_bound (η Cw : ℝ) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    {C : CellCoefficients} (A : ℕ × ℕ → CellInverseDatum C) (p : ℕ × ℕ) :
    cellUlNorm univ (fibreCoefficientQuadraticSource η v (fun a => (A a).raw) p) ≤
      ∑ j ∈ fibreCoefficientDirections p,
        ∑ a ∈ fibreCoefficientPairs (fibreCoefficientPrevious p j),
          ENNReal.ofReal Cw *
            cellEnergyNorm univ (A (fibreCoefficientComplement (fibreCoefficientPrevious p j) a)).raw *
            cellEnergyNorm univ (A a).raw := by
  let f := fun j a => fibreCoefficientQuadraticTerm η v (A a).raw
    (A (fibreCoefficientComplement (fibreCoefficientPrevious p j) a)).raw j
  have hm (j : Fin 2) (a : ℕ × ℕ) : AEStronglyMeasurable (Function.uncurry (f j a))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) :=
    (fibreCoefficientQuadraticTerm_bound η Cw hv hw j (A a)
      (A (fibreCoefficientComplement (fibreCoefficientPrevious p j) a))).2
  let g := fun j => ∑ a ∈ fibreCoefficientPairs (fibreCoefficientPrevious p j), f j a
  have hgm (j : Fin 2) : AEStronglyMeasurable (Function.uncurry (g j))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) := by
    simpa only [Function.uncurry_def, Finset.sum_apply, g] using
      cellFinite_sum_aestronglyMeasurable (fibreCoefficientPairs (fibreCoefficientPrevious p j))
        (fun a (z : ℝ × Vec 2) => f j a z.1 z.2) (fun a _ => hm j a)
  have he : fibreCoefficientQuadraticSource η v (fun a => (A a).raw) p =
      ∑ j ∈ fibreCoefficientDirections p, g j := by
    funext t x
    simp only [fibreCoefficientQuadraticSource, Finset.sum_apply, f, g]
  rw [he]
  apply (cellUlNorm_finset_sum_le _ g (fun j _ => hgm j)).trans
  apply Finset.sum_le_sum
  intro j _
  apply (cellUlNorm_finset_sum_le _ (f j) (fun a _ => hm j a)).trans
  apply Finset.sum_le_sum
  intro a _
  exact (fibreCoefficientQuadraticTerm_bound η Cw hv hw j (A a)
    (A (fibreCoefficientComplement (fibreCoefficientPrevious p j) a))).1

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! Uniform time bounds for the literal drift-mean symbol coefficients. -/

/-- Actual lower inverse states control the coordinate mean symbol uniformly at every time. -/
theorem fibreCoefficientDriftSymbol_uniform_le (η Cw : ℝ) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    {C : CellCoefficients} (A : ℕ × ℕ → CellInverseDatum C) (p : ℕ × ℕ) :
    (⨆ t, ‖fibreCoefficientDriftSymbol η v (fun a => (A a).raw) p t‖ₑ) ≤
      ∑ j ∈ fibreCoefficientDirections p, ENNReal.ofReal Cw *
        cellEnergyNorm Set.univ (A (fibreCoefficientPrevious p j)).raw := by
  apply iSup_le
  intro t
  apply (enorm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  let b := fibreDriftCoupling η v (fibreCoordinateFrequency j)
  have hb := fibreDriftCoupling_measurable η hv (fibreCoordinateFrequency j)
  have hB s x : ‖b s x‖ ≤ Cw := by
    simpa only [fibreCoordinateFrequency_norm, mul_one] using
      fibreDriftCoupling_norm_le η Cw v hw (fibreCoordinateFrequency j) s x
  have hi : ‖-Complex.I‖ₑ = 1 := by simp [enorm_eq_nnnorm]
  rw [enorm_mul, hi, one_mul]
  exact cellBoundedMean_energy_bound b Cw hb hB
    (A (fibreCoefficientPrevious p j)).isInverse.1 t

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! Actual admissibility of the finite linear Taylor forcing at every coefficient order. -/

/-- The complete linear Taylor source is jointly almost measurable and uniformly locally L2. -/
theorem fibreCoefficientLinearSource_admissible (η Cw : ℝ) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    {C : CellCoefficients} (A : ℕ × ℕ → CellInverseDatum C) (p : ℕ × ℕ) :
    cellUlNorm univ (fibreCoefficientLinearSource η v (fun a => (A a).raw) p) < ⊤ ∧
    AEStronglyMeasurable
      (Function.uncurry (fibreCoefficientLinearSource η v (fun a => (A a).raw) p))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) := by
  let f := fun j => fibreCoefficientLinearTerm η v (A (fibreCoefficientPrevious p j)).raw p j
  have hm (j : Fin 2) : AEStronglyMeasurable (Function.uncurry (f j))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) :=
    (fibreCoefficientLinearTerm_bound η Cw hv hw p j (A (fibreCoefficientPrevious p j))).2
  have hf (j : Fin 2) : cellUlNorm univ (f j) < ⊤ := by
    have hn := (A (fibreCoefficientPrevious p j)).isInverse.2.2
    exact (fibreCoefficientLinearTerm_bound η Cw hv hw p j
      (A (fibreCoefficientPrevious p j))).1.trans_lt (by finiteness)
  have he : fibreCoefficientLinearSource η v (fun a => (A a).raw) p =
      ∑ j ∈ fibreCoefficientDirections p, f j := by
    funext t x
    simp only [fibreCoefficientLinearSource, Finset.sum_apply, f]
  rw [he]
  refine ⟨cellUlNorm_finset_sum_lt_top _ f (fun j _ => hm j) (fun j _ => hf j), ?_⟩
  simpa only [Function.uncurry_def, Finset.sum_apply] using
    cellFinite_sum_aestronglyMeasurable (fibreCoefficientDirections p)
      (fun j (z : ℝ × Vec 2) => f j z.1 z.2) (fun j _ => hm j)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Every-time spatial bounds for literal quadratic coefficient forcing. -/

/-- The quadratic coefficient forcing satisfies its actual product majorant at every time. -/
theorem fibreCoefficientQuadraticTerm_cellL2Norm_le (η Cw : ℝ) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (j : Fin 2) {C : CellCoefficients} (A B : CellInverseDatum C) (t : ℝ) :
    cellL2Norm (fibreCoefficientQuadraticTerm η v A.raw B.raw j t) ≤
      ENNReal.ofReal Cw * cellEnergyNorm univ B.raw * cellEnergyNorm univ A.raw := by
  let b := fibreDriftCoupling η v (fibreCoordinateFrequency j)
  let m := cellMean (fun y => b t y * cellValue B.raw t y)
  have hb := fibreDriftCoupling_measurable η hv (fibreCoordinateFrequency j)
  have hB (s : ℝ) (x : Vec 2) : ‖b s x‖ ≤ Cw := by
    simpa only [fibreCoordinateFrequency_norm, mul_one] using
      fibreDriftCoupling_norm_le η Cw v hw (fibreCoordinateFrequency j) s x
  have hm : ‖m‖ₑ ≤ ENNReal.ofReal Cw * cellEnergyNorm univ B.raw :=
    cellBoundedMean_energy_bound b Cw hb hB B.isInverse.1 t
  have he : fibreCoefficientQuadraticTerm η v A.raw B.raw j t =
      (Complex.I * m) • cellValue A.raw t := by
    funext x
    simp only [fibreCoefficientQuadraticTerm, Pi.smul_apply, smul_eq_mul, m, b]
    ring
  change eLpNorm _ 2 _ ≤ _
  rw [he, eLpNorm_const_smul, enorm_mul]
  have hi : ‖Complex.I‖ₑ = 1 := by simp [enorm_eq_nnnorm]
  rw [hi, one_mul]
  exact mul_le_mul' hm (cellValue_cellL2Norm_le_energy A.raw t)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.CycleEvolution

/-! Directional differentiation of the actual cell inverse by its exact difference-quotient equation. -/

/-- Norm-convergent coefficient and source quotients yield the actual inverse derivative.
The lower-order continuity premise is supplied by `cellInverse_norm_continuous`. -/
theorem cellInverse_directional_derivative_of_continuity
    (G : ℝ → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (f : ℝ → ℝ → Vec 2 → ℂ)
    (F : ℝ → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D : ℝ → ℝ → RawJet2 1 ℂ)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hG : ∀ h, IsCellMetric (G h))
    (hf : ∀ h, cellUlNorm univ (f h) < ⊤ ∧
      AEStronglyMeasurable (Function.uncurry (f h))
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hF : ∀ h, cellUlNorm univ (F h) < ⊤ ∧
      AEStronglyMeasurable (Function.uncurry (F h))
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hD : ∀ h, IsCellInverseValue ⟨G h, v, 0, 0⟩ (fun t => cellQ0 (f h t)) (F h) (D h))
    (A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (f1 : ℝ → Vec 2 → ℂ) (F1 : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hA : cellMetricSupNorm A < ⊤ ∧ Measurable (Function.uncurry A))
    (hf1 : cellUlNorm univ f1 < ⊤ ∧ AEStronglyMeasurable (Function.uncurry f1)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hF1 : cellUlNorm univ F1 < ⊤ ∧ AEStronglyMeasurable (Function.uncurry F1)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hGc : Tendsto (fun h : ℝ => cellMetricSupNorm (h⁻¹ • (G h - G 0) - A)) (𝓝[≠] 0) (𝓝 0))
    (hfc : Tendsto (fun h : ℝ => cellUlNorm univ (h⁻¹ • (f h - f 0) - f1)) (𝓝[≠] 0) (𝓝 0))
    (hFc : Tendsto (fun h : ℝ => cellUlNorm univ (h⁻¹ • (F h - F 0) - F1)) (𝓝[≠] 0) (𝓝 0))
    (hDc : Tendsto (fun h : ℝ => cellEnergyNorm univ (D h - D 0)) (𝓝[≠] 0) (𝓝 0)) :
    ∃ D1 : ℝ → RawJet2 1 ℂ,
      IsCellInverseValue ⟨G 0, v, 0, 0⟩ (fun t => cellQ0 (f1 t))
        (F1 + cellMetricFlux A (D 0)) D1 ∧
      Tendsto (fun h : ℝ => cellEnergyNorm univ (h⁻¹ • (D h - D 0) - D1))
        (𝓝[≠] 0) (𝓝 0) := by
  obtain ⟨D1, hD1, _⟩ := cellInverse_metricJetStep_exists (hG 0) hv A hA.1 hA.2 f1 F1
    hf1.2 hF1.2 hf1.1 hF1.1 (D 0) (hD 0).1.2.2.2.1 (hD 0).2.2
  let qG := fun h : ℝ => h⁻¹ • (G h - G 0)
  let qf := fun h : ℝ => h⁻¹ • (f h - f 0)
  let qF := fun h : ℝ => h⁻¹ • (F h - F 0)
  let qD := fun h : ℝ => h⁻¹ • (D h - D 0)
  have hqG (h : ℝ) : cellMetricSupNorm (qG h) < ⊤ ∧
      Measurable (Function.uncurry (qG h)) := by
    refine ⟨?_, cellMetric_measurable_smul h⁻¹ (G h - G 0)
      (cellMetric_measurable_sub (G h) (G 0) (hG h).1 (hG 0).1)⟩
    exact (cellMetricSupNorm_smul h⁻¹ (G h - G 0)).trans_lt
      (ENNReal.mul_lt_top enorm_lt_top (cellMetricSupNorm_sub_lt_top (hG 0) (hG h)))
  have hqf (h : ℝ) : cellUlNorm univ (qf h) < ⊤ ∧
      AEStronglyMeasurable (Function.uncurry (qf h))
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) := by
    refine ⟨?_, ((hf h).2.sub (hf 0).2).const_smul h⁻¹⟩
    exact (cellUlNorm_smul univ h⁻¹ (f h - f 0) ((hf h).2.sub (hf 0).2)).trans_lt
      (ENNReal.mul_lt_top enorm_lt_top ((cellUlNorm_sub univ (f h) (f 0) (hf h).2 (hf 0).2).trans_lt
        (ENNReal.add_lt_top.mpr ⟨(hf h).1, (hf 0).1⟩)))
  have hqF (h : ℝ) : cellUlNorm univ (qF h) < ⊤ ∧
      AEStronglyMeasurable (Function.uncurry (qF h))
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) := by
    refine ⟨?_, ((hF h).2.sub (hF 0).2).const_smul h⁻¹⟩
    exact (cellUlNorm_smul univ h⁻¹ (F h - F 0) ((hF h).2.sub (hF 0).2)).trans_lt
      (ENNReal.mul_lt_top enorm_lt_top ((cellUlNorm_sub univ (F h) (F 0) (hF h).2 (hF 0).2).trans_lt
        (ENNReal.add_lt_top.mpr ⟨(hF h).1, (hF 0).1⟩)))
  have hqD (h : ℝ) : IsCellInverseValue ⟨G 0, v, 0, 0⟩ (fun t => cellQ0 (qf h t))
      (qF h + cellMetricFlux (qG h) (D h)) (qD h) :=
    cellInverse_scaled_parameter_difference (hG 0) (hG h) v (f 0) (f h) (F 0) (F h) (D 0) (D h)
      (hf 0).2 (hf h).2 (hf 0).1 (hf h).1 (hD 0) (hD h) h⁻¹
  refine ⟨D1, hD1, ?_⟩
  exact cellInverse_metricFlux_tendsto (𝓝[≠] (0 : ℝ)) (hG 0) hv qG A D (D 0)
    qf f1 qF F1 qD D1 hqG hA
    (fun h => ⟨(hD h).2.2, (hD h).1.2.2.2.1⟩)
    ⟨(hD 0).2.2, (hD 0).1.2.2.2.1⟩ hqf hf1 hqF hF1 hqD hD1 hGc hDc hfc hFc

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! Quantitative finite linear source bounds for the actual triangular fibre coefficients. -/

/-- The complete scalar linear coefficient forcing has the sum of its actual lower-state bounds. -/
theorem fibreCoefficientLinearSource_ul_bound (η Cw : ℝ) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    {C : CellCoefficients} (A : ℕ × ℕ → CellInverseDatum C) (p : ℕ × ℕ) :
    cellUlNorm univ (fibreCoefficientLinearSource η v (fun a => (A a).raw) p) ≤
      ∑ j ∈ fibreCoefficientDirections p, ENNReal.ofReal Cw *
        ((if p = cellJetDirection j then 1 else 0) +
          cellEnergyNorm univ (A (fibreCoefficientPrevious p j)).raw) := by
  let f := fun j => fibreCoefficientLinearTerm η v (A (fibreCoefficientPrevious p j)).raw p j
  have hm (j : Fin 2) : AEStronglyMeasurable (Function.uncurry (f j))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) :=
    (fibreCoefficientLinearTerm_bound η Cw hv hw p j (A (fibreCoefficientPrevious p j))).2
  have he : fibreCoefficientLinearSource η v (fun a => (A a).raw) p =
      ∑ j ∈ fibreCoefficientDirections p, f j := by
    funext t x
    simp only [fibreCoefficientLinearSource, Finset.sum_apply, f]
  rw [he]
  apply (cellUlNorm_finset_sum_le _ f (fun j _ => hm j)).trans
  apply Finset.sum_le_sum
  intro j _
  exact (fibreCoefficientLinearTerm_bound η Cw hv hw p j (A (fibreCoefficientPrevious p j))).1

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The flux difference separates a trajectory difference from the metric perturbation. -/

theorem fibreGraphFlux_metric_difference (η : ℝ)
    (G H : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (ξ : Fin 2 → ℂ)
    (r s : ℝ → Vec 2 → ℂ) :
    fibreGraphFlux η G ξ r - fibreGraphFlux η H ξ s =
      fibreGraphFlux η H ξ (r - s) + fibreGraphFlux η (G - H) ξ r := by
  funext t x
  apply PiLp.ext
  intro k
  simp only [fibreGraphFlux, Pi.sub_apply, Pi.add_apply, PiLp.sub_apply,
    PiLp.add_apply, Matrix.sub_apply, Fin.sum_univ_two, Complex.ofReal_sub]
  ring

theorem fibreGraphFlux_metric_difference_ul_bound (η : ℝ) (hη : η ≤ 1)
    (G H : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hGm : Measurable G) (hHm : Measurable H)
    (hH : ∀ t i j, |H t i j| ≤ 2) (B : ℝ) (hB : 0 ≤ B)
    (hd : ∀ t i j, |(G t - H t) i j| ≤ B) (ξ : Fin 2 → ℂ)
    {C C' : CellCoefficients} {src src' : ℝ → Vec 2 → ℂ}
    {F F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    {D E : ℝ → RawJet2 1 ℂ}
    (hD : IsCellSolution univ C src F D)
    (hdiff : IsCellSolution univ C' src' F' (D - E)) :
    cellUlNorm univ (fibreGraphFlux η G ξ (cellValue D) -
      fibreGraphFlux η H ξ (cellValue E)) ≤
      ENNReal.ofReal (8 * fibreNorm ξ) * cellEnergyNorm univ (D - E) +
        ENNReal.ofReal (4 * B * fibreNorm ξ) * cellEnergyNorm univ D := by
  have hgm : Measurable (G - H) :=
    Measurable.of_eval (fun i => Measurable.of_eval (fun j =>
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hGm)).sub
        ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hHm))))
  have hm1 := (fibreGraphFlux_ul_bound η hη H hHm hH ξ hdiff).2
  have hm2 : AEStronglyMeasurable
      (Function.uncurry (fibreGraphFlux η (G - H) ξ (cellValue D)))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) := by
    apply cellFiniteArray_aestronglyMeasurable
    intro k
    exact ((fibreGraphFlux_coefficient_measurable η (G - H) hgm ξ k).comp
      measurable_fst).aestronglyMeasurable.mul (hD.2.2.2.1 (valueIndex2 1))
  have hv : cellValue D - cellValue E = cellValue (D - E) := rfl
  rw [fibreGraphFlux_metric_difference, hv]
  exact (cellUlNorm_add univ _ _ hm1 hm2).trans
    (add_le_add (fibreGraphFlux_ul_bound η hη H hHm hH ξ hdiff).1
      (fibreGraphFlux_ul_bound_entry_size η hη (G - H) B hB hd ξ hD))

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! Every-time scalar forcing majorants for the literal triangular family. -/

/-- Every spatial trace of the scalar coefficient forcing satisfies the actual finite convolution majorant. -/
theorem fibreCoefficientSource_cellL2Norm_le (η Cw : ℝ) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    {C : CellCoefficients} (A : ℕ × ℕ → CellInverseDatum C) (p : ℕ × ℕ) (t : ℝ) :
    cellL2Norm (fibreCoefficientSource η v (fun a => (A a).raw) p t) ≤
      ((∑ j ∈ fibreCoefficientDirections p, ENNReal.ofReal Cw *
        ((if p = cellJetDirection j then 1 else 0) +
          cellEnergyNorm univ (A (fibreCoefficientPrevious p j)).raw)) +
       (∑ j ∈ fibreCoefficientDirections p,
        ∑ a ∈ fibreCoefficientPairs (fibreCoefficientPrevious p j), ENNReal.ofReal Cw *
          cellEnergyNorm univ (A (fibreCoefficientComplement (fibreCoefficientPrevious p j) a)).raw *
          cellEnergyNorm univ (A a).raw)) := by
  have hl : cellL2Norm (fibreCoefficientLinearSource η v (fun a => (A a).raw) p t) ≤
      ∑ j ∈ fibreCoefficientDirections p, ENNReal.ofReal Cw *
        ((if p = cellJetDirection j then 1 else 0) +
          cellEnergyNorm univ (A (fibreCoefficientPrevious p j)).raw) := by
    have he : fibreCoefficientLinearSource η v (fun a => (A a).raw) p t =
        ∑ j ∈ fibreCoefficientDirections p,
          fibreCoefficientLinearTerm η v (A (fibreCoefficientPrevious p j)).raw p j t := by
      funext x
      simp only [fibreCoefficientLinearSource, Finset.sum_apply]
    rw [he]
    exact (eLpNorm_sum_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
      (Finset.sum_le_sum (fun j _ =>
        fibreCoefficientLinearTerm_cellL2Norm_le η Cw hv hw p j _ t))
  have hq : cellL2Norm (fibreCoefficientQuadraticSource η v (fun a => (A a).raw) p t) ≤
      ∑ j ∈ fibreCoefficientDirections p,
        ∑ a ∈ fibreCoefficientPairs (fibreCoefficientPrevious p j), ENNReal.ofReal Cw *
          cellEnergyNorm univ (A (fibreCoefficientComplement (fibreCoefficientPrevious p j) a)).raw *
          cellEnergyNorm univ (A a).raw := by
    have he : fibreCoefficientQuadraticSource η v (fun a => (A a).raw) p t =
        ∑ j ∈ fibreCoefficientDirections p,
          ∑ a ∈ fibreCoefficientPairs (fibreCoefficientPrevious p j),
            fibreCoefficientQuadraticTerm η v (A a).raw
              (A (fibreCoefficientComplement (fibreCoefficientPrevious p j) a)).raw j t := by
      funext x
      simp only [fibreCoefficientQuadraticSource, Finset.sum_apply]
    rw [he]
    apply (eLpNorm_sum_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
    apply Finset.sum_le_sum
    intro j _
    exact (eLpNorm_sum_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
      (Finset.sum_le_sum (fun a _ =>
        fibreCoefficientQuadraticTerm_cellL2Norm_le η Cw hv hw j _ _ t))
  exact (eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans (add_le_add hl hq)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.CycleEvolution

/-! Every actual triangular cell jet family is energy-norm continuous when its input jets are norm continuous. -/

/-- Triangular dependence and actual inverse stability propagate continuity through every finite jet order. -/
theorem cellInverse_jetFamily_continuous {P : Type*} [TopologicalSpace P] (K : ℕ)
    (Gj : ℕ × ℕ → P → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (fj : ℕ × ℕ → P → ℝ → Vec 2 → ℂ)
    (Fj : ℕ × ℕ → P → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (cj : ℕ × ℕ → P → ℝ → RawJet2 1 ℂ)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hG0 : ∀ Y, IsCellMetric (Gj 0 Y))
    (hdata : ∀ α : ℕ × ℕ, α.1 + α.2 ≤ K → ∀ Y,
      cellMetricSupNorm (Gj α Y) < ⊤ ∧ Measurable (Function.uncurry (Gj α Y)) ∧
      cellUlNorm univ (fj α Y) < ⊤ ∧ cellUlNorm univ (Fj α Y) < ⊤ ∧
      AEStronglyMeasurable (Function.uncurry (fj α Y))
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) ∧
      AEStronglyMeasurable (Function.uncurry (Fj α Y))
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hsol : ∀ Y, ∀ α : ℕ × ℕ, α.1 + α.2 ≤ K →
      IsCellInverseValue ⟨Gj 0 Y, v, 0, 0⟩ (fun t => cellQ0 (fj α Y t))
        (Fj α Y + cellMetricJetFlux (fun β => Gj β Y) (fun β => cj β Y) α) (cj α Y))
    (hGc : ∀ α : ℕ × ℕ, α.1 + α.2 ≤ K → ∀ Y0,
      Tendsto (fun Y => cellMetricSupNorm (Gj α Y - Gj α Y0)) (𝓝 Y0) (𝓝 0))
    (hfc : ∀ α : ℕ × ℕ, α.1 + α.2 ≤ K → ∀ Y0,
      Tendsto (fun Y => cellUlNorm univ (fj α Y - fj α Y0)) (𝓝 Y0) (𝓝 0))
    (hFc : ∀ α : ℕ × ℕ, α.1 + α.2 ≤ K → ∀ Y0,
      Tendsto (fun Y => cellUlNorm univ (Fj α Y - Fj α Y0)) (𝓝 Y0) (𝓝 0)) :
    ∀ α : ℕ × ℕ, α.1 + α.2 ≤ K → ∀ Y0,
      Tendsto (fun Y => cellEnergyNorm univ (cj α Y - cj α Y0)) (𝓝 Y0) (𝓝 0) := by
  have hall (n : ℕ) : ∀ α : ℕ × ℕ, α.1 + α.2 = n → α.1 + α.2 ≤ K → ∀ Y0,
      Tendsto (fun Y => cellEnergyNorm univ (cj α Y - cj α Y0)) (𝓝 Y0) (𝓝 0) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro α heα hα Y0
      have hβord (β : ℕ × ℕ) (hβ : β ∈ cellJetFluxIndices α) : β.1 + β.2 ≤ K :=
        (cellJetFluxIndices_metric_order hβ).trans hα
      have hγord (β : ℕ × ℕ) (hβ : β ∈ cellJetFluxIndices α) :
          (α.1 - β.1) + (α.2 - β.2) ≤ K :=
        (Nat.le_of_lt (cellJetFluxIndices_lower_order hβ)).trans hα
      have hjm (Y : P) := cellMetricJetFlux_aestronglyMeasurable
        (fun β => Gj β Y) (fun β => cj β Y) α
        (fun β hβ => (hdata β (hβord β hβ) Y).2.1)
        (fun β hβ => (hsol Y (α.1 - β.1, α.2 - β.2) (hγord β hβ)).1.2.2.2.1)
      have hjf (Y : P) := cellMetricJetFlux_ul_lt_top
        (fun β => Gj β Y) (fun β => cj β Y) α
        (fun β hβ => (hdata β (hβord β hβ) Y).1)
        (fun β hβ => (hdata β (hβord β hβ) Y).2.1)
        (fun β hβ => (hsol Y (α.1 - β.1, α.2 - β.2) (hγord β hβ)).2.2)
        (fun β hβ => (hsol Y (α.1 - β.1, α.2 - β.2) (hγord β hβ)).1.2.2.2.1)
      have hjc := cellMetricJetFlux_tendsto (𝓝 Y0) Gj (fun β => Gj β Y0)
        cj (fun β => cj β Y0) α
        (fun β hβ Y => ⟨(hdata β (hβord β hβ) Y).1, (hdata β (hβord β hβ) Y).2.1⟩)
        (fun β hβ => ⟨(hdata β (hβord β hβ) Y0).1, (hdata β (hβord β hβ) Y0).2.1⟩)
        (fun β hβ => (hsol Y0 (α.1 - β.1, α.2 - β.2) (hγord β hβ)).2.2)
        (fun β hβ Y => (hsol Y (α.1 - β.1, α.2 - β.2) (hγord β hβ)).1.2.2.2.1)
        (fun β hβ => (hsol Y0 (α.1 - β.1, α.2 - β.2) (hγord β hβ)).1.2.2.2.1)
        (fun β hβ => hGc β (hβord β hβ) Y0)
        (fun β hβ => ih ((α.1 - β.1) + (α.2 - β.2))
          (by have hl := cellJetFluxIndices_lower_order hβ; omega)
          (α.1 - β.1, α.2 - β.2) rfl (hγord β hβ) Y0)
      let R := fun Y => Fj α Y + cellMetricJetFlux (fun β => Gj β Y) (fun β => cj β Y) α
      have hRm (Y : P) : AEStronglyMeasurable (Function.uncurry (R Y))
          ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) :=
        (hdata α hα Y).2.2.2.2.2.add (hjm Y)
      have hRf (Y : P) : cellUlNorm univ (R Y) < ⊤ :=
        (cellUlNorm_add univ (Fj α Y) _ (hdata α hα Y).2.2.2.2.2 (hjm Y)).trans_lt
          (ENNReal.add_lt_top.mpr ⟨(hdata α hα Y).2.2.2.1, hjf Y⟩)
      have hRc : Tendsto (fun Y => cellUlNorm univ (R Y - R Y0)) (𝓝 Y0) (𝓝 0) :=
        cellUlNorm_add_tendsto (𝓝 Y0) (Fj α)
          (fun Y => cellMetricJetFlux (fun β => Gj β Y) (fun β => cj β Y) α)
          (Fj α Y0) (cellMetricJetFlux (fun β => Gj β Y0) (fun β => cj β Y0) α)
          (fun Y => (hdata α hα Y).2.2.2.2.2) hjm
          (hdata α hα Y0).2.2.2.2.2 (hjm Y0) (hFc α hα Y0) hjc
      exact cellInverse_norm_continuous (Gj 0) (fj α) R (cj α) hv hG0
        (fun Y => ⟨(hdata α hα Y).2.2.2.2.1, (hdata α hα Y).2.2.1⟩)
        (fun Y => ⟨hRm Y, hRf Y⟩) (fun Y => hsol Y α hα) Y0
        (hGc 0 (by change 0 + 0 ≤ K; omega) Y0) (hfc α hα Y0) hRc
  intro α hα
  exact hall (α.1 + α.2) α rfl hα

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Genuine inverse construction of each triangular fibre Taylor coefficient. -/

/-- Scalar coefficient forcing is admissible for every family of actual lower inverse states. -/
theorem fibreCoefficientSource_admissible (η Cw : ℝ) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    {C : CellCoefficients} (A : ℕ × ℕ → CellInverseDatum C) (p : ℕ × ℕ) :
    cellUlNorm univ (fibreCoefficientSource η v (fun a => (A a).raw) p) < ⊤ ∧
    AEStronglyMeasurable (Function.uncurry (fibreCoefficientSource η v (fun a => (A a).raw) p))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) := by
  have hl := fibreCoefficientLinearSource_admissible η Cw hv hw A p
  have hq := fibreCoefficientQuadraticSource_admissible η Cw hv hw A p
  refine ⟨?_, hl.2.add hq.2⟩
  exact (cellUlNorm_add univ _ _ hl.2 hq.2).trans_lt (ENNReal.add_lt_top.mpr ⟨hl.1, hq.1⟩)

/-- Certified actual lower trajectories determine an actual next Taylor coefficient by mean-zero inversion. -/
def fibreCoefficientInverseStep (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (A : ℕ × ℕ → CellInverseDatum ⟨fun t _ => G t, v, 0, 0⟩) (p : ℕ × ℕ) :
    CellInverseDatum ⟨fun t _ => G t, v, 0, 0⟩ :=
  let hs := fibreCoefficientSource_admissible η Cw hv hw A p
  let hm : Measurable G := hG.1.comp
    (measurable_id.prodMk (measurable_const (a := (0 : Vec 2))))
  let hF := fibreCoefficientFlux_admissible η hη G hm
    (fun t i j => cellMetric_entry_bound hG t 0 i j) A p
  cellInverseDatum_of_forcing hG hv
    (fibreCoefficientSource η v (fun a => (A a).raw) p)
    (fibreCoefficientFlux η G (fun a => (A a).raw) p) hs.2 hF.2 hs.1 hF.1

/-- The certified next coefficient solves its actual literal triangular equation. -/
theorem fibreCoefficientInverseStep_isInverse (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (A : ℕ × ℕ → CellInverseDatum ⟨fun t _ => G t, v, 0, 0⟩) (p : ℕ × ℕ) :
    IsCellInverseValue ⟨fun t _ => G t, v, 0, 0⟩
      (fun t => cellQ0 (fibreCoefficientSource η v (fun a => (A a).raw) p t))
      (fibreCoefficientFlux η G (fun a => (A a).raw) p)
      (fibreCoefficientInverseStep η Cw hη G hG hv hw A p).raw :=
  (fibreCoefficientInverseStep η Cw hη G hG hv hw A p).isInverse

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.CycleEvolution

/-! Identifying a norm derivative with an already constructed solution of its differentiated equation. -/

/-- Actual inverse uniqueness identifies the derivative without choosing a new jet representative. -/
theorem cellInverse_directional_derivative_identified
    (G : ℝ → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (f : ℝ → ℝ → Vec 2 → ℂ)
    (F : ℝ → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D : ℝ → ℝ → RawJet2 1 ℂ)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hG : ∀ h, IsCellMetric (G h))
    (hf : ∀ h, cellUlNorm univ (f h) < ⊤ ∧
      AEStronglyMeasurable (Function.uncurry (f h))
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hF : ∀ h, cellUlNorm univ (F h) < ⊤ ∧
      AEStronglyMeasurable (Function.uncurry (F h))
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hD : ∀ h, IsCellInverseValue ⟨G h, v, 0, 0⟩ (fun t => cellQ0 (f h t)) (F h) (D h))
    (A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (f1 : ℝ → Vec 2 → ℂ) (F1 : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hA : cellMetricSupNorm A < ⊤ ∧ Measurable (Function.uncurry A))
    (hf1 : cellUlNorm univ f1 < ⊤ ∧ AEStronglyMeasurable (Function.uncurry f1)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hF1 : cellUlNorm univ F1 < ⊤ ∧ AEStronglyMeasurable (Function.uncurry F1)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hGc : Tendsto (fun h : ℝ => cellMetricSupNorm (h⁻¹ • (G h - G 0) - A)) (𝓝[≠] 0) (𝓝 0))
    (hfc : Tendsto (fun h : ℝ => cellUlNorm univ (h⁻¹ • (f h - f 0) - f1)) (𝓝[≠] 0) (𝓝 0))
    (hFc : Tendsto (fun h : ℝ => cellUlNorm univ (h⁻¹ • (F h - F 0) - F1)) (𝓝[≠] 0) (𝓝 0))
    (hDc : Tendsto (fun h : ℝ => cellEnergyNorm univ (D h - D 0)) (𝓝[≠] 0) (𝓝 0))
    (T : ℝ → RawJet2 1 ℂ)
    (hT : IsCellInverseValue ⟨G 0, v, 0, 0⟩ (fun t => cellQ0 (f1 t))
      (F1 + cellMetricFlux A (D 0)) T) :
    Tendsto (fun h : ℝ => cellEnergyNorm univ (h⁻¹ • (D h - D 0) - T))
      (𝓝[≠] 0) (𝓝 0) := by
  obtain ⟨D1, hD1, hd⟩ := cellInverse_directional_derivative_of_continuity
    G f F D hv hG hf hF hD A f1 F1 hA hf1 hF1 hGc hfc hFc hDc
  have he := cellInverse_unique_energy (hG 0) hv (fun t => cellQ0 (f1 t))
    (F1 + cellMetricFlux A (D 0)) T D1 hT hD1
  exact cellEnergyNorm_transfer_tendsto (𝓝[≠] (0 : ℝ))
    (fun h : ℝ => h⁻¹ • (D h - D 0)) D1 T
    (fun h a => (((hD h).1.2.2.2.1 a).sub ((hD 0).1.2.2.2.1 a)).const_smul h⁻¹)
    hD1.1.2.2.2.1 hT.1.2.2.2.1 he hd

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Coherent actual finite-order fibre coefficient stages. -/

/-- Actual inverse coefficients are constructed degree by degree, retaining every lower datum literally. -/
def fibreCoefficientStage (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) :
    ℕ → (ℕ × ℕ → CellInverseDatum ⟨fun t _ => G t, v, 0, 0⟩)
  | 0 => fun _ => cellInverseZeroDatum hG hv
  | n + 1 => fun p =>
      if p.1 + p.2 = n + 1 then
        fibreCoefficientInverseStep η Cw hη G hG hv hw
          (fibreCoefficientStage η Cw hη G hG hv hw n) p
      else fibreCoefficientStage η Cw hη G hG hv hw n p

/-- Every constructed datum of lower degree is preserved exactly by the next stage. -/
theorem fibreCoefficientStage_succ_lower (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (n : ℕ) (p : ℕ × ℕ) (hp : p.1 + p.2 ≤ n) :
    fibreCoefficientStage η Cw hη G hG hv hw (n + 1) p =
      fibreCoefficientStage η Cw hη G hG hv hw n p := by
  simp only [fibreCoefficientStage, ite_eq_right (by omega : p.1 + p.2 ≠ n + 1)]

/-- Later stages preserve every already constructed coefficient and its forcing certificate. -/
theorem fibreCoefficientStage_stable (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    {n m : ℕ} (hn : n ≤ m) (p : ℕ × ℕ) (hp : p.1 + p.2 ≤ n) :
    fibreCoefficientStage η Cw hη G hG hv hw m p =
      fibreCoefficientStage η Cw hη G hG hv hw n p := by
  induction m, hn using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    rw [fibreCoefficientStage_succ_lower η Cw hη G hG hv hw m p (hp.trans hm)]
    exact ih

end AVRegularity.CycleEvolution
end
