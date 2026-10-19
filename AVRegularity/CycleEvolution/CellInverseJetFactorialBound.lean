-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.CellInverseJetEquationExistence
import AVRegularity.CycleEvolution.CellEnergySpaceRawJetCauchyBound
import AVRegularity.CycleEvolution.CellLimitMoments

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Actual construction of every finite triangular family of cell inverse jets. -/

/-- All finite-order jet equations can be solved successively from their strictly lower-order forcing. -/
theorem cellInverse_finiteJetFamily_exists (K : ℕ)
    (Gj : ℕ × ℕ → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (fj : ℕ × ℕ → ℝ → Vec 2 → ℂ)
    (Fj : ℕ × ℕ → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hG0 : IsCellMetric (Gj 0))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hdata : ∀ α : ℕ × ℕ, α.1 + α.2 ≤ K →
      cellMetricSupNorm (Gj α) < ⊤ ∧ Measurable (Function.uncurry (Gj α)) ∧
      cellUlNorm univ (fj α) < ⊤ ∧ cellUlNorm univ (Fj α) < ⊤ ∧
      AEStronglyMeasurable (Function.uncurry (fj α))
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) ∧
      AEStronglyMeasurable (Function.uncurry (Fj α))
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube))) :
    ∃ cj : ℕ × ℕ → ℝ → RawJet2 1 ℂ,
      ∀ α : ℕ × ℕ, α.1 + α.2 ≤ K →
        IsCellInverseValue ⟨Gj 0, v, 0, 0⟩ (fun t => cellQ0 (fj α t))
          (Fj α + cellMetricJetFlux Gj cj α) (cj α) := by
  classical
  revert hdata
  induction K with
  | zero =>
    intro hdata
    have hd := hdata 0 (by change 0 + 0 ≤ 0; omega)
    obtain ⟨D, hD, _⟩ := cellAllTimeInverse_exists_bound_ae hG0 hv (fj 0) (Fj 0)
      hd.2.2.2.2.1 hd.2.2.2.2.2 hd.2.2.1 hd.2.2.2.1
    let cj := fun α : ℕ × ℕ => if α = 0 then D else 0
    refine ⟨cj, ?_⟩
    intro α hα
    have hα0 : α = 0 := Prod.ext (by change α.1 = 0; omega) (by change α.2 = 0; omega)
    subst α
    rw [cellMetricJetFlux_zero, add_zero]
    simpa only [cj, ite_eq_left rfl] using hD
  | succ n ih =>
    intro hdata
    obtain ⟨old, hold⟩ := ih (fun α hα => hdata α (hα.trans (Nat.le_succ n)))
    have hex (α : ℕ × ℕ) (hα : α.1 + α.2 = n + 1) :
        ∃ E : ℝ → RawJet2 1 ℂ,
          IsCellInverseValue ⟨Gj 0, v, 0, 0⟩ (fun t => cellQ0 (fj α t))
            (Fj α + cellMetricJetFlux Gj old α) E := by
      have hd := hdata α (by omega)
      apply cellInverse_jetEquation_exists Gj old α hG0 hv (fj α) (Fj α)
        hd.2.2.2.2.1 hd.2.2.2.2.2 hd.2.2.1 hd.2.2.2.1
      · intro β hβ
        exact (hdata β ((cellJetFluxIndices_metric_order hβ).trans (by omega))).1
      · intro β hβ
        exact (hdata β ((cellJetFluxIndices_metric_order hβ).trans (by omega))).2.1
      · intro β hβ
        have hl := cellJetFluxIndices_lower_order hβ
        exact (hold (α.1 - β.1, α.2 - β.2) (by omega)).2.2
      · intro β hβ
        have hl := cellJetFluxIndices_lower_order hβ
        exact (hold (α.1 - β.1, α.2 - β.2) (by omega)).1.2.2.2.1
    let cj := fun α : ℕ × ℕ => if hα : α.1 + α.2 = n + 1 then (hex α hα).choose else old α
    refine ⟨cj, ?_⟩
    intro α hα
    have hf : cellMetricJetFlux Gj cj α = cellMetricJetFlux Gj old α := by
      apply cellMetricJetFlux_congr_lower
      intro γ hγ
      have hn : γ.1 + γ.2 ≠ n + 1 := by omega
      simp only [cj, dite_eq_right hn]
    rw [hf]
    by_cases hn : α.1 + α.2 = n + 1
    · simp only [cj, dite_eq_left hn]
      exact (hex α hn).choose_spec
    · simp only [cj, dite_eq_right hn]
      exact hold α (by omega)

/-! Parameterwise construction of actual finite cell inverse jet families. -/

/-- Pointwise triangular inversion constructs one family solving every prescribed finite jet equation. -/
theorem cellInverse_parameterJetFamily_exists {P : Type*} (K : ℕ)
    (Gj : ℕ × ℕ → P → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (fj : ℕ × ℕ → P → ℝ → Vec 2 → ℂ)
    (Fj : ℕ × ℕ → P → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hG0 : ∀ Y, IsCellMetric (Gj 0 Y))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hdata : ∀ α : ℕ × ℕ, α.1 + α.2 ≤ K → ∀ Y,
      cellMetricSupNorm (Gj α Y) < ⊤ ∧ Measurable (Function.uncurry (Gj α Y)) ∧
      cellUlNorm univ (fj α Y) < ⊤ ∧ cellUlNorm univ (Fj α Y) < ⊤ ∧
      AEStronglyMeasurable (Function.uncurry (fj α Y))
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) ∧
      AEStronglyMeasurable (Function.uncurry (Fj α Y))
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube))) :
    ∃ cj : ℕ × ℕ → P → ℝ → RawJet2 1 ℂ,
      ∀ Y, ∀ α : ℕ × ℕ, α.1 + α.2 ≤ K →
        IsCellInverseValue ⟨Gj 0 Y, v, 0, 0⟩ (fun t => cellQ0 (fj α Y t))
          (Fj α Y + cellMetricJetFlux (fun β => Gj β Y) (fun β => cj β Y) α) (cj α Y) := by
  have hex (Y : P) := cellInverse_finiteJetFamily_exists K
    (fun α => Gj α Y) (fun α => fj α Y) (fun α => Fj α Y) (hG0 Y) hv
    (fun α hα => hdata α hα Y)
  choose c hc using hex
  exact ⟨fun α Y => c Y α, hc⟩

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! The actual scalar graph forcing is measurable and obeys its quadratic energy estimate. -/

/-- For an actual bounded mean-zero cell inverse, the scalar graph source has a quadratic energy bound. -/
theorem fibreGraphSource_ul_bound (η Cw : ℝ) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ)
    {C : CellCoefficients} {src : ℝ → Vec 2 → ℂ}
    {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {D : ℝ → RawJet2 1 ℂ}
    (hD : IsCellInverseValue C src F D) :
    cellUlNorm univ (fibreGraphSource η v ξ (cellValue D)) ≤
      2 * (ENNReal.ofReal (Cw * fibreNorm ξ) * (1 + cellEnergyNorm univ D)) +
        ENNReal.ofReal (Cw * fibreNorm ξ) * cellEnergyNorm univ D * cellEnergyNorm univ D ∧
    AEStronglyMeasurable (Function.uncurry (fibreGraphSource η v ξ (cellValue D)))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) := by
  let b := fibreDriftCoupling η v ξ
  have hb := fibreDriftCoupling_measurable η hv ξ
  have hB := fibreDriftCoupling_norm_le η Cw v hw ξ
  have hz : Measurable (Function.uncurry (fun t x => -Complex.I * b t x)) := hb.const_mul _
  have hZ (t : ℝ) (x : Vec 2) : ‖-Complex.I * b t x‖ ≤ Cw * fibreNorm ξ := by
    simpa only [norm_mul, norm_neg, Complex.norm_I, one_mul] using hB t x
  have hp := cellProjectedAffineMultiplier_ul_bound (fun t x => -Complex.I * b t x)
    (Cw * fibreNorm ξ) hz hZ hD
  have hq := cellMeanMultiplier_ul_bound b (Cw * fibreNorm ξ) hb hB hD hD
  let p : ℝ → Vec 2 → ℂ := fun t => cellQ0 (fun x => (-Complex.I * b t x) * (1 + cellValue D t x))
  let q : ℝ → Vec 2 → ℂ := fun t x => cellValue D t x * cellMean (fun y => b t y * cellValue D t y)
  have he : fibreGraphSource η v ξ (cellValue D) = p + Complex.I • q := by
    funext t x
    simp only [fibreGraphSource, p, q, b, fibreDriftCoupling, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    congr 1
    · congr 1
      funext y
      ring
    · ring
  have hqm : AEStronglyMeasurable (Function.uncurry (Complex.I • q))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) := by
    exact aestronglyMeasurable_const.mul hq.2
  rw [he]
  refine ⟨(cellUlNorm_add univ p (Complex.I • q) hp.2 hqm).trans ?_, hp.2.add hqm⟩
  apply add_le_add hp.1
  have h := cellUlNorm_complex_smul univ Complex.I q hq.2
  simpa only [show ‖Complex.I‖ₑ = 1 by simp [enorm_eq_nnnorm], one_mul] using h.trans
    (by simpa only [show ‖Complex.I‖ₑ = 1 by simp [enorm_eq_nnnorm], one_mul] using hq.1)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CycleEvolution

/-! Genuine conjugation and coefficient parity commute with the mean-free cell projection. -/

theorem cellMean_conjugate (f : Vec 2 → ℂ) :
    cellMean (fun x => star (f x)) = star (cellMean f) := cellIntegral_star _ _

theorem cellQ0_conjugate (f : Vec 2 → ℂ) :
    cellQ0 (fun x => star (f x)) = fun x => star (cellQ0 f x) := by
  funext x
  simp only [cellQ0, cellMean_conjugate, star_sub]

theorem cellQ0_parity_ae (σ : ℂ) (f : Vec 2 → ℂ)
    (hf : (fun x => star (f x)) =ᵐ[volume.restrict AVenhance.unitCube]
      (fun x => σ * f x)) :
    (fun x => star (cellQ0 f x)) =ᵐ[volume.restrict AVenhance.unitCube]
      (fun x => σ * cellQ0 f x) := by
  have h := cellQ0_congr_ae (fun x => star (f x)) (σ • f) hf
  rw [cellQ0_conjugate, cellQ0_complex_smul] at h
  exact h

end AVRegularity.CycleEvolution
end

section
open Homogenization
namespace AVRegularity.CycleEvolution

/-! The literal graph scalar source vanishes wherever the physical drift vanishes. -/

theorem fibreGraphSource_quiet (η : ℝ) (v : ℝ → Vec 2 → Vec 2) (ξ : Fin 2 → ℂ)
    (ρ : ℝ → Vec 2 → ℂ) (t : ℝ) (hv : ∀ x, v t x = 0) :
    fibreGraphSource η v ξ ρ t = 0 := by
  funext x
  simp only [fibreGraphSource, hv, Pi.zero_apply, Complex.ofReal_zero, zero_mul,
    Finset.sum_const_zero, mul_zero, cellQ0, cellMean, MeasureTheory.integral_zero,
    sub_zero, zero_add]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! The literal nonlinear graph forcing lies in L2 and has zero mean at every time. -/

local instance fibreGraphSourceL2ProbCube : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using cellCube_volume_one⟩

/-- Every actual graph forcing slice is L2 and mean-free, including the exceptional H1 times. -/
theorem fibreGraphSource_memLp_and_mean_zero (η Cw : ℝ) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ)
    {C : CellCoefficients} {src : ℝ → Vec 2 → ℂ}
    {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {D : ℝ → RawJet2 1 ℂ}
    (hD : IsCellInverseValue C src F D) (t : ℝ) :
    MemLp (fibreGraphSource η v ξ (cellValue D) t) 2
      (volume.restrict AVenhance.unitCube) ∧
    cellMean (fibreGraphSource η v ξ (cellValue D) t) = 0 := by
  let b := fibreDriftCoupling η v ξ
  let p : Vec 2 → ℂ := fun x => -Complex.I * (b t x * (1 + cellValue D t x))
  let m := cellMean (fun y => b t y * cellValue D t y)
  let q : Vec 2 → ℂ := fun x => Complex.I * cellValue D t x * m
  have hb := fibreDriftCoupling_measurable η hv ξ
  have hB := fibreDriftCoupling_norm_le η Cw v hw ξ
  have hp0 := cellAffineMultiplier_cellL2Norm_le (b t) (cellValue D t) (Cw * fibreNorm ξ)
    (hb.comp (measurable_const.prodMk measurable_id)) (hB t)
    (hD.1.2.2.1 t (mem_univ t)).1
  have hp1 : MemLp (fun x => b t x * (1 + cellValue D t x)) 2
      (volume.restrict AVenhance.unitCube) := hp0.trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.mpr
      ⟨by simp, (cellValue_cellL2Norm_le_energy D t).trans_lt hD.2.2⟩))
  have hp : MemLp p 2 (volume.restrict AVenhance.unitCube) := hp1.const_smul (-Complex.I)
  have heq : q = (Complex.I * m) • cellValue D t := by
    funext x
    simp only [q, Pi.smul_apply, smul_eq_mul]
    ring
  have hq : MemLp q 2 (volume.restrict AVenhance.unitCube) := by
    rw [heq]
    exact (hD.1.2.2.1 t (mem_univ t)).1.const_smul _
  have hs : fibreGraphSource η v ξ (cellValue D) t = cellQ0 p + q := rfl
  refine ⟨?_, ?_⟩
  · rw [hs]
    exact (cellQ0_memLp hp).add hq
  rw [hs]
  have ha : cellMean (cellQ0 p + q) = cellMean (cellQ0 p) + cellMean q :=
    integral_add ((cellQ0_memLp hp).integrable (by norm_num)) (hq.integrable (by norm_num))
  rw [ha, cellQ0_mean hp, heq, cellMean_complex_smul, hD.2.1 t, mul_zero, add_zero]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Exact projection of the nonlinear graph source on every time trace. -/

/-- Projection of the complete unprojected forcing equals the literal graph source for an actual mean-zero inverse. -/
theorem fibreGraphSource_projection (η Cw : ℝ) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ)
    {C : CellCoefficients} {src : ℝ → Vec 2 → ℂ}
    {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {D : ℝ → RawJet2 1 ℂ}
    (hD : IsCellInverseValue C src F D) (t : ℝ) :
    cellQ0 (fun x => -Complex.I * (fibreDriftCoupling η v ξ t x * (1 + cellValue D t x)) +
      Complex.I * cellValue D t x *
        cellMean (fun y => fibreDriftCoupling η v ξ t y * cellValue D t y)) =
      fibreGraphSource η v ξ (cellValue D) t := by
  let b := fibreDriftCoupling η v ξ
  let P := fun x => -Complex.I * (b t x * (1 + cellValue D t x))
  let m := cellMean (fun y => b t y * cellValue D t y)
  let Q := fun x => Complex.I * cellValue D t x * m
  have hb := fibreDriftCoupling_measurable η hv ξ
  have hB := fibreDriftCoupling_norm_le η Cw v hw ξ
  have hf := (hD.1.2.2.1 t (mem_univ t)).1
  have hp0 := cellAffineMultiplier_memLp (b t) (cellValue D t) (Cw * fibreNorm ξ)
    (hb.comp ((measurable_const (a := t)).prodMk measurable_id)) (hB t) hf
  have hp : MemLp P 2 (volume.restrict AVenhance.unitCube) := hp0.const_smul (-Complex.I)
  have heQ : Q = (Complex.I * m) • cellValue D t := by
    funext x
    simp only [Q, Pi.smul_apply, smul_eq_mul]
    ring
  have hq : MemLp Q 2 (volume.restrict AVenhance.unitCube) := by
    rw [heQ]
    exact hf.const_smul _
  have hm : cellMean Q = 0 := by
    rw [heQ, cellMean_complex_smul, hD.2.1 t, mul_zero]
  change cellQ0 (P + Q) = _
  rw [cellQ0_add P Q hp hq, cellQ0_eq_self_of_mean_zero Q hm]
  rfl

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Quantitative triangular recurrence for the actual cell inverse jet energy norms. -/

/-- Every actual jet solution obeys the binomial norm recurrence with one universal coefficient. -/
theorem cellInverse_jet_norm_recurrence
    (Gj : ℕ × ℕ → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (cj : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (α : ℕ × ℕ)
    (hG0 : IsCellMetric (Gj 0))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (f : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hfm : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hFm : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hf : cellUlNorm univ f < ⊤) (hF : cellUlNorm univ F < ⊤)
    (hG : ∀ β ∈ cellJetFluxIndices α, cellMetricSupNorm (Gj β) < ⊤)
    (hGm : ∀ β ∈ cellJetFluxIndices α, Measurable (Function.uncurry (Gj β)))
    (hc : ∀ β ∈ cellJetFluxIndices α,
      cellEnergyNorm univ (cj (α.1 - β.1, α.2 - β.2)) < ⊤)
    (hcm : ∀ β ∈ cellJetFluxIndices α, ∀ a,
      AEStronglyMeasurable (fun p : ℝ × Vec 2 => cj (α.1 - β.1, α.2 - β.2) p.1 a p.2)
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hsol : IsCellInverseValue ⟨Gj 0, v, 0, 0⟩ (fun t => cellQ0 (f t))
      (F + cellMetricJetFlux Gj cj α) (cj α)) :
    cellEnergyNorm univ (cj α) ≤ ENNReal.ofReal 100 *
      (cellUlNorm univ f + cellUlNorm univ F +
        ∑ β ∈ cellJetFluxIndices α, (cellJetChoose α β : ℝ≥0∞) *
          cellMetricSupNorm (Gj β) * cellEnergyNorm univ (cj (α.1 - β.1, α.2 - β.2))) := by
  have hJm := cellMetricJetFlux_aestronglyMeasurable Gj cj α hGm hcm
  have hJf := cellMetricJetFlux_ul_lt_top Gj cj α hG hGm hc hcm
  have hFs := cellUlNorm_add univ F (cellMetricJetFlux Gj cj α) hFm hJm
  have hb := cellAllTimeInverse_bound_ae hG0 hv f (F + cellMetricJetFlux Gj cj α)
    hfm (hFm.add hJm) hf (hFs.trans_lt (ENNReal.add_lt_top.mpr ⟨hF, hJf⟩)) (cj α) hsol
  have hJb := cellMetricJetFlux_ul_bound Gj cj α hG hGm hcm
  have hFs' := hFs.trans (add_le_add le_rfl hJb)
  have hsum : (∑ β ∈ cellJetFluxIndices α, (cellJetChoose α β : ℝ≥0∞) *
      (2 * cellMetricSupNorm (Gj β) * cellEnergyNorm univ (cj (α.1 - β.1, α.2 - β.2)))) =
      2 * ∑ β ∈ cellJetFluxIndices α, (cellJetChoose α β : ℝ≥0∞) *
        cellMetricSupNorm (Gj β) * cellEnergyNorm univ (cj (α.1 - β.1, α.2 - β.2)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro β _
    ring
  rw [hsum] at hFs'
  have hfirst : cellEnergyNorm univ (cj α) ≤ ENNReal.ofReal 13 *
      (cellUlNorm univ f + cellUlNorm univ F + 2 *
        ∑ β ∈ cellJetFluxIndices α, (cellJetChoose α β : ℝ≥0∞) *
          cellMetricSupNorm (Gj β) * cellEnergyNorm univ (cj (α.1 - β.1, α.2 - β.2))) := by
    refine hb.trans ?_
    rw [add_assoc]
    gcongr
  refine hfirst.trans ?_
  norm_num only [ENNReal.ofReal_ofNat]
  rw [mul_add, mul_add, mul_add, mul_add]
  rw [show (13 : ℝ≥0∞) * (2 * _) = 26 * _ by ring]
  gcongr <;> norm_num

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Exact nonlinear graph-source differences for actual bounded cell trajectories. -/

/-- The graph source difference is a projected linear term and two genuine quadratic difference terms. -/
theorem fibreGraphSource_difference (η Cw : ℝ) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ)
    {C C' : CellCoefficients} {src src' : ℝ → Vec 2 → ℂ}
    {F F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    {D E : ℝ → RawJet2 1 ℂ}
    (hD : IsCellInverseValue C src F D) (hE : IsCellInverseValue C' src' F' E) :
    fibreGraphSource η v ξ (cellValue D) - fibreGraphSource η v ξ (cellValue E) =
      fun t x =>
        cellQ0 (fun y => -Complex.I * fibreDriftCoupling η v ξ t y *
          cellValue (D - E) t y) x +
        Complex.I * cellValue (D - E) t x *
          cellMean (fun y => fibreDriftCoupling η v ξ t y * cellValue D t y) +
        Complex.I * cellValue E t x *
          cellMean (fun y => fibreDriftCoupling η v ξ t y * cellValue (D - E) t y) := by
  let b := fibreDriftCoupling η v ξ
  have hb := fibreDriftCoupling_measurable η hv ξ
  have hB := fibreDriftCoupling_norm_le η Cw v hw ξ
  funext t x
  have hbt : Measurable (b t) := hb.comp (measurable_const.prodMk measurable_id)
  have hd := (hD.1.2.2.1 t (mem_univ t)).1
  have he := (hE.1.2.2.1 t (mem_univ t)).1
  have hbf := cellMultiplier_memLp (b t) (cellValue D t) (Cw * fibreNorm ξ) hbt (hB t) hd
  have hbg := cellMultiplier_memLp (b t) (cellValue E t) (Cw * fibreNorm ξ) hbt (hB t) he
  have hz : Measurable (fun y => -Complex.I * b t y) := hbt.const_mul _
  have hZ (y : Vec 2) : ‖-Complex.I * b t y‖ ≤ Cw * fibreNorm ξ := by
    simpa only [norm_mul, norm_neg, Complex.norm_I, one_mul] using hB t y
  have hfd := cellAffineMultiplier_memLp (fun y => -Complex.I * b t y)
    (cellValue D t) (Cw * fibreNorm ξ) hz hZ hd
  have hfe := cellAffineMultiplier_memLp (fun y => -Complex.I * b t y)
    (cellValue E t) (Cw * fibreNorm ξ) hz hZ he
  have hp := cellProjectedAffine_difference (b t) (cellValue D t) (cellValue E t) hfd hfe x
  have hq := cellGraphQuadratic_difference (b t) (cellValue D t) (cellValue E t) hbf hbg x
  have ha (f : Vec 2 → ℂ) :
      (fun y => -Complex.I * (b t y * (1 + f y))) =
        (fun y => -Complex.I * b t y * (1 + f y)) := by
    funext y
    ring
  change (cellQ0 (fun y => -Complex.I * (b t y * (1 + cellValue D t y))) x +
      Complex.I * cellValue D t x * cellMean (fun y => b t y * cellValue D t y)) -
    (cellQ0 (fun y => -Complex.I * (b t y * (1 + cellValue E t y))) x +
      Complex.I * cellValue E t x * cellMean (fun y => b t y * cellValue E t y)) = _
  rw [ha, ha]
  calc
    _ =
      (cellQ0 (fun y => -Complex.I * b t y * (1 + cellValue D t y)) x -
        cellQ0 (fun y => -Complex.I * b t y * (1 + cellValue E t y)) x) +
      (Complex.I * cellValue D t x * cellMean (fun y => b t y * cellValue D t y) -
        Complex.I * cellValue E t x * cellMean (fun y => b t y * cellValue E t y)) := by ring
    _ = _ := by
      rw [hp, hq]
      simp only [cellValue, Pi.sub_apply]
      dsimp only [b]
      ring

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization
open scoped BigOperators
namespace AVRegularity.CycleEvolution

/-! Exact coordinate expansion of the actual drift multiplier mean. -/

local instance cycleEvolutionFibreCouplingMeanCoordinatesProbCube : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using cellCube_volume_one⟩

/-- The finite coordinate pairing recovers the literal arbitrary-frequency mean. -/
theorem fibreDriftCoupling_mean_coordinates (η Cw : ℝ) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (t : ℝ) (f : Vec 2 → ℂ)
    (hf : MemLp f 2 (volume.restrict AVenhance.unitCube)) :
    (∑ j : Fin 2, ξ j * cellMean (fun x =>
      fibreDriftCoupling η v (fibreCoordinateFrequency j) t x * f x)) =
      cellMean (fun x => fibreDriftCoupling η v ξ t x * f x) := by
  let b := fun j => fibreDriftCoupling η v (fibreCoordinateFrequency j) t
  have hb j : Measurable (b j) := (fibreDriftCoupling_measurable η hv
    (fibreCoordinateFrequency j)).comp ((measurable_const (a := t)).prodMk measurable_id)
  have hB j x : ‖b j x‖ ≤ Cw := by
    simpa only [fibreCoordinateFrequency_norm, mul_one] using
      fibreDriftCoupling_norm_le η Cw v hw (fibreCoordinateFrequency j) t x
  have hm j : Integrable (fun x => ξ j * (b j x * f x))
      (volume.restrict AVenhance.unitCube) :=
    ((cellMultiplier_memLp (b j) f Cw (hb j) (hB j) hf).const_smul (ξ j)).integrable (by norm_num)
  have he : (fun x => fibreDriftCoupling η v ξ t x * f x) =
      (fun x => ∑ j : Fin 2, ξ j * (b j x * f x)) := by
    funext x
    rw [← fibreDriftCoupling_coordinates η v ξ t x, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [b]
    ring
  rw [he]
  change _ = ∫ x, ∑ j : Fin 2, ξ j * (b j x * f x) ∂(volume.restrict AVenhance.unitCube)
  rw [integral_finsetSum _ (fun j _ => hm j)]
  apply Finset.sum_congr rfl
  intro j _
  exact (integral_const_mul (ξ j) (fun x => b j x * f x)).symm

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The scalar graph symbol depends Lipschitz continuously on the actual energy trace. -/

section
local instance fibreDriftMeanDifferenceProbCube : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using cellCube_volume_one⟩

theorem fibreDrift_mean_difference_norm_le (η Cw : ℝ) (hCw : 0 ≤ Cw)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) {C C' : CellCoefficients} {src src' : ℝ → Vec 2 → ℂ}
    {F F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    {D E : ℝ → RawJet2 1 ℂ}
    (hD : IsCellInverseValue C src F D) (hE : IsCellInverseValue C' src' F' E)
    (L : ℝ) (hL : 0 ≤ L) (hn : cellEnergyNorm univ (D - E) ≤ ENNReal.ofReal L) (t : ℝ) :
    ‖cellMean (fun x => fibreDriftCoupling η v ξ t x * cellValue D t x) -
      cellMean (fun x => fibreDriftCoupling η v ξ t x * cellValue E t x)‖ ≤
      Cw * fibreNorm ξ * L := by
  have hξ0 := fibreNorm_nonneg ξ
  let b := fibreDriftCoupling η v ξ t
  have hb : Measurable b := (fibreDriftCoupling_measurable η hv ξ).comp
    (measurable_const.prodMk measurable_id)
  have hB := fibreDriftCoupling_norm_le η Cw v hw ξ t
  have hd := (hD.1.2.2.1 t (mem_univ t)).1
  have he := (hE.1.2.2.1 t (mem_univ t)).1
  have hbd := cellMultiplier_memLp b (cellValue D t) (Cw * fibreNorm ξ) hb hB hd
  have hbe := cellMultiplier_memLp b (cellValue E t) (Cw * fibreNorm ξ) hb hB he
  have hm := cellMultiplier_memLp b (cellValue (D - E) t) (Cw * fibreNorm ξ) hb hB (hd.sub he)
  have hmAES := hb.aestronglyMeasurable.mul (hd.sub he).aestronglyMeasurable
  have hi : cellMean (fun x => b x * cellValue D t x) -
      cellMean (fun x => b x * cellValue E t x) =
      cellMean (fun x => b x * cellValue (D - E) t x) := by
    unfold cellMean
    rw [← integral_sub (hbd.integrable (by norm_num)) (hbe.integrable (by norm_num))]
    congr 1
    funext x
    simp only [cellValue, Pi.sub_apply]
    ring
  change ‖cellMean (fun x => b x * cellValue D t x) -
      cellMean (fun x => b x * cellValue E t x)‖ ≤ _
  rw [hi]
  have hnmean := (cellMean_enorm_le_cellL2Norm _ hm).trans
    ((cellL2Norm_mul_le b (cellValue (D - E) t) (Cw * fibreNorm ξ) hmAES
      (Filter.Eventually.of_forall hB)).trans
      (mul_le_mul' le_rfl ((cellValue_cellL2Norm_le_energy (D - E) t).trans hn)))
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (by positivity)] at hnmean
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hnmean
end

/-! The cell resolvent identity and its quantitative coefficient-continuity bound. -/

/-- With identical forcing, the difference of cell inverses is the inverse metric flux. -/
theorem cellInverse_resolvent
    {G H : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : IsCellMetric G) (hH : IsCellMetric H)
    (v : ℝ → Vec 2 → Vec 2) (src : ℝ → Vec 2 → ℂ)
    (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D E : ℝ → RawJet2 1 ℂ)
    (hD : IsCellInverseValue ⟨G, v, 0, 0⟩ src F D)
    (hE : IsCellInverseValue ⟨H, v, 0, 0⟩ src F E) :
    IsCellInverseValue ⟨G, v, 0, 0⟩ 0 (cellMetricFlux (H - G) E) (E - D) := by
  have hc := cellInverse_add
    (cellInverse_metric_change G H v src F E hG.2.2.1 hH.2.2.1 hE)
    (cellInverse_smul hD (-1))
  rw [neg_one_smul, neg_one_smul, neg_one_smul, add_neg_cancel,
    ← sub_eq_add_neg] at hc
  have he : (F + cellMetricFlux (H - G) E) - F = cellMetricFlux (H - G) E := by abel
  rw [he] at hc
  simpa only [sub_eq_add_neg] using hc

/-- The resolvent is continuous in the uniform metric norm with a universal energy constant. -/
theorem cellInverse_resolvent_bound
    {G H : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : IsCellMetric G) (hH : IsCellMetric H)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D E : ℝ → RawJet2 1 ℂ)
    (hD : IsCellInverseValue ⟨G, v, 0, 0⟩ src F D)
    (hE : IsCellInverseValue ⟨H, v, 0, 0⟩ src F E)
    (hd : cellMetricSupNorm (H - G) < ⊤) :
    cellEnergyNorm univ (E - D) ≤
      ENNReal.ofReal 26 * cellMetricSupNorm (H - G) * cellEnergyNorm univ E := by
  have hdm : Measurable (Function.uncurry (H - G)) :=
    Measurable.of_eval (fun i => Measurable.of_eval (fun j =>
      (cellMetric_entry_measurable hH i j).sub (cellMetric_entry_measurable hG i j)))
  have hflux := cellMetricFlux_ul_bound univ (H - G) hd hdm E hE.1.2.2.2.1
  have hfinite : cellUlNorm univ (cellMetricFlux (H - G) E) < ⊤ :=
    hflux.trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) hd) hE.2.2)
  have hzero : (fun t => cellQ0 ((0 : ℝ → Vec 2 → ℂ) t)) = 0 := by
    funext t x
    simp only [cellQ0, Pi.zero_apply, cellMean, integral_zero, sub_zero]
  have hr := cellInverse_resolvent hG hH v src F D E hD hE
  rw [← hzero] at hr
  have hb := cellAllTimeInverse_bound_ae hG hv 0 (cellMetricFlux (H - G) E)
    aestronglyMeasurable_zero
    (cellMetricFlux_aestronglyMeasurable univ (H - G) E hdm hE.1.2.2.2.1)
    (by simp [cellUlNorm, cellL2Norm]) hfinite (E - D) hr
  have hzeroUl : cellUlNorm univ (0 : ℝ → Vec 2 → ℂ) = 0 := by
    simp [cellUlNorm, cellL2Norm]
  rw [hzeroUl, zero_add] at hb
  calc
    _ ≤ ENNReal.ofReal 13 * (2 * cellMetricSupNorm (H - G) * cellEnergyNorm univ E) := by
      exact hb.trans (by gcongr)
    _ = _ := by norm_num; ring

/-! The genuine graph forcing is in product L² on every finite time interval. -/

theorem fibreGraphSource_interval_memLp (η Cw : ℝ) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) {C : CellCoefficients} {src : ℝ → Vec 2 → ℂ}
    {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {D : ℝ → RawJet2 1 ℂ}
    (hD : IsCellInverseValue C src F D) (a b : ℝ) :
    MemLp (Function.uncurry (fibreGraphSource η v ξ (cellValue D))) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)) := by
  have hs := fibreGraphSource_ul_bound η Cw hv hw ξ hD
  have hn := hD.2.2
  exact cellUl_memLp_product_interval_ae univ _ hs.2
    (hs.1.trans_lt (by finiteness)) a b (Set.subset_univ _)

theorem fibreGraphFlux_interval_memLp (η : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hGm : Measurable G)
    (hG : ∀ t i j, |G t i j| ≤ 2) (ξ : Fin 2 → ℂ)
    {C : CellCoefficients} {src : ℝ → Vec 2 → ℂ}
    {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {D : ℝ → RawJet2 1 ℂ}
    (hD : IsCellInverseValue C src F D) (a b : ℝ) :
    MemLp (Function.uncurry (fibreGraphFlux η G ξ (cellValue D))) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)) := by
  have hs := fibreGraphFlux_ul_bound η hη G hGm hG ξ hD.1
  have hn := hD.2.2
  exact cellUl_memLp_product_interval_ae univ _ hs.2
    (hs.1.trans_lt (by finiteness)) a b (Set.subset_univ _)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Actual weak Bloch evolution agrees with the local analytic perturbation inverse. -/

theorem cellBlochEvolution_inverse_formula {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (hκ : AEStronglyMeasurable C.κ (volume.restrict (Icc a b)))
    (hκb : ∀ t, ‖C.κ t‖ ≤ k)
    (δ : Fin 2 → ℂ) (q : Lp ℂ ∞ (volume.restrict (Icc a b)))
    (d : CellFiniteEnergyDatum a b) (z : CellEnergySpace a b) :
    let sol := cellFiniteEnergyEvolutionCLM hab C hG V k hv hb hκ hκb
    let T := cellBlochPolynomialEvolutionOperator hab C hG V hv hb sol δ q
    IsUnit (1 - T) →
    IsCellFiniteEnergyEvolution
      { C with θ := C.θ + δ, κ := fun t => C.κ t + q t } hG V hv hb d z →
    z = cellEnergyOperatorApplyCLM a b (Ring.inverse (1 - T))
      (sol (cellBlochExternalDatum δ d)) := by
  dsimp only
  intro hT hz
  apply cellEnergyOperator_inverse_fixedPoint _ hT
  rw [cellBlochPolynomialEvolutionOperator_apply]
  exact cellBlochEvolution_fixedPoint hab C hG V k hv hb hκ hκb δ q d z hz

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The exact parameter-difference equation for cell inverse families. -/

/-- Differences of bounded inverses solve the difference-forcing equation. -/
theorem cellInverse_sub {C : CellCoefficients}
    {src src' : ℝ → Vec 2 → ℂ}
    {F F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    {D E : ℝ → RawJet2 1 ℂ}
    (hD : IsCellInverseValue C src F D) (hE : IsCellInverseValue C src' F' E) :
    IsCellInverseValue C (src' - src) (F' - F) (E - D) := by
  simpa only [neg_one_smul, sub_eq_add_neg] using
    cellInverse_add hE (cellInverse_smul hD (-1))

/-- The actual inverse difference equation includes the metric perturbation flux. -/
theorem cellInverse_parameter_difference
    {G H : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : IsCellMetric G) (hH : IsCellMetric H)
    (v : ℝ → Vec 2 → Vec 2) (f g : ℝ → Vec 2 → ℂ)
    (F F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D E : ℝ → RawJet2 1 ℂ)
    (hfm : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hgm : AEStronglyMeasurable (Function.uncurry g)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hf : cellUlNorm univ f < ⊤) (hg : cellUlNorm univ g < ⊤)
    (hD : IsCellInverseValue ⟨G, v, 0, 0⟩ (fun t => cellQ0 (f t)) F D)
    (hE : IsCellInverseValue ⟨H, v, 0, 0⟩ (fun t => cellQ0 (g t)) F' E) :
    IsCellInverseValue ⟨G, v, 0, 0⟩ (fun t => cellQ0 ((g - f) t))
      ((F' - F) + cellMetricFlux (H - G) E) (E - D) := by
  have hr := cellInverse_sub hD
    (cellInverse_metric_change G H v (fun t => cellQ0 (g t)) F' E
      hG.2.2.1 hH.2.2.1 hE)
  have heF : F' + cellMetricFlux (H - G) E - F =
      (F' - F) + cellMetricFlux (H - G) E := by abel
  rw [heF] at hr
  have hs : ∀ᵐ t ∂volume.restrict univ,
      ((fun r => cellQ0 (g r)) - (fun r => cellQ0 (f r))) t =ᵐ[
        volume.restrict AVenhance.unitCube] cellQ0 ((g - f) t) := by
    have hmF := cellUl_memLp_slices_ae f hfm hf
    have hmG := cellUl_memLp_slices_ae g hgm hg
    simp only [Measure.restrict_univ]
    filter_upwards [hmF, hmG] with t hft hgt
    exact Filter.EventuallyEq.of_eq (cellQ0_sub (g t) (f t) hgt hft).symm
  refine ⟨?_, hr.2⟩
  exact cellSolution_source_congr_sections univ ⟨G, v, 0, 0⟩ _ _ _ _ (E - D) hs
    (Filter.Eventually.of_forall fun _ => Filter.EventuallyEq.rfl) hr.1

/-! The literal graph symbol inherits a quadratic metric-stability bound from the graph energy. -/

theorem fibreQuad_sub (G H : Matrix (Fin 2) (Fin 2) ℝ) (ξ : Fin 2 → ℂ) :
    fibreQuad G ξ - fibreQuad H ξ = fibreQuad (G - H) ξ := by
  simp only [fibreQuad, Fin.sum_univ_two, Matrix.sub_apply, Complex.ofReal_sub]
  ring

theorem fibreSymbol_metric_stability (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (B L : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hd : ∀ t i j, |(G t - H t) i j| ≤ B) (ξ : Fin 2 → ℂ)
    {C C' : CellCoefficients} {src src' : ℝ → Vec 2 → ℂ}
    {F F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    {D E : ℝ → RawJet2 1 ℂ}
    (hD : IsCellInverseValue C src F D) (hE : IsCellInverseValue C' src' F' E)
    (hn : cellEnergyNorm univ (D - E) ≤ ENNReal.ofReal (L * B * fibreNorm ξ)) (t : ℝ) :
    ‖(-(η : ℂ) * fibreQuad (G t) ξ - Complex.I *
        cellMean (fun x => fibreDriftCoupling η v ξ t x * cellValue D t x)) -
      (-(η : ℂ) * fibreQuad (H t) ξ - Complex.I *
        cellMean (fun x => fibreDriftCoupling η v ξ t x * cellValue E t x))‖ ≤
      (4 + Cw * L) * B * fibreNorm ξ ^ 2 := by
  have hmean := fibreDrift_mean_difference_norm_le η Cw hCw hv hw ξ hD hE
    (L * B * fibreNorm ξ) (mul_nonneg (mul_nonneg hL hB) (fibreNorm_nonneg ξ)) hn t
  have hquad := fibreQuad_norm_le_four_mul (G t - H t) B hB (hd t) ξ
  have hηnorm : ‖(η : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hη0] using hη
  have hq : ‖-(η : ℂ) * (fibreQuad (G t) ξ - fibreQuad (H t) ξ)‖ ≤
      4 * B * fibreNorm ξ ^ 2 := by
    rw [norm_mul, norm_neg, fibreQuad_sub]
    calc
      _ ≤ 1 * (4 * B * fibreNorm ξ ^ 2) :=
        mul_le_mul hηnorm hquad (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  have hsplit :
      (-(η : ℂ) * fibreQuad (G t) ξ - Complex.I *
        cellMean (fun x => fibreDriftCoupling η v ξ t x * cellValue D t x)) -
      (-(η : ℂ) * fibreQuad (H t) ξ - Complex.I *
        cellMean (fun x => fibreDriftCoupling η v ξ t x * cellValue E t x)) =
      -(η : ℂ) * (fibreQuad (G t) ξ - fibreQuad (H t) ξ) - Complex.I *
        (cellMean (fun x => fibreDriftCoupling η v ξ t x * cellValue D t x) -
          cellMean (fun x => fibreDriftCoupling η v ξ t x * cellValue E t x)) := by ring
  rw [hsplit]
  calc
    _ ≤ ‖-(η : ℂ) * (fibreQuad (G t) ξ - fibreQuad (H t) ξ)‖ +
        ‖Complex.I * (cellMean (fun x => fibreDriftCoupling η v ξ t x * cellValue D t x) -
          cellMean (fun x => fibreDriftCoupling η v ξ t x * cellValue E t x))‖ := norm_sub_le _ _
    _ ≤ 4 * B * fibreNorm ξ ^ 2 + Cw * fibreNorm ξ * (L * B * fibreNorm ξ) := by
      simpa only [norm_mul, Complex.norm_I, one_mul] using add_le_add hq hmean
    _ = _ := by ring

/-! Quantitative continuous dependence of the actual inverse on all three parameter-dependent data. -/

/-- The resolvent bound with simultaneous changes of metric, scalar source, and divergence source. -/
theorem cellInverse_parameter_bound
    {G H : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : IsCellMetric G) (hH : IsCellMetric H)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (f g : ℝ → Vec 2 → ℂ) (F F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D E : ℝ → RawJet2 1 ℂ)
    (hfm : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hgm : AEStronglyMeasurable (Function.uncurry g)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hFm : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hF'm : AEStronglyMeasurable (Function.uncurry F')
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hf : cellUlNorm univ f < ⊤) (hg : cellUlNorm univ g < ⊤)
    (hF : cellUlNorm univ F < ⊤) (hF' : cellUlNorm univ F' < ⊤)
    (hD : IsCellInverseValue ⟨G, v, 0, 0⟩ (fun t => cellQ0 (f t)) F D)
    (hE : IsCellInverseValue ⟨H, v, 0, 0⟩ (fun t => cellQ0 (g t)) F' E) :
    cellEnergyNorm univ (E - D) ≤ ENNReal.ofReal 13 *
      (cellUlNorm univ (g - f) + cellUlNorm univ (F' - F) +
        2 * cellMetricSupNorm (H - G) * cellEnergyNorm univ E) := by
  have hd := cellMetricSupNorm_sub_lt_top hG hH
  have hdm : Measurable (Function.uncurry (H - G)) :=
    Measurable.of_eval (fun i => Measurable.of_eval (fun j =>
      (cellMetric_entry_measurable hH i j).sub (cellMetric_entry_measurable hG i j)))
  have hfluxm := cellMetricFlux_aestronglyMeasurable univ (H - G) E hdm hE.1.2.2.2.1
  have hflux := cellMetricFlux_ul_bound univ (H - G) hd hdm E hE.1.2.2.2.1
  have hfluxfinite : cellUlNorm univ (cellMetricFlux (H - G) E) < ⊤ :=
    hflux.trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) hd) hE.2.2)
  have hgf := (cellUlNorm_sub univ g f hgm hfm).trans_lt
    (ENNReal.add_lt_top.mpr ⟨hg, hf⟩)
  have hFF := (cellUlNorm_sub univ F' F hF'm hFm).trans_lt
    (ENNReal.add_lt_top.mpr ⟨hF', hF⟩)
  have hR := cellUlNorm_add univ (F' - F) (cellMetricFlux (H - G) E)
    (hF'm.sub hFm) hfluxm
  have hRf := hR.trans_lt (ENNReal.add_lt_top.mpr ⟨hFF, hfluxfinite⟩)
  have hb := cellAllTimeInverse_bound_ae hG hv (g - f)
    ((F' - F) + cellMetricFlux (H - G) E) (hgm.sub hfm)
    ((hF'm.sub hFm).add hfluxm) hgf hRf (E - D)
    (cellInverse_parameter_difference hG hH v f g F F' D E hfm hgm hf hg hD hE)
  refine hb.trans ?_
  have hRb := hR.trans (add_le_add le_rfl hflux)
  rw [add_assoc]
  gcongr

/-! The exact scaled-difference equation for directional difference quotients. -/

/-- Real scaling commutes with the inverse relation for literal mean-free scalar sources. -/
theorem cellInverse_meanFree_smul {C : CellCoefficients}
    (f : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellInverseValue C (fun t => cellQ0 (f t)) F D) (r : ℝ) :
    IsCellInverseValue C (fun t => cellQ0 ((r • f) t)) (r • F) (r • D) := by
  have h := cellInverse_smul hD r
  have he : r • (fun t => cellQ0 (f t)) = fun t => cellQ0 ((r • f) t) := by
    funext t x
    exact congrFun (cellQ0_smul r (f t)).symm x
  rw [he] at h
  exact h

/-- The difference quotient solves the fixed-metric equation with the exact difference metric flux. -/
theorem cellInverse_scaled_parameter_difference
    {G H : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : IsCellMetric G) (hH : IsCellMetric H)
    (v : ℝ → Vec 2 → Vec 2) (f g : ℝ → Vec 2 → ℂ)
    (F F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D E : ℝ → RawJet2 1 ℂ)
    (hfm : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hgm : AEStronglyMeasurable (Function.uncurry g)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hf : cellUlNorm univ f < ⊤) (hg : cellUlNorm univ g < ⊤)
    (hD : IsCellInverseValue ⟨G, v, 0, 0⟩ (fun t => cellQ0 (f t)) F D)
    (hE : IsCellInverseValue ⟨H, v, 0, 0⟩ (fun t => cellQ0 (g t)) F' E) (r : ℝ) :
    IsCellInverseValue ⟨G, v, 0, 0⟩ (fun t => cellQ0 ((r • (g - f)) t))
      (r • (F' - F) + cellMetricFlux (r • (H - G)) E) (r • (E - D)) := by
  have h := cellInverse_meanFree_smul (g - f)
    ((F' - F) + cellMetricFlux (H - G) E) (E - D)
    (cellInverse_parameter_difference hG hH v f g F F' D E hfm hgm hf hg hD hE) r
  rw [smul_add, ← cellMetricFlux_smul_metric] at h
  exact h

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization Filter Topology
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Local analyticity of actual weak solution families follows from the proved perturbation inverse and uniqueness. -/

theorem cellBlochEvolution_family_analyticAt {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (hκ : AEStronglyMeasurable C.κ (volume.restrict (Icc a b)))
    (hκb : ∀ t, ‖C.κ t‖ ≤ k)
    (δ : X → Fin 2 → ℂ) (q : X → Lp ℂ ∞ (volume.restrict (Icc a b))) (x : X)
    (hδ : AnalyticAt ℂ δ x) (hq : AnalyticAt ℂ q x) (hδ0 : δ x = 0) (hq0 : q x = 0)
    (d : CellFiniteEnergyDatum a b) (z : X → CellEnergySpace a b)
    (hz : ∀ᶠ y in 𝓝 x, IsCellFiniteEnergyEvolution
      { C with θ := C.θ + δ y, κ := fun t => C.κ t + q y t } hG V hv hb d (z y)) :
    AnalyticAt ℂ z x := by
  let sol := cellFiniteEnergyEvolutionCLM hab C hG V k hv hb hκ hκb
  let T := fun y => cellBlochPolynomialEvolutionOperator hab C hG V hv hb sol (δ y) (q y)
  have hT : AnalyticAt ℂ T x :=
    cellBlochPolynomialEvolution_analyticAt hab C hG V hv hb sol δ q x hδ hq
  have hzero : T x = 0 := by
    dsimp only [T, cellBlochPolynomialEvolutionOperator]
    rw [hδ0, hq0, cellBlochPolynomialForcing_zero, map_zero]
  have hinv := analyticOperatorPerturbation_inverse hT hzero
  have hunit := analyticOperatorPerturbation_eventually_isUnit hT hzero
  let SL := (cellEnergySpaceOfCarrierCLM a b).comp sol
  have hd := cellBlochExternalDatum_analyticAt δ x hδ d
  have hu : AnalyticAt ℂ (fun y => SL (cellBlochExternalDatum (δ y) d)) x :=
    (SL.analyticAt (cellBlochExternalDatum (δ x) d)).comp
      (f := fun y => cellBlochExternalDatum (δ y) d) (x := x) hd
  have hf := cellEnergyOperatorApply_analyticAt a b
    (fun y => Ring.inverse (1 - T y)) (fun y => SL (cellBlochExternalDatum (δ y) d)) x hinv hu
  apply hf.congr
  filter_upwards [hunit, hz] with y hunit' hz'
  exact (cellBlochEvolution_inverse_formula hab C hG V k hv hb hκ hκb
    (δ y) (q y) d (z y) hunit' hz').symm

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.CycleEvolution

/-! Norm continuity of the actual cell inverse under norm-continuous data. -/

/-- The actual inverse carries continuous metric and source families to energy-continuous families. -/
theorem cellInverse_norm_continuous {A : Type*} [TopologicalSpace A]
    (G : A → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (f : A → ℝ → Vec 2 → ℂ)
    (F : A → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D : A → ℝ → RawJet2 1 ℂ)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hG : ∀ Y, IsCellMetric (G Y))
    (hf : ∀ Y, AEStronglyMeasurable (Function.uncurry (f Y))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) ∧
      cellUlNorm univ (f Y) < ⊤)
    (hF : ∀ Y, AEStronglyMeasurable (Function.uncurry (F Y))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) ∧
      cellUlNorm univ (F Y) < ⊤)
    (hD : ∀ Y, IsCellInverseValue ⟨G Y, v, 0, 0⟩ (fun t => cellQ0 (f Y t)) (F Y) (D Y))
    (Y0 : A)
    (hGc : Tendsto (fun Y => cellMetricSupNorm (G Y - G Y0)) (𝓝 Y0) (𝓝 0))
    (hfc : Tendsto (fun Y => cellUlNorm univ (f Y - f Y0)) (𝓝 Y0) (𝓝 0))
    (hFc : Tendsto (fun Y => cellUlNorm univ (F Y - F Y0)) (𝓝 Y0) (𝓝 0)) :
    Tendsto (fun Y => cellEnergyNorm univ (D Y - D Y0)) (𝓝 Y0) (𝓝 0) := by
  let B := fun Y => cellUlNorm univ (f Y - f Y0) + cellUlNorm univ (f Y0) +
    cellUlNorm univ (F Y - F Y0) + cellUlNorm univ (F Y0)
  have hB : Tendsto B (𝓝 Y0)
      (𝓝 (cellUlNorm univ (f Y0) + cellUlNorm univ (F Y0))) := by
    simpa only [zero_add, add_zero, B] using
      ((hfc.add_const (cellUlNorm univ (f Y0))).add hFc).add_const (cellUlNorm univ (F Y0))
  have hBd : ∀ Y, cellEnergyNorm univ (D Y) ≤ ENNReal.ofReal 13 * B Y := by
    intro Y
    have h1 := cellUlNorm_add univ (f Y - f Y0) (f Y0)
      ((hf Y).1.sub (hf Y0).1) (hf Y0).1
    have h2 := cellUlNorm_add univ (F Y - F Y0) (F Y0)
      ((hF Y).1.sub (hF Y0).1) (hF Y0).1
    rw [sub_add_cancel] at h1 h2
    have hb := cellAllTimeInverse_bound_ae (hG Y) hv (f Y) (F Y)
      (hf Y).1 (hF Y).1 (hf Y).2 (hF Y).2 (D Y) (hD Y)
    refine hb.trans ?_
    unfold B
    rw [add_assoc (cellUlNorm univ (f Y - f Y0) + cellUlNorm univ (f Y0))]
    gcongr
  have hbound (Y : A) : cellEnergyNorm univ (D Y - D Y0) ≤ ENNReal.ofReal 13 *
      (cellUlNorm univ (f Y - f Y0) + cellUlNorm univ (F Y - F Y0) +
        (2 * cellMetricSupNorm (G Y - G Y0)) * (ENNReal.ofReal 13 * B Y)) := by
    have hb := cellInverse_parameter_bound (hG Y0) (hG Y) hv
      (f Y0) (f Y) (F Y0) (F Y) (D Y0) (D Y)
      (hf Y0).1 (hf Y).1 (hF Y0).1 (hF Y).1
      (hf Y0).2 (hf Y).2 (hF Y0).2 (hF Y).2 (hD Y0) (hD Y)
    exact hb.trans (by gcongr; exact hBd Y)
  have hB13 := ENNReal.Tendsto.const_mul hB (a := ENNReal.ofReal 13) (Or.inr (by simp))
  have h2G := ENNReal.Tendsto.const_mul hGc (a := 2) (Or.inr (by norm_num))
  have hfin : ENNReal.ofReal 13 * (cellUlNorm univ (f Y0) + cellUlNorm univ (F Y0)) ≠ ⊤ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.mpr ⟨(hf Y0).2, (hF Y0).2⟩)).ne
  have hm := ENNReal.Tendsto.mul h2G (Or.inr hfin) hB13 (Or.inr (by simp))
  have hs := (hfc.add hFc).add hm
  have hl := ENNReal.Tendsto.const_mul hs (a := ENNReal.ofReal 13) (Or.inr (by simp))
  have hlim : Tendsto (fun Y => ENNReal.ofReal 13 *
      (cellUlNorm univ (f Y - f Y0) + cellUlNorm univ (F Y - F Y0) +
        (2 * cellMetricSupNorm (G Y - G Y0)) * (ENNReal.ofReal 13 * B Y)))
      (𝓝 Y0) (𝓝 0) := by simpa only [mul_zero, zero_mul, zero_add, add_zero] using hl
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) hbound

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! The factorial estimate for actual solutions of every finite literal cell jet equation. -/

/-- Actual triangular inverse solutions obey the literal factorial bound with universal constant 100. -/
theorem cellInverse_jet_factorial_bound (K : ℕ)
    (Gj : ℕ × ℕ → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (fj : ℕ × ℕ → ℝ → Vec 2 → ℂ)
    (Fj : ℕ × ℕ → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (cj : ℕ × ℕ → ℝ → RawJet2 1 ℂ)
    (hG0 : IsCellMetric (Gj 0))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hdata : ∀ α : ℕ × ℕ, α.1 + α.2 ≤ K →
      cellMetricSupNorm (Gj α) < ⊤ ∧ Measurable (Function.uncurry (Gj α)) ∧
      cellUlNorm univ (fj α) < ⊤ ∧ cellUlNorm univ (Fj α) < ⊤ ∧
      AEStronglyMeasurable (Function.uncurry (fj α))
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) ∧
      AEStronglyMeasurable (Function.uncurry (Fj α))
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hsol : ∀ α : ℕ × ℕ, α.1 + α.2 ≤ K →
      IsCellInverseValue ⟨Gj 0, v, 0, 0⟩ (fun t => cellQ0 (fj α t))
        (Fj α + cellMetricJetFlux Gj cj α) (cj α))
    {ρ : ℝ} (hρ : 0 < ρ)
    (hsmall : ENNReal.ofReal 100 * factorialJetSum ((jetIndices K).erase 0) ρ
      (fun β => cellMetricSupNorm (Gj β)) ≤ 1 / 2) :
    factorialJetSum (jetIndices K) ρ (fun α => cellEnergyNorm univ (cj α)) ≤
      ENNReal.ofReal 200 * factorialJetSum (jetIndices K) ρ
        (fun α => cellUlNorm univ (fj α) + cellUlNorm univ (Fj α)) := by
  have hrec (α : ℕ × ℕ) (ha : α ∈ jetIndices K) := by
    have hα := (mem_jetIndices_iff K α).mp ha
    have hb β (hβ : β ∈ cellJetFluxIndices α) :=
      (cellJetFluxIndices_metric_order hβ).trans hα
    have hg β (hβ : β ∈ cellJetFluxIndices α) :=
      (Nat.le_of_lt (cellJetFluxIndices_lower_order hβ)).trans hα
    exact cellInverse_jet_norm_recurrence Gj cj α hG0 hv (fj α) (Fj α)
      (hdata α hα).2.2.2.2.1 (hdata α hα).2.2.2.2.2
      (hdata α hα).2.2.1 (hdata α hα).2.2.2.1
      (fun β hβ => (hdata β (hb β hβ)).1)
      (fun β hβ => (hdata β (hb β hβ)).2.1)
      (fun β hβ => (hsol (α.1 - β.1, α.2 - β.2) (hg β hβ)).2.2)
      (fun β hβ => (hsol (α.1 - β.1, α.2 - β.2) (hg β hβ)).1.2.2.2.1)
      (hsol α hα)
  have hh := factorialJetMajorant K hρ.le (ENNReal.ofReal 100)
    (fun α => cellUlNorm univ (fj α) + cellUlNorm univ (Fj α))
    (fun β => cellMetricSupNorm (Gj β)) (fun α => cellEnergyNorm univ (cj α))
    (fun α ha => (hsol α ((mem_jetIndices_iff K α).mp ha)).2.2) hrec hsmall
  norm_num only [ENNReal.ofReal_ofNat] at hh ⊢
  simpa only [show (2 : ℝ≥0∞) * 100 = 200 by norm_num] using hh

end AVRegularity.CycleEvolution
end
