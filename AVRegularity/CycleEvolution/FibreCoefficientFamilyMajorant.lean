-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.FibreCoefficientStage
import AVRegularity.CycleEvolution.CellInverseJetFactorialBound
import AVRegularity.CycleEvolution.CellEnergySpaceRawJetCauchyBound
import AVRegularity.CycleEvolution.CellLimitMoments

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Every constructed coefficient stage satisfies the actual nonlinear triangular recurrence. -/

/-- All coefficients through the current degree solve their literal triangular inverse equations. -/
theorem fibreCoefficientStage_isInverse (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (n : ℕ) : ∀ (p : ℕ × ℕ), p.1 + p.2 ≤ n →
    IsCellInverseValue ⟨fun t _ => G t, v, 0, 0⟩
      (fun t => cellQ0 (fibreCoefficientSource η v
        (fun a => (fibreCoefficientStage η Cw hη G hG hv hw n a).raw) p t))
      (fibreCoefficientFlux η G
        (fun a => (fibreCoefficientStage η Cw hη G hG hv hw n a).raw) p)
      (fibreCoefficientStage η Cw hη G hG hv hw n p).raw := by
  induction n with
  | zero =>
    intro p hp
    have hp0 : p = 0 := Prod.ext (by change p.1 = 0; omega) (by change p.2 = 0; omega)
    subst p
    rw [fibreCoefficientSource_zero, fibreCoefficientFlux_zero]
    have hz : (fun t => cellQ0 ((0 : ℝ → Vec 2 → ℂ) t)) = 0 := by
      funext t x
      simp [cellQ0, cellMean]
    rw [hz]
    exact cellInverse_zero hG hv
  | succ n ih =>
    intro p hp
    have he (a : ℕ × ℕ) (ha : a.1 + a.2 < p.1 + p.2) :
        (fibreCoefficientStage η Cw hη G hG hv hw (n + 1) a).raw =
          (fibreCoefficientStage η Cw hη G hG hv hw n a).raw := by
      rw [fibreCoefficientStage_succ_lower η Cw hη G hG hv hw n a (by omega)]
    rw [fibreCoefficientSource_congr_lower η v _ _ p he,
      fibreCoefficientFlux_congr_lower η G _ _ p he]
    by_cases hn : p.1 + p.2 = n + 1
    · simp only [fibreCoefficientStage, ite_eq_left hn]
      exact fibreCoefficientInverseStep_isInverse η Cw hη G hG hv hw
        (fibreCoefficientStage η Cw hη G hG hv hw n) p
    · rw [fibreCoefficientStage_succ_lower η Cw hη G hG hv hw n p (by omega)]
      exact ih p (by omega)

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! An actual infinite triangular coefficient family from the coherent finite inverse stages. -/

/-- The coefficient of each degree is its actual inverse datum at its first construction stage. -/
def fibreCoefficientFamily (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) :
    ℕ × ℕ → ℝ → RawJet2 1 ℂ :=
  fun p => (fibreCoefficientStage η Cw hη G hG hv hw (p.1 + p.2) p).raw

/-- Each completed coefficient is literally identical to its value in every later finite stage. -/
theorem fibreCoefficientFamily_eq_stage (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (p : ℕ × ℕ) (n : ℕ) (hp : p.1 + p.2 ≤ n) :
    fibreCoefficientFamily η Cw hη G hG hv hw p =
      (fibreCoefficientStage η Cw hη G hG hv hw n p).raw := by
  unfold fibreCoefficientFamily
  rw [fibreCoefficientStage_stable η Cw hη G hG hv hw hp p le_rfl]

/-- Every coefficient of the infinite family solves the actual nonlinear triangular inverse equation. -/
theorem fibreCoefficientFamily_isInverse (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (p : ℕ × ℕ) :
    IsCellInverseValue ⟨fun t _ => G t, v, 0, 0⟩
      (fun t => cellQ0 (fibreCoefficientSource η v (fibreCoefficientFamily η Cw hη G hG hv hw) p t))
      (fibreCoefficientFlux η G (fibreCoefficientFamily η Cw hη G hG hv hw) p)
      (fibreCoefficientFamily η Cw hη G hG hv hw p) := by
  have he (a : ℕ × ℕ) (ha : a.1 + a.2 < p.1 + p.2) :
      fibreCoefficientFamily η Cw hη G hG hv hw a =
        (fibreCoefficientStage η Cw hη G hG hv hw (p.1 + p.2) a).raw :=
    fibreCoefficientFamily_eq_stage η Cw hη G hG hv hw a (p.1 + p.2) ha.le
  rw [fibreCoefficientSource_congr_lower η v _ _ p he,
    fibreCoefficientFlux_congr_lower η G _ _ p he]
  exact fibreCoefficientStage_isInverse η Cw hη G hG hv hw (p.1 + p.2) p le_rfl

/-- The correction has exactly zero constant coefficient. -/
theorem fibreCoefficientFamily_zero (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) :
    fibreCoefficientFamily η Cw hη G hG hv hw 0 = 0 := rfl

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Joint measurability and uniformly local finiteness of every actual coefficient forcing. -/

/-- Each actual scalar coefficient forcing satisfies the proved inverse-admissibility premises. -/
theorem fibreCoefficientFamily_source_admissible (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) (p : ℕ × ℕ) :
    let f := fibreCoefficientSource η v (fibreCoefficientFamily η Cw hη G hG hv hw) p
    cellUlNorm Set.univ f < ⊤ ∧ AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)) := by
  let A := fun a : ℕ × ℕ => fibreCoefficientStage η Cw hη G hG hv hw (a.1 + a.2) a
  exact fibreCoefficientSource_admissible η Cw hv hw A p

/-- Each actual vector coefficient forcing satisfies the proved inverse-admissibility premises. -/
theorem fibreCoefficientFamily_flux_admissible (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) (p : ℕ × ℕ) :
    let F := fibreCoefficientFlux η G (fibreCoefficientFamily η Cw hη G hG hv hw) p
    cellUlNorm Set.univ F < ⊤ ∧ AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)) := by
  let A := fun a : ℕ × ℕ => fibreCoefficientStage η Cw hη G hG hv hw (a.1 + a.2) a
  have hGm : Measurable G := hG.1.comp
    (measurable_id.prodMk (measurable_const (a := (0 : Vec 2))))
  exact fibreCoefficientFlux_admissible η hη G hGm
    (fun t i j => cellMetric_entry_bound hG t 0 i j) A p

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Actual Lipschitz estimates for the nonlinear scalar graph source. -/

/-- The nonlinear scalar forcing difference is controlled by the actual energy distance. -/
theorem fibreGraphSource_sub_ul_bound_of_inverse_difference (η Cw : ℝ) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ)
    {C C' C'' : CellCoefficients} {src src' src'' : ℝ → Vec 2 → ℂ}
    {F F' F'' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    {D E : ℝ → RawJet2 1 ℂ}
    (hD : IsCellInverseValue C src F D) (hE : IsCellInverseValue C' src' F' E)
    (hdiff : IsCellInverseValue C'' src'' F'' (D - E)) :
    cellUlNorm univ (fibreGraphSource η v ξ (cellValue D) -
      fibreGraphSource η v ξ (cellValue E)) ≤
      2 * (ENNReal.ofReal (Cw * fibreNorm ξ) * cellEnergyNorm univ (D - E)) +
        ENNReal.ofReal (Cw * fibreNorm ξ) * cellEnergyNorm univ D * cellEnergyNorm univ (D - E) +
        ENNReal.ofReal (Cw * fibreNorm ξ) * cellEnergyNorm univ (D - E) * cellEnergyNorm univ E := by
  let b := fibreDriftCoupling η v ξ
  have hb := fibreDriftCoupling_measurable η hv ξ
  have hB := fibreDriftCoupling_norm_le η Cw v hw ξ
  have hz : Measurable (Function.uncurry (fun t x => -Complex.I * b t x)) := hb.const_mul _
  have hZ (t : ℝ) (x : Vec 2) : ‖-Complex.I * b t x‖ ≤ Cw * fibreNorm ξ := by
    simpa only [norm_mul, norm_neg, Complex.norm_I, one_mul] using hB t x
  have hp := cellProjectedMultiplier_ul_bound (fun t x => -Complex.I * b t x)
    (Cw * fibreNorm ξ) hz hZ hdiff
  have hq := cellMeanMultiplier_ul_bound b (Cw * fibreNorm ξ) hb hB hD hdiff
  have hr := cellMeanMultiplier_ul_bound b (Cw * fibreNorm ξ) hb hB hdiff hE
  let p : ℝ → Vec 2 → ℂ := fun t => cellQ0 (fun x => -Complex.I * b t x * cellValue (D - E) t x)
  let q : ℝ → Vec 2 → ℂ := fun t x => cellValue (D - E) t x *
    cellMean (fun y => b t y * cellValue D t y)
  let r : ℝ → Vec 2 → ℂ := fun t x => cellValue E t x *
    cellMean (fun y => b t y * cellValue (D - E) t y)
  have he : fibreGraphSource η v ξ (cellValue D) - fibreGraphSource η v ξ (cellValue E) =
      (p + Complex.I • q) + Complex.I • r := by
    rw [fibreGraphSource_difference η Cw hv hw ξ hD hE]
    funext t x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, p, q, r, b]
    ring
  have hpm : AEStronglyMeasurable (Function.uncurry p)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) := by
    simpa only [p, Function.uncurry_def] using hp.2
  rw [he]
  exact (cellUlNorm_add_two_I_smul_le univ p q r hpm hq.2 hr.2).trans
    (add_le_add (add_le_add hp.1 hq.1) hr.1)

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Every monomial-scaled coefficient solves its actual projected cell equation. -/

/-- Actual coefficient inverse equations persist under the exact monomial scaling. -/
theorem fibreCoefficientFamily_scaled_isInverse (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (p : ℕ × ℕ) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    IsCellInverseValue ⟨fun t _ => G t, v, 0, 0⟩
      (fibreCoefficientScaledSource η v r ξ p) (fibreCoefficientScaledFlux η G r ξ p)
      (fibreMonomial ξ p • r p) :=
  cellInverse_complex_smul (fibreCoefficientFamily_isInverse η Cw hη G hG hv hw p)
    (fibreMonomial ξ p)

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
open scoped BigOperators
namespace AVRegularity.CycleEvolution

/-! Exact vanishing of the constant and linear symbol coefficients. -/

/-- The metric symbol is exactly quadratic and has no lower coefficients. -/
theorem fibreCoefficientMetricSymbol_low_order (η : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ × ℕ) (hp : p.1 + p.2 ≤ 1) (t : ℝ) :
    fibreCoefficientMetricSymbol η G p t = 0 := by
  have hne (i j : Fin 2) : p ≠ cellJetDirection i + cellJetDirection j := by
    have hi : (cellJetDirection i).1 + (cellJetDirection i).2 = 1 := by
      simpa using cellJetDirection_order (0 : ℕ × ℕ) i
    have hij := cellJetDirection_order (cellJetDirection i) j
    intro he
    rw [← he] at hij
    omega
  simp only [fibreCoefficientMetricSymbol, hne, ite_false, Finset.sum_const_zero, mul_zero]

/-- Any correction with zero constant coefficient gives a drift symbol without constant or linear terms. -/
theorem fibreCoefficientDriftSymbol_low_order (η : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (hr : r 0 = 0)
    (p : ℕ × ℕ) (hp : p.1 + p.2 ≤ 1) (t : ℝ) :
    fibreCoefficientDriftSymbol η v r p t = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  have ho := fibreCoefficientPrevious_order hj
  have hz : fibreCoefficientPrevious p j = 0 := by
    apply Prod.ext
    · change (fibreCoefficientPrevious p j).1 = 0
      omega
    · change (fibreCoefficientPrevious p j).2 = 0
      omega
  rw [hz, hr]
  simp [cellValue, cellMean]

/-- The actual symbol family has exactly zero constant and linear coefficients. -/
theorem fibreCoefficientFamily_symbol_low_order (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (p : ℕ × ℕ) (hp : p.1 + p.2 ≤ 1) (t : ℝ) :
    fibreCoefficientSymbol η G v (fibreCoefficientFamily η Cw hη G hG hv hw) p t = 0 := by
  rw [fibreCoefficientSymbol, fibreCoefficientMetricSymbol_low_order η G p hp t,
    fibreCoefficientDriftSymbol_low_order η v _
      (fibreCoefficientFamily_zero η Cw hη G hG hv hw) p hp t, zero_add]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The actual triangular inverse recurrence forces coefficient reality by uniqueness. -/

theorem fibreCoefficient_inverse_reality (η : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (D : ℕ × ℕ → ℝ → RawJet2 1 ℂ)
    (hD : ∀ p, IsCellInverseValue ⟨fun t _ => G t, v, 0, 0⟩
      (fun t => cellQ0 (fibreCoefficientSource η v D p t)) (fibreCoefficientFlux η G D p) (D p)) :
    ∀ p t, (fun x => star (cellValue (D p) t x)) =ᵐ[volume.restrict AVenhance.unitCube]
      (fun x => fibreRealitySign p * cellValue (D p) t x) := by
  have hn (n : ℕ) : ∀ p : ℕ × ℕ, p.1 + p.2 = n → ∀ t,
      (fun x => star (cellValue (D p) t x)) =ᵐ[volume.restrict AVenhance.unitCube]
        (fun x => fibreRealitySign p * cellValue (D p) t x) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hp
      have hlow (a : ℕ × ℕ) (ha : a.1 + a.2 < p.1 + p.2) (t : ℝ) :
          (fun x => star (cellValue (D a) t x)) =ᵐ[volume.restrict AVenhance.unitCube]
            (fun x => fibreRealitySign a * cellValue (D a) t x) :=
        ih (a.1 + a.2) (by omega) a rfl t
      have hs (t : ℝ) : (fun x => star (cellQ0 (fibreCoefficientSource η v D p t) x)) =ᵐ[
          volume.restrict AVenhance.unitCube]
          (fun x => fibreRealitySign p * cellQ0 (fibreCoefficientSource η v D p t) x) :=
        cellQ0_parity_ae _ _ (fibreCoefficientSource_reality η v D p t (fun a ha => hlow a ha t))
      have hf (t : ℝ) := fibreCoefficientFlux_reality η G D p t (fun a ha => hlow a ha t)
      have hc := cellInverse_conjugate (hD p)
      have hscaled := cellInverse_complex_smul (hD p) (fibreRealitySign p)
      have hc' : IsCellInverseValue ⟨fun t _ => G t, v, 0, 0⟩
          (fibreRealitySign p • (fun t => cellQ0 (fibreCoefficientSource η v D p t)))
          (fibreRealitySign p • fibreCoefficientFlux η G D p)
          (fun t => cellRawJetConj (D p t)) :=
        ⟨cellSolution_source_congr_sections univ ⟨fun t _ => G t, v, 0, 0⟩ _ _ _ _
          (fun t => cellRawJetConj (D p t)) (Filter.Eventually.of_forall hs)
          (Filter.Eventually.of_forall hf) hc.1, hc.2⟩
      have hu := cellAllTimeInverse_unique_arbitrary_source hG hv _ _ _ _ hc' hscaled
      intro t
      have ht := hu t
      change (fun x => star (cellValue (D p) t x)) =ᵐ[volume.restrict AVenhance.unitCube]
        (fun x => fibreRealitySign p * cellValue (D p) t x) at ht
      exact ht
  intro p t
  exact hn (p.1 + p.2) p rfl t

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! Actual coefficient energy bounds derived from the full triangular forcing recurrence. -/

/-- Every actual coefficient inverse obeys the finite linear-plus-quadratic energy recurrence. -/
theorem fibreCoefficient_inverse_energy_bound (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (A : ℕ × ℕ → CellInverseDatum ⟨fun t _ => G t, v, 0, 0⟩) (p : ℕ × ℕ)
    (R : ℝ → RawJet2 1 ℂ)
    (hR : IsCellInverseValue ⟨fun t _ => G t, v, 0, 0⟩
      (fun t => cellQ0 (fibreCoefficientSource η v (fun a => (A a).raw) p t))
      (fibreCoefficientFlux η G (fun a => (A a).raw) p) R) :
    cellEnergyNorm univ R ≤ 13 *
      ((∑ j ∈ fibreCoefficientDirections p, ENNReal.ofReal Cw *
        ((if p = cellJetDirection j then 1 else 0) +
          cellEnergyNorm univ (A (fibreCoefficientPrevious p j)).raw)) +
       (∑ j ∈ fibreCoefficientDirections p,
        ∑ a ∈ fibreCoefficientPairs (fibreCoefficientPrevious p j), ENNReal.ofReal Cw *
          cellEnergyNorm univ (A (fibreCoefficientComplement (fibreCoefficientPrevious p j) a)).raw *
          cellEnergyNorm univ (A a).raw) +
       (∑ j ∈ fibreCoefficientDirections p, 8 * cellEnergyNorm univ (A (fibreCoefficientPrevious p j)).raw)) := by
  have hGm : Measurable G := hG.1.comp
    (measurable_id.prodMk (measurable_const (a := (0 : Vec 2))))
  have he := fun t i j => cellMetric_entry_bound hG t 0 i j
  have hs := fibreCoefficientSource_admissible η Cw hv hw A p
  have hF := fibreCoefficientFlux_admissible η hη G hGm he A p
  have hb := cellAllTimeInverse_bound_ae hG hv
    (fibreCoefficientSource η v (fun a => (A a).raw) p)
    (fibreCoefficientFlux η G (fun a => (A a).raw) p) hs.2 hF.2 hs.1 hF.1 R hR
  norm_num only [ENNReal.ofReal_ofNat] at hb
  apply hb.trans
  apply mul_le_mul' le_rfl
  apply add_le_add
  · have hl := fibreCoefficientLinearSource_admissible η Cw hv hw A p
    have hq := fibreCoefficientQuadraticSource_admissible η Cw hv hw A p
    exact (cellUlNorm_add univ
      (fibreCoefficientLinearSource η v (fun a => (A a).raw) p)
      (fibreCoefficientQuadraticSource η v (fun a => (A a).raw) p) hl.2 hq.2).trans
      (add_le_add (fibreCoefficientLinearSource_ul_bound η Cw hv hw A p)
        (fibreCoefficientQuadraticSource_ul_bound η Cw hv hw A p))
  · exact fibreCoefficientFlux_ul_bound η hη G hGm he A p

/-! Actual coefficient forcing bounds derived from lower coefficient energy bounds. -/

/-- Actual coefficient forcing norms obey the finite linear-plus-quadratic energy bound. -/
theorem fibreCoefficient_forcing_norm_bound (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (A : ℕ × ℕ → CellInverseDatum ⟨fun t _ => G t, v, 0, 0⟩) (p : ℕ × ℕ)
    : cellUlNorm univ (fibreCoefficientSource η v (fun a => (A a).raw) p) +
      cellUlNorm univ (fibreCoefficientFlux η G (fun a => (A a).raw) p) ≤
      ((∑ j ∈ fibreCoefficientDirections p, ENNReal.ofReal Cw *
        ((if p = cellJetDirection j then 1 else 0) +
          cellEnergyNorm univ (A (fibreCoefficientPrevious p j)).raw)) +
       (∑ j ∈ fibreCoefficientDirections p,
        ∑ a ∈ fibreCoefficientPairs (fibreCoefficientPrevious p j), ENNReal.ofReal Cw *
          cellEnergyNorm univ (A (fibreCoefficientComplement (fibreCoefficientPrevious p j) a)).raw *
          cellEnergyNorm univ (A a).raw) +
       (∑ j ∈ fibreCoefficientDirections p, 8 * cellEnergyNorm univ (A (fibreCoefficientPrevious p j)).raw)) := by
  have hGm : Measurable G := hG.1.comp
    (measurable_id.prodMk (measurable_const (a := (0 : Vec 2))))
  have he := fun t i j => cellMetric_entry_bound hG t 0 i j
  apply add_le_add
  · have hl := fibreCoefficientLinearSource_admissible η Cw hv hw A p
    have hq := fibreCoefficientQuadraticSource_admissible η Cw hv hw A p
    exact (cellUlNorm_add univ
      (fibreCoefficientLinearSource η v (fun a => (A a).raw) p)
      (fibreCoefficientQuadraticSource η v (fun a => (A a).raw) p) hl.2 hq.2).trans
      (add_le_add (fibreCoefficientLinearSource_ul_bound η Cw hv hw A p)
        (fibreCoefficientQuadraticSource_ul_bound η Cw hv hw A p))
  · exact fibreCoefficientFlux_ul_bound η hη G hGm he A p

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Uniformly local bounds for the actual monomial-scaled coefficient forcing. -/

/-- Projection and monomial scaling give an absolute forcing norm bound. -/
theorem fibreCoefficientFamily_scaled_forcing_bound (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (p : ℕ × ℕ) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    cellUlNorm Set.univ (fibreCoefficientScaledSource η v r ξ p) +
      cellUlNorm Set.univ (fibreCoefficientScaledFlux η G r ξ p) ≤
      2 * (ENNReal.ofReal ‖fibreMonomial ξ p‖ *
        (cellUlNorm Set.univ (fibreCoefficientSource η v r p) +
          cellUlNorm Set.univ (fibreCoefficientFlux η G r p))) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  have hs := fibreCoefficientFamily_source_admissible η Cw hη G hG hv hw p
  have hF := fibreCoefficientFamily_flux_admissible η Cw hη G hG hv hw p
  have hq := cellQ0_aestronglyMeasurable hs.2
  have hb := (cellUlNorm_complex_smul Set.univ (fibreMonomial ξ p)
    (fun t => cellQ0 (fibreCoefficientSource η v r p t)) hq).trans
      (mul_le_mul' le_rfl (cellQ0_cellUlNorm_le _ hs.2 hs.1))
  have hflux := cellUlNorm_complex_smul Set.univ (fibreMonomial ξ p)
    (fibreCoefficientFlux η G r p) hF.2
  change cellUlNorm Set.univ (fibreMonomial ξ p • (fun t => cellQ0 (fibreCoefficientSource η v r p t))) +
    cellUlNorm Set.univ (fibreMonomial ξ p • fibreCoefficientFlux η G r p) ≤ _
  calc
    _ ≤ ‖fibreMonomial ξ p‖ₑ * (2 * cellUlNorm Set.univ (fibreCoefficientSource η v r p)) +
        ‖fibreMonomial ξ p‖ₑ * cellUlNorm Set.univ (fibreCoefficientFlux η G r p) := add_le_add hb hflux
    _ ≤ ‖fibreMonomial ξ p‖ₑ * (2 * cellUlNorm Set.univ (fibreCoefficientSource η v r p)) +
        2 * (‖fibreMonomial ξ p‖ₑ * cellUlNorm Set.univ (fibreCoefficientFlux η G r p)) := by
      apply add_le_add le_rfl
      exact le_mul_of_one_le_left' (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    _ = _ := by rw [ofReal_norm]; ring

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Joint almost measurability of the actual scaled coefficient forcing. -/

/-- The projected scalar forcing of every monomial-scaled coefficient is jointly almost measurable. -/
theorem fibreCoefficientFamily_scaled_source_aestronglyMeasurable (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (p : ℕ × ℕ) :
    AEStronglyMeasurable
      (Function.uncurry (fibreCoefficientScaledSource η v
        (fibreCoefficientFamily η Cw hη G hG hv hw) ξ p))
      ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)) := by
  have hs := fibreCoefficientFamily_source_admissible η Cw hη G hG hv hw p
  have hq := cellQ0_aestronglyMeasurable hs.2
  have he : Function.uncurry (fibreCoefficientScaledSource η v
      (fibreCoefficientFamily η Cw hη G hG hv hw) ξ p) =
      fibreMonomial ξ p • (fun z : ℝ × Vec 2 => cellQ0
        (fibreCoefficientSource η v (fibreCoefficientFamily η Cw hη G hG hv hw) p z.1) z.2) := by
    funext z
    rfl
  rw [he]
  exact hq.const_smul (fibreMonomial ξ p)

/-- The vector forcing of every monomial-scaled coefficient is jointly almost measurable. -/
theorem fibreCoefficientFamily_scaled_flux_aestronglyMeasurable (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (p : ℕ × ℕ) :
    AEStronglyMeasurable
      (Function.uncurry (fibreCoefficientScaledFlux η G
        (fibreCoefficientFamily η Cw hη G hG hv hw) ξ p))
      ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)) := by
  have hF := fibreCoefficientFamily_flux_admissible η Cw hη G hG hv hw p
  have he : Function.uncurry (fibreCoefficientScaledFlux η G
      (fibreCoefficientFamily η Cw hη G hG hv hw) ξ p) =
      fibreMonomial ξ p • Function.uncurry
        (fibreCoefficientFlux η G (fibreCoefficientFamily η Cw hη G hG hv hw) p) := by
    funext z
    rfl
  rw [he]
  exact hF.2.const_smul (fibreMonomial ξ p)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Quantitative metric stability before absorption, for any two actual nonlinear graphs. -/

theorem fibreGraph_metric_difference_bound (η Cw : ℝ) (hη : η ≤ 1)
    (G H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) (hH : IsCellMetric (fun t _ => H t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (B : ℝ) (hB : 0 ≤ B) (hd : ∀ t i j, |(G t - H t) i j| ≤ B)
    (ξ : Fin 2 → ℂ) (D E : ℝ → RawJet2 1 ℂ)
    (hD : IsCellInverseValue ⟨fun t _ => G t, v, 0, 0⟩
      (fibreGraphSource η v ξ (cellValue D)) (fibreGraphFlux η G ξ (cellValue D)) D)
    (hE : IsCellInverseValue ⟨fun t _ => H t, v, 0, 0⟩
      (fibreGraphSource η v ξ (cellValue E)) (fibreGraphFlux η H ξ (cellValue E)) E) :
    cellEnergyNorm univ (D - E) ≤
      (13 * (ENNReal.ofReal (Cw * fibreNorm ξ) *
        (2 + cellEnergyNorm univ D + cellEnergyNorm univ E) +
        ENNReal.ofReal (8 * fibreNorm ξ))) * cellEnergyNorm univ (D - E) +
      13 * (ENNReal.ofReal (4 * B * fibreNorm ξ) + 2 * ENNReal.ofReal B) *
        cellEnergyNorm univ D := by
  let f := fibreGraphSource η v ξ (cellValue E)
  let g := fibreGraphSource η v ξ (cellValue D)
  let F := fibreGraphFlux η H ξ (cellValue E)
  let F' := fibreGraphFlux η G ξ (cellValue D)
  have hgm : Measurable G := hG.1.comp
    (measurable_id.prodMk (measurable_const (a := (0 : Vec 2))))
  have hhm : Measurable H := hH.1.comp
    (measurable_id.prodMk (measurable_const (a := (0 : Vec 2))))
  have hgentries := fun t i j => cellMetric_entry_bound hG t 0 i j
  have hhentries := fun t i j => cellMetric_entry_bound hH t 0 i j
  have hfs := fibreGraphSource_ul_bound η Cw hv hw ξ hE
  have hgs := fibreGraphSource_ul_bound η Cw hv hw ξ hD
  have hF := fibreGraphFlux_ul_bound η hη H hhm hhentries ξ hE.1
  have hF' := fibreGraphFlux_ul_bound η hη G hgm hgentries ξ hD.1
  have hnD := hD.2.2
  have hnE := hE.2.2
  have hf : cellUlNorm univ f < ⊤ := hfs.1.trans_lt (by finiteness)
  have hg : cellUlNorm univ g < ⊤ := hgs.1.trans_lt (by finiteness)
  have hFf : cellUlNorm univ F < ⊤ := hF.1.trans_lt (by finiteness)
  have hF'f : cellUlNorm univ F' < ⊤ := hF'.1.trans_lt (by finiteness)
  have hqD : (fun t => cellQ0 (g t)) = g := by
    funext t
    exact cellQ0_eq_self_of_mean_zero _
      (fibreGraphSource_memLp_and_mean_zero η Cw hv hw ξ hD t).2
  have hqE : (fun t => cellQ0 (f t)) = f := by
    funext t
    exact cellQ0_eq_self_of_mean_zero _
      (fibreGraphSource_memLp_and_mean_zero η Cw hv hw ξ hE t).2
  have hDi : IsCellInverseValue ⟨fun t _ => G t, v, 0, 0⟩
      (fun t => cellQ0 (g t)) F' D := by rw [hqD]; exact hD
  have hEi : IsCellInverseValue ⟨fun t _ => H t, v, 0, 0⟩
      (fun t => cellQ0 (f t)) F E := by rw [hqE]; exact hE
  have hdiff := cellInverse_parameter_difference hH hG v f g F F' E D
    hfs.2 hgs.2 hf hg hEi hDi
  have hs := fibreGraphSource_sub_ul_bound_of_inverse_difference η Cw hv hw ξ hD hE hdiff
  have hflux := fibreGraphFlux_metric_difference_ul_bound η hη G H hgm hhm hhentries
    B hB hd ξ hD.1 hdiff.1
  have hm : cellMetricSupNorm ((fun t _ => G t) - (fun t _ => H t)) ≤ ENNReal.ofReal B := by
    apply iSup_le
    intro t
    apply iSup_le
    intro x
    apply iSup_le
    intro i
    apply iSup_le
    intro j
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (hd t i j)
  have hb := cellInverse_parameter_bound hH hG hv f g F F' E D hfs.2 hgs.2 hF.2 hF'.2
    hf hg hFf hF'f hEi hDi
  calc
    _ ≤ ENNReal.ofReal 13 *
        (cellUlNorm univ (g - f) + cellUlNorm univ (F' - F) +
          2 * ENNReal.ofReal B * cellEnergyNorm univ D) := hb.trans (by gcongr)
    _ ≤ ENNReal.ofReal 13 *
        ((2 * (ENNReal.ofReal (Cw * fibreNorm ξ) * cellEnergyNorm univ (D - E)) +
          ENNReal.ofReal (Cw * fibreNorm ξ) * cellEnergyNorm univ D * cellEnergyNorm univ (D - E) +
          ENNReal.ofReal (Cw * fibreNorm ξ) * cellEnergyNorm univ (D - E) * cellEnergyNorm univ E) +
          (ENNReal.ofReal (8 * fibreNorm ξ) * cellEnergyNorm univ (D - E) +
            ENNReal.ofReal (4 * B * fibreNorm ξ) * cellEnergyNorm univ D) +
          2 * ENNReal.ofReal B * cellEnergyNorm univ D) := by
      exact mul_le_mul' le_rfl (add_le_add (add_le_add hs hflux) le_rfl)
    _ = _ := by rw [ENNReal.ofReal_ofNat]; ring

/-! Metric stability of any two actual small nonlinear cell graphs. -/

theorem fibreGraph_metric_stability (η Cw : ℝ) (hη : η ≤ 1)
    (G H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) (hH : IsCellMetric (fun t _ => H t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (B : ℝ) (hB : 0 ≤ B) (hd : ∀ t i j, |(G t - H t) i j| ≤ B)
    (ξ : Fin 2 → ℂ) (D E : ℝ → RawJet2 1 ℂ)
    (hD : IsCellInverseValue ⟨fun t _ => G t, v, 0, 0⟩
      (fibreGraphSource η v ξ (cellValue D)) (fibreGraphFlux η G ξ (cellValue D)) D)
    (hE : IsCellInverseValue ⟨fun t _ => H t, v, 0, 0⟩
      (fibreGraphSource η v ξ (cellValue E)) (fibreGraphFlux η H ξ (cellValue E)) E)
    (hCw : 0 ≤ Cw) (hξ1 : fibreNorm ξ ≤ 1)
    (hnD : cellEnergyNorm univ D ≤ 1) (hnE : cellEnergyNorm univ E ≤ 1)
    (hsmall : 13 * (4 * Cw + 8) * fibreNorm ξ ≤ 1 / 2) :
    cellEnergyNorm univ (D - E) ≤ 156 * ENNReal.ofReal B * cellEnergyNorm univ D := by
  exact fibreMetric_stability_absorption _ _ _ (cellInverse_difference_energy_lt_top hD hE)
    B Cw (fibreNorm ξ) hB hCw (fibreNorm_nonneg ξ) hξ1 hnD hnE hsmall
    (fibreGraph_metric_difference_bound η Cw hη G H hG hH hv hw B hB hd ξ D E hD hE)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.CycleEvolution

/-! One actual derivative step in the triangular cell-jet induction. -/

/-- Differentiating lower states closes the next literal inverse equation, which identifies its solution. -/
theorem cellInverse_jetFamily_derivative_step (K : ℕ)
    (Gj : ℕ × ℕ → (Fin 2 → ℝ) → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (fj : ℕ × ℕ → (Fin 2 → ℝ) → ℝ → Vec 2 → ℂ)
    (Fj : ℕ × ℕ → (Fin 2 → ℝ) → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (cj : ℕ × ℕ → (Fin 2 → ℝ) → ℝ → RawJet2 1 ℂ)
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
    (hGj : IsNormJetFamily cellMetricSupNorm K univ Gj)
    (hfj : IsNormJetFamily (cellUlNorm univ) K univ fj)
    (hFj : IsNormJetFamily (cellUlNorm univ) K univ Fj)
    (hcc : ∀ α : ℕ × ℕ, α.1 + α.2 ≤ K → ∀ Y,
      Tendsto (fun Y' => cellEnergyNorm univ (cj α Y' - cj α Y)) (𝓝 Y) (𝓝 0))
    (α : ℕ × ℕ) (hα : α.1 + α.2 < K) (Y : Fin 2 → ℝ) (j : Fin 2)
    (hcd : ∀ β ∈ cellJetFluxIndices α,
      Tendsto (fun h : ℝ => cellEnergyNorm univ
        (h⁻¹ • (cj (α.1 - β.1, α.2 - β.2) (cellParameterLine Y j h) -
          cj (α.1 - β.1, α.2 - β.2) Y) -
          cj ((α.1 - β.1, α.2 - β.2) + cellJetDirection j) Y))
        (𝓝[≠] 0) (𝓝 0)) :
    Tendsto (fun h : ℝ => cellEnergyNorm univ
      (h⁻¹ • (cj α (cellParameterLine Y j h) - cj α Y) -
        cj (α + cellJetDirection j) Y)) (𝓝[≠] 0) (𝓝 0) := by
  let ε := cellJetDirection j
  let Z := cellParameterLine Y j
  have hαle := Nat.le_of_lt hα
  have hnext : (α + ε).1 + (α + ε).2 ≤ K := by
    change (α + cellJetDirection j).1 + (α + cellJetDirection j).2 ≤ K
    rw [cellJetDirection_order]
    omega
  have heps : ε.1 + ε.2 ≤ K := by
    have hh := cellJetDirection_order (0 : ℕ × ℕ) j
    change (0 + ε).1 + (0 + ε).2 = 0 + 0 + 1 at hh
    rw [zero_add] at hh
    omega
  have hβ (β : ℕ × ℕ) (hb : β ∈ cellJetFluxIndices α) : β.1 + β.2 < K :=
    (cellJetFluxIndices_metric_order hb).trans_lt hα
  have hγ (β : ℕ × ℕ) (hb : β ∈ cellJetFluxIndices α) :
      (α.1 - β.1) + (α.2 - β.2) < K :=
    (cellJetFluxIndices_lower_order hb).trans hα
  have hβnext (β : ℕ × ℕ) (hb : β ∈ cellJetFluxIndices α) :
      (β + ε).1 + (β + ε).2 ≤ K := by
    change (β + cellJetDirection j).1 + (β + cellJetDirection j).2 ≤ K
    rw [cellJetDirection_order]
    exact Nat.succ_le_of_lt (hβ β hb)
  have hγnext (β : ℕ × ℕ) (hb : β ∈ cellJetFluxIndices α) :
      ((α.1 - β.1, α.2 - β.2) + ε).1 +
        ((α.1 - β.1, α.2 - β.2) + ε).2 ≤ K := by
    change ((α.1 - β.1, α.2 - β.2) + cellJetDirection j).1 +
      ((α.1 - β.1, α.2 - β.2) + cellJetDirection j).2 ≤ K
    rw [cellJetDirection_order]
    exact Nat.succ_le_of_lt (hγ β hb)
  have hc (γ : ℕ × ℕ) (hγ : γ.1 + γ.2 ≤ K) W :
      cellEnergyNorm univ (cj γ W) < ⊤ ∧ ∀ a,
        AEStronglyMeasurable (fun p : ℝ × Vec 2 => cj γ W p.1 a p.2)
          ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) :=
    ⟨(hsol W γ hγ).2.2, (hsol W γ hγ).1.2.2.2.1⟩
  have hflux (γ : ℕ × ℕ) (hγ : γ.1 + γ.2 ≤ K) W :=
    cellMetricJetFlux_admissible_of_order K (fun β => Gj β W) (fun β => cj β W)
      (fun β hb => ⟨(hdata β hb W).1, (hdata β hb W).2.1⟩)
      (fun β hb => hc β hb W) γ hγ
  let L := fun W => cellMetricJetFlux (fun β => Gj β W) (fun β => cj β W) α
  let L1 := cellMetricJetFluxDerivative (fun β => Gj β Y) (fun β => cj β Y) α ε
  have hL1 := cellMetricJetFluxDerivative_admissible
    (fun β => Gj β Y) (fun β => cj β Y) α j (hflux (α + ε) hnext Y)
    ⟨(hdata ε heps Y).1, (hdata ε heps Y).2.1⟩ (hc α hαle Y).1 (hc α hαle Y).2
  have hLd : Tendsto (fun h : ℝ => cellUlNorm univ (h⁻¹ • (L (Z h) - L Y) - L1))
      (𝓝[≠] 0) (𝓝 0) :=
    cellMetricJetFlux_derivative_tendsto (𝓝[≠] (0 : ℝ)) (fun h : ℝ => h⁻¹)
      (fun β h => Gj β (Z h)) (fun β => Gj β Y)
      (fun β h => cj β (Z h)) (fun β => cj β Y) α ε
      (fun β hb h => ⟨(hdata β (Nat.le_of_lt (hβ β hb)) (Z h)).1,
        (hdata β (Nat.le_of_lt (hβ β hb)) (Z h)).2.1⟩)
      (fun β hb => ⟨(hdata β (Nat.le_of_lt (hβ β hb)) Y).1,
        (hdata β (Nat.le_of_lt (hβ β hb)) Y).2.1⟩)
      (fun β hb => ⟨(hdata (β + ε) (hβnext β hb) Y).1,
        (hdata (β + ε) (hβnext β hb) Y).2.1⟩)
      (fun β hb => (hc _ (Nat.le_of_lt (hγ β hb)) Y).1)
      (fun β hb h => (hc _ (Nat.le_of_lt (hγ β hb)) (Z h)).2)
      (fun β hb => (hc _ (Nat.le_of_lt (hγ β hb)) Y).2)
      (fun β hb => (hc _ (hγnext β hb) Y).2)
      (fun β hb => normJetFamily_directional cellMetricSupNorm K Gj hGj β (hβ β hb) Y j)
      (fun β hb => (hcc _ (Nat.le_of_lt (hγ β hb)) Y).comp (cellParameterLine_tendsto Y j))
      hcd
  let R := fun W => Fj α W + L W
  let R1 := Fj (α + ε) Y + L1
  have hR W : cellUlNorm univ (R W) < ⊤ ∧ AEStronglyMeasurable (Function.uncurry (R W))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) :=
    ⟨(cellUlNorm_add univ _ _ (hdata α hαle W).2.2.2.2.2 (hflux α hαle W).2).trans_lt
      (ENNReal.add_lt_top.mpr ⟨(hdata α hαle W).2.2.2.1, (hflux α hαle W).1⟩),
      (hdata α hαle W).2.2.2.2.2.add (hflux α hαle W).2⟩
  have hR1 : cellUlNorm univ R1 < ⊤ ∧ AEStronglyMeasurable (Function.uncurry R1)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) :=
    ⟨(cellUlNorm_add univ _ _ (hdata (α + ε) hnext Y).2.2.2.2.2 hL1.2).trans_lt
      (ENNReal.add_lt_top.mpr ⟨(hdata (α + ε) hnext Y).2.2.2.1, hL1.1⟩),
      (hdata (α + ε) hnext Y).2.2.2.2.2.add hL1.2⟩
  have hRd : Tendsto (fun h : ℝ => cellUlNorm univ (h⁻¹ • (R (Z h) - R Y) - R1))
      (𝓝[≠] 0) (𝓝 0) := by
    have hs := cellUlNorm_add_tendsto (𝓝[≠] (0 : ℝ))
      (fun h : ℝ => h⁻¹ • (Fj α (Z h) - Fj α Y))
      (fun h : ℝ => h⁻¹ • (L (Z h) - L Y)) (Fj (α + ε) Y) L1
      (fun h => ((hdata α hαle (Z h)).2.2.2.2.2.sub (hdata α hαle Y).2.2.2.2.2).const_smul h⁻¹)
      (fun h => ((hflux α hαle (Z h)).2.sub (hflux α hαle Y).2).const_smul h⁻¹)
      (hdata (α + ε) hnext Y).2.2.2.2.2 hL1.2
      (normJetFamily_directional (cellUlNorm univ) K Fj hFj α hα Y j) hLd
    convert hs using 1
    funext h
    congr 1
    dsimp [R, R1]
    simp only [smul_add, smul_sub]
    abel
  have hT : IsCellInverseValue ⟨Gj 0 Y, v, 0, 0⟩
      (fun t => cellQ0 (fj (α + ε) Y t))
      (R1 + cellMetricFlux (Gj ε Y) (cj α Y)) (cj (α + ε) Y) := by
    have he := cellMetricJetFluxDerivative_add_principal
      (fun β => Gj β Y) (fun β => cj β Y) α j
    dsimp [R1, L1]
    rw [add_assoc, he]
    exact hsol Y (α + ε) hnext
  have hout := cellInverse_directional_derivative_identified
    (fun h => Gj 0 (Z h)) (fun h => fj α (Z h)) (fun h => R (Z h))
    (fun h => cj α (Z h)) hv (fun h => hG0 (Z h))
    (fun h => ⟨(hdata α hαle (Z h)).2.2.1, (hdata α hαle (Z h)).2.2.2.2.1⟩)
    (fun h => hR (Z h)) (fun h => hsol (Z h) α hαle)
    (Gj ε Y) (fj (α + ε) Y) R1
    ⟨(hdata ε heps Y).1, (hdata ε heps Y).2.1⟩
    ⟨(hdata (α + ε) hnext Y).2.2.1, (hdata (α + ε) hnext Y).2.2.2.2.1⟩ hR1
    (by simpa [Z, cellParameterLine, ε] using
      normJetFamily_directional cellMetricSupNorm K Gj hGj 0 (by change 0 + 0 < K; omega) Y j)
    (by simpa [Z, cellParameterLine] using normJetFamily_directional (cellUlNorm univ) K fj hfj α hα Y j)
    (by simpa [Z, cellParameterLine] using hRd)
    (by simpa [Z, cellParameterLine, Function.comp_def] using (hcc α hαle Y).comp (cellParameterLine_tendsto Y j))
    (cj (α + ε) Y) (by simpa [Z, cellParameterLine] using hT)
  simpa [Z, cellParameterLine, ε] using hout

/-! Every actual finite triangular cell-jet family has the full parameter norm-jet regularity. -/

/-- Actual inverse stability and strong induction prove all continuous directional derivatives. -/
theorem cellInverse_jetFamily_isNormJetFamily (K : ℕ)
    (Gj : ℕ × ℕ → (Fin 2 → ℝ) → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (fj : ℕ × ℕ → (Fin 2 → ℝ) → ℝ → Vec 2 → ℂ)
    (Fj : ℕ × ℕ → (Fin 2 → ℝ) → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (cj : ℕ × ℕ → (Fin 2 → ℝ) → ℝ → RawJet2 1 ℂ)
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
    (hGj : IsNormJetFamily cellMetricSupNorm K univ Gj)
    (hfj : IsNormJetFamily (cellUlNorm univ) K univ fj)
    (hFj : IsNormJetFamily (cellUlNorm univ) K univ Fj)
 :
    IsNormJetFamily (cellEnergyNorm univ) K univ cj := by
  have hc := cellInverse_jetFamily_continuous K Gj fj Fj cj hv hG0 hdata hsol
    (fun α ha Y => hGj.1 α ha Y (mem_univ Y))
    (fun α ha Y => hfj.1 α ha Y (mem_univ Y))
    (fun α ha Y => hFj.1 α ha Y (mem_univ Y))
  have hd (n : ℕ) : ∀ α : ℕ × ℕ, α.1 + α.2 = n → α.1 + α.2 < K →
      ∀ Y j, Tendsto (fun h : ℝ => cellEnergyNorm univ
        (h⁻¹ • (cj α (cellParameterLine Y j h) - cj α Y) -
          cj (α + cellJetDirection j) Y)) (𝓝[≠] 0) (𝓝 0) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro α he ha Y j
      apply cellInverse_jetFamily_derivative_step K Gj fj Fj cj hv hG0 hdata hsol
        hGj hfj hFj hc α ha Y j
      intro β hb
      have hl := cellJetFluxIndices_lower_order hb
      exact ih ((α.1 - β.1) + (α.2 - β.2)) (by omega)
        (α.1 - β.1, α.2 - β.2) rfl (hl.trans ha) Y j
  refine ⟨fun α ha Y _ => hc α ha Y, ?_⟩
  intro α ha Y _
  constructor
  · simpa [cellParameterLine, cellJetDirection, Prod.add_def] using
      hd (α.1 + α.2) α rfl ha Y (0 : Fin 2)
  · simpa [cellParameterLine, cellJetDirection, Prod.add_def] using
      hd (α.1 + α.2) α rfl ha Y (1 : Fin 2)

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! The actual infinite Taylor coefficient family satisfies its quantitative nonlinear recurrence. -/

/-- The actual coefficient energies have zero constant term. -/
theorem fibreCoefficientFamily_energy_zero (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) :
    cellEnergyNorm Set.univ (fibreCoefficientFamily η Cw hη G hG hv hw 0) = 0 := by
  rw [fibreCoefficientFamily_zero, cellEnergyNorm_zero]

/-- The actual constructed coefficients obey the complete quantitative triangular norm recurrence. -/
theorem fibreCoefficientFamily_energy_recurrence (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (p : ℕ × ℕ) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let E := fun a => cellEnergyNorm Set.univ (r a)
    E p ≤ 13 *
      ((∑ j ∈ fibreCoefficientDirections p, ENNReal.ofReal Cw *
        ((if p = cellJetDirection j then 1 else 0) + E (fibreCoefficientPrevious p j))) +
       (∑ j ∈ fibreCoefficientDirections p,
        ∑ a ∈ fibreCoefficientPairs (fibreCoefficientPrevious p j), ENNReal.ofReal Cw *
          E (fibreCoefficientComplement (fibreCoefficientPrevious p j) a) * E a) +
       (∑ j ∈ fibreCoefficientDirections p, 8 * E (fibreCoefficientPrevious p j))) := by
  let A := fun a : ℕ × ℕ => fibreCoefficientStage η Cw hη G hG hv hw (a.1 + a.2) a
  exact fibreCoefficient_inverse_energy_bound η Cw hη G hG hv hw A p
    (fibreCoefficientFamily η Cw hη G hG hv hw p)
    (fibreCoefficientFamily_isInverse η Cw hη G hG hv hw p)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.CycleEvolution

/-! Construction of actual parameter-differentiable cell inverse families from the given data jets. -/

/-- Actual triangular inversion supplies a norm-jet family solving all literal jet equations. -/
theorem cellInverse_normJetFamily_exists (K : ℕ)
    (Gj : ℕ × ℕ → (Fin 2 → ℝ) → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (fj : ℕ × ℕ → (Fin 2 → ℝ) → ℝ → Vec 2 → ℂ)
    (Fj : ℕ × ℕ → (Fin 2 → ℝ) → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hG0 : ∀ Y, IsCellMetric (Gj 0 Y))
    (hdata : ∀ α : ℕ × ℕ, α.1 + α.2 ≤ K → ∀ Y,
      cellMetricSupNorm (Gj α Y) < ⊤ ∧ Measurable (Function.uncurry (Gj α Y)) ∧
      cellUlNorm univ (fj α Y) < ⊤ ∧ cellUlNorm univ (Fj α Y) < ⊤ ∧
      AEStronglyMeasurable (Function.uncurry (fj α Y))
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) ∧
      AEStronglyMeasurable (Function.uncurry (Fj α Y))
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hGj : IsNormJetFamily cellMetricSupNorm K univ Gj)
    (hfj : IsNormJetFamily (cellUlNorm univ) K univ fj)
    (hFj : IsNormJetFamily (cellUlNorm univ) K univ Fj)
 :
    ∃ cj : ℕ × ℕ → (Fin 2 → ℝ) → ℝ → RawJet2 1 ℂ,
      IsNormJetFamily (cellEnergyNorm univ) K univ cj ∧
      ∀ Y, ∀ α : ℕ × ℕ, α.1 + α.2 ≤ K →
        IsCellInverseValue ⟨Gj 0 Y, v, 0, 0⟩ (fun t => cellQ0 (fj α Y t))
          (Fj α Y + cellMetricJetFlux (fun β => Gj β Y) (fun β => cj β Y) α) (cj α Y) := by
  obtain ⟨cj, hsol⟩ := cellInverse_parameterJetFamily_exists K Gj fj Fj hG0 hv hdata
  exact ⟨cj, cellInverse_jetFamily_isNormJetFamily K Gj fj Fj cj hv hG0 hdata hsol hGj hfj hFj,
    hsol⟩

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Reality of every actual constructed inverse coefficient follows from the genuine recurrence and uniqueness. -/

theorem fibreCoefficientFamily_reality (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) :
    ∀ p t, (fun x => star (cellValue (fibreCoefficientFamily η Cw hη G hG hv hw p) t x)) =ᵐ[
      volume.restrict AVenhance.unitCube]
      (fun x => fibreRealitySign p * cellValue (fibreCoefficientFamily η Cw hη G hG hv hw p) t x) :=
  fibreCoefficient_inverse_reality η G hG hv _
    (fibreCoefficientFamily_isInverse η Cw hη G hG hv hw)

/-! The actual scalar symbol has minus-conjugate coefficient reality at every time. -/

theorem fibreCoefficientDriftSymbol_reality (η : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ)
    (hr : ∀ p t, (fun x => star (cellValue (r p) t x)) =ᵐ[volume.restrict AVenhance.unitCube]
      (fun x => fibreRealitySign p * cellValue (r p) t x)) (p : ℕ × ℕ) (t : ℝ) :
    star (fibreCoefficientDriftSymbol η v r p t) =
      fibreRealitySign p * fibreCoefficientDriftSymbol η v r p t := by
  simp only [fibreCoefficientDriftSymbol, star_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hm := fibreCoordinateFrequency_mean_reality η v j t
    (fibreRealitySign (fibreCoefficientPrevious p j)) (cellValue (r (fibreCoefficientPrevious p j)) t)
    (hr _ t)
  rw [star_mul, star_neg, show star Complex.I = -Complex.I from Complex.conj_I,
    hm, fibreRealitySign_previous hj]
  ring

theorem fibreCoefficientSymbol_reality (η : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ)
    (hr : ∀ p t, (fun x => star (cellValue (r p) t x)) =ᵐ[volume.restrict AVenhance.unitCube]
      (fun x => fibreRealitySign p * cellValue (r p) t x)) (p : ℕ × ℕ) (t : ℝ) :
    star (fibreCoefficientSymbol η G v r p t) =
      fibreRealitySign p * fibreCoefficientSymbol η G v r p t := by
  rw [fibreCoefficientSymbol, star_add, fibreCoefficientMetricSymbol_reality,
    fibreCoefficientDriftSymbol_reality η v r hr]
  ring

theorem fibreCoefficientFamily_symbol_reality (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) (p : ℕ × ℕ) (t : ℝ) :
    star (fibreCoefficientSymbol η G v (fibreCoefficientFamily η Cw hη G hG hv hw) p t) =
      fibreRealitySign p * fibreCoefficientSymbol η G v (fibreCoefficientFamily η Cw hη G hG hv hw) p t :=
  fibreCoefficientSymbol_reality η G v _ (fibreCoefficientFamily_reality η Cw hη G hG hv hw) p t

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! Summability of the actual recursively constructed fibre graph coefficients. -/

/-- The actual coefficient family has weighted total energy at most one at the explicit radius. -/
theorem fibreCoefficientFamily_weighted_energy_le (η Cw : ℝ) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) :
    (∑' p, fibreCoefficientWeight (ENNReal.ofReal (fibreCoefficientMajorantRadius Cw)) p *
      cellEnergyNorm Set.univ (fibreCoefficientFamily η Cw hη G hG hv hw p)) ≤ 1 := by
  let E := fun p => cellEnergyNorm Set.univ (fibreCoefficientFamily η Cw hη G hG hv hw p)
  let ρ := ENNReal.ofReal (fibreCoefficientMajorantRadius Cw)
  have hzero : fibreCoefficientWeightedPrefix ρ E 0 = 0 := by
    unfold fibreCoefficientWeightedPrefix
    apply Finset.sum_eq_zero
    intro p hp
    have ho := (mem_jetIndices_iff 0 p).mp hp
    have he : p = 0 := by apply Prod.ext <;> simp only [Prod.fst_zero, Prod.snd_zero] <;> omega
    rw [he]
    have hz : E 0 = 0 := fibreCoefficientFamily_energy_zero η Cw hη G hG hv hw
    rw [hz, mul_zero]
  apply fibreCoefficient_weighted_total_le
  exact fibreCoefficient_prefix_majorant ρ (ENNReal.ofReal Cw)
    (fibreCoefficientWeightedPrefix ρ E) hzero
    (fibreCoefficient_weighted_prefix_recurrence ρ (ENNReal.ofReal Cw) E
      (fibreCoefficientFamily_energy_recurrence η Cw hη G hG hv hw))
    (fibreCoefficientMajorantRadius_small hCw)

end AVRegularity.CycleEvolution
end
