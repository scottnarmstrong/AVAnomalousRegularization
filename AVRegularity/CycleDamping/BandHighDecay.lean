-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleDamping.ReferenceJetRegularity
import AVRegularity.CycleEvolution.CellInverseJetFactorialBound
public import AVRegularity.CycleEvolution.FibreCoefficientFamilyMajorant
import AVRegularity.CycleEvolution.CellEnergySpaceRawJetCauchyBound
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.CycleReference.ChartTestTransport

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleDamping

/-! The integrated weak identity of the actual reference corrector. -/

theorem referenceWeakRhs_time_integrable {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (B s t : ℝ) (y₀ : Vec 2) (j : Fin 2) (ψ : TorusHkFunction 1 ℂ) :
    IntegrableOn (fun τ => ∫ x in AVenhance.unitCube,
      referenceWeakRhs α q Λ ζ m ν B y₀ j ψ τ x) (Set.Ioc s t) := by
  simp_rw [referenceWeakRhs_pair hΛ hζ hν, cellReferenceValue_deriv_mode hΛ hζ,
    Complex.ofReal_mul, mul_assoc, integral_const_mul]
  apply Continuous.integrableOn_Ioc
  exact (Complex.continuous_ofReal.comp
    (cellReferenceAmplitude_contDiff_one hΛ hζ ν B j).continuous_deriv_one).mul
      continuous_const

theorem referenceWeak_time_identity {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (B : ℝ) {s t : ℝ} (hst : s ≤ t) (y₀ : Vec 2) (j : Fin 2)
    (ψ : TorusHkFunction 1 ℂ) :
    (∫ x in AVenhance.unitCube,
      cellValue (cellReferenceJet α q Λ ζ m ν B y₀ j) t x * ψ.jet (valueIndex2 1) x) -
    (∫ x in AVenhance.unitCube,
      cellValue (cellReferenceJet α q Λ ζ m ν B y₀ j) s x * ψ.jet (valueIndex2 1) x) =
    ∫ τ in Set.Ioc s t, ∫ x in AVenhance.unitCube,
      referenceWeakRhs α q Λ ζ m ν B y₀ j ψ τ x := by
  simp_rw [cellReferenceJet_value, referenceWeakRhs_pair hΛ hζ hν,
    cellReferenceValue_deriv_mode hΛ hζ, cellReferenceValue_single_mode hΛ,
    Complex.ofReal_mul]
  exact scalar_mode_time_integral _
    (cellReferenceAmplitude_contDiff_one hΛ hζ ν B j) _ _ hst

/-! The integrated weak predicate for the actual normalized reference corrector. -/

theorem cellReferenceJet_weak_identity {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (B : ℝ) {s t : ℝ} (hst : s ≤ t) (y₀ : Vec 2) (j : Fin 2)
    (ψ : TorusHkFunction 1 ℂ) :
    CellWeakIdentity ⟨fun _ _ => 1, ocCellDrift α q Λ ζ m ν y₀, 0, 0⟩ s t
      (cellValue (cellReferenceJet α q Λ ζ m ν B y₀ j) s)
      (cellValue (cellReferenceJet α q Λ ζ m ν B y₀ j) t)
      (ψ.jet (valueIndex2 1)) (fun i => ψ.jet ⟨⟨1, by decide⟩, fun _ => i⟩)
      (cellValue (cellReferenceJet α q Λ ζ m ν B y₀ j))
      (fun τ i => cellGradComp (cellReferenceJet α q Λ ζ m ν B y₀ j τ) i)
      (fun τ x => ((Real.sqrt (ν / B) * ocCellDrift α q Λ ζ m ν y₀ τ x j +
        cellSwitchResidual α q Λ ζ m ν B y₀ τ x j : ℝ) : ℂ)) (fun _ _ => 0) := by
  have he (τ : ℝ) (x : Vec 2) :
      -(∑ i : Fin 2, ∑ k : Fin 2, ((1 : Matrix (Fin 2) (Fin 2) ℝ) i k : ℂ) *
          cellGradComp (cellReferenceJet α q Λ ζ m ν B y₀ j τ) i x *
            ψ.jet ⟨⟨1, by decide⟩, fun _ => k⟩ x) -
        (∑ k : Fin 2, (ocCellDrift α q Λ ζ m ν y₀ τ x k : ℂ) *
          cellGradComp (cellReferenceJet α q Λ ζ m ν B y₀ j τ) k x *
            ψ.jet (valueIndex2 1) x) +
        ((Real.sqrt (ν / B) * ocCellDrift α q Λ ζ m ν y₀ τ x j +
          cellSwitchResidual α q Λ ζ m ν B y₀ τ x j : ℝ) : ℂ) *
            ψ.jet (valueIndex2 1) x =
      referenceWeakRhs α q Λ ζ m ν B y₀ j ψ τ x := by
    have hz := congrArg (fun r : ℝ => (r : ℂ))
      (cellReferenceValue_transport_zero (α := α) (q := q) (m := m) hΛ hζ ν B τ y₀ x j)
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_zero] at hz
    simp only [cellReferenceJet_grad]
    rw [← Finset.sum_mul, hz, zero_mul, sub_zero]
    simp only [referenceWeakRhs, cellReferenceJet_grad, Fin.sum_univ_two, Matrix.one_apply]
    norm_num
  unfold CellWeakIdentity
  simp only [WithLp.ofLp_zero, Pi.zero_apply, mul_zero, zero_mul, add_zero, sub_zero, Finset.sum_const_zero]
  simp_rw [he]
  refine ⟨?_, ?_, Filter.Eventually.of_forall (fun τ =>
    referenceWeakRhs_integrable hΛ hζ hν B τ y₀ j ψ),
    referenceWeakRhs_time_integrable hΛ hζ hν B s t y₀ j ψ,
    referenceWeak_time_identity hΛ hζ hν B hst y₀ j ψ⟩
  · exact memLp_one_iff_integrable.mp
      ((cellReferenceJet_value_memLp hΛ ν B t y₀ j).mul
        (ψ.hasPeriodicWeakJet.2.1 (valueIndex2 1)) : MemLp _ 1 _)
  · exact memLp_one_iff_integrable.mp
      ((cellReferenceJet_value_memLp hΛ ν B s y₀ j).mul
        (ψ.hasPeriodicWeakJet.2.1 (valueIndex2 1)) : MemLp _ 1 _)

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.CycleDamping

/-! The actual reference corrector is an all-time energy solution. -/

theorem cellReferenceJet_isCellSolution {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (B : ℝ) (y₀ : Vec 2) (j : Fin 2) :
    IsCellSolution Set.univ
      ⟨fun _ _ => 1, ocCellDrift α q Λ ζ m ν y₀, 0, 0⟩
      (fun τ x => ((Real.sqrt (ν / B) * ocCellDrift α q Λ ζ m ν y₀ τ x j +
        cellSwitchResidual α q Λ ζ m ν B y₀ τ x j : ℝ) : ℂ)) (fun _ _ => 0)
      (cellReferenceJet α q Λ ζ m ν B y₀ j) := by
  refine ⟨Set.ordConnected_univ,
    Filter.Eventually.of_forall (fun t => cellReferenceJet_periodicWeak hΛ ν B t y₀ j),
    (fun t _ => ⟨cellReferenceJet_value_memLp hΛ ν B t y₀ j,
      cellReferenceJet_value_periodic hΛ ν B t y₀ j⟩), ?_, ?_, ?_, ?_⟩
  · intro a
    exact (cellReferenceJet_joint_continuous hΛ hζ ν B y₀ j a).aestronglyMeasurable
  · intro t₀ ht₀
    simpa only [nhdsWithin_univ] using
      cellReferenceJet_trace_continuous hΛ hζ ν B y₀ j t₀
  · intro a ha b hb
    exact cellReferenceJet_gradient_energy_finite hΛ hζ ν B y₀ j a b
  · intro s hs t ht hst ψ
    exact cellReferenceJet_weak_identity hΛ hζ hν B hst y₀ j ψ

end AVRegularity.CycleDamping
end

section
open Homogenization
namespace AVRegularity.CycleDamping

/-! The reference corrector is the genuine bounded inverse of the switching-corrected source. -/

theorem cellReferenceJet_isCellInverse {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (hrelax : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m) (y₀ : Vec 2) (j : Fin 2) :
    IsCellInverseValue
      ⟨fun _ _ => 1, ocCellDrift α q Λ ζ m ν y₀, 0, 0⟩
      (fun τ x => ((Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
        ocCellDrift α q Λ ζ m ν y₀ τ x j +
        cellSwitchResidual α q Λ ζ m ν (ocMeanFlux α q Λ ζ m ν) y₀ τ x j : ℝ) : ℂ))
      (fun _ _ => 0)
      (cellReferenceJet α q Λ ζ m ν (ocMeanFlux α q Λ ζ m ν) y₀ j) :=
  ⟨cellReferenceJet_isCellSolution hΛ hζ hν _ y₀ j,
    (fun t => cellReferenceJet_mean_zero hΛ _ _ t y₀ j),
    cellReferenceJet_energy_finite hΛ hζ hν hrelax y₀ j⟩

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleDamping

/-! Bounded multiplier means of actual cell inverses are locally time integrable. -/

theorem inverse_multiplier_mean_intervalIntegrable
    (b : ℝ → Vec 2 → ℂ) (W : ℝ) (hW : 0 ≤ W)
    (hb : Measurable (Function.uncurry b)) (hbound : ∀ t x, ‖b t x‖ ≤ W)
    {C : CellCoefficients} {src : ℝ → Vec 2 → ℂ}
    {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {D : ℝ → RawJet2 1 ℂ}
    (hD : IsCellInverseValue C src F D) (a c : ℝ) :
    IntervalIntegrable (fun t => cellMean (fun x => b t x * cellValue D t x)) volume a c := by
  have hp : AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2 * cellValue D p.1 p.2)
      ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)) :=
    hb.aestronglyMeasurable.mul (hD.1.2.2.2.1 (valueIndex2 1))
  have hm := CycleEvolution.cellMean_aestronglyMeasurable (I := Set.univ)
    (f := fun t x => b t x * cellValue D t x) hp
  have hm' : AEStronglyMeasurable (fun t => cellMean (fun x => b t x * cellValue D t x)) volume := by
    simpa only [Measure.restrict_univ] using hm
  have hfinite : ENNReal.ofReal W * cellEnergyNorm Set.univ D ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hD.2.2.ne
  have hbnd (t : ℝ) : ‖cellMean (fun x => b t x * cellValue D t x)‖ ≤
      W * (cellEnergyNorm Set.univ D).toReal := by
    have hh := ENNReal.toReal_mono hfinite
      (CycleEvolution.cellBoundedMean_energy_bound b W hb hbound hD.1 t)
    simpa only [toReal_enorm, ENNReal.toReal_mul, ENNReal.toReal_ofReal hW] using hh
  apply intervalIntegrable_iff.mpr
  apply Measure.integrableOn_of_bounded (M := W * (cellEnergyNorm Set.univ D).toReal)
  · exact (measure_Ioc_lt_top (a := min a c) (b := max a c)).ne
  · exact hm'
  · exact Filter.Eventually.of_forall hbnd

end AVRegularity.CycleDamping
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping

/-! The actual complete-core shear yields uniform half-norm decay at small contrast. -/

theorem small_contrast_core_contraction_time (ξlo : ℝ) (hlo : 0 < ξlo) :
    ∃ d : ℝ, 0 < d ∧ ∀ (α q : ℝ) (Λ m : ℕ) (ζ : ℝ → ℝ),
      1 ≤ Λ → IsFastProfile ζ → ∀ ν : ℝ, 0 < ν →
      6 ≤ ocMu q Λ m ν * ocTau α q Λ m →
      ν / ocMeanFlux α q Λ ζ m ν ≤ 1 / 2 →
      ∀ (y₀ : Vec 2) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
        (hG : IsCellMetric (fun t _ => G t))
        (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀)) (V : ℝ)
        (hb : ∀ t x, ∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2 ≤ V ^ 2)
        (ξ : Vec 2), (∀ i, |Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) * ξ i| ≤ Real.pi) →
      ∀ j : Fin 2, ξlo / 2 ≤ |ξ j| →
      ∀ (a b : ℝ), a ≤ b → d ≤ b - a →
      ∀ (l n : ℤ), IsOCCompleteCore α q Λ m l n →
      n % 4 = (if j = 0 then 3 else 1) →
      (∀ t ∈ Icc a b, ocEll q Λ m ν ^ 2 * t ∈
        Icc (((n : ℝ) - 1 / 3) * ocTau α q Λ m) (((n : ℝ) + 1 / 3) * ocTau α q Λ m)) →
      ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ),
        CellWeakHilbertCurve a b u slice (fun t => cellDualDerivative
          ⟨fun s _ => G s, ocCellDrift α q Λ ζ m ν y₀,
            fun i => ((Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) * ξ i : ℝ) : ℂ), 0⟩
          hG V hv.1 hb t (slice t) 0 0) →
        ‖u b‖ ≤ (1 / 2 : ℝ) * ‖u a‖ := by
  obtain ⟨d, hd, hdrop⟩ := uniform_stationary_shear_contraction (Real.pi * ξlo) (mul_pos Real.pi_pos hlo)
  refine ⟨d, hd, ?_⟩
  intro α q Λ m ζ hΛ hζ ν hν hr hη y₀ G hG hv V hb ξ hθ j hj a b hab hlong l n hcore hn hinside u slice h
  let θ : Vec 2 := fun i => Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) * ξ i
  let A : ℝ := (if j = 0 then -1 else 1) * (2 * Real.pi * ocA α q Λ m * ocEll q Λ m ν ^ 2)
  have hkj : j ≠ 1 - j := by fin_cases j <;> norm_num
  have hcouple : Real.pi * ξlo ≤ |A * θ j| := by
    have he := constructed_shear_coupling_lower hΛ hζ hν hr hη (ξ j) ξlo hj
    dsimp only [A, θ]
    fin_cases j <;> norm_num at he ⊢ <;> simpa only [neg_mul, abs_neg] using he
  have hprofile : ∀ t ∈ Icc a b, ∀ x i,
      ocCellDrift α q Λ ζ m ν y₀ t x i =
        if i = j then A * cellCosine (1 - j) (y₀ (1 - j) / ocEpsilon q Λ m) x else 0 := by
    intro t ht x i
    exact ocCellDrift_on_oriented_core hΛ hζ ν y₀ j l n hcore hn t (hinside t ht) x i
  exact hdrop a b hab hlong G hG (ocCellDrift α q Λ ζ m ν y₀) hv V hb θ hθ
    (1 - j) j hkj (y₀ (1 - j) / ocEpsilon q Λ m) A hcouple hprofile u slice h

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleDamping

/-! The actual corrector bridge is locally integrable in cell time. -/

theorem metric_time_entry_intervalIntegrable
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric (fun t _ => G t))
    (i j : Fin 2) (a b : ℝ) : IntervalIntegrable (fun t => (G t i j : ℂ)) volume a b := by
  have hm : Measurable (fun t => G t i j) :=
    (CycleEvolution.cellMetric_entry_measurable hG i j).comp
      (measurable_id.prodMk (measurable_const (a := (0 : Vec 2))))
  apply intervalIntegrable_iff.mpr
  apply Measure.integrableOn_of_bounded (M := 2)
  · exact (measure_Ioc_lt_top (a := min a b) (b := max a b)).ne
  · exact (Complex.continuous_ofReal.measurable.comp hm).aestronglyMeasurable
  · filter_upwards [] with t
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact CycleEvolution.cellMetric_entry_bound hG t 0 i j

theorem bridge_entry_intervalIntegrable (η W : ℝ) (hW : 0 ≤ W)
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2)
    (hm : ∀ j, Measurable (fun p : ℝ × Vec 2 => ((Real.sqrt η * v p.1 p.2 j : ℝ) : ℂ)))
    (hw : ∀ t x j, ‖((Real.sqrt η * v t x j : ℝ) : ℂ)‖ ≤ W)
    (χ : Fin 2 → ℝ → RawJet2 1 ℂ)
    (hχ : ∀ j, IsCellInverseValue ⟨fun t _ => G t, v, 0, 0⟩
      (fun t => cellQ0 (fun x => ((Real.sqrt η * v t x j : ℝ) : ℂ))) (fun _ _ => 0) (χ j))
    (i j : Fin 2) (a b : ℝ) :
    IntervalIntegrable (fun t => fibreBridgeMatrix η G v χ t i j) volume a b := by
  have hij := inverse_multiplier_mean_intervalIntegrable
    (fun t x => ((Real.sqrt η * v t x i : ℝ) : ℂ)) W hW (hm i)
    (fun t x => hw t x i) (hχ j) a b
  have hji := inverse_multiplier_mean_intervalIntegrable
    (fun t x => ((Real.sqrt η * v t x j : ℝ) : ℂ)) W hW (hm j)
    (fun t x => hw t x j) (hχ i) a b
  exact ((metric_time_entry_intervalIntegrable hG i j a b).const_mul (η : ℂ)).add
    ((hij.add hji).const_mul (1 / 2 : ℂ))

theorem bridge_quadratic_intervalIntegrable (η W : ℝ) (hW : 0 ≤ W)
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2)
    (hm : ∀ j, Measurable (fun p : ℝ × Vec 2 => ((Real.sqrt η * v p.1 p.2 j : ℝ) : ℂ)))
    (hw : ∀ t x j, ‖((Real.sqrt η * v t x j : ℝ) : ℂ)‖ ≤ W)
    (χ : Fin 2 → ℝ → RawJet2 1 ℂ)
    (hχ : ∀ j, IsCellInverseValue ⟨fun t _ => G t, v, 0, 0⟩
      (fun t => cellQ0 (fun x => ((Real.sqrt η * v t x j : ℝ) : ℂ))) (fun _ _ => 0) (χ j))
    (ξ : Fin 2 → ℂ) (a b : ℝ) :
    IntervalIntegrable (fun t => -(∑ i, ∑ j,
      ξ i * fibreBridgeMatrix η G v χ t i j * ξ j)) volume a b := by
  have hi (i j : Fin 2) := ((bridge_entry_intervalIntegrable η W hW hG v hm hw χ hχ i j a b).const_mul (ξ i)).mul_const (ξ j)
  simpa only [Fin.sum_univ_two, Pi.neg_def] using
    (((hi 0 0).add (hi 0 1)).add ((hi 1 0).add (hi 1 1))).neg

end AVRegularity.CycleDamping
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping

/-! A common complete-core contraction time for every molecular contrast. -/

theorem complete_core_contraction_time (ξlo : ℝ) (hlo : 0 < ξlo) :
    ∃ d : ℝ, 0 < d ∧ ∀ (α q : ℝ) (Λ m : ℕ) (ζ : ℝ → ℝ),
      1 ≤ Λ → IsFastProfile ζ → ∀ ν : ℝ, 0 < ν →
      6 ≤ ocMu q Λ m ν * ocTau α q Λ m →
      ∀ (y₀ : Vec 2) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
        (hG : IsCellMetric (fun t _ => G t))
        (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀)) (V : ℝ)
        (hb : ∀ t x, ∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2 ≤ V ^ 2)
        (ξ : Vec 2), (∀ i, |Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) * ξ i| ≤ Real.pi) →
      ξlo ≤ Real.sqrt (∑ i : Fin 2, ξ i ^ 2) →
      ∀ j : Fin 2, ξlo / 2 ≤ |ξ j| →
      ∀ (a b : ℝ), a ≤ b → d ≤ b - a →
      ∀ (l n : ℤ), IsOCCompleteCore α q Λ m l n →
      n % 4 = (if j = 0 then 3 else 1) →
      (∀ t ∈ Icc a b, ocEll q Λ m ν ^ 2 * t ∈
        Icc (((n : ℝ) - 1 / 3) * ocTau α q Λ m) (((n : ℝ) + 1 / 3) * ocTau α q Λ m)) →
      ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ),
        CellWeakHilbertCurve a b u slice (fun t => cellDualDerivative
          ⟨fun s _ => G s, ocCellDrift α q Λ ζ m ν y₀,
            fun i => ((Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) * ξ i : ℝ) : ℂ), 0⟩
          hG V hv.1 hb t (slice t) 0 0) →
        ‖u b‖ ≤ (1 / 2 : ℝ) * ‖u a‖ := by
  obtain ⟨ds, hds, hs⟩ := small_contrast_core_contraction_time ξlo hlo
  obtain ⟨dm, hdm, hm⟩ := molecular_contraction_time ξlo hlo
  refine ⟨max ds dm, lt_of_lt_of_le hds (le_max_left _ _), ?_⟩
  intro α q Λ m ζ hΛ hζ ν hν hr y₀ G hG hv V hb ξ hθ hξ j hj a b hab hlong l n hcore hn hinside u slice h
  by_cases hη : ν / ocMeanFlux α q Λ ζ m ν ≤ 1 / 2
  · exact hs α q Λ m ζ hΛ hζ ν hν hr hη y₀ G hG hv V hb ξ hθ j hj a b hab
      ((le_max_left ds dm).trans hlong) l n hcore hn hinside u slice h
  · exact hm (ν / ocMeanFlux α q Λ ζ m ν) (le_of_lt (lt_of_not_ge hη)) ξ hθ hξ a b hab
      ((le_max_right ds dm).trans hlong) (fun t _ => G t) hG
      (ocCellDrift α q Λ ζ m ν y₀) hv V hb u slice h

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleDamping

/-! A quantitative bridge estimate in terms of actual corrector trace errors. -/

section
local instance bridgeDifferenceProbCube : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using CycleEvolution.cellCube_volume_one⟩

theorem mean_multiplier_difference_bound (b f h : Vec 2 → ℂ) (W : ℝ)
    (hb : Measurable b) (hW : ∀ x, ‖b x‖ ≤ W)
    (hf : MemLp f 2 (volume.restrict AVenhance.unitCube))
    (hh : MemLp h 2 (volume.restrict AVenhance.unitCube)) :
    ‖cellMean (fun x => b x * f x) - cellMean (fun x => b x * h x)‖ₑ ≤
      ENNReal.ofReal W * cellL2Norm (f - h) := by
  have hbf := CycleEvolution.cellMultiplier_memLp b f W hb hW hf
  have hbh := CycleEvolution.cellMultiplier_memLp b h W hb hW hh
  have he : cellMean (fun x => b x * f x) - cellMean (fun x => b x * h x) =
      cellMean (fun x => b x * (f - h) x) := by
    simp only [Pi.sub_apply, mul_sub]
    exact (integral_sub (hbf.integrable (by norm_num))
      (hbh.integrable (by norm_num))).symm
  rw [he]
  have hp := CycleEvolution.cellMultiplier_memLp b (f - h) W hb hW (hf.sub hh)
  exact (CycleEvolution.cellMean_enorm_le_cellL2Norm _ hp).trans
    (CycleEvolution.cellL2Norm_mul_le b (f - h) W hp.aestronglyMeasurable
      (Filter.Eventually.of_forall hW))
end

/-! Entrywise bridge stability from actual corrector trace distances. -/

theorem bridge_entry_difference_bound (η g W A : ℝ) (hη₀ : 0 ≤ η) (hη₁ : η ≤ 1)
    (hg : 0 ≤ g) (hW : 0 ≤ W) (hA : 0 ≤ A)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (χ Ψ : Fin 2 → ℝ → RawJet2 1 ℂ) (t : ℝ)
    (hG : ∀ i j, |G t i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ g)
    (hvm : ∀ i, Measurable (fun x => ((Real.sqrt η * v t x i : ℝ) : ℂ)))
    (hv : ∀ i x, ‖((Real.sqrt η * v t x i : ℝ) : ℂ)‖ ≤ W)
    (hχ : ∀ j, MemLp (cellValue (χ j) t) 2 (volume.restrict AVenhance.unitCube))
    (hΨ : ∀ j, MemLp (cellValue (Ψ j) t) 2 (volume.restrict AVenhance.unitCube))
    (he : ∀ j, cellL2Norm (cellValue (Ψ j) t - cellValue (χ j) t) ≤ ENNReal.ofReal A)
    (i j : Fin 2) :
    ‖fibreBridgeMatrix η G v χ t i j - fibreBridgeMatrix η (fun _ => 1) v Ψ t i j‖ ≤
      g + W * A := by
  let M (u : Fin 2 → ℝ → RawJet2 1 ℂ) (a b : Fin 2) :=
    cellMean (fun x => ((Real.sqrt η * v t x a : ℝ) : ℂ) * cellValue (u b) t x)
  have hm (a b : Fin 2) : ‖M χ a b - M Ψ a b‖ ≤ W * A := by
    have hh := mean_multiplier_difference_bound
      (fun x => ((Real.sqrt η * v t x a : ℝ) : ℂ))
      (cellValue (Ψ b) t) (cellValue (χ b) t) W (hvm a) (hv a) (hΨ b) (hχ b)
    have hb : ‖M Ψ a b - M χ a b‖ₑ ≤ ENNReal.ofReal W * ENNReal.ofReal A := by
      apply hh.trans
      gcongr
      exact he b
    rw [← ofReal_norm, ← ENNReal.ofReal_mul hW] at hb
    have hr := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hW hA)).mp hb
    simpa only [norm_sub_rev] using hr
  have hmetric : ‖(η : ℂ) * ((G t i j : ℂ) - ((1 : Matrix (Fin 2) (Fin 2) ℝ) i j : ℂ))‖ ≤ g := by
    rw [← Complex.ofReal_sub, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hη₀]
    exact (mul_le_mul_of_nonneg_left (hG i j) hη₀).trans
      ((mul_le_mul_of_nonneg_right hη₁ hg).trans_eq (one_mul g))
  have halg : fibreBridgeMatrix η G v χ t i j - fibreBridgeMatrix η (fun _ => 1) v Ψ t i j =
      (η : ℂ) * ((G t i j : ℂ) - ((1 : Matrix (Fin 2) (Fin 2) ℝ) i j : ℂ)) +
        (1 / 2 : ℂ) * ((M χ i j - M Ψ i j) + (M χ j i - M Ψ j i)) := by
    unfold fibreBridgeMatrix M
    ring
  rw [halg]
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ g + (1 / 2 : ℝ) * (W * A + W * A) := by
      apply add_le_add hmetric
      rw [norm_mul, norm_div, norm_one, Complex.norm_ofNat]
      exact mul_le_mul_of_nonneg_left
        ((norm_add_le _ _).trans (add_le_add (hm i j) (hm j i))) (by norm_num)
    _ = _ := by ring

end AVRegularity.CycleDamping
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleDamping

/-! Exponential high-frequency decay for genuine weak traces on admissible constructed intervals. -/

theorem admissible_weak_high_decay (ξlo : ℝ) (hlo : 0 < ξlo) :
    ∃ d c : ℝ, 0 < d ∧ 0 < c ∧ ∀ (α q : ℝ) (Λ m : ℕ) (ζ : ℝ → ℝ),
      1 ≤ Λ → IsFastProfile ζ → ∀ ν : ℝ, 0 < ν →
      6 ≤ ocMu q Λ m ν * ocTau α q Λ m →
      ∀ (y₀ : Vec 2) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
        (hG : IsCellMetric (fun t _ => G t))
        (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀)) (V : ℝ)
        (hb : ∀ t x, ∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2 ≤ V ^ 2)
        (ξ : Vec 2), (∀ i, |Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) * ξ i| ≤ Real.pi) →
      ξlo ≤ Real.sqrt (∑ i : Fin 2, ξ i ^ 2) →
      ∀ Θ ta T : ℝ, 1 ≤ Θ →
      IsOCAdmissibleInterval α q Λ ζ m ν (ocMeanFlux α q Λ ζ m ν) Θ d ta T →
      ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ),
        CellWeakHilbertCurve (ta / ocEll q Λ m ν ^ 2) ((ta + T) / ocEll q Λ m ν ^ 2) u slice
          (fun t => cellDualDerivative
            ⟨fun s _ => G s, ocCellDrift α q Λ ζ m ν y₀,
              fun i => ((Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) * ξ i : ℝ) : ℂ), 0⟩
            hG V hv.1 hb t (slice t) 0 0) →
        ENNReal.ofReal ‖u ((ta + T) / ocEll q Λ m ν ^ 2)‖ ≤
          ENNReal.ofReal (Real.exp (-c * (T / ocEll q Λ m ν ^ 2))) *
            ENNReal.ofReal ‖u (ta / ocEll q Λ m ν ^ 2)‖ := by
  obtain ⟨d, hd, hdrop⟩ := complete_core_contraction_time ξlo hlo
  let c : ℝ := ((1 - Real.exp (-2)) / 288) * Real.log 2 / d
  have hc : 0 < c := by
    have he : Real.exp (-2) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
    dsimp [c]
    positivity
  refine ⟨d, c, hd, hc, ?_⟩
  intro α q Λ m ζ hΛ hζ ν hν hr y₀ G hG hv V hb ξ hθ hξ Θ ta T hΘ hadm u slice h
  let L : ℝ := ocEll q Λ m ν ^ 2
  let θ : Vec 2 := fun i => Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) * ξ i
  have hL : 0 < L := by
    dsimp [L]
    rw [CycleReference.ocEll_sq_eq hν]
    have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
    positivity
  have hj : ∃ j : Fin 2, ξlo / 2 ≤ |ξ j| := by
    rcases real_frequency_large_coordinate ξ ξlo hlo hξ with h0 | h1
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
  obtain ⟨j, hj⟩ := hj
  let N : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal ‖u (t / L)‖
  have hN : AntitoneOn N (Icc ta (ta + T)) := physical_norm_antitone L ta (ta + T) hL u
    (real_shift_weak_norm_antitone hG (ocCellDrift α q Λ ζ m ν y₀) hv V hb θ h)
  change N (ta + T) ≤ ENNReal.ofReal (Real.exp (-c * (T / L))) * N ta
  apply admissible_decay_of_core_drops ν (ocMeanFlux α q Λ ζ m ν) Θ d ta T hd hΘ hL hadm N hN j
  intro x hxa hxb n hn hcore hca hcb
  have hlen := scaled_mark_length L x d hL
  have hab : x / L ≤ (x + d * L) / L := by linarith only [hlen, hd]
  have hh := h.mono (scaled_mark_interval_subset L ta (ta + T) x d hL hxa hxb)
  have he := hdrop α q Λ m ζ hΛ hζ ν hν hr y₀ G hG hv V hb ξ hθ hξ j hj
    (x / L) ((x + d * L) / L) hab (by rw [hlen]) (ocLabel α q Λ m n) n hcore hn
    (scaled_mark_inside_core L x d _ _ hL hca hcb) u slice hh
  change ENNReal.ofReal ‖u ((x + d * L) / L)‖ ≤ (1 / 2 : ℝ≥0∞) * ENNReal.ofReal ‖u (x / L)‖
  rw [← ofReal_half_mul]
  exact ENNReal.ofReal_le_ofReal he

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleDamping

/-! Metric stability of the actual cell inverse, with the identity inverse budget discharged. -/

theorem metric_inverse_difference_bound
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    {g : ℝ} (hg : IsMetricNearIdentity G g)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (f : ℝ → Vec 2 → ℂ)
    (hfm : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)))
    (hf : cellUlNorm Set.univ f < ⊤) (D E : ℝ → RawJet2 1 ℂ)
    (hD : IsCellInverseValue ⟨G, v, 0, 0⟩ (fun t => cellQ0 (f t)) (fun _ _ => 0) D)
    (hE : IsCellInverseValue ⟨fun _ _ => 1, v, 0, 0⟩
      (fun t => cellQ0 (f t)) (fun _ _ => 0) E) :
    cellEnergyNorm Set.univ (E - D) ≤
      ENNReal.ofReal 13 * (2 * ENNReal.ofReal g *
        (ENNReal.ofReal 13 * cellUlNorm Set.univ f)) := by
  have hz {H : Type} [NormedAddCommGroup H] :
      cellUlNorm Set.univ (0 : ℝ → Vec 2 → H) = 0 := by
    simp [cellUlNorm, cellL2Norm, Pi.zero_def]
  have hzero : cellUlNorm Set.univ (fun (_ : ℝ) (_ : Vec 2) =>
      (0 : PiLp 2 (fun _ : Fin 2 => ℂ))) < ⊤ := by
    simpa only [← Pi.zero_def] using (hz (H := PiLp 2 (fun _ : Fin 2 => ℂ))) ▸ ENNReal.zero_lt_top
  have hEb := CycleEvolution.cellAllTimeInverse_bound_ae identity_isCellMetric hv f
    (fun _ _ => 0) hfm aestronglyMeasurable_const hf hzero E hE
  have ht := CycleEvolution.cellInverse_parameter_bound hG identity_isCellMetric hv f f
    (fun _ _ => 0) (fun _ _ => 0) D E hfm hfm
    aestronglyMeasurable_const aestronglyMeasurable_const hf hf hzero hzero hD hE
  simp only [sub_self, hz, zero_add] at ht
  have hzF : cellUlNorm Set.univ (fun (_ : ℝ) (_ : Vec 2) =>
      (0 : PiLp 2 (fun _ : Fin 2 => ℂ))) = 0 := by
    simpa only [Pi.zero_def] using hz (H := PiLp 2 (fun _ : Fin 2 => ℂ))
  rw [hzF, add_zero] at hEb
  have hm : cellMetricSupNorm ((fun _ _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) - G) ≤
      ENNReal.ofReal g := by
    have he : ((fun _ _ => (1 : Matrix (Fin 2) (Fin 2) ℝ)) - G) =
        -(G - fun _ _ => 1) := by abel
    rw [he, CycleEvolution.cellMetricSupNorm_neg]
    exact metric_sup_error hG hg
  apply ht.trans
  gcongr

end AVRegularity.CycleDamping
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping

/-! Literal symbol coefficients associated with the committed cell coefficient construction. -/

def canonicalMetricSymbol (η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (p : ℕ × ℕ) (t : ℝ) : ℂ :=
  -(η : ℂ) * ∑ i : Fin 2, ∑ j : Fin 2,
    if p = cellJetDirection i + cellJetDirection j then (G t i j : ℂ) else 0

def canonicalDriftSymbol (η : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (p : ℕ × ℕ) (t : ℝ) : ℂ :=
  ∑ j ∈ fibreCoefficientDirections p, -Complex.I *
    cellMean (fun x => fibreDriftCoupling η v (fibreCoordinateFrequency j) t x *
      cellValue (r (fibreCoefficientPrevious p j)) t x)

def canonicalSymbol (η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ)
    (p : ℕ × ℕ) (t : ℝ) : ℂ :=
  canonicalMetricSymbol η G p t + canonicalDriftSymbol η v r p t

theorem homogeneous_scalar_two (a : ℕ × ℕ → ℝ → ℂ) (ξ : Fin 2 → ℂ) (t : ℝ) :
    fibreHomogeneous a ξ 2 t =
      ξ 0 ^ 2 * a (2, 0) t + ξ 0 * ξ 1 * a (1, 1) t + ξ 1 ^ 2 * a (0, 2) t := by
  have hp : Finset.HasAntidiagonal.antidiagonal (2 : ℕ) = {(2, 0), (1, 1), (0, 2)} := by decide
  simp [fibreHomogeneous, hp, fibreMonomial, smul_eq_mul]
  ring

theorem canonicalMetricSymbol_quadratic (η : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (ξ : Fin 2 → ℂ) (t : ℝ) :
    fibreHomogeneous (canonicalMetricSymbol η G) ξ 2 t = -(η : ℂ) * fibreQuad (G t) ξ := by
  rw [homogeneous_scalar_two]
  norm_num [canonicalMetricSymbol, cellJetDirection, Fin.sum_univ_two, Prod.add_def,
    fibreQuad]
  ring

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping

/-! Time measurability of the actual literal coefficient symbol and its finite Taylor sums. -/

theorem canonicalSymbol_aestronglyMeasurable (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) (p : ℕ × ℕ) :
    AEStronglyMeasurable (canonicalSymbol η G v
      (fibreCoefficientFamily η Cw hη G hG hv hw) p) volume := by
  have hm : Measurable (canonicalMetricSymbol η G p) := by
    unfold canonicalMetricSymbol
    apply measurable_const.mul
    apply Finset.measurable_sum
    intro i _
    apply Finset.measurable_sum
    intro j _
    split_ifs
    · exact Complex.continuous_ofReal.measurable.comp
        ((cellMetric_entry_measurable hG i j).comp
          (measurable_id.prodMk (measurable_const (a := (0 : Vec 2)))))
    · exact measurable_const
  have hd : AEStronglyMeasurable (canonicalDriftSymbol η v
      (fibreCoefficientFamily η Cw hη G hG hv hw) p) (volume.restrict Set.univ) := by
    have hj (j : Fin 2) : AEStronglyMeasurable (fun t => -Complex.I *
        cellMean (fun x => fibreDriftCoupling η v (fibreCoordinateFrequency j) t x *
          cellValue (fibreCoefficientFamily η Cw hη G hG hv hw
            (fibreCoefficientPrevious p j)) t x)) (volume.restrict Set.univ) := by
      apply aestronglyMeasurable_const.mul
      apply cellMean_aestronglyMeasurable
      exact (fibreDriftCoupling_measurable η hv (fibreCoordinateFrequency j)).aestronglyMeasurable.mul
        ((fibreCoefficientFamily_isInverse η Cw hη G hG hv hw
          (fibreCoefficientPrevious p j)).1.2.2.2.1 (valueIndex2 1))
    apply (Finset.aestronglyMeasurable_sum (fibreCoefficientDirections p) (fun j _ => hj j)).congr
    exact Filter.Eventually.of_forall (fun t => by
      simp only [canonicalDriftSymbol, Finset.sum_apply])
  have hd' : AEStronglyMeasurable (canonicalDriftSymbol η v
      (fibreCoefficientFamily η Cw hη G hG hv hw) p) volume := by
    simpa only [Measure.restrict_univ] using hd
  exact hm.aestronglyMeasurable.add hd'

theorem homogeneous_aestronglyMeasurable {lam : ℕ × ℕ → ℝ → ℂ}
    (hlam : ∀ p, AEStronglyMeasurable (lam p) volume) (ξ : Fin 2 → ℂ) (n : ℕ) :
    AEStronglyMeasurable (fibreHomogeneous lam ξ n) volume := by
  unfold fibreHomogeneous
  exact Finset.aestronglyMeasurable_sum _ (fun p _ => (hlam p).const_smul _)

theorem finite_symbol_aestronglyMeasurable {lam : ℕ × ℕ → ℝ → ℂ}
    (hlam : ∀ p, AEStronglyMeasurable (lam p) volume) (ξ : Fin 2 → ℂ) (N : ℕ) :
    AEStronglyMeasurable (fun t => ∑ n ∈ Finset.range (N + 1), fibreHomogeneous lam ξ n t) volume := by
  have hh := Finset.aestronglyMeasurable_sum (Finset.range (N + 1))
    (fun n _ => homogeneous_aestronglyMeasurable hlam ξ n)
  apply hh.congr
  exact Filter.Eventually.of_forall (fun t => by simp only [Finset.sum_apply])

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleDamping

/-! Identification of the actual first graph coefficients with the all-time cell correctors. -/

/-- Complex linearity and all-time uniqueness identify each constructed linear coefficient.
Equality is of the continuous L2 traces, so raw representatives need not agree pointwise. -/
theorem fibreCoefficientFamily_linear_corrector (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (χ : Fin 2 → ℝ → RawJet2 1 ℂ)
    (hχ : ∀ j, IsCellInverseValue ⟨fun t _ => G t, v, 0, 0⟩
      (fun t => cellQ0 (fun x => ((Real.sqrt η * v t x j : ℝ) : ℂ))) 0 (χ j))
    (j : Fin 2) (t : ℝ) :
    cellValue (CycleEvolution.fibreCoefficientFamily η Cw hη G hG hv hw
      (CycleEvolution.cellJetDirection j)) t =ᵐ[volume.restrict AVenhance.unitCube]
        fun x => -Complex.I * cellValue (χ j) t x := by
  let r := CycleEvolution.fibreCoefficientFamily η Cw hη G hG hv hw
  have hr0 : r 0 = 0 := CycleEvolution.fibreCoefficientFamily_zero η Cw hη G hG hv hw
  have hr := CycleEvolution.fibreCoefficientFamily_isInverse η Cw hη G hG hv hw
    (CycleEvolution.cellJetDirection j)
  change IsCellInverseValue _ (fun t => cellQ0
    (CycleEvolution.fibreCoefficientSource η v r (CycleEvolution.cellJetDirection j) t))
    (CycleEvolution.fibreCoefficientFlux η G r (CycleEvolution.cellJetDirection j))
    (r (CycleEvolution.cellJetDirection j)) at hr
  rw [fibreCoefficientSource_direction η v r hr0 j,
    fibreCoefficientFlux_direction η G r hr0 j] at hr
  have hc := CycleEvolution.cellInverse_complex_smul (hχ j) (-Complex.I)
  have hs : (-Complex.I) • (fun t => cellQ0
      (fun x => ((Real.sqrt η * v t x j : ℝ) : ℂ))) =
      fun t => cellQ0 (fun x => -Complex.I * ((Real.sqrt η * v t x j : ℝ) : ℂ)) := by
    funext t
    exact (CycleEvolution.cellQ0_complex_smul (-Complex.I) _).symm
  rw [hs, smul_zero] at hc
  exact CycleEvolution.cellAllTimeInverse_unique_arbitrary_source hG hv _ _ _ _ hr hc t

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping

/-! Actual all-time correctors obtained from the committed first inverse coefficients. -/

def canonicalCorrector (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (j : Fin 2) :
    ℝ → RawJet2 1 ℂ := Complex.I • r (cellJetDirection j)

theorem canonicalCorrector_isInverse (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw) (j : Fin 2) :
    IsCellInverseValue ⟨fun t _ => G t, v, 0, 0⟩
      (fun t => cellQ0 (fun x => ((Real.sqrt η * v t x j : ℝ) : ℂ))) 0
      (canonicalCorrector (fibreCoefficientFamily η Cw hη G hG hv hw) j) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  have hr0 : r 0 = 0 := fibreCoefficientFamily_zero η Cw hη G hG hv hw
  have hr := fibreCoefficientFamily_isInverse η Cw hη G hG hv hw (cellJetDirection j)
  change IsCellInverseValue _ (fun t => cellQ0 (fibreCoefficientSource η v r (cellJetDirection j) t))
    (fibreCoefficientFlux η G r (cellJetDirection j)) (r (cellJetDirection j)) at hr
  rw [fibreCoefficientSource_direction η v r hr0 j, fibreCoefficientFlux_direction η G r hr0 j] at hr
  have hh := cellInverse_complex_smul hr Complex.I
  have hs : Complex.I • (fun t => cellQ0 (fun x => -Complex.I *
      ((Real.sqrt η * v t x j : ℝ) : ℂ))) =
      fun t => cellQ0 (fun x => ((Real.sqrt η * v t x j : ℝ) : ℂ)) := by
    funext t
    simp only [Pi.smul_apply]
    rw [← cellQ0_complex_smul]
    congr 1
    funext x
    change Complex.I * (-Complex.I * _) = _
    rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]
  rw [hs, smul_zero] at hh
  exact hh

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleDamping

/-! The quadratic graph-symbol expression from the actual constructed linear response. -/

section
local instance linearResponseTensorProbCube : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using CycleEvolution.cellCube_volume_one⟩

/-- Substituting the actual first graph coefficients gives the true-corrector bridge tensor. -/
theorem linear_response_quadratic_tensor (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (χ : Fin 2 → ℝ → RawJet2 1 ℂ)
    (hχ : ∀ j, IsCellInverseValue ⟨fun t _ => G t, v, 0, 0⟩
      (fun t => cellQ0 (fun x => ((Real.sqrt η * v t x j : ℝ) : ℂ))) 0 (χ j))
    (ξ : Fin 2 → ℂ) (t : ℝ) :
    -(η : ℂ) * fibreQuad (G t) ξ - Complex.I *
      cellMean (fun x => CycleEvolution.fibreDriftCoupling η v ξ t x *
        ∑ j : Fin 2, ξ j * cellValue
          (CycleEvolution.fibreCoefficientFamily η Cw hη G hG hv hw
            (CycleEvolution.cellJetDirection j)) t x) =
      -(∑ i, ∑ j, ξ i * fibreBridgeMatrix η G v χ t i j * ξ j) := by
  let w : Fin 2 → Vec 2 → ℂ := fun i x => ((Real.sqrt η * v t x i : ℝ) : ℂ)
  let c : Fin 2 → Vec 2 → ℂ := fun j => cellValue (χ j) t
  have hwc (i j : Fin 2) : Integrable (fun x => w i x * c j x)
      (volume.restrict AVenhance.unitCube) := by
    have hm : Measurable (w i) := by
      exact Complex.continuous_ofReal.measurable.comp
        ((((measurable_pi_apply i).comp hv.1).comp
          (measurable_const.prodMk measurable_id)).const_mul _)
    have hb (x : Vec 2) : ‖w i x‖ ≤ Cw := by
      have hh := CycleEvolution.fibreDriftCoupling_norm_le η Cw v hw
        (CycleEvolution.fibreCoordinateFrequency i) t x
      simpa only [CycleEvolution.fibreCoordinateFrequency_coupling,
        CycleEvolution.fibreCoordinateFrequency_norm, mul_one, Complex.ofReal_mul, w] using hh
    have hf := (hχ j).1.2.2.1 t (Set.mem_univ t)
    exact (CycleEvolution.cellMultiplier_memLp (w i) (c j) Cw hm hb hf.1).integrable (by norm_num)
  have he : cellMean (fun x => CycleEvolution.fibreDriftCoupling η v ξ t x *
      ∑ j : Fin 2, ξ j * cellValue
        (CycleEvolution.fibreCoefficientFamily η Cw hη G hG hv hw
          (CycleEvolution.cellJetDirection j)) t x) =
      cellMean (fun x => (∑ i, w i x * ξ i) * (-Complex.I * ∑ j, ξ j * c j x)) := by
    apply integral_congr_ae
    have hfirst (j : Fin 2) := fibreCoefficientFamily_linear_corrector η Cw hη G hG hv hw χ hχ j t
    filter_upwards [ae_all_iff.2 hfirst] with x hx
    simp_rw [hx]
    rw [← CycleEvolution.fibreDriftCoupling_coordinates]
    simp only [CycleEvolution.fibreCoordinateFrequency_coupling, Fin.sum_univ_two, w, c,
      Complex.ofReal_mul]
    ring
  rw [he]
  rw [sub_eq_add_neg, ← neg_mul]
  rw [quadratic_corrector_mean w c hwc ξ, fibreBridgeMatrix_quadratic]
  dsimp [w, c]
  ring
end

/-! Both public low-frequency symbol conclusions from the actual quadratic and graph bounds. -/

theorem low_full_finite_damping_of_graph {η ξ₀ Cg : ℝ}
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {r : ℕ × ℕ → ℝ → RawJet2 1 ℂ} {lam : ℕ × ℕ → ℝ → ℂ}
    (hG : IsCellMetric (fun t _ => G t)) (hv : IsCellDrift v)
    (h : IsFibreGraph η G v ξ₀ Cg r lam) (hξ₀ : 0 < ξ₀) (hCg : 0 ≤ Cg)
    (hlam : ∀ p, AEStronglyMeasurable (lam p) volume)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ ξ₀ / 4)
    (a b c : ℝ) (hab : a ≤ b)
    (hsmall : (2 * Cg * (2 / ξ₀) ^ 3) * fibreNorm ξ ≤ c / 4)
    (hquad : (∫ t in a..b, fibreHomogeneous lam ξ 2 t).re ≤
      -(3 * c / 4) * (b - a) * fibreNorm ξ ^ 2) :
    (∫ t in a..b, fibreSeriesC lam ξ t).re ≤ -(c / 2) * (b - a) * fibreNorm ξ ^ 2 ∧
      ∀ N : ℕ, 2 ≤ N →
        (∫ t in a..b, ∑ n ∈ Finset.range (N + 1), fibreHomogeneous lam ξ n t).re ≤
          -(c / 2) * (b - a) * fibreNorm ξ ^ 2 := by
  have hQ := homogeneous_aestronglyMeasurable hlam ξ 2
  constructor
  · exact low_symbol_damping_of_graph_budget h ξ (fibreSeriesC lam ξ)
      (graph_symbol_aestronglyMeasurable hG hv h ξ (hξ.trans_lt (by linarith))) hQ
      (graph_symbol_quadratic_remainder h hξ₀ hCg ξ hξ) a b c hab hsmall hquad
  · intro N hN
    exact low_symbol_damping_of_graph_budget h ξ _
      (finite_symbol_aestronglyMeasurable hlam ξ N) hQ
      (graph_finite_symbol_quadratic_remainder h hξ₀ hCg ξ hξ N hN) a b c hab hsmall hquad

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping

/-! Identification of the literal degree-two symbol with the true inverse bridge. -/

local instance canonicalQuadraticSymbolProbCube : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using cellCube_volume_one⟩

theorem canonicalDriftSymbol_quadratic (η : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (ξ : Fin 2 → ℂ) (t : ℝ)
    (hi : ∀ i j : Fin 2, Integrable (fun x =>
      fibreDriftCoupling η v (fibreCoordinateFrequency i) t x *
        cellValue (r (cellJetDirection j)) t x) (volume.restrict AVenhance.unitCube)) :
    fibreHomogeneous (canonicalDriftSymbol η v r) ξ 2 t =
      -Complex.I * cellMean (fun x => fibreDriftCoupling η v ξ t x *
        ∑ j : Fin 2, ξ j * cellValue (r (cellJetDirection j)) t x) := by
  have hd20 : fibreCoefficientDirections (2, 0) = {0} := by decide
  have hd11 : fibreCoefficientDirections (1, 1) = {0, 1} := by decide
  have hd02 : fibreCoefficientDirections (0, 2) = {1} := by decide
  rw [homogeneous_scalar_two]
  simp only [canonicalDriftSymbol, hd20, hd11, hd02, Finset.sum_singleton,
    Finset.sum_insert, Finset.mem_singleton, show (0 : Fin 2) ≠ 1 by decide,
    not_false_eq_true]
  have hp20 : fibreCoefficientPrevious (2, 0) 0 = cellJetDirection 0 := by decide
  have hp110 : fibreCoefficientPrevious (1, 1) 0 = cellJetDirection 1 := by decide
  have hp111 : fibreCoefficientPrevious (1, 1) 1 = cellJetDirection 0 := by decide
  have hp02 : fibreCoefficientPrevious (0, 2) 1 = cellJetDirection 1 := by decide
  rw [hp20, hp110, hp111, hp02]
  have he : (fun x => fibreDriftCoupling η v ξ t x *
      ∑ j : Fin 2, ξ j * cellValue (r (cellJetDirection j)) t x) =
      fun x => (ξ 0 * ξ 0) * (fibreDriftCoupling η v (fibreCoordinateFrequency 0) t x *
          cellValue (r (cellJetDirection 0)) t x) +
        (ξ 0 * ξ 1) * (fibreDriftCoupling η v (fibreCoordinateFrequency 0) t x *
          cellValue (r (cellJetDirection 1)) t x) +
        (ξ 1 * ξ 0) * (fibreDriftCoupling η v (fibreCoordinateFrequency 1) t x *
          cellValue (r (cellJetDirection 0)) t x) +
        (ξ 1 * ξ 1) * (fibreDriftCoupling η v (fibreCoordinateFrequency 1) t x *
          cellValue (r (cellJetDirection 1)) t x) := by
    funext x
    rw [← fibreDriftCoupling_coordinates]
    simp only [Fin.sum_univ_two]
    ring
  rw [he]
  change _ = -Complex.I * ∫ x in AVenhance.unitCube, _
  have hab := integral_add (((hi 0 0).const_mul (ξ 0 * ξ 0)).add
      ((hi 0 1).const_mul (ξ 0 * ξ 1)) |>.add ((hi 1 0).const_mul (ξ 1 * ξ 0)))
    ((hi 1 1).const_mul (ξ 1 * ξ 1))
  have hac := integral_add (((hi 0 0).const_mul (ξ 0 * ξ 0)).add
      ((hi 0 1).const_mul (ξ 0 * ξ 1))) ((hi 1 0).const_mul (ξ 1 * ξ 0))
  have had := integral_add ((hi 0 0).const_mul (ξ 0 * ξ 0)) ((hi 0 1).const_mul (ξ 0 * ξ 1))
  simp only [Pi.add_apply] at hab hac had
  rw [hab, hac, had]
  simp only [integral_const_mul, cellMean]
  ring

theorem canonicalSymbol_quadratic_bridge (η Cw : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (χ : Fin 2 → ℝ → RawJet2 1 ℂ)
    (hχ : ∀ j, IsCellInverseValue ⟨fun t _ => G t, v, 0, 0⟩
      (fun t => cellQ0 (fun x => ((Real.sqrt η * v t x j : ℝ) : ℂ))) 0 (χ j))
    (ξ : Fin 2 → ℂ) (t : ℝ) :
    fibreHomogeneous (canonicalSymbol η G v
      (fibreCoefficientFamily η Cw hη G hG hv hw)) ξ 2 t =
      -(∑ i, ∑ j, ξ i * fibreBridgeMatrix η G v χ t i j * ξ j) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  have hi (i j : Fin 2) : Integrable (fun x =>
      fibreDriftCoupling η v (fibreCoordinateFrequency i) t x *
        cellValue (r (cellJetDirection j)) t x) (volume.restrict AVenhance.unitCube) := by
    have hm : Measurable (fun x => fibreDriftCoupling η v (fibreCoordinateFrequency i) t x) := by
      simp only [fibreCoordinateFrequency_coupling, ← Complex.ofReal_mul]
      exact Complex.continuous_ofReal.measurable.comp
        ((((measurable_pi_apply i).comp hv.1).comp
          (measurable_const.prodMk measurable_id)).const_mul _)
    have hb (x : Vec 2) : ‖fibreDriftCoupling η v (fibreCoordinateFrequency i) t x‖ ≤ Cw := by
      simpa only [fibreCoordinateFrequency_norm, mul_one] using
        fibreDriftCoupling_norm_le η Cw v hw (fibreCoordinateFrequency i) t x
    have hf := (fibreCoefficientFamily_isInverse η Cw hη G hG hv hw (cellJetDirection j)).1.2.2.1
      t (Set.mem_univ t)
    exact (cellMultiplier_memLp _ _ Cw hm hb hf.1).integrable (by norm_num)
  have hsplit : fibreHomogeneous (canonicalSymbol η G v r) ξ 2 t =
      fibreHomogeneous (canonicalMetricSymbol η G) ξ 2 t +
        fibreHomogeneous (canonicalDriftSymbol η v r) ξ 2 t := by
    simp only [homogeneous_scalar_two, canonicalSymbol]
    ring
  rw [hsplit, canonicalMetricSymbol_quadratic, canonicalDriftSymbol_quadratic η v r ξ t hi]
  simpa only [sub_eq_add_neg, neg_mul, r] using
    linear_response_quadratic_tensor η Cw hη G hG hv hw χ hχ ξ t

end AVRegularity.CycleDamping
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleDamping

/-! Exponential decay of the actual raw homogeneous cell solutions. -/

theorem admissible_raw_high_decay (ξlo : ℝ) (hlo : 0 < ξlo) :
    ∃ d c : ℝ, 0 < d ∧ 0 < c ∧ ∀ (α q : ℝ) (Λ m : ℕ) (ζ : ℝ → ℝ),
      1 ≤ Λ → IsFastProfile ζ → ∀ ν : ℝ, 0 < ν →
      6 ≤ ocMu q Λ m ν * ocTau α q Λ m →
      ∀ (y₀ : Vec 2) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
        (_hG : IsCellMetric (fun t _ => G t))
        (_hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀)) (V : ℝ)
        (_hb : ∀ t x, ∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2 ≤ V ^ 2)
        (ξ : Vec 2), (∀ i, |ξ i| ≤ Real.pi / Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν)) →
      ξlo ≤ Real.sqrt (∑ i : Fin 2, ξ i ^ 2) →
      ∀ Θ ta T : ℝ, 1 ≤ Θ →
      IsOCAdmissibleInterval α q Λ ζ m ν (ocMeanFlux α q Λ ζ m ν) Θ d ta T →
      ∀ D : ℝ → RawJet2 1 ℂ,
        IsCellSolution (Icc (ta / ocEll q Λ m ν ^ 2) ((ta + T) / ocEll q Λ m ν ^ 2))
          (fibreCoefficients (ν / ocMeanFlux α q Λ ζ m ν) G
            (ocCellDrift α q Λ ζ m ν y₀) (fun i => (ξ i : ℂ)) (fun _ => 0))
          (fun _ _ => 0) (fun _ _ => 0) D →
        cellL2Norm (cellValue D ((ta + T) / ocEll q Λ m ν ^ 2)) ≤
          ENNReal.ofReal (Real.exp (-c * (T / ocEll q Λ m ν ^ 2))) *
            cellL2Norm (cellValue D (ta / ocEll q Λ m ν ^ 2)) := by
  obtain ⟨d, c, hd, hc, hdec⟩ := admissible_weak_high_decay ξlo hlo
  refine ⟨d, c, hd, hc, ?_⟩
  intro α q Λ m ζ hΛ hζ ν hν hr y₀ G hG hv V hb ξ hξ hnorm Θ ta T hΘ hadm D h
  have hB := CycleReference.meanFlux_ge_input (α := α) (q := q) (m := m) hΛ hζ hν
  have hη : 0 < ν / ocMeanFlux α q Λ ζ m ν := div_pos hν (hν.trans_le hB)
  have hL : 0 < ocEll q Λ m ν ^ 2 := by
    rw [CycleReference.ocEll_sq_eq hν]
    have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
    positivity
  have hT : 0 ≤ T := by
    have hs : 0 ≤ T / ocEll q Λ m ν ^ 2 := le_trans (by linarith) hadm.2.1
    simpa only [div_mul_cancel₀ _ hL.ne'] using mul_nonneg hs hL.le
  have hab : ta / ocEll q Λ m ν ^ 2 ≤ (ta + T) / ocEll q Λ m ν ^ 2 :=
    div_le_div_of_nonneg_right (by linarith) hL.le
  have hh := h
  rw [real_fibre_coefficients] at hh
  have hw := raw_homogeneous_weak_curve hab (fun t _ => G t) hG
    (ocCellDrift α q Λ ζ m ν y₀) V hv.1 hb _ D hh
  have he := hdec α q Λ m ζ hΛ hζ ν hν hr y₀ G hG hv V hb ξ
    (scaled_real_brillouin _ hη ξ hξ) hnorm Θ ta T hΘ hadm
    (cellRawTrace D) (cellH1Slice D) hw
  rw [cellL2Norm_eq_of_class _ _ (cellRawTrace_ae D _ (h.2.2.1 _ ⟨hab, le_rfl⟩).1),
    cellL2Norm_eq_of_class _ _ (cellRawTrace_ae D _ (h.2.2.1 _ ⟨le_rfl, hab⟩).1)]
  exact he

end AVRegularity.CycleDamping
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleDamping

/-! Uniform raw high-frequency decay along every interior band-chain level. -/

theorem bandChain_high_decay {α s q : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ ξlo : ℝ, 0 < ξlo → ∃ d c : ℝ, 0 < d ∧ 0 < c ∧
      ∀ (M : ℕ) (κ : ℕ → ℝ), IsOCBandChain α q Λ ζ M κ →
      ∀ m : ℕ, 2 ≤ m → m ≤ M → ∀ ν B : ℝ, κ m = ν → κ (m - 1) = B →
      ∀ (y₀ : Vec 2) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ),
      IsCellMetric (fun t _ => G t) → ∀ Θ ta T : ℝ, 1 ≤ Θ →
      IsOCAdmissibleInterval α q Λ ζ m ν B Θ d ta T →
      ∀ ξ : Vec 2, (∀ i, |ξ i| ≤ Real.pi / Real.sqrt (ν / B)) →
      ξlo ≤ Real.sqrt (∑ i : Fin 2, ξ i ^ 2) →
      ∀ D : ℝ → RawJet2 1 ℂ,
      IsCellSolution (Icc (ta / ocEll q Λ m ν ^ 2) ((ta + T) / ocEll q Λ m ν ^ 2))
        (fibreCoefficients (ν / B) G (ocCellDrift α q Λ ζ m ν y₀)
          (fun i => (ξ i : ℂ)) (fun _ => 0)) (fun _ _ => 0) (fun _ _ => 0) D →
      cellL2Norm (cellValue D ((ta + T) / ocEll q Λ m ν ^ 2)) ≤
        ENNReal.ofReal (Real.exp (-c * (T / ocEll q Λ m ν ^ 2))) *
          cellL2Norm (cellValue D (ta / ocEll q Λ m ν ^ 2)) := by
  obtain ⟨Λ₀, hΛ₀, hr⟩ := bandChain_relaxation_large hα₀ hα₁ hs₀ hs₁ hq hζ 6 (by norm_num)
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ ξlo hlo
  obtain ⟨d, c, hd, hc, hdec⟩ := admissible_raw_high_decay ξlo hlo
  refine ⟨d, c, hd, hc, ?_⟩
  intro M κ hκ m hm hmM ν B hνeq hBeq y₀ G hG Θ ta T hΘ hadm ξ hξ hnorm D h
  have hΛ1 : 1 ≤ Λ := by omega
  have hν : 0 < ν := hνeq ▸ CycleReference.bandChain_pos hΛ1 hζ hκ hmM
  have hB : B = ocMeanFlux α q Λ ζ m ν := by
    rw [← hBeq, hκ.2 m (by omega) hmM, hνeq]
  have hv := ocCellDrift_isCellDrift (α := α) (q := q) (m := m) hΛ1 hζ ν y₀
  obtain ⟨V, hb⟩ := hv.2.1
  rw [hB] at hadm hξ h
  exact hdec α q Λ m ζ hΛ1 hζ ν hν (hνeq ▸ hr Λ hΛ M κ hκ m hm hmM)
    y₀ G hG hv V hb ξ hξ hnorm Θ ta T hΘ hadm D h

end AVRegularity.CycleDamping
end
