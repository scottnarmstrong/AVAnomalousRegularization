-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.CellTimeL1L2Bound
import AVRegularity.CycleEvolution.FibreCoefficientLinearSeries
public import AVRegularity.CycleEvolution.CellBochnerCarrier
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Real.Pi.Bounds

section
@[expose] public noncomputable section
open MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Integrated fixed tests as continuous linear functionals on temporal H¹ classes. -/

/-- Pair against a square-integrable time test supported on the chosen subinterval. -/
def cellTimeTestIntegralCLM (a b s t : ℝ) (w : ℝ → TorusHk 1 ℂ)
    (hw : MemLp w 2 (volume.restrict (Icc a b))) : CellBochnerH1 a b →L[ℝ] ℝ :=
  by
    let hwi : MemLp ((Ioc s t).indicator w) 2 (volume.restrict (Icc a b)) :=
      cellTime_memLp_indicator (Ioc s t) measurableSet_Ioc w hw
    let W : CellBochnerH1 a b := hwi.toLp ((Ioc s t).indicator w)
    exact innerSL ℝ W

/-- The temporal pairing functional is the literal subinterval integral. -/
theorem cellTimeTestIntegralCLM_apply {a b s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (u w : ℝ → TorusHk 1 ℂ)
    (hu : MemLp u 2 (volume.restrict (Icc a b)))
    (hw : MemLp w 2 (volume.restrict (Icc a b))) :
    cellTimeTestIntegralCLM a b s t w hw (hu.toLp u) =
      ∫ r in s..t, inner ℝ (u r) (w r) := by
  unfold cellTimeTestIntegralCLM
  rw [innerSL_apply_apply, L2.inner_def]
  have he : (∫ r in Icc a b,
      inner ℝ (((cellTime_memLp_indicator (Ioc s t) measurableSet_Ioc w hw).toLp ((Ioc s t).indicator w)) r)
        ((hu.toLp u) r)) =
      ∫ r in Icc a b, (Ioc s t).indicator (fun r => inner ℝ (u r) (w r)) r := by
    apply integral_congr_ae
    filter_upwards [hu.coeFn_toLp, (cellTime_memLp_indicator (Ioc s t) measurableSet_Ioc w hw).coeFn_toLp] with r hur hwr
    rw [hur, hwr]
    by_cases hr : r ∈ Ioc s t
    · simp only [indicator_of_mem hr, real_inner_comm]
    · simp only [indicator_of_notMem hr, inner_zero_left]
  rw [he, integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc]
  have hsub : Ioc s t ⊆ Icc a b :=
    Ioc_subset_Icc_self.trans (Icc_subset_Icc hs.1 ht.2)
  rw [inter_eq_left.mpr hsub, intervalIntegral.integral_of_le hst]

/-- The integrated generator against a fixed H¹ test as a temporal continuous functional. -/
def cellGeneratorIntegralCLM (a b s t : ℝ)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Homogenization.Vec 2 => C.v p.1 p.2))
    (hb : ∀ τ x, ∑ i, C.v τ x i ^ 2 ≤ V ^ 2)
    (hκ : Measurable C.κ) (hκb : ∀ τ, ‖C.κ τ‖ ≤ k) (z : TorusHk 1 ℂ) :
    CellBochnerH1 a b →L[ℝ] ℝ :=
  cellTimeTestIntegralCLM a b s t (fun τ => cellGeneratorTest C hG V hv hb τ z)
    (cellGeneratorTest_memLp a b C hG V k hv hb hκ hκb z)

/-- The generator functional evaluates to the literal fixed-test weak equation integral. -/
theorem cellGeneratorIntegralCLM_apply {a b s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Homogenization.Vec 2 => C.v p.1 p.2))
    (hb : ∀ τ x, ∑ i, C.v τ x i ^ 2 ≤ V ^ 2)
    (hκ : Measurable C.κ) (hκb : ∀ τ, ‖C.κ τ‖ ≤ k) (z : TorusHk 1 ℂ)
    (u : ℝ → TorusHk 1 ℂ) (hu : MemLp u 2 (volume.restrict (Icc a b))) :
    cellGeneratorIntegralCLM a b s t C hG V k hv hb hκ hκb z (hu.toLp u) =
      ∫ r in s..t, cellGeneratorForm C hG V hv hb r (u r) z := by
  rw [cellGeneratorIntegralCLM, cellTimeTestIntegralCLM_apply hs ht hst]
  exact intervalIntegral.integral_congr (fun r _ => cellGeneratorTest_pairing C hG V hv hb r _ z)

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Actual weak Hilbert solutions determine the complete complex energy carrier. -/

theorem cellWeakHilbertCurve_exists_energyCarrier (a b : ℝ)
    (u : ℝ → ComplexCellL2) (slice g : ℝ → TorusHk 1 ℂ)
    (hw : CellWeakHilbertCurve a b u slice g) :
    ∃ z : CellFiniteEnergyCarrier a b,
      (∀ t : CellCompactTime a b, z.val.1 t = u t.val) ∧
      (∀ᵐ t ∂(volume : Measure (CellCompactTime a b)),
        cellComplexH1RealEquiv (z.val.2 t) = slice t.val) := by
  have hmp : MeasurePreserving ((↑) : CellCompactTime a b → ℝ) volume (volume.restrict (Icc a b)) :=
    measurePreserving_subtype_coe measurableSet_Icc
  let tr : C(CellCompactTime a b, ComplexCellL2) :=
    ⟨fun t => u t.val, continuousOn_iff_continuous_domRestrict.mp hw.trace⟩
  let st : CellCompactTime a b → CellComplexH1 := fun t => cellComplexH1RealEquiv.symm (slice t.val)
  have hm : MemLp st 2 (volume : Measure (CellCompactTime a b)) :=
    cellComplexH1RealEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp'
      (hw.state.comp_measurePreserving hmp)
  have ha : ∀ᵐ t ∂(volume : Measure (CellCompactTime a b)), tr t = cellComplexH1ValueCLM (st t) := by
    filter_upwards [hmp.quasiMeasurePreserving.ae hw.agrees] with t ht
    change u t.val = cellComplexH1ValueCLM (cellComplexH1RealEquiv.symm (slice t.val))
    rw [cellComplexH1ValueCLM_eq, LinearIsometryEquiv.apply_symm_apply]
    exact ht
  let z := compatibleTraceLpOf (volume : Measure (CellCompactTime a b)) cellComplexH1ValueCLM tr st hm ha
  refine ⟨z, fun _ => rfl, ?_⟩
  filter_upwards [hm.coeFn_toLp] with t ht
  change cellComplexH1RealEquiv ((hm.toLp st) t) = slice t.val
  rw [ht]
  exact cellComplexH1RealEquiv.apply_symm_apply _

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open AVRegularity.Sobolev AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleEvolution

/-! Every constant real-linear fibre map preserves the actual weak Hilbert time equation. -/

theorem CellWeakHilbertCurve.fiber_map {a b : ℝ} {u : ℝ → ComplexCellL2}
    {slice g : ℝ → TorusHk 1 ℂ} (h : CellWeakHilbertCurve a b u slice g)
    (L : ℂ →L[ℝ] ℂ) :
    CellWeakHilbertCurve a b (fun t => cellFiberCLM L (u t))
      (fun t => mapTorusHkCLM 1 L (slice t)) (fun t => mapTorusHkCLM 1 L (g t)) := by
  apply h.map (cellFiberCLM L) (mapTorusHkCLM 1 L) (cellFiberCLM_value L)
  intro z
  rw [cellFiberCLM_adjoint, cellH1FiberMap_adjoint]
  exact cellFiberCLM_value L.adjoint z

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleEvolution

/-! Factorial weights turn the exact binomial jet recurrence into an ordinary positive convolution. -/

/-- The real factorial weight of a two-coordinate derivative. -/
def cellJetWeightReal (ρ : ℝ) (α : ℕ × ℕ) : ℝ :=
  ρ ^ (α.1 + α.2) / ((α.1.factorial : ℝ) * (α.2.factorial : ℝ))

/-- One-dimensional factorial cancellation in a binomial convolution. -/
theorem factorialWeight_binomial (ρ : ℝ) (n k : ℕ) (hk : k ≤ n) :
    (ρ ^ n / (n.factorial : ℝ)) * (n.choose k : ℝ) =
      (ρ ^ k / (k.factorial : ℝ)) *
        (ρ ^ (n - k) / ((n - k).factorial : ℝ)) := by
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hkf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hnk : ((n - k).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n - k)
  have hfac : (n.choose k : ℝ) * (k.factorial : ℝ) * ((n - k).factorial : ℝ) =
      (n.factorial : ℝ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  have hp : ρ ^ n = ρ ^ k * ρ ^ (n - k) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hp]
  field_simp [hn, hkf, hnk]
  rw [← hfac]
  ring

/-- A two-coordinate factorial weight separates into the two one-coordinate weights. -/
theorem cellJetWeightReal_eq_product (ρ : ℝ) (α : ℕ × ℕ) :
    cellJetWeightReal ρ α = (ρ ^ α.1 / (α.1.factorial : ℝ)) *
      (ρ ^ α.2 / (α.2.factorial : ℝ)) := by
  simp only [cellJetWeightReal, pow_add, div_mul_div_comm]

/-- Binomial factors disappear exactly under the two-coordinate factorial weights. -/
theorem cellJetWeightReal_choose (ρ : ℝ) (α β : ℕ × ℕ) (hβ : β ≤ α) :
    cellJetWeightReal ρ α * (cellJetChoose α β : ℝ) =
      cellJetWeightReal ρ β * cellJetWeightReal ρ (α.1 - β.1, α.2 - β.2) := by
  change β.1 ≤ α.1 ∧ β.2 ≤ α.2 at hβ
  simp only [cellJetWeightReal_eq_product, cellJetChoose, Nat.cast_mul]
  calc
    _ = ((ρ ^ α.1 / (α.1.factorial : ℝ)) * (α.1.choose β.1 : ℝ)) *
        ((ρ ^ α.2 / (α.2.factorial : ℝ)) * (α.2.choose β.2 : ℝ)) := by ring
    _ = _ := by rw [factorialWeight_binomial ρ α.1 β.1 hβ.1,
      factorialWeight_binomial ρ α.2 β.2 hβ.2]; ring

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! Literal Taylor coefficients and uniform L2 majorants for a scalar-normalized row. -/

def fibreRowCoefficients (k : ℕ × ℕ → ℝ → ℂ) (a : ℕ × ℕ → ℝ → Vec 2 → ℂ) :
    ℕ × ℕ → ℝ → Vec 2 → ℂ :=
  fun p t x => k p t + ∑ q ∈ fibreCoefficientPairs p,
    k q t * a (fibreCoefficientComplement p q) t x

theorem fibreRowCoefficients_uniform_le (k : ℕ × ℕ → ℝ → ℂ)
    (a : ℕ × ℕ → ℝ → Vec 2 → ℂ) (p : ℕ × ℕ) :
    (⨆ t, cellL2Norm (fibreRowCoefficients k a p t)) ≤
      (⨆ t, ‖k p t‖ₑ) + ∑ q ∈ fibreCoefficientPairs p,
        (⨆ t, ‖k q t‖ₑ) * ⨆ t, cellL2Norm (a (fibreCoefficientComplement p q) t) := by
  apply iSup_le
  intro t
  have hsum : cellL2Norm (fun x => ∑ q ∈ fibreCoefficientPairs p,
      k q t * a (fibreCoefficientComplement p q) t x) ≤
      ∑ q ∈ fibreCoefficientPairs p,
        (⨆ s, ‖k q s‖ₑ) * ⨆ s, cellL2Norm (a (fibreCoefficientComplement p q) s) := by
    have he := eLpNorm_sum_le (μ := volume.restrict AVenhance.unitCube)
      (s := fibreCoefficientPairs p)
      (f := fun q x => k q t * a (fibreCoefficientComplement p q) t x)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hfun : (∑ q ∈ fibreCoefficientPairs p,
        (fun x => k q t * a (fibreCoefficientComplement p q) t x)) =
        (fun x => ∑ q ∈ fibreCoefficientPairs p,
          k q t * a (fibreCoefficientComplement p q) t x) := by
      funext x
      simp only [Finset.sum_apply]
    rw [hfun] at he
    change cellL2Norm (fun x => ∑ q ∈ fibreCoefficientPairs p,
      k q t * a (fibreCoefficientComplement p q) t x) ≤
      ∑ q ∈ fibreCoefficientPairs p,
        cellL2Norm (fun x => k q t * a (fibreCoefficientComplement p q) t x) at he
    apply he.trans
    apply Finset.sum_le_sum
    intro q _
    rw [cellL2Norm_const_complex_mul]
    exact mul_le_mul' (le_iSup (fun s => ‖k q s‖ₑ) t)
      (le_iSup (fun s => cellL2Norm (a (fibreCoefficientComplement p q) s)) t)
  apply (eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
  apply add_le_add _ hsum
  change cellL2Norm (fun _ : Vec 2 => k p t) ≤ _
  rw [cellL2Norm_const]
  exact le_iSup (fun s => ‖k p s‖ₑ) t

theorem fibreRowCoefficients_weighted_le (k : ℕ × ℕ → ℝ → ℂ)
    (a : ℕ × ℕ → ℝ → Vec 2 → ℂ) (ρ : ℝ≥0∞) :
    (∑' p, fibreCoefficientWeight ρ p * ⨆ t, cellL2Norm (fibreRowCoefficients k a p t)) ≤
      (∑' p, fibreCoefficientWeight ρ p * ⨆ t, ‖k p t‖ₑ) +
        (∑' p, fibreCoefficientWeight ρ p * ⨆ t, ‖k p t‖ₑ) *
          ∑' p, fibreCoefficientWeight ρ p * ⨆ t, cellL2Norm (a p t) := by
  apply (ENNReal.tsum_le_tsum (fun p => mul_le_mul' le_rfl
    (fibreRowCoefficients_uniform_le k a p))).trans_eq
  simp_rw [mul_add]
  rw [ENNReal.tsum_add]
  exact congrArg (fun z => (∑' p, fibreCoefficientWeight ρ p * ⨆ t, ‖k p t‖ₑ) + z)
    (fibreCoefficient_weighted_convolution_total ρ (fun p => ⨆ t, ‖k p t‖ₑ)
      (fun p => ⨆ t, cellL2Norm (a p t)))

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Literal representative of the actual linear Bloch source class. -/

theorem cellBlochLinearSourceClass_ae (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Fin 2 → ℂ)
    (t : ℝ) (u : TorusHk 1 ℂ) :
    cellBlochLinearSourceClass G v V hv hb θ t u =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => -Complex.I * (∑ j : Fin 2, θ j * (v t x j : ℂ)) * torusHkValueCLM u x -
        (∑ j : Fin 2, ∑ k : Fin 2, (G t j k : ℂ) * θ j * θ k) * torusHkValueCLM u x := by
  let q := -(∑ j : Fin 2, ∑ k : Fin 2, (G t j k : ℂ) * θ j * θ k)
  let A := fun j => cellScalarCLM (-Complex.I * θ j)
    (cellDriftEntryCLM ⟨0, v, 0, 0⟩ V hv.1 hb t j (torusHkValueCLM u))
  let P := cellScalarCLM q (torusHkValueCLM u)
  have hA (j : Fin 2) : A j =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => (-Complex.I * θ j) * ((v t x j : ℂ) * torusHkValueCLM u x) := by
    filter_upwards [cellScalarCLM_ae (-Complex.I * θ j)
      (cellDriftEntryCLM ⟨0, v, 0, 0⟩ V hv.1 hb t j (torusHkValueCLM u)),
      cellDriftEntryCLM_ae ⟨0, v, 0, 0⟩ V hv.1 hb t j (torusHkValueCLM u)] with x ha hd
    rw [ha, hd]
  filter_upwards [ae_all_iff.mpr hA, Lp.coeFn_fun_finsetSum Finset.univ A,
    cellScalarCLM_ae q (torusHkValueCLM u), Lp.coeFn_add (∑ j : Fin 2, A j) P]
    with x ha hs hp hadd
  change ((∑ j : Fin 2, A j) + P) x = _
  rw [hadd]
  change (∑ j : Fin 2, A j) x + P x = _
  rw [hs, hp]
  simp only [Fin.sum_univ_two]
  rw [ha 0, ha 1]
  dsimp only [q]
  simp only [Fin.sum_univ_two]
  ring

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Actual coordinatewise conjugation preserves periodic ordered weak jets. -/

def cellRawJetConj {K : ℕ} (D : RawJet2 K ℂ) : RawJet2 K ℂ :=
  fun a x => star (D a x)

theorem cellComplex_real_inner_conjugate (e z : ℂ) :
    inner ℝ e (star z) = inner ℝ (star e) z := by
  have h := Complex.conjLIE.inner_map_map e (star z)
  change inner ℝ (star e) (star (star z)) = inner ℝ e (star z) at h
  rw [star_star] at h
  exact h.symm

theorem cellPeriodicWeakJet_conjugate {K : ℕ} {D : RawJet2 K ℂ}
    (hD : HasPeriodicOrderedWeakJet D) : HasPeriodicOrderedWeakJet (cellRawJetConj D) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a n x
    change star (D a (x + AVenhance.latticeShift n)) = star (D a x)
    rw [hD.1 a n x]
  · intro a
    exact Complex.conjCLE.toContinuousLinearMap.comp_memLp' (hD.2.1 a)
  · intro j w i e φ hφ hc hsub
    simpa only [cellRawJetConj, cellComplex_real_inner_conjugate] using
      hD.2.2 j w i (star e) φ hφ hc hsub

end AVRegularity.CycleEvolution
end
end

section
@[expose] public section
namespace AVRegularity.CycleEvolution

/-! Finite total-order index sets and the exact recovery map for triangular convolutions. -/

/-- Membership in the total-order index set is precisely the total-order bound. -/
theorem mem_jetIndices_iff (K : ℕ) (α : ℕ × ℕ) :
    α ∈ jetIndices K ↔ α.1 + α.2 ≤ K := by
  simp only [jetIndices, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

/-- Every positive metric index in a triangular convolution belongs to the positive total-order set. -/
theorem cellJetFluxIndices_mem_positive {K : ℕ} {α β : ℕ × ℕ}
    (hα : α ∈ jetIndices K) (hβ : β ∈ cellJetFluxIndices α) :
    β ∈ (jetIndices K).erase 0 := by
  have hb := cellJetFluxIndices_mem hβ
  apply Finset.mem_erase.mpr
  exact ⟨hb.2.2, (mem_jetIndices_iff K β).mpr
    ((cellJetFluxIndices_metric_order hβ).trans ((mem_jetIndices_iff K α).mp hα))⟩

/-- Every lower state index in a triangular convolution belongs to the full total-order set. -/
theorem cellJetFluxIndices_mem_lower {K : ℕ} {α β : ℕ × ℕ}
    (hα : α ∈ jetIndices K) (hβ : β ∈ cellJetFluxIndices α) :
    (α.1 - β.1, α.2 - β.2) ∈ jetIndices K := by
  apply (mem_jetIndices_iff K _).mpr
  exact (Nat.le_of_lt (cellJetFluxIndices_lower_order hβ)).trans
    ((mem_jetIndices_iff K α).mp hα)

/-- The two convolution indices recover the original total multi-index. -/
theorem cellJetFluxIndices_recover {α β : ℕ × ℕ} (hβ : β ∈ cellJetFluxIndices α) :
    β + (α.1 - β.1, α.2 - β.2) = α := by
  have hb := cellJetFluxIndices_mem hβ
  apply Prod.ext <;> simp only [Prod.add_def] <;> omega

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The actual graph flux class agrees with the literal Bloch graph flux. -/

theorem cellNormalizedGraphFluxClass_ae (η : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (ξ : Fin 2 → ℂ)
    (t : ℝ) (u : TorusHk 1 ℂ) (j : Fin 2) :
    cellNormalizedGraphFluxClass G (fun k => (Real.sqrt η : ℂ) * ξ k) t u j
      =ᵐ[volume.restrict AVenhance.unitCube]
        fun x => fibreGraphFlux η G ξ (fun _ y => torusHkValueCLM u y) t x j := by
  filter_upwards [cellScalarCLM_ae
    (2 * Complex.I * ∑ k : Fin 2, (G t j k : ℂ) * ((Real.sqrt η : ℂ) * ξ k))
    (torusHkValueCLM u)] with x hx
  change (cellScalarCLM _ (torusHkValueCLM u)) x = _
  rw [hx]
  simp only [fibreGraphFlux, Fin.sum_univ_two]
  ring

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Sharp Poincaré inequality on the actual periodic H¹ cell carrier by Fourier density. -/

/-- Removing the mean gives the sharp unit-torus Poincaré inequality for every H¹ field. -/
theorem cellH1_meanFree_poincare (u : TorusHk 1 ℂ) :
    ‖cellQ0CLM (torusHkValueCLM u)‖ ^ 2 ≤
      (4 * Real.pi ^ 2)⁻¹ * ∑ j, ‖cellDerivativeCLM j u‖ ^ 2 := by
  have hp := galerkinProj_tendsto u
  have hL := ((cellQ0CLM.comp torusHkValueCLM).continuous.norm.pow 2).continuousAt.tendsto.comp hp
  have hsum : Tendsto (fun N => ∑ j : Fin 2, ‖cellDerivativeCLM j (galerkinProj N u)‖ ^ 2)
      atTop (𝓝 (∑ j : Fin 2, ‖cellDerivativeCLM j u‖ ^ 2)) := by
    apply tendsto_finsetSum
    intro j _
    exact ((cellDerivativeCLM j).continuous.norm.pow 2).continuousAt.tendsto.comp hp
  have hR : Tendsto (fun N => (4 * Real.pi ^ 2)⁻¹ *
      ∑ j : Fin 2, ‖cellDerivativeCLM j (galerkinProj N u)‖ ^ 2) atTop
      (𝓝 ((4 * Real.pi ^ 2)⁻¹ * ∑ j : Fin 2, ‖cellDerivativeCLM j u‖ ^ 2)) :=
    tendsto_const_nhds.mul hsum
  change Tendsto (fun N => ‖cellQ0CLM (torusHkValueCLM (galerkinProj N u))‖ ^ 2)
    atTop (𝓝 (‖cellQ0CLM (torusHkValueCLM u)‖ ^ 2)) at hL
  exact le_of_tendsto_of_tendsto' hL hR (cellFinite_meanFree_poincare u)

/-- For mean-zero H¹ fields, the same sharp inequality bounds their entire L² value. -/
theorem cellH1_meanZero_poincare (u : TorusHk 1 ℂ) (hm : cellMean (torusHkValueCLM u) = 0) :
    ‖torusHkValueCLM u‖ ^ 2 ≤ (4 * Real.pi ^ 2)⁻¹ * ∑ j, ‖cellDerivativeCLM j u‖ ^ 2 := by
  have he : cellQ0CLM (torusHkValueCLM u) = torusHkValueCLM u := by
    simp only [cellQ0CLM, sub_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply, cellMeanCLM_apply, hm, map_zero, sub_zero]
  simpa only [he] using cellH1_meanFree_poincare u

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleEvolution

/-! Abstract-real factorial cancellation and the radius constants, separated from all cell PDE proofs. -/

/-- A factorial-growth bound cancels the factorial denominator of the corresponding weight. -/
theorem cellJetWeightReal_factorial_growth (ρ M a : ℝ) (β : ℕ × ℕ) :
    cellJetWeightReal ρ β *
      (M * ((β.1.factorial : ℝ) * (β.2.factorial : ℝ)) * a ^ (β.1 + β.2)) =
      M * (ρ * a) ^ (β.1 + β.2) := by
  have h1 : (β.1.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero β.1
  have h2 : (β.2.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero β.2
  unfold cellJetWeightReal
  rw [mul_pow]
  field_simp

/-- The prescribed radius has a positive small geometric ratio and makes the universal majorant absorb. -/
theorem factorialRadius_algebra (C M a : ℝ) (hC : 0 ≤ C) (hM : 0 ≤ M) (ha : 0 < a) :
    let ρ := (16 * (1 + C * M) * a)⁻¹
    0 < ρ ∧ 0 ≤ ρ * a ∧ ρ * a ≤ 1 / 2 ∧ C * (8 * M * (ρ * a)) ≤ 1 / 2 := by
  dsimp
  have hcm : 0 ≤ C * M := mul_nonneg hC hM
  have hd : 0 < 16 * (1 + C * M) := by positivity
  have hr : 0 < (16 * (1 + C * M) * a)⁻¹ := by positivity
  have he : (16 * (1 + C * M) * a)⁻¹ * a = (16 * (1 + C * M))⁻¹ := by
    field_simp
  refine ⟨hr, mul_nonneg hr.le ha.le, ?_, ?_⟩
  · rw [he, inv_eq_one_div]
    apply (div_le_iff₀ hd).mpr
    nlinarith
  · rw [he, inv_eq_one_div, ← mul_div_assoc, ← mul_div_assoc]
    apply (div_le_iff₀ hd).mpr
    nlinarith

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace AVRegularity.CycleEvolution

/-! Bounded pointwise scalar limits converge strongly in temporal L². -/

/-- Scalar square difference estimate, isolated from the Bochner carrier. -/
theorem cellScalar_square_difference (x y : ℝ) : (x - y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  nlinarith [sq_nonneg (x + y)]

/-- A uniform scalar square budget gives an L² limit and convergence of squared differences. -/
theorem cellScalar_bounded_L2_limit {μ : Measure ℝ} [IsFiniteMeasure μ]
    (f : ℕ → ℝ → ℝ) (hf : ∀ n, MemLp (f n) 2 μ) (p : ℝ → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n, ∀ᵐ t ∂μ, (f n t) ^ 2 ≤ C)
    (hl : ∀ᵐ t ∂μ, Tendsto (fun n => f n t) atTop (𝓝 (p t))) :
    MemLp p 2 μ ∧ Tendsto (fun n => ∫ t, (f n t - p t) ^ 2 ∂μ) atTop (𝓝 0) := by
  have hpmeas := aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hf n).aestronglyMeasurable) hl
  have hba := ae_all_iff.mpr hb
  have hpbound : ∀ᵐ t ∂μ, (p t) ^ 2 ≤ C := by
    filter_upwards [hl, hba] with t ht hbt
    exact le_of_tendsto (ht.pow 2) (Filter.Eventually.of_forall (fun n => hbt n))
  have hp : MemLp p 2 μ := by
    apply (memLp_const (C + 1)).of_le hpmeas
    filter_upwards [hpbound] with t ht
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (by linarith : 0 ≤ C + 1)]
    apply cellNorm_le_budget_add_one
    simpa only [sq_abs] using ht
  refine ⟨hp, ?_⟩
  have hi := tendsto_integral_of_dominated_convergence (fun _ => 4 * C)
    (fun n => ((hf n).aestronglyMeasurable.sub hpmeas).pow 2) (integrable_const (4 * C))
    (fun n => by
      filter_upwards [hb n, hpbound] with t hnt hpt
      change ‖(f n t - p t) ^ 2‖ ≤ 4 * C
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact (cellScalar_square_difference (f n t) (p t)).trans (by linarith))
    (by
      filter_upwards [hl] with t ht
      simpa only [Pi.pow_apply, Pi.sub_apply, sub_self, zero_pow (by decide : 2 ≠ 0)] using
        (ht.sub (tendsto_const_nhds (x := p t))).pow 2)
  simpa only [Pi.pow_apply, Pi.sub_apply, integral_zero] using hi

/-- Vanishing square difference integrals give norm convergence of temporal scalar L² classes. -/
theorem cellScalar_L2_tendsto_of_square_integrals {μ : Measure ℝ}
    (f : ℕ → ℝ → ℝ) (hf : ∀ n, MemLp (f n) 2 μ) (p : ℝ → ℝ) (hp : MemLp p 2 μ)
    (hl : Tendsto (fun n => ∫ t, (f n t - p t) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hp.toLp p)) := by
  have he (n : ℕ) : ‖(hf n).toLp (f n) - hp.toLp p‖ ^ 2 = ∫ t, (f n t - p t) ^ 2 ∂μ := by
    rw [← MemLp.toLp_sub]
    have hn := cellTimeL2_norm_sq_integral (f n - p) ((hf n).sub hp)
    simpa only [Pi.sub_apply, Real.norm_eq_abs, sq_abs] using hn
  have hsq : Tendsto (fun n => ‖(hf n).toLp (f n) - hp.toLp p‖ ^ 2) atTop (𝓝 0) := by
    simp_rw [he]
    exact hl
  have hroot := (Real.continuous_sqrt.tendsto 0).comp hsq
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using hroot

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! Positive triangular convolutions are bounded by the product of the corresponding full sums. -/

/-- The triangular metric-state convolution injects into the full positive-metric/state rectangle. -/
theorem cellJetConvolution_le_product (K : ℕ) (a b : ℕ × ℕ → ℝ≥0∞) :
    (∑ α ∈ jetIndices K, ∑ β ∈ cellJetFluxIndices α,
      a β * b (α.1 - β.1, α.2 - β.2)) ≤
    (∑ β ∈ (jetIndices K).erase 0, a β) * (∑ γ ∈ jetIndices K, b γ) := by
  classical
  let S := (jetIndices K).sigma cellJetFluxIndices
  let f : (Σ _ : ℕ × ℕ, ℕ × ℕ) → (ℕ × ℕ) × (ℕ × ℕ) :=
    fun p => (p.2, (p.1.1 - p.2.1, p.1.2 - p.2.2))
  have hf : Set.InjOn f (↑S : Set (Σ _ : ℕ × ℕ, ℕ × ℕ)) := by
    intro p hp q hq he
    have hp' := Finset.mem_sigma.mp hp
    have hq' := Finset.mem_sigma.mp hq
    have hβ : p.2 = q.2 := congrArg Prod.fst he
    have hγ : (p.1.1 - p.2.1, p.1.2 - p.2.2) =
        (q.1.1 - q.2.1, q.1.2 - q.2.2) := congrArg Prod.snd he
    have hα : p.1 = q.1 := by
      rw [← cellJetFluxIndices_recover hp'.2, ← cellJetFluxIndices_recover hq'.2]
      exact congrArg₂ (fun β γ : ℕ × ℕ => β + γ) hβ hγ
    cases p
    cases q
    dsimp at hα hβ
    cases hα
    cases hβ
    rfl
  have hsub : S.image f ⊆ (jetIndices K).erase 0 ×ˢ jetIndices K := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨ha, hb⟩ := Finset.mem_sigma.mp hq
    exact Finset.mem_product.mpr
      ⟨cellJetFluxIndices_mem_positive ha hb, cellJetFluxIndices_mem_lower ha hb⟩
  calc
    _ = ∑ p ∈ S, a (f p).1 * b (f p).2 := by rw [Finset.sum_sigma]
    _ = ∑ p ∈ S.image f, a p.1 * b p.2 := (Finset.sum_image (f := fun p : (ℕ × ℕ) × (ℕ × ℕ) => a p.1 * b p.2) hf).symm
    _ ≤ ∑ p ∈ (jetIndices K).erase 0 ×ˢ jetIndices K, a p.1 * b p.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => bot_le)
    _ = _ := by rw [Finset.sum_product, Finset.sum_mul_sum]

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Useful consequences of the sharp unit-cell mean-zero Poincaré inequality. -/

/-- One quarter of the gradient dissipation supplies the value-energy rate π². -/
theorem cellMeanZero_gradient_gap (u : TorusHk 1 ℂ) (hm : cellMean (torusHkValueCLM u) = 0) :
    Real.pi ^ 2 * ‖torusHkValueCLM u‖ ^ 2 ≤ (1 / 4) * ∑ j, ‖cellDerivativeCLM j u‖ ^ 2 := by
  have hp := cellH1_meanZero_poincare u hm
  rw [← div_eq_inv_mul] at hp
  have hmul := (le_div_iff₀ (show 0 < 4 * Real.pi ^ 2 by positivity)).mp hp
  calc
    _ = (1 / 4) * (‖torusHkValueCLM u‖ ^ 2 * (4 * Real.pi ^ 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hmul (by norm_num)

/-- The squared mean-zero value consumes less than one eighth of gradient dissipation. -/
theorem cellMeanZero_value_small_gradient (u : TorusHk 1 ℂ)
    (hm : cellMean (torusHkValueCLM u) = 0) :
    ‖torusHkValueCLM u‖ ^ 2 ≤ (1 / 8) * ∑ j, ‖cellDerivativeCLM j u‖ ^ 2 := by
  have hc : (4 * Real.pi ^ 2)⁻¹ ≤ (1 / 8 : ℝ) := by
    rw [← one_div, div_le_iff₀ (show 0 < 4 * Real.pi ^ 2 by positivity)]
    nlinarith [Real.pi_gt_three]
  exact (cellH1_meanZero_poincare u hm).trans
    (mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Actual metric dissipation and the sharp mean-zero spectral gap on the unit cell. -/

/-- The literal unshifted metric dissipation on the H¹ class. -/
def cellMetricEnergy {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    (t : ℝ) (u : TorusHk 1 ℂ) : ℝ :=
  ∑ j : Fin 2, ∑ k : Fin 2, inner ℝ
    (cellMetricEntryCLM hG t j k (cellDerivativeCLM j u)) (cellDerivativeCLM k u)

/-- The half-identity lower metric bound gives half the actual squared gradient norm. -/
theorem cellMetricEnergy_coercive {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : IsCellMetric G) (t : ℝ) (u : TorusHk 1 ℂ) :
    (1 / 2) * ∑ j, ‖cellDerivativeCLM j u‖ ^ 2 ≤ cellMetricEnergy hG t u := by
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
  have h := integral_mono_ae (hds.const_mul (1 / 2)) hfss (Filter.Eventually.of_forall (fun x => by
    simpa only [f, Fin.sum_univ_two, Complex.add_re] using
      cellMetric_complex_coercive hG t x (fun j => cellDerivativeCLM j u x)))
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

/-- Metric dissipation bounds the mean-zero value with spectral gap 2π². -/
theorem cellMetricEnergy_meanZero_gap {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : IsCellMetric G) (t : ℝ) (u : TorusHk 1 ℂ)
    (hm : cellMean (torusHkValueCLM u) = 0) :
    2 * Real.pi ^ 2 * ‖torusHkValueCLM u‖ ^ 2 ≤ cellMetricEnergy hG t u := by
  have hp := cellH1_meanZero_poincare u hm
  rw [← div_eq_inv_mul] at hp
  have hπ : 0 < 4 * Real.pi ^ 2 := by positivity
  have hmul := (le_div_iff₀ hπ).mp hp
  calc
    _ = (1 / 2) * (‖torusHkValueCLM u‖ ^ 2 * (4 * Real.pi ^ 2)) := by ring
    _ ≤ (1 / 2) * ∑ j, ‖cellDerivativeCLM j u‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hmul (by norm_num)
    _ ≤ cellMetricEnergy hG t u := cellMetricEnergy_coercive hG t u

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.CycleEvolution

/-! Vanishing metric-gradient perturbations in the uniformly local source norm. -/

/-- The zero metric has zero entrywise size. -/
theorem cellMetricSupNorm_zero : cellMetricSupNorm 0 = 0 := by simp [cellMetricSupNorm]

/-- A fixed bounded coefficient sends energy-small states to uniformly local small fluxes. -/
theorem cellMetricFlux_tendsto_zero_state {P : Type*} (l : Filter P)
    (A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (E : P → ℝ → RawJet2 1 ℂ)
    (hA : cellMetricSupNorm A < ⊤ ∧ Measurable (Function.uncurry A))
    (hE : ∀ p a, AEStronglyMeasurable (fun z : ℝ × Vec 2 => E p z.1 a z.2)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hEc : Tendsto (fun p => cellEnergyNorm univ (E p)) l (𝓝 0)) :
    Tendsto (fun p => cellUlNorm univ (cellMetricFlux A (E p))) l (𝓝 0) := by
  have hfin : 2 * cellMetricSupNorm A ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hA.1.ne
  have hl := ENNReal.Tendsto.const_mul hEc (a := 2 * cellMetricSupNorm A) (Or.inr hfin)
  have hlim : Tendsto (fun p => 2 * cellMetricSupNorm A * cellEnergyNorm univ (E p))
      l (𝓝 0) := by simpa only [mul_zero] using hl
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) (fun p => cellMetricFlux_ul_bound univ A hA.1 hA.2 (E p) (hE p))

/-- A norm-small metric multiplied by an energy-continuous state gives a norm-small flux. -/
theorem cellMetricFlux_tendsto_zero_metric {P : Type*} (l : Filter P)
    (A : P → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (E : P → ℝ → RawJet2 1 ℂ) (D : ℝ → RawJet2 1 ℂ)
    (hA : ∀ p, cellMetricSupNorm (A p) < ⊤ ∧ Measurable (Function.uncurry (A p)))
    (hD : cellEnergyNorm univ D < ⊤)
    (hEm : ∀ p a, AEStronglyMeasurable (fun z : ℝ × Vec 2 => E p z.1 a z.2)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hDm : ∀ a, AEStronglyMeasurable (fun z : ℝ × Vec 2 => D z.1 a z.2)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hAc : Tendsto (fun p => cellMetricSupNorm (A p)) l (𝓝 0))
    (hEc : Tendsto (fun p => cellEnergyNorm univ (E p - D)) l (𝓝 0)) :
    Tendsto (fun p => cellUlNorm univ (cellMetricFlux (A p) (E p))) l (𝓝 0) := by
  have hb : cellMetricSupNorm (0 : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) < ⊤ ∧
      Measurable (Function.uncurry (0 : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)) :=
    ⟨by rw [cellMetricSupNorm_zero]; exact ENNReal.zero_lt_top, measurable_const⟩
  have hc : Tendsto (fun p => cellMetricSupNorm (A p - 0)) l (𝓝 0) := by
    simpa only [sub_zero] using hAc
  simpa only [cellMetricFlux_zero_metric, sub_zero] using
    cellMetricFlux_tendsto l A 0 E D hA hb hD hEm hDm hc hEc

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Absolute product L2 summability of actual value and gradient trajectories on finite intervals. -/

/-- Absolutely energy-summable actual solution values are absolutely product L2 summable locally in time. -/
theorem cellSolutionSeries_value_interval_L2 {J : Type*} [Countable J]
    (C : J → CellCoefficients) (src : J → ℝ → Vec 2 → ℂ)
    (F : J → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D : J → ℝ → RawJet2 1 ℂ)
    (hD : ∀ j, IsCellSolution Set.univ (C j) (src j) (F j) (D j))
    (hs : (∑' j, cellEnergyNorm Set.univ (D j)) < ⊤) (a b : ℝ) :
    (∑' j, eLpNorm (Function.uncurry (cellValue (D j))) 2
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict AVenhance.unitCube))) < ⊤ := by
  have hm j : AEStronglyMeasurable (Function.uncurry (cellValue (D j)))
      ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)) :=
    (hD j).2.2.2.1 (valueIndex2 1)
  have hb j : cellUlNorm Set.univ (cellValue (D j)) ≤ cellEnergyNorm Set.univ (D j) :=
    cellUlNorm_le_uniform_cellL2Norm _ _ (fun t => cellValue_cellL2Norm_le_energy (D j) t)
  exact cellUlSeries_interval_eLpNorm_tsum_lt_top (fun j => cellValue (D j)) hm
    ((ENNReal.tsum_le_tsum hb).trans_lt hs) a b

/-- Absolutely energy-summable actual solution gradients are absolutely product L2 summable locally in time. -/
theorem cellSolutionSeries_gradient_interval_L2 {J : Type*} [Countable J]
    (C : J → CellCoefficients) (src : J → ℝ → Vec 2 → ℂ)
    (F : J → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D : J → ℝ → RawJet2 1 ℂ)
    (hD : ∀ j, IsCellSolution Set.univ (C j) (src j) (F j) (D j))
    (hs : (∑' j, cellEnergyNorm Set.univ (D j)) < ⊤) (a b : ℝ) :
    (∑' j, eLpNorm (fun p : ℝ × Vec 2 => cellGradient (D j p.1) p.2) 2
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict AVenhance.unitCube))) < ⊤ := by
  have hm j := cellRawGradient_aestronglyMeasurable Set.univ (D j) (hD j).2.2.2.1
  have hb j : cellUlNorm Set.univ (fun t => cellGradient (D j t)) ≤ cellEnergyNorm Set.univ (D j) :=
    le_add_left le_rfl
  simpa only [Function.uncurry_def] using
    cellUlSeries_interval_eLpNorm_tsum_lt_top (fun j t => cellGradient (D j t)) hm
      ((ENNReal.tsum_le_tsum hb).trans_lt hs) a b

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open scoped BigOperators
namespace AVRegularity.CycleEvolution

/-! A uniform finite geometric bound for positive two-coordinate indices. -/

/-- Every finite geometric prefix is bounded by its first term plus twice its ratio. -/
theorem finiteGeometric_small_bound {x : ℝ} (hx : 0 ≤ x) (hs : x ≤ 1 / 2) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), x ^ i) ≤ 1 + 2 * x := by
  induction n with
  | zero => simp; positivity
  | succ n ih =>
    have he : (∑ i ∈ Finset.range (n + 1 + 1), x ^ i) =
        x * (∑ i ∈ Finset.range (n + 1), x ^ i) + 1 := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp only [pow_succ', pow_zero]
    rw [he]
    calc
      _ ≤ x * (1 + 2 * x) + 1 := by gcongr
      _ ≤ 1 + 2 * x := by nlinarith

/-- The sum over any finite positive total-order triangle is at most eight times the ratio. -/
theorem finiteGeometric_positive_triangle {x : ℝ} (hx : 0 ≤ x) (hs : x ≤ 1 / 2) (K : ℕ) :
    (∑ α ∈ (jetIndices K).erase 0, x ^ (α.1 + α.2)) ≤ 8 * x := by
  have hsub : jetIndices K ⊆ Finset.range (K + 1) ×ˢ Finset.range (K + 1) := by
    intro α ha
    exact (Finset.mem_filter.mp ha).1
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun α _ _ => pow_nonneg hx (α.1 + α.2))
  have hrect : (∑ α ∈ Finset.range (K + 1) ×ˢ Finset.range (K + 1),
      x ^ (α.1 + α.2)) = (∑ i ∈ Finset.range (K + 1), x ^ i) ^ 2 := by
    rw [Finset.sum_product, pow_two, Finset.sum_mul_sum]
    simp only [pow_add]
  rw [hrect] at hsum
  have hn : 0 ≤ ∑ i ∈ Finset.range (K + 1), x ^ i :=
    Finset.sum_nonneg (fun i _ => pow_nonneg hx i)
  have hb := finiteGeometric_small_bound hx hs K
  have hz : (0 : ℕ × ℕ) ∈ jetIndices K :=
    (mem_jetIndices_iff K 0).mpr (by change 0 + 0 ≤ K; omega)
  have he := Finset.sum_erase_add (jetIndices K)
    (fun α => x ^ (α.1 + α.2)) hz
  simp only [Prod.fst_zero, Prod.snd_zero, zero_add, pow_zero] at he
  nlinarith

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace AVRegularity.CycleEvolution

/-! Identify bounded pointwise scalar moments of a weak temporal L² limit. -/

/-- A bounded pointwise scalar moment limit agrees a.e. with the corresponding weak L² moment. -/
theorem cellWeak_scalar_moment_identification {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure ℝ} [IsFiniteMeasure μ]
    (u : ℕ → ℝ → E) (hu : ∀ n, MemLp (u n) 2 μ) (U : Lp E 2 μ)
    (hw : ∀ ell : Lp E 2 μ →L[ℝ] ℝ,
      Tendsto (fun n => ell ((hu n).toLp (u n))) atTop (𝓝 (ell U)))
    (L : E →L[ℝ] ℝ) (p : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ n, ∀ᵐ t ∂μ, (L (u n t)) ^ 2 ≤ C)
    (hl : ∀ᵐ t ∂μ, Tendsto (fun n => L (u n t)) atTop (𝓝 (p t))) :
    ∀ᵐ t ∂μ, L (U t) = p t := by
  let f := fun n t => L (u n t)
  have hf (n : ℕ) : MemLp (f n) 2 μ := by
    simpa only [f, Function.comp_def] using L.comp_memLp' (hu n)
  obtain ⟨hp, hsquare⟩ := cellScalar_bounded_L2_limit f hf p C hC hb hl
  have hstrong := cellScalar_L2_tendsto_of_square_integrals f hf p hp hsquare
  let A := L.compLpL 2 μ
  have he (n : ℕ) : (hf n).toLp (f n) = A ((hu n).toLp (u n)) := by
    apply Lp.ext
    filter_upwards [(hf n).coeFn_toLp, (hu n).coeFn_toLp,
      L.coeFn_compLpL ((hu n).toLp (u n))] with t hft hut hat
    rw [hft, hat, hut]
  have hs : Tendsto (fun n => A ((hu n).toLp (u n))) atTop (𝓝 (hp.toLp p)) := by
    simpa only [he] using hstrong
  let q := A U - hp.toLp p
  let ell := (innerSL ℝ q).comp A
  have hweak := hw ell
  have htest := ((innerSL ℝ q).continuous.tendsto (hp.toLp p)).comp hs
  have heval : inner ℝ q (A U) = inner ℝ q (hp.toLp p) :=
    tendsto_nhds_unique hweak htest
  have hq : q = 0 := by
    have hi : inner ℝ q q = 0 := by
      change inner ℝ q (A U - hp.toLp p) = 0
      rw [inner_sub_right, heval, sub_self]
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp (by simpa only [real_inner_self_eq_norm_sq] using hi))
  have heq : A U = hp.toLp p := sub_eq_zero.mp hq
  filter_upwards [L.coeFn_compLpL U, hp.coeFn_toLp] with t hat hpt
  change A U t = L (U t) at hat
  rw [heq] at hat
  exact hat.symm.trans hpt

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Complex fixed-test time increments reconstructed from real Hilbert weak equations. -/

/-- Complex fixed-test dual pairing of the real H¹ Riesz derivative. -/
def cellDualComplexPair (g z : TorusHk 1 ℂ) : ℂ :=
  (inner ℝ g z : ℂ) + Complex.I * (inner ℝ g (cellH1Scalar Complex.I z) : ℂ)

/-- The real component is the original fixed-test pairing. -/
theorem cellDualComplexPair_re (g z : TorusHk 1 ℂ) :
    (cellDualComplexPair g z).re = inner ℝ g z := by simp [cellDualComplexPair]

/-- The imaginary component is the pairing with i times the test. -/
theorem cellDualComplexPair_im (g z : TorusHk 1 ℂ) :
    (cellDualComplexPair g z).im = inner ℝ g (cellH1Scalar Complex.I z) := by
  simp [cellDualComplexPair]

/-- Square-integrable dual derivatives give integrable complex fixed-test pairings. -/
theorem cellDualComplexPair_intervalIntegrable {a b s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (g : ℝ → TorusHk 1 ℂ) (hg : MemLp g 2 (volume.restrict (Icc a b)))
    (z : TorusHk 1 ℂ) : IntervalIntegrable (fun r => cellDualComplexPair (g r) z) volume s t := by
  have h1 := cellWeakPair_intervalIntegrable hs ht hst g hg z
  have h2 := cellWeakPair_intervalIntegrable hs ht hst g hg (cellH1Scalar Complex.I z)
  apply intervalIntegrable_iff.mpr
  have he1 := Complex.ofRealCLM.integrable_comp (intervalIntegrable_iff.mp h1)
  have he2 := (Complex.ofRealCLM.integrable_comp (intervalIntegrable_iff.mp h2)).const_mul Complex.I
  exact he1.add he2

/-- The complex trace equation follows from the two real equations for a test and its i multiple. -/
theorem CellWeakHilbertCurve.complex_increment {a b : ℝ}
    {u : ℝ → ComplexCellL2} {slice g : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice g)
    (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (z : TorusHk 1 ℂ) :
    cellComplexPair (u t) (torusHkValueCLM z) - cellComplexPair (u s) (torusHkValueCLM z) =
      ∫ r in s..t, cellDualComplexPair (g r) z := by
  have hi := cellDualComplexPair_intervalIntegrable hs ht hst g h.dual z
  apply Complex.ext
  · have he := Complex.reCLM.intervalIntegral_comp_comm hi
    change (∫ r in s..t, (cellDualComplexPair (g r) z).re) =
      (∫ r in s..t, cellDualComplexPair (g r) z).re at he
    rw [Complex.sub_re, cellComplexPair_re, cellComplexPair_re, ← he]
    simp only [cellDualComplexPair_re]
    exact h.increment s hs t ht hst z
  · have he := Complex.imCLM.intervalIntegral_comp_comm hi
    change (∫ r in s..t, (cellDualComplexPair (g r) z).im) =
      (∫ r in s..t, cellDualComplexPair (g r) z).im at he
    rw [Complex.sub_im, cellComplexPair_im, cellComplexPair_im, ← he]
    simp only [cellDualComplexPair_im]
    simpa only [cellH1Scalar_value] using h.increment s hs t ht hst (cellH1Scalar Complex.I z)

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Every compatible energy carrier with an actual weak solution trace has that solution's H1 state. -/

theorem cellFiniteEnergyCarrier_state_eq {a b : ℝ}
    (u : ℝ → ComplexCellL2) (slice g : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice g) (z : CellFiniteEnergyCarrier a b)
    (hz : ∀ t : CellCompactTime a b, z.val.1 t = u t.val) :
    ∀ᵐ t ∂(volume : Measure (CellCompactTime a b)),
      cellComplexH1RealEquiv (z.val.2 t) = slice t.val := by
  obtain ⟨w, hw, hs⟩ := cellWeakHilbertCurve_exists_energyCarrier a b u slice g h
  have he : z = w := by
    apply cellFiniteEnergyCarrier_trace_injective a b
    apply ContinuousMap.ext
    intro t
    exact (hz t).trans (hw t).symm
  rw [he]
  exact hs

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Actual measurability and uniformly local bounds for the literal metric-jet forcing. -/

/-- The metric-jet forcing is jointly almost measurable if its finitely many coefficients and states are. -/
theorem cellMetricJetFlux_aestronglyMeasurable
    (Gj : ℕ × ℕ → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (cj : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (α : ℕ × ℕ)
    (hGm : ∀ β ∈ cellJetFluxIndices α, Measurable (Function.uncurry (Gj β)))
    (hcm : ∀ β ∈ cellJetFluxIndices α, ∀ a,
      AEStronglyMeasurable (fun p : ℝ × Vec 2 => cj (α.1 - β.1, α.2 - β.2) p.1 a p.2)
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube))) :
    AEStronglyMeasurable (Function.uncurry (cellMetricJetFlux Gj cj α))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) := by
  rw [cellMetricJetFlux_eq_sum]
  simpa only [Function.uncurry_def, Finset.sum_apply, Pi.smul_def] using
    cellFinite_sum_aestronglyMeasurable (cellJetFluxIndices α)
      (fun β (p : ℝ × Vec 2) => (cellJetChoose α β : ℝ) •
        cellMetricFlux (Gj β) (cj (α.1 - β.1, α.2 - β.2)) p.1 p.2)
      (fun β hβ => (cellMetricFlux_aestronglyMeasurable univ (Gj β)
        (cj (α.1 - β.1, α.2 - β.2)) (hGm β hβ) (hcm β hβ)).const_smul (cellJetChoose α β : ℝ))

/-- The literal jet forcing is bounded by its finite binomial convolution of coefficient and state norms. -/
theorem cellMetricJetFlux_ul_bound
    (Gj : ℕ × ℕ → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (cj : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (α : ℕ × ℕ)
    (hG : ∀ β ∈ cellJetFluxIndices α, cellMetricSupNorm (Gj β) < ⊤)
    (hGm : ∀ β ∈ cellJetFluxIndices α, Measurable (Function.uncurry (Gj β)))
    (hcm : ∀ β ∈ cellJetFluxIndices α, ∀ a,
      AEStronglyMeasurable (fun p : ℝ × Vec 2 => cj (α.1 - β.1, α.2 - β.2) p.1 a p.2)
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube))) :
    cellUlNorm univ (cellMetricJetFlux Gj cj α) ≤
      ∑ β ∈ cellJetFluxIndices α, (cellJetChoose α β : ℝ≥0∞) *
        (2 * cellMetricSupNorm (Gj β) * cellEnergyNorm univ (cj (α.1 - β.1, α.2 - β.2))) := by
  rw [cellMetricJetFlux_eq_sum]
  refine (cellUlNorm_finset_sum_le (cellJetFluxIndices α) _ ?_).trans ?_
  · intro β hβ
    exact (cellMetricFlux_aestronglyMeasurable univ (Gj β)
      (cj (α.1 - β.1, α.2 - β.2)) (hGm β hβ) (hcm β hβ)).const_smul (cellJetChoose α β : ℝ)
  · apply Finset.sum_le_sum
    intro β hβ
    have hscale := cellUlNorm_smul univ (cellJetChoose α β : ℝ)
      (cellMetricFlux (Gj β) (cj (α.1 - β.1, α.2 - β.2)))
      (cellMetricFlux_aestronglyMeasurable univ (Gj β)
        (cj (α.1 - β.1, α.2 - β.2)) (hGm β hβ) (hcm β hβ))
    rw [Real.enorm_of_nonneg (Nat.cast_nonneg _), ENNReal.ofReal_natCast] at hscale
    have hflux := cellMetricFlux_ul_bound univ (Gj β) (hG β hβ) (hGm β hβ)
      (cj (α.1 - β.1, α.2 - β.2)) (hcm β hβ)
    exact hscale.trans (by gcongr)

/-- Every finite triangular jet forcing is an admissible uniformly local source. -/
theorem cellMetricJetFlux_ul_lt_top
    (Gj : ℕ × ℕ → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (cj : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (α : ℕ × ℕ)
    (hG : ∀ β ∈ cellJetFluxIndices α, cellMetricSupNorm (Gj β) < ⊤)
    (hGm : ∀ β ∈ cellJetFluxIndices α, Measurable (Function.uncurry (Gj β)))
    (hc : ∀ β ∈ cellJetFluxIndices α,
      cellEnergyNorm univ (cj (α.1 - β.1, α.2 - β.2)) < ⊤)
    (hcm : ∀ β ∈ cellJetFluxIndices α, ∀ a,
      AEStronglyMeasurable (fun p : ℝ × Vec 2 => cj (α.1 - β.1, α.2 - β.2) p.1 a p.2)
        ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube))) :
    cellUlNorm univ (cellMetricJetFlux Gj cj α) < ⊤ := by
  rw [cellMetricJetFlux_eq_sum]
  apply cellUlNorm_finset_sum_lt_top
  · intro β hβ
    exact (cellMetricFlux_aestronglyMeasurable univ (Gj β)
      (cj (α.1 - β.1, α.2 - β.2)) (hGm β hβ) (hcm β hβ)).const_smul (cellJetChoose α β : ℝ)
  · intro β hβ
    have hm := cellMetricFlux_aestronglyMeasurable univ (Gj β)
      (cj (α.1 - β.1, α.2 - β.2)) (hGm β hβ) (hcm β hβ)
    have hflux := (cellMetricFlux_ul_bound univ (Gj β) (hG β hβ) (hGm β hβ)
      (cj (α.1 - β.1, α.2 - β.2)) (hcm β hβ)).trans_lt
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) (hG β hβ)) (hc β hβ))
    exact (cellUlNorm_smul univ (cellJetChoose α β : ℝ) _ hm).trans_lt
      (ENNReal.mul_lt_top enorm_lt_top hflux)

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped BigOperators
namespace AVRegularity.CycleEvolution

/-! Exact next-jet identities for the differentiated proper metric flux. -/

/-- The finite bilinear derivative of a literal proper metric-jet flux. -/
def cellMetricJetFluxDerivative
    (Gj : ℕ × ℕ → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (cj : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (α ε : ℕ × ℕ) :
    ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ) :=
  ∑ β ∈ cellJetFluxIndices α, (cellJetChoose α β : ℝ) •
    (cellMetricFlux (Gj (β + ε)) (cj (α.1 - β.1, α.2 - β.2)) +
      cellMetricFlux (Gj β) (cj ((α.1 - β.1, α.2 - β.2) + ε)))

/-- The derivative of the zeroth coefficient closes the first literal next-jet flux. -/
theorem cellMetricJetFluxDerivative_first
    (Gj : ℕ × ℕ → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (cj : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (α : ℕ × ℕ) :
    cellMetricJetFluxDerivative Gj cj α (1, 0) + cellMetricFlux (Gj (1, 0)) (cj α) =
      cellMetricJetFlux Gj cj (α.1 + 1, α.2) := by
  rw [cellMetricJetFlux_eq_sum]
  simpa only [cellMetricJetFluxDerivative, cellJetFluxIndices, cellJetChoose,
    Nat.cast_smul_eq_nsmul, Prod.add_def, add_zero, Prod.eta] using
    binomialConvolution_proper_first (fun β γ => cellMetricFlux (Gj β) (cj γ)) α.1 α.2

/-- The derivative of the zeroth coefficient closes the second literal next-jet flux. -/
theorem cellMetricJetFluxDerivative_second
    (Gj : ℕ × ℕ → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (cj : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (α : ℕ × ℕ) :
    cellMetricJetFluxDerivative Gj cj α (0, 1) + cellMetricFlux (Gj (0, 1)) (cj α) =
      cellMetricJetFlux Gj cj (α.1, α.2 + 1) := by
  rw [cellMetricJetFlux_eq_sum]
  simpa only [cellMetricJetFluxDerivative, cellJetFluxIndices, cellJetChoose,
    Nat.cast_smul_eq_nsmul, Prod.add_def, add_zero, Prod.eta] using
    binomialConvolution_proper_second (fun β γ => cellMetricFlux (Gj β) (cj γ)) α.1 α.2

end AVRegularity.CycleEvolution
end
end
