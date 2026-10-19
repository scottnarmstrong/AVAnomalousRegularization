-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.CellEnergyOperator
public import AVRegularity.CycleEvolution.CellSpatialEnergy
import AVRegularity.CycleEvolution.CellDriftSmoothEnergy
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Module.Constructions

section
@[expose] public noncomputable section
namespace AVRegularity.CycleEvolution

/-! A named complete complex energy space with exactly the compatible trace and H1 state norm. -/

def CellEnergySpace (a b : ℝ) := CellFiniteEnergyCarrier a b

instance cellEnergySpace_normedAddCommGroup (a b : ℝ) : NormedAddCommGroup (CellEnergySpace a b) :=
  inferInstanceAs (NormedAddCommGroup (CellFiniteEnergyCarrier a b))

instance cellEnergySpace_normedSpace (a b : ℝ) : NormedSpace ℂ (CellEnergySpace a b) :=
  cellFiniteEnergyCarrier_normedSpace a b

instance cellEnergySpace_completeSpace (a b : ℝ) : CompleteSpace (CellEnergySpace a b) :=
  cellFiniteEnergyCarrier_complete a b

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Negating a scalar negates its genuine periodic H1 action. -/

theorem cellH1Scalar_neg (c : ℂ) (z : TorusHk 1 ℂ) : cellH1Scalar (-c) z = -cellH1Scalar c z := by
  apply Subtype.ext
  apply PiLp.ext
  intro a
  change (cellH1Scalar (-c) z).val a = -((cellH1Scalar c z).val a)
  apply Lp.ext
  filter_upwards [cellH1Scalar_jet_ae (-c) z a, cellH1Scalar_jet_ae c z a,
    Lp.coeFn_neg ((cellH1Scalar c z).val a)] with x hn hc he
  rw [hn, he]
  change -c * z.val a x = -((cellH1Scalar c z).val a x)
  rw [hc, neg_mul]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The metric perturbation flux is almost measurable and uniformly locally bounded. -/

/-- The divergence source produced by changing the metric. -/
def cellMetricFlux (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (D : ℝ → RawJet2 1 ℂ) : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ) :=
  fun t x => cellMetricFluxVector (G t x) (cellGradient (D t) x)

/-- Metric fluxes have the joint almost measurability required for the extended inverse. -/
theorem cellMetricFlux_aestronglyMeasurable (I : Set ℝ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (D : ℝ → RawJet2 1 ℂ)
    (hG : Measurable (Function.uncurry G))
    (hD : ∀ a, AEStronglyMeasurable (fun p : ℝ × Vec 2 => D p.1 a p.2)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    AEStronglyMeasurable (Function.uncurry (cellMetricFlux G D))
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) := by
  apply cellFiniteArray_aestronglyMeasurable
  intro i
  apply cellFinite_sum_aestronglyMeasurable Finset.univ
  intro j _
  have hm : Measurable (fun p : ℝ × Vec 2 => (G p.1 p.2 i j : ℂ)) :=
    Complex.measurable_ofReal.comp
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hG))
  exact hm.aestronglyMeasurable.mul (hD ⟨⟨1, by decide⟩, fun _ => j⟩)

/-- The finite entrywise metric size bounds each real entry. -/
theorem cellMetricSupNorm_entry_toReal
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : cellMetricSupNorm G < ⊤) (t : ℝ) (x : Vec 2) (i j : Fin 2) :
    |G t x i j| ≤ (cellMetricSupNorm G).toReal := by
  have h := ENNReal.toReal_mono hG.ne (cellMetricSupNorm_entry G t x i j)
  simpa only [enorm, ENNReal.coe_toReal, coe_nnnorm, Real.norm_eq_abs] using h

/-- Pointwise metric fluxes obey the dimension-two matrix norm bound. -/
theorem cellMetricFlux_norm_le
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : cellMetricSupNorm G < ⊤) (D : ℝ → RawJet2 1 ℂ) (t : ℝ) (x : Vec 2) :
    ‖cellMetricFlux G D t x‖ ≤ 2 * (cellMetricSupNorm G).toReal *
      ‖cellGradient (D t) x‖ :=
  cellMetricFluxVector_norm_le (G t x) _ ENNReal.toReal_nonneg
    (cellMetricSupNorm_entry_toReal G hG t x) _

/-- Metric perturbations turn energy fields into admissible uniformly local flux sources. -/
theorem cellMetricFlux_ul_bound (I : Set ℝ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : cellMetricSupNorm G < ⊤) (hGm : Measurable (Function.uncurry G))
    (D : ℝ → RawJet2 1 ℂ)
    (hD : ∀ a, AEStronglyMeasurable (fun p : ℝ × Vec 2 => D p.1 a p.2)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    cellUlNorm I (cellMetricFlux G D) ≤
      2 * cellMetricSupNorm G * cellEnergyNorm I D := by
  have hgrad := cellFiniteArray_aestronglyMeasurable
    (fun (p : ℝ × Vec 2) (j : Fin 2) => cellGradComp (D p.1) j p.2)
    (fun j => hD ⟨⟨1, by decide⟩, fun _ => j⟩)
  have h := cellUlNorm_le_mul I (cellMetricFlux G D) (fun t => cellGradient (D t))
    (2 * (cellMetricSupNorm G).toReal) (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)
    (cellMetricFlux_aestronglyMeasurable I G D hGm hD) hgrad
    (cellMetricFlux_norm_le G hG D)
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
    ENNReal.ofReal_toReal hG.ne] at h
  refine h.trans ?_
  gcongr
  exact le_add_left le_rfl

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Almost-everywhere identification of the genuine dual derivative preserves the weak equation. -/

theorem CellWeakHilbertCurve.dual_congr {a b : ℝ} {u : ℝ → ComplexCellL2}
    {slice g g' : ℝ → TorusHk 1 ℂ} (h : CellWeakHilbertCurve a b u slice g)
    (he : g =ᵐ[volume.restrict (Icc a b)] g') : CellWeakHilbertCurve a b u slice g' := by
  refine ⟨h.trace, h.state, (memLp_congr_ae he).mp h.dual, h.agrees, ?_⟩
  intro s hs t ht hst z
  have hi := h.increment s hs t ht hst z
  rw [intervalIntegral.integral_of_le hst] at hi ⊢
  apply hi.trans
  apply integral_congr_ae
  have he' := he.filter_mono (ae_mono (Measure.restrict_mono
    (Ioc_subset_Icc_self.trans (Icc_subset_Icc hs.1 ht.2)) le_rfl))
  filter_upwards [he'] with r hr
  rw [hr]

/-! The actual continuous cell trace is bounded on every compact time interval. -/

theorem CellWeakHilbertCurve.trace_memLp_top {a b : ℝ}
    {u : ℝ → ComplexCellL2} {slice g : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice g) : MemLp u ⊤ (volume.restrict (Icc a b)) := by
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn h.trace
  apply MemLp.of_bound (h.trace.aestronglyMeasurable measurableSet_Icc) R
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact hR t ht

end AVRegularity.CycleEvolution
end

section
open MeasureTheory
namespace AVRegularity.CycleEvolution

/-! Joint L² realizations of separated time and space factors. -/

/-- A temporal scalar L² function times a spatial vector L² function is jointly L². -/
theorem cellTensor_memLp {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    {f : α → ℝ} {g : β → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 ν) :
    MemLp (fun p : α × β => f p.1 • g p.2) 2 (μ.prod ν) := by
  have hm : AEStronglyMeasurable (fun p : α × β => f p.1 • g p.2) (μ.prod ν) := by
    exact (hf.aestronglyMeasurable.comp_quasiMeasurePreserving
      Measure.quasiMeasurePreserving_fst).smul
      (hg.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hi := hf.norm.integrable_sq.mul_prod hg.norm.integrable_sq
  simpa only [norm_smul, mul_pow] using hi

/-! Conjugation of cell L² fields agrees with conjugation of their complex pairing. -/

theorem cellComplexPair_conjugate (u z : ComplexCellL2) :
    cellComplexPair (cellFiberCLM Complex.conjCLE.toContinuousLinearMap u)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap z) = star (cellComplexPair u z) := by
  have he := Complex.conjCLE.toContinuousLinearMap.integral_comp_comm
    (cellComplex_pairing_integrable u z)
  change (∫ x in AVenhance.unitCube, star (u x * star (z x))) =
    star (cellComplexPair u z) at he
  rw [← he]
  unfold cellComplexPair
  apply integral_congr_ae
  filter_upwards [ContinuousLinearMap.coeFn_compLpL Complex.conjCLE.toContinuousLinearMap u,
    ContinuousLinearMap.coeFn_compLpL Complex.conjCLE.toContinuousLinearMap z] with x hu hz
  change cellFiberCLM Complex.conjCLE.toContinuousLinearMap u x = star (u x) at hu
  change cellFiberCLM Complex.conjCLE.toContinuousLinearMap z x = star (z x) at hz
  rw [hu, hz, star_mul]
  exact mul_comm _ _

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Complex constant-test pairings identify cell means, including the zero classes. -/

/-- The pairing against the constant-one class is the literal cell mean. -/
theorem cellComplexPair_one (u : ComplexCellL2) : cellComplexPair u (cellConstantCLM 1) = cellMean u := by
  apply integral_congr_ae
  filter_upwards [cellConstantCLM_ae 1] with x hx
  simp only [hx, star_one, mul_one]

/-- Pairing against zero vanishes on the actual L² quotient. -/
theorem cellComplexPair_zero_right (u : ComplexCellL2) : cellComplexPair u 0 = 0 := by
  apply Complex.ext
  · rw [cellComplexPair_re, inner_zero_right]
    rfl
  · rw [cellComplexPair_im, map_zero, inner_zero_right]
    rfl

/-- Pairing a zero trial class vanishes. -/
theorem cellComplexPair_zero_left (u : ComplexCellL2) : cellComplexPair 0 u = 0 := by
  apply Complex.ext
  · rw [cellComplexPair_re, inner_zero_left]
    rfl
  · rw [cellComplexPair_im, inner_zero_left]
    rfl

/-- The bounded projection has zero mean for every L² class. -/
theorem cellQ0CLM_mean_zero (u : ComplexCellL2) : cellMean (cellQ0CLM u) = 0 :=
  (integral_congr_ae (cellQ0CLM_ae u)).trans (cellQ0_mean (Lp.memLp u))

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Separating the actual scalar potential from the literal Bloch generator. -/

theorem cellComplexGenerator_potential (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (t : ℝ) (u z : TorusHk 1 ℂ) :
    cellComplexGenerator C hG V hv hb t u z =
      cellComplexGenerator {C with κ := fun _ => 0} hG V hv hb t u z +
        C.κ t * cellComplexPair (torusHkValueCLM u) (torusHkValueCLM z) := by
  simp only [cellComplexGenerator, cellComplexPair_scalar_left, zero_mul, add_zero]
  rfl

end AVRegularity.CycleEvolution
end

section
open AVRegularity.Sobolev
open scoped BigOperators
namespace AVRegularity.CycleEvolution

/-! Complex linearity of the actual scalar and divergence source pairing. -/

theorem cellComplexSource_scalar (θ : Fin 2 → ℂ) (S : ComplexCellL2)
    (F : Fin 2 → ComplexCellL2) (z : TorusHk 1 ℂ) (c : ℂ) :
    cellComplexSource θ (cellScalarCLM c S) (fun j => cellScalarCLM c (F j)) z =
      c * cellComplexSource θ S F z := by
  simp only [cellComplexSource, cellComplexPair_scalar_left, Fin.sum_univ_two]
  ring

end AVRegularity.CycleEvolution
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The transport form commutes with multiplication by i under the real Hilbert convention. -/

theorem cellDriftForm_I_left {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (u z : TorusHk 1 ℂ) :
    cellDriftForm v V hv.1 hb t (cellH1Scalar Complex.I u) z =
      -cellDriftForm v V hv.1 hb t u (cellH1Scalar Complex.I z) := by
  change (∑ j : Fin 2, inner ℝ
    (cellDriftEntryCLM ⟨0, v, 0, 0⟩ V hv.1 hb t j
      (cellDerivativeCLM j (cellH1Scalar Complex.I u))) (torusHkValueCLM z)) =
    -(∑ j : Fin 2, inner ℝ (cellDriftEntryCLM ⟨0, v, 0, 0⟩ V hv.1 hb t j
      (cellDerivativeCLM j u)) (torusHkValueCLM (cellH1Scalar Complex.I z)))
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [cellDrift_pairing_eq_integral, cellDrift_pairing_eq_integral, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [cellH1Scalar_jet_ae Complex.I u ⟨⟨1, by decide⟩, fun _ => j⟩,
    cellH1Scalar_jet_ae Complex.I z (valueIndex2 1)] with x hd hz
  change cellDerivativeCLM j (cellH1Scalar Complex.I u) x = Complex.I * cellDerivativeCLM j u x at hd
  change torusHkValueCLM (cellH1Scalar Complex.I z) x = Complex.I * torusHkValueCLM z x at hz
  rw [hd, hz]
  simp only [star_mul, Complex.star_def, Complex.conj_I]
  rw [← Complex.neg_re]
  congr 1
  ring

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The actual H⁻¹ cell derivative belongs to temporal L². -/

/-- The coefficient bounds and Bochner L² state/source data imply an L² dual derivative. -/
theorem cellDualDerivative_memLp {μ : Measure ℝ}
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (hκ : Measurable C.κ) (hκb : ∀ t, ‖C.κ t‖ ≤ k)
    (f : ℝ → TorusHk 1 ℂ) (hf : MemLp f 2 μ)
    (S : ℝ → ComplexCellL2) (hS : MemLp S 2 μ)
    (F : ℝ → Fin 2 → ComplexCellL2) (hF : ∀ j, MemLp (fun t => F t j) 2 μ) :
    MemLp (fun t => cellDualDerivative C hG V hv hb t (f t) (S t) (F t)) 2 μ := by
  obtain ⟨M, hM, hMb⟩ := cellGeneratorForm_uniform_norm_bound C hG V k hv hb hκb
  let J := ‖torusHkValueCLM (E := ℂ) (K := 1)‖
  let D := fun j => ‖cellShiftedDerivativeCLM (fun i => star (C.θ i)) j‖
  let budget := fun t => M * ‖f t‖ + J * ‖S t‖ + D 0 * ‖F t 0‖ + D 1 * ‖F t 1‖
  have hm : MemLp budget 2 μ := by
    simpa only [budget, Pi.smul_def, smul_eq_mul, Pi.add_def] using
      (((hf.norm.const_smul M).add (hS.norm.const_smul J)).add
        ((hF 0).norm.const_smul (D 0))).add ((hF 1).norm.const_smul (D 1))
  have hmeas := cellDualDerivative_aestronglyMeasurable C hG V hv hb hκ f
    hf.aestronglyMeasurable S hS.aestronglyMeasurable F (fun j => (hF j).aestronglyMeasurable)
  apply hm.of_le hmeas
  apply Filter.Eventually.of_forall
  intro t
  have hbn : 0 ≤ budget t := by dsimp only [budget, J, D]; positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hbn]
  have hn := cellDualDerivative_norm_le C hG V hv hb t (f t) (S t) (F t)
  have hb' := hMb t (f t)
  dsimp only [budget, J, D]
  simp only [Fin.sum_univ_two] at hn
  linarith

end AVRegularity.CycleEvolution
end

section
namespace AVRegularity.CycleEvolution

/-! Linear isometric conversion into the named cell energy operator algebra. -/

def cellEnergyOperatorOfCLM (a b : ℝ) :
    (CellFiniteEnergyCarrier a b →L[ℂ] CellFiniteEnergyCarrier a b) →L[ℂ] CellEnergyOperator a b :=
  ContinuousLinearMap.id ℂ (CellEnergyOperator a b)

/-! Bounded identity conversions between the actual compatible carrier and its named energy space. -/

def cellEnergySpaceOfCarrierCLM (a b : ℝ) : CellFiniteEnergyCarrier a b →L[ℂ] CellEnergySpace a b :=
  ContinuousLinearMap.id ℂ (CellEnergySpace a b)

theorem cellEnergySpaceOfCarrier_eq (a b : ℝ) (z : CellFiniteEnergyCarrier a b) :
    cellEnergySpaceOfCarrierCLM a b z = z := rfl

end AVRegularity.CycleEvolution
end

section
open MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The cell energy carrier is uniquely determined by its continuous L2 trace. -/

theorem cellComplexH1ValueCLM_injective : Function.Injective cellComplexH1ValueCLM := by
  intro u v h
  apply cellComplexH1RealEquiv.injective
  apply TorusHk.ext_value
  exact h

theorem cellFiniteEnergyCarrier_trace_injective (a b : ℝ) :
    Function.Injective (compatibleTraceLpTraceCLM
      (volume : Measure (CellCompactTime a b)) cellComplexH1ValueCLM) :=
  compatibleTraceLpTrace_injective _ _ cellComplexH1ValueCLM_injective

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set
namespace AVRegularity.CycleEvolution

/-! The complete energy carrier has a bounded complex-linear H1 readout on the restricted real time interval. -/

def cellFiniteEnergyTimeStateCLM {a b : ℝ} (hab : a ≤ b) :
    CellFiniteEnergyCarrier a b →L[ℂ] Lp CellComplexH1 2 (volume.restrict (Icc a b)) :=
  (Lp.compMeasurePreservingₗᵢ ℂ (projIcc a b hab)
    (cellCompactTimeProjection_measurePreserving hab)).toContinuousLinearMap.comp
    (compatibleTraceLpStateCLM (volume : Measure (CellCompactTime a b)) cellComplexH1ValueCLM)

def cellFiniteEnergyTimeValueCLM {a b : ℝ} (hab : a ≤ b) :
    CellFiniteEnergyCarrier a b →L[ℂ] Lp ComplexCellL2 2 (volume.restrict (Icc a b)) :=
  (cellComplexH1ValueCLM.compLpL 2 (volume.restrict (Icc a b))).comp
    (cellFiniteEnergyTimeStateCLM hab)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Uniformly local gradient bounds for literal summable raw jet series. -/

/-- The raw jet series inherits the sum of the uniformly local gradient bounds. -/
theorem cellGradientSeries_cellUlNorm_le {J : Type*} [Countable J]
    (I : Set ℝ) (D : J → ℝ → RawJet2 1 ℂ)
    (hD : ∀ j a, AEStronglyMeasurable (fun p : ℝ × Vec 2 => D j p.1 a p.2)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)))
    (hs : (∑' j, cellUlNorm I (fun t => cellGradient (D j t))) < ⊤) :
    cellUlNorm I (fun t => cellGradient (fun a x => ∑' j, D j t a x)) ≤
      ∑' j, cellUlNorm I (fun t => cellGradient (D j t)) := by
  have hg j := cellRawGradient_aestronglyMeasurable I (D j) (hD j)
  have hm := cellRawGradient_aestronglyMeasurable I (fun t a x => ∑' j, D j t a x)
    (cellJetSeries_aestronglyMeasurable I D hD)
  apply iSup_le
  intro a
  let μ := (volume.restrict (Set.Icc a (a + 1) ∩ I)).prod
    (volume.restrict AVenhance.unitCube)
  have hμ : μ ≤ (volume.restrict I).prod (volume.restrict AVenhance.unitCube) :=
    Measure.prod_mono (Measure.restrict_mono Set.inter_subset_right le_rfl) le_rfl
  have hb j : eLpNorm (fun p : ℝ × Vec 2 => cellGradient (D j p.1) p.2) 2 μ ≤
      cellUlNorm I (fun t => cellGradient (D j t)) := by
    have hw := cellUl_window_eq_product I (fun t => cellGradient (D j t)) a ((hg j).mono_measure hμ)
    simp only [Function.uncurry_def] at hw
    rw [← hw]
    exact le_iSup (fun b : ℝ => (∫⁻ t in Set.Icc b (b + 1) ∩ I,
      cellL2Norm (cellGradient (D j t)) ^ 2) ^ (1 / 2 : ℝ)) a
  have hf := cellLpSeries_memLp_bound μ
    (fun (j : J) (p : ℝ × Vec 2) => cellGradient (D j p.1) p.2)
    ((ENNReal.tsum_le_tsum hb).trans_lt hs)
  have he : (fun p : ℝ × Vec 2 => cellGradient (fun b x => ∑' j, D j p.1 b x) p.2) =ᵐ[μ]
      (fun p => ∑' j, cellGradient (D j p.1) p.2) := by
    filter_upwards [hf.2.2] with p hp
    exact cellGradient_tsum_of_summable (fun j => D j p.1) p.2 (Summable.of_norm hp)
  have hw := cellUl_window_eq_product I
    (fun t => cellGradient (fun b x => ∑' j, D j t b x)) a (hm.mono_measure hμ)
  simp only [Function.uncurry_def] at hw
  rw [hw, eLpNorm_congr_ae he]
  exact hf.2.1.trans (ENNReal.tsum_le_tsum hb)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Variable complex scalar actions preserve Bochner measurability and temporal H¹ L². -/

theorem cellH1Scalar_variable_memLp {μ : Measure ℝ}
    (c : ℝ → ℂ) (hc : MemLp c ⊤ μ) (f : ℝ → TorusHk 1 ℂ) (hf : MemLp f 2 μ) :
    MemLp (fun t => cellH1Scalar (c t) (f t)) 2 μ := by
  have hr := Complex.reCLM.comp_memLp' hc
  have hi := Complex.imCLM.comp_memLp' hc
  have hI := (cellH1ScalarCLM Complex.I).comp_memLp' hf
  have hs : MemLp (fun t => (c t).re • f t) 2 μ := hr.smul hf
  have hs' : MemLp (fun t => (c t).im • cellH1Scalar Complex.I (f t)) 2 μ := by
    have hb : MemLp ((fun t => Complex.imCLM (c t)) •
        (fun t => cellH1ScalarCLM Complex.I (f t))) 2 μ := hi.smul hI
    simpa only [Pi.smul_def', cellH1ScalarCLM_apply, Complex.imCLM_apply] using hb
  have ha : MemLp (fun t => (c t).re • f t + (c t).im • cellH1Scalar Complex.I (f t)) 2 μ := by
    simpa only [sub_neg_eq_add, Pi.add_def] using hs.sub hs'.neg
  apply (memLp_congr_ae (Filter.Eventually.of_forall
    (fun t => cellH1Scalar_real_imag (c t) (f t)))).mpr
  exact ha

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Mean-zero inverse trajectories preserve their normalization under absolute energy series. -/

/-- An absolutely energy-summable family of actual inverse trajectories has zero literal mean at every time. -/
theorem cellInverseSeries_mean_zero {J : Type*} [Countable J]
    (C : J → CellCoefficients) (src : J → ℝ → Vec 2 → ℂ)
    (F : J → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D : J → ℝ → RawJet2 1 ℂ)
    (hD : ∀ j, IsCellInverseValue (C j) (src j) (F j) (D j))
    (hs : (∑' j, cellEnergyNorm Set.univ (D j)) < ⊤) (t : ℝ) :
    cellMean (fun x => ∑' j, cellValue (D j) t x) = 0 := by
  have hl : (∑' j, cellL2Norm (cellValue (D j) t)) < ⊤ :=
    (ENNReal.tsum_le_tsum (fun j => cellValue_cellL2Norm_le_energy (D j) t)).trans_lt hs
  rw [cellMean_tsum_of_cellL2Norm (fun j => cellValue (D j) t) hl]
  simp only [(hD _).2.1 t, tsum_zero]

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Bilinear algebra of the metric-gradient flux on raw representatives. -/

/-- The perturbation flux is additive in its metric. -/
theorem cellMetricFlux_add_metric
    (G H : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (D : ℝ → RawJet2 1 ℂ) :
    cellMetricFlux (G + H) D = cellMetricFlux G D + cellMetricFlux H D := by
  funext t x
  apply PiLp.ext
  intro i
  simp only [cellMetricFlux, cellMetricFluxVector, cellGradient, Fin.sum_univ_two,
    Pi.add_apply, Matrix.add_apply, Complex.ofReal_add, PiLp.add_apply]
  ring

/-- The perturbation flux is real linear in its metric. -/
theorem cellMetricFlux_smul_metric (r : ℝ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (D : ℝ → RawJet2 1 ℂ) :
    cellMetricFlux (r • G) D = r • cellMetricFlux G D := by
  funext t x
  apply PiLp.ext
  intro i
  simp only [cellMetricFlux, cellMetricFluxVector, cellGradient, Fin.sum_univ_two,
    Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul, PiLp.smul_apply,
    Complex.real_smul]
  ring

/-- The perturbation flux is additive in the state. -/
theorem cellMetricFlux_add_state
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (D E : ℝ → RawJet2 1 ℂ) :
    cellMetricFlux G (D + E) = cellMetricFlux G D + cellMetricFlux G E := by
  funext t x
  apply PiLp.ext
  intro i
  simp only [cellMetricFlux, cellMetricFluxVector, cellGradient, cellGradComp,
    Fin.sum_univ_two, Pi.add_apply, PiLp.add_apply]
  ring

/-- The perturbation flux is real linear in the state. -/
theorem cellMetricFlux_smul_state (r : ℝ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (D : ℝ → RawJet2 1 ℂ) :
    cellMetricFlux G (r • D) = r • cellMetricFlux G D := by
  funext t x
  apply PiLp.ext
  intro i
  simp only [cellMetricFlux, cellMetricFluxVector, cellGradient, cellGradComp,
    Fin.sum_univ_two, Pi.smul_apply, PiLp.smul_apply, Complex.real_smul]
  ring

/-- The perturbation flux respects metric differences. -/
theorem cellMetricFlux_sub_metric
    (G H : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (D : ℝ → RawJet2 1 ℂ) :
    cellMetricFlux (G - H) D = cellMetricFlux G D - cellMetricFlux H D := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ H, cellMetricFlux_add_metric,
    cellMetricFlux_smul_metric, neg_one_smul, ← sub_eq_add_neg]

/-- The perturbation flux respects state differences. -/
theorem cellMetricFlux_sub_state
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (D E : ℝ → RawJet2 1 ℂ) :
    cellMetricFlux G (D - E) = cellMetricFlux G D - cellMetricFlux G E := by
  rw [sub_eq_add_neg, ← neg_one_smul ℝ E, cellMetricFlux_add_state,
    cellMetricFlux_smul_state, neg_one_smul, ← sub_eq_add_neg]

/-- A product difference separates into coefficient and state differences. -/
theorem cellMetricFlux_difference
    (G H : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (D E : ℝ → RawJet2 1 ℂ) :
    cellMetricFlux G D - cellMetricFlux H E =
      cellMetricFlux (G - H) D + cellMetricFlux H (D - E) := by
  rw [cellMetricFlux_sub_metric, cellMetricFlux_sub_state]
  abel

end AVRegularity.CycleEvolution
end

section
open Homogenization
namespace AVRegularity.CycleEvolution

/-! Divergence forcing enters the slow mean with one Bloch frequency factor. -/

theorem cellBloch_flux_mean_norm_le (θ : Fin 2 → ℂ) (q : ℝ)
    (hθ : ∀ j, ‖θ j‖ ≤ q) (F : Fin 2 → ComplexCellL2) :
    ‖∑ j : Fin 2, Complex.I * θ j * cellMean (F j)‖ ≤ q * (‖F 0‖ + ‖F 1‖) := by
  have hq : 0 ≤ q := (norm_nonneg (θ 0)).trans (hθ 0)
  have hm (j : Fin 2) : ‖cellMean (F j)‖ ≤ ‖F j‖ := by
    simpa only [cellMeanCLM_apply] using cellMeanCLM_norm_le (F j)
  calc
    _ ≤ ∑ j : Fin 2, ‖Complex.I * θ j * cellMean (F j)‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin 2, q * ‖F j‖ := by
      apply Finset.sum_le_sum
      intro j _
      simp only [norm_mul, Complex.norm_I, one_mul]
      exact mul_le_mul (hθ j) (hm j) (norm_nonneg _) hq
    _ = _ := by simp only [Fin.sum_univ_two]; ring

theorem cellBloch_flux_mean_graph_source_norm_le (θ : Fin 2 → ℂ) (q : ℝ)
    (hθ : ∀ j, ‖θ j‖ ≤ q) (F : Fin 2 → ComplexCellL2) (ρ : ComplexCellL2)
    (hρ : ‖ρ‖ ≤ 1) (hq : q ≤ 1) :
    ‖cellScalarCLM (∑ j : Fin 2, Complex.I * θ j * cellMean (F j)) ρ‖ ^ 2 ≤
      2 * ∑ j : Fin 2, ‖F j‖ ^ 2 := by
  have hn : ‖cellScalarCLM (∑ j : Fin 2, Complex.I * θ j * cellMean (F j)) ρ‖ ≤
      ‖F 0‖ + ‖F 1‖ := by
    rw [cellScalarCLM_norm]
    calc
      _ ≤ ‖∑ j : Fin 2, Complex.I * θ j * cellMean (F j)‖ * 1 :=
        mul_le_mul_of_nonneg_left hρ (norm_nonneg _)
      _ = _ := mul_one _
      _ ≤ q * (‖F 0‖ + ‖F 1‖) := cellBloch_flux_mean_norm_le θ q hθ F
      _ ≤ 1 * (‖F 0‖ + ‖F 1‖) := mul_le_mul_of_nonneg_right hq (by positivity)
      _ = _ := one_mul _
  have hp := norm_nonneg (cellScalarCLM (∑ j : Fin 2, Complex.I * θ j * cellMean (F j)) ρ)
  simp only [Fin.sum_univ_two] at hn hp ⊢
  nlinarith [sq_nonneg (‖F 0‖ - ‖F 1‖)]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Complex-linear derivative readouts of the actual periodic H1 energy state. -/

def cellComplexH1DerivativeCLM (j : Fin 2) : CellComplexH1 →L[ℂ] ComplexCellL2 :=
  (PiLp.proj (𝕜 := ℂ) 2 (fun _ : JetIndex2 1 => ComplexCellL2)
    ⟨⟨1, by decide⟩, fun _ => j⟩).comp cellComplexH1Submodule.subtypeL

theorem cellComplexH1DerivativeCLM_eq (j : Fin 2) (u : CellComplexH1) :
    cellComplexH1DerivativeCLM j u = cellDerivativeCLM j (cellComplexH1RealEquiv u) := rfl

def cellFiniteEnergyTimeDerivativeCLM {a b : ℝ} (hab : a ≤ b) (j : Fin 2) :
    CellFiniteEnergyCarrier a b →L[ℂ] Lp ComplexCellL2 2 (volume.restrict (Icc a b)) :=
  ((cellComplexH1DerivativeCLM j).compLpL 2 (volume.restrict (Icc a b))).comp
    (cellFiniteEnergyTimeStateCLM hab)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory
namespace AVRegularity.CycleEvolution

/-! Exact complex Hilbert representation and Cauchy--Schwarz bound of the actual cell pairing. -/

theorem cellComplexPair_eq_inner (u z : ComplexCellL2) :
    cellComplexPair u z = inner ℂ z u := by
  unfold cellComplexPair
  rw [L2.inner_def]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun (x : Homogenization.Vec 2) => by
    change u x * star (z x) = inner ℂ (z x) (u x)
    rw [RCLike.inner_apply]
    rfl)

theorem cellComplexPair_norm_le (u z : ComplexCellL2) :
    ‖cellComplexPair u z‖ ≤ ‖u‖ * ‖z‖ := by
  rw [cellComplexPair_eq_inner, mul_comm ‖u‖ ‖z‖]
  exact norm_inner_le_norm z u

theorem cellFiberConj_norm (u : ComplexCellL2) :
    ‖cellFiberCLM Complex.conjCLE.toContinuousLinearMap u‖ = ‖u‖ := by
  have he := congrArg Complex.re (cellComplexPair_conjugate u u)
  simp only [cellComplexPair_re, Complex.star_def, Complex.conj_re,
    real_inner_self_eq_norm_sq] at he
  nlinarith [norm_nonneg u, norm_nonneg (cellFiberCLM Complex.conjCLE.toContinuousLinearMap u)]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Temporal L² of the actual dual derivative with an almost measurable scalar potential. -/

/-- The coefficient bounds and Bochner L² state/source data imply an L² dual derivative. -/
theorem cellDualDerivative_memLp_aePotential {μ : Measure ℝ}
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (hκ : AEStronglyMeasurable C.κ μ) (hκb : ∀ t, ‖C.κ t‖ ≤ k)
    (f : ℝ → TorusHk 1 ℂ) (hf : MemLp f 2 μ)
    (S : ℝ → ComplexCellL2) (hS : MemLp S 2 μ)
    (F : ℝ → Fin 2 → ComplexCellL2) (hF : ∀ j, MemLp (fun t => F t j) 2 μ) :
    MemLp (fun t => cellDualDerivative C hG V hv hb t (f t) (S t) (F t)) 2 μ := by
  obtain ⟨M, hM, hMb⟩ := cellGeneratorForm_uniform_norm_bound C hG V k hv hb hκb
  let J := ‖torusHkValueCLM (E := ℂ) (K := 1)‖
  let D := fun j => ‖cellShiftedDerivativeCLM (fun i => star (C.θ i)) j‖
  let budget := fun t => M * ‖f t‖ + J * ‖S t‖ + D 0 * ‖F t 0‖ + D 1 * ‖F t 1‖
  have hm : MemLp budget 2 μ := by
    simpa only [budget, Pi.smul_def, smul_eq_mul, Pi.add_def] using
      (((hf.norm.const_smul M).add (hS.norm.const_smul J)).add
        ((hF 0).norm.const_smul (D 0))).add ((hF 1).norm.const_smul (D 1))
  have hmeas := cellDualDerivative_aestronglyMeasurable_aePotential C hG V hv hb hκ f
    hf.aestronglyMeasurable S hS.aestronglyMeasurable F (fun j => (hF j).aestronglyMeasurable)
  apply hm.of_le hmeas
  apply Filter.Eventually.of_forall
  intro t
  have hbn : 0 ≤ budget t := by dsimp only [budget, J, D]; positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hbn]
  have hn := cellDualDerivative_norm_le C hG V hv hb t (f t) (S t) (F t)
  have hb' := hMb t (f t)
  dsimp only [budget, J, D]
  simp only [Fin.sum_univ_two] at hn
  linarith

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleEvolution

/-! Cutoff-independent energy bounds for the actual finite cell equation. -/

/-- Square-integrable curves have integrable squared norm on every finite interval. -/
theorem cellTime_normSq_intervalIntegrable {E : Type*} [NormedAddCommGroup E]
    {a b : ℝ} (hab : a ≤ b) {u : ℝ → E}
    (hu : MemLp u 2 (volume.restrict (Icc a b))) :
    IntervalIntegrable (fun t => ‖u t‖ ^ 2) volume a b := by
  apply intervalIntegrable_iff.mpr
  rw [uIoc_of_le hab]
  exact hu.norm.integrable_sq.mono_measure (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)

/-- Finite variational solutions satisfy the universal cell energy bound.
The source and spatial integrability premises are derived by the actual Galerkin constructor. -/
theorem cellFinite_energy_bound {a b : ℝ} (hab : a ≤ b) (N : ℕ)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (hκ : ∀ t, ‖C.κ t‖ ≤ k)
    (S : ℝ → ComplexCellL2) (F : ℝ → Fin 2 → ComplexCellL2)
    (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (hF : ∀ j, MemLp (fun t => F t j) 2 (volume.restrict (Icc a b)))
    (u du : ℝ → ComplexCellL2) (y : ℝ → CellGalerkinSpace (E := ℂ) N)
    (hy : MemLp (fun t => (y t).val) 2 (volume.restrict (Icc a b)))
    (h : StrongVariationalSolution a b (cellGalerkinValue N).toLinearMap
      (fun t => cellGalerkinForm N (cellGeneratorB C hG V hv hb t))
      (fun t => cellGalerkinSource N (cellSourceFunctional C.θ (S t) (F t)).toLinearMap)
      u du y) :
    ∀ t ∈ Icc a b,
      ‖u t‖ ^ 2 + ∫ s in a..t, (1 / 2) * ∑ j, ‖cellDerivativeCLM j (y s).val‖ ^ 2 ≤
        (‖u a‖ ^ 2 + ∫ s in a..b, ‖S s‖ ^ 2 + 9 * ∑ j, ‖F s j‖ ^ 2) *
          Real.exp (300 * (1 + ∑ j, ‖C.θ j‖ ^ 2 + V ^ 2 + k) * (t - a)) := by
  let R := 300 * (1 + ∑ j, ‖C.θ j‖ ^ 2 + V ^ 2 + k)
  let f := fun s => ‖S s‖ ^ 2 + 9 * ∑ j, ‖F s j‖ ^ 2
  let d := fun s => (1 / 2) * ∑ j, ‖cellDerivativeCLM j (y s).val‖ ^ 2
  have hR : 0 ≤ R := by
    have hk := (norm_nonneg (C.κ a)).trans (hκ a)
    have hθ : 0 ≤ ∑ j, ‖C.θ j‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    dsimp only [R]
    positivity
  have hf : IntervalIntegrable f volume a b := by
    have hsum := (cellTime_normSq_intervalIntegrable hab (hF 0)).add
      (cellTime_normSq_intervalIntegrable hab (hF 1))
    simpa only [f, Fin.sum_univ_two, Pi.add_def] using
      (cellTime_normSq_intervalIntegrable hab hS).add (hsum.const_mul 9)
  have hd : IntervalIntegrable d volume a b := by
    have hdj (j : Fin 2) := cellTime_normSq_intervalIntegrable hab
      ((cellDerivativeCLM j).comp_memLp' hy)
    simpa only [d, Fin.sum_univ_two, Function.comp_def, Pi.add_def] using
      ((hdj 0).add (hdj 1)).const_mul (1 / 2)
  apply h.time.energy_dissipation_le_gronwall hab R hR f d hf hd
  · exact Filter.Eventually.of_forall (fun s => by dsimp only [f]; positivity)
  · exact Filter.Eventually.of_forall (fun s => by dsimp only [d]; positivity)
  · have ha := h.agrees
    have he := h.equation
    rw [uIcc_of_le hab] at ha he
    filter_upwards [ha, he] with s has hes
    have hp := cellGenerator_source_energy_bound C hG V k hv hb hκ s (y s).val (S s) (F s)
    have hi := hes (y s)
    rw [real_inner_comm, has, hi]
    change 2 * (cellGeneratorForm C hG V hv hb s (y s).val (y s).val +
      cellSourceFunctional C.θ (S s) (F s) (y s).val) + d s ≤
      R * ‖torusHkValueCLM (y s).val‖ ^ 2 + f s
    simpa only [d, R, f, add_assoc] using hp

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Exact bilinear product-rule error decomposition for metric-gradient difference quotients. -/

/-- The flux quotient error splits into coefficient error, state continuity, and state quotient error. -/
theorem cellMetricFlux_productRule_error (r : ℝ)
    (A B C : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (E D T : ℝ → RawJet2 1 ℂ) :
    r • (cellMetricFlux A E - cellMetricFlux B D) -
        (cellMetricFlux C D + cellMetricFlux B T) =
      cellMetricFlux (r • (A - B) - C) E +
        cellMetricFlux C (E - D) + cellMetricFlux B (r • (E - D) - T) := by
  simp only [cellMetricFlux_sub_metric, cellMetricFlux_smul_metric,
    cellMetricFlux_sub_state, cellMetricFlux_smul_state, smul_sub]
  abel

/-- A zero metric produces zero perturbation flux. -/
theorem cellMetricFlux_zero_metric (D : ℝ → RawJet2 1 ℂ) : cellMetricFlux 0 D = 0 := by
  funext t x
  apply PiLp.ext
  intro i
  simp [cellMetricFlux, cellMetricFluxVector]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Literal monomial weighting of multiplier means in the fibre graph series. -/

/-- Absolute weighted L2 convergence identifies the multiplier mean with the weighted coefficient means. -/
theorem fibreMean_monomial_tsum (ξ : Fin 2 → ℂ) (b : Vec 2 → ℂ)
    (hb : MemLp b 2 (volume.restrict AVenhance.unitCube))
    (f : ℕ × ℕ → Vec 2 → ℂ)
    (hs : (∑' p, cellL2Norm (fun x => fibreMonomial ξ p * f p x)) < ⊤) :
    cellMean (fun x => b x * ∑' p, fibreMonomial ξ p * f p x) =
      ∑' p, fibreMonomial ξ p * cellMean (fun x => b x * f p x) := by
  rw [cellMean_product_tsum b hb (fun p x => fibreMonomial ξ p * f p x) hs]
  apply tsum_congr
  intro p
  have he : (fun x => b x * (fibreMonomial ξ p * f p x)) =
      fibreMonomial ξ p • (fun x => b x * f p x) := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [he, cellMean_complex_smul]

/-- Absolute weighted L2 convergence also proves absolute convergence of the weighted coefficient means. -/
theorem fibreMean_monomial_summable_norm (ξ : Fin 2 → ℂ) (b : Vec 2 → ℂ)
    (hb : MemLp b 2 (volume.restrict AVenhance.unitCube))
    (f : ℕ × ℕ → Vec 2 → ℂ)
    (hs : (∑' p, cellL2Norm (fun x => fibreMonomial ξ p * f p x)) < ⊤) :
    Summable (fun p => ‖fibreMonomial ξ p * cellMean (fun x => b x * f p x)‖) := by
  have he p : cellMean (fun x => b x * (fibreMonomial ξ p * f p x)) =
      fibreMonomial ξ p * cellMean (fun x => b x * f p x) := by
    have hfun : (fun x => b x * (fibreMonomial ξ p * f p x)) =
        fibreMonomial ξ p • (fun x => b x * f p x) := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hfun, cellMean_complex_smul]
  have h := cellMean_product_series_enorm_lt_top b hb
    (fun p x => fibreMonomial ξ p * f p x) hs
  simp_rw [he] at h
  exact tsum_enorm_ne_top_iff_summable_norm.mp h.ne

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CycleEvolution

/-! Literal bilinear row evaluation is the complex pairing against its actual conjugate source class. -/

theorem cellComplexPair_conjugate_source_slice (f : ℝ → Vec 2 → ℂ) (t : ℝ)
    (hf : MemLp (f t) 2 (volume.restrict AVenhance.unitCube)) (u : ComplexCellL2) :
    cellComplexPair u (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellSourceSlice f t)) =
      cellMean (fun x => f t x * u x) := by
  unfold cellComplexPair cellMean
  apply integral_congr_ae
  filter_upwards [cellFiberConj_ae (cellSourceSlice f t), cellSourceSlice_ae f t hf]
    with x hc hs
  rw [hc, hs, star_star, mul_comm]

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The Bloch diffusion form has the conjugate frequency as its Hilbert adjoint. -/

def cellComplexDiffusionForm
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    (θ : Fin 2 → ℂ) (t : ℝ) (u z : TorusHk 1 ℂ) : ℂ :=
  -(∑ j : Fin 2, ∑ k : Fin 2, cellComplexPair
    (cellMetricEntryCLM hG t j k (cellShiftedDerivativeCLM θ j u))
    (cellShiftedDerivativeCLM (fun i => star (θ i)) k z))

theorem cellComplexDiffusionForm_adjoint
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    (θ : Fin 2 → ℂ) (t : ℝ) (u z : TorusHk 1 ℂ) :
    cellComplexDiffusionForm hG θ t u z =
      star (cellComplexDiffusionForm hG (fun i => star (θ i)) t z u) := by
  unfold cellComplexDiffusionForm
  simp only [star_star, star_neg]
  exact congrArg Neg.neg (cellComplexMetricForm_symm hG t
    (fun j => cellShiftedDerivativeCLM θ j u)
    (fun k => cellShiftedDerivativeCLM (fun i => star (θ i)) k z))

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The complex transport form is skew Hermitian on periodic H¹ fields. -/

def cellComplexDriftForm (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : IsCellDrift v) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (t : ℝ) (u z : TorusHk 1 ℂ) : ℂ :=
  ⟨cellDriftForm v V hv.1 hb t u z,
    cellDriftForm v V hv.1 hb t u (cellH1Scalar Complex.I z)⟩

theorem cellComplexDriftForm_eq_sum {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (u z : TorusHk 1 ℂ) :
    cellComplexDriftForm v V hv hb t u z =
      ∑ j : Fin 2, cellComplexPair
        (cellDriftEntryCLM ⟨0, v, 0, 0⟩ V hv.1 hb t j (cellDerivativeCLM j u))
        (torusHkValueCLM z) := by
  apply Complex.ext
  · simp only [cellComplexDriftForm, Fin.sum_univ_two, Complex.add_re, cellComplexPair_re]
    change (∑ j : Fin 2, inner ℝ
      (cellDriftEntryCLM ⟨0, v, 0, 0⟩ V hv.1 hb t j (cellDerivativeCLM j u))
      (torusHkValueCLM z)) = _
    rw [Fin.sum_univ_two]
  · simp only [cellComplexDriftForm, Fin.sum_univ_two, Complex.add_im, cellComplexPair_im]
    change cellDriftForm v V hv.1 hb t u (cellH1Scalar Complex.I z) = _
    change (∑ j : Fin 2, inner ℝ
      (cellDriftEntryCLM ⟨0, v, 0, 0⟩ V hv.1 hb t j (cellDerivativeCLM j u))
      (torusHkValueCLM (cellH1Scalar Complex.I z))) = _
    rw [cellH1Scalar_value]
    rw [Fin.sum_univ_two]

theorem cellComplexDriftForm_skew {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (u z : TorusHk 1 ℂ) :
    cellComplexDriftForm v V hv hb t u z =
      -star (cellComplexDriftForm v V hv hb t z u) := by
  apply Complex.ext
  · exact cellDriftForm_skew hv V hb t u z
  · change cellDriftForm v V hv.1 hb t u (cellH1Scalar Complex.I z) =
      -(-cellDriftForm v V hv.1 hb t z (cellH1Scalar Complex.I u))
    rw [cellDriftForm_skew hv V hb t u (cellH1Scalar Complex.I z),
      cellDriftForm_I_left hv V hb t z u]

end AVRegularity.CycleEvolution
end

section
open AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The actual divergence forcing changes by a scalar source under a Bloch shift. -/

theorem cellComplexSource_add_shift (θ δ : Fin 2 → ℂ) (S : ComplexCellL2)
    (F : Fin 2 → ComplexCellL2) (z : TorusHk 1 ℂ) :
    cellComplexSource (θ + δ) S F z = cellComplexSource θ
      (S + ∑ j : Fin 2, cellScalarCLM (Complex.I * δ j) (F j)) F z := by
  have hstar : (fun j => star ((θ + δ) j)) =
      (fun j => star (θ j)) + (fun j => star (δ j)) := by
    funext j
    simp only [Pi.add_apply, star_add]
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  simp only [cellComplexSource, hstar, cellShiftedDerivativeCLM_add_shift,
    Fin.sum_univ_two, cellComplexPair_add_left, cellComplexPair_add_right,
    cellComplexPair_scalar_right, cellComplexPair_scalar_left, star_mul, star_star, hI]
  ring

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Actual conjugation of H¹ values, derivatives and Bloch shifts. -/

theorem cellH1Conj_value (u : TorusHk 1 ℂ) :
    torusHkValueCLM (cellH1Conj u) =
      cellFiberCLM Complex.conjCLE.toContinuousLinearMap (torusHkValueCLM u) := by
  apply Lp.ext
  exact (cellH1Conj_jet_ae u (valueIndex2 1)).trans (cellFiberConj_ae _).symm

theorem cellH1Conj_shift (θ : Fin 2 → ℂ) (u : TorusHk 1 ℂ) (j : Fin 2) :
    cellShiftedDerivativeCLM (fun k => -star (θ k)) j (cellH1Conj u) =
      cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellShiftedDerivativeCLM θ j u) := by
  apply Lp.ext
  filter_upwards [cellShiftedDerivativeCLM_ae (fun k => -star (θ k)) j (cellH1Conj u),
    cellShiftedDerivativeCLM_ae θ j u, cellFiberConj_ae (cellShiftedDerivativeCLM θ j u),
    cellH1Conj_jet_ae u (valueIndex2 1),
    cellH1Conj_jet_ae u ⟨⟨1, by decide⟩, fun _ => j⟩] with x hs hz hc hv hd
  change torusHkValueCLM (cellH1Conj u) x = star (torusHkValueCLM u x) at hv
  change cellDerivativeCLM j (cellH1Conj u) x = star (cellDerivativeCLM j u x) at hd
  rw [hs, hc, hz, hv, hd]
  simp only [star_add, star_mul, show star Complex.I = -Complex.I from Complex.conj_I]
  ring

end AVRegularity.CycleEvolution
end
end
end
