-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.CellEnergySpaceRawSmul
public import AVRegularity.CycleEvolution.CellWeakForcedGapEnergy
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Set Filter Homogenization AVRegularity.Sobolev
open scoped Topology
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.CycleEvolution

/-! Generator convergence for the actual raw Galerkin state curves. -/

variable {a b : ℝ} {hab : a ≤ b} {C : CellCoefficients} {hG : IsCellMetric C.G} {V : ℝ}
  {hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2)}
  {hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2}
  {src : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
  {initial : ComplexCellL2}

/-- The raw periodic H¹ state of one actual finite path. -/
def CellGalerkinLimitData.state
    (D : CellGalerkinLimitData a b hab C hG V hv hb src F initial) (N : ℕ) (t : ℝ) :
    TorusHk 1 ℂ := (extendCurve hab (D.curve N) t).val

/-- The temporal H¹ class of one actual finite state. -/
def CellGalerkinLimitData.stateClass
    (D : CellGalerkinLimitData a b hab C hG V hv hb src F initial) (N : ℕ) : CellBochnerH1 a b :=
  (D.stateLp N).toLp (D.state N)

/-- Generator integrals of actual raw finite states converge with the projected test. -/
theorem CellGalerkinLimitData.generator_integral_tendsto
    (D : CellGalerkinLimitData a b hab C hG V hv hb src F initial)
    (k : ℝ) (hκ : Measurable C.κ) (hκb : ∀ r, ‖C.κ r‖ ≤ k)
    (z : TorusHk 1 ℂ) (t : ℝ) (ht : t ∈ Icc a b) :
    Tendsto (fun n => ∫ r in a..t, cellGeneratorForm C hG V hv hb r
      (D.state (D.subsequence n) r) (galerkinProj (D.subsequence n) z)) atTop
      (𝓝 (∫ r in a..t, cellGeneratorForm C hG V hv hb r (D.limit r) z)) := by
  let L := cellGeneratorIntegralTestCLM hab ⟨le_rfl, hab⟩ ht ht.1 C hG V k hv hb hκ hκb
  have htest := (L.continuous.tendsto z).comp
    ((galerkinProj_tendsto z).comp D.monotone.tendsto_atTop)
  have he := cellWeak_eval_perturbed_test (fun n => D.stateClass (D.subsequence n)) D.limit
    D.budget (fun n => D.norm_bound (D.subsequence n)) D.weak
    (fun n => L (galerkinProj (D.subsequence n) z)) (L z) htest
  have hr : L z D.limit = ∫ r in a..t, cellGeneratorForm C hG V hv hb r (D.limit r) z :=
    cellGeneratorIntegralCLM_apply_class ⟨le_rfl, hab⟩ ht ht.1 C hG V k hv hb hκ hκb z D.limit
  rw [hr] at he
  apply he.congr'
  filter_upwards with n
  exact (cellGeneratorIntegralCLM_apply ⟨le_rfl, hab⟩ ht ht.1 C hG V k hv hb hκ hκb
    (galerkinProj (D.subsequence n) z) (D.state (D.subsequence n)) (D.stateLp (D.subsequence n)))

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Raw gradient energy reads any jointly L2 Sobolev representative, without a PDE premise. -/

theorem cellRaw_gradient_lintegral_of_state {a b : ℝ} (hab : a ≤ b)
    (D : ℝ → RawJet2 1 ℂ)
    (hD : ∀ j, MemLp (fun p : ℝ × Vec 2 => D p.1 j p.2) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (slice : ℝ → TorusHk 1 ℂ) (hs : MemLp slice 2 (volume.restrict (Icc a b)))
    (hj : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ j,
      ((slice t).val j : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] D t j) :
    (∫⁻ t in Icc a b, cellL2Norm (cellGradient (D t)) ^ 2) =
      ENNReal.ofReal (∫ t in a..b, ∑ j, ‖cellDerivativeCLM j (slice t)‖ ^ 2) := by
  have hp := cellSource_memLp_slices (Icc a b) (fun t => cellGradient (D t))
    (cellRawGradient_memLp (Icc a b) D hD)
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
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Joint almost-everywhere identification of the weak integrand of actual solution series. -/

/-- Actual solution and forcing summability identify the summed weak integrand on each finite time interval. -/
theorem cellSolutionSeries_rhs_ae {J : Type*} [Countable J]
    (C : CellCoefficients) (src : J → ℝ → Vec 2 → ℂ)
    (F : J → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D : J → ℝ → RawJet2 1 ℂ)
    (hD : ∀ j, IsCellSolution Set.univ C (src j) (F j) (D j))
    (hsD : (∑' j, cellEnergyNorm Set.univ (D j)) < ⊤)
    (hsm : ∀ j, AEStronglyMeasurable (Function.uncurry (src j))
      ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)))
    (hFm : ∀ j, AEStronglyMeasurable (Function.uncurry (F j))
      ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)))
    (hss : (∑' j, cellUlNorm Set.univ (src j)) < ⊤)
    (hFs : (∑' j, cellUlNorm Set.univ (F j)) < ⊤)
    (a b : ℝ) (ψ : Vec 2 → ℂ) (dψ : Fin 2 → Vec 2 → ℂ) :
    ∀ᵐ p ∂((volume.restrict (Set.Icc a b)).prod (volume.restrict AVenhance.unitCube)),
      cellLiteralRHS C p.1 (cellValue (fun t k x => ∑' j, D j t k x) p.1)
        (cellGradComp (fun k x => ∑' j, D j p.1 k x)) ψ dψ
        (fun x => ∑' j, src j p.1 x) (fun x => ∑' j, F j p.1 x) p.2 =
      ∑' j, cellLiteralRHS C p.1 (cellValue (D j) p.1) (cellGradComp (D j p.1))
        ψ dψ (src j p.1) (F j p.1) p.2 := by
  let μ := (volume.restrict (Set.Icc a b)).prod (volume.restrict AVenhance.unitCube)
  have hv := cellLpSeries_memLp_bound μ (fun j => Function.uncurry (cellValue (D j)))
    (cellSolutionSeries_value_interval_L2 (fun _ => C) src F D hD hsD a b)
  have hg := cellLpSeries_memLp_bound μ (fun (j : J) (p : ℝ × Vec 2) => cellGradient (D j p.1) p.2)
    (cellSolutionSeries_gradient_interval_L2 (fun _ => C) src F D hD hsD a b)
  have hsrc := cellLpSeries_memLp_bound μ (fun j => Function.uncurry (src j))
    (cellUlSeries_interval_eLpNorm_tsum_lt_top src hsm hss a b)
  have hflux := cellLpSeries_memLp_bound μ (fun j => Function.uncurry (F j))
    (cellUlSeries_interval_eLpNorm_tsum_lt_top F hFm hFs a b)
  filter_upwards [hv.2.2, hg.2.2, hsrc.2.2, hflux.2.2] with p hpv hpg hps hpF
  exact cellLiteralRHS_raw_tsum C p.1 ψ dψ p.2 (fun j => D j p.1)
    (fun j => src j p.1) (fun j => F j p.1) (Summable.of_norm hpv) (Summable.of_norm hpg)
    (Summable.of_norm hps) (Summable.of_norm hpF)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleEvolution

/-! Actual conjugation of weak Bloch trajectories, with no smooth time premise. -/

theorem CellWeakHilbertCurve.conjugate {a b : ℝ} {u : ℝ → ComplexCellL2}
    {slice g : ℝ → TorusHk 1 ℂ} (h : CellWeakHilbertCurve a b u slice g) :
    CellWeakHilbertCurve a b
      (fun t => cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u t))
      (fun t => cellH1Conj (slice t)) (fun t => cellH1Conj (g t)) := by
  simpa only [mapTorusHkCLM_apply, cellH1Conj] using
    h.fiber_map Complex.conjCLE.toContinuousLinearMap

theorem CellWeakHilbertCurve.conjugate_homogeneous {a b : ℝ}
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    {u : ℝ → ComplexCellL2} {slice : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice (fun t =>
      cellDualDerivative C hG V hv hb t (slice t) 0 0)) :
    CellWeakHilbertCurve a b
      (fun t => cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u t))
      (fun t => cellH1Conj (slice t))
      (fun t => cellDualDerivative (cellConjugateCoefficients C) hG V hv hb t
        (cellH1Conj (slice t)) 0 0) := by
  apply h.conjugate.dual_congr
  exact Filter.Eventually.of_forall (fun t =>
    cellDualDerivative_conjugate C hG V hv hb t (slice t))

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The literal mean of every genuine weak cell trajectory is an absolutely continuous scalar. -/

theorem CellWeakHilbertCurve.mean_strongTime {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → ComplexCellL2} {slice g : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice g) :
    StrongTimeRegularity a b (fun t => cellMean (u t))
      (fun t => cellDualComplexPair (g t) cellH1One) := by
  simpa only [cellH1One_value, cellComplexPair_one] using
    h.complex_test_strongTime hab cellH1One

theorem CellWeakHilbertCurve.mean_increment {a b : ℝ}
    {u : ℝ → ComplexCellL2} {slice g : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice g)
    (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    cellMean (u t) - cellMean (u s) =
      ∫ r in s..t, cellDualComplexPair (g r) cellH1One := by
  simpa only [cellH1One_value, cellComplexPair_one] using
    h.complex_increment s hs t ht hst cellH1One

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The plain diffusion form has the literal unshifted derivative pairing. -/

theorem cellComplexDiffusionForm_zero_shift
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    (t : ℝ) (u z : TorusHk 1 ℂ) :
    cellComplexDiffusionForm hG (fun _ => 0) t u z =
      -(∑ j : Fin 2, ∑ k : Fin 2,
        cellComplexPair (cellMetricEntryCLM hG t j k (cellDerivativeCLM j u))
          (cellDerivativeCLM k z)) := by
  unfold cellComplexDiffusionForm
  simp only [star_zero, cellShiftedDerivative_zero_apply]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The time readout norm equals the literal covariant derivative energy. -/

theorem cellEnergySpaceTimeShiftedDerivative_norm_sq {a b : ℝ} (hab : a ≤ b)
    (z : CellEnergySpace a b) (θ : Fin 2 → ℂ) (j : Fin 2) :
    ‖cellFiniteEnergyTimeShiftedDerivativeCLM hab θ j (show CellFiniteEnergyCarrier a b from z)‖ ^ 2 =
      ∫ t in a..b, ‖cellShiftedDerivativeCLM θ j (cellEnergySpaceState hab z t)‖ ^ 2 := by
  let : InnerProductSpace ℝ ComplexCellL2 := InnerProductSpace.complexToReal
  rw [lpTwoHilbert_normSq_integral]
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards [cellEnergySpaceTimeShiftedDerivative_ae hab z θ j] with t ht
  rw [ht]

theorem cellEnergySpaceShiftedDerivative_sum_integral {a b : ℝ} (hab : a ≤ b)
    (z : CellEnergySpace a b) (θ : Fin 2 → ℂ) :
    (∫ t in a..b, ∑ j, ‖cellShiftedDerivativeCLM θ j (cellEnergySpaceState hab z t)‖ ^ 2) =
      ∑ j, ‖cellFiniteEnergyTimeShiftedDerivativeCLM hab θ j (show CellFiniteEnergyCarrier a b from z)‖ ^ 2 := by
  have hi (j : Fin 2) := cellTime_normSq_intervalIntegrable hab
    ((cellShiftedDerivativeCLM θ j).comp_memLp' (cellEnergySpaceState_memLp hab z))
  have h0 := cellEnergySpaceTimeShiftedDerivative_norm_sq hab z θ 0
  have h1 := cellEnergySpaceTimeShiftedDerivative_norm_sq hab z θ 1
  have hadd := intervalIntegral.integral_add (hi 0) (hi 1)
  have he := (congrArg₂ (fun x y : ℝ => x + y) h0 h1).symm
  simp only [Fin.sum_univ_two, Function.comp_def] at hadd ⊢
  exact hadd.trans (by
    simpa only [Fin.sum_univ_two, Function.comp_def] using he)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Bounded complex-linear scalar forcing operators for literal Bloch and potential perturbations. -/

def cellBlochPerturbationScalarCLM {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (δ : Fin 2 → ℂ) (q : Lp ℂ ∞ (volume.restrict (Icc a b))) :
    CellFiniteEnergyCarrier a b →L[ℂ] Lp ComplexCellL2 2 (volume.restrict (Icc a b)) :=
  (∑ k : Fin 2, (Complex.I * δ k) •
    (∑ j : Fin 2, (cellTimeMetricEntryCLM (Icc a b) hG j k).comp
      (cellFiniteEnergyTimeShiftedDerivativeCLM hab (C.θ + δ) j))) -
  (∑ j : Fin 2, (Complex.I * δ j) •
    ((cellTimeDriftEntryCLM (Icc a b) C V hv hb j).comp (cellFiniteEnergyTimeValueCLM hab))) +
  (lpTopScalarMultiplier (volume.restrict (Icc a b)) q).comp (cellFiniteEnergyTimeValueCLM hab)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Actual uniformly local source bounds for the bounded fibre multipliers. -/

/-- Multiplying an actual all-time cell trace by a bounded joint measurable scalar gives an admissible source. -/
theorem cellBoundedMultiplier_ul_bound
    (b : ℝ → Vec 2 → ℂ) (B : ℝ)
    (hb : Measurable (Function.uncurry b)) (hB : ∀ t x, ‖b t x‖ ≤ B)
    {C : CellCoefficients} {src : ℝ → Vec 2 → ℂ}
    {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {D : ℝ → RawJet2 1 ℂ}
    (hD : IsCellSolution univ C src F D) :
    cellUlNorm univ (fun t x => b t x * cellValue D t x) ≤
      ENNReal.ofReal B * cellEnergyNorm univ D ∧
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => b p.1 p.2 * cellValue D p.1 p.2)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) := by
  have hm (t : ℝ) : AEStronglyMeasurable (fun x => b t x * cellValue D t x)
      (volume.restrict AVenhance.unitCube) :=
    ((hb.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable).mul
      (hD.2.2.1 t (mem_univ t)).1.aestronglyMeasurable
  refine ⟨cellUlNorm_le_uniform_cellL2Norm _ _ (fun t => ?_), ?_⟩
  · exact (cellL2Norm_mul_le (b t) (cellValue D t) B (hm t)
      (Filter.Eventually.of_forall (hB t))).trans (by
        gcongr
        exact cellValue_cellL2Norm_le_energy D t)
  · exact hb.aestronglyMeasurable.mul (hD.2.2.2.1 (valueIndex2 1))

end AVRegularity.CycleEvolution
end

section
open AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Differences of raw representatives represent the actual carrier difference. -/

theorem cellEnergySpaceRawRepresentative_sub {a b : ℝ} (hab : a ≤ b)
    (z w : CellEnergySpace a b) (D E : ℝ → RawJet2 1 ℂ)
    (hD : IsCellEnergySpaceRawRepresentative hab z D)
    (hE : IsCellEnergySpaceRawRepresentative hab w E) :
    IsCellEnergySpaceRawRepresentative hab (z - w) (D - E) := by
  have hn := cellEnergySpaceRawRepresentative_smul hab (-1 : ℂ) w E hE
  have ha := cellEnergySpaceRawRepresentative_add hab z ((-1 : ℂ) • w) D ((-1 : ℂ) • E) hD hn
  simpa only [neg_one_smul, sub_eq_add_neg] using ha

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set
namespace AVRegularity.CycleEvolution

/-! Named complex-linear trace and Bloch derivative readouts for analytic energy families. -/

def cellEnergySpaceToCarrierCLM (a b : ℝ) : CellEnergySpace a b →L[ℂ] CellFiniteEnergyCarrier a b :=
  ContinuousLinearMap.id ℂ (CellFiniteEnergyCarrier a b)

def cellEnergySpaceTraceCLM (a b : ℝ) :
    CellEnergySpace a b →L[ℂ] C(CellCompactTime a b, ComplexCellL2) :=
  (compatibleTraceLpTraceCLM (volume : Measure (CellCompactTime a b)) cellComplexH1ValueCLM).comp
    (cellEnergySpaceToCarrierCLM a b)

def cellEnergySpaceShiftedDerivativeCLM {a b : ℝ} (hab : a ≤ b)
    (θ : Fin 2 → ℂ) (j : Fin 2) :
    CellEnergySpace a b →L[ℂ] Lp ComplexCellL2 2 (volume.restrict (Icc a b)) :=
  (cellFiniteEnergyTimeShiftedDerivativeCLM hab θ j).comp (cellEnergySpaceToCarrierCLM a b)

theorem cellEnergySpaceTraceCLM_apply (a b : ℝ) (z : CellEnergySpace a b)
    (t : CellCompactTime a b) :
    cellEnergySpaceTraceCLM a b z t = (show CellFiniteEnergyCarrier a b from z).val.1 t := rfl

theorem cellEnergySpaceShiftedDerivativeCLM_apply {a b : ℝ} (hab : a ≤ b)
    (θ : Fin 2 → ℂ) (j : Fin 2) (z : CellEnergySpace a b) :
    cellEnergySpaceShiftedDerivativeCLM hab θ j z =
      cellFiniteEnergyTimeShiftedDerivativeCLM hab θ j (show CellFiniteEnergyCarrier a b from z) := rfl

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Uniformly local raw source norms control the corresponding Bochner forcing budgets. -/

/-- A unit window of spatial Hilbert scalar classes is bounded by the raw uniformly local norm. -/
theorem cellUl_scalar_hilbert_window (I : Set ℝ) (f : ℝ → Vec 2 → ℂ)
    (hm : Measurable (Function.uncurry f)) (hf : cellUlNorm I f < ⊤) (a : ℝ) :
    (∫ t in Icc a (a + 1) ∩ I, ‖cellSourceSlice f t‖ ^ 2) ≤ (cellUlNorm I f).toReal ^ 2 := by
  let J := Icc a (a + 1) ∩ I
  have hp := cellSource_memLp_product J f hm (cellUl_window_integral_lt_top I f hf a)
  have hs := cellSourceSlice_memLp J f hp
  have he := cellEnergy_lintegral_of_ae (fun t => cellL2Norm (f t) ^ 2)
    (fun t => ‖cellSourceSlice f t‖ ^ 2) hs.norm.integrable_sq
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) (cellSource_cellNormSq_ae J f hp)
  have hle := cellUl_window_integral_le I f a
  rw [he] at hle
  have hr := ENNReal.toReal_mono (ENNReal.pow_ne_top hf.ne) hle
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun _ => sq_nonneg _)), ENNReal.toReal_pow] at hr
  exact hr

/-- A unit window of Hilbert flux coordinate classes is bounded by the raw vector source norm. -/
theorem cellUl_flux_hilbert_window (I : Set ℝ)
    (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hm : Measurable (Function.uncurry F)) (hF : cellUlNorm I F < ⊤) (a : ℝ) :
    (∫ t in Icc a (a + 1) ∩ I, ∑ j, ‖cellSourceSlice (fun r x => F r x j) t‖ ^ 2) ≤
      (cellUlNorm I F).toReal ^ 2 := by
  let J := Icc a (a + 1) ∩ I
  have hp := cellSource_memLp_product J F hm (cellUl_window_integral_lt_top I F hF a)
  have hs (j : Fin 2) := cellSourceSlice_memLp J (fun r x => F r x j)
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).comp_memLp' hp)
  have hi : Integrable (fun t => ∑ j, ‖cellSourceSlice (fun r x => F r x j) t‖ ^ 2)
      (volume.restrict J) := by
    simpa only [Fin.sum_univ_two, Pi.add_def] using (hs 0).norm.integrable_sq.add (hs 1).norm.integrable_sq
  have he := cellEnergy_lintegral_of_ae (fun t => cellL2Norm (F t) ^ 2)
    (fun t => ∑ j, ‖cellSourceSlice (fun r x => F r x j) t‖ ^ 2) hi
    (Filter.Eventually.of_forall (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    (cellFlux_cellNormSq_ae J F hp)
  have hle := cellUl_window_integral_le I F a
  rw [he] at hle
  have hr := ENNReal.toReal_mono (ENNReal.pow_ne_top hF.ne) hle
  rw [ENNReal.toReal_ofReal (integral_nonneg (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))),
    ENNReal.toReal_pow] at hr
  exact hr

end AVRegularity.CycleEvolution
end

section
open AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Mean subtraction does not change the energy pairing on the genuine mean-zero subspace. -/

theorem cellMeanZero_constant_pair_zero (c : ℂ) (u : ComplexCellL2)
    (hm : cellMean u = 0) :
    cellComplexPair (cellScalarCLM c (cellConstantCLM 1)) u = 0 := by
  rw [cellComplexPair_scalar_left, cellComplexPair_symm (cellConstantCLM 1),
    cellComplexPair_one, hm, star_zero, mul_zero]

theorem cellMeanZero_constant_pivot_inner_zero (c : ℂ) (u : TorusHk 1 ℂ)
    (hm : cellMean (torusHkValueCLM u) = 0) :
    inner ℝ (cellPivotDualCLM (cellScalarCLM c (cellConstantCLM 1))) u = 0 := by
  have he := congrArg Complex.re (cellMeanZero_constant_pair_zero c (torusHkValueCLM u) hm)
  rw [cellComplexPair_re, Complex.zero_re] at he
  simpa only [cellPivotDualCLM, ContinuousLinearMap.adjoint_inner_left] using he

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Actual energy and forcing bounds justify absolute weak-integrand summation locally in time. -/

/-- The actual solution and forcing summability premises prove the full local weak-integrand L1 majorant. -/
theorem cellSolutionSeries_rhs_L1 {J : Type*} [Countable J]
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
    (a b : ℝ) (ψ : TorusHkFunction 1 ℂ) :
    (∑' j, eLpNorm (fun p : ℝ × Vec 2 => cellLiteralRHS ⟨G, v, 0, 0⟩ p.1
      (cellValue (D j) p.1) (cellGradComp (D j p.1)) (ψ.jet (valueIndex2 1))
      (fun k => ψ.jet ⟨⟨1, by decide⟩, fun _ => k⟩) (src j p.1) (F j p.1) p.2) 1
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict AVenhance.unitCube))) < ⊤ := by
  let μ := (volume.restrict (Set.Icc a b)).prod (volume.restrict AVenhance.unitCube)
  have hμ : μ ≤ (volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube) :=
    Measure.prod_mono (Measure.restrict_mono (Set.subset_univ _) le_rfl) le_rfl
  have hgrad := cellSolutionSeries_gradient_interval_L2 (fun _ => ⟨G, v, 0, 0⟩) src F D hD hsD a b
  have hg (k : Fin 2) : (∑' j, eLpNorm (fun p : ℝ × Vec 2 => cellGradComp (D j p.1) k p.2) 2 μ) < ⊤ := by
    apply (ENNReal.tsum_le_tsum (fun j => cellGradComp_product_eLpNorm_le (Set.Icc a b) (D j) k
      (((hD j).2.2.2.1 ⟨⟨1, by decide⟩, fun _ => k⟩).mono_measure hμ))).trans_lt hgrad
  have hs := cellUlSeries_interval_eLpNorm_tsum_lt_top src hsm hss a b
  have hf := cellUlSeries_interval_eLpNorm_tsum_lt_top F hFm hFs a b
  have hflux (k : Fin 2) : (∑' j, eLpNorm (fun p : ℝ × Vec 2 => F j p.1 p.2 k) 2 μ) < ⊤ := by
    apply (ENNReal.tsum_le_tsum (fun j => ?_)).trans_lt hf
    have hm : MemLp (Function.uncurry (F j)) 2 μ := (ENNReal.le_tsum j).trans_lt hf
    have hp := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 2 => ℂ) k).comp_memLp' hm
    apply eLpNorm_mono_ae hp.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun p => PiLp.norm_apply_le (F j p.1 p.2) k)
  exact cellLiteralZeroRHS_series_L1 a b G hG v hvm V hvb ψ (fun j => cellValue (D j)) src
    (fun j t => cellGradComp (D j t)) F hg hs hflux

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set
namespace AVRegularity.CycleEvolution

/-! The temporal value readout costs exactly the square root of the time length. -/

theorem cellEnergySpaceTimeValue_norm_le {a b : ℝ} (hab : a ≤ b)
    (z : CellEnergySpace a b) :
    ‖cellFiniteEnergyTimeValueCLM hab (show CellFiniteEnergyCarrier a b from z)‖ ≤
      Real.sqrt (b - a) * ‖cellEnergySpaceTraceCLM a b z‖ := by
  let : InnerProductSpace ℝ ComplexCellL2 := InnerProductSpace.complexToReal
  have hv := cellEnergySpaceTimeValue_ae hab z
  have ha := cellEnergySpaceTrace_agrees hab z
  have he : cellFiniteEnergyTimeValueCLM hab (show CellFiniteEnergyCarrier a b from z)
      =ᵐ[volume.restrict (Icc a b)] cellEnergySpaceTrace hab z := hv.trans ha.symm
  have hp : ∀ t, ‖cellEnergySpaceTrace hab z t‖ ≤ ‖cellEnergySpaceTraceCLM a b z‖ := fun t =>
    (cellEnergySpaceTraceCLM a b z).norm_coe_le_norm (projIcc a b hab t)
  apply lpTwoFiniteInterval_norm_le hab _ _ (norm_nonneg _)
  filter_upwards [he] with t ht
  exact (congrArg norm ht).le.trans (hp t)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The quadratic mean multiplier in the fibre graph is an actual uniformly local source. -/

/-- The fibre quadratic source is jointly almost measurable and bounded by the product of the actual energy norms. -/
theorem cellMeanMultiplier_ul_bound
    (b : ℝ → Vec 2 → ℂ) (B : ℝ)
    (hb : Measurable (Function.uncurry b)) (hB : ∀ t x, ‖b t x‖ ≤ B)
    {C C' : CellCoefficients} {src src' : ℝ → Vec 2 → ℂ}
    {F F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    {D E : ℝ → RawJet2 1 ℂ}
    (hD : IsCellInverseValue C src F D) (hE : IsCellInverseValue C' src' F' E) :
    cellUlNorm univ (fun t x => cellValue E t x *
      cellMean (fun y => b t y * cellValue D t y)) ≤
      ENNReal.ofReal B * cellEnergyNorm univ D * cellEnergyNorm univ E ∧
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => cellValue E p.1 p.2 *
      cellMean (fun y => b p.1 y * cellValue D p.1 y))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) := by
  have hprod := cellBoundedMultiplier_ul_bound b B hb hB hD.1
  have hm (t : ℝ) : AEStronglyMeasurable (fun x => b t x * cellValue D t x)
      (volume.restrict AVenhance.unitCube) :=
    ((hb.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable).mul
      (hD.1.2.2.1 t (mem_univ t)).1.aestronglyMeasurable
  have hp (t : ℝ) : cellL2Norm (fun x => b t x * cellValue D t x) ≤
      ENNReal.ofReal B * cellEnergyNorm univ D :=
    (cellL2Norm_mul_le (b t) (cellValue D t) B (hm t)
      (Filter.Eventually.of_forall (hB t))).trans (by
        gcongr
        exact cellValue_cellL2Norm_le_energy D t)
  have hf (t : ℝ) : MemLp (fun x => b t x * cellValue D t x) 2
      (volume.restrict AVenhance.unitCube) :=
    (hp t).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hD.2.2)
  have hmean (t : ℝ) : ‖cellMean (fun y => b t y * cellValue D t y)‖ₑ ≤
      ENNReal.ofReal B * cellEnergyNorm univ D :=
    (cellMean_enorm_le_cellL2Norm _ (hf t)).trans (hp t)
  refine ⟨cellUlNorm_le_uniform_cellL2Norm _ _ (fun t => ?_), ?_⟩
  · have he : (fun x => cellValue E t x * cellMean (fun y => b t y * cellValue D t y)) =
        cellMean (fun y => b t y * cellValue D t y) • cellValue E t := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul, mul_comm]
    change eLpNorm _ 2 _ ≤ _
    rw [he, eLpNorm_const_smul]
    gcongr
    · exact hmean t
    · exact cellValue_cellL2Norm_le_energy E t
  · exact cellMean_product_aestronglyMeasurable (I := univ)
      (f := fun t x => b t x * cellValue D t x) (g := cellValue E) hprod.2 (hE.1.2.2.2.1 (valueIndex2 1))

/-! Literal raw covariant-gradient energy equals its actual shifted H¹ class budget. -/

theorem cellRaw_covGradient_lintegral_of_state {a b : ℝ} (hab : a ≤ b)
    (D : ℝ → RawJet2 1 ℂ)
    (hD : ∀ j, MemLp (fun p : ℝ × Vec 2 => D p.1 j p.2) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube))) (θ : Fin 2 → ℂ) (slice : ℝ → TorusHk 1 ℂ)
    (hs : MemLp slice 2 (volume.restrict (Icc a b)))
    (hj : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ j,
      ((slice t).val j : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] D t j) :
    (∫⁻ t in Icc a b, cellL2Norm (cellCovGradient θ (D t)) ^ 2) =
      ENNReal.ofReal (∫ t in a..b, ∑ j, ‖cellShiftedDerivativeCLM θ j (slice t)‖ ^ 2) := by
  have hp := cellSource_memLp_slices (Icc a b) (fun t => cellCovGradient θ (D t))
    (cellRawCovGradient_memLp (Icc a b) θ D hD)
  have he : (fun t => cellL2Norm (cellCovGradient θ (D t)) ^ 2) =ᵐ[volume.restrict (Icc a b)]
      fun t => ENNReal.ofReal (∑ j, ‖cellShiftedDerivativeCLM θ j (slice t)‖ ^ 2) := by
    filter_upwards [hp, hj] with t ht hjt
    exact cellArray_cellNormSq (cellCovGradient θ (D t)) ht _
      (fun j => cellShiftedDerivative_jet_ae θ (slice t) (D t) hjt j)
  have hi (j : Fin 2) := cellTime_normSq_intervalIntegrable hab
    ((cellShiftedDerivativeCLM θ j).comp_memLp' hs)
  have hsum : IntervalIntegrable (fun t => ∑ j, ‖cellShiftedDerivativeCLM θ j (slice t)‖ ^ 2) volume a b := by
    simpa only [Fin.sum_univ_two, Pi.add_apply, Function.comp_def] using (hi 0).add (hi 1)
  have hint := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hsum
  rw [cellEnergy_lintegral_of_ae _ _ hint
    (Filter.Eventually.of_forall (fun _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))) he,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]

 theorem cellSolution_covGradient_lintegral_of_state {a b : ℝ} (hab : a ≤ b)
    {C : CellCoefficients} {src : ℝ → Vec 2 → ℂ}
    {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {D : ℝ → RawJet2 1 ℂ}
    (h : IsCellSolution (Icc a b) C src F D) (θ : Fin 2 → ℂ) (slice : ℝ → TorusHk 1 ℂ)
    (hs : MemLp slice 2 (volume.restrict (Icc a b)))
    (hj : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ j,
      ((slice t).val j : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] D t j) :
    (∫⁻ t in Icc a b, cellL2Norm (cellCovGradient θ (D t)) ^ 2) =
      ENNReal.ofReal (∫ t in a..b, ∑ j, ‖cellShiftedDerivativeCLM θ j (slice t)‖ ^ 2) :=
  cellRaw_covGradient_lintegral_of_state hab D (IsCellSolution.jet_memLp hab h) θ slice hs hj

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Every-time L2 and periodicity properties of literal solution series. -/

/-- Absolute energy summability preserves the actual L2 and periodic value at every time. -/
theorem cellSolutionSeries_value_regular {J : Type*} [Countable J]
    (C : J → CellCoefficients) (src : J → ℝ → Vec 2 → ℂ)
    (F : J → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D : J → ℝ → RawJet2 1 ℂ)
    (hD : ∀ j, IsCellSolution Set.univ (C j) (src j) (F j) (D j))
    (hs : (∑' j, cellEnergyNorm Set.univ (D j)) < ⊤) (t : ℝ) :
    MemLp (fun x => ∑' j, cellValue (D j) t x) 2 (volume.restrict AVenhance.unitCube) ∧
      AVenhance.IsZ2Periodic (fun x => ∑' j, cellValue (D j) t x) := by
  have hl : (∑' j, cellL2Norm (cellValue (D j) t)) < ⊤ :=
    (ENNReal.tsum_le_tsum (fun j => cellValue_cellL2Norm_le_energy (D j) t)).trans_lt hs
  refine ⟨(cellL2Series_memLp_bound (fun j => cellValue (D j) t) hl).1, ?_⟩
  intro x z
  apply tsum_congr
  intro j
  exact ((hD j).2.2.1 t (Set.mem_univ t)).2 x z

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CycleEvolution

/-! The real coordinate drift coupling transports actual coefficient conjugation through the cell mean. -/

theorem fibreCoordinateFrequency_coupling_star (η : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (j : Fin 2) (t : ℝ) (x : Vec 2) :
    star (fibreDriftCoupling η v (fibreCoordinateFrequency j) t x) =
      fibreDriftCoupling η v (fibreCoordinateFrequency j) t x := by
  rw [fibreCoordinateFrequency_coupling]
  simp only [Complex.star_def, map_mul, Complex.conj_ofReal]

theorem fibreCoordinateFrequency_mean_reality (η : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (j : Fin 2) (t : ℝ) (σ : ℂ) (f : Vec 2 → ℂ)
    (hf : (fun x => star (f x)) =ᵐ[volume.restrict AVenhance.unitCube]
      (fun x => σ * f x)) :
    star (cellMean (fun x => fibreDriftCoupling η v (fibreCoordinateFrequency j) t x * f x)) =
      σ * cellMean (fun x => fibreDriftCoupling η v (fibreCoordinateFrequency j) t x * f x) := by
  change star (∫ x in AVenhance.unitCube,
    fibreDriftCoupling η v (fibreCoordinateFrequency j) t x * f x) = _
  rw [← cellIntegral_star]
  calc
    _ = ∫ x in AVenhance.unitCube,
        σ * (fibreDriftCoupling η v (fibreCoordinateFrequency j) t x * f x) := by
      apply integral_congr_ae
      filter_upwards [hf] with x hx
      rw [star_mul, hx, fibreCoordinateFrequency_coupling_star]
      ring
    _ = _ := integral_const_mul _ _

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set
namespace AVRegularity.CycleEvolution

/-! Changing the Bloch shift costs its frequency distance times the temporal value norm. -/

theorem cellEnergySpaceShiftedDerivative_change {a b : ℝ} (hab : a ≤ b)
    (z : CellEnergySpace a b) (θ ζ : Fin 2 → ℂ) (j : Fin 2) :
    cellEnergySpaceShiftedDerivativeCLM hab θ j z =
      cellEnergySpaceShiftedDerivativeCLM hab ζ j z +
        (Complex.I * (θ j - ζ j)) • cellFiniteEnergyTimeValueCLM hab
          (show CellFiniteEnergyCarrier a b from z) := by
  change cellFiniteEnergyTimeDerivativeCLM hab j (show CellFiniteEnergyCarrier a b from z) +
      (Complex.I * θ j) • cellFiniteEnergyTimeValueCLM hab (show CellFiniteEnergyCarrier a b from z) =
    (cellFiniteEnergyTimeDerivativeCLM hab j (show CellFiniteEnergyCarrier a b from z) +
      (Complex.I * ζ j) • cellFiniteEnergyTimeValueCLM hab (show CellFiniteEnergyCarrier a b from z)) + _
  module

theorem cellEnergySpaceShiftedDerivative_change_norm {a b : ℝ} (hab : a ≤ b)
    (z : CellEnergySpace a b) (θ ζ : Fin 2 → ℂ) (j : Fin 2) :
    ‖cellEnergySpaceShiftedDerivativeCLM hab θ j z‖ ≤
      ‖cellEnergySpaceShiftedDerivativeCLM hab ζ j z‖ +
        ‖θ j - ζ j‖ * Real.sqrt (b - a) * ‖cellEnergySpaceTraceCLM a b z‖ := by
  have he := cellEnergySpaceShiftedDerivative_change hab z θ ζ j
  have ht := norm_add_le (cellEnergySpaceShiftedDerivativeCLM hab ζ j z)
    ((Complex.I * (θ j - ζ j)) • cellFiniteEnergyTimeValueCLM hab
      (show CellFiniteEnergyCarrier a b from z))
  have hn : ‖(Complex.I * (θ j - ζ j)) • cellFiniteEnergyTimeValueCLM hab
      (show CellFiniteEnergyCarrier a b from z)‖ ≤
      ‖θ j - ζ j‖ * (Real.sqrt (b - a) * ‖cellEnergySpaceTraceCLM a b z‖) := by
    rw [norm_smul, norm_mul, Complex.norm_I, one_mul]
    exact mul_le_mul_of_nonneg_left (cellEnergySpaceTimeValue_norm_le hab z) (norm_nonneg _)
  exact (congrArg norm he).le.trans (ht.trans (by
    simpa only [mul_assoc] using add_le_add_right hn
      ‖cellEnergySpaceShiftedDerivativeCLM hab ζ j z‖))

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Actual dual time derivatives associated with arbitrary public raw solutions. -/

/-- The actual Riesz dual derivative of a public raw trajectory. -/
def cellRawSolutionDual (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D : ℝ → RawJet2 1 ℂ) (t : ℝ) : TorusHk 1 ℂ :=
  cellDualDerivative C hG V hv hb t (cellH1Slice D t) (cellSourceSlice src t)
    (fun j => cellSourceSlice (fun r x => F r x j) t)

/-- Every public solution has the actual dual derivative in temporal L². -/
theorem cellSolution_dual_memLp {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (hκ : Measurable C.κ) (hκb : ∀ t, ‖C.κ t‖ ≤ k)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (D : ℝ → RawJet2 1 ℂ) (h : IsCellSolution (Icc a b) C src F D) :
    MemLp (cellRawSolutionDual C hG V hv hb src F D) 2 (volume.restrict (Icc a b)) :=
  cellDualDerivative_memLp C hG V k hv hb hκ hκb (cellH1Slice D) (cellSolution_slice_memLp hab h)
    _ (cellSourceSlice_memLp (Icc a b) src hsrc) _
    (fun j => cellSourceSlice_memLp (Icc a b) (fun r x => F r x j)
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).comp_memLp' hF))

/-! Drift-independent forgetting of common forcing for actual weak cell curves. -/

/-- Common forcing cancels in the actual Riesz derivative, as an equality of H⁻¹ representatives. -/
theorem cellDualDerivative_sub_same_source (C : CellCoefficients) (hG : IsCellMetric C.G)
    (V : ℝ) (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (t : ℝ)
    (u w : TorusHk 1 ℂ) (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    cellDualDerivative C hG V hv hb t u S F - cellDualDerivative C hG V hv hb t w S F =
      cellDualDerivative C hG V hv hb t (u - w) 0 (fun _ => 0) := by
  apply ext_inner_right ℝ
  intro z
  rw [cellDualDerivative_difference_pairing, cellDualDerivative_pairing,
    cellSourceFunctional_zero, add_zero]

/-- Differences of actual weak solutions with common forcing solve the homogeneous equation. -/
theorem cellWeakActual_sub_same_source {a b : ℝ}
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (S : ℝ → ComplexCellL2) (F : ℝ → Fin 2 → ComplexCellL2)
    (u w : ℝ → ComplexCellL2) (slice other : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice
      (fun t => cellDualDerivative C hG V hv hb t (slice t) (S t) (F t)))
    (h' : CellWeakHilbertCurve a b w other
      (fun t => cellDualDerivative C hG V hv hb t (other t) (S t) (F t))) :
    CellWeakHilbertCurve a b (fun t => u t - w t) (fun t => slice t - other t)
      (fun t => cellDualDerivative C hG V hv hb t (slice t - other t) 0 (fun _ => 0)) := by
  have he : (fun t => cellDualDerivative C hG V hv hb t (slice t) (S t) (F t) -
      cellDualDerivative C hG V hv hb t (other t) (S t) (F t)) =
      (fun t => cellDualDerivative C hG V hv hb t (slice t - other t) 0 (fun _ => 0)) := by
    funext t
    exact cellDualDerivative_sub_same_source C hG V hv hb t (slice t) (other t) (S t) (F t)
  simpa only [he] using h.sub h'

/-- Two actual mean-zero solutions forget their common forcing at the homogeneous spectral rate. -/
theorem cellWeakActual_difference_decay {a b : ℝ} (hab : a ≤ b)
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (S : ℝ → ComplexCellL2) (F : ℝ → Fin 2 → ComplexCellL2)
    (u w : ℝ → ComplexCellL2) (slice other : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice
      (fun t => cellDualDerivative ⟨G, v, 0, 0⟩ hG V hv.1 hb t (slice t) (S t) (F t)))
    (h' : CellWeakHilbertCurve a b w other
      (fun t => cellDualDerivative ⟨G, v, 0, 0⟩ hG V hv.1 hb t (other t) (S t) (F t)))
    (hm : ∀ t ∈ Icc a b, cellMean (u t) = 0)
    (hm' : ∀ t ∈ Icc a b, cellMean (w t) = 0) :
    ∀ t ∈ Icc a b, ‖u t - w t‖ ^ 2 ≤
      Real.exp (-(4 * Real.pi ^ 2) * (t - a)) * ‖u a - w a‖ ^ 2 := by
  apply cellWeakHomogeneous_meanZero_decay hab hG hv V hb _ _
    (cellWeakActual_sub_same_source ⟨G, v, 0, 0⟩ hG V hv.1 hb S F u w slice other h h')
  intro t ht
  rw [← cellMeanCLM_apply, map_sub, cellMeanCLM_apply, cellMeanCLM_apply, hm t ht, hm' t ht,
    sub_self]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Lower-order trace reality gives the actual divergence-flux coefficient reality. -/

theorem fibreCoordinateGraphFlux_apply (η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (j k : Fin 2) (ρ : ℝ → Vec 2 → ℂ) (t : ℝ) (x : Vec 2) :
    fibreGraphFlux η G (fibreCoordinateFrequency j) ρ t x k =
      2 * Complex.I * (Real.sqrt η : ℂ) * (G t k j : ℂ) * ρ t x := by
  simp [fibreGraphFlux, fibreCoordinateFrequency, Pi.single_apply]

theorem fibreCoefficientFlux_reality (η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (D : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (p : ℕ × ℕ) (t : ℝ)
    (hD : ∀ a, a.1 + a.2 < p.1 + p.2 →
      (fun x => star (cellValue (D a) t x)) =ᵐ[volume.restrict AVenhance.unitCube]
        (fun x => fibreRealitySign a * cellValue (D a) t x)) :
    cellFluxConj (fibreCoefficientFlux η G D p t) =ᵐ[volume.restrict AVenhance.unitCube]
      (fun x => fibreRealitySign p • fibreCoefficientFlux η G D p t x) := by
  have he : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ j ∈ fibreCoefficientDirections p,
      star (cellValue (D (fibreCoefficientPrevious p j)) t x) =
        fibreRealitySign (fibreCoefficientPrevious p j) * cellValue (D (fibreCoefficientPrevious p j)) t x := by
    apply ae_all_iff.mpr
    intro j
    by_cases hj : j ∈ fibreCoefficientDirections p
    · have ho := fibreCoefficientPrevious_order hj
      exact (hD _ (by omega)).mono (fun _ hx _ => hx)
    · exact Filter.Eventually.of_forall (fun _ h => (hj h).elim)
  filter_upwards [he] with x hx
  apply PiLp.ext
  intro k
  have hsum : (∑ j ∈ fibreCoefficientDirections p, fibreGraphFlux η G (fibreCoordinateFrequency j)
      (cellValue (D (fibreCoefficientPrevious p j))) t x) k =
      ∑ j ∈ fibreCoefficientDirections p, fibreGraphFlux η G (fibreCoordinateFrequency j)
        (cellValue (D (fibreCoefficientPrevious p j))) t x k := by
    exact map_sum (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 2 => ℂ) k) _ _
  simp only [cellFluxConj, PiLp.toLp_apply, fibreCoefficientFlux,
    PiLp.smul_apply, smul_eq_mul, hsum, star_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [fibreCoordinateGraphFlux_apply]
  rw [star_mul, star_mul, star_mul, star_mul,
    show star (2 : ℂ) = 2 from by norm_num,
    show star Complex.I = -Complex.I from Complex.conj_I,
    show star (Real.sqrt η : ℂ) = (Real.sqrt η : ℂ) from Complex.conj_ofReal _,
    show star (G t k j : ℂ) = (G t k j : ℂ) from Complex.conj_ofReal _,
    hx j hj, fibreRealitySign_previous hj]
  ring

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The literal raw fibre X norm is the actual trace supremum plus shifted Hilbert gradient energy. -/

theorem cellSolution_fibreXNorm_of_state {a b : ℝ} (hab : a ≤ b)
    {C : CellCoefficients} {src : ℝ → Vec 2 → ℂ}
    {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {D : ℝ → RawJet2 1 ℂ}
    (h : IsCellSolution (Icc a b) C src F D) (θ : Fin 2 → ℂ)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (hu : ∀ t ∈ Icc a b, (u t : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] cellValue D t)
    (hs : MemLp slice 2 (volume.restrict (Icc a b)))
    (hj : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ j,
      ((slice t).val j : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] D t j) :
    fibreXNorm θ (Icc a b) D = (⨆ t ∈ Icc a b, ENNReal.ofReal ‖u t‖) +
      ENNReal.ofReal (Real.sqrt (∫ t in a..b, ∑ j, ‖cellShiftedDerivativeCLM θ j (slice t)‖ ^ 2)) := by
  unfold fibreXNorm
  congr 1
  · apply iSup_congr
    intro t
    apply iSup_congr
    intro ht
    exact cellL2Norm_eq_of_class _ _ (hu t ht)
  · rw [cellSolution_covGradient_lintegral_of_state hab h θ slice hs hj]
    have hn : 0 ≤ ∫ t in a..b, ∑ j, ‖cellShiftedDerivativeCLM θ j (slice t)‖ ^ 2 :=
      intervalIntegral.integral_nonneg hab (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    rw [ENNReal.ofReal_rpow_of_nonneg (p := (1 / 2 : ℝ)) hn (by norm_num), ← Real.sqrt_eq_rpow]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Filter Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Public raw complex weak identities from the actual Hilbert cell equation. -/

/-- Every raw realization of the actual weak Hilbert solution satisfies the literal public identity. -/
theorem cellWeakHilbert_raw_identity {a b : ℝ}
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
      (slice r) (cellSourceSlice src r) (fun j => cellSourceSlice (fun t x => F t x j) r)))
    (D : ℝ → RawJet2 1 ℂ)
    (htrace : ∀ t ∈ Icc a b, (u t : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] cellValue D t)
    (hjet : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ a,
      ((slice t).val a : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] D t a)
    (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (ψ : TorusHkFunction 1 ℂ) :
    CellWeakIdentity C s t (cellValue D s) (cellValue D t) (ψ.jet (valueIndex2 1))
      (fun j => ψ.jet ⟨⟨1, by decide⟩, fun _ => j⟩) (cellValue D)
      (fun r j => cellGradComp (D r) j) src F := by
  let g := fun r => cellDualDerivative C hG V hv hb r (slice r) (cellSourceSlice src r)
    (fun j => cellSourceSlice (fun t x => F t x j) r)
  let R := fun r => cellLiteralRHS C r (cellValue D r) (cellGradComp (D r))
    (ψ.jet (valueIndex2 1)) (fun j => ψ.jet ⟨⟨1, by decide⟩, fun _ => j⟩) (src r) (F r)
  have hFlux (j : Fin 2) := cellSource_memLp_slices (Icc a b) (fun r x => F r x j)
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).comp_memLp' hF)
  have hgood : ∀ᵐ r ∂volume.restrict (Ioc s t),
      Integrable (R r) (volume.restrict AVenhance.unitCube) ∧
        (∫ x in AVenhance.unitCube, R r x) = cellDualComplexPair (g r) (cellRawTest ψ) := by
    have hsub : Ioc s t ⊆ Icc a b := Ioc_subset_Icc_self.trans (Icc_subset_Icc hs.1 ht.2)
    have hj := hjet.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
    have hS := (cellSource_memLp_slices (Icc a b) src hsrc).filter_mono
      (ae_mono (Measure.restrict_mono hsub le_rfl))
    have hQ := (ae_all_iff.mpr hFlux).filter_mono
      (ae_mono (Measure.restrict_mono hsub le_rfl))
    filter_upwards [hj, hS, hQ] with r hr hsr hfr
    exact cellRawSpatial_equation C hG V hv hb r (slice r) (D r) hr ψ _ _ (src r) (F r)
      (cellSourceSlice_ae src r hsr) (fun j => cellSourceSlice_ae _ r (hfr j))
  have hi := cellDualComplexPair_intervalIntegrable hs ht hst g h.dual (cellRawTest ψ)
  have hti : Integrable (fun r => cellDualComplexPair (g r) (cellRawTest ψ))
      (volume.restrict (Ioc s t)) := by
    have hh := intervalIntegrable_iff.mp hi
    rw [uIoc_of_le hst] at hh
    exact hh
  have he : (fun r => ∫ x in AVenhance.unitCube, R r x) =ᵐ[volume.restrict (Ioc s t)]
      fun r => cellDualComplexPair (g r) (cellRawTest ψ) := hgood.mono (fun _ hr => hr.2)
  have htime := hti.congr he.symm
  have hinc := h.complex_increment s hs t ht hst (cellRawTest ψ)
  rw [cellRawTest_pairing_integral ψ (u t) _ (htrace t ht),
    cellRawTest_pairing_integral ψ (u s) _ (htrace s hs), intervalIntegral.integral_of_le hst] at hinc
  change Integrable (fun x => cellValue D t x * ψ.jet (valueIndex2 1) x) _ ∧
    Integrable (fun x => cellValue D s x * ψ.jet (valueIndex2 1) x) _ ∧
    (∀ᵐ r ∂volume.restrict (Ioc s t), Integrable (R r) _) ∧
    Integrable (fun r => ∫ x in AVenhance.unitCube, R r x) (volume.restrict (Ioc s t)) ∧
    (∫ x in AVenhance.unitCube, cellValue D t x * ψ.jet (valueIndex2 1) x) -
      (∫ x in AVenhance.unitCube, cellValue D s x * ψ.jet (valueIndex2 1) x) =
        ∫ r in Ioc s t, ∫ x in AVenhance.unitCube, R r x
  exact ⟨cellRawTest_pairing_integrable ψ _ _ (htrace t ht),
    cellRawTest_pairing_integrable ψ _ _ (htrace s hs),
    hgood.mono (fun _ hr => hr.1), htime, hinc.trans (integral_congr_ae he).symm⟩

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Bloch diffusion of the graph mode equals the plain graph diffusion and its actual flux and mass. -/

theorem cellConstantMetric_graph_diffusion {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : IsCellMetric (fun t _ => G t)) (θ : Fin 2 → ℂ) (t : ℝ) (u z : TorusHk 1 ℂ) :
    cellComplexDiffusionForm hG θ t (u + cellH1One) z =
      cellComplexDiffusionForm hG (fun _ => 0) t u z -
      (∑ j : Fin 2, cellComplexPair
        (cellScalarCLM (2 * Complex.I * ∑ k : Fin 2, (G t j k : ℂ) * θ k) (torusHkValueCLM u))
        (cellDerivativeCLM j z)) -
      (∑ j : Fin 2, ∑ k : Fin 2, (G t j k : ℂ) * θ j * θ k) *
        cellComplexPair (torusHkValueCLM u + cellConstantCLM 1) (torusHkValueCLM z) := by
  rw [cellConstantMetric_bloch_expansion, cellComplexDiffusionForm_zero_shift]
  simp only [map_add, cellH1One_derivative, add_zero, cellH1One_value,
    cellComplexPair_add_left, cellComplexPair_one_derivative,
    cellConstantMetricEntryCLM, cellComplexPair_scalar_left]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Summable actual energy trajectories give H1-in-time-ae literal series. -/

/-- Summable all-time energy bounds imply summable spatial gradient norms at almost every time. -/
theorem cellEnergySeries_gradient_summable_ae {J : Type*} [Countable J]
    (D : J → ℝ → RawJet2 1 ℂ)
    (hm : ∀ j, AEStronglyMeasurable (fun p : ℝ × Vec 2 => cellGradient (D j p.1) p.2)
      ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)))
    (hs : (∑' j, cellEnergyNorm Set.univ (D j)) < ⊤) :
    ∀ᵐ t ∂volume, (∑' j, cellL2Norm (cellGradient (D j t))) < ⊤ := by
  have hf (n : ℤ) (j : J) : AEStronglyMeasurable
      (fun p : ℝ × Vec 2 => cellGradient (D j p.1) p.2)
      ((volume.restrict (Set.Icc (n : ℝ) ((n : ℝ) + 1))).prod
        (volume.restrict AVenhance.unitCube)) :=
    (hm j).mono_measure (Measure.prod_mono
      (Measure.restrict_mono (Set.subset_univ _) le_rfl) le_rfl)
  apply cellSliceL2Series_allTime_ae (fun j t => cellGradient (D j t)) hf
  intro n
  apply (ENNReal.tsum_le_tsum (fun j => ?_)).trans_lt hs
  have he := cellUl_window_eq_product (E := PiLp 2 (fun _ : Fin 2 => ℂ)) Set.univ (fun t => cellGradient (D j t)) (n : ℝ)
    (by simpa only [Set.inter_univ, Function.uncurry_def] using hf n j)
  simp only [Set.inter_univ] at he
  rw [← he]
  have hw : (∫⁻ t in Set.Icc (n : ℝ) ((n : ℝ) + 1),
      cellL2Norm (cellGradient (D j t)) ^ 2) ^ (1 / 2 : ℝ) ≤
      cellUlNorm Set.univ (fun t => cellGradient (D j t)) := by
    change _ ≤ ⨆ a : ℝ, (∫⁻ t in Set.Icc a (a + 1) ∩ Set.univ,
      cellL2Norm (cellGradient (D j t)) ^ 2) ^ (1 / 2 : ℝ)
    simpa only [Set.inter_univ] using
      (le_iSup (fun a : ℝ => (∫⁻ t in Set.Icc a (a + 1) ∩ Set.univ,
        cellL2Norm (cellGradient (D j t)) ^ 2) ^ (1 / 2 : ℝ)) (n : ℝ))
  exact hw.trans (le_add_left le_rfl)

/-- A summable family of actual all-time cell solutions has an actual periodic weak-jet series ae in time. -/
theorem cellSolutionSeries_periodicWeakJet_ae {J : Type*} [Countable J]
    (C : J → CellCoefficients) (src : J → ℝ → Vec 2 → ℂ)
    (F : J → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D : J → ℝ → RawJet2 1 ℂ)
    (hD : ∀ j, IsCellSolution Set.univ (C j) (src j) (F j) (D j))
    (hs : (∑' j, cellEnergyNorm Set.univ (D j)) < ⊤) :
    ∀ᵐ t ∂volume, HasPeriodicOrderedWeakJet (fun a x => ∑' j, D j t a x) := by
  apply cellPeriodicTimeJet_tsum_of_slice_bounds D
    (fun j => by simpa only [Measure.restrict_univ] using (hD j).2.1)
    (fun j => cellEnergyNorm Set.univ (D j)) hs
    (fun j t => cellValue_cellL2Norm_le_energy (D j) t)
  exact cellEnergySeries_gradient_summable_ae D
    (fun j => cellSolution_gradient_aestronglyMeasurable (hD j)) hs

end AVRegularity.CycleEvolution
end
