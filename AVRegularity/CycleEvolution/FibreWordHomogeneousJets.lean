-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.FibreCoefficientForcedGradientBound
import AVRegularity.CycleEvolution.CellLimitMoments
import AVRegularity.CycleEvolution.CellEnergySpaceRawDirectionalLimit
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The actual normalized zero-trace forced curve has polynomial covariant-gradient energy. -/

theorem fibreCoefficient_forced_cov_gradient_bound (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreWordRadius Cw)
    {a b : ℝ} (hab : a ≤ b) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreSeriesC (fibreCoefficientSymbol η G v r) ξ
    ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ) (F : ℝ → Fin 2 → ComplexCellL2),
      (∀ j, MemLp (fun t => F t j) 2 (volume.restrict (Icc a b))) →
      CellWeakHilbertCurve a b u slice
        (fun t => cellDualDerivative (fibreCoefficients η G v ξ lam) hG V hv.1 hb t (slice t) 0 (F t)) →
      u a = 0 →
      let Cf := Real.sqrt 14 + 2 * (Cw * Real.sqrt (28 / Real.pi ^ 2) + 2) *
        fibreNorm ξ * Real.sqrt (b - a)
      (∫ t in a..b, ∑ j, ‖cellShiftedDerivativeCLM
          (fun j => (Real.sqrt η : ℂ) * ξ j) j (slice t)‖ ^ 2) ≤
        (224 + 16 * (b - a + 1) * (fibreNorm ξ / fibreCoefficientMajorantRadius Cw) ^ 2 * Cf ^ 2 +
          4 * fibreNorm ξ ^ 2 * (b - a) * Cf ^ 2) * (∫ t in a..b, ∑ j, ‖F t j‖ ^ 2) := by
  dsimp only
  intro u slice F hF h hu0
  let Q := ∫ t in a..b, ∑ j, ‖F t j‖ ^ 2
  let Cf := Real.sqrt 14 + 2 * (Cw * Real.sqrt (28 / Real.pi ^ 2) + 2) *
    fibreNorm ξ * Real.sqrt (b - a)
  have hQ : 0 ≤ Q := intervalIntegral.integral_nonneg hab
    (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hfn := fibreNorm_nonneg ξ
  have hCf : 0 ≤ Cf := by dsimp only [Cf]; positivity
  have hval := fibreCoefficient_forced_uniform_value_bound η Cw hη0 hη hCw G hG hg hgsmall hv hm hw
    V hb ξ hξ hab u slice F hF h hu0
  have hvalue : ∀ᵐ t ∂volume.restrict (Icc a b), ‖torusHkValueCLM (slice t)‖ ≤ Cf * Real.sqrt Q := by
    filter_upwards [h.agrees, ae_restrict_mem measurableSet_Icc] with t ht hti
    rw [← ht]
    exact hval t hti
  have hcov := cellShiftedGradient_integral_energy_le hab (fun j => (Real.sqrt η : ℂ) * ξ j)
    (fibreNorm ξ) (Cf * Real.sqrt Q) (fibreScaledFrequency_coordinate_le η hη ξ)
    (mul_nonneg hCf (Real.sqrt_nonneg _)) slice h.state hvalue
  have hgrad := fibreCoefficient_forced_gradient_bound η Cw hη0 hη hCw G hG hg hgsmall
    hv hm hw V hb ξ hξ hab u slice F hF h hu0
  apply hcov.trans
  calc
    _ ≤ 2 * ((112 + 8 * (b - a + 1) * (fibreNorm ξ / fibreCoefficientMajorantRadius Cw) ^ 2 * Cf ^ 2) * Q) +
        4 * fibreNorm ξ ^ 2 * (b - a) * (Cf * Real.sqrt Q) ^ 2 := by
      exact add_le_add (mul_le_mul_of_nonneg_left hgrad (by norm_num)) le_rfl
    _ = _ := by rw [mul_pow, Real.sq_sqrt hQ]; dsimp only [Cf, Q]; ring

/-! Reconstruction gives the polynomial finite-time homogeneous gradient budget. -/

theorem fibreCoefficient_homogeneous_gradient_bound (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreWordRadius Cw)
    {a b : ℝ} (hab : a ≤ b) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreSeriesC (fibreCoefficientSymbol η G v r) ξ
    ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ),
      CellWeakHilbertCurve a b u slice
        (fun t => cellDualDerivative (fibreCoefficients η G v ξ lam) hG V hv.1 hb t (slice t) 0 (fun _ => 0)) →
      (∫ t in a..b, ∑ j, ‖cellDerivativeCLM j (slice t)‖ ^ 2) ≤
        (72 + 8 * (5 + 24 * Cw / Real.pi ^ 2) ^ 2 * (b - a + 1) *
          (fibreNorm ξ / fibreCoefficientMajorantRadius Cw) ^ 2) * ‖u a‖ ^ 2 := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let D := fibreSeriesJet r ξ
  let lam := fibreSeriesC (fibreCoefficientSymbol η G v r) ξ
  let R := fun t => cellRawTrace D t + cellConstantCLM 1
  let z := fun (u : ℝ → ComplexCellL2) t => u t - cellScalarCLM (cellMean (u t)) (R t)
  let Ch := 5 + 24 * Cw / Real.pi ^ 2
  dsimp only
  intro u slice h
  have hRpos := fibreCoefficientMajorantRadius_pos hCw
  have hfn := fibreNorm_nonneg ξ
  have hCh : 0 ≤ Ch := by dsimp only [Ch]; positivity
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := by
    have ht := (hξ.trans (fibreWordRadius_le_graph Cw)).trans
      (fibreEvolutionRadius_le_majorant (Cw := Cw))
    linarith
  have hmean : ∀ t ∈ Icc a b, ‖cellMean (u t)‖ ≤ Ch * ‖u a‖ := by
    intro t ht
    have hvnorm := fibreCoefficient_homogeneous_value_bound η Cw hη0 hη hCw G hG hg hgsmall
      hv hm hw V hb ξ hξ ht.1 u slice (h.mono (Icc_subset_Icc le_rfl ht.2))
    have hmnorm : ‖cellMean (u t)‖ ≤ ‖u t‖ := by
      rw [← cellMeanCLM_apply (u t)]
      exact cellMeanCLM_norm_le (u t)
    exact hmnorm.trans hvnorm
  have hinv := fibreCoefficientFamily_graph_isInverse η Cw hη hCw G hG hv hw ξ hξR
  have hsol := cellSolution_restrict (Set.subset_univ (Icc a b)) Set.ordConnected_Icc hinv.1
  have hρ := cellSolution_slice_memLp hab hsol
  have hz := (fibreCoefficient_projected_remainder η Cw hη0 hη hCw G hG hv hm hw V hb
    ξ hξR hab u slice (fun _ _ => 0) h).1
  have hsplit := cellMeanRemainder_gradient_integral_le hab slice (cellH1Slice D)
    (fun t => cellMean (u t)) (Ch * ‖u a‖) (mul_nonneg hCh (norm_nonneg _)) hmean h.state hρ hz.state
  have henergy := fibreCoefficient_fast_energy_components η Cw hη0 hη hCw G hG hg hgsmall hv hm hw
    V hb ξ hξ hab u slice (fun _ _ => 0) (fun _ => MemLp.zero) h
  dsimp only at henergy
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero,
    intervalIntegral.integral_zero, mul_zero, add_zero] at henergy
  have hza : ‖z u a‖ ≤ 3 * ‖u a‖ := cellMean_graph_remainder_norm_le_two (u a) (R a)
    (fibreCoefficientFamily_word_graph_norm_le_two η Cw hη hCw G hG hv hw ξ hξ a)
  have hzasq := (sq_le_sq₀ (norm_nonneg (z u a)) (by positivity : 0 ≤ 3 * ‖u a‖)).mpr hza
  have hfast : (∫ t in a..b, ∑ j, ‖cellDerivativeCLM j
      (slice t - cellH1Scalar (cellMean (u t)) (cellH1Slice D t + cellH1One))‖ ^ 2) ≤ 36 * ‖u a‖ ^ 2 := by
    have he := henergy.2.2
    change (1 / 4 : ℝ) * (∫ t in a..b, ∑ j, ‖cellDerivativeCLM j
      (slice t - cellH1Scalar (cellMean (u t)) (cellH1Slice D t + cellH1One))‖ ^ 2) ≤ ‖z u a‖ ^ 2 at he
    nlinarith
  have hgraph := fibreCoefficientFamily_finite_hilbert_gradient η Cw hη hCw G hG hv hw ξ hξR hab
  calc
    _ ≤ 2 * (Ch * ‖u a‖) ^ 2 * (∫ t in a..b, ∑ j, ‖cellDerivativeCLM j (cellH1Slice D t)‖ ^ 2) +
        2 * ∫ t in a..b, ∑ j, ‖cellDerivativeCLM j
          (slice t - cellH1Scalar (cellMean (u t)) (cellH1Slice D t + cellH1One))‖ ^ 2 := hsplit
    _ ≤ 2 * (Ch * ‖u a‖) ^ 2 * (4 * (b - a + 1) *
          (fibreNorm ξ / fibreCoefficientMajorantRadius Cw) ^ 2) + 2 * (36 * ‖u a‖ ^ 2) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hgraph (by positivity))
        (mul_le_mul_of_nonneg_left hfast (by norm_num))
    _ = _ := by dsimp only [Ch]; ring

/-! Every genuine homogeneous Bloch solution initially in the constructed row kernel decays sharply. -/

theorem fibreAdjointRow_kernel_decay {a b : ℝ} (hab : a ≤ b)
    (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 1024)
    (hfreq : Cw * fibreNorm ξ + 1032 * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2 / 16)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice (fun t => cellDualDerivative
      ⟨fun t _ => G t, v, (fun j => (Real.sqrt η : ℂ) * ξ j), 0⟩
      hG V hv.1 hb t (slice t) 0 0))
    (hker : cellComplexPair (u a) (cellFiberCLM Complex.conjCLE.toContinuousLinearMap
      (cellSourceSlice (fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ) a)) = 0) :
    ∀ t ∈ Icc a b, ‖u t‖ ^ 2 ≤
      Real.exp (-(6 * Real.pi ^ 2) * (t - a)) * ‖u a‖ ^ 2 := by
  let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
  have hR := fibreCoefficientMajorantRadius_pos hCw
  have hξ16 : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16 := by linarith
  apply cellWeakBloch_rowKernel_decay hab η Cw hη0 hη hCw G hG hg hgsmall hv hw V hb
    ξ hfreq u slice h (fun t => cellSourceSlice ell t)
  · intro t _
    exact fibreAdjointRow_class_small η Cw hη hCw G hG hv hw ξ hξ t
  · intro t ht
    have htcurve := h.mono (Icc_subset_Icc le_rfl ht.2)
    have hp := fibreAdjointRow_pairing_transport η Cw hη0 hη hCw G hG hv hm hw V hb
      ξ hξ16 ht.1 htcurve
    dsimp only at hp
    rw [hker, mul_zero] at hp
    exact hp

/-! The actual normalized homogeneous curve has polynomial covariant-gradient energy. -/

theorem fibreCoefficient_homogeneous_cov_gradient_bound (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreWordRadius Cw)
    {a b : ℝ} (hab : a ≤ b) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let lam := fibreSeriesC (fibreCoefficientSymbol η G v r) ξ
    ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ),
      CellWeakHilbertCurve a b u slice
        (fun t => cellDualDerivative (fibreCoefficients η G v ξ lam) hG V hv.1 hb t (slice t) 0 (fun _ => 0)) →
      (∫ t in a..b, ∑ j, ‖cellShiftedDerivativeCLM
          (fun j => (Real.sqrt η : ℂ) * ξ j) j (slice t)‖ ^ 2) ≤
        (144 + 16 * (5 + 24 * Cw / Real.pi ^ 2) ^ 2 * (b - a + 1) *
          (fibreNorm ξ / fibreCoefficientMajorantRadius Cw) ^ 2 +
          4 * (5 + 24 * Cw / Real.pi ^ 2) ^ 2 * (b - a) * fibreNorm ξ ^ 2) * ‖u a‖ ^ 2 := by
  dsimp only
  intro u slice h
  let Ch := 5 + 24 * Cw / Real.pi ^ 2
  have hCh : 0 ≤ Ch := by dsimp only [Ch]; positivity
  have hval := fibreCoefficient_homogeneous_uniform_value_bound η Cw hη0 hη hCw G hG hg hgsmall hv hm hw
    V hb ξ hξ hab u slice h
  have hvalue : ∀ᵐ t ∂volume.restrict (Icc a b), ‖torusHkValueCLM (slice t)‖ ≤ Ch * ‖u a‖ := by
    filter_upwards [h.agrees, ae_restrict_mem measurableSet_Icc] with t ht hti
    rw [← ht]
    exact hval t hti
  have hcov := cellShiftedGradient_integral_energy_le hab (fun j => (Real.sqrt η : ℂ) * ξ j)
    (fibreNorm ξ) (Ch * ‖u a‖) (fibreScaledFrequency_coordinate_le η hη ξ)
    (mul_nonneg hCh (norm_nonneg _)) slice h.state hvalue
  have hgrad := fibreCoefficient_homogeneous_gradient_bound η Cw hη0 hη hCw G hG hg hgsmall
    ‹IsCellDrift v› hm hw V hb ξ hξ hab u slice h
  apply hcov.trans
  calc
    _ ≤ 2 * ((72 + 8 * Ch ^ 2 * (b - a + 1) * (fibreNorm ξ / fibreCoefficientMajorantRadius Cw) ^ 2) *
        ‖u a‖ ^ 2) + 4 * fibreNorm ξ ^ 2 * (b - a) * (Ch * ‖u a‖) ^ 2 := by
      exact add_le_add (mul_le_mul_of_nonneg_left hgrad (by norm_num)) le_rfl
    _ = _ := by dsimp only [Ch]; ring

/-! Every actual homogeneous weak Bloch curve has a sharply decaying graph remainder. -/

theorem fibreGraph_weak_remainder_decay {a b : ℝ} (hab : a ≤ b)
    (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 1024)
    (hfreq : Cw * fibreNorm ξ + 1032 * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2 / 16)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice (fun t => cellDualDerivative
      ⟨fun t _ => G t, v, (fun j => (Real.sqrt η : ℂ) * ξ j), 0⟩
      hG V hv.1 hb t (slice t) 0 0)) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let D := fibreSeriesJet r ξ
    let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
    let c := cellComplexPair (u a)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellSourceSlice ell a))
    let phase := fun t => Complex.exp (∫ s in a..t, fibreSeriesC (fibreCoefficientSymbol η G v r) ξ s)
    let w := fun t => u t - cellScalarCLM c (cellScalarCLM (phase t)
      (cellRawTrace D t + cellConstantCLM 1))
    ∀ t ∈ Icc a b, ‖w t‖ ^ 2 ≤
      Real.exp (-(6 * Real.pi ^ 2) * (t - a)) * ‖w a‖ ^ 2 := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let D := fibreSeriesJet r ξ
  let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
  let c := cellComplexPair (u a)
    (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellSourceSlice ell a))
  let phase := fun t => Complex.exp (∫ s in a..t, fibreSeriesC (fibreCoefficientSymbol η G v r) ξ s)
  have hR := fibreCoefficientMajorantRadius_pos hCw
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := by linarith
  have hξ16 : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16 := by linarith
  have hgraph := fibreCoefficientFamily_graph_homogeneous_evolution η Cw hη0 hη hCw
    G hG hv hm hw V hb ξ hξR hab
  have hmode := hgraph.homogeneous_complex_scalar (fun t _ => G t) hG v V hv.1 hb
    (fun j => (Real.sqrt η : ℂ) * ξ j) c
  have hdiff := cellWeakActual_sub_same_source
    ⟨fun t _ => G t, v, (fun j => (Real.sqrt η : ℂ) * ξ j), 0⟩ hG V hv.1 hb
    (fun _ => 0) (fun _ => 0) _ _ _ _ h hmode
  apply fibreAdjointRow_kernel_decay hab η Cw hη0 hη hCw G hG hg hgsmall hv hm hw V hb
    ξ hξ hfreq _ _ hdiff
  have hnorm := fibreAdjointRow_pairing_normalization η Cw hη hCw G hG hv hw ξ hξ16 a
  dsimp only at hnorm ⊢
  rw [cellComplexPair_eq_inner, inner_sub_right]
  rw [← cellComplexPair_eq_inner, ← cellComplexPair_eq_inner,
    cellComplexPair_scalar_left, cellComplexPair_scalar_left,
    intervalIntegral.integral_same, Complex.exp_zero, one_mul, hnorm]
  change c - c * 1 = 0
  ring

/-! Uniform sharp norm bound for the graph remainder of every actual homogeneous weak solution. -/

theorem fibreGraph_weak_remainder_norm {a b : ℝ} (hab : a ≤ b)
    (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 1024)
    (hfreq : Cw * fibreNorm ξ + 1032 * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2 / 16)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice (fun t => cellDualDerivative
      ⟨fun t _ => G t, v, (fun j => (Real.sqrt η : ℂ) * ξ j), 0⟩
      hG V hv.1 hb t (slice t) 0 0)) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let D := fibreSeriesJet r ξ
    let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
    let c := cellComplexPair (u a)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellSourceSlice ell a))
    let phase := fun t => Complex.exp (∫ s in a..t, fibreSeriesC (fibreCoefficientSymbol η G v r) ξ s)
    let w := fun t => u t - cellScalarCLM c (cellScalarCLM (phase t)
      (cellRawTrace D t + cellConstantCLM 1))
    ∀ t ∈ Icc a b, ‖w t‖ ≤ 13 * Real.exp (-(2 * Real.pi ^ 2) * (t - a)) * ‖u a‖ := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let D := fibreSeriesJet r ξ
  let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
  let c := cellComplexPair (u a)
    (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellSourceSlice ell a))
  let phase := fun t => Complex.exp (∫ s in a..t, fibreSeriesC (fibreCoefficientSymbol η G v r) ξ s)
  let w := fun t => u t - cellScalarCLM c (cellScalarCLM (phase t)
    (cellRawTrace D t + cellConstantCLM 1))
  have hs := fibreGraph_weak_remainder_decay hab η Cw hη0 hη hCw G hG hg hgsmall
    hv hm hw V hb ξ hξ hfreq u slice h
  dsimp only at hs
  change ∀ t ∈ Icc a b, ‖w t‖ ≤
    13 * Real.exp (-(2 * Real.pi ^ 2) * (t - a)) * ‖u a‖
  have hR := fibreCoefficientMajorantRadius_pos hCw
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := by linarith
  have hmode := (fibreCoefficientFamily_graph_mode_norm_bounds η Cw hη hCw G hG hv hw ξ hξR a).2
  have hrow := fibreAdjointRow_class_small η Cw hη hCw G hG hv hw ξ hξ a
  dsimp only at hrow
  have hnrow : ‖cellSourceSlice ell a‖ ≤ 4 := by
    have hn := norm_sub_norm_le (cellSourceSlice ell a) (cellConstantCLM 1)
    rw [cellConstantCLM_norm, norm_one] at hn
    linarith
  have hinit := cellNormalized_remainder_norm (u a) (cellRawTrace D a + cellConstantCLM 1)
    (cellSourceSlice ell a) hmode hnrow
  have hwa : ‖w a‖ ≤ 13 * ‖u a‖ := by
    simpa only [w, phase, intervalIntegral.integral_same, Complex.exp_zero,
      cellScalarCLM_smul, one_smul] using hinit
  intro t ht
  have hsqt : ‖w t‖ ^ 2 ≤ Real.exp (-(2 * (3 * Real.pi ^ 2)) * (t - a)) * ‖w a‖ ^ 2 := by
    have hs0 : ‖w t‖ ^ 2 ≤ Real.exp (-(6 * Real.pi ^ 2) * (t - a)) * ‖w a‖ ^ 2 := hs t ht
    simpa only [show (2 : ℝ) * (3 * Real.pi ^ 2) = 6 * Real.pi ^ 2 by ring] using hs0
  have hn := scalar_sharp_norm_decay (norm_nonneg (w t)) (norm_nonneg (w a)) hsqt
  have hcmp : -(3 * Real.pi ^ 2) * (t - a) ≤ -(2 * Real.pi ^ 2) * (t - a) := by
    have hp := mul_nonneg (sq_nonneg Real.pi) (sub_nonneg.mpr ht.1)
    linarith
  calc
    ‖w t‖ ≤ Real.exp (-(3 * Real.pi ^ 2) * (t - a)) * ‖w a‖ := hn
    _ ≤ Real.exp (-(2 * Real.pi ^ 2) * (t - a)) * (13 * ‖u a‖) :=
      mul_le_mul (Real.exp_le_exp.mpr hcmp) hwa (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by ring

/-! The graph remainder bound holds for every raw energy solution with arbitrary L² data. -/

theorem fibreGraph_raw_remainder_norm {a b : ℝ} (hab : a ≤ b)
    (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 1024)
    (D : ℝ → RawJet2 1 ℂ)
    (h : IsCellSolution (Icc a b) (fibreCoefficients η G v ξ (fun _ => 0))
      (fun _ _ => 0) (fun _ _ => 0) D) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
    let lam := fibreSeriesC (fibreCoefficientSymbol η G v r) ξ
    cellL2Norm (fun x => cellValue D b x - (1 + cellValue (fibreSeriesJet r ξ) b x) *
      Complex.exp (∫ s in a..b, lam s) * ∫ y in AVenhance.unitCube, ell a y * cellValue D a y) ≤
      ENNReal.ofReal (13 * Real.exp (-(2 * Real.pi ^ 2) * (b - a))) * cellL2Norm (cellValue D a) := by
  obtain ⟨V, hb⟩ := hv.2.1
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let graph := fibreSeriesJet r ξ
  let ell := fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hw) ξ
  let lam := fibreSeriesC (fibreCoefficientSymbol η G v r) ξ
  let phase := Complex.exp (∫ s in a..b, lam s)
  let c := cellComplexPair (cellRawTrace D a)
    (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellSourceSlice ell a))
  let w := cellRawTrace D b - cellScalarCLM c (cellScalarCLM phase
    (cellRawTrace graph b + cellConstantCLM 1))
  have h0 := h
  simp only [fibreCoefficients, neg_zero, show (fun _ : ℝ => (0 : ℂ)) = 0 from rfl] at h0
  have hweak := cellRawHomogeneous_to_Hilbert hab (fun t _ => G t) hG v V hv.1 hb
    (fun j => (Real.sqrt η : ℂ) * ξ j) D h0
  have hn := fibreGraph_weak_remainder_norm hab η Cw hη0 hη hCw G hG hg hgsmall hv hm hw V hb
    ξ hξ (fibreKernel_frequency_small hCw ξ hξ) (cellRawTrace D) (cellH1Slice D) hweak
  dsimp only at hn
  have hnb : ‖w‖ ≤ 13 * Real.exp (-(2 * Real.pi ^ 2) * (b - a)) * ‖cellRawTrace D a‖ :=
    hn b ⟨hab, le_rfl⟩
  have hR := fibreCoefficientMajorantRadius_pos hCw
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := by linarith
  have hξ16 : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16 := by linarith
  have hi := fibreCoefficientFamily_graph_isInverse η Cw hη hCw G hG hv hw ξ hξR
  have hl := (fibreAdjointRowCoefficients_series_memLp_bound η Cw hη hCw G hG hv hw ξ hξ16 a).1
  have hc : c = ∫ y in AVenhance.unitCube, ell a y * cellValue D a y := by
    dsimp only [c]
    rw [cellComplexPair_conjugate_source_slice ell a hl]
    apply integral_congr_ae
    filter_upwards [cellRawTrace_ae D a (h.2.2.1 a ⟨le_rfl, hab⟩).1] with y hy
    rw [hy]
  have he : (w : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      (fun x => cellValue D b x - (1 + cellValue graph b x) * phase * c) := by
    filter_upwards [Lp.coeFn_sub (cellRawTrace D b) (cellScalarCLM c (cellScalarCLM phase
      (cellRawTrace graph b + cellConstantCLM 1))),
      cellRawTrace_ae D b (h.2.2.1 b ⟨hab, le_rfl⟩).1,
      cellScalarCLM_ae c (cellScalarCLM phase (cellRawTrace graph b + cellConstantCLM 1)),
      cellScalarCLM_ae phase (cellRawTrace graph b + cellConstantCLM 1),
      cellRawTrace_add_one_ae graph b (hi.1.2.2.1 b (mem_univ b)).1] with x hs hd hc hp hg
    change (cellRawTrace D b - cellScalarCLM c (cellScalarCLM phase
      (cellRawTrace graph b + cellConstantCLM 1))) x = _
    rw [hs]
    change cellRawTrace D b x - cellScalarCLM c (cellScalarCLM phase
      (cellRawTrace graph b + cellConstantCLM 1)) x = _
    rw [hd, hc, hp, hg]
    ring
  change cellL2Norm (fun x => cellValue D b x - (1 + cellValue graph b x) * phase *
    ∫ y in AVenhance.unitCube, ell a y * cellValue D a y) ≤ _
  rw [← hc, cellL2Norm_eq_of_class _ w he,
    cellL2Norm_eq_of_class _ (cellRawTrace D a) (cellRawTrace_ae D a (h.2.2.1 a ⟨le_rfl, hab⟩).1),
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hnb

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The full literal forced word-operator bound for L² fluxes on arbitrary observation subintervals. -/

theorem fibreCoefficient_forced_raw_xnorm_bound
    (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreWordRadius Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (S s₀ a b : ℝ) (hS : 1 ≤ S) (hsa : s₀ ≤ a) (hab : a ≤ b) (hbS : b ≤ s₀ + S) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let C := fibreCoefficients η G v ξ (fibreSeriesC (fibreCoefficientSymbol η G v r) ξ)
    ∀ F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ),
      MemLp (Function.uncurry F) 2 ((volume.restrict (Icc s₀ b)).prod
        (volume.restrict AVenhance.unitCube)) →
      ∀ D : ℝ → RawJet2 1 ℂ,
      IsCellSolution (Icc s₀ b) C (fun _ _ => 0) F D →
      cellValue D s₀ =ᵐ[volume.restrict AVenhance.unitCube] 0 →
      fibreXNorm C.θ (Icc a b) D ≤
        ENNReal.ofReal (fibreWordForcedNormConstant Cw * (1 + Real.sqrt S * fibreNorm ξ) ^ 2) *
          (∫⁻ t in Icc s₀ b, cellL2Norm (F t) ^ 2) ^ (1 / 2 : ℝ) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let C := fibreCoefficients η G v ξ (fibreSeriesC (fibreCoefficientSymbol η G v r) ξ)
  dsimp only
  intro F hF D hD hu0
  have hsb := hsa.trans hab
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := by
    have ht := (hξ.trans (fibreWordRadius_le_graph Cw)).trans
      (fibreEvolutionRadius_le_majorant (Cw := Cw))
    have hp := fibreCoefficientMajorantRadius_pos hCw
    linarith
  let Fc := fun (t : ℝ) (j : Fin 2) => cellSourceSlice (fun r x => F r x j) t
  have hFc (j : Fin 2) : MemLp (fun t => Fc t j) 2 (volume.restrict (Icc s₀ b)) :=
    cellSourceSlice_memLp (Icc s₀ b) (fun r x => F r x j)
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).comp_memLp' hF)
  have h := fibreCoefficient_raw_forced_to_Hilbert hsb η Cw hη0 hη hCw G hG hv hw ξ hξR V hb F hF D hD
  have huclass : cellRawTrace D s₀ = 0 := by
    apply Lp.ext
    exact (cellRawTrace_ae D s₀ (hD.2.2.1 s₀ ⟨le_rfl, hsb⟩).1).trans
      (hu0.trans (Lp.coeFn_zero (E := ℂ) (p := 2) (μ := volume.restrict AVenhance.unitCube)).symm)
  let Q := ∫ t in s₀..b, ∑ j, ‖Fc t j‖ ^ 2
  have hQ : 0 ≤ Q := intervalIntegral.integral_nonneg hsb
    (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  let Cf := Real.sqrt 14 + 2 * (Cw * Real.sqrt (28 / Real.pi ^ 2) + 2) * fibreNorm ξ * Real.sqrt (b - s₀)
  have hfn := fibreNorm_nonneg ξ
  have hCf : 0 ≤ Cf := by dsimp only [Cf]; positivity
  let A := Cf * Real.sqrt Q
  let E := ∫ t in s₀..b, ∑ j, ‖cellShiftedDerivativeCLM C.θ j (cellH1Slice D t)‖ ^ 2
  have hval := fibreCoefficient_forced_uniform_value_bound η Cw hη0 hη hCw G hG hg hgsmall hv hm hw
    V hb ξ hξ hsb (cellRawTrace D) (cellH1Slice D) Fc hFc h huclass
  have hgrad := fibreCoefficient_forced_cov_gradient_bound η Cw hη0 hη hCw G hG hg hgsmall hv hm hw
    V hb ξ hξ hsb (cellRawTrace D) (cellH1Slice D) Fc hFc h huclass
  have hA : 0 ≤ A := mul_nonneg hCf (Real.sqrt_nonneg _)
  have hX := cellSolution_fibreXNorm_le_of_state_bounds hsb hD C.θ (cellRawTrace D) (cellH1Slice D)
    (fun t ht => cellRawTrace_ae D t (hD.2.2.1 t ht).1) h.state (cellSolution_slice_ae hD)
    A E hA hval le_rfl
  have hδ : b - s₀ ≤ S := by linarith
  have hbudget := word_forced_norm_budget (fibreCoefficientMajorantRadius Cw) Cf
    (fibreWordForcedAmplitude Cw) (fibreNorm ξ) S (b - s₀) A E Q
    (fibreCoefficientMajorantRadius_pos hCw) hCf (fibreWord_amplitudes_pos hCw).2.le hfn hS hδ hQ
    (fibreWord_forced_amplitude_le hCw hfn hδ) le_rfl hgrad
  have hnorm := cellFlux_finite_energy_half_norm hsb F hF
  have hCpos := (fibreWord_norm_constants_pos hCw).2
  calc
    _ ≤ fibreXNorm C.θ (Icc s₀ b) D := fibreXNorm_mono (Icc_subset_Icc hsa le_rfl) _ _
    _ ≤ ENNReal.ofReal (A + Real.sqrt E) := hX
    _ ≤ ENNReal.ofReal (fibreWordForcedNormConstant Cw * (1 + Real.sqrt S * fibreNorm ξ) ^ 2 *
        Real.sqrt Q) := ENNReal.ofReal_le_ofReal hbudget
    _ = _ := by rw [ENNReal.ofReal_mul (by positivity), hnorm]

/-! The full literal homogeneous word-operator bound on arbitrary observation subintervals. -/

theorem fibreCoefficient_homogeneous_raw_xnorm_bound
    (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreWordRadius Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (S s₀ a b : ℝ) (hS : 1 ≤ S) (hsa : s₀ ≤ a) (hab : a ≤ b) (hbS : b ≤ s₀ + S) :
    let r := fibreCoefficientFamily η Cw hη G hG hv hw
    let C := fibreCoefficients η G v ξ (fibreSeriesC (fibreCoefficientSymbol η G v r) ξ)
    ∀ D : ℝ → RawJet2 1 ℂ,
      IsCellSolution (Icc s₀ b) C (fun _ _ => 0) (fun _ _ => 0) D →
      fibreXNorm C.θ (Icc a b) D ≤
        ENNReal.ofReal (fibreWordHomogeneousNormConstant Cw * (1 + Real.sqrt S * fibreNorm ξ)) *
          cellL2Norm (cellValue D s₀) := by
  let r := fibreCoefficientFamily η Cw hη G hG hv hw
  let C := fibreCoefficients η G v ξ (fibreSeriesC (fibreCoefficientSymbol η G v r) ξ)
  dsimp only
  intro D hD
  have hsb := hsa.trans hab
  have hξR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := by
    have ht := (hξ.trans (fibreWordRadius_le_graph Cw)).trans
      (fibreEvolutionRadius_le_majorant (Cw := Cw))
    have hp := fibreCoefficientMajorantRadius_pos hCw
    linarith
  have h := fibreCoefficient_raw_homogeneous_to_Hilbert hsb η Cw hη0 hη hCw G hG hv hw ξ hξR V hb D hD
  have hval := fibreCoefficient_homogeneous_uniform_value_bound η Cw hη0 hη hCw G hG hg hgsmall hv hm hw
    V hb ξ hξ hsb (cellRawTrace D) (cellH1Slice D) h
  have hgrad := fibreCoefficient_homogeneous_cov_gradient_bound η Cw hη0 hη hCw G hG hg hgsmall hv hm hw
    V hb ξ hξ hsb (cellRawTrace D) (cellH1Slice D) h
  let A := fibreWordHomogeneousAmplitude Cw * ‖cellRawTrace D s₀‖
  let E := ∫ t in s₀..b, ∑ j, ‖cellShiftedDerivativeCLM C.θ j (cellH1Slice D t)‖ ^ 2
  have hA : 0 ≤ A := mul_nonneg (fibreWord_amplitudes_pos hCw).1.le (norm_nonneg _)
  have hX := cellSolution_fibreXNorm_le_of_state_bounds hsb hD C.θ (cellRawTrace D) (cellH1Slice D)
    (fun t ht => cellRawTrace_ae D t (hD.2.2.1 t ht).1) h.state (cellSolution_slice_ae hD)
    A E hA hval le_rfl
  have hδ : b - s₀ ≤ S := by linarith
  have hbudget := word_homogeneous_norm_budget (fibreCoefficientMajorantRadius Cw)
    (fibreWordHomogeneousAmplitude Cw) (fibreNorm ξ) S (b - s₀) A E ‖cellRawTrace D s₀‖
    (fibreCoefficientMajorantRadius_pos hCw) (fibreWord_amplitudes_pos hCw).1.le
    (fibreNorm_nonneg ξ) hS hδ (norm_nonneg _) le_rfl hgrad
  have hnorm : cellL2Norm (cellValue D s₀) = ENNReal.ofReal ‖cellRawTrace D s₀‖ :=
    cellL2Norm_eq_of_class _ _ (cellRawTrace_ae D s₀ (hD.2.2.1 s₀ ⟨le_rfl, hsb⟩).1)
  have hCpos := (fibreWord_norm_constants_pos hCw).1
  have hfn := fibreNorm_nonneg ξ
  calc
    _ ≤ fibreXNorm C.θ (Icc s₀ b) D := fibreXNorm_mono (Icc_subset_Icc hsa le_rfl) _ _
    _ ≤ ENNReal.ofReal (A + Real.sqrt E) := hX
    _ ≤ ENNReal.ofReal (fibreWordHomogeneousNormConstant Cw * (1 + Real.sqrt S * fibreNorm ξ) *
        ‖cellRawTrace D s₀‖) := ENNReal.ofReal_le_ofReal hbudget
    _ = _ := by rw [ENNReal.ofReal_mul (by positivity), hnorm]

/-! The actual forced analytic family inherits the uniform raw operator budget. -/

theorem fibreCoefficientForced_readout_bound {a b : ℝ} (hab : a ≤ b)
    (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (S : ℝ) (hS : 1 ≤ S) (hbS : b ≤ a + S)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreWordRadius Cw) :
    let z := fibreCoefficientEnergyFamily hab η Cw hη0 hη hCw G hG hv hw V hb
      (cellDivergenceEnergyDatum a b F hF) ξ
    let A := fibreWordForcedNormConstant Cw * (1 + Real.sqrt S * fibreNorm ξ) ^ 2 * cellDivergenceEnergyBudget a b F
    ‖cellEnergySpaceTraceCLM a b z‖ ≤ A ∧
      ∀ j : Fin 2, ‖cellEnergySpaceShiftedDerivativeCLM hab (Real.sqrt η • ξ) j z‖ ≤ A := by
  let d := cellDivergenceEnergyDatum a b F hF
  let z := fibreCoefficientEnergyFamily hab η Cw hη0 hη hCw G hG hv hw V hb d ξ
  let D := fibreCoefficientRawJetFamily hab η Cw hη0 hη hCw G hG hv hw V hb d (0, 0) ξ
  have hR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := by
    have ht := (hξ.trans (fibreWordRadius_le_graph Cw)).trans
      (fibreEvolutionRadius_le_majorant (Cw := Cw))
    linarith [fibreCoefficientMajorantRadius_pos hCw]
  have hs := fibreCoefficientForcedJetFamily_solves hab η Cw hη0 hη hCw G hG hv hw V hb F hF ξ hR
  have hi := fibreCoefficientRawJetFamily_initial_ae hab η Cw hη0 hη hCw G hG hv hw V hb d ξ hR
  have hi0 : cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] 0 :=
    hi.trans (Lp.coeFn_zero (E := ℂ) (p := 2) (μ := volume.restrict AVenhance.unitCube))
  have hcp := (fibreWord_norm_constants_pos hCw).2
  have hfn := fibreNorm_nonneg ξ
  have hQ : 0 ≤ cellDivergenceEnergyBudget a b F := Real.sqrt_nonneg _
  have hx := fibreCoefficient_forced_raw_xnorm_bound η Cw hη0 hη hCw G hG hg hgsmall
    hv hm hw ξ hξ V hb S a a b hS le_rfl hab hbS F hF D hs hi0
  rw [cellFlux_finite_energy_half_norm hab F hF, ← ENNReal.ofReal_mul (by positivity)] at hx
  have hrep : IsCellEnergySpaceRawRepresentative hab z D :=
    cellEnergySpaceAnalyticRawJet_zero_represents hab _ ξ
  constructor
  · exact cellEnergySpaceRaw_trace_budget hab z D hrep (Real.sqrt η • ξ) _ (by
      exact mul_nonneg (mul_nonneg (fibreWord_norm_constants_pos hCw).2.le
        (by positivity)) hQ) hx
  · intro j
    exact cellEnergySpaceRaw_shifted_budget hab z D hrep (Real.sqrt η • ξ) _ (by
      exact mul_nonneg (mul_nonneg (fibreWord_norm_constants_pos hCw).2.le
        (by positivity)) hQ) hx j

/-! The actual homogeneous analytic family inherits the uniform raw operator budget. -/

theorem fibreCoefficientHomogeneous_readout_bound {a b : ℝ} (hab : a ≤ b)
    (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (u : ComplexCellL2) (S : ℝ) (hS : 1 ≤ S) (hbS : b ≤ a + S)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreWordRadius Cw) :
    let z := fibreCoefficientEnergyFamily hab η Cw hη0 hη hCw G hG hv hw V hb
      (cellHomogeneousEnergyDatum a b u) ξ
    let A := fibreWordHomogeneousNormConstant Cw * (1 + Real.sqrt S * fibreNorm ξ) * ‖u‖
    ‖cellEnergySpaceTraceCLM a b z‖ ≤ A ∧
      ∀ j : Fin 2, ‖cellEnergySpaceShiftedDerivativeCLM hab (Real.sqrt η • ξ) j z‖ ≤ A := by
  let d := cellHomogeneousEnergyDatum a b u
  let z := fibreCoefficientEnergyFamily hab η Cw hη0 hη hCw G hG hv hw V hb d ξ
  let D := fibreCoefficientRawJetFamily hab η Cw hη0 hη hCw G hG hv hw V hb d (0, 0) ξ
  have hR : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw := by
    have ht := (hξ.trans (fibreWordRadius_le_graph Cw)).trans
      (fibreEvolutionRadius_le_majorant (Cw := Cw))
    linarith [fibreCoefficientMajorantRadius_pos hCw]
  have hs := fibreCoefficientHomogeneousJetFamily_solves hab η Cw hη0 hη hCw G hG hv hw V hb u ξ hR
  have hi := fibreCoefficientRawJetFamily_initial_ae hab η Cw hη0 hη hCw G hG hv hw V hb d ξ hR
  have hn : cellL2Norm (cellValue D a) = ENNReal.ofReal ‖u‖ :=
    cellL2Norm_eq_of_class _ u hi.symm
  have hcp := (fibreWord_norm_constants_pos hCw).1
  have hfn := fibreNorm_nonneg ξ
  have hx := fibreCoefficient_homogeneous_raw_xnorm_bound η Cw hη0 hη hCw G hG hg hgsmall
    hv hm hw ξ hξ V hb S a a b hS le_rfl hab hbS D hs
  rw [hn, ← ENNReal.ofReal_mul (by positivity)] at hx
  have hrep : IsCellEnergySpaceRawRepresentative hab z D :=
    cellEnergySpaceAnalyticRawJet_zero_represents hab _ ξ
  constructor
  · exact cellEnergySpaceRaw_trace_budget hab z D hrep (Real.sqrt η • ξ) _ (by
      exact mul_nonneg (mul_nonneg (fibreWord_norm_constants_pos hCw).1.le
        (by positivity)) (norm_nonneg u)) hx
  · intro j
    exact cellEnergySpaceRaw_shifted_budget hab z D hrep (Real.sqrt η • ξ) _ (by
      exact mul_nonneg (mul_nonneg (fibreWord_norm_constants_pos hCw).1.le
        (by positivity)) (norm_nonneg u)) hx j

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Metric Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Uniform fixed-frequency readout budgets on the forced parabolic Cauchy ball. -/

theorem fibreCoefficientForced_ball_readout_bound {a b : ℝ} (hab : a ≤ b)
    (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (S : ℝ) (hS : 1 ≤ S) (hbS : b ≤ a + S)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ < fibreWordRadius Cw / 4) :
    let f := fibreCoefficientEnergyFamily hab η Cw hη0 hη hCw G hG hv hw V hb
      (cellDivergenceEnergyDatum a b F hF)
    let M := 18 * fibreWordForcedNormConstant Cw * (1 + Real.sqrt S * fibreNorm ξ) ^ 2 * cellDivergenceEnergyBudget a b F
    ∀ ζ ∈ ball ξ (fibreWordCauchyRadius Cw S),
      ‖cellEnergySpaceTraceCLM a b (f ζ)‖ ≤ M ∧
      ∀ j : Fin 2, ‖cellEnergySpaceShiftedDerivativeCLM hab (Real.sqrt η • ξ) j (f ζ)‖ ≤ M := by
  intro f M ζ hζ
  have hz := fibreWordFrequencyBall_subset hCw hS ξ hξ hζ
  have hbase := fibreCoefficientForced_readout_bound hab η Cw hη0 hη hCw G hG hg hgsmall
    hv hm hw V hb F hF S hS hbS ζ hz.le
  let A := 9 * fibreWordForcedNormConstant Cw * (1 + Real.sqrt S * fibreNorm ξ) ^ 2 * cellDivergenceEnergyBudget a b F
  have hcp := (fibreWord_norm_constants_pos hCw).2
  have hfn := fibreNorm_nonneg ξ
  have hQ : 0 ≤ cellDivergenceEnergyBudget a b F := Real.sqrt_nonneg _
  have hfnζ := fibreNorm_nonneg ζ
  have hpoly := fibreWordFrequencyBall_polynomial_le hCw hS ξ hζ
  have hpoly2 := (sq_le_sq₀ (by positivity : 0 ≤ 1 + Real.sqrt S * fibreNorm ζ)
    (by positivity : 0 ≤ 3 * (1 + Real.sqrt S * fibreNorm ξ))).2 hpoly
  have hbound : fibreWordForcedNormConstant Cw * (1 + Real.sqrt S * fibreNorm ζ) ^ 2 * cellDivergenceEnergyBudget a b F ≤ A := by
    dsimp only [A]
    calc
      _ ≤ fibreWordForcedNormConstant Cw * (3 * (1 + Real.sqrt S * fibreNorm ξ)) ^ 2 * cellDivergenceEnergyBudget a b F :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly2 hcp.le) hQ
      _ = _ := by ring
  have ht : ‖cellEnergySpaceTraceCLM a b (f ζ)‖ ≤ A := hbase.1.trans hbound
  have hgζ (j : Fin 2) : ‖cellEnergySpaceShiftedDerivativeCLM hab (Real.sqrt η • ζ) j (f ζ)‖ ≤ A :=
    (hbase.2 j).trans hbound
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hAM : A ≤ M := by dsimp only [A, M]; nlinarith
  constructor
  · exact ht.trans hAM
  · intro j
    have hc := cellEnergySpaceShiftedDerivative_change_norm hab (f ζ)
      (Real.sqrt η • ξ) (Real.sqrt η • ζ) j
    have hd : ‖(Real.sqrt η • ξ) j - (Real.sqrt η • ζ) j‖ * Real.sqrt (b - a) ≤ 1 :=
      fibreWordFrequencyBall_shift_factor_le hCw hS hη (by linarith) ξ hζ j
    have he := mul_le_mul hd ht (norm_nonneg (cellEnergySpaceTraceCLM a b (f ζ))) (by norm_num)
    have hn := add_le_add (hgζ j) he
    have h2 : A + 1 * A = M := by dsimp only [A, M]; ring
    exact hc.trans (hn.trans_eq h2)

/-! Uniform fixed-frequency readout budgets on the homogeneous parabolic Cauchy ball. -/

theorem fibreCoefficientHomogeneous_ball_readout_bound {a b : ℝ} (hab : a ≤ b)
    (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (u : ComplexCellL2) (S : ℝ) (hS : 1 ≤ S) (hbS : b ≤ a + S)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ < fibreWordRadius Cw / 4) :
    let f := fibreCoefficientEnergyFamily hab η Cw hη0 hη hCw G hG hv hw V hb
      (cellHomogeneousEnergyDatum a b u)
    let M := 6 * fibreWordHomogeneousNormConstant Cw * (1 + Real.sqrt S * fibreNorm ξ) * ‖u‖
    ∀ ζ ∈ ball ξ (fibreWordCauchyRadius Cw S),
      ‖cellEnergySpaceTraceCLM a b (f ζ)‖ ≤ M ∧
      ∀ j : Fin 2, ‖cellEnergySpaceShiftedDerivativeCLM hab (Real.sqrt η • ξ) j (f ζ)‖ ≤ M := by
  intro f M ζ hζ
  have hz := fibreWordFrequencyBall_subset hCw hS ξ hξ hζ
  have hbase := fibreCoefficientHomogeneous_readout_bound hab η Cw hη0 hη hCw G hG hg hgsmall
    hv hm hw V hb u S hS hbS ζ hz.le
  let A := 3 * fibreWordHomogeneousNormConstant Cw * (1 + Real.sqrt S * fibreNorm ξ) * ‖u‖
  have hcp := (fibreWord_norm_constants_pos hCw).1
  have hfn := fibreNorm_nonneg ξ
  have hpoly := fibreWordFrequencyBall_polynomial_le hCw hS ξ hζ
  have hbound : fibreWordHomogeneousNormConstant Cw * (1 + Real.sqrt S * fibreNorm ζ) * ‖u‖ ≤ A := by
    dsimp only [A]
    calc
      _ ≤ fibreWordHomogeneousNormConstant Cw * (3 * (1 + Real.sqrt S * fibreNorm ξ)) * ‖u‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly hcp.le) (norm_nonneg u)
      _ = _ := by ring
  have ht : ‖cellEnergySpaceTraceCLM a b (f ζ)‖ ≤ A := hbase.1.trans hbound
  have hgζ (j : Fin 2) : ‖cellEnergySpaceShiftedDerivativeCLM hab (Real.sqrt η • ζ) j (f ζ)‖ ≤ A :=
    (hbase.2 j).trans hbound
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hAM : A ≤ M := by dsimp only [A, M]; nlinarith
  constructor
  · exact ht.trans hAM
  · intro j
    have hc := cellEnergySpaceShiftedDerivative_change_norm hab (f ζ)
      (Real.sqrt η • ξ) (Real.sqrt η • ζ) j
    have hd : ‖(Real.sqrt η • ξ) j - (Real.sqrt η • ζ) j‖ * Real.sqrt (b - a) ≤ 1 :=
      fibreWordFrequencyBall_shift_factor_le hCw hS hη (by linarith) ξ hζ j
    have he := mul_le_mul hd ht (norm_nonneg (cellEnergySpaceTraceCLM a b (f ζ))) (by norm_num)
    have hn := add_le_add (hgζ j) he
    have h2 : A + 1 * A = M := by dsimp only [A, M]; ring
    exact hc.trans (hn.trans_eq h2)

/-! Full quantitative forced frequency jets of the actual normalized solution operator. -/

def fibreWordForcedJetConstant (Cw : ℝ) (n : ℕ) : ℝ :=
  54 * fibreWordForcedNormConstant Cw * analyticBallDerivativeConstant n *
    (16 / fibreWordRadius Cw) ^ n

theorem fibreCoefficientForced_raw_jet_bound {a b : ℝ} (hab : a ≤ b)
    (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (S : ℝ) (hS : 1 ≤ S) (hbS : b ≤ a + S)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ < fibreWordRadius Cw / 4) (p : ℕ × ℕ) :
    fibreXNorm (Real.sqrt η • ξ) (Icc a b)
      (fibreCoefficientRawJetFamily hab η Cw hη0 hη hCw G hG hv hw V hb
        (cellDivergenceEnergyDatum a b F hF) p ξ) ≤
      ENNReal.ofReal (fibreWordForcedJetConstant Cw (p.1 + p.2) *
        Real.sqrt S ^ (p.1 + p.2) * (1 + Real.sqrt S * fibreNorm ξ) ^ 2 * cellDivergenceEnergyBudget a b F) := by
  let f := fibreCoefficientEnergyFamily hab η Cw hη0 hη hCw G hG hv hw V hb
    (cellDivergenceEnergyDatum a b F hF)
  let R := fibreWordCauchyRadius Cw S
  let M := 18 * fibreWordForcedNormConstant Cw * (1 + Real.sqrt S * fibreNorm ξ) ^ 2 * cellDivergenceEnergyBudget a b F
  have hr := fibreWordCauchyRadius_pos hCw hS
  have ha : AnalyticOnNhd ℂ f (ball ξ R) := by
    intro ζ hζ
    have hz := fibreWordFrequencyBall_subset hCw hS ξ hξ hζ
    have hwR := (fibreWordRadius_le_graph Cw).trans (fibreEvolutionRadius_le_majorant (Cw := Cw))
    have hzR : fibreNorm ζ < fibreCoefficientMajorantRadius Cw := by
      linarith [fibreCoefficientMajorantRadius_pos hCw]
    exact fibreCoefficientEnergyFamily_analyticAt hab η Cw hη0 hη hCw G hG hv hw V hb _ ζ hzR
  have hbounds := fibreCoefficientForced_ball_readout_bound hab η Cw hη0 hη hCw
    G hG hg hgsmall hv hm hw V hb F hF S hS hbS ξ hξ
  have hx := cellEnergySpaceRawJet_cauchy_bound hab f ξ (Real.sqrt η • ξ) R M hr ha
    (fun ζ hζ => (hbounds ζ hζ).1) (fun ζ hζ => (hbounds ζ hζ).2) p
  apply hx.trans_eq
  congr 1
  dsimp only [R, M, fibreWordForcedJetConstant, fibreWordCauchyRadius]
  have hwr := (fibreWordRadius_pos hCw).ne'
  have hs : Real.sqrt S ≠ 0 := (Real.sqrt_pos.2 (by linarith : 0 < S)).ne'
  rw [div_pow, mul_pow, div_pow]
  field_simp
  ring

/-! Full quantitative homogeneous frequency jets of the actual normalized solution operator. -/

def fibreWordHomogeneousJetConstant (Cw : ℝ) (n : ℕ) : ℝ :=
  18 * fibreWordHomogeneousNormConstant Cw * analyticBallDerivativeConstant n *
    (16 / fibreWordRadius Cw) ^ n

theorem fibreCoefficientHomogeneous_raw_jet_bound {a b : ℝ} (hab : a ≤ b)
    (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (u : ComplexCellL2) (S : ℝ) (hS : 1 ≤ S) (hbS : b ≤ a + S)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ < fibreWordRadius Cw / 4) (p : ℕ × ℕ) :
    fibreXNorm (Real.sqrt η • ξ) (Icc a b)
      (fibreCoefficientRawJetFamily hab η Cw hη0 hη hCw G hG hv hw V hb
        (cellHomogeneousEnergyDatum a b u) p ξ) ≤
      ENNReal.ofReal (fibreWordHomogeneousJetConstant Cw (p.1 + p.2) *
        Real.sqrt S ^ (p.1 + p.2) * (1 + Real.sqrt S * fibreNorm ξ) * ‖u‖) := by
  let f := fibreCoefficientEnergyFamily hab η Cw hη0 hη hCw G hG hv hw V hb
    (cellHomogeneousEnergyDatum a b u)
  let R := fibreWordCauchyRadius Cw S
  let M := 6 * fibreWordHomogeneousNormConstant Cw * (1 + Real.sqrt S * fibreNorm ξ) * ‖u‖
  have hr := fibreWordCauchyRadius_pos hCw hS
  have ha : AnalyticOnNhd ℂ f (ball ξ R) := by
    intro ζ hζ
    have hz := fibreWordFrequencyBall_subset hCw hS ξ hξ hζ
    have hwR := (fibreWordRadius_le_graph Cw).trans (fibreEvolutionRadius_le_majorant (Cw := Cw))
    have hzR : fibreNorm ζ < fibreCoefficientMajorantRadius Cw := by
      linarith [fibreCoefficientMajorantRadius_pos hCw]
    exact fibreCoefficientEnergyFamily_analyticAt hab η Cw hη0 hη hCw G hG hv hw V hb _ ζ hzR
  have hbounds := fibreCoefficientHomogeneous_ball_readout_bound hab η Cw hη0 hη hCw
    G hG hg hgsmall hv hm hw V hb u S hS hbS ξ hξ
  have hx := cellEnergySpaceRawJet_cauchy_bound hab f ξ (Real.sqrt η • ξ) R M hr ha
    (fun ζ hζ => (hbounds ζ hζ).1) (fun ζ hζ => (hbounds ζ hζ).2) p
  apply hx.trans_eq
  congr 1
  dsimp only [R, M, fibreWordHomogeneousJetConstant, fibreWordCauchyRadius]
  have hwr := (fibreWordRadius_pos hCw).ne'
  have hs : Real.sqrt S ≠ 0 := (Real.sqrt_pos.2 (by linarith : 0 < S)).ne'
  rw [div_pow, mul_pow, div_pow]
  field_simp
  ring

end AVRegularity.CycleEvolution
end

section
namespace AVRegularity.CycleEvolution

/-! Universal constants dominating both actual operator jets and the phase jets. -/

def fibreWordGateConstant (Cw : ℝ) : ℝ := 1 + fibreCoefficientGraphBound Cw +
  fibreWordHomogeneousNormConstant Cw + fibreWordForcedNormConstant Cw

def fibreWordGateJetConstant (Cw : ℝ) (K : ℕ) : ℝ := 1 + ∑ n ∈ Finset.range (K + 1),
  (fibreWordHomogeneousJetConstant Cw n + fibreWordForcedJetConstant Cw n + fibrePhaseJetConstant Cw n)

theorem fibreWordGateConstant_bounds {Cw : ℝ} (hCw : 0 ≤ Cw) :
    0 < fibreWordGateConstant Cw ∧ fibreCoefficientGraphBound Cw ≤ fibreWordGateConstant Cw ∧
      fibreWordHomogeneousNormConstant Cw ≤ fibreWordGateConstant Cw ∧
      fibreWordForcedNormConstant Cw ≤ fibreWordGateConstant Cw := by
  have hh := (fibreWord_norm_constants_pos hCw).1
  have hf := (fibreWord_norm_constants_pos hCw).2
  have hR := fibreCoefficientMajorantRadius_pos hCw
  have hg : 0 ≤ fibreCoefficientGraphBound Cw := by unfold fibreCoefficientGraphBound; positivity
  unfold fibreWordGateConstant
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem fibreWordJetConstants_pos {Cw : ℝ} (hCw : 0 ≤ Cw) (n : ℕ) :
    0 < fibreWordHomogeneousJetConstant Cw n ∧ 0 < fibreWordForcedJetConstant Cw n := by
  have hh := (fibreWord_norm_constants_pos hCw).1
  have hf := (fibreWord_norm_constants_pos hCw).2
  have ha := analyticBallDerivativeConstant_pos n
  have hw := fibreWordRadius_pos hCw
  unfold fibreWordHomogeneousJetConstant fibreWordForcedJetConstant
  constructor <;> positivity

theorem fibreWordGateJetConstant_pos {Cw : ℝ} (hCw : 0 ≤ Cw) (K : ℕ) :
    0 < fibreWordGateJetConstant Cw K := by
  have hn n : 0 ≤ fibreWordHomogeneousJetConstant Cw n + fibreWordForcedJetConstant Cw n +
      fibrePhaseJetConstant Cw n := by
    have hh := fibreWordJetConstants_pos hCw n
    have hp := fibrePhaseJetConstant_pos hCw n
    exact add_nonneg (add_nonneg hh.1.le hh.2.le) hp.le
  have hs := Finset.sum_nonneg (s := Finset.range (K + 1)) (fun n _ => hn n)
  unfold fibreWordGateJetConstant
  linarith

theorem fibreWordGateJetConstant_bounds {Cw : ℝ} (hCw : 0 ≤ Cw) {n K : ℕ} (hn : n ≤ K) :
    fibreWordHomogeneousJetConstant Cw n ≤ fibreWordGateJetConstant Cw K ∧
      fibreWordForcedJetConstant Cw n ≤ fibreWordGateJetConstant Cw K ∧
      fibrePhaseJetConstant Cw n ≤ fibreWordGateJetConstant Cw K := by
  have hp k := fibreWordJetConstants_pos hCw k
  have hphase k := fibrePhaseJetConstant_pos hCw k
  have hsum := Finset.single_le_sum
    (f := fun k => fibreWordHomogeneousJetConstant Cw k + fibreWordForcedJetConstant Cw k +
      fibrePhaseJetConstant Cw k)
    (fun k _ => add_nonneg (add_nonneg (hp k).1.le (hp k).2.le) (hphase k).le)
    (show n ∈ Finset.range (K + 1) from Finset.mem_range.mpr (by omega))
  have hh := hp n
  have hx := hphase n
  unfold fibreWordGateJetConstant
  constructor
  · linarith
  constructor <;> linarith

end AVRegularity.CycleEvolution
end
end
end

section
@[expose] public noncomputable section
section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The forced norm-jet clause with literal L2 data and observation subintervals. -/

theorem fibreWord_forced_jets
    (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (S s₀ a b : ℝ) (hS : 1 ≤ S) (hsa : s₀ ≤ a) (hab : a ≤ b) (hbS : b ≤ s₀ + S)
    (K : ℕ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hFm : Measurable (Function.uncurry F))
    (hFinite : (∫⁻ τ in Icc s₀ b, cellL2Norm (F τ) ^ 2) < ⊤) :
    ∃ J : ℕ × ℕ → (Fin 2 → ℂ) → ℝ → RawJet2 1 ℂ,
      IsNormJetFamily (𝕜 := ℂ) (cellEnergyNorm (Icc s₀ b)) K
        {ξ | fibreNorm ξ < fibreWordRadius Cw / 4} J ∧
      (∀ ξ : Fin 2 → ℂ, fibreNorm ξ < fibreWordRadius Cw / 4 →
        IsCellSolution (Icc s₀ b)
          (fibreCoefficients η G v ξ (fibreSeriesC (fibreCoefficientSymbol η G v
            (fibreCoefficientFamily η Cw hη G hG hv hw)) ξ)) (fun _ _ => 0) F
          (J (0, 0) ξ) ∧
        cellValue (J (0, 0) ξ) s₀ =ᵐ[volume.restrict AVenhance.unitCube] 0) ∧
      ∀ α : ℕ × ℕ, α.1 + α.2 ≤ K → ∀ ξ : Fin 2 → ℂ, fibreNorm ξ < fibreWordRadius Cw / 4 →
        fibreXNorm (Real.sqrt η • ξ) (Icc a b) (J α ξ) ≤
          ENNReal.ofReal (fibreWordGateJetConstant Cw K * Real.sqrt S ^ (α.1 + α.2) *
            (1 + Real.sqrt S * fibreNorm ξ) ^ 2) *
            (∫⁻ τ in Icc s₀ b, cellL2Norm (F τ) ^ 2) ^ (1 / 2 : ℝ) := by
  have hsb := hsa.trans hab
  have hF := cellSource_memLp_product (Icc s₀ b) F hFm hFinite
  let d := cellDivergenceEnergyDatum s₀ b F hF
  let J := fibreCoefficientRawJetFamily hsb η Cw hη0 hη hCw G hG hv hw V hb d
  have hR ξ (hξ : fibreNorm ξ < fibreWordRadius Cw / 4) :
      fibreNorm ξ < fibreCoefficientMajorantRadius Cw := by
    have ht := (fibreWordRadius_le_graph Cw).trans (fibreEvolutionRadius_le_majorant (Cw := Cw))
    linarith [fibreWordRadius_pos hCw, fibreCoefficientMajorantRadius_pos hCw]
  have hjet := fibreCoefficientRawJetFamily_isNormJetFamily hsb η Cw hη0 hη hCw G hG hv hw V hb d K
  refine ⟨J, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro p hp ξ hξ
    exact hjet.1 p hp ξ (hR ξ hξ)
  · intro p hp ξ hξ
    exact hjet.2 p hp ξ (hR ξ hξ)
  · intro ξ hξ
    exact ⟨fibreCoefficientForcedJetFamily_solves hsb η Cw hη0 hη hCw G hG hv hw V hb F hF ξ (hR ξ hξ).le,
      (fibreCoefficientRawJetFamily_initial_ae hsb η Cw hη0 hη hCw G hG hv hw V hb d ξ
        (hR ξ hξ).le).trans (Lp.coeFn_zero (E := ℂ) (p := 2)
          (μ := volume.restrict AVenhance.unitCube))⟩
  · intro α hα ξ hξ
    have hn := fibreNorm_nonneg ξ
    have hbound := fibreCoefficientForced_raw_jet_bound hsb η Cw hη0 hη hCw G hG hg hgsmall
      hv hm hw V hb F hF S hS hbS ξ hξ α
    have hCj := (fibreWordGateJetConstant_bounds hCw hα).2.1
    have hnorm := cellFlux_finite_energy_half_norm hsb F hF
    have hQ : 0 ≤ cellDivergenceEnergyBudget s₀ b F := Real.sqrt_nonneg _
    have hCJpos := fibreWordGateJetConstant_pos hCw K
    calc
      _ ≤ fibreXNorm (Real.sqrt η • ξ) (Icc s₀ b) (J α ξ) :=
        fibreXNorm_mono (Icc_subset_Icc hsa le_rfl) _ _
      _ ≤ _ := hbound
      _ ≤ ENNReal.ofReal (fibreWordGateJetConstant Cw K * Real.sqrt S ^ (α.1 + α.2) *
          (1 + Real.sqrt S * fibreNorm ξ) ^ 2 * cellDivergenceEnergyBudget s₀ b F) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCj (by positivity))
            (by positivity)) hQ
      _ = _ := by rw [ENNReal.ofReal_mul (by positivity), hnorm]; rfl

/-! The homogeneous norm-jet clause with literal L2 data and observation subintervals. -/

theorem fibreWord_homogeneous_jets
    (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (S s₀ a b : ℝ) (hS : 1 ≤ S) (hsa : s₀ ≤ a) (hab : a ≤ b) (hbS : b ≤ s₀ + S)
    (K : ℕ) (h₀ : Vec 2 → ℂ) (hh₀ : cellL2Norm h₀ < ⊤) :
    ∃ J : ℕ × ℕ → (Fin 2 → ℂ) → ℝ → RawJet2 1 ℂ,
      IsNormJetFamily (𝕜 := ℂ) (cellEnergyNorm (Icc s₀ b)) K
        {ξ | fibreNorm ξ < fibreWordRadius Cw / 4} J ∧
      (∀ ξ : Fin 2 → ℂ, fibreNorm ξ < fibreWordRadius Cw / 4 →
        IsCellSolution (Icc s₀ b)
          (fibreCoefficients η G v ξ (fibreSeriesC (fibreCoefficientSymbol η G v
            (fibreCoefficientFamily η Cw hη G hG hv hw)) ξ)) (fun _ _ => 0) (fun _ _ => 0)
          (J (0, 0) ξ) ∧
        cellValue (J (0, 0) ξ) s₀ =ᵐ[volume.restrict AVenhance.unitCube] h₀) ∧
      ∀ α : ℕ × ℕ, α.1 + α.2 ≤ K → ∀ ξ : Fin 2 → ℂ, fibreNorm ξ < fibreWordRadius Cw / 4 →
        fibreXNorm (Real.sqrt η • ξ) (Icc a b) (J α ξ) ≤
          ENNReal.ofReal (fibreWordGateJetConstant Cw K * Real.sqrt S ^ (α.1 + α.2) *
            (1 + Real.sqrt S * fibreNorm ξ)) * cellL2Norm h₀ := by
  have hsb := hsa.trans hab
  have hh : MemLp h₀ 2 (volume.restrict AVenhance.unitCube) := hh₀
  let u := hh.toLp h₀
  let d := cellHomogeneousEnergyDatum s₀ b u
  let J := fibreCoefficientRawJetFamily hsb η Cw hη0 hη hCw G hG hv hw V hb d
  have hR ξ (hξ : fibreNorm ξ < fibreWordRadius Cw / 4) :
      fibreNorm ξ < fibreCoefficientMajorantRadius Cw := by
    have ht := (fibreWordRadius_le_graph Cw).trans (fibreEvolutionRadius_le_majorant (Cw := Cw))
    linarith [fibreWordRadius_pos hCw, fibreCoefficientMajorantRadius_pos hCw]
  have hjet := fibreCoefficientRawJetFamily_isNormJetFamily hsb η Cw hη0 hη hCw G hG hv hw V hb d K
  refine ⟨J, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro p hp ξ hξ
    exact hjet.1 p hp ξ (hR ξ hξ)
  · intro p hp ξ hξ
    exact hjet.2 p hp ξ (hR ξ hξ)
  · intro ξ hξ
    exact ⟨fibreCoefficientHomogeneousJetFamily_solves hsb η Cw hη0 hη hCw G hG hv hw V hb u ξ (hR ξ hξ).le,
      (fibreCoefficientRawJetFamily_initial_ae hsb η Cw hη0 hη hCw G hG hv hw V hb d ξ
        (hR ξ hξ).le).trans hh.coeFn_toLp⟩
  · intro α hα ξ hξ
    have hn := fibreNorm_nonneg ξ
    have hbound := fibreCoefficientHomogeneous_raw_jet_bound hsb η Cw hη0 hη hCw G hG hg hgsmall
      hv hm hw V hb u S hS hbS ξ hξ α
    have hCj := (fibreWordGateJetConstant_bounds hCw hα).1
    have hCJpos := fibreWordGateJetConstant_pos hCw K
    have hnorm : cellL2Norm h₀ = ENNReal.ofReal ‖u‖ := cellL2Norm_eq_of_class _ _ hh.coeFn_toLp
    calc
      _ ≤ fibreXNorm (Real.sqrt η • ξ) (Icc s₀ b) (J α ξ) :=
        fibreXNorm_mono (Icc_subset_Icc hsa le_rfl) _ _
      _ ≤ _ := hbound
      _ ≤ ENNReal.ofReal (fibreWordGateJetConstant Cw K * Real.sqrt S ^ (α.1 + α.2) *
          (1 + Real.sqrt S * fibreNorm ξ) * ‖u‖) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCj (by positivity))
            (by positivity)) (norm_nonneg u)
      _ = _ := by rw [ENNReal.ofReal_mul (by positivity), hnorm]

end AVRegularity.CycleEvolution
end
end
end
