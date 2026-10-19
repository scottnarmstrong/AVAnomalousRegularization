-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.CellEnergySeriesRegularity
import AVRegularity.CycleEvolution.CellLimitMoments
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Exact spatial identification of the normalized graph operator with the literal Bloch generator. -/

theorem cellNormalizedGraph_generator (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v) (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (θ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) (u z : TorusHk 1 ℂ) :
    cellComplexGenerator ⟨fun t _ => G t, v, θ, κ⟩ hG V hv.1 hb t (u + cellH1One) z =
      cellComplexGenerator ⟨fun t _ => G t, v, 0, 0⟩ hG V hv.1 hb t u z +
        cellComplexSource (fun _ => 0) (cellNormalizedGraphSourceClass G v V hv hb θ κ t u)
          (cellNormalizedGraphFluxClass G θ t u) z := by
  rw [cellComplexGenerator_decomposition ⟨fun t _ => G t, v, θ, κ⟩ hG V hv hb,
    cellConstantMetric_graph_diffusion, cellComplexGenerator_plain hG hv V hb]
  simp only [cellComplexShiftedDriftForm, cellComplexDriftForm_add_one,
    cellNormalizedGraphSourceClass, cellNormalizedGraphFluxClass, cellComplexSource,
    star_zero, cellShiftedDerivative_zero_apply, map_add, cellH1One_value,
    Fin.sum_univ_two, cellComplexPair_add_left, cellComplexPair_scalar_left]
  ring

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The literal raw fibre X norm is the actual trace supremum plus shifted Hilbert gradient energy. -/

theorem cellEnergySpaceRaw_fibreXNorm {a b : ℝ} (hab : a ≤ b)
    (z : CellEnergySpace a b) (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellEnergySpaceRawRepresentative hab z D) (θ : Fin 2 → ℂ) :
    fibreXNorm θ (Icc a b) D = (⨆ t ∈ Icc a b, ENNReal.ofReal ‖cellEnergySpaceTrace hab z t‖) +
      ENNReal.ofReal (Real.sqrt (∫ t in a..b, ∑ j, ‖cellShiftedDerivativeCLM θ j (cellEnergySpaceState hab z t)‖ ^ 2)) := by
  unfold fibreXNorm
  congr 1
  · apply iSup_congr
    intro t
    apply iSup_congr
    intro ht
    exact cellL2Norm_eq_of_class _ _ (hD.2.1 t)
  · rw [cellRaw_covGradient_lintegral_of_state hab D hD.2.2.1 θ
      (cellEnergySpaceState hab z) (cellEnergySpaceState_memLp hab z) hD.2.2.2.1]
    have hn : 0 ≤ ∫ t in a..b, ∑ j, ‖cellShiftedDerivativeCLM θ j (cellEnergySpaceState hab z t)‖ ^ 2 :=
      intervalIntegral.integral_nonneg hab (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    rw [ENNReal.ofReal_rpow_of_nonneg (p := (1 / 2 : ℝ)) hn (by norm_num), ← Real.sqrt_eq_rpow]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Filter Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.CycleEvolution

/-! Uniform finite-trace bounds for identification of the weak Galerkin limit. -/

variable {a b : ℝ} {hab : a ≤ b} {C : CellCoefficients} {hG : IsCellMetric C.G} {V : ℝ}
  {hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2)}
  {hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2}
  {src : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
  {initial : ComplexCellL2}

/-- The actual finite traces have a nonnegative square budget uniform in time and cutoff. -/
theorem CellGalerkinLimitData.uniform_trace_bound
    (D : CellGalerkinLimitData a b hab C hG V hv hb src F initial)
    (k : ℝ) (hκb : ∀ r, ‖C.κ r‖ ≤ k)
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube))) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ N t, t ∈ Icc a b →
      ‖cellGalerkinValue N (extendCurve hab (D.curve N) t)‖ ^ 2 ≤ E := by
  let S := cellSourceSlice src
  let Q := fun r j => cellSourceSlice (fun t x => F t x j) r
  have hS := cellSourceSlice_memLp (Icc a b) src hsrc
  have hQ (j : Fin 2) := cellSourceSlice_memLp (Icc a b) (fun r x => F r x j)
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).comp_memLp' hF)
  let E := (‖initial‖ ^ 2 + ∫ r in a..b, ‖S r‖ ^ 2 + 9 * ∑ j, ‖Q r j‖ ^ 2) *
    Real.exp (300 * (1 + ∑ j, ‖C.θ j‖ ^ 2 + V ^ 2 + k) * (b - a))
  have hbound : ∀ N t, t ∈ Icc a b →
      ‖cellGalerkinValue N (extendCurve hab (D.curve N) t)‖ ^ 2 ≤ E := by
    intro N t ht
    have he := cellFinite_energy_sup_bound hab N C hG V k hv hb hκb S Q hS hQ _ _ _
      (D.stateLp N) (D.variational N) t ht
    have hn := cellGalerkinL2Initial_norm_le N initial
    have hn2 : ‖cellGalerkinValue N (extendCurve hab (D.curve N) a)‖ ^ 2 ≤ ‖initial‖ ^ 2 := by
      rw [D.initial_value N]
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hn
    exact he.trans (mul_le_mul_of_nonneg_right (add_le_add hn2 le_rfl) (Real.exp_nonneg _))
  exact ⟨E, (sq_nonneg _).trans (hbound 0 a ⟨le_rfl, hab⟩), hbound⟩

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Exact real energy production of the Bloch equation through actual scalar and divergence forcing. -/

theorem cellBlochLinear_generator_real (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2}
    (hv : IsCellDrift v) (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (θ : Fin 2 → ℂ) (t : ℝ) (u : TorusHk 1 ℂ) :
    cellGeneratorForm ⟨fun t _ => G t, v, θ, 0⟩ hG V hv.1 hb t u u =
      -cellMetricEnergy hG t u + inner ℝ (cellBlochLinearSourceClass G v V hv hb θ t u)
        (torusHkValueCLM u) -
      ∑ j : Fin 2, inner ℝ (cellNormalizedGraphFluxClass G θ t u j) (cellDerivativeCLM j u) := by
  have he := congrArg Complex.re (cellBlochLinear_generator G hG hv V hb θ t u u)
  simp only [Complex.add_re, cellComplexGenerator_re, cellComplexSource_re] at he
  rw [cellUnshiftedGenerator_drift_neutral hG hv V hb, cellSourceFunctional_unshifted] at he
  exact he.trans (by ring)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! The literal raw energy norm is controlled by the actual compatible trace and H1 carrier norm. -/

theorem cellEnergySpaceRaw_energyNorm_le {a b : ℝ} (hab : a ≤ b) (z : CellEnergySpace a b)
    (D : ℝ → RawJet2 1 ℂ) (hD : IsCellEnergySpaceRawRepresentative hab z D) :
    cellEnergyNorm (Icc a b) D ≤ ENNReal.ofReal (2 * ‖z‖) := by
  have hE : (∫⁻ t in Icc a b, cellL2Norm (cellGradient (D t)) ^ 2) ≤ (ENNReal.ofReal ‖z‖) ^ 2 := by
    calc
      _ = ENNReal.ofReal (∫ t in a..b, ∑ j, ‖cellDerivativeCLM j (cellEnergySpaceState hab z t)‖ ^ 2) :=
        cellRaw_gradient_lintegral_of_state hab D hD.2.2.1 _
          (cellEnergySpaceState_memLp hab z) hD.2.2.2.1
      _ ≤ ENNReal.ofReal (‖z‖ ^ 2) := ENNReal.ofReal_le_ofReal (cellEnergySpace_gradientSqIntegral_le hab z)
      _ = _ := ENNReal.ofReal_pow (norm_nonneg z) 2
  have hg := cellUlNorm_le_totalEnergy (Icc a b) (fun t => cellGradient (D t)) _ hE
  have hr : ((ENNReal.ofReal ‖z‖) ^ 2) ^ (1 / 2 : ℝ) = ENNReal.ofReal ‖z‖ := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hv : (⨆ t ∈ Icc a b, cellL2Norm (cellValue D t)) ≤ ENNReal.ofReal ‖z‖ := by
    apply iSup_le
    intro t
    apply iSup_le
    intro _
    rw [cellL2Norm_eq_of_class _ _ (hD.2.1 t)]
    exact ENNReal.ofReal_le_ofReal (cellEnergySpaceTrace_norm_le hab z t)
  calc
    _ ≤ ENNReal.ofReal ‖z‖ + ENNReal.ofReal ‖z‖ := add_le_add hv (hg.trans_eq hr)
    _ = ENNReal.ofReal (2 * ‖z‖) := by
      rw [← ENNReal.ofReal_add (norm_nonneg z) (norm_nonneg z)]
      congr 1
      ring

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! The bounded scalar perturbation readout has the literal weak PDE representative. -/

theorem cellBlochPerturbationScalarCLM_ae {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (δ : Fin 2 → ℂ) (q : Lp ℂ ∞ (volume.restrict (Icc a b)))
    (u : ℝ → ComplexCellL2) (slice g : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice g) (z : CellFiniteEnergyCarrier a b)
    (hz : ∀ t : CellCompactTime a b, z.val.1 t = u t.val) :
    cellBlochPerturbationScalarCLM hab C hG V hv hb δ q z =ᵐ[volume.restrict (Icc a b)]
      fun t => cellBlochPerturbationScalar C hG V hv hb δ q t (slice t) := by
  let M := fun k : Fin 2 => ∑ j : Fin 2,
    cellTimeMetricEntryCLM (Icc a b) hG j k
      (cellFiniteEnergyTimeShiftedDerivativeCLM hab (C.θ + δ) j z)
  have hM : ∀ k, M k =ᵐ[volume.restrict (Icc a b)] fun t =>
      ∑ j : Fin 2, cellMetricEntryCLM hG t j k (cellShiftedDerivativeCLM (C.θ + δ) j (slice t)) := by
    intro k
    have hj : ∀ j : Fin 2,
        cellTimeMetricEntryCLM (Icc a b) hG j k
          (cellFiniteEnergyTimeShiftedDerivativeCLM hab (C.θ + δ) j z)
          =ᵐ[volume.restrict (Icc a b)] fun t =>
            cellMetricEntryCLM hG t j k (cellShiftedDerivativeCLM (C.θ + δ) j (slice t)) := by
      intro j
      filter_upwards [cellTimeMetricEntryCLM_ae (Icc a b) hG j k
        (cellFiniteEnergyTimeShiftedDerivativeCLM hab (C.θ + δ) j z),
        cellFiniteEnergyTimeShiftedDerivativeCLM_ae hab (C.θ + δ) j u slice g h z hz]
        with t ht hd
      rw [ht, hd]
    simpa only [one_smul] using lpFiniteLinearCombination_ae (fun _ => (1 : ℂ))
      (fun j => cellTimeMetricEntryCLM (Icc a b) hG j k
        (cellFiniteEnergyTimeShiftedDerivativeCLM hab (C.θ + δ) j z))
      (fun j t => cellMetricEntryCLM hG t j k (cellShiftedDerivativeCLM (C.θ + δ) j (slice t))) hj
  let D := fun j : Fin 2 => cellTimeDriftEntryCLM (Icc a b) C V hv hb j
    (cellFiniteEnergyTimeValueCLM hab z)
  have hD : ∀ j, D j =ᵐ[volume.restrict (Icc a b)] fun t =>
      cellDriftEntryCLM C V hv hb t j (torusHkValueCLM (slice t)) := by
    intro j
    filter_upwards [cellTimeDriftEntryCLM_ae (Icc a b) C V hv hb j
      (cellFiniteEnergyTimeValueCLM hab z),
      cellFiniteEnergyTimeValueCLM_ae hab u slice g h z hz, h.agrees] with t ht hu ha
    rw [ht, hu, ha]
  have hm := lpFiniteLinearCombination_ae (fun k => Complex.I * δ k) M _ hM
  have hd := lpFiniteLinearCombination_ae (fun j => Complex.I * δ j) D _ hD
  have hq := lpTopScalarMultiplier_ae (volume.restrict (Icc a b)) q
    (cellFiniteEnergyTimeValueCLM hab z)
  have hu := cellFiniteEnergyTimeValueCLM_ae hab u slice g h z hz
  let A := ∑ k : Fin 2, (Complex.I * δ k) • M k
  let B := ∑ j : Fin 2, (Complex.I * δ j) • D j
  let Q := lpTopScalarMultiplier (volume.restrict (Icc a b)) q (cellFiniteEnergyTimeValueCLM hab z)
  have hs := Lp.coeFn_sub A B
  have ha := Lp.coeFn_add (A - B) Q
  simp only [cellBlochPerturbationScalarCLM, sum_apply, smul_apply, sub_apply, add_apply,
    ContinuousLinearMap.comp_apply]
  change (A - B + Q) =ᵐ[volume.restrict (Icc a b)] _
  filter_upwards [hm, hd, hq, hu, h.agrees, hs, ha] with t hm' hd' hq' hu' hag hs' ha'
  rw [ha']
  simp only [Pi.add_apply]
  rw [hs']
  simp only [Pi.sub_apply]
  rw [hm', hd', hq', hu', hag]
  have he : (∑ j : Fin 2, (Complex.I * δ j) •
      cellDriftEntryCLM C V hv hb t j (torusHkValueCLM (slice t))) =
      ∑ j : Fin 2, cellDriftEntryCLM C V hv hb t j
        ((Complex.I * δ j) • torusHkValueCLM (slice t)) := by
    apply Finset.sum_congr rfl
    intro j _
    simpa only [cellScalarCLM_smul] using
      (cellDriftEntryCLM_scalar C V hv hb t j (Complex.I * δ j)
        (torusHkValueCLM (slice t))).symm
  simp only [cellBlochPerturbationScalar, cellScalarCLM_smul]
  rw [he]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.CycleEvolution

/-! Carrier norm convergence implies convergence in the literal raw energy seminorm. -/

theorem cellEnergySpaceRaw_energyNorm_tendsto {P : Type*} {a b : ℝ} (hab : a ≤ b)
    (l : Filter P) (z : P → CellEnergySpace a b) (D : P → ℝ → RawJet2 1 ℂ)
    (hD : ∀ p, IsCellEnergySpaceRawRepresentative hab (z p) (D p))
    (hz : Tendsto z l (𝓝 0)) :
    Tendsto (fun p => cellEnergyNorm (Icc a b) (D p)) l (𝓝 0) := by
  have hn : Tendsto (fun p => ENNReal.ofReal (2 * ‖z p‖)) l (𝓝 0) := by
    have hr : Tendsto (fun p => (2 : ℝ) * ‖z p‖) l (𝓝 0) := by
      simpa only [norm_zero, mul_zero] using (tendsto_const_nhds (x := (2 : ℝ))).mul hz.norm
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hr
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hn
    (fun _ => bot_le) (fun p => cellEnergySpaceRaw_energyNorm_le hab (z p) (D p) (hD p))

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Filter Homogenization AVRegularity.Sobolev
open scoped Topology
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.CycleEvolution

/-! Identification of the Galerkin moment primitives with the weak state. -/

variable {a b : ℝ} {hab : a ≤ b} {C : CellCoefficients} {hG : IsCellMetric C.G} {V : ℝ}
  {hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2)}
  {hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2}
  {src : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
  {initial : ComplexCellL2}

/-- The weak temporal state satisfies the actual integrated cell equation a.e. for each test. -/
theorem CellGalerkinLimitData.moment_ae
    (D : CellGalerkinLimitData a b hab C hG V hv hb src F initial)
    (k : ℝ) (hκ : Measurable C.κ) (hκb : ∀ r, ‖C.κ r‖ ≤ k)
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (z : TorusHk 1 ℂ) : ∀ᵐ t ∂volume.restrict (Icc a b),
      inner ℝ (torusHkValueCLM (D.limit t)) (torusHkValueCLM z) =
        inner ℝ initial (torusHkValueCLM z) + ∫ r in a..t,
          cellGeneratorForm C hG V hv hb r (D.limit r) z +
            cellRawSourceFunctional C.θ src F r z := by
  obtain ⟨E, hE, hbound⟩ := D.uniform_trace_bound k hκb hsrc hF
  let L := (innerSL ℝ (torusHkValueCLM z)).comp (torusHkValueCLM (E := ℂ) (K := 1))
  let p := fun t => inner ℝ initial (torusHkValueCLM z) + ∫ r in a..t,
    cellGeneratorForm C hG V hv hb r (D.limit r) z + cellRawSourceFunctional C.θ src F r z
  have he (n : ℕ) (t : ℝ) : L (D.state (D.subsequence n) t) =
      inner ℝ (cellGalerkinValue (D.subsequence n)
        (extendCurve hab (D.curve (D.subsequence n)) t)) (torusHkValueCLM z) := by
    change inner ℝ (torusHkValueCLM z)
      (cellGalerkinValue (D.subsequence n) (extendCurve hab (D.curve (D.subsequence n)) t)) = _
    exact real_inner_comm _ _
  have hsq : ∀ n, ∀ᵐ t ∂volume.restrict (Icc a b),
      (L (D.state (D.subsequence n) t)) ^ 2 ≤ E * ‖torusHkValueCLM z‖ ^ 2 := by
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [he]
    have hi := abs_real_inner_le_norm
      (cellGalerkinValue (D.subsequence n) (extendCurve hab (D.curve (D.subsequence n)) t))
      (torusHkValueCLM z)
    calc
      _ ≤ (‖cellGalerkinValue (D.subsequence n)
          (extendCurve hab (D.curve (D.subsequence n)) t)‖ * ‖torusHkValueCLM z‖) ^ 2 :=
        by
          have hh := (sq_le_sq₀ (abs_nonneg _)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hi
          simpa only [sq_abs] using hh
      _ ≤ E * ‖torusHkValueCLM z‖ ^ 2 := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right (hbound _ t ht) (sq_nonneg _)
  have hl : ∀ᵐ t ∂volume.restrict (Icc a b),
      Tendsto (fun n => L (D.state (D.subsequence n) t)) atTop (𝓝 (p t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simpa only [he, p] using D.moment_primitive_tendsto k hκ hκb hsrc hF z t ht
  have hm := cellWeak_scalar_moment_identification
    (fun n => D.state (D.subsequence n)) (fun n => D.stateLp (D.subsequence n))
    D.limit D.weak L p (E * ‖torusHkValueCLM z‖ ^ 2)
    (mul_nonneg hE (sq_nonneg _)) hsq hl
  filter_upwards [hm] with t ht
  exact (real_inner_comm _ _).trans ht

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.CycleEvolution

/-! Actual weak time data and continuous Hilbert trace of the Galerkin limit. -/

variable {a b : ℝ} {hab : a ≤ b} {C : CellCoefficients} {hG : IsCellMetric C.G} {V : ℝ}
  {hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2)}
  {hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2}
  {src : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
  {initial : ComplexCellL2}

/-- The actual dual derivative of the weak Galerkin state. -/
def CellGalerkinLimitData.dualState
    (D : CellGalerkinLimitData a b hab C hG V hv hb src F initial) (t : ℝ) : TorusHk 1 ℂ :=
  cellDualDerivative C hG V hv hb t (D.limit t) (cellSourceSlice src t)
    (fun j => cellSourceSlice (fun r x => F r x j) t)

/-- All actual weak time premises follow from the Galerkin construction and L² data. -/
theorem CellGalerkinLimitData.weakTimeData
    (D : CellGalerkinLimitData a b hab C hG V hv hb src F initial)
    (k : ℝ) (hκ : Measurable C.κ) (hκb : ∀ r, ‖C.κ r‖ ≤ k)
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube))) :
    CellWeakTimeData a b D.limit D.dualState initial := by
  have hS := cellSourceSlice_memLp (Icc a b) src hsrc
  have hQ (j : Fin 2) := cellSourceSlice_memLp (Icc a b) (fun r x => F r x j)
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).comp_memLp' hF)
  refine ⟨Lp.memLp D.limit, ?_, ?_⟩
  · exact cellDualDerivative_memLp C hG V k hv hb hκ hκb D.limit (Lp.memLp D.limit)
      _ hS _ hQ
  · intro z
    filter_upwards [D.moment_ae k hκ hκb hsrc hF z] with t ht
    convert ht using 1
    congr 1
    apply intervalIntegral.integral_congr
    intro r _
    exact cellDualDerivative_pairing C hG V hv hb r (D.limit r) z _ _

/-- The actual Galerkin limit has a continuous L² trace, its prescribed initial value,
and the integrated weak equation on every closed subinterval. -/
theorem CellGalerkinLimitData.exists_continuous_trace
    (D : CellGalerkinLimitData a b hab C hG V hv hb src F initial) (hab' : a < b)
    (k : ℝ) (hκ : Measurable C.κ) (hκb : ∀ r, ‖C.κ r‖ ≤ k)
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube))) :
    ∃ U : C(Icc a b, ComplexCellL2),
      CellWeakHilbertCurve a b (extendCurve hab U) D.limit D.dualState ∧
        extendCurve hab U a = initial := by
  exact (D.weakTimeData k hκ hκb hsrc hF).exists_hilbert_curve hab'

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Addition of public cell solutions, including the literal continuous trace and local energy clauses. -/

/-- The public cell equation is linear jointly in the state and forcing. -/
theorem cellSolution_add {I : Set ℝ} {C : CellCoefficients}
    {src src' : ℝ → Vec 2 → ℂ}
    {F F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    {D E : ℝ → RawJet2 1 ℂ}
    (hD : IsCellSolution I C src F D) (hE : IsCellSolution I C src' F' E) :
    IsCellSolution I C (src + src') (F + F') (D + E) := by
  refine ⟨hD.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hD.2.1, hE.2.1] with t hDt hEt
    exact cellPeriodicWeakJet_add hDt hEt
  · intro t ht
    refine ⟨(hD.2.2.1 t ht).1.add (hE.2.2.1 t ht).1, ?_⟩
    intro n x
    change cellValue D t (x + AVenhance.latticeShift n) +
      cellValue E t (x + AVenhance.latticeShift n) = _
    rw [(hD.2.2.1 t ht).2 n x, (hE.2.2.1 t ht).2 n x]
    rfl
  · intro a
    exact (hD.2.2.2.1 a).add (hE.2.2.2.1 a)
  · apply cellClass_trace_continuity I (D + E) (fun t => cellRawTrace D t + cellRawTrace E t)
    · exact (cellRawTrace_continuous I D (fun t ht => (hD.2.2.1 t ht).1)
        hD.2.2.2.2.1).add
        (cellRawTrace_continuous I E (fun t ht => (hE.2.2.1 t ht).1) hE.2.2.2.2.1)
    · intro t ht
      exact (Lp.coeFn_add _ _).trans
        ((cellRawTrace_ae D t (hD.2.2.1 t ht).1).add (cellRawTrace_ae E t (hE.2.2.1 t ht).1))
  · intro a ha b hb
    by_cases hab : a ≤ b
    · have hsub : Icc a b ⊆ I := fun _ ht => hD.1.out ha hb ht
      have hDa := IsCellSolution.gradient_memLp hab
        (cellSolution_restrict hsub ordConnected_Icc hD)
      have hEa := IsCellSolution.gradient_memLp hab
        (cellSolution_restrict hsub ordConnected_Icc hE)
      exact cellProduct_cellNormSq_finite (Icc a b)
        (fun t => cellGradient ((D + E) t)) (hDa.add hEa)
    · simp only [Icc_eq_empty_of_lt (lt_of_not_ge hab), Measure.restrict_empty,
        lintegral_zero_measure]
      exact ENNReal.zero_lt_top
  · intro s hs t ht hst ψ
    exact cellWeakIdentity_add C s t _ _ _ _ _ _ _ _ _ _ src src' F F'
      (hD.2.2.2.2.2.2 s hs t ht hst ψ) (hE.2.2.2.2.2.2 s hs t ht hst ψ)

/-! Real scaling of public cell solutions, including the literal continuous trace and local energy clauses. -/

/-- The public cell equation commutes with real scaling. -/
theorem cellSolution_smul {I : Set ℝ} {C : CellCoefficients}
    {src : ℝ → Vec 2 → ℂ}
    {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    {D : ℝ → RawJet2 1 ℂ}
    (hD : IsCellSolution I C src F D) (r : ℝ) :
    IsCellSolution I C (r • src) (r • F) (r • D) := by
  refine ⟨hD.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hD.2.1] with t hDt
    exact cellPeriodicWeakJet_smul hDt r
  · intro t ht
    refine ⟨(hD.2.2.1 t ht).1.const_smul r, ?_⟩
    intro n x
    change r • cellValue D t (x + AVenhance.latticeShift n) = _
    rw [(hD.2.2.1 t ht).2 n x]
    rfl
  · intro a
    exact (hD.2.2.2.1 a).const_smul r
  · apply cellClass_trace_continuity I (r • D) (fun t => r • cellRawTrace D t)
    · exact (cellRawTrace_continuous I D (fun t ht => (hD.2.2.1 t ht).1)
        hD.2.2.2.2.1).const_smul r
    · intro t ht
      exact (Lp.coeFn_smul r _).trans ((cellRawTrace_ae D t (hD.2.2.1 t ht).1).const_smul r)
  · intro a ha b hb
    by_cases hab : a ≤ b
    · have hsub : Icc a b ⊆ I := fun _ ht => hD.1.out ha hb ht
      have hDa := IsCellSolution.gradient_memLp hab
        (cellSolution_restrict hsub ordConnected_Icc hD)
      exact cellProduct_cellNormSq_finite (Icc a b)
        (fun t => cellGradient ((r • D) t)) (hDa.const_smul r)
    · simp only [Icc_eq_empty_of_lt (lt_of_not_ge hab), Measure.restrict_empty,
        lintegral_zero_measure]
      exact ENNReal.zero_lt_top
  · intro s hs t ht hst ψ
    exact cellWeakIdentity_smul C s t r _ _ _ _ _ _ src F
      (hD.2.2.2.2.2.2 s hs t ht hst ψ)

/-! Conjugation and time reflection turn the opposite-frequency reversed evolution into the genuine backward adjoint. -/

theorem CellWeakHilbertCurve.reflected_adjoint {a b : ℝ}
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Fin 2 → ℂ)
    {u : ℝ → ComplexCellL2} {slice : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve (-b) (-a) u slice (fun t =>
      cellDualDerivative ⟨fun s x => G (-s) x, fun s x => -v (-s) x,
        fun j => -θ j, 0⟩ (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1
        (fun s x => by simpa only [Pi.neg_apply, neg_sq] using hb (-s) x) t (slice t) 0 0)) :
    CellWeakHilbertCurve a b
      (fun t => cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u (-t)))
      (fun t => cellH1Conj (slice (-t)))
      (fun t => -cellDualDerivative (cellAdjointCoefficients ⟨G, v, θ, 0⟩) hG V
        (cellDrift_neg hv).1 (cellDrift_neg_bound hb) t (cellH1Conj (slice (-t))) 0 0) := by
  let Cr : CellCoefficients := ⟨fun s x => G (-s) x, fun s x => -v (-s) x,
    fun j => -θ j, 0⟩
  have hr (s : ℝ) (x : Vec 2) : ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2 := by
    simpa only [Pi.neg_apply, neg_sq] using hb (-s) x
  have hc := h.conjugate_homogeneous Cr (cellMetric_timeReverse hG) V
    (cellDrift_timeReverse hv).1 hr
  have ht := hc.reverse_homogeneous (cellConjugateCoefficients Cr)
    (cellMetric_timeReverse hG) V (cellDrift_timeReverse hv).1 hr
  simpa only [Cr, cellReverseTimeCoefficients, cellConjugateCoefficients,
    cellAdjointCoefficients, neg_neg, star_neg, Pi.zero_apply, star_zero] using ht

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVenhance.Infra.ODE
namespace AVRegularity.CycleEvolution

/-! Actual Hilbert weak cell solutions for arbitrary L² data, including singleton intervals. -/

/-- The measurable coefficient and source premises construct an actual Hilbert weak solution. -/
theorem cellActual_exists_Hilbert {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hvb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (hκ : Measurable C.κ) (hκb : ∀ t, ‖C.κ t‖ ≤ k)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrcm : Measurable (Function.uncurry src)) (hFm : Measurable (Function.uncurry F))
    (hsrc : ∫⁻ t in Icc a b, cellL2Norm (src t) ^ 2 < ⊤)
    (hF : ∫⁻ t in Icc a b, cellL2Norm (F t) ^ 2 < ⊤)
    (initial : ComplexCellL2) :
    ∃ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ),
      CellWeakHilbertCurve a b u slice (fun r => cellDualDerivative C hG V hv hvb r
        (slice r) (cellSourceSlice src r) (fun j => cellSourceSlice (fun t x => F t x j) r)) ∧
      u a = initial := by
  rcases lt_or_eq_of_le hab with hlt | heq
  · obtain ⟨D⟩ := cellGalerkin_actual_limit_data hab C hG V k hv hvb hκ hκb
      src F hsrcm hFm hsrc hF initial
    obtain ⟨U, hU, hi⟩ := D.exists_continuous_trace hlt k hκ hκb
      (cellSource_memLp_product (Icc a b) src hsrcm hsrc)
      (cellSource_memLp_product (Icc a b) F hFm hF)
    exact ⟨extendCurve hab U, D.limit, hU, hi⟩
  · subst b
    exact ⟨fun _ => initial, fun _ => 0, cellSingleton_weak_curve a initial _, rfl⟩

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Complex scaling of public cell solutions, including the literal continuous trace and local energy clauses. -/

/-- The public cell equation commutes with complex scaling. -/
theorem cellSolution_complex_smul {I : Set ℝ} {C : CellCoefficients}
    {src : ℝ → Vec 2 → ℂ}
    {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    {D : ℝ → RawJet2 1 ℂ}
    (hD : IsCellSolution I C src F D) (r : ℂ) :
    IsCellSolution I C (r • src) (r • F) (r • D) := by
  refine ⟨hD.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hD.2.1] with t hDt
    exact cellPeriodicWeakJet_complex_smul hDt r
  · intro t ht
    refine ⟨(hD.2.2.1 t ht).1.const_smul r, ?_⟩
    intro n x
    change r • cellValue D t (x + AVenhance.latticeShift n) = _
    rw [(hD.2.2.1 t ht).2 n x]
    rfl
  · intro a
    exact (hD.2.2.2.1 a).const_smul r
  · apply cellClass_trace_continuity I (r • D) (fun t => r • cellRawTrace D t)
    · exact (cellRawTrace_continuous I D (fun t ht => (hD.2.2.1 t ht).1)
        hD.2.2.2.2.1).const_smul r
    · intro t ht
      exact (Lp.coeFn_smul r _).trans ((cellRawTrace_ae D t (hD.2.2.1 t ht).1).const_smul r)
  · intro a ha b hb
    by_cases hab : a ≤ b
    · have hsub : Icc a b ⊆ I := fun _ ht => hD.1.out ha hb ht
      have hDa := IsCellSolution.gradient_memLp hab
        (cellSolution_restrict hsub ordConnected_Icc hD)
      exact cellProduct_cellNormSq_finite (Icc a b)
        (fun t => cellGradient ((r • D) t)) (hDa.const_smul r)
    · simp only [Icc_eq_empty_of_lt (lt_of_not_ge hab), Measure.restrict_empty,
        lintegral_zero_measure]
      exact ENNReal.zero_lt_top
  · intro s hs t ht hst ψ
    exact cellWeakIdentity_complex_smul C s t r _ _ _ _ _ _ src F
      (hD.2.2.2.2.2.2 s hs t ht hst ψ)

/-! Raw fibre norms are controlled by the trace and two covariant L2 readouts. -/

theorem cellEnergySpaceRaw_fibreXNorm_le_readouts {a b : ℝ} (hab : a ≤ b)
    (z : CellEnergySpace a b) (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellEnergySpaceRawRepresentative hab z D) (θ : Fin 2 → ℂ) :
    fibreXNorm θ (Icc a b) D ≤ ENNReal.ofReal
      (‖cellEnergySpaceTraceCLM a b z‖ +
        ‖cellEnergySpaceShiftedDerivativeCLM hab θ 0 z‖ +
        ‖cellEnergySpaceShiftedDerivativeCLM hab θ 1 z‖) := by
  rw [cellEnergySpaceRaw_fibreXNorm hab z D hD θ,
    cellEnergySpaceShiftedDerivative_sum_integral hab z θ]
  have ht : (⨆ t ∈ Icc a b, ENNReal.ofReal ‖cellEnergySpaceTrace hab z t‖) ≤
      ENNReal.ofReal ‖cellEnergySpaceTraceCLM a b z‖ := by
    apply iSup_le
    intro t
    apply iSup_le
    intro _
    exact ENNReal.ofReal_le_ofReal
      ((cellEnergySpaceTraceCLM a b z).norm_coe_le_norm (projIcc a b hab t))
  have hs : Real.sqrt (∑ j, ‖cellFiniteEnergyTimeShiftedDerivativeCLM hab θ j
      (show CellFiniteEnergyCarrier a b from z)‖ ^ 2) ≤
      ‖cellEnergySpaceShiftedDerivativeCLM hab θ 0 z‖ +
      ‖cellEnergySpaceShiftedDerivativeCLM hab θ 1 z‖ := by
    simp only [Fin.sum_univ_two, ← cellEnergySpaceShiftedDerivativeCLM_apply]
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · nlinarith [norm_nonneg (cellEnergySpaceShiftedDerivativeCLM hab θ 0 z),
        norm_nonneg (cellEnergySpaceShiftedDerivativeCLM hab θ 1 z)]
  calc
    _ ≤ ENNReal.ofReal ‖cellEnergySpaceTraceCLM a b z‖ +
        ENNReal.ofReal (‖cellEnergySpaceShiftedDerivativeCLM hab θ 0 z‖ +
          ‖cellEnergySpaceShiftedDerivativeCLM hab θ 1 z‖) :=
      add_le_add ht (ENNReal.ofReal_le_ofReal hs)
    _ = _ := by rw [← ENNReal.ofReal_add (norm_nonneg _) (by positivity), add_assoc]

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The quiet graph equation retains a sharp mean-zero dissipation gap. -/

theorem cellGraphFlux_meanZero_dissipation (η : ℝ) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : 1024 * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2 / 16)
    (t : ℝ) (u : TorusHk 1 ℂ) (hm : cellMean (torusHkValueCLM u) = 0) :
    inner ℝ (cellDualDerivative ⟨fun t _ => G t, v, 0, 0⟩ hG V hv.1 hb t u 0
      (cellNormalizedGraphFluxClass G (fun j => (Real.sqrt η : ℂ) * ξ j) t u)) u ≤
      -(3 * Real.pi ^ 2) * ‖torusHkValueCLM u‖ ^ 2 := by
  let F := cellNormalizedGraphFluxClass G (fun j => (Real.sqrt η : ℂ) * ξ j) t u
  have hf := hilbertSmallFlux_young F (fun j => cellDerivativeCLM j u)
    (8 * fibreNorm ξ) ‖torusHkValueCLM u‖
    (fun j => cellNormalizedGraphFluxClass_norm_le η hη G hG ξ t u j)
  have he := cellMetricEnergy_near_identity_coercive hG hg t u
  have hp := cellMeanZero_gradient_gap u hm
  have hd : 0 ≤ ∑ j, ‖cellDerivativeCLM j u‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hc := mul_le_mul_of_nonneg_right hgsmall hd
  have hfreq := mul_le_mul_of_nonneg_right hξ (sq_nonneg ‖torusHkValueCLM u‖)
  rw [cellDualDerivative_pairing, cellUnshiftedGenerator_drift_neutral hG hv,
    cellSourceFunctional_unshifted, inner_zero_left, zero_sub]
  change -cellMetricEnergy hG t u - ∑ j, inner ℝ (F j) (cellDerivativeCLM j u) ≤ _
  nlinarith

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Filter Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Arbitrary public cell solutions satisfy the actual Hilbert fixed-test time equation. -/

/-- The public complex bilinear identity yields every real Hilbert H¹ test increment. -/
theorem cellSolution_Hilbert_increment {a b : ℝ}
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (D : ℝ → RawJet2 1 ℂ) (h : IsCellSolution (Icc a b) C src F D)
    (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (z : TorusHk 1 ℂ) :
    inner ℝ (cellRawTrace D t) (torusHkValueCLM z) -
      inner ℝ (cellRawTrace D s) (torusHkValueCLM z) =
        ∫ r in s..t, inner ℝ (cellRawSolutionDual C hG V hv hb src F D r) z := by
  let ψ := cellHilbertTest z
  let R := fun r => cellLiteralRHS C r (cellValue D r) (cellGradComp (D r))
    (ψ.jet (valueIndex2 1)) (fun j => ψ.jet ⟨⟨1, by decide⟩, fun _ => j⟩) (src r) (F r)
  have hid := h.2.2.2.2.2.2 s hs t ht hst ψ
  change Integrable (fun x => cellValue D t x * ψ.jet (valueIndex2 1) x) _ ∧
    Integrable (fun x => cellValue D s x * ψ.jet (valueIndex2 1) x) _ ∧
    (∀ᵐ r ∂volume.restrict (Ioc s t), Integrable (R r) _) ∧
    Integrable (fun r => ∫ x in AVenhance.unitCube, R r x) (volume.restrict (Ioc s t)) ∧
    (∫ x in AVenhance.unitCube, cellValue D t x * ψ.jet (valueIndex2 1) x) -
      (∫ x in AVenhance.unitCube, cellValue D s x * ψ.jet (valueIndex2 1) x) =
        ∫ r in Ioc s t, ∫ x in AVenhance.unitCube, R r x at hid
  have hsub : Ioc s t ⊆ Icc a b := Ioc_subset_Icc_self.trans (Icc_subset_Icc hs.1 ht.2)
  have hFlux (j : Fin 2) := cellSource_memLp_slices (Icc a b) (fun r x => F r x j)
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).comp_memLp' hF)
  have he : (fun r => ∫ x in AVenhance.unitCube, R r x) =ᵐ[volume.restrict (Ioc s t)]
      fun r => cellDualComplexPair (cellRawSolutionDual C hG V hv hb src F D r) z := by
    have hj := (cellSolution_slice_ae h).filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
    have hS := (cellSource_memLp_slices (Icc a b) src hsrc).filter_mono
      (ae_mono (Measure.restrict_mono hsub le_rfl))
    have hQ := (ae_all_iff.mpr hFlux).filter_mono
      (ae_mono (Measure.restrict_mono hsub le_rfl))
    filter_upwards [hj, hS, hQ] with r hr hsr hfr
    have heq := (cellRawSpatial_equation C hG V hv hb r (cellH1Slice D r) (D r) hr ψ
      (cellSourceSlice src r) (fun j => cellSourceSlice (fun t x => F t x j) r)
      (src r) (F r) (cellSourceSlice_ae src r hsr)
      (fun j => cellSourceSlice_ae (fun t x => F t x j) r (hfr j))).2
    change (∫ x in AVenhance.unitCube, R r x) =
      cellDualComplexPair (cellRawSolutionDual C hG V hv hb src F D r) (cellRawTest ψ) at heq
    rw [show cellRawTest ψ = z from cellHilbertTest_inverse z] at heq
    exact heq
  have hp (r : ℝ) (hr : r ∈ Icc a b) := cellRawTest_pairing_integral ψ (cellRawTrace D r)
    (cellValue D r) (cellRawTrace_ae D r (h.2.2.1 r hr).1)
  have hinc : cellComplexPair (cellRawTrace D t) (torusHkValueCLM z) -
      cellComplexPair (cellRawTrace D s) (torusHkValueCLM z) =
        ∫ r in Ioc s t, ∫ x in AVenhance.unitCube, R r x := by
    have hpt := hp t ht
    have hps := hp s hs
    rw [show cellRawTest ψ = z from cellHilbertTest_inverse z] at hpt hps
    rw [hpt, hps]
    exact hid.2.2.2.2
  have hre := congrArg Complex.re hinc
  simp only [Complex.sub_re, cellComplexPair_re] at hre
  have hmap := Complex.reCLM.integral_comp_comm hid.2.2.2.1
  change (∫ r in Ioc s t, (∫ x in AVenhance.unitCube, R r x).re) =
    (∫ r in Ioc s t, ∫ x in AVenhance.unitCube, R r x).re at hmap
  rw [← hmap] at hre
  rw [intervalIntegral.integral_of_le hst]
  have hreal : (fun r => (∫ x in AVenhance.unitCube, R r x).re) =ᵐ[
      volume.restrict (Ioc s t)] fun r => inner ℝ (cellRawSolutionDual C hG V hv hb src F D r) z :=
    he.mono (fun r hr => (congrArg Complex.re hr).trans (cellDualComplexPair_re _ _))
  exact hre.trans (integral_congr_ae hreal)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! A raw fibre budget controls each of the analytic readouts individually. -/

theorem cellEnergySpaceRaw_trace_budget {a b : ℝ} (hab : a ≤ b)
    (z : CellEnergySpace a b) (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellEnergySpaceRawRepresentative hab z D) (θ : Fin 2 → ℂ)
    (M : ℝ) (hM : 0 ≤ M) (hb : fibreXNorm θ (Icc a b) D ≤ ENNReal.ofReal M) :
    ‖cellEnergySpaceTraceCLM a b z‖ ≤ M := by
  rw [cellEnergySpaceRaw_fibreXNorm hab z D hD θ] at hb
  apply ((cellEnergySpaceTraceCLM a b z).norm_le hM).2
  intro t
  have he : ENNReal.ofReal ‖cellEnergySpaceTrace hab z t.val‖ ≤ ENNReal.ofReal M :=
    (le_iSup_of_le (f := fun s : ℝ => ⨆ (_ : s ∈ Icc a b),
      ENNReal.ofReal ‖cellEnergySpaceTrace hab z s‖) t.val
      (le_iSup_of_le (f := fun _ : t.val ∈ Icc a b =>
        ENNReal.ofReal ‖cellEnergySpaceTrace hab z t.val‖) t.property le_rfl)).trans
      ((le_add_of_nonneg_right (zero_le)).trans hb)
  have hn := (ENNReal.ofReal_le_ofReal_iff hM).mp he
  simpa only [cellEnergySpaceTrace, projIcc_val, cellEnergySpaceTraceCLM_apply] using hn

theorem cellEnergySpaceRaw_shifted_budget {a b : ℝ} (hab : a ≤ b)
    (z : CellEnergySpace a b) (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellEnergySpaceRawRepresentative hab z D) (θ : Fin 2 → ℂ)
    (M : ℝ) (hM : 0 ≤ M) (hb : fibreXNorm θ (Icc a b) D ≤ ENNReal.ofReal M)
    (j : Fin 2) : ‖cellEnergySpaceShiftedDerivativeCLM hab θ j z‖ ≤ M := by
  rw [cellEnergySpaceRaw_fibreXNorm hab z D hD θ,
    cellEnergySpaceShiftedDerivative_sum_integral hab z θ] at hb
  have hs : ENNReal.ofReal (Real.sqrt (∑ k, ‖cellFiniteEnergyTimeShiftedDerivativeCLM hab θ k
      (show CellFiniteEnergyCarrier a b from z)‖ ^ 2)) ≤ ENNReal.ofReal M :=
    (le_add_of_nonneg_left (zero_le)).trans hb
  have hn := (ENNReal.ofReal_le_ofReal_iff hM).mp hs
  have hj : ‖cellFiniteEnergyTimeShiftedDerivativeCLM hab θ j
      (show CellFiniteEnergyCarrier a b from z)‖ ^ 2 ≤
      ∑ k, ‖cellFiniteEnergyTimeShiftedDerivativeCLM hab θ k
        (show CellFiniteEnergyCarrier a b from z)‖ ^ 2 :=
    Finset.single_le_sum (f := fun k : Fin 2 =>
      ‖cellFiniteEnergyTimeShiftedDerivativeCLM hab θ k
        (show CellFiniteEnergyCarrier a b from z)‖ ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ j)
  have hr := Real.sqrt_le_sqrt hj
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] at hr
  exact hr.trans hn

/-! Every public raw cell solution satisfies the actual Hilbert variational equation. -/

/-- The public raw solution predicate discharges every premise of the weak Hilbert energy calculus. -/
theorem cellSolution_to_Hilbert {a b : ℝ} (hab : a ≤ b)
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
    CellWeakHilbertCurve a b (cellRawTrace D) (cellH1Slice D)
      (cellRawSolutionDual C hG V hv hb src F D) :=
  ⟨IsCellSolution.trace_continuous h, cellSolution_slice_memLp hab h,
    cellSolution_dual_memLp hab C hG V k hv hb hκ hκb src F hsrc hF D h,
    cellSolution_trace_agrees h,
    cellSolution_Hilbert_increment C hG V hv hb src F hsrc hF D h⟩

/-! The complete public energy-solution predicate is preserved by genuine conjugation. -/

theorem cellSolution_conjugate {I : Set ℝ} {C : CellCoefficients}
    {src : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    {D : ℝ → RawJet2 1 ℂ} (hD : IsCellSolution I C src F D) :
    IsCellSolution I (cellConjugateCoefficients C) (fun t x => star (src t x))
      (fun t => cellFluxConj (F t)) (fun t => cellRawJetConj (D t)) := by
  refine ⟨hD.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hD.2.1] with t ht
    exact cellPeriodicWeakJet_conjugate ht
  · intro t ht
    refine ⟨Complex.conjCLE.toContinuousLinearMap.comp_memLp' (hD.2.2.1 t ht).1, ?_⟩
    intro n x
    change star (cellValue D t (x + AVenhance.latticeShift n)) = star (cellValue D t x)
    rw [(hD.2.2.1 t ht).2 n x]
  · intro a
    exact Complex.conjCLE.continuous.comp_aestronglyMeasurable (hD.2.2.2.1 a)
  · apply cellClass_trace_continuity I (fun t => cellRawJetConj (D t))
      (fun t => cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellRawTrace D t))
    · exact (cellFiberCLM Complex.conjCLE.toContinuousLinearMap).continuous.comp_continuousOn
        (cellRawTrace_continuous I D (fun t ht => (hD.2.2.1 t ht).1) hD.2.2.2.2.1)
    · intro t ht
      exact (cellFiberConj_ae _).trans ((cellRawTrace_ae D t (hD.2.2.1 t ht).1).fun_comp star)
  · intro a ha b hb
    simpa only [cellL2Norm_gradient_conjugate] using hD.2.2.2.2.2.1 a ha b hb
  · intro s hs t ht hst ψ
    let ψ' : TorusHkFunction 1 ℂ := ⟨cellRawJetConj ψ.jet,
      cellPeriodicWeakJet_conjugate ψ.hasPeriodicWeakJet⟩
    have hw := cellWeakIdentity_conjugate C s t (cellValue D s) (cellValue D t)
      (ψ'.jet (valueIndex2 1)) (fun j => ψ'.jet ⟨⟨1, by decide⟩, fun _ => j⟩)
      (cellValue D) (fun r j => cellGradComp (D r) j) src F
      (hD.2.2.2.2.2.2 s hs t ht hst ψ')
    have hv (r : ℝ) : cellValue (fun t => cellRawJetConj (D t)) r =
        (fun x => star (cellValue D r x)) := rfl
    have hvs : cellValue (fun t => cellRawJetConj (D t)) =
        (fun r x => star (cellValue D r x)) := rfl
    have hgs : (fun r j => cellGradComp (cellRawJetConj (D r)) j) =
        (fun r j x => star (cellGradComp (D r) j x)) := rfl
    rw [hv s, hv t, hvs, hgs]
    simpa only [ψ', cellRawJetConj, cellValue, cellGradComp, star_star] using hw

/-! The actual Fourier Galerkin construction covers bounded almost measurable scalar gauges. -/

theorem cellActual_exists_Hilbert_aePotential {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hvb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (hκ : AEStronglyMeasurable C.κ (volume.restrict (Icc a b)))
    (hκb : ∀ t, ‖C.κ t‖ ≤ k)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrcm : Measurable (Function.uncurry src)) (hFm : Measurable (Function.uncurry F))
    (hsrc : ∫⁻ t in Icc a b, cellL2Norm (src t) ^ 2 < ⊤)
    (hF : ∫⁻ t in Icc a b, cellL2Norm (F t) ^ 2 < ⊤)
    (initial : ComplexCellL2) :
    ∃ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ),
      CellWeakHilbertCurve a b u slice (fun r => cellDualDerivative C hG V hv hvb r
        (slice r) (cellSourceSlice src r) (fun j => cellSourceSlice (fun t x => F t x j) r)) ∧
      u a = initial := by
  have hk : 0 ≤ k := (norm_nonneg (C.κ 0)).trans (hκb 0)
  obtain ⟨κ, hm, he, hb⟩ := complexBounded_measurable_representative C.κ hκ k hk
    (Filter.Eventually.of_forall hκb)
  let C' : CellCoefficients := {C with κ := κ}
  obtain ⟨u, slice, h, hi⟩ := cellActual_exists_Hilbert hab C' hG V k hv hvb hm hb
    src F hsrcm hFm hsrc hF initial
  refine ⟨u, slice, h.dual_congr ?_, hi⟩
  filter_upwards [he] with t ht
  dsimp only [C']
  unfold cellDualDerivative cellGeneratorForm
  rw [ht]
  rfl

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set AVRegularity.Sobolev Filter Topology
namespace AVRegularity.CycleEvolution

/-! Genuine complex Frechet derivatives lift to directional derivatives in the literal raw energy norm. -/

theorem cellEnergySpaceRaw_directional_tendsto {a b : ℝ} (hab : a ≤ b)
    (f : (Fin 2 → ℂ) → CellEnergySpace a b)
    (D : (Fin 2 → ℂ) → ℝ → RawJet2 1 ℂ)
    (f' : (Fin 2 → ℂ) →L[ℂ] CellEnergySpace a b) (x v : Fin 2 → ℂ)
    (E : ℝ → RawJet2 1 ℂ)
    (hD : ∀ y, IsCellEnergySpaceRawRepresentative hab (f y) (D y))
    (hE : IsCellEnergySpaceRawRepresentative hab (f' v) E)
    (hf : HasFDerivAt f f' x) :
    Tendsto (fun h : ℂ => cellEnergyNorm (Icc a b)
      (h⁻¹ • (D (x + h • v) - D x) - E)) (𝓝[≠] 0) (𝓝 0) := by
  apply cellEnergySpaceRaw_energyNorm_tendsto hab (𝓝[≠] (0 : ℂ))
    (fun h => h⁻¹ • (f (x + h • v) - f x) - f' v)
  · intro h
    have hs := cellEnergySpaceRawRepresentative_sub hab _ _ _ _ (hD (x + h • v)) (hD x)
    have hm := cellEnergySpaceRawRepresentative_smul hab h⁻¹ _ _ hs
    exact cellEnergySpaceRawRepresentative_sub hab _ _ _ _ hm hE
  · exact complexDirectional_differenceQuotient_tendsto f f' x v hf

end AVRegularity.CycleEvolution
end
