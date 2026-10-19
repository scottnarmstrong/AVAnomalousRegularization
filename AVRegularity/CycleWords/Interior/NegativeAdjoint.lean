-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.FibreGraphNativeSeries
import AVRegularity.CycleEvolution.CellLimitMoments
public import AVRegularity.CycleWords.Interior.ChartWeightBudget
import AVRegularity.CycleEvolution.CellEnergySpaceRawJetCauchyBound
public import AVRegularity.CycleWords.Assembly.InteriorScalarIngredients
public import AVRegularity.CycleDamping.ConstructedCanonicalGraph
public import AVRegularity.Weighted.DriftCoefficientEmbedding
import AVRegularity.CycleJoint.NativeRawOriginalFamilyTaylorSplitEdges
import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public noncomputable section

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Interior

/-! On a quiet interval the actual constant mode can be subtracted from the Hilbert curve. -/

private theorem pivot_scalar (c : ℂ) (u : ComplexCellL2) :
    cellH1Scalar c (cellPivotDualCLM u) = cellPivotDualCLM (cellScalarCLM c u) := by
  apply ext_inner_right ℝ
  intro z
  have he : cellDualComplexPair (cellH1Scalar c (cellPivotDualCLM u)) z =
      cellDualComplexPair (cellPivotDualCLM (cellScalarCLM c u)) z := by
    rw [cellDualComplexPair_scalar_left, cellPivotDual_complex_pair,
      cellPivotDual_complex_pair, cellComplexPair_scalar_left]
  simpa only [cellDualComplexPair_re] using congrArg Complex.re he

theorem quiet_projection_curve {a b : ℝ} (hab : a ≤ b)
    (η Cw : ℝ) (hη : 0 ≤ η) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hreal : ∀ j, (ξ j).im = 0)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice (fun t => cellDualDerivative
      ⟨fun t _ => G t, v, fun j => (Real.sqrt η : ℂ) * ξ j, 0⟩ hG V hv.1 hb t (slice t) 0 0))
    (hquiet : ∀ t ∈ Icc a b, ∀ x, v t x = 0) :
    CellWeakHilbertCurve a b (fun t => cellQ0CLM (u t))
      (fun t => slice t - cellH1Scalar (cellMean (u t)) cellH1One)
      (fun t => cellDualDerivative
        ⟨fun t _ => G t, v, fun j => (Real.sqrt η : ℂ) * ξ j, 0⟩ hG V hv.1 hb t
        (slice t - cellH1Scalar (cellMean (u t)) cellH1One) 0 0) := by
  let c := fun t => cellMean (u t)
  let r := fun t => -(η : ℂ) * fibreQuad (G t) ξ
  have hc := cellWeak_quiet_mean_strongTime hab η Cw hη hCw G hG hv V hb hw ξ u slice h hquiet
  have hr : MemLp r ⊤ (volume.restrict (Icc a b)) := by
    apply memLp_top_of_bound
      (measurable_const.mul (fibreQuad_time_measurable hG ξ)).aestronglyMeasurable
      (|η| * (8 * fibreNorm ξ ^ 2))
    apply Filter.Eventually.of_forall
    intro t
    change ‖-(η : ℂ) * fibreQuad (G t) ξ‖ ≤ |η| * (8 * fibreNorm ξ ^ 2)
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      (fibreQuad_norm_le_eight (G t) (fun i j => cellMetric_entry_bound hG t 0 i j) ξ)
      (abs_nonneg η)
  have hcm : MemLp c ⊤ (volume.restrict (Icc a b)) := by
    simpa only [c, cellMeanCLM_apply, Function.comp_def] using
      cellMeanCLM.comp_memLp' h.trace_memLp_top
  have hdc : MemLp (fun t => r t * c t) ⊤ (volume.restrict (Icc a b)) := by
    simpa only [ENNReal.top_mul, Pi.mul_def] using hr.mul hcm
  have hk := (cellWeakHilbert_constant a b cellH1One).variable_complex_scalar hab c
    (fun t => r t * c t) hc hdc
  have hsub := h.sub hk
  have htrace (t : ℝ) : u t - cellScalarCLM (c t) (torusHkValueCLM cellH1One) =
      cellQ0CLM (u t) := by
    rw [cellH1One_value, cellScalarCLM_constant_one]
    change u t - cellConstantCLM (cellMean (u t)) = u t - cellConstantCLM (cellMeanCLM (u t))
    rw [cellMeanCLM_apply]
  have hsub' : CellWeakHilbertCurve a b (fun t => cellQ0CLM (u t))
      (fun t => slice t - cellH1Scalar (c t) cellH1One)
      (fun t => cellDualDerivative
        ⟨fun t _ => G t, v, fun j => (Real.sqrt η : ℂ) * ξ j, 0⟩ hG V hv.1 hb t (slice t) 0 0 -
        (cellH1Scalar (c t) 0 + cellPivotDualCLM
          (cellScalarCLM (r t * c t) (torusHkValueCLM cellH1One)))) := by
    simpa only [htrace] using hsub
  apply hsub'.dual_congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [← cellH1ScalarCLM_apply, map_zero, zero_add]
  have hkdual := cellQuiet_constant_mode_dual η Cw hη hCw G hG hv V hb hw ξ hreal t (hquiet t ht)
  have he : cellPivotDualCLM (cellScalarCLM (r t * c t) (torusHkValueCLM cellH1One)) =
      cellH1Scalar (c t) (cellDualDerivative
        ⟨fun t _ => G t, v, fun j => (Real.sqrt η : ℂ) * ξ j, 0⟩ hG V hv.1 hb t cellH1One 0 0) := by
    rw [hkdual, pivot_scalar, cellH1One_value, cellScalarCLM_constant_one]
    congr 1
    rw [← cellScalarCLM_constant_one (r t), ← cellScalarCLM_constant_one (r t * c t)]
    simp only [cellScalarCLM_smul, smul_smul, mul_comm]
  rw [he, cellDualDerivative_sub_homogeneous_scalar]

/-! Full-band smoothing of the constructed fibre evolutions, forward and reversed, in the native
Sobolev carriers: on a step `δ` with `(price·P_e²)δ ≤ 1` and `Jδ ≤ t - s`, the `H^J` norm of the
solution at `t` is at most `(2e²/δ)^{J/2}` times its `L²` norm at `s`. The zeroth order is the real
`L²` contraction, so the price is polynomial in the frequency bound
`R` and no exponential of the frequency enters. -/

theorem interior_forward_native_bound (J : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (V : ℝ) (hb : ∀ t x, ∑ j, ocCellDrift α q Λ ζ m ν y₀ t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hreal : ∀ i, (ξ i).im = 0) (R : ℝ) (hR : 0 ≤ R) (hξ : fibreNorm ξ ≤ R)
    (hθ : ∀ i, ‖(Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i‖ ≤ R)
    {s t : ℝ} (hst : s < t) (δ : ℝ) (hδ : 0 < δ)
    (hshort : (constructedNativeWindowPrice J R 0 Cw *
      peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ 2) * δ ≤ 1)
    (hfit : s + J * δ ≤ t) (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc s t)
      (fibreCoefficients (ν / ocMeanFlux α q Λ ζ m ν) G (ocCellDrift α q Λ ζ m ν y₀) ξ
        (fun _ => 0)) (fun _ _ => 0) (fun _ _ => 0) D) :
    ∃ W : TorusHk J ℂ, torusHkValueCLM W = cellRawTrace D t ∧
      ‖W‖ ^ 2 ≤ (Real.exp 1 * (2 * Real.exp 1) / δ) ^ J * ‖cellRawTrace D s‖ ^ 2 := by
  have hh := cellRawHomogeneous_to_Hilbert hst.le (fun r _ => G r) hG
    (ocCellDrift α q Λ ζ m ν y₀) V hv.1 hb
    (fun j => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ j) D (by
      simpa only [fibreCoefficients, neg_zero,
        show (fun _ : ℝ => (0 : ℂ)) = 0 from rfl] using hD)
  have hP : 0 ≤ (Real.exp 1 * (2 * Real.exp 1) / δ) ^ J :=
    pow_nonneg (div_nonneg (by positivity) hδ.le) _
  apply cellActualWeak_native_of_finite_bound hst _ hG V 0 hv.1 hb measurable_const
    (fun _ => by simp) (cellRawTrace D s) (cellRawTrace D) (cellH1Slice D) hh rfl J t
    ⟨hst.le, le_rfl⟩ _ (mul_nonneg hP (sq_nonneg _))
  intro N y hy hyinit
  have hc := cellGalerkin_real_contraction N hG hv V hb _
    (fibreBloch_real_star _ ξ hreal) hst.le y hy
  have hzero : ∀ r ∈ Icc s t, ‖cellGalerkinValue N (y r)‖ ^ 2 ≤ ‖cellRawTrace D s‖ ^ 2 :=
    fun r hr' => (hc r hr').trans (by
      rw [hyinit]
      exact pow_le_pow_left₀ (norm_nonneg _) (cellGalerkinL2Initial_norm_le N _) 2)
  exact constructedFullGalerkin_native_smoothing J N hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw ξ
    R hR hξ hθ 0 0 (fun _ => by simp) hst.le y hy δ _ hδ (sq_nonneg _) hshort hzero t hfit
    le_rfl

theorem interior_reflected_native_bound (J : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (V : ℝ) (hb : ∀ t x, ∑ j, ocCellDrift α q Λ ζ m ν y₀ t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (hreal : ∀ i, (ξ i).im = 0) (R : ℝ) (hR : 0 ≤ R) (hξ : fibreNorm ξ ≤ R)
    (hθ : ∀ i, ‖(Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ i‖ ≤ R)
    {s t : ℝ} (hst : s < t) (δ : ℝ) (hδ : 0 < δ)
    (hshort : (constructedNativeWindowPrice J R 0 Cw *
      peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ 2) * δ ≤ 1)
    (hfit : s + J * δ ≤ t) (Ψ : ℝ → RawJet2 1 ℂ)
    (hΨ : IsCellSolution (Icc s t)
      (fibreCoefficients (ν / ocMeanFlux α q Λ ζ m ν) (fun τ => G (-τ))
        (fun τ z => -(ocCellDrift α q Λ ζ m ν y₀ (-τ) z)) ξ (fun _ => 0))
      (fun _ _ => 0) (fun _ _ => 0) Ψ) :
    ∃ W : TorusHk J ℂ, torusHkValueCLM W = cellRawTrace Ψ t ∧
      ‖W‖ ^ 2 ≤ (Real.exp 1 * (2 * Real.exp 1) / δ) ^ J * ‖cellRawTrace Ψ s‖ ^ 2 := by
  have hGr := cellMetric_timeReverse hG
  have hvr := cellDrift_timeReverse hv
  have hbr : ∀ r x, ∑ i, (fun τ z => -(ocCellDrift α q Λ ζ m ν y₀ (-τ) z)) r x i ^ 2 ≤ V ^ 2 :=
    fun r x => by simpa only [Pi.neg_apply, neg_sq] using hb (-r) x
  have hh := cellRawHomogeneous_to_Hilbert hst.le (fun r _ => G (-r)) hGr
    (fun τ z => -(ocCellDrift α q Λ ζ m ν y₀ (-τ) z)) V hvr.1 hbr
    (fun j => (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * ξ j) Ψ (by
      simpa only [fibreCoefficients, neg_zero,
        show (fun _ : ℝ => (0 : ℂ)) = 0 from rfl] using hΨ)
  have hP : 0 ≤ (Real.exp 1 * (2 * Real.exp 1) / δ) ^ J :=
    pow_nonneg (div_nonneg (by positivity) hδ.le) _
  apply cellActualWeak_native_of_finite_bound hst _ hGr V 0 hvr.1 hbr measurable_const
    (fun _ => by simp) (cellRawTrace Ψ s) (cellRawTrace Ψ) (cellH1Slice Ψ) hh rfl J t
    ⟨hst.le, le_rfl⟩ _ (mul_nonneg hP (sq_nonneg _))
  intro N y hy hyinit
  have hc := cellGalerkin_real_contraction N hGr hvr V hbr _
    (fibreBloch_real_star _ ξ hreal) hst.le y hy
  have hzero : ∀ r ∈ Icc s t, ‖cellGalerkinValue N (y r)‖ ^ 2 ≤ ‖cellRawTrace Ψ s‖ ^ 2 :=
    fun r hr' => (hc r hr').trans (by
      rw [hyinit]
      exact pow_le_pow_left₀ (norm_nonneg _) (cellGalerkinL2Initial_norm_le N _) 2)
  exact constructedReflectedGalerkin_native_smoothing J N hΛ hζ hν hr y₀ hv V hb G hG Cw hCw
    hw ξ R hR hξ hθ 0 0 (fun _ => by simp) hst.le y hy δ _ hδ (sq_nonneg _) hshort hzero t hfit
    le_rfl

end AVRegularity.CycleWords.Interior
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleWords.Interior

/-! Uniform jets and a bounded periodic stream for every interior band of the construction. -/

theorem interiorDriftScale : Assembly.InteriorDriftScaleStatement := by
  intro α s q hα₀ hα₁ hs₀ hs₁ hq ζ hζ
  obtain ⟨L, hL, hrel⟩ := CycleDamping.bandChain_relaxation_large
    hα₀ hα₁ hs₀ hs₁ hq hζ 6 (by norm_num)
  refine ⟨L, ?_⟩
  intro Λ hΛ
  have hΛ1 : 1 ≤ Λ := by omega
  refine ⟨Real.sqrt (2 / ((1 - Real.exp (-2)) / 96)), constructedSpatialJetPrice, ?_⟩
  intro M κ hκ m hm hmM ν B hνeq hBeq y₀
  have hν : 0 < ν := hνeq ▸ CycleReference.bandChain_pos hΛ1 hζ hκ hmM
  have hB : B = ocMeanFlux α q Λ ζ m ν := by
    rw [← hBeq, hκ.2 m (by omega) hmM, hνeq]
  have hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m :=
    hνeq ▸ hrel Λ hΛ M κ hκ m hm hmM
  refine ⟨?_, cellStream α q Λ ζ m ν y₀, cellStream_smooth hΛ1 hζ ν y₀,
    fun t => cellStream_periodic hΛ1 ν t y₀,
    fun t z => cellStream_velocity hΛ1 hζ ν t y₀ z, ?_⟩
  · intro j t z
    rw [hB]
    exact constructed_normalized_spatial_jet_bound hΛ1 hζ hν hr y₀ t j z
  · intro t z
    rw [hB]
    exact cellStream_amplitude hΛ1 hζ hν hr y₀ z t

end AVRegularity.CycleWords.Interior
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleWords.Interior

/-! The sharp shifted Fourier gap gives uniform decay of the mean-free quiet trace. -/

theorem quiet_meanFree_decay {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (θ : Vec 2) (hθ : ∀ j, |θ j| ≤ Real.pi)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice (fun t => cellDualDerivative
      ⟨G, v, fun j => (θ j : ℂ), 0⟩ hG V hv.1 hb t (slice t) 0 0))
    (hm : ∀ t ∈ Icc a b, cellMean (u t) = 0) :
    ‖u b‖ ≤ Real.exp (-(Real.pi ^ 2 / 2) * (b - a)) * ‖u a‖ := by
  have he := (h.energy_strongTime hab).scalar_decay hab (Real.pi ^ 2) (by
    filter_upwards [h.agrees, ae_restrict_mem measurableSet_Icc] with t ht hti
    have hmean := hm t hti
    rw [ht] at hmean
    have hq : cellQ0CLM (torusHkValueCLM (slice t)) = torusHkValueCLM (slice t) := by
      change _ - cellConstantCLM (cellMeanCLM (torusHkValueCLM (slice t))) = _
      rw [cellMeanCLM_apply, hmean, map_zero, sub_zero]
      rfl
    have hgap := cellH1_meanFree_shifted_sharp_gap θ hθ (slice t)
    rw [hq] at hgap
    have hco := cellMetricVectorEnergy_coercive hG t
      (fun j => cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j (slice t))
    rw [← cellDualComplexPair_re, cellDualComplexPair_actual]
    have hs : cellComplexSource (fun j => (θ j : ℂ)) 0 0 (slice t) = 0 := by
      exact cellComplexSource_zero _ _
    rw [hs, add_zero, cellComplexGenerator_real_diagonal hG hv V hb _
      (fun j => Complex.conj_ofReal (θ j)), ht]
    linarith only [hgap, hco])
  apply scalar_sharp_norm_decay (norm_nonneg _) (norm_nonneg _)
  simpa only [show 2 * (Real.pi ^ 2 / 2) = Real.pi ^ 2 by ring] using he b ⟨hab, le_rfl⟩

theorem cellQuietGap : Assembly.CellQuietGapStatement := by
  intro η G v hη hG hv ξ hξ a b hab hquiet D hD
  obtain ⟨V, hb⟩ := hv.2.1
  let Cw := Real.sqrt η * |V|
  have hCw : 0 ≤ Cw := mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  have hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw := by
    intro t x
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    exact (Real.sqrt_le_sqrt (hb t x)).trans_eq (Real.sqrt_sq_eq_abs V)
  have hh := cellRawHomogeneous_to_Hilbert hab (fun t _ => G t) hG v V hv.1 hb
    (fun j => (Real.sqrt η : ℂ) * ξ j) D (by
      simpa only [fibreCoefficients, neg_zero,
        show (fun _ : ℝ => (0 : ℂ)) = 0 from rfl] using hD)
  have hq := quiet_projection_curve hab η Cw hη.le hCw G hG hv V hb hw ξ
    (fun j => (hξ j).1) (cellRawTrace D) (cellH1Slice D) hh hquiet
  let θ : Vec 2 := fun j => Real.sqrt η * (ξ j).re
  have hθ : ∀ j, |θ j| ≤ Real.pi := by
    intro j
    dsimp only [θ]
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hj := (le_div_iff₀ (Real.sqrt_pos.mpr hη)).mp (hξ j).2
    simpa only [mul_comm] using hj
  have hshift : (fun j => (Real.sqrt η : ℂ) * ξ j) = (fun j => (θ j : ℂ)) := by
    funext j
    apply Complex.ext <;> simp only [θ, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, (hξ j).1, mul_zero, zero_mul, sub_zero, add_zero]
  rw [hshift] at hq
  have he := quiet_meanFree_decay hab (fun t _ => G t) hG hv V hb θ hθ
    (fun t => cellQ0CLM (cellRawTrace D t))
    (fun t => cellH1Slice D t - cellH1Scalar (cellMean (cellRawTrace D t)) cellH1One)
    hq (fun t _ => cellQ0CLM_mean_zero _)
  have hnorm (t : ℝ) (ht : t ∈ Icc a b) :
      cellL2Norm (cellQ0 (cellValue D t)) = ENNReal.ofReal ‖cellQ0CLM (cellRawTrace D t)‖ := by
    apply cellL2Norm_eq_of_class
    exact (cellQ0CLM_ae _).trans (cellQ0_congr_ae _ _
      (cellRawTrace_ae D t (hD.2.2.1 t ht).1))
  rw [hnorm b ⟨hab, le_rfl⟩, hnorm a ⟨le_rfl, hab⟩,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact ENNReal.ofReal_le_ofReal he

end AVRegularity.CycleWords.Interior
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CycleDamping AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleWords.Interior

/-! **`InteriorHighSmoothingStatement`, an ingredient of `scalar_package_interior`: full-band high
smoothing.**

The forward and reversed constructed fibre evolutions at real Brillouin-zone frequencies smooth
from `L²` to every `C^j` with `cellSobolevNorm j ≤ C_j P_e^{2j}(1 + (t-s)^{-j/2})` times the `L²`
norm of the datum (short smoothing on an end of length `min(t-s, c/P_e^Q)` and real `L²`
contraction before it). The step is
`δ = min((t-s)/(j+1), 1/(price·P_e²))`, the frequency bound `R = 5P_e` covers `|ξ|` and `|√ηξ|`
on the band, and the native window price is at most `R²` times its value at `R = 1`. -/

theorem constructedAllOrderPrice_le_sq (K : ℕ) {R : ℝ} (hR : 1 ≤ R) {Cw : ℝ} (hCw : 0 ≤ Cw) :
    constructedAllOrderPrice K R 0 Cw ≤ R ^ 2 * constructedAllOrderPrice K 1 0 Cw := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hRR : R ≤ R ^ 2 := by nlinarith
  have h1R : 1 ≤ R ^ 2 := hR.trans hRR
  cases K with
  | zero =>
    simp only [constructedAllOrderPrice, add_zero, one_pow, mul_one]
    have h2 : Cw * R ≤ Cw * R ^ 2 := mul_le_mul_of_nonneg_left hRR hCw
    nlinarith
  | succ j =>
    have hE0 := constructedEntryUniversalNativePrice_nonneg (j + 1)
    have hc0 : 0 ≤ ‖torusHigherScalarCLM (j + 1) Complex.I‖ := ContinuousLinearMap.opNorm_nonneg _
    simp only [constructedAllOrderPrice, constructedHigherEnergyOrderPrice,
      constructedAdvectionAdjacentPrice, mul_zero, zero_mul, add_zero, one_pow, mul_one, one_mul]
    generalize constructedEntryUniversalNativePrice (j + 1) = E at hE0 ⊢
    generalize ‖torusHigherScalarCLM (j + 1) Complex.I‖ = c at hc0 ⊢
    have hlin : 1 + R * (1 + c) ≤ R * (1 + (1 + c)) := by nlinarith
    have h0 : 0 ≤ 2 * E * (1 + R * (1 + c)) := by positivity
    have hle : 2 * E * (1 + R * (1 + c)) ≤ R * (2 * E * (1 + (1 + c))) := by
      calc 2 * E * (1 + R * (1 + c)) ≤ 2 * E * (R * (1 + (1 + c))) :=
            mul_le_mul_of_nonneg_left hlin (by positivity)
        _ = R * (2 * E * (1 + (1 + c))) := by ring
    have hsq : (2 * E * (1 + R * (1 + c))) ^ 2 ≤ R ^ 2 * (2 * E * (1 + (1 + c))) ^ 2 := by
      calc (2 * E * (1 + R * (1 + c))) ^ 2 ≤ (R * (2 * E * (1 + (1 + c)))) ^ 2 :=
            pow_le_pow_left₀ h0 hle 2
        _ = R ^ 2 * (2 * E * (1 + (1 + c))) ^ 2 := by ring
    nlinarith

theorem constructedNativeWindowPrice_le_sq (J : ℕ) {R : ℝ} (hR : 1 ≤ R) {Cw : ℝ}
    (hCw : 0 ≤ Cw) :
    constructedNativeWindowPrice J R 0 Cw ≤ R ^ 2 * constructedNativeWindowPrice J 1 0 Cw := by
  have h1R : 1 ≤ R ^ 2 := one_le_pow₀ hR
  unfold constructedNativeWindowPrice
  rw [mul_add, mul_one, Finset.mul_sum]
  exact add_le_add h1R (Finset.sum_le_sum fun j _ => constructedAllOrderPrice_le_sq j.val hR hCw)

theorem sqrt_pow_sq (c : ℝ) (hc : 0 ≤ c) (J : ℕ) : (Real.sqrt c ^ J) ^ 2 = c ^ J := by
  rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hc]

/-- The step arithmetic: with `δ = min(x/(J+1), 1/(P·P_e²))` and `P ≤ 25P_e²P₁`, the native
factor `(2e²/δ)^{J/2}` is at most `C P_e^{2J}(1 + x^{-J/2})`. -/
theorem interior_smoothing_step_price (J : ℕ) {Pe x P P1 : ℝ} (hPe : 1 ≤ Pe) (hx : 0 < x)
    (hP : 0 < P) (hP1 : 0 ≤ P1) (hPP1 : P ≤ 25 * Pe ^ 2 * P1) :
    Real.sqrt ((Real.exp 1 * (2 * Real.exp 1) / min (x / (J + 1)) (1 / (P * Pe ^ 2))) ^ J) ≤
      Real.sqrt (2 * Real.exp 1 ^ 2) ^ J *
        (Real.sqrt (J + 1) ^ J + Real.sqrt (25 * P1) ^ J) * Pe ^ (2 * J) *
        (1 + x ^ (-(J : ℝ) / 2)) := by
  have hJ1 : (0 : ℝ) < J + 1 := by positivity
  have hA : 0 < (J + 1 : ℝ) / x := div_pos hJ1 hx
  have hB : 0 < P * Pe ^ 2 := by positivity
  have hm : 0 < min (x / (J + 1)) (1 / (P * Pe ^ 2)) := lt_min (div_pos hx hJ1) (by positivity)
  have hpow : (1 / min (x / (J + 1)) (1 / (P * Pe ^ 2))) ^ J ≤
      ((J + 1) / x) ^ J + (P * Pe ^ 2) ^ J := by
    rcases min_choice (x / (J + 1)) (1 / (P * Pe ^ 2)) with h | h <;> rw [h]
    · rw [one_div_div]
      exact le_add_of_nonneg_right (pow_nonneg hB.le _)
    · rw [one_div_one_div]
      exact le_add_of_nonneg_left (pow_nonneg hA.le _)
  have hsplit : (Real.exp 1 * (2 * Real.exp 1) / min (x / (J + 1)) (1 / (P * Pe ^ 2))) ^ J =
      (2 * Real.exp 1 ^ 2) ^ J * (1 / min (x / (J + 1)) (1 / (P * Pe ^ 2))) ^ J := by
    rw [← mul_pow]
    congr 1
    field_simp
  have he2sq := sqrt_pow_sq (2 * Real.exp 1 ^ 2) (by positivity) J
  have hasq := sqrt_pow_sq ((J : ℝ) + 1) hJ1.le J
  have hbsq := sqrt_pow_sq (25 * P1) (by positivity) J
  have hysq : (x ^ (-(J : ℝ) / 2)) ^ 2 = (1 / x) ^ J := by
    rw [← Real.rpow_natCast (x ^ (-(J : ℝ) / 2)) 2, ← Real.rpow_mul hx.le,
      show -(J : ℝ) / 2 * ((2 : ℕ) : ℝ) = -(J : ℝ) by push_cast; ring, Real.rpow_neg hx.le,
      Real.rpow_natCast, one_div, inv_pow]
  have hQsq : (Pe ^ (2 * J)) ^ 2 = (Pe ^ 2 * Pe ^ 2) ^ J := by
    rw [← pow_add, ← pow_mul, ← pow_mul]
    congr 1
    ring
  have he20 : 0 ≤ Real.sqrt (2 * Real.exp 1 ^ 2) ^ J := pow_nonneg (Real.sqrt_nonneg _) _
  have ha0 : 0 ≤ Real.sqrt ((J : ℝ) + 1) ^ J := pow_nonneg (Real.sqrt_nonneg _) _
  have hb0 : 0 ≤ Real.sqrt (25 * P1) ^ J := pow_nonneg (Real.sqrt_nonneg _) _
  have hy0 : 0 ≤ x ^ (-(J : ℝ) / 2) := Real.rpow_nonneg hx.le _
  have hQ1 : 1 ≤ Pe ^ (2 * J) := one_le_pow₀ hPe
  generalize Real.sqrt (2 * Real.exp 1 ^ 2) ^ J = e2 at he2sq he20 ⊢
  generalize Real.sqrt ((J : ℝ) + 1) ^ J = a at hasq ha0 ⊢
  generalize Real.sqrt (25 * P1) ^ J = b at hbsq hb0 ⊢
  generalize x ^ (-(J : ℝ) / 2) = y at hysq hy0 ⊢
  generalize Pe ^ (2 * J) = Q at hQsq hQ1 ⊢
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ1
  have hsum : ((J + 1 : ℝ) / x) ^ J + (P * Pe ^ 2) ^ J ≤ (a * y) ^ 2 + (b * Q) ^ 2 := by
    have hay : (a * y) ^ 2 = ((J + 1 : ℝ) / x) ^ J := by
      rw [mul_pow, hasq, hysq, ← mul_pow, mul_one_div]
    have hbQ : (b * Q) ^ 2 = (25 * P1 * (Pe ^ 2 * Pe ^ 2)) ^ J := by
      rw [mul_pow, hbsq, hQsq, ← mul_pow]
    rw [hay, hbQ]
    apply add_le_add le_rfl
    apply pow_le_pow_left₀ hB.le
    calc P * Pe ^ 2 ≤ 25 * Pe ^ 2 * P1 * Pe ^ 2 := mul_le_mul_of_nonneg_right hPP1 (by positivity)
      _ = 25 * P1 * (Pe ^ 2 * Pe ^ 2) := by ring
  have hsq : (a * y) ^ 2 + (b * Q) ^ 2 ≤ (a * y + b * Q) ^ 2 := by
    have hc : 0 ≤ 2 * ((a * y) * (b * Q)) := by positivity
    calc (a * y) ^ 2 + (b * Q) ^ 2 ≤ (a * y) ^ 2 + (b * Q) ^ 2 + 2 * ((a * y) * (b * Q)) :=
          le_add_of_nonneg_right hc
      _ = (a * y + b * Q) ^ 2 := by ring
  have hmain : (Real.exp 1 * (2 * Real.exp 1) / min (x / (J + 1)) (1 / (P * Pe ^ 2))) ^ J ≤
      (e2 * (a * y + b * Q)) ^ 2 := by
    rw [hsplit, show (e2 * (a * y + b * Q)) ^ 2 = e2 ^ 2 * (a * y + b * Q) ^ 2 from
      mul_pow _ _ _, he2sq]
    exact mul_le_mul_of_nonneg_left (hpow.trans (hsum.trans hsq)) (pow_nonneg (by positivity) _)
  have hlin : a * y + b * Q ≤ (a + b) * Q * (1 + y) := by
    have h1 : a * y ≤ a * Q * y :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_right ha0 hQ1) hy0
    have h2 : 0 ≤ a * Q := mul_nonneg ha0 hQ0
    have h3 : 0 ≤ b * Q * y := mul_nonneg (mul_nonneg hb0 hQ0) hy0
    calc a * y + b * Q ≤ a * Q * y + b * Q + (a * Q + b * Q * y) := by linarith
      _ = (a + b) * Q * (1 + y) := by ring
  calc Real.sqrt ((Real.exp 1 * (2 * Real.exp 1) / min (x / (J + 1)) (1 / (P * Pe ^ 2))) ^ J)
      ≤ Real.sqrt ((e2 * (a * y + b * Q)) ^ 2) := Real.sqrt_le_sqrt hmain
    _ = e2 * (a * y + b * Q) := Real.sqrt_sq (mul_nonneg he20 (by positivity))
    _ ≤ e2 * ((a + b) * Q * (1 + y)) := mul_le_mul_of_nonneg_left hlin he20
    _ = e2 * (a + b) * Q * (1 + y) := by ring

/-- Readout: an all-order smooth `L²` class with an `H^j` carrier has a `C^j` representative whose
`cellSobolevNorm j` is bounded by the carrier norm. -/
theorem interior_smooth_readout (j : ℕ) (u : ComplexCellL2)
    (hall : ∀ K : ℕ, ∃ U : TorusHk K ℂ, torusHkValueCLM U = u)
    (W : TorusHk j ℂ) (hW : torusHkValueCLM W = u) :
    ∃ g₁ : Vec 2 → ℂ, ContDiff ℝ j g₁ ∧
      (u : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] g₁ ∧
      cellSobolevNorm j g₁ ≤
        (∑ b ∈ Finset.range (j + 1), (Fintype.card (DerivativeWord2 b) : ℝ≥0∞)) * ‖W‖ₑ := by
  obtain ⟨f, hf, _, hfu⟩ := torusHigher_all_order_smooth_representative u hall
  have hfj : ContDiff ℝ (j : ℕ∞) f := hf.of_le (by exact_mod_cast le_top)
  refine ⟨f, hfj, hfu.symm, ?_⟩
  exact torusHigher_smooth_cellSobolevNorm_le W f hfj (by rw [hW]; exact hfu.symm)

/-- The constants of ingredient 02. -/
def interiorSmoothingConstant (j : ℕ) : ℝ :=
  (∑ b ∈ Finset.range (j + 1), (Fintype.card (DerivativeWord2 b) : ℝ)) *
    (Real.sqrt (2 * Real.exp 1 ^ 2) ^ j *
      (Real.sqrt (j + 1) ^ j +
        Real.sqrt (25 * constructedNativeWindowPrice j 1 0 constructedGraphBudget) ^ j)) + 1

theorem interiorSmoothingConstant_pos (j : ℕ) : 0 < interiorSmoothingConstant j := by
  unfold interiorSmoothingConstant
  positivity

/-- Real Brillouin-zone frequencies: `|ξ|` and `|√η ξ_i|` are at most `5P_e`. -/
theorem brillouin_frequency_le {η : ℝ} (hη : 0 < η) (ξ : Fin 2 → ℂ)
    (hξ : ∀ i, (ξ i).im = 0 ∧ |(ξ i).re| ≤ Real.pi / Real.sqrt η) :
    fibreNorm ξ ≤ 5 * peFactor η ∧ ∀ i, ‖(Real.sqrt η : ℂ) * ξ i‖ ≤ 5 * peFactor η := by
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have hPe : 1 ≤ peFactor η := one_le_peFactor η
  have hinv : (Real.sqrt η)⁻¹ ≤ peFactor η := by
    unfold peFactor
    linarith
  have hpi := Real.pi_pos
  have hpi3 : Real.pi < 3.15 := Real.pi_lt_d2
  have hnorm : ∀ i, ‖ξ i‖ ≤ Real.pi * peFactor η := by
    intro i
    have he : ξ i = ((ξ i).re : ℂ) := Complex.ext (by simp) (by simp [(hξ i).1])
    rw [he, Complex.norm_real, Real.norm_eq_abs]
    calc |(ξ i).re| ≤ Real.pi / Real.sqrt η := (hξ i).2
      _ = Real.pi * (Real.sqrt η)⁻¹ := div_eq_mul_inv _ _
      _ ≤ Real.pi * peFactor η := mul_le_mul_of_nonneg_left hinv hpi.le
  refine ⟨?_, fun i => ?_⟩
  · unfold fibreNorm
    have hsum : ∑ i, ‖ξ i‖ ^ 2 ≤ (5 * peFactor η) ^ 2 := by
      rw [Fin.sum_univ_two]
      have h0 := pow_le_pow_left₀ (norm_nonneg _) (hnorm 0) 2
      have h1 := pow_le_pow_left₀ (norm_nonneg _) (hnorm 1) 2
      have hP2 : 0 ≤ peFactor η ^ 2 := by positivity
      have hpi2 : Real.pi ^ 2 ≤ 25 / 2 := by nlinarith
      calc ‖ξ 0‖ ^ 2 + ‖ξ 1‖ ^ 2 ≤ 2 * (Real.pi ^ 2 * peFactor η ^ 2) := by
            rw [mul_pow] at h0 h1
            linarith
        _ ≤ 2 * (25 / 2 * peFactor η ^ 2) := by gcongr
        _ = (5 * peFactor η) ^ 2 := by ring
    calc Real.sqrt (∑ i, ‖ξ i‖ ^ 2) ≤ Real.sqrt ((5 * peFactor η) ^ 2) := Real.sqrt_le_sqrt hsum
      _ = 5 * peFactor η := Real.sqrt_sq (by positivity)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    calc Real.sqrt η * ‖ξ i‖ ≤ Real.sqrt η * (Real.pi / Real.sqrt η) := by
          apply mul_le_mul_of_nonneg_left _ hs.le
          have he : ξ i = ((ξ i).re : ℂ) := Complex.ext (by simp) (by simp [(hξ i).1])
          rw [he, Complex.norm_real, Real.norm_eq_abs]
          exact (hξ i).2
      _ = Real.pi := by field_simp
      _ ≤ 5 * peFactor η := by linarith

theorem interior_step_valid (K : ℕ) {x P Pe : ℝ} (hx : 0 < x) (hP : 0 < P) (hPe : 0 < Pe) :
    0 < min (x / (K + 1)) (1 / (P * Pe ^ 2)) ∧
      (P * Pe ^ 2) * min (x / (K + 1)) (1 / (P * Pe ^ 2)) ≤ 1 ∧
      (K : ℝ) * min (x / (K + 1)) (1 / (P * Pe ^ 2)) ≤ x := by
  have hK : (0 : ℝ) < K + 1 := by positivity
  have hB : 0 < P * Pe ^ 2 := by positivity
  refine ⟨lt_min (div_pos hx hK) (by positivity), ?_, ?_⟩
  · calc (P * Pe ^ 2) * min (x / (K + 1)) (1 / (P * Pe ^ 2)) ≤ (P * Pe ^ 2) * (1 / (P * Pe ^ 2)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hB.le
      _ = 1 := mul_one_div_cancel hB.ne'
  · calc (K : ℝ) * min (x / (K + 1)) (1 / (P * Pe ^ 2)) ≤ (K : ℝ) * (x / (K + 1)) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) (Nat.cast_nonneg K)
      _ ≤ x := by
          rw [mul_div_assoc', div_le_iff₀ hK]
          nlinarith

/-- From the squared native bound to the `cellSobolevNorm` price of the statement. -/
theorem interior_smoothing_final (j : ℕ) {Pe x P : ℝ} (W : TorusHk j ℂ) {i : ℝ} (hi : 0 ≤ i)
    (hPe : 1 ≤ Pe) (hx : 0 < x) (hP : 0 < P)
    (hPP1 : P ≤ 25 * Pe ^ 2 * constructedNativeWindowPrice j 1 0 constructedGraphBudget)
    (hW : ‖W‖ ^ 2 ≤
      (Real.exp 1 * (2 * Real.exp 1) / min (x / (j + 1)) (1 / (P * Pe ^ 2))) ^ j * i ^ 2) :
    (∑ b ∈ Finset.range (j + 1), (Fintype.card (DerivativeWord2 b) : ℝ≥0∞)) * ‖W‖ₑ ≤
      ENNReal.ofReal (interiorSmoothingConstant j * Pe ^ (2 * j) * (1 + x) ^ (2 * j) *
        (1 + x ^ (-(j : ℝ) / 2))) * ENNReal.ofReal i := by
  have hP1 : 0 ≤ constructedNativeWindowPrice j 1 0 constructedGraphBudget :=
    (constructedNativeWindowPrice_pos j 1 0 _ zero_le_one le_rfl
      constructedGraphBudget_pos.le).le
  have hstep := interior_smoothing_step_price j hPe hx hP hP1 hPP1
  set F := (Real.exp 1 * (2 * Real.exp 1) / min (x / (j + 1)) (1 / (P * Pe ^ 2))) ^ j with hF
  have hF0 : 0 ≤ F := by
    rw [hF]
    apply pow_nonneg
    apply div_nonneg (by positivity)
    exact (lt_min (div_pos hx (by positivity)) (by positivity)).le
  have hWi : ‖W‖ ≤ Real.sqrt F * i := by
    calc ‖W‖ = Real.sqrt (‖W‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (F * i ^ 2) := Real.sqrt_le_sqrt hW
      _ = Real.sqrt F * i := by rw [Real.sqrt_mul hF0, Real.sqrt_sq hi]
  set c := ∑ b ∈ Finset.range (j + 1), (Fintype.card (DerivativeWord2 b) : ℝ) with hc
  have hc0 : 0 ≤ c := by positivity
  have hcard : (∑ b ∈ Finset.range (j + 1), (Fintype.card (DerivativeWord2 b) : ℝ≥0∞)) =
      ENNReal.ofReal c := by
    rw [hc, ENNReal.ofReal_sum_of_nonneg (fun _ _ => Nat.cast_nonneg _)]
    simp only [ENNReal.ofReal_natCast]
  set e2 := Real.sqrt (2 * Real.exp 1 ^ 2) ^ j
  set ab := Real.sqrt (j + 1) ^ j +
    Real.sqrt (25 * constructedNativeWindowPrice j 1 0 constructedGraphBudget) ^ j
  set y := x ^ (-(j : ℝ) / 2)
  have he2 : 0 ≤ e2 := pow_nonneg (Real.sqrt_nonneg _) _
  have hab : 0 ≤ ab := by positivity
  have hy : 0 ≤ y := Real.rpow_nonneg hx.le _
  have hQ : 1 ≤ Pe ^ (2 * j) := one_le_pow₀ hPe
  have hX : 1 ≤ (1 + x) ^ (2 * j) := one_le_pow₀ (by linarith)
  have hbound : c * ‖W‖ ≤ (interiorSmoothingConstant j * Pe ^ (2 * j) * (1 + x) ^ (2 * j) *
      (1 + y)) * i := by
    have hA : 0 ≤ c * (e2 * ab) := mul_nonneg hc0 (mul_nonneg he2 hab)
    have hB : 0 ≤ Pe ^ (2 * j) * (1 + y) := by positivity
    calc c * ‖W‖ ≤ c * (Real.sqrt F * i) := mul_le_mul_of_nonneg_left hWi hc0
      _ ≤ c * (e2 * ab * Pe ^ (2 * j) * (1 + y) * i) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hstep hi) hc0
      _ = (c * (e2 * ab)) * (Pe ^ (2 * j) * (1 + y)) * i := by ring
      _ ≤ (c * (e2 * ab) + 1) * (Pe ^ (2 * j) * (1 + y) * (1 + x) ^ (2 * j)) * i := by
          apply mul_le_mul_of_nonneg_right _ hi
          apply mul_le_mul (le_add_of_nonneg_right zero_le_one)
            (le_mul_of_one_le_right hB hX) hB (by positivity)
      _ = (interiorSmoothingConstant j * Pe ^ (2 * j) * (1 + x) ^ (2 * j) * (1 + y)) * i := by
          unfold interiorSmoothingConstant
          ring
  rw [hcard, ← ofReal_norm, ← ENNReal.ofReal_mul hc0, ← ENNReal.ofReal_mul
    (by unfold interiorSmoothingConstant; positivity)]
  exact ENNReal.ofReal_le_ofReal hbound

/-- **Ingredient 02 of `scalar_package_interior`.** -/
theorem interiorHighSmoothing : Assembly.InteriorHighSmoothingStatement := by
  intro α s₀ q hα₀ hα₁ hs₀ hs₁ hq ζ hζ
  obtain ⟨Λr, hΛr, hrel⟩ := bandChain_relaxation_large hα₀ hα₁ hs₀ hs₁ hq hζ 6 (by norm_num)
  refine ⟨Λr, fun Λ hΛ => ⟨interiorSmoothingConstant, fun j => 2 * j,
    interiorSmoothingConstant_pos, ?_⟩⟩
  intro M κ hband m hm2 hmM ν B hνeq hBeq y₀ G hG
  have hΛ1 : 1 ≤ Λ := by omega
  have hν : 0 < ν := hνeq ▸ CycleReference.bandChain_pos hΛ1 hζ hband hmM
  have hBmean : B = ocMeanFlux α q Λ ζ m ν := by
    rw [← hBeq, hband.2 m (by omega) hmM, hνeq]
  subst hBmean
  have hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m := hνeq ▸ hrel Λ hΛ M κ hband m hm2 hmM
  have hv := ocCellDrift_isCellDrift (α := α) (q := q) (m := m) hΛ1 hζ ν y₀
  obtain ⟨V, hV⟩ := hv.2.1
  have hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2) ≤ constructedGraphBudget :=
    fun t x => ocCellDrift_weighted_uniform_bound hΛ1 hζ hν hr y₀ x t
  have hCw : 0 ≤ constructedGraphBudget := constructedGraphBudget_pos.le
  have hη : 0 < ν / ocMeanFlux α q Λ ζ m ν :=
    div_pos hν (hν.trans_le (CycleReference.meanFlux_ge_input hΛ1 hζ hν))
  have hPe := one_le_peFactor (ν / ocMeanFlux α q Λ ζ m ν)
  have hPe0 : 0 < peFactor (ν / ocMeanFlux α q Λ ζ m ν) := zero_lt_one.trans_le hPe
  have hR1 : 1 ≤ 5 * peFactor (ν / ocMeanFlux α q Λ ζ m ν) := by linarith
  have hR0 : 0 ≤ 5 * peFactor (ν / ocMeanFlux α q Λ ζ m ν) := by linarith
  have hPrice : ∀ K : ℕ, constructedNativeWindowPrice K (5 * peFactor (ν / ocMeanFlux α q Λ ζ m ν))
      0 constructedGraphBudget ≤ 25 * peFactor (ν / ocMeanFlux α q Λ ζ m ν) ^ 2 *
        constructedNativeWindowPrice K 1 0 constructedGraphBudget := fun K =>
    (constructedNativeWindowPrice_le_sq K hR1 hCw).trans_eq (by ring)
  intro j ξ hξ s t hst
  obtain ⟨hξR, hθR⟩ := brillouin_frequency_le hη ξ hξ
  have hreal : ∀ i, (ξ i).im = 0 := fun i => (hξ i).1
  have hx : 0 < t - s := sub_pos.mpr hst
  have hPpos : ∀ K : ℕ, 0 < constructedNativeWindowPrice K
      (5 * peFactor (ν / ocMeanFlux α q Λ ζ m ν)) 0 constructedGraphBudget := fun K =>
    constructedNativeWindowPrice_pos K _ 0 _ hR0 le_rfl hCw
  refine ⟨fun D hD => ?_, fun Ψ hΨ => ?_⟩
  · have hall : ∀ K : ℕ, ∃ U : TorusHk K ℂ, torusHkValueCLM U = cellRawTrace D t := by
      intro K
      obtain ⟨hδ, hsh, hfit⟩ := interior_step_valid K hx (hPpos K) hPe0
      obtain ⟨U, hU, _⟩ := interior_forward_native_bound K hΛ1 hζ hν hr y₀ hv V hV G hG _ hCw
        hw ξ hreal _ hR0 hξR hθR hst _ hδ hsh (by linarith) D hD
      exact ⟨U, hU⟩
    obtain ⟨hδ, hsh, hfit⟩ := interior_step_valid j hx (hPpos j) hPe0
    obtain ⟨W, hWv, hWb⟩ := interior_forward_native_bound j hΛ1 hζ hν hr y₀ hv V hV G hG _ hCw
      hw ξ hreal _ hR0 hξR hθR hst _ hδ hsh (by linarith) D hD
    obtain ⟨g₁, hg₁, hae, hnorm⟩ := interior_smooth_readout j _ hall W hWv
    refine ⟨g₁, hg₁, (cellRawTrace_ae D t (hD.2.2.1 t ⟨hst.le, le_rfl⟩).1).symm.trans hae, ?_⟩
    rw [cellL2Norm_eq_of_class _ _ (cellRawTrace_ae D s (hD.2.2.1 s ⟨le_rfl, hst.le⟩).1)]
    exact hnorm.trans (interior_smoothing_final j W (norm_nonneg _) hPe hx (hPpos j)
      (hPrice j) hWb)
  · have hst' : -t < -s := neg_lt_neg hst
    have hx' : -s - -t = t - s := by ring
    have hrealn : ∀ i, (-ξ i).im = 0 := fun i => by simp [hreal i]
    have hξRn : fibreNorm (fun k => -ξ k) ≤ 5 * peFactor (ν / ocMeanFlux α q Λ ζ m ν) := by
      rw [fibreNorm_neg]
      exact hξR
    have hθRn : ∀ i, ‖(Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) : ℂ) * (fun k => -ξ k) i‖ ≤
        5 * peFactor (ν / ocMeanFlux α q Λ ζ m ν) := fun i => by
      simpa only [mul_neg, norm_neg] using hθR i
    have hall : ∀ K : ℕ, ∃ U : TorusHk K ℂ, torusHkValueCLM U = cellRawTrace Ψ (-s) := by
      intro K
      obtain ⟨hδ, hsh, hfit⟩ := interior_step_valid K hx (hPpos K) hPe0
      obtain ⟨U, hU, _⟩ := interior_reflected_native_bound K hΛ1 hζ hν hr y₀ hv V hV G hG _
        hCw hw (fun k => -ξ k) hrealn _ hR0 hξRn hθRn hst' _ hδ hsh (by linarith) Ψ hΨ
      exact ⟨U, hU⟩
    obtain ⟨hδ, hsh, hfit⟩ := interior_step_valid j hx (hPpos j) hPe0
    obtain ⟨W, hWv, hWb⟩ := interior_reflected_native_bound j hΛ1 hζ hν hr y₀ hv V hV G hG _
      hCw hw (fun k => -ξ k) hrealn _ hR0 hξRn hθRn hst' _ hδ hsh (by linarith) Ψ hΨ
    obtain ⟨g₁, hg₁, hae, hnorm⟩ := interior_smooth_readout j _ hall W hWv
    refine ⟨g₁, hg₁,
      (cellRawTrace_ae Ψ (-s) (hΨ.2.2.1 (-s) ⟨hst'.le, le_rfl⟩).1).symm.trans hae, ?_⟩
    rw [cellL2Norm_eq_of_class _ _ (cellRawTrace_ae Ψ (-t) (hΨ.2.2.1 (-t) ⟨le_rfl, hst'.le⟩).1)]
    exact hnorm.trans (interior_smoothing_final j W (norm_nonneg _) hPe hx (hPpos j)
      (hPrice j) hWb)

end AVRegularity.CycleWords.Interior
end

section
open Homogenization AVenhance AVRegularity.Weighted AVRegularity.CycleJointProofs
namespace AVRegularity.CycleWords.Interior

/-! Static polynomial chart certificates for every time-only cell metric and bounded stream. -/

theorem cellChartWeights : Assembly.CellChartWeightsStatement := by
  intro Cw Cψ Cvj
  refine ⟨chartWeightConstant Cψ, fun m => zero_lt_one.trans_le (chartWeightConstant_ge_one Cψ m), ?_⟩
  intro η G v h t₀ S hS M
  obtain ⟨ψ, hψ, _hperiodic, hv, hψbound⟩ := h.stream
  have hSpos : 0 < S := zero_lt_one.trans_le hS
  let e := Real.sqrt (η / S)
  have he : e ^ 2 = η / S := Real.sq_sqrt (div_pos h.eta_pos hSpos).le
  have hW (m : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (planeMomentPolynomial m e 0) := by
    unfold planeMomentPolynomial
    fun_prop
  have hWpos (m : ℕ) (z : Vec 2) : 0 < planeMomentPolynomial m e 0 z := by
    unfold planeMomentPolynomial
    positivity
  refine ⟨{
    W := fun m _ => planeMomentPolynomial m e 0
    Phi := fun m => chartStreamFlux ψ (planeMomentPolynomial m e 0)
    lam := fun m => chartWeightConstant Cψ m / S
    smooth := ?_
    pos := fun m _ _ z => hWpos m z
    comparable := ?_
    defect := ?_
    bound := ?_
    lam_bound := ?_ }⟩
  · intro m _
    exact ⟨((hW m).of_le (by simp)).comp contDiff_snd,
      chartStreamFlux_smooth ψ hψ _ (hW m)⟩
  · intro m _ t _ z
    have hc := chartWeightConstant_ge_one Cψ m
    have hi := (inv_le_one₀ (zero_lt_one.trans_le hc)).mpr hc
    constructor
    · change (chartWeightConstant Cψ m)⁻¹ * planeMomentPolynomial m e 0 z ≤ _
      exact (mul_le_mul_of_nonneg_right hi (hWpos m z).le).trans_eq (one_mul _)
    · change planeMomentPolynomial m e 0 z ≤ chartWeightConstant Cψ m * planeMomentPolynomial m e 0 z
      exact (one_mul _).symm.trans_le (mul_le_mul_of_nonneg_right hc (hWpos m z).le)
  · intro m _ t _ z
    simp only [deriv_const, zero_add]
    rw [hv t z]
    have hd := moment_metric_diffusion_le G h.metric m e t z
    have hr := chart_diffusion_rate (C := Cψ) h.eta_le hSpos he (hWpos m z).le m
    calc
      _ ≤ (∑ k : Fin 2, streamVel ψ t z k *
          fderiv ℝ (planeMomentPolynomial m e 0) z (basisVec k)) +
          chartWeightConstant Cψ m / S * planeMomentPolynomial m e 0 z :=
        add_le_add le_rfl (hd.trans hr)
      _ = _ := by rw [chartStreamFlux_divergence ψ hψ _ (hW m)]; ring
  · intro m _ t _ z
    rw [chartStreamFlux_sq]
    exact chart_gradient_flux_rate h.eta_pos h.eta_le hSpos he (hWpos m z)
      (hψbound t z) m (fun k => fderiv ℝ (planeMomentPolynomial m e 0) z (basisVec k))
      (fun k => planeMomentPolynomial_gradient_abs_le m e 0 z k)
  · intro m _
    exact ⟨div_nonneg (zero_le_one.trans (chartWeightConstant_ge_one Cψ m)) hSpos.le, le_rfl⟩

end AVRegularity.CycleWords.Interior
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleWords.Interior

/-! **`CellNegativeAdjointStatement`: negative-weight adjoint propagation**.

The transposed scalar equation is the forward chain of the time-reversed cell problem
(`G(-τ)`, `-v(-τ)`, stream `-ψ(-τ)`). For `0 < ε ≤ 1` the shifted weight
`W = (1 + ϖ²|z|²)^{-p} + ε` is a chart weight at the rate `Λ/S`, `Λ = 64(p+1)²(1+Cψ²)`
(`negChartWeights_exists`), so the clipped factorial energy at radius `ρ = r/L`,
`r = (3A·P_e)⁻¹`, grows by at most `3e^{18Λ}`.
Between the clipped weight and the decaying weight the energies differ by a factor `2` and an
`ε`-multiple of the unweighted energy; `ε → 0` removes the latter. The conversion between the
factorial energy and the negative jet norm costs `√(k+1)ρ^{-k}`, which is `P_e^k` up to
constants. -/

/-- The jet constant of the reversed drift. -/
def negAdjointJetConstant (Cvj : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (k + 1),
    (Fintype.card (DerivativeWord2 l) : ℝ) * ‖driftCoefficientEmbedding‖ * |Cvj l| + 1

theorem one_le_negAdjointJetConstant (Cvj : ℕ → ℝ) (k : ℕ) : 1 ≤ negAdjointJetConstant Cvj k := by
  unfold negAdjointJetConstant
  have : 0 ≤ ∑ l ∈ Finset.range (k + 1),
      (Fintype.card (DerivativeWord2 l) : ℝ) * ‖driftCoefficientEmbedding‖ * |Cvj l| :=
    Finset.sum_nonneg fun _ _ => by positivity
  linarith

theorem negAdjointJetConstant_term (Cvj : ℕ → ℝ) {k l : ℕ} (hl : l ≤ k) :
    (Fintype.card (DerivativeWord2 l) : ℝ) * ‖driftCoefficientEmbedding‖ * |Cvj l| ≤
      negAdjointJetConstant Cvj k := by
  unfold negAdjointJetConstant
  have h := Finset.single_le_sum (s := Finset.range (k + 1))
    (f := fun l => (Fintype.card (DerivativeWord2 l) : ℝ) * ‖driftCoefficientEmbedding‖ * |Cvj l|)
    (fun _ _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le hl))
  linarith

/-- The reserve `L = √(2e^{18Λ})` of the absorption. -/
def negAdjointReserve (Cψ : ℝ) (p : ℕ) : ℝ :=
  Real.sqrt (2 * Real.exp (18 * negWeightRate p Cψ))

theorem negAdjointReserve_sq (Cψ : ℝ) (p : ℕ) :
    negAdjointReserve Cψ p ^ 2 = 2 * Real.exp (18 * negWeightRate p Cψ) :=
  Real.sq_sqrt (by positivity)

theorem one_le_negAdjointReserve (Cψ : ℝ) (p : ℕ) : 1 ≤ negAdjointReserve Cψ p := by
  unfold negAdjointReserve
  rw [Real.one_le_sqrt]
  have h := Real.add_one_le_exp (18 * negWeightRate p Cψ)
  have h0 := negWeightRate_nonneg p Cψ
  linarith

/-- The constant of ingredient 05. -/
def negAdjointConstant (Cψ : ℝ) (Cvj : ℕ → ℝ) (k p : ℕ) : ℝ :=
  Real.sqrt (k + 1) * (3 * negAdjointJetConstant Cvj k * negAdjointReserve Cψ p) ^ k *
    (Real.sqrt 6 * Real.exp (9 * negWeightRate p Cψ))

/-- An inequality that holds up to every small multiple of a fixed quantity. -/
theorem le_of_forall_small_mul_add {X Y Z : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → X ≤ Y + ε * Z) : X ≤ Y := by
  by_contra hXY
  push Not at hXY
  have hZ : 0 ≤ |Z| := abs_nonneg Z
  set δ := X - Y with hδ
  have hδ0 : 0 < δ := by linarith
  set ε := min 1 (δ / (2 * (|Z| + 1))) with hεdef
  have hε : 0 < ε := lt_min one_pos (div_pos hδ0 (by positivity))
  have h1 := h ε hε (min_le_left _ _)
  have h2 : ε * Z ≤ ε * |Z| := mul_le_mul_of_nonneg_left (le_abs_self Z) hε.le
  have h3 : ε * |Z| ≤ δ / 2 := by
    have hε2 : ε ≤ δ / (2 * (|Z| + 1)) := min_le_right _ _
    calc ε * |Z| ≤ δ / (2 * (|Z| + 1)) * |Z| := mul_le_mul_of_nonneg_right hε2 hZ
      _ ≤ δ / (2 * (|Z| + 1)) * (|Z| + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = δ / 2 := by field_simp
  linarith

/-- The factorial energy of a zero carrier vanishes. -/
theorem rawWeightedFactorialEnergy_zero_carrier {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    (ρ : ℝ) (q : Vec 2 → ℝ) (K : ℕ) :
    rawWeightedFactorialEnergy ρ q (0 : PlaneHk Set.univ K E).toFunction.jet = 0 := by
  unfold rawWeightedFactorialEnergy
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Finset.sum_eq_zero, mul_zero]
  intro w _
  apply integral_eq_zero_of_ae
  filter_upwards [planeHk_zero_raw_jet (E := E) K ⟨j, w⟩] with x hx
  simp [hx]

/-- The time-reversed drift is a stream drift. -/
theorem reversed_streamVel (ψ : ℝ → Vec 2 → ℝ) (τ : ℝ) (z : Vec 2) :
    -(streamVel ψ (-τ) z) = streamVel (fun τ' z' => -ψ (-τ') z') τ z := by
  have he : spaceGrad (fun x => -ψ (-τ) x) z = -spaceGrad (ψ (-τ)) z := by
    ext k
    simp only [spaceGrad, fderiv_fun_neg, neg_apply, Pi.neg_apply]
  simp only [streamVel]
  rw [he, Matrix.mulVec_neg]

theorem cellNegativeAdjoint : Assembly.CellNegativeAdjointStatement := by
  intro Cw Cψ Cvj
  refine ⟨negAdjointConstant Cψ Cvj, fun k => k, ?_⟩
  intro η G v hb t₀ S hS k p s t hts hst htS f u w hchain
  obtain ⟨ψ, hψ, _hper, hvψ, hψb⟩ := hb.stream
  have hη := hb.eta_pos
  have hsη : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  set Λ := negWeightRate p Cψ with hΛdef
  have hΛ : 0 ≤ Λ := negWeightRate_nonneg p Cψ
  set A := negAdjointJetConstant Cvj k with hAdef
  have hA : 1 ≤ A := one_le_negAdjointJetConstant Cvj k
  set L := negAdjointReserve Cψ p with hLdef
  have hL : 1 ≤ L := one_le_negAdjointReserve Cψ p
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  set Pe := peFactor η with hPedef
  have hPe : 1 ≤ Pe := by
    simp only [hPedef, peFactor]
    have := inv_pos.mpr hsη
    linarith
  have hPe0 : 0 < Pe := lt_of_lt_of_le one_pos hPe
  have hsPe : Real.sqrt η * Pe = Real.sqrt η + 1 := by
    simp only [hPedef, peFactor]
    field_simp
  set r := 1 / (3 * A * Pe) with hrdef
  have hr : 0 < r := by positivity
  have hr3 : r ≤ 1 / 3 := by
    rw [hrdef]
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith
  set ϖ := Real.sqrt (η / S) with hϖdef
  -- the time-reversed problem
  set vr : ℝ → Vec 2 → Vec 2 := fun τ z => -(v (-τ) z) with hvrdef
  have hψr : ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Vec 2 => -ψ (-q.1) q.2) :=
    (hψ.comp (contDiff_fst.neg.prodMk contDiff_snd)).neg
  have hvr : ∀ τ z, vr τ z = streamVel (fun τ' z' => -ψ (-τ') z') τ z := fun τ z => by
    simp only [hvrdef]
    rw [hvψ (-τ) z]
    exact reversed_streamVel ψ τ z
  have hψrb : ∀ τ z, Real.sqrt η * |-ψ (-τ) z| ≤ Cψ := fun τ z => by
    rw [abs_neg]
    exact hψb (-τ) z
  have hGr : IsCellMetric (fun τ _ => G (-τ)) := cellMetric_timeReverse hb.metric
  have hvrD : IsCellDrift vr := cellDrift_timeReverse hb.drift
  have hvrs : ∀ τ, ContDiff ℝ (⊤ : ℕ∞) (vr τ) := fun τ => (hb.smooth (-τ)).neg
  -- the derivative bounds of the reversed drift
  have hiter : ∀ (l : ℕ) τ x, Real.sqrt η * ‖iteratedFDeriv ℝ l (vr τ) x‖ ≤ Cvj l := by
    intro l τ x
    have h := hb.jets l (-τ) x
    change ‖iteratedFDeriv ℝ l (Real.sqrt η • v (-τ)) x‖ ≤ _ at h
    have hs : iteratedFDeriv ℝ l (Real.sqrt η • v (-τ)) x =
        Real.sqrt η • iteratedFDeriv ℝ l (v (-τ)) x :=
      iteratedFDeriv_const_smul_apply ((hb.smooth (-τ)).contDiffAt.of_le
        (by exact_mod_cast le_top))
    have hn : iteratedFDeriv ℝ l (vr τ) x = -iteratedFDeriv ℝ l (v (-τ)) x :=
      iteratedFDeriv_neg_apply
    rw [hs, norm_smul, Real.norm_of_nonneg hsη.le] at h
    rw [hn, norm_neg]
    exact h
  set V := |Cvj 0| / Real.sqrt η with hVdef
  have hV : 0 ≤ V := by positivity
  have hbv : ∀ τ ∈ Icc (-t) (-s), ∀ x, ‖vr τ x‖ ≤ V := fun τ _ x => by
    have h := hiter 0 τ x
    rw [norm_iteratedFDeriv_zero] at h
    rw [hVdef, le_div_iff₀ hsη, mul_comm]
    exact h.trans (le_abs_self _)
  set strain := A / Real.sqrt η with hstraindef
  have hstrain : 0 ≤ strain := by positivity
  have hjets : ∀ τ ∈ Icc (-t) (-s), ∀ l, 1 ≤ l → l ≤ k → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (vr τ)) l x‖ ≤
        strain * (1 : ℝ) ^ l * (l.factorial : ℝ) * (1 : ℝ) ^ ((1 : ℤ) - l) := by
    intro τ _ l _ hlk x
    rw [one_pow, one_zpow, mul_one, mul_one]
    have h1 := driftCoefficient_array_norm_le_iterated (vr τ) l
      ((hvrs τ).of_le (by simp)) x
    have h2 := hiter l τ x
    have h3 := negAdjointJetConstant_term Cvj hlk
    have hc : 0 ≤ (Fintype.card (DerivativeWord2 l) : ℝ) * ‖driftCoefficientEmbedding‖ := by
      positivity
    have hit : ‖iteratedFDeriv ℝ l (vr τ) x‖ ≤ |Cvj l| / Real.sqrt η := by
      rw [le_div_iff₀ hsη, mul_comm]
      exact h2.trans (le_abs_self _)
    have hfac : (1 : ℝ) ≤ l.factorial := by exact_mod_cast Nat.factorial_pos l
    calc ‖coefficientDerivativeArray (driftCoefficient (vr τ)) l x‖
        ≤ (Fintype.card (DerivativeWord2 l) : ℝ) * ‖driftCoefficientEmbedding‖ *
            (|Cvj l| / Real.sqrt η) := h1.trans (mul_le_mul_of_nonneg_left hit hc)
      _ = (Fintype.card (DerivativeWord2 l) : ℝ) * ‖driftCoefficientEmbedding‖ * |Cvj l| /
            Real.sqrt η := by ring
      _ ≤ A / Real.sqrt η := div_le_div_of_nonneg_right h3 hsη.le
      _ ≤ A / Real.sqrt η * l.factorial := le_mul_of_one_le_right hstrain hfac
  have hsmall : 1 * r / 1 ≤ 1 / 2 := by
    rw [one_mul, div_one]
    linarith
  have hstrainSmall : strain * 1 * r ^ 2 ≤ 1 / 8 := by
    have hX : 1 ≤ A * (Real.sqrt η * Pe) * Pe := by
      rw [hsPe]
      have h1 : 1 ≤ Real.sqrt η + 1 := by linarith
      calc (1 : ℝ) = 1 * 1 * 1 := by ring
        _ ≤ A * (Real.sqrt η + 1) * Pe := by gcongr
    have he : strain * 1 * r ^ 2 = 1 / (9 * (A * (Real.sqrt η * Pe) * Pe)) := by
      rw [hstraindef, hrdef]
      field_simp
      ring
    rw [he]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hreserve : Real.exp (18 * Λ) / L ^ 2 ≤ 1 / 2 := by
    rw [hLdef, negAdjointReserve_sq, ← hΛdef]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith [Real.exp_pos (18 * Λ)]
  have hdiv : ∀ τ ∈ Icc (-t) (-s), ∀ x, ∑ k : Fin 2, fderiv ℝ (vr τ) x (basisVec k) k = 0 :=
    fun τ _ x => cellDrift_classical_divergence_zero hvrD hvrs τ x
  have hvm : Measurable (fun q : Icc (-t) (-s) × Vec 2 => vr q.1 q.2) :=
    hvrD.1.comp (measurable_subtype_coe.prodMap measurable_id)
  have hGm : Measurable (fun q : Icc (-t) (-s) × Vec 2 => (fun τ (_ : Vec 2) => G (-τ)) q.1 q.2) :=
    hGr.1.comp (measurable_subtype_coe.prodMap measurable_id)
  have hGb : ∀ (i : Fin 1 × Unit), ∀ τ ∈ Icc (-t) (-s), ∀ (l : Fin (k + 1)) (x : Vec 2) (a b : Fin 2),
      ‖iteratedFDeriv ℝ l.val (fun _ : Vec 2 => G (-τ) a b) x‖ ≤ 2 := by
    intro _ τ _ l x a b
    rcases Nat.eq_zero_or_pos l.val with hl | hl
    · rw [hl, norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      exact cellMetric_entry_bound hb.metric (-τ) x a b
    · rw [iteratedFDeriv_const_of_ne hl.ne']
      simp
  -- the energies for one shift `ε`
  set ρ := r / L with hρdef
  have hρ : 0 < ρ := div_pos hr hL0
  have hρ1 : ρ ≤ 1 := by
    rw [hρdef, div_le_one hL0]
    linarith
  have hlimit : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (∑ a : Fin (k + 1), factorialWeight ρ a.val *
          negJetIntegral ϖ p (u 0 () (-s)).toFunction.jet a) ≤
        6 * Real.exp (18 * Λ) * (∑ a : Fin (k + 1), factorialWeight ρ a.val *
            negJetIntegral ϖ p (f ()).toFunction.jet a) +
          ε * (6 * Real.exp (18 * Λ) * ∑ a : Fin (k + 1), factorialWeight ρ a.val *
            ∫ z, ∑ w : DerivativeWord2 a.val, ‖(f ()).toFunction.jet ⟨a, w⟩ z‖ ^ 2) := by
    intro ε hε hε1
    obtain ⟨C, hCW, hClam⟩ := negChartWeights_exists η S Cψ hη hb.eta_le hS
      (fun τ => G (-τ)) hGr vr (fun τ' z' => -ψ (-τ') z') hψr hvr hψrb p ε hε hε1 (-(t₀ + S))
    have hgr := constantMetric_scalarChain_clipped_factorial_absorption_of_rate
      (ι := Unit) (h := fun _ : Unit => ℝ) (-t) (-s) (by linarith) (fun _ _ => k) k
      (fun _ => le_rfl) vr hvm (fun τ _ => hvrs τ) V strain 1 1 hV hstrain le_rfl one_pos hbv
      hjets (fun τ _ => G (-τ)) hGm (fun _ _ _ _ _ => contDiff_const) (fun _ _ => 2) hGb hGr
      (fun _ _ => rfl) (fun τ _ x => hb.metric.2.2.1 (-τ) x) _ (fun _ _ => 0)
      (fun _ => planeHk_zero_time_memLp _ _) (fun q => u q.1 q.2) (fun q => w q.1 q.2) hchain
      ((0 : Fin 1), ()) (fun _ _ _ _ => contDiff_const) (-(t₀ + S)) S ϖ 0 0 0
      (fun _ => 2 + ε⁻¹ + negWeightRate p Cψ) C le_rfl 2 r L two_pos hr hL hsmall hstrainSmall
      Λ hΛ hClam.le hreserve hdiv (by linarith) (by linarith)
    dsimp only at hgr
    have h1 := hgr (-s) ⟨by linarith, le_rfl⟩
    simp only [hCW, rawWeightedFactorialEnergy_zero_carrier, intervalIntegral.integral_zero,
      mul_zero, add_zero] at h1
    have hgrad : 0 ≤ (∫ τ in (-t)..(-s), rawWeightedGradientEnergy (r / L)
        (fun x => clipWeight 2 (negWeight ϖ p x + ε)) (w 0 () τ).toFunction.jet) / 4 := by
      apply div_nonneg _ (by norm_num)
      apply intervalIntegral.integral_nonneg (by linarith)
      intro τ _
      exact rawWeightedGradientEnergy_nonneg _ _ (fun x => (clipWeight_pos two_pos
        (by have := negWeight_pos ϖ p x; linarith)).le) _
    have hq : rawWeightedFactorialEnergy ρ (fun z => clipWeight 2 (negWeight ϖ p z + ε))
          (u 0 () (-s)).toFunction.jet ≤
        3 * Real.exp (18 * Λ) * rawWeightedFactorialEnergy ρ
          (fun z => clipWeight 2 (negWeight ϖ p z + ε)) (f ()).toFunction.jet := by
      have h1' : rawWeightedFactorialEnergy ρ (fun z => clipWeight 2 (negWeight ϖ p z + ε))
            (u 0 () (-s)).toFunction.jet +
          (∫ τ in (-t)..(-s), rawWeightedGradientEnergy (r / L)
            (fun x => clipWeight 2 (negWeight ϖ p x + ε)) (w 0 () τ).toFunction.jet) / 4 ≤
          3 * Real.exp (18 * Λ) * rawWeightedFactorialEnergy ρ
            (fun z => clipWeight 2 (negWeight ϖ p z + ε)) (f ()).toFunction.jet := h1
      linarith
    have hu := (clip_shift_energy_bounds (u 0 () (-s)) ϖ p (ρ := ρ) hε hε1).1
    have hf := (clip_shift_energy_bounds (f ()) ϖ p (ρ := ρ) hε hε1).2
    have hsplit : (∑ a : Fin (k + 1), factorialWeight ρ a.val *
          (negJetIntegral ϖ p (f ()).toFunction.jet a +
            ε * ∫ z, ∑ w : DerivativeWord2 a.val, ‖(f ()).toFunction.jet ⟨a, w⟩ z‖ ^ 2)) =
        (∑ a : Fin (k + 1), factorialWeight ρ a.val *
            negJetIntegral ϖ p (f ()).toFunction.jet a) +
          ε * ∑ a : Fin (k + 1), factorialWeight ρ a.val *
            ∫ z, ∑ w : DerivativeWord2 a.val, ‖(f ()).toFunction.jet ⟨a, w⟩ z‖ ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    have he0 : 0 ≤ 6 * Real.exp (18 * Λ) := by positivity
    calc (∑ a : Fin (k + 1), factorialWeight ρ a.val *
          negJetIntegral ϖ p (u 0 () (-s)).toFunction.jet a)
        ≤ 2 * (3 * Real.exp (18 * Λ) * rawWeightedFactorialEnergy ρ
            (fun z => clipWeight 2 (negWeight ϖ p z + ε)) (f ()).toFunction.jet) := by linarith
      _ ≤ 6 * Real.exp (18 * Λ) * ((∑ a : Fin (k + 1), factorialWeight ρ a.val *
            negJetIntegral ϖ p (f ()).toFunction.jet a) +
          ε * ∑ a : Fin (k + 1), factorialWeight ρ a.val *
            ∫ z, ∑ w : DerivativeWord2 a.val, ‖(f ()).toFunction.jet ⟨a, w⟩ z‖ ^ 2) := by
          rw [← hsplit]
          nlinarith
      _ = _ := by ring
  have hE := le_of_forall_small_mul_add hlimit
  -- conversion to the negative jet norms
  set Iu := negJetIntegral ϖ p (u 0 () (-s)).toFunction.jet with hIudef
  set If := negJetIntegral ϖ p (f ()).toFunction.jet with hIfdef
  have hIu : ∀ a, 0 ≤ Iu a := negJetIntegral_nonneg ϖ p _
  have hIf : ∀ a, 0 ≤ If a := negJetIntegral_nonneg ϖ p _
  have hN1 := negNorm_le_energy k hρ hρ1 Iu hIu
  have hN2 := energy_le_negNorm_sq k hρ.le hρ1 If hIf
  set Nu := ∑ a : Fin (k + 1), (1 / (a.val.factorial : ℝ)) * Real.sqrt (Iu a) with hNudef
  set Nf := ∑ a : Fin (k + 1), (1 / (a.val.factorial : ℝ)) * Real.sqrt (If a) with hNfdef
  have hNf0 : 0 ≤ Nf := Finset.sum_nonneg fun _ _ => by positivity
  have hsq : Real.sqrt (∑ a : Fin (k + 1), factorialWeight ρ a.val * Iu a) ≤
      Real.sqrt 6 * Real.exp (9 * Λ) * Nf := by
    have h6 : Real.sqrt (6 * Real.exp (18 * Λ) * Nf ^ 2) = Real.sqrt 6 * Real.exp (9 * Λ) * Nf := by
      have hx : Real.exp (18 * Λ) = Real.exp (9 * Λ) ^ 2 := by
        rw [sq, ← Real.exp_add]
        ring_nf
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num), Real.sqrt_sq hNf0, hx,
        Real.sqrt_sq (Real.exp_pos _).le]
    rw [← h6]
    apply Real.sqrt_le_sqrt
    exact hE.trans (mul_le_mul_of_nonneg_left hN2 (by positivity))
  have hρinv : ρ⁻¹ = 3 * A * L * Pe := by
    rw [hρdef, hrdef]
    field_simp
  have hcore : Nu ≤ negAdjointConstant Cψ Cvj k p * Pe ^ k * Nf := by
    calc Nu ≤ Real.sqrt (k + 1) * ρ⁻¹ ^ k *
          Real.sqrt (∑ a : Fin (k + 1), factorialWeight ρ a.val * Iu a) := hN1
      _ ≤ Real.sqrt (k + 1) * ρ⁻¹ ^ k * (Real.sqrt 6 * Real.exp (9 * Λ) * Nf) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = negAdjointConstant Cψ Cvj k p * Pe ^ k * Nf := by
          rw [hρinv, negAdjointConstant, ← hAdef, ← hLdef, ← hΛdef]
          ring
  have hC0 : 0 ≤ negAdjointConstant Cψ Cvj k p := by
    unfold negAdjointConstant
    have := one_le_negAdjointJetConstant Cvj k
    have := one_le_negAdjointReserve Cψ p
    positivity
  have hT : 1 ≤ (1 + (t - s)) ^ k := one_le_pow₀ (by linarith)
  have hfinal : Nu ≤ negAdjointConstant Cψ Cvj k p * Pe ^ k * (1 + (t - s)) ^ k * Nf := by
    refine hcore.trans (mul_le_mul_of_nonneg_right ?_ hNf0)
    exact le_mul_of_one_le_right (by positivity) hT
  have hLu := weightedJetNorm_neg_eq ϖ p (u 0 () (-s))
  have hLf := weightedJetNorm_neg_eq ϖ p (f ())
  calc weightedJetNorm (fun _ : Unit => (1 : ℝ)) (-(p : ℝ)) k (Real.sqrt (η / S)) 1
        (fun x a w' => planeJetOrder (u 0 x (-s)) a w') = ENNReal.ofReal Nu := hLu
    _ ≤ ENNReal.ofReal (negAdjointConstant Cψ Cvj k p * Pe ^ k * (1 + (t - s)) ^ k * Nf) :=
        ENNReal.ofReal_le_ofReal hfinal
    _ = ENNReal.ofReal (negAdjointConstant Cψ Cvj k p * Pe ^ k * (1 + (t - s)) ^ k) *
          weightedJetNorm (fun _ : Unit => (1 : ℝ)) (-(p : ℝ)) k (Real.sqrt (η / S)) 1
            (fun x a w' => planeJetOrder (f x) a w') := by
        rw [ENNReal.ofReal_mul (by positivity)]
        exact congrArg _ hLf.symm

end AVRegularity.CycleWords.Interior
end
