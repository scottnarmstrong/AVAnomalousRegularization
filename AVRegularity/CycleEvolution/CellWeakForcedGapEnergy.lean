-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.CellTimeMetricDriftCLM
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The actual cell energy inequality bounds both coordinates of the finite energy carrier. -/

theorem cellActualWeak_state_energy_bound {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (hκ : ∀ t, ‖C.κ t‖ ≤ k)
    (S : ℝ → ComplexCellL2) (F : ℝ → Fin 2 → ComplexCellL2)
    (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (hF : ∀ j, MemLp (fun t => F t j) 2 (volume.restrict (Icc a b)))
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice
      (fun t => cellDualDerivative C hG V hv hb t (slice t) (S t) (F t))) :
    let W := (‖u a‖ ^ 2 + ∫ s in a..b, ‖S s‖ ^ 2 + 9 * ∑ j, ‖F s j‖ ^ 2) *
      Real.exp (300 * (1 + ∑ j, ‖C.θ j‖ ^ 2 + V ^ 2 + k) * (b - a))
    (∀ t ∈ Icc a b, ‖u t‖ ^ 2 ≤ W) ∧
      (∫ t in a..b, ‖slice t‖ ^ 2) ≤ (b - a + 2) * W := by
  let W := (‖u a‖ ^ 2 + ∫ s in a..b, ‖S s‖ ^ 2 + 9 * ∑ j, ‖F s j‖ ^ 2) *
    Real.exp (300 * (1 + ∑ j, ‖C.θ j‖ ^ 2 + V ^ 2 + k) * (b - a))
  have ht : ∀ t ∈ Icc a b, ‖u t‖ ^ 2 ≤ W :=
    cellActualWeak_energy_sup_bound hab C hG V k hv hb hκ S F hS hF u slice h
  have he := cellActualWeak_energy_bound hab C hG V k hv hb hκ S F hS hF u slice h b ⟨hab, le_rfl⟩
  change ‖u b‖ ^ 2 + (∫ s in a..b, (1 / 2) * ∑ j, ‖cellDerivativeCLM j (slice s)‖ ^ 2) ≤ W at he
  rw [intervalIntegral.integral_const_mul] at he
  have hg : (∫ s in a..b, ∑ j, ‖cellDerivativeCLM j (slice s)‖ ^ 2) ≤ 2 * W := by
    linarith [sq_nonneg ‖u b‖]
  have hs := cellWeakH1_integral_budget hab u slice _ h W (2 * W) ht hg
  refine ⟨ht, hs.trans_eq ?_⟩
  ring

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Filter Homogenization AVRegularity.Sobolev
open scoped Topology
namespace AVRegularity.CycleEvolution

/-! The Hilbert trace gives the literal extended-square continuity clause. -/

/-- Continuous spatial classes give the public raw trace continuity for any representatives. -/
theorem cellClass_trace_continuity (I : Set ℝ) (D : ℝ → RawJet2 1 ℂ)
    (u : ℝ → ComplexCellL2) (hu : ContinuousOn u I)
    (he : ∀ t ∈ I, (u t : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] cellValue D t) :
    ∀ t0 ∈ I, Tendsto (fun t => ∫⁻ x in AVenhance.unitCube,
      ‖cellValue D t x - cellValue D t0 x‖ₑ ^ 2) (𝓝[I] t0) (𝓝 0) := by
  intro t0 ht0
  have hn : Tendsto (fun t => ‖u t - u t0‖ ^ 2) (𝓝[I] t0) (𝓝 0) := by
    have hc : ContinuousWithinAt (fun _ : ℝ => u t0) I t0 := continuousWithinAt_const
    simpa only [Pi.sub_apply, Pi.pow_def, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
      (((hu t0 ht0).sub hc).norm.pow 2).tendsto
  have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hn
  have hEq : (fun t => ENNReal.ofReal (‖u t - u t0‖ ^ 2)) =ᶠ[𝓝[I] t0]
      fun t => ∫⁻ x in AVenhance.unitCube, ‖cellValue D t x - cellValue D t0 x‖ₑ ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    simpa only [Pi.sub_apply, ← ENNReal.ofReal_pow (norm_nonneg _)] using
      (cellTrace_square_lintegral _ (u t - u t0)
        ((Lp.coeFn_sub _ _).trans ((he t ht).sub (he t0 ht0)))).symm
  simpa only [Function.comp_def, ENNReal.ofReal_zero] using hlim.congr' hEq

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set
namespace AVRegularity.CycleEvolution

/-! Continuous Hilbert traces on finite time intervals are Bochner L². -/

/-- No additional temporal integrability premise is needed for a continuous trace on a finite interval. -/
theorem cellContinuous_trace_memLp {a b : ℝ} (u : ℝ → ComplexCellL2)
    (hu : ContinuousOn u (Icc a b)) : MemLp u 2 (volume.restrict (Icc a b)) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hu.norm
  apply MemLp.of_bound (hu.aestronglyMeasurable_of_isCompact isCompact_Icc measurableSet_Icc) M
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact hM (mem_image_of_mem (fun t => ‖u t‖) ht)

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The literal weak cell integrand respects actual absolutely convergent raw jet series. -/

/-- Absolutely convergent value, gradient, and forcing series give the literal raw-series integrand. -/
theorem cellLiteralRHS_raw_tsum {J : Type*} [Countable J]
    (C : CellCoefficients) (t : ℝ) (ψ : Vec 2 → ℂ) (dψ : Fin 2 → Vec 2 → ℂ)
    (x : Vec 2) (D : J → RawJet2 1 ℂ) (src : J → Vec 2 → ℂ)
    (F : J → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hu : Summable (fun j => cellValue (fun _ => D j) t x))
    (hdu : Summable (fun j => cellGradient (D j) x))
    (hsrc : Summable (fun j => src j x)) (hF : Summable (fun j => F j x)) :
    cellLiteralRHS C t (cellValue (fun _ a y => ∑' j, D j a y) t)
      (cellGradComp (fun a y => ∑' j, D j a y)) ψ dψ
      (fun y => ∑' j, src j y) (fun y => ∑' j, F j y) x =
      ∑' j, cellLiteralRHS C t (cellValue (fun _ => D j) t) (cellGradComp (D j))
        ψ dψ (src j) (F j) x := by
  have he := cellLiteralRHS_tsum_components C t ψ dψ x
    (fun j => cellValue (fun _ => D j) t x) (fun j => src j x)
    (fun j => cellGradient (D j) x) (fun j => F j x) hu hdu hsrc hF
  have hg := cellGradient_tsum_of_summable D x hdu
  change cellLiteralRHS C t (fun _ => ∑' j, cellValue (fun _ => D j) t x)
    (fun k _ => cellGradient (fun a y => ∑' j, D j a y) x k) ψ dψ
    (fun _ => ∑' j, src j x) (fun _ => ∑' j, F j x) x = _
  rw [hg]
  exact he

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Filter AVRegularity.Sobolev
open scoped Topology
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Continuous fixed-test forcing integrals and their Fourier limits. -/

/-- Source integral as a continuous H¹ test functional. -/
def cellSourceIntegralCLM (s t : ℝ) (θ : Fin 2 → ℂ)
    (S : ℝ → ComplexCellL2) (F : ℝ → Fin 2 → ComplexCellL2) : TorusHk 1 ℂ →L[ℝ] ℝ :=
  innerSL ℝ (∫ r in s..t, cellSourceDual θ (S r) (F r))

/-- The continuous source integral functional has the literal scalar/flux forcing value. -/
theorem cellSourceIntegralCLM_apply {a b s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) (θ : Fin 2 → ℂ)
    (S : ℝ → ComplexCellL2) (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (F : ℝ → Fin 2 → ComplexCellL2)
    (hF : ∀ j, MemLp (fun r => F r j) 2 (volume.restrict (Icc a b))) (z : TorusHk 1 ℂ) :
    cellSourceIntegralCLM s t θ S F z = ∫ r in s..t, cellSourceFunctional θ (S r) (F r) z := by
  have hg := cellSourceDual_memLp θ S hS F hF
  have hint : IntervalIntegrable (fun r => cellSourceDual θ (S r) (F r)) volume s t := by
    apply intervalIntegrable_iff.mpr
    rw [uIoc_of_le hst]
    exact (hg.integrable (by norm_num)).mono_measure (Measure.restrict_mono
      (Ioc_subset_Icc_self.trans (Icc_subset_Icc hs.1 ht.2)) le_rfl)
  let L := innerSL ℝ z
  calc
    _ = L (∫ r in s..t, cellSourceDual θ (S r) (F r)) := by
      change inner ℝ (∫ r in s..t, cellSourceDual θ (S r) (F r)) z =
        inner ℝ z (∫ r in s..t, cellSourceDual θ (S r) (F r))
      exact real_inner_comm _ _
    _ = ∫ r in s..t, L (cellSourceDual θ (S r) (F r)) :=
      (L.intervalIntegral_comp_comm hint).symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro r _
      exact (real_inner_comm _ _).trans (cellSourceDual_pairing θ (S r) (F r) z)

/-- Source integrals converge along Fourier-projected tests. -/
theorem cellSource_integral_fourier_tendsto {a b s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) (θ : Fin 2 → ℂ)
    (S : ℝ → ComplexCellL2) (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (F : ℝ → Fin 2 → ComplexCellL2)
    (hF : ∀ j, MemLp (fun r => F r j) 2 (volume.restrict (Icc a b)))
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (z : TorusHk 1 ℂ) :
    Tendsto (fun n => ∫ r in s..t, cellSourceFunctional θ (S r) (F r) (galerkinProj (φ n) z))
      atTop (𝓝 (∫ r in s..t, cellSourceFunctional θ (S r) (F r) z)) := by
  have he := ((cellSourceIntegralCLM s t θ S F).continuous.tendsto z).comp
    ((galerkinProj_tendsto z).comp hφ.tendsto_atTop)
  simpa only [Function.comp_def, cellSourceIntegralCLM_apply hs ht hst θ S hS F hF] using he

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CycleEvolution

/-! Temporal metric and drift operators have exactly the existing actual spatial entry representatives. -/

theorem cellTimeMetricEntryCLM_ae (I : Set ℝ)
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G) (j k : Fin 2)
    (u : Lp ComplexCellL2 2 (volume.restrict I)) :
    cellTimeMetricEntryCLM I hG j k u =ᵐ[volume.restrict I]
      fun t => cellMetricEntryCLM hG t j k (u t) := by
  have he := cellTimeCoefficientCLM_ae I (fun t x => (G t x j k : ℂ))
    (Complex.continuous_ofReal.measurable.comp (cellMetric_entry_measurable hG j k))
    2 (by norm_num) (fun t x => by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using cellMetric_entry_bound hG t x j k) u
  filter_upwards [he] with t ht
  exact ht.trans (cellCoefficientComplexCLM_eq (fun x => (G t x j k : ℂ))
    ((Complex.continuous_ofReal.measurable.comp (cellMetric_entry_measurable hG j k)).comp
      (measurable_const.prodMk measurable_id) |>.aestronglyMeasurable)
    2 (by norm_num) (fun x => by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using cellMetric_entry_bound hG t x j k) (u t))

theorem cellTimeDriftEntryCLM_ae (I : Set ℝ) (C : CellCoefficients) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (j : Fin 2)
    (u : Lp ComplexCellL2 2 (volume.restrict I)) :
    cellTimeDriftEntryCLM I C V hv hb j u =ᵐ[volume.restrict I]
      fun t => cellDriftEntryCLM C V hv hb t j (u t) := by
  have he := cellTimeCoefficientCLM_ae I (fun t x => (C.v t x j : ℂ))
    (Complex.continuous_ofReal.measurable.comp ((measurable_pi_apply j).comp hv))
    |V| (abs_nonneg V) (fun t x => by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using cellDrift_entry_bound hb t x j) u
  filter_upwards [he] with t ht
  exact ht.trans (cellCoefficientComplexCLM_eq (fun x => (C.v t x j : ℂ))
    ((Complex.continuous_ofReal.measurable.comp ((measurable_pi_apply j).comp hv)).comp
      (measurable_const.prodMk measurable_id) |>.aestronglyMeasurable)
    |V| (abs_nonneg V) (fun x => by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using cellDrift_entry_bound hb t x j) (u t))

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Actual variable-scalar fixed-test increments for a genuine weak Hilbert curve. -/

theorem cellWeakVariableScalar_increment {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → ComplexCellL2} {slice g : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice g) (c dc : ℝ → ℂ)
    (hc : StrongTimeRegularity a b c dc) (hdc : MemLp dc ⊤ (volume.restrict (Icc a b)))
    (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (z : TorusHk 1 ℂ) :
    inner ℝ (cellScalarCLM (c t) (u t)) (torusHkValueCLM z) -
      inner ℝ (cellScalarCLM (c s) (u s)) (torusHkValueCLM z) =
      ∫ r in s..t, inner ℝ (cellH1Scalar (c r) (g r) +
        cellPivotDualCLM (cellScalarCLM (dc r) (u r))) z := by
  have hsub : uIcc s t ⊆ uIcc a b := by
    rw [uIcc_of_le hst, uIcc_of_le hab]
    exact Icc_subset_Icc hs.1 ht.2
  have hE := h.complex_test_strongTime hab z
  have hEc : ContinuousOn (fun r => cellComplexPair (u r) (torusHkValueCLM z)) (uIcc s t) :=
    hE.ac.continuousOn.mono hsub
  have hc' := hc.mono hsub
  have hP := cellDualComplexPair_intervalIntegrable hs ht hst g h.dual z
  have hdc' : IntervalIntegrable dc volume s t := by
    apply intervalIntegrable_iff.mpr
    rw [uIoc_of_le hst]
    exact (hdc.integrable (by simp)).mono_measure (Measure.restrict_mono
      (Ioc_subset_Icc_self.trans (Icc_subset_Icc hs.1 ht.2)) le_rfl)
  have hprod := (hc.complex_mul hE).mono hsub
  have hdprod : IntervalIntegrable (fun r => dc r * cellComplexPair (u r) (torusHkValueCLM z) +
      c r * cellDualComplexPair (g r) z) volume s t :=
    (hdc'.mul_continuousOn hEc).add (hP.continuousOn_mul hc'.ac.continuousOn)
  have he := hprod.complex_increment hdprod
  have hreal := Complex.reCLM.intervalIntegral_comp_comm hdprod
  change (∫ r in s..t, (dc r * cellComplexPair (u r) (torusHkValueCLM z) +
    c r * cellDualComplexPair (g r) z).re) =
    (∫ r in s..t, dc r * cellComplexPair (u r) (torusHkValueCLM z) +
      c r * cellDualComplexPair (g r) z).re at hreal
  have hre := congrArg Complex.re he
  rw [Complex.sub_re, ← hreal] at hre
  simp only [← cellComplexPair_scalar_left, cellComplexPair_re] at hre
  rw [hre]
  apply intervalIntegral.integral_congr
  intro r _
  change (cellComplexPair (cellScalarCLM (dc r) (u r)) (torusHkValueCLM z) +
    c r * cellDualComplexPair (g r) z).re =
    inner ℝ (cellH1Scalar (c r) (g r) + cellPivotDualCLM (cellScalarCLM (dc r) (u r))) z
  rw [← cellDualComplexPair_re, cellDualComplexPair_add_left,
    cellDualComplexPair_scalar_left, cellPivotDual_complex_pair, cellComplexPair_scalar_left]
  congr 1
  exact add_comm _ _

/-! Actual variable-scalar fixed-test increments for a genuine weak Hilbert curve. -/

theorem cellWeakVariableScalar_increment_L2 {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → ComplexCellL2} {slice g : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice g) (c dc : ℝ → ℂ)
    (hc : StrongTimeRegularity a b c dc) (hdc : MemLp dc 2 (volume.restrict (Icc a b)))
    (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (z : TorusHk 1 ℂ) :
    inner ℝ (cellScalarCLM (c t) (u t)) (torusHkValueCLM z) -
      inner ℝ (cellScalarCLM (c s) (u s)) (torusHkValueCLM z) =
      ∫ r in s..t, inner ℝ (cellH1Scalar (c r) (g r) +
        cellPivotDualCLM (cellScalarCLM (dc r) (u r))) z := by
  have hsub : uIcc s t ⊆ uIcc a b := by
    rw [uIcc_of_le hst, uIcc_of_le hab]
    exact Icc_subset_Icc hs.1 ht.2
  have hE := h.complex_test_strongTime hab z
  have hEc : ContinuousOn (fun r => cellComplexPair (u r) (torusHkValueCLM z)) (uIcc s t) :=
    hE.ac.continuousOn.mono hsub
  have hc' := hc.mono hsub
  have hP := cellDualComplexPair_intervalIntegrable hs ht hst g h.dual z
  have hdc' : IntervalIntegrable dc volume s t := by
    apply intervalIntegrable_iff.mpr
    rw [uIoc_of_le hst]
    exact (hdc.integrable (by norm_num)).mono_measure (Measure.restrict_mono
      (Ioc_subset_Icc_self.trans (Icc_subset_Icc hs.1 ht.2)) le_rfl)
  have hprod := (hc.complex_mul hE).mono hsub
  have hdprod : IntervalIntegrable (fun r => dc r * cellComplexPair (u r) (torusHkValueCLM z) +
      c r * cellDualComplexPair (g r) z) volume s t :=
    (hdc'.mul_continuousOn hEc).add (hP.continuousOn_mul hc'.ac.continuousOn)
  have he := hprod.complex_increment hdprod
  have hreal := Complex.reCLM.intervalIntegral_comp_comm hdprod
  change (∫ r in s..t, (dc r * cellComplexPair (u r) (torusHkValueCLM z) +
    c r * cellDualComplexPair (g r) z).re) =
    (∫ r in s..t, dc r * cellComplexPair (u r) (torusHkValueCLM z) +
      c r * cellDualComplexPair (g r) z).re at hreal
  have hre := congrArg Complex.re he
  rw [Complex.sub_re, ← hreal] at hre
  simp only [← cellComplexPair_scalar_left, cellComplexPair_re] at hre
  rw [hre]
  apply intervalIntegral.integral_congr
  intro r _
  change (cellComplexPair (cellScalarCLM (dc r) (u r)) (torusHkValueCLM z) +
    c r * cellDualComplexPair (g r) z).re =
    inner ℝ (cellH1Scalar (c r) (g r) + cellPivotDualCLM (cellScalarCLM (dc r) (u r))) z
  rw [← cellDualComplexPair_re, cellDualComplexPair_add_left,
    cellDualComplexPair_scalar_left, cellPivotDual_complex_pair, cellComplexPair_scalar_left]
  congr 1
  exact add_comm _ _

end AVRegularity.CycleEvolution
end

section
open Homogenization
namespace AVRegularity.CycleEvolution

/-! Literal conjugation symmetry of the raw weak integrand, including actual forcing and tests. -/

def cellFluxConj (F : Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) :
    Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ) := fun x => WithLp.toLp 2 (fun j => star (F x j))

theorem cellLiteralRHS_conjugate (C : CellCoefficients) (t : ℝ)
    (u : Vec 2 → ℂ) (du : Fin 2 → Vec 2 → ℂ)
    (ψ : Vec 2 → ℂ) (dψ : Fin 2 → Vec 2 → ℂ)
    (src : Vec 2 → ℂ) (F : Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) (x : Vec 2) :
    cellLiteralRHS (cellConjugateCoefficients C) t (fun y => star (u y))
      (fun j y => star (du j y)) (fun y => star (ψ y))
      (fun j y => star (dψ j y)) (fun y => star (src y)) (cellFluxConj F) x =
      star (cellLiteralRHS C t u du ψ dψ src F x) := by
  simp only [cellLiteralRHS, cellConjugateCoefficients, cellFluxConj, Fin.sum_univ_two,
    PiLp.toLp_apply, star_sub, star_add, star_neg, star_mul, Complex.star_def, Complex.conj_ofReal,
    Complex.conj_I]
  ring

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! Actual periodic weak jets are closed under pointwise series with summable component L2 norms. -/

/-- A coordinate projection of the complete periodic Hilbert jet. -/
def cellJetComponentCLM (K : ℕ) (a : JetIndex2 K) :
    TorusHk K ℂ →L[ℝ] Lp ℂ 2 (volume.restrict AVenhance.unitCube) :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : JetIndex2 K => Lp ℂ 2 (volume.restrict AVenhance.unitCube)) a).comp
    (torusHkGraph (E := ℂ) K).toSubmodule.subtypeL

/-- Summability in all component L2 norms closes the actual raw periodic weak-jet predicate. -/
theorem cellPeriodicWeakJet_tsum {J : Type*} [Countable J] {K : ℕ}
    (D : J → RawJet2 K ℂ) (hD : ∀ j, HasPeriodicOrderedWeakJet (D j))
    (hs : (∑' j, ∑ a : JetIndex2 K, cellL2Norm (D j a)) < ⊤) :
    HasPeriodicOrderedWeakJet (fun a x => ∑' j, D j a x) := by
  let u : J → TorusHk K ℂ := fun j => (TorusHkFunction.mk (D j) (hD j)).toHk
  have hu (j : J) : ‖u j‖ₑ ≤ ∑ a : JetIndex2 K, cellL2Norm (D j a) :=
    cellPeriodicJet_enorm_le_cellL2Norm (TorusHkFunction.mk (D j) (hD j))
  have hus : (∑' j, ‖u j‖ₑ) < ⊤ := (ENNReal.tsum_le_tsum hu).trans_lt hs
  have hsummable : Summable u := Summable.of_enorm hus.ne
  have ha (a : JetIndex2 K) : (∑' j, ‖cellJetComponentCLM K a (u j)‖ₑ) < ⊤ := by
    have he (j : J) : ‖cellJetComponentCLM K a (u j)‖ₑ = cellL2Norm (D j a) := by
      change ‖((hD j).2.1 a).toLp (D j a)‖ₑ = _
      exact Lp.enorm_toLp _
    simp_rw [he]
    refine (ENNReal.tsum_le_tsum (fun j => ?_)).trans_lt hs
    exact Finset.single_le_sum
      (fun b _ => (bot_le : (0 : ℝ≥0∞) ≤ cellL2Norm (D j b))) (Finset.mem_univ a)
  have hrep (a : JetIndex2 K) :
      (((∑' j, u j).val a) : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
        (fun x => ∑' j, D j a x) := by
    change (cellJetComponentCLM K a (∑' j, u j) : Vec 2 → ℂ) =ᵐ[_] _
    rw [(cellJetComponentCLM K a).map_tsum hsummable]
    have hall : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ j,
        cellJetComponentCLM K a (u j) x = D j a x :=
      ae_all_iff.mpr (fun j => (hD j).2.1 a |>.coeFn_toLp)
    filter_upwards [Lp.coeFn_tsum (ha a).ne, hall] with x hx hx'
    exact hx.trans (tsum_congr (fun j => hx' j))
  apply cellPeriodicWeakJet_of_ae_components (∑' j, u j).toFunction.hasPeriodicWeakJet
  · intro a n x
    exact tsum_congr (fun j => (hD j).1 a n x)
  · intro a
    exact (hrep a).symm.trans (periodicJetRepresentative_ae (∑' j, u j).val a).symm

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Multiplication of a genuine weak Hilbert curve by an actual bounded differentiable phase. -/

theorem CellWeakHilbertCurve.variable_complex_scalar {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → ComplexCellL2} {slice g : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice g) (c dc : ℝ → ℂ)
    (hc : StrongTimeRegularity a b c dc) (hdc : MemLp dc ⊤ (volume.restrict (Icc a b))) :
    CellWeakHilbertCurve a b (fun t => cellScalarCLM (c t) (u t))
      (fun t => cellH1Scalar (c t) (slice t))
      (fun t => cellH1Scalar (c t) (g t) + cellPivotDualCLM (cellScalarCLM (dc t) (u t))) := by
  let μ := volume.restrict (Icc a b)
  have hcm := hc.complex_memLp_top hab
  have hcc : ContinuousOn c (Icc a b) := by simpa only [uIcc_of_le hab] using hc.ac.continuousOn
  have hu : MemLp u 2 μ := (memLp_congr_ae h.agrees).mpr ((torusHkValueCLM (E := ℂ) (K := 1)).comp_memLp' h.state)
  have hg := cellH1Scalar_variable_memLp c hcm g h.dual
  have hp := cellPivotDualCLM.comp_memLp' (cellScalarCLM_variable_memLp dc hdc u hu)
  have hdu : MemLp (fun t => cellH1Scalar (c t) (g t) +
      cellPivotDualCLM (cellScalarCLM (dc t) (u t))) 2 μ := by
    simpa only [sub_neg_eq_add, Pi.add_def, Function.comp_def, μ] using hg.sub hp.neg
  refine ⟨cellScalarCLM_variable_continuousOn c hcc u h.trace,
    cellH1Scalar_variable_memLp c hcm slice h.state, hdu, ?_, ?_⟩
  · filter_upwards [h.agrees] with t ht
    rw [ht, cellH1Scalar_value]
  · intro s hs t ht hst z
    exact cellWeakVariableScalar_increment hab h c dc hc hdc s hs t ht hst z

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The exact public weak-equation resolvent identity for symmetric metric changes. -/

/-- A change of metric is an additional divergence flux, with no additional solution regularity. -/
theorem cellSolution_metric_change (I : Set ℝ)
    (G H : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (src : ℝ → Vec 2 → ℂ)
    (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) (D : ℝ → RawJet2 1 ℂ)
    (hG : ∀ t x, (G t x).IsSymm) (hH : ∀ t x, (H t x).IsSymm)
    (hD : IsCellSolution I ⟨H, v, 0, 0⟩ src F D) :
    IsCellSolution I ⟨G, v, 0, 0⟩ src (F + cellMetricFlux (H - G) D) D := by
  refine ⟨hD.1, hD.2.1, hD.2.2.1, hD.2.2.2.1, hD.2.2.2.2.1,
    hD.2.2.2.2.2.1, ?_⟩
  intro s hs t ht hst ψ
  have hw := hD.2.2.2.2.2.2 s hs t ht hst ψ
  let μ := volume.restrict AVenhance.unitCube
  let R := fun τ => cellLiteralRHS ⟨H, v, 0, 0⟩ τ (cellValue D τ)
    (fun j => cellGradComp (D τ) j) (ψ.jet (valueIndex2 1))
    (fun j => ψ.jet ⟨⟨1, by decide⟩, fun _ => j⟩) (src τ) (F τ)
  let R' := fun τ => cellLiteralRHS ⟨G, v, 0, 0⟩ τ (cellValue D τ)
    (fun j => cellGradComp (D τ) j) (ψ.jet (valueIndex2 1))
    (fun j => ψ.jet ⟨⟨1, by decide⟩, fun _ => j⟩) (src τ)
    ((F + cellMetricFlux (H - G) D) τ)
  have he : R' = R := by
    funext τ x
    exact (cellLiteralRHS_metric_change G H v τ (D τ) _ _ (src τ) (F τ)
      (hG τ) (hH τ) x).symm
  change Integrable (fun x => cellValue D t x * ψ.jet (valueIndex2 1) x) μ ∧
    Integrable (fun x => cellValue D s x * ψ.jet (valueIndex2 1) x) μ ∧
    (∀ᵐ τ ∂volume.restrict (Ioc s t), Integrable (R τ) μ) ∧
    IntegrableOn (fun τ => ∫ x, R τ x ∂μ) (Ioc s t) ∧
    (∫ x, cellValue D t x * ψ.jet (valueIndex2 1) x ∂μ) -
      (∫ x, cellValue D s x * ψ.jet (valueIndex2 1) x ∂μ) =
        ∫ τ in Ioc s t, ∫ x, R τ x ∂μ at hw
  change Integrable (fun x => cellValue D t x * ψ.jet (valueIndex2 1) x) μ ∧
    Integrable (fun x => cellValue D s x * ψ.jet (valueIndex2 1) x) μ ∧
    (∀ᵐ τ ∂volume.restrict (Ioc s t), Integrable (R' τ) μ) ∧
    IntegrableOn (fun τ => ∫ x, R' τ x ∂μ) (Ioc s t) ∧
    (∫ x, cellValue D t x * ψ.jet (valueIndex2 1) x ∂μ) -
      (∫ x, cellValue D s x * ψ.jet (valueIndex2 1) x ∂μ) =
        ∫ τ in Ioc s t, ∫ x, R' τ x ∂μ
  rw [he]
  exact hw

/-- The inverse relation obeys the same exact metric-change identity. -/
theorem cellInverse_metric_change
    (G H : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (src : ℝ → Vec 2 → ℂ)
    (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) (D : ℝ → RawJet2 1 ℂ)
    (hG : ∀ t x, (G t x).IsSymm) (hH : ∀ t x, (H t x).IsSymm)
    (hD : IsCellInverseValue ⟨H, v, 0, 0⟩ src F D) :
    IsCellInverseValue ⟨G, v, 0, 0⟩ src (F + cellMetricFlux (H - G) D) D :=
  ⟨cellSolution_metric_change univ G H v src F D hG hH hD.1, hD.2⟩

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Conjugation preserves the actual pointwise gradient and cell L² norms. -/

theorem cellFluxConj_norm (F : Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) (x : Vec 2) :
    ‖cellFluxConj F x‖ = ‖F x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  simp only [cellFluxConj, PiLp.toLp_apply, norm_star]

theorem cellGradient_conjugate (D : RawJet2 1 ℂ) :
    cellGradient (cellRawJetConj D) = cellFluxConj (cellGradient D) := rfl

theorem cellL2Norm_conjugate (f : Vec 2 → ℂ) :
    cellL2Norm (fun x => star (f x)) = cellL2Norm f := eLpNorm_star

theorem cellFluxConj_continuous :
    Continuous (fun w : PiLp 2 (fun _ : Fin 2 => ℂ) =>
      WithLp.toLp 2 (fun j => star (w j))) := by fun_prop

theorem cellFluxConj_involutive (F : Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) :
    cellFluxConj (cellFluxConj F) = F := by
  funext x
  apply PiLp.ext
  intro j
  simp only [cellFluxConj, PiLp.toLp_apply, star_star]

theorem cellL2Norm_flux_conjugate (F : Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) :
    cellL2Norm (cellFluxConj F) = cellL2Norm F := by
  by_cases hf : AEStronglyMeasurable F (volume.restrict AVenhance.unitCube)
  · exact eLpNorm_congr_norm_ae
      (cellFluxConj_continuous.comp_aestronglyMeasurable hf) hf
      (Filter.Eventually.of_forall (cellFluxConj_norm F))
  · have hc : ¬ AEStronglyMeasurable (cellFluxConj F) (volume.restrict AVenhance.unitCube) := by
      intro h
      have hh := cellFluxConj_continuous.comp_aestronglyMeasurable h
      change AEStronglyMeasurable (cellFluxConj (cellFluxConj F))
        (volume.restrict AVenhance.unitCube) at hh
      rw [cellFluxConj_involutive] at hh
      exact hf hh
    exact (eLpNorm_of_not_aestronglyMeasurable hc).trans
      (eLpNorm_of_not_aestronglyMeasurable hf).symm

theorem cellL2Norm_gradient_conjugate (D : RawJet2 1 ℂ) :
    cellL2Norm (cellGradient (cellRawJetConj D)) = cellL2Norm (cellGradient D) := by
  rw [cellGradient_conjugate]
  exact cellL2Norm_flux_conjugate _

end AVRegularity.CycleEvolution
end

section
open AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! A periodic weak derivative has zero constant pairing; the zero Bloch shift is the plain derivative. -/

theorem cellComplexPair_one_derivative (j : Fin 2) (z : TorusHk 1 ℂ) :
    cellComplexPair (cellConstantCLM 1) (cellDerivativeCLM j z) = 0 := by
  have he := cellComplexDerivative_skew j cellH1One z
  rw [cellH1One_derivative, cellH1One_value, cellComplexPair_zero_left] at he
  exact (neg_eq_zero.mp he.symm)

theorem cellShiftedDerivative_zero_apply (j : Fin 2) (u : TorusHk 1 ℂ) :
    cellShiftedDerivativeCLM (fun _ => 0) j u = cellDerivativeCLM j u := by
  rw [show (fun _ : Fin 2 => (0 : ℂ)) = 0 from rfl, cellShiftedDerivative_zero]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Filter Homogenization AVRegularity.Sobolev
open scoped Topology
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Subinterval integrability and projected-test convergence of actual raw cell sources. -/

/-- Actual fixed-test scalar/flux forcing is integrable on every subinterval. -/
theorem cellRawSourceFunctional_intervalIntegrable {a b s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) (θ : Fin 2 → ℂ)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube))) (z : TorusHk 1 ℂ) :
    IntervalIntegrable (fun r => cellRawSourceFunctional θ src F r z) volume s t := by
  have hq := cellRawSourceFunctional_memLp θ src F hsrc hF z
  apply intervalIntegrable_iff.mpr
  rw [uIoc_of_le hst]
  exact (hq.integrable (by norm_num)).mono_measure (Measure.restrict_mono
    (Ioc_subset_Icc_self.trans (Icc_subset_Icc hs.1 ht.2)) le_rfl)

/-- Actual raw forcing integrals converge along the Fourier-projected H¹ tests. -/
theorem cellRawSource_integral_fourier_tendsto {a b s t : ℝ}
    (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) (θ : Fin 2 → ℂ)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (z : TorusHk 1 ℂ) :
    Tendsto (fun n => ∫ r in s..t, cellRawSourceFunctional θ src F r (galerkinProj (φ n) z))
      atTop (𝓝 (∫ r in s..t, cellRawSourceFunctional θ src F r z)) := by
  have hsL := cellSourceSlice_memLp (Icc a b) src hsrc
  have hfL (j : Fin 2) := cellSourceSlice_memLp (Icc a b) (fun r x => F r x j)
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).comp_memLp' hF)
  exact cellSource_integral_fourier_tendsto hs ht hst θ _ hsL _ hfL φ hφ z

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Multiplication of a genuine weak Hilbert curve by an actual bounded differentiable phase. -/

theorem CellWeakHilbertCurve.variable_complex_scalar_L2 {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → ComplexCellL2} {slice g : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice g) (c dc : ℝ → ℂ)
    (hc : StrongTimeRegularity a b c dc) (hdc : MemLp dc 2 (volume.restrict (Icc a b))) :
    CellWeakHilbertCurve a b (fun t => cellScalarCLM (c t) (u t))
      (fun t => cellH1Scalar (c t) (slice t))
      (fun t => cellH1Scalar (c t) (g t) + cellPivotDualCLM (cellScalarCLM (dc t) (u t))) := by
  let μ := volume.restrict (Icc a b)
  have hcm := hc.complex_memLp_top hab
  have hcc : ContinuousOn c (Icc a b) := by simpa only [uIcc_of_le hab] using hc.ac.continuousOn
  have hu : MemLp u ⊤ μ := h.trace_memLp_top
  have hg := cellH1Scalar_variable_memLp c hcm g h.dual
  have hp := cellPivotDualCLM.comp_memLp' (cellScalarCLM_variable_memLp_L2_top dc hdc u hu)
  have hdu : MemLp (fun t => cellH1Scalar (c t) (g t) +
      cellPivotDualCLM (cellScalarCLM (dc t) (u t))) 2 μ := by
    simpa only [sub_neg_eq_add, Pi.add_def, Function.comp_def, μ] using hg.sub hp.neg
  refine ⟨cellScalarCLM_variable_continuousOn c hcc u h.trace,
    cellH1Scalar_variable_memLp c hcm slice h.state, hdu, ?_, ?_⟩
  · filter_upwards [h.agrees] with t ht
    rw [ht, cellH1Scalar_value]
  · intro s hs t ht hst z
    exact cellWeakVariableScalar_increment_L2 hab h c dc hc hdc s hs t ht hst z

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization Set
namespace AVRegularity.CycleEvolution

/-! Conjugation preserves the entire integrable raw weak identity at minus conjugate frequency. -/

theorem cellIntegral_star {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℂ) :
    (∫ x, star (f x) ∂μ) = star (∫ x, f x ∂μ) := integral_conj

theorem cellWeakIdentity_conjugate (C : CellCoefficients) (s t : ℝ)
    (u0 u1 ψ : Vec 2 → ℂ) (dψ : Fin 2 → Vec 2 → ℂ)
    (u : ℝ → Vec 2 → ℂ) (du : ℝ → Fin 2 → Vec 2 → ℂ)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (h : CellWeakIdentity C s t u0 u1 ψ dψ u du src F) :
    CellWeakIdentity (cellConjugateCoefficients C) s t (fun x => star (u0 x))
      (fun x => star (u1 x)) (fun x => star (ψ x)) (fun j x => star (dψ j x))
      (fun r x => star (u r x)) (fun r j x => star (du r j x))
      (fun r x => star (src r x)) (fun r => cellFluxConj (F r)) := by
  let μ := volume.restrict AVenhance.unitCube
  let R := fun r => cellLiteralRHS C r (u r) (du r) ψ dψ (src r) (F r)
  let R' := fun r => cellLiteralRHS (cellConjugateCoefficients C) r
    (fun x => star (u r x)) (fun j x => star (du r j x))
    (fun x => star (ψ x)) (fun j x => star (dψ j x))
    (fun x => star (src r x)) (cellFluxConj (F r))
  change Integrable (fun x => u1 x * ψ x) μ ∧ Integrable (fun x => u0 x * ψ x) μ ∧
    (∀ᵐ r ∂volume.restrict (Ioc s t), Integrable (R r) μ) ∧
    Integrable (fun r => ∫ x, R r x ∂μ) (volume.restrict (Ioc s t)) ∧
    (∫ x, u1 x * ψ x ∂μ) - (∫ x, u0 x * ψ x ∂μ) =
      ∫ r in Ioc s t, ∫ x, R r x ∂μ at h
  change Integrable (fun x => star (u1 x) * star (ψ x)) μ ∧
    Integrable (fun x => star (u0 x) * star (ψ x)) μ ∧
    (∀ᵐ r ∂volume.restrict (Ioc s t), Integrable (R' r) μ) ∧
    Integrable (fun r => ∫ x, R' r x ∂μ) (volume.restrict (Ioc s t)) ∧
    (∫ x, star (u1 x) * star (ψ x) ∂μ) -
      (∫ x, star (u0 x) * star (ψ x) ∂μ) = ∫ r in Ioc s t, ∫ x, R' r x ∂μ
  have he (r : ℝ) : R' r = fun x => star (R r x) := by
    funext x
    exact cellLiteralRHS_conjugate C r (u r) (du r) ψ dψ (src r) (F r) x
  have hi : ∀ᵐ r ∂volume.restrict (Ioc s t), Integrable (R' r) μ := by
    filter_upwards [h.2.2.1] with r hr
    rw [he]
    exact Complex.conjCLE.toContinuousLinearMap.integrable_comp hr
  have hint : (fun r => ∫ x, R' r x ∂μ) = fun r => star (∫ x, R r x ∂μ) := by
    funext r
    rw [he]
    exact integral_conj
  have hp (f : Vec 2 → ℂ) : (fun x => star (f x) * star (ψ x)) =
      fun x => star (f x * ψ x) := by
    funext x
    rw [star_mul]
    exact mul_comm _ _
  refine ⟨?_, ?_, hi, ?_, ?_⟩
  · rw [hp u1]
    exact Complex.conjCLE.toContinuousLinearMap.integrable_comp h.1
  · rw [hp u0]
    exact Complex.conjCLE.toContinuousLinearMap.integrable_comp h.2.1
  · rw [hint]
    exact Complex.conjCLE.toContinuousLinearMap.integrable_comp h.2.2.2.1
  · rw [hp u1, hp u0, cellIntegral_star, cellIntegral_star, hint, cellIntegral_star,
      ← star_sub, h.2.2.2.2]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The public energy norm uniformly controls all Hilbert L² trace values. -/

/-- Every raw trace norm is bounded by the finite all-time energy norm. -/
theorem cellRawTrace_norm_le_energy {C : CellCoefficients} {src : ℝ → Vec 2 → ℂ}
    {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} (D : ℝ → RawJet2 1 ℂ)
    (h : IsCellSolution univ C src F D) (he : cellEnergyNorm univ D < ⊤) (t : ℝ) :
    ‖cellRawTrace D t‖ ≤ (cellEnergyNorm univ D).toReal := by
  have ht := cellRawTrace_ae D t (h.2.2.1 t (mem_univ _)).1
  have hnorm := cellL2Norm_eq_of_class _ _ ht
  have hs : cellL2Norm (cellValue D t) ≤ cellEnergyNorm univ D := by
    change _ ≤ (⨆ s ∈ (univ : Set ℝ), cellL2Norm (cellValue D s)) + _
    calc
      _ ≤ ⨆ s ∈ (univ : Set ℝ), cellL2Norm (cellValue D s) :=
        le_iSup_of_le t (le_iSup_of_le (mem_univ _) le_rfl)
      _ ≤ _ := le_add_of_nonneg_right (bot_le : (0 : ENNReal) ≤ _)
  rw [hnorm] at hs
  have hr := ENNReal.toReal_mono he.ne hs
  simpa only [ENNReal.toReal_ofReal (norm_nonneg _)] using hr

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Literal cell mean and bounded scalar multiplier estimates in L2. -/

/-- The literal mean is bounded by the literal cell L2 norm. -/
theorem cellMean_enorm_le_cellL2Norm (f : Vec 2 → ℂ)
    (hf : MemLp f 2 (volume.restrict AVenhance.unitCube)) :
    ‖cellMean f‖ₑ ≤ cellL2Norm f := by
  have he : cellMean (hf.toLp f) = cellMean f := integral_congr_ae hf.coeFn_toLp
  have hb := cellMeanCLM_norm_le (hf.toLp f)
  rw [cellMeanCLM_apply, he] at hb
  rw [cellL2Norm_eq_toLp f hf]
  simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal hb

/-- A bounded measurable scalar multiplier acts boundedly on literal cell L2 representatives. -/
theorem cellL2Norm_mul_le (b f : Vec 2 → ℂ) (B : ℝ)
    (hm : AEStronglyMeasurable (fun x => b x * f x) (volume.restrict AVenhance.unitCube))
    (hb : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ‖b x‖ ≤ B) :
    cellL2Norm (fun x => b x * f x) ≤ ENNReal.ofReal B * cellL2Norm f := by
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul hm _ 2
  filter_upwards [hb] with x hx
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

end AVRegularity.CycleEvolution
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Exact metric dissipation and nonpositive energy production for real Bloch frequencies. -/

theorem cellComplexDiffusionForm_real_diagonal
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    (θ : Fin 2 → ℂ) (hθ : ∀ j, star (θ j) = θ j) (t : ℝ) (u : TorusHk 1 ℂ) :
    (cellComplexDiffusionForm hG θ t u u).re =
      -cellMetricVectorEnergy hG t (fun j => cellShiftedDerivativeCLM θ j u) := by
  have he : (fun j => star (θ j)) = θ := funext hθ
  simp only [cellComplexDiffusionForm, he, cellMetricVectorEnergy, Fin.sum_univ_two,
    Complex.neg_re, Complex.add_re, cellComplexPair_re]

theorem cellComplexGenerator_real_diagonal
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (θ : Fin 2 → ℂ) (hθ : ∀ j, star (θ j) = θ j) (t : ℝ) (u : TorusHk 1 ℂ) :
    (cellComplexGenerator ⟨G, v, θ, 0⟩ hG V hv.1 hb t u u).re =
      -cellMetricVectorEnergy hG t (fun j => cellShiftedDerivativeCLM θ j u) := by
  rw [cellComplexGenerator_decomposition ⟨G, v, θ, 0⟩ hG V hv hb]
  simp only [Pi.zero_apply, cellComplexPair_scalar_left, zero_mul, add_zero,
    Complex.sub_re, cellComplexDiffusionForm_real_diagonal hG θ hθ,
    cellComplexShiftedDriftForm_real_diagonal V hv hb θ hθ, sub_zero]

theorem cellComplexGenerator_real_nonpos
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (θ : Fin 2 → ℂ) (hθ : ∀ j, star (θ j) = θ j) (t : ℝ) (u : TorusHk 1 ℂ) :
    (cellComplexGenerator ⟨G, v, θ, 0⟩ hG V hv.1 hb t u u).re ≤ 0 := by
  rw [cellComplexGenerator_real_diagonal hG hv V hb θ hθ]
  have he := cellMetricVectorEnergy_coercive hG t (fun j => cellShiftedDerivativeCLM θ j u)
  have hp : 0 ≤ (1 / 2 : ℝ) * ∑ j : Fin 2, ‖cellShiftedDerivativeCLM θ j u‖ ^ 2 := by
    positivity
  exact neg_nonpos.mpr (hp.trans he)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Homogeneous Riesz derivatives commute with complex scalars for every actual bounded scalar potential. -/

theorem cellDualDerivative_homogeneous_complex_scalar
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (t : ℝ) (u : TorusHk 1 ℂ) (c : ℂ) :
    cellH1Scalar c (cellDualDerivative C hG V hv hb t u 0 0) =
      cellDualDerivative C hG V hv hb t (cellH1Scalar c u) 0 0 := by
  apply ext_inner_right ℝ
  intro z
  have he : cellDualComplexPair
      (cellH1Scalar c (cellDualDerivative C hG V hv hb t u 0 0)) z =
      cellDualComplexPair (cellDualDerivative C hG V hv hb t (cellH1Scalar c u) 0 0) z := by
    rw [cellDualComplexPair_scalar_left, cellDualComplexPair_actual,
      cellDualComplexPair_actual, cellComplexGenerator_scalar]
    simp [cellComplexSource, cellComplexPair_zero_left]
  simpa only [cellDualComplexPair_re] using congrArg Complex.re he

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CycleEvolution

/-! Actual pointwise multiplier bounds imply actual Hilbert L² class norm bounds. -/

theorem cellL2Class_norm_le_of_ae_le_mul (B : ℝ) (hB : 0 ≤ B) (S u : ComplexCellL2)
    (he : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ‖S x‖ ≤ B * ‖u x‖) :
    ‖S‖ ≤ B * ‖u‖ := by
  have hn := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Lp.memLp S).aestronglyMeasurable he 2
  change cellL2Norm (S : Vec 2 → ℂ) ≤ ENNReal.ofReal B * cellL2Norm (u : Vec 2 → ℂ) at hn
  rw [cellL2Norm_eq_of_class _ S (Filter.Eventually.of_forall (fun _ => rfl)),
    cellL2Norm_eq_of_class _ u (Filter.Eventually.of_forall (fun _ => rfl)), ← ENNReal.ofReal_mul hB] at hn
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hB (norm_nonneg u))).mp hn

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Continuous Hilbert traces of summable families of actual all-time cell solutions. -/

/-- Absolute energy summability supplies a continuous trace for the literal value series. -/
theorem cellSolutionSeries_continuous_trace {J : Type*} [Countable J]
    (C : J → CellCoefficients) (src : J → ℝ → Vec 2 → ℂ)
    (F : J → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D : J → ℝ → RawJet2 1 ℂ)
    (hD : ∀ j, IsCellSolution Set.univ (C j) (src j) (F j) (D j))
    (hs : (∑' j, cellEnergyNorm Set.univ (D j)) < ⊤) :
    Continuous (fun t => ∑' j, cellRawTrace (D j) t) ∧
      ∀ t, ((∑' j, cellRawTrace (D j) t : ComplexCellL2) : Vec 2 → ℂ) =ᵐ[
        volume.restrict AVenhance.unitCube] (fun x => ∑' j, cellValue (D j) t x) ∧
        ‖∑' j, cellRawTrace (D j) t‖ₑ ≤ ∑' j, cellEnergyNorm Set.univ (D j) := by
  have hm j t : MemLp (cellValue (D j) t) 2 (volume.restrict AVenhance.unitCube) :=
    ((hD j).2.2.1 t (Set.mem_univ t)).1
  apply cellContinuousL2Series (fun j => cellValue (D j))
    (fun j => cellRawTrace (D j)) (fun j => cellEnergyNorm Set.univ (D j))
  · intro j
    exact continuousOn_univ.mp (cellRawTrace_continuous Set.univ (D j)
      (fun t _ => hm j t) (hD j).2.2.2.2.1)
  · intro j t
    exact cellRawTrace_ae (D j) t (hm j t)
  · intro j t
    rw [← ofReal_norm, ← cellL2Norm_eq_of_class _ _ (cellRawTrace_ae (D j) t (hm j t))]
    exact cellValue_cellL2Norm_le_energy (D j) t
  · exact hs

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! A bounded actual scalar potential gives the genuine phase-multiplied weak Hilbert trajectory. -/

theorem CellWeakHilbertCurve.multiply_integral_phase {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → ComplexCellL2} {slice g : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice g) (lam : ℝ → ℂ)
    (hlam : MemLp lam ⊤ (volume.restrict (Icc a b))) :
    CellWeakHilbertCurve a b
      (fun t => cellScalarCLM (Complex.exp (∫ r in a..t, lam r)) (u t))
      (fun t => cellH1Scalar (Complex.exp (∫ r in a..t, lam r)) (slice t))
      (fun t => cellH1Scalar (Complex.exp (∫ r in a..t, lam r)) (g t) +
        cellPivotDualCLM (cellScalarCLM (Complex.exp (∫ r in a..t, lam r) * lam t) (u t))) := by
  have hp := complexBoundedPhase_regular hab lam hlam
  exact h.variable_complex_scalar hab _ _ hp.1 hp.2

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Testing the actual unshifted weak equation against one gives exactly the source mean. -/

/-- Diffusion and divergence-free drift annihilate the constant test in the complex equation. -/
theorem cellComplexGenerator_one {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : IsCellMetric G) {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (u : TorusHk 1 ℂ) :
    cellComplexGenerator ⟨G, v, 0, 0⟩ hG V hv.1 hb t u cellH1One = 0 := by
  simp only [cellComplexGenerator, cellShiftedDerivative_zero, Pi.zero_apply, star_zero,
    show (fun _ : Fin 2 => (0 : ℂ)) = 0 from rfl, cellH1One_derivative, cellH1One_value,
    cellComplexPair_zero_right, Finset.sum_const_zero, neg_zero, zero_sub,
    cellScalarCLM, map_zero, zero_apply, cellComplexPair_zero_left, add_zero]
  rw [cellDrift_constant_pair_sum ⟨G, v, 0, 0⟩ hv V hb t u, neg_zero]

/-- A divergence source has zero constant-test pairing, leaving precisely the scalar source mean. -/
theorem cellComplexSource_one (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    cellComplexSource 0 S F cellH1One = cellMean S := by
  simp only [cellComplexSource, Pi.zero_apply, star_zero,
    show (fun _ : Fin 2 => (0 : ℂ)) = 0 from rfl, cellShiftedDerivative_zero,
    cellH1One_derivative, cellH1One_value, cellComplexPair_zero_right,
    Finset.sum_const_zero, sub_zero, cellComplexPair_one]

/-- The actual dual derivative paired with one is the literal scalar forcing mean. -/
theorem cellDualComplexPair_one {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : IsCellMetric G) {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (u : TorusHk 1 ℂ)
    (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    cellDualComplexPair (cellDualDerivative ⟨G, v, 0, 0⟩ hG V hv.1 hb t u S F) cellH1One =
      cellMean S := by
  rw [cellDualComplexPair_actual, cellComplexGenerator_one hG hv,
    cellComplexSource_one, zero_add]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Actual mean-zero weak solutions have a forced spectral energy bound uniform in the drift. -/

/-- The exact mean-zero cell equation retains a π² value gap and half the gradient energy. -/
theorem cellWeakActual_weighted_energy {a b : ℝ} (hab : a ≤ b)
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (S : ℝ → ComplexCellL2) (F : ℝ → Fin 2 → ComplexCellL2)
    (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (hF : ∀ j, MemLp (fun t => F t j) 2 (volume.restrict (Icc a b)))
    (h : CellWeakHilbertCurve a b u slice
      (fun t => cellDualDerivative ⟨G, v, 0, 0⟩ hG V hv.1 hb t (slice t) (S t) (F t)))
    (hm : ∀ t ∈ Icc a b, cellMean (u t) = 0) :
    Real.exp (Real.pi ^ 2 * (b - a)) * ‖u b‖ ^ 2 +
      (∫ t in a..b, Real.exp (Real.pi ^ 2 * (t - a)) *
        ((1 / 2) * ∑ j, ‖cellDerivativeCLM j (slice t)‖ ^ 2)) ≤
      ‖u a‖ ^ 2 + ∫ t in a..b, Real.exp (Real.pi ^ 2 * (t - a)) *
        (‖S t‖ ^ 2 + 8 * ∑ j, ‖F t j‖ ^ 2) := by
  have hsumF := (cellTime_normSq_intervalIntegrable hab (hF 0)).add
    (cellTime_normSq_intervalIntegrable hab (hF 1))
  have hf : IntervalIntegrable (fun t => ‖S t‖ ^ 2 + 8 * ∑ j, ‖F t j‖ ^ 2) volume a b := by
    simpa only [Fin.sum_univ_two, Pi.add_apply] using
      (cellTime_normSq_intervalIntegrable hab hS).add (hsumF.const_mul 8)
  have hd := (cellTime_gradientSq_intervalIntegrable hab slice h.state).const_mul (1 / 2)
  apply (h.energy_strongTime hab).scalar_weighted_bound hab (Real.pi ^ 2) _ _ hf hd
  filter_upwards [h.agrees, ae_restrict_mem measurableSet_Icc] with t ht hti
  have hmean := hm t hti
  rw [ht] at hmean
  rw [cellDualDerivative_pairing, ht]
  exact cellUnshifted_source_energy_bound hG hv V hb t (slice t) hmean (S t) (F t)

end AVRegularity.CycleEvolution
end
