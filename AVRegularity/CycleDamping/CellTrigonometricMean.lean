-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleEvolution.CellTimeMetricDriftCLM
import AVRegularity.CycleDamping.ReferenceTimeEquation
public import AVRegularity.CycleDamping.CellShiftedGap
public import AVRegularity.CycleEvolution.CellConjugateClass
import AVRegularity.Construction.Scales.Times
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.CoupledEnergy.Galerkin.PlainVariationalEnergy
import AVRegularity.CycleReference.ChartTestTransport
import AVenhance.Infra.Classical.GalerkinGenerator
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

@[expose] public noncomputable section

section
open MeasureTheory Homogenization Filter Topology
namespace AVRegularity.CycleDamping

/-! Continuous scalar time amplitudes give the literal continuous cell L² trace. -/

theorem scalar_cell_trace_continuous (a : ℝ → ℝ) (ha : Continuous a)
    (f : Vec 2 → ℂ) (hf : MemLp f 2 (volume.restrict AVenhance.unitCube)) :
    ∀ t₀ : ℝ, Tendsto (fun t => ∫⁻ x in AVenhance.unitCube,
      ‖(a t : ℂ) * f x - (a t₀ : ℂ) * f x‖ₑ ^ 2) (𝓝 t₀) (𝓝 0) := by
  let u : ℝ → CycleEvolution.ComplexCellL2 := fun t => a t • hf.toLp f
  have hu : Continuous u := ha.smul continuous_const
  have he (t : ℝ) : (u t : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => (a t : ℂ) * f x := by
    filter_upwards [Lp.coeFn_smul (a t) (hf.toLp f), hf.coeFn_toLp] with x hx hf'
    rw [hx]
    simp only [Pi.smul_apply, Complex.real_smul, hf']
  have hc := CycleEvolution.cellRaw_trace_continuous Set.univ u hu.continuousOn
    (fun t x => (a t : ℂ) * f x) (fun t _ => he t)
  intro t₀
  simpa only [nhdsWithin_univ] using hc t₀ (Set.mem_univ t₀)

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CycleDamping

/-! The weak time identity for a fixed spatial mode with a C¹ amplitude. -/

theorem scalar_mode_time_integral (a : ℝ → ℝ) (ha : ContDiff ℝ 1 a)
    (f ψ : Vec 2 → ℂ) {s t : ℝ} (hst : s ≤ t) :
    (∫ x in AVenhance.unitCube, (a t : ℂ) * f x * ψ x) -
      (∫ x in AVenhance.unitCube, (a s : ℂ) * f x * ψ x) =
    ∫ τ in Set.Ioc s t, ∫ x in AVenhance.unitCube,
      ((deriv a τ : ℝ) : ℂ) * f x * ψ x := by
  have had := contDiff_one_iff_deriv.mp ha
  let c : ℂ := ∫ x in AVenhance.unitCube, f x * ψ x
  have he (r : ℝ) : (∫ x in AVenhance.unitCube, (a r : ℂ) * f x * ψ x) =
      (a r : ℂ) * c := by simp only [mul_assoc, integral_const_mul, c]
  have hd (r : ℝ) : (∫ x in AVenhance.unitCube, ((deriv a r : ℝ) : ℂ) * f x * ψ x) =
      ((deriv a r : ℝ) : ℂ) * c := by simp only [mul_assoc, integral_const_mul, c]
  simp_rw [he, hd]
  have hh (r : ℝ) : HasDerivAt (fun u => (a u : ℂ) * c)
      (((deriv a r : ℝ) : ℂ) * c) r :=
    ((had.1 r).hasDerivAt.ofReal_comp).mul_const c
  have hc : Continuous (fun r => ((deriv a r : ℝ) : ℂ) * c) :=
    (Complex.continuous_ofReal.comp had.2).mul continuous_const
  exact ((intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hh r)
    (hc.intervalIntegrable s t)).symm.trans (intervalIntegral.integral_of_le hst))

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance.Infra.Torus
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping

/-! Brillouin dissipation controls the mean-free part of every Fourier approximant. -/

theorem projected_meanFree_shifted_gap (θ : Vec 2) (hθ : ∀ j, |θ j| ≤ Real.pi)
    (u : TorusHk 1 ℂ) (N : ℕ) :
    Real.pi ^ 2 * ‖cellQ0CLM (torusHkValueCLM (galerkinProj N u))‖ ^ 2 ≤
      4 * ∑ j : Fin 2, ‖cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j (galerkinProj N u)‖ ^ 2 := by
  let p := galerkinProj N u
  let q := smoothFourierJet (L := 1) N u (valueIndex2 1)
  have hq : ContDiff ℝ 1 q := (smoothFourierJet_contDiff N u _).of_le (by simp)
  have hp : AVenhance.IsZ2Periodic q := smoothFourierJet_periodic N u _
  have hq0 : ContDiff ℝ 1 (cellQ0 q) := hq.sub contDiff_const
  have hp0 : AVenhance.IsZ2Periodic (cellQ0 q) := by
    intro n x; dsimp only [cellQ0]; rw [hp n x]
  have hval : torusHkValueCLM p =ᵐ[volume.restrict AVenhance.unitCube] q :=
    galerkinProj_jet_ae_smooth N u (valueIndex2 1)
  have hm : cellMean (torusHkValueCLM p) = cellMean q := integral_congr_ae hval
  have hQ : cellQ0CLM (torusHkValueCLM p) =ᵐ[volume.restrict AVenhance.unitCube] cellQ0 q := by
    filter_upwards [cellQ0CLM_ae (torusHkValueCLM p), hval] with x hx hv
    rw [hx]; dsimp only [cellQ0]; rw [hv, hm]
  have hz : (∫ x in unitCell 2, cellQ0 q x) = 0 := by
    rw [integral_unitCell_eq_unitCube]
    exact cellQ0_mean (smoothFourierJet_memLp (L := 1) N u (valueIndex2 1))
  have hs (j : Fin 2) : cellQ0CLM (cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j p) =ᵐ[
      volume.restrict AVenhance.unitCube] smoothShiftedDerivative θ j (cellQ0 q) := by
    filter_upwards [cellQ0CLM_ae (cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j p),
      projected_shifted_derivative_ae θ u N j] with x hx hd
    rw [hx]; dsimp only [cellQ0]
    rw [hd, cellShiftedDerivative_mean, hm]
    dsimp only [smoothShiftedDerivative, coordDeriv, cellQ0]
    have hdq : fderiv ℝ (cellQ0 q) x = fderiv ℝ q x := by
      change fderiv ℝ (fun y => q y - cellMean q) x = fderiv ℝ q x
      exact fderiv_sub_const _
    rw [hdq]
    dsimp only [q]
    ring
  have hl : (∫ x in unitCell 2, ‖cellQ0 q x‖ ^ 2) =
      ‖cellQ0CLM (torusHkValueCLM p)‖ ^ 2 := by
    rw [integral_unitCell_eq_unitCube, ← cellL2_norm_sq_integral]
    exact integral_congr_ae (hQ.mono (fun x hx => congrArg (fun z : ℂ => ‖z‖ ^ 2) hx.symm))
  have he (j : Fin 2) : (∫ x in unitCell 2, ‖smoothShiftedDerivative θ j (cellQ0 q) x‖ ^ 2) =
      ‖cellQ0CLM (cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j p)‖ ^ 2 := by
    rw [integral_unitCell_eq_unitCube, ← cellL2_norm_sq_integral]
    exact integral_congr_ae ((hs j).mono (fun x hx => congrArg (fun z : ℂ => ‖z‖ ^ 2) hx.symm))
  have hg := smoothShiftedGradient_meanZero_gap θ hθ hq0 hp0 hz
  rw [hl] at hg
  simp_rw [he] at hg
  apply hg.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hb := cellQ0CLM_norm_le (cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j p)
  nlinarith only [hb, norm_nonneg (cellQ0CLM (cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j p)),
    norm_nonneg (cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j p)]

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping

/-! Mean-free shifted-gradient control for arbitrary weak H¹ cell fields. -/

theorem cellH1_meanFree_shifted_gap (θ : Vec 2) (hθ : ∀ j, |θ j| ≤ Real.pi)
    (u : TorusHk 1 ℂ) :
    Real.pi ^ 2 * ‖cellQ0CLM (torusHkValueCLM u)‖ ^ 2 ≤
      4 * ∑ j : Fin 2, ‖cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j u‖ ^ 2 := by
  have hp := galerkinProj_tendsto u
  have hl : Tendsto (fun N => Real.pi ^ 2 *
      ‖cellQ0CLM (torusHkValueCLM (galerkinProj N u))‖ ^ 2) atTop
      (𝓝 (Real.pi ^ 2 * ‖cellQ0CLM (torusHkValueCLM u)‖ ^ 2)) := tendsto_const_nhds.mul
    (((cellQ0CLM.comp torusHkValueCLM).continuous.norm.pow 2).continuousAt.tendsto.comp hp)
  have hr : Tendsto (fun N => 4 * ∑ j : Fin 2,
      ‖cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j (galerkinProj N u)‖ ^ 2) atTop
      (𝓝 (4 * ∑ j : Fin 2, ‖cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j u‖ ^ 2)) := by
    apply tendsto_const_nhds.mul
    apply tendsto_finsetSum
    intro j _
    exact (((cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j).continuous.norm.pow 2).continuousAt.tendsto.comp hp)
  exact le_of_tendsto_of_tendsto' hl hr (projected_meanFree_shifted_gap θ hθ u)

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleDamping

/-! Exact homogeneous real-shift dissipation on the actual complex cell carrier. -/

theorem real_shift_generator_diagonal
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (θ : Vec 2) (t : ℝ) (u : TorusHk 1 ℂ) :
    (cellComplexGenerator ⟨G, v, fun j => (θ j : ℂ), 0⟩ hG V hv.1 hb t u u).re =
      -metricVectorDissipation hG t
        (fun j => cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j u) := by
  have hc : (fun j => star (θ j : ℂ)) = (fun j => (θ j : ℂ)) := by
    funext j; exact Complex.conj_ofReal (θ j)
  have hz : cellScalarCLM (0 : ℂ) (torusHkValueCLM u) = 0 := by
    change (0 : ℂ) • torusHkValueCLM u = 0
    exact zero_smul _ _
  rw [cellComplexGenerator]
  change (-(∑ j : Fin 2, ∑ k : Fin 2, cellComplexPair
      (cellMetricEntryCLM hG t j k (cellShiftedDerivativeCLM (fun i => (θ i : ℂ)) j u))
      (cellShiftedDerivativeCLM (fun i => star (θ i : ℂ)) k u)) -
    (∑ j : Fin 2, cellComplexPair
      (cellDriftEntryCLM ⟨G, v, fun i => (θ i : ℂ), 0⟩ V hv.1 hb t j
        (cellShiftedDerivativeCLM (fun i => (θ i : ℂ)) j u)) (torusHkValueCLM u)) +
    cellComplexPair (cellScalarCLM 0 (torusHkValueCLM u)) (torusHkValueCLM u)).re = _
  rw [hc, hz, cellComplexPair_zero_left, add_zero, Complex.sub_re,
    real_shift_drift_energy_zero G v hv V hb θ t u, sub_zero]
  simp only [metricVectorDissipation, Fin.sum_univ_two, Complex.neg_re,
    Complex.add_re, cellComplexPair_re]

theorem real_shift_dual_production
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (θ : Vec 2) (t : ℝ) (u : TorusHk 1 ℂ) :
    2 * inner ℝ
      (cellDualDerivative ⟨G, v, fun j => (θ j : ℂ), 0⟩ hG V hv.1 hb t u 0 0) u +
      (∑ j : Fin 2, ‖cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j u‖ ^ 2) ≤ 0 := by
  have hh := congrArg Complex.re
    (homogeneous_dual_complex_generator ⟨G, v, fun j => (θ j : ℂ), 0⟩ hG V hv.1 hb t u u)
  rw [cellDualComplexPair_re, real_shift_generator_diagonal hG v hv V hb θ t u] at hh
  have he := metricVectorDissipation_coercive hG t
    (fun j => cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j u)
  linarith only [hh, he]

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CycleDamping

/-! The exact physical-to-cell change of variables in integrated reference-flux coercivity. -/

/-- Admissibility gives cell-time integrated coercivity for the normalized reference flux. -/
theorem admissible_cell_flux_coercivity {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    {ν B Θ θ ta T : ℝ} (hΛ : 1 ≤ Λ) (hν : 0 < ν) (hB : 0 < B)
    (hI : IsOCAdmissibleInterval α q Λ ζ m ν B Θ θ ta T) (w : Vec 2) :
    (1 - Real.exp (-2)) / 288 * (T / ocEll q Λ m ν ^ 2) * vecDot w w ≤
      ∫ t in (ta / ocEll q Λ m ν ^ 2)..((ta + T) / ocEll q Λ m ν ^ 2),
        vecDot w ((ocRefFlux α q Λ ζ m ν (ocEll q Λ m ν ^ 2 * t)).mulVec w) / B := by
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  have hL : 0 < ocEll q Λ m ν ^ 2 := by rw [CycleReference.ocEll_sq_eq hν]; positivity
  have ha : ocEll q Λ m ν ^ 2 * (ta / ocEll q Λ m ν ^ 2) = ta := mul_div_cancel₀ ta hL.ne'
  have hb : ocEll q Λ m ν ^ 2 * ((ta + T) / ocEll q Λ m ν ^ 2) = ta + T := mul_div_cancel₀ (ta + T) hL.ne'
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_comp_mul_left (fun t =>
      vecDot w ((ocRefFlux α q Λ ζ m ν t).mulVec w)) hL.ne', ha, hb]
  simp only [smul_eq_mul]
  have hs := div_le_div_of_nonneg_right (hI.2.2.1 w) (mul_pos hB hL).le
  convert hs using 1 <;> field_simp

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleDamping

/-! The literal mean equation for a real Bloch shift and a spatially constant metric. -/

theorem shifted_one_value (θ : Fin 2 → ℂ) (j : Fin 2) :
    cellShiftedDerivativeCLM θ j cellH1One = cellScalarCLM (Complex.I * θ j) (cellConstantCLM 1) := by
  change cellDerivativeCLM j cellH1One + cellScalarCLM (Complex.I * θ j)
    (torusHkValueCLM cellH1One) = _
  rw [cellH1One_derivative, cellH1One_value, zero_add]

theorem real_shift_mean_generator
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (θ : Vec 2) (t : ℝ) (u : TorusHk 1 ℂ) :
    cellComplexGenerator ⟨fun s _ => G s, v, fun j => (θ j : ℂ), 0⟩ hG V hv.1 hb t u cellH1One =
      -(∑ j : Fin 2, ∑ k : Fin 2, (θ k : ℂ) * (G t j k : ℂ) * (θ j : ℂ)) *
        cellMean (torusHkValueCLM u) -
      Complex.I * (∑ j : Fin 2, (θ j : ℂ) * cellMean
        (cellDriftEntryCLM ⟨fun s _ => G s, v, 0, 0⟩ V hv.1 hb t j (torusHkValueCLM u))) := by
  have hs (j : Fin 2) : cellComplexPair
      (cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j u) (cellConstantCLM 1) =
      Complex.I * (θ j : ℂ) * cellMean (torusHkValueCLM u) := by
    change cellComplexPair (cellDerivativeCLM j u +
      cellScalarCLM (Complex.I * (θ j : ℂ)) (torusHkValueCLM u)) (cellConstantCLM 1) = _
    rw [pair_add_left, pair_scalar_left, cellComplexPair_one,
      cellComplexPair_one, cellDerivative_mean_zero, zero_add]
  have hchange (j : Fin 2) (z : ComplexCellL2) :
      cellDriftEntryCLM ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ V hv.1 hb t j z =
        cellDriftEntryCLM ⟨fun s _ => G s, v, 0, 0⟩ V hv.1 hb t j z := by
    apply Lp.ext
    exact (cellDriftEntryCLM_ae _ V hv.1 hb t j z).trans
      (cellDriftEntryCLM_ae _ V hv.1 hb t j z).symm
  have hd (j : Fin 2) : cellComplexPair
      (cellDriftEntryCLM ⟨fun s _ => G s, v, fun k => (θ k : ℂ), 0⟩ V hv.1 hb t j
        (cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j u)) (cellConstantCLM 1) =
      cellComplexPair
        (cellDriftEntryCLM ⟨fun s _ => G s, v, 0, 0⟩ V hv.1 hb t j (cellDerivativeCLM j u))
        (cellConstantCLM 1) + Complex.I * (θ j : ℂ) * cellMean
        (cellDriftEntryCLM ⟨fun s _ => G s, v, 0, 0⟩ V hv.1 hb t j (torusHkValueCLM u)) := by
    change cellComplexPair (cellDriftEntryCLM _ V hv.1 hb t j
      (cellDerivativeCLM j u + cellScalarCLM (Complex.I * (θ j : ℂ)) (torusHkValueCLM u))) _ = _
    rw [map_add, drift_entry_scalar, pair_add_left, pair_scalar_left]
    simp only [cellComplexPair_one, hchange]
  have hz := cellDrift_complex_constant_zero (fun s _ => G s) v hv V hb t u
  rw [cellComplexGenerator]
  simp only [cellH1One_value, shifted_one_value, frozen_metric_entry_scalar,
    pair_scalar_right, pair_scalar_left, hs, hd, map_mul, Complex.star_def,
    Complex.conj_I, Complex.conj_ofReal, Pi.zero_apply, zero_mul, add_zero]
  simp only [Fin.sum_univ_two] at hz ⊢
  linear_combination (norm := skip) -hz
  ring_nf
  simp only [Complex.I_sq]
  ring

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CycleDamping

/-! Actual normalized reference-flux quadratic forms are integrable on every cell window. -/

theorem normalized_refFlux_entry_intervalIntegrable {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (B : ℝ) (i j : Fin 2) (a b : ℝ) :
    IntervalIntegrable (fun t => ocRefFlux α q Λ ζ m ν (ocEll q Λ m ν ^ 2 * t) i j / B)
      volume a b := by
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  have hL : ocEll q Λ m ν ^ 2 ≠ 0 := by
    rw [CycleReference.ocEll_sq_eq hν]
    positivity
  have hh := (CycleReference.refFlux_entry_intervalIntegrable (α := α) (q := q) (m := m) hΛ hζ hν i j
    (ocEll q Λ m ν ^ 2 * a) (ocEll q Λ m ν ^ 2 * b)).comp_mul_left
      (c := ocEll q Λ m ν ^ 2)
  have hi : IntervalIntegrable (fun t =>
      ocRefFlux α q Λ ζ m ν (ocEll q Λ m ν ^ 2 * t) i j) volume a b := by
    simpa only [mul_div_cancel_left₀ _ hL] using hh
  exact hi.div_const B

theorem normalized_refFlux_quadratic_intervalIntegrable {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (B : ℝ) (x : Vec 2) (a b : ℝ) :
    IntervalIntegrable (fun t => vecDot x
      ((ocRefFlux α q Λ ζ m ν (ocEll q Λ m ν ^ 2 * t)).mulVec x) / B) volume a b := by
  have hi (i j : Fin 2) := normalized_refFlux_entry_intervalIntegrable
    (α := α) (q := q) (m := m) hΛ hζ hν (1 : ℝ) i j a b
  simp only [div_one] at hi
  have hh := (((hi 0 0).mul_const (x 0)).add ((hi 0 1).mul_const (x 1))).const_mul (x 0)
  have hh' := (((hi 1 0).mul_const (x 0)).add ((hi 1 1).mul_const (x 1))).const_mul (x 1)
  simpa only [vecDot, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using (hh.add hh').div_const B

end AVRegularity.CycleDamping
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping

/-! Coercive real-shift energy for genuine weak-time cell trajectories. -/

theorem real_shift_weak_energy {a b : ℝ} (hab : a ≤ b)
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2)
    {u : ℝ → ComplexCellL2} {slice : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice (fun t =>
      cellDualDerivative ⟨G, v, fun j => (θ j : ℂ), 0⟩ hG V hv.1 hb t (slice t) 0 0)) :
    ‖u b‖ ^ 2 + (∫ t in a..b,
      ∑ j : Fin 2, ‖cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j (slice t)‖ ^ 2) ≤ ‖u a‖ ^ 2 := by
  have he := h.energy_increment hab
  have hP := h.production_intervalIntegrable hab
  have hi (j : Fin 2) : IntervalIntegrable
      (fun t => ‖cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j (slice t)‖ ^ 2) volume a b := by
    simpa only [Function.comp_def] using cellTime_normSq_intervalIntegrable hab
      ((cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j).comp_memLp' h.state)
  have hDs : IntervalIntegrable (fun t => ∑ j : Fin 2,
      ‖cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j (slice t)‖ ^ 2) volume a b := by
    simpa only [Fin.sum_univ_two] using (hi 0).add (hi 1)
  have hz : (∫ t in a..b, 2 * inner ℝ
      (cellDualDerivative ⟨G, v, fun j => (θ j : ℂ), 0⟩ hG V hv.1 hb t (slice t) 0 0) (slice t) +
      (∑ j : Fin 2, ‖cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j (slice t)‖ ^ 2)) ≤ 0 := by
    rw [intervalIntegral.integral_of_le hab]
    apply integral_nonpos_of_ae
    exact Filter.Eventually.of_forall (fun t => real_shift_dual_production hG v hv V hb θ t (slice t))
  rw [intervalIntegral.integral_add hP hDs] at hz
  linarith only [he, hz]

theorem real_shift_weak_contraction {a b : ℝ} (hab : a ≤ b)
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2)
    {u : ℝ → ComplexCellL2} {slice : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice (fun t =>
      cellDualDerivative ⟨G, v, fun j => (θ j : ℂ), 0⟩ hG V hv.1 hb t (slice t) 0 0)) :
    ‖u b‖ ≤ ‖u a‖ := by
  have he := real_shift_weak_energy hab hG v hv V hb θ h
  have hp : 0 ≤ ∫ t in a..b, ∑ j : Fin 2,
      ‖cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j (slice t)‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun t _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  nlinarith only [he, hp, norm_nonneg (u a), norm_nonneg (u b)]

/-! Monotonicity of the actual homogeneous real-shift trace on every subinterval. -/

theorem real_shift_weak_norm_antitone {a b : ℝ}
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2)
    {u : ℝ → ComplexCellL2} {slice : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice (fun t =>
      cellDualDerivative ⟨G, v, fun j => (θ j : ℂ), 0⟩ hG V hv.1 hb t (slice t) 0 0)) :
    AntitoneOn (fun t => ‖u t‖) (Icc a b) := by
  intro s hs t ht hst
  exact real_shift_weak_contraction hst hG v hv V hb θ
    (h.mono (Icc_subset_Icc hs.1 ht.2))

end AVRegularity.CycleDamping
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleDamping

/-! Physical-time norm monotonicity and half-drop transport for the actual weak trace. -/

theorem ofReal_half_mul (x : ℝ) :
    ENNReal.ofReal ((1 / 2 : ℝ) * x) = (1 / 2 : ℝ≥0∞) * ENNReal.ofReal x := by
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

theorem physical_norm_antitone (L a b : ℝ) (hL : 0 < L) (u : ℝ → ComplexCellL2)
    (h : AntitoneOn (fun t => ‖u t‖) (Icc (a / L) (b / L))) :
    AntitoneOn (fun t => ENNReal.ofReal ‖u (t / L)‖) (Icc a b) := by
  intro s hs t ht hst
  apply ENNReal.ofReal_le_ofReal
  exact h ⟨div_le_div_of_nonneg_right hs.1 hL.le, div_le_div_of_nonneg_right hs.2 hL.le⟩
    ⟨div_le_div_of_nonneg_right ht.1 hL.le, div_le_div_of_nonneg_right ht.2 hL.le⟩
    (div_le_div_of_nonneg_right hst hL.le)

theorem scaled_mark_interval_subset (L a b x d : ℝ) (hL : 0 < L)
    (hx : a ≤ x) (hxb : x + d * L ≤ b) :
    Icc (x / L) ((x + d * L) / L) ⊆ Icc (a / L) (b / L) :=
  Icc_subset_Icc (div_le_div_of_nonneg_right hx hL.le)
    (div_le_div_of_nonneg_right hxb hL.le)

theorem scaled_mark_length (L x d : ℝ) (hL : 0 < L) :
    (x + d * L) / L - x / L = d := by field_simp; ring

theorem scaled_mark_inside_core (L x d ca cb : ℝ) (hL : 0 < L)
    (hlo : ca ≤ x) (hhi : x + d * L ≤ cb) :
    ∀ t ∈ Icc (x / L) ((x + d * L) / L), L * t ∈ Icc ca cb := by
  intro t ht
  have ha := (div_le_iff₀ hL).mp ht.1
  have hb := (le_div_iff₀ hL).mp ht.2
  constructor <;> linarith only [hlo, hhi, ha, hb]

end AVRegularity.CycleDamping
end

section
open Homogenization
namespace AVRegularity.CycleDamping

/-! Renewal block admissibility from the actual pulse-length condition. -/

/-- Long pulses make every renewal block admissible for the prescribed mark length. -/
theorem renewal_block_admissible_of_long_pulses {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (Θ θ : ℝ) (hΘ : 1 ≤ Θ) (hθ : 0 < θ) (hΘθ : 3 * θ ≤ Θ)
    (hlong : Θ ≤ ocTau α q Λ m / ocEll q Λ m ν ^ 2) (l : ℤ) :
    IsOCAdmissibleInterval α q Λ ζ m ν (ocMeanFlux α q Λ ζ m ν) Θ θ
      (((l : ℝ) - 1 / 2) * ocTauPP α q Λ m) (ocTauPP α q Λ m) := by
  let L := ocEll q Λ m ν ^ 2
  let h := ocTauPP α q Λ m
  let τ := ocTau α q Λ m
  let a := ((l : ℝ) - 1 / 2) * h
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  have hL : 0 < L := by dsimp [L]; rw [CycleReference.ocEll_sq_eq hν]; positivity
  have hh : 0 < h := AVRegularity.Construction.Stream.ocTauPP_pos (α := α) (q := q) (m := m) hΛ
  have hτ : 0 < τ := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
  have hB : 0 < ocMeanFlux α q Λ ζ m ν :=
    hν.trans_le (CycleReference.meanFlux_ge_input hΛ hζ hν)
  have hτh : τ ≤ h := by
    have hLn : 1 ≤ ocL α q Λ m := by unfold ocL; omega
    have hLr : 1 ≤ (ocL α q Λ m : ℝ) := by exact_mod_cast hLn
    have hscale : (ocL α q Λ m : ℝ) ^ 2 * τ = h := by
      dsimp [τ, h]
      rw [ocTau]
      field_simp
    rw [← hscale]
    have hs : 1 ≤ (ocL α q Λ m : ℝ) ^ 2 := by nlinarith only [hLr]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hs hτ.le
  have hrelax : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m := by
    have hr := ocMu_cell_rate (q := q) (m := m) hΛ hν
    have hid : ocMu q Λ m ν * τ = 4 * Real.pi ^ 2 * (τ / L) := by
      calc
        _ = (ocMu q Λ m ν * L) * (τ / L) := by field_simp
        _ = _ := by rw [hr]
    have hratio : 1 ≤ τ / L := hΘ.trans hlong
    have hgap : 6 ≤ 4 * Real.pi ^ 2 := by nlinarith only [Real.pi_gt_three]
    rw [hid]
    exact hgap.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 4 * Real.pi ^ 2))
  have hend : a + h = ((l : ℝ) + 1 / 2) * h := by dsimp [a]; ring
  refine ⟨hlong, hlong.trans (div_le_div_of_nonneg_right hτh hL.le), ?_, ?_⟩
  · intro w
    have hb := renewal_block_flux_coercivity (α := α) (q := q) (m := m) hΛ hζ hν hrelax l w
    change _ ≤ ∫ t in a..(a + h), _
    rw [hend]
    refine le_trans ?_ hb
    have hn : 0 ≤ ocMeanFlux α q Λ ζ m ν * h * vecDot w w := by
      apply mul_nonneg (mul_nonneg hB.le hh.le)
      simp only [vecDot, Fin.sum_univ_two]
      nlinarith only [sq_nonneg (w 0), sq_nonneg (w 1)]
    have hconst : (1 - Real.exp (-2)) / 288 ≤ (1 - Real.exp (-2)) / 96 := by
      have hc := CycleReference.core_coercivity_constant_range.1
      linarith only [hc]
    convert mul_le_mul_of_nonneg_right hconst hn using 1 <;> ring
  · intro j
    let r : ℤ := if j = 0 then 3 else 1
    have hr : r = 1 ∨ r = 3 := by dsimp [r]; split_ifs <;> simp
    have h3 : 3 * (θ * L) ≤ τ := by
      have ht := (le_div_iff₀ hL).mp (hΘθ.trans hlong)
      linarith only [ht]
    obtain ⟨marks, hn, hm, hs⟩ := complete_core_marks (α := α) (q := q) (m := m)
      hΛ l r hr (θ * L) (mul_pos hθ hL) h3
    refine ⟨marks, ?_, ?_, hs⟩
    · refine le_trans ?_ hn
      change (1 - Real.exp (-2)) / 288 * (h / L) / θ ≤ h / (96 * (θ * L))
      have hconst : (1 - Real.exp (-2)) / 288 ≤ (1 / 96 : ℝ) := by
        have hp := Real.exp_pos (-2)
        linarith only [hp]
      convert mul_le_mul_of_nonneg_right hconst (div_nonneg hh.le (mul_pos hθ hL).le)
        using 1 <;> ring
    · intro x hx
      obtain ⟨hblock, k, hk, hcore, hlo, hhi⟩ := hm x hx
      refine ⟨hblock.1, ?_, k, hk, ?_, hlo, hhi⟩
      · change x + θ * L ≤ a + h
        rw [hend]
        exact hblock.2
      · rw [hcore.2.1]
        exact hcore

end AVRegularity.CycleDamping
end

section
open Filter Topology
namespace AVRegularity.CycleDamping

/-! Uniform eventual admissibility of every renewal block along every band chain. -/

/-- The level threshold is independent of terminal level, band point, and block label. -/
theorem bandChain_eventual_block_admissibility {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ Θ θ : ℝ, 1 ≤ Θ → 0 < θ → 3 * θ ≤ Θ →
      ∃ mStar : ℕ, ∀ (M : ℕ) (κ : ℕ → ℝ), IsOCBandChain α q Λ ζ M κ →
        ∀ m : ℕ, 2 ≤ m → mStar ≤ m → m ≤ M →
        ∀ ν B : ℝ, κ m = ν → κ (m - 1) = B → ∀ l : ℤ,
          IsOCAdmissibleInterval α q Λ ζ m ν B Θ θ
            (((l : ℝ) - 1 / 2) * ocTauPP α q Λ m) (ocTauPP α q Λ m) := by
  obtain ⟨C, hC, Λ₀, hΛ₀, hscale⟩ :=
    CycleReference.bandChain_memory_scale hα0 hα1 hs0 hs1 hq hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ Θ θ hΘ hθ hΘθ
  have h128 := hΛ₀.trans hΛ
  have hΛ1 : 1 ≤ Λ := by omega
  have hΘp : 0 < Θ := by linarith only [hΘ]
  have hp : 0 < 4 * ocDelta α q := mul_pos (by norm_num)
    (AVRegularity.Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq).2.1
  have ht : Tendsto (fun m : ℕ => C * ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q))
      atTop (𝓝 0) := by
    have he := (CycleReference.epsilon_parent_tendsto_zero hq.1 h128).rpow_const (Or.inr hp.le)
    simpa only [Real.zero_rpow hp.ne', mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C)).mul he
  have hevent : ∀ᶠ m : ℕ in atTop,
      C * ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q) ≤ 1 / Θ :=
    ht.eventually (eventually_le_nhds (one_div_pos.mpr hΘp))
  obtain ⟨mStar, hStar⟩ := eventually_atTop.1 hevent
  refine ⟨mStar, ?_⟩
  intro M κ hκ m hm hstart hmM ν B hνeq hBeq l
  have hν : 0 < ν := hνeq ▸ CycleReference.bandChain_pos hΛ1 hζ hκ hmM
  have hBmean : B = ocMeanFlux α q Λ ζ m ν := by
    rw [← hBeq, ← hνeq]
    exact hκ.2 m (by omega) hmM
  have hsmall := (hscale Λ hΛ M (by omega) κ hκ m hm hmM).1.trans (hStar m hstart)
  rw [hνeq] at hsmall
  have hτ := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ1
  have hlen : 0 < ocEll q Λ m ν ^ 2 := by
    rw [CycleReference.ocEll_sq_eq hν]
    have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ1
    positivity
  have hlong : Θ ≤ ocTau α q Λ m / ocEll q Λ m ν ^ 2 := by
    apply (le_div_iff₀ hlen).2
    have hi := (div_le_div_iff₀ hτ hΘp).mp hsmall
    simpa only [one_mul, mul_one, mul_comm] using hi
  rw [hBmean]
  exact renewal_block_admissible_of_long_pulses hΛ1 hζ hν Θ θ hΘ hθ hΘθ hlong l

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational AVenhance.Infra.Classical
namespace AVRegularity.CycleDamping

/-! Moving the gradient of a smooth periodic scalar onto an arbitrary weak H¹ test. -/

def complexSmoothScalarH1 (q : Vec 2 → ℝ) (hq : ContDiff ℝ (↑(⊤ : ℕ∞)) q)
    (hp : AVenhance.IsZ2Periodic q) : TorusHk 1 ℂ :=
  TorusHkFunction.toHk ⟨mapRawJet Complex.ofRealCLM (cellSmoothScalarJet q),
    mapRawJet_hasPeriodicWeakJet Complex.ofRealCLM _ (cellSmoothScalarJet_periodicWeak q hq hp)⟩

theorem complexSmoothScalarH1_ae (q : Vec 2 → ℝ) (hq : ContDiff ℝ (↑(⊤ : ℕ∞)) q)
    (hp : AVenhance.IsZ2Periodic q) (a : JetIndex2 1) :
    (complexSmoothScalarH1 q hq hp).val a =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => ((cellSmoothScalarJet q a x : ℝ) : ℂ) :=
  torusJetToL2_ae _ _ a

theorem smooth_partial_weak_ibp (q : Vec 2 → ℝ) (hq : ContDiff ℝ (↑(⊤ : ℕ∞)) q)
    (hp : AVenhance.IsZ2Periodic q) (ψ : TorusHkFunction 1 ℂ) (i : Fin 2) :
    (∫ x in AVenhance.unitCube,
      ((fderiv ℝ q x (basisVec i) : ℝ) : ℂ) * ψ.jet ⟨⟨1, by decide⟩, fun _ => i⟩ x) =
      -∫ x in AVenhance.unitCube,
        ((fderiv ℝ (fun z => fderiv ℝ q z (basisVec i)) x (basisVec i) : ℝ) : ℂ) *
          ψ.jet (valueIndex2 1) x := by
  let dq : Vec 2 → ℝ := fun x => fderiv ℝ q x (basisVec i)
  have hdq : ContDiff ℝ (↑(⊤ : ℕ∞)) dq :=
    GalerkinGenerator.classicalWordDerivative_smooth [i] q hq
  have hdp : AVenhance.IsZ2Periodic dq :=
    GalerkinGenerator.classicalWordDerivative_periodic [i] q hp
  let U := complexSmoothScalarH1 dq hdq hdp
  let Z := cellH1Conj ψ.toHk
  have hU0 := complexSmoothScalarH1_ae dq hdq hdp (valueIndex2 1)
  have hU1 := complexSmoothScalarH1_ae dq hdq hdp ⟨⟨1, by decide⟩, fun _ => i⟩
  have hZ (a : JetIndex2 1) : Z.val a =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => star (ψ.jet a x) := by
    exact (cellH1Conj_jet_ae ψ.toHk a).trans
      ((torusJetToL2_ae ψ.jet ψ.hasPeriodicWeakJet.2.1 a).fun_comp star)
  have hleft : cellComplexPair (torusHkValueCLM U) (cellDerivativeCLM i Z) =
      ∫ x in AVenhance.unitCube,
        ((fderiv ℝ q x (basisVec i) : ℝ) : ℂ) * ψ.jet ⟨⟨1, by decide⟩, fun _ => i⟩ x := by
    apply integral_congr_ae
    filter_upwards [hU0, hZ ⟨⟨1, by decide⟩, fun _ => i⟩] with x hu hz
    change torusHkValueCLM U x = ((dq x : ℝ) : ℂ) at hu
    change cellDerivativeCLM i Z x = _ at hz
    rw [hu, hz, star_star]
  have hright : cellComplexPair (cellDerivativeCLM i U) (torusHkValueCLM Z) =
      ∫ x in AVenhance.unitCube,
        ((fderiv ℝ dq x (basisVec i) : ℝ) : ℂ) * ψ.jet (valueIndex2 1) x := by
    apply integral_congr_ae
    filter_upwards [hU1, hZ (valueIndex2 1)] with x hu hz
    change cellDerivativeCLM i U x = ((fderiv ℝ dq x (basisVec i) : ℝ) : ℂ) at hu
    change torusHkValueCLM Z x = _ at hz
    rw [hu, hz, star_star]
  rw [← hleft, ← hright, weak_complex_derivative_pairing]
  exact (neg_neg _).symm

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleDamping

/-! First-derivative integration by parts against arbitrary periodic weak tests. -/

theorem smooth_weak_first_ibp (q : Vec 2 → ℝ) (hq : ContDiff ℝ (↑(⊤ : ℕ∞)) q)
    (hp : AVenhance.IsZ2Periodic q) (ψ : TorusHkFunction 1 ℂ) (i : Fin 2) :
    (∫ x in AVenhance.unitCube, (q x : ℂ) * ψ.jet ⟨⟨1, by decide⟩, fun _ => i⟩ x) =
      -∫ x in AVenhance.unitCube,
        ((fderiv ℝ q x (basisVec i) : ℝ) : ℂ) * ψ.jet (valueIndex2 1) x := by
  let U := complexSmoothScalarH1 q hq hp
  let Z := cellH1Conj ψ.toHk
  have hZ (a : JetIndex2 1) : Z.val a =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => star (ψ.jet a x) :=
    (cellH1Conj_jet_ae ψ.toHk a).trans
      ((torusJetToL2_ae ψ.jet ψ.hasPeriodicWeakJet.2.1 a).fun_comp star)
  have hl : cellComplexPair (torusHkValueCLM U) (cellDerivativeCLM i Z) =
      ∫ x in AVenhance.unitCube, (q x : ℂ) * ψ.jet ⟨⟨1, by decide⟩, fun _ => i⟩ x := by
    apply integral_congr_ae
    filter_upwards [complexSmoothScalarH1_ae q hq hp (valueIndex2 1),
      hZ ⟨⟨1, by decide⟩, fun _ => i⟩] with x hu hz
    change torusHkValueCLM U x = (q x : ℂ) at hu
    change cellDerivativeCLM i Z x = _ at hz
    rw [hu, hz, star_star]
  have hr : cellComplexPair (cellDerivativeCLM i U) (torusHkValueCLM Z) =
      ∫ x in AVenhance.unitCube,
        ((fderiv ℝ q x (basisVec i) : ℝ) : ℂ) * ψ.jet (valueIndex2 1) x := by
    apply integral_congr_ae
    filter_upwards [complexSmoothScalarH1_ae q hq hp ⟨⟨1, by decide⟩, fun _ => i⟩,
      hZ (valueIndex2 1)] with x hu hz
    change cellDerivativeCLM i U x = ((fderiv ℝ q x (basisVec i) : ℝ) : ℂ) at hu
    change torusHkValueCLM Z x = _ at hz
    rw [hu, hz, star_star]
  rw [← hl, ← hr, weak_complex_derivative_pairing]
  exact (neg_neg _).symm

theorem smooth_real_weak_first_ibp (q : Vec 2 → ℝ) (hq : ContDiff ℝ (↑(⊤ : ℕ∞)) q)
    (hp : AVenhance.IsZ2Periodic q) (ψ : TorusHkFunction 1 ℝ) (i : Fin 2) :
    (∫ x in AVenhance.unitCube, q x * ψ.jet ⟨⟨1, by decide⟩, fun _ => i⟩ x) =
      -∫ x in AVenhance.unitCube, fderiv ℝ q x (basisVec i) * ψ.jet (valueIndex2 1) x := by
  let Ψ : TorusHkFunction 1 ℂ := ⟨mapRawJet Complex.ofRealCLM ψ.jet,
    mapRawJet_hasPeriodicWeakJet Complex.ofRealCLM _ ψ.hasPeriodicWeakJet⟩
  have h := smooth_weak_first_ibp q hq hp Ψ i
  change (∫ x in AVenhance.unitCube, (q x : ℂ) * (ψ.jet ⟨⟨1, by decide⟩, fun _ => i⟩ x : ℂ)) =
      -∫ x in AVenhance.unitCube,
        ((fderiv ℝ q x (basisVec i) : ℝ) : ℂ) * (ψ.jet (valueIndex2 1) x : ℂ) at h
  simp_rw [← Complex.ofReal_mul] at h
  rw [integral_complex_ofReal, integral_complex_ofReal, ← Complex.ofReal_neg] at h
  exact Complex.ofReal_injective h

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVenhance.Infra.Classical
namespace AVRegularity.CycleDamping

/-! The summed weak Laplacian pairing for a smooth periodic scalar. -/

theorem continuous_weak_pair_integrable (q : Vec 2 → ℝ) (hq : Continuous q)
    (ψ : Vec 2 → ℂ) (hψ : MemLp ψ 2 (volume.restrict AVenhance.unitCube)) :
    Integrable (fun x => (q x : ℂ) * ψ x)
      (volume.restrict AVenhance.unitCube) := by
  have hq₂ := Complex.ofRealCLM.comp_memLp'
    (AVenhance.Infra.Parabolic.WeakUniqueness.weak_continuous_memL2On hq)
  exact memLp_one_iff_integrable.mp (hq₂.mul hψ : MemLp _ 1 _)

theorem smooth_laplacian_weak_pair (q : Vec 2 → ℝ)
    (hq : ContDiff ℝ (↑(⊤ : ℕ∞)) q) (hp : AVenhance.IsZ2Periodic q)
    (ψ : TorusHkFunction 1 ℂ) :
    -(∫ x in AVenhance.unitCube, ∑ i : Fin 2,
      ((fderiv ℝ q x (basisVec i) : ℝ) : ℂ) *
        ψ.jet ⟨⟨1, by decide⟩, fun _ => i⟩ x) =
    ∫ x in AVenhance.unitCube,
      ((∑ i : Fin 2, fderiv ℝ (fun z => fderiv ℝ q z (basisVec i)) x
        (basisVec i) : ℝ) : ℂ) * ψ.jet (valueIndex2 1) x := by
  have hi (i : Fin 2) := continuous_weak_pair_integrable
    (fun x => fderiv ℝ q x (basisVec i))
    (GalerkinGenerator.classicalWordDerivative_smooth [i] q hq).continuous
    (ψ.jet ⟨⟨1, by decide⟩, fun _ => i⟩)
    (ψ.hasPeriodicWeakJet.2.1 ⟨⟨1, by decide⟩, fun _ => i⟩)
  have hj (i : Fin 2) := continuous_weak_pair_integrable
    (fun x => fderiv ℝ (fun z => fderiv ℝ q z (basisVec i)) x (basisVec i))
    (GalerkinGenerator.classicalWordDerivative_smooth [i, i] q hq).continuous
    (ψ.jet (valueIndex2 1)) (ψ.hasPeriodicWeakJet.2.1 (valueIndex2 1))
  simp_rw [Complex.ofReal_sum, Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => hi i),
    integral_finsetSum _ (fun i _ => hj i)]
  simp_rw [smooth_partial_weak_ibp q hq hp ψ]
  rw [Finset.sum_neg_distrib, neg_neg]

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleDamping

/-! Genuine translated cosine and sine H¹ tests on the cell quotient. -/

def cellCosine (j : Fin 2) (phase : ℝ) (x : Vec 2) : ℝ :=
  Real.cos (2 * Real.pi * (x j + phase))

def cellSine (j : Fin 2) (phase : ℝ) (x : Vec 2) : ℝ :=
  Real.sin (2 * Real.pi * (x j + phase))

theorem cellCosine_smooth (j : Fin 2) (phase : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (cellCosine j phase) := by unfold cellCosine; fun_prop

theorem cellSine_smooth (j : Fin 2) (phase : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (cellSine j phase) := by unfold cellSine; fun_prop

theorem cellCosine_periodic (j : Fin 2) (phase : ℝ) : AVenhance.IsZ2Periodic (cellCosine j phase) := by
  intro n x
  have he : 2 * Real.pi * ((x + latticeShift n) j + phase) =
      2 * Real.pi * (x j + phase) + (n j : ℝ) * (2 * Real.pi) := by
    simp only [Pi.add_apply, latticeShift]; ring
  change Real.cos _ = Real.cos _
  rw [he, Real.cos_add_int_mul_two_pi]

theorem cellSine_periodic (j : Fin 2) (phase : ℝ) : AVenhance.IsZ2Periodic (cellSine j phase) := by
  intro n x
  have he : 2 * Real.pi * ((x + latticeShift n) j + phase) =
      2 * Real.pi * (x j + phase) + (n j : ℝ) * (2 * Real.pi) := by
    simp only [Pi.add_apply, latticeShift]; ring
  change Real.sin _ = Real.sin _
  rw [he, Real.sin_add_int_mul_two_pi]

def cellCosineH1 (j : Fin 2) (phase : ℝ) : TorusHk 1 ℂ :=
  complexSmoothScalarH1 (cellCosine j phase) (cellCosine_smooth j phase) (cellCosine_periodic j phase)

def cellSineH1 (j : Fin 2) (phase : ℝ) : TorusHk 1 ℂ :=
  complexSmoothScalarH1 (cellSine j phase) (cellSine_smooth j phase) (cellSine_periodic j phase)

theorem cellCosineH1_value_ae (j : Fin 2) (phase : ℝ) :
    torusHkValueCLM (cellCosineH1 j phase) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => (cellCosine j phase x : ℂ) := by
  exact complexSmoothScalarH1_ae _ (cellCosine_smooth j phase) (cellCosine_periodic j phase) (valueIndex2 1)

theorem cellSineH1_value_ae (j : Fin 2) (phase : ℝ) :
    torusHkValueCLM (cellSineH1 j phase) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => (cellSine j phase x : ℂ) := by
  exact complexSmoothScalarH1_ae _ (cellSine_smooth j phase) (cellSine_periodic j phase) (valueIndex2 1)

theorem cellCosine_derivative (j i : Fin 2) (phase : ℝ) (x : Vec 2) :
    fderiv ℝ (cellCosine j phase) x (basisVec i) =
      if i = j then -(2 * Real.pi) * cellSine j phase x else 0 := by
  have hp := ((hasFDerivAt_apply (𝕜 := ℝ) j x).add_const phase).const_mul (2 * Real.pi)
  have hc := (Real.hasDerivAt_cos (2 * Real.pi * (x j + phase))).comp_hasFDerivAt x hp
  change fderiv ℝ (fun y => Real.cos (2 * Real.pi * (y j + phase))) x (basisVec i) = _
  have he := hc.fderiv
  simp only [Function.comp_def] at he
  rw [he]
  by_cases hij : i = j
  · subst i
    simp only [smul_apply, ContinuousLinearMap.proj_apply, basisVec_apply, ite_true, smul_eq_mul]
    unfold cellSine
    ring
  · simp only [smul_apply, ContinuousLinearMap.proj_apply, basisVec_apply, Ne.symm hij,
      hij, ite_false, smul_zero]

theorem cellSine_derivative (j i : Fin 2) (phase : ℝ) (x : Vec 2) :
    fderiv ℝ (cellSine j phase) x (basisVec i) =
      if i = j then (2 * Real.pi) * cellCosine j phase x else 0 := by
  have hp := ((hasFDerivAt_apply (𝕜 := ℝ) j x).add_const phase).const_mul (2 * Real.pi)
  have hc := (Real.hasDerivAt_sin (2 * Real.pi * (x j + phase))).comp_hasFDerivAt x hp
  change fderiv ℝ (fun y => Real.sin (2 * Real.pi * (y j + phase))) x (basisVec i) = _
  have he := hc.fderiv
  simp only [Function.comp_def] at he
  rw [he]
  by_cases hij : i = j
  · subst i
    simp only [smul_apply, ContinuousLinearMap.proj_apply, basisVec_apply, ite_true, smul_eq_mul]
    unfold cellCosine
    ring
  · simp only [smul_apply, ContinuousLinearMap.proj_apply, basisVec_apply, Ne.symm hij,
      hij, ite_false, smul_zero]

end AVRegularity.CycleDamping
end

section
open Homogenization
namespace AVRegularity.CycleDamping

/-! A half-period phase change normalizes either sign of a shear-frequency coupling. -/

theorem cellCosine_half_period (j : Fin 2) (phase : ℝ) (x : Vec 2) :
    cellCosine j (phase + 1 / 2) x = -cellCosine j phase x := by
  unfold cellCosine
  have he : 2 * Real.pi * (x j + (phase + 1 / 2)) =
      2 * Real.pi * (x j + phase) + Real.pi := by ring
  rw [he, Real.cos_add_pi]

theorem stationary_shear_sign_normalization {a b : ℝ}
    (v : ℝ → Vec 2 → Vec 2) (j k : Fin 2) (phase A θk : ℝ)
    (hshear : ∀ t ∈ Set.Icc a b, ∀ x i,
      v t x i = if i = k then A * cellCosine j phase x else 0) :
    ∃ phase' A' : ℝ, A' * θk = |A * θk| ∧
      ∀ t ∈ Set.Icc a b, ∀ x i,
        v t x i = if i = k then A' * cellCosine j phase' x else 0 := by
  by_cases hp : 0 ≤ A * θk
  · exact ⟨phase, A, (abs_of_nonneg hp).symm, hshear⟩
  · refine ⟨phase + 1 / 2, -A, ?_, ?_⟩
    · rw [abs_of_neg (lt_of_not_ge hp)]; ring
    · intro t ht x i
      rw [hshear t ht x i, cellCosine_half_period]
      simp only [neg_mul_neg]

theorem real_frequency_large_coordinate (ξ : Vec 2) (ξlo : ℝ) (hlo : 0 < ξlo)
    (hξ : ξlo ≤ Real.sqrt (∑ i : Fin 2, ξ i ^ 2)) :
    ξlo / 2 ≤ |ξ 0| ∨ ξlo / 2 ≤ |ξ 1| := by
  have hs := (sq_le_sq₀ hlo.le (Real.sqrt_nonneg _)).mpr hξ
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _)), Fin.sum_univ_two] at hs
  by_contra hn
  have h0 : |ξ 0| < ξlo / 2 := lt_of_not_ge (fun h => hn (Or.inl h))
  have h1 : |ξ 1| < ξlo / 2 := lt_of_not_ge (fun h => hn (Or.inr h))
  have h0s := mul_self_lt_mul_self (abs_nonneg (ξ 0)) h0
  have h1s := mul_self_lt_mul_self (abs_nonneg (ξ 1)) h1
  nlinarith only [hs, h0s, h1s, sq_pos_of_pos hlo, sq_abs (ξ 0), sq_abs (ξ 1)]

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleDamping

/-! Smooth periodic divergence-free fields annihilate every weak periodic test. -/

theorem smooth_divergence_free_weak (v : Vec 2 → Vec 2)
    (hv : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => v x i))
    (hp : ∀ i, AVenhance.IsZ2Periodic (fun x => v x i))
    (hd : ∀ x, ∑ i : Fin 2, fderiv ℝ (fun z => v z i) x (basisVec i) = 0)
    (ψ : TorusHkFunction 1 ℝ) :
    (∫ x in AVenhance.unitCube, ∑ i : Fin 2,
      v x i * ψ.jet ⟨⟨1, by decide⟩, fun _ => i⟩ x) = 0 := by
  have hi (i : Fin 2) : Integrable (fun x => v x i *
      ψ.jet ⟨⟨1, by decide⟩, fun _ => i⟩ x) (volume.restrict AVenhance.unitCube) :=
    memLp_one_iff_integrable.mp
      ((AVenhance.Infra.Parabolic.WeakUniqueness.weak_continuous_memL2On (hv i).continuous).mul
        (ψ.hasPeriodicWeakJet.2.1 ⟨⟨1, by decide⟩, fun _ => i⟩) : MemLp _ 1 _)
  have hj (i : Fin 2) : Integrable (fun x => fderiv ℝ (fun z => v z i) x (basisVec i) *
      ψ.jet (valueIndex2 1) x) (volume.restrict AVenhance.unitCube) :=
    memLp_one_iff_integrable.mp
      ((AVenhance.Infra.Parabolic.WeakUniqueness.weak_continuous_memL2On
        (AVenhance.Infra.Classical.GalerkinGenerator.classicalWordDerivative_smooth
          [i] (fun z => v z i) (hv i)).continuous).mul
        (ψ.hasPeriodicWeakJet.2.1 (valueIndex2 1)) : MemLp _ 1 _)
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [smooth_real_weak_first_ibp _ (hv _) (hp _) ψ]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => hj i)]
  simp_rw [← Finset.sum_mul, hd, zero_mul]
  simp only [integral_zero, neg_zero]

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleDamping

/-! Exact first-derivative classes of the translated cell trigonometric tests. -/

theorem cellCosineH1_derivative (j i : Fin 2) (phase : ℝ) :
    cellDerivativeCLM i (cellCosineH1 j phase) =
      cellScalarCLM (if i = j then (-(2 * Real.pi) : ℂ) else 0)
        (torusHkValueCLM (cellSineH1 j phase)) := by
  apply Lp.ext
  have hd := complexSmoothScalarH1_ae _ (cellCosine_smooth j phase) (cellCosine_periodic j phase)
    ⟨⟨1, by decide⟩, fun _ => i⟩
  filter_upwards [hd, cellSineH1_value_ae j phase, cellScalarCLM_ae
    (if i = j then (-(2 * Real.pi) : ℂ) else 0) (torusHkValueCLM (cellSineH1 j phase))] with x hx hs hc
  change cellDerivativeCLM i (cellCosineH1 j phase) x = _ at hx
  rw [hx, hc, hs]
  change ((fderiv ℝ (cellCosine j phase) x (basisVec i) : ℝ) : ℂ) = _
  rw [cellCosine_derivative]
  by_cases hij : i = j <;> simp only [hij, ite_true, ite_false, Complex.ofReal_mul,
    Complex.ofReal_neg, Complex.ofReal_zero, Complex.ofReal_ofNat, zero_mul]

theorem cellSineH1_derivative (j i : Fin 2) (phase : ℝ) :
    cellDerivativeCLM i (cellSineH1 j phase) =
      cellScalarCLM (if i = j then (2 * Real.pi : ℂ) else 0)
        (torusHkValueCLM (cellCosineH1 j phase)) := by
  apply Lp.ext
  have hd := complexSmoothScalarH1_ae _ (cellSine_smooth j phase) (cellSine_periodic j phase)
    ⟨⟨1, by decide⟩, fun _ => i⟩
  filter_upwards [hd, cellCosineH1_value_ae j phase, cellScalarCLM_ae
    (if i = j then (2 * Real.pi : ℂ) else 0) (torusHkValueCLM (cellCosineH1 j phase))] with x hx hs hc
  change cellDerivativeCLM i (cellSineH1 j phase) x = _ at hx
  rw [hx, hc, hs]
  change ((fderiv ℝ (cellSine j phase) x (basisVec i) : ℝ) : ℂ) = _
  rw [cellSine_derivative]
  by_cases hij : i = j <;> simp only [hij, ite_true, ite_false, Complex.ofReal_mul,
    Complex.ofReal_zero, Complex.ofReal_ofNat, zero_mul]

theorem cellCosineH1_mean (j : Fin 2) (phase : ℝ) :
    cellMean (torusHkValueCLM (cellCosineH1 j phase)) = 0 := by
  have he : cellMean (torusHkValueCLM (cellCosineH1 j phase)) =
      ∫ x in unitCube, (cellCosine j phase x : ℂ) := integral_congr_ae (cellCosineH1_value_ae j phase)
  rw [he, integral_complex_ofReal]
  rw [show (∫ x in unitCube, cellCosine j phase x) = 0 from cell_cosine_mean_zero j phase,
    Complex.ofReal_zero]

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleDamping

/-! Exact shifted-gradient pairings with the two shear moments. -/

theorem shifted_cosine_pair (θ : Vec 2) (u : TorusHk 1 ℂ) (j i : Fin 2) (phase : ℝ) :
    cellComplexPair (cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) i u)
      (torusHkValueCLM (cellCosineH1 j phase)) =
    (if i = j then (2 * Real.pi : ℂ) else 0) *
      cellComplexPair (torusHkValueCLM u) (torusHkValueCLM (cellSineH1 j phase)) +
    Complex.I * (θ i : ℂ) *
      cellComplexPair (torusHkValueCLM u) (torusHkValueCLM (cellCosineH1 j phase)) := by
  change cellComplexPair (cellDerivativeCLM i u +
    cellScalarCLM (Complex.I * (θ i : ℂ)) (torusHkValueCLM u)) _ = _
  rw [pair_add_left, pair_scalar_left, weak_complex_derivative_pairing,
    cellCosineH1_derivative, pair_scalar_right]
  by_cases hij : i = j <;> simp only [hij, ite_true, ite_false, map_neg,
    Complex.star_def, Complex.conj_ofReal, map_mul, map_ofNat, map_zero, zero_mul, neg_zero]
  all_goals ring

theorem shifted_sine_pair (θ : Vec 2) (u : TorusHk 1 ℂ) (j i : Fin 2) (phase : ℝ) :
    cellComplexPair (cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) i u)
      (torusHkValueCLM (cellSineH1 j phase)) =
    -(if i = j then (2 * Real.pi : ℂ) else 0) *
      cellComplexPair (torusHkValueCLM u) (torusHkValueCLM (cellCosineH1 j phase)) +
    Complex.I * (θ i : ℂ) *
      cellComplexPair (torusHkValueCLM u) (torusHkValueCLM (cellSineH1 j phase)) := by
  change cellComplexPair (cellDerivativeCLM i u +
    cellScalarCLM (Complex.I * (θ i : ℂ)) (torusHkValueCLM u)) _ = _
  rw [pair_add_left, pair_scalar_left, weak_complex_derivative_pairing,
    cellSineH1_derivative, pair_scalar_right]
  by_cases hij : i = j <;> simp only [hij, ite_true, ite_false,
    Complex.star_def, Complex.conj_ofReal, map_mul, map_ofNat, map_zero, zero_mul, neg_zero]
  all_goals ring

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleDamping

/-! Means and fluctuation pairing identities for the actual shear tests. -/

theorem cellComplexPair_constant_left (c : ℂ) (z : ComplexCellL2) :
    cellComplexPair (cellConstantCLM c) z = c * star (cellMean z) := by
  rw [cellComplexPair_inner]
  have hc : cellConstantCLM c = cellScalarCLM c (cellConstantCLM 1) := by
    rw [cellScalar_constant, mul_one]
  rw [hc]
  change inner ℂ z (c • cellConstantCLM 1) = _
  rw [inner_smul_right, ← inner_conj_symm z (cellConstantCLM 1),
    ← cellComplexPair_inner z (cellConstantCLM 1), cellComplexPair_one]
  rfl

theorem meanFree_pair_of_zero_mean (u z : ComplexCellL2) (hz : cellMean z = 0) :
    cellComplexPair u z = cellComplexPair (cellQ0CLM u) z := by
  change cellComplexPair u z = cellComplexPair (u - cellConstantCLM (cellMeanCLM u)) z
  simp only [cellComplexPair_inner, inner_sub_right]
  rw [← cellComplexPair_inner (cellConstantCLM (cellMeanCLM u)) z,
    cellComplexPair_constant_left, hz, star_zero, mul_zero, sub_zero]

end AVRegularity.CycleDamping
end
