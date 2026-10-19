-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.CellWeakProjectedFeedbackDecay
public import AVRegularity.CycleEvolution.CellEnergySeriesRegularity
import AVRegularity.CycleEvolution.CellEnergySpaceRawDirectionalLimit
import AVRegularity.CycleEvolution.CellLimitMoments
import AVRegularity.CycleEvolution.CellEnergySpaceRawJetCauchyBound
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The mean-projected normalized equation has an unweighted forced energy bound with fixed constants. -/

theorem cellWeak_projected_feedback_local_energy {a b : ℝ} (hab : a ≤ b)
    (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (L Cr : ℝ)
    (hsmall : Cw * fibreNorm ξ + (1032 + L + Cr * Cw) * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2)
    (hξsmall : fibreNorm ξ ≤ 1)
    (hθ : ∀ j, ‖(Real.sqrt η : ℂ) * ξ j‖ ≤ fibreNorm ξ)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (lam : ℝ → ℂ) (hlam : ∀ t, ‖lam t‖ ≤ L * fibreNorm ξ ^ 2)
    (ρ : ℝ → ComplexCellL2) (hρ : ∀ t, ‖ρ t‖ ≤ Cr * fibreNorm ξ)
    (hρsmall : ∀ t, ‖ρ t‖ ≤ 1) (F : ℝ → Fin 2 → ComplexCellL2)
    (hF : ∀ j, MemLp (fun t => F t j) 2 (volume.restrict (Icc a b)))
    (h : CellWeakHilbertCurve a b u slice (fun t => cellDualDerivative
      ⟨fun t _ => G t, v, (fun j => (Real.sqrt η : ℂ) * ξ j), 0⟩
      hG V hv.1 hb t (slice t) 0 (F t) -
      cellPivotDualCLM (cellScalarCLM (lam t) (torusHkValueCLM (slice t))) -
      cellPivotDualCLM (cellScalarCLM
        (-Complex.I * cellBlochDriftMeanCLM η Cw hCw hv hw ξ t (torusHkValueCLM (slice t)) +
          ∑ j : Fin 2, Complex.I * ((Real.sqrt η : ℂ) * ξ j) * cellMean (F t j))
        (ρ t + cellConstantCLM 1))))
    (hm : ∀ t ∈ Icc a b, cellMean (u t) = 0) :
    ‖u b‖ ^ 2 + (∫ t in a..b,
      (Real.pi ^ 2 / 2) * ‖u t‖ ^ 2 + (1 / 4) * ∑ j, ‖cellDerivativeCLM j (slice t)‖ ^ 2) ≤
      ‖u a‖ ^ 2 + ∫ t in a..b, 14 * ∑ j, ‖F t j‖ ^ 2 := by
  have hf : IntervalIntegrable (fun t => 14 * ∑ j, ‖F t j‖ ^ 2) volume a b := by
    simpa only [Fin.sum_univ_two, Pi.add_apply] using
      ((cellTime_normSq_intervalIntegrable hab (hF 0)).add
        (cellTime_normSq_intervalIntegrable hab (hF 1))).const_mul 14
  have hvint : IntervalIntegrable (fun t => ‖u t‖ ^ 2) volume a b :=
    (h.trace.norm.pow 2).intervalIntegrable_of_Icc hab
  have hd := (hvint.const_mul (Real.pi ^ 2 / 2)).add
    ((cellTime_gradientSq_intervalIntegrable hab slice h.state).const_mul (1 / 4))
  have he := (h.energy_strongTime hab).scalar_weighted_bound hab 0
    (fun t => 14 * ∑ j, ‖F t j‖ ^ 2)
    (fun t => (Real.pi ^ 2 / 2) * ‖u t‖ ^ 2 + (1 / 4) * ∑ j, ‖cellDerivativeCLM j (slice t)‖ ^ 2) hf hd
  simp only [zero_mul, Real.exp_zero, one_mul] at he
  apply he
  filter_upwards [h.agrees, ae_restrict_mem measurableSet_Icc] with t ht hti
  have hmean := hm t hti
  rw [ht] at hmean
  have hbnd := cellBloch_projected_feedback_forced_energy η Cw hη0 hη hCw G hG hg hgsmall
    hv hw V hb ξ L Cr hsmall t (slice t) hmean (lam t) (hlam t) (ρ t) (hρ t)
    (hρsmall t) hξsmall hθ (F t)
  simpa only [ht, zero_mul, add_zero, add_assoc] using hbnd

/-! The mean-projected normalized equation has an unweighted forced energy bound with fixed constants. -/

theorem cellWeak_projected_feedback_energy_components {a b : ℝ} (hab : a ≤ b)
    (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (L Cr : ℝ)
    (hsmall : Cw * fibreNorm ξ + (1032 + L + Cr * Cw) * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2)
    (hξsmall : fibreNorm ξ ≤ 1)
    (hθ : ∀ j, ‖(Real.sqrt η : ℂ) * ξ j‖ ≤ fibreNorm ξ)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (lam : ℝ → ℂ) (hlam : ∀ t, ‖lam t‖ ≤ L * fibreNorm ξ ^ 2)
    (ρ : ℝ → ComplexCellL2) (hρ : ∀ t, ‖ρ t‖ ≤ Cr * fibreNorm ξ)
    (hρsmall : ∀ t, ‖ρ t‖ ≤ 1) (F : ℝ → Fin 2 → ComplexCellL2)
    (hF : ∀ j, MemLp (fun t => F t j) 2 (volume.restrict (Icc a b)))
    (h : CellWeakHilbertCurve a b u slice (fun t => cellDualDerivative
      ⟨fun t _ => G t, v, (fun j => (Real.sqrt η : ℂ) * ξ j), 0⟩
      hG V hv.1 hb t (slice t) 0 (F t) -
      cellPivotDualCLM (cellScalarCLM (lam t) (torusHkValueCLM (slice t))) -
      cellPivotDualCLM (cellScalarCLM
        (-Complex.I * cellBlochDriftMeanCLM η Cw hCw hv hw ξ t (torusHkValueCLM (slice t)) +
          ∑ j : Fin 2, Complex.I * ((Real.sqrt η : ℂ) * ξ j) * cellMean (F t j))
        (ρ t + cellConstantCLM 1))))
    (hm : ∀ t ∈ Icc a b, cellMean (u t) = 0) :
    let B := ‖u a‖ ^ 2 + 14 * ∫ t in a..b, ∑ j, ‖F t j‖ ^ 2
    ‖u b‖ ^ 2 ≤ B ∧
      (Real.pi ^ 2 / 2) * (∫ t in a..b, ‖u t‖ ^ 2) ≤ B ∧
      (1 / 4 : ℝ) * (∫ t in a..b, ∑ j, ‖cellDerivativeCLM j (slice t)‖ ^ 2) ≤ B := by
  dsimp only
  have hi := cellWeak_projected_feedback_local_energy hab η Cw hη0 hη hCw G hG hg hgsmall hv hw
    V hb ξ L Cr hsmall hξsmall hθ u slice lam hlam ρ hρ hρsmall F hF h hm
  have hvint : IntervalIntegrable (fun t => ‖u t‖ ^ 2) volume a b :=
    (h.trace.norm.pow 2).intervalIntegrable_of_Icc hab
  have hgradint := cellTime_gradientSq_intervalIntegrable hab slice h.state
  rw [intervalIntegral.integral_add (hvint.const_mul _) (hgradint.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hi
  have hvnon : 0 ≤ ∫ t in a..b, ‖u t‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun _ _ => sq_nonneg _)
  have hgnon : 0 ≤ ∫ t in a..b, ∑ j, ‖cellDerivativeCLM j (slice t)‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hmassnon : 0 ≤ (Real.pi ^ 2 / 2) * (∫ t in a..b, ‖u t‖ ^ 2) := by positivity
  have hgradnon : 0 ≤ (1 / 4 : ℝ) * (∫ t in a..b, ∑ j, ‖cellDerivativeCLM j (slice t)‖ ^ 2) := by positivity
  exact ⟨by linarith, by linarith [sq_nonneg ‖u b‖], by linarith [sq_nonneg ‖u b‖]⟩

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! The full actual Bloch perturbation as bounded zero-initial scalar and flux forcing data. -/

def cellBlochPerturbationDatumCLM {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (δ : Fin 2 → ℂ) (q : Lp ℂ ∞ (volume.restrict (Icc a b))) :
    CellFiniteEnergyCarrier a b →L[ℂ] CellFiniteEnergyDatum a b :=
  (0 : CellFiniteEnergyCarrier a b →L[ℂ] ComplexCellL2).prod
    ((cellBlochPerturbationScalarCLM hab C hG V hv hb δ q).prod
      (ContinuousLinearMap.pi (fun k => cellBlochPerturbationFluxCLM hab C hG δ k)))

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Bounded finite-past Hilbert solutions for the pullback construction of the cell inverse. -/

/-- The actual Galerkin construction produces a mean-zero weak solution with a horizon-independent bound. -/
theorem cellFinite_meanZero_Hilbert_bounded {a b : ℝ} (hab : a ≤ b)
    (I : Set ℝ) (hI : Icc a b ⊆ I)
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hV : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (f : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hfm : Measurable (Function.uncurry f)) (hFm : Measurable (Function.uncurry F))
    (hf : cellUlNorm I f < ⊤) (hF : cellUlNorm I F < ⊤)
    (initial : ComplexCellL2) (hi : cellMean initial = 0) :
    ∃ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ),
      CellWeakHilbertCurve a b u slice (fun t => cellDualDerivative ⟨G, v, 0, 0⟩ hG V hv.1 hV t
        (slice t) (cellSourceSlice (fun r => cellQ0 (f r)) t)
        (fun j => cellSourceSlice (fun r x => F r x j) t)) ∧
      u a = initial ∧ (∀ t ∈ Icc a b, cellMean (u t) = 0) ∧
      ∀ t ∈ Icc a b, ‖u t‖ ^ 2 ≤ ‖initial‖ ^ 2 +
        (4 * (cellUlNorm I f).toReal ^ 2 + 8 * (cellUlNorm I F).toReal ^ 2) /
          (1 - Real.exp (-(Real.pi ^ 2))) +
        (4 * (cellUlNorm I f).toReal ^ 2 + 8 * (cellUlNorm I F).toReal ^ 2) := by
  have hef := cellUl_interval_integral_lt_top I f hf a b
  have heF := cellUl_interval_integral_lt_top I F hF a b
  rw [inter_eq_left.mpr hI] at hef heF
  have hp := cellSource_memLp_product (Icc a b) f hfm hef
  have hqp := cellQ0_memLp_product (Icc a b) f hfm hp
  obtain ⟨u, slice, h, hinit⟩ := cellActual_exists_Hilbert hab ⟨G, v, 0, 0⟩ hG V 0 hv.1 hV
    measurable_const (fun _ => by simp) (fun t => cellQ0 (f t)) F (cellQ0_measurable hfm) hFm
    (cellProduct_cellNormSq_finite (Icc a b) _ hqp) heF initial
  have hm : ∀ t ∈ Icc a b, cellMean (u t) = 0 := by
    intro t ht
    rw [cellWeakActual_mean_conserved hab hG hv V hV u slice _ _ h
      (Filter.Eventually.of_forall (cellSourceSlice_Q0_mean f)) t ht, hinit, hi]
  refine ⟨u, slice, h, hinit, hm, ?_⟩
  simpa only [hinit] using
    cellWeakActual_ul_trace_bound hab I hI hG hv V hV f F hfm hFm hf hF u slice h hm

/-! Compatible actual finite-interval solutions for a prescribed finite-past initial trace. -/

/-- Compatible finite-past cell solutions with a fixed initial class and uniform energy control. -/
structure CellFinitePastApproximationData (s : ℝ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric G)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hV : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (f : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (initial : ComplexCellL2) (R : ℝ) where
  trace : ℕ → ℝ → ComplexCellL2
  slice : ℕ → ℝ → TorusHk 1 ℂ
  curve : ∀ n : ℕ, CellWeakHilbertCurve s (s + n) (trace n) (slice n)
    (fun t => cellDualDerivative ⟨G, v, 0, 0⟩ hG V hv.1 hV t (slice n t)
      (cellSourceSlice (fun r => cellQ0 (f r)) t)
      (fun j => cellSourceSlice (fun r x => F r x j) t))
  initial_eq : ∀ n : ℕ, trace n s = initial
  mean : ∀ (n : ℕ) (t : ℝ), t ∈ Icc s (s + n) → cellMean (trace n t) = 0
  bound : ∀ (n : ℕ) (t : ℝ), t ∈ Icc s (s + n) → ‖trace n t‖ ^ 2 ≤ R

/-- Actual Galerkin solutions provide the finite-past approximation family and its uniform bound. -/
theorem cellFinitePastApproximation_exists (s : ℝ)
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hV : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (f : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hfm : Measurable (Function.uncurry f)) (hFm : Measurable (Function.uncurry F))
    (hf : cellUlNorm (Ici s) f < ⊤) (hF : cellUlNorm (Ici s) F < ⊤)
    (initial : ComplexCellL2) (hi : cellMean initial = 0) :
    Nonempty (CellFinitePastApproximationData s G hG v hv V hV f F initial
      (‖initial‖ ^ 2 +
       (4 * (cellUlNorm (Ici s) f).toReal ^ 2 + 8 * (cellUlNorm (Ici s) F).toReal ^ 2) /
         (1 - Real.exp (-(Real.pi ^ 2))) +
       (4 * (cellUlNorm (Ici s) f).toReal ^ 2 + 8 * (cellUlNorm (Ici s) F).toReal ^ 2))) := by
  have hex (n : ℕ) := cellFinite_meanZero_Hilbert_bounded
    (show s ≤ s + n by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    (Ici s) (fun _ ht => ht.1) hG hv V hV f F hfm hFm hf hF initial hi
  choose u slice hu hi' hm hb using hex
  exact ⟨⟨u, slice, hu, hi', hm, hb⟩⟩

/-- Finite-past solutions with the same initial state agree on every nested interval. -/
theorem CellFinitePastApproximationData.coherent
    {s : ℝ} {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {hG : IsCellMetric G}
    {v : ℝ → Vec 2 → Vec 2} {hv : IsCellDrift v} {V : ℝ}
    {hV : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2}
    {f : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    {initial : ComplexCellL2} {R : ℝ}
    (D : CellFinitePastApproximationData s G hG v hv V hV f F initial R)
    {n m : ℕ} (hnm : n ≤ m) :
    ∀ t ∈ Icc s (s + n), D.trace n t = D.trace m t := by
  have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have hsub : Icc s (s + n) ⊆ Icc s (s + m) := Icc_subset_Icc le_rfl (add_le_add le_rfl hnm')
  have hab : s ≤ s + n := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  exact cellActualWeak_unique hab ⟨G, v, 0, 0⟩ hG V 0 hv.1 hV (fun _ => by simp)
    (cellSourceSlice (fun r => cellQ0 (f r)))
    (fun t j => cellSourceSlice (fun r x => F r x j) t)
    (D.trace n) (D.trace m) (D.slice n) (D.slice m) (D.curve n) ((D.curve m).mono hsub)
    ((D.initial_eq n).trans (D.initial_eq m).symm)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.CycleEvolution

/-! Compatible finite-interval traces assemble into the actual finite-past cell trajectory. -/

variable {s : ℝ} {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {hG : IsCellMetric G}
  {v : ℝ → Vec 2 → Vec 2} {hv : IsCellDrift v} {V : ℝ}
  {hV : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2}
  {f : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
  {initial : ComplexCellL2} {R : ℝ}

/-- The finite-past trace uses the compatible actual solution on an interval containing its time. -/
def CellFinitePastApproximationData.pastTrace
    (D : CellFinitePastApproximationData s G hG v hv V hV f F initial R) (t : ℝ) : ComplexCellL2 := by
  classical
  exact if s ≤ t then D.trace (cellLocalTimeIndex (t - s)) t else 0

/-- The assembled finite-past trace equals every finite solution on its full interval. -/
theorem CellFinitePastApproximationData.pastTrace_eq
    (D : CellFinitePastApproximationData s G hG v hv V hV f F initial R)
    {n : ℕ} {t : ℝ} (ht : t ∈ Icc s (s + n)) : D.pastTrace t = D.trace n t := by
  classical
  unfold CellFinitePastApproximationData.pastTrace
  rw [ite_eq_left ht.1]
  have hk : t ∈ Icc s (s + cellLocalTimeIndex (t - s)) := by
    constructor
    · exact ht.1
    · have := (cellLocalTimeIndex_mem (t - s)).2; linarith
  rcases le_total (cellLocalTimeIndex (t - s)) n with hkn | hnk
  · exact D.coherent hkn t hk
  · exact (D.coherent hnk t ht).symm

/-- The assembled trace has its prescribed arbitrary L² initial state. -/
theorem CellFinitePastApproximationData.pastTrace_initial
    (D : CellFinitePastApproximationData s G hG v hv V hV f F initial R) : D.pastTrace s = initial := by
  rw [D.pastTrace_eq (n := 0) (by simp), D.initial_eq]

/-- The actual finite-past trace is mean zero at every time in its domain. -/
theorem CellFinitePastApproximationData.pastTrace_mean
    (D : CellFinitePastApproximationData s G hG v hv V hV f F initial R) {t : ℝ} (ht : s ≤ t) :
    cellMean (D.pastTrace t) = 0 := by
  have hk : t ∈ Icc s (s + cellLocalTimeIndex (t - s)) :=
    ⟨ht, by have := (cellLocalTimeIndex_mem (t - s)).2; linarith⟩
  rw [D.pastTrace_eq hk]
  exact D.mean _ t hk

/-- The actual finite-past trace preserves its horizon-independent squared norm bound. -/
theorem CellFinitePastApproximationData.pastTrace_bound
    (D : CellFinitePastApproximationData s G hG v hv V hV f F initial R) {t : ℝ} (ht : s ≤ t) :
    ‖D.pastTrace t‖ ^ 2 ≤ R := by
  have hk : t ∈ Icc s (s + cellLocalTimeIndex (t - s)) :=
    ⟨ht, by have := (cellLocalTimeIndex_mem (t - s)).2; linarith⟩
  rw [D.pastTrace_eq hk]
  exact D.bound _ t hk

/-- The assembled trace is continuous into spatial L² on the closed finite-past half-line. -/
theorem CellFinitePastApproximationData.pastTrace_continuousOn
    (D : CellFinitePastApproximationData s G hG v hv V hV f F initial R) :
    ContinuousOn D.pastTrace (Ici s) := by
  intro t ht
  obtain ⟨N, hN⟩ := exists_nat_gt (t - s)
  have hupper : t < s + N := by linarith
  have htN : t ∈ Icc s (s + N) := ⟨ht, hupper.le⟩
  have he : 𝓝[Icc s (s + N)] t = 𝓝[Ici s] t := by
    rw [show Icc s (s + N) = Iic (s + N) ∩ Ici s by ext r; simp only [mem_Icc, mem_inter_iff, mem_Iic, mem_Ici]; tauto]
    exact nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hupper))
  have hlim := (D.curve N).trace t htN
  change Tendsto (D.trace N) (𝓝[Icc s (s + N)] t) (𝓝 (D.trace N t)) at hlim
  change Tendsto D.pastTrace (𝓝[Ici s] t) (𝓝 (D.pastTrace t))
  rw [he] at hlim
  rw [D.pastTrace_eq htN]
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hupper)] with r hr hru
  exact (D.pastTrace_eq ⟨hr, hru⟩).symm

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CycleEvolution

/-! Complex scalar multiplication of the actual finite-time evolution relation. -/

theorem IsCellFiniteEnergyEvolution.complex_smul {a b : ℝ}
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    {d : CellFiniteEnergyDatum a b} {z : CellFiniteEnergyCarrier a b}
    (hz : IsCellFiniteEnergyEvolution C hG V hv hb d z) (c : ℂ) :
    IsCellFiniteEnergyEvolution C hG V hv hb (c • d) (c • z) := by
  obtain ⟨u, slice, hu, hiu, htu⟩ := hz
  have hs := cellActualWeak_complex_smul C hG V hv hb d.2.1 (fun t j => d.2.2 j t) u slice hu c
  refine ⟨fun t => c • u t, fun t => cellH1Scalar c (slice t), hs.dual_congr ?_, ?_, ?_⟩
  · have hf j := Lp.coeFn_smul c (d.2.2 j)
    filter_upwards [Lp.coeFn_smul c d.2.1, ae_all_iff.mpr hf] with t hS hF
    have hs' : c • d.2.1 t = (c • d).2.1 t := hS.symm
    have hh : (fun j => c • d.2.2 j t) = (fun j => (c • d).2.2 j t) := by
      funext j
      exact (hF j).symm
    rw [hs', hh]
  · change c • u a = c • d.1
    rw [hiu]
  · intro t
    change c • z.val.1 t = c • u t.val
    rw [htu]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Actual zero-initial finite-past approximations for the all-time mean-zero cell inverse. -/

/-- Finite-past approximations constructed from the actual cell equation, with uniform energy control. -/
structure CellPullbackApproximationData
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric G)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hV : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (f : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) (R : ℝ) where
  trace : ℕ → ℝ → ComplexCellL2
  slice : ℕ → ℝ → TorusHk 1 ℂ
  curve : ∀ n : ℕ, CellWeakHilbertCurve (-(n : ℝ)) n (trace n) (slice n)
    (fun t => cellDualDerivative ⟨G, v, 0, 0⟩ hG V hv.1 hV t (slice n t)
      (cellSourceSlice (fun r => cellQ0 (f r)) t)
      (fun j => cellSourceSlice (fun r x => F r x j) t))
  initial : ∀ n : ℕ, trace n (-(n : ℝ)) = 0
  mean : ∀ (n : ℕ) (t : ℝ), t ∈ Icc (-(n : ℝ)) n → cellMean (trace n t) = 0
  bound : ∀ (n : ℕ) (t : ℝ), t ∈ Icc (-(n : ℝ)) n → ‖trace n t‖ ^ 2 ≤ R

/-- The Galerkin construction and unit-window estimates supply the full pullback approximation data. -/
theorem cellPullbackApproximation_exists
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hV : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (f : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hfm : Measurable (Function.uncurry f)) (hFm : Measurable (Function.uncurry F))
    (hf : cellUlNorm univ f < ⊤) (hF : cellUlNorm univ F < ⊤) :
    Nonempty (CellPullbackApproximationData G hG v hv V hV f F
      ((4 * (cellUlNorm univ f).toReal ^ 2 + 8 * (cellUlNorm univ F).toReal ^ 2) /
        (1 - Real.exp (-(Real.pi ^ 2))) +
       (4 * (cellUlNorm univ f).toReal ^ 2 + 8 * (cellUlNorm univ F).toReal ^ 2))) := by
  have hex (n : ℕ) := cellFinite_meanZero_Hilbert_bounded
    (show -(n : ℝ) ≤ n by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    univ (subset_univ _) hG hv V hV f F hfm hFm hf hF 0 (by rw [← cellMeanCLM_apply, map_zero])
  choose u slice hu hi hm hb using hex
  refine ⟨⟨u, slice, hu, hi, hm, ?_⟩⟩
  intro n t ht
  simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] using hb n t ht

/-- Nested finite-past approximations differ by an exponentially decaying entering trace. -/
theorem CellPullbackApproximationData.difference_bound
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {hG : IsCellMetric G}
    {v : ℝ → Vec 2 → Vec 2} {hv : IsCellDrift v} {V : ℝ}
    {hV : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2}
    {f : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {R : ℝ}
    (D : CellPullbackApproximationData G hG v hv V hV f F R)
    {n m : ℕ} (hnm : n ≤ m) {t : ℝ} (ht : t ∈ Icc (-(n : ℝ)) n) :
    ‖D.trace n t - D.trace m t‖ ^ 2 ≤ Real.exp (-(4 * Real.pi ^ 2) * (t + n)) * R := by
  have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have hsub : Icc (-(n : ℝ)) n ⊆ Icc (-(m : ℝ)) m := Icc_subset_Icc (by linarith) hnm'
  have hab : -(n : ℝ) ≤ n := ht.1.trans ht.2
  have he := cellWeakActual_difference_decay hab hG hv V hV
    (cellSourceSlice (fun r => cellQ0 (f r)))
    (fun r j => cellSourceSlice (fun s x => F s x j) r)
    (D.trace n) (D.trace m) (D.slice n) (D.slice m)
    (D.curve n) ((D.curve m).mono hsub) (D.mean n) (fun r hr => D.mean m r (hsub hr)) t ht
  rw [D.initial, zero_sub, norm_neg] at he
  have hb := D.bound m (-(n : ℝ)) (hsub ⟨le_rfl, hab⟩)
  have hmul := mul_le_mul_of_nonneg_left hb (Real.exp_pos (-(4 * Real.pi ^ 2) * (t - -(n : ℝ)))).le
  simpa only [sub_neg_eq_add] using he.trans hmul

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.CycleEvolution

/-! Complete-space pullback limits of the actual finite-past cell traces. -/

variable {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {hG : IsCellMetric G}
  {v : ℝ → Vec 2 → Vec 2} {hv : IsCellDrift v} {V : ℝ}
  {hV : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2}
  {f : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {R : ℝ}

/-- The scalar exponential budget of finite-past comparisons tends to zero. -/
theorem cellPullback_exp_budget_tendsto_zero (t R : ℝ) :
    Tendsto (fun n : ℕ => Real.exp (-(4 * Real.pi ^ 2) * (t + n)) * R) atTop (𝓝 0) := by
  have harg : Tendsto (fun n : ℕ => t + (n : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop t tendsto_natCast_atTop_atTop
  have hneg : -(4 * Real.pi ^ 2) < 0 :=
    neg_neg_of_pos (mul_pos (by norm_num) (sq_pos_of_pos Real.pi_pos))
  simpa only [Function.comp_def, zero_mul] using
    (Real.tendsto_exp_atBot.comp (harg.const_mul_atTop_of_neg hneg)).mul_const R

/-- At each fixed time, the actual finite-past traces form a Cauchy sequence. -/
theorem CellPullbackApproximationData.trace_cauchy
    (D : CellPullbackApproximationData G hG v hv V hV f F R) (t : ℝ) :
    CauchySeq (fun n => D.trace n t) := by
  have he := cellPullback_exp_budget_tendsto_zero t R
  apply Metric.cauchySeq_iff'.mpr
  intro ε hε
  obtain ⟨T, hT⟩ := exists_nat_gt |t|
  have hev := (he.eventually (gt_mem_nhds (sq_pos_of_pos hε))).and (eventually_ge_atTop T)
  obtain ⟨N, hN, hNT⟩ := hev.exists
  have hNr : (T : ℝ) ≤ N := by exact_mod_cast hNT
  have htN : t ∈ Icc (-(N : ℝ)) N := by
    constructor
    · have := neg_abs_le t; linarith
    · have := le_abs_self t; linarith
  refine ⟨N, fun n hn => ?_⟩
  have hd := D.difference_bound hn htN
  rw [dist_eq_norm, norm_sub_rev]
  have hs : ‖D.trace N t - D.trace n t‖ ^ 2 < ε ^ 2 := hd.trans_lt hN
  nlinarith [norm_nonneg (D.trace N t - D.trace n t)]

/-- Completeness of spatial L² supplies a genuine all-time trace limit. -/
theorem CellPullbackApproximationData.trace_exists_limit
    (D : CellPullbackApproximationData G hG v hv V hV f F R) (t : ℝ) :
    ∃ u : ComplexCellL2, Tendsto (fun n => D.trace n t) atTop (𝓝 u) :=
  cauchySeq_tendsto_of_complete (D.trace_cauchy t)

/-- The all-time pullback trace is the actual L² limit of the finite-past solutions. -/
def CellPullbackApproximationData.limit
    (D : CellPullbackApproximationData G hG v hv V hV f F R) (t : ℝ) : ComplexCellL2 :=
  Classical.choose (D.trace_exists_limit t)

/-- The chosen pullback trace has the defining convergence at every time. -/
theorem CellPullbackApproximationData.limit_tendsto
    (D : CellPullbackApproximationData G hG v hv V hV f F R) (t : ℝ) :
    Tendsto (fun n => D.trace n t) atTop (𝓝 (D.limit t)) :=
  Classical.choose_spec (D.trace_exists_limit t)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! One common H¹-a.e. state for the assembled actual finite-past trajectory. -/

variable {s : ℝ} {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {hG : IsCellMetric G}
  {v : ℝ → Vec 2 → Vec 2} {hv : IsCellDrift v} {V : ℝ}
  {hV : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2}
  {f : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
  {initial : ComplexCellL2} {R : ℝ}

/-- The common H¹-a.e. state of the actual finite-past solution. -/
def CellFinitePastApproximationData.pastState
    (D : CellFinitePastApproximationData s G hG v hv V hV f F initial R) (t : ℝ) : TorusHk 1 ℂ :=
  cellH1CanonicalLift (D.pastTrace t)

/-- The assembled finite-past trajectory solves the actual equation on every finite subinterval. -/
theorem CellFinitePastApproximationData.past_local_curve
    (D : CellFinitePastApproximationData s G hG v hv V hV f F initial R)
    {a b : ℝ} (_hab : a ≤ b) (hs : s ≤ a) :
    CellWeakHilbertCurve a b D.pastTrace D.pastState
      (fun t => cellDualDerivative ⟨G, v, 0, 0⟩ hG V hv.1 hV t (D.pastState t)
        (cellSourceSlice (fun r => cellQ0 (f r)) t)
        (fun j => cellSourceSlice (fun r x => F r x j) t)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (b - s)
  have hsub : Icc a b ⊆ Icc s (s + N) := Icc_subset_Icc hs (by linarith)
  have h := (D.curve N).mono hsub
  have he : ∀ t ∈ Icc a b, D.pastTrace t = D.trace N t :=
    fun t ht => D.pastTrace_eq (hsub ht)
  have hw : CellWeakHilbertCurve a b D.pastTrace (D.slice N)
      (fun t => cellDualDerivative ⟨G, v, 0, 0⟩ hG V hv.1 hV t (D.slice N t)
        (cellSourceSlice (fun r => cellQ0 (f r)) t)
        (fun j => cellSourceSlice (fun r x => F r x j) t)) := by
    refine ⟨D.pastTrace_continuousOn.mono (fun t ht => hs.trans ht.1), h.state, h.dual, ?_, ?_⟩
    · filter_upwards [h.agrees, ae_restrict_mem measurableSet_Icc] with t ht hti
      rw [he t hti]
      exact ht
    · intro r hr t ht hrt z
      rw [he r hr, he t ht]
      exact h.increment r hr t ht hrt z
  have hstate : D.slice N =ᵐ[volume.restrict (Icc a b)] D.pastState := by
    filter_upwards [hw.agrees] with t ht
    simp only [CellFinitePastApproximationData.pastState, ht, cellH1CanonicalLift_of_H1]
  apply hw.congr_state_dual hstate
  filter_upwards [hstate] with t ht
  rw [ht]

/-- The canonical finite-past H¹ state is locally L² on every clipped compact interval. -/
theorem CellFinitePastApproximationData.past_compact_curve
    (D : CellFinitePastApproximationData s G hG v hv V hV f F initial R) (n : ℕ) :
    MemLp D.pastState 2 (volume.restrict (Icc (-(n : ℝ)) n ∩ Ici s)) ∧
      ∀ᵐ t ∂volume.restrict (Icc (-(n : ℝ)) n ∩ Ici s),
        D.pastTrace t = AVRegularity.CoupledEnergy.Galerkin.torusHkValueCLM (D.pastState t) := by
  have he : Icc (-(n : ℝ)) n ∩ Ici s = Icc (max (-(n : ℝ)) s) n := by
    ext t
    simp only [mem_inter_iff, mem_Icc, mem_Ici, max_le_iff]
    tauto
  rw [he]
  rcases le_or_gt (max (-(n : ℝ)) s) (n : ℝ) with hab | hba
  · exact ⟨(D.past_local_curve hab (le_max_right _ _)).state,
      (D.past_local_curve hab (le_max_right _ _)).agrees⟩
  · rw [Icc_eq_empty_of_lt hba, Measure.restrict_empty]
    exact ⟨memLp_measure_zero, by simp⟩

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.CycleEvolution

/-! Mean, uniform bounds, and quantitative approximation of the actual pullback trace. -/

section
variable {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {hG : IsCellMetric G}
  {v : ℝ → Vec 2 → Vec 2} {hv : IsCellDrift v} {V : ℝ}
  {hV : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2}
  {f : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {R : ℝ}

/-- Every fixed time lies in all sufficiently large finite-past approximation intervals. -/
theorem cellPullback_eventually_time_mem (t : ℝ) :
    ∀ᶠ n : ℕ in atTop, t ∈ Icc (-(n : ℝ)) n := by
  obtain ⟨N, hN⟩ := exists_nat_gt |t|
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · have := neg_abs_le t; linarith
  · have := le_abs_self t; linarith

/-- The actual pullback trace retains the horizon-independent squared norm bound. -/
theorem CellPullbackApproximationData.limit_bound
    (D : CellPullbackApproximationData G hG v hv V hV f F R) (t : ℝ) :
    ‖D.limit t‖ ^ 2 ≤ R := by
  have hlim := (D.limit_tendsto t).norm.pow 2
  apply le_of_tendsto hlim
  filter_upwards [cellPullback_eventually_time_mem t] with n hn
  exact D.bound n t hn

/-- The bounded mean operator preserves zero mean in the actual pullback limit. -/
theorem CellPullbackApproximationData.limit_mean
    (D : CellPullbackApproximationData G hG v hv V hV f F R) (t : ℝ) :
    cellMean (D.limit t) = 0 := by
  have hlim := cellMeanCLM.continuous.continuousAt.tendsto.comp (D.limit_tendsto t)
  have he : (fun n => cellMeanCLM (D.trace n t)) =ᶠ[atTop] fun _ => (0 : ℂ) := by
    filter_upwards [cellPullback_eventually_time_mem t] with n hn
    rw [cellMeanCLM_apply, D.mean n t hn]
  have hz : Tendsto (fun n => cellMeanCLM (D.trace n t)) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' he.symm
  rw [← cellMeanCLM_apply]
  exact tendsto_nhds_unique hlim hz

/-- The finite-past trace approximates its actual all-time limit at the homogeneous spectral rate. -/
theorem CellPullbackApproximationData.limit_difference_bound
    (D : CellPullbackApproximationData G hG v hv V hV f F R)
    {n : ℕ} {t : ℝ} (ht : t ∈ Icc (-(n : ℝ)) n) :
    ‖D.trace n t - D.limit t‖ ^ 2 ≤ Real.exp (-(4 * Real.pi ^ 2) * (t + n)) * R := by
  have hlim : Tendsto (fun m => ‖D.trace n t - D.trace m t‖ ^ 2) atTop
      (𝓝 (‖D.trace n t - D.limit t‖ ^ 2)) :=
    (tendsto_const_nhds.sub (D.limit_tendsto t)).norm.pow 2
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop n] with m hm
  exact D.difference_bound hm ht
end

/-! Uniform convergence on compact time intervals and continuity of the actual pullback trace. -/

section
variable {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {hG : IsCellMetric G}
  {v : ℝ → Vec 2 → Vec 2} {hv : IsCellDrift v} {V : ℝ}
  {hV : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2}
  {f : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {R : ℝ}

/-- The actual pullback approximations converge uniformly on every compact time interval. -/
theorem CellPullbackApproximationData.limit_uniformOn
    (D : CellPullbackApproximationData G hG v hv V hV f F R) (a b : ℝ) :
    TendstoUniformlyOn D.trace D.limit atTop (Icc a b) := by
  have hR : 0 ≤ R := (sq_nonneg ‖D.trace 0 0‖).trans (D.bound 0 0 (by simp))
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have he := (cellPullback_exp_budget_tendsto_zero a R).eventually
    (gt_mem_nhds (sq_pos_of_pos hε))
  filter_upwards [he, cellPullback_eventually_time_mem a, cellPullback_eventually_time_mem b]
    with n hn ha hb
  intro t ht
  have hti : t ∈ Icc (-(n : ℝ)) n := (Icc_subset_Icc ha.1 hb.2) ht
  have hd := D.limit_difference_bound hti
  have hRate : 0 ≤ 4 * Real.pi ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have hm : Real.exp (-(4 * Real.pi ^ 2) * (t + n)) * R ≤
      Real.exp (-(4 * Real.pi ^ 2) * (a + n)) * R := by
    apply mul_le_mul_of_nonneg_right _ hR
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (add_le_add ht.1 (le_rfl : (n : ℝ) ≤ n)) (neg_nonpos.mpr hRate)
  have hs := (hd.trans hm).trans_lt hn
  rw [dist_eq_norm, norm_sub_rev]
  nlinarith [norm_nonneg (D.trace n t - D.limit t)]

/-- The actual pullback trace is continuous on every compact interval. -/
theorem CellPullbackApproximationData.limit_continuousOn
    (D : CellPullbackApproximationData G hG v hv V hV f F R) (a b : ℝ) :
    ContinuousOn D.limit (Icc a b) := by
  apply (D.limit_uniformOn a b).continuousOn
  apply Filter.Eventually.frequently
  filter_upwards [cellPullback_eventually_time_mem a, cellPullback_eventually_time_mem b]
    with n ha hb
  exact (D.curve n).trace.mono (Icc_subset_Icc ha.1 hb.2)

/-- The actual all-time pullback trace is strongly continuous into spatial L². -/
theorem CellPullbackApproximationData.limit_continuous
    (D : CellPullbackApproximationData G hG v hv V hV f F R) : Continuous D.limit := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (D.limit_continuousOn (t - 1) (t + 1)).continuousAt
    (Icc_mem_nhds (by linarith) (by linarith))
end

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization
namespace AVRegularity.CycleEvolution

/-! The actual existence-and-uniqueness construction is a complex linear cell solution map. -/

def cellFiniteEnergyEvolutionLinear {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (hκ : AEStronglyMeasurable C.κ (volume.restrict (Icc a b)))
    (hκb : ∀ t, ‖C.κ t‖ ≤ k) : CellFiniteEnergyDatum a b →ₗ[ℂ] CellFiniteEnergyCarrier a b := by
  let sol : CellFiniteEnergyDatum a b → CellFiniteEnergyCarrier a b := fun d =>
    Classical.choose (cellFiniteEnergyEvolution_exists hab C hG V k hv hb hκ hκb d)
  have hsol d : IsCellFiniteEnergyEvolution C hG V hv hb d (sol d) :=
    Classical.choose_spec (cellFiniteEnergyEvolution_exists hab C hG V k hv hb hκ hκb d)
  exact
    { toFun := sol
      map_add' := fun d e => cellFiniteEnergyEvolution_unique hab C hG V k hv hb hκb
        (d + e) (sol (d + e)) (sol d + sol e) (hsol (d + e)) ((hsol d).add C hG V hv hb (hsol e))
      map_smul' := fun c d => cellFiniteEnergyEvolution_unique hab C hG V k hv hb hκb
        (c • d) (sol (c • d)) (c • sol d) (hsol (c • d)) ((hsol d).complex_smul C hG V hv hb c) }

theorem cellFiniteEnergyEvolutionLinear_solves {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (hκ : AEStronglyMeasurable C.κ (volume.restrict (Icc a b)))
    (hκb : ∀ t, ‖C.κ t‖ ≤ k) (d : CellFiniteEnergyDatum a b) :
    IsCellFiniteEnergyEvolution C hG V hv hb d
      (cellFiniteEnergyEvolutionLinear hab C hG V k hv hb hκ hκb d) :=
  Classical.choose_spec (cellFiniteEnergyEvolution_exists hab C hG V k hv hb hκ hκb d)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.CycleEvolution

/-! Identification of the actual pullback trace with the finite-interval cell equation. -/

variable {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {hG : IsCellMetric G}
  {v : ℝ → Vec 2 → Vec 2} {hv : IsCellDrift v} {V : ℝ}
  {hV : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2}
  {f : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {R : ℝ}

/-- On each finite interval, the pullback limit equals the actual solution with its entering trace. -/
theorem CellPullbackApproximationData.limit_eq_finite
    (D : CellPullbackApproximationData G hG v hv V hV f F R)
    {a b : ℝ} (hab : a ≤ b) (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice (fun t => cellDualDerivative ⟨G, v, 0, 0⟩ hG V hv.1 hV t
      (slice t) (cellSourceSlice (fun r => cellQ0 (f r)) t)
      (fun j => cellSourceSlice (fun r x => F r x j) t)))
    (hm : ∀ t ∈ Icc a b, cellMean (u t) = 0) (hi : u a = D.limit a) :
    ∀ t ∈ Icc a b, D.limit t = u t := by
  intro t ht
  have hL : Tendsto (fun n => ‖D.trace n t - u t‖ ^ 2) atTop
      (𝓝 (‖D.limit t - u t‖ ^ 2)) :=
    ((D.limit_tendsto t).sub tendsto_const_nhds).norm.pow 2
  have hR : Tendsto (fun n => Real.exp (-(4 * Real.pi ^ 2) * (t - a)) *
      ‖D.trace n a - D.limit a‖ ^ 2) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] using
      (((D.limit_tendsto a).sub (tendsto_const_nhds (x := D.limit a))).norm.pow 2).const_mul
        (Real.exp (-(4 * Real.pi ^ 2) * (t - a)))
  have hle : ‖D.limit t - u t‖ ^ 2 ≤ 0 := by
    apply le_of_tendsto_of_tendsto hL hR
    filter_upwards [cellPullback_eventually_time_mem a, cellPullback_eventually_time_mem b]
      with n ha hb
    have hsub : Icc a b ⊆ Icc (-(n : ℝ)) n := Icc_subset_Icc ha.1 hb.2
    have he := cellWeakActual_difference_decay hab hG hv V hV
      (cellSourceSlice (fun r => cellQ0 (f r)))
      (fun r j => cellSourceSlice (fun s x => F s x j) r)
      (D.trace n) u (D.slice n) slice ((D.curve n).mono hsub) h
      (fun r hr => D.mean n r (hsub hr)) hm t ht
    simpa only [hi] using he
  have hn : ‖D.limit t - u t‖ = 0 := by nlinarith [norm_nonneg (D.limit t - u t)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- The pullback limit solves the actual weak cell equation on every finite interval. -/
theorem CellPullbackApproximationData.limit_local_solution
    (D : CellPullbackApproximationData G hG v hv V hV f F R)
    (hfm : Measurable (Function.uncurry f)) (hFm : Measurable (Function.uncurry F))
    (hf : cellUlNorm univ f < ⊤) (hF : cellUlNorm univ F < ⊤)
    {a b : ℝ} (hab : a ≤ b) :
    ∃ slice : ℝ → TorusHk 1 ℂ, CellWeakHilbertCurve a b D.limit slice
      (fun t => cellDualDerivative ⟨G, v, 0, 0⟩ hG V hv.1 hV t (slice t)
        (cellSourceSlice (fun r => cellQ0 (f r)) t)
        (fun j => cellSourceSlice (fun r x => F r x j) t)) := by
  obtain ⟨u, slice, h, hi, hm, _⟩ := cellFinite_meanZero_Hilbert_bounded hab univ (subset_univ _)
    hG hv V hV f F hfm hFm hf hF (D.limit a) (D.limit_mean a)
  have he := D.limit_eq_finite hab u slice h hm hi
  refine ⟨slice, ⟨D.limit_continuous.continuousOn, h.state, h.dual, ?_, ?_⟩⟩
  · filter_upwards [h.agrees, ae_restrict_mem measurableSet_Icc] with t ht hti
    rw [he t hti]
    exact ht
  · intro s hs t ht hst z
    rw [he s hs, he t ht]
    exact h.increment s hs t ht hst z

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Drift-independent short-interval gradient budgets for the actual finite-past solution. -/

/-- The actual finite-past state has a uniform gradient budget on every short interval. -/
theorem CellFinitePastApproximationData.gradient_short_bound
    {s : ℝ} {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {hG : IsCellMetric G}
    {v : ℝ → Vec 2 → Vec 2} {hv : IsCellDrift v} {V : ℝ}
    {hV : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2}
    {f : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {R : ℝ}
    {initial : ComplexCellL2}
    (D : CellFinitePastApproximationData s G hG v hv V hV f F initial R)
    (hfm : Measurable (Function.uncurry f)) (hFm : Measurable (Function.uncurry F))
    (hf : cellUlNorm (Ici s) f < ⊤) (hF : cellUlNorm (Ici s) F < ⊤) {a b : ℝ} (hab : a ≤ b) (hsa : s ≤ a) (hl : b - a ≤ 1) :
    (∫ t in a..b, ∑ j, ‖cellDerivativeCLM j (D.pastState t)‖ ^ 2) ≤
      2 * R + 2 * (4 * (cellUlNorm (Ici s) f).toReal ^ 2 + 8 * (cellUlNorm (Ici s) F).toReal ^ 2) := by
  have hcurve := D.past_local_curve hab hsa
  have hfp := cellUl_memLp_product_interval (Ici s) f hfm hf a b (fun _ ht => hsa.trans ht.1)
  have hFp := cellUl_memLp_product_interval (Ici s) F hFm hF a b (fun _ ht => hsa.trans ht.1)
  have hS := cellSourceSlice_memLp (Icc a b) (fun r => cellQ0 (f r))
    (cellQ0_memLp_product (Icc a b) f hfm hfp)
  have hflux (j : Fin 2) := cellSourceSlice_memLp (Icc a b) (fun r x => F r x j)
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).comp_memLp' hFp)
  have he := cellWeakActual_local_energy hab hG hv V hV D.pastTrace D.pastState _ _ hS hflux hcurve
    (fun t ht => D.pastTrace_mean (hsa.trans ht.1))
  have hb := cellMeanFreeForcingBudget_short_bound (Ici s) f F hfm hFm hf hF hab hl (fun _ ht => hsa.trans ht.1)
  change (∫ t in a..b,
    ‖cellSourceSlice (fun r => cellQ0 (f r)) t‖ ^ 2 +
      8 * ∑ j, ‖cellSourceSlice (fun r x => F r x j) t‖ ^ 2) ≤ _ at hb
  have hu := D.pastTrace_bound hsa
  nlinarith [sq_nonneg ‖D.pastTrace b‖]

/-! Public raw finite-past solutions from compatible actual Galerkin traces. -/

/-- The actual finite-past Galerkin trajectory admits a public raw solution with its exact trace. -/
theorem CellFinitePastApproximationData.exists_past_raw_solution
    {s : ℝ} {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {hG : IsCellMetric G}
    {v : ℝ → Vec 2 → Vec 2} {hv : IsCellDrift v} {V : ℝ}
    {hV : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2}
    {f : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    {initial : ComplexCellL2} {R : ℝ}
    (D : CellFinitePastApproximationData s G hG v hv V hV f F initial R)
    (hfm : Measurable (Function.uncurry f)) (hFm : Measurable (Function.uncurry F))
    (hf : cellUlNorm (Ici s) f < ⊤) (hF : cellUlNorm (Ici s) F < ⊤) :
    ∃ raw : ℝ → RawJet2 1 ℂ,
      IsCellSolution (Ici s) ⟨G, v, 0, 0⟩ (fun t => cellQ0 (f t)) F raw ∧
      (∀ t, (D.pastTrace t : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] cellValue raw t) ∧
      (∀ᵐ t ∂volume.restrict (Ici s), ∀ j,
        ((D.pastState t).val j : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] raw t j) := by
  exact cellDomainLocalHilbert_exists_raw_solution (Ici s) ordConnected_Ici ⟨G, v, 0, 0⟩ hG V hv.1 hV
    (fun t => cellQ0 (f t)) F
    (fun a ha b _ _ => cellQ0_memLp_product (Icc a b) f hfm
      (cellUl_memLp_product_interval (Ici s) f hfm hf a b (fun _ ht => ha.trans ht.1)))
    (fun a ha b _ _ => cellUl_memLp_product_interval (Ici s) F hFm hF a b (fun _ ht => ha.trans ht.1))
    D.pastTrace D.pastState D.pastTrace_continuousOn
    (fun n => (D.past_compact_curve n).1) (fun n => (D.past_compact_curve n).2)
    (fun _ ha _ _ hab => D.past_local_curve hab ha)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.CycleEvolution

/-! A common almost-everywhere H¹ lift of the actual all-time pullback trace. -/

variable {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {hG : IsCellMetric G}
  {v : ℝ → Vec 2 → Vec 2} {hv : IsCellDrift v} {V : ℝ}
  {hV : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2}
  {f : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {R : ℝ}

/-- The actual all-time trace's canonical H¹ representative, defined at every time. -/
def CellPullbackApproximationData.state
    (D : CellPullbackApproximationData G hG v hv V hV f F R) (t : ℝ) : TorusHk 1 ℂ :=
  cellH1CanonicalLift (D.limit t)

/-- The common H¹ lift solves the actual equation on every finite interval. -/
theorem CellPullbackApproximationData.state_local_curve
    (D : CellPullbackApproximationData G hG v hv V hV f F R)
    (hfm : Measurable (Function.uncurry f)) (hFm : Measurable (Function.uncurry F))
    (hf : cellUlNorm univ f < ⊤) (hF : cellUlNorm univ F < ⊤)
    {a b : ℝ} (hab : a ≤ b) :
    CellWeakHilbertCurve a b D.limit D.state
      (fun t => cellDualDerivative ⟨G, v, 0, 0⟩ hG V hv.1 hV t (D.state t)
        (cellSourceSlice (fun r => cellQ0 (f r)) t)
        (fun j => cellSourceSlice (fun r x => F r x j) t)) := by
  obtain ⟨slice, h⟩ := D.limit_local_solution hfm hFm hf hF hab
  have hs : slice =ᵐ[volume.restrict (Icc a b)] D.state := by
    filter_upwards [h.agrees] with t ht
    simp only [CellPullbackApproximationData.state, ht, cellH1CanonicalLift_of_H1]
  apply h.congr_state_dual hs
  filter_upwards [hs] with t ht
  rw [ht]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Actual Bloch evolution is the baseline weak equation with the explicit bounded perturbation datum. -/

theorem cellBlochEvolution_transfer {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (δ : Fin 2 → ℂ) (q : Lp ℂ ∞ (volume.restrict (Icc a b)))
    (d : CellFiniteEnergyDatum a b) (z : CellFiniteEnergyCarrier a b)
    (hz : IsCellFiniteEnergyEvolution
      { C with θ := C.θ + δ, κ := fun t => C.κ t + q t } hG V hv hb d z) :
    IsCellFiniteEnergyEvolution C hG V hv hb
      (cellBlochExternalDatum δ d + cellBlochPerturbationDatumCLM hab C hG V hv hb δ q z) z := by
  obtain ⟨u, slice, hu, hi, ht⟩ := hz
  let P := cellBlochPerturbationDatumCLM hab C hG V hv hb δ q z
  let e := cellBlochExternalDatum δ d
  have hp := cellBlochPerturbationScalarCLM_ae hab C hG V hv hb δ q u slice _ hu z ht
  have hf : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ j : Fin 2,
      P.2.2 j t = cellBlochPerturbationFlux C hG δ t (slice t) j := by
    rw [ae_all_iff]
    intro j
    exact cellBlochPerturbationFluxCLM_ae hab C hG δ j u slice _ hu z ht
  have he := cellBlochExternalDatum_scalar_ae δ d
  have ha := cellFiniteEnergyDatum_add_scalar_ae e P
  have hfa := cellFiniteEnergyDatum_add_flux_ae e P
  refine ⟨u, slice, hu.dual_congr ?_, ?_, ht⟩
  · filter_upwards [hp, hf, he, ha, hfa] with t hp' hf' he' ha' hfa'
    rw [cellDualDerivative_blochPerturbation]
    congr 1
    · change cellBlochPerturbationScalar C hG V hv hb δ q t (slice t) +
        (d.2.1 t + ∑ j, cellScalarCLM (Complex.I * δ j) (d.2.2 j t)) =
          (e.2.1 + P.2.1) t
      change _ = (e + P).2.1 t
      rw [ha']
      change _ = (cellBlochExternalDatum δ d).2.1 t + P.2.1 t
      rw [he']
      change _ = (d.2.1 t + ∑ j : Fin 2, (Complex.I * δ j) • d.2.2 j t) +
        cellBlochPerturbationScalarCLM hab C hG V hv hb δ q z t
      rw [hp']
      simp only [cellScalarCLM_smul]
      exact add_comm _ _
    · funext j
      change cellBlochPerturbationFlux C hG δ t (slice t) j + d.2.2 j t =
        (e + P).2.2 j t
      rw [hfa' j, hf' j]
      exact add_comm _ _
  · change u a = d.1 + 0
    simpa using hi

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Drift-independent unit-window gradient budgets for the actual pullback solution. -/

/-- The actual all-time pullback state has a uniformly bounded unit-window gradient budget. -/
theorem CellPullbackApproximationData.gradient_window_bound
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {hG : IsCellMetric G}
    {v : ℝ → Vec 2 → Vec 2} {hv : IsCellDrift v} {V : ℝ}
    {hV : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2}
    {f : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {R : ℝ}
    (D : CellPullbackApproximationData G hG v hv V hV f F R)
    (hfm : Measurable (Function.uncurry f)) (hFm : Measurable (Function.uncurry F))
    (hf : cellUlNorm univ f < ⊤) (hF : cellUlNorm univ F < ⊤) (a : ℝ) :
    (∫ t in a..a + 1, ∑ j, ‖cellDerivativeCLM j (D.state t)‖ ^ 2) ≤
      2 * R + 2 * (4 * (cellUlNorm univ f).toReal ^ 2 + 8 * (cellUlNorm univ F).toReal ^ 2) := by
  have hab : a ≤ a + 1 := by linarith
  have hcurve := D.state_local_curve hfm hFm hf hF hab
  have hfp := cellUl_memLp_product_interval univ f hfm hf a (a + 1) (subset_univ _)
  have hFp := cellUl_memLp_product_interval univ F hFm hF a (a + 1) (subset_univ _)
  have hS := cellSourceSlice_memLp (Icc a (a + 1)) (fun r => cellQ0 (f r))
    (cellQ0_memLp_product (Icc a (a + 1)) f hfm hfp)
  have hflux (j : Fin 2) := cellSourceSlice_memLp (Icc a (a + 1)) (fun r x => F r x j)
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).comp_memLp' hFp)
  have he := cellWeakActual_local_energy hab hG hv V hV D.limit D.state _ _ hS hflux hcurve
    (fun t _ => D.limit_mean t)
  have hb := cellMeanFreeForcingBudget_short_bound univ f F hfm hFm hf hF hab
    (by linarith) (subset_univ (Icc a (a + 1)))
  change (∫ t in a..a + 1,
    ‖cellSourceSlice (fun r => cellQ0 (f r)) t‖ ^ 2 +
      8 * ∑ j, ‖cellSourceSlice (fun r x => F r x j) t‖ ^ 2) ≤ _ at hb
  have hu := D.limit_bound a
  nlinarith [sq_nonneg ‖D.limit (a + 1)‖]

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.CycleEvolution

/-! Uniqueness of the bounded all-time mean-zero cell inverse. -/

/-- Bounded all-time mean-zero public solutions with common uniformly local forcing agree. -/
theorem cellAllTimeInverse_unique
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (f : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hfm : Measurable (Function.uncurry f)) (hFm : Measurable (Function.uncurry F))
    (hf : cellUlNorm univ f < ⊤) (hF : cellUlNorm univ F < ⊤)
    (D D' : ℝ → RawJet2 1 ℂ)
    (hD : IsCellInverseValue ⟨G, v, 0, 0⟩ (fun t => cellQ0 (f t)) F D)
    (hD' : IsCellInverseValue ⟨G, v, 0, 0⟩ (fun t => cellQ0 (f t)) F D') :
    ∀ t, cellValue D t =ᵐ[volume.restrict AVenhance.unitCube] cellValue D' t := by
  obtain ⟨V, hV⟩ := hv.2.1
  let K := (cellEnergyNorm univ D).toReal + (cellEnergyNorm univ D').toReal
  intro t
  have hbound (n : ℕ) : ‖cellRawTrace D t - cellRawTrace D' t‖ ^ 2 ≤
      Real.exp (-(4 * Real.pi ^ 2) * (n : ℝ)) * K ^ 2 := by
    have hst : t - n ≤ t := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    have hsrc := cellQ0_memLp_product (Icc (t - n) t) f hfm
      (cellUl_memLp_product_interval univ f hfm hf (t - n) t (subset_univ _))
    have hFp := cellUl_memLp_product_interval univ F hFm hF (t - n) t (subset_univ _)
    have he := cellRaw_meanZero_difference_decay hst hG hv V hV (fun r => cellQ0 (f r)) F hsrc hFp D D'
      (cellSolution_restrict (subset_univ (Icc (t - n) t)) ordConnected_Icc hD.1)
      (cellSolution_restrict (subset_univ (Icc (t - n) t)) ordConnected_Icc hD'.1)
      (fun r _ => hD.2.1 r) (fun r _ => hD'.2.1 r) t ⟨hst, le_rfl⟩
    have hnorm : ‖cellRawTrace D (t - n) - cellRawTrace D' (t - n)‖ ≤ K :=
      (norm_sub_le _ _).trans (add_le_add
        (cellRawTrace_norm_le_energy D hD.1 hD.2.2 (t - n))
        (cellRawTrace_norm_le_energy D' hD'.1 hD'.2.2 (t - n)))
    have hs : ‖cellRawTrace D (t - n) - cellRawTrace D' (t - n)‖ ^ 2 ≤ K ^ 2 := by
      simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg _) hnorm
    rw [show t - (t - (n : ℝ)) = n by ring] at he
    exact he.trans (mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le)
  have hlim : Tendsto (fun n : ℕ => Real.exp (-(4 * Real.pi ^ 2) * (n : ℝ)) * K ^ 2)
      atTop (𝓝 0) := by
    simpa only [zero_add] using cellPullback_exp_budget_tendsto_zero 0 (K ^ 2)
  have hz : ‖cellRawTrace D t - cellRawTrace D' t‖ ^ 2 ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hbound
  have hn : ‖cellRawTrace D t - cellRawTrace D' t‖ = 0 := by
    nlinarith [norm_nonneg (cellRawTrace D t - cellRawTrace D' t)]
  have heq := sub_eq_zero.mp (norm_eq_zero.mp hn)
  have htrace := cellRawTrace_ae D t (hD.1.2.2.1 t (mem_univ _)).1
  rw [heq] at htrace
  exact htrace.symm.trans (cellRawTrace_ae D' t (hD'.1.2.2.1 t (mem_univ _)).1)

end AVRegularity.CycleEvolution
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Public all-time raw energy solutions constructed by the actual finite-past pullback limit. -/

/-- The actual pullback limit supplies a public raw all-time solution with its exact L² trace. -/
theorem CellPullbackApproximationData.exists_raw_solution
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {hG : IsCellMetric G}
    {v : ℝ → Vec 2 → Vec 2} {hv : IsCellDrift v} {V : ℝ}
    {hV : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2}
    {f : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {R : ℝ}
    (D : CellPullbackApproximationData G hG v hv V hV f F R)
    (hfm : Measurable (Function.uncurry f)) (hFm : Measurable (Function.uncurry F))
    (hf : cellUlNorm univ f < ⊤) (hF : cellUlNorm univ F < ⊤) :
    ∃ raw : ℝ → RawJet2 1 ℂ,
      IsCellSolution univ ⟨G, v, 0, 0⟩ (fun t => cellQ0 (f t)) F raw ∧
      (∀ t, (D.limit t : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] cellValue raw t) ∧
      (∀ᵐ t ∂volume, ∀ j, ((D.state t).val j : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] raw t j) := by
  exact cellLocalHilbert_exists_raw_solution ⟨G, v, 0, 0⟩ hG V hv.1 hV
    (fun t => cellQ0 (f t)) F
    (fun a b _ => cellQ0_memLp_product (Icc a b) f hfm
      (cellUl_memLp_product_interval univ f hfm hf a b (subset_univ _)))
    (fun a b _ => cellUl_memLp_product_interval univ F hFm hF a b (subset_univ _))
    D.limit D.state D.limit_continuous
    (fun _ _ hab => D.state_local_curve hfm hFm hf hF hab)

end AVRegularity.CycleEvolution
end
