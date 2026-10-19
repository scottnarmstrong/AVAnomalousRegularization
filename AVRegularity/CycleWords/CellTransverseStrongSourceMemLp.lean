-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.CellMetricStoredWordResidualTimeIntegrability
public import AVRegularity.CycleWords.DerivativeSourceDensity
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev Set
namespace AVRegularity.CycleWords

/-! Every actual stored source word satisfies the clipped weighted scalar estimate with its true residuals. -/

open AVRegularity.Weighted

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem cellMetric_storedWords_clipped_value_energy_sum {K : ℕ}
    (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hv : ∀ t ∈ Icc a b, ContDiff ℝ 1 (v t))
    (hvm : Measurable (fun p : Icc a b × Vec 2 => v p.1 p.2))
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ j : Fin 2, fderiv ℝ (v t) x (basisVec j) j = 0)
    (Mv : ℝ) (hMv : 0 ≤ Mv) (hvb : ∀ t ∈ Icc a b, ∀ x, ‖v t x‖ ≤ Mv)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ t ∈ Icc a b, ∀ k j, ContDiff ℝ 1 (fun x => G t x k j))
    (hGm : Measurable (fun p : Icc a b × Vec 2 => G p.1 p.2))
    (hCell : IsCellMetric G)
    (hGs : ∀ t ∈ Icc a b, ∀ x, (G t x).IsSymm)
    (t₀ S ϖ : ℝ) (zc : Vec 2) (N m : ℕ) (Cw : ℕ → ℝ)
    (C : ChartWeights G v t₀ S ϖ zc N Cw) (hm : m ≤ N)
    (ha : t₀ ≤ a) (hb : b ≤ t₀ + S)
    (U H : ℝ → PlaneHk Set.univ K E)
    (W : ℝ → PlaneHk Set.univ (K + 1) E)
    (Q : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (hH : MemLp H 2 (volume.restrict (Icc a b)))
    (hQ : MemLp Q 2 (volume.restrict (Icc a b))) 
    (hcurve : ∀ α : JetIndex2 K, PlaneWeakHilbertCurve a b
      (fun t => planeJetReadoutOperator K α (U t))
      (fun t => planeWordH1SliceOperator K α (W t))
      (fun t => planeSourceDual (planeJetReadoutOperator K α (H t))
        (planeJetFluxOperator K α (Q t))))
    (B : ℝ) (hB : 0 < B) (ρ : ℝ) :
    let L := fun (α : JetIndex2 K) (t : ℝ) =>
      let u := fun t => planeJetReadoutOperator K α (U t)
      let slice := fun t => planeWordH1SliceOperator K α (W t)
      (∫ x, clipWeight B (C.W m t x) * ‖u t x‖ ^ 2) +
        (∫ s in a..t, ∫ x, (1 / 2) * clipWeight B (C.W m s x) *
          ‖(WithLp.toLp 2 (fun k => planeH1GradientOperator (slice s) k x) :
            PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2)
    let I := fun (α : JetIndex2 K) =>
      let u := fun t => planeJetReadoutOperator K α (U t)
      let slice := fun t => planeWordH1SliceOperator K α (W t)
      let T := planeIntervalTransport a b hab v (fun t ht => (hv t ht).continuous) Mv hvb
      let D := cellMetricIntervalDiffusion a b hab G
        (fun t ht k j => (hG t ht k j).continuous) hCell
      let F := fun t => planeJetFluxOperator K α (Q t) - D t (planeH1GradientOperator (slice t))
      let R := fun t => planeJetReadoutOperator K α (H t) + T t (planeH1GradientOperator (slice t))
      ((∫ x, clipWeight B (C.W m a x) * ‖u a x‖ ^ 2) +
          8 * (∫ s in a..b, ∫ x, clipWeight B (C.W m s x) *
            ‖(WithLp.toLp 2 (fun k => F s k x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) +
          2 * (∫ s in a..b, ∫ x, clipWeight B (C.W m s x) * (‖R s x‖ * ‖u s x‖)))
    ∀ t ∈ Icc a b,
      (∑ α : JetIndex2 K, factorialWeight ρ α.1.val * L α t) ≤
        (∑ α : JetIndex2 K, factorialWeight ρ α.1.val * I α) *
          Real.exp (18 * C.lam m * (t - a)) := by
  dsimp only
  intro t ht
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro α _
  have h := cellMetric_storedWord_clipped_value_energy_bound a b hab v hv hvm hdiv Mv hMv hvb
    G hG hGm hCell hGs t₀ S ϖ zc N m Cw C hm ha hb U H W Q hH hQ α
    (hcurve α) B hB t ht
  dsimp only at h
  exact (mul_le_mul_of_nonneg_left h (factorialWeight_nonneg ρ _)).trans_eq (by ring)

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Finite response sums cost only the number of response levels. Original
constituent and family vertex sums continue to use their graph row budgets. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  {L : Type*} [Fintype L]

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem native_norm_sum_sq_le (U : L → E) :
    ‖∑ j, U j‖ ^ 2 ≤ (Fintype.card L : ℝ) * ∑ j, ‖U j‖ ^ 2 := by
  classical
  have hn := pow_le_pow_left₀ (norm_nonneg (∑ j, U j)) (norm_sum_le Finset.univ U) 2
  have hc : (∑ j, ‖U j‖) ^ 2 ≤ (∑ _ : L, (1 : ℝ)) * ∑ j, ‖U j‖ ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (fun _ _ => zero_le_one) (fun j _ => sq_nonneg ‖U j‖)
    intro j _
    simp only [one_mul, le_refl]
  exact hn.trans (by simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using hc)

theorem planeFactorialDensity_sum_le {K : ℕ} (ρ : ℝ) (U : L → PlaneHk Set.univ K E) :
    ∀ᵐ z ∂volume, planeFactorialDensity ρ (∑ j, U j) z ≤
      (Fintype.card L : ℝ) * ∑ j, planeFactorialDensity ρ (U j) z := by
  classical
  filter_upwards [ae_all_iff.mpr (fun a : JetIndex2 K =>
    planeJetOrder_finite_sum_ae (Nat.le_of_lt_succ a.1.isLt) U a.2)] with z hz
  unfold planeFactorialDensity
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  rw [hz a, ← Finset.mul_sum]
  have hh := mul_le_mul_of_nonneg_left (native_norm_sum_sq_le (fun j => planeJetOrder (U j) a.1.val a.2 z))
    (factorialWeight_nonneg ρ a.1.val)
  simpa only [mul_assoc, mul_comm (Fintype.card L : ℝ), mul_left_comm (Fintype.card L : ℝ)] using hh

theorem weightedFactorialNormSq_sum_le {K : ℕ} (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ)
    (U : L → PlaneHk Set.univ K E) :
    weightedFactorialNormSq n ϖ zc ρ K (∑ j, U j) ≤
      (Fintype.card L : ℝ≥0∞) * ∑ j, weightedFactorialNormSq n ϖ zc ρ K (U j) := by
  classical
  have hm : AEMeasurable (Weighted.planeMomentPolynomial n ϖ zc) volume := by
    have hc : Continuous (Weighted.planeMomentPolynomial n ϖ zc) := by
      unfold Weighted.planeMomentPolynomial
      fun_prop
    exact hc.aemeasurable
  have hp (z : Vec 2) : 0 ≤ Weighted.planeMomentPolynomial n ϖ zc z := by
    unfold Weighted.planeMomentPolynomial
    positivity
  have hmq (j : L) : AEMeasurable (fun z => ENNReal.ofReal
      (Weighted.planeMomentPolynomial n ϖ zc z * planeFactorialDensity ρ (U j) z)) volume :=
    (hm.mul (nativeFactorialDensity_aemeasurable ρ (U j))).ennreal_ofReal
  simp_rw [weightedFactorialNormSq_density]
  rw [← lintegral_finsetSum' Finset.univ (f := fun j z => ENNReal.ofReal
    (Weighted.planeMomentPolynomial n ϖ zc z * planeFactorialDensity ρ (U j) z)) (fun j _ => hmq j),
    ← lintegral_const_mul' _ _ (by simp)]
  apply lintegral_mono_ae
  filter_upwards [planeFactorialDensity_sum_le ρ U] with z hz
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (hp z) (planeFactorialDensity_nonneg ρ (U j) z))]
  have hcard : (Fintype.card L : ℝ≥0∞) = ENNReal.ofReal (Fintype.card L : ℝ) := by simp
  rw [hcard, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hh := mul_le_mul_of_nonneg_left hz (hp z)
  rw [← Finset.mul_sum]
  simpa only [mul_assoc, mul_comm (Fintype.card L : ℝ), mul_left_comm (Fintype.card L : ℝ)] using hh

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The full constructed transport term on higher carriers, with its original shifted readout. -/

 def torusHigherShiftedFirstCLM (K : ℕ) (θ : Fin 2 → ℂ) (i : Fin 2) :
    TorusHk (K + 2) ℂ →L[ℝ] TorusHk K ℂ :=
  torusHigherFirstCLM K i + (torusHigherScalarCLM K (Complex.I * θ i)).comp
    (truncateTorusHk (by omega : K ≤ K + 2))

 theorem torusHigherShiftedFirstCLM_value (K : ℕ) (θ : Fin 2 → ℂ) (i : Fin 2)
    (U : TorusHk (K + 2) ℂ) :
    torusHkValueCLM (torusHigherShiftedFirstCLM K θ i U) =
      cellShiftedDerivativeCLM θ i
        (cellH2BaseCLM (truncateTorusHk (by omega : 2 ≤ K + 2) U)) := by
  simp only [torusHigherShiftedFirstCLM, add_apply, ContinuousLinearMap.comp_apply,
    map_add, torusHigherFirstCLM_value, torusHigherScalarCLM_value]
  rfl

 def constructedHigherAdvectionCLM (K : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (ν : ℝ) (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (θ : Fin 2 → ℂ) (t : ℝ) : TorusHk (K + 2) ℂ →L[ℝ] TorusHk K ℂ :=
  ∑ i : Fin 2, (constructedDriftEntryNativeCLM K hΛ hζ ν y₀ hv i t).comp
    (torusHigherShiftedFirstCLM K θ i)

 theorem constructedHigherAdvectionCLM_value (K : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (ν : ℝ) (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (V : ℝ) (hb : ∀ t x, ∑ j, ocCellDrift α q Λ ζ m ν y₀ t x j ^ 2 ≤ V ^ 2)
    (θ : Fin 2 → ℂ) (t : ℝ) (U : TorusHk (K + 2) ℂ) :
    torusHkValueCLM (constructedHigherAdvectionCLM K hΛ hζ ν y₀ hv θ t U) =
      ∑ i : Fin 2, cellDriftEntryCLM ⟨0, ocCellDrift α q Λ ζ m ν y₀, 0, 0⟩ V hv.1 hb t i
        (cellShiftedDerivativeCLM θ i
          (cellH2BaseCLM (truncateTorusHk (by omega : 2 ≤ K + 2) U))) := by
  simp only [constructedHigherAdvectionCLM, Fin.sum_univ_two, add_apply,
    ContinuousLinearMap.comp_apply, map_add, constructedDriftEntryNativeCLM_value K hΛ hζ ν y₀ hv V hb,
    torusHigherShiftedFirstCLM_value]

 def constructedHigherFullGeneratorCLM (K : ℕ)
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (ν : ℝ) (y₀ : Vec 2) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (θ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) :
    TorusHk (K + 2) ℂ →L[ℝ] TorusHk K ℂ :=
  torusHigherStrongDiffusionCLM K G θ t - constructedHigherAdvectionCLM K hΛ hζ ν y₀ hv θ t +
    (torusHigherScalarCLM K (κ t)).comp (truncateTorusHk (by omega : K ≤ K + 2))

end AVRegularity.CycleWords
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Normalized graph histories sharing a drift forget their entrance through the projected gap. -/

theorem cellWeak_normalized_graph_difference_decay {a b : ℝ} (hab : a ≤ b)
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
    (u w : ℝ → ComplexCellL2) (slice other : ℝ → TorusHk 1 ℂ)
    (lam mu : ℝ → ℂ) (hlam : ∀ t, ‖lam t‖ ≤ L * fibreNorm ξ ^ 2)
    (hρ : ∀ t, ‖w t - cellConstantCLM 1‖ ≤ Cr * fibreNorm ξ)
    (hρsmall : ∀ t, ‖w t - cellConstantCLM 1‖ ≤ 1)
    (hdiff : ∀ t ∈ Icc a b, lam t - mu t =
      -Complex.I * cellBlochDriftMeanCLM η Cw hCw hv hw ξ t (u t - w t))
    (h : CellWeakHilbertCurve a b u slice (fun t => cellDualDerivative
      ⟨fun t _ => G t, v, (fun j => (Real.sqrt η : ℂ) * ξ j), fun t => -lam t⟩
      hG V hv.1 hb t (slice t) 0 (fun _ => 0)))
    (h' : CellWeakHilbertCurve a b w other (fun t => cellDualDerivative
      ⟨fun t _ => G t, v, (fun j => (Real.sqrt η : ℂ) * ξ j), fun t => -mu t⟩
      hG V hv.1 hb t (other t) 0 (fun _ => 0)))
    (hmean : ∀ t ∈ Icc a b, cellMean (u t) = cellMean (w t)) :
    ∀ t ∈ Icc a b,
      ‖u t - w t‖ ^ 2 ≤ Real.exp (-(Real.pi ^ 2 / 2) * (t - a)) * ‖u a - w a‖ ^ 2 := by
  have hzmean : cellMean (0 : ComplexCellL2) = 0 := by
    rw [← cellMeanCLM_apply, map_zero]
  have hz : CellWeakHilbertCurve a b (fun t => u t - w t) (fun t => slice t - other t)
      (fun t => cellDualDerivative
        ⟨fun t _ => G t, v, (fun j => (Real.sqrt η : ℂ) * ξ j), 0⟩
        hG V hv.1 hb t (slice t - other t) 0 (fun _ => 0) -
        cellPivotDualCLM (cellScalarCLM (lam t) (torusHkValueCLM (slice t - other t))) -
        cellPivotDualCLM (cellScalarCLM
          (-Complex.I * cellBlochDriftMeanCLM η Cw hCw hv hw ξ t
            (torusHkValueCLM (slice t - other t)) +
            ∑ j : Fin 2, Complex.I * ((Real.sqrt η : ℂ) * ξ j) * cellMean (0 : ComplexCellL2))
          (w t - cellConstantCLM 1 + cellConstantCLM 1))) := (h.sub h').dual_congr (by
    filter_upwards [h.agrees, h'.agrees, ae_restrict_mem measurableSet_Icc] with t hu hw' ht
    rw [cellDualDerivative_normalized_gauge_difference]
    have hd := hdiff t ht
    rw [hu, hw', ← map_sub] at hd
    rw [hd]
    simp only [hzmean, mul_zero, Finset.sum_const_zero, add_zero,
      sub_add_cancel]
    rw [hw'])
  apply cellWeak_projected_feedback_decay hab η Cw hη0 hη hCw G hG hg hgsmall hv hw
    V hb ξ L Cr hsmall hξsmall hθ (fun t => u t - w t) (fun t => slice t - other t)
    lam hlam (fun t => w t - cellConstantCLM 1) hρ hρsmall hz
  intro t ht
  rw [← cellMeanCLM_apply, map_sub, cellMeanCLM_apply, cellMeanCLM_apply,
    hmean t ht, sub_self]

end AVRegularity.CycleWords
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Sobolev truncation preserves the actual word flux when it keeps all nonempty edges. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

theorem wordChainPreviousFlux_truncate (letters : Fin N → CycleLetter ι h D)
    (κ κ' : Fin (N + 1) → ι → ℕ) (hκ : ∀ j x, κ' j x ≤ κ j x)
    (hc : ∀ j x y (o : Finset.Icc 2 D), (letters j).edge x y o ≠ [] →
      κ j.succ x + o.1 ≤ κ j.castSucc y + 2)
    (hc' : ∀ j x y (o : Finset.Icc 2 D), (letters j).edge x y o ≠ [] →
      κ' j.succ x + o.1 ≤ κ' j.castSucc y + 2)
    (X0 : Vec 2) (δ : ℝ)
    (W : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (i : Fin (N + 1) × ι) (t : ℝ) (z : Vec 2) :
    wordChainPreviousFlux letters X0 δ κ'
      (fun p => truncatePlaneHk (Nat.succ_le_succ (hκ p.1 p.2)) (W p)) i t z =
      wordChainPreviousFlux letters X0 δ κ W i t z := by
  rcases i with ⟨j, x⟩
  refine Fin.cases ?_ (fun j => ?_) j
  · rw [wordChainPreviousFlux_initial, wordChainPreviousFlux_initial]
  · rw [wordChainPreviousFlux_succ, wordChainPreviousFlux_succ]
    exact letterAdmissibleFlux_truncate (letters j)
      (fun p : Fin (N + 1) × ι => κ p.1 p.2)
      (fun p : Fin (N + 1) × ι => κ' p.1 p.2)
      (fun p => hκ p.1 p.2) (j.succ, x) (fun u => (j.castSucc, u)) x
      (hc j x) (hc' j x) _ X0 δ (fun u => W (j.castSucc, u)) t z

theorem wordChainRawFlux_truncate [∀ i, FiniteDimensional ℝ (h i)] (hD : 2 ≤ D)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (letters : Fin N → CycleLetter ι h D)
    (κ κ' : Fin (N + 1) → ι → ℕ) (hκ : ∀ j x, κ' j x ≤ κ j x)
    (hc : ∀ j x y (o : Finset.Icc 2 D), (letters j).edge x y o ≠ [] →
      κ j.succ x + o.1 ≤ κ j.castSucc y + 2)
    (hc' : ∀ j x y (o : Finset.Icc 2 D), (letters j).edge x y o ≠ [] →
      κ' j.succ x + o.1 ≤ κ' j.castSucc y + 2)
    (X0 : Vec 2) (δ : ℝ)
    (W : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (i : Fin (N + 1) × ι) (t : ℝ) (z : Vec 2) :
    wordChainRawFlux G letters X0 δ κ'
      (fun p => truncatePlaneHk (Nat.succ_le_succ (hκ p.1 p.2)) (W p)) i t z =
      wordChainRawFlux G letters X0 δ κ W i t z := by
  rw [wordChainRawFlux_split hD, wordChainRawFlux_split hD,
    wordChainPreviousFlux_truncate letters κ κ' hκ hc hc']
  rfl

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Time integration of response sums preserves the level count bound. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]
  {L : Type*} [Fintype L]

theorem integrated_weightedFactorialNormSq_sum_le {K : ℕ}
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ) (μ : Measure ℝ)
    (U : L → ℝ → PlaneHk Set.univ K E) (hU : ∀ j, MemLp (U j) 2 μ) :
    (∫⁻ t, weightedFactorialNormSq n ϖ zc ρ K (∑ j, U j t) ∂μ) ≤
      (Fintype.card L : ℝ≥0∞) * ∑ j, ∫⁻ t, weightedFactorialNormSq n ϖ zc ρ K (U j t) ∂μ := by
  classical
  rw [← lintegral_finsetSum' Finset.univ (fun j _ =>
    Weighted.weightedFactorialNormSq_time_aemeasurable n ϖ zc ρ μ (U j) (hU j)),
    ← lintegral_const_mul' _ _ (by simp)]
  exact lintegral_mono (fun t => weightedFactorialNormSq_sum_le n ϖ zc ρ (fun j => U j t))
end

/-! Assembly of the two remainder sums and the terminal insertion in the
native forcing carrier. The finite sum cost counts response levels. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]
  {L : Type*} [Fintype L]

theorem nativeRemainderForcing_assembly {K : ℕ} (μ : Measure ℝ)
    (A B : L → ℝ → PlaneHk Set.univ K E) (T : ℝ → PlaneHk Set.univ K E)
    (hA : ∀ j, MemLp (A j) 2 μ) (hB : ∀ j, MemLp (B j) 2 μ) (hT : MemLp T 2 μ)
    (a b : L → ℝ → Vec 2 → E) (term : ℝ → Vec 2 → E)
    (ha : ∀ j, ∀ᵐ t ∂μ, planeValue (A j t) =ᵐ[volume] a j t)
    (hb : ∀ j, ∀ᵐ t ∂μ, planeValue (B j t) =ᵐ[volume] b j t)
    (ht : ∀ᵐ t ∂μ, planeValue (T t) =ᵐ[volume] term t) :
    ∃ V : ℝ → PlaneHk Set.univ K E, MemLp V 2 μ ∧
      (∀ᵐ t ∂μ, planeValue (V t) =ᵐ[volume]
        (fun z => (∑ j, a j t z) + (∑ j, b j t z) + term t z)) ∧
      (∀ n ϖ zc ρ, (∫⁻ t, weightedFactorialNormSq n ϖ zc ρ K (V t) ∂μ) ≤
        4 * (Fintype.card L : ℝ≥0∞) *
          ((∑ j, ∫⁻ t, weightedFactorialNormSq n ϖ zc ρ K (A j t) ∂μ) +
           ∑ j, ∫⁻ t, weightedFactorialNormSq n ϖ zc ρ K (B j t) ∂μ) +
        2 * ∫⁻ t, weightedFactorialNormSq n ϖ zc ρ K (T t) ∂μ) := by
  classical
  let As := fun t => ∑ j, A j t
  let Bs := fun t => ∑ j, B j t
  have hAs : MemLp As 2 μ := nativeTime_sum_memLp μ A hA
  have hBs : MemLp Bs 2 μ := nativeTime_sum_memLp μ B hB
  have hAB := nativeTime_add_memLp μ As Bs hAs hBs
  refine ⟨fun t => As t + Bs t + T t,
    nativeTime_add_memLp μ (fun t => As t + Bs t) T hAB hT, ?_, ?_⟩
  · filter_upwards [ae_all_iff.mpr ha, ae_all_iff.mpr hb, ht] with t hat hbt htt
    have hsa := planeJetOrder_finite_sum_ae (Nat.zero_le K) (fun j => A j t) (fun i : Fin 0 => Fin.elim0 i)
    have hsb := planeJetOrder_finite_sum_ae (Nat.zero_le K) (fun j => B j t) (fun i : Fin 0 => Fin.elim0 i)
    filter_upwards [planeValue_add_ae (As t + Bs t) (T t), planeValue_add_ae (As t) (Bs t),
      hsa, hsb, ae_all_iff.mpr hat, ae_all_iff.mpr hbt, htt] with z h1 h2 h3 h4 h5 h6 h7
    rw [h1, h2, h7]
    have h3' : planeValue (As t) z = ∑ j, planeValue (A j t) z := h3
    have h4' : planeValue (Bs t) z = ∑ j, planeValue (B j t) z := h4
    rw [h3', h4']
    exact congrArg₂ (fun u v => u + v + term t z)
      (Finset.sum_congr rfl (fun j _ => h5 j)) (Finset.sum_congr rfl (fun j _ => h6 j))
  · intro n ϖ zc ρ
    have h1 := integrated_weightedFactorialNormSq_add_le n ϖ zc ρ μ
      (fun t => As t + Bs t) T hAB
    have h2 := integrated_weightedFactorialNormSq_add_le n ϖ zc ρ μ As Bs hAs
    have h3 := integrated_weightedFactorialNormSq_sum_le n ϖ zc ρ μ A hA
    have h4 := integrated_weightedFactorialNormSq_sum_le n ϖ zc ρ μ B hB
    calc
      _ ≤ 2 * (2 * ((∫⁻ t, weightedFactorialNormSq n ϖ zc ρ K (As t) ∂μ) +
          ∫⁻ t, weightedFactorialNormSq n ϖ zc ρ K (Bs t) ∂μ) +
          ∫⁻ t, weightedFactorialNormSq n ϖ zc ρ K (T t) ∂μ) :=
        h1.trans (mul_le_mul_right (add_le_add_left h2 _) 2)
      _ ≤ 2 * (2 * ((Fintype.card L : ℝ≥0∞) *
          (∑ j, ∫⁻ t, weightedFactorialNormSq n ϖ zc ρ K (A j t) ∂μ) +
          (Fintype.card L : ℝ≥0∞) *
          ∑ j, ∫⁻ t, weightedFactorialNormSq n ϖ zc ρ K (B j t) ∂μ) +
          ∫⁻ t, weightedFactorialNormSq n ϖ zc ρ K (T t) ∂μ) :=
        mul_le_mul_right (add_le_add_left (mul_le_mul_right (add_le_add h3 h4) 2) _) 2
      _ = _ := by ring
end

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Interchanging the finite vertex mass sum and time integration. -/

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)]
  [∀ i, CompleteSpace (E i)] [∀ i, FiniteDimensional ℝ (E i)]

theorem weightedNativeMass_time_sum (K : ι → ℕ) (α : ι → ℝ≥0∞)
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ) (μ : Measure ℝ)
    (U : ∀ v, ℝ → PlaneHk Set.univ (K v) (E v)) (hU : ∀ v, MemLp (U v) 2 μ) :
    (∫⁻ t, (∑ v, α v * weightedFactorialNormSq n ϖ zc ρ (K v) (U v t)) ∂μ) =
      ∑ v, α v * ∫⁻ t, weightedFactorialNormSq n ϖ zc ρ (K v) (U v t) ∂μ := by
  classical
  rw [lintegral_finsetSum' Finset.univ (fun v _ =>
    (Weighted.weightedFactorialNormSq_time_aemeasurable n ϖ zc ρ μ (U v) (hU v)).const_mul (α v))]
  apply Finset.sum_congr rfl
  intro v _
  exact lintegral_const_mul'' _ (Weighted.weightedFactorialNormSq_time_aemeasurable n ϖ zc ρ μ (U v) (hU v))

omit [Fintype ι] in
theorem weightedNativeGrad_time_aemeasurable (K : ι → ℕ)
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ) (μ : Measure ℝ)
    (U : ∀ v, ℝ → PlaneHk Set.univ (K v + 1) (E v)) (hU : ∀ v, MemLp (U v) 2 μ) (v : ι) :
    AEMeasurable (fun t => weightedGradFactorialNormSq n ϖ zc ρ (K v) (U v t)) μ := by
  simp_rw [← planeGradientTensor_weightedFactorialNormSq n ϖ zc ρ]
  have hUg : MemLp (fun t => planeGradientTensor (U v t)) 2 μ := by
    simpa only [Function.comp_def, planeGradientTensorOperator_apply] using
      (planeGradientTensorOperator (E := E v) (K v)).comp_memLp' (hU v)
  exact Weighted.weightedFactorialNormSq_time_aemeasurable n ϖ zc ρ μ
    (fun t => planeGradientTensor (U v t)) hUg

theorem weightedNativeGradMass_time_sum (K : ι → ℕ) (α : ι → ℝ≥0∞)
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ) (μ : Measure ℝ)
    (U : ∀ v, ℝ → PlaneHk Set.univ (K v + 1) (E v)) (hU : ∀ v, MemLp (U v) 2 μ) :
    (∫⁻ t, (∑ v, α v * weightedGradFactorialNormSq n ϖ zc ρ (K v) (U v t)) ∂μ) =
      ∑ v, α v * ∫⁻ t, weightedGradFactorialNormSq n ϖ zc ρ (K v) (U v t) ∂μ := by
  classical
  rw [lintegral_finsetSum' Finset.univ (fun v _ =>
    (weightedNativeGrad_time_aemeasurable K n ϖ zc ρ μ U hU v).const_mul (α v))]
  apply Finset.sum_congr rfl
  intro v _
  exact lintegral_const_mul'' _ (weightedNativeGrad_time_aemeasurable K n ϖ zc ρ μ U hU v)

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Actual word energy solutions truncate when all nonempty edges remain admitted. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

theorem wordChainFrom_truncate (hD : 2 ≤ D)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (letters : Fin N → CycleLetter ι h D)
    (κ κ' : Fin (N + 1) → ι → ℕ) (hκ : ∀ j x, κ' j x ≤ κ j x)
    (hc : ∀ j x y (o : Finset.Icc 2 D), (letters j).edge x y o ≠ [] →
      κ j.succ x + o.1 ≤ κ j.castSucc y + 2)
    (hc' : ∀ j x y (o : Finset.Icc 2 D), (letters j).edge x y o ≠ [] →
      κ' j.succ x + o.1 ≤ κ' j.castSucc y + 2)
    (X0 : Vec 2) (δ a b : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (f : ∀ j x, PlaneHk Set.univ (κ j x) (h x))
    (F : ∀ j x, ℝ → PlaneHk Set.univ (κ j x) (PiLp 2 (fun _ : Fin 2 => h x)))
    (u : ∀ j x, ℝ → PlaneHk Set.univ (κ j x) (h x))
    (w : ∀ j x, ℝ → PlaneHk Set.univ (κ j x + 1) (h x))
    (hs : IsPlaneChainFrom (wordChainData G letters X0 δ) κ a b v f F u w) :
    IsPlaneChainFrom (wordChainData G letters X0 δ) κ' a b v
      (fun j x => truncatePlaneHk (hκ j x) (f j x))
      (fun j x t => truncatePlaneHk (hκ j x) (F j x t))
      (fun j x t => truncatePlaneHk (hκ j x) (u j x t))
      (fun j x t => truncatePlaneHk (Nat.succ_le_succ (hκ j x)) (w j x t)) := by
  have hf : ∀ p t z, coupledStoredFlux
      (fun q : Fin (N + 1) × ι => κ' q.1 q.2)
      (planeChainCoefficient (wordChainData G letters X0 δ) κ')
      (fun q => truncatePlaneHk (Nat.succ_le_succ (hκ q.1 q.2)) (w q.1 q.2 t)) p t z =
      coupledStoredFlux (fun q : Fin (N + 1) × ι => κ q.1 q.2)
        (planeChainCoefficient (wordChainData G letters X0 δ) κ)
        (fun q => w q.1 q.2 t) p t z := by
    intro p t z
    exact wordChainRawFlux_truncate hD G letters κ κ' hκ hc hc' X0 δ
      (fun q => w q.1 q.2 t) p t z
  have hh := coupledSolution_truncate
    (fun p : Fin (N + 1) × ι => κ p.1 p.2)
    (fun p : Fin (N + 1) × ι => κ' p.1 p.2) (fun p => hκ p.1 p.2)
    (planeChainCoefficient (wordChainData G letters X0 δ) κ)
    (planeChainCoefficient (wordChainData G letters X0 δ) κ')
    1 a b v (fun p => f p.1 p.2) (fun p => F p.1 p.2) (fun _ _ => 0)
    (fun p => u p.1 p.2) (fun p => w p.1 p.2) hf hs
  simpa only [IsPlaneChainFrom, map_zero] using hh

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The integrated actual cell generator equals its genuine plane diffusion and drift form. -/

theorem cellFrequencyGenerator_plane_form
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (C : ℝ) (hCpos : 0 < C) (hC : ∀ t i z, ‖cellDriftTorusSymbol v t i z‖ ≤ C)
    (t : ℝ) (u z : Lp CellComplexH1 2 centeredPlaneFrequencyMeasure) :
    (∫ θ, cellGeneratorForm ⟨fun t _ => G t, v, planePhysicalBlochShift θ, 0⟩ hG V hv.1 hb t
      (cellComplexH1RealEquiv (u θ)) (cellComplexH1RealEquiv (z θ))
      ∂centeredPlaneFrequencyMeasure) =
        -(∑ i : Fin 2, ∑ j : Fin 2, inner ℝ (G t i j • cellFrequencyPlaneGradient u i)
          (cellFrequencyPlaneGradient z j)) -
        ∑ i : Fin 2, inner ℝ
          (planeMeasurableTorusSymbolMultiplication (cellDriftTorusSymbol v t i)
            (cellDriftTorusSymbol_measurable v hv t i) C (hC t i)
              (cellFrequencyPlaneGradient u i)) (cellFrequencyPlaneValue z) := by
  rw [cellFrequencyGenerator_integral G hG v V hv.1 hb t u z]
  congr 1
  · congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [← (planeCellBlochUnitary centeredPlaneFrequencyBase 1 (by norm_num)).symm.inner_map_map]
    rw [cellFrequencyMetricField, cellScalarCLM_real_compLp, map_smul]
    rfl
  · apply Finset.sum_congr rfl
    intro i _
    rw [← (planeCellBlochUnitary centeredPlaneFrequencyBase 1 (by norm_num)).symm.inner_map_map]
    rw [cellFrequencyDriftField, planeCellBloch_drift_inverse centeredPlaneFrequencyBase
      ⟨fun t _ => G t, v, 0, 0⟩ hv V hb C hCpos hC t i]
    rfl

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleWords

/-! The genuine transverse generator of an H2 state has an actual native L2 source. -/

theorem cellComplexDiffusionForm_real_part
    (C : CellCoefficients) (hG : IsCellMetric C.G)
    (t : ℝ) (u z : TorusHk 1 ℂ) :
    (cellComplexDiffusionForm hG C.θ t u z).re = cellDiffusionForm C hG t u z := by
  simp only [cellComplexDiffusionForm, cellDiffusionForm, Fin.sum_univ_two,
    Complex.neg_re, Complex.add_re, cellComplexPair_re, neg_apply, add_apply,
    pullbackInnerCLM_apply, ContinuousLinearMap.comp_apply]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The literal correction forcing has a frequency-linear bound and native time integrability. -/

def cellZeroDriftCorrectionSource (η Cw : ℝ) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) (u : ComplexCellL2) : ComplexCellL2 :=
  -cellScalarCLM Complex.I (cellFibreDriftCouplingCLM η Cw hCw hv hw ξ t u) +
    cellScalarCLM (κ t - ∑ j : Fin 2, ∑ l : Fin 2,
      (G t j l : ℂ) * ((Real.sqrt η : ℂ) * ξ j) * ((Real.sqrt η : ℂ) * ξ l)) (cellConstantCLM 1)

theorem cellZeroDriftCorrectionSource_norm_le (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1)
    (hCw : 0 ≤ Cw) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : IsCellMetric (fun t _ => G t)) {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) (u : ComplexCellL2) :
    ‖cellZeroDriftCorrectionSource η Cw hCw G hv hw ξ κ t u‖ ≤
      Cw * fibreNorm ξ * ‖u - cellConstantCLM 1‖ +
        (Cw * fibreNorm ξ + ‖κ t‖ + 8 * fibreNorm ξ ^ 2) := by
  have hu : ‖u‖ ≤ ‖u - cellConstantCLM 1‖ + 1 := by
    have h := norm_add_le (u - cellConstantCLM 1) (cellConstantCLM 1)
    simpa only [sub_add_cancel, cellConstantCLM_norm, norm_one] using h
  have hd := (cellFibreDriftCouplingCLM_apply_norm_le η Cw hCw hv hw ξ t u).trans
    (mul_le_mul_of_nonneg_left hu (mul_nonneg hCw (fibreNorm_nonneg ξ)))
  have hq := scaledMetricQuad_norm_le η hη0 hη G hG ξ t
  have hs := norm_add_le
    (-cellScalarCLM Complex.I (cellFibreDriftCouplingCLM η Cw hCw hv hw ξ t u))
    (cellScalarCLM (κ t - ∑ j : Fin 2, ∑ l : Fin 2,
      (G t j l : ℂ) * ((Real.sqrt η : ℂ) * ξ j) * ((Real.sqrt η : ℂ) * ξ l)) (cellConstantCLM 1))
  simp only [norm_neg, cellScalarCLM_norm, Complex.norm_I, one_mul,
    cellConstantCLM_norm, norm_one, mul_one] at hs
  exact (hs.trans (add_le_add hd ((norm_sub_le _ _).trans (add_le_add le_rfl hq)))).trans_eq (by ring)

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Integrated gradient masses are dominated by the actual graded energy. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem nativeGradient_mass_le_graded_energy (K N : ι → ℕ) (n : ℕ)
    (hn : ∀ v, n ≤ N v) (α : ι → ℝ≥0∞) (ϖ ρ a b : ℝ)
    (U : ∀ v, ℝ → PlaneHk Set.univ (K v) (h v))
    (Uw : ∀ v, ℝ → PlaneHk Set.univ (K v + 1) (h v))
    (hUw : ∀ v, MemLp (Uw v) 2 (volume.restrict (Set.Icc a b))) :
    (∫⁻ t in Set.Icc a b, ∑ v, α v *
      weightedGradFactorialNormSq n ϖ 0 ρ (K v) (Uw v t)) ≤
    ∑ v, α v * nativeComponentEnergy (N v) ϖ ρ a b (U v) (Uw v) := by
  rw [weightedNativeGradMass_time_sum K α n ϖ 0 ρ _ Uw hUw]
  apply Finset.sum_le_sum
  intro v _
  apply mul_le_mul_right
  exact (lintegral_mono (fun t => weightedGradFactorialNormSq_moment_mono
    (hn v) ϖ 0 ρ (K v) (Uw v t))).trans le_add_self

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The true low scalar forcing grows at most linearly in correction mass. -/

theorem cellZeroDriftCorrectionSource_normSq_le
    (η Cw : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) (u : ComplexCellL2)
    (L : ℝ) (hL : 0 ≤ L) (hκ : ‖κ t‖ ≤ L * fibreNorm ξ ^ 2)
    (hξ1 : fibreNorm ξ ≤ 1) (hsmall : Cw * fibreNorm ξ ≤ 1) :
    ‖cellZeroDriftCorrectionSource η Cw hCw G hv hw ξ κ t u‖ ^ 2 ≤
      2 * ‖u - cellConstantCLM 1‖ ^ 2 + 2 * (Cw + L + 8) ^ 2 * fibreNorm ξ ^ 2 := by
  exact correction_source_growth_algebra Cw L (fibreNorm ξ) ‖u - cellConstantCLM 1‖
    ‖cellZeroDriftCorrectionSource η Cw hCw G hv hw ξ κ t u‖ ‖κ t‖ hCw hL
    (fibreNorm_nonneg ξ) hξ1 (norm_nonneg _) (norm_nonneg _) hsmall hκ
    (cellZeroDriftCorrectionSource_norm_le η Cw hη0 hη hCw G hG hv hw ξ κ t u)

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! Every actual scalar chain gives a weak time curve for each stored derivative word. -/

open AVRegularity.Weighted

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem cellMetric_scalarChain_ordered_planeWeakHilbertCurve
    (a b : ℝ) (hab : a ≤ b) (κ : Fin 1 → ι → ℕ) (Kmax : ℕ)
    (hκ : ∀ i : Fin 1 × ι, κ i.1 i.2 ≤ Kmax)
    (v : ℝ → Vec 2 → Vec 2)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hV : 0 ≤ V) (ha : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hGm : Measurable (fun p : Set.Icc a b × Vec 2 => G p.1 p.2))
    (hG : ∀ i : Fin 1 × ι, ∀ t ∈ Set.Icc a b, ∀ k j,
      ContDiff ℝ (κ i.1 i.2 : ℕ) (fun x => G t x k j))
    (M : ∀ i : Fin 1 × ι, Fin (κ i.1 i.2 + 1) → ℝ)
    (hb : ∀ i, ∀ t ∈ Set.Icc a b, ∀ (l : Fin (κ i.1 i.2 + 1)) x k j,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k j) x‖ ≤ M i l)
    (hCell : IsCellMetric G)
    (f : ∀ i : Fin 1 × ι, PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (F : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (PiLp 2 (fun _ : Fin 2 => h i.2)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (u : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (w : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2 + 1) (h i.2))
    (hsln : IsCoupledWeakSolutionPlane 1 a b v 2 (fun i : Fin 1 × ι => κ i.1 i.2)
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ) f F
      (fun _ _ => 0) u w) (i : Fin 1 × ι) (α : JetIndex2 (κ i.1 i.2)) :
    let H := scalarSobolevTransportSource (hκ i) hab v hv V strain B lam hbv hjets (w i)
    let S := scalarSobolevMetricSource hab G (hG i) (M i) (hb i) (w i) (F i)
    PlaneWeakHilbertCurve a b (fun t => planeJetReadoutOperator (κ i.1 i.2) α (u i t))
      (fun t => planeWordH1SliceOperator (κ i.1 i.2) α (w i t))
      (fun t => planeSourceDual (planeJetReadoutOperator (κ i.1 i.2) α (H t))
        (planeJetFluxOperator (κ i.1 i.2) α (S t))) := by
  dsimp only
  apply plane_ordered_source_curve
  · exact hsln.1 i
  · exact hsln.2.1 i
  · exact scalarSobolevTransportSource_memLp (hκ i) hab v hvm hv V strain B lam
      hV ha hB hlam hbv hjets (w i) (hsln.2.1 i)
  · exact scalarSobolevMetricSource_memLp hab G hGm (hG i) (M i) (hb i)
      (w i) (F i) (hsln.2.1 i) (hF i)
  · filter_upwards [hsln.2.2.1 i] with t ht
    exact ht.symm
  · intro s hs t ht hst Z
    have hi := scalarChainTrace_increment a b hab κ v G f F u w hsln i hs ht Z
    refine hi.trans ?_
    apply intervalIntegral.integral_congr
    intro r hr
    exact (cellMetric_scalarSobolevSource_pair_eq_raw (hκ i) hab v hv V strain B lam hbv hjets
      G (hG i) (M i) (hb i) hCell (w i) (F i) r
      (Set.Icc_subset_Icc hs.1 ht.2 (by simpa only [Set.uIcc_of_le hst] using hr)) Z).symm

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Weighted
namespace AVRegularity.CycleWords

/-! Every actual scalar chain gives a weak time curve for each stored derivative word. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem scalarChain_ordered_dual_aestronglyMeasurable
    (a b : ℝ) (hab : a ≤ b) (κ : Fin 1 → ι → ℕ) (Kmax : ℕ)
    (hκ : ∀ i : Fin 1 × ι, κ i.1 i.2 ≤ Kmax)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ)
    (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ i : Fin 1 × ι, ∀ t ∈ Set.Icc a b, ∀ k j,
      ContDiff ℝ (κ i.1 i.2 : ℕ) (fun x => G t x k j))
    (M : ∀ i : Fin 1 × ι, Fin (κ i.1 i.2 + 1) → ℝ)
    (hb : ∀ i, ∀ t ∈ Set.Icc a b, ∀ (l : Fin (κ i.1 i.2 + 1)) x k j,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k j) x‖ ≤ M i l)
    (g : ℝ) (hg4 : g ≤ 1 / 4) (hGnear : IsMetricNearIdentity G g)
    (hGs : ∀ t ∈ Set.Icc a b, ∀ x, (G t x).IsSymm)
    (f : ∀ i : Fin 1 × ι, PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (F : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (PiLp 2 (fun _ : Fin 2 => h i.2)))
    (u : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2) (h i.2))
    (w : ∀ i : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ i.1 i.2 + 1) (h i.2))
    (hsln : IsCoupledWeakSolutionPlane 1 a b v 2 (fun i : Fin 1 × ι => κ i.1 i.2)
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ) f F
      (fun _ _ => 0) u w) (i : Fin 1 × ι) (α : JetIndex2 (κ i.1 i.2)) :
    let H := scalarSobolevTransportSource (hκ i) hab v hv V strain B lam hbv hjets (w i)
    let S := scalarSobolevMetricSource hab G (hG i) (M i) (hb i) (w i) (F i)
    AEStronglyMeasurable
      (fun t => planeSourceDual (planeJetReadoutOperator (κ i.1 i.2) α (H t))
        (planeJetFluxOperator (κ i.1 i.2) α (S t))) (volume.restrict (Set.Icc a b)) := by
  dsimp only
  apply planeJetSourceDual_aestronglyMeasurable
  intro Z
  have hm := (scalarChain_rhs_integrableOn a b hab κ v G f F u w hsln i Z).aestronglyMeasurable
  apply hm.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact (scalarSobolevSource_pair_eq_raw (hκ i) hab v hv V strain B lam hbv hjets
    G (hG i) (M i) (hb i) g hg4 hGnear hGs (w i) (F i) t ht Z).symm

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleWords

/-! With zero transport the genuine H2 diffusion and scalar source are the native weak derivative. -/

theorem cellZeroDrift_dual_strong_source
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) (u : TorusHk 2 ℂ)
    (src : ComplexCellL2) :
    cellDualDerivative ⟨fun t _ => G t, 0, θ, κ⟩ hG 0 measurable_const
      (by intro t x; simp) t (cellH2BaseCLM u) src 0 =
      cellPivotDualCLM (cellConstantMetricStrongDiffusionCLM G θ t u +
        cellScalarCLM (κ t) (torusHkValueCLM u) + src) := by
  let C : CellCoefficients := ⟨fun t _ => G t, 0, θ, κ⟩
  have hd : cellDiffusionForm C hG t (cellH2BaseCLM u) =
      (innerSL ℝ (cellConstantMetricStrongDiffusionCLM G θ t u)).comp torusHkValueCLM := by
    ext z
    have he := congrArg Complex.re (cellConstantMetricStrongDiffusionCLM_pair G hG θ t u z)
    rw [cellComplexDiffusionForm_real_part C hG, cellComplexPair_re] at he
    exact he
  have hz (j : Fin 2) (w : ComplexCellL2) :
      cellDriftEntryCLM C 0 measurable_const (by intro t x; simp [C]) t j w = 0 := by
    apply Lp.ext
    have hh := cellDriftEntryCLM_ae C 0 measurable_const (by intro t x; simp [C]) t j w
    filter_upwards [hh, Lp.coeFn_zero ℂ 2 (volume.restrict AVenhance.unitCube)] with x hx h0
    rw [hx, h0]
    simp only [C, Pi.zero_apply, Complex.ofReal_zero, zero_mul]
  apply ext_inner_right ℝ
  intro z
  rw [cellDualDerivative_pairing, cellSourceFunctional_scalar_only]
  change cellGeneratorForm C hG 0 measurable_const (by intro t x; simp [C]) t
    (cellH2BaseCLM u) z + inner ℝ src (torusHkValueCLM z) = _
  simp only [cellGeneratorForm, add_apply, sub_apply, Fin.sum_univ_two,
    pullbackInnerCLM_apply, ContinuousLinearMap.comp_apply, hz, inner_zero_left,
    add_zero, sub_zero]
  rw [hd]
  change inner ℝ (cellConstantMetricStrongDiffusionCLM G θ t u) (torusHkValueCLM z) +
    inner ℝ (cellScalarCLM (κ t) (torusHkValueCLM u)) (torusHkValueCLM z) +
    inner ℝ src (torusHkValueCLM z) =
      inner ℝ ((torusHkValueCLM (E := ℂ) (K := 1)).adjoint _) z
  rw [ContinuousLinearMap.adjoint_inner_left, inner_add_left, inner_add_left]

/-! Zero transport leaves exactly diffusion and the actual scalar potential on every native H1 state. -/

theorem cellZeroDrift_generator_eq_diffusion
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) (u z : TorusHk 1 ℂ) :
    cellGeneratorForm ⟨fun t _ => G t, 0, θ, κ⟩ hG 0 measurable_const
      (by intro t x; simp) t u z =
    cellDiffusionForm ⟨fun t _ => G t, 0, θ, κ⟩ hG t u z +
      inner ℝ (cellScalarCLM (κ t) (torusHkValueCLM u)) (torusHkValueCLM z) := by
  let C : CellCoefficients := ⟨fun t _ => G t, 0, θ, κ⟩
  have hz (j : Fin 2) (w : ComplexCellL2) :
      cellDriftEntryCLM C 0 measurable_const (by intro t x; simp [C]) t j w = 0 := by
    apply Lp.ext
    have hh := cellDriftEntryCLM_ae C 0 measurable_const (by intro t x; simp [C]) t j w
    filter_upwards [hh, Lp.coeFn_zero ℂ 2 (volume.restrict AVenhance.unitCube)] with x hx h0
    rw [hx, h0]
    simp only [C, Pi.zero_apply, Complex.ofReal_zero, zero_mul]
  change cellGeneratorForm C hG 0 measurable_const (by intro t x; simp [C]) t u z = _
  simp only [cellGeneratorForm, add_apply, sub_apply, Fin.sum_univ_two,
    pullbackInnerCLM_apply, ContinuousLinearMap.comp_apply, hz, inner_zero_left,
    add_zero, sub_zero]
  rfl

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev Set
namespace AVRegularity.CycleWords

/-! Every actual stored source word satisfies the clipped weighted scalar estimate with its true residuals. -/

open AVRegularity.Weighted

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem cellMetric_storedWords_clipped_raw_energy_bound {K : ℕ}
    (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hv : ∀ t ∈ Icc a b, ContDiff ℝ 1 (v t))
    (hvm : Measurable (fun p : Icc a b × Vec 2 => v p.1 p.2))
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ j : Fin 2, fderiv ℝ (v t) x (basisVec j) j = 0)
    (Mv : ℝ) (hMv : 0 ≤ Mv) (hvb : ∀ t ∈ Icc a b, ∀ x, ‖v t x‖ ≤ Mv)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ t ∈ Icc a b, ∀ k j, ContDiff ℝ 1 (fun x => G t x k j))
    (hGm : Measurable (fun p : Icc a b × Vec 2 => G p.1 p.2))
    (hCell : IsCellMetric G)
    (hGs : ∀ t ∈ Icc a b, ∀ x, (G t x).IsSymm)
    (t₀ S ϖ : ℝ) (zc : Vec 2) (N m : ℕ) (Cw : ℕ → ℝ)
    (C : ChartWeights G v t₀ S ϖ zc N Cw) (hm : m ≤ N)
    (ha : t₀ ≤ a) (hb : b ≤ t₀ + S)
    (U H : ℝ → PlaneHk Set.univ K E)
    (W : ℝ → PlaneHk Set.univ (K + 1) E)
    (Q : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (hW : MemLp W 2 (volume.restrict (Icc a b)))
    (hH : MemLp H 2 (volume.restrict (Icc a b)))
    (hQ : MemLp Q 2 (volume.restrict (Icc a b))) 
    (hcurve : ∀ α : JetIndex2 K, PlaneWeakHilbertCurve a b
      (fun t => planeJetReadoutOperator K α (U t))
      (fun t => planeWordH1SliceOperator K α (W t))
      (fun t => planeSourceDual (planeJetReadoutOperator K α (H t))
        (planeJetFluxOperator K α (Q t))))
    (B : ℝ) (hB : 0 < B) (ρ : ℝ) :
    let T := planeIntervalTransport (E := E) a b hab v (fun t ht => (hv t ht).continuous) Mv hvb
    let D := cellMetricIntervalDiffusion (E := E) a b hab G
      (fun t ht k j => (hG t ht k j).continuous) hCell
    let L := fun (α : JetIndex2 K) t => planeJetFluxOperator K α (Q t) - D t
      (planeH1GradientOperator (planeWordH1SliceOperator K α (W t)))
    let R := fun (α : JetIndex2 K) t => planeJetReadoutOperator K α (H t) + T t
      (planeH1GradientOperator (planeWordH1SliceOperator K α (W t)))
    ∀ t ∈ Icc a b,
      rawWeightedFactorialEnergy ρ (fun x => clipWeight B (C.W m t x)) (U t).toFunction.jet +
      (1 / 2) * (∫ s in a..t, rawWeightedGradientEnergy ρ
        (fun x => clipWeight B (C.W m s x)) (W s).toFunction.jet) ≤
      (rawWeightedFactorialEnergy ρ (fun x => clipWeight B (C.W m a x)) (U a).toFunction.jet +
        8 * (∫ s in a..b, ∑ α : JetIndex2 K, factorialWeight ρ α.1.val *
          (∫ x, clipWeight B (C.W m s x) * ‖(WithLp.toLp 2 (fun k : Fin 2 => L α s k x) :
            PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2)) +
        2 * (∫ s in a..b, ∑ α : JetIndex2 K, factorialWeight ρ α.1.val *
          (∫ x, clipWeight B (C.W m s x) * (‖R α s x‖ * ‖planeJetReadoutOperator K α (U s) x‖)))) *
        Real.exp (18 * C.lam m * (t - a)) := by
  dsimp only
  let T := planeIntervalTransport (E := E) a b hab v (fun t ht => (hv t ht).continuous) Mv hvb
  let D := cellMetricIntervalDiffusion (E := E) a b hab G
    (fun t ht k j => (hG t ht k j).continuous) hCell
  let e := fun (α : JetIndex2 K) t =>
    ∫ x, clipWeight B (C.W m t x) * ‖planeJetReadoutOperator K α (U t) x‖ ^ 2
  let d := fun (α : JetIndex2 K) t =>
    ∫ x, clipWeight B (C.W m t x) * ‖(WithLp.toLp 2 (fun k : Fin 2 =>
      planeH1GradientOperator (planeWordH1SliceOperator K α (W t)) k x) :
      PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2
  let p := fun (α : JetIndex2 K) t =>
    ∫ x, clipWeight B (C.W m t x) * ‖(WithLp.toLp 2 (fun k : Fin 2 =>
      (planeJetFluxOperator K α (Q t) - D t
        (planeH1GradientOperator (planeWordH1SliceOperator K α (W t)))) k x) :
      PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2
  let z := fun (α : JetIndex2 K) t =>
    ∫ x, clipWeight B (C.W m t x) *
      (‖(planeJetReadoutOperator K α (H t) + T t
        (planeH1GradientOperator (planeWordH1SliceOperator K α (W t)))) x‖ *
        ‖planeJetReadoutOperator K α (U t) x‖)
  have hint α := cellMetric_storedWord_residual_time_integrable a b hab v hv hvm Mv hvb G hG hGm
    hCell t₀ S ϖ zc N m Cw C hm U H W Q hH hQ hcurve B hB α
  have hp α : IntervalIntegrable (p α) volume a b :=
    intervalIntegrable_of_integrable_Icc hab (hint α).1
  have hz α : IntervalIntegrable (z α) volume a b :=
    intervalIntegrable_of_integrable_Icc hab (hint α).2
  have he t : (∑ α : JetIndex2 K, factorialWeight ρ α.1.val * e α t) =
      rawWeightedFactorialEnergy ρ (fun x => clipWeight B (C.W m t x)) (U t).toFunction.jet :=
    planeStoredWord_factorial_energy ρ _ (U t)
  intro t ht
  have hh := cellMetric_storedWords_clipped_value_energy_sum a b hab v hv hvm hdiv Mv hMv hvb
    G hG hGm hCell hGs t₀ S ϖ zc N m Cw C hm ha hb U H W Q hH hQ hcurve B hB ρ t ht
  simp_rw [mul_assoc, integral_const_mul, intervalIntegral.integral_const_mul] at hh
  rw [← mul_assoc (18 : ℝ) (C.lam m) (t - a)] at hh
  change (∑ α : JetIndex2 K, factorialWeight ρ α.1.val * (e α t + (1 / 2) * ∫ s in a..t, d α s)) ≤
    (∑ α : JetIndex2 K, factorialWeight ρ α.1.val *
      (e α a + 8 * (∫ s in a..b, p α s) + 2 * (∫ s in a..b, z α s))) *
      Real.exp (18 * C.lam m * (t - a)) at hh
  rw [finite_weighted_sum_add, finite_three_energy_budget_sum, he t, he a,
    intervalIntegral_weighted_sum a b _ p hp, intervalIntegral_weighted_sum a b _ z hz] at hh
  have hWt := hW.mono_measure
    (Measure.restrict_mono (Icc_subset_Icc le_rfl ht.2) le_rfl)
  have hd := planeStoredWord_gradient_interval_energy C m hm B hB ρ a t ht.1 W hWt
  change (∑ α : JetIndex2 K, factorialWeight ρ α.1.val * (∫ s in a..t, d α s)) = _ at hd
  have hhalf : (∑ α : JetIndex2 K, factorialWeight ρ α.1.val * ((1 / 2) * ∫ s in a..t, d α s)) =
      (1 / 2) * (∑ α : JetIndex2 K, factorialWeight ρ α.1.val * (∫ s in a..t, d α s)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α _
    ring
  rw [hhalf, hd] at hh
  exact hh

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Nonempty finite Fourier derivatives have a Pe-independent scalar-forced gap without a transverse premise. -/

theorem cellZeroDrift_generator_scalar_source_energy
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) (u : TorusHk 1 ℂ) (src : ComplexCellL2) :
    2 * (cellGeneratorForm ⟨fun t _ => G t, 0, θ, κ⟩ hG 0 measurable_const
      (by intro t x; simp) t u u + cellSourceFunctional θ src 0 u) +
      (3 / 4) * ∑ j, ‖cellDerivativeCLM j u‖ ^ 2 ≤
    (264 * (∑ j, ‖θ j‖ ^ 2) + 2 * ‖κ t‖ + 1) * ‖torusHkValueCLM u‖ ^ 2 + ‖src‖ ^ 2 := by
  have hd := cellDiffusionForm_sharp_garding ⟨fun t _ => G t, 0, θ, κ⟩ hG t u
  have hf := cellSourceFunctional_scalar_energy_le θ src u
  have hp : inner ℝ (cellScalarCLM (κ t) (torusHkValueCLM u)) (torusHkValueCLM u) ≤
      ‖κ t‖ * ‖torusHkValueCLM u‖ ^ 2 := by
    have hh := real_inner_le_norm (cellScalarCLM (κ t) (torusHkValueCLM u)) (torusHkValueCLM u)
    rw [cellScalarCLM_norm] at hh
    exact hh.trans_eq (by ring)
  rw [cellZeroDrift_generator_eq_diffusion]
  linarith only [hd, hf, hp]

/-! Genuine native transverse H2 sources are time L2 without fast smoothness assumptions. -/

def cellTransverseStrongSource
    (η Cw : ℝ) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) (U : TorusHk 2 ℂ) : ComplexCellL2 :=
  cellConstantMetricStrongDiffusionCLM G (fun j => (Real.sqrt η : ℂ) * ξ j) t U -
    cellScalarCLM Complex.I (cellFibreDriftCouplingCLM η Cw hCw hv hw ξ t (torusHkValueCLM U)) +
    cellScalarCLM (κ t) (torusHkValueCLM U)

end AVRegularity.CycleWords
end
