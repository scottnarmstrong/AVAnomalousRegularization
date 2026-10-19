-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Weighted.ScaledDriftNormAbsorption
public import AVRegularity.Weighted.ParameterCoefficientJetMeasurable
public import AVRegularity.CoupledEnergyPlane.Variational.PlaneWeakDifferenceCurve
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane
open AVRegularity.Analysis.Convolution
namespace AVRegularity.Weighted

/-! Actual stored words inherit the weak Hilbert time curve from the original source equation. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem plane_ordered_source_curve {K : ℕ} {a b : ℝ}
    (U H : ℝ → PlaneHk Set.univ K E)
    (W : ℝ → PlaneHk Set.univ (K + 1) E)
    (S : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (hU : ContinuousOn U (Set.Icc a b))
    (hW : MemLp W 2 (volume.restrict (Set.Icc a b)))
    (hH : MemLp H 2 (volume.restrict (Set.Icc a b)))
    (hS : MemLp S 2 (volume.restrict (Set.Icc a b)))
    (hagrees : ∀ᵐ r ∂volume.restrict (Set.Icc a b),
      U r = truncatePlaneHk (Nat.le_succ K) (W r))
    (heq : ∀ s ∈ Set.Icc a b, ∀ t ∈ Set.Icc a b, s ≤ t →
      ∀ Z : PlaneHk Set.univ 1 E,
      inner ℝ (planeHkValueOperator K (U t)) (planeHkValueOperator 1 Z) -
        inner ℝ (planeHkValueOperator K (U s)) (planeHkValueOperator 1 Z) =
      ∫ r in s..t, inner ℝ (planeHkValueOperator K (H r)) (planeHkValueOperator 1 Z) -
        inner ℝ (planeFluxValueOperator K (S r)) (planeH1GradientOperator Z))
    (α : JetIndex2 K) :
    PlaneWeakHilbertCurve a b (fun t => planeJetReadoutOperator K α (U t))
      (fun t => planeWordH1SliceOperator K α (W t))
      (fun t => planeSourceDual (planeJetReadoutOperator K α (H t))
        (planeJetFluxOperator K α (S t))) := by
  refine ⟨(planeJetReadoutOperator K α).continuous.comp_continuousOn hU,
    (planeWordH1SliceOperator K α).comp_memLp' hW,
    planeJetSourceDual_memLp H S hH hS α, ?_, ?_⟩
  · filter_upwards [hagrees] with t ht
    rw [ht, planeWordH1Slice_value]
    rfl
  · intro s hs t ht hst Z
    have hi := plane_ordered_source_increment U H S hH hS hs ht hst
      (heq s hs t ht hst) α Z
    simp only [planeJetReadoutOperator_apply]
    rw [hi]
    apply intervalIntegral.integral_congr
    intro r _
    dsimp only
    rw [planeSourceDual_pair]
    simp only [planeJetSourcePair,
      PiLp.inner_apply, planeJetFluxOperator_apply]

end AVRegularity.Weighted
end

section
open Homogenization
namespace AVRegularity.Weighted

/-! The actual compact flux production obeys the pointwise energy budget. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def cutoffFluxProduction
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (v : Vec 2 → Vec 2)
    (q χ : Vec 2 → ℝ) (Φ : Fin 2 → Vec 2 → ℝ) (dt : Vec 2 → ℝ)
    (x : Vec 2) (du F : PiLp 2 (fun _ : Fin 2 => E)) (u : E) : ℝ :=
  let p : PiLp 2 (fun _ : Fin 2 => ℝ) := WithLp.toLp 2 (fun i => fderiv ℝ q x (basisVec i))
  let h : PiLp 2 (fun _ : Fin 2 => ℝ) := WithLp.toLp 2 (fun i => fderiv ℝ χ x (basisVec i))
  let φ : PiLp 2 (fun _ : Fin 2 => ℝ) := WithLp.toLp 2 (fun i => Φ i x)
  (χ x ^ 2 * dt x + ∑ i : Fin 2,
    fderiv ℝ (fun y => χ y ^ 2 * scalarChartFlux v G q Φ i y) x (basisVec i)) * ‖u‖ ^ 2 -
    2 * inner ℝ du (scalarHilbertTensor
      (χ x ^ 2 • φ + (2 * χ x * q x) • finiteMetricFlux (G x) h) u) -
    2 * inner ℝ F ((χ x ^ 2 * q x) • du + χ x ^ 2 • scalarHilbertTensor p u +
      (2 * χ x * q x) • scalarHilbertTensor h u) -
    2 * χ x ^ 2 * q x * (∑ k : Fin 2, ∑ j : Fin 2,
      G x k j * inner ℝ (du k) (du j)) + χ x ^ 2 * q x * ‖du‖ ^ 2

theorem cutoff_flux_energy_pointwise
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ)
    (hg4 : g ≤ 1 / 4) (hG : IsMetricNearIdentity G g)
    (t : ℝ) (x : Vec 2) (hGs : (G t x).IsSymm)
    (v : Vec 2 → Vec 2) (q χ : Vec 2 → ℝ) (Φ : Fin 2 → Vec 2 → ℝ)
    (hχd : Differentiable ℝ χ)
    (hA : ∀ i, Differentiable ℝ (scalarChartFlux v (G t) q Φ i))
    (dt : ℝ) {lam M η : ℝ} (hlam : 0 ≤ lam) (hM : 0 ≤ M) (hη : 0 ≤ η)
    (hq : 0 ≤ q x) (hχ : 0 ≤ χ x) (hχ1 : χ x ≤ 1)
    (hv : ‖v x‖ ≤ M) (hdχ : ‖fderiv ℝ χ x‖ ≤ η)
    (hp : ‖(WithLp.toLp 2 (fun i => fderiv ℝ q x (basisVec i)) :
      PiLp 2 (fun _ : Fin 2 => ℝ))‖ ≤ Real.sqrt lam * q x)
    (hΦ : ‖(WithLp.toLp 2 (fun i => Φ i x) : PiLp 2 (fun _ : Fin 2 => ℝ))‖ ≤
      Real.sqrt lam * q x)
    (hdef : dt + (∑ i : Fin 2,
      fderiv ℝ (scalarChartFlux v (G t) q Φ i) x (basisVec i)) ≤ 2 * lam * q x)
    (du F : PiLp 2 (fun _ : Fin 2 => E)) (u : E) :
    let p : PiLp 2 (fun _ : Fin 2 => ℝ) := WithLp.toLp 2 (fun i => fderiv ℝ q x (basisVec i))
    let h : PiLp 2 (fun _ : Fin 2 => ℝ) := WithLp.toLp 2 (fun i => fderiv ℝ χ x (basisVec i))
    let φ : PiLp 2 (fun _ : Fin 2 => ℝ) := WithLp.toLp 2 (fun i => Φ i x)
    (χ x ^ 2 * dt + ∑ i : Fin 2,
      fderiv ℝ (fun y => χ y ^ 2 * scalarChartFlux v (G t) q Φ i y) x (basisVec i)) * ‖u‖ ^ 2 -
      2 * inner ℝ du (scalarHilbertTensor
        (χ x ^ 2 • φ + (2 * χ x * q x) • finiteMetricFlux (G t x) h) u) -
      2 * inner ℝ F ((χ x ^ 2 * q x) • du + χ x ^ 2 • scalarHilbertTensor p u +
        (2 * χ x * q x) • scalarHilbertTensor h u) -
      2 * χ x ^ 2 * q x * (∑ k : Fin 2, ∑ j : Fin 2,
        G t x k j * inner ℝ (du k) (du j)) + χ x ^ 2 * q x * ‖du‖ ^ 2 ≤
    18 * lam * χ x ^ 2 * q x * ‖u‖ ^ 2 + 8 * q x * ‖F‖ ^ 2 +
      (4096 * η ^ 2 + 16 * M * η) * q x * ‖u‖ ^ 2 := by
  let p : PiLp 2 (fun _ : Fin 2 => ℝ) := WithLp.toLp 2 (fun i => fderiv ℝ q x (basisVec i))
  let h : PiLp 2 (fun _ : Fin 2 => ℝ) := WithLp.toLp 2 (fun i => fderiv ℝ χ x (basisVec i))
  let φ : PiLp 2 (fun _ : Fin 2 => ℝ) := WithLp.toLp 2 (fun i => Φ i x)
  let V : PiLp 2 (fun _ : Fin 2 => ℝ) := WithLp.toLp 2 (v x)
  have hV : ‖V‖ ≤ 2 * M :=
    (scalar_vector_piLp_norm_le_two (v x)).trans (by linarith only [hv])
  have hh : ‖h‖ ≤ 2 * η := cutoff_gradient_piLp_norm_le χ x hdχ
  have hflux := cutoff_chart_metric_pointwise G g hg4 hG t x hGs V p φ h du F u
    hq hlam hM hχ hχ1 hη hV hp hΦ hh
  have hcut := cutoff_defect_le χ hχd (scalarChartFlux v (G t) q Φ) hA x dt (q x)
    (2 * lam) hdef
  have he : (∑ i : Fin 2, fderiv ℝ χ x (basisVec i) * scalarChartFlux v (G t) q Φ i x) =
      inner ℝ h (q x • V + finiteMetricFlux (G t x) p - φ) := by
    simp only [PiLp.inner_apply, Real.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    change fderiv ℝ χ x (basisVec i) *
      (q x * v x i + ∑ j : Fin 2, G t x i j * fderiv ℝ q x (basisVec j) - Φ i x) =
      fderiv ℝ χ x (basisVec i) *
        (q x * v x i + ∑ j : Fin 2, G t x i j * fderiv ℝ q x (basisVec j) - Φ i x)
    rfl
  rw [he] at hcut
  have hmass := mul_le_mul_of_nonneg_right hcut (sq_nonneg ‖u‖)
  have hr := cutoff_residual_eq (G t x) V p φ h du F u (χ x) (q x)
  change _ ≤ _
  nlinarith only [hflux, hmass, hr]

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.Weighted

/-! The actual metric product jet is the exact sum of its positional derivative masks. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeMetricGradientCarrier_jet_masks_ae {K : ℕ}
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ k a, ContDiff ℝ (K : ℕ) (fun x => G x k a))
    (M : Fin (K + 1) → ℝ)
    (hb : ∀ l : Fin (K + 1), ∀ x k a,
      ‖iteratedFDeriv ℝ l.val (fun y => G y k a) x‖ ≤ M l)
    (p : PlaneHk Set.univ (K + 1) E) (j : Fin (K + 1))
    (w : DerivativeWord2 j.val) :
    (planeMetricGradientCarrier G hG M hb p).val ⟨j, w⟩
      =ᵐ[volume.restrict Set.univ] fun x => ∑ m : PositionMask j.val,
        metricMaskTerm (Nat.le_of_lt_succ j.isLt) G p.toFunction.jet m w x := by
  have hp : (planeMetricGradientCarrier G hG M hb p).val ⟨j, w⟩
      =ᵐ[volume.restrict Set.univ] multiplicationRawJet
        (fun x => metricFiberCoefficient (G x)) (planeGradientTensor p).toFunction.jet ⟨j, w⟩ := by
    unfold planeMetricGradientCarrier
    exact planeCoefficientCarrier_jet_ae _ _ _ _ _
  have hg : ∀ᵐ x ∂volume.restrict Set.univ, ∀ m : PositionMask j.val,
      (planeGradientTensor p).val (maskJetIndex (Nat.le_of_lt_succ j.isLt) m w) x =
        WithLp.toLp 2 (fun k : Fin 2 => p.val
          ⟨⟨maskRightLength j.val m + 1, by have := maskRightLength_le j.val m; omega⟩,
            Fin.snoc (maskWordEquiv 2 j.val m w).2 k⟩ x) := by
    apply ae_all_iff.mpr
    intro m
    exact planeGradientTensor_jet_ae p _ _
  filter_upwards [hp, hg] with x hx hgrad
  rw [hx]
  unfold multiplicationRawJet
  apply Finset.sum_congr rfl
  intro m _
  unfold multiplicationTerm
  rw [metricFiberCoefficient_orderedDerivative G (maskLeftLength j.val m)
    (fun k a => (hG k a).of_le (by exact_mod_cast
      (maskLeftLength_le j.val m).trans (Nat.le_of_lt_succ j.isLt)))]
  change metricFiberCoefficient _ ((planeGradientTensor p).val (maskJetIndex _ m w) x) = _
  rw [hgrad m]
  exact metricFiberCoefficient_apply
    (fun k a => orderedScalarDerivative (fun y => G y k a) (maskLeftLength j.val m)
      (maskWordEquiv 2 j.val m w).1 x) _

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.Weighted

/-! The literal unweighted retained gradient energy equals the Sobolev factorial norm. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem rawWeightedGradientEnergy_one {K : ℕ} (ρ : ℝ) (W : PlaneHk Set.univ (K + 1) E) :
    rawWeightedGradientEnergy ρ (fun _ => 1) W.toFunction.jet = gradFactorialNormSq ρ W.val := by
  rw [← planeGradientTensor_factorialNormSq]
  unfold rawWeightedGradientEnergy factorialNormSq derivativeNormSq
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply Finset.sum_congr rfl
  intro w _
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq, Measure.restrict_univ]
  apply integral_congr_ae
  have hh := planeGradientTensor_jet_ae W j w
  simp only [Measure.restrict_univ] at hh
  filter_upwards [hh] with x hx
  rw [hx, one_mul]
  rfl

end AVRegularity.Weighted
end

section
open Homogenization Set
namespace AVRegularity.Weighted

/-! Pointwise weighted energy production with the literal clipped ChartWeights fields. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem chartWeights_clipped_cutoff_energy_pointwise
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {t₀ S ϖ : ℝ} {zc : Vec 2} {N : ℕ} {Cw : ℕ → ℝ}
    (W : ChartWeights G v t₀ S ϖ zc N Cw) (m : ℕ) (hm : m ≤ N)
    (t : ℝ) (ht : t ∈ Icc t₀ (t₀ + S)) (B g : ℝ) (hB : 0 < B)
    (hg4 : g ≤ 1 / 4) (hGnear : IsMetricNearIdentity G g)
    (hv : ContDiff ℝ 1 (v t))
    (hdiv : ∀ x, ∑ j : Fin 2, fderiv ℝ (v t) x (basisVec j) j = 0)
    (hGs : ∀ x, (G t x).IsSymm)
    (hG : ∀ i j : Fin 2, ContDiff ℝ 1 (fun x => G t x i j))
    (χ : Vec 2 → ℝ) (hχd : Differentiable ℝ χ) (x : Vec 2)
    {M η : ℝ} (hM : 0 ≤ M) (hη : 0 ≤ η)
    (hχ : 0 ≤ χ x) (hχ1 : χ x ≤ 1)
    (hvb : ‖v t x‖ ≤ M) (hdχ : ‖fderiv ℝ χ x‖ ≤ η)
    (du F : PiLp 2 (fun _ : Fin 2 => E)) (u : E) :
    let q := fun y => clipWeight B (W.W m t y)
    let Φ := fun i y => clipWeightDeriv B (W.W m t y) * W.Phi m t y i
    let dt := fun y => deriv (fun s => clipWeight B (W.W m s y)) t
    cutoffFluxProduction (G t) (v t) q χ Φ dt x du F u ≤
      18 * W.lam m * χ x ^ 2 * q x * ‖u‖ ^ 2 + 8 * q x * ‖F‖ ^ 2 +
        (4096 * η ^ 2 + 16 * M * η) * q x * ‖u‖ ^ 2 := by
  obtain ⟨hA, hdef⟩ := chartWeights_clipped_flux_defect W m hm t ht B g hB hg4 hGnear
    hv hdiv hGs hG
  obtain ⟨hp, hΦ⟩ := chartWeights_clipped_log_norm_bounds W m hm t ht x B hB
  exact cutoff_flux_energy_pointwise G g hg4 hGnear t x (hGs x) (v t)
    (fun y => clipWeight B (W.W m t y)) χ
    (fun i y => clipWeightDeriv B (W.W m t y) * W.Phi m t y i) hχd
    (fun i => (hA i).differentiable (by norm_num))
    (deriv (fun s => clipWeight B (W.W m s x)) t) (W.lam_bound m hm).1 hM hη
    (clipWeight_pos hB (W.pos m hm t x)).le hχ hχ1 hvb hdχ hp hΦ (hdef x) du F u

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Separate the actual differentiated metric flux into principal and commutator terms. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem metricMask_sum_split {K j : ℕ} (hj : j ≤ K)
    (D : RawJet2 (K + 1) E) (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (w : DerivativeWord2 j) (x : Vec 2) :
    (∑ m : PositionMask j, metricMaskTerm hj G D m w x) =
      finiteMetricFlux (G x)
        (WithLp.toLp 2 (fun k : Fin 2 => D ⟨⟨j + 1, by omega⟩, Fin.snoc w k⟩ x)) +
      metricCommutatorTerm hj G D w x := by
  rw [← metricMaskTerm_principal_sum hj D G w x]
  unfold metricCommutatorTerm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hm : maskLeftLength j m = 0
  · simp [hm]
  · have hp : 1 ≤ maskLeftLength j m := by omega
    simp [hm, hp]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeMetricGradientCarrier_principal_commutator_ae {K : ℕ}
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ k a, ContDiff ℝ (K : ℕ) (fun x => G x k a))
    (M : Fin (K + 1) → ℝ)
    (hb : ∀ l : Fin (K + 1), ∀ x k a,
      ‖iteratedFDeriv ℝ l.val (fun y => G y k a) x‖ ≤ M l)
    (p : PlaneHk Set.univ (K + 1) E) (j : Fin (K + 1))
    (w : DerivativeWord2 j.val) :
    (planeMetricGradientCarrier G hG M hb p).val ⟨j, w⟩
      =ᵐ[volume.restrict Set.univ] fun x => finiteMetricFlux (G x)
        (WithLp.toLp 2 (fun k : Fin 2 => p.toFunction.jet
          ⟨⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩, Fin.snoc w k⟩ x)) +
        metricCommutatorTerm (Nat.le_of_lt_succ j.isLt) G p.toFunction.jet w x := by
  filter_upwards [planeMetricGradientCarrier_jet_masks_ae G hG M hb p j w] with x hx
  exact hx.trans (metricMask_sum_split (Nat.le_of_lt_succ j.isLt) p.toFunction.jet G w x)

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization
namespace AVRegularity.Weighted

/-! Bounded clipped chart weights supply the actual time-integrable energy budgets. -/

theorem chartWeights_clipped_time_coefficient
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {t₀ S ϖ : ℝ} {zc : Vec 2} {N : ℕ} {Cw : ℕ → ℝ}
    (W : ChartWeights G v t₀ S ϖ zc N Cw) (m : ℕ) (hm : m ≤ N)
    (B : ℝ) (hB : 0 < B) :
    (∀ t, Continuous (fun x => clipWeight B (W.W m t x))) ∧
    Measurable (fun p : ℝ × Vec 2 => clipWeight B (W.W m p.1 p.2)) ∧
    (∀ t x, |clipWeight B (W.W m t x)| ≤ B) := by
  have hd := clipped_field_contDiff B hB (fun p => W.W m p.1 p.2) (W.smooth m hm).1
    (fun p => W.pos m hm p.1 p.2)
  refine ⟨fun t => (chartWeights_clipped_spatial_regularity W m hm t B hB).1.continuous,
    hd.continuous.measurable, ?_⟩
  intro t x
  rw [abs_of_pos (clipWeight_pos hB (W.pos m hm t x))]
  exact clipWeight_le_bound hB (W.pos m hm t x)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [BorelSpace E] [CompleteSpace E] in
theorem chartWeights_clipped_scalar_time_integrable
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {t₀ S ϖ : ℝ} {zc : Vec 2} {N : ℕ} {Cw : ℕ → ℝ}
    (W : ChartWeights G v t₀ S ϖ zc N Cw) (m : ℕ) (hm : m ≤ N)
    (B : ℝ) (hB : 0 < B) (μ : Measure ℝ)
    (U : ℝ → Lp E 2 (volume : Measure (Vec 2))) (hU : MemLp U 2 μ) :
    Integrable (fun t => ∫ x, clipWeight B (W.W m t x) * ‖U t x‖ ^ 2) μ := by
  obtain ⟨hc, hj, hb⟩ := chartWeights_clipped_time_coefficient W m hm B hB
  exact weighted_spatial_energy_time_integrable _ hc hj hB.le hb U hU

omit [BorelSpace E] [CompleteSpace E] in
theorem chartWeights_clipped_finite_time_integrable
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {t₀ S ϖ : ℝ} {zc : Vec 2} {N : ℕ} {Cw : ℕ → ℝ}
    (W : ChartWeights G v t₀ S ϖ zc N Cw) (m : ℕ) (hm : m ≤ N)
    (B : ℝ) (hB : 0 < B) (μ : Measure ℝ)
    (U : ℝ → PiLp 2 (fun _ : Fin 2 => Lp E 2 (volume : Measure (Vec 2))))
    (hU : MemLp U 2 μ) :
    Integrable (fun t => ∫ x, clipWeight B (W.W m t x) * ‖(WithLp.toLp 2
      (fun i => U t i x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) μ := by
  obtain ⟨hc, hj, hb⟩ := chartWeights_clipped_time_coefficient W m hm B hB
  exact finite_weighted_spatial_energy_time_integrable _ hc hj hB.le hb U hU

omit [BorelSpace E] [CompleteSpace E] in
theorem chartWeights_clipped_cutoff_finite_time_integrable
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {t₀ S ϖ : ℝ} {zc : Vec 2} {N : ℕ} {Cw : ℕ → ℝ}
    (W : ChartWeights G v t₀ S ϖ zc N Cw) (m : ℕ) (hm : m ≤ N)
    (B : ℝ) (hB : 0 < B) (χ : Vec 2 → ℝ) (hχ : Continuous χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1) (μ : Measure ℝ)
    (U : ℝ → PiLp 2 (fun _ : Fin 2 => Lp E 2 (volume : Measure (Vec 2))))
    (hU : MemLp U 2 μ) :
    Integrable (fun t => ∫ x, χ x ^ 2 * clipWeight B (W.W m t x) * ‖(WithLp.toLp 2
      (fun i => U t i x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) μ := by
  obtain ⟨hc, hj, hb⟩ := chartWeights_clipped_time_coefficient W m hm B hB
  have hjq : Measurable (Function.uncurry (fun t x => χ x ^ 2 * clipWeight B (W.W m t x))) := by
    convert ((hχ.measurable.comp measurable_snd).pow_const 2).mul hj using 1
    funext p
    rfl
  apply finite_weighted_spatial_energy_time_integrable (E := E)
    (fun t x => χ x ^ 2 * clipWeight B (W.W m t x))
    (fun t => (hχ.pow 2).mul (hc t))
    hjq hB.le _ U hU
  intro t x
  rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  have hs : χ x ^ 2 ≤ 1 := by nlinarith only [hχ0 x, hχ1 x]
  exact (mul_le_mul hs (hb t x) (abs_nonneg _) (by norm_num)).trans_eq (one_mul B)

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.Weighted

/-! Measurable-time metrics act on the actual Bochner Sobolev gradient class. -/

variable {T E : Type*} [MeasurableSpace T] [Nonempty T]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def metricFiberArrayBudget {K : ℕ} (M : Fin (K + 1) → ℝ) (l : Fin (K + 1)) : ℝ :=
  (Fintype.card (DerivativeWord2 l.val) : ℝ) * (4 * M l)

omit [MeasurableSpace T] in
theorem metricFiberArrayBudget_nonneg {K : ℕ}
    (G : T → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (M : Fin (K + 1) → ℝ)
    (hb : ∀ t (l : Fin (K + 1)) x k a,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k a) x‖ ≤ M l) (l : Fin (K + 1)) :
    0 ≤ metricFiberArrayBudget M l := by
  let t : T := Classical.choice inferInstance
  have hm := (norm_nonneg (iteratedFDeriv ℝ l.val (fun y => G t y 0 0) 0)).trans
    (hb t l 0 0 0)
  exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num) hm)

def metricProductTimeCLM {K : ℕ} (μ : Measure T)
    (G : T → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hGm : Measurable (Function.uncurry G))
    (hG : ∀ t k a, ContDiff ℝ (K : ℕ) (fun x => G t x k a))
    (M : Fin (K + 1) → ℝ)
    (hb : ∀ t (l : Fin (K + 1)) x k a,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k a) x‖ ≤ M l) :
    Lp (PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) 2 μ →L[ℝ]
      Lp (PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) 2 μ :=
  by
    let C : T → Vec 2 → (PiLp 2 (fun _ : Fin 2 => E)) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => E) := fun t x => metricFiberCoefficient (G t x)
    have hm : Measurable (Function.uncurry C) :=
      metricFiberCoefficient_measurable (E := E) (Function.uncurry G) hGm
    have hc : ∀ t, ContDiff ℝ (K : ℕ) (C t) :=
      fun t => metricFiberCoefficient_contDiff (E := E) (G t) (hG t)
    let B := metricFiberArrayBudget M
    have hB : ∀ l, 0 ≤ B l := metricFiberArrayBudget_nonneg G M hb
    have hCb : ∀ (t : T) (l : Fin (K + 1)) (x : Vec 2),
        ‖coefficientDerivativeArray (C t) l.val x‖ ≤ B l :=
      fun t l x => metricFiberCoefficient_array_bound_entries (E := E) (G t) (hG t) M (hb t) l x
    exact productPlaneHkTimeCLM μ C hm hc B hB hCb

theorem metricProductTimeCLM_ae {K : ℕ} (μ : Measure T)
    (G : T → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hGm : Measurable (Function.uncurry G))
    (hG : ∀ t k a, ContDiff ℝ (K : ℕ) (fun x => G t x k a))
    (M : Fin (K + 1) → ℝ)
    (hb : ∀ t (l : Fin (K + 1)) x k a,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k a) x‖ ≤ M l)
    (U : Lp (PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) 2 μ) :
    metricProductTimeCLM μ G hGm hG M hb U =ᵐ[μ] fun t =>
      (U t).mulCoefficient (fun x => metricFiberCoefficient (G t x))
        (metricFiberCoefficient_contDiff (G t) (hG t))
        (metricFiberCoefficient_array_bound_entries (G t) (hG t) M (hb t)) :=
  productPlaneHkTimeCLM_ae (E := PiLp 2 (fun _ : Fin 2 => E))
    (F := PiLp 2 (fun _ : Fin 2 => E)) μ
    (fun t x => metricFiberCoefficient (E := E) (G t x))
    (metricFiberCoefficient_measurable (E := E) (Function.uncurry G) hGm)
    (fun t => metricFiberCoefficient_contDiff (E := E) (G t) (hG t))
    (metricFiberArrayBudget M) (metricFiberArrayBudget_nonneg G M hb)
    (fun t => metricFiberCoefficient_array_bound_entries (E := E) (G t) (hG t) M (hb t)) U

local instance metricTimeInputAdd (K : ℕ) : AddCommGroup (PlaneHk Set.univ K E) := inferInstance
local instance metricTimeInputTopAdd (K : ℕ) : IsTopologicalAddGroup (PlaneHk Set.univ K E) := inferInstance

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! The actual measurable-time metric flux of an energy-class lift is Bochner square integrable. -/

variable {T E : Type*} [MeasurableSpace T] [Nonempty T]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance metricIntegrableInputAdd (K : ℕ) : AddCommGroup (PlaneHk Set.univ K E) := inferInstance
local instance metricIntegrableInputTopAdd (K : ℕ) : IsTopologicalAddGroup (PlaneHk Set.univ K E) := inferInstance
theorem planeMetricGradientCarrier_memLp {K : ℕ} (μ : Measure T)
    (G : T → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hGm : Measurable (Function.uncurry G))
    (hG : ∀ t k a, ContDiff ℝ (K : ℕ) (fun x => G t x k a))
    (M : Fin (K + 1) → ℝ)
    (hb : ∀ t (l : Fin (K + 1)) x k a,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k a) x‖ ≤ M l)
    (w : T → PlaneHk Set.univ (K + 1) E) (hw : MemLp w 2 μ) :
    MemLp (fun t => planeMetricGradientCarrier (E := E) (G t) (hG t) M (hb t) (w t)) 2 μ := by
  have hg := (AVRegularity.CoupledEnergyPlane.Variational.planeGradientTensorOperator
    (E := E) K).comp_memLp' hw
  let f := (AVRegularity.CoupledEnergyPlane.Variational.planeGradientTensorOperator
    (E := E) K) ∘ w
  let U := hg.toLp f
  let V := metricProductTimeCLM (E := E) μ G hGm hG M hb U
  have he : V =ᵐ[μ] fun t => planeMetricGradientCarrier (E := E)
      (G t) (hG t) M (hb t) (w t) := by
    filter_upwards [metricProductTimeCLM_ae (E := E) μ G hGm hG M hb U,
      hg.coeFn_toLp] with t ht hu
    rw [ht, hu]
    dsimp only [Function.comp_apply]
    rw [AVRegularity.CoupledEnergyPlane.Variational.planeGradientTensorOperator_apply]
    rfl
  exact (memLp_congr_ae he).mp (Lp.memLp V)

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization
namespace AVRegularity.Weighted

/-! The actual clipped cutoff value-product budget is time integrable. -/

variable {E : Type*} [NormedAddCommGroup E]

theorem chartWeights_clipped_cutoff_value_product_integrable
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {t₀ S ϖ : ℝ} {zc : Vec 2} {N : ℕ} {Cw : ℕ → ℝ}
    (W : ChartWeights G v t₀ S ϖ zc N Cw) (m : ℕ) (hm : m ≤ N)
    (B : ℝ) (hB : 0 < B) (χ : Vec 2 → ℝ) (hχ : Continuous χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1) (μ : Measure ℝ)
    (U V : ℝ → Lp E 2 (volume : Measure (Vec 2))) (hU : MemLp U 2 μ) (hV : MemLp V 2 μ) :
    Integrable (fun t => ∫ x, (χ x ^ 2 * clipWeight B (W.W m t x)) *
      (‖U t x‖ * ‖V t x‖)) μ := by
  obtain ⟨hc, hj, hb⟩ := chartWeights_clipped_time_coefficient W m hm B hB
  have hjq : Measurable (Function.uncurry (fun t x => χ x ^ 2 * clipWeight B (W.W m t x))) := by
    convert ((hχ.measurable.comp measurable_snd).pow_const 2).mul hj using 1
    funext p
    rfl
  apply weighted_spatial_value_product_time_integrable
    (fun t x => χ x ^ 2 * clipWeight B (W.W m t x))
    (fun t => (hχ.pow 2).mul (hc t)) hjq hB.le _ U V hU hV
  intro t x
  rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  have hs : χ x ^ 2 ≤ 1 := by nlinarith only [hχ0 x, hχ1 x]
  exact (mul_le_mul_of_nonneg_right hs (abs_nonneg _)).trans
    (by simpa only [one_mul] using hb t x)

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization Filter
open scoped ENNReal Topology
namespace AVRegularity.Weighted

/-! Actual nonnegative weighted quadratic energies of the plane Hilbert readouts. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def chartScalarEnergy (q : Vec 2 → ℝ) (U : Lp E 2 (volume : Measure (Vec 2))) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (q x * ‖U x‖ ^ 2)

def chartFiniteEnergy (q : Vec 2 → ℝ)
    (U : PiLp 2 (fun _ : Fin 2 => Lp E 2 (volume : Measure (Vec 2)))) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (q x * ‖(WithLp.toLp 2 (fun i => U i x) :
    PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2)

omit [InnerProductSpace ℝ E] in
theorem chartScalarEnergy_mono (q w : Vec 2 → ℝ) (h : ∀ x, q x ≤ w x)
    (U : Lp E 2 (volume : Measure (Vec 2))) : chartScalarEnergy q U ≤ chartScalarEnergy w U := by
  apply lintegral_mono
  intro x
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (h x) (sq_nonneg _))

omit [InnerProductSpace ℝ E] in
theorem chartFiniteEnergy_mono (q w : Vec 2 → ℝ) (h : ∀ x, q x ≤ w x)
    (U : PiLp 2 (fun _ : Fin 2 => Lp E 2 (volume : Measure (Vec 2)))) :
    chartFiniteEnergy q U ≤ chartFiniteEnergy w U := by
  apply lintegral_mono
  intro x
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (h x) (sq_nonneg _))

theorem chartScalarEnergy_eq_ofReal (q : Vec 2 → ℝ) (hq : Continuous q)
    {B : ℝ} (hb : ∀ x, |q x| ≤ B) (hq0 : ∀ x, 0 ≤ q x)
    (U : Lp E 2 (volume : Measure (Vec 2))) :
    chartScalarEnergy q U = ENNReal.ofReal (∫ x, q x * ‖U x‖ ^ 2) := by
  exact (ofReal_integral_eq_lintegral_ofReal
    (bounded_scalar_Lp_normSq_integrable U q hq.aestronglyMeasurable
      (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x)))
    (Eventually.of_forall (fun x => mul_nonneg (hq0 x) (sq_nonneg _)))).symm

theorem chartFiniteEnergy_eq_ofReal (q : Vec 2 → ℝ) (hq : Continuous q)
    {B : ℝ} (hb : ∀ x, |q x| ≤ B) (hq0 : ∀ x, 0 ≤ q x)
    (U : PiLp 2 (fun _ : Fin 2 => Lp E 2 (volume : Measure (Vec 2)))) :
    chartFiniteEnergy q U = ENNReal.ofReal (∫ x, q x * ‖(WithLp.toLp 2
      (fun i => U i x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) := by
  exact (ofReal_integral_eq_lintegral_ofReal
    (bounded_scalar_finiteLp_normSq_integrable U q hq.aestronglyMeasurable
      (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x)))
    (Eventually.of_forall (fun x => mul_nonneg (hq0 x) (sq_nonneg _)))).symm

omit [InnerProductSpace ℝ E] in
theorem chartScalarEnergy_clipping_tendsto (w : Vec 2 → ℝ) (hw : ∀ x, 0 < w x)
    (hwm : ∀ n : ℕ, Measurable (fun x => clipWeight ((n : ℝ) + 1) (w x)))
    (U : Lp E 2 (volume : Measure (Vec 2))) :
    Tendsto (fun n : ℕ => chartScalarEnergy (fun x => clipWeight ((n : ℝ) + 1) (w x)) U)
      atTop (𝓝 (chartScalarEnergy w U)) :=
  lintegral_clipWeight_tendsto w (fun x => ‖U x‖ ^ 2) hw
    ((Lp.aestronglyMeasurable U).norm.aemeasurable.pow_const 2) (fun _ => sq_nonneg _) hwm

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.Weighted

/-! Integrating the pointwise cutoff flux production gives the actual weak energy production. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeScalarDual_cutoff_production_identity
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ 1 v)
    {Mv : ℝ} (hMv : 0 ≤ Mv) (hvb : ∀ k x, |v x k| ≤ Mv)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ k j, ContDiff ℝ 1 (fun x => G x k j)) (hGs : ∀ x, (G x).IsSymm)
    {MG : ℝ} (hMG : 0 ≤ MG) (hGb : ∀ k j x, |G x k j| ≤ MG)
    (q χ : Vec 2 → ℝ) (hq : ContDiff ℝ 2 q) (hχ : ContDiff ℝ 2 χ)
    (hsχ : HasCompactSupport χ) (Φ : Fin 2 → Vec 2 → ℝ)
    (hΦ : ∀ i, ContDiff ℝ 1 (Φ i)) (dt : Vec 2 → ℝ) (hdt : Continuous dt)
    (u z : PlaneHk Set.univ 1 E) (F : PlaneFluxL2 E)
    (hz : planeHkValueOperator (E := E) 1 z =ᵐ[volume]
      fun x => (χ x ^ 2 * q x) • planeHkValueOperator (E := E) 1 u x) :
    (2 * inner ℝ (planeWeakDualRepresentative
      (planeScalarTransport v (fun k => (contDiff_pi.mp hv k).continuous) hMv hvb)
      (planeScalarDiffusion G (fun k j => (hG k j).continuous) hMG hGb) u F) z +
    (∫ x, χ x ^ 2 * dt x * ‖planeHkValueOperator (E := E) 1 u x‖ ^ 2) +
    (∫ x, χ x ^ 2 * q x * ‖(WithLp.toLp 2
      (fun i => planeH1GradientOperator (E := E) u i x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) =
    ∫ x, cutoffFluxProduction G v q χ Φ dt x
      (WithLp.toLp 2 (fun i => planeH1GradientOperator (E := E) u i x))
      (WithLp.toLp 2 (fun i => F i x)) (planeHkValueOperator (E := E) 1 u x)) ∧
    Integrable (fun x => cutoffFluxProduction G v q χ Φ dt x
      (WithLp.toLp 2 (fun i => planeH1GradientOperator (E := E) u i x))
      (WithLp.toLp 2 (fun i => F i x)) (planeHkValueOperator (E := E) 1 u x)) volume := by
  let U := planeHkValueOperator (E := E) 1 u
  let du := planeH1GradientOperator (E := E) u
  let qt := fun x => χ x ^ 2 * q x
  let c : Fin 2 → Vec 2 → ℝ := fun i x => qt x * v x i +
    ∑ j : Fin 2, G x j i * fderiv ℝ qt x (basisVec j)
  let a := cutoffMainFlux v G q χ Φ
  let b := cutoffCorrectionFlux G q χ Φ
  have hqt : ContDiff ℝ 2 qt := (hχ.pow 2).mul hq
  have hst : HasCompactSupport qt := by
    convert (hsχ.mul_right (f' := χ)).mul_right (f' := q) using 1
    funext x
    exact congrArg (fun r => r * q x) (pow_two (χ x))
  obtain ⟨ha, hsa, hb, hsb, hsplit⟩ := cutoff_flux_split_regular v hv G hG q χ hq hχ hsχ Φ hΦ
  have hc i x : c i x = a i x + b i x := by
    change qt x * v x i + (∑ j : Fin 2, G x j i * fderiv ℝ qt x (basisVec j)) = _
    have he : (∑ j : Fin 2, G x j i * fderiv ℝ qt x (basisVec j)) =
        ∑ j : Fin 2, G x i j * fderiv ℝ qt x (basisVec j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [(hGs x).apply i j]
    rw [he]
    exact hsplit i x
  have hprod := planeScalarDual_compact_production_of_value v hv hMv hvb G hG hMG hGb
    qt hqt hst u z F hz
  have hdiv := planeH1_compact_divergence_split u c a b ha hb hsa hsb hc
  let mass := fun x => χ x ^ 2 * dt x * ‖U x‖ ^ 2
  let diva := fun x => (∑ i : Fin 2, fderiv ℝ (a i) x (basisVec i)) * ‖U x‖ ^ 2
  let T := fun x => inner ℝ (∑ i : Fin 2, b i x • du i x) (U x)
  let H := fun x => ∑ i : Fin 2, inner ℝ (F i x) (planeH1GradientOperator (E := E) z i x)
  let P := fun x => qt x * ∑ k : Fin 2, ∑ j : Fin 2,
    G x k j * inner ℝ (du k x) (du j x)
  let D := fun x => qt x * ‖(WithLp.toLp 2 (fun i => du i x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2
  have hmass : Integrable mass volume := by
    apply compact_scalar_normSq_integrable U _ ((hχ.continuous.pow 2).mul hdt)
    convert (hsχ.mul_right (f' := χ)).mul_right (f' := dt) using 1
    funext x
    exact congrArg (fun r => r * dt x) (pow_two (χ x))
  have hdiva : Integrable diva volume := compact_divergence_integrable U a ha hsa
  have hT : Integrable T volume := compact_scalar_gradient_pairing_integrable du U b
    (fun i => (hb i).continuous) hsb
  have hH : Integrable H volume := integrable_finsetSum _
    (fun i _ => L2.integrable_inner (F i) (planeH1GradientOperator (E := E) z i))
  obtain ⟨Mq, hMq⟩ := hqt.continuous.bounded_above_of_compact_support hst
  have hMq0 : 0 ≤ Mq := (norm_nonneg (qt 0)).trans (hMq 0)
  have hP : Integrable P volume := bounded_metric_quadratic_integrable du G
    (fun k j => (hG k j).continuous) hMG hGb qt hqt.continuous hMq0
    (by simpa only [← Real.norm_eq_abs] using hMq)
  have hD : Integrable D volume := bounded_scalar_finiteLp_normSq_integrable du qt
    hqt.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hMq)
  have hpoint : (fun x => cutoffFluxProduction G v q χ Φ dt x
      (WithLp.toLp 2 (fun i => du i x)) (WithLp.toLp 2 (fun i => F i x)) (U x)) =ᵐ[volume]
      fun x => mass x + diva x - 2 * T x - 2 * H x - 2 * P x + D x := by
    have hdz := planeH1_cutoff_gradient_ae χ q hχ hq hsχ u z hz
    filter_upwards [hdz] with x hx
    have hbvec : (χ x ^ 2 • (WithLp.toLp 2 (fun i => Φ i x) : PiLp 2 (fun _ : Fin 2 => ℝ)) +
        (2 * χ x * q x) • finiteMetricFlux (G x)
          (WithLp.toLp 2 (fun i => fderiv ℝ χ x (basisVec i)))) =
        WithLp.toLp 2 (fun i => b i x) := by
      apply PiLp.ext
      intro i
      rfl
    have hsource : inner ℝ (WithLp.toLp 2 (fun i => F i x))
        ((χ x ^ 2 * q x) • WithLp.toLp 2 (fun i => du i x) +
          χ x ^ 2 • scalarHilbertTensor (WithLp.toLp 2 (fun i => fderiv ℝ q x (basisVec i))) (U x) +
          (2 * χ x * q x) • scalarHilbertTensor
            (WithLp.toLp 2 (fun i => fderiv ℝ χ x (basisVec i))) (U x)) = H x := by
      rw [← hx]
      exact PiLp.inner_apply _ _
    unfold cutoffFluxProduction
    dsimp only
    rw [hbvec, finite_gradient_tensor_inner, hsource]
    have hdA : (∑ i : Fin 2, fderiv ℝ
        (fun y => χ y ^ 2 * scalarChartFlux v G q Φ i y) x (basisVec i)) =
        ∑ i : Fin 2, fderiv ℝ (a i) x (basisVec i) := rfl
    rw [hdA]
    dsimp only [mass, diva, T, H, P, D, qt]
    ring
  have hint : (∫ x, cutoffFluxProduction G v q χ Φ dt x
      (WithLp.toLp 2 (fun i => du i x)) (WithLp.toLp 2 (fun i => F i x)) (U x)) =
      (∫ x, mass x) + (∫ x, diva x) - 2 * (∫ x, T x) -
      2 * (∫ x, H x) - 2 * (∫ x, P x) + ∫ x, D x := by
    rw [integral_congr_ae hpoint]
    rw [integral_add
      (f := fun x => mass x + diva x - 2 * T x - 2 * H x - 2 * P x) (g := D)
      (((hmass.add hdiva).sub (hT.const_mul 2)).sub (hH.const_mul 2) |>.sub (hP.const_mul 2)) hD,
      integral_sub (f := fun x => mass x + diva x - 2 * T x - 2 * H x)
      (g := fun x => 2 * P x)
      (((hmass.add hdiva).sub (hT.const_mul 2)).sub (hH.const_mul 2)) (hP.const_mul 2),
      integral_sub (f := fun x => mass x + diva x - 2 * T x) (g := fun x => 2 * H x)
      ((hmass.add hdiva).sub (hT.const_mul 2)) (hH.const_mul 2),
      integral_sub (f := fun x => mass x + diva x) (g := fun x => 2 * T x)
      (hmass.add hdiva) (hT.const_mul 2),
      integral_add (f := mass) (g := diva) hmass hdiva,
      integral_const_mul, integral_const_mul, integral_const_mul]
  refine ⟨?_, ?_⟩
  · have hF : inner ℝ F (planeH1GradientOperator (E := E) z) = ∫ x, H x :=
      planeFlux_inner_eq_integral _ _
    have hPe : (∫ x, qt x * ∑ k : Fin 2, ∑ j : Fin 2,
        G x k j * inner ℝ (du j x) (du k x)) = ∫ x, P x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        dsimp only [P]
        congr 1
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro j _
        rw [real_inner_comm (du j x) (du k x)])
    rw [hF, hPe] at hprod
    change 2 * _ + 2 * (∫ x, P x) + 2 * (∫ x, H x) = _ at hprod
    change (∫ x, _) = (∫ x, diva x) - 2 * (∫ x, T x) at hdiv
    change 2 * _ + (∫ x, mass x) + (∫ x, D x) = _
    rw [hint]
    linarith only [hprod, hdiv]
  
  · exact (((((hmass.add hdiva).sub (hT.const_mul 2)).sub (hH.const_mul 2)).sub
      (hP.const_mul 2)).add hD).congr hpoint.symm

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization
open scoped ENNReal
namespace AVRegularity.Weighted

/-! Transfer the actual chart energies to and from the polynomial moment. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def planeMomentPolynomial (n : ℕ) (ϖ : ℝ) (zc : Vec 2) : Vec 2 → ℝ :=
  fun x => (1 + ϖ ^ 2 * ((x 0 - zc 0) ^ 2 + (x 1 - zc 1) ^ 2)) ^ n

omit [InnerProductSpace ℝ E] in
theorem chartScalarEnergy_le_scaled (q w : Vec 2 → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x, q x ≤ C * w x) (U : Lp E 2 (volume : Measure (Vec 2))) :
    chartScalarEnergy q U ≤ ENNReal.ofReal C * chartScalarEnergy w U := by
  unfold chartScalarEnergy
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro x
  dsimp only
  rw [← ENNReal.ofReal_mul hC]
  apply ENNReal.ofReal_le_ofReal
  nlinarith only [mul_le_mul_of_nonneg_right (h x) (sq_nonneg ‖U x‖)]

omit [InnerProductSpace ℝ E] in
theorem chartFiniteEnergy_le_scaled (q w : Vec 2 → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x, q x ≤ C * w x)
    (U : PiLp 2 (fun _ : Fin 2 => Lp E 2 (volume : Measure (Vec 2)))) :
    chartFiniteEnergy q U ≤ ENNReal.ofReal C * chartFiniteEnergy w U := by
  unfold chartFiniteEnergy
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro x
  dsimp only
  rw [← ENNReal.ofReal_mul hC]
  apply ENNReal.ofReal_le_ofReal
  nlinarith only [mul_le_mul_of_nonneg_right (h x)
    (sq_nonneg ‖(WithLp.toLp 2 (fun i => U i x) : PiLp 2 (fun _ : Fin 2 => E))‖)]

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory Filter
namespace AVRegularity.Weighted

/-! Finite literal weighted quadratic energy constructs the genuine weighted L2 class. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem weighted_plane_memLp_of_chartEnergy_ne_top
    (q : Vec 2 → ℝ) (hq : Continuous q)
    (U : Lp E 2 (volume : Measure (Vec 2)))
    (he : chartScalarEnergy (fun x => q x ^ 2) U ≠ ⊤) :
    MemLp (fun x => q x • U x) 2 volume := by
  have hm : AEStronglyMeasurable (fun x => q x • U x) volume :=
    hq.aestronglyMeasurable.smul (Lp.aestronglyMeasurable U)
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  refine ⟨hm.norm.pow 2, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun x => sq_nonneg ‖q x • U x‖))).mpr
  have hx x : ‖q x • U x‖ ^ 2 = q x ^ 2 * ‖U x‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  simp_rw [hx]
  exact lt_top_iff_ne_top.mpr he

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory
namespace AVRegularity.Weighted

/-! Any actual weighted L2 representative gives the literal polynomial energy and its time budget. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem chartScalarEnergy_eq_weighted_representative_norm (q : Vec 2 → ℝ)
    (U R : Lp E 2 (volume : Measure (Vec 2)))
    (hR : R =ᵐ[volume] fun x => q x • U x) :
    chartScalarEnergy (fun x => q x ^ 2) U = ENNReal.ofReal (‖R‖ ^ 2) := by
  have hn : ‖R‖ ^ 2 = ∫ x, ‖R x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards with x
    exact real_inner_self_eq_norm_sq (R x)
  rw [hn]
  calc
    _ = ∫⁻ x, ENNReal.ofReal (‖R x‖ ^ 2) := by
      apply lintegral_congr_ae
      filter_upwards [hR] with x hx
      rw [hx, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    _ = _ := (ofReal_integral_eq_lintegral_ofReal (Lp.memLp R).norm.integrable_sq
      (Filter.Eventually.of_forall (fun x => sq_nonneg ‖R x‖))).symm

theorem weighted_representative_time_energy_ne_top (q : Vec 2 → ℝ) (μ : Measure ℝ)
    (U R : ℝ → Lp E 2 (volume : Measure (Vec 2))) (hR : MemLp R 2 μ)
    (he : ∀ᵐ t ∂μ, R t =ᵐ[volume] fun x => q x • U t x) :
    (∫⁻ t, chartScalarEnergy (fun x => q x ^ 2) (U t) ∂μ) ≠ ⊤ := by
  have hi := hR.norm.integrable_sq
  have hh : (∫⁻ t, ENNReal.ofReal (‖R t‖ ^ 2) ∂μ) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun t => sq_nonneg ‖R t‖))).mp
      hi.hasFiniteIntegral
  have hs := lintegral_congr_ae (he.mono (fun t ht =>
    chartScalarEnergy_eq_weighted_representative_norm q (U t) (R t) ht))
  exact hs.trans_lt hh |>.ne

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.Weighted

/-! A compact smooth scalar weight is a justified test for any plane weak energy curve. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeWeak_compact_weighted_energy_strongTime
    {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → Lp E 2 (volume : Measure (Vec 2))}
    {slice dual : ℝ → PlaneHk Set.univ 1 E}
    (h : PlaneWeakHilbertCurve a b u slice dual)
    (f : ℝ × Vec 2 → ℝ) (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport f) :
    ∃ B : ℝ → PlaneHk Set.univ 1 E →L[ℝ] PlaneHk Set.univ 1 E,
      (∀ t z, planeHkValueOperator (E := E) 1 (B t z) =ᵐ[volume]
        fun x => f (t, x) ^ 2 • planeHkValueOperator (E := E) 1 z x) ∧
      AVRegularity.CycleEvolution.StrongTimeRegularity a b
        (fun t => ∫ x, f (t, x) ^ 2 * ‖u t x‖ ^ 2)
        (fun t => 2 * inner ℝ (dual t) (B t (slice t)) +
          2 * (∫ x, f (t, x) * fderiv ℝ f (t, x) (1, 0) * ‖u t x‖ ^ 2)) := by
  obtain ⟨c, dc, M, Md, hc, hdc, hM, hMd, hbA, hbdA, hA, hdA⟩ :=
    compactScalarMultiplier_time (E := E) f hf hs a b
  let C : ℝ × Vec 2 → E →L[ℝ] E := fun p => scalarFiberCoefficient (E := E) (f p ^ 2)
  have hC : ContDiff ℝ 1 C := (hf.of_le (by norm_num)).pow 2 |>.smul contDiff_const
  have hsSq : HasCompactSupport (fun p => f p ^ 2) := by
    convert hs.mul_right (f' := f) using 1
    funext p
    exact pow_two (f p)
  have hsC : HasCompactSupport C := hsSq.smul_right
    (f' := fun _ => ContinuousLinearMap.id ℝ E)
  obtain ⟨Mb, hMb, hCb⟩ := compactH1Coefficient_bounds C hC hsC
  have hCt t : ContDiff ℝ 1 (fun x => C (t, x)) :=
    hC.comp (contDiff_const.prodMk contDiff_id)
  let Jb : Fin 2 → ℝ := fun _ => 2 * Mb
  let B : ℝ → PlaneHk Set.univ 1 E →L[ℝ] PlaneHk Set.univ 1 E := fun t =>
    planeH1CoefficientOperator (fun x => C (t, x)) (hCt t) Jb (hCb t)
  have hbB t : ‖B t‖ ≤ 4 * Mb := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro z
    simpa only [B, planeH1CoefficientOperator_apply, Jb, show (2 * Mb + 2 * Mb) = 4 * Mb by ring]
      using planeH1_mulCoefficient_norm_le (fun x => C (t,x)) (hCt t) Jb (hCb t) z
  have hAB t z : (boundedScalarMultiplier (E := E) (c t)).adjoint
      (boundedScalarMultiplier (c t) (planeHkValueOperator (E := E) 1 z)) =
      planeHkValueOperator (E := E) 1 (B t z) := by
    have hcs : (fun x => scalarFiberCoefficient (E := E) (c t x ^ 2)) = fun x => C (t,x) := by
      funext x
      rw [hc]
    have he := planeScalarMultiplier_square_H1 (E := E) (c t) (c t).continuous
      (norm_nonneg (c t)) (fun x => by simpa only [Real.norm_eq_abs] using (c t).norm_coe_le_norm x)
      (hcs.symm ▸ hCt t) Jb (hcs.symm ▸ hCb t) z
    simpa only [boundedScalarMultiplier, hcs, B] using he
  have he := planeWeak_multiplier_energy_strongTime hab h
    (fun t => boundedScalarMultiplier (E := E) (c t))
    (fun t => boundedScalarMultiplier (E := E) (dc t)) B hA
    (Filter.Eventually.of_forall hdA) hAB M Md (4 * Mb) hM hMd (by positivity) hbA hbdA hbB
  refine ⟨B, ?_, ?_⟩
  · intro t z
    exact planeH1ScalarMultiplier_value_ae (fun x => f (t,x) ^ 2) (hCt t) Jb (hCb t) z
  · simpa only [boundedScalarMultiplier_normSq, boundedScalarMultiplier_inner_same, hc, hdc] using he

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.Weighted

/-! The true Sobolev transport carrier has exactly the original drift derivative masks. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeTransportCarrier_jet_masks_ae {K Kmax : ℕ} (hK : K ≤ Kmax)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (V : ℝ) (hbv : ∀ x, ‖v x‖ ≤ V) (a B lam : ℝ)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤
        a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (p : PlaneHk Set.univ (K + 1) E) (j : Fin (K + 1)) (w : DerivativeWord2 j.val) :
    (planeTransportCarrier hK v hv V hbv a B lam hjets p).val ⟨j, w⟩
      =ᵐ[volume.restrict Set.univ] fun x => ∑ m : PositionMask j.val,
        driftMaskTerm (Nat.le_of_lt_succ j.isLt) v p.toFunction.jet m w x := by
  have hp : (planeTransportCarrier hK v hv V hbv a B lam hjets p).val ⟨j, w⟩
      =ᵐ[volume.restrict Set.univ] multiplicationRawJet (driftFiberCoefficient v)
        (planeGradientTensor p).toFunction.jet ⟨j, w⟩ := by
    unfold planeTransportCarrier
    exact planeCoefficientCarrier_jet_ae _ _ _ _ _
  have hg : ∀ᵐ x ∂volume.restrict Set.univ, ∀ m : PositionMask j.val,
      (planeGradientTensor p).val (maskJetIndex (Nat.le_of_lt_succ j.isLt) m w) x =
        WithLp.toLp 2 (fun k : Fin 2 => p.val
          ⟨⟨maskRightLength j.val m + 1, by have := maskRightLength_le j.val m; omega⟩,
            Fin.snoc (maskWordEquiv 2 j.val m w).2 k⟩ x) := by
    apply ae_all_iff.mpr
    intro m
    exact planeGradientTensor_jet_ae p _ _
  filter_upwards [hp, hg] with x hx hgrad
  rw [hx]
  unfold multiplicationRawJet
  apply Finset.sum_congr rfl
  intro m _
  unfold multiplicationTerm
  change coefficientDerivativeArray (driftFiberCoefficient v) (maskLeftLength j.val m) x
    ((planeGradientTensor p).val (maskJetIndex _ m w) x) (maskWordEquiv 2 j.val m w).1 = _
  rw [driftFiberCoefficient_array_eq v hv, scalarTensorOperator_apply, hgrad m]
  rfl

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory Filter AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! A canonical L2 readout for finite weighted plane energy, defined everywhere in time. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def weightedPlaneLpReadout (q : Vec 2 → ℝ) (hq : Continuous q)
    (U : Lp E 2 (volume : Measure (Vec 2))) : Lp E 2 (volume : Measure (Vec 2)) :=
  if he : chartScalarEnergy (fun x => q x ^ 2) U ≠ ⊤ then
    (weighted_plane_memLp_of_chartEnergy_ne_top q hq U he).toLp (fun x => q x • U x)
  else 0

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem weightedPlaneLpReadout_ae (q : Vec 2 → ℝ) (hq : Continuous q)
    (U : Lp E 2 (volume : Measure (Vec 2)))
    (he : chartScalarEnergy (fun x => q x ^ 2) U ≠ ⊤) :
    weightedPlaneLpReadout q hq U =ᵐ[volume] fun x => q x • U x := by
  rw [weightedPlaneLpReadout, dite_eq_left he]
  exact MemLp.coeFn_toLp _

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem weightedPlaneLpReadout_energy (q : Vec 2 → ℝ) (hq : Continuous q)
    (U : Lp E 2 (volume : Measure (Vec 2)))
    (he : chartScalarEnergy (fun x => q x ^ 2) U ≠ ⊤) :
    ENNReal.ofReal (‖weightedPlaneLpReadout q hq U‖ ^ 2) =
      chartScalarEnergy (fun x => q x ^ 2) U := by
  have hw := weighted_plane_memLp_of_chartEnergy_ne_top q hq U he
  have hi : Integrable (fun x => q x ^ 2 * ‖U x‖ ^ 2) volume := by
    have hx x : ‖q x • U x‖ ^ 2 = q x ^ 2 * ‖U x‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    simpa only [hx] using hw.norm.integrable_sq
  have hn : ‖weightedPlaneLpReadout q hq U‖ ^ 2 = ∫ x, q x ^ 2 * ‖U x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [weightedPlaneLpReadout_ae q hq U he] with x hx
    rw [hx, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [hn]
  exact ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)))

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! A bounded positive testing weight scales stored jets without differentiating them. -/

theorem boundedWeightRoot_properties (q : Vec 2 → ℝ) (hq : Continuous q)
    (hq0 : ∀ x, 0 ≤ q x) (M : ℝ) (hbound : ∀ x, q x ≤ M) :
    Continuous (fun x => Real.sqrt (q x)) ∧
      (∀ x, |Real.sqrt (q x)| ≤ Real.sqrt M) ∧
      (∀ x, Real.sqrt (q x) ^ 2 = q x) := by
  refine ⟨hq.sqrt, ?_, fun x => Real.sq_sqrt (hq0 x)⟩
  intro x
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_sqrt (hbound x)

end AVRegularity.Weighted
end
