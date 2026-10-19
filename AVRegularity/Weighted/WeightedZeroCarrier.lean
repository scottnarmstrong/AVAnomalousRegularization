-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Weighted.ClippedValueTimeGrowth
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
namespace AVRegularity.Weighted

/-! Uniqueness for any given scalar plane energy solutions, independently of existence. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Any two scalar chain energy solutions with the prescribed measurable-time metric agree. -/
theorem scalarChain_energy_solution_unique
    (a b : ℝ) (hab : a ≤ b) (κ : Fin 1 → ι → ℕ)
    (v : ℝ → Vec 2 → Vec 2) (hv : ∀ t ∈ Icc a b, ContDiff ℝ 1 (v t))
    (hvm : Measurable (fun p : Icc a b × Vec 2 => v p.1 p.2))
    (hvb : ∃ M : ℝ, ∀ t ∈ Icc a b, ∀ z, ‖v t z‖ ≤ M)
    (hdiv : ∀ t ∈ Icc a b, ∀ z, ∑ k : Fin 2, fderiv ℝ (v t) z (basisVec k) k = 0)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hGc : ∀ t ∈ Icc a b, ∀ k j, Continuous (fun z => G t z k j))
    (hGm : Measurable (fun p : Icc a b × Vec 2 => G p.1 p.2))
    (g : ℝ) (hg4 : g ≤ 1 / 4) (hG : IsMetricNearIdentity G g)
    (hsym : ∀ t ∈ Icc a b, ∀ z, (G t z).IsSymm)
    (f : ∀ p : Fin 1 × ι, PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (F : ∀ p : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (PiLp 2 (fun _ : Fin 2 => h p.2)))
    (hF : ∀ p, MemLp (F p) 2 (volume.restrict (Icc a b)))
    (u u' : ∀ p : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (w w' : ∀ p : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hsln : IsCoupledWeakSolutionPlane 1 a b v 2 (fun p : Fin 1 × ι => κ p.1 p.2)
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ) f F (fun _ _ => 0) u w)
    (hsln' : IsCoupledWeakSolutionPlane 1 a b v 2 (fun p : Fin 1 × ι => κ p.1 p.2)
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ) f F (fun _ _ => 0) u' w') :
    ∀ i, ∀ t ∈ Icc a b, u i t = u' i t := by
  obtain ⟨M, hM⟩ := hvb
  let hvc : ∀ t ∈ Icc a b, Continuous (v t) := fun t ht => (hv t ht).continuous
  intro i
  have hc := scalarChain_planeWeakHilbertCurve a b hab κ v hvc hvm M hM G hGc hGm
    g hg4 hG hsym f F hF u w hsln i
  have hc' := scalarChain_planeWeakHilbertCurve a b hab κ v hvc hvm M hM G hGc hGm
    g hg4 hG hsym f F hF u' w' hsln' i
  have hu := planeWeakHilbert_unique_of_nonpositive_difference hab hc hc' (by
    simp only [coupledPlaneL2Trace, hsln.2.2.2.1 i, hsln'.2.2.2.1 i]) (by
    apply Filter.Eventually.of_forall
    intro r
    rw [planeWeakDualRepresentative_sub]
    apply mul_nonpos_of_nonneg_of_nonpos (by norm_num)
    exact planeScalarDual_zeroFlux_nonpositive
      (v (Set.projIcc a b hab r))
      (planeIntervalVelocity_continuous a b hab v hvc r) (le_max_right M 0)
      (planeIntervalVelocity_bound a b hab v M hM r)
      (hv _ (Set.projIcc a b hab r).property)
      ⟨M, hM _ (Set.projIcc a b hab r).property⟩
      (hdiv _ (Set.projIcc a b hab r).property)
      G g hg4 hG (Set.projIcc a b hab r)
      (planeIntervalMetric_continuous a b hab G hGc r) (by norm_num : (0 : ℝ) ≤ 5 / 4)
      (planeIntervalMetric_bound a b hab G g hg4 hG hsym r) _)
  intro t ht
  apply PlaneHk.ext_value isOpen_univ
  apply univToPlane.injective
  exact hu t ht

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! All raw jets and the literal word flux of zero carriers vanish almost everywhere. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeHk_zero_raw_jet (K : ℕ) (α : JetIndex2 K) :
    (0 : PlaneHk Set.univ K E).toFunction.jet α =ᵐ[volume] 0 := by
  have hh := planeJetReadout_ae_raw (0 : PlaneHk Set.univ K E) α
  rw [map_zero] at hh
  exact hh.symm.trans (Lp.coeFn_zero E 2 volume)

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {N D : ℕ}

theorem wordChainRawFlux_zero (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (letters : Fin N → CycleLetter ι h D) (κ : Fin (N + 1) → ι → ℕ)
    (X₀ : Vec 2) (δ : ℝ) (i : Fin (N + 1) × ι) (t : ℝ) :
    wordChainRawFlux G letters κ X₀ δ (fun _ => 0) i t =ᵐ[volume] 0 := by
  classical
  have hz (p : Fin (N + 1) × ι) : ∀ᵐ z ∂volume,
      ∀ α : JetIndex2 (κ p.1 p.2 + 1),
        (0 : PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2)).toFunction.jet α z = 0 :=
    ae_all_iff.mpr (fun α => planeHk_zero_raw_jet _ α)
  filter_upwards [ae_all_iff.mpr hz] with z hz
  unfold wordChainRawFlux
  apply Finset.sum_eq_zero
  intro p _
  apply Finset.sum_eq_zero
  intro d _
  have hi : wordCouplingInput κ i p d (0 : PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2)) z = 0 := by
    apply (WithLp.equiv 2 _).injective
    funext w
    exact hz p _
  rw [hi, map_zero]

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Weighted

/-! The actual finite commutator arrays retain every original nonprincipal source field. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

theorem driftCommutatorL2Array_ae {K j : ℕ} {U : Set (Vec 2)} (hj : j ≤ K)
    (v : Vec 2 → Vec 2) (D : RawJet2 (K + 1) E)
    (hT : ∀ (m : PositionMask j) (w : DerivativeWord2 j),
      MemLp (driftMaskTerm hj v D m w) 2 (volume.restrict U)) (w : DerivativeWord2 j) :
    AVRegularity.CoupledEnergyPlane.Variational.driftCommutatorL2Array hj v D hT w =ᵐ[volume.restrict U]
      planeDriftCommutatorTerm hj v D w := by
  simp only [AVRegularity.CoupledEnergyPlane.Variational.driftCommutatorL2Array, WithLp.ofLp_sum, Finset.sum_apply]
  change (∑ m : PositionMask j,
    (if 1 ≤ maskLeftLength j m then AVRegularity.CoupledEnergyPlane.Variational.driftMaskL2Array hj v D hT m else 0) w) =ᵐ[volume.restrict U] _
  have he (m : PositionMask j) :
      (if 1 ≤ maskLeftLength j m then AVRegularity.CoupledEnergyPlane.Variational.driftMaskL2Array hj v D hT m else 0) w =
      if 1 ≤ maskLeftLength j m then (hT m w).toLp (driftMaskTerm hj v D m w) else 0 := by
    split_ifs <;> rfl
  simp_rw [he]
  exact finiteLp_conditional_sum_ae (fun m => 1 ≤ maskLeftLength j m)
    (fun m => driftMaskTerm hj v D m w) (fun m => hT m w)

theorem metricCommutatorL2Array_ae {K j : ℕ} {U : Set (Vec 2)} (hj : j ≤ K)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (D : RawJet2 (K + 1) E)
    (hT : ∀ (m : PositionMask j) (w : DerivativeWord2 j),
      MemLp (metricMaskTerm hj G D m w) 2 (volume.restrict U)) (w : DerivativeWord2 j) :
    metricCommutatorL2Array hj G D hT w =ᵐ[volume.restrict U]
      metricCommutatorTerm hj G D w := by
  simp only [metricCommutatorL2Array, WithLp.ofLp_sum, Finset.sum_apply]
  change (∑ m : PositionMask j,
    (if 1 ≤ maskLeftLength j m then metricMaskL2Array hj G D hT m else 0) w) =ᵐ[volume.restrict U] _
  have he (m : PositionMask j) :
      (if 1 ≤ maskLeftLength j m then metricMaskL2Array hj G D hT m else 0) w =
      if 1 ≤ maskLeftLength j m then (hT m w).toLp (metricMaskTerm hj G D m w) else 0 := by
    split_ifs <;> rfl
  simp_rw [he]
  exact finiteLp_conditional_sum_ae (fun m => 1 ≤ maskLeftLength j m)
    (fun m => metricMaskTerm hj G D m w) (fun m => hT m w)

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped ENNReal
namespace AVRegularity.Weighted

/-! Factorial chart energies of actual stored Sobolev readouts. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def storedChartFactorialEnergy {K : ℕ} (ρ : ℝ) (q : Vec 2 → ℝ)
    (U : PlaneHk Set.univ K E) : ℝ≥0∞ :=
  ∑ α : JetIndex2 K, ENNReal.ofReal (factorialWeight ρ α.1.val) *
    chartScalarEnergy q (planeJetReadoutOperator K α U)

def storedChartGradientEnergy {K : ℕ} (ρ : ℝ) (q : Vec 2 → ℝ)
    (W : PlaneHk Set.univ (K + 1) E) : ℝ≥0∞ :=
  ∑ α : JetIndex2 K, ENNReal.ofReal (factorialWeight ρ α.1.val) *
    chartFiniteEnergy q (planeH1GradientOperator (planeWordH1SliceOperator K α W))

def storedChartFluxEnergy {K : ℕ} (ρ : ℝ) (q : Vec 2 → ℝ)
    (F : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) : ℝ≥0∞ :=
  ∑ α : JetIndex2 K, ENNReal.ofReal (factorialWeight ρ α.1.val) *
    chartFiniteEnergy q (planeJetFluxOperator K α F)

omit [FiniteDimensional ℝ E] in
theorem storedChartFactorialEnergy_eq_ofReal {K : ℕ} (ρ : ℝ) (q : Vec 2 → ℝ)
    (hq : Continuous q) {B : ℝ} (hb : ∀ x, |q x| ≤ B) (hq0 : ∀ x, 0 ≤ q x)
    (U : PlaneHk Set.univ K E) :
    storedChartFactorialEnergy ρ q U =
      ENNReal.ofReal (rawWeightedFactorialEnergy ρ q U.toFunction.jet) := by
  rw [← planeStoredWord_factorial_energy]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro α _
    rw [ENNReal.ofReal_mul (factorialWeight_nonneg _ _),
      ← chartScalarEnergy_eq_ofReal q hq hb hq0]
  · intro α _
    exact mul_nonneg (factorialWeight_nonneg _ _)
      (integral_nonneg (fun x => mul_nonneg (hq0 x) (sq_nonneg _)))

omit [FiniteDimensional ℝ E] in
theorem storedChartGradientEnergy_eq_ofReal {K : ℕ} (ρ : ℝ) (q : Vec 2 → ℝ)
    (hq : Continuous q) {B : ℝ} (hb : ∀ x, |q x| ≤ B) (hq0 : ∀ x, 0 ≤ q x)
    (W : PlaneHk Set.univ (K + 1) E) :
    storedChartGradientEnergy ρ q W =
      ENNReal.ofReal (rawWeightedGradientEnergy ρ q W.toFunction.jet) := by
  rw [← planeStoredWord_gradient_energy]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro α _
    rw [ENNReal.ofReal_mul (factorialWeight_nonneg _ _),
      ← chartFiniteEnergy_eq_ofReal q hq hb hq0]
  · intro α _
    exact mul_nonneg (factorialWeight_nonneg _ _)
      (integral_nonneg (fun x => mul_nonneg (hq0 x) (sq_nonneg _)))

theorem storedChartFluxEnergy_eq_ofReal {K : ℕ} (ρ : ℝ) (q : Vec 2 → ℝ)
    (hq : Continuous q) {B : ℝ} (hb : ∀ x, |q x| ≤ B) (hq0 : ∀ x, 0 ≤ q x)
    (F : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) :
    storedChartFluxEnergy ρ q F =
      ENNReal.ofReal (rawWeightedFactorialEnergy ρ q F.toFunction.jet) := by
  rw [← planeStoredWord_flux_energy]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro α _
    rw [ENNReal.ofReal_mul (factorialWeight_nonneg _ _),
      ← chartFiniteEnergy_eq_ofReal q hq hb hq0]
  · intro α _
    exact mul_nonneg (factorialWeight_nonneg _ _)
      (integral_nonneg (fun x => mul_nonneg (hq0 x) (sq_nonneg _)))

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Weighted

/-! Every positively weighted stored derivative inherits finiteness of the summed energy. -/

theorem finite_weighted_sum_component {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) (A : ι → ℝ≥0∞)
    (he : (∑ i, ENNReal.ofReal (c i) * A i) ≠ ⊤) (i : ι) : A i ≠ ⊤ := by
  have hi : ENNReal.ofReal (c i) * A i < ⊤ :=
    lt_of_le_of_lt (Finset.single_le_sum (f := fun j => ENNReal.ofReal (c j) * A j)
      (fun _ _ => bot_le) (Finset.mem_univ i)) (lt_top_iff_ne_top.mpr he)
  intro hh
  rw [hh, ENNReal.mul_top ((ENNReal.ofReal_pos.mpr (hc i)).ne')] at hi
  exact (lt_irrefl ⊤) hi

theorem finite_integrated_weighted_sum_component {T ι : Type*}
    [MeasurableSpace T] [Fintype ι] (μ : Measure T)
    (c : ι → ℝ) (hc : ∀ i, 0 < c i) (A : ι → T → ℝ≥0∞)
    (he : (∫⁻ t, ∑ i, ENNReal.ofReal (c i) * A i t ∂μ) ≠ ⊤) (i : ι) :
    (∫⁻ t, A i t ∂μ) ≠ ⊤ := by
  have hi : ENNReal.ofReal (c i) * (∫⁻ t, A i t ∂μ) < ⊤ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lt_of_le_of_lt (lintegral_mono (fun t =>
      Finset.single_le_sum (f := fun j => ENNReal.ofReal (c j) * A j t)
        (fun _ _ => bot_le) (Finset.mem_univ i))) (lt_top_iff_ne_top.mpr he)
  intro hh
  rw [hh, ENNReal.mul_top ((ENNReal.ofReal_pos.mpr (hc i)).ne')] at hi
  exact (lt_irrefl ⊤) hi

theorem factorialWeight_pos_of_radius_pos (ρ : ℝ) (hρ : 0 < ρ) (j : ℕ) :
    0 < factorialWeight ρ j := by
  unfold factorialWeight
  positivity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem storedChartFactorialEnergy_component_ne_top {K : ℕ}
    (ρ : ℝ) (hρ : 0 < ρ) (q : Vec 2 → ℝ) (U : PlaneHk Set.univ K E)
    (he : storedChartFactorialEnergy ρ q U ≠ ⊤) (α : JetIndex2 K) :
    chartScalarEnergy q (planeJetReadoutOperator K α U) ≠ ⊤ :=
  finite_weighted_sum_component (fun α : JetIndex2 K => factorialWeight ρ α.1.val)
    (fun α => factorialWeight_pos_of_radius_pos ρ hρ α.1.val) _ he α

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped ENNReal Topology
namespace AVRegularity.Weighted

/-! Integer clipping converges for the finite factorial sums of stored readouts. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem chartFiniteEnergy_clipping_tendsto (q : Vec 2 → ℝ) (hq : ∀ x, 0 < q x)
    (hqm : ∀ n : ℕ, Measurable (fun x => clipWeight ((n : ℝ) + 1) (q x)))
    (U : PiLp 2 (fun _ : Fin 2 => Lp E 2 (volume : Measure (Vec 2)))) :
    Tendsto (fun n : ℕ => chartFiniteEnergy (fun x => clipWeight ((n : ℝ) + 1) (q x)) U)
      atTop (𝓝 (chartFiniteEnergy q U)) := by
  exact lintegral_clipWeight_tendsto q _ hq
    (finiteLp_normSq_integrable U).aemeasurable (fun _ => sq_nonneg _) hqm

omit [FiniteDimensional ℝ E] in
theorem storedChartFactorialEnergy_clipping_tendsto {K : ℕ} (ρ : ℝ)
    (q : Vec 2 → ℝ) (hq : ∀ x, 0 < q x)
    (hqm : ∀ n : ℕ, Measurable (fun x => clipWeight ((n : ℝ) + 1) (q x)))
    (U : PlaneHk Set.univ K E) :
    Tendsto (fun n : ℕ => storedChartFactorialEnergy ρ
      (fun x => clipWeight ((n : ℝ) + 1) (q x)) U)
      atTop (𝓝 (storedChartFactorialEnergy ρ q U)) := by
  apply tendsto_finsetSum
  intro α _
  exact ENNReal.Tendsto.const_mul (chartScalarEnergy_clipping_tendsto q hq hqm
    (planeJetReadoutOperator K α U)) (Or.inr ENNReal.ofReal_ne_top)

omit [FiniteDimensional ℝ E] in
theorem storedChartGradientEnergy_clipping_tendsto {K : ℕ} (ρ : ℝ)
    (q : Vec 2 → ℝ) (hq : ∀ x, 0 < q x)
    (hqm : ∀ n : ℕ, Measurable (fun x => clipWeight ((n : ℝ) + 1) (q x)))
    (W : PlaneHk Set.univ (K + 1) E) :
    Tendsto (fun n : ℕ => storedChartGradientEnergy ρ
      (fun x => clipWeight ((n : ℝ) + 1) (q x)) W)
      atTop (𝓝 (storedChartGradientEnergy ρ q W)) := by
  apply tendsto_finsetSum
  intro α _
  exact ENNReal.Tendsto.const_mul (chartFiniteEnergy_clipping_tendsto q hq hqm
    (planeH1GradientOperator (planeWordH1SliceOperator K α W)))
      (Or.inr ENNReal.ofReal_ne_top)

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Weighted

/-! Monotonicity in the weight for actual stored factorial energies. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] in
theorem storedChartFactorialEnergy_mono {K : ℕ} (ρ : ℝ) (q p : Vec 2 → ℝ)
    (h : ∀ x, q x ≤ p x) (U : PlaneHk Set.univ K E) :
    storedChartFactorialEnergy ρ q U ≤ storedChartFactorialEnergy ρ p U := by
  apply Finset.sum_le_sum
  intro α _
  exact mul_le_mul' le_rfl (chartScalarEnergy_mono q p h _)

omit [FiniteDimensional ℝ E] in
theorem storedChartGradientEnergy_mono {K : ℕ} (ρ : ℝ) (q p : Vec 2 → ℝ)
    (h : ∀ x, q x ≤ p x) (W : PlaneHk Set.univ (K + 1) E) :
    storedChartGradientEnergy ρ q W ≤ storedChartGradientEnergy ρ p W := by
  apply Finset.sum_le_sum
  intro α _
  exact mul_le_mul' le_rfl (chartFiniteEnergy_mono q p h _)

theorem storedChartFluxEnergy_mono {K : ℕ} (ρ : ℝ) (q p : Vec 2 → ℝ)
    (h : ∀ x, q x ≤ p x) (F : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) :
    storedChartFluxEnergy ρ q F ≤ storedChartFluxEnergy ρ p F := by
  apply Finset.sum_le_sum
  intro α _
  exact mul_le_mul' le_rfl (chartFiniteEnergy_mono q p h _)

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.Weighted

/-! The stored transport is the word's transport plus its genuine value commutator. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeWordDriftCommutator_order_zero {K Kmax : ℕ} (hK : K ≤ Kmax)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (V : ℝ) (hbv : ∀ x, ‖v x‖ ≤ V) (a B lam : ℝ)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤
        a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (hvc : ∀ k, Continuous (fun x => v x k))
    (C : ℝ) (hC : 0 ≤ C) (hvb : ∀ k x, |v x k| ≤ C)
    (W : PlaneHk Set.univ (K + 1) E) :
    planeWordDriftCommutator hK v hv V hbv a B lam hjets hvc C hC hvb W (valueIndex2 K) = 0 := by
  apply Lp.ext
  have hm := planeWordDriftCommutator_ae hK v hv V hbv a B lam hjets hvc C hC hvb W (valueIndex2 K)
  filter_upwards [hm, Lp.coeFn_zero E 2 (volume : Measure (Vec 2))] with x hx hz
  have hzero := planeDriftCommutatorTerm_order_zero v W.toFunction.jet (valueIndex2 K).2 x
  exact (hx.trans hzero).trans hz.symm

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Weighted

/-! Uniform comparison of weights transfers the complete factorial chart energies. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] in
theorem storedChartFactorialEnergy_le_scaled {K : ℕ} (ρ : ℝ) (q p : Vec 2 → ℝ)
    {A : ℝ} (hA : 0 ≤ A) (h : ∀ x, q x ≤ A * p x) (U : PlaneHk Set.univ K E) :
    storedChartFactorialEnergy ρ q U ≤ ENNReal.ofReal A * storedChartFactorialEnergy ρ p U := by
  unfold storedChartFactorialEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro α _
  have hh := mul_le_mul' (le_rfl : ENNReal.ofReal (factorialWeight ρ α.1.val) ≤ _) (chartScalarEnergy_le_scaled q p hA h (planeJetReadoutOperator K α U))
  exact hh.trans_eq (by ac_rfl)

omit [FiniteDimensional ℝ E] in
theorem storedChartGradientEnergy_le_scaled {K : ℕ} (ρ : ℝ) (q p : Vec 2 → ℝ)
    {A : ℝ} (hA : 0 ≤ A) (h : ∀ x, q x ≤ A * p x) (W : PlaneHk Set.univ (K + 1) E) :
    storedChartGradientEnergy ρ q W ≤ ENNReal.ofReal A * storedChartGradientEnergy ρ p W := by
  unfold storedChartGradientEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro α _
  have hh := mul_le_mul' (le_rfl : ENNReal.ofReal (factorialWeight ρ α.1.val) ≤ _) (chartFiniteEnergy_le_scaled q p hA h
    (planeH1GradientOperator (planeWordH1SliceOperator K α W)))
  exact hh.trans_eq (by ac_rfl)

theorem storedChartFluxEnergy_le_scaled {K : ℕ} (ρ : ℝ) (q p : Vec 2 → ℝ)
    {A : ℝ} (hA : 0 ≤ A) (h : ∀ x, q x ≤ A * p x)
    (F : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) :
    storedChartFluxEnergy ρ q F ≤ ENNReal.ofReal A * storedChartFluxEnergy ρ p F := by
  unfold storedChartFluxEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro α _
  have hh := mul_le_mul' (le_rfl : ENNReal.ofReal (factorialWeight ρ α.1.val) ≤ _) (chartFiniteEnergy_le_scaled q p hA h (planeJetFluxOperator K α F))
  exact hh.trans_eq (by ac_rfl)
end

/-! Weight comparison also transfers the full interval production and source energies. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] in
theorem storedChartGradientEnergy_time_le_scaled {K : ℕ} (ρ : ℝ)
    (q p : ℝ → Vec 2 → ℝ) (μ : Measure ℝ) {A : ℝ} (hA : 0 ≤ A)
    (h : ∀ᵐ t ∂μ, ∀ x, q t x ≤ A * p t x) (W : ℝ → PlaneHk Set.univ (K + 1) E) :
    (∫⁻ t, storedChartGradientEnergy ρ (q t) (W t) ∂μ) ≤
      ENNReal.ofReal A * ∫⁻ t, storedChartGradientEnergy ρ (p t) (W t) ∂μ := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [h] with t ht
  exact storedChartGradientEnergy_le_scaled ρ _ _ hA ht (W t)

theorem storedChartFluxEnergy_time_le_scaled {K : ℕ} (ρ : ℝ)
    (q p : ℝ → Vec 2 → ℝ) (μ : Measure ℝ) {A : ℝ} (hA : 0 ≤ A)
    (h : ∀ᵐ t ∂μ, ∀ x, q t x ≤ A * p t x)
    (F : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) :
    (∫⁻ t, storedChartFluxEnergy ρ (q t) (F t) ∂μ) ≤
      ENNReal.ofReal A * ∫⁻ t, storedChartFluxEnergy ρ (p t) (F t) ∂μ := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [h] with t ht
  exact storedChartFluxEnergy_le_scaled ρ _ _ hA ht (F t)
end

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! The norm square of the actual scaled metric source array is its literal weighted source integral. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

theorem scaledMetricCommutator_normSq_eq_integral {K j : ℕ} {U : Set (Vec 2)} (hj : j ≤ K)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (s : Vec 2 → ℝ) (D : RawJet2 (K + 1) E)
    (hT : ∀ (m : PositionMask j) (w : DerivativeWord2 j),
      MemLp (metricMaskTerm hj G (scaledRawJet s D) m w) 2 (volume.restrict U)) :
    ‖metricCommutatorL2Array hj G (scaledRawJet s D) hT‖ ^ 2 =
      ∑ w : DerivativeWord2 j, ∫ x, s x ^ 2 * ‖metricCommutatorTerm hj G D w x‖ ^ 2
        ∂volume.restrict U := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro w _
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [metricCommutatorL2Array_ae hj G (scaledRawJet s D) hT w] with x hx
  rw [hx, metricCommutatorTerm_scaledRawJet, real_inner_self_eq_norm_sq,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped ENNReal Topology
namespace AVRegularity.Weighted

/-! Monotone clipping passage for the retained full interval factorial production. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem storedChartGradientEnergy_time_clipping_tendsto {K : ℕ} (ρ : ℝ)
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {t₀ S ϖ : ℝ} {zc : Vec 2} {N : ℕ} {Cw : ℕ → ℝ}
    (C : ChartWeights G v t₀ S ϖ zc N Cw) (m : ℕ) (hm : m ≤ N)
    (μ : Measure ℝ) (W : ℝ → PlaneHk Set.univ (K + 1) E) (hW : MemLp W 2 μ) :
    Tendsto (fun n : ℕ => ∫⁻ t, storedChartGradientEnergy ρ
      (fun x => clipWeight ((n : ℝ) + 1) (C.W m t x)) (W t) ∂μ)
      atTop (𝓝 (∫⁻ t, storedChartGradientEnergy ρ (C.W m t) (W t) ∂μ)) := by
  apply lintegral_tendsto_of_tendsto_of_monotone
  · intro n
    have hi := rawWeightedGradient_time_integrable C m hm ((n : ℝ) + 1)
      (by positivity) ρ μ W hW
    have he t : storedChartGradientEnergy ρ
        (fun x => clipWeight ((n : ℝ) + 1) (C.W m t x)) (W t) =
        ENNReal.ofReal (rawWeightedGradientEnergy ρ
          (fun x => clipWeight ((n : ℝ) + 1) (C.W m t x)) (W t).toFunction.jet) := by
      obtain ⟨hc, _, hb⟩ := chartWeights_clipped_time_coefficient C m hm ((n : ℝ) + 1) (by positivity)
      exact storedChartGradientEnergy_eq_ofReal ρ _ (hc t) (hb t)
        (fun x => (clipWeight_pos (by positivity) (C.pos m hm t x)).le) _
    simp_rw [he]
    exact ENNReal.measurable_ofReal.comp_aemeasurable hi.aemeasurable
  · exact Eventually.of_forall (fun t n k hnk => storedChartGradientEnergy_mono ρ _ _
      (fun x => clipWeight_nat_monotone (C.W m t x) (C.pos m hm t x) hnk) (W t))
  · exact Eventually.of_forall (fun t => storedChartGradientEnergy_clipping_tendsto ρ
      (C.W m t) (C.pos m hm t)
      (fun n => (chartWeights_clipped_continuous C m hm t ((n : ℝ) + 1) (by positivity)).measurable) (W t))

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Weighted

/-! The literal weighted value-source product is controlled by the actual scaled L2 arrays. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

theorem scaledDrift_value_product_le {K j : ℕ} {U : Set (Vec 2)} (hj : j ≤ K)
    (v : Vec 2 → Vec 2) (s : Vec 2 → ℝ) (D : RawJet2 (K + 1) E)
    (hD : JetMemL2On U (scaledRawJet s D))
    (hT : ∀ (m : PositionMask j) (w : DerivativeWord2 j),
      MemLp (driftMaskTerm hj v (scaledRawJet s D) m w) 2 (volume.restrict U)) :
    (∑ w : DerivativeWord2 j, ∫ x,
      s x ^ 2 * (‖planeDriftCommutatorTerm hj v D w x‖ *
        ‖D ⟨⟨j, by omega⟩, w⟩ x‖) ∂volume.restrict U) ≤
      ‖AVRegularity.CoupledEnergyPlane.Variational.driftCommutatorL2Array
        hj v (scaledRawJet s D) hT‖ *
        ‖orderL2Array (jetToL2 (scaledRawJet s D) hD) ⟨j, by omega⟩‖ := by
  let Q := AVRegularity.CoupledEnergyPlane.Variational.driftCommutatorL2Array
    hj v (scaledRawJet s D) hT
  let P := orderL2Array (jetToL2 (scaledRawJet s D) hD) ⟨j, by omega⟩
  have he (w : DerivativeWord2 j) : (∫ x, ‖Q w x‖ * ‖P w x‖ ∂volume.restrict U) =
      ∫ x, s x ^ 2 * (‖planeDriftCommutatorTerm hj v D w x‖ *
        ‖D ⟨⟨j, by omega⟩, w⟩ x‖) ∂volume.restrict U := by
    apply integral_congr_ae
    have hq := driftCommutatorL2Array_ae hj v (scaledRawJet s D) hT w
    have hp := jetToL2_ae (scaledRawJet s D) hD (⟨⟨j, by omega⟩, w⟩ : JetIndex2 (K + 1))
    filter_upwards [hq, hp] with x hx hy
    change ‖Q w x‖ * ‖(jetToL2 (scaledRawJet s D) hD) ⟨⟨j, by omega⟩, w⟩ x‖ = _
    dsimp only [planeJetRepresentative] at hy
    rw [hx, hy, planeDriftCommutatorTerm_scaledRawJet]
    simp only [scaledRawJet, norm_smul, Real.norm_eq_abs]
    rw [← sq_abs (s x)]
    ring
  rw [show (∑ w : DerivativeWord2 j, ∫ x, s x ^ 2 *
      (‖planeDriftCommutatorTerm hj v D w x‖ * ‖D ⟨⟨j, by omega⟩, w⟩ x‖) ∂volume.restrict U) =
      ∑ w : DerivativeWord2 j, ∫ x, ‖Q w x‖ * ‖P w x‖ ∂volume.restrict U from
        Finset.sum_congr rfl (fun w _ => (he w).symm)]
  exact finiteL2_norm_product_integral_le Q P

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergyPlane.Variational
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.Weighted

/-! The stored transport is the word's transport plus its genuine value commutator. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeDriftCarrier_principal_value {K Kmax : ℕ} (hK : K ≤ Kmax)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (V : ℝ) (hbv : ∀ x, ‖v x‖ ≤ V) (a B lam : ℝ)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤
        a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (hvc : ∀ k, Continuous (fun x => v x k))
    (C : ℝ) (hC : 0 ≤ C) (hvb : ∀ k x, |v x k| ≤ C)
    (W : PlaneHk Set.univ (K + 1) E) :
    planeHkValueOperator K (planeTransportCarrier hK v hv V hbv a B lam hjets W) =
      planeScalarTransport v hvc hC hvb
        (planeH1GradientOperator (truncatePlaneHk (by omega) W)) := by
  have hz := planeWordDriftCommutator_order_zero hK v hv V hbv a B lam hjets hvc C hC hvb W
  unfold planeWordDriftCommutator at hz
  rw [planeWordH1Slice_order_zero] at hz
  exact sub_eq_zero.mp hz

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.Weighted

/-! The exact factorial drift absorption survives multiplication of the raw jets by a weight. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E]

theorem scaledDriftValueSource_absorption {K Kmax : ℕ} {U : Set (Vec 2)}
    (hK : K ≤ Kmax) (hU : MeasurableSet U)
    (ρ a B lam ν V : ℝ) (hρ : 0 < ρ) (ha : 0 ≤ a) (hB : 1 ≤ B)
    (hlam : 0 < lam) (hν : 0 < ν) (hV : 0 ≤ V)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : a * B * ρ ^ 2 ≤ ν / 8)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hvb : ∀ x, ‖v x‖ ≤ V)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤
        a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (s : Vec 2 → ℝ) (hs : Continuous s) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x, |s x| ≤ M) (D : RawJet2 (K + 1) E) (hD : JetMemL2On U D) :
    (∑ j : Fin (K + 1), factorialWeight ρ j.val *
      (∑ w : DerivativeWord2 j.val, ∫ x, s x ^ 2 *
        (‖planeDriftCommutatorTerm (Nat.le_of_lt_succ j.isLt) v D w x‖ *
          ‖D ⟨⟨j.val, by omega⟩, w⟩ x‖) ∂volume.restrict U)) ≤
      (ν / 4) * gradFactorialNormSq ρ
        (jetToL2 (scaledRawJet s D) (scaledRawJet_memL2 s hs hM hb D hD)) := by
  have h := scaledDriftMasks_norm_product_absorption hK hU ρ a B lam ν V
    hρ ha hB hlam hν hV hsmall hstrain v hv hvb hjets s hs hM hb D hD
  dsimp only at h
  refine le_trans ?_ h
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (factorialWeight_nonneg ρ _)
  exact scaledDrift_value_product_le (Nat.le_of_lt_succ j.isLt) v s D
    (scaledRawJet_memL2 s hs hM hb D hD)
    (scaledDriftMasks_memLp v hv V a B lam hV hvb
      (fun l hl hlK => hjets l hl (hlK.trans hK)) s hs hM hb D hD j)

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! The actual weighted metric commutator has a small factorial source energy at a reduced radius. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

theorem scaledMetricFluxSource_energy_le {K : ℕ} {U : Set (Vec 2)}
    (ρ δ g : ℝ) (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ) (hg : 0 ≤ g) (hscale : ρ * δ ≤ 1)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ k a, ContDiff ℝ (K : ℕ) (fun x => G x k a))
    (CG : ℕ → ℝ)
    (hbfull : ∀ (l : Fin (K + 1)) x k a,
      ‖iteratedFDeriv ℝ l.val (fun y => G y k a) x‖ ≤ metricEntryEnvelope CG g δ l.val)
    (hb : ∀ l, 1 ≤ l → l ≤ K → ∀ x k a,
      ‖iteratedFDeriv ℝ l (fun y => G y k a) x‖ ≤ CG l * g * δ ^ l)
    (s : Vec 2 → ℝ) (hs : Continuous s) {C : ℝ} (hC : 0 ≤ C)
    (hsb : ∀ x, |s x| ≤ C) (D : RawJet2 (K + 1) E) (hD : JetMemL2On U D) :
    (∑ j : Fin (K + 1), factorialWeight ρ j.val *
      (∑ w : DerivativeWord2 j.val, ∫ x, s x ^ 2 *
        ‖metricCommutatorTerm (Nat.le_of_lt_succ j.isLt) G D w x‖ ^ 2 ∂volume.restrict U)) ≤
      (metricRadiusConstant K CG * g * (ρ * δ)) ^ 2 * gradFactorialNormSq ρ
        (jetToL2 (scaledRawJet s D) (scaledRawJet_memL2 s hs hC hsb D hD)) := by
  have h := scaledMetricCommutator_factorial_energy_le ρ δ g hρ hδ hg hscale
    G hG CG hbfull hb s hs hC hsb D hD
  dsimp only at h
  refine le_trans ?_ h
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (factorialWeight_nonneg ρ _)
  exact le_of_eq (scaledMetricCommutator_normSq_eq_integral (Nat.le_of_lt_succ j.isLt)
    G s D (scaledMetricMasks_memLp G hG (fun l => metricEntryEnvelope CG g δ l.val)
      hbfull s hs hC hsb D hD j)).symm

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution
open scoped ENNReal
namespace AVRegularity.Weighted

/-! Read each factorial derivative order as a finite sum of actual L2 moments. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeJetOrder_moment_readout {K j : ℕ} (hj : j ≤ K)
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (U : PlaneHk Set.univ K E) :
    (∫⁻ x, ENNReal.ofReal (planeMomentPolynomial n ϖ zc x *
      ∑ w : DerivativeWord2 j, ‖planeJetOrder U j w x‖ ^ 2)) =
      ∑ w : DerivativeWord2 j, chartScalarEnergy (planeMomentPolynomial n ϖ zc)
        (univToPlane (U.val ⟨⟨j, Nat.lt_succ_of_le hj⟩, w⟩)) := by
  classical
  have hp x : 0 ≤ planeMomentPolynomial n ϖ zc x := by
    unfold planeMomentPolynomial
    positivity
  calc
    _ = ∫⁻ x, ∑ w : DerivativeWord2 j,
        ENNReal.ofReal (planeMomentPolynomial n ϖ zc x * ‖planeJetOrder U j w x‖ ^ 2) := by
      apply lintegral_congr
      intro x
      rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg]
      intro w _
      exact mul_nonneg (hp x) (sq_nonneg _)
    _ = ∫⁻ x, ∑ w : DerivativeWord2 j,
        ENNReal.ofReal (planeMomentPolynomial n ϖ zc x *
          ‖univToPlane (U.val ⟨⟨j, Nat.lt_succ_of_le hj⟩, w⟩) x‖ ^ 2) := by
      apply lintegral_congr_ae
      have ha := ae_all_iff.mpr (fun w : DerivativeWord2 j =>
        univToPlane_ae (U.val ⟨⟨j, Nat.lt_succ_of_le hj⟩, w⟩))
      filter_upwards [ha] with x hx
      apply Finset.sum_congr rfl
      intro w _
      simp only [planeJetOrder, dite_eq_left hj]
      rw [hx w]
      rfl
    _ = _ := by
      rw [lintegral_finsetSum']
      · rfl
      · intro w _
        exact (by unfold planeMomentPolynomial; fun_prop :
          Measurable (planeMomentPolynomial n ϖ zc)).aemeasurable.mul
          ((Lp.aestronglyMeasurable
            (univToPlane (U.val ⟨⟨j, Nat.lt_succ_of_le hj⟩, w⟩))).norm.pow 2).aemeasurable |>.ennreal_ofReal

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution
namespace AVRegularity.Weighted

/-! The stored metric flux is the word's principal diffusion plus its actual commutator. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeWordMetricCommutator_order_zero {K : ℕ}
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ k a, ContDiff ℝ (K : ℕ) (fun x => G x k a))
    (M : Fin (K + 1) → ℝ)
    (hb : ∀ (l : Fin (K + 1)) x k a,
      ‖iteratedFDeriv ℝ l.val (fun y => G y k a) x‖ ≤ M l)
    (hGc : ∀ k a, Continuous (fun x => G x k a))
    (C : ℝ) (hC : 0 ≤ C) (hGb : ∀ k a x, |G x k a| ≤ C)
    (W : PlaneHk Set.univ (K + 1) E) :
    planeWordMetricCommutator G hG M hb hGc C hC hGb W (valueIndex2 K) = 0 := by
  apply PiLp.ext
  intro k
  apply Lp.ext
  have hm := planeWordMetricCommutator_ae G hG M hb hGc C hC hGb W (valueIndex2 K) k
  filter_upwards [hm, Lp.coeFn_zero E 2 (volume : Measure (Vec 2))] with x hx hz
  have hzero := metricCommutatorTerm_order_zero G W.toFunction.jet (valueIndex2 K).2 x
  have hx0 := hx.trans (congrArg (fun q : PiLp 2 (fun _ : Fin 2 => E) => q k) hzero)
  simpa only [PiLp.zero_apply, Pi.zero_apply] using hx0.trans hz.symm

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.Weighted

/-! The stored metric flux is the word's principal diffusion plus its actual commutator. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeMetricCarrier_principal_value {K : ℕ}
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ k a, ContDiff ℝ (K : ℕ) (fun x => G x k a))
    (M : Fin (K + 1) → ℝ)
    (hb : ∀ (l : Fin (K + 1)) x k a,
      ‖iteratedFDeriv ℝ l.val (fun y => G y k a) x‖ ≤ M l)
    (hGc : ∀ k a, Continuous (fun x => G x k a))
    (C : ℝ) (hC : 0 ≤ C) (hGb : ∀ k a x, |G x k a| ≤ C)
    (W : PlaneHk Set.univ (K + 1) E) :
    planeFluxValueOperator K (planeMetricGradientCarrier G hG M hb W) =
      planeScalarDiffusion G hGc hC hGb
        (planeH1GradientOperator (truncatePlaneHk (by omega) W)) := by
  have hz := planeWordMetricCommutator_order_zero G hG M hb hGc C hC hGb W
  unfold planeWordMetricCommutator at hz
  rw [planeJetFluxOperator_order_zero, planeWordH1Slice_order_zero] at hz
  exact sub_eq_zero.mp hz

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.Weighted

/-! The full Sobolev source carriers represent exactly the original scalar weak equation. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem scalarCarrierSource_pair_eq_raw {K Kmax : ℕ} (hK : K ≤ Kmax)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (V : ℝ) (hbv : ∀ x, ‖v x‖ ≤ V) (a B lam : ℝ)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤
        a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (hvc : ∀ k, Continuous (fun x => v x k))
    (Cv : ℝ) (hCv : 0 ≤ Cv) (hvb : ∀ k x, |v x k| ≤ Cv)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ k j, ContDiff ℝ (K : ℕ) (fun x => G x k j))
    (M : Fin (K + 1) → ℝ)
    (hb : ∀ (l : Fin (K + 1)) x k j,
      ‖iteratedFDeriv ℝ l.val (fun y => G y k j) x‖ ≤ M l)
    (hGc : ∀ k j, Continuous (fun x => G x k j))
    (CG : ℝ) (hCG : 0 ≤ CG) (hGb : ∀ k j x, |G x k j| ≤ CG)
    (W : PlaneHk Set.univ (K + 1) E)
    (F : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (Z : PlaneHk Set.univ 1 E) :
    inner ℝ (planeHkValueOperator K
      (-planeTransportCarrier hK v hv V hbv a B lam hjets W)) (planeHkValueOperator 1 Z) -
      inner ℝ (planeFluxValueOperator K (planeMetricGradientCarrier G hG M hb W + F))
        (planeH1GradientOperator Z) = ∫ x, planeScalarRawRhs K v G W F Z x := by
  rw [map_neg, map_add, planeMetricCarrier_principal_value G hG M hb hGc CG hCG hGb W,
    planeDriftCarrier_principal_value hK v hv V hbv a B lam hjets hvc Cv hCv hvb W,
    inner_neg_left]
  exact (planeWeakDualRepresentative_pair
    (planeScalarTransport v hvc hCv hvb) (planeScalarDiffusion G hGc hCG hGb)
    (truncatePlaneHk (by omega) W) Z (planeFluxValueOperator K F)).symm.trans
      (planeScalarDual_pair_eq_raw K v hvc hCv hvb G hGc hCG hGb W F Z)

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.Weighted

/-! Actual full Sobolev sources built from window-only coefficient hypotheses. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def scalarSobolevTransportSource {K Kmax : ℕ} {ta tb : ℝ}
    (hK : K ≤ Kmax) (hab : ta ≤ tb)
    (v : ℝ → Vec 2 → Vec 2) (hv : ∀ t ∈ Set.Icc ta tb, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hbv : ∀ t ∈ Set.Icc ta tb, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc ta tb, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (W : ℝ → PlaneHk Set.univ (K + 1) E) : ℝ → PlaneHk Set.univ K E :=
  fun t => -planeTransportCarrier hK (planeIntervalCoefficient ta tb hab v t)
    (hv _ (Set.projIcc ta tb hab t).property) V
    (hbv _ (Set.projIcc ta tb hab t).property) strain B lam
    (hjets _ (Set.projIcc ta tb hab t).property) (W t)

def scalarSobolevMetricSource {K : ℕ} {ta tb : ℝ} (hab : ta ≤ tb)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ t ∈ Set.Icc ta tb, ∀ k j, ContDiff ℝ (K : ℕ) (fun x => G t x k j))
    (M : Fin (K + 1) → ℝ)
    (hb : ∀ t ∈ Set.Icc ta tb, ∀ (l : Fin (K + 1)) x k j,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k j) x‖ ≤ M l)
    (W : ℝ → PlaneHk Set.univ (K + 1) E)
    (F : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) :
    ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)) :=
  fun t => planeMetricGradientCarrier (planeIntervalCoefficient ta tb hab G t)
    (hG _ (Set.projIcc ta tb hab t).property) M
    (hb _ (Set.projIcc ta tb hab t).property) (W t) + F t

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.Weighted

/-! On the original window the clamped full Sobolev sources have the prescribed scalar RHS. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem scalarSobolevSource_pair_eq_raw {K Kmax : ℕ} {ta tb : ℝ}
    (hK : K ≤ Kmax) (hab : ta ≤ tb)
    (v : ℝ → Vec 2 → Vec 2) (hv : ∀ t ∈ Set.Icc ta tb, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hbv : ∀ t ∈ Set.Icc ta tb, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc ta tb, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ t ∈ Set.Icc ta tb, ∀ k j, ContDiff ℝ (K : ℕ) (fun x => G t x k j))
    (M : Fin (K + 1) → ℝ)
    (hb : ∀ t ∈ Set.Icc ta tb, ∀ (l : Fin (K + 1)) x k j,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k j) x‖ ≤ M l)
    (g : ℝ) (hg4 : g ≤ 1 / 4) (hGnear : IsMetricNearIdentity G g)
    (hGs : ∀ t ∈ Set.Icc ta tb, ∀ x, (G t x).IsSymm)
    (W : ℝ → PlaneHk Set.univ (K + 1) E)
    (F : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (t : ℝ) (ht : t ∈ Set.Icc ta tb) (Z : PlaneHk Set.univ 1 E) :
    inner ℝ (planeHkValueOperator K
      (scalarSobolevTransportSource hK hab v hv V strain B lam hbv hjets W t))
      (planeHkValueOperator 1 Z) -
      inner ℝ (planeFluxValueOperator K (scalarSobolevMetricSource hab G hG M hb W F t))
        (planeH1GradientOperator Z) = ∫ x, planeScalarRawRhs K (v t) (G t) (W t) (F t) Z x := by
  let τ := Set.projIcc ta tb hab t
  have hh := scalarCarrierSource_pair_eq_raw hK
    (planeIntervalCoefficient ta tb hab v t) (hv τ τ.property) V (hbv τ τ.property)
    strain B lam (hjets τ τ.property)
    (fun k => (continuous_apply k).comp (hv τ τ.property).continuous)
    (max V 0) (le_max_right _ _)
    (planeIntervalVelocity_bound ta tb hab v V hbv t)
    (planeIntervalCoefficient ta tb hab G t) (hG τ τ.property) M (hb τ τ.property)
    (fun k j => (hG τ τ.property k j).continuous) (5 / 4) (by norm_num)
    (planeIntervalMetric_bound ta tb hab G g hg4 hGnear hGs t) (W t) (F t) Z
  refine hh.trans ?_
  rw [planeIntervalCoefficient_of_mem ta tb hab v t ht,
    planeIntervalCoefficient_of_mem ta tb hab G t ht]

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.Weighted

/-! On the original window the clamped full Sobolev sources have the prescribed scalar RHS. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem scalarSobolevSource_word_residual_ae {K Kmax : ℕ} {ta tb : ℝ}
    (hK : K ≤ Kmax) (hab : ta ≤ tb)
    (v : ℝ → Vec 2 → Vec 2) (hv : ∀ t ∈ Set.Icc ta tb, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hbv : ∀ t ∈ Set.Icc ta tb, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc ta tb, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ t ∈ Set.Icc ta tb, ∀ k j, ContDiff ℝ (K : ℕ) (fun x => G t x k j))
    (M : Fin (K + 1) → ℝ)
    (hb : ∀ t ∈ Set.Icc ta tb, ∀ (l : Fin (K + 1)) x k j,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k j) x‖ ≤ M l)
    (g : ℝ) (hg4 : g ≤ 1 / 4) (hGnear : IsMetricNearIdentity G g)
    (hGs : ∀ t ∈ Set.Icc ta tb, ∀ x, (G t x).IsSymm)
    (W : ℝ → PlaneHk Set.univ (K + 1) E)
    (F : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (t : ℝ) (ht : t ∈ Set.Icc ta tb)
    (hG1 : ∀ t ∈ Set.Icc ta tb, ∀ k j, ContDiff ℝ 1 (fun x => G t x k j))
    (α : JetIndex2 K) :
    let H := scalarSobolevTransportSource hK hab v hv V strain B lam hbv hjets W
    let Q := scalarSobolevMetricSource hab G hG M hb W F
    let T := planeIntervalTransport ta tb hab v (fun t ht => (hv t ht).continuous) V hbv
    let A := planeIntervalDiffusion ta tb hab G (fun t ht k j => (hG1 t ht k j).continuous)
      g hg4 hGnear hGs
    (planeJetReadoutOperator K α (H t) + T t
      (planeH1GradientOperator (planeWordH1SliceOperator K α (W t)))) =ᵐ[volume]
      (fun x => -planeDriftCommutatorTerm (Nat.le_of_lt_succ α.1.isLt)
        (v t) (W t).toFunction.jet α.2 x) ∧
    (∀ k : Fin 2, (planeJetFluxOperator K α (Q t) - A t
      (planeH1GradientOperator (planeWordH1SliceOperator K α (W t)))) k =ᵐ[volume]
      fun x => metricCommutatorTerm (Nat.le_of_lt_succ α.1.isLt)
        (G t) (W t).toFunction.jet α.2 x k + (F t).val α x k) := by
  let τ := Set.projIcc ta tb hab t
  dsimp only
  constructor
  · have hd := scalarDriftCarrier_word_residual_ae hK
      (planeIntervalCoefficient ta tb hab v t) (hv τ τ.property) V (hbv τ τ.property)
      strain B lam (hjets τ τ.property)
      (planeIntervalVelocity_continuous ta tb hab v
        (fun r hr => (hv r hr).continuous) t) (max V 0) (le_max_right _ _)
      (planeIntervalVelocity_bound ta tb hab v V hbv t) (W t) α
    refine hd.trans (Filter.Eventually.of_forall (fun x => ?_))
    rw [planeIntervalCoefficient_of_mem ta tb hab v t ht]
  · intro k
    have hd := scalarMetricCarrier_word_residual_ae
      (planeIntervalCoefficient ta tb hab G t) (hG τ τ.property) M (hb τ τ.property)
      (planeIntervalMetric_continuous ta tb hab G
        (fun r hr k j => (hG1 r hr k j).continuous) t) (5 / 4) (by norm_num)
      (planeIntervalMetric_bound ta tb hab G g hg4 hGnear hGs t) (W t) α (F t) k
    refine hd.trans (Filter.Eventually.of_forall (fun x => ?_))
    rw [planeIntervalCoefficient_of_mem ta tb hab G t ht]

end AVRegularity.Weighted
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
open scoped ENNReal
namespace AVRegularity.Weighted

/-! Component flux readouts recover the original Hilbert-valued stored factorial energy. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem storedChartFluxEnergy_eq_factorial {K : ℕ} (ρ : ℝ) (q : Vec 2 → ℝ)
    (F : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) :
    storedChartFluxEnergy ρ q F = storedChartFactorialEnergy ρ q F := by
  apply Finset.sum_congr rfl
  intro α _
  congr 1
  apply lintegral_congr_ae
  have hh := ae_all_iff.mpr (fun k : Fin 2 => planeJetFluxOperator_ae α F k)
  filter_upwards [hh, univToPlane_ae (F.val α)] with x hx hy
  rw [planeJetReadoutOperator_apply, hy]
  simp_rw [hx]

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped ENNReal
namespace AVRegularity.Weighted

/-! The public polynomial factorial norm is the actual stored-word chart energy. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem weightedFactorialNormSq_stored_readout {K : ℕ}
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ) (U : PlaneHk Set.univ K E) :
    weightedFactorialNormSq n ϖ zc ρ K U =
      storedChartFactorialEnergy ρ (planeMomentPolynomial n ϖ zc) U := by
  unfold weightedFactorialNormSq storedChartFactorialEnergy
  rw [← Fin.sum_univ_eq_sum_range, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only
  rw [← Finset.mul_sum]
  congr 1
  exact planeJetOrder_moment_readout (Nat.le_of_lt_succ j.isLt) n ϖ zc U

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped ENNReal Topology
namespace AVRegularity.Weighted

/-! Measurability of the true polynomial factorial source budgets. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [BorelSpace E] [CompleteSpace E] in
theorem chartScalarEnergy_stationary_time_aemeasurable (q : Vec 2 → ℝ)
    (hq : Continuous q) (hq0 : ∀ x, 0 < q x) (μ : Measure ℝ)
    (U : ℝ → Lp E 2 (volume : Measure (Vec 2))) (hU : MemLp U 2 μ) :
    AEMeasurable (fun t => chartScalarEnergy q (U t)) μ := by
  have hc (n : ℕ) : Continuous (fun x => clipWeight ((n : ℝ) + 1) (q x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hasDerivAt_clipWeight (by positivity) (hq0 x)).continuousAt.comp hq.continuousAt
  have hb (n : ℕ) x : |clipWeight ((n : ℝ) + 1) (q x)| ≤ (n : ℝ) + 1 := by
    rw [abs_of_pos (clipWeight_pos (by positivity) (hq0 x))]
    exact clipWeight_le_bound (by positivity) (hq0 x)
  apply ENNReal.aemeasurable_of_tendsto (f := fun n t =>
    chartScalarEnergy (fun x => clipWeight ((n : ℝ) + 1) (q x)) (U t))
  · intro n
    have hi := weighted_spatial_energy_time_integrable (fun _ x => clipWeight ((n : ℝ) + 1) (q x))
      (fun _ => hc n) ((hc n).measurable.comp measurable_snd) (by positivity) (fun _ => hb n) U hU
    have he t := chartScalarEnergy_eq_ofReal _ (hc n) (hb n)
      (fun x => (clipWeight_pos (by positivity) (hq0 x)).le) (U t)
    have hh := ENNReal.measurable_ofReal.comp_aemeasurable hi.aemeasurable
    apply hh.congr
    exact Eventually.of_forall (fun t => (he t).symm)
  · exact Eventually.of_forall (fun t => chartScalarEnergy_clipping_tendsto q hq0
      (fun n => (hc n).measurable) (U t))

theorem weightedFactorialNormSq_time_aemeasurable {K : ℕ}
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ) (μ : Measure ℝ)
    (U : ℝ → PlaneHk Set.univ K E) (hU : MemLp U 2 μ) :
    AEMeasurable (fun t => weightedFactorialNormSq n ϖ zc ρ K (U t)) μ := by
  simp only [weightedFactorialNormSq_stored_readout, storedChartFactorialEnergy]
  apply Finset.aemeasurable_fun_sum
  intro α _
  have hi := (planeJetReadoutOperator (E := E) K α).comp_memLp' hU
  have hh := chartScalarEnergy_stationary_time_aemeasurable (E := E) (planeMomentPolynomial n ϖ zc)
    (by unfold planeMomentPolynomial; fun_prop) (fun x => by unfold planeMomentPolynomial; positivity)
    μ (fun t => planeJetReadoutOperator K α (U t)) hi
  exact hh.const_mul _

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Weighted

/-! Zero carrier data and fluxes have zero true weighted factorial energy. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
@[simp] theorem chartScalarEnergy_zero (q : Vec 2 → ℝ) :
    chartScalarEnergy q (0 : Lp E 2 (volume : Measure (Vec 2))) = 0 := by
  unfold chartScalarEnergy
  calc
    _ = ∫⁻ (_x : Vec 2), (0 : ℝ≥0∞) := by
      apply lintegral_congr_ae
      filter_upwards [Lp.coeFn_zero E 2 (volume : Measure (Vec 2))] with x hx
      simp only [hx, Pi.zero_apply, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero,
        ENNReal.ofReal_zero]
    _ = _ := lintegral_zero

variable [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

@[simp] theorem weightedFactorialNormSq_zero_carrier (n : ℕ) (ϖ : ℝ) (zc : Vec 2)
    (ρ : ℝ) (K : ℕ) :
    weightedFactorialNormSq n ϖ zc ρ K (0 : PlaneHk Set.univ K E) = 0 := by
  simp only [weightedFactorialNormSq_stored_readout, storedChartFactorialEnergy, map_zero,
    chartScalarEnergy_zero, mul_zero, Finset.sum_const_zero]

theorem planeHk_zero_time_memLp (K : ℕ) (μ : Measure ℝ) :
    MemLp (fun _ : ℝ => (0 : PlaneHk Set.univ K E)) 2 μ :=
  MemLp.zero' (ε := PlaneHk Set.univ K E)

end AVRegularity.Weighted
end
end
