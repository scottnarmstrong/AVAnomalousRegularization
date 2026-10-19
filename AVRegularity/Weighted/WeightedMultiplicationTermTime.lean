-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Weighted.WeightedZeroCarrier
import AVRegularity.CoupledEnergyPlane.Variational.ResidualValueSource
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.Weighted

/-! On the original window the clamped full Sobolev sources have the prescribed scalar RHS. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem scalarSobolevSource_word_energy_readout {K Kmax : ℕ} {ta tb : ℝ}
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
    (U : PlaneHk Set.univ K E) (hU : U = truncatePlaneHk (Nat.le_succ K) (W t))
    (ρ : ℝ) (q : Vec 2 → ℝ) :
    let H := scalarSobolevTransportSource hK hab v hv V strain B lam hbv hjets W
    let Q := scalarSobolevMetricSource hab G hG M hb W F
    let T := planeIntervalTransport ta tb hab v (fun t ht => (hv t ht).continuous) V hbv
    let A := planeIntervalDiffusion ta tb hab G (fun t ht k j => (hG1 t ht k j).continuous)
      g hg4 hGnear hGs
    let R := fun α : JetIndex2 K => planeJetReadoutOperator K α (H t) + T t
      (planeH1GradientOperator (planeWordH1SliceOperator K α (W t)))
    let L := fun α : JetIndex2 K => planeJetFluxOperator K α (Q t) - A t
      (planeH1GradientOperator (planeWordH1SliceOperator K α (W t)))
    ((∑ α : JetIndex2 K, factorialWeight ρ α.1.val *
      (∫ x, q x * (‖R α x‖ * ‖planeJetReadoutOperator K α U x‖))) =
      ∑ j : Fin (K + 1), factorialWeight ρ j.val *
        (∑ w : DerivativeWord2 j.val, ∫ x, q x *
          (‖planeDriftCommutatorTerm (Nat.le_of_lt_succ j.isLt) (v t)
            (W t).toFunction.jet w x‖ *
            ‖(W t).toFunction.jet ⟨⟨j.val, by omega⟩, w⟩ x‖))) ∧
    ((∑ α : JetIndex2 K, factorialWeight ρ α.1.val *
      (∫ x, q x * ‖(WithLp.toLp 2 (fun k : Fin 2 => L α k x) :
        PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2)) =
      ∑ j : Fin (K + 1), factorialWeight ρ j.val *
        (∑ w : DerivativeWord2 j.val, ∫ x, q x *
          ‖metricCommutatorTerm (Nat.le_of_lt_succ j.isLt) (G t)
            (W t).toFunction.jet w x + (F t).toFunction.jet ⟨j, w⟩ x‖ ^ 2)) := by
  dsimp only
  have hr (α : JetIndex2 K) := scalarSobolevSource_word_residual_ae hK hab v hv
    V strain B lam hbv hjets G hG M hb g hg4 hGnear hGs W F t ht hG1 α
  constructor
  · rw [storedWord_sum_weighted (fun j : Fin (K + 1) => factorialWeight ρ j.val)]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    apply Finset.sum_congr rfl
    intro w _
    apply weightedValueProduct_readout q _ _ _ _ (hr ⟨j, w⟩).1
    rw [hU, planeWord_truncate_value, planeWordH1Slice_value]
    exact AVRegularity.Analysis.Convolution.univToPlane_ae _
  · rw [storedWord_sum_weighted (fun j : Fin (K + 1) => factorialWeight ρ j.val)]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    apply Finset.sum_congr rfl
    intro w _
    apply weightedFluxEnergy_readout q _ _
    intro k
    exact (hr ⟨j, w⟩).2 k

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Finite integrated moments give simultaneous pointwise-in-time finiteness of all stored jets. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeJet_energy_ae_ne_top {K : ℕ}
    (q : Vec 2 → ℝ) (hq : Continuous q) (hq0 : ∀ x, 0 < q x)
    (μ : Measure ℝ) (U : ℝ → PlaneHk Set.univ K E) (hU : MemLp U 2 μ)
    (he : ∀ α, (∫⁻ t, chartScalarEnergy (fun x => q x ^ 2)
      (planeJetReadoutOperator K α (U t)) ∂μ) ≠ ⊤) :
    ∀ᵐ t ∂μ, ∀ α, chartScalarEnergy (fun x => q x ^ 2)
      (planeJetReadoutOperator K α (U t)) ≠ ⊤ := by
  apply ae_all_iff.mpr
  intro α
  have hm := chartScalarEnergy_stationary_time_aemeasurable (E := E)
    (fun x => q x ^ 2) (hq.pow 2) (fun x => sq_pos_of_pos (hq0 x)) μ
    (fun t => planeJetReadoutOperator K α (U t))
    ((planeJetReadoutOperator (E := E) K α).comp_memLp' hU)
  exact (ae_lt_top' hm (he α)).mono (fun _ ht => ht.ne)

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
open scoped ENNReal
namespace AVRegularity.Weighted

/-! The public gradient factorial norm sums the actual stored word gradients. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeJetNextOrder_moment_readout {K : ℕ} (j : Fin (K + 1))
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (W : PlaneHk Set.univ (K + 1) E) :
    (∫⁻ x, ENNReal.ofReal (planeMomentPolynomial n ϖ zc x *
      ∑ w : DerivativeWord2 (j.val + 1), ‖planeJetOrder W (j.val + 1) w x‖ ^ 2)) =
      ∑ w : DerivativeWord2 j.val, chartFiniteEnergy (planeMomentPolynomial n ϖ zc)
        (planeH1GradientOperator (planeWordH1SliceOperator K ⟨j, w⟩ W)) := by
  have hp x : 0 ≤ planeMomentPolynomial n ϖ zc x := by unfold planeMomentPolynomial; positivity
  have hsum x : (∑ w : DerivativeWord2 (j.val + 1), ‖planeJetOrder W (j.val + 1) w x‖ ^ 2) =
      ∑ w : DerivativeWord2 j.val,
        ‖(WithLp.toLp 2 (fun k : Fin 2 => W.toFunction.jet
          ⟨⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩, Fin.snoc w k⟩ x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2 := by
    simp only [planeJetOrder, dite_eq_left (Nat.succ_le_succ (Nat.le_of_lt_succ j.isLt))]
    simp only [PiLp.norm_sq_eq_of_L2]
    rw [← (Fin.snocEquiv (fun _ : Fin (j.val + 1) => Fin 2)).sum_comp,
      Fintype.sum_prod_type, Finset.sum_comm]
    rfl
  have hae : ∀ᵐ x ∂volume, ∀ w : DerivativeWord2 j.val, ∀ k : Fin 2,
      planeH1GradientOperator (planeWordH1SliceOperator K ⟨j, w⟩ W) k x =
        W.toFunction.jet ⟨⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩, Fin.snoc w k⟩ x := by
    apply ae_all_iff.mpr
    intro w
    apply ae_all_iff.mpr
    intro k
    rw [planeWordH1Slice_gradient]
    exact univToPlane_ae _
  calc
    _ = ∫⁻ x, ∑ w : DerivativeWord2 j.val,
        ENNReal.ofReal (planeMomentPolynomial n ϖ zc x *
          ‖(WithLp.toLp 2 (fun k : Fin 2 => planeH1GradientOperator
            (planeWordH1SliceOperator K ⟨j, w⟩ W) k x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) := by
      apply lintegral_congr_ae
      filter_upwards [hae] with x hx
      rw [hsum, Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg]
      · simp_rw [hx]
      · intro w _
        exact mul_nonneg (hp x) (sq_nonneg _)
    _ = _ := by
      rw [lintegral_finsetSum']
      · rfl
      · intro w _
        exact (by unfold planeMomentPolynomial; fun_prop : Measurable (planeMomentPolynomial n ϖ zc)).aemeasurable.mul
          (finiteLp_normSq_integrable
            (planeH1GradientOperator (planeWordH1SliceOperator K ⟨j, w⟩ W))).aemeasurable |>.ennreal_ofReal

theorem weightedGradFactorialNormSq_stored_readout {K : ℕ}
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ) (W : PlaneHk Set.univ (K + 1) E) :
    weightedGradFactorialNormSq n ϖ zc ρ K W =
      storedChartGradientEnergy ρ (planeMomentPolynomial n ϖ zc) W := by
  unfold weightedGradFactorialNormSq storedChartGradientEnergy
  rw [← Fin.sum_univ_eq_sum_range, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only
  rw [← Finset.mul_sum]
  congr 1
  exact planeJetNextOrder_moment_readout j n ϖ zc W

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Weighted

/-! Finitely many genuine component budgets give finite public geometry norms. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [∀ i, FiniteDimensional ℝ (h i)] in
theorem geometryDataNorm_ne_top_of_components (π : ι → ℝ) (κ : ι → ℕ)
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ)
    (f : ∀ i, PlaneHk Set.univ (κ i) (h i))
    (he : ∀ i, weightedFactorialNormSq n ϖ zc ρ (κ i) (f i) ≠ ⊤) :
    geometryDataNorm π κ n ϖ zc ρ f ≠ ⊤ := by
  apply ENNReal.rpow_ne_top_of_nonneg (by norm_num)
  apply ENNReal.sum_ne_top.mpr
  intro i _
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (he i)

theorem geometryFluxNorm_ne_top_of_components (π : ι → ℝ) (κ : ι → ℕ)
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ ta tb : ℝ)
    (F : ∀ i, ℝ → PlaneHk Set.univ (κ i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc ta tb)))
    (he : ∀ i, (∫⁻ t in Set.Icc ta tb,
      weightedFactorialNormSq n ϖ zc ρ (κ i) (F i t)) ≠ ⊤) :
    geometryFluxNorm π κ n ϖ zc ρ ta tb F ≠ ⊤ := by
  apply ENNReal.rpow_ne_top_of_nonneg (by norm_num)
  rw [lintegral_finsetSum' _ (fun i _ =>
    (weightedFactorialNormSq_time_aemeasurable n ϖ zc ρ _ (F i) (hF i)).const_mul _)]
  apply ENNReal.sum_ne_top.mpr
  intro i _
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (he i)
end

/-! Integrated weighted production controls each literal next stored derivative. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem chartScalarEnergy_coordinate_le_finite (q : Vec 2 → ℝ)
    (hq : ∀ x, 0 ≤ q x)
    (U : PiLp 2 (fun _ : Fin 2 => Lp E 2 (volume : Measure (Vec 2)))) (k : Fin 2) :
    chartScalarEnergy q (U k) ≤ chartFiniteEnergy q U := by
  apply lintegral_mono
  intro x
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (hq x)
  rw [PiLp.norm_sq_eq_of_L2]
  exact Finset.single_le_sum (fun i _ => sq_nonneg ‖U i x‖) (Finset.mem_univ k)

theorem weighted_gradient_readout_integral_ne_top {K : ℕ}
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ) (hρ : 0 < ρ) (μ : Measure ℝ)
    (W : ℝ → PlaneHk Set.univ (K + 1) E)
    (he : (∫⁻ t, weightedGradFactorialNormSq n ϖ zc ρ K (W t) ∂μ) ≠ ⊤)
    (α : JetIndex2 K) (k : Fin 2) :
    (∫⁻ t, chartScalarEnergy (planeMomentPolynomial n ϖ zc)
      (planeJetReadoutOperator (K + 1)
        ⟨⟨α.1.val + 1, Nat.succ_lt_succ α.1.isLt⟩, Fin.snoc α.2 k⟩ (W t)) ∂μ) ≠ ⊤ := by
  have hh := finite_integrated_weighted_sum_component μ
    (fun α : JetIndex2 K => factorialWeight ρ α.1.val)
    (fun α => factorialWeight_pos_of_radius_pos ρ hρ α.1.val)
    (fun α t => chartFiniteEnergy (planeMomentPolynomial n ϖ zc)
      (planeH1GradientOperator (planeWordH1SliceOperator K α (W t))))
    (by simpa only [weightedGradFactorialNormSq_stored_readout, storedChartGradientEnergy] using he) α
  apply ne_top_of_le_ne_top hh
  apply lintegral_mono
  intro t
  dsimp only
  rw [planeJetReadoutOperator_apply, ← planeWordH1Slice_gradient K α (W t) k]
  exact chartScalarEnergy_coordinate_le_finite _
    (fun x => by unfold planeMomentPolynomial; positivity) _ k
end

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Every positive stored jet lies in the weighted production budget. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem weighted_production_positive_jet_integral_ne_top {K : ℕ}
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ) (hρ : 0 < ρ) (μ : Measure ℝ)
    (W : ℝ → PlaneHk Set.univ (K + 1) E)
    (he : (∫⁻ t, weightedGradFactorialNormSq n ϖ zc ρ K (W t) ∂μ) ≠ ⊤)
    (α : JetIndex2 (K + 1)) (hα : 0 < α.1.val) :
    (∫⁻ t, chartScalarEnergy (planeMomentPolynomial n ϖ zc)
      (planeJetReadoutOperator (K + 1) α (W t)) ∂μ) ≠ ⊤ := by
  rcases α with ⟨⟨j, hj⟩, w⟩
  cases j with
  | zero => exact (Nat.lt_irrefl 0 hα).elim
  | succ j =>
    let β : JetIndex2 K := ⟨⟨j, by omega⟩, Fin.init w⟩
    have hh := weighted_gradient_readout_integral_ne_top n ϖ zc ρ hρ μ W he β
      (w (Fin.last j))
    have heq : (⟨⟨β.1.val + 1, Nat.succ_lt_succ β.1.isLt⟩,
        Fin.snoc β.2 (w (Fin.last j))⟩ : JetIndex2 (K + 1)) = ⟨⟨j + 1, hj⟩, w⟩ := by
      simp only [β, Fin.snoc_init_self]
    simpa only [heq] using hh

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory Filter
open scoped Topology
namespace AVRegularity.Weighted

/-! Finite integrated polynomial energy supplies an actual strongly measurable weighted L2 curve. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [BorelSpace E] [CompleteSpace E] in
theorem weightedPlaneLpReadout_time_memLp (q : Vec 2 → ℝ) (hq : Continuous q)
    (hq0 : ∀ x, 0 < q x) (μ : Measure ℝ)
    (U : ℝ → Lp E 2 (volume : Measure (Vec 2))) (hU : MemLp U 2 μ)
    (he : (∫⁻ t, chartScalarEnergy (fun x => q x ^ 2) (U t) ∂μ) ≠ ⊤) :
    MemLp (fun t => weightedPlaneLpReadout q hq (U t)) 2 μ := by
  have hqe := chartScalarEnergy_stationary_time_aemeasurable (E := E)
    (fun x => q x ^ 2) (hq.pow 2) (fun x => sq_pos_of_pos (hq0 x)) μ U hU
  have hfin : ∀ᵐ t ∂μ, chartScalarEnergy (fun x => q x ^ 2) (U t) ≠ ⊤ :=
    (ae_lt_top' hqe he).mono (fun _ ht => ht.ne)
  have hc (n : ℕ) : Continuous (fun x => clipWeight ((n : ℝ) + 1) (q x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hasDerivAt_clipWeight (by positivity) (hq0 x)).continuousAt.comp hq.continuousAt
  have hb (n : ℕ) x : |clipWeight ((n : ℝ) + 1) (q x)| ≤ (n : ℝ) + 1 := by
    rw [abs_of_pos (clipWeight_pos (by positivity) (hq0 x))]
    exact clipWeight_le_bound (by positivity) (hq0 x)
  let f := fun (n : ℕ) t => planeScalarMultiplier (E := E)
    (fun x => clipWeight ((n : ℝ) + 1) (q x)) (hc n) (by positivity) (hb n) (U t)
  have hf (n : ℕ) : AEStronglyMeasurable (f n) μ :=
    ((planeScalarMultiplier (E := E) (fun x => clipWeight ((n : ℝ) + 1) (q x))
      (hc n) (by positivity) (hb n)).comp_memLp' hU).aestronglyMeasurable
  have ht : ∀ᵐ t ∂μ, Tendsto (fun n => f n t) atTop (𝓝 (weightedPlaneLpReadout q hq (U t))) := by
    filter_upwards [hfin] with t ht
    obtain ⟨hc', hb', hlim⟩ := weighted_planeLp_clipping_tendsto q hq hq0 (U t)
      (weighted_plane_memLp_of_chartEnergy_ne_top q hq (U t) ht)
    rw [weightedPlaneLpReadout, dite_eq_left ht]
    exact hlim
  have hm := aestronglyMeasurable_of_tendsto_ae atTop hf ht
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  refine ⟨hm.norm.pow 2, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun t =>
    sq_nonneg ‖weightedPlaneLpReadout q hq (U t)‖))).mpr
  have hsame : (∫⁻ t, ENNReal.ofReal (‖weightedPlaneLpReadout q hq (U t)‖ ^ 2) ∂μ) =
      ∫⁻ t, chartScalarEnergy (fun x => q x ^ 2) (U t) ∂μ :=
    lintegral_congr_ae (hfin.mono (fun t ht => weightedPlaneLpReadout_energy q hq (U t) ht))
  rw [hsame]
  exact lt_top_iff_ne_top.mpr he

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Weighted

/-! A true componentwise budget gives the public geometry energy norm. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem geometryEnergyNorm_of_component_bounds (π : ι → ℝ) (Kslot : ι → ℕ)
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (r a b : ℝ)
    (f : ∀ i, PlaneHk Set.univ (Kslot i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (Kslot i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (u : ∀ i, ℝ → PlaneHk Set.univ (Kslot i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (Kslot i + 1) (h i))
    (A : ℝ) (hA : 0 ≤ A)
    (hbudget : ∀ i,
      (⨆ t ∈ Set.Icc a b, weightedFactorialNormSq n ϖ zc r (Kslot i) (u i t)) +
        (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq n ϖ zc r (Kslot i) (w i t)) ≤
      ENNReal.ofReal A * (weightedFactorialNormSq n ϖ zc r (Kslot i) (f i) +
        16 * ∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ zc r (Kslot i) (F i t))) :
    geometryEnergyNorm π Kslot n ϖ zc r a b u w ≤
      ENNReal.ofReal ((16 * A) ^ (1 / 2 : ℝ)) *
        (geometryDataNorm π Kslot n ϖ zc r f + geometryFluxNorm π Kslot n ϖ zc r a b F) := by
  have hh := family_weighted_energy_budget (volume.restrict (Set.Icc a b))
    (fun i => ENNReal.ofReal ((π i)⁻¹)) (fun _ => ENNReal.ofReal_ne_top)
    (fun i => (⨆ t ∈ Set.Icc a b, weightedFactorialNormSq n ϖ zc r (Kslot i) (u i t)) +
      ∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq n ϖ zc r (Kslot i) (w i t))
    (fun i => weightedFactorialNormSq n ϖ zc r (Kslot i) (f i))
    (fun i t => weightedFactorialNormSq n ϖ zc r (Kslot i) (F i t)) (ENNReal.ofReal A)
    (fun i => weightedFactorialNormSq_time_aemeasurable n ϖ zc r _ (F i) (hF i)) hbudget
  exact family_energy_square_root hA hh

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Weighted

/-! Dividing a growing coefficient by the input weight gives a bounded native L2 operator. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] in
theorem growingCoefficient_normalized_bound
    (q : Vec 2 → ℝ) (hq0 : ∀ x, 0 < q x)
    (C : ℝ → Vec 2 → E →L[ℝ] F) (A : ℝ)
    (hb : ∀ t x, ‖C t x‖ ≤ A * q x) :
    ∀ t x, ‖(q x)⁻¹ • C t x‖ ≤ A := by
  intro t x
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (hq0 x).le)]
  calc
    (q x)⁻¹ * ‖C t x‖ ≤ (q x)⁻¹ * (A * q x) :=
      mul_le_mul_of_nonneg_left (hb t x) (inv_nonneg.mpr (hq0 x).le)
    _ = A := by rw [mul_left_comm, inv_mul_cancel₀ (hq0 x).ne', mul_one]

def growingCoefficientReadout
    (q : Vec 2 → ℝ) (hq : Continuous q) (hq0 : ∀ x, 0 < q x)
    (C : ℝ → Vec 2 → E →L[ℝ] F) (hc : ∀ t, Continuous (C t))
    (A : ℝ) (hA : 0 ≤ A) (hb : ∀ t x, ‖C t x‖ ≤ A * q x)
    (U : ℝ → Lp E 2 (volume : Measure (Vec 2))) (t : ℝ) :
    Lp F 2 (volume : Measure (Vec 2)) :=
  planeCoefficientOperator (fun x => (q x)⁻¹ • C t x)
    ((hq.inv₀ (fun x => (hq0 x).ne')).smul (hc t)) hA
    (growingCoefficient_normalized_bound q hq0 C A hb t)
    (weightedPlaneLpReadout q hq (U t))

omit [BorelSpace E] [CompleteSpace E] [BorelSpace F] [CompleteSpace F] in
theorem growingCoefficientReadout_time_memLp
    (q : Vec 2 → ℝ) (hq : Continuous q) (hq0 : ∀ x, 0 < q x)
    (C : ℝ → Vec 2 → E →L[ℝ] F) (hc : ∀ t, Continuous (C t))
    (hj : Measurable (Function.uncurry C))
    (A : ℝ) (hA : 0 ≤ A) (hb : ∀ t x, ‖C t x‖ ≤ A * q x)
    (μ : Measure ℝ) (U : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (hU : MemLp U 2 μ)
    (he : (∫⁻ t, chartScalarEnergy (fun x => q x ^ 2) (U t) ∂μ) ≠ ⊤) :
    MemLp (growingCoefficientReadout q hq hq0 C hc A hA hb U) 2 μ := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  let : SecondCountableTopology (Lp E 2 (volume : Measure (Vec 2))) := Lp.SecondCountableTopology
  borelize ↥(Lp E 2 (volume : Measure (Vec 2)))
  have hn : Measurable (Function.uncurry (fun t x => (q x)⁻¹ • C t x)) :=
    (hq.measurable.comp measurable_snd).inv.smul hj
  exact memLp_operator_action
    (fun t => planeCoefficientOperator (fun x => (q x)⁻¹ • C t x)
      ((hq.inv₀ (fun x => (hq0 x).ne')).smul (hc t)) hA
      (growingCoefficient_normalized_bound q hq0 C A hb t))
    (fun z => planeCoefficientOperator_stronglyMeasurable _ _ hn hA
      (growingCoefficient_normalized_bound q hq0 C A hb) z)
    (weightedPlaneLpReadout_time_memLp q hq hq0 μ U hU he) hA
    (fun t => planeCoefficientOperator_norm_le _ _ _ _)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [BorelSpace E] [CompleteSpace E] [BorelSpace F] [CompleteSpace F] in
theorem growingCoefficientReadout_ae
    (q : Vec 2 → ℝ) (hq : Continuous q) (hq0 : ∀ x, 0 < q x)
    (C : ℝ → Vec 2 → E →L[ℝ] F) (hc : ∀ t, Continuous (C t))
    (A : ℝ) (hA : 0 ≤ A) (hb : ∀ t x, ‖C t x‖ ≤ A * q x)
    (U : ℝ → Lp E 2 (volume : Measure (Vec 2))) (t : ℝ)
    (he : chartScalarEnergy (fun x => q x ^ 2) (U t) ≠ ⊤) :
    growingCoefficientReadout q hq hq0 C hc A hA hb U t =ᵐ[volume]
      fun x => C t x (U t x) := by
  filter_upwards [planeCoefficientOperator_ae _ _ hA
    (growingCoefficient_normalized_bound q hq0 C A hb t)
    (weightedPlaneLpReadout q hq (U t)), weightedPlaneLpReadout_ae q hq (U t) he]
    with x hx hw
  change growingCoefficientReadout q hq hq0 C hc A hA hb U t x = _ at hx ⊢
  rw [hx, hw]
  simp [map_smul, smul_smul, (hq0 x).ne']

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.Weighted

/-! The actual clipped compact energy estimate, retaining diffusion dissipation. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeWeak_clipped_compact_value_gronwall
    (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hv : ∀ t ∈ Icc a b, ContDiff ℝ 1 (v t))
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ j : Fin 2, fderiv ℝ (v t) x (basisVec j) j = 0)
    (M : ℝ) (hM : 0 ≤ M) (hvb : ∀ t ∈ Icc a b, ∀ x, ‖v t x‖ ≤ M)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ t ∈ Icc a b, ∀ k j, ContDiff ℝ 1 (fun x => G t x k j))
    (g : ℝ) (hg4 : g ≤ 1 / 4) (hGnear : IsMetricNearIdentity G g)
    (hGs : ∀ t ∈ Icc a b, ∀ x, (G t x).IsSymm)
    (t₀ S ϖ : ℝ) (zc : Vec 2) (N m : ℕ) (Cw : ℕ → ℝ)
    (W : ChartWeights G v t₀ S ϖ zc N Cw) (hm : m ≤ N)
    (ha : t₀ ≤ a) (hb : b ≤ t₀ + S)
    (u : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (slice : ℝ → PlaneHk Set.univ 1 E) (F : ℝ → PlaneFluxL2 E)
    (H : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (h : PlaneWeakHilbertCurve a b u slice
      (fun t => planeValueForcedDual
        (planeIntervalTransport a b hab v (fun t ht => (hv t ht).continuous) M hvb t)
        (planeIntervalDiffusion a b hab G (fun t ht k j => (hG t ht k j).continuous)
          g hg4 hGnear hGs t) (slice t) (F t) (H t)))
    (χ : Vec 2 → ℝ) (hχ : ContDiff ℝ 2 χ) (hsχ : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (η : ℝ) (hη : 0 ≤ η) (hdχ : ∀ x, ‖fderiv ℝ χ x‖ ≤ η)
    (B : ℝ) (hB : 0 < B) (hF : MemLp F 2 (volume.restrict (Icc a b)))
    (hH : MemLp H 2 (volume.restrict (Icc a b))) :
    ∀ t ∈ Icc a b,
      (∫ x, χ x ^ 2 * clipWeight B (W.W m t x) * ‖u t x‖ ^ 2) +
      (∫ s in a..t, ∫ x, χ x ^ 2 * clipWeight B (W.W m s x) *
        ‖(WithLp.toLp 2 (fun i => planeH1GradientOperator (E := E) (slice s) i x) :
          PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) ≤
      ((∫ x, χ x ^ 2 * clipWeight B (W.W m a x) * ‖u a x‖ ^ 2) +
        ∫ s in a..b,
          8 * (∫ x, clipWeight B (W.W m s x) *
            ‖(WithLp.toLp 2 (fun i => F s i x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) +
          (4096 * η ^ 2 + 16 * M * η) *
            (∫ x, clipWeight B (W.W m s x) * ‖u s x‖ ^ 2) +
          2 * (∫ x, (χ x ^ 2 * clipWeight B (W.W m s x)) * (‖H s x‖ * ‖u s x‖))) *
        Real.exp (18 * W.lam m * (t - a)) := by
  obtain ⟨P, htime, hgrowth⟩ := planeWeak_clipped_value_energy_growth a b hab v hv hdiv M hM hvb
    G hG g hg4 hGnear hGs t₀ S ϖ zc N m Cw W hm ha hb u slice F H h χ hχ hsχ
    hχ0 hχ1 η hη hdχ B hB
  let q := fun t x => clipWeight B (W.W m t x)
  let force := fun t => ∫ x, q t x *
    ‖(WithLp.toLp 2 (fun i => F t i x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2
  let val := fun t => ∫ x, (χ x ^ 2 * q t x) * (‖H t x‖ * ‖u t x‖)
  let mass := fun t => ∫ x, q t x * ‖u t x‖ ^ 2
  let d := fun t => ∫ x, χ x ^ 2 * q t x *
    ‖(WithLp.toLp 2 (fun i => planeH1GradientOperator (E := E) (slice t) i x) :
      PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2
  let c := 4096 * η ^ 2 + 16 * M * η
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hu : MemLp u 2 (volume.restrict (Icc a b)) :=
    (memLp_congr_ae h.agrees).2 ((planeHkValueOperator (E := E) 1).comp_memLp' h.state)
  have hvint : Integrable val (volume.restrict (Icc a b)) :=
    chartWeights_clipped_cutoff_value_product_integrable W m hm B hB χ hχ.continuous
      hχ0 hχ1 _ H u hH hu
  have hfint : Integrable force (volume.restrict (Icc a b)) :=
    chartWeights_clipped_finite_time_integrable W m hm B hB _ F hF
  have hmint : Integrable mass (volume.restrict (Icc a b)) :=
    chartWeights_clipped_scalar_time_integrable W m hm B hB _ u hu
  have hdint : Integrable d (volume.restrict (Icc a b)) :=
    chartWeights_clipped_cutoff_finite_time_integrable W m hm B hB χ hχ.continuous hχ0 hχ1 _
      (fun t => planeH1GradientOperator (E := E) (slice t))
      ((planeH1GradientOperator (E := E)).comp_memLp' h.state)
  have hforce0 t : 0 ≤ force t := integral_nonneg (fun x => by
    exact mul_nonneg (clipWeight_pos hB (W.pos m hm t x)).le (sq_nonneg _))
  have hval0 t : 0 ≤ val t := integral_nonneg (fun x =>
    mul_nonneg (mul_nonneg (sq_nonneg _) (clipWeight_pos hB (W.pos m hm t x)).le)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  have hmass0 t : 0 ≤ mass t := integral_nonneg (fun x =>
    mul_nonneg (clipWeight_pos hB (W.pos m hm t x)).le (sq_nonneg _))
  have hd0 t : 0 ≤ d t := integral_nonneg (fun x =>
    mul_nonneg (mul_nonneg (sq_nonneg _) (clipWeight_pos hB (W.pos m hm t x)).le) (sq_nonneg _))
  exact scalar_energy_dissipation_le_gronwall hab htime (18 * W.lam m)
    (mul_nonneg (by norm_num) (W.lam_bound m hm).1)
    (fun t => 8 * force t + c * mass t + 2 * val t) d
    (intervalIntegrable_of_integrable_Icc hab (((hfint.const_mul 8).add (hmint.const_mul c)).add (hvint.const_mul 2)))
    (intervalIntegrable_of_integrable_Icc hab hdint)
    (Filter.Eventually.of_forall (fun t => add_nonneg (add_nonneg (mul_nonneg (by norm_num) (hforce0 t))
      (mul_nonneg hc (hmass0 t))) (mul_nonneg (by norm_num) (hval0 t))))
    (Filter.Eventually.of_forall hd0) (by
      simpa only [d, force, c, mass, val, q, add_assoc] using hgrowth)

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory
namespace AVRegularity.Weighted

/-! Finite sums preserve the integrated polynomial moment of actual time L2 readouts. -/

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [Fintype ι]

theorem integrated_chart_energy_finite_sum_ne_top
    (q : Vec 2 → ℝ) (hq : Continuous q) (hq0 : ∀ x, 0 < q x)
    (μ : Measure ℝ) (U : ι → ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (hU : ∀ i, MemLp (U i) 2 μ)
    (he : ∀ i, (∫⁻ t, chartScalarEnergy (fun x => q x ^ 2) (U i t) ∂μ) ≠ ⊤) :
    (∫⁻ t, chartScalarEnergy (fun x => q x ^ 2) (∑ i, U i t) ∂μ) ≠ ⊤ := by
  classical
  have hf (i : ι) : ∃ R : ℝ → Lp E 2 (volume : Measure (Vec 2)), MemLp R 2 μ ∧
      ∀ᵐ t ∂μ, R t =ᵐ[volume] fun x => q x • U i t x := by
    refine ⟨fun t => weightedPlaneLpReadout q hq (U i t),
      weightedPlaneLpReadout_time_memLp q hq hq0 μ (U i) (hU i) (he i), ?_⟩
    have hm := chartScalarEnergy_stationary_time_aemeasurable (fun x => q x ^ 2)
      (hq.pow 2) (fun x => sq_pos_of_pos (hq0 x)) μ (U i) (hU i)
    filter_upwards [ae_lt_top' hm (he i)] with t ht
    exact weightedPlaneLpReadout_ae q hq (U i t) ht.ne
  obtain ⟨R, hR, hRae⟩ := exists_finite_time_l2_readout_sum μ volume
    (fun i t x => q x • U i t x) hf
  apply weighted_representative_time_energy_ne_top q μ _ R hR
  filter_upwards [hRae] with t ht
  have hsum := Lp.coeFn_finsetSum Finset.univ (fun i => U i t)
  filter_upwards [ht, hsum] with x hx hs
  rw [hx, hs]
  simp only [Finset.sum_apply, Finset.smul_sum]

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.Weighted

/-! The window source carriers are actual Bochner square-integrable Sobolev functions. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem scalarSobolevMetricSource_memLp {K : ℕ} {ta tb : ℝ} (hab : ta ≤ tb)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hGm : Measurable (fun p : Set.Icc ta tb × Vec 2 => G p.1 p.2))
    (hG : ∀ t ∈ Set.Icc ta tb, ∀ k j, ContDiff ℝ (K : ℕ) (fun x => G t x k j))
    (M : Fin (K + 1) → ℝ)
    (hb : ∀ t ∈ Set.Icc ta tb, ∀ (l : Fin (K + 1)) x k j,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k j) x‖ ≤ M l)
    (W : ℝ → PlaneHk Set.univ (K + 1) E)
    (F : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (hW : MemLp W 2 (volume.restrict (Set.Icc ta tb)))
    (hF : MemLp F 2 (volume.restrict (Set.Icc ta tb))) :
    MemLp (scalarSobolevMetricSource (E := E) (K := K) hab G hG M hb W F) 2
      (volume.restrict (Set.Icc ta tb)) := by
  unfold scalarSobolevMetricSource
  have hmetric := intervalMetricGradientCarrier_memLp (E := E) (K := K) hab G hGm hG M hb W hW
  exact bochnerSource_memLp_add hmetric hF

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Growing coefficients act measurably on each actual stored Sobolev time jet. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

omit [BorelSpace F] [CompleteSpace F] in
theorem growingCoefficient_planeJet_time_memLp {K : ℕ}
    (q : Vec 2 → ℝ) (hq : Continuous q) (hq0 : ∀ x, 0 < q x)
    (C : ℝ → Vec 2 → E →L[ℝ] F) (hc : ∀ t, Continuous (C t))
    (hj : Measurable (Function.uncurry C))
    (A : ℝ) (hA : 0 ≤ A) (hb : ∀ t x, ‖C t x‖ ≤ A * q x)
    (μ : Measure ℝ) (U : ℝ → PlaneHk Set.univ K E) (hU : MemLp U 2 μ)
    (α : JetIndex2 K)
    (he : (∫⁻ t, chartScalarEnergy (fun x => q x ^ 2)
      (planeJetReadoutOperator K α (U t)) ∂μ) ≠ ⊤) :
    MemLp (growingCoefficientReadout q hq hq0 C hc A hA hb
      (fun t => planeJetReadoutOperator K α (U t))) 2 μ :=
  growingCoefficientReadout_time_memLp q hq hq0 C hc hj A hA hb μ _
    ((planeJetReadoutOperator (E := E) K α).comp_memLp' hU) he

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [BorelSpace F] [CompleteSpace F] in
theorem growingCoefficient_planeJet_ae_raw {K : ℕ}
    (q : Vec 2 → ℝ) (hq : Continuous q) (hq0 : ∀ x, 0 < q x)
    (C : ℝ → Vec 2 → E →L[ℝ] F) (hc : ∀ t, Continuous (C t))
    (A : ℝ) (hA : 0 ≤ A) (hb : ∀ t x, ‖C t x‖ ≤ A * q x)
    (U : ℝ → PlaneHk Set.univ K E) (α : JetIndex2 K) (t : ℝ)
    (he : chartScalarEnergy (fun x => q x ^ 2) (planeJetReadoutOperator K α (U t)) ≠ ⊤) :
    growingCoefficientReadout q hq hq0 C hc A hA hb
      (fun t => planeJetReadoutOperator K α (U t)) t =ᵐ[volume]
        fun x => C t x ((U t).toFunction.jet α x) := by
  filter_upwards [growingCoefficientReadout_ae q hq hq0 C hc A hA hb
    (fun t => planeJetReadoutOperator K α (U t)) t he, planeJetReadout_ae_raw (U t) α]
    with x hx hu
  exact hx.trans (congrArg (C t x) hu)
end

/-! Weighted production gives true weighted L2 time curves for every positive derivative order. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def planeMomentSquareRoot (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (x : Vec 2) : ℝ :=
  Real.sqrt (planeMomentPolynomial n ϖ zc x)

theorem planeMomentSquareRoot_continuous (n : ℕ) (ϖ : ℝ) (zc : Vec 2) :
    Continuous (planeMomentSquareRoot n ϖ zc) := by
  unfold planeMomentSquareRoot planeMomentPolynomial
  fun_prop

theorem planeMomentSquareRoot_pos (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (x : Vec 2) :
    0 < planeMomentSquareRoot n ϖ zc x := by
  unfold planeMomentSquareRoot planeMomentPolynomial
  positivity

theorem planeMomentSquareRoot_sq (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (x : Vec 2) :
    planeMomentSquareRoot n ϖ zc x ^ 2 = planeMomentPolynomial n ϖ zc x := by
  apply Real.sq_sqrt
  unfold planeMomentPolynomial
  positivity
end

/-! Finite integrated stored-jet moments give the true factorial source budget. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem integrated_storedChartFactorialEnergy_ne_top {K : ℕ}
    (ρ : ℝ) (q : Vec 2 → ℝ) (hq : Continuous q) (hq0 : ∀ x, 0 < q x)
    (μ : Measure ℝ) (U : ℝ → PlaneHk Set.univ K E) (hU : MemLp U 2 μ)
    (he : ∀ α, (∫⁻ t, chartScalarEnergy q (planeJetReadoutOperator K α (U t)) ∂μ) ≠ ⊤) :
    (∫⁻ t, storedChartFactorialEnergy ρ q (U t) ∂μ) ≠ ⊤ := by
  classical
  have hm (α : JetIndex2 K) := chartScalarEnergy_stationary_time_aemeasurable
    q hq hq0 μ (fun t => planeJetReadoutOperator K α (U t))
      ((planeJetReadoutOperator (E := E) K α).comp_memLp' hU)
  simp only [storedChartFactorialEnergy]
  rw [lintegral_finsetSum' _ (fun α _ => (hm α).const_mul _)]
  apply ENNReal.sum_ne_top.mpr
  intro α _
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (he α)

theorem integrated_weightedFactorialNormSq_ne_top {K : ℕ}
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ) (μ : Measure ℝ)
    (U : ℝ → PlaneHk Set.univ K E) (hU : MemLp U 2 μ)
    (he : ∀ α, (∫⁻ t, chartScalarEnergy (fun x => (planeMomentSquareRoot n ϖ zc x) ^ 2)
      (planeJetReadoutOperator K α (U t)) ∂μ) ≠ ⊤) :
    (∫⁻ t, weightedFactorialNormSq n ϖ zc ρ K (U t) ∂μ) ≠ ⊤ := by
  have hs : (fun x => (planeMomentSquareRoot n ϖ zc x) ^ 2) =
      planeMomentPolynomial n ϖ zc := funext (planeMomentSquareRoot_sq n ϖ zc)
  simp only [hs] at he
  simp only [weightedFactorialNormSq_stored_readout]
  exact integrated_storedChartFactorialEnergy_ne_top ρ (planeMomentPolynomial n ϖ zc)
    (by unfold planeMomentPolynomial; fun_prop) (fun x => by unfold planeMomentPolynomial; positivity)
    μ U hU he
end

/-! Each positional Leibniz term is an actual L2 time curve under finite source moments. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

omit [BorelSpace F] [CompleteSpace F] in
theorem exists_growing_multiplicationTerm_time_readout {K j : ℕ} (hj : j ≤ K)
    (q : Vec 2 → ℝ) (hq : Continuous q) (hq0 : ∀ x, 0 < q x)
    (C : ℝ → Vec 2 → E →L[ℝ] F) (hC : ∀ t, ContDiff ℝ (K : ℕ) (C t))
    (hCm : ∀ l : Fin (K + 1), ∀ β : DerivativeWord2 l.val,
      Measurable (Function.uncurry (fun t => orderedCoefficientDerivative (C t) l.val β)))
    (A : Fin (K + 1) → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ l t x, ‖coefficientDerivativeArray (C t) l.val x‖ ≤ A l * q x)
    (μ : Measure ℝ) (U : ℝ → PlaneHk Set.univ K E) (hU : MemLp U 2 μ)
    (he : ∀ α, (∫⁻ t, chartScalarEnergy (fun x => q x ^ 2)
      (planeJetReadoutOperator K α (U t)) ∂μ) ≠ ⊤)
    (m : PositionMask j) (w : DerivativeWord2 j) :
    ∃ R : ℝ → Lp F 2 (volume : Measure (Vec 2)), MemLp R 2 μ ∧
      ∀ᵐ t ∂μ, R t =ᵐ[volume] multiplicationTerm hj (C t) (U t).toFunction.jet m w := by
  let l : Fin (K + 1) := ⟨maskLeftLength j m,
    Nat.lt_succ_of_le ((maskLeftLength_le j m).trans hj)⟩
  let β : DerivativeWord2 l.val := (maskWordEquiv 2 j m w).1
  let α : JetIndex2 K := maskJetIndex hj m w
  let B := fun t => orderedCoefficientDerivative (C t) l.val β
  have hBc (t : ℝ) : Continuous (B t) := by
    have hh : ContDiff ℝ (Nat.cast l.val : WithTop ℕ∞) (C t) :=
      (hC t).of_le (by exact_mod_cast Nat.le_of_lt_succ l.isLt)
    exact (orderedCoefficientDerivative_contDiff (C t) l.val 0
      (by simpa only [Nat.add_zero] using hh) β).continuous
  have hBb (t : ℝ) (x : Vec 2) : ‖B t x‖ ≤ A l * q x :=
    (orderedCoefficientDerivative_norm_le_array (C t) l.val β x).trans (hb l t x)
  let R := growingCoefficientReadout q hq hq0 B hBc (A l) (hA l) hBb
    (fun t => planeJetReadoutOperator K α (U t))
  have hR : MemLp R 2 μ := growingCoefficient_planeJet_time_memLp q hq hq0 B hBc
    (hCm l β) (A l) (hA l) hBb μ U hU α (he α)
  refine ⟨R, hR, ?_⟩
  have hme := chartScalarEnergy_stationary_time_aemeasurable (E := E)
    (fun x => q x ^ 2) (hq.pow 2) (fun x => sq_pos_of_pos (hq0 x)) μ
    (fun t => planeJetReadoutOperator K α (U t))
    ((planeJetReadoutOperator (E := E) K α).comp_memLp' hU)
  filter_upwards [ae_lt_top' hme (he α)] with t ht
  exact growingCoefficient_planeJet_ae_raw q hq hq0 B hBc (A l) (hA l) hBb U α t ht.ne
end

end AVRegularity.Weighted
end

section
open Homogenization
namespace AVRegularity.Weighted

/-! Polynomial moment square roots dominate the unweighted norm. -/

theorem planeMomentSquareRoot_one_le (n : ℕ) (ϖ : ℝ) (zc x : Vec 2) :
    1 ≤ planeMomentSquareRoot n ϖ zc x := by
  have hb : 1 ≤ 1 + ϖ ^ 2 * ((x 0 - zc 0) ^ 2 + (x 1 - zc 1) ^ 2) := le_add_of_nonneg_right (by positivity)
  have hp : 1 ≤ planeMomentPolynomial n ϖ zc x := by
    exact one_le_pow₀ hb
  simpa only [planeMomentSquareRoot, Real.sqrt_one] using! Real.sqrt_le_sqrt hp

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.Weighted

/-! The window source carriers are actual Bochner square-integrable Sobolev functions. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem scalarSobolevTransportSource_memLp {K Kmax : ℕ} {ta tb : ℝ}
    (hK : K ≤ Kmax) (hab : ta ≤ tb)
    (v : ℝ → Vec 2 → Vec 2) (hvm : Measurable (fun p : Set.Icc ta tb × Vec 2 => v p.1 p.2))
    (hv : ∀ t ∈ Set.Icc ta tb, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hV : 0 ≤ V) (ha : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hbv : ∀ t ∈ Set.Icc ta tb, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc ta tb, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (W : ℝ → PlaneHk Set.univ (K + 1) E)
    (hW : MemLp W 2 (volume.restrict (Set.Icc ta tb))) :
    MemLp (scalarSobolevTransportSource hK hab v hv V strain B lam hbv hjets W) 2
      (volume.restrict (Set.Icc ta tb)) := by
  exact (planeTransportCarrier_memLp _ hK (planeIntervalCoefficient ta tb hab v)
    (planeIntervalCoefficient_measurable ta tb hab v hvm)
    (fun t => hv _ (Set.projIcc ta tb hab t).property) V strain B lam
    (fun t => hbv _ (Set.projIcc ta tb hab t).property)
    (fun l => driftEnvelope_nonneg hV ha hB hlam l.val)
    (fun t => hjets _ (Set.projIcc ta tb hab t).property) W hW).neg

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Assemble the actual measurable time curves of the complete ordered product jet. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

omit [BorelSpace F] [CompleteSpace F] in
theorem exists_growing_multiplicationRawJet_time_readout {K : ℕ}
    (q : Vec 2 → ℝ) (hq : Continuous q) (hq0 : ∀ x, 0 < q x)
    (C : ℝ → Vec 2 → E →L[ℝ] F) (hC : ∀ t, ContDiff ℝ (K : ℕ) (C t))
    (hCm : ∀ l : Fin (K + 1), ∀ β : DerivativeWord2 l.val,
      Measurable (Function.uncurry (fun t => orderedCoefficientDerivative (C t) l.val β)))
    (A : Fin (K + 1) → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ l t x, ‖coefficientDerivativeArray (C t) l.val x‖ ≤ A l * q x)
    (μ : Measure ℝ) (U : ℝ → PlaneHk Set.univ K E) (hU : MemLp U 2 μ)
    (he : ∀ α, (∫⁻ t, chartScalarEnergy (fun x => q x ^ 2)
      (planeJetReadoutOperator K α (U t)) ∂μ) ≠ ⊤) :
    ∃ R : JetIndex2 K → ℝ → Lp F 2 (volume : Measure (Vec 2)),
      (∀ α, MemLp (R α) 2 μ) ∧
      ∀ᵐ t ∂μ, ∀ α, R α t =ᵐ[volume] multiplicationRawJet (C t) (U t).toFunction.jet α := by
  classical
  have hex (α : JetIndex2 K) (m : PositionMask α.1.val) :=
    exists_growing_multiplicationTerm_time_readout (Nat.le_of_lt_succ α.1.isLt)
      q hq hq0 C hC hCm A hA hb μ U hU he m α.2
  choose R hR hRae using hex
  refine ⟨fun α t => ∑ m, R α m t, ?_, ?_⟩
  · intro α
    exact memLp_finsetSum Finset.univ (fun m _ => hR α m)
  · have ht : ∀ᵐ t ∂μ, ∀ α m, R α m t =ᵐ[volume]
        multiplicationTerm (Nat.le_of_lt_succ α.1.isLt) (C t) (U t).toFunction.jet m α.2 :=
      ae_all_iff.mpr (fun α => ae_all_iff.mpr (fun m => hRae α m))
    filter_upwards [ht] with t ht
    intro α
    have hs := eventuallyEq_sum (s := Finset.univ) (fun m _ => ht α m)
    apply (Lp.coeFn_finsetSum _ _).trans
    filter_upwards [hs] with x hx
    simpa only [multiplicationRawJet, Finset.sum_apply] using hx

end AVRegularity.Weighted
end

section
open Homogenization
namespace AVRegularity.Weighted

/-! Polynomial growth on the plane consumes the corresponding number of source moments. -/

theorem plane_norm_sq_le_twice_coordinate_sq (x : Vec 2) :
    ‖x‖ ^ 2 ≤ 2 * (x 0 ^ 2 + x 1 ^ 2) := by
  have hn : ‖x‖ ≤ |x 0| + |x 1| := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro k
    fin_cases k
    · simpa only [Real.norm_eq_abs] using! le_add_of_nonneg_right (abs_nonneg (x 1))
    · simpa only [Real.norm_eq_abs] using! le_add_of_nonneg_left (abs_nonneg (x 0))
  have hs := pow_le_pow_left₀ (norm_nonneg x) hn 2
  have hd := sq_nonneg (|x 0| - |x 1|)
  have h0 := sq_abs (x 0)
  have h1 := sq_abs (x 1)
  nlinarith only [hs, hd, h0, h1]

theorem plane_norm_polynomial_base_bound (ϖ : ℝ) (hϖ : 0 < ϖ) (x : Vec 2) :
    (1 + ‖x‖) ^ 2 ≤ (2 + 4 / ϖ ^ 2) *
      (1 + ϖ ^ 2 * (x 0 ^ 2 + x 1 ^ 2)) := by
  have hs := plane_norm_sq_le_twice_coordinate_sq x
  have he : (2 + 4 / ϖ ^ 2) * (1 + ϖ ^ 2 * (x 0 ^ 2 + x 1 ^ 2)) =
      2 + 4 * (x 0 ^ 2 + x 1 ^ 2) + 2 * ϖ ^ 2 * (x 0 ^ 2 + x 1 ^ 2) + 4 / ϖ ^ 2 := by
    field_simp
    ring
  rw [he]
  have hprod : 0 ≤ 2 * ϖ ^ 2 * (x 0 ^ 2 + x 1 ^ 2) := by positivity
  have hinv : 0 ≤ 4 / ϖ ^ 2 := by positivity
  nlinarith only [hs, sq_nonneg (1 - ‖x‖), hprod, hinv]

theorem plane_polynomial_moment_absorption (ϖ : ℝ) (hϖ : 0 < ϖ) (n r : ℕ) (x : Vec 2) :
    (1 + ‖x‖) ^ r * planeMomentSquareRoot n ϖ 0 x ≤
      (Real.sqrt (2 + 4 / ϖ ^ 2)) ^ r * planeMomentSquareRoot (n + r) ϖ 0 x := by
  have hc : 0 ≤ 2 + 4 / ϖ ^ 2 := by positivity
  have hh := polynomial_square_root_moment_absorption (1 + ‖x‖)
    (1 + ϖ ^ 2 * (x 0 ^ 2 + x 1 ^ 2)) (Real.sqrt (2 + 4 / ϖ ^ 2))
    (by positivity) (by positivity) (Real.sqrt_nonneg _)
    (by rw [Real.sq_sqrt hc]; exact plane_norm_polynomial_base_bound ϖ hϖ x) n r
  simpa only [planeMomentSquareRoot, planeMomentPolynomial, Pi.zero_apply, sub_zero] using hh

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Descending slots place every jet of a positive derivative source in the weighted production. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def derivativeSourceOperator {K L r : ℕ} (hKL : K + r ≤ L + 1)
    (w : DerivativeWord2 r) : PlaneHk Set.univ (L + 1) E →L[ℝ] PlaneHk Set.univ K E :=
  (derivativePlaneHk w).comp (truncatePlaneHk hKL)

theorem derivativeSourceOperator_weighted_jet_integral_ne_top {K L r : ℕ}
    (hKL : K + r ≤ L + 1) (hr : 0 < r) (w : DerivativeWord2 r)
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ) (hρ : 0 < ρ) (μ : Measure ℝ)
    (W : ℝ → PlaneHk Set.univ (L + 1) E)
    (he : (∫⁻ t, weightedGradFactorialNormSq n ϖ zc ρ L (W t) ∂μ) ≠ ⊤)
    (α : JetIndex2 K) :
    (∫⁻ t, chartScalarEnergy (fun x => (planeMomentSquareRoot n ϖ zc x) ^ 2)
      (planeJetReadoutOperator K α (derivativeSourceOperator hKL w (W t))) ∂μ) ≠ ⊤ := by
  let β : JetIndex2 (L + 1) := truncateJetIndex hKL (prefixJetIndex w α)
  have hh := weighted_production_positive_jet_integral_ne_top n ϖ zc ρ hρ μ W he β
    (by change 0 < r + α.1.val; omega)
  simpa only [planeMomentSquareRoot_sq, derivativeSourceOperator, ContinuousLinearMap.comp_apply,
    planeJetReadoutOperator_apply, derivativePlaneHk_apply, truncatePlaneHk_apply, β] using hh
end

/-! A weighted Leibniz output term is L2 in time when the source moments absorb coefficient growth. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

omit [BorelSpace F] [CompleteSpace F] in
theorem exists_weighted_multiplicationTerm_time_readout {K j : ℕ} (hj : j ≤ K)
    (q : Vec 2 → ℝ) (hq : Continuous q) (hq0 : ∀ x, 0 < q x)
    (p : Vec 2 → ℝ) (hp : Continuous p) (hp0 : ∀ x, 0 ≤ p x)
    (C : ℝ → Vec 2 → E →L[ℝ] F) (hC : ∀ t, ContDiff ℝ (K : ℕ) (C t))
    (hCm : ∀ l : Fin (K + 1), ∀ β : DerivativeWord2 l.val,
      Measurable (Function.uncurry (fun t => orderedCoefficientDerivative (C t) l.val β)))
    (A : Fin (K + 1) → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ l t x, p x * ‖coefficientDerivativeArray (C t) l.val x‖ ≤ A l * q x)
    (μ : Measure ℝ) (U : ℝ → PlaneHk Set.univ K E) (hU : MemLp U 2 μ)
    (he : ∀ α, (∫⁻ t, chartScalarEnergy (fun x => q x ^ 2)
      (planeJetReadoutOperator K α (U t)) ∂μ) ≠ ⊤)
    (m : PositionMask j) (w : DerivativeWord2 j) :
    ∃ R : ℝ → Lp F 2 (volume : Measure (Vec 2)), MemLp R 2 μ ∧
      ∀ᵐ t ∂μ, R t =ᵐ[volume] fun x => p x •
        multiplicationTerm hj (C t) (U t).toFunction.jet m w x := by
  let l : Fin (K + 1) := ⟨maskLeftLength j m,
    Nat.lt_succ_of_le ((maskLeftLength_le j m).trans hj)⟩
  let β : DerivativeWord2 l.val := (maskWordEquiv 2 j m w).1
  let α : JetIndex2 K := maskJetIndex hj m w
  let B := fun t x => p x • orderedCoefficientDerivative (C t) l.val β x
  have hBc (t : ℝ) : Continuous (B t) := by
    have hh : ContDiff ℝ (Nat.cast l.val : WithTop ℕ∞) (C t) :=
      (hC t).of_le (by exact_mod_cast Nat.le_of_lt_succ l.isLt)
    exact hp.smul (orderedCoefficientDerivative_contDiff (C t) l.val 0
      (by simpa only [Nat.add_zero] using hh) β).continuous
  have hBm : Measurable (Function.uncurry B) :=
    (hp.measurable.comp measurable_snd).smul (hCm l β)
  have hBb (t : ℝ) (x : Vec 2) : ‖B t x‖ ≤ A l * q x := by
    rw [norm_smul, Real.norm_of_nonneg (hp0 x)]
    exact (mul_le_mul_of_nonneg_left
      (orderedCoefficientDerivative_norm_le_array (C t) l.val β x) (hp0 x)).trans (hb l t x)
  let R := growingCoefficientReadout q hq hq0 B hBc (A l) (hA l) hBb
    (fun t => planeJetReadoutOperator K α (U t))
  have hR : MemLp R 2 μ := growingCoefficient_planeJet_time_memLp q hq hq0 B hBc hBm
    (A l) (hA l) hBb μ U hU α (he α)
  refine ⟨R, hR, ?_⟩
  have hme := chartScalarEnergy_stationary_time_aemeasurable (E := E)
    (fun x => q x ^ 2) (hq.pow 2) (fun x => sq_pos_of_pos (hq0 x)) μ
    (fun t => planeJetReadoutOperator K α (U t))
    ((planeJetReadoutOperator (E := E) K α).comp_memLp' hU)
  filter_upwards [ae_lt_top' hme (he α)] with t ht
  exact growingCoefficient_planeJet_ae_raw q hq hq0 B hBc (A l) (hA l) hBb U α t ht.ne
end

end AVRegularity.Weighted
end
end
end
