-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Weighted.WeightedMultiplicationTermTime
import AVRegularity.CoupledEnergyPlane.Transport.CarrierTransport

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set Filter
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped Topology
namespace AVRegularity.Weighted

/-! The actual bounded-weight energy estimate on the whole plane, after spatial cutoff removal. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeWeak_clipped_value_energy_gronwall
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
    (B : ℝ) (hB : 0 < B) (hF : MemLp F 2 (volume.restrict (Icc a b)))
    (hH : MemLp H 2 (volume.restrict (Icc a b))) :
    ∀ t ∈ Icc a b,
      (∫ x, clipWeight B (W.W m t x) * ‖u t x‖ ^ 2) +
      (∫ s in a..t, ∫ x, clipWeight B (W.W m s x) *
        ‖(WithLp.toLp 2 (fun i => planeH1GradientOperator (E := E) (slice s) i x) :
          PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) ≤
      ((∫ x, clipWeight B (W.W m a x) * ‖u a x‖ ^ 2) +
        8 * (∫ s in a..b, ∫ x, clipWeight B (W.W m s x) *
          ‖(WithLp.toLp 2 (fun i => F s i x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) +
        2 * (∫ s in a..b, ∫ x, clipWeight B (W.W m s x) * (‖H s x‖ * ‖u s x‖))) *
        Real.exp (18 * W.lam m * (t - a)) := by
  obtain ⟨χ, Cχ, hCχ, hχ, hχrange, hχlim, hdχ⟩ :=
    AVRegularity.CoupledEnergyPlane.Transport.exists_expanding_smooth_cutoffs
  let q := fun t x => clipWeight B (W.W m t x)
  let force := fun t => ∫ x, q t x *
    ‖(WithLp.toLp 2 (fun i => F t i x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2
  let val := fun t => ∫ x, q t x * (‖H t x‖ * ‖u t x‖)
  let valc := fun n t => ∫ x, (χ n x ^ 2 * q t x) * (‖H t x‖ * ‖u t x‖)
  let mass := fun t => ∫ x, q t x * ‖u t x‖ ^ 2
  let η := fun n : ℕ => ((n : ℝ) + 1)⁻¹ * Cχ
  let c := fun n => 4096 * η n ^ 2 + 16 * M * η n
  have hu : MemLp u 2 (volume.restrict (Icc a b)) :=
    (memLp_congr_ae h.agrees).2 ((planeHkValueOperator (E := E) 1).comp_memLp' h.state)
  have hfint := intervalIntegrable_of_integrable_Icc hab
    (chartWeights_clipped_finite_time_integrable W m hm B hB _ F hF)
  have hmint := intervalIntegrable_of_integrable_Icc hab
    (chartWeights_clipped_scalar_time_integrable W m hm B hB _ u hu)
  obtain ⟨hqc, hqm, hqb⟩ := chartWeights_clipped_time_coefficient W m hm B hB
  have hvint := intervalIntegrable_of_integrable_Icc hab
    (weighted_spatial_value_product_time_integrable q hqc hqm hB.le hqb H u hH hu)
  have hH' : MemLp H 2 (volume.restrict (Ioc a b)) :=
    hH.mono_measure (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)
  have hu' : MemLp u 2 (volume.restrict (Ioc a b)) :=
    hu.mono_measure (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)
  have hvlim := value_product_spatial_cutoff_time_tendsto χ (fun n => (hχ n).1.continuous)
    hχrange hχlim q hqc hqm hB.le hqb (fun s x => (clipWeight_pos hB (W.pos m hm s x)).le)
    (volume.restrict (Ioc a b)) H u hH' hu'
  have hvlim' : Tendsto (fun n => ∫ s in a..b, valc n s) atTop
      (𝓝 (∫ s in a..b, val s)) := by
    simpa only [intervalIntegral.integral_of_le hab] using hvlim
  have hvnc n := intervalIntegrable_of_integrable_Icc hab
    (chartWeights_clipped_cutoff_value_product_integrable W m hm B hB (χ n)
      (hχ n).1.continuous (fun x => (hχrange n x).1) (fun x => (hχrange n x).2) _ H u hH hu)
  have hη n : 0 ≤ η n := by dsimp only [η]; positivity
  have hχ2 n : ContDiff ℝ 2 (χ n) := (hχ n).1.of_le (by simp)
  have hgr n := planeWeak_clipped_compact_value_gronwall a b hab v hv hdiv M hM hvb
    G hG g hg4 hGnear hGs t₀ S ϖ zc N m Cw W hm ha hb u slice F H h (χ n) (hχ2 n) (hχ n).2
    (fun x => (hχrange n x).1) (fun x => (hχrange n x).2) (η n) (hη n) (hdχ n) B hB hF hH
  have hqint t : Integrable (fun x => q t x * ‖u t x‖ ^ 2) volume :=
    bounded_scalar_Lp_normSq_integrable (u t) (q t)
      (chartWeights_clipped_spatial_regularity W m hm t B hB).1.continuous.aestronglyMeasurable
      (Eventually.of_forall (fun x => by
        rw [Real.norm_of_nonneg (clipWeight_pos hB (W.pos m hm t x)).le]
        exact clipWeight_le_bound hB (W.pos m hm t x)))
  have henergy t : Tendsto (fun n => ∫ x, χ n x ^ 2 * q t x * ‖u t x‖ ^ 2) atTop
      (𝓝 (mass t)) := by
    have hh := integral_spatial_cutoff_tendsto χ (fun x => q t x * ‖u t x‖ ^ 2)
      (fun n => (hχ n).1.continuous.aestronglyMeasurable) hχrange hχlim (hqint t)
    convert hh using 1
    funext n
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by ring)
  have hclim : Tendsto c atTop (𝓝 0) := cutoff_error_rate_tendsto_zero
  intro t ht
  have hsub : Ioc a t ⊆ Icc a b := Ioc_subset_Icc_self.trans (Icc_subset_Icc le_rfl ht.2)
  have hdu : MemLp (fun s => planeH1GradientOperator (E := E) (slice s)) 2
      (volume.restrict (Ioc a t)) :=
    ((planeH1GradientOperator (E := E)).comp_memLp' h.state).mono_measure
      (Measure.restrict_mono hsub le_rfl)
  have hdlim := finite_energy_spatial_cutoff_time_tendsto χ (fun n => (hχ n).1.continuous)
    hχrange hχlim q hqc hqm hB.le hqb (fun s x => (clipWeight_pos hB (W.pos m hm s x)).le)
    (volume.restrict (Ioc a t)) (fun s => planeH1GradientOperator (E := E) (slice s)) hdu
  have hdlim' : Tendsto (fun n => ∫ s in a..t, ∫ x, χ n x ^ 2 * q s x *
      ‖(WithLp.toLp 2 (fun i => planeH1GradientOperator (E := E) (slice s) i x) :
        PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) atTop
      (𝓝 (∫ s in a..t, ∫ x, q s x * ‖(WithLp.toLp 2
        (fun i => planeH1GradientOperator (E := E) (slice s) i x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2)) := by
    simpa only [intervalIntegral.integral_of_le ht.1] using hdlim
  have hl := (henergy t).add hdlim'
  have hsource := ((tendsto_const_nhds :
    Tendsto (fun _ : ℕ => 8 * (∫ s in a..b, force s)) atTop
      (𝓝 (8 * (∫ s in a..b, force s)))).add
    (hclim.mul_const (∫ s in a..b, mass s))).add (hvlim'.const_mul 2)
  have hr := ((henergy a).add hsource).mul_const
    (Real.exp (18 * W.lam m * (t - a)))
  have hbnd n := hgr n t ht
  have hrhs n : (∫ s in a..b, 8 * force s + c n * mass s + 2 * valc n s) =
      8 * (∫ s in a..b, force s) + c n * (∫ s in a..b, mass s) +
        2 * (∫ s in a..b, valc n s) := by
    rw [intervalIntegral.integral_add ((hfint.const_mul 8).add (hmint.const_mul (c n))) ((hvnc n).const_mul 2),
      intervalIntegral.integral_add (hfint.const_mul 8) (hmint.const_mul (c n)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  apply le_of_tendsto_of_tendsto hl (by simpa only [zero_mul, add_zero, add_assoc] using hr)
  exact Eventually.of_forall (fun n => by
    have hh := hbnd n
    change _ ≤ ((_ + ∫ s in a..b, 8 * force s + c n * mass s + 2 * valc n s) * _) at hh
    rw [hrhs] at hh
    simpa only [add_assoc] using hh)

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Weighted actual product jets have genuine L2 time representatives. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

omit [BorelSpace F] [CompleteSpace F] in
theorem exists_weighted_multiplicationRawJet_time_readout {K : ℕ}
    (q : Vec 2 → ℝ) (hq : Continuous q) (hq0 : ∀ x, 0 < q x)
    (p : Vec 2 → ℝ) (hp : Continuous p) (hp0 : ∀ x, 0 ≤ p x)
    (C : ℝ → Vec 2 → E →L[ℝ] F) (hC : ∀ t, ContDiff ℝ (K : ℕ) (C t))
    (hCm : ∀ l : Fin (K + 1), ∀ β : DerivativeWord2 l.val,
      Measurable (Function.uncurry (fun t => orderedCoefficientDerivative (C t) l.val β)))
    (A : Fin (K + 1) → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ l t x, p x * ‖coefficientDerivativeArray (C t) l.val x‖ ≤ A l * q x)
    (μ : Measure ℝ) (U : ℝ → PlaneHk Set.univ K E) (hU : MemLp U 2 μ)
    (he : ∀ α, (∫⁻ t, chartScalarEnergy (fun x => q x ^ 2)
      (planeJetReadoutOperator K α (U t)) ∂μ) ≠ ⊤) :
    ∃ R : JetIndex2 K → ℝ → Lp F 2 (volume : Measure (Vec 2)),
      (∀ α, MemLp (R α) 2 μ) ∧
      ∀ᵐ t ∂μ, ∀ α, R α t =ᵐ[volume] fun x =>
        p x • multiplicationRawJet (C t) (U t).toFunction.jet α x := by
  classical
  have hex (α : JetIndex2 K) := exists_finite_time_l2_readout_sum μ volume
    (fun (m : PositionMask α.1.val) t x => p x •
      multiplicationTerm (Nat.le_of_lt_succ α.1.isLt) (C t)
        (U t).toFunction.jet m α.2 x)
    (fun m => exists_weighted_multiplicationTerm_time_readout
      (Nat.le_of_lt_succ α.1.isLt) q hq hq0 p hp hp0 C hC hCm A hA hb μ U hU he m α.2)
  choose R hR hRae using hex
  refine ⟨R, hR, ?_⟩
  filter_upwards [ae_all_iff.mpr hRae] with t ht
  intro α
  filter_upwards [ht α] with x hx
  simpa only [multiplicationRawJet, Finset.smul_sum] using hx
end

/-! Finite sums of genuine Sobolev forcing curves retain their moment source budgets. -/

section
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [Fintype ι]

theorem finite_weighted_sobolev_time_sum {K : ℕ}
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ) (hρ : 0 < ρ) (μ : Measure ℝ)
    (U : ι → ℝ → PlaneHk Set.univ K E) (hU : ∀ i, MemLp (U i) 2 μ)
    (he : ∀ i, (∫⁻ t, weightedFactorialNormSq n ϖ zc ρ K (U i t) ∂μ) ≠ ⊤) :
    MemLp (fun t => ∑ i, U i t) 2 μ ∧
      (∫⁻ t, weightedFactorialNormSq n ϖ zc ρ K (∑ i, U i t) ∂μ) ≠ ⊤ := by
  classical
  have hsum : MemLp (fun t => ∑ i, U i t) 2 μ :=
    memLp_finsetSum (f := U) Finset.univ (fun i _ => hU i)
  refine ⟨hsum, ?_⟩
  have hcomp (i : ι) (α : JetIndex2 K) :
      (∫⁻ t, chartScalarEnergy (planeMomentPolynomial n ϖ zc)
        (planeJetReadoutOperator K α (U i t)) ∂μ) ≠ ⊤ := by
    have hi := he i
    simp only [weightedFactorialNormSq_stored_readout, storedChartFactorialEnergy] at hi
    exact finite_integrated_weighted_sum_component μ
      (fun α : JetIndex2 K => factorialWeight ρ α.1.val)
      (fun α => factorialWeight_pos_of_radius_pos ρ hρ α.1.val) _ hi α
  apply integrated_weightedFactorialNormSq_ne_top n ϖ zc ρ μ _ hsum
  intro α
  have hh := integrated_chart_energy_finite_sum_ne_top (planeMomentSquareRoot n ϖ zc)
    (planeMomentSquareRoot_continuous n ϖ zc) (planeMomentSquareRoot_pos n ϖ zc)
    μ (fun i t => planeJetReadoutOperator K α (U i t))
    (fun i => (planeJetReadoutOperator (E := E) K α).comp_memLp' (hU i))
    (fun i => by simpa only [planeMomentSquareRoot_sq] using hcomp i α)
  simpa only [map_sum] using hh
end

/-! The zeroth product readout is the literal scalar coefficient times the source derivative. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

theorem scalar_product_value_readout_ae {K : ℕ} (U : PlaneHk Set.univ K E)
    (V : PlaneHk Set.univ K F) (c : Vec 2 → ℝ) (T : E →L[ℝ] F)
    (hV : planeJetReadoutOperator K (valueIndex2 K) V =ᵐ[volume]
      multiplicationRawJet (fun x => c x • T) U.toFunction.jet (valueIndex2 K)) :
    planeJetReadoutOperator K (valueIndex2 K) V =ᵐ[volume]
      fun x => c x • T (planeJetReadoutOperator K (valueIndex2 K) U x) := by
  filter_upwards [hV, planeJetReadout_ae_raw U (valueIndex2 K)] with x hx hu
  rw [hx, multiplicationRawJet_value, ← hu]
  rfl

theorem derivativeSourceOperator_value_readout {K L r : ℕ} (hKL : K + r ≤ L + 1)
    (w : DerivativeWord2 r) (U : PlaneHk Set.univ (L + 1) E) :
    planeJetReadoutOperator K (valueIndex2 K) (derivativeSourceOperator hKL w U) =
      planeJetReadoutOperator (L + 1)
        (truncateJetIndex hKL (prefixJetIndex w (valueIndex2 K))) U := by
  simp only [planeJetReadoutOperator_apply, derivativeSourceOperator,
    ContinuousLinearMap.comp_apply, derivativePlaneHk_apply, truncatePlaneHk_apply]
end

end AVRegularity.Weighted
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! The derivative-source value index is the literal input word index. -/

def sourceWordIndex {K L r : ℕ} (hKL : K + r ≤ L + 1) (w : DerivativeWord2 r) :
    JetIndex2 (L + 1) := ⟨⟨r, by omega⟩, w⟩

theorem derivative_source_value_index {K L r : ℕ} (hKL : K + r ≤ L + 1)
    (w : DerivativeWord2 r) :
    truncateJetIndex hKL (prefixJetIndex w (valueIndex2 K)) = sourceWordIndex hKL w := by
  simp only [truncateJetIndex, prefixJetIndex, valueIndex2, valueIndex, sourceWordIndex]
  congr 1
  funext i
  change Fin.addCases w Fin.elim0 (Fin.castAdd 0 i) = w i
  exact Fin.addCases_left i

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Finite Sobolev forcing sums retain their literal flux representatives. -/

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [Fintype ι]

theorem finite_weighted_sobolev_flux_sum {K : ℕ}
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ) (hρ : 0 < ρ) (μ : Measure ℝ)
    (U : ι → ℝ → PlaneHk Set.univ K E) (hU : ∀ i, MemLp (U i) 2 μ)
    (he : ∀ i, (∫⁻ t, weightedFactorialNormSq n ϖ zc ρ K (U i t) ∂μ) ≠ ⊤)
    (f : ι → ℝ → Vec 2 → E)
    (hf : ∀ i, ∀ᵐ t ∂μ, planeJetReadoutOperator K (valueIndex2 K) (U i t) =ᵐ[volume] f i t) :
    ∃ V : ℝ → PlaneHk Set.univ K E, MemLp V 2 μ ∧
      (∫⁻ t, weightedFactorialNormSq n ϖ zc ρ K (V t) ∂μ) ≠ ⊤ ∧
      ∀ᵐ t ∂μ, planeJetReadoutOperator K (valueIndex2 K) (V t) =ᵐ[volume]
        fun x => ∑ i, f i t x := by
  classical
  obtain ⟨hV, hVe⟩ := finite_weighted_sobolev_time_sum n ϖ zc ρ hρ μ U hU he
  refine ⟨fun t => ∑ i, U i t, hV, hVe, ?_⟩
  filter_upwards [ae_all_iff.mpr hf] with t ht
  rw [map_sum]
  apply (Lp.coeFn_finsetSum _ _).trans
  have hh := eventuallyEq_sum (s := Finset.univ) (fun i _ => ht i)
  filter_upwards [hh] with x hx
  simpa only [Finset.sum_apply] using hx

end AVRegularity.Weighted
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Admissible coupled orders provide the exact positive derivative source reserve. -/

variable {σ : Type*}

theorem admissible_letter_source_reserve (κ : σ → ℕ) (D : ℕ) (a b : σ)
    (o : admissibleOrders κ D a b) : κ a + (o.1 - 1) ≤ κ b + 1 := by
  have hh := Finset.mem_filter.mp o.2
  have ho := Finset.mem_Icc.mp hh.1
  omega

def admissibleLetterSourceIndex (κ : σ → ℕ) (D : ℕ) (a b : σ)
    (o : admissibleOrders κ D a b) (w : DerivativeWord2 (o.1 - 1)) :
    JetIndex2 (κ b + 1) := sourceWordIndex (admissible_letter_source_reserve κ D a b o) w

def admissibleLetterOrder (κ : σ → ℕ) (D : ℕ) (a b : σ)
    (o : admissibleOrders κ D a b) : Finset.Icc 2 D :=
  ⟨o.1, (Finset.mem_filter.mp o.2).1⟩

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! The genuine growing-coefficient weak Sobolev product has the required time integrability. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

theorem growingPlaneHkCurve_time_memLp {K : ℕ}
    (q : Vec 2 → ℝ) (hq : Continuous q) (hq0 : ∀ x, 0 < q x)
    (C : ℝ → Vec 2 → E →L[ℝ] F) (hC : ∀ t, ContDiff ℝ (K : ℕ) (C t))
    (hCm : ∀ l : Fin (K + 1), ∀ β : DerivativeWord2 l.val,
      Measurable (Function.uncurry (fun t => orderedCoefficientDerivative (C t) l.val β)))
    (A : Fin (K + 1) → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ l t x, ‖coefficientDerivativeArray (C t) l.val x‖ ≤ A l * q x)
    (μ : Measure ℝ) (U : ℝ → PlaneHk Set.univ K E) (hU : MemLp U 2 μ)
    (he : ∀ α, (∫⁻ t, chartScalarEnergy (fun x => q x ^ 2)
      (planeJetReadoutOperator K α (U t)) ∂μ) ≠ ⊤) :
    MemLp (growingPlaneHkCurve q hq (fun x => (hq0 x).le) C hC A hA hb U) 2 μ := by
  obtain ⟨R, hR, hRae⟩ := exists_growing_multiplicationRawJet_time_readout
    q hq hq0 C hC hCm A hA hb μ U hU he
  have hfin := planeJet_energy_ae_ne_top q hq hq0 μ U hU he
  apply planeHk_time_memLp_of_readouts μ
  intro α
  apply (hR α).ae_eq
  filter_upwards [hfin, hRae] with t ht hrt
  apply Lp.ext
  exact (hrt α).trans
    (growingPlaneHkCurve_readout_ae q hq (fun x => (hq0 x).le) C hC A hA hb U t ht α).symm

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

theorem weightedDriftValueSource_absorption {K Kmax : ℕ} {U : Set (Vec 2)}
    (hK : K ≤ Kmax) (hU : MeasurableSet U)
    (ρ a B lam ν V : ℝ) (hρ : 0 < ρ) (ha : 0 ≤ a) (hB : 1 ≤ B)
    (hlam : 0 < lam) (hν : 0 < ν) (hV : 0 ≤ V)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : a * B * ρ ^ 2 ≤ ν / 8)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hvb : ∀ x, ‖v x‖ ≤ V)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤
        a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (q : Vec 2 → ℝ) (hq : Continuous q) (hq0 : ∀ x, 0 ≤ q x)
    (M : ℝ) (hb : ∀ x, q x ≤ M) (D : RawJet2 (K + 1) E) (hD : JetMemL2On U D) :
    (∑ j : Fin (K + 1), factorialWeight ρ j.val *
      (∑ w : DerivativeWord2 j.val, ∫ x, q x *
        (‖planeDriftCommutatorTerm (Nat.le_of_lt_succ j.isLt) v D w x‖ *
          ‖D ⟨⟨j.val, by omega⟩, w⟩ x‖) ∂volume.restrict U)) ≤
      (ν / 4) * (∑ j : Fin (K + 1), factorialWeight ρ j.val *
        (∫ x, q x * (∑ w : DerivativeWord2 j.val,
          ‖(WithLp.toLp 2 (fun k : Fin 2 =>
            D ⟨⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩, Fin.snoc w k⟩ x) :
            PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) ∂volume.restrict U)) := by
  obtain ⟨hs, hsbnd, hsquare⟩ := boundedWeightRoot_properties q hq hq0 M hb
  have h := scaledDriftValueSource_absorption hK hU ρ a B lam ν V hρ ha hB hlam hν hV hsmall hstrain v hv hvb hjets
    (fun x => Real.sqrt (q x)) hs (Real.sqrt_nonneg _) hsbnd D hD
  rw [scaledRawJet_gradFactorialNormSq] at h
  simp_rw [hsquare] at h
  exact h

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! The actual weighted metric commutator has a small factorial source energy at a reduced radius. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

theorem weightedMetricFluxSource_energy_le {K : ℕ} {U : Set (Vec 2)}
    (ρ δ g : ℝ) (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ) (hg : 0 ≤ g) (hscale : ρ * δ ≤ 1)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ k a, ContDiff ℝ (K : ℕ) (fun x => G x k a))
    (CG : ℕ → ℝ)
    (hbfull : ∀ (l : Fin (K + 1)) x k a,
      ‖iteratedFDeriv ℝ l.val (fun y => G y k a) x‖ ≤ metricEntryEnvelope CG g δ l.val)
    (hb : ∀ l, 1 ≤ l → l ≤ K → ∀ x k a,
      ‖iteratedFDeriv ℝ l (fun y => G y k a) x‖ ≤ CG l * g * δ ^ l)
    (q : Vec 2 → ℝ) (hq : Continuous q) (hq0 : ∀ x, 0 ≤ q x)
    (C : ℝ) (hsb : ∀ x, q x ≤ C) (D : RawJet2 (K + 1) E) (hD : JetMemL2On U D) :
    (∑ j : Fin (K + 1), factorialWeight ρ j.val *
      (∑ w : DerivativeWord2 j.val, ∫ x, q x *
        ‖metricCommutatorTerm (Nat.le_of_lt_succ j.isLt) G D w x‖ ^ 2 ∂volume.restrict U)) ≤
      (metricRadiusConstant K CG * g * (ρ * δ)) ^ 2 * (∑ j : Fin (K + 1), factorialWeight ρ j.val *
        (∫ x, q x * (∑ w : DerivativeWord2 j.val,
          ‖(WithLp.toLp 2 (fun k : Fin 2 =>
            D ⟨⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩, Fin.snoc w k⟩ x) :
            PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) ∂volume.restrict U)) := by
  obtain ⟨hs, hsbnd, hsquare⟩ := boundedWeightRoot_properties q hq hq0 C hsb
  have h := scaledMetricFluxSource_energy_le ρ δ g hρ hδ hg hscale G hG CG hbfull hb
    (fun x => Real.sqrt (q x)) hs (Real.sqrt_nonneg _) hsbnd D hD
  rw [scaledRawJet_gradFactorialNormSq] at h
  simp_rw [hsquare] at h
  exact h

end AVRegularity.Weighted
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Literal scalar polynomial growth is absorbed by exactly its degree in moments. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem scalar_operator_moment_array_bound (n r j : ℕ) (ϖ : ℝ) (hϖ : 0 < ϖ)
    (c : Vec 2 → ℝ) (hc : ContDiff ℝ (j : ℕ) c) (T : E →L[ℝ] F)
    (A : ℝ) (hA : 0 ≤ A)
    (hb : ∀ x, ‖iteratedFDeriv ℝ j c x‖ ≤ A * (1 + ‖x‖) ^ r) (x : Vec 2) :
    planeMomentSquareRoot n ϖ 0 x *
      ‖coefficientDerivativeArray (fun y => c y • T) j x‖ ≤
      ((Fintype.card (DerivativeWord2 j) : ℝ) * (A * ‖T‖) *
        (Real.sqrt (2 + 4 / ϖ ^ 2)) ^ r) * planeMomentSquareRoot (n + r) ϖ 0 x := by
  have hp : 0 ≤ planeMomentSquareRoot n ϖ 0 x :=
    (planeMomentSquareRoot_pos n ϖ 0 x).le
  let R := (Fintype.card (DerivativeWord2 j) : ℝ) * (A * ‖T‖)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  calc
    _ ≤ planeMomentSquareRoot n ϖ 0 x *
        ((Fintype.card (DerivativeWord2 j) : ℝ) * (‖iteratedFDeriv ℝ j c x‖ * ‖T‖)) :=
      mul_le_mul_of_nonneg_left (scalar_operator_array_norm_le c j hc T x) hp
    _ ≤ planeMomentSquareRoot n ϖ 0 x *
        ((Fintype.card (DerivativeWord2 j) : ℝ) * ((A * (1 + ‖x‖) ^ r) * ‖T‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hb x) (norm_nonneg T)) (by positivity)) hp
    _ = R * ((1 + ‖x‖) ^ r * planeMomentSquareRoot n ϖ 0 x) := by dsimp [R]; ring
    _ ≤ R * ((Real.sqrt (2 + 4 / ϖ ^ 2)) ^ r *
        planeMomentSquareRoot (n + r) ϖ 0 x) :=
      mul_le_mul_of_nonneg_left (plane_polynomial_moment_absorption ϖ hϖ n r x) hR
    _ = _ := by dsimp [R]; ring

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Growing-coefficient Sobolev products retain all output moments absorbed by the input moments. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

theorem growingPlaneHkCurve_weighted_energy_ne_top {K : ℕ}
    (q : Vec 2 → ℝ) (hq : Continuous q) (hq0 : ∀ x, 0 < q x)
    (p : Vec 2 → ℝ) (hp : Continuous p) (hp0 : ∀ x, 0 ≤ p x)
    (C : ℝ → Vec 2 → E →L[ℝ] F) (hC : ∀ t, ContDiff ℝ (K : ℕ) (C t))
    (hCm : ∀ l : Fin (K + 1), ∀ β : DerivativeWord2 l.val,
      Measurable (Function.uncurry (fun t => orderedCoefficientDerivative (C t) l.val β)))
    (A : Fin (K + 1) → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ l t x, ‖coefficientDerivativeArray (C t) l.val x‖ ≤ A l * q x)
    (B : Fin (K + 1) → ℝ) (hB : ∀ l, 0 ≤ B l)
    (hpb : ∀ l t x, p x * ‖coefficientDerivativeArray (C t) l.val x‖ ≤ B l * q x)
    (μ : Measure ℝ) (U : ℝ → PlaneHk Set.univ K E) (hU : MemLp U 2 μ)
    (he : ∀ α, (∫⁻ t, chartScalarEnergy (fun x => q x ^ 2)
      (planeJetReadoutOperator K α (U t)) ∂μ) ≠ ⊤) (α : JetIndex2 K) :
    (∫⁻ t, chartScalarEnergy (fun x => p x ^ 2)
      (planeJetReadoutOperator K α
        (growingPlaneHkCurve q hq (fun x => (hq0 x).le) C hC A hA hb U t)) ∂μ) ≠ ⊤ := by
  obtain ⟨R, hR, hRae⟩ := exists_weighted_multiplicationRawJet_time_readout
    q hq hq0 p hp hp0 C hC hCm B hB hpb μ U hU he
  apply weighted_representative_time_energy_ne_top p μ _ (R α) (hR α)
  have hfin := planeJet_energy_ae_ne_top q hq hq0 μ U hU he
  filter_upwards [hfin, hRae] with t ht hrt
  have hV := growingPlaneHkCurve_readout_ae q hq (fun x => (hq0 x).le)
    C hC A hA hb U t ht α
  filter_upwards [hrt α, hV] with x hx hv
  rw [hx, hv]

end AVRegularity.Weighted
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! The literal admissible forcing between successive levels. -/

variable {ι σ : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

def letterAdmissibleFlux (L : CycleLetter ι h D) (κ : σ → ℕ) (a : σ) (b : ι → σ)
    (v : ι) (lo : ℕ) (X₀ : Vec 2) (δ : ℝ)
    (W : ∀ u, PlaneHk Set.univ (κ (b u) + 1) (h u)) (t : ℝ) (z : Vec 2) :
    PiLp 2 (fun _ : Fin 2 => h v) :=
  ∑ u : ι, ∑ o : admissibleOrders κ D a (b u),
    slowEvalCoefficient (fun f z => taylorSlow lo L.slow f X₀ (δ • z))
      (L.edge v u (admissibleLetterOrder κ D a (b u) o)) t z
      (WithLp.toLp 2 (fun w => (W u).toFunction.jet
        (admissibleLetterSourceIndex κ D a (b u) o w) z))

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

theorem planeDriftValueSource_budget {K Kmax : ℕ} 
    (hK : K ≤ Kmax) 
    (ρ a B lam ν V : ℝ) (hρ : 0 < ρ) (ha : 0 ≤ a) (hB : 1 ≤ B)
    (hlam : 0 < lam) (hν : 0 < ν) (hV : 0 ≤ V)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : a * B * ρ ^ 2 ≤ ν / 8)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (⊤ : ℕ∞) v) (hvb : ∀ x, ‖v x‖ ≤ V)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤
        a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (q : Vec 2 → ℝ) (hq : Continuous q) (hq0 : ∀ x, 0 ≤ q x)
    (M : ℝ) (hb : ∀ x, q x ≤ M) (D : RawJet2 (K + 1) E) (hD : JetMemL2On Set.univ D) :
    (∑ j : Fin (K + 1), factorialWeight ρ j.val *
      (∑ w : DerivativeWord2 j.val, ∫ x, q x *
        (‖planeDriftCommutatorTerm (Nat.le_of_lt_succ j.isLt) v D w x‖ *
          ‖D ⟨⟨j.val, by omega⟩, w⟩ x‖))) ≤
      (ν / 4) * rawWeightedGradientEnergy ρ q D := by
  have h := weightedDriftValueSource_absorption hK MeasurableSet.univ ρ a B lam ν V hρ ha hB hlam hν hV hsmall hstrain v hv hvb hjets q hq hq0 M hb D hD
  simp only [Measure.restrict_univ] at h
  have hqb : ∀ᵐ x ∂volume, ‖q x‖ ≤ M :=
    Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hq0 x)]
      exact hb x)
  rw [rawWeightedGradient_integral_sum ρ q hq.aestronglyMeasurable hqb D hD] at h
  exact h

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! The actual weighted metric commutator has a small factorial source energy at a reduced radius. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

omit [MeasurableSpace E] in
theorem metricForcedFlux_addition_budget {K : ℕ} {U : Set (Vec 2)}
    (ρ δ g : ℝ)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ k a, ContDiff ℝ (K : ℕ) (fun x => G x k a))
    (CG : ℕ → ℝ)
    (hbfull : ∀ (l : Fin (K + 1)) x k a,
      ‖iteratedFDeriv ℝ l.val (fun y => G y k a) x‖ ≤ metricEntryEnvelope CG g δ l.val)
    (q : Vec 2 → ℝ) (hq : Continuous q) (hq0 : ∀ x, 0 ≤ q x)
    (C : ℝ) (hsb : ∀ x, q x ≤ C) (D : RawJet2 (K + 1) E) (hD : JetMemL2On U D)
    (F : RawJet2 K (PiLp 2 (fun _ : Fin 2 => E))) (hF : JetMemL2On U F) :
    (∑ j : Fin (K + 1), factorialWeight ρ j.val *
      (∑ w : DerivativeWord2 j.val, ∫ x, q x *
        ‖metricCommutatorTerm (Nat.le_of_lt_succ j.isLt) G D w x + F ⟨j, w⟩ x‖ ^ 2 ∂volume.restrict U)) ≤
      2 * (∑ j : Fin (K + 1), factorialWeight ρ j.val *
        (∑ w : DerivativeWord2 j.val, ∫ x, q x *
          ‖metricCommutatorTerm (Nat.le_of_lt_succ j.isLt) G D w x‖ ^ 2 ∂volume.restrict U)) + 2 * (∑ j : Fin (K + 1), factorialWeight ρ j.val *
        (∑ w : DerivativeWord2 j.val, ∫ x, q x * ‖F ⟨j, w⟩ x‖ ^ 2 ∂volume.restrict U)) := by
  have hqb : ∀ᵐ x ∂volume.restrict U, ‖q x‖ ≤ C :=
    Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hq0 x)]; exact hsb x)
  have hcomm (α : JetIndex2 K) := metricRawCommutator_memLp G hG
    (fun l => metricEntryEnvelope CG g δ l.val) hbfull D hD α
  have hadd := weightedSource_sum_add_le q hq.aestronglyMeasurable hq0 hqb
    (fun α : JetIndex2 K => factorialWeight ρ α.1.val)
    (fun α => factorialWeight_nonneg ρ α.1.val)
    (fun α x => metricCommutatorTerm (Nat.le_of_lt_succ α.1.isLt) G D α.2 x) F hcomm hF
  simp only [storedWord_sum_weighted
    (fun j : Fin (K + 1) => factorialWeight ρ j.val)] at hadd
  exact hadd

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev Set
namespace AVRegularity.Weighted

/-! Every actual stored source word satisfies the clipped weighted scalar estimate with its true residuals. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem storedWord_clipped_value_energy_bound {K : ℕ}
    (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hv : ∀ t ∈ Icc a b, ContDiff ℝ 1 (v t))
    (hvm : Measurable (fun p : Icc a b × Vec 2 => v p.1 p.2))
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ j : Fin 2, fderiv ℝ (v t) x (basisVec j) j = 0)
    (Mv : ℝ) (hMv : 0 ≤ Mv) (hvb : ∀ t ∈ Icc a b, ∀ x, ‖v t x‖ ≤ Mv)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ t ∈ Icc a b, ∀ k j, ContDiff ℝ 1 (fun x => G t x k j))
    (hGm : Measurable (fun p : Icc a b × Vec 2 => G p.1 p.2))
    (g : ℝ) (hg4 : g ≤ 1 / 4) (hGnear : IsMetricNearIdentity G g)
    (hGs : ∀ t ∈ Icc a b, ∀ x, (G t x).IsSymm)
    (t₀ S ϖ : ℝ) (zc : Vec 2) (N m : ℕ) (Cw : ℕ → ℝ)
    (C : ChartWeights G v t₀ S ϖ zc N Cw) (hm : m ≤ N)
    (ha : t₀ ≤ a) (hb : b ≤ t₀ + S)
    (U H : ℝ → PlaneHk Set.univ K E)
    (W : ℝ → PlaneHk Set.univ (K + 1) E)
    (Q : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (hH : MemLp H 2 (volume.restrict (Icc a b)))
    (hQ : MemLp Q 2 (volume.restrict (Icc a b))) (α : JetIndex2 K)
    (hcurve : PlaneWeakHilbertCurve a b
      (fun t => planeJetReadoutOperator K α (U t))
      (fun t => planeWordH1SliceOperator K α (W t))
      (fun t => planeSourceDual (planeJetReadoutOperator K α (H t))
        (planeJetFluxOperator K α (Q t))))
    (B : ℝ) (hB : 0 < B) :
    let u := fun t => planeJetReadoutOperator K α (U t)
    let slice := fun t => planeWordH1SliceOperator K α (W t)
    let T := planeIntervalTransport a b hab v (fun t ht => (hv t ht).continuous) Mv hvb
    let D := planeIntervalDiffusion a b hab G
      (fun t ht k j => (hG t ht k j).continuous) g hg4 hGnear hGs
    let F := fun t => planeJetFluxOperator K α (Q t) - D t (planeH1GradientOperator (slice t))
    let R := fun t => planeJetReadoutOperator K α (H t) + T t (planeH1GradientOperator (slice t))
    ∀ t ∈ Icc a b,
      (∫ x, clipWeight B (C.W m t x) * ‖u t x‖ ^ 2) +
      (∫ s in a..t, ∫ x, clipWeight B (C.W m s x) *
        ‖(WithLp.toLp 2 (fun k => planeH1GradientOperator (slice s) k x) :
          PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) ≤
      ((∫ x, clipWeight B (C.W m a x) * ‖u a x‖ ^ 2) +
        8 * (∫ s in a..b, ∫ x, clipWeight B (C.W m s x) *
          ‖(WithLp.toLp 2 (fun k => F s k x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) +
        2 * (∫ s in a..b, ∫ x, clipWeight B (C.W m s x) * (‖R s x‖ * ‖u s x‖))) *
        Real.exp (18 * C.lam m * (t - a)) := by
  dsimp only
  have hacts := planeIntervalActions_memLp a b hab v (fun t ht => (hv t ht).continuous)
    hvm Mv hvb G (fun t ht k j => (hG t ht k j).continuous) hGm
    g hg4 hGnear hGs (fun t => planeWordH1SliceOperator K α (W t)) hcurve.state
  have hres := orderedSourceResidual_memLp H Q hH hQ α _ _ hacts.1 hacts.2
  exact planeWeak_clipped_value_energy_gronwall a b hab v hv hdiv Mv hMv hvb G hG g hg4
    hGnear hGs t₀ S ϖ zc N m Cw C hm ha hb _ _ _ _
    (planeSourceCurve_scalar_residual _ _ _ _ _ _ hcurve) B hB hres.2 hres.1

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! The actual weighted metric commutator has a small factorial source energy at a reduced radius. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

theorem weightedMetricForcedFlux_energy_le {K : ℕ} {U : Set (Vec 2)}
    (ρ δ g : ℝ) (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ) (hg : 0 ≤ g) (hscale : ρ * δ ≤ 1)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ k a, ContDiff ℝ (K : ℕ) (fun x => G x k a))
    (CG : ℕ → ℝ)
    (hbfull : ∀ (l : Fin (K + 1)) x k a,
      ‖iteratedFDeriv ℝ l.val (fun y => G y k a) x‖ ≤ metricEntryEnvelope CG g δ l.val)
    (hb : ∀ l, 1 ≤ l → l ≤ K → ∀ x k a,
      ‖iteratedFDeriv ℝ l (fun y => G y k a) x‖ ≤ CG l * g * δ ^ l)
    (q : Vec 2 → ℝ) (hq : Continuous q) (hq0 : ∀ x, 0 ≤ q x)
    (C : ℝ) (hsb : ∀ x, q x ≤ C) (D : RawJet2 (K + 1) E) (hD : JetMemL2On U D)
    (F : RawJet2 K (PiLp 2 (fun _ : Fin 2 => E))) (hF : JetMemL2On U F) :
    (∑ j : Fin (K + 1), factorialWeight ρ j.val *
      (∑ w : DerivativeWord2 j.val, ∫ x, q x *
        ‖metricCommutatorTerm (Nat.le_of_lt_succ j.isLt) G D w x + F ⟨j, w⟩ x‖ ^ 2 ∂volume.restrict U)) ≤
      2 * ((metricRadiusConstant K CG * g * (ρ * δ)) ^ 2 * (∑ j : Fin (K + 1), factorialWeight ρ j.val *
        (∫ x, q x * (∑ w : DerivativeWord2 j.val,
          ‖(WithLp.toLp 2 (fun k : Fin 2 =>
            D ⟨⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩, Fin.snoc w k⟩ x) :
            PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) ∂volume.restrict U))) + 2 * (∑ j : Fin (K + 1), factorialWeight ρ j.val *
        (∑ w : DerivativeWord2 j.val, ∫ x, q x * ‖F ⟨j, w⟩ x‖ ^ 2 ∂volume.restrict U)) := by
  have hmetric := weightedMetricFluxSource_energy_le (E := E) (K := K) (U := U) ρ δ g hρ hδ hg hscale
    G hG CG hbfull hb q hq hq0 C hsb D hD
  have hadd := metricForcedFlux_addition_budget (E := E) (K := K) (U := U) ρ δ g G hG CG hbfull q hq hq0 C hsb D hD F hF
  have hm2 := mul_le_mul_of_nonneg_left hmetric (by norm_num : (0 : ℝ) ≤ 2)
  apply hadd.trans
  apply add_le_add_left
  exact hm2

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier Set
namespace AVRegularity.Weighted

/-! Every actual stored source word satisfies the clipped weighted scalar estimate with its true residuals. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem storedWord_residual_time_integrable {K : ℕ}
    (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hv : ∀ t ∈ Icc a b, ContDiff ℝ 1 (v t))
    (hvm : Measurable (fun p : Icc a b × Vec 2 => v p.1 p.2))
    (Mv : ℝ) (hvb : ∀ t ∈ Icc a b, ∀ x, ‖v t x‖ ≤ Mv)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ t ∈ Icc a b, ∀ k j, ContDiff ℝ 1 (fun x => G t x k j))
    (hGm : Measurable (fun p : Icc a b × Vec 2 => G p.1 p.2))
    (g : ℝ) (hg4 : g ≤ 1 / 4) (hGnear : IsMetricNearIdentity G g)
    (hGs : ∀ t ∈ Icc a b, ∀ x, (G t x).IsSymm)
    (t₀ S ϖ : ℝ) (zc : Vec 2) (N m : ℕ) (Cw : ℕ → ℝ)
    (C : ChartWeights G v t₀ S ϖ zc N Cw) (hm : m ≤ N)
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
    (B : ℝ) (hB : 0 < B) (α : JetIndex2 K) :
    let slice := fun t => planeWordH1SliceOperator K α (W t)
    let T := planeIntervalTransport a b hab v (fun t ht => (hv t ht).continuous) Mv hvb
    let D := planeIntervalDiffusion a b hab G
      (fun t ht k j => (hG t ht k j).continuous) g hg4 hGnear hGs
    let L := fun t => planeJetFluxOperator K α (Q t) - D t (planeH1GradientOperator (slice t))
    let R := fun t => planeJetReadoutOperator K α (H t) + T t (planeH1GradientOperator (slice t))
    Integrable (fun t => ∫ x, clipWeight B (C.W m t x) *
      ‖(WithLp.toLp 2 (fun k : Fin 2 => L t k x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2)
      (volume.restrict (Icc a b)) ∧
    Integrable (fun t => ∫ x, clipWeight B (C.W m t x) *
      (‖R t x‖ * ‖planeJetReadoutOperator K α (U t) x‖))
      (volume.restrict (Icc a b)) := by
  dsimp only
  have hc := hcurve α
  have hacts := planeIntervalActions_memLp a b hab v (fun t ht => (hv t ht).continuous)
    hvm Mv hvb G (fun t ht k j => (hG t ht k j).continuous) hGm
    g hg4 hGnear hGs (fun t => planeWordH1SliceOperator K α (W t)) hc.state
  have hres := orderedSourceResidual_memLp H Q hH hQ α _ _ hacts.1 hacts.2
  have hu : MemLp (fun t => planeJetReadoutOperator K α (U t)) 2
      (volume.restrict (Icc a b)) :=
    (memLp_congr_ae hc.agrees).2 ((planeHkValueOperator (E := E) 1).comp_memLp' hc.state)
  obtain ⟨hqc, hqm, hqb⟩ := chartWeights_clipped_time_coefficient C m hm B hB
  exact ⟨chartWeights_clipped_finite_time_integrable (E := E) C m hm B hB _ _ hres.2,
    weighted_spatial_value_product_time_integrable _ hqc hqm hB.le hqb _ _ hres.1 hu⟩

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev Set
namespace AVRegularity.Weighted

/-! Every actual stored source word satisfies the clipped weighted scalar estimate with its true residuals. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem storedWords_clipped_value_energy_sum {K : ℕ}
    (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hv : ∀ t ∈ Icc a b, ContDiff ℝ 1 (v t))
    (hvm : Measurable (fun p : Icc a b × Vec 2 => v p.1 p.2))
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ j : Fin 2, fderiv ℝ (v t) x (basisVec j) j = 0)
    (Mv : ℝ) (hMv : 0 ≤ Mv) (hvb : ∀ t ∈ Icc a b, ∀ x, ‖v t x‖ ≤ Mv)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ t ∈ Icc a b, ∀ k j, ContDiff ℝ 1 (fun x => G t x k j))
    (hGm : Measurable (fun p : Icc a b × Vec 2 => G p.1 p.2))
    (g : ℝ) (hg4 : g ≤ 1 / 4) (hGnear : IsMetricNearIdentity G g)
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
        (∫ s in a..t, ∫ x, clipWeight B (C.W m s x) *
          ‖(WithLp.toLp 2 (fun k => planeH1GradientOperator (slice s) k x) :
            PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2)
    let I := fun (α : JetIndex2 K) =>
      let u := fun t => planeJetReadoutOperator K α (U t)
      let slice := fun t => planeWordH1SliceOperator K α (W t)
      let T := planeIntervalTransport a b hab v (fun t ht => (hv t ht).continuous) Mv hvb
      let D := planeIntervalDiffusion a b hab G
        (fun t ht k j => (hG t ht k j).continuous) g hg4 hGnear hGs
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
  have h := storedWord_clipped_value_energy_bound a b hab v hv hvm hdiv Mv hMv hvb
    G hG hGm g hg4 hGnear hGs t₀ S ϖ zc N m Cw C hm ha hb U H W Q hH hQ α
    (hcurve α) B hB t ht
  dsimp only at h
  exact (mul_le_mul_of_nonneg_left h (factorialWeight_nonneg ρ _)).trans_eq (by ring)

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! The actual weighted metric commutator has a small factorial source energy at a reduced radius. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

theorem planeMetricForcedFlux_budget {K : ℕ} 
    (ρ δ g : ℝ) (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ) (hg : 0 ≤ g) (hscale : ρ * δ ≤ 1)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ k a, ContDiff ℝ (K : ℕ) (fun x => G x k a))
    (CG : ℕ → ℝ)
    (hbfull : ∀ (l : Fin (K + 1)) x k a,
      ‖iteratedFDeriv ℝ l.val (fun y => G y k a) x‖ ≤ metricEntryEnvelope CG g δ l.val)
    (hb : ∀ l, 1 ≤ l → l ≤ K → ∀ x k a,
      ‖iteratedFDeriv ℝ l (fun y => G y k a) x‖ ≤ CG l * g * δ ^ l)
    (q : Vec 2 → ℝ) (hq : Continuous q) (hq0 : ∀ x, 0 ≤ q x)
    (C : ℝ) (hsb : ∀ x, q x ≤ C) (D : RawJet2 (K + 1) E) (hD : JetMemL2On Set.univ D)
    (F : RawJet2 K (PiLp 2 (fun _ : Fin 2 => E))) (hF : JetMemL2On Set.univ F) :
    (∑ j : Fin (K + 1), factorialWeight ρ j.val *
      (∑ w : DerivativeWord2 j.val, ∫ x, q x *
        ‖metricCommutatorTerm (Nat.le_of_lt_succ j.isLt) G D w x + F ⟨j, w⟩ x‖ ^ 2)) ≤
      2 * ((metricRadiusConstant K CG * g * (ρ * δ)) ^ 2 * rawWeightedGradientEnergy ρ q D) + 2 * (∑ j : Fin (K + 1), factorialWeight ρ j.val *
        (∑ w : DerivativeWord2 j.val, ∫ x, q x * ‖F ⟨j, w⟩ x‖ ^ 2)) := by
  have h := weightedMetricForcedFlux_energy_le ρ δ g hρ hδ hg hscale G hG CG hbfull hb q hq hq0 C hsb D hD F hF
  simp only [Measure.restrict_univ] at h
  have hqb : ∀ᵐ x ∂volume, ‖q x‖ ≤ C :=
    Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hq0 x)]
      exact hsb x)
  rw [rawWeightedGradient_integral_sum ρ q hq.aestronglyMeasurable hqb D hD] at h
  exact h

end AVRegularity.Weighted
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! The native predecessor flux is exactly the chronological Taylor-letter forcing. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

theorem wordPredecessorFlux_zero (letters : Fin N → CycleLetter ι h D)
    (κ : Fin (N + 1) → ι → ℕ) (X₀ : Vec 2) (δ : ℝ)
    (W : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (x : ι) (t : ℝ) (z : Vec 2) :
    wordPredecessorFlux letters κ X₀ δ W (0, x) t z = 0 := by
  classical
  unfold wordPredecessorFlux
  apply Finset.sum_eq_zero
  intro i' _
  apply Finset.sum_eq_zero
  intro d _
  have hh : ¬(0 : Fin (N + 1)).val = i'.1.val + 1 := by simp
  simp only [wordPredecessorCoefficient, dite_eq_right hh, zero_apply]

theorem wordPredecessorFlux_succ (letters : Fin N → CycleLetter ι h D)
    (κ : Fin (N + 1) → ι → ℕ) (X₀ : Vec 2) (δ : ℝ)
    (W : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (j : Fin N) (x : ι) (t : ℝ) (z : Vec 2) :
    wordPredecessorFlux letters κ X₀ δ W (j.succ, x) t z =
      letterAdmissibleFlux (letters j) (fun p : Fin (N + 1) × ι => κ p.1 p.2)
        (j.succ, x) (fun u => (j.castSucc, u)) x (if (letters j).positive then 1 else 0)
        X₀ δ (fun u => W (j.castSucc, u)) t z := by
  classical
  simp only [wordPredecessorFlux, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single j.castSucc]
  · simp [wordPredecessorCoefficient, letterAdmissibleFlux, wordCouplingInput,
      admissibleLetterSourceIndex, admissibleLetterOrder, sourceWordIndex]
    rfl
  · intro j' _ hne
    apply Finset.sum_eq_zero
    intro u _
    apply Finset.sum_eq_zero
    intro d _
    have hh : ¬j.succ.val = j'.val + 1 := by
      intro h
      apply hne
      apply Fin.ext
      simpa only [Fin.val_castSucc] using (show j'.val = j.val by
        simp only [Fin.val_succ] at h; omega)
    simp only [wordPredecessorCoefficient, dite_eq_right hh, zero_apply]
  · intro hn
    exact (hn (Finset.mem_univ j.castSucc)).elim

end AVRegularity.Weighted
end
