-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Weighted.DriftCoefficientEmbedding
public import AVRegularity.Weighted.MetricWordCoefficientArrayBound
public import AVRegularity.Weighted.PlaneCoefficientRows
import AVRegularity.CycleComparison.Lift.LeftTermsFieldPostcomposition
public import AVRegularity.Statements.Intermediate.CycleComparison.OrderedDerivative
import AVRegularity.CycleComparison.Lift.LiftMeanRecursionCongruence
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! The true reserved cell velocity jets give a finite factorial drift envelope. -/

theorem finite_drift_jet_envelope (Kmax : ℕ) (η : ℝ) (hη : 0 < η)
    (v : ℝ → Vec 2 → Vec 2) (hv : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (C : ℕ → ℝ)
    (hb : ∀ j t x, ‖iteratedFDeriv ℝ j (fun y => Real.sqrt η • v t y) x‖ ≤ C j) :
    ∃ a : ℝ, 0 ≤ a ∧ ∀ l, 1 ≤ l → l ≤ Kmax → ∀ t x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤ a * (l.factorial : ℝ) := by
  classical
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  let B := fun l : Fin (Kmax + 1) =>
    ((Fintype.card (DerivativeWord2 l.val) : ℝ) * ‖driftCoefficientEmbedding‖) *
      (|C l.val| / Real.sqrt η)
  let a := ∑ l, B l
  have hB (l : Fin (Kmax + 1)) : 0 ≤ B l := by dsimp [B]; positivity
  have ha : 0 ≤ a := Finset.sum_nonneg (fun l _ => hB l)
  refine ⟨a, ha, ?_⟩
  intro l _ hl t x
  let li : Fin (Kmax + 1) := ⟨l, Nat.lt_succ_of_le hl⟩
  have hvj : ContDiff ℝ (l : ℕ) (v t) := (hv t).of_le (by simp)
  have he := iteratedFDeriv_const_smul_apply' (a := Real.sqrt η) (hvj.contDiffAt (x := x))
  have hh := (hb l t x).trans (le_abs_self (C l))
  rw [he, norm_smul, Real.norm_of_nonneg hs.le] at hh
  have hnorm : ‖iteratedFDeriv ℝ l (v t) x‖ ≤ |C l| / Real.sqrt η := by
    apply (le_div_iff₀ hs).mpr
    simpa only [mul_comm] using hh
  have harray : ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤ B li :=
    (driftCoefficient_array_norm_le_iterated (v t) l hvj x).trans
      (mul_le_mul_of_nonneg_left hnorm (by positivity))
  have hsingle : B li ≤ a := Finset.single_le_sum (f := B)
    (fun l _ => hB l) (Finset.mem_univ li)
  have hfac : (1 : ℝ) ≤ (l.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos l
  have hm : a ≤ a * (l.factorial : ℝ) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hfac ha
  exact (harray.trans hsingle).trans hm

end AVRegularity.Weighted
end
end

section
@[expose] public section
namespace AVRegularity.Weighted

/-! One reserve depending on the maximal slot absorbs every component's actual metric budget. -/

theorem maximalSlot_radius_source_reserve {K Kmax : ℕ} (hK : K ≤ Kmax)
    (CG : ℕ → ℝ) {A L r δ g : ℝ} (hA : 0 ≤ A) (hL : 1 ≤ L)
    (hreserve : A * (1 + (metricRadiusConstant Kmax CG) ^ 2) / L ^ 2 ≤ 1 / 16)
    (hr : 0 ≤ r) (hδ : 0 ≤ δ) (hg : 0 ≤ g) (hg4 : g ≤ 1 / 4) (hscale : r * δ ≤ 1) :
    A * (16 * (metricRadiusConstant K CG * g * ((r / L) * δ)) ^ 2 +
      (1 / L ^ 2) / 2) ≤ 1 / 2 := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hbig := radius_reserve_source_coefficient hA (metricRadiusConstant_nonneg Kmax CG)
    hL hreserve hr hδ hg hg4 hscale
  have hp := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (metricRadiusConstant_mono hK CG) hg)
    (mul_nonneg (div_nonneg hr hLp.le) hδ)
  have hp0 : 0 ≤ metricRadiusConstant K CG * g * ((r / L) * δ) :=
    mul_nonneg (mul_nonneg (metricRadiusConstant_nonneg K CG) hg)
      (mul_nonneg (div_nonneg hr hLp.le) hδ)
  have hs := pow_le_pow_left₀ hp0 hp 2
  have he : (1 / L ^ 2) / 2 = 1 / (2 * L ^ 2) := by ring
  rw [he]
  exact (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 16)) le_rfl) hA).trans hbig

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! The metric deviation has a finite literal factorial coefficient seminorm. -/

section
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]

theorem metricFlux_deviation_coefficientSeminorm_ne_top (ρ : ℝ) (K : ℕ) (ta tb : ℝ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ t ∈ Set.Icc ta tb, ∀ k j, ContDiff ℝ (K : ℕ) (fun x => G t x k j))
    (M : Fin (K + 1) → ℝ)
    (hb : ∀ (l : Fin (K + 1)) t, t ∈ Set.Icc ta tb → ∀ x k j,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k j) x‖ ≤ M l)
    {a b : ι} (m : ℕ) (hab : a = b) (hm : m = 1) :
    coefficientSeminorm ρ K ta tb
      (fun t x => metricFlux (h := h) (G t x - 1) m hab hm) ≠ ⊤ := by
  apply coefficientSeminorm_ne_top_of_array_bound ρ K ta tb _
    (fun l => (Fintype.card (DerivativeWord2 l.val) : ℝ) *
      ((|M l| + 1) * (∑ k : Fin 2, ∑ j : Fin 2, ‖metricWordEntry (h := h) m hab hm k j‖)))
  intro l t ht x
  have hc (k j : Fin 2) : ContDiff ℝ (l.val : ℕ) (fun y => G t y k j) :=
    (hG t ht k j).of_le (by exact_mod_cast Nat.le_of_lt_succ l.isLt)
  apply metricFlux_array_norm_le (fun y => G t y - 1) l.val
    (fun k j => (hc k j).sub contDiff_const) m hab hm (|M l| + 1) (by positivity)
  intro w y k j
  have hdev : ContDiff ℝ (l.val : ℕ) (fun z => (G t z - 1) k j) := (hc k j).sub contDiff_const
  have ho := orderedScalarDerivative_norm_le (fun z => (G t z - 1) k j) l.val hdev w y
  rw [Real.norm_eq_abs] at ho
  exact ho.trans (scalar_iteratedDerivative_sub_const_bound (fun z => G t z k j)
    l.val (hc k j) ((1 : Matrix (Fin 2) (Fin 2) ℝ) k j) (M l)
    (identityMatrix_entry_abs_le_one k j) y (hb l t ht y k j))
end

/-! The scalar chain's literal coefficient arrays inherit spatial regularity from the metric. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]

theorem scalarChainCoefficient_coefficientSeminorm_ne_top
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (κ : Fin 1 → ι → ℕ)
    (ρ ta tb : ℝ) (i i' : Fin 1 × ι)
    (d : admissibleOrders (fun p => κ p.1 p.2) 2 i i')
    (hG : ∀ t ∈ Set.Icc ta tb, ∀ k j, ContDiff ℝ (κ i.1 i.2 : ℕ) (fun x => G t x k j))
    (M : Fin (κ i.1 i.2 + 1) → ℝ)
    (hb : ∀ (l : Fin (κ i.1 i.2 + 1)) t, t ∈ Set.Icc ta tb → ∀ x k j,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k j) x‖ ≤ M l) :
    coefficientSeminorm ρ (κ i.1 i.2) ta tb
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i' d) ≠ ⊤ := by
  classical
  by_cases he : i = i'
  · subst i'
    have heq : planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i d =
        fun t x => metricFlux (h := h) (G t x - 1) (d.val - 1) (a := i.2) rfl
          (by have hd := scalarChain_order_eq_two κ i i d; omega) := by
      funext t x
      exact scalarChainCoefficient_diagonal G κ i d t x
    rw [heq]
    exact metricFlux_deviation_coefficientSeminorm_ne_top ρ (κ i.1 i.2) ta tb G hG M hb
      (d.val - 1) rfl (by have hd := scalarChain_order_eq_two κ i i d; omega)
  · have hc : i.2 ≠ i'.2 := by
      intro hc
      exact he (Prod.ext (Subsingleton.elim _ _) hc)
    have heq : planeChainCoefficient (geometryScalarData (h := h) 2 G) κ i i' d =
        fun _ _ => 0 := by
      funext t x
      exact scalarChainCoefficient_offDiagonal G κ i i' hc d t x
    rw [heq]
    apply coefficientSeminorm_ne_top_of_array_bound ρ (κ i.1 i.2) ta tb _ (fun _ => 0)
    intro l t ht x
    have hz : coefficientDerivativeArray (fun _ : Vec 2 =>
        (0 : (PiLp 2 (fun _ : DerivativeWord2 (d.val - 1) => h i'.2)) →L[ℝ]
          PiLp 2 (fun _ : Fin 2 => h i.2))) l.val x = 0 := by
      apply ContinuousLinearMap.ext
      intro z
      apply PiLp.ext
      intro w
      simp [coefficientDerivativeArray, orderedCoefficientDerivative_zero_function]
    rw [hz]
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro z
    simp
end

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Filter
open scoped Topology
namespace AVRegularity.Weighted

/-! Bounded clipped multiplication converges in the actual plane L2 space whenever the weighted energy is finite. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [BorelSpace E] [CompleteSpace E] in
theorem weighted_planeLp_clipping_tendsto (q : Vec 2 → ℝ) (hq : Continuous q)
    (hq0 : ∀ x, 0 < q x) (U : Lp E 2 (volume : Measure (Vec 2)))
    (hw : MemLp (fun x => q x • U x) 2 volume) :
    ∃ hc : ∀ n : ℕ, Continuous (fun x => clipWeight ((n : ℝ) + 1) (q x)),
    ∃ hb : ∀ n : ℕ, ∀ x, |clipWeight ((n : ℝ) + 1) (q x)| ≤ (n : ℝ) + 1,
    Tendsto (fun n : ℕ => planeScalarMultiplier (fun x => clipWeight ((n : ℝ) + 1) (q x))
      (hc n) (by positivity) (hb n) U) atTop (𝓝 (hw.toLp (fun x => q x • U x))) := by
  have hc (n : ℕ) : Continuous (fun x => clipWeight ((n : ℝ) + 1) (q x)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hasDerivAt_clipWeight (by positivity) (hq0 x)).continuousAt.comp hq.continuousAt
  have hb (n : ℕ) x : |clipWeight ((n : ℝ) + 1) (q x)| ≤ (n : ℝ) + 1 := by
    rw [abs_of_pos (clipWeight_pos (by positivity) (hq0 x))]
    exact clipWeight_le_bound (by positivity) (hq0 x)
  refine ⟨hc, hb, ?_⟩
  let f := fun (n : ℕ) x => clipWeight ((n : ℝ) + 1) (q x) • U x
  have hf (n : ℕ) : MemLp (f n) 2 volume := by
    have hm : MemLp (fun x => clipWeight ((n : ℝ) + 1) (q x)) ⊤ volume :=
      memLp_top_of_bound (hc n).aestronglyMeasurable ((n : ℝ) + 1)
        (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb n x))
    exact hm.smul (Lp.memLp U)
  have hB : Integrable (fun x => q x ^ 2 * ‖U x‖ ^ 2) volume := by
    have he x : ‖q x • U x‖ ^ 2 = q x ^ 2 * ‖U x‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    simpa only [he] using hw.norm.integrable_sq
  have hdom (n : ℕ) : ∀ᵐ x ∂volume, ‖f n x - q x • U x‖ ^ 2 ≤ q x ^ 2 * ‖U x‖ ^ 2 := by
    apply Eventually.of_forall
    intro x
    have hpos := (clipWeight_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1) (hq0 x)).le
    have hle := clipWeight_le_value (by positivity : (0 : ℝ) < (n : ℝ) + 1) (hq0 x)
    have hs : (clipWeight ((n : ℝ) + 1) (q x) - q x) ^ 2 ≤ q x ^ 2 := by
      nlinarith only [hpos, hle]
    dsimp only [f]
    rw [← sub_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    exact mul_le_mul_of_nonneg_right hs (sq_nonneg _)
  have ht := planeLp_tendsto_of_dominated_normSq f (fun x => q x • U x) hf hw
    (fun x => q x ^ 2 * ‖U x‖ ^ 2) hB hdom
    (Eventually.of_forall (fun x => (clipWeight_nat_tendsto (q x) (hq0 x)).smul_const (U x)))
  have he (n : ℕ) : planeScalarMultiplier (fun x => clipWeight ((n : ℝ) + 1) (q x))
      (hc n) (by positivity) (hb n) U = (hf n).toLp (f n) := by
    apply Lp.ext
    filter_upwards [planeScalarMultiplier_ae _ (hc n) (by positivity) (hb n) U, (hf n).coeFn_toLp]
      with x hx hy
    exact hx.trans hy.symm
  simpa only [he] using ht

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.Weighted

/-! The actual metric-gradient product, with its full ordered weak Sobolev jet. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def planeMetricGradientCarrier {K : ℕ}
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ k a, ContDiff ℝ (K : ℕ) (fun x => G x k a))
    (M : Fin (K + 1) → ℝ)
    (hb : ∀ l : Fin (K + 1), ∀ x k a,
      ‖iteratedFDeriv ℝ l.val (fun y => G y k a) x‖ ≤ M l)
    (p : PlaneHk Set.univ (K + 1) E) :
    PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)) :=
  (planeGradientTensor p).mulCoefficient (fun x => metricFiberCoefficient (G x))
    (metricFiberCoefficient_contDiff G hG)
    (A := fun l => (Fintype.card (DerivativeWord2 l.val) : ℝ) * (4 * M l))
    (metricFiberCoefficient_array_bound_entries (E := E) G hG M hb)
end

/-! The metric Sobolev carrier has exactly the literal matrix-gradient value. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeMetricGradientCarrier_value_ae {K : ℕ}
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ k a, ContDiff ℝ (K : ℕ) (fun x => G x k a))
    (M : Fin (K + 1) → ℝ)
    (hb : ∀ l : Fin (K + 1), ∀ x k a,
      ‖iteratedFDeriv ℝ l.val (fun y => G y k a) x‖ ≤ M l)
    (p : PlaneHk Set.univ (K + 1) E) :
    (planeMetricGradientCarrier G hG M hb p).val (valueIndex2 K)
      =ᵐ[volume.restrict Set.univ] fun x =>
        finiteMetricFlux (G x) ((planeGradientTensor p).val (valueIndex2 K) x) := by
  unfold planeMetricGradientCarrier
  exact (planeCoefficientCarrier_value_ae _ _ _ _).trans
    (Filter.Eventually.of_forall (fun x => metricFiberCoefficient_apply (G x) _))
end

end AVRegularity.Weighted
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Smooth spatial coefficient jets inherit joint measurability from their time slices. -/

section
variable {T F : Type*} [MeasurableSpace T]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology F]

theorem parameter_orderedDerivative_joint_measurable (K j : ℕ) (hj : j ≤ K)
    (f : T → Vec 2 → F) (hm : ∀ x, Measurable (fun t => f t x))
    (hf : ∀ t, ContDiff ℝ (K : ℕ) (f t)) (w : DerivativeWord2 j) :
    Measurable (Function.uncurry (fun t => orderedDerivative w (f t))) := by
  have hc (t : T) : Continuous (orderedDerivative w (f t)) :=
    (CycleComparison.Lift.orderedDerivative_contDiff w 0 (f t)
      (by simpa only [Nat.zero_add] using
        (hf t).of_le (by exact_mod_cast hj))).continuous
  have ht (x : Vec 2) : Measurable (fun t => orderedDerivative w (f t) x) :=
    CycleComparison.Lift.orderedDerivative_parameter_measurable f K hm hf j hj w x
  exact (measurable_uncurry_of_continuous_of_measurable hc ht).comp measurable_swap
end

/-! Ordered operator coefficient arrays have genuine joint measurable representatives. -/

section
variable {T E F : Type*} [MeasurableSpace T]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace (E →L[ℝ] F)] [BorelSpace (E →L[ℝ] F)]
  [SecondCountableTopology (E →L[ℝ] F)]

theorem parameter_orderedCoefficientDerivative_joint_measurable (K j : ℕ) (hj : j ≤ K)
    (C : T → Vec 2 → E →L[ℝ] F)
    (hm : ∀ x, Measurable (fun t => C t x))
    (hf : ∀ t, ContDiff ℝ (K : ℕ) (C t)) (w : DerivativeWord2 j) :
    Measurable (Function.uncurry (fun t => orderedCoefficientDerivative (C t) j w)) := by
  have he (t : T) : orderedCoefficientDerivative (C t) j w = orderedDerivative w (C t) := by
    funext x
    rw [orderedCoefficientDerivative_eq_iterated (C t) j
      ((hf t).of_le (by exact_mod_cast hj)) w x,
      orderedDerivative_eq_iteratedFDeriv w ((hf t).of_le (by exact_mod_cast hj))]
  simp_rw [he]
  exact parameter_orderedDerivative_joint_measurable K j hj C hm hf w
end

end AVRegularity.Weighted
end
end
