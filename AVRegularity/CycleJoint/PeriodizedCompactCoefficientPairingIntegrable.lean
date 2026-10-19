-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleJoint.PlaneImageJetMomentNorm
import AVRegularity.CycleJoint.PeriodicOperatorLocalization
public import AVRegularity.CycleJoint.TransitionJetTermDerivative
import AVRegularity.CycleComparison.Coarse.SecondOrderResponse
import AVRegularity.CycleJoint.PlaneCoupledFluxScaling
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleJointProofs

/-! Absolute local image convergence also pays both endpoint pairing series. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K L : ℕ}

theorem translated_compact_jet_pairing_summable (U : Set (Vec 2))
    (f : PlaneHk Set.univ K E) (α : JetIndex2 K) (φ : PlaneHk Set.univ L E)
    (β : JetIndex2 L)
    (hφ : ∀ᵐ x ∂volume, x ∉ U → φ.toFunction.jet β x = 0)
    (hs : (∑' n : Fin 2 → ℤ, ‖planeImageJetCLM U (AVenhance.latticeShift n) α f‖ₑ) < ⊤) :
    Summable (fun n : Fin 2 → ℤ => ∫ x,
      inner ℝ ((planeCarrierTranslation K (AVenhance.latticeShift n) f).toFunction.jet α x)
        (φ.toFunction.jet β x)) := by
  have himages : Summable (fun n : Fin 2 → ℤ =>
      planeImageJetCLM U (AVenhance.latticeShift n) α f) := Summable.of_enorm hs.ne
  let g : Lp E 2 (volume.restrict U) :=
    restrictPlaneLpCLM U (planeJetReadoutOperator L β φ)
  have hi : Summable (fun n : Fin 2 → ℤ =>
      inner ℝ (planeImageJetCLM U (AVenhance.latticeShift n) α f) g) :=
    summable_hilbert_pairing himages g
  exact hi.congr (fun n =>
    (translated_compact_jet_pairing U (AVenhance.latticeShift n) f α φ β hφ).symm)

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVenhance AVenhance.Infra.Section5 AVRegularity.Sobolev
open AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! Weighted native samples retain joint measurability after the exact fixed-anchor reference flow. -/

section
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem weighted_fixed_flow_sample_joint_measurable
    (F : ChartedFamily ι h D P Ctx) (ν e E tS tZ : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ)) E n)
    (hmeas : F.IsTimeMeasurable) (hwmeas : ∀ p, Measurable (F.weight p))
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (s : ℝ) (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) :
    Measurable (fun z : Set.Icc tS tZ × Vec 2 => F.weight p z.1 •
      F.dimFlux ν e E p c v u γ d I z.1
        (streamFlow φ hφ (F.piece p).anchor z.2 s)
        (e⁻¹ • streamFlow φ hφ (F.piece p).anchor z.2 s)) := by
  have hy : Continuous (fun z : Set.Icc tS tZ × Vec 2 =>
      streamFlow φ hφ (F.piece p).anchor z.2 s) := by
    exact (streamFlow_joint_smooth hφ).continuous.comp
      (continuous_const.prodMk (continuous_snd.prodMk
        continuous_const))
  exact (weighted_dimFlux_joint_measurable F ν e E tS tZ n hs hmeas hwmeas
    p c v u γ d I).comp
      (measurable_fst.prodMk (hy.measurable.prodMk (hy.const_smul (e⁻¹)).measurable))
end

/-! Weighted native samples along the natural inverse flow are jointly measurable. -/

section
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem weighted_natural_sample_joint_measurable
    (F : ChartedFamily ι h D P Ctx) (ν e E tS tZ : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ)) E n)
    (hmeas : F.IsTimeMeasurable) (hwmeas : ∀ p, Measurable (F.weight p))
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) :
    Measurable (fun z : Set.Icc tS tZ × Vec 2 => F.weight p z.1 •
      F.dimFlux ν e E p c v u γ d I z.1
        (streamFlow φ hφ (F.piece p).anchor z.2 z.1)
        (e⁻¹ • streamFlow φ hφ (F.piece p).anchor z.2 z.1)) := by
  have hy : Continuous (fun z : Set.Icc tS tZ × Vec 2 =>
      streamFlow φ hφ (F.piece p).anchor z.2 z.1) := by
    exact (streamFlow_joint_smooth hφ).continuous.comp
      (continuous_const.prodMk (continuous_snd.prodMk
        (continuous_subtype_val.comp continuous_fst)))
  exact (weighted_dimFlux_joint_measurable F ν e E tS tZ n hs hmeas hwmeas
    p c v u γ d I).comp
      (measurable_fst.prodMk (hy.measurable.prodMk (hy.const_smul (e⁻¹)).measurable))
end

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Every actual order-two diagonal frozen-metric coefficient has the original uniform smallness price. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]

theorem frozenMetric_diagonal_coefficientSeminorm_le
    (K : ι → ℕ) (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (ρ a b g : ℝ) (hg : 0 ≤ g)
    (hsym : ∀ t ∈ Set.Icc a b, (M t).IsSymm)
    (hquad : ∀ t ∈ Set.Icc a b, ∀ ξ : Vec 2,
      |∑ i, ∑ j, ξ i * (M t - (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j * ξ j| ≤
        g * ∑ i, ξ i ^ 2) (v : ι) (d : admissibleOrders K 2 v v) :
    coefficientSeminorm ρ (K v) a b
      (planeDiagonalGradientCoefficient (h := h) K 2 (fun _ t _ => M t - 1) v v d) ≤
        ENNReal.ofReal (4 * g) := by
  have hd : d.1 = 2 := by
    have hh := Finset.mem_Icc.mp (Finset.mem_filter.mp d.2).1
    omega
  have heq : planeDiagonalGradientCoefficient (h := h) K 2 (fun _ t _ => M t - 1) v v d =
      fun t _ => metricFlux (h := h) (M t - 1) (d.1 - 1) (a := v) rfl (by omega) := by
    funext t x
    exact planeDiagonalGradientCoefficient_self_eq_metricFlux K 2 (fun _ t _ => M t - 1) v d hd t x
  rw [heq]
  exact frozenMetric_coefficientSeminorm_le M (d.1 - 1) rfl (by omega) ρ (K v) a b g hg hsym hquad

theorem frozenMetric_offDiagonal_coefficient_zero (K : ι → ℕ)
    (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v u : ι)
    (d : admissibleOrders K 2 v u) (huv : u ≠ v) :
    planeDiagonalGradientCoefficient (h := h) K 2 (fun _ t _ => M t - 1) v u d = 0 := by
  funext t x
  exact planeDiagonalGradientCoefficient_of_component_ne K 2 (fun _ t _ => M t - 1) v u d t x huv

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Uniform fourth moments periodize continuous plane curves with actual L2 time traces. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem periodized_image_jet_continuousOn {X : Type*} [TopologicalSpace X]
    (U : Set (Vec 2)) (R : ℝ) (hR : 0 < R) (hU : U ⊆ Metric.ball (0 : Vec 2) R)
    (z : Vec 2) (a : JetIndex2 K) (f : X → PlaneHk Set.univ K E) (s : Set X)
    (hf : ContinuousOn f s) (M : ℝ) (hM : 0 ≤ M)
    (hw : ∀ t ∈ s, AEStronglyMeasurable
      (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet a y) volume)
    (hb : ∀ t ∈ s, eLpNorm
      (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet a y) 2 volume ≤ ENNReal.ofReal M) :
    ContinuousOn (fun t => ∑' n : Fin 2 → ℤ,
      planeImageJetCLM U (AVenhance.latticeShift n) a (f t)) s := by
  apply continuousOn_tsum
    (fun n => planeImageJetCLM_continuousOn U (AVenhance.latticeShift n) a f s hf)
    (spatialLatticeReciprocal_square_summable.mul_left ((1 + R + ‖z‖) ^ 4 * M))
  intro n t ht
  exact planeImageJetCLM_radial_norm_le U R hR hU z a (f t) M hM (hw t ht) (hb t ht) n

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Spatial dilation before the time change has the inverse cell flux price. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeRawCouplingFlux_affine_inverse_ae (K : ι → ℕ) (D : ℕ) (r e : ℝ)
    (he : e ≠ 0) (y : Vec 2)
    (A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (W : ∀ i, PlaneHk Set.univ (K i + 1) (h i)) (i : ι) :
    planeRawCouplingFlux K D r
      (fun v u d t z => (e⁻¹ * (e ^ (d.1 - 1))⁻¹) • A v u d t (y + e • z))
      (fun u => planeCarrierAffine e he y (W u)) i =ᵐ[volume]
      fun z => e⁻¹ • planeRawCouplingFlux K D r A W i (y + e • z) := by
  have ha : (fun v u d t z => (e⁻¹ * (e ^ (d.1 - 1))⁻¹) • A v u d t (y + e • z)) =
      (fun v u d t z => (e⁻¹) ^ 2 • ((e * (e ^ (d.1 - 1))⁻¹) • A v u d t (y + e • z))) := by
    funext v u d t z
    rw [smul_smul]
    congr 1
    field_simp
  rw [ha]
  filter_upwards [planeRawCouplingFlux_affine_ae K D r e he y A W i] with z hz
  rw [planeRawCouplingFlux_smul, hz, smul_smul]
  congr 1
  field_simp

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The fourth moment discharges absolute convergence of the actual image L2 series. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem planeImageJetCLM_radial_enorm_tsum_lt_top (U : Set (Vec 2)) (R : ℝ) (hR : 0 < R)
    (hU : U ⊆ Metric.ball (0 : Vec 2) R) (z : Vec 2) (a : JetIndex2 K)
    (f : PlaneHk Set.univ K E) (M : ℝ) (hM : 0 ≤ M)
    (hw : AEStronglyMeasurable (fun y => (1 + ‖y - z‖) ^ 4 • f.toFunction.jet a y) volume)
    (hb : eLpNorm (fun y => (1 + ‖y - z‖) ^ 4 • f.toFunction.jet a y) 2 volume ≤ ENNReal.ofReal M) :
    (∑' n : Fin 2 → ℤ, ‖planeImageJetCLM U (AVenhance.latticeShift n) a f‖ₑ) < ⊤ := by
  have ht := (spatialLatticeReciprocal_square_summable.mul_left
    ((1 + R + ‖z‖) ^ 4 * M)).tsum_ofReal_lt_top
  apply (ENNReal.tsum_le_tsum (fun n => ?_)).trans_lt ht
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal
    (planeImageJetCLM_radial_norm_le U R hR hU z a f M hM hw hb n)

end AVRegularity.CycleJointProofs
end

section
open AVRegularity.ChartTransport AVenhance.Infra.Section5
namespace AVRegularity.CycleJointProofs

/-! The certified inverse-Piola budget is at least one at every reserve order. -/

theorem preparation_jacobian_constant_ge_one (J : ℕ) (Cchart : ℕ → ℝ) (N : ℕ) :
    let C := 1 + ∑ p ∈ Finset.range (J + 2), |preparationFlowJetConstant Cchart p|
    1 ≤ compConst C N * C := by
  dsimp only
  let C := 1 + ∑ p ∈ Finset.range (J + 2), |preparationFlowJetConstant Cchart p|
  have hC : 1 ≤ C := one_le_jetConst _ _
  have hcomp : 1 ≤ compConst C N := by
    have hh := compConst_mono hC (Nat.zero_le N)
    simpa only [compConst, Nat.cast_zero, zero_add, Nat.factorial_zero, Nat.cast_one,
      pow_zero, mul_one, one_mul] using hh
  exact one_le_mul_of_one_le_of_one_le hcomp hC

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Frozen metric rows satisfy the literal coupled-energy Schur condition without component-count loss. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]

omit [Fintype ι] in
theorem frozenMetric_diagonal_schur_entry_le
    (K : ι → ℕ) (π : ι → ℝ) (hπ : ∀ v, 0 < π v)
    (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (ρ a b g : ℝ) (hg : 0 ≤ g)
    (hsym : ∀ t ∈ Set.Icc a b, (M t).IsSymm)
    (hquad : ∀ t ∈ Set.Icc a b, ∀ ξ : Vec 2,
      |∑ i, ∑ j, ξ i * (M t - (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j * ξ j| ≤
        g * ∑ i, ξ i ^ 2) (v : ι) :
    schurMatrix (h := h) 1 ρ π K 2 a b
      (planeDiagonalGradientCoefficient K 2 (fun _ t _ => M t - 1)) v v ≤ 4 * g := by
  classical
  have h2 : 2 ∈ admissibleOrders K 2 v v := by simp [admissibleOrders]
  let d2 : admissibleOrders K 2 v v := ⟨2, h2⟩
  have hb := frozenMetric_diagonal_coefficientSeminorm_le (h := h) K M ρ a b g hg hsym hquad v d2
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [ENNReal.toReal_ofReal (mul_nonneg (by norm_num) hg)] at hr
  have hfact : ((K v).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (K v))
  unfold schurMatrix
  rw [Finset.sum_eq_single d2]
  · simpa only [d2, div_self (ne_of_gt (hπ v)), Real.sqrt_one,
      Nat.sub_self, pow_zero, one_mul, div_one, Nat.add_sub_cancel, div_self hfact, mul_one] using hr
  · intro d _ hne
    have he : d = d2 := by
      apply Subtype.ext
      have hh := Finset.mem_Icc.mp (Finset.mem_filter.mp d.2).1
      dsimp [d2]
      omega
    exact (hne he).elim
  · simp

omit [Fintype ι] in
theorem frozenMetric_offDiagonal_schur_zero (K : ι → ℕ) (π : ι → ℝ)
    (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (ρ a b : ℝ) (v u : ι) (huv : u ≠ v) :
    schurMatrix (h := h) 1 ρ π K 2 a b
      (planeDiagonalGradientCoefficient K 2 (fun _ t _ => M t - 1)) v u = 0 := by
  unfold schurMatrix
  have he (d : admissibleOrders K 2 v u) := frozenMetric_offDiagonal_coefficient_zero (h := h) K M v u d huv
  simp only [he, CycleComparison.Coarse.coefficientSeminorm_zero_coefficient,
    ENNReal.toReal_zero, zero_div, zero_mul, Finset.sum_const_zero, mul_zero]

theorem frozenMetric_diagonal_schurCondition
    (K : ι → ℕ) (π : ι → ℝ) (hπ : ∀ v, 0 < π v)
    (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (ρ a b g : ℝ) (hg : 0 ≤ g) (hgsmall : 4 * g ≤ 1 / 8)
    (hsym : ∀ t ∈ Set.Icc a b, (M t).IsSymm)
    (hquad : ∀ t ∈ Set.Icc a b, ∀ ξ : Vec 2,
      |∑ i, ∑ j, ξ i * (M t - (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j * ξ j| ≤
        g * ∑ i, ξ i ^ 2) :
    SchurCondition (schurMatrix (h := h) 1 ρ π K 2 a b
      (planeDiagonalGradientCoefficient K 2 (fun _ t _ => M t - 1))) := by
  classical
  constructor
  · intro v
    rw [Finset.sum_eq_single v]
    · exact (frozenMetric_diagonal_schur_entry_le K π hπ M ρ a b g hg hsym hquad v).trans hgsmall
    · intro u _ huv
      exact frozenMetric_offDiagonal_schur_zero K π M ρ a b v u huv
    · simp
  · intro u
    rw [Finset.sum_eq_single u]
    · exact (frozenMetric_diagonal_schur_entry_le K π hπ M ρ a b g hg hsym hquad u).trans hgsmall
    · intro v _ hvu
      exact frozenMetric_offDiagonal_schur_zero K π M ρ a b v u (Ne.symm hvu)
    · simp
end

/-! Spatially frozen metric arrays have finite native coefficient reserves at every edge-order bound. -/

section
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]

variable (K : ι → ℕ) (D : ℕ) (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
  (ρ a b g : ℝ) (hg : 0 ≤ g)
  (hsym : ∀ t ∈ Set.Icc a b, (M t).IsSymm)
  (hquad : ∀ t ∈ Set.Icc a b, ∀ ξ : Vec 2,
    |∑ i, ∑ j, ξ i * (M t - (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j * ξ j| ≤ g * ∑ i, ξ i ^ 2)

include hg hsym hquad in
theorem frozenMetric_order_coefficientSeminorm_le (v u : ι) (d : admissibleOrders K D v u) :
    coefficientSeminorm ρ (K v) a b
      (planeDiagonalGradientCoefficient (h := h) K D (fun _ t _ => M t - 1) v u d) ≤
        ENNReal.ofReal (4 * g) := by
  by_cases huv : u = v
  · subst u
    by_cases hd : d.1 = 2
    · have heq : planeDiagonalGradientCoefficient (h := h) K D (fun _ t _ => M t - 1) v v d =
          fun t _ => metricFlux (h := h) (M t - 1) (d.1 - 1) (a := v) rfl (by omega) := by
        funext t x
        exact planeDiagonalGradientCoefficient_self_eq_metricFlux K D (fun _ t _ => M t - 1) v d hd t x
      rw [heq]
      exact frozenMetric_coefficientSeminorm_le M (d.1 - 1) rfl (by omega) ρ (K v) a b g hg hsym hquad
    · have hz : planeDiagonalGradientCoefficient (h := h) K D (fun _ t _ => M t - 1) v v d = 0 := by
        funext t x
        exact planeDiagonalGradientCoefficient_of_order_ne K D _ v v d t x hd
      rw [hz, CycleComparison.Coarse.coefficientSeminorm_zero_coefficient]
      exact zero_le
  · have hz : planeDiagonalGradientCoefficient (h := h) K D (fun _ t _ => M t - 1) v u d = 0 := by
      funext t x
      exact planeDiagonalGradientCoefficient_of_component_ne K D _ v u d t x huv
    rw [hz, CycleComparison.Coarse.coefficientSeminorm_zero_coefficient]
    exact zero_le

include hg hsym hquad in
theorem frozenMetric_order_coefficients_finite (v u : ι) (d : admissibleOrders K D v u) :
    coefficientSeminorm ρ (K v) a b
      (planeDiagonalGradientCoefficient (h := h) K D (fun _ t _ => M t - 1) v u d) ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (frozenMetric_order_coefficientSeminorm_le K D M ρ a b g hg hsym hquad v u d)

theorem frozenMetric_order_coefficient_contDiff (v u : ι) (d : admissibleOrders K D v u) (t : ℝ) :
    ContDiff ℝ (K v : ℕ)
      (planeDiagonalGradientCoefficient (h := h) K D (fun _ t _ => M t - 1) v u d t) := by
  change ContDiff ℝ (K v : ℕ) (fun _ : Vec 2 =>
    planeDiagonalGradientCoefficient (h := h) K D (fun _ t _ => M t - 1) v u d t 0)
  exact contDiff_const
end

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance AVRegularity.ChartTransport
namespace AVRegularity.CycleJointProofs

/-! Native Piola entries retain their physical jet bound in affine cell coordinates. -/

variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem naturalPreparation_cell_jacobian_scaled_jet_bound
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (ha : 0 ≤ ocA α q Λ (m - 1)) (hE : 0 < ocEpsilon q Λ (m - 1)) (s r : ℝ)
    (hs : s ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hr : r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hage : |r - s| ≤ 2 * Cage * ocTauPP α q Λ m)
    (n : ℕ) (hn : n ≤ Jchart) (i j : Fin 2) (e ρ : ℝ)
    (he : 0 < e) (hρ : 0 ≤ ρ) (hρE : ρ ≤ ocEpsilon q Λ (m - 1)) (yc z : Vec 2) :
    let C := 1 + ∑ p ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart p|
    ∀ l, l ≤ n → (ρ / e) ^ l *
      ‖iteratedFDeriv ℝ l (fun x => naturalPreparationJacobian hφ s r (yc + e • x) i j) z‖ ≤
        compConst C n * C := by
  dsimp only
  intro l hl
  have hf : ContDiff ℝ (l : ℕ) (fun y => naturalPreparationJacobian hφ s r y i j) :=
    ((naturalPreparationJacobian_entry_smooth hφ s i j).comp
      (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  rw [affineSample_scaled_jet_identity l _ hf e ρ he yc z]
  calc
    _ ≤ (ocEpsilon q Λ (m - 1)) ^ l *
        ‖iteratedFDeriv ℝ l (fun y => naturalPreparationJacobian hφ s r y i j) (yc + e • z)‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hρ hρE l) (norm_nonneg _)
    _ ≤ _ := naturalPreparationJacobian_scaled_jet_bound hc ha hE s r hs hr hage n hn
      i j (yc + e • z) l hl

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Integrable fourth-moment bounds periodize genuine plane curves in L2 time. -/

variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [MeasurableSpace X] {K : ℕ}

theorem periodized_image_jet_time_memLp (μ : Measure X)
    (U : Set (Vec 2)) (R : ℝ) (hR : 0 < R) (hU : U ⊆ Metric.ball (0 : Vec 2) R)
    (z : Vec 2) (a : JetIndex2 K) (f : X → PlaneHk Set.univ K E) (hf : MemLp f 2 μ)
    (M : X → ℝ) (hM : MemLp M 2 μ)
    (hw : ∀ᵐ t ∂μ, AEStronglyMeasurable
      (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet a y) volume)
    (hb : ∀ᵐ t ∂μ, eLpNorm
      (fun y => (1 + ‖y - z‖) ^ 4 • (f t).toFunction.jet a y) 2 volume ≤ ENNReal.ofReal ‖M t‖) :
    MemLp (fun t => ∑' n : Fin 2 → ℤ,
      planeImageJetCLM U (AVenhance.latticeShift n) a (f t)) 2 μ := by
  let g : (Fin 2 → ℤ) → X → Lp E 2 (volume.restrict U) :=
    fun n t => planeImageJetCLM U (AVenhance.latticeShift n) a (f t)
  have hg (n : Fin 2 → ℤ) : AEStronglyMeasurable (g n) μ := by
    let L : PlaneHk Set.univ K E →L[ℝ] Lp E 2 (volume.restrict U) :=
      planeImageJetCLM U (AVenhance.latticeShift n) a
    exact (L.comp_memLp' hf).aestronglyMeasurable
  let b : (Fin 2 → ℤ) → ℝ := fun n =>
    (1 + R + ‖z‖) ^ 4 * (1 / spatialLatticeWeight n) ^ 2
  have hbound : ∀ᵐ t ∂μ, ∀ n, ‖g n t‖ ≤ b n * ‖M t‖ := by
    filter_upwards [hw, hb] with t ht hm
    intro n
    have hh := planeImageJetCLM_radial_norm_le U R hR hU z a (f t) ‖M t‖ (norm_nonneg _)
      ht hm n
    convert hh using 1
    ring
  exact memLp_tsum_of_summable_majorant μ g hg b
    (spatialLatticeReciprocal_square_summable.mul_left ((1 + R + ‖z‖) ^ 4)) M hM hbound

end AVRegularity.CycleJointProofs
end

section
open AVRegularity.ChartTransport
namespace AVRegularity.CycleJointProofs

/-! Explicit family-independent finite constants for the preparation sampling bridge. -/

def preparationSamplingFlowConstant (Jchart : ℕ) (Cchart : ℕ → ℝ) : ℝ :=
  1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|

def preparationSamplingJacobianConstant (D Kmax Jchart : ℕ) (Cchart : ℕ → ℝ) : ℝ :=
  compConst (preparationSamplingFlowConstant Jchart Cchart) (Kmax + D + 2) *
    preparationSamplingFlowConstant Jchart Cchart

def preparationSamplingJetConstant (D Kmax Jchart : ℕ) (Cchart : ℕ → ℝ) : ℝ :=
  let N := Kmax + D + 2
  let CK := preparationSamplingJacobianConstant D Kmax Jchart Cchart
  let Cflow := preparationSamplingFlowConstant Jchart Cchart
  (2 : ℝ) ^ (D + 1) *
    (((Kmax + 1 : ℕ) * (2 : ℝ) ^ Kmax) ^ 2 * CK *
      (3 * (N + 1 : ℕ) * 2 ^ N * CK) ^ D) *
    ((Kmax.factorial : ℝ) * Cflow ^ Kmax * ((Kmax + 1 : ℕ) *
      ((4 : ℝ) ^ Kmax * (Kmax.factorial : ℝ) ^ 2)))

def preparationSamplingSeminormConstant (D Kmax Jchart : ℕ) (Cchart : ℕ → ℝ) : ℝ :=
  ((Kmax + 1 : ℕ) * (2 : ℝ) ^ Kmax) * preparationSamplingJetConstant D Kmax Jchart Cchart

theorem preparationSamplingJetConstant_nonnegative (D Kmax Jchart : ℕ) (Cchart : ℕ → ℝ) :
    0 ≤ preparationSamplingJetConstant D Kmax Jchart Cchart := by
  have hf : 0 ≤ preparationSamplingFlowConstant Jchart Cchart :=
    zero_le_one.trans (one_le_jetConst _ _)
  have hk : 0 ≤ preparationSamplingJacobianConstant D Kmax Jchart Cchart :=
    zero_le_one.trans (preparation_jacobian_constant_ge_one Jchart Cchart (Kmax + D + 2))
  unfold preparationSamplingJetConstant
  dsimp only
  positivity

theorem preparationSamplingSeminormConstant_nonnegative (D Kmax Jchart : ℕ) (Cchart : ℕ → ℝ) :
    0 ≤ preparationSamplingSeminormConstant D Kmax Jchart Cchart :=
  mul_nonneg (by positivity) (preparationSamplingJetConstant_nonnegative D Kmax Jchart Cchart)

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Higher-order patch budgets on the genuine linear Sobolev localization maps. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem spatialPatchLocalization_derivativeNormSq_sum {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (N : ℕ) (hN : 0 < N) {K : ℕ} (f : TorusHk K E) (j : Fin (K + 1))
    (A : ℕ → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ l, l ≤ j.val → ∀ k x, ‖coefficientDerivativeArray
      (spatialPatchCoefficient (E := E) ζ N k) l x‖ ≤ A l) :
    (∑ p : Fin 2 → Fin N, derivativeNormSq
      (spatialPatchLocalization hζ N hN (fun i => (p i : ℤ)) K f).val j) ≤
      (Fintype.card (PositionMask j.val) : ℝ) *
        ∑ m : PositionMask j.val, (9 * A (maskLeftLength j.val m) ^ 2) *
          derivativeNormSq f.val
            ⟨maskRightLength j.val m,
              Nat.lt_succ_of_le ((maskRightLength_le j.val m).trans
                (Nat.le_of_lt_succ j.isLt))⟩ := by
  have he (p : Fin 2 → Fin N) (a : JetIndex2 K) :
      ‖(spatialPatchLocalization hζ N hN (fun i => (p i : ℤ)) K f).val a‖ ^ 2 =
        ∫ x, ‖multiplicationRawJet
          (spatialPatchCoefficient (E := E) ζ N (fun i => (p i : ℤ)))
          f.toFunction.jet a x‖ ^ 2 ∂volume :=
    localizeTorusCarrier_component_norm_sq f _
      (spatialPatchCoefficient_smooth hζ N _ K)
      (spatialPatchCoefficient_compact hζ N hN _) a
  have hf (a : JetIndex2 K) := torusHk_component_norm_sq f a
  unfold derivativeNormSq
  simp_rw [he, hf]
  exact spatialPatch_multiplicationRawJet_order_budget hζ N hN
    (Nat.le_of_lt_succ j.isLt) f.toFunction.jet f.toFunction.hasPeriodicWeakJet
    (torusHk_jet_measurable f) A hA hb

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Spatial freezing supplies the actual variational coefficient regularity and measurability. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]

theorem frozenMetric_diagonal_coefficients_finite (K : ι → ℕ)
    (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (ρ a b g : ℝ) (hg : 0 ≤ g)
    (hsym : ∀ t ∈ Set.Icc a b, (M t).IsSymm)
    (hquad : ∀ t ∈ Set.Icc a b, ∀ ξ : Vec 2,
      |∑ i, ∑ j, ξ i * (M t - (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j * ξ j| ≤
        g * ∑ i, ξ i ^ 2) (v u : ι) (d : admissibleOrders K 2 v u) :
    coefficientSeminorm ρ (K v) a b
      (planeDiagonalGradientCoefficient (h := h) K 2 (fun _ t _ => M t - 1) v u d) ≠ ⊤ := by
  by_cases huv : u = v
  · subst u
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (frozenMetric_diagonal_coefficientSeminorm_le K M ρ a b g hg hsym hquad v d)
  · rw [frozenMetric_offDiagonal_coefficient_zero K M v u d huv,
      CycleComparison.Coarse.coefficientSeminorm_zero_coefficient]
    exact ENNReal.zero_ne_top

theorem frozenMetric_diagonal_coefficient_contDiff (K : ι → ℕ)
    (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v u : ι) (d : admissibleOrders K 2 v u) (t : ℝ) :
    ContDiff ℝ (K v : ℕ)
      (planeDiagonalGradientCoefficient (h := h) K 2 (fun _ t _ => M t - 1) v u d t) := by
  change ContDiff ℝ (K v : ℕ) (fun _ : Vec 2 =>
    planeDiagonalGradientCoefficient (h := h) K 2 (fun _ t _ => M t - 1) v u d t 0)
  exact contDiff_const

theorem frozenMetric_diagonal_coefficient_measurable [∀ i, FiniteDimensional ℝ (h i)]
    (K : ι → ℕ) (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hM : Measurable M)
    (a b : ℝ) (v u : ι) (d : admissibleOrders K 2 v u) :
    Measurable (fun p : Set.Icc a b × Vec 2 =>
      planeDiagonalGradientCoefficient (h := h) K 2 (fun _ t _ => M t - 1) v u d p.1 p.2) := by
  by_cases huv : u = v
  · subst u
    have hd : d.1 = 2 := by
      have hh := Finset.mem_Icc.mp (Finset.mem_filter.mp d.2).1
      omega
    have heq : (fun p : Set.Icc a b × Vec 2 =>
        planeDiagonalGradientCoefficient (h := h) K 2 (fun _ t _ => M t - 1) v v d p.1 p.2) =
        fun p => metricFlux (h := h) (M p.1 - 1) (d.1 - 1) (a := v) rfl (by omega) := by
      funext p
      exact planeDiagonalGradientCoefficient_self_eq_metricFlux K 2 (fun _ t _ => M t - 1) v d hd p.1 p.2
    rw [heq]
    have hMM : Measurable (fun p : Set.Icc a b × Vec 2 => M p.1 - 1) := by
      apply measurable_pi_iff.mpr
      intro i
      apply measurable_pi_iff.mpr
      intro j
      exact (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hM)).comp
        (measurable_subtype_coe.comp measurable_fst)).sub measurable_const
    exact Weighted.metricFlux_measurable _ hMM (d.1 - 1) rfl (by omega)
  · have heq : (fun p : Set.Icc a b × Vec 2 =>
        planeDiagonalGradientCoefficient (h := h) K 2 (fun _ t _ => M t - 1) v u d p.1 p.2) = 0 := by
      funext p
      exact planeDiagonalGradientCoefficient_of_component_ne K 2 (fun _ t _ => M t - 1) v u d p.1 p.2 huv
    rw [heq]
    exact measurable_const

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Coefficient-weighted image weak pairings retain the summable spatial moment price. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] {K : ℕ}

omit [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] in
theorem localImage_coefficient_pairing_radial_bound (U : Set (Vec 2)) (R : ℝ) (hR : 0 < R)
    (hU : U ⊆ Metric.ball (0 : Vec 2) R) (z : Vec 2) (α : JetIndex2 K)
    (C : Vec 2 → E →L[ℝ] F) (hc : Continuous C) (MC : ℝ) (hMC : 0 ≤ MC)
    (hC : ∀ x, ‖C x‖ ≤ MC)
    (f : PlaneHk Set.univ K E) (g : Lp F 2 (volume.restrict U))
    (M : ℝ) (hM : 0 ≤ M)
    (hw : AEStronglyMeasurable (fun y => (1 + ‖y - z‖) ^ 4 • f.toFunction.jet α y) volume)
    (hb : eLpNorm (fun y => (1 + ‖y - z‖) ^ 4 • f.toFunction.jet α y) 2 volume ≤ ENNReal.ofReal M)
    (n : Fin 2 → ℤ) :
    ‖inner ℝ (boundedCoefficientL2CLM (U := U) C hc MC hMC hC
      (planeImageJetCLM U (AVenhance.latticeShift n) α f)) g‖ ≤
      (MC * (1 + R + ‖z‖) ^ 4 * M * ‖g‖) * (1 / spatialLatticeWeight n) ^ 2 := by
  calc
    _ ≤ ‖boundedCoefficientL2CLM (U := U) C hc MC hMC hC
        (planeImageJetCLM U (AVenhance.latticeShift n) α f)‖ * ‖g‖ :=
      norm_inner_le_norm _ _
    _ ≤ MC * ‖planeImageJetCLM U (AVenhance.latticeShift n) α f‖ * ‖g‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg g)
      exact ((boundedCoefficientL2CLM (U := U) C hc MC hMC hC).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (boundedCoefficientL2CLM_norm_le C hc MC hMC hC)
          (norm_nonneg _))
    _ ≤ MC * (((1 + R + ‖z‖) ^ 4 * M) * (1 / spatialLatticeWeight n) ^ 2) * ‖g‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (planeImageJetCLM_radial_norm_le U R hR hU z α f M hM hw hb n) hMC) (norm_nonneg g)
    _ = _ := by ring

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Polynomial-moment plane jets give actual torus carriers with literal component readouts. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

def periodizeRadialPlaneCarrier (f : PlaneHk Set.univ K E) (z : Vec 2)
    (hm : ∀ a, MemLp (fun y => (1 + ‖y - z‖) ^ 4 • f.toFunction.jet a y) 2 volume) :
    TorusHk K E :=
  (TorusHkFunction.mk (periodizeRawJet f.toFunction.jet)
    (periodizeRawJet_of_radial_moments f.toFunction.jet f.toFunction.hasWeakJet z
      (fun a => by simpa only [Measure.restrict_univ] using
        (f.toFunction.memL2 a).aestronglyMeasurable) hm)).toHk

theorem periodizeRadialPlaneCarrier_component_ae (f : PlaneHk Set.univ K E) (z : Vec 2)
    (hm : ∀ a, MemLp (fun y => (1 + ‖y - z‖) ^ 4 • f.toFunction.jet a y) 2 volume)
    (a : JetIndex2 K) :
    (periodizeRadialPlaneCarrier f z hm).val a =ᵐ[volume.restrict AVenhance.unitCube]
      periodizeRawJet f.toFunction.jet a := by
  have hp := periodizeRawJet_of_radial_moments f.toFunction.jet f.toFunction.hasWeakJet z
    (fun a => by simpa only [Measure.restrict_univ] using
      (f.toFunction.memL2 a).aestronglyMeasurable) hm
  exact torusJetToL2_ae (periodizeRawJet f.toFunction.jet) hp.2.1 a

theorem unitCube_subset_ball_two : AVenhance.unitCube ⊆ Metric.ball (0 : Vec 2) 2 := by
  intro x hx
  rw [Metric.mem_ball, dist_zero_right]
  apply (pi_norm_lt_iff (by norm_num)).mpr
  intro i
  have hi := hx i (Set.mem_univ i)
  rw [Real.norm_eq_abs, abs_of_pos hi.1]
  exact hi.2.trans (by norm_num)

theorem periodizeRadialPlaneCarrier_component_eq_series (f : PlaneHk Set.univ K E) (z : Vec 2)
    (hm : ∀ a, MemLp (fun y => (1 + ‖y - z‖) ^ 4 • f.toFunction.jet a y) 2 volume)
    (a : JetIndex2 K) :
    (periodizeRadialPlaneCarrier f z hm).val a =
      ∑' n : Fin 2 → ℤ, planeImageJetCLM AVenhance.unitCube (AVenhance.latticeShift n) a f := by
  let M := (eLpNorm (fun y => (1 + ‖y - z‖) ^ 4 • f.toFunction.jet a y) 2 volume).toReal
  have he : eLpNorm (fun y => (1 + ‖y - z‖) ^ 4 • f.toFunction.jet a y) 2 volume =
      ENNReal.ofReal M := (ENNReal.ofReal_toReal (hm a).eLpNorm_lt_top.ne).symm
  have hs := planeImageJetCLM_radial_enorm_tsum_lt_top AVenhance.unitCube 2 (by norm_num)
    unitCube_subset_ball_two z a f M ENNReal.toReal_nonneg (hm a).aestronglyMeasurable he.le
  apply Lp.ext
  exact (periodizeRadialPlaneCarrier_component_ae f z hm a).trans
    (periodized_image_jet_series_ae AVenhance.unitCube a f hs).symm

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVenhance AVRegularity.CycleWords AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The actual family remainder has measurable time dependence and spatial jets
on the rescaled preparation interval, with a fixed reference chart time. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem inactiveTimeZeroFamily_natural_remainder_time_regularity
    (F : ChartedFamily ι h D P Ctx) (hw : ∀ p, Measurable (F.weight p))
    (hm : F.IsTimeMeasurable) (W : Set ℝ) (E e : ℝ) (hE : E ≠ 0) (he : e ≠ 0)
    (n : ι → ℕ) (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F W) E n)
    (Ks N : ℕ) (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u)
    (d : ℕ) (I : DerivativeWord2 (d - 1)) (k : Fin 2) (horder : Ks + N ≤ n v)
    (timeScale a b : ℝ) (htime : ∀ t ∈ Set.Icc a b, timeScale * t ∈ W)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (r σ : ℝ) (yc : Vec 2) :
    let f := fun t X z => (inactiveTimeZeroFamily F).flux p c v u γ d I (timeScale * t) X z k
    (∀ z, Measurable (fun t =>
      naturalSlowRemainderTimeCoefficient Ks f a b hφ r (fun _ => σ) e E yc t z)) ∧
    (∀ t, ContDiff ℝ (N : ℕ)
      (naturalSlowRemainderTimeCoefficient Ks f a b hφ r (fun _ => σ) e E yc t)) := by
  let F0 := inactiveTimeZeroFamily F
  let f := fun t X z => F0.flux p c v u γ d I (timeScale * t) X z k
  have hm0 := inactiveTimeZeroFamily_time_measurable F hw hm
  have hs0 := inactiveTimeZeroFamily_smooth_window F W E n hs
  have hfm X z : Measurable (fun t => f t X z) :=
    ((measurable_pi_apply k).comp (hm0 p c v u γ d I X z)).comp
      (measurable_const.mul measurable_id)
  have hfs t (ht : t ∈ Set.Icc a b) :
      ContDiff ℝ (Ks + N : ℕ) (Function.uncurry (f t)) := by
    have hh := molecular_joint_contDiff F0 (fun _ _ => W ×ˢ Set.univ) E hE n hs0
      p c (timeScale * t) (fun Y => ⟨htime t ht, Set.mem_univ Y⟩) v u γ d I
    have hhN : ContDiff ℝ (Ks + N : ℕ)
        (Function.uncurry (F0.flux p c v u γ d I (timeScale * t))) :=
      hh.of_le (by exact_mod_cast horder)
    exact (ContinuousLinearMap.proj k).contDiff.comp hhN
  constructor
  · intro z
    exact naturalSlowRemainderTimeCoefficient_measurable Ks f a b hfm
      (fun t ht => (hfs t ht).of_le (by exact_mod_cast Nat.le_add_right Ks N))
      hφ r (fun _ => σ) measurable_const e E yc z
  · exact naturalSlowRemainderTimeCoefficient_spatial_contDiff Ks N f a b hfs
      hφ r (fun _ => σ) e E he yc

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Actual constituent coefficients inherit positive active-piece budgets without counting pieces. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem positive_constituentPhysical_jet_assembly (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
    (ν e E : ℝ) (actual : ∀ p, Ctx p) (v u : ι) (γ : F.Γ v u)
    (d n : ℕ) (ρ B : ℝ) (hρ : 0 ≤ ρ) (hB : 0 ≤ B) (t : Set.Icc tS tZ)
    (g : P' → Vec 2 →
      ((PiLp 2 (fun _ : DerivativeWord2 (d - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))))
    (hg : ∀ p y, g p y = nativeArrayAssembly (d - 1) (F.identity v u γ).map
      (fun a A => transportedCoeff (naturalPreparationJacobian hφ (F.piece p).anchor t)
        (F.identity v u γ).maxOrder
        (fun d' I => F.dimFlux ν e E p (actual p) v u γ d' I t
          (streamFlow φ hφ (F.piece p).anchor y t)
          (e⁻¹ • streamFlow φ hφ (F.piece p).anchor y t)) (d - 1) A y a))
    (hgs : ∀ p, (t : ℝ) ∈ (F.piece p).output → ContDiff ℝ (n : ℕ) (g p))
    (hjet : ∀ p, (t : ℝ) ∈ (F.piece p).output → ∀ y,
      ρ ^ n * ‖iteratedFDeriv ℝ n (g p) y‖ ≤ B) (x : Vec 2) :
    ρ ^ n * ‖iteratedFDeriv ℝ n
      (constituentPhysical F ν e E actual v u γ d t) x‖ ≤ B := by
  let f := fun p y => F.weight p t • g p y
  have he : constituentPhysical F ν e E actual v u γ d t = fun y => ∑ᶠ p, f p y := by
    funext y
    unfold constituentPhysical
    apply finsum_congr
    intro p
    change F.weight p t • (nativeArrayAssembly (d - 1) (F.identity v u γ).map _) = _
    rw [weighted_piece_operator_eq_natural F hc ν e E p (actual p) v u γ (d - 1) t y]
    rw [← hg p y]
  rw [he]
  have hz p (hout : (t : ℝ) ∉ (F.piece p).output) : f p = fun _ => 0 := by
    funext y
    dsimp only [f]
    rw [F.weight_zero p t hout]
    exact zero_smul ℝ (g p y)
  apply positive_piece_jet_assembly_total F tS tZ t t.property f n
    (fun p => by
      by_cases hout : (t : ℝ) ∈ (F.piece p).output
      · exact (hgs p hout).const_smul _
      · rw [hz p hout]
        exact contDiff_const) _ ρ B hρ hB _ x
  · intro p y hout
    exact congrFun (hz p hout) y
  · intro p y
    by_cases hout : (t : ℝ) ∈ (F.piece p).output
    · dsimp only [f]
      rw [iteratedFDeriv_const_smul_apply' (hgs p hout).contDiffAt, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg (F.weight_nonneg p t)]
      have hh := mul_le_mul_of_nonneg_left (hjet p hout y) (F.weight_nonneg p t)
      convert hh using 1; ring
    · rw [hz p hout, iteratedFDeriv_fun_zero, F.weight_zero p t hout]
      simp only [Pi.zero_apply, norm_zero, mul_zero, zero_mul, le_refl]

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleJointProofs

/-! Absolute local image convergence passes coefficient-weighted weak tests through periodization. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] {K L : ℕ}

theorem summed_compact_coefficient_pairing (U : Set (Vec 2))
    (C : Vec 2 → E →L[ℝ] F) (hc : Continuous C)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, ‖C x‖ ≤ M)
    (f : PlaneHk Set.univ K E) (α : JetIndex2 K)
    (φ : PlaneHk Set.univ L F) (β : JetIndex2 L)
    (hφ : ∀ᵐ x ∂volume, x ∉ U → φ.toFunction.jet β x = 0)
    (hs : (∑' n : Fin 2 → ℤ, ‖planeImageJetCLM U (AVenhance.latticeShift n) α f‖ₑ) < ⊤) :
    (∑' n : Fin 2 → ℤ, ∫ x,
      inner ℝ (C x ((planeCarrierTranslation K (AVenhance.latticeShift n) f).toFunction.jet α x))
        (φ.toFunction.jet β x)) =
      ∫ x, inner ℝ (C x (periodizeRawJet f.toFunction.jet α x)) (φ.toFunction.jet β x) := by
  let g := restrictPlaneLpCLM U (planeJetReadoutOperator L β φ)
  let T := boundedCoefficientL2CLM (U := U) C hc M hM hb
  let a := fun n : Fin 2 → ℤ => planeImageJetCLM U (AVenhance.latticeShift n) α f
  have ha : Summable a := Summable.of_enorm hs.ne
  have hg : g =ᵐ[volume.restrict U] φ.toFunction.jet β :=
    (restrictPlaneLpCLM_ae U _).trans ((univToPlane_ae (φ.val β)).restrict (s := U))
  have hseries := periodized_image_jet_series_ae U α f hs
  have hmult := boundedCoefficientL2_ae C hc M hM hb (∑' n, a n)
  have hsupport : ∀ᵐ x ∂volume, x ∉ U →
      inner ℝ (C x (periodizeRawJet f.toFunction.jet α x)) (φ.toFunction.jet β x) = 0 := by
    filter_upwards [hφ] with x hx hxu
    rw [hx hxu, inner_zero_right]
  calc
    _ = ∑' n : Fin 2 → ℤ, inner ℝ (T (a n)) g := tsum_congr (fun n =>
      translated_compact_coefficient_pairing U (AVenhance.latticeShift n)
        C hc hM hb f α φ β hφ)
    _ = inner ℝ (∑' n : Fin 2 → ℤ, T (a n)) g := (inner_hilbert_tsum (T.summable ha) g).symm
    _ = inner ℝ (T (∑' n : Fin 2 → ℤ, a n)) g := by rw [T.map_tsum ha]
    _ = ∫ x in U, inner ℝ (C x (periodizeRawJet f.toFunction.jet α x))
        (φ.toFunction.jet β x) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hmult, hseries, hg] with x hx hy hz
      exact congrArg₂ (inner ℝ) (hx.trans (congrArg (C x) hy)) hz
    _ = _ := setIntegral_eq_integral_of_ae_compl_eq_zero hsupport

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVenhance AVenhance.Infra.Section5 AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Joint measurability of each weighted actual inverse-Piola array on the observation window. -/

section
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem weighted_piece_array_joint_measurable
    (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
    (ν e E : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ)) E n)
    (hmeas : F.IsTimeMeasurable) (hwmeas : ∀ p, Measurable (F.weight p))
    (p : P') (c : Ctx p) (v u : ι) (γ : F.Γ v u)
    (r : ℕ) (A : DerivativeWord2 r) (a : Fin 2) :
    Measurable (fun z : Set.Icc tS tZ × Vec 2 => F.weight p z.1 *
      transportedCoeff (chartInvJacobian ⇑((F.piece p).material z.1).symm)
        (F.identity v u γ).maxOrder
        (fun d I => F.dimFlux ν e E p c v u γ d I z.1
          (((F.piece p).material z.1).symm z.2)
          (e⁻¹ • ((F.piece p).material z.1).symm z.2)) r A z.2 a) := by
  let K := naturalPreparationJacobian hφ (F.piece p).anchor
  let B := fun d (I : DerivativeWord2 (d - 1)) (z : Set.Icc tS tZ × Vec 2) =>
    F.weight p z.1 • F.dimFlux ν e E p c v u γ d I z.1
      (streamFlow φ hφ (F.piece p).anchor z.2 z.1)
      (e⁻¹ • streamFlow φ hφ (F.piece p).anchor z.2 z.1)
  have hB : ∀ d I i, Measurable (fun z => B d I z i) := by
    intro d I i
    exact (measurable_pi_apply i).comp
      (weighted_natural_sample_joint_measurable F ν e E tS tZ n hs hmeas hwmeas
        hφ p c v u γ d I)
  have hm := transportedCoeff_joint_measurable tS tZ K
    (naturalPreparationJacobian_entry_smooth hφ (F.piece p).anchor)
    (F.identity v u γ).maxOrder B hB r A a
  convert hm using 1
  funext z
  dsimp [B, K]
  rw [transportedCoeff_smul_native]
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hw : F.weight p z.1 = 0
  · simp only [hw, zero_mul]
  have ht : (z.1 : ℝ) ∈ (F.piece p).output := by
    by_contra hout
    exact hw (F.weight_zero p z.1 hout)
  have hp : ((F.piece p).output ∩ Set.Icc tS tZ).Nonempty :=
    ⟨z.1, ht, z.1.property⟩
  rw [preparation_inverseJacobian_eq_natural hc p hp z.1 ((F.piece p).output_subset ht),
    preparation_inverse_material_eq_streamFlow hc p hp z.1 ((F.piece p).output_subset ht)]
end

/-! The retained weighted Piola array in a fixed reference chart is jointly measurable. -/

section
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem weighted_reference_piece_array_joint_measurable
    (F : ChartedFamily ι h D P Ctx) (ν e E tA tZ : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc tA tZ)) E n)
    (hmeas : F.IsTimeMeasurable) (hwmeas : ∀ p, Measurable (F.weight p))
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (s : ℝ)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u)
    (r : ℕ) (A : DerivativeWord2 r) (a : Fin 2) :
    Measurable (fun z : Set.Icc tA tZ × Vec 2 => F.weight p z.1 *
      transportedCoeff (naturalPreparationJacobian hφ (F.piece p).anchor s)
        (F.identity v u γ).maxOrder
        (fun d I => F.dimFlux ν e E p c v u γ d I z.1
          (streamFlow φ hφ (F.piece p).anchor z.2 s)
          (e⁻¹ • streamFlow φ hφ (F.piece p).anchor z.2 s)) r A z.2 a) := by
  let K := fun (_ : ℝ) => naturalPreparationJacobian hφ (F.piece p).anchor s
  let B := fun d (I : DerivativeWord2 (d - 1)) (z : Set.Icc tA tZ × Vec 2) =>
    F.weight p z.1 • F.dimFlux ν e E p c v u γ d I z.1
      (streamFlow φ hφ (F.piece p).anchor z.2 s)
      (e⁻¹ • streamFlow φ hφ (F.piece p).anchor z.2 s)
  have hB : ∀ d I i, Measurable (fun z => B d I z i) := by
    intro d I i
    exact (measurable_pi_apply i).comp
      (weighted_fixed_flow_sample_joint_measurable F ν e E tA tZ n hs hmeas hwmeas
        hφ s p c v u γ d I)
  have hK (i j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : ℝ × Vec 2 => K z.1 z.2 i j) :=
    (naturalPreparationJacobian_entry_smooth hφ (F.piece p).anchor i j).comp
      (contDiff_const.prodMk contDiff_snd)
  have hm := transportedCoeff_joint_measurable tA tZ K hK
    (F.identity v u γ).maxOrder B hB r A a
  convert hm using 1
  funext z
  dsimp [B, K]
  rw [transportedCoeff_smul_native]
  simp only [Pi.smul_apply, smul_eq_mul]
end

end AVRegularity.CycleJointProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleJointProofs

/-! Absolute image convergence gives genuine integrability of each periodized compact weak pairing. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] {K L : ℕ}

theorem periodized_compact_coefficient_pairing_integrable (U : Set (Vec 2)) (hU : MeasurableSet U)
    (C : Vec 2 → E →L[ℝ] F) (hc : Continuous C)
    (MC : ℝ) (hMC : 0 ≤ MC) (hC : ∀ x, ‖C x‖ ≤ MC)
    (f : PlaneHk Set.univ K E) (α : JetIndex2 K)
    (φ : PlaneHk Set.univ L F) (β : JetIndex2 L)
    (hφ : ∀ᵐ x ∂volume, x ∉ U → φ.toFunction.jet β x = 0)
    (hs : (∑' n : Fin 2 → ℤ, ‖planeImageJetCLM U (AVenhance.latticeShift n) α f‖ₑ) < ⊤) :
    Integrable (fun x => inner ℝ (C x (periodizeRawJet f.toFunction.jet α x))
      (φ.toFunction.jet β x)) volume := by
  let u := ∑' n : Fin 2 → ℤ, planeImageJetCLM U (AVenhance.latticeShift n) α f
  let g := restrictPlaneLpCLM U (planeJetReadoutOperator L β φ)
  have hg : g =ᵐ[volume.restrict U] φ.toFunction.jet β :=
    (restrictPlaneLpCLM_ae U _).trans ((univToPlane_ae (φ.val β)).restrict (s := U))
  have hu := periodized_image_jet_series_ae U α f hs
  have hA := boundedCoefficientL2_ae C hc MC hMC hC u
  have hi : IntegrableOn (fun x => inner ℝ (C x (periodizeRawJet f.toFunction.jet α x))
      (φ.toFunction.jet β x)) U volume := by
    apply (L2.integrable_inner (𝕜 := ℝ) (boundedCoefficientL2 C hc MC hMC hC u) g).congr
    filter_upwards [hA, hu, hg] with x hx hy hz
    exact congrArg₂ (inner ℝ) (hx.trans (congrArg (C x) hy)) hz
  apply ((integrable_indicator_iff hU).mpr hi).congr
  filter_upwards [hφ] with x hx
  by_cases hxu : x ∈ U
  · rw [Set.indicator_of_mem hxu]
  · rw [Set.indicator_of_notMem hxu, hx hxu, inner_zero_right]

end AVRegularity.CycleJointProofs
end
