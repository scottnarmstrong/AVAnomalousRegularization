-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleJoint.PlaneScalarDiffusionDeviationReadout
public import AVRegularity.CycleJoint.ConstituentPhysicalOrderSupport
public import AVRegularity.CycleWords.GeometryPieceNonempty
import AVRegularity.Weighted.MetricWordCoefficientArrayBound
public import AVRegularity.CycleReference.ChartTestTransport
public import AVRegularity.Weighted.PlaneIntervalCoefficients

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Every actual constituent physical coefficient is the finite weighted piece sum on the preparation window. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem constituentPhysical_eq_window_sum
    (F : ChartedFamily ι h D P Ctx) (ν e E : ℝ) (actual : ∀ p, Ctx p)
    (a b t : ℝ) (ht : t ∈ Set.Icc a b) (v u : ι) (γ : F.Γ v u)
    (d : ℕ) (x : Vec 2) :
    constituentPhysical F ν e E actual v u γ d t x =
      ∑ p ∈ (F.locally_finite a b).toFinset,
        F.weight p t • nativeArrayAssembly (d - 1) (F.identity v u γ).map
          (fun k A => transportedCoeff (chartInvJacobian ⇑((F.piece p).material t).symm)
            (F.identity v u γ).maxOrder
            (fun d' I => F.dimFlux ν e E p (actual p) v u γ d' I t
              (((F.piece p).material t).symm x)
              (e⁻¹ • ((F.piece p).material t).symm x)) (d - 1) A x k) := by
  exact piece_finsum_eq_window_sum (V :=
    (PiLp 2 (fun _ : DerivativeWord2 (d - 1) => h u)) →L[ℝ]
      (PiLp 2 (fun _ : Fin 2 => h v))) F a b t ht
    (fun p => F.weight p t • nativeArrayAssembly (d - 1) (F.identity v u γ).map
          (fun k A => transportedCoeff (chartInvJacobian ⇑((F.piece p).material t).symm)
            (F.identity v u γ).maxOrder
            (fun d' I => F.dimFlux ν e E p (actual p) v u γ d' I t
              (((F.piece p).material t).symm x)
              (e⁻¹ • ((F.piece p).material t).symm x)) (d - 1) A x k))
    (fun p hp => by
      rw [F.weight_zero p t hp]
      ext g k
      simp only [smul_apply, zero_smul, zero_apply, PiLp.zero_apply])

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public section
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! A fixed upper bound on the mass-conjugated Schur size suffices for a
uniform residual price; the actual size need not be at most one. -/

theorem coupledRetainedResidualPrice_source_scale_budget
    (C cm cs ct θ θcap ζ η G0 : ℝ≥0∞) (hθ : θ ≤ θcap) (p J H : ℕ) :
    (cm * ζ ^ (2 * p) * retainedResponseEnergyPrice C θ J H) * G0 +
      (cs * ζ ^ (2 * p) * retainedResponseEnergyPrice C θ J H) * G0 +
      (ct * terminalResponseEnergyPrice C θ J H * η ^ (2 * (J + 1))) * G0 ≤
    coupledRetainedResidualPrice (C * (1 + θcap ^ 2)) cm cs ct J H *
      (ζ ^ (2 * p) + η ^ (2 * (J + 1))) * G0 := by
  have hr := retainedResponseEnergyPrice_source_scale C θ θcap hθ J H
  have ht := terminalResponseEnergyPrice_source_scale C θ θcap hθ J H
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hr (show 0 ≤ cm * ζ ^ (2 * p) from zero_le)) (show 0 ≤ G0 from zero_le)
  have hs := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hr (show 0 ≤ cs * ζ ^ (2 * p) from zero_le)) (show 0 ≤ G0 from zero_le)
  have hterm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht (show 0 ≤ ct from zero_le))
      (show 0 ≤ η ^ (2 * (J + 1)) from zero_le)) (show 0 ≤ G0 from zero_le)
  exact (add_le_add (add_le_add hm hs) hterm).trans
    (coupledRetainedResidualPrice_budget (C * (1 + θcap ^ 2)) cm cs ct 1 ζ η G0 le_rfl p J H)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The coefficient assembly `nativeArrayAssembly` has its literal finite scalar constituent
action. -/

section
variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem nativeArrayAssembly_apply (r : ℕ) (C : U →L[ℝ] V)
    (b : Fin 2 → DerivativeWord2 r → ℝ)
    (g : PiLp 2 (fun _ : DerivativeWord2 r => U)) (k : Fin 2) :
    nativeArrayAssembly r C b g k = ∑ A : DerivativeWord2 r, b k A • C (g A) := by
  simp [nativeArrayAssembly]
end

/-! Spatial smoothness passes through the finite scalar-to-operator assembly. -/

section
variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem nativeArrayAssembly_spatial_smooth (r n : ℕ) (C : U →L[ℝ] V)
    (b : Vec 2 → Fin 2 → DerivativeWord2 r → ℝ)
    (hb : ∀ k A, ContDiff ℝ (n : ℕ) (fun x => b x k A)) :
    ContDiff ℝ (n : ℕ) (fun x => nativeArrayAssembly r C (b x)) := by
  have hc : ContDiff ℝ (n : ℕ) (nativeArrayAssembly r C) :=
    (LinearMap.toContinuousLinearMap (nativeArrayAssembly r C)).contDiff
  exact hc.comp (contDiff_pi.mpr (fun k => contDiff_pi.mpr (hb k)))
end

/-! A zero original component map annihilates its entire native Piola array. -/

section
variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem nativeArrayAssembly_zero_component_map (r : ℕ)
    (b : Fin 2 → DerivativeWord2 r → ℝ) :
    nativeArrayAssembly r (0 : U →L[ℝ] V) b = 0 := by
  ext g k
  simp [nativeArrayAssembly]
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleJointProofs

/-! Extracting the source after adding and subtracting its actual remainder recovers the exact family map. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {V Q : ι → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
  [∀ i, AddCommGroup (Q i)] [∀ i, Module ℝ (Q i)]

theorem nativeFamilyMapEdge_add_sub_assembly
    (T R : ∀ v, (∀ u, V u) →ₗ[ℝ] Q v) (v : ι) :
    nativeFamilyEdgeForcingMap (nativeFamilyMapEdge (fun i => T i + R i - R i)) v = T v := by
  have he : (fun i => T i + R i - R i) = T := funext (fun i => add_sub_cancel_right _ _)
  rw [he, nativeFamilyMapEdge_assembly]
end

/-! Native causal response fixed points retain the zeroth curve and eliminate the top inherited source boundary using the original graph. -/

section
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℝ (V i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem finiteNativeResponse_source_boundary_zero (F : ChartedFamily ι h D P Ctx)
    (R M S : Module.End ℝ (∀ i, V i))
    (hR : HasSourceDegreeOn F 0 R) (hM : HasSourceDegreeOn F 0 M)
    (hS : HasSourceDegreeOn F 1 S) (H : ℕ) (hdepth : F.HasDepthAtMost H)
    (f : ∀ i, V i) (j : ℕ) : S (finiteResponse R M S f j H) = 0 := by
  have hd : HasSourceDegreeOn F (H + 1) (S * finiteResponseOperator R M S j H) := by
    simpa only [Nat.add_comm 1 H] using sourceDegreeOn_mul hS
      (finiteNativeResponseOperator_sourceDegree F R M S hR hM hS j H)
  have hz := sourceDegreeOn_gt_depth_zero hdepth (Nat.lt_succ_self H) hd
  have he := congrArg (fun T : Module.End ℝ (∀ i, V i) => T f) hz
  simpa only [Module.End.mul_apply, finiteResponseOperator_apply, LinearMap.zero_apply] using he

theorem finiteNativeResponse_fixedPoint_source_residual (F : ChartedFamily ι h D P Ctx)
    (M S : Module.End ℝ (∀ i, V i))
    (hM : HasSourceDegreeOn F 0 M) (hS : HasSourceDegreeOn F 1 S)
    (H J : ℕ) (hdepth : F.HasDepthAtMost H) (f : ∀ i, V i) :
    let U := finiteResponse 1 M S f
    let W := ∑ j ∈ Finset.range (J + 1), ∑ n ∈ Finset.range (H + 1), U j n
    W - M W - S W = f - M (∑ n ∈ Finset.range (H + 1), U J n) := by
  have he := finiteResponse_native_fixedPoint_residual M S f J H
  dsimp only at he ⊢
  have htop : S (∑ j ∈ Finset.range (J + 1), finiteResponse 1 M S f j H) = 0 := by
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro j _
    exact finiteNativeResponse_source_boundary_zero F 1 M S (sourceDegreeOn_one F)
      hM hS H hdepth f j
  rw [htop, sub_zero] at he
  exact he
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Exact Piola transport preserves the original-array polynomial and remainder split. -/

section
theorem transportedCoeff_add_native
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (Dγ : ℕ)
    (B C : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2)
    (r : ℕ) (A : DerivativeWord2 r) (y : Vec 2) :
    transportedCoeff K Dγ (fun d I => B d I + C d I) r A y =
      transportedCoeff K Dγ B r A y + transportedCoeff K Dγ C r A y := by
  funext a
  simp only [transportedCoeff, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem transportedCoeff_remainder_split
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (Dγ : ℕ)
    (B P : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2)
    (r : ℕ) (A : DerivativeWord2 r) (y : Vec 2) :
    transportedCoeff K Dγ B r A y =
      transportedCoeff K Dγ P r A y +
        transportedCoeff K Dγ (fun d I => B d I - P d I) r A y := by
  rw [← transportedCoeff_add_native]
  congr 1
  funext d I
  exact (add_sub_cancel_left (P d I) (B d I)).symm.trans
    (add_sub_assoc (P d I) (B d I) (P d I))

variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem nativeArrayAssembly_transported_remainder_split
    (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (Dγ : ℕ)
    (B P : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2)
    (r : ℕ) (C : U →L[ℝ] V) (y : Vec 2) :
    nativeArrayAssembly r C (fun a A => transportedCoeff K Dγ B r A y a) =
      nativeArrayAssembly r C (fun a A => transportedCoeff K Dγ P r A y a) +
      nativeArrayAssembly r C
        (fun a A => transportedCoeff K Dγ (fun d I => B d I - P d I) r A y a) := by
  rw [← (nativeArrayAssembly r C).map_add]
  congr 1
  funext a A
  exact congrFun (transportedCoeff_remainder_split K Dγ B P r A y) a
end

/-! Descending physical slots retain every current order of each original constituent exactly once. -/

section
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem constituentPhysical_order_reindex
    (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ) (hdesc : F.IsDescending K)
    (ν e E : ℝ) (actual : ∀ p, Ctx p) (v u : ι) (γ : F.Γ v u) (t : ℝ) (x : Vec 2)
    (g : ∀ d : ℕ, PiLp 2 (fun _ : DerivativeWord2 (d - 1) => h u)) :
    (∑ d : admissibleOrders K D v u, constituentPhysical F ν e E actual v u γ d t x (g d)) =
      ∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder,
        constituentPhysical F ν e E actual v u γ d t x (g d) := by
  classical
  rw [Finset.sum_coe_sort (admissibleOrders K D v u)
    (fun d => constituentPhysical F ν e E actual v u γ d t x (g d))]
  have hz (d : ℕ) : constituentPhysical F ν e E actual v u γ d t x (g d) =
      if d ≤ (F.identity v u γ).maxOrder then
        constituentPhysical F ν e E actual v u γ d t x (g d) else 0 := by
    by_cases hd : d ≤ (F.identity v u γ).maxOrder
    · rw [ite_eq_left hd]
    · rw [ite_eq_right hd, constituentPhysical_zero_above_max F ν e E actual v u γ d
        (Nat.lt_of_not_ge hd) t x]
      rfl
  have he : (∑ d ∈ admissibleOrders K D v u,
      constituentPhysical F ν e E actual v u γ d t x (g d)) =
      ∑ d ∈ admissibleOrders K D v u, if d ≤ (F.identity v u γ).maxOrder then
        constituentPhysical F ν e E actual v u γ d t x (g d) else 0 :=
    Finset.sum_congr rfl (fun d _ => hz d)
  rw [he]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext d
    simp only [Finset.mem_filter, admissibleOrders, Finset.mem_Icc]
    constructor
    · intro hd
      exact ⟨hd.1.1.1, hd.2⟩
    · intro hd
      have hmax := (F.identity v u γ).le_D
      have hk := hdesc v u γ
      exact ⟨⟨⟨hd.1, hd.2.trans hmax⟩, by omega⟩, hd.2⟩
  · intro d hd
    rfl
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The actual coefficient product preserves scalar-weighted L² jets. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

/-- The genuine product carrier retains every finite scalar moment of its source jets. -/
theorem planeMulCoefficient_weight_memL2On {K : ℕ} (U : PlaneHk Set.univ K E)
    (C : Vec 2 → E →L[ℝ] F) (hC : ContDiff ℝ (K : ℕ) C)
    {A : Fin (K + 1) → ℝ}
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l)
    (q : Vec 2 → ℝ) (hD : JetMemL2On Set.univ (fun β x => q x • U.toFunction.jet β x)) :
    JetMemL2On Set.univ (fun β x => q x • (U.mulCoefficient C hC hb).toFunction.jet β x) := by
  intro β
  have hm := multiplicationRawJet_weight_memL2On C hC U.toFunction.jet q hD hb β
  simp only [Measure.restrict_univ] at hm ⊢
  apply MemLp.ae_eq (hf_Lp := hm)
  filter_upwards [planeMulCoefficient_rawJet_ae U C hC hb β] with x hx
  exact congrArg (fun v => q x • v) hx.symm

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Smooth original chart weights remain certificates for a clamped metric on the native window. -/

def chartWeightsMetricClamp {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    {v : ℝ → Vec 2 → Vec 2} {a b ϖ : ℝ} {zc : Vec 2} {N : ℕ} {Cw : ℕ → ℝ}
    (C : ChartWeights G v a (b - a) ϖ zc N Cw) :
    ChartWeights (metricClamp a b G) v a (b - a) ϖ zc N Cw :=
  chartWeightsOfEqOn C (fun t ht => metricClamp_of_mem G
    (by simpa only [add_sub_cancel] using ht))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Operator-valued iterated jet bounds control the exact ordered coefficient array. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem coefficient_array_iterated_jet_bound (A : Vec 2 → E →L[ℝ] F)
    (j : ℕ) (hA : ContDiff ℝ (j : ℕ) A) (x : Vec 2) :
    ‖coefficientDerivativeArray A j x‖ ≤
      (Fintype.card (DerivativeWord2 j) : ℝ) * ‖iteratedFDeriv ℝ j A x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  calc
    _ ≤ ∑ w : DerivativeWord2 j, ‖coefficientDerivativeArray A j x z w‖ :=
      Weighted.finitePiLp_norm_le_sum _
    _ ≤ ∑ _w : DerivativeWord2 j, ‖iteratedFDeriv ℝ j A x‖ * ‖z‖ := by
      apply Finset.sum_le_sum
      intro w _
      exact ((orderedCoefficientDerivative A j w x).le_opNorm z).trans
        (mul_le_mul_of_nonneg_right
          (Weighted.orderedCoefficientDerivative_norm_le A j hA w x) (norm_nonneg z))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

theorem coefficient_array_normalized_jet_bound (A : Vec 2 → E →L[ℝ] F)
    (j : ℕ) (hA : ContDiff ℝ (j : ℕ) A) (x : Vec 2)
    (ρ M : ℝ) (hρ : 0 ≤ ρ) (hb : ρ ^ j * ‖iteratedFDeriv ℝ j A x‖ ≤ M) :
    ρ ^ j * ‖coefficientDerivativeArray A j x‖ ≤ (2 : ℝ) ^ j * M := by
  have hh := mul_le_mul_of_nonneg_left
    (coefficient_array_iterated_jet_bound A j hA x) (pow_nonneg hρ j)
  have hc : (Fintype.card (DerivativeWord2 j) : ℝ) = (2 : ℝ) ^ j := by
    simp [DerivativeWord2]
  rw [hc, mul_left_comm] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hb (by positivity))
end

/-! Resolve the native array assembly into fixed coordinate operators. -/

section
variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem nativeArrayAssembly_expansion (r : ℕ) (C : U →L[ℝ] V)
    (b : Fin 2 → DerivativeWord2 r → ℝ) :
    nativeArrayAssembly r C b = ∑ k : Fin 2, ∑ A : DerivativeWord2 r,
      b k A • (Weighted.fluxCoordinateInjection k C).comp
        (PiLp.proj 2 (fun _ : DerivativeWord2 r => U) A) := by
  classical
  ext g j
  fin_cases j <;> simp [nativeArrayAssembly, Weighted.fluxCoordinateInjection,
    ContinuousLinearMap.comp_apply, PiLp.continuousLinearEquiv_symm_apply]
end

/-! Resolve the literal native array action into its positive scalar coordinate constituents. -/

section
variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem nativeArrayAssembly_value_expansion (r : ℕ) (C : U →L[ℝ] V)
    (b : Fin 2 → DerivativeWord2 r → ℝ) (u : DerivativeWord2 r → U) :
    nativeArrayAssembly r C b (WithLp.toLp 2 u) =
      ∑ a : Fin 2, ∑ I : DerivativeWord2 r, b a I • Weighted.fluxCoordinateInjection a C (u I) := by
  classical
  apply PiLp.ext
  intro a
  fin_cases a <;> simp [nativeArrayAssembly, ContinuousLinearMap.comp_apply,
    PiLp.continuousLinearEquiv_symm_apply, Weighted.fluxCoordinateInjection_apply, Finset.sum_apply]
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Conditional pointwise adapter for the coefficient seminorm `coefficientSeminorm`, distinct from
AE budgets. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem pointwise_coefficient_seminorm_budget (ρ : ℝ) (hρ : 0 < ρ) (K : ℕ)
    (a b : ℝ) (A : ℝ → Vec 2 → E →L[ℝ] F)
    (hA : ∀ t ∈ Set.Icc a b, ContDiff ℝ (K : ℕ) (A t))
    (M : ℕ → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hb : ∀ t ∈ Set.Icc a b, ∀ j, j ≤ K → ∀ x,
      ρ ^ j * ‖iteratedFDeriv ℝ j (A t) x‖ ≤ M j) :
    coefficientSeminorm ρ K a b A ≤
      ENNReal.ofReal (∑ j ∈ Finset.range (K + 1), (2 : ℝ) ^ j * M j / (j.factorial : ℝ)) := by
  unfold coefficientSeminorm
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ =>
    div_nonneg (mul_nonneg (by positivity) (hM j)) (by positivity))]
  apply Finset.sum_le_sum
  intro j hj
  have hjK : j ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hp : 0 < ρ ^ j := pow_pos hρ j
  have hsup : (⨆ t ∈ Set.Icc a b, ⨆ x : Vec 2,
      (‖coefficientDerivativeArray (A t) j x‖₊ : ℝ≥0∞)) ≤
      ENNReal.ofReal ((2 : ℝ) ^ j * M j / ρ ^ j) := by
    apply iSup_le
    intro t
    apply iSup_le
    intro ht
    apply iSup_le
    intro x
    rw [← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    apply (le_div_iff₀ hp).mpr
    simpa only [coe_nnnorm, mul_comm] using coefficient_array_normalized_jet_bound
      (A t) j ((hA t ht).of_le (by exact_mod_cast hjK)) x ρ (M j) hρ.le (hb t ht j hjK x)
  calc
    _ ≤ ENNReal.ofReal (ρ ^ j / (j.factorial : ℝ)) *
        ENNReal.ofReal ((2 : ℝ) ^ j * M j / ρ ^ j) := mul_le_mul_of_nonneg_left hsup zero_le
    _ = ENNReal.ofReal ((ρ ^ j / (j.factorial : ℝ)) *
        ((2 : ℝ) ^ j * M j / ρ ^ j)) := (ENNReal.ofReal_mul (by positivity)).symm
    _ = _ := by congr 1; field_simp

theorem pointwise_coefficient_seminorm_finite (ρ : ℝ) (hρ : 0 < ρ) (K : ℕ)
    (a b : ℝ) (A : ℝ → Vec 2 → E →L[ℝ] F)
    (hA : ∀ t ∈ Set.Icc a b, ContDiff ℝ (K : ℕ) (A t))
    (M : ℕ → ℝ) (hM : ∀ j, 0 ≤ M j)
    (hb : ∀ t ∈ Set.Icc a b, ∀ j, j ≤ K → ∀ x,
      ρ ^ j * ‖iteratedFDeriv ℝ j (A t) x‖ ≤ M j) :
    coefficientSeminorm ρ K a b A ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (pointwise_coefficient_seminorm_budget ρ hρ K a b A hA M hM hb)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! The physical inverse-flow test has the exact material transport correction in its time derivative. -/

theorem inverseMaterialTest_time_derivative {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s t : ℝ) (x : Vec 2) (η : ℝ → Vec 2 → ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => η p.1 p.2)) :
    deriv (fun r => chartUnpull hφ s η r x) t =
      deriv (fun r => η r (AVRegularity.streamFlow φ hφ s x t)) t -
        vecDot (spaceGrad (chartUnpull hφ s η t) x) (streamVel φ t x) := by
  let y := AVRegularity.streamFlow φ hφ s x t
  have hψ := inverseStreamFlow_test_smooth hφ s (η := η) hη
  have ht := streamFlow_test_time_chain hφ s t y (η := chartUnpull hφ s η) hψ
  have hinv : AVRegularity.streamFlow φ hφ t y s = x :=
    (streamFlowHomeomorph hφ t s).right_inv x
  have hfun : (fun r => chartUnpull hφ s η r (AVRegularity.streamFlow φ hφ r y s)) =
      fun r => η r y := by
    exact congrArg (fun f : ℝ → Vec 2 → ℝ => fun r => f r y) (chartPull_chartUnpull hφ s η)
  rw [hfun, hinv] at ht
  exact eq_sub_of_add_eq ht.symm

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! A matrix bounded on its prescribed time window supplies the native diffusion operator by time clamping. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

def planeWindowScalarDiffusion (a b : ℝ) (hab : a ≤ b)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hc : ∀ t ∈ Icc a b, ∀ k j, Continuous (fun x => G t x k j))
    (M : ℝ) (hb : ∀ t ∈ Icc a b, ∀ k j x, |G t x k j| ≤ M) :
    ℝ → PlaneFluxL2 E →L[ℝ] PlaneFluxL2 E :=
  fun t => planeScalarDiffusion (planeIntervalCoefficient a b hab G t)
    (planeIntervalMetric_continuous a b hab G hc t) (le_max_right M 0)
    (fun k j x => (hb _ (projIcc a b hab t).property k j x).trans (le_max_left M 0))

end AVRegularity.CycleJointProofs
end
end
