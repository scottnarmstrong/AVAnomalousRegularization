-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeakAssembly.QuietDuhamel
public import AVRegularity.EntryWeakAssembly.PairedForcingCostSchur
import AVRegularity.Construction.Preservation.FullLift.ZeroFreshMetricSliceJets
import AVRegularity.Construction.Preservation.FullLift.UniformNativeNormalizedJointBounds
import AVRegularity.Proofs.WeakGen.Reduction.CoeffAllOrder
import AVRegularity.Proofs.WeakGen.Reduction.ScalarForced
import AVRegularity.EntryWeakAssembly.FullReadoutLocalReserves
public import AVRegularity.EntryWeakAssembly.QuietParentPhysicalPrice
import AVRegularity.CycleJoint.PeriodicOperatorImageBudget

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Coarse
namespace AVRegularity.WeakEntryProofs.Assembly

/-! Integrability of the actual recursively ordered adjoint source paths.
The finite unweighted constants below are used only for Bochner existence;
the quantitative quiet margin price is proved separately in factorial norms. -/

variable {plan : WeakPassagePlan} {prices : WeakQuietPathPrices}

/-- The insertion bound gives a finite uniform operator bound on the actual
closed quiet margin. No estimate of an arbitrary off-quiet margin extension is used. -/
theorem weak_quiet_insertion_uniform_bound (x : WeakQuietExpansionCase plan prices)
    (S : WeakQuietInsertionData x) (hρ : 0 < x.radius)
    (v u : x.Vertex) (P : ℕ) (hP : P + x.order ≤ x.cap) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc x.left x.right,
      ∀ φ : TorusHk (P + x.order) ℝ, ‖S.apply v u P hP t φ‖ ≤ C * ‖φ‖ := by
  let F := x.c.D.κ x.c.M / x.c.D.eps (x.i - 1) ^ 2 * x.insertionPrice * x.b v u
  let C := |F| * Real.sqrt (factorialWeightMax x.radius (P + x.order)) /
    Real.sqrt (factorialWeightMin x.radius P)
  have hm : 0 < Real.sqrt (factorialWeightMin x.radius P) :=
    Real.sqrt_pos.mpr (factorialWeightMin_pos x.radius hρ)
  have hmax : 0 ≤ factorialWeightMax x.radius (P + x.order) :=
    (factorialWeight_nonneg x.radius 0).trans (factorialWeight_le_max x.radius
      (0 : Fin (P + x.order + 1)))
  refine ⟨C, div_nonneg (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) hm.le, ?_⟩
  intro t ht φ
  obtain ⟨D, Adj, he, hb⟩ := S.adjoint v u t ht
  have hs : Real.sqrt (factorialNormSq x.radius (S.apply v u P hP t φ).val) ≤
      |F| * Real.sqrt (factorialNormSq x.radius φ.val) := by
    rw [he P hP]
    exact (hb P hP φ).trans
      (mul_le_mul_of_nonneg_right (le_abs_self F) (Real.sqrt_nonneg _))
  have hφ := Real.sqrt_le_sqrt (factorialNormSq_upper x.radius φ.val)
  rw [Real.sqrt_mul hmax, Real.sqrt_sq (norm_nonneg _)] at hφ
  calc
    ‖S.apply v u P hP t φ‖ ≤
        Real.sqrt (factorialNormSq x.radius (S.apply v u P hP t φ).val) /
          Real.sqrt (factorialWeightMin x.radius P) :=
      CoupledEnergy.Variational.jetNorm_le_factorialRoot x.radius hρ _
    _ ≤ (|F| * Real.sqrt (factorialNormSq x.radius φ.val)) /
          Real.sqrt (factorialWeightMin x.radius P) :=
      div_le_div_of_nonneg_right hs hm.le
    _ ≤ (|F| * (Real.sqrt (factorialWeightMax x.radius (P + x.order)) * ‖φ‖)) /
          Real.sqrt (factorialWeightMin x.radius P) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hφ (abs_nonneg _)) hm.le
    _ = C * ‖φ‖ := by dsimp only [C]; ring

/-- Uniform finite-order bounds for the chosen propagator on the quiet margin
square, with reversed windows clamped to their identity endpoint. -/
theorem weak_quiet_backward_uniform_bound (x : WeakQuietExpansionCase plan prices)
    (hd : WeakScalarTorusDrift (x.c.D.κ x.c.M) x.radius x.left x.right
      (streamVel (x.c.D.Φ (x.i - 1))) x.cap) (P : ℕ) (hP : P ≤ x.cap) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : Set.Icc x.left x.right,
      ∀ φ : TorusHk P ℝ,
        ‖weakQuietBackwardOperator x hd P (min a.val b.val) b φ‖ ≤ C * ‖φ‖ := by
  refine ⟨Real.sqrt (2 * factorialWeightMax x.radius P / factorialWeightMin x.radius P),
    Real.sqrt_nonneg _, ?_⟩
  intro a b φ
  obtain ⟨z, zw, hz, he⟩ := (weakQuietBackwardEvolution x hd).native P hP
    (min a.val b.val) b (le_min a.property.1 b.property.1) (min_le_right _ _) b.property.2 φ
  rw [show weakQuietBackwardOperator x hd P (min a.val b.val) b φ = z (-min a.val b.val)
    from he]
  exact weak_scalar_torus_norm_bound hP
    ((hd.restrict (Set.Icc_subset_Icc (le_min a.property.1 b.property.1) b.property.2)
      le_rfl).reflected) hz ⟨neg_le_neg (min_le_right _ _), le_rfl⟩

/-- A bounded strongly measurable operator realization of one actual dual
path, simultaneously on all closed subwindows of the quiet margin. -/
structure WeakQuietDualPathOperator (x : WeakQuietExpansionCase plan prices)
    (S : WeakQuietInsertionData x) (H : WeakQuietBackwardEvolution x)
    (n : ℕ) (hn : n ≤ prices.depth x.R) (v u : x.Vertex)
    (π : WeakQuietWalk x.Vertex n v u) where
  apply : Set.Icc x.left x.right → Set.Icc x.left x.right →
    TorusHk (n * x.order) ℝ →L[ℝ] TorusHk 0 ℝ
  value : ∀ a b, a.val ≤ b.val → ∀ φ,
    apply a b φ = weakQuietWalkDual x S H n hn v u π a b φ
  measurable : ∀ φ, StronglyMeasurable
    (fun p : Set.Icc x.left x.right × Set.Icc x.left x.right => apply p.1 p.2 φ)
  bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ a b φ, ‖apply a b φ‖ ≤ C * ‖φ‖

/-- The empty path is the actual backward scalar operator. -/
def weakQuietDualPathOperatorZero (x : WeakQuietExpansionCase plan prices)
    (hd : WeakScalarTorusDrift (x.c.D.κ x.c.M) x.radius x.left x.right
      (streamVel (x.c.D.Φ (x.i - 1))) x.cap)
    (S : WeakQuietInsertionData x) (v u : x.Vertex) (π : WeakQuietWalk x.Vertex 0 v u) :
    WeakQuietDualPathOperator x S (weakQuietBackwardEvolution x hd) 0
      (Nat.zero_le _) v u π where
  apply a b := (weakQuietBackwardOperator x hd 0 (min a.val b.val) b).comp
    (truncateTorusHk (by simp))
  value a b hab φ := by
    rw [min_eq_left hab]
    rfl
  measurable φ := weak_quiet_backward_stronglyMeasurable_zero x hd
    (weakQuietBackwardEvolution x hd) (truncateTorusHk (by simp) φ)
  bound := by
    obtain ⟨C, hC, hbound⟩ := weak_quiet_backward_uniform_bound x hd 0 (Nat.zero_le x.cap)
    refine ⟨C, hC, fun a b φ => ?_⟩
    exact (hbound a b _).trans
      (mul_le_mul_of_nonneg_left (truncateTorusHk_norm_le (by simp) φ) hC)

/-- Clamp the left endpoint to obtain an ordered subwindow. -/
def weakQuietPathStart {x : WeakQuietExpansionCase plan prices}
    (a b : Set.Icc x.left x.right) : Set.Icc x.left x.right :=
  ⟨min a.val b.val, le_min a.property.1 b.property.1,
    (min_le_right _ _).trans b.property.2⟩

/-- One actual path step, extended in the integration variable by clamping to
the quiet margin. This extension is immaterial inside every actual time integral. -/
def weakQuietDualPathStep (x : WeakQuietExpansionCase plan prices)
    (hd : WeakScalarTorusDrift (x.c.D.κ x.c.M) x.radius x.left x.right
      (streamVel (x.c.D.Φ (x.i - 1))) x.cap)
    (S : WeakQuietInsertionData x) (n : ℕ) (hn : n + 1 ≤ prices.depth x.R)
    (v w u : x.Vertex) (π : WeakQuietWalk x.Vertex n w u)
    (V : WeakQuietDualPathOperator x S (weakQuietBackwardEvolution x hd)
      n (by omega) w u π)
    (a b : Set.Icc x.left x.right) (t : ℝ) :
    TorusHk ((n + 1) * x.order) ℝ →L[ℝ] TorusHk 0 ℝ :=
  let c := Set.projIcc x.left x.right x.heat_window.1.le t
  (V.apply (weakQuietPathStart a b) c).comp
    ((S.apply v w (n * x.order)
      (by simpa only [Nat.succ_mul] using x.path_reserve (n + 1) hn) c).comp
      ((truncateTorusHk (by rw [Nat.succ_mul])).comp
        (weakQuietBackwardOperator x hd ((n + 1) * x.order) (min c.val b.val) b)))

/-- The actual step is jointly strongly measurable on all endpoint and
integration parameters, for each fixed Sobolev test. -/
theorem weak_quiet_dual_path_step_measurable (x : WeakQuietExpansionCase plan prices)
    (hd : WeakScalarTorusDrift (x.c.D.κ x.c.M) x.radius x.left x.right
      (streamVel (x.c.D.Φ (x.i - 1))) x.cap)
    (S : WeakQuietInsertionData x) (n : ℕ) (hn : n + 1 ≤ prices.depth x.R)
    (v w u : x.Vertex) (π : WeakQuietWalk x.Vertex n w u)
    (V : WeakQuietDualPathOperator x S (weakQuietBackwardEvolution x hd)
      n (by omega) w u π)
    (φ : TorusHk ((n + 1) * x.order) ℝ) :
    StronglyMeasurable (fun p : (Set.Icc x.left x.right × Set.Icc x.left x.right) × ℝ =>
      weakQuietDualPathStep x hd S n hn v w u π V p.1.1 p.1.2 p.2 φ) := by
  let : TopologicalSpace.SeparableSpace (TorusHk (n * x.order + x.order) ℝ) :=
    CoupledEnergy.Variational.torusHkSeparableSpace _
  let : TopologicalSpace.SeparableSpace (TorusHk (n * x.order) ℝ) :=
    CoupledEnergy.Variational.torusHkSeparableSpace _
  borelize (TorusHk (n * x.order + x.order) ℝ) (TorusHk (n * x.order) ℝ)
  let T := (Set.Icc x.left x.right × Set.Icc x.left x.right) × ℝ
  let c : T → Set.Icc x.left x.right := fun p =>
    Set.projIcc x.left x.right x.heat_window.1.le p.2
  let a : T → Set.Icc x.left x.right := fun p => weakQuietPathStart p.1.1 p.1.2
  let b : T → Set.Icc x.left x.right := fun p => p.1.2
  have hc : Measurable c := continuous_projIcc.measurable.comp measurable_snd
  have ha : Measurable a := by
    exact ((measurable_fst.fst.subtype_val).min
      (measurable_fst.snd.subtype_val)).subtype_mk
  have hb : Measurable b := measurable_fst.snd
  have hH := weak_quiet_backward_stronglyMeasurable_action x hd ((n + 1) * x.order)
    (x.path_reserve (n + 1) hn) c b hc hb (fun _ : T => φ) stronglyMeasurable_const
  let hP : n * x.order + x.order ≤ x.cap :=
    by simpa only [Nat.succ_mul] using x.path_reserve (n + 1) hn
  have hS := CoupledEnergy.Variational.stronglyMeasurable_operator_action
    (fun p : T => S.apply v w (n * x.order) hP (c p))
    (fun ψ => (S.measurable v w (n * x.order) hP ψ).comp_measurable hc.subtype_val)
    ((truncateTorusHk (by rw [Nat.succ_mul])).continuous.comp_stronglyMeasurable hH)
  exact CoupledEnergy.Variational.stronglyMeasurable_operator_action
    (fun p : T => V.apply (a p) (c p))
    (fun ψ => (V.measurable ψ).comp_measurable (ha.prodMk hc)) hS

/-- One step has a finite uniform norm bound. It is independent of the
integration variable, so it proves genuine Bochner integrability. -/
theorem weak_quiet_dual_path_step_bound (x : WeakQuietExpansionCase plan prices)
    (hd : WeakScalarTorusDrift (x.c.D.κ x.c.M) x.radius x.left x.right
      (streamVel (x.c.D.Φ (x.i - 1))) x.cap)
    (S : WeakQuietInsertionData x) (n : ℕ) (hn : n + 1 ≤ prices.depth x.R)
    (v w u : x.Vertex) (π : WeakQuietWalk x.Vertex n w u)
    (V : WeakQuietDualPathOperator x S (weakQuietBackwardEvolution x hd)
      n (by omega) w u π) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b t φ,
      ‖weakQuietDualPathStep x hd S n hn v w u π V a b t φ‖ ≤ C * ‖φ‖ := by
  obtain ⟨CV, hCV, hV⟩ := V.bound
  obtain ⟨CS, hCS, hS⟩ := weak_quiet_insertion_uniform_bound x S hd.radius_pos v w
    (n * x.order) (by simpa only [Nat.succ_mul] using x.path_reserve (n + 1) hn)
  obtain ⟨CH, hCH, hH⟩ := weak_quiet_backward_uniform_bound x hd ((n + 1) * x.order)
    (x.path_reserve (n + 1) hn)
  refine ⟨CV * CS * CH, mul_nonneg (mul_nonneg hCV hCS) hCH, ?_⟩
  intro a b t φ
  let c := Set.projIcc x.left x.right x.heat_window.1.le t
  let y := weakQuietBackwardOperator x hd ((n + 1) * x.order) (min c.val b.val) b φ
  let y' : TorusHk (n * x.order + x.order) ℝ := truncateTorusHk (by rw [Nat.succ_mul]) y
  have he : ‖y'‖ ≤ CH * ‖φ‖ := (truncateTorusHk_norm_le _ y).trans (hH c b φ)
  have hs := (hS c c.property y').trans (mul_le_mul_of_nonneg_left he hCS)
  have hv := (hV (weakQuietPathStart a b) c _).trans (mul_le_mul_of_nonneg_left hs hCV)
  change ‖V.apply (weakQuietPathStart a b) c (S.apply v w (n * x.order) _ c y')‖ ≤ _
  calc
    _ ≤ CV * (CS * (CH * ‖φ‖)) := hv
    _ = (CV * CS * CH) * ‖φ‖ := by ring

section Step
variable (x : WeakQuietExpansionCase plan prices)
  (hd : WeakScalarTorusDrift (x.c.D.κ x.c.M) x.radius x.left x.right
    (streamVel (x.c.D.Φ (x.i - 1))) x.cap)
  (S : WeakQuietInsertionData x) (n : ℕ) (hn : n + 1 ≤ prices.depth x.R)
  (v w u : x.Vertex) (π : WeakQuietWalk x.Vertex n w u)
  (V : WeakQuietDualPathOperator x S (weakQuietBackwardEvolution x hd)
    n (by omega) w u π)

local notation "step" => weakQuietDualPathStep x hd S n hn v w u π V
include V

/-- Actual step integrals are integrable, rather than relying on the default
value assigned to a nonintegrable Bochner integral. -/
theorem weak_quiet_dual_path_step_integrable (a b : Set.Icc x.left x.right)
    (φ : TorusHk ((n + 1) * x.order) ℝ) :
    IntervalIntegrable (fun t => step a b t φ) volume (min a.val b.val) b := by
  obtain ⟨C, _, hb⟩ := weak_quiet_dual_path_step_bound x hd S n hn v w u π V
  have hm : StronglyMeasurable (fun t : ℝ => step a b t φ) :=
    (weak_quiet_dual_path_step_measurable x hd S n hn v w u π V φ).comp_measurable
      (measurable_const.prodMk measurable_id : Measurable (fun t : ℝ => ((a, b), t)))
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le (min_le_right a.val b.val)).mpr
  exact IntegrableOn.of_bound measure_Icc_lt_top hm.aestronglyMeasurable
    (C * ‖φ‖) (Filter.Eventually.of_forall fun t => hb a b t φ)

/-- The integral of one step is jointly strongly measurable in the closed
endpoints. The moving time interval is handled by its measurable indicator. -/
theorem weak_quiet_dual_path_step_integral_measurable
    (φ : TorusHk ((n + 1) * x.order) ℝ) :
    StronglyMeasurable (fun p : Set.Icc x.left x.right × Set.Icc x.left x.right =>
      ∫ t in (min p.1.val p.2.val)..p.2.val, step p.1 p.2 t φ) := by
  let A := Set.Icc x.left x.right × Set.Icc x.left x.right
  let E : Set (A × ℝ) := {p | min p.1.1.val p.1.2.val < p.2 ∧ p.2 ≤ p.1.2.val}
  have hE : MeasurableSet E :=
    (measurableSet_lt (measurable_fst.fst.subtype_val.min measurable_fst.snd.subtype_val)
      measurable_snd).inter (measurableSet_le measurable_snd measurable_fst.snd.subtype_val)
  have hm := ((weak_quiet_dual_path_step_measurable x hd S n hn v w u π V φ).indicator hE).integral_prod_right' (ν := volume)
  have he : (fun p : A => ∫ t, E.indicator
      (fun q => step q.1.1 q.1.2 q.2 φ) (p, t)) =
      (fun p : A => ∫ t in (min p.1.val p.2.val)..p.2.val, step p.1 p.2 t φ) := by
    funext p
    rw [intervalIntegral.integral_of_le (min_le_right _ _)]
    simpa only [E, Set.indicator, Set.mem_Ioc, Set.mem_ofPred_eq] using
      (integral_indicator (f := fun t => step p.1 p.2 t φ)
        (measurableSet_Ioc : MeasurableSet (Set.Ioc (min p.1.val p.2.val) p.2.val)))
  rw [he] at hm
  exact hm

/-- On the integration interval the clamped measurable step is exactly the
original recursive source integrand, with the original finite reserve. -/
theorem weak_quiet_dual_path_step_value (a b : Set.Icc x.left x.right)
    (hab : a.val ≤ b.val) (t : ℝ) (ht : t ∈ Set.Icc a.val b.val)
    (φ : TorusHk ((n + 1) * x.order) ℝ) :
    step a b t φ = weakQuietWalkDual x S (weakQuietBackwardEvolution x hd)
      n (by omega) w u π a.val t
        (S.apply v w (n * x.order)
          (by simpa only [Nat.succ_mul] using x.path_reserve (n + 1) hn) t
          (truncateTorusHk (by rw [Nat.succ_mul])
            ((weakQuietBackwardEvolution x hd).apply ((n + 1) * x.order) t b φ))) := by
  have htc : t ∈ Set.Icc x.left x.right := ⟨a.property.1.trans ht.1, ht.2.trans b.property.2⟩
  have hp : Set.projIcc x.left x.right x.heat_window.1.le t = ⟨t, htc⟩ :=
    Set.projIcc_of_mem x.heat_window.1.le htc
  dsimp only [weakQuietDualPathStep, ContinuousLinearMap.comp_apply]
  rw [hp, min_eq_left ht.2]
  have hs : weakQuietPathStart a b = a := Subtype.ext (min_eq_left hab)
  rw [hs, V.value a ⟨t, htc⟩ ht.1]
  rfl

/-- Integrating the bounded step constructs a continuous linear path
operator with the actual recursively ordered integral as its value. -/
theorem weak_quiet_dual_path_operator_succ :
    Nonempty (WeakQuietDualPathOperator x S (weakQuietBackwardEvolution x hd)
      (n + 1) hn v u ⟨w, π⟩) := by
  obtain ⟨C, hC, hb⟩ := weak_quiet_dual_path_step_bound x hd S n hn v w u π V
  let L (a b : Set.Icc x.left x.right) :
      TorusHk ((n + 1) * x.order) ℝ →ₗ[ℝ] TorusHk 0 ℝ :=
    { toFun := fun φ => ∫ t in (min a.val b.val)..b.val, step a b t φ
      map_add' := fun φ ψ => by
        simp only [map_add]
        exact intervalIntegral.integral_add
          (weak_quiet_dual_path_step_integrable x hd S n hn v w u π V a b φ)
          (weak_quiet_dual_path_step_integrable x hd S n hn v w u π V a b ψ)
      map_smul' := fun r φ => by
        simp only [map_smul, RingHom.id_apply]
        exact intervalIntegral.integral_smul r _ }
  have hL (a b : Set.Icc x.left x.right) (φ : TorusHk ((n + 1) * x.order) ℝ) :
      ‖L a b φ‖ ≤ (C * (x.right - x.left)) * ‖φ‖ := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (fun t (_ht : t ∈ Set.uIoc (min a.val b.val) b.val) => hb a b t φ)
    change ‖L a b φ‖ ≤ (C * ‖φ‖) * |b.val - min a.val b.val| at hh
    rw [abs_of_nonneg (sub_nonneg.mpr (min_le_right _ _))] at hh
    have hlen : b.val - min a.val b.val ≤ x.right - x.left :=
      sub_le_sub b.property.2 (le_min a.property.1 b.property.1)
    calc
      _ ≤ C * ‖φ‖ * (b.val - min a.val b.val) := hh
      _ ≤ C * ‖φ‖ * (x.right - x.left) :=
        mul_le_mul_of_nonneg_left hlen (mul_nonneg hC (norm_nonneg _))
      _ = _ := by ring
  refine ⟨{
    apply := fun a b => (L a b).mkContinuous (C * (x.right - x.left)) (hL a b)
    value := ?_
    measurable := fun φ => weak_quiet_dual_path_step_integral_measurable x hd S n hn v w u π V φ
    bound := ⟨C * (x.right - x.left), mul_nonneg hC (sub_nonneg.mpr x.heat_window.1.le), hL⟩ }⟩
  intro a b hab φ
  change (∫ t in (min a.val b.val)..b.val, step a b t φ) = _
  rw [min_eq_left hab]
  change (∫ t in a.val..b.val, step a b t φ) = ∫ t in a.val..b.val, _
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hab] at ht
  exact weak_quiet_dual_path_step_value x hd S n hn v w u π V a b hab t ht φ

end Step

/-- Every retained actual dual path is a bounded strongly measurable operator
on the entire family of closed quiet margin subwindows. -/
theorem weak_quiet_dual_path_operator (x : WeakQuietExpansionCase plan prices)
    (hd : WeakScalarTorusDrift (x.c.D.κ x.c.M) x.radius x.left x.right
      (streamVel (x.c.D.Φ (x.i - 1))) x.cap)
    (S : WeakQuietInsertionData x) (n : ℕ) (hn : n ≤ prices.depth x.R)
    (v u : x.Vertex) (π : WeakQuietWalk x.Vertex n v u) :
    Nonempty (WeakQuietDualPathOperator x S (weakQuietBackwardEvolution x hd) n hn v u π) := by
  induction n generalizing v with
  | zero => exact ⟨weakQuietDualPathOperatorZero x hd S v u π⟩
  | succ n ih =>
    obtain ⟨w, π⟩ := π
    obtain ⟨V⟩ := ih (hn := by omega) w π
    exact weak_quiet_dual_path_operator_succ x hd S n hn v w u π V

/-- The integrability premise of the finite ordered expansion is discharged
for the actual scalar evolution and every genuine insertion datum. -/
theorem weak_quiet_walk_integrable (x : WeakQuietExpansionCase plan prices)
    (hd : WeakScalarTorusDrift (x.c.D.κ x.c.M) x.radius x.left x.right
      (streamVel (x.c.D.Φ (x.i - 1))) x.cap)
    (S : WeakQuietInsertionData x) :
    WeakQuietWalkIntegrable x S (weakQuietBackwardEvolution x hd) := by
  intro n hn v u π a b ha hab hb φ
  obtain ⟨w, π⟩ := π
  obtain ⟨V⟩ := weak_quiet_dual_path_operator x hd S n (by omega) w u π
  let a' : Set.Icc x.left x.right := ⟨a, ha, hab.trans hb⟩
  let b' : Set.Icc x.left x.right := ⟨b, ha.trans hab, hb⟩
  have hi := weak_quiet_dual_path_step_integrable x hd S n hn v w u π V a' b' φ
  rw [min_eq_left hab] at hi
  have hI := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hi
  apply hI.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact weak_quiet_dual_path_step_value x hd S n hn v w u π V a' b' hab t ht φ

/-- The prescribed entrance size is exactly the order-zero factorial norm
of the mass-normalized row used in the actual path functional. -/
theorem weak_quiet_input_size (x : WeakQuietExpansionCase plan prices) (u : x.Vertex) :
    Real.sqrt (factorialNormSq 1
      (truncateTorusHk (Nat.zero_le x.R.Kw) (x.value u x.left)).val) = x.inputSize u := by
  dsimp only [WeakQuietExpansionCase.value, WeakQuietExpansionCase.inputSize]
  rw [map_smul]
  change Real.sqrt (factorialNormSq 1
    (Real.sqrt (x.mass u)⁻¹ • (truncateTorusHk (Nat.zero_le x.R.Kw)
      (x.run.Ur x.i u x.left)).val)) = _
  rw [sqrt_fNSq_smul, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sqrt_mul (inv_nonneg.mpr (x.mass_pos u).le)]

end AVRegularity.WeakEntryProofs.Assembly
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.WeakEntryProofs

/-! **The paired solve** (`WeakEntryPairedSolveStatement`).
The paired system of `Gw` (every identity regularized by `S_w = isoPairedKernel r_w`) is the
kernel-regularized system of a `TorusKernelOperator` on `[a_M, a + T₀]` at the capped radius
`c_K x`, the diffusivity `κ_M` and the order `K_w`:
* masses `π = Gw.mass law` (the weak masses, positive);
* coefficients: the physical coefficients of `Gw`, which are those of the stage `M` along the
  encoding (`weakEncoding_physCoeff`), jointly measurable, `C^{K_w}`, periodic, with finite
  seminorms at every radius `≤ ε_{M-1}` (`weakEntry_physCoeff_allOrder`);
* the regularizer constants of the paired kernel at every width (`weakPairedRegConstants`);
* the Schur bound `C ε_M^{χ_w} ≤ 1/8` (`weakPaired_schur` and the level floor).
The drift `𝐛_M` has the actual stream jets with `α = C_drift a_M`, `B = 1024`, `λ = ε_M`; the radius
`c_K ≤ 1/2048` pays `Bρ/λ ≤ 1/2`, and the level floor pays the strain `αBρ² ≤ κ_M/8`
(`weakPaired_strain_arith`: `a_M ε_M² = ε_M^{1+α}` and `κ_M ≥ ε_M^{1+α-γ}/2`).
Galerkin existence (`native_reg_solution_exists`) and the strong energy
(`native_reg_solution_strongEnergy`) give the statement. -/

open AVRegularity.WeakEntryProofs.Assembly

/-- The drift strain at the capped radius, in abstract reals. -/
theorem weakPaired_strain_arith {Cd cK ε γ a κ : ℝ} (hCd : 0 ≤ Cd) (hcK0 : 0 ≤ cK)
    (hcK : cK ≤ 1 / 2048) (hε : 0 < ε) (hκ : ε ^ ((1 + a) - γ) / 2 ≤ κ)
    (hγ : ε ^ γ ≤ 256 / (Cd + 1)) :
    Cd * ε ^ ((1 + a) - 2) * 1024 * (cK * ε) ^ 2 ≤ κ / 8 := by
  set X := ε ^ ((1 + a) - γ) with hX
  set Y := ε ^ γ with hY
  have hXpos : 0 < X := Real.rpow_pos_of_pos hε _
  have hY0 : 0 ≤ Y := (Real.rpow_pos_of_pos hε _).le
  have hsplit : ε ^ ((1 + a) - 2) * ε ^ 2 = X * Y := by
    rw [hX, hY, ← Real.rpow_natCast ε 2, ← Real.rpow_add hε, ← Real.rpow_add hε]
    congr 1
    push_cast
    ring
  have hCY : Cd * Y ≤ 256 := by
    have h1 : Cd * Y ≤ Cd * (256 / (Cd + 1)) := mul_le_mul_of_nonneg_left hγ hCd
    have h2 : Cd * (256 / (Cd + 1)) ≤ 256 := by
      rw [← mul_div_assoc, div_le_iff₀ (by linarith)]
      linarith
    linarith
  have hcK2 : cK ^ 2 ≤ (1 / 2048) ^ 2 := pow_le_pow_left₀ hcK0 hcK 2
  have hmain : 1024 * cK ^ 2 * (Cd * Y) ≤ 1024 * (1 / 2048) ^ 2 * 256 :=
    mul_le_mul (mul_le_mul_of_nonneg_left hcK2 (by norm_num)) hCY (mul_nonneg hCd hY0)
      (by norm_num)
  calc Cd * ε ^ ((1 + a) - 2) * 1024 * (cK * ε) ^ 2
      = 1024 * cK ^ 2 * Cd * (ε ^ ((1 + a) - 2) * ε ^ 2) := by ring
    _ = 1024 * cK ^ 2 * (Cd * Y) * X := by rw [hsplit]; ring
    _ ≤ 1024 * (1 / 2048) ^ 2 * 256 * X := mul_le_mul_of_nonneg_right hmain hXpos.le
    _ = X / 16 := by ring
    _ ≤ κ / 8 := by linarith

/-- The price `P ε^χ` with `ε^χ ≤ 1/(8(P+1))` is at most `1/8`. -/
theorem weakPaired_price_arith {P Z : ℝ} (hP : 0 ≤ P) (hZ : Z ≤ 1 / (8 * (P + 1))) :
    P * Z ≤ 1 / 8 := by
  have h1 : P * Z ≤ P * (1 / (8 * (P + 1))) := mul_le_mul_of_nonneg_left hZ hP
  have h2 : P * (1 / (8 * (P + 1))) ≤ 1 / 8 := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  linarith

section Pieces

variable {plan : WeakEntryGluePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A} {C : WeakEntryAllocation R (plan.radius R)}

theorem weakPaired_eps_eq (x : WeakEntryData plan C) :
    x.D.eps x.M = ocEpsilon B.q A.Λ x.M := by
  simp only [OCData.eps, x.q_eq, x.base_eq]

theorem weakPaired_eps_pos (x : WeakEntryData plan C) : 0 < ocEpsilon B.q A.Λ x.M :=
  Construction.Stream.ocEpsilon_pos ((by norm_num : 1 ≤ 128).trans x.base128)

theorem weakPaired_kappa_pos (x : WeakEntryData plan C) : 0 < x.D.κ x.M := by
  have hΛ1 : 1 ≤ x.D.Λ := by rw [x.base_eq]; exact (by norm_num : 1 ≤ 128).trans x.base128
  have hζ : IsFastProfile x.D.ζ := by rw [x.profile_eq]; exact B.hζ
  have hband : IsOCBandChain x.D.α x.D.q x.D.Λ x.D.ζ x.D.term x.D.κ := by
    rw [x.alpha, x.q_eq, x.base_eq, x.profile_eq, x.terminal]; exact x.band
  exact CycleReference.bandChain_pos hΛ1 hζ hband (by rw [x.terminal])

theorem weakPaired_radius_eq (x : WeakEntryData plan C) :
    x.D.termRStar (plan.radius R) x.M = plan.radius R * ocEpsilon B.q A.Λ x.M := by
  rw [OCData.termRStar, weakPaired_eps_eq]

theorem weakPaired_radius_pos (x : WeakEntryData plan C) :
    0 < x.D.termRStar (plan.radius R) x.M := by
  rw [weakPaired_radius_eq]
  exact mul_pos (weak_entry_radius_spec (plan.radiusBudget R)).1 (weakPaired_eps_pos x)

theorem weakPaired_radius_le (x : WeakEntryData plan C) :
    x.D.termRStar (plan.radius R) x.M ≤ x.D.eps (x.M - 1) := by
  have h1 : x.D.termRStar (plan.radius R) x.M ≤ ocEpsilon B.q A.Λ x.M := by
    rw [weakPaired_radius_eq]
    exact mul_le_of_le_one_left (weakPaired_eps_pos x).le
      (weak_entry_radius_spec (plan.radiusBudget R)).2.1
  have h2 : ocEpsilon B.q A.Λ x.M ≤ ocEpsilon B.q A.Λ (x.M - 1) :=
    EntryScales.epsilon_antitone B.hq.1 x.base128 (Nat.sub_le x.M 1)
  simpa only [OCData.eps, x.q_eq, x.base_eq] using h1.trans h2

theorem weakPaired_width_pos (x : WeakEntryData plan C) : 0 < x.D.termRW A.σw x.M :=
  Real.rpow_pos_of_pos (by rw [weakPaired_eps_eq]; exact weakPaired_eps_pos x) _

theorem weakPaired_order (x : WeakEntryData plan C) : 2 ≤ x.Dm := by
  have := x.order_ge
  have h1 : 1 ≤ A.Jw * A.Nw := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by have := A.Jw_pos; omega) (by have := A.Nw_pos; omega))
  omega

theorem weakPaired_mass_pos {x : WeakEntryData plan C} (g : WeakEntryStages x) (law : BirthLaw)
    (hm : law.rootMass = g.rootM) (v' : CompIn g.Gw.comps) : 0 < g.Gw.mass law v' := by
  have hΛ1 : 1 ≤ x.D.Λ := by rw [x.base_eq]; exact (by norm_num : 1 ≤ 128).trans x.base128
  obtain ⟨v, rfl⟩ := g.relabel.surjective v'
  rw [weakEncoding_mass A.Nw A.Jw A.η₀ g.rootM g.rootR _ _ g.relabel g.encoding law hm v]
  exact weakMass_pos x.D A.Nw A.Jw A.η₀ A.Nw_pos A.Jw_pos
    (fun _ => Construction.Stream.ocEpsilon_pos hΛ1) v.1

/-- The physical coefficients of `Gw`: measurable, smooth, periodic, finite seminorms. -/
theorem weakPaired_coeffReg (hcommon : WeakEntryCommonOK plan) {x : WeakEntryData plan C}
    (g : WeakEntryStages x)
    {e : ∀ v u, (g.stage x.M).fam.Γ v u ≃ g.Gw.fam.Γ (g.relabel v) (g.relabel u)}
    (hB : ∀ v u (γ : (g.stage x.M).fam.Γ v u) d,
      g.Gw.physCoeff (g.relabel v) (g.relabel u) (e v u γ) d = (g.stage x.M).physCoeff v u γ d)
    (a b : ℝ) (v' u' : CompIn g.Gw.comps) (α' : g.Gw.fam.Γ v' u') (d : ℕ) :
    Measurable (fun z : Set.Icc a b × Vec 2 => g.Gw.physCoeff v' u' α' d z.1 z.2) ∧
      (∀ t, ContDiff ℝ (R.Kw : ℕ) (g.Gw.physCoeff v' u' α' d t)) ∧
      (∀ t, AVenhance.IsZ2Periodic (g.Gw.physCoeff v' u' α' d t)) ∧
      coefficientSeminorm (x.D.termRStar (plan.radius R) x.M) R.Kw a b
        (g.Gw.physCoeff v' u' α' d) ≠ ⊤ := by
  obtain ⟨v, rfl⟩ := g.relabel.surjective v'
  obtain ⟨u, rfl⟩ := g.relabel.surjective u'
  obtain ⟨α, rfl⟩ := (e v u).surjective α'
  rw [hB]
  obtain ⟨h1, h2, h3, h4⟩ := Providers.WeakGen.Reduction.weakEntry_physCoeff_allOrder hcommon
    g x.M le_rfl (by have := A.Jw_pos; omega) v u α R.Kw d a b
  exact ⟨h1, h2, h3, h4 _ (weakPaired_radius_pos x) (weakPaired_radius_le x)⟩

theorem weakPaired_theta (hok : WeakEntryPairedPlanOK plan) (x : WeakEntryData plan C) :
    weakPairedPriceConst R * (weakStoredLedgerData A).C * x.D.eps x.M ^ weakChi B.α B.q A.η₀ ≤
      1 / 8 := by
  rw [weakPaired_eps_eq]
  exact weakPaired_price_arith (mul_nonneg (weakPairedPriceConst_nonneg R)
    (weakStoredLedgerData A).positive.le) (weakPairedLevelFloor_spec hok x).2.2.1

theorem weakPaired_regularizer {x : WeakEntryData plan C} (g : WeakEntryStages x) (ρ a b : ℝ)
    (v u : CompIn g.Gw.comps) (γ : g.Gw.fam.Γ v u) :
    IsSpatialRegularizerTorus (G := ScalarH u.1.root) ρ R.Kw x.Dm a b (weakPairedRegConstants R)
      (x.D.termRW A.σw x.M)
      (g.Gw.sysS x.P (fun _ => isoPairedKernel (x.D.termRW A.σw x.M) R.nW)
        (fun _ => isoPairedKernel (x.D.termRW A.σw x.M) R.nW) A.φ₀ A.hφ₀ v u γ) := by
  rw [sysS_constKernel]
  exact (weakPairedRegConstants_spec R).2 _ (weakPaired_width_pos x) ρ a b R.Kw x.Dm

/-- **The kernel operator of the paired system of `Gw`** on `[a, b]`. -/
def weakPairedOperator (hcommon : WeakEntryCommonOK plan) (hok : WeakEntryPairedPlanOK plan)
    {x : WeakEntryData plan C} (g : WeakEntryStages x) (law : BirthLaw)
    (hm : law.rootMass = g.rootM)
    (e : ∀ v u, (g.stage x.M).fam.Γ v u ≃ g.Gw.fam.Γ (g.relabel v) (g.relabel u))
    (hB : ∀ v u (γ : (g.stage x.M).fam.Γ v u) d,
      g.Gw.physCoeff (g.relabel v) (g.relabel u) (e v u γ) d = (g.stage x.M).physCoeff v u γ d)
    {a b : ℝ} (hab : a ≤ b) :
    KernelEnergy.TorusKernelOperator (h := fun v : CompIn g.Gw.comps => ScalarH v.1.root)
      (Γ := g.Gw.fam.Γ) (G := fun _ u _ => ScalarH u.1.root) a b
      (x.D.termRStar (plan.radius R) x.M) (x.D.κ x.M) R.Kw x.Dm where
  htime := hab
  radius_pos := weakPaired_radius_pos x
  diffusivity_pos := weakPaired_kappa_pos x
  order_ge_two := weakPaired_order x
  π := g.Gw.mass law
  hπ := weakPaired_mass_pos g law hm
  B := fun v u γ d => g.Gw.physCoeff v u γ d.1
  hB_meas := fun v u γ d => (weakPaired_coeffReg hcommon g hB a b v u γ d.1).1
  hB_smooth := fun v u γ d t _ => (weakPaired_coeffReg hcommon g hB a b v u γ d.1).2.1 t
  hB_per := fun v u γ d t _ => (weakPaired_coeffReg hcommon g hB a b v u γ d.1).2.2.1 t
  hB_fin := fun v u γ d => (weakPaired_coeffReg hcommon g hB a b v u γ d.1).2.2.2
  C := fun _ u _ => ContinuousLinearMap.id ℝ (ScalarH u.1.root)
  S := g.Gw.sysS x.P (fun _ => isoPairedKernel (x.D.termRW A.σw x.M) R.nW)
    (fun _ => isoPairedKernel (x.D.termRW A.σw x.M) R.nW) A.φ₀ A.hφ₀
  c := weakPairedRegConstants R
  r := fun _ _ _ => x.D.termRW A.σw x.M
  hr := fun _ _ _ => weakPaired_width_pos x
  hS := fun v u γ => weakPaired_regularizer g _ a b v u γ
  θ := weakPairedPriceConst R * (weakStoredLedgerData A).C * x.D.eps x.M ^ weakChi B.α B.q A.η₀
  hθ := weakPaired_theta hok x
  hschur := weakPaired_schur hok g law hm e hB a b

/-- The drift at the capped radius: `Bρ/λ ≤ 1/2` and `αBρ² ≤ κ_M/8`. -/
theorem weakPaired_drift (hok : WeakEntryPairedPlanOK plan) (x : WeakEntryData plan C) :
    1024 * x.D.termRStar (plan.radius R) x.M / ocEpsilon B.q A.Λ x.M ≤ 1 / 2 ∧
      Construction.Preservation.Buffer.actualDriftJetConstant * ocA B.α B.q A.Λ x.M * 1024 *
        x.D.termRStar (plan.radius R) x.M ^ 2 ≤ x.D.κ x.M / 8 := by
  have hε := weakPaired_eps_pos x
  have hcK := weak_entry_radius_spec (plan.radiusBudget R)
  have hcK' : plan.radius R ≤ 1 / 2048 := hok.1 R
  rw [weakPaired_radius_eq]
  refine ⟨?_, weakPaired_strain_arith Construction.Preservation.Buffer.actualDriftJetConstant_nonneg
    hcK.1.le hcK' hε x.band.1.1 (weakPairedLevelFloor_spec hok x).2.2.2⟩
  have hε0 := hε.ne'
  rw [show 1024 * (plan.radius R * ocEpsilon B.q A.Λ x.M) / ocEpsilon B.q A.Λ x.M =
    1024 * plan.radius R by field_simp]
  linarith

theorem weakPaired_jets (hcommon : WeakEntryCommonOK plan) (x : WeakEntryData plan C)
    (a b : ℝ) :
    ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ R.Kw → ∀ y,
      ‖coefficientDerivativeArray (driftCoefficient (streamVel (x.D.Φ x.M) t)) l y‖ ≤
        Construction.Preservation.Buffer.actualDriftJetConstant * ocA B.α B.q A.Λ x.M *
          1024 ^ l * (l.factorial : ℝ) * ocEpsilon B.q A.Λ x.M ^ ((1 : ℤ) - l) :=
  fun t _ l hl _ y => Construction.Preservation.Buffer.actual_stream_drift_arrays B.α B.s B.hα₀
    B.hα₁ B.hs₀ B.hs₁ B.q B.hq B.ζ B.hζ A.Λ x.base128 x.D.Φ x.streams x.M
    (by have := Providers.WeakGen.Reduction.weakEntryData_M_ge_two hcommon x; omega) t l hl y

end Pieces

/-- **The paired solve** (`WeakEntryPairedSolveStatement`), under the common plan and the
paired plan floors. -/
theorem weak_entry_paired_solve (plan : WeakEntryGluePlan) (hcommon : WeakEntryCommonOK plan)
    (hok : WeakEntryPairedPlanOK plan) : WeakEntryPairedSolveStatement plan := by
  intro B A R C x g s law hm hr U₀
  obtain ⟨e, hB⟩ := weakEncoding_physCoeff g.encoding
  have haT : s.tq (x.M + 1) ≤ x.a + A.T₀ := s.finish.trans (by linarith [A.τ_small])
  have hα : 0 ≤ Construction.Preservation.Buffer.actualDriftJetConstant * ocA B.α B.q A.Λ x.M :=
    mul_nonneg Construction.Preservation.Buffer.actualDriftJetConstant_nonneg
      (Real.rpow_pos_of_pos (weakPaired_eps_pos x) _).le
  have hφ := Velocity.streamSeq_admissible B.hζ x.base128 x.streams x.M
  obtain ⟨hsmall, hstrain⟩ := weakPaired_drift hok x
  let Rop := weakPairedOperator hcommon hok g law hm e hB haT
  have hRB : Rop.B = fun v u γ (d : ↥(Finset.Icc 2 x.Dm)) => g.Gw.physCoeff v u γ d.1 := rfl
  have hRC : Rop.C = fun _ u _ => ContinuousLinearMap.id ℝ (ScalarH u.1.root) := rfl
  have hRS : Rop.S = g.Gw.sysS x.P (fun _ => isoPairedKernel (x.D.termRW A.σw x.M) R.nW)
      (fun _ => isoPairedKernel (x.D.termRW A.σw x.M) R.nW) A.φ₀ A.hφ₀ := rfl
  have hRπ : Rop.π = g.Gw.mass law := rfl
  obtain ⟨V, Vw, Vk, hsol⟩ := Construction.Preservation.FullLift.native_reg_solution_exists x.P
    (fun _ => isoPairedKernel (x.D.termRW A.σw x.M) R.nW)
    (fun _ => isoPairedKernel (x.D.termRW A.σw x.M) R.nW) A.φ₀ A.hφ₀ g.Gw Rop hRB hRC hRS hφ
    (Construction.Preservation.Buffer.actualDriftJetConstant * ocA B.α B.q A.Λ x.M) 1024
    (ocEpsilon B.q A.Λ x.M) hα (by norm_num) (weakPaired_eps_pos x) hsmall hstrain
    (weakPaired_jets hcommon x _ _) U₀
  have hen := Construction.Preservation.FullLift.native_reg_solution_strongEnergy x.P
    (fun _ => isoPairedKernel (x.D.termRW A.σw x.M) R.nW)
    (fun _ => isoPairedKernel (x.D.termRW A.σw x.M) R.nW) A.φ₀ A.hφ₀ g.Gw Rop hRB hRC hRS hφ
    (Construction.Preservation.Buffer.actualDriftJetConstant * ocA B.α B.q A.Λ x.M) 1024
    (ocEpsilon B.q A.Λ x.M) hα (by norm_num) (weakPaired_eps_pos x) hsmall hstrain
    (weakPaired_jets hcommon x _ _) U₀ V Vw Vk hsol
  rw [hRπ] at hen
  exact ⟨V, Vw, Vk, hsol, hen⟩

end AVRegularity.WeakEntryProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Coarse
open scoped Topology Classical
namespace AVRegularity.WeakEntryProofs.Assembly

/-! Measurable positive representatives and Bochner integration of the
actual finite source words. Cubes are finite products of the closed heat
quiet margin; the ordered simplex is a measurable subset of that finite measure. -/

variable {plan : WeakPassagePlan} {prices : WeakQuietPathPrices}

/-- A finite time cube, with the latest source coordinate first. -/
def WeakQuietTimeCube (I : Type) : ℕ → Type
  | 0 => PUnit
  | n + 1 => I × WeakQuietTimeCube I n

@[reducible] instance weakQuietTimeCubeMeasurableSpace (I : Type) [MeasurableSpace I] (n : ℕ) :
    MeasurableSpace (WeakQuietTimeCube I n) := by
  induction n with
  | zero => exact inferInstanceAs (MeasurableSpace PUnit)
  | succ n ih =>
    let : MeasurableSpace (WeakQuietTimeCube I n) := ih
    exact inferInstanceAs (MeasurableSpace (I × WeakQuietTimeCube I n))

/-- Forget the quiet margin subtype without changing chronological coordinates. -/
def weakQuietCubeTimes (x : WeakQuietExpansionCase plan prices) :
    (n : ℕ) → WeakQuietTimeCube (Set.Icc x.left x.right) n → WeakQuietInsertionTimes n
  | 0, _ => PUnit.unit
  | n + 1, t => (t.1.val, weakQuietCubeTimes x n t.2)

/-- The measurable recursive chronological region, including its boundary. -/
theorem weak_quiet_cube_ordered_measurable (x : WeakQuietExpansionCase plan prices) (n : ℕ) :
    MeasurableSet {p : (Set.Icc x.left x.right × Set.Icc x.left x.right) ×
        WeakQuietTimeCube (Set.Icc x.left x.right) n |
      WeakQuietTimesOrdered p.1.1.val p.1.2.val (weakQuietCubeTimes x n p.2)} := by
  induction n with
  | zero => exact measurableSet_le measurable_fst.fst.subtype_val measurable_fst.snd.subtype_val
  | succ n ih =>
    change MeasurableSet {p : (Set.Icc x.left x.right × Set.Icc x.left x.right) ×
        (Set.Icc x.left x.right × WeakQuietTimeCube (Set.Icc x.left x.right) n) |
      p.1.1.val ≤ p.2.1.val ∧ p.2.1.val ≤ p.1.2.val ∧
        WeakQuietTimesOrdered p.1.1.val p.2.1.val (weakQuietCubeTimes x n p.2.2)}
    exact (measurableSet_le measurable_fst.fst.subtype_val measurable_snd.fst.subtype_val).inter
      ((measurableSet_le measurable_snd.fst.subtype_val measurable_fst.snd.subtype_val).inter
        (ih.preimage ((measurable_fst.fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd)))

/-- A measurable bounded realization on the whole time cube. Each scalar gap
is clamped to its identity endpoint outside its chronological region. -/
structure WeakQuietInstantCubeOperator (x : WeakQuietExpansionCase plan prices)
    (S : WeakQuietInsertionData x) (hd : WeakQuietScalarDrift x)
    (P n : ℕ) (hn : n * x.order + P ≤ x.cap) (v u : x.Vertex)
    (π : WeakQuietWalk x.Vertex n v u) where
  apply : Set.Icc x.left x.right → Set.Icc x.left x.right →
    WeakQuietTimeCube (Set.Icc x.left x.right) n →
      TorusHk (n * x.order + P) ℝ →L[ℝ] TorusHk P ℝ
  value : ∀ a b t, WeakQuietTimesOrdered a.val b.val (weakQuietCubeTimes x n t) →
    ∀ φ, apply a b t φ = weakQuietInstantOperator x S hd P n hn v u π
      (weakQuietCubeTimes x n t) a b φ
  measurable : ∀ φ, StronglyMeasurable
    (fun p : (Set.Icc x.left x.right × Set.Icc x.left x.right) ×
      WeakQuietTimeCube (Set.Icc x.left x.right) n => apply p.1.1 p.1.2 p.2 φ)
  bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ a b t φ, ‖apply a b t φ‖ ≤ C * ‖φ‖

/-- The empty cube carries precisely the clamped native scalar evolution. -/
def weakQuietInstantCubeZero (x : WeakQuietExpansionCase plan prices)
    (S : WeakQuietInsertionData x) (hd : WeakQuietScalarDrift x) (P : ℕ)
    (hP : 0 * x.order + P ≤ x.cap) (v u : x.Vertex) (π : WeakQuietWalk x.Vertex 0 v u) :
    WeakQuietInstantCubeOperator x S hd P 0 hP v u π where
  apply a b _ := (weakQuietBackwardOperator x hd P (min a.val b.val) b).comp
    (truncateTorusHk (by omega))
  value a b _ ht φ := by
    change (weakQuietBackwardOperator x hd P (min a.val b.val) b) _ =
      (weakQuietBackwardOperator x hd P a b) _
    rw [min_eq_left ht]
  measurable φ :=
    (weak_quiet_backward_stronglyMeasurable x hd (weakQuietBackwardEvolution x hd)
      P (by simpa using hP) (truncateTorusHk (by omega) φ)).comp_measurable measurable_fst
  bound := by
    obtain ⟨C, hC, hbound⟩ := weak_quiet_backward_uniform_bound x hd P (by simpa using hP)
    exact ⟨C, hC, fun a b _ φ => (hbound a b _).trans
      (mul_le_mul_of_nonneg_left (truncateTorusHk_norm_le (by omega) φ) hC)⟩

section CubeStep
variable (x : WeakQuietExpansionCase plan prices) (S : WeakQuietInsertionData x)
  (hd : WeakQuietScalarDrift x) (P n : ℕ) (hn : (n + 1) * x.order + P ≤ x.cap)
  (v w u : x.Vertex) (π : WeakQuietWalk x.Vertex n w u)
  (V : WeakQuietInstantCubeOperator x S hd P n
    ((Nat.add_le_add_right (Nat.mul_le_mul_right x.order (Nat.le_succ n)) P).trans hn) w u π)

/-- One clamped source word step. -/
def weakQuietInstantCubeStep
    (a b : Set.Icc x.left x.right)
    (t : WeakQuietTimeCube (Set.Icc x.left x.right) (n + 1)) :
    TorusHk ((n + 1) * x.order + P) ℝ →L[ℝ] TorusHk P ℝ :=
  have hm : (n + 1) * x.order = n * x.order + x.order := Nat.succ_mul n x.order
  (V.apply a t.1 t.2).comp ((S.apply v w (n * x.order + P) (by omega) t.1).comp
    ((truncateTorusHk (by omega)).comp
      (weakQuietBackwardOperator x hd ((n + 1) * x.order + P) (min t.1.val b.val) b)))

/-- All clamped steps have a finite unweighted bound; this serves only
Bochner existence and never enters the quantitative factorial price. -/
theorem weak_quiet_instant_cube_step_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b t φ,
      ‖weakQuietInstantCubeStep x S hd P n hn v w u π V a b t φ‖ ≤ C * ‖φ‖ := by
  have hm : (n + 1) * x.order = n * x.order + x.order := Nat.succ_mul n x.order
  obtain ⟨CV, hCV, hV⟩ := V.bound
  obtain ⟨CS, hCS, hS⟩ := weak_quiet_insertion_uniform_bound x S hd.radius_pos v w
    (n * x.order + P) (by omega)
  obtain ⟨CH, hCH, hH⟩ := weak_quiet_backward_uniform_bound x hd ((n + 1) * x.order + P) hn
  refine ⟨CV * (CS * CH), mul_nonneg hCV (mul_nonneg hCS hCH), ?_⟩
  intro a b t φ
  exact (hV a t.1 t.2 _).trans ((mul_le_mul_of_nonneg_left
    ((hS t.1 t.1.property _).trans (mul_le_mul_of_nonneg_left
      ((truncateTorusHk_norm_le (by omega) _).trans (hH t.1 b φ)) hCS)) hCV).trans_eq
      (by ring))

/-- Joint strong measurability of the actual clamped word step follows from
strong operator measurability of its three genuine factors. -/
theorem weak_quiet_instant_cube_step_measurable
    (φ : TorusHk ((n + 1) * x.order + P) ℝ) :
    StronglyMeasurable (fun p : (Set.Icc x.left x.right × Set.Icc x.left x.right) ×
      WeakQuietTimeCube (Set.Icc x.left x.right) (n + 1) =>
        weakQuietInstantCubeStep x S hd P n hn v w u π V p.1.1 p.1.2 p.2 φ) := by
  have hm : (n + 1) * x.order = n * x.order + x.order := Nat.succ_mul n x.order
  let T := (Set.Icc x.left x.right × Set.Icc x.left x.right) ×
    WeakQuietTimeCube (Set.Icc x.left x.right) (n + 1)
  let : TopologicalSpace.SeparableSpace (TorusHk (n * x.order + P + x.order) ℝ) :=
    CoupledEnergy.Variational.torusHkSeparableSpace _
  let : TopologicalSpace.SeparableSpace (TorusHk (n * x.order + P) ℝ) :=
    CoupledEnergy.Variational.torusHkSeparableSpace _
  borelize (TorusHk (n * x.order + P + x.order) ℝ) (TorusHk (n * x.order + P) ℝ)
  have hH := weak_quiet_backward_stronglyMeasurable_action x hd
    ((n + 1) * x.order + P) hn
    (fun p : T => p.2.1) (fun p : T => p.1.2)
    measurable_snd.fst measurable_fst.snd (fun _ => φ) stronglyMeasurable_const
  have hC := (truncateTorusHk (E := ℝ)
    (show n * x.order + P + x.order ≤ (n + 1) * x.order + P by omega)).continuous.comp_stronglyMeasurable hH
  have hS := CoupledEnergy.Variational.stronglyMeasurable_operator_action
    (fun p : T => S.apply v w (n * x.order + P) (by omega) p.2.1)
    (fun ψ => (S.measurable v w (n * x.order + P) (by omega) ψ).comp_measurable
      measurable_snd.fst.subtype_val) hC
  exact CoupledEnergy.Variational.stronglyMeasurable_operator_action
    (fun p : T => V.apply p.1.1 p.2.1 p.2.2)
    (fun ψ => (V.measurable ψ).comp_measurable
      ((measurable_fst.fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd)) hS

/-- One measurable cube step is the literal pointwise source word on its
chronological region. -/
theorem weak_quiet_instant_cube_step_value
    (a b : Set.Icc x.left x.right)
    (t : WeakQuietTimeCube (Set.Icc x.left x.right) (n + 1))
    (ht : WeakQuietTimesOrdered a.val b.val (weakQuietCubeTimes x (n + 1) t))
    (φ : TorusHk ((n + 1) * x.order + P) ℝ) :
    weakQuietInstantCubeStep x S hd P n hn v w u π V a b t φ =
      weakQuietInstantOperator x S hd P (n + 1) hn v u ⟨w, π⟩
        (weakQuietCubeTimes x (n + 1) t) a b φ := by
  change a.val ≤ t.1.val ∧ t.1.val ≤ b.val ∧
    WeakQuietTimesOrdered a.val t.1.val (weakQuietCubeTimes x n t.2) at ht
  dsimp only [weakQuietInstantCubeStep, ContinuousLinearMap.comp_apply]
  rw [min_eq_left ht.2.1, V.value a t.1 t.2 ht.2.2]
  rfl

/-- The measurable clamped cube operator for one additional source. -/
def weakQuietInstantCubeSucc :
    WeakQuietInstantCubeOperator x S hd P (n + 1) hn v u ⟨w, π⟩ where
  apply := weakQuietInstantCubeStep x S hd P n hn v w u π V
  value := weak_quiet_instant_cube_step_value x S hd P n hn v w u π V
  measurable := weak_quiet_instant_cube_step_measurable x S hd P n hn v w u π V
  bound := weak_quiet_instant_cube_step_bound x S hd P n hn v w u π V

end CubeStep

/-- Simultaneous bounded measurable realizations of every retained pointwise
word, before choosing any positive representative. -/
theorem weak_quiet_instant_cube_operator (x : WeakQuietExpansionCase plan prices)
    (S : WeakQuietInsertionData x) (hd : WeakQuietScalarDrift x)
    (P n : ℕ) (hn : n * x.order + P ≤ x.cap) (v u : x.Vertex)
    (π : WeakQuietWalk x.Vertex n v u) :
    Nonempty (WeakQuietInstantCubeOperator x S hd P n hn v u π) := by
  induction n generalizing v with
  | zero => exact ⟨weakQuietInstantCubeZero x S hd P hn v u π⟩
  | succ n ih =>
    have hm : (n + 1) * x.order = n * x.order + x.order := Nat.succ_mul n x.order
    obtain ⟨w, π⟩ := π
    obtain ⟨V⟩ := ih (by omega) w π
    exact ⟨weakQuietInstantCubeSucc x S hd P n hn v w u π V⟩

/-- Positive representatives are strongly measurable whenever their native
pairings against the retained positive tests are measurable. The Sobolev
value embedding and the dense test embedding give a continuous injective
map into one separable Hilbert carrier. -/
theorem weak_quiet_positive_representatives_measurable {T : Type*} [MeasurableSpace T]
    (K P : ℕ) (Z : T → TorusHk K ℝ) (f : TorusHk 0 ℝ)
    (O : T → TorusHk P ℝ →L[ℝ] TorusHk 0 ℝ)
    (hO : ∀ φ, StronglyMeasurable (fun t => O t φ))
    (hZ : ∀ t φ, inner ℝ (truncateTorusHk (Nat.zero_le K) (Z t))
      (truncateTorusHk (Nat.zero_le P) φ) = inner ℝ f (O t φ)) :
    StronglyMeasurable Z := by
  let : TopologicalSpace.SeparableSpace (TorusHk K ℝ) := CoupledEnergy.Variational.torusHkSeparableSpace K
  let : TopologicalSpace.SeparableSpace (TorusHk P ℝ) := CoupledEnergy.Variational.torusHkSeparableSpace P
  borelize (TorusHk K ℝ) (TorusHk P ℝ)
  let B : TorusHk K ℝ →L[ℝ] TorusHk P ℝ :=
    (truncateTorusHk (E := ℝ) (Nat.zero_le P)).adjoint.comp (truncateTorusHk (Nat.zero_le K))
  have hB (z : TorusHk K ℝ) (φ : TorusHk P ℝ) :
      inner ℝ (B z) φ = inner ℝ (truncateTorusHk (Nat.zero_le K) z)
        (truncateTorusHk (Nat.zero_le P) φ) :=
    ContinuousLinearMap.adjoint_inner_left _ _ _
  have hi : Function.Injective B := by
    intro z w he
    have hh := (CycleJointProofs.truncateTorusHk_denseRange (E := ℝ) (Nat.zero_le P)).equalizer
      (continuous_const.inner continuous_id : Continuous
        (fun φ : TorusHk 0 ℝ => inner ℝ (truncateTorusHk (Nat.zero_le K) z) φ))
      (continuous_const.inner continuous_id : Continuous
        (fun φ : TorusHk 0 ℝ => inner ℝ (truncateTorusHk (Nat.zero_le K) w) φ))
      (funext fun φ => by
        dsimp only [Function.comp_apply]
        rw [← hB, ← hB, he])
    have hz := ext_inner_right ℝ (congrFun hh)
    apply TorusHk.ext_value
    exact congrArg (fun y : TorusHk 0 ℝ => CoupledEnergy.Galerkin.torusHkValueCLM y) hz
  have hm : StronglyMeasurable (fun t => B (Z t)) := by
    apply weak_quiet_stronglyMeasurable_of_inner
    intro φ
    have hh : (fun t => inner ℝ (B (Z t)) φ) = (fun t => inner ℝ f (O t φ)) :=
      funext fun t => (hB _ _).trans (hZ t φ)
    rw [hh]
    exact (stronglyMeasurable_const.inner (hO φ)).measurable
  exact ((B.continuous.measurableEmbedding hi).measurable_comp_iff.mp hm.measurable).stronglyMeasurable

/-- Positive representatives of the chronological pointwise words, chosen
simultaneously and extended by zero off the closed chronological simplex. -/
theorem weak_quiet_point_representatives (x : WeakQuietExpansionCase plan prices)
    (S : WeakQuietInsertionData x) (hd : WeakQuietScalarDrift x)
    (n K : ℕ) (hcap : K + n * x.order ≤ x.cap) (v u : x.Vertex)
    (π : WeakQuietWalk x.Vertex n v u)
    (V : WeakQuietInstantCubeOperator x S hd 0 n (by omega) v u π)
    {δ G : ℝ} (hδ : 0 < δ) (hG0 : 0 ≤ G)
    (hlen : (n + 1 : ℕ) * δ ≤ x.right - x.left)
    (hG : WeakQuietGapPriceBound x δ G) (f : TorusHk 0 ℝ) :
    ∃ Z : WeakQuietTimeCube (Set.Icc x.left x.right) n → TorusHk K ℝ,
      StronglyMeasurable Z ∧
      (∀ t, Real.sqrt (factorialNormSq x.radius (Z t).val) ≤
        ‖f‖ * G * weakQuietInstantCost x n v u π) ∧
      ∀ t (φ : TorusHk (n * x.order) ℝ),
        inner ℝ (truncateTorusHk (Nat.zero_le K) (Z t))
          (truncateTorusHk (Nat.zero_le (n * x.order)) φ) =
        inner ℝ f (if WeakQuietTimesOrdered x.left x.right (weakQuietCubeTimes x n t)
          then V.apply ⟨x.left, ⟨le_rfl, x.heat_window.1.le⟩⟩
            ⟨x.right, ⟨x.heat_window.1.le, le_rfl⟩⟩ t φ else 0) := by
  let a : Set.Icc x.left x.right := ⟨x.left, ⟨le_rfl, x.heat_window.1.le⟩⟩
  let b : Set.Icc x.left x.right := ⟨x.right, ⟨x.heat_window.1.le, le_rfl⟩⟩
  let Ω := {t | WeakQuietTimesOrdered x.left x.right (weakQuietCubeTimes x n t)}
  have hmab : Measurable (fun t : WeakQuietTimeCube (Set.Icc x.left x.right) n => ((a, b), t)) :=
    (measurable_const.prodMk measurable_const).prodMk measurable_id
  have hΩ : MeasurableSet Ω := (weak_quiet_cube_ordered_measurable x n).preimage hmab
  let ell : TorusHk 0 ℝ →L[ℝ] ℝ := innerSL ℝ f
  have he : WeakScalarFunctionalBound x.radius 0 ell ‖f‖ := by
    intro φ
    change |inner ℝ f φ| ≤ _
    rw [CycleJointProofs.factorialNormSq_order_zero_measure,
      Real.sqrt_sq (norm_nonneg _)]
    exact abs_real_inner_le_norm _ _
  have hp (t) (ht : t ∈ Ω) : ∃ Z : TorusHk K ℝ,
      Real.sqrt (factorialNormSq x.radius Z.val) ≤ ‖f‖ * G * weakQuietInstantCost x n v u π ∧
      ∀ φ : TorusHk (n * x.order) ℝ,
        inner ℝ (truncateTorusHk (Nat.zero_le K) Z)
          (truncateTorusHk (Nat.zero_le (n * x.order)) φ) = inner ℝ f (V.apply a b t φ) := by
    obtain ⟨Z, hZ, hz⟩ := weak_quiet_instant_word_represented x S hd hδ hG n 0 K
      (by omega) v u π (weakQuietCubeTimes x n t) x.left x.right le_rfl le_rfl ht
      (weak_quiet_has_long_gap _ hlen) ell (norm_nonneg f) he
    refine ⟨Z, hZ, ?_⟩
    intro φ
    exact (hz φ).trans (congrArg (fun z => inner ℝ f z) (V.value a b t ht φ).symm)
  let Z (t) : TorusHk K ℝ := if ht : t ∈ Ω then (hp t ht).choose else 0
  let O (t) : TorusHk (n * x.order) ℝ →L[ℝ] TorusHk 0 ℝ :=
    if t ∈ Ω then V.apply a b t else 0
  have hpair (t) (φ : TorusHk (n * x.order) ℝ) :
      inner ℝ (truncateTorusHk (Nat.zero_le K) (Z t))
        (truncateTorusHk (Nat.zero_le (n * x.order)) φ) = inner ℝ f (O t φ) := by
    by_cases ht : t ∈ Ω
    · simpa only [Z, O, dite_eq_left ht, ite_eq_left ht] using (hp t ht).choose_spec.2 φ
    · simp only [Z, O, dite_eq_right ht, ite_eq_right ht, map_zero, zero_apply,
        inner_zero_right, inner_zero_left]
  have hOm (φ : TorusHk (n * x.order) ℝ) : StronglyMeasurable (fun t => O t φ) := by
    have hh : StronglyMeasurable (fun t => if t ∈ Ω then V.apply a b t φ else 0) :=
      StronglyMeasurable.ite hΩ ((V.measurable φ).comp_measurable hmab) stronglyMeasurable_const
    have he : (fun t => O t φ) = (fun t => if t ∈ Ω then V.apply a b t φ else 0) := by
      funext t
      by_cases ht : t ∈ Ω
      · simp only [O, ite_eq_left ht]
      · simp only [O, ite_eq_right ht, zero_apply]
    rw [he]
    exact hh
  refine ⟨Z, weak_quiet_positive_representatives_measurable K (n * x.order) Z f O hOm hpair, ?_, ?_⟩
  · intro t
    by_cases ht : t ∈ Ω
    · simpa only [Z, dite_eq_left ht] using (hp t ht).choose_spec.1
    · simpa only [Z, dite_eq_right ht, sqrt_fNSq_torus_zero] using
        mul_nonneg (mul_nonneg (norm_nonneg f) hG0) (weak_quiet_instant_cost_nonneg x hd n v u π)
  · intro t φ
    by_cases ht : t ∈ Ω
    · have ht' : WeakQuietTimesOrdered x.left x.right (weakQuietCubeTimes x n t) := ht
      simp only [ite_eq_left ht']
      simpa only [O, ite_eq_left ht] using hpair t φ
    · have ht' : ¬ WeakQuietTimesOrdered x.left x.right (weakQuietCubeTimes x n t) := ht
      simp only [ite_eq_right ht']
      simpa only [O, ite_eq_right ht, zero_apply] using hpair t φ

attribute [local instance] Measure.Subtype.measureSpace

instance weakQuietMarginVolumeFinite (x : WeakQuietExpansionCase plan prices) :
    IsFiniteMeasure (volume : Measure (Set.Icc x.left x.right)) :=
  ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
    exact measure_Icc_lt_top⟩

/-- The finite product measure on all chronological coordinates. -/
def weakQuietTimeCubeMeasure (x : WeakQuietExpansionCase plan prices) :
    (n : ℕ) → Measure (WeakQuietTimeCube (Set.Icc x.left x.right) n)
  | 0 => Measure.dirac PUnit.unit
  | n + 1 => (volume : Measure (Set.Icc x.left x.right)).prod (weakQuietTimeCubeMeasure x n)

instance weakQuietTimeCubeFinite (x : WeakQuietExpansionCase plan prices) (n : ℕ) :
    IsFiniteMeasure (weakQuietTimeCubeMeasure x n) := by
  induction n with
  | zero => exact inferInstanceAs (IsFiniteMeasure (Measure.dirac (PUnit.unit : PUnit)))
  | succ n ih =>
    let : IsFiniteMeasure (weakQuietTimeCubeMeasure x n) := ih
    exact inferInstanceAs (IsFiniteMeasure
      ((volume : Measure (Set.Icc x.left x.right)).prod (weakQuietTimeCubeMeasure x n)))

/-- The cube has exactly the nth power of the quiet margin length as its volume. -/
theorem weak_quiet_time_cube_volume (x : WeakQuietExpansionCase plan prices) (n : ℕ) :
    weakQuietTimeCubeMeasure x n Set.univ = ENNReal.ofReal (x.right - x.left) ^ n := by
  induction n with
  | zero =>
    simp only [weakQuietTimeCubeMeasure, pow_zero]
    exact Measure.dirac_apply_of_mem (Set.mem_univ PUnit.unit)
  | succ n ih =>
    change ((volume : Measure (Set.Icc x.left x.right)).prod (weakQuietTimeCubeMeasure x n)) Set.univ = _
    rw [← Set.univ_prod_univ, Measure.prod_prod, ih,
      Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet, Real.volume_Icc, pow_succ]
    exact mul_comm _ _

/-- Real-valued cube volume, used after Bochner norm integration. -/
theorem weak_quiet_time_cube_volume_real (x : WeakQuietExpansionCase plan prices) (n : ℕ) :
    (weakQuietTimeCubeMeasure x n).real Set.univ = (x.right - x.left) ^ n := by
  rw [measureReal_def, weak_quiet_time_cube_volume, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (sub_nonneg.mpr x.heat_window.1.le)]

/-- A chronological cube integrand is Bochner integrable before Fubini is
used. Its finite unweighted bound serves only existence. -/
theorem weak_quiet_cube_word_integrable (x : WeakQuietExpansionCase plan prices)
    (S : WeakQuietInsertionData x) (hd : WeakQuietScalarDrift x)
    (P n : ℕ) (hn : n * x.order + P ≤ x.cap) (v u : x.Vertex)
    (π : WeakQuietWalk x.Vertex n v u) (V : WeakQuietInstantCubeOperator x S hd P n hn v u π)
    (a b : Set.Icc x.left x.right) (φ : TorusHk (n * x.order + P) ℝ) :
    Integrable (fun t => if WeakQuietTimesOrdered a.val b.val (weakQuietCubeTimes x n t)
      then V.apply a b t φ else 0) (weakQuietTimeCubeMeasure x n) := by
  have hmab : Measurable (fun t : WeakQuietTimeCube (Set.Icc x.left x.right) n => ((a, b), t)) :=
    (measurable_const.prodMk measurable_const).prodMk measurable_id
  have hΩ := (weak_quiet_cube_ordered_measurable x n).preimage hmab
  have hm : StronglyMeasurable (fun t =>
      if WeakQuietTimesOrdered a.val b.val (weakQuietCubeTimes x n t) then V.apply a b t φ else 0) :=
    StronglyMeasurable.ite hΩ ((V.measurable φ).comp_measurable hmab) stronglyMeasurable_const
  obtain ⟨C, hC, hbound⟩ := V.bound
  apply (integrable_const (C * ‖φ‖)).mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  by_cases ht : WeakQuietTimesOrdered a.val b.val (weakQuietCubeTimes x n t)
  · simpa only [ite_eq_left ht] using hbound a b t φ
  · simpa only [ite_eq_right ht, norm_zero] using mul_nonneg hC (norm_nonneg φ)

/-- A quiet margin-subtype integral of a chronological indicator is exactly the
ordinary real interval integral. No integrability convention is involved. -/
theorem weak_quiet_subtype_indicator_interval (x : WeakQuietExpansionCase plan prices)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : Set.Icc x.left x.right) (hab : a.val ≤ b.val) (g : ℝ → E) :
    (∫ t : Set.Icc x.left x.right,
      if a.val ≤ t.val ∧ t.val ≤ b.val then g t.val else 0) = ∫ t in a.val..b.val, g t := by
  have he : (fun t : Set.Icc x.left x.right =>
      if a.val ≤ t.val ∧ t.val ≤ b.val then g t.val else 0) =
      (fun t : Set.Icc x.left x.right => (Set.Icc a.val b.val).indicator g t.val) := by
    funext t
    by_cases ht : t.val ∈ Set.Icc a.val b.val
    · rw [ite_eq_left (Set.mem_Icc.mp ht), Set.indicator_of_mem ht]
    · rw [ite_eq_right (fun h => ht (Set.mem_Icc.mpr h)), Set.indicator_of_notMem ht]
  rw [he, integral_subtype measurableSet_Icc, integral_indicator measurableSet_Icc,
    Measure.restrict_restrict measurableSet_Icc,
    Set.inter_eq_left.mpr (Set.Icc_subset_Icc a.property.1 b.property.2),
    integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]

/-- On the chronological simplex the cube step factors through the prefix
word and its literal latest source. This equality uses native values only. -/
theorem weak_quiet_cube_word_split (x : WeakQuietExpansionCase plan prices)
    (S : WeakQuietInsertionData x) (hd : WeakQuietScalarDrift x)
    (n : ℕ) (hn : (n + 1) * x.order ≤ x.cap) (v w u : x.Vertex)
    (π : WeakQuietWalk x.Vertex n w u)
    (V : WeakQuietInstantCubeOperator x S hd 0 (n + 1) hn v u ⟨w, π⟩)
    (W : WeakQuietInstantCubeOperator x S hd 0 n
      ((Nat.mul_le_mul_right x.order (Nat.le_succ n)).trans hn) w u π)
    (a b τ : Set.Icc x.left x.right)
    (t : WeakQuietTimeCube (Set.Icc x.left x.right) n)
    (φ : TorusHk ((n + 1) * x.order) ℝ) :
    (if WeakQuietTimesOrdered a.val b.val (weakQuietCubeTimes x (n + 1) (τ, t))
      then V.apply a b (τ, t) φ else 0) =
    if a.val ≤ τ.val ∧ τ.val ≤ b.val then
      (if WeakQuietTimesOrdered a.val τ.val (weakQuietCubeTimes x n t) then
        W.apply a τ t
          (S.apply v w (n * x.order) (by rw [← Nat.succ_mul]; exact hn) τ.val
            (truncateTorusHk (by rw [Nat.succ_mul])
              (weakQuietBackwardOperator x hd ((n + 1) * x.order) τ.val b.val φ))) else 0)
      else 0 := by
  dsimp only [weakQuietCubeTimes, WeakQuietTimesOrdered]
  by_cases ha : a.val ≤ τ.val
  · by_cases hb : τ.val ≤ b.val
    · by_cases hp : WeakQuietTimesOrdered a.val τ.val (weakQuietCubeTimes x n t)
      · simp only [ha, hb, hp, and_self, ite_true]
        rw [V.value a b (τ, t) ⟨ha, hb, hp⟩, W.value a τ t hp]
        rfl
      · simp only [ha, hb, hp, and_false, and_true, ite_false, ite_true]
    · simp only [hb, and_false, false_and, ite_false]
  · simp only [ha, false_and, ite_false]


/-- The measurable chronological cube integral is the actual recursively
ordered Bochner path, with exactly the original finite source and test reserve. -/
theorem weak_quiet_cube_word_value (x : WeakQuietExpansionCase plan prices)
    (S : WeakQuietInsertionData x) (hd : WeakQuietScalarDrift x)
    (n : ℕ) (hn : n ≤ prices.depth x.R) (v u : x.Vertex)
    (π : WeakQuietWalk x.Vertex n v u)
    (V : WeakQuietInstantCubeOperator x S hd 0 n (x.path_reserve n hn) v u π)
    (a b : Set.Icc x.left x.right) (hab : a.val ≤ b.val) (φ : TorusHk (n * x.order) ℝ) :
    (∫ t, if WeakQuietTimesOrdered a.val b.val (weakQuietCubeTimes x n t)
      then V.apply a b t φ else 0 ∂(weakQuietTimeCubeMeasure x n)) =
      weakQuietWalkDual x S (weakQuietBackwardEvolution x hd) n hn v u π a b φ := by
  induction n generalizing v b with
  | zero =>
    change (∫ t : PUnit, if a.val ≤ b.val then V.apply a b t φ else 0
      ∂(Measure.dirac PUnit.unit)) = _
    rw [integral_dirac]
    rw [ite_eq_left hab, V.value a b PUnit.unit hab]
    rfl
  | succ n ih =>
    obtain ⟨w, π⟩ := π
    obtain ⟨W⟩ := weak_quiet_instant_cube_operator x S hd 0 n
      (x.path_reserve n (by omega)) w u π
    let ψ (τ : ℝ) : TorusHk (n * x.order) ℝ :=
      S.apply v w (n * x.order)
        (by simpa only [Nat.succ_mul] using x.path_reserve (n + 1) hn) τ
          (truncateTorusHk (by rw [Nat.succ_mul])
            (weakQuietBackwardOperator x hd ((n + 1) * x.order) τ b.val φ))
    let g (τ : ℝ) := weakQuietWalkDual x S (weakQuietBackwardEvolution x hd)
      n (by omega) w u π a.val τ (ψ τ)
    have hF := weak_quiet_cube_word_integrable x S hd 0 (n + 1)
      (x.path_reserve (n + 1) hn) v u ⟨w, π⟩ V a b φ
    calc
      _ = ∫ τ : Set.Icc x.left x.right, ∫ t,
          if WeakQuietTimesOrdered a.val b.val (weakQuietCubeTimes x (n + 1) (τ, t))
          then V.apply a b (τ, t) φ else 0 ∂(weakQuietTimeCubeMeasure x n) :=
        integral_prod _ hF
      _ = ∫ τ : Set.Icc x.left x.right,
          if a.val ≤ τ.val ∧ τ.val ≤ b.val then g τ.val else 0 := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro τ
        have hs := weak_quiet_cube_word_split x S hd n (x.path_reserve (n + 1) hn)
          v w u π V W a b τ
        simp_rw [hs]
        by_cases ht : a.val ≤ τ.val ∧ τ.val ≤ b.val
        · simp only [ite_eq_left ht]
          exact ih (hn := by omega) w π W τ ht.1 (ψ τ.val)
        · simp only [ite_eq_right ht, integral_zero]
      _ = ∫ τ in a.val..b.val, g τ := weak_quiet_subtype_indicator_interval x a b hab g
      _ = _ := rfl

/-- A bounded measurable positive word is genuinely Bochner integrable, and
its factorial norm is bounded by the same constant times the finite volume. -/
theorem weak_quiet_factorial_integral_bound {T : Type*} [MeasurableSpace T]
    {μ : Measure T} [IsFiniteMeasure μ] (K : ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (Z : T → TorusHk K ℝ) (hm : StronglyMeasurable Z) (C : ℝ)
    (hb : ∀ t, Real.sqrt (factorialNormSq ρ (Z t).val) ≤ C) :
    Integrable Z μ ∧
      Real.sqrt (factorialNormSq ρ (∫ t, Z t ∂μ).val) ≤ C * μ.real Set.univ := by
  have hn (t) : ‖Z t‖ ≤ C / Real.sqrt (factorialWeightMin ρ K) :=
    (CoupledEnergy.Variational.jetNorm_le_factorialRoot ρ hρ (Z t).val).trans
      (div_le_div_of_nonneg_right (hb t) (Real.sqrt_nonneg _))
  have hZi : Integrable Z μ := (integrable_const (C / Real.sqrt (factorialWeightMin ρ K))).mono'
    hm.aestronglyMeasurable (Filter.Eventually.of_forall hn)
  let L : TorusHk K ℝ →L[ℝ] JetL2 (volume.restrict unitCube) K ℝ :=
    (CoupledEnergy.Variational.factorialWeightedJetCLM ρ K).comp
      (torusHkGraph (E := ℝ) K).toSubmodule.subtypeL
  have hL (t) : ‖L (Z t)‖ ≤ C := by
    change ‖CoupledEnergy.Variational.factorialWeightedJet ρ (Z t).val‖ ≤ C
    rw [CoupledEnergy.Variational.factorialWeightedJet_norm]
    exact hb t
  have hh := norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall hL)
  rw [L.integral_comp_comm hZi] at hh
  change ‖CoupledEnergy.Variational.factorialWeightedJet ρ (∫ t, Z t ∂μ).val‖ ≤ _ at hh
  rw [CoupledEnergy.Variational.factorialWeightedJet_norm] at hh
  exact ⟨hZi, hh⟩

/-- The integral of the positive pointwise representatives represents the
original recursive dual path, with its full positive factorial price. -/
theorem weak_quiet_integrated_word_represented (x : WeakQuietExpansionCase plan prices)
    (S : WeakQuietInsertionData x) (hd : WeakQuietScalarDrift x)
    (n K : ℕ) (hn : n ≤ prices.depth x.R) (hcap : K + n * x.order ≤ x.cap)
    (v u : x.Vertex) (π : WeakQuietWalk x.Vertex n v u)
    {δ G : ℝ} (hδ : 0 < δ) (hG0 : 0 ≤ G)
    (hlen : (n + 1 : ℕ) * δ ≤ x.right - x.left)
    (hG : WeakQuietGapPriceBound x δ G) (f : TorusHk 0 ℝ) :
    ∃ Z : TorusHk K ℝ,
      Real.sqrt (factorialNormSq x.radius Z.val) ≤
        (‖f‖ * G * weakQuietInstantCost x n v u π) * (x.right - x.left) ^ n ∧
      ∀ φ : TorusHk (n * x.order) ℝ,
        inner ℝ (truncateTorusHk (Nat.zero_le K) Z)
          (truncateTorusHk (Nat.zero_le (n * x.order)) φ) =
        inner ℝ f (weakQuietWalkDual x S (weakQuietBackwardEvolution x hd) n hn v u π
          x.left x.right φ) := by
  obtain ⟨V⟩ := weak_quiet_instant_cube_operator x S hd 0 n (x.path_reserve n hn) v u π
  obtain ⟨Z, hm, hb, hp⟩ := weak_quiet_point_representatives x S hd n K hcap v u π V
    hδ hG0 hlen hG f
  obtain ⟨hZi, hprice⟩ := weak_quiet_factorial_integral_bound (μ := weakQuietTimeCubeMeasure x n)
    K x.radius hd.radius_pos Z hm (‖f‖ * G * weakQuietInstantCost x n v u π) hb
  refine ⟨∫ t, Z t ∂(weakQuietTimeCubeMeasure x n), ?_, ?_⟩
  · simpa only [weak_quiet_time_cube_volume_real] using hprice
  · intro φ
    let a : Set.Icc x.left x.right := ⟨x.left, ⟨le_rfl, x.heat_window.1.le⟩⟩
    let b : Set.Icc x.left x.right := ⟨x.right, ⟨x.heat_window.1.le, le_rfl⟩⟩
    let O (t) := if WeakQuietTimesOrdered x.left x.right (weakQuietCubeTimes x n t)
      then V.apply a b t φ else 0
    have hOi := weak_quiet_cube_word_integrable x S hd 0 n (x.path_reserve n hn) v u π V a b φ
    let L := (innerSL ℝ (truncateTorusHk (Nat.zero_le (n * x.order)) φ)).comp
      (truncateTorusHk (E := ℝ) (Nat.zero_le K))
    calc
      _ = L (∫ t, Z t ∂(weakQuietTimeCubeMeasure x n)) := real_inner_comm _ _
      _ = ∫ t, L (Z t) ∂(weakQuietTimeCubeMeasure x n) := (L.integral_comp_comm hZi).symm
      _ = ∫ t, inner ℝ f (O t) ∂(weakQuietTimeCubeMeasure x n) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun t => (real_inner_comm _ _).trans (hp t φ)
      _ = inner ℝ f (∫ t, O t ∂(weakQuietTimeCubeMeasure x n)) :=
        (innerSL ℝ f).integral_comp_comm hOi
      _ = _ := congrArg (fun z => inner ℝ f z)
        (weak_quiet_cube_word_value x S hd n hn v u π V a b x.heat_window.1.le φ)

end AVRegularity.WeakEntryProofs.Assembly
end
