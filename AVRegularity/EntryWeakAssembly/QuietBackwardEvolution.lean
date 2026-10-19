-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeakAssembly.Assembly.WeakQuietExpansionOfIngredients
import AVRegularity.CycleComparison.Coarse.Energy.Zero
import AVRegularity.CycleComparison.Error.WeakSolution

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.WeakEntryProofs.Assembly

/-! Nonnegative powers of the actual quiet margin matrix have dimension-free Schur
bounds. No record-size matrix is substituted for a coefficient bound. -/

private theorem matrix_power_budget {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : ι → ι → ℝ) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ v u, 0 ≤ b v u)
    (hr : ∀ v, ∑ u, b v u ≤ C) (hc : ∀ u, ∑ v, b v u ≤ C) (n : ℕ) :
    (∀ v u, 0 ≤ (Matrix.of b ^ n) v u) ∧
    (∀ v, ∑ u, (Matrix.of b ^ n) v u ≤ C ^ n) ∧
    (∀ u, ∑ v, (Matrix.of b ^ n) v u ≤ C ^ n) := by
  induction n with
  | zero =>
    simp only [pow_zero, Matrix.one_apply]
    refine ⟨fun v u => ?_, fun v => ?_, fun u => ?_⟩
    · split <;> norm_num
    · simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      exact le_rfl
    · simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      exact le_rfl
  | succ n ih =>
    obtain ⟨hn, hnr, hnc⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro v u
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun j _ => mul_nonneg (hn v j) (hb j u)
    · intro v
      simp only [pow_succ, Matrix.mul_apply]
      rw [Finset.sum_comm]
      calc
        (∑ j, ∑ u, (Matrix.of b ^ n) v j * b j u) =
            ∑ j, (Matrix.of b ^ n) v j * ∑ u, b j u := by
          simp only [Finset.mul_sum]
        _ ≤ ∑ j, (Matrix.of b ^ n) v j * C :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hr j) (hn v j)
        _ = (∑ j, (Matrix.of b ^ n) v j) * C := (Finset.sum_mul _ _ _).symm
        _ ≤ C ^ n * C := mul_le_mul_of_nonneg_right (hnr v) hC
        _ = C ^ (n + 1) := (pow_succ _ _).symm
    · intro u
      simp only [pow_succ, Matrix.mul_apply]
      rw [Finset.sum_comm]
      calc
        (∑ j, ∑ v, (Matrix.of b ^ n) v j * b j u) =
            ∑ j, (∑ v, (Matrix.of b ^ n) v j) * b j u := by
          simp only [Finset.sum_mul]
        _ ≤ ∑ j, C ^ n * b j u :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hnc j) (hb j u)
        _ = C ^ n * ∑ j, b j u := (Finset.mul_sum _ _ _).symm
        _ ≤ C ^ n * C := mul_le_mul_of_nonneg_left (hc u) (pow_nonneg hC _)
        _ = C ^ (n + 1) := (pow_succ _ _).symm

/-- Both Schur sums of the actual quiet margin kernel, including the empty path. -/
theorem weak_quiet_margin_schur : WeakQuietMarginSchurStatement := by
  intro prices B A R ι _ _ b C hC hb hr hc
  have hp := matrix_power_budget b C hC hb hr hc
  refine ⟨?_, ?_, ?_⟩
  · intro v u
    unfold weakQuietMarginPathKernel
    apply add_nonneg
    · split <;> [exact prices.nonneg R 0; exact le_rfl]
    · exact Finset.sum_nonneg fun n _ => mul_nonneg (prices.nonneg R _) ((hp _).1 v u)
  · intro v
    unfold weakQuietMarginPathKernel
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    apply add_le_add le_rfl
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro n _
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left ((hp _).2.1 v) (prices.nonneg R _)
  · intro u
    unfold weakQuietMarginPathKernel
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    apply add_le_add le_rfl
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro n _
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left ((hp _).2.2 u) (prices.nonneg R _)

/-- The smoothing layer with the finite quiet margin-matrix and scalar Schur algebra discharged. -/
theorem weak_quiet_smoothing_of_quiet_margin_estimates (plan : WeakPassagePlan)
    (prices : WeakQuietPathPrices)
    (hcoeff : ∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A), 0 ≤ plan.coeffC R)
    (hexpand : WeakQuietMarginExpansionStatement plan prices)
    (hprice : WeakQuietMarginPriceStatement plan prices) : WeakQuietSmoothingStatement plan := by
  exact weak_quiet_smoothing_of_quiet_margin_ingredients plan prices hcoeff hexpand hprice
    weak_quiet_margin_schur

end AVRegularity.WeakEntryProofs.Assembly
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Coarse
namespace AVRegularity.WeakEntryProofs.Assembly

/-! The finite graph underlying the quiet margin expansion, and compatibility of
the native backward scalar evolutions. Actual source edges strictly increase
the weak component rank; an arbitrary majorant matrix need not do so. -/

/-- Products over vertex walks are exactly the powers of the given matrix.
Repeated identities have already been aggregated into its single b-entry. -/
theorem weak_quiet_walk_weight_sum {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : ι → ι → ℝ) (n : ℕ) (v u : ι) :
    (∑ π : WeakQuietWalk ι n v u, weakQuietWalkWeight b n v u π) =
      (Matrix.of b ^ n) v u := by
  induction n generalizing v with
  | zero =>
    by_cases h : v = u
    · subst v
      let : Subsingleton (WeakQuietWalk ι 0 u u) := by
        change Subsingleton (PLift (u = u))
        infer_instance
      let : Nonempty (WeakQuietWalk ι 0 u u) := ⟨PLift.up rfl⟩
      let : Unique (WeakQuietWalk ι 0 u u) :=
        ⟨⟨PLift.up rfl⟩, fun π => Subsingleton.elim _ _⟩
      simp only [pow_zero, Matrix.one_apply, ite_true, weakQuietWalkWeight]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one,
        Finset.card_univ, Fintype.card_unique, Nat.cast_one]
    · have : IsEmpty (WeakQuietWalk ι 0 v u) := ⟨fun π => h π.down⟩
      simp only [Finset.univ_eq_empty, Finset.sum_empty, pow_zero, Matrix.one_apply,
        h, ite_false]
  | succ n ih =>
    let e : WeakQuietWalk ι (n + 1) v u ≃ (Σ w : ι, WeakQuietWalk ι n w u) :=
      Equiv.refl _
    calc
      _ = ∑ π : (Σ w : ι, WeakQuietWalk ι n w u),
          b v π.1 * weakQuietWalkWeight b n π.1 u π.2 :=
        Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = _ := ?_
    rw [Fintype.sum_sigma, pow_succ', Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro w _
    change (∑ π : WeakQuietWalk ι n w u, b v w * weakQuietWalkWeight b n w u π) =
      b v w * (Matrix.of b ^ n) w u
    rw [← Finset.mul_sum, ih]

/-- A zero-length backward scalar evolution is the identity, independently
of the choice of native solution outside its window. -/
theorem weak_quiet_backward_same_time {plan : WeakPassagePlan}
    {prices : WeakQuietPathPrices} (x : WeakQuietExpansionCase plan prices)
    (H : WeakQuietBackwardEvolution x) (P : ℕ) (hP : P ≤ x.cap)
    (a : ℝ) (ha : a ∈ Set.Icc x.left x.right) (φ : TorusHk P ℝ) :
    H.apply P a a φ = φ := by
  obtain ⟨z, zw, hs, he⟩ := H.native P hP a a ha.1 le_rfl ha.2 φ
  exact he.trans (hs.2.2.2.1 0)

/-- The genuine native backward evolution commutes with every lowering of
the test reserve. Uniqueness is used only on the actual reflected subwindow. -/
theorem weak_quiet_backward_truncate {plan : WeakPassagePlan}
    {prices : WeakQuietPathPrices} (x : WeakQuietExpansionCase plan prices)
    (hd : WeakScalarTorusDrift (x.c.D.κ x.c.M) x.radius x.left x.right
      (streamVel (x.c.D.Φ (x.i - 1))) x.cap)
    (H : WeakQuietBackwardEvolution x) {P Q : ℕ} (hPQ : P ≤ Q) (hQ : Q ≤ x.cap)
    (a b : ℝ) (ha : x.left ≤ a) (hab : a ≤ b) (hb : b ≤ x.right)
    (φ : TorusHk Q ℝ) :
    truncateTorusHk hPQ (H.apply Q a b φ) =
      H.apply P a b (truncateTorusHk hPQ φ) := by
  obtain ⟨z, zw, hs, he⟩ := H.native Q hQ a b ha hab hb φ
  obtain ⟨y, yw, hy, hey⟩ := H.native P (hPQ.trans hQ) a b ha hab hb
    (truncateTorusHk hPQ φ)
  have hsub := (hd.restrict (Set.Icc_subset_Icc ha hb) hQ).reflected
  have huniq := (weak_scalar_torus_exists_unique hPQ hsub (neg_le_neg hab)
    (truncateTorusHk hPQ φ)).2
  rw [he, hey]
  exact huniq _ _ _ _ (weak_scalar_torus_solution_truncate hPQ hs) hy
    (-a) ⟨neg_le_neg hab, le_rfl⟩

/-- A chosen backward solution agrees with the propagator at every closed
subwindow endpoint. This permits the moving test in the actual Duhamel identity. -/
theorem weak_quiet_backward_values {plan : WeakPassagePlan}
    {prices : WeakQuietPathPrices} (x : WeakQuietExpansionCase plan prices)
    (hd : WeakScalarTorusDrift (x.c.D.κ x.c.M) x.radius x.left x.right
      (streamVel (x.c.D.Φ (x.i - 1))) x.cap)
    (H : WeakQuietBackwardEvolution x) {P : ℕ} (hP : P ≤ x.cap)
    {a b : ℝ} (ha : x.left ≤ a) (hb : b ≤ x.right)
    {φ : TorusHk P ℝ} {z : ℝ → TorusHk P ℝ} {zw : ℝ → TorusHk (P + 1) ℝ}
    (hz : WeakScalarTorusSolution (x.c.D.κ x.c.M) (-b) (-a)
      (fun t y => -streamVel (x.c.D.Φ (x.i - 1)) (-t) y) P φ z zw)
    (t : ℝ) (ht : t ∈ Set.Icc a b) : H.apply P t b φ = z (-t) := by
  obtain ⟨y, yw, hy, he⟩ := H.native P hP t b (ha.trans ht.1) ht.2 hb φ
  have hsub := (hd.restrict (Set.Icc_subset_Icc (ha.trans ht.1) hb) hP).reflected
  have huniq := (weak_scalar_torus_exists_unique (le_refl P) hsub
    (neg_le_neg ht.2) φ).2
  have hz' := CycleComparison.Error.isCoupledWeakSolutionTorus_restrict_left
    (neg_le_neg ht.1) hz
  rw [he]
  exact huniq _ _ _ _ hy hz' (-t) ⟨neg_le_neg ht.2, le_rfl⟩

/-- An absent physical edge gives the zero adjoint insertion even if its
chosen nonnegative b-majorant is positive. -/
theorem weak_quiet_insertion_zero_of_no_edge {plan : WeakPassagePlan}
    {prices : WeakQuietPathPrices} (x : WeakQuietExpansionCase plan prices)
    (S : WeakQuietInsertionData x) (v u : x.Vertex)
    (hnone : ¬ Nonempty ((x.c.stage x.i).fam.Γ v u))
    (P : ℕ) (hP : P + x.order ≤ x.cap) (t : ℝ)
    (ht : t ∈ Set.Icc x.left x.right) (φ : TorusHk (P + x.order) ℝ) :
    S.apply v u P hP t φ = 0 := by
  let : IsEmpty ((x.c.stage x.i).fam.Γ v u) := ⟨fun γ => hnone ⟨γ⟩⟩
  obtain ⟨C, Adj, heq, _⟩ := S.adjoint v u t ht
  rw [heq P hP]
  apply torusHk_eq_of_cellInner
  intro ψ hψ hp
  rw [Adj.ident P hP φ ψ (hψ.of_le (by simp)) hp, cellInner_tval_zero]
  have hz : x.source v u t ψ = fun _ => 0 := by
    funext y
    simp only [WeakQuietExpansionCase.source, Finset.univ_eq_empty, Finset.sum_empty,
      mul_zero]
  rw [hz]
  simp only [cellInner, inner_zero_right, integral_zero]

/-- A native homogeneous propagator sends zero to zero on each genuine
subwindow, by the order-`P` uniqueness theorem `weak_scalar_torus_exists_unique`. -/
theorem weak_quiet_backward_zero {plan : WeakPassagePlan}
    {prices : WeakQuietPathPrices} (x : WeakQuietExpansionCase plan prices)
    (hd : WeakScalarTorusDrift (x.c.D.κ x.c.M) x.radius x.left x.right
      (streamVel (x.c.D.Φ (x.i - 1))) x.cap)
    (H : WeakQuietBackwardEvolution x) (P : ℕ) (hP : P ≤ x.cap)
    (a b : ℝ) (ha : x.left ≤ a) (hab : a ≤ b) (hb : b ≤ x.right) :
    H.apply P a b 0 = 0 := by
  obtain ⟨z, zw, hs, he⟩ := H.native P hP a b ha hab hb 0
  have hsub := (hd.restrict (Set.Icc_subset_Icc ha hb) hP).reflected
  have huniq := (weak_scalar_torus_exists_unique le_rfl hsub (neg_le_neg hab)
    (0 : TorusHk P ℝ)).2
  rw [he]
  exact huniq z (fun _ => 0) zw (fun _ => 0) hs
    (Providers.WeakGen.Comparison.torusForcedRow_zero _ _ _ _ 2 P)
    (-a) ⟨neg_le_neg hab, le_rfl⟩

/-- Every iterated native adjoint path is zero on the zero test. This is an
identity of the actual Bochner integrands, with no integrability convention. -/
theorem weak_quiet_walk_dual_zero {plan : WeakPassagePlan}
    {prices : WeakQuietPathPrices} (x : WeakQuietExpansionCase plan prices)
    (hd : WeakScalarTorusDrift (x.c.D.κ x.c.M) x.radius x.left x.right
      (streamVel (x.c.D.Φ (x.i - 1))) x.cap)
    (S : WeakQuietInsertionData x) (H : WeakQuietBackwardEvolution x)
    (n : ℕ) (hn : n ≤ prices.depth x.R) (v u : x.Vertex)
    (π : WeakQuietWalk x.Vertex n v u) (a b : ℝ)
    (ha : x.left ≤ a) (hab : a ≤ b) (hb : b ≤ x.right) :
    weakQuietWalkDual x S H n hn v u π a b 0 = 0 := by
  induction n generalizing v a b with
  | zero =>
    change H.apply 0 a b (truncateTorusHk _ 0) = 0
    rw [map_zero]
    exact weak_quiet_backward_zero x hd H 0 (Nat.zero_le _) a b ha hab hb
  | succ n ih =>
    change (∫ t in a..b, weakQuietWalkDual x S H n _ π.1 u π.2 a t
      (S.apply v π.1 _ _ t (truncateTorusHk _ (H.apply _ t b 0)))) = 0
    calc
      _ = ∫ _t in a..b, (0 : TorusHk 0 ℝ) := by
        apply intervalIntegral.integral_congr_ae_restrict
        rw [Set.uIoc_of_le hab]
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        rw [weak_quiet_backward_zero x hd H _ (x.path_reserve (n + 1) hn)
          t b (ha.trans ht.1.le) ht.2 hb, map_zero, map_zero]
        exact ih (by omega) π.1 π.2 a t ha ht.1.le (ht.2.trans hb)
      _ = 0 := intervalIntegral.integral_zero

end AVRegularity.WeakEntryProofs.Assembly
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.WeakEntryProofs.Assembly

/-! The backward operators used by the actual quiet margin paths. Every operator
comes from the native reflected scalar equation, and the estimates reuse the
already proved positive and negative scalar smoothing theorems. -/

variable {plan : WeakPassagePlan} {prices : WeakQuietPathPrices}

/-- A simultaneous choice of backward scalar operators at all finite orders.
The zero extension outside actual subwindows is used only to give a total map. -/
def weakQuietBackwardOperator (x : WeakQuietExpansionCase plan prices)
    (hd : WeakScalarTorusDrift (x.c.D.κ x.c.M) x.radius x.left x.right
      (streamVel (x.c.D.Φ (x.i - 1))) x.cap)
    (P : ℕ) (a b : ℝ) : TorusHk P ℝ →L[ℝ] TorusHk P ℝ :=
  weakScalarTorusForward hd.reflected P (-b) (-a)

/-- The native backward family required by the scalar-path ingredient. -/
def weakQuietBackwardEvolution (x : WeakQuietExpansionCase plan prices)
    (hd : WeakScalarTorusDrift (x.c.D.κ x.c.M) x.radius x.left x.right
      (streamVel (x.c.D.Φ (x.i - 1))) x.cap) : WeakQuietBackwardEvolution x where
  apply P a b := weakQuietBackwardOperator x hd P a b
  native _P hP a b ha hab hb φ :=
    weak_scalar_torus_forward_native hd.reflected hP (-b) (-a)
      (neg_le_neg hb) (neg_le_neg hab) (neg_le_neg ha) φ

/-- Backward propagation costs at most sqrt(2) in every available factorial
reserve. This estimate is uniform in the quiet margin length and physical level. -/
theorem weak_quiet_backward_factorial_bound (x : WeakQuietExpansionCase plan prices)
    (hd : WeakScalarTorusDrift (x.c.D.κ x.c.M) x.radius x.left x.right
      (streamVel (x.c.D.Φ (x.i - 1))) x.cap)
    (H : WeakQuietBackwardEvolution x) (P : ℕ) (hP : P ≤ x.cap)
    (a b : ℝ) (ha : x.left ≤ a) (hab : a ≤ b) (hb : b ≤ x.right)
    (φ : TorusHk P ℝ) :
    Real.sqrt (factorialNormSq x.radius (H.apply P a b φ).val) ≤
      Real.sqrt 2 * Real.sqrt (factorialNormSq x.radius φ.val) := by
  obtain ⟨z, zw, hz, he⟩ := H.native P hP a b ha hab hb φ
  have hsub := (hd.restrict (Set.Icc_subset_Icc ha hb) le_rfl).reflected
  have hh := weak_scalar_torus_factorial_bound hP hsub hz
    (show -a ∈ Set.Icc (-b) (-a) from ⟨neg_le_neg hab, le_rfl⟩)
  rw [he]
  have hr := Real.sqrt_le_sqrt hh
  rwa [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at hr

/-- For a fixed terminal time the backward trajectory is continuous on the
whole closed subwindow, including its identity endpoint. -/
theorem weak_quiet_backward_continuous_left (x : WeakQuietExpansionCase plan prices)
    (hd : WeakScalarTorusDrift (x.c.D.κ x.c.M) x.radius x.left x.right
      (streamVel (x.c.D.Φ (x.i - 1))) x.cap)
    (H : WeakQuietBackwardEvolution x) (P : ℕ) (hP : P ≤ x.cap)
    (b : ℝ) (hb : b ∈ Set.Icc x.left x.right) (φ : TorusHk P ℝ) :
    ContinuousOn (fun a => H.apply P a b φ) (Set.Icc x.left b) := by
  obtain ⟨z, zw, hz, _⟩ := H.native P hP x.left b le_rfl hb.1 hb.2 φ
  have hc : ContinuousOn (fun a => z (-a)) (Set.Icc x.left b) :=
    (hz.1 0).comp continuous_neg.continuousOn
      (fun a ha => ⟨neg_le_neg ha.2, neg_le_neg ha.1⟩)
  apply hc.congr
  intro a ha
  exact weak_quiet_backward_values x hd H hP le_rfl hb.2 hz a ha

/-- In order zero, the native backward propagator is the Hilbert adjoint of
the actual forward propagator, on every closed quiet margin subwindow. -/
theorem weak_quiet_backward_forward_pair (x : WeakQuietExpansionCase plan prices)
    (hd : WeakScalarTorusDrift (x.c.D.κ x.c.M) x.radius x.left x.right
      (streamVel (x.c.D.Φ (x.i - 1))) x.cap)
    (H : WeakQuietBackwardEvolution x)
    (a b : ℝ) (ha : x.left ≤ a) (hab : a ≤ b) (hb : b ≤ x.right)
    (φ ψ : TorusHk 0 ℝ) :
    inner ℝ (H.apply 0 a b φ) ψ =
      inner ℝ φ (weakScalarTorusForward hd 0 a b ψ) := by
  obtain ⟨u, w, hu, he⟩ := weak_scalar_torus_forward_native hd (Nat.zero_le x.cap)
    a b ha hab hb ψ
  obtain ⟨z, zw, hz, hzH⟩ := H.native 0 (Nat.zero_le x.cap) a b ha hab hb φ
  have hp := weak_scalar_adjoint_pair 0 hab
    (hd.restrict (Set.Icc_subset_Icc ha hb) (Nat.zero_le x.cap)) hu hz
  have hinitu : u a = ψ := hu.2.2.2.1 0
  have hinitz : z (-b) = φ := hz.2.2.2.1 0
  have htr (y : TorusHk 0 ℝ) : truncateTorusHk (Nat.zero_le 0) y = y := rfl
  simp only [htr, hinitu, hinitz] at hp
  rw [hzH, he, real_inner_comm ψ (z (-a)), real_inner_comm (u b) φ]
  exact hp.symm

end AVRegularity.WeakEntryProofs.Assembly
end
end
end
