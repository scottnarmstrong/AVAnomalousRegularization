-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleComparison.CellInner
public import AVRegularity.Statements.Intermediate.CycleComparison.TensorFluxAdjoint
public import AVRegularity.Sobolev.Multiply.Carrier
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Coarse

/-! Calculus of coefficient derivative arrays.

For operator-valued coefficients `C : Vec 2 → E →L F`, the ordered derivative words and the array
norm `‖coefficientDerivativeArray C j x‖` are compared with: (i) the same quantities for
`x ↦ Φ (C x)` with `Φ` a fixed bounded linear map of operator spaces, (ii) the norm of the
iterated Fréchet derivative, (iii) constant coefficients. -/

/-- The Euclidean norm on `PiLp 2` is at most the sum of the component norms. -/
theorem norm_piLp_le_sum {ι : Type*} [Fintype ι] {β : ι → Type*}
    [∀ i, NormedAddCommGroup (β i)] [∀ i, NormedSpace ℝ (β i)] (v : PiLp 2 β) :
    ‖v‖ ≤ ∑ i, ‖v i‖ := by
  classical
  have h : v = ∑ i, PiLp.single 2 i (v i) := by
    ext j
    simp [Finset.sum_apply]
  conv_lhs => rw [h]
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
  simp [PiLp.norm_single]

section Arrays

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Each ordered derivative word is bounded by the array norm. -/
theorem norm_ordered_le_array (C : Vec 2 → E →L[ℝ] F) (j : ℕ) (w : DerivativeWord2 j) (x : Vec 2) :
    ‖orderedCoefficientDerivative C j w x‖ ≤ ‖coefficientDerivativeArray C j x‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg _) fun z => ?_
  calc ‖orderedCoefficientDerivative C j w x z‖
      = ‖coefficientDerivativeArray C j x z w‖ := rfl
    _ ≤ ‖coefficientDerivativeArray C j x z‖ := PiLp.norm_apply_le _ _
    _ ≤ _ := (coefficientDerivativeArray C j x).le_opNorm z

/-- The array norm is at most the sum of the norms of the ordered derivative words. -/
theorem norm_array_le_sum (C : Vec 2 → E →L[ℝ] F) (j : ℕ) (x : Vec 2) :
    ‖coefficientDerivativeArray C j x‖ ≤
      ∑ w : DerivativeWord2 j, ‖orderedCoefficientDerivative C j w x‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    fun z => ?_
  refine (norm_piLp_le_sum _).trans ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun w _ => (orderedCoefficientDerivative C j w x).le_opNorm z

theorem card_derivativeWord2 (j : ℕ) : Fintype.card (DerivativeWord2 j) = 2 ^ j := by
  simp [DerivativeWord2]

/-- Array norm against the maximal word norm. -/
theorem norm_array_le_card_mul (C : Vec 2 → E →L[ℝ] F) (j : ℕ) (x : Vec 2) {B : ℝ}
    (hB : ∀ w : DerivativeWord2 j, ‖orderedCoefficientDerivative C j w x‖ ≤ B) :
    ‖coefficientDerivativeArray C j x‖ ≤ 2 ^ j * B := by
  refine (norm_array_le_sum C j x).trans ?_
  refine (Finset.sum_le_sum fun w _ => hB w).trans ?_
  rw [Finset.sum_const, Finset.card_univ, card_derivativeWord2, nsmul_eq_mul]
  simp

/-- Ordered derivatives commute with a fixed bounded linear map of operator spaces. -/
theorem orderedCoefficientDerivative_clm_comp {E₂ F₂ : Type*} [NormedAddCommGroup E₂]
    [NormedSpace ℝ E₂] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    (Φ : (E →L[ℝ] F) →L[ℝ] (E₂ →L[ℝ] F₂)) (C : Vec 2 → E →L[ℝ] F) :
    ∀ (j : ℕ), ContDiff ℝ (j : ℕ) C → ∀ (w : DerivativeWord2 j) (x : Vec 2),
      orderedCoefficientDerivative (fun y => Φ (C y)) j w x =
        Φ (orderedCoefficientDerivative C j w x)
  | 0, _, _, _ => rfl
  | j + 1, hC, w, x => by
    have ih : orderedCoefficientDerivative (fun y => Φ (C y)) j (Fin.init w) =
        fun y => Φ (orderedCoefficientDerivative C j (Fin.init w) y) :=
      funext fun y => orderedCoefficientDerivative_clm_comp Φ C j
        (hC.of_le (by exact_mod_cast Nat.le_succ j)) (Fin.init w) y
    have hd : DifferentiableAt ℝ (orderedCoefficientDerivative C j (Fin.init w)) x :=
      (orderedCoefficientDerivative_contDiff C j 1 (by simpa using hC) (Fin.init w)).differentiable
        (by simp) x
    change fderiv ℝ (orderedCoefficientDerivative (fun y => Φ (C y)) j (Fin.init w)) x
        (basisVec (w (Fin.last j))) =
      Φ (fderiv ℝ (orderedCoefficientDerivative C j (Fin.init w)) x (basisVec (w (Fin.last j))))
    have hf : HasFDerivAt (fun y => Φ (orderedCoefficientDerivative C j (Fin.init w) y))
        (Φ.comp (fderiv ℝ (orderedCoefficientDerivative C j (Fin.init w)) x)) x :=
      Φ.hasFDerivAt.comp x hd.hasFDerivAt
    rw [ih, hf.fderiv]
    rfl

/-- Array norm of a bounded linear image of a coefficient. -/
theorem norm_array_clm_comp_le {E₂ F₂ : Type*} [NormedAddCommGroup E₂]
    [NormedSpace ℝ E₂] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    (Φ : (E →L[ℝ] F) →L[ℝ] (E₂ →L[ℝ] F₂)) (C : Vec 2 → E →L[ℝ] F) (j : ℕ)
    (hC : ContDiff ℝ (j : ℕ) C) (x : Vec 2) :
    ‖coefficientDerivativeArray (fun y => Φ (C y)) j x‖ ≤
      2 ^ j * (‖Φ‖ * ‖coefficientDerivativeArray C j x‖) := by
  refine norm_array_le_card_mul _ j x fun w => ?_
  rw [orderedCoefficientDerivative_clm_comp Φ C j hC w x]
  exact (Φ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_ordered_le_array C j w x)
    (norm_nonneg _))

/-- Higher derivatives of a constant coefficient vanish. -/
theorem orderedCoefficientDerivative_const_succ (L : E →L[ℝ] F) :
    ∀ (j : ℕ) (w : DerivativeWord2 (j + 1)) (x : Vec 2),
      orderedCoefficientDerivative (fun _ => L) (j + 1) w x = 0
  | 0, w, x => by
    change fderiv ℝ (fun _ : Vec 2 => L) x _ = 0
    simp
  | j + 1, w, x => by
    have ih : orderedCoefficientDerivative (fun _ : Vec 2 => L) (j + 1) (Fin.init w) =
        fun _ => 0 := funext fun y => orderedCoefficientDerivative_const_succ L j _ y
    change fderiv ℝ (orderedCoefficientDerivative (fun _ : Vec 2 => L) (j + 1) (Fin.init w)) x _ = 0
    rw [ih]
    simp

theorem coefficientDerivativeArray_const_succ (L : E →L[ℝ] F) (j : ℕ) (x : Vec 2) :
    coefficientDerivativeArray (fun _ => L) (j + 1) x = 0 := by
  ext z w
  simp [orderedCoefficientDerivative_const_succ]

/-- Ordered derivative words are values of the iterated Fréchet derivative on basis vectors. -/
theorem orderedCoefficientDerivative_eq_iteratedFDeriv (C : Vec 2 → E →L[ℝ] F) :
    ∀ (j : ℕ), ContDiff ℝ (j : ℕ) C → ∀ (w : DerivativeWord2 j) (x : Vec 2),
      orderedCoefficientDerivative C j w x =
        iteratedFDeriv ℝ j C x (fun i => basisVec (w (Fin.rev i)))
  | 0, _, w, x => by
    ext z
    simp [iteratedFDeriv_zero_apply]
  | j + 1, hC, w, x => by
    have ih : orderedCoefficientDerivative C j (Fin.init w) =
        fun y => iteratedFDeriv ℝ j C y (fun i => basisVec (Fin.init w (Fin.rev i))) :=
      funext fun y => orderedCoefficientDerivative_eq_iteratedFDeriv C j
        (hC.of_le (by exact_mod_cast Nat.le_succ j)) (Fin.init w) y
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ j C) x :=
      (hC.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self j)) x
    change fderiv ℝ (orderedCoefficientDerivative C j (Fin.init w)) x
        (basisVec (w (Fin.last j))) = _
    rw [ih, fderiv_continuousMultilinear_apply_const_apply hd,
      iteratedFDeriv_succ_apply_left]
    congr 1
    funext k
    simp [Fin.tail, Fin.init, Fin.rev_succ]

theorem norm_basisVec_le_one (i : Fin 2) : ‖basisVec i‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun k => ?_
  by_cases h : k = i <;> simp [h]

/-- Ordered derivative words are bounded by the norm of the iterated derivative. -/
theorem norm_ordered_le_iteratedFDeriv (C : Vec 2 → E →L[ℝ] F) (j : ℕ)
    (hC : ContDiff ℝ (j : ℕ) C) (w : DerivativeWord2 j) (x : Vec 2) :
    ‖orderedCoefficientDerivative C j w x‖ ≤ ‖iteratedFDeriv ℝ j C x‖ := by
  rw [orderedCoefficientDerivative_eq_iteratedFDeriv C j hC w x]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  have : ∏ i, ‖basisVec (w (Fin.rev i))‖ ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => norm_basisVec_le_one _
  calc _ ≤ ‖iteratedFDeriv ℝ j C x‖ * 1 :=
        mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = _ := mul_one _

/-- Array norm against the norm of the iterated derivative. -/
theorem norm_array_le_iteratedFDeriv (C : Vec 2 → E →L[ℝ] F) (j : ℕ)
    (hC : ContDiff ℝ (j : ℕ) C) (x : Vec 2) :
    ‖coefficientDerivativeArray C j x‖ ≤ 2 ^ j * ‖iteratedFDeriv ℝ j C x‖ :=
  norm_array_le_card_mul C j x fun w => norm_ordered_le_iteratedFDeriv C j hC w x

end Arrays

end AVRegularity.CycleComparison.Coarse
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Coarse

/-! Formal adjoints of differential operators on periodic Sobolev fields.

A `TorusAdj T m R Kc C` packages, for an operator `T` acting on test fields `ψ : Vec 2 → F` (of
order `m`), bounded maps `adj K : TorusHk (K + m) E →L TorusHk K F` for `K + m ≤ Kc` with norm
at most `C`, such that the value of `adj K U` pairs with every `C^m` periodic test field `ψ` as
`U` pairs with `T ψ`. The operator also maps `C^{r+m}` periodic fields to `C^r` periodic fields
for `r ≤ R`, which makes adjoints compose. The coarse response fluxes are the adjoints of the
operators `coarseFluxAdjoint ∘ covPolyQ` and `covPolyP ∘ edgeFluxAdjoint ∘ covPolyQ`. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

/-- The value (order-zero jet) of a periodic Sobolev field. -/
def tval {K : ℕ} (U : TorusHk K E) : Vec 2 → E := U.toFunction.jet (valueIndex2 K)

/-- A formal adjoint on periodic Sobolev fields, of order `m`, mapping regularity through `R`,
defined on Sobolev orders `K + m ≤ Kc`, with operator norm at most `C`. -/
structure TorusAdj (T : (Vec 2 → F) → (Vec 2 → E)) (m R Kc : ℕ) (C : ℝ) where
  /-- The adjoint maps. -/
  adj : ∀ K, K + m ≤ Kc → TorusHk (K + m) E →L[ℝ] TorusHk K F
  /-- Uniform operator bound. -/
  bound : ∀ K (hK : K + m ≤ Kc), ‖adj K hK‖ ≤ C
  /-- Regularity of the operator on periodic test fields. -/
  maps : ∀ r, r ≤ R → ∀ ψ : Vec 2 → F, ContDiff ℝ ((r + m : ℕ) : ℕ∞) ψ →
    AVenhance.IsZ2Periodic ψ → ContDiff ℝ (r : ℕ∞) (T ψ) ∧ AVenhance.IsZ2Periodic (T ψ)
  /-- The adjoint identity. -/
  ident : ∀ K (hK : K + m ≤ Kc) (U : TorusHk (K + m) E) (ψ : Vec 2 → F),
    ContDiff ℝ (m : ℕ∞) ψ → AVenhance.IsZ2Periodic ψ →
    cellInner (tval (adj K hK U)) ψ = cellInner (tval U) (T ψ)
end

/-! Order casts, value jets and cell integrability for the adjoint calculus.

`torusCast` identifies `TorusHk K E` with `TorusHk L E` along `K = L`; it leaves the value jet
unchanged. The value jet `tval` is determined almost everywhere on the cell by the Hilbert class,
and pairs integrably with every continuous field. -/

section
variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] [NormedAddCommGroup G]
  [InnerProductSpace ℝ G] [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]

/-- Transport along an equality of Sobolev orders. -/
def torusCast {K L : ℕ} (h : K = L) : TorusHk K E →L[ℝ] TorusHk L E := by
  subst h
  exact ContinuousLinearMap.id ℝ _

/-- Scalar multiplication as a bounded linear map (avoids a costly instance search). -/
def torusSmulCLM {K : ℕ} (c : ℝ) : TorusHk K E →L[ℝ] TorusHk K E :=
  LinearMap.mkContinuous
    { toFun := fun U => c • U
      map_add' := fun U V => smul_add c U V
      map_smul' := fun a U => (smul_comm a c U).symm } |c|
    (fun U => by
      change ‖c • U‖ ≤ |c| * ‖U‖
      rw [norm_smul, Real.norm_eq_abs])

theorem torusSmulCLM_apply {K : ℕ} (c : ℝ) (U : TorusHk K E) : torusSmulCLM c U = c • U := rfl

theorem norm_torusSmulCLM_le {K : ℕ} (c : ℝ) :
    ‖(torusSmulCLM c : TorusHk K E →L[ℝ] _)‖ ≤ |c| :=
  LinearMap.mkContinuous_norm_le _ (abs_nonneg c) _

/-- The cast does not change the value jet. -/
theorem tval_torusCast {K L : ℕ} (h : K = L) (U : TorusHk K E) :
    tval (torusCast h U) = tval U := by
  subst h
  rfl

/-- The cast is isometric. -/
theorem norm_torusCast {K L : ℕ} (h : K = L) (U : TorusHk K E) :
    ‖torusCast h U‖ = ‖U‖ := by
  subst h
  rfl

/-- The cast is a contraction. -/
theorem norm_torusCast_le {K L : ℕ} (h : K = L) : ‖(torusCast h : TorusHk K E →L[ℝ] _)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun U => by
    rw [norm_torusCast, one_mul])

/-- The value jet agrees on the cell with the value component of the Hilbert class. -/
theorem tval_ae {K : ℕ} (U : TorusHk K E) :
    tval U =ᵐ[volume.restrict AVenhance.unitCube]
      ((U.val (valueIndex2 K) : ComponentL2 (volume.restrict AVenhance.unitCube) E) :
        Vec 2 → E) :=
  periodicJetRepresentative_ae U.val (valueIndex2 K)

/-- The value jet is square integrable on the cell. -/
theorem memLp_tval {K : ℕ} (U : TorusHk K E) :
    MemLp (tval U) 2 (volume.restrict AVenhance.unitCube) :=
  U.toFunction.hasPeriodicWeakJet.2.1 (valueIndex2 K)

/-- Truncation does not change the value jet. -/
theorem tval_truncateTorusHk {K L : ℕ} (hKL : K ≤ L) (U : TorusHk L E) :
    tval (truncateTorusHk hKL U) = tval U := by
  have hidx : truncateJetIndex hKL (valueIndex2 K) = valueIndex2 L := by
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      funext z
      exact Fin.elim0 z
  change periodicJetRepresentative (truncateTorusHk hKL U).val (valueIndex2 K) =
    periodicJetRepresentative U.val (valueIndex2 L)
  rw [← hidx]
  rfl

theorem unitCube_subset_closedBall : AVenhance.unitCube ⊆ Metric.closedBall (0 : Vec 2) 1 := by
  intro x hx
  rw [mem_closedBall_zero_iff]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  have hi : 0 < x i ∧ x i < 1 := hx i (Set.mem_univ i)
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [hi.1, hi.2]

theorem measurableSet_unitCube' : MeasurableSet AVenhance.unitCube := by
  simpa [AVenhance.unitCube, Set.pi] using
    (MeasurableSet.univ_pi' (fun _ : Fin 2 =>
      (measurableSet_Ioo : MeasurableSet (Set.Ioo (0 : ℝ) 1))))

instance isFiniteMeasure_cell : IsFiniteMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_lt (measure_mono unitCube_subset_closedBall)
      (isCompact_closedBall _ _).measure_lt_top⟩

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
/-- Square integrable fields pair integrably with continuous fields on the cell. -/
theorem integrable_inner_continuous {u g : Vec 2 → E}
    (hu : MemLp u 2 (volume.restrict AVenhance.unitCube)) (hg : Continuous g) :
    Integrable (fun x => inner ℝ (u x) (g x)) (volume.restrict AVenhance.unitCube) := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Vec 2) 1).exists_bound_of_continuousOn
    hg.continuousOn
  have hint : Integrable (fun x => ‖u x‖) (volume.restrict AVenhance.unitCube) :=
    (hu.integrable one_le_two).norm
  refine Integrable.mono' (hint.const_mul M)
    (hu.aestronglyMeasurable.inner hg.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_unitCube'] with x hx
  calc ‖inner ℝ (u x) (g x)‖ ≤ ‖u x‖ * ‖g x‖ := norm_inner_le_norm _ _
    _ ≤ ‖u x‖ * M := mul_le_mul_of_nonneg_left (hM x (unitCube_subset_closedBall hx))
        (norm_nonneg _)
    _ = M * ‖u x‖ := mul_comm _ _

/-- The cell pairing of a value jet with a continuous field is integrable. -/
theorem integrable_tval_inner {K : ℕ} (U : TorusHk K E) {g : Vec 2 → E} (hg : Continuous g) :
    Integrable (fun x => inner ℝ (tval U x) (g x)) (volume.restrict AVenhance.unitCube) :=
  integrable_inner_continuous (memLp_tval U) hg
end

/-! Linearity of the cell pairing `cellInner (tval U) ψ` in the Sobolev field `U` and in the
test field `ψ`. Pairings with value jets are only defined up to null sets, so linearity in `U`
is an almost-everywhere statement; linearity in `ψ` needs integrability, which continuity gives. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
/-- Almost-everywhere equal first arguments give equal cell pairings. -/
theorem cellInner_congr_left {g g' : Vec 2 → E}
    (h : g =ᵐ[volume.restrict AVenhance.unitCube] g') (ψ : Vec 2 → E) :
    cellInner g ψ = cellInner g' ψ := by
  unfold cellInner
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

theorem tval_add_ae {K : ℕ} (U V : TorusHk K E) :
    tval (U + V) =ᵐ[volume.restrict AVenhance.unitCube] fun x => tval U x + tval V x := by
  filter_upwards [tval_ae (U + V), tval_ae U, tval_ae V,
    Lp.coeFn_add (U.val (valueIndex2 K)) (V.val (valueIndex2 K))] with x h1 h2 h3 h4
  rw [h1]
  exact h4.trans (by rw [Pi.add_apply, h2, h3])

theorem tval_neg_ae {K : ℕ} (U : TorusHk K E) :
    tval (-U) =ᵐ[volume.restrict AVenhance.unitCube] fun x => -tval U x := by
  filter_upwards [tval_ae (-U), tval_ae U, Lp.coeFn_neg (U.val (valueIndex2 K))] with x h1 h2 h3
  rw [h1]
  exact h3.trans (by rw [Pi.neg_apply, h2])

theorem tval_smul_ae {K : ℕ} (c : ℝ) (U : TorusHk K E) :
    tval (c • U) =ᵐ[volume.restrict AVenhance.unitCube] fun x => c • tval U x := by
  filter_upwards [tval_ae (c • U), tval_ae U, Lp.coeFn_smul c (U.val (valueIndex2 K))] with
    x h1 h2 h3
  rw [h1]
  exact h3.trans (by rw [Pi.smul_apply, h2])

theorem tval_zero_ae {K : ℕ} :
    tval (0 : TorusHk K E) =ᵐ[volume.restrict AVenhance.unitCube] fun _ => 0 := by
  filter_upwards [tval_ae (0 : TorusHk K E), Lp.coeFn_zero E 2 (volume.restrict AVenhance.unitCube)]
    with x h1 h2
  rw [h1]
  exact h2

/-- The pairing of the zero field vanishes. -/
theorem cellInner_tval_zero {K : ℕ} (ψ : Vec 2 → E) :
    cellInner (tval (0 : TorusHk K E)) ψ = 0 := by
  rw [cellInner_congr_left tval_zero_ae]
  simp [cellInner]

theorem cellInner_tval_add {K : ℕ} (U V : TorusHk K E) {ψ : Vec 2 → E} (hψ : Continuous ψ) :
    cellInner (tval (U + V)) ψ = cellInner (tval U) ψ + cellInner (tval V) ψ := by
  rw [cellInner_congr_left (tval_add_ae U V)]
  unfold cellInner
  simp_rw [inner_add_left]
  exact integral_add (integrable_tval_inner U hψ) (integrable_tval_inner V hψ)

theorem cellInner_tval_neg {K : ℕ} (U : TorusHk K E) (ψ : Vec 2 → E) :
    cellInner (tval (-U)) ψ = -cellInner (tval U) ψ := by
  rw [cellInner_congr_left (tval_neg_ae U)]
  unfold cellInner
  simp_rw [inner_neg_left]
  exact integral_neg _

theorem cellInner_tval_smul {K : ℕ} (c : ℝ) (U : TorusHk K E) (ψ : Vec 2 → E) :
    cellInner (tval (c • U)) ψ = c * cellInner (tval U) ψ := by
  rw [cellInner_congr_left (tval_smul_ae c U)]
  unfold cellInner
  simp_rw [real_inner_smul_left]
  exact integral_const_mul _ _

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem cellInner_add_right (g : Vec 2 → E) {ψ₁ ψ₂ : Vec 2 → E}
    (h₁ : Integrable (fun x => inner ℝ (g x) (ψ₁ x)) (volume.restrict AVenhance.unitCube))
    (h₂ : Integrable (fun x => inner ℝ (g x) (ψ₂ x)) (volume.restrict AVenhance.unitCube)) :
    cellInner g (fun x => ψ₁ x + ψ₂ x) = cellInner g ψ₁ + cellInner g ψ₂ := by
  unfold cellInner
  simp_rw [inner_add_right]
  exact integral_add h₁ h₂

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem cellInner_neg_right (g ψ : Vec 2 → E) :
    cellInner g (fun x => -ψ x) = -cellInner g ψ := by
  unfold cellInner
  simp_rw [inner_neg_right]
  exact integral_neg _

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem cellInner_smul_right (c : ℝ) (g ψ : Vec 2 → E) :
    cellInner g (fun x => c • ψ x) = c * cellInner g ψ := by
  unfold cellInner
  simp_rw [real_inner_smul_right]
  exact integral_const_mul _ _
end

end AVRegularity.CycleComparison.Coarse
end
end
end

section
@[expose] public noncomputable section

section
open AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Coarse

/-! Algebra of the diagonal tensor flux `A ⊗ id`.

For `B : ℝ^{words m} →L ℝ²`, `tensorFluxAdjoint B` and its pointwise adjoint `tensorPrimal B`
(the map `φ ↦ (k ↦ ∑_α B_{kα} φ_α)`) are bounded linear maps with norm at most `2^{m+1} ‖B‖`,
depending boundedly and linearly on `B`; they are packaged as bounded linear maps of `B`. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}

/-- The word-array coefficient `B_{kα} = (B e_α)_k`. -/
def tcoef (B : PiLp 2 (fun _ : DerivativeWord2 m => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (k : Fin 2) (α : DerivativeWord2 m) : ℝ :=
  B (WithLp.toLp 2 (Pi.single α (1 : ℝ))) k

theorem abs_tcoef_le (B : PiLp 2 (fun _ : DerivativeWord2 m => ℝ) →L[ℝ]
    PiLp 2 (fun _ : Fin 2 => ℝ)) (k : Fin 2) (α : DerivativeWord2 m) : |tcoef B k α| ≤ ‖B‖ := by
  have h1 : ‖(WithLp.toLp 2 (Pi.single α (1 : ℝ)) :
      PiLp 2 (fun _ : DerivativeWord2 m => ℝ))‖ = 1 := by
    simp
  calc |tcoef B k α| = ‖B (WithLp.toLp 2 (Pi.single α (1 : ℝ))) k‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖B (WithLp.toLp 2 (Pi.single α (1 : ℝ)))‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖B‖ * ‖(WithLp.toLp 2 (Pi.single α (1 : ℝ)) :
        PiLp 2 (fun _ : DerivativeWord2 m => ℝ))‖ := B.le_opNorm _
    _ = ‖B‖ := by rw [h1, mul_one]

theorem tcoef_add (B B' : PiLp 2 (fun _ : DerivativeWord2 m => ℝ) →L[ℝ]
    PiLp 2 (fun _ : Fin 2 => ℝ)) (k : Fin 2) (α : DerivativeWord2 m) :
    tcoef (B + B') k α = tcoef B k α + tcoef B' k α := rfl

theorem tcoef_smul (c : ℝ) (B : PiLp 2 (fun _ : DerivativeWord2 m => ℝ) →L[ℝ]
    PiLp 2 (fun _ : Fin 2 => ℝ)) (k : Fin 2) (α : DerivativeWord2 m) :
    tcoef (c • B) k α = c * tcoef B k α := rfl

/-- The pointwise adjoint `(A ⊗ id)` of `tensorFluxAdjoint`. -/
def tensorPrimal (B : PiLp 2 (fun _ : DerivativeWord2 m => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (φ : PiLp 2 (fun _ : DerivativeWord2 m => E)) : PiLp 2 (fun _ : Fin 2 => E) :=
  WithLp.toLp 2 fun k => ∑ α, tcoef B k α • φ α

theorem tensorFluxAdjoint_apply (B : PiLp 2 (fun _ : DerivativeWord2 m => ℝ) →L[ℝ]
    PiLp 2 (fun _ : Fin 2 => ℝ)) (ψ : PiLp 2 (fun _ : Fin 2 => E)) (α : DerivativeWord2 m) :
    AVRegularity.tensorFluxAdjoint B ψ α = ∑ k, tcoef B k α • ψ k := rfl

theorem norm_tensorFluxAdjoint_le (B : PiLp 2 (fun _ : DerivativeWord2 m => ℝ) →L[ℝ]
    PiLp 2 (fun _ : Fin 2 => ℝ)) (ψ : PiLp 2 (fun _ : Fin 2 => E)) :
    ‖AVRegularity.tensorFluxAdjoint B ψ‖ ≤ (2 ^ m * 2) * ‖B‖ * ‖ψ‖ := by
  refine (norm_piLp_le_sum _).trans ?_
  have hα : ∀ α : DerivativeWord2 m, ‖AVRegularity.tensorFluxAdjoint B ψ α‖ ≤ 2 * ‖B‖ * ‖ψ‖ := by
    intro α
    rw [tensorFluxAdjoint_apply]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k, ‖tcoef B k α • ψ k‖ ≤ ∑ _k : Fin 2, ‖B‖ * ‖ψ‖ := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul (abs_tcoef_le B k α) (PiLp.norm_apply_le ψ k) (norm_nonneg _)
            (norm_nonneg _)
      _ = 2 * ‖B‖ * ‖ψ‖ := by simp [Finset.sum_const]; ring
  calc ∑ α, ‖AVRegularity.tensorFluxAdjoint B ψ α‖ ≤ ∑ _α : DerivativeWord2 m, 2 * ‖B‖ * ‖ψ‖ :=
        Finset.sum_le_sum fun α _ => hα α
    _ = (2 ^ m * 2) * ‖B‖ * ‖ψ‖ := by
        rw [Finset.sum_const, Finset.card_univ, card_derivativeWord2, nsmul_eq_mul]
        push_cast; ring

theorem norm_tensorPrimal_le (B : PiLp 2 (fun _ : DerivativeWord2 m => ℝ) →L[ℝ]
    PiLp 2 (fun _ : Fin 2 => ℝ)) (φ : PiLp 2 (fun _ : DerivativeWord2 m => E)) :
    ‖tensorPrimal B φ‖ ≤ (2 ^ m * 2) * ‖B‖ * ‖φ‖ := by
  refine (norm_piLp_le_sum _).trans ?_
  have hk : ∀ k : Fin 2, ‖tensorPrimal B φ k‖ ≤ 2 ^ m * ‖B‖ * ‖φ‖ := by
    intro k
    change ‖∑ α, tcoef B k α • φ α‖ ≤ _
    refine (norm_sum_le _ _).trans ?_
    calc ∑ α, ‖tcoef B k α • φ α‖ ≤ ∑ _α : DerivativeWord2 m, ‖B‖ * ‖φ‖ := by
          refine Finset.sum_le_sum fun α _ => ?_
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul (abs_tcoef_le B k α) (PiLp.norm_apply_le φ α) (norm_nonneg _)
            (norm_nonneg _)
      _ = 2 ^ m * ‖B‖ * ‖φ‖ := by
          rw [Finset.sum_const, Finset.card_univ, card_derivativeWord2, nsmul_eq_mul]
          push_cast; ring
  calc ∑ k, ‖tensorPrimal B φ k‖ ≤ ∑ _k : Fin 2, 2 ^ m * ‖B‖ * ‖φ‖ :=
        Finset.sum_le_sum fun k _ => hk k
    _ = (2 ^ m * 2) * ‖B‖ * ‖φ‖ := by simp [Finset.sum_const]; ring

/-- `tensorFluxAdjoint B` as a bounded linear map. -/
def tensorFluxAdjointCLM (B : PiLp 2 (fun _ : DerivativeWord2 m => ℝ) →L[ℝ]
    PiLp 2 (fun _ : Fin 2 => ℝ)) :
    PiLp 2 (fun _ : Fin 2 => E) →L[ℝ] PiLp 2 (fun _ : DerivativeWord2 m => E) :=
  LinearMap.mkContinuous
    { toFun := AVRegularity.tensorFluxAdjoint B
      map_add' := fun ψ ψ' => by
        ext α
        simp [tensorFluxAdjoint_apply, smul_add, Finset.sum_add_distrib]
      map_smul' := fun c ψ => by
        ext α
        simp [tensorFluxAdjoint_apply, smul_comm c] } ((2 ^ m * 2) * ‖B‖)
    (fun ψ => norm_tensorFluxAdjoint_le B ψ)

/-- `tensorPrimal B` as a bounded linear map. -/
def tensorPrimalCLM (B : PiLp 2 (fun _ : DerivativeWord2 m => ℝ) →L[ℝ]
    PiLp 2 (fun _ : Fin 2 => ℝ)) :
    PiLp 2 (fun _ : DerivativeWord2 m => E) →L[ℝ] PiLp 2 (fun _ : Fin 2 => E) :=
  LinearMap.mkContinuous
    { toFun := tensorPrimal B
      map_add' := fun φ φ' => by
        ext k
        simp [tensorPrimal, smul_add, Finset.sum_add_distrib]
      map_smul' := fun c φ => by
        ext k
        simp [tensorPrimal, Finset.smul_sum, smul_comm c] } ((2 ^ m * 2) * ‖B‖)
    (fun φ => norm_tensorPrimal_le B φ)

/-- `B ↦ tensorFluxAdjoint B` as a bounded linear map, of norm at most `2^m * 2`. -/
def tensorFluxAdjointMap (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (m : ℕ) :
    (PiLp 2 (fun _ : DerivativeWord2 m => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)) →L[ℝ]
      (PiLp 2 (fun _ : Fin 2 => E) →L[ℝ] PiLp 2 (fun _ : DerivativeWord2 m => E)) :=
  LinearMap.mkContinuous
    { toFun := tensorFluxAdjointCLM
      map_add' := fun B B' => by
        ext ψ α
        simp [tensorFluxAdjointCLM, tensorFluxAdjoint_apply, tcoef_add, add_smul,
          Finset.sum_add_distrib]
      map_smul' := fun c B => by
        ext ψ α
        simp [tensorFluxAdjointCLM, tensorFluxAdjoint_apply, tcoef_smul, mul_smul] } (2 ^ m * 2)
    (fun B => by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun ψ => ?_
      exact norm_tensorFluxAdjoint_le B ψ |>.trans (le_of_eq (by ring)))

/-- `B ↦ tensorPrimal B` as a bounded linear map, of norm at most `2^m * 2`. -/
def tensorPrimalMap (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (m : ℕ) :
    (PiLp 2 (fun _ : DerivativeWord2 m => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)) →L[ℝ]
      (PiLp 2 (fun _ : DerivativeWord2 m => E) →L[ℝ] PiLp 2 (fun _ : Fin 2 => E)) :=
  LinearMap.mkContinuous
    { toFun := tensorPrimalCLM
      map_add' := fun B B' => by
        ext φ k
        simp [tensorPrimalCLM, tensorPrimal, tcoef_add, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c B => by
        ext φ k
        simp [tensorPrimalCLM, tensorPrimal, tcoef_smul, mul_smul, Finset.smul_sum] }
    (2 ^ m * 2)
    (fun B => by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun φ => ?_
      exact norm_tensorPrimal_le B φ |>.trans (le_of_eq (by ring)))

theorem norm_tensorPrimalMap_le :
    ‖tensorPrimalMap E m‖ ≤ 2 ^ m * 2 :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

end AVRegularity.CycleComparison.Coarse
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Coarse

/-! Closure properties of `TorusAdj`: reindexing, monotonicity, constants, linear combinations
and composition (`adj (T₁ ∘ T₂) = adj T₂ ∘ adj T₁`, with the Sobolev index shift `K + (m₁ + m₂)`
identified with `(K + m₂) + m₁` by `torusCast`). -/

section
variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] [NormedAddCommGroup G]
  [InnerProductSpace ℝ G] [MeasurableSpace G] [BorelSpace G] [CompleteSpace G]

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]
  [InnerProductSpace ℝ G] [MeasurableSpace G] [BorelSpace G] [CompleteSpace G] in
theorem opNorm_finsetSum_le' {X Y ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (s : Finset ι) (f : ι → X →L[ℝ] Y) :
    ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := norm_sum_le _ _

namespace TorusAdj

variable {T T' : (Vec 2 → F) → (Vec 2 → E)} {m m' R R' Kc Kc' : ℕ} {C C' : ℝ}

/-- Transport along an equality of operators. -/
def ofOp (h : T = T') (A : TorusAdj T m R Kc C) : TorusAdj T' m R Kc C := by
  subst h
  exact A

/-- Transport along an equality of orders. -/
def ofOrder (h : m = m') (A : TorusAdj T m R Kc C) : TorusAdj T m' R Kc C := by
  subst h
  exact A

/-- The operator maps a `C^m` periodic field to a continuous field. -/
theorem continuous_apply (A : TorusAdj T m R Kc C) {ψ : Vec 2 → F}
    (hψ : ContDiff ℝ (m : ℕ∞) ψ) (hp : AVenhance.IsZ2Periodic ψ) : Continuous (T ψ) :=
  (A.maps 0 (Nat.zero_le _) ψ (by simpa using hψ) hp).1.continuous

/-- Smaller regularity and Sobolev range, and a larger constant, remain admissible. -/
def mono (A : TorusAdj T m R Kc C) (hR : R' ≤ R) (hKc : Kc' ≤ Kc) (hC : C ≤ C') :
    TorusAdj T m R' Kc' C' where
  adj K hK := A.adj K (hK.trans hKc)
  bound K hK := (A.bound K (hK.trans hKc)).trans hC
  maps r hr := A.maps r (hr.trans hR)
  ident K hK := A.ident K (hK.trans hKc)

/-- A larger order is admissible, by truncating the Sobolev field. -/
def liftOrder (A : TorusAdj T m R Kc C) (hm : m ≤ m') : TorusAdj T m' R Kc C where
  adj K hK := (A.adj K (by omega)).comp
    (truncateTorusHk (Nat.add_le_add_left hm K))
  bound K hK := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h1 : ‖(truncateTorusHk (E := E) (Nat.add_le_add_left hm K))‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one
        (fun f => by simpa using truncateTorusHk_norm_le _ f)
    have h2 := A.bound K (by omega)
    calc _ ≤ C * 1 :=
          mul_le_mul h2 h1 (ContinuousLinearMap.opNorm_nonneg _)
            ((ContinuousLinearMap.opNorm_nonneg _).trans h2)
      _ = C := mul_one C
  maps r hr ψ hψ hp :=
    A.maps r hr ψ (hψ.of_le (by exact_mod_cast Nat.add_le_add_left hm r)) hp
  ident K hK U ψ hψ hp := by
    change cellInner (tval (A.adj K _ (truncateTorusHk _ U))) ψ = _
    rw [A.ident K _ _ ψ (hψ.of_le (by exact_mod_cast hm)) hp, tval_truncateTorusHk]

end TorusAdj

section Constants

/-- The zero operator. -/
def TorusAdj.zero (m R Kc : ℕ) :
    TorusAdj (fun _ : Vec 2 → F => (fun _ => 0 : Vec 2 → E)) m R Kc 0 where
  adj K _ := 0
  bound K _ := (ContinuousLinearMap.opNorm_zero (𝕜 := ℝ)).le
  maps r _ ψ _ _ := ⟨contDiff_const, fun _ _ => rfl⟩
  ident K _ U ψ _ _ := by
    change cellInner (tval (0 : TorusHk K F)) ψ = _
    rw [cellInner_tval_zero]
    simp [cellInner]

/-- The identity operator, of order zero. -/
def TorusAdj.id (R Kc : ℕ) : TorusAdj (fun ψ : Vec 2 → E => ψ) 0 R Kc 1 where
  adj K _ := ContinuousLinearMap.id ℝ _
  bound K _ := ContinuousLinearMap.norm_id_le
  maps r _ ψ h hp := ⟨by simpa using h, hp⟩
  ident K _ U ψ _ _ := rfl

end Constants

namespace TorusAdj

variable {T T₁ T₂ : (Vec 2 → F) → (Vec 2 → E)} {m R Kc : ℕ} {C C₁ C₂ : ℝ}

/-- Sum of two operators of the same order. -/
def add (A₁ : TorusAdj T₁ m R Kc C₁) (A₂ : TorusAdj T₂ m R Kc C₂) :
    TorusAdj (fun ψ => T₁ ψ + T₂ ψ) m R Kc (C₁ + C₂) where
  adj K hK := A₁.adj K hK + A₂.adj K hK
  bound K hK := (ContinuousLinearMap.opNorm_add_le _ _).trans (add_le_add (A₁.bound K hK) (A₂.bound K hK))
  maps r hr ψ hψ hp := by
    obtain ⟨h1, p1⟩ := A₁.maps r hr ψ hψ hp
    obtain ⟨h2, p2⟩ := A₂.maps r hr ψ hψ hp
    exact ⟨h1.add h2, fun n x => by
      simp only [Pi.add_apply, p1 n x, p2 n x]⟩
  ident K hK U ψ hψ hp := by
    change cellInner (tval (A₁.adj K hK U + A₂.adj K hK U)) ψ = _
    have hc : Continuous ψ := hψ.continuous
    rw [cellInner_tval_add _ _ (hψ.continuous), A₁.ident K hK U ψ hψ hp,
      A₂.ident K hK U ψ hψ hp,
      ← cellInner_add_right _ (integrable_tval_inner U (A₁.continuous_apply hψ hp))
        (integrable_tval_inner U (A₂.continuous_apply hψ hp))]
    rfl

/-- Negative of an operator. -/
def neg (A : TorusAdj T m R Kc C) : TorusAdj (fun ψ => -T ψ) m R Kc C where
  adj K hK := -A.adj K hK
  bound K hK := by rw [ContinuousLinearMap.opNorm_neg]; exact A.bound K hK
  maps r hr ψ hψ hp := by
    obtain ⟨h1, p1⟩ := A.maps r hr ψ hψ hp
    exact ⟨h1.neg, fun n x => by simp only [Pi.neg_apply, p1 n x]⟩
  ident K hK U ψ hψ hp := by
    change cellInner (tval (-A.adj K hK U)) ψ = _
    rw [cellInner_tval_neg, A.ident K hK U ψ hψ hp,
      ← cellInner_neg_right]
    rfl

/-- Difference of two operators of the same order. -/
def sub (A₁ : TorusAdj T₁ m R Kc C₁) (A₂ : TorusAdj T₂ m R Kc C₂) :
    TorusAdj (fun ψ => T₁ ψ - T₂ ψ) m R Kc (C₁ + C₂) :=
  (A₁.add A₂.neg).ofOp (by funext ψ; exact (sub_eq_add_neg _ _).symm)

/-- Real multiple of an operator. -/
def smul (c : ℝ) (A : TorusAdj T m R Kc C) :
    TorusAdj (fun ψ => c • T ψ) m R Kc (|c| * C) where
  adj K hK := (torusSmulCLM c).comp (A.adj K hK)
  bound K hK := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    exact mul_le_mul (norm_torusSmulCLM_le c) (A.bound K hK)
      (ContinuousLinearMap.opNorm_nonneg _) (abs_nonneg c)
  maps r hr ψ hψ hp := by
    obtain ⟨h1, p1⟩ := A.maps r hr ψ hψ hp
    exact ⟨h1.const_smul c, fun n x => by simp only [Pi.smul_apply, p1 n x]⟩
  ident K hK U ψ hψ hp := by
    change cellInner (tval (c • A.adj K hK U)) ψ = _
    rw [cellInner_tval_smul, A.ident K hK U ψ hψ hp,
      ← cellInner_smul_right]
    rfl

/-- Finite sum of operators of the same order. -/
def sum {ι : Type*} (s : Finset ι) {T : ι → (Vec 2 → F) → (Vec 2 → E)} {C : ι → ℝ}
    (A : ∀ i, TorusAdj (T i) m R Kc (C i)) :
    TorusAdj (fun ψ x => ∑ i ∈ s, T i ψ x) m R Kc (∑ i ∈ s, C i) where
  adj K hK := ∑ i ∈ s, (A i).adj K hK
  bound K hK :=
    (opNorm_finsetSum_le' _ _).trans (Finset.sum_le_sum fun i _ => (A i).bound K hK)
  maps r hr ψ hψ hp :=
    ⟨ContDiff.sum fun i _ => ((A i).maps r hr ψ hψ hp).1, fun n x => by
      exact Finset.sum_congr rfl fun i _ => ((A i).maps r hr ψ hψ hp).2 n x⟩
  ident K hK U ψ hψ hp := by
    classical
    have key : ∀ s' : Finset ι, cellInner (tval (∑ i ∈ s', (A i).adj K hK U)) ψ =
        cellInner (tval U) (fun x => ∑ i ∈ s', T i ψ x) := by
     intro s'
     induction s' using Finset.induction_on with
     | empty =>
      simp only [Finset.sum_empty]
      rw [cellInner_tval_zero]
      simp [cellInner]
     | insert a s ha ih =>
      have hcont : ∀ i, Continuous (T i ψ) := fun i => (A i).continuous_apply hψ hp
      rw [Finset.sum_insert ha, cellInner_tval_add _ _ hψ.continuous,
        (A a).ident K hK U ψ hψ hp]
      rw [ih]
      have hfun : (fun x => ∑ i ∈ insert a s, T i ψ x) =
          fun x => T a ψ x + ∑ i ∈ s, T i ψ x := by
        funext x
        exact Finset.sum_insert ha
      rw [hfun, cellInner_add_right _ (integrable_tval_inner U (hcont a))
        (integrable_tval_inner U (continuous_finsetSum _ fun i _ => hcont i))]
    have h2 := key s
    rw [← sum_apply] at h2
    exact h2

/-- Finite sum of operators indexed by the members of a finset. -/
def sumMem {ι : Type*} (s : Finset ι) {T : ι → (Vec 2 → F) → (Vec 2 → E)} {C : ι → ℝ}
    (A : ∀ i ∈ s, TorusAdj (T i) m R Kc (C i)) :
    TorusAdj (fun ψ x => ∑ i ∈ s, T i ψ x) m R Kc (∑ i ∈ s, C i) :=
  ((TorusAdj.sum (Finset.univ : Finset s) (T := fun i : s => T i.1) (C := fun i : s => C i.1)
    (fun i => A i.1 i.2)).mono le_rfl le_rfl (le_of_eq (by
      rw [Finset.sum_coe_sort s C]))).ofOp (by
    funext ψ x
    exact Finset.sum_coe_sort s (fun i => T i ψ x))

/-- Composition `T₁ ∘ T₂`, of order `m₁ + m₂`. The regularity range `R` must satisfy
`R ≤ R₁` and `R + m₁ ≤ R₂`. -/
def comp {T₁ : (Vec 2 → G) → (Vec 2 → E)} {T₂ : (Vec 2 → F) → (Vec 2 → G)}
    {m₁ m₂ R₁ R₂ : ℕ} (A₁ : TorusAdj T₁ m₁ R₁ Kc C₁) (A₂ : TorusAdj T₂ m₂ R₂ Kc C₂)
    (hR₁ : R ≤ R₁) (hR₂ : R + m₁ ≤ R₂) :
    TorusAdj (fun ψ => T₁ (T₂ ψ)) (m₁ + m₂) R Kc (C₁ * C₂) where
  adj K hK := (A₂.adj K (by omega)).comp
    ((A₁.adj (K + m₂) (by omega)).comp
      (torusCast (by omega : K + (m₁ + m₂) = K + m₂ + m₁)))
  bound K hK := by
    have hb₁ := A₁.bound (K + m₂) (by omega)
    have hb₂ := A₂.bound K (by omega)
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h3 : ‖(A₁.adj (K + m₂) (by omega)).comp
        (torusCast (E := E) (by omega : K + (m₁ + m₂) = K + m₂ + m₁))‖ ≤ C₁ := by
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      calc _ ≤ C₁ * 1 := mul_le_mul hb₁ (norm_torusCast_le _) (ContinuousLinearMap.opNorm_nonneg _)
            ((ContinuousLinearMap.opNorm_nonneg _).trans hb₁)
        _ = C₁ := mul_one C₁
    have h4 : ‖A₂.adj K (by omega)‖ * ‖(A₁.adj (K + m₂) (by omega)).comp
        (torusCast (E := E) (by omega : K + (m₁ + m₂) = K + m₂ + m₁))‖ ≤ C₂ * C₁ :=
      mul_le_mul hb₂ h3 (ContinuousLinearMap.opNorm_nonneg _)
        ((ContinuousLinearMap.opNorm_nonneg _).trans hb₂)
    exact h4.trans (le_of_eq (mul_comm _ _))
  maps r hr ψ hψ hp := by
    have hr' : r + (m₁ + m₂) = (r + m₁) + m₂ := (Nat.add_assoc _ _ _).symm
    rw [hr'] at hψ
    obtain ⟨h2, p2⟩ := A₂.maps (r + m₁) (by omega) ψ hψ hp
    exact A₁.maps r (by omega) (T₂ ψ) (by simpa using h2) p2
  ident K hK U ψ hψ hp := by
    have hψ₂ : ContDiff ℝ (m₂ : ℕ∞) ψ := hψ.of_le (by exact_mod_cast Nat.le_add_left m₂ m₁)
    obtain ⟨h2, p2⟩ := A₂.maps m₁ (by omega) ψ hψ hp
    change cellInner (tval (A₂.adj K _ (A₁.adj (K + m₂) _ (torusCast _ U)))) ψ = _
    rw [A₂.ident K _ _ ψ hψ₂ hp, A₁.ident (K + m₂) _ _ (T₂ ψ) h2 p2, tval_torusCast]

end TorusAdj
end

/-! Pointwise multiplication by a smooth periodic operator field as a `TorusAdj`.

For `M : Vec 2 → F →L E` and a pointwise adjoint `N : Vec 2 → E →L F` (so that
`⟨N x v, w⟩ = ⟨v, M x w⟩`), the operator `T ψ = M · ψ` has adjoint `U ↦ N · U` given by
`TorusHk.mulCoefficient`. The latter is only a function on `TorusHk K E`; here it is promoted to a
bounded linear map, with unweighted norm at most `K! · ∑_{l ≤ K} A_l / l!`, where `A_l` bounds the
operator-array norm of the `l`-th derivative of `N`. -/

section
section Jets

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

/-- Two torus classes whose periodic jets agree almost everywhere on the cell are equal. -/
theorem torusHk_ext_of_jet_ae {K : ℕ} {U V : TorusHk K F}
    (h : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube),
      ∀ a, U.toFunction.jet a x = V.toFunction.jet a x) : U = V := by
  apply Subtype.ext
  apply PiLp.ext
  intro a
  apply Lp.ext
  filter_upwards [h, periodicJetRepresentative_ae U.val a,
    periodicJetRepresentative_ae V.val a] with x hx hU hV
  rw [← hU, ← hV]
  exact hx a

theorem jet_add_ae {K : ℕ} (U V : TorusHk K E) :
    ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ a,
      (U + V).toFunction.jet a x = U.toFunction.jet a x + V.toFunction.jet a x := by
  rw [ae_all_iff]
  intro a
  filter_upwards [periodicJetRepresentative_ae (U + V).val a,
    periodicJetRepresentative_ae U.val a, periodicJetRepresentative_ae V.val a,
    Lp.coeFn_add (U.val a) (V.val a)] with x h1 h2 h3 h4
  change periodicJetRepresentative (U + V).val a x =
    periodicJetRepresentative U.val a x + periodicJetRepresentative V.val a x
  rw [h1, h2, h3]
  exact h4

theorem jet_smul_ae {K : ℕ} (c : ℝ) (U : TorusHk K E) :
    ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ a,
      (c • U).toFunction.jet a x = c • U.toFunction.jet a x := by
  rw [ae_all_iff]
  intro a
  filter_upwards [periodicJetRepresentative_ae (c • U).val a,
    periodicJetRepresentative_ae U.val a, Lp.coeFn_smul c (U.val a)] with x h1 h2 h4
  change periodicJetRepresentative (c • U).val a x = c • periodicJetRepresentative U.val a x
  rw [h1, h2]
  exact h4

end Jets

section Leibniz

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

theorem multiplicationRawJet_congr {K : ℕ} (C : Vec 2 → E →L[ℝ] F) {D D' : RawJet2 K E}
    (a : JetIndex2 K) (x : Vec 2) (h : ∀ b, D b x = D' b x) :
    multiplicationRawJet C D a x = multiplicationRawJet C D' a x := by
  unfold multiplicationRawJet multiplicationTerm
  exact Finset.sum_congr rfl fun m _ => by rw [h]

theorem multiplicationRawJet_add_apply {K : ℕ} (C : Vec 2 → E →L[ℝ] F) (D D' : RawJet2 K E)
    (a : JetIndex2 K) (x : Vec 2) :
    multiplicationRawJet C (fun b y => D b y + D' b y) a x =
      multiplicationRawJet C D a x + multiplicationRawJet C D' a x := by
  unfold multiplicationRawJet multiplicationTerm
  simp only [map_add, Finset.sum_add_distrib]

theorem multiplicationRawJet_smul_apply {K : ℕ} (C : Vec 2 → E →L[ℝ] F) (c : ℝ)
    (D : RawJet2 K E) (a : JetIndex2 K) (x : Vec 2) :
    multiplicationRawJet C (fun b y => c • D b y) a x = c • multiplicationRawJet C D a x := by
  unfold multiplicationRawJet multiplicationTerm
  simp only [map_smul, Finset.smul_sum]

end Leibniz

section Multiplication

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

variable {K : ℕ} {N : Vec 2 → E →L[ℝ] F} {hN : ContDiff ℝ (K : ℕ) N}
  {hp : AVenhance.IsZ2Periodic N} {A : Fin (K + 1) → ℝ}
  {hb : ∀ l x, ‖coefficientDerivativeArray N l.val x‖ ≤ A l}

theorem mulCoefficient_jet_ae (U : TorusHk K E) :
    ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ a,
      (U.mulCoefficient N hN hp hb).toFunction.jet a x =
        multiplicationRawJet N U.toFunction.jet a x := by
  rw [ae_all_iff]
  intro a
  filter_upwards [periodicJetRepresentative_ae (U.mulCoefficient N hN hp hb).val a,
    torusJetToL2_ae (multiplicationRawJet N U.toFunction.jet)
      (U.toFunction.mulCoefficient N hN hp hb).hasPeriodicWeakJet.2.1 a] with x h1 h2
  exact h1.trans h2

/-- Coefficient multiplication as a linear map. -/
def torusMulLM (N : Vec 2 → E →L[ℝ] F) (hN : ContDiff ℝ (K : ℕ) N)
    (hp : AVenhance.IsZ2Periodic N) {A : Fin (K + 1) → ℝ}
    (hb : ∀ l x, ‖coefficientDerivativeArray N l.val x‖ ≤ A l) :
    TorusHk K E →ₗ[ℝ] TorusHk K F where
  toFun U := U.mulCoefficient N hN hp hb
  map_add' U V := by
    apply torusHk_ext_of_jet_ae
    filter_upwards [mulCoefficient_jet_ae (N := N) (hN := hN) (hp := hp) (hb := hb) (U + V),
      mulCoefficient_jet_ae (N := N) (hN := hN) (hp := hp) (hb := hb) U,
      mulCoefficient_jet_ae (N := N) (hN := hN) (hp := hp) (hb := hb) V, jet_add_ae U V,
      jet_add_ae (U.mulCoefficient N hN hp hb) (V.mulCoefficient N hN hp hb)] with
      x h1 h2 h3 h4 h5 a
    rw [h5 a, h1 a, h2 a, h3 a, multiplicationRawJet_congr (D' := fun b y => U.toFunction.jet b y + V.toFunction.jet b y) N a x h4,
      multiplicationRawJet_add_apply]
  map_smul' c U := by
    apply torusHk_ext_of_jet_ae
    filter_upwards [mulCoefficient_jet_ae (N := N) (hN := hN) (hp := hp) (hb := hb) (c • U),
      mulCoefficient_jet_ae (N := N) (hN := hN) (hp := hp) (hb := hb) U, jet_smul_ae c U,
      jet_smul_ae c (U.mulCoefficient N hN hp hb)] with x h1 h2 h4 h5 a
    rw [RingHom.id_apply, h5 a, h1 a, h2 a, multiplicationRawJet_congr (D' := fun b y => c • U.toFunction.jet b y) N a x h4,
      multiplicationRawJet_smul_apply]

/-- The explicit operator-norm constant of coefficient multiplication at order `K`. -/
def mulConstK (K : ℕ) (A : Fin (K + 1) → ℝ) : ℝ :=
  (K.factorial : ℝ) * ∑ l : Fin (K + 1), factorialRootWeight 1 l.val * A l

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] in
theorem mulConstK_nonneg (hb : ∀ l x, ‖coefficientDerivativeArray N l.val x‖ ≤ A l) :
    0 ≤ mulConstK K A := by
  refine mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun l _ => mul_nonneg ?_ ?_)
  · exact div_nonneg (by simp) (Nat.cast_nonneg _)
  · exact (ContinuousLinearMap.opNorm_nonneg _).trans (hb l 0)

end Multiplication
end

/-! Norm bound for coefficient multiplication and the multiplication `TorusAdj`.

The unweighted operator norm of `U ↦ N · U` on `TorusHk K` is bounded by `K! · ∑_{l ≤ K} A_l / l!`
by comparing the unweighted jet norm with the factorial norm at radius `ρ = 1`, whose weights lie
between `1 / (K!)²` and `1`. -/

section
theorem factorialWeightMin_one_ge (K : ℕ) :
    1 / ((K.factorial : ℝ) ^ 2) ≤ factorialWeightMin 1 K := by
  unfold factorialWeightMin
  refine (Finset.le_inf'_iff _ _).2 fun j _ => ?_
  unfold factorialWeight
  rw [one_pow]
  have hj : (j.val.factorial : ℝ) ≤ K.factorial := by
    exact_mod_cast Nat.factorial_le (Nat.le_of_lt_succ j.isLt)
  have hpos : (0 : ℝ) < j.val.factorial := by exact_mod_cast Nat.factorial_pos _
  exact one_div_le_one_div_of_le (pow_pos hpos 2) (pow_le_pow_left₀ hpos.le hj 2)

theorem factorialWeightMax_one_le (K : ℕ) : factorialWeightMax 1 K ≤ 1 := by
  unfold factorialWeightMax
  refine Finset.sup'_le _ _ fun j _ => ?_
  unfold factorialWeight
  rw [one_pow, one_div]
  have h1 : (1 : ℝ) ≤ j.val.factorial := by exact_mod_cast Nat.factorial_pos _
  exact inv_le_one_of_one_le₀ (one_le_pow₀ h1)

section Norm

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

variable {K : ℕ} {N : Vec 2 → E →L[ℝ] F} {hN : ContDiff ℝ (K : ℕ) N}
  {hp : AVenhance.IsZ2Periodic N} {A : Fin (K + 1) → ℝ}
  {hb : ∀ l x, ‖coefficientDerivativeArray N l.val x‖ ≤ A l}

/-- Coefficient multiplication has unweighted norm at most `mulConstK K A`. -/
theorem norm_mulCoefficient_le (U : TorusHk K E) :
    ‖U.mulCoefficient N hN hp hb‖ ≤ mulConstK K A * ‖U‖ := by
  set P := U.mulCoefficient N hN hp hb with hP
  set S := ∑ l : Fin (K + 1), factorialRootWeight 1 l.val * A l with hSdef
  have hS : 0 ≤ S := Finset.sum_nonneg fun l _ => mul_nonneg
    (div_nonneg (by simp) (Nat.cast_nonneg _)) ((ContinuousLinearMap.opNorm_nonneg _).trans (hb l 0))
  have h := U.mulCoefficient_factorialNorm_le hN hp hb (ρ := 1) zero_le_one
  have h2 : factorialNormSq 1 P.val ≤ S ^ 2 * factorialNormSq 1 U.val := by
    calc factorialNormSq 1 P.val = Real.sqrt (factorialNormSq 1 P.val) ^ 2 :=
          (Real.sq_sqrt (factorialNormSq_nonneg _ _)).symm
      _ ≤ (S * Real.sqrt (factorialNormSq 1 U.val)) ^ 2 :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
      _ = S ^ 2 * factorialNormSq 1 U.val := by
          rw [mul_pow, Real.sq_sqrt (factorialNormSq_nonneg _ _)]
  have h3 := factorialNormSq_lower 1 P.val
  have h4 := factorialNormSq_upper 1 U.val
  have hf : (0 : ℝ) < K.factorial := by exact_mod_cast Nat.factorial_pos _
  have hmin := factorialWeightMin_one_ge K
  have hmax := factorialWeightMax_one_le K
  have h5 : (1 / ((K.factorial : ℝ) ^ 2)) * ‖P.val‖ ^ 2 ≤ S ^ 2 * ‖U.val‖ ^ 2 := by
    calc (1 / ((K.factorial : ℝ) ^ 2)) * ‖P.val‖ ^ 2 ≤ factorialWeightMin 1 K * ‖P.val‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hmin (sq_nonneg _)
      _ ≤ factorialNormSq 1 P.val := h3
      _ ≤ S ^ 2 * factorialNormSq 1 U.val := h2
      _ ≤ S ^ 2 * (factorialWeightMax 1 K * ‖U.val‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h4 (sq_nonneg _)
      _ ≤ S ^ 2 * (1 * ‖U.val‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmax (sq_nonneg _)) (sq_nonneg _)
      _ = S ^ 2 * ‖U.val‖ ^ 2 := by rw [one_mul]
  have h6 : ‖P.val‖ ^ 2 ≤ ((K.factorial : ℝ) * S * ‖U.val‖) ^ 2 := by
    have hf2 : (0 : ℝ) < (K.factorial : ℝ) ^ 2 := pow_pos hf 2
    calc ‖P.val‖ ^ 2 = (K.factorial : ℝ) ^ 2 * ((1 / ((K.factorial : ℝ) ^ 2)) * ‖P.val‖ ^ 2) := by
          field_simp
      _ ≤ (K.factorial : ℝ) ^ 2 * (S ^ 2 * ‖U.val‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h5 hf2.le
      _ = ((K.factorial : ℝ) * S * ‖U.val‖) ^ 2 := by ring
  have h7 := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (mul_nonneg hf.le hS) (norm_nonneg _))).mp h6
  change ‖P.val‖ ≤ mulConstK K A * ‖U.val‖
  unfold mulConstK
  rw [← hSdef]
  exact h7

/-- Coefficient multiplication as a bounded linear map. -/
def torusMulCLM (N : Vec 2 → E →L[ℝ] F) (hN : ContDiff ℝ (K : ℕ) N)
    (hp : AVenhance.IsZ2Periodic N) {A : Fin (K + 1) → ℝ}
    (hb : ∀ l x, ‖coefficientDerivativeArray N l.val x‖ ≤ A l) :
    TorusHk K E →L[ℝ] TorusHk K F :=
  LinearMap.mkContinuous (torusMulLM N hN hp hb) (mulConstK K A)
    (fun U => norm_mulCoefficient_le U)

theorem torusMulCLM_apply (U : TorusHk K E) :
    torusMulCLM N hN hp hb U = U.mulCoefficient N hN hp hb := rfl

theorem norm_torusMulCLM_le : ‖torusMulCLM N hN hp hb‖ ≤ mulConstK K A :=
  LinearMap.mkContinuous_norm_le _ (mulConstK_nonneg hb) _

end Norm
end

/-! Pointwise multiplication `T ψ = M · ψ` as a `TorusAdj` of order zero. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

/-- The uniform operator-norm constant for coefficient multiplication through order `Kc`, from
bounds `A l` on the operator-array norms of the derivatives of the adjoint coefficient. -/
def mulConst (A : ℕ → ℝ) (Kc : ℕ) : ℝ :=
  (Kc.factorial : ℝ) * ∑ l ∈ Finset.range (Kc + 1), A l / (l.factorial : ℝ)

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] in
theorem mulConstK_le_mulConst {N : Vec 2 → E →L[ℝ] F} {A : ℕ → ℝ} {K Kc : ℕ} (hK : K ≤ Kc)
    (hA : ∀ l ≤ Kc, ∀ x, ‖coefficientDerivativeArray N l x‖ ≤ A l) :
    mulConstK K (fun l : Fin (K + 1) => A l.val) ≤ mulConst A Kc := by
  have hnn : ∀ l ≤ Kc, 0 ≤ A l / (l.factorial : ℝ) := fun l hl =>
    div_nonneg ((ContinuousLinearMap.opNorm_nonneg _).trans (hA l hl 0)) (Nat.cast_nonneg _)
  have hsum : ∑ l : Fin (K + 1), factorialRootWeight 1 l.val * A l.val =
      ∑ l ∈ Finset.range (K + 1), A l / (l.factorial : ℝ) := by
    rw [← Fin.sum_univ_eq_sum_range (fun l => A l / (l.factorial : ℝ)) (K + 1)]
    exact Finset.sum_congr rfl fun l _ => by
      simp [factorialRootWeight, div_eq_mul_inv, mul_comm]
  unfold mulConstK mulConst
  rw [hsum]
  refine mul_le_mul (by exact_mod_cast Nat.factorial_le hK) ?_
    (Finset.sum_nonneg fun l hl => hnn l (by
      have := Finset.mem_range.mp hl
      omega)) (Nat.cast_nonneg _)
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.mpr (Nat.succ_le_succ hK))
    (fun l hl _ => hnn l (Nat.le_of_lt_succ (Finset.mem_range.mp hl)))

/-- Multiplication by `M` has adjoint multiplication by a pointwise adjoint `N`, of order zero.
Here `M` is `C^R`, `N` is `C^{Kc}`, both are `Z²`-periodic, and `A l` bounds the operator-array
norm of the `l`-th derivative of `N` for `l ≤ Kc`. -/
def TorusAdj.mulOp {M : Vec 2 → F →L[ℝ] E} {N : Vec 2 → E →L[ℝ] F} (R Kc : ℕ)
    (hM : ContDiff ℝ (R : ℕ) M) (hMp : AVenhance.IsZ2Periodic M)
    (hN : ContDiff ℝ (Kc : ℕ) N) (hNp : AVenhance.IsZ2Periodic N)
    (hMN : ∀ x v w, inner ℝ (N x v) w = inner ℝ v (M x w)) (A : ℕ → ℝ)
    (hA : ∀ l ≤ Kc, ∀ x, ‖coefficientDerivativeArray N l x‖ ≤ A l) :
    TorusAdj (fun (ψ : Vec 2 → F) (x : Vec 2) => M x (ψ x)) 0 R Kc (mulConst A Kc) where
  adj K hK :=
    have hKc : K ≤ Kc := by omega
    torusMulCLM N (hN.of_le (by exact_mod_cast hKc)) hNp (A := fun l => A l.val)
      (fun l x => hA l.val ((Nat.le_of_lt_succ l.isLt).trans hKc) x)
  bound K hK := by
    have hKc : K ≤ Kc := by omega
    exact (norm_torusMulCLM_le).trans (mulConstK_le_mulConst hKc hA)
  maps r hr ψ hψ hp := by
    have hψ' : ContDiff ℝ (r : ℕ∞) ψ := by simpa using hψ
    exact ⟨(hM.of_le (by exact_mod_cast hr)).clm_apply hψ', fun n x => by
      change M (x + AVenhance.latticeShift n) (ψ (x + AVenhance.latticeShift n)) = M x (ψ x)
      rw [hMp n x, hp n x]⟩
  ident K hK U ψ hψ hp := by
    have hKc : K ≤ Kc := by omega
    have hae : tval (U.mulCoefficient N (hN.of_le (by exact_mod_cast hKc)) hNp
        (A := fun l : Fin (K + 1) => A l.val)
        (fun l x => hA l.val ((Nat.le_of_lt_succ l.isLt).trans hKc) x)) =ᵐ[
          volume.restrict AVenhance.unitCube] fun x => N x (tval U x) := by
      filter_upwards [mulCoefficient_jet_ae (N := N) (U := U)
        (hN := hN.of_le (by exact_mod_cast hKc)) (hp := hNp)
        (hb := fun l x => hA l.val ((Nat.le_of_lt_succ l.isLt).trans hKc) x)] with x hx
      rw [show tval (U.mulCoefficient N _ hNp _) x = _ from hx (valueIndex2 K),
        multiplicationRawJet_value]
      rfl
    change cellInner (tval (U.mulCoefficient N _ hNp _)) ψ = _
    rw [cellInner_congr_left hae]
    unfold cellInner
    simp_rw [hMN]
end

end AVRegularity.CycleComparison.Coarse
end
end
end
