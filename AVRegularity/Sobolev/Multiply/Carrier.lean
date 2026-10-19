-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev.Multiply.Coefficient
public import AVRegularity.Sobolev.Multiply.OperatorProduct
public import AVRegularity.Sobolev.FactorialShift
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization
namespace AVRegularity.Sobolev

/-! The literal ordered positional-subset Leibniz jet. -/

section
/-- The complementary subword indexes an actual lower-order weak derivative. -/
def maskJetIndex {K j : ℕ} (hj : j ≤ K) (m : PositionMask j)
    (w : DerivativeWord2 j) : JetIndex2 K :=
  ⟨⟨maskRightLength j m, Nat.lt_succ_of_le ((maskRightLength_le j m).trans hj)⟩,
    (maskWordEquiv 2 j m w).2⟩

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A single positional-subset contribution to the ordered Leibniz formula. -/
def multiplicationTerm {K j : ℕ} (hj : j ≤ K) (C : Vec 2 → E →L[ℝ] F)
    (D : RawJet2 K E) (m : PositionMask j) (w : DerivativeWord2 j) (x : Vec 2) : F :=
  orderedCoefficientDerivative C (maskLeftLength j m) (maskWordEquiv 2 j m w).1 x
    (D (maskJetIndex hj m w) x)

/-- Sum over all positional subsets, keeping the original order in each subword. -/
def multiplicationRawJet {K : ℕ} (C : Vec 2 → E →L[ℝ] F) (D : RawJet2 K E) : RawJet2 K F :=
  fun a x => ∑ m : PositionMask a.1.val,
    multiplicationTerm (Nat.le_of_lt_succ a.1.isLt) C D m a.2 x

/-- The order-zero Leibniz jet is the actual pointwise product. -/
theorem multiplicationRawJet_value {K : ℕ} (C : Vec 2 → E →L[ℝ] F)
    (D : RawJet2 K E) (x : Vec 2) :
    multiplicationRawJet C D (valueIndex2 K) x = C x (D (valueIndex2 K) x) := by
  change (∑ m : PUnit, multiplicationTerm (Nat.zero_le K) C D m Fin.elim0 x) = _
  rw [Fintype.sum_unique]
  rfl
end

/-! Finite classical coefficient derivatives descend to the actual periodic cell. -/

section
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Differentiate a periodic function using its literal translation identity. -/
theorem fderiv_isZ2Periodic {C : Vec 2 → G} (hC : Differentiable ℝ C)
    (hp : AVenhance.IsZ2Periodic C) : AVenhance.IsZ2Periodic (fderiv ℝ C) := by
  intro n x
  have ht : HasFDerivAt (fun y : Vec 2 => y + AVenhance.latticeShift n)
      (ContinuousLinearMap.id ℝ (Vec 2)) x := (hasFDerivAt_id x).add_const _
  have hh := (hC (x + AVenhance.latticeShift n)).hasFDerivAt.comp x ht
  have heq : (fun y => C (y + AVenhance.latticeShift n)) = C := funext (hp n)
  change HasFDerivAt (fun y => C (y + AVenhance.latticeShift n))
    ((fderiv ℝ C (x + AVenhance.latticeShift n)).comp (ContinuousLinearMap.id ℝ (Vec 2))) x at hh
  rw [heq] at hh
  simpa only [ContinuousLinearMap.comp_id] using hh.fderiv.symm

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Every available finite classical coefficient derivative is periodic. -/
theorem orderedCoefficientDerivative_isZ2Periodic (C : Vec 2 → E →L[ℝ] F) (j m : ℕ)
    (hC : ContDiff ℝ (j + m : ℕ) C) (hp : AVenhance.IsZ2Periodic C)
    (w : DerivativeWord2 j) :
    AVenhance.IsZ2Periodic (orderedCoefficientDerivative C j w) := by
  induction j generalizing m with
  | zero => exact hp
  | succ j ih =>
    have hCm : ContDiff ℝ (j + (m + 1) : ℕ) C := by
      simpa only [Nat.succ_add, Nat.add_succ] using hC
    have hD := orderedCoefficientDerivative_contDiff C j (m + 1) hCm (Fin.init w)
    have hperiod := fderiv_isZ2Periodic (hD.differentiable (by simp))
      (ih (m + 1) hCm (Fin.init w))
    intro n x
    exact congrArg (fun A => A (basisVec (w (Fin.last j)))) (hperiod n x)
end

end AVRegularity.Sobolev
end

section
open MeasureTheory Homogenization
namespace AVRegularity.Sobolev

/-! L² multiplication estimates with the literal operator norm. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] in
/-- A uniformly bounded continuous operator multiplies genuine `L²` functions. -/
theorem memLp_operator_mul {U : Set (Vec 2)} {C : Vec 2 → E →L[ℝ] F} {u : Vec 2 → E}
    (hC : Continuous C) (hu : MemLp u 2 (volume.restrict U)) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x, ‖C x‖ ≤ M) : MemLp (fun x => C x (u x)) 2 (volume.restrict U) := by
  apply (hu.const_smul M).of_le
  · exact (ContinuousLinearMap.apply ℝ F).flip.aestronglyMeasurable_comp₂
      hC.aestronglyMeasurable hu.aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro x
    calc
      ‖C x (u x)‖ ≤ ‖C x‖ * ‖u x‖ := (C x).le_opNorm _
      _ ≤ M * ‖u x‖ := mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)
      _ = ‖M • u x‖ := by rw [norm_smul, Real.norm_of_nonneg hM]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
/-- The L²-class norm square equals the integral of its representative norm square. -/
theorem normSq_toLp_eq_integral {U : Set (Vec 2)} {u : Vec 2 → E}
    (hu : MemLp u 2 (volume.restrict U)) :
    ‖hu.toLp u‖ ^ 2 = ∫ x in U, ‖u x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  exact hu.coeFn_toLp.mono fun x hx => by
    change inner ℝ ((hu.toLp u) x) ((hu.toLp u) x) = ‖u x‖ ^ 2
    rw [hx, real_inner_self_eq_norm_sq]

omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
/-- Every norm square of an `L²` representative is integrable. -/
theorem integrable_normSq_of_memLp {U : Set (Vec 2)} {u : Vec 2 → E}
    (hu : MemLp u 2 (volume.restrict U)) : Integrable (fun x => ‖u x‖ ^ 2) (volume.restrict U) :=
  hu.norm.integrable_sq

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] in
/-- Bounding the full operator-array norm also bounds each component operator. -/
theorem orderedCoefficientDerivative_norm_le_array (C : Vec 2 → E →L[ℝ] F)
    (j : ℕ) (w : DerivativeWord2 j) (x : Vec 2) :
    ‖orderedCoefficientDerivative C j w x‖ ≤ ‖coefficientDerivativeArray C j x‖ := by
  refine (orderedCoefficientDerivative C j w x).opNorm_le_bound
    (M := ‖coefficientDerivativeArray C j x‖)
    (norm_nonneg (coefficientDerivativeArray C j x)) ?_
  intro z
  exact (PiLp.norm_apply_le (coefficientDerivativeArray C j x z) w).trans
    ((coefficientDerivativeArray C j x).le_opNorm z)

end AVRegularity.Sobolev
end

section
open Homogenization MeasureTheory Set
namespace AVRegularity.Sobolev

/-! Ordered Leibniz weak identities for the literal positional-subset jet. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- A mask excluding the last position puts the new derivative on the weak factor. -/
theorem multiplicationTerm_snoc_false {K j : ℕ} (hj : j < K)
    (C : Vec 2 → E →L[ℝ] F) (D : RawJet2 K E)
    (m : PositionMask j) (w : DerivativeWord2 j) (i : Fin 2) (x : Vec 2) :
    multiplicationTerm (Nat.succ_le_of_lt hj) C D (m, false) (Fin.snoc w i) x =
      orderedCoefficientDerivative C (maskLeftLength j m) (maskWordEquiv 2 j m w).1 x
        (D (nextIndex2 ⟨maskRightLength j m, (maskRightLength_le j m).trans_lt hj⟩
          (maskWordEquiv 2 j m w).2 i) x) := by
  unfold multiplicationTerm maskJetIndex nextIndex2 nextIndex
  rw [maskWordEquiv_snoc_false]

omit [CompleteSpace F] in
/-- A mask including the last position puts the new derivative on the coefficient. -/
theorem multiplicationTerm_snoc_true {K j : ℕ} (hj : j < K)
    (C : Vec 2 → E →L[ℝ] F) (D : RawJet2 K E)
    (m : PositionMask j) (w : DerivativeWord2 j) (i : Fin 2) (x : Vec 2) :
    multiplicationTerm (Nat.succ_le_of_lt hj) C D (m, true) (Fin.snoc w i) x =
      fderiv ℝ (orderedCoefficientDerivative C (maskLeftLength j m)
        (maskWordEquiv 2 j m w).1) x (basisVec i)
        (D (lowerIndex2 ⟨maskRightLength j m, (maskRightLength_le j m).trans_lt hj⟩
          (maskWordEquiv 2 j m w).2) x) := by
  unfold multiplicationTerm maskJetIndex lowerIndex2 lowerIndex
  rw [maskWordEquiv_snoc_true]
  exact congrArg (fun A => A x (D ⟨⟨maskRightLength j m, Nat.lt_succ_of_le ((maskRightLength_le j m).trans (Nat.le_of_lt hj))⟩, (maskWordEquiv 2 j m w).2⟩ x))
    (orderedCoefficientDerivative_snoc C (maskWordEquiv 2 j m w).1 i)

/-- The positional-subset Leibniz jet satisfies genuine ordered weak identities. -/
theorem multiplicationRawJet_hasOrderedWeakJetOn [FiniteDimensional ℝ E] {K : ℕ}
    {C : Vec 2 → E →L[ℝ] F} (hC : ContDiff ℝ (K : ℕ) C) {D : RawJet2 K E}
    (hD : HasOrderedWeakJetOn univ D)
    (hLoc : ∀ a e, LocallyIntegrable (fun x => inner ℝ e (D a x)) volume) :
    HasOrderedWeakJetOn univ (multiplicationRawJet C D) := by
  intro j w i f
  let r := fun m : PositionMask j.val =>
    (⟨maskRightLength j.val m, (maskRightLength_le j.val m).trans_lt j.isLt⟩ : Fin K)
  let A := fun m : PositionMask j.val =>
    orderedCoefficientDerivative C (maskLeftLength j.val m) (maskWordEquiv 2 j.val m w).1
  have hA : ∀ m, ContDiff ℝ 1 (A m) := by
    intro m
    have hle : maskLeftLength j.val m + 1 ≤ K :=
      Nat.succ_le_of_lt ((maskLeftLength_le j.val m).trans_lt j.isLt)
    exact orderedCoefficientDerivative_contDiff C (maskLeftLength j.val m) 1
      (hC.of_le (by exact_mod_cast hle)) (maskWordEquiv 2 j.val m w).1
  let u := fun m x => D (lowerIndex2 (r m) (maskWordEquiv 2 j.val m w).2) x
  let g := fun m x => D (nextIndex2 (r m) (maskWordEquiv 2 j.val m w).2 i) x
  have hp : ∀ m, HasWeakPartialDerivOn univ i (fun x => inner ℝ f (A m x (u m x)))
      (fun x => inner ℝ f (A m x (g m x) + fderiv ℝ (A m) x (basisVec i) (u m x))) := by
    intro m
    exact hasWeakPartialDerivOn_operator_contDiff_one
      (hD (r m) (maskWordEquiv 2 j.val m w).2 i)
      (hLoc _) (hLoc _) (hA m) f
  have hl : ∀ m, LocallyIntegrable (fun x => inner ℝ f (A m x (u m x))) volume :=
    fun m => locallyIntegrable_inner_operator (hLoc _) (hA m).continuous f
  have hr : ∀ m, LocallyIntegrable
      (fun x => inner ℝ f (A m x (g m x) + fderiv ℝ (A m) x (basisVec i) (u m x))) volume := by
    intro m
    simp only [inner_add_right]
    exact (locallyIntegrable_inner_operator (hLoc _) (hA m).continuous f).add
      (locallyIntegrable_inner_operator (hLoc _)
        (((hA m).continuous_fderiv (by simp)).clm_apply continuous_const) f)
  have hs := hasWeakPartialDerivOn_finsetSum Finset.univ
    (fun m _hm => hl m) (fun m _hm => hr m) (fun m _hm => hp m)
  convert hs using 1
  · funext x
    rw [multiplicationRawJet, inner_sum]
    rfl
  · funext x
    change inner ℝ f (∑ m : PositionMask j.val × Bool,
      multiplicationTerm (Nat.succ_le_of_lt j.isLt) C D m (Fin.snoc w i) x) = _
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, inner_sum, inner_add_right,
      multiplicationTerm_snoc_false j.isLt, multiplicationTerm_snoc_true j.isLt]
    apply Finset.sum_congr rfl
    intro m _hm
    exact add_comm _ _

end AVRegularity.Sobolev
end

section
open MeasureTheory Homogenization
namespace AVRegularity.Sobolev

/-! The ordered Leibniz formula retains all lower-order L² data. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Bounded finite coefficient derivatives give L² for every positional-subset term. -/
theorem multiplicationTerm_memLp {K j : ℕ} (hj : j ≤ K) {U : Set (Vec 2)}
    {C : Vec 2 → E →L[ℝ] F} (hC : ContDiff ℝ (K : ℕ) C) {D : RawJet2 K E}
    (hD : JetMemL2On U D) {A : Fin (K + 1) → ℝ}
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l)
    (m : PositionMask j) (w : DerivativeWord2 j) :
    MemLp (multiplicationTerm hj C D m w) 2 (volume.restrict U) := by
  let l : Fin (K + 1) := ⟨maskLeftLength j m,
    Nat.lt_succ_of_le ((maskLeftLength_le j m).trans hj)⟩
  have hCl : ContDiff ℝ (l.val : ℕ) C :=
    hC.of_le (by exact_mod_cast (Nat.le_of_lt_succ l.isLt))
  have hcont : Continuous
      (orderedCoefficientDerivative C l.val (maskWordEquiv 2 j m w).1) :=
    (orderedCoefficientDerivative_contDiff C l.val 0
      (by simpa only [Nat.add_zero] using hCl) (maskWordEquiv 2 j m w).1).continuous
  have hnonneg : 0 ≤ A l := (norm_nonneg (coefficientDerivativeArray C l.val 0)).trans (hb l 0)
  exact memLp_operator_mul hcont (hD (maskJetIndex hj m w)) hnonneg
    (fun x => (orderedCoefficientDerivative_norm_le_array C l.val
      (maskWordEquiv 2 j m w).1 x).trans (hb l x))

/-- The complete ordered Leibniz jet belongs to the literal jet-L² predicate. -/
theorem multiplicationRawJet_memL2On {K : ℕ} {U : Set (Vec 2)}
    {C : Vec 2 → E →L[ℝ] F} (hC : ContDiff ℝ (K : ℕ) C) {D : RawJet2 K E}
    (hD : JetMemL2On U D) {A : Fin (K + 1) → ℝ}
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l) :
    JetMemL2On U (multiplicationRawJet C D) := by
  intro a
  exact memLp_finsetSum Finset.univ (fun m _hm =>
    multiplicationTerm_memLp (Nat.le_of_lt_succ a.1.isLt) hC hD hb m a.2)

end AVRegularity.Sobolev
end

section
open Homogenization MeasureTheory
namespace AVRegularity.Sobolev

/-! The dimension-free tensor estimate for a fixed positional subset. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The fixed-subset tensor square is controlled by the full coefficient operator array. -/
theorem multiplicationTerm_pointwise_sumSq_le {K j : ℕ} (hj : j ≤ K)
    (C : Vec 2 → E →L[ℝ] F) (D : RawJet2 K E) (m : PositionMask j) (x : Vec 2)
    {M : ℝ} (hM : 0 ≤ M)
    (hb : ‖coefficientDerivativeArray C (maskLeftLength j m) x‖ ≤ M) :
    (∑ w : DerivativeWord2 j, ‖multiplicationTerm hj C D m w x‖ ^ 2) ≤
      M ^ 2 * ∑ v : DerivativeWord2 (maskRightLength j m),
        ‖D ⟨⟨maskRightLength j m, Nat.lt_succ_of_le ((maskRightLength_le j m).trans hj)⟩, v⟩ x‖ ^ 2 := by
  let f := fun p : DerivativeWord2 (maskLeftLength j m) × DerivativeWord2 (maskRightLength j m) =>
    ‖orderedCoefficientDerivative C (maskLeftLength j m) p.1 x
      (D ⟨⟨maskRightLength j m, Nat.lt_succ_of_le ((maskRightLength_le j m).trans hj)⟩, p.2⟩ x)‖ ^ 2
  have heq : (∑ w : DerivativeWord2 j, ‖multiplicationTerm hj C D m w x‖ ^ 2) = ∑ p, f p :=
    Fintype.sum_equiv (maskWordEquiv 2 j m) _ _ (fun _ => rfl)
  rw [heq, Fintype.sum_prod_type, Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _hv
  dsimp only [f]
  rw [← coefficientDerivativeArray_normSq]
  have hnorm : ‖coefficientDerivativeArray C (maskLeftLength j m) x
      (D ⟨⟨maskRightLength j m, Nat.lt_succ_of_le ((maskRightLength_le j m).trans hj)⟩, v⟩ x)‖ ≤
      M * ‖D ⟨⟨maskRightLength j m, Nat.lt_succ_of_le ((maskRightLength_le j m).trans hj)⟩, v⟩ x‖ :=
    ((coefficientDerivativeArray C (maskLeftLength j m) x).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hb (norm_nonneg _))
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).mpr hnorm |>.trans_eq
    (mul_pow _ _ 2)

variable [MeasurableSpace E] [MeasurableSpace F]

/-- A fixed-subset contribution as the actual Hilbert array of L² classes. -/
def multiplicationTermL2Array {K j : ℕ} (hj : j ≤ K) {U : Set (Vec 2)}
    {C : Vec 2 → E →L[ℝ] F} (hC : ContDiff ℝ (K : ℕ) C) {D : RawJet2 K E}
    (hD : JetMemL2On U D) {A : Fin (K + 1) → ℝ}
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l) (m : PositionMask j) :
    PiLp 2 (fun _ : DerivativeWord2 j => ComponentL2 (volume.restrict U) F) :=
  WithLp.toLp 2 (fun w =>
    (multiplicationTerm_memLp hj hC hD hb m w).toLp (multiplicationTerm hj C D m w))

/-- The L² tensor bound for one subset has constant one and no dimension factor. -/
theorem multiplicationTermL2Array_normSq_le {K j : ℕ} (hj : j ≤ K) {U : Set (Vec 2)}
    {C : Vec 2 → E →L[ℝ] F} (hC : ContDiff ℝ (K : ℕ) C) {D : RawJet2 K E}
    (hD : JetMemL2On U D) {A : Fin (K + 1) → ℝ}
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l) (m : PositionMask j) :
    ‖multiplicationTermL2Array hj hC hD hb m‖ ^ 2 ≤
      A ⟨maskLeftLength j m, Nat.lt_succ_of_le ((maskLeftLength_le j m).trans hj)⟩ ^ 2 *
      derivativeNormSq (jetToL2 D hD)
        ⟨maskRightLength j m, Nat.lt_succ_of_le ((maskRightLength_le j m).trans hj)⟩ := by
  classical
  let l : Fin (K + 1) := ⟨maskLeftLength j m,
    Nat.lt_succ_of_le ((maskLeftLength_le j m).trans hj)⟩
  let r : Fin (K + 1) := ⟨maskRightLength j m,
    Nat.lt_succ_of_le ((maskRightLength_le j m).trans hj)⟩
  let T := fun w : DerivativeWord2 j => multiplicationTerm hj C D m w
  have hT : ∀ w, MemLp (T w) 2 (volume.restrict U) :=
    multiplicationTerm_memLp hj hC hD hb m
  have hleft := integrable_finsetSum Finset.univ (fun w _hw => integrable_normSq_of_memLp (hT w))
  have hright := integrable_finsetSum Finset.univ
    (fun v _hv => integrable_normSq_of_memLp (hD ⟨r, v⟩))
  have hn : 0 ≤ A l := (norm_nonneg (coefficientDerivativeArray C l.val 0)).trans (hb l 0)
  calc
    ‖multiplicationTermL2Array hj hC hD hb m‖ ^ 2 =
        ∫ x in U, ∑ w : DerivativeWord2 j, ‖T w x‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      change (∑ w : DerivativeWord2 j, ‖(hT w).toLp (T w)‖ ^ 2) = _
      simp_rw [normSq_toLp_eq_integral]
      exact (integral_finsetSum Finset.univ
        (fun w _hw => integrable_normSq_of_memLp (hT w))).symm
    _ ≤ ∫ x in U, A l ^ 2 * ∑ v : DerivativeWord2 r.val, ‖D ⟨r, v⟩ x‖ ^ 2 := by
      apply integral_mono hleft (hright.const_mul (A l ^ 2))
      exact fun x => multiplicationTerm_pointwise_sumSq_le hj C D m x hn (hb l x)
    _ = A l ^ 2 * derivativeNormSq (jetToL2 D hD) r := by
      rw [integral_const_mul, integral_finsetSum Finset.univ
        (fun v _hv => integrable_normSq_of_memLp (hD ⟨r, v⟩))]
      change A l ^ 2 * (∑ v : DerivativeWord2 r.val, ∫ x in U, ‖D ⟨r, v⟩ x‖ ^ 2) =
        A l ^ 2 * ∑ v : DerivativeWord2 r.val, ‖(hD ⟨r, v⟩).toLp (D ⟨r, v⟩)‖ ^ 2
      congr 1
      apply Finset.sum_congr rfl
      intro v _hv
      exact (normSq_toLp_eq_integral (hD ⟨r, v⟩)).symm

/-- Take the square root of the exact tensor-square bound. -/
theorem multiplicationTermL2Array_norm_le {K j : ℕ} (hj : j ≤ K) {U : Set (Vec 2)}
    {C : Vec 2 → E →L[ℝ] F} (hC : ContDiff ℝ (K : ℕ) C) {D : RawJet2 K E}
    (hD : JetMemL2On U D) {A : Fin (K + 1) → ℝ}
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l) (m : PositionMask j) :
    ‖multiplicationTermL2Array hj hC hD hb m‖ ≤
      A ⟨maskLeftLength j m, Nat.lt_succ_of_le ((maskLeftLength_le j m).trans hj)⟩ *
      Real.sqrt (derivativeNormSq (jetToL2 D hD)
        ⟨maskRightLength j m, Nat.lt_succ_of_le ((maskRightLength_le j m).trans hj)⟩) := by
  let l : Fin (K + 1) := ⟨maskLeftLength j m,
    Nat.lt_succ_of_le ((maskLeftLength_le j m).trans hj)⟩
  let r : Fin (K + 1) := ⟨maskRightLength j m,
    Nat.lt_succ_of_le ((maskRightLength_le j m).trans hj)⟩
  have hA : 0 ≤ A l := (norm_nonneg (coefficientDerivativeArray C l.val 0)).trans (hb l 0)
  have hDsq : 0 ≤ derivativeNormSq (jetToL2 D hD) r :=
    Finset.sum_nonneg fun _w _hw => sq_nonneg _
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hA (Real.sqrt_nonneg _))).mp
  change ‖multiplicationTermL2Array hj hC hD hb m‖ ^ 2 ≤
    (A l * Real.sqrt (derivativeNormSq (jetToL2 D hD) r)) ^ 2
  rw [mul_pow, Real.sq_sqrt hDsq]
  exact multiplicationTermL2Array_normSq_le hj hC hD hb m
end

/-! Triangle and exact binomial recombination of the genuine L² Leibniz tensors. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace E] [MeasurableSpace F]

/-- An order of the actual L² jet as a finite Hilbert tensor array. -/
def orderL2Array {K : ℕ} {U : Set (Vec 2)} (D : JetL2 (volume.restrict U) K E) (j : Fin (K + 1)) :
    PiLp 2 (fun _ : DerivativeWord2 j.val => ComponentL2 (volume.restrict U) E) :=
  WithLp.toLp 2 (fun w => D ⟨j, w⟩)

omit [InnerProductSpace ℝ E] in
/-- This array norm is exactly the source derivative tensor norm. -/
theorem orderL2Array_norm {K : ℕ} {U : Set (Vec 2)} (D : JetL2 (volume.restrict U) K E) (j : Fin (K + 1)) :
    ‖orderL2Array D j‖ = Real.sqrt (derivativeNormSq D j) := by
  have hsq : ‖orderL2Array D j‖ ^ 2 = derivativeNormSq D j := PiLp.norm_sq_eq_of_L2 _ _
  rw [← hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

omit [MeasurableSpace E] in
/-- The promoted genuine product tensor equals the sum of the subset tensors. -/
theorem orderL2Array_multiplication_eq_sum {K : ℕ} {U : Set (Vec 2)}
    {C : Vec 2 → E →L[ℝ] F} (hC : ContDiff ℝ (K : ℕ) C) {D : RawJet2 K E}
    (hD : JetMemL2On U D) {A : Fin (K + 1) → ℝ}
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l) (j : Fin (K + 1)) :
    orderL2Array (jetToL2 (multiplicationRawJet C D) (multiplicationRawJet_memL2On hC hD hb)) j =
      ∑ m : PositionMask j.val, multiplicationTermL2Array (Nat.le_of_lt_succ j.isLt) hC hD hb m := by
  classical
  apply PiLp.ext
  intro w
  change (multiplicationRawJet_memL2On hC hD hb ⟨j, w⟩).toLp
    (multiplicationRawJet C D ⟨j, w⟩) =
      WithLp.ofLp (∑ m : PositionMask j.val,
        multiplicationTermL2Array (Nat.le_of_lt_succ j.isLt) hC hD hb m) w
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  apply Lp.ext
  have hsum := Lp.coeFn_fun_finsetSum Finset.univ (fun m : PositionMask j.val =>
    (multiplicationTerm_memLp (Nat.le_of_lt_succ j.isLt) hC hD hb m w).toLp
      (multiplicationTerm (Nat.le_of_lt_succ j.isLt) C D m w))
  have hterms : ∀ᵐ x ∂volume.restrict U, ∀ m : PositionMask j.val,
      ((multiplicationTerm_memLp (Nat.le_of_lt_succ j.isLt) hC hD hb m w).toLp
        (multiplicationTerm (Nat.le_of_lt_succ j.isLt) C D m w)) x =
          multiplicationTerm (Nat.le_of_lt_succ j.isLt) C D m w x :=
    ae_all_iff.mpr fun m => (multiplicationTerm_memLp (Nat.le_of_lt_succ j.isLt) hC hD hb m w).coeFn_toLp
  filter_upwards [(multiplicationRawJet_memL2On hC hD hb ⟨j, w⟩).coeFn_toLp,
    hsum, hterms] with x hx hs ht
  rw [hx]
  change multiplicationRawJet C D ⟨j, w⟩ x =
    (∑ m : PositionMask j.val,
      (multiplicationTerm_memLp (Nat.le_of_lt_succ j.isLt) hC hD hb m w).toLp
        (multiplicationTerm (Nat.le_of_lt_succ j.isLt) C D m w)) x
  rw [hs]
  change (∑ m : PositionMask j.val, multiplicationTerm (Nat.le_of_lt_succ j.isLt) C D m w x) = _
  apply Finset.sum_congr rfl
  intro m _hm
  exact (ht m).symm

/-- Zero extension of a finite scalar sequence. -/
def finiteSequence {K : ℕ} (a : Fin (K + 1) → ℝ) (j : ℕ) : ℝ :=
  if h : j ≤ K then a ⟨j, Nat.lt_succ_of_le h⟩ else 0

/-- Reading a sequence within its finite range returns its exact component. -/
theorem finiteSequence_of_le {K : ℕ} (a : Fin (K + 1) → ℝ) {j : ℕ} (h : j ≤ K) :
    finiteSequence a j = a ⟨j, Nat.lt_succ_of_le h⟩ := by
  simp only [finiteSequence, dite_eq_left h]

/-- The complete product tensor has the source binomial estimate with constant one. -/
theorem multiplication_derivativeNorm_le {K : ℕ} {U : Set (Vec 2)}
    {C : Vec 2 → E →L[ℝ] F} (hC : ContDiff ℝ (K : ℕ) C) {D : RawJet2 K E}
    (hD : JetMemL2On U D) {A : Fin (K + 1) → ℝ}
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l) (j : Fin (K + 1)) :
    Real.sqrt (derivativeNormSq
      (jetToL2 (multiplicationRawJet C D) (multiplicationRawJet_memL2On hC hD hb)) j) ≤
      ∑ l ∈ Finset.range (j.val + 1), (j.val.choose l : ℝ) *
        (finiteSequence A l * finiteSequence (fun r => Real.sqrt (derivativeNormSq (jetToL2 D hD) r)) (j.val - l)) := by
  rw [← orderL2Array_norm, orderL2Array_multiplication_eq_sum hC hD hb]
  calc
    ‖∑ m : PositionMask j.val, multiplicationTermL2Array (Nat.le_of_lt_succ j.isLt) hC hD hb m‖ ≤
        ∑ m : PositionMask j.val, ‖multiplicationTermL2Array (Nat.le_of_lt_succ j.isLt) hC hD hb m‖ :=
      norm_sum_le _ _
    _ ≤ ∑ m : PositionMask j.val, finiteSequence A (maskLeftLength j.val m) *
        finiteSequence (fun r => Real.sqrt (derivativeNormSq (jetToL2 D hD) r)) (maskRightLength j.val m) := by
      apply Finset.sum_le_sum
      intro m _hm
      rw [finiteSequence_of_le A ((maskLeftLength_le j.val m).trans (Nat.le_of_lt_succ j.isLt)),
        finiteSequence_of_le _ ((maskRightLength_le j.val m).trans (Nat.le_of_lt_succ j.isLt))]
      exact multiplicationTermL2Array_norm_le (Nat.le_of_lt_succ j.isLt) hC hD hb m
    _ = _ := sum_positionMask_eq_choose j.val (fun l r =>
      finiteSequence A l * finiteSequence (fun s => Real.sqrt (derivativeNormSq (jetToL2 D hD) s)) r)
end

end AVRegularity.Sobolev
end

section
namespace AVRegularity.Sobolev

/-! Characterization of the actual finite convolution in the source range notation. -/

/-- Restricting a range sum by `l ≤ j` is exactly the sum through `j`. -/
theorem sum_range_if_le {K j : ℕ} (hj : j ≤ K) (f : ℕ → ℝ) :
    (∑ l ∈ Finset.range (K + 1), if l ≤ j then f l else 0) =
      ∑ l ∈ Finset.range (j + 1), f l := by
  have hsub : Finset.range (j + 1) ⊆ Finset.range (K + 1) :=
    Finset.range_mono (Nat.succ_le_succ hj)
  have heq := Finset.sum_subset hsub (f := fun l => if l ≤ j then f l else 0)
    (fun l _hl hnot => ite_eq_right (fun h => hnot (Finset.mem_range.mpr (Nat.lt_succ_of_le h))))
  rw [← heq]
  apply Finset.sum_congr rfl
  intro l hl
  rw [ite_eq_left (Nat.le_of_lt_succ (Finset.mem_range.mp hl))]

/-- Reading finite convolution gives precisely the source truncated convolution sum. -/
theorem finiteConvolution_eq_sum_range {K : ℕ} (c : Fin (K + 1) → ℝ)
    (a : PiLp 2 (fun _ : Fin (K + 1) => ℝ)) (j : Fin (K + 1)) :
    finiteConvolution c a j = ∑ l ∈ Finset.range (j.val + 1),
      finiteSequence c l * finiteSequence (fun r => a r) (j.val - l) := by
  calc
    finiteConvolution c a j = ∑ l : Fin (K + 1),
        if l.val ≤ j.val then finiteSequence c l.val *
          finiteSequence (fun r => a r) (j.val - l.val) else 0 := by
      rw [finiteConvolution_apply]
      apply Finset.sum_congr rfl
      intro l _hl
      by_cases h : l.val ≤ j.val
      · rw [ite_eq_left h, ite_eq_left h,
          finiteSequence_of_le c (Nat.le_of_lt_succ l.isLt),
          finiteSequence_of_le _ ((Nat.sub_le _ _).trans (Nat.le_of_lt_succ j.isLt))]
      · rw [ite_eq_right h, ite_eq_right h, mul_zero]
    _ = ∑ l ∈ Finset.range (K + 1), if l ≤ j.val then
        finiteSequence c l * finiteSequence (fun r => a r) (j.val - l) else 0 :=
      Fin.sum_univ_eq_sum_range (fun l => if l ≤ j.val then
        finiteSequence c l * finiteSequence (fun r => a r) (j.val - l) else 0) (K + 1)
    _ = _ := sum_range_if_le (Nat.le_of_lt_succ j.isLt) _

end AVRegularity.Sobolev
end

section
open MeasureTheory Homogenization
namespace AVRegularity.Sobolev

/-! Factorial reweighting identifies the source norm with a finite Hilbert sequence norm. -/

/-- The source factorial weight at one derivative order. -/
def factorialRootWeight (ρ : ℝ) (j : ℕ) : ℝ := ρ ^ j / (j.factorial : ℝ)

/-- Its square is exactly the already accepted source norm weight. -/
theorem factorialRootWeight_sq (ρ : ℝ) (j : ℕ) :
    factorialRootWeight ρ j ^ 2 = factorialWeight ρ j := by
  rw [factorialRootWeight, factorialWeight, div_pow, ← pow_mul, Nat.mul_comm]

/-- The factorial weights cancel every binomial coefficient exactly. -/
theorem factorialRootWeight_mul_choose (ρ : ℝ) {j l : ℕ} (hl : l ≤ j) :
    factorialRootWeight ρ j * (j.choose l : ℝ) = factorialRootWeight ρ l * factorialRootWeight ρ (j - l) := by
  have hf : (j.choose l : ℝ) * (l.factorial : ℝ) * ((j - l).factorial : ℝ) = (j.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hl
  have hp : ρ ^ j = ρ ^ l * ρ ^ (j - l) := by rw [← pow_add, Nat.add_sub_of_le hl]
  unfold factorialRootWeight
  rw [hp]
  field_simp [Nat.factorial_ne_zero]
  linear_combination (ρ ^ l * ρ ^ (j - l)) * hf

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]

/-- The actual weighted derivative tensor norms as a Hilbert sequence. -/
def factorialJetSequence {K : ℕ} {U : Set (Vec 2)} (ρ : ℝ) (D : JetL2 (volume.restrict U) K E) :
    PiLp 2 (fun _ : Fin (K + 1) => ℝ) :=
  WithLp.toLp 2 (fun j => factorialRootWeight ρ j.val * Real.sqrt (derivativeNormSq D j))

/-- No norm is changed by passing to this finite sequence. -/
theorem factorialJetSequence_normSq {K : ℕ} {U : Set (Vec 2)} (ρ : ℝ) (D : JetL2 (volume.restrict U) K E) :
    ‖factorialJetSequence ρ D‖ ^ 2 = factorialNormSq ρ D := by
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ j : Fin (K + 1), ‖factorialRootWeight ρ j.val * Real.sqrt (derivativeNormSq D j)‖ ^ 2) = _
  unfold factorialNormSq
  apply Finset.sum_congr rfl
  intro j _hj
  have hn : 0 ≤ derivativeNormSq D j := Finset.sum_nonneg fun _w _hw => sq_nonneg _
  rw [Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt hn, factorialRootWeight_sq]

/-- The sequence norm equals the precise source factorial norm. -/
theorem factorialJetSequence_norm {K : ℕ} {U : Set (Vec 2)} (ρ : ℝ) (D : JetL2 (volume.restrict U) K E) :
    ‖factorialJetSequence ρ D‖ = Real.sqrt (factorialNormSq ρ D) := by
  rw [← factorialJetSequence_normSq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

end AVRegularity.Sobolev
end

section
open Homogenization MeasureTheory
namespace AVRegularity.Sobolev

/-! Exact factorial product bound for the actual ordered L² product jet. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace E] [MeasurableSpace F]

/-- Factorial recombination of the genuine Leibniz tensors has constant one.
Here `A` is any pointwise bound of the coefficient derivative arrays. -/
theorem multiplication_factorialNorm_le_of_bounds {K : ℕ} {U : Set (Vec 2)}
    {C : Vec 2 → E →L[ℝ] F} (hC : ContDiff ℝ (K : ℕ) C) {D : RawJet2 K E}
    (hD : JetMemL2On U D) {A : Fin (K + 1) → ℝ}
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Real.sqrt (factorialNormSq ρ
      (jetToL2 (multiplicationRawJet C D) (multiplicationRawJet_memL2On hC hD hb))) ≤
      (∑ l : Fin (K + 1), factorialRootWeight ρ l.val * A l) *
        Real.sqrt (factorialNormSq ρ (jetToL2 D hD)) := by
  let P := jetToL2 (multiplicationRawJet C D) (multiplicationRawJet_memL2On hC hD hb)
  let J := jetToL2 D hD
  let c := fun l : Fin (K + 1) => factorialRootWeight ρ l.val * A l
  let a := factorialJetSequence ρ J
  have hw : ∀ j, 0 ≤ factorialRootWeight ρ j := fun j => div_nonneg (pow_nonneg hρ j) (by positivity)
  have hc : ∀ l, 0 ≤ c l := fun l => mul_nonneg (hw l.val) ((norm_nonneg (coefficientDerivativeArray C l.val 0)).trans (hb l 0))
  have hle : ∀ j : Fin (K + 1), factorialJetSequence ρ P j ≤ finiteConvolution c a j := by
    intro j
    change factorialRootWeight ρ j.val * Real.sqrt (derivativeNormSq P j) ≤ _
    calc
      factorialRootWeight ρ j.val * Real.sqrt (derivativeNormSq P j) ≤
          factorialRootWeight ρ j.val * ∑ l ∈ Finset.range (j.val + 1),
            (j.val.choose l : ℝ) * (finiteSequence A l *
              finiteSequence (fun r => Real.sqrt (derivativeNormSq J r)) (j.val - l)) :=
        mul_le_mul_of_nonneg_left (multiplication_derivativeNorm_le hC hD hb j) (hw j.val)
      _ = finiteConvolution c a j := by
        rw [finiteConvolution_eq_sum_range, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l hl
        have hlj : l ≤ j.val := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
        have hlK : l ≤ K := hlj.trans (Nat.le_of_lt_succ j.isLt)
        have hrK : j.val - l ≤ K := (Nat.sub_le _ _).trans (Nat.le_of_lt_succ j.isLt)
        rw [finiteSequence_of_le A hlK, finiteSequence_of_le _ hrK,
          finiteSequence_of_le c hlK, finiteSequence_of_le _ hrK]
        change factorialRootWeight ρ j.val * ((j.val.choose l : ℝ) *
          (A ⟨l, _⟩ * Real.sqrt (derivativeNormSq J ⟨j.val-l, _⟩))) =
          (factorialRootWeight ρ l * A ⟨l, _⟩) *
            (factorialRootWeight ρ (j.val-l) * Real.sqrt (derivativeNormSq J ⟨j.val-l, _⟩))
        rw [← mul_assoc, factorialRootWeight_mul_choose ρ hlj]
        ring
  have hn : ∀ j, 0 ≤ factorialJetSequence ρ P j :=
    fun j => mul_nonneg (hw j.val) (Real.sqrt_nonneg _)
  calc
    Real.sqrt (factorialNormSq ρ P) = ‖factorialJetSequence ρ P‖ := (factorialJetSequence_norm ρ P).symm
    _ ≤ ‖finiteConvolution c a‖ := finiteSequence_norm_mono _ _ hn hle
    _ ≤ (∑ l, c l) * ‖a‖ := finiteConvolution_norm_le c hc a
    _ = _ := by rw [factorialJetSequence_norm]

end AVRegularity.Sobolev
end

section
open Homogenization MeasureTheory Set
namespace AVRegularity.Sobolev

/-! Coefficient multiplication on the plane and torus weak Sobolev carriers. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- Scalar components of plane `L²` jets are locally integrable. -/
theorem jet_scalar_locallyIntegrable {K : ℕ} {D : RawJet2 K E}
    (hD : JetMemL2On Set.univ D) (a : JetIndex2 K) (e : E) :
    LocallyIntegrable (fun x => inner ℝ e (D a x)) volume := by
  have he : MemLp (fun x => inner ℝ e (D a x)) 2 (volume.restrict Set.univ) :=
    (InnerProductSpace.toDual ℝ E e).comp_memLp' (hD a)
  simpa only [Measure.restrict_univ] using he.locallyIntegrable (by norm_num)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- Periodic cell-`L²` jet components are locally integrable on the covering plane. -/
theorem periodicJet_scalar_locallyIntegrable {K : ℕ} {D : RawJet2 K E}
    (hD : HasPeriodicOrderedWeakJet D) (a : JetIndex2 K) (e : E) :
    LocallyIntegrable (fun x => inner ℝ e (D a x)) volume := by
  have he : MemLp (fun x => inner ℝ e (D a x)) 2
      (volume.restrict AVenhance.unitCube) :=
    (InnerProductSpace.toDual ℝ E e).comp_memLp' (hD.2.1 a)
  apply locallyIntegrable_of_periodic_memL2 he
  intro n x
  change inner ℝ e (D a (x + AVenhance.latticeShift n)) = inner ℝ e (D a x)
  rw [hD.1 a n x]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F] in
/-- The ordered product jet is periodic when both factors are periodic. -/
theorem multiplicationRawJet_isZ2Periodic {K : ℕ} {C : Vec 2 → E →L[ℝ] F}
    (hC : ContDiff ℝ (K : ℕ) C) (hp : AVenhance.IsZ2Periodic C) {D : RawJet2 K E}
    (hD : ∀ a, AVenhance.IsZ2Periodic (D a)) :
    ∀ a, AVenhance.IsZ2Periodic (multiplicationRawJet C D a) := by
  intro a n x
  unfold multiplicationRawJet
  apply Finset.sum_congr rfl
  intro m _hm
  let l := maskLeftLength a.1.val m
  have hle : l ≤ K := (maskLeftLength_le a.1.val m).trans (Nat.le_of_lt_succ a.1.isLt)
  have hCl : ContDiff ℝ (Nat.cast l : WithTop ℕ∞) C := hC.of_le (by exact_mod_cast hle)
  have hperiod := orderedCoefficientDerivative_isZ2Periodic C l 0
    (by simpa only [Nat.add_zero] using hCl) hp (maskWordEquiv 2 a.1.val m a.2).1
  unfold multiplicationTerm
  rw [hperiod n x, hD _ n x]

/-- A plane raw witness is closed under a finite `C^K` operator coefficient. -/
def PlaneHkFunction.mulCoefficient {K : ℕ}
    (w : PlaneHkFunction (Set.univ : Set (Vec 2)) K E)
    (C : Vec 2 → E →L[ℝ] F) (hC : ContDiff ℝ (K : ℕ) C)
    {A : Fin (K + 1) → ℝ}
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l) :
    PlaneHkFunction (Set.univ : Set (Vec 2)) K F where
  jet := multiplicationRawJet C w.jet
  memL2 := multiplicationRawJet_memL2On hC w.memL2 hb
  hasWeakJet := multiplicationRawJet_hasOrderedWeakJetOn hC w.hasWeakJet
    (jet_scalar_locallyIntegrable w.memL2)

/-- A periodic raw witness is closed under a periodic finite `C^K` coefficient. -/
def TorusHkFunction.mulCoefficient {K : ℕ} (w : TorusHkFunction K E)
    (C : Vec 2 → E →L[ℝ] F) (hC : ContDiff ℝ (K : ℕ) C)
    (hp : AVenhance.IsZ2Periodic C) {A : Fin (K + 1) → ℝ}
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l) : TorusHkFunction K F where
  jet := multiplicationRawJet C w.jet
  hasPeriodicWeakJet := ⟨multiplicationRawJet_isZ2Periodic hC hp w.hasPeriodicWeakJet.1,
    multiplicationRawJet_memL2On hC w.hasPeriodicWeakJet.2.1 hb,
    multiplicationRawJet_hasOrderedWeakJetOn hC w.hasPeriodicWeakJet.2.2
      (periodicJet_scalar_locallyIntegrable w.hasPeriodicWeakJet)⟩

/-- Coefficient multiplication maps the plane Hilbert graph to the output graph. -/
def PlaneHk.mulCoefficient {K : ℕ}
    (w : PlaneHk (Set.univ : Set (Vec 2)) K E)
    (C : Vec 2 → E →L[ℝ] F) (hC : ContDiff ℝ (K : ℕ) C)
    {A : Fin (K + 1) → ℝ}
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l) :
    PlaneHk (Set.univ : Set (Vec 2)) K F :=
  (w.toFunction.mulCoefficient C hC hb).toHk

/-- Periodic coefficient multiplication maps the torus graph to the output graph. -/
def TorusHk.mulCoefficient {K : ℕ} (w : TorusHk K E)
    (C : Vec 2 → E →L[ℝ] F) (hC : ContDiff ℝ (K : ℕ) C)
    (hp : AVenhance.IsZ2Periodic C) {A : Fin (K + 1) → ℝ}
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l) : TorusHk K F :=
  (w.toFunction.mulCoefficient C hC hp hb).toHk

/-- The plane multiplier obeys the factorial convolution bound on the actual graph. -/
theorem PlaneHk.mulCoefficient_factorialNorm_le {K : ℕ}
    (w : PlaneHk (Set.univ : Set (Vec 2)) K E) {C : Vec 2 → E →L[ℝ] F}
    (hC : ContDiff ℝ (K : ℕ) C) {A : Fin (K + 1) → ℝ}
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l) {ρ : ℝ}
    (hρ : 0 ≤ ρ) :
    Real.sqrt (factorialNormSq ρ (w.mulCoefficient C hC hb).val) ≤
      (∑ l : Fin (K + 1), factorialRootWeight ρ l.val * A l) *
        Real.sqrt (factorialNormSq ρ w.val) := by
  have h := multiplication_factorialNorm_le_of_bounds hC w.toFunction.memL2 hb hρ
  have hround := congrArg Subtype.val (PlaneHk.toFunction_toHk w)
  change jetToL2 w.toFunction.jet w.toFunction.memL2 = w.val at hround
  rw [hround] at h
  exact h

/-- The torus multiplier obeys the same factorial convolution bound. -/
theorem TorusHk.mulCoefficient_factorialNorm_le {K : ℕ} (w : TorusHk K E)
    {C : Vec 2 → E →L[ℝ] F} (hC : ContDiff ℝ (K : ℕ) C)
    (hp : AVenhance.IsZ2Periodic C) {A : Fin (K + 1) → ℝ}
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l) {ρ : ℝ}
    (hρ : 0 ≤ ρ) :
    Real.sqrt (factorialNormSq ρ (w.mulCoefficient C hC hp hb).val) ≤
      (∑ l : Fin (K + 1), factorialRootWeight ρ l.val * A l) *
        Real.sqrt (factorialNormSq ρ w.val) := by
  have h := multiplication_factorialNorm_le_of_bounds hC
    w.toFunction.hasPeriodicWeakJet.2.1 hb hρ
  have hround := congrArg Subtype.val (TorusHk.toFunction_toHk w)
  change jetToL2 w.toFunction.jet w.toFunction.hasPeriodicWeakJet.2.1 = w.val at hround
  rw [hround] at h
  exact h

end AVRegularity.Sobolev
end
