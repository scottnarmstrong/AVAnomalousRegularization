-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev.Basic
import AVenhance.Infra.Parabolic.FourierGalerkin.WeakGradientPeriodization
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Monotonicity.Lemmas

section
section
/-! Compact mollifications used to extend weak identities to finite-regularity tests. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization Filter Set Metric ContinuousLinearMap
open scoped Convolution Topology Pointwise

namespace AVRegularity.Sobolev

/-- Shrinking normalized smooth kernels, with supports bounded by the unit ball. -/
def testBump (n : ℕ) : ContDiffBump (0 : Vec 2) where
  rIn := ((n : ℝ) + 1)⁻¹ / 2
  rOut := ((n : ℝ) + 1)⁻¹
  rIn_pos := div_pos (inv_pos.mpr (by positivity)) (by norm_num)
  rIn_lt_rOut := half_lt_self (inv_pos.mpr (by positivity))

/-- Ordinary scalar mollification of a test. -/
def mollifyTest (n : ℕ) (g : Vec 2 → ℝ) : Vec 2 → ℝ :=
  (testBump n).normed volume ⋆[lsmul ℝ ℝ, volume] g

/-- The kernels shrink to the origin. -/
theorem testBump_radius_tendsto :
    Tendsto (fun n => (testBump n).rOut) atTop (𝓝 0) := by
  simpa [testBump, one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- Mollification converges at every point of a continuous test. -/
theorem mollifyTest_tendsto {g : Vec 2 → ℝ} (hg : Continuous g) (x : Vec 2) :
    Tendsto (fun n => mollifyTest n g x) atTop (𝓝 (g x)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous testBump_radius_tendsto hg x

/-- Mollifications of a continuous compact test are smooth. -/
theorem mollifyTest_contDiff {g : Vec 2 → ℝ} (hg : Continuous g) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (mollifyTest n g) :=
  (testBump n).hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
    (testBump n).contDiff_normed hg.locallyIntegrable

/-- Every mollification remains compactly supported. -/
theorem mollifyTest_hasCompactSupport {g : Vec 2 → ℝ}
    (hg : HasCompactSupport g) (n : ℕ) : HasCompactSupport (mollifyTest n g) :=
  (testBump n).hasCompactSupport_normed.convolution (lsmul ℝ ℝ) hg

/-- A common compact set contains all mollified supports. -/
theorem mollifyTest_support_subset {g : Vec 2 → ℝ} (n : ℕ) :
    Function.support (mollifyTest n g) ⊆ closedBall (0 : Vec 2) 1 + tsupport g := by
  apply (support_convolution_subset (lsmul ℝ ℝ)).trans
  apply add_subset_add _ subset_closure
  rw [(testBump n).support_normed_eq]
  intro x hx
  rw [mem_closedBall]
  rw [mem_ball] at hx
  apply le_trans (le_of_lt hx)
  change ((n : ℝ) + 1)⁻¹ ≤ 1
  exact inv_le_one_of_one_le₀ (le_add_of_nonneg_left (Nat.cast_nonneg n))

/-- A bound on a continuous test gives a common bound on its mollifications. -/
theorem mollifyTest_norm_le {g : Vec 2 → ℝ} (hg : Continuous g) {M : ℝ}
    (hM : ∀ x, ‖g x‖ ≤ M) (n : ℕ) (x : Vec 2) :
    ‖mollifyTest n g x‖ ≤ 3 * M := by
  have hd : dist (mollifyTest n g x) (g x) ≤ 2 * M := by
    apply (testBump n).dist_normed_convolution_le hg.aestronglyMeasurable
    intro y _hy
    rw [dist_eq_norm]
    exact (norm_sub_le _ _).trans (by simpa [two_mul] using add_le_add (hM y) (hM x))
  calc
    ‖mollifyTest n g x‖ ≤ ‖mollifyTest n g x - g x‖ + ‖g x‖ :=
      by simpa only [sub_add_cancel] using
        (norm_add_le (mollifyTest n g x - g x) (g x))
    _ ≤ 2 * M + M := add_le_add hd (hM x)
    _ = 3 * M := by ring

/-- Locally integrable pairings converge under compact test mollification. -/
theorem integral_mul_mollifyTest_tendsto {u g : Vec 2 → ℝ}
    (hu : LocallyIntegrable u volume) (hg : Continuous g) (hcg : HasCompactSupport g) :
    Tendsto (fun n => ∫ x, u x * mollifyTest n g x) atTop (𝓝 (∫ x, u x * g x)) := by
  obtain ⟨M, hM⟩ := hg.bounded_above_of_compact_support hcg
  let Q := closedBall (0 : Vec 2) 1 + tsupport g
  have hQ : IsCompact Q := (isCompact_closedBall (0 : Vec 2) 1).add hcg
  have hbound : Integrable (Q.indicator (fun x => 3 * M * ‖u x‖)) volume := by
    rw [integrable_indicator_iff hQ.measurableSet]
    exact (hu.integrableOn_isCompact hQ).norm.const_mul (3 * M)
  refine tendsto_integral_of_dominated_convergence _ ?_ hbound ?_ ?_
  · intro n
    exact hu.aestronglyMeasurable.mul (mollifyTest_contDiff hg n).continuous.aestronglyMeasurable
  · intro n
    apply Filter.Eventually.of_forall
    intro x
    by_cases hx : x ∈ Q
    · rw [indicator_of_mem hx, norm_mul]
      calc
        ‖u x‖ * ‖mollifyTest n g x‖ ≤ ‖u x‖ * (3 * M) :=
          mul_le_mul_of_nonneg_left (mollifyTest_norm_le hg hM n x) (norm_nonneg _)
        _ = 3 * M * ‖u x‖ := mul_comm _ _
    · have hz : mollifyTest n g x = 0 := by
        apply Function.notMem_support.mp
        exact fun hh => hx (mollifyTest_support_subset n hh)
      simp [indicator_of_notMem hx, hz]
  · exact Filter.Eventually.of_forall fun x => tendsto_const_nhds.mul (mollifyTest_tendsto hg x)

/-- Differentiating the mollification convolves the classical first derivative. -/
theorem fderiv_mollifyTest_apply {g : Vec 2 → ℝ} (hg : ContDiff ℝ 1 g)
    (hcg : HasCompactSupport g) (n : ℕ) (x v : Vec 2) :
    fderiv ℝ (mollifyTest n g) x v =
      mollifyTest n (fun y => fderiv ℝ g y v) x := by
  unfold mollifyTest
  rw [(hcg.hasFDerivAt_convolution_right (lsmul ℝ ℝ)
    (testBump n).continuous_normed.locallyIntegrable hg x).fderiv]
  exact convolution_precompR_apply (lsmul ℝ ℝ)
    (testBump n).continuous_normed.locallyIntegrable (hcg.fderiv ℝ)
    (hg.continuous_fderiv (by simp)) x v

/-- The literal weak derivative identity also holds for compact `C¹` tests. -/
theorem hasWeakPartialDerivOn_test_contDiff_one {u gi : Vec 2 → ℝ} {i : Fin 2}
    (hweak : HasWeakPartialDerivOn univ i u gi)
    (hu : LocallyIntegrable u volume) (hgi : LocallyIntegrable gi volume)
    {g : Vec 2 → ℝ} (hg : ContDiff ℝ 1 g) (hcg : HasCompactSupport g) :
    ∫ x, u x * fderiv ℝ g x (basisVec i) = -∫ x, gi x * g x := by
  have hval := integral_mul_mollifyTest_tendsto hgi hg.continuous hcg
  have hder := integral_mul_mollifyTest_tendsto hu
    ((hg.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hcg.fderiv_apply (𝕜 := ℝ) (basisVec i))
  have hid : ∀ n, (∫ x, u x * mollifyTest n (fun y => fderiv ℝ g y (basisVec i)) x) =
      -(∫ x, gi x * mollifyTest n g x) := by
    intro n
    simpa only [Measure.restrict_univ, fderiv_mollifyTest_apply hg hcg] using
      hweak (mollifyTest n g) (mollifyTest_contDiff hg.continuous n)
        (mollifyTest_hasCompactSupport hcg n) (subset_univ _)
  exact tendsto_nhds_unique hder ((hval.neg).congr' (Filter.Eventually.of_forall (fun n => (hid n).symm)))

end AVRegularity.Sobolev
end
end

section
/-! The exact finite ℓ¹–ℓ² convolution estimate, with truncated shifts as contractions. -/

@[expose] public noncomputable section

namespace AVRegularity.Sobolev

/-- Move a finite sequence to the right and discard terms beyond its last order. -/
def shiftFiniteSequence {K : ℕ} (l : Fin (K + 1))
    (a : PiLp 2 (fun _ : Fin (K + 1) => ℝ)) : PiLp 2 (fun _ : Fin (K + 1) => ℝ) :=
  WithLp.toLp 2 (fun j => if l.val ≤ j.val then
    a ⟨j.val - l.val, Nat.lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩ else 0)

/-- Each actual truncated shift is a contraction in the Hilbert sequence norm. -/
theorem shiftFiniteSequence_norm_le {K : ℕ} (l : Fin (K + 1))
    (a : PiLp 2 (fun _ : Fin (K + 1) => ℝ)) : ‖shiftFiniteSequence l a‖ ≤ ‖a‖ := by
  classical
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  let s := Finset.univ.filter (fun j : Fin (K + 1) => l.val ≤ j.val)
  let g := fun j : Fin (K + 1) =>
    (⟨j.val - l.val, Nat.lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩ : Fin (K + 1))
  have hinj : Set.InjOn g s := by
    intro j hj k hk heq
    have hjl := (Finset.mem_filter.mp hj).2
    have hkl := (Finset.mem_filter.mp hk).2
    apply Fin.ext
    have hsub := congrArg Fin.val heq
    change j.val - l.val = k.val - l.val at hsub
    exact (Nat.sub_add_cancel hjl).symm.trans
      ((congrArg (fun z => z + l.val) hsub).trans (Nat.sub_add_cancel hkl))
  have heq : (∑ j : Fin (K + 1), ‖shiftFiniteSequence l a j‖ ^ 2) = ∑ j ∈ s, ‖a (g j)‖ ^ 2 := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _hj
    by_cases h : l.val ≤ j.val
    · simp only [shiftFiniteSequence, WithLp.ofLp_toLp, ite_eq_left h, g]
    · simp only [shiftFiniteSequence, WithLp.ofLp_toLp, ite_eq_right h, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
  have himage : (∑ j ∈ s, ‖a (g j)‖ ^ 2) = ∑ k ∈ s.image g, ‖a k‖ ^ 2 := by
    rw [Finset.sum_image]
    exact hinj
  rw [heq, himage]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun j _hj _hjs => sq_nonneg ‖a j‖)

/-- The finite convolution is the sum of its actual shifts. -/
def finiteConvolution {K : ℕ} (c : Fin (K + 1) → ℝ)
    (a : PiLp 2 (fun _ : Fin (K + 1) => ℝ)) : PiLp 2 (fun _ : Fin (K + 1) => ℝ) :=
  ∑ l, c l • shiftFiniteSequence l a

/-- The convolution reads exactly the truncated scalar sequence convolution. -/
theorem finiteConvolution_apply {K : ℕ} (c : Fin (K + 1) → ℝ)
    (a : PiLp 2 (fun _ : Fin (K + 1) => ℝ)) (j : Fin (K + 1)) :
    finiteConvolution c a j = ∑ l : Fin (K + 1), c l *
      (if l.val ≤ j.val then a ⟨j.val - l.val, Nat.lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩ else 0) := by
  change WithLp.ofLp (∑ l : Fin (K + 1), c l • shiftFiniteSequence l a) j = _
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro l _hl
  rfl

/-- Coordinate comparison of nonnegative sequences controls their Hilbert norms. -/
theorem finiteSequence_norm_mono {K : ℕ} (a b : PiLp 2 (fun _ : Fin (K + 1) => ℝ))
    (ha : ∀ j, 0 ≤ a j) (hab : ∀ j, a j ≤ b j) : ‖a‖ ≤ ‖b‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_le_sum
  intro j _hj
  rw [Real.norm_of_nonneg (ha j), Real.norm_of_nonneg ((ha j).trans (hab j))]
  exact (sq_le_sq₀ (ha j) ((ha j).trans (hab j))).mpr (hab j)

/-- Finite ℓ¹–ℓ² Young inequality with exact constant one. -/
theorem finiteConvolution_norm_le {K : ℕ} (c : Fin (K + 1) → ℝ)
    (hc : ∀ l, 0 ≤ c l) (a : PiLp 2 (fun _ : Fin (K + 1) => ℝ)) :
    ‖finiteConvolution c a‖ ≤ (∑ l, c l) * ‖a‖ := by
  calc
    ‖finiteConvolution c a‖ ≤ ∑ l, ‖c l • shiftFiniteSequence l a‖ := norm_sum_le _ _
    _ = ∑ l, c l * ‖shiftFiniteSequence l a‖ := by
      apply Finset.sum_congr rfl
      intro l _hl
      rw [norm_smul, Real.norm_of_nonneg (hc l)]
    _ ≤ ∑ l, c l * ‖a‖ :=
      Finset.sum_le_sum fun l _hl => mul_le_mul_of_nonneg_left (shiftFiniteSequence_norm_le l a) (hc l)
    _ = (∑ l, c l) * ‖a‖ := (Finset.sum_mul _ _ _).symm

end AVRegularity.Sobolev
end
end

section
/-! Positional subsets as finite binary choices, with an exact word-splitting bijection. -/

@[expose] public noncomputable section

namespace AVRegularity.Sobolev

/-- Separate the last direction of an ordered word. -/
def wordInitLastEquiv (d j : ℕ) : DerivativeWord d (j + 1) ≃ DerivativeWord d j × Fin d where
  toFun w := (Fin.init w, w (Fin.last j))
  invFun p := Fin.snoc p.1 p.2
  left_inv := Fin.snoc_init_self
  right_inv p := by simp only [Fin.init_snoc, Fin.snoc_last]

/-- One binary inclusion choice for each position, built in the original order. -/
abbrev PositionMask : ℕ → Type
  | 0 => PUnit
  | j + 1 => PositionMask j × Bool

instance positionMaskFintype : (j : ℕ) → Fintype (PositionMask j)
  | 0 => inferInstanceAs (Fintype PUnit)
  | j + 1 => by
    letI := positionMaskFintype j
    exact inferInstanceAs (Fintype (PositionMask j × Bool))

/-- The number of selected positions. -/
abbrev maskLeftLength : (j : ℕ) → PositionMask j → ℕ
  | 0, _ => 0
  | j + 1, (m, false) => maskLeftLength j m
  | j + 1, (m, true) => maskLeftLength j m + 1

/-- The number of complementary positions. -/
abbrev maskRightLength : (j : ℕ) → PositionMask j → ℕ
  | 0, _ => 0
  | j + 1, (m, false) => maskRightLength j m + 1
  | j + 1, (m, true) => maskRightLength j m

/-- The selected and complementary positions partition the original word. -/
theorem mask_lengths_add (j : ℕ) (m : PositionMask j) :
    maskLeftLength j m + maskRightLength j m = j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    obtain ⟨m, b⟩ := m
    cases b <;> simp only [maskLeftLength, maskRightLength, Nat.add_succ, Nat.succ_add, ih m]

/-- For every positional subset, splitting bijects the full ordered word arrays. -/
def maskWordEquiv (d : ℕ) : (j : ℕ) → (m : PositionMask j) →
    DerivativeWord d j ≃
      DerivativeWord d (maskLeftLength j m) × DerivativeWord d (maskRightLength j m)
  | 0, _ =>
    { toFun := fun _ => (Fin.elim0, Fin.elim0)
      invFun := fun _ => Fin.elim0
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun p => by
        change (Fin.elim0, Fin.elim0) = p
        apply Prod.ext <;> exact Subsingleton.elim _ _ }
  | j + 1, (m, false) =>
    ((wordInitLastEquiv d j).trans ((maskWordEquiv d j m).prodCongr (Equiv.refl (Fin d)))).trans
      ((Equiv.prodAssoc _ _ (Fin d)).trans
        ((Equiv.refl _).prodCongr (wordInitLastEquiv d _).symm))
  | j + 1, (m, true) =>
    ((wordInitLastEquiv d j).trans ((maskWordEquiv d j m).prodCongr (Equiv.refl (Fin d)))).trans
      ((Equiv.prodAssoc _ _ (Fin d)).trans
        (((Equiv.refl _).prodCongr (Equiv.prodComm _ (Fin d))).trans
          ((Equiv.prodAssoc _ (Fin d) _).symm.trans
            ((wordInitLastEquiv d _).symm.prodCongr (Equiv.refl _)))))

/-- Excluding the last position appends its direction to the complementary word. -/
theorem maskWordEquiv_snoc_false (d j : ℕ) (m : PositionMask j)
    (w : DerivativeWord d j) (i : Fin d) :
    maskWordEquiv d (j + 1) (m, false) (Fin.snoc w i) =
      ((maskWordEquiv d j m w).1, Fin.snoc (maskWordEquiv d j m w).2 i) := by
  change ((maskWordEquiv d j m (Fin.init (Fin.snoc w i : DerivativeWord d (j + 1)))).1,
    (Fin.snoc (maskWordEquiv d j m (Fin.init (Fin.snoc w i : DerivativeWord d (j + 1)))).2
      ((Fin.snoc w i : DerivativeWord d (j + 1)) (Fin.last j)) : DerivativeWord d (maskRightLength j m + 1))) = _
  simp only [Fin.init_snoc, Fin.snoc_last]

/-- Including the last position appends its direction to the selected word. -/
theorem maskWordEquiv_snoc_true (d j : ℕ) (m : PositionMask j)
    (w : DerivativeWord d j) (i : Fin d) :
    maskWordEquiv d (j + 1) (m, true) (Fin.snoc w i) =
      (Fin.snoc (maskWordEquiv d j m w).1 i, (maskWordEquiv d j m w).2) := by
  change ((Fin.snoc (maskWordEquiv d j m (Fin.init (Fin.snoc w i : DerivativeWord d (j + 1)))).1
    ((Fin.snoc w i : DerivativeWord d (j + 1)) (Fin.last j)) : DerivativeWord d (maskLeftLength j m + 1)), (maskWordEquiv d j m (Fin.init (Fin.snoc w i : DerivativeWord d (j + 1)))).2) = _
  simp only [Fin.init_snoc, Fin.snoc_last]

/-- The selected word has no more positions than the original word. -/
theorem maskLeftLength_le (j : ℕ) (m : PositionMask j) : maskLeftLength j m ≤ j := by
  exact (Nat.le_add_right (maskLeftLength j m) (maskRightLength j m)).trans_eq
    (mask_lengths_add j m)

/-- The complementary word has no more positions than the original word. -/
theorem maskRightLength_le (j : ℕ) (m : PositionMask j) : maskRightLength j m ≤ j := by
  exact (Nat.le_add_left (maskRightLength j m) (maskLeftLength j m)).trans_eq
    (mask_lengths_add j m)

end AVRegularity.Sobolev
end
end

section
/-! Exact binomial counting of the positional-subset Leibniz terms. -/

@[expose] public noncomputable section

namespace AVRegularity.Sobolev

/-- Binary positional masks have exactly the source binomial multiplicities. -/
theorem sum_positionMask_eq_choose (j : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ m : PositionMask j, f (maskLeftLength j m) (maskRightLength j m)) =
      ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * f l (j - l) := by
  induction j generalizing f with
  | zero =>
    change (∑ _m : PUnit, f 0 0) = _
    simp only [Nat.zero_add, Fintype.sum_unique, Finset.sum_range_one, Nat.choose_zero_right,
      Nat.cast_one, Nat.sub_self, one_mul]
  | succ j ih =>
    change (∑ m : PositionMask j × Bool,
      f (maskLeftLength (j + 1) m) (maskRightLength (j + 1) m)) = _
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, maskLeftLength, maskRightLength, Finset.sum_add_distrib]
    rw [ih (fun l r => f (l + 1) r), ih (fun l r => f l (r + 1)),
      Finset.sum_choose_succ_mul f j]
    have hfalse :
        (∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * f l (j - l + 1)) =
          ∑ l ∈ Finset.range (j + 1), (j.choose l : ℝ) * f l (j + 1 - l) := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [tsub_add_eq_add_tsub (Nat.le_of_lt_succ (Finset.mem_range.mp hl))]
    rw [hfalse, add_comm]

end AVRegularity.Sobolev
end
end
end

section
section
/-! First-order multiplication derived from the literal compact-test weak identity. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization Set

namespace AVRegularity.Sobolev

/-- A locally integrable scalar function pairs integrably with a continuous compact test. -/
theorem integrable_mul_compact_test {u g : Vec 2 → ℝ}
    (hu : LocallyIntegrable u volume) (hg : Continuous g) (hcg : HasCompactSupport g) :
    Integrable (fun x => u x * g x) volume :=
  hu.integrable_smul_right_of_hasCompactSupport hg hcg

/-- The genuine first-order weak product rule uses only `C¹` coefficient regularity. -/
theorem hasWeakPartialDerivOn_mul_contDiff_one {u gi c : Vec 2 → ℝ} {i : Fin 2}
    (hweak : HasWeakPartialDerivOn univ i u gi)
    (hu : LocallyIntegrable u volume) (hgi : LocallyIntegrable gi volume)
    (hc : ContDiff ℝ 1 c) :
    HasWeakPartialDerivOn univ i (fun x => c x * u x)
      (fun x => c x * gi x + fderiv ℝ c x (basisVec i) * u x) := by
  intro φ hφ hφc _hφs
  let dc := fun x => fderiv ℝ c x (basisVec i)
  let dφ := fun x => fderiv ℝ φ x (basisVec i)
  have hdc : Continuous dc :=
    (hc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφ : Continuous dφ :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφc : HasCompactSupport dφ := hφc.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hA := integrable_mul_compact_test hu (hc.continuous.mul hdφ) hdφc.mul_left
  have hB := integrable_mul_compact_test hu (hdc.mul hφ.continuous) hφc.mul_left
  have hC := integrable_mul_compact_test hgi (hc.continuous.mul hφ.continuous) hφc.mul_left
  simp only [Pi.mul_apply] at hA hB hC
  have hder : ∀ x, fderiv ℝ (fun y => c y * φ y) x (basisVec i) =
      c x * dφ x + φ x * dc x := by
    intro x
    rw [fderiv_fun_mul (hc.differentiable (by simp)).differentiableAt
      (hφ.differentiable (by simp)).differentiableAt]
    simp only [add_apply, smul_apply, smul_eq_mul, dc, dφ]
  have hid := hasWeakPartialDerivOn_test_contDiff_one hweak hu hgi
    (hc.mul (hφ.of_le (by simp))) hφc.mul_left
  simp_rw [hder] at hid
  have heq : (fun x => u x * (c x * dφ x + φ x * dc x)) =
      (fun x => u x * (c x * dφ x) + u x * (dc x * φ x)) := by
    funext x
    ring
  rw [heq, integral_add hA hB] at hid
  simp only [Measure.restrict_univ]
  have hleft : (fun x => c x * u x * dφ x) = (fun x => u x * (c x * dφ x)) := by
    funext x
    ring
  have hright : (fun x => (c x * gi x + dc x * u x) * φ x) =
      (fun x => gi x * (c x * φ x) + u x * (dc x * φ x)) := by
    funext x
    ring
  change (∫ x, c x * u x * dφ x) = -(∫ x, (c x * gi x + dc x * u x) * φ x)
  rw [hleft, hright, integral_add hC hB]
  linarith only [hid]

end AVRegularity.Sobolev
end
end

section
/-! Local integrability of the actual periodic cell-L² representatives. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization Set Metric
open scoped Topology

namespace AVRegularity.Sobolev

/-- Periodic cell-`L²` representatives are locally integrable on the covering plane. -/
theorem locallyIntegrable_of_periodic_memL2 {u : Vec 2 → ℝ}
    (hu : MemLp u 2 (volume.restrict AVenhance.unitCube))
    (hp : AVenhance.IsZ2Periodic u) : LocallyIntegrable u volume := by
  intro x
  let φ : ContDiffBump x := ⟨1, 2, by norm_num, by norm_num⟩
  have hint := AVenhance.Infra.Parabolic.FourierGalerkin.periodic_compact_pairing_integrable
    hu hp φ.continuous φ.hasCompactSupport
  refine ⟨ball x 1, ball_mem_nhds x (by norm_num), ?_⟩
  apply hint.integrableOn.congr_fun _ measurableSet_ball
  intro y hy
  change u y * φ y = u y
  rw [φ.one_of_mem_closedBall (ball_subset_closedBall hy), mul_one]

end AVRegularity.Sobolev
end
end

section
/-! Finite sums preserve the literal weak partial derivative identity. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization Set

namespace AVRegularity.Sobolev

/-- Sum the actual weak identities, with integrability supplied by compact tests. -/
theorem hasWeakPartialDerivOn_finsetSum {ι : Type*} (s : Finset ι)
    {u gi : ι → Vec 2 → ℝ} {i : Fin 2}
    (hu : ∀ a ∈ s, LocallyIntegrable (u a) volume)
    (hgi : ∀ a ∈ s, LocallyIntegrable (gi a) volume)
    (hw : ∀ a ∈ s, HasWeakPartialDerivOn univ i (u a) (gi a)) :
    HasWeakPartialDerivOn univ i (fun x => ∑ a ∈ s, u a x) (fun x => ∑ a ∈ s, gi a x) := by
  intro φ hφ hφc hφs
  simp only [Measure.restrict_univ, Finset.sum_mul]
  rw [integral_finsetSum s (fun a ha => integrable_mul_compact_test (hu a ha)
    ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hφc.fderiv_apply (𝕜 := ℝ) (basisVec i))),
    integral_finsetSum s (fun a ha => integrable_mul_compact_test (hgi a ha)
      hφ.continuous hφc), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  simpa only [Measure.restrict_univ] using hw a ha φ hφ hφc hφs

end AVRegularity.Sobolev
end
end

section
/-! Finite-Hilbert-valued multiplication, derived through scalar weak identities. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization Set

namespace AVRegularity.Sobolev

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Coefficient matrix elements retain the exact finite classical regularity. -/
theorem contDiff_coefficient_inner {C : Vec 2 → E →L[ℝ] F} {n : WithTop ℕ∞}
    (hC : ContDiff ℝ n C) (e : E) (f : F) :
    ContDiff ℝ n (fun x => inner ℝ f (C x e)) :=
  (InnerProductSpace.toDual ℝ F f).contDiff.comp (hC.clm_apply contDiff_const)

/-- Differentiate a coefficient matrix element by differentiating its operator. -/
theorem fderiv_coefficient_inner {C : Vec 2 → E →L[ℝ] F}
    (hC : ContDiff ℝ 1 C) (e : E) (f : F) (x v : Vec 2) :
    fderiv ℝ (fun y => inner ℝ f (C y e)) x v = inner ℝ f (fderiv ℝ C x v e) := by
  let L : (E →L[ℝ] F) →L[ℝ] ℝ :=
    (InnerProductSpace.toDual ℝ F f).comp ((ContinuousLinearMap.apply ℝ F) e)
  have h := L.hasFDerivAt.comp x (hC.differentiable (by simp)).differentiableAt.hasFDerivAt
  simpa [L, Function.comp_def] using congrArg (fun A => A v) h.fderiv

omit [CompleteSpace F] in
/-- An operator acting on a vector expands through an orthonormal basis without norm losses. -/
theorem inner_operator_eq_sum [FiniteDimensional ℝ E] (C : E →L[ℝ] F) (u : E) (f : F) :
    inner ℝ f (C u) = ∑ a, inner ℝ f (C (stdOrthonormalBasis ℝ E a)) *
      inner ℝ (stdOrthonormalBasis ℝ E a) u := by
  nth_rw 1 [← (stdOrthonormalBasis ℝ E).sum_repr' u]
  rw [map_sum, inner_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  simp only [map_smul, inner_smul_right]
  exact mul_comm _ _

/-- Continuous operator multiplication preserves local scalar integrability. -/
theorem locallyIntegrable_inner_operator [FiniteDimensional ℝ E]
    {u : Vec 2 → E} {C : Vec 2 → E →L[ℝ] F}
    (hu : ∀ e, LocallyIntegrable (fun x => inner ℝ e (u x)) volume)
    (hC : Continuous C) (f : F) :
    LocallyIntegrable (fun x => inner ℝ f (C x (u x))) volume := by
  have hsum := locallyIntegrable_finsetSum Finset.univ (fun a _ha =>
    (hu (stdOrthonormalBasis ℝ E a)).continuous_mul
      ((InnerProductSpace.toDual ℝ F f).continuous.comp (hC.clm_apply (continuous_const (y := stdOrthonormalBasis ℝ E a)))))
  convert hsum using 1
  funext x
  exact inner_operator_eq_sum (C x) (u x) f

/-- The actual first-order operator weak product rule on the covering plane. -/
theorem hasWeakPartialDerivOn_operator_contDiff_one [FiniteDimensional ℝ E]
    {u gi : Vec 2 → E} {C : Vec 2 → E →L[ℝ] F} {i : Fin 2}
    (hweak : ∀ e, HasWeakPartialDerivOn univ i (fun x => inner ℝ e (u x))
      (fun x => inner ℝ e (gi x)))
    (hu : ∀ e, LocallyIntegrable (fun x => inner ℝ e (u x)) volume)
    (hgi : ∀ e, LocallyIntegrable (fun x => inner ℝ e (gi x)) volume)
    (hC : ContDiff ℝ 1 C) (f : F) :
    HasWeakPartialDerivOn univ i (fun x => inner ℝ f (C x (u x)))
      (fun x => inner ℝ f (C x (gi x) + fderiv ℝ C x (basisVec i) (u x))) := by
  let b := stdOrthonormalBasis ℝ E
  let c := fun a x => inner ℝ f (C x (b a))
  let dc := fun a x => inner ℝ f (fderiv ℝ C x (basisVec i) (b a))
  have hdc : ∀ a, Continuous (dc a) := by
    intro a
    exact (InnerProductSpace.toDual ℝ F f).continuous.comp
      (((hC.continuous_fderiv (by simp)).clm_apply continuous_const).clm_apply continuous_const)
  have hc : ∀ a, ContDiff ℝ 1 (c a) := fun a => contDiff_coefficient_inner hC (b a) f
  have hp : ∀ a, HasWeakPartialDerivOn univ i
      (fun x => c a x * inner ℝ (b a) (u x))
      (fun x => c a x * inner ℝ (b a) (gi x) + dc a x * inner ℝ (b a) (u x)) := by
    intro a
    simpa only [c, dc, fderiv_coefficient_inner hC] using
      hasWeakPartialDerivOn_mul_contDiff_one (hweak (b a)) (hu (b a)) (hgi (b a)) (hc a)
  have hsum := hasWeakPartialDerivOn_finsetSum Finset.univ
    (fun a _ha => (hu (b a)).continuous_mul (hc a).continuous)
    (fun a _ha => ((hgi (b a)).continuous_mul (hc a).continuous).add
      ((hu (b a)).continuous_mul (hdc a))) (fun a _ha => hp a)
  convert hsum using 1
  · funext x
    exact inner_operator_eq_sum (C x) (u x) f
  · funext x
    rw [inner_add_right, inner_operator_eq_sum (C x) (gi x) f,
      inner_operator_eq_sum (fderiv ℝ C x (basisVec i)) (u x) f,
      ← Finset.sum_add_distrib]
    rfl

end AVRegularity.Sobolev
end
end
end
