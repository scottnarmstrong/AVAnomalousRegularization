-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.Seam.FamilyNorm
import AVRegularity.CycleComparison.Residual.Jets.Lift
import AVRegularity.CycleWords.CellTransitionLipschitz
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Bounds

@[expose] public noncomputable section

section
open Homogenization MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! Polynomial prices for translations of the negative-weight compact tests. -/

/-- The squared Japanese bracket at the slow scale. -/
def cutoffBracket (s : ℝ) (x : Vec 2) : ℝ := 1 + s ^ 2 * (x 0 ^ 2 + x 1 ^ 2)

theorem cutoffBracket_one_le (s : ℝ) (x : Vec 2) : 1 ≤ cutoffBracket s x :=
  le_add_of_nonneg_right (mul_nonneg (sq_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _)))

theorem cutoffBracket_add_le (s : ℝ) (x y : Vec 2) :
    cutoffBracket s (x + y) ≤ 2 * cutoffBracket s x * cutoffBracket s y := by
  have h0 : (x 0 + y 0) ^ 2 ≤ 2 * x 0 ^ 2 + 2 * y 0 ^ 2 := by
    nlinarith only [sq_nonneg (x 0 - y 0)]
  have h1 : (x 1 + y 1) ^ 2 ≤ 2 * x 1 ^ 2 + 2 * y 1 ^ 2 := by
    nlinarith only [sq_nonneg (x 1 - y 1)]
  have hs := mul_le_mul_of_nonneg_left (add_le_add h0 h1) (sq_nonneg s)
  have hp := mul_nonneg
    (mul_nonneg (sq_nonneg s) (add_nonneg (sq_nonneg (x 0)) (sq_nonneg (x 1))))
    (mul_nonneg (sq_nonneg s) (add_nonneg (sq_nonneg (y 0)) (sq_nonneg (y 1))))
  dsimp only [cutoffBracket, Pi.add_apply]
  nlinarith only [hs, hp]

/-- Translation increases the inverse polynomial weight by a fixed polynomial in its shift. -/
theorem cutoff_negative_weight_shift (s : ℝ) (p : ℕ) (x y : Vec 2) :
    cutoffBracket s x ^ (-(p : ℝ) / 2) ≤
      (2 * cutoffBracket s y) ^ p * cutoffBracket s (x + y) ^ (-(p : ℝ) / 2) := by
  have hx := cutoffBracket_one_le s x
  have hy := cutoffBracket_one_le s y
  have hxy := cutoffBracket_one_le s (x + y)
  have hq : -(p : ℝ) / 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg p)) (by norm_num)
  have hd : 0 < 2 * cutoffBracket s y := by positivity
  have hh := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < cutoffBracket s (x + y))
    (cutoffBracket_add_le s x y) hq
  have he : (2 * cutoffBracket s x * cutoffBracket s y) ^ (-(p : ℝ) / 2) =
      cutoffBracket s x ^ (-(p : ℝ) / 2) * (2 * cutoffBracket s y) ^ (-(p : ℝ) / 2) := by
    rw [show 2 * cutoffBracket s x * cutoffBracket s y =
      cutoffBracket s x * (2 * cutoffBracket s y) by ring,
      Real.mul_rpow (by positivity) hd.le]
  rw [he] at hh
  have hb : (2 * cutoffBracket s y) ^ ((p : ℝ) / 2) ≤
      (2 * cutoffBracket s y) ^ p := by
    calc
      _ ≤ (2 * cutoffBracket s y) ^ (p : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith only [hy])
          (by linarith only [Nat.cast_nonneg (α := ℝ) p])
      _ = _ := Real.rpow_natCast _ _
  have hm := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hd.le ((p : ℝ) / 2))
  have hc : (2 * cutoffBracket s y) ^ (-(p : ℝ) / 2) *
      (2 * cutoffBracket s y) ^ ((p : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hd]
    rw [show -(p : ℝ) / 2 + (p : ℝ) / 2 = 0 by ring, Real.rpow_zero]
  rw [mul_assoc, hc, mul_one] at hm
  exact hm.trans (by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg (by positivity) _))

/-- A common componentwise `L²` price passes through the inverse-mass jet norm. -/
theorem cutoff_weightedJetNorm_component_le {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)]
    (π : ι → ℝ) (p : ℝ) (j : ℕ) (s r : ℝ) (A : ℝ≥0∞)
    (J J' : ∀ v, ∀ a : ℕ, Sobolev.DerivativeWord2 a → Vec 2 → h v)
    (hb : ∀ v a,
      eLpNorm (fun z => cutoffBracket s z ^ (p / 2) *
        Real.sqrt (∑ w, ‖J v a w z‖ ^ 2)) 2 volume ≤
      A * eLpNorm (fun z => cutoffBracket s z ^ (p / 2) *
        Real.sqrt (∑ w, ‖J' v a w z‖ ^ 2)) 2 volume) :
    weightedJetNorm π p j s r J ≤ A * weightedJetNorm π p j s r J' := by
  let Y := fun v a => eLpNorm (fun z => cutoffBracket s z ^ (p / 2) *
    Real.sqrt (∑ w, ‖J' v a w z‖ ^ 2)) 2 volume
  have hf (a : ℕ) : (∑ v, ENNReal.ofReal ((π v)⁻¹) * (A * Y v a) ^ 2) ^ (1 / 2 : ℝ) =
      A * (∑ v, ENNReal.ofReal ((π v)⁻¹) * Y v a ^ 2) ^ (1 / 2 : ℝ) := by
    have he (v : ι) : ENNReal.ofReal ((π v)⁻¹) * (A * Y v a) ^ 2 =
        A ^ 2 * (ENNReal.ofReal ((π v)⁻¹) * Y v a ^ 2) := by ring
    simp only [he, ← Finset.mul_sum]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast,
      ← ENNReal.rpow_mul]
    norm_num
  unfold weightedJetNorm
  calc
    _ ≤ ∑ a ∈ Finset.range (j + 1), ENNReal.ofReal (r ^ a / (a.factorial : ℝ)) *
        (∑ v, ENNReal.ofReal ((π v)⁻¹) * (A * Y v a) ^ 2) ^ (1 / 2 : ℝ) := by
      apply Finset.sum_le_sum
      intro a _
      gcongr with v
      exact hb v a
    _ = _ := by
      simp_rw [hf]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      dsimp only [Y, cutoffBracket]
      ring

/-- Translations of a continuous jet array have a polynomial cost in the shift. -/
theorem cutoff_weightedJetNorm_translation_le {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)]
    (π : ι → ℝ) (p j : ℕ) (s r : ℝ) (y : Vec 2)
    (J : ∀ v, ∀ a : ℕ, Sobolev.DerivativeWord2 a → Vec 2 → h v)
    (hJ : ∀ v a w, Continuous (J v a w)) :
    weightedJetNorm π (-(p : ℝ)) j s r (fun v a w z => J v a w (z + y)) ≤
      ENNReal.ofReal ((2 * cutoffBracket s y) ^ p) * weightedJetNorm π (-(p : ℝ)) j s r J := by
  apply cutoff_weightedJetNorm_component_le
  intro v a
  let Q := fun z : Vec 2 => cutoffBracket s z ^ (-(p : ℝ) / 2) *
    Real.sqrt (∑ w, ‖J v a w z‖ ^ 2)
  have hQ : Continuous Q := by
    exact (Assembly.weight_continuous s (-(p : ℝ))).mul
      (Real.continuous_sqrt.comp (continuous_finsetSum _ fun w _ => (hJ v a w).norm.pow 2))
  have hbound : eLpNorm (fun z => cutoffBracket s z ^ (-(p : ℝ) / 2) *
      Real.sqrt (∑ w, ‖J v a w (z + y)‖ ^ 2)) 2 volume ≤
      ENNReal.ofReal ((2 * cutoffBracket s y) ^ p) * eLpNorm (Q ∘ fun z => z + y) 2 volume := by
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    · exact (Assembly.weight_continuous s (-(p : ℝ))).aestronglyMeasurable.mul
        (Real.continuous_sqrt.comp_aestronglyMeasurable
          (Finset.aestronglyMeasurable_fun_sum _ fun w _ =>
            ((hJ v a w).comp (continuous_id.add continuous_const)).aestronglyMeasurable.norm.pow 2))
    · exact Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
          (Real.rpow_nonneg (by linarith only [cutoffBracket_one_le s z]) _) (Real.sqrt_nonneg _))]
        exact (mul_le_mul_of_nonneg_right (cutoff_negative_weight_shift s p z y)
          (Real.sqrt_nonneg _)).trans_eq (by
            dsimp only [Q, Function.comp_apply]
            rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
              (Real.rpow_nonneg (by linarith only [cutoffBracket_one_le s (z + y)]) _)
              (Real.sqrt_nonneg _))]
            ring)
  rw [eLpNorm_comp_measurePreserving hQ.aestronglyMeasurable
    (measurePreserving_add_right volume y)] at hbound
  exact hbound

end AVRegularity.CycleWords.Seam
end

section
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! Componentwise bounds of an order-weighted norm give the inverse-mass family bound at the cost
`√(m+1)`, independently of the number of components:
`∑_a w_a (∑_i c_i X_{i,a}²)^{1/2} ≤ √(m+1) (∑_i c_i (∑_a w_a X_{i,a})²)^{1/2}` (Cauchy–Schwarz over
the orders, and `∑ x_a² ≤ (∑ x_a)²`), and `(∑_i c_i (∑_a w_a Y_{i,a})²)^{1/2} ≤ ∑_a w_a
(∑_i c_i Y_{i,a}²)^{1/2}` (Minkowski). -/

theorem familyNorm_sq {ι : Type*} [Fintype ι] (c X : ι → ℝ≥0∞) :
    familyNorm c X ^ 2 = ∑ v, c v * X v ^ 2 := by
  unfold familyNorm
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- Cauchy–Schwarz over a finite index set. -/
theorem ennreal_sum_le_sqrt_card_mul {α : Type*} (s : Finset α) (u : α → ℝ≥0∞) :
    ∑ a ∈ s, u a ≤ ENNReal.ofReal (Real.sqrt s.card) * (∑ a ∈ s, u a ^ 2) ^ (1 / 2 : ℝ) := by
  have h := ENNReal.inner_le_Lp_mul_Lq s (fun _ => (1 : ℝ≥0∞)) u Real.HolderConjugate.two_two
  simp only [one_mul, ENNReal.one_rpow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  · rw [← ENNReal.ofReal_natCast, ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg _)
      (by norm_num), Real.sqrt_eq_rpow]
  · congr 1
    apply Finset.sum_congr rfl
    intro a _
    rw [← ENNReal.rpow_natCast]
    norm_num

/-- **Componentwise to family.** -/
theorem familyNorm_orders_of_components {ι : Type*} [Fintype ι] (c : ι → ℝ≥0∞) (m : ℕ)
    (w : ℕ → ℝ≥0∞) (X Y : ι → ℕ → ℝ≥0∞) (K : ℝ≥0∞)
    (h : ∀ i, ∑ a ∈ Finset.range (m + 1), w a * X i a ≤
      K * ∑ a ∈ Finset.range (m + 1), w a * Y i a) :
    ∑ a ∈ Finset.range (m + 1), w a * familyNorm c (fun i => X i a) ≤
      ENNReal.ofReal (Real.sqrt (m + 1)) * K *
        ∑ a ∈ Finset.range (m + 1), w a * familyNorm c (fun i => Y i a) := by
  set s := Finset.range (m + 1)
  have hcard : (s.card : ℝ) = m + 1 := by simp [s]
  -- the left side through the families of the products
  have hL : ∑ a ∈ s, w a * familyNorm c (fun i => X i a) =
      ∑ a ∈ s, familyNorm c (fun i => w a * X i a) :=
    Finset.sum_congr rfl fun a _ => (familyNorm_mul c _ (w a)).symm
  have h1 := ennreal_sum_le_sqrt_card_mul s (fun a => familyNorm c (fun i => w a * X i a))
  rw [hcard] at h1
  -- the squares
  have h2 : ∑ a ∈ s, familyNorm c (fun i => w a * X i a) ^ 2 ≤
      ∑ i, c i * (∑ a ∈ s, w a * X i a) ^ 2 := by
    simp only [familyNorm_sq]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro i _
    rw [← Finset.mul_sum]
    gcongr
    exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => zero_le)
  have h3 : ∑ i, c i * (∑ a ∈ s, w a * X i a) ^ 2 ≤
      K ^ 2 * ∑ i, c i * (∑ a ∈ s, w a * Y i a) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    calc c i * (∑ a ∈ s, w a * X i a) ^ 2 ≤ c i * (K * ∑ a ∈ s, w a * Y i a) ^ 2 := by
          gcongr
          exact h i
      _ = K ^ 2 * (c i * (∑ a ∈ s, w a * Y i a) ^ 2) := by ring
  have h4 : (K ^ 2 * ∑ i, c i * (∑ a ∈ s, w a * Y i a) ^ 2) ^ (1 / 2 : ℝ) =
      K * familyNorm c (fun i => ∑ a ∈ s, w a * Y i a) := by
    unfold familyNorm
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast,
      ← ENNReal.rpow_mul]
    norm_num
  have h5 : familyNorm c (fun i => ∑ a ∈ s, w a * Y i a) ≤
      ∑ a ∈ s, w a * familyNorm c (fun i => Y i a) := by
    refine (familyNorm_sum_le c s (fun a i => w a * Y i a)).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun a _ => familyNorm_mul c _ (w a)
  calc ∑ a ∈ s, w a * familyNorm c (fun i => X i a)
      = ∑ a ∈ s, familyNorm c (fun i => w a * X i a) := hL
    _ ≤ ENNReal.ofReal (Real.sqrt (m + 1)) *
          (∑ a ∈ s, familyNorm c (fun i => w a * X i a) ^ 2) ^ (1 / 2 : ℝ) := h1
    _ ≤ ENNReal.ofReal (Real.sqrt (m + 1)) *
          (K ^ 2 * ∑ i, c i * (∑ a ∈ s, w a * Y i a) ^ 2) ^ (1 / 2 : ℝ) := by
        gcongr
        exact h2.trans h3
    _ = ENNReal.ofReal (Real.sqrt (m + 1)) * (K * familyNorm c (fun i => ∑ a ∈ s, w a * Y i a)) := by
        rw [h4]
    _ ≤ ENNReal.ofReal (Real.sqrt (m + 1)) * (K * ∑ a ∈ s, w a * familyNorm c (fun i => Y i a)) := by
        gcongr
    _ = _ := by ring

end AVRegularity.CycleWords.Seam
end

section
open Homogenization MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam.YoungKernel

/-! # A weighted Young inequality in `L²` and the Peetre inequality

* `young2`: `‖a ⋆ h‖₂ ≤ ‖a‖₁ ‖h‖₂` for nonnegative extended functions.
* `wbase_sub_le`, `peetre_real` (Peetre): `⟨ϖy⟩^{-n} ⟨ϖ(y-t)⟩^{n} ≤ 2^{n/2} ⟨ϖt⟩^{n}`.
-/

/-- Cauchy-Schwarz against a density. -/
theorem cauchy_schwarz_density {a g : Vec 2 → ℝ≥0∞} (ha : Measurable a) (hg : Measurable g) :
    (∫⁻ t, a t * g t) ^ 2 ≤ (∫⁻ t, a t) * ∫⁻ t, a t * g t ^ 2 := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.withDensity a)
    Real.HolderConjugate.two_two (f := fun _ => (1 : ℝ≥0∞)) (g := g) aemeasurable_const
    hg.aemeasurable
  simp only [Pi.mul_apply, one_mul, ENNReal.one_rpow, lintegral_const, one_mul,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  rw [lintegral_withDensity_eq_lintegral_mul _ ha hg] at h
  have h2 : ∫⁻ t, g t ^ (2 : ℝ) ∂(volume.withDensity a) = ∫⁻ t, a t * g t ^ 2 := by
    rw [lintegral_withDensity_eq_lintegral_mul _ ha (hg.pow_const _)]
    simp
  rw [h2] at h
  have := pow_le_pow_left' h 2
  refine this.trans ?_
  rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul]
  norm_num

/-- Young's inequality `L¹ ∗ L² → L²` for nonnegative functions. -/
theorem young2 {a h : Vec 2 → ℝ≥0∞} (ha : Measurable a) (hh : Measurable h)
    (hfin : ∫⁻ t, a t ≠ ⊤) :
    ∫⁻ y, (∫⁻ t, a t * h (y - t)) ^ 2 ≤ (∫⁻ t, a t) ^ 2 * ∫⁻ y, h y ^ 2 := by
  have hm : Measurable fun p : Vec 2 × Vec 2 => a p.2 * h (p.1 - p.2) ^ 2 :=
    (ha.comp measurable_snd).mul ((hh.comp (measurable_fst.sub measurable_snd)).pow_const _)
  calc ∫⁻ y, (∫⁻ t, a t * h (y - t)) ^ 2
      ≤ ∫⁻ y, (∫⁻ t, a t) * ∫⁻ t, a t * h (y - t) ^ 2 := lintegral_mono fun y =>
        cauchy_schwarz_density ha (hh.comp (measurable_const.sub measurable_id))
    _ = (∫⁻ t, a t) * ∫⁻ y, ∫⁻ t, a t * h (y - t) ^ 2 := by
        rw [lintegral_const_mul' _ _ hfin]
    _ = (∫⁻ t, a t) * ∫⁻ t, ∫⁻ y, a t * h (y - t) ^ 2 := by
        rw [lintegral_lintegral_swap hm.aemeasurable]
    _ = (∫⁻ t, a t) * ∫⁻ t, a t * ∫⁻ y, h y ^ 2 := by
        congr 1
        refine lintegral_congr fun t => ?_
        have hmt : Measurable fun y => h (y - t) ^ 2 :=
          (hh.comp (measurable_sub_const t)).pow_const 2
        rw [lintegral_const_mul _ hmt, lintegral_sub_right_eq_self (fun y => h y ^ 2) t]
    _ = _ := by
        rw [lintegral_mul_const _ ha]
        ring

/-- The weight base `1 + s²|z|²`. -/
def wbase (s : ℝ) (z : Vec 2) : ℝ := 1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)

theorem wbase_pos (s : ℝ) (z : Vec 2) : 0 < wbase s z := by
  unfold wbase; positivity

theorem wbase_one_le (s : ℝ) (z : Vec 2) : 1 ≤ wbase s z := by
  unfold wbase; nlinarith [sq_nonneg s, sq_nonneg (z 0), sq_nonneg (z 1),
    mul_nonneg (sq_nonneg s) (add_nonneg (sq_nonneg (z 0)) (sq_nonneg (z 1)))]

/-- Peetre's inequality on the bases. -/
theorem wbase_sub_le (s : ℝ) (y t : Vec 2) : wbase s (y - t) ≤ 2 * wbase s y * wbase s t := by
  unfold wbase
  simp only [Pi.sub_apply]
  nlinarith [sq_nonneg (s * y 0 + s * t 0), sq_nonneg (s * y 1 + s * t 1),
    sq_nonneg (s ^ 2 * y 0 * t 0), mul_nonneg (sq_nonneg s) (add_nonneg (sq_nonneg (y 0)) (sq_nonneg (y 1))),
    mul_nonneg (sq_nonneg s) (add_nonneg (sq_nonneg (t 0)) (sq_nonneg (t 1))),
    mul_nonneg (mul_nonneg (sq_nonneg s) (add_nonneg (sq_nonneg (y 0)) (sq_nonneg (y 1))))
      (mul_nonneg (sq_nonneg s) (add_nonneg (sq_nonneg (t 0)) (sq_nonneg (t 1))))]

theorem peetre_real {x u v : ℝ} (hx : 0 < x) (hu : 0 < u) (hv : 0 < v)
    (h : u ≤ 2 * x * v) {q : ℝ} (hq : 0 ≤ q) : x ^ (-q) ≤ (2 * v) ^ q * u ^ (-q) := by
  have h1 : x⁻¹ ≤ 2 * v / u := by
    rw [inv_eq_one_div, div_le_div_iff₀ hx hu]; nlinarith
  rw [Real.rpow_neg hx.le, Real.rpow_neg hu.le, ← Real.inv_rpow hx.le,
    ← div_eq_mul_inv, ← Real.div_rpow (by positivity) hu.le]
  exact Real.rpow_le_rpow (inv_nonneg.mpr hx.le) h1 hq

end AVRegularity.CycleWords.Seam.YoungKernel
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam.YoungKernel

/-! # the cell kernel and its truncations
The kernel `K = cutoffKernel μ` is a Schwartz function and even. Its truncations
`κ_R(t) = χ(R⁻¹ t) K(t)` are smooth with compact support, and their weighted `L¹` norms of every
order are bounded uniformly in `R ≥ 1`.
-/

/-- A fixed bump function (one near `0`, compact support). -/
def chiBump : ContDiffBump (0 : Vec 2) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The bump as a function. -/
def chi : Vec 2 → ℝ := ⇑chiBump

theorem chi_contDiff : ContDiff ℝ (⊤ : ℕ∞) chi := chiBump.contDiff

theorem chi_compact : HasCompactSupport chi := chiBump.hasCompactSupport

theorem chi_zero : chi 0 = 1 :=
  chiBump.one_of_mem_closedBall (by simp [chiBump])

theorem chi_abs_le (x : Vec 2) : |chi x| ≤ 1 := by
  change |chiBump x| ≤ 1
  rw [abs_of_nonneg chiBump.nonneg]; exact chiBump.le_one

/-- The truncated kernel. -/
def kappa (μ : Vec 2 → ℝ) (R : ℝ) (t : Vec 2) : ℝ := chi (R⁻¹ • t) * cutoffKernel μ t

theorem kernel_contDiff {μ : Vec 2 → ℝ}
    (hm : ∀ ξ, Real.pi / 2 ≤ Real.sqrt (vecDot ξ ξ) → μ ξ = 0)
    (hs : ContDiff ℝ (⊤ : ℕ∞) μ) : ContDiff ℝ (⊤ : ℕ∞) (cutoffKernel μ) := by
  rw [← seamRealCutoffSchwartz_eq μ (Real.pi / 2) hm hs]
  exact (seamRealCutoffSchwartz μ (Real.pi / 2) hm hs).smooth ⊤

theorem kernel_even (μ : Vec 2 → ℝ) (x : Vec 2) : cutoffKernel μ (-x) = cutoffKernel μ x := by
  unfold cutoffKernel
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
  have : vecDot θ (-x) = - vecDot θ x := by simp [vecDot]
  simp only [this, Real.cos_neg]

theorem one_add_pow_le (r : ℝ) (hr : 0 ≤ r) (m : ℕ) : (1 + r) ^ m ≤ 2 ^ m * (1 + r ^ m) := by
  rcases le_total r 1 with h | h
  · calc (1 + r) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      _ ≤ _ := by nlinarith [pow_nonneg hr m, pow_pos (two_pos : (0:ℝ) < 2) m]
  · calc (1 + r) ^ m ≤ (2 * r) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      _ = 2 ^ m * r ^ m := mul_pow _ _ _
      _ ≤ _ := by nlinarith [pow_nonneg hr m, pow_pos (two_pos : (0:ℝ) < 2) m]

/-- The weighted derivatives of a Schwartz function on the plane are integrable. -/
theorem schwartz_weighted_integrable (F : SchwartzMap (Vec 2) ℝ) (i n : ℕ) :
    Integrable (fun t => (1 + ‖t‖) ^ n * ‖iteratedFDeriv ℝ i F t‖) := by
  obtain ⟨C0, hC0⟩ := F.decay 0 i
  obtain ⟨C1, hC1⟩ := F.decay (n + 3) i
  have hcont : Continuous fun t => (1 + ‖t‖) ^ n * ‖iteratedFDeriv ℝ i F t‖ :=
    (continuous_const.add continuous_norm).pow n |>.mul
      (F.smooth ⊤ |>.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
  have hint := integrable_one_add_norm (E := Vec 2) (μ := volume) (r := 3)
    (by rw [Module.finrank_fintype_fun_eq_card]; norm_num)
  refine (hint.const_mul (2 ^ (n + 3) * (|C0| + |C1|))).mono' hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  have h1 : (1 + ‖t‖) ^ (n + 3) * ‖iteratedFDeriv ℝ i F t‖ ≤ 2 ^ (n + 3) * (|C0| + |C1|) := by
    calc _ ≤ 2 ^ (n + 3) * (1 + ‖t‖ ^ (n + 3)) * ‖iteratedFDeriv ℝ i F t‖ :=
          mul_le_mul_of_nonneg_right (one_add_pow_le _ (norm_nonneg _) _) (norm_nonneg _)
      _ = 2 ^ (n + 3) * (‖t‖ ^ 0 * ‖iteratedFDeriv ℝ i F t‖ +
          ‖t‖ ^ (n + 3) * ‖iteratedFDeriv ℝ i F t‖) := by ring
      _ ≤ _ := by
          exact mul_le_mul_of_nonneg_left (add_le_add ((hC0.2 t).trans (le_abs_self _)) ((hC1.2 t).trans (le_abs_self _))) (by positivity)
  have hp : (0 : ℝ) < 1 + ‖t‖ := by positivity
  have h3 : (1 + ‖t‖) ^ (-(3 : ℝ)) * (1 + ‖t‖) ^ (n + 3) = (1 + ‖t‖) ^ n := by
    rw [Real.rpow_neg hp.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      pow_add]
    field_simp
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc (1 + ‖t‖) ^ n * ‖iteratedFDeriv ℝ i F t‖
      = (1 + ‖t‖) ^ (-(3 : ℝ)) * ((1 + ‖t‖) ^ (n + 3) * ‖iteratedFDeriv ℝ i F t‖) := by
        rw [← mul_assoc, h3]
    _ ≤ (1 + ‖t‖) ^ (-(3 : ℝ)) * (2 ^ (n + 3) * (|C0| + |C1|)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring

theorem nat_le_top (j : ℕ) : (j : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast le_top

/-- The scaled bump as a function of `t`. -/
def chiR (R : ℝ) (t : Vec 2) : ℝ := chi (R⁻¹ • t)

theorem chiR_eq (R : ℝ) :
    chiR R = chi ∘ ⇑(R⁻¹ • ContinuousLinearMap.id ℝ (Vec 2)) := by
  funext t; simp [chiR]

theorem chiR_contDiff (R : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (chiR R) := by
  rw [chiR_eq]
  exact chi_contDiff.comp (R⁻¹ • ContinuousLinearMap.id ℝ (Vec 2)).contDiff

theorem chiR_compact {R : ℝ} (hR : R ≠ 0) : HasCompactSupport (chiR R) :=
  chi_compact.comp_homeomorph (Homeomorph.smul (Units.mk0 R⁻¹ (inv_ne_zero hR)))

/-- The derivatives of the scaled bump are bounded uniformly in `R ≥ 1`. -/
theorem chiR_deriv_bound (j : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ R : ℝ, 1 ≤ R → ∀ t, ‖iteratedFDeriv ℝ j (chiR R) t‖ ≤ B := by
  obtain ⟨B, hB⟩ := (chi_contDiff.continuous_iteratedFDeriv (m := j)
    (nat_le_top j)).bounded_above_of_compact_support (chi_compact.iteratedFDeriv j)
  refine ⟨B, (norm_nonneg _).trans (hB 0), fun R hR t => ?_⟩
  have hRp : 0 < R := zero_lt_one.trans_le hR
  rw [chiR_eq, ContinuousLinearMap.iteratedFDeriv_comp_right _
    chi_contDiff t (nat_le_top j)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hg : ‖R⁻¹ • ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    have : R⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR
    simp only [smul_apply, ContinuousLinearMap.id_apply, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRp), one_mul]
    nlinarith [norm_nonneg x]
  calc _ ≤ ‖iteratedFDeriv ℝ j chi _‖ * ∏ _i : Fin j, 1 := by
        gcongr
    _ ≤ B := by simpa using hB _

theorem kappa_contDiff {μ : Vec 2 → ℝ}
    (hm : ∀ ξ, Real.pi / 2 ≤ Real.sqrt (vecDot ξ ξ) → μ ξ = 0)
    (hs : ContDiff ℝ (⊤ : ℕ∞) μ) (R : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (kappa μ R) :=
  (chiR_contDiff R).mul (kernel_contDiff hm hs)

theorem kappa_compact (μ : Vec 2 → ℝ) {R : ℝ} (hR : R ≠ 0) : HasCompactSupport (kappa μ R) :=
  (chiR_compact hR).mul_right

/-- Leibniz bound for the derivatives of the truncated kernel, uniform in `R ≥ 1`. -/
theorem kappa_deriv_bound {μ : Vec 2 → ℝ}
    (hm : ∀ ξ, Real.pi / 2 ≤ Real.sqrt (vecDot ξ ξ) → μ ξ = 0)
    (hs : ContDiff ℝ (⊤ : ℕ∞) μ) (a : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ R : ℝ, 1 ≤ R → ∀ t, ‖iteratedFDeriv ℝ a (kappa μ R) t‖ ≤
      B * ∑ j ∈ Finset.range (a + 1), ‖iteratedFDeriv ℝ j (cutoffKernel μ) t‖ := by
  choose Bc hBc0 hBc using chiR_deriv_bound
  refine ⟨∑ i ∈ Finset.range (a + 1), (a.choose i : ℝ) * Bc i, Finset.sum_nonneg fun i _ =>
    mul_nonneg (Nat.cast_nonneg _) (hBc0 i), fun R hR t => ?_⟩
  have hK := kernel_contDiff hm hs
  have hLeib := norm_iteratedFDeriv_mul_le (chiR_contDiff R) hK t (n := a) (nat_le_top a)
  refine hLeib.trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hia : a - i ∈ Finset.range (a + 1) := Finset.mem_range.2 (by omega)
  have hS : ‖iteratedFDeriv ℝ (a - i) (cutoffKernel μ) t‖ ≤
      ∑ j ∈ Finset.range (a + 1), ‖iteratedFDeriv ℝ j (cutoffKernel μ) t‖ :=
    Finset.single_le_sum (f := fun j => ‖iteratedFDeriv ℝ j (cutoffKernel μ) t‖)
      (fun _ _ => norm_nonneg _) hia
  calc (a.choose i : ℝ) * ‖iteratedFDeriv ℝ i (chiR R) t‖ * ‖iteratedFDeriv ℝ (a - i) (cutoffKernel μ) t‖
      ≤ (a.choose i : ℝ) * Bc i * ∑ j ∈ Finset.range (a + 1), ‖iteratedFDeriv ℝ j (cutoffKernel μ) t‖ := by
        have h1 := hBc i R hR t
        have h0 := hBc0 i
        have hc : (0 : ℝ) ≤ a.choose i := Nat.cast_nonneg _
        have := mul_le_mul_of_nonneg_left h1 hc
        exact mul_le_mul this hS (norm_nonneg _) (mul_nonneg hc h0)
    _ = _ := rfl

theorem kernel_weighted_integrable {μ : Vec 2 → ℝ}
    (hm : ∀ ξ, Real.pi / 2 ≤ Real.sqrt (vecDot ξ ξ) → μ ξ = 0)
    (hs : ContDiff ℝ (⊤ : ℕ∞) μ) (i n : ℕ) :
    Integrable (fun t => (1 + ‖t‖) ^ n * ‖iteratedFDeriv ℝ i (cutoffKernel μ) t‖) := by
  have := schwartz_weighted_integrable (seamRealCutoffSchwartz μ (Real.pi / 2) hm hs) i n
  rwa [seamRealCutoffSchwartz_eq μ (Real.pi / 2) hm hs] at this

theorem wbase_rpow_le (ϖ : ℝ) (hϖ : ϖ ≤ 1) (hϖ0 : 0 < ϖ) (t : Vec 2) (n : ℕ) :
    (2 * wbase ϖ t) ^ ((n : ℝ) / 2) ≤ (2 * (1 + ‖t‖)) ^ n := by
  have h0 : |t 0| ≤ ‖t‖ := by simpa using norm_le_pi_norm t 0
  have h1 : |t 1| ≤ ‖t‖ := by simpa using norm_le_pi_norm t 1
  have hb : 2 * wbase ϖ t ≤ (2 * (1 + ‖t‖)) ^ 2 := by
    unfold wbase
    have e0 : t 0 ^ 2 ≤ ‖t‖ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h0 2
    have e1 : t 1 ^ 2 ≤ ‖t‖ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have hϖ2 : ϖ ^ 2 ≤ 1 := by nlinarith
    have : ϖ ^ 2 * (t 0 ^ 2 + t 1 ^ 2) ≤ 2 * ‖t‖ ^ 2 := by
      calc _ ≤ 1 * (t 0 ^ 2 + t 1 ^ 2) :=
            mul_le_mul_of_nonneg_right hϖ2 (by positivity)
        _ ≤ _ := by linarith
    nlinarith [norm_nonneg t]
  have hpos : 0 ≤ 2 * wbase ϖ t := by have := wbase_pos ϖ t; positivity
  calc (2 * wbase ϖ t) ^ ((n : ℝ) / 2) ≤ ((2 * (1 + ‖t‖)) ^ 2) ^ ((n : ℝ) / 2) :=
        Real.rpow_le_rpow hpos hb (by positivity)
    _ = (2 * (1 + ‖t‖)) ^ n := by
        rw [← Real.rpow_natCast (2 * (1 + ‖t‖)) 2, ← Real.rpow_mul (by positivity)]
        rw [show ((2 : ℕ) : ℝ) * ((n : ℝ) / 2) = (n : ℝ) by push_cast; ring, Real.rpow_natCast]

/-- The weighted `L¹` norm of the derivatives of the truncated kernel, uniformly in `R ≥ 1` and
the scale `ϖ ≤ 1`. -/
theorem kappa_young_const {μ : Vec 2 → ℝ}
    (hm : ∀ ξ, Real.pi / 2 ≤ Real.sqrt (vecDot ξ ξ) → μ ξ = 0)
    (hs : ContDiff ℝ (⊤ : ℕ∞) μ) (a n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (R ϖ : ℝ), 1 ≤ R → 0 < ϖ → ϖ ≤ 1 → ∀ w : DerivativeWord2 a,
      ∫⁻ t, ENNReal.ofReal ((2 * wbase ϖ t) ^ ((n : ℝ) / 2) *
        ‖orderedDerivative w (kappa μ R) t‖) ≤ ENNReal.ofReal A := by
  obtain ⟨B, hB0, hB⟩ := kappa_deriv_bound hm hs a
  set G : Vec 2 → ℝ := fun t => 2 ^ n * B *
    ∑ j ∈ Finset.range (a + 1), ((1 + ‖t‖) ^ n * ‖iteratedFDeriv ℝ j (cutoffKernel μ) t‖) with hG
  have hGi : Integrable G :=
    (integrable_finsetSum _ fun j _ => kernel_weighted_integrable hm hs j n).const_mul _
  have hG0 : ∀ t, 0 ≤ G t := fun t => by
    simp only [hG]; positivity
  refine ⟨∫ t, G t, integral_nonneg hG0, fun R ϖ hR hϖ hϖ1 w => ?_⟩
  rw [ofReal_integral_eq_lintegral_ofReal hGi (Filter.Eventually.of_forall hG0)]
  refine lintegral_mono fun t => ENNReal.ofReal_le_ofReal ?_
  have hκ : ContDiff ℝ (a : ℕ∞) (kappa μ R) := (kappa_contDiff hm hs R).of_le (nat_le_top a)
  have h1 := norm_orderedDerivative_le hκ w t
  have h2 := hB R hR t
  have h3 := wbase_rpow_le ϖ hϖ1 hϖ t n
  have h4 : (0 : ℝ) ≤ (2 * wbase ϖ t) ^ ((n : ℝ) / 2) := Real.rpow_nonneg (by
    have := wbase_pos ϖ t; positivity) _
  calc (2 * wbase ϖ t) ^ ((n : ℝ) / 2) * ‖orderedDerivative w (kappa μ R) t‖
      ≤ (2 * (1 + ‖t‖)) ^ n * (B * ∑ j ∈ Finset.range (a + 1),
        ‖iteratedFDeriv ℝ j (cutoffKernel μ) t‖) :=
        mul_le_mul h3 (h1.trans h2) (norm_nonneg _) (by positivity)
    _ = G t := by
        simp only [hG, Finset.mul_sum, mul_pow]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring

end AVRegularity.CycleWords.Seam.YoungKernel
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords.Seam.NegLowBand

/-! # Derivatives of the weight `ϖ^{|β|}/β! · z^β · χ_R`

`‖D^i q_{β,R}(z)‖ ≤ C_i ⟨ϖz⟩^{n}` for `|β| ≤ n`, uniformly in `R ≥ 1` and `0 < ϖ ≤ 1`.
-/

open AVRegularity.CycleWords.Seam.YoungKernel

/-- The moment weight with the cutoff: `ϖ^{|β|}/β! z₀^{β₁} z₁^{β₂} χ(z/R)`. -/
def qfun (ϖ : ℝ) (β : ℕ × ℕ) (R : ℝ) (z : Vec 2) : ℝ :=
  (ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) *
    ((z 0 ^ β.1 * z 1 ^ β.2) * chiR R z)

theorem coord_le_norm (c : Fin 2) (z : Vec 2) : |z c| ≤ ‖z‖ := by
  simpa using norm_le_pi_norm z c

theorem coord_pow_deriv_bound (c : Fin 2) (b i : ℕ) (z : Vec 2) :
    ‖iteratedFDeriv ℝ i (fun y : Vec 2 => y c ^ b) z‖ ≤ (b.factorial : ℝ) * (1 + ‖z‖) ^ b := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => t ^ b) := by fun_prop
  have e : (fun y : Vec 2 => y c ^ b) =
      (fun t : ℝ => t ^ b) ∘ ⇑(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) c) :=
    rfl
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right _ hg z (nat_le_top i)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hL : ‖(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) c)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    simpa using norm_le_pi_norm x c
  have h1 : ‖iteratedFDeriv ℝ i (fun t : ℝ => t ^ b)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) c) z)‖ ≤
      (b.factorial : ℝ) * (1 + ‖z‖) ^ b := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_pow]
    simp only [ContinuousLinearMap.proj_apply, norm_mul, norm_pow, Real.norm_eq_abs, Nat.abs_cast]
    have hd : (b.descFactorial i : ℝ) ≤ (b.factorial : ℝ) := by
      by_cases hi : i ≤ b
      · have := Nat.factorial_mul_descFactorial hi
        have hp : 0 < (b - i).factorial := Nat.factorial_pos _
        have : b.descFactorial i ≤ b.factorial := by
          calc b.descFactorial i ≤ (b - i).factorial * b.descFactorial i :=
                Nat.le_mul_of_pos_left _ hp
            _ = b.factorial := this
        exact_mod_cast this
      · rw [Nat.descFactorial_eq_zero_iff_lt.2 (not_le.1 hi)]
        simp
    have hz : |z c| ^ (b - i) ≤ (1 + ‖z‖) ^ b := by
      calc |z c| ^ (b - i) ≤ (1 + ‖z‖) ^ (b - i) :=
            pow_le_pow_left₀ (abs_nonneg _) (by linarith [coord_le_norm c z]) _
        _ ≤ (1 + ‖z‖) ^ b :=
            pow_le_pow_right₀ (by linarith [norm_nonneg z]) (Nat.sub_le b i)
    exact mul_le_mul hd hz (by positivity) (by positivity)
  calc _ ≤ ‖iteratedFDeriv ℝ i (fun t : ℝ => t ^ b)
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) c) z)‖ *
          ∏ _i : Fin i, ‖(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) c)‖ :=
        le_rfl
    _ ≤ ‖iteratedFDeriv ℝ i (fun t : ℝ => t ^ b)
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) c) z)‖ * 1 := by
        gcongr
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        exact pow_le_one₀ (norm_nonneg _) hL
    _ ≤ _ := by rw [mul_one]; exact h1

theorem monomial_deriv_bound (b1 b2 i : ℕ) (z : Vec 2) :
    ‖iteratedFDeriv ℝ i (fun y : Vec 2 => y 0 ^ b1 * y 1 ^ b2) z‖ ≤
      2 ^ i * ((b1.factorial : ℝ) * (b2.factorial : ℝ)) * (1 + ‖z‖) ^ (b1 + b2) := by
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => y 0 ^ b1) := by fun_prop
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => y 1 ^ b2) := by fun_prop
  refine (norm_iteratedFDeriv_mul_le hf hg z (nat_le_top i)).trans ?_
  have hterm : ∀ j ∈ Finset.range (i + 1),
      (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j (fun y : Vec 2 => y 0 ^ b1) z‖ *
        ‖iteratedFDeriv ℝ (i - j) (fun y : Vec 2 => y 1 ^ b2) z‖ ≤
      (i.choose j : ℝ) * ((b1.factorial : ℝ) * (b2.factorial : ℝ) * (1 + ‖z‖) ^ (b1 + b2)) := by
    intro j _
    have h1 := coord_pow_deriv_bound 0 b1 j z
    have h2 := coord_pow_deriv_bound 1 b2 (i - j) z
    have : ‖iteratedFDeriv ℝ j (fun y : Vec 2 => y 0 ^ b1) z‖ *
        ‖iteratedFDeriv ℝ (i - j) (fun y : Vec 2 => y 1 ^ b2) z‖ ≤
        (b1.factorial : ℝ) * (1 + ‖z‖) ^ b1 * ((b2.factorial : ℝ) * (1 + ‖z‖) ^ b2) :=
      mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    calc (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j (fun y : Vec 2 => y 0 ^ b1) z‖ *
          ‖iteratedFDeriv ℝ (i - j) (fun y : Vec 2 => y 1 ^ b2) z‖
        = (i.choose j : ℝ) * (‖iteratedFDeriv ℝ j (fun y : Vec 2 => y 0 ^ b1) z‖ *
          ‖iteratedFDeriv ℝ (i - j) (fun y : Vec 2 => y 1 ^ b2) z‖) := by ring
      _ ≤ (i.choose j : ℝ) * ((b1.factorial : ℝ) * (1 + ‖z‖) ^ b1 *
          ((b2.factorial : ℝ) * (1 + ‖z‖) ^ b2)) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by rw [pow_add]; ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
  push_cast
  linarith

theorem qfun_contDiff (ϖ : ℝ) (β : ℕ × ℕ) (R : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (qfun ϖ β R) := by
  unfold qfun
  exact contDiff_const.mul ((by fun_prop : ContDiff ℝ (⊤ : ℕ∞)
    (fun y : Vec 2 => y 0 ^ β.1 * y 1 ^ β.2)).mul (chiR_contDiff R))

theorem qfun_deriv_bound (β : ℕ × ℕ) (i : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ϖ R : ℝ), 1 ≤ R → 0 < ϖ → ϖ ≤ 1 → ∀ z : Vec 2,
      ‖iteratedFDeriv ℝ i (qfun ϖ β R) z‖ ≤ C * (1 + ϖ * ‖z‖) ^ (β.1 + β.2) := by
  choose Bc hBc0 hBc using chiR_deriv_bound
  set d : ℕ := β.1 + β.2 with hd
  set P : ℝ := ((β.1.factorial : ℝ) * (β.2.factorial : ℝ)) with hP
  have hPpos : 0 < P := by
    have h1 : (0 : ℝ) < β.1.factorial := by exact_mod_cast Nat.factorial_pos _
    have h2 : (0 : ℝ) < β.2.factorial := by exact_mod_cast Nat.factorial_pos _
    exact mul_pos h1 h2
  refine ⟨∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (2 ^ j) * Bc (i - j), ?_, ?_⟩
  · exact Finset.sum_nonneg fun j _ => by have := hBc0 (i - j); positivity
  intro ϖ R hR hϖ hϖ1 z
  have hmono : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => y 0 ^ β.1 * y 1 ^ β.2) := by fun_prop
  have hq : qfun ϖ β R = (ϖ ^ d / P) • (fun y : Vec 2 => (y 0 ^ β.1 * y 1 ^ β.2) * chiR R y) := by
    funext y
    simp only [qfun, Pi.smul_apply, smul_eq_mul, hd, hP]
    push_cast
    ring
  rw [hq, iteratedFDeriv_const_smul_apply
    ((hmono.mul (chiR_contDiff R)).contDiffAt.of_le (nat_le_top i)), norm_smul]
  have hLeib := norm_iteratedFDeriv_mul_le hmono (chiR_contDiff R) z (n := i) (nat_le_top i)
  have hsum : ‖iteratedFDeriv ℝ i (fun y : Vec 2 => (y 0 ^ β.1 * y 1 ^ β.2) * chiR R y) z‖ ≤
      (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (2 ^ j) * Bc (i - j)) *
        (P * (1 + ‖z‖) ^ d) := by
    refine hLeib.trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j hj => ?_
    have h1 := monomial_deriv_bound β.1 β.2 j z
    have h2 := hBc (i - j) R hR z
    have h3 : (2 : ℝ) ^ j * P * (1 + ‖z‖) ^ d ≥ ‖iteratedFDeriv ℝ j
        (fun y : Vec 2 => y 0 ^ β.1 * y 1 ^ β.2) z‖ := by
      simpa [hd, hP] using h1
    calc (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j (fun y : Vec 2 => y 0 ^ β.1 * y 1 ^ β.2) z‖ *
          ‖iteratedFDeriv ℝ (i - j) (chiR R) z‖
        ≤ (i.choose j : ℝ) * ((2 : ℝ) ^ j * P * (1 + ‖z‖) ^ d) * Bc (i - j) := by
          have := hBc0 (i - j)
          gcongr
      _ = _ := by ring
  have hRp : 0 ≤ ϖ ^ d / P := by positivity
  rw [Real.norm_of_nonneg hRp]
  have hϖd : ϖ ^ d * (1 + ‖z‖) ^ d ≤ (1 + ϖ * ‖z‖) ^ d := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ d
    nlinarith [norm_nonneg z]
  calc ϖ ^ d / P * ‖iteratedFDeriv ℝ i (fun y : Vec 2 => (y 0 ^ β.1 * y 1 ^ β.2) * chiR R y) z‖
      ≤ ϖ ^ d / P * ((∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (2 ^ j) * Bc (i - j)) *
        (P * (1 + ‖z‖) ^ d)) := mul_le_mul_of_nonneg_left hsum hRp
    _ = (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (2 ^ j) * Bc (i - j)) *
        (ϖ ^ d * (1 + ‖z‖) ^ d) := by field_simp
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left hϖd ?_
        exact Finset.sum_nonneg fun j _ => by have := hBc0 (i - j); positivity

theorem norm_sq_le_coords (z : Vec 2) : ‖z‖ ^ 2 ≤ z 0 ^ 2 + z 1 ^ 2 := by
  have hr : 0 ≤ Real.sqrt (z 0 ^ 2 + z 1 ^ 2) := Real.sqrt_nonneg _
  have hle : ‖z‖ ≤ Real.sqrt (z 0 ^ 2 + z 1 ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg hr).2 fun i => ?_
    rw [Real.norm_eq_abs]
    refine Real.abs_le_sqrt ?_
    fin_cases i
    · simp; nlinarith [sq_nonneg (z 1)]
    · simp; nlinarith [sq_nonneg (z 0)]
  calc ‖z‖ ^ 2 ≤ Real.sqrt (z 0 ^ 2 + z 1 ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = z 0 ^ 2 + z 1 ^ 2 := Real.sq_sqrt (by positivity)

theorem one_add_mul_norm_le (ϖ : ℝ) (z : Vec 2) :
    1 + ϖ * ‖z‖ ≤ 2 * wbase ϖ z ^ ((1 : ℝ) / 2) := by
  have hw := wbase_pos ϖ z
  have hs : wbase ϖ z ^ ((1 : ℝ) / 2) = Real.sqrt (wbase ϖ z) := (Real.sqrt_eq_rpow _).symm
  rw [hs]
  have hn := norm_sq_le_coords z
  have hsq : (1 + |ϖ| * ‖z‖) ^ 2 ≤ (2 * Real.sqrt (wbase ϖ z)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hw.le]
    unfold wbase
    have : (|ϖ| * ‖z‖) ^ 2 ≤ ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2) := by
      rw [mul_pow, sq_abs]
      exact mul_le_mul_of_nonneg_left hn (sq_nonneg _)
    nlinarith [sq_nonneg (1 - |ϖ| * ‖z‖)]
  have h2 : 1 + |ϖ| * ‖z‖ ≤ 2 * Real.sqrt (wbase ϖ z) :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).1 hsq
  calc 1 + ϖ * ‖z‖ ≤ 1 + |ϖ| * ‖z‖ := by
        have := le_abs_self ϖ
        nlinarith [norm_nonneg z]
    _ ≤ _ := h2

theorem qfun_weight_bound (n : ℕ) (β : ℕ × ℕ) (hβ : β.1 + β.2 ≤ n) (i : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ϖ R : ℝ), 1 ≤ R → 0 < ϖ → ϖ ≤ 1 → ∀ z : Vec 2,
      ‖iteratedFDeriv ℝ i (qfun ϖ β R) z‖ ≤ C * wbase ϖ z ^ ((n : ℝ) / 2) := by
  obtain ⟨C0, hC0, hC⟩ := qfun_deriv_bound β i
  refine ⟨C0 * 2 ^ (β.1 + β.2), by positivity, fun ϖ R hR hϖ hϖ1 z => ?_⟩
  refine (hC ϖ R hR hϖ hϖ1 z).trans ?_
  have h1 := one_add_mul_norm_le ϖ z
  have hw := wbase_one_le ϖ z
  have h2 : (1 + ϖ * ‖z‖) ^ (β.1 + β.2) ≤ 2 ^ (β.1 + β.2) * wbase ϖ z ^ ((n : ℝ) / 2) := by
    calc (1 + ϖ * ‖z‖) ^ (β.1 + β.2)
        ≤ (2 * wbase ϖ z ^ ((1 : ℝ) / 2)) ^ (β.1 + β.2) :=
          pow_le_pow_left₀ (by have := norm_nonneg z; positivity) h1 _
      _ = 2 ^ (β.1 + β.2) * wbase ϖ z ^ (((β.1 + β.2 : ℕ) : ℝ) / 2) := by
          rw [mul_pow, ← Real.rpow_natCast (wbase ϖ z ^ ((1 : ℝ) / 2)),
            ← Real.rpow_mul (wbase_pos ϖ z).le]
          congr 2
          ring
      _ ≤ 2 ^ (β.1 + β.2) * wbase ϖ z ^ ((n : ℝ) / 2) := by
          refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hw ?_) (by positivity)
          have : ((β.1 + β.2 : ℕ) : ℝ) ≤ n := by exact_mod_cast hβ
          linarith
  calc C0 * (1 + ϖ * ‖z‖) ^ (β.1 + β.2)
      ≤ C0 * (2 ^ (β.1 + β.2) * wbase ϖ z ^ ((n : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left h2 hC0
    _ = _ := by ring

end AVRegularity.CycleWords.Seam.NegLowBand
end

section
open Homogenization MeasureTheory
open scoped SchwartzMap
namespace AVRegularity.CycleWords.Seam

/-! The cutoff kernel moments at the slow weight scale have the required dilation price. -/

/-- Absolute kernel moment with the polynomial translation price of the tests. -/
def cutoffWeightedMoment (κ : Vec 2 → ℝ) (s : ℝ) (N p : ℕ) : ℝ :=
  ∫ y, ‖κ y‖ * ‖y‖ ^ N * (2 * cutoffBracket s y) ^ p

theorem cutoffWeightedMoment_nonneg (κ : Vec 2 → ℝ) (s : ℝ) (N p : ℕ) :
    0 ≤ cutoffWeightedMoment κ s N p := by
  apply integral_nonneg
  intro y
  have hq : 0 ≤ 2 * cutoffBracket s y := by linarith only [cutoffBracket_one_le s y]
  exact mul_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _))
    (pow_nonneg hq _)

/-- Every weighted moment of a Schwartz kernel is finite. -/
theorem cutoff_schwartz_weightedMoment_integrable (κ : 𝓢(Vec 2, ℝ)) (s : ℝ) (N p : ℕ) :
    Integrable (fun y => ‖κ y‖ * ‖y‖ ^ N * (2 * cutoffBracket s y) ^ p) := by
  let q := fun y : Vec 2 => (2 * cutoffBracket s y) ^ p
  have h0 : (fun y : Vec 2 => y 0).HasTemperateGrowth :=
    (ContinuousLinearMap.proj (0 : Fin 2) : Vec 2 →L[ℝ] ℝ).hasTemperateGrowth
  have h1 : (fun y : Vec 2 => y 1).HasTemperateGrowth :=
    (ContinuousLinearMap.proj (1 : Fin 2) : Vec 2 →L[ℝ] ℝ).hasTemperateGrowth
  have hq : q.HasTemperateGrowth :=
    ((Function.HasTemperateGrowth.const (2 : ℝ)).mul
      ((Function.HasTemperateGrowth.const (1 : ℝ)).add
        ((Function.HasTemperateGrowth.const (s ^ 2)).mul ((h0.pow 2).add (h1.pow 2))))).pow p
  have hi := (SchwartzMap.smulLeftCLM ℝ q κ).integrable_pow_mul volume N
  have he (y : Vec 2) : ‖y‖ ^ N * ‖SchwartzMap.smulLeftCLM ℝ q κ y‖ =
      ‖κ y‖ * ‖y‖ ^ N * (2 * cutoffBracket s y) ^ p := by
    rw [SchwartzMap.smulLeftCLM_apply_apply hq, norm_smul,
      Real.norm_of_nonneg (show 0 ≤ q y by
        dsimp only [q]; exact pow_nonneg (by linarith only [cutoffBracket_one_le s y]) _)]
    dsimp only [q]
    ring
  simpa only [he] using hi

theorem cutoffBracket_scaled_le (s a : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a)
    (hsa : s * a ≤ 1) (y : Vec 2) : cutoffBracket s (a • y) ≤ cutoffBracket 1 y := by
  have hp : (s * a) ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (mul_nonneg hs ha) hsa 2
  have hm := mul_le_mul_of_nonneg_right hp (add_nonneg (sq_nonneg (y 0)) (sq_nonneg (y 1)))
  dsimp only [cutoffBracket, Pi.smul_apply, smul_eq_mul]
  nlinarith only [hm]

/-- Dilation costs exactly `a^N` when the translated-test weight has scale at most one. -/
theorem cutoffWeightedMoment_dilation_le (m : Vec 2 → ℝ) (R : ℝ)
    (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0)
    (hsm : ContDiff ℝ (⊤ : ℕ∞) m) (s a : ℝ) (hs : 0 ≤ s) (ha : 0 < a)
    (hsa : s * a ≤ 1) (N p : ℕ) :
    cutoffWeightedMoment (cutoffKernel (fun ξ => m (a • ξ))) s N p ≤
      a ^ N * cutoffWeightedMoment (cutoffKernel m) 1 N p := by
  let K := seamRealCutoffSchwartz m R hm hsm
  let H := fun y : Vec 2 => ‖cutoffKernel m y‖ * ‖a • y‖ ^ N *
    (2 * cutoffBracket s (a • y)) ^ p
  let B := fun y : Vec 2 => ‖cutoffKernel m y‖ * ‖y‖ ^ N * (2 * cutoffBracket 1 y) ^ p
  have hB : Integrable B := by
    simpa only [B, K, seamRealCutoffSchwartz_eq] using
      cutoff_schwartz_weightedMoment_integrable K 1 N p
  have hb (y : Vec 2) : H y ≤ a ^ N * B y := by
    have hprice := pow_le_pow_left₀
      (show 0 ≤ 2 * cutoffBracket s (a • y) by linarith only [cutoffBracket_one_le s (a • y)])
      (mul_le_mul_of_nonneg_left (cutoffBracket_scaled_le s a hs ha.le hsa y) (by norm_num)) p
    dsimp only [H, B]
    rw [norm_smul, Real.norm_of_nonneg ha.le, mul_pow]
    exact (mul_le_mul_of_nonneg_left hprice (by positivity)).trans_eq (by ring)
  have hH : Integrable H := by
    apply Integrable.mono' (hB.const_mul (a ^ N))
    · have hc : Continuous H := by
        have hKc : Continuous (cutoffKernel m) :=
          (seamCutoffKernel_contDiff m R hm hsm.continuous).continuous
        dsimp only [H]
        unfold cutoffBracket
        fun_prop
      exact hc.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (show 0 ≤ H y by
          dsimp only [H]
          exact mul_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _))
            (pow_nonneg (by linarith only [cutoffBracket_one_le s (a • y)]) _))]
        exact hb y
  have he (y : Vec 2) :
      ‖cutoffKernel (fun ξ => m (a • ξ)) y‖ * ‖y‖ ^ N * (2 * cutoffBracket s y) ^ p =
        |(a ^ 2)⁻¹| * H (a⁻¹ • y) := by
    rw [seamCutoffKernel_dilation m a ha.ne', norm_mul,
      Real.norm_of_nonneg (abs_nonneg _)]
    dsimp only [H]
    rw [smul_inv_smul₀ ha.ne']
    ring
  unfold cutoffWeightedMoment
  simp_rw [he]
  rw [integral_const_mul, Measure.integral_comp_smul (volume : Measure (Vec 2)) H a⁻¹]
  have hdim : Module.finrank ℝ (Vec 2) = 2 := by simp [Vec]
  rw [hdim]
  simp only [smul_eq_mul, inv_pow, inv_inv]
  rw [← mul_assoc, ← abs_mul, inv_mul_cancel₀ (pow_ne_zero 2 ha.ne'), abs_one, one_mul]
  exact (integral_mono hH (hB.const_mul (a ^ N)) hb).trans_eq (integral_const_mul _ _)

theorem cutoff_radial_norm_smul (a : ℝ) (ha : 0 ≤ a) (ξ : Vec 2) :
    Real.sqrt (vecDot (a • ξ) (a • ξ)) = a * Real.sqrt (vecDot ξ ξ) := by
  have he : vecDot (a • ξ) (a • ξ) = a ^ 2 * vecDot ξ ξ := by
    unfold vecDot
    simp only [Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two]
    ring
  rw [he, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]

/-- Smoothness, radial support and flatness of the scaled multiplier. -/
theorem cutoff_dilation_data (m : Vec 2 → ℝ) (R : ℝ)
    (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0)
    (hs : ContDiff ℝ (⊤ : ℕ∞) m)
    (hflat : ∃ ε : ℝ, 0 < ε ∧ ∀ ξ, Real.sqrt (vecDot ξ ξ) ≤ ε → m ξ = 1)
    (a : ℝ) (ha : 0 < a) :
    ContDiff ℝ (⊤ : ℕ∞) (fun ξ => m (a • ξ)) ∧
    (∀ ξ, R / a ≤ Real.sqrt (vecDot ξ ξ) → m (a • ξ) = 0) ∧
    (∃ ε : ℝ, 0 < ε ∧ ∀ ξ, Real.sqrt (vecDot ξ ξ) ≤ ε → m (a • ξ) = 1) := by
  refine ⟨hs.comp (a • ContinuousLinearMap.id ℝ (Vec 2)).contDiff, ?_, ?_⟩
  · intro ξ hξ
    apply hm
    rw [cutoff_radial_norm_smul a ha.le]
    simpa only [mul_comm] using (div_le_iff₀ ha).mp hξ
  · obtain ⟨ε, hε, hεm⟩ := hflat
    refine ⟨ε / a, div_pos hε ha, ?_⟩
    intro ξ hξ
    apply hεm
    rw [cutoff_radial_norm_smul a ha.le]
    simpa only [mul_comm] using (le_div_iff₀ ha).mp hξ

/-- The ratio between the weight and cutoff scales is the reciprocal square root of `S`. -/
theorem cutoff_scale_ratio (η S s : ℝ) (hη : 0 < η)
    (hs : s = Real.sqrt (η / S)) : s * (Real.sqrt η)⁻¹ = (Real.sqrt S)⁻¹ := by
  have hroot : Real.sqrt η ≠ 0 := (Real.sqrt_pos.mpr hη).ne'
  rw [hs, Real.sqrt_div hη.le]
  field_simp

theorem cutoff_scale_relations (η S s : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (hS : 1 ≤ S)
    (hs : s = Real.sqrt (η / S)) :
    0 < s ∧ s ≤ 1 ∧ 1 ≤ (Real.sqrt η)⁻¹ ∧ s * (Real.sqrt η)⁻¹ ≤ 1 := by
  have hSp : 0 < S := zero_lt_one.trans_le hS
  have hroot : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have hsr : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr (div_pos hη hSp)
  have har : 1 ≤ (Real.sqrt η)⁻¹ := (one_le_inv₀ hroot).mpr (Real.sqrt_le_one.mpr hη1)
  have hrat : s * (Real.sqrt η)⁻¹ ≤ 1 := by
    rw [cutoff_scale_ratio η S s hη hs]
    exact (inv_le_one₀ (Real.sqrt_pos.mpr hSp)).mpr (Real.one_le_sqrt.mpr hS)
  have hs1 : s ≤ 1 := (by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left har hsr.le : s ≤ s * (Real.sqrt η)⁻¹).trans hrat
  exact ⟨hsr, hs1, har, hrat⟩

/-- The dilation and derivative-scale prices combine to precisely `S^{-N/2}`. -/
theorem cutoff_scale_power (η S s : ℝ) (hη : 0 < η) (hS : 1 ≤ S)
    (hs : s = Real.sqrt (η / S)) (N : ℕ) :
    (s * (Real.sqrt η)⁻¹) ^ N = S ^ (-(N : ℝ) / 2) := by
  have hSp : 0 < S := zero_lt_one.trans_le hS
  rw [cutoff_scale_ratio η S s hη hs, Real.sqrt_eq_rpow,
    ← Real.rpow_neg hSp.le, ← Real.rpow_natCast, ← Real.rpow_mul hSp.le]
  congr 1
  ring

end AVRegularity.CycleWords.Seam
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! Derivative subarrays and the large-scale test norm in the cutoff-complement estimate. -/

/-- A fixed prefix of the full word array can only decrease its Euclidean size. -/
theorem cutoff_word_subarray_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N a : ℕ} (β : DerivativeWord2 N) (φ : Vec 2 → E) (z : Vec 2) :
    Real.sqrt (∑ w : DerivativeWord2 a, ‖orderedDerivative w (orderedDerivative β φ) z‖ ^ 2) ≤
      Real.sqrt (∑ w : DerivativeWord2 (N + a), ‖orderedDerivative w φ z‖ ^ 2) := by
  classical
  let e := fun w : DerivativeWord2 a => Fin.append β w
  have he : Function.Injective e := by
    intro w w' hh
    funext i
    have hi := congrFun hh (i.natAdd N)
    simpa only [e, Fin.append_right] using hi
  apply Real.sqrt_le_sqrt
  simp_rw [← orderedDerivative_append]
  change (∑ w : DerivativeWord2 a, ‖orderedDerivative (e w) φ z‖ ^ 2) ≤ _
  rw [← Finset.sum_image (f := fun w : DerivativeWord2 (N + a) =>
    ‖orderedDerivative w φ z‖ ^ 2) (s := Finset.univ) (g := e)
    (fun w _ w' _ hh => he hh)]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro w _ _
  exact sq_nonneg _

/-- Component `L²` sizes of a derivative test are bounded by the retained higher-order array. -/
theorem cutoff_word_subarray_eLpNorm_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {N a : ℕ} (β : DerivativeWord2 N) (φ : Vec 2 → E)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (p s : ℝ) :
    eLpNorm (fun z => cutoffBracket s z ^ (p / 2) *
      Real.sqrt (∑ w : DerivativeWord2 a, ‖orderedDerivative w (orderedDerivative β φ) z‖ ^ 2))
      2 volume ≤
    eLpNorm (fun z => cutoffBracket s z ^ (p / 2) *
      Real.sqrt (∑ w : DerivativeWord2 (N + a), ‖orderedDerivative w φ z‖ ^ 2)) 2 volume := by
  have hβ : ContDiff ℝ (a : ℕ∞) (orderedDerivative β φ) :=
    ChartTransport.contDiff_orderedDerivative (p := a) β (hφ.of_le (by simp))
  apply eLpNorm_mono_real
    ((Assembly.weight_continuous s p).aestronglyMeasurable.mul
      (Real.continuous_sqrt.comp_aestronglyMeasurable
        (Finset.aestronglyMeasurable_fun_sum _ fun w _ =>
          ((Assembly.orderedDerivative_continuous w hβ).norm.pow 2).aestronglyMeasurable)))
  intro z
  change ‖cutoffBracket s z ^ (p / 2) *
    Real.sqrt (∑ w : DerivativeWord2 a, ‖orderedDerivative w (orderedDerivative β φ) z‖ ^ 2)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (Real.rpow_nonneg (by linarith only [cutoffBracket_one_le s z]) _) (Real.sqrt_nonneg _))]
  exact mul_le_mul_of_nonneg_left (cutoff_word_subarray_norm_le β φ z)
    (Real.rpow_nonneg (by linarith only [cutoffBracket_one_le s z]) _)

/-- The inverse-mass `L²` size of one order of the whole test family. -/
def cutoffJetSize {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] (π : ι → ℝ) (p s : ℝ)
    (φ : ∀ v, Vec 2 → h v) (a : ℕ) : ℝ≥0∞ :=
  (∑ v, ENNReal.ofReal ((π v)⁻¹) * eLpNorm (fun z => cutoffBracket s z ^ (p / 2) *
    Real.sqrt (∑ w : DerivativeWord2 a, ‖orderedDerivative w (φ v) z‖ ^ 2)) 2 volume ^ 2) ^
      (1 / 2 : ℝ)

theorem cutoff_weightedJetNorm_eq_sum {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
    (π : ι → ℝ) (p s r : ℝ) (φ : ∀ v, Vec 2 → h v) (k : ℕ) :
    weightedJetNorm π p k s r (fun v _ w z => orderedDerivative w (φ v) z) =
      ∑ a ∈ Finset.range (k + 1), ENNReal.ofReal (r ^ a / (a.factorial : ℝ)) *
        cutoffJetSize π p s φ a := rfl

theorem cutoffJetSize_derivative_le {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    (π : ι → ℝ) (p s : ℝ) {N : ℕ} (β : DerivativeWord2 N)
    (φ : ∀ v, Vec 2 → h v) (hφ : ∀ v, ContDiff ℝ (⊤ : ℕ∞) (φ v)) (a : ℕ) :
    cutoffJetSize π p s (fun v => orderedDerivative β (φ v)) a ≤
      cutoffJetSize π p s φ (N + a) := by
  unfold cutoffJetSize
  gcongr with v
  exact cutoff_word_subarray_eLpNorm_le β (φ v) (hφ v) p s

/-- A retained higher-order component gains the reciprocal `N`th power of the large scale. -/
theorem cutoffJetSize_le_largeScale {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
    (π : ι → ℝ) (p s R : ℝ) (hR : 1 ≤ R) (φ : ∀ v, Vec 2 → h v)
    (N d M : ℕ) (hNd : N ≤ d) (hdM : d ≤ M) :
    cutoffJetSize π p s φ d ≤ ENNReal.ofReal ((M.factorial : ℝ) * R⁻¹ ^ N) *
      weightedJetNorm π p M s R (fun v _ w z => orderedDerivative w (φ v) z) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hfactM : 0 < (M.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos M
  have hfactd : 0 < (d.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos d
  have hcoeff : R ^ N / (M.factorial : ℝ) ≤ R ^ d / (d.factorial : ℝ) :=
    div_le_div₀ (pow_nonneg hRp.le _) (pow_le_pow_right₀ hR hNd) hfactd
      (by exact_mod_cast Nat.factorial_le hdM)
  have hterm : ENNReal.ofReal (R ^ N / (M.factorial : ℝ)) * cutoffJetSize π p s φ d ≤
      weightedJetNorm π p M s R (fun v _ w z => orderedDerivative w (φ v) z) := by
    rw [cutoff_weightedJetNorm_eq_sum]
    exact (mul_le_mul' (ENNReal.ofReal_le_ofReal hcoeff) le_rfl).trans
      (Finset.single_le_sum (f := fun a => ENNReal.ofReal (R ^ a / (a.factorial : ℝ)) *
        cutoffJetSize π p s φ a) (fun _ _ => zero_le)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hdM)))
  have hA : 0 ≤ (M.factorial : ℝ) * R⁻¹ ^ N := by positivity
  have hc : ENNReal.ofReal ((M.factorial : ℝ) * R⁻¹ ^ N) *
      ENNReal.ofReal (R ^ N / (M.factorial : ℝ)) = 1 := by
    rw [← ENNReal.ofReal_mul hA]
    have he : (M.factorial : ℝ) * R⁻¹ ^ N * (R ^ N / (M.factorial : ℝ)) = 1 := by
      rw [inv_pow]
      field_simp
    rw [he, ENNReal.ofReal_one]
  calc
    _ = ENNReal.ofReal ((M.factorial : ℝ) * R⁻¹ ^ N) *
        (ENNReal.ofReal (R ^ N / (M.factorial : ℝ)) * cutoffJetSize π p s φ d) := by
      rw [← mul_assoc, hc, one_mul]
    _ ≤ _ := mul_le_mul' le_rfl hterm

/-- The derivative test at unit scale is small in the large-scale higher-order norm. -/
theorem cutoff_derivative_test_largeScale_le {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    (π : ι → ℝ) (p s R : ℝ) (hR : 1 ≤ R) (N k : ℕ) (β : DerivativeWord2 N)
    (φ : ∀ v, Vec 2 → h v) (hφ : ∀ v, ContDiff ℝ (⊤ : ℕ∞) (φ v)) :
    weightedJetNorm π p k s 1 (fun v _ w z => orderedDerivative w (orderedDerivative β (φ v)) z) ≤
      ENNReal.ofReal (((k + 1 : ℕ) : ℝ) * ((N + k).factorial : ℝ) * R⁻¹ ^ N) *
        weightedJetNorm π p (N + k) s R (fun v _ w z => orderedDerivative w (φ v) z) := by
  let B := weightedJetNorm π p (N + k) s R (fun v _ w z => orderedDerivative w (φ v) z)
  let A : ℝ := ((N + k).factorial : ℝ) * R⁻¹ ^ N
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  rw [cutoff_weightedJetNorm_eq_sum]
  calc
    _ ≤ ∑ _a ∈ Finset.range (k + 1), ENNReal.ofReal A * B := by
      apply Finset.sum_le_sum
      intro a ha
      have hac : a ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
      have hc : ENNReal.ofReal (1 ^ a / (a.factorial : ℝ)) ≤ 1 := by
        rw [one_pow, ← ENNReal.ofReal_one]
        apply ENNReal.ofReal_le_ofReal
        apply (div_le_one (by exact_mod_cast Nat.factorial_pos a)).mpr
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero a)
      calc
        _ ≤ cutoffJetSize π p s (fun v => orderedDerivative β (φ v)) a := by
          simpa only [one_mul] using mul_le_mul' hc (le_refl (cutoffJetSize π p s
            (fun v => orderedDerivative β (φ v)) a))
        _ ≤ cutoffJetSize π p s φ (N + a) := cutoffJetSize_derivative_le π p s β φ hφ a
        _ ≤ _ := cutoffJetSize_le_largeScale π p s R hR φ N (N + a) (N + k)
          (Nat.le_add_right _ _) (Nat.add_le_add_left hac N)
    _ = _ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      change ((k + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal A * B) =
        ENNReal.ofReal (((k + 1 : ℕ) : ℝ) * ((N + k).factorial : ℝ) * R⁻¹ ^ N) * B
      rw [← ENNReal.ofReal_natCast, ← mul_assoc, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      exact congrArg (fun c : ℝ => ENNReal.ofReal c * B)
        (mul_assoc ((k + 1 : ℕ) : ℝ) ((N + k).factorial : ℝ) (R⁻¹ ^ N)).symm

end AVRegularity.CycleWords.Seam
end
