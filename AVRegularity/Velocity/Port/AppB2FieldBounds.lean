-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Velocity.Port.MaterialGoalSource
import AVenhance.Infra.Flow.JointSmoothFromFixedStart
public import AVenhance.Infra.FaaDiBruno.TransportODEApplications
public import Mathlib.Algebra.Order.Archimedean.Real.Hom
import AVenhance.Infra.Construction.StreamAdmissible
import AVenhance.Infra.FaaDiBruno.Composition
import AVenhance.Infra.Flow.Laws
import AVenhance.Infra.Flow.SmoothField
import AVenhance.Statements.FlowDefs.FlowIsFlow
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Monotonicity.Lemmas

section
@[expose] public section
namespace AVRegularity.Velocity.Port.Section2Induction

/-! Section 2 spatial stream summation for the OC scales.

The seminorm telescoping and high-order scale-gap arguments are the checked
generic port. As in the upstream proof, they consume the all-order
increment estimate as a separate input; this module does not assert that the
stream recursion supplies it.
-/

open Homogenization AVenhance

/-- All-order stream increment bounds at the OC recursion radii. -/
abbrev StreamIncrementBounds {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) (Φ : ℕ → ℝ → Vec 2 → ℝ) : Prop :=
  AVRegularity.Velocity.Jets.JetIncrementBounds D Φ

/-- The exact Section 2 spatial stream induction hypothesis at one level.
This is the source `e.indyhyp` bound, with the OC radius and jet-size
sequences substituted. -/
def Section2StreamInductionHypothesis {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (m : ℕ) : Prop :=
  ∀ t : ℝ, ∀ n : ℕ, 2 ≤ n →
    FaaDiBruno.snorm (Φ m t) n (D.radius m) ≤
      ENNReal.ofReal (D.jetSize m * (D.radius m)⁻¹ ^ 2 *
        (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3))

/-- The stream-regularity estimates of the `AVenhance` library with the OC scales substituted.
This is an explicit induction input, separate from the increment estimate of the recursion. -/
def OCStreamRegularityBounds {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) (C : ℝ)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ t : ℝ,
    (∀ n : ℕ,
      AVenhance.barNorm n (2 ^ 7 * (D.epsilon m)⁻¹)
        (Φ m t - Φ (m - 1) t) ≤
        ENNReal.ofReal (10 * D.epsilon m ^ (1 + α))) ∧
    (∀ n : ℕ, 2 ≤ n →
      AVenhance.barNorm n (2 ^ 8 * (D.epsilon m)⁻¹) (Φ m t) ≤
        ENNReal.ofReal (2 ^ 5 * D.velocityAmplitude m * D.epsilon m ^ 2 *
          (((n : ℝ) + 2) ^ 2 / ((n : ℝ) + 1) ^ 3))) ∧
    (∀ n : ℕ, n ≤ 1 →
      AVenhance.barNorm n (C * (D.epsilon m)⁻¹) (Φ m t) ≤
        ENNReal.ofReal (C * D.epsilon m ^ n))

/-- The high-order source bound follows from the abstract OC scale gap,
conditional on the increment jets. -/
theorem high_order_stream_bound_of_increment_bounds
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦzero : ∀ t x, Φ 0 t x = 0)
    (hΦsmooth : ∀ m t, ContDiff ℝ (⊤ : ℕ∞) (Φ m t))
    (hinc : StreamIncrementBounds D Φ) (m : ℕ)
    (t : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    AVenhance.barNorm n (2 ^ 7 * (D.epsilon m)⁻¹) (Φ m t) ≤
      ENNReal.ofReal (20 * D.epsilon m ^ (1 + α)) :=
  AVRegularity.Velocity.Jets.barNorm_high_order_bound_of_increment_bounds
    D hΦzero hΦsmooth hinc m t n hn

private theorem low_order_geometric_sum (m : ℕ) :
    (∑ j ∈ Finset.range (m + 1), (1 / 128 : ℝ) ^ j) ≤ 128 / 127 := by
  have hsum := AVRegularity.Velocity.Port.Scalars.sum_geometric_le
    (by norm_num : (0 : ℝ) ≤ 1 / 128) (by norm_num : (1 / 128 : ℝ) < 1) (m + 1)
  have hden : 0 < 1 - (1 / 128 : ℝ) := by norm_num
  rw [show (1 - (1 / 128 : ℝ))⁻¹ = 128 / 127 by norm_num] at hsum
  exact hsum

private theorem epsilon_rpow_le_initial_geometric
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) {p : ℝ} (hp : 1 ≤ p) (j : ℕ) :
    D.epsilon j ^ p ≤ (1 / 128 : ℝ) ^ j := by
  have hgap := D.epsilon_gap_ratio j 0 (Nat.zero_le j)
  rw [D.epsilon_zero, div_one, Nat.sub_zero] at hgap
  have he : 0 < D.epsilon j := D.epsilon_pos j
  have hbase : D.epsilon j ^ p ≤ D.epsilon j :=
    (Real.rpow_le_rpow_of_exponent_ge he (D.epsilon_le_one j) hp).trans_eq
      (Real.rpow_one _)
  exact hbase.trans hgap

private theorem low_order_epsilon_power_sum
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) {p : ℝ} (hp : 0 < p) (m : ℕ) :
    (∑ j ∈ Finset.range (m + 1), D.epsilon j ^ p) ≤
      (1 - (1 / 128 : ℝ) ^ p)⁻¹ := by
  have hterm : ∀ j, D.epsilon j ^ p ≤ ((1 / 128 : ℝ) ^ p) ^ j := by
    intro j
    have hgap := D.epsilon_gap_ratio j 0 (Nat.zero_le j)
    rw [D.epsilon_zero, div_one, Nat.sub_zero] at hgap
    have hpow := Real.rpow_le_rpow (D.epsilon_pos j).le hgap hp.le
    have hrewrite : ((1 / 128 : ℝ) ^ j) ^ p =
        ((1 / 128 : ℝ) ^ p) ^ j := by
      rw [← Real.rpow_natCast (1 / 128 : ℝ) j,
        ← Real.rpow_natCast ((1 / 128 : ℝ) ^ p) j]
      calc
        ((1 / 128 : ℝ) ^ (j : ℝ)) ^ p =
            (1 / 128 : ℝ) ^ ((j : ℝ) * p) := by
          rw [← Real.rpow_mul (by norm_num : 0 ≤ (1 / 128 : ℝ))]
        _ = (1 / 128 : ℝ) ^ (p * (j : ℝ)) := by congr 1; ring
        _ = ((1 / 128 : ℝ) ^ p) ^ (j : ℝ) := by
          rw [Real.rpow_mul (by norm_num : 0 ≤ (1 / 128 : ℝ))]
    exact hpow.trans_eq hrewrite
  have hratioPos : 0 < (1 / 128 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) _
  have hratioLt : (1 / 128 : ℝ) ^ p < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) hp
  have hgeom := AVRegularity.Velocity.Port.Scalars.sum_geometric_le
    hratioPos.le hratioLt (m + 1)
  calc
    _ ≤ ∑ j ∈ Finset.range (m + 1), ((1 / 128 : ℝ) ^ p) ^ j :=
      Finset.sum_le_sum fun j _ => hterm j
    _ ≤ (1 - (1 / 128 : ℝ) ^ p)⁻¹ := hgeom

private theorem low_order_first_order_denominator
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) :
    (5 / 3 : ℝ) * α ≤ 1 - (1 / 128 : ℝ) ^ α := by
  have hlog : 4 ≤ Real.log (128 : ℝ) := by
    apply (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 128)).2
    have he : Real.exp (4 : ℝ) < 81 := by
      have h := pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos 1).le
        (by norm_num : (4 : ℕ) ≠ 0)
      rw [← Real.exp_nat_mul] at h
      norm_num at h
      exact h

    exact le_trans (le_of_lt he) (by norm_num)
  have hαthird : α ≤ 1 / 3 := by linarith [D.hαlt]
  have hlin : 1 + 4 * α ≤ Real.exp (α * Real.log (128 : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_left hlog D.hαpos.le
    have hExp := Real.add_one_le_exp (α * Real.log (128 : ℝ))
    linarith
  have hdenpos : 0 < 1 + 4 * α := by linarith [D.hαpos]
  have hinv := (inv_le_inv₀ (Real.exp_pos _) hdenpos).2 hlin
  have hrpow : (1 / 128 : ℝ) ^ α ≤ (1 + 4 * α)⁻¹ := by
    have hinvpow : (1 / 128 : ℝ) ^ α = (128 : ℝ) ^ (-α) := by
      rw [show (1 / 128 : ℝ) = (128 : ℝ)⁻¹ by norm_num,
        Real.inv_rpow (by norm_num : 0 ≤ (128 : ℝ)),
        Real.rpow_neg (by norm_num : 0 ≤ (128 : ℝ))]
    rw [hinvpow]
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 128)]
    have hlogmul : Real.log 128 * -α = -(α * Real.log 128) := by ring
    rw [hlogmul, Real.exp_neg]
    exact hinv
  have hfrac : (1 + 4 * α)⁻¹ ≤ 1 - (5 / 3 : ℝ) * α := by
    rw [← one_div]
    apply (div_le_iff₀ hdenpos).2
    have hnonneg := mul_nonneg D.hαpos.le (sub_nonneg.mpr hαthird)
    nlinarith
  linarith

/-- Zeroth and first order stream bounds obtained by summing the stream
increment scales. The source constant and its dependence on `α` are retained. -/
theorem low_order_stream_bounds_of_increment_bounds
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ)
    (hinc : StreamIncrementBounds D Φ) (m : ℕ) (t : ℝ) :
    let C : ℝ := 11 + 768 / α
    ∀ n : ℕ, n ≤ 1 →
      AVenhance.barNorm n (C * (D.epsilon m)⁻¹) (Φ m t) ≤
        ENNReal.ofReal (C * D.epsilon m ^ n) := by
  dsimp
  let C : ℝ := 11 + 768 / α
  let em : ℝ := D.epsilon m
  have hαpos : 0 < α := D.hαpos
  have hC : 0 < C := by dsimp [C]; positivity
  have hC1 : 1 ≤ C := by
    dsimp [C]
    have hnonneg : 0 ≤ 768 / α := by positivity
    linarith
  have hem : 0 < em := by dsimp [em]; exact D.epsilon_pos m
  have hS : 0 < C * em⁻¹ := by positivity
  have hΦzero : ∀ t x, Φ 0 t x = 0 := by
    intro t x
    have hzero := hseq.1
    change Φ 0 = (fun _ _ => 0) at hzero
    exact congrFun (congrFun hzero t) x
  have hΦsmooth : ∀ k t, ContDiff ℝ (⊤ : ℕ∞) (Φ k t) := by
    intro k t
    exact (AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq k).1.comp
      (contDiff_const.prodMk contDiff_id)
  have hbound (n : ℕ) :
      AVenhance.barNorm n (C * em⁻¹) (Φ m t) ≤
        ENNReal.ofReal (∑ j ∈ Finset.range m,
          (10 * D.epsilon (j + 1) ^ (1 + α)) *
            ((2 ^ 7 * (D.epsilon (j + 1))⁻¹) / (C * em⁻¹)) ^ n) :=
    AVRegularity.Velocity.Jets.barNorm_telescope_bound_of_increment_bounds
      D hΦzero hΦsmooth hinc m t n hS
  have hsumAlpha :
      (∑ j ∈ Finset.range m, D.epsilon (j + 1) ^ α) ≤
        ∑ j ∈ Finset.range (m + 1), D.epsilon j ^ α := by
    rw [Finset.sum_range_succ']
    exact le_add_of_nonneg_right (Real.rpow_nonneg (D.epsilon_pos 0).le α)
  have hsumAlphaBound :
      (∑ j ∈ Finset.range m, D.epsilon (j + 1) ^ α) ≤ 3 / (5 * α) := by
    have hsumAll := low_order_epsilon_power_sum D hαpos m
    have hden := low_order_first_order_denominator D
    have hdenpos : 0 < 1 - (1 / 128 : ℝ) ^ α := by
      have hsmall : (1 / 128 : ℝ) ^ α < 1 :=
        Real.rpow_lt_one (by norm_num) (by norm_num) D.hαpos
      linarith
    have hbound : (1 - (1 / 128 : ℝ) ^ α)⁻¹ ≤ 3 / (5 * α) := by
      have hbase : 0 < (5 / 3 : ℝ) * α := by positivity
      have hinv := (inv_le_inv₀ hdenpos hbase).2 hden
      calc
        (1 - (1 / 128 : ℝ) ^ α)⁻¹ ≤ ((5 / 3 : ℝ) * α)⁻¹ := hinv
        _ = 3 / (5 * α) := by field_simp
    calc
      _ ≤ ∑ j ∈ Finset.range (m + 1), D.epsilon j ^ α := hsumAlpha
      _ ≤ (1 - (1 / 128 : ℝ) ^ α)⁻¹ := hsumAll
      _ ≤ 3 / (5 * α) := hbound
  have hsumPower :
      (∑ j ∈ Finset.range (m + 1), D.epsilon j ^ (1 + α)) ≤ 128 / 127 := by
    calc
      _ ≤ ∑ j ∈ Finset.range (m + 1), (1 / 128 : ℝ) ^ j := by
        apply Finset.sum_le_sum
        intro j hj
        have hp : 1 ≤ 1 + α := by linarith
        exact epsilon_rpow_le_initial_geometric D hp j
      _ ≤ 128 / 127 := low_order_geometric_sum m
  have hsumZero :
      10 * (∑ j ∈ Finset.range m, D.epsilon (j + 1) ^ (1 + α)) ≤ 11 := by
    have hshift :
        (∑ j ∈ Finset.range m, D.epsilon (j + 1) ^ (1 + α)) ≤
          ∑ j ∈ Finset.range (m + 1), D.epsilon j ^ (1 + α) := by
      rw [Finset.sum_range_succ']
      exact le_add_of_nonneg_right (Real.rpow_nonneg (D.epsilon_pos 0).le _)
    have hraw := hshift.trans hsumPower
    have hnumeric : 10 * (128 / 127 : ℝ) ≤ 11 := by norm_num
    exact (mul_le_mul_of_nonneg_left hraw (by norm_num)).trans hnumeric
  have hpow0 :
      (∑ j ∈ Finset.range m,
        (10 * D.epsilon (j + 1) ^ (1 + α)) *
          ((2 ^ 7 * (D.epsilon (j + 1))⁻¹) / (C * em⁻¹)) ^ 0) =
        10 * (∑ j ∈ Finset.range m, D.epsilon (j + 1) ^ (1 + α)) := by
    simp only [pow_zero, mul_one]
    rw [← Finset.mul_sum]
  have hpow1 :
      (∑ j ∈ Finset.range m,
        (10 * D.epsilon (j + 1) ^ (1 + α)) *
          ((2 ^ 7 * (D.epsilon (j + 1))⁻¹) / (C * em⁻¹)) ^ 1) =
        (1280 / C) * em *
          (∑ j ∈ Finset.range m, D.epsilon (j + 1) ^ α) := by
    have hterm : ∀ j ∈ Finset.range m,
        (10 * D.epsilon (j + 1) ^ (1 + α)) *
            ((2 ^ 7 * (D.epsilon (j + 1))⁻¹) / (C * em⁻¹)) ^ 1 =
          (1280 / C) * em * D.epsilon (j + 1) ^ α := by
      intro j hj
      have he := D.epsilon_pos (j + 1)
      have hpow : D.epsilon (j + 1) ^ (1 + α) =
          D.epsilon (j + 1) * D.epsilon (j + 1) ^ α := by
        simpa [Real.rpow_one] using Real.rpow_add he (1 : ℝ) α
      calc
        _ = 10 * (D.epsilon (j + 1) * D.epsilon (j + 1) ^ α) *
            ((2 ^ 7 * (D.epsilon (j + 1))⁻¹) / (C * em⁻¹)) := by
              rw [pow_one, hpow]
        _ = (1280 / C) * em * D.epsilon (j + 1) ^ α := by
              field_simp [ne_of_gt hC, ne_of_gt hem, ne_of_gt he]
              ring
    calc
      _ = ∑ j ∈ Finset.range m,
          (1280 / C) * em * D.epsilon (j + 1) ^ α := by
            apply Finset.sum_congr rfl
            intro j hj
            exact hterm j hj
      _ = (1280 / C) * em *
          (∑ j ∈ Finset.range m, D.epsilon (j + 1) ^ α) := by
            rw [Finset.mul_sum]
  have hcoef : (1280 / C) * (3 / (5 * α)) ≤ C := by
    have hCsmall : 768 / α ≤ C := by dsimp [C]; linarith
    have hprod : 768 ≤ C * α := (div_le_iff₀ hαpos).mp hCsmall
    have hfrac : 768 / (C * α) ≤ 1 := by
      apply (div_le_iff₀ (mul_pos hC hαpos)).2
      linarith
    calc
      (1280 / C) * (3 / (5 * α)) = 768 / (C * α) := by
        field_simp [ne_of_gt hC, ne_of_gt hαpos]
        norm_num
      _ ≤ 1 := hfrac
      _ ≤ C := hC1
  intro n hn
  have hfin := hbound n
  by_cases hn0 : n = 0
  · subst n
    rw [hpow0] at hfin
    have hreal : 10 * (∑ j ∈ Finset.range m,
        D.epsilon (j + 1) ^ (1 + α)) ≤ C := by
      dsimp [C]
      have hCterm : 0 ≤ 768 / α := by positivity
      linarith [hsumZero]
    have hfinal := hfin.trans (ENNReal.ofReal_le_ofReal hreal)
    simpa [C, em, pow_zero] using hfinal
  · have hn1 : n = 1 := by omega
    subst n
    rw [hpow1] at hfin
    have hreal : (1280 / C) * em *
        (∑ j ∈ Finset.range m, D.epsilon (j + 1) ^ α) ≤ C * em := by
      calc
        _ ≤ ((1280 / C) * em) * (3 / (5 * α) : ℝ) := by
          exact mul_le_mul_of_nonneg_left hsumAlphaBound
            (mul_nonneg (by positivity) hem.le)
        _ ≤ C * em := by
          have hmul := mul_le_mul_of_nonneg_right hcoef hem.le
          nlinarith [hmul]
    have hfinal := hfin.trans (ENNReal.ofReal_le_ofReal hreal)
    simpa [C, em] using hfinal

end AVRegularity.Velocity.Port.Section2Induction
end
end

section
@[expose] public section
noncomputable section
open Homogenization AVenhance AVenhance.Infra.Construction
namespace AVRegularity.Velocity.Port.MaterialPullback

/-! Pulling material derivatives back along a flow turns them into ordinary
time derivatives. This is the all-order chain-rule interface for material
estimates. -/

def constructionJointScalar (F : ℝ → Vec 2 → ℝ) : ℝ × Vec 2 → ℝ :=
  fun p => F p.1 p.2

def constructionJointVector (b : ℝ → Vec 2 → Vec 2) : ℝ × Vec 2 → Vec 2 :=
  fun p => b p.1 p.2

def constructionSpatialInputCLM :
    Vec 2 →L[ℝ] (ℝ × Vec 2 × ℝ) :=
  (0 : Vec 2 →L[ℝ] ℝ).prod
    ((ContinuousLinearMap.id ℝ (Vec 2)).prod (0 : Vec 2 →L[ℝ] ℝ))

/-- The material derivative is the joint derivative in the space-time
direction `(1,b)`. -/
theorem constructionMaterialDerivative_eq_joint_fderiv
    {b : ℝ → Vec 2 → Vec 2} {F : ℝ → Vec 2 → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) (constructionJointScalar F)) (t : ℝ) (x : Vec 2) :
    constructionMaterialDerivative b F t x =
      fderiv ℝ (constructionJointScalar F) (t, x) (1, b t x) := by
  let H := constructionJointScalar F
  have hH := (hF.differentiable (by norm_num) (t, x)).hasFDerivAt
  have htimePath : HasDerivAt (fun r : ℝ => (r, x)) (1, (0 : Vec 2)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const (c := x) (x := t))
  have htime := hH.comp_hasDerivAt t htimePath
  have htime' : deriv (fun r : ℝ => F r x) t =
      fderiv ℝ H (t, x) (1, (0 : Vec 2)) := by
    simpa [H, constructionJointScalar, Function.comp_def] using htime.deriv
  have hspacePath := hasFDerivAt_prodMk_right
    (𝕜 := ℝ) (E := ℝ) (F := Vec 2) t x
  have hspace := hH.comp x hspacePath
  have hspace' : fderiv ℝ (F t) x =
      (fderiv ℝ H (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ (Vec 2)) := by
    simpa [H, constructionJointScalar, Function.comp_def] using hspace.fderiv
  change deriv (fun r : ℝ => F r x) t + fderiv ℝ (F t) x (b t x) = _
  rw [htime', hspace']
  change fderiv ℝ H (t, x) (1, (0 : Vec 2)) +
      fderiv ℝ H (t, x) (0, b t x) = _
  have hsplit : ((1 : ℝ), b t x) =
      (1, (0 : Vec 2)) + (0, b t x) := by
    ext <;> simp
  rw [← map_add]
  exact congrArg (fderiv ℝ H (t, x)) hsplit.symm

/-- Smooth space-time data give a smooth material derivative. -/
theorem constructionMaterialDerivative_joint_contDiff
    {b : ℝ → Vec 2 → Vec 2} {F : ℝ → Vec 2 → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) (constructionJointVector b))
    (hF : ContDiff ℝ (⊤ : ℕ∞) (constructionJointScalar F)) :
    ContDiff ℝ (⊤ : ℕ∞)
      (constructionJointScalar (constructionMaterialDerivative b F)) := by
  let H := constructionJointScalar F
  have hdf : ContDiff ℝ (⊤ : ℕ∞) (fun p => fderiv ℝ H p) :=
    hF.fderiv_right (by simp)
  have hb' : ContDiff ℝ (⊤ : ℕ∞) (constructionJointVector b) := hb
  have hv : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 => ((1 : ℝ), constructionJointVector b p)) :=
    contDiff_const.prodMk hb'
  have hresult := hdf.clm_apply hv
  have heq : constructionJointScalar (constructionMaterialDerivative b F) =
      fun p => fderiv ℝ H p ((1 : ℝ), constructionJointVector b p) := by
    funext p
    exact constructionMaterialDerivative_eq_joint_fderiv hF p.1 p.2
  rw [heq]
  exact hresult

/-- Every material iterate stays smooth when the velocity and the original
space-time profile are smooth. -/
theorem constructionMaterialIterate_joint_contDiff
    {b : ℝ → Vec 2 → Vec 2} {F : ℝ → Vec 2 → ℝ}
    (hb : ContDiff ℝ (⊤ : ℕ∞) (constructionJointVector b))
    (hF : ContDiff ℝ (⊤ : ℕ∞) (constructionJointScalar F)) :
    ∀ ell : ℕ, ContDiff ℝ (⊤ : ℕ∞)
      (constructionJointScalar (constructionMaterialIterate b ell F)) := by
  intro ell
  induction ell with
  | zero => exact hF
  | succ ell ih =>
      simpa [constructionMaterialIterate] using
        constructionMaterialDerivative_joint_contDiff hb ih

/-- The composed forward Jacobian is jointly smooth in the target time and
spatial point. This is obtained by differentiating the joint smooth flow in
its spatial variable and composing with the jointly smooth inverse flow. -/
theorem constructionComposedFlowJacobian_joint_contDiff
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {D : JetRecursionData α s q Λ ζ}
    {hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ} (m : ℕ) (s : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 =>
        Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s p.1 p.2) := by
  let v : ℝ → Vec 2 → Vec 2 := streamVel (Φ m)
  let hφ := AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq m
  have hv : Infra.Flow.SmoothPeriodicField v := AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ
  have hIsFlow : IsFlow v (Section2FlowIdentities.constructionFlow D hseq m) := by
    dsimp [v, Section2FlowIdentities.constructionFlow,
      Section2FlowIdentities.streamFlow]
    exact flow_isFlow (streamVel (Φ m)) hφ.vel_continuous hφ.vel_lipschitz
  have hforward : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 × ℝ =>
        Section2FlowIdentities.constructionFlow D hseq m p.1 p.2.1 p.2.2) := by
    simpa [Section2FlowIdentities.constructionFlow] using
      Infra.Flow.flow_joint_contDiff_infty hv hIsFlow
  have hdf : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 × ℝ => fderiv ℝ
        (fun q : ℝ × Vec 2 × ℝ =>
          Section2FlowIdentities.constructionFlow D hseq m q.1 q.2.1 q.2.2) p) :=
    hforward.fderiv_right (by simp)
  have hpartial : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 × ℝ =>
        (fderiv ℝ (fun q : ℝ × Vec 2 × ℝ =>
          Section2FlowIdentities.constructionFlow D hseq m q.1 q.2.1 q.2.2) p).comp
          constructionSpatialInputCLM) :=
    hdf.clm_comp contDiff_const
  have hparam : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 => (s + p.1, p.2, s)) := by
    fun_prop
  have hpartialShift : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 =>
        (fderiv ℝ (fun q : ℝ × Vec 2 × ℝ =>
          Section2FlowIdentities.constructionFlow D hseq m q.1 q.2.1 q.2.2) (s + p.1, p.2, s)).comp
          constructionSpatialInputCLM) := by
    exact hpartial.comp hparam
  have hJacobian : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 =>
        Section2FlowIdentities.constructionFlowJacobian D hseq m p.1 s p.2) := by
    have heq : (fun p : ℝ × Vec 2 =>
        Section2FlowIdentities.constructionFlowJacobian D hseq m p.1 s p.2) =
        fun p =>
          (fderiv ℝ (fun q : ℝ × Vec 2 × ℝ =>
            Section2FlowIdentities.constructionFlow D hseq m q.1 q.2.1 q.2.2) (s + p.1, p.2, s)).comp
            constructionSpatialInputCLM := by
      funext p
      let q : ℝ × Vec 2 × ℝ := (s + p.1, p.2, s)
      have hfirst : HasFDerivAt (fun _ : Vec 2 => q.1)
          (0 : Vec 2 →L[ℝ] ℝ) p.2 :=
        hasFDerivAt_const (c := q.1) (x := p.2)
      have hsecond : HasFDerivAt (fun y : Vec 2 => (y, q.2.2))
          ((ContinuousLinearMap.id ℝ (Vec 2)).prod
            (0 : Vec 2 →L[ℝ] ℝ)) p.2 :=
        (hasFDerivAt_id p.2).prodMk
          (hasFDerivAt_const (c := q.2.2) (x := p.2))
      have hinput : HasFDerivAt (fun y : Vec 2 => (q.1, (y, q.2.2)))
          constructionSpatialInputCLM p.2 := by
        simpa [constructionSpatialInputCLM] using hfirst.prodMk hsecond
      have hjointDeriv := (hforward.differentiable (by norm_num) q).hasFDerivAt
      have hcomp := hjointDeriv.comp p.2 hinput
      calc
        fderiv ℝ (fun y : Vec 2 => Section2FlowIdentities.constructionFlow D hseq m (s + p.1) y s)
            p.2 = fderiv ℝ (fun y : Vec 2 =>
              (fun q : ℝ × Vec 2 × ℝ =>
                Section2FlowIdentities.constructionFlow D hseq m q.1 q.2.1 q.2.2) (s + p.1, y, s)) p.2 := by
                congr 1
        _ = (fderiv ℝ (fun q : ℝ × Vec 2 × ℝ =>
              Section2FlowIdentities.constructionFlow D hseq m q.1 q.2.1 q.2.2)
              (s + p.1, p.2, s)).comp constructionSpatialInputCLM := by
                simpa [Function.comp_def, q, constructionSpatialInputCLM] using
                  hcomp.fderiv
    rw [heq]
    exact hpartialShift
  have hinverseJoint : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 × ℝ =>
        Section2FlowIdentities.constructionFlowInv D hseq m p.1 p.2.1 p.2.2) := by
    simpa [Section2FlowIdentities.constructionFlowInv,
      Section2FlowIdentities.constructionFlow,
      Section2FlowIdentities.streamFlowInv,
      Section2FlowIdentities.streamFlow, AVenhance.flowInv] using
      Infra.Flow.flow_inverse_joint_contDiff_infty hv hIsFlow
  have hinverseMap : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 =>
        Section2FlowIdentities.constructionFlowInv D hseq m (s + p.1) p.2 s) := by
    have h := hinverseJoint.comp hparam
    simpa [Function.comp_def] using h
  have hpair : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 =>
        (p.1, Section2FlowIdentities.constructionFlowInv D hseq m (s + p.1) p.2 s)) :=
    contDiff_fst.prodMk hinverseMap
  have hmatrix : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 =>
        Section2FlowIdentities.constructionFlowJacobian D hseq m p.1 s
          (Section2FlowIdentities.constructionFlowInv D hseq m (s + p.1) p.2 s)) := by
    simpa [Function.comp_def] using hJacobian.comp hpair
  have heq : (fun p : ℝ × Vec 2 =>
      Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s p.1 p.2) =
      fun p => Section2FlowIdentities.constructionFlowJacobian D hseq m p.1 s
        (Section2FlowIdentities.constructionFlowInv D hseq m (s + p.1) p.2 s) := by
    funext p
    rfl
  rw [heq]
  exact hmatrix

/-- Along any differentiable characteristic of `b`, one material derivative
is the ordinary derivative of the pulled-back profile. -/
theorem constructionMaterialDerivative_eq_deriv_pullback
    {b : ℝ → Vec 2 → Vec 2} {F : ℝ → Vec 2 → ℝ} {X : ℝ → Vec 2}
    (hF : ContDiff ℝ (⊤ : ℕ∞) (constructionJointScalar F)) (t : ℝ)
    (hX : HasDerivAt X (b t (X t)) t) :
    constructionMaterialDerivative b F t (X t) =
      deriv (fun r : ℝ => F r (X r)) t := by
  let H := constructionJointScalar F
  have hH := (hF.differentiable (by norm_num) (t, X t)).hasFDerivAt
  have hpath : HasDerivAt (fun r : ℝ => (r, X r)) (1, b t (X t)) t :=
    (hasDerivAt_id t).prodMk hX
  have hcomp := hH.comp_hasDerivAt t hpath
  have hjoint : deriv (fun r : ℝ => F r (X r)) t =
      fderiv ℝ H (t, X t) (1, b t (X t)) := by
    simpa [H, constructionJointScalar, Function.comp_def] using hcomp.deriv
  rw [constructionMaterialDerivative_eq_joint_fderiv hF t (X t), hjoint]

/-- All iterated material derivatives pull back to ordinary time derivatives
along the characteristic. -/
theorem constructionMaterialIterate_eq_iteratedTimeDerivative_pullback
    {b : ℝ → Vec 2 → Vec 2} {F : ℝ → Vec 2 → ℝ} {X : ℝ → Vec 2}
    (hb : ContDiff ℝ (⊤ : ℕ∞) (constructionJointVector b))
    (hF : ContDiff ℝ (⊤ : ℕ∞) (constructionJointScalar F))
    (hX : ∀ t : ℝ, HasDerivAt X (b t (X t)) t)
    (ell : ℕ) (t : ℝ) :
    constructionMaterialIterate b ell F t (X t) =
      MaterialGoalSource.iteratedTimeDerivative ell (fun r : ℝ => F r (X r)) t := by
  induction ell generalizing t with
  | zero => rfl
  | succ ell ih =>
      have hprev : MaterialGoalSource.iteratedTimeDerivative ell (fun r : ℝ => F r (X r)) =
          fun r : ℝ => constructionMaterialIterate b ell F r (X r) := by
        funext r
        exact (ih r).symm
      rw [MaterialGoalSource.iteratedTimeDerivative, hprev]
      have hstep := constructionMaterialDerivative_eq_deriv_pullback
        (F := constructionMaterialIterate b ell F)
        (constructionMaterialIterate_joint_contDiff hb hF ell) t (hX t)
      simpa [constructionMaterialIterate] using hstep

/-- For the Section 2 flow, material iteration of the composed forward
Jacobian becomes ordinary differentiation of the forward Jacobian along its
starting point. The smoothness premise is qualitative joint smoothness of the
composed Jacobian entry. -/
theorem constructionComposedFlowJacobian_materialIterate_eq_timeDerivative
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {D : JetRecursionData α s q Λ ζ}
    {hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ} (m : ℕ) (s : ℝ) (x : Vec 2)
    (i j : Fin 2) (ell : ℕ) (t : ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 =>
        Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s p.1 p.2
          (basisVec j) i)) :
    constructionMaterialIterate
      (fun r y => streamVel (Φ m) (s + r) y) ell
      (fun r y => Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s r y
        (basisVec j) i) t
      (Section2FlowIdentities.constructionFlow D hseq m (s + t) x s) =
    MaterialGoalSource.iteratedTimeDerivative ell
      (fun r => Section2FlowIdentities.constructionFlowJacobian D hseq m r s x (basisVec j) i) t := by
  let b : ℝ → Vec 2 → Vec 2 := fun r y => streamVel (Φ m) (s + r) y
  let F : ℝ → Vec 2 → ℝ := fun r y =>
    Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s r y (basisVec j) i
  let X : ℝ → Vec 2 := fun r => Section2FlowIdentities.constructionFlow D hseq m (s + r) x s
  let v := streamVel (Φ m)
  let hφ := AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq m
  have hv : Infra.Flow.SmoothPeriodicField v := AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ
  have hIsFlow : IsFlow v (Section2FlowIdentities.constructionFlow D hseq m) := by
    dsimp [v, Section2FlowIdentities.constructionFlow,
      Section2FlowIdentities.streamFlow]
    exact flow_isFlow (streamVel (Φ m)) hφ.vel_continuous hφ.vel_lipschitz
  have hb : ContDiff ℝ (⊤ : ℕ∞) (constructionJointVector b) := by
    have hbase : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : ℝ × Vec 2 => v p.1 p.2) := hv.smooth
    have hshift : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : ℝ × Vec 2 => (s + p.1, p.2)) := by fun_prop
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 => streamVel (Φ m) (s + p.1) p.2)
    exact hbase.comp hshift
  have hX (r : ℝ) : HasDerivAt X (b r (X r)) r := by
    have hode := hIsFlow.2 x s (r + s)
    simpa [X, b, v, Section2FlowIdentities.constructionFlow,
      Section2FlowIdentities.streamFlow, add_comm] using hode.comp_add_const r s
  have hF' : ContDiff ℝ (⊤ : ℕ∞) (constructionJointScalar F) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 =>
        Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s p.1 p.2
          (basisVec j) i)
    exact hF
  have hpull := constructionMaterialIterate_eq_iteratedTimeDerivative_pullback
    (b := b) (F := F) (X := X) hb hF' hX ell t
  have hL : ∃ L : ℝ, ∀ q y z,
      ‖v q y - v q z‖ ≤ L * ‖y - z‖ := by
    obtain ⟨L, _, hL⟩ := Infra.Flow.exists_global_spatial_lipschitz hv
    exact ⟨L, hL⟩
  have hinv (r : ℝ) :
      Section2FlowIdentities.constructionFlowInv D hseq m (s + r)
        (Section2FlowIdentities.constructionFlow D hseq m (s + r) x s) s = x := by
    calc
      Section2FlowIdentities.constructionFlowInv D hseq m (s + r)
          (Section2FlowIdentities.constructionFlow D hseq m (s + r) x s) s =
        Section2FlowIdentities.constructionFlow D hseq m s
          (Section2FlowIdentities.constructionFlow D hseq m (s + r) x s) (s + r) := by
            rfl
      _ = Section2FlowIdentities.constructionFlow D hseq m s x s := by
        exact Infra.Flow.flow_group_law v hL hIsFlow x s (s + r) s
      _ = x := hIsFlow.1 x s
  have hinv' (r : ℝ) :
      Section2FlowIdentities.streamFlowInv (Φ m) hφ (s + r)
        (Section2FlowIdentities.constructionFlow D hseq m (s + r) x s) s = x := by
    simpa [Section2FlowIdentities.constructionFlowInv] using hinv r
  have htrace : (fun r : ℝ => F r (X r)) =
      fun r => Section2FlowIdentities.constructionFlowJacobian D hseq m r s x (basisVec j) i := by
    funext r
    simp [F, X, Section2FlowIdentities.constructionComposedFlowJacobian,
      Section2FlowIdentities.streamComposedFlowJacobian,
      Section2FlowIdentities.constructionFlowJacobian, hinv' r]
  calc
    _ = MaterialGoalSource.iteratedTimeDerivative ell (fun r : ℝ => F r (X r)) t := by
      simpa [b, F, X] using hpull
    _ = MaterialGoalSource.iteratedTimeDerivative ell
        (fun r => Section2FlowIdentities.constructionFlowJacobian D hseq m r s x (basisVec j) i) t := by
      rw [htrace]

/-- The composed-flow Jacobian pullback identity with its qualitative
smoothness premise supplied by joint smoothness of the construction flow. -/
theorem constructionComposedFlowJacobian_materialIterate_eq_timeDerivative_of_flow
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    {D : JetRecursionData α s q Λ ζ}
    {hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ} (m : ℕ) (s : ℝ) (x : Vec 2)
    (i j : Fin 2) (ell : ℕ) (t : ℝ) :
    constructionMaterialIterate
      (fun r y => streamVel (Φ m) (s + r) y) ell
      (fun r y => Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s r y
        (basisVec j) i) t
      (Section2FlowIdentities.constructionFlow D hseq m (s + t) x s) =
    MaterialGoalSource.iteratedTimeDerivative ell
      (fun r => Section2FlowIdentities.constructionFlowJacobian D hseq m r s x (basisVec j) i) t := by
  have hmatrix := constructionComposedFlowJacobian_joint_contDiff
    (D := D) (hseq := hseq) m s
  have hcolumn : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 =>
        Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s p.1 p.2 (basisVec j)) :=
    hmatrix.clm_apply contDiff_const
  have hentry : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × Vec 2 =>
        Section2FlowIdentities.constructionComposedFlowJacobian D hseq m s p.1 p.2 (basisVec j) i) :=
    (contDiff_pi.1 hcolumn) i
  exact constructionComposedFlowJacobian_materialIterate_eq_timeDerivative
    (hseq := hseq) m s x i j ell t hentry

end AVRegularity.Velocity.Port.MaterialPullback
end
end
end

section
@[expose] public section
noncomputable section
open Homogenization MeasureTheory AVenhance
open scoped ContDiff
namespace AVRegularity.Velocity.Port.AppB2FieldBounds

/-! App. B.2 extraction of spatial seminorms for the OC stream velocity. -/

open AVRegularity.Velocity.Port.Section2Induction

noncomputable def scalarStreamEmbedding : ℝ →L[ℝ] Vec 2 :=
  ContinuousLinearMap.toSpanSingleton ℝ (Homogenization.basisVec 0)

theorem scalarStreamEmbedding_norm_le : ‖scalarStreamEmbedding‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro r
  calc
    ‖scalarStreamEmbedding r‖ = ‖r‖ := by
      change ‖r • Homogenization.basisVec 0‖ = ‖r‖
      rw [norm_smul]
      simp [Homogenization.basisVec, Pi.norm_single]
    _ ≤ 1 * ‖r‖ := by norm_num

noncomputable def streamGradientExtraction : FaaDiBruno.FlowMatrix →L[ℝ] Vec 2 :=
  ContinuousLinearMap.mk
    { toFun := fun A => ![-A 0 1, A 0 0]
      map_add' := by
        intro A B
        ext i
        fin_cases i
        · simp [add_comm]
        · simp
      map_smul' := by
        intro c A
        ext i
        fin_cases i <;> simp [smul_eq_mul] }
    (by fun_prop)

theorem streamGradientExtraction_norm_le (A : FaaDiBruno.FlowMatrix) :
    ‖streamGradientExtraction A‖ ≤ ‖A‖ := by
  rw [pi_norm_le_iff_of_nonempty]
  intro i
  fin_cases i
  · calc
      ‖-A 0 1‖ = ‖A 0 1‖ := norm_neg _
      _ ≤ ‖A 0‖ := norm_le_pi_norm _ _
      _ ≤ ‖A‖ := norm_le_pi_norm _ _
  · calc
      ‖A 0 0‖ ≤ ‖A 0‖ := norm_le_pi_norm _ _
      _ ≤ ‖A‖ := norm_le_pi_norm _ _

theorem streamGradientExtraction_opNorm_le :
    ‖streamGradientExtraction‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro A
  calc
    ‖streamGradientExtraction A‖ ≤ ‖A‖ := streamGradientExtraction_norm_le A
    _ = 1 * ‖A‖ := by ring

theorem derivativeSup_postCLM_le
    {n : ℕ} {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →L[ℝ] G) (f : Vec 2 → F) (hf : ContDiff ℝ n f)
    (hL : ‖L‖ ≤ 1) :
    FaaDiBruno.derivativeSup n (fun x => L (f x)) ≤
      FaaDiBruno.derivativeSup n f := by
  classical
  have hpartial (I : Fin n → Fin 2) (x : Vec 2) :
      FaaDiBruno.orderedPartial n (fun y => L (f y)) x I =
        L (FaaDiBruno.orderedPartial n f x I) := by
    let z : FaaDiBruno.VecOne 2 := WithLp.toLp 1 x
    have hcomp := L.iteratedFDeriv_comp_left (f := FaaDiBruno.liftVecOne f)
      (FaaDiBruno.contDiff_liftVecOne hf).contDiffAt (i := n) le_rfl (x := z)
    have hcomp' :
        iteratedFDeriv ℝ n (FaaDiBruno.liftVecOne (fun y => L (f y))) z =
          L.compContinuousMultilinearMap
            (iteratedFDeriv ℝ n (FaaDiBruno.liftVecOne f) z) := by
      simpa [FaaDiBruno.liftVecOne, Function.comp_def, z] using hcomp
    have heval := congrArg
      (fun D => D (fun j => FaaDiBruno.coordinateVectorOne 2 (I j))) hcomp'
    simpa [FaaDiBruno.orderedPartial, z] using heval
  unfold FaaDiBruno.derivativeSup
  refine iSup_le fun I => ?_
  calc
    FaaDiBruno.partialSup n (fun x => L (f x)) I ≤
        FaaDiBruno.partialSup n f I := by
      unfold FaaDiBruno.partialSup
      apply eLpNormEssSup_mono_enorm_ae
      filter_upwards with x
      rw [hpartial I x]
      have hnorm : ‖L (FaaDiBruno.orderedPartial n f x I)‖ ≤
          ‖FaaDiBruno.orderedPartial n f x I‖ := by
        calc
          ‖L (FaaDiBruno.orderedPartial n f x I)‖ ≤
              ‖L‖ * ‖FaaDiBruno.orderedPartial n f x I‖ := L.le_opNorm _
          _ ≤ 1 * ‖FaaDiBruno.orderedPartial n f x I‖ :=
            mul_le_mul_of_nonneg_right hL (norm_nonneg _)
          _ = ‖FaaDiBruno.orderedPartial n f x I‖ := by ring
      simpa [Real.enorm_eq_ofReal_abs] using ENNReal.ofReal_le_ofReal hnorm
    _ ≤ FaaDiBruno.derivativeSup n f := le_iSup_of_le I le_rfl

theorem streamVel_eq_extractedGradient
    (φ : ℝ → Vec 2 → ℝ) (hφsmooth : ContDiff ℝ ∞ (Function.uncurry φ))
    (t : ℝ) :
    streamVel φ t = fun x => streamGradientExtraction
      (FaaDiBruno.spatialGradientMatrix
        (fun y => scalarStreamEmbedding (φ t y)) x) := by
  funext x
  rw [streamVel_eq_timeIncrementRotate]
  have hφslice : ContDiff ℝ 1 (φ t) := by
    have hmap : ContDiff ℝ 1 (fun y : Vec 2 => (t, y)) := by fun_prop
    exact (hφsmooth.of_le (by norm_num)).comp hmap
  have hcomp := scalarStreamEmbedding.hasFDerivAt.comp x
    (hφslice.differentiable (by norm_num) x).hasFDerivAt
  have hderiv : fderiv ℝ (fun y => scalarStreamEmbedding (φ t y)) x =
      scalarStreamEmbedding.comp (fderiv ℝ (φ t) x) := by
    simpa only [Function.comp_def] using hcomp.fderiv
  unfold FaaDiBruno.spatialGradientMatrix
  rw [hderiv]
  ext i
  fin_cases i <;>
    simp [streamGradientExtraction, scalarStreamEmbedding, timeIncrementRotate,
      ContinuousLinearMap.comp_apply, Homogenization.basisVec,
      FaaDiBruno.coordinateVector]

theorem streamVel_derivativeSup_le_next
    (φ : ℝ → Vec 2 → ℝ) (hφ : ContDiff ℝ ∞ (Function.uncurry φ))
    (t : ℝ) (n : ℕ) :
    FaaDiBruno.derivativeSup n (streamVel φ t) ≤
      FaaDiBruno.derivativeSup (n + 1) (φ t) := by
  let F : Vec 2 → Vec 2 := fun x => scalarStreamEmbedding (φ t x)
  have hslice : ContDiff ℝ ∞ (φ t) := by
    have hmap : ContDiff ℝ ∞ (fun x : Vec 2 => (t, x)) := by fun_prop
    exact hφ.comp hmap
  have hF : ContDiff ℝ ∞ F := scalarStreamEmbedding.contDiff.comp hslice
  have hFderiv : ContDiff ℝ ∞ (fun x : Vec 2 => fderiv ℝ F x) :=
    hF.fderiv_right (by simp)
  have hgradient : ContDiff ℝ ∞ (FaaDiBruno.spatialGradientMatrix F) := by
    unfold FaaDiBruno.spatialGradientMatrix
    apply contDiff_pi.2
    intro i
    apply contDiff_pi.2
    intro j
    have hcolumn : ContDiff ℝ ∞
        (fun x : Vec 2 => fderiv ℝ F x (FaaDiBruno.coordinateVector 2 j)) :=
      hFderiv.clm_apply contDiff_const
    exact (contDiff_apply ℝ ℝ i).comp hcolumn
  rw [streamVel_eq_extractedGradient φ hφ t]
  calc
    FaaDiBruno.derivativeSup n
        (fun x => streamGradientExtraction (FaaDiBruno.spatialGradientMatrix F x)) ≤
        FaaDiBruno.derivativeSup n (FaaDiBruno.spatialGradientMatrix F) :=
      derivativeSup_postCLM_le streamGradientExtraction
        (FaaDiBruno.spatialGradientMatrix F)
        (hgradient.of_le (by simp)) streamGradientExtraction_opNorm_le
    _ ≤ FaaDiBruno.derivativeSup (n + 1) F :=
      FaaDiBruno.spatialGradientMatrix_derivativeSup_le F hF n
    _ = FaaDiBruno.derivativeSup (n + 1)
        (fun x => scalarStreamEmbedding (φ t x)) := rfl
    _ ≤ FaaDiBruno.derivativeSup (n + 1) (φ t) :=
      derivativeSup_postCLM_le scalarStreamEmbedding (φ t)
        (hslice.of_le (by simp)) scalarStreamEmbedding_norm_le

theorem streamVel_snorm_le_from_induction
    (φ : ℝ → Vec 2 → ℝ) (hφ : ContDiff ℝ ∞ (Function.uncurry φ))
    (t : ℝ) (n : ℕ) {R M : ℝ} (hR : 0 < R) (hM : 0 < M)
    (hprev : FaaDiBruno.snorm (φ t) (n + 1) R ≤ ENNReal.ofReal
      (M * R⁻¹ ^ 2 * (((n : ℝ) + 3) ^ 2 / ((n : ℝ) + 2) ^ 3))) :
    FaaDiBruno.snorm (streamVel φ t) n R ≤ ENNReal.ofReal (M / R) := by
  have hDprev := FaaDiBruno.derivativeSup_le_of_snorm_le (φ t) hR hprev
  have hDprev' : FaaDiBruno.derivativeSup (n + 1) (φ t) ≤
      ENNReal.ofReal
        (M * R⁻¹ ^ 2 * (((n : ℝ) + 3) ^ 2 / ((n : ℝ) + 2) ^ 3) *
          (n + 1).factorial * R ^ (n + 1) / ((n : ℝ) + 2) ^ 2) := by
    have hden : (((n + 1 : ℕ) : ℝ) + 1) ^ 2 = ((n : ℝ) + 2) ^ 2 := by
      push_cast
      ring
    have hDprev'' := hDprev
    rw [hden] at hDprev''
    exact hDprev''
  have hDvel := streamVel_derivativeSup_le_next φ hφ t n
  have hpoly : ((n : ℝ) + 1) ^ 3 * ((n : ℝ) + 3) ^ 2 ≤
      ((n : ℝ) + 2) ^ 5 := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [sq_nonneg ((n : ℝ) + 2), sq_nonneg ((n : ℝ) + 3)]
  have hderiv : FaaDiBruno.derivativeSup n (streamVel φ t) ≤
      ENNReal.ofReal
        ((M / R) * n.factorial * R ^ n / ((n : ℝ) + 1) ^ 2) := by
    calc
      FaaDiBruno.derivativeSup n (streamVel φ t) ≤
          FaaDiBruno.derivativeSup (n + 1) (φ t) := hDvel
      _ ≤ ENNReal.ofReal
          (M * R⁻¹ ^ 2 * (((n : ℝ) + 3) ^ 2 / ((n : ℝ) + 2) ^ 3) *
            (n + 1).factorial * R ^ (n + 1) / ((n : ℝ) + 2) ^ 2) := hDprev'
      _ ≤ ENNReal.ofReal
          ((M / R) * n.factorial * R ^ n / ((n : ℝ) + 1) ^ 2) := by
          apply ENNReal.ofReal_le_ofReal
          have hRn : R ^ (n + 1) = R ^ n * R := by rw [pow_succ]
          rw [hRn, Nat.factorial_succ]
          have hpolyFac :
              ((n : ℝ) + 1) ^ 3 * ((n : ℝ) + 3) ^ 2 *
                  (n.factorial : ℝ) ≤
                ((n : ℝ) + 2) ^ 5 * (n.factorial : ℝ) :=
            mul_le_mul_of_nonneg_right hpoly (by positivity)
          push_cast
          field_simp [hR.ne']
          nlinarith [hpolyFac]
  have hderiv' : FaaDiBruno.derivativeSup n (streamVel φ t) ≤
      ENNReal.ofReal ((M / R) * R ^ n * n.factorial / ((n : ℝ) + 1) ^ 2) := by
    convert hderiv using 1
    congr 1
    ring
  exact FaaDiBruno.snorm_le_of_derivativeSup_le (streamVel φ t) hR hderiv'

/-- The source App. B.2 field estimate, with the current OC induction level. -/
theorem section2_streamVel_snorm_bound
    {α s q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ}
    (D : JetRecursionData α s q Λ ζ)
    {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseq : AVRegularity.IsOCStreamSeq α q Λ ζ Φ)
    {m n : ℕ} (hprev : Section2StreamInductionHypothesis D Φ m)
    (hn : 1 ≤ n) (t : ℝ) :
    FaaDiBruno.snorm (streamVel (Φ m) t) n (D.radius m) ≤
      ENNReal.ofReal (D.jetSize m / D.radius m) := by
  have hR := AVRegularity.Velocity.Port.Section2Scales.section2_radius_pos D m
  have hM := AVRegularity.Velocity.Port.Section2Scales.section2_amplitude_pos D m
  have hsource0 : FaaDiBruno.snorm (Φ m t) (n + 1) (D.radius m) ≤
      ENNReal.ofReal
        (D.jetSize m * (D.radius m)⁻¹ ^ 2 *
          (((n : ℝ) + 1 + 2) ^ 2 / ((n : ℝ) + 1 + 1) ^ 3)) := by
    simpa only [Section2StreamInductionHypothesis, Nat.cast_add, Nat.cast_one] using
      hprev t (n + 1) (by omega)
  have hsource : FaaDiBruno.snorm (Φ m t) (n + 1) (D.radius m) ≤
      ENNReal.ofReal
        (D.jetSize m * (D.radius m)⁻¹ ^ 2 *
          (((n : ℝ) + 3) ^ 2 / ((n : ℝ) + 2) ^ 3)) := by
    convert hsource0 using 1
    congr 1
    ring
  exact streamVel_snorm_le_from_induction (Φ m)
    (AVRegularity.Velocity.streamSeq_admissible D.hζ D.hΛ hseq m).1
    t n hR hM hsource

end AVRegularity.Velocity.Port.AppB2FieldBounds
end
end
end
