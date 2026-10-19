-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev.Basic
import Mathlib.Algebra.Order.Star.Real

/-! Unweighted and factorial weighted norms on the ambient jet product. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization
open scoped ENNReal

namespace AVRegularity.Sobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
variable {μ : Measure (Vec 2)} {K : ℕ}

/-- Squared `L²` norm of the complete ordered derivative tensor of order `j`. -/
def derivativeNormSq (D : JetL2 μ K E) (j : Fin (K + 1)) : ℝ :=
  ∑ w : DerivativeWord2 j.val, ‖D ⟨j, w⟩‖ ^ 2

/-- The factorial weight assigned to derivative level `j`. -/
def factorialWeight (ρ : ℝ) (j : ℕ) : ℝ :=
  ρ ^ (2 * j) / (j.factorial : ℝ) ^ 2

/-- The squared factorial weighted norm on the finite jet product. -/
def factorialNormSq (ρ : ℝ) (D : JetL2 μ K E) : ℝ :=
  ∑ j : Fin (K + 1), factorialWeight ρ j.val * derivativeNormSq D j

omit [InnerProductSpace ℝ E] [BorelSpace E] [CompleteSpace E] in
/-- Every derivative tensor has nonnegative squared norm. -/
theorem derivativeNormSq_nonneg (D : JetL2 μ K E) (j : Fin (K + 1)) :
    0 ≤ derivativeNormSq D j :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- The factorial weight is nonnegative for every real radius. -/
theorem factorialWeight_nonneg (ρ : ℝ) (j : ℕ) : 0 ≤ factorialWeight ρ j := by
  unfold factorialWeight
  have hp : ρ ^ (2 * j) = (ρ ^ j) ^ 2 := by
    rw [Nat.mul_comm, pow_mul]
  rw [hp]
  positivity

omit [InnerProductSpace ℝ E] [BorelSpace E] [CompleteSpace E] in
/-- The factorial weighted square is nonnegative. -/
theorem factorialNormSq_nonneg (ρ : ℝ) (D : JetL2 μ K E) :
    0 ≤ factorialNormSq ρ D := by
  unfold factorialNormSq
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (factorialWeight_nonneg ρ j.val) (derivativeNormSq_nonneg D j)

omit [InnerProductSpace ℝ E] [BorelSpace E] [CompleteSpace E] in
/-- The unweighted Hilbert norm is the sum of all derivative tensor squares. -/
theorem jet_norm_sq_eq_sum (D : JetL2 μ K E) :
    ‖D‖ ^ 2 = ∑ j : Fin (K + 1), derivativeNormSq D j := by
  rw [PiLp.norm_sq_eq_of_L2]
  unfold derivativeNormSq
  exact Fintype.sum_sigma fun a : JetIndex2 K => ‖D a‖ ^ 2

/-- Smallest factorial coefficient over the finite jet orders. -/
def factorialWeightMin (ρ : ℝ) (K : ℕ) : ℝ :=
  Finset.univ.inf' ⟨⟨0, Nat.zero_lt_succ K⟩, Finset.mem_univ _⟩
    (fun j : Fin (K + 1) => factorialWeight ρ j.val)

/-- Largest factorial coefficient over the finite jet orders. -/
def factorialWeightMax (ρ : ℝ) (K : ℕ) : ℝ :=
  Finset.univ.sup' ⟨⟨0, Nat.zero_lt_succ K⟩, Finset.mem_univ _⟩
    (fun j : Fin (K + 1) => factorialWeight ρ j.val)

/-- Every finite-order factorial coefficient is at least its explicit minimum. -/
theorem factorialWeightMin_le (ρ : ℝ) (j : Fin (K + 1)) :
    factorialWeightMin ρ K ≤ factorialWeight ρ j.val :=
  Finset.inf'_le _ (Finset.mem_univ j)

/-- Every finite-order factorial coefficient is at most its explicit maximum. -/
theorem factorialWeight_le_max (ρ : ℝ) (j : Fin (K + 1)) :
    factorialWeight ρ j.val ≤ factorialWeightMax ρ K :=
  Finset.le_sup' (fun i : Fin (K + 1) => factorialWeight ρ i.val)
    (Finset.mem_univ j)

/-- At positive radius every finite-order factorial coefficient has positive minimum. -/
theorem factorialWeightMin_pos (ρ : ℝ) (hρ : 0 < ρ) :
    0 < factorialWeightMin ρ K := by
  unfold factorialWeightMin
  apply (Finset.lt_inf'_iff _).2
  intro j hj
  unfold factorialWeight
  exact div_pos (pow_pos hρ _) (by positivity)

omit [InnerProductSpace ℝ E] [BorelSpace E] [CompleteSpace E] in
/-- The weighted square is bounded below by the minimum coefficient times the unweighted square. -/
theorem factorialNormSq_lower (ρ : ℝ) (D : JetL2 μ K E) :
    factorialWeightMin ρ K * ‖D‖ ^ 2 ≤ factorialNormSq ρ D := by
  rw [factorialNormSq, jet_norm_sq_eq_sum]
  calc
    factorialWeightMin ρ K * ∑ j : Fin (K + 1), derivativeNormSq D j ≤
        ∑ j : Fin (K + 1), factorialWeight ρ j.val * derivativeNormSq D j := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right (factorialWeightMin_le ρ j)
        (derivativeNormSq_nonneg D j)

omit [InnerProductSpace ℝ E] [BorelSpace E] [CompleteSpace E] in
/-- The weighted square is bounded above by the maximum coefficient times the unweighted square. -/
theorem factorialNormSq_upper (ρ : ℝ) (D : JetL2 μ K E) :
    factorialNormSq ρ D ≤ factorialWeightMax ρ K * ‖D‖ ^ 2 := by
  rw [factorialNormSq, jet_norm_sq_eq_sum]
  calc
    (∑ j : Fin (K + 1), factorialWeight ρ j.val * derivativeNormSq D j) ≤
        ∑ j : Fin (K + 1), factorialWeightMax ρ K * derivativeNormSq D j := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right (factorialWeight_le_max ρ j)
        (derivativeNormSq_nonneg D j)
    _ = factorialWeightMax ρ K * ∑ j : Fin (K + 1), derivativeNormSq D j := by
      rw [Finset.mul_sum]

end AVRegularity.Sobolev
