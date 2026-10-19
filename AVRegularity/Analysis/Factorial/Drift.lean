-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

section
open scoped BigOperators
namespace AVRegularity.Analysis.Factorial

/-- The finite analytic weight `ρ^j / j!`. -/
noncomputable def factorialWeight (ρ : ℝ) (j : ℕ) : ℝ := ρ ^ j / (j.factorial : ℝ)

private theorem factorialRiseMonotone {j K r : ℕ} (hjk : j ≤ K) :
    (j + r).factorial * K.factorial ≤ (K + r).factorial * j.factorial := by
  have hchoose : (j + r).choose r ≤ (K + r).choose r :=
    Nat.choose_le_choose r (Nat.add_le_add_right hjk r)
  have hleft : (j + r).choose r * r.factorial * j.factorial = (j + r).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (n := j + r) (k := r) (by omega)
    simpa [Nat.add_sub_cancel_right] using this
  have hright : (K + r).choose r * r.factorial * K.factorial = (K + r).factorial := by
    have := Nat.choose_mul_factorial_mul_factorial (n := K + r) (k := r) (by omega)
    simpa [Nat.add_sub_cancel_right] using this
  have hmul := Nat.mul_le_mul_right (r.factorial * j.factorial * K.factorial) hchoose
  calc
    (j + r).factorial * K.factorial =
        (j + r).choose r * (r.factorial * j.factorial * K.factorial) := by
          rw [← hleft]
          ac_rfl
    _ ≤ (K + r).choose r * (r.factorial * j.factorial * K.factorial) := hmul
    _ = (K + r).factorial * j.factorial := by
          rw [← hright]
          ac_rfl

private theorem shiftedForwardSquareSum_le (K r : ℕ) (W : ℕ → ℝ) :
    (∑ j ∈ Finset.range (K + 1), W (j + r) ^ 2) ≤
      ∑ k ∈ Finset.range (K + r + 1), W k ^ 2 := by
  classical
  let R := Finset.range (K + 1)
  have hinj : Set.InjOn (fun j => j + r) R := by
    intro j hj k hk heq
    exact Nat.add_right_cancel heq
  have hsub : R.image (fun j => j + r) ⊆ Finset.range (K + r + 1) := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_range.mpr (by
      have hjK : j < K + 1 := Finset.mem_range.mp hj
      omega)
  calc
    (∑ j ∈ R, W (j + r) ^ 2) = ∑ k ∈ R.image (fun j => j + r), W k ^ 2 := by
      rw [Finset.sum_image]
      exact hinj
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun k _ _ => sq_nonneg (W k))

/-- Shifting `r` derivative levels costs at most the factor `ρ^{-r} (K+r)!/K!`
(Lemma 7.1(b) of the paper). -/
theorem factorialShiftInequality {K r : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    (w : ℕ → NNReal) :
    Real.sqrt (∑ j ∈ Finset.range (K + 1),
      (factorialWeight ρ j * (w (j + r) : ℝ)) ^ 2) ≤
      ((ρ ^ r)⁻¹ * ((K + r).factorial : ℝ) / (K.factorial : ℝ)) *
        Real.sqrt (∑ k ∈ Finset.range (K + r + 1),
          (factorialWeight ρ k * (w k : ℝ)) ^ 2) := by
  let C := (ρ ^ r)⁻¹ * ((K + r).factorial : ℝ) / (K.factorial : ℝ)
  let W := fun k => factorialWeight ρ k * (w k : ℝ)
  have hρnonneg : 0 ≤ ρ := hρ.le
  have hweightpos : ∀ k, 0 < factorialWeight ρ k := by
    intro k
    unfold factorialWeight
    exact div_pos (pow_pos hρ _) (by exact_mod_cast Nat.factorial_pos k)
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  have hCrho : C * ρ ^ r = ((K + r).factorial : ℝ) / (K.factorial : ℝ) := by
    dsimp [C]
    field_simp [ne_of_gt (pow_pos hρ r),
      ne_of_gt (by exact_mod_cast Nat.factorial_pos K : (K.factorial : ℝ) ≠ 0)]
  have hfactor (j : ℕ) (hj : j ≤ K) :
      1 / (j.factorial : ℝ) ≤
        (((K + r).factorial : ℝ) / (K.factorial : ℝ)) /
          ((j + r).factorial : ℝ) := by
    have hnat := factorialRiseMonotone (r := r) hj
    have hnatR :
        ((j + r).factorial : ℝ) * (K.factorial : ℝ) ≤
          ((K + r).factorial : ℝ) * (j.factorial : ℝ) := by exact_mod_cast hnat
    apply (div_le_div_iff₀
      (by exact_mod_cast Nat.factorial_pos j : (0 : ℝ) < (j.factorial : ℝ))
      (by exact_mod_cast Nat.factorial_pos (j + r) : (0 : ℝ) < ((j + r).factorial : ℝ))).2
    field_simp [ne_of_gt (by exact_mod_cast Nat.factorial_pos K : (K.factorial : ℝ) ≠ 0)]
    nlinarith [hnatR]
  have hcoeff (j : ℕ) (hj : j ≤ K) :
      factorialWeight ρ j ≤ C * factorialWeight ρ (j + r) := by
    unfold factorialWeight
    have hp : ρ ^ (j + r) = ρ ^ j * ρ ^ r := by rw [pow_add]
    calc
      ρ ^ j / (j.factorial : ℝ) =
          ρ ^ j * (1 / (j.factorial : ℝ)) := by ring
      _ ≤ ρ ^ j * ((((K + r).factorial : ℝ) / (K.factorial : ℝ)) /
          ((j + r).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left (hfactor j hj) (pow_nonneg hρnonneg _)
      _ = C * (ρ ^ (j + r) / ((j + r).factorial : ℝ)) := by
        rw [hp, ← hCrho]
        ring
  have hpoint (j : ℕ) (hj : j ∈ Finset.range (K + 1)) :
      (factorialWeight ρ j * (w (j + r) : ℝ)) ^ 2 ≤
        (C * W (j + r)) ^ 2 := by
    have hjK : j ≤ K := by simp only [Finset.mem_range] at hj; omega
    have hle := mul_le_mul_of_nonneg_right (hcoeff j hjK)
      (NNReal.coe_nonneg (w (j + r)))
    have hnonnegL : 0 ≤ factorialWeight ρ j * (w (j + r) : ℝ) :=
      mul_nonneg (hweightpos j).le (NNReal.coe_nonneg _)
    have hWnonneg : 0 ≤ W (j + r) := by
      dsimp [W]
      exact mul_nonneg (hweightpos (j + r)).le (NNReal.coe_nonneg (w (j + r)))
    have hnonnegR : 0 ≤ C * W (j + r) := mul_nonneg hCpos.le hWnonneg
    have hdiff : factorialWeight ρ j * (w (j + r) : ℝ) ≤ C * W (j + r) := by
      simpa [W, mul_assoc] using hle
    nlinarith [mul_nonneg (sub_nonneg.mpr hdiff) (add_nonneg hnonnegL hnonnegR)]
  have hsumPoint :
      (∑ j ∈ Finset.range (K + 1),
        (factorialWeight ρ j * (w (j + r) : ℝ)) ^ 2) ≤
        C ^ 2 * (∑ j ∈ Finset.range (K + 1), W (j + r) ^ 2) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (K + 1), (C * W (j + r)) ^ 2 :=
        Finset.sum_le_sum fun j hj => hpoint j hj
      _ = C ^ 2 * (∑ j ∈ Finset.range (K + 1), W (j + r) ^ 2) := by
        simp only [mul_pow]
        rw [Finset.mul_sum]
  have hsumBound :
      (∑ j ∈ Finset.range (K + 1),
        (factorialWeight ρ j * (w (j + r) : ℝ)) ^ 2) ≤
        C ^ 2 * (∑ k ∈ Finset.range (K + r + 1), W k ^ 2) := by
    exact hsumPoint.trans (mul_le_mul_of_nonneg_left
      (shiftedForwardSquareSum_le K r W) (sq_nonneg C))
  have hLnonneg : 0 ≤ ∑ j ∈ Finset.range (K + 1),
      (factorialWeight ρ j * (w (j + r) : ℝ)) ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have hRnonneg : 0 ≤ ∑ k ∈ Finset.range (K + r + 1), W k ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  have hrightNonneg : 0 ≤ C * Real.sqrt (∑ k ∈ Finset.range (K + r + 1), W k ^ 2) :=
    mul_nonneg hCpos.le (Real.sqrt_nonneg _)
  have hroot : Real.sqrt (∑ j ∈ Finset.range (K + 1),
      (factorialWeight ρ j * (w (j + r) : ℝ)) ^ 2) ≤
        C * Real.sqrt (∑ k ∈ Finset.range (K + r + 1), W k ^ 2) := by
    have hrightSq :
        (C * Real.sqrt (∑ k ∈ Finset.range (K + r + 1), W k ^ 2)) ^ 2 =
          C ^ 2 * (∑ k ∈ Finset.range (K + r + 1), W k ^ 2) := by
      rw [mul_pow, Real.sq_sqrt hRnonneg]
    exact Real.sqrt_le_iff.mpr ⟨hrightNonneg, by
      rw [hrightSq]
      exact hsumBound⟩
  simpa [C, W] using hroot

private theorem factorialWeightPred (ρ : ℝ) {j : ℕ} (hj : 1 ≤ j) :
    factorialWeight ρ j = (ρ / (j : ℝ)) * factorialWeight ρ (j - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  simp only [Nat.succ_sub_one]
  unfold factorialWeight
  rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem factorialWeightAnalyticJet (ρ a B ell : ℝ) (l : ℕ) :
    factorialWeight ρ l * (a * B ^ l * (l.factorial : ℝ) / ell ^ (l - 1)) =
      a * (B * ρ) ^ l / ell ^ (l - 1) := by
  unfold factorialWeight
  field_simp [Nat.factorial_ne_zero]
  ring

private theorem factorialWeightMulChoose (ρ : ℝ) {j l : ℕ} (hlj : l ≤ j) :
    factorialWeight ρ j * (j.choose l : ℝ) =
      factorialWeight ρ l * factorialWeight ρ (j - l) := by
  have hf : (j.choose l : ℝ) * (l.factorial : ℝ) * ((j - l).factorial : ℝ) =
      (j.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hlj
  have hp : ρ ^ j = ρ ^ l * ρ ^ (j - l) := by
    rw [← pow_add, Nat.add_sub_of_le hlj]
  unfold factorialWeight
  rw [hp]
  field_simp [Nat.factorial_ne_zero]
  linear_combination (ρ ^ l * ρ ^ (j - l)) * hf

private theorem driftCoefficientIdentity {ρ a B ell : ℝ} {j l : ℕ}
    (hl : 1 ≤ l) (hlj : l ≤ j) (hell : 0 < ell) :
    factorialWeight ρ j ^ 2 * (j.choose l : ℝ) *
        (a * B ^ l * (l.factorial : ℝ) / ell ^ (l - 1)) =
      (a * B * ρ ^ 2 / (j : ℝ)) * (B * ρ / ell) ^ (l - 1) *
        factorialWeight ρ (j - l) * factorialWeight ρ (j - 1) := by
  have hj : 1 ≤ j := hl.trans hlj
  have hpow : (l - 1) + 1 = l := by omega
  calc
    factorialWeight ρ j ^ 2 * (j.choose l : ℝ) *
        (a * B ^ l * (l.factorial : ℝ) / ell ^ (l - 1)) =
      factorialWeight ρ j * (factorialWeight ρ l *
        (a * B ^ l * (l.factorial : ℝ) / ell ^ (l - 1))) *
        factorialWeight ρ (j - l) := by
          have hc := factorialWeightMulChoose ρ hlj
          linear_combination factorialWeight ρ j *
            (a * B ^ l * (l.factorial : ℝ) / ell ^ (l - 1)) * hc
    _ = factorialWeight ρ j *
        (a * (B * ρ) ^ l / ell ^ (l - 1)) * factorialWeight ρ (j - l) := by
      rw [factorialWeightAnalyticJet]
    _ = ((ρ / (j : ℝ)) * factorialWeight ρ (j - 1)) *
        (a * (B * ρ) ^ l / ell ^ (l - 1)) * factorialWeight ρ (j - l) := by
          rw [factorialWeightPred ρ hj]
    _ = (a * B * ρ ^ 2 / (j : ℝ)) * (B * ρ / ell) ^ (l - 1) *
        factorialWeight ρ (j - l) * factorialWeight ρ (j - 1) := by
      rw [show (B * ρ) ^ l = (B * ρ) ^ (l - 1) * (B * ρ) by
        simpa only [hpow] using pow_succ (B * ρ) (l - 1), div_pow]
      field_simp [ne_of_gt hell,
        ne_of_gt (show 0 < (j : ℝ) by exact_mod_cast (by omega : 0 < j))]

private theorem driftFactorialTermBound {ρ a B ell A Y Z : ℝ} {j l : ℕ}
    (hρ : 0 ≤ ρ) (ha : 0 ≤ a) (hB : 0 ≤ B) (hell : 0 < ell)
    (hl : 1 ≤ l) (hlj : l ≤ j) (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
    (hA : A ≤ a * B ^ l * (l.factorial : ℝ) / ell ^ (l - 1)) :
    factorialWeight ρ j ^ 2 * (j.choose l : ℝ) * (A * Y) * Z ≤
      (a * B * ρ ^ 2) * (B * ρ / ell) ^ (l - 1) *
        ((factorialWeight ρ (j - l) * Y) *
          (factorialWeight ρ (j - 1) * Z)) := by
  have hα : 0 ≤ a * B * ρ ^ 2 := mul_nonneg (mul_nonneg ha hB) (sq_nonneg ρ)
  have hj : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hl.trans hlj
  have hprice : (a * B * ρ ^ 2) / (j : ℝ) ≤ a * B * ρ ^ 2 := div_le_self hα hj
  have htail : 0 ≤ (B * ρ / ell) ^ (l - 1) *
      factorialWeight ρ (j - l) * factorialWeight ρ (j - 1) * Y * Z := by
    unfold factorialWeight
    positivity
  calc
    factorialWeight ρ j ^ 2 * (j.choose l : ℝ) * (A * Y) * Z ≤
        (factorialWeight ρ j ^ 2 * (j.choose l : ℝ) *
          (a * B ^ l * (l.factorial : ℝ) / ell ^ (l - 1))) * Y * Z := by
      apply mul_le_mul_of_nonneg_right _ hZ
      calc
        factorialWeight ρ j ^ 2 * (j.choose l : ℝ) * (A * Y) =
            (factorialWeight ρ j ^ 2 * (j.choose l : ℝ) * A) * Y := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hA
            (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _))) hY
    _ = ((a * B * ρ ^ 2) / (j : ℝ)) *
        ((B * ρ / ell) ^ (l - 1) * factorialWeight ρ (j - l) *
          factorialWeight ρ (j - 1) * Y * Z) := by
      rw [driftCoefficientIdentity hl hlj hell]
      ring
    _ ≤ _ := by
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_right hprice htail

private theorem shiftedSquareSumLe (K l : ℕ) (x : ℕ → ℝ) :
    (∑ j ∈ (Finset.range (K + 1)).filter (fun j => l ≤ j), x (j - l) ^ 2) ≤
      ∑ k ∈ Finset.range (K + 1), x k ^ 2 := by
  classical
  let s := (Finset.range (K + 1)).filter (fun j => l ≤ j)
  have hinj : Set.InjOn (fun j => j - l) s := by
    intro j hj k hk heq
    have hjl := (Finset.mem_filter.mp hj).2
    have hkl := (Finset.mem_filter.mp hk).2
    change j - l = k - l at heq
    omega
  have hsub : s.image (fun j => j - l) ⊆ Finset.range (K + 1) := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_range.mpr
      ((Nat.sub_le j l).trans_lt (Finset.mem_range.mp (Finset.mem_filter.mp hj).1))
  calc
    _ = ∑ k ∈ s.image (fun j => j - l), x k ^ 2 := by
      rw [Finset.sum_image]
      exact hinj
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun k _ _ => sq_nonneg (x k))

private theorem driftShiftedProductSumLe (K : ℕ) {l : ℕ} (hl : 1 ≤ l)
    (x : ℕ → ℝ) :
    (∑ j ∈ (Finset.range (K + 1)).filter (fun j => l ≤ j),
      x (j - l) * x (j - 1)) ≤ ∑ k ∈ Finset.range (K + 1), x k ^ 2 := by
  classical
  have hfirst :
      (∑ j ∈ (Finset.range (K + 1)).filter (fun j => l ≤ j), x (j - 1) ^ 2) ≤
        ∑ k ∈ Finset.range (K + 1), x k ^ 2 := by
    calc
      _ ≤ ∑ j ∈ (Finset.range (K + 1)).filter (fun j => 1 ≤ j), x (j - 1) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (by
            intro j hj
            exact Finset.mem_filter.mpr
              ⟨(Finset.mem_filter.mp hj).1,
                hl.trans (Finset.mem_filter.mp hj).2⟩)
          (fun j _ _ => sq_nonneg _)
      _ ≤ _ := shiftedSquareSumLe K 1 x
  have hsecond := shiftedSquareSumLe K l x
  have hprod :
      (∑ j ∈ (Finset.range (K + 1)).filter (fun j => l ≤ j),
        2 * (x (j - l) * x (j - 1))) ≤
      ∑ j ∈ (Finset.range (K + 1)).filter (fun j => l ≤ j),
        (x (j - l) ^ 2 + x (j - 1) ^ 2) := by
    apply Finset.sum_le_sum
    intro j _
    nlinarith [sq_nonneg (x (j - l) - x (j - 1))]
  rw [← Finset.mul_sum, Finset.sum_add_distrib] at hprod
  linarith

private theorem driftGeometricSumLeTwo (K : ℕ) {q : ℝ}
    (hq : 0 ≤ q) (hqhalf : q ≤ 1 / 2) :
    (∑ l ∈ (Finset.range (K + 1)).erase 0, q ^ (l - 1)) ≤ 2 := by
  classical
  have heq : (Finset.range (K + 1)).erase 0 = (Finset.range K).image Nat.succ := by
    ext l
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨h0, hlt⟩
      exact ⟨l - 1, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      omega
  rw [heq, Finset.sum_image (fun a _ b _ h => Nat.succ_injective h)]
  simp only [Nat.succ_sub_one]
  exact (Finset.sum_le_sum (fun k _ => pow_le_pow_left₀ hq hqhalf k)).trans
    (sum_geometric_two_le K)

private theorem driftTriangleExchange (K : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ j ∈ Finset.range (K + 1),
      ∑ l ∈ (Finset.range (j + 1)).erase 0, f j l) =
    ∑ l ∈ (Finset.range (K + 1)).erase 0,
      ∑ j ∈ (Finset.range (K + 1)).filter (fun j => l ≤ j), f j l := by
  classical
  have hinner (j : ℕ) (hj : j ∈ Finset.range (K + 1)) :
      (∑ l ∈ (Finset.range (j + 1)).erase 0, f j l) =
        ∑ l ∈ (Finset.range (K + 1)).erase 0, if l ≤ j then f j l else 0 := by
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext l
      simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_filter]
      have hjK := Finset.mem_range.mp hj
      omega
    · intro l _
      rfl
  calc
    _ = ∑ j ∈ Finset.range (K + 1),
        ∑ l ∈ (Finset.range (K + 1)).erase 0, if l ≤ j then f j l else 0 :=
      Finset.sum_congr rfl hinner
    _ = _ := by rw [Finset.sum_comm]; simp only [Finset.sum_filter]

private theorem driftGeometricPairSumLe (K : ℕ) {q : ℝ}
    (hq : 0 ≤ q) (hqhalf : q ≤ 1 / 2) (x : ℕ → ℝ) :
    (∑ j ∈ Finset.range (K + 1),
      ∑ l ∈ (Finset.range (j + 1)).erase 0,
        q ^ (l - 1) * (x (j - l) * x (j - 1))) ≤
      2 * ∑ k ∈ Finset.range (K + 1), x k ^ 2 := by
  classical
  rw [driftTriangleExchange]
  calc
    _ = ∑ l ∈ (Finset.range (K + 1)).erase 0, q ^ (l - 1) *
        ∑ j ∈ (Finset.range (K + 1)).filter (fun j => l ≤ j),
          x (j - l) * x (j - 1) := by simp only [Finset.mul_sum]
    _ ≤ ∑ l ∈ (Finset.range (K + 1)).erase 0, q ^ (l - 1) *
        ∑ k ∈ Finset.range (K + 1), x k ^ 2 := by
      apply Finset.sum_le_sum
      intro l hl
      have hlpos : 1 ≤ l := by have hn := (Finset.mem_erase.mp hl).1; omega
      exact mul_le_mul_of_nonneg_left (driftShiftedProductSumLe K hlpos x)
        (pow_nonneg hq _)
    _ = (∑ l ∈ (Finset.range (K + 1)).erase 0, q ^ (l - 1)) *
        ∑ k ∈ Finset.range (K + 1), x k ^ 2 := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (driftGeometricSumLeTwo K hq hqhalf)
      (Finset.sum_nonneg fun k _ => sq_nonneg (x k))

/-- The source drift commutator sum is absorbed by one quarter of the
factorial-weighted dissipation under the two analytic jet budgets. -/
theorem driftCommutatorAbsorption {K : ℕ} {ρ a B ell ν : ℝ}
    (hρ : 0 ≤ ρ) (ha : 0 ≤ a) (hB : 0 ≤ B) (hell : 0 < ell) (_hν : 0 < ν)
    (hsmall : B * ρ / ell ≤ 1 / 2) (hstrain : a * B * ρ ^ 2 ≤ ν / 8)
    (V Y : ℕ → ℝ) (hY : ∀ j, 0 ≤ Y j)
    (hjet : ∀ l, 1 ≤ l → l ≤ K →
      V l ≤ a * B ^ l * (l.factorial : ℝ) / ell ^ (l - 1)) :
    (∑ j ∈ Finset.range (K + 1), factorialWeight ρ j ^ 2 *
      ∑ l ∈ (Finset.range (j + 1)).erase 0,
        (j.choose l : ℝ) * V l * Y (j - l + 1) * Y j) ≤
      (ν / 4) * ∑ k ∈ Finset.range (K + 1),
        (factorialWeight ρ k * Y (k + 1)) ^ 2 := by
  classical
  let X := fun k => factorialWeight ρ k * Y (k + 1)
  have hweight : ∀ k, 0 ≤ factorialWeight ρ k := by
    intro k
    unfold factorialWeight
    exact div_nonneg (pow_nonneg hρ _) (Nat.cast_nonneg _)
  have hX : ∀ k, 0 ≤ X k := by
    intro k
    exact mul_nonneg (hweight k) (hY (k + 1))
  have hα : 0 ≤ a * B * ρ ^ 2 := mul_nonneg (mul_nonneg ha hB) (sq_nonneg ρ)
  have hq : 0 ≤ B * ρ / ell := div_nonneg (mul_nonneg hB hρ) hell.le
  have hsum :
      (∑ j ∈ Finset.range (K + 1), factorialWeight ρ j ^ 2 *
        ∑ l ∈ (Finset.range (j + 1)).erase 0,
          (j.choose l : ℝ) * V l * Y (j - l + 1) * Y j) ≤
      (a * B * ρ ^ 2) *
        (∑ j ∈ Finset.range (K + 1),
          ∑ l ∈ (Finset.range (j + 1)).erase 0,
            (B * ρ / ell) ^ (l - 1) * (X (j - l) * X (j - 1))) := by
    calc
      (∑ j ∈ Finset.range (K + 1), factorialWeight ρ j ^ 2 *
          ∑ l ∈ (Finset.range (j + 1)).erase 0,
            (j.choose l : ℝ) * V l * Y (j - l + 1) * Y j) =
        ∑ j ∈ Finset.range (K + 1),
          ∑ l ∈ (Finset.range (j + 1)).erase 0,
            factorialWeight ρ j ^ 2 *
              ((j.choose l : ℝ) * V l * Y (j - l + 1) * Y j) := by
          simp only [Finset.mul_sum]
      _ ≤ ∑ j ∈ Finset.range (K + 1),
          ∑ l ∈ (Finset.range (j + 1)).erase 0,
            (a * B * ρ ^ 2) * (B * ρ / ell) ^ (l - 1) *
              (X (j - l) * X (j - 1)) := by
          apply Finset.sum_le_sum
          intro j hj
          apply Finset.sum_le_sum
          intro l hl
          have hlpos : 1 ≤ l := by have hn := (Finset.mem_erase.mp hl).1; omega
          have hlj : l ≤ j := Nat.le_of_lt_succ
            (Finset.mem_range.mp (Finset.mem_erase.mp hl).2)
          have hjK : j ≤ K := by simp only [Finset.mem_range] at hj; omega
          have hlK : l ≤ K := hlj.trans hjK
          have hterm := driftFactorialTermBound hρ ha hB hell hlpos hlj
            (hY (j - l + 1)) (hY j) (hjet l hlpos hlK)
          simpa only [X, mul_assoc, Nat.sub_add_cancel (hlpos.trans hlj)] using hterm
      _ = (a * B * ρ ^ 2) *
          (∑ j ∈ Finset.range (K + 1),
            ∑ l ∈ (Finset.range (j + 1)).erase 0,
              (B * ρ / ell) ^ (l - 1) * (X (j - l) * X (j - 1))) := by
          calc
            (∑ j ∈ Finset.range (K + 1),
                ∑ l ∈ (Finset.range (j + 1)).erase 0,
                  (a * B * ρ ^ 2) * (B * ρ / ell) ^ (l - 1) *
                    (X (j - l) * X (j - 1))) =
              ∑ j ∈ Finset.range (K + 1),
                (a * B * ρ ^ 2) *
                  (∑ l ∈ (Finset.range (j + 1)).erase 0,
                    (B * ρ / ell) ^ (l - 1) * (X (j - l) * X (j - 1))) := by
                apply Finset.sum_congr rfl
                intro j _
                calc
                  (∑ l ∈ (Finset.range (j + 1)).erase 0,
                      (a * B * ρ ^ 2) * (B * ρ / ell) ^ (l - 1) *
                        (X (j - l) * X (j - 1))) =
                    ∑ l ∈ (Finset.range (j + 1)).erase 0,
                      (a * B * ρ ^ 2) *
                        ((B * ρ / ell) ^ (l - 1) * (X (j - l) * X (j - 1))) := by
                          apply Finset.sum_congr rfl
                          intro l _
                          ring
                  _ = (a * B * ρ ^ 2) *
                      (∑ l ∈ (Finset.range (j + 1)).erase 0,
                        (B * ρ / ell) ^ (l - 1) * (X (j - l) * X (j - 1))) := by
                          rw [Finset.mul_sum]
            _ = (a * B * ρ ^ 2) *
                (∑ j ∈ Finset.range (K + 1),
                  ∑ l ∈ (Finset.range (j + 1)).erase 0,
                    (B * ρ / ell) ^ (l - 1) * (X (j - l) * X (j - 1))) := by
                  rw [Finset.mul_sum]
  have hgeom := driftGeometricPairSumLe K hq hsmall X
  have hcoeff : 2 * (a * B * ρ ^ 2) ≤ ν / 4 := by linarith
  calc
    (∑ j ∈ Finset.range (K + 1), factorialWeight ρ j ^ 2 *
      ∑ l ∈ (Finset.range (j + 1)).erase 0,
        (j.choose l : ℝ) * V l * Y (j - l + 1) * Y j) ≤
      (a * B * ρ ^ 2) *
        (∑ j ∈ Finset.range (K + 1),
          ∑ l ∈ (Finset.range (j + 1)).erase 0,
            (B * ρ / ell) ^ (l - 1) * (X (j - l) * X (j - 1))) := hsum
    _ ≤ (a * B * ρ ^ 2) *
        (2 * ∑ k ∈ Finset.range (K + 1), X k ^ 2) :=
      mul_le_mul_of_nonneg_left hgeom hα
    _ ≤ (ν / 4) * ∑ k ∈ Finset.range (K + 1), X k ^ 2 := by
      have hXsq : 0 ≤ ∑ k ∈ Finset.range (K + 1), X k ^ 2 :=
        Finset.sum_nonneg fun k _ => sq_nonneg _
      simpa only [mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_right hcoeff hXsq
    _ = (ν / 4) * ∑ k ∈ Finset.range (K + 1),
        (factorialWeight ρ k * Y (k + 1)) ^ 2 := by rfl

end AVRegularity.Analysis.Factorial
end
