-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CoupledEnergy.GradFactorialNormSq
import AVRegularity.CycleComparison.Coarse.Exists.Cell
public import AVRegularity.Statements.Intermediate.CycleComparison.CoarseFluxAdjoint
public import AVRegularity.CycleComparison.Coarse.Adj.MulOp
public import AVRegularity.Statements.Intermediate.CycleComparison.CovPolyQ
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open scoped ENNReal
namespace AVRegularity.CycleComparison.Coarse

/-! The scalar algebra of one step of the letter recursion: from the energy bound
`E ≤ √(6F + 24Φ/B)`, the flux bound `Φ ≤ 2C_D²X' + 2S²X''` and the gradient bounds
`B X' ≤ E'²`, `B X'' ≤ E''²`, deduce `E ≤ √6 √F + (√48 C_D/B) E' + (√48 S/B) E''`. -/

/-- A square root bound from a square bound in `ℝ≥0∞`. -/
theorem ofReal_sqrt_le_of_sq {X : ℝ} {E : ℝ≥0∞} (h : ENNReal.ofReal X ≤ E ^ (2 : ℝ)) :
    ENNReal.ofReal (Real.sqrt X) ≤ E := by
  rcases le_or_gt X 0 with hX | hX
  · rw [Real.sqrt_eq_zero'.2 hX, ENNReal.ofReal_zero]; exact zero_le
  have h1 : ENNReal.ofReal (Real.sqrt X) ^ (2 : ℝ) ≤ E ^ (2 : ℝ) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num)]
    have : Real.sqrt X ^ (2 : ℝ) = X := by
      rw [Real.rpow_two, Real.sq_sqrt hX.le]
    rw [this]; exact h
  exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).1 h1

/-- **One step of the letter recursion.** -/
theorem letter_step {B F Φ X' X'' CgD S : ℝ} (hB : 0 < B) (hF : 0 ≤ F)
    (hX' : 0 ≤ X') (hX'' : 0 ≤ X'') (hCgD : 0 ≤ CgD) (hS : 0 ≤ S) (n1 n2 : ℕ)
    {E E' E'' : ℝ≥0∞}
    (hE : E ≤ ENNReal.ofReal (Real.sqrt (6 * F + 24 / B * Φ)))
    (hΦb : Φ ≤ (if n1 = 0 then 0 else 2 * CgD ^ 2 * X') + (if n2 = 0 then 0 else 2 * S ^ 2 * X''))
    (h' : n1 ≠ 0 → ENNReal.ofReal (B * X') ≤ E' ^ (2 : ℝ))
    (h'' : n2 ≠ 0 → ENNReal.ofReal (B * X'') ≤ E'' ^ (2 : ℝ)) :
    E ≤ ENNReal.ofReal (Real.sqrt 6 * Real.sqrt F) +
      (if n1 = 0 then 0 else ENNReal.ofReal (Real.sqrt 48 * CgD / B) * E') +
      (if n2 = 0 then 0 else ENNReal.ofReal (Real.sqrt 48 * S / B) * E'') := by
  set a : ℝ := if n1 = 0 then 0 else Real.sqrt 48 * CgD / B * Real.sqrt (B * X')
  set c : ℝ := if n2 = 0 then 0 else Real.sqrt 48 * S / B * Real.sqrt (B * X'')
  have ha : 0 ≤ a := by simp only [a]; split_ifs <;> positivity
  have hc : 0 ≤ c := by simp only [c]; split_ifs <;> positivity
  have hsB : Real.sqrt B * Real.sqrt B = B := Real.mul_self_sqrt hB.le
  -- the real inequality
  have hreal : Real.sqrt (6 * F + 24 / B * Φ) ≤ Real.sqrt 6 * Real.sqrt F + a + c := by
    rw [Real.sqrt_le_left (by positivity)]
    have hΦ' : 24 / B * Φ ≤ (a + c) ^ 2 := by
      have h1 : 24 / B * Φ ≤ 24 / B * ((if n1 = 0 then 0 else 2 * CgD ^ 2 * X') +
          (if n2 = 0 then 0 else 2 * S ^ 2 * X'')) :=
        mul_le_mul_of_nonneg_left hΦb (by positivity)
      refine h1.trans ?_
      have hsq48 : Real.sqrt 48 ^ 2 = 48 := Real.sq_sqrt (by norm_num)
      have hBne : B ≠ 0 := hB.ne'
      have hA : 24 / B * (if n1 = 0 then 0 else 2 * CgD ^ 2 * X') ≤ a ^ 2 := by
        simp only [a]
        split_ifs
        · simp
        · rw [mul_pow, div_pow, mul_pow, hsq48, Real.sq_sqrt (mul_nonneg hB.le hX')]
          refine le_of_eq ?_
          field_simp
          ring
      have hC : 24 / B * (if n2 = 0 then 0 else 2 * S ^ 2 * X'') ≤ c ^ 2 := by
        simp only [c]
        split_ifs
        · simp
        · rw [mul_pow, div_pow, mul_pow, hsq48, Real.sq_sqrt (mul_nonneg hB.le hX'')]
          refine le_of_eq ?_
          field_simp
          ring
      nlinarith [mul_nonneg ha hc]
    have h6 : (Real.sqrt 6 * Real.sqrt F) ^ 2 = 6 * F := by
      rw [mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hF]
    nlinarith [mul_nonneg (mul_nonneg (Real.sqrt_nonneg 6) (Real.sqrt_nonneg F)) (add_nonneg ha hc)]
  refine hE.trans ((ENNReal.ofReal_le_ofReal hreal).trans ?_)
  rw [ENNReal.ofReal_add (by positivity) hc, ENNReal.ofReal_add (by positivity) ha]
  refine add_le_add (add_le_add le_rfl ?_) ?_
  · simp only [a]
    split_ifs with hn
    · simp
    · rw [ENNReal.ofReal_mul (by positivity)]
      exact mul_le_mul_of_nonneg_left (ofReal_sqrt_le_of_sq (h' hn)) zero_le
  · simp only [c]
    split_ifs with hn
    · simp
    · rw [ENNReal.ofReal_mul (by positivity)]
      exact mul_le_mul_of_nonneg_left (ofReal_sqrt_le_of_sq (h'' hn)) zero_le

/-! The binomial word bound: a doubly indexed family obeying the letter recursion
`e_{i,j} ≤ [i=j=0] 4F + x e_{i-1,j} + y e_{i,j-1}` is at most `4 binom(i+j, i) x^i y^j F`
(Pascal's identity). -/

/-- **The binomial word bound.** -/
theorem binomial_word_bound {x y F : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hF : 0 ≤ F)
    (e : ℕ → ℕ → ℝ≥0∞) (J H : ℕ)
    (hrec : ∀ i, i ≤ J → ∀ j, j ≤ H →
      e i j ≤ (if i = 0 ∧ j = 0 then ENNReal.ofReal (4 * F) else 0) +
        (if i = 0 then 0 else ENNReal.ofReal x * e (i - 1) j) +
        (if j = 0 then 0 else ENNReal.ofReal y * e i (j - 1))) :
    ∀ i, i ≤ J → ∀ j, j ≤ H →
      e i j ≤ ENNReal.ofReal (4 * (Nat.choose (i + j) i : ℝ) * x ^ i * y ^ j * F) := by
  suffices h : ∀ n, ∀ i j, i + j = n → i ≤ J → j ≤ H →
      e i j ≤ ENNReal.ofReal (4 * (Nat.choose (i + j) i : ℝ) * x ^ i * y ^ j * F) from
    fun i hi j hj => h (i + j) i j rfl hi hj
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i j hij hi hj
    refine (hrec i hi j hj).trans ?_
    -- the predecessor bounds
    have hP : i ≠ 0 → ENNReal.ofReal x * e (i - 1) j ≤
        ENNReal.ofReal (x * (4 * (Nat.choose (i - 1 + j) (i - 1) : ℝ) * x ^ (i - 1) * y ^ j * F)) := by
      intro hi0
      rw [ENNReal.ofReal_mul hx]
      exact mul_le_mul_of_nonneg_left (ih (i - 1 + j) (by omega) (i - 1) j rfl (by omega) hj) zero_le
    have hQ : j ≠ 0 → ENNReal.ofReal y * e i (j - 1) ≤
        ENNReal.ofReal (y * (4 * (Nat.choose (i + (j - 1)) i : ℝ) * x ^ i * y ^ (j - 1) * F)) := by
      intro hj0
      rw [ENNReal.ofReal_mul hy]
      exact mul_le_mul_of_nonneg_left (ih (i + (j - 1)) (by omega) i (j - 1) rfl hi (by omega)) zero_le
    rcases Nat.eq_zero_or_pos i with rfl | hi0 <;> rcases Nat.eq_zero_or_pos j with rfl | hj0
    · simp
    · -- i = 0, j > 0
      simp only [true_and, (Nat.pos_iff_ne_zero.1 hj0), ↓reduceIte, zero_add,
        Nat.choose_zero_right, pow_zero]
      refine (hQ (Nat.pos_iff_ne_zero.1 hj0)).trans (le_of_eq ?_)
      congr 1
      simp only [zero_add, Nat.choose_zero_right, Nat.cast_one, pow_zero]
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      simp only [Nat.add_sub_cancel, pow_succ]
      ring
    · -- i > 0, j = 0
      simp only [(Nat.pos_iff_ne_zero.1 hi0), and_true, ↓reduceIte, zero_add, add_zero]
      refine (hP (Nat.pos_iff_ne_zero.1 hi0)).trans (le_of_eq ?_)
      congr 1
      simp only [add_zero, Nat.choose_self, Nat.cast_one, pow_zero]
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      simp only [Nat.add_sub_cancel, pow_succ]
      ring
    · -- both positive
      have hi' : i ≠ 0 := Nat.pos_iff_ne_zero.1 hi0
      have hj' : j ≠ 0 := Nat.pos_iff_ne_zero.1 hj0
      simp only [hi', hj', and_false, ↓reduceIte, zero_add]
      refine (add_le_add (hP hi') (hQ hj')).trans (le_of_eq ?_)
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hpascal : Nat.choose (i' + 1 + (j' + 1)) (i' + 1) =
          Nat.choose (i' + (j' + 1)) i' + Nat.choose (i' + 1 + j') (i' + 1) := by
        have e1 : i' + 1 + (j' + 1) = (i' + (j' + 1)) + 1 := by ring
        have e2 : i' + 1 + j' = i' + (j' + 1) := by ring
        rw [e1, e2, Nat.choose_succ_succ]
      simp only [Nat.add_sub_cancel]
      rw [hpascal]
      push_cast
      ring

end AVRegularity.CycleComparison.Coarse
end

section
namespace AVRegularity.CycleComparison.Coarse

/-! The mass-weighted Schur test for the edge part of the coarse fluxes, and row and column sums of
powers of a nonnegative matrix. -/

variable {ι : Type*} [Fintype ι]

/-- Cauchy–Schwarz with nonnegative weights. -/
theorem sq_sum_mul_le (a y : ι → ℝ) (ha : ∀ u, 0 ≤ a u) :
    (∑ u, a u * y u) ^ 2 ≤ (∑ u, a u) * ∑ u, a u * y u ^ 2 := by
  have h1 : ∑ u, a u * y u = ∑ u, Real.sqrt (a u) * (Real.sqrt (a u) * y u) := by
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← mul_assoc, Real.mul_self_sqrt (ha u)]
  rw [h1]
  refine (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun u => Real.sqrt (a u))
    (fun u => Real.sqrt (a u) * y u)).trans (le_of_eq ?_)
  congr 1
  · exact Finset.sum_congr rfl fun u _ => Real.sq_sqrt (ha u)
  · refine Finset.sum_congr rfl fun u _ => ?_
    rw [mul_pow, Real.sq_sqrt (ha u)]

/-- **The mass-weighted Schur test.** -/
theorem schur_mass_sq_le (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (c : ι → ι → ℝ)
    (hc : ∀ v u, 0 ≤ c v u) (x : ι → ℝ) (S : ℝ)
    (hrow : ∀ v, ∑ u, Real.sqrt (π u / π v) * c v u ≤ S)
    (hcol : ∀ u, ∑ v, Real.sqrt (π u / π v) * c v u ≤ S) :
    ∑ v, (π v)⁻¹ * (∑ u, c v u * x u) ^ 2 ≤ S ^ 2 * ∑ u, (π u)⁻¹ * x u ^ 2 := by
  classical
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨v₀⟩⟩
  · simp
  set a : ι → ι → ℝ := fun v u => Real.sqrt (π u / π v) * c v u
  set y : ι → ℝ := fun u => x u / Real.sqrt (π u)
  have ha : ∀ v u, 0 ≤ a v u := fun v u => mul_nonneg (Real.sqrt_nonneg _) (hc v u)
  have hrel : ∀ v, (π v)⁻¹ * (∑ u, c v u * x u) ^ 2 = (∑ u, a v u * y u) ^ 2 := by
    intro v
    have hsv : 0 < Real.sqrt (π v) := Real.sqrt_pos.2 (hπ v)
    have e : ∑ u, c v u * x u = Real.sqrt (π v) * ∑ u, a v u * y u := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      have hsu : 0 < Real.sqrt (π u) := Real.sqrt_pos.2 (hπ u)
      simp only [a, y]
      rw [Real.sqrt_div (hπ u).le]
      field_simp
    rw [e, mul_pow, Real.sq_sqrt (hπ v).le, ← mul_assoc, inv_mul_cancel₀ (hπ v).ne', one_mul]
  have hy : ∀ u, (π u)⁻¹ * x u ^ 2 = y u ^ 2 := by
    intro u
    simp only [y]
    rw [div_pow, Real.sq_sqrt (hπ u).le, inv_mul_eq_div]
  have hS : 0 ≤ S := (Finset.sum_nonneg fun u _ => ha v₀ u).trans (hrow v₀)
  simp_rw [hrel, hy]
  calc ∑ v, (∑ u, a v u * y u) ^ 2 ≤ ∑ v, S * ∑ u, a v u * y u ^ 2 := by
        refine Finset.sum_le_sum fun v _ => (sq_sum_mul_le (a v) y (ha v)).trans ?_
        exact mul_le_mul_of_nonneg_right (hrow v)
          (Finset.sum_nonneg fun u _ => mul_nonneg (ha v u) (sq_nonneg _))
    _ = S * ∑ u, (∑ v, a v u) * y u ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        exact Finset.sum_congr rfl fun u _ => by rw [Finset.sum_mul]
    _ ≤ S * ∑ u, S * y u ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u _ => ?_) hS
        exact mul_le_mul_of_nonneg_right (hcol u) (sq_nonneg _)
    _ = S ^ 2 * ∑ u, y u ^ 2 := by rw [← Finset.mul_sum]; ring

/-- Row sums of powers of a nonnegative matrix. -/
theorem matrix_pow_row_sum_le [DecidableEq ι] (A : Matrix ι ι ℝ) (hA : ∀ v u, 0 ≤ A v u)
    {Θ : ℝ} (hΘ : 0 ≤ Θ) (hrow : ∀ v, ∑ u, A v u ≤ Θ) :
    ∀ r : ℕ, (∀ v u, 0 ≤ (A ^ r) v u) ∧ ∀ v, ∑ u, (A ^ r) v u ≤ Θ ^ r
  | 0 => by
      refine ⟨fun v u => ?_, fun v => ?_⟩
      · rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
      · rw [pow_zero, pow_zero]
        simp [Matrix.one_apply]
  | r + 1 => by
      obtain ⟨h0, h1⟩ := matrix_pow_row_sum_le A hA hΘ hrow r
      refine ⟨fun v u => ?_, fun v => ?_⟩
      · rw [pow_succ, Matrix.mul_apply]
        exact Finset.sum_nonneg fun w _ => mul_nonneg (h0 v w) (hA w u)
      · rw [pow_succ]
        simp only [Matrix.mul_apply]
        rw [Finset.sum_comm]
        calc ∑ w, ∑ u, (A ^ r) v w * A w u = ∑ w, (A ^ r) v w * ∑ u, A w u := by
              exact Finset.sum_congr rfl fun w _ => by rw [Finset.mul_sum]
          _ ≤ ∑ w, (A ^ r) v w * Θ :=
              Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left (hrow w) (h0 v w)
          _ = (∑ w, (A ^ r) v w) * Θ := by rw [Finset.sum_mul]
          _ ≤ Θ ^ r * Θ := mul_le_mul_of_nonneg_right (h1 v) hΘ
          _ = Θ ^ (r + 1) := by rw [pow_succ]

/-- Column sums of powers of a nonnegative matrix. -/
theorem matrix_pow_col_sum_le [DecidableEq ι] (A : Matrix ι ι ℝ) (hA : ∀ v u, 0 ≤ A v u)
    {Θ : ℝ} (hΘ : 0 ≤ Θ) (hcol : ∀ u, ∑ v, A v u ≤ Θ) (r : ℕ) (u : ι) :
    ∑ v, (A ^ r) v u ≤ Θ ^ r := by
  have hT := matrix_pow_row_sum_le A.transpose (fun v u => hA u v) hΘ (fun v => by
    simpa [Matrix.transpose_apply] using hcol v) r
  have e : (A.transpose ^ r) = (A ^ r).transpose := (Matrix.transpose_pow A r).symm
  have := hT.2 u
  rw [e] at this
  simpa [Matrix.transpose_apply] using this

end AVRegularity.CycleComparison.Coarse
end

section
open MeasureTheory
namespace AVRegularity.CycleComparison.Coarse

/-! The integrated letter bound: from the pointwise bound of the flux of each component by a
diagonal gradient term and edge gradient terms, the mass-weighted time integral of the flux is
bounded by `2 C_D²` times that of the diagonal gradients plus `2 S²` times that of the edge
gradients, `S` the mass-weighted Schur constant of the edge coefficients. -/

variable {ι : Type*} [Fintype ι]

/-- Pointwise form. -/
theorem flux_mass_pointwise (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (n1 n2 : ℕ) {CgD S : ℝ}
    (c : ι → ι → ℝ) (hc : ∀ v u, 0 ≤ c v u)
    (hrow : ∀ v, ∑ u, Real.sqrt (π u / π v) * c v u ≤ S)
    (hcol : ∀ u, ∑ v, Real.sqrt (π u / π v) * c v u ≤ S)
    (f gD gE : ι → ℝ) (hf : ∀ v, 0 ≤ f v) (hgD : ∀ v, 0 ≤ gD v) (hgE : ∀ u, 0 ≤ gE u)
    (hpt : ∀ v, Real.sqrt (f v) ≤ (if n1 = 0 then 0 else CgD * Real.sqrt (gD v)) +
      ∑ u, (if n2 = 0 then 0 else c v u * Real.sqrt (gE u))) :
    ∑ v, (π v)⁻¹ * f v ≤ (if n1 = 0 then 0 else 2 * CgD ^ 2 * ∑ v, (π v)⁻¹ * gD v) +
      (if n2 = 0 then 0 else 2 * S ^ 2 * ∑ u, (π u)⁻¹ * gE u) := by
  set A : ι → ℝ := fun v => if n1 = 0 then 0 else CgD * Real.sqrt (gD v)
  set Bs : ι → ℝ := fun v => ∑ u, (if n2 = 0 then 0 else c v u * Real.sqrt (gE u))
  have hfv : ∀ v, f v ≤ 2 * A v ^ 2 + 2 * Bs v ^ 2 := by
    intro v
    have h0 : 0 ≤ Real.sqrt (f v) := Real.sqrt_nonneg _
    have h1 : f v = Real.sqrt (f v) ^ 2 := (Real.sq_sqrt (hf v)).symm
    have h2 : Real.sqrt (f v) ^ 2 ≤ (A v + Bs v) ^ 2 :=
      pow_le_pow_left₀ h0 (hpt v) 2
    nlinarith [sq_nonneg (A v - Bs v)]
  have hπi : ∀ v, 0 ≤ (π v)⁻¹ := fun v => inv_nonneg.2 (hπ v).le
  calc ∑ v, (π v)⁻¹ * f v ≤ ∑ v, (π v)⁻¹ * (2 * A v ^ 2 + 2 * Bs v ^ 2) :=
        Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (hfv v) (hπi v)
    _ = 2 * ∑ v, (π v)⁻¹ * A v ^ 2 + 2 * ∑ v, (π v)⁻¹ * Bs v ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun v _ => by ring
    _ ≤ _ := by
        refine add_le_add ?_ ?_
        · by_cases hn : n1 = 0
          · simp [A, hn]
          · simp only [A, hn, ↓reduceIte]
            rw [Finset.mul_sum, Finset.mul_sum]
            refine le_of_eq (Finset.sum_congr rfl fun v _ => ?_)
            rw [mul_pow, Real.sq_sqrt (hgD v)]; ring
        · by_cases hn : n2 = 0
          · simp [Bs, hn]
          · simp only [Bs, hn, ↓reduceIte]
            have hs := schur_mass_sq_le π hπ c hc (fun u => Real.sqrt (gE u)) S hrow hcol
            have he : ∀ u, (π u)⁻¹ * Real.sqrt (gE u) ^ 2 = (π u)⁻¹ * gE u := fun u => by
              rw [Real.sq_sqrt (hgE u)]
            simp only [he] at hs
            linarith

/-- **The integrated letter bound.** -/
theorem flux_mass_integral_le {I : Set ℝ} (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (n1 n2 : ℕ)
    {CgD S : ℝ} (c : ι → ι → ℝ) (hc : ∀ v u, 0 ≤ c v u)
    (hrow : ∀ v, ∑ u, Real.sqrt (π u / π v) * c v u ≤ S)
    (hcol : ∀ u, ∑ v, Real.sqrt (π u / π v) * c v u ≤ S)
    (f gD gE wD wE : ℝ → ι → ℝ) (hf : ∀ s v, 0 ≤ f s v) (hgD : ∀ s v, 0 ≤ gD s v)
    (hgE : ∀ s u, 0 ≤ gE s u)
    (hpt : ∀ s ∈ I, ∀ v, Real.sqrt (f s v) ≤ (if n1 = 0 then 0 else CgD * Real.sqrt (gD s v)) +
      ∑ u, (if n2 = 0 then 0 else c v u * Real.sqrt (gE s u)))
    (hwD : ∀ᵐ s ∂(volume.restrict I), ∀ v, gD s v ≤ wD s v)
    (hwE : ∀ᵐ s ∂(volume.restrict I), ∀ u, gE s u ≤ wE s u)
    (hfi : ∀ v, Integrable (fun s => f s v) (volume.restrict I))
    (hwDi : ∀ v, Integrable (fun s => wD s v) (volume.restrict I))
    (hwEi : ∀ u, Integrable (fun s => wE s u) (volume.restrict I))
    (hmeas : MeasurableSet I) :
    ∫ s in I, ∑ v, (π v)⁻¹ * f s v ≤
      (if n1 = 0 then 0 else 2 * CgD ^ 2 * ∫ s in I, ∑ v, (π v)⁻¹ * wD s v) +
        (if n2 = 0 then 0 else 2 * S ^ 2 * ∫ s in I, ∑ u, (π u)⁻¹ * wE s u) := by
  have hint1 : Integrable (fun s => ∑ v, (π v)⁻¹ * f s v) (volume.restrict I) :=
    integrable_finsetSum _ fun v _ => (hfi v).const_mul _
  have hintD : Integrable (fun s => ∑ v, (π v)⁻¹ * wD s v) (volume.restrict I) :=
    integrable_finsetSum _ fun v _ => (hwDi v).const_mul _
  have hintE : Integrable (fun s => ∑ u, (π u)⁻¹ * wE s u) (volume.restrict I) :=
    integrable_finsetSum _ fun u _ => (hwEi u).const_mul _
  have hrhs : ∫ s in I, ((if n1 = 0 then 0 else 2 * CgD ^ 2 * ∑ v, (π v)⁻¹ * wD s v) +
      (if n2 = 0 then 0 else 2 * S ^ 2 * ∑ u, (π u)⁻¹ * wE s u)) =
      (if n1 = 0 then 0 else 2 * CgD ^ 2 * ∫ s in I, ∑ v, (π v)⁻¹ * wD s v) +
        (if n2 = 0 then 0 else 2 * S ^ 2 * ∫ s in I, ∑ u, (π u)⁻¹ * wE s u) := by
    by_cases h1 : n1 = 0 <;> by_cases h2 : n2 = 0 <;>
      simp only [h1, h2, ↓reduceIte, zero_add, add_zero, integral_zero, integral_const_mul]
    rw [integral_add (hintD.const_mul _) (hintE.const_mul _), integral_const_mul,
      integral_const_mul]
  rw [← hrhs]
  have hπi : ∀ v, 0 ≤ (π v)⁻¹ := fun v => inv_nonneg.2 (hπ v).le
  refine integral_mono_ae hint1 ?_ ?_
  · by_cases h1 : n1 = 0 <;> by_cases h2 : n2 = 0 <;> simp only [h1, h2, ↓reduceIte]
    · exact integrable_zero _ _ _ |>.add (integrable_zero _ _ _)
    · exact (integrable_zero _ _ _).add (hintE.const_mul _)
    · exact (hintD.const_mul _).add (integrable_zero _ _ _)
    · exact (hintD.const_mul _).add (hintE.const_mul _)
  · filter_upwards [hwD, hwE, ae_restrict_mem hmeas] with s hD hE hs
    refine (flux_mass_pointwise π hπ n1 n2 c hc hrow hcol (f s) (gD s) (gE s) (hf s) (hgD s)
      (hgE s) (hpt s hs)).trans ?_
    refine add_le_add ?_ ?_
    · by_cases h1 : n1 = 0
      · simp [h1]
      · simp only [h1, ↓reduceIte]
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ =>
          mul_le_mul_of_nonneg_left (hD v) (hπi v)) (by positivity)
    · by_cases h2 : n2 = 0
      · simp [h2]
      · simp only [h2, ↓reduceIte]
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u _ =>
          mul_le_mul_of_nonneg_left (hE u) (hπi u)) (by positivity)

end AVRegularity.CycleComparison.Coarse
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Coarse

/-! Factorial norms are continuous on the jet spaces and bounded by the unweighted norm, so for a
square-integrable field in time they are integrable. -/

section
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] {μ : Measure (Vec 2)}

theorem continuous_factorialNormSq (ρ : ℝ) (K : ℕ) :
    Continuous fun D : JetL2 μ K E => factorialNormSq ρ D := by
  unfold factorialNormSq derivativeNormSq
  refine continuous_finsetSum _ fun j _ => continuous_const.mul ?_
  exact continuous_finsetSum _ fun w _ =>
    ((PiLp.continuous_apply 2 _ (⟨j, w⟩ : JetIndex2 K)).norm).pow 2

theorem continuous_gradFactorialNormSq (ρ : ℝ) (K : ℕ) :
    Continuous fun D : JetL2 μ (K + 1) E => gradFactorialNormSq ρ D := by
  unfold gradFactorialNormSq
  refine continuous_finsetSum _ fun j _ => continuous_const.mul ?_
  exact continuous_finsetSum _ fun w _ =>
    ((PiLp.continuous_apply 2 _ _).norm).pow 2

theorem gradFactorialNormSq_nonneg (ρ : ℝ) {K : ℕ} (D : JetL2 μ (K + 1) E) :
    0 ≤ gradFactorialNormSq ρ D :=
  Finset.sum_nonneg fun j _ => mul_nonneg (factorialWeight_nonneg ρ j.val)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- The gradient factorial norm is at most the full factorial norm at the next radius scale:
in particular it is bounded by a multiple of the unweighted norm. -/
theorem gradFactorialNormSq_le (ρ : ℝ) {K : ℕ} (D : JetL2 μ (K + 1) E) :
    gradFactorialNormSq ρ D ≤ factorialWeightMax ρ K * ‖D‖ ^ 2 := by
  rw [jet_norm_sq_eq_sum]
  unfold gradFactorialNormSq
  calc ∑ j : Fin (K + 1), factorialWeight ρ j.val *
        ∑ w : DerivativeWord2 (j.val + 1), ‖D ⟨⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩, w⟩‖ ^ 2
      ≤ ∑ j : Fin (K + 1), factorialWeightMax ρ K *
          derivativeNormSq D ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ := by
        refine Finset.sum_le_sum fun j _ => ?_
        exact mul_le_mul_of_nonneg_right (factorialWeight_le_max ρ j)
          (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    _ = factorialWeightMax ρ K * ∑ j : Fin (K + 1),
          derivativeNormSq D ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ := by rw [Finset.mul_sum]
    _ ≤ factorialWeightMax ρ K * ∑ j : Fin (K + 1 + 1), derivativeNormSq D j := by
        have hmax : 0 ≤ factorialWeightMax ρ K :=
          (factorialWeight_nonneg ρ 0).trans (factorialWeight_le_max ρ ⟨0, Nat.succ_pos K⟩)
        refine mul_le_mul_of_nonneg_left ?_ hmax
        rw [Fin.sum_univ_succ (f := fun j : Fin (K + 1 + 1) => derivativeNormSq D j)]
        exact le_add_of_nonneg_of_le (derivativeNormSq_nonneg D 0) le_rfl

variable {ν : Measure ℝ}

section Torus
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F]
  [BorelSpace F] [CompleteSpace F]

/-- The factorial norm of a square-integrable family of periodic Sobolev fields is integrable. -/
theorem integrable_factorialNormSq_torus {ρ : ℝ} {K : ℕ} {U : ℝ → TorusHk K F}
    (hU : MemLp U 2 ν) : Integrable (fun s => factorialNormSq ρ (U s).val) ν := by
  have hsq : Integrable (fun s => ‖U s‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm hU.aestronglyMeasurable).1 hU
  refine (hsq.const_mul (factorialWeightMax ρ K)).mono'
    (((continuous_factorialNormSq ρ K).comp continuous_subtype_val).comp_aestronglyMeasurable
      hU.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun s => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (factorialNormSq_nonneg ρ _)]
  exact factorialNormSq_upper ρ (U s).val

/-- The gradient factorial norm of a square-integrable family of periodic Sobolev fields is
integrable. -/
theorem integrable_gradFactorialNormSq_torus {ρ : ℝ} {K : ℕ} {U : ℝ → TorusHk (K + 1) F}
    (hU : MemLp U 2 ν) : Integrable (fun s => gradFactorialNormSq ρ (U s).val) ν := by
  have hsq : Integrable (fun s => ‖U s‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm hU.aestronglyMeasurable).1 hU
  refine (hsq.const_mul (factorialWeightMax ρ K)).mono'
    (((continuous_gradFactorialNormSq ρ K).comp continuous_subtype_val).comp_aestronglyMeasurable
      hU.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun s => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (gradFactorialNormSq_nonneg ρ _)]
  exact gradFactorialNormSq_le ρ (U s).val

end Torus
end

/-! A periodic Sobolev field is determined by its pairings with smooth periodic test fields. -/

section
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- **Uniqueness from pairings.** -/
theorem torusHk_eq_of_cellInner {K : ℕ} {X Y : TorusHk K F}
    (h : ∀ ψ : Vec 2 → F, ContDiff ℝ (⊤ : ℕ∞) ψ → AVenhance.IsZ2Periodic ψ →
      cellInner (tval X) ψ = cellInner (tval Y) ψ) : X = Y := by
  apply tvalL2_injective
  set d := tvalL2 X - tvalL2 Y
  have hS : ∀ f ∈ {f : Lp F 2 (volume.restrict AVenhance.unitCube) |
      ∃ ψ : Vec 2 → F, ContDiff ℝ (⊤ : ℕ∞) ψ ∧ AVenhance.IsZ2Periodic ψ ∧
        f =ᵐ[volume.restrict AVenhance.unitCube] ψ}, inner ℝ d f = 0 := by
    rintro f ⟨ψ, hψ, hp, hf⟩
    rw [inner_sub_left, inner_tvalL2 X f ψ hf, inner_tvalL2 Y f ψ hf, h ψ hψ hp, sub_self]
  have hclosed : IsClosed {f : Lp F 2 (volume.restrict AVenhance.unitCube) | inner ℝ d f = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hall : ∀ f, inner ℝ d f = 0 := by
    intro f
    have hsub := hclosed.closure_subset_iff.2 hS
    rw [dense_smooth_periodic_lp.closure_eq] at hsub
    exact hsub (Set.mem_univ f)
  have hd : d = 0 := inner_self_eq_zero.1 (hall d)
  exact sub_eq_zero.1 hd
end

end AVRegularity.CycleComparison.Coarse
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Coarse

/-! The flux operators vanish on the zero test field, so the response-flux identity can be
tested one component at a time. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem covPolyP_zero_field (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) :
    covPolyP Hc p (0 : Vec 2 → E) = 0 := by
  unfold covPolyP
  simp [covLin_iterate_zero]

theorem covPolyQ_zero_field (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) :
    covPolyQ Hc p (0 : Vec 2 → E) = 0 := by
  unfold covPolyQ
  simp [covLin_iterate_zero]

theorem orderedDerivativeRev_zero_field {m : ℕ} (α : DerivativeWord2 m) :
    orderedDerivativeRev α (fun _ : Vec 2 => (0 : E)) = fun _ => 0 := by
  unfold orderedDerivativeRev
  induction (List.ofFn α) with
  | nil => rfl
  | cons i l ih =>
      rw [List.foldr_cons, ih]
      funext x
      simp

theorem wordAdjoint_zero_field (m : ℕ) :
    wordAdjoint m (fun _ : Vec 2 => (0 : PiLp 2 (fun _ : DerivativeWord2 m => E))) =
      fun _ => 0 := by
  funext x
  simp [wordAdjoint, orderedDerivativeRev_zero_field]

@[simp] theorem tensorFluxAdjoint_zero_right {m : ℕ}
    (A : PiLp 2 (fun _ : DerivativeWord2 m => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)) :
    tensorFluxAdjoint A (0 : PiLp 2 (fun _ : Fin 2 => E)) = 0 := by
  unfold tensorFluxAdjoint
  ext α
  simp

theorem commutatorAdjoint_zero_field (b : ℝ → Vec 2 → Vec 2) (Hc : Matrix (Fin 2) (Fin 2) ℝ)
    (t : ℝ) : commutatorAdjoint b Hc t (0 : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) = 0 := by
  funext x
  simp [commutatorAdjoint]

theorem diagonalFluxAdjoint_zero_field (D : ℕ)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (t : ℝ) : diagonalFluxAdjoint D AD t (0 : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) = 0 := by
  funext x
  simp [diagonalFluxAdjoint, wordAdjoint_zero_field]

theorem coarseFluxAdjoint_zero_field (D : ℕ) (b : ℝ → Vec 2 → Vec 2)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (t : ℝ) :
    coarseFluxAdjoint D b AD Hc p t (0 : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) = 0 := by
  unfold coarseFluxAdjoint
  simp [covLin_iterate_zero, commutatorAdjoint_zero_field, diagonalFluxAdjoint_zero_field,
    covPolyP_zero_field]

end AVRegularity.CycleComparison.Coarse
end
