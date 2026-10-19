-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

section
@[expose] public noncomputable section
namespace AVRegularity.CycleWords.Assembly

/-! # The well-buffered case: the regimes from the threshold

A frame is well buffered when `C₀ P^{Q₀}(1+S)^{Q₀}((1+J)e^{-c₀D} + e^{-c₀D_q}) < 1`.
* Every regime `C P^Q (1+J) e^{-cD} ≤ 1` with `C ≤ C₀`, `Q ≤ Q₀`, `c₀ ≤ c` follows
  (`threshold_le`). The activity bound and the slow defect are of this form.
* The terminal quiet stretch is nondegenerate, `0 < D_q` (`threshold_quiet`).
* `ζ²(b − a) ≤ 2C_H(1 + y)²` for `ζ = min 1 (x + S^{-1/2})`, `b − a ≤ C_H S`, `y = x√S`
  (`zeta_window_le`). -/

/-- **The regimes from the threshold.** -/
theorem threshold_le {C₀ c₀ P S J D Dq C c : ℝ} {Q₀ Q : ℕ} (hP : 1 ≤ P) (hS : 0 ≤ S)
    (hJ : 0 ≤ J) (hD : 0 ≤ D) (hC : C ≤ C₀) (hQ : Q ≤ Q₀) (hc : c₀ ≤ c)
    (hth : C₀ * P ^ Q₀ * (1 + S) ^ Q₀ * ((1 + J) * Real.exp (-c₀ * D) + Real.exp (-c₀ * Dq)) < 1) :
    C * P ^ Q * (1 + J) * Real.exp (-c * D) ≤ 1 := by
  have hPQ : 0 ≤ P ^ Q := pow_nonneg (by linarith) _
  have hJ1 : 0 ≤ 1 + J := by linarith
  rcases le_total C 0 with hneg | hpos
  · have : C * P ^ Q * (1 + J) * Real.exp (-c * D) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg hneg hPQ) hJ1) (Real.exp_pos _).le
    linarith
  have hC₀ : 0 ≤ C₀ := hpos.trans hC
  have h1 : P ^ Q ≤ P ^ Q₀ := pow_le_pow_right₀ hP hQ
  have h2 : 1 ≤ (1 + S) ^ Q₀ := one_le_pow₀ (by linarith)
  have h3 : Real.exp (-c * D) ≤ Real.exp (-c₀ * D) := Real.exp_le_exp.2 (by nlinarith)
  have hPQ₀ : 0 ≤ P ^ Q₀ := pow_nonneg (by linarith) _
  have hA : C * P ^ Q ≤ C₀ * P ^ Q₀ * (1 + S) ^ Q₀ := by
    calc C * P ^ Q ≤ C₀ * P ^ Q₀ := mul_le_mul hC h1 hPQ hC₀
      _ = C₀ * P ^ Q₀ * 1 := (mul_one _).symm
      _ ≤ C₀ * P ^ Q₀ * (1 + S) ^ Q₀ := mul_le_mul_of_nonneg_left h2 (mul_nonneg hC₀ hPQ₀)
  have hB : (1 + J) * Real.exp (-c * D) ≤
      (1 + J) * Real.exp (-c₀ * D) + Real.exp (-c₀ * Dq) := by
    have := mul_le_mul_of_nonneg_left h3 hJ1
    linarith [Real.exp_pos (-c₀ * Dq)]
  have hX0 : 0 ≤ C * P ^ Q := mul_nonneg hpos hPQ
  calc C * P ^ Q * (1 + J) * Real.exp (-c * D)
      = (C * P ^ Q) * ((1 + J) * Real.exp (-c * D)) := by ring
    _ ≤ (C₀ * P ^ Q₀ * (1 + S) ^ Q₀) *
        ((1 + J) * Real.exp (-c₀ * D) + Real.exp (-c₀ * Dq)) :=
        mul_le_mul hA hB (mul_nonneg hJ1 (Real.exp_pos _).le) (hX0.trans hA)
    _ ≤ 1 := hth.le

/-- **The terminal quiet stretch is nondegenerate.** -/
theorem threshold_quiet {C₀ c₀ P S J D Dq : ℝ} {Q₀ : ℕ} (hC₀ : 1 ≤ C₀)
    (hP : 1 ≤ P) (hS : 0 ≤ S) (hJ : 0 ≤ J) (hDq : 0 ≤ Dq)
    (hth : C₀ * P ^ Q₀ * (1 + S) ^ Q₀ * ((1 + J) * Real.exp (-c₀ * D) + Real.exp (-c₀ * Dq)) < 1) :
    0 < Dq := by
  rcases hDq.lt_or_eq with h | h
  · exact h
  exfalso
  rw [← h, mul_zero, Real.exp_zero] at hth
  have hX : 1 ≤ C₀ * P ^ Q₀ * (1 + S) ^ Q₀ :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC₀ (one_le_pow₀ hP))
      (one_le_pow₀ (by linarith))
  have hY : 1 ≤ (1 + J) * Real.exp (-c₀ * D) + 1 := by
    have := mul_nonneg (show (0 : ℝ) ≤ 1 + J by linarith) (Real.exp_pos (-c₀ * D)).le
    linarith
  have := one_le_mul_of_one_le_of_one_le hX hY
  linarith

/-- **The window factor of `ζ`.** -/
theorem zeta_window_le {x S CH T y : ℝ} (hx : 0 ≤ x) (hS : 0 < S) (hCH : 0 ≤ CH)
    (hT : T ≤ CH * S) (hy : y = x * Real.sqrt S) :
    min 1 (x + (Real.sqrt S)⁻¹) ^ 2 * T ≤ 2 * CH * (1 + y) ^ 2 := by
  have hs : 0 < Real.sqrt S := Real.sqrt_pos.2 hS
  have hss : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS.le
  set z := min 1 (x + (Real.sqrt S)⁻¹) with hz
  have hz0 : 0 ≤ z := le_min zero_le_one (add_nonneg hx (inv_nonneg.2 hs.le))
  have hzle : z ≤ x + (Real.sqrt S)⁻¹ := min_le_right _ _
  have hinv : (Real.sqrt S)⁻¹ * Real.sqrt S = 1 := inv_mul_cancel₀ hs.ne'
  -- `z √S ≤ y + 1`
  have hzs : z * Real.sqrt S ≤ y + 1 := by
    calc z * Real.sqrt S ≤ (x + (Real.sqrt S)⁻¹) * Real.sqrt S :=
          mul_le_mul_of_nonneg_right hzle hs.le
      _ = y + 1 := by rw [add_mul, hinv, hy]
  have hzs0 : 0 ≤ z * Real.sqrt S := mul_nonneg hz0 hs.le
  have hsq : z ^ 2 * S ≤ (1 + y) ^ 2 := by
    have := pow_le_pow_left₀ hzs0 hzs 2
    rw [mul_pow, hss] at this
    linarith
  have hy0 : 0 ≤ y := hy ▸ mul_nonneg hx (Real.sqrt_nonneg _)
  calc z ^ 2 * T ≤ z ^ 2 * (CH * S) := mul_le_mul_of_nonneg_left hT (sq_nonneg z)
    _ = CH * (z ^ 2 * S) := by ring
    _ ≤ CH * (1 + y) ^ 2 := mul_le_mul_of_nonneg_left hsq hCH
    _ ≤ 2 * CH * (1 + y) ^ 2 := by nlinarith [sq_nonneg (1 + y)]

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public section
namespace AVRegularity.CycleWords.Assembly

/-! # Jet-to-value transfer: the coefficients

One letter `k` splits each term into a term with the same moment and a term with the moment
lowered in the direction `k`, the latter with the factor `β_k - a_k`. The coefficients
`C(c,a) β^{(a)}` absorb this by Pascal's rule and `β^{(a+1)} = (β - a) β^{(a)}`
(`sum_choose_descFactorial_succ`); on the product of ranges this is `transferSum_step_zero` and
`transferSum_step_one`. -/

/-- **Pascal's rule with descending factorials.** -/
theorem sum_choose_descFactorial_succ (c b : ℕ) (F : ℕ → ℂ) :
    ∑ i ∈ Finset.range (c + 2), ((c + 1).choose i : ℂ) * (b.descFactorial i : ℂ) * F i =
      ∑ i ∈ Finset.range (c + 1), (c.choose i : ℂ) * (b.descFactorial i : ℂ) *
        (F i + ((b - i : ℕ) : ℂ) * F (i + 1)) := by
  have hd : ∀ i, ((b.descFactorial (i + 1) : ℕ) : ℂ) =
      ((b - i : ℕ) : ℂ) * (b.descFactorial i : ℂ) := fun i => by
    rw [Nat.descFactorial_succ]
    push_cast
    ring
  have h1 : ∑ i ∈ Finset.range (c + 1), (c.choose i : ℂ) * (b.descFactorial i : ℂ) *
        (F i + ((b - i : ℕ) : ℂ) * F (i + 1)) =
      ∑ i ∈ Finset.range (c + 1), (c.choose i : ℂ) * (b.descFactorial i : ℂ) * F i +
        ∑ i ∈ Finset.range (c + 1), (c.choose i : ℂ) * (b.descFactorial (i + 1) : ℂ) *
          F (i + 1) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hd]
    ring
  have h2 : ∑ i ∈ Finset.range (c + 1), ((c + 1).choose (i + 1) : ℂ) *
        (b.descFactorial (i + 1) : ℂ) * F (i + 1) =
      ∑ i ∈ Finset.range (c + 1), (c.choose i : ℂ) * (b.descFactorial (i + 1) : ℂ) *
          F (i + 1) +
        ∑ i ∈ Finset.range (c + 1), (c.choose (i + 1) : ℂ) * (b.descFactorial (i + 1) : ℂ) *
          F (i + 1) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.choose_succ_succ']
    push_cast
    ring
  have h3 : ∑ i ∈ Finset.range (c + 1), (c.choose (i + 1) : ℂ) * (b.descFactorial (i + 1) : ℂ) *
        F (i + 1) =
      ∑ i ∈ Finset.range c, (c.choose (i + 1) : ℂ) * (b.descFactorial (i + 1) : ℂ) *
        F (i + 1) := by
    rw [Finset.sum_range_succ, Nat.choose_succ_self]
    simp
  rw [h1, Finset.sum_range_succ' _ (c + 1), h2, h3,
    Finset.sum_range_succ' (fun i => (c.choose i : ℂ) * (b.descFactorial i : ℂ) * F i) c]
  simp only [Nat.choose_zero_right, Nat.descFactorial_zero, Nat.cast_one, one_mul]
  ring

/-- The coefficient `C(c,a) β^{(a)}` of the transfer. -/
def transferCoef (c β a : ℕ × ℕ) : ℂ :=
  (((c.1.choose a.1 * c.2.choose a.2 * β.1.descFactorial a.1 * β.2.descFactorial a.2 : ℕ)) : ℂ)

/-- The transfer sum `∑_{a ≤ c} C(c,a) β^{(a)} X(a)`. -/
def transferSum (c β : ℕ × ℕ) (X : ℕ × ℕ → ℂ) : ℂ :=
  ∑ a ∈ Finset.range (c.1 + 1) ×ˢ Finset.range (c.2 + 1), transferCoef c β a * X a

/-- **A letter `0`.** -/
theorem transferSum_step_zero (c β : ℕ × ℕ) (X : ℕ × ℕ → ℂ) :
    transferSum (c.1 + 1, c.2) β X =
      ∑ a ∈ Finset.range (c.1 + 1) ×ˢ Finset.range (c.2 + 1), transferCoef c β a *
        (X a + ((β.1 - a.1 : ℕ) : ℂ) * X (a.1 + 1, a.2)) := by
  unfold transferSum
  rw [Finset.sum_product, Finset.sum_product]
  have hL : ∀ i, ∑ j ∈ Finset.range (c.2 + 1), transferCoef (c.1 + 1, c.2) β (i, j) * X (i, j) =
      ((c.1 + 1).choose i : ℂ) * (β.1.descFactorial i : ℂ) *
        ∑ j ∈ Finset.range (c.2 + 1), (c.2.choose j : ℂ) * (β.2.descFactorial j : ℂ) *
          X (i, j) := fun i => by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [transferCoef]
    push_cast
    ring
  simp only [hL]
  rw [sum_choose_descFactorial_succ c.1 β.1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [transferCoef]
  push_cast
  ring

/-- **A letter `1`.** -/
theorem transferSum_step_one (c β : ℕ × ℕ) (X : ℕ × ℕ → ℂ) :
    transferSum (c.1, c.2 + 1) β X =
      ∑ a ∈ Finset.range (c.1 + 1) ×ˢ Finset.range (c.2 + 1), transferCoef c β a *
        (X a + ((β.2 - a.2 : ℕ) : ℂ) * X (a.1, a.2 + 1)) := by
  unfold transferSum
  rw [Finset.sum_product, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hL : ∑ j ∈ Finset.range (c.2 + 1 + 1), transferCoef (c.1, c.2 + 1) β (i, j) * X (i, j) =
      (c.1.choose i : ℂ) * (β.1.descFactorial i : ℂ) *
        ∑ j ∈ Finset.range (c.2 + 2), ((c.2 + 1).choose j : ℂ) * (β.2.descFactorial j : ℂ) *
          X (i, j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [transferCoef]
    push_cast
    ring
  rw [hL, sum_choose_descFactorial_succ c.2 β.2 (fun j => X (i, j)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [transferCoef]
  push_cast
  ring

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public noncomputable section
open Module
namespace AVRegularity.CycleWords.Assembly

/-! # Parseval on the basis for the letter blocks

For `M : H₂ →L H₁` between finite-dimensional real Hilbert spaces with orthonormal bases `e` of `H₁`
and `e'` of `H₂`, the matrix `mat b b' = ⟨M* e_b, e'_{b'}⟩` and a bounded `A : X →L Y` between
real Hilbert spaces, the block operator `T b b' = mat b b' • A` obeys
`∑_{b'} ‖∑_b T b b' (f b)‖² ≤ (‖M‖ ‖A‖)² ∑_b ‖f b‖²` (`blockBound_mat_smul`).  `BlockBound c T` is
closed under sums (`BlockBound.sum`, `BlockBound.list_sum`), which carries the bound through the
nested sums over the terms of the letter transform. -/

section Bessel

variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [FiniteDimensional ℝ H₁]
  [FiniteDimensional ℝ H₂] {m₁ m₂ : ℕ}

/-- The matrix of `M*` between orthonormal bases: `⟨M* e_b, e'_{b'}⟩`. -/
def letterMat (e : OrthonormalBasis (Fin m₁) ℝ H₁) (e' : OrthonormalBasis (Fin m₂) ℝ H₂)
    (M : H₂ →L[ℝ] H₁) (b : Fin m₁) (b' : Fin m₂) : ℝ :=
  inner ℝ (ContinuousLinearMap.adjoint M (e b)) (e' b')

theorem letterMat_scalar_bessel (e : OrthonormalBasis (Fin m₁) ℝ H₁)
    (e' : OrthonormalBasis (Fin m₂) ℝ H₂) (M : H₂ →L[ℝ] H₁) (y : Fin m₁ → ℝ) :
    ∑ b', (∑ b, letterMat e e' M b b' * y b) ^ 2 ≤ ‖M‖ ^ 2 * ∑ b, y b ^ 2 := by
  set v : H₁ := ∑ b, y b • e b with hv
  have h1 : ∀ b', ∑ b, letterMat e e' M b b' * y b =
      inner ℝ (e' b') (ContinuousLinearMap.adjoint M v) := by
    intro b'
    rw [real_inner_comm, ContinuousLinearMap.adjoint_inner_left, hv, sum_inner]
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold letterMat
    rw [inner_smul_left, ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.adjoint_inner_left,
      real_inner_comm]
    simp [mul_comm]
  have h2 : ∑ b', (∑ b, letterMat e e' M b b' * y b) ^ 2 =
      ‖ContinuousLinearMap.adjoint M v‖ ^ 2 := by
    rw [← e'.sum_sq_norm_inner_right (ContinuousLinearMap.adjoint M v)]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [h1, Real.norm_eq_abs, sq_abs]
  have h3 : ‖v‖ ^ 2 = ∑ b, y b ^ 2 := by
    rw [← e.sum_sq_norm_inner_right v]
    refine Finset.sum_congr rfl fun c _ => ?_
    have : inner ℝ (e c) v = y c := by
      rw [hv, inner_sum]
      simp [inner_smul_right, orthonormal_iff_ite.1 e.orthonormal c]
    rw [this, Real.norm_eq_abs, sq_abs]
  rw [h2, ← h3, ← mul_pow]
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  have hn : ‖ContinuousLinearMap.adjoint M‖ = ‖M‖ := ContinuousLinearMap.adjoint.norm_map M
  exact (ContinuousLinearMap.le_opNorm _ _).trans (by rw [hn])

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

theorem letterMat_bessel_hilbert (e : OrthonormalBasis (Fin m₁) ℝ H₁)
    (e' : OrthonormalBasis (Fin m₂) ℝ H₂) (M : H₂ →L[ℝ] H₁) (f : Fin m₁ → X) :
    ∑ b', ‖∑ b, letterMat e e' M b b' • f b‖ ^ 2 ≤ ‖M‖ ^ 2 * ∑ b, ‖f b‖ ^ 2 := by
  classical
  let W : Submodule ℝ X := Submodule.span ℝ (Set.range f)
  have : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ (Set.finite_range f)
  let u := stdOrthonormalBasis ℝ W
  have hf : ∀ b, f b ∈ W := fun b => Submodule.subset_span ⟨b, rfl⟩
  let fW : Fin m₁ → W := fun b => ⟨f b, hf b⟩
  have hsum : ∀ b', ∑ b, letterMat e e' M b b' • f b = ((∑ b, letterMat e e' M b b' • fW b : W) : X) := by
    intro b'
    simp [fW]
  have key : ∀ b', ‖∑ b, letterMat e e' M b b' • f b‖ ^ 2 =
      ∑ j, (∑ b, letterMat e e' M b b' * inner ℝ (u j) (fW b)) ^ 2 := by
    intro b'
    rw [hsum, Submodule.norm_coe, ← u.sum_sq_norm_inner_right]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Real.norm_eq_abs, sq_abs, inner_sum]
    simp only [inner_smul_right]
  simp only [key]
  rw [Finset.sum_comm]
  calc _ ≤ ∑ j, ‖M‖ ^ 2 * ∑ b, inner ℝ (u j) (fW b) ^ 2 :=
        Finset.sum_le_sum fun j _ => letterMat_scalar_bessel e e' M (fun b => inner ℝ (u j) (fW b))
    _ = ‖M‖ ^ 2 * ∑ b, ∑ j, inner ℝ (u j) (fW b) ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ = ‖M‖ ^ 2 * ∑ b, ‖f b‖ ^ 2 := by
        congr 1
        refine Finset.sum_congr rfl fun b _ => ?_
        have e0 : ‖f b‖ = ‖fW b‖ := (Submodule.norm_coe (fW b)).symm
        rw [e0, ← u.sum_sq_norm_inner_right (fW b)]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Real.norm_eq_abs, sq_abs]

/-- The block bound of a family of operators `T b b' : X →L Y`. -/
def BlockBound {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] (c : ℝ)
    (T : Fin m₁ → Fin m₂ → X →L[ℝ] Y) : Prop :=
  0 ≤ c ∧ ∀ f : Fin m₁ → X, ∑ b', ‖∑ b, T b b' (f b)‖ ^ 2 ≤ c ^ 2 * ∑ b, ‖f b‖ ^ 2

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

theorem blockBound_mat_smul (e : OrthonormalBasis (Fin m₁) ℝ H₁)
    (e' : OrthonormalBasis (Fin m₂) ℝ H₂) (M : H₂ →L[ℝ] H₁) (A : X →L[ℝ] Y) :
    BlockBound (‖M‖ * ‖A‖) (fun b b' => letterMat e e' M b b' • A) := by
  refine ⟨by positivity, fun f => ?_⟩
  have h1 : ∀ b', ∑ b, (letterMat e e' M b b' • A) (f b) =
      A (∑ b, letterMat e e' M b b' • f b) := by
    intro b'
    simp [map_sum]
  simp only [h1]
  calc ∑ b', ‖A (∑ b, letterMat e e' M b b' • f b)‖ ^ 2
      ≤ ∑ b', (‖A‖ * ‖∑ b, letterMat e e' M b b' • f b‖) ^ 2 :=
        Finset.sum_le_sum fun b' _ => pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm _) 2
    _ = ‖A‖ ^ 2 * ∑ b', ‖∑ b, letterMat e e' M b b' • f b‖ ^ 2 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ ‖A‖ ^ 2 * (‖M‖ ^ 2 * ∑ b, ‖f b‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (letterMat_bessel_hilbert e e' M f) (by positivity)
    _ = (‖M‖ * ‖A‖) ^ 2 * ∑ b, ‖f b‖ ^ 2 := by ring

theorem BlockBound.zero : BlockBound (X := X) (Y := Y) (m₁ := m₁) (m₂ := m₂) 0 (fun _ _ => 0) :=
  ⟨le_rfl, fun f => by simp⟩

theorem BlockBound.mono {c c' : ℝ} {T : Fin m₁ → Fin m₂ → X →L[ℝ] Y} (h : BlockBound c T)
    (hc : c ≤ c') : BlockBound c' T :=
  ⟨h.1.trans hc, fun f => (h.2 f).trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ h.1 hc 2) (Finset.sum_nonneg fun _ _ => by positivity))⟩

theorem BlockBound.add {c c' : ℝ} {T T' : Fin m₁ → Fin m₂ → X →L[ℝ] Y} (h : BlockBound c T)
    (h' : BlockBound c' T') : BlockBound (c + c') (fun b b' => T b b' + T' b b') := by
  refine ⟨add_nonneg h.1 h'.1, fun f => ?_⟩
  set R := ∑ b, ‖f b‖ ^ 2 with hR
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun _ _ => by positivity
  have n1 := h.2 f
  have n2 := h'.2 f
  let g : Fin m₂ → Y := fun b' => ∑ b, T b b' (f b)
  let g' : Fin m₂ → Y := fun b' => ∑ b, T' b b' (f b)
  have hsq : ∀ q : Fin m₂ → Y, ‖(WithLp.toLp 2 q : PiLp 2 fun _ : Fin m₂ => Y)‖ ^ 2 =
      ∑ b', ‖q b'‖ ^ 2 := fun q => PiLp.norm_sq_eq_of_L2 _ _
  have e1 : ‖(WithLp.toLp 2 g : PiLp 2 fun _ : Fin m₂ => Y)‖ ≤ c * Real.sqrt R := by
    rw [← Real.sqrt_sq (norm_nonneg _), hsq, ← Real.sqrt_sq h.1, ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt (n1.trans_eq (by ring))
  have e2 : ‖(WithLp.toLp 2 g' : PiLp 2 fun _ : Fin m₂ => Y)‖ ≤ c' * Real.sqrt R := by
    rw [← Real.sqrt_sq (norm_nonneg _), hsq, ← Real.sqrt_sq h'.1, ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt (n2.trans_eq (by ring))
  have e3 : ‖(WithLp.toLp 2 (fun b' => ∑ b, (T b b' + T' b b') (f b)) : PiLp 2 fun _ : Fin m₂ => Y)‖
      ≤ (c + c') * Real.sqrt R := by
    have : (WithLp.toLp 2 (fun b' => ∑ b, (T b b' + T' b b') (f b)) : PiLp 2 fun _ : Fin m₂ => Y) =
        WithLp.toLp 2 g + WithLp.toLp 2 g' := by
      ext b'
      simp [g, g', Finset.sum_add_distrib]
    rw [this]
    exact (norm_add_le _ _).trans (by linarith)
  have hs : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR0
  calc ∑ b', ‖∑ b, (T b b' + T' b b') (f b)‖ ^ 2
      = ‖(WithLp.toLp 2 (fun b' => ∑ b, (T b b' + T' b b') (f b)) : PiLp 2 fun _ : Fin m₂ => Y)‖ ^ 2 :=
        (hsq _).symm
    _ ≤ ((c + c') * Real.sqrt R) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) e3 2
    _ = (c + c') ^ 2 * R := by rw [mul_pow, hs]

theorem BlockBound.finset_sum {κ : Type*} (s : Finset κ) {c : κ → ℝ}
    {T : κ → Fin m₁ → Fin m₂ → X →L[ℝ] Y} (h : ∀ k ∈ s, BlockBound (c k) (T k)) :
    BlockBound (∑ k ∈ s, c k) (fun b b' => ∑ k ∈ s, T k b b') := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using BlockBound.zero
  | insert a s ha ih =>
    have := (h a (Finset.mem_insert_self a s)).add (ih fun k hk => h k (Finset.mem_insert_of_mem hk))
    simpa [Finset.sum_insert ha] using this

theorem BlockBound.list_sum {κ : Type*} (l : List κ) {c : κ → ℝ}
    {T : κ → Fin m₁ → Fin m₂ → X →L[ℝ] Y} (h : ∀ k ∈ l, BlockBound (c k) (T k)) :
    BlockBound (l.map c).sum (fun b b' => (l.map fun k => T k b b').sum) := by
  induction l with
  | nil => simpa using BlockBound.zero
  | cons a l ih =>
    have := (h a List.mem_cons_self).add (ih fun k hk => h k (List.mem_cons_of_mem _ hk))
    simpa using this

theorem BlockBound.smul {c : ℝ} {T : Fin m₁ → Fin m₂ → X →L[ℝ] Y} (h : BlockBound c T) (a : ℝ) :
    BlockBound (|a| * c) (fun b b' => a • T b b') := by
  refine ⟨mul_nonneg (abs_nonneg _) h.1, fun f => ?_⟩
  have e : ∀ b', ‖∑ b, (a • T b b') (f b)‖ ^ 2 = a ^ 2 * ‖∑ b, T b b' (f b)‖ ^ 2 := by
    intro b'
    simp only [smul_apply, ← Finset.smul_sum, norm_smul, Real.norm_eq_abs]
    rw [mul_pow, sq_abs]
  simp only [e, ← Finset.mul_sum]
  calc _ ≤ a ^ 2 * (c ^ 2 * ∑ b, ‖f b‖ ^ 2) := mul_le_mul_of_nonneg_left (h.2 f) (sq_nonneg _)
    _ = _ := by rw [mul_pow, sq_abs]; ring

end Bessel

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public section
namespace AVRegularity.CycleWords.Assembly

/-! # the Schur test for families of bounded operators between normed spaces

If
`T g g' : E g →L H g'` has `‖T g g'‖ ≤ w g g'`, with `w ≥ 0` of row sums at most `A` and column sums
at most `B`, then `∑_{g'} ‖∑_g T g g' ψ_g‖² ≤ A B ∑_g ‖ψ_g‖²`. -/

/-- **Schur test for vectors**: `y g g'` has norm at most `w g g' a g`; the sums of `y` over `g`
have squared norms summing to at most `A B ∑ a²`, with sums over finsets of indices. -/
theorem elem_schur {G G' : Type*} {H : G' → Type*} [∀ g', NormedAddCommGroup (H g')]
    (s : Finset G) (s' : Finset G') (y : G → ∀ g', H g') (w : G → G' → ℝ) (a : G → ℝ)
    (hw0 : ∀ g g', 0 ≤ w g g') (hy : ∀ g ∈ s, ∀ g' ∈ s', ‖y g g'‖ ≤ w g g' * a g)
    {A B : ℝ} (hA : ∀ g ∈ s, ∑ g' ∈ s', w g g' ≤ A) (hB : ∀ g' ∈ s', ∑ g ∈ s, w g g' ≤ B)
    (hB0 : 0 ≤ B) :
    ∑ g' ∈ s', ‖∑ g ∈ s, y g g'‖ ^ 2 ≤ A * B * ∑ g ∈ s, a g ^ 2 := by
  have hone : ∀ g' ∈ s', ‖∑ g ∈ s, y g g'‖ ^ 2 ≤ B * ∑ g ∈ s, w g g' * a g ^ 2 := by
    intro g' hg'
    have h1 : ‖∑ g ∈ s, y g g'‖ ≤ ∑ g ∈ s, w g g' * a g :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun g hg => hy g hg g' hg')
    have h2 : (∑ g ∈ s, w g g' * a g) ^ 2 ≤ (∑ g ∈ s, w g g') * ∑ g ∈ s, w g g' * a g ^ 2 := by
      have := Finset.sum_mul_sq_le_sq_mul_sq s (fun g => Real.sqrt (w g g'))
        (fun g => Real.sqrt (w g g') * a g)
      have e1 : ∀ g, Real.sqrt (w g g') * (Real.sqrt (w g g') * a g) = w g g' * a g := by
        intro g
        rw [← mul_assoc, Real.mul_self_sqrt (hw0 g g')]
      have e2 : ∀ g, Real.sqrt (w g g') ^ 2 = w g g' := fun g => Real.sq_sqrt (hw0 g g')
      have e3 : ∀ g, (Real.sqrt (w g g') * a g) ^ 2 = w g g' * a g ^ 2 := by
        intro g
        rw [mul_pow, e2]
      simpa only [e1, e2, e3] using this
    have h3 : 0 ≤ ∑ g ∈ s, w g g' * a g ^ 2 :=
      Finset.sum_nonneg fun g _ => mul_nonneg (hw0 g g') (sq_nonneg _)
    calc ‖∑ g ∈ s, y g g'‖ ^ 2 ≤ (∑ g ∈ s, w g g' * a g) ^ 2 := by
          refine pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∑ g ∈ s, w g g') * ∑ g ∈ s, w g g' * a g ^ 2 := h2
      _ ≤ B * ∑ g ∈ s, w g g' * a g ^ 2 := mul_le_mul_of_nonneg_right (hB g' hg') h3
  calc ∑ g' ∈ s', ‖∑ g ∈ s, y g g'‖ ^ 2 ≤ ∑ g' ∈ s', B * ∑ g ∈ s, w g g' * a g ^ 2 :=
        Finset.sum_le_sum fun g' hg' => hone g' hg'
    _ = B * ∑ g ∈ s, (∑ g' ∈ s', w g g') * a g ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [Finset.sum_mul]
    _ ≤ B * ∑ g ∈ s, A * a g ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun g hg => ?_) hB0
        exact mul_le_mul_of_nonneg_right (hA g hg) (sq_nonneg _)
    _ = A * B * ∑ g ∈ s, a g ^ 2 := by
        rw [← Finset.mul_sum]; ring

/-- **Schur test over fibres of a key map.** The pair operators `T i i'` are bounded on the blocks
`{i : key i = g}`, `{i' : key i' = g'}` by `w g g'`; the sum over all pairs obeys the Schur bound. -/
theorem fibre_schur {B G Y : Type*} [DecidableEq G] [Fintype B]
    [NormedAddCommGroup Y] (key : B → G) (stk stk' : Finset B)
    (z : B → B → Y) (ψn : B → ℝ) (w : G → G → ℝ) (hw0 : ∀ g g', 0 ≤ w g g')
    {A Bc : ℝ} (hA : ∀ g ∈ stk.image key, ∑ g' ∈ stk'.image key, w g g' ≤ A)
    (hB : ∀ g' ∈ stk'.image key, ∑ g ∈ stk.image key, w g g' ≤ Bc) (hB0 : 0 ≤ Bc)
    (hblock : ∀ g ∈ stk.image key, ∀ g' ∈ stk'.image key,
      ∑ i' ∈ stk'.filter (fun i' => key i' = g'),
        ‖∑ i ∈ stk.filter (fun i => key i = g), z i i'‖ ^ 2 ≤
          w g g' ^ 2 * ∑ i ∈ stk.filter (fun i => key i = g), ψn i ^ 2) :
    ∑ i' ∈ stk', ‖∑ i ∈ stk, z i i'‖ ^ 2 ≤ A * Bc * ∑ i ∈ stk, ψn i ^ 2 := by
  classical
  set Fi : G → Finset B := fun g => stk.filter fun i => key i = g with hFi
  set Fo : G → Finset B := fun g => stk'.filter fun i => key i = g with hFo
  let y : G → G → PiLp 2 (fun _ : B => Y) := fun g g' =>
    WithLp.toLp 2 (fun i' => if i' ∈ Fo g' then ∑ i ∈ Fi g, z i i' else 0)
  let a : G → ℝ := fun g => Real.sqrt (∑ i ∈ Fi g, ψn i ^ 2)
  have hnormy : ∀ g g', ‖y g g'‖ ^ 2 = ∑ i' ∈ Fo g', ‖∑ i ∈ Fi g, z i i'‖ ^ 2 := by
    intro g g'
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [y]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i' => i' ∈ Fo g')]
    rw [Finset.sum_eq_zero (s := Finset.univ.filter fun i' => i' ∉ Fo g') (by
      intro i' hi'
      have hn : i' ∉ Fo g' := (Finset.mem_filter.1 hi').2
      simp [hn]), add_zero]
    refine Finset.sum_congr (by ext; simp) fun i' hi' => ?_
    have hm : i' ∈ Fo g' := hi'
    simp only [hm, ↓reduceIte]
  have hmm : ∀ g, a g ^ 2 = ∑ i ∈ Fi g, ψn i ^ 2 := fun g =>
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hyb : ∀ g ∈ stk.image key, ∀ g' ∈ stk'.image key, ‖y g g'‖ ≤ w g g' * a g := by
    intro g hg g' hg'
    refine (pow_le_pow_iff_left₀ (norm_nonneg _)
      (mul_nonneg (hw0 g g') (Real.sqrt_nonneg _)) two_ne_zero).1 ?_
    rw [hnormy, mul_pow, hmm]
    exact hblock g hg g' hg'
  have key' := elem_schur (stk.image key) (stk'.image key) y w a hw0 hyb hA hB hB0
  have hin : ∑ g ∈ stk.image key, a g ^ 2 = ∑ i ∈ stk, ψn i ^ 2 := by
    calc ∑ g ∈ stk.image key, a g ^ 2 = ∑ g ∈ stk.image key, ∑ i ∈ Fi g, ψn i ^ 2 :=
          Finset.sum_congr rfl fun g _ => hmm g
      _ = _ := Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem _ hi) _
  have hout : ∀ g' ∈ stk'.image key, ‖∑ g ∈ stk.image key, y g g'‖ ^ 2 =
      ∑ i' ∈ Fo g', ‖∑ i ∈ stk, z i i'‖ ^ 2 := by
    intro g' _
    have hsum : ∑ g ∈ stk.image key, y g g' =
        WithLp.toLp 2 (fun i' => if i' ∈ Fo g' then ∑ i ∈ stk, z i i' else 0) := by
      ext i'
      simp only [y, WithLp.ofLp_sum, Finset.sum_apply]
      by_cases hi' : i' ∈ Fo g'
      · simp only [hi', ↓reduceIte]
        exact Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem _ hi)
          (fun i => z i i')
      · simp [hi']
    rw [hsum, PiLp.norm_sq_eq_of_L2]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i' => i' ∈ Fo g')]
    rw [Finset.sum_eq_zero (s := Finset.univ.filter fun i' => i' ∉ Fo g') (by
      intro i' hi'
      have hn : i' ∉ Fo g' := (Finset.mem_filter.1 hi').2
      simp [hn]), add_zero]
    refine Finset.sum_congr (by ext; simp) fun i' hi' => ?_
    have hm : i' ∈ Fo g' := hi'
    simp only [hm, ↓reduceIte]
  calc ∑ i' ∈ stk', ‖∑ i ∈ stk, z i i'‖ ^ 2
      = ∑ g' ∈ stk'.image key, ∑ i' ∈ Fo g', ‖∑ i ∈ stk, z i i'‖ ^ 2 :=
        (Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem _ hi) _).symm
    _ = ∑ g' ∈ stk'.image key, ‖∑ g ∈ stk.image key, y g g'‖ ^ 2 :=
        Finset.sum_congr rfl fun g' hg' => (hout g' hg').symm
    _ ≤ A * Bc * ∑ g ∈ stk.image key, a g ^ 2 := key'
    _ = A * Bc * ∑ i ∈ stk, ψn i ^ 2 := by rw [hin]

end AVRegularity.CycleWords.Assembly
end
end
