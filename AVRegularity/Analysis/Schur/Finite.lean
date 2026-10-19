-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

open scoped BigOperators

namespace AVRegularity.Analysis.Schur

variable {ι κ : Type*}

/-- Finite Schur test: both row and column budgets control the bilinear form. -/
theorem finiteSchurBilinear (s : Finset ι) (t : Finset κ)
    (b : ι → κ → ℝ) (x : ι → ℝ) (y : κ → ℝ) (θ : ℝ)
    (hθ : 0 ≤ θ) (hb : ∀ i ∈ s, ∀ j ∈ t, 0 ≤ b i j)
    (hrow : ∀ i ∈ s, ∑ j ∈ t, b i j ≤ θ)
    (hcol : ∀ j ∈ t, ∑ i ∈ s, b i j ≤ θ) :
    (∑ i ∈ s, ∑ j ∈ t, b i j * x i * y j) ≤
      θ * Real.sqrt (∑ i ∈ s, x i ^ 2) * Real.sqrt (∑ j ∈ t, y j ^ 2) := by
  let X : ι × κ → ℝ := fun p => Real.sqrt (b p.1 p.2) * x p.1
  let Y : ι × κ → ℝ := fun p => Real.sqrt (b p.1 p.2) * y p.2
  have hbilinear :
      (∑ i ∈ s, ∑ j ∈ t, b i j * x i * y j) =
        ∑ p ∈ s ×ˢ t, X p * Y p := by
    symm
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    calc
      (Real.sqrt (b i j) * x i) * (Real.sqrt (b i j) * y j) =
          (Real.sqrt (b i j) * Real.sqrt (b i j)) * x i * y j := by ring
      _ = b i j * x i * y j := by rw [Real.mul_self_sqrt (hb i hi j hj)]
  have hXeq :
      (∑ p ∈ s ×ˢ t, X p ^ 2) =
        ∑ i ∈ s, (∑ j ∈ t, b i j) * x i ^ 2 := by
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro i hi
    calc
      (∑ j ∈ t, X (i, j) ^ 2) = ∑ j ∈ t, b i j * x i ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        dsimp [X]
        rw [mul_pow, Real.sq_sqrt (hb i hi j hj)]
      _ = (∑ j ∈ t, b i j) * x i ^ 2 := by rw [← Finset.sum_mul]
  have hYeq :
      (∑ p ∈ s ×ˢ t, Y p ^ 2) =
        ∑ j ∈ t, (∑ i ∈ s, b i j) * y j ^ 2 := by
    rw [Finset.sum_product, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    calc
      (∑ i ∈ s, Y (i, j) ^ 2) = ∑ i ∈ s, b i j * y j ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [Y]
        rw [mul_pow, Real.sq_sqrt (hb i hi j hj)]
      _ = (∑ i ∈ s, b i j) * y j ^ 2 := by rw [← Finset.sum_mul]
  have hXbound :
      (∑ p ∈ s ×ˢ t, X p ^ 2) ≤ θ * ∑ i ∈ s, x i ^ 2 := by
    rw [hXeq]
    calc
      (∑ i ∈ s, (∑ j ∈ t, b i j) * x i ^ 2) ≤
          ∑ i ∈ s, θ * x i ^ 2 :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hrow i hi) (sq_nonneg _)
      _ = θ * ∑ i ∈ s, x i ^ 2 := by rw [Finset.mul_sum]
  have hYbound :
      (∑ p ∈ s ×ˢ t, Y p ^ 2) ≤ θ * ∑ j ∈ t, y j ^ 2 := by
    rw [hYeq]
    calc
      (∑ j ∈ t, (∑ i ∈ s, b i j) * y j ^ 2) ≤
          ∑ j ∈ t, θ * y j ^ 2 :=
        Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right (hcol j hj) (sq_nonneg _)
      _ = θ * ∑ j ∈ t, y j ^ 2 := by rw [Finset.mul_sum]
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (s ×ˢ t) X Y
  have hrootX := Real.sqrt_le_sqrt hXbound
  have hrootY := Real.sqrt_le_sqrt hYbound
  calc
    (∑ i ∈ s, ∑ j ∈ t, b i j * x i * y j) =
        ∑ p ∈ s.product t, X p * Y p := hbilinear
    _ ≤ Real.sqrt (∑ p ∈ s ×ˢ t, X p ^ 2) *
        Real.sqrt (∑ p ∈ s ×ˢ t, Y p ^ 2) := hcs
    _ ≤ Real.sqrt (θ * ∑ i ∈ s, x i ^ 2) *
        Real.sqrt (θ * ∑ j ∈ t, y j ^ 2) :=
      mul_le_mul hrootX hrootY (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = θ * Real.sqrt (∑ i ∈ s, x i ^ 2) *
        Real.sqrt (∑ j ∈ t, y j ^ 2) := by
      calc
        Real.sqrt (θ * ∑ i ∈ s, x i ^ 2) *
            Real.sqrt (θ * ∑ j ∈ t, y j ^ 2) =
          (Real.sqrt θ * Real.sqrt θ) *
            (Real.sqrt (∑ i ∈ s, x i ^ 2) * Real.sqrt (∑ j ∈ t, y j ^ 2)) := by
              rw [Real.sqrt_mul hθ, Real.sqrt_mul hθ]
              ring
        _ = θ * Real.sqrt (∑ i ∈ s, x i ^ 2) *
            Real.sqrt (∑ j ∈ t, y j ^ 2) := by
              rw [Real.mul_self_sqrt hθ]
              ring

private theorem inverseSqrtSquare {π : ℝ} (hπ : 0 < π) :
    (Real.sqrt π)⁻¹ ^ 2 = π⁻¹ := by
  rw [inv_pow, Real.sq_sqrt hπ.le]

private theorem inverseSqrtRatio {πi πj : ℝ} (hi : 0 < πi) (hj : 0 < πj) :
    (Real.sqrt πi)⁻¹ / (Real.sqrt πj)⁻¹ = Real.sqrt (πj / πi) := by
  rw [Real.sqrt_div hj.le]
  field_simp [ne_of_gt (Real.sqrt_pos.mpr hi), ne_of_gt (Real.sqrt_pos.mpr hj)]

/-- Schur bound conjugated by the source inverse square root masses. -/
theorem massSchurBilinear (s : Finset ι) (π : ι → ℝ) (b : ι → ι → ℝ)
    (x y : ι → ℝ) (θ : ℝ)
    (hπ : ∀ i ∈ s, 0 < π i)
    (hb : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ b i j)
    (hθ : 0 ≤ θ)
    (hrow : ∀ i ∈ s,
      ∑ j ∈ s, Real.sqrt (π j / π i) * b i j ≤ θ)
    (hcol : ∀ j ∈ s,
      ∑ i ∈ s, Real.sqrt (π j / π i) * b i j ≤ θ) :
    (∑ i ∈ s, ∑ j ∈ s, (π i)⁻¹ * b i j * x i * y j) ≤
      θ * Real.sqrt (∑ i ∈ s, (π i)⁻¹ * x i ^ 2) *
        Real.sqrt (∑ j ∈ s, (π j)⁻¹ * y j ^ 2) := by
  let w : ι → ℝ := fun i => (Real.sqrt (π i))⁻¹
  have hnorm : ∀ i ∈ s, ∀ j ∈ s,
      (π i)⁻¹ * b i j * x i * y j =
        (Real.sqrt (π j / π i) * b i j) * (w i * x i) * (w j * y j) := by
    intro i hi j hj
    dsimp [w]
    rw [← inverseSqrtSquare (hπ i hi), ← inverseSqrtRatio (hπ i hi) (hπ j hj)]
    field_simp [ne_of_gt (Real.sqrt_pos.mpr (hπ i hi)),
      ne_of_gt (Real.sqrt_pos.mpr (hπ j hj))]
  have hs := finiteSchurBilinear s s
    (fun i j => Real.sqrt (π j / π i) * b i j)
    (fun i => w i * x i) (fun j => w j * y j) θ hθ
    (by
      intro i hi j hj
      exact mul_nonneg (Real.sqrt_nonneg _) (hb i hi j hj))
    hrow hcol
  have hsum :
      (∑ i ∈ s, ∑ j ∈ s, (π i)⁻¹ * b i j * x i * y j) =
        ∑ i ∈ s, ∑ j ∈ s,
          (Real.sqrt (π j / π i) * b i j) * (w i * x i) * (w j * y j) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact hnorm i hi j hj
  have hnormX :
      (∑ i ∈ s, (w i * x i) ^ 2) = ∑ i ∈ s, (π i)⁻¹ * x i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [w]
    rw [mul_pow, inverseSqrtSquare (hπ i hi)]
  have hnormY :
      (∑ j ∈ s, (w j * y j) ^ 2) = ∑ j ∈ s, (π j)⁻¹ * y j ^ 2 := by
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [w]
    rw [mul_pow, inverseSqrtSquare (hπ j hj)]
  calc
    (∑ i ∈ s, ∑ j ∈ s, (π i)⁻¹ * b i j * x i * y j) =
        ∑ i ∈ s, ∑ j ∈ s,
          (Real.sqrt (π j / π i) * b i j) * (w i * x i) * (w j * y j) := hsum
    _ ≤ θ * Real.sqrt (∑ i ∈ s, (π i)⁻¹ * x i ^ 2) *
        Real.sqrt (∑ j ∈ s, (π j)⁻¹ * y j ^ 2) := by
      rw [← hnormX, ← hnormY]
      exact hs

end AVRegularity.Analysis.Schur
