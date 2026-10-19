-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Coarse.Energy.Zero
public import AVRegularity.CycleComparison.Coarse.Defect.FcIdent
public import AVRegularity.CycleComparison.Coarse.Energy.Cell
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
namespace AVRegularity.CycleComparison.Coarse

/-! Real algebra for the final form of the retained-flux bound: the square root of the
time-integrated mass bound, and the comparison of the four parts with the letter sizes. -/

/-- One part of the square-root step. -/
theorem final_part_le {B F₀ Nb c N Y Z : ℝ} (hB : 0 < B) (hN : 0 ≤ N)
    (hNb : N ≤ Nb) (hY : B * Y ≤ (4 * F₀) ^ 2 * Z ^ 2) :
    4 * (c ^ 2 * N * Y) / B ≤ 64 * Nb * F₀ ^ 2 * (c / B * Z) ^ 2 := by
  have hY' : Y ≤ (4 * F₀) ^ 2 * Z ^ 2 / B := by
    rw [le_div_iff₀ hB, mul_comm]; exact hY
  have hQ : 0 ≤ (4 * F₀) ^ 2 * Z ^ 2 / B := by positivity
  have h4 : (0 : ℝ) ≤ 4 := by norm_num
  calc 4 * (c ^ 2 * N * Y) / B ≤ 4 * (c ^ 2 * N * ((4 * F₀) ^ 2 * Z ^ 2 / B)) / B :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hY' (mul_nonneg (sq_nonneg c) hN)) h4) hB.le
    _ ≤ 4 * (c ^ 2 * Nb * ((4 * F₀) ^ 2 * Z ^ 2 / B)) / B :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNb (sq_nonneg c)) hQ) h4)
          hB.le
    _ = 64 * Nb * F₀ ^ 2 * (c / B * Z) ^ 2 := by field_simp; ring

/-- **The square-root step.** With `B Y_t ≤ (4F₀)² Z_t²`,
`√(4 ∑ c_t² N_t Y_t / B) ≤ 8 √Nb F₀ ∑ (c_t / B) Z_t`. -/
theorem final_sqrt_le {B F₀ Nb N1 N2 N3 N5 c1 c2 c3 c5 Y1 Y2 Y3 Y5 Z1 Z2 Z3 Z5 : ℝ}
    (hB : 0 < B) (hF : 0 ≤ F₀) (hN1 : 0 ≤ N1) (hN2 : 0 ≤ N2) (hN3 : 0 ≤ N3) (hN5 : 0 ≤ N5)
    (hN1b : N1 ≤ Nb) (hN2b : N2 ≤ Nb) (hN3b : N3 ≤ Nb) (hN5b : N5 ≤ Nb)
    (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hc3 : 0 ≤ c3) (hc5 : 0 ≤ c5)
    (hZ1 : 0 ≤ Z1) (hZ2 : 0 ≤ Z2) (hZ3 : 0 ≤ Z3) (hZ5 : 0 ≤ Z5)
    (hY1 : B * Y1 ≤ (4 * F₀) ^ 2 * Z1 ^ 2) (hY2 : B * Y2 ≤ (4 * F₀) ^ 2 * Z2 ^ 2)
    (hY3 : B * Y3 ≤ (4 * F₀) ^ 2 * Z3 ^ 2) (hY5 : B * Y5 ≤ (4 * F₀) ^ 2 * Z5 ^ 2) :
    Real.sqrt (4 * (c1 ^ 2 * N1 * Y1 + c2 ^ 2 * N2 * Y2 + c3 ^ 2 * N3 * Y3 + c5 ^ 2 * N5 * Y5) / B)
      ≤ 8 * Real.sqrt Nb * F₀ * (c1 / B * Z1 + c2 / B * Z2 + c3 / B * Z3 + c5 / B * Z5) := by
  have hNb : 0 ≤ Nb := hN1.trans hN1b
  have hR : 0 ≤ 8 * Real.sqrt Nb * F₀ * (c1 / B * Z1 + c2 / B * Z2 + c3 / B * Z3 + c5 / B * Z5) :=
    by positivity
  have p1 := final_part_le (c := c1) hB hN1 hN1b hY1
  have p2 := final_part_le (c := c2) hB hN2 hN2b hY2
  have p3 := final_part_le (c := c3) hB hN3 hN3b hY3
  have p5 := final_part_le (c := c5) hB hN5 hN5b hY5
  have a1 : 0 ≤ c1 / B * Z1 := by positivity
  have a2 : 0 ≤ c2 / B * Z2 := by positivity
  have a3 : 0 ≤ c3 / B * Z3 := by positivity
  have a5 : 0 ≤ c5 / B * Z5 := by positivity
  have hsq : (8 * Real.sqrt Nb * F₀ * (c1 / B * Z1 + c2 / B * Z2 + c3 / B * Z3 + c5 / B * Z5)) ^ 2
      = 64 * Nb * F₀ ^ 2 * (c1 / B * Z1 + c2 / B * Z2 + c3 / B * Z3 + c5 / B * Z5) ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hNb]; ring
  have hcross : (c1 / B * Z1) ^ 2 + (c2 / B * Z2) ^ 2 + (c3 / B * Z3) ^ 2 + (c5 / B * Z5) ^ 2 ≤
      (c1 / B * Z1 + c2 / B * Z2 + c3 / B * Z3 + c5 / B * Z5) ^ 2 := by
    set x1 := c1 / B * Z1
    set x2 := c2 / B * Z2
    set x3 := c3 / B * Z3
    set x5 := c5 / B * Z5
    have e : (x1 + x2 + x3 + x5) ^ 2 = x1 ^ 2 + x2 ^ 2 + x3 ^ 2 + x5 ^ 2 +
        2 * (x1 * x2 + x1 * x3 + x1 * x5 + x2 * x3 + x2 * x5 + x3 * x5) := by ring
    have hp : 0 ≤ x1 * x2 + x1 * x3 + x1 * x5 + x2 * x3 + x2 * x5 + x3 * x5 := by positivity
    rw [e]
    linarith
  have hK : 0 ≤ 64 * Nb * F₀ ^ 2 := by positivity
  have hle : 4 * (c1 ^ 2 * N1 * Y1 + c2 ^ 2 * N2 * Y2 + c3 ^ 2 * N3 * Y3 + c5 ^ 2 * N5 * Y5) / B
      ≤ (8 * Real.sqrt Nb * F₀ * (c1 / B * Z1 + c2 / B * Z2 + c3 / B * Z3 + c5 / B * Z5)) ^ 2 := by
    rw [hsq]
    have e : 4 * (c1 ^ 2 * N1 * Y1 + c2 ^ 2 * N2 * Y2 + c3 ^ 2 * N3 * Y3 + c5 ^ 2 * N5 * Y5) / B
        = 4 * (c1 ^ 2 * N1 * Y1) / B + 4 * (c2 ^ 2 * N2 * Y2) / B + 4 * (c3 ^ 2 * N3 * Y3) / B +
          4 * (c5 ^ 2 * N5 * Y5) / B := by ring
    rw [e]
    have h2 := mul_le_mul_of_nonneg_left hcross hK
    have e2 : 64 * Nb * F₀ ^ 2 * ((c1 / B * Z1) ^ 2 + (c2 / B * Z2) ^ 2 + (c3 / B * Z3) ^ 2 +
        (c5 / B * Z5) ^ 2) = 64 * Nb * F₀ ^ 2 * (c1 / B * Z1) ^ 2 +
        64 * Nb * F₀ ^ 2 * (c2 / B * Z2) ^ 2 + 64 * Nb * F₀ ^ 2 * (c3 / B * Z3) ^ 2 +
        64 * Nb * F₀ ^ 2 * (c5 / B * Z5) ^ 2 := by ring
    rw [e2] at h2
    linarith
  calc Real.sqrt (4 * (c1 ^ 2 * N1 * Y1 + c2 ^ 2 * N2 * Y2 + c3 ^ 2 * N3 * Y3 +
        c5 ^ 2 * N5 * Y5) / B) ≤
      Real.sqrt ((8 * Real.sqrt Nb * F₀ *
        (c1 / B * Z1 + c2 / B * Z2 + c3 / B * Z3 + c5 / B * Z5)) ^ 2) := Real.sqrt_le_sqrt hle
    _ = _ := Real.sqrt_sq hR

/-- **The comparison with the letter sizes.** -/
theorem final_compare_le {Nb F₀ C c1 c2 c3 c5 Z1 Z2 Z3 Z5 B K1 K2 K3 K5 W1 W0 s0 s1 k₀ Sig TJ
    q₀ q₁ : ℝ} (hB : 0 < B) (hF : 0 ≤ F₀) (hC1 : 1 ≤ C)
    (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hK3 : 0 ≤ K3) (hK5 : 0 ≤ K5)
    (hW1 : 0 ≤ W1) (hW0 : 0 ≤ W0) (hs0 : 0 ≤ s0) (hs1 : 0 ≤ s1) (hk₀ : 0 ≤ k₀)
    (hZ1 : 0 ≤ Z1) (hZ2 : 0 ≤ Z2) (hZ3 : 0 ≤ Z3) (hZ5 : 0 ≤ Z5)
    (hb1 : c1 / B ≤ K1 * W1 * s0) (hb2 : c2 / B ≤ K2 * W1 * s1) (hb3 : c3 / B ≤ K3 * s0)
    (hb5 : c5 / B ≤ K5 * k₀ * W0)
    (hz1 : Z1 ≤ Sig) (hz2 : Z2 ≤ Sig) (hz3 : Z3 ≤ TJ) (hz5 : Z5 ≤ Sig)
    (hq₀ : q₀ = C * s0) (hq₁ : q₁ = C * s1)
    (hKC : 8 * Real.sqrt Nb * (K1 + K2 + K3 + K5) ≤ C)
    (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2) (hc3 : 0 ≤ c3) (hc5 : 0 ≤ c5) :
    8 * Real.sqrt Nb * F₀ * (c1 / B * Z1 + c2 / B * Z2 + c3 / B * Z3 + c5 / B * Z5) ≤
      C * F₀ * ((W1 * (q₀ + q₁) + k₀ * W0) * Sig + q₀ * TJ) := by
  have hs : 0 ≤ Real.sqrt Nb := Real.sqrt_nonneg _
  have hC0 : 0 ≤ C := zero_le_one.trans hC1
  have hSig : 0 ≤ Sig := hZ1.trans hz1
  have hTJ : 0 ≤ TJ := hZ3.trans hz3
  have hcb1 : 0 ≤ c1 / B := div_nonneg hc1 hB.le
  have hcb2 : 0 ≤ c2 / B := div_nonneg hc2 hB.le
  have hcb3 : 0 ≤ c3 / B := div_nonneg hc3 hB.le
  have hcb5 : 0 ≤ c5 / B := div_nonneg hc5 hB.le
  -- each part against its letter
  have t1 : c1 / B * Z1 ≤ K1 * (W1 * s0 * Sig) := by
    calc c1 / B * Z1 ≤ K1 * W1 * s0 * Sig := mul_le_mul hb1 hz1 hZ1 (by positivity)
      _ = _ := by ring
  have t2 : c2 / B * Z2 ≤ K2 * (W1 * s1 * Sig) := by
    calc c2 / B * Z2 ≤ K2 * W1 * s1 * Sig := mul_le_mul hb2 hz2 hZ2 (by positivity)
      _ = _ := by ring
  have t3 : c3 / B * Z3 ≤ K3 * (s0 * TJ) := by
    calc c3 / B * Z3 ≤ K3 * s0 * TJ := mul_le_mul hb3 hz3 hZ3 (by positivity)
      _ = _ := by ring
  have t5 : c5 / B * Z5 ≤ K5 * (k₀ * W0 * Sig) := by
    calc c5 / B * Z5 ≤ K5 * k₀ * W0 * Sig := mul_le_mul hb5 hz5 hZ5 (by positivity)
      _ = _ := by ring
  -- the constants against `C`
  have hKC1 : 8 * Real.sqrt Nb * K1 ≤ C * C := by
    have : 8 * Real.sqrt Nb * K1 ≤ 8 * Real.sqrt Nb * (K1 + K2 + K3 + K5) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    exact this.trans (hKC.trans (le_mul_of_one_le_left hC0 hC1))
  have hKC2 : 8 * Real.sqrt Nb * K2 ≤ C * C := by
    have : 8 * Real.sqrt Nb * K2 ≤ 8 * Real.sqrt Nb * (K1 + K2 + K3 + K5) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    exact this.trans (hKC.trans (le_mul_of_one_le_left hC0 hC1))
  have hKC3 : 8 * Real.sqrt Nb * K3 ≤ C * C := by
    have : 8 * Real.sqrt Nb * K3 ≤ 8 * Real.sqrt Nb * (K1 + K2 + K3 + K5) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    exact this.trans (hKC.trans (le_mul_of_one_le_left hC0 hC1))
  have hKC5 : 8 * Real.sqrt Nb * K5 ≤ C := by
    have : 8 * Real.sqrt Nb * K5 ≤ 8 * Real.sqrt Nb * (K1 + K2 + K3 + K5) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hA1 : 0 ≤ F₀ * (W1 * s0 * Sig) := by positivity
  have hA2 : 0 ≤ F₀ * (W1 * s1 * Sig) := by positivity
  have hA3 : 0 ≤ F₀ * (s0 * TJ) := by positivity
  have hA5 : 0 ≤ F₀ * (k₀ * W0 * Sig) := by positivity
  have h8 : 0 ≤ 8 * Real.sqrt Nb * F₀ := by positivity
  calc 8 * Real.sqrt Nb * F₀ * (c1 / B * Z1 + c2 / B * Z2 + c3 / B * Z3 + c5 / B * Z5) ≤
      8 * Real.sqrt Nb * F₀ * (K1 * (W1 * s0 * Sig) + K2 * (W1 * s1 * Sig) + K3 * (s0 * TJ) +
        K5 * (k₀ * W0 * Sig)) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add t1 t2) t3) t5) h8
    _ = (8 * Real.sqrt Nb * K1) * (F₀ * (W1 * s0 * Sig)) +
        (8 * Real.sqrt Nb * K2) * (F₀ * (W1 * s1 * Sig)) +
        (8 * Real.sqrt Nb * K3) * (F₀ * (s0 * TJ)) +
        (8 * Real.sqrt Nb * K5) * (F₀ * (k₀ * W0 * Sig)) := by ring
    _ ≤ (C * C) * (F₀ * (W1 * s0 * Sig)) + (C * C) * (F₀ * (W1 * s1 * Sig)) +
        (C * C) * (F₀ * (s0 * TJ)) + C * (F₀ * (k₀ * W0 * Sig)) :=
        add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_right hKC1 hA1)
          (mul_le_mul_of_nonneg_right hKC2 hA2)) (mul_le_mul_of_nonneg_right hKC3 hA3))
          (mul_le_mul_of_nonneg_right hKC5 hA5)
    _ = C * F₀ * ((W1 * (q₀ + q₁) + k₀ * W0) * Sig + q₀ * TJ) := by
        rw [hq₀, hq₁]; ring

/-! Real algebra for the mass-weighted bound of the retained flux at one time: four parts, one of
them coupling the components through a matrix controlled by the mass-weighted Schur test, and
Cauchy–Schwarz over the cells. -/

section
theorem sq_add4_le (a b c d : ℝ) : (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c),
    sq_nonneg (b - d), sq_nonneg (c - d)]

variable {ι : Type*} [Fintype ι]

/-- **The mass-weighted bound of four parts at one time.** -/
theorem mass_four_le (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (c : ι → ι → ℝ) (hc : ∀ v u, 0 ≤ c v u)
    {S : ℝ} (hrow : ∀ v, ∑ u, Real.sqrt (π u / π v) * c v u ≤ S)
    (hcol : ∀ u, ∑ v, Real.sqrt (π u / π v) * c v u ≤ S) {c1 c3 c5 : ℝ}
    (f x1 x3 x5 y : ι → ℝ) (hf : ∀ v, 0 ≤ f v)
    (hpt : ∀ v, Real.sqrt (f v) ≤ c1 * x1 v + ∑ u, c v u * y u + c3 * x3 v + c5 * x5 v) :
    ∑ v, (π v)⁻¹ * f v ≤ 4 * (c1 ^ 2 * ∑ v, (π v)⁻¹ * x1 v ^ 2 +
      S ^ 2 * ∑ u, (π u)⁻¹ * y u ^ 2 + c3 ^ 2 * ∑ v, (π v)⁻¹ * x3 v ^ 2 +
        c5 ^ 2 * ∑ v, (π v)⁻¹ * x5 v ^ 2) := by
  have hπi : ∀ v, 0 ≤ (π v)⁻¹ := fun v => inv_nonneg.2 (hπ v).le
  have hfv : ∀ v, f v ≤ 4 * ((c1 * x1 v) ^ 2 + (∑ u, c v u * y u) ^ 2 + (c3 * x3 v) ^ 2 +
      (c5 * x5 v) ^ 2) := fun v => by
    have h0 : f v = Real.sqrt (f v) ^ 2 := (Real.sq_sqrt (hf v)).symm
    have h1 : Real.sqrt (f v) ^ 2 ≤ (c1 * x1 v + ∑ u, c v u * y u + c3 * x3 v + c5 * x5 v) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) (hpt v) 2
    rw [h0]
    exact h1.trans (sq_add4_le _ _ _ _)
  have hs := schur_mass_sq_le π hπ c hc y S hrow hcol
  calc ∑ v, (π v)⁻¹ * f v ≤ ∑ v, (π v)⁻¹ * (4 * ((c1 * x1 v) ^ 2 + (∑ u, c v u * y u) ^ 2 +
        (c3 * x3 v) ^ 2 + (c5 * x5 v) ^ 2)) :=
        Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (hfv v) (hπi v)
    _ = 4 * (c1 ^ 2 * ∑ v, (π v)⁻¹ * x1 v ^ 2 + ∑ v, (π v)⁻¹ * (∑ u, c v u * y u) ^ 2 +
        c3 ^ 2 * ∑ v, (π v)⁻¹ * x3 v ^ 2 + c5 ^ 2 * ∑ v, (π v)⁻¹ * x5 v ^ 2) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun v _ => ?_
        ring
    _ ≤ _ := by
        have h4 : (0 : ℝ) ≤ 4 := by norm_num
        refine mul_le_mul_of_nonneg_left ?_ h4
        linarith
end

end AVRegularity.CycleComparison.Coarse
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Coarse

/-! The remainder `qpRem` of `𝖰_p 𝖯_p`: on smooth fields `ψ - 𝖰_p(𝖯_p ψ) = - qpRem Hc p ψ`, where
`qpRem` collects the terms `𝒞^{a+b}` with `a + b ≥ p + 1`; its smoothness, periodicity, `TorusAdj`
structure (order `4p`) and factorial-norm bound with constant `cqp`. -/

section
/-! ### Pure real algebra -/

/-- Alternating binomial sum, in factorial form. -/
theorem alt_factorial_sum (m : ℕ) :
    ∑ a ∈ Finset.range (m + 1), (-1 : ℝ) ^ a / ((a.factorial : ℝ) * ((m - a).factorial : ℝ)) =
      if m = 0 then 1 else 0 := by
  have h := Int.alternating_sum_range_choose (n := m)
  have h' : ∑ a ∈ Finset.range (m + 1), (-1 : ℝ) ^ a * (m.choose a : ℝ) =
      if m = 0 then 1 else 0 := by
    have := congrArg (fun z : ℤ => (z : ℝ)) h
    simpa [apply_ite] using this
  have hm : (m.factorial : ℝ) ≠ 0 := by positivity
  have : ∀ a ∈ Finset.range (m + 1),
      (-1 : ℝ) ^ a / ((a.factorial : ℝ) * ((m - a).factorial : ℝ)) =
        (m.factorial : ℝ)⁻¹ * ((-1 : ℝ) ^ a * (m.choose a : ℝ)) := by
    intro a ha
    have hl : a ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    rw [Nat.cast_choose ℝ hl]
    have h1 : (a.factorial : ℝ) ≠ 0 := by positivity
    have h2 : ((m - a).factorial : ℝ) ≠ 0 := by positivity
    field_simp
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum, h']
  split_ifs with h0
  · subst h0; simp
  · simp

section Split

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The low-degree part of the double sum collapses to the degree-zero term. -/
theorem double_sum_low (T : ℕ → V) (p : ℕ) :
    ∑ a ∈ Finset.range (p + 1), ∑ b ∈ Finset.range (p + 1),
      (if a + b ≤ p then ((-1 : ℝ) ^ a / ((a.factorial : ℝ) * (b.factorial : ℝ))) • T (a + b)
        else 0) = T 0 := by
  have h1 : ∀ a ∈ Finset.range (p + 1), ∑ b ∈ Finset.range (p + 1),
      (if a + b ≤ p then ((-1 : ℝ) ^ a / ((a.factorial : ℝ) * (b.factorial : ℝ))) • T (a + b)
        else 0) = ∑ b ∈ Finset.range (p + 1 - a),
      ((-1 : ℝ) ^ a / ((a.factorial : ℝ) * (b.factorial : ℝ))) • T (a + b) := by
    intro a _
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext b; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [Finset.sum_congr rfl h1, ← Finset.sum_range_diag_flip]
  have h2 : ∀ i ∈ Finset.range (p + 1), ∑ j ∈ Finset.range (i + 1),
      ((-1 : ℝ) ^ j / ((j.factorial : ℝ) * ((i - j).factorial : ℝ))) • T (j + (i - j)) =
        (if i = 0 then (1 : ℝ) else 0) • T i := by
    intro i _
    rw [← alt_factorial_sum i, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
  rw [Finset.sum_congr rfl h2, Finset.sum_eq_single 0]
  · simp
  · intro i _ hi; simp [hi]
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos p)) h

/-- Splitting the double sum by total degree. -/
theorem double_sum_split (T : ℕ → V) (p : ℕ) :
    ∑ a ∈ Finset.range (p + 1), ∑ b ∈ Finset.range (p + 1),
      ((-1 : ℝ) ^ a / ((a.factorial : ℝ) * (b.factorial : ℝ))) • T (a + b) =
    T 0 + ∑ a ∈ Finset.range (p + 1), ∑ b ∈ Finset.range (p + 1),
      (if p + 1 ≤ a + b then (-1 : ℝ) ^ a / ((a.factorial : ℝ) * (b.factorial : ℝ)) else 0) •
        T (a + b) := by
  rw [← double_sum_low T p, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases h : a + b ≤ p
  · have : ¬ p + 1 ≤ a + b := by omega
    simp [h, this]
  · have : p + 1 ≤ a + b := by omega
    simp [h, this]

end Split

/-! ### The remainder -/

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The remainder of `𝖰_p 𝖯_p`: the terms of `𝒞^{a+b}` with `a + b ≥ p + 1`. -/
def qpRem (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (ψ : Vec 2 → E) : Vec 2 → E :=
  ∑ a ∈ Finset.range (p + 1), ∑ b ∈ Finset.range (p + 1),
    (if p + 1 ≤ a + b then (-1 : ℝ) ^ a / ((a.factorial : ℝ) * (b.factorial : ℝ)) else 0) •
      (AVRegularity.covOperator Hc)^[a + b] ψ

theorem covIter_smul (Hc : Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ) {f : Vec 2 → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ∀ n : ℕ, (AVRegularity.covOperator Hc)^[n] (c • f) = c • (AVRegularity.covOperator Hc)^[n] f
  | 0 => rfl
  | n + 1 => by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      show c • f = fun x => c • f x from rfl,
      covOperator_smul Hc c (contDiff_top_nat hf 2)]
    exact covIter_smul Hc c (contDiff_covOperator_top Hc hf) n

theorem sub_covPolyQ_covPolyP_eq (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) {ψ : Vec 2 → E}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ψ - AVRegularity.covPolyQ Hc p (AVRegularity.covPolyP Hc p ψ) = -qpRem Hc p ψ := by
  have hsm : ∀ a : ℕ, ∀ b ∈ Finset.range (p + 1), ContDiff ℝ ((2 * a : ℕ) : ℕ∞)
      (((b.factorial : ℝ)⁻¹) • (AVRegularity.covOperator Hc)^[b] ψ) := fun a b _ =>
    (((contDiff_covIter_top Hc hψ b).const_smul _).of_le (by exact_mod_cast le_top))
  have hQP : AVRegularity.covPolyQ Hc p (AVRegularity.covPolyP Hc p ψ) =
      ∑ a ∈ Finset.range (p + 1), ∑ b ∈ Finset.range (p + 1),
        ((-1 : ℝ) ^ a / ((a.factorial : ℝ) * (b.factorial : ℝ))) •
          (AVRegularity.covOperator Hc)^[a + b] ψ := by
    unfold AVRegularity.covPolyQ AVRegularity.covPolyP
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [covLin_iterate_sum Hc a (Finset.range (p + 1)) (hsm a), Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [covIter_smul Hc _ (contDiff_covIter_top Hc hψ b) a, ← Function.iterate_add_apply,
      smul_smul]
    congr 1; ring
  rw [hQP, double_sum_split (fun n => (AVRegularity.covOperator Hc)^[n] ψ) p]
  unfold qpRem
  simp only [Function.iterate_zero, id_eq]
  abel

theorem qpRem_apply (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (f : Vec 2 → E) (x : Vec 2) :
    qpRem Hc p f x = ∑ a ∈ Finset.range (p + 1), ∑ b ∈ Finset.range (p + 1),
      (if p + 1 ≤ a + b then (-1 : ℝ) ^ a / ((a.factorial : ℝ) * (b.factorial : ℝ)) else 0) •
        (AVRegularity.covOperator Hc)^[a + b] f x := by
  simp only [qpRem, Finset.sum_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> simp

theorem contDiff_qpRem_top (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) {f : Vec 2 → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (qpRem Hc p f) := by
  have : qpRem Hc p f = fun x => ∑ a ∈ Finset.range (p + 1), ∑ b ∈ Finset.range (p + 1),
      (if p + 1 ≤ a + b then (-1 : ℝ) ^ a / ((a.factorial : ℝ) * (b.factorial : ℝ)) else 0) •
        (AVRegularity.covOperator Hc)^[a + b] f x := funext (qpRem_apply Hc p f)
  rw [this]
  exact ContDiff.sum fun a _ => ContDiff.sum fun b _ =>
    ContDiff.const_smul _ (contDiff_covIter_top Hc hf _)

theorem isZ2Periodic_qpRem (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) {f : Vec 2 → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f) :
    AVenhance.IsZ2Periodic (qpRem Hc p f) := by
  intro n x
  simp only [qpRem_apply, isZ2Periodic_covIter Hc hf hp _ n x]

/-! ### Real constants -/

/-- The constant of `qpRem`: the terms of total degree `≥ p + 1`. -/
def cqp (X : ℝ) (p : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (p + 1), ∑ b ∈ Finset.range (p + 1),
    (if p + 1 ≤ a + b then X ^ (a + b) / ((a.factorial : ℝ) * (b.factorial : ℝ)) else 0)

/-- The constant `cqp` without the degree cut-off. -/
def cqpBig (Y : ℝ) (p : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (p + 1), ∑ b ∈ Finset.range (p + 1),
    Y ^ (a + b) / ((a.factorial : ℝ) * (b.factorial : ℝ))

theorem cqp_nonneg {X : ℝ} (hX : 0 ≤ X) (p : ℕ) : 0 ≤ cqp X p :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by
    split_ifs
    · positivity
    · exact le_rfl

theorem cqpBig_nonneg {Y : ℝ} (hY : 0 ≤ Y) (p : ℕ) : 0 ≤ cqpBig Y p :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem cqp_le {X Y ω : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (hω : 0 ≤ ω) (hω1 : ω ≤ 1)
    (hXY : X ≤ Y * ω) (p : ℕ) : cqp X p ≤ cqpBig Y p * ω ^ (p + 1) := by
  unfold cqp cqpBig
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun b _ => ?_
  have hd : (0 : ℝ) ≤ (a.factorial : ℝ) * (b.factorial : ℝ) := by positivity
  split_ifs with h
  · rw [div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ hd
    calc X ^ (a + b) ≤ (Y * ω) ^ (a + b) := pow_le_pow_left₀ hX hXY _
      _ = Y ^ (a + b) * ω ^ (a + b) := mul_pow _ _ _
      _ ≤ Y ^ (a + b) * ω ^ (p + 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hω hω1 h) (by positivity)
  · positivity

theorem sum_abs_qpCoef_mul_pow (X : ℝ) (p : ℕ) :
    ∑ a ∈ Finset.range (p + 1), ∑ b ∈ Finset.range (p + 1),
      |(if p + 1 ≤ a + b then (-1 : ℝ) ^ a / ((a.factorial : ℝ) * (b.factorial : ℝ)) else 0)| *
        X ^ (a + b) = cqp X p := by
  unfold cqp
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs
  · rw [abs_div, abs_pow, abs_neg, abs_one, one_pow,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (a.factorial : ℝ) * (b.factorial : ℝ)),
      div_mul_eq_mul_div, one_mul]
  · simp

end Smooth

/-! ### Adjoint structure -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- A single term of `qpRem`. -/
def TorusAdj.qpRemTerm (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M)
    (p R Kc a b : ℕ) (ha : a < p + 1) (hb : b < p + 1) :
    TorusAdj (fun ψ : Vec 2 → E =>
      (if p + 1 ≤ a + b then (-1 : ℝ) ^ a / ((a.factorial : ℝ) * (b.factorial : ℝ)) else 0) •
        (AVRegularity.covOperator Hc)^[a + b] ψ) (4 * p) R Kc
      (|(if p + 1 ≤ a + b then (-1 : ℝ) ^ a / ((a.factorial : ℝ) * (b.factorial : ℝ))
        else 0)| * M ^ (a + b)) :=
  ((TorusAdj.covIter (E := E) Hc hM (a + b) R Kc).liftOrder
    (by omega : 2 * (a + b) ≤ 4 * p)).smul _

/-- `-qpRem`: order `4p`, constant `cqp M p`. -/
def TorusAdj.qpRem (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M)
    (p R Kc : ℕ) :
    TorusAdj (fun ψ : Vec 2 → E => -qpRem Hc p ψ) (4 * p) R Kc (cqp M p) :=
  ((TorusAdj.sumMem (Finset.range (p + 1)) (fun a ha =>
    TorusAdj.sumMem (Finset.range (p + 1)) (fun b hb =>
      TorusAdj.qpRemTerm (E := E) Hc hM p R Kc a b (Finset.mem_range.mp ha)
        (Finset.mem_range.mp hb)))
    |>.mono le_rfl le_rfl (le_of_eq (sum_abs_qpCoef_mul_pow M p))
    |>.ofOp (by funext ψ x; exact (qpRem_apply Hc p ψ x).symm)).neg)

namespace TorusAdj.FBound

variable {ρ : ℝ}

theorem qpRemTerm (hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M)
    (p R Kc a b : ℕ) (ha : a < p + 1) (hb : b < p + 1) :
    (TorusAdj.qpRemTerm (E := E) Hc hM p R Kc a b ha hb).FBound ρ
      (|(if p + 1 ≤ a + b then (-1 : ℝ) ^ a / ((a.factorial : ℝ) * (b.factorial : ℝ))
        else 0)| * fbCovConst ρ Hc Kc ^ (a + b)) :=
  FBound.smul _ (FBound.liftOrder (covIter (E := E) hρ Hc hM (a + b) R Kc)
    (pow_nonneg (fbCovConst_nonneg hρ Hc Kc) (a + b)) _)

/-- `-qpRem` costs `cqp Cc p`. -/
theorem qpRem (hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M)
    (p R Kc : ℕ) :
    (TorusAdj.qpRem (E := E) Hc hM p R Kc).FBound ρ (cqp (fbCovConst ρ Hc Kc) p) := by
  have h : (TorusAdj.sumMem (Finset.range (p + 1)) (fun a ha =>
      TorusAdj.sumMem (Finset.range (p + 1)) (fun b hb =>
        TorusAdj.qpRemTerm (E := E) Hc hM p R Kc a b (Finset.mem_range.mp ha)
          (Finset.mem_range.mp hb)))).FBound ρ
      (∑ a ∈ Finset.range (p + 1), ∑ b ∈ Finset.range (p + 1),
        |(if p + 1 ≤ a + b then (-1 : ℝ) ^ a / ((a.factorial : ℝ) * (b.factorial : ℝ))
          else 0)| * fbCovConst ρ Hc Kc ^ (a + b)) :=
    FBound.sumMem _ (fun a ha => FBound.sumMem _ (fun b hb =>
      qpRemTerm hρ Hc hM p R Kc a b (Finset.mem_range.mp ha) (Finset.mem_range.mp hb)))
  have h2 := h.mono_const (le_of_eq (sum_abs_qpCoef_mul_pow (fbCovConst ρ Hc Kc) p))
  unfold TorusAdj.qpRem
  exact FBound.neg (FBound.ofOp _ (h2.mono le_rfl le_rfl
    (le_of_eq (sum_abs_qpCoef_mul_pow M p))))

end TorusAdj.FBound
end

/-! Gradient-form adjoints of the parts of the retained flux without the inner `𝖰_p`: the
diagonal flux `ψ ↦ F_p(s)^* ψ` and the `(v,u)` block `ψ ↦ 𝖯_p (F_E(s)^* ψ)_u` of the edge flux.
They are in divergence form on smooth fields, with the inner fluxes of the response operators
(before `𝖰_p`). -/

section
section Diag

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- **`ψ ↦ F_p(s)^* ψ` in gradient form**, of order `2p + D`, with the constant of the inner
fluxes before `𝖰_p`. -/
def GAdj.fluxF (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M)
    (b : ℝ → Vec 2 → Vec 2) (D p : ℕ) (hD : 1 ≤ D)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (s : ℝ) (R Kc Q : ℕ) (hR : 1 ≤ R) (hQR : R + 2 * p + D + 2 ≤ Q) (hQK : Kc + 1 ≤ Q)
    (hb : ContDiff ℝ (Q : ℕ) (b s)) (hbp : AVenhance.IsZ2Periodic (b s)) (Bb : ℕ → ℝ)
    (hBb : ∀ l ≤ Kc, ∀ x, ‖iteratedFDeriv ℝ (l + 1) (b s) x‖ ≤ Bb l)
    (hA : ∀ d, ContDiff ℝ (Q : ℕ) (AD d s)) (hAp : ∀ d, AVenhance.IsZ2Periodic (AD d s))
    (BA : ℕ → ℕ → ℝ)
    (hBA : ∀ d : Finset.Icc 2 D, ∀ l ≤ Kc, ∀ x,
      ‖coefficientDerivativeArray (AD d s) l x‖ ≤ BA d.1 l)
    (ρ : ℝ) (hρ : 0 < ρ) :
    GAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E) =>
      AVRegularity.coarseFluxAdjoint D b AD Hc p s ψ) (2 * p + D - 1) Kc ρ
      (∑ _j : Fin 2, gfbFluxDivConst ρ Hc M Kc p D Bb BA) :=
  ((GAdj.ofDiv hR (fun j => (TorusAdj.fluxDiv (E := E) Hc hM b D p hD AD s j R Kc Q hQR hQK hb
      hbp Bb hBb hA hAp BA hBA).neg) ρ
    (fun j => (TorusAdj.FBound.fluxDiv (E := E) hρ Hc hM b D p hD AD s j R Kc Q hQR hQK hb hbp
      Bb hBb hA hAp BA hBA).neg)
    (fun _ => gfbFluxDivConst_nonneg hρ Hc ((covBound_nonneg Hc).trans hM) Kc p D
      (fun l hl => (norm_nonneg _).trans (hBb l hl 0))
      (fun d l hl => coefficient_bound_nonneg (hBA d) l hl))
    (T := fun ψ x => -(AVRegularity.coarseFluxAdjoint D b AD Hc p s ψ x))
    (fun ψ hs _ => (coarseFlux_divRep Hc b D p AD s Q (by omega) hb hA ψ
      (fun r => hs.of_le (by exact_mod_cast le_top))).2)).neg).ofOp
    (fun ψ _ _ => by funext x; simp)

end Diag

section Edge

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The inner flux `Sⱼ` of the `(v,u)` block `ψ ↦ 𝖯_p (F_E^* ψ)_u`: order `2p + D - 1`. -/
def TorusAdj.edgePDiv (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M)
    (D H p : ℕ) (hD : 1 ≤ D)
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (v u : ι) (s : ℝ) (j : Fin 2) (R Kc Q : ℕ) (hQR : R + 2 * p + D ≤ Q) (hQK : Kc ≤ Q)
    (hC : ∀ r d, ContDiff ℝ (Q : ℕ) (CE r v u d s))
    (hp : ∀ r d, AVenhance.IsZ2Periodic (CE r v u d s)) (BE : ℕ → ℕ → ℕ → ℝ)
    (hBE : ∀ r (d : Finset.Icc 2 D), ∀ l ≤ Kc, ∀ x,
      ‖coefficientDerivativeArray (CE r v u d s) l x‖ ≤ BE r d.1 l) :
    TorusAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v) =>
      AVRegularity.covPolyP Hc p (fun x => ∑ r ∈ Finset.Icc 1 H, ∑ d : Finset.Icc 2 D,
        wordDivTerm (d.1 - 1) j
          (fun y => ContinuousLinearMap.adjoint (CE r v u d s y) (ψ y)) x)) (2 * p + D - 1) R Kc
      (covPolyConst M p * edgeDivConst D H Kc BE) :=
  ((TorusAdj.covPolyP (E := h u) Hc hM p R Kc).comp
    (TorusAdj.edgeFluxBlockDiv (X := h v) (Y := h u) D H (fun r d => CE r v u d s) j
      (R + 2 * p) Kc Q (by omega) hQK hC hp BE hBE) le_rfl le_rfl).liftOrder
    (by omega : 2 * p + (D - 2) ≤ 2 * p + D - 1)

theorem TorusAdj.FBound.edgePDiv {ρ : ℝ} (hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ}
    (hM : covBound Hc ≤ M) (D H p : ℕ) (hD : 1 ≤ D)
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (v u : ι) (s : ℝ) (j : Fin 2) (R Kc Q : ℕ) (hQR : R + 2 * p + D ≤ Q) (hQK : Kc ≤ Q)
    (hC : ∀ r d, ContDiff ℝ (Q : ℕ) (CE r v u d s))
    (hp : ∀ r d, AVenhance.IsZ2Periodic (CE r v u d s)) (BE : ℕ → ℕ → ℕ → ℝ)
    (hBE : ∀ r (d : Finset.Icc 2 D), ∀ l ≤ Kc, ∀ x,
      ‖coefficientDerivativeArray (CE r v u d s) l x‖ ≤ BE r d.1 l) :
    (TorusAdj.edgePDiv Hc hM D H p hD CE v u s j R Kc Q hQR hQK hC hp BE hBE).FBound ρ
      (covPolyConst (fbCovConst ρ Hc Kc) p * gfbEdgeConst ρ D H Kc BE) := by
  have hec : 0 ≤ gfbEdgeConst ρ D H Kc BE :=
    gfbEdgeConst_nonneg hρ (fun r d l hl => coefficient_bound_nonneg (hBE r d) l hl)
  have hkap := covPolyConst_nonneg hρ Hc p Kc
  unfold TorusAdj.edgePDiv
  exact FBound.liftOrder (FBound.comp (FBound.covPolyP (E := h u) hρ Hc hM p R Kc)
    (FBound.edgeFluxBlockDiv (X := h v) (Y := h u) hρ D H (fun r d => CE r v u d s)
      j (R + 2 * p) Kc Q (by omega) hQK hC hp BE hBE) hec le_rfl le_rfl)
    (mul_nonneg hkap hec) _

/-- **`ψ ↦ 𝖯_p (F_E(s)^* ψ)_u` in gradient form** (the `(v,u)` block), of order `2p + D`. -/
def GAdj.edgeP (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M) (D H p : ℕ)
    (hD : 1 ≤ D)
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (v u : ι) (s : ℝ) (R Kc Q : ℕ) (hR : 1 ≤ R) (hQR : R + 2 * p + D ≤ Q) (hQK : Kc ≤ Q)
    (hC : ∀ r d, ContDiff ℝ (Q : ℕ) (CE r v u d s))
    (hp : ∀ r d, AVenhance.IsZ2Periodic (CE r v u d s)) (BE : ℕ → ℕ → ℕ → ℝ)
    (hBE : ∀ r (d : Finset.Icc 2 D), ∀ l ≤ Kc, ∀ x,
      ‖coefficientDerivativeArray (CE r v u d s) l x‖ ≤ BE r d.1 l)
    (ρ : ℝ) (hρ : 0 < ρ) :
    GAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v) =>
      AVRegularity.covPolyP Hc p (edgeBlock D H CE s v u ψ)) (2 * p + D - 1) Kc ρ
      (∑ _j : Fin 2, covPolyConst (fbCovConst ρ Hc Kc) p * gfbEdgeConst ρ D H Kc BE) :=
  GAdj.ofDiv hR
    (fun j => TorusAdj.edgePDiv Hc hM D H p hD CE v u s j R Kc Q hQR hQK hC hp BE hBE) ρ
    (fun j => TorusAdj.FBound.edgePDiv hρ Hc hM D H p hD CE v u s j R Kc Q hQR hQK hC hp BE hBE)
    (fun _ => mul_nonneg (covPolyConst_nonneg hρ Hc p Kc)
      (gfbEdgeConst_nonneg hρ (fun r d l hl => coefficient_bound_nonneg (hBE r d) l hl)))
    (fun ψ hs _ => (edgeFlux_divRep Hc D H p CE v u s Q (by omega) hC ψ
      (fun r => hs.of_le (by exact_mod_cast le_top))).2)

end Edge
end

/-! The Taylor flux `ψ ↦ (p!)⁻¹ 𝒞^p ∑_{k,l} c_{kl} ∂_l ψ_k` in gradient form: it is the divergence
of `ψ ↦ (p!)⁻¹ 𝒞^p ∑_k c_{kl} ψ_k`, and its constant is `(p!)⁻¹ Cc^p ∑ |c_{kl}|`. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The inner flux `S_l ψ = (p!)⁻¹ 𝒞^p ∑_k c_{kl} ψ_k` of the Taylor flux: order `2p`. -/
def TorusAdj.taylorDiv (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M)
    (c : Matrix (Fin 2) (Fin 2) ℝ) (p R Kc : ℕ) (l : Fin 2) :
    TorusAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E) =>
      ((p.factorial : ℝ)⁻¹) • (AVRegularity.covOperator Hc)^[p]
        (fun x => ∑ k : Fin 2, c k l • ψ x k)) (2 * p) R Kc
      (|((p.factorial : ℝ)⁻¹)| * (M ^ p * ∑ k : Fin 2, |c k l| * ((Kc.factorial : ℝ) * 1))) :=
  ((((TorusAdj.covIter (E := E) Hc hM p R Kc).comp
    (TorusAdj.sum (Finset.univ : Finset (Fin 2)) fun k =>
      (TorusAdj.componentOp (E := E) k (R + 2 * p) Kc).smul (c k l)) le_rfl le_rfl).ofOrder
    (by omega : 2 * p + 0 = 2 * p)).smul ((p.factorial : ℝ)⁻¹)).ofOp (by funext ψ; rfl)

theorem TorusAdj.FBound.taylorDiv {ρ : ℝ} (hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ}
    (hM : covBound Hc ≤ M) (c : Matrix (Fin 2) (Fin 2) ℝ) (p R Kc : ℕ) (l : Fin 2) :
    (TorusAdj.taylorDiv (E := E) Hc hM c p R Kc l).FBound ρ
      (|((p.factorial : ℝ)⁻¹)| * (fbCovConst ρ Hc Kc ^ p * ∑ k : Fin 2, |c k l| * 1)) := by
  have hs : 0 ≤ ∑ k : Fin 2, |c k l| * 1 :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) zero_le_one
  unfold TorusAdj.taylorDiv
  exact FBound.ofOp _ (FBound.smul _ (FBound.ofOrder _ (FBound.comp
    (FBound.covIter (E := E) hρ Hc hM p R Kc)
    (FBound.sum _ fun k => FBound.smul _ (FBound.componentOp (E := E) hρ.le k _ Kc)) hs
    le_rfl le_rfl)))

theorem taylorDivConst_nonneg {ρ : ℝ} (hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ)
    (c : Matrix (Fin 2) (Fin 2) ℝ) (p Kc : ℕ) (l : Fin 2) :
    0 ≤ |((p.factorial : ℝ)⁻¹)| * (fbCovConst ρ Hc Kc ^ p * ∑ k : Fin 2, |c k l| * 1) :=
  mul_nonneg (abs_nonneg _) (mul_nonneg (pow_nonneg (fbCovConst_nonneg hρ Hc Kc) p)
    (Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) zero_le_one))

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The Taylor flux in divergence form, on a smooth field. -/
theorem taylor_divRep (Hc : Matrix (Fin 2) (Fin 2) ℝ) (c : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ)
    (ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    DivRep (fun x => ((p.factorial : ℝ)⁻¹) • (AVRegularity.covOperator Hc)^[p]
        (fun x => ∑ k : Fin 2, ∑ l : Fin 2, c k l • fderiv ℝ (fun y => ψ y k) x (basisVec l)) x)
      (fun l x => ((p.factorial : ℝ)⁻¹) • (AVRegularity.covOperator Hc)^[p]
        (fun x => ∑ k : Fin 2, c k l • ψ x k) x) := by
  have hk : ∀ k : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun y => ψ y k) := fun k =>
    (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => E) k).contDiff.comp hψ
  have hY : ∀ l : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑ k : Fin 2, c k l • ψ x k) := fun l =>
    ContDiff.sum fun k _ => (hk k).const_smul _
  have h0 : DivRep (fun x => ∑ k : Fin 2, ∑ l : Fin 2, c k l • fderiv ℝ (fun y => ψ y k) x
      (basisVec l)) (fun l x => ∑ k : Fin 2, c k l • ψ x k) := by
    refine ⟨fun l => (hY l).of_le (by exact_mod_cast le_top), ?_⟩
    funext x
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [partialOp_sum l Finset.univ (fun k x => c k l • ψ x k)
      (fun k _ => ((hk k).const_smul _).of_le (by exact_mod_cast le_top))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [partialOp_smul l (c k l) ((hk k).of_le (by exact_mod_cast le_top))]
    rfl
  exact (DivRep.constCoef (ConstCoefOp.covIter (E := E) Hc p) h0
    (fun l => contDiff_top_nat (hY l) _)).smul _

/-- **The Taylor flux in gradient form**, of order `2p + 1`. -/
def GAdj.taylorF (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M)
    (c : Matrix (Fin 2) (Fin 2) ℝ) (p R Kc : ℕ) (hR : 1 ≤ R) (ρ : ℝ) (hρ : 0 < ρ) :
    GAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E) =>
      ((p.factorial : ℝ)⁻¹) • (AVRegularity.covOperator Hc)^[p]
        (fun x => ∑ k : Fin 2, ∑ l : Fin 2, c k l • fderiv ℝ (fun y => ψ y k) x (basisVec l)))
      (2 * p) Kc ρ
      (∑ l : Fin 2, |((p.factorial : ℝ)⁻¹)| * (fbCovConst ρ Hc Kc ^ p * ∑ k : Fin 2, |c k l| * 1)) :=
  GAdj.ofDiv hR (fun l => TorusAdj.taylorDiv (E := E) Hc hM c p R Kc l) ρ
    (fun l => TorusAdj.FBound.taylorDiv hρ Hc hM c p R Kc l)
    (fun l => taylorDivConst_nonneg hρ Hc c p Kc l)
    (fun ψ hs _ => (taylor_divRep Hc c p ψ hs).2)
end

/-! Gradient-form adjoints of the retained parts of the coarse flux: `F_p(s)^* (I - 𝖰_p 𝖯_p)` and
the `(v,u)` block of `𝖯_p F_E(s)^* (I - 𝖰_p 𝖯_p)`. On smooth fields `I - 𝖰_p 𝖯_p = -qpRem`, whose
factorial cost `cqp` carries the factor `ω^{p+1}`. -/

section
/-- `-qpRem` maps smooth periodic fields to smooth periodic fields. -/
theorem neg_qpRem_smooth {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) (ψ : Vec 2 → E) (hs : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hp : AVenhance.IsZ2Periodic ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (-qpRem Hc p ψ) ∧ AVenhance.IsZ2Periodic (-qpRem Hc p ψ) := by
  refine ⟨(contDiff_qpRem_top Hc p hs).neg, fun n x => ?_⟩
  simp only [Pi.neg_apply, isZ2Periodic_qpRem Hc p hs hp n x]

section Diag

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- **`ψ ↦ F_p(s)^* (ψ - 𝖰_p 𝖯_p ψ)` in gradient form**, of order `6p + D`. -/
def GAdj.fluxRemF (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M)
    (b : ℝ → Vec 2 → Vec 2) (D p : ℕ) (hD : 1 ≤ D)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (s : ℝ) (R Kc Q : ℕ) (hR : 1 ≤ R) (hQR : R + 2 * p + D + 2 ≤ Q) (hQK : Kc + 1 ≤ Q)
    (hb : ContDiff ℝ (Q : ℕ) (b s)) (hbp : AVenhance.IsZ2Periodic (b s)) (Bb : ℕ → ℝ)
    (hBb : ∀ l ≤ Kc, ∀ x, ‖iteratedFDeriv ℝ (l + 1) (b s) x‖ ≤ Bb l)
    (hA : ∀ d, ContDiff ℝ (Q : ℕ) (AD d s)) (hAp : ∀ d, AVenhance.IsZ2Periodic (AD d s))
    (BA : ℕ → ℕ → ℝ)
    (hBA : ∀ d : Finset.Icc 2 D, ∀ l ≤ Kc, ∀ x,
      ‖coefficientDerivativeArray (AD d s) l x‖ ≤ BA d.1 l)
    (ρ : ℝ) (hρ : 0 < ρ) :
    GAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E) =>
      AVRegularity.coarseFluxAdjoint D b AD Hc p s
        (ψ - AVRegularity.covPolyQ Hc p (AVRegularity.covPolyP Hc p ψ)))
      (4 * p + (2 * p + D - 1)) Kc ρ
      (cqp (fbCovConst ρ Hc Kc) p * ∑ _j : Fin 2, gfbFluxDivConst ρ Hc M Kc p D Bb BA) :=
  ((GAdj.fluxF (E := E) Hc hM b D p hD AD s R Kc Q hR hQR hQK hb hbp Bb hBb hA hAp BA hBA ρ
      hρ).precomp (TorusAdj.qpRem (E := PiLp 2 (fun _ : Fin 2 => E)) Hc hM p 0 Kc)
    (TorusAdj.FBound.qpRem hρ Hc hM p 0 Kc) (cqp_nonneg (fbCovConst_nonneg hρ Hc Kc) p)
    (neg_qpRem_smooth Hc p)).ofOp
    (fun ψ hs _ => by rw [sub_covPolyQ_covPolyP_eq Hc p hs])

end Diag

section Edge

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- **`ψ ↦ 𝖯_p (F_E(s)^* (ψ - 𝖰_p 𝖯_p ψ))_u` in gradient form** (the `(v,u)` block), of order
`6p + D`. -/
def GAdj.edgeRemP (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ} (hM : covBound Hc ≤ M) (D H p : ℕ)
    (hD : 1 ≤ D)
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (v u : ι) (s : ℝ) (R Kc Q : ℕ) (hR : 1 ≤ R) (hQR : R + 2 * p + D ≤ Q) (hQK : Kc ≤ Q)
    (hC : ∀ r d, ContDiff ℝ (Q : ℕ) (CE r v u d s))
    (hp : ∀ r d, AVenhance.IsZ2Periodic (CE r v u d s)) (BE : ℕ → ℕ → ℕ → ℝ)
    (hBE : ∀ r (d : Finset.Icc 2 D), ∀ l ≤ Kc, ∀ x,
      ‖coefficientDerivativeArray (CE r v u d s) l x‖ ≤ BE r d.1 l)
    (ρ : ℝ) (hρ : 0 < ρ) :
    GAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v) =>
      AVRegularity.covPolyP Hc p (edgeBlock D H CE s v u
        (ψ - AVRegularity.covPolyQ Hc p (AVRegularity.covPolyP Hc p ψ))))
      (4 * p + (2 * p + D - 1)) Kc ρ
      (cqp (fbCovConst ρ Hc Kc) p *
        ∑ _j : Fin 2, covPolyConst (fbCovConst ρ Hc Kc) p * gfbEdgeConst ρ D H Kc BE) :=
  ((GAdj.edgeP Hc hM D H p hD CE v u s R Kc Q hR hQR hQK hC hp BE hBE ρ hρ).precomp
    (TorusAdj.qpRem (E := PiLp 2 (fun _ : Fin 2 => h v)) Hc hM p 0 Kc)
    (TorusAdj.FBound.qpRem hρ Hc hM p 0 Kc) (cqp_nonneg (fbCovConst_nonneg hρ Hc Kc) p)
    (neg_qpRem_smooth Hc p)).ofOp
    (fun ψ hs _ => by rw [sub_covPolyQ_covPolyP_eq Hc p hs])

end Edge
end

/-! The gradient-form adjoints of the four surviving parts of the retained flux at a time of the
window, with constants uniform in time: `ω^{p+1}` times the diagonal and edge letter constants for
the retained parts, the diagonal letter constant for the terminal diagonal part, and
`(p!)⁻¹ (4 Kc² ω)^p · 4 ‖𝖩 - B I‖_∞` for the Taylor part, where `ω = ‖H_cov‖_∞ / ρ²`. -/

section
theorem one_le_covPolyConst {X : ℝ} (hX : 0 ≤ X) (p : ℕ) : 1 ≤ covPolyConst X p := by
  unfold covPolyConst
  rw [Finset.sum_range_succ']
  have h : 0 ≤ ∑ l ∈ Finset.range p, X ^ (l + 1) / ((l + 1).factorial : ℝ) :=
    Finset.sum_nonneg fun l _ => by positivity
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  linarith

theorem fluxDivSum_le_coarseCg {ρ : ℝ} (hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) {M : ℝ}
    (hM : 0 ≤ M) (Kc p D : ℕ) {Bb : ℕ → ℝ} {BA : ℕ → ℕ → ℝ} (hB : ∀ l ≤ Kc, 0 ≤ Bb l)
    (hBA : ∀ d : Finset.Icc 2 D, ∀ l ≤ Kc, 0 ≤ BA d.1 l) :
    ∑ _j : Fin 2, gfbFluxDivConst ρ Hc M Kc p D Bb BA ≤ gfbCoarseCg ρ Hc M Kc p D Bb BA := by
  unfold gfbCoarseCg
  refine Finset.sum_le_sum fun _ _ => ?_
  have h0 := gfbFluxDivConst_nonneg hρ Hc hM Kc p D hB hBA
  have h1 := one_le_covPolyConst (fbCovConst_nonneg hρ Hc Kc) p
  exact le_mul_of_one_le_right h0 h1

theorem edgePSum_le_edgeCg {ρ : ℝ} (hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) (Kc p D H : ℕ)
    {BE : ℕ → ℕ → ℕ → ℝ} (hB : ∀ r, ∀ d : Finset.Icc 2 D, ∀ l ≤ Kc, 0 ≤ BE r d.1 l) :
    ∑ _j : Fin 2, covPolyConst (fbCovConst ρ Hc Kc) p * gfbEdgeConst ρ D H Kc BE ≤
      gfbEdgeCg ρ Hc Kc p D H BE := by
  unfold gfbEdgeCg
  refine Finset.sum_le_sum fun _ _ => ?_
  have hk0 := covPolyConst_nonneg hρ Hc p Kc
  have hk1 := one_le_covPolyConst (fbCovConst_nonneg hρ Hc Kc) p
  have he := gfbEdgeConst_nonneg (H := H) hρ hB
  unfold gfbEdgeDivConst edgeFluxPairConst
  exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right he hk1) hk0

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]
  {t₀ t₁ ρ B a B₀ lam : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H p J k L N : ℕ}
  {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
  {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
    (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ] (PiLp 2 (fun _ : Fin 2 => h v))}
  {π : ι → ℝ} {Aedge : Matrix ι ι ℝ} {Cstar Θ : ℝ}

/-- The covariance ratio `ω = ‖H_cov‖_∞ / ρ²`. -/
def covRatio (t₀ t₁ ρ B : ℝ) (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal / ρ ^ 2

/-- The size `‖𝖩 - B I‖_∞` of the deviation of `𝖩`. -/
def jDev (t₀ t₁ B : ℝ) (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (matrixSupNorm (fun t => Jm t - B • (1 : Matrix (Fin 2) (Fin 2) ℝ)) t₀ t₁).toReal

/-- The Taylor constant `(p!)⁻¹ (4 Kc² ω)^p · 4 ‖𝖩 - B I‖_∞`. -/
def taylorC (Kc p : ℕ) (ω σJ : ℝ) : ℝ :=
  ((p.factorial : ℝ)⁻¹) * (4 * (Kc : ℝ) ^ 2 * ω) ^ p * (4 * σJ)

omit [Fintype ι] [DecidableEq ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] in
theorem edgeBlock_edgeExt (s : ℝ) (v u : ι) (χ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)) :
    edgeBlock D H (edgeExt H CE) s v u χ = edgeBlock D H CE s v u χ := by
  funext x
  unfold edgeBlock
  refine Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun d _ => ?_
  simp only [edgeExt_of_mem hr]

theorem covRatio_nonneg (t₀ t₁ ρ B : ℝ) (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) :
    0 ≤ covRatio t₀ t₁ ρ B Jm :=
  div_nonneg ENNReal.toReal_nonneg (sq_nonneg ρ)

section
variable (P : IsCoarseSetting t₀ t₁ ρ B a B₀ lam b D H p J k L N Jm AD CE π Aedge Cstar Θ)
include P

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
theorem covRatio_le_one : covRatio t₀ t₁ ρ B Jm ≤ 1 := by
  have hρ := P.rho_pos
  have h1 : (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal ≤ ρ ^ 2 :=
    ENNReal.toReal_le_of_le_ofReal (sq_nonneg ρ) P.cov_small
  unfold covRatio
  rw [div_le_one (by positivity)]
  exact h1

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
theorem fbCovConst_le_covRatio {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁) (Kc : ℕ) :
    fbCovConst ρ (covarianceMatrix Jm B t₀ s) Kc ≤ 4 * (Kc : ℝ) ^ 2 * covRatio t₀ t₁ ρ B Jm := by
  have hρ := P.rho_pos
  have h := covBound_le_supNorm P hs
  unfold fbCovConst covRatio
  calc covBound (covarianceMatrix Jm B t₀ s) * ((Kc : ℝ) / ρ) ^ 2 ≤
        4 * (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal * ((Kc : ℝ) / ρ) ^ 2 :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = _ := by field_simp

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
theorem cqp_le_covRatio {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁) (Kc : ℕ) :
    cqp (fbCovConst ρ (covarianceMatrix Jm B t₀ s) Kc) p ≤
      cqpBig (4 * (Kc : ℝ) ^ 2) p * covRatio t₀ t₁ ρ B Jm ^ (p + 1) :=
  cqp_le (fbCovConst_nonneg P.rho_pos _ Kc) (by positivity) (covRatio_nonneg t₀ t₁ ρ B Jm)
    (covRatio_le_one P) (fbCovConst_le_covRatio P hs Kc) p

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
theorem jm_dev_le {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁) (i j : Fin 2) :
    |Jm s i j - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ jDev t₀ t₁ B Jm := by
  have hS : matrixSupNorm (fun t => Jm t - B • (1 : Matrix (Fin 2) (Fin 2) ℝ)) t₀ t₁ ≤
      ENNReal.ofReal (jDev t₀ t₁ B Jm) := by
    unfold jDev; rw [ENNReal.ofReal_toReal P.J_bdd]
  have h := abs_entry_le_of_matrixSupNorm ENNReal.toReal_nonneg hS hs i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h
  exact h

/-- **The terminal diagonal part** `ψ ↦ F_p(s)^* ψ`. -/
def gT3 (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] {Kc : ℕ} (hKc : Kc + 1 ≤ N)
    {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁) :
    GAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E) =>
      AVRegularity.coarseFluxAdjoint D b AD (covarianceMatrix Jm B t₀ s) p s ψ)
      (2 * p + D - 1) Kc ρ
      (cellCgD ρ a B₀ (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal Kc D p t₀ t₁ AD) :=
  (GAdj.fluxF (E := E) (covarianceMatrix Jm B t₀ s) (covBound_le_supNorm P hs) b D p
    (by have := P.D_ge; omega) AD s 1 Kc N le_rfl (by have := setting_order_le P; omega) hKc
    ((P.drift_smooth s hs).of_le (by exact_mod_cast le_top)) (P.drift_per s hs)
    (driftB a B₀ lam) (fun l hl x => drift_bound_explicit P (by omega) hs x)
    (fun d => P.AD_smooth d s hs) (fun d => P.AD_per d s hs) (diagSup t₀ t₁ AD)
    (fun d l hl x => by
      simp only [diagSup, d.2, ↓reduceDIte]
      exact coeffSup_bound P.rho_pos (P.AD_fin d) (by omega) hs x)
    ρ P.rho_pos).mono
    ((fluxDivSum_le_coarseCg P.rho_pos _ (by positivity) Kc p D
      (fun l _ => (norm_nonneg _).trans (drift_bound_explicit P (l := l) (by omega) hs 0))
      (fun d l _ => diagSup_nonneg d.1 l)).trans
    (gfbCoarseCg_le P.rho_pos _ Kc D p (covBound_le P hs) (covBound_le_supNorm P hs)
      P.a_nonneg P.B₀_ge P.lam_pos P.drift_scale (fun _ => rfl) diagSup_nonneg))

/-- **The retained diagonal part** `ψ ↦ F_p(s)^* (ψ - 𝖰_p 𝖯_p ψ)`. -/
def gT1 (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] {Kc : ℕ} (hKc : Kc + 1 ≤ N)
    {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁) :
    GAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E) =>
      AVRegularity.coarseFluxAdjoint D b AD (covarianceMatrix Jm B t₀ s) p s
        (ψ - AVRegularity.covPolyQ (covarianceMatrix Jm B t₀ s) p
          (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p ψ)))
      (4 * p + (2 * p + D - 1)) Kc ρ
      (cqpBig (4 * (Kc : ℝ) ^ 2) p * covRatio t₀ t₁ ρ B Jm ^ (p + 1) *
        cellCgD ρ a B₀ (matrixSupNorm (covarianceMatrix Jm B t₀) t₀ t₁).toReal Kc D p t₀ t₁ AD) :=
  (GAdj.fluxRemF (E := E) (covarianceMatrix Jm B t₀ s) (covBound_le_supNorm P hs) b D p
    (by have := P.D_ge; omega) AD s 1 Kc N le_rfl (by have := setting_order_le P; omega) hKc
    ((P.drift_smooth s hs).of_le (by exact_mod_cast le_top)) (P.drift_per s hs)
    (driftB a B₀ lam) (fun l hl x => drift_bound_explicit P (by omega) hs x)
    (fun d => P.AD_smooth d s hs) (fun d => P.AD_per d s hs) (diagSup t₀ t₁ AD)
    (fun d l hl x => by
      simp only [diagSup, d.2, ↓reduceDIte]
      exact coeffSup_bound P.rho_pos (P.AD_fin d) (by omega) hs x)
    ρ P.rho_pos).mono
    (mul_le_mul (cqp_le_covRatio P hs Kc)
      ((fluxDivSum_le_coarseCg P.rho_pos _ (by positivity) Kc p D
        (fun l _ => (norm_nonneg _).trans (drift_bound_explicit P (l := l) (by omega) hs 0))
        (fun d l _ => diagSup_nonneg d.1 l)).trans
      (gfbCoarseCg_le P.rho_pos _ Kc D p (covBound_le P hs) (covBound_le_supNorm P hs)
        P.a_nonneg P.B₀_ge P.lam_pos P.drift_scale (fun _ => rfl) diagSup_nonneg))
      (Finset.sum_nonneg fun _ _ => gfbFluxDivConst_nonneg P.rho_pos _ (by positivity) Kc p D
        (fun l _ => (norm_nonneg _).trans (drift_bound_explicit P (l := l) (by omega) hs 0))
        (fun d l _ => diagSup_nonneg d.1 l))
      (mul_nonneg (cqpBig_nonneg (by positivity) p)
        (pow_nonneg (covRatio_nonneg t₀ t₁ ρ B Jm) _)))

/-- **The retained edge part**, the `(v,u)` block of `𝖯_p F_E(s)^* (I - 𝖰_p 𝖯_p)`. -/
def gT2 {Kc : ℕ} (hKc : Kc ≤ N) (v u : ι) {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁) :
    GAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => h v) =>
      AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p (edgeBlock D H CE s v u
        (ψ - AVRegularity.covPolyQ (covarianceMatrix Jm B t₀ s) p
          (AVRegularity.covPolyP (covarianceMatrix Jm B t₀ s) p ψ))))
      (4 * p + (2 * p + D - 1)) Kc ρ
      (cqpBig (4 * (Kc : ℝ) ^ 2) p * covRatio t₀ t₁ ρ B Jm ^ (p + 1) *
        cellCgE ρ Kc D H p t₀ t₁ CE v u) :=
  ((GAdj.edgeRemP (covarianceMatrix Jm B t₀ s) (covBound_le P hs) D H p
    (by have := P.D_ge; omega) (edgeExt H CE) v u s 1 Kc N le_rfl
    (by have := setting_order_le P; omega) hKc
    (fun r d => by
      by_cases hr : r ∈ Finset.Icc 1 H
      · rw [edgeExt_of_mem hr]; exact P.CE_smooth r hr v u d s hs
      · have he : edgeExt (D := D) H CE r v u d s = 0 := by simp [edgeExt, hr]
        rw [he]; exact contDiff_const)
    (fun r d => by
      by_cases hr : r ∈ Finset.Icc 1 H
      · rw [edgeExt_of_mem hr]; exact P.CE_per r hr v u d s hs
      · have he : edgeExt (D := D) H CE r v u d s = 0 := by simp [edgeExt, hr]
        rw [he]; intro n x; rfl)
    (edgeSup t₀ t₁ H CE v u)
    (fun r d l hl x => by
      by_cases hr : r ∈ Finset.Icc 1 H
      · simp only [edgeExt_of_mem hr, edgeSup, hr, d.2, and_self, ↓reduceDIte]
        exact coeffSup_bound P.rho_pos (P.CE_fin r hr v u d) (by omega) hs x
      · have he : edgeExt (D := D) H CE r v u d s = 0 := by simp [edgeExt, hr]
        rw [he, coefficientDerivativeArray_zero_coefficient, ContinuousLinearMap.opNorm_zero]
        exact edgeSup_nonneg v u r d.1 l)
    ρ P.rho_pos).mono
    (mul_le_mul (cqp_le_covRatio P hs Kc)
      ((edgePSum_le_edgeCg P.rho_pos (covarianceMatrix Jm B t₀ s) Kc p D H
        (fun r d l _ => edgeSup_nonneg v u r d.1 l)).trans
        (gfbEdgeCg_le P.rho_pos _ Kc D H p (covBound_le P hs) (edgeSup_nonneg v u)))
      (Finset.sum_nonneg fun _ _ => mul_nonneg
        (covPolyConst_nonneg P.rho_pos (covarianceMatrix Jm B t₀ s) p Kc)
        (gfbEdgeConst_nonneg (H := H) P.rho_pos fun r d l _ => edgeSup_nonneg v u r d.1 l))
      (mul_nonneg (cqpBig_nonneg (by positivity) p)
        (pow_nonneg (covRatio_nonneg t₀ t₁ ρ B Jm) _)))).ofOp
    (fun ψ _ _ => by rw [edgeBlock_edgeExt])

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
theorem taylorC_bound {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁) (Kc : ℕ) :
    ∑ l : Fin 2, |((p.factorial : ℝ)⁻¹)| *
      (fbCovConst ρ (covarianceMatrix Jm B t₀ s) Kc ^ p * ∑ k' : Fin 2,
        |(fun k' l => Jm s k' l - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) k' l) k' l| * 1) ≤
      taylorC Kc p (covRatio t₀ t₁ ρ B Jm) (jDev t₀ t₁ B Jm) := by
  have hf0 := fbCovConst_nonneg P.rho_pos (covarianceMatrix Jm B t₀ s) Kc
  have hf := fbCovConst_le_covRatio P hs Kc
  have hpow : fbCovConst ρ (covarianceMatrix Jm B t₀ s) Kc ^ p ≤
      (4 * (Kc : ℝ) ^ 2 * covRatio t₀ t₁ ρ B Jm) ^ p := pow_le_pow_left₀ hf0 hf p
  have hJ0 : 0 ≤ jDev t₀ t₁ B Jm := ENNReal.toReal_nonneg
  have hrow : ∀ l : Fin 2, ∑ k' : Fin 2,
      |(fun k' l => Jm s k' l - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) k' l) k' l| * 1 ≤
        2 * jDev t₀ t₁ B Jm := fun l => by
    simp only [Fin.sum_univ_two, mul_one]
    linarith [jm_dev_le P hs 0 l, jm_dev_le P hs 1 l]
  have hfac : 0 ≤ |((p.factorial : ℝ)⁻¹)| := abs_nonneg _
  have hterm : ∀ l : Fin 2, |((p.factorial : ℝ)⁻¹)| *
      (fbCovConst ρ (covarianceMatrix Jm B t₀ s) Kc ^ p * ∑ k' : Fin 2,
        |(fun k' l => Jm s k' l - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) k' l) k' l| * 1) ≤
      ((p.factorial : ℝ)⁻¹) * ((4 * (Kc : ℝ) ^ 2 * covRatio t₀ t₁ ρ B Jm) ^ p *
        (2 * jDev t₀ t₁ B Jm)) := fun l => by
    rw [abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hpow (hrow l)
      (Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) zero_le_one)
      (pow_nonneg (mul_nonneg (by positivity) (covRatio_nonneg t₀ t₁ ρ B Jm)) p))
      (inv_nonneg.mpr (Nat.cast_nonneg _))
  calc _ ≤ ∑ _l : Fin 2, ((p.factorial : ℝ)⁻¹) *
        ((4 * (Kc : ℝ) ^ 2 * covRatio t₀ t₁ ρ B Jm) ^ p * (2 * jDev t₀ t₁ B Jm)) :=
        Finset.sum_le_sum fun l _ => hterm l
    _ = _ := by unfold taylorC; simp only [Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]; ring

/-- **The Taylor part** `ψ ↦ (p!)⁻¹ 𝒞^p ∑_{k,l} (𝖩(s) - B I)_{kl} ∂_l ψ_k`. -/
def gT5 (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] (Kc : ℕ)
    {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁) :
    GAdj (fun ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E) =>
      taylorOp (covarianceMatrix Jm B t₀ s) p Jm B s ψ) (2 * p) Kc ρ
      (taylorC Kc p (covRatio t₀ t₁ ρ B Jm) (jDev t₀ t₁ B Jm)) :=
  ((GAdj.taylorF (E := E) (covarianceMatrix Jm B t₀ s) (covBound_le P hs)
    (fun k' l => Jm s k' l - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) k' l) p 1 Kc le_rfl ρ
    P.rho_pos).mono (taylorC_bound P hs Kc)).ofOp (fun _ _ _ => rfl)

end
end

end AVRegularity.CycleComparison.Coarse
end
