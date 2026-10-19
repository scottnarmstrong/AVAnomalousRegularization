-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Scales.Times
import AVRegularity.CycleWords.LowerCarrierTimeIntegrability
public import AVRegularity.Definitions.CycleJoint.IsPointwiseMolecularEnvelope
public import AVRegularity.CycleJoint.PlaneScalarDiffusionDeviationReadout
public import AVRegularity.CycleWords.GeometryScalarComponentFlux
public import AVRegularity.Definitions.CycleWords.ScalarPackage
public import AVRegularity.Definitions.CycleComparison.IsLiftTailPresentation
public import AVRegularity.Statements.Intermediate.CycleJoint.OcTrimmedQuietTimes
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
namespace AVRegularity.CycleJointProofs.Assembly

/-! **Abstract real algebra of the price ledger**.

The prices of the one-patch statement are powers of the small scale `E = ε_{m-1} ∈ (0, 1]` times constants. These
lemmas keep the `Real.rpow`/`Real.exp` algebra away from the PDE objects:
- `exp_neg_le_factorial_div`: `e^{-y} ≤ k!/y^k` for `y > 0`;
- `poly_exp_le_rpow`: a long time `S ≥ C⁻¹ E^{-b}` makes
  `S^Q e^{-c S} ≤ (Q+k)! c^{-(Q+k)} C^k E^{b k}`;
- `rpow_mono_small`: for `E ∈ (0,1]`, `E^a ≤ E^{a'}` when `a' ≤ a`;
- `interp_rpow_le`: `(C₀ E^{a})^{1-θ} (C₁ E^{-b})^θ ≤ C₀^{1-θ} C₁^θ E^{(1-θ) a - θ b}`.

For `k = 0` the bound reads `e^{-y} ≤ 1`, for `E = 1` all powers are `1`, and `θ = 0` and `θ = 1`
are the two extreme interpolations. -/

/-- `e^{-y} ≤ k!/y^k` for `y > 0`. -/
theorem exp_neg_le_factorial_div {y : ℝ} (hy : 0 < y) (k : ℕ) :
    Real.exp (-y) ≤ (k.factorial : ℝ) / y ^ k := by
  have h := Real.pow_div_factorial_le_exp y hy.le k
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hyk : 0 < y ^ k := pow_pos hy k
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos y) (div_pos hk hyk), inv_div]
  exact h

/-- For `E ∈ (0, 1]`, larger exponents give smaller powers. -/
theorem rpow_mono_small {E a a' : ℝ} (hE : 0 < E) (hE1 : E ≤ 1) (h : a' ≤ a) :
    E ^ a ≤ E ^ a' :=
  Real.rpow_le_rpow_of_exponent_ge hE hE1 h

/-- The interpolated price of two power bounds. -/
theorem interp_rpow_le {C₀ C₁ E a b θ X Y : ℝ} (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hE : 0 < E)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y) (hX : X ≤ C₀ * E ^ a)
    (hY : Y ≤ C₁ * E ^ (-b)) :
    X ^ (1 - θ) * Y ^ θ ≤ C₀ ^ (1 - θ) * C₁ ^ θ * E ^ ((1 - θ) * a - θ * b) := by
  have h1θ : 0 ≤ 1 - θ := by linarith
  have hXp := Real.rpow_le_rpow hX0 hX h1θ
  have hYp := Real.rpow_le_rpow hY0 hY hθ0
  have hEa : 0 ≤ E ^ a := (Real.rpow_pos_of_pos hE a).le
  have hEb : 0 ≤ E ^ (-b) := (Real.rpow_pos_of_pos hE _).le
  calc X ^ (1 - θ) * Y ^ θ
      ≤ (C₀ * E ^ a) ^ (1 - θ) * (C₁ * E ^ (-b)) ^ θ :=
        mul_le_mul hXp hYp (Real.rpow_nonneg hY0 _) (Real.rpow_nonneg (mul_nonneg hC₀ hEa) _)
    _ = C₀ ^ (1 - θ) * C₁ ^ θ * E ^ ((1 - θ) * a - θ * b) := by
        rw [Real.mul_rpow hC₀ hEa, Real.mul_rpow hC₁ hEb, ← Real.rpow_mul hE.le,
          ← Real.rpow_mul hE.le,
          show (1 - θ) * a - θ * b = a * (1 - θ) + -b * θ by ring, Real.rpow_add hE]
        ring

/-- **The interpolated price of the patch error.** The unweighted price `x₀ L^{2K}` is small,
`x₀ ≤ c₀ E^k`, the moment price `x₁ L^{2K}` is bounded, `x₁ ≤ c₁`, and the radius ratio
`L ≤ Lc E^{-b}`; the interpolated price is at most `(CP E^P)²` once
`2P ≤ (1-θ)(k - 2bK) - θ (2bK)`. -/
theorem price_interp_final {E x₀ x₁ L c₀ c₁ Lc k b P θ : ℝ} (K : ℕ) (hE : 0 < E) (hE1 : E ≤ 1)
    (hx₀ : 0 ≤ x₀) (hx₁ : 0 ≤ x₁) (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (hx₀E : x₀ ≤ c₀ * E ^ k)
    (hx₁E : x₁ ≤ c₁) (hL1 : 1 ≤ L) (hLc : L ≤ Lc * E ^ (-b)) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hP : 2 * P ≤ (1 - θ) * (k - 2 * b * K) - θ * (2 * b * K)) :
    (x₀ * L ^ (2 * K)) ^ (1 - θ) * (x₁ * L ^ (2 * K)) ^ θ ≤
      ((c₀ * Lc ^ (2 * K)) ^ (1 - θ) * (c₁ * Lc ^ (2 * K)) ^ θ) * E ^ (2 * P) := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL1
  have hLc0 : 0 ≤ Lc * E ^ (-b) := hL0.trans hLc
  have hLc' : 0 ≤ Lc := (mul_nonneg_iff_of_pos_right (Real.rpow_pos_of_pos hE _)).1 hLc0
  have hLK : L ^ (2 * K) ≤ Lc ^ (2 * K) * E ^ (-(2 * b * K)) := by
    have h := pow_le_pow_left₀ hL0 hLc (2 * K)
    rw [mul_pow, ← Real.rpow_natCast (E ^ (-b)), ← Real.rpow_mul hE.le] at h
    refine h.trans (le_of_eq ?_)
    congr 2
    push_cast
    ring
  have hEp (x : ℝ) : 0 < E ^ x := Real.rpow_pos_of_pos hE x
  have h0 : x₀ * L ^ (2 * K) ≤ (c₀ * Lc ^ (2 * K)) * E ^ (k - 2 * b * K) := by
    calc x₀ * L ^ (2 * K) ≤ (c₀ * E ^ k) * (Lc ^ (2 * K) * E ^ (-(2 * b * K))) :=
          mul_le_mul hx₀E hLK (pow_nonneg hL0 _) (mul_nonneg hc₀ (hEp k).le)
      _ = (c₀ * Lc ^ (2 * K)) * E ^ (k - 2 * b * K) := by
          rw [sub_eq_add_neg, Real.rpow_add hE]
          ring
  have h1 : x₁ * L ^ (2 * K) ≤ (c₁ * Lc ^ (2 * K)) * E ^ (-(2 * b * K)) := by
    calc x₁ * L ^ (2 * K) ≤ c₁ * (Lc ^ (2 * K) * E ^ (-(2 * b * K))) :=
          mul_le_mul hx₁E hLK (pow_nonneg hL0 _) hc₁
      _ = _ := by ring
  have hi := interp_rpow_le (mul_nonneg hc₀ (pow_nonneg hLc' _))
    (mul_nonneg hc₁ (pow_nonneg hLc' _)) hE hθ0 hθ1 (mul_nonneg hx₀ (pow_nonneg hL0 _))
    (mul_nonneg hx₁ (pow_nonneg hL0 _)) h0 h1
  refine hi.trans (mul_le_mul_of_nonneg_left (rpow_mono_small hE hE1 hP) ?_)
  exact mul_nonneg (Real.rpow_nonneg (mul_nonneg hc₀ (pow_nonneg hLc' _)) _)
    (Real.rpow_nonneg (mul_nonneg hc₁ (pow_nonneg hLc' _)) _)

/-! **The seam price in powers of `E`**.

Abstract form of `seamWindowPrice`: with `pe ≤ 2 Cl E^{-qγ}` (the Péclet factor), `S ≥ max 1
(Cl⁻¹ E^{-6δ})` (the block length in cell time), `Tq ≥ Cl⁻¹ E^{-4δ}` (the pulse length in cell time),
`S = Rt · Tq` with `Rt ≤ Cl E^{-2δ}` (the pulse count) and a quiet margin `T2 ≥ Tq`,
`pe^Q (1+S)^Q (e^{-cS} + (5 + Rt) e^{-c Tq/4} + e^{-c T2} + S^{-Ns/2}) ≤ Cs E^a` for any
exponent `a`, once `Ns` is large in terms of `Q`, `a`, `qγ`, `δ` (chosen before `c` and `Cl`).
Each exponential beats every polynomial (`e^{-y} ≤ k!/y^k`).

For `Q = 0` there are no polynomial losses, and for `a ≤ 0` any `Ns ≥ 1` works with a constant
bound. -/

/-- A lower bound `x ≥ Cl⁻¹ E^{-b}` is an upper bound `x⁻¹ ≤ Cl E^b`. -/
theorem inv_le_of_ge_rpow {Cl E b x : ℝ} (hCl : 0 < Cl) (hE : 0 < E)
    (hx : Cl⁻¹ * E ^ (-b) ≤ x) : x⁻¹ ≤ Cl * E ^ b := by
  have h0 : 0 < Cl⁻¹ * E ^ (-b) := mul_pos (inv_pos.2 hCl) (Real.rpow_pos_of_pos hE _)
  have h1 := inv_anti₀ h0 hx
  rwa [mul_inv, inv_inv, Real.rpow_neg hE.le, inv_inv] at h1

/-- `(E^b)^j = E^{b j}`. -/
theorem rpow_pow_eq {E b : ℝ} (hE : 0 < E) (j : ℕ) : (E ^ b) ^ j = E ^ (b * j) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hE.le]

/-- A polynomial in `x` times `k!/(c x)^{Q+j}` is at most a constant times `(x⁻¹)^j`. -/
theorem poly_exp_le {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (Q j : ℕ) (A : ℝ) (hA : 0 ≤ A) :
    A * x ^ Q * Real.exp (-c * x) ≤
      A * ((Q + j).factorial : ℝ) * (c⁻¹) ^ (Q + j) * (x⁻¹) ^ j := by
  have h1 := exp_neg_le_factorial_div (mul_pos hc hx) (Q + j)
  rw [neg_mul]
  calc A * x ^ Q * Real.exp (-(c * x))
      ≤ A * x ^ Q * (((Q + j).factorial : ℝ) / (c * x) ^ (Q + j)) :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg hA (pow_nonneg hx.le _))
    _ = A * ((Q + j).factorial : ℝ) * (c⁻¹) ^ (Q + j) * (x⁻¹) ^ j := by
        have hx' : x ≠ 0 := hx.ne'
        have hc' : c ≠ 0 := hc.ne'
        rw [inv_pow, inv_pow, mul_pow, pow_add, pow_add]
        field_simp

/-- A polynomial times an exponential at a long time: `S^Q e^{-cS} ≤ C E^{b j}`. -/
theorem poly_exp_le_rpow {c Cl E b S : ℝ} (hc : 0 < c) (hCl : 0 < Cl) (hE : 0 < E)
    (hS : Cl⁻¹ * E ^ (-b) ≤ S) (Q j : ℕ) :
    S ^ Q * Real.exp (-c * S) ≤
      ((Q + j).factorial : ℝ) * (c⁻¹) ^ (Q + j) * Cl ^ j * E ^ (b * j) := by
  have hS0 : 0 < S := lt_of_lt_of_le (mul_pos (inv_pos.2 hCl) (Real.rpow_pos_of_pos hE _)) hS
  have h1 := poly_exp_le hc hS0 Q j 1 zero_le_one
  rw [one_mul, one_mul] at h1
  refine h1.trans ?_
  have hinv := inv_le_of_ge_rpow hCl hE hS
  have hp := pow_le_pow_left₀ (inv_nonneg.2 hS0.le) hinv j
  rw [mul_pow, rpow_pow_eq hE] at hp
  have hk : 0 ≤ ((Q + j).factorial : ℝ) * (c⁻¹) ^ (Q + j) :=
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (inv_nonneg.2 hc.le) _)
  calc ((Q + j).factorial : ℝ) * (c⁻¹) ^ (Q + j) * (S⁻¹) ^ j
      ≤ ((Q + j).factorial : ℝ) * (c⁻¹) ^ (Q + j) * (Cl ^ j * E ^ (b * j)) :=
        mul_le_mul_of_nonneg_left hp hk
    _ = _ := by ring

/-- For `E ∈ (0,1]` and `e ≥ b`, a bound `C E^e` is a bound `C E^b`. -/
theorem le_rpow_of_exponent {C E e b X : ℝ} (hC : 0 ≤ C) (hE : 0 < E) (hE1 : E ≤ 1)
    (heb : b ≤ e) (hX : X ≤ C * E ^ e) : X ≤ C * E ^ b :=
  hX.trans (mul_le_mul_of_nonneg_left (rpow_mono_small hE hE1 heb) hC)

/-- `S^Q S^{-(2Q + 2j)/2} = (S⁻¹)^j`. -/
theorem rpow_seam_tail {S : ℝ} (hS : 0 < S) (Q j : ℕ) :
    S ^ Q * S ^ (-((2 * Q + 2 * j : ℕ) : ℝ) / 2) = (S⁻¹) ^ j := by
  rw [← Real.rpow_natCast S Q, ← Real.rpow_add hS, inv_pow, ← Real.rpow_natCast S j,
    ← Real.rpow_neg hS.le]
  congr 1
  push_cast
  ring

/-- The pulse term of the seam price. -/
theorem seam_pulse_term {c Cl E δ Rt Tq S : ℝ} (hc : 0 < c) (hCl : 1 ≤ Cl) (hE : 0 < E)
    (hE1 : E ≤ 1) (hδ : 0 < δ) (hTq : Cl⁻¹ * E ^ (-(4 * δ)) ≤ Tq) (hRt0 : 0 ≤ Rt)
    (hRt : Rt ≤ Cl * E ^ (-(2 * δ))) (hSRT : S = Rt * Tq) (Q j : ℕ) :
    S ^ Q * ((5 + Rt) * Real.exp (-c * (Tq / 4))) ≤
      (Cl ^ Q * (6 * Cl) * (4 ^ Q * (((Q + j).factorial : ℝ) * (c⁻¹) ^ (Q + j) *
        (4 * Cl) ^ j))) * (E ^ (-(2 * δ) * Q) * E ^ (-(2 * δ)) * E ^ (4 * δ * j)) := by
  have hCl0 : 0 < Cl := zero_lt_one.trans_le hCl
  have hTq0 : 0 < Tq :=
    lt_of_lt_of_le (mul_pos (inv_pos.2 hCl0) (Real.rpow_pos_of_pos hE _)) hTq
  have hRtQ : Rt ^ Q ≤ Cl ^ Q * E ^ (-(2 * δ) * Q) := by
    rw [← rpow_pow_eq hE, ← mul_pow]
    exact pow_le_pow_left₀ hRt0 hRt Q
  have h5 : 5 + Rt ≤ 6 * Cl * E ^ (-(2 * δ)) := by
    have h1 : 1 ≤ E ^ (-(2 * δ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hE hE1 (by linarith)
    nlinarith
  have hTq4 : (4 * Cl)⁻¹ * E ^ (-(4 * δ)) ≤ Tq / 4 := by
    rw [mul_inv, mul_assoc]
    linarith
  have hP2 := poly_exp_le_rpow hc (by positivity : 0 < 4 * Cl) hE hTq4 Q j
  have heq : S ^ Q * ((5 + Rt) * Real.exp (-c * (Tq / 4))) =
      (Rt ^ Q * (5 + Rt)) * (4 ^ Q * ((Tq / 4) ^ Q * Real.exp (-c * (Tq / 4)))) := by
    rw [hSRT, mul_pow, div_pow]
    field_simp
  rw [heq]
  have hA : Rt ^ Q * (5 + Rt) ≤ (Cl ^ Q * E ^ (-(2 * δ) * Q)) * (6 * Cl * E ^ (-(2 * δ))) :=
    mul_le_mul hRtQ h5 (by linarith) (by positivity)
  have hB := mul_le_mul_of_nonneg_left hP2 (by positivity : (0 : ℝ) ≤ 4 ^ Q)
  have hEp (x : ℝ) : 0 < E ^ x := Real.rpow_pos_of_pos hE x
  refine (mul_le_mul hA hB (by positivity) (by positivity)).trans (le_of_eq ?_)
  ring

/-- The quiet margin term of the seam price. -/
theorem seam_quiet_margin_term {c Cl E δ Rt Tq T2 S : ℝ} (hc : 0 < c) (hCl : 1 ≤ Cl) (hE : 0 < E)
    (hTq : Cl⁻¹ * E ^ (-(4 * δ)) ≤ Tq) (hT2 : Tq ≤ T2) (hRt0 : 0 ≤ Rt)
    (hRt : Rt ≤ Cl * E ^ (-(2 * δ))) (hSRT : S = Rt * Tq) (Q j : ℕ) :
    S ^ Q * Real.exp (-c * T2) ≤
      (Cl ^ Q * (((Q + j).factorial : ℝ) * (c⁻¹) ^ (Q + j) * Cl ^ j)) *
        (E ^ (-(2 * δ) * Q) * E ^ (4 * δ * j)) := by
  have hCl0 : 0 < Cl := zero_lt_one.trans_le hCl
  have hTq0 : 0 < Tq :=
    lt_of_lt_of_le (mul_pos (inv_pos.2 hCl0) (Real.rpow_pos_of_pos hE _)) hTq
  have hRtQ : Rt ^ Q ≤ Cl ^ Q * E ^ (-(2 * δ) * Q) := by
    rw [← rpow_pow_eq hE, ← mul_pow]
    exact pow_le_pow_left₀ hRt0 hRt Q
  have hexp : Real.exp (-c * T2) ≤ Real.exp (-c * Tq) :=
    Real.exp_le_exp.2 (by nlinarith)
  have h1 : S ^ Q * Real.exp (-c * T2) ≤ Rt ^ Q * (Tq ^ Q * Real.exp (-c * Tq)) := by
    rw [hSRT, mul_pow, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (by positivity))
      (by positivity)
  have hP3 := poly_exp_le_rpow hc hCl0 hE hTq Q j
  have hEp (x : ℝ) : 0 < E ^ x := Real.rpow_pos_of_pos hE x
  refine (h1.trans (mul_le_mul hRtQ hP3 (by positivity) (by positivity))).trans (le_of_eq ?_)
  ring

/-- Three powers of `E` with total exponent at least `b`. -/
theorem rpow_three_le {E x y z b : ℝ} (hE : 0 < E) (hE1 : E ≤ 1) (h : b ≤ x + y + z) :
    E ^ x * E ^ y * E ^ z ≤ E ^ b := by
  rw [← Real.rpow_add hE, ← Real.rpow_add hE]
  exact rpow_mono_small hE hE1 h

/-- Two powers of `E` with total exponent at least `b`. -/
theorem rpow_two_le {E x y b : ℝ} (hE : 0 < E) (hE1 : E ≤ 1) (h : b ≤ x + y) :
    E ^ x * E ^ y ≤ E ^ b := by
  rw [← Real.rpow_add hE]
  exact rpow_mono_small hE hE1 h

/-- The final product of the seam price. -/
theorem seam_price_product {pe S X Cl E qγ c₀ a b : ℝ} (Q : ℕ) (hE : 0 < E) (hS1 : 1 ≤ S)
    (hpe0 : 0 ≤ pe) (hpe : pe ≤ 2 * Cl * E ^ (-qγ)) (hX0 : 0 ≤ X)
    (hX : S ^ Q * X ≤ c₀ * E ^ b) (hab : a = -qγ * Q + b) :
    pe ^ Q * (1 + S) ^ Q * X ≤ (2 * Cl) ^ Q * 2 ^ Q * c₀ * E ^ a := by
  have hEp (x : ℝ) : 0 < E ^ x := Real.rpow_pos_of_pos hE x
  have hCl : 0 ≤ 2 * Cl * E ^ (-qγ) := hpe0.trans hpe
  have hpeQ : pe ^ Q ≤ (2 * Cl) ^ Q * E ^ (-qγ * Q) := by
    rw [← rpow_pow_eq hE, ← mul_pow]
    exact pow_le_pow_left₀ hpe0 hpe Q
  have h1S : (1 + S) ^ Q ≤ 2 ^ Q * S ^ Q := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith) Q
  have hCl' : 0 ≤ (2 * Cl) ^ Q := by
    have : 0 ≤ 2 * Cl := by
      by_contra hneg
      push Not at hneg
      have := mul_neg_of_neg_of_pos hneg (hEp (-qγ))
      linarith
    positivity
  calc pe ^ Q * (1 + S) ^ Q * X
      ≤ ((2 * Cl) ^ Q * E ^ (-qγ * Q)) * (2 ^ Q * S ^ Q) * X :=
        mul_le_mul_of_nonneg_right (mul_le_mul hpeQ h1S (by positivity) (by positivity)) hX0
    _ = ((2 * Cl) ^ Q * E ^ (-qγ * Q) * 2 ^ Q) * (S ^ Q * X) := by ring
    _ ≤ ((2 * Cl) ^ Q * E ^ (-qγ * Q) * 2 ^ Q) * (c₀ * E ^ b) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
    _ = (2 * Cl) ^ Q * 2 ^ Q * c₀ * E ^ a := by
        rw [hab, Real.rpow_add hE]
        ring

/-- **The seam price in powers of `E`.** -/
theorem seamPrice_abstract (Q : ℕ) {δ qγ a : ℝ} (hδ : 0 < δ) :
    ∃ Ns : ℕ, 1 ≤ Ns ∧ ∀ c Cl : ℝ, 0 < c → 1 ≤ Cl → ∃ Cs : ℝ, 0 ≤ Cs ∧
    ∀ E S Tq T2 Rt pe : ℝ, 0 < E → E ≤ 1 → 1 ≤ S → Cl⁻¹ * E ^ (-(6 * δ)) ≤ S →
      Cl⁻¹ * E ^ (-(4 * δ)) ≤ Tq → Tq ≤ T2 → 0 ≤ Rt → Rt ≤ Cl * E ^ (-(2 * δ)) →
      S = Rt * Tq → 0 ≤ pe → pe ≤ 2 * Cl * E ^ (-qγ) →
      pe ^ Q * (1 + S) ^ Q * (Real.exp (-c * S) + (5 + Rt) * Real.exp (-c * (Tq / 4)) +
        Real.exp (-c * T2) + S ^ (-(Ns : ℝ) / 2)) ≤ Cs * E ^ a := by
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = a + qγ * Q := ⟨_, rfl⟩
  obtain ⟨j₁, hj₁⟩ : ∃ j : ℕ, j = ⌈b / (6 * δ)⌉₊ + 1 := ⟨_, rfl⟩
  obtain ⟨j₂, hj₂⟩ : ∃ j : ℕ, j = ⌈(b + 2 * δ * Q + 2 * δ) / (4 * δ)⌉₊ := ⟨_, rfl⟩
  have hj₁b : b ≤ 6 * δ * j₁ := by
    have h := Nat.le_ceil (b / (6 * δ))
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 6 * δ)] at h
    have : ((⌈b / (6 * δ)⌉₊ : ℕ) : ℝ) ≤ (j₁ : ℝ) := by rw [hj₁]; push_cast; linarith
    nlinarith
  have hj₂b : b + 2 * δ * Q + 2 * δ ≤ 4 * δ * j₂ := by
    have h := Nat.le_ceil ((b + 2 * δ * Q + 2 * δ) / (4 * δ))
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 4 * δ), ← hj₂] at h
    linarith
  refine ⟨2 * Q + 2 * j₁, by omega, fun c Cl hc hCl => ?_⟩
  have hCl0 : 0 < Cl := zero_lt_one.trans_le hCl
  refine ⟨(2 * Cl) ^ Q * 2 ^ Q * (((Q + j₁).factorial : ℝ) * (c⁻¹) ^ (Q + j₁) * Cl ^ j₁ +
      (Cl ^ Q * (6 * Cl) * (4 ^ Q * (((Q + j₂).factorial : ℝ) * (c⁻¹) ^ (Q + j₂) *
        (4 * Cl) ^ j₂))) + (Cl ^ Q * (((Q + j₂).factorial : ℝ) * (c⁻¹) ^ (Q + j₂) * Cl ^ j₂)) +
      Cl ^ j₁), by positivity, ?_⟩
  intro E S Tq T2 Rt pe hE hE1 hS1 hS hTq hT2 hRt0 hRt hSRT hpe0 hpe
  have hS0 : 0 < S := zero_lt_one.trans_le hS1
  have hEp (x : ℝ) : 0 < E ^ x := Real.rpow_pos_of_pos hE x
  have hT1 := le_rpow_of_exponent (b := b) (by positivity) hE hE1 (by linarith)
    (poly_exp_le_rpow hc hCl0 hE hS Q j₁)
  have hT2' := (seam_pulse_term hc hCl hE hE1 hδ hTq hRt0 hRt hSRT Q j₂).trans
    (mul_le_mul_of_nonneg_left (rpow_three_le hE hE1 (b := b) (by linarith)) (by positivity))
  have hT3 := (seam_quiet_margin_term hc hCl hE hTq hT2 hRt0 hRt hSRT Q j₂).trans
    (mul_le_mul_of_nonneg_left (rpow_two_le hE hE1 (b := b) (by linarith)) (by positivity))
  have hT4 : S ^ Q * S ^ (-((2 * Q + 2 * j₁ : ℕ) : ℝ) / 2) ≤ Cl ^ j₁ * E ^ b := by
    rw [rpow_seam_tail hS0 Q j₁]
    have hinv := inv_le_of_ge_rpow hCl0 hE hS
    have hp := pow_le_pow_left₀ (inv_nonneg.2 hS0.le) hinv j₁
    rw [mul_pow, rpow_pow_eq hE] at hp
    exact le_rpow_of_exponent (by positivity) hE hE1 (by linarith) hp
  have hX0 : 0 ≤ Real.exp (-c * S) + (5 + Rt) * Real.exp (-c * (Tq / 4)) +
      Real.exp (-c * T2) + S ^ (-((2 * Q + 2 * j₁ : ℕ) : ℝ) / 2) := by
    have := Real.rpow_nonneg hS0.le (-((2 * Q + 2 * j₁ : ℕ) : ℝ) / 2)
    positivity
  refine seam_price_product (b := b) Q hE hS1 hpe0 hpe hX0 ?_ (by rw [hb]; ring)
  calc _ = S ^ Q * Real.exp (-c * S) + S ^ Q * ((5 + Rt) * Real.exp (-c * (Tq / 4))) +
        S ^ Q * Real.exp (-c * T2) + S ^ Q * S ^ (-((2 * Q + 2 * j₁ : ℕ) : ℝ) / 2) := by ring
    _ ≤ _ := add_le_add (add_le_add (add_le_add hT1 hT2') hT3) hT4
    _ = _ := by ring

/-! **High levels make `E = ε_{m-1}` small**.

Rounded scales separate by at least `Λ ≥ 128` (`epsilon_ratio_lower`), so `ε_n ≤ 2^{-n}`, and for
every threshold `E₀ > 0` there is a starting level beyond which `ε_{m-1} ≤ E₀`, uniformly in
`Λ ≥ 128`. A power `E^p ≤ t` follows from `E ≤ t^{1/p}`.

For `E₀ ≥ 1` every level works, and for `m = 1` one has `ε_0 = 1`. -/

theorem epsilon_le_half_pow {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ) (n : ℕ) :
    ocEpsilon q Λ n ≤ (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => simpa using (Scales.epsilon_basic (m := 0) hq hΛ).2.1
  | succ k ih =>
    have hpos := (Scales.epsilon_basic (m := k + 1) hq hΛ).1
    have hr := Scales.epsilon_ratio_lower (m := k + 1) hq hΛ (by omega)
    simp only [Nat.add_sub_cancel] at hr
    have hΛr : (2 : ℝ) ≤ Λ := by exact_mod_cast (by omega : 2 ≤ Λ)
    have h1 : 2 * ocEpsilon q Λ (k + 1) ≤ ocEpsilon q Λ k := by
      have := (le_div_iff₀ hpos).1 hr
      nlinarith
    rw [pow_succ]
    nlinarith

/-- **High levels make `E` small**, uniformly in `Λ ≥ 128`. -/
theorem exists_level_small {q : ℝ} (hq : 1 < q) {E₀ : ℝ} (hE₀ : 0 < E₀) :
    ∃ m₀ : ℕ, ∀ Λ : ℕ, 128 ≤ Λ → ∀ m : ℕ, m₀ ≤ m → ocEpsilon q Λ (m - 1) ≤ E₀ := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hE₀ (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨n + 1, fun Λ hΛ m hm => (epsilon_le_half_pow hq hΛ (m - 1)).trans ?_⟩
  exact (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)).trans hn.le

/-- A small base makes a positive power small. -/
theorem rpow_le_of_le_root {E p t : ℝ} (hE : 0 ≤ E) (hp : 0 < p) (ht : 0 < t)
    (h : E ≤ t ^ (1 / p)) : E ^ p ≤ t := by
  calc E ^ p ≤ (t ^ (1 / p)) ^ p := Real.rpow_le_rpow hE h hp.le
    _ = t := by rw [← Real.rpow_mul ht.le, one_div_mul_cancel hp.ne', Real.rpow_one]

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleJointProofs.Assembly

/-! Mixed jet algebra for the finite time-weighted block readout. -/

/-- The fast derivative of order zero is an isometric copy of the slow field. -/
theorem block_fastZero_mixed_norm (f : Vec 2 → Vec 2 → Vec 2) (r : ℕ) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ 0 (f Y) z) X‖ =
      ‖iteratedFDeriv ℝ r (fun Y => f Y z) X‖ := by
  change ‖iteratedFDeriv ℝ r ((continuousMultilinearCurryFin0 ℝ (Vec 2) (Vec 2)).symm ∘
    (fun Y => f Y z)) X‖ = _
  exact (continuousMultilinearCurryFin0 ℝ (Vec 2) (Vec 2)).symm.norm_iteratedFDeriv_comp_left _ X r

/-- Slow affine resampling has its exact derivative norm factor. -/
theorem block_affine_slow_jet_norm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Vec 2 → F) (n : ℕ) (hf : ContDiff ℝ (n : ℕ) f)
    (a : ℝ) (ha : 0 ≤ a) (X₀ X : Vec 2) :
    ‖iteratedFDeriv ℝ n (fun Y => f (a • (Y - X₀))) X‖ =
      a ^ n * ‖iteratedFDeriv ℝ n f (a • (X - X₀))‖ := by
  have he : (fun Y => f (a • (Y - X₀))) =
      (fun Y => (fun Z => f (a • Z)) (Y + -X₀)) := by
    funext Y
    rw [sub_eq_add_neg]
  rw [he, iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := fun Z => f (a • Z)) n (-X₀) X,
    congrFun (iteratedFDeriv_comp_const_smul a hf) (X + -X₀), norm_smul,
    Real.norm_of_nonneg (pow_nonneg ha _)]
  rfl

/-- A coefficient independent of the fast variable has only fast degree zero. -/
theorem block_fastConstant_mixed_norm (f : Vec 2 → Vec 2) (r q : ℕ) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q (fun _ : Vec 2 => f Y) z) X‖ =
      if q = 0 then ‖iteratedFDeriv ℝ r f X‖ else 0 := by
  by_cases hq : q = 0
  · subst q
    rw [ite_eq_left rfl]
    change ‖iteratedFDeriv ℝ r ((continuousMultilinearCurryFin0 ℝ (Vec 2) (Vec 2)).symm ∘ f) X‖ = _
    exact (continuousMultilinearCurryFin0 ℝ (Vec 2) (Vec 2)).symm.norm_iteratedFDeriv_comp_left f X r
  · simp only [hq, ite_false, iteratedFDeriv_const_of_ne hq, Pi.zero_apply,
      iteratedFDeriv_fun_zero, norm_zero]

/-- A translation of fast phase preserves the full vector mixed jet norm. -/
theorem block_fastShift_mixed_norm (f : Vec 2 → Vec 2 → Vec 2) (r q : ℕ)
    (φ X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q (fun y => f Y (y + φ)) z) X‖ =
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q (f Y) (z + φ)) X‖ := by
  simp_rw [iteratedFDeriv_comp_add_right]

/-- Coordinate bounds control the vector jet in the sup norm, with no dimension loss. -/
theorem block_vector_jet_norm_le (f : Vec 2 → Vec 2) (n : ℕ) (hf : ContDiff ℝ (n : ℕ) f)
    (C : ℝ) (hC : 0 ≤ C) (hcoord : ∀ k X, ‖iteratedFDeriv ℝ n (fun x => f x k) X‖ ≤ C)
    (X : Vec 2) : ‖iteratedFDeriv ℝ n f X‖ ≤ C := by
  have he : iteratedFDeriv ℝ n f X =
      ContinuousMultilinearMap.pi (fun k : Fin 2 => iteratedFDeriv ℝ n (fun x => f x k) X) := by
    ext m k
    have hh := (ContinuousLinearMap.proj k : Vec 2 →L[ℝ] ℝ).iteratedFDeriv_comp_left (x := X)
      hf.contDiffAt le_rfl
    exact (congrArg (fun L => L m) hh).symm
  rw [he, ContinuousMultilinearMap.opNorm_pi]
  exact (pi_norm_le_iff_of_nonneg hC).mpr (fun k => hcoord k X)

/-- A finite sum of smooth independent fields respects positive mixed jet budgets. -/
theorem block_mixed_sum_norm_le {P : Type*} (pieces : Finset P)
    (f : P → Vec 2 → Vec 2 → Vec 2) (r q : ℕ)
    (hf : ∀ p ∈ pieces, IsBoxSmooth r q (f p)) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q (fun y => ∑ p ∈ pieces, f p Y y) z) X‖ ≤
      ∑ p ∈ pieces, ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q (f p Y) z) X‖ := by
  have he (Y : Vec 2) : iteratedFDeriv ℝ q (fun y => ∑ p ∈ pieces, f p Y y) z =
      ∑ p ∈ pieces, iteratedFDeriv ℝ q (f p Y) z :=
    iteratedFDeriv_fun_sum_apply (fun p hp => ((hf p hp).1 Y).contDiffAt)
  simp_rw [he]
  exact finite_jet_finset_sum_norm_le pieces (fun p Y => iteratedFDeriv ℝ q (f p Y) z)
    r (fun p hp => ((hf p hp).2.1 q le_rfl z)) X

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity.CycleJointProofs.Assembly

/-! **Slow Taylor polynomials under an affine rescaling**.

The Taylor polynomial at `X₀` with increment `δ z` of `X ↦ f (δ⁻¹ (X - X₀))` is the Taylor
polynomial of `f` at `0` with increment `z`. This identifies the metric letter of a block
(coefficient `G τ (δ⁻¹ (X - X₀))`, evaluation `taylorSlow 1 Ks · X₀ (δ • z)`) with the metric
Taylor insertion `taylorSlow 1 Ks (G t ·) 0 z`. -/

/-- The iterated derivative of `X ↦ f (δ⁻¹ (X - X₀))` at `X₀` in the direction `δ z` is that of `f`
at `0` in the direction `z`. -/
theorem iteratedFDeriv_rescale_apply (r : ℕ) (f : Vec 2 → ℝ) (X₀ z : Vec 2) {δ : ℝ}
    (hδ : δ ≠ 0) :
    iteratedFDeriv ℝ r (fun X => f (δ⁻¹ • (X - X₀))) X₀ (fun _ => δ • z) =
      iteratedFDeriv ℝ r f 0 (fun _ => z) := by
  let L : Vec 2 ≃L[ℝ] Vec 2 :=
    (LinearEquiv.smulOfNeZero ℝ (Vec 2) δ⁻¹ (inv_ne_zero hδ)).toContinuousLinearEquiv
  have hL : ∀ y, L y = δ⁻¹ • y := fun _ => rfl
  have hsub := iteratedFDeriv_comp_sub (𝕜 := ℝ) (f := f ∘ L) r X₀ X₀
  have hcomp : iteratedFDeriv ℝ r (f ∘ L) 0 =
      (iteratedFDeriv ℝ r f (L 0)).compContinuousLinearMap fun _ => (L : Vec 2 →L[ℝ] Vec 2) := by
    simp only [← iteratedFDerivWithin_univ]
    have h := L.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (Set.mem_univ (L 0)) r
    simpa only [Set.preimage_univ] using h
  have hfun : (fun X => f (δ⁻¹ • (X - X₀))) = fun X => (f ∘ L) (X - X₀) := by
    funext X
    simp only [Function.comp_apply, hL]
  rw [hfun, hsub, sub_self, hcomp]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, ContinuousLinearEquiv.coe_coe,
    hL, smul_zero, smul_smul, inv_mul_cancel₀ hδ, one_smul]

/-- **Slow Taylor polynomials under an affine rescaling.** -/
theorem taylorSlow_rescale (lo K : ℕ) (f : Vec 2 → ℝ) (X₀ z : Vec 2) {δ : ℝ} (hδ : δ ≠ 0) :
    taylorSlow lo K (fun X => f (δ⁻¹ • (X - X₀))) X₀ (δ • z) = taylorSlow lo K f 0 z := by
  unfold taylorSlow
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [iteratedFDeriv_rescale_apply r f X₀ z hδ]

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs.Assembly

/-! The factorial energy of an arbitrary finite, mass-weighted family is a single
nonnegative density. Hölder then interpolates its polynomial moment weight. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

private theorem mass_jet_density_measurable {K : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [CompleteSpace E] (U : PlaneHk Set.univ K E) (j : ℕ) :
    AEMeasurable (fun z => ENNReal.ofReal (∑ w : DerivativeWord2 j,
      ‖planeJetOrder U j w z‖ ^ 2)) volume := by
  apply AEMeasurable.ennreal_ofReal
  apply Finset.aemeasurable_fun_sum
  intro w _
  by_cases hj : j ≤ K
  · exact (CycleWords.planeJetOrder_memLp hj U w).aestronglyMeasurable.norm.aemeasurable.pow_const 2
  · simp only [planeJetOrder, dite_eq_right hj, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact aemeasurable_const

/-- The literal density, with arbitrary extended nonnegative masses and output orders. -/
def massFactorialDensity (p : ι → ℝ≥0∞) (K K' : ι → ℕ)
    (U : ∀ i, PlaneHk Set.univ (K' i) (h i)) (r : ℝ) (z : Vec 2) : ℝ≥0∞ :=
  ∑ i, p i * ∑ j ∈ Finset.range (K i + 1),
    ENNReal.ofReal (r ^ (2 * j) / ((j.factorial : ℝ)) ^ 2) *
      ENNReal.ofReal (∑ w : DerivativeWord2 j, ‖planeJetOrder (U i) j w z‖ ^ 2)

/-- No finiteness of the masses is needed for measurability. -/
theorem massFactorialDensity_aemeasurable (p : ι → ℝ≥0∞) (K K' : ι → ℕ)
    (U : ∀ i, PlaneHk Set.univ (K' i) (h i)) (r : ℝ) :
    AEMeasurable (massFactorialDensity p K K' U r) volume := by
  apply Finset.aemeasurable_fun_sum
  intro i _
  apply aemeasurable_const.mul
  apply Finset.aemeasurable_fun_sum
  intro j _
  exact aemeasurable_const.mul (mass_jet_density_measurable (U i) j)

/-- Base of the polynomial moment weight in the literal factorial norm. -/
def massMomentBase (ϖ : ℝ) (zc z : Vec 2) : ℝ :=
  1 + ϖ ^ 2 * ((z 0 - zc 0) ^ 2 + (z 1 - zc 1) ^ 2)

private theorem mass_moment_base_nonneg (ϖ : ℝ) (zc z : Vec 2) :
    0 ≤ massMomentBase ϖ zc z := by
  unfold massMomentBase
  positivity

private theorem mass_moment_base_measurable (ϖ : ℝ) (zc : Vec 2) :
    Measurable (massMomentBase ϖ zc) := by
  unfold massMomentBase
  fun_prop

/-- Moving all factorial sums inside the integral preserves even infinite masses. -/
theorem weighted_factorial_family_density (p : ι → ℝ≥0∞) (K K' : ι → ℕ)
    (U : ∀ i, PlaneHk Set.univ (K' i) (h i)) (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (r : ℝ) :
    ∑ i, p i * weightedFactorialNormSq n ϖ zc r (K i) (U i) =
      ∫⁻ z, ENNReal.ofReal (massMomentBase ϖ zc z ^ n) * massFactorialDensity p K K' U r z := by
  have hm : AEMeasurable (fun z => ENNReal.ofReal (massMomentBase ϖ zc z ^ n)) volume :=
    ((mass_moment_base_measurable ϖ zc).pow_const n).aemeasurable.ennreal_ofReal
  have hjm (i : ι) (j : ℕ) : AEMeasurable (fun z =>
      ENNReal.ofReal (massMomentBase ϖ zc z ^ n) * (p i *
        (ENNReal.ofReal (r ^ (2 * j) / ((j.factorial : ℝ)) ^ 2) *
          ENNReal.ofReal (∑ w : DerivativeWord2 j, ‖planeJetOrder (U i) j w z‖ ^ 2)))) volume :=
    hm.mul (aemeasurable_const.mul
      (aemeasurable_const.mul (mass_jet_density_measurable (U i) j)))
  simp only [massFactorialDensity, Finset.mul_sum]
  rw [lintegral_finsetSum' _ (fun i _ => Finset.aemeasurable_fun_sum _ (fun j _ => hjm i j))]
  apply Finset.sum_congr rfl
  intro i _
  unfold weightedFactorialNormSq
  rw [Finset.mul_sum, lintegral_finsetSum' _ (fun j _ => hjm i j)]
  apply Finset.sum_congr rfl
  intro j _
  have he : (fun z => ENNReal.ofReal
      ((1 + ϖ ^ 2 * ((z 0 - zc 0) ^ 2 + (z 1 - zc 1) ^ 2)) ^ n *
        ∑ w : DerivativeWord2 j, ‖planeJetOrder (U i) j w z‖ ^ 2)) =
      fun z => ENNReal.ofReal (massMomentBase ϖ zc z ^ n) *
        ENNReal.ofReal (∑ w : DerivativeWord2 j, ‖planeJetOrder (U i) j w z‖ ^ 2) := by
    funext z
    exact ENNReal.ofReal_mul (pow_nonneg (mass_moment_base_nonneg ϖ zc z) n)
  rw [he, ← mul_assoc, ← lintegral_const_mul''
    (p i * ENNReal.ofReal (r ^ (2 * j) / ((j.factorial : ℝ)) ^ 2))
    (f := fun z => ENNReal.ofReal (massMomentBase ϖ zc z ^ n) *
      ENNReal.ofReal (∑ w : DerivativeWord2 j, ‖planeJetOrder (U i) j w z‖ ^ 2))
    (hm.mul (mass_jet_density_measurable (U i) j))]
  apply lintegral_congr
  intro z
  ac_rfl

/-- Hölder for one arbitrary nonnegative density and two polynomial moments. -/
theorem mass_moment_holder (g : Vec 2 → ℝ≥0∞) (hg : AEMeasurable g volume)
    (n n' : ℕ) (hn : n ≤ n') (hn' : 0 < n') (ϖ : ℝ) (zc : Vec 2) :
    (∫⁻ z, ENNReal.ofReal (massMomentBase ϖ zc z ^ n) * g z) ≤
      (∫⁻ z, g z) ^ (1 - (n : ℝ) / n') *
        (∫⁻ z, ENNReal.ofReal (massMomentBase ϖ zc z ^ n') * g z) ^ ((n : ℝ) / n') := by
  have hn'r : (0 : ℝ) < n' := Nat.cast_pos.mpr hn'
  have hθ : 0 ≤ (n : ℝ) / n' := div_nonneg (Nat.cast_nonneg _) hn'r.le
  have hθ1 : (n : ℝ) / n' ≤ 1 := (div_le_one hn'r).mpr (Nat.cast_le.mpr hn)
  have h1θ : 0 ≤ 1 - (n : ℝ) / n' := sub_nonneg.mpr hθ1
  have hw : AEMeasurable (fun z => ENNReal.ofReal (massMomentBase ϖ zc z ^ n')) volume :=
    ((mass_moment_base_measurable ϖ zc).pow_const n').aemeasurable.ennreal_ofReal
  have he (z : Vec 2) : ENNReal.ofReal (massMomentBase ϖ zc z ^ n) * g z =
      g z ^ (1 - (n : ℝ) / n') *
        (ENNReal.ofReal (massMomentBase ϖ zc z ^ n') * g z) ^ ((n : ℝ) / n') := by
    have hpow : (ENNReal.ofReal (massMomentBase ϖ zc z ^ n')) ^ ((n : ℝ) / n') =
        ENNReal.ofReal (massMomentBase ϖ zc z ^ n) := by
      rw [ENNReal.ofReal_rpow_of_nonneg
        (pow_nonneg (mass_moment_base_nonneg ϖ zc z) _) hθ,
        ← Real.rpow_natCast (massMomentBase ϖ zc z) n',
        ← Real.rpow_mul (mass_moment_base_nonneg ϖ zc z),
        mul_div_cancel₀ _ hn'r.ne', Real.rpow_natCast]
    rw [ENNReal.mul_rpow_of_nonneg _ _ hθ, hpow]
    rw [mul_left_comm,
      ← ENNReal.rpow_add_of_nonneg _ _ h1θ hθ]
    simp only [sub_add_cancel, ENNReal.rpow_one]
  simp_rw [he]
  exact ENNReal.lintegral_mul_norm_pow_le hg (hw.mul hg) h1θ hθ (sub_add_cancel _ _)

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! Hölder interpolation in the moment weight, with the exact family statement
of mass interpolation. The literal type keeps this proof independent of the PDE imports of the one-patch statement. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
universe u v
namespace AVRegularity.CycleJointProofs.Assembly

/-- Moment interpolation for arbitrary mass-weighted plane Sobolev families. -/
theorem massInterpolation :
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (p : ι → ℝ≥0∞) (K K' : ι → ℕ) (U : ∀ i, PlaneHk Set.univ (K' i) (h i)) (n n' : ℕ),
    n ≤ n' → 0 < n' → ∀ (ϖ : ℝ) (zc : Vec 2) (r : ℝ),
    ∑ i, p i * weightedFactorialNormSq n ϖ zc r (K i) (U i) ≤
      (∑ i, p i * weightedFactorialNormSq 0 ϖ zc r (K i) (U i)) ^ (1 - (n : ℝ) / n') *
        (∑ i, p i * weightedFactorialNormSq n' ϖ zc r (K i) (U i)) ^ ((n : ℝ) / n') := by
  intro ι _ h _ _ _ _ _ p K K' U n n' hn hn' ϖ zc r
  rw [weighted_factorial_family_density p K K' U n ϖ zc r,
    weighted_factorial_family_density p K K' U 0 ϖ zc r,
    weighted_factorial_family_density p K K' U n' ϖ zc r]
  simpa only [pow_zero, ENNReal.ofReal_one, one_mul] using
    mass_moment_holder (massFactorialDensity p K K' U r)
      (massFactorialDensity_aemeasurable p K K' U r) n n' hn hn' ϖ zc

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **Level C of the route to `cycle_joint`: statements**.

`NonQuietCoreStatement`: a piece of the preparation schedule that carries a non-quiet output
time `t` has `t` in the open core of its own label's block (`core_label`, with the support of
the slow envelope carried by every pulse).

`PlaneModelExtensionStatement`: a linear plane model defined on data at the family's
descending slots, bounded in a weighted factorial norm by the `L²` norm of a continuous image of
the slot-`0` truncation, extends uniquely to `L²` data with the same bound and finite radial
moments (density of the truncations, extension in the Hilbert norm, Fatou for the weighted norm). -/

@[expose] public section

open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

/-- **Output times outside the trimmed quiet times lie in the core of the piece's block.**
For a preparation chart schedule (`core_label` at the margin `τ' - τ/24`), every
output time of a piece in `[tS, tZ]` outside the trimmed quiet times lies in the open core
`((l - 1/2) τ'' + (τ' - τ/24), (l + 1/2) τ'' - (τ' - τ/24))` of the block of the piece's label `l`. -/
def NonQuietCoreStatement : Prop :=
  ∀ {ι : Type u} {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
    {D : ℕ} {P' : Type w} {Ctx : P' → Type x}
    (α q : ℝ) (Λ m : ℕ) (_hΛ : 1 ≤ Λ) (ζ : ℝ → ℝ) (φ : ℝ → Vec 2 → ℝ)
    (hφ : IsAdmissibleStream φ) (tS tZ Cpad Cage : ℝ) (Npad : ℕ) (l₀ : ℤ) (P : ℕ)
    (F : ChartedFamily ι h D P' Ctx)
    (_hsched : IsPreparationChartSchedule α q Λ m φ hφ tS tZ Cpad Cage Npad l₀ P F),
    ∀ p, ∀ t ∈ (F.piece p).output ∩ Set.Icc tS tZ, t ∉ ocTrimmedQuietTimes α q Λ ζ m →
      t ∈ Set.Ioo ((((F.piece p).label : ℝ) - 1 / 2) * ocTauPP α q Λ m +
          (ocTauP α q Λ m - ocTau α q Λ m / 24))
        ((((F.piece p).label : ℝ) + 1 / 2) * ocTauPP α q Λ m -
          (ocTauP α q Λ m - ocTau α q Λ m / 24))

/-- **Output times outside a quiet set lie in the core of the piece's block**: the
conclusion with a set `S` of quiet times (fast independence is available on trimmed
quiet times only, so the level-C statements take the set as a parameter), at the core margin
`τ' - τ/24`. For `S = ocTrimmedQuietTimes` it is the conclusion of
`NonQuietCoreStatement`. -/
def IsCoreOutside {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P' : Type*} {Ctx : P' → Type*} (α q : ℝ) (Λ m : ℕ)
    (F : ChartedFamily ι h D P' Ctx) (tS tZ : ℝ) (S : Set ℝ) : Prop :=
  ∀ p, ∀ t ∈ (F.piece p).output ∩ Set.Icc tS tZ, t ∉ S →
    t ∈ Set.Ioo ((((F.piece p).label : ℝ) - 1 / 2) * ocTauPP α q Λ m +
        (ocTauP α q Λ m - ocTau α q Λ m / 24))
      ((((F.piece p).label : ℝ) + 1 / 2) * ocTauPP α q Λ m - (ocTauP α q Λ m - ocTau α q Λ m / 24))

/-- **Extension of a plane model to `L²` data.** Let `P` be a linear map from data at
slots `K` to plane fields of orders `M i ≤ Mb`, whose mass-weighted factorial norm of order `Mb`
at radius `r > 0`, with weight `(1 + ϖ² |x - y|²)^n` (`ϖ > 0`, `n ≥ 4`), is at most `C²` times the
mass-weighted squared norm of `ℓ i` applied to the slot-`0` truncation of the datum. Then there is
a linear map `Q` on `L²` data that agrees with `P` on truncations, obeys the same bound, has finite
radial moments around `y`, and is the only linear map with these two properties for any constant
`C'` in place of `C`. -/
def PlaneModelExtensionStatement : Prop :=
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ) (_hπ : ∀ i, 0 < π i) (K M : ι → ℕ) (Mb n : ℕ) (_hM : ∀ i, M i ≤ Mb)
    (_hn : 4 ≤ n) (ϖ r C : ℝ) (_hϖ : 0 < ϖ) (_hr : 0 < r) (y : Vec 2)
    (ℓ : ∀ i, TorusHk 0 (h i) →L[ℝ] PlaneHk Set.univ 0 (h i))
    (P : (∀ i, TorusHk (K i) (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (M i) (h i)))
    (_hP : ∀ f, ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ y r Mb (P f i) ≤
      ENNReal.ofReal (C ^ 2 * ∑ i, (π i)⁻¹ *
        ‖ℓ i (truncateTorusHk (Nat.zero_le (K i)) (f i))‖ ^ 2)),
    ∃ Q : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (M i) (h i)),
      (∀ f, Q (fun i => truncateTorusHk (Nat.zero_le (K i)) (f i)) = P f) ∧
      (∀ g, ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ y r Mb (Q g i) ≤
        ENNReal.ofReal (C ^ 2 * ∑ i, (π i)⁻¹ * ‖ℓ i (g i)‖ ^ 2)) ∧
      (∀ g i, CycleJointProofs.HasRadialPlaneMoments (Q g i) y) ∧
      ∀ (C' : ℝ) (Q' : (∀ i, TorusHk 0 (h i)) →ₗ[ℝ] (∀ i, PlaneHk Set.univ (M i) (h i))),
        (∀ f, Q' (fun i => truncateTorusHk (Nat.zero_le (K i)) (f i)) = P f) →
        (∀ g, ∑ i, ENNReal.ofReal ((π i)⁻¹) * weightedFactorialNormSq n ϖ y r Mb (Q' g i) ≤
          ENNReal.ofReal (C' ^ 2 * ∑ i, (π i)⁻¹ * ‖ℓ i (g i)‖ ^ 2)) →
        Q' = Q

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **Uniqueness of word chains with finite moment energies: statement**.

`WordChainUniqueStatement`: two word chains (`IsPlaneChain` with `wordChainData`) on `[a, b]` with
the same datum, metric, letters, drift and slots, whose `H^{κ+1}` fields have finite
time-integrated weighted gradient energies of every moment order, have the same levels at every
time of the window.

The edge-free clause of the one-patch statement uses it at slot `0`: the old word chains of the two-block theorem at slot `0` and the slot-`0`
truncations of its old word chains at slot `K` agree, so the cell model of the seam is the same at
both slots. -/

@[expose] public section

open MeasureTheory Homogenization AVRegularity.Sobolev

universe u v

namespace AVRegularity.CycleJointProofs.Assembly

/-- **Word chains with finite moment energies are unique.** -/
def WordChainUniqueStatement : Prop :=
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {D N : ℕ} (_hD : 2 ≤ D) (π : ι → ℝ) (_hπ : ∀ i, 0 < π i)
    -- the metric and the drift
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (_hG : IsCellMetric (fun t _ => G t)) (g : ℝ)
    (_hg : g ≤ 1 / 4) (_hGn : IsMetricNearIdentity (fun t _ => G t) g)
    (vd : ℝ → Vec 2 → Vec 2) (_hv : IsCellDrift vd) (_hvs : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (vd t))
    -- the window and the letters
    (a b : ℝ) (_hab : a ≤ b) (J H : ℕ) (letters : Fin N → CycleLetter ι h D)
    (_hL : ∀ j, IsCycleLetter π (letters j) (Set.Icc a b ×ˢ Set.univ) J H)
    (_hm : ∀ j x y o, ∀ γ ∈ (letters j).edge x y o, ∀ α X z,
      Measurable fun t => γ.coeff α t X z)
    (X₀ : Vec 2) (δ : ℝ) (κ : Fin (N + 1) → ι → ℕ) (_hκJ : ∀ j x, κ j x ≤ J)
    -- the two chains
    (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (u u' : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
    (w w' : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x))
    (_hc : IsPlaneChain (wordChainData G letters X₀ δ) κ a b vd f (fun _ _ _ => 0) u w)
    (_hc' : IsPlaneChain (wordChainData G letters X₀ δ) κ a b vd f (fun _ _ _ => 0) u' w')
    -- their moment energies
    (ϖ ρ : ℝ) (_hϖ : 0 < ϖ) (_hρ : 0 < ρ)
    (_he : ∀ j x n,
      (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq n ϖ 0 ρ (κ j x) (w j x t)) ≠ ⊤)
    (_he' : ∀ j x n,
      (∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq n ϖ 0 ρ (κ j x) (w' j x t)) ≠ ⊤),
    ∀ j x, ∀ t ∈ Set.Icc a b, u j x t = u' j x t

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **Uniqueness of word chains: the steps**.

Statements only (steps of the proof of `WordChainUniqueStatement`, each as a `Prop`); the
uniqueness itself is `wordChainUnique`.

* `WordChainLevelEq`: the induction clause at level `j`: equal values at every time of the window
  and equal `H^{κ+1}` fields almost everywhere on the window.
* `WordChainFluxCongrStatement` (proved as `wordChainFluxCongr`): the previous-letter flux at
  level `j+1` depends only on the fields of level `j`.
* `PlaneTruncEqStatement` (proved as `planeTruncEq`): (i) ⇒ (ii) through clause 3 of the solution
  class and the injectivity of the truncation.
* the component step: two chains with a common source `V` for the component `i` agree on that
  component (Duhamel formula on `[a, t]`, then fibre coordinates); the source step: the
  finite-energy source `V` of level `j+1`; the level step and the assembly. These are in the proof
  of `wordChainUnique`. -/

@[expose] public section

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleWords

universe u v

namespace AVRegularity.CycleJointProofs.Assembly

/-- The induction clause at level `j`. -/
def WordChainLevelEq {ι : Type u} {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {N : ℕ}
    (κ : Fin (N + 1) → ι → ℕ) (a b : ℝ)
    (u u' : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x) (h x))
    (w w' : ∀ (j : Fin (N + 1)) (x : ι), ℝ → PlaneHk Set.univ (κ j x + 1) (h x))
    (j : Fin (N + 1)) : Prop :=
  (∀ x, ∀ t ∈ Set.Icc a b, u j x t = u' j x t) ∧
    ∀ x, ∀ᵐ t ∂(volume.restrict (Set.Icc a b)), w j x t = w' j x t

/-- The previous-letter flux at level `j + 1` depends only on the fields of level `j`. -/
def WordChainFluxCongrStatement : Prop :=
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {D N : ℕ} (letters : Fin N → CycleLetter ι h D) (X0 : Vec 2) (δ : ℝ)
    (κ : Fin (N + 1) → ι → ℕ)
    (U U' : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (j : Fin N) (x : ι) (_hU : ∀ y, U (j.castSucc, y) = U' (j.castSucc, y)) (t : ℝ),
    wordChainPreviousFlux letters X0 δ κ U (j.succ, x) t =
      wordChainPreviousFlux letters X0 δ κ U' (j.succ, x) t

/-- (i) ⇒ (ii): equal `H^K` values force equal `H^{K+1}` lifts. -/
def PlaneTruncEqStatement : Prop :=
  ∀ {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ} (a b : ℝ)
    (w w' : ℝ → PlaneHk Set.univ (K + 1) E) (u u' : ℝ → PlaneHk Set.univ K E)
    (_hw : ∀ᵐ s ∂(volume.restrict (Set.Icc a b)), truncatePlaneHk (Nat.le_succ K) (w s) = u s)
    (_hw' : ∀ᵐ s ∂(volume.restrict (Set.Icc a b)), truncatePlaneHk (Nat.le_succ K) (w' s) = u' s)
    (_hu : ∀ t ∈ Set.Icc a b, u t = u' t),
    ∀ᵐ s ∂(volume.restrict (Set.Icc a b)), w s = w' s

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **The statement of `cycle_seam`** (restated as a definition).

`CycleSeamStatement` is the type of `Providers.cycle_seam`
verbatim, with the universes of the family named and the
unused binders underscored. The glue of the one-patch statement takes it as a hypothesis (`cycle_seam` is not imported by
library code). -/

@[expose] public section

open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal

universe u v

namespace AVRegularity.CycleJointProofs.Assembly

/-- The statement of `cycle_seam`, verbatim (named universes). -/
def CycleSeamStatement : Prop :=
  ∀ (K : ScalarConstants),
    ∃ g₁ : ℝ, 0 < g₁ ∧
    ∀ (D H Kmax pout k : ℕ) (_hD : 2 ≤ D) (Nm Np : ℕ) (dO KsO : Fin Nm → ℕ) (posO : Fin Nm → Bool)
      (dF KsF : Fin Np → ℕ) (posF : Fin Np → Bool) (_hk : Kmax + ∑ i, dO i + 2 ≤ k),
    ∃ Q : ℕ, ∀ Mmod Nmod : ℕ, ∃ qΥ : ℕ,
    ∀ (Cout C0 Cs CU CH : ℝ) (_hCout : 0 < Cout) (_hCH : 0 < CH) (χm : Vec 2 → ℝ)
      (_hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) χm) (_hχ_even : ∀ ξ, χm (-ξ) = χm ξ)
      (_hχ_supp : ∀ ξ, 2 * K.ξlo ≤ Real.sqrt (vecDot ξ ξ) → χm ξ = 0)
      (_hχ_one : ∃ ε : ℝ, 0 < ε ∧ ∀ ξ, Real.sqrt (vecDot ξ ξ) ≤ ε → χm ξ = 1),
    ∃ (c : ℝ) (CM CN : ℕ → ℝ), 0 < c ∧ (∀ M, 0 < CM M) ∧ (∀ N, 0 < CN N) ∧
      ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
        [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
        [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
        (π : ι → ℝ) (_hπ : ∀ x, 0 < π x)
        (lettersF : Fin Np → CycleLetter ι h D)
        (_hlF : ∀ i, (lettersF i).order = dF i ∧ (lettersF i).slow = KsF i ∧
          (lettersF i).positive = posF i)
        -- the common scales
        (η S ηg rstar ϖ : ℝ) (_hη : 0 < η) (_hη1 : η ≤ 1) (_hS : 1 ≤ S) (_hηg : 0 < ηg)
        (_hηg1 : ηg ≤ 1) (_hrstar : 0 < rstar) (_hrstarC : rstar ≤ Cout) (_hϖ : ϖ = Real.sqrt (η / S))
        -- the future complete block
        (tF : ℝ) (GF : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (vF : ℝ → Vec 2 → Vec 2) (gF : ℝ)
        (_hGmF : IsCellMetric (fun t _ => GF t)) (_hvF : IsCellDrift vF)
        (_hv0F : ∀ t (k : Fin 2), cellMean (fun x => (vF t x k : ℂ)) = 0)
        (_hvsF : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (vF t))
        (_hvwF : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, vF t x i ^ 2) ≤ K.Cw)
        (_hvjF : ∀ (j : ℕ) t z,
          ‖iteratedFDeriv ℝ j (fun z' => Real.sqrt η • vF t z') z‖ ≤ K.Cvj j)
        (_hg0F : 0 ≤ gF) (_hgF : gF ≤ K.g0) (_hg₁F : gF ≤ g₁) (_hGnF : IsMetricNearIdentity (fun t _ => GF t) gF)
        (regF : BlockRegions) (_pkgF : ScalarPackage K η GF vF tF S ϖ regF)
        (_hletF : ∀ i, IsCycleLetter π (lettersF i) (Set.Icc tF (tF + S) ×ˢ Set.univ)
          (2 * (k + Kmax + pout + (∑ i, KsO i + ∑ i, KsF i) + ∑ i, dF i + 2) +
            max (Finset.univ.sup dO) (Finset.univ.sup dF) + 2) H)
        (_htransF : ∀ i, IsTransverseOnPulses (lettersF i).edge
          (fun p : Fin regF.P => Set.Icc (regF.lo p) (regF.hi p)) regF.orient)
        (_hquietF : ∀ i, IsQuietOn (lettersF i).edge vF (regF.quiet ∩ Set.Icc tF (tF + S)))
        (_hmeasF : ∀ i x y o, ∀ γ ∈ (lettersF i).edge x y o, ∀ α X z,
          Measurable fun t => γ.coeff α t X z)
        (a : ℝ) (_ha : 0 ≤ a) (_haS : a ≤ S) (_hquietMargin : Set.Icc tF (tF + a) ⊆ regF.quiet)
        (X₀F : Vec 2)
        (_hC0 : peFactor η ^ Q * (1 + S) ^ Q * (1 + regF.joins) *
          Real.exp (-c * regF.buffer) ≤ C0),
      ∃ Kp : (∀ x, Vec 2 → h x) →ₗ[ℝ] (∀ x, Vec 2 → h x),
        -- the future slots and output orders (the kernel is uniform in them), the old
        -- letters, the chart transition and the old partial piece
        ∀ (κF : Fin (Np + 1) → ι → ℕ) (Kout : ι → ℕ) (_hKout : ∀ x, Kout x ≤ Kmax)
          (_hκFf : ∀ x, Kout x ≤ κF (Fin.last Np) x)
          (_hκF : ∀ (j : Fin Np) x y (o : Finset.Icc 2 D), (lettersF j).edge x y o ≠ [] →
            κF j.succ x + o.1 ≤ κF j.castSucc y + 2)
          (lettersO : Fin Nm → CycleLetter ι h D)
          (_hlO : ∀ i, (lettersO i).order = dO i ∧ (lettersO i).slow = KsO i ∧
            (lettersO i).positive = posO i)
          (Υ Υinv : Vec 2 → Vec 2) (gU δ : ℝ) (_hδ : δ = ϖ * ηg)
          (_hgU : 0 ≤ gU ∧ gU ≤ K.g0) (_hΥ : IsCenteredTransition Υ Υinv gU δ CU qΥ)
          (_hΥs : ContDiff ℝ (⊤ : ℕ∞) Υinv)
          (tO SO aO bO : ℝ) (GO : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (vO : ℝ → Vec 2 → Vec 2) (gO : ℝ)
          (_hGmO : IsCellMetric (fun t _ => GO t)) (_hvO : IsCellDrift vO)
          (_hv0O : ∀ t (k : Fin 2), cellMean (fun x => (vO t x k : ℂ)) = 0)
          (_hvsO : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (vO t))
          (_hvwO : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, vO t x i ^ 2) ≤ K.Cw)
          (_hvjO : ∀ (j : ℕ) t z,
            ‖iteratedFDeriv ℝ j (fun z' => Real.sqrt η • vO t z') z‖ ≤ K.Cvj j)
          (_hg0O : 0 ≤ gO) (_hgO : gO ≤ K.g0) (_hg₁O : gO ≤ g₁) (_hGnO : IsMetricNearIdentity (fun t _ => GO t) gO)
          (regO : BlockRegions) (_pkgO : CoreScalarPackage K η GO vO tO SO ϖ regO)
          (_hwin : tO ≤ aO ∧ aO ≤ bO ∧ bO ≤ tO + SO) (_hdur : bO - aO ≤ CH * S)
          (_hC0O : peFactor η ^ Q * (1 + S) ^ Q * (1 + regO.joins) *
            Real.exp (-c * regO.buffer) ≤ C0)
          (_hseam : Set.Icc (bO - regF.buffer) bO ⊆ regO.quiet ∩ Set.Icc tO (tO + SO))
          (_hletO : ∀ i, IsCycleLetter π (lettersO i) (Set.Icc aO bO ×ˢ Set.univ)
            (2 * (k + Kmax + pout + (∑ i, KsO i + ∑ i, KsF i) + ∑ i, dF i + 2) +
              max (Finset.univ.sup dO) (Finset.univ.sup dF) + 2) H)
          (_htransO : ∀ i, IsTransverseOnPulses (lettersO i).edge
            (fun p : Fin regO.P => Set.Icc (regO.lo p) (regO.hi p)) regO.orient)
          (_hquietO : ∀ i, IsQuietOn (lettersO i).edge vO (regO.quiet ∩ Set.Icc tO (tO + SO)))
          (_hmeasO : ∀ i x y o, ∀ γ ∈ (lettersO i).edge x y o, ∀ α X z,
            Measurable fun t => γ.coeff α t X z)
          (X₀O : Vec 2) (κO : Fin (Nm + 1) → ι → ℕ)
          (_hκO : ∀ (j : Fin Nm) x y (o : Finset.Icc 2 D), (lettersO j).edge x y o ≠ [] →
            κO j.succ x + o.1 ≤ κO j.castSucc y + 2)
          (_hκmatch : ∀ x, κF 0 x ≤ κO (Fin.last Nm) x)
          (f : ∀ x, PlaneHk Set.univ (κO 0 x) (h x))
          (_hfsupp : ∀ x, ∀ᵐ z : Vec 2 ∂volume, (Cs / ϖ) ^ 2 < z 0 ^ 2 + z 1 ^ 2 →
            planeValue (f x) z = 0)
          (uO : ∀ (j : Fin (Nm + 1)) (x : ι), ℝ → PlaneHk Set.univ (κO j x) (h x))
          (wO : ∀ (j : Fin (Nm + 1)) (x : ι), ℝ → PlaneHk Set.univ (κO j x + 1) (h x))
          (_hchainO : IsPlaneChain (wordChainData GO lettersO X₀O δ) κO aO bO vO f
            (fun _ _ _ => 0) uO wO)
          (fF : ∀ x, PlaneHk Set.univ (κF 0 x) (h x))
          (_hfF : ∀ x, planeValue (fF x) =ᵐ[volume]
            fun z => planeValue (uO (Fin.last Nm) x bO) (Υ z))
          (uF : ∀ (j : Fin (Np + 1)) (x : ι), ℝ → PlaneHk Set.univ (κF j x) (h x))
          (wF : ∀ (j : Fin (Np + 1)) (x : ι), ℝ → PlaneHk Set.univ (κF j x + 1) (h x))
          (_hchainF : IsPlaneChain (wordChainData GF lettersF X₀F δ) κF tF (tF + S) vF fF
            (fun _ _ _ => 0) uF wF),
        (∀ x, ∀ M : ℕ, ContDiff ℝ M
          (Kp (fun x' z => fourierCutoff (fun θ => χm ((Real.sqrt η)⁻¹ • θ))
              (planeValue (uO (Fin.last Nm) x' bO)) (Υ z)) x)) ∧
        (∀ M : ℕ, M ≤ Mmod →
          weightedJetNorm π (pout : ℝ) M ϖ ϖ⁻¹
              (fun x _ wd z => orderedDerivative wd
                (Kp (fun x' z' => fourierCutoff (fun θ => χm ((Real.sqrt η)⁻¹ • θ))
                  (planeValue (uO (Fin.last Nm) x' bO)) (Υ z')) x) z) ≤
            ENNReal.ofReal (CM M * (wordTheta ηg lettersO * wordTheta ηg lettersF)) *
              momentNorm π 0 ϖ (fun x => planeValue (f x))) ∧
        (∀ N : ℕ, 1 ≤ N → N ≤ Nmod →
          weightedJetNorm π (pout : ℝ) Kmax ϖ rstar
              (fun x a' wd z => if a' ≤ Kout x then planeJetOrder (uF (Fin.last Np) x (tF + S)) a' wd z -
                orderedDerivative wd
                  (Kp (fun x' z' => fourierCutoff (fun θ => χm ((Real.sqrt η)⁻¹ • θ))
                    (planeValue (uO (Fin.last Nm) x' bO)) (Υ z')) x) z else 0) ≤
            ENNReal.ofReal (CN N * (wordTheta ηg lettersO * wordTheta ηg lettersF) *
                peFactor η ^ Q * (1 + S) ^ Q *
                (Real.exp (-c * S) + (1 + regF.joins) * Real.exp (-c * regF.buffer) +
                  Real.exp (-c * a) + S ^ (-(N : ℝ) / 2))) *
              momentNorm π 0 ϖ (fun x => planeValue (f x)))

end AVRegularity.CycleJointProofs.Assembly
end
end
