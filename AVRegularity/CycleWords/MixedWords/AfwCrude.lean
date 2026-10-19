-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.AmplitudeLimit
import AVRegularity.CycleWords.MixedWords.BlochContinuity
import AVRegularity.Analysis.Convolution
import AVRegularity.CycleWords.MixedWords.AmplitudePlancherel
import Mathlib.Algebra.Ring.IsFormallyReal

section
@[expose] public section
namespace AVRegularity.CycleWords.Assembly

/-! # The crude error budget

The crude source bound of a stage `k` is
`ε_k = Θ ∑_{k' < k} L^{k'} (1 + T)^{k'} (2D_{k'} + D_{p,k'})` (`afw_crude_sources`), where
`T = b − a ≤ C_H S`. With `Θ ≤ Θ' P^{q₁}`, `1 ≤ L ≤ L' P^{q₂}`,
`D, D_p ≤ c P^{q₃} d` for a monotone nonnegative `d` and `P ≥ 1`, the integrated error is
polynomial: `ε_k T ≤ C P^Q (1 + S)^Q d_k` for `k ≤ M`, with
`C = 3 Θ' c M L'^M (1 + C_H)^{M+1}` and `Q = q₁ + q₂ M + q₃ + M + 1` (`crude_eps_le`). This is the
`P_e`-polynomial bookkeeping of the poorly buffered instantiation. -/

/-- **The crude error budget.** -/
theorem crude_eps_le {Θ Θ' L L' c P S T CH : ℝ} {q₁ q₂ q₃ M k : ℕ} (D Dp d : ℕ → ℝ)
    (hP : 1 ≤ P) (hS : 0 ≤ S) (hT : 0 ≤ T) (hTS : T ≤ CH * S) (hCH : 0 ≤ CH)
    (hΘ0 : 0 ≤ Θ) (hΘ : Θ ≤ Θ' * P ^ q₁) (hL1 : 1 ≤ L) (hL : L ≤ L' * P ^ q₂)
    (hc : 0 ≤ c) (hd0 : ∀ k, 0 ≤ d k) (hdm : Monotone d)
    (hD0 : ∀ k, 0 ≤ D k) (hDp0 : ∀ k, 0 ≤ Dp k)
    (hD : ∀ k, D k ≤ c * P ^ q₃ * d k) (hDp : ∀ k, Dp k ≤ c * P ^ q₃ * d k) (hkM : k ≤ M) :
    Θ * (∑ k' ∈ Finset.range k, L ^ k' * (1 + T) ^ k' * (2 * D k' + Dp k')) * T ≤
      3 * Θ' * c * M * L' ^ M * (1 + CH) ^ (M + 1) *
        P ^ (q₁ + q₂ * M + q₃ + M + 1) * (1 + S) ^ (q₁ + q₂ * M + q₃ + M + 1) * d k := by
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hT1 : 1 ≤ 1 + T := by linarith
  have hS1 : 1 ≤ 1 + S := by linarith
  have hL0 : 0 ≤ L := zero_le_one.trans hL1
  have hL'0 : 0 ≤ L' * P ^ q₂ := hL0.trans hL
  -- `1 + T ≤ (1 + C_H)(1 + S)`
  have hTb : 1 + T ≤ (1 + CH) * (1 + S) := by nlinarith
  have hdk : ∀ k' ∈ Finset.range k, d k' ≤ d k := fun k' hk' =>
    hdm (Finset.mem_range.1 hk').le
  -- each term
  have hterm : ∀ k' ∈ Finset.range k, L ^ k' * (1 + T) ^ k' * (2 * D k' + Dp k') ≤
      (L' * P ^ q₂) ^ M * ((1 + CH) * (1 + S)) ^ M * (3 * (c * P ^ q₃ * d k)) := by
    intro k' hk'
    have hk'M : k' ≤ M := (Finset.mem_range.1 hk').le.trans hkM
    have h1 : L ^ k' ≤ (L' * P ^ q₂) ^ M :=
      (pow_le_pow_right₀ hL1 hk'M).trans (pow_le_pow_left₀ hL0 hL M)
    have h2 : (1 + T) ^ k' ≤ ((1 + CH) * (1 + S)) ^ M :=
      (pow_le_pow_right₀ hT1 hk'M).trans (pow_le_pow_left₀ (by linarith) hTb M)
    have h3 : 2 * D k' + Dp k' ≤ 3 * (c * P ^ q₃ * d k) := by
      have hdk' := hdk k' hk'
      have hcp : 0 ≤ c * P ^ q₃ := mul_nonneg hc (pow_nonneg hP0 _)
      have e1 : D k' ≤ c * P ^ q₃ * d k := (hD k').trans (mul_le_mul_of_nonneg_left hdk' hcp)
      have e2 : Dp k' ≤ c * P ^ q₃ * d k := (hDp k').trans (mul_le_mul_of_nonneg_left hdk' hcp)
      linarith
    have hLk0 : 0 ≤ L ^ k' := pow_nonneg hL0 _
    have hTk0 : 0 ≤ (1 + T) ^ k' := pow_nonneg (by linarith) _
    calc L ^ k' * (1 + T) ^ k' * (2 * D k' + Dp k')
        ≤ (L' * P ^ q₂) ^ M * ((1 + CH) * (1 + S)) ^ M * (2 * D k' + Dp k') :=
          mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 hTk0 (pow_nonneg hL'0 _))
            (by linarith [hD0 k', hDp0 k'])
      _ ≤ (L' * P ^ q₂) ^ M * ((1 + CH) * (1 + S)) ^ M * (3 * (c * P ^ q₃ * d k)) :=
          mul_le_mul_of_nonneg_left h3
            (mul_nonneg (pow_nonneg hL'0 _) (pow_nonneg (by positivity) _))
  set X := (L' * P ^ q₂) ^ M * ((1 + CH) * (1 + S)) ^ M * (3 * (c * P ^ q₃ * d k)) with hX
  have hX0 : 0 ≤ X := by
    have : 0 ≤ c * P ^ q₃ * d k := mul_nonneg (mul_nonneg hc (pow_nonneg hP0 _)) (hd0 k)
    positivity
  have hsum : ∑ k' ∈ Finset.range k, L ^ k' * (1 + T) ^ k' * (2 * D k' + Dp k') ≤ M * X := by
    calc ∑ k' ∈ Finset.range k, L ^ k' * (1 + T) ^ k' * (2 * D k' + Dp k')
        ≤ ∑ _k' ∈ Finset.range k, X := Finset.sum_le_sum hterm
      _ = k * X := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ M * X := mul_le_mul_of_nonneg_right (by exact_mod_cast hkM) hX0
  have hTle : T ≤ (1 + CH) * (1 + S) := by linarith
  have hΘ'0 : 0 ≤ Θ' * P ^ q₁ := hΘ0.trans hΘ
  -- collect
  have hPS : ∀ a b : ℕ, a ≤ b → P ^ a * (1 + S) ^ a ≤ P ^ b * (1 + S) ^ b := fun a b hab =>
    mul_le_mul (pow_le_pow_right₀ hP hab) (pow_le_pow_right₀ hS1 hab)
      (pow_nonneg (by linarith) _) (pow_nonneg hP0 _)
  calc Θ * (∑ k' ∈ Finset.range k, L ^ k' * (1 + T) ^ k' * (2 * D k' + Dp k')) * T
      ≤ (Θ' * P ^ q₁) * (M * X) * ((1 + CH) * (1 + S)) :=
        mul_le_mul (mul_le_mul hΘ hsum (Finset.sum_nonneg fun k' _ => by
            have := hD0 k'; have := hDp0 k'; positivity) hΘ'0) hTle hT
          (mul_nonneg hΘ'0 (mul_nonneg (Nat.cast_nonneg _) hX0))
    _ = 3 * Θ' * c * M * L' ^ M * (1 + CH) ^ (M + 1) *
          (P ^ (q₁ + q₂ * M + q₃) * (1 + S) ^ (M + 1)) * d k := by
        rw [hX, mul_pow, mul_pow, ← pow_mul]
        ring
    _ ≤ 3 * Θ' * c * M * L' ^ M * (1 + CH) ^ (M + 1) *
          (P ^ (q₁ + q₂ * M + q₃ + M + 1) * (1 + S) ^ (q₁ + q₂ * M + q₃ + M + 1)) * d k := by
        have hcoef : 0 ≤ 3 * Θ' * c * M * L' ^ M * (1 + CH) ^ (M + 1) := by
          have hΘ' : 0 ≤ Θ' := by
            by_contra hn
            push Not at hn
            have : Θ' * P ^ q₁ < 0 := mul_neg_of_neg_of_pos hn (pow_pos (by linarith) _)
            linarith
          have hL' : 0 ≤ L' := by
            by_contra hn
            push Not at hn
            have : L' * P ^ q₂ < 0 := mul_neg_of_neg_of_pos hn (pow_pos (by linarith) _)
            linarith
          positivity
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hcoef) (hd0 k)
        exact mul_le_mul (pow_le_pow_right₀ hP (by omega)) (pow_le_pow_right₀ hS1 (by omega))
          (pow_nonneg (by linarith) _) (pow_nonneg hP0 _)
    _ = _ := by ring

/-- **The crude constants are polynomial in `P`**: with `C_w = C_s P^{Q_s}` and
`C_a ≤ C_a' P^{Q_a}`, `Θ = B (1 + C_w)(1 + c_R + c_R C_w) ≤ B (1 + C_s)² (1 + c_R) P^{2Q_s}` and
`1 ≤ L = 1 + Θ max(1, C_a) M c₁ ≤ (1 + B (1 + C_s)² (1 + c_R)(1 + C_a') M c₁) P^{2Q_s + Q_a}`. -/
theorem crude_constants_le {B Cs cR Ca Ca' P c₁ : ℝ} {Qs Qa M : ℕ} (hB : 0 ≤ B) (hCs : 0 ≤ Cs)
    (hcR : 0 ≤ cR) (hCa : 0 ≤ Ca) (hCa' : Ca ≤ Ca' * P ^ Qa) (hP : 1 ≤ P) (hc₁ : 0 ≤ c₁) :
    B * (1 + Cs * P ^ Qs) * (1 + cR + cR * (Cs * P ^ Qs)) ≤
        B * (1 + Cs) ^ 2 * (1 + cR) * P ^ (2 * Qs) ∧
      1 ≤ 1 + B * (1 + Cs * P ^ Qs) * (1 + cR + cR * (Cs * P ^ Qs)) * max 1 Ca * M * c₁ ∧
      1 + B * (1 + Cs * P ^ Qs) * (1 + cR + cR * (Cs * P ^ Qs)) * max 1 Ca * M * c₁ ≤
        (1 + B * (1 + Cs) ^ 2 * (1 + cR) * (1 + Ca') * M * c₁) * P ^ (2 * Qs + Qa) := by
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hPs : 1 ≤ P ^ Qs := one_le_pow₀ hP
  have hPa : 1 ≤ P ^ Qa := one_le_pow₀ hP
  have hw : 1 + Cs * P ^ Qs ≤ (1 + Cs) * P ^ Qs := by nlinarith
  have hr : 1 + cR + cR * (Cs * P ^ Qs) ≤ (1 + cR) * (1 + Cs) * P ^ Qs := by
    have h1 : cR * (Cs * P ^ Qs) ≤ cR * Cs * P ^ Qs := le_of_eq (by ring)
    nlinarith [mul_nonneg hcR hCs]
  have hΘ0 : 0 ≤ B * (1 + Cs * P ^ Qs) * (1 + cR + cR * (Cs * P ^ Qs)) := by positivity
  have hΘ : B * (1 + Cs * P ^ Qs) * (1 + cR + cR * (Cs * P ^ Qs)) ≤
      B * (1 + Cs) ^ 2 * (1 + cR) * P ^ (2 * Qs) := by
    calc B * (1 + Cs * P ^ Qs) * (1 + cR + cR * (Cs * P ^ Qs))
        ≤ B * ((1 + Cs) * P ^ Qs) * ((1 + cR) * (1 + Cs) * P ^ Qs) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hw hB) hr (by positivity)
            (mul_nonneg hB (by positivity))
      _ = B * (1 + Cs) ^ 2 * (1 + cR) * P ^ (2 * Qs) := by ring
  have hmax : max 1 Ca ≤ (1 + Ca') * P ^ Qa := by
    have hCa'0 : 0 ≤ Ca' * P ^ Qa := hCa.trans hCa'
    refine max_le (by nlinarith) (hCa'.trans (by nlinarith))
  have hmax0 : 0 ≤ max 1 Ca := le_max_of_le_left zero_le_one
  refine ⟨hΘ, by
    have : 0 ≤ B * (1 + Cs * P ^ Qs) * (1 + cR + cR * (Cs * P ^ Qs)) * max 1 Ca * M * c₁ := by
      positivity
    linarith, ?_⟩
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hX : B * (1 + Cs * P ^ Qs) * (1 + cR + cR * (Cs * P ^ Qs)) * max 1 Ca * M * c₁ ≤
      B * (1 + Cs) ^ 2 * (1 + cR) * (1 + Ca') * M * c₁ * P ^ (2 * Qs + Qa) := by
    calc B * (1 + Cs * P ^ Qs) * (1 + cR + cR * (Cs * P ^ Qs)) * max 1 Ca * M * c₁
        ≤ (B * (1 + Cs) ^ 2 * (1 + cR) * P ^ (2 * Qs)) * ((1 + Ca') * P ^ Qa) * M * c₁ := by
          gcongr
      _ = B * (1 + Cs) ^ 2 * (1 + cR) * (1 + Ca') * M * c₁ * P ^ (2 * Qs + Qa) := by ring
  have hPQ : 1 ≤ P ^ (2 * Qs + Qa) := one_le_pow₀ hP
  have hY : 0 ≤ B * (1 + Cs) ^ 2 * (1 + cR) * (1 + Ca') * M * c₁ := by
    have : 0 ≤ 1 + Ca' := by
      have : 0 ≤ Ca' * P ^ Qa := hCa.trans hCa'
      nlinarith
    positivity
  nlinarith

/-- **The crude error budget, in the form of the crude pass**: `ε_k (b − a)` with `ε_k` as in
`b1w_crude_pass`, `C_w = C_s P^{Q_s}`, `C_a = C_a' P^{Q_a}`, `D = (c_q + C_a) d`, `D_p = C_a d`. -/
theorem crude_eps_budget {B Cs cR Ca' cq P S T CH : ℝ} {Qs Qa M k : ℕ} (d : ℕ → ℝ)
    (hB : 0 ≤ B) (hCs : 0 ≤ Cs) (hcR : 0 ≤ cR) (hCa' : 0 ≤ Ca') (hcq : 0 ≤ cq) (hP : 1 ≤ P)
    (hS : 0 ≤ S) (hT : 0 ≤ T) (hTS : T ≤ CH * S) (hCH : 0 ≤ CH) (hd0 : ∀ k, 0 ≤ d k)
    (hdm : Monotone d) (hkM : k ≤ M) :
    B * (1 + Cs * P ^ Qs) * (1 + cR + cR * (Cs * P ^ Qs)) *
        (∑ k' ∈ Finset.range k,
          (1 + B * (1 + Cs * P ^ Qs) * (1 + cR + cR * (Cs * P ^ Qs)) * max 1 (Ca' * P ^ Qa) *
            M * (2 + 2 / (Real.pi ^ 2 / 8 - Real.pi ^ 2 / 16))) ^ k' * (1 + T) ^ k' *
            (2 * ((cq + Ca' * P ^ Qa) * d k') + Ca' * P ^ Qa * d k')) * T ≤
      3 * (B * (1 + Cs) ^ 2 * (1 + cR)) * (cq + Ca') * M *
        (1 + B * (1 + Cs) ^ 2 * (1 + cR) * (1 + Ca') * M *
          (2 + 2 / (Real.pi ^ 2 / 8 - Real.pi ^ 2 / 16))) ^ M * (1 + CH) ^ (M + 1) *
        P ^ (2 * Qs + (2 * Qs + Qa) * M + Qa + M + 1) *
        (1 + S) ^ (2 * Qs + (2 * Qs + Qa) * M + Qa + M + 1) * d k := by
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hc₁ : 0 ≤ 2 + 2 / (Real.pi ^ 2 / 8 - Real.pi ^ 2 / 16) := by
    have : 0 < Real.pi ^ 2 / 8 - Real.pi ^ 2 / 16 := by
      have : 0 < Real.pi ^ 2 := by positivity
      linarith
    positivity
  have hCa0 : 0 ≤ Ca' * P ^ Qa := mul_nonneg hCa' (pow_nonneg hP0 _)
  obtain ⟨hΘ, hL1, hL⟩ := crude_constants_le (M := M) hB hCs hcR hCa0 le_rfl hP hc₁
    (Qs := Qs) (Ca' := Ca')
  have hΘ0 : 0 ≤ B * (1 + Cs * P ^ Qs) * (1 + cR + cR * (Cs * P ^ Qs)) := by positivity
  have hPa : 1 ≤ P ^ Qa := one_le_pow₀ hP
  refine crude_eps_le (D := fun k => (cq + Ca' * P ^ Qa) * d k) (Dp := fun k => Ca' * P ^ Qa * d k)
    d hP hS hT hTS hCH hΘ0 hΘ hL1 hL (by positivity) hd0 hdm
    (fun k => mul_nonneg (by positivity) (hd0 k)) (fun k => mul_nonneg hCa0 (hd0 k))
    (fun k => mul_le_mul_of_nonneg_right ?_ (hd0 k))
    (fun k => mul_le_mul_of_nonneg_right ?_ (hd0 k)) hkM
  · have : cq ≤ cq * P ^ Qa := le_mul_of_one_le_right hcq hPa
    nlinarith
  · have : 0 ≤ cq * P ^ Qa := mul_nonneg hcq (pow_nonneg hP0 _)
    nlinarith

/-- **The crude stage bound is polynomial**: `L^k (1 + T)^k (2D_k + D_{p,k}) ≤
3c L'^M (1 + C_H)^M P^{q₂M + q₃} (1 + S)^{q₂M + q₃ + M} d_k` for `k ≤ M`. -/
theorem crude_stage_poly {L L' c P S T CH : ℝ} {q₂ q₃ M k : ℕ} (D Dp d : ℕ → ℝ)
    (hP : 1 ≤ P) (hS : 0 ≤ S) (hT : 0 ≤ T) (hTS : T ≤ CH * S) (hCH : 0 ≤ CH) (hL1 : 1 ≤ L)
    (hL : L ≤ L' * P ^ q₂) (hc : 0 ≤ c) (hd0 : 0 ≤ d k) (hD0 : 0 ≤ D k) (hDp0 : 0 ≤ Dp k)
    (hD : D k ≤ c * P ^ q₃ * d k) (hDp : Dp k ≤ c * P ^ q₃ * d k) (hkM : k ≤ M) :
    L ^ k * (1 + T) ^ k * (2 * D k + Dp k) ≤
      3 * c * L' ^ M * (1 + CH) ^ M * P ^ (q₂ * M + q₃) * (1 + S) ^ (q₂ * M + q₃ + M) * d k := by
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hL0 : 0 ≤ L := zero_le_one.trans hL1
  have hL'0 : 0 ≤ L' * P ^ q₂ := hL0.trans hL
  have hS1 : 1 ≤ 1 + S := by linarith
  have hTb : 1 + T ≤ (1 + CH) * (1 + S) := by nlinarith
  have h1 : L ^ k ≤ (L' * P ^ q₂) ^ M :=
    (pow_le_pow_right₀ hL1 hkM).trans (pow_le_pow_left₀ hL0 hL M)
  have h2 : (1 + T) ^ k ≤ ((1 + CH) * (1 + S)) ^ M :=
    (pow_le_pow_right₀ (by linarith) hkM).trans (pow_le_pow_left₀ (by linarith) hTb M)
  have h3 : 2 * D k + Dp k ≤ 3 * (c * P ^ q₃ * d k) := by linarith
  have hX : 0 ≤ c * P ^ q₃ * d k := mul_nonneg (mul_nonneg hc (pow_nonneg hP0 _)) hd0
  calc L ^ k * (1 + T) ^ k * (2 * D k + Dp k)
      ≤ (L' * P ^ q₂) ^ M * ((1 + CH) * (1 + S)) ^ M * (3 * (c * P ^ q₃ * d k)) :=
        mul_le_mul (mul_le_mul h1 h2 (pow_nonneg (by linarith) _) (pow_nonneg hL'0 _)) h3
          (by linarith) (mul_nonneg (pow_nonneg hL'0 _) (pow_nonneg (by positivity) _))
    _ = 3 * c * L' ^ M * (1 + CH) ^ M * P ^ (q₂ * M + q₃) * (1 + S) ^ M * d k := by
        rw [mul_pow, mul_pow, ← pow_mul, pow_add]
        ring
    _ ≤ 3 * c * L' ^ M * (1 + CH) ^ M * P ^ (q₂ * M + q₃) * (1 + S) ^ (q₂ * M + q₃ + M) *
          d k := by
        have hL' : 0 ≤ L' := by
          by_contra hn
          push Not at hn
          have : L' * P ^ q₂ < 0 := mul_neg_of_neg_of_pos hn (pow_pos (by linarith) _)
          linarith
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hS1 (by omega)) (by positivity)) hd0

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! Gaussian amplitude Plancherel: weighted amplitude jets, Gaussian absorption and
Bloch moment Parseval, with constants uniform in the component family and all scales. -/

universe u v

theorem gaussianPlancherel : GaussianPlancherelStatement.{u, v} := by
  intro m n p M cGa hcGa χlo hχ hcχ
  obtain ⟨B, _, hB⟩ := exists_iteratedFDeriv_bound hχ hcχ n
  let D := blochMomentTotal n B + 1
  have hD1 : 1 ≤ D := le_add_of_nonneg_left (blochMomentTotal_nonneg n B)
  have hD : 0 < D := zero_lt_one.trans_le hD1
  have hTD : blochMomentTotal n B ≤ D ^ 2 :=
    (le_add_of_nonneg_right zero_le_one).trans (le_self_pow₀ hD1 (by decide))
  let C := gaussJetConst m M * gaussConst (M + p) cGa * D
  have hC : 0 < C := mul_pos (mul_pos (gaussJetConst_pos m M) (gaussConst_pos _ hcGa)) hD
  refine ⟨C, hC, ?_⟩
  intro ι _ h _ _ _ _ _ _ π _ η ϖ r CGa hη hϖ hϖη hCGa g A Bamp F hF hret hAB hvan hgauss
  let Φ θ := ∑ α ∈ momentIndices n,
    ENNReal.ofReal (ϖ ^ (α.1 + α.2) / ((α.1.factorial * α.2.factorial : ℕ) : ℝ)) *
      blochFibreDerivNorm π (fun θ' => χlo ((Real.sqrt η)⁻¹ • θ')) α F θ
  have hmoment : (∫⁻ θ in freqCube, Φ θ ^ 2) ≤
      (ENNReal.ofReal D * momentNorm π n ϖ F) ^ 2 := by
    have ht := lintegral_compact_bloch_sum_sq_le hχ hB hη hϖ hϖη π F
      (fun x => ⟨(hF x).1.continuous, (hF x).2⟩)
    refine ht.trans ?_
    rw [mul_pow]
    apply mul_le_mul_left
    rw [← ENNReal.ofReal_pow hD.le]
    exact ENNReal.ofReal_le_ofReal hTD
  have hint := ampJetIntegral_le_cube (M := M) π hϖ hcGa hCGa hvan Φ hgauss
  have hamp : ampJetIntegral π m M ϖ A Bamp ≤
      (ENNReal.ofReal (CGa * gaussConst (M + p) cGa) *
        (ENNReal.ofReal D * momentNorm π n ϖ F)) ^ 2 := by
    refine hint.trans ?_
    rw [mul_pow]
    exact mul_le_mul_right hmoment _
  have hroot := ENNReal.rpow_le_rpow hamp (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [sq_rpow_half] at hroot
  have hA (x : ι) : IsBandAmp |r| m (A x) := by
    refine ⟨(hAB x).1, fun θ hθ => ?_⟩
    exact ((hret x).1 θ (by simpa only [sq_abs] using hθ)).1
  have hBamp (x : ι) : IsBandAmp |r| m (Bamp x) := by
    refine ⟨(hAB x).2, fun θ hθ => ?_⟩
    exact ((hret x).1 θ (by simpa only [sq_abs] using hθ)).2
  have hg : g = fun x => ampFun |r| (A x) (Bamp x) := by
    funext x z
    simpa only [ampFun, sq_abs] using (hret x).2.2.2 z
  rw [hg]
  refine (weightedJetNorm_ampFun_le π (abs_nonneg r) hϖ hA hBamp).trans
    ((mul_le_mul_right hroot _).trans (le_of_eq ?_))
  rw [ENNReal.ofReal_mul hCGa]
  rw [ENNReal.ofReal_mul hC.le, ENNReal.ofReal_mul (mul_pos
    (gaussJetConst_pos m M) (gaussConst_pos _ hcGa)).le,
    ENNReal.ofReal_mul (gaussJetConst_pos m M).le]
  ring

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! # The retained amplitude factor: from a smooth compactly supported datum to a plane datum

`RetainedAmplitudeFactorStatement` takes its datum as the plane value of `f`, vanishing a.e.
outside a ball, with the Bloch jets of that plane value. A consumer with a smooth compactly
supported `φ` and `planeValue (f x) = φ x` a.e. supplies both:

* the support radius (`planeDatum_support_of_compact`): one radius for all components, the
  sup-norm radius of `exists_support_radius` doubled;
* the jets: the Bloch fibre derivative norm only sees its data a.e.
  (`blochFibreDerivNorm_congr_ae`, `datumJets_congr_ae`).

Conversely, a plane datum vanishing a.e. outside a ball has a strongly measurable compactly
supported representative, cut off on a ball (`planeDatum_rep`); the frame of the amplitude
identification (`AmplitudeIdentificationStatement`) carries it. -/

/-- **One support radius for a compactly supported datum.** -/
theorem planeDatum_support_of_compact {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] (φ : ∀ x, Vec 2 → h x) (hφ : ∀ x, HasCompactSupport (φ x))
    (g : ∀ x, Vec 2 → h x) (hg : ∀ x, g x =ᵐ[volume] φ x) :
    ∃ R : ℝ, ∀ x, ∀ᵐ z ∂volume, R ^ 2 < z 0 ^ 2 + z 1 ^ 2 → g x z = 0 := by
  choose R hR0 hR using fun x => exists_support_radius (hφ x)
  refine ⟨2 * ∑ x, R x, fun x => ?_⟩
  filter_upwards [hg x] with z hz hzR
  rw [hz]
  refine hR x z ?_
  have hsum : R x ≤ ∑ x, R x :=
    Finset.single_le_sum (fun x _ => hR0 x) (Finset.mem_univ x)
  have hS0 : 0 ≤ ∑ x, R x := Finset.sum_nonneg fun x _ => hR0 x
  by_contra hc
  push Not at hc
  have h0 : |z 0| ≤ ‖z‖ := by
    rw [← Real.norm_eq_abs]
    exact norm_le_pi_norm z 0
  have h1 : |z 1| ≤ ‖z‖ := by
    rw [← Real.norm_eq_abs]
    exact norm_le_pi_norm z 1
  have hz0 : z 0 ^ 2 ≤ (∑ x, R x) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (h0.trans (hc.trans hsum)) 2
  have hz1 : z 1 ^ 2 ≤ (∑ x, R x) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (h1.trans (hc.trans hsum)) 2
  nlinarith

/-- **A compactly supported representative of a datum** vanishing a.e. outside a ball: its
strongly measurable version, cut off on a ball. -/
theorem planeDatum_compact_rep {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    (g : ∀ x, Vec 2 → h x) (hgm : ∀ x, AEStronglyMeasurable (g x) volume)
    (hg : ∃ R : ℝ, ∀ x, ∀ᵐ z ∂volume, R ^ 2 < z 0 ^ 2 + z 1 ^ 2 → g x z = 0) :
    ∃ φ : ∀ x, Vec 2 → h x, (∀ x, StronglyMeasurable (φ x) ∧ HasCompactSupport (φ x)) ∧
      ∀ x, g x =ᵐ[volume] φ x := by
  obtain ⟨R, hR⟩ := hg
  refine ⟨fun x => (Metric.closedBall (0 : Vec 2) |R|).indicator ((hgm x).mk (g x)), fun x =>
    ⟨(hgm x).stronglyMeasurable_mk.indicator Metric.isClosed_closedBall.measurableSet,
      HasCompactSupport.intro (isCompact_closedBall 0 |R|) fun z hz =>
        Set.indicator_of_notMem hz _⟩, fun x => ?_⟩
  filter_upwards [hR x, (hgm x).ae_eq_mk] with z hz hmk
  by_cases hb : z ∈ Metric.closedBall (0 : Vec 2) |R|
  · rw [Set.indicator_of_mem hb, hmk]
  · rw [Set.indicator_of_notMem hb]
    refine hz ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hb
    by_contra hc
    push Not at hc
    have h0 : |z 0| ≤ |R| := sq_le_sq.1 (by linarith [sq_nonneg (z 1)])
    have h1 : |z 1| ≤ |R| := sq_le_sq.1 (by linarith [sq_nonneg (z 0)])
    exact absurd ((pi_norm_le_iff_of_nonneg (abs_nonneg R)).2 (Fin.forall_fin_two.2
      ⟨by rw [Real.norm_eq_abs]; exact h0, by rw [Real.norm_eq_abs]; exact h1⟩)) (not_le.2 hb)

/-- **The compactly supported representative of a plane datum** (`planeDatum_compact_rep` for
`planeValue (f x)`). -/
theorem planeDatum_rep {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {κ : ι → ℕ} (f : ∀ x, PlaneHk Set.univ (κ x) (h x))
    (hf : ∃ R : ℝ, ∀ x, ∀ᵐ z ∂volume, R ^ 2 < z 0 ^ 2 + z 1 ^ 2 → planeValue (f x) z = 0) :
    ∃ φ : ∀ x, Vec 2 → h x, (∀ x, StronglyMeasurable (φ x) ∧ HasCompactSupport (φ x)) ∧
      ∀ x, planeValue (f x) =ᵐ[volume] φ x :=
  planeDatum_compact_rep (fun x => planeValue (f x))
    (fun x => (planeJetOrder_memLp (Nat.zero_le _) (f x) _).aestronglyMeasurable) hf

/-- The datum jets only see their data a.e. -/
theorem datumJets_congr_ae {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] (π : ι → ℝ) (ϖ : ℝ)
    (n : ℕ) {φ φ' : ∀ x, Vec 2 → h x} (hφ : ∀ x, φ x =ᵐ[volume] φ' x) (θ : Vec 2) :
    datumJets π ϖ n φ θ = datumJets π ϖ n φ' θ := by
  unfold datumJets
  exact Finset.sum_congr rfl fun α _ => by rw [blochFibreDerivNorm_congr_ae hφ θ]

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords.Assembly

/-! # Abstract fibre word: the fast inequality

The fast seminorm of stage `k` at `a + t` is a supremum over admissible unit test families `ψ`.
For each one, H4 provides genuine adjoint curves `Ψ_i` on `[a, a + t]` ending at `ψ_i`, with
`Ψ(a)` admissible of size `C_f e^{-c_f t}`, and at each `r` a block splitting of the tested
sources `∑_i src_i(r)(Ψ_i(r))`: slow part `≤ Θ ζ C_f e^{-c_f(a+t-r)} / (|N₀| Γ(r))` against the
slow coordinates, admissible fast part `≤ Θ C_f e^{-c_f(a+t-r)}`, remainder `≤ ε_f / Γ(a+t)`.
The pairing `⟨W_i, Ψ_i⟩` is transported exactly; the gauge grows at most like
`Γ(a+t) ≤ e^{σ(a+t-r)} Γ(r)`.
So `B_k(t) ≤ C_f e^{-(c_f-σ)t} B_k(0) + ε_f t + Θ C_f ∑_{k'<k} ∫_0^t e^{-(c_f-σ)(t-r)}
(ζ a_{k'} + b_{k'})` (`afw_fast`), the fast hypothesis of `triangularGronwall_majorant`. -/

variable {I : Type*} [Fintype I]

/-- The tested sources of one fast family at one time, bounded through the block splitting. -/
theorem fast_source_le {st : I → ℕ} {k : ℕ} {W : I → ComplexCellL2} {q : ComplexCellL2}
    {Adm : ℕ → ComplexCellL2 → Prop} {ν : ℕ → ComplexCellL2 → ℝ}
    (hAdm : ∀ k' (c : ℂ) ψ, Adm k' ψ → Adm k' (cellScalarCLM c ψ))
    (hν : ∀ k' (c : ℂ) ψ, ν k' (cellScalarCLM c ψ) = ‖c‖ * ν k' ψ)
    (hνL : ∀ k' ψ, Adm k' ψ → ‖ψ‖ ≤ ν k' ψ)
    {s₁ s₀ ε : ℝ} (κ : I → ℂ) (φ : I → ComplexCellL2) (src : ℂ)
    (hφ : ∀ k' < k, ∀ i' ∈ stageSet st k', Adm k' (φ i'))
    (hκ : ∀ k' < k, stageNorm st k' κ ≤ s₁)
    (hφn : ∀ k' < k, Real.sqrt (∑ i' ∈ stageSet st k', ν k' (φ i') ^ 2) ≤ s₀)
    (hsplit : ‖src - ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet st k',
      (κ i' * cellComplexPair (W i') q + cellComplexPair (W i') (φ i'))‖ ≤ ε) :
    ‖src‖ ≤ ε + ∑ k' ∈ Finset.range k,
      (s₁ * stageNorm st k' (fun i => cellComplexPair (W i) q) +
        s₀ * fastRaw st k' W (Adm k') (ν k')) := by
  have h1 : ‖src‖ ≤ ‖∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet st k',
      (κ i' * cellComplexPair (W i') q + cellComplexPair (W i') (φ i'))‖ + ε := by
    have h := norm_le_norm_add_norm_sub' src (∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet st k',
      (κ i' * cellComplexPair (W i') q + cellComplexPair (W i') (φ i')))
    linarith
  refine h1.trans ?_
  rw [add_comm ε]
  refine add_le_add ((norm_sum_le _ _).trans (Finset.sum_le_sum fun k' hk' => ?_)) le_rfl
  have hk'k : k' < k := Finset.mem_range.1 hk'
  rw [Finset.sum_add_distrib]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (norm_sum_mul_le_stageNorm st k' κ _).trans
      (mul_le_mul_of_nonneg_right (hκ k' hk'k) (stageNorm_nonneg _ _ _))
  · refine (norm_sum_pair_le_fastRaw st k' W (Adm k') (ν k') (hAdm k') (hν k') (hνL k') φ
      (hφ k' hk'k)).trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (hφn k' hk'k) (fastRaw_nonneg _ _ _ _ _)

/-- The gauge factor against the decay: `Γ(s) e^{-c_f(s-r)} ≤ e^{-(c_f-σ)(s-r)} Γ(r)`. -/
theorem gauge_decay_le {Γs Γr σ cf x : ℝ} (hΓ : Γs ≤ Real.exp (σ * x) * Γr) :
    Γs * Real.exp (-cf * x) ≤ Real.exp (-(cf - σ) * x) * Γr := by
  have he : Real.exp (-(cf - σ) * x) = Real.exp (σ * x) * Real.exp (-cf * x) := by
    rw [← Real.exp_add]
    ring_nf
  rw [he]
  calc Γs * Real.exp (-cf * x) ≤ Real.exp (σ * x) * Γr * Real.exp (-cf * x) :=
        mul_le_mul_of_nonneg_right hΓ (Real.exp_pos _).le
    _ = _ := by ring

/-- **AFW, the fast inequality.** -/
theorem afw_fast {a b : ℝ} (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : IsCellDrift C.v) (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (st : I → ℕ) (M : ℕ)
    (W : I → ℝ → ComplexCellL2) (Ws : I → ℝ → TorusHk 1 ℂ) (S : I → ℝ → ComplexCellL2)
    (F : I → ℝ → Fin 2 → ComplexCellL2)
    (hW : ∀ i, CellWeakHilbertCurve a b (W i) (Ws i) (fun t =>
      cellDualDerivative C hG V hv.1 hb t (Ws i t) (S i t) (F i t)))
    (q : ℝ → ComplexCellL2) (N₀ : ℂ) (hN₀ : N₀ ≠ 0) (Γ : ℝ → ℝ) (hΓ : ∀ r, 0 < Γ r)
    (σ cf : ℝ) (hgauge : ∀ r s, a ≤ r → r ≤ s → s ≤ b → Γ s ≤ Real.exp (σ * (s - r)) * Γ r)
    (Adm : ℕ → ℝ → ComplexCellL2 → Prop) (ν : ℕ → ℝ → ComplexCellL2 → ℝ)
    (hAdm : ∀ k' r (c : ℂ) ψ, Adm k' r ψ → Adm k' r (cellScalarCLM c ψ))
    (hν : ∀ k' r (c : ℂ) ψ, ν k' r (cellScalarCLM c ψ) = ‖c‖ * ν k' r ψ)
    (hνL : ∀ k' r ψ, Adm k' r ψ → ‖ψ‖ ≤ ν k' r ψ)
    {Θ ζ Cf : ℝ} {εf : ℕ → ℝ} (hΘ : 0 ≤ Θ) (hζ : 0 ≤ ζ) (hεf : ∀ k, 0 ≤ εf k) (hCf : 0 ≤ Cf)
    (H4 : ∀ t ∈ Icc 0 (b - a), ∀ k < M, ∀ ψ : I → ComplexCellL2,
      (∀ i ∈ stageSet st k, Adm k (a + t) (ψ i)) →
      Real.sqrt (∑ i ∈ stageSet st k, ν k (a + t) (ψ i) ^ 2) ≤ 1 →
      ∃ (Ψv : I → ℝ → ComplexCellL2) (Ψs : I → ℝ → TorusHk 1 ℂ),
        (∀ i ∈ stageSet st k, CellWeakHilbertCurve a (a + t) (Ψv i) (Ψs i) (fun r =>
          -cellDualDerivative (cellAdjointCoefficients C) hG V (cellDrift_neg hv).1
            (cellDrift_neg_bound hb) r (Ψs i r) 0 0) ∧ Ψv i (a + t) = ψ i) ∧
        (∀ i ∈ stageSet st k, Adm k a (Ψv i a)) ∧
        Real.sqrt (∑ i ∈ stageSet st k, ν k a (Ψv i a) ^ 2) ≤ Cf * Real.exp (-cf * t) ∧
        ∀ r ∈ Icc a (a + t), ∃ κ : I → ℂ, ∃ φ : I → ComplexCellL2,
          (∀ k' < k, ∀ i' ∈ stageSet st k', Adm k' r (φ i')) ∧
          (∀ k' < k, stageNorm st k' κ ≤
            Θ * ζ * Cf * Real.exp (-cf * (a + t - r)) / (‖N₀‖ * Γ r)) ∧
          (∀ k' < k, Real.sqrt (∑ i' ∈ stageSet st k', ν k' r (φ i') ^ 2) ≤
            Θ * Cf * Real.exp (-cf * (a + t - r))) ∧
          ‖∑ i ∈ stageSet st k, cellComplexSource C.θ (S i r) (F i r) (Ψs i r) -
            ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet st k',
              (κ i' * cellComplexPair (W i' r) (q r) + cellComplexPair (W i' r) (φ i'))‖ ≤
            εf k / Γ (a + t)) :
    ∀ k < M, ∀ t ∈ Icc 0 (b - a), ∀ a' b' : ℕ → ℝ → ℝ,
      (∀ k' < k, Continuous (a' k') ∧ Continuous (b' k') ∧
        ∀ r ∈ Icc 0 t, slowStage st k' W q N₀ a r ≤ a' k' r ∧
          fastStage st k' W Adm ν Γ a r ≤ b' k' r) →
      fastStage st k W Adm ν Γ a t ≤
        Cf * Real.exp (-(cf - σ) * t) * fastStage st k W Adm ν Γ a 0 + εf k * t +
          Θ * Cf * ∑ k' ∈ Finset.range k,
            ∫ r in (0 : ℝ)..t, Real.exp (-(cf - σ) * (t - r)) * (ζ * a' k' r + b' k' r) := by
  intro k hk t ht a' b' hmaj
  have hN : 0 < ‖N₀‖ := norm_pos_iff.2 hN₀
  have hat : a ≤ a + t := by linarith [ht.1]
  have hsub : Icc a (a + t) ⊆ Icc a b := Icc_subset_Icc le_rfl (by linarith [ht.2])
  have hΓt := hΓ (a + t)
  -- the gauged majorant of the tested sources
  set g : ℝ → ℝ := fun s => εf k + Θ * Cf * ∑ k' ∈ Finset.range k,
    Real.exp (-(cf - σ) * (t - s)) * (ζ * a' k' s + b' k' s) with hgdef
  have hgc : Continuous g := by
    rw [hgdef]
    refine continuous_const.add (continuous_const.mul (continuous_finsetSum _ fun k' hk' => ?_))
    obtain ⟨hac, hbc, _⟩ := hmaj k' (Finset.mem_range.1 hk')
    exact (by fun_prop : Continuous fun s : ℝ => Real.exp (-(cf - σ) * (t - s))).mul
      ((continuous_const.mul hac).add hbc)
  have hgint : ∫ s in (0 : ℝ)..t, g s = εf k * t + Θ * Cf * ∑ k' ∈ Finset.range k,
      ∫ r in (0 : ℝ)..t, Real.exp (-(cf - σ) * (t - r)) * (ζ * a' k' r + b' k' r) := by
    have hc : ∀ k' ∈ Finset.range k, IntervalIntegrable
        (fun r => Real.exp (-(cf - σ) * (t - r)) * (ζ * a' k' r + b' k' r)) volume 0 t :=
      fun k' hk' => by
        obtain ⟨hac, hbc, _⟩ := hmaj k' (Finset.mem_range.1 hk')
        exact ((by fun_prop : Continuous fun s : ℝ => Real.exp (-(cf - σ) * (t - s))).mul
          ((continuous_const.mul hac).add hbc)).intervalIntegrable _ _
    rw [hgdef, intervalIntegral.integral_add intervalIntegrable_const
      ((IntervalIntegrable.sum (Finset.range k) hc).const_mul (Θ * Cf) |>.congr (by
        intro r _; simp [Finset.sum_apply])),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum hc]
    simp [smul_eq_mul, mul_comm]
  -- the bound for one admissible unit family
  have hfam : ∀ ψ : I → ComplexCellL2, (∀ i ∈ stageSet st k, Adm k (a + t) (ψ i)) →
      Real.sqrt (∑ i ∈ stageSet st k, ν k (a + t) (ψ i) ^ 2) ≤ 1 →
      Γ (a + t) * ‖∑ i ∈ stageSet st k, cellComplexPair (W i (a + t)) (ψ i)‖ ≤
        Cf * Real.exp (-(cf - σ) * t) * fastStage st k W Adm ν Γ a 0 +
          ∫ s in (0 : ℝ)..t, g s := by
    intro ψ hψ hψ1
    obtain ⟨Ψv, Ψs, hΨ, hΨa, hΨan, hsplit⟩ := H4 t ht k hk ψ hψ hψ1
    have hF1 : ∀ i ∈ stageSet st k, cellComplexPair (W i (a + t)) (ψ i) =
        cellComplexPair (W i a) (Ψv i a) +
          ∫ r in a..a + t, cellComplexSource C.θ (S i r) (F i r) (Ψs i r) := by
      intro i hi
      have h := cellWeakAdjointPairing_forced hat C hG V hv hb ((hW i).mono hsub) (hΨ i hi).1
      rw [(hΨ i hi).2] at h
      rw [← h]
      ring
    have hint : ∀ i ∈ stageSet st k, IntervalIntegrable
        (fun r => cellComplexSource C.θ (S i r) (F i r) (Ψs i r)) volume a (a + t) :=
      fun i hi => cellWeakAdjoint_forced_source_intervalIntegrable hat C hG V hv hb
        ((hW i).mono hsub) (hΨ i hi).1
    have hsum : ∑ i ∈ stageSet st k, cellComplexPair (W i (a + t)) (ψ i) =
        ∑ i ∈ stageSet st k, cellComplexPair (W i a) (Ψv i a) +
          ∫ r in a..a + t, ∑ i ∈ stageSet st k,
            cellComplexSource C.θ (S i r) (F i r) (Ψs i r) := by
      rw [intervalIntegral.integral_finsetSum hint, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl hF1
    -- the initial term
    have hinit : Γ (a + t) * ‖∑ i ∈ stageSet st k, cellComplexPair (W i a) (Ψv i a)‖ ≤
        Cf * Real.exp (-(cf - σ) * t) * fastStage st k W Adm ν Γ a 0 := by
      have h1 := norm_sum_pair_le_fastRaw st k (fun i => W i a) (Adm k a) (ν k a) (hAdm k a)
        (hν k a) (hνL k a) (fun i => Ψv i a) hΨa
      have h2 : ‖∑ i ∈ stageSet st k, cellComplexPair (W i a) (Ψv i a)‖ ≤
          fastRaw st k (fun i => W i a) (Adm k a) (ν k a) * (Cf * Real.exp (-cf * t)) :=
        h1.trans (mul_le_mul_of_nonneg_left hΨan (fastRaw_nonneg _ _ _ _ _))
      have hg := gauge_decay_le (cf := cf) (x := t)
        (by have := hgauge a (a + t) le_rfl hat (by linarith [ht.2]); simpa using this)
      have hf0 := fastRaw_nonneg st k (fun i => W i a) (Adm k a) (ν k a)
      have h3 := mul_le_mul_of_nonneg_left h2 hΓt.le
      calc Γ (a + t) * ‖∑ i ∈ stageSet st k, cellComplexPair (W i a) (Ψv i a)‖
          ≤ Γ (a + t) * (fastRaw st k (fun i => W i a) (Adm k a) (ν k a) *
              (Cf * Real.exp (-cf * t))) := h3
        _ = Cf * fastRaw st k (fun i => W i a) (Adm k a) (ν k a) *
              (Γ (a + t) * Real.exp (-cf * t)) := by ring
        _ ≤ Cf * fastRaw st k (fun i => W i a) (Adm k a) (ν k a) *
              (Real.exp (-(cf - σ) * t) * Γ a) :=
            mul_le_mul_of_nonneg_left hg (mul_nonneg hCf hf0)
        _ = Cf * Real.exp (-(cf - σ) * t) * fastStage st k W Adm ν Γ a 0 := by
            simp only [fastStage, add_zero]
            ring
    -- the integral term
    have hpt : ∀ r ∈ Icc a (a + t), Γ (a + t) * ‖∑ i ∈ stageSet st k,
        cellComplexSource C.θ (S i r) (F i r) (Ψs i r)‖ ≤ g (r - a) := by
      intro r hr
      obtain ⟨κ, φ, hφ, hκ, hφn, hsp⟩ := hsplit r hr
      have h := fast_source_le (W := fun i => W i r) (q := q r) (Adm := fun k' => Adm k' r)
        (ν := fun k' => ν k' r) (fun k' => hAdm k' r) (fun k' => hν k' r) (fun k' => hνL k' r)
        κ φ _ hφ hκ hφn hsp
      have hΓr := hΓ r
      have hgr := gauge_decay_le (cf := cf) (x := a + t - r)
        (hgauge r (a + t) hr.1 hr.2 (by linarith [ht.2]))
      have hterm : ∀ k' ∈ Finset.range k,
          Γ (a + t) * (Θ * ζ * Cf * Real.exp (-cf * (a + t - r)) / (‖N₀‖ * Γ r) *
              stageNorm st k' (fun i => cellComplexPair (W i r) (q r)) +
            Θ * Cf * Real.exp (-cf * (a + t - r)) * fastRaw st k' (fun i => W i r) (Adm k' r)
              (ν k' r)) ≤
          Θ * Cf * (Real.exp (-(cf - σ) * (t - (r - a))) *
            (ζ * a' k' (r - a) + b' k' (r - a))) := by
        intro k' hk'
        obtain ⟨_, _, hle⟩ := hmaj k' (Finset.mem_range.1 hk')
        have hra : r - a ∈ Icc 0 t := ⟨by linarith [hr.1], by linarith [hr.2]⟩
        obtain ⟨hA', hB'⟩ := hle (r - a) hra
        have har : a + (r - a) = r := by ring
        rw [slowStage, har] at hA'
        rw [fastStage, har] at hB'
        have h1 : stageNorm st k' (fun i => cellComplexPair (W i r) (q r)) ≤
            ‖N₀‖ * a' k' (r - a) := by
          rwa [div_le_iff₀ hN, mul_comm] at hA'
        have hx : a + t - r = t - (r - a) := by ring
        rw [hx] at hgr ⊢
        have hS0 := stageNorm_nonneg st k' (fun i => cellComplexPair (W i r) (q r))
        have hF0 := fastRaw_nonneg st k' (fun i => W i r) (Adm k' r) (ν k' r)
        have hA0 : 0 ≤ a' k' (r - a) := (div_nonneg hS0 hN.le).trans hA'
        have hB0 : 0 ≤ b' k' (r - a) := (mul_nonneg hΓr.le hF0).trans hB'
        set e := Real.exp (-cf * (t - (r - a))) with he
        have he0 : 0 ≤ e := (Real.exp_pos _).le
        -- rewrite the left side through the gauged quantities
        have hL : Γ (a + t) * (Θ * ζ * Cf * e / (‖N₀‖ * Γ r) *
              stageNorm st k' (fun i => cellComplexPair (W i r) (q r)) +
            Θ * Cf * e * fastRaw st k' (fun i => W i r) (Adm k' r) (ν k' r)) =
            Θ * Cf * ((Γ (a + t) * e) / Γ r) * (ζ * (stageNorm st k'
              (fun i => cellComplexPair (W i r) (q r)) / ‖N₀‖) +
              Γ r * fastRaw st k' (fun i => W i r) (Adm k' r) (ν k' r)) := by
          field_simp
        rw [hL]
        have hratio : (Γ (a + t) * e) / Γ r ≤ Real.exp (-(cf - σ) * (t - (r - a))) := by
          rw [div_le_iff₀ hΓr]
          exact hgr
        have hinner : ζ * (stageNorm st k' (fun i => cellComplexPair (W i r) (q r)) / ‖N₀‖) +
            Γ r * fastRaw st k' (fun i => W i r) (Adm k' r) (ν k' r) ≤
            ζ * a' k' (r - a) + b' k' (r - a) := add_le_add (mul_le_mul_of_nonneg_left hA' hζ) hB'
        have hin0 : 0 ≤ ζ * (stageNorm st k' (fun i => cellComplexPair (W i r) (q r)) / ‖N₀‖) +
            Γ r * fastRaw st k' (fun i => W i r) (Adm k' r) (ν k' r) :=
          add_nonneg (mul_nonneg hζ (div_nonneg hS0 hN.le)) (mul_nonneg hΓr.le hF0)
        have hr0 : 0 ≤ (Γ (a + t) * e) / Γ r := div_nonneg (mul_nonneg hΓt.le he0) hΓr.le
        calc Θ * Cf * ((Γ (a + t) * e) / Γ r) * (ζ * (stageNorm st k'
              (fun i => cellComplexPair (W i r) (q r)) / ‖N₀‖) +
              Γ r * fastRaw st k' (fun i => W i r) (Adm k' r) (ν k' r))
            ≤ Θ * Cf * (Real.exp (-(cf - σ) * (t - (r - a)))) * (ζ * a' k' (r - a) +
                b' k' (r - a)) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hratio (mul_nonneg hΘ hCf)) hinner hin0
                (mul_nonneg (mul_nonneg hΘ hCf) (Real.exp_pos _).le)
          _ = _ := by ring
      calc Γ (a + t) * ‖∑ i ∈ stageSet st k, cellComplexSource C.θ (S i r) (F i r) (Ψs i r)‖
          ≤ Γ (a + t) * (εf k / Γ (a + t) + ∑ k' ∈ Finset.range k,
              (Θ * ζ * Cf * Real.exp (-cf * (a + t - r)) / (‖N₀‖ * Γ r) *
                stageNorm st k' (fun i => cellComplexPair (W i r) (q r)) +
              Θ * Cf * Real.exp (-cf * (a + t - r)) *
                fastRaw st k' (fun i => W i r) (Adm k' r) (ν k' r))) :=
            mul_le_mul_of_nonneg_left h hΓt.le
        _ = εf k + ∑ k' ∈ Finset.range k, Γ (a + t) *
              (Θ * ζ * Cf * Real.exp (-cf * (a + t - r)) / (‖N₀‖ * Γ r) *
                stageNorm st k' (fun i => cellComplexPair (W i r) (q r)) +
              Θ * Cf * Real.exp (-cf * (a + t - r)) *
                fastRaw st k' (fun i => W i r) (Adm k' r) (ν k' r)) := by
            rw [mul_add, Finset.mul_sum, mul_div_cancel₀ _ hΓt.ne']
        _ ≤ εf k + ∑ k' ∈ Finset.range k, Θ * Cf * (Real.exp (-(cf - σ) * (t - (r - a))) *
              (ζ * a' k' (r - a) + b' k' (r - a))) :=
            add_le_add le_rfl (Finset.sum_le_sum hterm)
        _ = g (r - a) := by simp only [hgdef, Finset.mul_sum]
    have hsrcint : IntervalIntegrable (fun r => ∑ i ∈ stageSet st k,
        cellComplexSource C.θ (S i r) (F i r) (Ψs i r)) volume a (a + t) := by
      have := IntervalIntegrable.sum (stageSet st k) hint
      convert this using 1
      funext r
      simp only [Finset.sum_apply]
    have hI : Γ (a + t) * ∫ r in a..a + t, ‖∑ i ∈ stageSet st k,
        cellComplexSource C.θ (S i r) (F i r) (Ψs i r)‖ ≤ ∫ s in (0 : ℝ)..t, g s := by
      rw [← intervalIntegral.integral_const_mul]
      have hmc : Continuous fun r => g (r - a) := hgc.comp (continuous_sub_right a)
      have h := intervalIntegral.integral_mono_on (g := fun r => g (r - a)) hat
        (hsrcint.norm.const_mul (Γ (a + t))) (hmc.intervalIntegrable _ _) hpt
      refine h.trans (le_of_eq ?_)
      rw [intervalIntegral.integral_comp_sub_right (fun r => g r) a]
      simp
    calc Γ (a + t) * ‖∑ i ∈ stageSet st k, cellComplexPair (W i (a + t)) (ψ i)‖
        ≤ Γ (a + t) * (‖∑ i ∈ stageSet st k, cellComplexPair (W i a) (Ψv i a)‖ +
            ∫ r in a..a + t, ‖∑ i ∈ stageSet st k,
              cellComplexSource C.θ (S i r) (F i r) (Ψs i r)‖) := by
          rw [hsum]
          exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add le_rfl
            (intervalIntegral.norm_integral_le_integral_norm hat))) hΓt.le
      _ = Γ (a + t) * ‖∑ i ∈ stageSet st k, cellComplexPair (W i a) (Ψv i a)‖ +
            Γ (a + t) * ∫ r in a..a + t, ‖∑ i ∈ stageSet st k,
              cellComplexSource C.θ (S i r) (F i r) (Ψs i r)‖ := mul_add _ _ _
      _ ≤ _ := add_le_add hinit hI
  -- the supremum
  have hg0 : ∀ s ∈ Icc (0 : ℝ) t, 0 ≤ g s := by
    intro s hs
    rw [hgdef]
    refine add_nonneg (hεf k) (mul_nonneg (mul_nonneg hΘ hCf)
      (Finset.sum_nonneg fun k' hk' => ?_))
    obtain ⟨_, _, hle⟩ := hmaj k' (Finset.mem_range.1 hk')
    obtain ⟨hA', hB'⟩ := hle s hs
    have hA0 : 0 ≤ a' k' s :=
      (div_nonneg (stageNorm_nonneg _ _ _) (norm_nonneg _)).trans hA'
    have hB0 : 0 ≤ b' k' s := (mul_nonneg (hΓ _).le (fastRaw_nonneg _ _ _ _ _)).trans hB'
    exact mul_nonneg (Real.exp_pos _).le (add_nonneg (mul_nonneg hζ hA0) hB0)
  have hRHS0 : 0 ≤ Cf * Real.exp (-(cf - σ) * t) * fastStage st k W Adm ν Γ a 0 +
      ∫ s in (0 : ℝ)..t, g s :=
    add_nonneg (mul_nonneg (mul_nonneg hCf (Real.exp_pos _).le)
      (mul_nonneg (hΓ _).le (fastRaw_nonneg _ _ _ _ _)))
      (intervalIntegral.integral_nonneg ht.1 hg0)
  have hsup : fastRaw st k (fun i => W i (a + t)) (Adm k (a + t)) (ν k (a + t)) ≤
      (Cf * Real.exp (-(cf - σ) * t) * fastStage st k W Adm ν Γ a 0 +
        ∫ s in (0 : ℝ)..t, g s) / Γ (a + t) := by
    refine Real.sSup_le (fun y hy => ?_) (div_nonneg hRHS0 hΓt.le)
    obtain ⟨ψ, hψ, hψ1, rfl⟩ := hy
    rw [le_div_iff₀ hΓt, mul_comm]
    exact hfam ψ hψ hψ1
  have hfin : fastStage st k W Adm ν Γ a t ≤
      Cf * Real.exp (-(cf - σ) * t) * fastStage st k W Adm ν Γ a 0 + ∫ s in (0 : ℝ)..t, g s := by
    have := mul_le_mul_of_nonneg_left hsup hΓt.le
    rw [mul_div_cancel₀ _ hΓt.ne'] at this
    exact this
  rw [hgint] at hfin
  exact hfin.trans_eq (by ring)

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # Abstract fibre word: the stage bound

`afw_slow` and `afw_fast` are the two hypotheses of `triangularGronwall_majorant_mono` for the
gauged slow coordinates and fast seminorms of the abstract fibre word, with the rate
`c = c_f - σ`, the letter constant `Θ' = Θ max(1, C_f)` and monotone stage data: the initial slow
coordinates `≤ D_k`, `C_f` times the initial fast seminorms `≤ D_{p,k}`, and the accumulated
remainders `(ε_s + ε_f)(b - a) ≤ E_k`. So every stage is bounded by
`L^k (1 + ζ²t)^k (D_k + (1+t)^k E_k)` (`afw_bound`). -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
  AVRegularity.Analysis

namespace AVRegularity.CycleWords.Assembly

variable {I : Type*} [Fintype I]

/-- The majorants of the earlier stages are nonnegative on `[0, t]`, so are their integrals. -/
theorem majorant_integral_nonneg {t ζ cf σ : ℝ} (ht : 0 ≤ t) (hζ : 0 ≤ ζ) {a' b' : ℝ → ℝ}
    (ha : ∀ r ∈ Icc 0 t, 0 ≤ a' r) (hb : ∀ r ∈ Icc 0 t, 0 ≤ b' r) :
    0 ≤ ∫ r in (0 : ℝ)..t, (ζ ^ 2 * a' r + ζ * b' r) ∧
      0 ≤ ∫ r in (0 : ℝ)..t, Real.exp (-(cf - σ) * (t - r)) * (ζ * a' r + b' r) :=
  ⟨intervalIntegral.integral_nonneg ht fun r hr =>
      add_nonneg (mul_nonneg (sq_nonneg ζ) (ha r hr)) (mul_nonneg hζ (hb r hr)),
    intervalIntegral.integral_nonneg ht fun r hr =>
      mul_nonneg (Real.exp_pos _).le (add_nonneg (mul_nonneg hζ (ha r hr)) (hb r hr))⟩

/-- **AFW, the stage bound.** -/
theorem afw_bound {a b : ℝ} (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : IsCellDrift C.v) (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (st : I → ℕ) (M : ℕ)
    (W : I → ℝ → ComplexCellL2) (Ws : I → ℝ → TorusHk 1 ℂ) (S : I → ℝ → ComplexCellL2)
    (F : I → ℝ → Fin 2 → ComplexCellL2)
    (hW : ∀ i, CellWeakHilbertCurve a b (W i) (Ws i) (fun t =>
      cellDualDerivative C hG V hv.1 hb t (Ws i t) (S i t) (F i t)))
    (q : ℝ → ComplexCellL2) (qs : ℝ → TorusHk 1 ℂ)
    (hq : CellWeakHilbertCurve a b q qs (fun t =>
      -cellDualDerivative (cellAdjointCoefficients C) hG V (cellDrift_neg hv).1
        (cellDrift_neg_bound hb) t (qs t) 0 0))
    (N₀ : ℂ) (hN₀ : N₀ ≠ 0) (Γ : ℝ → ℝ) (hΓ : ∀ r, 0 < Γ r)
    (σ cf : ℝ) (hσ : σ < cf)
    (hgauge : ∀ r s, a ≤ r → r ≤ s → s ≤ b → Γ s ≤ Real.exp (σ * (s - r)) * Γ r)
    (Adm : ℕ → ℝ → ComplexCellL2 → Prop) (ν : ℕ → ℝ → ComplexCellL2 → ℝ)
    (hAdm : ∀ k' r (c : ℂ) ψ, Adm k' r ψ → Adm k' r (cellScalarCLM c ψ))
    (hν : ∀ k' r (c : ℂ) ψ, ν k' r (cellScalarCLM c ψ) = ‖c‖ * ν k' r ψ)
    (hνL : ∀ k' r ψ, Adm k' r ψ → ‖ψ‖ ≤ ν k' r ψ)
    {Θ ζ Cf : ℝ} {εs εf : ℕ → ℝ} (hΘ : 0 ≤ Θ) (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (hεs : ∀ k, 0 ≤ εs k) (hεf : ∀ k, 0 ≤ εf k) (hCf : 0 ≤ Cf)
    (H3s : ∀ r ∈ Icc a b, ∀ k < M, ∀ β : I → ℂ, ∃ κ : I → ℂ, ∃ φ : I → ComplexCellL2,
      (∀ k' < k, ∀ i' ∈ stageSet st k', Adm k' r (φ i')) ∧
      (∀ k' < k, stageNorm st k' κ ≤ Θ * ζ ^ 2 * stageNorm st k β) ∧
      (∀ k' < k, Real.sqrt (∑ i' ∈ stageSet st k', ν k' r (φ i') ^ 2) ≤
        Θ * ζ * (‖N₀‖ * Γ r) * stageNorm st k β) ∧
      ‖∑ i ∈ stageSet st k, β i * cellComplexSource C.θ (S i r) (F i r) (qs r) -
        ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet st k',
          (κ i' * cellComplexPair (W i' r) (q r) + cellComplexPair (W i' r) (φ i'))‖ ≤
        ‖N₀‖ * εs k * stageNorm st k β)
    (H4 : ∀ t ∈ Icc 0 (b - a), ∀ k < M, ∀ ψ : I → ComplexCellL2,
      (∀ i ∈ stageSet st k, Adm k (a + t) (ψ i)) →
      Real.sqrt (∑ i ∈ stageSet st k, ν k (a + t) (ψ i) ^ 2) ≤ 1 →
      ∃ (Ψv : I → ℝ → ComplexCellL2) (Ψs : I → ℝ → TorusHk 1 ℂ),
        (∀ i ∈ stageSet st k, CellWeakHilbertCurve a (a + t) (Ψv i) (Ψs i) (fun r =>
          -cellDualDerivative (cellAdjointCoefficients C) hG V (cellDrift_neg hv).1
            (cellDrift_neg_bound hb) r (Ψs i r) 0 0) ∧ Ψv i (a + t) = ψ i) ∧
        (∀ i ∈ stageSet st k, Adm k a (Ψv i a)) ∧
        Real.sqrt (∑ i ∈ stageSet st k, ν k a (Ψv i a) ^ 2) ≤ Cf * Real.exp (-cf * t) ∧
        ∀ r ∈ Icc a (a + t), ∃ κ : I → ℂ, ∃ φ : I → ComplexCellL2,
          (∀ k' < k, ∀ i' ∈ stageSet st k', Adm k' r (φ i')) ∧
          (∀ k' < k, stageNorm st k' κ ≤
            Θ * ζ * Cf * Real.exp (-cf * (a + t - r)) / (‖N₀‖ * Γ r)) ∧
          (∀ k' < k, Real.sqrt (∑ i' ∈ stageSet st k', ν k' r (φ i') ^ 2) ≤
            Θ * Cf * Real.exp (-cf * (a + t - r))) ∧
          ‖∑ i ∈ stageSet st k, cellComplexSource C.θ (S i r) (F i r) (Ψs i r) -
            ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet st k',
              (κ i' * cellComplexPair (W i' r) (q r) + cellComplexPair (W i' r) (φ i'))‖ ≤
            εf k / Γ (a + t))
    (D Dp E : ℕ → ℝ) (hDm : Monotone D) (hDpm : Monotone Dp) (hEm : Monotone E)
    (hD : ∀ k, 0 ≤ D k) (hDp : ∀ k, 0 ≤ Dp k) (hζDp : ∀ k, ζ * Dp k ≤ D k) (hE : ∀ k, 0 ≤ E k)
    (hD0 : ∀ k < M, slowStage st k W q N₀ a 0 ≤ D k)
    (hDp0 : ∀ k < M, Cf * fastStage st k W Adm ν Γ a 0 ≤ Dp k)
    (hE0 : ∀ k < M, (εs k + εf k) * (b - a) ≤ E k) :
    ∀ k < M, ∀ t ∈ Icc 0 (b - a),
      slowStage st k W q N₀ a t ≤ (1 + Θ * max 1 Cf * M * (2 + 2 / (cf - σ))) ^ k *
          (1 + ζ ^ 2 * t) ^ k * (D k + (1 + t) ^ k * E k) ∧
      fastStage st k W Adm ν Γ a t ≤ (1 + Θ * max 1 Cf * M * (2 + 2 / (cf - σ))) ^ k *
          (1 + ζ ^ 2 * t) ^ k *
            (ζ * D k + Real.exp (-((cf - σ) / 2) * t) * Dp k + (1 + t) ^ k * E k) := by
  have hc : 0 < cf - σ := sub_pos.2 hσ
  have hΘ' : 0 ≤ Θ * max 1 Cf := mul_nonneg hΘ (le_max_of_le_left zero_le_one)
  have hslow := afw_slow C hG V hv hb st M W Ws S F hW q qs hq N₀ hN₀ Γ (fun r => (hΓ r).le)
    Adm ν hAdm hν hνL hΘ hζ hεs H3s
  have hfast := afw_fast C hG V hv hb st M W Ws S F hW q N₀ hN₀ Γ hΓ σ cf hgauge Adm ν hAdm hν
    hνL hΘ hζ hεf hCf H4
  -- the stage quantities are nonnegative
  have hA0 : ∀ k r, 0 ≤ slowStage st k W q N₀ a r := fun k r =>
    div_nonneg (stageNorm_nonneg _ _ _) (norm_nonneg _)
  have hB0 : ∀ k r, 0 ≤ fastStage st k W Adm ν Γ a r := fun k r =>
    mul_nonneg (hΓ _).le (fastRaw_nonneg _ _ _ _ _)
  refine triangularGronwall_majorant_mono D Dp E hc hζ hζ1 hΘ' hDm hDpm hEm hD hDp hζDp hE
    (slowStage st · W q N₀ a) (fastStage st · W Adm ν Γ a) ?_ ?_
  · intro k hk t ht a' b' hmaj
    have h := hslow k hk t ht a' b' hmaj
    have hsum0 : 0 ≤ ∑ k' ∈ Finset.range k, ∫ r in (0 : ℝ)..t, (ζ ^ 2 * a' k' r + ζ * b' k' r) :=
      Finset.sum_nonneg fun k' hk' => by
        obtain ⟨_, _, hle⟩ := hmaj k' (Finset.mem_range.1 hk')
        exact (majorant_integral_nonneg (cf := cf) (σ := σ) ht.1 hζ
          (fun r hr => (hA0 k' r).trans (hle r hr).1)
          (fun r hr => (hB0 k' r).trans (hle r hr).2)).1
    have hΘle : Θ ≤ Θ * max 1 Cf := le_mul_of_one_le_right hΘ (le_max_left _ _)
    have hεt : εs k * t ≤ E k := by
      have h1 : εs k * t ≤ (εs k + εf k) * (b - a) :=
        mul_le_mul (by linarith [hεf k]) ht.2 ht.1 (by linarith [hεs k, hεf k])
      exact h1.trans (hE0 k hk)
    calc slowStage st k W q N₀ a t
        ≤ slowStage st k W q N₀ a 0 + εs k * t + Θ * ∑ k' ∈ Finset.range k,
            ∫ r in (0 : ℝ)..t, (ζ ^ 2 * a' k' r + ζ * b' k' r) := h
      _ ≤ D k + E k + Θ * max 1 Cf * ∑ k' ∈ Finset.range k,
            ∫ r in (0 : ℝ)..t, (ζ ^ 2 * a' k' r + ζ * b' k' r) :=
          add_le_add (add_le_add (hD0 k hk) hεt) (mul_le_mul_of_nonneg_right hΘle hsum0)
  · intro k hk t ht a' b' hmaj
    have h := hfast k hk t ht a' b' hmaj
    have hsum0 : 0 ≤ ∑ k' ∈ Finset.range k, ∫ r in (0 : ℝ)..t,
        Real.exp (-(cf - σ) * (t - r)) * (ζ * a' k' r + b' k' r) :=
      Finset.sum_nonneg fun k' hk' => by
        obtain ⟨_, _, hle⟩ := hmaj k' (Finset.mem_range.1 hk')
        exact (majorant_integral_nonneg (cf := cf) (σ := σ) ht.1 hζ
          (fun r hr => (hA0 k' r).trans (hle r hr).1)
          (fun r hr => (hB0 k' r).trans (hle r hr).2)).2
    have hΘle : Θ * Cf ≤ Θ * max 1 Cf := mul_le_mul_of_nonneg_left (le_max_right _ _) hΘ
    have hεt : εf k * t ≤ E k := by
      have h1 : εf k * t ≤ (εs k + εf k) * (b - a) :=
        mul_le_mul (by linarith [hεs k]) ht.2 ht.1 (by linarith [hεs k, hεf k])
      exact h1.trans (hE0 k hk)
    have hinit : Cf * Real.exp (-(cf - σ) * t) * fastStage st k W Adm ν Γ a 0 ≤
        Real.exp (-(cf - σ) * t) * Dp k := by
      have := mul_le_mul_of_nonneg_left (hDp0 k hk) (Real.exp_pos (-(cf - σ) * t)).le
      calc Cf * Real.exp (-(cf - σ) * t) * fastStage st k W Adm ν Γ a 0
          = Real.exp (-(cf - σ) * t) * (Cf * fastStage st k W Adm ν Γ a 0) := by ring
        _ ≤ _ := this
    calc fastStage st k W Adm ν Γ a t
        ≤ Cf * Real.exp (-(cf - σ) * t) * fastStage st k W Adm ν Γ a 0 + εf k * t +
            Θ * Cf * ∑ k' ∈ Finset.range k, ∫ r in (0 : ℝ)..t,
              Real.exp (-(cf - σ) * (t - r)) * (ζ * a' k' r + b' k' r) := h
      _ ≤ Real.exp (-(cf - σ) * t) * Dp k + E k + Θ * max 1 Cf * ∑ k' ∈ Finset.range k,
            ∫ r in (0 : ℝ)..t, Real.exp (-(cf - σ) * (t - r)) * (ζ * a' k' r + b' k' r) :=
          add_le_add (add_le_add hinit hεt) (mul_le_mul_of_nonneg_right hΘle hsum0)

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # Abstract fibre word: the crude source bound

The crude pass runs the abstract fibre word with exact splittings (`ε_s = ε_f = 0`) and `ζ = 1`.
Then `afw_bound` bounds the gauged stage quantities by `L^k (1 + t)^k` times the data, and the H3s
splitting at a time `r` (`slow_source_le`) bounds the tested sources of a stage by the earlier
stage quantities at `r`. So every tested source is bounded by `‖N₀‖ ε'_k ‖β‖`, with
`ε'_k = Θ ∑_{k' < k} L^{k'} (1 + (b - a))^{k'} (2 D_{k'} + D_{p,k'})` (`afw_crude_sources`). This is
the error of the poorly buffered instantiation, where the whole source pairing is put into `ε_s`. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
  AVRegularity.Analysis

namespace AVRegularity.CycleWords.Assembly

variable {I : Type*} [Fintype I]

/-- Scaling the weights of a stage by a nonnegative real. -/
theorem stageNorm_smul (st : I → ℕ) (k : ℕ) {c : ℝ} (hc : 0 ≤ c) (β : I → ℂ) :
    stageNorm st k (fun i => (c : ℂ) * β i) = c * stageNorm st k β := by
  unfold stageNorm
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc, mul_pow]
  rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-- A family of zero stage norm vanishes on the stage. -/
theorem eq_zero_of_stageNorm_eq_zero (st : I → ℕ) (k : ℕ) {β : I → ℂ}
    (h : stageNorm st k β = 0) : ∀ i ∈ stageSet st k, β i = 0 := by
  intro i hi
  unfold stageNorm at h
  have hs := (Real.sqrt_eq_zero (Finset.sum_nonneg fun i _ => sq_nonneg ‖β i‖)).1 h
  have hi0 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg ‖β i‖).1 hs i hi
  exact norm_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 hi0)

/-- **AFW, the crude stage bounds**: with exact splittings and `ζ = 1`, every gauged stage
quantity is at most `L^k (1 + (b − a))^k (2D_k + D_{p,k})`. -/
theorem afw_crude_stages {a b : ℝ} (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : IsCellDrift C.v) (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (st : I → ℕ) (M : ℕ)
    (W : I → ℝ → ComplexCellL2) (Ws : I → ℝ → TorusHk 1 ℂ) (S : I → ℝ → ComplexCellL2)
    (F : I → ℝ → Fin 2 → ComplexCellL2)
    (hW : ∀ i, CellWeakHilbertCurve a b (W i) (Ws i) (fun t =>
      cellDualDerivative C hG V hv.1 hb t (Ws i t) (S i t) (F i t)))
    (q : ℝ → ComplexCellL2) (qs : ℝ → TorusHk 1 ℂ)
    (hq : CellWeakHilbertCurve a b q qs (fun t =>
      -cellDualDerivative (cellAdjointCoefficients C) hG V (cellDrift_neg hv).1
        (cellDrift_neg_bound hb) t (qs t) 0 0))
    (N₀ : ℂ) (hN₀ : N₀ ≠ 0) (Γ : ℝ → ℝ) (hΓ : ∀ r, 0 < Γ r)
    (σ cf : ℝ) (hσ : σ < cf)
    (hgauge : ∀ r s, a ≤ r → r ≤ s → s ≤ b → Γ s ≤ Real.exp (σ * (s - r)) * Γ r)
    (Adm : ℕ → ℝ → ComplexCellL2 → Prop) (ν : ℕ → ℝ → ComplexCellL2 → ℝ)
    (hAdm : ∀ k' r (c : ℂ) ψ, Adm k' r ψ → Adm k' r (cellScalarCLM c ψ))
    (hν : ∀ k' r (c : ℂ) ψ, ν k' r (cellScalarCLM c ψ) = ‖c‖ * ν k' r ψ)
    (hνL : ∀ k' r ψ, Adm k' r ψ → ‖ψ‖ ≤ ν k' r ψ)
    {Θ Cf : ℝ} (hΘ : 0 ≤ Θ) (hCf : 0 ≤ Cf)
    (H3s : ∀ r ∈ Icc a b, ∀ k < M, ∀ β : I → ℂ, ∃ κ : I → ℂ, ∃ φ : I → ComplexCellL2,
      (∀ k' < k, ∀ i' ∈ stageSet st k', Adm k' r (φ i')) ∧
      (∀ k' < k, stageNorm st k' κ ≤ Θ * 1 ^ 2 * stageNorm st k β) ∧
      (∀ k' < k, Real.sqrt (∑ i' ∈ stageSet st k', ν k' r (φ i') ^ 2) ≤
        Θ * 1 * (‖N₀‖ * Γ r) * stageNorm st k β) ∧
      ‖∑ i ∈ stageSet st k, β i * cellComplexSource C.θ (S i r) (F i r) (qs r) -
        ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet st k',
          (κ i' * cellComplexPair (W i' r) (q r) + cellComplexPair (W i' r) (φ i'))‖ ≤
        ‖N₀‖ * 0 * stageNorm st k β)
    (H4 : ∀ t ∈ Icc 0 (b - a), ∀ k < M, ∀ ψ : I → ComplexCellL2,
      (∀ i ∈ stageSet st k, Adm k (a + t) (ψ i)) →
      Real.sqrt (∑ i ∈ stageSet st k, ν k (a + t) (ψ i) ^ 2) ≤ 1 →
      ∃ (Ψv : I → ℝ → ComplexCellL2) (Ψs : I → ℝ → TorusHk 1 ℂ),
        (∀ i ∈ stageSet st k, CellWeakHilbertCurve a (a + t) (Ψv i) (Ψs i) (fun r =>
          -cellDualDerivative (cellAdjointCoefficients C) hG V (cellDrift_neg hv).1
            (cellDrift_neg_bound hb) r (Ψs i r) 0 0) ∧ Ψv i (a + t) = ψ i) ∧
        (∀ i ∈ stageSet st k, Adm k a (Ψv i a)) ∧
        Real.sqrt (∑ i ∈ stageSet st k, ν k a (Ψv i a) ^ 2) ≤ Cf * Real.exp (-cf * t) ∧
        ∀ r ∈ Icc a (a + t), ∃ κ : I → ℂ, ∃ φ : I → ComplexCellL2,
          (∀ k' < k, ∀ i' ∈ stageSet st k', Adm k' r (φ i')) ∧
          (∀ k' < k, stageNorm st k' κ ≤
            Θ * 1 * Cf * Real.exp (-cf * (a + t - r)) / (‖N₀‖ * Γ r)) ∧
          (∀ k' < k, Real.sqrt (∑ i' ∈ stageSet st k', ν k' r (φ i') ^ 2) ≤
            Θ * Cf * Real.exp (-cf * (a + t - r))) ∧
          ‖∑ i ∈ stageSet st k, cellComplexSource C.θ (S i r) (F i r) (Ψs i r) -
            ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet st k',
              (κ i' * cellComplexPair (W i' r) (q r) + cellComplexPair (W i' r) (φ i'))‖ ≤
            0 / Γ (a + t))
    (D Dp : ℕ → ℝ) (hDm : Monotone D) (hDpm : Monotone Dp)
    (hD : ∀ k, 0 ≤ D k) (hDp : ∀ k, 0 ≤ Dp k) (hDDp : ∀ k, Dp k ≤ D k)
    (hD0 : ∀ k < M, slowStage st k W q N₀ a 0 ≤ D k)
    (hDp0 : ∀ k < M, Cf * fastStage st k W Adm ν Γ a 0 ≤ Dp k) :
    ∀ k < M, ∀ t ∈ Icc 0 (b - a),
      slowStage st k W q N₀ a t ≤ (1 + Θ * max 1 Cf * M * (2 + 2 / (cf - σ))) ^ k *
          (1 + (b - a)) ^ k * (2 * D k + Dp k) ∧
      fastStage st k W Adm ν Γ a t ≤ (1 + Θ * max 1 Cf * M * (2 + 2 / (cf - σ))) ^ k *
          (1 + (b - a)) ^ k * (2 * D k + Dp k) := by
  have hc : 0 < cf - σ := sub_pos.2 hσ
  have hL1 : 1 ≤ 1 + Θ * max 1 Cf * M * (2 + 2 / (cf - σ)) := by
    have : 0 ≤ Θ * max 1 Cf * M * (2 + 2 / (cf - σ)) := by
      have h1 : 0 ≤ max 1 Cf := le_max_of_le_left zero_le_one
      have h2 : 0 ≤ 2 + 2 / (cf - σ) := by positivity
      positivity
    linarith
  have hstage := afw_bound (ζ := 1) (εs := fun _ => 0) (εf := fun _ => 0) C hG V hv hb st M W
    Ws S F hW q qs hq N₀ hN₀ Γ hΓ σ cf hσ hgauge Adm ν hAdm hν hνL hΘ zero_le_one le_rfl
    (fun _ => le_rfl) (fun _ => le_rfl) hCf H3s H4 D Dp (fun _ => 0) hDm hDpm
    (fun _ _ _ => le_rfl) hD hDp (fun k => by rw [one_mul]; exact hDDp k) (fun _ => le_rfl)
    hD0 hDp0 (fun k _ => by simp)
  intro k hk t ht
  obtain ⟨hs, hf⟩ := hstage k hk t ht
  have h1 : 1 + 1 ^ 2 * t = 1 + t := by ring
  have hpow : (1 + 1 ^ 2 * t) ^ k ≤ (1 + (b - a)) ^ k := by
    rw [h1]
    exact pow_le_pow_left₀ (by linarith [ht.1]) (by linarith [ht.2]) k
  have hLk : 0 ≤ (1 + Θ * max 1 Cf * M * (2 + 2 / (cf - σ))) ^ k := pow_nonneg (by linarith) _
  have hba : 0 ≤ (1 + (b - a)) ^ k := pow_nonneg (by linarith [ht.1, ht.2]) _
  have he : Real.exp (-((cf - σ) / 2) * t) ≤ 1 :=
    Real.exp_le_one_iff.2
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (div_pos hc two_pos).le) ht.1)
  refine ⟨hs.trans ?_, hf.trans ?_⟩
  · simp only [mul_zero, add_zero]
    refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hLk) (hD k)).trans ?_
    exact mul_le_mul_of_nonneg_left (by linarith [hD k, hDp k]) (mul_nonneg hLk hba)
  · simp only [mul_zero, add_zero, one_mul]
    have hD' : D k + Real.exp (-((cf - σ) / 2) * t) * Dp k ≤ 2 * D k + Dp k := by
      have := mul_le_of_le_one_left (hDp k) he
      linarith [hD k]
    refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hLk)
      (add_nonneg (hD k) (mul_nonneg (Real.exp_pos _).le (hDp k)))).trans ?_
    exact mul_le_mul_of_nonneg_left hD' (mul_nonneg hLk hba)

/-- **AFW, the crude source bound.** -/
theorem afw_crude_sources {a b : ℝ} (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : IsCellDrift C.v) (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (st : I → ℕ) (M : ℕ)
    (W : I → ℝ → ComplexCellL2) (Ws : I → ℝ → TorusHk 1 ℂ) (S : I → ℝ → ComplexCellL2)
    (F : I → ℝ → Fin 2 → ComplexCellL2)
    (hW : ∀ i, CellWeakHilbertCurve a b (W i) (Ws i) (fun t =>
      cellDualDerivative C hG V hv.1 hb t (Ws i t) (S i t) (F i t)))
    (q : ℝ → ComplexCellL2) (qs : ℝ → TorusHk 1 ℂ)
    (hq : CellWeakHilbertCurve a b q qs (fun t =>
      -cellDualDerivative (cellAdjointCoefficients C) hG V (cellDrift_neg hv).1
        (cellDrift_neg_bound hb) t (qs t) 0 0))
    (N₀ : ℂ) (hN₀ : N₀ ≠ 0) (Γ : ℝ → ℝ) (hΓ : ∀ r, 0 < Γ r)
    (σ cf : ℝ) (hσ : σ < cf)
    (hgauge : ∀ r s, a ≤ r → r ≤ s → s ≤ b → Γ s ≤ Real.exp (σ * (s - r)) * Γ r)
    (Adm : ℕ → ℝ → ComplexCellL2 → Prop) (ν : ℕ → ℝ → ComplexCellL2 → ℝ)
    (hAdm : ∀ k' r (c : ℂ) ψ, Adm k' r ψ → Adm k' r (cellScalarCLM c ψ))
    (hν : ∀ k' r (c : ℂ) ψ, ν k' r (cellScalarCLM c ψ) = ‖c‖ * ν k' r ψ)
    (hνL : ∀ k' r ψ, Adm k' r ψ → ‖ψ‖ ≤ ν k' r ψ)
    {Θ Cf : ℝ} (hΘ : 0 ≤ Θ) (hCf : 0 ≤ Cf)
    (H3s : ∀ r ∈ Icc a b, ∀ k < M, ∀ β : I → ℂ, ∃ κ : I → ℂ, ∃ φ : I → ComplexCellL2,
      (∀ k' < k, ∀ i' ∈ stageSet st k', Adm k' r (φ i')) ∧
      (∀ k' < k, stageNorm st k' κ ≤ Θ * 1 ^ 2 * stageNorm st k β) ∧
      (∀ k' < k, Real.sqrt (∑ i' ∈ stageSet st k', ν k' r (φ i') ^ 2) ≤
        Θ * 1 * (‖N₀‖ * Γ r) * stageNorm st k β) ∧
      ‖∑ i ∈ stageSet st k, β i * cellComplexSource C.θ (S i r) (F i r) (qs r) -
        ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet st k',
          (κ i' * cellComplexPair (W i' r) (q r) + cellComplexPair (W i' r) (φ i'))‖ ≤
        ‖N₀‖ * 0 * stageNorm st k β)
    (H4 : ∀ t ∈ Icc 0 (b - a), ∀ k < M, ∀ ψ : I → ComplexCellL2,
      (∀ i ∈ stageSet st k, Adm k (a + t) (ψ i)) →
      Real.sqrt (∑ i ∈ stageSet st k, ν k (a + t) (ψ i) ^ 2) ≤ 1 →
      ∃ (Ψv : I → ℝ → ComplexCellL2) (Ψs : I → ℝ → TorusHk 1 ℂ),
        (∀ i ∈ stageSet st k, CellWeakHilbertCurve a (a + t) (Ψv i) (Ψs i) (fun r =>
          -cellDualDerivative (cellAdjointCoefficients C) hG V (cellDrift_neg hv).1
            (cellDrift_neg_bound hb) r (Ψs i r) 0 0) ∧ Ψv i (a + t) = ψ i) ∧
        (∀ i ∈ stageSet st k, Adm k a (Ψv i a)) ∧
        Real.sqrt (∑ i ∈ stageSet st k, ν k a (Ψv i a) ^ 2) ≤ Cf * Real.exp (-cf * t) ∧
        ∀ r ∈ Icc a (a + t), ∃ κ : I → ℂ, ∃ φ : I → ComplexCellL2,
          (∀ k' < k, ∀ i' ∈ stageSet st k', Adm k' r (φ i')) ∧
          (∀ k' < k, stageNorm st k' κ ≤
            Θ * 1 * Cf * Real.exp (-cf * (a + t - r)) / (‖N₀‖ * Γ r)) ∧
          (∀ k' < k, Real.sqrt (∑ i' ∈ stageSet st k', ν k' r (φ i') ^ 2) ≤
            Θ * Cf * Real.exp (-cf * (a + t - r))) ∧
          ‖∑ i ∈ stageSet st k, cellComplexSource C.θ (S i r) (F i r) (Ψs i r) -
            ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet st k',
              (κ i' * cellComplexPair (W i' r) (q r) + cellComplexPair (W i' r) (φ i'))‖ ≤
            0 / Γ (a + t))
    (D Dp : ℕ → ℝ) (hDm : Monotone D) (hDpm : Monotone Dp)
    (hD : ∀ k, 0 ≤ D k) (hDp : ∀ k, 0 ≤ Dp k) (hDDp : ∀ k, Dp k ≤ D k)
    (hD0 : ∀ k < M, slowStage st k W q N₀ a 0 ≤ D k)
    (hDp0 : ∀ k < M, Cf * fastStage st k W Adm ν Γ a 0 ≤ Dp k) :
    ∀ r ∈ Icc a b, ∀ k < M, ∀ β : I → ℂ,
      ‖∑ i ∈ stageSet st k, β i * cellComplexSource C.θ (S i r) (F i r) (qs r)‖ ≤
        ‖N₀‖ * (Θ * ∑ k' ∈ Finset.range k,
          (1 + Θ * max 1 Cf * M * (2 + 2 / (cf - σ))) ^ k' * (1 + (b - a)) ^ k' *
            (2 * D k' + Dp k')) * stageNorm st k β := by
  set L := 1 + Θ * max 1 Cf * M * (2 + 2 / (cf - σ)) with hL
  have hc : 0 < cf - σ := sub_pos.2 hσ
  have hL1 : 1 ≤ L := by
    have : 0 ≤ Θ * max 1 Cf * M * (2 + 2 / (cf - σ)) := by
      have h1 : 0 ≤ max 1 Cf := le_max_of_le_left zero_le_one
      have h2 : 0 ≤ 2 + 2 / (cf - σ) := by positivity
      positivity
    linarith
  -- the stage bounds of the crude pass
  have hstage := afw_bound (ζ := 1) (εs := fun _ => 0) (εf := fun _ => 0) C hG V hv hb st M W
    Ws S F hW q qs hq N₀ hN₀ Γ hΓ σ cf hσ hgauge Adm ν hAdm hν hνL hΘ zero_le_one le_rfl
    (fun _ => le_rfl) (fun _ => le_rfl) hCf H3s H4 D Dp (fun _ => 0) hDm hDpm
    (fun _ _ _ => le_rfl) hD hDp (fun k => by rw [one_mul]; exact hDDp k) (fun _ => le_rfl)
    hD0 hDp0 (fun k _ => by simp)
  intro r hr k hk β
  have hN : 0 < ‖N₀‖ := norm_pos_iff.2 hN₀
  have ht : r - a ∈ Icc 0 (b - a) := ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have har : a + (r - a) = r := by ring
  -- each earlier stage at `r`
  have hterm : ∀ k' < k, Θ * 1 ^ 2 * stageNorm st k' (fun i => cellComplexPair (W i r) (q r)) +
      Θ * 1 * (‖N₀‖ * Γ r) * fastRaw st k' (fun i => W i r) (Adm k' r) (ν k' r) ≤
        ‖N₀‖ * (Θ * (L ^ k' * (1 + (b - a)) ^ k' * (2 * D k' + Dp k'))) := by
    intro k' hk'
    have hk'M : k' < M := hk'.trans hk
    obtain ⟨hs, hf⟩ := hstage k' hk'M (r - a) ht
    have h1 : 1 + 1 ^ 2 * (r - a) = 1 + (r - a) := by ring
    have hpow : (1 + 1 ^ 2 * (r - a)) ^ k' ≤ (1 + (b - a)) ^ k' := by
      rw [h1]
      exact pow_le_pow_left₀ (by linarith [ht.1]) (by linarith [ht.2]) k'
    have hLk : 0 ≤ L ^ k' := pow_nonneg (by linarith) _
    have hba : 0 ≤ (1 + (b - a)) ^ k' := pow_nonneg (by linarith [ht.1, ht.2]) _
    have hslow : slowStage st k' W q N₀ a (r - a) ≤ L ^ k' * (1 + (b - a)) ^ k' * D k' := by
      refine hs.trans ?_
      simp only [mul_zero, add_zero]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hLk) (hD k')
    have hfast : fastStage st k' W Adm ν Γ a (r - a) ≤
        L ^ k' * (1 + (b - a)) ^ k' * (D k' + Dp k') := by
      refine hf.trans ?_
      simp only [mul_zero, add_zero, one_mul]
      have he : Real.exp (-((cf - σ) / 2) * (r - a)) ≤ 1 :=
        Real.exp_le_one_iff.2
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (div_pos hc two_pos).le) ht.1)
      have hD' : D k' + Real.exp (-((cf - σ) / 2) * (r - a)) * Dp k' ≤ D k' + Dp k' :=
        add_le_add le_rfl (mul_le_of_le_one_left (hDp k') he)
      calc L ^ k' * (1 + 1 ^ 2 * (r - a)) ^ k' *
            (D k' + Real.exp (-((cf - σ) / 2) * (r - a)) * Dp k')
          ≤ L ^ k' * (1 + (b - a)) ^ k' *
            (D k' + Real.exp (-((cf - σ) / 2) * (r - a)) * Dp k') :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hLk)
              (add_nonneg (hD k') (mul_nonneg (Real.exp_pos _).le (hDp k')))
        _ ≤ L ^ k' * (1 + (b - a)) ^ k' * (D k' + Dp k') :=
            mul_le_mul_of_nonneg_left hD' (mul_nonneg hLk hba)
    have hsl : stageNorm st k' (fun i => cellComplexPair (W i r) (q r)) =
        ‖N₀‖ * slowStage st k' W q N₀ a (r - a) := by
      unfold slowStage
      rw [har, mul_div_cancel₀ _ hN.ne']
    have hfa : Γ r * fastRaw st k' (fun i => W i r) (Adm k' r) (ν k' r) =
        fastStage st k' W Adm ν Γ a (r - a) := by
      unfold fastStage
      rw [har]
    calc Θ * 1 ^ 2 * stageNorm st k' (fun i => cellComplexPair (W i r) (q r)) +
          Θ * 1 * (‖N₀‖ * Γ r) * fastRaw st k' (fun i => W i r) (Adm k' r) (ν k' r)
        = ‖N₀‖ * (Θ * (slowStage st k' W q N₀ a (r - a) +
            fastStage st k' W Adm ν Γ a (r - a))) := by
          rw [hsl, ← hfa]
          ring
      _ ≤ ‖N₀‖ * (Θ * (L ^ k' * (1 + (b - a)) ^ k' * D k' +
            L ^ k' * (1 + (b - a)) ^ k' * (D k' + Dp k'))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add hslow hfast) hΘ)
            hN.le
      _ = ‖N₀‖ * (Θ * (L ^ k' * (1 + (b - a)) ^ k' * (2 * D k' + Dp k'))) := by ring
  set sβ := stageNorm st k β with hsβ
  have hsβ0 : 0 ≤ sβ := stageNorm_nonneg _ _ _
  rcases hsβ0.eq_or_lt with h0 | hpos
  · -- a zero family
    have hz := eq_zero_of_stageNorm_eq_zero st k h0.symm
    rw [Finset.sum_eq_zero fun i hi => by rw [hz i hi, zero_mul], norm_zero, ← h0, mul_zero]
  -- normalize the weights
  set β' : I → ℂ := fun i => ((sβ⁻¹ : ℝ) : ℂ) * β i with hβ'
  have hβ'1 : stageNorm st k β' = 1 := by
    rw [hβ', stageNorm_smul st k (inv_nonneg.2 hsβ0) β, ← hsβ, inv_mul_cancel₀ hpos.ne']
  have hsum : ∑ i ∈ stageSet st k, β i * cellComplexSource C.θ (S i r) (F i r) (qs r) =
      (sβ : ℂ) * ∑ i ∈ stageSet st k, β' i * cellComplexSource C.θ (S i r) (F i r) (qs r) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hβ', ← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hpos.ne',
      Complex.ofReal_one, one_mul]
  obtain ⟨κ, φ, h1, h2, h3, h4⟩ := H3s r hr k hk β'
  have hsrc := slow_source_le (Adm := fun k' => Adm k' r) (ν := fun k' => ν k' r) (hAdm · r)
    (hν · r) (hνL · r) hΘ
    zero_le_one (hΓ r).le β' κ φ hβ'1.le _ h1 h2 h3 h4 le_rfl
  rw [hsum, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, mul_comm]
  refine mul_le_mul_of_nonneg_right (hsrc.trans ?_) hsβ0
  rw [mul_zero, zero_add, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun k' hk' => hterm k' (Finset.mem_range.1 hk')

end AVRegularity.CycleWords.Assembly
end
end
