-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Homogenization.Ambient.Basic

section
@[expose] public section
namespace AVRegularity.WeakEntryProofs

/-! Uniform response-depth bounds for the positive geometric mass series. -/

section
open scoped BigOperators

theorem one_add_geometric_Icc_mul (x : ℝ) (R : ℕ) :
    (1 + ∑ n ∈ Finset.Icc 1 R, x ^ n) * (1 - x) = 1 - x ^ (R + 1) := by
  induction R with
  | zero => simp
  | succ R ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ R + 1)]
      calc
        _ = (1 + ∑ n ∈ Finset.Icc 1 R, x ^ n) * (1 - x) +
            x ^ (R + 1) * (1 - x) := by ring
        _ = 1 - x ^ (R + 1 + 1) := by rw [ih, pow_succ]; ring

 theorem one_add_geometric_Icc_le (x : ℝ) (hx : 0 ≤ x) (hx1 : x < 1) (R : ℕ) :
    1 + ∑ n ∈ Finset.Icc 1 R, x ^ n ≤ 1 / (1 - x) := by
  apply (le_div_iff₀ (sub_pos.mpr hx1)).mpr
  rw [one_add_geometric_Icc_mul]
  exact sub_le_self 1 (pow_nonneg hx _)
end

/-! The finite-window flux energy estimate absorbs arbitrary finite transport through Gronwall. -/

theorem finiteWindowFluxEnergy_arithmetic (d T S F B U W A C : ℝ)
    (hd : (3 / 4) * W ^ 2 ≤ d) (hT : |T| ≤ B * W * U)
    (hS : |S| ≤ A * U) (hF : |F| ≤ C * W) :
    2 * (-d - T + S - F) + W ^ 2 / 2 ≤
      (1 + 4 * B ^ 2) * U ^ 2 + A ^ 2 + 4 * C ^ 2 := by
  have ht := (neg_le_abs T).trans hT
  have hs := (le_abs_self S).trans hS
  have hf := (neg_le_abs F).trans hF
  have yt := sq_nonneg (W / 2 - 2 * B * U)
  have ys := sq_nonneg (A - U)
  have yf := sq_nonneg (W / 2 - 2 * C)
  nlinarith [sq_nonneg W]

theorem finiteWindowFluxEnergy_normSq_arithmetic (E H Q R d T S F B U W A C : ℝ)
    (hd : (3 / 4) * H ≤ d) (hT : |T| ≤ B * W * U)
    (hS : |S| ≤ A * U) (hF : |F| ≤ C * W)
    (hU : U ^ 2 = E) (hW : W ^ 2 = H) (hA : A ^ 2 = Q) (hC : C ^ 2 = R) :
    2 * (-d - T + S - F) + H / 2 ≤ (1 + 4 * B ^ 2) * E + Q + 4 * R := by
  have hh := finiteWindowFluxEnergy_arithmetic d T S F B U W A C
    (by simpa only [hW] using hd) hT hS hF
  simpa only [hU, hW, hA, hC] using hh

/-! Order consequences of the time-window bound and consecutive quiet margins. -/

 theorem quietTimes_antitone (tq : ℕ → ℝ) (lo hi : ℕ)
    (hstep : ∀ k, lo ≤ k → k < hi → tq (k + 1) ≤ tq k)
    (i j : ℕ) (hli : lo ≤ i) (hij : i ≤ j) (hjh : j ≤ hi) : tq j ≤ tq i := by
  have main : ∀ n : ℕ, i + n ≤ hi → tq (i + n) ≤ tq i := by
    intro n
    induction n with
    | zero => intro _; exact le_refl _
    | succ n ih =>
        intro hn
        exact (hstep (i + n) (by omega) (by omega)).trans (ih (by omega))
  have h := main (j - i) (by omega)
  simpa only [Nat.add_sub_of_le hij] using h

 theorem quietTimes_mem_window (tq : ℕ → ℝ) (lo hi : ℕ) (a T : ℝ)
    (hstep : ∀ k, lo ≤ k → k < hi → tq (k + 1) ≤ tq k)
    (hstart : a ≤ tq hi) (hend : tq lo ≤ T)
    (i : ℕ) (hli : lo ≤ i) (hih : i ≤ hi) : tq i ∈ Set.Icc a T := by
  exact ⟨hstart.trans (quietTimes_antitone tq lo hi hstep i hi hli hih le_rfl),
    (quietTimes_antitone tq lo hi hstep lo i le_rfl hli hih).trans hend⟩

/-! The symmetric transition used by the actual weak cutoff is an exact partition pair. -/

theorem smoothTransition_add_complement (x : ℝ) :
    Real.smoothTransition x + Real.smoothTransition (1 - x) = 1 := by
  have hd := (Real.smoothTransition.pos_denom x).ne'
  unfold Real.smoothTransition
  rw [show 1 - (1 - x) = x by ring, add_comm (expNegInvGlue (1 - x))]
  rw [← add_div, div_self hd]

theorem smoothTransition_pair (a b : ℝ) (hab : a + b = 1) :
    Real.smoothTransition a + Real.smoothTransition b = 1 := by
  have hb : b = 1 - a := by linarith only [hab]
  rw [hb]
  exact smoothTransition_add_complement a

end AVRegularity.WeakEntryProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.WeakEntryProofs

/-! Zero extension of a time-window field is a linear map. -/

open Homogenization
open scoped Classical

def windowFieldExtension (a b : ℝ) :
    ({t : ℝ // t ∈ Set.Icc a b} → Vec 2 → ℝ) →ₗ[ℝ] (ℝ → Vec 2 → ℝ) where
  toFun := fun f t => if ht : t ∈ Set.Icc a b then f ⟨t, ht⟩ else 0
  map_add' := by
    intro f g
    funext t z
    by_cases ht : t ∈ Set.Icc a b
    · simp only [dite_eq_left ht, Pi.add_apply]
    · simp only [dite_eq_right ht, Pi.add_apply, Pi.zero_apply, zero_add]
  map_smul' := by
    intro k f
    funext t z
    by_cases ht : t ∈ Set.Icc a b
    · simp only [dite_eq_left ht, Pi.smul_apply, RingHom.id_apply]
    · simp only [dite_eq_right ht, Pi.smul_apply, Pi.zero_apply, smul_zero, RingHom.id_apply]

@[simp] theorem windowFieldExtension_apply_mem (a b : ℝ)
    (f : {t : ℝ // t ∈ Set.Icc a b} → Vec 2 → ℝ) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    windowFieldExtension a b f t = f ⟨t, ht⟩ := dite_eq_left ht

@[simp] theorem windowFieldExtension_apply_not_mem (a b : ℝ)
    (f : {t : ℝ // t ∈ Set.Icc a b} → Vec 2 → ℝ) (t : ℝ) (ht : t ∉ Set.Icc a b) :
    windowFieldExtension a b f t = 0 := dite_eq_right ht

end AVRegularity.WeakEntryProofs
end
end
