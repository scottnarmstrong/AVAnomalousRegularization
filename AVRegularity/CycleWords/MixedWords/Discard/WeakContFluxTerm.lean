-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.MixedWords.Discard.Multiset
public import AVRegularity.CycleJoint.CompactWeakCorrectionIntegrability
import AVRegularity.CycleJoint.UnitPatchValuePeriodization
import AVRegularity.CycleJoint.PlaneCoupledFluxScaling
public import AVRegularity.CycleWords.FamilyMolecularMixedReserve
public import AVRegularity.Weighted.PlaneH1CoefficientOperator
import Mathlib.Algebra.Order.Star.Real

section
/-! # the triangular Duhamel bound for the vector of stage modes

The coupling `T(r)` has `ℓ²` operator norm at most `B Y` (independent of the number of
components) and is strictly triangular for `st`. Then the vector of modes satisfies
`‖c i t‖ ≤ L^{M+1} ((1+τ) Y)^M e^{-ρτ/2} (∑ ‖c i' t₁‖²)^{1/2}`, `L = 1 + (M+1) B`. -/

@[expose] public section

open MeasureTheory Set

namespace AVRegularity.CycleWords.Discard

/-- The level-`k` claim of `quietTriVec_total`. -/
theorem quietTriVec_level {I : Type*} [Fintype I] (st : I → ℕ) {Mst : ℕ}
    (hst : ∀ i, st i ≤ Mst) {ρ B Y : ℝ} (hB : 0 ≤ B) (hY : 1 ≤ Y) {t₁ t₂ : ℝ}
    (lam : ℝ → ℂ) (c : I → ℝ → ℂ) (T : I → I → ℝ → ℂ)
    (hop : ∀ r (w : I → ℂ), ∑ i, ‖∑ i', T i i' r * w i'‖ ^ 2 ≤ (B * Y) ^ 2 * ∑ i', ‖w i'‖ ^ 2)
    (hT0 : ∀ i i' r, ¬ st i' < st i → T i i' r = 0)
    (hM : ∀ s t, t₁ ≤ s → s ≤ t → t ≤ t₂ →
      ‖Complex.exp (∫ r in s..t, lam r)‖ ≤ Real.exp (-(ρ / 2) * (t - s)))
    (hint : ∀ t ∈ Icc t₁ t₂, ∀ i, IntervalIntegrable (fun r =>
      Complex.exp (∫ s in r..t, lam s) * ∑ i', T i i' r * c i' r) volume t₁ t)
    (hD : ∀ i, ∀ t ∈ Icc t₁ t₂, c i t = Complex.exp (∫ r in t₁..t, lam r) * c i t₁ +
      ∫ r in t₁..t, Complex.exp (∫ s in r..t, lam s) * ∑ i', T i i' r * c i' r)
    (k : ℕ) :
    ∀ t ∈ Icc t₁ t₂, Real.sqrt (∑ i ∈ Finset.univ.filter (fun i => st i = k), ‖c i t‖ ^ 2) ≤
      (1 + (Mst + 1) * B) ^ (k + 1) * ((1 + (t - t₁)) * Y) ^ k *
        Real.exp (-(ρ / 2) * (t - t₁)) * Real.sqrt (∑ i', ‖c i' t₁‖ ^ 2) := by
  classical
  set L : ℝ := 1 + (Mst + 1) * B with hL
  have hL1 : 1 ≤ L := by rw [hL]; nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ Mst + 1) hB]
  set a : ℝ := Real.sqrt (∑ i', ‖c i' t₁‖ ^ 2) with ha
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro t ht
  have hτ : 0 ≤ t - t₁ := by linarith [ht.1]
  set W : ℝ := (1 + (t - t₁)) * Y with hW
  have hW1 : 1 ≤ W := by rw [hW]; nlinarith
  set E : ℝ := Real.exp (-(ρ / 2) * (t - t₁)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  by_cases hkM : Mst < k
  · have : Finset.univ.filter (fun i => st i = k) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 fun i _ => ?_
      have := hst i; omega
    rw [this, Finset.sum_empty, Real.sqrt_zero]
    positivity
  replace hkM := not_lt.1 hkM
  set lev : Finset I := Finset.univ.filter (fun i => st i = k) with hlev
  -- the decomposition
  have hdec : ∀ i ∈ lev, c i t = Complex.exp (∫ r in t₁..t, lam r) * c i t₁ +
      ∫ r in t₁..t, Complex.exp (∫ s in r..t, lam s) * ∑ i', T i i' r * c i' r :=
    fun i _ => hD i t ht
  have hmink := sqrt_sum_norm_add_le' lev (fun i => Complex.exp (∫ r in t₁..t, lam r) * c i t₁)
    (fun i => ∫ r in t₁..t, Complex.exp (∫ s in r..t, lam s) * ∑ i', T i i' r * c i' r)
  have hx : Real.sqrt (∑ i ∈ lev, ‖Complex.exp (∫ r in t₁..t, lam r) * c i t₁‖ ^ 2) ≤ E * a := by
    simp_rw [norm_mul, mul_pow]
    rw [← Finset.mul_sum, Real.sqrt_mul (by positivity)]
    rw [Real.sqrt_sq (norm_nonneg _)]
    refine mul_le_mul (hM t₁ t le_rfl ht.1 ht.2) (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _) hE0.le
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _
  -- the lower levels
  have hlow : ∀ r ∈ Icc t₁ t, ∑ i' ∈ Finset.univ.filter (fun i' => st i' < k), ‖c i' r‖ ^ 2 ≤
      k * (L ^ k * W ^ (k - 1) * Real.exp (-(ρ / 2) * (r - t₁)) * a) ^ 2 := by
    intro r hr
    have hr' : r ∈ Icc t₁ t₂ := ⟨hr.1, hr.2.trans ht.2⟩
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun i' => st i' < k))
      (t := Finset.range k) (g := st) (fun i hi => Finset.mem_range.2 (Finset.mem_filter.1 hi).2)]
    calc _ ≤ ∑ k' ∈ Finset.range k, (L ^ k * W ^ (k - 1) * Real.exp (-(ρ / 2) * (r - t₁)) * a) ^ 2 := by
          refine Finset.sum_le_sum fun k' hk' => ?_
          have hk'k := Finset.mem_range.1 hk'
          have hprev := ih k' hk'k r hr'
          have hsub : (Finset.univ.filter (fun i' => st i' < k)).filter (fun i => st i = k') =
              Finset.univ.filter (fun i => st i = k') := by
            ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · exact fun h => h.2
            · exact fun h => ⟨h ▸ hk'k, h⟩
          rw [hsub]
          have hWr : (1 + (r - t₁)) * Y ≤ W := by
            rw [hW]; exact mul_le_mul_of_nonneg_right (by linarith [hr.2]) (by linarith)
          have hWr1 : 1 ≤ (1 + (r - t₁)) * Y := by nlinarith [hr.1]
          have : L ^ (k' + 1) * ((1 + (r - t₁)) * Y) ^ k' * Real.exp (-(ρ / 2) * (r - t₁)) * a ≤
              L ^ k * W ^ (k - 1) * Real.exp (-(ρ / 2) * (r - t₁)) * a := by
            have e1 : L ^ (k' + 1) ≤ L ^ k := pow_le_pow_right₀ hL1 (by omega)
            have e2 : ((1 + (r - t₁)) * Y) ^ k' ≤ W ^ (k - 1) :=
              (pow_le_pow_left₀ (by linarith) hWr _).trans (pow_le_pow_right₀ hW1 (by omega))
            have e3 : 0 ≤ Real.exp (-(ρ / 2) * (r - t₁)) := (Real.exp_pos _).le
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
              (mul_le_mul e1 e2 (by positivity) (by positivity)) e3) ha0
          calc _ = (Real.sqrt (∑ i ∈ Finset.univ.filter (fun i => st i = k'), ‖c i r‖ ^ 2)) ^ 2 :=
                (Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)).symm
            _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hprev.trans this) 2
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  set G : ℝ := E * (B * Y) * Real.sqrt k * L ^ k * W ^ (k - 1) * a with hG
  have hG0 : 0 ≤ G := by positivity
  have hpt : ∀ r ∈ Ioc t₁ t, ∑ i ∈ lev, ‖Complex.exp (∫ s in r..t, lam s) *
      ∑ i', T i i' r * c i' r‖ ^ 2 ≤ G ^ 2 := by
    intro r hr
    have hrI : r ∈ Icc t₁ t := ⟨hr.1.le, hr.2⟩
    have hexp := hM r t hr.1.le hr.2 ht.2
    set w : I → ℂ := fun i' => if st i' < k then c i' r else 0 with hw
    have hu : ∀ i ∈ lev, ∑ i', T i i' r * c i' r = ∑ i', T i i' r * w i' := by
      intro i hi
      have hik : st i = k := (Finset.mem_filter.1 hi).2
      refine Finset.sum_congr rfl fun i' _ => ?_
      by_cases h : st i' < k
      · simp [hw, h]
      · rw [hT0 i i' r (by omega)]; simp
    have hsw : ∑ i', ‖w i'‖ ^ 2 = ∑ i' ∈ Finset.univ.filter (fun i' => st i' < k), ‖c i' r‖ ^ 2 := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun i' _ => ?_
      by_cases h : st i' < k <;> simp [hw, h]
    have hlev_u : ∑ i ∈ lev, ‖∑ i', T i i' r * c i' r‖ ^ 2 ≤
        (B * Y) ^ 2 * ∑ i' ∈ Finset.univ.filter (fun i' => st i' < k), ‖c i' r‖ ^ 2 := by
      calc ∑ i ∈ lev, ‖∑ i', T i i' r * c i' r‖ ^ 2
          = ∑ i ∈ lev, ‖∑ i', T i i' r * w i'‖ ^ 2 :=
            Finset.sum_congr rfl fun i hi => by rw [hu i hi]
        _ ≤ ∑ i, ‖∑ i', T i i' r * w i'‖ ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _
        _ ≤ (B * Y) ^ 2 * ∑ i', ‖w i'‖ ^ 2 := hop r w
        _ = _ := by rw [hsw]
    have hlow' := hlow r hrI
    have hEr : Real.exp (-(ρ / 2) * (t - r)) * Real.exp (-(ρ / 2) * (r - t₁)) = E := by
      rw [← Real.exp_add, hE]; congr 1; ring
    calc ∑ i ∈ lev, ‖Complex.exp (∫ s in r..t, lam s) * ∑ i', T i i' r * c i' r‖ ^ 2
        = ‖Complex.exp (∫ s in r..t, lam s)‖ ^ 2 *
            ∑ i ∈ lev, ‖∑ i', T i i' r * c i' r‖ ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [norm_mul, mul_pow]
      _ ≤ (Real.exp (-(ρ / 2) * (t - r))) ^ 2 * ((B * Y) ^ 2 *
            (k * (L ^ k * W ^ (k - 1) * Real.exp (-(ρ / 2) * (r - t₁)) * a) ^ 2)) := by
          refine mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hexp 2) ?_
            (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
          exact hlev_u.trans (mul_le_mul_of_nonneg_left hlow' (by positivity))
      _ = G ^ 2 := by
          have hs : Real.sqrt (k : ℝ) ^ 2 = k := Real.sq_sqrt (Nat.cast_nonneg _)
          have key : ∀ e b s l w er a' : ℝ, s ^ 2 = k →
              e ^ 2 * (b ^ 2 * (k * (l * w * er * a') ^ 2)) = (e * er * b * s * l * w * a') ^ 2 := by
            intro e b s l w er a' h
            rw [← h]; ring
          rw [hG, ← hEr]
          have := key (Real.exp (-(ρ / 2) * (t - r))) (B * Y) (Real.sqrt k) (L ^ k) (W ^ (k - 1))
            (Real.exp (-(ρ / 2) * (r - t₁))) a hs
          rw [this]
  have hJ := norm_sq_integral_le lev (fun i r => Complex.exp (∫ s in r..t, lam s) *
      ∑ i', T i i' r * c i' r) ht.1 (fun i _ => hint t ht i) hG0 hpt
  have hJ' : Real.sqrt (∑ i ∈ lev, ‖∫ r in t₁..t, Complex.exp (∫ s in r..t, lam s) *
      ∑ i', T i i' r * c i' r‖ ^ 2) ≤ (t - t₁) * G := by
    rw [Real.sqrt_le_left (by positivity)]
    exact hJ
  have hfin : Real.sqrt (∑ i ∈ lev, ‖c i t‖ ^ 2) ≤ E * a + (t - t₁) * G := by
    calc Real.sqrt (∑ i ∈ lev, ‖c i t‖ ^ 2)
        = Real.sqrt (∑ i ∈ lev, ‖Complex.exp (∫ r in t₁..t, lam r) * c i t₁ +
            ∫ r in t₁..t, Complex.exp (∫ s in r..t, lam s) * ∑ i', T i i' r * c i' r‖ ^ 2) := by
          congr 1
          exact Finset.sum_congr rfl fun i hi => by rw [hdec i hi]
      _ ≤ _ := hmink.trans (add_le_add hx hJ')
  have hGle : (t - t₁) * G ≤ E * a * (B * Real.sqrt k * L ^ k * W ^ k) := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk1
    · subst hk0; simp [hG]
    · have hτY : (t - t₁) * Y ≤ W := by rw [hW]; nlinarith
      have hWk : (t - t₁) * Y * W ^ (k - 1) ≤ W ^ k := by
        calc (t - t₁) * Y * W ^ (k - 1) ≤ W * W ^ (k - 1) :=
              mul_le_mul_of_nonneg_right hτY (by positivity)
          _ = W ^ k := by rw [← pow_succ']; congr 1; omega
      calc (t - t₁) * G = E * a * (B * Real.sqrt k * L ^ k) * ((t - t₁) * Y * W ^ (k - 1)) := by
            rw [hG]; ring
        _ ≤ E * a * (B * Real.sqrt k * L ^ k) * W ^ k :=
            mul_le_mul_of_nonneg_left hWk (by positivity)
        _ = _ := by ring
  have hsk : Real.sqrt (k : ℝ) ≤ Mst + 1 := by
    rw [Real.sqrt_le_left (by positivity)]
    have : (k : ℝ) ≤ Mst := by exact_mod_cast hkM
    nlinarith
  have hLk : 1 ≤ L ^ k := one_le_pow₀ hL1
  have hWk1 : 1 ≤ W ^ k := one_le_pow₀ hW1
  have hBL : 1 + B * Real.sqrt k ≤ L := by
    rw [hL]; nlinarith [mul_le_mul_of_nonneg_left hsk hB]
  calc Real.sqrt (∑ i ∈ lev, ‖c i t‖ ^ 2) ≤ E * a + E * a * (B * Real.sqrt k * L ^ k * W ^ k) :=
        hfin.trans (add_le_add_right hGle _) |>.trans_eq' rfl
    _ ≤ E * a * (W ^ k * (L ^ k * (1 + B * Real.sqrt k))) := by
        have h0 : 0 ≤ E * a := by positivity
        have h1 : 1 + B * Real.sqrt k * L ^ k * W ^ k ≤ W ^ k * (L ^ k * (1 + B * Real.sqrt k)) := by
          have hBs : 0 ≤ B * Real.sqrt k := by positivity
          nlinarith [mul_nonneg hBs (mul_nonneg (sub_nonneg.2 hLk) (sub_nonneg.2 hWk1)),
            mul_nonneg hBs (sub_nonneg.2 hLk), mul_nonneg hBs (sub_nonneg.2 hWk1),
            mul_nonneg (sub_nonneg.2 hLk) (sub_nonneg.2 hWk1)]
        nlinarith [mul_le_mul_of_nonneg_left h1 h0]
    _ ≤ E * a * (W ^ k * (L ^ k * L)) := by gcongr
    _ = _ := by rw [pow_succ]; ring

/-- **The total square bound.** -/
theorem quietTriVec_total {I : Type*} [Fintype I] (st : I → ℕ) {Mst : ℕ}
    (hst : ∀ i, st i ≤ Mst) {ρ B Y : ℝ} (hB : 0 ≤ B) (hY : 1 ≤ Y) {t₁ t₂ : ℝ}
    (lam : ℝ → ℂ) (c : I → ℝ → ℂ) (T : I → I → ℝ → ℂ)
    (hop : ∀ r (w : I → ℂ), ∑ i, ‖∑ i', T i i' r * w i'‖ ^ 2 ≤ (B * Y) ^ 2 * ∑ i', ‖w i'‖ ^ 2)
    (hT0 : ∀ i i' r, ¬ st i' < st i → T i i' r = 0)
    (hM : ∀ s t, t₁ ≤ s → s ≤ t → t ≤ t₂ →
      ‖Complex.exp (∫ r in s..t, lam r)‖ ≤ Real.exp (-(ρ / 2) * (t - s)))
    (hint : ∀ t ∈ Icc t₁ t₂, ∀ i, IntervalIntegrable (fun r =>
      Complex.exp (∫ s in r..t, lam s) * ∑ i', T i i' r * c i' r) volume t₁ t)
    (hD : ∀ i, ∀ t ∈ Icc t₁ t₂, c i t = Complex.exp (∫ r in t₁..t, lam r) * c i t₁ +
      ∫ r in t₁..t, Complex.exp (∫ s in r..t, lam s) * ∑ i', T i i' r * c i' r)
    (t : ℝ) (ht : t ∈ Icc t₁ t₂) :
    ∑ i, ‖c i t‖ ^ 2 ≤ (Mst + 1) * ((1 + (Mst + 1) * B) ^ (Mst + 1) *
      ((1 + (t - t₁)) * Y) ^ Mst * Real.exp (-(ρ / 2) * (t - t₁))) ^ 2 * ∑ i', ‖c i' t₁‖ ^ 2 := by
  classical
  have hL1 : 1 ≤ 1 + (Mst + 1) * B := by nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ Mst + 1) hB]
  have hτ : 0 ≤ t - t₁ := by linarith [ht.1]
  have hW1 : 1 ≤ (1 + (t - t₁)) * Y := by nlinarith
  have hsplit : ∑ i, ‖c i t‖ ^ 2 = ∑ k ∈ Finset.range (Mst + 1),
      ∑ i ∈ Finset.univ.filter (fun i => st i = k), ‖c i t‖ ^ 2 :=
    (Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.range (Mst + 1)) (g := st)
      (fun i _ => Finset.mem_range.2 (Nat.lt_succ_of_le (hst i))) (fun i => ‖c i t‖ ^ 2)).symm
  have hE0 := Real.exp_pos (-(ρ / 2) * (t - t₁))
  set a2 : ℝ := ∑ i', ‖c i' t₁‖ ^ 2 with ha2
  have ha20 : 0 ≤ a2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [hsplit]
  calc ∑ k ∈ Finset.range (Mst + 1), ∑ i ∈ Finset.univ.filter (fun i => st i = k), ‖c i t‖ ^ 2
      ≤ ∑ _k ∈ Finset.range (Mst + 1), ((1 + (Mst + 1) * B) ^ (Mst + 1) *
          ((1 + (t - t₁)) * Y) ^ Mst * Real.exp (-(ρ / 2) * (t - t₁))) ^ 2 * a2 := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hkM := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
        have h1 := quietTriVec_level st hst hB hY lam c T hop hT0 hM hint hD k t ht
        have e1 : (1 + (Mst + 1) * B) ^ (k + 1) ≤ (1 + (Mst + 1) * B) ^ (Mst + 1) :=
          pow_le_pow_right₀ hL1 (by omega)
        have e2 : ((1 + (t - t₁)) * Y) ^ k ≤ ((1 + (t - t₁)) * Y) ^ Mst :=
          pow_le_pow_right₀ hW1 hkM
        have h2 : Real.sqrt (∑ i ∈ Finset.univ.filter (fun i => st i = k), ‖c i t‖ ^ 2) ≤
            (1 + (Mst + 1) * B) ^ (Mst + 1) * ((1 + (t - t₁)) * Y) ^ Mst *
              Real.exp (-(ρ / 2) * (t - t₁)) * Real.sqrt a2 := by
          refine h1.trans ?_
          gcongr
        have h3 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
        rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _), mul_pow,
          Real.sq_sqrt ha20] at h3
        exact h3
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

end AVRegularity.CycleWords.Discard
end
end

section
/-! # the scalar absorption for one Fourier mode

`quietMode_scalar_bound`: from the triangular Duhamel bound of one mode, the terminal value at the
end of a stretch of length `D_q ≥ 1`, times `(1 + |y|²)^{K_f}`, is at most a constant times
`(1 + D_q)^{2M} e^{-(y₀/2) D_q}` times the weighted squared norms of the initial values, when
`|y|² ≥ y₀ > 0`. -/

@[expose] public noncomputable section

open MeasureTheory Set

namespace AVRegularity.CycleWords.Discard

/-- The constant of the absorption of `(1 + y)^P` by `e^{-y/2}`. -/
def quietAbsorbConst (P : ℕ) : ℝ := (P.factorial : ℝ) * 4 ^ P * Real.exp 1

theorem quietAbsorbConst_pos (P : ℕ) : 0 < quietAbsorbConst P := by
  unfold quietAbsorbConst; positivity

theorem quiet_poly_exp (P : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    (1 + y) ^ P * Real.exp (-(y / 2)) ≤ quietAbsorbConst P := by
  have hp := Real.pow_div_factorial_le_exp ((1 + y) / 4) (by positivity) P
  have hfac : (0 : ℝ) < P.factorial := by positivity
  have h1 : (1 + y) ^ P ≤ (P.factorial : ℝ) * 4 ^ P * Real.exp ((1 + y) / 4) := by
    rw [div_pow, div_div, div_le_iff₀ (by positivity)] at hp
    nlinarith [hp]
  calc (1 + y) ^ P * Real.exp (-(y / 2))
      ≤ ((P.factorial : ℝ) * 4 ^ P * Real.exp ((1 + y) / 4)) * Real.exp (-(y / 2)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = (P.factorial : ℝ) * 4 ^ P * Real.exp (1 / 4 - y / 4) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ (P.factorial : ℝ) * 4 ^ P * Real.exp 1 := by
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (by positivity)
    _ = _ := rfl

theorem quietMode_scalar_bound {I : Type*} [Fintype I] (st : I → ℕ) {Mst : ℕ}
    (hst : ∀ i, st i ≤ Mst) {B : ℝ} (hB : 0 ≤ B) (p S Kf : ℕ) {y0 yq Dq : ℝ} (hy0 : 0 ≤ y0)
    (hyq : y0 ≤ yq) (hDq : 1 ≤ Dq) {t₁ : ℝ} (lam : ℝ → ℂ) (c : I → ℝ → ℂ)
    (T : I → I → ℝ → ℂ)
    (hop : ∀ r (w : I → ℂ), ∑ i, ‖∑ i', T i i' r * w i'‖ ^ 2 ≤
      (B * (1 + yq) ^ p) ^ 2 * ∑ i', ‖w i'‖ ^ 2)
    (hT0 : ∀ i i' r, ¬ st i' < st i → T i i' r = 0)
    (hM : ∀ s t, t₁ ≤ s → s ≤ t → t ≤ t₁ + Dq →
      ‖Complex.exp (∫ r in s..t, lam r)‖ ≤ Real.exp (-(yq / 2) * (t - s)))
    (hint : ∀ t ∈ Icc t₁ (t₁ + Dq), ∀ i, IntervalIntegrable (fun r =>
      Complex.exp (∫ s in r..t, lam s) * ∑ i', T i i' r * c i' r) volume t₁ t)
    (hD : ∀ i, ∀ t ∈ Icc t₁ (t₁ + Dq), c i t = Complex.exp (∫ r in t₁..t, lam r) * c i t₁ +
      ∫ r in t₁..t, Complex.exp (∫ s in r..t, lam s) * ∑ i', T i i' r * c i' r)   :
    (1 + yq) ^ Kf * ∑ i, ‖c i (t₁ + Dq)‖ ^ 2 ≤
      ((Mst + 1) * (1 + (Mst + 1) * B) ^ (2 * (Mst + 1)) *
        quietAbsorbConst (Kf + 2 * p * Mst + S)) * (1 + Dq) ^ (2 * Mst) *
        Real.exp (-(y0 / 2) * Dq) * ∑ i', ((1 + yq) ^ S)⁻¹ * ‖c i' t₁‖ ^ 2 := by
  set L : ℝ := 1 + (Mst + 1) * B with hL
  set u : ℝ := 1 + yq with hu
  have hyq0 : 0 ≤ yq := hy0.trans hyq
  have hu1 : 1 ≤ u := by rw [hu]; linarith
  have hL1 : 1 ≤ L := by rw [hL]; nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ Mst + 1) hB]
  have hY1 : 1 ≤ u ^ p := one_le_pow₀ hu1
  have hDq0 : 0 ≤ Dq := by linarith
  have htri := quietTriVec_total st hst (ρ := yq) (B := B) (Y := u ^ p) hB hY1 (t₁ := t₁)
    (t₂ := t₁ + Dq) lam c T hop hT0 hM hint hD (t₁ + Dq) ⟨by linarith, le_rfl⟩
  rw [add_sub_cancel_left] at htri
  set E : ℝ := Real.exp (-(yq / 2) * Dq) with hE
  set W : ℝ := (1 + Dq) * u ^ p with hW
  have hE0 : 0 < E := Real.exp_pos _
  have h2 : ∑ i, ‖c i (t₁ + Dq)‖ ^ 2 ≤
      (Mst + 1) * (L ^ (Mst + 1) * W ^ Mst * E) ^ 2 * ∑ i', ‖c i' t₁‖ ^ 2 := htri
  have hsum : ∑ i', ‖c i' t₁‖ ^ 2 = u ^ S * ∑ i', (u ^ S)⁻¹ * ‖c i' t₁‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i' _ => ?_
    have : u ^ S ≠ 0 := by positivity
    field_simp
  set sw : ℝ := ∑ i', (u ^ S)⁻¹ * ‖c i' t₁‖ ^ 2 with hswdef
  have hsw0 : 0 ≤ sw := Finset.sum_nonneg fun _ _ => by positivity
  have hE2 : E ^ 2 = Real.exp (-yq * Dq) := by
    rw [hE, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hexp : u ^ (Kf + 2 * p * Mst + S) * Real.exp (-yq * Dq) ≤
      quietAbsorbConst (Kf + 2 * p * Mst + S) * Real.exp (-(y0 / 2) * Dq) := by
    have h3 : Real.exp (-yq * Dq) ≤ Real.exp (-(yq / 2)) * Real.exp (-(y0 / 2) * Dq) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      nlinarith [mul_le_mul_of_nonneg_right hyq (by linarith : (0 : ℝ) ≤ Dq),
        mul_nonneg hyq0 (by linarith : (0 : ℝ) ≤ Dq - 1)]
    calc u ^ (Kf + 2 * p * Mst + S) * Real.exp (-yq * Dq)
        ≤ u ^ (Kf + 2 * p * Mst + S) * (Real.exp (-(yq / 2)) * Real.exp (-(y0 / 2) * Dq)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (u ^ (Kf + 2 * p * Mst + S) * Real.exp (-(yq / 2))) * Real.exp (-(y0 / 2) * Dq) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by
          have := quiet_poly_exp (Kf + 2 * p * Mst + S) hyq0
          simpa [hu] using this) (Real.exp_pos _).le
  have hWpow : W ^ Mst = (1 + Dq) ^ Mst * (u ^ p) ^ Mst := by rw [hW, mul_pow]
  calc u ^ Kf * ∑ i, ‖c i (t₁ + Dq)‖ ^ 2
      ≤ u ^ Kf * ((Mst + 1) * (L ^ (Mst + 1) * W ^ Mst * E) ^ 2 * (u ^ S * sw)) := by
        rw [← hsum]; exact mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (Mst + 1) * L ^ (2 * (Mst + 1)) * (1 + Dq) ^ (2 * Mst) *
          (u ^ (Kf + 2 * p * Mst + S) * Real.exp (-yq * Dq)) * sw := by
        rw [mul_pow, mul_pow, hWpow, hE2, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul]
        have : u ^ (Kf + 2 * p * Mst + S) = u ^ Kf * (u ^ (p * Mst)) ^ 2 * u ^ S := by
          rw [← pow_mul, ← pow_add, ← pow_add]; congr 1; ring
        rw [this]
        ring_nf
    _ ≤ (Mst + 1) * L ^ (2 * (Mst + 1)) * (1 + Dq) ^ (2 * Mst) *
          (quietAbsorbConst (Kf + 2 * p * Mst + S) * Real.exp (-(y0 / 2) * Dq)) * sw := by
        gcongr
    _ = _ := by ring

end AVRegularity.CycleWords.Discard
end
end

section
/-! # a derivative on the frequency side is a moment on the physical side

* `lineDerivOp_of_hasLineDerivAt`: an `L²` function with a classical line derivative that is
  in `L²` has that derivative as its tempered-distribution derivative (Mathlib's integration by
  parts for line derivatives against a Schwartz test).
* `fourierInv_ae_of_lineDerivOp`: if the distributional line derivative of `𝓕 f` is the `L²`
  function `H`, then `𝓕⁻ H = -(2πi) (x·m) f` almost everywhere
  (`TemperedDistribution.lineDerivOp_fourier_eq`).
* `moment_step`: the same in the coordinates `Vec 2`: `y_j f ∈ L²` and its transform is
  `(i / 2π) H`.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform LineDeriv Homogenization
open scoped FourierTransform SchwartzMap ENNReal

namespace AVRegularity.CycleWords.Discard

open AVRegularity.CoupledEnergyPlane.Fourier

section General

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- A Schwartz function times an `L²` function is integrable. -/
theorem schwartz_mul_integrable (φ : 𝓢(V, ℂ)) {g : V → ℂ} (hg : MemLp g 2 volume) :
    Integrable (fun x => φ x * g x) volume :=
  (φ.memLp 2 volume).integrable_mul hg

/-- **Classical line derivatives are distributional.** -/
theorem lineDerivOp_of_hasLineDerivAt (G H : Lp ℂ 2 (volume : Measure V)) (m : V)
    (g h : V → ℂ) (hG : G =ᵐ[volume] g) (hH : H =ᵐ[volume] h)
    (hd : ∀ x, HasLineDerivAt ℝ g (h x) x m) :
    ∂_{m} (G : 𝓢'(V, ℂ)) = (H : 𝓢'(V, ℂ)) := by
  have hg : MemLp g 2 volume := (Lp.memLp G).ae_eq hG
  have hh : MemLp h 2 volume := (Lp.memLp H).ae_eq hH
  ext φ
  rw [TemperedDistribution.lineDerivOp_apply_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply]
  have h1 : (∫ x, (-∂_{m} φ) x • G x) = -∫ x, (∂_{m} φ) x * g x := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [hG] with x hx
    rw [hx, neg_apply, smul_eq_mul, neg_mul]
  have h2 : (∫ x, φ x • H x) = ∫ x, φ x * h x := by
    apply integral_congr_ae
    filter_upwards [hH] with x hx
    rw [hx, smul_eq_mul]
  rw [h1, h2]
  refine (integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := (volume : Measure V)) (f := fun x => φ x) (f' := fun x => (∂_{m} φ) x) (g := g)
    (g' := h) (v := m) (B := ContinuousLinearMap.mul ℝ ℂ) ?_ ?_ ?_ ?_ ?_).symm
  · exact schwartz_mul_integrable (∂_{m} φ) hg
  · exact schwartz_mul_integrable φ hh
  · exact schwartz_mul_integrable φ hg
  · intro x _
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
    exact (φ.differentiableAt (x := x)).hasFDerivAt.hasLineDerivAt m
  · intro x _
    exact hd x

/-- **The frequency-side derivative is a physical-side multiplier.** -/
theorem fourierInv_ae_of_lineDerivOp (f H : Lp ℂ 2 (volume : Measure V)) (m : V)
    (hd : ∂_{m} ((𝓕 f : Lp ℂ 2 volume) : 𝓢'(V, ℂ)) = (H : 𝓢'(V, ℂ))) :
    (𝓕⁻ H : Lp ℂ 2 volume) =ᵐ[volume] fun x =>
      -((2 * (Real.pi : ℂ) * Complex.I) * (inner ℝ x m : ℂ) * f x) := by
  rw [← Lp.fourier_toTemperedDistribution_eq, TemperedDistribution.lineDerivOp_fourier_eq] at hd
  have h1 : ((𝓕⁻ H : Lp ℂ 2 volume) : 𝓢'(V, ℂ)) =
      -((2 * (Real.pi : ℂ) * Complex.I) •
        TemperedDistribution.smulLeftCLM ℂ (fun x => (inner ℝ x m : ℂ)) (f : 𝓢'(V, ℂ))) := by
    rw [← Lp.fourierInv_toTemperedDistribution_eq, ← hd, FourierTransform.fourierInv_fourier_eq,
      neg_smul]
  have h2 : ((-(𝓕⁻ H : Lp ℂ 2 volume) : Lp ℂ 2 volume) : 𝓢'(V, ℂ)) =
      (2 * (Real.pi : ℂ) * Complex.I) •
        TemperedDistribution.smulLeftCLM ℂ (fun x => (inner ℝ x m : ℂ)) (f : 𝓢'(V, ℂ)) := by
    have h3 := (Lp.toTemperedDistributionCLM ℂ (volume : Measure V) 2).map_neg
      (𝓕⁻ H : Lp ℂ 2 volume)
    rw [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistributionCLM_apply] at h3
    rw [h3, h1, neg_neg]
  have h4 := frequency_product_ae_of_toTemperedDistribution f (-(𝓕⁻ H : Lp ℂ 2 volume)) m h2
  filter_upwards [h4, Lp.coeFn_neg (𝓕⁻ H : Lp ℂ 2 volume)] with x hx hn
  rw [← hx, hn, Pi.neg_apply, neg_neg]

end General

/-- The inverse plane transform in the auxiliary Hilbert coordinates. -/
theorem coordinate_fourierL2_symm (h : Lp ℂ 2 (volume : Measure (Vec 2))) :
    coordinateL2Equiv (fourierL2.symm h) = 𝓕⁻ (coordinateL2Equiv h) := by
  have h1 := coordinate_fourierL2 (fourierL2.symm h)
  rw [LinearIsometryEquiv.apply_symm_apply] at h1
  rw [h1, FourierTransform.fourierInv_fourier_eq]

/-- The coordinate map sends the Hilbert coordinate vector to the basis vector. -/
theorem ofLp_add_smul_coordinateVector (x : AVRegularity.CoupledEnergyPlane.Fourier.HilbertTwo) (t : ℝ) (j : Fin 2) :
    WithLp.ofLp (x + t • AVRegularity.CoupledEnergyPlane.Fourier.coordinateVector j) = WithLp.ofLp x + t • basisVec j := by
  ext k
  simp [AVRegularity.CoupledEnergyPlane.Fourier.coordinateVector, basisVec, Pi.single_apply]

/-- **The step lemma.** If the transform `G` of `f ∈ L²` has the classical partial derivative `H`
in the direction `e_j`, and `H ∈ L²`, then `y_j f ∈ L²` with transform `(i / 2π) H`. -/
theorem moment_step (f : Lp ℂ 2 (volume : Measure (Vec 2))) (j : Fin 2) (G H : Vec 2 → ℂ)
    (hG : fourierL2 f =ᵐ[volume] G) (hH : MemLp H 2 volume)
    (hd : ∀ x, HasDerivAt (fun t : ℝ => G (x + t • basisVec j)) (H x) 0) :
    ∃ g : Lp ℂ 2 (volume : Measure (Vec 2)),
      (g =ᵐ[volume] fun y => (y j : ℂ) * f y) ∧
      fourierL2 g =ᵐ[volume] fun x => (Complex.I / (2 * (Real.pi : ℂ))) * H x := by
  set Hl : Lp ℂ 2 (volume : Measure (Vec 2)) := hH.toLp H with hHl
  have hmp := (PiLp.volume_preserving_ofLp (Fin 2)).quasiMeasurePreserving
  have hmp' := (PiLp.volume_preserving_toLp (Fin 2)).quasiMeasurePreserving
  -- the distributional derivative in the Hilbert coordinates
  have hGc : (𝓕 (coordinateL2Equiv f) : Lp ℂ 2 (volume : Measure AVRegularity.CoupledEnergyPlane.Fourier.HilbertTwo)) =ᵐ[volume]
      fun x : AVRegularity.CoupledEnergyPlane.Fourier.HilbertTwo => G (WithLp.ofLp x) := by
    rw [← coordinate_fourierL2]
    filter_upwards [coordinateL2Equiv_ae (fourierL2 f), hmp.ae hG] with x hx hx'
    rw [hx, hx']
  have hHc : (coordinateL2Equiv Hl : Lp ℂ 2 (volume : Measure AVRegularity.CoupledEnergyPlane.Fourier.HilbertTwo)) =ᵐ[volume]
      fun x : AVRegularity.CoupledEnergyPlane.Fourier.HilbertTwo => H (WithLp.ofLp x) := by
    filter_upwards [coordinateL2Equiv_ae Hl, hmp.ae hH.coeFn_toLp] with x hx hx'
    rw [hx, hx']
  have hline : ∀ x : AVRegularity.CoupledEnergyPlane.Fourier.HilbertTwo, HasLineDerivAt ℝ (fun x : AVRegularity.CoupledEnergyPlane.Fourier.HilbertTwo => G (WithLp.ofLp x))
      (H (WithLp.ofLp x)) x (AVRegularity.CoupledEnergyPlane.Fourier.coordinateVector j) := by
    intro x
    unfold HasLineDerivAt
    simp only [ofLp_add_smul_coordinateVector]
    exact hd (WithLp.ofLp x)
  have hdist := lineDerivOp_of_hasLineDerivAt _ _ (AVRegularity.CoupledEnergyPlane.Fourier.coordinateVector j) _ _ hGc hHc hline
  have hinv := fourierInv_ae_of_lineDerivOp (coordinateL2Equiv f) (coordinateL2Equiv Hl)
    (AVRegularity.CoupledEnergyPlane.Fourier.coordinateVector j) hdist
  rw [← coordinate_fourierL2_symm] at hinv
  -- back to `Vec 2`
  have hback : (fourierL2.symm Hl : Lp ℂ 2 (volume : Measure (Vec 2))) =ᵐ[volume] fun y =>
      -((2 * (Real.pi : ℂ) * Complex.I) * (y j : ℂ) * f y) := by
    have h1 := hmp'.ae hinv
    have h2 := hmp'.ae (coordinateL2Equiv_ae (fourierL2.symm Hl))
    have h3 := hmp'.ae (coordinateL2Equiv_ae f)
    filter_upwards [h1, h2, h3] with y hy1 hy2 hy3
    rw [hy2] at hy1
    rw [hy3] at hy1
    simpa [PiLp.inner_apply, AVRegularity.CoupledEnergyPlane.Fourier.coordinateVector, Pi.single_apply] using hy1
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  refine ⟨(Complex.I / (2 * (Real.pi : ℂ))) • fourierL2.symm Hl, ?_, ?_⟩
  · filter_upwards [Lp.coeFn_smul (Complex.I / (2 * (Real.pi : ℂ))) (fourierL2.symm Hl), hback]
      with y hy1 hy2
    rw [hy1, Pi.smul_apply, hy2, smul_eq_mul]
    field_simp
    rw [Complex.I_sq]
    ring
  · rw [map_smul, LinearIsometryEquiv.apply_symm_apply]
    filter_upwards [Lp.coeFn_smul (Complex.I / (2 * (Real.pi : ℂ))) Hl, hH.coeFn_toLp]
      with x hx1 hx2
    rw [hx1, Pi.smul_apply, hx2, smul_eq_mul]

end AVRegularity.CycleWords.Discard
end
end

section
/-! # The expanding cutoffs on scalar `L²` and `H¹`

The cutoffs `χ_n = spatialApproximationCutoff n` (equal to one near `0`, supported in
`|z| ≤ 2(n+1)`, gradient `O(1/(n+1))`) as bounded operators:

* `weakContL2Cut n` on `L²` (self-adjoint, at most one, strongly convergent to the identity),
* `weakContL2Deriv n k`, multiplication by `∂_k χ_n` (strongly convergent to zero),
* `weakContH1Cut n` on `H¹`, with value `χ_n u`, gradient `χ_n ∂_k u + ∂_k χ_n u`, a bound
  uniform in `n`, strong convergence to the identity, and gradients vanishing almost everywhere
  outside the ball of radius `2n + 3`. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory Set Filter AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CycleJointProofs
open AVRegularity.Analysis.Convolution
open scoped Topology

namespace AVRegularity.CycleWords.Discard

theorem weakCont_cutoff_abs_le (n : ℕ) (x : Vec 2) : |spatialApproximationCutoff n x| ≤ 1 := by
  rw [abs_of_nonneg (spatialApproximationCutoff_bounds n x).1]
  exact (spatialApproximationCutoff_bounds n x).2

/-- Multiplication by the `n`-th cutoff on scalar `L²`. -/
def weakContL2Cut (n : ℕ) :
    Lp ℝ 2 (volume : Measure (Vec 2)) →L[ℝ] Lp ℝ 2 (volume : Measure (Vec 2)) :=
  planeScalarMultiplier (spatialApproximationCutoff n)
    (spatialApproximationCutoff_smooth n).continuous (by norm_num : (0 : ℝ) ≤ 1)
    (weakCont_cutoff_abs_le n)

theorem weakContL2Cut_ae (n : ℕ) (u : Lp ℝ 2 (volume : Measure (Vec 2))) :
    weakContL2Cut n u =ᵐ[volume] fun z => spatialApproximationCutoff n z * u z :=
  planeScalarMultiplier_ae _ _ _ _ u

theorem weakContL2Cut_inner (n : ℕ) (u w : Lp ℝ 2 (volume : Measure (Vec 2))) :
    inner ℝ (weakContL2Cut n u) w = inner ℝ u (weakContL2Cut n w) :=
  planeScalarMultiplier_inner _ _ _ _ u w

theorem weakContL2Cut_norm_le (n : ℕ) : ‖weakContL2Cut n‖ ≤ 1 :=
  planeScalarMultiplier_norm_le _ _ _ _

theorem weakContL2Cut_tendsto (u : Lp ℝ 2 (volume : Measure (Vec 2))) :
    Tendsto (fun n => weakContL2Cut n u) atTop (𝓝 u) :=
  planeScalarMultiplier_tendsto_one spatialApproximationCutoff
    (fun n => (spatialApproximationCutoff_smooth n).continuous)
    spatialApproximationCutoff_bounds spatialApproximationCutoff_tendsto u

/-! ## The derivative of the cutoff -/

theorem weakCont_cutoff_deriv_continuous (n : ℕ) (k : Fin 2) :
    Continuous (fun x => fderiv ℝ (spatialApproximationCutoff n) x (basisVec k)) :=
  ((spatialApproximationCutoff_smooth n).continuous_fderiv (by simp)).clm_apply continuous_const

/-- The uniform bound of `∂_k χ_n`. -/
def weakContDerivBound (n : ℕ) (k : Fin 2) : ℝ :=
  Classical.choose spatialApproximationCutoff_derivative_bound * spatialApproximationScale n *
    ‖(basisVec k : Vec 2)‖

theorem weakContDerivBound_nonneg (n : ℕ) (k : Fin 2) : 0 ≤ weakContDerivBound n k :=
  mul_nonneg (mul_nonneg (Classical.choose_spec spatialApproximationCutoff_derivative_bound).1
    (spatialApproximationScale_pos n).le) (norm_nonneg _)

theorem weakCont_cutoff_deriv_le (n : ℕ) (k : Fin 2) (x : Vec 2) :
    |fderiv ℝ (spatialApproximationCutoff n) x (basisVec k)| ≤ weakContDerivBound n k :=
  (Classical.choose_spec spatialApproximationCutoff_derivative_bound).2 n x (basisVec k)

theorem weakContDerivBound_tendsto (k : Fin 2) :
    Tendsto (fun n => weakContDerivBound n k) atTop (𝓝 0) := by
  unfold weakContDerivBound
  simpa only [mul_zero, zero_mul] using (spatialApproximationScale_tendsto.const_mul
    (Classical.choose spatialApproximationCutoff_derivative_bound)).mul_const
      ‖(basisVec k : Vec 2)‖

/-- The bound of `∂_k χ_n` uniform in `n`. -/
def weakContDerivSup (k : Fin 2) : ℝ :=
  Classical.choose spatialApproximationCutoff_derivative_bound * ‖(basisVec k : Vec 2)‖

theorem weakContDerivBound_le_sup (n : ℕ) (k : Fin 2) :
    weakContDerivBound n k ≤ weakContDerivSup k := by
  unfold weakContDerivBound weakContDerivSup
  have h0 := (Classical.choose_spec spatialApproximationCutoff_derivative_bound).1
  have h1 := spatialApproximationScale_le_one n
  have h2 := (spatialApproximationScale_pos n).le
  have h3 : Classical.choose spatialApproximationCutoff_derivative_bound *
      spatialApproximationScale n ≤
        Classical.choose spatialApproximationCutoff_derivative_bound :=
    mul_le_of_le_one_right h0 h1
  exact mul_le_mul_of_nonneg_right h3 (norm_nonneg _)

theorem weakContDerivSup_nonneg (k : Fin 2) : 0 ≤ weakContDerivSup k :=
  mul_nonneg (Classical.choose_spec spatialApproximationCutoff_derivative_bound).1 (norm_nonneg _)

/-- Multiplication by `∂_k χ_n` on scalar `L²`. -/
def weakContL2Deriv (n : ℕ) (k : Fin 2) :
    Lp ℝ 2 (volume : Measure (Vec 2)) →L[ℝ] Lp ℝ 2 (volume : Measure (Vec 2)) :=
  planeScalarMultiplier (fun x => fderiv ℝ (spatialApproximationCutoff n) x (basisVec k))
    (weakCont_cutoff_deriv_continuous n k) (weakContDerivBound_nonneg n k)
    (weakCont_cutoff_deriv_le n k)

theorem weakContL2Deriv_ae (n : ℕ) (k : Fin 2) (u : Lp ℝ 2 (volume : Measure (Vec 2))) :
    weakContL2Deriv n k u =ᵐ[volume]
      fun z => fderiv ℝ (spatialApproximationCutoff n) z (basisVec k) * u z :=
  planeScalarMultiplier_ae _ _ _ _ u

theorem weakContL2Deriv_norm_le (n : ℕ) (k : Fin 2) : ‖weakContL2Deriv n k‖ ≤ weakContDerivSup k :=
  (planeScalarMultiplier_norm_le _ _ _ _).trans (weakContDerivBound_le_sup n k)

theorem weakContL2Deriv_tendsto (k : Fin 2) (u : Lp ℝ 2 (volume : Measure (Vec 2))) :
    Tendsto (fun n => weakContL2Deriv n k u) atTop (𝓝 0) :=
  planeScalarMultiplier_tendsto_zero
    (fun n x => fderiv ℝ (spatialApproximationCutoff n) x (basisVec k))
    (fun n => weakCont_cutoff_deriv_continuous n k) (fun n => weakContDerivBound n k)
    (fun n => weakContDerivBound_nonneg n k) (fun n => weakCont_cutoff_deriv_le n k)
    (weakContDerivBound_tendsto k) u

/-! ## The cutoff on `H¹` -/

theorem weakCont_h1cut_contDiff (n : ℕ) :
    ContDiff ℝ 1 (fun x => scalarFiberCoefficient (E := ℝ) (spatialApproximationCutoff n x)) :=
  ((spatialApproximationCutoff_smooth n).of_le (by simp)).smul contDiff_const

theorem weakCont_h1cut_budget : ∃ A : Fin 2 → ℝ, (∀ l, 0 ≤ A l) ∧ ∀ n (l : Fin 2) x,
    ‖coefficientDerivativeArray
      (fun y => scalarFiberCoefficient (E := ℝ) (spatialApproximationCutoff n y)) l.val x‖ ≤
        A l := by
  have hC : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : Vec 2 => scalarFiberCoefficient (E := ℝ) (spatialApproximationBump y)) :=
    spatialApproximationBump.contDiff.smul contDiff_const
  have hc : HasCompactSupport
      (fun y : Vec 2 => scalarFiberCoefficient (E := ℝ) (spatialApproximationBump y)) :=
    spatialApproximationBump.hasCompactSupport.smul_right
  obtain ⟨A, hA, hb⟩ := exists_smoothCompact_coefficient_rescale_bound _ hC hc 1
  exact ⟨A, hA, fun n l x => hb (spatialApproximationScale n) (spatialApproximationScale_pos n).le
    (spatialApproximationScale_le_one n) l x⟩

/-- The budget of the cutoffs on `H¹`, uniform in `n`. -/
def weakContH1Budget : Fin 2 → ℝ := Classical.choose weakCont_h1cut_budget

theorem weakContH1Budget_nonneg (l : Fin 2) : 0 ≤ weakContH1Budget l :=
  (Classical.choose_spec weakCont_h1cut_budget).1 l

theorem weakContH1Budget_bound (n : ℕ) (l : Fin 2) (x : Vec 2) :
    ‖coefficientDerivativeArray
      (fun y => scalarFiberCoefficient (E := ℝ) (spatialApproximationCutoff n y)) l.val x‖ ≤
        weakContH1Budget l :=
  (Classical.choose_spec weakCont_h1cut_budget).2 n l x

/-- Multiplication by the `n`-th cutoff on scalar `H¹`. -/
def weakContH1Cut (n : ℕ) : PlaneHk Set.univ 1 ℝ →L[ℝ] PlaneHk Set.univ 1 ℝ :=
  planeH1CoefficientOperator
    (fun x => scalarFiberCoefficient (E := ℝ) (spatialApproximationCutoff n x))
    (weakCont_h1cut_contDiff n) weakContH1Budget (weakContH1Budget_bound n)

theorem weakContH1Cut_value (n : ℕ) (w : PlaneHk Set.univ 1 ℝ) :
    planeHkValueOperator 1 (weakContH1Cut n w) = weakContL2Cut n (planeHkValueOperator 1 w) := by
  apply Lp.ext
  filter_upwards [planeH1ScalarMultiplier_value_ae (E := ℝ) (spatialApproximationCutoff n)
    (weakCont_h1cut_contDiff n) weakContH1Budget (weakContH1Budget_bound n) w,
    weakContL2Cut_ae n (planeHkValueOperator 1 w)] with x h1 h2
  exact h1.trans h2.symm

theorem weakContH1Cut_gradient (n : ℕ) (w : PlaneHk Set.univ 1 ℝ) (k : Fin 2) :
    planeH1GradientOperator (weakContH1Cut n w) k =
      weakContL2Cut n (planeH1GradientOperator w k) +
        weakContL2Deriv n k (planeHkValueOperator 1 w) := by
  apply Lp.ext
  filter_upwards [planeH1ScalarMultiplier_gradient_ae (E := ℝ) (spatialApproximationCutoff n)
    ((spatialApproximationCutoff_smooth n).of_le (by simp)) (weakCont_h1cut_contDiff n)
    weakContH1Budget (weakContH1Budget_bound n) w k,
    weakContL2Cut_ae n (planeH1GradientOperator w k),
    weakContL2Deriv_ae n k (planeHkValueOperator 1 w),
    Lp.coeFn_add (weakContL2Cut n (planeH1GradientOperator w k))
      (weakContL2Deriv n k (planeHkValueOperator 1 w))] with x h1 h2 h3 h4
  rw [h4, Pi.add_apply, h2, h3]
  exact h1

theorem weakContH1Cut_norm_apply_le (n : ℕ) (w : PlaneHk Set.univ 1 ℝ) :
    ‖weakContH1Cut n w‖ ≤ (weakContH1Budget 0 + weakContH1Budget 1) * ‖w‖ :=
  planeH1_mulCoefficient_norm_le _ (weakCont_h1cut_contDiff n) weakContH1Budget
    (weakContH1Budget_bound n) w

theorem weakContH1Cut_tendsto (w : PlaneHk Set.univ 1 ℝ) :
    Tendsto (fun n => weakContH1Cut n w) atTop (𝓝 w) := by
  apply planeH1_tendsto_of_readouts
  · simp only [weakContH1Cut_value]
    exact weakContL2Cut_tendsto _
  · have hc : Tendsto (fun n => fun k : Fin 2 => planeH1GradientOperator (weakContH1Cut n w) k)
        atTop (𝓝 (fun k : Fin 2 => planeH1GradientOperator w k)) := by
      apply tendsto_pi_nhds.mpr
      intro k
      simp only [weakContH1Cut_gradient]
      simpa only [add_zero] using (weakContL2Cut_tendsto (planeH1GradientOperator w k)).add
        (weakContL2Deriv_tendsto k (planeHkValueOperator 1 w))
    have hp := (PiLp.continuous_toLp 2
      (fun _ : Fin 2 => Lp ℝ 2 (volume : Measure (Vec 2)))).tendsto
        (fun k : Fin 2 => planeH1GradientOperator w k) |>.comp hc
    simpa only [Function.comp_def, WithLp.toLp_ofLp] using hp

/-- The support of the `n`-th cutoff is inside the closed ball of radius `2(n+1)`. -/
theorem weakCont_cutoff_tsupport_subset (n : ℕ) :
    tsupport (spatialApproximationCutoff n) ⊆ Metric.closedBall (0 : Vec 2) (2 * ((n : ℝ) + 1)) := by
  refine closure_minimal (fun x hx => ?_) Metric.isClosed_closedBall
  have hx' : spatialApproximationEquiv n x ∈ Function.support spatialApproximationBump := hx
  rw [spatialApproximationBump.support_eq, Metric.mem_ball, dist_zero_right] at hx'
  have hs : spatialApproximationEquiv n x = spatialApproximationScale n • x := rfl
  rw [hs, norm_smul, Real.norm_of_nonneg (spatialApproximationScale_pos n).le] at hx'
  have hr : spatialApproximationBump.rOut = 2 := rfl
  rw [hr] at hx'
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [Metric.mem_closedBall, dist_zero_right]
  unfold spatialApproximationScale at hx'
  rw [one_div, inv_mul_lt_iff₀ hpos] at hx'
  linarith

/-- Outside the ball of radius `2n + 3` the gradient of a cut `H¹` element vanishes almost
everywhere. -/
theorem weakContH1Cut_jet_outside (n : ℕ) (w : PlaneHk Set.univ 1 ℝ) (k : Fin 2) :
    ∀ᵐ z ∂volume, z ∉ Metric.ball (0 : Vec 2) (((2 * n + 2 : ℕ) : ℝ) + 1) →
      (weakContH1Cut n w).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩ z = 0 := by
  have hg := planeH1ScalarMultiplier_gradient_ae (E := ℝ) (spatialApproximationCutoff n)
    ((spatialApproximationCutoff_smooth n).of_le (by simp)) (weakCont_h1cut_contDiff n)
    weakContH1Budget (weakContH1Budget_bound n) w k
  have hu : (planeH1GradientOperator (weakContH1Cut n w) k : Vec 2 → ℝ) =ᵐ[volume]
      (weakContH1Cut n w).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩ :=
    univToPlane_ae _
  filter_upwards [hg, hu] with z h1 h2 hz
  have hzs : z ∉ tsupport (spatialApproximationCutoff n) := by
    intro hmem
    have hcb := weakCont_cutoff_tsupport_subset n hmem
    rw [Metric.mem_closedBall, dist_zero_right] at hcb
    apply hz
    rw [Metric.mem_ball, dist_zero_right]
    push_cast
    linarith
  have hχ : spatialApproximationCutoff n z = 0 := image_eq_zero_of_notMem_tsupport hzs
  have hdχ : fderiv ℝ (spatialApproximationCutoff n) z = 0 := fderiv_of_notMem_tsupport ℝ hzs
  rw [← h2]
  have h1' : (planeH1GradientOperator (weakContH1Cut n w) k : Vec 2 → ℝ) z =
      spatialApproximationCutoff n z • (planeH1GradientOperator w k : Vec 2 → ℝ) z +
        fderiv ℝ (spatialApproximationCutoff n) z (basisVec k) •
          (planeHkValueOperator 1 w : Vec 2 → ℝ) z := h1
  rw [h1', hχ, hdχ]
  simp

end AVRegularity.CycleWords.Discard
end
end

section
/-! # Removing the cutoff at one time

At a fixed time let `F` be the letter flux, `wt` a weight with `wt⁻¹ F ∈ L²` (norm `≤ A`), and `Ψ`
an `H¹` test with `wt Ψ, wt ∇Ψ ∈ L²` (norms `≤ B`). If `S_n ∈ L²` agrees with `F` on the ball of
radius `2n + 3`, then

`⟨e·S_n, ∇(χ_n Ψ)⟩ → ∫ ∑_k ⟨e, F_k⟩ ∂_kΨ`, and `|⟨e·S_n, ∇(χ_n Ψ)⟩| ≤ c ‖e‖ A B` for every `n`

(`weakCont_flux_term`): the weight is split between the flux and the test, and the cutoffs converge
strongly on `L²`. `weakCont_integrand_tendsto` adds the two generator terms, which cancel in the
limit when `⟨X, Ψ⟩ = ⟨Y, s⟩` (the opposite-drift symmetry of the generator form). -/

@[expose] public noncomputable section

open Homogenization MeasureTheory Set Filter AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CycleJointProofs
open scoped Topology

namespace AVRegularity.CycleWords.Discard

/-- Outside the ball of radius `2n + 3` the `n`-th cutoff and its derivative vanish. -/
theorem weakCont_cutoff_zero_outside (n : ℕ) {z : Vec 2}
    (hz : z ∉ Metric.ball (0 : Vec 2) (((2 * n + 2 : ℕ) : ℝ) + 1)) :
    spatialApproximationCutoff n z = 0 ∧ fderiv ℝ (spatialApproximationCutoff n) z = 0 := by
  have hzs : z ∉ tsupport (spatialApproximationCutoff n) := by
    intro hmem
    have hcb := weakCont_cutoff_tsupport_subset n hmem
    rw [Metric.mem_closedBall, dist_zero_right] at hcb
    apply hz
    rw [Metric.mem_ball, dist_zero_right]
    push_cast
    linarith
  exact ⟨image_eq_zero_of_notMem_tsupport hzs, fderiv_of_notMem_tsupport ℝ hzs⟩

/-- A function that agrees almost everywhere on every ball with a measurable function is almost
everywhere strongly measurable. -/
theorem weakCont_aestronglyMeasurable_of_balls {E : Type*} [NormedAddCommGroup E]
    (f : Vec 2 → E) (S : ℕ → Vec 2 → E) (hS : ∀ n, AEStronglyMeasurable (S n) volume)
    (h : ∀ n : ℕ, ∀ᵐ z ∂volume, z ∈ Metric.ball (0 : Vec 2) ((n : ℝ) + 1) → S n z = f z) :
    AEStronglyMeasurable f volume := by
  refine aestronglyMeasurable_of_tendsto_ae atTop hS ?_
  filter_upwards [ae_all_iff.mpr h] with z hz
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop ⌈‖z‖⌉₊] with n hn
  refine (hz n ?_).symm
  rw [Metric.mem_ball, dist_zero_right]
  have h1 := Nat.le_ceil ‖z‖
  have h2 : (⌈‖z‖⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
  linarith

section FluxTerm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The constant of the flux term: `∑_k (1 + sup |∂_k χ|)`. -/
def weakContFluxConst : ℝ := ∑ k : Fin 2, (1 + weakContDerivSup k)

theorem weakCont_alg_in (a w g v c d : ℝ) (hw : w ≠ 0) :
    a * (c * g + d * v) = w⁻¹ * a * (c * (w * g) + d * (w * v)) := by
  field_simp

theorem weakCont_alg_out (x y g v g' v' : ℝ) :
    x * (0 * g + 0 * v) = y * (0 * g' + 0 * v') := by
  ring

theorem weakCont_alg_val (a w g : ℝ) (hw : w ≠ 0) : w⁻¹ * a * (w * g) = a * g := by
  field_simp

omit [BorelSpace E] in
/-- One direction of the flux term, with the weight moved from the flux to the test. -/
theorem weakCont_flux_term_key (e : E) (F : Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (wt : Vec 2 → ℝ) (hw1 : ∀ z, 0 < wt z) (S : PlaneFluxL2 E) (n : ℕ) (k : Fin 2)
    (hS : ∀ᵐ z ∂volume, z ∈ Metric.ball (0 : Vec 2) (((2 * n + 2 : ℕ) : ℝ) + 1) →
      (S k : Vec 2 → E) z = F z k)
    (G0 V0 Fw Gw Vw : Lp ℝ 2 (volume : Measure (Vec 2)))
    (hFw : Fw =ᵐ[volume] fun z => (wt z)⁻¹ * inner ℝ e (F z k))
    (hGw : Gw =ᵐ[volume] fun z => wt z * (G0 : Vec 2 → ℝ) z)
    (hVw : Vw =ᵐ[volume] fun z => wt z * (V0 : Vec 2 → ℝ) z) :
    inner ℝ (planeFluxFiberCoordinateCLM e S k)
        (weakContL2Cut n G0 + weakContL2Deriv n k V0) =
      inner ℝ Fw (weakContL2Cut n Gw + weakContL2Deriv n k Vw) := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  have hgr : (weakContL2Cut n G0 + weakContL2Deriv n k V0 :
      Lp ℝ 2 (volume : Measure (Vec 2))) =ᵐ[volume]
      fun z => spatialApproximationCutoff n z * (G0 : Vec 2 → ℝ) z +
        fderiv ℝ (spatialApproximationCutoff n) z (basisVec k) * (V0 : Vec 2 → ℝ) z :=
    (Lp.coeFn_add _ _).trans ((weakContL2Cut_ae n G0).add (weakContL2Deriv_ae n k V0))
  have hgr' : (weakContL2Cut n Gw + weakContL2Deriv n k Vw :
      Lp ℝ 2 (volume : Measure (Vec 2))) =ᵐ[volume]
      fun z => spatialApproximationCutoff n z * (wt z * (G0 : Vec 2 → ℝ) z) +
        fderiv ℝ (spatialApproximationCutoff n) z (basisVec k) * (wt z * (V0 : Vec 2 → ℝ) z) :=
    (Lp.coeFn_add _ _).trans
      (((weakContL2Cut_ae n Gw).trans (Filter.EventuallyEq.rfl.mul hGw)).add
        ((weakContL2Deriv_ae n k Vw).trans (Filter.EventuallyEq.rfl.mul hVw)))
  filter_upwards [planeFluxFiberCoordinateCLM_ae e S k, hS, hgr, hgr', hFw] with z h1 h2 h3 h4 h5
  rw [h1, h3, h4, h5, Real.inner_apply, Real.inner_apply]
  by_cases hz : z ∈ Metric.ball (0 : Vec 2) (((2 * n + 2 : ℕ) : ℝ) + 1)
  · rw [h2 hz]
    exact weakCont_alg_in _ _ _ _ _ _ (hw1 z).ne'
  · obtain ⟨hχ, hdχ⟩ := weakCont_cutoff_zero_outside n hz
    rw [hχ, hdχ, zero_apply]
    exact weakCont_alg_out _ _ _ _ _ _

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
/-- The limit of one direction of the flux term, with the weight moved back. -/
theorem weakCont_flux_term_val (e : E) (F : Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (wt : Vec 2 → ℝ) (hw1 : ∀ z, 0 < wt z) (k : Fin 2)
    (G0 Fw Gw : Lp ℝ 2 (volume : Measure (Vec 2)))
    (hFw : Fw =ᵐ[volume] fun z => (wt z)⁻¹ * inner ℝ e (F z k))
    (hGw : Gw =ᵐ[volume] fun z => wt z * (G0 : Vec 2 → ℝ) z) :
    Integrable (fun z => inner ℝ e (F z k) * (G0 : Vec 2 → ℝ) z) volume ∧
      inner ℝ Fw Gw = ∫ z, inner ℝ e (F z k) * (G0 : Vec 2 → ℝ) z := by
  have hae : (fun z => inner ℝ ((Fw : Vec 2 → ℝ) z) ((Gw : Vec 2 → ℝ) z)) =ᵐ[volume]
      fun z => inner ℝ e (F z k) * (G0 : Vec 2 → ℝ) z := by
    filter_upwards [hFw, hGw] with z h1 h2
    rw [h1, h2, Real.inner_apply]
    exact weakCont_alg_val _ _ _ (hw1 z).ne'
  refine ⟨(L2.integrable_inner Fw Gw).congr hae, ?_⟩
  rw [L2.inner_def]
  exact integral_congr_ae hae

omit [BorelSpace E] in
/-- **The flux term at one time**: convergence and a bound uniform in the cutoff. -/
theorem weakCont_flux_term (e : E) (F : Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (wt : Vec 2 → ℝ) (hwc : Continuous wt) (hw1 : ∀ z, 0 < wt z)
    (hFm : ∀ k : Fin 2, AEStronglyMeasurable (fun z => F z k) volume)
    (Af : ℝ) (hAf : 0 ≤ Af)
    (hF : ∀ k : Fin 2, eLpNorm (fun z => (wt z)⁻¹ • F z k) 2 volume ≤ ENNReal.ofReal Af)
    (Sn : ℕ → PlaneFluxL2 E)
    (hSn : ∀ n k, ∀ᵐ z ∂volume, z ∈ Metric.ball (0 : Vec 2) (((2 * n + 2 : ℕ) : ℝ) + 1) →
      (Sn n k : Vec 2 → E) z = F z k)
    (Ψ : PlaneHk Set.univ 1 ℝ) (Bd : ℝ) (hBd : 0 ≤ Bd)
    (hΨv : eLpNorm (fun z => wt z * (planeHkValueOperator 1 Ψ : Vec 2 → ℝ) z) 2 volume ≤
      ENNReal.ofReal Bd)
    (hΨg : ∀ k : Fin 2,
      eLpNorm (fun z => wt z * (planeH1GradientOperator Ψ k : Vec 2 → ℝ) z) 2 volume ≤
        ENNReal.ofReal Bd) :
    (∀ k : Fin 2, Integrable (fun z => inner ℝ e (F z k) *
        (planeH1GradientOperator Ψ k : Vec 2 → ℝ) z) volume) ∧
      Tendsto (fun n => inner ℝ (planeFluxFiberCoordinateCLM e (Sn n))
        (planeH1GradientOperator (weakContH1Cut n Ψ))) atTop
        (𝓝 (∫ z, ∑ k : Fin 2, inner ℝ e (F z k) *
          (planeH1GradientOperator Ψ k : Vec 2 → ℝ) z)) ∧
      ∀ n, |inner ℝ (planeFluxFiberCoordinateCLM e (Sn n))
        (planeH1GradientOperator (weakContH1Cut n Ψ))| ≤ weakContFluxConst * (‖e‖ * Af) * Bd := by
  have hwinv : Continuous fun z => (wt z)⁻¹ := hwc.inv₀ fun z => (hw1 z).ne'
  -- the weighted flux coordinate
  have hpt : ∀ (k : Fin 2) (z : Vec 2), ‖(wt z)⁻¹ * inner ℝ e (F z k)‖ ≤
      ‖e‖ * ‖(wt z)⁻¹ • F z k‖ := by
    intro k z
    rw [norm_mul, norm_smul]
    calc ‖(wt z)⁻¹‖ * ‖inner ℝ e (F z k)‖ ≤ ‖(wt z)⁻¹‖ * (‖e‖ * ‖F z k‖) :=
          mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (norm_nonneg _)
      _ = ‖e‖ * (‖(wt z)⁻¹‖ * ‖F z k‖) := by ring
  have hFwm : ∀ k : Fin 2, AEStronglyMeasurable (fun z => (wt z)⁻¹ * inner ℝ e (F z k)) volume :=
    fun k => hwinv.aestronglyMeasurable.mul (aestronglyMeasurable_const.inner (hFm k))
  have hFwle : ∀ k : Fin 2, eLpNorm (fun z => (wt z)⁻¹ * inner ℝ e (F z k)) 2 volume ≤
      ENNReal.ofReal (‖e‖ * Af) := by
    intro k
    refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hFwm k)
      (Filter.Eventually.of_forall (hpt k)) 2).trans ?_
    rw [ENNReal.ofReal_mul (norm_nonneg e)]
    exact mul_le_mul' le_rfl (hF k)
  have hFw : ∀ k : Fin 2, MemLp (fun z => (wt z)⁻¹ * inner ℝ e (F z k)) 2 volume := fun k =>
    (hFwle k).trans_lt ENNReal.ofReal_lt_top
  obtain ⟨Fw, hFwc, hFwn⟩ : ∃ Fw : Fin 2 → Lp ℝ 2 (volume : Measure (Vec 2)),
      (∀ k, Fw k =ᵐ[volume] fun z => (wt z)⁻¹ * inner ℝ e (F z k)) ∧
        ∀ k, ‖Fw k‖ ≤ ‖e‖ * Af := by
    refine ⟨fun k => (hFw k).toLp _, fun k => (hFw k).coeFn_toLp, fun k => ?_⟩
    rw [Lp.norm_toLp]
    exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg (norm_nonneg _) hAf) (hFwle k)
  -- the weighted test
  have hGw : ∀ k : Fin 2, MemLp (fun z => wt z * (planeH1GradientOperator Ψ k : Vec 2 → ℝ) z)
      2 volume := fun k => (hΨg k).trans_lt ENNReal.ofReal_lt_top
  obtain ⟨Gw, hGwc, hGwn⟩ : ∃ Gw : Fin 2 → Lp ℝ 2 (volume : Measure (Vec 2)),
      (∀ k, Gw k =ᵐ[volume] fun z => wt z * (planeH1GradientOperator Ψ k : Vec 2 → ℝ) z) ∧
        ∀ k, ‖Gw k‖ ≤ Bd := by
    refine ⟨fun k => (hGw k).toLp _, fun k => (hGw k).coeFn_toLp, fun k => ?_⟩
    rw [Lp.norm_toLp]
    exact ENNReal.toReal_le_of_le_ofReal hBd (hΨg k)
  have hVw : MemLp (fun z => wt z * (planeHkValueOperator 1 Ψ : Vec 2 → ℝ) z) 2 volume :=
    hΨv.trans_lt ENNReal.ofReal_lt_top
  obtain ⟨Vw, hVwc, hVwn⟩ : ∃ Vw : Lp ℝ 2 (volume : Measure (Vec 2)),
      (Vw =ᵐ[volume] fun z => wt z * (planeHkValueOperator 1 Ψ : Vec 2 → ℝ) z) ∧ ‖Vw‖ ≤ Bd := by
    refine ⟨hVw.toLp _, hVw.coeFn_toLp, ?_⟩
    rw [Lp.norm_toLp]
    exact ENNReal.toReal_le_of_le_ofReal hBd hΨv
  have hinner : ∀ n, inner ℝ (planeFluxFiberCoordinateCLM e (Sn n))
        (planeH1GradientOperator (weakContH1Cut n Ψ)) =
      ∑ k : Fin 2, inner ℝ (Fw k) (weakContL2Cut n (Gw k) + weakContL2Deriv n k Vw) := by
    intro n
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [weakContH1Cut_gradient]
    exact weakCont_flux_term_key e F wt hw1 (Sn n) n k (hSn n k) _ _ _ _ _ (hFwc k) (hGwc k) hVwc
  -- the limit, with the weight moved back
  have hvalk := fun k : Fin 2 => weakCont_flux_term_val e F wt hw1 k
    (planeH1GradientOperator Ψ k) (Fw k) (Gw k) (hFwc k) (hGwc k)
  have hval : ∑ k : Fin 2, inner ℝ (Fw k) (Gw k) =
      ∫ z, ∑ k : Fin 2, inner ℝ e (F z k) * (planeH1GradientOperator Ψ k : Vec 2 → ℝ) z := by
    rw [integral_finsetSum _ fun k _ => (hvalk k).1]
    exact Finset.sum_congr rfl fun k _ => (hvalk k).2
  refine ⟨fun k => (hvalk k).1, ?_, ?_⟩
  · have hlim : Tendsto (fun n => ∑ k : Fin 2,
          inner ℝ (Fw k) (weakContL2Cut n (Gw k) + weakContL2Deriv n k Vw)) atTop
        (𝓝 (∑ k : Fin 2, inner ℝ (Fw k) (Gw k + 0))) :=
      tendsto_finsetSum _ fun k _ => tendsto_const_nhds.inner
        ((weakContL2Cut_tendsto (Gw k)).add (weakContL2Deriv_tendsto k Vw))
    simp only [add_zero] at hlim
    rw [hval] at hlim
    exact hlim.congr fun n => (hinner n).symm
  · intro n
    rw [hinner n]
    have hterm : ∀ k : Fin 2,
        |inner ℝ (Fw k) (weakContL2Cut n (Gw k) + weakContL2Deriv n k Vw)| ≤
          (‖e‖ * Af) * ((1 + weakContDerivSup k) * Bd) := by
      intro k
      have ha : ‖weakContL2Cut n (Gw k)‖ ≤ 1 * Bd :=
        ((weakContL2Cut n).le_opNorm _).trans
          (mul_le_mul (weakContL2Cut_norm_le n) (hGwn k) (norm_nonneg _) zero_le_one)
      have hb : ‖weakContL2Deriv n k Vw‖ ≤ weakContDerivSup k * Bd :=
        ((weakContL2Deriv n k).le_opNorm _).trans
          (mul_le_mul (weakContL2Deriv_norm_le n k) hVwn (norm_nonneg _)
            (weakContDerivSup_nonneg k))
      have h1 : ‖weakContL2Cut n (Gw k) + weakContL2Deriv n k Vw‖ ≤
          (1 + weakContDerivSup k) * Bd := by
        refine (norm_add_le _ _).trans ?_
        linarith
      exact (abs_real_inner_le_norm _ _).trans
        (mul_le_mul (hFwn k) h1 (norm_nonneg _) (mul_nonneg (norm_nonneg _) hAf))
    calc |∑ k : Fin 2, inner ℝ (Fw k) (weakContL2Cut n (Gw k) + weakContL2Deriv n k Vw)|
        ≤ ∑ k : Fin 2, |inner ℝ (Fw k) (weakContL2Cut n (Gw k) + weakContL2Deriv n k Vw)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k : Fin 2, (‖e‖ * Af) * ((1 + weakContDerivSup k) * Bd) :=
          Finset.sum_le_sum fun k _ => hterm k
      _ = weakContFluxConst * (‖e‖ * Af) * Bd := by
          unfold weakContFluxConst
          rw [Finset.sum_mul, Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ => by ring

omit [BorelSpace E] in
/-- **The integrand of the cut pairing at one time**: its limit and a bound uniform in the cutoff.
`X` and `Y` are the generator duals of the level and of the test; they cancel in the limit. -/
theorem weakCont_integrand_tendsto (e : E) (F : Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (wt : Vec 2 → ℝ) (hwc : Continuous wt) (hw1 : ∀ z, 0 < wt z)
    (hFm : ∀ k : Fin 2, AEStronglyMeasurable (fun z => F z k) volume)
    (Af : ℝ) (hAf : 0 ≤ Af)
    (hF : ∀ k : Fin 2, eLpNorm (fun z => (wt z)⁻¹ • F z k) 2 volume ≤ ENNReal.ofReal Af)
    (Sn : ℕ → PlaneFluxL2 E)
    (hSn : ∀ n k, ∀ᵐ z ∂volume, z ∈ Metric.ball (0 : Vec 2) (((2 * n + 2 : ℕ) : ℝ) + 1) →
      (Sn n k : Vec 2 → E) z = F z k)
    (Ψ : PlaneHk Set.univ 1 ℝ) (Bd : ℝ) (hBd : 0 ≤ Bd)
    (hΨv : eLpNorm (fun z => wt z * (planeHkValueOperator 1 Ψ : Vec 2 → ℝ) z) 2 volume ≤
      ENNReal.ofReal Bd)
    (hΨg : ∀ k : Fin 2,
      eLpNorm (fun z => wt z * (planeH1GradientOperator Ψ k : Vec 2 → ℝ) z) 2 volume ≤
        ENNReal.ofReal Bd)
    (s X Y : PlaneHk Set.univ 1 ℝ) (hXY : inner ℝ X Ψ = inner ℝ Y s) :
    (∀ k : Fin 2, Integrable (fun z => inner ℝ e (F z k) *
        (planeH1GradientOperator Ψ k : Vec 2 → ℝ) z) volume) ∧
      Tendsto (fun n => inner ℝ (X + planeSourceDual 0 (planeFluxFiberCoordinateCLM e (Sn n)))
          (weakContH1Cut n Ψ) - inner ℝ Y (weakContH1Cut n s)) atTop
        (𝓝 (-∫ z, ∑ k : Fin 2, inner ℝ e (F z k) *
          (planeH1GradientOperator Ψ k : Vec 2 → ℝ) z)) ∧
      ∀ n, |inner ℝ (X + planeSourceDual 0 (planeFluxFiberCoordinateCLM e (Sn n)))
          (weakContH1Cut n Ψ) - inner ℝ Y (weakContH1Cut n s)| ≤
        (weakContH1Budget 0 + weakContH1Budget 1) * ‖X‖ * ‖Ψ‖ +
          weakContFluxConst * (‖e‖ * Af) * Bd +
          (weakContH1Budget 0 + weakContH1Budget 1) * ‖Y‖ * ‖s‖ := by
  obtain ⟨hfint, hflim, hfb⟩ :=
    weakCont_flux_term e F wt hwc hw1 hFm Af hAf hF Sn hSn Ψ Bd hBd hΨv hΨg
  have hsplit : ∀ n, inner ℝ (X + planeSourceDual 0 (planeFluxFiberCoordinateCLM e (Sn n)))
        (weakContH1Cut n Ψ) - inner ℝ Y (weakContH1Cut n s) =
      inner ℝ X (weakContH1Cut n Ψ) -
        inner ℝ (planeFluxFiberCoordinateCLM e (Sn n))
          (planeH1GradientOperator (weakContH1Cut n Ψ)) -
        inner ℝ Y (weakContH1Cut n s) := by
    intro n
    rw [inner_add_left, planeSourceDual_pair, inner_zero_left]
    ring
  refine ⟨hfint, ?_, ?_⟩
  · have h1 : Tendsto (fun n => inner ℝ X (weakContH1Cut n Ψ)) atTop (𝓝 (inner ℝ X Ψ)) :=
      tendsto_const_nhds.inner (weakContH1Cut_tendsto Ψ)
    have h3 : Tendsto (fun n => inner ℝ Y (weakContH1Cut n s)) atTop (𝓝 (inner ℝ Y s)) :=
      tendsto_const_nhds.inner (weakContH1Cut_tendsto s)
    have hall := (h1.sub hflim).sub h3
    rw [hXY] at hall
    have he : inner ℝ Y s - (∫ z, ∑ k : Fin 2, inner ℝ e (F z k) *
        (planeH1GradientOperator Ψ k : Vec 2 → ℝ) z) - inner ℝ Y s =
        -∫ z, ∑ k : Fin 2, inner ℝ e (F z k) *
          (planeH1GradientOperator Ψ k : Vec 2 → ℝ) z := by ring
    rw [he] at hall
    exact hall.congr fun n => (hsplit n).symm
  · intro n
    rw [hsplit n]
    have hA0 : 0 ≤ weakContH1Budget 0 + weakContH1Budget 1 :=
      add_nonneg (weakContH1Budget_nonneg 0) (weakContH1Budget_nonneg 1)
    have h1 : |inner ℝ X (weakContH1Cut n Ψ)| ≤
        (weakContH1Budget 0 + weakContH1Budget 1) * ‖X‖ * ‖Ψ‖ := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      calc ‖X‖ * ‖weakContH1Cut n Ψ‖ ≤ ‖X‖ * ((weakContH1Budget 0 + weakContH1Budget 1) * ‖Ψ‖) :=
            mul_le_mul_of_nonneg_left (weakContH1Cut_norm_apply_le n Ψ) (norm_nonneg _)
        _ = _ := by ring
    have h3 : |inner ℝ Y (weakContH1Cut n s)| ≤
        (weakContH1Budget 0 + weakContH1Budget 1) * ‖Y‖ * ‖s‖ := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      calc ‖Y‖ * ‖weakContH1Cut n s‖ ≤ ‖Y‖ * ((weakContH1Budget 0 + weakContH1Budget 1) * ‖s‖) :=
            mul_le_mul_of_nonneg_left (weakContH1Cut_norm_apply_le n s) (norm_nonneg _)
        _ = _ := by ring
    have h2 := hfb n
    calc |inner ℝ X (weakContH1Cut n Ψ) -
          inner ℝ (planeFluxFiberCoordinateCLM e (Sn n))
            (planeH1GradientOperator (weakContH1Cut n Ψ)) - inner ℝ Y (weakContH1Cut n s)|
        ≤ |inner ℝ X (weakContH1Cut n Ψ)| +
            |inner ℝ (planeFluxFiberCoordinateCLM e (Sn n))
              (planeH1GradientOperator (weakContH1Cut n Ψ))| +
            |inner ℝ Y (weakContH1Cut n s)| := by
          exact (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ _ := add_le_add (add_le_add h1 h2) h3

end FluxTerm

end AVRegularity.CycleWords.Discard
end
end
