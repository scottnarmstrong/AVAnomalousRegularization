-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.TransformBoundCLM
public import AVRegularity.CycleWords.MixedWords.TransformBoundLetterSteps
import Mathlib.Algebra.Ring.IsFormallyReal

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords.Assembly

/-! # the algebra of the same-level transform

The ratio `c_i / c_{i'}` of the stage scales of one component and level, the five shifted moments of
`b1wSameTransform`, and their product `ratio * coefficient = ϖ^{|s|} g` (the scales cancel).  The
result `same_star_eff` writes `ratio * conj T^{same}(conj f)` at a point as five effective real
coefficients times the unscaled operators of order `≤ 1`. -/

section
universe u v

/-- The real ratio `(ϖ^{|β|}/β!) / (ϖ^{|β'|}/β'!)`. -/
def sameRatioReal (ϖ : ℝ) (β β' : ℕ × ℕ) : ℝ :=
  (ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) /
    (ϖ ^ (β'.1 + β'.2) / ((β'.1.factorial * β'.2.factorial : ℕ) : ℝ))

theorem sameRatioReal_shift (ϖ : ℝ) (hϖ : ϖ ≠ 0) (b0 b1 s0 s1 : ℕ) :
    sameRatioReal ϖ (b0 + s0, b1 + s1) (b0, b1) =
      ϖ ^ (s0 + s1) * (((b0.factorial * b1.factorial : ℕ) : ℝ) /
        (((b0 + s0).factorial * (b1 + s1).factorial : ℕ) : ℝ)) := by
  unfold sameRatioReal
  simp only
  have h1 : (b0.factorial * b1.factorial : ℕ) ≠ 0 := by positivity
  have h2 : ((b0 + s0).factorial * (b1 + s1).factorial : ℕ) ≠ 0 := by positivity
  have h1' : (((b0.factorial * b1.factorial : ℕ)) : ℝ) ≠ 0 := by exact_mod_cast h1
  have h2' : ((((b0 + s0).factorial * (b1 + s1).factorial : ℕ)) : ℝ) ≠ 0 := by exact_mod_cast h2
  have hp : ϖ ^ (b0 + b1) ≠ 0 := pow_ne_zero _ hϖ
  have e : ϖ ^ (b0 + s0 + (b1 + s1)) = ϖ ^ (s0 + s1) * ϖ ^ (b0 + b1) := by
    rw [← pow_add]; congr 1; ring
  rw [e]
  field_simp

theorem ratio_alg (p A ϖ F F' : ℝ) (k k' : ℕ) (hp : p ≠ 0) (hA : A ≠ 0) (hϖ : ϖ ≠ 0)
    (hF : F ≠ 0) (hF' : F' ≠ 0) :
    (p * ϖ ^ k / F * A⁻¹) / (p * ϖ ^ k' / F' * A⁻¹) = (ϖ ^ k / F) / (ϖ ^ k' / F') := by
  have h1 : ϖ ^ k' ≠ 0 := pow_ne_zero _ hϖ
  field_simp

/-- A shifted moment term: the coefficient `g κ(m)` times the ratio is `g ϖ^{|s|}` when
`m = b + s`, and `0` otherwise. -/
theorem shift_eff (ϖ : ℝ) (hϖ : ϖ ≠ 0) (s : ℕ × ℕ) (κ : ℕ × ℕ → ℝ) (g : ℝ) (m b : ℕ × ℕ)
    (hκ0 : ∀ m : ℕ × ℕ, ¬ (s.1 ≤ m.1 ∧ s.2 ≤ m.2) → κ m = 0)
    (hκ1 : ∀ b0 b1 : ℕ, κ (b0 + s.1, b1 + s.2) *
      (((b0.factorial * b1.factorial : ℕ) : ℝ) /
        (((b0 + s.1).factorial * (b1 + s.2).factorial : ℕ) : ℝ)) = 1) :
    (if b = (m.1 - s.1, m.2 - s.2) then (g * κ m) * sameRatioReal ϖ m b else 0) =
      if m = (b.1 + s.1, b.2 + s.2) then g * ϖ ^ (s.1 + s.2) else 0 := by
  by_cases hs : s.1 ≤ m.1 ∧ s.2 ≤ m.2
  · obtain ⟨hs1, hs2⟩ := hs
    obtain ⟨b0, b1⟩ := b
    obtain ⟨m0, m1⟩ := m
    simp only at hs1 hs2 ⊢
    by_cases hc : (b0, b1) = (m0 - s.1, m1 - s.2)
    · have hm : (m0, m1) = (b0 + s.1, b1 + s.2) := by
        simp only [Prod.mk.injEq] at hc ⊢
        omega
      rw [ite_eq_left_of_eq_true _ _ (eq_true hc), ite_eq_left_of_eq_true _ _ (eq_true hm)]
      obtain ⟨hm0, hm1⟩ := Prod.mk.injEq _ _ _ _ ▸ hm
      subst hm0 hm1
      rw [sameRatioReal_shift ϖ hϖ]
      have := hκ1 b0 b1
      calc g * κ (b0 + s.1, b1 + s.2) * (ϖ ^ (s.1 + s.2) *
          (((b0.factorial * b1.factorial : ℕ) : ℝ) /
            (((b0 + s.1).factorial * (b1 + s.2).factorial : ℕ) : ℝ)))
          = g * ϖ ^ (s.1 + s.2) * (κ (b0 + s.1, b1 + s.2) *
            (((b0.factorial * b1.factorial : ℕ) : ℝ) /
              (((b0 + s.1).factorial * (b1 + s.2).factorial : ℕ) : ℝ))) := by ring
        _ = g * ϖ ^ (s.1 + s.2) := by rw [this, mul_one]
    · have hm : ¬ (m0, m1) = (b0 + s.1, b1 + s.2) := by
        simp only [Prod.mk.injEq] at hc ⊢
        omega
      rw [ite_eq_right_of_eq_false _ _ (eq_false hc), ite_eq_right_of_eq_false _ _ (eq_false hm)]
  · have h0 := hκ0 m hs
    have hm : ¬ m = (b.1 + s.1, b.2 + s.2) := by
      intro h; apply hs; rw [h]; exact ⟨Nat.le_add_left _ _, Nat.le_add_left _ _⟩
    simp only [hm, ↓reduceIte, h0, mul_zero, zero_mul, ite_self]

theorem term_br (Q ι X : ℝ) (c : Prop) [Decidable c] (W : ℂ) :
    (Q : ℂ) * star ((ι : ℂ) * (if c then (X : ℂ) * W else 0)) =
      ((ι * (if c then Q * X else 0) : ℝ) : ℂ) * star W := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte, star_mul', Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring
  · simp [hc]

section Coef

theorem coef_t1 (ϖ : ℝ) (hϖ : ϖ ≠ 0) (g al : ℝ) (m b : ℕ × ℕ) :
    (if b = (m.1 - 2, m.2) then
        al * sameRatioReal ϖ m b * (g * ((m.1 : ℝ) * ((m.1 : ℝ) - 1))) else 0) =
      al * (if m = (b.1 + 2, b.2 + 0) then g * ϖ ^ (2 + 0) else 0) := by
  have h := shift_eff ϖ hϖ (2, 0) (fun m => (m.1 : ℝ) * ((m.1 : ℝ) - 1)) g m b
    (by
      intro m hm
      have : m.1 < 2 := by
        by_contra hc
        exact hm ⟨by omega, Nat.zero_le _⟩
      interval_cases m.1 <;> simp)
    (by
      intro b0 b1
      simp only [add_zero, Nat.factorial_succ]
      push_cast
      have : (b0.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have : (b1.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      field_simp
      ring)
  simp only [Nat.sub_zero] at h
  calc _ = al * (if b = (m.1 - 2, m.2) then
        (g * ((m.1 : ℝ) * ((m.1 : ℝ) - 1))) * sameRatioReal ϖ m b else 0) := by
        split_ifs <;> ring
    _ = _ := by rw [h]

theorem coef_t2 (ϖ : ℝ) (hϖ : ϖ ≠ 0) (g al : ℝ) (m b : ℕ × ℕ) :
    (if b = (m.1 - 1, m.2 - 1) then
        al * sameRatioReal ϖ m b * (g * ((m.1 : ℝ) * (m.2 : ℝ))) else 0) =
      al * (if m = (b.1 + 1, b.2 + 1) then g * ϖ ^ (1 + 1) else 0) := by
  have h := shift_eff ϖ hϖ (1, 1) (fun m => (m.1 : ℝ) * (m.2 : ℝ)) g m b
    (by
      intro m hm
      have : m.1 = 0 ∨ m.2 = 0 := by
        by_contra hc
        push Not at hc
        exact hm ⟨by omega, by omega⟩
      rcases this with h0 | h0 <;> simp [h0])
    (by
      intro b0 b1
      simp only [Nat.factorial_succ]
      push_cast
      have : (b0.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have : (b1.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      field_simp)
  calc _ = al * (if b = (m.1 - 1, m.2 - 1) then
        (g * ((m.1 : ℝ) * (m.2 : ℝ))) * sameRatioReal ϖ m b else 0) := by
        split_ifs <;> ring
    _ = _ := by rw [h]

theorem coef_t3 (ϖ : ℝ) (hϖ : ϖ ≠ 0) (g al : ℝ) (m b : ℕ × ℕ) :
    (if b = (m.1, m.2 - 2) then
        al * sameRatioReal ϖ m b * (g * ((m.2 : ℝ) * ((m.2 : ℝ) - 1))) else 0) =
      al * (if m = (b.1 + 0, b.2 + 2) then g * ϖ ^ (0 + 2) else 0) := by
  have h := shift_eff ϖ hϖ (0, 2) (fun m => (m.2 : ℝ) * ((m.2 : ℝ) - 1)) g m b
    (by
      intro m hm
      have : m.2 < 2 := by
        by_contra hc
        exact hm ⟨Nat.zero_le _, by omega⟩
      interval_cases m.2 <;> simp)
    (by
      intro b0 b1
      simp only [add_zero, Nat.factorial_succ]
      push_cast
      have : (b0.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have : (b1.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      field_simp
      ring)
  simp only [Nat.sub_zero] at h
  calc _ = al * (if b = (m.1, m.2 - 2) then
        (g * ((m.2 : ℝ) * ((m.2 : ℝ) - 1))) * sameRatioReal ϖ m b else 0) := by
        split_ifs <;> ring
    _ = _ := by rw [h]

theorem coef_t4 (ϖ : ℝ) (hϖ : ϖ ≠ 0) (al : ℝ) (m b : ℕ × ℕ) :
    (if b = (m.1 - 1, m.2) then al * sameRatioReal ϖ m b * (m.1 : ℝ) else 0) =
      al * (if m = (b.1 + 1, b.2 + 0) then 1 * ϖ ^ (1 + 0) else 0) := by
  have h := shift_eff ϖ hϖ (1, 0) (fun m => (m.1 : ℝ)) 1 m b
    (by
      intro m hm
      have : m.1 = 0 := by
        by_contra hc
        exact hm ⟨by omega, Nat.zero_le _⟩
      simp [this])
    (by
      intro b0 b1
      simp only [add_zero, Nat.factorial_succ]
      push_cast
      have : (b0.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have : (b1.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      field_simp)
  simp only [Nat.sub_zero] at h
  calc _ = al * (if b = (m.1 - 1, m.2) then
        (1 * (m.1 : ℝ)) * sameRatioReal ϖ m b else 0) := by
        split_ifs <;> ring
    _ = _ := by rw [h]

theorem coef_t5 (ϖ : ℝ) (hϖ : ϖ ≠ 0) (al : ℝ) (m b : ℕ × ℕ) :
    (if b = (m.1, m.2 - 1) then al * sameRatioReal ϖ m b * (m.2 : ℝ) else 0) =
      al * (if m = (b.1 + 0, b.2 + 1) then 1 * ϖ ^ (0 + 1) else 0) := by
  have h := shift_eff ϖ hϖ (0, 1) (fun m => (m.2 : ℝ)) 1 m b
    (by
      intro m hm
      have : m.2 = 0 := by
        by_contra hc
        exact hm ⟨Nat.zero_le _, by omega⟩
      simp [this])
    (by
      intro b0 b1
      simp only [add_zero, Nat.factorial_succ]
      push_cast
      have : (b0.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have : (b1.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      field_simp)
  simp only [Nat.sub_zero] at h
  calc _ = al * (if b = (m.1, m.2 - 1) then
        (1 * (m.2 : ℝ)) * sameRatioReal ϖ m b else 0) := by
        split_ifs <;> ring
    _ = _ := by rw [h]

end Coef

section SameEff

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- Same level, same component and same basis index. -/
def SameAct (i i' : B1WIndex ι h Nw m Ks) : Prop :=
  i'.1 = i.1 ∧ i.2.1 = i'.2.1 ∧ i.2.2.2.val = i'.2.2.2.val

open Classical in
/-- The effective coefficient of one shifted term. -/
def sameE (al : ℝ) (i i' : B1WIndex ι h Nw m Ks) (s : ℕ × ℕ) (c : ℝ) : ℝ :=
  if SameAct i i' then
    al * (if b1wMom i = ((b1wMom i').1 + s.1, (b1wMom i').2 + s.2) then c else 0)
  else 0

omit [Fintype ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
open Classical in
theorem inner_sameVec (i i' : B1WIndex ι h Nw m Ks) :
    (inner ℝ (b1wSameVec i i') (b1wVec i') : ℝ) =
      if (i.2.1 = i'.2.1 ∧ i.2.2.2.val = i'.2.2.2.val) then 1 else 0 := by
  obtain ⟨j, x, β, b⟩ := i
  obtain ⟨j', x', β', b'⟩ := i'
  by_cases hx : x = x'
  · subst hx
    simp [b1wSameVec, b1wVec, OrthonormalBasis.inner_eq_ite, Fin.ext_iff]
  · simp [b1wSameVec, hx]

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem b1wScaleRatio_same (π : ι → ℝ) (ϖ ηg : ℝ) (letters : Fin Nw → CycleLetter ι h D)
    (hπ : ∀ x, 0 < π x) (hϖ : ϖ ≠ 0) (i i' : B1WIndex ι h Nw m Ks) (hj : i'.1 = i.1)
    (hx : i.2.1 = i'.2.1) :
    b1wScaleRatio π ϖ ηg letters i i' =
      (((if b1wAmp ηg letters i.1 = 0 then 0 else 1) * sameRatioReal ϖ (b1wMom i) (b1wMom i') : ℝ) : ℂ) := by
  unfold b1wScaleRatio b1wScale
  have hA' : b1wAmp ηg letters i'.1 = b1wAmp ηg letters i.1 := by rw [hj]
  have hπ' : π i'.2.1 = π i.2.1 := by rw [hx]
  rw [hA', hπ']
  rw [← Complex.ofReal_div]
  congr 1
  by_cases hA : b1wAmp ηg letters i.1 = 0
  · simp [hA]
  · have hp : π i.2.1 ^ (-(1 / 2 : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos (hπ _) _).ne'
    have hF : (((b1wMom i).1.factorial * (b1wMom i).2.factorial : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (by positivity : (b1wMom i).1.factorial * (b1wMom i).2.factorial ≠ 0)
    have hF' : (((b1wMom i').1.factorial * (b1wMom i').2.factorial : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (by positivity : (b1wMom i').1.factorial * (b1wMom i').2.factorial ≠ 0)
    exact (ratio_alg _ _ _ _ _ _ _ hp hA hϖ hF hF').trans (by simp [hA, sameRatioReal, b1wMom])

/-- `0` if the amplitude `A_j` vanishes (the scales are `0`), else `1`. -/
def sameAlive (ηg : ℝ) (letters : Fin Nw → CycleLetter ι h D)
    (i : B1WIndex ι h Nw m Ks) : ℝ := if b1wAmp ηg letters i.1 = 0 then 0 else 1

theorem split5 (q ι a b c d e : ℂ) :
    q * star (ι * (a + b + c + d + e)) = q * star (ι * a) + q * star (ι * b) + q * star (ι * c) +
      q * star (ι * d) + q * star (ι * e) := by
  simp only [mul_add, star_add]

omit [Fintype ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
open Classical in
theorem same_star_eff (π : ι → ℝ) (ϖ ηg : ℝ) (letters : Fin Nw → CycleLetter ι h D)
    (hπ : ∀ x, 0 < π x) (hϖ : ϖ ≠ 0) (θ : Vec 2) (G : Matrix (Fin 2) (Fin 2) ℝ)
    (vf : Vec 2 → Vec 2) (i i' : B1WIndex ι h Nw m Ks) (f : Vec 2 → ℂ) (z : Vec 2)
    (hf : DifferentiableAt ℝ f z) :
    b1wScaleRatio π ϖ ηg letters i i' *
      star (b1wSameTransform θ G vf i i' (fun y => star (f y)) z) =
    ((sameE (sameAlive ηg letters i) i i' (2, 0) (G 0 0 * ϖ ^ (2 + 0)) +
        sameE (sameAlive ηg letters i) i i' (1, 1) ((G 0 1 + G 1 0) * ϖ ^ (1 + 1)) +
        sameE (sameAlive ηg letters i) i i' (0, 2) (G 1 1 * ϖ ^ (0 + 2)) : ℝ) : ℂ) * f z +
      ((sameE (sameAlive ηg letters i) i i' (1, 0) (1 * ϖ ^ (1 + 0)) : ℝ) : ℂ) *
        ((vf z 0 : ℂ) * f z +
          ∑ k : Fin 2, ((G k 0 + G 0 k : ℝ) : ℂ) * fibreCovDeriv θ k f z) +
      ((sameE (sameAlive ηg letters i) i i' (0, 1) (1 * ϖ ^ (0 + 1)) : ℝ) : ℂ) *
        ((vf z 1 : ℂ) * f z +
          ∑ k : Fin 2, ((G k 1 + G 1 k : ℝ) : ℂ) * fibreCovDeriv θ k f z) := by
  unfold b1wSameTransform
  by_cases hl : i'.1 = i.1
  · by_cases hι : (i.2.1 = i'.2.1 ∧ i.2.2.2.val = i'.2.2.2.val)
    · have hact : SameAct i i' := ⟨hl, hι.1, hι.2⟩
      rw [b1wScaleRatio_same π ϖ ηg letters hπ hϖ i i' hl hι.1, inner_sameVec]
      simp only [hl, hι, and_self, ↓reduceIte]
      have hcov : ∀ k, star (fibreCovDeriv (-θ) k (fun y => star (f y)) z) =
          fibreCovDeriv θ k f z := fun k => tb_star_cov θ k f z hf
      rw [split5, term_br, term_br, term_br, term_br, term_br]
      simp only [star_add, star_mul', star_sum, star_star, hcov]
      simp only [Complex.star_def, Complex.conj_ofReal]
      simp only [sameE, sameAlive, hact, ↓reduceIte]
      rw [coef_t1 ϖ hϖ, coef_t2 ϖ hϖ, coef_t3 ϖ hϖ, coef_t4 ϖ hϖ, coef_t5 ϖ hϖ]
      push_cast
      ring
    · have hnact : ¬ SameAct i i' := fun hh => hι ⟨hh.2.1, hh.2.2⟩
      rw [inner_sameVec]
      simp only [hl, hι, ↓reduceIte, sameE, hnact, Complex.ofReal_zero, zero_mul, mul_zero, star_zero,
        add_zero]
  · have hnact : ¬ SameAct i i' := fun hh => hl hh.1
    simp only [hl, ↓reduceIte, sameE, hnact, star_zero, mul_zero, Complex.ofReal_zero, zero_mul, add_zero]

end SameEff
end

/-! # the scale ratio of a letter pair

For `i` at level `l + 1` and `i'` at level `l` the ratio `c_i / c_{i'}` of `b1wScale` is the
real number `letterRatioReal`: `√(π_{x'}/π_x) ϖ^{|β|-|β'|} (β'!/β!) A_l / A_{l+1}` with
`A_{l+1} = A_l θ_l η_g^{[pos]}` (`b1wAmp`).  It is `0` when `A_l = 0` or `θ_l η_g^{[pos]} = 0`.
`letter_scale_abs_le` bounds its product with the Taylor factor `(ϖ η_g)^s / s!` by
`√(π_{x'}/π_x) β'! / θ_l` whenever the exponent of `ϖ` is nonnegative and `s ≥ [pos]`. -/

section
universe u v

section Ratio

variable {ι : Type u} {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- The factor of the amplitude gained by the letter `l`. -/
def letterFac (ηg : ℝ) (letters : Fin Nw → CycleLetter ι h D) (l : Fin Nw) : ℝ :=
  (letters l).theta * (if (letters l).positive then ηg else 1)

/-- `0` if the amplitude `A_l` vanishes, else `1`. -/
def letterAlive (ηg : ℝ) (letters : Fin Nw → CycleLetter ι h D) (l : Fin Nw) : ℝ :=
  if b1wAmp ηg letters l.castSucc = 0 then 0 else 1

/-- The ratio of the masses `π_x^{-1/2} / π_{x'}^{-1/2}`. -/
def piRatio (π : ι → ℝ) (x x' : ι) : ℝ := π x ^ (-(1 / 2 : ℝ)) / π x' ^ (-(1 / 2 : ℝ))

/-- The real scale ratio of a letter pair. -/
def letterRatioReal (π : ι → ℝ) (ϖ ηg : ℝ) (letters : Fin Nw → CycleLetter ι h D) (l : Fin Nw)
    (x x' : ι) (β β' : ℕ × ℕ) : ℝ :=
  letterAlive ηg letters l * piRatio π x x' * (ϖ ^ (β.1 + β.2) / ϖ ^ (β'.1 + β'.2)) *
    ((((β'.1.factorial * β'.2.factorial : ℕ) : ℝ) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ))) *
    (letterFac ηg letters l)⁻¹

theorem b1wAmp_succ (ηg : ℝ) (letters : Fin Nw → CycleLetter ι h D) (l : Fin Nw) :
    b1wAmp ηg letters l.succ = b1wAmp ηg letters l.castSucc * letterFac ηg letters l := by
  unfold b1wAmp letterFac
  set g : Fin Nw → ℝ := fun l' => (letters l').theta *
    (if (letters l').positive then ηg else 1) with hg
  have key : ∀ l' : Fin Nw, (if l'.val < (l.succ).val then g l' else 1) =
      (if l'.val < (l.castSucc).val then g l' else 1) * (if l' = l then g l' else 1) := by
    intro l'
    by_cases h1 : l' = l
    · subst h1
      simp
    · have h2 : l'.val < l.val + 1 ↔ l'.val < l.val := by
        have : l'.val ≠ l.val := fun e => h1 (Fin.ext e)
        omega
      simp [h1, h2]
  rw [Finset.prod_congr rfl (fun l' _ => key l'), Finset.prod_mul_distrib]
  simp [hg]

omit [∀ i, InnerProductSpace ℝ (h i)] in
theorem inv_prod_ratio (c c' A f : ℝ) :
    (c * (A * f)⁻¹) / (c' * A⁻¹) = (if A = 0 then 0 else 1) * (c / c') * f⁻¹ := by
  by_cases hA : A = 0
  · simp [hA]
  · simp only [hA, ite_false, one_mul, mul_inv]
    field_simp

theorem b1wScaleRatio_letter (π : ι → ℝ) (ϖ ηg : ℝ) (letters : Fin Nw → CycleLetter ι h D)
    (l : Fin Nw) (i i' : B1WIndex ι h Nw m Ks) (hi : i.1 = l.succ) (hi' : i'.1 = l.castSucc) :
    b1wScaleRatio π ϖ ηg letters i i' =
      ((letterRatioReal π ϖ ηg letters l i.2.1 i'.2.1 (b1wMom i) (b1wMom i') : ℝ) : ℂ) := by
  have e1 : b1wAmp ηg letters i.1 = b1wAmp ηg letters l.castSucc * letterFac ηg letters l := by
    rw [hi, b1wAmp_succ]
  have e2 : b1wAmp ηg letters i'.1 = b1wAmp ηg letters l.castSucc := by rw [hi']
  unfold b1wScaleRatio b1wScale
  rw [e1, e2, ← Complex.ofReal_div]
  congr 1
  rw [inv_prod_ratio]
  unfold letterRatioReal piRatio letterAlive
  by_cases hA : b1wAmp ηg letters l.castSucc = 0
  · simp [hA]
  · simp only [hA, ite_false, b1wMom]
    simp only [div_eq_mul_inv, mul_inv, inv_inv]
    ring

omit [∀ i, InnerProductSpace ℝ (h i)] in
theorem piRatio_eq_sqrt (π : ι → ℝ) (x x' : ι) (hx : 0 < π x) (hx' : 0 < π x') :
    piRatio π x x' = Real.sqrt (π x' / π x) := by
  unfold piRatio
  rw [Real.sqrt_div hx'.le, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.rpow_neg hx.le,
    Real.rpow_neg hx'.le]
  have h1 : 0 < π x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx _
  have h2 : 0 < π x' ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx' _
  field_simp

theorem pow_ratio_mul (ϖ : ℝ) (hϖ : 0 < ϖ) (A B s E : ℕ) (h : A + s = B + E) :
    ϖ ^ A / ϖ ^ B * ϖ ^ s = ϖ ^ E := by
  have : ϖ ^ A * ϖ ^ s = ϖ ^ B * ϖ ^ E := by rw [← pow_add, ← pow_add, h]
  have hB : ϖ ^ B ≠ 0 := (pow_pos hϖ B).ne'
  field_simp
  exact this

omit [∀ i, InnerProductSpace ℝ (h i)] in
theorem eta_fac_le (ηg θ : ℝ) (pos : Bool) (s : ℕ) (hg0 : 0 < ηg) (hg1 : ηg ≤ 1) (hθ : 0 < θ)
    (hs : (if pos then 1 else 0) ≤ s) :
    0 ≤ ηg ^ s * (θ * (if pos then ηg else 1))⁻¹ ∧
      ηg ^ s * (θ * (if pos then ηg else 1))⁻¹ ≤ θ⁻¹ := by
  cases pos
  · simp only [Bool.false_eq_true, ite_false, mul_one]
    refine ⟨by positivity, ?_⟩
    rw [← div_eq_mul_inv, ← one_div, div_le_div_iff_of_pos_right hθ]
    exact pow_le_one₀ hg0.le hg1
  · simp only [ite_true] at hs ⊢
    obtain ⟨e, rfl⟩ : ∃ e, s = e + 1 := ⟨s - 1, by omega⟩
    have : ηg ^ (e + 1) * (θ * ηg)⁻¹ = ηg ^ e * θ⁻¹ := by
      field_simp
      ring
    rw [this]
    refine ⟨by positivity, ?_⟩
    exact mul_le_of_le_one_left (inv_nonneg.2 hθ.le) (pow_le_one₀ hg0.le hg1)

theorem letter_scale_abs_le (π : ι → ℝ) (ϖ ηg : ℝ) (letters : Fin Nw → CycleLetter ι h D)
    (l : Fin Nw) (x x' : ι) (β β' β0 a : ℕ × ℕ) (s : ℕ)
    (hx : 0 < π x) (hx' : 0 < π x') (hϖ0 : 0 < ϖ) (hϖ1 : ϖ ≤ 1) (hg0 : 0 < ηg) (hg1 : ηg ≤ 1)
    (hθ : 0 < (letters l).theta) (hs : (if (letters l).positive then 1 else 0) ≤ s)
    (hexp : β'.1 + β'.2 + (a.1 + a.2) = β0.1 + β0.2 + s) (hb0 : β0.1 + β0.2 ≤ β.1 + β.2) :
    |letterRatioReal π ϖ ηg letters l x x' β β' * ((ϖ * ηg) ^ s / (s.factorial : ℝ))| ≤
      Real.sqrt (π x' / π x) * ((β'.1.factorial * β'.2.factorial : ℕ) : ℝ) / (letters l).theta := by
  have hE := pow_ratio_mul ϖ hϖ0 (β.1 + β.2) (β'.1 + β'.2) s (β.1 + β.2 - (β0.1 + β0.2) + (a.1 + a.2))
    (by omega)
  have hEle : ϖ ^ (β.1 + β.2 - (β0.1 + β0.2) + (a.1 + a.2)) ≤ 1 := pow_le_one₀ hϖ0.le hϖ1
  obtain ⟨hf0, hf1⟩ := eta_fac_le ηg (letters l).theta (letters l).positive s hg0 hg1 hθ hs
  have hF : (1 : ℝ) ≤ ((β.1.factorial * β.2.factorial : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (by positivity)
  have hF' : (0 : ℝ) ≤ ((β'.1.factorial * β'.2.factorial : ℕ) : ℝ) := Nat.cast_nonneg _
  have hsf : (1 : ℝ) ≤ (s.factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (by positivity)
  have hal : letterAlive ηg letters l = 0 ∨ letterAlive ηg letters l = 1 := by
    unfold letterAlive; split_ifs <;> simp
  have hsq : 0 ≤ Real.sqrt (π x' / π x) := Real.sqrt_nonneg _
  have eq : letterRatioReal π ϖ ηg letters l x x' β β' * ((ϖ * ηg) ^ s / (s.factorial : ℝ)) =
      letterAlive ηg letters l * Real.sqrt (π x' / π x) *
        (ϖ ^ (β.1 + β.2 - (β0.1 + β0.2) + (a.1 + a.2)) *
          (((β'.1.factorial * β'.2.factorial : ℕ) : ℝ) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) *
          (ηg ^ s * (letterFac ηg letters l)⁻¹) / (s.factorial : ℝ)) := by
    unfold letterRatioReal
    rw [piRatio_eq_sqrt π x x' hx hx', ← hE, mul_pow]
    unfold letterFac
    ring
  rw [eq]
  have hq : 0 ≤ ϖ ^ (β.1 + β.2 - (β0.1 + β0.2) + (a.1 + a.2)) *
          (((β'.1.factorial * β'.2.factorial : ℕ) : ℝ) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) *
          (ηg ^ s * (letterFac ηg letters l)⁻¹) / (s.factorial : ℝ) := by
    have := pow_nonneg hϖ0.le (β.1 + β.2 - (β0.1 + β0.2) + (a.1 + a.2))
    positivity
  rw [abs_mul, abs_mul, abs_of_nonneg hsq, abs_of_nonneg hq]
  have hal1 : |letterAlive ηg letters l| ≤ 1 := by rcases hal with h | h <;> simp [h]
  have hq1 : ϖ ^ (β.1 + β.2 - (β0.1 + β0.2) + (a.1 + a.2)) *
          (((β'.1.factorial * β'.2.factorial : ℕ) : ℝ) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) *
          (ηg ^ s * (letterFac ηg letters l)⁻¹) / (s.factorial : ℝ) ≤
        ((β'.1.factorial * β'.2.factorial : ℕ) : ℝ) / (letters l).theta := by
    have hd : (((β'.1.factorial * β'.2.factorial : ℕ) : ℝ) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ))
        ≤ ((β'.1.factorial * β'.2.factorial : ℕ) : ℝ) := div_le_self hF' hF
    have hdn : 0 ≤ (((β'.1.factorial * β'.2.factorial : ℕ) : ℝ) /
        ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) := by positivity
    have hp0 := pow_nonneg hϖ0.le (β.1 + β.2 - (β0.1 + β0.2) + (a.1 + a.2))
    calc _ ≤ ϖ ^ (β.1 + β.2 - (β0.1 + β0.2) + (a.1 + a.2)) *
          (((β'.1.factorial * β'.2.factorial : ℕ) : ℝ) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) *
          (ηg ^ s * (letterFac ηg letters l)⁻¹) := div_le_self (by positivity) hsf
      _ ≤ 1 * ((β'.1.factorial * β'.2.factorial : ℕ) : ℝ) * (letters l).theta⁻¹ := by
          have h1 : ηg ^ s * (letterFac ηg letters l)⁻¹ ≤ (letters l).theta⁻¹ := hf1
          have h2 : ηg ^ s * (letterFac ηg letters l)⁻¹ ≥ 0 := hf0
          gcongr
      _ = _ := by rw [one_mul, div_eq_mul_inv]
  calc |letterAlive ηg letters l| * Real.sqrt (π x' / π x) * _ ≤
      1 * Real.sqrt (π x' / π x) * (((β'.1.factorial * β'.2.factorial : ℕ) : ℝ) /
        (letters l).theta) := by gcongr
    _ = _ := by ring

end Ratio
end

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # the same-level operators and the same-level transform bound

Proof of `SameLevelOpsStatement` and hence of `sameLevelTransformBound`.  For a pair of
stages `(i, i')` the operator is the real-linear map `sameOp` of `H^N`: the constant `e₁₂₃` times the
truncation, and `e₄`, `e₅` times the drift multiplier by `v₀`, `v₁` (bounded through
`ϖ ‖D^l v‖ ≤ C_{vj}(l)`, the jets of `√η v` and `ϖ ≤ √η`) plus the twisted derivatives with the
coefficients `G_{k0} + G_{0k}`, `G_{k1} + G_{1k}` of the cell metric.  The effective coefficients
come from `same_star_eff` (the scales cancel against the moment factors). -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
  AVRegularity.CycleEvolution

namespace AVRegularity.CycleWords.Assembly

universe u v


theorem metric_sum_le (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hM : ∀ ξ : Vec 2, 1 / 2 * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, ξ i * M i j * ξ j ∧
      ∑ i, ∑ j, ξ i * M i j * ξ j ≤ 2 * ∑ i, ξ i ^ 2) (j k : Fin 2) :
    |M j k + M k j| ≤ 4 := by
  have h0 := hM ![1, 0]
  have h1 := hM ![0, 1]
  have h2 := hM ![1, 1]
  simp [Fin.sum_univ_two] at h0 h1 h2
  rw [abs_le]
  fin_cases j <;> fin_cases k <;> simp <;> constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]

theorem drift_comp_jet {K : ScalarConstants} {η S ϖ : ℝ} (hη : 0 < η) (hS : 1 ≤ S)
    (hϖ : ϖ = Real.sqrt (η / S)) (v : Vec 2 → Vec 2) (hvs : ContDiff ℝ (⊤ : ℕ∞) v)
    (hvj : ∀ (j : ℕ) z, ‖iteratedFDeriv ℝ j (fun z' => Real.sqrt η • v z') z‖ ≤ K.Cvj j)
    (c : Fin 2) (l : ℕ) (x : Vec 2) :
    ϖ * ‖iteratedFDeriv ℝ l (fun y => v y c) x‖ ≤ K.Cvj l := by
  have hvl : ContDiff ℝ (l : ℕ) v := hvs.of_le (by simp)
  let g : Vec 2 →L[ℝ] ℝ := ContinuousLinearMap.proj c
  have hg : ‖g‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun y => by simpa [g] using norm_le_pi_norm y c)
  have hj := g.norm_iteratedFDeriv_comp_left (x := x) hvl.contDiffAt le_rfl
  have hc : (fun y => v y c) = g ∘ v := rfl
  have hle : ϖ ≤ Real.sqrt η := by
    rw [hϖ]
    exact Real.sqrt_le_sqrt (div_le_self hη.le hS)
  have hs := hvj l x
  rw [iteratedFDeriv_const_smul_apply' hvl.contDiffAt, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hs
  have h1 : ‖iteratedFDeriv ℝ l (fun y => v y c) x‖ ≤ ‖iteratedFDeriv ℝ l v x‖ := by
    rw [hc]
    exact hj.trans (by nlinarith [norm_nonneg (iteratedFDeriv ℝ l v x)])
  calc ϖ * ‖iteratedFDeriv ℝ l (fun y => v y c) x‖ ≤ Real.sqrt η * ‖iteratedFDeriv ℝ l v x‖ :=
        mul_le_mul hle h1 (norm_nonneg _) (Real.sqrt_nonneg _)
    _ ≤ K.Cvj l := hs

theorem value_comb {n : ℕ} (U V W : TorusHk n ℂ) (a b c : ℝ) (f g h : Vec 2 → ℂ)
    (hU : (torusHkValueCLM U : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] f)
    (hV : (torusHkValueCLM V : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] g)
    (hW : (torusHkValueCLM W : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] h) :
    (torusHkValueCLM (a • U + b • V + c • W) : Vec 2 → ℂ)
      =ᵐ[volume.restrict AVenhance.unitCube] fun z => (a : ℂ) * f z + (b : ℂ) * g z + (c : ℂ) * h z := by
  rw [map_add, map_add, map_smul, map_smul, map_smul]
  filter_upwards [Lp.coeFn_add (a • torusHkValueCLM U + b • torusHkValueCLM V) (c • torusHkValueCLM W),
    Lp.coeFn_add (a • torusHkValueCLM U) (b • torusHkValueCLM V),
    Lp.coeFn_smul a (torusHkValueCLM U), Lp.coeFn_smul b (torusHkValueCLM V),
    Lp.coeFn_smul c (torusHkValueCLM W), hU, hV, hW] with z h1 h2 h3 h4 h5 h6 h7 h8
  rw [h1, Pi.add_apply, h2, Pi.add_apply, h3, h4, h5]
  simp only [Pi.smul_apply, h6, h7, h8, Complex.real_smul]

theorem drift_mul_exists (K : ScalarConstants) {η S ϖ : ℝ} (hη : 0 < η) (hS : 1 ≤ S)
    (hϖ : ϖ = Real.sqrt (η / S)) (n : ℕ) (v : Vec 2 → Vec 2)
    (hvs : ContDiff ℝ (⊤ : ℕ∞) v) (hper : AVenhance.IsZ2Periodic v)
    (hvj : ∀ (j : ℕ) z, ‖iteratedFDeriv ℝ j (fun z' => Real.sqrt η • v z') z‖ ≤ K.Cvj j) :
    ∃ M : Fin 2 → TorusHk n ℂ →L[ℝ] TorusHk n ℂ,
      (∀ c U, ‖M c U‖ ≤ (|cellDriftNativePrice n| *
        ((∑ l ∈ Finset.range (n + 1), |K.Cvj l|) / ϖ)) * ‖U‖) ∧
      ∀ c U, (torusHkValueCLM (M c U) : Vec 2 → ℂ)
        =ᵐ[volume.restrict AVenhance.unitCube] fun x => (v x c : ℂ) * torusHkValueCLM U x := by
  have hϖpos : 0 < ϖ := by
    rw [hϖ]; exact Real.sqrt_pos.2 (div_pos hη (by linarith))
  have hvl : ContDiff ℝ (n : ℕ) v := hvs.of_le (by simp)
  have hcomp : ∀ c : Fin 2, ContDiff ℝ (n : ℕ) (fun x => v x c) := fun c =>
    (contDiff_apply ℝ ℝ c).comp hvl
  have hper' : ∀ c : Fin 2, AVenhance.IsZ2Periodic (fun x => v x c) := by
    intro c k x
    simp only [hper k x]
  have hP : ∀ c : Fin 2, ∀ l ≤ n, ∀ x, ‖iteratedFDeriv ℝ l (fun y => v y c) x‖ ≤
      (∑ l ∈ Finset.range (n + 1), |K.Cvj l|) / ϖ := by
    intro c l hl x
    rw [le_div_iff₀ hϖpos, mul_comm]
    refine (drift_comp_jet hη hS hϖ v hvs hvj c l x).trans ?_
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun l => |K.Cvj l|)
      (fun l _ => abs_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hl)))
  refine ⟨fun c => tbMulCLM n (hcomp c) (hper' c) (hP c), fun c U => ?_, fun c U => ?_⟩
  · refine (tbMulCLM_norm_le n (hcomp c) (hper' c) (hP c) U).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (div_nonneg
      (Finset.sum_nonneg fun l _ => abs_nonneg _) hϖpos.le)
  · exact tbMulCLM_value_ae n (hcomp c) (hper' c) (hP c) U

theorem value_smul_ae {n : ℕ} (U : TorusHk n ℂ) (a : ℝ) (f : Vec 2 → ℂ)
    (hU : (torusHkValueCLM U : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] f) :
    (torusHkValueCLM (a • U) : Vec 2 → ℂ)
      =ᵐ[volume.restrict AVenhance.unitCube] fun z => (a : ℂ) * f z := by
  rw [map_smul]
  filter_upwards [Lp.coeFn_smul a (torusHkValueCLM U), hU] with z h1 h2
  rw [h1]
  simp only [Pi.smul_apply, h2, Complex.real_smul]

theorem value_bracket_ae {n : ℕ} (M : TorusHk n ℂ) (W : Fin 2 → TorusHk n ℂ) (a : Fin 2 → ℝ)
    (g : Vec 2 → ℂ) (c : Fin 2 → Vec 2 → ℂ)
    (hM : (torusHkValueCLM M : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] g)
    (hW : ∀ k, (torusHkValueCLM (W k) : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] c k) :
    (torusHkValueCLM (M + ∑ k, a k • W k) : Vec 2 → ℂ)
      =ᵐ[volume.restrict AVenhance.unitCube] fun z => g z + ∑ k, (a k : ℂ) * c k z := by
  rw [map_add]
  filter_upwards [Lp.coeFn_add (torusHkValueCLM M) (torusHkValueCLM (∑ k, a k • W k)),
    torusHk_value_sum_ae Finset.univ (fun k => a k • W k) (fun k z => (a k : ℂ) * c k z)
      (fun k _ => value_smul_ae (W k) (a k) (c k) (hW k)), hM] with z h1 h2 h3
  rw [h1, Pi.add_apply, h2, h3]

theorem theta_abs_le {η ρ : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (θ : Vec 2)
    (h : fibreNorm (planeFibreFrequency η θ) ≤ ρ) (k : Fin 2) : |θ k| ≤ ρ := by
  refine le_trans ?_ h
  unfold fibreNorm planeFibreFrequency
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.2 hη
  have hs1 : Real.sqrt η ≤ 1 := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hη1
  have h1 : |θ k| ≤ |θ k| / Real.sqrt η := by
    rw [le_div_iff₀ hs]; nlinarith [abs_nonneg (θ k)]
  refine h1.trans (Real.le_sqrt_of_sq_le ?_)
  have := Finset.single_le_sum (f := fun i : Fin 2 => ‖(((θ i / Real.sqrt η : ℝ)) : ℂ)‖ ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ k)
  simpa [Complex.norm_real, div_pow, sq_abs] using this

section
variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem sameAlive_abs_le (ηg : ℝ) (letters : Fin Nw → CycleLetter ι h D)
    (i : B1WIndex ι h Nw m Ks) : |sameAlive ηg letters i| ≤ 1 := by
  unfold sameAlive; split_ifs <;> simp

open Classical in
omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem sameE_abs_le (al : ℝ) (hal : |al| ≤ 1) (i i' : B1WIndex ι h Nw m Ks) (s : ℕ × ℕ)
    (c : ℝ) : |sameE al i i' s c| ≤ |c| := by
  unfold sameE
  split_ifs
  · rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right hal (abs_nonneg _)).trans_eq (one_mul _)
  all_goals simp

open Classical in
omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem sameE_eq_zero_of_not_rel (al : ℝ) (i i' : B1WIndex ι h Nw m Ks) (hn : ¬ SameRel i i')
    (s : ℕ × ℕ) (hs : s ∈ sameShifts) (c : ℝ) : sameE al i i' s c = 0 := by
  unfold sameE
  split_ifs with h1 h2
  · exact absurd ⟨h1.1.symm, h1.2.1, h1.2.2, s, hs, h2⟩ hn
  · simp
  · rfl

end

/-- The same-level operator: the three constants times the truncation, and `e₄`, `e₅` times the
drift multiplier and the twisted derivatives. -/
def sameOp (n N : ℕ) (hnN : n + 1 ≤ N) (θ : Vec 2)
    (M : Fin 2 → TorusHk n ℂ →L[ℝ] TorusHk n ℂ) (a4 a5 : Fin 2 → ℝ) (e123 e4 e5 : ℝ) :
    TorusHk N ℂ →L[ℝ] TorusHk n ℂ :=
  e123 • truncateTorusHk (by omega : n ≤ N) +
    e4 • ((M 0).comp (truncateTorusHk (by omega : n ≤ N)) +
      (a4 0 • (tbTwist n θ 0).comp (truncateTorusHk hnN) +
        a4 1 • (tbTwist n θ 1).comp (truncateTorusHk hnN))) +
    e5 • ((M 1).comp (truncateTorusHk (by omega : n ≤ N)) +
      (a5 0 • (tbTwist n θ 0).comp (truncateTorusHk hnN) +
        a5 1 • (tbTwist n θ 1).comp (truncateTorusHk hnN)))

theorem sameOp_value (n N : ℕ) (hnN : n + 1 ≤ N) (h3 : 3 ≤ N) (θ : Vec 2)
    (M : Fin 2 → TorusHk n ℂ →L[ℝ] TorusHk n ℂ) (v : Vec 2 → Vec 2)
    (hMv : ∀ c U, (torusHkValueCLM (M c U) : Vec 2 → ℂ)
      =ᵐ[volume.restrict AVenhance.unitCube] fun x => (v x c : ℂ) * torusHkValueCLM U x)
    (a4 a5 : Fin 2 → ℝ) (e123 e4 e5 : ℝ) (ψ : TorusHk N ℂ) :
    (torusHkValueCLM (sameOp n N hnN θ M a4 a5 e123 e4 e5 ψ) : Vec 2 → ℂ)
      =ᵐ[volume.restrict AVenhance.unitCube] fun z =>
        (e123 : ℂ) * torusHigherClassicalValue N ψ z +
          (e4 : ℂ) * ((v z 0 : ℂ) * torusHigherClassicalValue N ψ z +
            ((a4 0 : ℂ) * fibreCovDeriv θ 0 (torusHigherClassicalValue N ψ) z +
              (a4 1 : ℂ) * fibreCovDeriv θ 1 (torusHigherClassicalValue N ψ) z)) +
          (e5 : ℂ) * ((v z 1 : ℂ) * torusHigherClassicalValue N ψ z +
            ((a5 0 : ℂ) * fibreCovDeriv θ 0 (torusHigherClassicalValue N ψ) z +
              (a5 1 : ℂ) * fibreCovDeriv θ 1 (torusHigherClassicalValue N ψ) z)) := by
  have hf1 : ContDiff ℝ 1 (torusHigherClassicalValue N ψ) := by
    have := torusHigherClassicalValue_contDiff N 1 (by omega) ψ
    exact_mod_cast this
  have hval : (torusHkValueCLM ψ : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      torusHigherClassicalValue N ψ := (torusHigherClassicalValue_ae N (by omega) ψ).symm
  have hvtr : (torusHkValueCLM (truncateTorusHk (by omega : n ≤ N) ψ) : Vec 2 → ℂ)
      =ᵐ[volume.restrict AVenhance.unitCube] torusHigherClassicalValue N ψ := hval
  have hvtr1 : (torusHkValueCLM (truncateTorusHk hnN ψ) : Vec 2 → ℂ)
      =ᵐ[volume.restrict AVenhance.unitCube] torusHigherClassicalValue N ψ := hval
  have hcov : ∀ k, (torusHkValueCLM (tbTwist n θ k (truncateTorusHk hnN ψ)) : Vec 2 → ℂ)
      =ᵐ[volume.restrict AVenhance.unitCube] fibreCovDeriv θ k (torusHigherClassicalValue N ψ) :=
    fun k => tbTwist_value_ae n θ k (truncateTorusHk hnN ψ) _ hf1 hvtr1
  have hmul : ∀ c, (torusHkValueCLM (M c (truncateTorusHk (by omega : n ≤ N) ψ)) : Vec 2 → ℂ)
      =ᵐ[volume.restrict AVenhance.unitCube]
        fun x => (v x c : ℂ) * torusHigherClassicalValue N ψ x := fun c => by
    filter_upwards [hMv c (truncateTorusHk (by omega : n ≤ N) ψ), hvtr] with x h1 h2
    rw [h1, h2]
  have h4 := value_bracket_ae _ (fun k => tbTwist n θ k (truncateTorusHk hnN ψ)) a4 _ _
    (hmul 0) hcov
  have h5 := value_bracket_ae _ (fun k => tbTwist n θ k (truncateTorusHk hnN ψ)) a5 _ _
    (hmul 1) hcov
  simp only [Fin.sum_univ_two] at h4 h5
  exact value_comb _ _ _ e123 e4 e5 _ _ _ hvtr h4 h5

theorem sameOp_bracket_norm (n N : ℕ) (hnN : n + 1 ≤ N) (θ : Vec 2)
    (M : Fin 2 → TorusHk n ℂ →L[ℝ] TorusHk n ℂ) (c : Fin 2) (a : Fin 2 → ℝ)
    (B ρ : ℝ) (hB : 0 ≤ B) (hMB : ∀ c U, ‖M c U‖ ≤ B * ‖U‖)
    (ha : ∀ k, |a k| ≤ 4) (hθ : ∀ k, |θ k| ≤ ρ) (ψ : TorusHk N ℂ) :
    ‖M c (truncateTorusHk (by omega : n ≤ N) ψ) +
      (a 0 • tbTwist n θ 0 (truncateTorusHk hnN ψ) +
        a 1 • tbTwist n θ 1 (truncateTorusHk hnN ψ))‖ ≤ (B + 8 * (1 + ρ)) * ‖ψ‖ := by
  have hn1 : ‖truncateTorusHk (by omega : n ≤ N) ψ‖ ≤ ‖ψ‖ := truncateTorusHk_norm_le _ ψ
  have hn2 : ‖truncateTorusHk hnN ψ‖ ≤ ‖ψ‖ := truncateTorusHk_norm_le _ ψ
  have hk : ∀ k, ‖a k • tbTwist n θ k (truncateTorusHk hnN ψ)‖ ≤ 4 * (1 + ρ) * ‖ψ‖ := by
    intro k
    rw [norm_smul, Real.norm_eq_abs]
    have h1 : ‖tbTwist n θ k (truncateTorusHk hnN ψ)‖ ≤ (1 + ρ) * ‖ψ‖ :=
      ((tbTwist n θ k).le_opNorm _).trans
        (mul_le_mul (((tbTwist_norm_le n θ k)).trans (by linarith [hθ k])) hn2
          (norm_nonneg _) (by linarith [(abs_nonneg _).trans (hθ k)]))
    calc |a k| * ‖tbTwist n θ k (truncateTorusHk hnN ψ)‖ ≤ 4 * ((1 + ρ) * ‖ψ‖) :=
          mul_le_mul (ha k) h1 (norm_nonneg _) (by norm_num)
      _ = 4 * (1 + ρ) * ‖ψ‖ := by ring
  calc ‖M c (truncateTorusHk (by omega : n ≤ N) ψ) +
        (a 0 • tbTwist n θ 0 (truncateTorusHk hnN ψ) +
          a 1 • tbTwist n θ 1 (truncateTorusHk hnN ψ))‖
      ≤ ‖M c (truncateTorusHk (by omega : n ≤ N) ψ)‖ +
        (‖a 0 • tbTwist n θ 0 (truncateTorusHk hnN ψ)‖ +
          ‖a 1 • tbTwist n θ 1 (truncateTorusHk hnN ψ)‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ B * ‖ψ‖ + (4 * (1 + ρ) * ‖ψ‖ + 4 * (1 + ρ) * ‖ψ‖) :=
        add_le_add ((hMB c _).trans (mul_le_mul_of_nonneg_left hn1 hB))
          (add_le_add (hk 0) (hk 1))
    _ = (B + 8 * (1 + ρ)) * ‖ψ‖ := by ring

theorem sameOp_norm_le (n N : ℕ) (hnN : n + 1 ≤ N) (θ : Vec 2)
    (M : Fin 2 → TorusHk n ℂ →L[ℝ] TorusHk n ℂ) (a4 a5 : Fin 2 → ℝ) (e123 e4 e5 : ℝ)
    (B ρ : ℝ) (hB : 0 ≤ B) (hMB : ∀ c U, ‖M c U‖ ≤ B * ‖U‖)
    (ha4 : ∀ k, |a4 k| ≤ 4) (ha5 : ∀ k, |a5 k| ≤ 4) (hθ : ∀ k, |θ k| ≤ ρ) (ψ : TorusHk N ℂ) :
    ‖sameOp n N hnN θ M a4 a5 e123 e4 e5 ψ‖ ≤
      (|e123| + |e4| * (B + 8 * (1 + ρ)) + |e5| * (B + 8 * (1 + ρ))) * ‖ψ‖ := by
  have hn1 : ‖truncateTorusHk (by omega : n ≤ N) ψ‖ ≤ ‖ψ‖ := truncateTorusHk_norm_le _ ψ
  have hb4 := sameOp_bracket_norm n N hnN θ M 0 a4 B ρ hB hMB ha4 hθ ψ
  have hb5 := sameOp_bracket_norm n N hnN θ M 1 a5 B ρ hB hMB ha5 hθ ψ
  have hap : sameOp n N hnN θ M a4 a5 e123 e4 e5 ψ =
      e123 • truncateTorusHk (by omega : n ≤ N) ψ +
      e4 • (M 0 (truncateTorusHk (by omega : n ≤ N) ψ) +
        (a4 0 • tbTwist n θ 0 (truncateTorusHk hnN ψ) +
          a4 1 • tbTwist n θ 1 (truncateTorusHk hnN ψ))) +
      e5 • (M 1 (truncateTorusHk (by omega : n ≤ N) ψ) +
        (a5 0 • tbTwist n θ 0 (truncateTorusHk hnN ψ) +
          a5 1 • tbTwist n θ 1 (truncateTorusHk hnN ψ))) := rfl
  rw [hap]
  calc _ ≤ ‖e123 • truncateTorusHk (by omega : n ≤ N) ψ‖ +
        ‖e4 • (M 0 (truncateTorusHk (by omega : n ≤ N) ψ) +
          (a4 0 • tbTwist n θ 0 (truncateTorusHk hnN ψ) +
            a4 1 • tbTwist n θ 1 (truncateTorusHk hnN ψ)))‖ +
        ‖e5 • (M 1 (truncateTorusHk (by omega : n ≤ N) ψ) +
          (a5 0 • tbTwist n θ 0 (truncateTorusHk hnN ψ) +
            a5 1 • tbTwist n θ 1 (truncateTorusHk hnN ψ)))‖ := norm_add₃_le
    _ ≤ |e123| * ‖ψ‖ + |e4| * ((B + 8 * (1 + ρ)) * ‖ψ‖) + |e5| * ((B + 8 * (1 + ρ)) * ‖ψ‖) := by
        refine add_le_add (add_le_add ?_ ?_) ?_
        · exact (norm_smul_le _ _).trans (by
            rw [Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left hn1 (abs_nonneg _))
        · exact (norm_smul_le _ _).trans (by
            rw [Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left hb4 (abs_nonneg _))
        · exact (norm_smul_le _ _).trans (by
            rw [Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left hb5 (abs_nonneg _))
    _ = _ := by ring

section Main
variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- The constant coefficient of the three zeroth-order terms. -/
def sameE123 (al ϖ : ℝ) (G : Matrix (Fin 2) (Fin 2) ℝ) (i i' : B1WIndex ι h Nw m Ks) : ℝ :=
  sameE al i i' (2, 0) (G 0 0 * ϖ ^ (2 + 0)) +
    sameE al i i' (1, 1) ((G 0 1 + G 1 0) * ϖ ^ (1 + 1)) +
    sameE al i i' (0, 2) (G 1 1 * ϖ ^ (0 + 2))

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem sameE123_abs_le (al ϖ : ℝ) (hal : |al| ≤ 1) (hϖ0 : 0 ≤ ϖ) (hϖ1 : ϖ ≤ 1)
    (G : Matrix (Fin 2) (Fin 2) ℝ) (h00 : |G 0 0| ≤ 2) (h11 : |G 1 1| ≤ 2)
    (h01 : |G 0 1 + G 1 0| ≤ 4) (i i' : B1WIndex ι h Nw m Ks) : |sameE123 al ϖ G i i'| ≤ 8 := by
  unfold sameE123
  have hp : ∀ k : ℕ, |ϖ ^ k| ≤ 1 := fun k => by
    rw [abs_of_nonneg (pow_nonneg hϖ0 k)]; exact pow_le_one₀ hϖ0 hϖ1
  have b1 := sameE_abs_le al hal i i' (2, 0) (G 0 0 * ϖ ^ (2 + 0))
  have b2 := sameE_abs_le al hal i i' (1, 1) ((G 0 1 + G 1 0) * ϖ ^ (1 + 1))
  have b3 := sameE_abs_le al hal i i' (0, 2) (G 1 1 * ϖ ^ (0 + 2))
  rw [abs_mul] at b1 b2 b3
  have c1 := mul_le_mul h00 (hp (2 + 0)) (abs_nonneg _) (by norm_num)
  have c2 := mul_le_mul h01 (hp (1 + 1)) (abs_nonneg _) (by norm_num)
  have c3 := mul_le_mul h11 (hp (0 + 2)) (abs_nonneg _) (by norm_num)
  calc _ ≤ |sameE al i i' (2, 0) (G 0 0 * ϖ ^ (2 + 0)) +
        sameE al i i' (1, 1) ((G 0 1 + G 1 0) * ϖ ^ (1 + 1))| +
        |sameE al i i' (0, 2) (G 1 1 * ϖ ^ (0 + 2))| := abs_add_le _ _
    _ ≤ |sameE al i i' (2, 0) (G 0 0 * ϖ ^ (2 + 0))| +
        |sameE al i i' (1, 1) ((G 0 1 + G 1 0) * ϖ ^ (1 + 1))| +
        |sameE al i i' (0, 2) (G 1 1 * ϖ ^ (0 + 2))| := by gcongr; exact abs_add_le _ _
    _ ≤ 8 := by linarith

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem sameE123_eq_zero (al ϖ : ℝ) (G : Matrix (Fin 2) (Fin 2) ℝ) (i i' : B1WIndex ι h Nw m Ks)
    (hn : ¬ SameRel i i') : sameE123 al ϖ G i i' = 0 := by
  unfold sameE123
  rw [sameE_eq_zero_of_not_rel al i i' hn _ (by simp [sameShifts]),
    sameE_eq_zero_of_not_rel al i i' hn _ (by simp [sameShifts]),
    sameE_eq_zero_of_not_rel al i i' hn _ (by simp [sameShifts])]
  simp

end Main

theorem sameLevelOps : SameLevelOpsStatement.{u, v} := by
  classical
  intro K Nw D m d Ks ρ n
  refine ⟨8 + 2 * (|cellDriftNativePrice n| * (∑ l ∈ Finset.range (n + 1), |K.Cvj l|) +
    8 * (1 + |ρ|)), by positivity, ?_⟩
  intro g₁ ι _ h _ _ _ _ _ _ F θ hρ r hr N hnN hdN i i'
  have hη := F.piece.hη
  have hη1 := F.piece.hη1
  have hS := F.piece.hS
  have hϖ := F.piece.hϖ
  have hϖpos : 0 < F.ϖ := by
    rw [hϖ]; exact Real.sqrt_pos.2 (div_pos hη (by linarith))
  have hϖ1 : F.ϖ ≤ 1 := by
    rw [hϖ, ← Real.sqrt_one]
    exact Real.sqrt_le_sqrt ((div_le_self hη.le hS).trans hη1)
  obtain ⟨M, hMn, hMv⟩ := drift_mul_exists K hη hS hϖ n (F.v r) (F.piece.hvs r)
    (F.piece.hv.2.2.1 r) (fun j z => F.piece.hvj j r z)
  have hθ := hρ
  have hsum : ∀ j k, |F.G r j k + F.G r k j| ≤ 4 := fun j k =>
    metric_sum_le (F.G r) (fun ξ => F.piece.hGm.2.2.2 r 0 ξ) j k
  have hdiag : ∀ j, |F.G r j j| ≤ 2 := by
    intro j
    have := hsum j j
    rw [← two_mul, abs_mul] at this
    norm_num at this
    linarith
  have hal := sameAlive_abs_le F.ηg F.letters i
  have ha4 : ∀ k, |F.G r k 0 + F.G r 0 k| ≤ 4 := fun k => hsum k 0
  have ha5 : ∀ k, |F.G r k 1 + F.G r 1 k| ≤ 4 := fun k => hsum k 1
  refine ⟨sameOp n N hnN θ M (fun k => F.G r k 0 + F.G r 0 k) (fun k => F.G r k 1 + F.G r 1 k)
    (sameE123 (sameAlive F.ηg F.letters i) F.ϖ (F.G r) i i')
    (sameE (sameAlive F.ηg F.letters i) i i' (1, 0) (1 * F.ϖ ^ (1 + 0)))
    (sameE (sameAlive F.ηg F.letters i) i i' (0, 1) (1 * F.ϖ ^ (0 + 1))), ?_, ?_⟩
  · have hρ0 : 0 ≤ ρ := (abs_nonneg _).trans (hθ 0)
    by_cases hrel : SameRel i i'
    · simp only [hrel, ↓reduceIte]
      have hSnn : 0 ≤ ∑ l ∈ Finset.range (n + 1), |K.Cvj l| :=
        Finset.sum_nonneg fun l _ => abs_nonneg _
      have hBnn : 0 ≤ |cellDriftNativePrice n| *
          ((∑ l ∈ Finset.range (n + 1), |K.Cvj l|) / F.ϖ) :=
        mul_nonneg (abs_nonneg _) (div_nonneg hSnn hϖpos.le)
      have hC0 : 0 ≤ 8 + 2 * (|cellDriftNativePrice n| *
          (∑ l ∈ Finset.range (n + 1), |K.Cvj l|) + 8 * (1 + |ρ|)) := by positivity
      refine ContinuousLinearMap.opNorm_le_bound _ hC0 fun ψ => ?_
      have hn := sameOp_norm_le n N hnN θ M (fun k => F.G r k 0 + F.G r 0 k)
        (fun k => F.G r k 1 + F.G r 1 k)
        (sameE123 (sameAlive F.ηg F.letters i) F.ϖ (F.G r) i i')
        (sameE (sameAlive F.ηg F.letters i) i i' (1, 0) (1 * F.ϖ ^ (1 + 0)))
        (sameE (sameAlive F.ηg F.letters i) i i' (0, 1) (1 * F.ϖ ^ (0 + 1)))
        _ ρ hBnn hMn ha4 ha5 hθ ψ
      have h123 := sameE123_abs_le (sameAlive F.ηg F.letters i) F.ϖ hal hϖpos.le hϖ1 (F.G r)
        (hdiag 0) (hdiag 1) (hsum 0 1) i i'
      have h4 : |sameE (sameAlive F.ηg F.letters i) i i' (1, 0) (1 * F.ϖ ^ (1 + 0))| ≤ F.ϖ :=
        (sameE_abs_le (sameAlive F.ηg F.letters i) hal i i' (1, 0)
          (1 * F.ϖ ^ (1 + 0))).trans (by simp [abs_of_pos hϖpos])
      have h5 : |sameE (sameAlive F.ηg F.letters i) i i' (0, 1) (1 * F.ϖ ^ (0 + 1))| ≤ F.ϖ :=
        (sameE_abs_le (sameAlive F.ηg F.letters i) hal i i' (0, 1)
          (1 * F.ϖ ^ (0 + 1))).trans (by simp [abs_of_pos hϖpos])
      refine hn.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      have hkey : F.ϖ * (|cellDriftNativePrice n| *
          ((∑ l ∈ Finset.range (n + 1), |K.Cvj l|) / F.ϖ) + 8 * (1 + ρ)) ≤
          |cellDriftNativePrice n| * (∑ l ∈ Finset.range (n + 1), |K.Cvj l|) +
            8 * (1 + |ρ|) := by
        have e : F.ϖ * (|cellDriftNativePrice n| *
            ((∑ l ∈ Finset.range (n + 1), |K.Cvj l|) / F.ϖ)) =
            |cellDriftNativePrice n| * (∑ l ∈ Finset.range (n + 1), |K.Cvj l|) := by
          field_simp
        nlinarith [le_abs_self ρ]
      have hq : 0 ≤ |cellDriftNativePrice n| *
          ((∑ l ∈ Finset.range (n + 1), |K.Cvj l|) / F.ϖ) + 8 * (1 + ρ) := by positivity
      have e4' := mul_le_mul_of_nonneg_right h4 hq
      have e5' := mul_le_mul_of_nonneg_right h5 hq
      nlinarith
    · simp only [hrel, ↓reduceIte]
      refine ContinuousLinearMap.opNorm_le_bound _ le_rfl fun ψ => ?_
      have hn := sameOp_norm_le n N hnN θ M (fun k => F.G r k 0 + F.G r 0 k)
        (fun k => F.G r k 1 + F.G r 1 k)
        (sameE123 (sameAlive F.ηg F.letters i) F.ϖ (F.G r) i i')
        (sameE (sameAlive F.ηg F.letters i) i i' (1, 0) (1 * F.ϖ ^ (1 + 0)))
        (sameE (sameAlive F.ηg F.letters i) i i' (0, 1) (1 * F.ϖ ^ (0 + 1)))
        _ ρ (mul_nonneg (abs_nonneg _) (div_nonneg (Finset.sum_nonneg fun l _ => abs_nonneg _)
          hϖpos.le)) hMn ha4 ha5 hθ ψ
      refine hn.trans (le_of_eq ?_)
      rw [sameE123_eq_zero _ _ _ i i' hrel,
        sameE_eq_zero_of_not_rel _ i i' hrel (1, 0) (by simp [sameShifts]),
        sameE_eq_zero_of_not_rel _ i i' hrel (0, 1) (by simp [sameShifts])]
      simp
  · intro ψ
    have hv := sameOp_value n N hnN (by omega) θ M (F.v r) hMv
      (fun k => F.G r k 0 + F.G r 0 k) (fun k => F.G r k 1 + F.G r 1 k)
      (sameE123 (sameAlive F.ηg F.letters i) F.ϖ (F.G r) i i')
      (sameE (sameAlive F.ηg F.letters i) i i' (1, 0) (1 * F.ϖ ^ (1 + 0)))
      (sameE (sameAlive F.ηg F.letters i) i i' (0, 1) (1 * F.ϖ ^ (0 + 1))) ψ
    have hf1 : ContDiff ℝ 1 (torusHigherClassicalValue N ψ) := by
      have := torusHigherClassicalValue_contDiff N 1 (by omega) ψ
      exact_mod_cast this
    filter_upwards [hv] with z hz
    rw [hz, same_star_eff F.π F.ϖ F.ηg F.letters F.piece.hπ hϖpos.ne' θ (F.G r) (F.v r) i i'
      (torusHigherClassicalValue N ψ) z ((hf1.differentiable one_ne_zero) z)]
    simp only [Fin.sum_univ_two, sameE123]

/-- **The same-level transform bound at every frequency of the zone**. -/
theorem sameLevelTransformBoundZone : SameLevelTransformBoundZoneStatement.{u, v} :=
  sameLevelTransformBoundZone_of_ops sameLevelOps

/-- **The same-level transform bound**: the zone bound with `theta_abs_le`. -/
theorem sameLevelTransformBound : SameLevelTransformBoundStatement.{u, v} := by
  intro K Nw D m d Ks ρ n
  obtain ⟨C, hC, hZ⟩ := sameLevelTransformBoundZone.{u, v} K Nw D m d Ks ρ n
  refine ⟨C, hC, ?_⟩
  intro g₁ ι _ h _ _ _ _ _ _ F θ hρ
  exact hZ g₁ F θ (theta_abs_le F.piece.hη F.piece.hη1 θ hρ)

end AVRegularity.CycleWords.Assembly
end
end
