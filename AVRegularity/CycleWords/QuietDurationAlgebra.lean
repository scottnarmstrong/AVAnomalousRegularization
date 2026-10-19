-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Homogenization.Ambient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Function.L2Space

section
@[expose] public section
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Finite positive vertex mass controls every component without a vertex count. -/

theorem finitePositiveMass_component_ne_top {ι : Type*} [Fintype ι]
    (α E : ι → ℝ≥0∞) (hα : ∀ v, α v ≠ 0) (he : (∑ v, α v * E v) ≠ ⊤) (v : ι) :
    E v ≠ ⊤ := by
  classical
  have hm : α v * E v ≠ ⊤ := ne_top_of_le_ne_top he
    (Finset.single_le_sum (fun u _ => (zero_le : 0 ≤ α u * E u)) (Finset.mem_univ v))
  exact (ENNReal.lt_top_of_mul_ne_top_right hm (hα v)).ne

theorem finitePositiveMass_ofReal_inv_component_ne_top {ι : Type*} [Fintype ι]
    (π : ι → ℝ) (E : ι → ℝ≥0∞) (hπ : ∀ v, 0 < π v)
    (he : (∑ v, ENNReal.ofReal ((π v)⁻¹) * E v) ≠ ⊤) (v : ι) : E v ≠ ⊤ := by
  exact finitePositiveMass_component_ne_top (fun v => ENNReal.ofReal ((π v)⁻¹)) E
    (fun v => (ENNReal.ofReal_pos.mpr (inv_pos.mpr (hπ v))).ne') he v

/-! Inverse-mass summation of the response remainder assembly budget. -/

theorem finiteRemainder_mass_budget {ι L : Type*} [Fintype ι] [Fintype L]
    (α E T : ι → ℝ≥0∞) (A B : L → ι → ℝ≥0∞) (c : ℝ≥0∞)
    (h : ∀ v, E v ≤ 4 * c * ((∑ j, A j v) + ∑ j, B j v) + 2 * T v) :
    (∑ v, α v * E v) ≤
      4 * c * ((∑ j, ∑ v, α v * A j v) + ∑ j, ∑ v, α v * B j v) +
      2 * ∑ v, α v * T v := by
  classical
  calc
    _ ≤ ∑ v, α v * (4 * c * ((∑ j, A j v) + ∑ j, B j v) + 2 * T v) :=
      Finset.sum_le_sum (fun v _ => mul_le_mul_right (h v) (α v))
    _ = _ := by
      have hp (v : ι) : α v * (4 * c * ((∑ j, A j v) + ∑ j, B j v) + 2 * T v) =
          4 * c * ((∑ j, α v * A j v) + ∑ j, α v * B j v) + 2 * (α v * T v) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        ring
      simp_rw [hp, Finset.sum_add_distrib]
      rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun v j => α v * A j v),
        Finset.sum_comm (f := fun v j => α v * B j v)]

/-! A finite renewal recurrence with a uniform forcing budget. -/

theorem finite_renewal_budget {P N : ℕ} (hP : P ≤ N)
    (E : Fin P → ℝ≥0∞) (D F A R H : ℝ≥0∞) (hH : 1 ≤ H)
    (hAH : A ≤ H) (hARH : A * R + A ≤ H)
    (hzero : ∀ i : Fin P, i.val = 0 → E i ≤ A * (D + F))
    (hstep : ∀ i j : Fin P, j.val = i.val + 1 → E j ≤ A * (R * E i + F)) :
    ∀ i : Fin P, E i ≤ H ^ N * (D + F) := by
  have haux : ∀ k, ∀ i : Fin P, i.val = k → E i ≤ H ^ (k + 1) * (D + F) := by
    intro k
    induction k with
    | zero =>
      intro i hi
      simpa only [zero_add, pow_one] using (hzero i hi).trans (mul_le_mul' hAH le_rfl)
    | succ k ih =>
      intro j hj
      let i : Fin P := ⟨k, by omega⟩
      have hei := ih i rfl
      have hf : F ≤ H ^ (k + 1) * (D + F) := by
        have hp : (1 : ℝ≥0∞) ≤ H ^ (k + 1) := one_le_pow₀ hH
        exact (le_add_left le_rfl).trans (by simpa using mul_le_mul' hp (le_rfl : D + F ≤ D + F))
      calc
        E j ≤ A * (R * E i + F) := hstep i j (by simpa [i] using hj)
        _ ≤ A * (R * (H ^ (k + 1) * (D + F)) + H ^ (k + 1) * (D + F)) :=
          mul_le_mul_right (add_le_add (mul_le_mul_right hei R) hf) A
        _ = (A * R + A) * (H ^ (k + 1) * (D + F)) := by ring
        _ ≤ H * (H ^ (k + 1) * (D + F)) := mul_le_mul' hARH le_rfl
        _ = H ^ (k + 1 + 1) * (D + F) := by rw [pow_succ]; ring
  intro i
  exact (haux i.val i rfl).trans (mul_le_mul'
    (pow_le_pow_right₀ hH (by omega : i.val + 1 ≤ N)) le_rfl)

/-! Finite response sums retain the Taylor remainder and terminal level gains. -/

theorem finiteResponse_level_sum_le (J : ℕ) (C ε D : ℝ≥0∞) (hC : 1 ≤ C) (hε : ε ≤ 1)
    (e : Fin (J + 1) → ℝ≥0∞) (he : ∀ j, e j ≤ C ^ (j.val + 1) * ε ^ j.val * D) :
    (∑ j, e j) ≤ (J + 1 : ℝ≥0∞) * C ^ (J + 1) * D := by
  classical
  have hp (j : Fin (J + 1)) : e j ≤ C ^ (J + 1) * D := by
    have hc := pow_le_pow_right₀ hC (Nat.succ_le_succ (Nat.le_of_lt_succ j.isLt))
    have hεp : ε ^ j.val ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ zero_le hε j.val
    exact (he j).trans (by simpa only [mul_one] using mul_le_mul_left (mul_le_mul' hc hεp) D)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hp j)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one, mul_assoc] using hh

theorem finiteResponse_remainder_budget (J : ℕ) (C ε ζsq D a b c : ℝ≥0∞)
    (hC : 1 ≤ C) (hε : ε ≤ 1) (e : Fin (J + 1) → ℝ≥0∞) (terminal forcing : ℝ≥0∞)
    (he : ∀ j, e j ≤ C ^ (j.val + 1) * ε ^ j.val * D)
    (ht : terminal ≤ C ^ (J + 1) * ε ^ J * D)
    (hf : forcing ≤ 4 * (J + 1 : ℝ≥0∞) * ((a + b) * ζsq * ∑ j, e j) + 2 * c * ε * terminal) :
    forcing ≤ (1 + 4 * (J + 1 : ℝ≥0∞) ^ 2 * (a + b) * C ^ (J + 1) +
      2 * c * C ^ (J + 1)) * (ζsq + ε ^ (J + 1)) * D := by
  have hs := finiteResponse_level_sum_le J C ε D hC hε e he
  let A := 4 * (J + 1 : ℝ≥0∞) ^ 2 * (a + b) * C ^ (J + 1)
  let B := 2 * c * C ^ (J + 1)
  have hh : forcing ≤ A * ζsq * D + B * ε ^ (J + 1) * D := by
    calc
      _ ≤ _ := hf
      _ ≤ 4 * (J + 1 : ℝ≥0∞) * ((a + b) * ζsq * ((J + 1 : ℝ≥0∞) * C ^ (J + 1) * D)) +
          2 * c * ε * (C ^ (J + 1) * ε ^ J * D) :=
        add_le_add (mul_le_mul_right (mul_le_mul_right hs _) _) (mul_le_mul_right ht _)
      _ = _ := by dsimp [A, B]; rw [pow_succ]; ring
  have hA : A ≤ 1 + A + B := (le_add_left le_rfl).trans (le_add_right le_rfl)
  have hB : B ≤ 1 + A + B := le_add_left le_rfl
  calc
    _ ≤ _ := hh
    _ ≤ (1 + A + B) * ζsq * D + (1 + A + B) * ε ^ (J + 1) * D :=
      add_le_add (mul_le_mul_left (mul_le_mul_left hA ζsq) D)
        (mul_le_mul_left (mul_le_mul_left hB _) D)
    _ = _ := by dsimp [A, B]; ring

/-! Finite data can be propagated before invoking a piece estimate that
requires finite initial moments. -/

theorem finite_response_renewal_data_ne_top {P : ℕ} (J : ℕ)
    (data energy : Fin P → ℕ → ℝ≥0∞) (L : ℝ≥0∞) (hL : L ≠ ⊤)
    (hzero : ∀ i : Fin P, i.val = 0 → ∀ j ≤ J, data i j ≠ ⊤)
    (hrenew : ∀ i i' : Fin P, i'.val = i.val + 1 → ∀ j ≤ J, data i' j ≤ L * energy i j)
    (hpiece : ∀ i : Fin P, (∀ j ≤ J, data i j ≠ ⊤) → ∀ j ≤ J, energy i j ≠ ⊤) :
    ∀ i : Fin P, ∀ j ≤ J, data i j ≠ ⊤ := by
  have haux : ∀ k, ∀ i : Fin P, i.val = k → ∀ j ≤ J, data i j ≠ ⊤ := by
    intro k
    induction k with
    | zero => exact fun i hi => hzero i hi
    | succ k ih =>
      intro i' hi' j hj
      let i : Fin P := ⟨k, by omega⟩
      have hi : i'.val = i.val + 1 := by simpa only [i] using hi'
      have he := hpiece i (ih i rfl) j hj
      exact ne_top_of_le_ne_top (ENNReal.mul_ne_top hL he) (hrenew i i' hi j hj)
  exact fun i => haux i.val i rfl

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleWords

/-! Ordered differentiation changes only the explicit coefficient jet budget. -/

section
variable {I V : Type*} [NormedAddCommGroup V]

def frequencyOrderedJetPrice (direction : I → V) (w : List I) (B : ℕ → ℝ) : ℕ → ℝ :=
  w.foldl (fun C i n => ‖direction i‖ * C (n + 1) + C n) B

theorem frequencyOrderedJetPrice_nonneg (direction : I → V) (w : List I)
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n) : ∀ n, 0 ≤ frequencyOrderedJetPrice direction w B n := by
  induction w generalizing B with
  | nil => exact hB
  | cons i w ih =>
    exact ih _ (fun n => add_nonneg (mul_nonneg (norm_nonneg _) (hB (n + 1))) (hB n))
end

/-! Ordered frequency derivatives and the literal operator coefficient product rule. -/

section
variable {I V E F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def frequencyOrderedDerivative (direction : I → V) (w : List I) (f : V → E) : V → E :=
  w.foldl (fun g i => fun x => fderiv ℝ g x (direction i)) f
end

/-! Exact extraction of the cumulative scalar phase from a chronological operator and derivative word. -/

section
variable {I V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

inductive FrequencyPhaseWordStep (I V E : Type*) [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℂ E] where
  | operator (A : V → E →L[ℂ] E)
  | phase (P : V → ℂ)
  | differentiate (word : List I)
end

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Filter Topology
namespace AVRegularity.CycleWords

/-! The future pulse integral satisfies the adjoint scalar memory equation. -/

def futureMemory (μ : ℝ) (p : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (μ * t) * ∫ s in Set.Ici t, p s * Real.exp (-μ * s)

theorem futureMemory_hasDerivAt (μ : ℝ) (p : ℝ → ℝ)
    (hp : Continuous p) (hc : HasCompactSupport p) (t : ℝ) :
    HasDerivAt (futureMemory μ p) (μ * futureMemory μ p t - p t) t := by
  let g := fun s : ℝ => p s * Real.exp (-μ * s)
  have hg : Continuous g := hp.mul (by fun_prop)
  have hgi : Integrable g := hg.integrable_of_hasCompactSupport (hc.mul_right)
  have heq (r : ℝ) : (∫ s in Set.Ici r, g s) =
      (∫ s, g s) - (∫ s in Set.Iic 0, g s) - ∫ s in (0 : ℝ)..r, g s := by
    have hsum := intervalIntegral.integral_Iic_add_Ioi
      (hgi.integrableOn : IntegrableOn g (Set.Iic r))
      (hgi.integrableOn : IntegrableOn g (Set.Ioi r))
    have hsub := intervalIntegral.integral_Iic_sub_Iic
      (μ := volume) (f := g) (hgi.integrableOn : IntegrableOn g (Set.Iic 0))
      (hgi.integrableOn : IntegrableOn g (Set.Iic r))
    rw [integral_Ici_eq_integral_Ioi]
    linarith only [hsum, hsub]
  have hprim : HasDerivAt (fun r => ∫ s in (0 : ℝ)..r, g s) (g t) t := by
    apply intervalIntegral.integral_hasDerivAt_right
    · exact hg.intervalIntegrable 0 t
    · exact hg.stronglyMeasurableAtFilter volume (𝓝 t)
    · exact hg.continuousAt
  have hi := hprim.const_sub ((∫ s, g s) - ∫ s in Set.Iic 0, g s)
  have hexp := (hasDerivAt_const_mul (x := t) μ).exp
  have hprod := hexp.mul hi
  have hcancel : Real.exp (μ * t) * Real.exp (-μ * t) = 1 := by
    rw [← Real.exp_add, show μ * t + -μ * t = 0 by ring, Real.exp_zero]
  have hfun : futureMemory μ p = fun r => Real.exp (μ * r) *
      ((∫ s, g s) - (∫ s in Set.Iic 0, g s) - ∫ s in (0 : ℝ)..r, g s) := by
    funext r
    exact congrArg (Real.exp (μ * r) * ·) (heq r)
  rw [hfun]
  convert hprod using 1
  dsimp [g]
  rw [show Real.exp (μ * t) * (-(p t * Real.exp (-μ * t))) =
    -(p t * (Real.exp (μ * t) * Real.exp (-μ * t))) by ring, hcancel]
  ring

end AVRegularity.CycleWords
end
end

section
@[expose] public section
namespace AVRegularity.CycleWords

/-! The preparation cover contains a uniformly bounded number of renewal pieces. -/

theorem renewal_piece_count_bound (h ta T C l : ℝ) (P : ℕ) (hh : 0 < h)
    (hstart : ta < (l + 1 / 2) * h)
    (hend : (l + (P : ℝ) - 3 / 2) * h < ta + T) (hdur : T ≤ C * h) :
    (P : ℝ) < C + 2 := by
  have hp : ((P : ℝ) - 2) * h < T := by nlinarith only [hstart, hend]
  have hprod : ((P : ℝ) - 2) * h < C * h := hp.trans_le hdur
  exact (sub_lt_iff_lt_add).mp ((mul_lt_mul_iff_left₀ hh).mp hprod)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Passing the actual quadratic remainder estimate to the norm. -/

theorem finiteError_root_budget (A C a b : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hAC : A ≤ C ^ 2) (E D : ℝ≥0∞)
    (hE : E ≤ ENNReal.ofReal A * (ENNReal.ofReal (a ^ 2) + ENNReal.ofReal (b ^ 2)) * D) :
    E ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (C * (a + b)) * D ^ (1 / 2 : ℝ) := by
  have hsq : A * (a ^ 2 + b ^ 2) ≤ (C * (a + b)) ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hAC (add_nonneg (sq_nonneg a) (sq_nonneg b))
    have h2 : a ^ 2 + b ^ 2 ≤ (a + b) ^ 2 := by nlinarith [mul_nonneg ha hb]
    have h3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg C)
    calc
      _ ≤ C ^ 2 * (a ^ 2 + b ^ 2) := h1
      _ ≤ C ^ 2 * (a + b) ^ 2 := h3
      _ = _ := by ring
  have hcoef : ENNReal.ofReal A * (ENNReal.ofReal (a ^ 2) + ENNReal.ofReal (b ^ 2)) ≤
      ENNReal.ofReal (C * (a + b)) ^ 2 := by
    rw [← ENNReal.ofReal_add (sq_nonneg a) (sq_nonneg b), ← ENNReal.ofReal_mul hA,
      ← ENNReal.ofReal_pow (mul_nonneg hC (add_nonneg ha hb))]
    exact ENNReal.ofReal_le_ofReal hsq
  have he := ENNReal.rpow_le_rpow (hE.trans (mul_le_mul_left hcoef D)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_two,
    ← ENNReal.rpow_mul] at he
  norm_num only [show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one] at he
  exact he

theorem finiteError_response_square (x : ℝ) (_hx : 0 ≤ x) (J : ℕ) :
    ENNReal.ofReal (x ^ 2) ^ (J + 1) = ENNReal.ofReal ((x ^ (J + 1)) ^ 2) := by
  rw [← ENNReal.ofReal_pow (sq_nonneg x)]
  congr 1
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

theorem finiteError_mass_finite_of_root {D : ℝ≥0∞} (h : D ^ (1 / 2 : ℝ) ≠ ⊤) : D ≠ ⊤ := by
  intro hd
  apply h
  rw [hd, ENNReal.top_rpow_of_pos (by norm_num)]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleWords

/-! Clipping enlarged pulses behind endpoint margins preserves their quiet quarter-pulse buffers. -/

def interiorBufferedPulseLo (τ a D : ℝ) (n : ℤ) : ℝ :=
  max (a + D) ((2 * (n : ℝ) + 1) * τ - 3 / 4 * τ)

def interiorBufferedPulseHi (τ b D : ℝ) (n : ℤ) : ℝ :=
  min (b - D) ((2 * (n : ℝ) + 1) * τ + 3 / 4 * τ)

theorem interiorBufferedPulse_inside (τ a b D : ℝ) (n : ℤ) :
    Set.Icc (interiorBufferedPulseLo τ a D n - D)
      (interiorBufferedPulseHi τ b D n + D) ⊆ Set.Icc a b := by
  intro t ht
  have hlo := le_max_left (a + D) ((2 * (n : ℝ) + 1) * τ - 3 / 4 * τ)
  have hhi := min_le_left (b - D) ((2 * (n : ℝ) + 1) * τ + 3 / 4 * τ)
  change _ ≤ interiorBufferedPulseLo τ a D n at hlo
  change interiorBufferedPulseHi τ b D n ≤ _ at hhi
  constructor <;> linarith [ht.1, ht.2]

theorem interiorBufferedPulse_left_buffer {τ a D : ℝ} (hτ : 0 < τ)
    (hD : D ≤ τ / 4) (n : ℤ) {t : ℝ}
    (ht : t ∈ Set.Ico (interiorBufferedPulseLo τ a D n - D)
      (interiorBufferedPulseLo τ a D n)) :
    t ∈ Set.Ico a (a + D) ∨
      3 / 4 * τ ≤ |t - (2 * (n : ℝ) + 1) * τ| ∧
        |t - (2 * (n : ℝ) + 1) * τ| ≤ τ := by
  by_cases h : (2 * (n : ℝ) + 1) * τ - 3 / 4 * τ ≤ a + D
  · left
    simp only [interiorBufferedPulseLo, max_eq_left h] at ht
    exact ⟨by linarith [ht.1], ht.2⟩
  · right
    have h' := le_of_lt (lt_of_not_ge h)
    simp only [interiorBufferedPulseLo, max_eq_right h'] at ht
    have hs : t - (2 * (n : ℝ) + 1) * τ ≤ 0 := by linarith [ht.2]
    rw [abs_of_nonpos hs]
    constructor <;> linarith [ht.1, ht.2]

theorem interiorBufferedPulse_right_buffer {τ b D : ℝ} (hτ : 0 < τ)
    (hD : D ≤ τ / 4) (n : ℤ) {t : ℝ}
    (ht : t ∈ Set.Ioc (interiorBufferedPulseHi τ b D n)
      (interiorBufferedPulseHi τ b D n + D)) :
    t ∈ Set.Ioc (b - D) b ∨
      3 / 4 * τ ≤ |t - (2 * (n : ℝ) + 1) * τ| ∧
        |t - (2 * (n : ℝ) + 1) * τ| ≤ τ := by
  by_cases h : b - D ≤ (2 * (n : ℝ) + 1) * τ + 3 / 4 * τ
  · left
    simp only [interiorBufferedPulseHi, min_eq_left h] at ht
    exact ⟨ht.1, by linarith [ht.2]⟩
  · right
    have h' := le_of_lt (lt_of_not_ge h)
    simp only [interiorBufferedPulseHi, min_eq_right h'] at ht
    have hs : 0 ≤ t - (2 * (n : ℝ) + 1) * τ := by linarith [ht.1]
    rw [abs_of_nonneg hs]
    constructor <;> linarith [ht.1, ht.2]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Positive real molecular prices preserve the original constituent sums. -/

def molecularRealPrice (ν ρ : ℝ) (K d : ℕ) (M : ℝ≥0∞) : ℝ :=
  M.toReal * (ν * ρ ^ d)⁻¹ * (((K + d).factorial : ℝ) / (K.factorial : ℝ))

theorem molecularRealPrice_nonneg (ν ρ : ℝ) (hν : 0 ≤ ν) (hρ : 0 ≤ ρ)
    (K d : ℕ) (M : ℝ≥0∞) : 0 ≤ molecularRealPrice ν ρ K d M := by
  unfold molecularRealPrice
  positivity

theorem molecularRealPrice_ofReal_le (ν ρ : ℝ) (hν : 0 < ν) (hρ : 0 < ρ)
    (K d : ℕ) (M : ℝ≥0∞) :
    ENNReal.ofReal (molecularRealPrice ν ρ K d M) ≤
      M * (ENNReal.ofReal (ν * ρ ^ d))⁻¹ *
        ENNReal.ofReal (((K + d).factorial : ℝ) / (K.factorial : ℝ)) := by
  unfold molecularRealPrice
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_inv_of_pos (by positivity)]
  exact mul_le_mul' (mul_le_mul' (ENNReal.ofReal_toReal_le (a := M)) le_rfl) le_rfl

theorem molecularRealPrice_div_identity (ν ρ : ℝ) (hν : 0 < ν) (hρ : 0 < ρ)
    (K d : ℕ) (M : ℝ≥0∞) :
    M.toReal / ((ν * ρ ^ d) * ((K.factorial : ℝ) / ((K + d).factorial : ℝ))) =
      molecularRealPrice ν ρ K d M := by
  unfold molecularRealPrice
  field_simp

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleWords

/-! Exact radius bookkeeping under constant spatial rescaling. -/

theorem normalizedJet_rescaling_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (j : ℕ) {f : Vec 2 → E} (hf : ContDiff ℝ (j : ℕ) f)
    (ρ τ : ℝ) (z : Vec 2) :
    ρ ^ j * ‖iteratedFDeriv ℝ j (fun z => f (τ • z)) z‖ =
      (ρ * |τ|) ^ j * ‖iteratedFDeriv ℝ j f (τ • z)‖ := by
  rw [congrFun (iteratedFDeriv_comp_const_smul τ hf) z, norm_smul,
    Real.norm_eq_abs, abs_pow, mul_pow]
  ring

end AVRegularity.CycleWords
end
end

section
@[expose] public section
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! A scalar metric insertion bound passes to normalized component energies
before any choice of the response level or Hilbert space. -/

variable {ι : Type*} [Fintype ι]

theorem normalized_response_metric_budget (α m M ε : ℝ) (hM : 0 ≤ M)
    (hm : m ≤ M * ε) (G E : ι → ℝ≥0∞) (hGE : ∀ u, G u ≤ E u) :
    32 * (ENNReal.ofReal α * ENNReal.ofReal m * ∑ u, G u) ≤
      ENNReal.ofReal (32 * M) * ENNReal.ofReal ε * ∑ u, ENNReal.ofReal α * E u := by
  have hh := mul_le_mul_left (ENNReal.ofReal_le_ofReal hm) (ENNReal.ofReal α)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun u _ => hGE u)
  have hb := mul_le_mul_right (mul_le_mul hh hs zero_le zero_le) 32
  rw [ENNReal.ofReal_mul hM] at hb
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 32)]
  simp only [ENNReal.ofReal_ofNat, ← Finset.mul_sum]
  simpa only [mul_assoc, mul_comm (ENNReal.ofReal α), mul_left_comm (ENNReal.ofReal α)] using hb

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! The native normalized row bound is exactly a scalar multiple of the
normalized descending graph acting on inverse-mass component energies. -/

variable {ι : Type*} [Fintype ι]

theorem normalized_response_source_budget (θ : ℝ) (hθ : 0 ≤ θ)
    (p α : ι → ℝ) (hp : ∀ u, 0 ≤ p u) (_hα : ∀ u, 0 ≤ α u)
    (G E : ι → ℝ≥0∞) (hGE : ∀ u, G u ≤ E u) :
    32 * ENNReal.ofReal θ * (∑ u, ENNReal.ofReal (p u * α u) * G u) ≤
      ENNReal.ofReal (32 * θ * (1 + θ)) *
        ∑ u, ENNReal.ofReal (p u / (1 + θ)) * (ENNReal.ofReal (α u) * E u) := by
  have ht : 0 < 1 + θ := by linarith
  have hs (u : ι) : p u = (1 + θ) * (p u / (1 + θ)) := by
    exact (mul_div_cancel₀ _ ht.ne').symm
  have hrew (u : ι) : ENNReal.ofReal (p u * α u) =
      ENNReal.ofReal (1 + θ) * ENNReal.ofReal (p u / (1 + θ)) * ENNReal.ofReal (α u) := by
    rw [ENNReal.ofReal_mul (hp u)]
    conv_lhs => lhs; rw [hs u, ENNReal.ofReal_mul ht.le]
  simp_rw [hrew]
  rw [ENNReal.ofReal_mul (mul_nonneg (by norm_num) hθ), ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 32)]
  simp only [ENNReal.ofReal_ofNat]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u _
  have hh := mul_le_mul_right (hGE u)
    (32 * ENNReal.ofReal θ * ENNReal.ofReal (1 + θ) * ENNReal.ofReal (p u / (1 + θ)) * ENNReal.ofReal (α u))
  simpa only [mul_assoc] using hh

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.CycleWords

/-! Actual L2 fiber coordinates pair against scalar tests by their literal fiber injections. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def planeFiberCoordinateCLM (e : E) :
    Lp E 2 (volume : Measure (Vec 2)) →L[ℝ] Lp ℝ 2 (volume : Measure (Vec 2)) :=
  (InnerProductSpace.toDual ℝ E e).compLpL 2 volume

def planeFiberInjectionCLM (e : E) :
    Lp ℝ 2 (volume : Measure (Vec 2)) →L[ℝ] Lp E 2 (volume : Measure (Vec 2)) :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight e).compLpL 2 volume

theorem planeFiberCoordinate_pair (e : E)
    (u : Lp E 2 (volume : Measure (Vec 2))) (φ : Lp ℝ 2 (volume : Measure (Vec 2))) :
    inner ℝ (planeFiberCoordinateCLM e u) φ = inner ℝ u (planeFiberInjectionCLM e φ) := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(InnerProductSpace.toDual ℝ E e).coeFn_compLpL u,
    ((ContinuousLinearMap.id ℝ ℝ).smulRight e).coeFn_compLpL φ] with x hc hi
  change planeFiberCoordinateCLM e u x = inner ℝ e (u x) at hc
  change planeFiberInjectionCLM e φ x = φ x • e at hi
  rw [hc, hi, Real.inner_apply, real_inner_smul_right, real_inner_comm (u x) e]
  ring

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set Function
namespace AVRegularity.CycleWords

/-! Exact half-open frequency cells for a plane lattice. -/

def planeFrequencyCell (a : Vec 2) (P : ℝ) : Set (Vec 2) :=
  {x | ∀ i, x i ∈ Ioc (a i) (a i + P)}

theorem planeFrequencyCell_measurable (a : Vec 2) (P : ℝ) :
    MeasurableSet (planeFrequencyCell a P) := by
  have he : planeFrequencyCell a P =
      ⋂ i : Fin 2, (fun x : Vec 2 => x i) ⁻¹' Ioc (a i) (a i + P) := by
    ext x
    simp [planeFrequencyCell]
  rw [he]
  exact MeasurableSet.iInter (fun i : Fin 2 => measurableSet_Ioc.preimage
    (show Measurable (fun x : Vec 2 => x i) from measurable_pi_apply i))

def planeLatticeEmbedding (P : ℝ) : (Fin 2 → ℤ) →+ Vec 2 where
  toFun n i := n i • P
  map_zero' := by ext i; simp
  map_add' n m := by ext i; simp [add_mul]

theorem planeLatticeEmbedding_injective (P : ℝ) (hP : 0 < P) :
    Injective (planeLatticeEmbedding P) := by
  intro n m h
  funext i
  exact (zsmul_left_strictMono hP).injective (congrFun h i)

theorem planeFrequencyCell_unique_shift (a x : Vec 2) (P : ℝ) (hP : 0 < P) :
    ∃! n : Fin 2 → ℤ, planeLatticeEmbedding P n + x ∈ planeFrequencyCell a P := by
  have h : ∀ i : Fin 2, ∃! n : ℤ, x i + n • P ∈ Ioc (a i) (a i + P) :=
    fun i => existsUnique_add_zsmul_mem_Ioc hP (x i) (a i)
  choose n hn hu using h
  refine ⟨n, ?_, ?_⟩
  · intro i
    simpa only [planeLatticeEmbedding, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Pi.add_apply,
      add_comm] using hn i
  · intro m hm
    funext i
    apply hu i
    have hh := hm i
    change m i • P + x i ∈ Ioc (a i) (a i + P) at hh
    simpa only [add_comm] using hh

end AVRegularity.CycleWords
end
end

section
@[expose] public section
namespace AVRegularity.CycleWords

/-! The quiet duration premise controls the future-memory residual at the inverse time scale. -/

theorem quiet_duration_normalized_sq {B T L τ E D C : ℝ}
    (hB : 0 < B) (hT : 0 < T) (hτ : 0 < τ) (hL : 0 ≤ L) (hE : 0 ≤ E) (hC : 0 ≤ C)
    (hD : D ^ 2 ≤ C * B * L ^ 2)
    (hdur : Real.sqrt T * L / τ * E ≤ 1) :
    (T / Real.sqrt (B * T) * (E * D / τ)) ^ 2 ≤ C := by
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤ Real.sqrt T * L / τ * E) zero_le_one).2 hdur
  simp only [mul_pow, div_pow, Real.sq_sqrt hT.le, one_pow] at hsq
  have hmul := mul_le_mul_of_nonneg_left hD
    (show 0 ≤ T * E ^ 2 / (B * τ ^ 2) by positivity)
  have hid : (T / Real.sqrt (B * T) * (E * D / τ)) ^ 2 =
      (T * E ^ 2 / (B * τ ^ 2)) * D ^ 2 := by
    simp only [mul_pow, div_pow, Real.sq_sqrt (mul_pos hB hT).le]
    field_simp
  rw [hid]
  apply hmul.trans
  have hh := mul_le_mul_of_nonneg_left hsq hC
  convert hh using 1 <;> field_simp

end AVRegularity.CycleWords
end
end
