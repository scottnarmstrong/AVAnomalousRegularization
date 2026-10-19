-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.ChildInert.Center
public import AVRegularity.Proofs.ComplexVel.Main
import AVRegularity.CycleReference.SingleModeFlux
import AVRegularity.Construction.Stream.NextAdmissible
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.RingTheory.PicardGroup

@[expose] public noncomputable section

section
namespace AVRegularity.Providers.ComplexFlow

/-! **The constants of the chain induction** (abstract-real lemmas). The family of level `k` of a
chain has the radius `ϱ_k = 8bε_k`, the window of half length `3h_{k+1}/5` and the two-time Jacobian
rate `K a_k`, `K = 2^25` (`chainK`). The inputs are the smallness `a_k h_{k+1} ≤ b/10^4` of the
carrier start (with `Υ, C_H ≥ 1`), `b ≤ 10^{-4}`, `128ε_k ≤ ε_{k-1}` and `2a_{k-1} ≤ a_k`.
* the `step_…` lemmas: the radius conditions and the rate bound of the child step (`CFam.ChildHyp`),
  with the transverse strip `σ = 15bε_k`, the shear bounds `M = 2πa_kε_k e^{30πb}`,
  `M' = 4π²a_k e^{30πb+1}`, the center bound `3bε_k/4` and the phase bound `(3+1/2)b + b/64`;
* `base_consts`: the window and domain conditions of the base family (`CFam.baseFam_ok`) with the
  strip `19ε/1000` of the complex base flow and the base labels in `S_{15ε/1000}`. -/

/-- The chain constant `K = 2^25`. -/
def chainK : ℝ := 2 ^ 25

/-- The phase bound `(3 + 1/2) b + b/64` of the children on the outer carrier. -/
def phB (b : ℝ) : ℝ := 225 / 64 * b

theorem exp_small_le {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 10000) :
    Real.exp (30 * Real.pi * b) ≤ 101 / 100 := by
  have hπ := Real.pi_lt_d2
  have hx0 : 0 ≤ 30 * Real.pi * b := by positivity
  have hx1 : 30 * Real.pi * b ≤ 945 / 100000 := by
    have := mul_le_mul_of_nonneg_right hπ.le hb0
    have e1 : 30 * Real.pi * b = 30 * (Real.pi * b) := by ring
    rw [e1]; linarith
  refine (Real.exp_bound_div_one_sub_of_interval hx0 (by linarith)).trans ?_
  rw [div_le_iff₀ (by linarith)]
  linarith

theorem exp_small_one_le {b : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1 / 10000) :
    Real.exp (30 * Real.pi * b + 1) ≤ 11 / 4 := by
  rw [Real.exp_add]
  have h1 := exp_small_le hb0 hb1
  have h2 := Real.exp_one_lt_d9
  have h3 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  calc Real.exp (30 * Real.pi * b) * Real.exp 1 ≤ 101 / 100 * 2.7182818286 :=
        mul_le_mul h1 h2.le h3 (by norm_num)
    _ ≤ 11 / 4 := by norm_num

theorem chainK_eq : chainK = 33554432 := by norm_num [chainK]

/-- The parent product `ΛT = K A (6H/5)` is at most `4027 b`. -/
theorem step_u_le {b A H : ℝ} (hA : 0 ≤ A) (hH : 0 ≤ H) (hAH : A * H ≤ b / 10000) :
    chainK * A * (6 / 5 * H) ≤ 4027 * b := by
  have e : chainK * A * (6 / 5 * H) = 6 / 5 * chainK * (A * H) := by ring
  rw [e]
  have h1 : 6 / 5 * chainK * (A * H) ≤ 6 / 5 * chainK * (b / 10000) :=
    mul_le_mul_of_nonneg_left hAH (by rw [chainK_eq]; norm_num)
  have h0 : 0 ≤ A * H := mul_nonneg hA hH
  have hb : 0 ≤ b := by linarith
  rw [chainK_eq] at h1 ⊢
  linarith

theorem step_u_nonneg {A H : ℝ} (hA : 0 ≤ A) (hH : 0 ≤ H) : 0 ≤ chainK * A * (6 / 5 * H) := by
  rw [chainK_eq]; positivity

/-- The shear displacement over the child window `T'M` is at most `b ε/1000`. -/
theorem step_w_le {b e a h X : ℝ} (he : 0 < e) (ha : 0 ≤ a) (hh : 0 ≤ h)
    (hah : a * h ≤ b / 10000) (hX0 : 0 ≤ X) (hX : X ≤ 101 / 100) :
    6 / 5 * h * (2 * Real.pi * a * e * X) ≤ 1 / 1000 * b * e := by
  have hπ := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  have e1 : 6 / 5 * h * (2 * Real.pi * a * e * X) = 12 / 5 * (Real.pi * X) * (a * h) * e := by ring
  have h1 : Real.pi * X ≤ 3.15 * (101 / 100) := mul_le_mul hπ.le hX hX0 (by norm_num)
  have h2 : (Real.pi * X) * (a * h) ≤ (3.15 * (101 / 100)) * (b / 10000) :=
    mul_le_mul h1 hah (mul_nonneg ha hh) (by norm_num)
  have h3 : 12 / 5 * (Real.pi * X) * (a * h) * e ≤ 12 / 5 * ((3.15 * (101 / 100)) * (b / 10000)) * e := by
    have : 12 / 5 * (Real.pi * X) * (a * h) * e = 12 / 5 * ((Real.pi * X) * (a * h)) * e := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by norm_num)) he.le
  rw [e1]
  refine h3.trans ?_
  have hb : 0 ≤ b := by have := mul_nonneg ha hh; linarith
  have hbe : 0 ≤ b * e := mul_nonneg hb he.le
  have e2 : 12 / 5 * ((3.15 * (101 / 100)) * (b / 10000)) * e =
      12 * 3.15 * 101 / (5 * 100 * 10000) * (b * e) := by ring
  have e3 : 1 / 1000 * b * e = 1 / 1000 * (b * e) := by ring
  rw [e2, e3]
  have : (12 * 3.15 * 101 / (5 * 100 * 10000) : ℝ) ≤ 1 / 1000 := by norm_num
  exact mul_le_mul_of_nonneg_right this hbe

theorem step_w_nonneg {e a h X : ℝ} (he : 0 < e) (ha : 0 ≤ a) (hh : 0 ≤ h) (hX0 : 0 ≤ X) :
    0 ≤ 6 / 5 * h * (2 * Real.pi * a * e * X) := by
  have := Real.pi_pos; positivity

/-- The transverse strip of the child step. -/
theorem step_sigma {b e u w : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1 / 10000) (he : 0 < e)
    (hu : u ≤ 4027 * b) (hw : w ≤ 1 / 1000 * b * e) :
    (1 + u) * (8 * b * e) + w + e * phB b ≤ 15 * b * e := by
  have hbe : 0 < b * e := mul_pos hb0 he
  have h1 : (1 + u) * (8 * b * e) ≤ (1 + 41 / 100) * (8 * b * e) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have e1 : e * phB b = 225 / 64 * (b * e) := by unfold phB; ring
  have e2 : (1 + 41 / 100) * (8 * b * e) = 1128 / 100 * (b * e) := by ring
  have e3 : 15 * b * e = 15 * (b * e) := by ring
  have e4 : 1 / 1000 * b * e = 1 / 1000 * (b * e) := by ring
  rw [e1, e3]; rw [e2] at h1; rw [e4] at hw
  linarith

/-- The first radius condition of the child step. -/
theorem step_Ra {b E e u w : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1 / 10000) (he : 0 < e)
    (hE : 128 * e ≤ E) (hu : u ≤ 4027 * b) (hw0 : 0 ≤ w)
    (hw : w ≤ 1 / 1000 * b * e) :
    8 * b * e + (1 + u) * (3 / 4 * b * e + w) < 8 * b * E / 4 := by
  have hbe : 0 < b * e := mul_pos hb0 he
  have hbE : 256 * (b * e) ≤ 8 * b * E / 4 := by
    have := mul_le_mul_of_nonneg_left hE hb0.le
    linarith
  have h1 : (1 + u) * (3 / 4 * b * e + w) ≤ (1 + 41 / 100) * (3 / 4 * (b * e) + 1 / 1000 * (b * e)) :=
    mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
  have e1 : (1 + 41 / 100) * (3 / 4 * (b * e) + 1 / 1000 * (b * e)) = 105891 / 100000 * (b * e) := by ring
  have e2 : 8 * b * e = 8 * (b * e) := by ring
  rw [e1] at h1; rw [e2]
  linarith

/-- The second radius condition of the child step. -/
theorem step_Rb {b E e u w : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1 / 10000) (he : 0 < e)
    (hE : 128 * e ≤ E) (hu : u ≤ 4027 * b) (hw : w ≤ 1 / 1000 * b * e) :
    3 / 4 * b * e + (1 + u) * (8 * b * e) + 2 * w < 8 * b * E / 4 := by
  have hbe : 0 < b * e := mul_pos hb0 he
  have hbE : 256 * (b * e) ≤ 8 * b * E / 4 := by
    have := mul_le_mul_of_nonneg_left hE hb0.le
    linarith
  have h1 : (1 + u) * (8 * b * e) ≤ (1 + 41 / 100) * (8 * (b * e)) :=
    mul_le_mul (by linarith) (by linarith) (by positivity) (by norm_num)
  have e1 : 3 / 4 * b * e = 3 / 4 * (b * e) := by ring
  have e4 : 1 / 1000 * b * e = 1 / 1000 * (b * e) := by ring
  rw [e1]; rw [e4] at hw
  linarith

/-- The Cauchy term of the rate of the child step. -/
theorem step_cauchy {b E e a u X : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1 / 10000) (he : 0 < e)
    (hE : 128 * e ≤ E) (ha : 0 ≤ a) (hu0 : 0 ≤ u) (hu : u ≤ 4027 * b) (hX0 : 0 ≤ X)
    (hX : X ≤ 101 / 100) :
    (1 + u) * (4 * u / (8 * b * E)) * (2 * Real.pi * a * e * X) ≤ 143 * a := by
  have hπ := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  have hE0 : 0 < E := by linarith
  have t1 : 4 * u / (8 * b * E) ≤ 2014 / E := by
    rw [div_le_div_iff₀ (by positivity) hE0]
    have := mul_le_mul_of_nonneg_right hu hE0.le
    have e1 : 4 * u * E = 4 * (u * E) := by ring
    have e2 : 2014 * (8 * b * E) = 16112 * (b * E) := by ring
    have e3 : 4027 * b * E = 4027 * (b * E) := by ring
    rw [e1, e2]; rw [e3] at this
    have : 0 ≤ b * E := by positivity
    linarith
  have t2 : 2 * Real.pi * a * e * X ≤ 637 / 100 * (a * e) := by
    have h1 : Real.pi * X ≤ 3.15 * (101 / 100) := mul_le_mul hπ.le hX hX0 (by norm_num)
    have e1 : 2 * Real.pi * a * e * X = 2 * (Real.pi * X) * (a * e) := by ring
    rw [e1]
    have := mul_le_mul_of_nonneg_right h1 (mul_nonneg ha he.le)
    have : 0 ≤ a * e := mul_nonneg ha he.le
    nlinarith
  have t3 : 2014 / E * (637 / 100 * (a * e)) ≤ 101 * a := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hE0]
    have h1 := mul_le_mul_of_nonneg_left hE ha
    have e1 : 2014 * (637 / 100 * (a * e)) = 2014 * 637 / 100 * (a * e) := by ring
    have e2 : a * (128 * e) = 128 * (a * e) := by ring
    rw [e1]; rw [e2] at h1
    have : 0 ≤ a * e := mul_nonneg ha he.le
    linarith
  have h4 : 0 ≤ 4 * u / (8 * b * E) := by positivity
  have h5 : 0 ≤ 2 * Real.pi * a * e * X := by positivity
  calc (1 + u) * (4 * u / (8 * b * E)) * (2 * Real.pi * a * e * X)
      = (1 + u) * ((4 * u / (8 * b * E)) * (2 * Real.pi * a * e * X)) := by ring
    _ ≤ (1 + 41 / 100) * (101 * a) := by
      refine mul_le_mul (by linarith) ?_ (by positivity) (by norm_num)
      exact (mul_le_mul t1 t2 h5 (by positivity)).trans t3
    _ ≤ 143 * a := by linarith

/-- The shear derivative term of the rate of the child step. -/
theorem step_shear {b a u Y : ℝ} (hb1 : b ≤ 1 / 10000) (ha : 0 ≤ a) (hu0 : 0 ≤ u)
    (hu : u ≤ 4027 * b) (hY0 : 0 ≤ Y) (hY : Y ≤ 11 / 4) :
    (1 + u) ^ 2 * (4 * Real.pi ^ 2 * a * Y) ≤ 219 * a := by
  have hπ := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  have h1 : (1 + u) ^ 2 ≤ (1 + 41 / 100) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  have h2 : Real.pi ^ 2 ≤ 3.15 ^ 2 := pow_le_pow_left₀ hπ0.le hπ.le 2
  have h3 : Real.pi ^ 2 * Y ≤ 3.15 ^ 2 * (11 / 4) := mul_le_mul h2 hY hY0 (by norm_num)
  have h4 : 4 * Real.pi ^ 2 * a * Y ≤ 4 * (3.15 ^ 2 * (11 / 4)) * a := by
    have e1 : 4 * Real.pi ^ 2 * a * Y = 4 * (Real.pi ^ 2 * Y) * a := by ring
    rw [e1]
    exact mul_le_mul_of_nonneg_right (by linarith) ha
  calc (1 + u) ^ 2 * (4 * Real.pi ^ 2 * a * Y)
      ≤ (1 + 41 / 100) ^ 2 * (4 * (3.15 ^ 2 * (11 / 4)) * a) :=
        mul_le_mul h1 h4 (by positivity) (by norm_num)
    _ ≤ 219 * a := by norm_num; linarith

/-- **The rate of the child step** is at most `K a_k`. -/
theorem step_rate {b E e A a H X Y : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1 / 10000) (he : 0 < e)
    (hE : 128 * e ≤ E) (hA : 0 ≤ A) (hAa : 2 * A ≤ a) (hH : 0 ≤ H)
    (hAH : A * H ≤ b / 10000) (hX0 : 0 ≤ X) (hX : X ≤ 101 / 100) (hY0 : 0 ≤ Y)
    (hY : Y ≤ 11 / 4) :
    chainK * A + (1 + chainK * A * (6 / 5 * H)) *
        (4 * (chainK * A * (6 / 5 * H)) / (8 * b * E)) * (2 * Real.pi * a * e * X) +
        (1 + chainK * A * (6 / 5 * H)) ^ 2 * (4 * Real.pi ^ 2 * a * Y) ≤ chainK * a := by
  have ha : 0 ≤ a := by linarith
  have hu0 := step_u_nonneg hA hH
  have hu := step_u_le hA hH hAH
  have h1 := step_cauchy hb0 hb1 he hE ha hu0 hu hX0 hX
  have h2 := step_shear hb1 ha hu0 hu hY0 hY
  have hKA : chainK * A ≤ chainK * a / 2 := by rw [chainK_eq]; linarith
  have h3 : chainK * a / 2 + 143 * a + 219 * a ≤ chainK * a := by rw [chainK_eq]; linarith
  linarith

/-- The child window: `K a_k (6h_{k+1}/5) ≤ 1/2`. -/
theorem step_window {b a h : ℝ} (hb1 : b ≤ 1 / 10000) (ha : 0 ≤ a) (hh : 0 ≤ h)
    (hah : a * h ≤ b / 10000) : chainK * a * (6 / 5 * h) ≤ 1 / 2 := by
  have := step_u_le ha hh hah
  linarith

/-- The base product `ΓT = 2^21 A (6H/5)` is at most `26/1000`. -/
theorem base_g_le {b A H : ℝ} (hb1 : b ≤ 1 / 10000)
    (hAH : A * H ≤ b / 10000) : 2 ^ 21 * A * (6 / 5 * H) ≤ 26 / 1000 := by
  have e : 2 ^ 21 * A * (6 / 5 * H) = 6 / 5 * 2 ^ 21 * (A * H) := by ring
  rw [e]
  have h1 : 6 / 5 * 2 ^ 21 * (A * H) ≤ 6 / 5 * 2 ^ 21 * (b / 10000) :=
    mul_le_mul_of_nonneg_left hAH (by norm_num)
  linarith

/-- The domain condition of the base family. -/
theorem base_dom {b E g : ℝ} (hb1 : b ≤ 1 / 10000) (hE0 : 0 < E)
    (hg : g ≤ 26 / 1000) :
    15 / 1000 * E / (1 - g) + 2 * (8 * b * E) ≤ (1 - g) ^ 2 * (19 / 1000 * E) := by
  have h1g : 0 < 1 - g := by linarith
  have h1 : 15 / 1000 * E / (1 - g) ≤ 155 / 10000 * E := by
    rw [div_le_iff₀ h1g]
    have := mul_le_mul_of_nonneg_right hg hE0.le
    have e1 : 155 / 10000 * E * (1 - g) = 155 / 10000 * E - 155 / 10000 * (g * E) := by ring
    rw [e1]; linarith
  have h2 : 1 - 2 * g ≤ (1 - g) ^ 2 := by have := sq_nonneg g; linarith [sq_nonneg g]
  have h3 : (1 - 2 * g) * (19 / 1000 * E) ≤ (1 - g) ^ 2 * (19 / 1000 * E) :=
    mul_le_mul_of_nonneg_right h2 (by positivity)
  have h4 : 2 * (8 * b * E) ≤ 16 / 10000 * E := by
    have := mul_le_mul_of_nonneg_right hb1 hE0.le
    have e1 : 2 * (8 * b * E) = 16 * (b * E) := by ring
    rw [e1]; linarith
  have h5 := mul_le_mul_of_nonneg_right hg hE0.le
  have e2 : (1 - 2 * g) * (19 / 1000 * E) = 19 / 1000 * E - 38 / 1000 * (g * E) := by ring
  rw [e2] at h3
  linarith

/-- **The constants of the base family.** -/
theorem base_consts {b E A H : ℝ} (hb1 : b ≤ 1 / 10000) (hE0 : 0 < E) (hA : 0 ≤ A)
    (hH : 0 ≤ H) (hAH : A * H ≤ b / 10000) :
    10 * (2 ^ 21 * A) * (6 / 5 * H) ≤ 1 / 2 ∧ 2 ^ 21 * A * (6 / 5 * H) ≤ 2 / 5 ∧
      15 / 1000 * E / (1 - 2 ^ 21 * A * (6 / 5 * H)) + 2 * (8 * b * E) ≤
        (1 - 2 ^ 21 * A * (6 / 5 * H)) ^ 2 * (19 / 1000 * E) ∧
      10 * (2 ^ 21 * A) ≤ chainK * A ∧ chainK * A * (6 / 5 * H) ≤ 1 / 2 := by
  have hg := base_g_le hb1 hAH
  refine ⟨?_, by linarith, base_dom hb1 hE0 hg, ?_, step_window hb1 hA hH hAH⟩
  · have e : 10 * (2 ^ 21 * A) * (6 / 5 * H) = 10 * (2 ^ 21 * A * (6 / 5 * H)) := by ring
    rw [e]; linarith
  · rw [chainK_eq]; linarith

end AVRegularity.Providers.ComplexFlow
end

section
open Complex MeasureTheory Set
open scoped Interval
namespace AVRegularity.Providers.ComplexFlow

/-! **Fourier decay of periodic functions holomorphic on a strip** (the final-phase modes of a
function holomorphic on `|Im ζ_q| < w` decay like `e^{-2π w|h|}`). For a `1`-periodic `g`
holomorphic and bounded by `M` on the strip `|Im z| < w`, the `h`-th Fourier coefficient
`∫_0^1 g(s) e^{-2πihs} ds` is at most `M e^{-2π w'|h|}` for every `0 ≤ w' < w`
(`norm_fourierCoeff_le_of_strip`). The proof shifts the segment `[0,1]` to `[0,1] ∓ i w'` (Cauchy's
theorem on a rectangle, `integral_shift_of_periodic`); the vertical sides cancel by periodicity. -/

/-- **Shift of the period segment** for a `1`-periodic function holomorphic on the rectangle. -/
theorem integral_shift_of_periodic {F : ℂ → ℂ} {c : ℝ}
    (hF : DifferentiableOn ℂ F ([[(0 : ℝ), 1]] ×ℂ [[(0 : ℝ), c]]))
    (hper : ∀ y ∈ [[(0 : ℝ), c]], F (1 + y * I) = F (y * I)) :
    ∫ x in (0 : ℝ)..1, F x = ∫ x in (0 : ℝ)..1, F (x + c * I) := by
  have h := integral_boundary_rect_eq_zero_of_differentiableOn F 0 (1 + c * I)
    (by simpa using hF)
  simp only [zero_re, zero_im, add_re, one_re, mul_re, I_re, mul_zero, ofReal_re, I_im,
    mul_one, sub_self, add_zero, add_im, one_im, mul_im, ofReal_im, zero_add, ofReal_zero,
    zero_mul, ofReal_one] at h
  have hv : ∫ y in (0 : ℝ)..c, F (1 + y * I) = ∫ y in (0 : ℝ)..c, F (y * I) :=
    intervalIntegral.integral_congr fun y hy => hper y hy
  rw [hv, add_sub_cancel_right, sub_eq_zero] at h
  exact h

/-- **Fourier decay on a strip.** -/
theorem norm_fourierCoeff_le_of_strip {g : ℂ → ℂ} {w M : ℝ}
    (hg : DifferentiableOn ℂ g {z : ℂ | |z.im| < w})
    (hper : ∀ z : ℂ, |z.im| < w → g (z + 1) = g z)
    (hM : ∀ z : ℂ, |z.im| < w → ‖g z‖ ≤ M) (h : ℤ) {w' : ℝ} (hw' : 0 ≤ w') (hw'w : w' < w) :
    ‖∫ s in (0 : ℝ)..1, g s * Complex.exp (-(2 * Real.pi * I * h * s))‖ ≤
      M * Real.exp (-(2 * Real.pi * w' * |(h : ℝ)|)) := by
  set F : ℂ → ℂ := fun z => g z * Complex.exp (-(2 * Real.pi * I * h * z)) with hF_def
  set c : ℝ := if 0 ≤ h then -w' else w' with hc_def
  have hc : |c| = w' := by
    rw [hc_def]; split_ifs <;> simp [abs_of_nonneg hw']
  have hy : ∀ y ∈ [[(0 : ℝ), c]], |y| ≤ w' := by
    intro y hy
    rw [← hc]
    rcases Set.mem_uIcc.1 hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [abs_of_nonneg h1]; exact h2.trans (le_abs_self c)
    · rw [abs_of_nonpos h2]; linarith [neg_abs_le c]
  have hrect : [[(0 : ℝ), 1]] ×ℂ [[(0 : ℝ), c]] ⊆ {z : ℂ | |z.im| < w} := fun z hz =>
    lt_of_le_of_lt (hy _ ((mem_reProdIm.1 hz).2)) hw'w
  have hexp : Differentiable ℂ fun z : ℂ => Complex.exp (-(2 * Real.pi * I * h * z)) := by
    fun_prop
  have hFd : DifferentiableOn ℂ F {z : ℂ | |z.im| < w} := hg.mul hexp.differentiableOn
  have hper' : ∀ y ∈ [[(0 : ℝ), c]], F (1 + y * I) = F (y * I) := by
    intro y hy'
    have hyI : |((y : ℂ) * I).im| < w := by
      simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
      exact lt_of_le_of_lt (hy y hy') hw'w
    have hg1 : g (1 + y * I) = g (y * I) := by rw [add_comm]; exact hper _ hyI
    have he : Complex.exp (-(2 * Real.pi * I * h * (1 + y * I))) =
        Complex.exp (-(2 * Real.pi * I * h * (y * I))) := by
      have e1 : -(2 * Real.pi * I * h * (1 + y * I)) =
          -(2 * Real.pi * I * h * (y * I)) + ((-h : ℤ) : ℂ) * (2 * Real.pi * I) := by
        push_cast; ring
      rw [e1, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    simp only [hF_def, hg1, he]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simpa using hw'.trans_lt hw'w))
  have hbound : ∀ x : ℝ, ‖F (x + c * I)‖ ≤ M * Real.exp (-(2 * Real.pi * w' * |(h : ℝ)|)) := by
    intro x
    have him : |((x : ℂ) + c * I).im| < w := by
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
        add_zero, zero_add]
      rw [hc]; exact hw'w
    have hre : (-(2 * Real.pi * I * h * ((x : ℂ) + c * I))).re = 2 * Real.pi * h * c := by
      simp only [neg_re, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, add_re, add_im,
        intCast_re, intCast_im]
      norm_num
    have hc' : 2 * Real.pi * h * c = -(2 * Real.pi * w' * |(h : ℝ)|) := by
      rw [hc_def]
      split_ifs with h0
      · have : (0 : ℝ) ≤ h := by exact_mod_cast h0
        rw [abs_of_nonneg this]; ring
      · have : (h : ℝ) < 0 := by exact_mod_cast not_le.1 h0
        rw [abs_of_neg this]; ring
    show ‖g (x + c * I) * Complex.exp (-(2 * Real.pi * I * h * (x + c * I)))‖ ≤ _
    rw [norm_mul, Complex.norm_exp, hre, hc']
    exact mul_le_mul_of_nonneg_right (hM _ him) (Real.exp_pos _).le
  have hshift := integral_shift_of_periodic (hFd.mono hrect) hper'
  show ‖∫ s in (0 : ℝ)..1, F s‖ ≤ _
  rw [hshift]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun x : ℝ => F (x + c * I)) fun x _ => hbound x
  simpa using this

end AVRegularity.Providers.ComplexFlow
end

section
open Set Homogenization
namespace AVRegularity.Providers.ComplexFlow

/-! **The time windows of the families of a scheduled chain**. The family anchored at the renewal
anchor `s_𝗉` of a slot `𝗉` of level `k` uses the window `[s_𝗉 - 3h_k/5, s_𝗉 + 3h_k/5]` (`slotWin`),
`h_k = τ_k''`. It contains every time where the cutoff `ϖ_𝗉` is nonzero (`mem_slotWin_of_cutoff`),
and the window of a slot scheduled in `𝗉` lies in it once `h_{k+1} < τ_k/48` (`slotWin_subset`), the
history separation of the carrier start. The anchor is within `h_k/2 + τ_k/2` of the center `kτ_k`
of the slot (`label_bounds`), and `τ_k ≤ h_k/25`. -/

/-- The window of the family anchored at the slot `p` of level `k`. -/
def slotWin (D : OCData) (k : ℕ) (p : ℤ) : Set ℝ :=
  Icc (D.slotAnchor k p - 3 / 5 * ocTauPP D.α D.q D.Λ k)
    (D.slotAnchor k p + 3 / 5 * ocTauPP D.α D.q D.Λ k)

variable (D : OCData)

theorem anchor_mem_slotWin (hΛ : 1 ≤ D.Λ) (k : ℕ) (p : ℤ) : D.slotAnchor k p ∈ slotWin D k p := by
  have h0 : 0 < ocTauPP D.α D.q D.Λ k := Construction.Stream.ocTauPP_pos hΛ
  constructor <;> linarith

theorem abs_sub_le_of_mem_slotWin {k : ℕ} {p : ℤ} {u r : ℝ} (hu : u ∈ slotWin D k p)
    (hr : r ∈ slotWin D k p) : |u - r| ≤ 6 / 5 * ocTauPP D.α D.q D.Λ k := by
  rw [abs_le]
  constructor <;> linarith [hu.1, hu.2, hr.1, hr.2]

theorem tau_le (hΛ : 1 ≤ D.Λ) (k : ℕ) : ocTau D.α D.q D.Λ k ≤ ocTauPP D.α D.q D.Λ k / 25 := by
  have hh0 : 0 < ocTauPP D.α D.q D.Λ k := Construction.Stream.ocTauPP_pos hΛ
  have hL := ChildInert.ocL_ge_five D.α D.q hΛ k
  have hτeq : ocTau D.α D.q D.Λ k = ocTauPP D.α D.q D.Λ k / (ocL D.α D.q D.Λ k : ℝ) ^ 2 := rfl
  rw [hτeq]
  apply div_le_div_of_nonneg_left hh0.le (by norm_num)
  nlinarith

/-- The anchor is within `h/2 + τ/2` of the center of the slot. -/
theorem label_bounds (hΛ : 1 ≤ D.Λ) (k : ℕ) (p : ℤ) :
    -(ocTauPP D.α D.q D.Λ k - ocTau D.α D.q D.Λ k) / 2 ≤
        (p : ℝ) * ocTau D.α D.q D.Λ k - D.slotAnchor k p ∧
      (p : ℝ) * ocTau D.α D.q D.Λ k - D.slotAnchor k p <
        (ocTauPP D.α D.q D.Λ k + ocTau D.α D.q D.Λ k) / 2 := by
  set h := ocTauPP D.α D.q D.Λ k
  set τ := ocTau D.α D.q D.Λ k
  have hh0 : 0 < h := Construction.Stream.ocTauPP_pos hΛ
  set l := ocLabel D.α D.q D.Λ k p
  have hf1 : (l : ℝ) ≤ ((p : ℝ) * τ + (h - τ) / 2) / h := Int.floor_le _
  have hf2 : ((p : ℝ) * τ + (h - τ) / 2) / h < l + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ hh0] at hf1
  rw [div_lt_iff₀ hh0] at hf2
  have hs : D.slotAnchor k p = (l : ℝ) * h := rfl
  rw [hs]
  constructor <;> nlinarith

/-- Times of the output window are within `h/2 + 85τ/48` of the anchor. -/
theorem abs_sub_anchor_le_of_mem_window (hΛ : 1 ≤ D.Λ) {k : ℕ} {p : ℤ} {t : ℝ}
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ k p) :
    |t - D.slotAnchor k p| ≤ ocTauPP D.α D.q D.Λ k / 2 + 85 / 48 * ocTau D.α D.q D.Λ k := by
  have hτ0 : 0 < ocTau D.α D.q D.Λ k := Construction.Stream.ocTau_pos hΛ
  obtain ⟨h1, h2⟩ := label_bounds D hΛ k p
  have ht1 := ht.1
  have ht2 := ht.2
  rw [abs_le]
  constructor <;> nlinarith

/-- Times where the cutoff is nonzero are within `h/2 + 7τ/4` of the anchor. -/
theorem abs_sub_anchor_lt_of_cutoff (hΛ : 1 ≤ D.Λ) {k : ℕ} {p : ℤ} {t : ℝ}
    (hc : ocCutoff D.α D.q D.Λ k p t ≠ 0) :
    |t - D.slotAnchor k p| < ocTauPP D.α D.q D.Λ k / 2 + 7 / 4 * ocTau D.α D.q D.Λ k := by
  set τ := ocTau D.α D.q D.Λ k with hτdef
  have hτ0 : 0 < τ := Construction.Stream.ocTau_pos hΛ
  have hpos : 0 < 5 / 2 - 2 * |t - (p : ℝ) * τ| / τ := by
    by_contra hneg
    exact hc (Real.smoothTransition.zero_of_nonpos (not_lt.1 hneg))
  have habs : |t - (p : ℝ) * τ| < 5 * τ / 4 := by
    have h1 : 2 * |t - (p : ℝ) * τ| / τ < 5 / 2 := by linarith
    rw [div_lt_iff₀ hτ0] at h1
    linarith
  obtain ⟨h1, h2⟩ := label_bounds D hΛ k p
  have habs' := abs_lt.1 habs
  rw [abs_lt]
  constructor <;> linarith [habs'.1, habs'.2]

/-- **The window contains the support of the cutoff.** -/
theorem mem_slotWin_of_cutoff (hΛ : 1 ≤ D.Λ) {k : ℕ} {p : ℤ} {t : ℝ}
    (hc : ocCutoff D.α D.q D.Λ k p t ≠ 0) : t ∈ slotWin D k p := by
  have h1 := abs_sub_anchor_lt_of_cutoff D hΛ hc
  have h2 := tau_le D hΛ k
  have h0 : 0 < ocTau D.α D.q D.Λ k := Construction.Stream.ocTau_pos hΛ
  have h1' := abs_lt.1 h1
  constructor <;> linarith [h1'.1, h1'.2]

/-- **The windows of scheduled slots are nested.** -/
theorem slotWin_subset (hΛ : 1 ≤ D.Λ) {k : ℕ} {p' p : ℤ} (hs : IsScheduledIn D k p' p)
    (hsep : ocTauPP D.α D.q D.Λ (k + 1) < ocTau D.α D.q D.Λ k / 48) :
    slotWin D (k + 1) p' ⊆ slotWin D k p := by
  obtain ⟨t₀, ht₀c, ht₀w⟩ := hs
  have hc : ocCutoff D.α D.q D.Λ (k + 1) p' t₀ ≠ 0 := ht₀c
  have h1 := abs_lt.1 (abs_sub_anchor_lt_of_cutoff D hΛ hc)
  have h2 := abs_le.1 (abs_sub_anchor_le_of_mem_window D hΛ ht₀w)
  have h3 := tau_le D hΛ k
  have h4 := tau_le D hΛ (k + 1)
  have h0 : 0 < ocTau D.α D.q D.Λ (k + 1) := Construction.Stream.ocTau_pos hΛ
  intro u hu
  obtain ⟨hu1, hu2⟩ := hu
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

end AVRegularity.Providers.ComplexFlow
end

section
open MeasureTheory Set Filter Topology Homogenization AVenhance
open scoped Interval
namespace AVRegularity.Providers.ComplexFlow

/-! **The complex shear velocity and the complex relative displacement.**
* `ocShearVelC`: the entire extension of the shear velocity `𝐮_{m,k} = ∇^⊥ψ_{m,k}`; for odd `k` it
  points in the parallel direction and depends only on the transverse coordinate
  (`ocShearVelC_ofRealVec`, `norm_ocShearVelC_le`).
* `relDispC`: the entire extension in `θ` of the relative displacement
  `d_k(u; s, θ) = ε_k⁻¹ (∫_s^u p_{k,p}) 𝐮_{k,p}(ε_k θ)` (`relDispC_ofRealVec`), with
  `|ε_k d_k| ≤ 2π ε_k^α |u - s| e^{2π|Im θ_q|}` (`norm_smul_relDispC_le`). -/

/-- The amplitude `2π ε_m^{1+α}/ε_m` of the shear velocity. -/
def shearAmp (α q : ℝ) (Λ m : ℕ) : ℝ :=
  2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) * (ocEpsilon q Λ m)⁻¹

/-- The frequency `2π/ε_m` of the shear. -/
def shearFreq (q : ℝ) (Λ m : ℕ) : ℝ := 2 * Real.pi * (ocEpsilon q Λ m)⁻¹

/-- **The entire extension of the shear velocity.** -/
def ocShearVelC (α q : ℝ) (Λ m : ℕ) (k : ℤ) (w : CVec) : CVec :=
  if k % 4 = 1 then ![0, (shearAmp α q Λ m : ℂ) * Complex.cos ((shearFreq q Λ m : ℂ) * w 0)]
  else if k % 4 = 3 then
    ![-((shearAmp α q Λ m : ℂ) * Complex.cos ((shearFreq q Λ m : ℂ) * w 1)), 0]
  else 0

theorem ocShearVel_even {α q : ℝ} {Λ m : ℕ} {k : ℤ} (h1 : k % 4 ≠ 1) (h3 : k % 4 ≠ 3) (y : Vec 2) :
    ocShearVel α q Λ m k y = 0 := by
  have hψ : ocShear α q Λ m k = fun _ => 0 := by
    funext z
    unfold ocShear psi0
    rw [ite_eq_right h1, ite_eq_right h3, mul_zero]
  unfold ocShearVel
  rw [hψ]
  exact streamVel_zero 0 y

theorem ocShearVelC_ofRealVec (α q : ℝ) (Λ m : ℕ) (k : ℤ) (y : Vec 2) :
    ocShearVelC α q Λ m k (ofRealVec y) = ofRealVec (ocShearVel α q Λ m k y) := by
  unfold ocShearVelC
  split_ifs with h1 h3
  · rw [CycleReference.ocShearVel_horizontal h1]
    funext a
    fin_cases a <;> simp [ofRealVec, shearAmp, shearFreq, Complex.ofReal_cos]
  · rw [CycleReference.ocShearVel_vertical h3]
    funext a
    fin_cases a <;> simp [ofRealVec, shearAmp, shearFreq, Complex.ofReal_cos]
  · rw [ocShearVel_even h1 h3]
    funext a
    simp [ofRealVec]

theorem differentiable_ocShearVelC (α q : ℝ) (Λ m : ℕ) (k : ℤ) :
    Differentiable ℂ (ocShearVelC α q Λ m k) := by
  unfold ocShearVelC
  split_ifs
  · refine differentiable_pi.mpr fun a => ?_
    fin_cases a
    · exact differentiable_const _
    · exact (differentiable_const _).mul
        (Complex.differentiable_cos.comp ((differentiable_const _).mul (differentiable_apply 0)))
  · refine differentiable_pi.mpr fun a => ?_
    fin_cases a
    · exact ((differentiable_const _).mul
        (Complex.differentiable_cos.comp ((differentiable_const _).mul (differentiable_apply 1)))).neg
    · exact differentiable_const _
  · exact differentiable_const _

/-- `|cos z| ≤ e^{|Im z|}`. -/
theorem norm_cos_le (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  have e : Complex.cos z = Complex.sin (z + Real.pi / 2) := by
    rw [Complex.sin_add_pi_div_two]
  rw [e]
  refine (norm_sin_le _).trans (le_of_eq ?_)
  congr 2
  simp

theorem shearAmp_nonneg {α q : ℝ} {Λ m : ℕ} (hε : 0 < ocEpsilon q Λ m) : 0 ≤ shearAmp α q Λ m := by
  unfold shearAmp
  have := Real.rpow_nonneg hε.le (1 + α)
  positivity

theorem shearFreq_pos {q : ℝ} {Λ m : ℕ} (hε : 0 < ocEpsilon q Λ m) : 0 < shearFreq q Λ m := by
  unfold shearFreq
  positivity

/-- **The bound of the complex shear velocity** by the transverse imaginary part. -/
theorem norm_ocShearVelC_le (α q : ℝ) (Λ m : ℕ) (k : ℤ) (hε : 0 < ocEpsilon q Λ m) (w : CVec) :
    ‖ocShearVelC α q Λ m k w‖ ≤
      shearAmp α q Λ m * Real.exp (shearFreq q Λ m * |(w (transverseIndex k)).im|) := by
  have hA := shearAmp_nonneg (α := α) hε
  have hF := shearFreq_pos (q := q) (m := m) hε
  have hb : ∀ a : Fin 2, ‖(shearAmp α q Λ m : ℂ) * Complex.cos ((shearFreq q Λ m : ℂ) * w a)‖ ≤
      shearAmp α q Λ m * Real.exp (shearFreq q Λ m * |(w a).im|) := by
    intro a
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA]
    refine mul_le_mul_of_nonneg_left ((norm_cos_le _).trans (le_of_eq ?_)) hA
    congr 1
    rw [Complex.im_ofReal_mul, abs_mul, abs_of_pos hF]
  have h0 : 0 ≤ shearAmp α q Λ m * Real.exp (shearFreq q Λ m * |(w (transverseIndex k)).im|) :=
    mul_nonneg hA (Real.exp_pos _).le
  unfold ocShearVelC
  split_ifs with h1 h3
  · have hq : transverseIndex k = 0 := by unfold transverseIndex; rw [ite_eq_right (by omega)]
    rw [hq] at h0 ⊢
    refine (pi_norm_le_iff_of_nonneg h0).mpr fun a => ?_
    fin_cases a
    · simpa using h0
    · exact hb 0
  · have hq : transverseIndex k = 1 := by unfold transverseIndex; rw [ite_eq_left h3]
    rw [hq] at h0 ⊢
    refine (pi_norm_le_iff_of_nonneg h0).mpr fun a => ?_
    fin_cases a
    · simpa only [Fin.zero_eta, Matrix.cons_val_zero, norm_neg] using hb 1
    · simpa using h0
  · simpa using h0

/-! ### The complex relative displacement -/

/-- **The complex relative displacement** `d_i(u; s, θ)` of the pulse `p` of level `i`. -/
def relDispC (D : OCData) (i : ℕ) (p : ℤ) (u s : ℝ) (θ : CVec) : CVec :=
  (((D.eps i)⁻¹ * ∫ v in s..u, ocPulse D.α D.q D.Λ D.ζ i p v : ℝ) : ℂ) •
    ocShearVelC D.α D.q D.Λ i p (((D.eps i : ℝ) : ℂ) • θ)

theorem relDispC_ofRealVec (D : OCData) (i : ℕ) (p : ℤ) (u s : ℝ) (θ : Vec 2) :
    relDispC D i p u s (ofRealVec θ) = ofRealVec (D.relDisp i p u s θ) := by
  have e : (((D.eps i : ℝ) : ℂ) • ofRealVec θ) = ofRealVec (D.eps i • θ) := by
    funext a
    simp [ofRealVec]
  unfold relDispC OCData.relDisp
  rw [e, ocShearVelC_ofRealVec]
  funext a
  simp [ofRealVec, OCData.eps, mul_assoc]

theorem differentiable_relDispC (D : OCData) (i : ℕ) (p : ℤ) (u s : ℝ) :
    Differentiable ℂ (relDispC D i p u s) := by
  unfold relDispC
  have h1 : Differentiable ℂ (fun θ : CVec => ocShearVelC D.α D.q D.Λ i p (((D.eps i : ℝ) : ℂ) • θ)) :=
    (differentiable_ocShearVelC _ _ _ _ _).comp
      ((differentiable_id (𝕜 := ℂ) (E := CVec)).const_smul (((D.eps i : ℝ) : ℂ)))
  exact h1.const_smul ((((D.eps i)⁻¹ * ∫ v in s..u, ocPulse D.α D.q D.Λ D.ζ i p v : ℝ) : ℂ))

theorem abs_integral_pulse_le (D : OCData) (hζ : IsFastProfile D.ζ) (i : ℕ) (p : ℤ) (u s : ℝ) :
    |∫ v in s..u, ocPulse D.α D.q D.Λ D.ζ i p v| ≤ |u - s| := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := u) (C := 1)
    (f := fun v => ocPulse D.α D.q D.Λ D.ζ i p v) fun v _ => by
      unfold ocPulse slowEnvelope
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg
        (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)) (hζ.2.2.2.1 _).1)]
      calc _ ≤ (1 : ℝ) * 1 * 1 := by
            refine mul_le_mul (mul_le_mul (Real.smoothTransition.le_one _)
              (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _) zero_le_one)
              (hζ.2.2.2.1 _).2 (hζ.2.2.2.1 _).1 (by norm_num)
        _ = 1 := by norm_num
  rw [Real.norm_eq_abs, one_mul] at h
  exact h

/-- **The bound of the complex displacement** `ε_i d_i` by the transverse imaginary part of the
phase. -/
theorem norm_smul_relDispC_le (D : OCData) (hζ : IsFastProfile D.ζ) {i : ℕ} (hε : 0 < D.eps i) (p : ℤ)
    (u s : ℝ) (θ : CVec) :
    ‖((D.eps i : ℝ) : ℂ) • relDispC D i p u s θ‖ ≤
      |u - s| * (shearAmp D.α D.q D.Λ i *
        Real.exp (shearFreq D.q D.Λ i * (D.eps i * |(θ (transverseIndex p)).im|))) := by
  unfold relDispC
  rw [smul_smul, norm_smul, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs,
    ← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul]
  have hv := norm_ocShearVelC_le D.α D.q D.Λ i p hε (((D.eps i : ℝ) : ℂ) • θ)
  have him : |((((D.eps i : ℝ) : ℂ) • θ) (transverseIndex p)).im| =
      D.eps i * |(θ (transverseIndex p)).im| := by
    rw [Pi.smul_apply, smul_eq_mul, Complex.im_ofReal_mul, abs_mul, abs_of_pos hε]
  rw [him] at hv
  exact mul_le_mul (abs_integral_pulse_le D hζ i p u s) hv (norm_nonneg _) (abs_nonneg _)

end AVRegularity.Providers.ComplexFlow
end

section
open MeasureTheory Set Filter Topology Homogenization AVenhance Metric
open scoped Interval
namespace AVRegularity.Providers.ComplexFlow

/-! **Properties of the complex shear and displacement** used by the child step of the chain
induction: for an odd pulse `p` with transverse coordinate `q`,
* the shear velocity has no transverse component and depends only on the transverse coordinate
  (`ocShearVelC_transverse`, `ocShearVelC_add_of_transverse`), and the displacement has no
  transverse component (`relDispC_transverse`);
* the derivative of the shear velocity obeys Cauchy's estimate (`norm_fderiv_ocShearVelC_le`). -/

open AVRegularity.Providers.GenSem

theorem ocShearVelC_transverse (α q : ℝ) (Λ m : ℕ) (k : ℤ) (w : CVec) :
    ocShearVelC α q Λ m k w (transverseIndex k) = 0 := by
  unfold ocShearVelC transverseIndex
  split_ifs with h1 h3 h3' <;> first | omega | simp

theorem ocShearVelC_add_of_transverse (α q : ℝ) (Λ m : ℕ) (k : ℤ) (w v : CVec)
    (hv : v (transverseIndex k) = 0) : ocShearVelC α q Λ m k (w + v) = ocShearVelC α q Λ m k w := by
  unfold ocShearVelC
  unfold transverseIndex at hv
  split_ifs with h1 h3
  · rw [ite_eq_right (by omega)] at hv
    simp [hv]
  · rw [ite_eq_left h3] at hv
    simp [hv]
  · rfl

theorem relDispC_transverse (D : OCData) (i : ℕ) (p : ℤ) (u s : ℝ) (θ : CVec) :
    relDispC D i p u s θ (transverseIndex p) = 0 := by
  unfold relDispC
  rw [Pi.smul_apply, ocShearVelC_transverse, smul_zero]

theorem continuous_ocPulse (D : OCData) (hζ : IsFastProfile D.ζ) (i : ℕ) (p : ℤ) :
    Continuous (ocPulse D.α D.q D.Λ D.ζ i p) := by
  unfold ocPulse slowEnvelope
  refine ((Real.smoothTransition.continuous.comp ?_).mul
    (Real.smoothTransition.continuous.comp ?_)).mul (hζ.1.continuous.comp ?_) <;> fun_prop

/-- A bound of a vector-valued derivative by the bounds of its coordinates. -/
theorem norm_fderiv_le_of_coord {f : CVec → CVec} {w : CVec} (hf : DifferentiableAt ℂ f w)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ c : Fin 2, ‖fderiv ℂ (fun z => f z c) w‖ ≤ M) :
    ‖fderiv ℂ f w‖ ≤ M := by
  refine ContinuousLinearMap.opNorm_le_bound _ hM0 fun v => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun c => ?_
  have h2 : HasFDerivAt (fun z => f z c)
      ((ContinuousLinearMap.proj c : CVec →L[ℂ] ℂ).comp (fderiv ℂ f w)) w :=
    ((ContinuousLinearMap.proj c : CVec →L[ℂ] ℂ).hasFDerivAt).comp w hf.hasFDerivAt
  have e : fderiv ℂ f w v c = fderiv ℂ (fun z => f z c) w v := by rw [h2.fderiv]; rfl
  rw [e]
  exact ((fderiv ℂ (fun z => f z c) w).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hM c)
    (norm_nonneg _))

/-- **Cauchy's estimate for the derivative of the shear velocity.** -/
theorem norm_fderiv_ocShearVelC_le (α q : ℝ) (Λ m : ℕ) (k : ℤ) (hε : 0 < ocEpsilon q Λ m)
    (w : CVec) :
    ‖fderiv ℂ (ocShearVelC α q Λ m k) w‖ ≤ shearAmp α q Λ m * shearFreq q Λ m *
      Real.exp (shearFreq q Λ m * |(w (transverseIndex k)).im| + 1) := by
  have hF := shearFreq_pos (q := q) (m := m) hε
  have hA := shearAmp_nonneg (α := α) hε
  have hρ : 0 < (shearFreq q Λ m)⁻¹ := inv_pos.mpr hF
  refine norm_fderiv_le_of_coord ((differentiable_ocShearVelC _ _ _ _ _) w) (by positivity)
    fun c => ?_
  have hdc : Differentiable ℂ (fun z => ocShearVelC α q Λ m k z c) := fun z =>
    (ContinuousLinearMap.proj c : CVec →L[ℂ] ℂ).differentiableAt.comp z
      ((differentiable_ocShearVelC _ _ _ _ _) z)
  have h := norm_fderiv_le_of_closedBall hρ hdc.differentiableOn (M := shearAmp α q Λ m *
      Real.exp (shearFreq q Λ m * |(w (transverseIndex k)).im| + 1)) fun z hz => by
    refine (norm_le_pi_norm _ c).trans ((norm_ocShearVelC_le α q Λ m k hε z).trans ?_)
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hA
    have hzw : |(z (transverseIndex k)).im - (w (transverseIndex k)).im| ≤ (shearFreq q Λ m)⁻¹ := by
      rw [mem_closedBall, dist_eq_norm] at hz
      have e : (z (transverseIndex k)).im - (w (transverseIndex k)).im =
          ((z - w) (transverseIndex k)).im := by simp
      rw [e]
      exact (Complex.abs_im_le_norm _).trans ((norm_le_pi_norm (z - w) _).trans hz)
    have h1 : |(z (transverseIndex k)).im| ≤ |(w (transverseIndex k)).im| + (shearFreq q Λ m)⁻¹ := by
      have := abs_sub_abs_le_abs_sub (z (transverseIndex k)).im (w (transverseIndex k)).im
      linarith
    calc shearFreq q Λ m * |(z (transverseIndex k)).im|
        ≤ shearFreq q Λ m * (|(w (transverseIndex k)).im| + (shearFreq q Λ m)⁻¹) :=
          mul_le_mul_of_nonneg_left h1 hF.le
      _ = shearFreq q Λ m * |(w (transverseIndex k)).im| + 1 := by
          rw [mul_add, mul_inv_cancel₀ hF.ne']
  rw [div_inv_eq_mul] at h
  calc _ ≤ shearAmp α q Λ m * Real.exp (shearFreq q Λ m * |(w (transverseIndex k)).im| + 1) *
        shearFreq q Λ m := h
    _ = _ := by ring

end AVRegularity.Providers.ComplexFlow
end

section
open MeasureTheory Set Filter Topology Homogenization AVenhance
namespace AVRegularity.Providers.ComplexFlow

/-! **The complex geometry of a chain**. The real geometry of a chain (`RealChain.geom`) is the
explicit offset-flow recursion `𝔛'(u,x,r) = 𝔛(u, Z_γ(u; r, 𝔛(s,x,r)), s)`,
`x_{𝒜'} = 𝔛(s', x_𝒜 + c, s)` from the base flow `X_{j'-1}`. Its complex version uses the same
recursion with complex parameters (base label, centers, phases), the complex base flow `cflow` of
the complex velocity `velC` (`baseFlowC`) and the complex displacement `relDispC`:
* `childGeomC`, `geomAuxC`, `geomC`: the complex geometry of the last family of a chain with
  discrete data `dd` and complex parameters `x : ChainParamsC n`;
* `CGeomAgree G gC g`: the complex geometry restricts to the real one at real points, for times
  in `G`; it passes from a parent to a child (`childGeomC_agree`) and along the chain
  (`geomAuxC_agree`) when the anchors lie in `G`. -/

/-- A complex family geometry: the offset flow `𝔛(u, x, r)`, the center point `x_𝒜` and the
anchor `s`. -/
abbrev CGeom : Type := (ℝ → CVec → ℝ → CVec) × CVec × ℝ

/-- The real number `ε_k` as a complex scalar. -/
def epsC (D : OCData) (k : ℕ) : ℂ := ((D.eps k : ℝ) : ℂ)

/-- The real number `ε_k⁻¹` as a complex scalar. -/
def epsInvC (D : OCData) (k : ℕ) : ℂ := (((D.eps k)⁻¹ : ℝ) : ℂ)

/-- **The complex child geometry** of level `k` (pulse `pk`, anchor `s'`, center `c.1`,
phase `c.2`) of a family with complex geometry `g`. -/
def childGeomC (D : OCData) (k : ℕ) (pk : ℤ) (s' : ℝ) (c : CVec × CVec) (g : CGeom) : CGeom :=
  (fun u x r => g.1 u (g.1 g.2.2 x r + epsC D k • relDispC D k pk u r
      (epsInvC D k • g.1 g.2.2 x r + (c.2 - epsInvC D k • (g.2.1 + c.1)))) g.2.2,
    g.1 s' (g.2.1 + c.1) g.2.2, s')

/-- The complex geometry after the children `cs` of levels `k, k+1, …`. -/
def geomAuxC (D : OCData) : ℕ → List ℤ → List (CVec × CVec) → CGeom → CGeom
  | k, pk :: pk1 :: rest, c :: cs, g =>
      geomAuxC D (k + 1) (pk1 :: rest) cs (childGeomC D k pk (D.slotAnchor (k + 1) pk1) c g)
  | _, _, _, g => g

/-- The width of the closed strip of the complex base flow of level `k`. -/
def baseW (D : OCData) (k : ℕ) : ℝ := 19 / 1000 * D.eps k

/-- **The complex base flow** `X^ℂ_k` of level `k`. -/
def baseFlowC (D : OCData) (k : ℕ) : ℝ → CVec → ℝ → CVec :=
  cflow (velC D.α D.q D.Λ D.ζ k) (baseW D k)

/-- **The complex geometry of the last family of a chain** with discrete data `dd` and complex
parameters `x`. -/
def geomC (D : OCData) (dd : ChainData) {n : ℕ} (x : ChainParamsC n) : CGeom :=
  geomAuxC D (dd.baseLevel + 1) dd.slots (List.ofFn x.2.1)
    (baseFlowC D dd.baseLevel, x.1, D.slotAnchor (dd.baseLevel + 1) (dd.slots.headD 0))

/-! ### Agreement with the real geometry -/

/-- The complex parameters of a real child. -/
def _root_.AVRegularity.ChainChild.toC (c : ChainChild) : CVec × CVec :=
  (ofRealVec c.center, ofRealVec c.phase)

/-- **The complex geometry restricts to the real one** at real points, for times in `G`. -/
structure CGeomAgree (G : Set ℝ) (gC : CGeom) (g : ChainGeom) : Prop where
  center : gC.2.1 = ofRealVec g.2.1
  anchor : gC.2.2 = g.2.2
  flow : ∀ u ∈ G, ∀ r ∈ G, ∀ y, gC.1 u (ofRealVec y) r = ofRealVec (g.1 u y r)

theorem ofRealVec_add (x y : Vec 2) : ofRealVec (x + y) = ofRealVec x + ofRealVec y := by
  funext a
  simp [ofRealVec]

theorem ofRealVec_sub (x y : Vec 2) : ofRealVec (x - y) = ofRealVec x - ofRealVec y := by
  funext a
  simp [ofRealVec]

theorem ofRealVec_smul (c : ℝ) (x : Vec 2) : ofRealVec (c • x) = ((c : ℝ) : ℂ) • ofRealVec x := by
  funext a
  simp [ofRealVec]

/-- **Agreement passes from a parent to a child.** -/
theorem childGeomC_agree (D : OCData) {G : Set ℝ} {gC : CGeom} {g : ChainGeom}
    (h : CGeomAgree G gC g) (hs : g.2.2 ∈ G) (k : ℕ) (pk : ℤ) {s' : ℝ} (hs' : s' ∈ G)
    (c : ChainChild) :
    CGeomAgree G (childGeomC D k pk s' c.toC gC) (D.childGeom k pk s' c g) where
  center := by
    show gC.1 s' (gC.2.1 + ofRealVec c.center) gC.2.2 = ofRealVec (g.1 s' (g.2.1 + c.center) g.2.2)
    rw [h.center, h.anchor, ← ofRealVec_add, h.flow s' hs' g.2.2 hs]
  anchor := rfl
  flow := by
    intro u hu r hr y
    show gC.1 u (gC.1 gC.2.2 (ofRealVec y) r + epsC D k • relDispC D k pk u r
      (epsInvC D k • gC.1 gC.2.2 (ofRealVec y) r +
        (ofRealVec c.phase - epsInvC D k • (gC.2.1 + ofRealVec c.center)))) gC.2.2 =
      ofRealVec (g.1 u ((g.1 g.2.2 y r) + D.eps k • D.relDisp k pk u r
        ((D.eps k)⁻¹ • (g.1 g.2.2 y r) + (c.phase - (D.eps k)⁻¹ • (g.2.1 + c.center)))) g.2.2)
    rw [h.anchor, h.center, h.flow g.2.2 hs r hr y]
    have e1 : epsInvC D k • ofRealVec (g.1 g.2.2 y r) +
        (ofRealVec c.phase - epsInvC D k • (ofRealVec g.2.1 + ofRealVec c.center)) =
        ofRealVec ((D.eps k)⁻¹ • (g.1 g.2.2 y r) + (c.phase - (D.eps k)⁻¹ • (g.2.1 + c.center))) := by
      rw [ofRealVec_add, ofRealVec_sub, ofRealVec_smul, ofRealVec_smul, ofRealVec_add]
      rfl
    rw [e1, relDispC_ofRealVec]
    have e2 : ofRealVec (g.1 g.2.2 y r) + epsC D k • ofRealVec (D.relDisp k pk u r
        ((D.eps k)⁻¹ • (g.1 g.2.2 y r) + (c.phase - (D.eps k)⁻¹ • (g.2.1 + c.center)))) =
        ofRealVec ((g.1 g.2.2 y r) + D.eps k • D.relDisp k pk u r
          ((D.eps k)⁻¹ • (g.1 g.2.2 y r) + (c.phase - (D.eps k)⁻¹ • (g.2.1 + c.center)))) := by
      rw [ofRealVec_add, ofRealVec_smul]
      rfl
    rw [e2, h.flow u hu g.2.2 hs]

/-- **Agreement along a chain**, when the anchors of the children lie in `G`. -/
theorem geomAuxC_agree (D : OCData) {G : Set ℝ} :
    ∀ (k : ℕ) (ps : List ℤ) (cs : List ChainChild) (gC : CGeom) (g : ChainGeom),
      CGeomAgree G gC g → g.2.2 ∈ G →
      (∀ j : ℕ, ∀ hj : j + 1 < ps.length, D.slotAnchor (k + j + 1) ps[j + 1] ∈ G) →
      CGeomAgree G (geomAuxC D k ps (cs.map ChainChild.toC) gC) (D.geomAux k ps cs g) ∧
        (D.geomAux k ps cs g).2.2 ∈ G := by
  intro k ps cs
  induction cs generalizing k ps with
  | nil =>
    intro gC g h hs _
    cases ps with
    | nil => exact ⟨h, hs⟩
    | cons p ps' =>
      cases ps' with
      | nil => exact ⟨h, hs⟩
      | cons p1 rest => exact ⟨h, hs⟩
  | cons c cs ih =>
    intro gC g h hs hG
    cases ps with
    | nil => exact ⟨h, hs⟩
    | cons p ps' =>
      cases ps' with
      | nil => exact ⟨h, hs⟩
      | cons p1 rest =>
        have hs' : D.slotAnchor (k + 1) p1 ∈ G := by
          simpa using hG 0 (by simp)
        have hc := childGeomC_agree D h hs k p hs' c
        refine ih (k + 1) (p1 :: rest) _ _ hc hs' fun j hj => ?_
        have := hG (j + 1) (by simp at hj ⊢; omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 j] using this

theorem toC_ofFn_paramsC (ch : RealChain) (ζ : Vec 2) :
    List.ofFn (ch.paramsC ζ).2.1 = ch.children.map ChainChild.toC := by
  refine List.ext_get (by simp) fun j h1 h2 => ?_
  simp only [RealChain.paramsC, List.get_eq_getElem, List.getElem_ofFn, List.getElem_map,
    ChainChild.toC]
  rfl

/-- **The complex geometry of a real chain restricts to its real geometry**, given the agreement
of the base flows and the anchors in `G`. -/
theorem geomC_agree (D : OCData) {G : Set ℝ} (ch : RealChain) (ζ : Vec 2)
    (hbase : ∀ u ∈ G, ∀ r ∈ G, ∀ y,
      baseFlowC D ch.baseLevel u (ofRealVec y) r = ofRealVec (D.flowOf ch.baseLevel u y r))
    (hs0 : D.slotAnchor (ch.baseLevel + 1) (ch.slots.headD 0) ∈ G)
    (hG : ∀ j : ℕ, ∀ hj : j + 1 < ch.slots.length,
      D.slotAnchor (ch.baseLevel + 1 + j + 1) ch.slots[j + 1] ∈ G) :
    CGeomAgree G (geomC D ch.data (ch.paramsC ζ)) (ch.geom D) ∧ (ch.geom D).2.2 ∈ G := by
  have h0 : CGeomAgree G (baseFlowC D ch.baseLevel, ofRealVec ch.base,
      D.slotAnchor (ch.baseLevel + 1) (ch.slots.headD 0))
      (D.flowOf ch.baseLevel, ch.base, D.slotAnchor (ch.baseLevel + 1) (ch.slots.headD 0)) :=
    ⟨rfl, rfl, hbase⟩
  have h := geomAuxC_agree D (ch.baseLevel + 1) ch.slots ch.children _ _ h0 hs0 hG
  unfold geomC RealChain.geom
  rw [toC_ofFn_paramsC]
  exact h

end AVRegularity.Providers.ComplexFlow
end

section
open MeasureTheory Set Filter Topology Homogenization Metric
namespace AVRegularity.Providers.ComplexFlow

/-! **Complex families over a parameter space**. A complex family over the parameter space
`Par` (`CFam`) is an offset flow `𝔛_P(u, y, r)`, a center point `x_P` and an anchor `s`; its center
is transported to the time `r` as `c_P(r) = 𝔛_P(r, x_P, s)` (`CFam.cur`). The invariants of the
induction along a chain (`CFam.OK`), for parameters in the open set `Ω` and times in `W` with
`|u - r| ≤ T`, on the balls of radius `ϱ` around the transported centers:
* joint holomorphy in the parameters and the point;
* the identity at equal times and the group law (on the quarter balls);
* the two-time Jacobian bound `‖D_y𝔛_P(u, y, r) - I‖ ≤ Λ|u - r|`, with `ΛT ≤ 1/2`.
Derived here: the transported centers are holomorphic in the parameters and are transported by
the flow (`cur_eq`), the flow is `(1 ± ΛT)`-bi-Lipschitz on the balls (`norm_fl_sub_sub_le`), maps
balls around centers to balls around centers (`fl_mem_ball`), and its derivative is
`4ΛT/ϱ`-Lipschitz on the half balls (`norm_fderiv_fl_sub_le`, Cauchy's estimate). -/

open AVRegularity.Providers.GenSem

/-- **A complex family over the parameter space `Par`.** -/
structure CFam (Par : Type*) where
  /-- The offset flow `𝔛_P(u, y, r)`. -/
  fl : Par → ℝ → CVec → ℝ → CVec
  /-- The center point `x_P`. -/
  ctr : Par → CVec
  /-- The anchor `s`. -/
  anc : ℝ

namespace CFam

variable {Par : Type*} [NormedAddCommGroup Par] [NormedSpace ℂ Par]

/-- The center transported to the time `r`: `c_P(r) = 𝔛_P(r, x_P, s)`. -/
def cur (F : CFam Par) (P : Par) (r : ℝ) : CVec := F.fl P r (F.ctr P) F.anc

/-- The domain of the offset flow from the time `r`: parameters in `Ω` and points in the ball of
radius `ϱ` around the transported center. -/
def dom (F : CFam Par) (Ω : Set Par) (ϱ r : ℝ) : Set (Par × CVec) :=
  {q | q.1 ∈ Ω ∧ q.2 ∈ ball (F.cur q.1 r) ϱ}

/-- **The invariants of a complex family.** -/
structure OK (F : CFam Par) (Ω : Set Par) (W : Set ℝ) (ϱ Λ T : ℝ) : Prop where
  hϱ : 0 < ϱ
  hΛ : 0 ≤ Λ
  hT : ∀ u ∈ W, ∀ r ∈ W, |u - r| ≤ T
  hΛT : Λ * T ≤ 1 / 2
  anc_mem : F.anc ∈ W
  hΩ : IsOpen Ω
  ctr_hol : DifferentiableOn ℂ F.ctr Ω
  cur_anc : ∀ P ∈ Ω, F.cur P F.anc = F.ctr P
  hol : ∀ u ∈ W, ∀ r ∈ W,
    DifferentiableOn ℂ (fun q : Par × CVec => F.fl q.1 u q.2 r) (F.dom Ω ϱ r)
  init : ∀ P ∈ Ω, ∀ r ∈ W, ∀ y ∈ ball (F.cur P r) ϱ, F.fl P r y r = y
  jac : ∀ P ∈ Ω, ∀ u ∈ W, ∀ r ∈ W, ∀ y ∈ ball (F.cur P r) ϱ,
    ‖fderiv ℂ (fun y => F.fl P u y r) y - ContinuousLinearMap.id ℂ CVec‖ ≤ Λ * |u - r|
  group : ∀ P ∈ Ω, ∀ u ∈ W, ∀ v ∈ W, ∀ r ∈ W, ∀ y ∈ ball (F.cur P r) (ϱ / 4),
    F.fl P u (F.fl P v y r) v = F.fl P u y r

variable {F : CFam Par} {Ω : Set Par} {W : Set ℝ} {ϱ Λ T : ℝ}

namespace OK

theorem hT0 (h : F.OK Ω W ϱ Λ T) : 0 ≤ T := (abs_nonneg _).trans (h.hT _ h.anc_mem _ h.anc_mem)

/-- The transported centers are holomorphic in the parameters. -/
theorem cur_hol (h : F.OK Ω W ϱ Λ T) {r : ℝ} (hr : r ∈ W) :
    DifferentiableOn ℂ (fun P => F.cur P r) Ω := by
  have hmaps : MapsTo (fun P => (P, F.ctr P)) Ω (F.dom Ω ϱ F.anc) := fun P hP =>
    ⟨hP, by rw [h.cur_anc P hP]; exact mem_ball_self h.hϱ⟩
  exact (h.hol r hr F.anc h.anc_mem).comp (differentiableOn_id.prodMk h.ctr_hol) hmaps

theorem isOpen_dom (h : F.OK Ω W ϱ Λ T) {r : ℝ} (hr : r ∈ W) : IsOpen (F.dom Ω ϱ r) := by
  have hc : ContinuousOn (fun q : Par × CVec => dist q.2 (F.cur q.1 r)) (Ω ×ˢ univ) :=
    continuous_dist.comp_continuousOn (continuous_snd.continuousOn.prodMk
      ((h.cur_hol hr).continuousOn.comp continuous_fst.continuousOn fun q hq => hq.1))
  have e : F.dom Ω ϱ r = (Ω ×ˢ univ) ∩ (fun q : Par × CVec => dist q.2 (F.cur q.1 r)) ⁻¹' Iio ϱ := by
    ext q
    simp [dom, mem_ball]
  rw [e]
  exact hc.isOpen_inter_preimage (h.hΩ.prod isOpen_univ) isOpen_Iio

/-- The offset flow is holomorphic in the point. -/
theorem differentiableAt_fl (h : F.OK Ω W ϱ Λ T) {P : Par} (hP : P ∈ Ω) {u r : ℝ} (hu : u ∈ W)
    (hr : r ∈ W) {y : CVec} (hy : y ∈ ball (F.cur P r) ϱ) :
    DifferentiableAt ℂ (fun y => F.fl P u y r) y := by
  have hq : (P, y) ∈ F.dom Ω ϱ r := ⟨hP, hy⟩
  have hd := (h.hol u hu r hr).differentiableAt ((h.isOpen_dom hr).mem_nhds hq)
  exact hd.comp y ((differentiableAt_const P).prodMk differentiableAt_id)

theorem differentiableOn_fl (h : F.OK Ω W ϱ Λ T) {P : Par} (hP : P ∈ Ω) {u r : ℝ} (hu : u ∈ W)
    (hr : r ∈ W) : DifferentiableOn ℂ (fun y => F.fl P u y r) (ball (F.cur P r) ϱ) :=
  fun _ hy => (h.differentiableAt_fl hP hu hr hy).differentiableWithinAt

/-- **The offset flow is close to a translation**: `‖𝔛(u,y,r) - 𝔛(u,y',r) - (y - y')‖ ≤
Λ|u - r| ‖y - y'‖` on the ball. -/
theorem norm_fl_sub_sub_le (h : F.OK Ω W ϱ Λ T) {P : Par} (hP : P ∈ Ω) {u r : ℝ} (hu : u ∈ W)
    (hr : r ∈ W) {y y' : CVec} (hy : y ∈ ball (F.cur P r) ϱ) (hy' : y' ∈ ball (F.cur P r) ϱ) :
    ‖F.fl P u y r - F.fl P u y' r - (y - y')‖ ≤ Λ * |u - r| * ‖y - y'‖ := by
  have hg : ∀ z ∈ ball (F.cur P r) ϱ, DifferentiableAt ℂ (fun y => F.fl P u y r - y) z :=
    fun z hz => (h.differentiableAt_fl hP hu hr hz).sub differentiableAt_fun_id
  have hbd : ∀ z ∈ ball (F.cur P r) ϱ, ‖fderiv ℂ (fun y => F.fl P u y r - y) z‖ ≤ Λ * |u - r| := by
    intro z hz
    rw [fderiv_fun_sub (h.differentiableAt_fl hP hu hr hz) differentiableAt_fun_id, fderiv_fun_id]
    exact h.jac P hP u hu r hr z hz
  have := (convex_ball (F.cur P r) ϱ).norm_image_sub_le_of_norm_fderiv_le hg hbd hy' hy
  simpa [sub_sub, sub_add_eq_sub_sub, add_comm, sub_eq_add_neg, add_assoc, add_left_comm] using this

theorem norm_fl_sub_le (h : F.OK Ω W ϱ Λ T) {P : Par} (hP : P ∈ Ω) {u r : ℝ} (hu : u ∈ W)
    (hr : r ∈ W) {y y' : CVec} (hy : y ∈ ball (F.cur P r) ϱ) (hy' : y' ∈ ball (F.cur P r) ϱ) :
    ‖F.fl P u y r - F.fl P u y' r‖ ≤ (1 + Λ * T) * ‖y - y'‖ := by
  have h1 := h.norm_fl_sub_sub_le hP hu hr hy hy'
  have h2 : Λ * |u - r| ≤ Λ * T := mul_le_mul_of_nonneg_left (h.hT u hu r hr) h.hΛ
  calc ‖F.fl P u y r - F.fl P u y' r‖
      = ‖(F.fl P u y r - F.fl P u y' r - (y - y')) + (y - y')‖ := by congr 1; abel
    _ ≤ Λ * |u - r| * ‖y - y'‖ + ‖y - y'‖ := (norm_add_le _ _).trans (add_le_add h1 le_rfl)
    _ ≤ Λ * T * ‖y - y'‖ + ‖y - y'‖ :=
        add_le_add (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)) le_rfl
    _ = (1 + Λ * T) * ‖y - y'‖ := by ring

/-- The center at the anchor time is the center point. -/
theorem ctr_mem_quarter (h : F.OK Ω W ϱ Λ T) {P : Par} (hP : P ∈ Ω) :
    F.ctr P ∈ ball (F.cur P F.anc) (ϱ / 4) := by
  rw [h.cur_anc P hP]
  exact mem_ball_self (by linarith [h.hϱ])

/-- **The flow transports the centers.** -/
theorem cur_eq (h : F.OK Ω W ϱ Λ T) {P : Par} (hP : P ∈ Ω) {u r : ℝ} (hu : u ∈ W) (hr : r ∈ W) :
    F.fl P u (F.cur P r) r = F.cur P u :=
  h.group P hP u hu r hr F.anc h.anc_mem (F.ctr P) (h.ctr_mem_quarter hP)

/-- **Balls around centers are mapped to balls around centers.** -/
theorem fl_mem_ball (h : F.OK Ω W ϱ Λ T) {P : Par} (hP : P ∈ Ω) {u r : ℝ} (hu : u ∈ W)
    (hr : r ∈ W) {ρ : ℝ} (hρ : ρ ≤ ϱ) {y : CVec} (hy : y ∈ ball (F.cur P r) ρ) :
    F.fl P u y r ∈ ball (F.cur P u) ((1 + Λ * T) * ρ) := by
  have hy' : y ∈ ball (F.cur P r) ϱ := ball_subset_ball hρ hy
  have hc : F.cur P r ∈ ball (F.cur P r) ϱ := mem_ball_self h.hϱ
  rw [mem_ball, dist_eq_norm, ← h.cur_eq hP hu hr]
  have h1 := h.norm_fl_sub_le hP hu hr hy' hc
  rw [mem_ball, dist_eq_norm] at hy
  have hΛT : 0 ≤ Λ * T := mul_nonneg h.hΛ h.hT0
  calc ‖F.fl P u y r - F.fl P u (F.cur P r) r‖ ≤ (1 + Λ * T) * ‖y - F.cur P r‖ := h1
    _ < (1 + Λ * T) * ρ := mul_lt_mul_of_pos_left hy (by linarith)

/-- **The derivative of the offset flow is Lipschitz on the half balls** (Cauchy's estimate). -/
theorem norm_fderiv_fl_sub_le (h : F.OK Ω W ϱ Λ T) {P : Par} (hP : P ∈ Ω) {u r : ℝ} (hu : u ∈ W)
    (hr : r ∈ W) {z z' : CVec} (hz : z ∈ ball (F.cur P r) (ϱ / 2))
    (hz' : z' ∈ ball (F.cur P r) (ϱ / 2)) :
    ‖fderiv ℂ (fun y => F.fl P u y r) z - fderiv ℂ (fun y => F.fl P u y r) z'‖ ≤
      4 * (Λ * T) / ϱ * ‖z - z'‖ := by
  have hϱ := h.hϱ
  have hΛT : 0 ≤ Λ * T := mul_nonneg h.hΛ h.hT0
  have hC : 0 ≤ 4 * (Λ * T) / ϱ * ‖z - z'‖ := by positivity
  refine ContinuousLinearMap.opNorm_le_of_unit_norm hC fun w hw1 => ?_
  refine (pi_norm_le_iff_of_nonneg hC).mpr fun c => ?_
  have hd := h.differentiableOn_fl hP hu hr
  have hFc : DifferentiableOn ℂ (fun y => F.fl P u y r c) (ball (F.cur P r) ϱ) := fun x hx =>
    ((ContinuousLinearMap.proj c : CVec →L[ℂ] ℂ).differentiableAt.comp_differentiableWithinAt
      x (hd x hx))
  have hG := differentiableOn_fderiv_apply isOpen_ball hFc w
  have hGeq : ∀ x ∈ ball (F.cur P r) ϱ,
      fderiv ℂ (fun y => F.fl P u y r c) x w = fderiv ℂ (fun y => F.fl P u y r) x w c := by
    intro x hx
    have hD : HasFDerivAt (fun y => F.fl P u y r) (fderiv ℂ (fun y => F.fl P u y r) x) x :=
      (h.differentiableAt_fl hP hu hr hx).hasFDerivAt
    have h2 : HasFDerivAt (fun y => F.fl P u y r c)
        ((ContinuousLinearMap.proj c : CVec →L[ℂ] ℂ).comp (fderiv ℂ (fun y => F.fl P u y r) x)) x :=
      ((ContinuousLinearMap.proj c : CVec →L[ℂ] ℂ).hasFDerivAt).comp x hD
    rw [h2.fderiv]
    rfl
  -- the scalar function `g = (D𝔛 w)_c - w_c`
  let g : CVec → ℂ := fun x => fderiv ℂ (fun y => F.fl P u y r c) x w - w c
  have hg : DifferentiableOn ℂ g (ball (F.cur P r) ϱ) := hG.sub (differentiableOn_const _)
  have hgb : ∀ x ∈ ball (F.cur P r) ϱ, ‖g x‖ ≤ Λ * T := by
    intro x hx
    show ‖fderiv ℂ (fun y => F.fl P u y r c) x w - w c‖ ≤ Λ * T
    rw [hGeq x hx]
    have e : fderiv ℂ (fun y => F.fl P u y r) x w c - w c =
        ((fderiv ℂ (fun y => F.fl P u y r) x - ContinuousLinearMap.id ℂ CVec) w) c := by simp
    rw [e]
    refine (norm_le_pi_norm _ c).trans (((fderiv ℂ (fun y => F.fl P u y r) x -
      ContinuousLinearMap.id ℂ CVec).le_opNorm w).trans ?_)
    rw [hw1, mul_one]
    exact (h.jac P hP u hu r hr x hx).trans
      (mul_le_mul_of_nonneg_left (h.hT u hu r hr) h.hΛ)
  have hgd : ∀ x ∈ ball (F.cur P r) (ϱ / 2), ‖fderiv ℂ g x‖ ≤ Λ * T / (ϱ / 4) := by
    intro x hx
    have hsub : closedBall x (ϱ / 4) ⊆ ball (F.cur P r) ϱ := by
      intro y hy
      rw [mem_closedBall] at hy
      rw [mem_ball] at hx ⊢
      have := dist_triangle y x (F.cur P r)
      linarith
    exact norm_fderiv_le_of_closedBall (by positivity) (hg.mono hsub) fun y hy => hgb y (hsub hy)
  have hmv := (convex_ball (F.cur P r) (ϱ / 2)).norm_image_sub_le_of_norm_fderiv_le
    (fun x hx => hg.differentiableAt (isOpen_ball.mem_nhds
      (ball_subset_ball (by linarith) hx))) hgd hz' hz
  have e1 : g z - g z' = fderiv ℂ (fun y => F.fl P u y r) z w c -
      fderiv ℂ (fun y => F.fl P u y r) z' w c := by
    show (fderiv ℂ (fun y => F.fl P u y r c) z w - w c) -
      (fderiv ℂ (fun y => F.fl P u y r c) z' w - w c) = _
    rw [hGeq z (ball_subset_ball (by linarith) hz), hGeq z' (ball_subset_ball (by linarith) hz')]
    ring
  rw [e1] at hmv
  have e2 : Λ * T / (ϱ / 4) = 4 * (Λ * T) / ϱ := by field_simp
  rw [e2] at hmv
  simpa [sub_apply] using hmv

end OK

end CFam

end AVRegularity.Providers.ComplexFlow
end
