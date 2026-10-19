-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Construction.OcA
public import AVRegularity.Statements.Construction.OcCStar
public import AVRegularity.Statements.Construction.IsAdmissibleQ
import AVRegularity.Velocity.ExistsLimitVelocity
import AVenhance.Infra.Flow.MeasurePreservation
import AVenhance.Infra.Flow.JointSmoothFromFixedStart
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVenhance.Infra.Flow.VariationalEquation
public import AVenhance.Statements.Roots.IsZ2Periodic
import AVenhance.Infra.Construction.StreamAdmissible
import AVenhance.Infra.Flow.GradientDeviation
import AVenhance.Infra.Flow.InverseC1
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Topology.Compactness.DeltaGeneratedSpace

section
@[expose] public section
noncomputable section

section
open Homogenization
namespace AVRegularity.Applications

/-! # Sup norm versus Euclidean norm on `Vec 2`

`‖w‖` is the sup norm; `Real.sqrt (vecNormSq w)` the Euclidean one. -/

theorem vecNormSq_two (w : Vec 2) : vecNormSq w = w 0 ^ 2 + w 1 ^ 2 := by
  simp [vecNormSq, vecDot, Fin.sum_univ_two, sq]

/-- The sup norm is at most the Euclidean norm. -/
theorem norm_le_sqrt_vecNormSq (w : Vec 2) : ‖w‖ ≤ Real.sqrt (vecNormSq w) := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  apply Real.abs_le_sqrt
  rw [vecNormSq_two]
  fin_cases i <;> simp <;> nlinarith [sq_nonneg (w 0), sq_nonneg (w 1)]

/-- `|w|_E² ≤ 2 ‖w‖²`. -/
theorem vecNormSq_le_two_mul_norm_sq (w : Vec 2) : vecNormSq w ≤ 2 * ‖w‖ ^ 2 := by
  have h0 : |w 0| ≤ ‖w‖ := by simpa using norm_le_pi_norm w 0
  have h1 : |w 1| ≤ ‖w‖ := by simpa using norm_le_pi_norm w 1
  rw [vecNormSq_two]
  have a0 : w 0 ^ 2 ≤ ‖w‖ ^ 2 := by simpa using sq_le_sq' (abs_le.1 h0).1 (abs_le.1 h0).2
  have a1 : w 1 ^ 2 ≤ ‖w‖ ^ 2 := by simpa using sq_le_sq' (abs_le.1 h1).1 (abs_le.1 h1).2
  linarith

/-- `|w|_E ≤ 2 ‖w‖`. -/
theorem sqrt_vecNormSq_le_two_mul_norm (w : Vec 2) : Real.sqrt (vecNormSq w) ≤ 2 * ‖w‖ := by
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, ?_⟩
  have := vecNormSq_le_two_mul_norm_sq w
  nlinarith [norm_nonneg w]

/-! # Euclidean Lipschitz bound from a close-to-identity derivative

If `D f` is within `1/2` of the identity in the Euclidean operator norm
(`|Df v - v|² ≤ |v|²/4`), then `f` is `2`-Lipschitz for the Euclidean norm
(mean value theorem applied to `s ↦ ⟨f y - f y', f (y' + s (y - y'))⟩`). -/

theorem abs_vecDot_le_sqrt_mul (u z : Vec 2) :
    |vecDot u z| ≤ Real.sqrt (vecNormSq u) * Real.sqrt (vecNormSq z) := by
  rw [← Real.sqrt_mul (vecNormSq_nonneg u)]
  exact Real.abs_le_sqrt (sq_vecDot_le_vecNormSq_mul_vecNormSq u z)

/-- A map whose derivative is `1/2`-close to the identity is `2`-Lipschitz (Euclidean norm). -/
theorem euclid_lipschitz_of_fderiv_close {f : Vec 2 → Vec 2} (hf : Differentiable ℝ f)
    (hD : ∀ y v, vecNormSq (fderiv ℝ f y v - v) ≤ (1 / 4) * vecNormSq v) (y y' : Vec 2) :
    Real.sqrt (vecNormSq (f y - f y')) ≤ 2 * Real.sqrt (vecNormSq (y - y')) := by
  set w := y - y' with hw
  set u := f y - f y' with hu
  set γ : ℝ → Vec 2 := fun s => y' + s • w with hγ
  set ψ : ℝ → ℝ := fun s => vecDot u (f (γ s)) with hψ
  have hγd (s : ℝ) : HasDerivAt γ w s := by
    show HasDerivAt (fun s => y' + s • w) w s
    simpa using ((hasDerivAt_id s).smul_const w).const_add y'
  have hψd (s : ℝ) : HasDerivAt ψ (vecDot u (fderiv ℝ f (γ s) w)) s := by
    have hfd : HasDerivAt (fun s => f (γ s)) (fderiv ℝ f (γ s) w) s :=
      (hf (γ s)).hasFDerivAt.comp_hasDerivAt s (hγd s)
    have h0 := (hasDerivAt_pi.1 hfd) 0
    have h1 := (hasDerivAt_pi.1 hfd) 1
    have := (h0.const_mul (u 0)).fun_add (h1.const_mul (u 1))
    simpa [hψ, vecDot, Fin.sum_univ_two] using this
  have hcont : ContinuousOn ψ (Set.Icc 0 1) :=
    fun s _ => (hψd s).continuousAt.continuousWithinAt
  obtain ⟨c, _, hc⟩ := exists_hasDerivAt_eq_slope ψ (fun s => vecDot u (fderiv ℝ f (γ s) w))
    (by norm_num : (0 : ℝ) < 1) hcont (fun s _ => hψd s)
  have hψ1 : ψ 1 = vecDot u (f y) := by simp [hψ, hγ, hw]
  have hψ0 : ψ 0 = vecDot u (f y') := by simp [hψ, hγ]
  have hslope : vecNormSq u = vecDot u (fderiv ℝ f (γ c) w) := by
    have : (ψ 1 - ψ 0) / (1 - 0) = vecNormSq u := by
      rw [hψ1, hψ0]
      simp [vecNormSq, vecDot, Fin.sum_univ_two, hu]
      ring
    rw [← this, ← hc]
  set e := fderiv ℝ f (γ c) w - w with he
  have hsplit : vecDot u (fderiv ℝ f (γ c) w) = vecDot u w + vecDot u e := by
    simp [he, vecDot, Fin.sum_univ_two]
    ring
  have hesq : Real.sqrt (vecNormSq e) ≤ (1 / 2) * Real.sqrt (vecNormSq w) := by
    have h := Real.sqrt_le_sqrt (hD (γ c) w)
    rw [Real.sqrt_mul (by norm_num)] at h
    have h2 : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h2] at h
    exact h
  set a := Real.sqrt (vecNormSq u) with ha
  set c' := Real.sqrt (vecNormSq w) with hc'
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hc0 : 0 ≤ c' := Real.sqrt_nonneg _
  have haa : a * a = vecNormSq u := Real.mul_self_sqrt (vecNormSq_nonneg u)
  have h1 := abs_vecDot_le_sqrt_mul u w
  have h2 := abs_vecDot_le_sqrt_mul u e
  have key : a * a ≤ (3 / 2) * a * c' := by
    rw [haa, hslope, hsplit]
    have := le_abs_self (vecDot u w)
    have := le_abs_self (vecDot u e)
    nlinarith [mul_le_mul_of_nonneg_left hesq ha0]
  show a ≤ 2 * c'
  by_contra hcon
  push Not at hcon
  nlinarith

end AVRegularity.Applications
end

section
namespace AVRegularity.Applications

/-! # Rounded scales for the applications layer

`ocEpsilon_succ_le`, `ocEpsilon_succ_ge`: the rounding bounds `⌈y⌉ ≤ 2y` (`y ≥ 1`) give
`ε_{m+1} ≤ 2^q ε_m^q` and `ε_m^q / 2 ≤ ε_{m+1}` for `m ≥ 1`.
Also the ratio bound
`a_m ≥ 16 a_{m-1}` for `a_m = ε_m^{β-2}`, and a crude bound on `c_*`. -/

open AVRegularity

private theorem ceil_le_two_mul {y : ℝ} (hy : 1 ≤ y) : (⌈y⌉₊ : ℝ) ≤ 2 * y := by
  have h := Nat.ceil_lt_add_one (by linarith : 0 ≤ y)
  linarith

private theorem raw_ge_one {q : ℝ} {Λ m : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ) :
    1 ≤ (Λ : ℝ) ^ (q ^ m / (q - 1)) := by
  have hΛ1 : (1 : ℝ) ≤ Λ := by exact_mod_cast (by omega : 1 ≤ Λ)
  apply Real.one_le_rpow hΛ1
  have : 0 < q - 1 := by linarith
  have : 0 ≤ q ^ m := by positivity
  positivity

private theorem raw_succ {q : ℝ} {Λ m : ℕ} :
    (Λ : ℝ) ^ (q ^ (m + 1) / (q - 1)) = ((Λ : ℝ) ^ (q ^ m / (q - 1))) ^ q := by
  have hΛ0 : (0 : ℝ) ≤ Λ := by positivity
  rw [← Real.rpow_mul hΛ0]
  congr 1
  rw [pow_succ]
  ring

private theorem eps_eq {q : ℝ} {Λ m : ℕ} (hm : 1 ≤ m) :
    ocEpsilon q Λ m = ((⌈(Λ : ℝ) ^ (q ^ m / (q - 1))⌉₊ : ℕ) : ℝ)⁻¹ := by
  simp [ocEpsilon, Nat.ne_of_gt hm]

/-- `ε_{m+1} ≤ 2^q ε_m^q` for `m ≥ 1`. -/
theorem ocEpsilon_succ_le {q : ℝ} {Λ m : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ) (hm : 1 ≤ m) :
    ocEpsilon q Λ (m + 1) ≤ 2 ^ q * ocEpsilon q Λ m ^ q := by
  set y := (Λ : ℝ) ^ (q ^ m / (q - 1)) with hy
  have hy1 : 1 ≤ y := raw_ge_one hq hΛ
  have hypos : 0 < y := by linarith
  have hc : (⌈y⌉₊ : ℝ) ≤ 2 * y := ceil_le_two_mul hy1
  have hcpos : 0 < (⌈y⌉₊ : ℝ) := by exact_mod_cast Nat.ceil_pos.mpr hypos
  have hy' : y ^ q ≤ (⌈(Λ : ℝ) ^ (q ^ (m + 1) / (q - 1))⌉₊ : ℝ) := by
    rw [raw_succ]
    exact Nat.le_ceil _
  rw [eps_eq (by omega : 1 ≤ m + 1), eps_eq hm]
  have hypq : 0 < y ^ q := Real.rpow_pos_of_pos hypos q
  have h1 : ((⌈(Λ : ℝ) ^ (q ^ (m + 1) / (q - 1))⌉₊ : ℕ) : ℝ)⁻¹ ≤ (y ^ q)⁻¹ :=
    inv_anti₀ hypq hy'
  have h2 : (y ^ q)⁻¹ ≤ 2 ^ q * ((⌈y⌉₊ : ℝ)⁻¹) ^ q := by
    rw [Real.inv_rpow hcpos.le, ← div_eq_mul_inv, ← one_div, div_le_div_iff₀ hypq
      (Real.rpow_pos_of_pos hcpos q)]
    have : (⌈y⌉₊ : ℝ) ^ q ≤ (2 * y) ^ q := Real.rpow_le_rpow hcpos.le hc (by linarith)
    rw [Real.mul_rpow (by norm_num) hypos.le] at this
    linarith
  exact h1.trans h2

/-- `ε_m^q / 2 ≤ ε_{m+1}` for `m ≥ 1`. -/
theorem ocEpsilon_succ_ge {q : ℝ} {Λ m : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ) (hm : 1 ≤ m) :
    ocEpsilon q Λ m ^ q / 2 ≤ ocEpsilon q Λ (m + 1) := by
  set y := (Λ : ℝ) ^ (q ^ m / (q - 1)) with hy
  have hy1 : 1 ≤ y := raw_ge_one hq hΛ
  have hypos : 0 < y := by linarith
  have hcpos : 0 < (⌈y⌉₊ : ℝ) := by exact_mod_cast Nat.ceil_pos.mpr hypos
  have hyc : y ≤ (⌈y⌉₊ : ℝ) := Nat.le_ceil y
  set z := (Λ : ℝ) ^ (q ^ (m + 1) / (q - 1)) with hz
  have hz1 : 1 ≤ z := raw_ge_one hq hΛ
  have hzpos : 0 < z := by linarith
  have hczpos : 0 < (⌈z⌉₊ : ℝ) := by exact_mod_cast Nat.ceil_pos.mpr hzpos
  have hcz : (⌈z⌉₊ : ℝ) ≤ 2 * z := ceil_le_two_mul hz1
  have hzq : z = y ^ q := raw_succ
  rw [eps_eq (by omega : 1 ≤ m + 1), eps_eq hm]
  have hyq : y ^ q ≤ (⌈y⌉₊ : ℝ) ^ q := Real.rpow_le_rpow hypos.le hyc (by linarith)
  have hypq : 0 < y ^ q := Real.rpow_pos_of_pos hypos q
  rw [Real.inv_rpow hcpos.le, div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  have hinv : ((⌈y⌉₊ : ℝ) ^ q)⁻¹ ≤ (y ^ q)⁻¹ := inv_anti₀ hypq hyq
  have h5 : z⁻¹ ≤ (⌈z⌉₊ : ℝ)⁻¹ * 2 := by
    rw [inv_eq_one_div, inv_eq_one_div, one_div_mul_eq_div, div_le_div_iff₀ hzpos hczpos]
    linarith
  calc _ ≤ (y ^ q)⁻¹ := hinv
    _ = z⁻¹ := by rw [hzq]
    _ ≤ _ := h5

private theorem sixteen_le_rpow {α : ℝ} {Λ : ℕ} (hα : α < 1 / 3) (hΛ : 128 ≤ Λ) :
    (16 : ℝ) ≤ (Λ : ℝ) ^ (1 - α) := by
  have hΛr : (128 : ℝ) ≤ Λ := by exact_mod_cast hΛ
  have h1 : (128 : ℝ) ^ (1 - α) ≤ (Λ : ℝ) ^ (1 - α) :=
    Real.rpow_le_rpow (by norm_num) hΛr (by linarith)
  have h2 : (128 : ℝ) ^ ((4 : ℝ) / 7) ≤ (128 : ℝ) ^ (1 - α) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h3 : (128 : ℝ) ^ ((4 : ℝ) / 7) = 16 := by
    have : (128 : ℝ) = (2 : ℝ) ^ (7 : ℕ) := by norm_num
    rw [this, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have h4 : ((7 : ℕ) : ℝ) * ((4 : ℝ) / 7) = ((4 : ℕ) : ℝ) := by norm_num
    rw [h4, Real.rpow_natCast]
    norm_num
  linarith

/-- `a_m = ε_m^{β-2}` is positive. -/
theorem ocA_pos (α q : ℝ) (hq : 1 < q) (Λ m : ℕ) (hΛ : 128 ≤ Λ) : 0 < ocA α q Λ m :=
  Real.rpow_pos_of_pos (AVRegularity.Scales.epsilon_basic (m := m) hq hΛ).1 _

/-- `a_{m+1} ≥ 16 a_m` (the rounded scales separate by at least `Λ ≥ 128`, and `1 - α > 2/3`). -/
theorem ocA_succ_ge {α q : ℝ} {Λ : ℕ} (hα : α < 1 / 3) (hq : 1 < q) (hΛ : 128 ≤ Λ) (m : ℕ) :
    16 * ocA α q Λ m ≤ ocA α q Λ (m + 1) := by
  have hΛr : (128 : ℝ) ≤ Λ := by exact_mod_cast hΛ
  have hΛpos : (0 : ℝ) < Λ := by linarith
  have hε := (AVRegularity.Scales.epsilon_basic (m := m) hq hΛ).1
  have hε' := (AVRegularity.Scales.epsilon_basic (m := m + 1) hq hΛ).1
  have hratio := AVRegularity.Scales.epsilon_ratio_lower (m := m + 1) hq hΛ (by omega)
  simp only [Nat.add_sub_cancel] at hratio
  have hle : ocEpsilon q Λ (m + 1) ≤ ocEpsilon q Λ m / Λ := by
    rw [le_div_iff₀ hΛpos, mul_comm]
    exact (le_div_iff₀ hε').1 hratio
  have he : (1 + α) - 2 ≤ 0 := by linarith
  have h1 : (ocEpsilon q Λ m / Λ) ^ ((1 + α) - 2) ≤ ocEpsilon q Λ (m + 1) ^ ((1 + α) - 2) :=
    Real.rpow_le_rpow_of_nonpos hε' hle he
  rw [Real.div_rpow hε.le hΛpos.le] at h1
  have h16 := sixteen_le_rpow hα hΛ
  have hneg : (Λ : ℝ) ^ ((1 + α) - 2) = ((Λ : ℝ) ^ (1 - α))⁻¹ := by
    rw [← Real.rpow_neg hΛpos.le]
    congr 1
    ring
  have hpos : 0 < ocEpsilon q Λ m ^ ((1 + α) - 2) := Real.rpow_pos_of_pos hε _
  have hΛe : 0 < (Λ : ℝ) ^ (1 - α) := Real.rpow_pos_of_pos hΛpos _
  rw [hneg, div_inv_eq_mul] at h1
  unfold ocA
  calc 16 * ocEpsilon q Λ m ^ ((1 + α) - 2)
      ≤ (Λ : ℝ) ^ (1 - α) * ocEpsilon q Λ m ^ ((1 + α) - 2) :=
        mul_le_mul_of_nonneg_right h16 hpos.le
    _ = ocEpsilon q Λ m ^ ((1 + α) - 2) * (Λ : ℝ) ^ (1 - α) := mul_comm _ _
    _ ≤ _ := h1

/-- `∑_{j<m} a_{j+1} ≤ (16/15) a_m`. -/
theorem ocA_partial_sum_le {α q : ℝ} {Λ : ℕ} (hα : α < 1 / 3) (hq : 1 < q) (hΛ : 128 ≤ Λ)
    (m : ℕ) :
    ∑ j ∈ Finset.range m, ocA α q Λ (j + 1) ≤ (16 / 15) * ocA α q Λ m := by
  induction m with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      exact mul_nonneg (by norm_num) (ocA_pos α q hq Λ 0 hΛ).le
  | succ m ih =>
      rw [Finset.sum_range_succ]
      have h := ocA_succ_ge hα hq hΛ m
      linarith

/-- A crude bound for the short-chart constant: `c_* ≤ 1 / 800000`. -/
theorem ocCStar_le : ocCStar ≤ 1 / 800000 := by
  unfold ocCStar
  have hcosh : (1 : ℝ) ≤ Real.cosh (10 * Real.pi * (1 / 100)) := Real.one_le_cosh _
  rw [inv_eq_one_div]
  apply one_div_le_one_div_of_le (by norm_num)
  have h : 10 * (2 * (4 * Real.cosh (10 * Real.pi * (1 / 100)) / (1 / 100) ^ 2)) =
      800000 * Real.cosh (10 * Real.pi * (1 / 100)) := by ring
  rw [h]
  linarith

end AVRegularity.Applications
end

section
open Homogenization AVenhance AVRegularity
namespace AVRegularity.Applications

/-! # Pointwise bounds for the stream increments

The stream-regularity theorem `Velocity.stream_regularity` bounds the `barNorm` of every increment
`Φ_j - Φ_{j-1}` at radius `2^7 / ε_j` by `10 ε_j^{1+α}`. We convert the orders `0, 1, 2`
into pointwise bounds on the increment, its gradient and its Hessian. -/

section
/-- Each slice of a term of the stream sequence is smooth. -/
theorem streamSeq_slice_smooth {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hζ : IsFastProfile ζ) (hΛ : 128 ≤ Λ) (hΦ : IsOCStreamSeq α q Λ ζ Φ) (m : ℕ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (Φ m t) :=
  (AVRegularity.Velocity.streamSeq_admissible hζ hΛ hΦ m).1.comp
    (contDiff_const.prodMk contDiff_id)

section Bounds

variable (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
  (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ)
  (hΛ : 128 ≤ Λ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (hΦ : IsOCStreamSeq α q Λ ζ Φ)

include hα₀ hα₁ hs₀ hs₁ hq hζ hΛ hΦ

private theorem increment_barNorm (j : ℕ) (hj : 1 ≤ j) (t : ℝ) (n : ℕ) :
    barNorm n (2 ^ 7 * (ocEpsilon q Λ j)⁻¹) (Φ j t - Φ (j - 1) t) ≤
      ENNReal.ofReal (10 * ocEpsilon q Λ j ^ (1 + α)) := by
  obtain ⟨_, _, h⟩ := AVRegularity.Velocity.stream_regularity α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ
    Φ hΦ
  exact (h j hj t).1 n

private theorem increment_iter_bound (j : ℕ) (hj : 1 ≤ j) (t : ℝ) (n : ℕ)
    (i : Fin n → Fin 2) (x : Vec 2) :
    ‖iteratedFDeriv ℝ n (Φ j t - Φ (j - 1) t) x (fun k => basisVec (i k))‖ ≤
      10 * ocEpsilon q Λ j ^ (1 + α) /
        (((n + 1 : ℝ) ^ 2 / (n.factorial : ℝ)) * (2 ^ 7 * (ocEpsilon q Λ j)⁻¹)⁻¹ ^ n) := by
  have hε : 0 < ocEpsilon q Λ j := (AVRegularity.Scales.epsilon_basic (m := j) hq.1 hΛ).1
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (Φ j t - Φ (j - 1) t) :=
    (streamSeq_slice_smooth hζ hΛ hΦ j t).sub (streamSeq_slice_smooth hζ hΛ hΦ (j - 1) t)
  have hcont := AVenhance.continuous_iteratedCoordinate (n := n) hsm i
  exact barNorm_iterated_pointwise i hcont (by positivity) (by positivity)
    (increment_barNorm α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ j hj t n) x

/-- Order zero: the stream increment is at most `10 ε_j^{1+α}`. -/
theorem increment_abs_le (j : ℕ) (hj : 1 ≤ j) (t : ℝ) (x : Vec 2) :
    |Φ j t x - Φ (j - 1) t x| ≤ 10 * ocEpsilon q Λ j ^ (1 + α) := by
  have h := increment_iter_bound α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ j hj t 0
    (fun k => k.elim0) x
  rw [iteratedFDeriv_zero_apply, Real.norm_eq_abs] at h
  simpa using h

/-- Order one: the gradient of the increment is at most `320 ε_j^α` in each coordinate. -/
theorem increment_grad_le (j : ℕ) (hj : 1 ≤ j) (t : ℝ) (x : Vec 2) (i : Fin 2) :
    |fderiv ℝ (Φ j t - Φ (j - 1) t) x (basisVec i)| ≤ 320 * ocEpsilon q Λ j ^ α := by
  have hε : 0 < ocEpsilon q Λ j := (AVRegularity.Scales.epsilon_basic (m := j) hq.1 hΛ).1
  have h := increment_iter_bound α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ j hj t 1
    (fun _ => i) x
  rw [iteratedFDeriv_one_apply, Real.norm_eq_abs] at h
  refine h.trans (le_of_eq ?_)
  have hr : ocEpsilon q Λ j ^ (1 + α) = ocEpsilon q Λ j * ocEpsilon q Λ j ^ α := by
    rw [Real.rpow_add hε, Real.rpow_one]
  rw [hr]
  field_simp
  norm_num

/-- Order two: every Hessian entry of the increment is at most `36500 a_j`. -/
theorem increment_hess_le (j : ℕ) (hj : 1 ≤ j) (t : ℝ) (x : Vec 2) (i k : Fin 2) :
    |fderiv ℝ (fderiv ℝ (Φ j t - Φ (j - 1) t)) x (basisVec i) (basisVec k)| ≤
      36500 * ocA α q Λ j := by
  have hε : 0 < ocEpsilon q Λ j := (AVRegularity.Scales.epsilon_basic (m := j) hq.1 hΛ).1
  have h := increment_iter_bound α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ j hj t 2
    ![i, k] x
  have hm : (fun l : Fin 2 => basisVec (![i, k] l)) = ![basisVec i, basisVec k] := by
    ext l a
    fin_cases l <;> simp
  rw [hm, iteratedFDeriv_two_apply, Real.norm_eq_abs] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h
  have hr : ocEpsilon q Λ j ^ (1 + α) = ocEpsilon q Λ j ^ 2 * ocA α q Λ j := by
    unfold ocA
    rw [← Real.rpow_natCast, ← Real.rpow_add hε]
    norm_num
  have hA : 0 < ocA α q Λ j := ocA_pos α q hq.1 Λ j hΛ
  refine h.trans ?_
  rw [hr]
  have : 10 * (ocEpsilon q Λ j ^ 2 * ocA α q Λ j) /
      ((((2 : ℕ) + 1 : ℝ) ^ 2 / ((2 : ℕ).factorial : ℝ)) *
        (2 ^ 7 * (ocEpsilon q Λ j)⁻¹)⁻¹ ^ 2) = (327680 / 9) * ocA α q Λ j := by
    simp only [Nat.factorial, Nat.cast_ofNat]
    field_simp
    norm_num
  rw [this]
  nlinarith

end Bounds
end

/-! # Partial sums of the stream increments

Telescoping `Φ_m = ∑_{j<m} (Φ_{j+1} - Φ_j)` with the pointwise increment bounds gives
bounds on the gradient and Hessian of `Φ_m`:
`|∂_i Φ_m| ≤ 320 ∑_{j≤m} ε_j^α` and `|∂_i ∂_k Φ_m| ≤ 39000 a_m`. -/

section
/-- Additive induction over the increments, for the iterated derivative of order `n`. -/
theorem iter_sum_bound {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hζ : IsFastProfile ζ) (hΛ : 128 ≤ Λ) (hΦ : IsOCStreamSeq α q Λ ζ Φ) (n : ℕ) (i : Fin n → Fin 2) (c : ℕ → ℝ)
    (hc : ∀ j, 1 ≤ j → ∀ t x,
      ‖iteratedFDeriv ℝ n (Φ j t - Φ (j - 1) t) x (fun k => basisVec (i k))‖ ≤ c j)
    (m : ℕ) (t : ℝ) (x : Vec 2) :
    ‖iteratedFDeriv ℝ n (Φ m t) x (fun k => basisVec (i k))‖ ≤
      ∑ j ∈ Finset.range m, c (j + 1) := by
  induction m with
  | zero =>
      rw [hΦ.1]
      simp [iteratedFDeriv_fun_zero]
  | succ m ih =>
      have hsm : ContDiff ℝ (⊤ : ℕ∞) (Φ m t) := streamSeq_slice_smooth hζ hΛ hΦ m t
      have hsm' : ContDiff ℝ (⊤ : ℕ∞) (Φ (m + 1) t - Φ (m + 1 - 1) t) :=
        (streamSeq_slice_smooth hζ hΛ hΦ (m + 1) t).sub
          (streamSeq_slice_smooth hζ hΛ hΦ (m + 1 - 1) t)
      have hsplit : Φ (m + 1) t = Φ m t + (Φ (m + 1) t - Φ (m + 1 - 1) t) := by
        simp
      have hadd : iteratedFDeriv ℝ n (Φ (m + 1) t) x =
          iteratedFDeriv ℝ n (Φ m t) x +
            iteratedFDeriv ℝ n (Φ (m + 1) t - Φ (m + 1 - 1) t) x := by
        conv_lhs => rw [hsplit]
        exact iteratedFDeriv_add_apply (i := n)
          (hsm.contDiffAt.of_le (by exact_mod_cast le_top))
          (hsm'.contDiffAt.of_le (by exact_mod_cast le_top))
      rw [hadd, add_apply, Finset.sum_range_succ]
      exact (norm_add_le _ _).trans (add_le_add ih (hc (m + 1) (by omega) t x))

section Sums

variable (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
  (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ)
  (hΛ : 128 ≤ Λ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (hΦ : IsOCStreamSeq α q Λ ζ Φ)

include hα₀ hα₁ hs₀ hs₁ hq hζ hΛ hΦ

/-- Gradient of a partial sum. -/
theorem partial_grad_le (m : ℕ) (t : ℝ) (x : Vec 2) (i : Fin 2) :
    |fderiv ℝ (Φ m t) x (basisVec i)| ≤
      320 * ∑ j ∈ Finset.range m, ocEpsilon q Λ (j + 1) ^ α := by
  have h := iter_sum_bound hζ hΛ hΦ 1 (fun _ => i)
    (fun j => 320 * ocEpsilon q Λ j ^ α)
    (fun j hj t x => by
      rw [iteratedFDeriv_one_apply, Real.norm_eq_abs]
      exact increment_grad_le α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ j hj t x i) m t x
  rw [iteratedFDeriv_one_apply, Real.norm_eq_abs, ← Finset.mul_sum] at h
  exact h

/-- Hessian of a partial sum. -/
theorem partial_hess_le' (m : ℕ) (t : ℝ) (x : Vec 2) (i k : Fin 2) :
    |fderiv ℝ (fderiv ℝ (Φ m t)) x (basisVec i) (basisVec k)| ≤
      36500 * ∑ j ∈ Finset.range m, ocA α q Λ (j + 1) := by
  have h := iter_sum_bound hζ hΛ hΦ 2 ![i, k]
    (fun j => 36500 * ocA α q Λ j)
    (fun j hj t x => by
      have hm : (fun l : Fin 2 => basisVec (![i, k] l)) = ![basisVec i, basisVec k] := by
        ext l a
        fin_cases l <;> simp
      rw [hm, iteratedFDeriv_two_apply, Real.norm_eq_abs]
      exact increment_hess_le α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ j hj t x i k) m t x
  have hm : (fun l : Fin 2 => basisVec (![i, k] l)) = ![basisVec i, basisVec k] := by
    ext l a
    fin_cases l <;> simp
  rw [hm, iteratedFDeriv_two_apply, Real.norm_eq_abs, ← Finset.mul_sum] at h
  simpa using h

/-- `|∂_i ∂_k Φ_m| ≤ 39000 a_m`. -/
theorem partial_hess_le (m : ℕ) (t : ℝ) (x : Vec 2) (i k : Fin 2) :
    |fderiv ℝ (fderiv ℝ (Φ m t)) x (basisVec i) (basisVec k)| ≤ 39000 * ocA α q Λ m := by
  refine (partial_hess_le' α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ m t x i k).trans ?_
  have h := ocA_partial_sum_le hα₁ hq.1 hΛ m
  have hA := ocA_pos α q hq.1 Λ m hΛ
  nlinarith

end Sums
end

/-! # Velocity bounds for the finite stages

For `b_m = σ ∇ φ_m = streamVel (Φ m)`:
* `‖b_m‖ ≤ velBound` (uniformly in `m`),
* `‖D b_m‖ ≤ 78000 a_m` in the operator norm for the sup norm,
* the Euclidean spatial Lipschitz bound `|b_m(x) - b_m(y)|_E ≤ 156000 a_m |x - y|_E`. -/

section
theorem streamVel_apply_zero (φ : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) :
    streamVel φ t x 0 = -fderiv ℝ (φ t) x (basisVec 1) := by
  simp [streamVel, sigmaMat, spaceGrad, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem streamVel_apply_one (φ : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) :
    streamVel φ t x 1 = fderiv ℝ (φ t) x (basisVec 0) := by
  simp [streamVel, sigmaMat, spaceGrad, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem streamVel_eq_mk (φ : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) :
    streamVel φ t x = ![-fderiv ℝ (φ t) x (basisVec 1), fderiv ℝ (φ t) x (basisVec 0)] := by
  ext i
  fin_cases i
  · exact streamVel_apply_zero φ t x
  · exact streamVel_apply_one φ t x

/-- The sup norm of the velocity is controlled by the sup norm of the gradient. -/
theorem streamVel_norm_le_of_grad {φ : ℝ → Vec 2 → ℝ} {t : ℝ} {x : Vec 2} {G : ℝ}
    (hG : 0 ≤ G) (h : ∀ i, |fderiv ℝ (φ t) x (basisVec i)| ≤ G) : ‖streamVel φ t x‖ ≤ G := by
  refine (pi_norm_le_iff_of_nonneg hG).2 fun i => ?_
  rw [Real.norm_eq_abs]
  fin_cases i
  · simpa [streamVel_apply_zero] using h 1
  · simpa [streamVel_apply_one] using h 0

/-- Mixed partial: `∂_v (∂_w f) = D²f (v, w)`. -/
theorem fderiv_partial_apply {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (z v w : Vec 2) :
    fderiv ℝ (fun y => fderiv ℝ f y w) z v = fderiv ℝ (fderiv ℝ f) z v w := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by simp)).differentiable (by simp) z
  have := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const w z)).fderiv
  rw [this]
  simp

/-- A bilinear form bounded on the basis is bounded by `2 M ‖v‖` against a basis vector. -/
theorem bilinear_basis_bound (H : Vec 2 →L[ℝ] Vec 2 →L[ℝ] ℝ) {M : ℝ}
    (h : ∀ i k, |H (basisVec i) (basisVec k)| ≤ M) (v : Vec 2) (k : Fin 2) :
    |H v (basisVec k)| ≤ 2 * M * ‖v‖ := by
  have hv : v = v 0 • basisVec 0 + v 1 • basisVec 1 := by
    ext j
    fin_cases j <;> simp [basisVec]
  have h0 : |v 0| ≤ ‖v‖ := by simpa using norm_le_pi_norm v 0
  have h1 : |v 1| ≤ ‖v‖ := by simpa using norm_le_pi_norm v 1
  have e : H v (basisVec k) =
      v 0 * H (basisVec 0) (basisVec k) + v 1 * H (basisVec 1) (basisVec k) := by
    conv_lhs => rw [hv]
    simp
  rw [e]
  calc |v 0 * H (basisVec 0) (basisVec k) + v 1 * H (basisVec 1) (basisVec k)|
      ≤ |v 0 * H (basisVec 0) (basisVec k)| + |v 1 * H (basisVec 1) (basisVec k)| :=
        abs_add_le _ _
    _ ≤ ‖v‖ * M + ‖v‖ * M := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul h0 (h 0 k) (abs_nonneg _) (norm_nonneg _))
          (mul_le_mul h1 (h 1 k) (abs_nonneg _) (norm_nonneg _))
    _ = 2 * M * ‖v‖ := by ring

section Bounds

variable (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
  (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ)
  (hΛ : 128 ≤ Λ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (hΦ : IsOCStreamSeq α q Λ ζ Φ)

/-- The explicit uniform bound for the finite velocities. -/
def velBound (α q : ℝ) (Λ : ℕ) : ℝ :=
  320 * (ocEpsilon q Λ 1 ^ α / (1 - (Λ : ℝ) ^ (-α)))

theorem velBound_nonneg {α q : ℝ} (hα₀ : 0 < α) (hq1 : 1 < q) {Λ : ℕ} (hΛ : 128 ≤ Λ) :
    0 ≤ velBound α q Λ := by
  have hΛr : (128 : ℝ) ≤ Λ := by exact_mod_cast hΛ
  have h1 : (Λ : ℝ) ^ (-α) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have h2 : (Λ : ℝ) ^ (-α) < 1 := by
    have : (Λ : ℝ) ^ (-α) < (Λ : ℝ) ^ (0 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by linarith)
    simpa using this
  have hε := (AVRegularity.Scales.epsilon_basic (m := 1) hq1 hΛ).1
  unfold velBound
  have : 0 < 1 - (Λ : ℝ) ^ (-α) := by linarith
  positivity

include hζ hΛ hΦ

/-- The velocity of every stage is smooth in space. -/
theorem streamVel_slice_smooth (m : ℕ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (streamVel (Φ m) t) :=
  ((AVenhance.Infra.Construction.smoothPeriodic_streamVel
    (AVRegularity.Velocity.streamSeq_admissible hζ hΛ hΦ m)).smooth).comp
      (contDiff_const.prodMk contDiff_id)

include hα₀ hα₁ hs₀ hs₁ hq

/-- The finite velocities are uniformly bounded. -/
theorem streamVel_norm_le (m : ℕ) (t : ℝ) (x : Vec 2) :
    ‖streamVel (Φ m) t x‖ ≤ velBound α q Λ := by
  apply streamVel_norm_le_of_grad (velBound_nonneg hα₀ hq.1 hΛ)
  intro i
  refine (partial_grad_le α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ m t x i).trans ?_
  have htail := AVRegularity.Scales.epsilon_forward_tail (m := 1) hq.1 hΛ le_rfl hα₀
  have hsum : ∑ j ∈ Finset.range m, ocEpsilon q Λ (j + 1) ^ α ≤
      ∑' k : ℕ, ocEpsilon q Λ (1 + k) ^ α := by
    have := htail.1.sum_le_tsum (Finset.range m) (fun k _ =>
      Real.rpow_nonneg (AVRegularity.Scales.epsilon_basic (m := 1 + k) hq.1 hΛ).1.le α)
    simpa [add_comm] using this
  unfold velBound
  have := mul_le_mul_of_nonneg_left (hsum.trans htail.2) (by norm_num : (0 : ℝ) ≤ 320)
  exact this

/-- Operator-norm bound `‖D b_m‖ ≤ 78000 a_m` for the spatial derivative of the velocity. -/
theorem streamVel_slice_fderiv_le (m : ℕ) (t : ℝ) (z : Vec 2) :
    ‖fderiv ℝ (streamVel (Φ m) t) z‖ ≤ 78000 * ocA α q Λ m := by
  have hf := streamSeq_slice_smooth hζ hΛ hΦ m t
  have hg := streamVel_slice_smooth α q ζ hζ Λ hΛ Φ hΦ m t
  have hgd : DifferentiableAt ℝ (streamVel (Φ m) t) z := hg.differentiable (by simp) z
  have hA := ocA_pos α q hq.1 Λ m hΛ
  have hhess : ∀ i k, |fderiv ℝ (fderiv ℝ (Φ m t)) z (basisVec i) (basisVec k)| ≤
      39000 * ocA α q Λ m := fun i k =>
    partial_hess_le α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ m t z i k
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [Real.norm_eq_abs]
  have hcomp : (fderiv ℝ (streamVel (Φ m) t) z v) i =
      fderiv ℝ (fun y => streamVel (Φ m) t y i) z v := by
    have := (hasFDerivAt_pi'.1 hgd.hasFDerivAt i).fderiv
    rw [this]
    rfl
  have hb := bilinear_basis_bound (fderiv ℝ (fderiv ℝ (Φ m t)) z) hhess v
  rw [hcomp]
  fin_cases i
  · have e : (fun y => streamVel (Φ m) t y 0) = fun y => -fderiv ℝ (Φ m t) y (basisVec 1) := by
      funext y
      exact streamVel_apply_zero _ t y
    simp only [Fin.zero_eta]
    rw [e, fderiv_fun_neg, neg_apply, fderiv_partial_apply hf, abs_neg]
    calc _ ≤ 2 * (39000 * ocA α q Λ m) * ‖v‖ := hb 1
      _ = _ := by ring
  · have e : (fun y => streamVel (Φ m) t y 1) = fun y => fderiv ℝ (Φ m t) y (basisVec 0) := by
      funext y
      exact streamVel_apply_one _ t y
    simp only [Fin.mk_one]
    rw [e, fderiv_partial_apply hf]
    calc _ ≤ 2 * (39000 * ocA α q Λ m) * ‖v‖ := hb 0
      _ = _ := by ring

/-- The Euclidean spatial Lipschitz bound `|b_m(x) - b_m(y)|_E ≤ 156000 a_m |x - y|_E`. -/
theorem streamVel_lipschitz_euclid (m : ℕ) (t : ℝ) (x y : Vec 2) :
    Real.sqrt (vecNormSq (streamVel (Φ m) t x - streamVel (Φ m) t y)) ≤
      156000 * ocA α q Λ m * Real.sqrt (vecNormSq (x - y)) := by
  have hg := streamVel_slice_smooth α q ζ hζ Λ hΛ Φ hΦ m t
  have hA := ocA_pos α q hq.1 Λ m hΛ
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := streamVel (Φ m) t)
    (s := Set.univ) (C := 78000 * ocA α q Λ m) (fun z _ => hg.differentiable (by simp) z)
    (fun z _ => streamVel_slice_fderiv_le α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ m t z)
    convex_univ (Set.mem_univ y) (Set.mem_univ x)
  have h1 := sqrt_vecNormSq_le_two_mul_norm (streamVel (Φ m) t x - streamVel (Φ m) t y)
  have h2 := norm_le_sqrt_vecNormSq (x - y)
  calc _ ≤ 2 * ‖streamVel (Φ m) t x - streamVel (Φ m) t y‖ := h1
    _ ≤ 2 * (78000 * ocA α q Λ m * ‖x - y‖) := by linarith
    _ ≤ 2 * (78000 * ocA α q Λ m * Real.sqrt (vecNormSq (x - y))) := by gcongr
    _ = _ := by ring

end Bounds
end

end AVRegularity.Applications
end

section
open Homogenization AVenhance AVRegularity Filter Topology
namespace AVRegularity.Applications

/-! # The limit stream and its tails

The limit stream is `φ = ∑_j (Φ_{j+1} - Φ_j)`. Summing the pointwise increment bounds
against the geometric decay `ε_{j+1} ≤ ε_j / Λ` gives
`|φ - Φ_m| ≤ C ε_{m+1}^{1+α}` and `‖b - b_m‖ ≤ C ε_{m+1}^α`.
-/

section
/-- Tail bound for series dominated by `K ε_{j+1}^p`. -/
theorem tail_bound {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] {q : ℝ} {Λ : ℕ}
    (hq : 1 < q) (hΛ : 128 ≤ Λ) {p K : ℝ} (hp : 0 < p) (hK : 0 ≤ K) (f : ℕ → E)
    (hf : ∀ j, ‖f j‖ ≤ K * ocEpsilon q Λ (j + 1) ^ p) :
    Summable f ∧ ∀ m : ℕ, ‖∑' k, f (k + m)‖ ≤
      K * (ocEpsilon q Λ (m + 1) ^ p / (1 - (Λ : ℝ) ^ (-p))) := by
  have hsum : ∀ m : ℕ, Summable (fun k : ℕ => ocEpsilon q Λ (m + 1 + k) ^ p) ∧
      ∑' k : ℕ, ocEpsilon q Λ (m + 1 + k) ^ p ≤
        ocEpsilon q Λ (m + 1) ^ p / (1 - (Λ : ℝ) ^ (-p)) := fun m =>
    AVRegularity.Scales.epsilon_forward_tail hq hΛ (by omega) hp
  have hmaj : ∀ m : ℕ, Summable (fun k : ℕ => K * ocEpsilon q Λ (k + m + 1) ^ p) := by
    intro m
    have := ((hsum m).1.mul_left K)
    refine this.congr fun k => ?_
    rw [show m + 1 + k = k + m + 1 by omega]
  have hs : ∀ m : ℕ, Summable (fun k => f (k + m)) := fun m =>
    Summable.of_norm_bounded (hmaj m) fun k => hf (k + m)
  refine ⟨by simpa using hs 0, fun m => ?_⟩
  have h1 := tsum_of_norm_bounded (f := fun k => f (k + m)) (hmaj m).hasSum fun k => hf (k + m)
  refine h1.trans ?_
  have : ∑' k : ℕ, K * ocEpsilon q Λ (k + m + 1) ^ p =
      K * ∑' k : ℕ, ocEpsilon q Λ (m + 1 + k) ^ p := by
    rw [← tsum_mul_left]
    refine tsum_congr fun k => ?_
    rw [show m + 1 + k = k + m + 1 by omega]
  rw [this]
  exact mul_le_mul_of_nonneg_left (hsum m).2 hK

section Limit

variable (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
  (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ)
  (hΛ : 128 ≤ Λ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (hΦ : IsOCStreamSeq α q Λ ζ Φ)

/-- The limit stream `φ = ∑_j (Φ_{j+1} - Φ_j)`. -/
def limitStream (Φ : ℕ → ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) : ℝ :=
  ∑' j : ℕ, (Φ (j + 1) t x - Φ j t x)

theorem sum_range_incr {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsOCStreamSeq α q Λ ζ Φ) (M : ℕ) (t : ℝ) (x : Vec 2) :
    ∑ j ∈ Finset.range M, (Φ (j + 1) t x - Φ j t x) = Φ M t x := by
  rw [Finset.sum_range_sub (fun j => Φ j t x), hΦ.1]
  simp

include hα₀ hα₁ hs₀ hs₁ hq hζ hΛ hΦ

theorem incr_norm_le (j : ℕ) (t : ℝ) (x : Vec 2) :
    ‖Φ (j + 1) t x - Φ j t x‖ ≤ 10 * ocEpsilon q Λ (j + 1) ^ (1 + α) := by
  have := increment_abs_le α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ (j + 1) (by omega) t x
  simpa [Real.norm_eq_abs] using this

theorem vel_incr_norm_le (j : ℕ) (t : ℝ) (x : Vec 2) :
    ‖streamVel (Φ (j + 1)) t x - streamVel (Φ j) t x‖ ≤ 320 * ocEpsilon q Λ (j + 1) ^ α := by
  have hε := (AVRegularity.Scales.epsilon_basic (m := j + 1) hq.1 hΛ).1
  have hnn : 0 ≤ 320 * ocEpsilon q Λ (j + 1) ^ α := by positivity
  have hd (i : Fin 2) : |fderiv ℝ (Φ (j + 1) t) x (basisVec i) - fderiv ℝ (Φ j t) x (basisVec i)|
      ≤ 320 * ocEpsilon q Λ (j + 1) ^ α := by
    have h := increment_grad_le α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ (j + 1) (by omega) t x i
    have hsub : fderiv ℝ (Φ (j + 1) t - Φ (j + 1 - 1) t) x =
        fderiv ℝ (Φ (j + 1) t) x - fderiv ℝ (Φ (j + 1 - 1) t) x :=
      fderiv_sub (((streamSeq_slice_smooth hζ hΛ hΦ (j + 1) t).differentiable (by simp)) x)
        (((streamSeq_slice_smooth hζ hΛ hΦ (j + 1 - 1) t).differentiable (by simp)) x)
    rw [hsub] at h
    simpa using h
  refine (pi_norm_le_iff_of_nonneg hnn).2 fun i => ?_
  rw [Real.norm_eq_abs]
  fin_cases i
  · simp only [Fin.zero_eta, Pi.sub_apply, streamVel_apply_zero]
    rw [show -fderiv ℝ (Φ (j + 1) t) x (basisVec 1) - -fderiv ℝ (Φ j t) x (basisVec 1) =
      -(fderiv ℝ (Φ (j + 1) t) x (basisVec 1) - fderiv ℝ (Φ j t) x (basisVec 1)) by ring,
      abs_neg]
    exact hd 1
  · simp only [Fin.mk_one, Pi.sub_apply, streamVel_apply_one]
    exact hd 0

end Limit
end

/-! # Regularity of the limit stream

The limit stream `φ = limitStream Φ` is jointly continuous, `ℤ × ℤ²`-periodic and
differentiable in space, and `σ ∇ φ = b` for any pointwise limit `b` of the velocities. -/

section
/-- A linear functional on `Vec 2` bounded by `G` on the basis has norm at most `2 G`. -/
theorem clm_norm_le_of_basis (L : Vec 2 →L[ℝ] ℝ) {G : ℝ} (hG : 0 ≤ G)
    (h : ∀ i, |L (basisVec i)| ≤ G) : ‖L‖ ≤ 2 * G := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have hv : v = v 0 • basisVec 0 + v 1 • basisVec 1 := by
    ext j
    fin_cases j <;> simp [basisVec]
  have h0 : |v 0| ≤ ‖v‖ := by simpa using norm_le_pi_norm v 0
  have h1 : |v 1| ≤ ‖v‖ := by simpa using norm_le_pi_norm v 1
  have e : L v = v 0 * L (basisVec 0) + v 1 * L (basisVec 1) := by
    conv_lhs => rw [hv]
    simp
  rw [Real.norm_eq_abs, e]
  calc |v 0 * L (basisVec 0) + v 1 * L (basisVec 1)|
      ≤ |v 0 * L (basisVec 0)| + |v 1 * L (basisVec 1)| := abs_add_le _ _
    _ ≤ ‖v‖ * G + ‖v‖ * G := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul h0 (h 0) (abs_nonneg _) (norm_nonneg _))
          (mul_le_mul h1 (h 1) (abs_nonneg _) (norm_nonneg _))
    _ = 2 * G * ‖v‖ := by ring

theorem sum_range_vel_incr {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsOCStreamSeq α q Λ ζ Φ) (M : ℕ) (t : ℝ) (x : Vec 2) :
    ∑ j ∈ Finset.range M, (streamVel (Φ (j + 1)) t x - streamVel (Φ j) t x) =
      streamVel (Φ M) t x := by
  rw [Finset.sum_range_sub (fun j => streamVel (Φ j) t x), hΦ.1]
  ext i
  fin_cases i <;> simp [streamVel, spaceGrad]

section LimitStream

variable (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
  (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ)
  (hΛ : 128 ≤ Λ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (hΦ : IsOCStreamSeq α q Λ ζ Φ)

include hα₀ hα₁ hs₀ hs₁ hq hζ hΛ hΦ

theorem incr_summable (t : ℝ) (x : Vec 2) :
    Summable (fun j : ℕ => Φ (j + 1) t x - Φ j t x) :=
  (tail_bound hq.1 hΛ (by linarith : (0 : ℝ) < 1 + α) (by norm_num : (0 : ℝ) ≤ 10) _
    (incr_norm_le α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ · t x)).1

/-- Pointwise convergence of the streams. -/
theorem limit_tendsto (t : ℝ) (x : Vec 2) :
    Tendsto (fun M => Φ M t x) atTop (𝓝 (limitStream Φ t x)) := by
  have h := (incr_summable α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ t x).hasSum.tendsto_sum_nat
  simp only [sum_range_incr hΦ] at h
  exact h

/-- The stream tail. -/
theorem limit_tail (m : ℕ) (t : ℝ) (x : Vec 2) :
    |limitStream Φ t x - Φ m t x| ≤
      10 * (ocEpsilon q Λ (m + 1) ^ (1 + α) / (1 - (Λ : ℝ) ^ (-(1 + α)))) := by
  have hs := incr_summable α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ t x
  have htail := (tail_bound hq.1 hΛ (by linarith : (0 : ℝ) < 1 + α) (by norm_num : (0 : ℝ) ≤ 10)
    _ (incr_norm_le α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ · t x)).2 m
  have h := hs.sum_add_tsum_nat_add m
  rw [sum_range_incr hΦ] at h
  have : limitStream Φ t x - Φ m t x = ∑' k, (Φ (k + m + 1) t x - Φ (k + m) t x) := by
    unfold limitStream
    linarith
  rw [this]
  simpa [Real.norm_eq_abs] using htail

theorem vel_incr_summable (t : ℝ) (x : Vec 2) :
    Summable (fun j : ℕ => streamVel (Φ (j + 1)) t x - streamVel (Φ j) t x) :=
  (tail_bound hq.1 hΛ hα₀ (by norm_num : (0 : ℝ) ≤ 320) _
    (vel_incr_norm_le α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ · t x)).1

variable (b : ℝ → Vec 2 → Vec 2)
  (hb : ∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x)))

include hb

theorem vel_hasSum (t : ℝ) (x : Vec 2) :
    HasSum (fun j : ℕ => streamVel (Φ (j + 1)) t x - streamVel (Φ j) t x) (b t x) := by
  have hsum := vel_incr_summable α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ t x
  have h := hsum.hasSum.tendsto_sum_nat
  simp only [sum_range_vel_incr hΦ] at h
  have := tendsto_nhds_unique h (hb t x)
  rw [← this]
  exact hsum.hasSum

/-- The velocity tail. -/
theorem vel_tail (m : ℕ) (t : ℝ) (x : Vec 2) :
    ‖b t x - streamVel (Φ m) t x‖ ≤
      320 * (ocEpsilon q Λ (m + 1) ^ α / (1 - (Λ : ℝ) ^ (-α))) := by
  have hs := vel_incr_summable α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ t x
  have htail := (tail_bound hq.1 hΛ hα₀ (by norm_num : (0 : ℝ) ≤ 320)
    _ (vel_incr_norm_le α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ · t x)).2 m
  have h := hs.sum_add_tsum_nat_add m
  rw [sum_range_vel_incr hΦ,
    (vel_hasSum α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ b hb t x).tsum_eq] at h
  have : b t x - streamVel (Φ m) t x =
      ∑' k, (streamVel (Φ (k + m + 1)) t x - streamVel (Φ (k + m)) t x) := by
    rw [← h]
    abel
  rw [this]
  exact htail

omit hb in
theorem incr_fderiv_norm_le (j : ℕ) (t : ℝ) (y : Vec 2) :
    ‖fderiv ℝ (fun z => Φ (j + 1) t z - Φ j t z) y‖ ≤ 2 * (320 * ocEpsilon q Λ (j + 1) ^ α) := by
  have hε := (AVRegularity.Scales.epsilon_basic (m := j + 1) hq.1 hΛ).1
  refine clm_norm_le_of_basis _ (by positivity) fun i => ?_
  have h := increment_grad_le α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ (j + 1) (by omega) t y i
  exact h

omit hb hα₀ hα₁ hs₀ hs₁ hq in
theorem incr_hasFDerivAt (j : ℕ) (t : ℝ) (y : Vec 2) :
    HasFDerivAt (fun z => Φ (j + 1) t z - Φ j t z)
      (fderiv ℝ (fun z => Φ (j + 1) t z - Φ j t z) y) y :=
  (((streamSeq_slice_smooth hζ hΛ hΦ (j + 1) t).sub
    (streamSeq_slice_smooth hζ hΛ hΦ j t)).differentiable (by simp) y).hasFDerivAt

omit hb in
theorem limit_hasFDerivAt (t : ℝ) (x : Vec 2) :
    HasFDerivAt (limitStream Φ t)
      (∑' n : ℕ, fderiv ℝ (fun z => Φ (n + 1) t z - Φ n t z) x) x := by
  have hu : Summable (fun n : ℕ => 2 * (320 * ocEpsilon q Λ (n + 1) ^ α)) :=
    (tail_bound hq.1 hΛ hα₀ (by norm_num : (0 : ℝ) ≤ 640) _ (fun j => by
      have hε := (AVRegularity.Scales.epsilon_basic (m := j + 1) hq.1 hΛ).1
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      linarith)).1
  exact hasFDerivAt_tsum (f := fun n z => Φ (n + 1) t z - Φ n t z) (x₀ := 0) hu
    (fun n y => incr_hasFDerivAt α q ζ hζ Λ hΛ Φ hΦ n t y)
    (fun n y => incr_fderiv_norm_le α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ n t y)
    (incr_summable α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ t 0) x

omit hb in
theorem limit_differentiable (t : ℝ) : Differentiable ℝ (limitStream Φ t) := fun x =>
  (limit_hasFDerivAt α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ t x).differentiableAt

/-- `σ ∇ φ = b`. -/
theorem limit_streamVel_eq (t : ℝ) (x : Vec 2) : streamVel (limitStream Φ) t x = b t x := by
  have hd := limit_hasFDerivAt α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ t x
  have hu : Summable (fun n : ℕ => 2 * (320 * ocEpsilon q Λ (n + 1) ^ α)) :=
    (tail_bound hq.1 hΛ hα₀ (by norm_num : (0 : ℝ) ≤ 640) _ (fun j => by
      have hε := (AVRegularity.Scales.epsilon_basic (m := j + 1) hq.1 hΛ).1
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      linarith)).1
  have hsumL : Summable (fun n : ℕ => fderiv ℝ (fun z => Φ (n + 1) t z - Φ n t z) x) :=
    Summable.of_norm_bounded hu fun n =>
      incr_fderiv_norm_le α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ n t x
  have hcoord (w : Vec 2) : HasSum
      (fun n : ℕ => fderiv ℝ (fun z => Φ (n + 1) t z - Φ n t z) x w)
      (fderiv ℝ (limitStream Φ t) x w) := by
    have := hsumL.hasSum.mapL (ContinuousLinearMap.apply ℝ ℝ w)
    rw [hd.fderiv]
    simpa using this
  have hvel := Pi.hasSum.1
    (vel_hasSum α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ b hb t x)
  have hsubd (n : ℕ) (w : Vec 2) :
      fderiv ℝ (fun z => Φ (n + 1) t z - Φ n t z) x w =
        fderiv ℝ (Φ (n + 1) t) x w - fderiv ℝ (Φ n t) x w := by
    rw [show (fun z => Φ (n + 1) t z - Φ n t z) = Φ (n + 1) t - Φ n t from rfl,
      fderiv_sub (((streamSeq_slice_smooth hζ hΛ hΦ (n + 1) t).differentiable (by simp)) x)
      (((streamSeq_slice_smooth hζ hΛ hΦ n t).differentiable (by simp)) x)]
    rfl
  ext i
  fin_cases i
  · have h0 := hvel 0
    have h1 := (hcoord (basisVec 1)).neg
    have e : (fun n : ℕ => -fderiv ℝ (fun z => Φ (n + 1) t z - Φ n t z) x (basisVec 1)) =
        fun n : ℕ => (streamVel (Φ (n + 1)) t x - streamVel (Φ n) t x) 0 := by
      funext n
      simp only [Pi.sub_apply, streamVel_apply_zero, hsubd]
      ring
    rw [e] at h1
    simpa [streamVel_apply_zero] using h1.unique h0
  · have h0 := hvel 1
    have h1 := hcoord (basisVec 0)
    have e : (fun n : ℕ => fderiv ℝ (fun z => Φ (n + 1) t z - Φ n t z) x (basisVec 0)) =
        fun n : ℕ => (streamVel (Φ (n + 1)) t x - streamVel (Φ n) t x) 1 := by
      funext n
      simp only [Pi.sub_apply, streamVel_apply_one, hsubd]
    rw [e] at h1
    simpa [streamVel_apply_one] using h1.unique h0

omit hb in
theorem limit_continuous : Continuous (fun p : ℝ × Vec 2 => limitStream Φ p.1 p.2) := by
  have hu : Summable (fun n : ℕ => 10 * ocEpsilon q Λ (n + 1) ^ (1 + α)) :=
    (tail_bound hq.1 hΛ (by linarith : (0 : ℝ) < 1 + α) (by norm_num : (0 : ℝ) ≤ 10) _
      (fun j => by
        have hε := (AVRegularity.Scales.epsilon_basic (m := j + 1) hq.1 hΛ).1
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)])).1
  refine continuous_tsum (u := fun n : ℕ => 10 * ocEpsilon q Λ (n + 1) ^ (1 + α))
    (fun n => ?_) hu (fun n p => incr_norm_le α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ n p.1 p.2)
  have h1 := (AVRegularity.Velocity.streamSeq_admissible hζ hΛ hΦ (n + 1)).1.continuous
  have h0 := (AVRegularity.Velocity.streamSeq_admissible hζ hΛ hΦ n).1.continuous
  exact h1.sub h0

omit hb hα₀ hα₁ hs₀ hs₁ hq in
theorem limit_spatial_periodic (t : ℝ) : IsZ2Periodic (limitStream Φ t) := by
  intro k x
  unfold limitStream
  refine tsum_congr fun n => ?_
  have h1 := (AVRegularity.Velocity.streamSeq_admissible hζ hΛ hΦ (n + 1)).2 0 k t x
  have h0 := (AVRegularity.Velocity.streamSeq_admissible hζ hΛ hΦ n).2 0 k t x
  simp only [Int.cast_zero, add_zero] at h1 h0
  rw [h1, h0]

omit hb hα₀ hα₁ hs₀ hs₁ hq in
theorem limit_time_periodic (t : ℝ) (x : Vec 2) : limitStream Φ (t + 1) x = limitStream Φ t x := by
  have hz : latticeShift (0 : Fin 2 → ℤ) = (0 : Vec 2) := by
    ext i
    simp [latticeShift]
  unfold limitStream
  refine tsum_congr fun n => ?_
  have h1 := (AVRegularity.Velocity.streamSeq_admissible hζ hΛ hΦ (n + 1)).2 1 0 t x
  have h0 := (AVRegularity.Velocity.streamSeq_admissible hζ hΛ hΦ n).2 1 0 t x
  simp only [hz, add_zero, Int.cast_one] at h1 h0
  rw [h1, h0]

end LimitStream
end

end AVRegularity.Applications
end

section
open Homogenization AVenhance AVRegularity MeasureTheory
namespace AVRegularity.Applications

/-! # Short-flow bounds

For the flow `X` of `b_m = streamVel (Φ m)` and `h a_m ≤ c_*`, the fixed-time maps
`F = X(t, ·, t₁)` and `G = X(t₁, ·, t)` (`|t - t₁| ≤ h`) are smooth inverse diffeomorphisms
preserving Lebesgue measure; `DF`, `DG` are within `1/2` of the identity in the Euclidean
operator norm and `F`, `G` are `2`-Lipschitz for the Euclidean norm. The Gronwall bound
uses `‖D b_m‖ ≤ 78000 a_m` (sup operator norm) and `c_* ≤ 1/800000`. -/

theorem exp_sub_one_le_eighth {x : ℝ} (h1 : x ≤ 1 / 10) :
    Real.exp x - 1 ≤ 1 / 8 := by
  have h := Real.add_one_le_exp (-x)
  have e : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have hx : 0 < Real.exp x := Real.exp_pos x
  nlinarith [mul_le_mul_of_nonneg_left h hx.le]

/-- Euclidean closeness of the fixed-time flow map's derivative to the identity,
from the sup-norm Gronwall bound. -/
theorem flow_map_euclid_close {b : ℝ → Vec 2 → Vec 2}
    (hb : AVenhance.Infra.Flow.SmoothPeriodicField b) {X : ℝ → Vec 2 → ℝ → Vec 2}
    (hX : AVenhance.IsFlow b X) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ r y, ‖AVenhance.Infra.Flow.jointSpatialFDeriv b r y‖ ≤ L) (s t : ℝ)
    (hLt : L * |t - s| ≤ 1 / 10) (y v : Vec 2) :
    vecNormSq (fderiv ℝ (fun z => X t z s) y v - v) ≤ (1 / 4) * vecNormSq v := by
  have hdev := AVenhance.Infra.Flow.flow_fderiv_deviation hb hX hL0 hL s t y
  have hδ : Real.exp (L * |t - s|) - 1 ≤ 1 / 8 := exp_sub_one_le_eighth hLt
  have hnorm : ‖fderiv ℝ (fun z => X t z s) y v - v‖ ≤ (1 / 8) * ‖v‖ := by
    have h1 := (fderiv ℝ (fun z => X t z s) y - 1).le_opNorm v
    simp only [sub_apply, one_apply_eq_self] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (hdev.trans hδ) (norm_nonneg _))
  have h2 := vecNormSq_le_two_mul_norm_sq (fderiv ℝ (fun z => X t z s) y v - v)
  have h3 : ‖v‖ ^ 2 ≤ vecNormSq v := by
    have := norm_le_sqrt_vecNormSq v
    calc ‖v‖ ^ 2 ≤ Real.sqrt (vecNormSq v) ^ 2 := by gcongr
      _ = vecNormSq v := Real.sq_sqrt (vecNormSq_nonneg v)
  have h4 : ‖fderiv ℝ (fun z => X t z s) y v - v‖ ^ 2 ≤ (1 / 8) ^ 2 * ‖v‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  nlinarith

section Short

variable (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
  (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ)
  (hΛ : 128 ≤ Λ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (hΦ : IsOCStreamSeq α q Λ ζ Φ)

include hα₀ hα₁ hs₀ hs₁ hq hζ hΛ hΦ

/-- **Short-flow bounds.** -/
theorem short_flow_bounds (m : ℕ) (X : ℝ → Vec 2 → ℝ → Vec 2)
    (hX : AVenhance.IsFlow (streamVel (Φ m)) X) (t₁ h : ℝ) (_hh0 : 0 < h)
    (hh : h * ocA α q Λ m ≤ ocCStar) (t : ℝ) (ht : |t - t₁| ≤ h) :
    (∀ y, X t₁ (X t y t₁) t = y) ∧ (∀ x, X t (X t₁ x t) t₁ = x) ∧
      ContDiff ℝ (⊤ : ℕ∞) (fun y => X t y t₁) ∧ ContDiff ℝ (⊤ : ℕ∞) (fun x => X t₁ x t) ∧
      ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => X p.1 p.2 t₁) ∧
      MeasurePreserving (fun y => X t y t₁) volume volume ∧
      (∀ y v, vecNormSq (fderiv ℝ (fun z => X t z t₁) y v - v) ≤ (1 / 4) * vecNormSq v) ∧
      (∀ x v, vecNormSq (fderiv ℝ (fun z => X t₁ z t) x v - v) ≤ (1 / 4) * vecNormSq v) ∧
      (∀ y y', Real.sqrt (vecNormSq (X t y t₁ - X t y' t₁)) ≤
        2 * Real.sqrt (vecNormSq (y - y'))) ∧
      (∀ x x', Real.sqrt (vecNormSq (X t₁ x t - X t₁ x' t)) ≤
        2 * Real.sqrt (vecNormSq (x - x'))) := by
  have hφ := AVRegularity.Velocity.streamSeq_admissible hζ hΛ hΦ m
  have hb := AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ
  have hA := ocA_pos α q hq.1 Λ m hΛ
  set L : ℝ := 78000 * ocA α q Λ m with hLdef
  have hL0 : 0 ≤ L := by positivity
  have hL : ∀ r y, ‖AVenhance.Infra.Flow.jointSpatialFDeriv (streamVel (Φ m)) r y‖ ≤ L := by
    intro r y
    rw [AVenhance.Infra.Flow.jointSpatialFDeriv_eq_slice hb]
    exact streamVel_slice_fderiv_le α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ m r y
  have hLh : L * |t - t₁| ≤ 1 / 10 := by
    have h1 : L * |t - t₁| ≤ L * h := mul_le_mul_of_nonneg_left ht hL0
    have h2 : L * h = 78000 * (h * ocA α q Λ m) := by rw [hLdef]; ring
    have h3 := ocCStar_le
    have : h * ocA α q Λ m ≤ 1 / 800000 := hh.trans h3
    linarith
  have hLh' : L * |t₁ - t| ≤ 1 / 10 := by rwa [abs_sub_comm]
  have hjoint := AVenhance.Infra.Flow.flow_joint_contDiff_infty hb hX
  have hFs : ContDiff ℝ (⊤ : ℕ∞) (fun y => X t y t₁) :=
    hjoint.comp (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const))
  have hGs : ContDiff ℝ (⊤ : ℕ∞) (fun x => X t₁ x t) :=
    hjoint.comp (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const))
  have hFj : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => X p.1 p.2 t₁) :=
    hjoint.comp (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const))
  obtain ⟨_, _, hinv1, hinv2⟩ := AVenhance.Infra.Flow.flow_fixed_time_maps_are_C1_inverses hb hX t₁ t
  have hdiv : ∀ u y, AVenhance.Infra.Flow.spatialDivergence (streamVel (Φ m)) u y = 0 :=
    fun u y => AVRegularity.Velocity.Port.Section2FlowIdentities.streamVel_spatialDivergence_eq_zero hφ u y
  have hFc := flow_map_euclid_close hb hX hL0 hL t₁ t hLh
  have hGc := flow_map_euclid_close hb hX hL0 hL t t₁ hLh'
  refine ⟨hinv1, hinv2, hFs, hGs, hFj,
    AVenhance.Infra.Flow.flow_measurePreserving_of_divergence_free hb hX hdiv t₁ t,
    hFc, hGc, ?_, ?_⟩
  · exact euclid_lipschitz_of_fderiv_close (f := fun z => X t z t₁)
      (hFs.differentiable (by simp)) hFc
  · exact euclid_lipschitz_of_fderiv_close (f := fun z => X t₁ z t)
      (hGs.differentiable (by simp)) hGc

end Short

end AVRegularity.Applications
end
end
end
end

section
@[expose] public section
noncomputable section
open Homogenization AVenhance AVRegularity Filter Topology
namespace AVRegularity.Applications

/-! # Stream bounds and skew form

The bounds (8.1) of the paper, construction part: the stream `φ` with `σ ∇ φ = b`, the tail
bounds `‖φ - φ_m‖ ≤ C ε_{m+1}^β`, `‖b - b_m‖ ≤ C ε_{m+1}^{β-1}`, and
`‖D b_m‖ ≤ C ε_m^{β-2}`. -/

private theorem geom_pos {Λ : ℕ} (hΛ : 128 ≤ Λ) {p : ℝ} (hp : 0 < p) :
    0 < 1 - (Λ : ℝ) ^ (-p) := by
  have hΛr : (128 : ℝ) ≤ Λ := by exact_mod_cast hΛ
  have : (Λ : ℝ) ^ (-p) < (Λ : ℝ) ^ (0 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by linarith)
  simp only [Real.rpow_zero] at this
  linarith

/-- **Stream bounds and skew form**: the construction side of the bounds (8.1) of the paper,
from (1.14) and Proposition 6.3(iii). -/
theorem stream_tail_bounds
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (Λ : ℕ) (hΛ : 128 ≤ Λ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (hΦ : IsOCStreamSeq α q Λ ζ Φ)
    (b : ℝ → Vec 2 → Vec 2)
    (hb : ∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) :
    ∃ (φ : ℝ → Vec 2 → ℝ) (C : ℝ), 0 ≤ C ∧
      (∀ t x, Tendsto (fun M => Φ M t x) atTop (𝓝 (φ t x))) ∧
      (∀ m t x, |φ t x - Φ m t x| ≤ C * ocEpsilon q Λ (m + 1) ^ (1 + α)) ∧
      (∀ m t x, ‖b t x - streamVel (Φ m) t x‖ ≤ C * ocEpsilon q Λ (m + 1) ^ α) ∧
      (∀ t, Differentiable ℝ (φ t)) ∧ (∀ t x, streamVel φ t x = b t x) ∧
      Continuous (fun p : ℝ × Vec 2 => φ p.1 p.2) ∧ (∀ t, IsZ2Periodic (φ t)) ∧
      (∀ t x, φ (t + 1) x = φ t x) ∧
      (∀ m, 1 ≤ m → ∀ t x y,
        Real.sqrt (vecNormSq (streamVel (Φ m) t x - streamVel (Φ m) t y)) ≤
          C * ocEpsilon q Λ m ^ ((1 + α) - 2) * Real.sqrt (vecNormSq (x - y))) ∧
      (∀ m t x, ‖streamVel (Φ m) t x‖ ≤ C) := by
  have hg1 := geom_pos hΛ (by linarith : (0 : ℝ) < 1 + α)
  have hg2 := geom_pos hΛ hα₀
  have hvb := velBound_nonneg hα₀ hq.1 hΛ
  set C1 : ℝ := 10 / (1 - (Λ : ℝ) ^ (-(1 + α))) with hC1
  set C2 : ℝ := 320 / (1 - (Λ : ℝ) ^ (-α)) with hC2
  set V : ℝ := velBound α q Λ with hV
  have hC1n : 0 ≤ C1 := by positivity
  have hC2n : 0 ≤ C2 := by positivity
  refine ⟨limitStream Φ, C1 + C2 + V + 156000, by positivity,
    limit_tendsto α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ, ?_, ?_,
    limit_differentiable α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ,
    limit_streamVel_eq α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ b hb,
    limit_continuous α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ,
    limit_spatial_periodic α q ζ hζ Λ hΛ Φ hΦ, limit_time_periodic α q ζ hζ Λ hΛ Φ hΦ, ?_, ?_⟩
  · intro m t x
    have hε := (AVRegularity.Scales.epsilon_basic (m := m + 1) hq.1 hΛ).1
    have hp : 0 ≤ ocEpsilon q Λ (m + 1) ^ (1 + α) := by positivity
    refine (limit_tail α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ m t x).trans ?_
    have : 10 * (ocEpsilon q Λ (m + 1) ^ (1 + α) / (1 - (Λ : ℝ) ^ (-(1 + α)))) =
        C1 * ocEpsilon q Λ (m + 1) ^ (1 + α) := by
      rw [hC1]; ring
    rw [this]
    nlinarith [mul_nonneg (add_nonneg (add_nonneg hC2n hvb) (by norm_num : (0 : ℝ) ≤ 156000)) hp]
  · intro m t x
    have hε := (AVRegularity.Scales.epsilon_basic (m := m + 1) hq.1 hΛ).1
    have hp : 0 ≤ ocEpsilon q Λ (m + 1) ^ α := by positivity
    refine (vel_tail α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ b hb m t x).trans ?_
    have : 320 * (ocEpsilon q Λ (m + 1) ^ α / (1 - (Λ : ℝ) ^ (-α))) =
        C2 * ocEpsilon q Λ (m + 1) ^ α := by
      rw [hC2]; ring
    rw [this]
    nlinarith [mul_nonneg (add_nonneg (add_nonneg hC1n hvb) (by norm_num : (0 : ℝ) ≤ 156000)) hp]
  · intro m _ t x y
    have hA := ocA_pos α q hq.1 Λ m hΛ
    refine (streamVel_lipschitz_euclid α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ m t x y).trans ?_
    have hn : 0 ≤ Real.sqrt (vecNormSq (x - y)) := Real.sqrt_nonneg _
    have h1 : 156000 * ocA α q Λ m ≤ (C1 + C2 + V + 156000) * ocA α q Λ m := by
      apply mul_le_mul_of_nonneg_right _ hA.le
      linarith
    exact mul_le_mul_of_nonneg_right h1 hn
  · intro m t x
    exact (streamVel_norm_le α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ m t x).trans (by linarith)

end AVRegularity.Applications
end
end
end
