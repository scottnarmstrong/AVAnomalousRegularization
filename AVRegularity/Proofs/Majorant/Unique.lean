-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Definitions.Construction.Gen.Majorant
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
public import AVRegularity.Statements.Construction.IsFastProfile
import AVRegularity.Construction.Stream.NextAdmissible
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.PSeries

@[expose] public noncomputable section

section
open scoped ENNReal
namespace AVRegularity.Providers.Majorant

/-! **Weighted mode sums of mode profiles.** The context norm
`∑_h e^{a|h|}(1+|h|)^L f(h)` of a mode profile `f : ℤ → [0,∞]` (`wsum`, as in `ctxSize` and in
the ledger of `successor_ledger`) is

* additive and monotone, and homogeneous under constant factors;
* submultiplicative under the convolution of profiles (`wsum_mconv_le`), the `mul` clause of
  `genMode`, because the weight is submultiplicative (`modeWeight_add_le`);
* the profile of a single zero mode is its value (`wsum_single`);
* the mode multiplier `2π|h|` costs one fast weight (`wsum_modeMul_le`), the mode gain
  `(2π|h|)⁻¹` gains `(2π)⁻¹` (`wsum_modeGain_le`);
* exponential profiles `C e^{-a'|h|}` of rate `a' > a` have finite weighted sums
  (`wsum_expProfile_lt_top`), so the profiles of `MajOK bw κ` (rate `6π bw`) have finite sums
  against the ledger weight of rate `3π bw`. -/

/-- The weight `e^{a|h|}(1+|h|)^L` of the context norm. -/
def modeWeight (a : ℝ) (L : ℕ) (h : ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (a * |(h : ℝ)|) * (1 + |(h : ℝ)|) ^ L)

/-- The weighted mode sum `∑_h e^{a|h|}(1+|h|)^L f(h)` of a profile. -/
def wsum (a : ℝ) (L : ℕ) (f : ℤ → ℝ≥0∞) : ℝ≥0∞ := ∑' h, modeWeight a L h * f h

/-- The convolution of mode profiles (the `mul` clause of `genMode`). -/
def mconv (f g : ℤ → ℝ≥0∞) (h : ℤ) : ℝ≥0∞ := ∑' k, f k * g (h - k)

/-- The exponential profile `C e^{-a|h|}`. -/
def expProfile (C a : ℝ) (h : ℤ) : ℝ≥0∞ := ENNReal.ofReal (C * Real.exp (-(a * |(h : ℝ)|)))

theorem modeWeight_zero (a : ℝ) (L : ℕ) : modeWeight a L 0 = 1 := by
  simp [modeWeight]

theorem modeWeight_add_le {a : ℝ} (ha : 0 ≤ a) (L : ℕ) (k m : ℤ) :
    modeWeight a L (k + m) ≤ modeWeight a L k * modeWeight a L m := by
  unfold modeWeight
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have habs : |((k + m : ℤ) : ℝ)| ≤ |(k : ℝ)| + |(m : ℝ)| := by
    push_cast
    exact abs_add_le _ _
  have h1 : Real.exp (a * |((k + m : ℤ) : ℝ)|) ≤
      Real.exp (a * |(k : ℝ)|) * Real.exp (a * |(m : ℝ)|) := by
    rw [← Real.exp_add, ← mul_add]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left habs ha)
  have h2 : (1 + |((k + m : ℤ) : ℝ)|) ^ L ≤ (1 + |(k : ℝ)|) ^ L * (1 + |(m : ℝ)|) ^ L := by
    rw [← mul_pow]
    gcongr
    nlinarith [habs, mul_nonneg (abs_nonneg (k : ℝ)) (abs_nonneg (m : ℝ))]
  calc Real.exp (a * |((k + m : ℤ) : ℝ)|) * (1 + |((k + m : ℤ) : ℝ)|) ^ L
      ≤ (Real.exp (a * |(k : ℝ)|) * Real.exp (a * |(m : ℝ)|)) *
          ((1 + |(k : ℝ)|) ^ L * (1 + |(m : ℝ)|) ^ L) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = Real.exp (a * |(k : ℝ)|) * (1 + |(k : ℝ)|) ^ L *
          (Real.exp (a * |(m : ℝ)|) * (1 + |(m : ℝ)|) ^ L) := by ring

theorem modeWeight_mono {a a' : ℝ} (haa : a ≤ a') {L L' : ℕ} (hLL : L ≤ L') (h : ℤ) :
    modeWeight a L h ≤ modeWeight a' L' h := by
  unfold modeWeight
  apply ENNReal.ofReal_le_ofReal
  have h1 : Real.exp (a * |(h : ℝ)|) ≤ Real.exp (a' * |(h : ℝ)|) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right haa (abs_nonneg _))
  have h2 : (1 + |(h : ℝ)|) ^ L ≤ (1 + |(h : ℝ)|) ^ L' :=
    pow_le_pow_right₀ (by linarith [abs_nonneg (h : ℝ)]) hLL
  exact mul_le_mul h1 h2 (by positivity) (by positivity)

theorem wsum_mono {a : ℝ} {L : ℕ} {f g : ℤ → ℝ≥0∞} (hfg : ∀ h, f h ≤ g h) :
    wsum a L f ≤ wsum a L g :=
  ENNReal.tsum_le_tsum fun h => mul_le_mul_right (hfg h) _

theorem wsum_mono_weight {a a' : ℝ} (haa : a ≤ a') {L L' : ℕ} (hLL : L ≤ L')
    (f : ℤ → ℝ≥0∞) : wsum a L f ≤ wsum a' L' f :=
  ENNReal.tsum_le_tsum fun h => mul_le_mul_left (modeWeight_mono haa hLL h) _

theorem wsum_add (a : ℝ) (L : ℕ) (f g : ℤ → ℝ≥0∞) :
    wsum a L (fun h => f h + g h) = wsum a L f + wsum a L g := by
  unfold wsum
  simp only [mul_add]
  exact ENNReal.tsum_add

theorem wsum_const_mul (a : ℝ) (L : ℕ) (c : ℝ≥0∞) (f : ℤ → ℝ≥0∞) :
    wsum a L (fun h => c * f h) = c * wsum a L f := by
  unfold wsum
  simp only [mul_left_comm (modeWeight a L _) c]
  exact ENNReal.tsum_mul_left

theorem wsum_single (a : ℝ) (L : ℕ) (x : ℝ≥0∞) :
    wsum a L (fun h => if h = 0 then x else 0) = x := by
  unfold wsum
  rw [tsum_eq_single 0 fun b hb => by simp [hb]]
  simp [modeWeight_zero]

/-- **Submultiplicativity** of the weighted mode sum under convolution. -/
theorem wsum_mconv_le {a : ℝ} (ha : 0 ≤ a) (L : ℕ) (f g : ℤ → ℝ≥0∞) :
    wsum a L (mconv f g) ≤ wsum a L f * wsum a L g := by
  unfold wsum mconv
  calc ∑' h, modeWeight a L h * ∑' k, f k * g (h - k)
      = ∑' h, ∑' k, modeWeight a L h * (f k * g (h - k)) := by
        simp_rw [ENNReal.tsum_mul_left]
    _ = ∑' k, ∑' h, modeWeight a L h * (f k * g (h - k)) := ENNReal.tsum_comm
    _ = ∑' k, ∑' m, modeWeight a L (k + m) * (f k * g m) := by
        refine tsum_congr fun k => ?_
        rw [← (Equiv.addLeft k).tsum_eq (fun h => modeWeight a L h * (f k * g (h - k)))]
        simp only [Equiv.coe_addLeft, add_sub_cancel_left]
    _ ≤ ∑' k, ∑' m, modeWeight a L k * f k * (modeWeight a L m * g m) := by
        refine ENNReal.tsum_le_tsum fun k => ENNReal.tsum_le_tsum fun m => ?_
        calc modeWeight a L (k + m) * (f k * g m)
            ≤ modeWeight a L k * modeWeight a L m * (f k * g m) :=
              mul_le_mul_left (modeWeight_add_le ha L k m) _
          _ = modeWeight a L k * f k * (modeWeight a L m * g m) := by ring
    _ = (∑' k, modeWeight a L k * f k) * ∑' m, modeWeight a L m * g m := by
        simp_rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]

/-- The mode multiplier `2π|h|` costs one fast weight. -/
theorem wsum_modeMul_le (a : ℝ) (L : ℕ) (f : ℤ → ℝ≥0∞) :
    wsum a L (fun h => modeMul h * f h) ≤ ENNReal.ofReal (2 * Real.pi) * wsum a (L + 1) f := by
  rw [← wsum_const_mul]
  refine ENNReal.tsum_le_tsum fun h => ?_
  rw [← mul_assoc, ← mul_assoc]
  refine mul_le_mul_left ?_ _
  unfold modeWeight modeMul
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hh : |(h : ℝ)| ≤ 1 + |(h : ℝ)| := by linarith
  have he : 0 ≤ Real.exp (a * |(h : ℝ)|) := (Real.exp_pos _).le
  have hp : 0 ≤ (1 + |(h : ℝ)|) ^ L := by positivity
  calc Real.exp (a * |(h : ℝ)|) * (1 + |(h : ℝ)|) ^ L * (2 * Real.pi * |(h : ℝ)|)
      ≤ Real.exp (a * |(h : ℝ)|) * (1 + |(h : ℝ)|) ^ L * (2 * Real.pi * (1 + |(h : ℝ)|)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh (by positivity))
          (mul_nonneg he hp)
    _ = Real.exp (a * |(h : ℝ)|) * (1 + |(h : ℝ)|) ^ (L + 1) * (2 * Real.pi) := by ring

/-- The mode gain is at most `(2π)⁻¹`. -/
theorem modeGain_le (h : ℤ) : modeGain h ≤ ENNReal.ofReal (2 * Real.pi)⁻¹ := by
  unfold modeGain
  split_ifs with h0
  · exact zero_le
  · have h1 : (1 : ℝ) ≤ |(h : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs h0
    have hpos : 0 < 2 * Real.pi * |(h : ℝ)| := by positivity
    unfold modeMul
    rw [← ENNReal.ofReal_inv_of_pos hpos]
    apply ENNReal.ofReal_le_ofReal
    apply inv_anti₀ (by positivity)
    nlinarith [Real.pi_pos]

/-- The mode gain `(2π|h|)⁻¹` gains `(2π)⁻¹`. -/
theorem wsum_modeGain_le (a : ℝ) (L : ℕ) (f : ℤ → ℝ≥0∞) :
    wsum a L (fun h => modeGain h * f h) ≤ ENNReal.ofReal (2 * Real.pi)⁻¹ * wsum a L f := by
  rw [← wsum_const_mul]
  exact wsum_mono fun h => mul_le_mul_left (modeGain_le h) _

/-- Polynomials times decaying exponentials are summable. -/
theorem summable_poly_mul_exp {c : ℝ} (hc : 0 < c) (L : ℕ) :
    Summable fun n : ℕ => (1 + (n : ℝ)) ^ L * Real.exp (-(c * n)) := by
  have e : ∀ n : ℕ, (1 + (n : ℝ)) ^ L * Real.exp (-(c * n)) =
      ∑ j ∈ Finset.range (L + 1),
        (L.choose j : ℝ) * ((n : ℝ) ^ j * Real.exp (-c * n)) := by
    intro n
    rw [add_comm, add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [one_pow, mul_one, neg_mul]
    ring
  simp_rw [e]
  exact summable_sum fun j _ => (Real.summable_pow_mul_exp_neg_nat_mul j hc).mul_left _

/-- The real weighted sum of an exponential profile of a larger rate is summable over `ℤ`. -/
theorem summable_weight_mul_exp {a a' : ℝ} (haa : a < a') (L : ℕ) (C : ℝ) :
    Summable fun h : ℤ => Real.exp (a * |(h : ℝ)|) * (1 + |(h : ℝ)|) ^ L *
      (C * Real.exp (-(a' * |(h : ℝ)|))) := by
  have e : ∀ h : ℤ, Real.exp (a * |(h : ℝ)|) * (1 + |(h : ℝ)|) ^ L *
      (C * Real.exp (-(a' * |(h : ℝ)|))) =
      C * ((1 + |(h : ℝ)|) ^ L * Real.exp (-((a' - a) * |(h : ℝ)|))) := by
    intro h
    have : Real.exp (a * |(h : ℝ)|) * Real.exp (-(a' * |(h : ℝ)|)) =
        Real.exp (-((a' - a) * |(h : ℝ)|)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc Real.exp (a * |(h : ℝ)|) * (1 + |(h : ℝ)|) ^ L * (C * Real.exp (-(a' * |(h : ℝ)|)))
        = C * ((1 + |(h : ℝ)|) ^ L *
            (Real.exp (a * |(h : ℝ)|) * Real.exp (-(a' * |(h : ℝ)|)))) := by ring
      _ = _ := by rw [this]
  simp_rw [e]
  refine Summable.mul_left _ ?_
  have hc : 0 < a' - a := by linarith
  refine Summable.of_nat_of_neg ?_ ?_
  · simpa using summable_poly_mul_exp hc L
  · simpa using summable_poly_mul_exp hc L

/-- **Exponential profiles of a larger rate have finite weighted sums.** -/
theorem wsum_expProfile_lt_top {a a' : ℝ} (haa : a < a') (L : ℕ) (C : ℝ) :
    wsum a L (expProfile C a') < ⊤ := by
  rcases le_or_gt C 0 with hC | hC
  · have hz : ∀ h, expProfile C a' h = 0 := fun h => by
      unfold expProfile
      exact ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hC (Real.exp_pos _).le)
    simp [wsum, hz]
  · have e : wsum a L (expProfile C a') = ∑' h : ℤ, ENNReal.ofReal
        (Real.exp (a * |(h : ℝ)|) * (1 + |(h : ℝ)|) ^ L * (C * Real.exp (-(a' * |(h : ℝ)|)))) := by
      unfold wsum modeWeight expProfile
      exact tsum_congr fun h => (ENNReal.ofReal_mul (by positivity)).symm
    rw [e, ← ENNReal.ofReal_tsum_of_nonneg
      (fun h => mul_nonneg (by positivity) (mul_nonneg hC.le (Real.exp_pos _).le))
      (summable_weight_mul_exp haa L C)]
    exact ENNReal.ofReal_lt_top

/-! ### The history supremum of the transverse inverse -/

/-- The inverse-square weights `(1 + |h|)⁻²` are summable over `ℤ`. -/
theorem summable_inv_sq_weight : Summable fun h : ℤ => ((1 + |(h : ℝ)|) ^ 2)⁻¹ := by
  have hn : Summable fun n : ℕ => ((1 + (n : ℝ)) ^ 2)⁻¹ := by
    have := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).comp_injective
      (add_left_injective 1)
    refine this.congr fun n => ?_
    simp [Function.comp, one_div, add_comm]
  refine Summable.of_nat_of_neg ?_ ?_
  · simpa using hn
  · simpa using hn

/-- The gain constant `π⁻¹ ∑_h (1 + |h|)⁻²` of the history supremum. -/
def cGain : ℝ≥0∞ := ENNReal.ofReal (Real.pi⁻¹ * ∑' h : ℤ, ((1 + |(h : ℝ)|) ^ 2)⁻¹)

theorem cGain_ne_top : cGain ≠ ⊤ := ENNReal.ofReal_ne_top

/-- The mode gain against one fast weight: `(2π|h|)⁻¹ (1+|h|)⁻¹ ≤ π⁻¹ (1+|h|)⁻²`. -/
theorem modeGain_mul_weight_le {a : ℝ} (L : ℕ) (h : ℤ) :
    modeWeight a L h * modeGain h ≤
      ENNReal.ofReal (Real.pi⁻¹ * ((1 + |(h : ℝ)|) ^ 2)⁻¹) * modeWeight a (L + 1) h := by
  unfold modeGain
  split_ifs with h0
  · simp
  · have h1 : (1 : ℝ) ≤ |(h : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs h0
    have hpos : 0 < 2 * Real.pi * |(h : ℝ)| := by positivity
    unfold modeMul modeWeight
    rw [← ENNReal.ofReal_inv_of_pos hpos, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have he : 0 < Real.exp (a * |(h : ℝ)|) := Real.exp_pos _
    have hw : 0 < 1 + |(h : ℝ)| := by positivity
    rw [pow_succ]
    have key : (2 * Real.pi * |(h : ℝ)|)⁻¹ ≤ Real.pi⁻¹ * ((1 + |(h : ℝ)|) ^ 2)⁻¹ * (1 + |(h : ℝ)|) := by
      rw [show Real.pi⁻¹ * ((1 + |(h : ℝ)|) ^ 2)⁻¹ * (1 + |(h : ℝ)|) =
        (Real.pi * (1 + |(h : ℝ)|))⁻¹ by field_simp]
      apply inv_anti₀ (by positivity)
      nlinarith [Real.pi_pos]
    calc Real.exp (a * |(h : ℝ)|) * (1 + |(h : ℝ)|) ^ L * (2 * Real.pi * |(h : ℝ)|)⁻¹
        ≤ Real.exp (a * |(h : ℝ)|) * (1 + |(h : ℝ)|) ^ L *
            (Real.pi⁻¹ * ((1 + |(h : ℝ)|) ^ 2)⁻¹ * (1 + |(h : ℝ)|)) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = Real.pi⁻¹ * ((1 + |(h : ℝ)|) ^ 2)⁻¹ *
            (Real.exp (a * |(h : ℝ)|) * ((1 + |(h : ℝ)|) ^ L * (1 + |(h : ℝ)|))) := by ring

/-- **The mode gain of a history supremum** costs one fast weight and `cGain`, mode by mode
before summing. -/
theorem wsum_modeGain_iSup_le (a : ℝ) (L : ℕ) (S : Set ℝ) (g : ℤ → ℝ → ℝ≥0∞) :
    wsum a L (fun h => modeGain h * ⨆ s ∈ S, g h s) ≤
      cGain * ⨆ s ∈ S, wsum a (L + 1) (fun h => g h s) := by
  have hpt : ∀ h, modeWeight a L h * (modeGain h * ⨆ s ∈ S, g h s) ≤
      ENNReal.ofReal (Real.pi⁻¹ * ((1 + |(h : ℝ)|) ^ 2)⁻¹) *
        ⨆ s ∈ S, wsum a (L + 1) (fun k => g k s) := by
    intro h
    rw [← mul_assoc]
    refine (mul_le_mul_left (modeGain_mul_weight_le L h) _).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_right ?_ _
    rw [ENNReal.mul_iSup]
    refine iSup_mono fun s => ?_
    rw [ENNReal.mul_iSup]
    refine iSup_mono fun _ => ?_
    exact ENNReal.le_tsum (f := fun k => modeWeight a (L + 1) k * g k s) h
  refine (ENNReal.tsum_le_tsum hpt).trans ?_
  rw [ENNReal.tsum_mul_right]
  refine mul_le_mul_left ?_ _
  unfold cGain
  rw [← tsum_mul_left, ENNReal.ofReal_tsum_of_nonneg (fun h => by positivity)
    (summable_inv_sq_weight.mul_left _)]

/-- The mode gain lowers the fast weight by one: `(1+|h|)(2π|h|)⁻¹ ≤ π⁻¹` for `h ≠ 0`. -/
theorem wsum_modeGain_succ_le (a : ℝ) (L : ℕ) (f : ℤ → ℝ≥0∞) :
    wsum a (L + 1) (fun h => modeGain h * f h) ≤ ENNReal.ofReal Real.pi⁻¹ * wsum a L f := by
  rw [← wsum_const_mul]
  refine ENNReal.tsum_le_tsum fun h => ?_
  rw [← mul_assoc, ← mul_assoc]
  refine mul_le_mul_left ?_ _
  unfold modeGain
  split_ifs with h0
  · simp
  · have h1 : (1 : ℝ) ≤ |(h : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs h0
    have hpos : 0 < 2 * Real.pi * |(h : ℝ)| := by positivity
    unfold modeMul modeWeight
    rw [← ENNReal.ofReal_inv_of_pos hpos, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have he : 0 < Real.exp (a * |(h : ℝ)|) := Real.exp_pos _
    rw [pow_succ]
    have key : (1 + |(h : ℝ)|) * (2 * Real.pi * |(h : ℝ)|)⁻¹ ≤ Real.pi⁻¹ := by
      rw [← div_eq_mul_inv, div_le_iff₀ hpos]
      rw [show Real.pi⁻¹ * (2 * Real.pi * |(h : ℝ)|) = 2 * |(h : ℝ)| by field_simp]
      linarith
    calc Real.exp (a * |(h : ℝ)|) * ((1 + |(h : ℝ)|) ^ L * (1 + |(h : ℝ)|)) *
          (2 * Real.pi * |(h : ℝ)|)⁻¹
        = Real.exp (a * |(h : ℝ)|) * (1 + |(h : ℝ)|) ^ L *
            ((1 + |(h : ℝ)|) * (2 * Real.pi * |(h : ℝ)|)⁻¹) := by ring
      _ ≤ Real.exp (a * |(h : ℝ)|) * (1 + |(h : ℝ)|) ^ L * Real.pi⁻¹ :=
          mul_le_mul_of_nonneg_left key (by positivity)

end AVRegularity.Providers.Majorant
end

section
open scoped ENNReal
open AVRegularity
namespace AVRegularity.Providers.Majorant

/-! **The weighted structural norm of `genMode`.** `genNorm … e a mres L t` bounds the
weighted mode sum `∑_h e^{a|h|}(1+|h|)^L genMode e mres h t` at the time `t` by structural
recursion (`wsum_genMode_le`; both are resolved in time):

* sums add and products multiply (`wsum_mconv_le`);
* the fast derivatives (`dPhase`, `dInternal`, the final-phase term of `dOld`) cost one fast
  weight `L ↦ L + 1`; the transverse primitive gains `(2π)⁻¹` at weight `0` and lowers the fast
  weight by one at the factor `π⁻¹` otherwise; the transverse inverse takes the supremum of its
  flux over the history `[t₀, t]` at one more fast weight, with the factor `(4/3) cGain` (the
  weighted mode sum is bounded mode by mode before the supremum), and its initial state
  at `t₀`;
* the reserve derivatives cost their Cauchy factors (`⊤` past the outer reserve);
* the zero-mode nodes (`mean`, `famCell`) and the child evaluation `evalChild` read their input
  only at mode zero; there the rate switches to the inner rate `a₀` and the fast weight restarts
  at `0` (for `evalChild` the weight is carried by `κ.child`: the restoration of the fast weights
  by the final-phase strip), and `evalChild` keeps its cutoff weight
  `ϖ_{i+1,𝗉'}(t)`;
* a time letter has its value `|L(t)|`.

So the expressions of the construction are measured at an outer rate `a` (up to the `6π bw`
decay of `MajOK`) on their context levels and at the rate `a₀` of the certified old coefficients
inside cell and family functions. Pointwise, `modeWeight a 0 h * f h ≤ wsum a 0 f`
(`le_wsum_single`). -/

/-- **The weighted structural norm** of an expression, at the outer rate `a`, the inner rate
`a₀`, the reserve `mres`, the fast weight `L` and the time `t`. -/
def genNorm (D : OCData) (κ : MajConsts) (Δ a₀ : ℝ)
    (leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞)) :
    {s : GenSort} → {i : ℕ} → {p : ℤ} → Gen s i p → ℝ → ℝ → ℕ → ℝ → ℝ≥0∞
  | _, _, _, e@(.geo fr L), a, mres, Lw, _ =>
      (leaf e).elim (wsum a Lw (κ.geo fr L)) fun B => wsum a Lw (B mres)
  | _, _, _, e@(.drift c), a, mres, Lw, _ =>
      (leaf e).elim (wsum a Lw (κ.drift c)) fun B => wsum a Lw (B mres)
  | _, _, _, e@(.time L), a, mres, Lw, t =>
      (leaf e).elim (ENNReal.ofReal |L.eval D t|) fun B => wsum a Lw (B mres)
  | _, _, _, e@(.add x y), a, mres, Lw, t =>
      (leaf e).elim (genNorm D κ Δ a₀ leaf x a mres Lw t + genNorm D κ Δ a₀ leaf y a mres Lw t)
        fun B => wsum a Lw (B mres)
  | _, _, _, e@(.mul x y), a, mres, Lw, t =>
      (leaf e).elim (genNorm D κ Δ a₀ leaf x a mres Lw t * genNorm D κ Δ a₀ leaf y a mres Lw t)
        fun B => wsum a Lw (B mres)
  | _, i, p, e@(.dOld j x), a, mres, Lw, t =>
      (leaf e).elim
        ((if mres + Δ ≤ 2 then κ.Cold / ENNReal.ofReal (D.eps i * Δ) *
            genNorm D κ Δ a₀ leaf x a (mres + Δ) Lw t else ⊤) +
          (if j = transverseIndex p then
            ENNReal.ofReal (2 * Real.pi / D.eps i) * genNorm D κ Δ a₀ leaf x a mres (Lw + 1) t
            else 0))
        fun B => wsum a Lw (B mres)
  | _, _, _, e@(.dPhase x), a, mres, Lw, t =>
      (leaf e).elim (ENNReal.ofReal (2 * Real.pi) * genNorm D κ Δ a₀ leaf x a mres (Lw + 1) t)
        fun B => wsum a Lw (B mres)
  | _, i, _, e@(.dSlowFam _ c), a, mres, Lw, t =>
      (leaf e).elim
        (if mres + Δ ≤ 2 then κ.Cslow / ENNReal.ofReal (D.eps (i - 1) * Δ) *
            genNorm D κ Δ a₀ leaf c a (mres + Δ) Lw t else ⊤)
        fun B => wsum a Lw (B mres)
  | _, i, _, e@(.dSlowCell _ w), a, mres, Lw, t =>
      (leaf e).elim
        (if mres + Δ ≤ 2 then κ.Cslow / ENNReal.ofReal (D.eps (i - 1) * Δ) *
            genNorm D κ Δ a₀ leaf w a (mres + Δ) Lw t else ⊤)
        fun B => wsum a Lw (B mres)
  | _, _, _, e@(.dInternal w), a, mres, Lw, t =>
      (leaf e).elim (ENNReal.ofReal (2 * Real.pi) * genNorm D κ Δ a₀ leaf w a mres (Lw + 1) t)
        fun B => wsum a Lw (B mres)
  | _, _, _, e@(.restrict x), a, mres, Lw, t =>
      (leaf e).elim (genNorm D κ Δ a₀ leaf x a mres Lw t) fun B => wsum a Lw (B mres)
  | _, _, p, e@(.cellInv F t₀ ι), a, mres, Lw, t =>
      (leaf e).elim (genNorm D κ Δ a₀ leaf ι a mres Lw t₀ +
          ENNReal.ofReal (4 / 3) * cGain *
            ⨆ s ∈ Set.Icc t₀ t, genNorm D κ Δ a₀ leaf (F (transverseIndex p)) a mres (Lw + 1) s)
        fun B => wsum a Lw (B mres)
  | _, _, _, e@(.transPrim w), a, mres, Lw, t =>
      (leaf e).elim (if Lw = 0 then ENNReal.ofReal (2 * Real.pi)⁻¹ * genNorm D κ Δ a₀ leaf w a mres 0 t
          else ENNReal.ofReal Real.pi⁻¹ * genNorm D κ Δ a₀ leaf w a mres (Lw - 1) t)
        fun B => wsum a Lw (B mres)
  | _, _, _, e@(.solved ..), a, mres, Lw, _ => (leaf e).elim ⊤ fun B => wsum a Lw (B mres)
  | _, _, _, e@(.mean w), a, mres, Lw, t =>
      (leaf e).elim (genNorm D κ Δ a₀ leaf w a₀ mres 0 t) fun B => wsum a Lw (B mres)
  | _, _, _, e@(.famCell c), a, mres, Lw, t =>
      (leaf e).elim (genNorm D κ Δ a₀ leaf c a₀ mres 0 t) fun B => wsum a Lw (B mres)
  | _, i, _, e@(.evalChild p' c), a, mres, Lw, t =>
      (leaf e).elim
        (ENNReal.ofReal (ocCutoff D.α D.q D.Λ (i + 1) p' t) * wsum a Lw κ.child *
          genNorm D κ Δ a₀ leaf c a₀ mres 0 t)
        fun B => wsum a Lw (B mres)

theorem le_wsum_single (a : ℝ) (L : ℕ) (f : ℤ → ℝ≥0∞) (h : ℤ) :
    modeWeight a L h * f h ≤ wsum a L f :=
  ENNReal.le_tsum (f := fun k => modeWeight a L k * f k) h

theorem le_wsum_zero (a : ℝ) (L : ℕ) (f : ℤ → ℝ≥0∞) : f 0 ≤ wsum a L f := by
  simpa [modeWeight_zero] using le_wsum_single a L f 0

theorem wsum_mul_const (a : ℝ) (L : ℕ) (f : ℤ → ℝ≥0∞) (c : ℝ≥0∞) :
    wsum a L (fun h => f h * c) = wsum a L f * c := by
  simp only [mul_comm _ c]
  rw [wsum_const_mul, mul_comm]

theorem wsum_derivCost_le (a : ℝ) (L : ℕ) (C : ℝ≥0∞) (ε Δ mres : ℝ) (g : ℤ → ℝ≥0∞) :
    wsum a L (fun h => derivCost C ε Δ mres (g h)) ≤
      if mres + Δ ≤ 2 then C / ENNReal.ofReal (ε * Δ) * wsum a L g else ⊤ := by
  unfold derivCost
  split_ifs
  · rw [wsum_const_mul]
  · exact le_top

/-- The final-phase term of the recentering derivative costs one fast weight. -/
theorem wsum_phaseShift_le (a : ℝ) (L : ℕ) (ε : ℝ) (g : ℤ → ℝ≥0∞) :
    wsum a L (fun h => ENNReal.ofReal (2 * Real.pi * |(h : ℝ)| / ε) * g h) ≤
      ENNReal.ofReal (2 * Real.pi / ε) * wsum a (L + 1) g := by
  rw [← wsum_const_mul]
  refine ENNReal.tsum_le_tsum fun h => ?_
  rw [← mul_assoc, ← mul_assoc]
  refine mul_le_mul_left ?_ _
  unfold modeWeight
  rw [← ENNReal.ofReal_mul (by positivity)]
  rcases le_or_gt ε 0 with hε | hε
  · have : 2 * Real.pi * |(h : ℝ)| / ε ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos (by positivity) hε
    rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by positivity) this)]
    exact zero_le
  · rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hh : |(h : ℝ)| ≤ 1 + |(h : ℝ)| := by linarith
    have he : 0 ≤ Real.exp (a * |(h : ℝ)|) := (Real.exp_pos _).le
    have hp : 0 ≤ (1 + |(h : ℝ)|) ^ L := by positivity
    have h2 : 2 * Real.pi * |(h : ℝ)| / ε ≤ 2 * Real.pi / ε * (1 + |(h : ℝ)|) := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hε]
      exact mul_le_mul_of_nonneg_left hh (by positivity)
    calc Real.exp (a * |(h : ℝ)|) * (1 + |(h : ℝ)|) ^ L * (2 * Real.pi * |(h : ℝ)| / ε)
        ≤ Real.exp (a * |(h : ℝ)|) * (1 + |(h : ℝ)|) ^ L *
            (2 * Real.pi / ε * (1 + |(h : ℝ)|)) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg he hp)
      _ = Real.exp (a * |(h : ℝ)|) * (1 + |(h : ℝ)|) ^ (L + 1) * (2 * Real.pi / ε) := by ring

theorem wsum_optionElim (a : ℝ) (L : ℕ) (o : Option (ℝ → ℤ → ℝ≥0∞)) (X : ℤ → ℝ≥0∞)
    (mres : ℝ) :
    wsum a L (fun h => o.elim (X h) fun B => B mres h) =
      o.elim (wsum a L X) fun B => wsum a L (B mres) := by
  cases o <;> rfl

theorem optionElim_le {β : Type*} (o : Option β) {x y : ℝ≥0∞} (f : β → ℝ≥0∞) (hxy : x ≤ y) :
    o.elim x f ≤ o.elim y f := by
  cases o
  · exact hxy
  · exact le_rfl

section Main

variable (D : OCData) (κ : MajConsts) (Δ a₀ : ℝ)
  (leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞))

/-- **The weighted mode sum of `genMode` is bounded by the structural norm.** -/
theorem wsum_genMode_le (ha₀ : 0 ≤ a₀) {s : GenSort} {i : ℕ} {p : ℤ} (e : Gen s i p) :
    ∀ (t a mres : ℝ) (L : ℕ), 0 ≤ a →
      wsum a L (fun h => genMode D κ Δ leaf e mres h t) ≤ genNorm D κ Δ a₀ leaf e a mres L t := by
  induction e with
  | geo fr Lt =>
    intro t a mres L _
    simp only [genMode, genNorm]
    rw [wsum_optionElim]
  | drift c =>
    intro t a mres L _
    simp only [genMode, genNorm]
    rw [wsum_optionElim]
  | time Lt =>
    intro t a mres L _
    simp only [genMode, genNorm]
    rw [wsum_optionElim]
    exact optionElim_le _ _ (wsum_single a L _).le
  | add x y ihx ihy =>
    intro t a mres L ha
    simp only [genMode, genNorm]
    rw [wsum_optionElim]
    refine optionElim_le _ _ ?_
    rw [wsum_add]
    exact add_le_add (ihx t a mres L ha) (ihy t a mres L ha)
  | mul x y ihx ihy =>
    intro t a mres L ha
    simp only [genMode, genNorm]
    rw [wsum_optionElim]
    refine optionElim_le _ _ ?_
    exact (wsum_mconv_le ha L _ _).trans (mul_le_mul' (ihx t a mres L ha) (ihy t a mres L ha))
  | dOld j x ihx =>
    intro t a mres L ha
    simp only [genMode, genNorm]
    rw [wsum_optionElim]
    refine optionElim_le _ _ ?_
    rw [wsum_add]
    refine add_le_add ((wsum_derivCost_le a L _ _ _ _ _).trans ?_) ?_
    · split_ifs
      · exact mul_le_mul_right (ihx t a (mres + Δ) L ha) _
      · exact le_rfl
    · split_ifs
      · exact (wsum_phaseShift_le a L _ _).trans (mul_le_mul_right (ihx t a mres (L + 1) ha) _)
      · simp [wsum]
  | dPhase x ihx =>
    intro t a mres L ha
    simp only [genMode, genNorm]
    rw [wsum_optionElim]
    refine optionElim_le _ _ ?_
    exact (wsum_modeMul_le a L _).trans (mul_le_mul_right (ihx t a mres (L + 1) ha) _)
  | dSlowFam j c ihc =>
    intro t a mres L ha
    simp only [genMode, genNorm]
    rw [wsum_optionElim]
    refine optionElim_le _ _ ((wsum_derivCost_le a L _ _ _ _ _).trans ?_)
    split_ifs
    · exact mul_le_mul_right (ihc t a (mres + Δ) L ha) _
    · exact le_rfl
  | dSlowCell j w ihw =>
    intro t a mres L ha
    simp only [genMode, genNorm]
    rw [wsum_optionElim]
    refine optionElim_le _ _ ((wsum_derivCost_le a L _ _ _ _ _).trans ?_)
    split_ifs
    · exact mul_le_mul_right (ihw t a (mres + Δ) L ha) _
    · exact le_rfl
  | dInternal w ihw =>
    intro t a mres L ha
    simp only [genMode, genNorm]
    rw [wsum_optionElim]
    refine optionElim_le _ _ ?_
    exact (wsum_modeMul_le a L _).trans (mul_le_mul_right (ihw t a mres (L + 1) ha) _)
  | restrict x ihx =>
    intro t a mres L ha
    simp only [genMode, genNorm]
    rw [wsum_optionElim]
    exact optionElim_le _ _ (ihx t a mres L ha)
  | @cellInv i p F t₀ ι ihF ihι =>
    intro t a mres L ha
    simp only [genMode, genNorm]
    rw [wsum_optionElim]
    refine optionElim_le _ _ ?_
    rw [wsum_add]
    refine add_le_add (ihι t₀ a mres L ha) ?_
    have e : wsum a L (fun h => ENNReal.ofReal (4 / 3) * modeGain h *
        ⨆ s ∈ Set.Icc t₀ t, genMode D κ Δ leaf (F (transverseIndex p)) mres h s) =
        ENNReal.ofReal (4 / 3) * wsum a L (fun h => modeGain h *
          ⨆ s ∈ Set.Icc t₀ t, genMode D κ Δ leaf (F (transverseIndex p)) mres h s) := by
      rw [← wsum_const_mul]
      simp only [mul_assoc]
    rw [e, mul_assoc]
    refine mul_le_mul_right ((wsum_modeGain_iSup_le a L _ _).trans
      (mul_le_mul_right (iSup₂_mono fun s _ => ihF _ s a mres (L + 1) ha) _)) _
  | transPrim w ihw =>
    intro t a mres L ha
    simp only [genMode, genNorm]
    rw [wsum_optionElim]
    refine optionElim_le _ _ ?_
    rcases L with _ | L
    · simp only [↓reduceIte]
      exact (wsum_modeGain_le a 0 _).trans (mul_le_mul_right (ihw t a mres 0 ha) _)
    · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      exact (wsum_modeGain_succ_le a L _).trans (mul_le_mul_right (ihw t a mres L ha) _)
  | solved G v F q t₀ t₁ c sZ ι =>
    intro t a mres L _
    simp only [genMode, genNorm]
    rw [wsum_optionElim]
    exact optionElim_le _ _ le_top
  | mean w ihw =>
    intro t a mres L _
    simp only [genMode, genNorm]
    rw [wsum_optionElim]
    refine optionElim_le _ _ ?_
    rw [wsum_single]
    exact (le_wsum_zero a₀ 0 _).trans (ihw t a₀ mres 0 ha₀)
  | famCell c ihc =>
    intro t a mres L _
    simp only [genMode, genNorm]
    rw [wsum_optionElim]
    refine optionElim_le _ _ ?_
    rw [wsum_single]
    exact (le_wsum_zero a₀ 0 _).trans (ihc t a₀ mres 0 ha₀)
  | evalChild p' c ihc =>
    intro t a mres L _
    simp only [genMode, genNorm]
    rw [wsum_optionElim]
    refine optionElim_le _ _ ?_
    rw [wsum_mul_const, wsum_const_mul]
    exact mul_le_mul_right ((le_wsum_zero a₀ 0 _).trans (ihc t a₀ mres 0 ha₀)) _

/-- **Pointwise decay** from the structural norm at the rate `a`. -/
theorem genMode_le_of_genNorm (ha₀ : 0 ≤ a₀) {s : GenSort} {i : ℕ} {p : ℤ} (e : Gen s i p)
    {a : ℝ} (ha : 0 ≤ a) (mres : ℝ) (h : ℤ) (t : ℝ) :
    modeWeight a 0 h * genMode D κ Δ leaf e mres h t ≤ genNorm D κ Δ a₀ leaf e a mres 0 t :=
  (le_wsum_single a 0 (fun k => genMode D κ Δ leaf e mres k t) h).trans
    (wsum_genMode_le D κ Δ a₀ leaf ha₀ e t a mres 0 ha)

end Main

end AVRegularity.Providers.Majorant
end

section
open Homogenization AVRegularity MeasureTheory
namespace AVRegularity.Providers.Majorant

/-! **Uniqueness of denotations on the output domain** (a conditional statement). If the
denotation of every export of `𝒮` is unique on the pulse window and the admissible chains of its
slot, then so is the denotation of every scheduled expression with seed provenance
(`denotes_agreeOn_of_exports`).

The induction follows the restricted parallel invariance (`ParInvOn`):
* the recentering derivatives (`dOld`, `dSlowFam`, `dSlowCell`) see the inputs on an admissible
  neighbourhood (`recenter_eventually`);
* the transverse inverse sees the flux on `[slotStart, t] ⊆ J_𝗉` and the initial state at
  `slotStart`;
* the evaluation at the appended child sees the family at the odd, admissible child
  (`appendChild_admissible`), at a time of its window;
* there is no `solved` node outside the exports (`FromSeed`).

The export hypothesis is an assumption on the exports, hence the distinct name. -/

open AVRegularity.Providers.GenSem

/-- Agreement of two functions of a sort on the pulse window and the admissible chains of the
slot `p` of level `i`. -/
def AgreeOn (D : OCData) (b : ℝ) (j₀ i : ℕ) (p : ℤ) : (s : GenSort) → s.Sem → s.Sem → Prop
  | .ctx, f, f' => ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p, ∀ ch, IsAdmissibleChain D b j₀ i p ch →
      ∀ ζ, f t ch ζ = f' t ch ζ
  | .cell, f, f' => ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p, ∀ ch, IsAdmissibleChain D b j₀ i p ch →
      ∀ η, f t ch η = f' t ch η
  | .fam, f, f' => ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p, ∀ ch, IsAdmissibleChain D b j₀ i p ch →
      f t ch = f' t ch

/-- The transverse inverse at a chain sees the flux only on `[t₀, t]` and the initial state only
at `t₀`. -/
theorem transverseInverseSem_congr_on (D : OCData) (i : ℕ) (p : ℤ)
    (F F' : Fin 2 → GenSort.Sem .cell) (t₀ : ℝ) (ι ι' : GenSort.Sem .cell) (t : ℝ)
    (ch : RealChain) (η : Vec 2) (ht : t₀ ≤ t)
    (hF : ∀ k, ∀ s ∈ Set.Icc t₀ t, F k s ch = F' k s ch) (hι : ι t₀ ch = ι' t₀ ch) :
    transverseInverseSem D i p F t₀ ι t ch η = transverseInverseSem D i p F' t₀ ι' t ch η := by
  have key : ∀ h : ℤ, (∫ s in t₀..t, modeKernel D i (transverseIndex p) ch h t s *
      phaseCoeff (transverseIndex p) (F (transverseIndex p) s ch) h) =
      ∫ s in t₀..t, modeKernel D i (transverseIndex p) ch h t s *
      phaseCoeff (transverseIndex p) (F' (transverseIndex p) s ch) h := by
    intro h
    apply intervalIntegral.integral_congr
    intro s hs
    rw [Set.uIcc_of_le ht] at hs
    simp only [hF _ s hs]
  simp only [transverseInverseSem, key, hι]

section Main

variable {D : OCData} (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) {b : ℝ} (hb : 0 < b) {j₀ : ℕ}
  (hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
    2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ b / (64 * (8 * Real.pi ^ 2)))
  {𝒮 : SeedExports}
  (hexp : ∀ {i p} (e : Gen .ctx i p), 𝒮 e → ∀ f f', Gen.Denotes D b j₀ e f →
      Gen.Denotes D b j₀ e f' → AgreeOn D b j₀ i p .ctx f f')

include hΛ hζ hb hstart hexp in
/-- **Uniqueness of denotations on the output domain**, from that of the exports. -/
theorem denotes_agreeOn_of_exports {s : GenSort} {i : ℕ} {p : ℤ} {e : Gen s i p} {f : s.Sem}
    (hd : Gen.Denotes D b j₀ e f) :
    Gen.FromSeed 𝒮 e → Gen.IsScheduled D e → ∀ {f' : s.Sem}, Gen.Denotes D b j₀ e f' →
      AgreeOn D b j₀ i p s f f' := by
  induction hd with
  | @geo i p fr L =>
    intro _ _ f' hd'
    cases hd'
    exact fun _ _ _ _ _ => rfl
  | @drift i p c =>
    intro _ _ f' hd'
    cases hd'
    exact fun _ _ _ _ _ => rfl
  | @time s i p L =>
    intro _ _ f' hd'
    cases hd'
    cases s
    · exact fun _ _ _ _ _ => rfl
    · exact fun _ _ _ _ => rfl
    · exact fun _ _ _ _ _ => rfl
  | @add s i p a b' fa fb ha hb' iha ihb =>
    intro hfs hsch f' hd'
    cases hfs with
    | «export» hx => exact hexp _ hx _ _ (Gen.Denotes.add ha hb') hd'
    | add hfa hfb =>
      cases hsch with
      | add hsa hsb =>
        cases hd' with
        | add ha' hb'' =>
          have h1 := iha hfa hsa ha'
          have h2 := ihb hfb hsb hb''
          cases s
          · intro t ht ch hA ζ
            show fa t ch ζ + fb t ch ζ = _ + _
            rw [h1 t ht ch hA ζ, h2 t ht ch hA ζ]
          · intro t ht ch hA
            show fa t ch + fb t ch = _ + _
            rw [h1 t ht ch hA, h2 t ht ch hA]
          · intro t ht ch hA η
            show fa t ch η + fb t ch η = _ + _
            rw [h1 t ht ch hA η, h2 t ht ch hA η]
  | @mul s i p a b' fa fb ha hb' iha ihb =>
    intro hfs hsch f' hd'
    cases hfs with
    | «export» hx => exact hexp _ hx _ _ (Gen.Denotes.mul ha hb') hd'
    | mul hfa hfb =>
      cases hsch with
      | mul hsa hsb =>
        cases hd' with
        | mul ha' hb'' =>
          have h1 := iha hfa hsa ha'
          have h2 := ihb hfb hsb hb''
          cases s
          · intro t ht ch hA ζ
            show fa t ch ζ * fb t ch ζ = _ * _
            rw [h1 t ht ch hA ζ, h2 t ht ch hA ζ]
          · intro t ht ch hA
            show fa t ch * fb t ch = _ * _
            rw [h1 t ht ch hA, h2 t ht ch hA]
          · intro t ht ch hA η
            show fa t ch η * fb t ch η = _ * _
            rw [h1 t ht ch hA η, h2 t ht ch hA η]
  | @dOld i p j a fa ha iha =>
    intro hfs hsch f' hd'
    cases hfs with
    | «export» hx => exact hexp _ hx _ _ (Gen.Denotes.dOld j ha) hd'
    | dOld _ hfa =>
      cases hsch with
      | dOld _ hsa =>
        cases hd' with
        | @dOld _ _ _ _ fa' ha' =>
          have ih := iha hfa hsa ha'
          intro t ht ch hA ζ
          have hN := recenter_eventually D hζ b j₀ i p hA
          have hev : (fun h : Vec 2 => fa t (ch.recenter D h) (ζ + (D.eps i)⁻¹ • h)) =ᶠ[nhds 0]
              (fun h : Vec 2 => fa' t (ch.recenter D h) (ζ + (D.eps i)⁻¹ • h)) :=
            hN.mono fun h hh => ih t ht _ hh _
          show fderiv ℝ _ 0 _ = fderiv ℝ _ 0 _
          rw [hev.fderiv_eq]
  | @dPhase i p a fa ha iha =>
    intro hfs hsch f' hd'
    cases hfs with
    | «export» hx => exact hexp _ hx _ _ (Gen.Denotes.dPhase ha) hd'
    | dPhase hfa =>
      cases hsch with
      | dPhase hsa =>
        cases hd' with
        | @dPhase _ _ _ fa' ha' =>
          have ih := iha hfa hsa ha'
          intro t ht ch hA ζ
          have : fa t ch = fa' t ch := funext fun z => ih t ht ch hA z
          show fderiv ℝ _ _ _ = fderiv ℝ _ _ _
          rw [this]
  | @dSlowFam i p j c fc hc ihc =>
    intro hfs hsch f' hd'
    cases hfs with
    | dSlowFam _ hfa =>
      cases hsch with
      | dSlowFam _ hsa =>
        cases hd' with
        | @dSlowFam _ _ _ _ fc' hc' =>
          have ih := ihc hfa hsa hc'
          intro t ht ch hA
          have hN := recenter_eventually D hζ b j₀ i p hA
          have hev : (fun h : Vec 2 => fc t (ch.recenter D h)) =ᶠ[nhds 0]
              (fun h : Vec 2 => fc' t (ch.recenter D h)) :=
            hN.mono fun h hh => ih t ht _ hh
          show fderiv ℝ _ _ _ = fderiv ℝ _ _ _
          rw [hev.fderiv_eq]
  | @dSlowCell i p j w fw hw ihw =>
    intro hfs hsch f' hd'
    cases hfs with
    | dSlowCell _ hfa =>
      cases hsch with
      | dSlowCell _ hsa =>
        cases hd' with
        | @dSlowCell _ _ _ _ fw' hw' =>
          have ih := ihw hfa hsa hw'
          intro t ht ch hA η
          have hN := recenter_eventually D hζ b j₀ i p hA
          have hev : (fun h : Vec 2 => fw t (ch.recenter D h) η) =ᶠ[nhds 0]
              (fun h : Vec 2 => fw' t (ch.recenter D h) η) :=
            hN.mono fun h hh => ih t ht _ hh η
          show fderiv ℝ _ _ _ = fderiv ℝ _ _ _
          rw [hev.fderiv_eq]
  | @dInternal i p w fw hw ihw =>
    intro hfs hsch f' hd'
    cases hfs with
    | dInternal hfa =>
      cases hsch with
      | dInternal hsa =>
        cases hd' with
        | @dInternal _ _ _ fw' hw' =>
          have ih := ihw hfa hsa hw'
          intro t ht ch hA η
          have : fw t ch = fw' t ch := funext fun z => ih t ht ch hA z
          show fderiv ℝ _ _ _ = fderiv ℝ _ _ _
          rw [this]
  | @restrict i p a fa ha iha =>
    intro hfs hsch f' hd'
    cases hfs with
    | restrict hfa =>
      cases hsch with
      | restrict hsa =>
        cases hd' with
        | restrict ha' => exact iha hfa hsa ha'
  | @cellInv i p F t₀ ι fF fι hF hι ihF ihι =>
    intro hfs hsch f' hd'
    cases hfs with
    | cellInv _ hFa hιa =>
      obtain ⟨h0, hFs, hιs⟩ := IsScheduled.cellInv_inv hsch
      subst h0
      cases hd' with
      | @cellInv _ _ _ _ _ fF' fι' hF' hι' =>
        have ihF' := fun k => ihF k (hFa k) (hFs k) (hF' k)
        have ihι' := ihι hιa hιs hι'
        intro t ht ch hA η
        have ht' : t ∈ Set.Icc (D.slotStart i p) (((p : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ i) := ht
        obtain ⟨hw1, hw2⟩ := ht'
        have hwin : ∀ u, D.slotStart i p ≤ u → u ≤ t → u ∈ ocPulseWindow D.α D.q D.Λ i p :=
          fun u h1 h2 => by
            show u ∈ Set.Icc _ _
            exact ⟨h1, h2.trans hw2⟩
        exact transverseInverseSem_congr_on D i p fF fF' _ fι fι' t ch η hw1
          (fun k u hu => funext fun z => ihF' k u (hwin u hu.1 hu.2) ch hA z)
          (funext fun z => ihι' _ (hwin _ le_rfl hw1) ch hA z)
  | @transPrim i p w fw hw ihw =>
    intro hfs hsch f' hd'
    cases hfs with
    | transPrim hfa =>
      cases hsch with
      | transPrim hsa =>
        cases hd' with
        | @transPrim _ _ _ fw' hw' =>
          have ih := ihw hfa hsa hw'
          intro t ht ch hA η
          have : fw t ch = fw' t ch := funext fun z => ih t ht ch hA z
          simp only [transversePrimitiveSem, this]
  | @solved i p G v F q t₀ t₁ c sZ ι fG fv fF fq fι ω h1 h2 hG hv hF hq hι hsol hzero ihG ihv ihF
      ihq ihι =>
    intro hfs _ _ _
    cases hfs
  | @mean i p w fw hw ihw =>
    intro hfs hsch f' hd'
    cases hfs with
    | mean hfa =>
      cases hsch with
      | mean hsa =>
        cases hd' with
        | @mean _ _ _ fw' hw' =>
          have ih := ihw hfa hsa hw'
          intro t ht ch hA
          have : fw t ch = fw' t ch := funext fun z => ih t ht ch hA z
          simp only [cellMeanSem, this]
  | @famCell i p c fc hc ihc =>
    intro hfs hsch f' hd'
    cases hfs with
    | famCell hfa =>
      cases hsch with
      | famCell hsa =>
        cases hd' with
        | @famCell _ _ _ fc' hc' =>
          have ih := ihc hfa hsa hc'
          exact fun t ht ch hA _ => ih t ht ch hA
  | @evalChild i p p' c fc hc ihc =>
    intro hfs hsch f' hd'
    cases hfs with
    | «export» hx => exact hexp _ hx _ _ (Gen.Denotes.evalChild p' hc) hd'
    | evalChild _ hfa =>
      cases hsch with
      | evalChild _ hodd hsi hsa =>
        cases hd' with
        | @evalChild _ _ _ _ fc' hc' =>
          have ih := ihc hfa hsa hc'
          intro t ht ch hA ζ
          show _ * fc t (ch.appendChild D p' t ζ) = _ * fc' t (ch.appendChild D p' t ζ)
          by_cases hcut : ocCutoff D.α D.q D.Λ (i + 1) p' t = 0
          · rw [hcut, zero_mul, zero_mul]
          · have hτ : 0 < ocTau D.α D.q D.Λ (i + 1) :=
              Construction.Stream.ocTau_pos (α := D.α) (q := D.q) (m := i + 1) hΛ
            have htw := mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hcut
            have hA1 := appendChild_admissible D hΛ hζ hb hstart i p ch hA p' hodd hsi t hcut ζ
            rw [ih t htw _ hA1]

end Main

end AVRegularity.Providers.Majorant
end
