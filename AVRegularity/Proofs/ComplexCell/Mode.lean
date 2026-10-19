-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.Transverse.Link
import Mathlib.Algebra.Order.Star.Real

/-! **The modes of the complex transverse cell inverse**. For a complex transverse metric entry `a`
with `Re a ≥ a₀ > 0` (the complex molecular metric on the carrier), the kernel `exp(−r_h ∫_s^t a)`
and the Duhamel amplitude `W(t) = (2πih/c) ∫_{t₀}^t exp(−r_h ∫_s^t a) F(s) ds` (`modeKC`, `modeWC`):
* restrict to the real kernels and amplitudes `modeK`, `modeW` for real `a` (`modeKC_ofReal`,
  `modeWC_ofReal`);
* obey `‖exp(−r_h ∫_s^t a)‖ ≤ e^{−r_h a₀ (t−s)}` (`norm_modeKC_le`), which gives the gain of the
  inverse, `‖W(t)‖ ≤ sup|F| / (2π|h| a₀)`. -/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Interval

namespace AVRegularity.Providers.ComplexCell

open AVRegularity.Providers.Transverse

/-- The complex mode kernel `exp(−r_h ∫_s^t a)`. -/
def modeKC (c : ℝ) (a : ℝ → ℂ) (h : ℤ) (t s : ℝ) : ℂ :=
  Complex.exp (-((modeRate c h : ℝ) : ℂ) * ∫ u in s..t, a u)

/-- The complex Duhamel amplitude of the mode `h` from zero at `t₀`. -/
def modeWC (c : ℝ) (a : ℝ → ℂ) (F : ℝ → ℂ) (t₀ : ℝ) (h : ℤ) (t : ℝ) : ℂ :=
  modeCoup c h * ∫ s in t₀..t, modeKC c a h t s * F s

theorem modeKC_ofReal (c : ℝ) (a : ℝ → ℝ) (h : ℤ) (t s : ℝ) :
    modeKC c (fun u => (a u : ℂ)) h t s = modeK c a h t s := by
  unfold modeKC modeK
  rw [intervalIntegral.integral_ofReal, ← Complex.ofReal_neg, ← Complex.ofReal_mul,
    ← Complex.ofReal_exp]

theorem modeWC_ofReal (c : ℝ) (a : ℝ → ℝ) (F : ℝ → ℂ) (t₀ : ℝ) (h : ℤ) (t : ℝ) :
    modeWC c (fun u => (a u : ℂ)) F t₀ h t = modeW c a F t₀ h t := by
  unfold modeWC modeW
  simp_rw [modeKC_ofReal]

theorem modeRate_nonneg {c : ℝ} (hc : 0 < c) (h : ℤ) : 0 ≤ modeRate c h := by
  unfold modeRate; positivity

/-- **The kernel decays at the rate of the lower bound of the real part.** -/
theorem norm_modeKC_le {c : ℝ} (hc : 0 < c) {a : ℝ → ℂ} {a₀ : ℝ} (h : ℤ) {s t : ℝ} (hst : s ≤ t)
    (hai : IntervalIntegrable a volume s t) (hre : ∀ u ∈ Icc s t, a₀ ≤ (a u).re) :
    ‖modeKC c a h t s‖ ≤ Real.exp (-(modeRate c h * a₀ * (t - s))) := by
  unfold modeKC
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.mpr ?_
  have hre_int : (∫ u in s..t, a u).re = ∫ u in s..t, (a u).re :=
    (Complex.reCLM.intervalIntegral_comp_comm hai).symm
  have hlow : a₀ * (t - s) ≤ ∫ u in s..t, (a u).re := by
    have h1 : ∫ u in s..t, a₀ ≤ ∫ u in s..t, (a u).re :=
      intervalIntegral.integral_mono_on hst intervalIntegrable_const
        ⟨hai.1.re, hai.2.re⟩ hre
    rw [intervalIntegral.integral_const, smul_eq_mul] at h1
    linarith
  have hr := modeRate_nonneg hc h
  rw [← Complex.ofReal_neg, Complex.re_ofReal_mul, hre_int]
  nlinarith

/-- The integral of the decaying exponential. -/
theorem integral_exp_decay_le {r : ℝ} (hr : 0 < r) (t₀ t : ℝ) :
    ∫ s in t₀..t, Real.exp (-(r * (t - s))) ≤ 1 / r := by
  have hder : ∀ s ∈ uIcc t₀ t, HasDerivAt (fun s => Real.exp (-(r * (t - s))) / r)
      (Real.exp (-(r * (t - s)))) s := by
    intro s _
    have h0 : HasDerivAt (fun s => t - s) (-1) s := by
      have := (hasDerivAt_id s).const_sub t
      simpa using this
    have h1 : HasDerivAt (fun s => -(r * (t - s))) r s := by
      convert (h0.const_mul r).neg using 1; ring
    have h3 := ((Real.hasDerivAt_exp _).comp s h1).div_const r
    convert h3 using 1
    · rfl
    · field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder
    ((Real.continuous_exp.comp (by fun_prop)).intervalIntegrable _ _)]
  simp only [sub_self, mul_zero, neg_zero, Real.exp_zero]
  have : 0 < Real.exp (-(r * (t - t₀))) / r := by positivity
  linarith

end AVRegularity.Providers.ComplexCell
