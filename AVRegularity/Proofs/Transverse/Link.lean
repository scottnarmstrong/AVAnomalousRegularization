-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Lift.SettingDimensionalScales
public import AVRegularity.Construction.Uniqueness.Translate.FieldInverse
public import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Topology.Algebra.InfiniteSum.ContinuousEval
import Mathlib.Topology.Compactness.DeltaGeneratedSpace

section
section
@[expose] public noncomputable section
open MeasureTheory Set
namespace AVRegularity.Providers.Transverse

/-! The modes of the transverse cell inverse: for the rate `r_h = 4π²h²/c`, the metric entry `a`
and the flux mode `F`, the Duhamel amplitude
`W(t) = (2πih/c) ∫_{t₀}^t exp(-r_h ∫_s^t a) F(s) ds`
solves `W' = -r_h a W + (2πih/c) F`, `W(t₀) = 0`, and is bounded by `sup|F| / (2π|h| a_min)` (the
gain of the inverse) and by `(2π|h|/c)(t - t₀) sup|F|`. -/

/-- The decay rate `4π²h²/c` of the mode `h`. -/
def modeRate (c : ℝ) (h : ℤ) : ℝ := 4 * Real.pi ^ 2 * (h : ℝ) ^ 2 / c

/-- The mode kernel `exp(-r_h ∫_s^t a)`. -/
def modeK (c : ℝ) (a : ℝ → ℝ) (h : ℤ) (t s : ℝ) : ℂ :=
  ((Real.exp (-(modeRate c h) * ∫ u in s..t, a u) : ℝ) : ℂ)

/-- The mode coupling `2πih/c`. -/
def modeCoup (c : ℝ) (h : ℤ) : ℂ := 2 * Real.pi * Complex.I * (h : ℂ) / (c : ℂ)

/-- The Duhamel amplitude of the mode `h` from zero at `t₀`. -/
def modeW (c : ℝ) (a : ℝ → ℝ) (F : ℝ → ℂ) (t₀ : ℝ) (h : ℤ) (t : ℝ) : ℂ :=
  modeCoup c h * ∫ s in t₀..t, modeK c a h t s * F s

/-- The primitive `A(x) = ∫_{t₀}^x a`. -/
def primA (a : ℝ → ℝ) (t₀ x : ℝ) : ℝ := ∫ u in t₀..x, a u

theorem modeK_eq {a : ℝ → ℝ} (ha : Continuous a) (c : ℝ) (h : ℤ) (t₀ t s : ℝ) :
    modeK c a h t s = ((Real.exp (-(modeRate c h) * primA a t₀ t) : ℝ) : ℂ) *
      ((Real.exp (modeRate c h * primA a t₀ s) : ℝ) : ℂ) := by
  have hi : ∀ x y : ℝ, IntervalIntegrable a volume x y := fun x y =>
    ha.intervalIntegrable x y
  have e : ∫ u in s..t, a u = primA a t₀ t - primA a t₀ s := by
    unfold primA
    exact (intervalIntegral.integral_interval_sub_left (hi t₀ t) (hi t₀ s)).symm
  rw [modeK, e, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

theorem modeW_eq {a : ℝ → ℝ} (ha : Continuous a) (c : ℝ) (F : ℝ → ℂ) (t₀ : ℝ) (h : ℤ)
    (t : ℝ) :
    modeW c a F t₀ h t = modeCoup c h * (((Real.exp (-(modeRate c h) * primA a t₀ t) : ℝ) : ℂ) *
      ∫ s in t₀..t, ((Real.exp (modeRate c h * primA a t₀ s) : ℝ) : ℂ) * F s) := by
  rw [modeW]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [modeK_eq ha c h t₀ t s]
  ring

theorem hasDerivAt_primA {a : ℝ → ℝ} (ha : Continuous a) (t₀ t : ℝ) :
    HasDerivAt (primA a t₀) (a t) t :=
  intervalIntegral.integral_hasDerivAt_right (ha.intervalIntegrable _ _)
    ha.aestronglyMeasurable.stronglyMeasurableAtFilter ha.continuousAt

theorem modeW_start (c : ℝ) (a : ℝ → ℝ) (F : ℝ → ℂ) (t₀ : ℝ) (h : ℤ) :
    modeW c a F t₀ h t₀ = 0 := by
  simp [modeW]

/-! The mode equation in integrated form for locally integrable fluxes (Carathéodory solutions):
`W(t) - W(s) = ∫_s^t (-r_h a W + (2πih/c) F)`, by the fundamental theorem of calculus for
absolutely continuous functions applied to the real and imaginary parts of `exp(-r A)·∫ exp(r A) F`
and Lebesgue's differentiation theorem. -/

/-- FTC for `P · ∫_{t₀}^x g` with `P` of class `C¹` and `g` integrable. -/
theorem integral_deriv_mul_primitive {P : ℝ → ℝ} (hP : ContDiff ℝ 1 P) {g : ℝ → ℝ} {t₀ t : ℝ}
    (hg : IntervalIntegrable g volume t₀ t) :
    ∫ τ in t₀..t, (deriv P τ * ∫ σ in t₀..τ, g σ) + P τ * g τ =
      P t * ∫ σ in t₀..t, g σ := by
  have hPa : AbsolutelyContinuousOnInterval P t₀ t := (hP.contDiffOn).absolutelyContinuousOnInterval
  have hGa : AbsolutelyContinuousOnInterval (fun x => ∫ σ in t₀..x, g σ) t₀ t :=
    hg.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have h := hPa.integral_deriv_mul_eq_sub hGa
  simp only [intervalIntegral.integral_same, mul_zero, sub_zero] at h
  rw [← h]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hg.ae_hasDerivAt_integral] with τ hτ hτm
  have hd := hτ (uIoc_subset_uIcc hτm) t₀ (by simp)
  rw [hd.deriv]

/-- **The mode equation in integrated form.** -/
theorem modeW_sub_start {a : ℝ → ℝ} (ha : Continuous a) {F : ℝ → ℂ} (c : ℝ) (t₀ : ℝ) (h : ℤ)
    {t : ℝ} (hF : IntervalIntegrable F volume t₀ t) :
    modeW c a F t₀ h t =
      ∫ τ in t₀..t, ((-(modeRate c h) * a τ : ℝ) : ℂ) * modeW c a F t₀ h τ + modeCoup c h * F τ := by
  set r := modeRate c h
  set A := primA a t₀
  have hA : ∀ x, HasDerivAt A (a x) x := hasDerivAt_primA ha t₀
  have hAc : ContDiff ℝ 1 A := by
    rw [contDiff_one_iff_deriv]
    refine ⟨fun x => (hA x).differentiableAt, ?_⟩
    simpa [funext fun x => (hA x).deriv] using ha
  set P : ℝ → ℝ := fun x => Real.exp (-r * A x)
  set E : ℝ → ℝ := fun x => Real.exp (r * A x)
  have hPc : ContDiff ℝ 1 P := Real.contDiff_exp.comp (contDiff_const.mul hAc)
  have hEc : Continuous E := (Real.continuous_exp.comp (continuous_const.mul hAc.continuous))
  have hPd : ∀ x, deriv P x = -r * a x * P x := by
    intro x
    have := ((hA x).const_mul (-r)).exp
    rw [this.deriv]; simp only [P]; ring
  have hPE : ∀ x, P x * E x = 1 := fun x => by
    simp only [P, E]; rw [← Real.exp_add]; simp
  -- the real and imaginary parts
  have hEF : IntervalIntegrable (fun σ => ((E σ : ℝ) : ℂ) * F σ) volume t₀ t :=
    hF.continuousOn_mul (Complex.continuous_ofReal.comp hEc).continuousOn
  set J : ℝ → ℂ := fun x => ∫ σ in t₀..x, ((E σ : ℝ) : ℂ) * F σ
  have hre : IntervalIntegrable (fun σ => E σ * (F σ).re) volume t₀ t :=
    ⟨by simpa [Complex.mul_re] using hEF.1.re, by simpa [Complex.mul_re] using hEF.2.re⟩
  have him : IntervalIntegrable (fun σ => E σ * (F σ).im) volume t₀ t :=
    ⟨by simpa [Complex.mul_im] using hEF.1.im, by simpa [Complex.mul_im] using hEF.2.im⟩
  have hsub : ∀ x ∈ uIcc t₀ t, IntervalIntegrable (fun σ => ((E σ : ℝ) : ℂ) * F σ) volume t₀ x :=
    fun x hx => hEF.mono_set (uIcc_subset_uIcc_left hx |>.trans (by rfl))
  have Jre : ∀ x ∈ uIcc t₀ t, (J x).re = ∫ σ in t₀..x, E σ * (F σ).re := by
    intro x hx
    have := intervalIntegral.intervalIntegral_re (hsub x hx)
    simp only [RCLike.re_to_complex] at this
    rw [← this]; simp [Complex.mul_re]
  have Jim : ∀ x ∈ uIcc t₀ t, (J x).im = ∫ σ in t₀..x, E σ * (F σ).im := by
    intro x hx
    have := intervalIntegral.intervalIntegral_im (hsub x hx)
    simp only [RCLike.im_to_complex] at this
    rw [← this]; simp [Complex.mul_im]
  -- the integrand
  set φ : ℝ → ℂ := fun τ => ((deriv P τ : ℝ) : ℂ) * J τ + ((P τ * E τ : ℝ) : ℂ) * F τ
  have hJc : ContinuousOn J (uIcc t₀ t) :=
    intervalIntegral.continuousOn_primitive_interval' hEF (by simp)
  have hdP : Continuous (deriv P) := by
    rw [funext hPd]
    exact ((continuous_const.mul ha).mul hPc.continuous)
  have hφi : IntervalIntegrable φ volume t₀ t := by
    refine IntervalIntegrable.add ?_ ?_
    · exact ((Complex.continuous_ofReal.comp hdP).continuousOn.mul hJc).intervalIntegrable
    · exact hF.continuousOn_mul
        (Complex.continuous_ofReal.comp (hPc.continuous.mul hEc)).continuousOn
  have hQ : ((P t : ℝ) : ℂ) * J t = ∫ τ in t₀..t, φ τ := by
    apply Complex.ext
    · have h1 := intervalIntegral.intervalIntegral_re hφi
      simp only [RCLike.re_to_complex] at h1
      rw [← h1, Complex.re_ofReal_mul, Jre t (by simp),
        ← integral_deriv_mul_primitive hPc hre]
      refine intervalIntegral.integral_congr fun τ hτ => ?_
      simp only [φ, Complex.add_re, Complex.re_ofReal_mul, Jre τ hτ]
      ring
    · have h1 := intervalIntegral.intervalIntegral_im hφi
      simp only [RCLike.im_to_complex] at h1
      rw [← h1, Complex.im_ofReal_mul, Jim t (by simp),
        ← integral_deriv_mul_primitive hPc him]
      refine intervalIntegral.integral_congr fun τ hτ => ?_
      simp only [φ, Complex.add_im, Complex.im_ofReal_mul, Jim τ hτ]
      ring
  have hW : ∀ x, modeW c a F t₀ h x = modeCoup c h * (((P x : ℝ) : ℂ) * J x) :=
    fun x => modeW_eq ha c F t₀ h x
  rw [hW t, hQ, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun τ _ => ?_
  simp only [φ, hW τ, hPd τ]
  have hpe := hPE τ
  push_cast
  have hpe' : ((P τ : ℝ) : ℂ) * ((E τ : ℝ) : ℂ) = 1 := by exact_mod_cast hpe
  linear_combination (modeCoup c h * F τ) * hpe'

/-- **The mode equation in integrated form**, between two times. -/
theorem modeW_sub {a : ℝ → ℝ} (ha : Continuous a) {F : ℝ → ℂ}
    (hF : ∀ x y, IntervalIntegrable F volume x y) (c t₀ : ℝ) (h : ℤ) (s t : ℝ) :
    modeW c a F t₀ h t - modeW c a F t₀ h s =
      ∫ τ in s..t, ((-(modeRate c h) * a τ : ℝ) : ℂ) * modeW c a F t₀ h τ + modeCoup c h * F τ := by
  have hW : Continuous (modeW c a F t₀ h) := by
    have hfun : modeW c a F t₀ h = fun x => modeCoup c h *
        (((Real.exp (-(modeRate c h) * primA a t₀ x) : ℝ) : ℂ) *
          ∫ σ in t₀..x, ((Real.exp (modeRate c h * primA a t₀ σ) : ℝ) : ℂ) * F σ) :=
      funext fun x => modeW_eq ha c F t₀ h x
    have hA : Continuous (primA a t₀) := continuous_iff_continuousAt.mpr fun x =>
      (hasDerivAt_primA ha t₀ x).continuousAt
    rw [hfun]
    refine continuous_const.mul ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul hA))).mul ?_)
    exact intervalIntegral.continuous_primitive (fun x y => (hF x y).continuousOn_mul
      (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
        (continuous_const.mul hA))).continuousOn) t₀
  have hI : ∀ x y, IntervalIntegrable (fun τ => ((-(modeRate c h) * a τ : ℝ) : ℂ) *
      modeW c a F t₀ h τ + modeCoup c h * F τ) volume x y := fun x y =>
    ((Complex.continuous_ofReal.comp (continuous_const.mul ha)).mul hW).intervalIntegrable x y
      |>.add ((hF x y).const_mul _)
  rw [modeW_sub_start ha c t₀ h (hF t₀ t), modeW_sub_start ha c t₀ h (hF t₀ s),
    intervalIntegral.integral_interval_sub_left (hI t₀ t) (hI t₀ s)]

/-! Bounds of the transverse modes: the kernel is at most one, and with `a ≥ a₀ > 0` the Duhamel
amplitude gains `‖W_h(t)‖ ≤ M / (2π|h| a₀)` (`h ≠ 0`), where `M` bounds the flux mode; its time
derivative is at most `(r_h ‖a‖ + 2π|h|/c)`-weighted. -/

theorem modeRate_nonneg {c : ℝ} (hc : 0 < c) (h : ℤ) : 0 ≤ modeRate c h := by
  unfold modeRate; positivity

/-! **Uniqueness for the scalar linear integral equation**:
`A(t) - A(t₀) = ∫_{(t₀,t]} (k A + f)` on `[t₀, t₁]`, with a continuous real rate `k` and both
integrands integrable, has at most one solution from a given start (`eq_of_linear_integral_eq`;
Grönwall). Also: the Duhamel amplitude is continuous (`continuous_modeW`). -/

/-- A function given on a window by the integrals of an integrable function is continuous there. -/
theorem continuousOn_of_integral_eq {A φ : ℝ → ℂ} {t₀ t₁ : ℝ}
    (hφ : IntegrableOn φ (Ioc t₀ t₁))
    (hA : ∀ t ∈ Icc t₀ t₁, A t - A t₀ = ∫ τ in Ioc t₀ t, φ τ) : ContinuousOn A (Icc t₀ t₁) := by
  rcases le_or_gt t₀ t₁ with h01 | h01
  · have hint : IntegrableOn φ (uIcc t₀ t₁) := by
      rw [uIcc_of_le h01, integrableOn_Icc_iff_integrableOn_Ioc]
      exact hφ
    have := (intervalIntegral.continuousOn_primitive_interval hint).add
      (continuousOn_const (c := A t₀))
    rw [uIcc_of_le h01] at this
    refine this.congr fun t ht => ?_
    simp only [Pi.add_apply]
    rw [intervalIntegral.integral_of_le ht.1, ← hA t ht]
    ring
  · rw [Icc_eq_empty (not_le.mpr h01)]
    exact continuousOn_empty _

/-- **Uniqueness for the scalar linear integral equation.** -/
theorem eq_of_linear_integral_eq {k : ℝ → ℝ} (hk : Continuous k) {f A B : ℝ → ℂ} {t₀ t₁ : ℝ}
    (hAi : IntegrableOn (fun τ => (k τ : ℂ) * A τ + f τ) (Ioc t₀ t₁))
    (hA : ∀ t ∈ Icc t₀ t₁, A t - A t₀ = ∫ τ in Ioc t₀ t, (k τ : ℂ) * A τ + f τ)
    (hBi : IntegrableOn (fun τ => (k τ : ℂ) * B τ + f τ) (Ioc t₀ t₁))
    (hB : ∀ t ∈ Icc t₀ t₁, B t - B t₀ = ∫ τ in Ioc t₀ t, (k τ : ℂ) * B τ + f τ)
    (h0 : A t₀ = B t₀) : ∀ t ∈ Icc t₀ t₁, A t = B t := by
  intro t ht
  have h01 : t₀ ≤ t₁ := ht.1.trans ht.2
  set D : ℝ → ℂ := fun τ => A τ - B τ with hDdef
  have hDi : IntegrableOn (fun τ => (k τ : ℂ) * D τ) (Ioc t₀ t₁) := by
    have : (fun τ => (k τ : ℂ) * D τ) =
        fun τ => ((k τ : ℂ) * A τ + f τ) - ((k τ : ℂ) * B τ + f τ) :=
      funext fun τ => by simp only [hDdef]; ring
    rw [this]
    exact hAi.sub hBi
  have hD : ∀ t ∈ Icc t₀ t₁, D t = ∫ τ in Ioc t₀ t, (k τ : ℂ) * D τ := by
    intro t ht
    have hsub : Ioc t₀ t ⊆ Ioc t₀ t₁ := Ioc_subset_Ioc_right ht.2
    have e : ∫ τ in Ioc t₀ t, (k τ : ℂ) * D τ =
        (∫ τ in Ioc t₀ t, (k τ : ℂ) * A τ + f τ) - ∫ τ in Ioc t₀ t, (k τ : ℂ) * B τ + f τ := by
      rw [← integral_sub (hAi.mono_set hsub) (hBi.mono_set hsub)]
      congr 1
      funext τ
      simp only [hDdef]
      ring
    rw [e, ← hA t ht, ← hB t ht, h0]
    simp only [hDdef]
    ring
  have hD0 : D t₀ = 0 := by simp only [hDdef, h0, sub_self]
  have hDc : ContinuousOn D (Icc t₀ t₁) :=
    continuousOn_of_integral_eq hDi fun t ht => by rw [hD0, sub_zero]; exact hD t ht
  set P : ℝ → ℝ := fun τ => (projIcc t₀ t₁ h01 τ : ℝ) with hP
  have hPc : Continuous P := continuous_subtype_val.comp continuous_projIcc
  have hPm : ∀ τ, P τ ∈ Icc t₀ t₁ := fun τ => (projIcc t₀ t₁ h01 τ).2
  have hPid : ∀ τ ∈ Icc t₀ t₁, P τ = τ := fun τ hτ => by
    simp only [hP, projIcc_of_mem h01 hτ]
  set φ : ℝ → ℂ := fun τ => (k τ : ℂ) * D (P τ) with hφ
  have hφc : Continuous φ :=
    (Complex.continuous_ofReal.comp hk).mul (hDc.comp_continuous hPc hPm)
  set E : ℝ → ℂ := fun t => ∫ τ in t₀..t, φ τ with hE
  have hE' : ∀ x, HasDerivAt E (φ x) x := fun x =>
    (hφc.integral_hasStrictDerivAt t₀ x).hasDerivAt
  have hED : ∀ t ∈ Icc t₀ t₁, E t = D t := by
    intro t ht
    rw [hD t ht, hE]
    simp only
    rw [intervalIntegral.integral_of_le ht.1]
    refine setIntegral_congr_fun measurableSet_Ioc fun τ hτ => ?_
    simp only [hφ, hPid τ ⟨hτ.1.le, hτ.2.trans ht.2⟩]
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn (hk.continuousOn (s := Icc t₀ t₁))
  have hE0 := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (K := K)
    (a := t₀) (b := t₁) (f := E) (f' := φ)
    (fun x _ => (hE' x).continuousAt.continuousWithinAt) (fun x _ => (hE' x).hasDerivWithinAt)
    (by simp [hE]) (fun x hx => by
      have hx' : x ∈ Icc t₀ t₁ := Ico_subset_Icc_self hx
      simp only [hφ, hPid x hx', ← hED x hx', norm_mul, Complex.norm_real]
      exact mul_le_mul_of_nonneg_right (hK x hx') (norm_nonneg _))
  have := hE0 t ht
  rw [hED t ht] at this
  exact sub_eq_zero.mp this

/-- The Duhamel amplitude is continuous. -/
theorem continuous_modeW {a : ℝ → ℝ} (ha : Continuous a) {F : ℝ → ℂ}
    (hF : ∀ x y, IntervalIntegrable F volume x y) (c t₀ : ℝ) (h : ℤ) :
    Continuous (modeW c a F t₀ h) := by
  have hfun : modeW c a F t₀ h = fun x => modeCoup c h *
      (((Real.exp (-(modeRate c h) * primA a t₀ x) : ℝ) : ℂ) *
        ∫ σ in t₀..x, ((Real.exp (modeRate c h * primA a t₀ σ) : ℝ) : ℂ) * F σ) :=
    funext fun x => modeW_eq ha c F t₀ h x
  have hA : Continuous (primA a t₀) := continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_primA ha t₀ x).continuousAt
  rw [hfun]
  refine continuous_const.mul ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
    (continuous_const.mul hA))).mul ?_)
  exact intervalIntegral.continuous_primitive (fun x y => (hF x y).continuousOn_mul
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul hA))).continuousOn) t₀

end AVRegularity.Providers.Transverse
end
end

section
@[expose] public section
open Homogenization MeasureTheory Complex
namespace AVRegularity.Providers.Transverse

/-! Transverse Fourier calculus: the coefficients `phaseCoeff q f h` of a function of
the transverse phase `η_q`, their bounds, derivative rule, summability and inversion for
`ℤ²`-periodic `C²` functions that are transverse; and the calculus of the modes `modeExp`. -/

/-- `f` depends only on the `q`-th coordinate. -/
def IsTransverse (q : Fin 2) (f : Vec 2 → ℝ) : Prop :=
  ∀ η, f η = f (η q • basisVec q)

/-- The mode `e^{2πi h η_q}`. -/
noncomputable def modeExp (q : Fin 2) (h : ℤ) (η : Vec 2) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (h : ℂ) * (η q : ℂ))

/-! ### Mode calculus -/

theorem modeExp_add (q : Fin 2) (h : ℤ) (η ξ : Vec 2) :
    modeExp q h (η + ξ) = modeExp q h η * modeExp q h ξ := by
  simp only [modeExp, Pi.add_apply, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem norm_modeExp (q : Fin 2) (h : ℤ) (η : Vec 2) : ‖modeExp q h η‖ = 1 := by
  rw [modeExp, Complex.norm_exp]
  simp

/-- The derivative of `modeExp q h` at `η`, as a continuous linear map. -/
noncomputable def modeExpDeriv (q : Fin 2) (h : ℤ) (η : Vec 2) : Vec 2 →L[ℝ] ℂ :=
  (modeExp q h η * (2 * Real.pi * Complex.I * (h : ℂ))) •
    (Complex.ofRealCLM.comp (ContinuousLinearMap.proj q))

theorem modeExpDeriv_apply (q : Fin 2) (h : ℤ) (η w : Vec 2) :
    modeExpDeriv q h η w = 2 * Real.pi * Complex.I * (h : ℂ) * (w q : ℂ) * modeExp q h η := by
  simp only [modeExpDeriv, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, Complex.ofRealCLM_apply, smul_eq_mul]
  ring

theorem hasFDerivAt_modeExp (q : Fin 2) (h : ℤ) (η : Vec 2) :
    HasFDerivAt (modeExp q h) (modeExpDeriv q h η) η := by
  have hl : HasFDerivAt (fun η : Vec 2 => 2 * Real.pi * Complex.I * (h : ℂ) * (η q : ℂ))
      ((2 * Real.pi * Complex.I * (h : ℂ)) •
        (Complex.ofRealCLM.comp (ContinuousLinearMap.proj q) : Vec 2 →L[ℝ] ℂ)) η := by
    have := ((Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ)
      q)).hasFDerivAt (x := η)).const_smul (2 * Real.pi * Complex.I * (h : ℂ))
    exact this
  have h2 : HasFDerivAt (modeExp q h) (Complex.exp (2 * Real.pi * Complex.I * (h : ℂ) * (η q : ℂ)) •
      ((2 * Real.pi * Complex.I * (h : ℂ)) •
        (Complex.ofRealCLM.comp (ContinuousLinearMap.proj q) : Vec 2 →L[ℝ] ℂ))) η := hl.cexp
  refine h2.congr_fderiv ?_
  simp only [modeExpDeriv, modeExp, smul_smul]

theorem modeExp_periodic (q : Fin 2) (h : ℤ) : AVenhance.IsZ2Periodic (modeExp q h) := by
  intro n x
  rw [modeExp_add]
  have : modeExp q h (AVenhance.latticeShift n) = 1 := by
    simp only [modeExp, AVenhance.latticeShift]
    have := Complex.exp_int_mul_two_pi_mul_I (h * n q)
    rw [← this]
    congr 1
    push_cast
    ring
  rw [this, mul_one]

theorem fderiv_modeExp_basisVec (q k : Fin 2) (h : ℤ) (η : Vec 2) :
    fderiv ℝ (modeExp q h) η (basisVec k) =
      (if k = q then 2 * Real.pi * Complex.I * (h : ℂ) else 0) * modeExp q h η := by
  rw [(hasFDerivAt_modeExp q h η).fderiv, modeExpDeriv_apply, basisVec_apply]
  by_cases hk : k = q
  · subst hk; simp
  · simp [hk, Ne.symm hk]

/-! ### Elementary bounds -/

theorem phaseCoeff_neg (q : Fin 2) (f : Vec 2 → ℝ) (_hf : Continuous f) (h : ℤ) :
    phaseCoeff q f (-h) = (starRingEnd ℂ) (phaseCoeff q f h) := by
  simp only [phaseCoeff]
  simp only [intervalIntegral.integral_of_le zero_le_one]
  rw [← integral_conj]
  congr 1
  funext s
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 1
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, map_intCast, map_ofNat,
    Complex.conj_ofReal, Int.cast_neg]
  ring_nf

/-! ### Derivative rule -/

private theorem isZ2Periodic_fderiv {f : Vec 2 → ℝ} (hp : AVenhance.IsZ2Periodic f) (k : Vec 2) :
    AVenhance.IsZ2Periodic (fun η => fderiv ℝ f η k) := by
  intro n x
  have h1 : (fun y => f (y + AVenhance.latticeShift n)) = f := funext fun y => hp n y
  have := fderiv_comp_add_right (𝕜 := ℝ) (f := f) (x := x) (AVenhance.latticeShift n)
  simp only
  rw [← this, h1]

private theorem latticeShift_single (q : Fin 2) :
    AVenhance.latticeShift (Pi.single q 1) = basisVec q := by
  funext i
  by_cases h : i = q
  · subst h; simp [AVenhance.latticeShift]
  · simp [AVenhance.latticeShift, h]

private theorem line_periodic {f : Vec 2 → ℝ} (hp : AVenhance.IsZ2Periodic f) (q : Fin 2)
    (s : ℝ) : f ((s + 1) • basisVec q) = f (s • basisVec q) := by
  have := hp (Pi.single q 1) (s • basisVec q)
  rw [latticeShift_single] at this
  rw [← this, add_smul, one_smul]

private theorem hasDerivAt_line {f : Vec 2 → ℝ} (hf : Differentiable ℝ f) (q : Fin 2) (s : ℝ) :
    HasDerivAt (fun s : ℝ => f (s • basisVec q)) (fderiv ℝ f (s • basisVec q) (basisVec q)) s := by
  have h1 : HasDerivAt (fun s : ℝ => s • basisVec q) (basisVec q) s := by
    simpa using (hasDerivAt_id s).smul_const (basisVec q)
  exact (hf (s • basisVec q)).hasFDerivAt.comp_hasDerivAt s h1

private theorem continuous_line {f : Vec 2 → ℝ} (hf : Continuous f) (q : Fin 2) :
    Continuous fun s : ℝ => f (s • basisVec q) :=
  hf.comp (continuous_id.smul continuous_const)

theorem phaseCoeff_deriv {q : Fin 2} {f : Vec 2 → ℝ} (hf : ContDiff ℝ 1 f)
    (hp : AVenhance.IsZ2Periodic f) (h : ℤ) :
    phaseCoeff q (fun η => fderiv ℝ f η (basisVec q)) h =
      2 * Real.pi * Complex.I * h * phaseCoeff q f h := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hc' : Continuous fun η => fderiv ℝ f η (basisVec q) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  set c : ℂ := 2 * Real.pi * Complex.I * (h : ℂ) with hc
  have hv : ∀ s : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (-(c * (s : ℂ))))
      (-c * Complex.exp (-(c * (s : ℂ)))) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => -(c * (s : ℂ))) (-c) s := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := s)).const_mul c).fun_neg
    simpa [mul_comm] using h1.cexp
  have hu : ∀ s : ℝ, HasDerivAt (fun s : ℝ => ((f (s • basisVec q) : ℝ) : ℂ))
      (((fderiv ℝ f (s • basisVec q) (basisVec q) : ℝ) : ℂ)) s := fun s =>
    (hasDerivAt_line hd q s).ofReal_comp
  have hcu : Continuous fun s : ℝ => ((fderiv ℝ f (s • basisVec q) (basisVec q) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_line hc' q)
  have hcv : Continuous fun s : ℝ => -c * Complex.exp (-(c * (s : ℂ))) := by fun_prop
  have hcf : Continuous fun s : ℝ => ((f (s • basisVec q) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_line hf.continuous q)
  have key := intervalIntegral.integral_deriv_mul_eq_sub (a := (0 : ℝ)) (b := 1)
    (u := fun s : ℝ => ((f (s • basisVec q) : ℝ) : ℂ))
    (v := fun s : ℝ => Complex.exp (-(c * (s : ℂ))))
    (u' := fun s : ℝ => ((fderiv ℝ f (s • basisVec q) (basisVec q) : ℝ) : ℂ))
    (v' := fun s : ℝ => -c * Complex.exp (-(c * (s : ℂ))))
    (fun s _ => hu s) (fun s _ => hv s) (hcu.intervalIntegrable _ _) (hcv.intervalIntegrable _ _)
  have e1 : Complex.exp (-(c * ((1 : ℝ) : ℂ))) = 1 := by
    have := Complex.exp_int_mul_two_pi_mul_I (-h)
    rw [← this]
    congr 1
    simp only [hc]; push_cast; ring
  have e0 : Complex.exp (-(c * ((0 : ℝ) : ℂ))) = 1 := by simp
  have hper : f ((1 : ℝ) • basisVec q) = f ((0 : ℝ) • basisVec q) := by
    simpa using line_periodic hp q 0
  simp only [e1, e0, mul_one, hper, sub_self] at key
  have i1 : IntervalIntegrable (fun s : ℝ => ((fderiv ℝ f (s • basisVec q) (basisVec q) : ℝ) : ℂ) *
      Complex.exp (-(c * (s : ℂ)))) volume 0 1 :=
    (hcu.mul (by fun_prop : Continuous fun s : ℝ => Complex.exp (-(c * (s : ℂ))))).intervalIntegrable
      _ _
  have i2 : IntervalIntegrable (fun s : ℝ => ((f (s • basisVec q) : ℝ) : ℂ) *
      (-c * Complex.exp (-(c * (s : ℂ))))) volume 0 1 := (hcf.mul hcv).intervalIntegrable _ _
  rw [intervalIntegral.integral_add i1 i2] at key
  have e2 : ∫ s in (0 : ℝ)..1, ((f (s • basisVec q) : ℝ) : ℂ) *
      (-c * Complex.exp (-(c * (s : ℂ)))) = -(c * phaseCoeff q f h) := by
    rw [phaseCoeff, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [hc]; ring
  rw [e2] at key
  have : phaseCoeff q (fun η => fderiv ℝ f η (basisVec q)) h =
      ∫ s in (0 : ℝ)..1, ((fderiv ℝ f (s • basisVec q) (basisVec q) : ℝ) : ℂ) *
        Complex.exp (-(c * (s : ℂ))) := rfl
  rw [this]
  linear_combination key

/-! ### Second-derivative decay and summability -/

private theorem contDiff_fderiv_apply {f : Vec 2 → ℝ} (hf : ContDiff ℝ 2 f) (q : Fin 2) :
    ContDiff ℝ 1 (fun η => fderiv ℝ f η (basisVec q)) :=
  (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

theorem exists_bound_of_periodic {g : Vec 2 → ℝ} (hc : Continuous g)
    (hp : AVenhance.IsZ2Periodic g) : ∃ M, ∀ η, |g η| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_univ_pi (fun _ : Fin 2 => isCompact_Icc (a := (0 : ℝ)) (b := 1))
    ).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨M, fun η => ?_⟩
  have hη : η = (fun i => Int.fract (η i)) + AVenhance.latticeShift (fun i => ⌊η i⌋) := by
    funext i
    simp [AVenhance.latticeShift]
  rw [hη, hp]
  have := hM (fun i => Int.fract (η i)) (fun i _ => ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩)
  simpa using this

/-! ### Fourier inversion -/

end AVRegularity.Providers.Transverse
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Providers.Transverse

/-! Iterated derivatives of the transverse modes: `e_h = (s ↦ exp(2πih s)) ∘ π_q` is smooth with
`‖D^k e_h‖ ≤ (2π|h|)^k`. -/

theorem iteratedDeriv_cexp_real (l : ℂ) (k : ℕ) :
    iteratedDeriv k (fun s : ℝ => Complex.exp (l * s)) = fun s : ℝ => l ^ k * Complex.exp (l * s) := by
  induction k with
  | zero => funext s; simp
  | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      funext s
      have h1 : HasDerivAt (fun s : ℝ => l * (s : ℂ)) l s := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).const_mul l
      have h2 := (h1.cexp).const_mul (l ^ k)
      rw [h2.deriv]
      ring

/-- The mode as a composition with the coordinate projection. -/
theorem modeExp_eq_comp (q : Fin 2) (h : ℤ) :
    modeExp q h = (fun s : ℝ => Complex.exp ((2 * Real.pi * Complex.I * (h : ℂ)) * s)) ∘
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) q) := by
  funext η; simp [modeExp]

theorem contDiff_modeExp (q : Fin 2) (h : ℤ) {n : WithTop ℕ∞} : ContDiff ℝ n (modeExp q h) := by
  rw [modeExp_eq_comp]
  refine ContDiff.comp ?_ (ContinuousLinearMap.contDiff _)
  exact (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

theorem norm_iteratedFDeriv_modeExp_le (q : Fin 2) (h : ℤ) (k : ℕ) (η : Vec 2) :
    ‖iteratedFDeriv ℝ k (modeExp q h) η‖ ≤ (2 * Real.pi * |(h : ℝ)|) ^ k := by
  set l : ℂ := 2 * Real.pi * Complex.I * (h : ℂ)
  set P := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) q
  have hf : ContDiff ℝ ⊤ (fun s : ℝ => Complex.exp (l * s)) :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  rw [modeExp_eq_comp, P.iteratedFDeriv_comp_right hf η (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hP : ‖P‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    simpa [P] using norm_le_pi_norm x q
  have hl : ‖l‖ = 2 * Real.pi * |(h : ℝ)| := by
    simp only [l, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_intCast,
      Complex.norm_ofNat, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one]
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_cexp_real, norm_mul, norm_pow, hl]
  have he : ‖Complex.exp (l * (P η : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp [l]
  rw [he, mul_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h0 : 0 ≤ 2 * Real.pi * |(h : ℝ)| := by positivity
  calc (2 * Real.pi * |(h : ℝ)|) ^ k * ‖P‖ ^ k ≤ (2 * Real.pi * |(h : ℝ)|) ^ k * 1 ^ k := by
        gcongr
    _ = _ := by simp

end AVRegularity.Providers.Transverse
end
end

section
/-! Transverse series `S_A(η) = ∑_h A_h e_h(η)`: smoothness from the decay of the amplitudes,
termwise first derivatives, time derivatives of time-dependent amplitudes and joint continuity. -/

@[expose] public noncomputable section

open Homogenization

namespace AVRegularity.Providers.Transverse

/-- The transverse series with amplitudes `A`. -/
def tser (q : Fin 2) (A : ℤ → ℂ) (η : Vec 2) : ℂ := ∑' h : ℤ, A h * modeExp q h η

/-- The weight `2π(1+|h|)`. -/
def wt (h : ℤ) : ℝ := 2 * Real.pi * (1 + |(h : ℝ)|)

theorem one_le_wt (h : ℤ) : 1 ≤ wt h := by
  unfold wt
  have : (1 : ℝ) ≤ 1 + |(h : ℝ)| := by linarith [abs_nonneg (h : ℝ)]
  nlinarith [Real.pi_gt_three]

theorem mode_le_wt (h : ℤ) : 2 * Real.pi * |(h : ℝ)| ≤ wt h := by
  unfold wt; nlinarith [Real.pi_pos]

theorem norm_iteratedFDeriv_term_le (q : Fin 2) (a : ℂ) (h : ℤ) (k : ℕ) (η : Vec 2) :
    ‖iteratedFDeriv ℝ k (fun η => a * modeExp q h η) η‖ ≤ ‖a‖ * (2 * Real.pi * |(h : ℝ)|) ^ k := by
  have e : (fun η => a * modeExp q h η) = (ContinuousLinearMap.mul ℝ ℂ a) ∘ modeExp q h := by
    funext η; simp
  rw [e, (ContinuousLinearMap.mul ℝ ℂ a).iteratedFDeriv_comp_left
    (contDiff_modeExp q h).contDiffAt (by exact_mod_cast le_top)]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  refine mul_le_mul ?_ (norm_iteratedFDeriv_modeExp_le q h k η) (norm_nonneg _) (norm_nonneg _)
  exact (ContinuousLinearMap.opNorm_mul_apply_le ℝ ℂ a).trans (le_refl _)

/-- **Smoothness of a transverse series.** -/
theorem contDiff_tser (q : Fin 2) {A : ℤ → ℂ} (N : ℕ)
    (hA : Summable fun h => ‖A h‖ * wt h ^ N) : ContDiff ℝ N (tser q A) := by
  unfold tser
  refine contDiff_tsum (v := fun _ h => ‖A h‖ * wt h ^ N)
    (fun h => contDiff_const.mul (contDiff_modeExp q h)) (fun _ _ => hA) ?_
  intro k h η hk
  refine (norm_iteratedFDeriv_term_le q (A h) h k η).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc (2 * Real.pi * |(h : ℝ)|) ^ k ≤ wt h ^ k :=
        pow_le_pow_left₀ (by positivity) (mode_le_wt h) k
    _ ≤ wt h ^ N := pow_le_pow_right₀ (one_le_wt h) (by exact_mod_cast hk)

theorem summable_of_wt {A : ℤ → ℂ} {N : ℕ} (hA : Summable fun h => ‖A h‖ * wt h ^ N) (k : ℕ)
    (hk : k ≤ N) : Summable fun h => ‖A h‖ * wt h ^ k :=
  hA.of_nonneg_of_le (fun h => by have := one_le_wt h; positivity)
    fun h => mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one_le_wt h) hk) (norm_nonneg _)

theorem norm_modeExpDeriv_le (q : Fin 2) (h : ℤ) (η : Vec 2) :
    ‖modeExpDeriv q h η‖ ≤ 2 * Real.pi * |(h : ℝ)| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  rw [modeExpDeriv_apply]
  simp only [norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_intCast,
    Complex.norm_ofNat, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one, norm_modeExp]
  have hw : |w q| ≤ ‖w‖ := by simpa using norm_le_pi_norm w q
  have : 0 ≤ 2 * Real.pi * |(h : ℝ)| := by positivity
  nlinarith

/-- **The first derivatives of a transverse series.** -/
theorem fderiv_tser (q : Fin 2) {A : ℤ → ℂ} (hA : Summable fun h => ‖A h‖ * wt h ^ 1)
    (η : Vec 2) (k : Fin 2) :
    fderiv ℝ (tser q A) η (basisVec k) =
      tser q (fun h => (if k = q then 2 * Real.pi * Complex.I * (h : ℂ) else 0) * A h) η := by
  have hu : Summable fun h => ‖A h‖ * (2 * Real.pi * |(h : ℝ)|) :=
    hA.of_nonneg_of_le (fun h => by positivity)
      fun h => mul_le_mul_of_nonneg_left (by simpa using mode_le_wt h) (norm_nonneg _)
  have h0 : Summable fun h => A h * modeExp q h 0 := by
    refine Summable.of_norm_bounded (summable_of_wt hA 0 (by omega)) fun h => ?_
    simp [norm_modeExp]
  have hb : ∀ (h : ℤ) (x : Vec 2), ‖A h • modeExpDeriv q h x‖ ≤ ‖A h‖ * (2 * Real.pi * |(h : ℝ)|) :=
    fun h x => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (norm_modeExpDeriv_le q h x) (norm_nonneg _)
  have hf : ∀ (h : ℤ) (x : Vec 2), HasFDerivAt (fun η => A h * modeExp q h η)
      (A h • modeExpDeriv q h x) x := fun h x => (hasFDerivAt_modeExp q h x).const_mul (A h)
  have hD := hasFDerivAt_tsum hu hf hb h0 η
  unfold tser
  rw [hD.fderiv]
  have hs : Summable fun h => A h • modeExpDeriv q h η :=
    Summable.of_norm_bounded hu fun h => hb h η
  rw [tsum_apply hs]
  refine tsum_congr fun h => ?_
  rw [smul_apply, modeExpDeriv_apply, smul_eq_mul]
  by_cases hk : k = q
  · subst hk; simp [basisVec]; ring
  · simp [basisVec, hk, Ne.symm hk]

end AVRegularity.Providers.Transverse

namespace AVRegularity.Providers.Transverse

theorem differentiable_tser (q : Fin 2) {A : ℤ → ℂ} (hA : Summable fun h => ‖A h‖ * wt h ^ 1) :
    Differentiable ℝ (tser q A) :=
  (contDiff_tser q 1 hA).differentiable (by norm_num)

/-- First derivatives of the real part of a transverse series. -/
theorem fderiv_re_tser (q : Fin 2) {A : ℤ → ℂ} (hA : Summable fun h => ‖A h‖ * wt h ^ 1)
    (η : Vec 2) (k : Fin 2) :
    fderiv ℝ (fun y => (tser q A y).re) η (basisVec k) =
      (tser q (fun h => (if k = q then 2 * Real.pi * Complex.I * (h : ℂ) else 0) * A h) η).re := by
  have hd := (differentiable_tser q hA η).hasFDerivAt
  have hre := (Complex.reCLM.hasFDerivAt (x := tser q A η)).comp η hd
  rw [show (fun y => (tser q A y).re) = Complex.reCLM ∘ tser q A from rfl, hre.fderiv]
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, Complex.reCLM_apply]
  rw [fderiv_tser q hA η k]

end AVRegularity.Providers.Transverse
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.Providers.Transverse

/-! The cell mean of a transverse series is its zero mode. -/

theorem volume_restrict_unitCube :
    (volume : Measure (Vec 2)).restrict AVenhance.unitCube =
      Measure.pi fun _ : Fin 2 => (volume : Measure ℝ).restrict (Set.Ioo 0 1) := by
  rw [AVenhance.unitCube, volume_pi, Measure.restrict_pi_pi]

theorem integral_unitCube_modeExp (q : Fin 2) (h : ℤ) :
    ∫ x in AVenhance.unitCube, modeExp q h x = if h = 0 then 1 else 0 := by
  have e : ∀ x : Vec 2, modeExp q h x =
      ∏ i : Fin 2, (if i = q then Complex.exp ((2 * Real.pi * Complex.I * (h : ℂ)) * (x i : ℂ))
        else 1) := by
    intro x
    rw [Finset.prod_ite_eq' Finset.univ q]
    simp [modeExp]
  simp_rw [e]
  rw [volume_restrict_unitCube, integral_fintype_prod_eq_prod
    (f := fun i (s : ℝ) => if i = q then Complex.exp ((2 * Real.pi * Complex.I * (h : ℂ)) * (s : ℂ))
      else 1)]
  rw [Finset.prod_eq_single q (fun i _ hi => by simp [hi]) (by simp)]
  simp only [ite_true]
  rw [← intervalIntegral.integral_of_le zero_le_one |>.trans (integral_Ioc_eq_integral_Ioo)]
  by_cases hh : h = 0
  · subst hh; simp
  · have hc : (2 * Real.pi * Complex.I * (h : ℂ)) ≠ 0 := by
      simp [Real.pi_ne_zero, hh, Complex.I_ne_zero]
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp (2 * Real.pi * Complex.I * (h : ℂ) * ((1 : ℝ) : ℂ)) = 1 :=
      Complex.exp_eq_one_iff.mpr ⟨h, by push_cast; ring⟩
    rw [h1]
    simp [hh]

end AVRegularity.Providers.Transverse
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
namespace AVRegularity.Providers.Transverse

/-! The amplitudes of the transverse cell inverse in cell time `τ`, from zero at `τ₀`: the Duhamel
amplitude of the mode `h` at the physical time `c · max(τ, τ₀)`. They are continuous, uniformly
bounded by `M_h/(2πa₀)`, and for `τ > τ₀` they solve
`∂_τ A_h = -4π²h² a(cτ) A_h + 2πih F_h(cτ)`. -/

/-- The data of a transverse inverse. -/
structure TData where
  /-- The cell time scale. -/
  c : ℝ
  /-- The transverse metric entry (physical time). -/
  a : ℝ → ℝ
  /-- Its lower bound. -/
  a₀ : ℝ
  /-- Its upper bound. -/
  a₁ : ℝ
  /-- The transverse flux modes (physical time). -/
  Fm : ℤ → ℝ → ℂ
  /-- The bounds of the flux modes. -/
  M : ℤ → ℝ
  /-- The start (cell time). -/
  τ₀ : ℝ

/-- The hypotheses on the data, with flux mode decay of order `N` (`N ≥ 1`). -/
structure TData.Good (T : TData) (N : ℕ) : Prop where
  hc : 0 < T.c
  ha : Continuous T.a
  ha₀ : 0 < T.a₀
  hlo : ∀ u, T.a₀ ≤ T.a u
  hhi : ∀ u, T.a u ≤ T.a₁
  hF : ∀ h, Continuous (T.Fm h)
  hM : ∀ h s, ‖T.Fm h s‖ ≤ T.M h
  hMs : Summable fun h => T.M h * wt h ^ N
  hN : 1 ≤ N

namespace TData

variable (T : TData)

/-- The amplitude of the mode `h` at the cell time `τ`. -/
def amp (h : ℤ) (τ : ℝ) : ℂ := modeW T.c T.a (T.Fm h) (T.c * T.τ₀) h (T.c * max τ T.τ₀)

theorem amp_zero (τ : ℝ) : T.amp 0 τ = 0 := by
  simp [amp, modeW, modeCoup]

variable {T} {N : ℕ}

theorem Good.M_nonneg (hT : T.Good N) (h : ℤ) : 0 ≤ T.M h :=
  le_trans (norm_nonneg _) (hT.hM h 0)

end TData

end AVRegularity.Providers.Transverse
end
end
end

section
section
@[expose] public noncomputable section
open MeasureTheory Set
namespace AVRegularity.Providers.Transverse

/-! The amplitudes of the transverse inverse for measurable, bounded flux modes (Carathéodory):
continuity, the uniform bounds, and the integrated amplitude equation
`A_h(τ) - A_h(σ) = ∫_σ^τ ∂A_h` for `τ₀ ≤ σ ≤ τ`. -/

namespace TData

/-- The hypotheses on the data with measurable flux modes. -/
structure GoodM (T : TData) (N : ℕ) : Prop where
  hc : 0 < T.c
  ha : Continuous T.a
  ha₀ : 0 < T.a₀
  hlo : ∀ u, T.a₀ ≤ T.a u
  hhi : ∀ u, T.a u ≤ T.a₁
  hF : ∀ h, Measurable (T.Fm h)
  hM : ∀ h s, ‖T.Fm h s‖ ≤ T.M h
  hMs : Summable fun h => T.M h * wt h ^ N
  hN : 1 ≤ N

variable {T : TData} {N : ℕ}

theorem GoodM.intervalIntegrable_Fm (hT : T.GoodM N) (h : ℤ) (x y : ℝ) :
    IntervalIntegrable (T.Fm h) volume x y := by
  refine (intervalIntegrable_const (c := T.M h)).mono_fun ?_ ?_
  · exact (hT.hF h).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun s => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (le_trans (norm_nonneg _) (hT.hM h s))]
        using hT.hM h s

theorem GoodM.M_nonneg (hT : T.GoodM N) (h : ℤ) : 0 ≤ T.M h :=
  le_trans (norm_nonneg _) (hT.hM h 0)

theorem GoodM.continuous_modeW (hT : T.GoodM N) (h : ℤ) :
    Continuous (modeW T.c T.a (T.Fm h) (T.c * T.τ₀) h) := by
  have hfun : modeW T.c T.a (T.Fm h) (T.c * T.τ₀) h = fun x => modeCoup T.c h *
      (((Real.exp (-(modeRate T.c h) * primA T.a (T.c * T.τ₀) x) : ℝ) : ℂ) *
        ∫ σ in (T.c * T.τ₀)..x,
          ((Real.exp (modeRate T.c h * primA T.a (T.c * T.τ₀) σ) : ℝ) : ℂ) * T.Fm h σ) :=
    funext fun x => modeW_eq hT.ha T.c (T.Fm h) _ h x
  have hA : Continuous (primA T.a (T.c * T.τ₀)) := continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_primA hT.ha _ x).continuousAt
  rw [hfun]
  refine continuous_const.mul ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp
    (continuous_const.mul hA))).mul ?_)
  exact intervalIntegral.continuous_primitive (fun x y => (hT.intervalIntegrable_Fm h x y)
    |>.continuousOn_mul (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul hA))).continuousOn) _

end TData

end AVRegularity.Providers.Transverse
end
end

section
/-! **The transverse modes of a transverse cell inverse** (the route without
time-uniform bounds). For a finite-past cell field inverse `c` (scalar) of a source `g`, both
transverse in the phase `q`, with a drift without `q`-component, the transverse Fourier modes
`A_h(t) = phaseCoeff q (c t) h` vanish at the start and satisfy, on the window,
`A_h(t) - A_h(s) = ∫_{(s,t]} (-4π²h² G_qq(τ) A_h(τ) + ĝ_h(τ)) dτ`
(`phaseCoeff_cellFieldInverse_sub`). This is the weak cell identity tested against the transverse
mode `e^{-2πi h z_q}` (`transverseModeTest`).

Auxiliary facts: cell integrals of transverse functions against modes are their transverse
Fourier coefficients (`integral_unitCube_mul_modeExp_neg`); transverse functions have no derivative
along the parallel coordinate (`IsTransverse.fderiv_other`) and their `q`-derivatives are
transverse (`IsTransverse.fderiv_q`). -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity AVRegularity.Sobolev
  AVRegularity.Uniqueness.Translate

namespace AVRegularity.Providers.Transverse

/-! ### Transverse functions -/

theorem IsTransverse.line_other {q p : Fin 2} (hpq : p ≠ q) {f : Vec 2 → ℝ}
    (ht : IsTransverse q f) (x : Vec 2) (s : ℝ) : f (x + s • basisVec p) = f x := by
  rw [ht (x + s • basisVec p), ht x]
  congr 2
  simp [basisVec_apply, Ne.symm hpq]

theorem IsTransverse.fderiv_other {q p : Fin 2} (hpq : p ≠ q) {f : Vec 2 → ℝ}
    (ht : IsTransverse q f) (x : Vec 2) : fderiv ℝ f x (basisVec p) = 0 := by
  by_cases hd : DifferentiableAt ℝ f x
  · have hline : HasDerivAt (fun s : ℝ => f (x + s • basisVec p)) (fderiv ℝ f x (basisVec p)) 0 := by
      have hl : HasDerivAt (fun s : ℝ => x + s • basisVec p) (basisVec p) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (basisVec p)).const_add x
      have := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
      simpa [Function.comp_def] using this
    have hconst : (fun s : ℝ => f (x + s • basisVec p)) = fun _ => f x :=
      funext fun s => ht.line_other hpq x s
    rw [hconst] at hline
    exact (hline.unique (hasDerivAt_const 0 (f x))).trans rfl
  · rw [fderiv_zero_of_not_differentiableAt hd]
    rfl

theorem IsTransverse.fderiv_q {q : Fin 2} {f : Vec 2 → ℝ} (hf : Differentiable ℝ f)
    (ht : IsTransverse q f) : IsTransverse q (fun x => fderiv ℝ f x (basisVec q)) := by
  intro x
  have hline : ∀ y : Vec 2, HasDerivAt (fun s : ℝ => f (y + s • basisVec q))
      (fderiv ℝ f y (basisVec q)) 0 := fun y => by
    have hl : HasDerivAt (fun s : ℝ => y + s • basisVec q) (basisVec q) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (basisVec q)).const_add y
    have := (hf y).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
    simpa [Function.comp_def] using this
  have heq : (fun s : ℝ => f (x + s • basisVec q)) =
      fun s : ℝ => f (x q • basisVec q + s • basisVec q) := by
    funext s
    rw [ht (x + s • basisVec q), ht (x q • basisVec q + s • basisVec q)]
    congr 2
    simp [basisVec_apply]
  have h1 := hline x
  rw [heq] at h1
  exact h1.unique (hline (x q • basisVec q))

/-! ### Cell integrals against modes -/

/-- **The cell integral of a transverse function against the mode `e^{-2πi h z_q}`** is its
transverse Fourier coefficient. -/
theorem integral_unitCube_mul_modeExp_neg {q : Fin 2} {f : Vec 2 → ℝ} (ht : IsTransverse q f)
    (h : ℤ) : ∫ x in AVenhance.unitCube, ((f x : ℝ) : ℂ) * modeExp q (-h) x = phaseCoeff q f h := by
  set F : ℝ → ℂ := fun s => ((f (s • basisVec q) : ℝ) : ℂ) *
    Complex.exp (-(2 * Real.pi * Complex.I * (h : ℂ) * (s : ℂ))) with hF
  have e : ∀ x : Vec 2, ((f x : ℝ) : ℂ) * modeExp q (-h) x =
      ∏ i : Fin 2, (if i = q then F (x i) else 1) := by
    intro x
    rw [Finset.prod_ite_eq' Finset.univ q]
    simp only [Finset.mem_univ, ite_true, hF, modeExp]
    rw [ht x]
    congr 2
    push_cast
    ring
  simp_rw [e]
  rw [volume_restrict_unitCube, integral_fintype_prod_eq_prod
    (f := fun i (s : ℝ) => if i = q then F s else 1)]
  rw [Finset.prod_eq_single q (fun i _ hi => by simp [hi]) (by simp)]
  simp only [ite_true]
  rw [← intervalIntegral.integral_of_le zero_le_one |>.trans (integral_Ioc_eq_integral_Ioo)]
  rfl

/-! ### The transverse mode as a test function -/

/-- The transverse mode `e^{-2πi h z_q}` as a periodic `H¹` test function. -/
def transverseModeTest (q : Fin 2) (h : ℤ) : TorusHkFunction 1 ℂ :=
  TorusHkFunction.mk (CycleComparison.Lift.classicalCellJet (modeExp q (-h)))
    (CycleComparison.Lift.classicalCellJet_periodicWeak _ (contDiff_modeExp q (-h))
      (modeExp_periodic q (-h)))

theorem transverseModeTest_value (q : Fin 2) (h : ℤ) (x : Vec 2) :
    (transverseModeTest q h).jet (valueIndex2 1) x = modeExp q (-h) x := by
  simp [transverseModeTest, CycleComparison.Lift.classicalCellJet, valueIndex2, valueIndex]

theorem transverseModeTest_grad (q : Fin 2) (h : ℤ) (k : Fin 2) (x : Vec 2) :
    (transverseModeTest q h).jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x =
      (if k = q then 2 * Real.pi * Complex.I * ((-h : ℤ) : ℂ) else 0) * modeExp q (-h) x := by
  simp only [transverseModeTest, CycleComparison.Lift.classicalCellJet, zero_lt_one, dite_true]
  exact fderiv_modeExp_basisVec q k (-h) x

/-! ### The mode equation -/

theorem integrableOn_unitCube_of_continuous' {f : Vec 2 → ℂ} (hf : Continuous f) :
    IntegrableOn f AVenhance.unitCube :=
  (hf.continuousOn.integrableOn_compact (isCompact_univ_pi fun _ => isCompact_Icc)).mono_set
    (Set.pi_mono fun _ _ => Set.Ioo_subset_Icc_self :
      AVenhance.unitCube ⊆ Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1)

/-- The values of a scalar cell inverse are periodic on the window. -/
theorem periodic_of_cellFieldInverse {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {sZ : ℕ} {t₀ t₁ : ℝ} {g c : ℝ → Vec 2 → ℝ}
    (hC : IsCellFieldInverse G v sZ t₀ t₁ (fun _ => 0) g c) {τ : ℝ} (hτ : τ ∈ Icc t₀ t₁) :
    AVenhance.IsZ2Periodic (c τ) := by
  intro n x
  have := ((hC.2 (ContinuousLinearMap.id ℝ ℝ)).1.2.2.1 τ hτ).2 n x
  simpa [cellValue, cellJetOfField, valueIndex2, valueIndex] using this

/-- The weak cell integrand against the transverse mode, for a transverse trajectory and a drift
without transverse component. -/
theorem weakRhs_mode {q : Fin 2} (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (g c : ℝ → Vec 2 → ℝ) (h : ℤ) {τ : ℝ} (hct : IsTransverse q (c τ))
    (hvq : ∀ x, v τ x q = 0) (x : Vec 2) :
    weakRhs ⟨fun t _ => G t, v, 0, 0⟩ (modeExp q (-h))
        (fun k x => (if k = q then 2 * Real.pi * Complex.I * ((-h : ℤ) : ℂ) else 0) *
          modeExp q (-h) x)
        (fun τ x => ((c τ x : ℝ) : ℂ)) (fun τ k x => ((fderiv ℝ (c τ) x (basisVec k) : ℝ) : ℂ))
        (fun τ x => ((g τ x : ℝ) : ℂ)) (fun _ _ => 0) τ x =
      -((G τ q q : ℂ) * (2 * Real.pi * Complex.I * ((-h : ℤ) : ℂ))) *
          (((fderiv ℝ (c τ) x (basisVec q) : ℝ) : ℂ) * modeExp q (-h) x) +
        ((g τ x : ℝ) : ℂ) * modeExp q (-h) x := by
  fin_cases q
  · have h1 := hct.fderiv_other (p := 1) (by decide) x
    have h2 := hvq x
    simp only [Fin.zero_eta, Fin.isValue] at h1 h2
    simp [weakRhs, Fin.sum_univ_two, h1, h2]
    ring
  · have h1 := hct.fderiv_other (p := 0) (by decide) x
    have h2 := hvq x
    simp only [Fin.mk_one, Fin.isValue] at h1 h2
    simp [weakRhs, Fin.sum_univ_two, h1, h2]
    ring

/-- **The transverse modes of a transverse cell inverse** solve the mode equation in integrated
form between two times of the window. -/
theorem phaseCoeff_cellFieldInverse_sub {q : Fin 2} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {v : ℝ → Vec 2 → Vec 2} {sZ : ℕ} (hsZ : 1 ≤ sZ) {t₀ t₁ : ℝ} {g c : ℝ → Vec 2 → ℝ}
    (hC : IsCellFieldInverse G v sZ t₀ t₁ (fun _ => 0) g c)
    (hct : ∀ τ ∈ Icc t₀ t₁, IsTransverse q (c τ))
    (hgt : ∀ τ ∈ Icc t₀ t₁, IsTransverse q (g τ))
    (hgc : ∀ τ ∈ Icc t₀ t₁, Continuous (g τ))
    (hvq : ∀ τ ∈ Icc t₀ t₁, ∀ x, v τ x q = 0) (h : ℤ) {s t : ℝ} (hs : t₀ ≤ s) (hst : s ≤ t)
    (ht : t ≤ t₁) :
    IntegrableOn (fun τ => ((-(4 * Real.pi ^ 2 * (h : ℝ) ^ 2) * G τ q q : ℝ) : ℂ) *
        phaseCoeff q (c τ) h + phaseCoeff q (g τ) h) (Ioc s t) ∧
      phaseCoeff q (c t) h - phaseCoeff q (c s) h =
        ∫ τ in Ioc s t, ((-(4 * Real.pi ^ 2 * (h : ℝ) ^ 2) * G τ q q : ℝ) : ℂ) *
          phaseCoeff q (c τ) h + phaseCoeff q (g τ) h := by
  obtain ⟨hreg, hsol⟩ := hC
  obtain ⟨hS, -, -, -⟩ := hsol (ContinuousLinearMap.id ℝ ℝ)
  have hW := hS.2.2.2.2.2.2 s ⟨hs, hst.trans ht⟩ t ⟨hs.trans hst, ht⟩ hst (transverseModeTest q h)
  have eu : cellValue (cellJetOfField (ContinuousLinearMap.id ℝ ℝ) c) =
      fun τ x => ((c τ x : ℝ) : ℂ) := by
    funext τ x
    simp [cellValue, cellJetOfField, valueIndex2, valueIndex]
  have edu : (fun τ k => cellGradComp (cellJetOfField (ContinuousLinearMap.id ℝ ℝ) c τ) k) =
      fun τ k x => ((fderiv ℝ (c τ) x (basisVec k) : ℝ) : ℂ) := by
    funext τ k x
    simp [cellGradComp, cellJetOfField]
  have eψ : (transverseModeTest q h).jet (valueIndex2 1) = modeExp q (-h) :=
    funext (transverseModeTest_value q h)
  have edψ : (fun k => (transverseModeTest q h).jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩) =
      fun k x => (if k = q then 2 * Real.pi * Complex.I * ((-h : ℤ) : ℂ) else 0) *
        modeExp q (-h) x :=
    funext fun k => funext (transverseModeTest_grad q h k)
  have esrc : (fun t x => (((ContinuousLinearMap.id ℝ ℝ) (g t x) : ℝ) : ℂ)) =
      fun t x => ((g t x : ℝ) : ℂ) := rfl
  rw [esrc, eu, edu, eψ, edψ, cellWeakIdentity_iff] at hW
  obtain ⟨-, -, -, hint, heq⟩ := hW
  have hwin : ∀ τ ∈ Ioc s t, τ ∈ Icc t₀ t₁ := fun τ hτ =>
    ⟨hs.trans hτ.1.le, hτ.2.trans ht⟩
  have key : EqOn (fun τ => ∫ x in AVenhance.unitCube, weakRhs ⟨fun t _ => G t, v, 0, 0⟩
      (modeExp q (-h))
      (fun k x => (if k = q then 2 * Real.pi * Complex.I * ((-h : ℤ) : ℂ) else 0) *
        modeExp q (-h) x)
      (fun τ x => ((c τ x : ℝ) : ℂ)) (fun τ k x => ((fderiv ℝ (c τ) x (basisVec k) : ℝ) : ℂ))
      (fun τ x => ((g τ x : ℝ) : ℂ)) (fun _ _ => 0) τ x)
      (fun τ => ((-(4 * Real.pi ^ 2 * (h : ℝ) ^ 2) * G τ q q : ℝ) : ℂ) *
        phaseCoeff q (c τ) h + phaseCoeff q (g τ) h) (Ioc s t) := by
    intro τ hτ
    have hτ' := hwin τ hτ
    have hc1 : ContDiff ℝ 1 (c τ) := (hreg τ hτ').of_le (by exact_mod_cast hsZ)
    have hper : AVenhance.IsZ2Periodic (c τ) :=
      periodic_of_cellFieldInverse ⟨hreg, hsol⟩ hτ'
    have hdc : Continuous fun x => fderiv ℝ (c τ) x (basisVec q) :=
      (hc1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    simp only
    simp_rw [weakRhs_mode G v g c h (hct τ hτ') (hvq τ hτ')]
    have i1 : IntegrableOn (fun x => -((G τ q q : ℂ) * (2 * Real.pi * Complex.I * ((-h : ℤ) : ℂ))) *
        (((fderiv ℝ (c τ) x (basisVec q) : ℝ) : ℂ) * modeExp q (-h) x)) AVenhance.unitCube :=
      integrableOn_unitCube_of_continuous' (continuous_const.mul
        ((Complex.continuous_ofReal.comp hdc).mul (contDiff_modeExp q (-h) (n := 0)).continuous))
    have i2 : IntegrableOn (fun x => ((g τ x : ℝ) : ℂ) * modeExp q (-h) x) AVenhance.unitCube :=
      integrableOn_unitCube_of_continuous' ((Complex.continuous_ofReal.comp (hgc τ hτ')).mul
        (contDiff_modeExp q (-h) (n := 0)).continuous)
    rw [integral_add i1 i2, integral_const_mul,
      integral_unitCube_mul_modeExp_neg ((hct τ hτ').fderiv_q (hc1.differentiable one_ne_zero)) h,
      integral_unitCube_mul_modeExp_neg (hgt τ hτ') h, phaseCoeff_deriv hc1 hper h]
    push_cast
    linear_combination (4 * (Real.pi : ℂ) ^ 2 * (h : ℂ) ^ 2 * (G τ q q : ℂ) *
      phaseCoeff q (c τ) h) * Complex.I_sq
  refine ⟨hint.congr_fun key measurableSet_Ioc, ?_⟩
  beta_reduce at heq
  rw [← setIntegral_congr_fun measurableSet_Ioc key, ← heq,
    integral_unitCube_mul_modeExp_neg (hct t ⟨hs.trans hst, ht⟩) h,
    integral_unitCube_mul_modeExp_neg (hct s ⟨hs, hst.trans ht⟩) h]

/-- The transverse modes of a cell inverse from zero vanish at the start. -/
theorem phaseCoeff_cellFieldInverse_start {q : Fin 2} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {v : ℝ → Vec 2 → Vec 2} {sZ : ℕ} {t₀ t₁ : ℝ} {g c : ℝ → Vec 2 → ℝ}
    (hC : IsCellFieldInverse G v sZ t₀ t₁ (fun _ => 0) g c) (hct : IsTransverse q (c t₀))
    (h : ℤ) : phaseCoeff q (c t₀) h = 0 := by
  obtain ⟨-, -, hinit, -⟩ := hC.2 (ContinuousLinearMap.id ℝ ℝ)
  rw [← integral_unitCube_mul_modeExp_neg hct h]
  have e : (fun x => ((c t₀ x : ℝ) : ℂ) * modeExp q (-h) x) =ᵐ[volume.restrict AVenhance.unitCube]
      fun _ => 0 := by
    filter_upwards [hinit] with x hx
    simp [cellValue, cellJetOfField, valueIndex2, valueIndex] at hx
    simp [hx]
  rw [integral_congr_ae e, integral_zero]

/-- The zero transverse mode of a cell inverse vanishes (zero cell mean). -/
theorem phaseCoeff_cellFieldInverse_zero {q : Fin 2} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {v : ℝ → Vec 2 → Vec 2} {sZ : ℕ} {t₀ t₁ : ℝ} {g c : ℝ → Vec 2 → ℝ}
    (hC : IsCellFieldInverse G v sZ t₀ t₁ (fun _ => 0) g c) {τ : ℝ} (hτ : τ ∈ Icc t₀ t₁)
    (hct : IsTransverse q (c τ)) : phaseCoeff q (c τ) 0 = 0 := by
  obtain ⟨-, hmean, -, -⟩ := hC.2 (ContinuousLinearMap.id ℝ ℝ)
  have := hmean τ hτ
  rw [← integral_unitCube_mul_modeExp_neg hct 0]
  simpa [cellMean, cellValue, cellJetOfField, valueIndex2, valueIndex, modeExp] using this

end AVRegularity.Providers.Transverse
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization
namespace AVRegularity.Providers.Transverse

/-! **The transverse cell inverse.** For a transverse flux with summably decaying modes,
a metric whose transverse entry is `a(cτ)` and a drift without transverse component, the series
`ω(τ) = Re ∑_h A_h(τ) e_h` of the Duhamel amplitudes is the finite-past cell inverse
(`IsCellFieldInverse`) of the source `∂_q F_q = Re ∑_h 2πih F_h(cτ) e_h`, from zero at `τ₀`. -/

section
/-- The mode multiplier of `∂_k`. -/
def dmul (q k : Fin 2) (h : ℤ) : ℂ := if k = q then 2 * Real.pi * Complex.I * (h : ℂ) else 0

namespace TData

variable (T : TData) (q : Fin 2)

/-- The transverse cell inverse (cell time). -/
def sol (τ : ℝ) (x : Vec 2) : ℝ := (tser q (fun h => T.amp h τ) x).re

/-- The source `∂_q F_q` (cell time). -/
def src (τ : ℝ) (x : Vec 2) : ℝ :=
  (tser q (fun h => 2 * Real.pi * Complex.I * (h : ℂ) * T.Fm h (T.c * τ)) x).re

end TData
end

/-! The `Gen` semantics of the transverse inverse (`transverseInverseSem`, zero initial state) is
the series `TData.sol` of the transverse cell inverse, in cell time, whenever the data agree with
the transverse metric entry and the transverse flux modes of the chain after the start. -/

theorem modeW_congr {c : ℝ} {a a' : ℝ → ℝ} {F F' : ℝ → ℂ} {t₀ : ℝ} (h : ℤ) {t : ℝ}
    (ht : t₀ ≤ t) (ha : ∀ u ∈ Icc t₀ t, a u = a' u) (hF : ∀ s ∈ Icc t₀ t, F s = F' s) :
    modeW c a F t₀ h t = modeW c a' F' t₀ h t := by
  unfold modeW
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le ht] at hs
  rw [hF s hs]
  have hi : ∫ u in s..t, a u = ∫ u in s..t, a' u := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le hs.2] at hu
    exact ha u ⟨hs.1.trans hu.1, hu.2⟩
  simp only [modeK, hi]

theorem phaseCoeff_zero (q : Fin 2) (h : ℤ) : phaseCoeff q (fun _ => (0 : ℝ)) h = 0 := by
  simp [phaseCoeff]

end AVRegularity.Providers.Transverse
end
end
end
