-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CoupledEnergy.Galerkin.PlainVariationalEnergy
public import AVRegularity.CycleComparison.Lift.SettingDimensionalScales
public import AVRegularity.Statements.Intermediate.CoupledEnergy.CoupledSolutionTorus
public import AVRegularity.CycleComparison.Coarse.Adj.Coarse
import AVRegularity.CycleComparison.Coarse.Fact.GradWord
public import AVRegularity.CoupledEnergy.Galerkin.CarrierFamilyProjection
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

section
@[expose] public noncomputable section
open MeasureTheory Filter Topology
namespace AVRegularity.CycleComparison.Coarse

/-! Extension of an integrated identity `L φ = ∫_{(t₀,t]} R(s) φ ds` from an approximating sequence
to its limit, for maps `L`, `R(s)` that are subtractive and uniformly bounded in the test. -/

/-- **Density extension of an integrated identity.** -/
theorem integrated_identity_of_tendsto {X : Type*} [SeminormedAddCommGroup X]
    {t₀ t : ℝ} (L : X → ℝ) (R : ℝ → X → ℝ)
    (hLsub : ∀ φ φ', L (φ - φ') = L φ - L φ') {c : ℝ} (hLb : ∀ φ, |L φ| ≤ c * ‖φ‖)
    (hRsub : ∀ s ∈ Set.Ioc t₀ t, ∀ φ φ', R s (φ - φ') = R s φ - R s φ') {M : ℝ}
    (hRb : ∀ s ∈ Set.Ioc t₀ t, ∀ φ, |R s φ| ≤ M * ‖φ‖)
    {φ : X} {φN : ℕ → X} (hconv : Tendsto φN atTop (𝓝 φ))
    (hN : ∀ n, IntegrableOn (fun s => R s (φN n)) (Set.Ioc t₀ t) ∧
      L (φN n) = ∫ s in Set.Ioc t₀ t, R s (φN n)) :
    IntegrableOn (fun s => R s φ) (Set.Ioc t₀ t) ∧ L φ = ∫ s in Set.Ioc t₀ t, R s φ := by
  have hdist : Tendsto (fun n => ‖φN n - φ‖) atTop (𝓝 0) := by
    simpa [dist_eq_norm] using (tendsto_iff_dist_tendsto_zero.1 hconv)
  have hRb' : ∀ s ∈ Set.Ioc t₀ t, ∀ ψ, |R s ψ| ≤ |M| * ‖ψ‖ := fun s hs ψ =>
    (hRb s hs ψ).trans (mul_le_mul_of_nonneg_right (le_abs_self M) (norm_nonneg ψ))
  -- pointwise convergence of the right sides
  have hpt : ∀ s ∈ Set.Ioc t₀ t, Tendsto (fun n => R s (φN n)) atTop (𝓝 (R s φ)) := by
    intro s hs
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (by simpa using hdist.const_mul |M|)
    rw [Real.norm_eq_abs, ← hRsub s hs]
    exact hRb' s hs _
  -- the limit right side is integrable
  have hmeas : AEStronglyMeasurable (fun s => R s φ) (volume.restrict (Set.Ioc t₀ t)) :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hN n).1.aestronglyMeasurable)
      ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall hpt))
  have hint : IntegrableOn (fun s => R s φ) (Set.Ioc t₀ t) := by
    have : IsFiniteMeasure (volume.restrict (Set.Ioc t₀ t)) := ⟨by
      rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
    exact ⟨hmeas, HasFiniteIntegral.of_bounded (C := |M| * ‖φ‖)
      ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun s hs => by
        rw [Real.norm_eq_abs]; exact hRb' s hs φ))⟩
  refine ⟨hint, ?_⟩
  -- convergence of both sides
  have hL : Tendsto (fun n => L (φN n)) atTop (𝓝 (L φ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (by simpa using hdist.const_mul |c|)
    rw [Real.norm_eq_abs, ← hLsub]
    exact (hLb _).trans (mul_le_mul_of_nonneg_right (le_abs_self c) (norm_nonneg _))
  have hI : Tendsto (fun n => ∫ s in Set.Ioc t₀ t, R s (φN n)) atTop
      (𝓝 (∫ s in Set.Ioc t₀ t, R s φ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (g := fun n => |M| * ‖φN n - φ‖ * volume.real (Set.Ioc t₀ t))
      (fun n => norm_nonneg _) (fun n => ?_)
      (by simpa using (hdist.const_mul |M|).mul_const (volume.real (Set.Ioc t₀ t)))
    rw [← integral_sub (hN n).1 hint]
    have hb : ∀ s ∈ Set.Ioc t₀ t, ‖R s (φN n) - R s φ‖ ≤ |M| * ‖φN n - φ‖ := fun s hs => by
      rw [Real.norm_eq_abs, ← hRsub s hs]
      exact hRb' s hs _
    exact norm_setIntegral_le_of_norm_le_const measure_Ioc_lt_top hb
  have hL' : Tendsto (fun n => L (φN n)) atTop (𝓝 (∫ s in Set.Ioc t₀ t, R s φ)) :=
    hI.congr fun n => ((hN n).2).symm
  exact tendsto_nhds_unique hL hL'

end AVRegularity.CycleComparison.Coarse
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
namespace AVRegularity.CycleComparison.Coarse

/-! The product rule for indefinite integrals: if `c` and `g` are of integral type on `[t₀,t]`,
i.e. `c s = c t₀ + ∫_{(t₀,s]} dc`, then `c g` is again of integral type with density
`dc g + c dg`. The proof goes through Mathlib's absolutely continuous integration by parts and
the Lebesgue differentiation theorem. Indefinite integrals are continuous, hence bounded. -/

/-- The global indefinite integral `s ↦ c₀ + ∫_{t₀}^s d`. -/
def primFun (c₀ t₀ : ℝ) (d : ℝ → ℝ) (s : ℝ) : ℝ := c₀ + ∫ σ in t₀..s, d σ

theorem intervalIntegrable_of_integrableOn {t₀ t : ℝ} (ht : t₀ ≤ t) {d : ℝ → ℝ}
    (hd : IntegrableOn d (Ioc t₀ t)) : IntervalIntegrable d volume t₀ t :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).2 hd

theorem integrableOn_Ioc_mono {t₀ t s : ℝ} (hs : s ∈ Icc t₀ t) {d : ℝ → ℝ}
    (hd : IntegrableOn d (Ioc t₀ t)) : IntegrableOn d (Ioc t₀ s) :=
  hd.mono_set (Ioc_subset_Ioc_right hs.2)

theorem primFun_eq_of_mem {t₀ t : ℝ} {c : ℝ → ℝ} {dc : ℝ → ℝ}
    (hc : ∀ s ∈ Icc t₀ t, c s = c t₀ + ∫ σ in Ioc t₀ s, dc σ) {s : ℝ} (hs : s ∈ Icc t₀ t) :
    c s = primFun (c t₀) t₀ dc s := by
  rw [hc s hs, primFun, intervalIntegral.integral_of_le hs.1]

theorem absolutelyContinuousOnInterval_primFun {t₀ t : ℝ} (ht : t₀ ≤ t) (c₀ : ℝ) {d : ℝ → ℝ}
    (hd : IntegrableOn d (Ioc t₀ t)) :
    AbsolutelyContinuousOnInterval (primFun c₀ t₀ d) t₀ t := by
  have h1 := (intervalIntegrable_of_integrableOn ht hd).absolutelyContinuousOnInterval_intervalIntegral
    (c := t₀) left_mem_uIcc
  have h2 : AbsolutelyContinuousOnInterval (fun _ : ℝ => c₀) t₀ t :=
    (LipschitzWith.const c₀).lipschitzOnWith.absolutelyContinuousOnInterval
  exact h2.add h1

theorem continuousOn_primFun {t₀ t : ℝ} (ht : t₀ ≤ t) (c₀ : ℝ) {d : ℝ → ℝ}
    (hd : IntegrableOn d (Ioc t₀ t)) : ContinuousOn (primFun c₀ t₀ d) (Icc t₀ t) := by
  have := (absolutelyContinuousOnInterval_primFun ht c₀ hd).continuousOn
  rwa [uIcc_of_le ht] at this

theorem ae_deriv_primFun {t₀ t : ℝ} (ht : t₀ ≤ t) (c₀ : ℝ) {d : ℝ → ℝ}
    (hd : IntegrableOn d (Ioc t₀ t)) :
    ∀ᵐ s ∂(volume.restrict (Ioc t₀ t)), deriv (primFun c₀ t₀ d) s = d s := by
  have h := (intervalIntegrable_of_integrableOn ht hd).ae_hasDerivAt_integral
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [h] with s hs hsm
  have := (hs (by rw [uIcc_of_le ht]; exact Ioc_subset_Icc_self hsm) t₀
    (by rw [uIcc_of_le ht]; exact left_mem_Icc.2 ht)).const_add c₀
  exact this.deriv

/-- **Product rule for indefinite integrals.** -/
theorem product_rule_integral {t₀ t : ℝ} (ht : t₀ ≤ t) {c g dc dg : ℝ → ℝ}
    (hdc : IntegrableOn dc (Set.Ioc t₀ t)) (hdg : IntegrableOn dg (Set.Ioc t₀ t))
    (hc : ∀ s ∈ Set.Icc t₀ t, c s = c t₀ + ∫ σ in Set.Ioc t₀ s, dc σ)
    (hg : ∀ s ∈ Set.Icc t₀ t, g s = g t₀ + ∫ σ in Set.Ioc t₀ s, dg σ) :
    IntegrableOn (fun s => dc s * g s + c s * dg s) (Set.Ioc t₀ t) ∧
      c t * g t - c t₀ * g t₀ = ∫ s in Set.Ioc t₀ t, (dc s * g s + c s * dg s) := by
  have hCc := continuousOn_primFun ht (c t₀) hdc
  have hGc := continuousOn_primFun ht (g t₀) hdg
  have hCa := absolutelyContinuousOnInterval_primFun ht (c t₀) hdc
  have hGa := absolutelyContinuousOnInterval_primFun ht (g t₀) hdg
  have hcC : ∀ s ∈ Ioc t₀ t, c s = primFun (c t₀) t₀ dc s := fun s hs =>
    primFun_eq_of_mem hc ⟨hs.1.le, hs.2⟩
  have hgG : ∀ s ∈ Ioc t₀ t, g s = primFun (g t₀) t₀ dg s := fun s hs =>
    primFun_eq_of_mem hg ⟨hs.1.le, hs.2⟩
  have hdcI : IntegrableOn dc (Icc t₀ t) := (integrableOn_Icc_iff_integrableOn_Ioc).2 hdc
  have hdgI : IntegrableOn dg (Icc t₀ t) := (integrableOn_Icc_iff_integrableOn_Ioc).2 hdg
  have hint : IntegrableOn (fun s => dc s * primFun (g t₀) t₀ dg s +
      primFun (c t₀) t₀ dc s * dg s) (Ioc t₀ t) :=
    ((hdcI.mul_continuousOn hGc isCompact_Icc).add
      (hdgI.continuousOn_mul hCc isCompact_Icc)).mono_set Ioc_subset_Icc_self
  have hcongr : EqOn (fun s => dc s * g s + c s * dg s)
      (fun s => dc s * primFun (g t₀) t₀ dg s + primFun (c t₀) t₀ dc s * dg s) (Ioc t₀ t) :=
    fun s hs => by simp only [hcC s hs, hgG s hs]
  refine ⟨hint.congr_fun hcongr.symm measurableSet_Ioc, ?_⟩
  have key := AbsolutelyContinuousOnInterval.integral_deriv_mul_eq_sub hCa hGa
  rw [intervalIntegral.integral_of_le ht] at key
  have e1 : ∫ x in Ioc t₀ t, (deriv (primFun (c t₀) t₀ dc) x * primFun (g t₀) t₀ dg x +
      primFun (c t₀) t₀ dc x * deriv (primFun (g t₀) t₀ dg) x) =
      ∫ x in Ioc t₀ t, (dc x * primFun (g t₀) t₀ dg x + primFun (c t₀) t₀ dc x * dg x) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_deriv_primFun ht (c t₀) hdc, ae_deriv_primFun ht (g t₀) hdg] with s h1 h2
    simp only [h1, h2]
  rw [e1] at key
  rw [setIntegral_congr_fun measurableSet_Ioc hcongr, key]
  have a1 : primFun (c t₀) t₀ dc t = c t := (primFun_eq_of_mem hc ⟨ht, le_rfl⟩).symm
  have a2 : primFun (g t₀) t₀ dg t = g t := (primFun_eq_of_mem hg ⟨ht, le_rfl⟩).symm
  have a3 : primFun (c t₀) t₀ dc t₀ = c t₀ := by simp [primFun]
  have a4 : primFun (g t₀) t₀ dg t₀ = g t₀ := by simp [primFun]
  rw [a1, a2, a3, a4]

/-- The product of two functions of integral type is of integral type. -/
theorem prod_prim {t₀ t : ℝ} {c g dc dg : ℝ → ℝ}
    (hdc : IntegrableOn dc (Set.Ioc t₀ t)) (hdg : IntegrableOn dg (Set.Ioc t₀ t))
    (hc : ∀ s ∈ Set.Icc t₀ t, c s = c t₀ + ∫ σ in Set.Ioc t₀ s, dc σ)
    (hg : ∀ s ∈ Set.Icc t₀ t, g s = g t₀ + ∫ σ in Set.Ioc t₀ s, dg σ) :
    ∀ s ∈ Set.Icc t₀ t, c s * g s =
      c t₀ * g t₀ + ∫ σ in Set.Ioc t₀ s, (dc σ * g σ + c σ * dg σ) := by
  intro s hs
  have h := product_rule_integral hs.1
    (integrableOn_Ioc_mono hs hdc) (integrableOn_Ioc_mono hs hdg)
    (fun r hr => hc r ⟨hr.1, hr.2.trans hs.2⟩) (fun r hr => hg r ⟨hr.1, hr.2.trans hs.2⟩)
  linarith [h.2]

end AVRegularity.CycleComparison.Coarse
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization
namespace AVRegularity.CycleComparison.Coarse

/-! Time-dependent test fields `∑ₖ cₖ(t) ψₖ` with fixed smooth periodic `ψₖ` and coefficients of
integral type on `[t₀,t₁]`, together with the operations that keep this class: constants, sums,
constant multiples, products with scalar functions of integral type, and the application of a
fixed smooth-linear operator. `TimeTest.val` is the field at time `t` and `TimeTest.deriv` its
time derivative. -/

/-- A time-dependent test field `∑ₖ cₖ(t) ψₖ` with fixed smooth periodic `ψₖ` and coefficients of
integral type on `[t₀,t₁]`. -/
structure TimeTest (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (t₀ t₁ : ℝ) where
  /-- The finite index type. -/
  ι : Type
  [fin : Fintype ι]
  /-- The coefficients. -/
  c : ι → ℝ → ℝ
  /-- The coefficient densities. -/
  dc : ι → ℝ → ℝ
  /-- The fixed fields. -/
  ψ : ι → Vec 2 → E
  smooth : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (ψ k)
  per : ∀ k, AVenhance.IsZ2Periodic (ψ k)
  dc_int : ∀ k, IntegrableOn (dc k) (Set.Ioc t₀ t₁)
  prim : ∀ k, ∀ t ∈ Set.Icc t₀ t₁, c k t = c k t₀ + ∫ s in Set.Ioc t₀ t, dc k s

attribute [instance] TimeTest.fin

/-- An operator on fields that preserves smooth periodic fields and is additive and homogeneous
on smooth fields. -/
structure SmoothLinOp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : (Vec 2 → E) → (Vec 2 → E)) : Prop where
  smooth : ∀ f, ContDiff ℝ (⊤ : ℕ∞) f → ContDiff ℝ (⊤ : ℕ∞) (T f)
  per : ∀ f, ContDiff ℝ (⊤ : ℕ∞) f → AVenhance.IsZ2Periodic f → AVenhance.IsZ2Periodic (T f)
  lin : ∀ {κ : Type} [Fintype κ] (a : κ → ℝ) (f : κ → Vec 2 → E),
    (∀ k, ContDiff ℝ (⊤ : ℕ∞) (f k)) →
    T (fun x => ∑ k, a k • f k x) = fun x => ∑ k, a k • T (f k) x

namespace TimeTest

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {t₀ t₁ : ℝ}

/-- The field at time `t`. -/
def val (Φ : TimeTest E t₀ t₁) (t : ℝ) : Vec 2 → E := fun x => ∑ k, Φ.c k t • Φ.ψ k x

/-- The time derivative of the field at time `t`. -/
def deriv (Φ : TimeTest E t₀ t₁) (t : ℝ) : Vec 2 → E := fun x => ∑ k, Φ.dc k t • Φ.ψ k x

/-- The constant test field `ψ`. -/
def const (ψ : Vec 2 → E) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hp : AVenhance.IsZ2Periodic ψ) :
    TimeTest E t₀ t₁ where
  ι := Unit
  c _ _ := 1
  dc _ _ := 0
  ψ _ := ψ
  smooth _ := hψ
  per _ := hp
  dc_int _ := integrableOn_zero
  prim _ _ _ := by simp

theorem val_const (ψ : Vec 2 → E) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hp : AVenhance.IsZ2Periodic ψ)
    (t : ℝ) : (const (t₀ := t₀) (t₁ := t₁) ψ hψ hp).val t = ψ := by
  funext x
  show ∑ _k : Unit, (1 : ℝ) • ψ x = ψ x
  simp

theorem deriv_const (ψ : Vec 2 → E) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hp : AVenhance.IsZ2Periodic ψ)
    (t : ℝ) : (const (t₀ := t₀) (t₁ := t₁) ψ hψ hp).deriv t = 0 := by
  funext x
  show ∑ _k : Unit, (0 : ℝ) • ψ x = 0
  simp

/-- The sum of two test fields. -/
def add (Φ Ψ : TimeTest E t₀ t₁) : TimeTest E t₀ t₁ where
  ι := Φ.ι ⊕ Ψ.ι
  c := Sum.elim Φ.c Ψ.c
  dc := Sum.elim Φ.dc Ψ.dc
  ψ := Sum.elim Φ.ψ Ψ.ψ
  smooth := fun k => by cases k with
    | inl k => exact Φ.smooth k
    | inr k => exact Ψ.smooth k
  per := fun k => by cases k with
    | inl k => exact Φ.per k
    | inr k => exact Ψ.per k
  dc_int := fun k => by cases k with
    | inl k => exact Φ.dc_int k
    | inr k => exact Ψ.dc_int k
  prim := fun k => by cases k with
    | inl k => exact Φ.prim k
    | inr k => exact Ψ.prim k

/-- The multiple of a test field by a function `h` of integral type. -/
def mulScalar (h dh : ℝ → ℝ) (ht : t₀ ≤ t₁) (hdh : IntegrableOn dh (Ioc t₀ t₁))
    (hh : ∀ t ∈ Icc t₀ t₁, h t = h t₀ + ∫ s in Ioc t₀ t, dh s) (Φ : TimeTest E t₀ t₁) :
    TimeTest E t₀ t₁ where
  ι := Φ.ι
  c k t := h t * Φ.c k t
  dc k t := dh t * Φ.c k t + h t * Φ.dc k t
  ψ := Φ.ψ
  smooth := Φ.smooth
  per := Φ.per
  dc_int k := (product_rule_integral ht hdh (Φ.dc_int k) hh (Φ.prim k)).1
  prim k t htm := by
    exact prod_prim hdh (Φ.dc_int k) hh (Φ.prim k) t htm

theorem val_mulScalar (h dh : ℝ → ℝ) (ht : t₀ ≤ t₁) (hdh : IntegrableOn dh (Ioc t₀ t₁))
    (hh : ∀ t ∈ Icc t₀ t₁, h t = h t₀ + ∫ s in Ioc t₀ t, dh s) (Φ : TimeTest E t₀ t₁) (t : ℝ) :
    (mulScalar h dh ht hdh hh Φ).val t = fun x => h t • Φ.val t x := by
  funext x; simp [val, mulScalar, Finset.smul_sum, mul_smul]; rfl

theorem deriv_mulScalar (h dh : ℝ → ℝ) (ht : t₀ ≤ t₁) (hdh : IntegrableOn dh (Ioc t₀ t₁))
    (hh : ∀ t ∈ Icc t₀ t₁, h t = h t₀ + ∫ s in Ioc t₀ t, dh s) (Φ : TimeTest E t₀ t₁) (t : ℝ) :
    (mulScalar h dh ht hdh hh Φ).deriv t = fun x => dh t • Φ.val t x + h t • Φ.deriv t x := by
  funext x
  simp [deriv, val, mulScalar, Finset.smul_sum, mul_smul, add_smul, Finset.sum_add_distrib]
  rfl

/-- A constant multiple of a test field. -/
def smul (a : ℝ) (Φ : TimeTest E t₀ t₁) : TimeTest E t₀ t₁ where
  ι := Φ.ι
  c k t := a * Φ.c k t
  dc k t := a * Φ.dc k t
  ψ := Φ.ψ
  smooth := Φ.smooth
  per := Φ.per
  dc_int k := (Φ.dc_int k).const_mul a
  prim k t htm := by
    rw [Φ.prim k t htm, integral_const_mul]; ring

/-- A finite weighted sum of test fields. -/
def sum {κ : Type} [Fintype κ] (a : κ → ℝ) (Φ : κ → TimeTest E t₀ t₁) : TimeTest E t₀ t₁ where
  ι := Σ m, (Φ m).ι
  c p t := a p.1 * (Φ p.1).c p.2 t
  dc p t := a p.1 * (Φ p.1).dc p.2 t
  ψ p := (Φ p.1).ψ p.2
  smooth p := (Φ p.1).smooth p.2
  per p := (Φ p.1).per p.2
  dc_int p := ((Φ p.1).dc_int p.2).const_mul _
  prim p t htm := by
    rw [(Φ p.1).prim p.2 t htm, integral_const_mul]; ring

omit [NormedSpace ℝ E] in
theorem sum_sigma_aux {κ : Type} [Fintype κ] {ι : κ → Type} [∀ m, Fintype (ι m)] (g : (Σ m, ι m) → E) :
    ∑ k, g k = ∑ m, ∑ j, g ⟨m, j⟩ := by
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]

theorem val_sum {κ : Type} [Fintype κ] (a : κ → ℝ) (Φ : κ → TimeTest E t₀ t₁) (t : ℝ) :
    (sum a Φ).val t = fun x => ∑ m, a m • (Φ m).val t x := by
  funext x
  simp only [val, sum, Finset.smul_sum, mul_smul]
  exact sum_sigma_aux _

theorem deriv_sum {κ : Type} [Fintype κ] (a : κ → ℝ) (Φ : κ → TimeTest E t₀ t₁) (t : ℝ) :
    (sum a Φ).deriv t = fun x => ∑ m, a m • (Φ m).deriv t x := by
  funext x
  simp only [deriv, sum, Finset.smul_sum, mul_smul]
  exact sum_sigma_aux _

/-- The application of a smooth-linear operator `T` to a test field. -/
def mapOp {T : (Vec 2 → E) → (Vec 2 → E)} (hT : SmoothLinOp T) (Φ : TimeTest E t₀ t₁) :
    TimeTest E t₀ t₁ where
  ι := Φ.ι
  c := Φ.c
  dc := Φ.dc
  ψ k := T (Φ.ψ k)
  smooth k := hT.smooth _ (Φ.smooth k)
  per k := hT.per _ (Φ.smooth k) (Φ.per k)
  dc_int := Φ.dc_int
  prim := Φ.prim

theorem val_mapOp {T : (Vec 2 → E) → (Vec 2 → E)} (hT : SmoothLinOp T) (Φ : TimeTest E t₀ t₁)
    (t : ℝ) : (mapOp hT Φ).val t = T (Φ.val t) := by
  have := hT.lin (fun k => Φ.c k t) Φ.ψ Φ.smooth
  funext x
  exact (congrFun this x).symm

theorem deriv_mapOp {T : (Vec 2 → E) → (Vec 2 → E)} (hT : SmoothLinOp T) (Φ : TimeTest E t₀ t₁)
    (t : ℝ) : (mapOp hT Φ).deriv t = T (Φ.deriv t) := by
  have := hT.lin (fun k => Φ.dc k t) Φ.ψ Φ.smooth
  funext x
  exact (congrFun this x).symm

/-- The combination `∑ₘ hₘ(t) Tₘ Φ(t)` with scalar functions `hₘ` of integral type and
smooth-linear operators `Tₘ`. -/
def lincomb {κ : Type} [Fintype κ] (h dh : κ → ℝ → ℝ) (ht : t₀ ≤ t₁)
    (hdh : ∀ m, IntegrableOn (dh m) (Ioc t₀ t₁))
    (hh : ∀ m, ∀ t ∈ Icc t₀ t₁, h m t = h m t₀ + ∫ s in Ioc t₀ t, dh m s)
    {T : κ → (Vec 2 → E) → (Vec 2 → E)} (hT : ∀ m, SmoothLinOp (T m)) (Φ : TimeTest E t₀ t₁) :
    TimeTest E t₀ t₁ :=
  sum (fun _ => (1 : ℝ)) fun m => mulScalar (h m) (dh m) ht (hdh m) (hh m) (mapOp (hT m) Φ)

theorem val_lincomb {κ : Type} [Fintype κ] (h dh : κ → ℝ → ℝ) (ht : t₀ ≤ t₁)
    (hdh : ∀ m, IntegrableOn (dh m) (Ioc t₀ t₁))
    (hh : ∀ m, ∀ t ∈ Icc t₀ t₁, h m t = h m t₀ + ∫ s in Ioc t₀ t, dh m s)
    {T : κ → (Vec 2 → E) → (Vec 2 → E)} (hT : ∀ m, SmoothLinOp (T m)) (Φ : TimeTest E t₀ t₁)
    (t : ℝ) : (lincomb h dh ht hdh hh hT Φ).val t = fun x => ∑ m, h m t • T m (Φ.val t) x := by
  funext x
  simp only [lincomb, val_sum, val_mulScalar, val_mapOp, one_smul]

theorem deriv_lincomb {κ : Type} [Fintype κ] (h dh : κ → ℝ → ℝ) (ht : t₀ ≤ t₁)
    (hdh : ∀ m, IntegrableOn (dh m) (Ioc t₀ t₁))
    (hh : ∀ m, ∀ t ∈ Icc t₀ t₁, h m t = h m t₀ + ∫ s in Ioc t₀ t, dh m s)
    {T : κ → (Vec 2 → E) → (Vec 2 → E)} (hT : ∀ m, SmoothLinOp (T m)) (Φ : TimeTest E t₀ t₁)
    (t : ℝ) : (lincomb h dh ht hdh hh hT Φ).deriv t =
      fun x => ∑ m, (dh m t • T m (Φ.val t) x + h m t • T m (Φ.deriv t) x) := by
  funext x
  simp only [lincomb, deriv_sum, deriv_mulScalar, val_mapOp, deriv_mapOp, one_smul]

end TimeTest

end AVRegularity.CycleComparison.Coarse
end
end

section
section
/-! Smooth approximants of a first-order periodic Sobolev field: the Galerkin projections converge
to the field, and their value and first-derivative jets are, almost everywhere on the cell, a
smooth periodic field and its first derivatives. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin

namespace AVRegularity.CycleComparison.Coarse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The smooth field of the `n`-th Galerkin approximant. -/
def approxField (n : ℕ) (φ : TorusHk 1 E) : Vec 2 → E :=
  smoothFourierJet (L := 1) n φ (valueIndex2 1)

theorem approxField_contDiff (n : ℕ) (φ : TorusHk 1 E) :
    ContDiff ℝ (⊤ : ℕ∞) (approxField n φ) :=
  smoothFourierJet_contDiff n φ _

theorem approxField_periodic (n : ℕ) (φ : TorusHk 1 E) :
    AVenhance.IsZ2Periodic (approxField n φ) :=
  smoothFourierJet_periodic n φ _

theorem galerkin_value_ae (n : ℕ) (φ : TorusHk 1 E) :
    (galerkinProj n φ).toFunction.jet (valueIndex2 1)
      =ᵐ[volume.restrict AVenhance.unitCube] approxField n φ :=
  (periodicJetRepresentative_ae _ _).trans (galerkinProj_jet_ae_smooth n φ _)

theorem galerkin_deriv_ae (n : ℕ) (φ : TorusHk 1 E) (k : Fin 2) :
    (galerkinProj n φ).toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩
      =ᵐ[volume.restrict AVenhance.unitCube]
        fun x => fderiv ℝ (approxField n φ) x (basisVec k) := by
  refine (periodicJetRepresentative_ae _ _).trans
    ((galerkinProj_jet_ae_smooth n φ _).trans (ae_of_all _ fun x => ?_))
  have hlow : lowerIndex2 (⟨0, Nat.one_pos⟩ : Fin 1) Fin.elim0 = valueIndex2 1 := by
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      funext z
      exact Fin.elim0 z
  have hnext : nextIndex2 (⟨0, Nat.one_pos⟩ : Fin 1) Fin.elim0 k =
      (⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ : JetIndex2 1) := by
    unfold nextIndex2 nextIndex
    congr 1
  have h := smoothFourierJet_fderiv (L := 1) n φ (⟨0, Nat.one_pos⟩ : Fin 1) Fin.elim0 k x
  rw [hlow, hnext] at h
  exact h.symm

end AVRegularity.CycleComparison.Coarse
end
end

section
/-! The weak identity of a response (a decoupled second-order energy solution with a flux) tested
with a `C¹` periodic field: the field is promoted to a first-order periodic Sobolev field whose
jets are, almost everywhere, the field and its first derivatives. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev

namespace AVRegularity.CycleComparison.Coarse

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E]

/-- A `C¹` periodic field as a first-order periodic Sobolev field. -/
def smoothH1 (ψ : Vec 2 → E) (hψ : ContDiff ℝ 1 ψ) (hp : AVenhance.IsZ2Periodic ψ) :
    TorusHk 1 E :=
  (⟨Lift.classicalCellJet ψ, Lift.classicalCellJet_periodicWeak ψ hψ hp⟩ :
    TorusHkFunction 1 E).toHk

theorem smoothH1_value_ae (ψ : Vec 2 → E) (hψ : ContDiff ℝ 1 ψ) (hp : AVenhance.IsZ2Periodic ψ) :
    (smoothH1 ψ hψ hp).toFunction.jet (valueIndex2 1) =ᵐ[volume.restrict AVenhance.unitCube]
      ψ := by
  refine (TorusHkFunction.toHk_toFunction_ae _ (valueIndex2 1)).trans (ae_of_all _ fun x => ?_)
  simp [Lift.classicalCellJet, valueIndex2, valueIndex]

theorem smoothH1_deriv_ae (ψ : Vec 2 → E) (hψ : ContDiff ℝ 1 ψ) (hp : AVenhance.IsZ2Periodic ψ)
    (k : Fin 2) :
    (smoothH1 ψ hψ hp).toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩
      =ᵐ[volume.restrict AVenhance.unitCube] fun x => fderiv ℝ ψ x (basisVec k) := by
  refine (TorusHkFunction.toHk_toFunction_ae _ _).trans (ae_of_all _ fun x => ?_)
  simp [Lift.classicalCellJet]

end Smooth

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- The integrand of the right side of the weak identity of a response, tested with `ψ`. -/
def respIntegrand {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] (B : ℝ) (b : ℝ → Vec 2 → Vec 2)
    {K : ℕ} (Uw : ℝ → TorusHk (K + 1) E) (G : ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => E)))
    (ψ : Vec 2 → E) (s : ℝ) (x : Vec 2) : ℝ :=
  -(∑ k : Fin 2, b s x k *
      inner ℝ ((Uw s).toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos K)⟩, fun _ => k⟩ x)
        (ψ x))
    - B * ∑ k : Fin 2,
      inner ℝ ((Uw s).toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos K)⟩, fun _ => k⟩ x)
        (fderiv ℝ ψ x (basisVec k))
    - ∑ k : Fin 2, inner ℝ ((G s).toFunction.jet (valueIndex2 K) x k)
        (fderiv ℝ ψ x (basisVec k))

/-- The right side of the weak identity of a response, tested with a `C¹` field `ψ`, at time `s`. -/
def respRhs {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] (B : ℝ) (b : ℝ → Vec 2 → Vec 2)
    {K : ℕ} (Uw : ℝ → TorusHk (K + 1) E) (G : ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => E)))
    (ψ : Vec 2 → E) (s : ℝ) : ℝ :=
  ∫ x in AVenhance.unitCube, respIntegrand B b Uw G ψ s x

/-- **The weak identity of a response with a `C¹` periodic test field.** -/
theorem resp_weak_smooth {B t₀ t₁ : ℝ} {b : ℝ → Vec 2 → Vec 2} {K : ℕ}
    {f₀ : ∀ v, TorusHk K (h v)} {G : ∀ v, ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => h v))}
    {U : ∀ v, ℝ → TorusHk K (h v)} {Uw : ∀ v, ℝ → TorusHk (K + 1) (h v)}
    (hsol : IsCoupledWeakSolutionTorus B t₀ t₁ b 2 (fun _ => K) (fun _ _ _ _ _ => 0) f₀ G
      (fun _ _ => 0) U Uw) (v : ι) {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) {ψ : Vec 2 → h v}
    (hψ : ContDiff ℝ 1 ψ) (hp : AVenhance.IsZ2Periodic ψ) :
    IntegrableOn (respRhs B b (Uw v) (G v) ψ) (Set.Ioc t₀ t) ∧
      cellInner (tval (U v t)) ψ - cellInner (tval (f₀ v)) ψ =
        ∫ s in Set.Ioc t₀ t, respRhs B b (Uw v) (G v) ψ s := by
  have h5 := hsol.2.2.2.2 v t ht (smoothH1 ψ hψ hp)
  obtain ⟨_, _, _, hint, heq⟩ := h5
  have hval := smoothH1_value_ae ψ hψ hp
  have hder := fun k => smoothH1_deriv_ae ψ hψ hp k
  have hg : (0 : TorusHk K (h v)).toFunction.jet (valueIndex2 K)
      =ᵐ[volume.restrict AVenhance.unitCube] fun _ => 0 := tval_zero_ae
  have hrhs : ∀ s, (∫ x in AVenhance.unitCube,
      (-(∑ k : Fin 2, b s x k * inner ℝ ((Uw v s).toFunction.jet
          ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos K)⟩, fun _ => k⟩ x)
          ((smoothH1 ψ hψ hp).toFunction.jet (valueIndex2 1) x))
        - B * ∑ k : Fin 2, inner ℝ ((Uw v s).toFunction.jet
          ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos K)⟩, fun _ => k⟩ x)
          ((smoothH1 ψ hψ hp).toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)
        - ∑ k : Fin 2, inner ℝ ((∑ i' : ι, ∑ d : admissibleOrders (fun _ => K) 2 v i',
            (0 : PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
              PiLp 2 (fun _ : Fin 2 => h v)) (WithLp.toLp 2 fun word =>
              (Uw i' s).toFunction.jet ⟨⟨d.1 - 1, by
                have h := Finset.mem_filter.1 d.2
                have := Finset.mem_Icc.1 h.1
                omega⟩, word⟩ x)) k + (G v s).toFunction.jet (valueIndex2 K) x k)
          ((smoothH1 ψ hψ hp).toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x)
        + inner ℝ ((0 : TorusHk K (h v)).toFunction.jet (valueIndex2 K) x)
          ((smoothH1 ψ hψ hp).toFunction.jet (valueIndex2 1) x))) =
      respRhs B b (Uw v) (G v) ψ s := by
    intro s
    unfold respRhs respIntegrand
    refine integral_congr_ae ?_
    filter_upwards [hval, hder 0, hder 1, hg] with x h0 hd0 hd1 hgx
    have hdk : ∀ k : Fin 2, (smoothH1 ψ hψ hp).toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩ x
        = fderiv ℝ ψ x (basisVec k) := fun k => by fin_cases k; exacts [hd0, hd1]
    simp only [h0, hdk, hgx, zero_apply, Finset.sum_const_zero,
      PiLp.zero_apply, zero_add, inner_zero_left, add_zero]
  have hL : ∫ x in AVenhance.unitCube, inner ℝ ((U v t).toFunction.jet (valueIndex2 K) x)
      ((smoothH1 ψ hψ hp).toFunction.jet (valueIndex2 1) x) = cellInner (tval (U v t)) ψ :=
    integral_congr_ae (hval.mono fun x hx => by beta_reduce; rw [hx]; rfl)
  have hF : ∫ x in AVenhance.unitCube, inner ℝ ((f₀ v).toFunction.jet (valueIndex2 K) x)
      ((smoothH1 ψ hψ hp).toFunction.jet (valueIndex2 1) x) = cellInner (tval (f₀ v)) ψ :=
    integral_congr_ae (hval.mono fun x hx => by beta_reduce; rw [hx]; rfl)
  refine ⟨hint.congr_fun (fun s _ => hrhs s) measurableSet_Ioc, ?_⟩
  rw [← hL, ← hF, heq]
  exact setIntegral_congr_fun measurableSet_Ioc fun s _ => hrhs s

end AVRegularity.CycleComparison.Coarse
end
end

section
/-! Periodic integration by parts for the jets of a periodic Sobolev field: the jet of order `m`
and word `α`, tested against a `C^m` periodic field `χ`, equals `(-1)^m` times the value tested
against the ordered derivative `∂_{α_0} ⋯ ∂_{α_{m-1}} χ`. -/

@[expose] public noncomputable section

open Homogenization AVenhance MeasureTheory
open AVenhance.Infra.Classical
open AVenhance.Infra.Torus AVenhance.Infra.Parabolic.WeakUniqueness
open AVRegularity.Sobolev

namespace AVRegularity.CycleComparison.Coarse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E]

/-- A jet and its first derivatives, tested against a fixed vector, form a periodic `H¹` pair. -/
theorem torusHk_isPeriodicH1With_at {K : ℕ} (U : TorusHk K E) (j : Fin K)
    (w : DerivativeWord2 j.val) (e : E) :
    IsPeriodicH1With (fun x => inner ℝ e (U.toFunction.jet (lowerIndex2 j w) x))
      (fun x i => inner ℝ e (U.toFunction.jet (nextIndex2 j w i) x)) := by
  have hraw := U.toFunction.hasPeriodicWeakJet
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n x
    change inner ℝ e (U.toFunction.jet _ (x + latticeShift n)) = _
    rw [hraw.1 _ n x]
  · intro n x
    funext i
    change inner ℝ e (U.toFunction.jet _ (x + latticeShift n)) = _
    rw [hraw.1 _ n x]
  · exact (InnerProductSpace.toDual ℝ E e).comp_memLp' (hraw.2.1 _)
  · intro i
    exact (InnerProductSpace.toDual ℝ E e).comp_memLp' (hraw.2.1 _)
  · intro i
    exact hraw.2.2 j w i e

/-- **One step of periodic integration by parts for a jet.** -/
theorem cellInner_nextJet_eq_neg [FiniteDimensional ℝ E] {K : ℕ} (U : TorusHk K E) (j : Fin K)
    (w : DerivativeWord2 j.val) (i : Fin 2) {ψ : Vec 2 → E} (hψ : ContDiff ℝ 1 ψ)
    (hp : IsZ2Periodic ψ) :
    cellInner (U.toFunction.jet (nextIndex2 j w i)) ψ =
      -cellInner (U.toFunction.jet (lowerIndex2 j w)) (fun x => fderiv ℝ ψ x (basisVec i)) := by
  classical
  let b := stdOrthonormalBasis ℝ E
  let D := U.toFunction.jet (nextIndex2 j w i)
  let V := U.toFunction.jet (lowerIndex2 j w)
  have hsum : ∀ v w : E, inner ℝ v w = ∑ k, inner ℝ (b k) v * inner ℝ (b k) w := by
    intro v w
    rw [← b.sum_inner_mul_inner v w]
    exact Finset.sum_congr rfl fun k _ => by rw [real_inner_comm (b k) v]
  let η : Fin (Module.finrank ℝ E) → Vec 2 → ℝ := fun k x => inner ℝ (b k) (ψ x)
  have hη : ∀ k, ContDiff ℝ 1 (η k) := fun k => contDiff_const.inner ℝ hψ
  have hηp : ∀ k, IsZ2Periodic (η k) := fun k n x => by
    change inner ℝ (b k) (ψ (x + latticeShift n)) = _
    rw [hp n x]
  have hdη : ∀ k x, spaceGrad (η k) x i = inner ℝ (b k) (fderiv ℝ ψ x (basisVec i)) :=
    fun k x => fderiv_inner_const_apply hψ (b k) x _
  have hdcont : Continuous (fun x => fderiv ℝ ψ x (basisVec i)) :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcomp : ∀ k, Continuous (fun x => inner ℝ (b k) (fderiv ℝ ψ x (basisVec i))) :=
    fun k => continuous_const.inner hdcont
  have hL1 : ∀ k, Integrable (fun x => inner ℝ (b k) (D x) * η k x)
      (volume.restrict unitCube) := fun k =>
    ((torusHk_isPeriodicH1With_at U j w (b k)).2.2.2.1 i).integrable_mul
      (weak_continuous_memL2On (continuous_const.inner hψ.continuous))
  have hR1 : ∀ k, Integrable (fun x => inner ℝ (b k) (V x) *
      inner ℝ (b k) (fderiv ℝ ψ x (basisVec i))) (volume.restrict unitCube) := fun k =>
    (torusHk_isPeriodicH1With_at U j w (b k)).2.2.1.integrable_mul
      (weak_continuous_memL2On (hcomp k))
  have e1 : (∫ x in unitCube, inner ℝ (D x) (ψ x)) =
      ∑ k, ∫ x in unitCube, inner ℝ (b k) (D x) * η k x := by
    rw [← integral_finsetSum _ (fun k _ => hL1 k)]
    exact integral_congr_ae (ae_of_all _ fun x => hsum (D x) (ψ x))
  have e2 : (∫ x in unitCube, inner ℝ (V x) (fderiv ℝ ψ x (basisVec i))) =
      ∑ k, ∫ x in unitCube, inner ℝ (b k) (V x) *
        inner ℝ (b k) (fderiv ℝ ψ x (basisVec i)) := by
    rw [← integral_finsetSum _ (fun k _ => hR1 k)]
    exact integral_congr_ae (ae_of_all _ fun x => hsum _ _)
  unfold cellInner
  rw [e1, e2, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h := periodicH1_cell_ibp_c1 (torusHk_isPeriodicH1With_at U j w (b k)) (hη k) (hηp k) i
  have h2 : (∫ x in unitCube, inner ℝ (b k) (V x) *
      inner ℝ (b k) (fderiv ℝ ψ x (basisVec i))) =
      -∫ x in unitCube, inner ℝ (b k) (D x) * inner ℝ (b k) (ψ x) := by
    simpa only [hdη] using h
  rw [h2, neg_neg]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
theorem contDiff_orderedDerivativeRev_of {m n : ℕ} (α : DerivativeWord2 m) {χ : Vec 2 → E}
    (hχ : ContDiff ℝ ((m + n : ℕ) : WithTop ℕ∞) χ) :
    ContDiff ℝ (n : WithTop ℕ∞) (AVRegularity.orderedDerivativeRev α χ) := by
  induction m generalizing n χ with
  | zero => simpa [AVRegularity.orderedDerivativeRev] using hχ
  | succ m ih =>
    rw [orderedDerivativeRev_succ]
    refine ih (Fin.init α) (n := n) ?_
    have h1 : ContDiff ℝ ((m + n + 1 : ℕ) : WithTop ℕ∞) χ := by
      have : m + 1 + n = m + n + 1 := by omega
      rw [this] at hχ; exact hχ
    exact (h1.fderiv_right (by exact_mod_cast le_rfl)).clm_apply contDiff_const

/-- **Periodic integration by parts for a jet of order `m`.** -/
theorem cellInner_jet_eq [FiniteDimensional ℝ E] {K : ℕ} (U : TorusHk K E) :
    ∀ {m : ℕ} (hm : m ≤ K) (α : DerivativeWord2 m) {χ : Vec 2 → E},
      ContDiff ℝ (m : WithTop ℕ∞) χ → IsZ2Periodic χ →
      cellInner (U.toFunction.jet ⟨⟨m, Nat.lt_succ_of_le hm⟩, α⟩) χ =
        (-1 : ℝ) ^ m * cellInner (tval U) (AVRegularity.orderedDerivativeRev α χ)
  | 0, _, α, χ, _, _ => by
    have hα : (⟨⟨0, Nat.lt_succ_of_le (Nat.zero_le K)⟩, α⟩ : JetIndex2 K) = valueIndex2 K := by
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        funext z
        exact Fin.elim0 z
    rw [hα]
    simp [tval, AVRegularity.orderedDerivativeRev]
  | m + 1, hm, α, χ, hχ, hp => by
    have hidx : (⟨⟨m + 1, Nat.lt_succ_of_le hm⟩, α⟩ : JetIndex2 K) =
        nextIndex2 (⟨m, by omega⟩ : Fin K) (Fin.init α) (α (Fin.last m)) := by
      unfold nextIndex2 nextIndex
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        exact (Fin.snoc_init_self α).symm
    have h1 : ContDiff ℝ 1 χ := hχ.of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m))
    rw [hidx, cellInner_nextJet_eq_neg U _ _ _ h1 hp]
    have hlow : lowerIndex2 (⟨m, by omega⟩ : Fin K) (Fin.init α) =
        (⟨⟨m, Nat.lt_succ_of_le (by omega)⟩, Fin.init α⟩ : JetIndex2 K) := rfl
    have hχ' : ContDiff ℝ (m : WithTop ℕ∞) (fun x => fderiv ℝ χ x (basisVec (α (Fin.last m)))) :=
      (hχ.fderiv_right (by exact_mod_cast le_rfl)).clm_apply contDiff_const
    have hp' : IsZ2Periodic (fun x => fderiv ℝ χ x (basisVec (α (Fin.last m)))) := by
      intro n x
      have hd : (fun y => χ (y + latticeShift n)) = χ := funext fun y => hp n y
      have := (fderiv_comp_add_right (𝕜 := ℝ) (f := χ) (latticeShift n) :
        fderiv ℝ (fun y => χ (y + latticeShift n)) x = fderiv ℝ χ (x + latticeShift n))
      rw [hd] at this
      change fderiv ℝ χ (x + latticeShift n) _ = fderiv ℝ χ x _
      rw [← this]
    rw [hlow, cellInner_jet_eq U (by omega) (Fin.init α) hχ' hp', orderedDerivativeRev_succ]
    unfold partialOp
    ring

end AVRegularity.CycleComparison.Coarse
end
end

section
/-! Smooth-linear operator structure of the coordinate derivatives and of `covOperator`, and the
commutation `𝒞_H 𝒞_{H'} = 𝒞_{H'} 𝒞_H` of constant-coefficient covariance operators on smooth
fields. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev

namespace AVRegularity.CycleComparison.Coarse

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem contDiff_nat_of_top {f : Vec 2 → E} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) :
    ContDiff ℝ (n : WithTop ℕ∞) f := contDiff_infty.1 hf n

theorem contDiff_top_partialOp {f : Vec 2 → E} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (partialOp i f) :=
  contDiff_infty.2 fun n => contDiff_partialOp (k := n) (contDiff_nat_of_top hf (n + 1)) i

theorem periodic_partialOp {f : Vec 2 → E} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : AVenhance.IsZ2Periodic f) (i : Fin 2) : AVenhance.IsZ2Periodic (partialOp i f) :=
  fun n x => congrArg (fun A => A (basisVec i))
    (fderiv_isZ2Periodic (hf.differentiable (by simp)) hp n x)

theorem SmoothLinOp.comp {T₁ T₂ : (Vec 2 → E) → (Vec 2 → E)} (h₁ : SmoothLinOp T₁)
    (h₂ : SmoothLinOp T₂) : SmoothLinOp (fun f => T₁ (T₂ f)) where
  smooth f hf := h₁.smooth _ (h₂.smooth f hf)
  per f hf hp := h₁.per _ (h₂.smooth f hf) (h₂.per f hf hp)
  lin a f hf := by
    show T₁ (T₂ _) = _
    rw [h₂.lin a f hf]
    exact h₁.lin a (fun k => T₂ (f k)) fun k => h₂.smooth _ (hf k)

theorem smoothLinOp_partialOp (i : Fin 2) : SmoothLinOp (E := E) (partialOp i) where
  smooth f hf := contDiff_top_partialOp hf i
  per f hf hp := periodic_partialOp hf hp i
  lin a f hf := by
    have h1 : ∀ k ∈ (Finset.univ : Finset _), ContDiff ℝ 1 (fun x => a k • f k x) := fun k _ =>
      ((contDiff_nat_of_top (hf k) 1).const_smul (a k))
    rw [partialOp_sum i Finset.univ (fun k x => a k • f k x) h1]
    funext x
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [partialOp_smul i (a k) (contDiff_nat_of_top (hf k) 1)]

theorem smoothLinOp_partialOp_partialOp (i j : Fin 2) :
    SmoothLinOp (E := E) (fun f => partialOp i (partialOp j f)) :=
  (smoothLinOp_partialOp i).comp (smoothLinOp_partialOp j)

theorem smoothLinOp_covOperator (Hc : Matrix (Fin 2) (Fin 2) ℝ) :
    SmoothLinOp (E := E) (AVRegularity.covOperator Hc) where
  smooth f hf := contDiff_infty.2 fun n =>
    contDiff_covOperator Hc (contDiff_nat_of_top hf (n + 2))
  per f hf hp := by
    rw [covOperator_eq]
    intro n x
    simp only [periodic_partialOp (contDiff_top_partialOp hf _) (periodic_partialOp hf hp _) _ n x]
  lin a f hf := by
    have h2 : ∀ k ∈ (Finset.univ : Finset _), ContDiff ℝ 2 (fun x => a k • f k x) := fun k _ =>
      ((contDiff_nat_of_top (hf k) 2).const_smul (a k))
    rw [covOperator_sum Hc Finset.univ (fun k x => a k • f k x) h2]
    funext x
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [covOperator_smul Hc (a k) (contDiff_nat_of_top (hf k) 2)]

/-- Constant-coefficient covariance operators commute on smooth fields. -/
theorem ttCovOperator_comm (H H' : Matrix (Fin 2) (Fin 2) ℝ) {f : Vec 2 → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    AVRegularity.covOperator H (AVRegularity.covOperator H' f) =
      AVRegularity.covOperator H' (AVRegularity.covOperator H f) := by
  have h3 : ContDiff ℝ 3 f := by exact_mod_cast contDiff_nat_of_top hf 3
  have h3j : ∀ j, ContDiff ℝ 3 (partialOp j f) := fun j => by
    have := contDiff_partialOp (k := 3) (contDiff_nat_of_top hf 4) j
    exact_mod_cast this
  have p1 : ∀ j, partialOp j (AVRegularity.covOperator H' f) =
      AVRegularity.covOperator H' (partialOp j f) := fun j => partialOp_covOperator H' j h3
  have p2 : ∀ i j, partialOp i (AVRegularity.covOperator H' (partialOp j f)) =
      AVRegularity.covOperator H' (partialOp i (partialOp j f)) := fun i j =>
    partialOp_covOperator H' i (h3j j)
  have h2ij : ∀ i j, ContDiff ℝ 2 (partialOp i (partialOp j f)) := fun i j => by
    have := contDiff_partialOp (k := 2) (by exact_mod_cast h3j j) i
    exact_mod_cast this
  have e : AVRegularity.covOperator H' (AVRegularity.covOperator H f) =
      fun x => ∑ i, ∑ j, H i j • AVRegularity.covOperator H' (partialOp i (partialOp j f)) x := by
    rw [covOperator_eq H f]
    rw [covOperator_sum H' Finset.univ (fun i x => ∑ j, H i j • partialOp i (partialOp j f) x)
      (fun i _ => ContDiff.sum fun j _ => ContDiff.const_smul _ (h2ij i j))]
    funext x
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [covOperator_sum H' Finset.univ (fun j x => H i j • partialOp i (partialOp j f) x)
      (fun j _ => ContDiff.const_smul _ (h2ij i j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [covOperator_smul H' _ (h2ij i j)]
  rw [e, covOperator_eq H (AVRegularity.covOperator H' f)]
  simp only [p1, p2]

end AVRegularity.CycleComparison.Coarse
end
end
end
