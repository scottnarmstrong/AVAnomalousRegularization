-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import AVRegularity.Analysis.Factorial.Drift
public import AVRegularity.Statements.Intermediate.CoupledEnergy.SchurMatrix

section
@[expose] public section
namespace AVRegularity

/-! Numerical closure of the coupled-energy estimate. -/

/-- Close the supremum and dissipation estimates with the constants used in
the coupled-energy proposition. The input inequalities are the scalar bounds
`S² ≤ Φ + 2SΓ` and `νR ≤ Φ + 2SΓ` from the tested energy identity. -/
theorem coupledEnergyConstants {S Γ Φ ν R : ℝ}
    (hS : S ^ 2 ≤ Φ + 2 * S * Γ)
    (hR : ν * R ≤ Φ + 2 * S * Γ) :
    S ^ 2 + ν / 2 * R ≤ 2 * Φ + 10 * Γ ^ 2 := by
  have hSbound : S ^ 2 ≤ 2 * Φ + 4 * Γ ^ 2 := by
    nlinarith [sq_nonneg (S - 2 * Γ)]
  have hyoung : 3 * S * Γ ≤ (1 / 4 : ℝ) * S ^ 2 + 9 * Γ ^ 2 := by
    nlinarith [sq_nonneg (S - 6 * Γ)]
  calc
    S ^ 2 + ν / 2 * R ≤ (3 / 2 : ℝ) * Φ + 3 * S * Γ := by
      nlinarith
    _ ≤ (3 / 2 : ℝ) * Φ + (1 / 4 : ℝ) * S ^ 2 + 9 * Γ ^ 2 := by
      linarith [hyoung]
    _ ≤ 2 * Φ + 10 * Γ ^ 2 := by
      nlinarith [hSbound]

/-- The flux forcing consumes ν/8 of the gradient square with the exact complementary constant. -/
theorem coupledFluxYoung {ν : ℝ} (hν : 0 < ν) (X Y : ℝ) :
    X * Y ≤ (ν / 8) * Y ^ 2 + (2 / ν) * X ^ 2 := by
  have hcalc : ν * ((ν / 8) * Y ^ 2 + (2 / ν) * X ^ 2 - X * Y) =
      (ν * Y - 4 * X) ^ 2 / 8 := by
    field_simp
    ring
  have hp : 0 ≤ ν * ((ν / 8) * Y ^ 2 + (2 / ν) * X ^ 2 - X * Y) := by
    rw [hcalc]
    exact div_nonneg (sq_nonneg _) (by norm_num)
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hν).mp hp)

end AVRegularity
end
end

section
@[expose] public section
open MeasureTheory Set
namespace AVRegularity

/-! Scalar time integration after the native Galerkin energy chain rule. -/

/-- Conditional calculus helper: integrate a differential energy inequality with a fixed bound S. -/
theorem coupledTimeEnergy_integrated_of_deriv_le {a b ν S : ℝ}
    {E R G F : ℝ → ℝ} (hab : a ≤ b)
    (hE : AbsolutelyContinuousOnInterval E a b)
    (hR : IntervalIntegrable R volume a b)
    (hG : IntervalIntegrable G volume a b)
    (hF : IntervalIntegrable F volume a b)
    (hineq : ∀ᵐ t ∂volume.restrict (Icc a b),
      deriv E t + ν * R t ≤ 2 * S * G t + (4 / ν) * F t) :
    E b + ν * (∫ t in a..b, R t) ≤
      E a + 2 * S * (∫ t in a..b, G t) + (4 / ν) * (∫ t in a..b, F t) := by
  have hmono := intervalIntegral.integral_mono_ae_restrict hab
    (hE.intervalIntegrable_deriv.add (hR.const_mul ν))
    ((hG.const_mul (2 * S)).add (hF.const_mul (4 / ν))) hineq
  rw [intervalIntegral.integral_add hE.intervalIntegrable_deriv (hR.const_mul ν),
    intervalIntegral.integral_add (hG.const_mul (2 * S)) (hF.const_mul (4 / ν)),
    hE.integral_deriv_eq_sub] at hmono
  simp only [intervalIntegral.integral_const_mul] at hmono
  linarith

end AVRegularity
end
end

section
@[expose] public section
open scoped BigOperators
namespace AVRegularity.CoupledEnergy

/-! The paper's integer-power drift budget feeds the factorial commutator estimate. -/

/-- Rewrite the negative integer decay power in the source drift assumption as a reciprocal
natural power. -/
theorem real_zpow_one_sub_nat {ell : ℝ} (_hell : 0 < ell) (l : ℕ) (hl : 1 ≤ l) :
    ell ^ ((1 : ℤ) - l) = 1 / ell ^ (l - 1) := by
  have hexp : (1 : ℤ) - (l : ℤ) = -((l - 1 : ℕ) : ℤ) := by omega
  rw [hexp, zpow_neg, zpow_natCast]
  simp [div_eq_mul_inv]

/-- The derivative-envelope and two smallness assumptions imply the exact
`driftCommutatorAbsorption` estimate for any nonnegative derivative sequence. -/
theorem coupledDriftCommutatorAbsorption {K Kmax : ℕ} {ρ a B ell ν : ℝ}
    (hρ : 0 ≤ ρ) (ha : 0 ≤ a) (hB : 1 ≤ B) (hell : 0 < ell) (hν : 0 < ν)
    (hsmall : B * ρ / ell ≤ 1 / 2) (hstrain : a * B * ρ ^ 2 ≤ ν / 8)
    (hK : K ≤ Kmax)
    (V Y : ℕ → ℝ)
    (hjet : ∀ l : ℕ, 1 ≤ l → l ≤ Kmax →
      V l ≤ a * B ^ l * (l.factorial : ℝ) * ell ^ ((1 : ℤ) - l))
    (hY : ∀ j, 0 ≤ Y j) :
    (∑ j ∈ Finset.range (K + 1),
      AVRegularity.Analysis.Factorial.factorialWeight ρ j ^ 2 *
        ∑ l ∈ (Finset.range (j + 1)).erase 0,
          (j.choose l : ℝ) * V l * Y (j - l + 1) * Y j) ≤
      (ν / 4) * ∑ k ∈ Finset.range (K + 1),
        (AVRegularity.Analysis.Factorial.factorialWeight ρ k * Y (k + 1)) ^ 2 := by
  apply AVRegularity.Analysis.Factorial.driftCommutatorAbsorption
    hρ ha (by linarith) hell hν hsmall hstrain V Y hY
  intro l hl₁ hlK
  have hlMax : l ≤ Kmax := hlK.trans hK
  have hbound := hjet l hl₁ hlMax
  rw [real_zpow_one_sub_nat hell l hl₁] at hbound
  have hrew : 1 / ell ^ (l - 1) = (ell ^ (l - 1))⁻¹ := by ring
  rw [hrew] at hbound
  have htarget : a * B ^ l * (l.factorial : ℝ) * (ell ^ (l - 1))⁻¹ =
      a * B ^ l * (l.factorial : ℝ) / ell ^ (l - 1) := by
    rw [div_eq_mul_inv]
  rw [htarget] at hbound
  exact hbound

end AVRegularity.CoupledEnergy
end
end

section
@[expose] public section
open MeasureTheory Set
namespace AVRegularity

/-! Supremum closure for the scalar differential inequality produced by Galerkin testing. -/

/-- Conditional scalar calculus helper closing the exact constants after the tested equation. -/
theorem coupledTimeEnergy_uniform_of_deriv_le {a b ν : ℝ} {E R G F : ℝ → ℝ}
    (hab : a ≤ b) (hν : 0 < ν) (hE : AbsolutelyContinuousOnInterval E a b)
    (hEn : ∀ t ∈ Icc a b, 0 ≤ E t) (hRn : ∀ t ∈ Icc a b, 0 ≤ R t)
    (hGn : ∀ t ∈ Icc a b, 0 ≤ G t) (hFn : ∀ t ∈ Icc a b, 0 ≤ F t)
    (hR : IntervalIntegrable R volume a b) (hG : IntervalIntegrable G volume a b)
    (hF : IntervalIntegrable F volume a b)
    (hineq : ∀ᵐ t ∂volume.restrict (Icc a b),
      deriv E t + ν * R t ≤ 2 * G t * Real.sqrt (E t) + (4 / ν) * F t) :
    ∃ S : ℝ, 0 ≤ S ∧ (∀ t ∈ Icc a b, E t ≤ S ^ 2) ∧
      S ^ 2 + (ν / 2) * (∫ t in a..b, R t) ≤
        2 * E a + (8 / ν) * (∫ t in a..b, F t) + 10 * (∫ t in a..b, G t) ^ 2 := by
  have hc : ContinuousOn E (Icc a b) := by simpa only [uIcc_of_le hab] using hE.continuousOn
  obtain ⟨tmax, htmax, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨a, le_rfl, hab⟩ hc
  let S := Real.sqrt (E tmax)
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hSq : S ^ 2 = E tmax := Real.sq_sqrt (hEn tmax htmax)
  have hbound : ∀ t ∈ Icc a b, E t ≤ S ^ 2 := fun t ht => (hmax ht).trans_eq hSq.symm
  have hsqrt : ∀ t ∈ Icc a b, Real.sqrt (E t) ≤ S := by
    intro t ht
    exact Real.sqrt_le_sqrt (hmax ht)
  have hglobal : ∀ᵐ t ∂volume.restrict (Icc a b),
      deriv E t + ν * R t ≤ 2 * S * G t + (4 / ν) * F t := by
    filter_upwards [hineq, ae_restrict_mem measurableSet_Icc] with t hi ht
    have hg := mul_le_mul_of_nonneg_left (hsqrt t ht) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hGn t ht))
    nlinarith
  have hsub (t : ℝ) (ht : t ∈ Icc a b) : uIcc a t ⊆ uIcc a b := by
    rw [uIcc_of_le ht.1, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl ht.2
  have hi (t : ℝ) (ht : t ∈ Icc a b) :
      E t + ν * (∫ s in a..t, R s) ≤
        E a + 2 * S * (∫ s in a..t, G s) + (4 / ν) * (∫ s in a..t, F s) := by
    apply coupledTimeEnergy_integrated_of_deriv_le ht.1 (hE.mono (hsub t ht))
      (hR.mono_set (hsub t ht)) (hG.mono_set (hsub t ht)) (hF.mono_set (hsub t ht))
    exact hglobal.filter_mono (ae_mono (Measure.restrict_mono
      (Icc_subset_Icc le_rfl ht.2) le_rfl))
  have hmono (H : ℝ → ℝ) (hH : IntervalIntegrable H volume a b)
      (hHn : ∀ s ∈ Icc a b, 0 ≤ H s) (t : ℝ) (ht : t ∈ Icc a b) :
      (∫ s in a..t, H s) ≤ ∫ s in a..b, H s := by
    apply intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 _ hH
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hHn s (Ioc_subset_Icc_self hs)
  have hRmax : 0 ≤ ∫ t in a..tmax, R t := intervalIntegral.integral_nonneg htmax.1
    (fun t ht => hRn t (Icc_subset_Icc le_rfl htmax.2 ht))
  have hSineq : S ^ 2 ≤ E a + (4 / ν) * (∫ t in a..b, F t) +
      2 * S * (∫ t in a..b, G t) := by
    have hg := mul_le_mul_of_nonneg_left (hmono G hG hGn tmax htmax) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hS0)
    have hf := mul_le_mul_of_nonneg_left (hmono F hF hFn tmax htmax) (by positivity : 0 ≤ 4 / ν)
    rw [hSq]
    nlinarith [hi tmax htmax]
  have hRineq : ν * (∫ t in a..b, R t) ≤ E a + (4 / ν) * (∫ t in a..b, F t) +
      2 * S * (∫ t in a..b, G t) := by
    have hb := hi b ⟨hab, le_rfl⟩
    linarith [hEn b ⟨hab, le_rfl⟩]
  refine ⟨S, hS0, hbound, ?_⟩
  have hclose := coupledEnergyConstants hSineq hRineq
  convert hclose using 1; ring

end AVRegularity
end
end

section
@[expose] public section
noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy

/-! Sign and finite-matrix consequences of the coupled coefficient budget. -/

/-- Every entry of the coupling Schur matrix is nonnegative under the stated
positivity and finite coefficient-seminorm hypotheses. -/
theorem schurMatrix_nonneg {ι : Type*} [Fintype ι]
    {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)]
    (ν ρ : ℝ) (hν : 0 < ν) (hρ : 0 < ρ) (π : ι → ℝ)
    (_hπ : ∀ i, 0 < π i) (K : ι → ℕ) (D : ℕ) (t₀ t₁ : ℝ)
    (A : ∀ (i i' : ι) (d : AVRegularity.admissibleOrders K D i i'),
      ℝ → Vec 2 →
        (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
          (PiLp 2 (fun _ : Fin 2 => h i)))
    (_hA : ∀ i i' d, coefficientSeminorm ρ (K i) t₀ t₁ (A i i' d) ≠ ⊤)
    (i i' : ι) : 0 ≤
      AVRegularity.schurMatrix ν ρ π K D t₀ t₁ A i i' := by
  unfold AVRegularity.schurMatrix
  have hsqrt : 0 ≤ Real.sqrt (π i' / π i) := Real.sqrt_nonneg _
  apply mul_nonneg hsqrt
  apply Finset.sum_nonneg
  intro d hd
  have hseminorm : 0 ≤ (coefficientSeminorm ρ (K i) t₀ t₁ (A i i' d)).toReal :=
    ENNReal.toReal_nonneg
  have hden : 0 < ν * ρ ^ (d.1 - 2) :=
    mul_pos hν (pow_pos hρ _)
  have hfacK : 0 < ((K i).factorial : ℝ) := by positivity
  have hfacTop : 0 < (((K i + d.1 - 2).factorial : ℝ)) := by positivity
  have hratio : 0 <
      (((K i + d.1 - 2).factorial : ℝ) / ((K i).factorial : ℝ)) :=
    div_pos hfacTop hfacK
  have hpiece : 0 ≤
      (coefficientSeminorm ρ (K i) t₀ t₁ (A i i' d)).toReal /
          (ν * ρ ^ (d.1 - 2)) :=
    div_nonneg hseminorm hden.le
  exact mul_nonneg hpiece hratio.le

end AVRegularity.CoupledEnergy
end
end
end
