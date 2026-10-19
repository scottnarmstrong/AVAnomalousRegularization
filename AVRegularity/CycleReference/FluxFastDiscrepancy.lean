-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleReference.ChartTestCalculus
import AVenhance.Infra.Section4.Amnr.StreamProfileJets
import AVRegularity.CycleReference.CoreFlux
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain
import AVenhance.Infra.Section4.IteratesStreamFlux
import AVRegularity.CycleReference.TransitionZero
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.CycleReference.CorrectorMeanGeometry
import AVRegularity.CycleReference.SingleModeFlux
import AVenhance.Infra.Section5.FlowPiolaDivergence
import AVRegularity.CycleReference.MeanEnhancementScale
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

section
@[expose] public section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleReference

/-! All ordered spatial derivatives of a cosine shear. -/

theorem cosine_shear_array_bound (c ω : ℝ) (hω : 0 ≤ ω) (i j : Fin 2) (b : ℕ) (y : Vec 2) :
    derivArrayNorm (fun x : Vec 2 => (c * Real.cos (ω * x i)) • basisVec j) b y ≤
      (2 : ℝ) ^ (b + 1) * (|c| * ω ^ b) := by
  let P : Vec 2 →L[ℝ] ℝ := ω • ContinuousLinearMap.proj i
  let g := fun u : ℝ => (c * Real.cos u) • basisVec j
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := by dsimp [g]; fun_prop
  have hP : ‖P‖ ≤ ω := by
    apply ContinuousLinearMap.opNorm_le_bound _ hω
    intro x
    change ‖ω * x i‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hω]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x i) hω
  have hcos : ‖iteratedFDeriv ℝ b Real.cos (P y)‖ ≤ 1 := by
    simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using
      Real.abs_iteratedDeriv_cos_le_one b (P y)
  have hgj : ‖iteratedFDeriv ℝ b g (P y)‖ ≤ |c| := by
    have he : g = fun u : ℝ => c • (Real.cos u • basisVec j) := by
      funext u
      simp only [g, smul_smul]
    rw [he, iteratedFDeriv_const_smul_apply' (by fun_prop), norm_smul, Real.norm_eq_abs]
    rw [iteratedFDeriv_smul_const_apply (i := b) (x := P y) (v := basisVec j)
      ((Real.contDiff_cos : ContDiff ℝ (⊤ : ℕ∞) Real.cos).contDiffAt.of_le (by simp))]
    have hl := ContinuousLinearMap.norm_compContinuousMultilinearMap_le
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (basisVec j)) (iteratedFDeriv ℝ b Real.cos (P y))
    simp only [ContinuousLinearMap.norm_smulRight_apply, ContinuousLinearMap.norm_id,
      show ‖basisVec j‖ = 1 by simp [basisVec, Pi.norm_single], mul_one, one_mul] at hl
    exact (mul_le_mul_of_nonneg_left (hl.trans hcos) (abs_nonneg c)).trans_eq (mul_one _)
  have hc := AVenhance.Infra.Section4.amnr_iteratedFDeriv_comp_linear_norm_le hg P b y
  have hbound : ‖iteratedFDeriv ℝ b (g ∘ P) y‖ ≤ |c| * ω ^ b :=
    hc.trans (mul_le_mul hgj (pow_le_pow_left₀ (norm_nonneg P) hP b)
      (pow_nonneg (norm_nonneg P) b) (abs_nonneg c))
  have hfull : ContDiff ℝ (⊤ : ℕ∞) (g ∘ P) := hg.comp P.contDiff
  apply derivArrayNorm_le_components (mul_nonneg (abs_nonneg c) (pow_nonneg hω b))
  intro w l
  change |orderedPartial (g ∘ P) b w y l| ≤ _
  rw [orderedPartial_eq_reversed_iteratedFDeriv hfull]
  have ha := (iteratedFDeriv ℝ b (g ∘ P) y).le_opNorm (fun r => basisVec (w r.rev))
  simp only [show ∀ r : Fin b, ‖basisVec (w r.rev)‖ = 1 by
    intro r; simp [basisVec, Pi.norm_single], Finset.prod_const_one, mul_one] at ha
  have hcomp : |(iteratedFDeriv ℝ b (g ∘ P) y (fun r => basisVec (w r.rev))) l| ≤
      ‖iteratedFDeriv ℝ b (g ∘ P) y (fun r => basisVec (w r.rev))‖ := by
    simpa only [Real.norm_eq_abs] using
      norm_le_pi_norm (iteratedFDeriv ℝ b (g ∘ P) y (fun r => basisVec (w r.rev))) l
  exact hcomp.trans (ha.trans hbound)

end AVRegularity.CycleReference
end

section
open Homogenization
open scoped Matrix
namespace AVRegularity.CycleReference

/-! Entrywise instantaneous approximation of the reference flux. -/

theorem ocPi_entry_range (k : {k : ℤ // Odd k}) (i j : Fin 2) :
    ocPi k i j ∈ Set.Icc (0 : ℝ) 1 := by
  fin_cases i <;> fin_cases j <;> by_cases hk : k.1 % 4 = 1 <;> simp [ocPi, hk]

theorem refFlux_entry_instantaneous_error {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (α q : ℝ) (Λ m : ℕ), 1 ≤ Λ → ∀ ν : ℝ, 0 < ν →
    ∀ (t : ℝ) (i j : Fin 2),
      |ocRefFlux α q Λ ζ m ν t i j - ν * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j -
        ocHStar α q Λ m ν * pulseWeightedSquare α q Λ m ζ (fun k => ocPi k i j) t| ≤
      ocHStar α q Λ m ν * (K / (ocMu q Λ m ν * ocTau α q Λ m)) := by
  obtain ⟨K, hK, herror⟩ := pulse_memory_instantaneous_error hζ
  refine ⟨K, hK, ?_⟩
  intro α q Λ m hΛ ν hν t i j
  have hH := ocHStar_pos (α := α) (q := q) (m := m) hΛ hν
  have hμ := ocMu_pos (q := q) (m := m) hΛ hν
  have hτ := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
  by_cases he : ∃ k : {k : ℤ // Odd k}, ζ (t / ocTau α q Λ m - k.1) ≠ 0
  · obtain ⟨k, hk⟩ := he
    have hsum : (∑' j : {j : ℤ // Odd j},
        (ocPulse α q Λ ζ m j.1 t * ocPulseMemory α q Λ ζ m ν j.1 t) • ocPi j) =
        (ocPulse α q Λ ζ m k.1 t * ocPulseMemory α q Λ ζ m ν k.1 t) • ocPi k := by
      apply tsum_eq_single k
      intro j hj
      have hz : ζ (t / ocTau α q Λ m - j.1) = 0 := by
        by_contra hz
        exact hj (Subtype.ext (odd_fast_support_unique hζ j.2 k.2 hz hk))
      rw [ocPulse_eq_scaledProduct hΛ j.1 t, hz]
      simp
    rw [ocRefFlux, hsum, pulseWeightedSquare_single hΛ hζ t _ k hk]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    have hp := ocPulse_range (α := α) (q := q) (Λ := Λ) (m := m) hζ k.1 t
    have hw := ocPi_entry_range k i j
    have herr := herror α q Λ m hΛ ν hν k.1 t
    have hprod : ocHStar α q Λ m ν * ocPulse α q Λ ζ m k.1 t * ocPi k i j ≤
        ocHStar α q Λ m ν := by
      have h := mul_le_mul hp.2 hw.2 hw.1 (by norm_num : (0 : ℝ) ≤ 1)
      simpa only [mul_one, mul_assoc] using mul_le_mul_of_nonneg_left h hH.le
    have hprod0 : 0 ≤ ocHStar α q Λ m ν * ocPulse α q Λ ζ m k.1 t * ocPi k i j :=
      mul_nonneg (mul_nonneg hH.le hp.1) hw.1
    calc
      _ = (ocHStar α q Λ m ν * ocPulse α q Λ ζ m k.1 t * ocPi k i j) *
          |ocPulse α q Λ ζ m k.1 t - ocMu q Λ m ν * ocPulseMemory α q Λ ζ m ν k.1 t| := by
        rw [show ν * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j +
            ocMu q Λ m ν * ocHStar α q Λ m ν *
              ((ocPulse α q Λ ζ m k.1 t * ocPulseMemory α q Λ ζ m ν k.1 t) * ocPi k i j) -
            ν * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j -
            ocHStar α q Λ m ν * (ocPulse α q Λ ζ m k.1 t ^ 2 * ocPi k i j) =
            -(ocHStar α q Λ m ν * ocPulse α q Λ ζ m k.1 t * ocPi k i j) *
              (ocPulse α q Λ ζ m k.1 t - ocMu q Λ m ν * ocPulseMemory α q Λ ζ m ν k.1 t) by ring,
          abs_mul, abs_neg, abs_of_nonneg hprod0]
      _ ≤ _ := mul_le_mul hprod herr (abs_nonneg _) hH.le
  · have hz (k : {k : ℤ // Odd k}) : ζ (t / ocTau α q Λ m - k.1) = 0 := by
      by_contra hk
      exact he ⟨k, hk⟩
    have hp (k : {k : ℤ // Odd k}) : ocPulse α q Λ ζ m k.1 t = 0 := by
      rw [ocPulse_eq_scaledProduct hΛ k.1 t, hz k, mul_zero]
    rw [ocRefFlux, pulseMatrixSum_eq_zero_of_quiet ν t hp]
    simp only [pulseWeightedSquare, hp, zero_pow (by decide : 2 ≠ 0), zero_mul, tsum_zero,
      smul_zero, add_zero, Matrix.smul_apply, smul_eq_mul, sub_self, mul_zero, abs_zero]
    exact mul_nonneg hH.le (div_nonneg hK (mul_pos hμ hτ).le)

end AVRegularity.CycleReference
end

section
open MeasureTheory
namespace AVRegularity.CycleReference

/-! Positivity and monotonicity of every finite reference-diffusivity chain. -/

theorem meanFlux_ge_input {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν) :
    ν ≤ ocMeanFlux α q Λ ζ m ν := by
  let T := 4 * ocTauPP α q Λ m
  have hT : 0 < T := by
    dsimp [T]
    exact mul_pos (by norm_num) (AVRegularity.Construction.Stream.ocTauPP_pos hΛ)
  have hi := refFlux_entry_intervalIntegrable (α := α) (q := q) (m := m)
    hΛ hζ hν (0 : Fin 2) (0 : Fin 2) 0 T
  have hb : ν * T ≤ ∫ t in (0 : ℝ)..T, ocRefFlux α q Λ ζ m ν t 0 0 := by
    have h := intervalIntegral.integral_mono_on hT.le
      (show IntervalIntegrable (fun _ : ℝ => ν) volume 0 T from intervalIntegrable_const)
      hi (fun t _ => refFlux_diagonal_molecular_lower hΛ hζ hν t 0)
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm] using h
  have hm := refFlux_full_period_mean_entry (α := α) (q := q) (m := m)
    hΛ hζ hν (0 : Fin 2) (0 : Fin 2)
  simp only [Matrix.one_apply, ite_true, mul_one] at hm
  change T⁻¹ * (∫ t in (0 : ℝ)..T, ocRefFlux α q Λ ζ m ν t 0 0) = _ at hm
  rw [← hm]
  calc
    ν = T⁻¹ * (ν * T) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (inv_pos.mpr hT).le

theorem band_isClosed (α q : ℝ) (Λ M : ℕ) : IsClosed (ocBand α q Λ M) :=
  isClosed_Icc

theorem bandChain_pos {α q : ℝ} {Λ M : ℕ} {ζ : ℝ → ℝ} {κ : ℕ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (hκ : IsOCBandChain α q Λ ζ M κ) {m : ℕ} (hm : m ≤ M) : 0 < κ m := by
  have hterminal : 0 < κ M := by
    have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := M) hΛ
    exact lt_of_lt_of_le (div_pos (Real.rpow_pos_of_pos he _) (by norm_num)) hκ.1.1
  have hdown : ∀ n : ℕ, n ≤ M → 0 < κ (M - n) := by
    intro n
    induction n with
    | zero => intro _; simpa using hterminal
    | succ n ih =>
      intro hn
      have hp := ih (by omega)
      have heq := hκ.2 (M - n) (by omega) (by omega)
      have hge := meanFlux_ge_input (α := α) (q := q) (m := M - n) hΛ hζ hp
      have hindex : M - n - 1 = M - (n + 1) := by omega
      rw [hindex] at heq
      rw [heq]
      exact hp.trans_le hge
  simpa only [Nat.sub_sub_self hm] using hdown (M - m) (by omega)

theorem bandChain_step_ge {α q : ℝ} {Λ M : ℕ} {ζ : ℝ → ℝ} {κ : ℕ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (hκ : IsOCBandChain α q Λ ζ M κ) {m : ℕ} (hm : 1 ≤ m) (hM : m ≤ M) :
    κ m ≤ κ (m - 1) := by
  rw [hκ.2 m hm hM]
  exact meanFlux_ge_input hΛ hζ (bandChain_pos hΛ hζ hκ hM)

end AVRegularity.CycleReference
end

section
open MeasureTheory Homogenization AVenhance
open scoped Matrix
namespace AVRegularity.CycleReference

/-! Quadratic-form versions of block and long-interval coercivity. -/

theorem refFlux_qform_diagonal {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν) (t : ℝ) (v : Vec 2) :
    vecDot v ((ocRefFlux α q Λ ζ m ν t).mulVec v) =
      ocRefFlux α q Λ ζ m ν t 0 0 * v 0 ^ 2 +
      ocRefFlux α q Λ ζ m ν t 1 1 * v 1 ^ 2 := by
  obtain ⟨h01, h10⟩ := refFlux_diagonal (α := α) (q := q) (m := m) hΛ hζ (ν := ν) (t := t) hν
  simp [vecDot, Matrix.mulVec, dotProduct, Fin.sum_univ_two, h01, h10]
  ring

theorem diagonal_integral_qform_lower {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν) (a b c : ℝ)
    (hc : ∀ i : Fin 2, c ≤ ∫ t in a..b, ocRefFlux α q Λ ζ m ν t i i) (v : Vec 2) :
    c * vecDot v v ≤ ∫ t in a..b, vecDot v ((ocRefFlux α q Λ ζ m ν t).mulVec v) := by
  have hi (i : Fin 2) := refFlux_entry_intervalIntegrable (α := α) (q := q) (m := m) hΛ hζ hν i i a b
  have he : (∫ t in a..b, vecDot v ((ocRefFlux α q Λ ζ m ν t).mulVec v)) =
      (∫ t in a..b, ocRefFlux α q Λ ζ m ν t 0 0) * v 0 ^ 2 +
      (∫ t in a..b, ocRefFlux α q Λ ζ m ν t 1 1) * v 1 ^ 2 := by
    calc
      _ = ∫ t in a..b, (ocRefFlux α q Λ ζ m ν t 0 0 * v 0 ^ 2 +
          ocRefFlux α q Λ ζ m ν t 1 1 * v 1 ^ 2) := by
        apply intervalIntegral.integral_congr
        intro t _
        exact refFlux_qform_diagonal hΛ hζ hν t v
      _ = _ := by
        rw [intervalIntegral.integral_add ((hi 0).mul_const _) ((hi 1).mul_const _),
          intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
  rw [he]
  have h0 := mul_le_mul_of_nonneg_right (hc 0) (sq_nonneg (v 0))
  have h1 := mul_le_mul_of_nonneg_right (hc 1) (sq_nonneg (v 1))
  simp only [vecDot, Fin.sum_univ_two]
  nlinarith

theorem refFlux_block_qform_lower {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (hrelax : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m) (l : ℤ) (v : Vec 2) :
    (ν + (1 - Real.exp (-2)) / 96 * ocHStar α q Λ m ν) * ocTauPP α q Λ m * vecDot v v ≤
      ∫ t in (((l : ℝ) - 1 / 2) * ocTauPP α q Λ m)..
        (((l : ℝ) + 1 / 2) * ocTauPP α q Λ m), vecDot v ((ocRefFlux α q Λ ζ m ν t).mulVec v) :=
  diagonal_integral_qform_lower hΛ hζ hν _ _ _
    (refFlux_block_diagonal_lower hΛ hζ hν hrelax l) v

theorem refFlux_long_qform_lower {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (hrelax : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m) (s t : ℝ)
    (hst : 3 * ocTauPP α q Λ m ≤ t - s) (v : Vec 2) :
    (1 - Real.exp (-2)) / 96 / 3 * ocMeanFlux α q Λ ζ m ν * (t - s) * vecDot v v ≤
      ∫ r in s..t, vecDot v ((ocRefFlux α q Λ ζ m ν r).mulVec v) := by
  apply diagonal_integral_qform_lower hΛ hζ hν
  intro i
  let c := (1 - Real.exp (-2)) / 96 * ocMeanFlux α q Λ ζ m ν
  have hB := (refFlux_mean_core_bounds hΛ hζ hν hrelax).2
  have hν := hν
  have hH := (ocHStar_pos (α := α) (q := q) (m := m) hΛ hν).le
  have hb : ∀ l : ℤ, c * ocTauPP α q Λ m ≤ ∫ r in
      (((l : ℝ) - 1 / 2) * ocTauPP α q Λ m)..
      (((l : ℝ) + 1 / 2) * ocTauPP α q Λ m), ocRefFlux α q Λ ζ m ν r i i := by
    intro l
    apply le_trans _ (refFlux_block_diagonal_lower hΛ hζ hν hrelax l i)
    apply mul_le_mul_of_nonneg_right _ (AVRegularity.Construction.Stream.ocTauPP_pos hΛ).le
    have hcν := mul_le_mul_of_nonneg_right core_coercivity_constant_range.2 hν.le
    have hcb := mul_le_mul_of_nonneg_left hB core_coercivity_constant_range.1.le
    dsimp [c]
    linarith
  have hmeanpos : 0 ≤ ocMeanFlux α q Λ ζ m ν :=
    (mul_nonneg core_coercivity_constant_range.1.le (by linarith)).trans
      (refFlux_mean_core_bounds hΛ hζ hν hrelax).1
  have hc : 0 ≤ c := mul_nonneg core_coercivity_constant_range.1.le hmeanpos
  have hl := long_interval_block_lower _ _ c (AVRegularity.Construction.Stream.ocTauPP_pos hΛ) hc
    (refFlux_entry_intervalIntegrable hΛ hζ hν i i)
    (fun r => hν.le.trans (refFlux_diagonal_molecular_lower hΛ hζ hν r i)) hb s t hst
  dsimp [c] at hl
  convert hl using 1
  ring

end AVRegularity.CycleReference
end

section
open Homogenization AVenhance Filter Topology
namespace AVRegularity.CycleReference

/-! The exact switching-defect identity for the glued reference corrector. -/

theorem refCorrector_equation {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν t : ℝ) (y : Vec 2) (j : Fin 2) :
    deriv (fun s => ocRefCorrector α q Λ ζ m ν s y j) t
      - ν * ∑ i : Fin 2, fderiv ℝ
          (fun z => fderiv ℝ (fun x => ocRefCorrector α q Λ ζ m ν t x j)
            z (basisVec i)) y (basisVec i)
      + ∑ i : Fin 2, streamVel (ocPulseStream α q Λ ζ m) t y i *
          fderiv ℝ (fun z => ocRefCorrector α q Λ ζ m ν t z j) y (basisVec i)
      + streamVel (ocPulseStream α q Λ ζ m) t y j =
        ∑' k : {k : ℤ // Odd k}, deriv (ocCutoff α q Λ m k.1) t *
          ocPulseCorrector α q Λ ζ m ν k.1 t y j := by
  classical
  obtain ⟨S, hS⟩ := cutoff_locally_finite hΛ t
  have hzero (k : {k : ℤ // Odd k}) (hk : k ∉ S) :
      ocCutoff α q Λ m k.1 =ᶠ[𝓝 t] fun _ => 0 := by
    filter_upwards [hS] with s hs
    exact hs k hk
  have hzero_t (k : {k : ℤ // Odd k}) (hk : k ∉ S) : ocCutoff α q Λ m k.1 t = 0 :=
    (hzero k hk).eq_of_nhds
  have hzero_d (k : {k : ℤ // Odd k}) (hk : k ∉ S) : deriv (ocCutoff α q Λ m k.1) t = 0 := by
    rw [(hzero k hk).deriv_eq]
    exact deriv_const _ _
  have hlocal : (fun s => ocRefCorrector α q Λ ζ m ν s y j) =ᶠ[𝓝 t]
      fun s => ∑ k ∈ S, ocCutoff α q Λ m k.1 s * ocPulseCorrector α q Λ ζ m ν k.1 s y j := by
    filter_upwards [hS] with s hs
    have hsum : ocRefCorrector α q Λ ζ m ν s y =
        ∑ k ∈ S, ocCutoff α q Λ m k.1 s • ocPulseCorrector α q Λ ζ m ν k.1 s y := by
      unfold ocRefCorrector
      apply tsum_eq_sum
      intro k hk
      rw [hs k hk, zero_smul]
    rw [hsum]
    simp [Pi.smul_apply, smul_eq_mul]
  have htime : deriv (fun s => ocRefCorrector α q Λ ζ m ν s y j) t =
      ∑ k ∈ S, (deriv (ocCutoff α q Λ m k.1) t * ocPulseCorrector α q Λ ζ m ν k.1 t y j +
        ocCutoff α q Λ m k.1 t *
          (-(ocPulse α q Λ ζ m k.1 t - ocMu q Λ m ν * ocPulseMemory α q Λ ζ m ν k.1 t) *
            ocShearVel α q Λ m k.1 y j)) := by
    rw [hlocal.deriv_eq]
    apply HasDerivAt.deriv
    apply HasDerivAt.fun_sum
    intro k hk
    exact ((ocCutoff_contDiff hΛ k.1).differentiable (by simp) t).hasDerivAt.mul
      (pulseCorrector_hasDerivAt hΛ hζ ν k.1 t y j)
  have hres : (∑' k : {k : ℤ // Odd k}, deriv (ocCutoff α q Λ m k.1) t *
      ocPulseCorrector α q Λ ζ m ν k.1 t y j) =
      ∑ k ∈ S, deriv (ocCutoff α q Λ m k.1) t * ocPulseCorrector α q Λ ζ m ν k.1 t y j := by
    apply tsum_eq_sum
    intro k hk
    rw [hzero_d k hk, zero_mul]
  have hval : ocRefCorrector α q Λ ζ m ν t y j =
      ∑ k ∈ S, ocCutoff α q Λ m k.1 t * ocPulseCorrector α q Λ ζ m ν k.1 t y j :=
    hlocal.eq_of_nhds
  have hforcing : (∑ k ∈ S, ocCutoff α q Λ m k.1 t * ocPulse α q Λ ζ m k.1 t *
      ocShearVel α q Λ m k.1 y j) = streamVel (ocPulseStream α q Λ ζ m) t y j := by
    by_cases hp : ∃ k : ℤ, Odd k ∧ ocPulse α q Λ ζ m k t ≠ 0
    · obtain ⟨k, hk, hp⟩ := hp
      have hkS : (⟨k, hk⟩ : {k : ℤ // Odd k}) ∈ S := by
        by_contra hn
        have hz := hzero_t ⟨k, hk⟩ hn
        rw [ocCutoff_eq_one_of_pulse_ne_zero hΛ hζ hp] at hz
        norm_num at hz
      rw [Finset.sum_eq_single ⟨k, hk⟩]
      · rw [ocCutoff_eq_one_of_pulse_ne_zero hΛ hζ hp,
          pulseStreamVel_eq_active hΛ hζ hk hp y]
        simp
      · intro a ha hne
        have hp0 : ocPulse α q Λ ζ m a.1 t = 0 := by
          by_contra han
          have heq := odd_pulse_support_unique hΛ hζ a.2 hk han hp
          exact hne (Subtype.ext heq)
        rw [hp0, mul_zero, zero_mul]
      · exact fun hn => (hn hkS).elim
    · have hp0 : ∀ k : ℤ, Odd k → ocPulse α q Λ ζ m k t = 0 := by
        intro k hk
        by_contra hne
        exact hp ⟨k, hk, hne⟩
      rw [pulseStreamVel_eq_zero_of_quiet hp0]
      change (∑ k ∈ S, _) = 0
      apply Finset.sum_eq_zero
      intro k hk
      rw [hp0 k.1 k.2, mul_zero, zero_mul]
  have hμ : ocMu q Λ m ν = ν * (2 * Real.pi * (ocEpsilon q Λ m)⁻¹) ^ 2 := by
    unfold ocMu
    field_simp
    ring
  rw [refCorrector_laplacian hΛ, pulseStream_transport_refCorrector_zero hΛ hζ,
    htime, hres, ← hforcing, hval]
  have hterm (k : {k : ℤ // Odd k}) :
      ocCutoff α q Λ m k.1 t *
        (-(ocPulse α q Λ ζ m k.1 t - ocMu q Λ m ν * ocPulseMemory α q Λ ζ m ν k.1 t) *
          ocShearVel α q Λ m k.1 y j) =
        -(ocCutoff α q Λ m k.1 t * ocPulse α q Λ ζ m k.1 t * ocShearVel α q Λ m k.1 y j) -
          ocMu q Λ m ν * (ocCutoff α q Λ m k.1 t * ocPulseCorrector α q Λ ζ m ν k.1 t y j) := by
    simp only [ocPulseCorrector, Pi.smul_apply, smul_eq_mul]
    ring
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  simp_rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
  rw [hμ]
  ring

end AVRegularity.CycleReference
end

section
open Homogenization AVenhance MeasureTheory
open scoped Matrix
namespace AVRegularity.CycleReference

/-! The weak drift equals the flux of the antisymmetric stream coefficient. -/

theorem rotated_gradient_smooth {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => sigmaMat.mulVec (spaceGrad f x)) := by
  have hg : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => spaceGrad f x i) := by
    intro i
    exact (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · simpa [sigmaMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using (hg 1).neg
  · simpa [sigmaMat, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using hg 0

theorem rotated_gradient_compact {f : Vec 2 → ℝ} (hc : HasCompactSupport f) :
    HasCompactSupport (fun x => sigmaMat.mulVec (spaceGrad f x)) := by
  have hd := hc.fderiv ℝ
  apply hd.comp_left
    (g := fun L : Vec 2 →L[ℝ] ℝ => sigmaMat.mulVec (fun i => L (basisVec i)))
  ext i
  fin_cases i <;> simp

theorem rotated_gradient_div_zero {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Vec 2) :
    vecDiv (fun y => sigmaMat.mulVec (spaceGrad f y)) x = 0 := by
  have he := Infra.Section4.iterate_stream_flux_divergence contDiff_const hf x
    (φ := fun _ => (1 : ℝ))
  simpa [spaceGrad, fderiv_const, Matrix.mulVec, dotProduct, vecDot] using he

theorem spaceGrad_mul {f g : Vec 2 → ℝ} {x : Vec 2}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    spaceGrad (fun y => f y * g y) x = f x • spaceGrad g x + g x • spaceGrad f x := by
  ext i
  unfold spaceGrad
  change (fderiv ℝ (f * g) x) (basisVec i) = _
  rw [(hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv]
  simp only [add_apply, smul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem weak_stream_flux_pairing {u ψ η : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (hu : LocallyIntegrable u volume) (hDu : ∀ i, LocallyIntegrable (fun x => Du x i) volume)
    (hw : HasWeakGradientOn Set.univ u Du)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hc : HasCompactSupport η) :
    ∫ x, vecDot ((ψ x • sigmaMat).mulVec (Du x)) (spaceGrad η x) =
      ∫ x, vecDot (sigmaMat.mulVec (spaceGrad ψ x)) (Du x) * η x := by
  let g := fun x => ψ x * η x
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := hψ.mul hη
  have hgc : HasCompactSupport g := hc.mul_left
  have hz := weakGradient_vector_test hu hDu hw
    (fun x => sigmaMat.mulVec (spaceGrad g x))
    (rotated_gradient_smooth hg) (rotated_gradient_compact hgc)
  simp_rw [← vecDiv_eq_sum_fderiv, rotated_gradient_div_zero hg] at hz
  simp only [mul_zero, integral_zero] at hz
  have he (x : Vec 2) : vecDot (Du x) (sigmaMat.mulVec (spaceGrad g x)) =
      vecDot (sigmaMat.mulVec (spaceGrad ψ x)) (Du x) * η x -
        vecDot ((ψ x • sigmaMat).mulVec (Du x)) (spaceGrad η x) := by
    rw [show spaceGrad g x = _ from spaceGrad_mul
      (hψ.differentiable (by simp) x) (hη.differentiable (by simp) x)]
    simp [vecDot, Matrix.mulVec, dotProduct, Fin.sum_univ_two, sigmaMat]
    ring
  have hfirst : Integrable (fun x => vecDot (sigmaMat.mulVec (spaceGrad ψ x)) (Du x) * η x) volume := by
    have hp := rotated_gradient_smooth hψ
    have hi (i : Fin 2) := locallyIntegrable_mul_test (hDu i)
      (((contDiff_apply ℝ ℝ i).comp hp).continuous.mul hη.continuous)
      (hc.mul_left)
    convert integrable_finsetSum Finset.univ (fun i _ => hi i) using 1
    funext x
    simp [vecDot, Fin.sum_univ_two, Matrix.mulVec, dotProduct]
    ring
  have hsecond : Integrable (fun x => vecDot ((ψ x • sigmaMat).mulVec (Du x)) (spaceGrad η x)) volume := by
    have hp := rotated_gradient_smooth hη
    have hpc := rotated_gradient_compact hc
    have hi (i : Fin 2) := locallyIntegrable_mul_test (hDu i)
      (hψ.continuous.mul ((contDiff_apply ℝ ℝ i).comp hp).continuous)
      ((hpc.comp_left (g := fun v : Vec 2 => v i) rfl).mul_left)
    have hs := integrable_finsetSum Finset.univ (fun i _ => hi i)
    convert hs.neg using 1
    funext x
    simp [vecDot, Fin.sum_univ_two, sigmaMat, Matrix.mulVec, dotProduct]
    ring
  simp_rw [he] at hz
  rw [integral_sub hfirst hsecond] at hz
  linarith

end AVRegularity.CycleReference
end

section
open Homogenization AVenhance AVenhance.Infra.Section5
namespace AVRegularity.CycleReference

/-! Smoothness of the planar cofactor entries. -/

theorem rowCofactor_smooth {M : Vec 2 → Vec 2} (hM : ContDiff ℝ (⊤ : ℕ∞) M)
    (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => rowCofactor (gradMatrix M x) i j) := by
  have hd := hM.differentiable (by simp)
  have he (a b : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun x => gradMatrix M x a b) := by
    have hh (x : Vec 2) := congrArg (fun A => A b a) (jacMatrix_eq_gradMatrix_transpose hd x)
    simpa only [Matrix.transpose_apply, hh] using jacMatrix_entry_smooth hM b a
  fin_cases i <;> fin_cases j
  · change ContDiff ℝ (⊤ : ℕ∞) (fun x => rowCofactor (gradMatrix M x) 0 0)
    simp_rw [FlowPiolaDivergence.rowCofactor_00]
    exact he 1 1
  · change ContDiff ℝ (⊤ : ℕ∞) (fun x => rowCofactor (gradMatrix M x) 0 1)
    simp_rw [FlowPiolaDivergence.rowCofactor_01]
    exact (he 1 0).neg
  · change ContDiff ℝ (⊤ : ℕ∞) (fun x => rowCofactor (gradMatrix M x) 1 0)
    simp_rw [FlowPiolaDivergence.rowCofactor_10]
    exact (he 0 1).neg
  · change ContDiff ℝ (⊤ : ℕ∞) (fun x => rowCofactor (gradMatrix M x) 1 1)
    simp_rw [FlowPiolaDivergence.rowCofactor_11]
    exact he 0 0

end AVRegularity.CycleReference
end

section
open MeasureTheory
open scoped Matrix
namespace AVRegularity.CycleReference

/-! The bare fast orientation has a uniformly bounded centered primitive. -/

theorem fast_entry_primitive {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (i j : Fin 2) :
    ∃ b ∈ Set.Icc (0 : ℝ) 1,
      (∀ a : ℝ, (∫ t in a..(a + 4 * ocTauPP α q Λ m),
        fastWeightedSquare ζ (ocTau α q Λ m) (fun k => ocPi k i j) t - b) = 0) ∧
      (∀ a c : ℝ, |∫ t in a..c,
        fastWeightedSquare ζ (ocTau α q Λ m) (fun k => ocPi k i j) t - b| ≤
          8 * ocTau α q Λ m) := by
  let τ := ocTau α q Λ m
  let f := fastWeightedSquare ζ τ (fun k => ocPi k i j)
  have hτ : 0 < τ := AVRegularity.Construction.Stream.ocTau_pos hΛ
  have hp : Function.Periodic f (4 * τ) := fastWeightedSquare_periodic ζ hτ
    (fun k => congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A i j)
      (ocPi_add_mod4zero k 4 (by decide) (by decide)))
  have hi := fastWeightedSquare_intervalIntegrable hζ τ (fun k => ocPi_entry_range k i j)
  obtain ⟨b, hb, hm, _hprim⟩ := periodic_centered_average (by positivity : 0 < 4 * τ) hp hi
    (fun t => fastWeightedSquare_range hζ τ t (fun k => ocPi_entry_range k i j))
  have hper : Function.Periodic (fun t => f t - b) (4 * τ) := by
    intro t
    change f (t + 4 * τ) - b = f t - b
    rw [hp t]
  have hii (a c : ℝ) : IntervalIntegrable (fun t => f t - b) volume a c :=
    (hi a c).sub intervalIntegrable_const
  have hscale : (ocL α q Λ m : ℝ) ^ 2 * τ = ocTauPP α q Λ m := by
    dsimp [τ]
    rw [ocTau]
    have hL : (ocL α q Λ m : ℝ) ≠ 0 := by
      have hn : 0 < ocL α q Λ m := by unfold ocL; omega
      exact_mod_cast hn.ne'
    field_simp
  refine ⟨b, hb, ?_, ?_⟩
  · intro a
    have h := hper.intervalIntegral_add_zsmul_eq ((ocL α q Λ m : ℤ) ^ 2) a hii
    have hzero : (∫ t in a..(a + 4 * τ), f t - b) = 0 := by
      rw [hper.intervalIntegral_add_eq a 0, zero_add]
      simpa only [Int.cast_one, one_mul] using hm 1
    rw [hzero] at h
    simp only [zsmul_eq_mul, mul_zero] at h
    push_cast at h
    have he : (ocL α q Λ m : ℝ) ^ 2 * (4 * τ) = 4 * ocTauPP α q Λ m := by
      rw [← hscale]; ring
    simpa only [he] using h
  · intro a c
    have hf (t : ℝ) : |f t - b| ≤ 1 := by
      have hr := fastWeightedSquare_range hζ τ t (fun k => ocPi_entry_range k i j)
      rw [abs_le]
      constructor <;> linarith only [hr.1, hr.2, hb.1, hb.2]
    have hz : (∫ t in (0 : ℝ)..(4 * τ), f t - b) = 0 := by
      simpa only [Int.cast_one, one_mul] using hm 1
    have h := periodic_zero_mean_integral_bound (by positivity : 0 < 4 * τ)
      (by norm_num : (0 : ℝ) ≤ 1) hper hii hz hf a c
    convert h using 1; ring

end AVRegularity.CycleReference
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleReference

/-! The uniform switching-tail estimate, with the physical normalization. -/

theorem shear_amplitude_eq {α q : ℝ} {Λ m : ℕ} (hΛ : 1 ≤ Λ) :
    2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) * (ocEpsilon q Λ m)⁻¹ =
      2 * Real.pi * ocA α q Λ m * ocEpsilon q Λ m := by
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos
    (q := q) (Λ := Λ) (n := m) hΛ
  unfold ocA
  rw [Real.rpow_sub he, Real.rpow_two]
  field_simp

theorem pulseCorrector_scaled_norm_le {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (k : ℤ) (hk : Odd k) (t d : ℝ) (y : Vec 2) :
    Real.sqrt (vecNormSq (d • ocPulseCorrector α q Λ ζ m ν k t y)) ≤
      |d| * ocPulseMemory α q Λ ζ m ν k t *
        (2 * Real.pi * ocA α q Λ m * ocEpsilon q Λ m) := by
  let A := 2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) * (ocEpsilon q Λ m)⁻¹
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos
    (q := q) (Λ := Λ) (n := m) hΛ
  have hA : 0 < A := by dsimp [A]; positivity
  have hM : 0 ≤ ocPulseMemory α q Λ ζ m ν k t :=
    (ocPulseMemory_range hΛ hζ ν hν k t).1
  have hnorm : ∃ z : ℝ, Real.sqrt (vecNormSq (d • ocPulseCorrector α q Λ ζ m ν k t y)) =
      |d| * ocPulseMemory α q Λ ζ m ν k t * A * |Real.cos z| := by
    rcases odd_int_mod_four hk with h1 | h3
    · refine ⟨2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y 0, ?_⟩
      simp only [ocPulseCorrector, ocShearVel_horizontal h1,
        vecNormSq, vecDot, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, zero_add]
      rw [← pow_two, Real.sqrt_sq_eq_abs]
      simp only [abs_mul, abs_neg, abs_of_nonneg hM,
        abs_of_pos Real.pi_pos, abs_of_pos (Real.rpow_pos_of_pos he _),
        abs_of_pos (inv_pos.mpr he)]
      dsimp [A]
      ring
    · refine ⟨2 * Real.pi * (ocEpsilon q Λ m)⁻¹ * y 1, ?_⟩
      simp only [ocPulseCorrector, ocShearVel_vertical h3,
        vecNormSq, vecDot, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, add_zero]
      rw [← pow_two, Real.sqrt_sq_eq_abs]
      simp only [abs_mul, abs_neg, abs_of_nonneg hM,
        abs_of_pos Real.pi_pos, abs_of_pos (Real.rpow_pos_of_pos he _),
        abs_of_pos (inv_pos.mpr he)]
      dsimp [A]
      ring
  obtain ⟨z, hz⟩ := hnorm
  rw [hz, ← shear_amplitude_eq hΛ]
  change |d| * ocPulseMemory α q Λ ζ m ν k t * A * |Real.cos z| ≤
    |d| * ocPulseMemory α q Λ ζ m ν k t * A
  exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one z)
    (by positivity)).trans_eq (mul_one _)

theorem switching_residual_bound {α q : ℝ} {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, ∀ Λ : ℕ, 1 ≤ Λ → ∀ m : ℕ, ∀ ν : ℝ, 0 < ν → ∀ t : ℝ, ∀ y : Vec 2,
      Real.sqrt (vecNormSq (∑' k : {k : ℤ // Odd k}, deriv (ocCutoff α q Λ m k.1) t •
        ocPulseCorrector α q Λ ζ m ν k.1 t y)) ≤
        C * ocA α q Λ m * ocEpsilon q Λ m / (ocMu q Λ m ν * ocTau α q Λ m) *
          Real.exp (-(ocMu q Λ m ν) * ocTau α q Λ m / 12) := by
  obtain ⟨K, hK, hbound⟩ := cutoff_derivative_uniform_bound
  refine ⟨2 * Real.pi * K, ?_⟩
  intro Λ hΛ m ν hν t y
  have hμ := ocMu_pos (q := q) (m := m) hΛ hν
  have hτ := AVRegularity.Construction.Stream.ocTau_pos
    (α := α) (q := q) (Λ := Λ) (m := m) hΛ
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos
    (q := q) (Λ := Λ) (n := m) hΛ
  have ha : 0 < ocA α q Λ m := by unfold ocA; positivity
  classical
  by_cases hactive : ∃ k : {k : ℤ // Odd k}, deriv (ocCutoff α q Λ m k.1) t •
      ocPulseCorrector α q Λ ζ m ν k.1 t y ≠ 0
  · obtain ⟨k, hk⟩ := hactive
    rw [switching_residual_single hΛ hζ ν t y k hk]
    have ht := (switching_nonzero_falling hΛ hζ ν k.1 t y hk).1.le
    have hdecay := pulseMemory_quiet_tail hΛ hζ hν k.1 t ht
    have hd := hbound α q Λ m hΛ k.1 t
    calc
      _ ≤ |deriv (ocCutoff α q Λ m k.1) t| * ocPulseMemory α q Λ ζ m ν k.1 t *
          (2 * Real.pi * ocA α q Λ m * ocEpsilon q Λ m) :=
        pulseCorrector_scaled_norm_le hΛ hζ hν k.1 k.2 t _ y
      _ ≤ (K / ocTau α q Λ m) *
          ((ocMu q Λ m ν)⁻¹ * Real.exp (-(ocMu q Λ m ν) * ocTau α q Λ m / 12)) *
          (2 * Real.pi * ocA α q Λ m * ocEpsilon q Λ m) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul hd hdecay (ocPulseMemory_range hΛ hζ ν hν k.1 t).1 (by positivity)
      _ = _ := by field_simp
  · have hz (k : {k : ℤ // Odd k}) : deriv (ocCutoff α q Λ m k.1) t •
        ocPulseCorrector α q Λ ζ m ν k.1 t y = 0 := by
      by_contra hk
      exact hactive ⟨k, hk⟩
    simp_rw [hz]
    simp only [tsum_zero, vecNormSq, vecDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
      Real.sqrt_zero]
    positivity

end AVRegularity.CycleReference
end

section
open Homogenization AVenhance MeasureTheory
namespace AVRegularity.CycleReference

/-! Integration by parts for a smooth divergence-free drift and weak H¹ data. -/

/-- Coordinate product rule, adapted from upstream `vecDiv_scalar_mul`. -/
theorem vecDiv_scalar_mul {η : Vec 2 → ℝ} {B : Vec 2 → Vec 2}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hB : ContDiff ℝ (⊤ : ℕ∞) B) (x : Vec 2) :
    vecDiv (fun y => η y • B y) x =
      vecDot (spaceGrad η x) (B x) + η x * vecDiv B x := by
  have he (i : Fin 2) : spaceGrad (fun y => (η y • B y) i) x i =
      η x * spaceGrad (fun y => B y i) x i + B x i * spaceGrad η x i := by
    have hb := ((contDiff_apply ℝ ℝ i).comp hB).differentiable (by simp) x
    have h := spaceGrad_mul (hη.differentiable (by simp) x) hb
    exact congrFun h i
  unfold vecDiv vecDot
  simp_rw [he]
  simp [Fin.sum_univ_two]
  ring

theorem weak_divFree_drift_pairing {u η : Vec 2 → ℝ} {Du B : Vec 2 → Vec 2}
    (hu : LocallyIntegrable u volume) (hDu : ∀ i, LocallyIntegrable (fun x => Du x i) volume)
    (hw : HasWeakGradientOn Set.univ u Du)
    (hB : ContDiff ℝ (⊤ : ℕ∞) B) (hdiv : ∀ x, vecDiv B x = 0)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η) :
    ∫ x, vecDot (B x) (Du x) * η x =
      -∫ x, u x * vecDot (B x) (spaceGrad η x) := by
  have hz := weakGradient_vector_test hu hDu hw (fun x => η x • B x)
    (hη.smul hB) hc.smul_right
  simp_rw [← vecDiv_eq_sum_fderiv, vecDiv_scalar_mul hη hB, hdiv,
    mul_zero, add_zero] at hz
  have hleft (x : Vec 2) : vecDot (spaceGrad η x) (B x) =
      vecDot (B x) (spaceGrad η x) := by
    simp [vecDot, mul_comm]
  have hright (x : Vec 2) : vecDot (Du x) (η x • B x) =
      vecDot (B x) (Du x) * η x := by
    simp [vecDot, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
    ring
  simp_rw [hleft, hright] at hz
  linarith

end AVRegularity.CycleReference
end

section
open Homogenization AVenhance AVenhance.Infra.Section5
namespace AVRegularity.CycleReference

/-! Compact scalar tests transported by the cofactor of an inverse chart. -/

noncomputable def piolaTest (Y : Vec 2 → Vec 2) (η : Vec 2 → ℝ) (j : Fin 2) : Vec 2 → Vec 2 :=
  fun x i => rowCofactor (gradMatrix Y x) i j * η (Y x)

theorem piolaTest_smooth {Y : Vec 2 → Vec 2} (hY : ContDiff ℝ (⊤ : ℕ∞) Y)
    {η : Vec 2 → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (piolaTest Y η j) := by
  apply contDiff_pi.2
  intro i
  exact (rowCofactor_smooth hY i j).mul (hη.comp hY)

theorem piolaTest_compact (Y : Vec 2 ≃ₜ Vec 2)
    {η : Vec 2 → ℝ} (hc : HasCompactSupport η) (j : Fin 2) :
    HasCompactSupport (piolaTest Y η j) := by
  apply (hc.comp_homeomorph Y).mono'
  intro x hx
  by_contra h
  have hη : η (Y x) = 0 := (show (η ∘ Y) x = 0 from image_eq_zero_of_notMem_tsupport h)
  have hv : piolaTest Y η j x = 0 := by
    ext i
    simp [piolaTest, hη]
  exact hx hv

theorem piolaTest_divergence {Y : Vec 2 → Vec 2} (hY : ContDiff ℝ (⊤ : ℕ∞) Y)
    (hd : ∀ x, (jacMatrix Y x).det = 1)
    {η : Vec 2 → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (j : Fin 2) (x : Vec 2) :
    vecDiv (piolaTest Y η j) x = fderiv ℝ η (Y x) (basisVec j) := by
  let g : Vec 2 → Vec 2 := fun y => η y • basisVec j
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := hη.smul contDiff_const
  have hfun : piolaTest Y η j = fun y =>
      (jacMatrix Y y)⁻¹.mulVec (g (Y y)) := by
    funext y i
    rw [← rowCofactor_eq_jacMatrix_inverse (hY.differentiable (by simp)) y (hd y)]
    fin_cases j <;> simp [piolaTest, g, Matrix.mulVec, dotProduct, Fin.sum_univ_two, basisVec]
  rw [hfun, inverse_jacobian_piola hY hg hd]
  rw [vecDiv_eq_sum_fderiv]
  have he (i : Fin 2) : (fun y => g y i) = fun y => η y * basisVec j i := by
    funext y
    simp [g]
  simp_rw [he]
  fin_cases j <;> simp [Fin.sum_univ_two, basisVec]

end AVRegularity.CycleReference
end
end
end

section
@[expose] public section
open Homogenization AVenhance
open scoped Matrix
namespace AVRegularity.CycleReference

/-! The scalar, gradient, vector-flux and metric pullbacks of a fixed-start chart. -/

noncomputable def chartPull {E : Type*} {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) (f : ℝ → Vec 2 → E) : ℝ → Vec 2 → E :=
  fun t y => f t (AVRegularity.streamFlow φ hφ t y s)

noncomputable def chartJac {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s t : ℝ) (y : Vec 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  jacMatrix (fun x => AVRegularity.streamFlow φ hφ t x s) y

noncomputable def chartGradient {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) (D : ℝ → Vec 2 → Vec 2) : ℝ → Vec 2 → Vec 2 :=
  fun t y => (chartJac hφ s t y)ᵀ.mulVec (chartPull hφ s D t y)

noncomputable def chartVector {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) (v : ℝ → Vec 2 → Vec 2) : ℝ → Vec 2 → Vec 2 :=
  fun t y => (chartJac hφ s t y)⁻¹.mulVec (chartPull hφ s v t y)

noncomputable def chartMetric {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s t : ℝ) (y : Vec 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  (chartJac hφ s t y)⁻¹ * ((chartJac hφ s t y)⁻¹)ᵀ

theorem planeWeakIntegrand_chart_pullback {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s ν : ℝ)
    (b q : ℝ → Vec 2 → Vec 2) (f θ : ℝ → Vec 2 → ℝ) (Dθ : ℝ → Vec 2 → Vec 2)
    (η : ℝ → Vec 2 → ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => η p.1 p.2)) (t : ℝ) (y : Vec 2) :
    planeWeakIntegrand (chartVector hφ s (fun r x => b r x - streamVel φ r x))
      (fun r x => ν • chartMetric hφ s r x) (chartVector hφ s q)
      (chartPull hφ s f) (chartPull hφ s θ) (chartGradient hφ s Dθ) (chartPull hφ s η) (t, y) =
    planeWeakIntegrand b (fun _ _ => ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)) q f θ Dθ η
      (t, AVRegularity.streamFlow φ hφ t y s) -
      (chartPull hφ s θ t y * vecDot (chartPull hφ s (streamVel φ) t y)
        (chartPull hφ s (fun r x => spaceGrad (η r) x) t y) +
      vecDot (chartPull hφ s (streamVel φ) t y) (chartPull hφ s Dθ t y) * chartPull hφ s η t y) := by
  have ht := streamFlow_test_time_chain hφ s t y hη
  have hs : DifferentiableAt ℝ (η t) (AVRegularity.streamFlow φ hφ t y s) :=
    (hη.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) _
  have hg := spaceGrad_comp_jacMatrix hs
    ((streamFlow_spatial_smooth hφ t s).differentiable (by simp) y)
  have hF : IsUnit (chartJac hφ s t y).det := by
    rw [chartJac, streamFlow_jacMatrix_det_one hφ]
    exact isUnit_one
  unfold planeWeakIntegrand chartVector chartGradient chartMetric chartPull
  dsimp only
  rw [ht, hg]
  exact material_integrand_algebra _ hF _ _ _ _ _ _ _ _ _ _

end AVRegularity.CycleReference
end
end

section
@[expose] public section
namespace AVRegularity.CycleReference

/-! Scale substitution in the reference mean-enhancement bound. -/

theorem slow_quiet_margin_ratio_le {α q : ℝ} {Λ m : ℕ} (hΛ : 1 ≤ Λ) :
    4 * ocTauP α q Λ m / ocTauPP α q Λ m ≤
      ocEpsilon q Λ (m - 1) ^ ocDelta α q := by
  let e := ocEpsilon q Λ (m - 1)
  let d := ocDelta α q
  let L : ℝ := ocL α q Λ m
  have he : 0 < e := AVRegularity.Construction.Stream.ocEpsilon_pos hΛ
  have hL : 0 < L := by
    have hn : 0 < ocL α q Λ m := by unfold ocL; omega
    dsimp [L]
    exact_mod_cast hn
  have hc : e ^ (-d) ≤ (⌈e ^ (-d)⌉₊ : ℝ) := Nat.le_ceil _
  have hfour : 4 * e ^ (-d) ≤ L := by
    dsimp [L, ocL, e, d] at *
    push_cast
    linarith only [hc]
  have hcancel : e ^ (-d) * e ^ d = 1 := by rw [← Real.rpow_add he]; simp
  have hmul := mul_le_mul_of_nonneg_right hfour (Real.rpow_pos_of_pos he d).le
  have hscaled : 4 ≤ L * e ^ d := by
    calc
      4 = (4 * e ^ (-d)) * e ^ d := by rw [mul_assoc, hcancel, mul_one]
      _ ≤ _ := hmul
  have hh := AVRegularity.Construction.Stream.ocTauPP_pos (α := α) (q := q) (m := m) hΛ
  have hratio : 4 * ocTauP α q Λ m / ocTauPP α q Λ m = 4 / L := by
    unfold ocTauP
    dsimp [L]
    field_simp
  rw [hratio]
  apply (div_le_iff₀ hL).mpr
  simpa only [mul_comm] using hscaled

theorem refFlux_mean_enhancement {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, ∀ (α q : ℝ) (Λ m : ℕ), 1 ≤ Λ → ∀ ν : ℝ, 0 < ν →
      |ocMeanFlux α q Λ ζ m ν - ν - 9 / 80 * ocEpsilon q Λ m ^ (2 * (1 + α)) / ν| ≤
        C * (ocEpsilon q Λ m ^ (2 * (1 + α)) / ν) *
          (ocEpsilon q Λ m ^ 2 / (ν * ocTau α q Λ m) +
            ocEpsilon q Λ (m - 1) ^ ocDelta α q) := by
  obtain ⟨K, hK, hb⟩ := refFlux_mean_enhancement_scale hζ
  let c := K / (16 * Real.pi ^ 2)
  refine ⟨c + 1, ?_⟩
  intro α q Λ m hΛ ν hν
  let S := ocEpsilon q Λ m ^ (2 * (1 + α)) / ν
  let R := ocEpsilon q Λ m ^ 2 / (ν * ocTau α q Λ m)
  let E := ocEpsilon q Λ (m - 1) ^ ocDelta α q
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  have hτ := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
  have hS : 0 ≤ S := (div_pos (Real.rpow_pos_of_pos he _) hν).le
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hE : 0 ≤ E := Real.rpow_nonneg (AVRegularity.Construction.Stream.ocEpsilon_pos hΛ).le _
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hH : 0 ≤ ocHStar α q Λ m ν / 2 := (div_pos (ocHStar_pos hΛ hν) (by norm_num)).le
  have htarget : (9 / 40 : ℝ) * ocHStar α q Λ m ν =
      9 / 80 * ocEpsilon q Λ m ^ (2 * (1 + α)) / ν := by unfold ocHStar; ring
  rw [← htarget]
  apply (hb α q Λ m hΛ ν hν).trans
  have hquietMargin := mul_le_mul_of_nonneg_left
    (slow_quiet_margin_ratio_le (α := α) (q := q) (m := m) hΛ) hH
  have hmem : ocHStar α q Λ m ν / 2 * (K / (ocMu q Λ m ν * ocTau α q Λ m)) = c * S * R := by
    dsimp [ocHStar, ocMu, c, S, R]
    field_simp
    ring
  have hslow : ocHStar α q Λ m ν / 2 * E = (1 / 4 : ℝ) * S * E := by
    dsimp [ocHStar, S]
    ring
  calc
    _ = c * S * R + ocHStar α q Λ m ν / 2 * (4 * ocTauP α q Λ m / ocTauPP α q Λ m) := by
      rw [mul_add, hmem]
    _ ≤ c * S * R + (1 / 4 : ℝ) * S * E := by
      rw [← hslow]
      exact add_le_add le_rfl hquietMargin
    _ ≤ (c + 1) * S * R + (c + 1) * S * E := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hS) hR
      · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith only [hc]) hS) hE
    _ = _ := by dsimp [S, R, E]; ring

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open Homogenization
namespace AVRegularity.CycleReference

/-! All spatial derivative arrays of a scaled reference shear. -/

theorem scaled_shear_array_bound {α q : ℝ} {Λ m : ℕ} (hΛ : 1 ≤ Λ)
    (k : ℤ) (hk : Odd k) (c : ℝ) (b : ℕ) (y : Vec 2) :
    derivArrayNorm (fun x => c • ocShearVel α q Λ m k x) b y ≤
      (2 : ℝ) ^ (b + 1) * (|c| *
        (2 * Real.pi * ocEpsilon q Λ m ^ α) *
          (2 * Real.pi * (ocEpsilon q Λ m)⁻¹) ^ b) := by
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  let A := 2 * Real.pi * ocEpsilon q Λ m ^ α
  let ω := 2 * Real.pi * (ocEpsilon q Λ m)⁻¹
  have hA : 0 < A := by dsimp [A]; positivity
  have hω : 0 < ω := by dsimp [ω]; positivity
  have hamp : 2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) * (ocEpsilon q Λ m)⁻¹ = A := by
    dsimp [A]
    rw [mul_assoc, ← div_eq_mul_inv, ← Real.rpow_sub_one he.ne']
    congr 2
    ring
  have hmod : k % 4 = 1 ∨ k % 4 = 3 := by
    rcases hk with ⟨l, hl⟩
    have hn := Int.emod_nonneg k (b := 4) (by norm_num)
    have hu := Int.emod_lt k (b := 4) (by norm_num)
    omega
  rcases hmod with h1 | h3
  · have hf : (fun x => c • ocShearVel α q Λ m k x) =
        fun x : Vec 2 => (c * A * Real.cos (ω * x 0)) • basisVec 1 := by
      funext x
      rw [ocShearVel_horizontal h1 x, hamp]
      ext i
      fin_cases i <;> simp [basisVec, ω, smul_eq_mul, mul_assoc]
    rw [hf]
    have hb := cosine_shear_array_bound (c * A) ω hω.le 0 1 b y
    rw [abs_mul, abs_of_pos hA] at hb
    exact hb
  · have hf : (fun x => c • ocShearVel α q Λ m k x) =
        fun x : Vec 2 => (-c * A * Real.cos (ω * x 1)) • basisVec 0 := by
      funext x
      rw [ocShearVel_vertical h3 x, hamp]
      ext i
      fin_cases i <;> simp [basisVec, ω, smul_eq_mul, mul_assoc]
    rw [hf]
    have hb := cosine_shear_array_bound (-c * A) ω hω.le 1 0 b y
    rw [abs_mul, abs_neg, abs_of_pos hA] at hb
    exact hb

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open Homogenization AVenhance AVenhance.Infra.Section5 MeasureTheory
open scoped Matrix
namespace AVRegularity.CycleReference

/-! Weak gradients transported by a smooth volume-preserving chart. -/

theorem weakGradient_homeomorph_piola (X : Vec 2 ≃ₜ Vec 2)
    (hX : MeasurePreserving X volume volume)
    (hY : ContDiff ℝ (⊤ : ℕ∞) (X.symm : Vec 2 → Vec 2))
    (hd : ∀ x, (jacMatrix (X.symm : Vec 2 → Vec 2) x).det = 1)
    {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (hu : LocallyIntegrable u volume) (hDu : ∀ i, LocallyIntegrable (fun x => Du x i) volume)
    (hw : HasWeakGradientOn Set.univ u Du) :
    HasWeakGradientOn Set.univ (fun y => u (X y))
      (fun y => (rowCofactor (gradMatrix (X.symm : Vec 2 → Vec 2) (X y)))ᵀ.mulVec (Du (X y))) := by
  intro j η hη hc _
  simp only [Measure.restrict_univ]
  let V := piolaTest (X.symm : Vec 2 → Vec 2) η j
  have hs : ContDiff ℝ (⊤ : ℕ∞) V := piolaTest_smooth hY hη j
  have hsc : HasCompactSupport V := piolaTest_compact X.symm hc j
  have he := weakGradient_vector_test hu hDu hw V hs hsc
  have hdiv (x : Vec 2) : (∑ i : Fin 2, fderiv ℝ (fun y => V y i) x (basisVec i)) =
      fderiv ℝ η (X.symm x) (basisVec j) :=
    piolaTest_divergence hY hd hη j x
  simp_rw [hdiv] at he
  have hleft := hX.integral_comp X.measurableEmbedding
    (fun x => u x * fderiv ℝ η (X.symm x) (basisVec j))
  have hright := hX.integral_comp X.measurableEmbedding
    (fun x => vecDot (Du x) (V x))
  simp only [X.symm_apply_apply] at hleft
  have hp (y : Vec 2) : vecDot (Du (X y)) (V (X y)) =
      ((rowCofactor (gradMatrix (X.symm : Vec 2 → Vec 2) (X y)))ᵀ.mulVec (Du (X y))) j * η y := by
    simp only [V, piolaTest, X.symm_apply_apply, vecDot, Matrix.mulVec, dotProduct,
      Matrix.transpose_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hleft, he, ← hright]
  simp_rw [hp]

end AVRegularity.CycleReference
end
end

section
@[expose] public section
open MeasureTheory
open scoped Matrix
namespace AVRegularity.CycleReference

/-! A full renewal cycle discrepancy from the bare fast flux. -/

theorem refFlux_fast_cycle_discrepancy {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (α q : ℝ) (Λ m : ℕ), 1 ≤ Λ → ∀ ν : ℝ, 0 < ν →
    ∀ i j : Fin 2,
      (∫ t in (-ocTauPP α q Λ m / 2)..(-ocTauPP α q Λ m / 2 + 4 * ocTauPP α q Λ m),
        |ocRefFlux α q Λ ζ m ν t i j -
          (ν * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j + ocHStar α q Λ m ν *
            fastWeightedSquare ζ (ocTau α q Λ m) (fun k => ocPi k i j) t)|) ≤
      ocHStar α q Λ m ν *
        (4 * ocTauPP α q Λ m * (K / (ocMu q Λ m ν * ocTau α q Λ m)) +
          16 * ocTauP α q Λ m) := by
  obtain ⟨K, hK, herr⟩ := refFlux_entry_instantaneous_error hζ
  refine ⟨K, hK, ?_⟩
  intro α q Λ m hΛ ν hν i j
  let H := ocHStar α q Λ m ν
  let h := ocTauPP α q Λ m
  let g := fun t => fastSquareSum ζ (ocTau α q Λ m) t - pulseSquareSum α q Λ ζ m t
  let R := K / (ocMu q Λ m ν * ocTau α q Λ m)
  let F := fun t => ν * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j + H *
    fastWeightedSquare ζ (ocTau α q Λ m) (fun k => ocPi k i j) t
  have hH : 0 < H := ocHStar_pos hΛ hν
  have hh : 0 < h := AVRegularity.Construction.Stream.ocTauPP_pos hΛ
  have hτ := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
  have hF (a b : ℝ) : IntervalIntegrable F volume a b := intervalIntegrable_const.add
    ((fastWeightedSquare_intervalIntegrable hζ _ (fun k => ocPi_entry_range k i j) a b).const_mul H)
  have hg (a b : ℝ) : IntervalIntegrable g volume a b :=
    (fastSquareSum_intervalIntegrable hζ hτ a b).sub (pulseSquareSum_intervalIntegrable hΛ hζ a b)
  have hbound (t : ℝ) : |ocRefFlux α q Λ ζ m ν t i j - F t| ≤ H * (R + g t) := by
    have hw := weightedSquare_discrepancy (α := α) (q := q) (m := m) hΛ hζ (fun k => ocPi_entry_range k i j) t
    have he := herr α q Λ m hΛ ν hν t i j
    have hsplit : ocRefFlux α q Λ ζ m ν t i j - F t =
        (ocRefFlux α q Λ ζ m ν t i j - ν * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j -
          H * pulseWeightedSquare α q Λ m ζ (fun k => ocPi k i j) t) +
        H * (pulseWeightedSquare α q Λ m ζ (fun k => ocPi k i j) t -
          fastWeightedSquare ζ (ocTau α q Λ m) (fun k => ocPi k i j) t) := by dsimp [F]; ring
    rw [hsplit]
    have hw' := mul_le_mul_of_nonneg_left hw hH.le
    rw [← abs_of_pos hH, ← abs_mul, abs_of_pos hH] at hw'
    have he' := add_le_add he hw'
    exact (abs_add_le _ _).trans (by dsimp [H, R, g] at *; convert he' using 1; ring)
  have hi (a b : ℝ) :=
    ((refFlux_entry_intervalIntegrable (α := α) (q := q) (m := m) hΛ hζ hν i j a b).sub (hF a b)).abs
  have hmono := intervalIntegral.integral_mono_on (by linarith : -h / 2 ≤ -h / 2 + 4 * h)
    (hi _ _) ((intervalIntegrable_const.add (hg _ _)).const_mul H) (fun t _ => hbound t)
  have hcalc : (∫ t in (-h / 2)..(-h / 2 + 4 * h), H * (R + g t)) =
      H * (4 * h * R + ∫ t in (-h / 2)..(-h / 2 + 4 * h), g t) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add intervalIntegrable_const (hg _ _), intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [hcalc] at hmono
  exact hmono.trans (mul_le_mul_of_nonneg_left
    (add_le_add (le_refl (4 * h * R))
      (square_quiet_margin_cycle_bound (α := α) (q := q) (m := m) hΛ hζ)) hH.le)

end AVRegularity.CycleReference
end
end
