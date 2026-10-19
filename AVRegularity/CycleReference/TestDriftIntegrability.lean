-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleReference.TransitionZero
import AVRegularity.Velocity.Jets.OCData
public import AVRegularity.Definitions.CycleReference.OcRefCorrector
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.CycleReference.PlaneCoefficientCongruence
import AVRegularity.CycleReference.SpacetimeGradientPairing
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.Monotonicity.Lemmas

section
@[expose] public section

section
open MeasureTheory
namespace AVRegularity.CycleReference

/-! Zero history and the quantitative memory tail after a quiet delay. -/

theorem pulseMemory_zero_before {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (k : ℤ) (t : ℝ)
    (ht : t ≤ ((k : ℝ) - 2 / 3) * ocTau α q Λ m) :
    ocPulseMemory α q Λ ζ m ν k t = 0 := by
  unfold ocPulseMemory
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro r hr
  have hp : ocPulse α q Λ ζ m k (t - r) = 0 := by
    by_contra hne
    have hh := (pulse_nonzero_center_distance hΛ hζ hne).1
    have hr' : 0 < r := hr
    linarith
  rw [hp, mul_zero]

theorem pulseMemory_quiet_tail {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (k : ℤ) (t : ℝ) (ht : ((k : ℝ) + 3 / 4) * ocTau α q Λ m ≤ t) :
    ocPulseMemory α q Λ ζ m ν k t ≤
      (ocMu q Λ m ν)⁻¹ * Real.exp (-(ocMu q Λ m ν) * ocTau α q Λ m / 12) := by
  let μ := ocMu q Λ m ν
  let d := ocTau α q Λ m / 12
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos
    (q := q) (Λ := Λ) (n := m) hΛ
  have hμ : 0 < μ := by dsimp [μ, ocMu]; positivity
  have hd : 0 < d := by
    dsimp [d]
    exact div_pos (AVRegularity.Construction.Stream.ocTau_pos hΛ) (by norm_num)
  let g : ℝ → ℝ := (Set.Ioi d).indicator (fun r => Real.exp (-μ * r))
  have hg : Integrable g := by
    unfold g
    rw [integrable_indicator_iff measurableSet_Ioi]
    exact integrableOn_exp_mul_Ioi (by linarith) d
  have hupper : ocPulseMemory α q Λ ζ m ν k t ≤ ∫ r, g r := by
    unfold ocPulseMemory
    rw [← integral_indicator measurableSet_Ioi]
    apply integral_mono_of_nonneg
    · filter_upwards [] with r
      by_cases hr : 0 < r
      · simp only [Set.indicator, Set.mem_Ioi, ite_eq_left hr]
        exact mul_nonneg (Real.exp_pos _).le (ocPulse_range hζ k (t - r)).1
      · simp [Set.indicator, Set.mem_Ioi, hr]
    · exact hg
    · filter_upwards [] with r
      by_cases hr : 0 < r
      · by_cases hrd : d < r
        · simp only [g, Set.indicator, Set.mem_Ioi, ite_eq_left hr, ite_eq_left hrd]
          exact (mul_le_mul_of_nonneg_left (ocPulse_range hζ k (t - r)).2
            (Real.exp_pos _).le).trans_eq (mul_one _)
        · have hp : ocPulse α q Λ ζ m k (t - r) = 0 := by
            by_contra hp
            have hsupport := (pulse_nonzero_center_distance hΛ hζ hp).2
            have hrd' : r ≤ ocTau α q Λ m / 12 := le_of_not_gt hrd
            linarith
          simp [Set.indicator, Set.mem_Ioi, hr, hp, g, hrd]
      · have hrd : ¬d < r := by linarith
        simp [Set.indicator, Set.mem_Ioi, hr, g, hrd]
  calc
    ocPulseMemory α q Λ ζ m ν k t ≤ ∫ r, g r := hupper
    _ = μ⁻¹ * Real.exp (-μ * d) := by
      rw [show g = (Set.Ioi d).indicator (fun r => Real.exp (-μ * r)) by rfl,
        integral_indicator measurableSet_Ioi,
        integral_exp_mul_Ioi (by linarith : -μ < 0)]
      simp
      ring
    _ = _ := by dsimp [μ, d]; congr 2; ring

end AVRegularity.CycleReference
end

section
namespace AVRegularity.CycleReference

/-! Each renewal block has the required number of complete cores in either orientation. -/

theorem complete_cores_exist {α q : ℝ} {Λ m : ℕ} (hΛ : 1 ≤ Λ) (l r : ℤ)
    (hr : r = 1 ∨ r = 3) :
    ∃ S : Finset ℤ, (ocL α q Λ m : ℝ) ^ 2 / 32 ≤ S.card ∧
      ∀ k ∈ S, k % 4 = r ∧ IsOCCompleteCore α q Λ m l k := by
  let N := ⌈ocEpsilon q Λ (m - 1) ^ (-ocDelta α q)⌉₊
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos
    (q := q) (Λ := Λ) (n := m - 1) hΛ
  have hN : 1 ≤ N := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos he _)
  have hL : ocL α q Λ m = 4 * N + 1 := rfl
  have hLr : (ocL α q Λ m : ℝ) = 4 * (N : ℝ) + 1 := by rw [hL]; push_cast; rfl
  have hLn : 0 < (ocL α q Λ m : ℝ) := by rw [hLr]; positivity
  let τ := ocTau α q Λ m
  let L : ℝ := ocL α q Λ m
  have hτ : 0 < τ := AVRegularity.Construction.Stream.ocTau_pos hΛ
  have hPP : ocTauPP α q Λ m = L ^ 2 * τ := by
    dsimp [τ, L]
    rw [ocTau]
    field_simp
  have hP : ocTauP α q Λ m = L * τ := by
    rw [ocTauP, hPP]
    dsimp [L]
    field_simp
  obtain ⟨S, hcard, hS⟩ := residue_core_slots N hN l r hr
  refine ⟨S, ?_, ?_⟩
  · rw [hLr, hcard]
    exact core_count_square_bound N hN
  · intro k hk
    obtain ⟨hmod, hodd, hlo, hhi⟩ := hS k hk
    refine ⟨hmod, completeCore_of_plateau hΛ l k hodd ?_ ?_ ?_⟩
    all_goals
      have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have hlow : -2 * (N : ℝ) ^ 2 + 1 ≤ (k : ℝ) - (l : ℝ) * L ^ 2 := by
        dsimp [L]
        rw [hLr]
        exact_mod_cast hlo
      have hhigh : (k : ℝ) - (l : ℝ) * L ^ 2 ≤ 2 * (N : ℝ) ^ 2 := by
        dsimp [L]
        rw [hLr]
        exact_mod_cast hhi
      have hmargin : 2 * (N : ℝ) ^ 2 + 1 / 3 ≤ L ^ 2 / 2 - 2 * L := by
        dsimp [L]
        rw [hLr]
        nlinarith [sq_nonneg ((N : ℝ) - 1)]
      have hLm : 5 ≤ L := by dsimp [L]; rw [hLr]; linarith
      have hlmul := mul_le_mul_of_nonneg_right hlow hτ.le
      have hhmul := mul_le_mul_of_nonneg_right hhigh hτ.le
      have hmmul := mul_le_mul_of_nonneg_right hmargin hτ.le
    · apply ocLabel_eq_of_center hΛ l k
      · rw [hPP]
        nlinarith
      · rw [hPP]
        nlinarith
    · rw [hPP, hP]
      change _ ≤ ((k : ℝ) - 1 / 3) * τ
      nlinarith
    · rw [hPP, hP]
      change ((k : ℝ) + 1 / 3) * τ ≤ _
      nlinarith

end AVRegularity.CycleReference
end

section
open Filter Topology
namespace AVRegularity.CycleReference

/-! Uniform cutoff derivative bound and its quiet transition support. -/

noncomputable def glueProfile (x : ℝ) : ℝ := Real.smoothTransition (5 / 2 - 2 * |x|)

theorem glueProfile_contDiff : ContDiff ℝ (⊤ : ℕ∞) glueProfile := by
  have heq : glueProfile = fun x =>
      Real.smoothTransition (5 / 2 - 2 * x) * Real.smoothTransition (5 / 2 + 2 * x) :=
    funext smoothTransition_abs_eq_mul
  rw [heq]
  fun_prop

theorem glueProfile_hasCompactSupport : HasCompactSupport glueProfile := by
  apply IsCompact.of_isClosed_subset
    (isCompact_Icc (a := -(5 / 4 : ℝ)) (b := 5 / 4)) isClosed_closure
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have ha : 0 < 5 / 2 - 2 * |x| := by
    by_contra ha
    exact hx (Real.smoothTransition.zero_of_nonpos (le_of_not_gt ha))
  have hdist : |x| < 5 / 4 := by linarith
  exact ⟨(abs_lt.mp hdist).1.le, (abs_lt.mp hdist).2.le⟩

theorem ocCutoff_eq_glueProfile {α q : ℝ} {Λ m : ℕ} (hΛ : 1 ≤ Λ) (k : ℤ) :
    ocCutoff α q Λ m k = fun t =>
      glueProfile ((t - (k : ℝ) * ocTau α q Λ m) / ocTau α q Λ m) := by
  funext t
  have hτ := AVRegularity.Construction.Stream.ocTau_pos
    (α := α) (q := q) (Λ := Λ) (m := m) hΛ
  unfold ocCutoff glueProfile
  rw [abs_div, abs_of_pos hτ]
  congr 1
  ring

theorem cutoff_derivative_uniform_bound : ∃ K : ℝ, 0 < K ∧
    ∀ (α q : ℝ) (Λ m : ℕ), 1 ≤ Λ → ∀ k : ℤ, ∀ t : ℝ,
      |deriv (ocCutoff α q Λ m k) t| ≤ K / ocTau α q Λ m := by
  have hcont : Continuous (deriv glueProfile) :=
    glueProfile_contDiff.continuous_deriv (by simp)
  obtain ⟨B, hB⟩ := hcont.norm.bddAbove_range_of_hasCompactSupport
    glueProfile_hasCompactSupport.deriv.norm
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro α q Λ m hΛ k t
  have hτ := AVRegularity.Construction.Stream.ocTau_pos
    (α := α) (q := q) (Λ := Λ) (m := m) hΛ
  have hinner : HasDerivAt (fun s : ℝ => (s - (k : ℝ) * ocTau α q Λ m) / ocTau α q Λ m)
      (ocTau α q Λ m)⁻¹ t := by
    convert ((hasDerivAt_id t).sub_const ((k : ℝ) * ocTau α q Λ m)).div_const
      (ocTau α q Λ m) using 1 <;> simp [one_div]
  have hd := (glueProfile_contDiff.differentiable (by simp) _).hasDerivAt.comp t hinner
  have hd' : deriv (fun s => glueProfile ((s - (k : ℝ) * ocTau α q Λ m) / ocTau α q Λ m)) t =
      deriv glueProfile ((t - (k : ℝ) * ocTau α q Λ m) / ocTau α q Λ m) *
        (ocTau α q Λ m)⁻¹ := by
    simpa only [Function.comp_def] using hd.deriv
  rw [ocCutoff_eq_glueProfile hΛ k, hd', abs_mul, abs_of_pos (inv_pos.mpr hτ)]
  have hb : |deriv glueProfile ((t - (k : ℝ) * ocTau α q Λ m) / ocTau α q Λ m)| ≤ B := by
    exact hB (Set.mem_range_self _)
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (hb.trans (le_max_left _ _)) (inv_nonneg.mpr hτ.le)

theorem cutoff_derivative_nonzero_distance {α q : ℝ} {Λ m : ℕ}
    (hΛ : 1 ≤ Λ) (k : ℤ) (t : ℝ) (hd : deriv (ocCutoff α q Λ m k) t ≠ 0) :
    3 / 4 * ocTau α q Λ m < |t - (k : ℝ) * ocTau α q Λ m| ∧
      |t - (k : ℝ) * ocTau α q Λ m| < 5 / 4 * ocTau α q Λ m := by
  have hτ := AVRegularity.Construction.Stream.ocTau_pos
    (α := α) (q := q) (Λ := Λ) (m := m) hΛ
  have hne0 : ocCutoff α q Λ m k t ≠ 0 := by
    intro hz
    apply hd
    apply IsLocalMin.deriv_eq_zero
    filter_upwards [] with s
    rw [hz]
    exact Real.smoothTransition.nonneg _
  have hne1 : ocCutoff α q Λ m k t ≠ 1 := by
    intro hz
    apply hd
    apply IsLocalMax.deriv_eq_zero
    filter_upwards [] with s
    rw [hz]
    exact Real.smoothTransition.le_one _
  have ha0 : 0 < 5 / 2 - 2 * |t - (k : ℝ) * ocTau α q Λ m| / ocTau α q Λ m := by
    by_contra ha
    exact hne0 (Real.smoothTransition.zero_of_nonpos (le_of_not_gt ha))
  have ha1 : 5 / 2 - 2 * |t - (k : ℝ) * ocTau α q Λ m| / ocTau α q Λ m < 1 := by
    by_contra ha
    exact hne1 (Real.smoothTransition.one_of_one_le (le_of_not_gt ha))
  have hlo : 3 / 2 < 2 * |t - (k : ℝ) * ocTau α q Λ m| / ocTau α q Λ m := by linarith
  have hhi : 2 * |t - (k : ℝ) * ocTau α q Λ m| / ocTau α q Λ m < 5 / 2 := by linarith
  have hhlo := (lt_div_iff₀ hτ).mp hlo
  have hhhi := (div_lt_iff₀ hτ).mp hhi
  constructor <;> linarith

end AVRegularity.CycleReference
end

section
namespace AVRegularity.CycleReference

/-! Only the current block label contributes to a material pulse. -/

theorem pulse_label_on_block {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) {l k : ℤ} {t : ℝ}
    (ht : ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ t ∧
      t ≤ ((l : ℝ) + 1 / 2) * ocTauPP α q Λ m)
    (hp : ocPulse α q Λ ζ m k t ≠ 0) : ocLabel α q Λ m k = l := by
  have hs : slowEnvelope α q Λ m (ocLabel α q Λ m k) t ≠ 0 := by
    intro hz
    apply hp
    simp [ocPulse, hz]
  have hP := AVRegularity.Velocity.Jets.ocTauP_pos (α := α) (q := q) (Λ := Λ) (m := m) hΛ
  have hh := AVRegularity.Construction.Stream.ocTauPP_pos (α := α) (q := q) (Λ := Λ) (m := m) hΛ
  have hw := AVRegularity.Velocity.Jets.slow_support_window hP hs
  by_contra h
  rcases lt_or_gt_of_ne h with hlo | hhi
  · have hi : ocLabel α q Λ m k + 1 ≤ l := by omega
    have hi' : (ocLabel α q Λ m k : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast hi
    have hb := mul_le_mul_of_nonneg_right hi' hh.le
    nlinarith only [hb, hw.2, ht.1, hP]
  · have hi : l + 1 ≤ ocLabel α q Λ m k := by omega
    have hi' : (l : ℝ) + 1 ≤ (ocLabel α q Λ m k : ℝ) := by exact_mod_cast hi
    have hb := mul_le_mul_of_nonneg_right hi' hh.le
    nlinarith only [hb, hw.1, ht.2, hP]

end AVRegularity.CycleReference
end

section
open MeasureTheory
open Homogenization
open scoped Matrix
namespace AVRegularity.CycleReference

/-! Finite-slot reductions and matrix positivity for the reference flux. -/

def oddSlotAddEquiv (K : ℤ) (hK : Even K) :
    {k : ℤ // Odd k} ≃ {k : ℤ // Odd k} where
  toFun k := ⟨k.1 + K, by
    rcases k.2 with ⟨a, ha⟩
    rcases hK with ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    rw [ha, hb]
    ring⟩
  invFun k := ⟨k.1 - K, by
    rcases k.2 with ⟨a, ha⟩
    rcases hK with ⟨b, hb⟩
    refine ⟨a - b, ?_⟩
    rw [ha, hb]
    ring⟩
  left_inv k := by
    apply Subtype.ext
    simp
  right_inv k := by
    apply Subtype.ext
    simp

theorem ocL_mod_four (α q : ℝ) (Λ m : ℕ) : ocL α q Λ m % 4 = 1 := by
  simp [ocL, Nat.add_mod]

theorem ocL_sq_int_mod_four (α q : ℝ) (Λ m : ℕ) :
    ((ocL α q Λ m : ℤ) ^ 2) % 4 = 1 := by
  have h := ocL_mod_four α q Λ m
  have hcast : (ocL α q Λ m : ℤ) % 4 = 1 := by exact_mod_cast h
  have hsq : (ocL α q Λ m : ℤ) * (ocL α q Λ m : ℤ) % 4 = 1 := by
    rw [Int.mul_emod, hcast]
    norm_num
  simpa [pow_two] using hsq

theorem ocPi_add_mod4zero (k : {k : ℤ // Odd k}) (K : ℤ) (hK : Even K)
    (hK4 : K % 4 = 0) :
    ocPi (oddSlotAddEquiv K hK k) = ocPi k := by
  have hmod : (k.1 + K) % 4 = k.1 % 4 := by omega
  by_cases hk : k.1 % 4 = 1 <;>
    simp [ocPi, oddSlotAddEquiv, hk, hmod]

theorem ocPi_add_mod4two (k : {k : ℤ // Odd k}) (K : ℤ) (hK : Even K)
    (hK4 : K % 4 = 2) :
    ocPi (oddSlotAddEquiv K hK k) = AVenhance.sigmaMat * ocPi k * AVenhance.sigmaMatᵀ := by
  have hclass : k.1 % 4 = 1 ∨ k.1 % 4 = 3 := by
    rcases k.2 with ⟨a, ha⟩
    have hrem := Int.emod_lt k.1 (b := 4) (by norm_num)
    have hnon := Int.emod_nonneg k.1 (b := 4) (by norm_num)
    omega
  have hmod : (k.1 + K) % 4 = (k.1 % 4 + 2) % 4 := by
    rw [Int.add_emod, hK4]
  rcases hclass with hk | hk
  · have hs : (k.1 + K) % 4 = 3 := by rw [hmod, hk]; norm_num
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ocPi, oddSlotAddEquiv, AVenhance.sigmaMat, Matrix.mul_apply,
        Matrix.transpose_apply, Fin.sum_univ_two, hk, hs]
  · have hs : (k.1 + K) % 4 = 1 := by rw [hmod, hk]; norm_num
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ocPi, oddSlotAddEquiv, AVenhance.sigmaMat, Matrix.mul_apply,
        Matrix.transpose_apply, Fin.sum_univ_two, hk, hs]

theorem pulseMatrixSum_time_shift {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (ν t N : ℝ) (K J : ℤ)
    (hK : Even K) (hK4 : K % 4 = 0)
    (hKτ : (K : ℝ) * ocTau α q Λ m = N)
    (hJPP : (J : ℝ) * ocTauPP α q Λ m = N) :
    (∑' k : {k : ℤ // Odd k},
      (ocPulse α q Λ ζ m k.1 (t + N) * ocPulseMemory α q Λ ζ m ν k.1 (t + N)) • ocPi k) =
    (∑' k : {k : ℤ // Odd k},
      (ocPulse α q Λ ζ m k.1 t * ocPulseMemory α q Λ ζ m ν k.1 t) • ocPi k) := by
  classical
  let e := oddSlotAddEquiv K hK
  let f : {k : ℤ // Odd k} → Matrix (Fin 2) (Fin 2) ℝ := fun k =>
    (ocPulse α q Λ ζ m k.1 (t + N) * ocPulseMemory α q Λ ζ m ν k.1 (t + N)) • ocPi k
  change (∑' k, f k) = _
  calc
    (∑' k, f k) = ∑' k, f (e k) := (Equiv.tsum_eq e f).symm
    _ = ∑' k : {k : ℤ // Odd k},
        (ocPulse α q Λ ζ m k.1 t * ocPulseMemory α q Λ ζ m ν k.1 t) • ocPi k := by
      apply tsum_congr
      intro k
      change (ocPulse α q Λ ζ m (k.1 + K) (t + N) *
          ocPulseMemory α q Λ ζ m ν (k.1 + K) (t + N)) •
            ocPi (e k) = _
      rw [pulse_time_shift hΛ k.1 K J t N hKτ hJPP,
        pulseMemory_time_shift hΛ ν k.1 K J t N hKτ hJPP,
        ocPi_add_mod4zero k K hK hK4]

theorem refFlux_time_shift_four {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (ν t : ℝ) (h : ℝ)
    (hh : h = ocTauPP α q Λ m) :
    ocRefFlux α q Λ ζ m ν (t + 4 * h) = ocRefFlux α q Λ ζ m ν t := by
  let L : ℤ := ocL α q Λ m
  let K : ℤ := 4 * L ^ 2
  have hKeven : Even K := by
    refine ⟨2 * L ^ 2, ?_⟩
    dsimp [K]
    ring
  have hK4 : K % 4 = 0 := by
    dsimp [K]
    rw [Int.mul_emod]
    norm_num
  have hKτ : (K : ℝ) * ocTau α q Λ m = 4 * h := by
    rw [hh, ocTau]
    have hL : (ocL α q Λ m : ℝ) ≠ 0 := by
      have : 0 < ocL α q Λ m := by unfold ocL; omega
      exact_mod_cast (ne_of_gt this)
    dsimp [K, L]
    push_cast
    field_simp [hL]
  have hJPP : (4 : ℝ) * ocTauPP α q Λ m = 4 * h := by rw [hh]
  unfold ocRefFlux
  rw [pulseMatrixSum_time_shift hΛ ν t (4 * h) K 4 hKeven hK4 hKτ hJPP]

theorem ocPi_diagonal (k : {k : ℤ // Odd k}) :
    ocPi k = Matrix.diagonal (fun i : Fin 2 =>
      if k.1 % 4 = 1 then (if i = 1 then (1 : ℝ) else 0)
      else if i = 0 then 1 else 0) := by
  by_cases hk : k.1 % 4 = 1 <;> ext i j <;>
    fin_cases i <;> fin_cases j <;> simp [ocPi, Matrix.diagonal, hk]

theorem ocPi_smul_posSemidef (k : {k : ℤ // Odd k}) {c : ℝ} (hc : 0 ≤ c) :
    (c • ocPi k).PosSemidef := by
  rw [ocPi_diagonal]
  rw [show c • Matrix.diagonal (fun i : Fin 2 =>
      if k.1 % 4 = 1 then (if i = 1 then (1 : ℝ) else 0)
      else if i = 0 then 1 else 0) =
    Matrix.diagonal (fun i => c * (if k.1 % 4 = 1 then
      (if i = 1 then (1 : ℝ) else 0) else if i = 0 then 1 else 0)) by
      ext i j
      simp [Matrix.diagonal]]
  apply Matrix.PosSemidef.diagonal
  intro i
  by_cases hk : k.1 % 4 = 1 <;> by_cases hi : i = 1 <;> by_cases h0 : i = 0 <;>
    simp_all

theorem ocPi_upper_posSemidef (k : {k : ℤ // Odd k}) {H c : ℝ}
    (hH : 0 ≤ H) (hc : c ≤ H) : (H • (1 : Matrix (Fin 2) (Fin 2) ℝ) - c • ocPi k).PosSemidef := by
  rw [ocPi_diagonal]
  have hdiag : H • (1 : Matrix (Fin 2) (Fin 2) ℝ) -
      c • Matrix.diagonal (fun i : Fin 2 =>
        if k.1 % 4 = 1 then (if i = 1 then (1 : ℝ) else 0)
        else if i = 0 then 1 else 0) =
      Matrix.diagonal (fun i => H - c * (if k.1 % 4 = 1 then
        (if i = 1 then (1 : ℝ) else 0) else if i = 0 then 1 else 0)) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  rw [hdiag]
  apply Matrix.PosSemidef.diagonal
  intro i
  by_cases hk : k.1 % 4 = 1 <;> by_cases hi : i = 1 <;> by_cases h0 : i = 0 <;>
    simp_all

theorem pulseMatrixSum_single {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν t : ℝ) :
    (∃ k : {k : ℤ // Odd k}, ocPulse α q Λ ζ m k.1 t ≠ 0 ∧
      (∑' j : {j : ℤ // Odd j},
        (ocPulse α q Λ ζ m j.1 t * ocPulseMemory α q Λ ζ m ν j.1 t) • ocPi j) =
        (ocPulse α q Λ ζ m k.1 t * ocPulseMemory α q Λ ζ m ν k.1 t) • ocPi k) ∨
    ((∀ k : {k : ℤ // Odd k}, ocPulse α q Λ ζ m k.1 t = 0) ∧
      (∑' j : {j : ℤ // Odd j},
        (ocPulse α q Λ ζ m j.1 t * ocPulseMemory α q Λ ζ m ν j.1 t) • ocPi j) = 0) := by
  classical
  let f : {j : ℤ // Odd j} → Matrix (Fin 2) (Fin 2) ℝ := fun j =>
    (ocPulse α q Λ ζ m j.1 t * ocPulseMemory α q Λ ζ m ν j.1 t) • ocPi j
  by_cases hex : ∃ k : {k : ℤ // Odd k}, ocPulse α q Λ ζ m k.1 t ≠ 0
  · rcases hex with ⟨k, hk⟩
    left
    refine ⟨k, hk, ?_⟩
    change (∑' j, f j) = f k
    rw [tsum_eq_single k]
    intro j hj
    have hpj : ocPulse α q Λ ζ m j.1 t = 0 := by
      by_contra hne
      have heq : k.1 = j.1 := odd_pulse_support_unique hΛ hζ
        (k := k.1) (j := j.1) (t := t) k.2 j.2 hk hne
      exact hj (Subtype.ext heq.symm)
    simp [f, hpj]
  · right
    constructor
    · intro k
      by_contra hk
      exact hex ⟨k, hk⟩
    · change (∑' j, f j) = 0
      have hpzero : ∀ j : {j : ℤ // Odd j}, ocPulse α q Λ ζ m j.1 t = 0 := by
        intro j
        by_contra hj
        exact hex ⟨j, hj⟩
      calc
        (∑' j, f j) = ∑' _j : {j : ℤ // Odd j}, (0 : Matrix (Fin 2) (Fin 2) ℝ) := by
          apply tsum_congr
          intro j
          simp [f, hpzero j]
        _ = 0 := tsum_zero

theorem pulseMatrixSum_eq_at_active {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν t : ℝ)
    (k : {k : ℤ // Odd k}) (hk : ocPulse α q Λ ζ m k.1 t ≠ 0) :
    (∑' j : {j : ℤ // Odd j},
      (ocPulse α q Λ ζ m j.1 t * ocPulseMemory α q Λ ζ m ν j.1 t) • ocPi j) =
      (ocPulse α q Λ ζ m k.1 t * ocPulseMemory α q Λ ζ m ν k.1 t) • ocPi k := by
  classical
  rw [tsum_eq_single k]
  intro j hj
  have hpj : ocPulse α q Λ ζ m j.1 t = 0 := by
    by_contra hne
    have heq : k.1 = j.1 := odd_pulse_support_unique hΛ hζ
      (k := k.1) (j := j.1) (t := t) k.2 j.2 hk hne
    exact hj (Subtype.ext heq.symm)
  simp [hpj]

theorem pulseMatrixSum_eq_zero_of_quiet {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (ν t : ℝ) (hp : ∀ k : {k : ℤ // Odd k}, ocPulse α q Λ ζ m k.1 t = 0) :
    (∑' j : {j : ℤ // Odd j},
      (ocPulse α q Λ ζ m j.1 t * ocPulseMemory α q Λ ζ m ν j.1 t) • ocPi j) = 0 := by
  calc
    (∑' j : {j : ℤ // Odd j},
      (ocPulse α q Λ ζ m j.1 t * ocPulseMemory α q Λ ζ m ν j.1 t) • ocPi j) =
        ∑' _j : {j : ℤ // Odd j}, (0 : Matrix (Fin 2) (Fin 2) ℝ) := by
      apply tsum_congr
      intro j
      simp [hp j]
    _ = 0 := tsum_zero

theorem pulseMatrixSum_time_shift_flip {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν t N : ℝ) (K J : ℤ)
    (hK : Even K) (hK4 : K % 4 = 2)
    (hKτ : (K : ℝ) * ocTau α q Λ m = N)
    (hJPP : (J : ℝ) * ocTauPP α q Λ m = N) :
    (∑' k : {k : ℤ // Odd k},
      (ocPulse α q Λ ζ m k.1 (t + N) * ocPulseMemory α q Λ ζ m ν k.1 (t + N)) • ocPi k) =
    AVenhance.sigmaMat *
      (∑' k : {k : ℤ // Odd k},
        (ocPulse α q Λ ζ m k.1 t * ocPulseMemory α q Λ ζ m ν k.1 t) • ocPi k) *
      AVenhance.sigmaMatᵀ := by
  classical
  let e := oddSlotAddEquiv K hK
  by_cases hex : ∃ k : {k : ℤ // Odd k}, ocPulse α q Λ ζ m k.1 t ≠ 0
  · rcases hex with ⟨k, hk⟩
    have hk' : ocPulse α q Λ ζ m (e k).1 (t + N) ≠ 0 := by
      change ocPulse α q Λ ζ m (k.1 + K) (t + N) ≠ 0
      rw [pulse_time_shift hΛ k.1 K J t N hKτ hJPP]
      exact hk
    rw [pulseMatrixSum_eq_at_active hΛ hζ ν (t + N) (e k) hk',
      pulseMatrixSum_eq_at_active hΛ hζ ν t k hk]
    change (ocPulse α q Λ ζ m (k.1 + K) (t + N) *
        ocPulseMemory α q Λ ζ m ν (k.1 + K) (t + N)) • ocPi (e k) = _
    rw [pulse_time_shift hΛ k.1 K J t N hKτ hJPP,
      pulseMemory_time_shift hΛ ν k.1 K J t N hKτ hJPP,
      ocPi_add_mod4two k K hK hK4]
    simp
  · have hpzero : ∀ k : {k : ℤ // Odd k}, ocPulse α q Λ ζ m k.1 t = 0 := by
      intro k
      by_contra hk
      exact hex ⟨k, hk⟩
    have hpzero' : ∀ k : {k : ℤ // Odd k}, ocPulse α q Λ ζ m k.1 (t + N) = 0 := by
      intro k
      by_contra hk
      have hback := pulse_time_shift (α := α) (q := q) (Λ := Λ) (m := m) (ζ := ζ)
        hΛ (k.1 - K) K J t N hKτ hJPP
      have hindex : (k.1 - K) + K = k.1 := by ring
      have hval : ocPulse α q Λ ζ m (k.1 - K) t ≠ 0 := by
        intro hz
        apply hk
        rw [← hindex, hback, hz]
      exact hval (hpzero ⟨k.1 - K, by
        rcases k.2 with ⟨a, ha⟩
        rcases hK with ⟨b, hb⟩
        exact ⟨a - b, by rw [ha, hb]; ring⟩⟩)
    rw [pulseMatrixSum_eq_zero_of_quiet ν (t + N) hpzero',
      pulseMatrixSum_eq_zero_of_quiet ν t hpzero]
    simp

theorem refFlux_time_shift_two {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν t : ℝ) (h : ℝ)
    (hh : h = ocTauPP α q Λ m) :
    ocRefFlux α q Λ ζ m ν (t + 2 * h) =
      AVenhance.sigmaMat * ocRefFlux α q Λ ζ m ν t * AVenhance.sigmaMatᵀ := by
  let L : ℤ := ocL α q Λ m
  let K : ℤ := 2 * L ^ 2
  have hKeven : Even K := by
    refine ⟨L ^ 2, ?_⟩
    dsimp [K]
    ring
  have hK4 : K % 4 = 2 := by
    dsimp [K]
    rw [Int.mul_emod, ocL_sq_int_mod_four]
    norm_num
  have hKτ : (K : ℝ) * ocTau α q Λ m = 2 * h := by
    rw [hh, ocTau]
    have hL : (ocL α q Λ m : ℝ) ≠ 0 := by
      have : 0 < ocL α q Λ m := by unfold ocL; omega
      exact_mod_cast (ne_of_gt this)
    dsimp [K, L]
    push_cast
    field_simp [hL]
  have hJPP : (2 : ℝ) * ocTauPP α q Λ m = 2 * h := by rw [hh]
  have hσ : AVenhance.sigmaMat * (1 : Matrix (Fin 2) (Fin 2) ℝ) *
      AVenhance.sigmaMatᵀ = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [AVenhance.sigmaMat, Matrix.mul_apply, Matrix.transpose_apply,
        Fin.sum_univ_two]
  unfold ocRefFlux
  rw [pulseMatrixSum_time_shift_flip hΛ hζ ν t (2 * h) K 2 hKeven hK4 hKτ hJPP]
  have hconj (S : Matrix (Fin 2) (Fin 2) ℝ) (a : ℝ) :
      ν • (1 : Matrix (Fin 2) (Fin 2) ℝ) + a •
        (AVenhance.sigmaMat * S * AVenhance.sigmaMatᵀ) =
      AVenhance.sigmaMat *
        (ν • (1 : Matrix (Fin 2) (Fin 2) ℝ) + a • S) * AVenhance.sigmaMatᵀ := by
    calc
      _ = ν • (AVenhance.sigmaMat * (1 : Matrix (Fin 2) (Fin 2) ℝ) *
            AVenhance.sigmaMatᵀ) +
          a • (AVenhance.sigmaMat * S * AVenhance.sigmaMatᵀ) := by rw [hσ]
      _ = AVenhance.sigmaMat *
          (ν • (1 : Matrix (Fin 2) (Fin 2) ℝ) + a • S) * AVenhance.sigmaMatᵀ := by
        simp [Matrix.add_mul, Matrix.mul_add, mul_assoc]
  exact hconj _ _

theorem ocMu_pos {q : ℝ} {Λ m : ℕ} {ν : ℝ} (hΛ : 1 ≤ Λ) (hν : 0 < ν) :
    0 < ocMu q Λ m ν := by
  unfold ocMu
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (Λ := Λ) (n := m) hΛ
  positivity

theorem ocHStar_pos {α q : ℝ} {Λ m : ℕ} {ν : ℝ} (hΛ : 1 ≤ Λ) (hν : 0 < ν) :
    0 < ocHStar α q Λ m ν := by
  unfold ocHStar
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (Λ := Λ) (n := m) hΛ
  have hp : 0 < ocEpsilon q Λ m ^ (2 * (1 + α)) :=
    Real.rpow_pos_of_pos he _
  positivity

theorem scalar_identity_posSemidef {c : ℝ} (hc : 0 ≤ c) :
    (c • (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosSemidef := by
  rw [show c • (1 : Matrix (Fin 2) (Fin 2) ℝ) = Matrix.diagonal (fun _ : Fin 2 => c) by
    ext i j
    simp [Matrix.diagonal, Matrix.one_apply]]
  exact Matrix.PosSemidef.diagonal (by intro i; exact hc)

theorem refFlux_pointwise_posSemidef {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν t : ℝ} (hν : 0 < ν) :
    (ocRefFlux α q Λ ζ m ν t - ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosSemidef ∧
    ((ν + ocHStar α q Λ m ν) • (1 : Matrix (Fin 2) (Fin 2) ℝ) -
      ocRefFlux α q Λ ζ m ν t).PosSemidef := by
  have hμ := ocMu_pos (q := q) (Λ := Λ) (m := m) hΛ hν
  have hH := ocHStar_pos (α := α) (q := q) (Λ := Λ) (m := m) hΛ hν
  rcases pulseMatrixSum_single (α := α) (q := q) (Λ := Λ) (m := m) (ζ := ζ)
      hΛ hζ ν t with hactive | hquiet
  · rcases hactive with ⟨k, hpk, hsum⟩
    have hp := ocPulse_range (α := α) (q := q) (Λ := Λ) (m := m) hζ k.1 t
    have hm := ocPulseMemory_range (α := α) (q := q) (Λ := Λ) (m := m)
      hΛ hζ ν hν k.1 t
    let c : ℝ := ocMu q Λ m ν * ocHStar α q Λ m ν *
      (ocPulse α q Λ ζ m k.1 t * ocPulseMemory α q Λ ζ m ν k.1 t)
    have hc : 0 ≤ c := by
      dsimp [c]
      exact mul_nonneg (mul_nonneg hμ.le hH.le) (mul_nonneg hp.1 hm.1)
    have hnormalized : ocMu q Λ m ν *
        (ocPulse α q Λ ζ m k.1 t * ocPulseMemory α q Λ ζ m ν k.1 t) ≤ 1 := by
      have hprod : ocPulse α q Λ ζ m k.1 t *
          (ocMu q Λ m ν * ocPulseMemory α q Λ ζ m ν k.1 t) ≤ 1 * 1 :=
        mul_le_mul hp.2 hm.2 (mul_nonneg hμ.le hm.1) (by norm_num)
      calc
        ocMu q Λ m ν *
            (ocPulse α q Λ ζ m k.1 t * ocPulseMemory α q Λ ζ m ν k.1 t) =
          ocPulse α q Λ ζ m k.1 t *
            (ocMu q Λ m ν * ocPulseMemory α q Λ ζ m ν k.1 t) := by ring
        _ ≤ 1 := by simpa using hprod
    have hcH : c ≤ ocHStar α q Λ m ν := by
      dsimp [c]
      calc
        ocMu q Λ m ν * ocHStar α q Λ m ν *
            (ocPulse α q Λ ζ m k.1 t * ocPulseMemory α q Λ ζ m ν k.1 t) =
          ocHStar α q Λ m ν *
            (ocMu q Λ m ν *
              (ocPulse α q Λ ζ m k.1 t * ocPulseMemory α q Λ ζ m ν k.1 t)) := by ring
        _ ≤ ocHStar α q Λ m ν * 1 := mul_le_mul_of_nonneg_left hnormalized hH.le
        _ = ocHStar α q Λ m ν := by ring
    have hflux : ocRefFlux α q Λ ζ m ν t =
        ν • (1 : Matrix (Fin 2) (Fin 2) ℝ) + c • ocPi k := by
      rw [ocRefFlux, hsum, smul_smul]
    constructor
    · rw [hflux]
      simpa using ocPi_smul_posSemidef k hc
    · rw [hflux]
      have hmatrix : (ν + ocHStar α q Λ m ν) •
          (1 : Matrix (Fin 2) (Fin 2) ℝ) -
          (ν • (1 : Matrix (Fin 2) (Fin 2) ℝ) + c • ocPi k) =
          ocHStar α q Λ m ν • (1 : Matrix (Fin 2) (Fin 2) ℝ) - c • ocPi k := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]
      rw [hmatrix]
      exact ocPi_upper_posSemidef k hH.le hcH
  · rcases hquiet with ⟨hpzero, hsum⟩
    have hflux : ocRefFlux α q Λ ζ m ν t =
        ν • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      rw [ocRefFlux, hsum]
      simp
    constructor
    · rw [hflux]
      have hz : (0 : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef := by
        rw [show (0 : Matrix (Fin 2) (Fin 2) ℝ) =
          Matrix.diagonal (fun _ : Fin 2 => (0 : ℝ)) by ext i j; simp]
        exact Matrix.PosSemidef.diagonal (by intro i; norm_num)
      simpa using hz
    · rw [hflux]
      have hmatrix : (ν + ocHStar α q Λ m ν) •
          (1 : Matrix (Fin 2) (Fin 2) ℝ) -
          ν • (1 : Matrix (Fin 2) (Fin 2) ℝ) =
          ocHStar α q Λ m ν • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]
      rw [hmatrix]
      exact scalar_identity_posSemidef hH.le

theorem refFlux_shape {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν t : ℝ} (hν : 0 < ν) :
    (∃ k : {k : ℤ // Odd k}, ∃ c : ℝ,
      ocRefFlux α q Λ ζ m ν t =
        ν • (1 : Matrix (Fin 2) (Fin 2) ℝ) + c • ocPi k ∧
      0 ≤ c ∧ c ≤ ocHStar α q Λ m ν) ∨
    ocRefFlux α q Λ ζ m ν t = ν • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have hμ := ocMu_pos (q := q) (Λ := Λ) (m := m) hΛ hν
  have hH := ocHStar_pos (α := α) (q := q) (Λ := Λ) (m := m) hΛ hν
  rcases pulseMatrixSum_single (α := α) (q := q) (Λ := Λ) (m := m) (ζ := ζ)
      hΛ hζ ν t with hactive | hquiet
  · rcases hactive with ⟨k, hpk, hsum⟩
    have hp := ocPulse_range (α := α) (q := q) (Λ := Λ) (m := m) hζ k.1 t
    have hm := ocPulseMemory_range (α := α) (q := q) (Λ := Λ) (m := m)
      hΛ hζ ν hν k.1 t
    let c : ℝ := ocMu q Λ m ν * ocHStar α q Λ m ν *
      (ocPulse α q Λ ζ m k.1 t * ocPulseMemory α q Λ ζ m ν k.1 t)
    have hc : 0 ≤ c := by
      dsimp [c]
      exact mul_nonneg (mul_nonneg hμ.le hH.le) (mul_nonneg hp.1 hm.1)
    have hnormalized : ocMu q Λ m ν *
        (ocPulse α q Λ ζ m k.1 t * ocPulseMemory α q Λ ζ m ν k.1 t) ≤ 1 := by
      have hprod : ocPulse α q Λ ζ m k.1 t *
          (ocMu q Λ m ν * ocPulseMemory α q Λ ζ m ν k.1 t) ≤ 1 * 1 :=
        mul_le_mul hp.2 hm.2 (mul_nonneg hμ.le hm.1) (by norm_num)
      calc
        ocMu q Λ m ν *
            (ocPulse α q Λ ζ m k.1 t * ocPulseMemory α q Λ ζ m ν k.1 t) =
          ocPulse α q Λ ζ m k.1 t *
            (ocMu q Λ m ν * ocPulseMemory α q Λ ζ m ν k.1 t) := by ring
        _ ≤ 1 := by simpa using hprod
    have hcH : c ≤ ocHStar α q Λ m ν := by
      dsimp [c]
      calc
        ocMu q Λ m ν * ocHStar α q Λ m ν *
            (ocPulse α q Λ ζ m k.1 t * ocPulseMemory α q Λ ζ m ν k.1 t) =
          ocHStar α q Λ m ν *
            (ocMu q Λ m ν *
              (ocPulse α q Λ ζ m k.1 t * ocPulseMemory α q Λ ζ m ν k.1 t)) := by ring
        _ ≤ ocHStar α q Λ m ν * 1 := mul_le_mul_of_nonneg_left hnormalized hH.le
        _ = ocHStar α q Λ m ν := by ring
    left
    refine ⟨k, c, ?_, hc, hcH⟩
    rw [ocRefFlux, hsum, smul_smul]
  · rcases hquiet with ⟨_, hsum⟩
    right
    rw [ocRefFlux, hsum]
    simp

theorem refFlux_entry_norm_le {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν t : ℝ} (hν : 0 < ν)
    (i j : Fin 2) :
    ‖ocRefFlux α q Λ ζ m ν t i j‖ ≤ ν + ocHStar α q Λ m ν := by
  rcases refFlux_shape hΛ hζ hν with hactive | hquiet
  · rcases hactive with ⟨k, c, hflux, hc, hcH⟩
    have hH := ocHStar_pos (α := α) (q := q) (Λ := Λ) (m := m) hΛ hν
    have hνc : 0 ≤ ν + c := by linarith
    rw [hflux]
    fin_cases i <;> fin_cases j <;> by_cases hk : k.1 % 4 = 1 <;>
      simp [Matrix.smul_apply, ocPi, hk, Real.norm_eq_abs,
        abs_of_nonneg hν.le, abs_of_nonneg hνc] <;> linarith
  · rw [hquiet]
    have hH := ocHStar_pos (α := α) (q := q) (Λ := Λ) (m := m) hΛ hν
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.smul_apply, Real.norm_eq_abs,
        abs_of_nonneg hν.le] <;> linarith

private theorem pulseMatrixSum_entry_tsum {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν t : ℝ) (i j : Fin 2) :
    (∑' k : {k : ℤ // Odd k},
      (ocPulse α q Λ ζ m k.1 t * ocPulseMemory α q Λ ζ m ν k.1 t) • ocPi k) i j =
      ∑' k : {k : ℤ // Odd k},
        (ocPulse α q Λ ζ m k.1 t * ocPulseMemory α q Λ ζ m ν k.1 t) * ocPi k i j := by
  classical
  rcases pulseMatrixSum_single (α := α) (q := q) (Λ := Λ) (m := m) (ζ := ζ)
      hΛ hζ ν t with hactive | hquiet
  · rcases hactive with ⟨k₀, hk₀, hmatrix⟩
    have hzero (k : {k : ℤ // Odd k}) (hne : k ≠ k₀) :
        ocPulse α q Λ ζ m k.1 t = 0 := by
      by_contra hk
      have heq := odd_pulse_support_unique hΛ hζ (k := k₀.1) (j := k.1)
        (t := t) k₀.2 k.2 hk₀ hk
      exact hne (Subtype.ext heq.symm)
    have hscalar :
        (∑' k : {k : ℤ // Odd k},
          (ocPulse α q Λ ζ m k.1 t * ocPulseMemory α q Λ ζ m ν k.1 t) * ocPi k i j) =
          (ocPulse α q Λ ζ m k₀.1 t * ocPulseMemory α q Λ ζ m ν k₀.1 t) * ocPi k₀ i j := by
      rw [tsum_eq_single k₀]
      · intro k hk
        simp [hzero k hk]
    have hcoord := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M i j) hmatrix
    calc
      _ = (ocPulse α q Λ ζ m k₀.1 t * ocPulseMemory α q Λ ζ m ν k₀.1 t) *
          ocPi k₀ i j := by simpa [Matrix.smul_apply] using hcoord
      _ = _ := hscalar.symm
  · rcases hquiet with ⟨hp, hmatrix⟩
    have hscalar :
        (∑' k : {k : ℤ // Odd k},
          (ocPulse α q Λ ζ m k.1 t * ocPulseMemory α q Λ ζ m ν k.1 t) * ocPi k i j) = 0 := by
      calc
        _ = ∑' _k : {k : ℤ // Odd k}, (0 : ℝ) := by
          apply tsum_congr
          intro k
          simp [hp k]
        _ = 0 := tsum_zero
    have hcoord := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M i j) hmatrix
    calc
      _ = 0 := by simpa [Matrix.smul_apply] using hcoord
      _ = _ := hscalar.symm

theorem refFlux_entry_measurable {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (i j : Fin 2) : Measurable (fun t => ocRefFlux α q Λ ζ m ν t i j) := by
  have hterm (k : {k : ℤ // Odd k}) :
      Continuous (fun t : ℝ =>
        (ocPulse α q Λ ζ m k.1 t * ocPulseMemory α q Λ ζ m ν k.1 t) * ocPi k i j) := by
    have hp := ocPulse_continuous (α := α) (q := q) (Λ := Λ) (m := m) hζ k.1
    have hm := ocPulseMemory_continuous (α := α) (q := q) (Λ := Λ) (m := m)
      hΛ hζ hν k.1
    fun_prop
  have hsum : Measurable (fun t : ℝ =>
      ∑' k : {k : ℤ // Odd k},
        (ocPulse α q Λ ζ m k.1 t * ocPulseMemory α q Λ ζ m ν k.1 t) * ocPi k i j) :=
    Measurable.tsum (fun k => (hterm k).measurable)
  have hformula : (fun t => ocRefFlux α q Λ ζ m ν t i j) = fun t =>
      (ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j +
        (ocMu q Λ m ν * ocHStar α q Λ m ν) *
          (∑' k : {k : ℤ // Odd k},
            (ocPulse α q Λ ζ m k.1 t * ocPulseMemory α q Λ ζ m ν k.1 t) * ocPi k i j) := by
    funext t
    change ν • ((1 : Matrix (Fin 2) (Fin 2) ℝ) i j) +
      (ocMu q Λ m ν * ocHStar α q Λ m ν) •
        ((∑' k : {k : ℤ // Odd k},
          (ocPulse α q Λ ζ m k.1 t * ocPulseMemory α q Λ ζ m ν k.1 t) • ocPi k) i j) = _
    rw [pulseMatrixSum_entry_tsum (α := α) (q := q) (Λ := Λ) (m := m) (ζ := ζ)
      hΛ hζ ν t i j]
    simp [smul_eq_mul]
  rw [hformula]
  exact measurable_const.add (hsum.const_mul _)

theorem refFlux_entry_intervalIntegrable {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (i j : Fin 2) (a b : ℝ) :
    IntervalIntegrable (fun t => ocRefFlux α q Λ ζ m ν t i j) volume a b := by
  have hmeas : Measurable (fun t => ocRefFlux α q Λ ζ m ν t i j) :=
    refFlux_entry_measurable hΛ hζ hν i j
  have hbounded : ∀ t, ‖ocRefFlux α q Λ ζ m ν t i j‖ ≤
      ν + ocHStar α q Λ m ν :=
    fun t => refFlux_entry_norm_le hΛ hζ hν i j
  apply intervalIntegrable_iff.mpr
  apply MeasureTheory.Measure.integrableOn_of_bounded (M := ν + ocHStar α q Λ m ν)
  · have hfinite : volume (Set.uIoc a b) < ⊤ := by
      calc
        volume (Set.uIoc a b) ≤ volume (Set.Icc (min a b) (max a b)) := by
          apply measure_mono
          exact Set.uIoc_subset_uIcc
        _ < ⊤ := measure_Icc_lt_top
    exact hfinite.ne
  · exact hmeas.aestronglyMeasurable
  · filter_upwards [] with t
    exact hbounded t

theorem refFlux_has_molecular_eigenvector {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν t : ℝ} (hν : 0 < ν) :
    ∃ v : Vec 2, v ≠ 0 ∧ (ocRefFlux α q Λ ζ m ν t).mulVec v = ν • v := by
  rcases refFlux_shape hΛ hζ hν with hactive | hquiet
  · rcases hactive with ⟨k, c, hflux, _, _⟩
    by_cases hk : k.1 % 4 = 1
    · let v : Vec 2 := fun i => if i = 0 then 1 else 0
      have hv : v ≠ 0 := by
        intro hz
        have h0 := congrFun hz (0 : Fin 2)
        norm_num [v] at h0
      refine ⟨v, hv, ?_⟩
      rw [hflux]
      ext i
      fin_cases i <;>
        simp [v, ocPi, hk, Matrix.mulVec, dotProduct]
    · let v : Vec 2 := fun i => if i = 1 then 1 else 0
      have hv : v ≠ 0 := by
        intro hz
        have h1 := congrFun hz (1 : Fin 2)
        norm_num [v] at h1
      refine ⟨v, hv, ?_⟩
      rw [hflux]
      ext i
      fin_cases i <;>
        simp [v, ocPi, hk, Matrix.mulVec, dotProduct]
  · refine ⟨fun i => if i = 0 then 1 else 0, ?_, ?_⟩
    · intro hz
      have h0 := congrFun hz (0 : Fin 2)
      norm_num at h0
    · rw [hquiet]
      ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct]

end AVRegularity.CycleReference
end

section
open scoped NNReal
namespace AVRegularity.CycleReference

/-! Uniform Lipschitz constants for the fixed smooth time profiles. -/

theorem smooth_compact_lipschitz {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) : ∃ K : ℝ≥0, LipschitzWith K f := by
  obtain ⟨B, hB⟩ := (hf.continuous_deriv (by simp)).norm.bddAbove_range_of_hasCompactSupport
    hc.deriv.norm
  refine ⟨⟨max B 0, le_max_right _ _⟩, lipschitzWith_of_nnnorm_deriv_le
    (hf.differentiable (by simp)) ?_⟩
  intro x
  change ‖deriv f x‖ ≤ max B 0
  exact (hB (Set.mem_range_self _)).trans (le_max_left _ _)

theorem smoothTransition_deriv_hasCompactSupport : HasCompactSupport (deriv Real.smoothTransition) := by
  apply IsCompact.of_isClosed_subset (isCompact_Icc (a := (0 : ℝ)) (b := 1)) isClosed_closure
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hn : deriv Real.smoothTransition x ≠ 0 := hx
  constructor
  · by_contra h
    apply hn
    apply IsLocalMin.deriv_eq_zero
    have hz : Real.smoothTransition x = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
    filter_upwards [] with y
    rw [hz]
    exact Real.smoothTransition.nonneg y
  · by_contra h
    apply hn
    apply IsLocalMax.deriv_eq_zero
    have hz : Real.smoothTransition x = 1 := Real.smoothTransition.one_of_one_le (by linarith)
    filter_upwards [] with y
    rw [hz]
    exact Real.smoothTransition.le_one y

theorem smoothTransition_lipschitz : ∃ K : ℝ≥0, LipschitzWith K Real.smoothTransition := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).continuous_deriv (by simp)
  obtain ⟨B, hB⟩ := hc.norm.bddAbove_range_of_hasCompactSupport
    smoothTransition_deriv_hasCompactSupport.norm
  refine ⟨⟨max B 0, le_max_right _ _⟩, lipschitzWith_of_nnnorm_deriv_le
    ((Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).differentiable (by simp)) ?_⟩
  intro x
  change ‖deriv Real.smoothTransition x‖ ≤ max B 0
  exact (hB (Set.mem_range_self _)).trans (le_max_left _ _)

theorem fastProfile_lipschitz {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ K : ℝ≥0, LipschitzWith K ζ := by
  apply smooth_compact_lipschitz hζ.1
  exact IsCompact.of_isClosed_subset (isCompact_Icc (a := -(2 / 3 : ℝ)) (b := 2 / 3))
    isClosed_closure (hζ.2.2.1.trans Set.Ioo_subset_Icc_self)

/-! Pulse time variations are uniformly controlled on the fast time scale. -/

theorem unit_product_sub_bound {a b c d : ℝ}
    (hb : |b| ≤ 1) (hc : |c| ≤ 1) : |a * b - c * d| ≤ |a - c| + |b - d| := by
  calc
    _ = |(a - c) * b + c * (b - d)| := by congr 1; ring
    _ ≤ |(a - c) * b| + |c * (b - d)| := abs_add_le _ _
    _ ≤ |a - c| * 1 + 1 * |b - d| := by
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hb (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hc (abs_nonneg _))
    _ = _ := by ring

theorem ocPulse_uniform_lipschitz {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (α q : ℝ) (Λ m : ℕ), 1 ≤ Λ → ∀ k : ℤ, ∀ t u : ℝ,
      |ocPulse α q Λ ζ m k t - ocPulse α q Λ ζ m k u| ≤
        K / ocTau α q Λ m * |t - u| := by
  obtain ⟨H, hH⟩ := smoothTransition_lipschitz
  obtain ⟨Z, hZ⟩ := fastProfile_lipschitz hζ
  refine ⟨2 * (H : ℝ) + Z, by positivity, ?_⟩
  intro α q Λ m hΛ k t u
  let τ := ocTau α q Λ m
  let P := ocTauP α q Λ m
  let l := ocLabel α q Λ m k
  let a := ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m + P
  let b := ((l : ℝ) + 1 / 2) * ocTauPP α q Λ m - P
  have hτ : 0 < τ := AVRegularity.Construction.Stream.ocTau_pos hΛ
  have hL : 1 ≤ (ocL α q Λ m : ℝ) := by
    have hn : 1 ≤ ocL α q Λ m := by unfold ocL; omega
    exact_mod_cast hn
  have heq : P = (ocL α q Λ m : ℝ) * τ := by
    dsimp [P, τ]
    rw [ocTauP, ocTau]
    field_simp
  have hPτ : τ ≤ P := by rw [heq]; nlinarith only [hL, hτ]
  have hP : 0 < P := hτ.trans_le hPτ
  have hs (x y : ℝ) : |Real.smoothTransition x - Real.smoothTransition y| ≤ (H : ℝ) * |x - y| :=
    by simpa only [Real.norm_eq_abs] using hH.norm_sub_le x y
  have hz (x y : ℝ) : |ζ x - ζ y| ≤ (Z : ℝ) * |x - y| :=
    by simpa only [Real.norm_eq_abs] using hZ.norm_sub_le x y
  have hdist1 : |(t - a) / P - (u - a) / P| = |t - u| / P := by
    rw [← sub_div, show t - a - (u - a) = t - u by ring, abs_div, abs_of_pos hP]
  have hdist2 : |(b - t) / P - (b - u) / P| = |t - u| / P := by
    rw [← sub_div, show b - t - (b - u) = -(t - u) by ring, abs_div, abs_neg, abs_of_pos hP]
  have hdist3 : |(t - (k : ℝ) * τ) / τ - (u - (k : ℝ) * τ) / τ| = |t - u| / τ := by
    rw [← sub_div, show t - (k : ℝ) * τ - (u - (k : ℝ) * τ) = t - u by ring,
      abs_div, abs_of_pos hτ]
  have hslow : |slowEnvelope α q Λ m l t - slowEnvelope α q Λ m l u| ≤
      2 * (H : ℝ) * (|t - u| / P) := by
    have h1 := hs ((t - a) / P) ((u - a) / P)
    have h2 := hs ((b - t) / P) ((b - u) / P)
    rw [hdist1] at h1
    rw [hdist2] at h2
    have hp := unit_product_sub_bound
      (a := Real.smoothTransition ((t - a) / P))
      (b := Real.smoothTransition ((b - t) / P))
      (c := Real.smoothTransition ((u - a) / P))
      (d := Real.smoothTransition ((b - u) / P))
      (by rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]; exact Real.smoothTransition.le_one _)
      (by rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]; exact Real.smoothTransition.le_one _)
    have ht : slowEnvelope α q Λ m l t = Real.smoothTransition ((t - a) / P) *
        Real.smoothTransition ((b - t) / P) := by unfold slowEnvelope; dsimp [a, b, P]; congr 2; ring
    have hu : slowEnvelope α q Λ m l u = Real.smoothTransition ((u - a) / P) *
        Real.smoothTransition ((b - u) / P) := by unfold slowEnvelope; dsimp [a, b, P]; congr 2; ring
    rw [ht, hu]
    linarith only [hp, h1, h2]
  have hfast := hz ((t - (k : ℝ) * τ) / τ) ((u - (k : ℝ) * τ) / τ)
  rw [hdist3] at hfast
  have hp := unit_product_sub_bound
    (a := slowEnvelope α q Λ m l t) (b := ζ ((t - (k : ℝ) * τ) / τ))
    (c := slowEnvelope α q Λ m l u) (d := ζ ((u - (k : ℝ) * τ) / τ))
    (by rw [abs_of_nonneg (hζ.2.2.2.1 _).1]; exact (hζ.2.2.2.1 _).2)
    (by rw [abs_of_nonneg (slowEnvelope_range α q Λ m l u).1]; exact (slowEnvelope_range α q Λ m l u).2)
  have hratio : |t - u| / P ≤ |t - u| / τ := div_le_div_of_nonneg_left (abs_nonneg _) hτ hPτ
  have hscaled := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 2 * (H : ℝ) by positivity)
  change |slowEnvelope α q Λ m l t * ζ ((t - (k : ℝ) * τ) / τ) -
    slowEnvelope α q Λ m l u * ζ ((u - (k : ℝ) * τ) / τ)| ≤ _
  calc
    _ ≤ 2 * (H : ℝ) * (|t - u| / P) + (Z : ℝ) * (|t - u| / τ) :=
      hp.trans (add_le_add hslow hfast)
    _ ≤ 2 * (H : ℝ) * (|t - u| / τ) + (Z : ℝ) * (|t - u| / τ) :=
      add_le_add hscaled le_rfl
    _ = _ := by dsimp [τ]; ring

end AVRegularity.CycleReference
end

section
open Filter Topology Homogenization
namespace AVRegularity.CycleReference

/-! Every time derivative after the forcing has ended follows the homogeneous memory ODE. -/

theorem iteratedDeriv_linear_ode_on_ray {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {c T : ℝ} (hf : ∀ t, T < t → HasDerivAt f (c • f t) t)
    (n : ℕ) (t : ℝ) (ht : T < t) : iteratedDeriv n f t = c ^ n • f t := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    have he : iteratedDeriv n f =ᶠ[𝓝 t] (fun u => c ^ n • f u) := by
      filter_upwards [Ioi_mem_nhds ht] with u hu
      exact ih u hu
    have hd := (hf t ht).const_smul (c ^ n)
    have hd' := hd.congr_of_eventuallyEq he
    rw [iteratedDeriv_succ, hd'.deriv, smul_smul]
    congr 1

theorem pulseCorrector_quiet_time_derivative {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (k : ℤ) (a : ℕ)
    (t : ℝ) (ht : ((k : ℝ) + 3 / 4) * ocTau α q Λ m ≤ t) (y : Vec 2) :
    iteratedDeriv a (fun u => ocPulseCorrector α q Λ ζ m ν k u y) t =
      (-(ocMu q Λ m ν)) ^ a • ocPulseCorrector α q Λ ζ m ν k t y := by
  have hτ := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
  have ht' : ((k : ℝ) + 2 / 3) * ocTau α q Λ m < t := by linarith
  apply iteratedDeriv_linear_ode_on_ray (T := ((k : ℝ) + 2 / 3) * ocTau α q Λ m)
    (t := t) (c := -(ocMu q Λ m ν)) (n := a) _ ht'
  intro u hu
  have hp : ocPulse α q Λ ζ m k u = 0 := by
    by_contra hp
    have hh := (pulse_nonzero_center_distance hΛ hζ hp).2
    linarith only [hh, hu]
  have hd := ((ocPulseMemory_hasDerivAt (α := α) (q := q) (m := m) hΛ hζ ν k u).neg).smul_const
    (ocShearVel α q Λ m k y)
  change HasDerivAt (fun u => -(ocPulseMemory α q Λ ζ m ν k u) • ocShearVel α q Λ m k y)
    ((-(ocMu q Λ m ν)) • (-(ocPulseMemory α q Λ ζ m ν k u) • ocShearVel α q Λ m k y)) u
  convert hd using 1
  rw [hp]
  simp only [zero_sub, neg_neg, smul_smul]
  congr 1
  ring

end AVRegularity.CycleReference
end
end
end

section
@[expose] public section
open Homogenization AVenhance MeasureTheory
namespace AVRegularity.CycleReference

/-! The weak solution's tested integrability controls the chart's drift correction. -/

theorem spaceGrad_eq_zero_of_eq_zero {η : Vec 2 → ℝ} (hη : ∀ x, η x = 0) (x : Vec 2) :
    spaceGrad η x = 0 := by
  have he : η = fun _ => 0 := funext hη
  rw [he]
  ext i
  simp [spaceGrad]

theorem tested_integrability_implies_drift_correction_integrability
    (b : ℝ → Vec 2 → Vec 2) (A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (q : ℝ → Vec 2 → Vec 2) (f θ : ℝ → Vec 2 → ℝ)
    (Dθ : ℝ → Vec 2 → Vec 2) (a c : ℝ)
    (hI : ∀ η : ℝ → Vec 2 → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => η p.1 p.2) →
      HasCompactSupport (fun p : ℝ × Vec 2 => η p.1 p.2) →
      (∀ t, c ≤ t → ∀ x, η t x = 0) →
      Integrable (planeWeakIntegrand b A q f θ Dθ η)
        (volume.restrict (Set.Ioo a c ×ˢ Set.univ)))
    (B : ℝ → Vec 2 → Vec 2)
    (hB : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => B p.1 p.2))
    (η : ℝ → Vec 2 → ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => η p.1 p.2))
    (hc : HasCompactSupport (fun p : ℝ × Vec 2 => η p.1 p.2))
    (hz : ∀ t, c ≤ t → ∀ x, η t x = 0) :
    Integrable (fun p : ℝ × Vec 2 => θ p.1 p.2 *
      vecDot (B p.1 p.2) (spaceGrad (η p.1) p.2))
      (volume.restrict (Set.Ioo a c ×ˢ Set.univ)) := by
  let ξ := fun t x => vecDot (B t x) (spaceGrad (η t) x)
  have he : (fun p : ℝ × Vec 2 => ξ p.1 p.2) =
      (fun p => B p.1 p.2 0 * spaceGrad (η p.1) p.2 0 +
        B p.1 p.2 1 * spaceGrad (η p.1) p.2 1) := by
    funext p
    simp [ξ, vecDot, Fin.sum_univ_two]
  have hξ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => ξ p.1 p.2) := by
    rw [he]
    exact (((contDiff_apply ℝ ℝ 0).comp hB).mul (joint_spaceGrad_smooth hη 0)).add
      (((contDiff_apply ℝ ℝ 1).comp hB).mul (joint_spaceGrad_smooth hη 1))
  have hcξ : HasCompactSupport (fun p : ℝ × Vec 2 => ξ p.1 p.2) := by
    rw [he]
    exact ((joint_spaceGrad_compact hη hc 0).mul_left).add
      ((joint_spaceGrad_compact hη hc 1).mul_left)
  have hzξ : ∀ t, c ≤ t → ∀ x, ξ t x = 0 := by
    intro t ht x
    dsimp [ξ]
    rw [spaceGrad_eq_zero_of_eq_zero (hz t ht)]
    simp [vecDot]
  exact tested_integrability_implies_mul_test_integrability b A q f θ Dθ a c hI ξ hξ hcξ hzξ

end AVRegularity.CycleReference
end
end
