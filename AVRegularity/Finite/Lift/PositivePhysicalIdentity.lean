-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Finite.Assembly.TerminalSeedTransportOfIngredients
import AVRegularity.Construction.Preservation.FullLift.PositiveChartInputJets
import AVRegularity.CycleComparison.Lift.LiftMeanCompositionLowDegree
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction

/-! Separate the literal degree-zero physical pulse without any coefficient norm estimate. -/

@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.Finite
open Construction.Preservation.FullLift CycleComparison.Lift

theorem positive_scale_gain : PositiveScaleGainStatement := by
  intro e E s he heE hs
  have hE : 0 < E := he.trans_le heE
  exact Real.rpow_le_one (div_nonneg he.le hE.le) ((div_le_one hE).mpr heE)
    (sub_nonneg.mpr hs.le)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

/-- The removed zero-degree part is the physical input, at height zero only. -/
theorem pulse_positive_difference (Q : LiftOperatorData ι h D)
    (sX sZ : ℕ) (a b : ℝ) (N H : ℕ) (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h) (k : ℤ)
    (hseq : IsLiftSequence Q sX sZ a b N H (Cc k))
    (c ρ e εc τ : ℝ) (hρ : ρ ≠ 0) (ht : c⁻¹ * τ ∈ Set.Icc a b)
    (Φ Ψ : Vec 2 → Vec 2) (f : Vec 2 → ∀ i, h i) (x : Vec 2) (hinv : Φ (Ψ x) = x) (v : ι) :
    pulsePhysicalLift c ρ e εc N H (Cc k) (fun _ => Φ) (fun _ => Ψ) (fun _ => f) τ x v -
      pulsePhysicalLift c ρ e εc N H (positiveLiftCoefficients Cc k)
        (fun _ => Φ) (fun _ => Ψ) (fun _ => f) τ x v = f x v := by
  classical
  rw [pulsePhysicalLift_static_expansion, pulsePhysicalLift_static_expansion,
    ← Finset.sum_sub_distrib]
  have hdegree (hh : ℕ) (hhh : hh ≤ H) :
      (∑ n ∈ Finset.range (N + 1), εc ^ n •
        liftApply n (Cc k hh n) (fun _ Y => f (Φ (ρ • Y)))
          (c⁻¹ * τ) (ρ⁻¹ • Ψ x) (e⁻¹ • Ψ x) v) -
      (∑ n ∈ Finset.range (N + 1), εc ^ n •
        liftApply n (positiveLiftCoefficients Cc k hh n) (fun _ Y => f (Φ (ρ • Y)))
          (c⁻¹ * τ) (ρ⁻¹ • Ψ x) (e⁻¹ • Ψ x) v) = if hh = 0 then f x v else 0 := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single 0]
    · have hz : liftApply 0 (positiveLiftCoefficients Cc k hh 0)
          (fun _ Y => f (Φ (ρ • Y))) (c⁻¹ * τ) (ρ⁻¹ • Ψ x) (e⁻¹ • Ψ x) v = 0 := by
        simp only [positiveLiftCoefficients, ite_true, liftApply,
          Pi.zero_apply, zero_apply, Finset.sum_const_zero]
      rw [pow_zero, one_smul, one_smul, hz, sub_zero]
      by_cases hh0 : hh = 0
      · subst hh
        rw [ite_eq_left rfl]
        have h := liftSequence_zero_degree_action Q sX sZ a b N H (Cc k) hseq
          (fun _ Y => f (Φ (ρ • Y))) (c⁻¹ * τ) ht (ρ⁻¹ • Ψ x) (e⁻¹ • Ψ x)
        simpa only [smul_smul, mul_inv_cancel₀ hρ, one_smul, hinv] using congrArg (fun z => z v) h
      · rw [ite_eq_right hh0]
        have h := liftApply_positive_grade_zero_degree Q sX sZ a b N H (Cc k) hseq hh
          (Nat.one_le_iff_ne_zero.mpr hh0) hhh (fun _ Y => f (Φ (ρ • Y)))
        exact congrArg (fun z => z (c⁻¹ * τ) (ρ⁻¹ • Ψ x) (e⁻¹ • Ψ x) v) h
    · intro n _ hn
      simp only [positiveLiftCoefficients, ite_eq_right hn, sub_self]
    · intro hn
      exact False.elim (hn (Finset.mem_range.mpr (Nat.zero_lt_succ N)))
  trans ∑ hh ∈ Finset.range (H + 1), if hh = 0 then f x v else 0
  · exact Finset.sum_congr rfl
      (fun hh hhh => hdegree hh (Nat.lt_succ_iff.mp (Finset.mem_range.mp hhh)))
  · rw [Finset.sum_eq_single 0]
    · simp only [ite_true]
    · intro hh _ hh0
      exact ite_eq_right hh0
    · intro h0
      exact False.elim (h0 (Finset.mem_range.mpr (Nat.zero_lt_succ H)))

/-- The same identity for genuine time-dependent chart data, before any chart estimates. -/
theorem pulse_positive_difference_time (Q : LiftOperatorData ι h D)
    (sX sZ : ℕ) (a b : ℝ) (N H : ℕ) (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h) (k : ℤ)
    (hseq : IsLiftSequence Q sX sZ a b N H (Cc k))
    (c ρ e εc τ : ℝ) (hc : c ≠ 0) (hρ : ρ ≠ 0) (ht : c⁻¹ * τ ∈ Set.Icc a b)
    (chart label : ℝ → Vec 2 → Vec 2) (f : ℝ → Vec 2 → ∀ i, h i) (x : Vec 2)
    (hinv : chart τ (label τ x) = x) (v : ι) :
    pulsePhysicalLift c ρ e εc N H (Cc k) chart label f τ x v -
      pulsePhysicalLift c ρ e εc N H (positiveLiftCoefficients Cc k) chart label f τ x v = f τ x v := by
  have hclock : c * (c⁻¹ * τ) = τ := by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  rw [pulsePhysicalLift_freeze_time c ρ e εc N H (Cc k) chart label f τ,
    pulsePhysicalLift_freeze_time c ρ e εc N H (positiveLiftCoefficients Cc k) chart label f τ]
  simp only [hclock]
  exact pulse_positive_difference Q sX sZ a b N H Cc k hseq c ρ e εc τ hρ ht
    (chart τ) (label τ) (f τ) x hinv v

end AVRegularity.Finite
