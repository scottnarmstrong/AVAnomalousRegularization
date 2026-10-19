-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleReference.CoreFlux
import AVRegularity.Velocity.Port.Section2FlowRegularityCore
import AVRegularity.CycleReference.ChartTestCalculus
public import AVRegularity.CycleReference.ChartIntegrandAlgebra
import AVRegularity.CycleReference.TransitionZero
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Intermediate.CycleReference.OcMeanFlux
public import AVenhance.Statements.Construction.BarNorm
import AVenhance.Infra.Construction.StreamAdmissible
import AVenhance.Infra.Section4.Amnr.SpatialPrimitive
import Mathlib.Algebra.Order.Star.Real
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Tactic.Monotonicity.Lemmas

@[expose] public section

section
open Homogenization AVenhance AVenhance.Infra.Flow
namespace AVRegularity.CycleReference

/-! Uniform bounds on compact time intervals for spatially periodic fields. -/

theorem spatial_periodic_bound_on_compact_time {E : Type*} [NormedAddCommGroup E]
    (f : ℝ × Vec 2 → E) (hf : Continuous f)
    (hper : ∀ t x k, f (t, x + latticeShift k) = f (t, x))
    (T : Set ℝ) (hT : IsCompact T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ T, ∀ x, ‖f (t, x)‖ ≤ C := by
  let U : Set (Vec 2) := Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1)
  have hU : IsCompact U := isCompact_univ_pi (fun _ => isCompact_Icc)
  obtain ⟨C, hb⟩ := (hT.prod hU).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t ht x
  let k : Fin 2 → ℤ := fun i => Int.floor (x i)
  let y := x - latticeShift k
  have hy : y ∈ U := by
    intro i _
    change 0 ≤ x i - (Int.floor (x i) : ℝ) ∧ x i - (Int.floor (x i) : ℝ) ≤ 1
    constructor <;> linarith [Int.floor_le (x i), Int.lt_floor_add_one (x i)]
  have he : f (t, y) = f (t, x) := by
    have hp := hper t y k
    simpa only [y, sub_add_cancel] using hp.symm
  rw [← he]
  exact (hb (t, y) ⟨ht, hy⟩).trans (le_max_left _ _)

theorem streamFlow_jacMatrix_spatial_periodic {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (t s : ℝ) (x : Vec 2) (k : Fin 2 → ℤ) :
    jacMatrix (fun y => AVRegularity.streamFlow φ hφ t y s) (x + latticeShift k) =
      jacMatrix (fun y => AVRegularity.streamFlow φ hφ t y s) x := by
  have hb := AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ
  have hp : ∀ r, IsZ2Periodic (streamVel φ r) := by
    intro r j y
    simpa using hb.periodic 0 j r y
  have hflow := flow_isFlow _ hφ.vel_continuous hφ.vel_lipschitz
  have he : (fun y => AVRegularity.streamFlow φ hφ t (y + latticeShift k) s) =
      (fun y => AVRegularity.streamFlow φ hφ t y s + latticeShift k) := by
    funext y
    exact flow_lattice_equivariant _ hφ.vel_lipschitz hp hflow y s t k
  have hd := congrArg (fun f : Vec 2 → Vec 2 => fderiv ℝ f x) he
  have hs := fderiv_comp_add_right (𝕜 := ℝ)
    (f := fun y => AVRegularity.streamFlow φ hφ t y s) (x := x) (latticeShift k)
  have ha := fderiv_add_const (𝕜 := ℝ)
    (f := fun y => AVRegularity.streamFlow φ hφ t y s) (x := x) (latticeShift k)
  rw [hs, ha] at hd
  ext i j
  exact congrArg (fun L : Vec 2 →L[ℝ] Vec 2 => L (basisVec j) i) hd

theorem streamFlow_jacMatrix_joint_continuous {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) :
    Continuous (fun p : ℝ × Vec 2 =>
      jacMatrix (fun y => AVRegularity.streamFlow φ hφ p.1 y s) p.2) := by
  have hG : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 =>
      AVRegularity.streamFlow φ hφ p.1 p.2 s) :=
    (streamFlow_joint_smooth hφ).comp
      (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const))
  have hd := AVRegularity.Velocity.Port.Section2FlowRegularityCore.partialFDeriv_joint_contDiff _ hG
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (continuous_apply i).comp (hd.continuous.clm_apply continuous_const)

theorem streamFlow_jacMatrix_bounded_on_compact_time {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) (T : Set ℝ) (hT : IsCompact T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ T, ∀ x i j,
      |jacMatrix (fun y => AVRegularity.streamFlow φ hφ t y s) x i j| ≤ C := by
  have hb : ∀ i j : Fin 2, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ T, ∀ x,
      |jacMatrix (fun y => AVRegularity.streamFlow φ hφ t y s) x i j| ≤ C := by
    intro i j
    have hc := ((continuous_apply j).comp ((continuous_apply i).comp
      (streamFlow_jacMatrix_joint_continuous hφ s)))
    obtain ⟨C, hC, hb⟩ := spatial_periodic_bound_on_compact_time
      (fun p : ℝ × Vec 2 => jacMatrix (fun y => AVRegularity.streamFlow φ hφ p.1 y s) p.2 i j)
      hc (fun t x k => congrArg (fun M => M i j)
        (streamFlow_jacMatrix_spatial_periodic hφ t s x k)) T hT
    exact ⟨C, hC, fun t ht x => by simpa only [Real.norm_eq_abs] using hb t ht x⟩
  choose C hC hb using hb
  refine ⟨∑ i, ∑ j, C i j, Finset.sum_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ => hC i j)), ?_⟩
  intro t ht x i j
  exact (hb i j t ht x).trans ((Finset.single_le_sum (fun j _ => hC i j)
    (Finset.mem_univ j)).trans (Finset.single_le_sum (fun i _ =>
      Finset.sum_nonneg (fun j _ => hC i j)) (Finset.mem_univ i)))

end AVRegularity.CycleReference
end

section
open MeasureTheory
namespace AVRegularity.CycleReference

/-! The square-average error is bounded by the total renewal-quiet margin length. -/

theorem quietMargin_integral_le (f : ℝ → ℝ) (A B P : ℝ) (hP : 0 ≤ P) (hgap : 4 * P ≤ B - A)
    (hi : ∀ a b, IntervalIntegrable f volume a b) (hf : ∀ t, f t ≤ 1)
    (hzero : ∀ t ∈ Set.Icc (A + 2 * P) (B - 2 * P), f t = 0) :
    (∫ t in A..B, f t) ≤ 4 * P := by
  have hleft : (∫ t in A..(A + 2 * P), f t) ≤ 2 * P := by
    calc
      _ ≤ ∫ t in A..(A + 2 * P), (1 : ℝ) :=
        intervalIntegral.integral_mono_on (by linarith) (hi _ _) intervalIntegrable_const (fun t _ => hf t)
      _ = _ := by simp
  have hright : (∫ t in (B - 2 * P)..B, f t) ≤ 2 * P := by
    calc
      _ ≤ ∫ t in (B - 2 * P)..B, (1 : ℝ) :=
        intervalIntegral.integral_mono_on (by linarith) (hi _ _) intervalIntegrable_const (fun t _ => hf t)
      _ = _ := by simp
  have hmid : (∫ t in (A + 2 * P)..(B - 2 * P), f t) = 0 := by
    calc
      _ = ∫ t in (A + 2 * P)..(B - 2 * P), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        apply hzero t
        simpa only [Set.uIcc_of_le (by linarith : A + 2 * P ≤ B - 2 * P)] using ht
      _ = 0 := by simp
  have hsum := intervalIntegral.integral_add_adjacent_intervals (hi A (A + 2 * P))
    (hi (A + 2 * P) (B - 2 * P))
  have hsum' := intervalIntegral.integral_add_adjacent_intervals (hi A (B - 2 * P)) (hi (B - 2 * P) B)
  linarith only [hleft, hright, hmid, hsum, hsum']

theorem square_quiet_margin_block_bound {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (l : ℤ) :
    (∫ t in (((l : ℝ) - 1 / 2) * ocTauPP α q Λ m)..
        (((l : ℝ) + 1 / 2) * ocTauPP α q Λ m),
      fastSquareSum ζ (ocTau α q Λ m) t - pulseSquareSum α q Λ ζ m t) ≤
      4 * ocTauP α q Λ m := by
  have hτ := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
  have hP : 0 ≤ ocTauP α q Λ m := hτ.le.trans (pulse_time_scale_relations hΛ).1
  apply quietMargin_integral_le _ _ _ _ hP
  · have h := (pulse_time_scale_relations (α := α) (q := q) (m := m) hΛ).2
    nlinarith only [h]
  · intro a b
    exact (fastSquareSum_intervalIntegrable hζ hτ a b).sub (pulseSquareSum_intervalIntegrable hΛ hζ a b)
  · intro t
    have h := pulseSquareSum_le_fast (α := α) (q := q) (m := m) hΛ hζ t
    have hfast := fastSquareSum_range hζ (ocTau α q Λ m) t
    linarith only [h.1, hfast.2]
  · intro t ht
    rw [pulseSquareSum_eq_fast_on_plateau hΛ hζ l t ht.1 ht.2, sub_self]

theorem square_quiet_margin_cycle_bound {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) :
    (∫ t in (-ocTauPP α q Λ m / 2)..(-ocTauPP α q Λ m / 2 + 4 * ocTauPP α q Λ m),
      fastSquareSum ζ (ocTau α q Λ m) t - pulseSquareSum α q Λ ζ m t) ≤
      16 * ocTauP α q Λ m := by
  let h := ocTauPP α q Λ m
  let P := ocTauP α q Λ m
  let f := fun t => fastSquareSum ζ (ocTau α q Λ m) t - pulseSquareSum α q Λ ζ m t
  have hh : 0 < h := AVRegularity.Construction.Stream.ocTauPP_pos hΛ
  have hτ := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
  have hi : ∀ a b, IntervalIntegrable f volume a b := fun a b =>
    (fastSquareSum_intervalIntegrable hζ hτ a b).sub (pulseSquareSum_intervalIntegrable hΛ hζ a b)
  have hc : (-4 * P / h) * h = -4 * P := by field_simp
  have hb : ∀ l : ℤ, (-4 * P / h) * h ≤
      ∫ t in (((l : ℝ) - 1 / 2) * h)..(((l : ℝ) + 1 / 2) * h), -f t := by
    intro l
    rw [hc, intervalIntegral.integral_neg]
    simpa only [neg_mul] using neg_le_neg
      (square_quiet_margin_block_bound (α := α) (q := q) (m := m) hΛ hζ l)
  have hl := consecutive_blocks_lower (fun t => -f t) h (-4 * P / h)
    (fun a b => (hi a b).neg) hb 0 4
  rw [intervalIntegral.integral_neg] at hl
  norm_num at hl
  have hstart : -((1 / 2 : ℝ) * h) = -h / 2 := by ring
  have hend : (7 / 2 : ℝ) * h = -h / 2 + 4 * h := by ring
  rw [hstart, hend] at hl
  have he : (4 : ℝ) * (-(4 * P) / h) * h = -16 * P := by field_simp; ring
  rw [he] at hl
  apply neg_le_neg_iff.mp
  simpa only [neg_mul] using hl

end AVRegularity.CycleReference
end

section
namespace AVRegularity.CycleReference

/-! The integrated instantaneous-memory error fits inside a renewal quiet margin. -/

theorem renewal_memory_scale_le_quiet_margin {α q : ℝ} {Λ m : ℕ}
    (hΛ : 1 ≤ Λ) (hE : 0 < ocEpsilon q Λ (m - 1))
    (hE1 : ocEpsilon q Λ (m - 1) ≤ 1) (hd : 0 ≤ ocDelta α q) :
    ocTauPP α q Λ m * ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q) ≤
      9 * ocTauP α q Λ m := by
  have hP : 0 ≤ ocTauP α q Λ m :=
    (AVRegularity.Construction.Stream.ocTau_pos hΛ).le.trans (pulse_time_scale_relations hΛ).1
  have hL : (ocL α q Λ m : ℝ) ≠ 0 := by
    have hn : 0 < ocL α q Λ m := by unfold ocL; omega
    exact_mod_cast hn.ne'
  have heq : ocTauPP α q Λ m = (ocL α q Λ m : ℝ) * ocTauP α q Λ m := by
    rw [ocTauP]
    field_simp
  have h := mul_le_mul_of_nonneg_right (ocL_power_bounds hE hE1 hd).2
    (Real.rpow_pos_of_pos hE (4 * ocDelta α q)).le
  have hpow : ocEpsilon q Λ (m - 1) ^ (-ocDelta α q) *
      ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q) =
      ocEpsilon q Λ (m - 1) ^ (3 * ocDelta α q) := by
    rw [← Real.rpow_add hE]
    congr 1
    ring
  rw [mul_assoc, hpow] at h
  have hsmall : ocEpsilon q Λ (m - 1) ^ (3 * ocDelta α q) ≤ 1 :=
    Real.rpow_le_one hE.le hE1 (by positivity)
  have hsmall9 : 9 * ocEpsilon q Λ (m - 1) ^ (3 * ocDelta α q) ≤ 9 := by
    linarith only [hsmall]
  have h' := h.trans hsmall9
  rw [heq]
  have h'' := mul_le_mul_of_nonneg_right h' hP
  convert h'' using 1; ring

end AVRegularity.CycleReference
end

section
open Homogenization AVenhance AVenhance.Infra.Flow
namespace AVRegularity.CycleReference

/-! Compact-time derivative bounds for the inverse fixed-start chart. -/

theorem inverseStreamFlow_jacMatrix_joint_continuous {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) :
    Continuous (fun p : ℝ × Vec 2 =>
      jacMatrix (fun y => AVRegularity.streamFlow φ hφ s y p.1) p.2) := by
  have hG : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 =>
      AVRegularity.streamFlow φ hφ s p.2 p.1) :=
    (streamFlow_joint_smooth hφ).comp
      (contDiff_const.prodMk (contDiff_snd.prodMk contDiff_fst))
  have hd := AVRegularity.Velocity.Port.Section2FlowRegularityCore.partialFDeriv_joint_contDiff _ hG
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (continuous_apply i).comp (hd.continuous.clm_apply continuous_const)

theorem inverseStreamFlow_jacMatrix_bounded_on_compact_time {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) (T : Set ℝ) (hT : IsCompact T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ T, ∀ x i j,
      |jacMatrix (fun y => AVRegularity.streamFlow φ hφ s y t) x i j| ≤ C := by
  have hb : ∀ i j : Fin 2, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ T, ∀ x,
      |jacMatrix (fun y => AVRegularity.streamFlow φ hφ s y t) x i j| ≤ C := by
    intro i j
    have hc := (continuous_apply j).comp ((continuous_apply i).comp
      (inverseStreamFlow_jacMatrix_joint_continuous hφ s))
    obtain ⟨C, hC, hb⟩ := spatial_periodic_bound_on_compact_time
      (fun p : ℝ × Vec 2 => jacMatrix (fun y => AVRegularity.streamFlow φ hφ s y p.1) p.2 i j)
      hc (fun t x k => congrArg (fun M => M i j)
        (streamFlow_jacMatrix_spatial_periodic hφ s t x k)) T hT
    exact ⟨C, hC, fun t ht x => by simpa only [Real.norm_eq_abs] using hb t ht x⟩
  choose C hC hb using hb
  refine ⟨∑ i, ∑ j, C i j, Finset.sum_nonneg (fun i _ =>
    Finset.sum_nonneg (fun j _ => hC i j)), ?_⟩
  intro t ht x i j
  exact (hb i j t ht x).trans ((Finset.single_le_sum (fun j _ => hC i j)
    (Finset.mem_univ j)).trans (Finset.single_le_sum (fun i _ =>
      Finset.sum_nonneg (fun j _ => hC i j)) (Finset.mem_univ i)))

end AVRegularity.CycleReference
end

section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleReference

/-! Euclidean transition arrays extracted from the inverse-flow seminorm. -/

theorem jacMatrix_displacement_entry_bound {f : Vec 2 → Vec 2}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {R B : ℝ} (hR : 0 < R) (hB : 0 ≤ B)
    (hb : ∀ n i a, barNorm n R
      (fun x => jacMatrix f x i a - (1 : Matrix (Fin 2) (Fin 2) ℝ) i a) ≤ ENNReal.ofReal B)
    (x : Vec 2) (i a : Fin 2) :
    |jacMatrix f x i a - (1 : Matrix (Fin 2) (Fin 2) ℝ) i a| ≤ B := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun y => jacMatrix f y i a - (1 : Matrix (Fin 2) (Fin 2) ℝ) i a) :=
    (jacMatrix_entry_smooth hf i a).sub contDiff_const
  have ht := AVenhance.Infra.Section4.amnr_partial_norm_le_of_barNorm _ 0
    (hs.of_le (by simp)) hR hB (hb 0 i a) x (fun j => j.elim0)
  simpa only [iteratedFDeriv_zero_apply, Nat.factorial_zero, Nat.cast_one, Nat.cast_zero,
    pow_zero, zero_add, one_pow, mul_one, div_one, Real.norm_eq_abs] using ht

theorem derivArrayNorm_from_jacobian_bar {f : Vec 2 → Vec 2}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {R B : ℝ} (hR : 0 < R) (hB : 0 ≤ B)
    (hb : ∀ n i a, barNorm n R
      (fun x => jacMatrix f x i a - (1 : Matrix (Fin 2) (Fin 2) ℝ) i a) ≤ ENNReal.ofReal B)
    (n : ℕ) (hn : 1 ≤ n) (x : Vec 2) :
    derivArrayNorm f (n + 1) x ≤ (2 : ℝ) ^ (n + 2) *
      (B * (n.factorial : ℝ) * R ^ n) := by
  have hp := orderedPartial_component_bound hf hR hB hb n hn
  have hden : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    have hn' : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  have hnum : 0 ≤ B * (n.factorial : ℝ) * R ^ n := by positivity
  apply derivArrayNorm_le_components hnum
  intro w i
  exact (hp w x i).trans (div_le_self hnum hden)

end AVRegularity.CycleReference
end

section
open Homogenization AVenhance
open scoped Matrix
namespace AVRegularity.CycleReference

/-! The stream increment and its velocity in material coordinates. -/

theorem inverse_sigma_eq_sigma_transpose (F : Matrix (Fin 2) (Fin 2) ℝ)
    (hd : F.det = 1) : F⁻¹ * sigmaMat = sigmaMat * Fᵀ := by
  rw [Matrix.inv_def, hd]
  simp only [Ring.inverse_one, one_smul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, sigmaMat, Matrix.adjugate_fin_two]

noncomputable def chartStreamIncrement {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) (Ψ : ℝ → Vec 2 → ℝ) (t : ℝ) (y : Vec 2) : ℝ :=
  Ψ t (AVRegularity.streamFlow φ hφ t y s) - φ t (AVRegularity.streamFlow φ hφ t y s)

theorem chartStreamIncrement_smooth {φ Ψ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (hΨ : IsAdmissibleStream Ψ) (s : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => chartStreamIncrement hφ s Ψ p.1 p.2) :=
  (streamFlow_test_smooth hφ s hΨ.1).sub (streamFlow_test_smooth hφ s hφ.1)

theorem chartStreamIncrement_velocity {φ Ψ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (hΨ : IsAdmissibleStream Ψ) (s t : ℝ) (y : Vec 2) :
    streamVel (chartStreamIncrement hφ s Ψ) t y =
      (jacMatrix (fun x => AVRegularity.streamFlow φ hφ t x s) y)⁻¹.mulVec
        (streamVel Ψ t (AVRegularity.streamFlow φ hφ t y s) -
          streamVel φ t (AVRegularity.streamFlow φ hφ t y s)) := by
  let X := fun x => AVRegularity.streamFlow φ hφ t x s
  have hX := (streamFlow_spatial_smooth hφ t s).differentiable (by simp) y
  have hΨt : DifferentiableAt ℝ (Ψ t) (X y) := (hΨ.1.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) (X y)
  have hφt : DifferentiableAt ℝ (φ t) (X y) := (hφ.1.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) (X y)
  have hΨX : DifferentiableAt ℝ (fun x => Ψ t (X x)) y := by
    simpa only [Function.comp_def] using hΨt.comp y hX
  have hφX : DifferentiableAt ℝ (fun x => φ t (X x)) y := by
    simpa only [Function.comp_def] using hφt.comp y hX
  have hg : spaceGrad (chartStreamIncrement hφ s Ψ t) y =
      (jacMatrix X y)ᵀ.mulVec (spaceGrad (Ψ t) (X y) - spaceGrad (φ t) (X y)) := by
    unfold chartStreamIncrement spaceGrad
    ext i
    have hd := fderiv_sub hΨX hφX
    change (fderiv ℝ (fun x => Ψ t (X x) - φ t (X x)) y) (basisVec i) = _
    have hs : (fun x => Ψ t (X x) - φ t (X x)) =
      (fun x => Ψ t (X x)) - (fun x => φ t (X x)) := rfl
    rw [hs, hd]
    change spaceGrad (fun x => Ψ t (X x)) y i - spaceGrad (fun x => φ t (X x)) y i = _
    rw [spaceGrad_comp_jacMatrix hΨt hX, spaceGrad_comp_jacMatrix hφt hX,
      Matrix.mulVec_sub]
    rfl
  unfold streamVel
  rw [hg]
  rw [Matrix.mulVec_mulVec, ← inverse_sigma_eq_sigma_transpose _
    (streamFlow_jacMatrix_det_one hφ t s y), ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]

theorem chartStreamIncrement_eq_ocPulseStream {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) {Φ : ℕ → ℝ → Vec 2 → ℝ} (hseq : IsOCStreamSeq α q Λ ζ Φ)
    (hm : 1 ≤ m) (hφ : IsAdmissibleStream (Φ (m - 1))) (l : ℤ) (t : ℝ)
    (ht : ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ t ∧
      t ≤ ((l : ℝ) + 1 / 2) * ocTauPP α q Λ m) (y : Vec 2) :
    chartStreamIncrement hφ ((l : ℝ) * ocTauPP α q Λ m) (Φ m) t y =
      ocPulseStream α q Λ ζ m t y := by
  obtain ⟨hprev, hrec⟩ := hseq.2 m hm
  have hh : hprev = hφ := Subsingleton.elim _ _
  rw [hh] at hrec
  unfold chartStreamIncrement
  rw [hrec]
  change ocNextStream α q Λ ζ m (Φ (m - 1)) hφ t (ocChart α q Λ m (Φ (m - 1)) hφ l t y) -
    Φ (m - 1) t (ocChart α q Λ m (Φ (m - 1)) hφ l t y) = _
  rw [ocNextStream_in_chart hΛ hφ l t ht]
  ring

end AVRegularity.CycleReference
end

section
open MeasureTheory
namespace AVRegularity.CycleReference

/-! Mean enhancement in the primitive time-scale variables. -/

theorem refFlux_mean_enhancement_scale {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (α q : ℝ) (Λ m : ℕ), 1 ≤ Λ → ∀ ν : ℝ, 0 < ν →
      |ocMeanFlux α q Λ ζ m ν - ν - (9 / 40) * ocHStar α q Λ m ν| ≤
        ocHStar α q Λ m ν / 2 * (K / (ocMu q Λ m ν * ocTau α q Λ m) +
          4 * ocTauP α q Λ m / ocTauPP α q Λ m) := by
  obtain ⟨K, hK, herr⟩ := refFlux_trace_instantaneous_error hζ
  refine ⟨K, hK, ?_⟩
  intro α q Λ m hΛ ν hν
  let h := ocTauPP α q Λ m
  let T := 4 * h
  let s := -h / 2
  let H := ocHStar α q Λ m ν
  let D := K / (ocMu q Λ m ν * ocTau α q Λ m)
  let F := fastSquareSum ζ (ocTau α q Λ m)
  let p := pulseSquareSum α q Λ ζ m
  let R := fun t => Matrix.trace (ocRefFlux α q Λ ζ m ν t)
  let E := fun t => R t - 2 * ν - H * p t
  let J := ∫ t in s..(s + T), F t - p t
  have hh : 0 < h := AVRegularity.Construction.Stream.ocTauPP_pos hΛ
  have hT : 0 < T := by dsimp [T]; positivity
  have hH : 0 < H := ocHStar_pos hΛ hν
  have hτ := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
  have hiR : IntervalIntegrable R volume s (s + T) := refFlux_trace_intervalIntegrable hΛ hζ hν _ _
  have hip : IntervalIntegrable p volume s (s + T) := pulseSquareSum_intervalIntegrable hΛ hζ _ _
  have hiF : IntervalIntegrable F volume s (s + T) := fastSquareSum_intervalIntegrable hζ hτ _ _
  have hJ : 0 ≤ J := by
    apply intervalIntegral.integral_nonneg_of_forall (by linarith only [hT])
    intro t
    exact sub_nonneg.mpr (pulseSquareSum_le_fast hΛ hζ t).2
  have hJup : J ≤ 16 * ocTauP α q Λ m := square_quiet_margin_cycle_bound hΛ hζ
  have hE : |∫ t in s..(s + T), E t| ≤ H * D * T := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := s) (b := s + T) (f := E) (C := H * D)
      (fun t _ => by simpa only [Real.norm_eq_abs] using herr α q Λ m hΛ ν hν t)
    simpa only [Real.norm_eq_abs, add_sub_cancel_left, abs_of_pos hT] using hb
  have hformula : (∫ t in s..(s + T), E t) =
      2 * T * (ocMeanFlux α q Λ ζ m ν - ν - (9 / 40) * H) + H * J := by
    have hF : (∫ t in s..(s + T), F t) = T * (9 / 20) := fastSquareSum_cycle_average hΛ hζ s
    have hR : (∫ t in s..(s + T), R t) = 2 * ocMeanFlux α q Λ ζ m ν * T :=
      refFlux_window_trace_integral hΛ hζ hν s
    dsimp [E, J]
    rw [intervalIntegral.integral_sub (hiR.sub intervalIntegrable_const) (hip.const_mul H),
      intervalIntegral.integral_sub hiR intervalIntegrable_const, intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hiF hip, hR, hF]
    simp only [smul_eq_mul, add_sub_cancel_left]
    ring
  have hscaled : 2 * T * |ocMeanFlux α q Λ ζ m ν - ν - (9 / 40) * H| ≤
      H * D * T + H * (16 * ocTauP α q Λ m) := by
    calc
      _ = |(∫ t in s..(s + T), E t) - H * J| := by
        rw [hformula, add_sub_cancel_right, abs_mul, abs_of_pos (by positivity : 0 < 2 * T)]
      _ ≤ |∫ t in s..(s + T), E t| + |H * J| := abs_sub _ _
      _ ≤ H * D * T + H * (16 * ocTauP α q Λ m) := by
        rw [abs_of_nonneg (mul_nonneg hH.le hJ)]
        exact add_le_add hE (mul_le_mul_of_nonneg_left hJup hH.le)
  apply (mul_le_mul_iff_of_pos_left (show 0 < 2 * T by positivity)).mp
  convert hscaled using 1
  dsimp [H, D, T, h]
  have hne : ocTauPP α q Λ m ≠ 0 := hh.ne'
  field_simp
  ring

end AVRegularity.CycleReference
end
