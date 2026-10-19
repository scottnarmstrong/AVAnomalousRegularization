-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import AVRegularity.CycleComparison.Lift.NormalizedCellB1MixedGrading
public import AVRegularity.Statements.Intermediate.CycleComparison.IsBoxSmooth
public import AVRegularity.CycleComparison.Lift.TransverseModeKernel
public import AVRegularity.Statements.Intermediate.CycleComparison.FieldCellMean
public import AVRegularity.Sobolev.Basic

section
@[expose] public noncomputable section
namespace AVRegularity.CycleComparison.Lift

/-! Multiplication by a unit Fourier phase does not enlarge real parameter jets. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem unit_complex_mul_contDiff (p : ℕ) (f : E → ℂ)
    (hf : ContDiff ℝ (p : ℕ∞) f) (c : ℂ) :
    ContDiff ℝ (p : ℕ∞) (fun x => c * f x) := by
  let A : ℂ →L[ℝ] ℂ := c • ContinuousLinearMap.id ℝ ℂ
  simpa only [A, Function.comp_def, smul_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul] using! A.contDiff.comp hf

theorem norm_iteratedFDeriv_unit_complex_mul_le (p q : ℕ) (hq : q ≤ p)
    (f : E → ℂ) (hf : ContDiff ℝ (p : ℕ∞) f) (c : ℂ) (hc : ‖c‖ = 1) (x : E) :
    ‖iteratedFDeriv ℝ q (fun y => c * f y) x‖ ≤ ‖iteratedFDeriv ℝ q f x‖ := by
  let A : ℂ →L[ℝ] ℂ := c • ContinuousLinearMap.id ℝ ℂ
  have hA : ‖A‖ = 1 := by simp only [A, norm_smul, ContinuousLinearMap.norm_id, hc, mul_one]
  have he := A.norm_iteratedFDeriv_comp_left (x := x) hf.contDiffAt
    (n := q) (by exact_mod_cast hq)
  simpa only [A, Function.comp_def, smul_apply, ContinuousLinearMap.id_apply,
    smul_eq_mul, hA, one_mul] using! he

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVenhance.Infra.Torus
namespace AVRegularity.CycleComparison.Lift

/-! Scalar duals commute with the actual weighted Fourier coefficient jets. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem weighted_integral_dual_iteratedFDeriv (p r : ℕ) (hr : r ≤ p)
    (f : Vec 2 → Vec 2 → E) (hf : ∀ X, Continuous (f X))
    (w : Vec 2 → ℝ) (hw : Continuous w)
    (hc : ContDiff ℝ (p : ℕ∞) (fun Y => ∫ z in AVenhance.unitCube, w z • f Y z))
    (l : E →L[ℝ] ℝ) (X : Vec 2) :
    iteratedFDeriv ℝ r (fun Y => ∫ z in AVenhance.unitCube, w z • l (f Y z)) X =
      l.compContinuousMultilinearMap
        (iteratedFDeriv ℝ r (fun Y => ∫ z in AVenhance.unitCube, w z • f Y z) X) := by
  have he : (fun Y => ∫ z in AVenhance.unitCube, w z • l (f Y z)) =
      l ∘ (fun Y => ∫ z in AVenhance.unitCube, w z • f Y z) := by
    funext Y
    have hi : IntegrableOn (fun z => w z • f Y z) AVenhance.unitCube :=
      (Calculus.continuous_integrableOn_unitCell (hw.smul (hf Y))).congr_set_ae
        unitCell_ae_eq_unitCube.symm
    simpa only [map_smul, Function.comp_apply] using! l.integral_comp_comm hi
  rw [he]
  exact l.iteratedFDeriv_comp_left hc.contDiffAt (by exact_mod_cast hr)

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public section
namespace AVRegularity.CycleComparison.Lift

/-! A vanishing zero tested order becomes the divergence-form cutoff at order two. -/

section
variable {E : Type*} [AddCommMonoid E]

theorem sum_range_zero_order_shift (n : ℕ) (hn : 1 ≤ n) (f : ℕ → E) (hzero : f 0 = 0) :
    (∑ m ∈ Finset.range n, f m) = ∑ d ∈ Finset.Icc 2 n, f (d - 1) := by
  rw [Finset.sum_range_eq_add_Ico f (by omega), hzero, zero_add]
  have he := Finset.sum_Ico_add_right_sub_eq (f := f) 1 n 1
  simpa only [Finset.Ico_add_one_right_eq_Icc] using he.symm
end

/-! The flux predecessor leaves an extra slow derivative without enlarging the reserve. -/

theorem ambient_flux_predecessor_reserve (P Q D H R hh n j : ℕ)
    (hhh : 1 ≤ hh) (hhH : hh ≤ H) (hn : 2 ≤ n) (hnR : n ≤ R) (hj : j ≤ n - 1) :
    P + 1 + j ≤ ambientDegreeSlowReserve P R (n - 1 - j) ∧
      D - 1 - j ≤ ambientDegreeFastReserve Q D H R (hh - 1) (n - 1 - j) := by
  constructor
  · unfold ambientDegreeSlowReserve
    omega
  · have hheight : 1 ≤ H - (hh - 1) := by omega
    have hD : D ≤ (H - (hh - 1)) * D := by
      simpa only [one_mul] using Nat.mul_le_mul_right D hheight
    unfold ambientDegreeFastReserve
    omega

/-! Quotient and remainder identify each finite degree block in the scalar recursion. -/

theorem ambientRecurrenceRank_div (R hh n : ℕ) (hn : n ≤ R) :
    ambientRecurrenceRank R hh n / (R + 1) = hh := by
  unfold ambientRecurrenceRank
  rw [Nat.mul_comm hh, Nat.mul_add_div (by omega : 0 < R + 1),
    Nat.div_eq_of_lt (by omega : n < R + 1)]
  omega

theorem ambientRecurrenceRank_mod (R hh n : ℕ) (hn : n ≤ R) :
    ambientRecurrenceRank R hh n % (R + 1) = n := by
  unfold ambientRecurrenceRank
  simp only [Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_eq_of_lt (by omega : n < R + 1)]

/-! The common recurrence reserve is paid by the original data, including source degree zero. -/

theorem ambientDegreeFastReserve_data (Q D H R hh n : ℕ) (hn : 1 ≤ n) (hR : n ≤ R) :
    ambientDegreeFastReserve Q D H R hh n + 1 ≤ Q + H * D + 2 * R := by
  unfold ambientDegreeFastReserve
  have hm := Nat.mul_le_mul_right D (Nat.sub_le H hh)
  omega

theorem ambientDegreeFastReserve_two (Q D H R hh n : ℕ) (hQ : 2 ≤ Q) :
    2 ≤ ambientDegreeFastReserve Q D H R hh n := by
  unfold ambientDegreeFastReserve
  omega

theorem ambient_source_slow_box_supported (P N D n j : ℕ)
    (hn : n ≤ N + D) (hj : j ≤ n) (hpred : n - j ≤ N) :
    max D (ambientDegreeSlowReserve P (N + D) n + j) ≤
      ambientDegreeSlowReserve P (N + D) (n - j) := by
  rw [ambientDegreeSlowReserve_source P (N + D) n j hn hj]
  unfold ambientDegreeSlowReserve
  omega

theorem ambient_source_fast_box_supported (Q N D H hh n j : ℕ)
    (hhpos : 1 ≤ hh) (hhH : hh ≤ H) (hn : n ≤ N + D) (hj : j ≤ n) (hjD : j ≤ D) :
    max D (ambientDegreeFastReserve Q D H (N + D) hh n + D - j) ≤
      ambientDegreeFastReserve Q D H (N + D) (hh - 1) (n - j) := by
  have hcost := ambientDegreeFastReserve_source Q D H (N + D) hh n j hhpos hhH hn hj hjD
  have he : H - (hh - 1) = (H - hh) + 1 := by omega
  have hcount : ambientDegreeFastReserve Q D H (N + D) hh n + D - j =
      ambientDegreeFastReserve Q D H (N + D) hh n + (D - j) := by omega
  rw [hcount]
  apply max_le _ hcost
  unfold ambientDegreeFastReserve
  rw [he, Nat.add_mul, Nat.one_mul]
  omega

/-! Earlier degrees and lower source heights retain at least the current rectangular reserve. -/

theorem ambientDegreeSlowReserve_mono (P R n m : ℕ) (hm : m ≤ n) :
    ambientDegreeSlowReserve P R n ≤ ambientDegreeSlowReserve P R m := by
  unfold ambientDegreeSlowReserve
  omega

theorem ambientDegreeFastReserve_mono (Q D H R hh h' n m : ℕ)
    (hh' : h' ≤ hh) (hm : m ≤ n) :
    ambientDegreeFastReserve Q D H R hh n ≤ ambientDegreeFastReserve Q D H R h' m := by
  have hs : H - hh ≤ H - h' := by omega
  have hp := Nat.mul_le_mul_right D hs
  unfold ambientDegreeFastReserve
  omega

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleComparison.Lift

/-! Scalar majorants for the uncentered and mean parts of the lift recurrence. -/

def ambientUncenteredScalarBudget (D hh n : ℕ) (B : ℕ → ℕ → ℝ)
    (K₁ K₂ : ℝ) (Ksource : ℕ → ℝ) : ℝ :=
  (if 1 ≤ n then K₁ * B hh (n - 1) else 0) +
  (if 2 ≤ n then K₂ * B hh (n - 2) else 0) +
  (if 1 ≤ hh then ∑ j ∈ Finset.range (min D n + 1),
    Ksource j * B (hh - 1) (n - j) else 0)

theorem ambientUncenteredScalarBudget_nonneg (D hh n : ℕ) (B : ℕ → ℕ → ℝ)
    (K₁ K₂ : ℝ) (Ksource : ℕ → ℝ) (hB : ∀ h m, 0 ≤ B h m)
    (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂) (hKs : ∀ j, 0 ≤ Ksource j) :
    0 ≤ ambientUncenteredScalarBudget D hh n B K₁ K₂ Ksource := by
  unfold ambientUncenteredScalarBudget
  apply add_nonneg
  · apply add_nonneg
    · split_ifs <;> first | exact mul_nonneg hK₁ (hB _ _) | exact le_refl 0
    · split_ifs <;> first | exact mul_nonneg hK₂ (hB _ _) | exact le_refl 0
  · split_ifs
    · exact Finset.sum_nonneg fun j _ => mul_nonneg (hKs j) (hB _ _)
    · exact le_refl 0

theorem ambientUncenteredScalarBudget_congr_earlier (R D hh n : ℕ)
    (hn : n ≤ R) (B C : ℕ → ℕ → ℝ)
    (heq : ∀ h m, ambientRecurrenceRank R h m < ambientRecurrenceRank R hh n →
      B h m = C h m) (K₁ K₂ : ℝ) (Ksource : ℕ → ℝ) :
    ambientUncenteredScalarBudget D hh n B K₁ K₂ Ksource =
      ambientUncenteredScalarBudget D hh n C K₁ K₂ Ksource := by
  unfold ambientUncenteredScalarBudget
  congr 1
  · congr 1
    · split_ifs with h
      · rw [heq hh (n - 1) (ambientRecurrenceRank_degree R hh n 1 (by omega) h)]
      · rfl
    · split_ifs with h
      · rw [heq hh (n - 2) (ambientRecurrenceRank_degree R hh n 2 (by omega) h)]
      · rfl
  · split_ifs with h
    · apply Finset.sum_congr rfl
      intro j _
      rw [heq (hh - 1) (n - j) (ambientRecurrenceRank_source R hh n j h hn)]
    · rfl

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! Absolute series commute with each interval integral inside the finite time window. -/

variable {J E : Type*} [Countable J] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem boundedTimeSeries_intervalIntegral_tsum (f : J → ℝ → E) (B : J → ℝ)
    (hB : Summable B) (a b : ℝ)
    (hm : ∀ j, AEStronglyMeasurable (f j) (volume.restrict (Icc a b)))
    (hb : ∀ j t, t ∈ Icc a b → ‖f j t‖ ≤ B j)
    (s t : ℝ) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    (∫ r in s..t, ∑' j, f j r) = ∑' j, ∫ r in s..t, f j r := by
  simp only [intervalIntegral.integral_of_le hst]
  have hsub : Ioc s t ⊆ Icc a b := fun r hr => ⟨hs.1.trans hr.1.le, hr.2.trans ht.2⟩
  apply boundedSeries_integral_tsum f B hB
    (fun j => (hm j).mono_measure (Measure.restrict_mono hsub le_rfl))
  intro j
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  exact hb j r (hsub hr)

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Zeroth fast jets recover all reserved jointly continuous slow jets. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem boxSmooth_slow_jet_continuous {p q : ℕ} {f : Vec 2 → Vec 2 → E}
    (hf : IsBoxSmooth p q f) (r : ℕ) (hr : r ≤ p) :
    Continuous (fun x : Vec 2 × Vec 2 => iteratedFDeriv ℝ r (fun X => f X x.2) x.1) := by
  let c0 := (continuousMultilinearCurryFin0 ℝ (Vec 2) E).toContinuousLinearEquiv
  let L := c0.continuousMultilinearMapCongrRight (fun _ : Fin r => Vec 2)
  have hc := L.continuous.comp (hf.2.2 r 0 hr (Nat.zero_le _))
  apply hc.congr
  intro x
  have he : (fun X => f X x.2) = c0 ∘ (fun X => iteratedFDeriv ℝ 0 (f X) x.2) := by
    funext X
    rfl
  rw [he, c0.iteratedFDeriv_comp_left]
  rfl
end

/-! The zeroth fast jet recovers the original slow field without losing regularity. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem boxSmooth_slow_contDiff {sX sZ : ℕ} {f : Vec 2 → Vec 2 → E}
    (hf : IsBoxSmooth sX sZ f) (z : Vec 2) :
    ContDiff ℝ (sX : ℕ∞) (fun X => f X z) := by
  have hh := hf.2.1 0 (Nat.zero_le _) z
  have he : (fun X => f X z) =
      (continuousMultilinearCurryFin0 ℝ (Vec 2) E) ∘
        (fun X => iteratedFDeriv ℝ 0 (f X) z) := by
    funext X
    rfl
  rw [he]
  exact (continuousMultilinearCurryFin0 ℝ (Vec 2) E).contDiff.comp hh

theorem boxSmooth_continuous {sX sZ : ℕ} {f : Vec 2 → Vec 2 → E}
    (hf : IsBoxSmooth sX sZ f) : Continuous (Function.uncurry f) := by
  have hh := hf.2.2 0 0 (Nat.zero_le _) (Nat.zero_le _)
  have he : Function.uncurry f =
      (continuousMultilinearCurryFin0 ℝ (Vec 2) E) ∘
        (continuousMultilinearCurryFin0 ℝ (Vec 2)
          (ContinuousMultilinearMap ℝ (fun _ : Fin 0 => Vec 2) E)) ∘
        (fun p : Vec 2 × Vec 2 =>
          iteratedFDeriv ℝ 0 (fun X => iteratedFDeriv ℝ 0 (f X) p.2) p.1) := by
    funext p
    rfl
  rw [he]
  exact (continuousMultilinearCurryFin0 ℝ (Vec 2) E).continuous.comp
    ((continuousMultilinearCurryFin0 ℝ (Vec 2) _).continuous.comp hh)
end

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! Centered primitive bounds on the fast unit interval require no periodic extension. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem centeredIntervalPrimitive_unit_norm_le (f : ℝ → E)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ r, ‖f r‖ ≤ C)
    (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    ‖centeredIntervalPrimitive f r‖ ≤ 2 * C := by
  have hanchor (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
      ‖∫ y in (0 : ℝ)..s, f y‖ ≤ C := by
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := s) (fun y _ => hb y)
    simp only [sub_zero, abs_of_nonneg hs.1] at hi
    exact hi.trans ((mul_le_mul_of_nonneg_left hs.2 hC).trans_eq (mul_one C))
  have hcenter : ‖∫ s in (0 : ℝ)..1, ∫ y in (0 : ℝ)..s, f y‖ ≤ C := by
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (fun s hs => by
        have hs' : s ∈ Set.Ioc (0 : ℝ) 1 := by
          simpa only [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
        exact hanchor s ⟨hs'.1.le, hs'.2⟩)
    simpa only [sub_zero, abs_one, mul_one] using hi
  exact (norm_sub_le _ _).trans ((add_le_add (hanchor r hr) hcenter).trans_eq
    (by ring : C + C = 2 * C))

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public section
namespace AVRegularity.CycleComparison.Lift

/-! The original setting reserve pays for the explicit finite source construction. -/

theorem constructedLiftExistence_slow_reserve (K N D H : ℕ) (hD : 2 ≤ D) :
    (K + N + D + 2) + (N + D) ≤ K + 4 * (H + 1) * (N + D) ^ 2 := by
  have hs : 2 ≤ N + D := by omega
  have hsq : 2 * (N + D) + 2 ≤ 4 * (N + D) ^ 2 := by nlinarith
  have hmul : 4 * (N + D) ^ 2 ≤ 4 * (H + 1) * (N + D) ^ 2 := by
    exact Nat.mul_le_mul_right _ (by omega)
  omega

theorem constructedLiftExistence_fast_reserve (k L D H N hh n : ℕ)
    (hD : 2 ≤ D) (hn : n ≤ N) :
    max (k + 1) (L + 2) ≤ ambientDegreeFastReserve (max k (L + 2)) D H (N + D) hh n := by
  have hd := ambientDegreeFastReserve_original_orders (max k (L + 2)) D H N hh n hn
  have hk := le_max_left k (L + 2)
  have hL := le_max_right k (L + 2)
  omega

/-! The slow Leibniz rule retains a common damping factor in the scalar propagator. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_iteratedFDeriv_smul_damped_le (n : ℕ) (f : E → ℝ) (g : E → F)
    (hf : ContDiff ℝ (n : ℕ∞) f) (hg : ContDiff ℝ (n : ℕ∞) g)
    (x : E) (lam κ T : ℝ) (hlam : 0 ≤ lam) (hκ : 0 ≤ κ) (hT : 1 ≤ T)
    (A B : ℕ → ℝ) (hA : ∀ j ≤ n, 0 ≤ A j) (hB : ∀ j ≤ n, 0 ≤ B j)
    (hbA : ∀ j ≤ n, ‖iteratedFDeriv ℝ j f x‖ ≤ (A j * κ * T ^ j) * lam ^ j)
    (hbB : ∀ j ≤ n, ‖iteratedFDeriv ℝ j g x‖ ≤ B j * lam ^ j) :
    ‖iteratedFDeriv ℝ n (fun y => f y • g y) x‖ ≤
      (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * A j * B (n - j)) *
        κ * T ^ n * lam ^ n := by
  have hT₀ : 0 ≤ T := zero_le_one.trans hT
  have hh := norm_iteratedFDeriv_smul_scaled_le n f g hf hg x lam hlam
    (fun j => A j * κ * T ^ j) B
    (fun j hj => mul_nonneg (mul_nonneg (hA j hj) hκ) (pow_nonneg hT₀ j)) hB hbA hbB
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hlam n)
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hjn : j ≤ n := by have hh := Finset.mem_range.mp hj; omega
  have hp : T ^ j ≤ T ^ n := pow_le_pow_right₀ hT hjn
  calc
    _ = ((n.choose j : ℝ) * A j * B (n - j) * κ) * T ^ j := by ring
    _ ≤ ((n.choose j : ℝ) * A j * B (n - j) * κ) * T ^ n :=
      mul_le_mul_of_nonneg_left hp (by
        exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA j hjn))
          (hB (n - j) (Nat.sub_le n j))) hκ)
    _ = _ := by ring
end

/-! Nested slow-fast multilinear norms are recovered from real duals with constant one. -/

section
variable {ι κ : Type*} [Fintype ι] [Fintype κ] {D : ι → Type*} {F : κ → Type*}
  [∀ i, NormedAddCommGroup (D i)] [∀ i, NormedSpace ℝ (D i)]
  [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mixed_multilinear_norm_le_from_real_duals
    (f : ContinuousMultilinearMap ℝ D (ContinuousMultilinearMap ℝ F E))
    (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ l : E →L[ℝ] ℝ,
      ‖(ContinuousLinearMap.compContinuousMultilinearMapL ℝ F E ℝ l).compContinuousMultilinearMap f‖ ≤
        C * ‖l‖) : ‖f‖ ≤ C := by
  apply ContinuousMultilinearMap.opNorm_le_bound hC
  intro x
  have hprod : 0 ≤ ∏ i, ‖x i‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  apply multilinear_norm_le_from_real_duals (f x) (C * ∏ i, ‖x i‖) (mul_nonneg hC hprod)
  intro l
  let A := ContinuousLinearMap.compContinuousMultilinearMapL ℝ F E ℝ l
  have hh := (A.compContinuousMultilinearMap f).le_opNorm x
  calc
    ‖l.compContinuousMultilinearMap (f x)‖ ≤ ‖A.compContinuousMultilinearMap f‖ * ∏ i, ‖x i‖ := hh
    _ ≤ (C * ‖l‖) * ∏ i, ‖x i‖ := mul_le_mul_of_nonneg_right (hf l) hprod
    _ = (C * ∏ i, ‖x i‖) * ‖l‖ := by ring
end

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! A field independent of the slow variable has any slow reserve under its original fast regularity. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isBoxSmooth_fast_field (p q : ℕ) (f : Vec 2 → E)
    (hf : ContDiff ℝ (q : ℕ∞) f) : IsBoxSmooth p q (fun _ z => f z) := by
  refine ⟨fun _ => hf, fun _ _ _ => contDiff_const, ?_⟩
  intro r b _ hb
  cases r with
  | zero =>
    have hc := (hf.continuous_iteratedFDeriv (by exact_mod_cast hb)).comp
      (continuous_snd : Continuous (fun x : Vec 2 × Vec 2 => x.2))
    exact (continuousMultilinearCurryFin0 ℝ (Vec 2)
      (ContinuousMultilinearMap ℝ (fun _ : Fin b => Vec 2) E)).symm.continuous.comp hc
  | succ r =>
    simp only [iteratedFDeriv_succ_const, Pi.zero_apply]
    exact continuous_const

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! Continuous cell slices and measurable time slices give measurable genuine cell means. -/

variable {T E : Type*} [MeasurableSpace T]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem fieldCellMean_parameter_measurable (f : T → Vec 2 → E)
    (hm : ∀ z, Measurable (fun t => f t z)) (hf : ∀ t, Continuous (f t)) :
    Measurable (fun t => fieldCellMean (f t)) := by
  have hs : Measurable (fun p : Vec 2 × T => f p.2 p.1) :=
    measurable_uncurry_of_continuous_of_measurable hf hm
  have hj : Measurable (Function.uncurry f) := hs.comp measurable_swap
  exact (hj.stronglyMeasurable.integral_prod_right
    (ν := volume.restrict AVenhance.unitCube)).measurable

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! Recovery of a vector time primitive from its complexified real dual coordinates. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem timeIntegral_of_all_complexified_real_duals (f : ℝ → E) (u : E) (a b : ℝ)
    (h : ∀ l : E →L[ℝ] ℝ,
      IntervalIntegrable (fun s => ((l (f s) : ℝ) : ℂ)) volume a b ∧
        ((l u : ℝ) : ℂ) = ∫ s in a..b, ((l (f s) : ℝ) : ℂ)) :
    IntervalIntegrable f volume a b ∧ u = ∫ s in a..b, f s := by
  have hreal (l : E →L[ℝ] ℝ) : IntervalIntegrable (fun s => l (f s)) volume a b := by
    obtain ⟨hi, _⟩ := h l
    apply intervalIntegrable_iff.mpr
    change Integrable (fun s => l (f s)) (volume.restrict (Set.uIoc a b))
    simpa only [Complex.ofRealCLM_apply, Complex.reCLM_apply, Complex.ofReal_re] using
      Complex.reCLM.integrable_comp (intervalIntegrable_iff.mp hi)
  have hi := intervalIntegrable_of_all_real_duals f volume a b hreal
  refine ⟨hi, ?_⟩
  let e := (Module.finBasis ℝ E).equivFunL
  apply e.injective
  funext i
  let l : E →L[ℝ] ℝ := (ContinuousLinearMap.proj i).comp e.toContinuousLinearMap
  have he := congrArg Complex.re (h l).2
  change l u = Complex.reCLM (∫ s in a..b, ((l (f s) : ℝ) : ℂ)) at he
  rw [← Complex.reCLM.intervalIntegral_comp_comm (h l).1] at he
  change l u = l (∫ s in a..b, f s)
  rw [← l.intervalIntegral_comp_comm hi]
  simpa only [Complex.reCLM_apply, Complex.ofReal_re] using he

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Finite tested-word sums have constants fixed before the component family is chosen. -/

def finiteLiftWordCount (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (n + 1), (Fintype.card (DerivativeWord2 m) : ℝ)

theorem finiteLiftWordCount_nonneg (n : ℕ) : 0 ≤ finiteLiftWordCount n :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

theorem finite_lift_word_sum (n : ℕ) (x : ℝ) :
    (∑ m ∈ Finset.range (n + 1), ∑ _α : DerivativeWord2 m, x) = finiteLiftWordCount n * x := by
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, finiteLiftWordCount, Finset.sum_mul]

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleComparison.Lift

/-! One nonnegative matrix power records source height and composes exactly across ordered grades. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def finiteMatrixPower (A : ι → ι → ℝ) (hh : ℕ) : ι → ι → ℝ := (Matrix.of A) ^ hh

theorem finiteMatrixPower_zero (A : ι → ι → ℝ) :
    finiteMatrixPower A 0 = fun v u => if v = u then 1 else 0 := by
  funext v u
  simp [finiteMatrixPower, Matrix.one_apply]

theorem finiteMatrixPower_add (A : ι → ι → ℝ) (h₁ h₂ : ℕ) :
    finiteMatrixProduct (finiteMatrixPower A h₁) (finiteMatrixPower A h₂) =
      finiteMatrixPower A (h₁ + h₂) := by
  change (Matrix.of A) ^ h₁ * (Matrix.of A) ^ h₂ = (Matrix.of A) ^ (h₁ + h₂)
  exact (pow_add _ _ _).symm

theorem finiteMatrixPower_succ (A : ι → ι → ℝ) (hh : ℕ) :
    finiteMatrixPower A (hh + 1) = finiteMatrixProduct A (finiteMatrixPower A hh) := by
  change (Matrix.of A) ^ (hh + 1) = Matrix.of A * (Matrix.of A) ^ hh
  exact pow_succ' _ _

theorem finiteMatrixPower_nonneg (A : ι → ι → ℝ) (hA : ∀ v u, 0 ≤ A v u) (hh : ℕ) :
    ∀ v u, 0 ≤ finiteMatrixPower A hh v u := by
  induction hh with
  | zero =>
    rw [finiteMatrixPower_zero]
    intro v u
    change 0 ≤ if v = u then (1 : ℝ) else 0
    split_ifs <;> norm_num
  | succ hh ih =>
    rw [finiteMatrixPower_succ]
    intro v u
    exact Finset.sum_nonneg fun r _ => mul_nonneg (hA v r) (ih r u)

theorem HasRealSchurBudget.power {A : ι → ι → ℝ} {C : ℝ}
    (hA : HasRealSchurBudget A C) (hC : 0 ≤ C) (hh : ℕ) :
    HasRealSchurBudget (finiteMatrixPower A hh) (C ^ hh) := by
  induction hh with
  | zero => rw [finiteMatrixPower_zero, pow_zero]; exact hasRealSchurBudget_diagonal
  | succ hh ih =>
    rw [finiteMatrixPower_succ, pow_succ']
    exact hA.product ih hC (pow_nonneg hC hh)
end

/-! Nonnegative matrix budgets sum over finite order tables with their scalar budgets. -/

section
variable {ι α : Type*} [Fintype ι]

theorem HasRealSchurBudget.finset_sum (s : Finset α) (A : α → ι → ι → ℝ) (C : α → ℝ)
    (hA : ∀ a ∈ s, HasRealSchurBudget (A a) (C a)) :
    HasRealSchurBudget (fun i j => ∑ a ∈ s, A a i j) (∑ a ∈ s, C a) := by
  constructor
  · intro i j
    exact Finset.sum_nonneg fun a ha => (hA a ha).nonneg i j
  · intro i
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun a ha => (hA a ha).row_sum i
  · intro j
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun a ha => (hA a ha).col_sum j
end

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! The clamped first Fourier forcing is centered at every time, including outside the window. -/

theorem unitProfileFourierCoeff_zero_eq_integral (f : ℝ → ℂ) :
    unitProfileFourierCoeff f 0 = ∫ x in (0 : ℝ)..1, f x := by
  simp [unitProfileFourierCoeff, fourierCoeffOn_eq_integral]

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Uniform Fourier majorants give joint continuity of slow parameter jets. -/

theorem fourier_parameter_jet_continuous (p q : ℕ) (hq : q ≤ p)
    (F : ℤ → Vec 2 → ℂ) (hF : ∀ m, ContDiff ℝ (p : ℕ∞) (F m))
    (V : ℕ → ℤ → ℝ) (hV : ∀ r ≤ p, Summable (V r))
    (hb : ∀ r ≤ p, ∀ m X, ‖iteratedFDeriv ℝ r (F m) X‖ ≤ V r m) :
    Continuous (fun x : Vec 2 × ℝ => iteratedFDeriv ℝ q
      (fun X => ∑' m : ℤ, fourier m (x.2 : AddCircle (1 : ℝ)) * F m X) x.1) := by
  have he : (fun x : Vec 2 × ℝ => iteratedFDeriv ℝ q
      (fun X => ∑' m : ℤ, fourier m (x.2 : AddCircle (1 : ℝ)) * F m X) x.1) =
      fun x => ∑' m : ℤ, fourier m (x.2 : AddCircle (1 : ℝ)) •
        iteratedFDeriv ℝ q (F m) x.1 := by
    funext x
    rw [iteratedFDeriv_tsum_apply
      (fun m => unit_complex_mul_contDiff p _ (hF m) _)
      (fun r hr => hV r (by exact_mod_cast hr))
      (fun r m X hr => (norm_iteratedFDeriv_unit_complex_mul_le p r
        (by exact_mod_cast hr) _ (hF m) _
        (by simp only [fourier_apply, Circle.norm_coe]) X).trans
        (hb r (by exact_mod_cast hr) m X)) (by exact_mod_cast hq)]
    apply tsum_congr
    intro m
    simpa only [smul_eq_mul] using
      iteratedFDeriv_const_smul_apply' (a := (fourier m (x.2 : AddCircle (1 : ℝ)) : ℂ))
        ((hF m).of_le (by exact_mod_cast hq)).contDiffAt
  rw [he]
  refine continuous_tsum ?_ (hV q hq) ?_
  · intro m
    exact (((fourier m).continuous.comp (AddCircle.continuous_mk' (1 : ℝ))).comp
      continuous_snd).smul ((hF m).continuous_iteratedFDeriv
        (by exact_mod_cast hq) |>.comp continuous_fst)
  · intro m x
    simpa only [norm_smul, fourier_apply, Circle.norm_coe, one_mul] using hb q hq m x.1

end AVRegularity.CycleComparison.Lift
end
end
