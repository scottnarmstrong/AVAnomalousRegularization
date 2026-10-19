-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction
public import AVRegularity.CycleComparison.Lift.ProfileCellInitial
import AVRegularity.CycleComparison.Lift.FirstDiagonalSource
public import AVRegularity.Definitions.CycleComparison.IsLiftSequenceFrom

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The recursion source vanishes once its lower constant-input fields are constant. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ}

theorem liftApply_congr_time (n : ℕ) (c : LiftCoeff ι h)
    (a a' : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (he : a t = a' t) :
    liftApply n c a t = liftApply n c a' t := by
  funext X z v
  simp only [liftApply, he]

theorem liftA_const_zero_of_lower (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (c0 : ∀ i, h i) (hh n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (hcurrent : ∀ m, m < n → ∃ c : ∀ i, h i,
      liftApply m (Cc hh m) (fun _ _ => c0) t = fun _ _ => c)
    (hprevious : hh ≠ 0 → ∀ m, m ≤ n → ∃ c : ∀ i, h i,
      liftApply m (Cc (hh - 1) m) (fun _ _ => c0) t = fun _ _ => c) :
    liftA Q Cc (fun _ _ => c0) hh n t = 0 := by
  obtain ⟨c1, h1⟩ := hcurrent (n - 1) (by omega)
  have hb1 : cellB1 Q.η Q.G Q.v t
      (liftApply (n - 1) (Cc hh (n - 1)) (fun _ _ => c0) t) = 0 := by
    rw [h1]
    exact cellB1_const _ _ _ _ _
  have hb2 : (if 2 ≤ n then cellB2 Q.η Q.G t
      (liftApply (n - 2) (Cc hh (n - 2)) (fun _ _ => c0) t) else 0) = 0 := by
    split_ifs with h2
    · obtain ⟨c2, he2⟩ := hcurrent (n - 2) (by omega)
      rw [he2]
      exact cellB2_const _ _ _ _
    · rfl
  have hs : (if hh = 0 then 0 else ∑ j ∈ Finset.range (min D n + 1),
      sourceCoeff Q.edge Q.η j t
        (liftApply (n - j) (Cc (hh - 1) (n - j)) (fun _ _ => c0) t)) = 0 := by
    split_ifs with hhh
    · rfl
    · apply Finset.sum_eq_zero
      intro j hj
      obtain ⟨c, he⟩ := hprevious hhh (n - j) (by omega)
      rw [he]
      exact sourceCoeff_const _ _ _ _ _
  funext X z
  change _ + _ - _ = 0
  have hb1p := congrFun (congrFun hb1 X) z
  have hb2p := congrFun (congrFun hb2 X) z
  have hsp := congrFun (congrFun hs X) z
  simp only [ite_apply, Finset.sum_apply, Pi.zero_apply] at hb1p hb2p hsp
  rw [hb1p, hb2p, hsp]
  simp

 theorem liftMean_zero_of_A_zero (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i) (hh n : ℕ) (t : ℝ)
    (hA : liftA Q Cc a hh n t = 0) : liftMean Q Cc a hh n t = 0 := by
  funext X
  simp [liftMean, hA, fieldCellMean]

 theorem liftCellSource_zero_of_A_and_lower_means (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i) (hh n : ℕ) (t : ℝ)
    (hA : liftA Q Cc a hh n t = 0)
    (hL : ∀ (p : ℕ × ℕ), p ∈ Finset.HasAntidiagonal.antidiagonal hh → ∀ m, 2 ≤ m → m < n →
      liftMean Q Cc a p.2 m t = 0) : liftCellSource Q Cc a hh n t = 0 := by
  have hmean := liftMean_zero_of_A_zero Q Cc a hh n t hA
  funext X z
  simp only [liftCellSource, hA, hmean, Pi.zero_apply, sub_self, neg_zero, zero_add]
  apply Finset.sum_eq_zero
  intro j hj
  apply Finset.sum_eq_zero
  intro p hp
  have hjb := Finset.mem_Icc.mp hj
  have hl := hL p hp (n - j) (by omega) (by omega)
  have he := liftApply_congr_time j (Cc p.1 j) (liftMean Q Cc a p.2 (n - j)) 0 t hl
  rw [he, liftApply_zero]
  rfl
end

/-! The recursion source vanishes past the lift cutoff plus the maximum source degree. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem liftA_above_full_cutoff (Q : LiftOperatorData ι h D)
    (sX sZ : ℕ) (a b : ℝ) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (hD : 2 ≤ D)
    (f : ℝ → Vec 2 → ∀ i, h i) (hh n : ℕ) (hhh : hh ≤ H) (hn : N + D < n) (t : ℝ) :
    liftA Q Cc f hh n t = 0 := by
  have hz (q : ℕ) (hq : q ≤ H) (m : ℕ) (hm : N < m) :
      liftApply m (Cc q m) f t = 0 :=
    congrFun (liftApply_above_cutoff Q sX sZ a b N H Cc hseq q hq m hm f) t
  have hb1 : cellB1 Q.η Q.G Q.v t (liftApply (n - 1) (Cc hh (n - 1)) f t) = 0 := by
    rw [hz hh hhh (n - 1) (by omega)]
    exact cellB1_const _ _ _ _ _
  have hb2 : cellB2 Q.η Q.G t (liftApply (n - 2) (Cc hh (n - 2)) f t) = 0 := by
    rw [hz hh hhh (n - 2) (by omega)]
    exact cellB2_const _ _ _ _
  have hs : (if hh = 0 then 0 else ∑ j ∈ Finset.range (min D n + 1),
      sourceCoeff Q.edge Q.η j t (liftApply (n - j) (Cc (hh - 1) (n - j)) f t)) = 0 := by
    split_ifs
    · rfl
    · apply Finset.sum_eq_zero
      intro j hj
      have hjD : j ≤ D := by have := Finset.mem_range.mp hj; omega
      rw [hz (hh - 1) (by omega) (n - j) (by omega)]
      exact sourceCoeff_const _ _ _ _ _
  funext X z
  have h1 := congrFun (congrFun hb1 X) z
  have h2 := congrFun (congrFun hb2 X) z
  have h3 := congrFun (congrFun hs X) z
  simp only [ite_apply, Finset.sum_apply, Pi.zero_apply] at h1 h2 h3
  change _ + (if 2 ≤ n then _ else 0) - _ = 0
  rw [h1, ite_eq_left (show 2 ≤ n by omega), h2, h3]
  simp
end

/-! The literal full source convolution has finite degree inherited from the lift cutoff. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

def liftSourceConvolution (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (f : ℝ → Vec 2 → ∀ i, h i) (hh n : ℕ) (t : ℝ) (X z : Vec 2) : ∀ i, h i :=
  ∑ j ∈ Finset.range (min D n + 1), sourceCoeff Q.edge Q.η j t
    (liftApply (n - j) (Cc hh (n - j)) f t) X z

theorem liftSourceConvolution_above_cutoff (Q : LiftOperatorData ι h D)
    (sX sZ : ℕ) (a b : ℝ) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (f : ℝ → Vec 2 → ∀ i, h i)
    (hh n : ℕ) (hhh : hh ≤ H) (hn : N + D < n) (t : ℝ) (X z : Vec 2) :
    liftSourceConvolution Q Cc f hh n t X z = 0 := by
  unfold liftSourceConvolution
  apply Finset.sum_eq_zero
  intro j hj
  have hjD : j ≤ D := by
    have hj' := Finset.mem_range.mp hj
    have hmin := Nat.min_le_left D n
    omega
  have he := congrFun (liftApply_above_cutoff Q sX sZ a b N H Cc hseq
    hh hhh (n - j) (by omega) f) t
  rw [he]
  change sourceCoeff Q.edge Q.η j t 0 X z = 0
  rw [sourceCoeff_zero_input]
  rfl
end

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! A centered transverse source has a literally mean-zero Fourier response on its finite past. -/

theorem profileCellResponse_cellMean_zero (g : ℝ → ℝ) (f : ℝ → ℝ → ℂ)
    (a t κ C : ℝ) (hat : a ≤ t) (hκ : 0 < κ)
    (hi : IntegrableOn g (Icc a t)) (hg : ∀ s ∈ Icc a t, κ ≤ g s)
    (hC : 0 ≤ C) (hf : ∀ s ∈ Icc a t, Continuous (f s))
    (hp : ∀ s ∈ Icc a t, Function.Periodic (f s) 1)
    (hb : ∀ s ∈ Icc a t, ∀ x ∈ Icc (0 : ℝ) 1, ‖f s x‖ ≤ C)
    (hcenter : ∀ s ∈ Icc a t, unitProfileFourierCoeff (f s) 0 = 0)
    (p : Fin 2) : cellMean (fun z => profileCellResponse g f a t (z p)) = 0 := by
  have hc : Continuous (profileCellResponse g f a t) :=
    (profileCellResponse_contDiff g f a t κ hat hκ hi hg 0 (fun _ => C)
      (fun _ _ => hC) (fun s hs => contDiff_zero.mpr (hf s hs)) hp
      (fun j hj s hs x hx => by
        have hj0 : j = 0 := by omega
        subst j
        simpa only [iteratedDeriv_zero] using hb s hs x hx)).continuous
  unfold cellMean
  rw [integral_coordinate_eq_intervalIntegral p _ hc,
    ← unitProfileFourierCoeff_zero_eq_integral,
    unitProfileFourierCoeff_profileCellResponse g f a t κ C hat hκ hi hg hC hf hp hb 0]
  unfold profileModeResponse transverseModeResponse
  calc
    _ = ∫ s in a..t, (0 : ℂ) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le hat] at hs
      change transverseModeKernel (‖profileFourierFrequency 0‖ ^ 2) g s t •
        unitProfileFourierCoeff (f s) 0 = 0
      rw [hcenter s hs, smul_zero]
    _ = 0 := by simp

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! Bounded continuous Fourier weights preserve the available slow regularity. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

local instance weightedCellCoefficientRegularityProbCube : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using AVRegularity.CycleEvolution.cellCube_volume_one⟩

theorem weighted_cell_coefficient_contDiff (p : ℕ) (f : Vec 2 → Vec 2 → E)
    (hf : ∀ X, Continuous (f X))
    (hs : ∀ z, ContDiff ℝ (p : ℕ∞) (fun X => f X z))
    (C : ℕ → ℝ) (hb : ∀ r ≤ p, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => f Y z) X‖ ≤ C r)
    (w : Vec 2 → ℝ) (hw : Continuous w) (hwn : ∀ z, ‖w z‖ ≤ 1) :
    ContDiff ℝ (p : ℕ∞) (fun Y => ∫ z in AVenhance.unitCube, w z • f Y z) := by
  apply parameter_integral_contDiff (volume.restrict AVenhance.unitCube) p
    (fun z Y => w z • f Y z)
    (fun X => (hw.smul (hf X)).measurable)
    (fun z => (hs z).const_smul (w z)) C
  intro r hr z X
  rw [iteratedFDeriv_const_smul_apply' ((hs z).contDiffAt.of_le (by exact_mod_cast hr)), norm_smul]
  exact (mul_le_mul_of_nonneg_right (hwn z) (norm_nonneg _)).trans
    (by simpa only [one_mul] using hb r hr X z)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Lexicographically lower constant-input coefficients give a zero recursion source. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}
  (Q : LiftOperatorData ι h D) (sX sZ : ℕ) (a b : ℝ) (N H : ℕ)
  (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
  (c0 : ∀ i, h i) (hh n : ℕ) (hhh : hh ≤ H)
  (hknown : ∀ q, q ≤ hh → ∀ d, 1 ≤ d → (q < hh ∨ d < n) →
    ∀ t ∈ Set.Icc a b, liftApply d (Cc q d) (fun _ _ => c0) t = 0)

include hseq hhh hknown in
theorem liftA_const_zero_lex (q m : ℕ) (hq : q ≤ hh) (hm : 1 ≤ m)
    (hqm : q < hh ∨ m ≤ n) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    liftA Q Cc (fun _ _ => c0) q m t = 0 := by
  apply liftA_const_zero_of_lower Q Cc c0 q m hm t
  · intro d hd
    by_cases hd0 : d = 0
    · subst d
      exact ⟨if q = 0 then c0 else 0,
        liftApply_const_degree_zero Q sX sZ a b N H Cc hseq c0 q (hq.trans hhh) t ht⟩
    · refine ⟨0, ?_⟩
      exact hknown q hq d (by omega) (by omega) t ht
  · intro hq0 d hd
    by_cases hd0 : d = 0
    · subst d
      exact ⟨if q - 1 = 0 then c0 else 0,
        liftApply_const_degree_zero Q sX sZ a b N H Cc hseq c0 (q - 1) (by omega) t ht⟩
    · refine ⟨0, ?_⟩
      exact hknown (q - 1) (by omega) d (by omega) (Or.inl (by omega)) t ht

include hseq hhh hknown in
theorem liftCellSource_const_zero_lex (hn : 1 ≤ n) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    liftCellSource Q Cc (fun _ _ => c0) hh n t = 0 := by
  apply liftCellSource_zero_of_A_and_lower_means
  · exact liftA_const_zero_lex Q sX sZ a b N H Cc hseq c0 hh n hhh hknown hh n le_rfl hn
      (Or.inr le_rfl) t ht
  · intro p hp m hm hmn
    apply liftMean_zero_of_A_zero
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    exact liftA_const_zero_lex Q sX sZ a b N H Cc hseq c0 hh n hhh hknown p.2 m (by omega) (by omega)
      (Or.inr hmn.le) t ht
end

/-! The mean operator on a coarse input depends only on that input's current spatial field. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem liftA_congr_time_input (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (a a' : ℝ → Vec 2 → ∀ i, h i) (hh n : ℕ) (t : ℝ) (he : a t = a' t) :
    liftA Q Cc a hh n t = liftA Q Cc a' hh n t := by
  have hall (m : ℕ) (c : LiftCoeff ι h) : liftApply m c a t = liftApply m c a' t :=
    liftApply_congr_time m c a a' t he
  unfold liftA
  simp_rw [hall]

theorem liftMean_congr_time_input (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (a a' : ℝ → Vec 2 → ∀ i, h i) (hh n : ℕ) (t : ℝ) (he : a t = a' t) :
    liftMean Q Cc a hh n t = liftMean Q Cc a' hh n t := by
  unfold liftMean
  rw [liftA_congr_time_input Q Cc a a' hh n t he]
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! Rectangular regularity and pointwise mixed jets control the cell energy norm. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mixed_jet_fieldEnergyNorm_le (I : Set ℝ) (hI : MeasurableSet I)
    (f : ℝ → Vec 2 → Vec 2 → E) (r j : ℕ) (X : Vec 2)
    (hf : ∀ t ∈ I, IsBoxSmooth r (j + 1) (f t))
    (B₀ B₁ : ℝ) (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁)
    (hb₀ : ∀ t ∈ I, ∀ z,
      ‖iteratedFDeriv ℝ j (fun y => iteratedFDeriv ℝ r (fun Y => f t Y y) X) z‖ ≤ B₀)
    (hb₁ : ∀ t ∈ I, ∀ z,
      ‖iteratedFDeriv ℝ (j + 1) (fun y => iteratedFDeriv ℝ r (fun Y => f t Y y) X) z‖ ≤ B₁) :
    fieldEnergyNorm I (fun t z =>
      iteratedFDeriv ℝ j (fun y => iteratedFDeriv ℝ r (fun Y => f t Y y) X) z) ≤
      ENNReal.ofReal (B₀ + B₁) := by
  have hc t (ht : t ∈ I) : ContDiff ℝ ((j + 1 : ℕ) : ℕ∞)
      (fun y => iteratedFDeriv ℝ r (fun Y => f t Y y) X) :=
    (isBoxSmooth_iteratedFDeriv_slow r 0 (j + 1) (f t)
      (by simpa only [Nat.zero_add] using hf t ht)).1 X
  apply fieldEnergyNorm_le_pointwise_bounds I hI _ B₀ B₁ hB₀ hB₁
  · intro t ht
    exact (hc t ht).continuous_iteratedFDeriv (by exact_mod_cast Nat.le_succ j)
  · intro t ht
    have he : (fun z => fderiv ℝ
        (fun y => iteratedFDeriv ℝ j (fun z' => iteratedFDeriv ℝ r
          (fun Y => f t Y z') X) y) z) =
        fun z => (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => Vec 2)
          (Vec 2 [×r]→L[ℝ] E))
          (iteratedFDeriv ℝ (j + 1)
            (fun y => iteratedFDeriv ℝ r (fun Y => f t Y y) X) z) := by
      funext z
      rw [iteratedFDeriv_succ_eq_comp_left]
      simp
    change Continuous (fun z => fderiv ℝ
      (fun y => iteratedFDeriv ℝ j (fun z' => iteratedFDeriv ℝ r
        (fun Y => f t Y z') X) y) z)
    rw [he]
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => Vec 2)
      (Vec 2 [×r]→L[ℝ] E)).continuous.comp
      ((hc t ht).continuous_iteratedFDeriv le_rfl)
  · exact hb₀
  · intro t ht z
    simpa only [norm_fderiv_iteratedFDeriv] using hb₁ t ht z

end AVRegularity.CycleComparison.Lift
end
