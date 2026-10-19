-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction
public import AVRegularity.CycleComparison.Lift.ProfileCellInitial
public import AVRegularity.CycleComparison.Residual.Jets.Lift
import AVRegularity.CycleComparison.Lift.LiftApplyFiniteVectorSynthesis
public import AVRegularity.Statements.Intermediate.CycleComparison.LiftCellSource
import AVRegularity.CycleComparison.Residual.TailJets
import AVRegularity.CycleComparison.Lift.LiftMeanRecursionCongruence
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleComparison.TrimmedQuietMargin
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

section
@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The literal uncentered recurrence preserves periodicity of each actual source term. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem liftA_normalized_periodic_of_terms (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (f : ℝ → Vec 2 → ∀ i, h i)
    (hh n : ℕ) (t : ℝ) (v : ι) (A : Vec 2 →L[ℝ] ℝ) (lam : ℝ)
    (h₁ : ∀ X, AVenhance.IsZ2Periodic (fun z => (Real.exp ((lam • A) X))⁻¹ •
      cellB1 Q.η Q.G Q.v t (liftApply (n - 1) (Cc hh (n - 1)) f t) X z v))
    (h₂ : 2 ≤ n → ∀ X, AVenhance.IsZ2Periodic (fun z => (Real.exp ((lam • A) X))⁻¹ •
      cellB2 Q.η Q.G t (liftApply (n - 2) (Cc hh (n - 2)) f t) X z v))
    (hS : hh ≠ 0 → ∀ j ≤ min D n, ∀ X, AVenhance.IsZ2Periodic (fun z =>
      (Real.exp ((lam • A) X))⁻¹ • sourceCoeff Q.edge Q.η j t
        (liftApply (n - j) (Cc (hh - 1) (n - j)) f t) X z v)) :
    ∀ X, AVenhance.IsZ2Periodic (fun z => (Real.exp ((lam • A) X))⁻¹ •
      liftA Q Cc f hh n t X z v) := by
  intro X k z
  simp_rw [liftA_normalized_component_expansion]
  have he₁ := h₁ X k z
  dsimp only at he₁
  rw [he₁]
  have he₂ : (if 2 ≤ n then (Real.exp ((lam • A) X))⁻¹ • cellB2 Q.η Q.G t
      (liftApply (n - 2) (Cc hh (n - 2)) f t) X (z + AVenhance.latticeShift k) v else 0) =
      if 2 ≤ n then (Real.exp ((lam • A) X))⁻¹ • cellB2 Q.η Q.G t
        (liftApply (n - 2) (Cc hh (n - 2)) f t) X z v else 0 := by
    split_ifs with hn
    · exact h₂ hn X k z
    · rfl
  rw [he₂]
  by_cases hh0 : hh = 0
  · simp only [ite_eq_left hh0]
  · simp only [ite_eq_right hh0]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    exact hS hh0 j (by have he := Finset.mem_range.mp hj; omega) X k z
end

/-! At height zero, paired uncentered sources contain exactly the two cross differences. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem liftA_zero_height_normalized_paired_expansion
    (Q : LiftOperatorData ι h D) (J : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (Cc Ci : ℕ → ℕ → LiftCoeff ι h) (f : ℝ → Vec 2 → ∀ i, h i)
    (n : ℕ) (t : ℝ) (X z : Vec 2) (v : ι) (A : Vec 2 →L[ℝ] ℝ) (lam : ℝ) :
    (Real.exp ((lam • A) X))⁻¹ • liftA Q Cc f 0 n t X z v -
      (Real.exp ((lam • A) X))⁻¹ •
        liftA (⟨Q.η, J, Q.v, Q.edge⟩ : LiftOperatorData ι h D) Ci f 0 n t X z v =
    ((Real.exp ((lam • A) X))⁻¹ • cellB1 Q.η Q.G Q.v t
        (liftApply (n - 1) (Cc 0 (n - 1)) f t) X z v -
      (Real.exp ((lam • A) X))⁻¹ • cellB1 Q.η J Q.v t
        (liftApply (n - 1) (Ci 0 (n - 1)) f t) X z v) +
    if 2 ≤ n then
      (Real.exp ((lam • A) X))⁻¹ • cellB2 Q.η Q.G t
        (liftApply (n - 2) (Cc 0 (n - 2)) f t) X z v -
      (Real.exp ((lam • A) X))⁻¹ • cellB2 Q.η J t
        (liftApply (n - 2) (Ci 0 (n - 2)) f t) X z v else 0 := by
  rw [liftA_normalized_component_expansion, liftA_normalized_component_expansion]
  simp only [ite_true, sub_zero]
  split_ifs <;> abel
end

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! The mode right-hand-side series is the classical scalar diffusion operator plus the actual source. -/

theorem profileCellResponse_rhs_series_spatial_identity (g : ℝ → ℝ) (f : ℝ → ℝ → ℂ)
    (a t κ : ℝ) (hat : a ≤ t) (hκ : 0 < κ) (hi : IntegrableOn g (Icc a t))
    (hg : ∀ s ∈ Icc a t, κ ≤ g s) (C : ℕ → ℝ) (hC : ∀ j ≤ 2, 0 ≤ C j)
    (hf : ∀ s ∈ Icc a t, ContDiff ℝ 2 (f s))
    (hp : ∀ s ∈ Icc a t, Function.Periodic (f s) 1)
    (hj : ∀ j ≤ 2, ∀ s ∈ Icc a t, ∀ y ∈ Icc (0 : ℝ) 1,
      ‖iteratedDeriv j (f s) y‖ ≤ C j) (x : ℝ) :
    profileFourierSeries (fun n =>
      (-(‖profileFourierFrequency n‖ ^ 2) * g t) • profileModeResponse g f a t n +
        unitProfileFourierCoeff (f t) n) x =
      g t • iteratedDeriv 2 (profileCellResponse g f a t) x + f t x := by
  let c := profileModeResponse g f a t
  have hs (j : ℕ) (hj2 : j ≤ 2) : Summable (fun n => profileFourierFrequency n ^ j * c n) := by
    apply profileFourier_jet_summable c j (C j / κ)
    intro n hn
    exact profileModeResponse_frequency_weight_bound g f a t κ hat hκ hi hg j (C j) (hC j hj2)
      (fun s hs => (hf s hs).of_le (by exact_mod_cast hj2)) hp (hj j hj2) n hn
  have hsrc : Summable (unitProfileFourierCoeff (f t)) := by
    have hh := profileFourier_jet_summable (unitProfileFourierCoeff (f t)) 0 (C 2)
      (fun n hn => unitProfileFourierCoeff_frequency_weight_bound 2 (f t)
        (hf t ⟨hat, le_rfl⟩) (hp t ⟨hat, le_rfl⟩) n hn (C 2) (hj 2 le_rfl t ⟨hat, le_rfl⟩))
    simpa only [pow_zero, one_mul] using hh
  have ht2 := profileFourierSeries_term_summable _ (hs 2 le_rfl) x
  have ht0 := profileFourierSeries_term_summable _ hsrc x
  have he (n : ℤ) : fourier n (x : AddCircle (1 : ℝ)) *
      ((-(‖profileFourierFrequency n‖ ^ 2) * g t) • c n + unitProfileFourierCoeff (f t) n) =
      g t • (fourier n (x : AddCircle (1 : ℝ)) * (profileFourierFrequency n ^ 2 * c n)) +
        fourier n (x : AddCircle (1 : ℝ)) * unitProfileFourierCoeff (f t) n := by
    rw [profileFourierFrequency_sq]
    simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_neg]
    ring
  change (∑' n, fourier n (x : AddCircle (1 : ℝ)) *
    ((-(‖profileFourierFrequency n‖ ^ 2) * g t) • c n + unitProfileFourierCoeff (f t) n)) = _
  simp_rw [he]
  rw [(ht2.const_smul (g t)).tsum_add ht0, Summable.tsum_const_smul (g t) ht2]
  change g t • profileFourierSeries (fun n => profileFourierFrequency n ^ 2 * c n) x +
    profileFourierSeries (unitProfileFourierCoeff (f t)) x = _
  rw [profileFourierSeries_reconstruct (f t) (hf t ⟨hat, le_rfl⟩).continuous (hp t ⟨hat, le_rfl⟩) hsrc]
  rw [← profileFourierSeries_iteratedDeriv 2 c hs]
  rfl

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Group the source flux on a coarse input by its covariant monomial degree. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

def slowSourceFluxOrder (edge : ConstituentEdges D h) (η t : ℝ)
    (f : Vec 2 → ∀ i, h i) (d : Finset.Icc 2 D) (q : Fin 2) :
    Vec 2 → Vec 2 → ∀ i, h i :=
  fun X z v => ∑ u : ι, ((edge v u d).map fun γ =>
    ∑ α : DerivativeWord2 (d.1 - 1),
      (Real.sqrt η ^ (d.1 - 1) * γ.coeff α t X z q) •
        γ.map (orderedDerivative α f X u)).sum

theorem sourceFlux_independent_expand (edge : ConstituentEdges D h) (η ε t : ℝ)
    (f : Vec 2 → ∀ i, h i) (q : Fin 2) (X z : Vec 2) :
    sourceFlux edge η ε t (fun X _ => f X) q X z =
      ∑ d : Finset.Icc 2 D, ε ^ (d.1 - 1) • slowSourceFluxOrder edge η t f d q X z := by
  funext v
  simp only [sourceFlux, dEpsWord_independent, slowSourceFluxOrder,
    Finset.sum_apply, Pi.smul_apply, Finset.smul_sum, List.smul_sum, List.map_map,
    Function.comp_def, mul_pow, map_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  apply List.map_congr_left
  intro γ _
  apply Finset.sum_congr rfl
  intro α _
  simp only [smul_smul]
  congr 1
  ring
end

/-! Slow coordinate words obey the full mixed-jet majorant without a loss. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fast_jet_slow_word_norm_le {r q : ℕ} {f : Vec 2 → Vec 2 → E}
    (hf : IsBoxSmooth r q f) (w : DerivativeWord2 r) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ q (fun y => orderedDerivative w (fun Y => f Y y) X) z‖ ≤
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q (f Y) z) X‖ := by
  rw [orderedDerivative_slow_fast_jet r q f w hf X z]
  exact norm_orderedDerivative_le (hf.2.1 q le_rfl z) w X
end

/-! The zero-parameter source flux inherits the cell periodicity of its input. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem sourceFlux_zero_periodic (edge : ConstituentEdges D h) (η t : ℝ)
    (Φ : Vec 2 → Vec 2 → ∀ i, h i) (X : Vec 2)
    (hf : ContDiff ℝ (D : ℕ∞) (Φ X)) (hp : AVenhance.IsZ2Periodic (Φ X))
    (q : Fin 2) : AVenhance.IsZ2Periodic (sourceFlux edge η 0 t Φ q X) := by
  intro n z
  funext v
  simp only [sourceFlux, dEpsWord_zero_parameter]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro d _
  congr 1
  apply List.map_congr_left
  intro γ _
  apply Finset.sum_congr rfl
  intro α _
  have hd : d.1 - 1 ≤ D := by have hh := (Finset.mem_Icc.mp d.2).2; omega
  have hword := orderedDerivative_periodic α (Φ X)
    (hf.of_le (by exact_mod_cast hd)) hp
  rw [γ.periodic α t X n z, hword n z]
end

/-! The literal uncentered source preserves transverse geometry of its actual three terms. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem liftA_normalized_transverse_of_terms (par : Fin 2) (I : Set ℝ)
    (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (f : ℝ → Vec 2 → ∀ i, h i) (hh n : ℕ) (v : ι)
    (A : Vec 2 →L[ℝ] ℝ) (lam : ℝ)
    (h₁ : IsTransverseOn par I (fun t X z => (Real.exp ((lam • A) X))⁻¹ •
      cellB1 Q.η Q.G Q.v t (liftApply (n - 1) (Cc hh (n - 1)) f t) X z v))
    (h₂ : 2 ≤ n → IsTransverseOn par I (fun t X z => (Real.exp ((lam • A) X))⁻¹ •
      cellB2 Q.η Q.G t (liftApply (n - 2) (Cc hh (n - 2)) f t) X z v))
    (hS : hh ≠ 0 → ∀ j ≤ min D n, IsTransverseOn par I (fun t X z =>
      (Real.exp ((lam • A) X))⁻¹ • sourceCoeff Q.edge Q.η j t
        (liftApply (n - j) (Cc (hh - 1) (n - j)) f t) X z v)) :
    IsTransverseOn par I (fun t X z => (Real.exp ((lam • A) X))⁻¹ •
      liftA Q Cc f hh n t X z v) := by
  intro t ht X z s
  simp_rw [liftA_normalized_component_expansion]
  have he₁ := h₁ t ht X z s
  dsimp only at he₁
  rw [he₁]
  have he₂ : (if 2 ≤ n then (Real.exp ((lam • A) X))⁻¹ • cellB2 Q.η Q.G t
      (liftApply (n - 2) (Cc hh (n - 2)) f t) X (z + s • basisVec par) v else 0) =
      if 2 ≤ n then (Real.exp ((lam • A) X))⁻¹ • cellB2 Q.η Q.G t
        (liftApply (n - 2) (Cc hh (n - 2)) f t) X z v else 0 := by
    split_ifs with hn
    · exact h₂ hn t ht X z s
    · rfl
  rw [he₂]
  by_cases hh0 : hh = 0
  · simp only [ite_eq_left hh0]
  · simp only [ite_eq_right hh0]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    exact hS hh0 j (by have he := Finset.mem_range.mp hj; omega) t ht X z s
end

/-! Slow partials raise the base grade once; fast partials preserve it. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem slowPartial_mixed_grading_at_slow_point (p q δ : ℕ) (lam C : ℝ)
    (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth (p + 1) q f) (X : Vec 2)
    (hb : ∀ a ≤ p + 1, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (f Y) z) X‖ ≤ C * lam ^ (δ + a))
    (k : Fin 2) : ∀ a ≤ p, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (slowPartial k f Y) z) X‖ ≤
        C * lam ^ ((δ + 1) + a) := by
  intro a ha b hbq z
  have hh := norm_mixed_slow_direction_le (hf.mono (show a + 1 ≤ p + 1 by omega) hbq)
    (basisVec k) X z
  have he (Y y : Vec 2) : fderiv ℝ (fun Z => f Z y) Y (basisVec k) = slowPartial k f Y y := rfl
  simp_rw [he] at hh
  rw [norm_basisVec, one_mul] at hh
  simpa only [show δ + (a + 1) = (δ + 1) + a by omega] using
    hh.trans (hb (a + 1) (by omega) b hbq z)

theorem fastPartial_mixed_grading_at_slow_point (p q δ : ℕ) (lam C : ℝ)
    (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth p (q + 1) f) (X : Vec 2)
    (hb : ∀ a ≤ p, ∀ b ≤ q + 1, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (f Y) z) X‖ ≤ C * lam ^ (δ + a))
    (k : Fin 2) : ∀ a ≤ p, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (fastPartial k f Y) z) X‖ ≤
        C * lam ^ (δ + a) := by
  intro a ha b hbq z
  have hh := norm_mixed_fast_direction_le (hf.mono ha (show b + 1 ≤ q + 1 by omega))
    (basisVec k) X z
  have he (Y y : Vec 2) : fderiv ℝ (f Y) y (basisVec k) = fastPartial k f Y y := rfl
  simp_rw [he] at hh
  rw [norm_basisVec, one_mul] at hh
  exact hh.trans (hb a ha (b + 1) (by omega) z)
end

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! The centered response uses one universal finite Fourier constant, linear in the source jet bound. -/

def centeredProfileJetConstant : ℝ :=
  (1 / (4 * Real.pi ^ 2)) * ∑' n : ℤ, (1 / (n : ℝ) ^ 2)

theorem centeredProfileJetConstant_nonneg : 0 ≤ centeredProfileJetConstant := by
  apply mul_nonneg
  · exact one_div_nonneg.mpr (mul_nonneg (by norm_num) (sq_nonneg Real.pi))
  · exact tsum_nonneg (fun n => one_div_nonneg.mpr (sq_nonneg (n : ℝ)))

theorem profileJetMajorant_tsum_centered (M : ℝ) :
    (∑' n : ℤ, profileJetMajorant M 0 n) = M * centeredProfileJetConstant := by
  have he : profileJetMajorant M 0 = fun n : ℤ =>
      M / (4 * Real.pi ^ 2) * (1 / (n : ℝ) ^ 2) := by
    funext n
    by_cases hn : n = 0
    · subst n
      simp [profileJetMajorant]
    · simp only [profileJetMajorant, ite_eq_right hn]
  rw [he, tsum_mul_left]
  unfold centeredProfileJetConstant
  ring

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set AVenhance.Infra.ODE
namespace AVRegularity.CycleComparison.Lift

/-! Each Fourier coefficient of the synthesized response is an actual compiled finite-dimensional ODE solution. -/

theorem profileModeResponse_solves (g : ℝ → ℝ) (f : ℝ → ℝ → ℂ) (a b : ℝ) (hab : a ≤ b)
    (M : ℝ) (hM : 0 ≤ M) (hgm : AEStronglyMeasurable g volume) (hgb : ∀ t, |g t| ≤ M)
    (hfm : Measurable (Function.uncurry f)) (C : ℝ)
    (hfb : ∀ t ∈ uIcc a b, ∀ x ∈ Icc (0 : ℝ) 1, ‖f t x‖ ≤ C) (n : ℤ) :
    IsLinearIntegralSolution
        (fun t => (-(‖profileFourierFrequency n‖ ^ 2) * g t) • ContinuousLinearMap.id ℝ ℂ)
        (fun t => unitProfileFourierCoeff (f t) n) 0 a b
        (fun t => profileModeResponse g f a t n) ∧
      AbsolutelyContinuousOnInterval (fun t => profileModeResponse g f a t n) a b := by
  exact transverseModeResponse_vector_solves (‖profileFourierFrequency n‖ ^ 2) g
    (fun t => unitProfileFourierCoeff (f t) n) a b hab M hM hgm hgb
    (unitProfileFourierCoeff_time_intervalIntegrable f hfm a b C hfb n)

end AVRegularity.CycleComparison.Lift
end

section
open scoped ComplexConjugate
namespace AVRegularity.CycleComparison.Lift

/-! The literal transverse inverse of real forcing is real, by mode conjugate symmetry. -/

theorem profileFourierSeries_conj_eq (c : ℤ → ℂ)
    (hc : ∀ n, c (-n) = conj (c n)) (x : ℝ) :
    conj (profileFourierSeries c x) = profileFourierSeries c x := by
  unfold profileFourierSeries
  rw [RCLike.conj_tsum]
  have he : (fun n : ℤ => conj (fourier n (x : AddCircle (1 : ℝ)) * c n)) =
      fun n => fourier (-n) (x : AddCircle (1 : ℝ)) * c (-n) := by
    funext n
    rw [map_mul, ← fourier_neg, ← hc n]
  rw [he]
  exact (Equiv.neg ℤ).tsum_eq (fun n : ℤ => fourier n (x : AddCircle (1 : ℝ)) * c n)

theorem profileCellResponse_conj_eq (g : ℝ → ℝ) (f : ℝ → ℝ → ℂ)
    (hp : ∀ t, Function.Periodic (f t) 1) (hreal : ∀ t x, conj (f t x) = f t x)
    (a b x : ℝ) : conj (profileCellResponse g f a b x) = profileCellResponse g f a b x := by
  exact profileFourierSeries_conj_eq _
    (profileModeResponse_neg_of_real g f hp hreal a b) x

theorem profileCellResponse_ofReal_re (g : ℝ → ℝ) (f : ℝ → ℝ → ℂ)
    (hp : ∀ t, Function.Periodic (f t) 1) (hreal : ∀ t x, conj (f t x) = f t x)
    (a b x : ℝ) : ((profileCellResponse g f a b x).re : ℂ) =
      profileCellResponse g f a b x := by
  have hi := congrArg Complex.im (profileCellResponse_conj_eq g f hp hreal a b x)
  simp only [Complex.conj_im] at hi
  have him : (profileCellResponse g f a b x).im = 0 := by linarith
  apply Complex.ext <;> simp [him]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVenhance.Infra.Torus
namespace AVRegularity.CycleComparison.Lift

/-! One explicit profile identity applies uniformly at every slow parameter. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem transverse_parameterized_dual_fourier_identity
    (par : Fin 2) (f : Vec 2 → Vec 2 → E)
    (ht : IsTransverseOn par Set.univ (fun _ : ℝ => f)) (l : E →L[ℝ] ℝ)
    (hs : ∀ X, ContDiff ℝ 1
      (fun z : ℝ => ((l (f X (z • basisVec par.rev)) : ℝ) : ℂ)))
    (hp : ∀ X, Function.Periodic
      (fun z : ℝ => ((l (f X (z • basisVec par.rev)) : ℝ) : ℂ)) 1)
    (k : Fin 2 → ℤ) :
    (fun X => smoothFourierCoeff (fun z => ((l (f X z) : ℝ) : ℂ)) k) =
      fun X => if k par = 0 then
        unitProfileFourierCoeff (fun z => ((l (f X (z • basisVec par.rev)) : ℝ) : ℂ)) (k par.rev)
      else 0 := by
  funext X
  have he : (fun z => ((l (f X z) : ℝ) : ℂ)) =
      fun z => ((l (f X (z par.rev • basisVec par.rev)) : ℝ) : ℂ) := by
    funext z
    rw [transverse_profile_representation par Set.univ (fun _ : ℝ => f) ht 0
      (Set.mem_univ _) X z]
  rw [he]
  exact smoothFourierCoeff_transverse_profile_all par _ (hs X) (hp X) k

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! Scalar constituent coordinates use the same uniform majorant as the vector coefficient. -/

theorem constituentScalarMixedBudget_bounds (I : Set ℝ) (p q : ℕ) (lam : ℝ)
    (hlam : 0 < lam) (f : ℝ → Vec 2 → Vec 2 → Vec 2)
    (hfin : ∀ r ≤ p, ∀ s ≤ q, jetSup I r s f < ⊤)
    (t : ℝ) (ht : t ∈ I) (hf : IsBoxSmooth p q (f t))
    (k : Fin 2) (r s : ℕ) (hr : r ≤ p) (hs : s ≤ q) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (fun y => f t Y y k) z) X‖ ≤
      constituentUniformMixedBudget I p q lam f * lam ^ r := by
  let L : Vec 2 →L[ℝ] ℝ := ContinuousLinearMap.proj k
  have hp := norm_mixed_jet_postcomposition_le p q r s hr hs (f t) hf.1
    (hf.2.1 s hs) L X z
  calc
    _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (f t Y) z) X‖ := hp
    _ ≤ 1 * ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (f t Y) z) X‖ :=
      mul_le_mul_of_nonneg_right (cell_coordinate_projection_norm_le k) (norm_nonneg _)
    _ ≤ _ := by
      rw [one_mul]
      exact constituentUniformMixedBudget_bounds I p q lam hlam f hfin r s hr hs t ht X z

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The literal centered recurrence splits into its normalized source and ordered corrections. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem liftCellSource_normalized_component_expansion (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (f : ℝ → Vec 2 → ∀ i, h i)
    (hh n : ℕ) (t : ℝ) (X z : Vec 2) (v : ι) (A : Vec 2 →L[ℝ] ℝ) (lam : ℝ) :
    (Real.exp ((lam • A) X))⁻¹ • liftCellSource Q Cc f hh n t X z v =
      -((Real.exp ((lam • A) X))⁻¹ • liftA Q Cc f hh n t X z v -
        (Real.exp ((lam • A) X))⁻¹ • liftMean Q Cc f hh n t X v) +
      ∑ j ∈ Finset.Icc 1 (n - 2), ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal hh,
        (Real.exp ((lam • A) X))⁻¹ •
          liftApply j (Cc ab.1 j) (liftMean Q Cc f ab.2 (n - j)) t X z v := by
  simp only [liftCellSource, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Finset.sum_apply,
    smul_add, smul_neg, smul_sub, Finset.smul_sum]
end

/-! Recover the energy ordering of mixed jets from the rectangular mixed-jet majorant. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fast_slow_mixed_jet_norm_le {r q : ℕ} {f : Vec 2 → Vec 2 → E}
    (hf : IsBoxSmooth r q f) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ q (fun y => iteratedFDeriv ℝ r (fun Y => f Y y) X) z‖ ≤
      2 ^ r * ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q (f Y) z) X‖ := by
  classical
  let g := fun y => iteratedFDeriv ℝ r (fun Y => f Y y) X
  have hg : ContDiff ℝ (q : ℕ∞) g :=
    (isBoxSmooth_iteratedFDeriv_slow r 0 q f
      (by simpa only [Nat.zero_add] using hf)).1 X
  apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (by positivity) (norm_nonneg _))
  intro v
  apply (norm_le_sum_basisVec (iteratedFDeriv ℝ q g z v)).trans
  have hword (w : DerivativeWord2 r) :
      (fun y => g y (fun i => basisVec (w i))) =
      fun y => orderedDerivative (wordRev r w) (fun Y => f Y y) X := by
    funext y
    rw [orderedDerivative_eq_iteratedFDeriv _ (hf.contDiff_slow y)]
    simp only [g, wordRev, Equiv.coe_fn_mk, Fin.rev_rev]
  have hb (w : DerivativeWord2 r) :
      ‖iteratedFDeriv ℝ q g z v (fun i => basisVec (w i))‖ ≤
        ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q (f Y) z) X‖ *
          ∏ i, ‖v i‖ := by
    let A := ContinuousMultilinearMap.apply ℝ (fun _ : Fin r => Vec 2) E
      (fun i => basisVec (w i))
    have he := A.iteratedFDeriv_comp_left (hg.contDiffAt (x := z)) (i := q) le_rfl
    have hv : iteratedFDeriv ℝ q g z v (fun i => basisVec (w i)) =
        iteratedFDeriv ℝ q (fun y => g y (fun i => basisVec (w i))) z v := by
      rw [show (fun y => g y (fun i => basisVec (w i))) = A ∘ g from rfl, he]
      rfl
    rw [hv, hword]
    exact ((iteratedFDeriv ℝ q
      (fun y => orderedDerivative (wordRev r w) (fun Y => f Y y) X) z).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (fast_jet_slow_word_norm_le hf (wordRev r w) X z)
        (Finset.prod_nonneg fun _ _ => norm_nonneg _))
  calc
    _ ≤ ∑ _w : DerivativeWord2 r,
        ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q (f Y) z) X‖ * ∏ i, ‖v i‖ :=
      Finset.sum_le_sum fun w _ => hb w
    _ = (2 ^ r * ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q (f Y) z) X‖) *
        ∏ i, ‖v i‖ := by
      rw [Finset.sum_const, card_derivativeWord2, nsmul_eq_mul]
      push_cast
      ring
end

/-! Explicit selected-component fields for the actual exponential lift test and its source. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

def normalizedLiftTestField (c : LiftCoeff ι h) (n : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (u v : ι) (ξ : h u) : ℝ → Vec 2 → Vec 2 → h v :=
  fun t X z => (Real.exp (A X))⁻¹ •
    liftApply n c (fun _ Y => Real.exp (A Y) • Pi.single u ξ) t X z v

def normalizedLiftSourceField {D : ℕ} (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (u v : ι) (ξ : h u) : ℝ → Vec 2 → Vec 2 → h v :=
  fun t X z => (Real.exp (A X))⁻¹ •
    liftCellSource Q Cc (fun _ Y => Real.exp (A Y) • Pi.single u ξ) hh n t X z v
end

end AVRegularity.CycleComparison.Lift
end

section
namespace AVRegularity.CycleComparison.Lift

/-! Allowing the mean mode preserves a universal finite Fourier budget. -/

theorem profileJetMajorant_nonneg (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) (m : ℤ) :
    0 ≤ profileJetMajorant C R m := by
  unfold profileJetMajorant
  split_ifs
  · exact hR
  · positivity

theorem profileJetMajorant_const_mul (C R B : ℝ) (m : ℤ) :
    profileJetMajorant (B * C) (B * R) m = B * profileJetMajorant C R m := by
  unfold profileJetMajorant
  split_ifs
  · rfl
  · ring

theorem profileJetMajorant_tsum_full (C R : ℝ) :
    (∑' m : ℤ, profileJetMajorant C R m) = C * centeredProfileJetConstant + R := by
  have he : profileJetMajorant C R =
      fun m : ℤ => profileJetMajorant C 0 m + if m = 0 then R else 0 := by
    funext m
    by_cases hm : m = 0 <;> simp [profileJetMajorant, hm]
  rw [he, Summable.tsum_add (profileJetMajorant_summable C 0)]
  · simp [profileJetMajorant_tsum_centered]
  · exact (hasSum_ite_eq 0 R).summable

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Each slow-input flux coefficient has one classical derivative in either variable. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem slowSourceFluxOrder_fast_contDiff (edge : ConstituentEdges D h) (η t : ℝ)
    (f : Vec 2 → ∀ i, h i) (d : Finset.Icc 2 D) (q : Fin 2) (X : Vec 2)
    (hc : ∀ v u, ∀ γ ∈ edge v u d, ∀ α, ContDiff ℝ 1 (γ.coeff α t X)) :
    ContDiff ℝ 1 (slowSourceFluxOrder edge η t f d q X) := by
  apply contDiff_pi.mpr
  intro v
  simp only [slowSourceFluxOrder]
  apply ContDiff.sum
  intro u _
  apply contDiff_list_sum_map
  intro γ hγ
  apply ContDiff.sum
  intro α _
  have hs : ContDiff ℝ 1 (fun z => γ.coeff α t X z q) :=
    (ContinuousLinearMap.proj q : Vec 2 →L[ℝ] ℝ).contDiff.comp (hc v u γ hγ α)
  exact (contDiff_const.mul hs).smul contDiff_const

theorem slowSourceFluxOrder_slow_contDiff (edge : ConstituentEdges D h) (η t : ℝ)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (D : ℕ∞) f)
    (d : Finset.Icc 2 D) (q : Fin 2) (z : Vec 2)
    (hc : ∀ v u, ∀ γ ∈ edge v u d, ∀ α,
      ContDiff ℝ 1 (fun X => γ.coeff α t X z)) :
    ContDiff ℝ 1 (fun X => slowSourceFluxOrder edge η t f d q X z) := by
  apply contDiff_pi.mpr
  intro v
  simp only [slowSourceFluxOrder]
  apply ContDiff.sum
  intro u _
  apply contDiff_list_sum_map
  intro γ hγ
  apply ContDiff.sum
  intro α _
  have hs : ContDiff ℝ 1 (fun X => γ.coeff α t X z q) :=
    (ContinuousLinearMap.proj q : Vec 2 →L[ℝ] ℝ).contDiff.comp (hc v u γ hγ α)
  have hd : 2 ≤ d.1 ∧ d.1 ≤ D := Finset.mem_Icc.mp d.2
  have hw := orderedDerivative_contDiff α 1 f
    (hf.of_le (by exact_mod_cast (show 1 + (d.1 - 1) ≤ D by omega)))
  have hu : ContDiff ℝ 1 (fun X => orderedDerivative α f X u) := by
    simpa only [Function.comp_def] using!
      (ContinuousLinearMap.proj u : (∀ i, h i) →L[ℝ] h u).contDiff.comp hw
  exact (contDiff_const.mul hs).smul (γ.map.contDiff.comp hu)
end

/-! Classical fast words on transverse profiles reduce exactly to scalar iterated derivatives. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem orderedDerivative_append_direction {m : ℕ} (α : DerivativeWord2 m) (i : Fin 2)
    (f : Vec 2 → E) :
    orderedDerivative (Fin.snoc α i : DerivativeWord2 (m + 1)) f =
      fun z => fderiv ℝ (orderedDerivative α f) z (basisVec i) := by
  simp only [orderedDerivative, List.ofFn_succ', List.concat_eq_append, List.foldl_append,
    List.foldl_cons, List.foldl_nil]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

theorem orderedDerivative_transverse_profile {m : ℕ} (α : DerivativeWord2 m)
    (f : ℝ → E) (hf : ContDiff ℝ (m : ℕ∞) f) (p : Fin 2) :
    orderedDerivative α (fun z : Vec 2 => f (z p)) =
      fun z => if (∀ i, α i = p) then iteratedDeriv m f (z p) else 0 := by
  induction m with
  | zero => simp [orderedDerivative]
  | succ m ih =>
    have hα : α = Fin.snoc (Fin.init α) (α (Fin.last m)) := (Fin.snoc_init_self α).symm
    have hf' : ContDiff ℝ (m : ℕ∞) f := hf.of_le (by exact_mod_cast Nat.le_succ m)
    rw [hα, orderedDerivative_append_direction, ih (Fin.init α) hf']
    have hcond : (∀ i, Fin.snoc (Fin.init α) (α (Fin.last m)) i = p) ↔
        (∀ i, Fin.init α i = p) ∧ α (Fin.last m) = p := by
      simp only [Fin.forall_fin_succ', Fin.snoc_castSucc, Fin.snoc_last]
    by_cases hinit : ∀ i, Fin.init α i = p
    · simp only [ite_eq_left hinit]
      funext z
      rw [fderiv_profile_basis _ (hf.differentiable_iteratedDeriv m
        (by exact_mod_cast Nat.lt_succ_self m))]
      have hlast : (∀ i, Fin.snoc (Fin.init α) (α (Fin.last m)) i = p) ↔
          α (Fin.last m) = p :=
        ⟨fun h => (hcond.mp h).2, fun h => hcond.mpr ⟨hinit, h⟩⟩
      simp only [hlast, iteratedDeriv_succ]
    · simp only [ite_eq_right hinit]
      funext z
      have hfull : ¬∀ i, Fin.snoc (Fin.init α) (α (Fin.last m)) i = p :=
        fun h => hinit (hcond.mp h).1
      simp only [fderiv_fun_const, Pi.zero_apply, zero_apply, ite_eq_right hfull]
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Centering and the actual finite ordered corrections preserve clamped scalar-dual measurability. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem liftCellSource_normalized_clamped_dual_measurable_of_terms
    (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (f : ℝ → Vec 2 → ∀ i, h i) (hh n : ℕ) (a b : ℝ) (hab : a ≤ b)
    (v : ι) (l : h v →L[ℝ] ℝ) (A : Vec 2 →L[ℝ] ℝ) (lam : ℝ) (X z : Vec 2)
    (hA : Measurable (fun t => l ((Real.exp ((lam • A) X))⁻¹ •
      liftA Q Cc f hh n (Set.projIcc a b hab t) X z v)))
    (hMean : Measurable (fun t => l ((Real.exp ((lam • A) X))⁻¹ •
      liftMean Q Cc f hh n (Set.projIcc a b hab t) X v)))
    (hT : ∀ j ∈ Finset.Icc 1 (n - 2), ∀ ab ∈ Finset.HasAntidiagonal.antidiagonal hh,
      Measurable (fun t => l ((Real.exp ((lam • A) X))⁻¹ •
        liftApply j (Cc ab.1 j) (liftMean Q Cc f ab.2 (n - j))
          (Set.projIcc a b hab t) X z v))) :
    Measurable (fun t => l ((Real.exp ((lam • A) X))⁻¹ •
      liftCellSource Q Cc f hh n (Set.projIcc a b hab t) X z v)) := by
  simp_rw [liftCellSource_normalized_component_expansion, map_add, map_neg, map_sub, map_sum]
  exact (hA.sub hMean).neg.add (Finset.measurable_sum _ fun j hj =>
    Finset.measurable_sum _ fun ab hab => hT j hj ab hab)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The literal height-zero source difference preserves the order of both correction operators. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem liftCellSource_zero_height_normalized_paired_expansion
    (Q Qi : LiftOperatorData ι h D) (Cc Ci : ℕ → ℕ → LiftCoeff ι h)
    (f : ℝ → Vec 2 → ∀ i, h i) (n : ℕ) (t : ℝ) (X z : Vec 2) (v : ι)
    (A : Vec 2 →L[ℝ] ℝ) (lam : ℝ) :
    (Real.exp ((lam • A) X))⁻¹ • liftCellSource Q Cc f 0 n t X z v -
      (Real.exp ((lam • A) X))⁻¹ • liftCellSource Qi Ci f 0 n t X z v =
    -(((Real.exp ((lam • A) X))⁻¹ • liftA Q Cc f 0 n t X z v -
        (Real.exp ((lam • A) X))⁻¹ • liftA Qi Ci f 0 n t X z v) -
      ((Real.exp ((lam • A) X))⁻¹ • liftMean Q Cc f 0 n t X v -
        (Real.exp ((lam • A) X))⁻¹ • liftMean Qi Ci f 0 n t X v)) +
    ∑ j ∈ Finset.Icc 1 (n - 2),
      ((Real.exp ((lam • A) X))⁻¹ •
          liftApply j (Cc 0 j) (liftMean Q Cc f 0 (n - j)) t X z v -
        (Real.exp ((lam • A) X))⁻¹ •
          liftApply j (Ci 0 j) (liftMean Qi Ci f 0 (n - j)) t X z v) := by
  rw [liftCellSource_normalized_component_expansion, liftCellSource_normalized_component_expansion]
  simp only [Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
  rw [Finset.sum_sub_distrib]
  abel
end

/-! The literal finite graded composition coefficient in the explicit tail. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

def liftMeanCompositionCoefficient (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (N : ℕ) (a : ℝ → Vec 2 → ∀ i, h i)
    (hh n : ℕ) (t : ℝ) (X z : Vec 2) : ∀ i, h i :=
  ∑ r ∈ Finset.range (N + 1),
    if r ≤ n ∧ 2 ≤ n - r ∧ n - r ≤ N + D then
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
        liftApply r (Cc p.1 r) (liftMean Q Cc a p.2 (n - r)) t X z
    else 0

theorem liftTailCoeff_eq_difference (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (N : ℕ) (a : ℝ → Vec 2 → ∀ i, h i)
    (hh n : ℕ) (t : ℝ) (X z : Vec 2) :
    liftTailCoeff Q Cc N a hh n t X z =
      liftA Q Cc a hh n t X z - liftMeanCompositionCoefficient Q Cc N a hh n t X z := rfl

theorem liftMeanComposition_first_zero (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (N : ℕ) (a : ℝ → Vec 2 → ∀ i, h i)
    (hh : ℕ) (t : ℝ) (X z : Vec 2) :
    liftMeanCompositionCoefficient Q Cc N a hh 1 t X z = 0 := by
  unfold liftMeanCompositionCoefficient
  apply Finset.sum_eq_zero
  intro r _
  rw [ite_eq_right (by omega)]
end

/-! The finite positive-degree right side supplied by the actual lift primitives. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

def liftPositiveTimeRhs (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (N : ℕ) (ε : ℝ) (hh : ℕ) (f : Vec 2 → ∀ i, h i)
    (s : ℝ) (X z : Vec 2) : ∀ i, h i :=
  ∑ n ∈ Finset.Icc 1 N, ε ^ n •
    (-cellOperator (Q.G s X) (Q.v s) (liftApply n (Cc hh n) (fun _ => f) s X) z +
      liftCellSource Q Cc (fun _ => f) hh n s X z)
end

/-! Literal component expansion of the normalized tail preserves the truncated convolution. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem liftTail_normalized_component_expansion (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (N hh n : ℕ)
    (f : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (X z : Vec 2) (v : ι) (c : ℝ) :
    c • liftTailCoeff Q Cc N f hh n t X z v = c • liftA Q Cc f hh n t X z v -
      ∑ r ∈ Finset.range (N + 1),
        if r ≤ n ∧ 2 ≤ n - r ∧ n - r ≤ N + D then
          ∑ p ∈ Finset.HasAntidiagonal.antidiagonal hh,
            c • liftApply r (Cc p.1 r) (liftMean Q Cc f p.2 (n - r)) t X z v
        else 0 := by
  simp only [liftTailCoeff, Pi.sub_apply, Finset.sum_apply, smul_sub, Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  split_ifs
  · simp only [Finset.sum_apply, Finset.smul_sum]
  · simp
end

/-! Named normalized coarse-test fields for the exact truncated lift tail. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

def normalizedLiftTailField (Q : LiftOperatorData ι h D)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (N hh n : ℕ) (A : Vec 2 →L[ℝ] ℝ)
    (u v : ι) (ξ : h u) : ℝ → Vec 2 → Vec 2 → h v :=
  fun t X z => (Real.exp (A X))⁻¹ • liftTailCoeff Q Cc N
    (fun _ Y => Real.exp (A Y) • Pi.single u ξ) hh n t X z v
end

/-! Centering changes no fast geometry; only the actual ordered corrections need checking. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem liftCellSource_normalized_transverse_of_terms (par : Fin 2) (I : Set ℝ)
    (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (f : ℝ → Vec 2 → ∀ i, h i) (hh n : ℕ) (v : ι) (A : Vec 2 →L[ℝ] ℝ) (lam : ℝ)
    (hA : IsTransverseOn par I (fun t X z => (Real.exp ((lam • A) X))⁻¹ •
      liftA Q Cc f hh n t X z v))
    (hT : ∀ j ∈ Finset.Icc 1 (n - 2), ∀ ab ∈ Finset.HasAntidiagonal.antidiagonal hh,
      IsTransverseOn par I (fun t X z => (Real.exp ((lam • A) X))⁻¹ •
        liftApply j (Cc ab.1 j) (liftMean Q Cc f ab.2 (n - j)) t X z v)) :
    IsTransverseOn par I (fun t X z => (Real.exp ((lam • A) X))⁻¹ •
      liftCellSource Q Cc f hh n t X z v) := by
  intro t ht X z s
  simp_rw [liftCellSource_normalized_component_expansion]
  have he := hA t ht X z s
  dsimp only at he
  rw [he]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro ab hab
  exact hT j hj ab hab t ht X z s

theorem liftCellSource_normalized_periodic_of_terms
    (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (f : ℝ → Vec 2 → ∀ i, h i) (hh n : ℕ) (t : ℝ) (v : ι)
    (A : Vec 2 →L[ℝ] ℝ) (lam : ℝ)
    (hA : ∀ X, AVenhance.IsZ2Periodic (fun z => (Real.exp ((lam • A) X))⁻¹ •
      liftA Q Cc f hh n t X z v))
    (hT : ∀ j ∈ Finset.Icc 1 (n - 2), ∀ ab ∈ Finset.HasAntidiagonal.antidiagonal hh,
      ∀ X, AVenhance.IsZ2Periodic (fun z => (Real.exp ((lam • A) X))⁻¹ •
        liftApply j (Cc ab.1 j) (liftMean Q Cc f ab.2 (n - j)) t X z v)) :
    ∀ X, AVenhance.IsZ2Periodic (fun z => (Real.exp ((lam • A) X))⁻¹ •
      liftCellSource Q Cc f hh n t X z v) := by
  intro X k z
  simp_rw [liftCellSource_normalized_component_expansion]
  have he := hA X k z
  dsimp only at he
  rw [he]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro ab hab
  exact hT j hj ab hab X k z
end

/-! Normalized coarse tests retain exact linearity in their actual coefficient arrays. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem normalizedLiftTestField_sub (c d : LiftCoeff ι h) (n : ℕ)
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) :
    normalizedLiftTestField (fun m α t X z i j => c m α t X z i j - d m α t X z i j)
      n A u v ξ =
      fun t X z => normalizedLiftTestField c n A u v ξ t X z -
        normalizedLiftTestField d n A u v ξ t X z := by
  funext t X z
  simp only [normalizedLiftTestField, liftApply_coefficient_sub, Pi.sub_apply, smul_sub]
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Fast Taylor composition uses each original fast jet separately, retaining the full slow reserve. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem isBoxSmooth_comp_of_jet_regularities {p q : ℕ} {f : Vec 2 → Vec 2 → E}
    (hf : IsBoxSmooth p q f) (g : E → F) (hg : ContDiff ℝ (q : ℕ∞) g)
    (hjet : ∀ b ≤ q, ContDiff ℝ (p : ℕ∞) (iteratedFDeriv ℝ b g)) :
    IsBoxSmooth p q (fun X z => g (f X z)) := by
  rw [isBoxSmooth_iff]
  refine ⟨fun X => hg.comp (hf.1 X), fun b hb => ?_⟩
  have hs : IsSlowSmooth p f := hf.isSlowSmooth
  have he : (fun X z => iteratedFDeriv ℝ b (fun y => g (f X y)) z) =
      fun X z => (ftaylorSeries ℝ g (f X z)).taylorComp (ftaylorSeries ℝ (f X) z) b := by
    funext X z
    exact iteratedFDeriv_comp hg.contDiffAt (hf.1 X).contDiffAt (by exact_mod_cast hb)
  rw [he]
  change IsSlowSmooth p (fun X z => ∑ c : OrderedFinpartition b,
    c.compAlongOrderedFinpartition (iteratedFDeriv ℝ c.length g (f X z))
      (fun i => iteratedFDeriv ℝ (c.partSize i) (f X) z))
  apply IsSlowSmooth.sum
  intro c _
  let L := c.compAlongOrderedFinpartitionL ℝ (Vec 2) E F
  have ho := isSlowSmooth_comp hs (iteratedFDeriv ℝ c.length g)
    (hjet _ (c.length_le.trans hb))
  have hi : IsSlowSmooth p (fun X z => fun i : Fin c.length =>
      iteratedFDeriv ℝ (c.partSize i) (f X) z) :=
    IsSlowSmooth.pi fun i => (isBoxSmooth_iff.mp hf).2 _ ((c.partSize_le i).trans hb)
  change IsSlowSmooth p (fun X z =>
    L (iteratedFDeriv ℝ c.length g (f X z))
      (fun i => iteratedFDeriv ℝ (c.partSize i) (f X) z))
  exact isSlowSmooth_multilinear_evaluation c.length p _ _ _
    (isSlowSmooth_clm_comp
      (G := ContinuousMultilinearMap ℝ
        (fun i : Fin c.length => ContinuousMultilinearMap ℝ
          (fun _ : Fin (c.partSize i) => Vec 2) E)
        (ContinuousMultilinearMap ℝ (fun _ : Fin b => Vec 2) F)) L ho) hi

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The source on a coarse field is a finite classical polynomial in the cell parameter. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem sourceOp_independent_expand (edge : ConstituentEdges D h) (η ε t : ℝ)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (D : ℕ∞) f)
    (hfast : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X, ContDiff ℝ 1 (γ.coeff α t X))
    (hslow : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α z,
      ContDiff ℝ 1 (fun X => γ.coeff α t X z)) (X z : Vec 2) :
    sourceOp edge η ε t (fun X _ => f X) X z =
      ∑ d : Finset.Icc 2 D,
        (ε ^ (d.1 - 1) • (∑ q : Fin 2,
          fastPartial q (slowSourceFluxOrder edge η t f d q) X z)
        + ε ^ d.1 • (Real.sqrt η • ∑ q : Fin 2,
          slowPartial q (slowSourceFluxOrder edge η t f d q) X z)) := by
  have hflux (q : Fin 2) : sourceFlux edge η ε t (fun X _ => f X) q =
      fun X z => ∑ d : Finset.Icc 2 D, ε ^ (d.1 - 1) • slowSourceFluxOrder edge η t f d q X z := by
    funext X z
    exact sourceFlux_independent_expand edge η ε t f q X z
  have hcov (q : Fin 2) : dEps η ε q (sourceFlux edge η ε t (fun X _ => f X) q) X z =
      ∑ d : Finset.Icc 2 D, ε ^ (d.1 - 1) • dEps η ε q (slowSourceFluxOrder edge η t f d q) X z := by
    rw [hflux, dEps_finset_sum]
    · apply Finset.sum_congr rfl
      intro d _
      exact congrFun (congrFun (dEps_smul η ε q (ε ^ (d.1 - 1))
        (slowSourceFluxOrder edge η t f d q)) X) z
    · intro d _
      simpa only [Pi.smul_apply] using! ((slowSourceFluxOrder_fast_contDiff edge η t f d q X
        (fun v u γ hγ α => hfast v u d γ hγ α X)).differentiable (by norm_num) z).const_smul (ε ^ (d.1 - 1))
    · intro d _
      simpa only [Pi.smul_apply] using! ((slowSourceFluxOrder_slow_contDiff edge η t f hf d q z
        (fun v u γ hγ α => hslow v u d γ hγ α z)).differentiable (by norm_num) X).const_smul (ε ^ (d.1 - 1))
  simp only [sourceOp, hcov]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  simp only [dEps, Finset.smul_sum, smul_add, Finset.sum_add_distrib, smul_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  have hd : d.1 = (d.1 - 1) + 1 := by have hh := (Finset.mem_Icc.mp d.2).1; omega
  congr 1
  conv_rhs => rw [hd, pow_succ]
  ring
end

/-! Positive fast words of the primitive are source words of one lower order. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem iteratedDeriv_centeredIntervalPrimitive_succ (m : ℕ) (f : ℝ → E)
    (hf : Continuous f) :
    iteratedDeriv (m + 1) (centeredIntervalPrimitive f) = iteratedDeriv m f := by
  rw [iteratedDeriv_succ', centeredIntervalPrimitive_deriv f hf]

theorem orderedDerivative_centeredIntervalPrimitive_profile_succ
    (m : ℕ) (α : DerivativeWord2 (m + 1)) (f : ℝ → E)
    (hf : ContDiff ℝ (m : ℕ∞) f) (p : Fin 2) :
    orderedDerivative α (fun z : Vec 2 => centeredIntervalPrimitive f (z p)) =
      fun z => if (∀ i, α i = p) then iteratedDeriv m f (z p) else 0 := by
  rw [orderedDerivative_transverse_profile α (centeredIntervalPrimitive f)
    (centeredIntervalPrimitive_contDiff m f hf) p,
    iteratedDeriv_centeredIntervalPrimitive_succ m f hf.continuous]
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Real dual profile bounds pass to the complex Fourier representation with constant one. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem complexified_real_dual_norm_le (l : E →L[ℝ] ℝ) :
    ‖Complex.ofRealCLM.comp l‖ ≤ ‖l‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg l)
  intro x
  simpa only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.norm_real,
    Real.norm_eq_abs] using l.le_opNorm x

theorem norm_mixed_complexified_linear_profile_le (p q r j : ℕ)
    (hr : r ≤ p) (hj : j ≤ q)
    (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth p q f)
    (L : ℝ →L[ℝ] Vec 2) (l : E →L[ℝ] ℝ) (X : Vec 2) (x : ℝ) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedDeriv j
      (fun y => ((l (f Y (L y)) : ℝ) : ℂ)) x) X‖ ≤
      ‖l‖ * ‖L‖ ^ j *
        ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (f Y) (L x)) X‖ := by
  apply (norm_mixed_dual_linear_profile_le p q r j hr hj f hf L
    (Complex.ofRealCLM.comp l) X x).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (complexified_real_dual_norm_le l)
      (pow_nonneg (norm_nonneg L) j)) (norm_nonneg _)
end

/-! Two extra fast derivatives supply the summable Wiener majorant. -/

theorem profile_fourier_jet_wiener_majorant (p r L : ℕ) (hr : r ≤ p)
    (F : Vec 2 → ℂ) (hF : ContDiff ℝ (p : ℕ∞) F)
    (m : ℤ) (hm : m ≠ 0) (X : Vec 2) (C : ℝ)
    (hb : ‖iteratedFDeriv ℝ r
      (fun Y => profileFourierFrequency m ^ (L + 2) * F Y) X‖ ≤ C) :
    (1 + |(m : ℝ)|) ^ L * ‖iteratedFDeriv ℝ r F X‖ ≤ profileJetMajorant C 0 m := by
  let G := fun Y => profileFourierFrequency m ^ L * F Y
  have hG : ContDiff ℝ (p : ℕ∞) G := unit_complex_mul_contDiff p F hF _
  have he : (fun Y => profileFourierFrequency m ^ 2 * G Y) =
      (fun Y => profileFourierFrequency m ^ (L + 2) * F Y) := by
    funext Y
    dsimp [G]
    rw [pow_add]
    ring
  have hd := profile_frequency_jet_decay p r 2 hr G hG m hm X C (by rw [he]; exact hb)
  apply (profile_wiener_parameter_jet_weight_le p r L hr F hF m hm X).trans
  apply hd.trans_eq
  rw [profileFourierFrequency_norm_sq]
  simp only [profileJetMajorant, ite_eq_right hm]
  ring

end AVRegularity.CycleComparison.Lift
end
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The two actual cross difference estimates combine into the height-zero source estimate. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem liftA_zero_height_paired_grading_of_cross_terms
    (Q : LiftOperatorData ι h D) (J : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (Cc Ci : ℕ → ℕ → LiftCoeff ι h) (f : ℝ → Vec 2 → ∀ i, h i)
    (n p q : ℕ) (t : ℝ) (v : ι) (A : Vec 2 →L[ℝ] ℝ) (lam K₁ K₂ : ℝ)
    (h₁ : IsBoxSmooth p q (fun X z =>
      (Real.exp ((lam • A) X))⁻¹ • cellB1 Q.η Q.G Q.v t
        (liftApply (n - 1) (Cc 0 (n - 1)) f t) X z v -
      (Real.exp ((lam • A) X))⁻¹ • cellB1 Q.η J Q.v t
        (liftApply (n - 1) (Ci 0 (n - 1)) f t) X z v))
    (hb₁ : ∀ r ≤ p, ∀ s ≤ q, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (fun y =>
        (Real.exp ((lam • A) Y))⁻¹ • cellB1 Q.η Q.G Q.v t
          (liftApply (n - 1) (Cc 0 (n - 1)) f t) Y y v -
        (Real.exp ((lam • A) Y))⁻¹ • cellB1 Q.η J Q.v t
          (liftApply (n - 1) (Ci 0 (n - 1)) f t) Y y v) z) X‖ ≤ K₁ * lam ^ (n + r))
    (h₂ : 2 ≤ n → IsBoxSmooth p q (fun X z =>
      (Real.exp ((lam • A) X))⁻¹ • cellB2 Q.η Q.G t
        (liftApply (n - 2) (Cc 0 (n - 2)) f t) X z v -
      (Real.exp ((lam • A) X))⁻¹ • cellB2 Q.η J t
        (liftApply (n - 2) (Ci 0 (n - 2)) f t) X z v))
    (hb₂ : 2 ≤ n → ∀ r ≤ p, ∀ s ≤ q, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (fun y =>
        (Real.exp ((lam • A) Y))⁻¹ • cellB2 Q.η Q.G t
          (liftApply (n - 2) (Cc 0 (n - 2)) f t) Y y v -
        (Real.exp ((lam • A) Y))⁻¹ • cellB2 Q.η J t
          (liftApply (n - 2) (Ci 0 (n - 2)) f t) Y y v) z) X‖ ≤ K₂ * lam ^ (n + r)) :
    IsBoxSmooth p q (fun X z =>
      (Real.exp ((lam • A) X))⁻¹ • liftA Q Cc f 0 n t X z v -
      (Real.exp ((lam • A) X))⁻¹ •
        liftA (⟨Q.η, J, Q.v, Q.edge⟩ : LiftOperatorData ι h D) Ci f 0 n t X z v) ∧
    ∀ r ≤ p, ∀ s ≤ q, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (fun y =>
        (Real.exp ((lam • A) Y))⁻¹ • liftA Q Cc f 0 n t Y y v -
        (Real.exp ((lam • A) Y))⁻¹ •
          liftA (⟨Q.η, J, Q.v, Q.edge⟩ : LiftOperatorData ι h D) Ci f 0 n t Y y v) z) X‖ ≤
        (K₁ + if 2 ≤ n then K₂ else 0) * lam ^ (n + r) := by
  simp_rw [liftA_zero_height_normalized_paired_expansion]
  by_cases hn₂ : 2 ≤ n
  · simp only [ite_eq_left hn₂]
    refine ⟨h₁.add (h₂ hn₂), ?_⟩
    intro r hr s hs X z
    exact ((norm_mixed_jet_add_le (h₁.mono hr hs) ((h₂ hn₂).mono hr hs) X z).trans
      (add_le_add (hb₁ r hr s hs X z) (hb₂ hn₂ r hr s hs X z))).trans_eq (by ring)
  · simp only [ite_eq_right hn₂, add_zero]
    exact ⟨h₁, hb₁⟩

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance.Infra.Torus
namespace AVRegularity.CycleComparison.Lift

/-! The zeroth source coefficient is a fast divergence and has zero cell mean. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

theorem fieldCellMean_sourceCoeff_zero (edge : ConstituentEdges D h) (η t : ℝ)
    (Φ : Vec 2 → Vec 2 → ∀ i, h i) (X : Vec 2)
    (hf : ContDiff ℝ (D : ℕ∞) (Φ X)) (hp : AVenhance.IsZ2Periodic (Φ X))
    (hc : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α,
      ContDiff ℝ (D : ℕ∞) (γ.coeff α t X)) :
    fieldCellMean (fun z => sourceCoeff edge η 0 t Φ X z) = 0 := by
  have hflux (q : Fin 2) : ContDiff ℝ 1 (sourceFlux edge η 0 t Φ q X) :=
    contDiff_pi.mpr (fun v => sourceFlux_zero_component_contDiff edge η t Φ X hf hc q v)
  have hi (q : Fin 2) : IntegrableOn
      (fun z => fderiv ℝ (sourceFlux edge η 0 t Φ q X) z (basisVec q)) (unitCell 2) :=
    Calculus.continuous_integrableOn_unitCell
      (((hflux q).continuous_fderiv (by norm_num)).clm_apply continuous_const)
  simp only [sourceCoeff, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
    iteratedDeriv_zero, sourceOp, dEps, mul_zero, zero_smul, add_zero, fastPartial,
    fieldCellMean, ← integral_unitCell_eq_unitCube]
  rw [integral_finsetSum _ (fun q _ => hi q)]
  apply Finset.sum_eq_zero
  intro q _
  have hh := fieldCellMean_fastPartial_eq_zero (sourceFlux edge η 0 t Φ q X)
    (hflux q) (sourceFlux_zero_periodic edge η t Φ X hf hp q) q
  simpa only [fieldCellMean, ← integral_unitCell_eq_unitCube] using hh

end AVRegularity.CycleComparison.Lift
end
end
