-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Lift.SettingInverseZero
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! Each nonzero source constituent is graded with its original normalized envelope budget. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem envelope_normalized_constituent_mixed_bound
    (π : ι → ℝ) (edge : ConstituentEdges D h) (I : Set ℝ)
    (lam : ℝ) (hlam : 0 < lam) (Cj : ℕ → ℕ → ℝ) (qs qf : ℕ)
    (b : ι → ι → ℝ) (Θ : ℝ) (he : IsScaledJetEnvelope π edge I lam Cj qs qf b Θ)
    (v u : ι) (hv : 0 < π v) (hu : 0 < π u)
    (d : Finset.Icc 2 D) (γ : Constituent d.val (h u) (h v))
    (hγ : γ ∈ edge v u d) (hmap : γ.map ≠ 0) (α : DerivativeWord2 (d.val - 1))
    (η : ℝ) (hη : η ≤ 1) (δ p q j : ℕ) (hp : p ≤ qs) (hq : q ≤ qf)
    (hj : j ≤ (List.ofFn α).length) (C : ℝ) (hC : 0 ≤ C)
    (A : Vec 2 →L[ℝ] ℝ) (f : Vec 2 → Vec 2 → h u)
    (t : ℝ) (ht : t ∈ I) (hbox : IsBoxSmooth p q (γ.coeff α t))
    (hf : IsBoxSmooth (p + j) (q + (List.ofFn α).length - j) f)
    (X : Vec 2) (hbf : ∀ a ≤ p + j, ∀ s ≤ q + (List.ofFn α).length - j, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ s (f Y) z) X‖ ≤ C * lam ^ (δ + a))
    (k : Fin 2) (z : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • (γ.coeff α t Y y k •
        γ.map (covariantListCoefficients η (List.ofFn α)
          (fun Z y => Real.exp ((lam • A) Z) • f Z y) j Y y))) z) X‖ ≤
      (normalizedCovariantProductConstant p q j (List.ofFn α) A *
        constituentUniformMixedBudget I p q lam (γ.coeff α) * ‖γ.map‖ * C) *
          lam ^ (δ + j + p) := by
  have hfin : ∀ a ≤ p, ∀ s ≤ q, jetSup I a s (γ.coeff α) < ⊤ := by
    intro a ha s hs
    exact scaledEnvelope_constituent_jet_finite π edge I lam Cj qs qf b Θ he
      v u hv hu d γ hγ hmap α a s (ha.trans hp) (hs.trans hq)
  exact norm_mixed_normalized_covariant_product_le η hη δ p q j lam
    (constituentUniformMixedBudget I p q lam (γ.coeff α)) C hlam.le
    (constituentUniformMixedBudget_nonneg I p q lam hlam.le _) hC
    (List.ofFn α) hj A (fun Y y => γ.coeff α t Y y k) f γ.map
    (hbox.clm_comp (ContinuousLinearMap.proj k)) hf X
    (fun a ha s hs z => constituentScalarMixedBudget_bounds I p q lam hlam
      (γ.coeff α) hfin t ht hbox k a s ha hs X z) hbf z

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! A shear in the parallel direction annihilates each transverse Fourier state in the actual L² drift operator. -/

theorem transverseFourierModeH1_drift_zero (C : CellCoefficients) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t z, ∑ i, C.v t z i ^ 2 ≤ V ^ 2)
    (par : Fin 2) (ht : ∀ t z, C.v t z par.rev = 0)
    (t : ℝ) (n : ℤ) (j : Fin 2) :
    cellDriftEntryCLM C V hv hb t j (cellDerivativeCLM j (transverseFourierModeH1 par n)) = 0 := by
  apply Lp.ext
  filter_upwards [cellDriftEntryCLM_ae C V hv hb t j
    (cellDerivativeCLM j (transverseFourierModeH1 par n)),
    transverseFourierModeH1_derivative_ae par n j, Lp.coeFn_zero (ℂ)
      2 (volume.restrict AVenhance.unitCube)] with z hd hj hz
  rw [hd, hj, hz]
  by_cases he : j = par.rev
  · simp only [he, ite_true, ht, Complex.ofReal_zero, zero_mul, Pi.zero_apply]
  · simp only [he, ite_false, mul_zero, Pi.zero_apply]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The full polynomial source-flux convolution has finite tested order. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

def sourceFluxConvolutionLeftTerms (edge : ConstituentEdges D h) (η t : ℝ)
    (n : ℕ) (c : ℕ → LiftCoeff ι h) (k : Fin 2) (v : ι) :
    List (LeftTerm (∀ i, h i) (h v)) :=
  (Finset.range (min (D - 1) n + 1)).toList.flatMap fun j =>
    sourceFluxLeftTerms edge η t (n - j) (c (n - j)) k j v

theorem sourceFluxConvolutionLeftTerms_order (edge : ConstituentEdges D h) (η t : ℝ)
    (n : ℕ) (c : ℕ → LiftCoeff ι h) (k : Fin 2) (v : ι)
    (e : LeftTerm (∀ i, h i) (h v))
    (he : e ∈ sourceFluxConvolutionLeftTerms edge η t n c k v) : e.order ≤ n := by
  obtain ⟨j, hj, he⟩ := List.mem_flatMap.mp he
  have hjn : j ≤ n := by
    have hh := Finset.mem_range.mp (Finset.mem_toList.mp hj)
    omega
  have hb := sourceFluxLeftTerms_order edge η t (n - j) (c (n - j)) k j v e he
  omega
end

/-! Calibrated coarse-test bounds control coefficient operator jets with no component-dimension factor. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]

theorem symmetric_lift_coefficient_mixed_bound_of_tests
    (c : LiftCoeff ι h) (n m p q : ℕ) (hm : m ≤ n)
    (hc : ∀ β (σ : Equiv.Perm (Fin m)), c m (β ∘ σ) = c m β)
    (α : DerivativeWord2 m) (lam : ℝ) (hlam : 0 < lam) (u v : ι) (t : ℝ)
    (K : (Vec 2 →L[ℝ] ℝ) → ℝ) (hK : ∀ A, 0 ≤ K A) (M : ℝ) (hM : 0 ≤ M)
    (hbox : ∀ (ξ : h u) (A : Vec 2 →L[ℝ] ℝ),
      IsBoxSmooth p q (normalizedLiftTestField c n (lam • A) u v ξ t))
    (hb : ∀ (ξ : h u) (A : Vec 2 →L[ℝ] ℝ), ∀ r ≤ p, ∀ s ≤ q, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
        (normalizedLiftTestField c n (lam • A) u v ξ t Y) z) X‖ ≤
          (K A * M * ‖ξ‖) * lam ^ (n + r))
    (r s : ℕ) (hr : r ≤ p) (hs : s ≤ q) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (fun y => c m α t Y y v u) z) X‖ ≤
      (∑ j : Fin (m + 1) × Fin (n + 1), |liftCalibrationWeight n m α lam j| *
        K ((j.2 : ℝ) • coordinateSymbolDirection (j.1 : ℝ))) * M * lam ^ (n + r) := by
  have hbox' := symmetric_lift_coefficient_box_of_tests c n m p q hm hc α lam hlam.ne' u v t hbox
  have hsum : 0 ≤ ∑ j : Fin (m + 1) × Fin (n + 1), |liftCalibrationWeight n m α lam j| *
      K ((j.2 : ℝ) • coordinateSymbolDirection (j.1 : ℝ)) :=
    Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (hK _)
  apply mixed_operator_jet_norm_le_from_apply r s _ (hbox'.mono hr hs) X z _
    (mul_nonneg (mul_nonneg hsum hM) (pow_nonneg hlam.le _))
  intro ξ
  have he : (fun X z => c m α t X z v u ξ) =
      calibratedLiftCoefficientEntry c n m α lam u v ξ t := by
    funext Y y
    exact (calibratedLiftCoefficientEntry_eq c n m hm hc α lam hlam.ne' u v ξ t Y y).symm
  have hp (Y y : Vec 2) := congrFun (congrFun he Y) y
  simp_rw [hp]
  have hh := calibratedLiftCoefficientEntry_mixed_bound c n m p q α lam u v ξ t K M
    (hbox ξ) (hb ξ) r s hr hs X z
  convert hh using 1
  ring
end

end AVRegularity.CycleComparison.Lift
end

section
namespace AVRegularity.CycleComparison.Lift

/-! One original-data inverse constant controls every slow suborder of the ambient reserve. -/

def ambientInverseUniformConstant (p : ℕ) (M κ : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (p + 1),
    parameterizedModeJetConstant p r M 1 κ (fun s => (2 : ℝ) ^ s) * centeredProfileJetConstant

theorem ambientInverseUniformConstant_entry_le (p r : ℕ) (hr : r ≤ p) (M κ : ℝ)
    (hM : 0 ≤ M) (hκ : 0 < κ) :
    parameterizedModeJetConstant p r M 1 κ (fun s => (2 : ℝ) ^ s) * centeredProfileJetConstant ≤
      ambientInverseUniformConstant p M κ := by
  exact Finset.single_le_sum (fun r _ => mul_nonneg
    (parameterizedModeJetConstant_nonneg p r M 1 κ _ hM (by norm_num) hκ
      (fun s _ => by positivity)) centeredProfileJetConstant_nonneg)
    (Finset.mem_range.mpr (by omega))

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Actual symmetric coefficients inherit a fixed finite-direction test budget without changing ambient orders. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]

theorem liftCoefficient_grading_of_direction_budget
    (N n m p q : ℕ) (c : LiftCoeff ι h)
    (hsym : ∀ m (α : DerivativeWord2 m) (σ : Equiv.Perm (Fin m)), c m (α ∘ σ) = c m α) (hn : n ≤ N) (hm : m ≤ n)
    (α : DerivativeWord2 m) (t : ℝ) (v u : ι) (X z : Vec 2)
    (lam B : ℝ) (hlam : 0 < lam) (hB : 0 ≤ B) (K : (Vec 2 →L[ℝ] ℝ) → ℝ)
    (htest : ∀ A : Vec 2 →L[ℝ] ℝ, ∀ ξ : h u,
      IsBoxSmooth p q (normalizedLiftTestField c n (lam • A) u v ξ t))
    (hb : ∀ A : Vec 2 →L[ℝ] ℝ, ∀ ξ : h u,
      ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
        (normalizedLiftTestField c n (lam • A) u v ξ t Y) z) X‖ ≤
          (K A * B * ‖ξ‖) * lam ^ (n + p)) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => c m α t Y y v u) z) X‖ ≤
        (finiteLiftCalibrationBudget N * finiteLiftTestDirectionBudget N K * B) * lam ^ (n - m + p) := by
  let C := finiteLiftTestDirectionBudget N K
  have hC : 0 ≤ C := finiteLiftTestDirectionBudget_nonneg N K
  have hs (j : Fin (m + 1)) (s : Fin (n + 1)) :
      K ((s : ℝ) • coordinateSymbolDirection (j : ℝ)) ≤ C :=
    finiteLiftTestDirectionBudget_entry_le N s.val j.val
      (by have hh' := s.isLt; omega) (by have hh' := j.isLt; omega) K
  have hdir (j : Fin (m + 1)) (s : Fin (n + 1)) :
      lam • ((s : ℝ) • coordinateSymbolDirection (j : ℝ)) =
        (s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ)) := smul_comm _ _ _
  have hcoef := liftCoefficient_mixed_grading_of_finite_tests p q n m hm c lam hlam
    (hsym m) α t v u
    (fun ξ j s => by
      have ht := htest ((s : ℝ) • coordinateSymbolDirection (j : ℝ)) ξ
      rw [hdir j s] at ht
      exact ht)
    X z (C * B) (mul_nonneg hC hB) ?_
  · apply hcoef.trans
    have hc := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (finiteTestCalibrationConstant_le_budget N n m hn (hm.trans hn) α)
        (mul_nonneg hC hB)) (pow_nonneg hlam.le (n - m + p))
    convert hc using 1
    dsimp only [C]
    ring
  · intro ξ j s
    have ht := hb ((s : ℝ) • coordinateSymbolDirection (j : ℝ)) ξ
    rw [hdir j s] at ht
    apply ht.trans
    have hc := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hs j s) hB) (norm_nonneg ξ))
      (pow_nonneg hlam.le (n + p))
    convert hc using 1
    ring
end

/-! Actual symmetric coefficients inherit a fixed finite-direction test budget without changing ambient orders. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem liftSequence_coefficient_grading_of_direction_budget (Q : LiftOperatorData ι h D)
    (sX sZ : ℕ) (a b : ℝ) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (hh n m p q : ℕ) (hhh : hh ≤ H) (hn : n ≤ N) (hm : m ≤ n)
    (α : DerivativeWord2 m) (t : ℝ) (v u : ι) (X z : Vec 2)
    (lam B : ℝ) (hlam : 0 < lam) (hB : 0 ≤ B) (K : (Vec 2 →L[ℝ] ℝ) → ℝ)
    (htest : ∀ A : Vec 2 →L[ℝ] ℝ, ∀ ξ : h u,
      IsBoxSmooth p q (normalizedLiftTestField (Cc hh n) n (lam • A) u v ξ t))
    (hb : ∀ A : Vec 2 →L[ℝ] ℝ, ∀ ξ : h u,
      ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
        (normalizedLiftTestField (Cc hh n) n (lam • A) u v ξ t Y) z) X‖ ≤
          (K A * B * ‖ξ‖) * lam ^ (n + p)) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => Cc hh n m α t Y y v u) z) X‖ ≤
        (finiteLiftCalibrationBudget N * finiteLiftTestDirectionBudget N K * B) * lam ^ (n - m + p) := by
  let C := finiteLiftTestDirectionBudget N K
  have hC : 0 ≤ C := finiteLiftTestDirectionBudget_nonneg N K
  have hs (j : Fin (m + 1)) (s : Fin (n + 1)) :
      K ((s : ℝ) • coordinateSymbolDirection (j : ℝ)) ≤ C :=
    finiteLiftTestDirectionBudget_entry_le N s.val j.val
      (by have hh' := s.isLt; omega) (by have hh' := j.isLt; omega) K
  have hdir (j : Fin (m + 1)) (s : Fin (n + 1)) :
      lam • ((s : ℝ) • coordinateSymbolDirection (j : ℝ)) =
        (s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ)) := smul_comm _ _ _
  have hcoef := liftCoefficient_mixed_grading_of_finite_tests p q n m hm (Cc hh n) lam hlam
    (hseq.2.2.2.2.1 hh hhh n m) α t v u
    (fun ξ j s => by
      have ht := htest ((s : ℝ) • coordinateSymbolDirection (j : ℝ)) ξ
      rw [hdir j s] at ht
      exact ht)
    X z (C * B) (mul_nonneg hC hB) ?_
  · apply hcoef.trans
    have hc := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (finiteTestCalibrationConstant_le_budget N n m hn (hm.trans hn) α)
        (mul_nonneg hC hB)) (pow_nonneg hlam.le (n - m + p))
    convert hc using 1
    dsimp only [C]
    ring
  · intro ξ j s
    have ht := hb ((s : ℝ) • coordinateSymbolDirection (j : ℝ)) ξ
    rw [hdir j s] at ht
    apply ht.trans
    have hc := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hs j s) hB) (norm_nonneg ξ))
      (pow_nonneg hlam.le (n + p))
    convert hc using 1
    ring
end

/-! Full finite source-flux terms reproduce the literal component convolution. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem sourceFluxConvolutionLeftTerms_apply (edge : ConstituentEdges D h) (η t : ℝ)
    (n : ℕ) (c : ℕ → LiftCoeff ι h) (k : Fin 2) (v : ι)
    (hc : ∀ j ≤ min (D - 1) n, ∀ m ≤ n - j, ∀ α : DerivativeWord2 m, ∀ u u',
      IsBoxSmooth j ((D - 1) - j) (fun X z => c (n - j) m α t X z u u'))
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (X z : Vec 2) :
    leftTermsApply (sourceFluxConvolutionLeftTerms edge η t n c k v) f X z =
      ∑ j ∈ Finset.range (min (D - 1) n + 1),
        sourceFluxComponentCoefficient edge η t
          (liftApply (n - j) (c (n - j)) (fun _ => f) t) k j v X z := by
  unfold sourceFluxConvolutionLeftTerms
  rw [leftTermsApply_finset_flatMap]
  apply Finset.sum_congr rfl
  intro j hj
  exact sourceFluxLeftTerms_apply edge η t (n - j) (c (n - j)) k j v
    (hc j (by have hh := Finset.mem_range.mp hj; omega)) f hf X z
end

/-! Full source-flux convolution coefficients retain their ambient slow reserve. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem sourceFluxConvolutionLeftTerms_box (edge : ConstituentEdges D h) (η t : ℝ)
    (n : ℕ) (c : ℕ → LiftCoeff ι h) (k : Fin 2) (p q : ℕ) (v : ι)
    (hc : ∀ j ≤ min (D - 1) n, ∀ m ≤ n - j, ∀ α : DerivativeWord2 m, ∀ u u',
      IsBoxSmooth (p + j) (q + (D - 1) - j) (fun X z => c (n - j) m α t X z u u'))
    (hΓ : ∀ u d, ∀ γ ∈ edge v u d, ∀ α,
      IsBoxSmooth p q (fun X z => γ.coeff α t X z k))
    (e : LeftTerm (∀ i, h i) (h v))
    (he : e ∈ sourceFluxConvolutionLeftTerms edge η t n c k v) :
    IsBoxSmooth p q e.coeff := by
  obtain ⟨j, hj, he⟩ := List.mem_flatMap.mp he
  have hj' : j ≤ min (D - 1) n := by
    have hh := Finset.mem_range.mp (Finset.mem_toList.mp hj)
    omega
  exact sourceFluxLeftTerms_box edge η t (n - j) (c (n - j)) k j p q v
    (hc j hj') hΓ e he
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! Box regularity and periodicity of centered transverse flux fields. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem transverseCenteredFlux_box_and_periodic
    (par k : Fin 2) (p q : ℕ) (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth p q f)
    (hfactor : ∀ X z, f X z = f X ((z par.rev) • basisVec par.rev))
    (C : ℕ → ℝ)
    (hb : ∀ j ≤ p, ∀ (r : ℝ) (X : Vec 2),
      ‖iteratedFDeriv ℝ j (fun Y => f Y (r • basisVec par.rev)) X‖ ≤ C j)
    (hp : ∀ X, AVenhance.IsZ2Periodic (f X))
    (hz : ∀ X, fieldCellMean (f X) = 0) :
    IsBoxSmooth p (q + 1) (fun X z => transverseCenteredFlux par
      (fun r => f X (r • basisVec par.rev)) k z) ∧
    ∀ X, AVenhance.IsZ2Periodic (fun z => transverseCenteredFlux par
      (fun r => f X (r • basisVec par.rev)) k z) := by
  refine ⟨?_, ?_⟩
  · by_cases hk : k = par.rev
    · have he : (fun X z => transverseCenteredFlux par
          (fun r => f X (r • basisVec par.rev)) k z) = transversePrimitiveField par.rev f := by
        funext X z
        exact ite_eq_left hk
      rw [he]
      exact transversePrimitiveField_boxSmooth par.rev p q f hf hfactor C hb
    · have he : (fun X z => transverseCenteredFlux par
          (fun r => f X (r • basisVec par.rev)) k z) = 0 := by
        funext X z
        exact ite_eq_right hk
      rw [he]
      exact IsBoxSmooth.zero
  · intro X
    let line : ℝ →L[ℝ] Vec 2 := (ContinuousLinearMap.id ℝ ℝ).smulRight (basisVec par.rev)
    have hc : Continuous (fun r : ℝ => f X (r • basisVec par.rev)) :=
      (hf.1 X).continuous.comp line.continuous
    have hper := cell_periodic_linear_profile par.rev (f X) (fun n z => hp X n z)
    have hmean : (∫ r in (0 : ℝ)..1, f X (r • basisVec par.rev)) = 0 := by
      have he : (fun z => f X ((z par.rev) • basisVec par.rev)) = f X :=
        funext fun z => (hfactor X z).symm
      have hcell : fieldCellMean (fun z => f X ((z par.rev) • basisVec par.rev)) = 0 := by
        rw [he]
        exact hz X
      change (∫ z in AVenhance.unitCube, f X ((z par.rev) • basisVec par.rev)) = 0 at hcell
      rw [integral_coordinate_eq_intervalIntegral par.rev _ hc] at hcell
      exact hcell
    exact transverseCenteredFlux_periodic par k _ hc hper hmean
end

/-! Uniform source slow jets control the transverse flux on the actual fast cell. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem transverseCenteredFlux_slow_norm_le
    (par dir : Fin 2) (p q : ℕ) (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth p q f)
    (C : ℕ → ℝ)
    (hb : ∀ j ≤ p, ∀ (r : ℝ) (X : Vec 2),
      ‖iteratedFDeriv ℝ j (fun Y => f Y (r • basisVec par.rev)) X‖ ≤ C j)
    (j : ℕ) (hj : j ≤ p) (X z : Vec 2) (hz : z par.rev ∈ Set.Icc (0 : ℝ) 1) :
    ‖iteratedFDeriv ℝ j (fun Y => transverseCenteredFlux par
      (fun r => f Y (r • basisVec par.rev)) dir z) X‖ ≤ (2 : ℝ) ^ j * (2 * C j) := by
  have hC : 0 ≤ C j := (norm_nonneg _).trans (hb j hj 0 0)
  by_cases hd : dir = par.rev
  · have he : (fun Y => transverseCenteredFlux par
        (fun r => f Y (r • basisVec par.rev)) dir z) =
        fun Y => centeredIntervalPrimitive (fun r => f Y (r • basisVec par.rev)) (z par.rev) := by
      funext Y
      exact ite_eq_left hd
    rw [he]
    exact parameter_centeredIntervalPrimitive_slow_norm_le p
      (fun r Y => f Y (r • basisVec par.rev))
      (fun Y => (hf.1 Y).continuous.comp (continuous_id.smul continuous_const))
      (fun r => boxSmooth_slow_contDiff hf (r • basisVec par.rev)) C hb j hj X _ hz
  · have he : (fun Y => transverseCenteredFlux par
        (fun r => f Y (r • basisVec par.rev)) dir z) = 0 := by
      funext Y
      exact ite_eq_right hd
    rw [he, iteratedFDeriv_zero]
    change ‖(0 : ContinuousMultilinearMap ℝ (fun _ : Fin j => Vec 2) E)‖ ≤ _
    rw [norm_zero]
    exact mul_nonneg (pow_nonneg (by norm_num) _) (mul_nonneg (by norm_num) hC)
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! Parameter-dependent forcing has a genuine uniform Fourier synthesis reserve. -/

def parameterizedProfileResponse (g : ℝ → Vec 2 → ℝ) (U : ℤ → ℝ → Vec 2 → ℂ)
    (a b : ℝ) (X : Vec 2) (z : ℝ) : ℂ :=
  profileFourierSeries (fun m => transverseModeResponse (‖profileFourierFrequency m‖ ^ 2)
    (fun t => g t X) (fun t => U m t X) a b) z

theorem parameterizedProfileResponse_reserve (p : ℕ)
    (g : ℝ → Vec 2 → ℝ) (hm : ∀ X, Measurable (fun t => g t X))
    (hs : ∀ t, ContDiff ℝ (p : ℕ∞) (g t))
    (M lam κ a b : ℝ) (hM : 0 ≤ M) (hlam : 0 ≤ lam) (hκ : 0 < κ) (hab : a ≤ b)
    (hb : ∀ r ≤ p, ∀ t X, ‖iteratedFDeriv ℝ r (g t) X‖ ≤ M * lam ^ r)
    (hgl : ∀ t X, κ ≤ g t X)
    (U : ℤ → ℝ → Vec 2 → ℂ) (hUm : ∀ m X, Measurable (fun t => U m t X))
    (hUs : ∀ m t, ContDiff ℝ (p : ℕ∞) (U m t))
    (S : ℕ → ℝ) (hS : ∀ r ≤ p, 0 ≤ S r)
    (hUb : ∀ r ≤ p, ∀ m t X, ‖iteratedFDeriv ℝ r (U m t) X‖ ≤ S r * lam ^ r)
    (hU0 : ∀ t X, U 0 t X = 0) :
    (∀ z, ContDiff ℝ (p : ℕ∞) (fun X => parameterizedProfileResponse g U a b X z)) ∧
    (∀ q ≤ p, Continuous (fun x : Vec 2 × ℝ => iteratedFDeriv ℝ q
      (fun X => parameterizedProfileResponse g U a b X x.2) x.1)) ∧
    ∀ q ≤ p, ∀ X z,
      ‖iteratedFDeriv ℝ q (fun Y => parameterizedProfileResponse g U a b Y z) X‖ ≤
        parameterizedModeJetConstant p q M lam κ S * centeredProfileJetConstant := by
  let F := fun m X => transverseModeResponse (‖profileFourierFrequency m‖ ^ 2)
    (fun t => g t X) (fun t => U m t X) a b
  let V := fun q => profileJetMajorant (parameterizedModeJetConstant p q M lam κ S) 0
  have hmode : ∀ m, ContDiff ℝ (p : ℕ∞) (F m) := fun m =>
    transverseModeResponse_parameter_contDiff p g hm hs M lam _ κ a b
      hM hlam (sq_nonneg _) hκ hab hb hgl (U m) (hUm m) (hUs m) S hS
      (fun r hr => hUb r hr m)
  have hsum : ∀ q ≤ p, Summable (V q) := fun _ _ => profileJetMajorant_summable _ _
  have hbound : ∀ q ≤ p, ∀ m X, ‖iteratedFDeriv ℝ q (F m) X‖ ≤ V q m :=
    fun q hq => parameterizedModeResponse_jet_bound p q hq g hm hs M lam κ a b
      hM hlam hκ hab hb hgl U hUm hUs S hS hUb hU0
  refine ⟨?_, ?_, ?_⟩
  · intro z
    change ContDiff ℝ (p : ℕ∞)
      (fun X => ∑' m : ℤ, fourier m (z : AddCircle (1 : ℝ)) * F m X)
    refine contDiff_tsum (fun m => unit_complex_mul_contDiff p _ (hmode m) _)
      (fun q hq => hsum q (by exact_mod_cast hq)) ?_
    intro q m X hq
    exact (norm_iteratedFDeriv_unit_complex_mul_le p q (by exact_mod_cast hq)
      _ (hmode m) _ (by simp only [fourier_apply, Circle.norm_coe]) X).trans
      (hbound q (by exact_mod_cast hq) m X)
  · intro q hq
    exact fourier_parameter_jet_continuous p q hq F hmode V hsum hbound
  · intro q hq X z
    exact (fourier_parameter_jet_norm_le p q hq F hmode V hsum hbound X z).trans_eq
      (profileJetMajorant_tsum_centered _)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The full source divergence is one existing covariant step on its explicit flux terms. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

def sourceConvolutionLeftTerms (edge : ConstituentEdges D h) (η t : ℝ)
    (n : ℕ) (c : ℕ → LiftCoeff ι h) (v : ι) : List (LeftTerm (∀ i, h i) (h v)) :=
  (Finset.univ.toList : List (Fin 2)).flatMap fun k =>
    covariantLeftTermStep η k (fun m => sourceFluxConvolutionLeftTerms edge η t m c k v) n

theorem sourceConvolutionLeftTerms_order (edge : ConstituentEdges D h) (η t : ℝ)
    (n : ℕ) (c : ℕ → LiftCoeff ι h) (v : ι)
    (e : LeftTerm (∀ i, h i) (h v)) (he : e ∈ sourceConvolutionLeftTerms edge η t n c v) :
    e.order ≤ n := by
  obtain ⟨k, _, hk⟩ := List.mem_flatMap.mp he
  have hb := covariantLeftTermStep_order η k
    (fun m => sourceFluxConvolutionLeftTerms edge η t m c k v) n 0
    (fun d hd => by simpa only [Nat.zero_add] using sourceFluxConvolutionLeftTerms_order edge η t n c k v d hd)
    (fun _ d hd => by simpa only [Nat.zero_add] using sourceFluxConvolutionLeftTerms_order edge η t (n - 1) c k v d hd)
    e hk
  simpa only [Nat.zero_add] using hb

theorem sourceConvolutionLeftTerms_apply (edge : ConstituentEdges D h) (η t : ℝ)
    (n : ℕ) (c : ℕ → LiftCoeff ι h) (v : ι)
    (hfast : ∀ k d, d ∈ sourceFluxConvolutionLeftTerms edge η t n c k v → IsBoxSmooth 0 1 d.coeff)
    (hslow : n ≠ 0 → ∀ k d, d ∈ sourceFluxConvolutionLeftTerms edge η t (n - 1) c k v →
      IsBoxSmooth 1 0 d.coeff)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (X z : Vec 2) :
    leftTermsApply (sourceConvolutionLeftTerms edge η t n c v) f X z =
      ∑ k : Fin 2, covariantCoefficientStep η k
        (fun m => leftTermsApply (sourceFluxConvolutionLeftTerms edge η t m c k v) f) n X z := by
  unfold sourceConvolutionLeftTerms
  rw [leftTermsApply_finset_flatMap]
  apply Finset.sum_congr rfl
  intro k _
  rw [covariantLeftTermStep_apply η k
    (fun m => sourceFluxConvolutionLeftTerms edge η t m c k v) n
    (hfast k) (fun hn => hslow hn k) f hf]
end

/-! Calibrated coarse-test bounds control coefficient operator jets with no component-dimension factor. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]

theorem symmetric_lift_coefficient_graded_bound_of_tests
    (c : LiftCoeff ι h) (n m p q : ℕ) (hm : m ≤ n)
    (hc : ∀ β (σ : Equiv.Perm (Fin m)), c m (β ∘ σ) = c m β)
    (α : DerivativeWord2 m) (lam : ℝ) (hlam : 0 < lam) (u v : ι) (t : ℝ)
    (K : (Vec 2 →L[ℝ] ℝ) → ℝ) (hK : ∀ A, 0 ≤ K A) (M : ℝ) (hM : 0 ≤ M)
    (hbox : ∀ (ξ : h u) (A : Vec 2 →L[ℝ] ℝ),
      IsBoxSmooth p q (normalizedLiftTestField c n (lam • A) u v ξ t))
    (hb : ∀ (ξ : h u) (A : Vec 2 →L[ℝ] ℝ), ∀ r ≤ p, ∀ s ≤ q, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
        (normalizedLiftTestField c n (lam • A) u v ξ t Y) z) X‖ ≤
          (K A * M * ‖ξ‖) * lam ^ (n + r))
    (r s : ℕ) (hr : r ≤ p) (hs : s ≤ q) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (fun y => c m α t Y y v u) z) X‖ ≤
      (∑ j : Fin (m + 1) × Fin (n + 1), |liftCalibrationWeight n m α 1 j| *
        K ((j.2 : ℝ) • coordinateSymbolDirection (j.1 : ℝ))) * M * lam ^ (n - m + r) := by

  have hh := symmetric_lift_coefficient_mixed_bound_of_tests c n m p q hm hc α lam hlam
    u v t K hK M hM hbox hb r s hr hs X z
  let B := ∑ j : Fin (m + 1) × Fin (n + 1), |liftCalibrationWeight n m α 1 j| *
    K ((j.2 : ℝ) • coordinateSymbolDirection (j.1 : ℝ))
  have hsum : (∑ j : Fin (m + 1) × Fin (n + 1), |liftCalibrationWeight n m α lam j| *
      K ((j.2 : ℝ) • coordinateSymbolDirection (j.1 : ℝ))) = (lam ^ m)⁻¹ * B := by
    simp_rw [liftCalibrationWeight_abs_scale n m α lam hlam, mul_assoc]
    exact (Finset.mul_sum _ _ _).symm
  rw [hsum] at hh
  have he : ((lam ^ m)⁻¹ * B) * M * lam ^ (n + r) = B * M * lam ^ (n - m + r) := by
    calc
      _ = (B * M) * ((lam ^ m)⁻¹ * lam ^ (n + r)) := by ring
      _ = _ := by rw [inverse_power_mul_graded_power lam hlam.ne' n m r hm]
  rw [he] at hh
  exact hh
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Rectangular ambient coefficient bounds control the literal energy jets. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem AmbientLiftCoefficientData.cellEnergyJet_le
    {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b} {n p q : ℕ}
    {c : LiftCoeff ι h} {M : ι → ι → ℝ}
    (data : AmbientLiftCoefficientData par a b hab lam n p q c M)
    (hlam : 0 ≤ lam) {m r fast : ℕ} (hm : m ≤ n) (hr : r ≤ p)
    (hfast : fast + 1 ≤ q) (α : DerivativeWord2 m) (v u : ι) :
    cellEnergyJet (Set.Icc a b) fast r (fun t X z => c m α t X z v u) ≤
      ∑ _s ∈ Finset.range (fast + 1),
        ENNReal.ofReal (2 ^ r *
          (M v u * lam ^ (n - m + r) + M v u * lam ^ (n - m + r))) := by
  unfold cellEnergyJet
  apply Finset.sum_le_sum
  intro s hs
  have hsq : s + 1 ≤ q :=
    (Nat.succ_le_of_lt (Finset.mem_range.mp hs)).trans hfast
  apply iSup_le
  intro X
  exact rectangular_mixed_fieldEnergyNorm_le (Set.Icc a b) measurableSet_Icc
    (fun t X z => c m α t X z v u) r s X
    (fun t ht => (data.box m hm α v u t ht).mono hr hsq)
    _ _ (mul_nonneg (data.nonneg v u) (pow_nonneg hlam _))
    (mul_nonneg (data.nonneg v u) (pow_nonneg hlam _))
    (fun t ht z => data.bound m hm α v u r hr s
      ((Nat.le_succ s).trans hsq) t ht X z)
    (fun t ht z => data.bound m hm α v u r hr (s + 1) hsq t ht X z)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Symmetric paired coefficients inherit the fixed finite-direction test difference budget. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]

theorem paired_coefficient_grading_of_direction_budget
    (c ci : LiftCoeff ι h) (N n m p q : ℕ) (hn : n ≤ N) (hm : m ≤ n)
    (hc : ∀ β (σ : Equiv.Perm (Fin m)), c m (β ∘ σ) = c m β)
    (hci : ∀ β (σ : Equiv.Perm (Fin m)), ci m (β ∘ σ) = ci m β)
    (α : DerivativeWord2 m) (t : ℝ) (v u : ι) (X z : Vec 2)
    (lam B : ℝ) (hlam : 0 < lam) (hB : 0 ≤ B) (K : (Vec 2 →L[ℝ] ℝ) → ℝ)
    (htest : ∀ A : Vec 2 →L[ℝ] ℝ, ∀ ξ : h u,
      IsBoxSmooth p q ((fun Y y => normalizedLiftTestField c n (lam • A) u v ξ t Y y -
        normalizedLiftTestField ci n (lam • A) u v ξ t Y y)))
    (hb : ∀ A : Vec 2 →L[ℝ] ℝ, ∀ ξ : h u,
      ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
        ((fun Y y => normalizedLiftTestField c n (lam • A) u v ξ t Y y -
        normalizedLiftTestField ci n (lam • A) u v ξ t Y y) Y) z) X‖ ≤
          (K A * B * ‖ξ‖) * lam ^ (n + p)) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => c m α t Y y v u - ci m α t Y y v u) z) X‖ ≤
        (finiteLiftCalibrationBudget N * finiteLiftTestDirectionBudget N K * B) * lam ^ (n - m + p)  := by
  let dc : LiftCoeff ι h := fun d β s Y y i j => c d β s Y y i j - ci d β s Y y i j
  have hdc : ∀ β (σ : Equiv.Perm (Fin m)), dc m (β ∘ σ) = dc m β := by
    intro β σ
    funext s Y y i j
    change c m (β ∘ σ) s Y y i j - ci m (β ∘ σ) s Y y i j = _
    rw [hc β σ, hci β σ]
  have he (A : Vec 2 →L[ℝ] ℝ) (ξ : h u) :
      normalizedLiftTestField dc n (lam • A) u v ξ t =
        fun Y y => normalizedLiftTestField c n (lam • A) u v ξ t Y y -
          normalizedLiftTestField ci n (lam • A) u v ξ t Y y := by
    exact congrArg (fun F => F t) (normalizedLiftTestField_sub c ci n (lam • A) u v ξ)
  let C := finiteLiftTestDirectionBudget N K
  have hC : 0 ≤ C := finiteLiftTestDirectionBudget_nonneg N K
  have hs (j : Fin (m + 1)) (s : Fin (n + 1)) :
      K ((s : ℝ) • coordinateSymbolDirection (j : ℝ)) ≤ C :=
    finiteLiftTestDirectionBudget_entry_le N s.val j.val
      (by have hh' := s.isLt; omega) (by have hh' := j.isLt; omega) K
  have hdir (j : Fin (m + 1)) (s : Fin (n + 1)) :
      lam • ((s : ℝ) • coordinateSymbolDirection (j : ℝ)) =
        (s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ)) := smul_comm _ _ _
  have hcoef := liftCoefficient_mixed_grading_of_finite_tests p q n m hm dc lam hlam
    hdc α t v u
    (fun ξ j s => by
      have ht := htest ((s : ℝ) • coordinateSymbolDirection (j : ℝ)) ξ
      rw [← he] at ht
      rw [hdir j s] at ht
      exact ht)
    X z (C * B) (mul_nonneg hC hB) ?_
  · apply hcoef.trans
    have hc := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (finiteTestCalibrationConstant_le_budget N n m hn (hm.trans hn) α)
        (mul_nonneg hC hB)) (pow_nonneg hlam.le (n - m + p))
    convert hc using 1
    dsimp only [C]
    ring
  · intro ξ j s
    have ht := hb ((s : ℝ) • coordinateSymbolDirection (j : ℝ)) ξ
    rw [← he] at ht
    rw [hdir j s] at ht
    apply ht.trans
    have hc := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hs j s) hB) (norm_nonneg ξ))
      (pow_nonneg hlam.le (n + p))
    convert hc using 1
    ring

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The finite ordered-word array contributes only its fixed cardinality. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem AmbientLiftCoefficientData.energyArray_le
    {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b} {n p q : ℕ}
    {c : LiftCoeff ι h} {M : ι → ι → ℝ}
    (data : AmbientLiftCoefficientData par a b hab lam n p q c M)
    (hlam : 0 ≤ lam) {m r fast : ℕ} (hm : m ≤ n) (hr : r ≤ p)
    (hfast : fast + 1 ≤ q) (v u : ι) :
    (∑ α : DerivativeWord2 m,
      cellEnergyJet (Set.Icc a b) fast r (fun t X z => c m α t X z v u)) ≤
      ENNReal.ofReal ((2 ^ m : ℝ) * (fast + 1) * (2 ^ r *
        (M v u * lam ^ (n - m + r) + M v u * lam ^ (n - m + r)))) := by
  have hM := data.nonneg v u
  have hB : 0 ≤ 2 ^ r *
      (M v u * lam ^ (n - m + r) + M v u * lam ^ (n - m + r)) := by
    positivity
  calc
    _ ≤ ∑ _α : DerivativeWord2 m, ∑ _s ∈ Finset.range (fast + 1),
        ENNReal.ofReal (2 ^ r *
          (M v u * lam ^ (n - m + r) + M v u * lam ^ (n - m + r))) :=
      Finset.sum_le_sum fun α _ => data.cellEnergyJet_le hlam hm hr hfast α v u
    _ = ENNReal.ofReal ((2 ^ m : ℝ) * (fast + 1) * (2 ^ r *
        (M v u * lam ^ (n - m + r) + M v u * lam ^ (n - m + r)))) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => hB)]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => hB))]
      simp only [Finset.sum_const, Finset.card_range, card_derivativeWord2,
        nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
      congr 1
      ring

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Finite outer coordinate divergence sums normalized flux budgets without a component-count loss. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem normalizedSourceComponentZeroStep_mixed_bound
    (edge : ConstituentEdges D h) (η t lam : ℝ) (hlam : 0 ≤ lam)
    (Φ : Vec 2 → Vec 2 → ∀ i, h i) (δ p q : ℕ)
    (A : Vec 2 →L[ℝ] ℝ) (v : ι) (U : Fin 2 → ℝ)
    (hU : ∀ k, 0 ≤ U k)
    (hf : ∀ k, IsBoxSmooth p (q + 1) (sourceFluxComponentCoefficient edge η t Φ k 0 v))
    (X : Vec 2)
    (hbf : ∀ k, ∀ a ≤ p, ∀ b ≤ q + 1, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun y => (Real.exp ((lam • A) Y))⁻¹ •
          sourceFluxComponentCoefficient edge η t Φ k 0 v Y y) z) X‖ ≤
        U k * lam ^ (δ + a))
     (z : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => (Real.exp ((lam • A) Y))⁻¹ •
        sourceComponentCoefficientArray edge η t Φ 0 v Y y) z) X‖ ≤
      ∑ k : Fin 2, (2 ^ (p + 2 * q) * (max 1 ‖A‖) ^ p *
        (2 ^ (p + 2 * (q + 1)) * (max 1 ‖A‖) ^ p * U k)) *
        lam ^ (δ + p) := by
  let P := fun k i => sourceFluxComponentCoefficient edge η t Φ k i v
  let T := fun k Y y => (Real.exp ((lam • A) Y))⁻¹ • covariantCoefficientStep η k (P k) 0 Y y
  have hT : ∀ k, IsBoxSmooth p q (T k) := by
    intro k
    have hc := covariantCoefficientStep_box_reserve p q 0 η k (P k) (hf k)
      (fun hn => False.elim (hn rfl))
    have he := isBoxSmooth_slow_field p q (fun Y => Real.exp (-((lam • A) Y)))
      (Real.contDiff_exp.comp ((lam • A).contDiff.neg))
    simpa only [T, Real.exp_neg, ContinuousLinearMap.lsmul_apply] using!
      isBoxSmooth_bilinear he hc (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] h v →L[ℝ] h v)
  have he (Y y : Vec 2) : (Real.exp ((lam • A) Y))⁻¹ •
      sourceComponentCoefficientArray edge η t Φ 0 v Y y = ∑ k : Fin 2, T k Y y := by
    simp only [sourceComponentCoefficientArray, Finset.smul_sum, T, P]
  simp_rw [he]
  apply (norm_mixed_jet_finset_sum_le Finset.univ p q T (fun k _ => hT k) X z).trans
  apply Finset.sum_le_sum
  intro k _
  exact norm_mixed_covariantStep_zero_from_normalized_bounds_le η p q δ lam (U k)
    hlam (hU k) A k (P k) (hf k) X (hbf k) z

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! Actual cross tests are measurable after clamping to the given time window. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_ambient_first_cross_test_measurable
    (n p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hqs : 1 ≤ qs)
    (c : LiftCoeff ι h) (M : ι → ι → ℝ)
    (data : AmbientLiftCoefficientData par a b P.window lam n p q c M)
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) (l : h v →L[ℝ] ℝ) (X z : Vec 2) :
    Measurable (fun t => l ((Real.exp ((lam • A) X))⁻¹ • cellB1 Q.η Q.G Q.v
      (Set.projIcc a b P.window t)
      (liftApply n c (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ)
        (Set.projIcc a b P.window t)) X z v)) := by
  have hproj : Measurable (fun t : ℝ => (Set.projIcc a b P.window t : ℝ)) :=
    (continuous_projIcc (a := a) (b := b) (h := P.window)).measurable.subtype_val
  have hm := cellB1_parameter_measurable Q.η (fun t : ℝ => (Set.projIcc a b P.window t : ℝ)) Q.G Q.v
    (fun t => liftApply n c (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ)
      (Set.projIcc a b P.window t)) (data.raw_test_measurable A u ξ)
    (fun t => (data.raw_test_box A u ξ _ ((Set.projIcc a b P.window t).2)).mono hp hq)
    (fun Y i j => (P.G_meas Y i j).comp hproj)
    (by
      intro t i j
      exact (P.G_smooth _ (Set.projIcc a b P.window t).2 i j).of_le
        (by exact_mod_cast hqs))
    (fun y k => ((continuous_apply k).measurable.comp (P.v_meas y)).comp
      hproj) X z
  exact l.continuous.measurable.comp
    (((continuous_apply v).measurable.comp hm).const_smul _)

include P in
theorem setting_ambient_second_cross_test_measurable
    (n p q : ℕ) (hp : 2 ≤ p) (hqs : 1 ≤ qs)
    (c : LiftCoeff ι h) (M : ι → ι → ℝ)
    (data : AmbientLiftCoefficientData par a b P.window lam n p q c M)
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) (l : h v →L[ℝ] ℝ) (X z : Vec 2) :
    Measurable (fun t => l ((Real.exp ((lam • A) X))⁻¹ • cellB2 Q.η Q.G
      (Set.projIcc a b P.window t)
      (liftApply n c (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ)
        (Set.projIcc a b P.window t)) X z v)) := by
  have hproj : Measurable (fun t : ℝ => (Set.projIcc a b P.window t : ℝ)) :=
    (continuous_projIcc (a := a) (b := b) (h := P.window)).measurable.subtype_val
  have hm := cellB2_parameter_measurable Q.η (fun t : ℝ => (Set.projIcc a b P.window t : ℝ)) Q.G
    (fun t => liftApply n c (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ)
      (Set.projIcc a b P.window t)) (data.raw_test_measurable A u ξ)
    (fun t => (data.raw_test_box A u ξ _ ((Set.projIcc a b P.window t).2)).mono hp (Nat.zero_le q))
    (fun Y i j => (P.G_meas Y i j).comp hproj)
    (by
      intro t i j
      exact (P.G_smooth _ (Set.projIcc a b P.window t).2 i j).of_le
        (by exact_mod_cast hqs)) X z
  exact l.continuous.measurable.comp
    (((continuous_apply v).measurable.comp hm).const_smul _)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Finite outer coordinate divergence sums normalized flux budgets without a component-count loss. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem normalizedSourceComponentStep_mixed_bound
    (edge : ConstituentEdges D h) (η t lam : ℝ) (hη : η ≤ 1) (hlam : 0 ≤ lam)
    (Φ : Vec 2 → Vec 2 → ∀ i, h i) (δ p q j : ℕ) (hj : j ≠ 0)
    (A : Vec 2 →L[ℝ] ℝ) (v : ι) (U V : Fin 2 → ℝ)
    (hU : ∀ k, 0 ≤ U k) (hV : ∀ k, 0 ≤ V k)
    (hf : ∀ k, IsBoxSmooth p (q + 1) (sourceFluxComponentCoefficient edge η t Φ k j v))
    (hs : ∀ k, IsBoxSmooth (p + 1) q
      (sourceFluxComponentCoefficient edge η t Φ k (j - 1) v))
    (X : Vec 2)
    (hbf : ∀ k, ∀ a ≤ p, ∀ b ≤ q + 1, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun y => (Real.exp ((lam • A) Y))⁻¹ •
          sourceFluxComponentCoefficient edge η t Φ k j v Y y) z) X‖ ≤
        U k * lam ^ (δ + j + a))
    (hbs : ∀ k, ∀ a ≤ p + 1, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun y => (Real.exp ((lam • A) Y))⁻¹ •
          sourceFluxComponentCoefficient edge η t Φ k (j - 1) v Y y) z) X‖ ≤
        V k * lam ^ (δ + (j - 1) + a)) (z : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => (Real.exp ((lam • A) Y))⁻¹ •
        sourceComponentCoefficientArray edge η t Φ j v Y y) z) X‖ ≤
      ∑ k : Fin 2, (2 ^ (p + 2 * q) * (max 1 ‖A‖) ^ p *
        (2 ^ (p + 2 * (q + 1)) * (max 1 ‖A‖) ^ p * U k +
          2 ^ ((p + 1) + 2 * q) * (max 1 ‖A‖) ^ (p + 1) * V k)) *
        lam ^ (δ + j + p) := by
  let P := fun k i => sourceFluxComponentCoefficient edge η t Φ k i v
  let T := fun k Y y => (Real.exp ((lam • A) Y))⁻¹ • covariantCoefficientStep η k (P k) j Y y
  have hT : ∀ k, IsBoxSmooth p q (T k) := by
    intro k
    have hc := covariantCoefficientStep_box_reserve p q j η k (P k) (hf k) (fun _ => hs k)
    have he := isBoxSmooth_slow_field p q (fun Y => Real.exp (-((lam • A) Y)))
      (Real.contDiff_exp.comp ((lam • A).contDiff.neg))
    simpa only [T, Real.exp_neg, ContinuousLinearMap.lsmul_apply] using!
      isBoxSmooth_bilinear he hc (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] h v →L[ℝ] h v)
  have he (Y y : Vec 2) : (Real.exp ((lam • A) Y))⁻¹ •
      sourceComponentCoefficientArray edge η t Φ j v Y y = ∑ k : Fin 2, T k Y y := by
    simp only [sourceComponentCoefficientArray, Finset.smul_sum, T, P]
  simp_rw [he]
  apply (norm_mixed_jet_finset_sum_le Finset.univ p q T (fun k _ => hT k) X z).trans
  apply Finset.sum_le_sum
  intro k _
  exact norm_mixed_covariantStep_from_normalized_bounds_le η hη δ p q j hj lam (U k) (V k)
    hlam (hU k) (hV k) A k (P k) (hf k) (hs k) X (hbf k) (hbs k) z

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Paired second-cross jets retain one metric perturbation factor and the original two-degree gain. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem normalizedCellB2_paired_mixed_grading
    (p q δ r s : ℕ) (hr : r ≤ p) (hs : s ≤ q) (η lam M Md g Cf Cd : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hlam : 0 ≤ lam) (hM : 0 ≤ M) (hMd : 0 ≤ Md)
    (hg : 0 ≤ g) (hCf : 0 ≤ Cf) (hCd : 0 ≤ Cd)
    (A : Vec 2 →L[ℝ] ℝ) (G J : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ)
    (t : ℝ) (f fi : Vec 2 → Vec 2 → E)
    (hf : IsBoxSmooth (p + 2) q f) (hfi : IsBoxSmooth (p + 2) q fi)
    (hG : ∀ i j, IsBoxSmooth (p + 1) q (fun Y (_ : Vec 2) => G t Y i j))
    (hJ : ∀ i j, IsBoxSmooth (p + 1) q (fun Y (_ : Vec 2) => J t Y i j))
    (X : Vec 2)
    (hbG : ∀ i j, ∀ a ≤ p + 1, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (fun (_ : Vec 2) => G t Y i j) z) X‖ ≤ M * lam ^ a)
    (hbD : ∀ i j, ∀ a ≤ p + 1, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun (_ : Vec 2) => G t Y i j - J t Y i j) z) X‖ ≤ (Md * g) * lam ^ a)
    (hbfi : ∀ a ≤ p + 2, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (fi Y) z) X‖ ≤ Cf * lam ^ (δ + a))
    (hbdf : ∀ a ≤ p + 2, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (fun y => f Y y - fi Y y) z) X‖ ≤
        (Cd * g) * lam ^ (δ + a)) (z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (fun y =>
      (Real.exp ((lam • A) Y))⁻¹ • cellB2 η G t (fun Z w => Real.exp ((lam • A) Z) • f Z w) Y y -
      (Real.exp ((lam • A) Y))⁻¹ • cellB2 η J t (fun Z w => Real.exp ((lam • A) Z) • fi Z w) Y y) z) X‖ ≤
      (normalizedCellB2UniformConstant p q A M * Cd +
        normalizedCellB2UniformConstant p q A Md * Cf) * g * lam ^ ((δ + 2) + r) := by
  let df := fun Y y => f Y y - fi Y y
  let D := fun u Y i j => G u Y i j - J u Y i j
  let U := fun Y y => (Real.exp ((lam • A) Y))⁻¹ •
    cellB2 η G t (fun Z w => Real.exp ((lam • A) Z) • df Z w) Y y
  let T := fun Y y => (Real.exp ((lam • A) Y))⁻¹ •
    cellB2 η D t (fun Z w => Real.exp ((lam • A) Z) • fi Z w) Y y
  have hdf : IsBoxSmooth (p + 2) q df := hf.sub hfi
  have hD (i j : Fin 2) : IsBoxSmooth (p + 1) q (fun Y (_ : Vec 2) => D t Y i j) :=
    (hG i j).sub (hJ i j)
  have hΦdf : IsBoxSmooth (p + 2) q
      (fun Y y => Real.exp ((lam • A) Y) • df Y y) :=
    isBoxSmooth_bilinear (isBoxSmooth_slow_field _ _ _ (Real.contDiff_exp.comp (lam • A).contDiff)) hdf
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)
  have hΦfi : IsBoxSmooth (p + 2) q
      (fun Y y => Real.exp ((lam • A) Y) • fi Y y) :=
    isBoxSmooth_bilinear (isBoxSmooth_slow_field _ _ _ (Real.contDiff_exp.comp (lam • A).contDiff)) hfi
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)
  have hU : IsBoxSmooth p q U := exponential_normalization_box_reserve p q (lam • A) _
    (cellB2_box_reserve p q η G t _ hΦdf hG)
  have hT : IsBoxSmooth p q T := exponential_normalization_box_reserve p q (lam • A) _
    (cellB2_box_reserve p q η D t _ hΦfi hD)
  have he (Y y : Vec 2) :
      (Real.exp ((lam • A) Y))⁻¹ • cellB2 η G t (fun Z w => Real.exp ((lam • A) Z) • f Z w) Y y -
      (Real.exp ((lam • A) Y))⁻¹ • cellB2 η J t (fun Z w => Real.exp ((lam • A) Z) • fi Z w) Y y =
      U Y y + T Y y :=
    normalizedCellB2_paired_difference η (lam • A) G J t f fi
      (hf.mono (by omega) (by omega)) (hfi.mono (by omega) (by omega))
      (fun i j => (hG i j).mono (by omega) (Nat.zero_le _))
      (fun i j => (hJ i j).mono (by omega) (Nat.zero_le _)) Y y
  simp_rw [he]
  apply (norm_mixed_jet_add_le (hU.mono hr hs) (hT.mono hr hs) X z).trans
  have hu := normalizedCellB2_uniform_mixed_grading_at_slow_point p q δ η lam M
    (Cd * g) hη0 hη hlam hM (mul_nonneg hCd hg) A G t df hdf hG X hbG hbdf r s hr hs z
  have ht := normalizedCellB2_uniform_mixed_grading_at_slow_point p q δ η lam (Md * g)
    Cf hη0 hη hlam (mul_nonneg hMd hg) hCf A D t fi hfi hD X hbD hbfi r s hr hs z
  apply (add_le_add hu ht).trans_eq
  rw [normalizedCellB2UniformConstant_metric_mul]
  ring

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! The metric difference of a centered Fourier mode has a summable reciprocal-frequency majorant. -/

def metricDifferenceModeJetConstant (p q : ℕ) (M Md κ : ℝ) (S : ℕ → ℝ) : ℝ :=
  ((2 : ℝ) ^ q * ((2 : ℝ) ^ q * metricDifferenceKernelSourceConstant p q M Md κ S)) * (4 / κ)

theorem parameterizedModeResponse_metric_difference_jet_bound
    (p q : ℕ) (hq : q ≤ p) (g : ℝ → Vec 2 → ℝ)
    (hm : ∀ X, Measurable (fun t => g t X)) (hs : ∀ t, ContDiff ℝ (p : ℕ∞) (g t))
    (M Md eps lam κ a b : ℝ) (hM : 0 ≤ M) (hMd : 0 ≤ Md) (heps : 0 ≤ eps)
    (hlam : 0 ≤ lam) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hab : a ≤ b)
    (hb : ∀ j ≤ p, ∀ t X, ‖iteratedFDeriv ℝ j (g t) X‖ ≤ M * lam ^ j)
    (hdb : ∀ j ≤ p, ∀ t X, ‖iteratedFDeriv ℝ j (fun Y => g t Y - 1) X‖ ≤ Md * eps * lam ^ j)
    (hgl : ∀ t X, κ ≤ g t X)
    (U : ℤ → ℝ → Vec 2 → ℂ) (hUm : ∀ m X, Measurable (fun t => U m t X))
    (hUs : ∀ m t, ContDiff ℝ (p : ℕ∞) (U m t)) (S : ℕ → ℝ)
    (hS : ∀ j ≤ p, 0 ≤ S j) (hUb : ∀ j ≤ p, ∀ m t X, ‖iteratedFDeriv ℝ j (U m t) X‖ ≤ S j * lam ^ j)
    (m : ℤ) (X : Vec 2) :
    ‖iteratedFDeriv ℝ q (fun Y =>
      transverseModeResponse (‖profileFourierFrequency m‖ ^ 2) (fun t => g t Y) (fun t => U m t Y) a b -
        transverseModeResponse (‖profileFourierFrequency m‖ ^ 2) (fun _ => 1) (fun t => U m t Y) a b) X‖ ≤
      profileJetMajorant (metricDifferenceModeJetConstant p q M Md κ S * eps * lam ^ q) 0 m := by
  by_cases hm0 : m = 0
  · subst m
    have he : (fun Y =>
        transverseModeResponse (‖profileFourierFrequency 0‖ ^ 2) (fun t => g t Y) (fun t => U 0 t Y) a b -
          transverseModeResponse (‖profileFourierFrequency 0‖ ^ 2) (fun _ => 1) (fun t => U 0 t Y) a b) = 0 := by
      funext Y
      simp [profileFourierFrequency, transverseModeResponse, transverseModeKernel]
    rw [he]
    simp [profileJetMajorant]
  · have hr : 0 < ‖profileFourierFrequency m‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr (profileFourierFrequency_ne_zero m hm0))
    have hh := transverseModeResponse_metric_difference_jet_bound p q hq g hm hs M Md eps lam
      (‖profileFourierFrequency m‖ ^ 2) κ a b hM hMd heps hlam hr hκ hκ1 hab hb hdb hgl
      (U m) (hUm m) (hUs m) S hS (fun j hj t Y => hUb j hj m t Y) X
    apply hh.trans_eq
    simp only [profileJetMajorant, ite_eq_right hm0, metricDifferenceModeJetConstant,
      profileFourierFrequency_norm_sq]
    field_simp

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Operator-valued mixed jets supply uniform scalar-dual Fourier decay. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem complex_dual_profile_fourier_parameter_data (p q r L : ℕ)
    (hr : r ≤ p) (hL : L + 2 ≤ q)
    (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth p q f)
    (line : ℝ →L[ℝ] Vec 2) (hline : ‖line‖ = 1)
    (l : E →L[ℝ] ℝ) (hper : ∀ X,
      Function.Periodic (fun z => ((l (f X (line z)) : ℝ) : ℂ)) 1)
    (C : ℕ → ℝ) (hb : ∀ a ≤ p, ∀ b ≤ q, ∀ X z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (f Y) z) X‖ ≤ C a)
    (m : ℤ) :
    ContDiff ℝ (p : ℕ∞)
      (fun X => unitProfileFourierCoeff (fun z => ((l (f X (line z)) : ℝ) : ℂ)) m) ∧
    (m ≠ 0 → ∀ X, (1 + |(m : ℝ)|) ^ L *
      ‖iteratedFDeriv ℝ r
        (fun Y => unitProfileFourierCoeff (fun z => ((l (f Y (line z)) : ℝ) : ℂ)) m) X‖ ≤
      profileJetMajorant (2 ^ r * (‖l‖ * C r)) 0 m) := by
  let F := fun X z => ((l (f X (line z)) : ℝ) : ℂ)
  have hbox := hf.clm_comp (Complex.ofRealCLM.comp l)
  have hs (j : ℕ) (hj : j ≤ q) (z : ℝ) :
      ContDiff ℝ (p : ℕ∞) (fun X => iteratedDeriv j (F X) z) :=
    linear_profile_iteratedDeriv_parameter_contDiff p q j hj _ hbox line z
  have hbound (j : ℕ) (hj : j ≤ q) (a : ℕ) (ha : a ≤ p) (z : ℝ) (X : Vec 2) :
      ‖iteratedFDeriv ℝ a (fun Y => iteratedDeriv j (F Y) z) X‖ ≤ ‖l‖ * C a := by
    have h := norm_mixed_complexified_linear_profile_le p q a j ha hj f hf line l X z
    simp only [hline, one_pow, mul_one] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hb a ha j hj X (line z)) (norm_nonneg l))
  have hF : ContDiff ℝ (p : ℕ∞) (fun X => unitProfileFourierCoeff (F X) m) :=
    unitProfileFourierCoeff_parameter_contDiff p F
      (fun X => ((Complex.ofRealCLM.comp l).continuous.comp ((hf.1 X).continuous.comp
        line.continuous)).measurable)
      (fun z => by simpa only [iteratedDeriv_zero] using hs 0 (Nat.zero_le q) z)
      (fun a => ‖l‖ * C a)
      (fun a ha z X => by simpa only [iteratedDeriv_zero] using hbound 0 (Nat.zero_le q) a ha z X) m
  refine ⟨hF, ?_⟩
  intro hm X
  have hw := nonzero_weightedProfileFourierCoeff_parameter_data p r (L + 2) hr F
    (fun X => ((Complex.ofRealCLM.comp l).contDiff.comp ((hf.1 X).comp line.contDiff)).of_le
      (by exact_mod_cast hL)) hper (hs (L + 2) hL)
    (fun a => ‖l‖ * C a) (hbound (L + 2) hL) m hm
  exact profile_fourier_jet_wiener_majorant p r L hr _ hF m hm X _ (hw.2 X)

end AVRegularity.CycleComparison.Lift
end
