-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev.Basic
public import Mathlib.Order.CompletePartialOrder

/-! Literal finite classical coefficient derivatives and their operator-array norms. -/

@[expose] public noncomputable section

open Homogenization

namespace AVRegularity.Sobolev

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Ordered coordinate differentiation, applying directions in the order of the word. -/
def orderedCoefficientDerivative (C : Vec 2 → E →L[ℝ] F) :
    (j : ℕ) → DerivativeWord2 j → Vec 2 → E →L[ℝ] F
  | 0, _ => C
  | j + 1, w => fun x =>
      fderiv ℝ (orderedCoefficientDerivative C j (Fin.init w)) x (basisVec (w (Fin.last j)))

/-- The empty word is the coefficient itself. -/
@[simp] theorem orderedCoefficientDerivative_zero (C : Vec 2 → E →L[ℝ] F)
    (w : DerivativeWord2 0) : orderedCoefficientDerivative C 0 w = C := rfl

/-- Appending a direction takes exactly that coordinate derivative. -/
@[simp] theorem orderedCoefficientDerivative_snoc (C : Vec 2 → E →L[ℝ] F)
    {j : ℕ} (w : DerivativeWord2 j) (i : Fin 2) :
    orderedCoefficientDerivative C (j + 1) (Fin.snoc w i) =
      fun x => fderiv ℝ (orderedCoefficientDerivative C j w) x (basisVec i) := by
  simp only [orderedCoefficientDerivative, Fin.init_snoc, Fin.snoc_last]

/-- An order-`j` derivative of a `C^(j+m)` coefficient is `C^m`. -/
theorem orderedCoefficientDerivative_contDiff (C : Vec 2 → E →L[ℝ] F) (j m : ℕ)
    (hC : ContDiff ℝ (j + m : ℕ) C) (w : DerivativeWord2 j) :
    ContDiff ℝ (m : ℕ) (orderedCoefficientDerivative C j w) := by
  induction j generalizing m with
  | zero => simpa only [Nat.zero_add, orderedCoefficientDerivative] using hC
  | succ j ih =>
    have hCm : ContDiff ℝ (j + (m + 1) : ℕ) C := by
      simpa only [Nat.succ_add, Nat.add_succ] using hC
    have hj := ih (m + 1) hCm (Fin.init w)
    exact (hj.fderiv_right (m := (m : ℕ)) (by simp)).clm_apply contDiff_const

/-- The source coefficient tensor as an operator into the Hilbert word array. -/
def coefficientDerivativeArray (C : Vec 2 → E →L[ℝ] F) (j : ℕ) (x : Vec 2) :
    E →L[ℝ] PiLp 2 (fun _ : DerivativeWord2 j => F) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : DerivativeWord2 j => F)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun w => orderedCoefficientDerivative C j w x))

/-- The array has precisely the ordered coefficient components. -/
@[simp] theorem coefficientDerivativeArray_apply (C : Vec 2 → E →L[ℝ] F)
    (j : ℕ) (x : Vec 2) (z : E) (w : DerivativeWord2 j) :
    coefficientDerivativeArray C j x z w = orderedCoefficientDerivative C j w x z := rfl

/-- The value-array norm is exactly the Euclidean tensor norm used in the source. -/
theorem coefficientDerivativeArray_normSq (C : Vec 2 → E →L[ℝ] F)
    (j : ℕ) (x : Vec 2) (z : E) :
    ‖coefficientDerivativeArray C j x z‖ ^ 2 =
      ∑ w : DerivativeWord2 j, ‖orderedCoefficientDerivative C j w x z‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 _ _

end AVRegularity.Sobolev
