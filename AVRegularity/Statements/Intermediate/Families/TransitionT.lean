-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev.Basic
public import Homogenization.Sobolev.WeakDerivatives
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-! The order-lowering recursion `T_{I,A}` of a chart transition. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

/-- The recursion: `T_{∅,∅} = 1`, `T_{∅,A} = 0` for `A ≠ ∅`, and
`T_{(i,I),A} = ∑_b K_{bi} ∂'_b T_{I,A} + [A = (a,A₀)] K_{ai} T_{I,A₀}`. -/
def transitionT (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) :
    List (Fin 2) → List (Fin 2) → Vec 2 → ℝ
  | [], [] => fun _ => 1
  | [], _ :: _ => fun _ => 0
  | i :: I, A => fun y =>
      (∑ b : Fin 2, K y b i * fderiv ℝ (transitionT K I A) y (basisVec b)) +
        match A with
        | [] => 0
        | a :: A₀ => K y a i * transitionT K I A₀ y

end AVRegularity
