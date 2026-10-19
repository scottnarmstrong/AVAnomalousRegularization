-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Homogenization.Sobolev.WeakDerivatives
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-! The constant-coefficient second-order covariance operator `𝒞 = H_cov : D²` on a classical field.
It is applied below to smooth periodic test fields; on Sobolev fields it is defined by duality
against these. For a symmetric constant matrix it is formally self-adjoint. -/

@[expose] public noncomputable section

open Homogenization

namespace AVRegularity

/-- `(𝒞 φ)(x) = ∑_{i,j} H_{ij} ∂_i ∂_j φ(x)` (derivatives by `fderiv`; meaningful for `C²`
`φ`, which is the only use). -/
def covOperator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) (φ : Vec 2 → E) : Vec 2 → E :=
  fun x => ∑ i : Fin 2, ∑ j : Fin 2,
    Hc i j • fderiv ℝ (fun y => fderiv ℝ φ y (basisVec j)) x (basisVec i)

end AVRegularity
