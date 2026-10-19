-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Homogenization.Sobolev.WeakDerivatives

/-! The Jacobian matrix of a planar map, `(Df)_{ij} = ∂_j f_i`. -/

@[expose] public section

open Homogenization

namespace AVRegularity

/-- `(Df(y))_{ij} = ∂_j f_i(y)`. -/
noncomputable def jacMatrix (f : Vec 2 → Vec 2) (y : Vec 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => fderiv ℝ f y (basisVec j) i

end AVRegularity
