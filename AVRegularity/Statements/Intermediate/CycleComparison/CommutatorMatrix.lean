-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Homogenization.Sobolev.WeakDerivatives
public import Mathlib.Data.Matrix.Basic

/-! The commutator coefficient `𝔑 = D𝐛 H_cov + H_cov D𝐛ᵀ`, so that
`𝒥_H f = -𝔑 ∇f = -(D𝐛 H_cov + H_cov D𝐛ᵀ)∇f`, with `(D𝐛)_{ij} = ∂_j 𝐛_i`. -/

@[expose] public noncomputable section

open Homogenization

namespace AVRegularity

/-- `𝔑(t,x)_{ij} = ∑_k (∂_k 𝐛_i H_{kj} + H_{ik} ∂_k 𝐛_j)` at time `t`, position `x`. -/
def commutatorMatrix (b : ℝ → Vec 2 → Vec 2) (Hc : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ)
    (x : Vec 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => ∑ k : Fin 2,
    (fderiv ℝ (b t) x (basisVec k) i * Hc k j + Hc i k * fderiv ℝ (b t) x (basisVec k) j)

end AVRegularity
