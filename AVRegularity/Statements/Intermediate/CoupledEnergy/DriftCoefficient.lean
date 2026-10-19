-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev.Multiply.Coefficient

/-! The drift `v` as a coefficient between finite Euclidean spaces, `z ↦ v(x)·z` on `ℝ²`. The
transport term `v·∇u_i` is the coefficient `v(x)·` applied to the gradient slot of `∇u_i` (the
operator `𝗁⊗ℝ² → 𝗁`, `z⊗e ↦ (v·e) z`, has the same operator norm and derivative array as `ℝ² → ℝ`).
`ℝ²` carries its Euclidean norm (`PiLp 2`), so
`‖coefficientDerivativeArray (driftCoefficient v) l x‖` is the paper's operator norm `‖∇^l v(x)‖`:
sup over unit `z` of the Euclidean array `(∂^w v(x) · z)_w`. -/

@[expose] public noncomputable section

open Homogenization

namespace AVRegularity

/-- The velocity field as a coefficient `ℝ² → ℝ`, `z ↦ ∑_k v(x)_k z_k`, `ℝ²` Euclidean. -/
def driftCoefficient (b : Vec 2 → Vec 2) :
    Vec 2 → (PiLp 2 (fun _ : Fin 2 => ℝ)) →L[ℝ] ℝ :=
  fun x => ∑ k : Fin 2, (b x k) • PiLp.proj 2 (fun _ : Fin 2 => ℝ) k

end AVRegularity
