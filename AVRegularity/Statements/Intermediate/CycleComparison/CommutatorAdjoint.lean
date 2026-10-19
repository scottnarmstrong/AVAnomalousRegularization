-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleComparison.CommutatorMatrix
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The formal adjoint on smooth periodic vector test fields of the
commutator flux `𝒥_H f = -𝔑 ∇f`: from
`∫ ⟨𝒥_H f, ψ⟩ = -∑_{k,j} ∫ ⟨𝔑_{kj} ∂_j f, ψ_k⟩`, `𝒥_H^* ψ = ∑_j ∂_j(∑_k 𝔑_{kj} ψ_k)`. -/

@[expose] public noncomputable section

open Homogenization

namespace AVRegularity

/-- `𝒥_H^* ψ (x) = ∑_j ∂_j (∑_k 𝔑(t,·)_{kj} ψ_k) (x)`. -/
def commutatorAdjoint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : ℝ → Vec 2 → Vec 2) (Hc : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ)
    (ψ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) : Vec 2 → E :=
  fun x => ∑ j : Fin 2,
    fderiv ℝ (fun y => ∑ k : Fin 2, (commutatorMatrix b Hc t y k j) • ψ y k) x (basisVec j)

end AVRegularity
