-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleEvolution.CellCoefficients
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The integrated duality identity of the cell/fibre equation on `𝕋²` between two times. The
pairing is the bilinear complex pairing `∫ u ψ`, tested against every complex `H¹` function, so
the identity is the holomorphic continuation in `θ` of the real-`ξ` weak form. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization

namespace AVRegularity

/-- For coefficients `C`, times `s ≤ t`, values `u₀ = u(s)`, `u₁ = u(t)`, a test `ψ` with
gradient `dψ`, a trajectory `u` with gradient `du`, a scalar source `src` and a vector source `F`:
`∫u(t)ψ - ∫u(s)ψ = ∫_{(s,t]} ∫ rhs`, where
`rhs = -(G D_θ u)·(D_{-θ}ψ) - (v·D_θ u)ψ + κ u ψ + src ψ - F·D_{-θ}ψ`
and `D_θ u = ∇u + iθu`, `D_{-θ}ψ = ∇ψ - iθψ`; this is the weak form of
`∂ₜu = D_θ·(G D_θ u) - v·D_θ u + κ u + src + D_θ·F` (the adjoint of `D_θ` under the bilinear
pairing is `-D_{-θ}`). All integrals are required integrable (per-time integrability of `rhs τ`
for almost every `τ ∈ (s,t]`), so no Bochner junk value occurs. -/
def CellWeakIdentity (C : CellCoefficients) (s t : ℝ) (u₀ u₁ ψ : Vec 2 → ℂ)
    (dψ : Fin 2 → Vec 2 → ℂ) (u : ℝ → Vec 2 → ℂ) (du : ℝ → Fin 2 → Vec 2 → ℂ)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) : Prop :=
  let μ := volume.restrict AVenhance.unitCube
  let rhs : ℝ → Vec 2 → ℂ := fun τ x =>
    -(∑ j : Fin 2, ∑ k : Fin 2, (C.G τ x j k : ℂ) *
        (du τ j x + Complex.I * C.θ j * u τ x) * (dψ k x - Complex.I * C.θ k * ψ x))
      - ∑ k : Fin 2, (C.v τ x k : ℂ) * (du τ k x + Complex.I * C.θ k * u τ x) * ψ x
      + C.κ τ * u τ x * ψ x + src τ x * ψ x
      - ∑ k : Fin 2, F τ x k * (dψ k x - Complex.I * C.θ k * ψ x)
  Integrable (fun x => u₁ x * ψ x) μ ∧
  Integrable (fun x => u₀ x * ψ x) μ ∧
  (∀ᵐ τ ∂(volume.restrict (Set.Ioc s t)), Integrable (rhs τ) μ) ∧
  IntegrableOn (fun τ => ∫ x, rhs τ x ∂μ) (Set.Ioc s t) ∧
  ∫ x, u₁ x * ψ x ∂μ - ∫ x, u₀ x * ψ x ∂μ = ∫ τ in Set.Ioc s t, ∫ x, rhs τ x ∂μ

end AVRegularity
