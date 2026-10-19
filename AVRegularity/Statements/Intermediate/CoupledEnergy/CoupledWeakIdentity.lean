-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The integrated `L²`-duality identity for one component of the coupled system, tested against one
`H¹` test at one time: the tested form of display (7.3) of the paper. It is written on raw
representatives so that the same statement serves `Ω = 𝕋²` (`μ` = Lebesgue measure on the unit cell)
and `Ω = ℝ²` (`μ` = Lebesgue measure). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization

namespace AVRegularity

/-- For a component with values in `H`, `ν > 0`, initial time `t₀`, time `t`, drift `v`:
`⟨u(t),φ⟩ − ⟨f,φ⟩ = ∫_{(t₀,t]} [ −⟨v·∇u,φ⟩ − ν⟨∇u,∇φ⟩ − ⟨flux + F, ∇φ⟩ + ⟨g,φ⟩ ] ds`,
where `u₀` represents `u(t)`, `du s k` represents `∂ₖ u(s)`, `flux s` represents
`∑_{i',d} A_{ii',d} ∇^{d-1}u_{i'}(s)`, `F s`, `g s` represent the forcing at time `s`, and
`φ`, `dφ k` represent the test and its gradient. Every integral that occurs is required to be
integrable (the inner integrand for each `s ∈ (t₀,t]`, the outer time integrand, and both
left-hand pairings), so no integral takes the Bochner junk value. -/
def CoupledWeakIdentity {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (μ : Measure (Vec 2)) (ν t₀ t : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (u₀ f φ : Vec 2 → H) (dφ : Fin 2 → Vec 2 → H)
    (du : ℝ → Fin 2 → Vec 2 → H)
    (flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)) (g : ℝ → Vec 2 → H) : Prop :=
  let rhs : ℝ → Vec 2 → ℝ := fun s x =>
    -(∑ k : Fin 2, v s x k * inner ℝ (du s k x) (φ x))
      - ν * ∑ k : Fin 2, inner ℝ (du s k x) (dφ k x)
      - ∑ k : Fin 2, inner ℝ (flux s x k + F s x k) (dφ k x)
      + inner ℝ (g s x) (φ x)
  Integrable (fun x => inner ℝ (u₀ x) (φ x)) μ ∧
  Integrable (fun x => inner ℝ (f x) (φ x)) μ ∧
  (∀ s ∈ Set.Ioc t₀ t, Integrable (rhs s) μ) ∧
  IntegrableOn (fun s => ∫ x, rhs s x ∂μ) (Set.Ioc t₀ t) ∧
  ∫ x, inner ℝ (u₀ x) (φ x) ∂μ - ∫ x, inner ℝ (f x) (φ x) ∂μ
    = ∫ s in Set.Ioc t₀ t, ∫ x, rhs s x ∂μ

end AVRegularity
