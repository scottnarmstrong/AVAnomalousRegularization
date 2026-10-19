-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Definitions.IsWindowTestFunction
public import AVenhance.Statements.Roots.IsPeriodicH1With
public import AVenhance.Statements.Roots.L2NormSq
public import AVenhance.Statements.Roots.SpaceGrad

/-! Weak (energy-class) solutions of `∂ₜθ + b·∇θ − κΔθ = 0` on `[t₁, t₂] × 𝕋²` with `θ(t₁) = f`: the
weak solutions of the initial-value problems (2.2) of Theorem A and (3.1) of the paper. The
time-window analogue of `AVenhance.IsWeakSolutionGrad`. -/

@[expose] public section

open MeasureTheory Homogenization AVenhance

namespace AVRegularity

/-- `θ ∈ L^∞_t L²_x ∩ L²_t H¹_x` on `[t₁, t₂] × 𝕋²` with gradient `Dθ`, weakly continuous
in time on the closed window, solving the equation against every window test function, with
initial datum `f` at `t₁`. The drift term is required integrable, so no integral in the weak
form takes the Bochner junk value. -/
def IsWeakSolutionOn (b : ℝ → Vec 2 → Vec 2) (κ t₁ t₂ : ℝ) (f : Vec 2 → ℝ)
    (θ : ℝ → Vec 2 → ℝ) : Prop :=
  ∃ Dθ : ℝ → Vec 2 → Vec 2,
    (∀ t ∈ Set.Icc t₁ t₂, IsZ2Periodic (θ t) ∧ MemL2On unitCube (θ t)) ∧
    (∃ C : ℝ, ∀ t ∈ Set.Icc t₁ t₂, l2NormSq (θ t) ≤ C) ∧
    MemLp (fun p : ℝ × Vec 2 => θ p.1 p.2) 2
      (volume.restrict (Set.Ioo t₁ t₂ ×ˢ unitCube)) ∧
    (∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => Dθ p.1 p.2 i) 2
      (volume.restrict (Set.Ioo t₁ t₂ ×ˢ unitCube))) ∧
    (∀ᵐ t ∂(volume.restrict (Set.Ioo t₁ t₂)), IsPeriodicH1With (θ t) (Dθ t)) ∧
    Integrable (fun p : ℝ × Vec 2 => vecDot (b p.1 p.2) (Dθ p.1 p.2))
      (volume.restrict (Set.Ioo t₁ t₂ ×ˢ unitCube)) ∧
    (∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → IsZ2Periodic ψ →
      ContinuousOn (fun t => ∫ x in unitCube, θ t x * ψ x) (Set.Icc t₁ t₂)) ∧
    (∀ φ : ℝ → Vec 2 → ℝ, IsWindowTestFunction t₂ φ →
      ∫ p in Set.Ioo t₁ t₂ ×ˢ unitCube,
        (-(θ p.1 p.2) * deriv (fun s => φ s p.2) p.1
          + vecDot (b p.1 p.2) (Dθ p.1 p.2) * φ p.1 p.2
          + κ * vecDot (Dθ p.1 p.2) (spaceGrad (φ p.1) p.2))
        = ∫ x in unitCube, f x * φ t₁ x)

end AVRegularity
