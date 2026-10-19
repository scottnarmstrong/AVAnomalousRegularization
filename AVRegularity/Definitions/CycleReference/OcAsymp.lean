-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVenhance.Statements.Roots.SpaceGrad
public import Homogenization.Sobolev.H1.Definitions

@[expose] public section

section
open MeasureTheory Filter Topology Homogenization AVenhance
namespace AVRegularity

/-! Energy solutions on the plane of the linear parabolic equation
`∂ₜθ + b·∇θ - div(A∇θ) = div q + f` with continuous `L²` trace. Covers both
`∂ₜθ + 𝐛ₘ·∇θ - νΔθ = div q + f` (`A = νI`) and the pulled-back material equation
(`b = 0`, `A = νG + ψσ`, non-symmetric). -/

/-- `θ ∈ C([t₀,t₁];L²(ℝ²)) ∩ L²(t₀,t₁;H¹(ℝ²))` with gradient `Dθ`, trace `θ(t₀) = θ₀`, solving
`∂ₜθ + b·∇θ - div(A∇θ) = div q + f` on `(t₀,t₁) × ℝ²` in the weak sense against every smooth,
compactly supported space-time test function vanishing for `t ≥ t₁`:
`∬ [-θ ∂ₜφ + (b·Dθ) φ + (A Dθ)·∇φ + q·∇φ - f φ] = ∫ θ₀ φ(t₀)`. The tested integrand is required
integrable, so no integral takes the Bochner junk value. -/
def IsPlaneEnergySolution (b : ℝ → Vec 2 → Vec 2)
    (A : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (t₀ t₁ : ℝ) (q : ℝ → Vec 2 → Vec 2)
    (f : ℝ → Vec 2 → ℝ) (θ₀ : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ) : Prop :=
  ∃ Dθ : ℝ → Vec 2 → Vec 2,
    (∀ t ∈ Set.Icc t₀ t₁, MemL2On Set.univ (θ t)) ∧
    (∀ t ∈ Set.Icc t₀ t₁,
      Tendsto (fun s => eLpNorm (fun x => θ s x - θ t x) 2 volume)
        (𝓝[Set.Icc t₀ t₁] t) (𝓝 0)) ∧
    θ t₀ =ᵐ[volume] θ₀ ∧
    (∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => Dθ p.1 p.2 i) 2
      (volume.restrict (Set.Ioo t₀ t₁ ×ˢ Set.univ))) ∧
    (∀ᵐ t ∂(volume.restrict (Set.Ioo t₀ t₁)), HasWeakGradientOn Set.univ (θ t) (Dθ t)) ∧
    ∀ φ : ℝ → Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => φ p.1 p.2) →
      HasCompactSupport (fun p : ℝ × Vec 2 => φ p.1 p.2) → (∀ t, t₁ ≤ t → ∀ x, φ t x = 0) →
      Integrable
        (fun p : ℝ × Vec 2 =>
          -(θ p.1 p.2) * deriv (fun s => φ s p.2) p.1
            + vecDot (b p.1 p.2) (Dθ p.1 p.2) * φ p.1 p.2
            + vecDot ((A p.1 p.2).mulVec (Dθ p.1 p.2)) (spaceGrad (φ p.1) p.2)
            + vecDot (q p.1 p.2) (spaceGrad (φ p.1) p.2) - f p.1 p.2 * φ p.1 p.2)
        (volume.restrict (Set.Ioo t₀ t₁ ×ˢ Set.univ)) ∧
      ∫ p in Set.Ioo t₀ t₁ ×ˢ Set.univ,
          (-(θ p.1 p.2) * deriv (fun s => φ s p.2) p.1
            + vecDot (b p.1 p.2) (Dθ p.1 p.2) * φ p.1 p.2
            + vecDot ((A p.1 p.2).mulVec (Dθ p.1 p.2)) (spaceGrad (φ p.1) p.2)
            + vecDot (q p.1 p.2) (spaceGrad (φ p.1) p.2) - f p.1 p.2 * φ p.1 p.2)
        = ∫ x, θ₀ x * φ t₀ x

end AVRegularity
end

section
namespace AVRegularity

/-! Two-sided comparability `x ≍ y` with an explicit constant. -/

/-- `x ≍ y` with constant `C`: `C⁻¹ y ≤ x ≤ C y`. -/
def ocAsymp (C x y : ℝ) : Prop := C⁻¹ * y ≤ x ∧ x ≤ C * y

end AVRegularity
end
