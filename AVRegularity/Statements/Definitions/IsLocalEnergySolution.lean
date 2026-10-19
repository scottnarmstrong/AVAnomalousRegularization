-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Definitions.OuterPipe
public import Homogenization.Sobolev.H1.Definitions
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-! Local energy solutions in a material pipe.
-/

@[expose] public section

open MeasureTheory Homogenization

namespace AVRegularity

/-- `θ` is a local energy solution of `∂ₜθ + b·∇θ - κΔθ = 0` in `𝒫_out`: it is square
integrable there and satisfies the equation distributionally against smooth tests compactly
supported in `𝒫_out` (with `b·∇θ = div(bθ)` for divergence-free `b`), and its pullback
`U(t,y) = θ(t, F_t(y))` lies in `L^∞_t L²(B_R) ∩ L²_t H¹(B_R)` on `(t₁ - 8T, t₁)`, with weak
gradient `DU`. No lateral data are prescribed. -/
def IsLocalEnergySolution (b : ℝ → Vec 2 → Vec 2) (κ : ℝ) (F : ℝ → Vec 2 → Vec 2)
    (t₁ T R : ℝ) (θ : ℝ → Vec 2 → ℝ) : Prop :=
  MemLp (fun p : ℝ × Vec 2 => θ p.1 p.2) 2 (volume.restrict (outerPipe F t₁ T R)) ∧
  (∀ φ : ℝ × Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    tsupport φ ⊆ outerPipe F t₁ T R →
    ∫ p in outerPipe F t₁ T R, θ p.1 p.2 *
      (fderiv ℝ φ p (1, 0) + ∑ i : Fin 2, b p.1 p.2 i * fderiv ℝ φ p (0, basisVec i)
        + κ * ∑ i : Fin 2,
          fderiv ℝ (fun p' => fderiv ℝ φ p' (0, basisVec i)) p (0, basisVec i)) = 0) ∧
  ∃ DU : ℝ → Vec 2 → Vec 2,
    (∃ C : ℝ, ∀ᵐ t ∂(volume.restrict (Set.Ioo (t₁ - 8 * T) t₁)),
      MemL2On (euclidBall 0 R) (fun y => θ t (F t y)) ∧
      ∫ y in euclidBall 0 R, θ t (F t y) ^ 2 ≤ C) ∧
    (∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => DU p.1 p.2 i) 2
      (volume.restrict (Set.Ioo (t₁ - 8 * T) t₁ ×ˢ euclidBall 0 R))) ∧
    (∀ᵐ t ∂(volume.restrict (Set.Ioo (t₁ - 8 * T) t₁)),
      HasWeakGradientOn (euclidBall 0 R) (fun y => θ t (F t y)) (DU t))

end AVRegularity
