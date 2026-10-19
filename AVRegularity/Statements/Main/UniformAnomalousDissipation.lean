-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.Main.UniformAnomalousDissipation
public import AVRegularity.Statements.Definitions.IsHolderDivFreeVelocity
public import AVRegularity.Statements.Definitions.IsWeakSolutionOn
public import AVRegularity.Statements.Definitions.IsWeakSolutionOnGrad

/-! Theorem B of the paper (uniform anomalous dissipation), in existential form, as
`interior_regularity` is for Theorem A. -/

@[expose] public section

open MeasureTheory Homogenization AVenhance

namespace AVRegularity

/-- **Theorem B (uniform anomalous dissipation).** For `0 < α < 1/3` there are a bounded,
periodic, divergence-free velocity `b ∈ C^α(ℝ × 𝕋²)`, disjoint diffusivity bands
`𝒦 = ⋃_M [κ_M/2, 2κ_M]`, `κ_M ↓ 0`, and `c > 0` such that for all `a ∈ ℝ`, `κ ∈ 𝒦` and
`f ∈ L²(𝕋²)`, with `(f) = ∫_{𝕋²} f`:
(i) a weak solution `θ` on `[a, a+1]` with `θ(a) = f` exists, and every such solution, with
gradient `Dθ`, has `κ ∫_a^{a+1} ∫_{𝕋²} |Dθ|² ≥ c ‖f - (f)‖₂²`;
(ii) for every `t > a`, a weak solution `θ` on `[a, t]` with `θ(a) = f` exists, and every such
solution has `‖θ(t) - (f)‖₂² ≤ 4 e^{-2c(t-a)} ‖f - (f)‖₂²`. -/
theorem uniform_anomalous_dissipation (α : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) :
    ∃ b : ℝ → Vec 2 → Vec 2, IsHolderDivFreeVelocity α b ∧
    ∃ κc : ℕ → ℝ, (∀ M, 0 < κc M) ∧ (∀ M, 4 * κc (M + 1) < κc M) ∧
    ∃ c : ℝ, 0 < c ∧
      (∀ a : ℝ, ∀ κ ∈ ⋃ M : ℕ, Set.Icc (κc M / 2) (2 * κc M), ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
        (∃ θ : ℝ → Vec 2 → ℝ, ∃ Dθ : ℝ → Vec 2 → Vec 2,
          IsWeakSolutionOnGrad b κ a (a + 1) f θ Dθ) ∧
        ∀ θ : ℝ → Vec 2 → ℝ, ∀ Dθ : ℝ → Vec 2 → Vec 2,
          IsWeakSolutionOnGrad b κ a (a + 1) f θ Dθ →
            c * l2NormSq (fun x => f x - ∫ y in unitCube, f y) ≤
              κ * ∫ p in Set.Ioo a (a + 1) ×ˢ unitCube, vecNormSq (Dθ p.1 p.2)) ∧
      (∀ a : ℝ, ∀ κ ∈ ⋃ M : ℕ, Set.Icc (κc M / 2) (2 * κc M), ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
        ∀ t : ℝ, a < t →
        (∃ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a t f θ) ∧
        ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a t f θ →
          l2NormSq (fun x => θ t x - ∫ y in unitCube, f y) ≤
            4 * Real.exp (-2 * c * (t - a)) *
              l2NormSq (fun x => f x - ∫ y in unitCube, f y)) :=
  by exact AVRegularity.Providers.uniform_anomalous_dissipation α hα₀ hα₁

end AVRegularity
