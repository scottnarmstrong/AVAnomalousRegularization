-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.Main.InteriorRegularityAndDissipation
public import AVRegularity.Statements.Definitions.CsNormLe
public import AVRegularity.Statements.Definitions.IsHolderDivFreeVelocity
public import AVRegularity.Statements.Definitions.IsWeakSolutionOn
public import AVRegularity.Statements.Definitions.IsWeakSolutionOnGrad

/-! Theorems A and B of the paper for the same velocity field and bands, in existential
form. -/

@[expose] public section

open MeasureTheory Homogenization AVenhance

namespace AVRegularity

/-- **Theorems A and B of the paper for one velocity field.** For `0 < α < 1/3` and
`0 < s < (1-α)/2` there are a bounded, periodic, divergence-free velocity `b ∈ C^α(ℝ × 𝕋²)` and
disjoint diffusivity bands `𝒦 = ⋃_M [κ_M/2, 2κ_M]`, `κ_M ↓ 0`, such that the conclusions of
Theorem A (`interior_regularity`) and of Theorem B (`uniform_anomalous_dissipation`) hold for
this `b` and `𝒦`. -/
theorem interior_regularity_and_dissipation (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) :
    ∃ b : ℝ → Vec 2 → Vec 2, IsHolderDivFreeVelocity α b ∧
    ∃ κc : ℕ → ℝ, (∀ M, 0 < κc M) ∧ (∀ M, 4 * κc (M + 1) < κc M) ∧
    (∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∃ C : ℝ,
      ∀ a : ℝ, ∀ κ ∈ ⋃ M : ℕ, Set.Icc (κc M / 2) (2 * κc M),
      ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
        (∃ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a (a + T) f θ) ∧
        ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a (a + T) f θ →
          ∃ Θ : ℝ → Vec 2 → ℝ,
            ContinuousOn (fun p : ℝ × Vec 2 => Θ p.1 p.2)
              (Set.Icc (a + t₀) (a + T) ×ˢ Set.univ) ∧
            ∀ t ∈ Set.Icc (a + t₀) (a + T),
              IsZ2Periodic (Θ t) ∧ Θ t =ᵐ[volume.restrict unitCube] θ t ∧
              CsNormLe s (Θ t) (C * Real.sqrt (l2NormSq f))) ∧
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
  by exact AVRegularity.Providers.interior_regularity_and_dissipation α s hα₀ hα₁ hs₀ hs₁

end AVRegularity
