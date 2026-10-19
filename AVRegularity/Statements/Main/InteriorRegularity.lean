-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.Main.InteriorRegularity
public import AVRegularity.Statements.Definitions.CsNormLe
public import AVRegularity.Statements.Definitions.IsHolderDivFreeVelocity
public import AVRegularity.Statements.Definitions.IsWeakSolutionOn

/-! Theorem A of the paper (interior regularity), in existential form: there are a velocity
field and diffusivity bands with the interior estimate. `interior_regularity_construction`
states it for the construction of Section 1. -/

@[expose] public section

open MeasureTheory Homogenization AVenhance

namespace AVRegularity

/-- **Theorem A of the paper (interior regularity), existential form.** For `0 < α < 1/3` and
`0 < s < (1-α)/2` there are a bounded, periodic, divergence-free velocity `b ∈ C^α(ℝ × 𝕋²)` and
disjoint diffusivity bands `𝒦 = ⋃_M [κ_M/2, 2κ_M]`, `κ_M ↓ 0`, such that for every
`0 < t₀ < T` there is `C` with: for all `a ∈ ℝ`, `κ ∈ 𝒦`, `f ∈ L²(𝕋²)`, a weak solution with
`θ(a) = f` on `[a, a+T]` exists, and every such solution has a representative jointly continuous
on `[a+t₀, a+T] × 𝕋²` with `sup_{a+t₀ ≤ t ≤ a+T} ‖θ(t)‖_{C^s(𝕋²)} ≤ C ‖f‖₂`. -/
theorem interior_regularity (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) :
    ∃ b : ℝ → Vec 2 → Vec 2, IsHolderDivFreeVelocity α b ∧
    ∃ κc : ℕ → ℝ, (∀ M, 0 < κc M) ∧ (∀ M, 4 * κc (M + 1) < κc M) ∧
    ∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∃ C : ℝ,
      ∀ a : ℝ, ∀ κ ∈ ⋃ M : ℕ, Set.Icc (κc M / 2) (2 * κc M),
      ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
        (∃ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a (a + T) f θ) ∧
        ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a (a + T) f θ →
          ∃ Θ : ℝ → Vec 2 → ℝ,
            ContinuousOn (fun p : ℝ × Vec 2 => Θ p.1 p.2)
              (Set.Icc (a + t₀) (a + T) ×ˢ Set.univ) ∧
            ∀ t ∈ Set.Icc (a + t₀) (a + T),
              IsZ2Periodic (Θ t) ∧ Θ t =ᵐ[volume.restrict unitCube] θ t ∧
              CsNormLe s (Θ t) (C * Real.sqrt (l2NormSq f)) :=
  by exact AVRegularity.Providers.interior_regularity α s hα₀ hα₁ hs₀ hs₁

end AVRegularity
