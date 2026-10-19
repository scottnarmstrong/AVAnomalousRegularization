-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.Main.UniformAnomalousDissipationConstruction
public import AVRegularity.Statements.Definitions.IsHolderDivFreeVelocity
public import AVRegularity.Statements.Definitions.IsWeakSolutionOn
public import AVRegularity.Statements.Definitions.IsWeakSolutionOnGrad
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.OcBandSet
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Construction.IsFastProfile

/-! Theorem B of the paper (uniform anomalous dissipation) for the construction of Section 1,
for `Λ ≥ Λ₀`, as `interior_regularity_construction` is for Theorem A. -/

@[expose] public section

open MeasureTheory Filter Topology Homogenization AVenhance

namespace AVRegularity

/-- **Theorem B of the paper for the construction (uniform anomalous dissipation).**
Fix `0 < α < 1/3`, `0 < s < (1-α)/2`, an admissible `q` and fast profile `ζ`. There is
`Λ₀ ≥ 128` such that for every integer `Λ ≥ Λ₀` the stream recursion of Section 1 can be carried
out, its velocities `b_M = ∇^⊥ φ_M` converge to a bounded, periodic, divergence-free `b ∈ C^α`,
and, with the bands `𝒦 = ⋃_{M ≥ 1} [ε_M^{β-γ}/2, 2ε_M^{β-γ}]`, there is `c > 0` such that for
all `a ∈ ℝ`, `κ ∈ 𝒦` and `f ∈ L²(𝕋²)`, with `(f) = ∫_{𝕋²} f`:
(i) a weak solution `θ` on `[a, a+1]` with `θ(a) = f` exists, and every such solution, with
gradient `Dθ`, has `κ ∫_a^{a+1} ∫_{𝕋²} |Dθ|² ≥ c ‖f - (f)‖₂²`;
(ii) for every `t > a`, a weak solution `θ` on `[a, t]` with `θ(a) = f` exists, and every such
solution has `‖θ(t) - (f)‖₂² ≤ 4 e^{-2c(t-a)} ‖f - (f)‖₂²`. -/
theorem uniform_anomalous_dissipation_construction (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      (∃ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ) ∧
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
        ∃ b : ℝ → Vec 2 → Vec 2,
          (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) ∧
          IsHolderDivFreeVelocity α b ∧
          ∃ c : ℝ, 0 < c ∧
            (∀ a : ℝ, ∀ κ ∈ ocBandSet α q Λ, ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
              (∃ θ : ℝ → Vec 2 → ℝ, ∃ Dθ : ℝ → Vec 2 → Vec 2,
                IsWeakSolutionOnGrad b κ a (a + 1) f θ Dθ) ∧
              ∀ θ : ℝ → Vec 2 → ℝ, ∀ Dθ : ℝ → Vec 2 → Vec 2,
                IsWeakSolutionOnGrad b κ a (a + 1) f θ Dθ →
                  c * l2NormSq (fun x => f x - ∫ y in unitCube, f y) ≤
                    κ * ∫ p in Set.Ioo a (a + 1) ×ˢ unitCube, vecNormSq (Dθ p.1 p.2)) ∧
            (∀ a : ℝ, ∀ κ ∈ ocBandSet α q Λ, ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
              ∀ t : ℝ, a < t →
              (∃ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a t f θ) ∧
              ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a t f θ →
                l2NormSq (fun x => θ t x - ∫ y in unitCube, f y) ≤
                  4 * Real.exp (-2 * c * (t - a)) *
                    l2NormSq (fun x => f x - ∫ y in unitCube, f y)) :=
  by exact AVRegularity.Providers.uniform_anomalous_dissipation_construction α s hα₀ hα₁ hs₀ hs₁ q hq
      ζ hζ

end AVRegularity
