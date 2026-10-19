-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.Main.InteriorRegularityConstruction
public import AVRegularity.Statements.Definitions.CsNormLe
public import AVRegularity.Statements.Definitions.IsHolderDivFreeVelocity
public import AVRegularity.Statements.Definitions.IsWeakSolutionOn
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.OcBandSet
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Construction.IsFastProfile

/-! Theorem A of the paper (interior regularity) for the velocity field of the construction of
Section 1, for every integer `Λ ≥ Λ₀`, together with the existence of the weak solutions. -/

@[expose] public section

open MeasureTheory Filter Topology Homogenization AVenhance

namespace AVRegularity

/-- **Theorem A for the construction.** Fix `0 < α < 1/3`, `0 < s < (1-α)/2`, an admissible
`q` and fast profile `ζ`. There is `Λ₀ ≥ 128` such that for every integer `Λ ≥ Λ₀` the
stream recursion of Section 1 can be carried out, its velocities `b_M = ∇^⊥ φ_M` converge to a
bounded, periodic, divergence-free `b ∈ C^α`, and, with `β = 1+α` and the bands
`𝒦 = ⋃_{M ≥ 1} [ε_M^{β-γ}/2, 2ε_M^{β-γ}]`, for every `0 < t₀ < T` there is `C` such that for all
`a ∈ ℝ`, `κ ∈ 𝒦`, `f ∈ L²(𝕋²)` a weak solution with `θ(a) = f` on `[a, a+T]` exists and every
such solution has a jointly continuous representative on `[a+t₀, a+T] × 𝕋²` with
`sup_{a+t₀ ≤ t ≤ a+T} ‖θ(t)‖_{C^s(𝕋²)} ≤ C ‖f‖₂`. -/
theorem interior_regularity_construction (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      (∃ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ) ∧
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
        ∃ b : ℝ → Vec 2 → Vec 2,
          (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) ∧
          IsHolderDivFreeVelocity α b ∧
          ∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∃ C : ℝ,
            ∀ a : ℝ,
            ∀ κ ∈ ocBandSet α q Λ,
            ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
              (∃ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a (a + T) f θ) ∧
              ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a (a + T) f θ →
                ∃ Θ : ℝ → Vec 2 → ℝ,
                  ContinuousOn (fun p : ℝ × Vec 2 => Θ p.1 p.2)
                    (Set.Icc (a + t₀) (a + T) ×ˢ Set.univ) ∧
                  ∀ t ∈ Set.Icc (a + t₀) (a + T),
                    IsZ2Periodic (Θ t) ∧ Θ t =ᵐ[volume.restrict unitCube] θ t ∧
                    CsNormLe s (Θ t) (C * Real.sqrt (l2NormSq f)) :=
  by exact AVRegularity.Providers.interior_regularity_construction α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

end AVRegularity
