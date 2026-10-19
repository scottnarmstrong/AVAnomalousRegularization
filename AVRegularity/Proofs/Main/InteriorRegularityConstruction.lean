-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Proofs.FinalAssembly.Roots
import AVRegularity.Proofs.Results.Construction.PreservationSuccessor
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Construction.OcBandSet
public import AVRegularity.Statements.Definitions.CsNormLe
public import AVRegularity.Statements.Definitions.IsHolderDivFreeVelocity
public import AVRegularity.Statements.Definitions.IsWeakSolutionOn

/-! Proof of the root `interior_regularity_construction`.

The root is the conditional assembly
`interior_regularity_construction_of_preservation`
(`Providers/Endgame/W34Roots.lean`: `roots_of_finiteTarget` through `oc_finite` from
the proofs of the error energy bound and `successor_bill`) at the `preservation_successor` proof. The
statement is the root's, verbatim. -/

@[expose] public section

open MeasureTheory Filter Topology Homogenization AVenhance

namespace AVRegularity.Providers

/-- **`interior_regularity_construction`**. -/
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
  Endgame.interior_regularity_construction_of_preservation Providers.preservation_successor
    α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

end AVRegularity.Providers
