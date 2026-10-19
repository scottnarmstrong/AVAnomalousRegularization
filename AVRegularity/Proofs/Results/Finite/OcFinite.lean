-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Proofs.FinalAssembly.Roots
import AVRegularity.Proofs.Results.Construction.PreservationSuccessor
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Construction.OcGamma
public import AVRegularity.Statements.Definitions.CsNormLe
public import AVRegularity.Statements.Definitions.IsWeakSolutionOn

/-! Proof of `oc_finite` (the statement below is a copy of its text): the conditional assembly
`ocFinite_of_preservation` (module `Proofs.FinalAssembly.Roots`: the error energy bound, the
`successor_bill` proof, `ocFiniteTarget_of_leaves`) at the `preservation_successor` proof. -/

@[expose] public section

open MeasureTheory Homogenization AVenhance

namespace AVRegularity.Providers

/-- **Regularity at finite velocity**. Proposition 3.1 of the paper follows from it. -/
theorem oc_finite (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
    ∀ J : ℕ, 1 ≤ J → ∀ t₀ T : ℝ, 0 < t₀ → t₀ < T →
    ∃ (Mstar : ℕ) (C : ℝ), ∀ M : ℕ, Mstar ≤ M →
    ∀ κ ∈ Set.Icc (ocEpsilon q Λ M ^ ((1 + α) - ocGamma α q) / 2)
        (2 * ocEpsilon q Λ M ^ ((1 + α) - ocGamma α q)),
    ∀ a : ℝ, ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
    ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn (streamVel (Φ (M + J))) κ a (a + T) f θ →
    ∀ t ∈ Set.Icc (a + t₀) (a + T), ∃ Θt : Vec 2 → ℝ,
      IsZ2Periodic Θt ∧ Θt =ᵐ[volume.restrict unitCube] θ t ∧
      CsNormLe s Θt (C * Real.sqrt (l2NormSq f)) :=
  Endgame.ocFinite_of_preservation preservation_successor α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

end AVRegularity.Providers
