-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Proofs.Main.UniformAnomalousDissipationConstruction
import AVRegularity.Assembly.ConstructionToInterior
import AVRegularity.Proofs.PaperFacing.Arithmetic
import AVRegularity.Statements.Construction.ExistsFastProfile
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Construction.OcBandSet
public import AVRegularity.Statements.Definitions.CsNormLe
public import AVRegularity.Statements.Definitions.IsHolderDivFreeVelocity
public import AVRegularity.Statements.Definitions.IsWeakSolutionOn
public import AVRegularity.Statements.Definitions.IsWeakSolutionOnGrad

/-! Proof of the root `uniform_anomalous_dissipation`: `uniform_anomalous_dissipation_construction`
at `s = (1-α)/4`, an admissible `q` (`exists_isAdmissibleQ_of_lt`), a fast profile
(`exists_isFastProfile`) and `Λ = Λ₀`, with the bands `κ_M = ε_{M+1}^{β-γ}` of
`interior_regularity_of_construction` (`exists_bandCenters_eq_ocBandSet`). -/

@[expose] public section

open MeasureTheory Filter Topology Homogenization AVenhance

namespace AVRegularity.Providers

/-- **`uniform_anomalous_dissipation`**. -/
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
              l2NormSq (fun x => f x - ∫ y in unitCube, f y)) := by
  have hs₀ : 0 < (1 - α) / 4 := by linarith
  have hs₁ : (1 - α) / 4 < (1 - α) / 2 := by linarith
  obtain ⟨q, hq⟩ := PaperFacing.exists_isAdmissibleQ_of_lt hα₀ hα₁ hs₀ hs₁
  obtain ⟨ζ, hζ⟩ := AVRegularity.exists_isFastProfile
  obtain ⟨Λ₀, hΛ₀, hB⟩ :=
    uniform_anomalous_dissipation_construction α _ hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨⟨Φ, hΦ⟩, hΦall⟩ := hB Λ₀ le_rfl
  obtain ⟨b, -, hbH, c, hc, hdis, hdec⟩ := hΦall Φ hΦ
  obtain ⟨κc, hκpos, hκgap, hbands⟩ := Assembly.exists_bandCenters_eq_ocBandSet hα₀ hq hΛ₀
  exact ⟨b, hbH, κc, hκpos, hκgap, c, hc, fun a κ hκ => hdis a κ (hbands ▸ hκ),
    fun a κ hκ => hdec a κ (hbands ▸ hκ)⟩

end AVRegularity.Providers
