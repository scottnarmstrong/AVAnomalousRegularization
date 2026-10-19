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

/-! Proof of `interior_regularity_and_dissipation`: `interior_regularity_and_dissipation_of_limit`
(Theorems A and B of the paper for one limit `b`) at an admissible `q`, a fast profile and `Λ = Λ₀`,
with the bands of `interior_regularity_of_construction` (`exists_bandCenters_eq_ocBandSet`). -/

@[expose] public section

open MeasureTheory Filter Topology Homogenization AVenhance

namespace AVRegularity.Providers

/-- **`interior_regularity_and_dissipation`**. -/
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
              l2NormSq (fun x => f x - ∫ y in unitCube, f y)) := by
  obtain ⟨q, hq⟩ := PaperFacing.exists_isAdmissibleQ_of_lt hα₀ hα₁ hs₀ hs₁
  obtain ⟨ζ, hζ⟩ := AVRegularity.exists_isFastProfile
  obtain ⟨Λ₀, hΛ₀, h⟩ := interior_regularity_and_dissipation_of_limit α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨⟨Φ, hΦ⟩, hΦall⟩ := h Λ₀ le_rfl
  obtain ⟨b, -, hbH, hAt, c, hc, hdis, hdec⟩ := hΦall Φ hΦ
  obtain ⟨κc, hκpos, hκgap, hbands⟩ := Assembly.exists_bandCenters_eq_ocBandSet hα₀ hq hΛ₀
  refine ⟨b, hbH, κc, hκpos, hκgap, fun t₀ T ht₀ hT => ?_, c, hc,
    fun a κ hκ => hdis a κ (hbands ▸ hκ), fun a κ hκ => hdec a κ (hbands ▸ hκ)⟩
  obtain ⟨C, hC⟩ := hAt t₀ T ht₀ hT
  exact ⟨C, fun a κ hκ => hC a κ (hbands ▸ hκ)⟩

end AVRegularity.Providers
