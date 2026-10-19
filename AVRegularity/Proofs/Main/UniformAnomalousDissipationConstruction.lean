-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Proofs.Main.InteriorRegularityConstruction
import AVRegularity.Proofs.PaperFacing.UniformDissipation
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Construction.OcBandSet
public import AVRegularity.Statements.Definitions.CsNormLe
public import AVRegularity.Statements.Definitions.IsHolderDivFreeVelocity
public import AVRegularity.Statements.Definitions.IsWeakSolutionOn
public import AVRegularity.Statements.Definitions.IsWeakSolutionOnGrad

/-! Proof of `uniform_anomalous_dissipation_construction` (Theorem B of the paper), and
`interior_regularity_and_dissipation_of_limit` (Theorems A and B for every limit `b` of the
stream recursion): the stream sequence, its Hölder limit and Theorem A from
`interior_regularity_construction`; the dissipation and the decay from
`PaperFacing.uniform_dissipation_exp` (stated for every limit `b`); the existence of the weak
solutions from Theorem A's existence clause. `IsWeakSolutionOnGrad` is definitionally
`IsWeakSolutionOnWith`. -/

@[expose] public section

open MeasureTheory Filter Topology Homogenization AVenhance

namespace AVRegularity.Providers

/-- **Theorems A and B of the paper for every limit of the stream recursion**, at `Λ ≥ Λ₀` (`Λ₀` the
larger of the thresholds of `interior_regularity_construction` and
`PaperFacing.uniform_dissipation_exp`): Theorem A's conclusion, and Theorem B's with the existence
of the weak solutions, which comes from Theorem A's existence clause on the windows
`[a, a + (t - a)]`. -/
theorem interior_regularity_and_dissipation_of_limit (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      (∃ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ) ∧
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
        ∃ b : ℝ → Vec 2 → Vec 2,
          (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) ∧
          IsHolderDivFreeVelocity α b ∧
          (∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∃ C : ℝ,
            ∀ a : ℝ, ∀ κ ∈ ocBandSet α q Λ,
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
                    l2NormSq (fun x => f x - ∫ y in unitCube, f y)) := by
  obtain ⟨Λ₁, hΛ₁, hA⟩ := interior_regularity_construction α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λ₂, -, hB⟩ := PaperFacing.uniform_dissipation_exp α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨max Λ₁ Λ₂, hΛ₁.trans (le_max_left _ _), fun Λ hΛ =>
    ⟨(hA Λ ((le_max_left _ _).trans hΛ)).1, fun Φ hΦ => ?_⟩⟩
  obtain ⟨b, hb, hbH, hAt⟩ := (hA Λ ((le_max_left _ _).trans hΛ)).2 Φ hΦ
  obtain ⟨c, hc, hdis, hdec⟩ := hB Λ ((le_max_right _ _).trans hΛ) Φ hΦ b hb
  have hex : ∀ a : ℝ, ∀ κ ∈ ocBandSet α q Λ, ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
      ∀ t : ℝ, a < t → ∃ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a t f θ := by
    intro a κ hκ f hf t ht
    have hu : 0 < t - a := sub_pos.2 ht
    obtain ⟨C, hC⟩ := hAt ((t - a) / 2) (t - a) (half_pos hu) (half_lt_self hu)
    obtain ⟨θ, hθ⟩ := (hC a κ hκ f hf).1
    have e : a + (t - a) = t := by ring
    exact ⟨θ, e ▸ hθ⟩
  refine ⟨b, hb, hbH, hAt, c, hc, fun a κ hκ f hf => ⟨?_, hdis a κ hκ f hf⟩,
    fun a κ hκ f hf t ht => ⟨hex a κ hκ f hf t ht, hdec a κ hκ f hf t ht⟩⟩
  obtain ⟨θ, Dθ, hθ⟩ := hex a κ hκ f hf (a + 1) (by linarith)
  exact ⟨θ, Dθ, hθ⟩

/-- **`uniform_anomalous_dissipation_construction`**. -/
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
                    l2NormSq (fun x => f x - ∫ y in unitCube, f y)) := by
  obtain ⟨Λ₀, hΛ₀, h⟩ := interior_regularity_and_dissipation_of_limit α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, fun Λ hΛ => ⟨(h Λ hΛ).1, fun Φ hΦ => ?_⟩⟩
  obtain ⟨b, hb, hbH, -, hB⟩ := (h Λ hΛ).2 Φ hΦ
  exact ⟨b, hb, hbH, hB⟩

end AVRegularity.Providers
