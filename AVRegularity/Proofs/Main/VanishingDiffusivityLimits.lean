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
public import AVRegularity.Statements.Definitions.IsWeakSolutionOn

/-! Proof of the root `vanishing_diffusivity_limits`.

The root is the conditional assembly
`vanishing_diffusivity_limits_of_preservation`
(`Providers/Endgame/W34Roots.lean`: `roots_of_finiteTarget` through `oc_finite` from
the proofs of the error energy bound and `successor_bill`) at the `preservation_successor` proof. The
statement is the root's, verbatim. -/

@[expose] public section

open MeasureTheory Filter Topology Homogenization AVenhance

namespace AVRegularity.Providers

/-- **`vanishing_diffusivity_limits`**. -/
theorem vanishing_diffusivity_limits (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
        ∃ b : ℝ → Vec 2 → Vec 2,
          (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) ∧
          ∃ Cthm : ℝ → ℝ → ℝ,
          ∀ (a F : ℝ) (κ : ℕ → ℝ) (f : ℕ → Vec 2 → ℝ) (θ : ℕ → ℝ → Vec 2 → ℝ),
            (∀ i, κ i ∈ ocBandSet α q Λ) → Tendsto κ atTop (𝓝 0) →
            (∀ i, MemL2On unitCube (f i) ∧ Real.sqrt (l2NormSq (f i)) ≤ F) →
            (∀ i, ∀ T : ℝ, 0 < T → IsWeakSolutionOn b (κ i) a (a + T) (f i) (θ i)) →
            ∃ (σ : ℕ → ℕ) (fstar : Vec 2 → ℝ) (Θ : ℕ → ℝ → Vec 2 → ℝ)
                (θstar : ℝ → Vec 2 → ℝ),
              StrictMono σ ∧ MemL2On unitCube fstar ∧
              (∀ g : Vec 2 → ℝ, MemL2On unitCube g →
                Tendsto (fun i => ∫ x in unitCube, f (σ i) x * g x) atTop
                  (𝓝 (∫ x in unitCube, fstar x * g x))) ∧
              (∀ i, ContinuousOn (fun p : ℝ × Vec 2 => Θ i p.1 p.2) (Set.Ioi a ×ˢ Set.univ) ∧
                ∀ t, a < t → IsZ2Periodic (Θ i t) ∧ Θ i t =ᵐ[volume.restrict unitCube] θ i t) ∧
              TendstoLocallyUniformlyOn (fun i (p : ℝ × Vec 2) => Θ (σ i) p.1 p.2)
                (fun p : ℝ × Vec 2 => θstar p.1 p.2) atTop (Set.Ioi a ×ˢ Set.univ) ∧
              (∀ φ : ℝ × Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
                tsupport φ ⊆ Set.Ioi a ×ˢ Set.univ →
                ∫ p, θstar p.1 p.2 *
                  (fderiv ℝ φ p (1, 0) + ∑ j : Fin 2, b p.1 p.2 j * fderiv ℝ φ p (0, basisVec j))
                  = 0) ∧
              (∀ g : Vec 2 → ℝ, MemL2On unitCube g →
                Tendsto (fun t => ∫ x in unitCube, θstar t x * g x) (𝓝[>] a)
                  (𝓝 (∫ x in unitCube, fstar x * g x))) ∧
              (∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∀ t ∈ Set.Icc (a + t₀) (a + T),
                IsZ2Periodic (θstar t) ∧ CsNormLe s (θstar t) (Cthm t₀ T * F)) ∧
              (∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∃ C' : ℝ,
                ∀ t ∈ Set.Icc (a + t₀) (a + T), ∀ t' ∈ Set.Icc (a + t₀) (a + T), ∀ x : Vec 2,
                  |θstar t x - θstar t' x| ≤ C' * |t - t'| ^ (s / (1 + s))) ∧
              (∀ (Mi : ℕ → ℕ) (θ' : ℕ → ℝ → Vec 2 → ℝ),
                (∀ i, 1 ≤ Mi i ∧ κ i ∈ Set.Icc
                  (ocEpsilon q Λ (Mi i) ^ ((1 + α) - ocGamma α q) / 2)
                  (2 * ocEpsilon q Λ (Mi i) ^ ((1 + α) - ocGamma α q))) →
                (∀ i, ∀ T : ℝ, 0 < T →
                  IsWeakSolutionOn (streamVel (Φ (Mi i))) (κ i) a (a + T) (f i) (θ' i)) →
                ∀ φ : ℝ × Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
                  tsupport φ ⊆ Set.Ioi a ×ˢ Set.univ →
                  Tendsto (fun i => ∫ p, (θ i p.1 p.2 - θ' i p.1 p.2) * φ p) atTop (𝓝 0)) :=
  Endgame.vanishing_diffusivity_limits_of_preservation Providers.preservation_successor
    α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

end AVRegularity.Providers
