-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.Main.VanishingDiffusivityLimitsLocal
public import AVRegularity.Statements.Definitions.IsLocalEnergySolution
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Construction.OcBandSet
public import AVRegularity.Statements.Construction.OcA
public import AVRegularity.Statements.Construction.OcCStar
public import AVenhance.Statements.Flow.IsFlow
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-! Selected vanishing-diffusivity limits, local part, with the pipe data of
`local_interior_regularity`. -/

@[expose] public section

open MeasureTheory Filter Topology Homogenization AVenhance

namespace AVRegularity

/-- **Vanishing-diffusivity limits, local part** (Corollary D(b) of the paper follows from it).
With the construction and pipe data `n, T, R` of `local_interior_regularity` and inner-pipe
constants `C(ϱ, ϑ)`: local energy solutions on one fixed outer pipe
with `κ_i ∈ 𝒦`, `κ_i → 0` and normalized `L²` averages at most `F` have continuous
representatives, a subsequence of which converges uniformly on compact subsets of
`S = {(t, F_t(y)) : t₁ - 4T < t ≤ t₁, |y| < R/8}`. The limit is continuous on `S` (so it has the
one-sided top trace), solves `∂ₜθ + b·∇θ = 0` distributionally on the interior of `S`, and
satisfies every inner-pipe estimate of `local_interior_regularity` (all `0 < ϱ < 1/8`,
`0 < ϑ < 4`) with right side `C(ϱ, ϑ) F`. -/
theorem vanishing_diffusivity_limits_local (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
        ∃ b : ℝ → Vec 2 → Vec 2,
          (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) ∧
          ∀ cT CT : ℝ, 0 < cT → 0 < CT → ∃ C₁ : ℝ, 0 < C₁ ∧
            ∀ (n : ℕ) (T R : ℝ), 2 ≤ n → 0 < T → 0 < R →
              cT * ocTauPP α q Λ (n - 1) ≤ T → T ≤ CT * ocTauPP α q Λ (n - 1) →
              8 * T * ocA α q Λ (n - 2) ≤ ocCStar →
              C₁ * max (ocEpsilon q Λ (n - 1) ^ α * T)
                  (Real.sqrt (sSup (ocBandSet α q Λ) * T)) ≤ R →
              R ≤ 1 / 8 →
              ∃ C : ℝ → ℝ → ℝ, ∀ t₁ : ℝ, ∀ X : ℝ → Vec 2 → ℝ → Vec 2,
                IsFlow (streamVel (Φ (n - 2))) X →
                ∀ (F : ℝ) (κ : ℕ → ℝ) (θ : ℕ → ℝ → Vec 2 → ℝ),
                  (∀ i, κ i ∈ ocBandSet α q Λ) → Tendsto κ atTop (𝓝 0) →
                  (∀ i, IsLocalEnergySolution b (κ i) (fun t y => X t y t₁) t₁ T R (θ i)) →
                  (∀ i, Real.sqrt ((volume (outerPipe (fun t y => X t y t₁) t₁ T R)).toReal⁻¹ *
                      ∫ p in outerPipe (fun t y => X t y t₁) t₁ T R, θ i p.1 p.2 ^ 2) ≤ F) →
                  ∃ (σ : ℕ → ℕ) (Θ : ℕ → ℝ → Vec 2 → ℝ) (θstar : ℝ → Vec 2 → ℝ),
                    StrictMono σ ∧
                    (∀ i, ContinuousOn (fun p : ℝ × Vec 2 => Θ i p.1 p.2)
                        {p | t₁ - 4 * T < p.1 ∧ p.1 ≤ t₁ ∧
                          ∃ y ∈ euclidBall 0 (R / 8), p.2 = X p.1 y t₁} ∧
                      (fun p : ℝ × Vec 2 => Θ i p.1 p.2) =ᵐ[volume.restrict
                        {p | t₁ - 4 * T < p.1 ∧ p.1 ≤ t₁ ∧
                          ∃ y ∈ euclidBall 0 (R / 8), p.2 = X p.1 y t₁}]
                        (fun p : ℝ × Vec 2 => θ i p.1 p.2)) ∧
                    (∀ K ⊆ {p : ℝ × Vec 2 | t₁ - 4 * T < p.1 ∧ p.1 ≤ t₁ ∧
                          ∃ y ∈ euclidBall 0 (R / 8), p.2 = X p.1 y t₁}, IsCompact K →
                      TendstoUniformlyOn (fun i (p : ℝ × Vec 2) => Θ (σ i) p.1 p.2)
                        (fun p : ℝ × Vec 2 => θstar p.1 p.2) atTop K) ∧
                    ContinuousOn (fun p : ℝ × Vec 2 => θstar p.1 p.2)
                      {p | t₁ - 4 * T < p.1 ∧ p.1 ≤ t₁ ∧
                        ∃ y ∈ euclidBall 0 (R / 8), p.2 = X p.1 y t₁} ∧
                    (∀ φ : ℝ × Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
                      tsupport φ ⊆ interior {p : ℝ × Vec 2 | t₁ - 4 * T < p.1 ∧ p.1 ≤ t₁ ∧
                          ∃ y ∈ euclidBall 0 (R / 8), p.2 = X p.1 y t₁} →
                      ∫ p, θstar p.1 p.2 *
                        (fderiv ℝ φ p (1, 0) +
                          ∑ j : Fin 2, b p.1 p.2 j * fderiv ℝ φ p (0, basisVec j)) = 0) ∧
                    ∀ ϱ ϑ : ℝ, 0 < ϱ → ϱ < 1 / 8 → 0 < ϑ → ϑ < 4 →
                    ∀ t ∈ Set.Icc (t₁ - ϑ * T) t₁,
                    ∀ x ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R),
                    ∀ y ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R),
                    ∀ z ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R), y ≠ z →
                      |θstar t x| + |θstar t y - θstar t z| /
                        Real.sqrt (vecNormSq (y - z)) ^ s ≤ C ϱ ϑ * F :=
  by exact AVRegularity.Providers.vanishing_diffusivity_limits_local α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

end AVRegularity
