-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.Main.LocalInteriorRegularity
public import AVRegularity.Statements.Definitions.IsLocalEnergySolution
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Construction.OcBandSet
public import AVRegularity.Statements.Construction.OcA
public import AVRegularity.Statements.Construction.OcCStar
public import AVenhance.Statements.Flow.IsFlow

/-! Local interior regularity in material pipes. Theorem C of the paper follows from it. -/

@[expose] public section

open MeasureTheory Filter Topology Homogenization AVenhance

namespace AVRegularity

/-- **Local interior regularity** (Theorem C of the paper follows from it). Fix the construction
(`Λ ≥ Λ₀`) with limit velocity `b`, and constants `c_T, C_T > 0`; there is a construction constant
`C₁` such that for pipe data `n ≥ 2`, `T, R > 0`, `0 < ϱ < 1/8`, `0 < ϑ < 4` with
`c_T τ″_{n-1} ≤ T ≤ C_T τ″_{n-1}`, `8Ta_{n-2} ≤ c_*`, `C₁ max{ε_{n-1}^α T, √(κ_max T)} ≤ R ≤ 1/8`
(`κ_max = sup 𝒦`), there is `C` such that for every `t₁`, with `F_t` the flow of `b_{n-2}`
normalized by `F_{t₁} = I`, every `κ ∈ 𝒦` and every local energy solution `θ` in `𝒫_out`: for each
`t ∈ I = [t₁ - ϑT, t₁]` the local trace of `θ(t)` (the `L²` limit from below of the pulled-back
slices) has a representative continuous on `K_t = F_t(B_{ϱR})` with
`‖θ(t)‖_{L^∞(K_t)} + [θ(t)]_{C^s(K_t)} ≤ C A`, `A = (|𝒫_out|⁻¹ ∬_{𝒫_out} |θ|²)^{1/2}`. -/
theorem local_interior_regularity (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
        ∃ b : ℝ → Vec 2 → Vec 2,
          (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) ∧
          ∀ cT CT : ℝ, 0 < cT → 0 < CT → ∃ C₁ : ℝ, 0 < C₁ ∧
            ∀ (n : ℕ) (T R ϱ ϑ : ℝ), 2 ≤ n → 0 < T → 0 < R → 0 < ϱ → ϱ < 1 / 8 →
              0 < ϑ → ϑ < 4 →
              cT * ocTauPP α q Λ (n - 1) ≤ T → T ≤ CT * ocTauPP α q Λ (n - 1) →
              8 * T * ocA α q Λ (n - 2) ≤ ocCStar →
              C₁ * max (ocEpsilon q Λ (n - 1) ^ α * T)
                  (Real.sqrt (sSup (ocBandSet α q Λ) * T)) ≤ R →
              R ≤ 1 / 8 →
              ∃ C : ℝ, ∀ t₁ : ℝ, ∀ X : ℝ → Vec 2 → ℝ → Vec 2,
                IsFlow (streamVel (Φ (n - 2))) X →
                ∀ κ ∈ ocBandSet α q Λ, ∀ θ : ℝ → Vec 2 → ℝ,
                  IsLocalEnergySolution b κ (fun t y => X t y t₁) t₁ T R θ →
                  ∃ Θ : ℝ → Vec 2 → ℝ, ∀ t ∈ Set.Icc (t₁ - ϑ * T) t₁,
                    ContinuousOn (Θ t) ((fun y => X t y t₁) '' euclidBall 0 (ϱ * R)) ∧
                    Tendsto (fun r => ∫ y in euclidBall 0 (ϱ * R),
                        (θ r (X r y t₁) - Θ t (X t y t₁)) ^ 2)
                      (𝓝[<] t ⊓ ae volume) (𝓝 0) ∧
                    ∀ x ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R),
                    ∀ y ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R),
                    ∀ z ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R), y ≠ z →
                      |Θ t x| + |Θ t y - Θ t z| / Real.sqrt (vecNormSq (y - z)) ^ s ≤
                        C * Real.sqrt ((volume (outerPipe (fun t y => X t y t₁) t₁ T R)).toReal⁻¹ *
                          ∫ p in outerPipe (fun t y => X t y t₁) t₁ T R, θ p.1 p.2 ^ 2) :=
  by exact AVRegularity.Providers.local_interior_regularity α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

end AVRegularity
