-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Definitions.IsHolderDivFreeVelocity
public import AVRegularity.Statements.Definitions.IsLocalEnergySolution
public import AVRegularity.Applications.Construction
import AVRegularity.Proofs.Applications.VanishingDiffusivityLimitsLocal
import AVRegularity.Statements.Construction.ExistsOCStreamSeq
import AVRegularity.Velocity.ExistsLimitVelocity
import AVRegularity.Assembly.ConstructionToInterior

@[expose] public section

section
open MeasureTheory Filter Topology Homogenization AVenhance
namespace AVRegularity.Assembly.TopWiring

/-! Text copies of the statements `oc_finite` and `oc_global`, so that library
code can take them as hypotheses without importing the module proving them. -/

/-- The statement of `oc_finite`. Verbatim copy of `AVRegularity.Providers.oc_finite`. -/
def OcFiniteTargetStatement : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ),
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
      CsNormLe s Θt (C * Real.sqrt (l2NormSq f))

/-- The statement of `oc_global`. Verbatim copy of `AVRegularity.Providers.oc_global`. -/
def OcGlobalTargetStatement : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ),
  ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
        ∀ b : ℝ → Vec 2 → Vec 2,
          (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) →
          ∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∃ C : ℝ,
            ∀ a : ℝ, ∀ κ ∈ ocBandSet α q Λ, ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
            ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a (a + T) f θ →
              ∃ Θ : ℝ → Vec 2 → ℝ,
                ContinuousOn (fun p : ℝ × Vec 2 => Θ p.1 p.2)
                  (Set.Icc (a + t₀) (a + T) ×ˢ Set.univ) ∧
                ∀ t ∈ Set.Icc (a + t₀) (a + T),
                  IsZ2Periodic (Θ t) ∧ Θ t =ᵐ[volume.restrict unitCube] θ t ∧
                  CsNormLe s (Θ t) (C * Real.sqrt (l2NormSq f))

/-! Text copies of the statements of the five root theorems, as closed `Prop`s. -/

/-- The statement of `interior_regularity` (Theorem A of the paper), verbatim. -/
def InteriorRegularityRootStatement : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2),
  ∃ b : ℝ → Vec 2 → Vec 2, IsHolderDivFreeVelocity α b ∧
    ∃ κc : ℕ → ℝ, (∀ M, 0 < κc M) ∧ (∀ M, 4 * κc (M + 1) < κc M) ∧
    ∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∃ C : ℝ,
      ∀ a : ℝ, ∀ κ ∈ ⋃ M : ℕ, Set.Icc (κc M / 2) (2 * κc M),
      ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
        (∃ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a (a + T) f θ) ∧
        ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a (a + T) f θ →
          ∃ Θ : ℝ → Vec 2 → ℝ,
            ContinuousOn (fun p : ℝ × Vec 2 => Θ p.1 p.2)
              (Set.Icc (a + t₀) (a + T) ×ˢ Set.univ) ∧
            ∀ t ∈ Set.Icc (a + t₀) (a + T),
              IsZ2Periodic (Θ t) ∧ Θ t =ᵐ[volume.restrict unitCube] θ t ∧
              CsNormLe s (Θ t) (C * Real.sqrt (l2NormSq f))

/-- The statement of `interior_regularity_construction` (Theorem A of the paper), verbatim. -/
def InteriorRegularityConstructionRootStatement : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ),
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
                    CsNormLe s (Θ t) (C * Real.sqrt (l2NormSq f))

/-- The statement of `local_interior_regularity` (Theorem C of the paper), verbatim. -/
def LocalInteriorRegularityRootStatement : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ),
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
                          ∫ p in outerPipe (fun t y => X t y t₁) t₁ T R, θ p.1 p.2 ^ 2)

/-- The statement of `vanishing_diffusivity_limits` (Corollary D(a) of the paper), verbatim. -/
def VanishingDiffusivityLimitsRootStatement : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ),
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
                  Tendsto (fun i => ∫ p, (θ i p.1 p.2 - θ' i p.1 p.2) * φ p) atTop (𝓝 0))

/-- The statement of `vanishing_diffusivity_limits_local` (Corollary D(b) of the paper),
verbatim. -/
def VanishingDiffusivityLimitsLocalRootStatement : Prop :=
  ∀ (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ),
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
                        Real.sqrt (vecNormSq (y - z)) ^ s ≤ C ϱ ϑ * F

end AVRegularity.Assembly.TopWiring
end

section
open MeasureTheory Filter Topology Homogenization AVenhance AVRegularity.Applications
namespace AVRegularity.Assembly.TopWiring

/-! The finite statement implies `OcFiniteStatement` (restrict to `1 ≤ M`), hence the
global statement through `oc_global_of_finite`. -/

/-- The statement of `oc_finite` gives `OcFiniteStatement` at every admissible parameter. -/
theorem ocFiniteStatement_of_target (h : OcFiniteTargetStatement)
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) : OcFiniteStatement α s q ζ := by
  obtain ⟨Λ₀, hΛ₀, H⟩ := h α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, fun Λ hΛ Φ hΦ J hJ t₀ T ht₀ htT => ?_⟩
  obtain ⟨Mstar, C, H2⟩ := H Λ hΛ Φ hΦ J hJ t₀ T ht₀ htT
  exact ⟨Mstar, C, fun M hM _ => H2 M hM⟩

/-- `OcGlobalStatement` at every admissible parameter, from the finite statement. -/
theorem ocGlobalStatement_of_finiteTarget (h : OcFiniteTargetStatement)
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) : OcGlobalStatement α s q ζ :=
  Providers.oc_global_of_finite α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
    (ocFiniteStatement_of_target h α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)

/-- The literal statement of `oc_global` from the literal statement of `oc_finite`. -/
theorem ocGlobalTarget_of_finiteTarget (h : OcFiniteTargetStatement) :
    OcGlobalTargetStatement :=
  fun α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ =>
    ocGlobalStatement_of_finiteTarget h α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

end AVRegularity.Assembly.TopWiring
end

section
open MeasureTheory Filter Topology Homogenization AVenhance
namespace AVRegularity.Assembly.TopWiring

/-! The construction theorem (`interior_regularity_construction`) from the global statement, the existence of
the stream sequence and of the limit velocity, and existence of weak solutions. -/

/-- Every diffusivity in the band set `ocBandSet` is positive (for `Λ ≥ 1`). -/
theorem pos_of_mem_ocBandSet {α q : ℝ} {Λ : ℕ} (hΛ : 1 ≤ Λ) {κ : ℝ}
    (hκ : κ ∈ ocBandSet α q Λ) : 0 < κ := by
  rw [ocBandSet] at hκ
  obtain ⟨M, hM⟩ := Set.mem_iUnion.mp hκ
  obtain ⟨_, hmem⟩ := Set.mem_iUnion.mp hM
  have hε := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := M) hΛ
  have hpos : 0 < ocEpsilon q Λ M ^ ((1 + α) - ocGamma α q) / 2 :=
    div_pos (Real.rpow_pos_of_pos hε _) two_pos
  exact lt_of_lt_of_le hpos hmem.1

/-- The construction theorem from the global statement. -/
theorem interiorRegularityConstructionRoot_of_global (h : OcGlobalTargetStatement) :
    InteriorRegularityConstructionRootStatement := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λ₀, hΛ₀, H⟩ := h α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, fun Λ hΛ => ?_⟩
  have h128 : 128 ≤ Λ := hΛ₀.trans hΛ
  refine ⟨exists_isOCStreamSeq α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ h128, fun Φ hΦ => ?_⟩
  obtain ⟨b, hlim, hb⟩ :=
    Velocity.exists_limit_velocity α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ h128 Φ hΦ
  refine ⟨b, hlim, hb, fun t₀ T ht₀ htT => ?_⟩
  obtain ⟨C, hC⟩ := H Λ hΛ Φ hΦ b hlim t₀ T ht₀ htT
  refine ⟨C, fun a κ hκ f hf => ⟨?_, fun θ hθ => hC a κ hκ f hf θ hθ⟩⟩
  have hκpos := pos_of_mem_ocBandSet (by omega) hκ
  obtain ⟨θ, hθ, -⟩ := Wellposed.exists_unique_isWeakSolutionOn_of_isHolderDivFreeVelocity
    α hα₀ b hb κ hκpos a (a + T) (by linarith) f hf
  exact ⟨θ, hθ⟩

/-! The main theorems `interior_regularity`, `local_interior_regularity`,
`vanishing_diffusivity_limits` and `vanishing_diffusivity_limits_local` from the finite
statement (the first via the construction statement). -/

/-- Local interior regularity from the finite statement. -/
theorem localInteriorRegularityRoot_of_finiteTarget (h : OcFiniteTargetStatement) :
    LocalInteriorRegularityRootStatement :=
  fun α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ =>
    Providers.local_interior_regularity_of_global α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
      (ocGlobalStatement_of_finiteTarget h α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)

/-- The vanishing-diffusivity limits from the finite statement. -/
theorem vanishingDiffusivityLimitsRoot_of_finiteTarget (h : OcFiniteTargetStatement) :
    VanishingDiffusivityLimitsRootStatement :=
  fun α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ =>
    Providers.vanishing_diffusivity_limits_of_global α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
      (ocGlobalStatement_of_finiteTarget h α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)

/-- The local vanishing-diffusivity limits from the finite statement. -/
theorem vanishingDiffusivityLimitsLocalRoot_of_finiteTarget (h : OcFiniteTargetStatement) :
    VanishingDiffusivityLimitsLocalRootStatement :=
  fun α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ =>
    Providers.vanishing_diffusivity_limits_local_of_global α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
      (ocGlobalStatement_of_finiteTarget h α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)

/-- Interior regularity from the construction statement. -/
theorem interiorRegularityRoot_of_constructionRoot
    (h : InteriorRegularityConstructionRootStatement) : InteriorRegularityRootStatement :=
  interior_regularity_of_construction h

end AVRegularity.Assembly.TopWiring
end

section
namespace AVRegularity.Assembly.TopWiring

/-! The five root theorems from the single hypothesis `OcFiniteTargetStatement`. -/

/-- All five root statements follow from the literal statement of `oc_finite`. -/
theorem roots_of_finiteTarget (h : OcFiniteTargetStatement) :
    InteriorRegularityRootStatement ∧ InteriorRegularityConstructionRootStatement ∧
    LocalInteriorRegularityRootStatement ∧ VanishingDiffusivityLimitsRootStatement ∧
    VanishingDiffusivityLimitsLocalRootStatement :=
  have h2 := interiorRegularityConstructionRoot_of_global (ocGlobalTarget_of_finiteTarget h)
  ⟨interiorRegularityRoot_of_constructionRoot h2, h2,
    localInteriorRegularityRoot_of_finiteTarget h,
    vanishingDiffusivityLimitsRoot_of_finiteTarget h,
    vanishingDiffusivityLimitsLocalRoot_of_finiteTarget h⟩

end AVRegularity.Assembly.TopWiring
end
