-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Construction.OcA
public import AVRegularity.Statements.Construction.OcBandSet
public import AVRegularity.Statements.Construction.OcCStar
public import AVRegularity.Statements.Definitions.CsNormLe
public import AVRegularity.Statements.Definitions.IsHolderDivFreeVelocity
public import AVRegularity.Statements.Definitions.IsLocalEnergySolution
public import AVRegularity.Statements.Definitions.IsWeakSolutionOn
public import AVRegularity.Applications.TorusEnergy.With
import AVRegularity.Construction.Scales.Times
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.Proofs.Main.LocalInteriorRegularity
import AVRegularity.Proofs.Main.VanishingDiffusivityLimits
import AVRegularity.Proofs.Main.VanishingDiffusivityLimitsLocal
import AVRegularity.Proofs.PaperFacing.UniformDissipation
import AVRegularity.Velocity.ExistsLimitVelocity
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-! # Theorems A, B, C and Corollary D of the paper with one `Λ₀`

With `h = h_{m+1} = τ''_{m+1} = ocTauPP α q Λ (m + 1)`:

* `eight_ocTauPP_mul_ocA_le`: the short-time bound at the tube of Theorem C,
  `8 h_{m+1} ε_m^{β-2} ≤ 2^{-22}`; `two_zpow_neg_22_lt_ocCStar`: `2^{-22} < c_*`. Together they
  discharge the near-rigidity hypothesis `8 T ε_{n-2}^{β-2} ≤ c_*` of the local theorems at
  `T = h_{m+1}`, `n = m + 2`.
* `PaperTheoremC`, `PaperLocalLimits` (Theorem C and the local part of Corollary D): the clauses of
  `Providers.local_interior_regularity` and `Providers.vanishing_diffusivity_limits_local` at the
  tube of duration `8h`, `h = h_{m+1}`, radius `ρ`, `c_T = C_T = 1`, `n = m + 2`, with the inner
  radius `ρ′ = ϱρ` in place of the ratio `ϱ` and Theorem A's waiting time `t₀ ∈ (4h, 8h)` in
  place of the fraction `ϑ = 8 - t₀/h` (window `[t₁ - 8h + t₀, t₁]`).
* `PaperLocalResults`, `paper_local_results`: Theorem C and Corollary D (local part) with one
  `Λ₀`, one limit velocity `b` and one geometry constant `C₁`.
* `PaperTheoremA`, `PaperCorollaryDGlobal`, `PaperTheoremB`: the clauses of `Providers.oc_global`,
  `Providers.vanishing_diffusivity_limits` and `oc_global_and_uniform_dissipation_exp` after the
  limit velocity `b`.
* `paper_main_results`: Theorems A, B, C and Corollary D with one `Λ₀` and one `b`. -/

@[expose] public noncomputable section

open MeasureTheory Filter Topology Homogenization AVenhance AVRegularity.Applications

namespace AVRegularity.PaperFacing

/-! ### The near-rigidity condition -/

/-- The short-time bound at the tube of Theorem C of the paper: `8 h_{m+1} ε_m^{β-2} ≤ 2^{-22}`,
`h_{m+1} = τ''_{m+1}`. -/
theorem eight_ocTauPP_mul_ocA_le {α s q : ℝ} {Λ : ℕ} (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) (hΛ : 128 ≤ Λ) (m : ℕ) :
    8 * ocTauPP α q Λ (m + 1) * ocA α q Λ m ≤ (2 : ℝ) ^ (-22 : ℤ) := by
  have h : ocA α q Λ m * ocTauPP α q Λ (m + 1) ≤
      (2 : ℝ) ^ (-25 : ℤ) * ocEpsilon q Λ m ^ (2 * ocDelta α q) :=
    (Scales.admissible_time_scale_facts hα₀ hα₁ hs₀ hs₁ hq hΛ (m := m + 1)
      (Nat.succ_pos m)).2.2.2.2.1
  have hε := Scales.epsilon_basic (m := m) hq.1 hΛ
  have hδ := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  have hpow : ocEpsilon q Λ m ^ (2 * ocDelta α q) ≤ 1 :=
    Real.rpow_le_one hε.1.le hε.2.1 (by linarith)
  have h25 : (0 : ℝ) ≤ (2 : ℝ) ^ (-25 : ℤ) := by positivity
  calc 8 * ocTauPP α q Λ (m + 1) * ocA α q Λ m = 8 * (ocA α q Λ m * ocTauPP α q Λ (m + 1)) := by
        ring
    _ ≤ 8 * ((2 : ℝ) ^ (-25 : ℤ) * 1) :=
        mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_left hpow h25)) (by norm_num)
    _ = (2 : ℝ) ^ (-22 : ℤ) := by norm_num

/-- `2^{-22} < (800000 c)⁻¹` for `0 < c ≤ 3`. -/
private theorem paper_two_zpow_neg_22_lt_inv (c : ℝ) (hc0 : 0 < c) (hc : c ≤ 3) :
    (2 : ℝ) ^ (-22 : ℤ) < (800000 * c)⁻¹ := by
  rw [zpow_neg, inv_lt_inv₀ (by positivity) (by positivity)]
  norm_num
  linarith

/-- `2^{-22} < c_*` (`c_* = 1 / (800000 cosh (π/10)) ≈ 1.19 · 10^{-6}`). -/
theorem two_zpow_neg_22_lt_ocCStar : (2 : ℝ) ^ (-22 : ℤ) < ocCStar := by
  have hc : ocCStar = (800000 * Real.cosh (10 * Real.pi * (1 / 100)))⁻¹ := by
    unfold ocCStar
    congr 1
    ring
  have hx0 : 0 ≤ 10 * Real.pi * (1 / 100) := by positivity
  have hx1 : 10 * Real.pi * (1 / 100) ≤ 1 := by linarith [Real.pi_lt_four]
  have hsq : (10 * Real.pi * (1 / 100)) ^ 2 / 2 ≤ 1 := by
    have := pow_le_one₀ hx0 hx1 (n := 2)
    linarith
  have hcosh : Real.cosh (10 * Real.pi * (1 / 100)) ≤ 3 :=
    (Real.cosh_le_exp_half_sq _).trans ((Real.exp_le_exp.mpr hsq).trans
      (Real.exp_one_lt_d9.le.trans (by norm_num)))
  rw [hc]
  exact paper_two_zpow_neg_22_lt_inv _ (Real.cosh_pos _) hcosh

/-! ### Theorem C and Corollary D (local part) -/

/-- The inner tube `𝒯′ = {(t, X_m(t,y,t₁)) : t₁ - 4h < t ≤ t₁, |y| < ρ/8}`. -/
def paperInnerTube (X : ℝ → Vec 2 → ℝ → Vec 2) (t₁ h ρ : ℝ) : Set (ℝ × Vec 2) :=
  {p | t₁ - 4 * h < p.1 ∧ p.1 ≤ t₁ ∧ ∃ y ∈ euclidBall 0 (ρ / 8), p.2 = X p.1 y t₁}

/-- **Theorem C** of the paper (local interior regularity; it follows from this clause) at level
`m` and radius `ρ`: the tube
`𝒯 = outerPipe (fun t y => X t y t₁) t₁ h ρ` of duration `8h`, `h = h_{m+1}`, along the flow `X`
of `b_m`; for every inner radius `0 < ρ′ < ρ/8` and waiting time `4h < t₀ < 8h` there is `C` such
that every local energy solution `θ` on `𝒯` (any `t₁`, `X`, `κ ∈ 𝒦`) has on
`[t₁ - 8h + t₀, t₁]` local traces `Θ(t)` on `E_t = X(t, D_{ρ′}, t₁)` with
`‖Θ(t)‖_{C^s(E_t)} ≤ C (⨍_𝒯 θ²)^{1/2}`. -/
def PaperTheoremC (α s q : ℝ) (Λ : ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (b : ℝ → Vec 2 → Vec 2)
    (m : ℕ) (ρ : ℝ) : Prop :=
  ∀ ρ' t₀ : ℝ, 0 < ρ' → ρ' < ρ / 8 →
    4 * ocTauPP α q Λ (m + 1) < t₀ → t₀ < 8 * ocTauPP α q Λ (m + 1) →
    ∃ C : ℝ, ∀ t₁ : ℝ, ∀ X : ℝ → Vec 2 → ℝ → Vec 2,
      IsFlow (streamVel (Φ m)) X →
      ∀ κ ∈ ocBandSet α q Λ, ∀ θ : ℝ → Vec 2 → ℝ,
        IsLocalEnergySolution b κ (fun t y => X t y t₁) t₁ (ocTauPP α q Λ (m + 1)) ρ θ →
        ∃ Θ : ℝ → Vec 2 → ℝ, ∀ t ∈ Set.Icc (t₁ - 8 * ocTauPP α q Λ (m + 1) + t₀) t₁,
          ContinuousOn (Θ t) ((fun y => X t y t₁) '' euclidBall 0 ρ') ∧
          Tendsto (fun r => ∫ y in euclidBall 0 ρ',
              (θ r (X r y t₁) - Θ t (X t y t₁)) ^ 2)
            (𝓝[<] t ⊓ ae volume) (𝓝 0) ∧
          ∀ x ∈ (fun y => X t y t₁) '' euclidBall 0 ρ',
          ∀ y ∈ (fun y => X t y t₁) '' euclidBall 0 ρ',
          ∀ z ∈ (fun y => X t y t₁) '' euclidBall 0 ρ', y ≠ z →
            |Θ t x| + |Θ t y - Θ t z| / Real.sqrt (vecNormSq (y - z)) ^ s ≤
              C * Real.sqrt ((volume (outerPipe (fun t y => X t y t₁) t₁
                  (ocTauPP α q Λ (m + 1)) ρ)).toReal⁻¹ *
                ∫ p in outerPipe (fun t y => X t y t₁) t₁ (ocTauPP α q Λ (m + 1)) ρ,
                  θ p.1 p.2 ^ 2)

/-- **Corollary D of the paper, local part** at level `m` and radius `ρ` (Corollary D follows
from it): for every sequence `κ_i → 0` in `𝒦` and local energy solutions `θ_i` on the tube `𝒯`
(of Theorem C) with `(⨍_𝒯 θ_i²)^{1/2} ≤ F`, a
subsequence of continuous representatives on the inner tube `𝒯′` converges locally uniformly to a
continuous weak solution `θ_*` of the transport equation on `𝒯′`, with
`‖θ_*(t)‖_{C^s(E_t)} ≤ C(ρ′, t₀) F` on `[t₁ - 8h + t₀, t₁]`. -/
def PaperLocalLimits (α s q : ℝ) (Λ : ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (b : ℝ → Vec 2 → Vec 2)
    (m : ℕ) (ρ : ℝ) : Prop :=
  ∃ C : ℝ → ℝ → ℝ, ∀ t₁ : ℝ, ∀ X : ℝ → Vec 2 → ℝ → Vec 2,
    IsFlow (streamVel (Φ m)) X →
    ∀ (F : ℝ) (κ : ℕ → ℝ) (θ : ℕ → ℝ → Vec 2 → ℝ),
      (∀ i, κ i ∈ ocBandSet α q Λ) → Tendsto κ atTop (𝓝 0) →
      (∀ i, IsLocalEnergySolution b (κ i) (fun t y => X t y t₁) t₁ (ocTauPP α q Λ (m + 1)) ρ
        (θ i)) →
      (∀ i, Real.sqrt ((volume (outerPipe (fun t y => X t y t₁) t₁
          (ocTauPP α q Λ (m + 1)) ρ)).toReal⁻¹ *
          ∫ p in outerPipe (fun t y => X t y t₁) t₁ (ocTauPP α q Λ (m + 1)) ρ,
            θ i p.1 p.2 ^ 2) ≤ F) →
      ∃ (σ : ℕ → ℕ) (Θ : ℕ → ℝ → Vec 2 → ℝ) (θstar : ℝ → Vec 2 → ℝ),
        StrictMono σ ∧
        (∀ i, ContinuousOn (fun p : ℝ × Vec 2 => Θ i p.1 p.2)
            (paperInnerTube X t₁ (ocTauPP α q Λ (m + 1)) ρ) ∧
          (fun p : ℝ × Vec 2 => Θ i p.1 p.2) =ᵐ[volume.restrict
            (paperInnerTube X t₁ (ocTauPP α q Λ (m + 1)) ρ)]
            (fun p : ℝ × Vec 2 => θ i p.1 p.2)) ∧
        (∀ K ⊆ paperInnerTube X t₁ (ocTauPP α q Λ (m + 1)) ρ, IsCompact K →
          TendstoUniformlyOn (fun i (p : ℝ × Vec 2) => Θ (σ i) p.1 p.2)
            (fun p : ℝ × Vec 2 => θstar p.1 p.2) atTop K) ∧
        ContinuousOn (fun p : ℝ × Vec 2 => θstar p.1 p.2)
          (paperInnerTube X t₁ (ocTauPP α q Λ (m + 1)) ρ) ∧
        (∀ φ : ℝ × Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ interior (paperInnerTube X t₁ (ocTauPP α q Λ (m + 1)) ρ) →
          ∫ p, θstar p.1 p.2 *
            (fderiv ℝ φ p (1, 0) +
              ∑ j : Fin 2, b p.1 p.2 j * fderiv ℝ φ p (0, basisVec j)) = 0) ∧
        ∀ ρ' t₀ : ℝ, 0 < ρ' → ρ' < ρ / 8 →
        4 * ocTauPP α q Λ (m + 1) < t₀ → t₀ < 8 * ocTauPP α q Λ (m + 1) →
        ∀ t ∈ Set.Icc (t₁ - 8 * ocTauPP α q Λ (m + 1) + t₀) t₁,
        ∀ x ∈ (fun y => X t y t₁) '' euclidBall 0 ρ',
        ∀ y ∈ (fun y => X t y t₁) '' euclidBall 0 ρ',
        ∀ z ∈ (fun y => X t y t₁) '' euclidBall 0 ρ', y ≠ z →
          |θstar t x| + |θstar t y - θstar t z| /
            Real.sqrt (vecNormSq (y - z)) ^ s ≤ C ρ' t₀ * F

/-- Theorem C and Corollary D (local part) of the paper with one geometry constant `C₁`: for every
level `m` and radius `ρ ≤ 1/8` with `C₁ max{ε_{m+1}^α h, (sup 𝒦 · h)^{1/2}} ≤ ρ`, `h = h_{m+1}`. -/
def PaperLocalResults (α s q : ℝ) (Λ : ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (b : ℝ → Vec 2 → Vec 2) : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (m : ℕ) (ρ : ℝ), 0 < ρ →
    C₁ * max (ocEpsilon q Λ (m + 1) ^ α * ocTauPP α q Λ (m + 1))
        (Real.sqrt (sSup (ocBandSet α q Λ) * ocTauPP α q Λ (m + 1))) ≤ ρ →
    ρ ≤ 1 / 8 →
    PaperTheoremC α s q Λ Φ b m ρ ∧ PaperLocalLimits α s q Λ Φ b m ρ

/-- **Theorem C and Corollary D (local part) of the paper**, tube of duration `8h_{m+1}`, the
near-rigidity condition discharged; one `Λ₀`, one `b`, one `C₁`. -/
theorem paper_local_results (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
        ∃ b : ℝ → Vec 2 → Vec 2,
          (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) ∧
          PaperLocalResults α s q Λ Φ b := by
  obtain ⟨ΛB, hB128, hB⟩ := Providers.local_interior_regularity α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨ΛL, -, hL⟩ := Providers.vanishing_diffusivity_limits_local α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨max ΛB ΛL, hB128.trans (le_max_left _ _), fun Λ hΛ Φ hΦ => ?_⟩
  have hΛ128 : 128 ≤ Λ := hB128.trans ((le_max_left _ _).trans hΛ)
  obtain ⟨b, hb, HB⟩ := hB Λ ((le_max_left _ _).trans hΛ) Φ hΦ
  obtain ⟨bL, hbL, HL⟩ := hL Λ ((le_max_right _ _).trans hΛ) Φ hΦ
  have hbeq : bL = b := funext fun t => funext fun x => tendsto_nhds_unique (hbL t x) (hb t x)
  subst hbeq
  refine ⟨bL, hbL, ?_⟩
  obtain ⟨C₁B, hC₁B, HB₁⟩ := HB 1 1 one_pos one_pos
  obtain ⟨C₁L, -, HL₁⟩ := HL 1 1 one_pos one_pos
  refine ⟨max C₁B C₁L, lt_of_lt_of_le hC₁B (le_max_left _ _), fun m ρ hρ hC₁ hρ8 => ⟨?_, ?_⟩⟩
  all_goals
    have hT : 0 < ocTauPP α q Λ (m + 1) := Construction.Stream.ocTauPP_pos (by omega)
    have hrig : 8 * ocTauPP α q Λ (m + 1) * ocA α q Λ m ≤ ocCStar :=
      (eight_ocTauPP_mul_ocA_le hα₀ hα₁ hs₀ hs₁ hq hΛ128 m).trans two_zpow_neg_22_lt_ocCStar.le
    have hM : 0 ≤ max (ocEpsilon q Λ (m + 1) ^ α * ocTauPP α q Λ (m + 1))
        (Real.sqrt (sSup (ocBandSet α q Λ) * ocTauPP α q Λ (m + 1))) :=
      (Real.sqrt_nonneg _).trans (le_max_right _ _)
  · -- Theorem C
    intro ρ' t₀ hρ' hρ'8 ht₀4 ht₀8
    have hϱ : 0 < ρ' / ρ := div_pos hρ' hρ
    have hϱ8 : ρ' / ρ < 1 / 8 := by rw [div_lt_iff₀ hρ]; linarith
    have hϑ0 : 0 < 8 - t₀ / ocTauPP α q Λ (m + 1) := by
      rw [sub_pos, div_lt_iff₀ hT]; linarith
    have hϑ4 : 8 - t₀ / ocTauPP α q Λ (m + 1) < 4 := by
      have : 4 < t₀ / ocTauPP α q Λ (m + 1) := by rw [lt_div_iff₀ hT]; linarith
      linarith
    obtain ⟨C, hC⟩ := HB₁ (m + 2) (ocTauPP α q Λ (m + 1)) ρ (ρ' / ρ)
      (8 - t₀ / ocTauPP α q Λ (m + 1)) (by omega) hT hρ hϱ hϱ8 hϑ0 hϑ4 (one_mul _).le
      (one_mul _).symm.le hrig ((mul_le_mul_of_nonneg_right (le_max_left _ _) hM).trans hC₁) hρ8
    refine ⟨C, fun t₁ X hX κ hκ θ hθ => ?_⟩
    obtain ⟨Θ, hΘ⟩ := hC t₁ X hX κ hκ θ hθ
    have eρ : ρ' / ρ * ρ = ρ' := div_mul_cancel₀ ρ' hρ.ne'
    have et : t₁ - (8 - t₀ / ocTauPP α q Λ (m + 1)) * ocTauPP α q Λ (m + 1) =
        t₁ - 8 * ocTauPP α q Λ (m + 1) + t₀ := by
      rw [sub_mul, div_mul_cancel₀ t₀ hT.ne']; ring
    refine ⟨Θ, fun t ht => ?_⟩
    have h1 := hΘ t (by rw [et]; exact ht)
    rw [eρ] at h1
    exact h1
  · -- Corollary D, local part
    obtain ⟨C, hC⟩ := HL₁ (m + 2) (ocTauPP α q Λ (m + 1)) ρ (by omega) hT hρ (one_mul _).le
      (one_mul _).symm.le hrig ((mul_le_mul_of_nonneg_right (le_max_right _ _) hM).trans hC₁) hρ8
    refine ⟨fun ρ' t₀ => C (ρ' / ρ) (8 - t₀ / ocTauPP α q Λ (m + 1)),
      fun t₁ X hX F κ θ hκ hκ0 hθ hF => ?_⟩
    obtain ⟨σ, Θ, θstar, hσ, hrep, hunif, hcont, hweak, hbound⟩ :=
      hC t₁ X hX F κ θ hκ hκ0 hθ hF
    refine ⟨σ, Θ, θstar, hσ, hrep, hunif, hcont, hweak,
      fun ρ' t₀ hρ' hρ'8 ht₀4 ht₀8 t ht => ?_⟩
    have hϱ : 0 < ρ' / ρ := div_pos hρ' hρ
    have hϱ8 : ρ' / ρ < 1 / 8 := by rw [div_lt_iff₀ hρ]; linarith
    have hϑ0 : 0 < 8 - t₀ / ocTauPP α q Λ (m + 1) := by
      rw [sub_pos, div_lt_iff₀ hT]; linarith
    have hϑ4 : 8 - t₀ / ocTauPP α q Λ (m + 1) < 4 := by
      have : 4 < t₀ / ocTauPP α q Λ (m + 1) := by rw [lt_div_iff₀ hT]; linarith
      linarith
    have eρ : ρ' / ρ * ρ = ρ' := div_mul_cancel₀ ρ' hρ.ne'
    have et : t₁ - (8 - t₀ / ocTauPP α q Λ (m + 1)) * ocTauPP α q Λ (m + 1) =
        t₁ - 8 * ocTauPP α q Λ (m + 1) + t₀ := by
      rw [sub_mul, div_mul_cancel₀ t₀ hT.ne']; ring
    have h1 := hbound (ρ' / ρ) (8 - t₀ / ocTauPP α q Λ (m + 1)) hϱ hϱ8 hϑ0 hϑ4 t
      (by rw [et]; exact ht)
    rw [eρ] at h1
    exact h1

/-! ### Theorems A, B, C and Corollary D with one `Λ₀` -/

/-- **Theorem A** of the paper at `(Λ, b)` (it follows from this clause): the clause of
`Providers.oc_global` after the limit velocity `b`. -/
def PaperTheoremA (α s q : ℝ) (Λ : ℕ) (b : ℝ → Vec 2 → Vec 2) : Prop :=
  ∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∃ C : ℝ,
    ∀ a : ℝ, ∀ κ ∈ ocBandSet α q Λ, ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
    ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a (a + T) f θ →
      ∃ Θ : ℝ → Vec 2 → ℝ,
        ContinuousOn (fun p : ℝ × Vec 2 => Θ p.1 p.2)
          (Set.Icc (a + t₀) (a + T) ×ˢ Set.univ) ∧
        ∀ t ∈ Set.Icc (a + t₀) (a + T),
          IsZ2Periodic (Θ t) ∧ Θ t =ᵐ[volume.restrict unitCube] θ t ∧
          CsNormLe s (Θ t) (C * Real.sqrt (l2NormSq f))

/-- **Corollary D of the paper, global part** at `(Λ, Φ, b)` (Corollary D follows from it): the
clause of
`Providers.vanishing_diffusivity_limits` after the limit velocity `b`. -/
def PaperCorollaryDGlobal (α s q : ℝ) (Λ : ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
    (b : ℝ → Vec 2 → Vec 2) : Prop :=
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

/-- **Theorem B** of the paper at `(Λ, b)`: the clause of `oc_global_and_uniform_dissipation_exp`
after its Theorem A clause: uniform dissipation over unit time and exponential decay of the
variance. -/
def PaperTheoremB (α q : ℝ) (Λ : ℕ) (b : ℝ → Vec 2 → Vec 2) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    (∀ a : ℝ, ∀ κ ∈ ocBandSet α q Λ, ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
      ∀ θ : ℝ → Vec 2 → ℝ, ∀ Dθ : ℝ → Vec 2 → Vec 2,
        IsWeakSolutionOnWith b κ a (a + 1) f θ Dθ →
          c * l2NormSq (fun x => f x - ∫ y in unitCube, f y) ≤
            κ * ∫ p in Set.Ioo a (a + 1) ×ˢ unitCube, vecNormSq (Dθ p.1 p.2)) ∧
    (∀ a : ℝ, ∀ κ ∈ ocBandSet α q Λ, ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
      ∀ t : ℝ, a < t → ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a t f θ →
        l2NormSq (fun x => θ t x - ∫ y in unitCube, f y) ≤
          4 * Real.exp (-2 * c * (t - a)) *
            l2NormSq (fun x => f x - ∫ y in unitCube, f y))

/-- **Theorems A, B, C and Corollary D of the paper with one `Λ₀`**: for `Λ ≥ Λ₀` and the stream
sequence `Φ`, the limit velocity `b` of `b_M = ∇^⊥Φ_M` exists, is a bounded, periodic,
divergence-free `C^α` field, and satisfies Theorem A, Theorem C and Corollary D (local part)
(`PaperLocalResults`), Corollary D (global part) and Theorem B. -/
theorem paper_main_results (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
        ∃ b : ℝ → Vec 2 → Vec 2,
          (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) ∧
          IsHolderDivFreeVelocity α b ∧
          PaperTheoremA α s q Λ b ∧
          PaperLocalResults α s q Λ Φ b ∧
          PaperCorollaryDGlobal α s q Λ Φ b ∧
          PaperTheoremB α q Λ b := by
  obtain ⟨ΛAD, hAD128, hAD⟩ := oc_global_and_uniform_dissipation_exp α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨ΛL, -, hL⟩ := paper_local_results α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨ΛC, -, hC⟩ := Providers.vanishing_diffusivity_limits α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨max ΛAD (max ΛL ΛC), hAD128.trans (le_max_left _ _), fun Λ hΛ Φ hΦ => ?_⟩
  have hΛAD : ΛAD ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛL : ΛL ≤ Λ := ((le_max_left _ _).trans (le_max_right _ _)).trans hΛ
  have hΛC : ΛC ≤ Λ := ((le_max_right _ _).trans (le_max_right _ _)).trans hΛ
  obtain ⟨b, hb, hbH⟩ :=
    Velocity.exists_limit_velocity α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ (hAD128.trans hΛAD) Φ hΦ
  obtain ⟨bL, hbL, hLR⟩ := hL Λ hΛL Φ hΦ
  obtain ⟨bC, hbC, hCG⟩ := hC Λ hΛC Φ hΦ
  have hCG' : PaperCorollaryDGlobal α s q Λ Φ bC := hCG
  have hbL' : bL = b := funext fun t => funext fun x => tendsto_nhds_unique (hbL t x) (hb t x)
  have hbC' : bC = b := funext fun t => funext fun x => tendsto_nhds_unique (hbC t x) (hb t x)
  rw [hbL'] at hLR
  rw [hbC'] at hCG'
  have hADb := hAD Λ hΛAD Φ hΦ b hb
  exact ⟨b, hb, hbH, hADb.1, hLR, hCG', hADb.2⟩

end AVRegularity.PaperFacing
