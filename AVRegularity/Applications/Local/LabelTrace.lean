-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Definitions.IsLocalEnergySolution
import AVRegularity.Applications.Global.CompactRangeMain
public import AVRegularity.Statements.Construction.OcBandSet
public import AVRegularity.Applications.Pipe.PushTest
public import AVRegularity.Applications.Torus.JointContinuityMain
import AVenhance.Infra.Flow.StartTimeDerivative
import AVRegularity.Applications.Microscopic.Main
import AVRegularity.Applications.Tubes.Periodic
import AVRegularity.Applications.LocalEnergy.Mollifier
public import AVenhance.Infra.Flow.PeriodicSmooth
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Monotonicity.Lemmas

@[expose] public section
noncomputable section

section
namespace AVRegularity.Applications

/-! # Abstract-real bounds for the smoothing step of the local theorem

The factor `r^{-1-s} exp(-D/κ)` is bounded uniformly in `κ > 0` for the radius
`r = min {r₀, c κ^{1/(1+α)}, √(κ τ₀)}`, by `y^p e^{-y} ≤ C_p` (Step 4 of the proof of Theorem C
of the paper). -/

/-- `y^e e^{-y}` is bounded on `(0,∞)`. -/
theorem rpow_mul_exp_neg_le (e : ℝ) (he : 0 ≤ e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 < y → y ^ e * Real.exp (-y) ≤ C := by
  refine ⟨max 1 (Nat.factorial ⌈e⌉₊), by positivity, fun y hy => ?_⟩
  have hexp : 0 < Real.exp (-y) := Real.exp_pos _
  by_cases h1 : y ≤ 1
  · have : y ^ e ≤ 1 := Real.rpow_le_one hy.le h1 he
    have h2 : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    calc y ^ e * Real.exp (-y) ≤ 1 * 1 :=
          mul_le_mul this h2 hexp.le zero_le_one
      _ ≤ _ := by simp
  · push Not at h1
    have hN : y ^ e ≤ y ^ ((⌈e⌉₊ : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h1.le (Nat.le_ceil e)
    rw [Real.rpow_natCast] at hN
    have hfac := Real.pow_div_factorial_le_exp y hy.le ⌈e⌉₊
    have hfpos : (0 : ℝ) < Nat.factorial ⌈e⌉₊ := by exact_mod_cast Nat.factorial_pos _
    have h3 : y ^ ⌈e⌉₊ ≤ (Nat.factorial ⌈e⌉₊ : ℝ) * Real.exp y := by
      rwa [div_le_iff₀ hfpos, mul_comm] at hfac
    have h4 : y ^ e * Real.exp (-y) ≤ (Nat.factorial ⌈e⌉₊ : ℝ) := by
      calc y ^ e * Real.exp (-y) ≤ ((Nat.factorial ⌈e⌉₊ : ℝ) * Real.exp y) * Real.exp (-y) :=
            mul_le_mul_of_nonneg_right (hN.trans h3) hexp.le
        _ = (Nat.factorial ⌈e⌉₊ : ℝ) := by
            rw [mul_assoc, ← Real.exp_add]; simp
    exact h4.trans (le_max_right _ _)

/-- `κ^{-e} e^{-D/κ}` is bounded on `(0,∞)`. -/
theorem rpow_neg_mul_exp_le (e D : ℝ) (he : 0 ≤ e) (hD : 0 < D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ κ : ℝ, 0 < κ → κ ^ (-e) * Real.exp (-(D / κ)) ≤ C := by
  obtain ⟨C₀, hC₀, h⟩ := rpow_mul_exp_neg_le e he
  refine ⟨C₀ / D ^ e, by positivity, fun κ hκ => ?_⟩
  have hy : 0 < D / κ := by positivity
  have hk : κ ^ (-e) = (D / κ) ^ e / D ^ e := by
    rw [← Real.div_rpow hy.le hD.le, Real.rpow_neg hκ.le]
    have h1 : D / κ / D = κ⁻¹ := by field_simp
    rw [h1, Real.inv_rpow hκ.le]
  rw [hk, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right (h _ hy) (Real.rpow_nonneg hD.le e)

/-- The radius of the smoothing step. -/
def smoothRadius (α r₀ c τ₀ κ : ℝ) : ℝ :=
  min r₀ (min (c * κ ^ (1 / (1 + α))) (Real.sqrt (κ * τ₀)))

theorem smoothRadius_pos {α r₀ c τ₀ κ : ℝ} (hr₀ : 0 < r₀) (hc : 0 < c) (hτ : 0 < τ₀)
    (hκ : 0 < κ) : 0 < smoothRadius α r₀ c τ₀ κ := by
  unfold smoothRadius
  exact lt_min hr₀ (lt_min (by positivity) (Real.sqrt_pos.2 (by positivity)))

/-- **Uniform bound for the radius factor** (Step 4 of the proof of Theorem C of the paper). -/
theorem smoothRadius_bound {α s r₀ c τ₀ D : ℝ} (hα : 0 < α) (hs : 0 < s) (hr₀ : 0 < r₀)
    (hc : 0 < c) (hτ : 0 < τ₀) (hD : 0 < D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ κ : ℝ, 0 < κ →
      smoothRadius α r₀ c τ₀ κ ^ (-1 - s) * Real.exp (-(D / κ)) ≤ C := by
  obtain ⟨C₁, hC₁, h₁⟩ := rpow_neg_mul_exp_le ((1 + s) / (1 + α)) D (by positivity) hD
  obtain ⟨C₂, hC₂, h₂⟩ := rpow_neg_mul_exp_le ((1 + s) / 2) D (by positivity) hD
  refine ⟨r₀ ^ (-1 - s) + c ^ (-1 - s) * C₁ + τ₀ ^ (-(1 + s) / 2) * C₂,
    by positivity, fun κ hκ => ?_⟩
  have hex : 0 < Real.exp (-(D / κ)) := Real.exp_pos _
  have hex1 : Real.exp (-(D / κ)) ≤ 1 := Real.exp_le_one_iff.2 (by
    have : 0 < D / κ := by positivity
    linarith)
  have hr := smoothRadius_pos (α := α) hr₀ hc hτ hκ
  have ha : (0 : ℝ) < c * κ ^ (1 / (1 + α)) := by positivity
  have hb : (0 : ℝ) < Real.sqrt (κ * τ₀) := Real.sqrt_pos.2 (by positivity)
  -- the values of `r^{-1-s}` at the three terms of the minimum
  have hT1 : r₀ ^ (-1 - s) * Real.exp (-(D / κ)) ≤ r₀ ^ (-1 - s) :=
    mul_le_of_le_one_right (Real.rpow_nonneg hr₀.le _) hex1
  have hT2 : (c * κ ^ (1 / (1 + α))) ^ (-1 - s) * Real.exp (-(D / κ)) ≤ c ^ (-1 - s) * C₁ := by
    have : (c * κ ^ (1 / (1 + α))) ^ (-1 - s) = c ^ (-1 - s) * κ ^ (-((1 + s) / (1 + α))) := by
      rw [Real.mul_rpow hc.le (Real.rpow_nonneg hκ.le _), ← Real.rpow_mul hκ.le]
      congr 2
      field_simp
      ring
    rw [this, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h₁ κ hκ) (Real.rpow_nonneg hc.le _)
  have hT3 : (Real.sqrt (κ * τ₀)) ^ (-1 - s) * Real.exp (-(D / κ)) ≤
      τ₀ ^ (-(1 + s) / 2) * C₂ := by
    have : (Real.sqrt (κ * τ₀)) ^ (-1 - s) = τ₀ ^ (-(1 + s) / 2) * κ ^ (-((1 + s) / 2)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity),
        Real.mul_rpow hκ.le hτ.le, mul_comm]
      congr 2 <;> ring
    rw [this, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h₂ κ hκ) (Real.rpow_nonneg hτ.le _)
  have hnn1 : 0 ≤ r₀ ^ (-1 - s) * Real.exp (-(D / κ)) := by positivity
  have hnn2 : 0 ≤ (c * κ ^ (1 / (1 + α))) ^ (-1 - s) * Real.exp (-(D / κ)) := by positivity
  have hnn3 : 0 ≤ (Real.sqrt (κ * τ₀)) ^ (-1 - s) * Real.exp (-(D / κ)) := by positivity
  unfold smoothRadius
  rcases min_choice r₀ (min (c * κ ^ (1 / (1 + α))) (Real.sqrt (κ * τ₀))) with h | h
  · rw [h]; linarith
  · rw [h]
    rcases min_choice (c * κ ^ (1 / (1 + α))) (Real.sqrt (κ * τ₀)) with h' | h'
    · rw [h']; linarith
    · rw [h']; linarith


/-- Properties of the smoothing radius used for the containment of tubes. -/
theorem smoothRadius_props {α r₀ c τ₀ V₁ d κ : ℝ} (hr₀ : 0 < r₀) (hr₀d : r₀ ≤ d / 4)
    (hr₀8 : r₀ ≤ 1 / 8) (hc : 0 < c) (hτ₀ : 0 < τ₀) (hτd : τ₀ ≤ d / (12 * (1 + V₁)))
    (hV₁ : 0 ≤ V₁) (hκ : 0 < κ) :
    smoothRadius α r₀ c τ₀ κ ≤ 1 / 8 ∧
      smoothRadius α r₀ c τ₀ κ ≤ c * κ ^ (1 / (1 + α)) ∧
      smoothRadius α r₀ c τ₀ κ ^ 2 / κ ≤ τ₀ ∧
      2 * smoothRadius α r₀ c τ₀ κ + 6 * V₁ * (smoothRadius α r₀ c τ₀ κ ^ 2 / κ) ≤ d := by
  have hr := smoothRadius_pos (α := α) (κ := κ) hr₀ hc hτ₀ hκ
  have h1 : smoothRadius α r₀ c τ₀ κ ≤ r₀ := min_le_left _ _
  have h2 : smoothRadius α r₀ c τ₀ κ ≤ c * κ ^ (1 / (1 + α)) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have h3 : smoothRadius α r₀ c τ₀ κ ≤ Real.sqrt (κ * τ₀) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have h4 : smoothRadius α r₀ c τ₀ κ ^ 2 / κ ≤ τ₀ := by
    rw [div_le_iff₀ hκ]
    calc smoothRadius α r₀ c τ₀ κ ^ 2 ≤ Real.sqrt (κ * τ₀) ^ 2 :=
          pow_le_pow_left₀ hr.le h3 2
      _ = κ * τ₀ := Real.sq_sqrt (by positivity)
      _ = τ₀ * κ := mul_comm _ _
  refine ⟨h1.trans hr₀8, h2, h4, ?_⟩
  have h5 : 6 * V₁ * (smoothRadius α r₀ c τ₀ κ ^ 2 / κ) ≤ d / 2 := by
    have h6 : 6 * V₁ * τ₀ ≤ d / 2 := by
      have h7 : τ₀ * (12 * (1 + V₁)) ≤ d := by
        rwa [le_div_iff₀ (by positivity)] at hτd
      nlinarith
    calc 6 * V₁ * (smoothRadius α r₀ c τ₀ κ ^ 2 / κ) ≤ 6 * V₁ * τ₀ :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ ≤ d / 2 := h6
  linarith


/-- Elementary time arithmetic of the window `[t₁ - ϑT, t₁)` relative to `s₀ = t₁ - 9T/2`. -/
theorem window_arith {t₁ T ϑ t h τ₀ : ℝ} (hT : 0 < T) (hϑ : ϑ < 4) (ht : t₁ - ϑ * T ≤ t)
    (hh : h ≤ τ₀) (hτ : τ₀ ≤ (4 - ϑ) * T / 2) : t₁ - 9 * T / 2 < t - h := by
  have h5 : 0 < (4 - ϑ) * T := mul_pos (by linarith) hT
  nlinarith only [hT, h5, ht, hh, hτ]

theorem window_arith₂ {t₁ T ϑ t : ℝ} (hT : 0 < T) (ht : t₁ - ϑ * T ≤ t) :
    t₁ - 9 * T / 2 + (4 - ϑ) * T < t := by
  nlinarith only [hT, ht]

theorem window_arith₃ {t₁ T ϑ t : ℝ} (hT : 0 < T) (hϑ : ϑ < 4) (ht : t₁ - ϑ * T ≤ t) :
    t₁ - 8 * T < t := by
  have h5 : 0 < (4 - ϑ) * T := mul_pos (by linarith) hT
  nlinarith only [hT, h5, ht]

/-- Geometry of the radii `ϱR < ϱ'R < R/8`. -/
theorem pipe_numerics {R ϱ : ℝ} (hR : 0 < R) (hR8 : R ≤ 1 / 8) (hϱ : 0 < ϱ) (hϱ8 : ϱ < 1 / 8) :
    0 < (1 / 8 - ϱ) * R / 2 ∧ ϱ * R < (ϱ + 1 / 8) / 2 * R ∧
      R / 8 - (ϱ + 1 / 8) / 2 * R = (1 / 8 - ϱ) * R / 2 ∧ ϱ * R ≤ 1 / 4 ∧ ϱ * R ≤ R := by
  have h1 : 0 < 1 / 8 - ϱ := by linarith
  refine ⟨by positivity, ?_, by ring, ?_, ?_⟩
  · nlinarith only [hR, hϱ8]
  · nlinarith only [hR, hR8, hϱ, hϱ8]
  · nlinarith only [hR, hϱ8]

end AVRegularity.Applications
end

section
open MeasureTheory Filter Topology Homogenization AVenhance
namespace AVRegularity.Applications

/-! # Interfaces of the proof of the local theorem

The proof of the local theorem (Theorem C of the paper) has three analytic inputs, stated here
as propositions about the fixed construction and velocity `b`, and proved in their own modules:

* `DaviesStmt`: the localization lemma (cutoff comparison with a torus solution,
  exponential separation on the inner label ball `B_{R/8}` after `s₀ = t₁ - 9T/2`);
* `PhysLiftStmt`: the difference `θ - u_f` is a physical local weak solution in the comparison
  pipe `{(ℓ, F_ℓ y) : s₀ < ℓ < t₁, |y| < R/8}`;
* `LocalTraceStmt`: the pulled-back slices have local `L²` traces from below,
  including at the top time `t₁`. -/

/-- The comparison pipe `{(ℓ, X ℓ y t₁) : s₀ < ℓ < t₁, |y| < ρ}`. -/
def innerPipeO (X : ℝ → Vec 2 → ℝ → Vec 2) (t₁ s₀ ρ : ℝ) : Set (ℝ × Vec 2) :=
  {p | s₀ < p.1 ∧ p.1 < t₁ ∧ ∃ y ∈ euclidBall 0 ρ, p.2 = X p.1 y t₁}

/-- The normalized amplitude `A = (|𝒫_out|⁻¹ ∬_{𝒫_out} θ²)^{1/2}` of the local theorem. -/
def pipeAmp (X : ℝ → Vec 2 → ℝ → Vec 2) (t₁ T R : ℝ) (θ : ℝ → Vec 2 → ℝ) : ℝ :=
  Real.sqrt ((volume (outerPipe (fun t y => X t y t₁) t₁ T R)).toReal⁻¹ *
    ∫ p in outerPipe (fun t y => X t y t₁) t₁ T R, θ p.1 p.2 ^ 2)

/-- **Statement of the localization lemma** for the construction `(α, q, Λ, Φ)` with limit
velocity `b` (Lemma 8.3 of the paper follows from it). The buffer constant `Cb` and the constants
`C, c` are fixed before the pipe data, the diffusivity and the solution. -/
def DaviesStmt (α q : ℝ) (Λ : ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (b : ℝ → Vec 2 → Vec 2) : Prop :=
  ∃ Cb C c : ℝ, 0 < Cb ∧ 0 ≤ C ∧ 0 < c ∧
    ∀ n : ℕ, 2 ≤ n → ∀ X : ℝ → Vec 2 → ℝ → Vec 2, IsFlow (streamVel (Φ (n - 2))) X →
    ∀ t₁ T R κ : ℝ, 0 < T → 0 < R → R ≤ 1 / 8 → 0 < κ →
      8 * T * ocA α q Λ (n - 2) ≤ ocCStar →
      Cb * (ocEpsilon q Λ (n - 1) ^ α * T) ≤ R → Cb * Real.sqrt (κ * T) ≤ R →
    ∀ θ : ℝ → Vec 2 → ℝ, IsLocalEnergySolution b κ (fun t y => X t y t₁) t₁ T R θ →
    ∃ f : Vec 2 → ℝ, MemL2On unitCube f ∧
      Real.sqrt (l2NormSq f) ≤ C * R * pipeAmp X t₁ T R θ ∧
      ∀ u : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ (t₁ - 9 * T / 2) (t₁ - 9 * T / 2 + 5 * T) f u →
        ∀ᵐ t ∂(volume.restrict (Set.Ioo (t₁ - 9 * T / 2) t₁)),
          ∫ y in euclidBall 0 (R / 8), (θ t (X t y t₁) - u t (X t y t₁)) ^ 2 ≤
            (C * R * pipeAmp X t₁ T R θ * Real.exp (-c * R ^ 2 / (κ * T))) ^ 2

/-- **Physical form of the difference**: for a local energy solution `θ` and a torus energy
solution `u` from `s₀ = t₁ - 9T/2`, `θ - u` is a local weak solution (in the physical sense of
`IsLocalWeakSolution`) in the comparison pipe of material radius `R/8`. -/
def PhysLiftStmt (α q : ℝ) (Λ : ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (b : ℝ → Vec 2 → Vec 2) : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ X : ℝ → Vec 2 → ℝ → Vec 2, IsFlow (streamVel (Φ (n - 2))) X →
  ∀ t₁ T R κ : ℝ, 0 < T → 0 < R → R ≤ 1 / 8 → 0 < κ →
    8 * T * ocA α q Λ (n - 2) ≤ ocCStar →
  ∀ θ : ℝ → Vec 2 → ℝ, IsLocalEnergySolution b κ (fun t y => X t y t₁) t₁ T R θ →
  ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
  ∀ u : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ (t₁ - 9 * T / 2) (t₁ - 9 * T / 2 + 5 * T) f u →
    ∃ Dw : ℝ × Vec 2 → Vec 2,
      IsLocalWeakSolution b κ (innerPipeO X t₁ (t₁ - 9 * T / 2) (R / 8))
        (fun p => θ p.1 p.2 - u p.1 p.2) Dw

/-- **Local traces from below** of the pulled-back slices `U(t) = θ(t, F_t ·)` on label balls
`B_ρ`, `ρ < R`, at every `t ∈ (t₁ - 6T, t₁]`, the top time included. -/
def LocalTraceStmt (α q : ℝ) (Λ : ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (b : ℝ → Vec 2 → Vec 2) : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ X : ℝ → Vec 2 → ℝ → Vec 2, IsFlow (streamVel (Φ (n - 2))) X →
  ∀ t₁ T R κ : ℝ, 0 < T → 0 < R → R ≤ 1 / 8 → 0 < κ →
    8 * T * ocA α q Λ (n - 2) ≤ ocCStar →
  ∀ θ : ℝ → Vec 2 → ℝ, IsLocalEnergySolution b κ (fun t y => X t y t₁) t₁ T R θ →
  ∀ ρ : ℝ, 0 < ρ → ρ < R → ∀ t ∈ Set.Ioc (t₁ - 6 * T) t₁,
    ∃ Ut : Vec 2 → ℝ, MemL2On (euclidBall 0 ρ) Ut ∧
      Tendsto (fun r => ∫ y in euclidBall 0 ρ, (θ r (X r y t₁) - Ut y) ^ 2)
        (𝓝[<] t ⊓ ae volume) (𝓝 0)

end AVRegularity.Applications
end

section
namespace AVRegularity.Applications

/-! # The permitted diffusivities are positive and bounded

`𝒦 ⊆ (0, 2]`: every band `[ε_M^e/2, 2 ε_M^e]` has `e = (1+α) - γ > 0` and `0 < ε_M ≤ 1`.
Hence `κ_max = sSup 𝒦` is a genuine upper bound of `𝒦`. -/

theorem band_exponent_pos {α q : ℝ} (hα : 0 < α) (hq : 1 < q) : 0 < (1 + α) - ocGamma α q := by
  simp only [ocGamma]
  have hq0 : 0 < q + 1 := by linarith
  have heq : (1 + α) - (q - 1) * (1 + α) / (q + 1) = 2 * (1 + α) / (q + 1) := by
    rw [eq_div_iff hq0.ne', sub_mul, div_mul_cancel₀ _ hq0.ne']; ring
  rw [heq]; positivity

theorem band_pos_le_two {α q : ℝ} {Λ : ℕ} (hα : 0 < α) (hq : 1 < q) (hΛ : 128 ≤ Λ) {κ : ℝ}
    (hκ : κ ∈ ocBandSet α q Λ) : 0 < κ ∧ κ ≤ 2 := by
  simp only [ocBandSet, Set.mem_iUnion] at hκ
  obtain ⟨M, hM, hκ⟩ := hκ
  have he := band_exponent_pos hα hq
  have hε := eps_pos (m := M) hq hΛ
  have h1 : ocEpsilon q Λ M ^ ((1 + α) - ocGamma α q) ≤ 1 :=
    Real.rpow_le_one hε.le (eps_le_one hq hΛ) he.le
  have h2 : 0 < ocEpsilon q Λ M ^ ((1 + α) - ocGamma α q) := Real.rpow_pos_of_pos hε _
  exact ⟨lt_of_lt_of_le (by positivity) hκ.1, by linarith [hκ.2]⟩

theorem band_bddAbove {α q : ℝ} {Λ : ℕ} (hα : 0 < α) (hq : 1 < q) (hΛ : 128 ≤ Λ) :
    BddAbove (ocBandSet α q Λ) :=
  ⟨2, fun _ hκ => (band_pos_le_two hα hq hΛ hκ).2⟩

theorem band_le_sSup {α q : ℝ} {Λ : ℕ} (hα : 0 < α) (hq : 1 < q) (hΛ : 128 ≤ Λ) {κ : ℝ}
    (hκ : κ ∈ ocBandSet α q Λ) : κ ≤ sSup (ocBandSet α q Λ) :=
  le_csSup (band_bddAbove hα hq hΛ) hκ

end AVRegularity.Applications
end

section
open MeasureTheory Homogenization AVenhance AVRegularity Set
namespace AVRegularity.Applications

/-! # Translating tubes stay in the comparison pipe (Step 3 of the proof of Theorem C of the paper)

For a backward trajectory `X̃` of `b` and the material
label `Y(ℓ) = F_ℓ⁻¹(X̃(ℓ))`, `Y' = (D H_ℓ)(b - b₀)(ℓ, X̃(ℓ))`; hence `Y` moves with speed at most
`3 V₁` (sup norm) where `V₁` bounds `|b - b₀|`. Together with the `2`-Lipschitz bound of `H_ℓ`
this puts every closed translating tube of small radius and duration inside
`innerPipeO X t₁ s₀ ρ`. -/

section Chart

variable {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T : ℝ}

/-- Chain rule for the label path `Y(τ) = X t₁ (X̃ τ) τ`. -/
theorem hasDerivWithinAt_labelPath (hb0 : AVenhance.Infra.Flow.SmoothPeriodicField b0)
    (ch : IsPipeChart b0 X t₁ T) {Xt : ℝ → Vec 2} {S : Set ℝ} {ℓ : ℝ} {v : Vec 2}
    (hX : HasDerivWithinAt Xt v S ℓ) :
    HasDerivWithinAt (fun τ => X t₁ (Xt τ) τ)
      (fderiv ℝ (fun z => X t₁ z ℓ) (Xt ℓ) (v - b0 ℓ (Xt ℓ))) S ℓ := by
  set Ψ : ℝ × Vec 2 → Vec 2 := fun p => X t₁ p.2 p.1 with hΨ
  have hΨd : HasFDerivAt Ψ (fderiv ℝ Ψ (ℓ, Xt ℓ)) (ℓ, Xt ℓ) :=
    ((ch.smoothH.differentiable (by simp)) _).hasFDerivAt
  have hcurve : HasDerivWithinAt (fun τ => (τ, Xt τ)) ((1 : ℝ), v) S ℓ :=
    (hasDerivAt_id ℓ).hasDerivWithinAt.prodMk hX
  have h1 := hΨd.comp_hasDerivWithinAt_of_eq ℓ hcurve rfl
  -- partial derivative in time
  have htime : HasDerivAt (fun r => X t₁ (Xt ℓ) r)
      (fderiv ℝ Ψ (ℓ, Xt ℓ) ((1 : ℝ), (0 : Vec 2))) ℓ := by
    have hc : HasDerivAt (fun r : ℝ => (r, Xt ℓ)) ((1 : ℝ), (0 : Vec 2)) ℓ :=
      (hasDerivAt_id ℓ).prodMk (hasDerivAt_const ℓ (Xt ℓ))
    exact hΨd.comp_hasDerivAt_of_eq ℓ hc rfl
  have htime' := AVenhance.Infra.Flow.flow_initialTime_hasDerivAt hb0 ch.flow (Xt ℓ) ℓ t₁
  have hu := htime.unique htime'
  -- partial derivative in space
  have hspace : fderiv ℝ (fun z => X t₁ z ℓ) (Xt ℓ) =
      (fderiv ℝ Ψ (ℓ, Xt ℓ)).comp (ContinuousLinearMap.inr ℝ ℝ (Vec 2)) := by
    have := hΨd.comp (Xt ℓ) (hasFDerivAt_prodMk_right ℓ (Xt ℓ))
    exact this.fderiv
  have hsplit : ((1 : ℝ), v) = ((1 : ℝ), (0 : Vec 2)) + ((0 : ℝ), v) := by simp
  have hval : fderiv ℝ Ψ (ℓ, Xt ℓ) ((1 : ℝ), v) =
      fderiv ℝ (fun z => X t₁ z ℓ) (Xt ℓ) (v - b0 ℓ (Xt ℓ)) := by
    rw [hsplit, map_add, hu, hspace, map_sub]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
    abel
  rw [← hval]
  exact h1

theorem eNorm_le_of_vecNormSq_le {v : Vec 2} {r : ℝ} (hr : 0 ≤ r) (h : vecNormSq v ≤ r ^ 2) :
    eNorm v ≤ r := by
  unfold eNorm
  exact Real.sqrt_le_iff.2 ⟨hr, h⟩

theorem vecNormSq_lt_of_eNorm_lt {v : Vec 2} {r : ℝ} (h : eNorm v < r) :
    vecNormSq v < r ^ 2 := by
  unfold eNorm at h
  exact (Real.sqrt_lt' (lt_of_le_of_lt (Real.sqrt_nonneg _) h)).1 h

theorem eNorm_lt_of_vecNormSq_lt {v : Vec 2} {r : ℝ} (hr : 0 ≤ r) (h : vecNormSq v < r ^ 2) :
    eNorm v < r := by
  unfold eNorm
  have := Real.sqrt_lt_sqrt (vecNormSq_nonneg v) h
  rwa [Real.sqrt_sq hr] at this

/-- `‖v‖ ≤ |v|_E ≤ 2‖v‖`. -/
theorem eNorm_le_two_mul_norm (v : Vec 2) : eNorm v ≤ 2 * ‖v‖ :=
  sqrt_vecNormSq_le_two_mul_norm v

theorem norm_le_eNorm' (v : Vec 2) : ‖v‖ ≤ eNorm v := norm_le_sqrt_vecNormSq v

/-- The derivative of the inverse chart moves vectors by at most the factor `3/2`. -/
theorem eNorm_chart_fderiv_le {D : Vec 2 →L[ℝ] Vec 2}
    (hD : ∀ v, vecNormSq (D v - v) ≤ (1 / 4) * vecNormSq v) (v : Vec 2) :
    eNorm (D v) ≤ (3 / 2) * eNorm v := by
  have h1 : eNorm (D v - v) ≤ (1 / 2) * eNorm v := by
    unfold eNorm
    have h := Real.sqrt_le_sqrt (hD v)
    rw [Real.sqrt_mul (by norm_num)] at h
    have h2 : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rwa [h2] at h
  have h3 := eNorm_add_le (D v - v) v
  rw [sub_add_cancel] at h3
  linarith

theorem hLip_label (ch : IsPipeChart b0 X t₁ T) {ℓ : ℝ} (hℓ : ℓ ∈ Icc (t₁ - 8 * T) t₁)
    (y z : Vec 2) : eNorm (X t₁ y ℓ - X t₁ z ℓ) ≤ 2 * eNorm (y - z) := by
  have hd : Differentiable ℝ (fun w : Vec 2 => X t₁ w ℓ) :=
    (ch.smoothH.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  exact euclid_lipschitz_of_fderiv_close hd (ch.closeInv ℓ hℓ) y z

theorem hLip_chart (ch : IsPipeChart b0 X t₁ T) {ℓ : ℝ} (hℓ : ℓ ∈ Icc (t₁ - 8 * T) t₁)
    (y z : Vec 2) : eNorm (X ℓ y t₁ - X ℓ z t₁) ≤ 2 * eNorm (y - z) := by
  have hd : Differentiable ℝ (fun w : Vec 2 => X ℓ w t₁) :=
    (ch.smoothF.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  exact euclid_lipschitz_of_fderiv_close hd (ch.close ℓ hℓ) y z

/-- **Tube containment.** -/
theorem closedTube_subset_innerPipeO (hb0 : AVenhance.Infra.Flow.SmoothPeriodicField b0)
    (ch : IsPipeChart b0 X t₁ T) {b : ℝ → Vec 2 → Vec 2} {V₁ : ℝ}
    (hV : ∀ τ z, ‖b τ z - b0 τ z‖ ≤ V₁) {s₀ ρin ρout t r κ : ℝ} (hs₀ : t₁ - 8 * T ≤ s₀)
    (hκ : 0 < κ) (hr : 0 < r)
    (hd : 2 * r + 6 * V₁ * (r ^ 2 / κ) ≤ ρout - ρin) (htl : s₀ < t - r ^ 2 / κ) (ht1 : t < t₁)
    {y : Vec 2} (hy : vecNormSq y < ρin ^ 2) (hρin : 0 ≤ ρin) {Xt : ℝ → Vec 2}
    (hXt : IsBackwardTrajectory b Xt t (r ^ 2 / κ)) (hXt0 : Xt t = X t y t₁) :
    closedTube Xt t r κ ⊆ innerPipeO X t₁ s₀ ρout := by
  set h : ℝ := r ^ 2 / κ with hh
  have hh0 : 0 ≤ h := by positivity
  have hV0 : 0 ≤ V₁ := (norm_nonneg _).trans (hV 0 0)
  have hwin : ∀ ℓ ∈ Icc (t - h) t, ℓ ∈ Icc (t₁ - 8 * T) t₁ := fun ℓ hℓ =>
    ⟨by linarith [hℓ.1], by linarith [hℓ.2]⟩
  -- the label path
  set Y : ℝ → Vec 2 := fun τ => X t₁ (Xt τ) τ with hY
  have hYd : ∀ τ ∈ Icc (t - h) t, HasDerivWithinAt Y
      (fderiv ℝ (fun z => X t₁ z τ) (Xt τ) (b τ (Xt τ) - b0 τ (Xt τ))) (Icc (t - h) t) τ :=
    fun τ hτ => hasDerivWithinAt_labelPath hb0 ch (hXt τ hτ)
  have hYb : ∀ τ ∈ Icc (t - h) t,
      ‖fderiv ℝ (fun z => X t₁ z τ) (Xt τ) (b τ (Xt τ) - b0 τ (Xt τ))‖ ≤ 3 * V₁ := by
    intro τ hτ
    have h1 := eNorm_chart_fderiv_le (D := fderiv ℝ (fun z => X t₁ z τ) (Xt τ))
      (ch.closeInv τ (hwin τ hτ) (Xt τ)) (b τ (Xt τ) - b0 τ (Xt τ))
    have h2 := eNorm_le_two_mul_norm (b τ (Xt τ) - b0 τ (Xt τ))
    have h3 := norm_le_eNorm' (fderiv ℝ (fun z => X t₁ z τ) (Xt τ) (b τ (Xt τ) - b0 τ (Xt τ)))
    have h4 := hV τ (Xt τ)
    linarith
  have hYt : Y t = y := by
    simp only [hY, hXt0]
    exact ch.left t (hwin t ⟨by linarith, le_rfl⟩) y
  intro p hp
  obtain ⟨⟨hp1, hp2⟩, hp3⟩ := hp
  have hp1 : t - h ≤ p.1 := hp1
  have hpl : s₀ < p.1 := by linarith [hp1]
  have hpt : p.1 < t₁ := by linarith [hp2]
  have hpw : p.1 ∈ Icc (t₁ - 8 * T) t₁ := ⟨by linarith, hpt.le⟩
  refine ⟨hpl, hpt, X t₁ p.2 p.1, ?_, (ch.right p.1 hpw p.2).symm⟩
  -- estimate `|H_ℓ p.2|`
  have hmv : ‖Y p.1 - Y t‖ ≤ 3 * V₁ * ‖p.1 - t‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := Y)
      (f' := fun τ => fderiv ℝ (fun z => X t₁ z τ) (Xt τ) (b τ (Xt τ) - b0 τ (Xt τ)))
      (s := Icc (t - h) t) hYd hYb (convex_Icc _ _) ⟨by linarith, le_rfl⟩ ⟨hp1, hp2⟩
  have hdrift : eNorm (Y p.1 - y) ≤ 6 * V₁ * h := by
    have h1 := eNorm_le_two_mul_norm (Y p.1 - y)
    rw [← hYt] at h1 ⊢
    have h2 : ‖p.1 - t‖ ≤ h := by
      rw [Real.norm_eq_abs, abs_of_nonpos (by linarith [hp2])]
      linarith [hp1]
    have : 3 * V₁ * ‖p.1 - t‖ ≤ 3 * V₁ * h := mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  have hlip : eNorm (X t₁ p.2 p.1 - Y p.1) ≤ 2 * r := by
    have h1 := hLip_label ch hpw p.2 (Xt p.1)
    have h2 : eNorm (p.2 - Xt p.1) ≤ r := eNorm_le_of_vecNormSq_le hr.le hp3
    simp only [hY]
    linarith
  have hyn : eNorm y < ρin := eNorm_lt_of_vecNormSq_lt hρin hy
  have htot : eNorm (X t₁ p.2 p.1) < ρout := by
    have h1 : X t₁ p.2 p.1 = (X t₁ p.2 p.1 - Y p.1) + (Y p.1 - y) + y := by abel
    have h2 := eNorm_add_le ((X t₁ p.2 p.1 - Y p.1) + (Y p.1 - y)) y
    have h3 := eNorm_add_le (X t₁ p.2 p.1 - Y p.1) (Y p.1 - y)
    rw [h1]
    linarith
  have hρout : 0 ≤ ρout := (eNorm_nonneg _).trans htot.le
  have := vecNormSq_lt_of_eNorm_lt htot
  simpa [euclidBall] using this

end Chart

end AVRegularity.Applications
end

section
open MeasureTheory Filter Topology Homogenization AVenhance AVRegularity Set
namespace AVRegularity.Applications

/-! # The comparison pipe `𝒪` and its time sections

`𝒪 = innerPipeO X t₁ s₀ ρ` is open, its time section at `τ ∈ (s₀, t₁)` is `F_τ(B_ρ)` and empty
otherwise, and (by measure preservation of `F_τ`) integrals over the section are integrals over
the label ball of the pulled-back function. This turns the Davies bound on label balls into the
`L²` bound on time sections used by `tube_regularity`. -/

section
variable {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T : ℝ}

theorem mem_innerPipeO_iff (ch : IsPipeChart b0 X t₁ T) {s₀ ρ : ℝ} (hs₀ : t₁ - 8 * T ≤ s₀)
    (p : ℝ × Vec 2) :
    p ∈ innerPipeO X t₁ s₀ ρ ↔ s₀ < p.1 ∧ p.1 < t₁ ∧ X t₁ p.2 p.1 ∈ euclidBall 0 ρ := by
  constructor
  · rintro ⟨h1, h2, y, hy, hp⟩
    have hw : p.1 ∈ Icc (t₁ - 8 * T) t₁ := ⟨by linarith, h2.le⟩
    refine ⟨h1, h2, ?_⟩
    rw [hp, ch.left p.1 hw y]
    exact hy
  · rintro ⟨h1, h2, h3⟩
    have hw : p.1 ∈ Icc (t₁ - 8 * T) t₁ := ⟨by linarith, h2.le⟩
    exact ⟨h1, h2, _, h3, (ch.right p.1 hw p.2).symm⟩

theorem isOpen_innerPipeO (ch : IsPipeChart b0 X t₁ T) {s₀ ρ : ℝ} (hs₀ : t₁ - 8 * T ≤ s₀) :
    IsOpen (innerPipeO X t₁ s₀ ρ) := by
  have hset : innerPipeO X t₁ s₀ ρ = {p : ℝ × Vec 2 | s₀ < p.1} ∩ ({p | p.1 < t₁} ∩
      (fun p : ℝ × Vec 2 => X t₁ p.2 p.1) ⁻¹' euclidBall 0 ρ) := by
    ext p
    rw [mem_innerPipeO_iff ch hs₀]
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage]
  rw [hset]
  have hc : Continuous fun p : ℝ × Vec 2 => X t₁ p.2 p.1 := ch.smoothH.continuous
  have hball : IsOpen (euclidBall (0 : Vec 2) ρ) := by
    have hcont : Continuous (fun x : Vec 2 => vecNormSq (x - 0)) := by
      unfold vecNormSq vecDot; fun_prop
    exact isOpen_lt hcont continuous_const
  exact (isOpen_lt continuous_const continuous_fst).inter
    ((isOpen_lt continuous_fst continuous_const).inter (hball.preimage hc))

theorem timeSection_innerPipeO_of_mem {s₀ ρ τ : ℝ} (hτ : τ ∈ Ioo s₀ t₁) :
    timeSection (innerPipeO X t₁ s₀ ρ) τ = (fun y => X τ y t₁) '' euclidBall 0 ρ := by
  ext x
  simp only [timeSection, innerPipeO, mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨-, -, y, hy, hx⟩
    exact ⟨y, hy, hx.symm⟩
  · rintro ⟨y, hy, hx⟩
    exact ⟨hτ.1, hτ.2, y, hy, hx.symm⟩

theorem timeSection_innerPipeO_of_notMem {s₀ ρ τ : ℝ} (hτ : τ ∉ Ioo s₀ t₁) :
    timeSection (innerPipeO X t₁ s₀ ρ) τ = ∅ := by
  ext x
  simp only [timeSection, innerPipeO, mem_ofPred_eq, mem_empty_iff_false, iff_false]
  rintro ⟨h1, h2, -⟩
  exact hτ ⟨h1, h2⟩

theorem isOpen_euclidBall' (c : Vec 2) (ρ : ℝ) : IsOpen (euclidBall c ρ) := by
  have hcont : Continuous (fun x : Vec 2 => vecNormSq (x - c)) := by
    unfold vecNormSq vecDot; fun_prop
  exact isOpen_lt hcont continuous_const

/-- The chart `F_τ` is a measure preserving measurable embedding. -/
theorem chart_mp_emb (ch : IsPipeChart b0 X t₁ T) {τ : ℝ} (hτ : τ ∈ Icc (t₁ - 8 * T) t₁) :
    MeasurePreserving (fun y => X τ y t₁) volume volume ∧
      MeasurableEmbedding (fun y => X τ y t₁) :=
  ⟨ch.mp τ hτ, (chartHomeo ch hτ).measurableEmbedding⟩

theorem section_integral_eq (ch : IsPipeChart b0 X t₁ T) {τ : ℝ} (hτ : τ ∈ Icc (t₁ - 8 * T) t₁)
    (g : Vec 2 → ℝ) (B : Set (Vec 2)) :
    ∫ x in (fun y => X τ y t₁) '' B, g x = ∫ y in B, g (X τ y t₁) := by
  obtain ⟨hmp, hemb⟩ := chart_mp_emb ch hτ
  exact hmp.setIntegral_image_emb hemb g B

theorem section_integrableOn_iff (ch : IsPipeChart b0 X t₁ T) {τ : ℝ}
    (hτ : τ ∈ Icc (t₁ - 8 * T) t₁) (g : Vec 2 → ℝ) (B : Set (Vec 2)) :
    IntegrableOn g ((fun y => X τ y t₁) '' B) ↔ IntegrableOn (fun y => g (X τ y t₁)) B := by
  obtain ⟨hmp, hemb⟩ := chart_mp_emb ch hτ
  exact hmp.integrableOn_image hemb

/-- **Section bound.** A bound on the pulled-back square integrals over `B_ρ` for a.e. `τ` in
`(s₀, t₁)` gives the corresponding bound on all time sections of `𝒪`. -/
theorem section_bound (ch : IsPipeChart b0 X t₁ T) {s₀ ρ E : ℝ} (hs₀ : t₁ - 8 * T ≤ s₀)
    {w : ℝ → Vec 2 → ℝ}
    (hint : ∀ᵐ τ ∂(volume.restrict (Ioo s₀ t₁)),
      IntegrableOn (fun y => w τ (X τ y t₁) ^ 2) (euclidBall 0 ρ))
    (hbd : ∀ᵐ τ ∂(volume.restrict (Ioo s₀ t₁)),
      ∫ y in euclidBall 0 ρ, w τ (X τ y t₁) ^ 2 ≤ E ^ 2) :
    ∀ᵐ τ ∂(volume : Measure ℝ),
      IntegrableOn (fun x => w τ x ^ 2) (timeSection (innerPipeO X t₁ s₀ ρ) τ) ∧
        ∫ x in timeSection (innerPipeO X t₁ s₀ ρ) τ, w τ x ^ 2 ≤ E ^ 2 := by
  have hb := ae_restrict_iff' (measurableSet_Ioo (a := s₀) (b := t₁)) |>.1 hbd
  have hi := ae_restrict_iff' (measurableSet_Ioo (a := s₀) (b := t₁)) |>.1 hint
  filter_upwards [hb, hi] with τ h1 h2
  by_cases hτ : τ ∈ Ioo s₀ t₁
  · have hw : τ ∈ Icc (t₁ - 8 * T) t₁ := ⟨by linarith [hτ.1], hτ.2.le⟩
    rw [timeSection_innerPipeO_of_mem hτ]
    refine ⟨(section_integrableOn_iff ch hw (fun x => w τ x ^ 2) _).2 (h2 hτ), ?_⟩
    rw [section_integral_eq ch hw (fun x => w τ x ^ 2)]
    exact h1 hτ
  · rw [timeSection_innerPipeO_of_notMem hτ]
    simp only [Measure.restrict_empty, integral_zero_measure]
    exact ⟨integrableOn_empty, by positivity⟩
end

/-! # Integral utilities for the label traces of the local theorem

Finite covers, `∫_{⋃ S_i} g ≤ ∑ ∫_{S_i} g`, change of variables for a measure preserving
embedding on a set covered by finitely many sets, and the elementary
`∫ (a+b)² ≤ 2 ∫ a² + 2 ∫ b²`. -/

theorem setIntegral_biUnion_le {ι : Type*} [DecidableEq ι] (I : Finset ι) {S : ι → Set (Vec 2)}
    {g : Vec 2 → ℝ} (hg : ∀ x, 0 ≤ g x) (hint : ∀ i ∈ I, IntegrableOn g (S i)) :
    ∫ x in ⋃ i ∈ I, S i, g x ≤ ∑ i ∈ I, ∫ x in S i, g x := by
  induction I using Finset.induction_on with
  | empty => simp
  | insert a I ha ih =>
    have hI : ∀ i ∈ I, IntegrableOn g (S i) := fun i hi => hint i (Finset.mem_insert_of_mem hi)
    have ha' : IntegrableOn g (S a) := hint a (Finset.mem_insert_self a I)
    have hU : IntegrableOn g (⋃ i ∈ I, S i) := (integrableOn_finset_iUnion).2 hI
    rw [Finset.sum_insert ha]
    have hset : (⋃ i ∈ insert a I, S i) = S a ∪ ⋃ i ∈ I, S i := by
      ext x; simp
    rw [hset]
    have hle : volume.restrict (S a ∪ ⋃ i ∈ I, S i) ≤
        volume.restrict (S a) + volume.restrict (⋃ i ∈ I, S i) :=
      Measure.restrict_union_le _ _
    calc ∫ x in S a ∪ ⋃ i ∈ I, S i, g x
        ≤ ∫ x, g x ∂(volume.restrict (S a) + volume.restrict (⋃ i ∈ I, S i)) :=
          integral_mono_measure hle (Eventually.of_forall hg) (Integrable.add_measure ha' hU)
      _ = (∫ x in S a, g x) + ∫ x in ⋃ i ∈ I, S i, g x := integral_add_measure ha' hU
      _ ≤ (∫ x in S a, g x) + ∑ i ∈ I, ∫ x in S i, g x := by gcongr; exact ih hI

/-- Change of variables on a set covered by finitely many sets. -/
theorem setIntegral_comp_le_sum {ι : Type*} [DecidableEq ι] {f : Vec 2 → Vec 2}
    (hmp : MeasurePreserving f volume volume) (hemb : MeasurableEmbedding f) (I : Finset ι)
    {S : ι → Set (Vec 2)} (hS : ∀ i, MeasurableSet (S i)) {g : Vec 2 → ℝ} (hg : ∀ x, 0 ≤ g x)
    (hint : ∀ i ∈ I, IntegrableOn g (S i)) {B : Set (Vec 2)}
    (hcov : ∀ y ∈ B, f y ∈ ⋃ i ∈ I, S i) :
    IntegrableOn (fun y => g (f y)) B ∧ ∫ y in B, g (f y) ≤ ∑ i ∈ I, ∫ x in S i, g x := by
  have hUm : MeasurableSet (⋃ i ∈ I, S i) := MeasurableSet.biUnion I.countable_toSet fun i _ => hS i
  have hU : IntegrableOn g (⋃ i ∈ I, S i) := (integrableOn_finset_iUnion).2 hint
  have hP : IntegrableOn (fun y => g (f y)) (f ⁻¹' ⋃ i ∈ I, S i) :=
    (hmp.integrableOn_comp_preimage hemb).2 hU
  have hsub : B ⊆ f ⁻¹' ⋃ i ∈ I, S i := fun y hy => hcov y hy
  refine ⟨hP.mono_set hsub, ?_⟩
  calc ∫ y in B, g (f y) ≤ ∫ y in f ⁻¹' ⋃ i ∈ I, S i, g (f y) :=
        setIntegral_mono_set hP (Eventually.of_forall fun y => hg _) (Eventually.of_forall hsub)
    _ = ∫ x in ⋃ i ∈ I, S i, g x := hmp.setIntegral_preimage_emb hemb g _
    _ ≤ _ := setIntegral_biUnion_le I hg hint

theorem integral_sq_add_le {S : Set (Vec 2)} {a b : Vec 2 → ℝ}
    (ha : IntegrableOn (fun y => a y ^ 2) S) (hb : IntegrableOn (fun y => b y ^ 2) S) :
    ∫ y in S, (a y + b y) ^ 2 ≤ 2 * (∫ y in S, a y ^ 2) + 2 * (∫ y in S, b y ^ 2) := by
  have h2 : IntegrableOn (fun y => 2 * a y ^ 2 + 2 * b y ^ 2) S :=
    (ha.const_mul 2).add (hb.const_mul 2)
  calc ∫ y in S, (a y + b y) ^ 2 ≤ ∫ y in S, (2 * a y ^ 2 + 2 * b y ^ 2) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun y => sq_nonneg _) h2
          (Eventually.of_forall fun y => ?_)
        nlinarith [sq_nonneg (a y - b y)]
    _ = _ := by
        rw [integral_add (ha.const_mul 2) (hb.const_mul 2), integral_const_mul, integral_const_mul]

theorem euclidBall_subset_closedBall (c : Vec 2) (ρ : ℝ) :
    euclidBall c ρ ⊆ Metric.closedBall c |ρ| := by
  intro y hy
  have h : vecNormSq (y - c) < ρ ^ 2 := hy
  rw [mem_closedBall_iff_norm]
  have h1 := norm_le_sqrt_vecNormSq (y - c)
  have h2 : Real.sqrt (vecNormSq (y - c)) ≤ |ρ| := by
    rw [Real.sqrt_le_left (abs_nonneg ρ), sq_abs]; exact h.le
  linarith

/-- Finite cover of a Euclidean ball by small sup-balls centered in it. -/
theorem exists_finite_cover (ρ ε : ℝ) (hε : 0 < ε) :
    ∃ N : Finset (Vec 2), (∀ y ∈ N, y ∈ euclidBall 0 ρ) ∧
      ∀ y ∈ euclidBall 0 ρ, ∃ z ∈ N, ‖y - z‖ < ε := by
  have htb : TotallyBounded (euclidBall (0 : Vec 2) ρ) :=
    ((isCompact_closedBall (0 : Vec 2) |ρ|).totallyBounded).subset
      (euclidBall_subset_closedBall 0 ρ)
  obtain ⟨t, hts, htf, hcov⟩ := Metric.finite_approx_of_totallyBounded htb ε hε
  refine ⟨htf.toFinset, fun y hy => hts (htf.mem_toFinset.1 hy), fun y hy => ?_⟩
  have := hcov hy
  simp only [mem_iUnion, Metric.mem_ball, exists_prop] at this
  obtain ⟨z, hz, hd⟩ := this
  exact ⟨z, htf.mem_toFinset.2 hz, by rwa [dist_eq_norm] at hd⟩

/-! # From physical tube traces to traces in label coordinates

The tube lemma gives `L²` traces from below on physical discs `B_{r/4}(x)`, `x ∈ K_t`. Here we
transfer them to the label trace `∫_{B_ρ} (w(σ, F_σ y) - W(F_t y))² dy → 0` as `σ → t⁻`
(`F_σ y → F_t y` uniformly in `y`, `F_σ` measure preserving, finite cover of `B_ρ`). -/

section
variable {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T : ℝ}

/-- `F_σ y` moves with speed at most `Cb` in time. -/
theorem chart_time_close (ch : IsPipeChart b0 X t₁ T) {Cb : ℝ}
    (hCb : ∀ τ z, ‖b0 τ z‖ ≤ Cb) (y : Vec 2) (σ t : ℝ) :
    eNorm (X σ y t₁ - X t y t₁) ≤ 2 * Cb * |σ - t| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ)
    (f := fun τ => X τ y t₁) (f' := fun τ => b0 τ (X τ y t₁)) (s := univ) (C := Cb)
    (fun τ _ => (ch.flow.2 y t₁ τ).hasDerivWithinAt) (fun τ _ => hCb τ _) convex_univ
    (mem_univ t) (mem_univ σ)
  rw [Real.norm_eq_abs] at h
  have h2 := eNorm_le_two_mul_norm (X σ y t₁ - X t y t₁)
  have h3 : 0 ≤ Cb := (norm_nonneg _).trans (hCb 0 0)
  nlinarith

theorem chart_time_close' (ch : IsPipeChart b0 X t₁ T) {Cb : ℝ}
    (hCb : ∀ τ z, ‖b0 τ z‖ ≤ Cb) (y : Vec 2) (σ t : ℝ) :
    eNorm (X σ y t₁ - X t y t₁) ≤ 2 * (Cb + 1) * |σ - t| := by
  refine (chart_time_close ch hCb y σ t).trans ?_
  have := abs_nonneg (σ - t)
  nlinarith

theorem chart_time_close_mem (ch : IsPipeChart b0 X t₁ T) {t : ℝ}
    (ht : t ∈ Icc (t₁ - 8 * T) t₁) {ρ₀ ρ₁ σ : ℝ} (hρ₀ : 0 ≤ ρ₀) {y : Vec 2}
    (hy : y ∈ euclidBall 0 ρ₀) (hclose : eNorm (X σ y t₁ - X t y t₁) < (ρ₁ - ρ₀) / 2) :
    X σ y t₁ ∈ (fun y => X t y t₁) '' euclidBall 0 ρ₁ := by
  refine ⟨X t₁ (X σ y t₁) t, ?_, ch.right t ht _⟩
  have h1 := hLip_label ch ht (X σ y t₁) (X t y t₁)
  rw [ch.left t ht y] at h1
  have hyn : eNorm y < ρ₀ := by
    have : vecNormSq y < ρ₀ ^ 2 := by simpa [euclidBall] using hy
    exact eNorm_lt_of_vecNormSq_lt hρ₀ this
  have h2 : eNorm (X t₁ (X σ y t₁) t) < ρ₁ := by
    have h3 := eNorm_add_le (X t₁ (X σ y t₁) t - y) y
    rw [sub_add_cancel] at h3
    linarith
  have hρ₁ : 0 ≤ ρ₁ := (eNorm_nonneg _).trans h2.le
  have := vecNormSq_lt_of_eNorm_lt h2
  simpa [euclidBall] using this


/-- **Label trace of the difference.** -/
theorem label_trace_w (ch : IsPipeChart b0 X t₁ T) {Cb : ℝ} (hCb : ∀ τ z, ‖b0 τ z‖ ≤ Cb)
    {t : ℝ} (ht : t ∈ Ioc (t₁ - 8 * T) t₁) {ρ₀ ρ₁ r s M : ℝ} (hρ₀ : 0 ≤ ρ₀) (hρ : ρ₀ < ρ₁)
    (hr : 0 < r) (hs : 0 < s) (hM : 0 ≤ M) {w : ℝ → Vec 2 → ℝ} {W : Vec 2 → ℝ}
    (hWc : ContinuousOn W (⋃ x ∈ (fun y => X t y t₁) '' euclidBall 0 ρ₁, euclidBall x (r / 4)))
    (hWh : ∀ x ∈ (fun y => X t y t₁) '' euclidBall 0 ρ₁,
      ∀ z ∈ (fun y => X t y t₁) '' euclidBall 0 ρ₁, |W x - W z| ≤ M * eNorm (x - z) ^ s)
    (htr : ∀ x ∈ (fun y => X t y t₁) '' euclidBall 0 ρ₁,
      Tendsto (fun σ => ∫ y in euclidBall x (r / 4), (w σ y - W y) ^ 2)
        (𝓝[<] t ⊓ ae volume) (𝓝 0))
    (hint : ∀ x ∈ (fun y => X t y t₁) '' euclidBall 0 ρ₁,
      ∀ᶠ σ in 𝓝[<] t ⊓ ae volume, IntegrableOn (fun y => (w σ y - W y) ^ 2) (euclidBall x (r / 4)))
    (hwm : ∀ᶠ σ in 𝓝[<] t ⊓ ae volume,
      AEStronglyMeasurable (fun y => w σ (X σ y t₁)) (volume.restrict (euclidBall 0 ρ₀))) :
    Tendsto (fun σ => ∫ y in euclidBall 0 ρ₀, (w σ (X σ y t₁) - W (X t y t₁)) ^ 2)
        (𝓝[<] t ⊓ ae volume) (𝓝 0) ∧
      ∀ᶠ σ in 𝓝[<] t ⊓ ae volume,
        IntegrableOn (fun y => (w σ (X σ y t₁) - W (X t y t₁)) ^ 2) (euclidBall 0 ρ₀) := by
  set F : Filter ℝ := 𝓝[<] t ⊓ ae volume with hF
  set K : Set (Vec 2) := (fun y => X t y t₁) '' euclidBall 0 ρ₁ with hK
  set B₀ : Set (Vec 2) := euclidBall 0 ρ₀ with hB₀
  have htw : t ∈ Icc (t₁ - 8 * T) t₁ := ⟨ht.1.le, ht.2⟩
  have hCb0 : 0 ≤ Cb := (norm_nonneg _).trans (hCb 0 0)
  set Cb' : ℝ := Cb + 1 with hCb'
  have hCb'pos : 0 < Cb' := by positivity
  -- the time window
  set κ₀ : ℝ := min (r / (16 * Cb')) ((ρ₁ - ρ₀) / (8 * Cb')) with hκ₀
  have hκ₀pos : 0 < κ₀ := lt_min (by positivity) (div_pos (by linarith) (by positivity))
  have hnear : Ioo (max (t - κ₀) (t₁ - 8 * T)) t ∈ 𝓝[<] t :=
    Ioo_mem_nhdsLT (max_lt (by linarith) ht.1)
  have hevt : ∀ᶠ σ in F, σ ∈ Ioo (max (t - κ₀) (t₁ - 8 * T)) t := mem_inf_of_left hnear
  -- finite cover
  obtain ⟨N, hNB, hNcov⟩ := exists_finite_cover ρ₀ (r / 64) (by positivity)
  classical
  have hNK : ∀ z ∈ N, X t z t₁ ∈ K := fun z hz =>
    ⟨z, euclidBall_mono 0 hρ₀ hρ.le (hNB z hz), rfl⟩
  have hKN : K ⊆ ⋃ x ∈ K, euclidBall x (r / 4) := by
    intro x hx
    simp only [mem_iUnion]
    exact ⟨x, hx, mem_euclidBall_self x (by positivity)⟩
  have hint' : ∀ᶠ σ in F, ∀ z ∈ N, IntegrableOn (fun y => (w σ y - W y) ^ 2)
      (euclidBall (X t z t₁) (r / 4)) :=
    (Filter.eventually_all_finset N).2 fun z hz => hint _ (hNK z hz)
  -- the key estimates, for σ in the good set
  have hgood : ∀ σ, σ ∈ Ioo (max (t - κ₀) (t₁ - 8 * T)) t →
      σ ∈ Icc (t₁ - 8 * T) t₁ ∧ 2 * Cb' * |σ - t| < min (r / 8) ((ρ₁ - ρ₀) / 4) := by
    intro σ hσ
    have h1 : t - κ₀ < σ := (le_max_left _ _).trans_lt hσ.1
    have h2 : t₁ - 8 * T < σ := (le_max_right _ _).trans_lt hσ.1
    refine ⟨⟨h2.le, by linarith [hσ.2, ht.2]⟩, ?_⟩
    have habs : |σ - t| < κ₀ := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith [hσ.2])]; linarith
    have hk1 : κ₀ ≤ r / (16 * Cb') := min_le_left _ _
    have hk2 : κ₀ ≤ (ρ₁ - ρ₀) / (8 * Cb') := min_le_right _ _
    have e1 : 2 * Cb' * |σ - t| < r / 8 := by
      have : |σ - t| < r / (16 * Cb') := habs.trans_le hk1
      rw [lt_div_iff₀ (by positivity)] at this
      nlinarith
    have e2 : 2 * Cb' * |σ - t| < (ρ₁ - ρ₀) / 4 := by
      have : |σ - t| < (ρ₁ - ρ₀) / (8 * Cb') := habs.trans_le hk2
      rw [lt_div_iff₀ (by positivity)] at this
      nlinarith
    exact lt_min e1 e2
  have hclose : ∀ σ, ∀ y, eNorm (X σ y t₁ - X t y t₁) ≤ 2 * Cb' * |σ - t| := by
    intro σ y
    refine (chart_time_close ch hCb y σ t).trans ?_
    have := abs_nonneg (σ - t)
    nlinarith
  -- measurability data
  have hB₀m : MeasurableSet B₀ := (isOpen_euclidBall' 0 ρ₀).measurableSet
  have hB₀fin : volume B₀ ≠ ⊤ := euclidBall_volume_ne_top 0 ρ₀
  have hFσcont : ∀ σ, Continuous (fun y => X σ y t₁) := fun σ =>
    ch.smoothF.continuous.comp (continuous_const.prodMk continuous_id)
  have hWF : ∀ σ ∈ Ioo (max (t - κ₀) (t₁ - 8 * T)) t,
      ContinuousOn (fun y => W (X σ y t₁)) B₀ := by
    intro σ hσ
    refine hWc.comp (hFσcont σ).continuousOn fun y hy => ?_
    have hmem : X σ y t₁ ∈ K := by
      refine chart_time_close_mem ch htw hρ₀ hy ?_
      have := (hgood σ hσ).2
      have h1 := hclose σ y
      have h2 : min (r / 8) ((ρ₁ - ρ₀) / 4) ≤ (ρ₁ - ρ₀) / 4 := min_le_right _ _
      linarith
    exact hKN hmem
  have hWt : ContinuousOn (fun y => W (X t y t₁)) B₀ := by
    refine hWc.comp (hFσcont t).continuousOn fun y hy => ?_
    exact hKN ⟨y, euclidBall_mono 0 hρ₀ hρ.le hy, rfl⟩
  -- pointwise bound on the second term
  have hbd2 : ∀ σ ∈ Ioo (max (t - κ₀) (t₁ - 8 * T)) t, ∀ y ∈ B₀,
      |W (X σ y t₁) - W (X t y t₁)| ≤ M * (2 * Cb' * |σ - t|) ^ s := by
    intro σ hσ y hy
    have hmem : X σ y t₁ ∈ K := by
      refine chart_time_close_mem ch htw hρ₀ hy ?_
      have := (hgood σ hσ).2
      have h1 := hclose σ y
      have h2 : min (r / 8) ((ρ₁ - ρ₀) / 4) ≤ (ρ₁ - ρ₀) / 4 := min_le_right _ _
      linarith
    have hmem' : X t y t₁ ∈ K := ⟨y, euclidBall_mono 0 hρ₀ hρ.le hy, rfl⟩
    refine (hWh _ hmem _ hmem').trans ?_
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (eNorm_nonneg _) (hclose σ y) hs.le) hM
  -- bound for the first term via the cover
  have hcover : ∀ σ ∈ Ioo (max (t - κ₀) (t₁ - 8 * T)) t, ∀ y ∈ B₀,
      X σ y t₁ ∈ ⋃ z ∈ N, euclidBall (X t z t₁) (r / 4) := by
    intro σ hσ y hy
    obtain ⟨z, hzN, hyz⟩ := hNcov y hy
    simp only [mem_iUnion]
    refine ⟨z, hzN, ?_⟩
    have hw := (hgood σ hσ).1
    have h1 := hclose σ y
    have h2 := (hgood σ hσ).2
    have h3 : min (r / 8) ((ρ₁ - ρ₀) / 4) ≤ r / 8 := min_le_left _ _
    have h4 := hLip_label ch htw y z
    have h5 := eNorm_le_two_mul_norm (y - z)
    have h6 : eNorm (X σ y t₁ - X t z t₁) ≤
        eNorm (X σ y t₁ - X t y t₁) + eNorm (X t y t₁ - X t z t₁) := by
      have := eNorm_add_le (X σ y t₁ - X t y t₁) (X t y t₁ - X t z t₁)
      rwa [sub_add_sub_cancel] at this
    have h7 : eNorm (X σ y t₁ - X t z t₁) < r / 4 := by
      have : eNorm (y - z) ≤ 2 * (r / 64) := h5.trans (by nlinarith [hyz])
      -- chart Lipschitz: `|F_t y - F_t z| ≤ 2 |y - z|`
      have h8 : eNorm (X t y t₁ - X t z t₁) ≤ 2 * eNorm (y - z) := by
        have hd : Differentiable ℝ (fun w : Vec 2 => X t w t₁) :=
          (ch.smoothF.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
        exact euclid_lipschitz_of_fderiv_close hd (ch.close t htw) y z
      linarith
    have : vecNormSq (X σ y t₁ - X t z t₁) < (r / 4) ^ 2 := vecNormSq_lt_of_eNorm_lt h7
    simpa [euclidBall] using this
  -- assemble
  set e : ℝ → ℝ := fun σ => M * (2 * Cb' * |σ - t|) ^ s with he
  have hecont : Continuous e := by
    have h1 : Continuous fun σ : ℝ => 2 * Cb' * |σ - t| := by fun_prop
    exact continuous_const.mul ((Real.continuous_rpow_const hs.le).comp h1)
  have he0 : Tendsto e F (𝓝 0) := by
    have h1 : Tendsto e (𝓝 t) (𝓝 (e t)) := hecont.tendsto t
    have h2 : e t = 0 := by simp [he, Real.zero_rpow hs.ne']
    rw [h2] at h1
    exact h1.mono_left (inf_le_left.trans nhdsWithin_le_nhds)
  have hJ : Tendsto (fun σ => ∑ z ∈ N, ∫ x in euclidBall (X t z t₁) (r / 4), (w σ x - W x) ^ 2)
      F (𝓝 0) := by
    have := tendsto_finsetSum N (fun z hz => htr _ (hNK z hz))
    simpa using this
  have hU : Tendsto (fun σ => 2 * (∑ z ∈ N, ∫ x in euclidBall (X t z t₁) (r / 4),
      (w σ x - W x) ^ 2) + 2 * ((volume B₀).toReal * e σ ^ 2)) F (𝓝 0) := by
    have h1 := (hJ.const_mul 2).add (((he0.pow 2).const_mul (volume B₀).toReal).const_mul 2)
    simpa using h1
  -- the estimates for good `σ`
  have hmain : ∀ σ, σ ∈ Ioo (max (t - κ₀) (t₁ - 8 * T)) t →
      (∀ z ∈ N, IntegrableOn (fun y => (w σ y - W y) ^ 2) (euclidBall (X t z t₁) (r / 4))) →
      AEStronglyMeasurable (fun y => w σ (X σ y t₁)) (volume.restrict B₀) →
      IntegrableOn (fun y => (w σ (X σ y t₁) - W (X t y t₁)) ^ 2) B₀ ∧
      ∫ y in B₀, (w σ (X σ y t₁) - W (X t y t₁)) ^ 2 ≤
        2 * (∑ z ∈ N, ∫ x in euclidBall (X t z t₁) (r / 4), (w σ x - W x) ^ 2) +
          2 * ((volume B₀).toReal * e σ ^ 2) := by
    intro σ hσ hI hm
    have hw := (hgood σ hσ).1
    obtain ⟨hmp, hemb⟩ := chart_mp_emb ch hw
    obtain ⟨hI1, hI2⟩ := setIntegral_comp_le_sum hmp hemb N
      (S := fun z => euclidBall (X t z t₁) (r / 4))
      (fun z => (isOpen_euclidBall' _ _).measurableSet)
      (g := fun x => (w σ x - W x) ^ 2) (fun x => sq_nonneg _) hI (B := B₀) (hcover σ hσ)
    -- the second term
    have hm2 : AEStronglyMeasurable (fun y => W (X σ y t₁) - W (X t y t₁)) (volume.restrict B₀) :=
      ((hWF σ hσ).sub hWt).aestronglyMeasurable hB₀m
    have hbd : ∀ y ∈ B₀, ‖(W (X σ y t₁) - W (X t y t₁)) ^ 2‖ ≤ e σ ^ 2 := by
      intro y hy
      have := hbd2 σ hσ y hy
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    have hI3 : IntegrableOn (fun y => (W (X σ y t₁) - W (X t y t₁)) ^ 2) B₀ :=
      haveI : IsFiniteMeasure (volume.restrict B₀) := isFiniteMeasure_restrict.mpr hB₀fin
      Integrable.of_bound (hm2.pow 2) (e σ ^ 2)
        ((ae_restrict_iff' hB₀m).2 (Eventually.of_forall hbd))
    have hI4 : ∫ y in B₀, (W (X σ y t₁) - W (X t y t₁)) ^ 2 ≤ (volume B₀).toReal * e σ ^ 2 := by
      have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := B₀)
        (f := fun y => (W (X σ y t₁) - W (X t y t₁)) ^ 2) (C := e σ ^ 2)
        (lt_top_iff_ne_top.2 hB₀fin) hbd
      refine (le_abs_self _).trans ?_
      rw [← Real.norm_eq_abs]
      simpa [Measure.real, mul_comm] using this
    have hfun : (fun y => (w σ (X σ y t₁) - W (X t y t₁)) ^ 2) = fun y =>
        ((w σ (X σ y t₁) - W (X σ y t₁)) + (W (X σ y t₁) - W (X t y t₁))) ^ 2 := by
      funext y; ring
    have hsum := integral_sq_add_le (S := B₀) (a := fun y => w σ (X σ y t₁) - W (X σ y t₁))
      (b := fun y => W (X σ y t₁) - W (X t y t₁)) hI1 hI3
    refine ⟨?_, ?_⟩
    · -- integrability of the square of the total
      have hmeas : AEStronglyMeasurable (fun y => w σ (X σ y t₁) - W (X t y t₁))
          (volume.restrict B₀) := hm.sub (hWt.aestronglyMeasurable hB₀m)
      refine Integrable.mono' (g := fun y => 2 * (w σ (X σ y t₁) - W (X σ y t₁)) ^ 2 +
        2 * (W (X σ y t₁) - W (X t y t₁)) ^ 2) ((hI1.const_mul 2).add (hI3.const_mul 2))
        (hmeas.pow 2) (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [sq_nonneg ((w σ (X σ y t₁) - W (X σ y t₁)) - (W (X σ y t₁) - W (X t y t₁)))]
    · rw [hfun]
      calc _ ≤ 2 * (∫ y in B₀, (w σ (X σ y t₁) - W (X σ y t₁)) ^ 2) +
            2 * (∫ y in B₀, (W (X σ y t₁) - W (X t y t₁)) ^ 2) := hsum
        _ ≤ _ := by gcongr
  have hev : ∀ᶠ σ in F, σ ∈ Ioo (max (t - κ₀) (t₁ - 8 * T)) t ∧
      (∀ z ∈ N, IntegrableOn (fun y => (w σ y - W y) ^ 2) (euclidBall (X t z t₁) (r / 4))) ∧
      AEStronglyMeasurable (fun y => w σ (X σ y t₁)) (volume.restrict B₀) :=
    hevt.and (hint'.and hwm)
  refine ⟨?_, hev.mono fun σ hσ => (hmain σ hσ.1 hσ.2.1 hσ.2.2).1⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU
    (Eventually.of_forall fun σ => setIntegral_nonneg hB₀m fun y _ => sq_nonneg _) ?_
  exact hev.mono fun σ hσ => (hmain σ hσ.1 hσ.2.1 hσ.2.2).2
end

end AVRegularity.Applications
end
