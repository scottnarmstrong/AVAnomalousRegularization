-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Applications.Local.Instance
import AVRegularity.Applications.Microscopic.Main
import AVRegularity.Velocity.ExistsLimitVelocity
import AVRegularity.Wellposed.Existence
public import AVRegularity.Applications.Construction
import AVRegularity.Applications.Global.CompactRangeMain
import AVenhance.Infra.Construction.StreamAdmissible
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Monotonicity.Lemmas

@[expose] public section
noncomputable section

section
open MeasureTheory Filter Topology Homogenization AVenhance AVRegularity Set
namespace AVRegularity.Applications

/-! # The local estimate for one instance, from the three analytic inputs

`local_instance` assembles the proof of Theorem C of the paper for fixed pipe data and one
`(t₁, X, κ, θ)`, given the data produced by Davies' lemma, the physical lift and the local traces
(`u`, `Θ_u`, `Dw`, `U`): the translating tubes of radius `r = smoothRadius` stay in the comparison
pipe, the tube estimate bounds the difference, and `r^{-1-s} e^{-D/κ}` is bounded uniformly. -/

section
variable {b b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T : ℝ}

/-- The slices `θ(σ, F_σ ·)` are `L²` on the labels of the inner pipe, for a.e. `σ`. -/
theorem theta_pullback_memLp {R κ : ℝ} {θ : ℝ → Vec 2 → ℝ}
    (hθ : IsLocalEnergySolution b κ (fun t y => X t y t₁) t₁ T R θ) :
    ∀ᵐ σ ∂(volume : Measure ℝ), σ ∈ Ioo (t₁ - 8 * T) t₁ →
      MemL2On (euclidBall 0 R) (fun y => θ σ (X σ y t₁)) := by
  obtain ⟨-, -, DU, ⟨C, hC⟩, -, -⟩ := hθ
  have := (ae_restrict_iff' (measurableSet_Ioo (a := t₁ - 8 * T) (b := t₁))).1 hC
  filter_upwards [this] with σ h hσ
  exact (h hσ).1


/-- The squared difference of the pulled-back slices is integrable on the label ball, a.e. -/
theorem diff_sq_integrable (ch : IsPipeChart b0 X t₁ T) {s₀ R ρ : ℝ} {θ u : ℝ → Vec 2 → ℝ}
    (hs₀t : s₀ < t₁) (hs₀5 : t₁ ≤ s₀ + 5 * T) (hρ : 0 < ρ)
    (hρ2 : 2 * ρ ≤ 1 / 2) (hρR : ρ ≤ R)
    (hθL2 : ∀ᵐ σ ∂(volume : Measure ℝ), σ ∈ Ioo (t₁ - 8 * T) t₁ →
      MemL2On (euclidBall 0 R) (fun y => θ σ (X σ y t₁)))
    (hup : ∀ σ ∈ Icc s₀ (s₀ + 5 * T), IsZ2Periodic (u σ))
    (hum : ∀ σ ∈ Icc s₀ (s₀ + 5 * T), MemL2On unitCube (u σ)) :
    ∀ᵐ τ ∂(volume.restrict (Ioo s₀ t₁)),
      IntegrableOn (fun y => (θ τ (X τ y t₁) - u τ (X τ y t₁)) ^ 2) (euclidBall 0 ρ) := by
  refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
  filter_upwards [hθL2] with τ h hτ
  have hτ' : τ ∈ Ioo (t₁ - 8 * T) t₁ := ⟨by linarith [hτ.1], hτ.2⟩
  have hτw : τ ∈ Icc (t₁ - 8 * T) t₁ := ⟨hτ'.1.le, hτ'.2.le⟩
  have hτI : τ ∈ Icc s₀ (s₀ + 5 * T) := ⟨hτ.1.le, by linarith [hτ.2]⟩
  have hθm : MemLp (fun y => θ τ (X τ y t₁)) 2 (volume.restrict (euclidBall 0 ρ)) :=
    (h hτ').mono_measure (Measure.restrict_mono (euclidBall_mono 0 hρ.le hρR) le_rfl)
  have hum' := memLp_pullback_of_periodic ch hτw hρ hρ2 (hup τ hτI) (hum τ hτI)
  exact (hθm.sub hum').integrable_sq

/-- **The local estimate for one instance.** -/
theorem local_instance {α s : ℝ} (ch : IsPipeChart b0 X t₁ T)
    (hb0 : AVenhance.Infra.Flow.SmoothPeriodicField b0) {Cb0 V₁ : ℝ}
    (hCb : ∀ τ z, ‖b0 τ z‖ ≤ Cb0) (hV : ∀ τ z, ‖b τ z - b0 τ z‖ ≤ V₁) (hV₁ : 0 ≤ V₁)
    (hs : 0 < s) (hs1 : s ≤ 1) {R ϱ ϑ κ : ℝ} (hT : 0 < T) (hR : 0 < R) (hR8 : R ≤ 1 / 8)
    (hϱ : 0 < ϱ) (hϱ8 : ϱ < 1 / 8) (hϑ : 0 < ϑ) (hϑ4 : ϑ < 4) (hκ : 0 < κ) {c Ct : ℝ}
    (hcpos : 0 < c) (hCt : 0 ≤ Ct) (hc : TubeStmt α s b c Ct) {CD cD Cg Cr r₀ τ₀ : ℝ}
    (hCD : 0 ≤ CD) (hCg : 0 ≤ Cg) (hCr : 0 ≤ Cr) (hr₀ : 0 < r₀)
    (hr₀d : r₀ ≤ (1 / 8 - ϱ) * R / 2 / 4) (hr₀8 : r₀ ≤ 1 / 8) (hτ₀ : 0 < τ₀)
    (hτ₀m : τ₀ ≤ (4 - ϑ) * T / 2) (hτ₀d : τ₀ ≤ (1 / 8 - ϱ) * R / 2 / (12 * (1 + V₁)))
    (hCrb : ∀ κ' : ℝ, 0 < κ' →
      smoothRadius α r₀ c τ₀ κ' ^ (-1 - s) * Real.exp (-(cD * R ^ 2 / T / κ')) ≤ Cr)
    {θ u : ℝ → Vec 2 → ℝ} {Dw : ℝ × Vec 2 → Vec 2} {Θu : ℝ → Vec 2 → ℝ}
    (hθ : IsLocalEnergySolution b κ (fun t y => X t y t₁) t₁ T R θ)
    (hup : ∀ σ ∈ Icc (t₁ - 9 * T / 2) (t₁ - 9 * T / 2 + 5 * T), IsZ2Periodic (u σ))
    (hum : ∀ σ ∈ Icc (t₁ - 9 * T / 2) (t₁ - 9 * T / 2 + 5 * T), MemL2On unitCube (u σ))
    (hΘc : ContinuousOn (fun p : ℝ × Vec 2 => Θu p.1 p.2)
      (Icc (t₁ - 9 * T / 2 + (4 - ϑ) * T) (t₁ - 9 * T / 2 + 5 * T) ×ˢ univ))
    (hΘ : ∀ σ ∈ Icc (t₁ - 9 * T / 2 + (4 - ϑ) * T) (t₁ - 9 * T / 2 + 5 * T),
      IsZ2Periodic (Θu σ) ∧ Θu σ =ᵐ[volume.restrict unitCube] u σ ∧
        CsNormLe s (Θu σ) (Cg * CD * R * pipeAmp X t₁ T R θ))
    (hDav : ∀ᵐ τ ∂(volume.restrict (Ioo (t₁ - 9 * T / 2) t₁)),
      ∫ y in euclidBall 0 (R / 8), (θ τ (X τ y t₁) - u τ (X τ y t₁)) ^ 2 ≤
        (CD * R * pipeAmp X t₁ T R θ * Real.exp (-cD * R ^ 2 / (κ * T))) ^ 2)
    (hDw : IsLocalWeakSolution b κ (innerPipeO X t₁ (t₁ - 9 * T / 2) (R / 8))
      (fun p => θ p.1 p.2 - u p.1 p.2) Dw)
    (hUt : ∃ Ut : Vec 2 → ℝ, MemL2On (euclidBall 0 (ϱ * R)) Ut ∧
      Tendsto (fun σ => ∫ y in euclidBall 0 (ϱ * R), (θ σ (X σ y t₁) - Ut y) ^ 2)
        (𝓝[<] t₁ ⊓ ae volume) (𝓝 0)) :
    ∃ Θ : ℝ → Vec 2 → ℝ, ∀ t ∈ Icc (t₁ - ϑ * T) t₁,
      ContinuousOn (Θ t) ((fun y => X t y t₁) '' euclidBall 0 (ϱ * R)) ∧
      Tendsto (fun σ => ∫ y in euclidBall 0 (ϱ * R), (θ σ (X σ y t₁) - Θ t (X t y t₁)) ^ 2)
        (𝓝[<] t ⊓ ae volume) (𝓝 0) ∧
      ∀ x ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R),
      ∀ y ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R),
      ∀ z ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R), y ≠ z →
        |Θ t x| + |Θ t y - Θ t z| / Real.sqrt (vecNormSq (y - z)) ^ s ≤
          (2 * (Ct * CD * R * Cr + 4 * Cg * CD * R)) * pipeAmp X t₁ T R θ := by
  obtain ⟨hd, hρ₀₁, hρd, hρ₀', hρ₀R⟩ := pipe_numerics hR hR8 hϱ hϱ8
  set s₀ : ℝ := t₁ - 9 * T / 2 with hs₀def
  set Amp : ℝ := pipeAmp X t₁ T R θ with hAmpdef
  have hAmp : 0 ≤ Amp := Real.sqrt_nonneg _
  set ρ₀ : ℝ := ϱ * R with hρ₀def
  set ρ₁ : ℝ := (ϱ + 1 / 8) / 2 * R with hρ₁def
  have hρ₀ : 0 < ρ₀ := by positivity
  have hs₀w : t₁ - 8 * T ≤ s₀ := by rw [hs₀def]; linarith only [hT]
  -- the radius
  obtain ⟨hr8, hrc, hrτ, hrd⟩ := smoothRadius_props (α := α) (V₁ := V₁)
    (d := (1 / 8 - ϱ) * R / 2) hr₀ hr₀d hr₀8 hcpos hτ₀ hτ₀d hV₁ hκ
  have hrpos := smoothRadius_pos (α := α) hr₀ hcpos hτ₀ hκ
  set r : ℝ := smoothRadius α r₀ c τ₀ κ with hrdef
  have hrd' : 2 * r + 6 * V₁ * (r ^ 2 / κ) ≤ R / 8 - ρ₁ := by rw [hρ₁def, hρd]; exact hrd
  -- the bound on the difference at the sections
  set E : ℝ := CD * R * Amp * Real.exp (-cD * R ^ 2 / (κ * T)) with hEdef
  have hEnn : 0 ≤ E := by positivity
  have hEeq : E = CD * R * Amp * Real.exp (-(cD * R ^ 2 / T / κ)) := by
    rw [hEdef]; congr 2; field_simp
  have hθL2 := theta_pullback_memLp hθ
  have hint := diff_sq_integrable ch (by rw [hs₀def]; linarith) (by rw [hs₀def]; linarith)
    (by positivity : 0 < R / 8) (by linarith) (by linarith) hθL2 hup hum
  have hsec := section_bound ch hs₀w (ρ := R / 8) (E := E) (w := fun τ x => θ τ x - u τ x) hint hDav
  -- the constant
  set Bd : ℝ := (Ct * CD * R * Cr + 4 * Cg * CD * R) * Amp with hBddef
  have hBd : 0 ≤ Bd := by positivity
  have hradius : Ct * r ^ (-1 - s) * E + 4 * (Cg * CD * R * Amp) ≤ Bd := by
    have h1 : r ^ (-1 - s) * Real.exp (-(cD * R ^ 2 / T / κ)) ≤ Cr := hCrb κ hκ
    have h2 : Ct * r ^ (-1 - s) * E = Ct * CD * R * Amp *
        (r ^ (-1 - s) * Real.exp (-(cD * R ^ 2 / T / κ))) := by rw [hEeq]; ring
    have h3 : Ct * CD * R * Amp * (r ^ (-1 - s) * Real.exp (-(cD * R ^ 2 / T / κ))) ≤
        Ct * CD * R * Amp * Cr := mul_le_mul_of_nonneg_left h1 (by positivity)
    rw [h2, hBddef]
    nlinarith
  have hσ₁s₀ : s₀ ≤ s₀ + (4 - ϑ) * T := by
    have : 0 < (4 - ϑ) * T := mul_pos (by linarith only [hϑ4]) hT
    linarith only [this]
  have hup' : ∀ σ ∈ Icc (s₀ + (4 - ϑ) * T) (s₀ + 5 * T), IsZ2Periodic (u σ) :=
    fun σ hσ => hup σ ⟨hσ₁s₀.trans hσ.1, hσ.2⟩
  have hum' : ∀ σ ∈ Icc (s₀ + (4 - ϑ) * T) (s₀ + 5 * T), MemL2On unitCube (u σ) :=
    fun σ hσ => hum σ ⟨hσ₁s₀.trans hσ.1, hσ.2⟩
  -- the family of slices
  have hfam : SliceFam X t₁ θ (ϑ * T) ρ₀ s Bd := by
    intro t ht
    have ht1 : t < t₁ := ht.2
    have htl : s₀ < t - r ^ 2 / κ := window_arith hT hϑ4 ht.1 hrτ hτ₀m
    have hσ₁ : s₀ + (4 - ϑ) * T < t := window_arith₂ hT ht.1
    have htσ₂ : t ≤ s₀ + 5 * T := by rw [hs₀def]; linarith only [ht.2, hT]
    have hθm : ∀ᶠ σ in 𝓝[<] t ⊓ ae volume,
        AEStronglyMeasurable (fun y => θ σ (X σ y t₁)) (volume.restrict (euclidBall 0 ρ₀)) := by
      have hδ : 0 < t - (t₁ - 8 * T) := by linarith only [window_arith₃ hT hϑ4 ht.1]
      refine eventually_of_Ioo hδ ?_
      filter_upwards [hθL2] with σ h hσ
      have hσ' : σ ∈ Ioo (t₁ - 8 * T) t₁ := ⟨by linarith only [hσ.1], by linarith only [hσ.2, ht.2]⟩
      exact ((h hσ').mono_measure (Measure.restrict_mono (euclidBall_mono 0 hρ₀.le
        hρ₀R) le_rfl)).aestronglyMeasurable
    obtain ⟨Θt, hc', hb1, hb2, htr⟩ := slice_below ch hb0 hCb hV hs hs1 hc hCt hκ hs₀w hρ₀ hρ₀'
      hρ₀₁ hEnn hrpos hr8 hrc hrd' hDw hsec ht1 htl hθm hσ₁ htσ₂ hΘc hΘ hup' hum'
    have hsub : (fun y => X t y t₁) '' euclidBall (0 : Vec 2) ρ₀ ⊆
        (fun y => X t y t₁) '' euclidBall 0 ρ₁ :=
      Set.image_mono (euclidBall_mono 0 hρ₀.le hρ₀₁.le)
    refine ⟨Θt, hc'.mono hsub, fun x hx => (hb1 x (hsub hx)).trans hradius, fun x hx z hz => ?_,
      htr⟩
    refine (hb2 x (hsub hx) z (hsub hz)).trans ?_
    exact mul_le_mul_of_nonneg_right hradius (Real.rpow_nonneg (eNorm_nonneg _) _)
  have hθL2' : ∀ᵐ σ ∂(volume : Measure ℝ), σ ∈ Ioo (t₁ - ϑ * T) t₁ →
      MemLp (fun y => θ σ (X σ y t₁)) 2 (volume.restrict (euclidBall 0 ρ₀)) := by
    filter_upwards [hθL2] with σ h hσ
    have hϑT : ϑ * T ≤ 8 * T := by nlinarith only [hT, hϑ4]
    have hσ' : σ ∈ Ioo (t₁ - 8 * T) t₁ := ⟨by linarith only [hσ.1, hϑT], hσ.2⟩
    exact (h hσ').mono_measure (Measure.restrict_mono (euclidBall_mono 0 hρ₀.le hρ₀R) le_rfl)
  have hϑT : 0 < ϑ * T := mul_pos hϑ hT
  have hϑ8 : ϑ * T ≤ 8 * T := by nlinarith only [hT, hϑ4]
  obtain ⟨Θ, hΘ'⟩ := instance_final ch hϑT hϑ8 hs hs1 hBd hθL2' hfam hUt
  refine ⟨Θ, fun t ht => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hΘ' t ht
  refine ⟨h1, h2, fun x hx y hy z hz hyz => (h3 x hx y hy z hz hyz).trans ?_⟩
  rw [hBddef]; ring_nf; exact le_rfl
end

/-! # Assembly of the local theorem from its tools

The local theorem is Theorem C of the paper. The three analytic inputs `DaviesStmt`,
`PhysLiftStmt`, `LocalTraceStmt` and the global theorem are explicit hypotheses. Here: the
instance level (`instance_of_tools`), fixed pipe data (`local_after_constants`), and
`local_interior_regularity_of_tools`. -/

section
/-- The body of `DaviesStmt` after the choice of the constants. -/
def DaviesBody (α q : ℝ) (Λ : ℕ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (b : ℝ → Vec 2 → Vec 2)
    (Cb C c : ℝ) : Prop :=
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

theorem daviesBody_of_stmt {α q : ℝ} {Λ : ℕ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {b : ℝ → Vec 2 → Vec 2}
    (h : DaviesStmt α q Λ Φ b) :
    ∃ Cb C c : ℝ, 0 < Cb ∧ 0 ≤ C ∧ 0 < c ∧ DaviesBody α q Λ Φ b Cb C c := h

/-- The global theorem at one window, with the constant `C`. -/
def GlobalWindow (α s q : ℝ) (Λ : ℕ) (b : ℝ → Vec 2 → Vec 2) (t₀ T C : ℝ) : Prop :=
  ∀ a : ℝ, ∀ κ ∈ ocBandSet α q Λ, ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
    ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a (a + T) f θ →
      ∃ Θ : ℝ → Vec 2 → ℝ,
        ContinuousOn (fun p : ℝ × Vec 2 => Θ p.1 p.2) (Set.Icc (a + t₀) (a + T) ×ˢ Set.univ) ∧
        ∀ t ∈ Set.Icc (a + t₀) (a + T),
          IsZ2Periodic (Θ t) ∧ Θ t =ᵐ[volume.restrict unitCube] θ t ∧
          CsNormLe s (Θ t) (C * Real.sqrt (l2NormSq f))

theorem globalWindow_of_statement {α s q : ℝ} {ζ : ℝ → ℝ} (h : OcGlobalStatement α s q ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
      ∀ b : ℝ → Vec 2 → Vec 2,
        (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) →
        ∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∃ C : ℝ, GlobalWindow α s q Λ b t₀ T C := h


section Instance

variable {α s q : ℝ} {ζ : ℝ → ℝ} {Λ : ℕ} {Φ : ℕ → ℝ → Vec 2 → ℝ} {b : ℝ → Vec 2 → Vec 2}

/-- **One instance of the local theorem**, for fixed constants and numerics. -/
theorem instance_of_tools (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (hζ : IsFastProfile ζ) (hΛ : 128 ≤ Λ)
    (hΦ : IsOCStreamSeq α q Λ ζ Φ)
    (hholder : IsHolderDivFreeVelocity α b) {Cb CD cD : ℝ} (hDav : DaviesBody α q Λ Φ b Cb CD cD)
    (hCD : 0 ≤ CD) (hphys : PhysLiftStmt α q Λ Φ b) (htr : LocalTraceStmt α q Λ Φ b) {Cs : ℝ}
    (htail : ∀ m t x, ‖b t x - streamVel (Φ m) t x‖ ≤ Cs * ocEpsilon q Λ (m + 1) ^ α)
    (hbdd : ∀ m t x, ‖streamVel (Φ m) t x‖ ≤ Cs) (hCs : 0 ≤ Cs) {c Ct : ℝ} (hcpos : 0 < c)
    (hCt : 0 ≤ Ct) (hc : TubeStmt α s b c Ct) {n : ℕ} (hn : 2 ≤ n) {T R ϱ ϑ : ℝ} (hT : 0 < T)
    (hR : 0 < R) (hR8 : R ≤ 1 / 8) (hϱ : 0 < ϱ) (hϱ8 : ϱ < 1 / 8) (hϑ : 0 < ϑ) (hϑ4 : ϑ < 4)
    (h8T : 8 * T * ocA α q Λ (n - 2) ≤ ocCStar)
    (hCbε : Cb * (ocEpsilon q Λ (n - 1) ^ α * T) ≤ R)
    (hCbκ : ∀ κ ∈ ocBandSet α q Λ, Cb * Real.sqrt (κ * T) ≤ R) {Cg Cr r₀ τ₀ : ℝ} (hCg : 0 ≤ Cg)
    (hCr : 0 ≤ Cr) (hr₀ : 0 < r₀)
    (hr₀d : r₀ ≤ (1 / 8 - ϱ) * R / 2 / 4) (hr₀8 : r₀ ≤ 1 / 8) (hτ₀ : 0 < τ₀)
    (hτ₀m : τ₀ ≤ (4 - ϑ) * T / 2)
    (hτ₀d : τ₀ ≤ (1 / 8 - ϱ) * R / 2 / (12 * (1 + Cs * ocEpsilon q Λ (n - 1) ^ α)))
    (hCrb : ∀ κ' : ℝ, 0 < κ' →
      smoothRadius α r₀ c τ₀ κ' ^ (-1 - s) * Real.exp (-(cD * R ^ 2 / T / κ')) ≤ Cr)
    (hGl : GlobalWindow α s q Λ b ((4 - ϑ) * T) (5 * T) Cg)
    {t₁ : ℝ} {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlow (streamVel (Φ (n - 2))) X) {κ : ℝ}
    (hκ : κ ∈ ocBandSet α q Λ) {θ : ℝ → Vec 2 → ℝ}
    (hθ : IsLocalEnergySolution b κ (fun t y => X t y t₁) t₁ T R θ) :
    ∃ Θ : ℝ → Vec 2 → ℝ, ∀ t ∈ Icc (t₁ - ϑ * T) t₁,
      ContinuousOn (Θ t) ((fun y => X t y t₁) '' euclidBall 0 (ϱ * R)) ∧
      Tendsto (fun σ => ∫ y in euclidBall 0 (ϱ * R), (θ σ (X σ y t₁) - Θ t (X t y t₁)) ^ 2)
        (𝓝[<] t ⊓ ae volume) (𝓝 0) ∧
      ∀ x ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R),
      ∀ y ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R),
      ∀ z ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R), y ≠ z →
        |Θ t x| + |Θ t y - Θ t z| / Real.sqrt (vecNormSq (y - z)) ^ s ≤
          (2 * (Ct * CD * R * Cr + 4 * Cg * CD * R)) * pipeAmp X t₁ T R θ := by
  have hq1 : 1 < q := hq.1
  obtain ⟨hκ0, -⟩ := band_pos_le_two hα₀ hq1 hΛ hκ
  have hn1 : n - 2 + 1 = n - 1 := by omega
  have hch := isPipeChart_of_construction α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ (n - 2) X hX
    t₁ T hT h8T
  have hb0 := AVenhance.Infra.Construction.smoothPeriodic_streamVel
    (AVRegularity.Velocity.streamSeq_admissible hζ hΛ hΦ (n - 2))
  have hV : ∀ τ z, ‖b τ z - streamVel (Φ (n - 2)) τ z‖ ≤ Cs * ocEpsilon q Λ (n - 1) ^ α := by
    intro τ z
    have := htail (n - 2) τ z
    rwa [hn1] at this
  have hV₁ : 0 ≤ Cs * ocEpsilon q Λ (n - 1) ^ α := by
    have := eps_pos (q := q) (Λ := Λ) (m := n - 1) hq1 hΛ
    positivity
  have hκT : Cb * Real.sqrt (κ * T) ≤ R := hCbκ κ hκ
  obtain ⟨f, hfL2, hfn, HDav⟩ := hDav n hn X hX t₁ T R κ hT hR hR8 hκ0 h8T hCbε hκT θ hθ
  obtain ⟨u, hu, -⟩ := Wellposed.exists_unique_isWeakSolutionOn_of_isHolderDivFreeVelocity α hα₀ b
    hholder κ hκ0 (t₁ - 9 * T / 2) (t₁ - 9 * T / 2 + 5 * T) (by linarith) f hfL2
  have hDavI := HDav u hu
  obtain ⟨Dw, hDw⟩ := hphys n hn X hX t₁ T R κ hT hR hR8 hκ0 h8T θ hθ f hfL2 u hu
  have hUt := htr n hn X hX t₁ T R κ hT hR hR8 hκ0 h8T θ hθ (ϱ * R) (by positivity)
    (by nlinarith) t₁ ⟨by linarith, le_rfl⟩
  obtain ⟨Θu, hΘc, hΘ⟩ := hGl (t₁ - 9 * T / 2) κ hκ f hfL2 u hu
  have hup : ∀ σ ∈ Icc (t₁ - 9 * T / 2) (t₁ - 9 * T / 2 + 5 * T), IsZ2Periodic (u σ) := by
    obtain ⟨-, hsl, -⟩ := hu
    exact fun σ hσ => (hsl σ hσ).1
  have hum : ∀ σ ∈ Icc (t₁ - 9 * T / 2) (t₁ - 9 * T / 2 + 5 * T), MemL2On unitCube (u σ) := by
    obtain ⟨-, hsl, -⟩ := hu
    exact fun σ hσ => (hsl σ hσ).2
  have hKle : Cg * Real.sqrt (l2NormSq f) ≤ Cg * CD * R * pipeAmp X t₁ T R θ := by
    have := mul_le_mul_of_nonneg_left hfn hCg
    calc Cg * Real.sqrt (l2NormSq f) ≤ Cg * (CD * R * pipeAmp X t₁ T R θ) := this
      _ = Cg * CD * R * pipeAmp X t₁ T R θ := by ring
  refine local_instance hch hb0 (fun τ z => hbdd (n - 2) τ z) hV hV₁ hs₀ (by linarith only [hs₁, hα₀]) hT hR hR8 hϱ hϱ8 hϑ hϑ4 hκ0 hcpos hCt hc hCD hCg hCr hr₀ hr₀d hr₀8
    hτ₀ hτ₀m hτ₀d hCrb hθ hup hum hΘc (fun σ hσ => ?_) hDavI hDw hUt
  obtain ⟨h1, h2, h3⟩ := hΘ σ hσ
  exact ⟨h1, h2, csNormLe_mono h3 hKle⟩


/-- **Fixed pipe data**: the constant `C` of the local theorem. -/
theorem local_after_constants (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s)
    (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) (hζ : IsFastProfile ζ) (hΛ : 128 ≤ Λ)
    (hΦ : IsOCStreamSeq α q Λ ζ Φ)
    (hb : ∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x)))
    (hholder : IsHolderDivFreeVelocity α b) {Cb CD cD : ℝ} (hCb : 0 < Cb)
    (hDav : DaviesBody α q Λ Φ b Cb CD cD) (hCD : 0 ≤ CD) (hcD : 0 < cD)
    (hphys : PhysLiftStmt α q Λ Φ b) (htr : LocalTraceStmt α q Λ Φ b)
    (hG : ∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∃ C : ℝ, GlobalWindow α s q Λ b t₀ T C)
    {n : ℕ} (hn : 2 ≤ n) {T R ϱ ϑ : ℝ} (hT : 0 < T) (hR : 0 < R) (hϱ : 0 < ϱ) (hϱ8 : ϱ < 1 / 8)
    (hϑ : 0 < ϑ) (hϑ4 : ϑ < 4) (h8T : 8 * T * ocA α q Λ (n - 2) ≤ ocCStar)
    (hC1 : Cb * max (ocEpsilon q Λ (n - 1) ^ α * T)
      (Real.sqrt (sSup (ocBandSet α q Λ) * T)) ≤ R) (hR8 : R ≤ 1 / 8) :
    ∃ C : ℝ, ∀ t₁ : ℝ, ∀ X : ℝ → Vec 2 → ℝ → Vec 2, IsFlow (streamVel (Φ (n - 2))) X →
      ∀ κ ∈ ocBandSet α q Λ, ∀ θ : ℝ → Vec 2 → ℝ,
        IsLocalEnergySolution b κ (fun t y => X t y t₁) t₁ T R θ →
        ∃ Θ : ℝ → Vec 2 → ℝ, ∀ t ∈ Icc (t₁ - ϑ * T) t₁,
          ContinuousOn (Θ t) ((fun y => X t y t₁) '' euclidBall 0 (ϱ * R)) ∧
          Tendsto (fun σ => ∫ y in euclidBall 0 (ϱ * R), (θ σ (X σ y t₁) - Θ t (X t y t₁)) ^ 2)
            (𝓝[<] t ⊓ ae volume) (𝓝 0) ∧
          ∀ x ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R),
          ∀ y ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R),
          ∀ z ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R), y ≠ z →
            |Θ t x| + |Θ t y - Θ t z| / Real.sqrt (vecNormSq (y - z)) ^ s ≤
              C * Real.sqrt ((volume (outerPipe (fun t y => X t y t₁) t₁ T R)).toReal⁻¹ *
                ∫ p in outerPipe (fun t y => X t y t₁) t₁ T R, θ p.1 p.2 ^ 2) := by
  have hq1 : 1 < q := hq.1
  -- constants of the construction
  obtain ⟨-, Cs, hCs, -, -, htail, -, -, -, -, -, -, hbdd⟩ :=
    stream_tail_bounds α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ b hb
  -- the tube constants
  have hs1 : s < 1 := by linarith
  obtain ⟨c, Ct, hcpos, hCt, hc⟩ := tubeStmt_exists ocMicroscopicStatement_holds hα₀ hholder hs₀
    (a' := (1 + s) / 2) (by linarith) (by linarith)
  -- the numerics
  set V₁ : ℝ := Cs * ocEpsilon q Λ (n - 1) ^ α with hV₁def
  have hV₁ : 0 ≤ V₁ := by
    have := eps_pos (q := q) (Λ := Λ) (m := n - 1) hq1 hΛ
    positivity
  obtain ⟨hd, -, -, -, -⟩ := pipe_numerics hR hR8 hϱ hϱ8
  set d : ℝ := (1 / 8 - ϱ) * R / 2 with hddef
  have hm : 0 < (4 - ϑ) * T := mul_pos (by linarith only [hϑ4]) hT
  set r₀ : ℝ := min (1 / 8) (d / 4) with hr₀def
  set τ₀ : ℝ := min ((4 - ϑ) * T / 2) (d / (12 * (1 + V₁))) with hτ₀def
  have hr₀ : 0 < r₀ := lt_min (by norm_num) (by positivity)
  have hτ₀ : 0 < τ₀ := lt_min (by positivity) (by positivity)
  obtain ⟨Cr, hCr, hCrb⟩ := smoothRadius_bound (α := α) (s := s) (r₀ := r₀) (c := c) (τ₀ := τ₀)
    (D := cD * R ^ 2 / T) hα₀ hs₀ hr₀ hcpos hτ₀ (by positivity)
  -- the global constant
  obtain ⟨Cg₀, hGl⟩ := hG ((4 - ϑ) * T) (5 * T) hm (by nlinarith only [hT, hϑ])
  refine ⟨2 * (Ct * CD * R * Cr + 4 * max Cg₀ 0 * CD * R), fun t₁ X hX κ hκ θ hθ => ?_⟩
  have hGl' : GlobalWindow α s q Λ b ((4 - ϑ) * T) (5 * T) (max Cg₀ 0) := by
    intro a κ' hκ' f hf θ' hθ'
    obtain ⟨Θ, h1, h2⟩ := hGl a κ' hκ' f hf θ' hθ'
    refine ⟨Θ, h1, fun t ht => ?_⟩
    obtain ⟨p1, p2, p3⟩ := h2 t ht
    exact ⟨p1, p2, csNormLe_mono p3 (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.sqrt_nonneg _))⟩
  have hCbκ : ∀ κ ∈ ocBandSet α q Λ, Cb * Real.sqrt (κ * T) ≤ R := by
    intro κ hκ
    have h1 : Real.sqrt (κ * T) ≤ Real.sqrt (sSup (ocBandSet α q Λ) * T) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (band_le_sSup hα₀ hq1 hΛ hκ) hT.le)
    exact (mul_le_mul_of_nonneg_left (h1.trans (le_max_right _ _)) hCb.le).trans hC1
  have hCbε : Cb * (ocEpsilon q Λ (n - 1) ^ α * T) ≤ R :=
    (mul_le_mul_of_nonneg_left (le_max_left _ _) hCb.le).trans hC1
  exact instance_of_tools hα₀ hα₁ hs₀ hs₁ hq hζ hΛ hΦ hholder hDav hCD hphys htr htail hbdd hCs
    hcpos hCt hc hn hT hR hR8 hϱ hϱ8 hϑ hϑ4 h8T hCbε hCbκ (le_max_right _ _) hCr hr₀
    (min_le_right _ _) (min_le_left _ _) hτ₀ (min_le_left _ _) (min_le_right _ _) hCrb hGl' hX hκ hθ

end Instance

/-- **Local interior regularity**, assembled from the global theorem and the three
analytic inputs of its proof (Davies' localization, the physical lift of the difference, the local
traces from below). The conclusion is that of `AVRegularity.local_interior_regularity`. -/
theorem local_interior_regularity_of_tools (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (hglob : OcGlobalStatement α s q ζ)
    (hdav : ∀ Λ : ℕ, 128 ≤ Λ → ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
      ∀ b : ℝ → Vec 2 → Vec 2,
        (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) →
          DaviesStmt α q Λ Φ b)
    (hphys : ∀ Λ : ℕ, 128 ≤ Λ → ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
      ∀ b : ℝ → Vec 2 → Vec 2,
        (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) →
          PhysLiftStmt α q Λ Φ b)
    (htr : ∀ Λ : ℕ, 128 ≤ Λ → ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
      ∀ b : ℝ → Vec 2 → Vec 2,
        (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) →
          LocalTraceStmt α q Λ Φ b) :
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
                          ∫ p in outerPipe (fun t y => X t y t₁) t₁ T R, θ p.1 p.2 ^ 2) := by
  obtain ⟨Λ₀, hΛ₀, Hg⟩ := globalWindow_of_statement hglob
  refine ⟨Λ₀, hΛ₀, fun Λ hΛ Φ hΦ => ?_⟩
  have hΛ128 : 128 ≤ Λ := hΛ₀.trans hΛ
  obtain ⟨b, hb, hholder⟩ :=
    Velocity.exists_limit_velocity α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ128 Φ hΦ
  refine ⟨b, hb, fun cT CT _ _ => ?_⟩
  obtain ⟨Cb, CD, cD, hCb, hCD, hcD, hDav⟩ := daviesBody_of_stmt (hdav Λ hΛ128 Φ hΦ b hb)
  refine ⟨Cb, hCb, fun n T R ϱ ϑ hn hT hR hϱ hϱ8 hϑ hϑ4 _ _ h8T hC1 hR8 => ?_⟩
  exact local_after_constants hα₀ hα₁ hs₀ hs₁ hq hζ hΛ128 hΦ hb hholder hCb hDav hCD hcD
    (hphys Λ hΛ128 Φ hΦ b hb) (htr Λ hΛ128 Φ hΦ b hb) (Hg Λ hΛ Φ hΦ b hb) hn hT hR hϱ hϱ8 hϑ hϑ4
    h8T hC1 hR8
end

end AVRegularity.Applications
end
