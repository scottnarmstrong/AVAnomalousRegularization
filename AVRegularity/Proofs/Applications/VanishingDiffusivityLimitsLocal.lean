-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Applications.Microscopic.Main
public import AVRegularity.Applications.Construction
import AVRegularity.Applications.Limits.Comparison
public import AVRegularity.Applications.LimitsLocal.Kern
public import AVRegularity.External.Campanato.Holder
import AVRegularity.Applications.Davies.LocalTrace
import AVRegularity.Applications.LimitsLocal.Main
import AVRegularity.Applications.Local.Assembly
import AVRegularity.Applications.LocalPhys.Main
import AVRegularity.Applications.Transfer.Main
import AVRegularity.Velocity.ExistsLimitVelocity
import Mathlib.Tactic.Monotonicity.Lemmas

@[expose] public section

section
open MeasureTheory Filter Topology Homogenization AVRegularity.Applications
open AVRegularity.External.Campanato
namespace AVRegularity.Providers

/-! The microscopic oscillation lemma.
Proved unconditionally. -/

/-- **Microscopic oscillation**: the Hölder estimate, with the trace clause, for weak solutions of
    perturbed heat equations on the unit cylinder, for every Hölder exponent `a' ∈ (0, 1)`.
    Lemma 3.3 of the paper follows from it. -/
theorem oc_microscopic (a' : ℝ) (ha₀ : 0 < a') (ha₁ : a' < 1) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧
      ∀ (K : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (d : ℝ × Vec 2 → Vec 2)
        (U : ℝ × Vec 2 → ℝ) (DU : ℝ × Vec 2 → Vec 2),
        (∀ i j : Fin 2, AEStronglyMeasurable (fun p => K p i j) (volume.restrict (openCyl 0 1))) →
        (∀ i : Fin 2, AEStronglyMeasurable (fun p => d p i) (volume.restrict (openCyl 0 1))) →
        (∀ᵐ p ∂(volume.restrict (openCyl 0 1)), (K p).transpose = -K p) →
        (∃ kK kd : ℝ, 0 ≤ kK ∧ 0 ≤ kd ∧ kK + kd ≤ η ∧
          ∀ᵐ p ∂(volume.restrict (openCyl 0 1)),
            (∀ e : Vec 2, vecNormSq ((K p).mulVec e) ≤ kK ^ 2 * vecNormSq e) ∧
            vecNormSq (d p) ≤ kd ^ 2) →
        IsDivFreeQ1 d → IsEnergyClassQ1 U DU → IsSkewDriftWeak K d U DU →
        ∃ Ut : ℝ × Vec 2 → ℝ,
          ContinuousOn Ut (cylinder 0 (1 / 2)) ∧
          Ut =ᵐ[volume.restrict (cylinder 0 (1 / 2))] U ∧
          Tendsto (fun τ => ∫ y in euclidBall 0 (1 / 2), (U (τ, y) - Ut (0, y)) ^ 2)
            (𝓝[<] 0 ⊓ ae volume) (𝓝 0) ∧
          ∀ c : ℝ, ∀ x ∈ cylinder 0 (1 / 2), ∀ z ∈ cylinder 0 (1 / 2),
            ∀ w ∈ cylinder 0 (1 / 2), z ≠ w →
              |Ut z - Ut w| / parabolicHolderDistance z w ^ a' + |Ut x - cylinderMean U 0 1|
                ≤ C * Real.sqrt (⨍ p in openCyl 0 1, (U p - c) ^ 2) :=
  ocMicroscopicStatement_holds a' ha₀ ha₁

end AVRegularity.Providers
end

section
open MeasureTheory Filter Topology Homogenization AVenhance AVRegularity.Applications
namespace AVRegularity.Providers

/-! The full-velocity consequence of the microscopic oscillation lemma. Proved unconditionally
from the translating-tube
regularity `tube_regularity`, the microscopic oscillation lemma, and the Hölder structure of the
limit velocity. -/

/-- **Microscopic oscillation, full-velocity consequence**: local weak solutions of the equation
    with the limit velocity `b` are Hölder continuous on the translating tubes of radius
    `r ≤ c κ^{1/(1+α)}`, with the bound `C r^{-1-s} A`. -/
theorem oc_microscopic_tube (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (Φ : ℕ → ℝ → Vec 2 → ℝ) (hΦ : IsOCStreamSeq α q Λ ζ Φ)
    (b : ℝ → Vec 2 → Vec 2) (hb : ∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x)))
    (a' : ℝ) (hsa : s < a') (ha₁ : a' < 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
      ∀ κ : ℝ, 0 < κ → ∀ O : Set (ℝ × Vec 2), IsOpen O →
      ∀ (w : ℝ × Vec 2 → ℝ) (Dw : ℝ × Vec 2 → Vec 2), IsLocalWeakSolution b κ O w Dw →
      ∀ A : ℝ, 0 ≤ A →
        (∀ᵐ τ ∂(volume : Measure ℝ), IntegrableOn (fun y => w (τ, y) ^ 2) (timeSection O τ) ∧
          ∫ y in timeSection O τ, w (τ, y) ^ 2 ≤ A ^ 2) →
      ∀ r : ℝ, 0 < r → r ≤ 1 / 8 → r ≤ c * κ ^ (1 / (1 + α)) →
      ∀ (t : ℝ) (Kt : Set (Vec 2)),
        (∀ x ∈ Kt, ∀ X : ℝ → Vec 2, IsBackwardTrajectory b X t (r ^ 2 / κ) → X t = x →
          closedTube X t r κ ⊆ O) →
        ∃ W : Vec 2 → ℝ,
          ContinuousOn W (⋃ x ∈ Kt, euclidBall x (r / 4)) ∧
          (∀ x ∈ Kt, Tendsto (fun τ => ∫ y in euclidBall x (r / 4), (w (τ, y) - W y) ^ 2)
            (𝓝[<] t ⊓ ae volume) (𝓝 0)) ∧
          ∀ x ∈ Kt, ∀ y ∈ Kt, ∀ z ∈ Kt, y ≠ z →
            |W x| + |W y - W z| / Real.sqrt (vecNormSq (y - z)) ^ s ≤ C * r ^ (-1 - s) * A :=
  tube_regularity ocMicroscopicStatement_holds hα₀ (by linarith)
    (limit_isHolderDivFree α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ b hb) hs₀ hsa ha₁

end AVRegularity.Providers
end

section
open MeasureTheory Filter Topology Homogenization AVenhance
namespace AVRegularity.Providers

/-! # Vanishing-diffusivity limits, global part (conditional on the global statement)

Proof of `AVRegularity.vanishing_diffusivity_limits`, from which Corollary D(a) of the paper
follows. The theorem here is conditional on the global interior regularity statement
`OcGlobalStatement`. -/

open AVRegularity.Applications

theorem csNormLe_mono {s : ℝ} {g : Vec 2 → ℝ} {K K' : ℝ} (h : CsNormLe s g K) (hK : K ≤ K') :
    CsNormLe s g K' := fun x y z hyz => (h x y z hyz).trans hK

/-- **Vanishing-diffusivity limits, global part**, conditional on `OcGlobalStatement`. -/
theorem vanishing_diffusivity_limits_of_global (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (hglob : AVRegularity.Applications.OcGlobalStatement α s q ζ) :
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
                  Tendsto (fun i => ∫ p, (θ i p.1 p.2 - θ' i p.1 p.2) * φ p) atTop (𝓝 0)) := by
  obtain ⟨Λg, hΛg128, hg⟩ := hglob
  refine ⟨max Λg 128, le_max_right _ _, fun Λ hΛ Φ hΦ => ?_⟩
  have hΛ128 : 128 ≤ Λ := (le_max_right _ _).trans hΛ
  have hΛg : Λg ≤ Λ := (le_max_left _ _).trans hΛ
  obtain ⟨b, hbΦ, hbH⟩ := Velocity.exists_limit_velocity α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ
    hΛ128 Φ hΦ
  refine ⟨b, hbΦ, ?_⟩
  have hC : ∀ t₀ T : ℝ, ∃ C : ℝ, 0 < t₀ → t₀ < T → ∀ a : ℝ, ∀ κ ∈ ocBandSet α q Λ,
      ∀ f : Vec 2 → ℝ, MemL2On unitCube f → ∀ θ : ℝ → Vec 2 → ℝ,
      IsWeakSolutionOn b κ a (a + T) f θ → ∃ Θ : ℝ → Vec 2 → ℝ,
        ContinuousOn (fun p : ℝ × Vec 2 => Θ p.1 p.2) (Set.Icc (a + t₀) (a + T) ×ˢ Set.univ) ∧
        ∀ t ∈ Set.Icc (a + t₀) (a + T), IsZ2Periodic (Θ t) ∧
          Θ t =ᵐ[volume.restrict unitCube] θ t ∧ CsNormLe s (Θ t) (C * Real.sqrt (l2NormSq f)) := by
    intro t₀ T
    by_cases h : 0 < t₀ ∧ t₀ < T
    · obtain ⟨C, hC⟩ := hg Λ hΛg Φ hΦ b hbΦ t₀ T h.1 h.2
      exact ⟨C, fun _ _ => hC⟩
    · exact ⟨0, fun h0 h1 => absurd ⟨h0, h1⟩ h⟩
  choose C0 hC0 using hC
  refine ⟨fun t₀ T => max (C0 t₀ T) 0, ?_⟩
  intro a F κ f θ hκband hκ hf hθ
  have hF : 0 ≤ F := (Real.sqrt_nonneg _).trans (hf 0).2
  have hq1 : 1 < q := hq.1
  have hκpos : ∀ i, 0 < κ i := by
    intro i
    obtain ⟨M, hM⟩ := Set.mem_iUnion.1 (hκband i)
    obtain ⟨hM1, hmem⟩ := Set.mem_iUnion.1 hM
    have := (Scales.epsilon_basic (m := M) hq1 hΛ128).1
    exact lt_of_lt_of_le (by positivity) hmem.1
  have hb := isContDrift_of_holder hα₀ hbH
  have hrep : ∀ i, ∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∃ Θ : ℝ → Vec 2 → ℝ,
      ContinuousOn (fun p : ℝ × Vec 2 => Θ p.1 p.2) (Set.Icc (a + t₀) (a + T) ×ˢ Set.univ) ∧
      ∀ t ∈ Set.Icc (a + t₀) (a + T), IsZ2Periodic (Θ t) ∧
        Θ t =ᵐ[volume.restrict unitCube] θ i t ∧
        CsNormLe s (Θ t) (max (C0 t₀ T) 0 * F) := by
    intro i t₀ T h0 h1
    obtain ⟨Θ, hc, h⟩ := hC0 t₀ T h0 h1 a (κ i) (hκband i) (f i) (hf i).1 (θ i) (hθ i T (by linarith))
    refine ⟨Θ, hc, fun t ht => ⟨(h t ht).1, (h t ht).2.1, csNormLe_mono (h t ht).2.2 ?_⟩⟩
    have hs0 : 0 ≤ Real.sqrt (l2NormSq (f i)) := Real.sqrt_nonneg _
    calc C0 t₀ T * Real.sqrt (l2NormSq (f i)) ≤ max (C0 t₀ T) 0 * Real.sqrt (l2NormSq (f i)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hs0
      _ ≤ max (C0 t₀ T) 0 * F := mul_le_mul_of_nonneg_left (hf i).2 (le_max_right _ _)
  obtain ⟨σ, fstar, Θ, θstar, hσ, hfs, hweak, hΘ, hconv, hdist, htrace, hCs, hHol⟩ :=
    limits_core hα₀ hs₀ hbH a F hF (fun t₀ T => max (C0 t₀ T) 0 * F) κ hκpos hκ f hf θ hθ hrep
  exact ⟨σ, fstar, Θ, θstar, hσ, hfs, hweak, hΘ, hconv, hdist, htrace, hCs, hHol,
    fun Mi θ' hMi hθ' φ hφ hφc hts =>
      matched_comparison α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ128 Φ hΦ b hbΦ hb a F hF κ f θ hκ hf hθ
        Mi θ' hMi hθ' φ hφ hφc hts⟩

end AVRegularity.Providers
end

section
open MeasureTheory Filter Topology Homogenization AVenhance AVRegularity.Applications
namespace AVRegularity.Providers

/-! The global statement `OcGlobalStatement` from the finite-level statement.

This section proves the reduction **finite ⇒ global** with the finite-level statement
`OcFiniteStatement` as an explicit hypothesis; the transfer and the compact-range estimate are
proved. -/

/-- **finite ⇒ global** (a conditional theorem): `OcGlobalStatement` follows from
`OcFiniteStatement`. -/
theorem oc_global_of_finite (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (hfin : OcFiniteStatement α s q ζ) :
    OcGlobalStatement α s q ζ :=
  oc_global_of_finite_transfer_compact α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ hfin
    (transfer_holds s hs₀ (by linarith)) (compactRange_holds hα₀ (by linarith) hs₀ (by linarith))

/-! Proof of the local interior regularity theorem, conditional on the global statement
`OcGlobalStatement`.

`local_interior_regularity_of_global` has exactly the conclusion of the theorem; the global theorem enters
only as the explicit hypothesis `OcGlobalStatement`. The Davies localization, the physical lift
of the comparison difference and the local traces are proved. -/

/-- **Local interior regularity from the global theorem** (a conditional theorem): the
conclusion of `local_interior_regularity`, given `OcGlobalStatement`. -/
theorem local_interior_regularity_of_global (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (hglob : OcGlobalStatement α s q ζ) :
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
  local_interior_regularity_of_tools α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ hglob
    (fun Λ hΛ Φ hΦ b hb => davies_holds α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ b hb)
    (fun Λ hΛ Φ hΦ b hb => physLift_holds α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ b hb)
    (fun Λ hΛ Φ hΦ b hb => localTrace_holds α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ b hb)

end AVRegularity.Providers
end

section
open MeasureTheory Filter Topology Homogenization AVenhance AVRegularity
namespace AVRegularity.Providers

/-! Proof of `vanishing_diffusivity_limits_local`.


`vanishing_diffusivity_limits_local_of_local` (re-exported) has exactly the conclusion of the theorem and
takes the statement `OcLocalStatement` of the local theorem as its only extra hypothesis;
`vanishing_diffusivity_limits_local_of_global` has the same conclusion, conditional on the
global statement `OcGlobalStatement` only (the local theorem being assembled from it). -/

export AVRegularity.Applications (vanishing_diffusivity_limits_local_of_local)

/-- The statement of the local theorem follows from that of the global theorem. -/
theorem ocLocalStatement_of_global (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (hglob : AVRegularity.Applications.OcGlobalStatement α s q ζ) :
    AVRegularity.Applications.OcLocalStatement α s q ζ :=
  local_interior_regularity_of_global α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ hglob

/-- **Vanishing-diffusivity limits, local part**, conditional on `OcGlobalStatement`. -/
theorem vanishing_diffusivity_limits_local_of_global (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ)
    (hglob : AVRegularity.Applications.OcGlobalStatement α s q ζ) :
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
  AVRegularity.Applications.vanishing_diffusivity_limits_local_of_local α s hα₀ hα₁ hs₀ hs₁ q hq ζ
    hζ (ocLocalStatement_of_global α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ hglob)

end AVRegularity.Providers
end
