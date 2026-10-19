-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Applications.Construction.StreamTail
public import AVRegularity.Applications.Pipe.PushTest
public import AVRegularity.Applications.TorusEnergy.LocalInt
import AVRegularity.Applications.LocalEnergy.Mollifier
import AVRegularity.Applications.Microscopic.DilationTests
import AVRegularity.Velocity.Port.MaterialGoalSource
import AVenhance.Infra.Construction.StreamAdmissible
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.UniformSpace.Uniformizable

section
@[expose] public section
namespace AVRegularity.Applications.Davies

/-! # Real-number bookkeeping for the Davies localization -/

theorem srcBound_alg {κ T R N V₀ Kb Ef SD IG IGf : ℝ} (hT : 0 < T) (hκ : 0 < κ) (hKb : 0 ≤ Kb)
    (hIG0 : 0 ≤ IG) (hIGf0 : 0 ≤ IGf) (hκT : κ * T ≤ R ^ 2)
    (hVT : (V₀ * T) ^ 2 ≤ R ^ 2) (hEf : Ef ≤ 625 * Kb) (hS : SD ≤ 9 * T * Kb + 729 * T * Ef)
    (hIG : κ * IG ≤ Kb) (hIGf : κ * IGf ≤ 162 * Ef) :
    (729 / 8 * κ * N ^ 2 + T * (2 * V₀ ^ 2 * N ^ 2)) * SD +
      T * (9 * κ ^ 2 * N ^ 2) * (IG + 9 / 4 * IGf) ≤ 50000000 * (N * R) ^ 2 * Kb := by
  have hS' : SD ≤ 455634 * T * Kb := by nlinarith
  have hc1 : 0 ≤ 729 / 8 * κ * N ^ 2 + T * (2 * V₀ ^ 2 * N ^ 2) := by positivity
  have hN2 : 0 ≤ N ^ 2 := sq_nonneg N
  have h1 : (729 / 8 * κ * N ^ 2 + T * (2 * V₀ ^ 2 * N ^ 2)) * SD ≤
      (729 / 8 * κ * N ^ 2 + T * (2 * V₀ ^ 2 * N ^ 2)) * (455634 * T * Kb) :=
    mul_le_mul_of_nonneg_left hS' hc1
  have h2 : (729 / 8 * κ * N ^ 2 + T * (2 * V₀ ^ 2 * N ^ 2)) * (455634 * T * Kb) =
      455634 * Kb * N ^ 2 * (729 / 8 * (κ * T) + 2 * (V₀ * T) ^ 2) := by ring
  have h3 : 729 / 8 * (κ * T) + 2 * (V₀ * T) ^ 2 ≤ 729 / 8 * R ^ 2 + 2 * R ^ 2 := by nlinarith
  have h4 : 455634 * Kb * N ^ 2 * (729 / 8 * (κ * T) + 2 * (V₀ * T) ^ 2) ≤
      455634 * Kb * N ^ 2 * (729 / 8 * R ^ 2 + 2 * R ^ 2) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  have h5 : κ * (IG + 9 / 4 * IGf) ≤ Kb + 9 / 4 * (162 * Ef) := by nlinarith
  have h6 : κ * (IG + 9 / 4 * IGf) ≤ 227815 * Kb := by nlinarith
  have h7 : T * (9 * κ ^ 2 * N ^ 2) * (IG + 9 / 4 * IGf) =
      9 * (κ * T) * N ^ 2 * (κ * (IG + 9 / 4 * IGf)) := by ring
  have h8 : 9 * (κ * T) * N ^ 2 * (κ * (IG + 9 / 4 * IGf)) ≤
      9 * R ^ 2 * N ^ 2 * (227815 * Kb) := by
    have hk : 0 ≤ κ * (IG + 9 / 4 * IGf) := by positivity
    calc 9 * (κ * T) * N ^ 2 * (κ * (IG + 9 / 4 * IGf))
        ≤ 9 * R ^ 2 * N ^ 2 * (κ * (IG + 9 / 4 * IGf)) := by
          apply mul_le_mul_of_nonneg_right _ hk
          nlinarith
      _ ≤ 9 * R ^ 2 * N ^ 2 * (227815 * Kb) :=
          mul_le_mul_of_nonneg_left h6 (by positivity)
  have hRN : (N * R) ^ 2 = N ^ 2 * R ^ 2 := by ring
  rw [hRN]
  have hNRK : 0 ≤ N ^ 2 * R ^ 2 * Kb := by positivity
  nlinarith [h1, h2, h4, h7, h8]

theorem exponent_alg {κ T R V₀ ca : ℝ} (hκ : 0 < κ) (hT : 0 < T)
    (hVT : (V₀ * T) ^ 2 ≤ ca ^ 2 / 12960 * R ^ 2) :
    2 * (10 * κ * ((ca / 90 * R / (κ * T)) ^ 2) + 8 * V₀ ^ 2 / κ + (1 / T) / 2) * (9 * T / 2) -
        2 * (ca / 90 * R / (κ * T)) * (ca * R) ≤ 9 / 2 - ca ^ 2 / 180 * (R ^ 2 / (κ * T)) := by
  have hkT : 0 < κ * T := mul_pos hκ hT
  have e1 : 2 * (10 * κ * ((ca / 90 * R / (κ * T)) ^ 2) + 8 * V₀ ^ 2 / κ + (1 / T) / 2) *
        (9 * T / 2) - 2 * (ca / 90 * R / (κ * T)) * (ca * R) =
      9 / 2 + (ca ^ 2 / 90 - 2 * ca ^ 2 / 90) * (R ^ 2 / (κ * T)) +
        72 * ((V₀ * T) ^ 2 / (κ * T)) := by
    field_simp
    ring
  have e2 : 72 * ((V₀ * T) ^ 2 / (κ * T)) ≤ 72 * (ca ^ 2 / 12960 * R ^ 2 / (κ * T)) := by
    have := div_le_div_of_nonneg_right hVT hkT.le
    linarith
  have e3 : 72 * (ca ^ 2 / 12960 * R ^ 2 / (κ * T)) = ca ^ 2 / 180 * (R ^ 2 / (κ * T)) := by
    field_simp; ring
  rw [e1]
  nlinarith [e2, e3]

theorem step1_alg {κ T R L Lm V₀ M A : ℝ} (hκ : 0 ≤ κ) (hT : 0 < T) (hR : 0 < R) (hL : 0 ≤ L)
    (hLm : L ≤ Lm) (hV₀ : 0 ≤ V₀) (hM : M ≤ 32 * T * R ^ 2 * A ^ 2)
    (hκT : κ * T ≤ R ^ 2) (hVT : V₀ * T ≤ R) :
    (1 / (2 * T) + (9 * κ * (L / R) ^ 2 + 2 * V₀ * (L / R))) * M ≤
      (16 + 288 * Lm ^ 2 + 64 * Lm) * (R ^ 2 * A ^ 2) := by
  have hc : 0 ≤ 1 / (2 * T) + (9 * κ * (L / R) ^ 2 + 2 * V₀ * (L / R)) := by positivity
  have h1 : (1 / (2 * T) + (9 * κ * (L / R) ^ 2 + 2 * V₀ * (L / R))) * M ≤
      (1 / (2 * T) + (9 * κ * (L / R) ^ 2 + 2 * V₀ * (L / R))) * (32 * T * R ^ 2 * A ^ 2) :=
    mul_le_mul_of_nonneg_left hM hc
  have e : (1 / (2 * T) + (9 * κ * (L / R) ^ 2 + 2 * V₀ * (L / R))) * (32 * T * R ^ 2 * A ^ 2) =
      (16 + 288 * L ^ 2 * (κ * T) / R ^ 2 + 64 * L * (V₀ * T) / R) * (R ^ 2 * A ^ 2) := by
    field_simp
    ring
  have h2 : 288 * L ^ 2 * (κ * T) / R ^ 2 ≤ 288 * Lm ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have : L ^ 2 ≤ Lm ^ 2 := pow_le_pow_left₀ hL hLm 2
    nlinarith [mul_nonneg hκ hT.le, sq_nonneg L]
  have h3 : 64 * L * (V₀ * T) / R ≤ 64 * Lm := by
    rw [div_le_iff₀ hR]
    have : L * (V₀ * T) ≤ Lm * R := mul_le_mul hLm hVT (by positivity) (hL.trans hLm)
    nlinarith
  have hA : 0 ≤ R ^ 2 * A ^ 2 := by positivity
  calc _ ≤ _ := h1
    _ = _ := e
    _ ≤ (16 + 288 * Lm ^ 2 + 64 * Lm) * (R ^ 2 * A ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) hA

end AVRegularity.Applications.Davies
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.Applications

/-! # Radial cutoffs and their scalings

`cutProfile a b` is a smooth radial profile equal to `1` on `|y| ≤ a` and `0` for `|y| ≥ b`;
`scaleFn c R y = c (R⁻¹ y)`. A gradient bound `L` for `c` gives the bound `L/R` for `scaleFn c R`. -/

/-- The radial profile `smoothTransition ((b² - |y|²)/(b² - a²))`. -/
def cutProfile (a b : ℝ) (y : Vec 2) : ℝ :=
  Real.smoothTransition ((b ^ 2 - vecNormSq y) / (b ^ 2 - a ^ 2))

theorem contDiff_vecNormSq_top : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => vecNormSq y) := by
  unfold vecNormSq vecDot
  exact ContDiff.sum fun i _ => ((contDiff_apply ℝ ℝ i).mul (contDiff_apply ℝ ℝ i))

theorem contDiff_cutProfile (a b : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (cutProfile a b) := by
  unfold cutProfile
  exact Real.smoothTransition.contDiff.comp
    ((contDiff_const.sub contDiff_vecNormSq_top).div_const _)

theorem cutProfile_nonneg (a b : ℝ) (y : Vec 2) : 0 ≤ cutProfile a b y :=
  Real.smoothTransition.nonneg _

theorem cutProfile_le_one (a b : ℝ) (y : Vec 2) : cutProfile a b y ≤ 1 :=
  Real.smoothTransition.le_one _

theorem cutProfile_eq_one {a b : ℝ} (hab : a < b) (ha : 0 ≤ a) {y : Vec 2}
    (h : vecNormSq y ≤ a ^ 2) : cutProfile a b y = 1 := by
  unfold cutProfile
  apply Real.smoothTransition.one_of_one_le
  have : 0 < b ^ 2 - a ^ 2 := by nlinarith
  rw [le_div_iff₀ this]
  linarith

theorem cutProfile_eq_zero {a b : ℝ} (hab : a < b) (ha : 0 ≤ a) {y : Vec 2}
    (h : b ^ 2 ≤ vecNormSq y) : cutProfile a b y = 0 := by
  unfold cutProfile
  apply Real.smoothTransition.zero_of_nonpos
  have : 0 < b ^ 2 - a ^ 2 := by nlinarith
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) this.le

theorem isCompact_vecNormSq_le (r : ℝ) : IsCompact {y : Vec 2 | vecNormSq y ≤ r} := by
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_le contDiff_vecNormSq_top.continuous continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : Vec 2)) (r := max 1 r)).subset ?_
    intro y hy
    simp only [Set.mem_ofPred_eq, vecNormSq, vecDot, Fin.sum_univ_two] at hy
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (le_trans zero_le_one (le_max_left _ _))]
    intro i
    rw [Real.norm_eq_abs]
    have h0 := sq_nonneg (y 0)
    have h1 := sq_nonneg (y 1)
    have hy' : y i * y i ≤ r := by fin_cases i <;> simp <;> nlinarith
    have hr := le_max_right 1 r
    have h1' := le_max_left 1 r
    apply abs_le_of_sq_le_sq' _ (by linarith) |>.2
    nlinarith [sq_abs (y i)]

theorem cutProfile_compactSupport {a b : ℝ} (hab : a < b) (ha : 0 ≤ a) :
    HasCompactSupport (cutProfile a b) :=
  HasCompactSupport.intro (isCompact_vecNormSq_le (b ^ 2)) fun _ hy =>
    cutProfile_eq_zero hab ha (not_le.1 hy).le

/-- A uniform gradient bound for a smooth compactly supported function. -/
theorem exists_grad_bound {c : Vec 2 → ℝ} (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcs : HasCompactSupport c) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ y, vecNormSq (spGrad c y) ≤ L ^ 2 := by
  have hb : ∀ i : Fin 2, ∃ C : ℝ, ∀ y, ‖spGrad c y i‖ ≤ C := by
    intro i
    have hcont : Continuous fun y => spGrad c y i :=
      (contDiff_fderiv_apply_of_smooth hc (basisVec i)).continuous
    exact hcont.bounded_above_of_compact_support (hasCompactSupport_fderiv_apply hcs _)
  obtain ⟨C0, hC0⟩ := hb 0
  obtain ⟨C1, hC1⟩ := hb 1
  refine ⟨2 * (|C0| + |C1|), by positivity, fun y => ?_⟩
  have h0 := (hC0 y).trans (le_abs_self C0)
  have h1 := (hC1 y).trans (le_abs_self C1)
  simp only [vecNormSq, vecDot, Fin.sum_univ_two]
  rw [Real.norm_eq_abs] at h0 h1
  have := sq_abs (spGrad c y 0)
  have := sq_abs (spGrad c y 1)
  nlinarith [abs_nonneg C0, abs_nonneg C1, abs_nonneg (spGrad c y 0), abs_nonneg (spGrad c y 1)]

/-- Dilation `y ↦ c (R⁻¹ y)`. -/
def scaleFn (c : Vec 2 → ℝ) (R : ℝ) (y : Vec 2) : ℝ := c (R⁻¹ • y)

theorem contDiff_scaleFn {c : Vec 2 → ℝ} (hc : ContDiff ℝ (⊤ : ℕ∞) c) (R : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (scaleFn c R) :=
  hc.comp (contDiff_const_smul R⁻¹)

theorem spGrad_scaleFn {c : Vec 2 → ℝ} (hc : ContDiff ℝ (⊤ : ℕ∞) c) (R : ℝ) (y : Vec 2) :
    spGrad (scaleFn c R) y = R⁻¹ • spGrad c (R⁻¹ • y) := by
  ext i
  have hd : DifferentiableAt ℝ c (R⁻¹ • y) := (hc.differentiable (by simp)) _
  have h := (hd.hasFDerivAt.comp y ((hasFDerivAt_id y).const_smul R⁻¹))
  simp only [spGrad]
  change fderiv ℝ (c ∘ fun z => R⁻¹ • z) y (basisVec i) = _
  rw [h.fderiv]
  simp [Pi.smul_apply, smul_eq_mul, spGrad]

theorem vecNormSq_spGrad_scaleFn_le {c : Vec 2 → ℝ} (hc : ContDiff ℝ (⊤ : ℕ∞) c) {L : ℝ}
    (hL : ∀ y, vecNormSq (spGrad c y) ≤ L ^ 2) (R : ℝ) (y : Vec 2) :
    vecNormSq (spGrad (scaleFn c R) y) ≤ (R⁻¹) ^ 2 * L ^ 2 := by
  rw [spGrad_scaleFn hc, vecNormSq_smul]
  exact mul_le_mul_of_nonneg_left (hL _) (sq_nonneg _)

end AVRegularity.Applications
end
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization Matrix
namespace AVRegularity.Applications.Davies

/-! # Elementary algebra for the Davies localization

Euclidean norm facts on `Vec 2`, the Cauchy-Schwarz inequality for symmetric positive
semidefinite matrices and slice measure theory on cylinders `(a,b) × B`. -/

theorem vecDot_comm (x y : Vec 2) : vecDot x y = vecDot y x := by
  simp [vecDot, mul_comm]

theorem vecDot_add_left (x y z : Vec 2) : vecDot (x + y) z = vecDot x z + vecDot y z := by
  simp [vecDot, add_mul, Finset.sum_add_distrib]

theorem vecDot_add_right (x y z : Vec 2) : vecDot x (y + z) = vecDot x y + vecDot x z := by
  simp [vecDot, mul_add, Finset.sum_add_distrib]

theorem vecDot_smul_left (c : ℝ) (x y : Vec 2) : vecDot (c • x) y = c * vecDot x y := by
  simp [vecDot, Fin.sum_univ_two]; ring

theorem vecDot_smul_right (c : ℝ) (x y : Vec 2) : vecDot x (c • y) = c * vecDot x y := by
  rw [vecDot_comm, vecDot_smul_left, vecDot_comm]

theorem vecDot_mulVec_left (A : Matrix (Fin 2) (Fin 2) ℝ) (w g : Vec 2) :
    vecDot (A.mulVec w) g = vecDot w (Aᵀ.mulVec g) := by
  change (A.mulVec w) ⬝ᵥ g = w ⬝ᵥ (Aᵀ.mulVec g)
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_comm]

theorem abs_coord_le_sqrt (e : Vec 2) (i : Fin 2) : |e i| ≤ Real.sqrt (vecNormSq e) := by
  have := norm_le_sqrt_vecNormSq e
  have h2 := norm_le_pi_norm e i
  rw [Real.norm_eq_abs] at h2
  exact h2.trans this

theorem abs_vecDot_le (a b : Vec 2) :
    |vecDot a b| ≤ Real.sqrt (vecNormSq a) * Real.sqrt (vecNormSq b) :=
  abs_vecDot_le_sqrt_mul a b

/-- Cauchy-Schwarz for a symmetric matrix with `e·Ge ≥ 0`. -/
theorem cauchy_symm {G : Matrix (Fin 2) (Fin 2) ℝ} (hs : Gᵀ = G)
    (hp : ∀ e, 0 ≤ vecDot e (G.mulVec e)) (a b : Vec 2) :
    vecDot a (G.mulVec b) ^ 2 ≤ vecDot a (G.mulVec a) * vecDot b (G.mulVec b) := by
  have hsym : vecDot b (G.mulVec a) = vecDot a (G.mulVec b) := by
    rw [vecDot_comm, vecDot_mulVec_left, hs]
  have hq : ∀ s : ℝ, 0 ≤ vecDot b (G.mulVec b) * (s * s) + 2 * vecDot a (G.mulVec b) * s +
      vecDot a (G.mulVec a) := by
    intro s
    have h := hp (a + s • b)
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, vecDot_add_left, vecDot_add_right,
      vecDot_add_right, vecDot_smul_left, vecDot_smul_right, vecDot_smul_left,
      vecDot_smul_right, hsym] at h
    nlinarith [h]
  have := discrim_le_zero hq
  unfold discrim at this
  nlinarith [this]

end AVRegularity.Applications.Davies
end
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity Filter Topology
namespace AVRegularity.Applications.Davies

/-! # Facts on the limit velocity and the approximating velocities

For the construction: the limit velocity `b` is a window drift (measurable, bounded, spatially
periodic, divergence free) and the approximating velocity is smooth with divergence free slices. -/

open AVRegularity.Applications

section Construction

variable (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
  (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) (Λ : ℕ)
  (hΛ : 128 ≤ Λ) (Φ : ℕ → ℝ → Vec 2 → ℝ) (hΦ : IsOCStreamSeq α q Λ ζ Φ)

include hα₀ hα₁ hs₀ hs₁ hq hζ hΛ hΦ

omit hα₀ hα₁ hs₀ hs₁ hq in
theorem limit_velocity_periodic (b : ℝ → Vec 2 → Vec 2)
    (hb : ∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) (t : ℝ) :
    IsZ2Periodic (b t) := by
  intro k x
  have hper : ∀ M, streamVel (Φ M) t (x + latticeShift k) = streamVel (Φ M) t x := fun M => by
    have := (AVenhance.Infra.Construction.smoothPeriodic_streamVel
      (AVRegularity.Velocity.streamSeq_admissible hζ hΛ hΦ M)).periodic 0 k t x
    simpa using this
  refine tendsto_nhds_unique (hb t (x + latticeShift k)) ?_
  simp only [hper]
  exact hb t x

theorem limit_window_drift (b : ℝ → Vec 2 → Vec 2)
    (hb : ∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) (t₁ t₂ : ℝ) :
    IsWindowDrift b t₁ t₂ := by
  obtain ⟨hbm, ⟨B, hBb⟩, hdb⟩ := limit_velocity_facts α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ b hb
  exact ⟨hbm, ⟨B, fun t _ x => hBb t x⟩,
    fun t _ => limit_velocity_periodic α q ζ hζ Λ hΛ Φ hΦ b hb t,
    fun t _ φ hφ hφc => hdb t φ hφ hφc⟩

omit hα₀ hα₁ hs₀ hs₁ hq in
theorem approx_velocity_facts (m : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => streamVel (Φ m) p.1 p.2) ∧
      ∀ t x, divSp (streamVel (Φ m) t) x = 0 := by
  have hφ := AVRegularity.Velocity.streamSeq_admissible hζ hΛ hΦ m
  refine ⟨(AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ).smooth, ?_⟩
  intro t x
  have h1 := AVRegularity.Velocity.Port.Section2FlowIdentities.streamVel_spatialDivergence_eq_zero
    hφ t x
  rw [AVRegularity.Velocity.Port.Section2FlowIdentities.spatialDivergence_eq_vecDiv
    (AVenhance.Infra.Construction.smoothPeriodic_streamVel hφ)] at h1
  exact h1

end Construction

end AVRegularity.Applications.Davies
end
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.Applications.Davies

/-! # Slices of functions on cylinders `(a,b) × B` -/

theorem ae_slice_memLp_gen {a b : ℝ} {B : Set (Vec 2)} {f : ℝ × Vec 2 → ℝ}
    (hf : MemLp f 2 (volume.restrict (Set.Ioo a b ×ˢ B))) :
    ∀ᵐ τ ∂(volume.restrict (Set.Ioo a b)),
      MemLp (fun y => f (τ, y)) 2 (volume.restrict B) := by
  have hint : Integrable (fun p => f p ^ 2) (volume.restrict (Set.Ioo a b ×ˢ B)) :=
    hf.integrable_sq
  rw [volume_restrict_prod_eq] at hint
  have h1 := hint.prod_right_ae
  have h2 : AEStronglyMeasurable f ((volume.restrict (Set.Ioo a b)).prod (volume.restrict B)) := by
    have := hf.aestronglyMeasurable
    rwa [volume_restrict_prod_eq] at this
  filter_upwards [h1, h2.prodMk_left] with τ i1 m1
  exact (memLp_two_iff_integrable_sq m1).2 i1

/-- Fubini on `(τ₁, τ₂] × B`. -/
theorem setIntegral_Ioc_prod {τ₁ τ₂ : ℝ} {B : Set (Vec 2)} {F : ℝ × Vec 2 → ℝ}
    (hF : IntegrableOn F (Set.Ioc τ₁ τ₂ ×ˢ B)) :
    ∫ p in Set.Ioc τ₁ τ₂ ×ˢ B, F p = ∫ τ in Set.Ioc τ₁ τ₂, ∫ y in B, F (τ, y) := by
  have h : Integrable F ((volume.restrict (Set.Ioc τ₁ τ₂)).prod (volume.restrict B)) := by
    have := hF
    unfold IntegrableOn at this
    rwa [volume_restrict_prod_eq] at this
  rw [volume_restrict_prod_eq, integral_prod _ h]

theorem ae_Ioc_of_ae_Ioo {a b τ₁ τ₂ : ℝ} (h1 : a ≤ τ₁) (h2 : τ₂ ≤ b) {P : ℝ → Prop}
    (hP : ∀ᵐ τ ∂(volume.restrict (Set.Ioo a b)), P τ) :
    ∀ᵐ τ ∂(volume.restrict (Set.Ioc τ₁ τ₂)), P τ := by
  have hsub : Set.Ioc τ₁ τ₂ ⊆ Set.Ioc a b := Set.Ioc_subset_Ioc h1 h2
  have h3 : ∀ᵐ τ ∂(volume.restrict (Set.Ioc a b)), P τ := by
    rwa [Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm]
  exact ae_restrict_of_ae_restrict_of_subset hsub h3

theorem Ioc_prod_ae_eq_Ioo_prod (a b : ℝ) (B : Set (Vec 2)) :
    (Set.Ioc a b ×ˢ B : Set (ℝ × Vec 2)) =ᵐ[volume] (Set.Ioo a b ×ˢ B : Set (ℝ × Vec 2)) := by
  have := Measure.set_prod_ae_eq (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Vec 2)))
    (Ioo_ae_eq_Ioc (a := a) (b := b)).symm (Filter.EventuallyEq.refl _ B)
  rwa [← Measure.volume_eq_prod] at this

theorem integrableOn_Ioc_of_Ioo {F : ℝ × Vec 2 → ℝ} {a b τ₁ τ₂ : ℝ} {B : Set (Vec 2)}
    (h : IntegrableOn F (Set.Ioo a b ×ˢ B)) (h1 : a ≤ τ₁) (h2 : τ₂ ≤ b) :
    IntegrableOn F (Set.Ioc τ₁ τ₂ ×ˢ B) := by
  have h3 : IntegrableOn F (Set.Ioc a b ×ˢ B) :=
    (integrableOn_congr_set_ae (Ioc_prod_ae_eq_Ioo_prod a b B)).2 h
  exact h3.mono_set (Set.prod_mono (Set.Ioc_subset_Ioc h1 h2) le_rfl)

theorem integrableOn_Ioo_of_Ioo {F : ℝ × Vec 2 → ℝ} {a b τ₁ τ₂ : ℝ} {B : Set (Vec 2)}
    (h : IntegrableOn F (Set.Ioo a b ×ˢ B)) (h1 : a ≤ τ₁) (h2 : τ₂ ≤ b) :
    IntegrableOn F (Set.Ioo τ₁ τ₂ ×ˢ B) :=
  h.mono_set (Set.prod_mono (Set.Ioo_subset_Ioo h1 h2) le_rfl)

theorem setIntegral_Ioc_prod_eq_Ioo {F : ℝ × Vec 2 → ℝ} {a b : ℝ} {B : Set (Vec 2)} :
    ∫ p in Set.Ioc a b ×ˢ B, F p = ∫ p in Set.Ioo a b ×ˢ B, F p :=
  setIntegral_congr_set (Ioc_prod_ae_eq_Ioo_prod a b B)

end AVRegularity.Applications.Davies
end
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization Matrix
namespace AVRegularity.Applications.Davies

/-! # Label coefficients

`LabelCoeffs G V V₀ ta tb` records the properties of the chart coefficients used in the Davies
localization: on `t ∈ [ta, tb]` the matrix `G` is symmetric with `1/4 ≤ G ≤ 9/4` (in the sense of
`pipe_coeff_bounds_uniform`), and `V` is bounded by `V₀` and distributionally divergence free. -/

structure LabelCoeffs (G : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (V : ℝ × Vec 2 → Vec 2)
    (V₀ ta tb : ℝ) : Prop where
  symm : ∀ p, (G p)ᵀ = G p
  ell : ∀ p, p.1 ∈ Set.Icc ta tb → ∀ e, (1 / 4) * vecNormSq e ≤ vecDot e ((G p).mulVec e)
  bdd : ∀ p, p.1 ∈ Set.Icc ta tb → ∀ e, vecNormSq ((G p).mulVec e) ≤ (9 / 4) ^ 2 * vecNormSq e
  Gmeas : ∀ i j : Fin 2, Measurable fun p => G p i j
  Vmeas : Measurable V
  V0 : 0 ≤ V₀
  Vbd : ∀ p, p.1 ∈ Set.Icc ta tb → vecNormSq (V p) ≤ V₀ ^ 2
  Vdiv : ∀ t ∈ Set.Icc ta tb, ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
    ∫ y, vecDot (V (t, y)) (spGrad ψ y) = 0

theorem LabelCoeffs.mono {G V V₀ ta tb ta' tb'} (h : LabelCoeffs G V V₀ ta tb)
    (h1 : ta ≤ ta') (h2 : tb' ≤ tb) : LabelCoeffs G V V₀ ta' tb' :=
  ⟨h.symm, fun p hp => h.ell p ⟨h1.trans hp.1, hp.2.trans h2⟩,
    fun p hp => h.bdd p ⟨h1.trans hp.1, hp.2.trans h2⟩, h.Gmeas, h.Vmeas, h.V0,
    fun p hp => h.Vbd p ⟨h1.trans hp.1, hp.2.trans h2⟩,
    fun t ht => h.Vdiv t ⟨h1.trans ht.1, ht.2.trans h2⟩⟩

theorem LabelCoeffs.psd {G V V₀ ta tb} (h : LabelCoeffs G V V₀ ta tb) {p : ℝ × Vec 2}
    (hp : p.1 ∈ Set.Icc ta tb) (e : Vec 2) : 0 ≤ vecDot e ((G p).mulVec e) := by
  have := h.ell p hp e
  have := vecNormSq_nonneg e
  linarith

theorem LabelCoeffs.cs {G V V₀ ta tb} (h : LabelCoeffs G V V₀ ta tb) {p : ℝ × Vec 2}
    (hp : p.1 ∈ Set.Icc ta tb) (a b : Vec 2) :
    vecDot a ((G p).mulVec b) ^ 2 ≤ vecDot a ((G p).mulVec a) * vecDot b ((G p).mulVec b) :=
  cauchy_symm (h.symm p) (fun e => h.psd hp e) a b

/-- `n·Gn ≤ (9/4) |n|²`. -/
theorem LabelCoeffs.quad_le {G V V₀ ta tb} (h : LabelCoeffs G V V₀ ta tb) {p : ℝ × Vec 2}
    (hp : p.1 ∈ Set.Icc ta tb) (n : Vec 2) :
    vecDot n ((G p).mulVec n) ≤ (9 / 4) * vecNormSq n := by
  have h1 := abs_vecDot_le n ((G p).mulVec n)
  have h2 := h.bdd p hp n
  have h3 : Real.sqrt (vecNormSq ((G p).mulVec n)) ≤ (9 / 4) * Real.sqrt (vecNormSq n) := by
    apply Real.sqrt_le_iff.2
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (vecNormSq_nonneg n)]
    exact h2
  have h4 : Real.sqrt (vecNormSq n) * Real.sqrt (vecNormSq ((G p).mulVec n)) ≤
      Real.sqrt (vecNormSq n) * ((9 / 4) * Real.sqrt (vecNormSq n)) :=
    mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)
  have h5 : Real.sqrt (vecNormSq n) * ((9 / 4) * Real.sqrt (vecNormSq n)) =
      (9 / 4) * vecNormSq n := by
    have := Real.mul_self_sqrt (vecNormSq_nonneg n)
    nlinarith
  calc vecDot n ((G p).mulVec n) ≤ |vecDot n ((G p).mulVec n)| := le_abs_self _
    _ ≤ _ := h1
    _ ≤ _ := h4
    _ = _ := h5

theorem LabelCoeffs.entry_bound {G V V₀ ta tb} (h : LabelCoeffs G V V₀ ta tb) {p : ℝ × Vec 2}
    (hp : p.1 ∈ Set.Icc ta tb) (i j : Fin 2) : |G p i j| ≤ 9 / 4 := by
  have h1 := h.bdd p hp (basisVec j)
  have h2 : vecNormSq (basisVec j : Vec 2) = 1 := by
    fin_cases j <;> simp [vecNormSq_two, basisVec]
  rw [h2, mul_one] at h1
  have h3 : (G p).mulVec (basisVec j) i = G p i j := by
    fin_cases j <;> fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, basisVec]
  have h4 := abs_coord_le_sqrt ((G p).mulVec (basisVec j)) i
  rw [h3] at h4
  refine h4.trans ?_
  apply Real.sqrt_le_iff.2
  exact ⟨by norm_num, h1⟩

theorem LabelCoeffs.Ventry_bound {G V V₀ ta tb} (h : LabelCoeffs G V V₀ ta tb) {p : ℝ × Vec 2}
    (hp : p.1 ∈ Set.Icc ta tb) (i : Fin 2) : |V p i| ≤ V₀ :=
  (abs_coord_le_sqrt (V p) i).trans (Real.sqrt_le_iff.2 ⟨h.V0, h.Vbd p hp⟩)

/-! # Pointwise algebra for the cutoff energy inequality -/

/-- The pointwise integrand of the dissipation: `κη²D·GD + 2κηu (GD)·n - ηu² V·n`. -/
def fluxE (κ : ℝ) (G : Matrix (Fin 2) (Fin 2) ℝ) (V : Vec 2) (η u : ℝ) (D n : Vec 2) : ℝ :=
  κ * η ^ 2 * vecDot D (G.mulVec D) + 2 * κ * η * u * vecDot (G.mulVec D) n -
    η * u ^ 2 * vecDot V n

theorem P_dot_eq (κ : ℝ) (G : Matrix (Fin 2) (Fin 2) ℝ) (V D n : Vec 2) (η u : ℝ) :
    vecDot (κ • G.mulVec D - u • V) (η ^ 2 • D + (2 * η * u) • n) =
      fluxE κ G V η u D n - (η * u) * vecDot V (η • D + u • n) := by
  simp only [fluxE, vecDot, Fin.sum_univ_two, Pi.sub_apply, Pi.smul_apply, Pi.add_apply,
    smul_eq_mul]
  ring

theorem energy_pointwise_bound {G : Matrix (Fin 2) (Fin 2) ℝ} {V : Vec 2} {V₀ κ η u N : ℝ}
    (hs : Gᵀ = G) (hell : ∀ e, (1 / 4) * vecNormSq e ≤ vecDot e (G.mulVec e))
    (hbdd : ∀ e, vecNormSq (G.mulVec e) ≤ (9 / 4) ^ 2 * vecNormSq e)
    (hκ : 0 ≤ κ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hN : 0 ≤ N) (hV0 : 0 ≤ V₀)
    (hV : vecNormSq V ≤ V₀ ^ 2) (D n : Vec 2) (hn : vecNormSq n ≤ N ^ 2) :
    -2 * fluxE κ G V η u D n + κ * η ^ 2 * vecDot D (G.mulVec D) ≤
      (9 * κ * N ^ 2 + 2 * V₀ * N) * u ^ 2 := by
  have hpsd : ∀ e, 0 ≤ vecDot e (G.mulVec e) := fun e => by
    have := hell e; have := vecNormSq_nonneg e; linarith
  set q := vecDot D (G.mulVec D) with hq
  set m := vecDot n (G.mulVec n) with hm
  set c := vecDot (G.mulVec D) n with hc
  have hq0 : 0 ≤ q := hpsd D
  have hm0 : 0 ≤ m := hpsd n
  have hcs : c ^ 2 ≤ m * q := by
    have := cauchy_symm hs hpsd n D
    rw [hc, vecDot_comm]
    exact this
  have hmN : m ≤ (9 / 4) * N ^ 2 := by
    have h1 := abs_vecDot_le n (G.mulVec n)
    have h2 := hbdd n
    have h3 : Real.sqrt (vecNormSq (G.mulVec n)) ≤ (9 / 4) * Real.sqrt (vecNormSq n) := by
      apply Real.sqrt_le_iff.2
      refine ⟨by positivity, ?_⟩
      rw [mul_pow, Real.sq_sqrt (vecNormSq_nonneg n)]
      exact h2
    have h4 : Real.sqrt (vecNormSq n) ≤ N := Real.sqrt_le_iff.2 ⟨hN, hn⟩
    have h5 : Real.sqrt (vecNormSq n) * Real.sqrt (vecNormSq (G.mulVec n)) ≤
        N * ((9 / 4) * N) := by
      calc _ ≤ Real.sqrt (vecNormSq n) * ((9 / 4) * Real.sqrt (vecNormSq n)) :=
            mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)
        _ ≤ N * ((9 / 4) * N) := by gcongr
    calc m ≤ |m| := le_abs_self _
      _ ≤ _ := h1
      _ ≤ N * ((9 / 4) * N) := h5
      _ = (9 / 4) * N ^ 2 := by ring
  -- the cross term
  have hcross : |4 * η * u * c| ≤ η ^ 2 * q + 4 * u ^ 2 * m := by
    have hrhs : 0 ≤ η ^ 2 * q + 4 * u ^ 2 * m := by positivity
    have h1 : (4 * η * u * c) ^ 2 ≤ 16 * η ^ 2 * u ^ 2 * (m * q) := by
      have : (4 * η * u * c) ^ 2 = 16 * η ^ 2 * u ^ 2 * c ^ 2 := by ring
      rw [this]
      have : 0 ≤ 16 * η ^ 2 * u ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hcs this]
    have h2 : (4 * η * u * c) ^ 2 ≤ (η ^ 2 * q + 4 * u ^ 2 * m) ^ 2 := by
      nlinarith [sq_nonneg (η ^ 2 * q - 4 * u ^ 2 * m)]
    exact abs_le_of_sq_le_sq' h2 hrhs |> fun h => abs_le.2 h
  have hVn : |η * u ^ 2 * vecDot V n| ≤ V₀ * N * u ^ 2 := by
    have h1 := abs_vecDot_le V n
    have h2 : Real.sqrt (vecNormSq V) ≤ V₀ := Real.sqrt_le_iff.2 ⟨hV0, hV⟩
    have h3 : Real.sqrt (vecNormSq n) ≤ N := Real.sqrt_le_iff.2 ⟨hN, hn⟩
    have h4 : |vecDot V n| ≤ V₀ * N :=
      h1.trans (mul_le_mul h2 h3 (Real.sqrt_nonneg _) hV0)
    rw [abs_mul, abs_mul, abs_of_nonneg hη0, abs_of_nonneg (sq_nonneg u)]
    have : |vecDot V n| * (η * u ^ 2) ≤ V₀ * N * u ^ 2 := by
      have h5 : η * u ^ 2 ≤ u ^ 2 := by nlinarith [sq_nonneg u]
      calc |vecDot V n| * (η * u ^ 2) ≤ (V₀ * N) * (η * u ^ 2) :=
            mul_le_mul_of_nonneg_right h4 (by positivity)
        _ ≤ (V₀ * N) * u ^ 2 := mul_le_mul_of_nonneg_left h5 (by positivity)
    linarith
  unfold fluxE
  have hcross' := abs_le.1 hcross
  have hV' := abs_le.1 hVn
  have e1 : -2 * (κ * η ^ 2 * q + 2 * κ * η * u * c - η * u ^ 2 * vecDot V n) =
      -2 * κ * η ^ 2 * q - κ * (4 * η * u * c) + 2 * (η * u ^ 2 * vecDot V n) := by ring
  rw [e1]
  have h6 : κ * (4 * η * u * c) ≥ -(κ * (η ^ 2 * q + 4 * u ^ 2 * m)) := by
    nlinarith [mul_le_mul_of_nonneg_left hcross'.1 hκ]
  have h7 : κ * (4 * u ^ 2 * m) ≤ κ * (4 * u ^ 2 * ((9 / 4) * N ^ 2)) := by
    gcongr
  nlinarith [h6, h7, hV'.2]

/-! # Pointwise algebra for the weighted energy inequality

The Young inequalities behind the differential inequality of the weighted energy: for the flux
`P = κ G d + H`, the weight `w` (with `∇w = ℓ w e`, `|e| ≤ 1`, `∂ₜ w = -λ w`), the drift `V` and
the scalar source `g'`,
`-2 (P̃ · (w² D Z̃ + 2 w Z̃ ∇w) - g̃ w² Z̃) ≤ θ² w² (18 κ⁻¹ |H|² + λ'⁻¹ g'²)` where `λ =
10κℓ² + 8V₀²/κ + λ'/2`. -/

/-- The decay rate of the time weight. -/
def decayRate (κ ℓ V₀ lam : ℝ) : ℝ := 10 * κ * ℓ ^ 2 + 8 * V₀ ^ 2 / κ + lam / 2

theorem young_q {κ q hh t : ℝ} (hκ : 0 < κ) (hq : 0 ≤ q) (hh0 : 0 ≤ hh)
    (ht : t ^ 2 ≤ 4 * hh * q) : -2 * t ≤ κ / 4 * q + 16 * hh / κ := by
  have hu : 0 ≤ κ / 4 * q := by positivity
  have hv : 0 ≤ 16 * hh / κ := by positivity
  have huv : (κ / 4 * q) * (16 * hh / κ) = 4 * hh * q := by field_simp; ring
  have h1 : (2 * t) ^ 2 ≤ (κ / 4 * q + 16 * hh / κ) ^ 2 := by
    nlinarith [sq_nonneg (κ / 4 * q - 16 * hh / κ)]
  have h2 := abs_le_of_sq_le_sq' h1 (by positivity)
  linarith [h2.1]

theorem core_ineq {κ ℓ V₀ lam q Z s hd he vd g' hh : ℝ} (hκ : 0 < κ) (hlam : 0 < lam)
    (hq : 0 ≤ q) (hh0 : 0 ≤ hh) (hs : s ^ 2 ≤ 9 / 4 * q) (hhd : hd ^ 2 ≤ 4 * hh * q)
    (hhe : he ^ 2 ≤ hh) (hvd : vd ^ 2 ≤ 4 * V₀ ^ 2 * q) :
    -2 * (κ * q + 2 * κ * ℓ * Z * s + hd + 2 * ℓ * Z * he + Z * vd + g' * Z +
        decayRate κ ℓ V₀ lam * Z ^ 2) ≤ 18 / κ * hh + g' ^ 2 / lam := by
  have y1 : -4 * (ℓ * Z) * s ≤ 18 * (ℓ * Z) ^ 2 + q / 2 := by
    nlinarith [sq_nonneg (9 * (ℓ * Z) + s)]
  have y2 := young_q hκ hq hh0 hhd
  have y3 : -4 * (ℓ * Z) * he ≤ 2 * κ * (ℓ * Z) ^ 2 + 2 * hh / κ := by
    have h : 0 ≤ (κ * (ℓ * Z) - he) ^ 2 := sq_nonneg _
    have h' : 2 * (κ * (ℓ * Z) - he) ^ 2 / κ ≥ 0 := by positivity
    have e : 2 * κ * (ℓ * Z) ^ 2 + 2 * he ^ 2 / κ + 4 * (ℓ * Z) * he
        = 2 * (κ * (ℓ * Z) + he) ^ 2 / κ := by field_simp; ring
    have e2 : 2 * he ^ 2 / κ ≤ 2 * hh / κ := by
      apply div_le_div_of_nonneg_right _ hκ.le
      linarith
    have : 0 ≤ 2 * (κ * (ℓ * Z) + he) ^ 2 / κ := by positivity
    nlinarith
  have y4 := young_q hκ hq (by positivity : 0 ≤ V₀ ^ 2 * Z ^ 2)
    (t := Z * vd) (by nlinarith [sq_nonneg Z, mul_le_mul_of_nonneg_left hvd (sq_nonneg Z)])
  have y5 : -2 * g' * Z ≤ g' ^ 2 / lam + lam * Z ^ 2 := by
    have : 0 ≤ (g' + lam * Z) ^ 2 / lam := by positivity
    have e : (g' + lam * Z) ^ 2 / lam = g' ^ 2 / lam + 2 * g' * Z + lam * Z ^ 2 := by
      field_simp
      ring
    nlinarith
  unfold decayRate
  have y1' := mul_le_mul_of_nonneg_left y1 hκ.le
  have hq' : 0 ≤ κ * q := mul_nonneg hκ.le hq
  have e1 : 16 * (V₀ ^ 2 * Z ^ 2) / κ = 16 * V₀ ^ 2 / κ * Z ^ 2 := by ring
  have e2 : 8 * V₀ ^ 2 / κ * Z ^ 2 * 2 = 16 * V₀ ^ 2 / κ * Z ^ 2 := by ring
  have e3 : 18 / κ * hh = 16 * hh / κ + 2 * hh / κ := by ring
  have e4 : 2 * hh / κ = 2 * hh / κ := rfl
  nlinarith [y1', y2, y3, y4, y5, hq', mul_nonneg hκ.le (sq_nonneg (ℓ * Z))]


theorem vecDot_sq_le (a b : Vec 2) : vecDot a b ^ 2 ≤ vecNormSq a * vecNormSq b := by
  have h := abs_vecDot_le a b
  have h2 : |vecDot a b| ^ 2 ≤ (Real.sqrt (vecNormSq a) * Real.sqrt (vecNormSq b)) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [sq_abs, mul_pow, Real.sq_sqrt (vecNormSq_nonneg a), Real.sq_sqrt (vecNormSq_nonneg b)] at h2
  exact h2

theorem quad_le_gen {G : Matrix (Fin 2) (Fin 2) ℝ}
    (hbdd : ∀ x, vecNormSq (G.mulVec x) ≤ (9 / 4) ^ 2 * vecNormSq x) (n : Vec 2) :
    vecDot n (G.mulVec n) ≤ (9 / 4) * vecNormSq n := by
  have h1 := abs_vecDot_le n (G.mulVec n)
  have h3 : Real.sqrt (vecNormSq (G.mulVec n)) ≤ (9 / 4) * Real.sqrt (vecNormSq n) := by
    apply Real.sqrt_le_iff.2
    refine ⟨by positivity, ?_⟩
    rw [mul_pow, Real.sq_sqrt (vecNormSq_nonneg n)]
    exact hbdd n
  have h4 : Real.sqrt (vecNormSq n) * Real.sqrt (vecNormSq (G.mulVec n)) ≤
      Real.sqrt (vecNormSq n) * ((9 / 4) * Real.sqrt (vecNormSq n)) :=
    mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)
  have h5 : Real.sqrt (vecNormSq n) * ((9 / 4) * Real.sqrt (vecNormSq n)) =
      (9 / 4) * vecNormSq n := by
    have := Real.mul_self_sqrt (vecNormSq_nonneg n)
    nlinarith
  calc vecDot n (G.mulVec n) ≤ |vecDot n (G.mulVec n)| := le_abs_self _
    _ ≤ _ := h1
    _ ≤ _ := h4
    _ = _ := h5

theorem weighted_pointwise {G : Matrix (Fin 2) (Fin 2) ℝ} {V : Vec 2} {V₀ κ ℓ lam θ w Z g' : ℝ}
    {d e H : Vec 2} (hs : Gᵀ = G) (hell : ∀ x, (1 / 4) * vecNormSq x ≤ vecDot x (G.mulVec x))
    (hbdd : ∀ x, vecNormSq (G.mulVec x) ≤ (9 / 4) ^ 2 * vecNormSq x)
    (hκ : 0 < κ) (hlam : 0 < lam) (hV : vecNormSq V ≤ V₀ ^ 2) (he : vecNormSq e ≤ 1) :
    -2 * (vecDot (θ • (κ • G.mulVec d + H)) ((w ^ 2) • (θ • d) + (2 * w * (θ * Z)) • ((ℓ * w) • e))
        - (θ * (-(vecDot V d) - g') - decayRate κ ℓ V₀ lam * (θ * Z)) * w ^ 2 * (θ * Z)) ≤
      θ ^ 2 * w ^ 2 * (18 / κ * vecNormSq H + g' ^ 2 / lam) := by
  have hpsd : ∀ x, 0 ≤ vecDot x (G.mulVec x) := fun x => by
    have := hell x; have := vecNormSq_nonneg x; linarith
  set q := vecDot d (G.mulVec d) with hq
  set s := vecDot e (G.mulVec d) with hsdef
  have hq0 : 0 ≤ q := hpsd d
  have hd4 : vecNormSq d ≤ 4 * q := by have := hell d; linarith
  have hexp : vecDot (θ • (κ • G.mulVec d + H))
      ((w ^ 2) • (θ • d) + (2 * w * (θ * Z)) • ((ℓ * w) • e)) -
      (θ * (-(vecDot V d) - g') - decayRate κ ℓ V₀ lam * (θ * Z)) * w ^ 2 * (θ * Z) =
      θ ^ 2 * w ^ 2 * (κ * q + 2 * κ * ℓ * Z * s + vecDot H d + 2 * ℓ * Z * vecDot H e +
        Z * vecDot V d + g' * Z + decayRate κ ℓ V₀ lam * Z ^ 2) := by
    simp only [hq, hsdef, vecDot, Fin.sum_univ_two, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  rw [hexp]
  have hs2 : s ^ 2 ≤ 9 / 4 * q := by
    have h1 := cauchy_symm hs hpsd e d
    have h2 := quad_le_gen hbdd e
    have h3 : vecDot e (G.mulVec e) ≤ 9 / 4 := by linarith
    have h4 := hpsd e
    calc s ^ 2 ≤ vecDot e (G.mulVec e) * q := h1
      _ ≤ 9 / 4 * q := mul_le_mul_of_nonneg_right h3 hq0
  have hhd : vecDot H d ^ 2 ≤ 4 * vecNormSq H * q := by
    have := vecDot_sq_le H d
    nlinarith [vecNormSq_nonneg H]
  have hhe : vecDot H e ^ 2 ≤ vecNormSq H := by
    have := vecDot_sq_le H e
    nlinarith [vecNormSq_nonneg H]
  have hvd : vecDot V d ^ 2 ≤ 4 * V₀ ^ 2 * q := by
    have := vecDot_sq_le V d
    have h1 : vecNormSq V * vecNormSq d ≤ V₀ ^ 2 * (4 * q) :=
      mul_le_mul hV hd4 (vecNormSq_nonneg d) (sq_nonneg _)
    nlinarith
  have := core_ineq (κ := κ) (ℓ := ℓ) (V₀ := V₀) (lam := lam) (q := q) (Z := Z) (s := s)
    (hd := vecDot H d) (he := vecDot H e) (vd := vecDot V d) (g' := g')
    (hh := vecNormSq H) hκ hlam hq0 (vecNormSq_nonneg H) hs2 hhd hhe hvd
  have hθw : 0 ≤ θ ^ 2 * w ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left this hθw]

/-! # The equation for the localized difference `Z = χ D`

If `D` solves `∂ₜD = div(κ G ∇D) - V·∇D` in a cylinder, then `Z = χ D` solves
`∂ₜZ = div P + g` with `P = κ G ∇Z + H`, `g = -V·∇Z - g'`, where
`H = -κ D G∇χ` and `g' = κ ∇χ·G∇D - D V·∇χ`. Multiplying by the time weight `θ(t) = e^{-Λ(t-ta)}`
gives the equation for `θ Z` with flux `θ P` and source `θ g - Λ θ Z`. -/

section
/-- The time weight `e^{-Λ(t - ta)}`. -/
def tw (Λ ta t : ℝ) : ℝ := Real.exp (-Λ * (t - ta))

theorem tw_hasDerivAt (Λ ta t : ℝ) : HasDerivAt (tw Λ ta) (-Λ * tw Λ ta t) t := by
  have h0 : HasDerivAt (fun s : ℝ => s - ta) 1 t := (hasDerivAt_id t).sub_const ta
  have h1 := (h0.const_mul (-Λ)).exp
  refine h1.congr_deriv ?_
  show Real.exp (-Λ * (t - ta)) * (-Λ * 1) = -Λ * Real.exp (-Λ * (t - ta))
  ring

theorem tw_contDiff (Λ ta : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (tw Λ ta) := by
  unfold tw
  exact Real.contDiff_exp.comp (by fun_prop)

theorem tw_pos (Λ ta t : ℝ) : 0 < tw Λ ta t := Real.exp_pos _

theorem tw_le_one {Λ ta t : ℝ} (hΛ : 0 ≤ Λ) (ht : ta ≤ t) : tw Λ ta t ≤ 1 := by
  unfold tw
  rw [Real.exp_le_one_iff]
  nlinarith

theorem deriv_tw (Λ ta t : ℝ) : deriv (tw Λ ta) t = -Λ * tw Λ ta t := (tw_hasDerivAt Λ ta t).deriv

/-- Product rule for the derivative of a product of smooth space-time functions. -/
theorem fderiv_mul_st {f g : ℝ × Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (p e : ℝ × Vec 2) :
    fderiv ℝ (fun z => f z * g z) p e = f p * fderiv ℝ g p e + g p * fderiv ℝ f p e := by
  have hfd : DifferentiableAt ℝ f p := (hf.differentiable (by simp)) p
  have hgd : DifferentiableAt ℝ g p := (hg.differentiable (by simp)) p
  have hd : HasFDerivAt (fun z => f z * g z) _ p := hfd.hasFDerivAt.mul hgd.hasFDerivAt
  rw [hd.fderiv]
  simp

/-- The space-time function `θ(t) χ(y)`. -/
def wtest (Λ ta : ℝ) (χ : Vec 2 → ℝ) : ℝ × Vec 2 → ℝ := fun p => tw Λ ta p.1 * χ p.2

theorem contDiff_wtest (Λ ta : ℝ) {χ : Vec 2 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) :
    ContDiff ℝ (⊤ : ℕ∞) (wtest Λ ta χ) :=
  ((tw_contDiff Λ ta).comp contDiff_fst).mul (hχ.comp contDiff_snd)

theorem fderiv_wtest (Λ ta : ℝ) {χ : Vec 2 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (p v : ℝ × Vec 2) :
    fderiv ℝ (wtest Λ ta χ) p v = (-Λ * tw Λ ta p.1) * v.1 * χ p.2 +
      tw Λ ta p.1 * fderiv ℝ χ p.2 v.2 := by
  have hζd : DifferentiableAt ℝ (tw Λ ta) p.1 := ((tw_contDiff Λ ta).differentiable (by simp)) _
  have hχd : DifferentiableAt ℝ χ p.2 := (hχ.differentiable (by simp)) _
  have h1 : HasFDerivAt (fun p : ℝ × Vec 2 => tw Λ ta p.1)
      ((fderiv ℝ (tw Λ ta) p.1).comp (ContinuousLinearMap.fst ℝ ℝ (Vec 2))) p :=
    hζd.hasFDerivAt.comp p (ContinuousLinearMap.fst ℝ ℝ (Vec 2)).hasFDerivAt
  have h2 : HasFDerivAt (fun p : ℝ × Vec 2 => χ p.2)
      ((fderiv ℝ χ p.2).comp (ContinuousLinearMap.snd ℝ ℝ (Vec 2))) p :=
    hχd.hasFDerivAt.comp p (ContinuousLinearMap.snd ℝ ℝ (Vec 2)).hasFDerivAt
  have := (h1.mul h2).fderiv
  have e0 : wtest Λ ta χ = (fun p : ℝ × Vec 2 => tw Λ ta p.1) * (fun p : ℝ × Vec 2 => χ p.2) :=
    rfl
  rw [e0, this]
  simp only [_root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    smul_eq_mul]
  have e : fderiv ℝ (tw Λ ta) p.1 v.1 = deriv (tw Λ ta) p.1 * v.1 := by
    have h := (fderiv ℝ (tw Λ ta) p.1).map_smul v.1 1
    rw [smul_eq_mul, mul_one] at h
    rw [h, smul_eq_mul, fderiv_apply_one_eq_deriv, mul_comm]
  rw [e, deriv_tw]
  ring

theorem isSTTest_wtest_mul {S : Set (ℝ × Vec 2)} {φ : ℝ × Vec 2 → ℝ} (Λ ta : ℝ)
    {χ : Vec 2 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hφ : IsSTTest S φ) :
    IsSTTest S (fun p => wtest Λ ta χ p * φ p) :=
  ⟨(contDiff_wtest Λ ta hχ).mul hφ.1, hφ.2.1.mul_left,
    (tsupport_mul_subset_right).trans hφ.2.2⟩

section Defs

variable (Λ ta κ : ℝ) (G : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (V : ℝ × Vec 2 → Vec 2)
  (χ : Vec 2 → ℝ) (D : ℝ × Vec 2 → ℝ) (DD : ℝ × Vec 2 → Vec 2)

/-- The flux source `H = -κ D G∇χ`. -/
def srcH (p : ℝ × Vec 2) : Vec 2 := (-(κ * D p)) • (G p).mulVec (spGrad χ p.2)

/-- The scalar source `g' = κ ∇χ·G∇D - D V·∇χ`. -/
def srcG (p : ℝ × Vec 2) : ℝ :=
  κ * vecDot (spGrad χ p.2) ((G p).mulVec (DD p)) - D p * vecDot (V p) (spGrad χ p.2)

/-- The gradient of `χ D`. -/
def dZ (p : ℝ × Vec 2) : Vec 2 := χ p.2 • DD p + D p • spGrad χ p.2

/-- The time-weighted localized difference `θ χ D`. -/
def Zt (p : ℝ × Vec 2) : ℝ := tw Λ ta p.1 * (χ p.2 * D p)

/-- Its gradient. -/
def DZt (p : ℝ × Vec 2) : Vec 2 := tw Λ ta p.1 • dZ χ D DD p

/-- Its flux. -/
def Pt (p : ℝ × Vec 2) : Vec 2 :=
  tw Λ ta p.1 • (κ • (G p).mulVec (dZ χ D DD p) + srcH κ G χ D p)

/-- Its source. -/
def gt (p : ℝ × Vec 2) : ℝ :=
  tw Λ ta p.1 * (-(vecDot (V p) (dZ χ D DD p)) - srcG κ G V χ D DD p) - Λ * Zt Λ ta χ D p

end Defs

/-- The pointwise identity behind the localized equation. -/
theorem Zt_integrand_eq (Λ ta κ : ℝ) (G : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (V : ℝ × Vec 2 → Vec 2) {χ : Vec 2 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (D : ℝ × Vec 2 → ℝ) (DD : ℝ × Vec 2 → Vec 2) {φ : ℝ × Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (p : ℝ × Vec 2) :
    -(D p * stTimeDeriv (fun q => wtest Λ ta χ q * φ q) p) +
        vecDot (V p) (DD p) * (wtest Λ ta χ p * φ p) +
        κ * vecDot ((G p).mulVec (DD p)) (stSpaceGrad (fun q => wtest Λ ta χ q * φ q) p) =
      -(Zt Λ ta χ D p * stTimeDeriv φ p) + vecDot (Pt Λ ta κ G χ D DD p) (stSpaceGrad φ p) -
        gt Λ ta κ G V χ D DD p * φ p := by
  have hw := contDiff_wtest Λ ta hχ
  have e1 : stTimeDeriv (fun q => wtest Λ ta χ q * φ q) p =
      wtest Λ ta χ p * stTimeDeriv φ p + φ p * (-Λ * tw Λ ta p.1 * χ p.2) := by
    unfold stTimeDeriv
    rw [fderiv_mul_st hw hφ, fderiv_wtest Λ ta hχ]
    simp
  have e2 : ∀ i : Fin 2, stSpaceGrad (fun q => wtest Λ ta χ q * φ q) p i =
      wtest Λ ta χ p * stSpaceGrad φ p i + φ p * (tw Λ ta p.1 * spGrad χ p.2 i) := by
    intro i
    unfold stSpaceGrad
    rw [fderiv_mul_st hw hφ, fderiv_wtest Λ ta hχ]
    simp [spGrad]
  have e3 : stSpaceGrad (fun q => wtest Λ ta χ q * φ q) p =
      fun i => wtest Λ ta χ p * stSpaceGrad φ p i + φ p * (tw Λ ta p.1 * spGrad χ p.2 i) :=
    funext e2
  rw [e1, e3]
  simp only [Pt, gt, Zt, srcH, srcG, dZ, wtest, vecDot, Fin.sum_univ_two, Matrix.mulVec_add,
    Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **The equation for `θ χ D`**. -/
theorem Zt_weak {S : Set (ℝ × Vec 2)} {G : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    {V : ℝ × Vec 2 → Vec 2} {κ : ℝ} {D : ℝ × Vec 2 → ℝ} {DD : ℝ × Vec 2 → Vec 2}
    (Λ ta : ℝ) {χ : Vec 2 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (heq : ∀ ξ, IsSTTest S ξ → ∫ p in S, (-(D p * stTimeDeriv ξ p) +
        vecDot (V p) (DD p) * ξ p + κ * vecDot ((G p).mulVec (DD p)) (stSpaceGrad ξ p)) = 0) :
    ∀ φ, IsSTTest S φ → ∫ p in S, (-(Zt Λ ta χ D p * stTimeDeriv φ p) +
      vecDot (Pt Λ ta κ G χ D DD p) (stSpaceGrad φ p) - gt Λ ta κ G V χ D DD p * φ p) = 0 := by
  intro φ hφ
  rw [← heq _ (isSTTest_wtest_mul Λ ta hχ hφ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  exact (Zt_integrand_eq Λ ta κ G V hχ D DD hφ.1 p).symm
end

end AVRegularity.Applications.Davies
end
end
end
