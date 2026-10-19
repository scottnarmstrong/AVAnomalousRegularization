-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Applications.Davies.ChartBridge
public import AVRegularity.Applications.Davies.Equation
import AVRegularity.Applications.Pipe.LocalEnergy
import AVRegularity.Applications.TorusEnergy.StreamFacts
public import AVRegularity.Statements.Intermediate.CycleReference.JacMatrix
public import AVRegularity.Statements.Intermediate.CycleReference.StreamFlow
import AVRegularity.Applications.Construction.StreamTail
import AVRegularity.Applications.LocalEnergy.DivFreeMollify.Limit
import AVRegularity.Applications.LocalEnergy.MolEnergy
import AVRegularity.Applications.Microscopic.DilationTests
import AVRegularity.CycleReference.TransitionTaylorBounds
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Int.Star
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section
noncomputable section

section
open MeasureTheory Homogenization Filter Topology
namespace AVRegularity.Applications.Davies

/-! # The cutoffs and the weight of the Davies localization

Scaled radial cutoffs `χ` (one on `B_{R/2}`, supported in `B_{3R/4}`), `η` (one on `B_{7R/8}`,
supported in `B_{15R/16}`) and the weight profile `ψ` (zero on `B_{R/8}`, equal to `-c_a R` outside
`B_{R/2}`, `|∇ψ| ≤ 1`), with gradient bounds `L/R`. -/

open AVRegularity.Applications

theorem spGrad_eq_zero_of_eventually {f : Vec 2 → ℝ} {y : Vec 2} {c : ℝ}
    (h : f =ᶠ[𝓝 y] fun _ => c) : spGrad f y = 0 := by
  funext i
  simp [spGrad, h.fderiv_eq]

theorem vecNormSq_smul_inv_le {R : ℝ} (hR : 0 < R) {y : Vec 2} {a : ℝ}
    (h : vecNormSq y ≤ (a * R) ^ 2) : vecNormSq (R⁻¹ • y) ≤ a ^ 2 := by
  rw [vecNormSq_smul]
  have : R⁻¹ ^ 2 * (a * R) ^ 2 = a ^ 2 := by field_simp
  have h2 : 0 < R⁻¹ ^ 2 := by positivity
  nlinarith

theorem vecNormSq_smul_inv_ge {R : ℝ} (hR : 0 < R) {y : Vec 2} {a : ℝ}
    (h : (a * R) ^ 2 ≤ vecNormSq y) : a ^ 2 ≤ vecNormSq (R⁻¹ • y) := by
  rw [vecNormSq_smul]
  have : R⁻¹ ^ 2 * (a * R) ^ 2 = a ^ 2 := by field_simp
  have h2 : 0 < R⁻¹ ^ 2 := by positivity
  nlinarith

theorem isOpen_vecNormSq_lt (r : ℝ) : IsOpen {y : Vec 2 | vecNormSq y < r} :=
  isOpen_lt contDiff_vecNormSq_top.continuous continuous_const

theorem isOpen_vecNormSq_gt (r : ℝ) : IsOpen {y : Vec 2 | r < vecNormSq y} :=
  isOpen_lt continuous_const contDiff_vecNormSq_top.continuous

/-- The scaled profile `y ↦ cutProfile a b (y/R)`. -/
def prof (a b R : ℝ) : Vec 2 → ℝ := scaleFn (cutProfile a b) R

theorem prof_contDiff (a b R : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (prof a b R) :=
  contDiff_scaleFn (contDiff_cutProfile a b) R

theorem prof_eq_one {a b R : ℝ} (hR : 0 < R) (hab : a < b) (ha : 0 ≤ a) {y : Vec 2}
    (h : vecNormSq y ≤ (a * R) ^ 2) : prof a b R y = 1 :=
  cutProfile_eq_one hab ha (by
    have := vecNormSq_smul_inv_le hR h
    simpa [scaleFn] using this)

theorem prof_eq_zero {a b R : ℝ} (hR : 0 < R) (hab : a < b) (ha : 0 ≤ a) {y : Vec 2}
    (h : (b * R) ^ 2 ≤ vecNormSq y) : prof a b R y = 0 :=
  cutProfile_eq_zero hab ha (by
    have := vecNormSq_smul_inv_ge hR h
    simpa [scaleFn] using this)

theorem prof_nonneg (a b R : ℝ) (y : Vec 2) : 0 ≤ prof a b R y := cutProfile_nonneg a b _
theorem prof_le_one (a b R : ℝ) (y : Vec 2) : prof a b R y ≤ 1 := cutProfile_le_one a b _

theorem prof_hasCompactSupport {a b R : ℝ} (hR : 0 < R) (hab : a < b) (ha : 0 ≤ a) :
    HasCompactSupport (prof a b R) :=
  HasCompactSupport.intro (isCompact_vecNormSq_le ((b * R) ^ 2)) fun _ hy =>
    prof_eq_zero hR hab ha (not_le.1 hy).le

theorem prof_tsupport {a b R : ℝ} (hR : 0 < R) (hab : a < b) (ha : 0 ≤ a) :
    tsupport (prof a b R) ⊆ {y : Vec 2 | vecNormSq y ≤ (b * R) ^ 2} := by
  refine closure_minimal ?_ (isClosed_le contDiff_vecNormSq_top.continuous continuous_const)
  intro y hy
  by_contra h
  exact hy (prof_eq_zero hR hab ha (not_le.1 h).le)

theorem prof_grad_bound {a b R L : ℝ} (hL : ∀ y, vecNormSq (spGrad (cutProfile a b) y) ≤ L ^ 2)
    (y : Vec 2) : vecNormSq (spGrad (prof a b R) y) ≤ (L / R) ^ 2 := by
  have := vecNormSq_spGrad_scaleFn_le (contDiff_cutProfile a b) hL R y
  simpa [prof, div_eq_inv_mul, mul_pow] using this

theorem prof_grad_zero_inner {a b R : ℝ} (hR : 0 < R) (hab : a < b) (ha : 0 ≤ a) {y : Vec 2}
    (h : vecNormSq y < (a * R) ^ 2) : spGrad (prof a b R) y = 0 := by
  refine spGrad_eq_zero_of_eventually (c := 1) ?_
  filter_upwards [(isOpen_vecNormSq_lt ((a * R) ^ 2)).mem_nhds h] with z hz
  exact prof_eq_one hR hab ha (le_of_lt hz)

theorem prof_grad_zero_outer {a b R : ℝ} (hR : 0 < R) (hab : a < b) (ha : 0 ≤ a) {y : Vec 2}
    (h : (b * R) ^ 2 < vecNormSq y) : spGrad (prof a b R) y = 0 := by
  refine spGrad_eq_zero_of_eventually (c := 0) ?_
  filter_upwards [(isOpen_vecNormSq_gt ((b * R) ^ 2)).mem_nhds h] with z hz
  exact prof_eq_zero hR hab ha (le_of_lt hz)

/-- The cutoff package of the Davies localization. -/
theorem exists_cutoffs : ∃ L₁ L₂ ca : ℝ, 0 ≤ L₁ ∧ 0 ≤ L₂ ∧ 0 < ca ∧ ca ≤ 1 ∧ ∀ R : ℝ, 0 < R →
    ∃ χ η ψ : Vec 2 → ℝ,
      IsSpTest (euclidBall 0 R) χ ∧ (∀ y, 0 ≤ χ y ∧ χ y ≤ 1) ∧
      (∀ y, vecNormSq (spGrad χ y) ≤ (L₁ / R) ^ 2) ∧
      IsSpTest (euclidBall 0 R) η ∧ (∀ y, 0 ≤ η y ∧ η y ≤ 1) ∧
      (∀ y, vecNormSq (spGrad η y) ≤ (L₂ / R) ^ 2) ∧
      (∀ y, y ∈ tsupport χ → η y = 1 ∧ spGrad η y = 0) ∧
      ContDiff ℝ (⊤ : ℕ∞) ψ ∧ (∀ y, vecNormSq (spGrad ψ y) ≤ 1) ∧
      (∀ y, vecNormSq y ≤ (R / 8) ^ 2 → ψ y = 0 ∧ χ y = 1 ∧ η y = 1) ∧
      (∀ y, spGrad χ y ≠ 0 → ψ y = -(ca * R) ∧ η y = 1) ∧
      (∀ y, χ y ≠ 1 → ψ y = -(ca * R)) ∧ (∀ y, χ y ≠ 0 → η y = 1) := by
  obtain ⟨L₁, hL₁0, hL₁⟩ := exists_grad_bound (contDiff_cutProfile (1 / 2) (3 / 4))
    (cutProfile_compactSupport (by norm_num) (by norm_num))
  obtain ⟨L₂, hL₂0, hL₂⟩ := exists_grad_bound (contDiff_cutProfile (7 / 8) (15 / 16))
    (cutProfile_compactSupport (by norm_num) (by norm_num))
  obtain ⟨L₃, hL₃0, hL₃⟩ := exists_grad_bound (contDiff_cutProfile (1 / 8) (1 / 2))
    (cutProfile_compactSupport (by norm_num) (by norm_num))
  have hca0 : 0 < 1 / (L₃ + 1) := by positivity
  refine ⟨L₁, L₂, 1 / (L₃ + 1), hL₁0, hL₂0, hca0, ?_, fun R hR => ?_⟩
  · rw [div_le_one (by positivity)]; linarith
  set ca := 1 / (L₃ + 1) with hca
  refine ⟨prof (1 / 2) (3 / 4) R, prof (7 / 8) (15 / 16) R,
    fun y => -(ca * R) * (1 - prof (1 / 8) (1 / 2) R y), ?_⟩
  have h34 : tsupport (prof (1 / 2) (3 / 4) R) ⊆ euclidBall 0 R := by
    intro y hy
    have := prof_tsupport hR (by norm_num) (by norm_num) hy
    simp only [Set.mem_ofPred_eq] at this
    simp only [euclidBall, Set.mem_ofPred_eq, sub_zero]
    nlinarith [sq_nonneg R]
  have h1516 : tsupport (prof (7 / 8) (15 / 16) R) ⊆ euclidBall 0 R := by
    intro y hy
    have := prof_tsupport hR (by norm_num) (by norm_num) hy
    simp only [Set.mem_ofPred_eq] at this
    simp only [euclidBall, Set.mem_ofPred_eq, sub_zero]
    nlinarith [sq_nonneg R]
  have hψs : ContDiff ℝ (⊤ : ℕ∞) (fun y => -(ca * R) * (1 - prof (1 / 8) (1 / 2) R y)) :=
    contDiff_const.mul (contDiff_const.sub (prof_contDiff _ _ _))
  refine ⟨⟨prof_contDiff _ _ _, prof_hasCompactSupport hR (by norm_num) (by norm_num), h34⟩,
    fun y => ⟨prof_nonneg _ _ _ _, prof_le_one _ _ _ _⟩, prof_grad_bound hL₁,
    ⟨prof_contDiff _ _ _, prof_hasCompactSupport hR (by norm_num) (by norm_num), h1516⟩,
    fun y => ⟨prof_nonneg _ _ _ _, prof_le_one _ _ _ _⟩, prof_grad_bound hL₂, ?_, hψs, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro y hy
    have hy' := prof_tsupport hR (by norm_num) (by norm_num) hy
    simp only [Set.mem_ofPred_eq] at hy'
    refine ⟨prof_eq_one hR (by norm_num) (by norm_num) (by nlinarith [sq_nonneg R]), ?_⟩
    exact prof_grad_zero_inner hR (by norm_num) (by norm_num) (by nlinarith [sq_nonneg R])
  · intro y
    have hsm : spGrad (fun y => -(ca * R) * (1 - prof (1 / 8) (1 / 2) R y)) y =
        (ca * R) • spGrad (prof (1 / 8) (1 / 2) R) y := by
      funext i
      have hd : DifferentiableAt ℝ (prof (1 / 8) (1 / 2) R) y :=
        ((prof_contDiff _ _ _).differentiable (by simp)) y
      have h := ((hd.hasFDerivAt.const_sub 1).const_mul (-(ca * R))).fderiv
      simp only [spGrad, Pi.smul_apply, smul_eq_mul]
      rw [h]
      simp
    rw [hsm, vecNormSq_smul]
    have hb := prof_grad_bound (R := R) hL₃ y
    have h1 : (ca * R) ^ 2 * (L₃ / R) ^ 2 ≤ 1 := by
      have : (ca * R) ^ 2 * (L₃ / R) ^ 2 = (ca * L₃) ^ 2 := by field_simp
      rw [this, hca]
      have : 1 / (L₃ + 1) * L₃ ≤ 1 := by
        rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]; linarith
      have h0 : 0 ≤ 1 / (L₃ + 1) * L₃ := by positivity
      nlinarith
    calc (ca * R) ^ 2 * vecNormSq (spGrad (prof (1 / 8) (1 / 2) R) y)
        ≤ (ca * R) ^ 2 * (L₃ / R) ^ 2 := mul_le_mul_of_nonneg_left hb (sq_nonneg _)
      _ ≤ 1 := h1
  · intro y hy
    have hp := prof_eq_one hR (by norm_num) (by norm_num) (a := 1 / 8) (b := 1 / 2) (y := y)
      (by rw [show (1 / 8 * R) ^ 2 = (R / 8) ^ 2 by ring]; exact hy)
    refine ⟨?_, ?_, ?_⟩
    · show -(ca * R) * (1 - prof (1 / 8) (1 / 2) R y) = 0
      rw [hp]; ring
    · exact prof_eq_one hR (by norm_num) (by norm_num) (by nlinarith [sq_nonneg R])
    · exact prof_eq_one hR (by norm_num) (by norm_num) (by nlinarith [sq_nonneg R])
  · intro y hy
    have h2 : (1 / 2 * R) ^ 2 ≤ vecNormSq y := by
      by_contra hlt
      exact hy (prof_grad_zero_inner hR (by norm_num) (by norm_num) (not_le.1 hlt))
    have h3 : prof (1 / 8) (1 / 2) R y = 0 := prof_eq_zero hR (by norm_num) (by norm_num) h2
    have h4 : vecNormSq y ≤ (3 / 4 * R) ^ 2 := by
      by_contra hlt
      exact hy (prof_grad_zero_outer hR (by norm_num) (by norm_num) (not_le.1 hlt))
    refine ⟨?_, prof_eq_one hR (by norm_num) (by norm_num) ?_⟩
    · show -(ca * R) * (1 - prof (1 / 8) (1 / 2) R y) = -(ca * R)
      rw [h3]; ring
    · nlinarith [sq_nonneg R]
  · intro y hy
    have h2 : (1 / 2 * R) ^ 2 < vecNormSq y := by
      by_contra hlt
      exact hy (prof_eq_one hR (by norm_num) (by norm_num) (not_lt.1 hlt))
    have h3 : prof (1 / 8) (1 / 2) R y = 0 := prof_eq_zero hR (by norm_num) (by norm_num) h2.le
    show -(ca * R) * (1 - prof (1 / 8) (1 / 2) R y) = -(ca * R)
    rw [h3]; ring
  · intro y hy
    have h4 : vecNormSq y ≤ (3 / 4 * R) ^ 2 := by
      by_contra hlt
      exact hy (prof_eq_zero hR (by norm_num) (by norm_num) (not_le.1 hlt).le)
    exact prof_eq_one hR (by norm_num) (by norm_num) (by nlinarith [sq_nonneg R])

/-- The cutoff package in structure form. -/
structure CutoffPack (R L₁ L₂ ca : ℝ) (χ η ψ : Vec 2 → ℝ) : Prop where
  hχ : IsSpTest (euclidBall 0 R) χ
  hχ1 : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1
  hχN : ∀ y, vecNormSq (spGrad χ y) ≤ (L₁ / R) ^ 2
  hη : IsSpTest (euclidBall 0 R) η
  hη1 : ∀ y, 0 ≤ η y ∧ η y ≤ 1
  hηN : ∀ y, vecNormSq (spGrad η y) ≤ (L₂ / R) ^ 2
  hηχ : ∀ y, y ∈ tsupport χ → η y = 1 ∧ spGrad η y = 0
  hψ : ContDiff ℝ (⊤ : ℕ∞) ψ
  hψ1 : ∀ y, vecNormSq (spGrad ψ y) ≤ 1
  hP10 : ∀ y, vecNormSq y ≤ (R / 8) ^ 2 → ψ y = 0 ∧ χ y = 1 ∧ η y = 1
  hP11 : ∀ y, spGrad χ y ≠ 0 → ψ y = -(ca * R) ∧ η y = 1
  hP12 : ∀ y, χ y ≠ 1 → ψ y = -(ca * R)

theorem exists_cutoffPack : ∃ L₁ L₂ ca : ℝ, 0 ≤ L₁ ∧ 0 ≤ L₂ ∧ 0 < ca ∧ ca ≤ 1 ∧ ∀ R : ℝ, 0 < R →
    ∃ χ η ψ : Vec 2 → ℝ, CutoffPack R L₁ L₂ ca χ η ψ := by
  obtain ⟨L₁, L₂, ca, h1, h2, h3, h4, h⟩ := exists_cutoffs
  refine ⟨L₁, L₂, ca, h1, h2, h3, h4, fun R hR => ?_⟩
  obtain ⟨χ, η, ψ, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := h R hR
  exact ⟨χ, η, ψ, ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩⟩

end AVRegularity.Applications.Davies
end

section
open MeasureTheory Homogenization Matrix Filter Topology
open AVRegularity.Applications.LocalEnergy.Moll
namespace AVRegularity.Applications.Davies

/-! # Non-conservative form of the label equation

For a divergence-free label drift `V`, the conservative weak form
`∂ₜU = div(κ G∇U - V U)` is equivalent to `∂ₜU = div(κ G∇U) - V·∇U`: the difference is
`∫_B V·∇(ξ U) = 0` on a.e. time slice. -/

variable {G : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {V : ℝ × Vec 2 → Vec 2} {V₀ ta tb : ℝ}

theorem stTimeDeriv_memLp {μ : Measure (ℝ × Vec 2)} [IsFiniteMeasureOnCompacts μ] {ξ : ℝ × Vec 2 → ℝ}
    (hξ : ContDiff ℝ (⊤ : ℕ∞) ξ) (hc : HasCompactSupport ξ) :
    MemLp (stTimeDeriv ξ) 2 μ :=
  (contDiff_fderiv_apply_of_smooth hξ ((1 : ℝ), (0 : Vec 2))).continuous.memLp_of_hasCompactSupport
    (hasCompactSupport_fderiv_apply hc _)

theorem stSpaceGrad_memLp {μ : Measure (ℝ × Vec 2)} [IsFiniteMeasureOnCompacts μ] {ξ : ℝ × Vec 2 → ℝ}
    (hξ : ContDiff ℝ (⊤ : ℕ∞) ξ) (hc : HasCompactSupport ξ) (i : Fin 2) :
    MemLp (fun p => stSpaceGrad ξ p i) 2 μ :=
  (contDiff_fderiv_apply_of_smooth hξ ((0 : ℝ), basisVec i)).continuous.memLp_of_hasCompactSupport
    (hasCompactSupport_fderiv_apply hc _)

theorem spGrad_slice_eq {ξ : ℝ × Vec 2 → ℝ} (hξ : ContDiff ℝ (⊤ : ℕ∞) ξ) (τ : ℝ) (y : Vec 2)
    (i : Fin 2) : spGrad (fun z => ξ (τ, z)) y i = stSpaceGrad ξ (τ, y) i := by
  simp [spGrad, stSpaceGrad, fderiv_slice hξ]

/-- **Conservative to non-conservative form.** -/
theorem nonconservative_of_flux (hc : LabelCoeffs G V V₀ ta tb) {R κ : ℝ}
    {U : ℝ × Vec 2 → ℝ} {DU : ℝ × Vec 2 → Vec 2}
    (hU : MemLp U 2 (volume.restrict (Set.Ioo ta tb ×ˢ euclidBall 0 R)))
    (hDU : ∀ i : Fin 2,
      MemLp (fun p => DU p i) 2 (volume.restrict (Set.Ioo ta tb ×ˢ euclidBall 0 R)))
    (hgrad : ∀ᵐ τ ∂(volume.restrict (Set.Ioo ta tb)),
      HasWeakGradientOn (euclidBall 0 R) (fun y => U (τ, y)) (fun y => DU (τ, y)))
    (hweak : ∀ φ : ℝ × Vec 2 → ℝ, IsSTTest (Set.Ioo ta tb ×ˢ euclidBall 0 R) φ →
      ∫ p in Set.Ioo ta tb ×ˢ euclidBall 0 R,
        (-(U p * stTimeDeriv φ p) + vecDot (κ • (G p).mulVec (DU p) - U p • V p)
          (stSpaceGrad φ p)) = 0) :
    ∀ ξ, IsSTTest (Set.Ioo ta tb ×ˢ euclidBall 0 R) ξ →
      ∫ p in Set.Ioo ta tb ×ˢ euclidBall 0 R, (-(U p * stTimeDeriv ξ p) +
        vecDot (V p) (DU p) * ξ p + κ * vecDot ((G p).mulVec (DU p)) (stSpaceGrad ξ p)) = 0 := by
  intro ξ hξ
  set B := euclidBall (0 : Vec 2) R with hBdef
  have hBo : IsOpen B := pipe_isOpen_euclidBall 0 R
  have hBm : MeasurableSet B := hBo.measurableSet
  set μ := volume.restrict (Set.Ioo ta tb ×ˢ B) with hμ
  have hae := ae_mem_cyl (ta := ta) (tb := tb) hBm
  have hVm : ∀ i, AEStronglyMeasurable (fun p => V p i) μ := fun i =>
    ((measurable_pi_apply i).comp hc.Vmeas).aestronglyMeasurable
  have hVb : ∀ᵐ p ∂μ, ∀ i, ‖V p i‖ ≤ V₀ :=
    hae.mono fun p hp i => by rw [Real.norm_eq_abs]; exact hc.Ventry_bound hp i
  have hξt := stTimeDeriv_memLp (μ := μ) hξ.1 hξ.2.1
  have hξg := fun i => stSpaceGrad_memLp (μ := μ) hξ.1 hξ.2.1 i
  have hξ2 : MemLp ξ 2 μ := hξ.1.continuous.memLp_of_hasCompactSupport hξ.2.1
  have hP := memLp_flux hc hBm (κ := κ) hU hDU
  have i1 : Integrable (fun p => U p * stTimeDeriv ξ p) μ := hU.integrable_mul hξt
  have i2 : Integrable (fun p => vecDot (κ • (G p).mulVec (DU p) - U p • V p)
      (stSpaceGrad ξ p)) μ := by
    have : (fun p => vecDot (κ • (G p).mulVec (DU p) - U p • V p) (stSpaceGrad ξ p)) =
        fun p => ∑ i : Fin 2, (κ • (G p).mulVec (DU p) - U p • V p) i * stSpaceGrad ξ p i := rfl
    rw [this]
    exact integrable_finsetSum _ fun i _ => (hP i).integrable_mul (hξg i)
  have hVDU : MemLp (fun p => vecDot (V p) (DU p)) 2 μ :=
    memLp_dot_bdd (a := V) (v := DU) hVm hVb hDU
  have hVξ : MemLp (fun p => vecDot (V p) (stSpaceGrad ξ p)) 2 μ :=
    memLp_dot_bdd (a := V) (v := stSpaceGrad ξ) hVm hVb hξg
  have i3 : Integrable (fun p => vecDot (V p) (DU p) * ξ p) μ := hVDU.integrable_mul hξ2
  have i4 : Integrable (fun p => U p * vecDot (V p) (stSpaceGrad ξ p)) μ := hU.integrable_mul hVξ
  -- the vanishing of the transport term
  have hm : ∫ p in Set.Ioo ta tb ×ˢ B, (vecDot (V p) (DU p) * ξ p +
      U p * vecDot (V p) (stSpaceGrad ξ p)) = 0 := by
    have him : Integrable (fun p => vecDot (V p) (DU p) * ξ p +
        U p * vecDot (V p) (stSpaceGrad ξ p)) μ := i3.add i4
    have him' := him
    rw [hμ, volume_restrict_prod_eq] at him'
    rw [volume_restrict_prod_eq, integral_prod _ him']
    refine integral_eq_zero_of_ae ?_
    have hUs := ae_slice_memLp_gen hU
    have hDs : ∀ᵐ τ ∂(volume.restrict (Set.Ioo ta tb)), ∀ i : Fin 2,
        MemLp (fun y => DU (τ, y) i) 2 (volume.restrict B) := by
      rw [Filter.eventually_all]
      exact fun i => ae_slice_memLp_gen (hDU i)
    filter_upwards [hUs, hDs, hgrad, ae_restrict_mem measurableSet_Ioo] with τ hτU hτD hτg hτm
    have hτI : τ ∈ Set.Icc ta tb := ⟨hτm.1.le, hτm.2.le⟩
    have hχ := isSpTest_slice hξ τ
    have hdm : ∀ i : Fin 2, AEStronglyMeasurable (fun y => V (τ, y) i) (volume.restrict B) :=
      fun i => (((measurable_pi_apply i).comp hc.Vmeas).comp
        (measurable_prodMk_left (x := τ))).aestronglyMeasurable
    have hbd : ∀ᵐ y ∂(volume.restrict B), vecNormSq (V (τ, y)) ≤ V₀ ^ 2 :=
      Filter.Eventually.of_forall fun y => hc.Vbd (τ, y) hτI
    have hdiv : ∀ ψ0, IsSpTest B ψ0 → ∫ y in B, vecDot (V (τ, y)) (spGrad ψ0 y) = 0 := by
      intro ψ0 hψ0
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
      · exact hc.Vdiv τ hτI ψ0 hψ0.1 hψ0.2.1
      · intro y hy
        have : y ∉ tsupport ψ0 := fun h => hy (hψ0.2.2 h)
        have h0 : spGrad ψ0 y = 0 := by
          ext i
          simp [spGrad, fderiv_of_notMem_tsupport (𝕜 := ℝ) this]
        simp [h0, vecDot]
    have hψw := hasWeakGradientOn_smul_smooth hBo hτg hτU hτD hχ
    have hgc : ∀ i : Fin 2, Continuous fun y => spGrad (fun z => ξ (τ, z)) y i := fun i =>
      (contDiff_fderiv_apply_of_smooth hχ.1 (basisVec i)).continuous
    have hgcs : ∀ i : Fin 2, HasCompactSupport fun y => spGrad (fun z => ξ (τ, z)) y i := fun i =>
      hasCompactSupport_fderiv_apply hχ.2.1 _
    have hψ : MemLp (fun y => ξ (τ, y) * U (τ, y)) 2 (volume.restrict B) :=
      memLp_two_mul_bdd hχ.1.continuous.aestronglyMeasurable
        (C := (hχ.1.continuous.bounded_above_of_compact_support hχ.2.1).choose)
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs]
          exact (hχ.1.continuous.bounded_above_of_compact_support hχ.2.1).choose_spec y) hτU
    have hDψ : ∀ i : Fin 2, MemLp
        (fun y => (ξ (τ, y) • DU (τ, y) + U (τ, y) • spGrad (fun z => ξ (τ, z)) y) i) 2
        (volume.restrict B) := by
      intro i
      have h1 : MemLp (fun y => ξ (τ, y) * DU (τ, y) i) 2 (volume.restrict B) :=
        memLp_two_mul_bdd hχ.1.continuous.aestronglyMeasurable
          (C := (hχ.1.continuous.bounded_above_of_compact_support hχ.2.1).choose)
          (Filter.Eventually.of_forall fun y => by
            rw [Real.norm_eq_abs]
            exact (hχ.1.continuous.bounded_above_of_compact_support hχ.2.1).choose_spec y)
          (hτD i)
      have h2 : MemLp (fun y => spGrad (fun z => ξ (τ, z)) y i * U (τ, y)) 2
          (volume.restrict B) :=
        memLp_two_mul_bdd (hgc i).aestronglyMeasurable
          (C := ((hgc i).bounded_above_of_compact_support (hgcs i)).choose)
          (Filter.Eventually.of_forall fun y => by
            rw [Real.norm_eq_abs]
            exact ((hgc i).bounded_above_of_compact_support (hgcs i)).choose_spec y) hτU
      refine (h1.add h2).ae_eq (Filter.Eventually.of_forall fun y => ?_)
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have := divFree_slice_grad hBo (pipe_volume_euclidBall_lt_top R).ne hdm hbd hdiv hψ hDψ
      hψw hχ.2.1 hχ.2.2 (fun y hy => by simp [image_eq_zero_of_notMem_tsupport hy])
    simp only [Pi.zero_apply]
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [vecDot, Fin.sum_univ_two, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      spGrad_slice_eq hξ.1 τ y]
    ring
  -- assemble
  have hsplit : ∀ p, -(U p * stTimeDeriv ξ p) + vecDot (V p) (DU p) * ξ p +
      κ * vecDot ((G p).mulVec (DU p)) (stSpaceGrad ξ p) =
      (-(U p * stTimeDeriv ξ p) + vecDot (κ • (G p).mulVec (DU p) - U p • V p) (stSpaceGrad ξ p))
        + (vecDot (V p) (DU p) * ξ p + U p * vecDot (V p) (stSpaceGrad ξ p)) := by
    intro p
    simp only [vecDot, Fin.sum_univ_two, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp_rw [hsplit]
  have ia : Integrable (fun p => -(U p * stTimeDeriv ξ p) +
      vecDot (κ • (G p).mulVec (DU p) - U p • V p) (stSpaceGrad ξ p)) μ := i1.neg.add i2
  have ib : Integrable (fun p => vecDot (V p) (DU p) * ξ p +
      U p * vecDot (V p) (stSpaceGrad ξ p)) μ := i3.add i4
  rw [integral_add ia ib, hm, hweak ξ hξ, add_zero]

end AVRegularity.Applications.Davies
end

section
open MeasureTheory Homogenization Matrix Filter Topology
namespace AVRegularity.Applications.Davies

/-! # The equation for the difference of two label solutions

Solutions of the non-conservative label equation in `L²H¹` form a vector space. -/

variable {G : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {V : ℝ × Vec 2 → Vec 2} {V₀ ta tb : ℝ}

theorem nc_integrand_integrable (hc : LabelCoeffs G V V₀ ta tb) {R κ : ℝ}
    {U : ℝ × Vec 2 → ℝ} {DU : ℝ × Vec 2 → Vec 2}
    (hU : MemLp U 2 (volume.restrict (Set.Ioo ta tb ×ˢ euclidBall 0 R)))
    (hDU : ∀ i : Fin 2,
      MemLp (fun p => DU p i) 2 (volume.restrict (Set.Ioo ta tb ×ˢ euclidBall 0 R)))
    {ξ : ℝ × Vec 2 → ℝ} (hξ : IsSTTest (Set.Ioo ta tb ×ˢ euclidBall 0 R) ξ) :
    Integrable (fun p => -(U p * stTimeDeriv ξ p) + vecDot (V p) (DU p) * ξ p +
      κ * vecDot ((G p).mulVec (DU p)) (stSpaceGrad ξ p))
      (volume.restrict (Set.Ioo ta tb ×ˢ euclidBall 0 R)) := by
  set B := euclidBall (0 : Vec 2) R with hBdef
  have hBm : MeasurableSet B := (pipe_isOpen_euclidBall 0 R).measurableSet
  set μ := volume.restrict (Set.Ioo ta tb ×ˢ B) with hμ
  have hae := ae_mem_cyl (ta := ta) (tb := tb) hBm
  have hGm : ∀ i j, AEStronglyMeasurable (fun p => G p i j) μ := fun i j =>
    (hc.Gmeas i j).aestronglyMeasurable
  have hGb : ∀ᵐ p ∂μ, ∀ i j, ‖G p i j‖ ≤ 9 / 4 :=
    hae.mono fun p hp i j => by rw [Real.norm_eq_abs]; exact hc.entry_bound hp i j
  have hVm : ∀ i, AEStronglyMeasurable (fun p => V p i) μ := fun i =>
    ((measurable_pi_apply i).comp hc.Vmeas).aestronglyMeasurable
  have hVb : ∀ᵐ p ∂μ, ∀ i, ‖V p i‖ ≤ V₀ :=
    hae.mono fun p hp i => by rw [Real.norm_eq_abs]; exact hc.Ventry_bound hp i
  have hξt := stTimeDeriv_memLp (μ := μ) hξ.1 hξ.2.1
  have hξg := fun i => stSpaceGrad_memLp (μ := μ) hξ.1 hξ.2.1 i
  have hξ2 : MemLp ξ 2 μ := hξ.1.continuous.memLp_of_hasCompactSupport hξ.2.1
  have i1 : Integrable (fun p => U p * stTimeDeriv ξ p) μ := hU.integrable_mul hξt
  have hVDU : MemLp (fun p => vecDot (V p) (DU p)) 2 μ :=
    memLp_dot_bdd (a := V) (v := DU) hVm hVb hDU
  have i3 : Integrable (fun p => vecDot (V p) (DU p) * ξ p) μ := hVDU.integrable_mul hξ2
  have hG : ∀ i, MemLp (fun p => ((G p).mulVec (DU p)) i) 2 μ := fun i =>
    memLp_matvec_bdd (M := G) (v := DU) hGm hGb hDU i
  have i5 : Integrable (fun p => vecDot ((G p).mulVec (DU p)) (stSpaceGrad ξ p)) μ := by
    have : (fun p => vecDot ((G p).mulVec (DU p)) (stSpaceGrad ξ p)) =
        fun p => ∑ i : Fin 2, ((G p).mulVec (DU p)) i * stSpaceGrad ξ p i := rfl
    rw [this]
    exact integrable_finsetSum _ fun i _ => (hG i).integrable_mul (hξg i)
  exact (i1.neg.add i3).add (i5.const_mul κ)

/-- Differences of solutions are solutions. -/
theorem weakEq_sub (hc : LabelCoeffs G V V₀ ta tb) {R κ : ℝ}
    {U₁ U₂ : ℝ × Vec 2 → ℝ} {D₁ D₂ : ℝ × Vec 2 → Vec 2}
    (hU₁ : MemLp U₁ 2 (volume.restrict (Set.Ioo ta tb ×ˢ euclidBall 0 R)))
    (hD₁ : ∀ i : Fin 2,
      MemLp (fun p => D₁ p i) 2 (volume.restrict (Set.Ioo ta tb ×ˢ euclidBall 0 R)))
    (hU₂ : MemLp U₂ 2 (volume.restrict (Set.Ioo ta tb ×ˢ euclidBall 0 R)))
    (hD₂ : ∀ i : Fin 2,
      MemLp (fun p => D₂ p i) 2 (volume.restrict (Set.Ioo ta tb ×ˢ euclidBall 0 R)))
    (h₁ : ∀ ξ, IsSTTest (Set.Ioo ta tb ×ˢ euclidBall 0 R) ξ →
      ∫ p in Set.Ioo ta tb ×ˢ euclidBall 0 R, (-(U₁ p * stTimeDeriv ξ p) +
        vecDot (V p) (D₁ p) * ξ p + κ * vecDot ((G p).mulVec (D₁ p)) (stSpaceGrad ξ p)) = 0)
    (h₂ : ∀ ξ, IsSTTest (Set.Ioo ta tb ×ˢ euclidBall 0 R) ξ →
      ∫ p in Set.Ioo ta tb ×ˢ euclidBall 0 R, (-(U₂ p * stTimeDeriv ξ p) +
        vecDot (V p) (D₂ p) * ξ p + κ * vecDot ((G p).mulVec (D₂ p)) (stSpaceGrad ξ p)) = 0) :
    ∀ ξ, IsSTTest (Set.Ioo ta tb ×ˢ euclidBall 0 R) ξ →
      ∫ p in Set.Ioo ta tb ×ˢ euclidBall 0 R, (-((U₁ p - U₂ p) * stTimeDeriv ξ p) +
        vecDot (V p) (D₁ p - D₂ p) * ξ p +
        κ * vecDot ((G p).mulVec (D₁ p - D₂ p)) (stSpaceGrad ξ p)) = 0 := by
  intro ξ hξ
  have i1 := nc_integrand_integrable (κ := κ) hc hU₁ hD₁ hξ
  have i2 := nc_integrand_integrable (κ := κ) hc hU₂ hD₂ hξ
  have := integral_sub i1 i2
  rw [h₁ ξ hξ, h₂ ξ hξ, sub_zero] at this
  rw [← this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [vecDot, Fin.sum_univ_two, Pi.sub_apply, Matrix.mulVec_sub]
  ring

end AVRegularity.Applications.Davies
end

section
open MeasureTheory Homogenization Matrix
namespace AVRegularity.Applications.Davies

/-! # The cutoff traces and their bounds

For a cutoff `ζ` with `|∇ζ| ≤ L/R` the trace `W` of `ζ U` satisfies, for `t ≥ t₁ - 6T`,
`‖W(t)‖² ≤ K₀ R² A²` and `κ ∬_{(t₁-6T,t₁)} ζ² DU·G DU ≤ K₀ R² A²`. -/

section
open AVRegularity.Applications

variable {G : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {V : ℝ × Vec 2 → Vec 2}

theorem davies_traces {V₀ T t₁ R κ L Lm A : ℝ} (hc : LabelCoeffs G V V₀ (t₁ - 8 * T) t₁)
    (hT : 0 < T) (hκ : 0 < κ) (hR : 0 < R)
    {U : ℝ × Vec 2 → ℝ} {DU : ℝ × Vec 2 → Vec 2}
    (hU : MemLp U 2 (volume.restrict (Set.Ioo (t₁ - 8 * T) t₁ ×ˢ euclidBall 0 R)))
    (hDU : ∀ i : Fin 2, MemLp (fun p => DU p i) 2
      (volume.restrict (Set.Ioo (t₁ - 8 * T) t₁ ×ˢ euclidBall 0 R)))
    (hgrad : ∀ᵐ τ ∂(volume.restrict (Set.Ioo (t₁ - 8 * T) t₁)),
      HasWeakGradientOn (euclidBall 0 R) (fun y => U (τ, y)) (fun y => DU (τ, y)))
    (hweak : ∀ φ : ℝ × Vec 2 → ℝ, IsSTTest (Set.Ioo (t₁ - 8 * T) t₁ ×ˢ euclidBall 0 R) φ →
      ∫ p in Set.Ioo (t₁ - 8 * T) t₁ ×ˢ euclidBall 0 R,
        (-(U p * stTimeDeriv φ p) + vecDot (κ • (G p).mulVec (DU p) - U p • V p)
          (stSpaceGrad φ p)) = 0)
    {ζ : Vec 2 → ℝ} (hζ : IsSpTest (euclidBall 0 R) ζ) (hζ0 : ∀ y, 0 ≤ ζ y) (hζ1 : ∀ y, ζ y ≤ 1)
    (hL : 0 ≤ L) (hLm : L ≤ Lm) (hζN : ∀ y, vecNormSq (spGrad ζ y) ≤ (L / R) ^ 2)
    (hM : ∫ p in Set.Ioo (t₁ - 8 * T) t₁ ×ˢ euclidBall 0 R, U p ^ 2 ≤ 32 * T * R ^ 2 * A ^ 2)
    (hκT : κ * T ≤ R ^ 2) (hVT : V₀ * T ≤ R) :
    ∃ W : ℝ → Lp ℝ 2 (volume.restrict (euclidBall 0 R)),
      ContinuousOn W (Set.Icc (t₁ - 8 * T) t₁) ∧
      (∀ᵐ τ ∂(volume.restrict (Set.Ioo (t₁ - 8 * T) t₁)),
        (W τ : Vec 2 → ℝ) =ᵐ[volume.restrict (euclidBall 0 R)] fun y => ζ y * U (τ, y)) ∧
      (∀ τ ∈ Set.Icc (t₁ - 8 * T + 2 * T) t₁,
        ‖W τ‖ ^ 2 ≤ (16 + 288 * Lm ^ 2 + 64 * Lm) * (R ^ 2 * A ^ 2)) ∧
      κ * ∫ p in Set.Ioo (t₁ - 8 * T + 2 * T) t₁ ×ˢ euclidBall 0 R,
          ζ p.2 ^ 2 * vecDot (DU p) ((G p).mulVec (DU p)) ≤
        (16 + 288 * Lm ^ 2 + 64 * Lm) * (R ^ 2 * A ^ 2) := by
  have hab : t₁ - 8 * T < t₁ := by linarith
  obtain ⟨W, hWc, hWae, hWb, hgb⟩ := cutoff_energy_bound hc hab (σ := 2 * T) hκ.le
    (by positivity) (by linarith) hU hDU hgrad hweak hζ hζ0 hζ1 (N := L / R) (by positivity) hζN
  have hV₀ := hc.V0
  have hbound := step1_alg hκ.le hT hR hL hLm hV₀
    (M := ∫ p in Set.Ioo (t₁ - 8 * T) t₁ ×ˢ euclidBall 0 R, U p ^ 2) hM hκT hVT
  refine ⟨W, hWc, hWae, fun τ hτ => (hWb τ hτ).trans hbound, ?_⟩
  exact hgb.trans hbound
end

/-! # Restricting the label equation to a later time window -/

section
open AVRegularity.Applications

theorem nc_eq_restrict {a a' b : ℝ} (ha : a ≤ a') {B : Set (Vec 2)} (hB : MeasurableSet B)
    {κ : ℝ} {G : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {V : ℝ × Vec 2 → Vec 2}
    {U : ℝ × Vec 2 → ℝ} {DU : ℝ × Vec 2 → Vec 2}
    (h : ∀ ξ, IsSTTest (Set.Ioo a b ×ˢ B) ξ →
      ∫ p in Set.Ioo a b ×ˢ B, (-(U p * stTimeDeriv ξ p) +
        vecDot (V p) (DU p) * ξ p + κ * vecDot ((G p).mulVec (DU p)) (stSpaceGrad ξ p)) = 0) :
    ∀ ξ, IsSTTest (Set.Ioo a' b ×ˢ B) ξ →
      ∫ p in Set.Ioo a' b ×ˢ B, (-(U p * stTimeDeriv ξ p) +
        vecDot (V p) (DU p) * ξ p + κ * vecDot ((G p).mulVec (DU p)) (stSpaceGrad ξ p)) = 0 := by
  intro ξ hξ
  have hsub : Set.Ioo a' b ×ˢ B ⊆ Set.Ioo a b ×ˢ B :=
    Set.prod_mono (Set.Ioo_subset_Ioo ha le_rfl) le_rfl
  have hξ' : IsSTTest (Set.Ioo a b ×ˢ B) ξ := ⟨hξ.1, hξ.2.1, hξ.2.2.trans hsub⟩
  rw [← h ξ hξ']
  refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (measurableSet_Ioo.prod hB) hsub ?_).symm
  intro p hp
  have hnot : p ∉ tsupport ξ := fun hm => hp.2 (hξ.2.2 hm)
  obtain ⟨h1, h2, _⟩ := st_derivs_zero hnot
  simp [h1, h2, image_eq_zero_of_notMem_tsupport hnot, vecDot]
end

end AVRegularity.Applications.Davies
end

section
open MeasureTheory Homogenization AVenhance
namespace AVRegularity.Applications.Davies

/-! # Integrals over a small ball are bounded by the cell integral

For a nonnegative `ℤ²`-periodic function `G`, `∫_A G ≤ 81 ∫_{(0,1)²} G` for every measurable
`A ⊆ {‖x‖ ≤ 1}`. The constant `81` comes from the partition of unity `cutoffZ`, whose square is at
least `1/81` on the sup-ball of radius one. -/

open AVRegularity.Applications

theorem cutBump_sq_supBdd : SupBdd 3 (fun _ y => (cutBump : Vec 2 → ℝ) y ^ 2) := by
  intro t y hne
  have : (cutBump : Vec 2 → ℝ) y ≠ 0 := fun h => hne (by simp [h])
  exact (cutBump_norm_lt this).le

theorem perX_cutBump_sq_le {x : Vec 2} (hx : ‖x‖ ≤ 1) :
    perX (fun y => (cutBump : Vec 2 → ℝ) y ^ 2) x ≤ 81 := by
  unfold perX
  rw [perST_eq_sum (R := 3) (r := 1) (M := 4) (by norm_num) cutBump_sq_supBdd 0 hx]
  have hcard : (latBox 4).card = 81 := by
    simp [latBox, Fintype.card_piFinset]
  calc ∑ n ∈ latBox 4, (cutBump : Vec 2 → ℝ) (x + latticeShift n) ^ 2
      ≤ ∑ n ∈ latBox 4, (1 : ℝ) := by
        refine Finset.sum_le_sum fun n _ => ?_
        have h0 : 0 ≤ (cutBump : Vec 2 → ℝ) (x + latticeShift n) := cutBump.nonneg
        have h1 : (cutBump : Vec 2 → ℝ) (x + latticeShift n) ≤ 1 := cutBump.le_one
        nlinarith
    _ = 81 := by simp [hcard]

theorem perX_cutBump_sq_ge {x : Vec 2} (hx : ‖x‖ ≤ 1) :
    1 ≤ perX (fun y => (cutBump : Vec 2 → ℝ) y ^ 2) x := by
  unfold perX
  rw [perST_eq_sum (R := 3) (r := 1) (M := 4) (by norm_num) cutBump_sq_supBdd 0 hx]
  have hb : (cutBump : Vec 2 → ℝ) x = 1 := by
    apply cutBump.one_of_mem_closedBall
    simpa [cutBump, dist_zero_right] using hx.trans (by norm_num : (1 : ℝ) ≤ 2)
  have h0 : (0 : Fin 2 → ℤ) ∈ latBox 4 := by
    simp [latBox, Fintype.mem_piFinset]
  have h00 : latticeShift (0 : Fin 2 → ℤ) = 0 := by funext i; simp [latticeShift]
  calc (1 : ℝ) = (cutBump : Vec 2 → ℝ) (x + latticeShift 0) ^ 2 := by
        rw [h00, add_zero, hb]; norm_num
    _ ≤ _ := Finset.single_le_sum (f := fun n => (cutBump : Vec 2 → ℝ) (x + latticeShift n) ^ 2)
        (fun n _ => sq_nonneg _) h0

theorem cutoffZ_sq_ge {x : Vec 2} (hx : ‖x‖ ≤ 1) : 1 / 81 ≤ cutoffZ x ^ 2 := by
  have hb : (cutBump : Vec 2 → ℝ) x = 1 := by
    apply cutBump.one_of_mem_closedBall
    simpa [cutBump, dist_zero_right] using hx.trans (by norm_num : (1 : ℝ) ≤ 2)
  have hS1 := perX_cutBump_sq_le hx
  have hS0 := perX_cutBump_sq_ge hx
  unfold cutoffZ
  rw [div_pow, Real.sq_sqrt (by linarith), hb, one_pow]
  exact one_div_le_one_div_of_le (by linarith) hS1


theorem integrable_mul_cutoffZ_sq {G : Vec 2 → ℝ} (hper : IsZ2Periodic G)
    (hG : Integrable G (volume.restrict unitCube)) :
    Integrable (fun x => G x * cutoffZ x ^ 2) := by
  have hGB := integrableOn_supBall_space hper hG 3
  have hc : Continuous fun x => cutoffZ x ^ 2 := cutoffZ_contDiff.continuous.pow 2
  have hcc : HasCompactSupport fun x => cutoffZ x ^ 2 := by
    have : (fun x => cutoffZ x ^ 2) = fun x => cutoffZ x * cutoffZ x := by funext x; ring
    rw [this]; exact cutoffZ_hasCompactSupport.mul_left
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcc
  have h1 : IntegrableOn (fun x => G x * cutoffZ x ^ 2) (supBall 3) :=
    hGB.mul_bdd hc.aestronglyMeasurable (c := C) (Filter.Eventually.of_forall hC)
  refine h1.integrable_of_forall_notMem_eq_zero fun x hx => ?_
  have : cutoffZ x = 0 := by
    by_contra hne
    exact hx (cutoffZ_supBdd 0 x hne)
  simp [this]

/-- For a nonnegative periodic `G`, the integral over a small set is at most `81` times the cell
integral. -/
theorem setIntegral_le_cell {G : Vec 2 → ℝ} (hper : IsZ2Periodic G) (hG0 : ∀ x, 0 ≤ G x)
    (hG : Integrable G (volume.restrict unitCube)) {A : Set (Vec 2)} (hA : MeasurableSet A)
    (hAs : A ⊆ supBall 1) :
    ∫ x in A, G x ≤ 81 * ∫ x in unitCube, G x := by
  have hint := integrable_mul_cutoffZ_sq hper hG
  have heq := integral_unfold_space (G := G) (ρ := fun y => cutoffZ y ^ 2)
    (cutoffZ_contDiff.pow 2) (by
      have : (fun x => cutoffZ x ^ 2) = fun x => cutoffZ x * cutoffZ x := by funext x; ring
      rw [this]; exact cutoffZ_hasCompactSupport.mul_left) hper hG
  have h1 : ∀ x, perX (fun y => cutoffZ y ^ 2) x = 1 := perX_cutoffZ_sq
  simp only [h1, mul_one] at heq
  have hA' : IntegrableOn G A := (show IntegrableOn G (supBall 1) volume from integrableOn_supBall_space hper hG 1).mono_set hAs
  calc ∫ x in A, G x ≤ ∫ x in A, 81 * (G x * cutoffZ x ^ 2) := by
        refine setIntegral_mono_on hA' (hint.integrableOn.const_mul 81) hA fun x hx => ?_
        have := cutoffZ_sq_ge (hAs hx)
        have := hG0 x
        nlinarith
    _ = 81 * ∫ x in A, G x * cutoffZ x ^ 2 := integral_const_mul _ _
    _ ≤ 81 * ∫ x, G x * cutoffZ x ^ 2 := by
        refine mul_le_mul_of_nonneg_left (setIntegral_le_integral hint ?_) (by norm_num)
        exact Filter.Eventually.of_forall fun x => mul_nonneg (hG0 x) (sq_nonneg _)
    _ = 81 * ∫ x in unitCube, G x := by rw [heq]

end AVRegularity.Applications.Davies
end

section
open MeasureTheory Homogenization AVenhance AVenhance.Infra.Section5 AVRegularity.CycleReference
open scoped Matrix
namespace AVRegularity.Applications.Davies

/-! # `L²` and weak-gradient transfer through the material chart

For periodic data on the torus window, the pull-back `g ↦ g(t, F_t y)` is square integrable on the
label cylinder `(a,b) × B_R`, and weak gradients pull back by the chain rule. -/

open AVRegularity.Applications

theorem chart_bound {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T : ℝ}
    (ch : IsPipeChart b0 X t₁ T) (a b R : ℝ) :
    ∃ r : ℝ, ∀ t ∈ Set.Icc a b, ∀ y ∈ euclidBall (0 : Vec 2) R, ‖X t y t₁‖ ≤ r := by
  have hK : IsCompact (Set.Icc a b ×ˢ Metric.closedBall (0 : Vec 2) |R|) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨r, hr⟩ := hK.exists_bound_of_continuousOn
    (f := fun p : ℝ × Vec 2 => X p.1 p.2 t₁) ch.smoothF.continuous.continuousOn
  refine ⟨r, fun t ht y hy => hr (t, y) ⟨ht, ?_⟩⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have h1 := norm_le_sqrt_vecNormSq y
  have h2 : vecNormSq y < R ^ 2 := by simpa [euclidBall] using hy
  exact h1.trans (Real.sqrt_le_iff.2 ⟨abs_nonneg _, by rw [sq_abs]; exact h2.le⟩)

theorem memLp_comp_chart {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T : ℝ}
    (ch : IsPipeChart b0 X t₁ T) (hT : 0 < T) {a b : ℝ} (ha : t₁ - 8 * T ≤ a) (hb : b ≤ t₁)
    (R : ℝ) {g : ℝ → Vec 2 → ℝ}
    (hper : ∀ᵐ t ∂(volume.restrict (Set.Ioo a b)), IsZ2Periodic (g t))
    (hg : MemLp (fun p : ℝ × Vec 2 => g p.1 p.2) 2 (volume.restrict (Set.Ioo a b ×ˢ unitCube))) :
    MemLp (fun p : ℝ × Vec 2 => g p.1 (X p.1 p.2 t₁)) 2
      (volume.restrict (Set.Ioo a b ×ˢ euclidBall 0 R)) := by
  obtain ⟨r, hr⟩ := chart_bound ch a b R
  have hs := memLp_two_supBall_of_cell measurableSet_Ioo hper hg r
  have hSm : MeasurableSet (Set.Ioo a b ×ˢ supBall r) :=
    measurableSet_Ioo.prod (measurableSet_supBall r)
  have hmp := (pipeMap_mp ch hT).restrict_preimage_emb (pipeMap_measurableEmbedding ch hT)
    (Set.Ioo a b ×ˢ supBall r)
  have h2 := hs.comp_measurePreserving hmp
  have hsub : Set.Ioo a b ×ˢ euclidBall (0 : Vec 2) R ⊆
      pipeMap X t₁ T ⁻¹' (Set.Ioo a b ×ˢ supBall r) := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    have htI : t ∈ Set.Icc (t₁ - 8 * T) t₁ := ⟨ha.trans ht.1.le, ht.2.le.trans hb⟩
    simp only [Set.mem_preimage, pipeMap_apply_of_mem htI, Set.mem_prod]
    exact ⟨ht, hr t ⟨ht.1.le, ht.2.le⟩ y hy⟩
  have h3 := h2.mono_measure (Measure.restrict_mono hsub le_rfl)
  refine h3.ae_eq ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' (measurableSet_Ioo.prod (pipe_isOpen_euclidBall 0 R).measurableSet)]
  refine Filter.Eventually.of_forall fun ⟨t, y⟩ hp => ?_
  have htI : t ∈ Set.Icc (t₁ - 8 * T) t₁ := ⟨ha.trans hp.1.1.le, hp.1.2.le.trans hb⟩
  simp [Function.comp, pipeMap_apply_of_mem htI]

section Grad

variable {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (t s : ℝ)

include hφ in
/-- The chain rule for weak gradients through the chart, for locally integrable data. -/
theorem streamFlow_weakGradient_loc {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (hul : LocallyIntegrable u volume) (hDul : ∀ i, LocallyIntegrable (fun x => Du x i) volume)
    (hw : HasWeakGradientOn Set.univ u Du) :
    HasWeakGradientOn Set.univ (fun y => u (AVRegularity.streamFlow φ hφ t y s))
      (fun y => (jacMatrix (fun x => AVRegularity.streamFlow φ hφ t x s) y)ᵀ.mulVec
        (Du (AVRegularity.streamFlow φ hφ t y s))) := by
  let X := streamFlowHomeomorph hφ t s
  have hX : ContDiff ℝ (⊤ : ℕ∞) (X : Vec 2 → Vec 2) := streamFlow_spatial_smooth hφ t s
  have hY : ContDiff ℝ (⊤ : ℕ∞) (X.symm : Vec 2 → Vec 2) := streamFlow_spatial_smooth hφ s t
  have hd : ∀ x, (jacMatrix (X.symm : Vec 2 → Vec 2) x).det = 1 :=
    fun x => streamFlow_jacMatrix_det_one hφ s t x
  have ht := weakGradient_homeomorph_piola X (streamFlow_measurePreserving hφ t s)
    hY hd hul hDul hw
  have hc (y : Vec 2) : rowCofactor (gradMatrix (X.symm : Vec 2 → Vec 2) (X y)) =
      jacMatrix (X : Vec 2 → Vec 2) y := by
    rw [rowCofactor_eq_jacMatrix_inverse (hY.differentiable (by simp)) _ (hd _)]
    exact homeomorph_inverse_jacMatrix X (hX.differentiable (by simp))
      (hY.differentiable (by simp)) y
  simp_rw [hc] at ht
  exact ht

end Grad

end AVRegularity.Applications.Davies
end

section
open MeasureTheory Homogenization AVenhance Matrix Filter Topology
open scoped Matrix
namespace AVRegularity.Applications.Davies

/-! # The torus solution `u_f` in label coordinates

For a weak solution `u` on the torus window, `U_f(t,y) = u(t, F_t y)` with
`DU_f = (D_yF_t)ᵀ (Du)(t, F_t y)` is square integrable with square integrable gradient on the label
cylinder, has slice weak gradient `DU_f`, and satisfies the non-conservative chart equation
`∂ₜU_f = div(κ G∇U_f) - V·∇U_f`. -/

open AVRegularity.Applications

/-- The pulled-back solution. -/
def Ufun (u : ℝ → Vec 2 → ℝ) (X : ℝ → Vec 2 → ℝ → Vec 2) (t₁ : ℝ) (p : ℝ × Vec 2) : ℝ :=
  u p.1 (X p.1 p.2 t₁)

/-- The pulled-back gradient `(D_yF_t)ᵀ (Du)(t, F_t y)`. -/
def DUfun (Du : ℝ → Vec 2 → Vec 2) (X : ℝ → Vec 2 → ℝ → Vec 2) (t₁ : ℝ) (p : ℝ × Vec 2) :
    Vec 2 :=
  (pipeJac X t₁ p)ᵀ.mulVec (Du p.1 (X p.1 p.2 t₁))

section Chart

variable {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T : ℝ}
  (ch : IsPipeChart b0 X t₁ T)

include ch

theorem pipeJac_entry_bound {t : ℝ} (ht : t ∈ Set.Icc (t₁ - 8 * T) t₁) (y : Vec 2) (i j : Fin 2) :
    |pipeJac X t₁ (t, y) i j| ≤ 3 / 2 := by
  have h := (pipeJac_close ch ht y (basisVec j)).2
  have h2 : vecNormSq (basisVec j : Vec 2) = 1 := by
    fin_cases j <;> simp [vecNormSq_two, basisVec]
  rw [h2, mul_one] at h
  have h3 : (pipeJac X t₁ (t, y)).mulVec (basisVec j) i = pipeJac X t₁ (t, y) i j := by
    fin_cases j <;> fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, basisVec]
  have h4 := abs_coord_le_sqrt ((pipeJac X t₁ (t, y)).mulVec (basisVec j)) i
  rw [h3] at h4
  refine h4.trans (Real.sqrt_le_iff.2 ⟨by norm_num, ?_⟩)
  nlinarith

/-- `DU_f · G DU_f = |Du ∘ F|²`. -/
theorem quad_DUf {t : ℝ} (ht : t ∈ Set.Icc (t₁ - 8 * T) t₁) (y : Vec 2) (w : Vec 2) :
    vecDot ((pipeJac X t₁ (t, y))ᵀ.mulVec w)
      ((pipeMetric X t₁ (t, y)).mulVec ((pipeJac X t₁ (t, y))ᵀ.mulVec w)) = vecNormSq w := by
  have h2 : (pipeMetric X t₁ (t, y)).mulVec ((pipeJac X t₁ (t, y))ᵀ.mulVec w) =
      (pipeJac X t₁ (t, y))⁻¹.mulVec w := by
    unfold pipeMetric
    rw [← Matrix.mulVec_mulVec, inv_transpose_mulVec ch ht]
  rw [h2, vecDot_mulVec_left, Matrix.transpose_transpose, Matrix.mulVec_mulVec,
    pipeJac_mul_inv ch ht y, Matrix.one_mulVec]
  simp [vecDot, vecNormSq]

end Chart


section Memb

variable {b0 : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T : ℝ}
  (ch : IsPipeChart b0 X t₁ T) (hT : 0 < T) {a b : ℝ} (ha : t₁ - 8 * T ≤ a) (hb : b ≤ t₁) (R : ℝ)
  {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}

include ch hT ha hb

theorem Ufun_memLp
    (hper : ∀ᵐ t ∂(volume.restrict (Set.Ioo a b)), IsZ2Periodic (u t))
    (hU : MemLp (fun p : ℝ × Vec 2 => u p.1 p.2) 2
      (volume.restrict (Set.Ioo a b ×ˢ unitCube))) :
    MemLp (Ufun u X t₁) 2 (volume.restrict (Set.Ioo a b ×ˢ euclidBall 0 R)) :=
  memLp_comp_chart ch hT ha hb R hper hU

theorem DUfun_memLp
    (hDper : ∀ᵐ t ∂(volume.restrict (Set.Ioo a b)), IsZ2Periodic (Du t))
    (hDU : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => Du p.1 p.2 i) 2
      (volume.restrict (Set.Ioo a b ×ˢ unitCube))) (i : Fin 2) :
    MemLp (fun p => DUfun Du X t₁ p i) 2 (volume.restrict (Set.Ioo a b ×ˢ euclidBall 0 R)) := by
  have hBm : MeasurableSet (euclidBall (0 : Vec 2) R) := (pipe_isOpen_euclidBall 0 R).measurableSet
  have hj : ∀ j : Fin 2, MemLp (fun p : ℝ × Vec 2 => Du p.1 (X p.1 p.2 t₁) j) 2
      (volume.restrict (Set.Ioo a b ×ˢ euclidBall 0 R)) := fun j =>
    memLp_comp_chart ch hT ha hb R (g := fun t x => Du t x j)
      (hDper.mono fun t ht k x => by simp [ht k x]) (hDU j)
  have hae : ∀ᵐ p ∂(volume.restrict (Set.Ioo a b ×ˢ euclidBall (0 : Vec 2) R)),
      p.1 ∈ Set.Icc (t₁ - 8 * T) t₁ := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod hBm)] with p hp
    exact ⟨ha.trans hp.1.1.le, hp.1.2.le.trans hb⟩
  have h : ∀ j : Fin 2, MemLp (fun p : ℝ × Vec 2 => pipeJac X t₁ p j i *
      Du p.1 (X p.1 p.2 t₁) j) 2 (volume.restrict (Set.Ioo a b ×ˢ euclidBall 0 R)) := fun j =>
    memLp_two_mul_bdd (contDiff_pipeJac_entry ch j i).continuous.aestronglyMeasurable (C := 3 / 2)
      (hae.mono fun p hp => by
        rw [Real.norm_eq_abs]
        exact pipeJac_entry_bound ch hp p.2 j i) (hj j)
  refine ((h 0).add (h 1)).ae_eq (Filter.Eventually.of_forall fun p => ?_)
  simp [DUfun, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.transpose_apply]

end Memb


theorem locallyIntegrable_of_periodic {g : Vec 2 → ℝ} (hper : IsZ2Periodic g)
    (hg : MemL2On unitCube g) : LocallyIntegrable g volume := by
  intro x
  refine ⟨supBall (‖x‖ + 1), ?_, ?_⟩
  · have hx : x ∈ Metric.ball (0 : Vec 2) (‖x‖ + 1) := by
      rw [Metric.mem_ball, dist_zero_right]; linarith
    refine Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hx) fun y hy => ?_
    rw [Metric.mem_ball, dist_zero_right] at hy
    exact hy.le
  · have hm := memLp_two_supBall_space hper hg (‖x‖ + 1)
    have : IsFiniteMeasure (volume.restrict (supBall (‖x‖ + 1))) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply_univ]
      have : supBall (‖x‖ + 1) = Metric.closedBall (0 : Vec 2) (‖x‖ + 1) := by
        ext y; simp [supBall, dist_zero_right]
      rw [this]
      exact (isCompact_closedBall _ _).measure_lt_top
    exact hm.integrable (by norm_num)

section Grad

variable {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) {X : ℝ → Vec 2 → ℝ → Vec 2}
  (hX : IsFlow (streamVel φ) X) {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}

include hφ hX

/-- The slice weak gradient of the pulled-back solution. -/
theorem Ufun_slice_grad {t t₁ : ℝ} (h : IsPeriodicH1With (u t) (Du t)) :
    HasWeakGradientOn Set.univ (fun y => u t (X t y t₁))
      (fun y => (pipeJac X t₁ (t, y))ᵀ.mulVec (Du t (X t y t₁))) := by
  obtain ⟨hup, hDp, hu2, hDu2, hw⟩ := h
  have hul := locallyIntegrable_of_periodic hup hu2
  have hDul : ∀ i, LocallyIntegrable (fun x => Du t x i) volume := fun i =>
    locallyIntegrable_of_periodic (fun k x => by simp [hDp k x]) (hDu2 i)
  have := X_eq_streamFlow hφ hX
  subst this
  exact streamFlow_weakGradient_loc hφ t t₁ hul hDul hw

end Grad


section Weak

variable {b0 b : ℝ → Vec 2 → Vec 2} {X : ℝ → Vec 2 → ℝ → Vec 2} {t₁ T κ : ℝ}

/-- The non-conservative label equation of the pulled-back torus solution in a label ball. -/
theorem Ufun_weak (ch : IsPipeChart b0 X t₁ T) (hT : 0 < T) {a' : ℝ} (ha : t₁ - 8 * T ≤ a')
    {B : ℝ} (hbm : Measurable fun p : ℝ × Vec 2 => b p.1 p.2) (hbB : ∀ t x, ‖b t x‖ ≤ B)
    (hb0s : ContDiff ℝ (⊤ : ℕ∞) fun p : ℝ × Vec 2 => b0 p.1 p.2)
    (hb0d : ∀ t x, divSp (b0 t) x = 0) {O : Set (ℝ × Vec 2)}
    (hO : ∀ t ∈ Set.Ioo a' t₁, ∀ y, (t, X t y t₁) ∈ O)
    {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
    (hu : IsLocalWeakSolution b κ O (fun p => u p.1 p.2) (fun p => Du p.1 p.2)) (R : ℝ) :
    ∀ ξ, IsSTTest (Set.Ioo a' t₁ ×ˢ euclidBall 0 R) ξ →
      ∫ p in Set.Ioo a' t₁ ×ˢ euclidBall 0 R,
        (-(Ufun u X t₁ p * stTimeDeriv ξ p) +
          vecDot (pipeDrift b b0 X t₁ p) (DUfun Du X t₁ p) * ξ p +
          κ * vecDot ((pipeMetric X t₁ p).mulVec (DUfun Du X t₁ p)) (stSpaceGrad ξ p)) = 0 := by
  intro ξ hξ
  have hξ' : IsSTTest (Set.Ioo a' t₁ ×ˢ (Set.univ : Set (Vec 2))) ξ :=
    ⟨hξ.1, hξ.2.1, hξ.2.2.trans (Set.prod_mono le_rfl (Set.subset_univ _))⟩
  have h := pipe_pullback_weak_global_core ch hT ha hbm hbB hb0s hb0d hO hu hξ'
  rw [← h]
  refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (measurableSet_Ioo.prod MeasurableSet.univ) (Set.prod_mono le_rfl (Set.subset_univ _))
    ?_).symm
  intro p hp
  have hnot : p ∉ tsupport ξ := fun hm => hp.2 (hξ.2.2 hm)
  obtain ⟨h1, h2, _⟩ := st_derivs_zero hnot
  simp [h1, h2, image_eq_zero_of_notMem_tsupport hnot, vecDot]

end Weak

end AVRegularity.Applications.Davies
end

section
open MeasureTheory Homogenization AVenhance Matrix Filter Topology
namespace AVRegularity.Applications.Davies

/-! # Energy bounds for `u_f` in label coordinates

From the torus energy identity `‖u(t)‖² + 2κ∬|Du|² = ‖f‖²` and the cell comparison
`∫_{B_R} g(F_t y)² dy ≤ 81 ∫_{(0,1)²} g²` we obtain
`∬_{(s₀,t₁)×B_R} U_f² ≤ 81 (t₁ - s₀) ‖f‖²` and `κ ∬ |DU_f|² ≤ 162 ‖f‖²`. -/

open AVRegularity.Applications

theorem prod_integral_le {a b : ℝ} {B : Set (Vec 2)} {F : ℝ × Vec 2 → ℝ}
    (hF : IntegrableOn F (Set.Ioo a b ×ˢ B)) {c : ℝ → ℝ} (hc : IntegrableOn c (Set.Ioo a b))
    (h : ∀ᵐ τ ∂(volume.restrict (Set.Ioo a b)), ∫ y in B, F (τ, y) ≤ c τ) :
    ∫ p in Set.Ioo a b ×ˢ B, F p ≤ ∫ τ in Set.Ioo a b, c τ := by
  have hF' := hF
  unfold IntegrableOn at hF'
  rw [volume_restrict_prod_eq] at hF'
  rw [volume_restrict_prod_eq, integral_prod _ hF']
  exact integral_mono_ae hF'.integral_prod_left hc h

section Ball

variable {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) {X : ℝ → Vec 2 → ℝ → Vec 2}
  (hX : IsFlow (streamVel φ) X)

include hφ hX

theorem ball_sq_le {R : ℝ} (hR0 : 0 ≤ R) (hR : R ≤ 1) {g : Vec 2 → ℝ} (hp : IsZ2Periodic g)
    (hg : MemL2On unitCube g) (t s : ℝ) :
    ∫ y in euclidBall (0 : Vec 2) R, g (X t y s) ^ 2 ≤ 81 * l2NormSq g := by
  have hper : IsZ2Periodic (fun y => g (X t y s) ^ 2) := fun k y => by
    simp only [X_lattice hφ hX t s y k, hp k]
  have hint : Integrable (fun y => g (X t y s) ^ 2) (volume.restrict unitCube) :=
    (X_cell_memL2 hφ hX t s hp hg).integrable_sq
  have hsub : euclidBall (0 : Vec 2) R ⊆ supBall 1 := by
    intro y hy
    have h2 : vecNormSq y < R ^ 2 := by simpa [euclidBall] using hy
    have h1 := norm_le_sqrt_vecNormSq y
    have h3 : Real.sqrt (vecNormSq y) ≤ |R| :=
      Real.sqrt_le_iff.2 ⟨abs_nonneg _, by rw [sq_abs]; exact h2.le⟩
    have hR1 : |R| ≤ 1 := by rw [abs_of_nonneg hR0]; exact hR
    exact h1.trans (h3.trans hR1)
  have := setIntegral_le_cell hper (fun y => sq_nonneg _) hint
    (pipe_isOpen_euclidBall 0 R).measurableSet hsub
  rw [X_cell_integral hφ hX t s (u := fun x => g x ^ 2) (fun k x => by simp [hp k x])] at this
  exact this

end Ball


section Energy

variable {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) {X : ℝ → Vec 2 → ℝ → Vec 2}
  (hX : IsFlow (streamVel φ) X) {t₁ T : ℝ} (ch : IsPipeChart (streamVel φ) X t₁ T) (hT : 0 < T)
  {b : ℝ → Vec 2 → Vec 2} {κ s₀ e : ℝ} (hs : t₁ - 8 * T ≤ s₀) (hs1 : s₀ < t₁) (ht1 : t₁ ≤ e)
  {f : Vec 2 → ℝ} {u : ℝ → Vec 2 → ℝ} {Du : ℝ → Vec 2 → Vec 2}
  (hu : IsWeakSolutionOnWith b κ s₀ e f u Du) (hb : IsWindowDrift b s₀ e)
  (hf : MemL2On unitCube f) (hκ : 0 < κ) {R : ℝ} (hR0 : 0 ≤ R) (hR : R ≤ 1)

include hφ hX ch hT hs hs1 ht1 hu hb hf hκ hR0 hR

theorem uf_energy_U :
    ∫ p in Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R, Ufun u X t₁ p ^ 2 ≤ 81 * (t₁ - s₀) * l2NormSq f := by
  have hu' := hu
  obtain ⟨hslice, -, hL2, -, -, -, -, -⟩ := hu'
  have hen := (l2NormSq_le_of_weakSolutionOnWith hκ.le (hs1.trans_le ht1) hb hf hu).1
  have hsub : Set.Ioo s₀ t₁ ×ˢ unitCube ⊆ Set.Ioo s₀ e ×ˢ unitCube :=
    Set.prod_mono (Set.Ioo_subset_Ioo le_rfl ht1) le_rfl
  have hper : ∀ᵐ t ∂(volume.restrict (Set.Ioo s₀ t₁)), IsZ2Periodic (u t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (hslice t ⟨ht.1.le, ht.2.le.trans ht1⟩).1
  have hU := Ufun_memLp ch hT hs le_rfl R hper (hL2.mono_measure (Measure.restrict_mono hsub le_rfl))
  have hint : IntegrableOn (fun p => Ufun u X t₁ p ^ 2) (Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R) :=
    hU.integrable_sq
  refine (prod_integral_le hint (c := fun _ => 81 * l2NormSq f) (integrableOn_const (by simp [Real.volume_Ioo])) ?_).trans ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with τ hτ
    have hτI : τ ∈ Set.Icc s₀ e := ⟨hτ.1.le, hτ.2.le.trans ht1⟩
    have := ball_sq_le hφ hX hR0 hR (hslice τ hτI).1 (hslice τ hτI).2 τ t₁
    exact this.trans (by have := hen τ hτI; linarith)
  · rw [setIntegral_const, Real.volume_real_Ioo_of_le hs1.le]
    simp only [smul_eq_mul]
    nlinarith


theorem uf_energy_DU :
    κ * ∫ p in Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R, vecNormSq (DUfun Du X t₁ p) ≤ 162 * l2NormSq f := by
  have hu' := hu
  obtain ⟨hslice, -, hL2, hDL2, hH1, -, -, -⟩ := hu'
  have hBm : MeasurableSet (euclidBall (0 : Vec 2) R) := (pipe_isOpen_euclidBall 0 R).measurableSet
  have hens := (l2NormSq_le_of_weakSolutionOnWith hκ.le (hs1.trans_le ht1) hb hf hu).2 t₁
    ⟨hs1.le, ht1⟩
  have hsub : Set.Ioo s₀ t₁ ×ˢ unitCube ⊆ Set.Ioo s₀ e ×ˢ unitCube :=
    Set.prod_mono (Set.Ioo_subset_Ioo le_rfl ht1) le_rfl
  have hDL2' : ∀ i : Fin 2, MemLp (fun p : ℝ × Vec 2 => Du p.1 p.2 i) 2
      (volume.restrict (Set.Ioo s₀ t₁ ×ˢ unitCube)) := fun i =>
    (hDL2 i).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hH1' : ∀ᵐ t ∂(volume.restrict (Set.Ioo s₀ t₁)), IsPeriodicH1With (u t) (Du t) :=
    ae_restrict_of_ae_restrict_of_subset (Set.Ioo_subset_Ioo le_rfl ht1) hH1
  have hDper : ∀ᵐ t ∂(volume.restrict (Set.Ioo s₀ t₁)), IsZ2Periodic (Du t) :=
    hH1'.mono fun t ht => ht.2.1
  have hw : ∀ j : Fin 2, MemLp (fun p : ℝ × Vec 2 => Du p.1 (X p.1 p.2 t₁) j) 2
      (volume.restrict (Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R)) := fun j =>
    memLp_comp_chart ch hT hs le_rfl R (g := fun t x => Du t x j)
      (hDper.mono fun t ht k x => by simp [ht k x]) (hDL2' j)
  have hDU := DUfun_memLp ch hT hs le_rfl R hDper hDL2'
  have hint : IntegrableOn (fun p => vecNormSq (DUfun Du X t₁ p))
      (Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R) := by
    have := ((hDU 0).integrable_sq).add ((hDU 1).integrable_sq)
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [vecNormSq_two, sq, Pi.add_apply]
  -- the cell side
  have hcell : Integrable (fun p : ℝ × Vec 2 => vecNormSq (Du p.1 p.2))
      (volume.restrict (Set.Ioo s₀ t₁ ×ˢ unitCube)) := by
    have := ((hDL2' 0).integrable_sq).add ((hDL2' 1).integrable_sq)
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [vecNormSq_two, sq, Pi.add_apply]
  have hcell' := hcell
  rw [volume_restrict_prod_eq] at hcell'
  have hcint : IntegrableOn (fun τ => 324 * ∫ x in unitCube, vecNormSq (Du τ x))
      (Set.Ioo s₀ t₁) := (hcell'.integral_prod_left).const_mul 324
  have hmain : ∫ p in Set.Ioo s₀ t₁ ×ˢ euclidBall 0 R, vecNormSq (DUfun Du X t₁ p) ≤
      ∫ τ in Set.Ioo s₀ t₁, 324 * ∫ x in unitCube, vecNormSq (Du τ x) := by
    refine prod_integral_le hint hcint ?_
    have hws : ∀ᵐ τ ∂(volume.restrict (Set.Ioo s₀ t₁)), ∀ j : Fin 2,
        MemLp (fun y => Du τ (X τ y t₁) j) 2 (volume.restrict (euclidBall (0 : Vec 2) R)) := by
      rw [Filter.eventually_all]
      exact fun j => ae_slice_memLp_gen (hw j)
    filter_upwards [hws, hH1', ae_restrict_mem measurableSet_Ioo] with τ hτw hτH hτm
    have hτI : τ ∈ Set.Icc (t₁ - 8 * T) t₁ := ⟨hs.trans hτm.1.le, hτm.2.le⟩
    obtain ⟨hup, hDp, hu2, hDu2, -⟩ := hτH
    have hcp : ∀ j : Fin 2, IsZ2Periodic (fun x => Du τ x j) := fun j k x => by simp [hDp k x]
    have hsq : ∀ j : Fin 2, Integrable (fun y => Du τ (X τ y t₁) j ^ 2)
        (volume.restrict (euclidBall (0 : Vec 2) R)) := fun j => (hτw j).integrable_sq
    have hle1 : ∫ y in euclidBall (0 : Vec 2) R, vecNormSq (DUfun Du X t₁ (τ, y)) ≤
        ∫ y in euclidBall (0 : Vec 2) R,
          4 * (Du τ (X τ y t₁) 0 ^ 2 + Du τ (X τ y t₁) 1 ^ 2) := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => vecNormSq_nonneg _)
        (((hsq 0).add (hsq 1)).const_mul 4) (Filter.Eventually.of_forall fun y => ?_)
      have h1 := (pipeMetric_bounds ch hτI y (DUfun Du X t₁ (τ, y))).1
      have h2 := quad_DUf ch hτI y (Du τ (X τ y t₁))
      have h3 : vecNormSq (DUfun Du X t₁ (τ, y)) ≤ 4 * vecNormSq (Du τ (X τ y t₁)) := by
        have : (1 / 4) * vecNormSq (DUfun Du X t₁ (τ, y)) ≤ vecNormSq (Du τ (X τ y t₁)) := by
          have e : DUfun Du X t₁ (τ, y) = (pipeJac X t₁ (τ, y))ᵀ.mulVec (Du τ (X τ y t₁)) := rfl
          rw [← h2, e]
          rw [e] at h1
          exact h1
        linarith
      simpa [vecNormSq_two, sq] using h3
    have hb0 := ball_sq_le hφ hX hR0 hR (hcp 0) (hDu2 0) τ t₁
    have hb1 := ball_sq_le hφ hX hR0 hR (hcp 1) (hDu2 1) τ t₁
    have hcube : ∫ x in unitCube, vecNormSq (Du τ x) =
        l2NormSq (fun x => Du τ x 0) + l2NormSq (fun x => Du τ x 1) := by
      unfold l2NormSq
      rw [← integral_add (hDu2 0).integrable_sq (hDu2 1).integrable_sq]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp [vecNormSq_two, sq]
    rw [hcube]
    refine hle1.trans ?_
    rw [integral_const_mul, integral_add (hsq 0) (hsq 1)]
    nlinarith
  refine (mul_le_mul_of_nonneg_left hmain hκ.le).trans ?_
  rw [integral_const_mul]
  have e2 : ∫ τ in Set.Ioo s₀ t₁, ∫ x in unitCube, vecNormSq (Du τ x) =
      ∫ p in Set.Ioo s₀ t₁ ×ˢ unitCube, vecNormSq (Du p.1 p.2) := by
    rw [volume_restrict_prod_eq, integral_prod _ hcell']
  rw [e2]
  nlinarith

end Energy

end AVRegularity.Applications.Davies
end
