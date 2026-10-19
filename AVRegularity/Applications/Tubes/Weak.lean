-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import AVRegularity.External.Peano.HalfLine
public import AVRegularity.Applications.Microscopic.RescaleHyp
public import Mathlib.Analysis.Calculus.BumpFunction.Normed

section
@[expose] public section
namespace AVRegularity.Applications

/-! # Real-variable estimates for the final tube bound -/

theorem holder_ratio {s a' r d : ℝ} (hsa : s < a') (hr : 0 < r) (hd : 0 < d)
    (hdr : d ≤ r) : (d / r) ^ a' / d ^ s ≤ r ^ (-s) := by
  have h1 : (d / r) ^ a' = d ^ a' / r ^ a' := Real.div_rpow hd.le hr.le _
  have h2 : d ^ a' = d ^ (a' - s) * d ^ s := by rw [← Real.rpow_add hd]; ring_nf
  have h3 : r ^ a' = r ^ (a' - s) * r ^ s := by rw [← Real.rpow_add hr]; ring_nf
  have h4 : d ^ (a' - s) ≤ r ^ (a' - s) := Real.rpow_le_rpow hd.le hdr (by linarith)
  have hds : 0 < d ^ s := Real.rpow_pos_of_pos hd _
  have hrs : 0 < r ^ s := Real.rpow_pos_of_pos hr _
  have hra : 0 < r ^ (a' - s) := Real.rpow_pos_of_pos hr _
  rw [h1, h2, h3, Real.rpow_neg hr.le]
  have key : d ^ (a' - s) * d ^ s / (r ^ (a' - s) * r ^ s) / d ^ s =
      (d ^ (a' - s) / r ^ (a' - s)) * (r ^ s)⁻¹ := by field_simp
  rw [key]
  calc (d ^ (a' - s) / r ^ (a' - s)) * (r ^ s)⁻¹ ≤ 1 * (r ^ s)⁻¹ :=
        mul_le_mul_of_nonneg_right ((div_le_one hra).2 h4) (inv_nonneg.2 hrs.le)
    _ = (r ^ s)⁻¹ := one_mul _

theorem rpow_neg_one_sub {s r : ℝ} (hr : 0 < r) : r ^ (-1 - s) = r⁻¹ * r ^ (-s) := by
  rw [show -1 - s = -1 + -s by ring, Real.rpow_add hr, Real.rpow_neg_one]

theorem one_le_rpow_neg {s r : ℝ} (hs : 0 < s) (hr : 0 < r) (hr1 : r ≤ 1) : 1 ≤ r ^ (-s) := by
  rw [Real.rpow_neg hr.le]
  exact (one_le_inv₀ (Real.rpow_pos_of_pos hr _)).2 (Real.rpow_le_one hr.le hr1 hs.le)

theorem bound_near {s a' r d M₀ M₁ A X H : ℝ} (hs : 0 < s) (hsa : s < a') (hr : 0 < r)
    (hr1 : r ≤ 1) (hd : 0 < d) (hdr : d ≤ r) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (hA : 0 ≤ A)
    (hX : |X| ≤ M₀ * (r⁻¹ * A)) (hH : H ≤ M₁ * (r⁻¹ * A) * (d / r) ^ a') :
    |X| + H / d ^ s ≤ (M₀ + M₁) * (r ^ (-1 - s) * A) := by
  have hds : 0 < d ^ s := Real.rpow_pos_of_pos hd _
  have hq := holder_ratio hsa hr hd hdr
  have h1 := one_le_rpow_neg hs hr hr1
  rw [rpow_neg_one_sub hr]
  have hrA : 0 ≤ r⁻¹ * A := by positivity
  have h2 : H / d ^ s ≤ M₁ * (r⁻¹ * A) * ((d / r) ^ a' / d ^ s) := by
    rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right hH hds.le
  have h3 : M₁ * (r⁻¹ * A) * ((d / r) ^ a' / d ^ s) ≤ M₁ * (r⁻¹ * A) * r ^ (-s) :=
    mul_le_mul_of_nonneg_left hq (by positivity)
  have h4 : M₀ * (r⁻¹ * A) ≤ M₀ * (r⁻¹ * A) * r ^ (-s) := le_mul_of_one_le_right (by positivity) h1
  nlinarith [h2, h3, h4]

theorem bound_far {s r d M₀ A X Y Z : ℝ} (hs : 0 < s) (hr : 0 < r)
    (hr1 : r ≤ 1) (hd : r / 4 ≤ d) (hM₀ : 0 ≤ M₀) (hA : 0 ≤ A)
    (hX : |X| ≤ M₀ * (r⁻¹ * A)) (hY : |Y| ≤ M₀ * (r⁻¹ * A)) (hZ : |Z| ≤ M₀ * (r⁻¹ * A)) :
    |X| + |Y - Z| / d ^ s ≤ (M₀ + 2 * 4 ^ s * M₀) * (r ^ (-1 - s) * A) := by
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity) hd
  have hds : 0 < d ^ s := Real.rpow_pos_of_pos hd0 _
  have h1 := one_le_rpow_neg hs hr hr1
  rw [rpow_neg_one_sub hr]
  have hrs : (r / 4) ^ s ≤ d ^ s := Real.rpow_le_rpow (by positivity) hd hs.le
  have hrs' : 0 < (r / 4) ^ s := Real.rpow_pos_of_pos (by positivity) _
  have e1 : (r / 4) ^ s = r ^ s / 4 ^ s := Real.div_rpow hr.le (by norm_num) _
  have h4s : 0 < (4 : ℝ) ^ s := Real.rpow_pos_of_pos (by norm_num) _
  have hrneg : r ^ (-s) = (r ^ s)⁻¹ := Real.rpow_neg hr.le _
  have h2 : |Y - Z| / d ^ s ≤ 2 * (M₀ * (r⁻¹ * A)) / (r / 4) ^ s := by
    calc |Y - Z| / d ^ s ≤ |Y - Z| / (r / 4) ^ s :=
          div_le_div_of_nonneg_left (abs_nonneg _) hrs' hrs
      _ ≤ 2 * (M₀ * (r⁻¹ * A)) / (r / 4) ^ s := by
          refine div_le_div_of_nonneg_right ?_ hrs'.le
          linarith [abs_sub Y Z]
  have h3 : 2 * (M₀ * (r⁻¹ * A)) / (r / 4) ^ s = 2 * 4 ^ s * (M₀ * (r⁻¹ * A)) * r ^ (-s) := by
    rw [e1, hrneg]; field_simp
  have h5 : M₀ * (r⁻¹ * A) ≤ M₀ * (r⁻¹ * A) * r ^ (-s) := le_mul_of_one_le_right (by positivity) h1
  have h6 : 0 ≤ 2 * 4 ^ s * (M₀ * (r⁻¹ * A)) := by positivity
  nlinarith [h2, h3, h5, h6]

end AVRegularity.Applications
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization Set Metric
open scoped Convolution
namespace AVRegularity.Applications

/-! # The weak formulation holds for `C¹` compactly supported test functions

The local weak formulation `IsLocalWeakSolution` holds for every continuously differentiable `φ`
with compact support in `O`: a `C¹` test function is approximated, together with its first
derivatives and uniformly, by its mollifications `ρ_ε ⋆ φ ∈ C^∞_c(O)`; since `w`, `Dw` are
integrable on a fixed compact neighbourhood and `b` is bounded, the weak formulation passes to the
limit. -/

/-- The integrand of the local weak formulation `IsLocalWeakSolution`. -/
def localWeakIntegrand (b : ℝ → Vec 2 → Vec 2) (κ : ℝ) (w : ℝ × Vec 2 → ℝ)
    (Dw : ℝ × Vec 2 → Vec 2) (φ : ℝ × Vec 2 → ℝ) (p : ℝ × Vec 2) : ℝ :=
  -(w p * stTimeDeriv φ p) + vecDot (b p.1 p.2) (Dw p) * φ p
    + κ * vecDot (Dw p) (stSpaceGrad φ p)

theorem localWeakIntegrand_eq (b : ℝ → Vec 2 → Vec 2) (κ : ℝ) (w : ℝ × Vec 2 → ℝ)
    (Dw : ℝ × Vec 2 → Vec 2) (φ : ℝ × Vec 2 → ℝ) (p : ℝ × Vec 2) :
    localWeakIntegrand b κ w Dw φ p = -(w p * stTimeDeriv φ p) +
      ∑ i : Fin 2, Dw p i * (b p.1 p.2 i * φ p + κ * stSpaceGrad φ p i) := by
  simp only [localWeakIntegrand, vecDot, Fin.sum_univ_two]
  ring

section Approx

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- Normed bumps of small radius approximate a continuous compactly supported function
uniformly. -/
theorem normed_conv_approx {g : E → ℝ} (hg : Continuous g) (hcs : HasCompactSupport g)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ ρ : ContDiffBump (0 : E), ρ.rOut < δ → ∀ x,
      |(ρ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g) x - g x| ≤ ε := by
  obtain ⟨δ, hδ, hunif⟩ := Metric.uniformContinuous_iff.1
    (hcs.uniformContinuous_of_continuous hg) ε hε
  refine ⟨δ, hδ, fun ρ hρ x => ?_⟩
  have := ρ.dist_normed_convolution_le (μ := μ) (x₀ := x) (ε := ε)
    hg.aestronglyMeasurable (fun y hy => (hunif (by
      have : dist y x < ρ.rOut := hy
      linarith)).le)
  simpa [Real.dist_eq] using this

end Approx

/-- Derivative of a mollification: the derivative falls on `φ`. -/
theorem fderiv_normed_conv_apply {φ : ℝ × Vec 2 → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hcs : HasCompactSupport φ) (ρ : ContDiffBump (0 : ℝ × Vec 2)) (x v : ℝ × Vec 2) :
    fderiv ℝ (ρ.normed (volume : Measure (ℝ × Vec 2)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] φ)
        x v =
      (ρ.normed (volume : Measure (ℝ × Vec 2)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        fun a => fderiv ℝ φ a v) x := by
  have hρ : Continuous (ρ.normed (volume : Measure (ℝ × Vec 2))) := ρ.continuous_normed
  have hli := hρ.locallyIntegrable (μ := (volume : Measure (ℝ × Vec 2)))
  have h := hcs.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hli hφ x
  rw [h.fderiv, convolution_precompR_apply _ hli
    (hcs.fderiv (𝕜 := ℝ)) (hφ.continuous_fderiv one_ne_zero)]

theorem continuous_fderiv_apply_of_c1 {φ : ℝ × Vec 2 → ℝ} (hφ : ContDiff ℝ 1 φ)
    (v : ℝ × Vec 2) : Continuous fun a => fderiv ℝ φ a v :=
  (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- A `C¹` compactly supported function is approximated by `C^∞_c` functions, uniformly together
with its first derivatives, with supports in any prescribed neighbourhood of its support. -/
theorem exists_smooth_approx {φ : ℝ × Vec 2 → ℝ} (hφ : ContDiff ℝ 1 φ) (hcs : HasCompactSupport φ)
    {δ₀ ε : ℝ} (hδ₀ : 0 < δ₀) (hε : 0 < ε) :
    ∃ ψ : ℝ × Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ cthickening δ₀ (tsupport φ) ∧ (∀ x, |ψ x - φ x| ≤ ε) ∧
      (∀ x, |stTimeDeriv ψ x - stTimeDeriv φ x| ≤ ε) ∧
      ∀ x i, |stSpaceGrad ψ x i - stSpaceGrad φ x i| ≤ ε := by
  have hvol : ∀ v : ℝ × Vec 2, ∃ δ > 0, ∀ ρ : ContDiffBump (0 : ℝ × Vec 2), ρ.rOut < δ → ∀ x,
      |(ρ.normed (volume : Measure (ℝ × Vec 2)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        fun a => fderiv ℝ φ a v) x - fderiv ℝ φ x v| ≤ ε := fun v =>
    normed_conv_approx (continuous_fderiv_apply_of_c1 hφ v)
      (hasCompactSupport_fderiv_apply hcs v) hε
  obtain ⟨δ0, hδ0, h0⟩ := normed_conv_approx (μ := (volume : Measure (ℝ × Vec 2)))
    hφ.continuous hcs hε
  obtain ⟨δ1, hδ1, h1⟩ := hvol (1, 0)
  obtain ⟨δ2, hδ2, h2⟩ := hvol (0, basisVec 0)
  obtain ⟨δ3, hδ3, h3⟩ := hvol (0, basisVec 1)
  set δ := min (min δ0 δ1) (min δ2 δ3) with hδdef
  have hδpos : 0 < δ := lt_min (lt_min hδ0 hδ1) (lt_min hδ2 hδ3)
  set ρ0 : ℝ := min δ δ₀ / 2 with hρ0
  have hρ0pos : 0 < ρ0 := by positivity
  let ρ : ContDiffBump (0 : ℝ × Vec 2) :=
    { rIn := ρ0 / 2, rOut := ρ0, rIn_pos := by positivity, rIn_lt_rOut := by linarith }
  have hρδ : ρ.rOut < δ := by
    show ρ0 < δ
    have : min δ δ₀ ≤ δ := min_le_left _ _
    linarith
  have hρδ₀ : ρ.rOut ≤ δ₀ := by
    show ρ0 ≤ δ₀
    have : min δ δ₀ ≤ δ₀ := min_le_right _ _
    linarith
  have hli : LocallyIntegrable (ρ.normed (volume : Measure (ℝ × Vec 2))) volume :=
    (ρ.continuous_normed (μ := (volume : Measure (ℝ × Vec 2)))).locallyIntegrable
  refine ⟨ρ.normed (volume : Measure (ℝ × Vec 2)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] φ,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (ρ.hasCompactSupport_normed (μ := (volume : Measure (ℝ × Vec 2)))).contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (ρ.contDiff_normed (μ := (volume : Measure (ℝ × Vec 2)))
        (n := (⊤ : ℕ∞)))
      (hφ.continuous.locallyIntegrable)
  · exact (ρ.hasCompactSupport_normed (μ := (volume : Measure (ℝ × Vec 2)))).convolution
      (ContinuousLinearMap.lsmul ℝ ℝ) hcs
  · have hsupp : Function.support
        (ρ.normed (volume : Measure (ℝ × Vec 2)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] φ) ⊆
          cthickening δ₀ (tsupport φ) := by
      intro x hx
      have := support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) hx
      obtain ⟨a, ha, y, hy, rfl⟩ := this
      rw [ρ.support_normed_eq] at ha
      refine mem_cthickening_of_dist_le (a + y) y δ₀ _ (subset_tsupport φ hy) ?_
      have : dist a 0 < ρ.rOut := ha
      rw [dist_zero_right] at this
      rw [dist_add_self_left]
      linarith
    exact closure_minimal hsupp isClosed_cthickening
  · intro x
    exact h0 ρ (lt_of_lt_of_le hρδ ((min_le_left _ _).trans (min_le_left _ _))) x
  · intro x
    unfold stTimeDeriv
    rw [fderiv_normed_conv_apply hφ hcs]
    exact h1 ρ (lt_of_lt_of_le hρδ ((min_le_left _ _).trans (min_le_right _ _))) x
  · intro x i
    unfold stSpaceGrad
    rw [fderiv_normed_conv_apply hφ hcs]
    fin_cases i
    · exact h2 ρ (lt_of_lt_of_le hρδ ((min_le_right _ _).trans (min_le_left _ _))) x
    · exact h3 ρ (lt_of_lt_of_le hρδ ((min_le_right _ _).trans (min_le_right _ _))) x

section Main

variable {b : ℝ → Vec 2 → Vec 2} {κ : ℝ} {w : ℝ × Vec 2 → ℝ} {Dw : ℝ × Vec 2 → Vec 2}

theorem abs_apply_le_of_norm_le {v : Vec 2} {B : ℝ} (h : ‖v‖ ≤ B) (i : Fin 2) : |v i| ≤ B :=
  (norm_le_pi_norm v i).trans h

theorem integrableOn_localWeakIntegrand {P : Set (ℝ × Vec 2)} (hwI : IntegrableOn w P)
    (hDI : ∀ i : Fin 2, IntegrableOn (fun p => Dw p i) P)
    (hbc : Continuous fun p : ℝ × Vec 2 => b p.1 p.2) {B : ℝ} (hB : ∀ r y, ‖b r y‖ ≤ B)
    {θ : ℝ × Vec 2 → ℝ} (hθ : ContDiff ℝ 1 θ) (hcs : HasCompactSupport θ) :
    IntegrableOn (localWeakIntegrand b κ w Dw θ) P := by
  have hT := continuous_fderiv_apply_of_c1 hθ (1, 0)
  obtain ⟨CT, hCT⟩ := hT.bounded_above_of_compact_support (hasCompactSupport_fderiv_apply hcs _)
  obtain ⟨Cθ, hCθ⟩ := hθ.continuous.bounded_above_of_compact_support hcs
  have hG : ∀ i : Fin 2, ∃ C, ∀ p, ‖b p.1 p.2 i * θ p + κ * stSpaceGrad θ p i‖ ≤ C := by
    intro i
    obtain ⟨Ci, hCi⟩ := (continuous_fderiv_apply_of_c1 hθ (0, basisVec i)).bounded_above_of_compact_support
      (hasCompactSupport_fderiv_apply hcs _)
    refine ⟨B * Cθ + |κ| * Ci, fun p => ?_⟩
    calc ‖b p.1 p.2 i * θ p + κ * stSpaceGrad θ p i‖
        ≤ ‖b p.1 p.2 i * θ p‖ + ‖κ * stSpaceGrad θ p i‖ := norm_add_le _ _
      _ ≤ B * Cθ + |κ| * Ci := by
        rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        have hbi := abs_apply_le_of_norm_le (hB p.1 p.2) i
        refine add_le_add (mul_le_mul hbi (hCθ p)
          (abs_nonneg _) ((abs_nonneg _).trans hbi)) ?_
        exact mul_le_mul_of_nonneg_left (hCi p) (abs_nonneg _)
  have hmeas : ∀ i : Fin 2, AEStronglyMeasurable (fun p => b p.1 p.2 i * θ p +
      κ * stSpaceGrad θ p i) (volume.restrict P) := by
    intro i
    have h1 : Continuous fun p : ℝ × Vec 2 => b p.1 p.2 i := (continuous_apply i).comp hbc
    have h2 : Continuous fun p : ℝ × Vec 2 => stSpaceGrad θ p i :=
      continuous_fderiv_apply_of_c1 hθ (0, basisVec i)
    exact ((h1.mul hθ.continuous).add (continuous_const.mul h2)).aestronglyMeasurable
  have hterm0 : Integrable (fun p => w p * stTimeDeriv θ p) (volume.restrict P) :=
    hwI.mul_bdd hT.aestronglyMeasurable (Filter.Eventually.of_forall hCT)
  have hterm : ∀ i : Fin 2, Integrable (fun p => Dw p i * (b p.1 p.2 i * θ p +
      κ * stSpaceGrad θ p i)) (volume.restrict P) := fun i =>
    (hDI i).mul_bdd (hmeas i) (Filter.Eventually.of_forall (hG i).choose_spec)
  have : localWeakIntegrand b κ w Dw θ = fun p => -(w p * stTimeDeriv θ p) +
      ∑ i : Fin 2, Dw p i * (b p.1 p.2 i * θ p + κ * stSpaceGrad θ p i) :=
    funext (localWeakIntegrand_eq b κ w Dw θ)
  rw [IntegrableOn, this]
  exact hterm0.neg.add (integrable_finsetSum _ fun i _ => hterm i)

theorem localWeakIntegrand_eq_zero_of_notMem {θ : ℝ × Vec 2 → ℝ} {p : ℝ × Vec 2}
    (hp : p ∉ tsupport θ) : localWeakIntegrand b κ w Dw θ p = 0 := by
  have hfd : fderiv ℝ θ p = 0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hp
  have hval : θ p = 0 := image_eq_zero_of_notMem_tsupport hp
  have hgrad : stSpaceGrad θ p = 0 := by
    funext i; simp [stSpaceGrad, hfd]
  simp [localWeakIntegrand, stTimeDeriv, hfd, hval, hgrad, vecDot]

theorem setIntegral_localWeakIntegrand_eq {O P : Set (ℝ × Vec 2)} (hO : MeasurableSet O)
    (hPO : P ⊆ O) {θ : ℝ × Vec 2 → ℝ} (hts : tsupport θ ⊆ P) :
    ∫ p in O, localWeakIntegrand b κ w Dw θ p = ∫ p in P, localWeakIntegrand b κ w Dw θ p :=
  setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hO hPO fun _ hp =>
    localWeakIntegrand_eq_zero_of_notMem fun h => hp.2 (hts h)

/-- The local weak formulation `IsLocalWeakSolution` holds for `C¹` test functions with compact
support in `O`. -/
theorem weak_form_C1 {O : Set (ℝ × Vec 2)} (hO : IsOpen O)
    (hw : IsLocalWeakSolution b κ O w Dw)
    (hbc : Continuous fun p : ℝ × Vec 2 => b p.1 p.2) {B : ℝ} (hB : ∀ r y, ‖b r y‖ ≤ B)
    {φ : ℝ × Vec 2 → ℝ} (hφ : ContDiff ℝ 1 φ) (hcs : HasCompactSupport φ)
    (hts : tsupport φ ⊆ O) :
    ∫ p in O, localWeakIntegrand b κ w Dw φ p = 0 := by
  obtain ⟨δ₀, hδ₀, hPO⟩ := hcs.isCompact.exists_cthickening_subset_open hO hts
  set P : Set (ℝ × Vec 2) := cthickening δ₀ (tsupport φ) with hP
  have hPc : IsCompact P := hcs.isCompact.cthickening
  have : IsFiniteMeasure (volume.restrict P) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hPc.measure_lt_top⟩
  have hwI : IntegrableOn w P := (hw.1 P hPO hPc).integrable one_le_two
  have hDI : ∀ i : Fin 2, IntegrableOn (fun p => Dw p i) P := fun i =>
    ((hw.2.1 P hPO hPc i).integrable one_le_two)
  have hφP : tsupport φ ⊆ P := self_subset_cthickening _
  rw [setIntegral_localWeakIntegrand_eq hO.measurableSet hPO hφP]
  set M : ℝ := ∫ p in P, (|w p| + (B + |κ|) * (|Dw p 0| + |Dw p 1|)) with hM
  have hGint : IntegrableOn (fun p => |w p| + (B + |κ|) * (|Dw p 0| + |Dw p 1|)) P :=
    hwI.abs.add (((hDI 0).abs.add (hDI 1).abs).const_mul _)
  have hMnn : 0 ≤ M := setIntegral_nonneg hPc.measurableSet fun p _ => by
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 0)
    positivity
  have hkey : ∀ ε : ℝ, 0 < ε → |∫ p in P, localWeakIntegrand b κ w Dw φ p| ≤ ε * M := by
    intro ε hε
    obtain ⟨ψ, hψ, hψcs, hψts, hψ0, hψt, hψx⟩ := exists_smooth_approx hφ hcs hδ₀ hε
    have hψO : tsupport ψ ⊆ O := hψts.trans hPO
    have hzero : ∫ p in P, localWeakIntegrand b κ w Dw ψ p = 0 := by
      rw [← setIntegral_localWeakIntegrand_eq hO.measurableSet hPO hψts]
      exact hw.2.2.2 ψ ⟨hψ, hψcs, hψO⟩
    have hψc1 : ContDiff ℝ 1 ψ := hψ.of_le (by exact_mod_cast le_top)
    have hIφ := integrableOn_localWeakIntegrand (κ := κ) hwI hDI hbc hB hφ hcs
    have hIψ := integrableOn_localWeakIntegrand (κ := κ) hwI hDI hbc hB hψc1 hψcs
    have hsub : ∫ p in P, localWeakIntegrand b κ w Dw φ p =
        ∫ p in P, (localWeakIntegrand b κ w Dw φ p - localWeakIntegrand b κ w Dw ψ p) := by
      rw [integral_sub hIφ hIψ, hzero, sub_zero]
    rw [hsub]
    have hbound : ∀ p, ‖localWeakIntegrand b κ w Dw φ p - localWeakIntegrand b κ w Dw ψ p‖ ≤
        ε * (|w p| + (B + |κ|) * (|Dw p 0| + |Dw p 1|)) := by
      intro p
      rw [localWeakIntegrand_eq, localWeakIntegrand_eq, Real.norm_eq_abs]
      simp only [Fin.sum_univ_two]
      have e1 := hψt p
      have e0 := hψ0 p
      have ex0 := hψx p 0
      have ex1 := hψx p 1
      have hb0 := abs_apply_le_of_norm_le (hB p.1 p.2) 0
      have hb1 := abs_apply_le_of_norm_le (hB p.1 p.2) 1
      set a0 := stTimeDeriv ψ p - stTimeDeriv φ p
      set c := ψ p - φ p
      set d0 := stSpaceGrad ψ p 0 - stSpaceGrad φ p 0
      set d1 := stSpaceGrad ψ p 1 - stSpaceGrad φ p 1
      have hid : -(w p * stTimeDeriv φ p) + (Dw p 0 * (b p.1 p.2 0 * φ p + κ * stSpaceGrad φ p 0)
          + Dw p 1 * (b p.1 p.2 1 * φ p + κ * stSpaceGrad φ p 1)) -
          (-(w p * stTimeDeriv ψ p) + (Dw p 0 * (b p.1 p.2 0 * ψ p + κ * stSpaceGrad ψ p 0)
          + Dw p 1 * (b p.1 p.2 1 * ψ p + κ * stSpaceGrad ψ p 1))) =
          w p * a0 - Dw p 0 * (b p.1 p.2 0 * c + κ * d0)
            - Dw p 1 * (b p.1 p.2 1 * c + κ * d1) := by
        simp only [a0, c, d0, d1]; ring
      rw [hid]
      have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 0)
      have t1 : |w p * a0| ≤ |w p| * ε := by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left e1 (abs_nonneg _)
      have t2 : ∀ (q : ℝ) (bi di : ℝ), |bi| ≤ B → |di| ≤ ε → |c| ≤ ε →
          |q * (bi * c + κ * di)| ≤ |q| * ((B + |κ|) * ε) := by
        intro q bi di hbi hdi hc
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        calc |bi * c + κ * di| ≤ |bi * c| + |κ * di| := abs_add_le _ _
          _ ≤ B * ε + |κ| * ε := by
            rw [abs_mul, abs_mul]
            exact add_le_add (mul_le_mul hbi hc (abs_nonneg _) hB0)
              (mul_le_mul_of_nonneg_left hdi (abs_nonneg _))
          _ = (B + |κ|) * ε := by ring
      have u0 := t2 (Dw p 0) _ _ hb0 ex0 e0
      have u1 := t2 (Dw p 1) _ _ hb1 ex1 e0
      calc |w p * a0 - Dw p 0 * (b p.1 p.2 0 * c + κ * d0)
            - Dw p 1 * (b p.1 p.2 1 * c + κ * d1)|
          ≤ |w p * a0| + |Dw p 0 * (b p.1 p.2 0 * c + κ * d0)|
            + |Dw p 1 * (b p.1 p.2 1 * c + κ * d1)| := by
            have := abs_sub (w p * a0 - Dw p 0 * (b p.1 p.2 0 * c + κ * d0))
              (Dw p 1 * (b p.1 p.2 1 * c + κ * d1))
            have h2 := abs_sub (w p * a0) (Dw p 0 * (b p.1 p.2 0 * c + κ * d0))
            linarith
        _ ≤ ε * (|w p| + (B + |κ|) * (|Dw p 0| + |Dw p 1|)) := by nlinarith [t1, u0, u1]
    calc |∫ p in P, (localWeakIntegrand b κ w Dw φ p - localWeakIntegrand b κ w Dw ψ p)|
        = ‖∫ p in P, (localWeakIntegrand b κ w Dw φ p - localWeakIntegrand b κ w Dw ψ p)‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ∫ p in P, ε * (|w p| + (B + |κ|) * (|Dw p 0| + |Dw p 1|)) :=
          norm_integral_le_of_norm_le (hGint.const_mul ε) (Filter.Eventually.of_forall hbound)
      _ = ε * M := by rw [integral_const_mul]
  by_contra hne
  have hpos : 0 < |∫ p in P, localWeakIntegrand b κ w Dw φ p| := abs_pos.2 hne
  set I := |∫ p in P, localWeakIntegrand b κ w Dw φ p|
  have h := hkey (I / (M + 1)) (by positivity)
  have h2 : I / (M + 1) * M < I := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

end Main

end AVRegularity.Applications
end
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.Applications

/-! # The tube map `Θ` and its change of variables

For a continuous curve `Y : ℝ → ℝ²`, `t : ℝ`, `c > 0` (the duration `r²/κ`) and `r > 0`,
`tubeMap Y t c r (τ, y) = (t + c τ, Y (t + c τ) + r y)` is the composition of the affine map
`(τ, y) ↦ (t + c τ, r y)` with the shear `(s, x) ↦ (s, x + Y s)`. The shear preserves Lebesgue
measure (Fubini and translation invariance on each time slice).
-/

/-- The shear `(s, x) ↦ (s, Y s + x)`. -/
def shearMap (Y : ℝ → Vec 2) (q : ℝ × Vec 2) : ℝ × Vec 2 := (q.1, Y q.1 + q.2)

/-- The affine map `(τ, y) ↦ (t + c τ, r y)`. -/
def tubeAff (t c r : ℝ) (p : ℝ × Vec 2) : ℝ × Vec 2 := (t + c * p.1, r • p.2)

/-- The tube map `Θ(τ, y) = (t + c τ, Y (t + c τ) + r y)`. -/
def tubeMap (Y : ℝ → Vec 2) (t c r : ℝ) (p : ℝ × Vec 2) : ℝ × Vec 2 :=
  (t + c * p.1, Y (t + c * p.1) + r • p.2)

/-- The inverse of the tube map. -/
def tubeInv (Y : ℝ → Vec 2) (t c r : ℝ) (q : ℝ × Vec 2) : ℝ × Vec 2 :=
  ((q.1 - t) / c, r⁻¹ • (q.2 - Y q.1))

theorem tubeMap_eq (Y : ℝ → Vec 2) (t c r : ℝ) :
    tubeMap Y t c r = shearMap Y ∘ tubeAff t c r := by
  funext p
  simp only [tubeMap, shearMap, tubeAff, Function.comp_apply]

section Basic

variable {Y : ℝ → Vec 2} {t c r : ℝ}

theorem tubeInv_tubeMap (hc : c ≠ 0) (hr : r ≠ 0) (p : ℝ × Vec 2) :
    tubeInv Y t c r (tubeMap Y t c r p) = p := by
  rcases p with ⟨τ, y⟩
  simp only [tubeInv, tubeMap, add_sub_cancel_left, add_sub_cancel_left, smul_smul,
    inv_mul_cancel₀ hr, one_smul, Prod.mk.injEq, and_true]
  field_simp

theorem tubeMap_tubeInv (hc : c ≠ 0) (hr : r ≠ 0) (q : ℝ × Vec 2) :
    tubeMap Y t c r (tubeInv Y t c r q) = q := by
  rcases q with ⟨s, x⟩
  simp only [tubeMap, tubeInv, smul_smul, mul_inv_cancel₀ hr, one_smul]
  have h1 : t + c * ((s - t) / c) = s := by field_simp; ring
  rw [h1]
  simp

theorem measurable_tubeMap (hY : Measurable Y) : Measurable (tubeMap Y t c r) := by
  unfold tubeMap
  fun_prop

theorem measurable_tubeInv (hY : Measurable Y) : Measurable (tubeInv Y t c r) := by
  unfold tubeInv
  fun_prop

theorem continuous_tubeMap (hY : Continuous Y) : Continuous (tubeMap Y t c r) := by
  unfold tubeMap
  fun_prop

theorem continuous_tubeInv (hY : Continuous Y) : Continuous (tubeInv Y t c r) := by
  unfold tubeInv
  fun_prop

/-- `tubeMap` as a measurable equivalence. -/
def tubeEquiv (hY : Measurable Y) (hc : c ≠ 0) (hr : r ≠ 0) :
    (ℝ × Vec 2) ≃ᵐ (ℝ × Vec 2) where
  toFun := tubeMap Y t c r
  invFun := tubeInv Y t c r
  left_inv := tubeInv_tubeMap hc hr
  right_inv := tubeMap_tubeInv hc hr
  measurable_toFun := measurable_tubeMap hY
  measurable_invFun := measurable_tubeInv hY

theorem measurableEmbedding_tubeMap (hY : Measurable Y) (hc : c ≠ 0) (hr : r ≠ 0) :
    MeasurableEmbedding (tubeMap Y t c r) :=
  (tubeEquiv (t := t) hY hc hr).measurableEmbedding

/-- The shear preserves Lebesgue measure on space-time. -/
theorem measurePreserving_shearMap (hY : Measurable Y) :
    MeasurePreserving (shearMap Y) (volume : Measure (ℝ × Vec 2)) volume := by
  have h := MeasurePreserving.skew_product (μa := (volume : Measure ℝ)) (μb := volume)
    (μc := (volume : Measure (Vec 2))) (μd := volume) (f := fun a : ℝ => a)
    (g := fun a y => Y a + y) (MeasurePreserving.id _)
    (by fun_prop) (Filter.Eventually.of_forall fun a => map_add_left_eq_self _ _)
  rw [Measure.volume_eq_prod]
  exact h

theorem map_tubeAff_volume (hc : 0 < c) (hr : r ≠ 0) :
    Measure.map (tubeAff t c r) (volume : Measure (ℝ × Vec 2)) =
      ENNReal.ofReal (c⁻¹ * (r ^ 2)⁻¹) • volume := by
  rw [Measure.volume_eq_prod ℝ (Vec 2)]
  change Measure.map (Prod.map (fun τ : ℝ => t + c * τ) (fun y : Vec 2 => r • y))
    (volume.prod volume) = _
  rw [← Measure.map_prod_map volume volume (by fun_prop) (by fun_prop)]
  have h1 := map_time_affine_volume t c hc.ne'
  have h2 : Measure.map (fun y : Vec 2 => r • y) (volume : Measure (Vec 2)) =
      ENNReal.ofReal |(r ^ 2)⁻¹| • volume := by
    rw [Measure.map_addHaar_smul volume hr, Module.finrank_fin_fun]
  rw [h1, h2, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 2
  rw [abs_of_nonneg (inv_nonneg.2 (sq_nonneg r)), abs_of_pos (inv_pos.mpr hc)]

theorem measurable_shearMap (hY : Measurable Y) : Measurable (shearMap Y) :=
  (measurePreserving_shearMap hY).measurable

theorem measurable_tubeAff : Measurable (tubeAff t c r) := by
  unfold tubeAff
  fun_prop

/-- Lebesgue measure scales by `c r²` under the tube map. -/
theorem map_tubeMap_volume (hY : Measurable Y) (hc : 0 < c) (hr : r ≠ 0) :
    Measure.map (tubeMap Y t c r) (volume : Measure (ℝ × Vec 2)) =
      ENNReal.ofReal (c⁻¹ * (r ^ 2)⁻¹) • volume := by
  rw [tubeMap_eq, ← Measure.map_map (measurable_shearMap hY) measurable_tubeAff,
    map_tubeAff_volume hc hr, Measure.map_smul _ _,
    (measurePreserving_shearMap hY).map_eq]
  · exact (measurable_shearMap hY).aemeasurable

theorem map_tubeMap_restrict (hY : Measurable Y) (hc : 0 < c) (hr : r ≠ 0)
    (S : Set (ℝ × Vec 2)) :
    Measure.map (tubeMap Y t c r) (volume.restrict S) =
      ENNReal.ofReal (c⁻¹ * (r ^ 2)⁻¹) • volume.restrict (tubeMap Y t c r '' S) := by
  have hemb := measurableEmbedding_tubeMap (t := t) hY hc.ne' hr
  rw [← Measure.restrict_smul, ← map_tubeMap_volume hY hc hr, hemb.restrict_map,
    Set.preimage_image_eq _ hemb.injective]

/-- Change of variables for the tube map. -/
theorem integral_tubeMap (hY : Measurable Y) (hc : 0 < c) (hr : r ≠ 0) (f : ℝ × Vec 2 → ℝ)
    (S : Set (ℝ × Vec 2)) :
    ∫ p in S, f (tubeMap Y t c r p) = (c * r ^ 2)⁻¹ * ∫ q in tubeMap Y t c r '' S, f q := by
  have hemb := measurableEmbedding_tubeMap (t := t) hY hc.ne' hr
  have h1 : ∫ p in S, f (tubeMap Y t c r p) =
      ∫ q, f q ∂(Measure.map (tubeMap Y t c r) (volume.restrict S)) :=
    (hemb.integral_map f).symm
  rw [h1, map_tubeMap_restrict hY hc hr, integral_smul_measure]
  have hpos : 0 ≤ c⁻¹ * (r ^ 2)⁻¹ := by positivity
  rw [ENNReal.toReal_ofReal hpos, smul_eq_mul, mul_inv]

theorem measurableSet_image_tubeMap (hY : Measurable Y) (hc : 0 < c) (hr : r ≠ 0)
    {S : Set (ℝ × Vec 2)} (hS : MeasurableSet S) : MeasurableSet (tubeMap Y t c r '' S) :=
  (measurableEmbedding_tubeMap (t := t) hY hc.ne' hr).measurableSet_image.2 hS

end Basic

end AVRegularity.Applications
end
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization Set
namespace AVRegularity.Applications

/-! # Trajectories and the geometry of tubes

* `exists_c1_trajectory`: a backward Peano trajectory ending at `(t, x)` extends, by its
  tangent line, to a `C¹` curve `Y : ℝ → ℝ²` with `Ẏ(s) = b(min s t, Y(min s t))`.
* `isCompact_closedTube`: closed translating tubes along a continuous curve are compact.
* `tubeMap_mem_closedTube`: `Θ(Q₁)` lies in the closed tube. -/

section
section Trajectory

variable {b : ℝ → Vec 2 → Vec 2}

/-- A `C¹` curve with `Ẏ(s) = b(s, Y(s))` for `s ≤ t`, `Y(t) = x`, continued by the tangent line. -/
theorem exists_c1_trajectory (hbc : Continuous (fun p : ℝ × Vec 2 => b p.1 p.2))
    (hbd : ∃ B : ℝ, 0 ≤ B ∧ ∀ r y, ‖b r y‖ ≤ B) (t : ℝ) (x : Vec 2) :
    ∃ Y : ℝ → Vec 2, ContDiff ℝ 1 Y ∧ Y t = x ∧
      ∀ s, HasDerivAt Y (b (min s t) (Y (min s t))) s := by
  obtain ⟨X, hX0, hX⟩ := External.exists_peanoBackwardTrajectory b hbc hbd t x
  set v0 : Vec 2 := b t x with hv0
  let Y : ℝ → Vec 2 := fun s => if s ≤ t then X s else x + (s - t) • v0
  have hYle : ∀ s, s ≤ t → Y s = X s := fun s hs => by simp [Y, hs]
  have hYgt : ∀ s, t < s → Y s = x + (s - t) • v0 := fun s hs => by
    simp [Y, not_le.2 hs]
  have hYt : Y t = x := by rw [hYle t le_rfl, hX0]
  have hderiv : ∀ s, HasDerivAt Y (b (min s t) (Y (min s t))) s := by
    intro s
    rcases lt_trichotomy s t with hst | hst | hst
    · have hX' : HasDerivAt X (b s (X s)) s :=
        (hX s hst.le).hasDerivAt (Iic_mem_nhds hst)
      have heq : X =ᶠ[nhds s] Y := by
        filter_upwards [Iio_mem_nhds hst] with y hy
        exact (hYle y (le_of_lt hy)).symm
      rw [min_eq_left hst.le, hYle s hst.le]
      exact hX'.congr_of_eventuallyEq heq.symm
    · subst hst
      rw [min_self, hYt]
      have hleft : HasDerivWithinAt Y (b s x) (Iic s) s := by
        have := hX s le_rfl
        rw [hX0] at this
        exact this.congr (fun y hy => hYle y hy) (hYle s le_rfl)
      have hright : HasDerivWithinAt Y (b s x) (Ici s) s := by
        have haff : HasDerivAt (fun y : ℝ => x + (y - s) • v0) v0 s := by
          have h1 : HasDerivAt (fun y : ℝ => y - s) 1 s := (hasDerivAt_id s).sub_const s
          simpa using (h1.smul_const v0).const_add x
        refine haff.hasDerivWithinAt.congr (fun y hy => ?_) ?_
        · rcases eq_or_lt_of_le (show s ≤ y from hy) with h | h
          · subst h
            simp [hYt]
          · exact hYgt y h
        · simp [hYt]
      have := hleft.union hright
      rw [Iic_union_Ici] at this
      exact hasDerivWithinAt_univ.1 this
    · have haff : HasDerivAt (fun y : ℝ => x + (y - t) • v0) v0 s := by
        have h1 : HasDerivAt (fun y : ℝ => y - t) 1 s := (hasDerivAt_id s).sub_const t
        simpa using (h1.smul_const v0).const_add x
      have heq : (fun y : ℝ => x + (y - t) • v0) =ᶠ[nhds s] Y := by
        filter_upwards [Ioi_mem_nhds hst] with y hy
        exact (hYgt y hy).symm
      rw [min_eq_right hst.le, hYt]
      exact haff.congr_of_eventuallyEq heq.symm
  refine ⟨Y, ?_, hYt, hderiv⟩
  rw [contDiff_one_iff_deriv]
  have hdiff : Differentiable ℝ Y := fun s => (hderiv s).differentiableAt
  have hderEq : deriv Y = fun s => b (min s t) (Y (min s t)) := funext fun s => (hderiv s).deriv
  refine ⟨hdiff, ?_⟩
  rw [hderEq]
  have hYc : Continuous Y := hdiff.continuous
  have hmin : Continuous fun s : ℝ => min s t := continuous_id.min continuous_const
  exact hbc.comp (hmin.prodMk (hYc.comp hmin))

/-- The `C¹` trajectory is a backward trajectory in the sense of `IsBackwardTrajectory`. -/
theorem isBackwardTrajectory_of_hasDerivAt {Y : ℝ → Vec 2} {t h : ℝ}
    (hY : ∀ s, HasDerivAt Y (b (min s t) (Y (min s t))) s) : IsBackwardTrajectory b Y t h := by
  intro τ hτ
  have := (hY τ).hasDerivWithinAt (s := Icc (t - h) t)
  rwa [min_eq_left hτ.2] at this

end Trajectory

section Tube

theorem norm_le_of_vecNormSq_le {v : Vec 2} {r : ℝ} (hr : 0 ≤ r) (h : vecNormSq v ≤ r ^ 2) :
    ‖v‖ ≤ r := by
  rw [pi_norm_le_iff_of_nonneg hr]
  intro i
  rw [Real.norm_eq_abs]
  have h1 := sq_apply_le_vecNormSq v i
  exact abs_le_of_sq_le_sq' (h1.trans h) hr |> fun h => abs_le.2 h

theorem isCompact_closedTube {Y : ℝ → Vec 2} (hY : Continuous Y) (t r κ : ℝ) :
    IsCompact (closedTube Y t r κ) := by
  have hcl : IsClosed (closedTube Y t r κ) := by
    have h1 : IsClosed {p : ℝ × Vec 2 | p.1 ∈ Icc (t - r ^ 2 / κ) t} :=
      isClosed_Icc.preimage continuous_fst
    have hc : Continuous fun p : ℝ × Vec 2 => vecNormSq (p.2 - Y p.1) := by
      unfold vecNormSq vecDot
      have : Continuous fun p : ℝ × Vec 2 => p.2 - Y p.1 :=
        continuous_snd.sub (hY.comp continuous_fst)
      fun_prop
    exact h1.inter (isClosed_le hc continuous_const)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := t - r ^ 2 / κ) (b := t)).exists_bound_of_continuousOn
    hY.continuousOn
  refine IsCompact.of_isClosed_subset
    ((isCompact_Icc (a := t - r ^ 2 / κ) (b := t)).prod (isCompact_closedBall (0 : Vec 2) (M + |r|))) hcl ?_
  rintro ⟨s, y⟩ ⟨hs, hy⟩
  refine ⟨hs, ?_⟩
  simp only [Metric.mem_closedBall, dist_zero_right]
  have h1 : ‖y - Y s‖ ≤ |r| :=
    norm_le_of_vecNormSq_le (abs_nonneg r) (by rwa [sq_abs])
  calc ‖y‖ = ‖(y - Y s) + Y s‖ := by rw [sub_add_cancel]
    _ ≤ ‖y - Y s‖ + ‖Y s‖ := norm_add_le _ _
    _ ≤ |r| + M := add_le_add h1 (hM s hs)
    _ = M + |r| := add_comm _ _

theorem mem_openCyl_zero_one_iff {p : ℝ × Vec 2} :
    p ∈ openCyl 0 1 ↔ p.1 ∈ Ioo (-1 : ℝ) 0 ∧ vecNormSq p.2 < 1 := by
  simp [openCyl, euclidBall]

/-- `Θ(Q₁)` lies in the closed tube. -/
theorem tubeMap_mem_closedTube {Y : ℝ → Vec 2} {t r κ : ℝ} (hr : 0 < r) (hκ : 0 < κ)
    {p : ℝ × Vec 2} (hp : p ∈ openCyl 0 1) :
    tubeMap Y t (r ^ 2 / κ) r p ∈ closedTube Y t r κ := by
  rw [mem_openCyl_zero_one_iff] at hp
  obtain ⟨⟨h1, h2⟩, h3⟩ := hp
  have hc : 0 < r ^ 2 / κ := by positivity
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [tubeMap]
    nlinarith
  · simp only [tubeMap]
    nlinarith
  · simp only [tubeMap, add_sub_cancel_left]
    rw [vecNormSq_smul]
    nlinarith [sq_nonneg r]

theorem tubeMap_image_subset_closedTube {Y : ℝ → Vec 2} {t r κ : ℝ} (hr : 0 < r)
    (hκ : 0 < κ) : tubeMap Y t (r ^ 2 / κ) r '' openCyl 0 1 ⊆ closedTube Y t r κ := by
  rintro _ ⟨p, hp, rfl⟩
  exact tubeMap_mem_closedTube hr hκ hp

end Tube
end

/-! # The pulled-back test function

For `φ̃ ∈ C^∞_c(Q₁)`, `φ = φ̃ ∘ Θ⁻¹` is `C¹` with compact support in `Θ(Q₁)` and
`∂ₜφ ∘ Θ = c⁻¹ ∂τφ̃ - r⁻¹ Ẏ·∇φ̃`, `∇φ ∘ Θ = r⁻¹ ∇φ̃`.
-/

section
/-- The pulled-back test function `φ̃ ∘ Θ⁻¹`. -/
def pullTest (Y : ℝ → Vec 2) (t c r : ℝ) (φ : ℝ × Vec 2 → ℝ) : ℝ × Vec 2 → ℝ :=
  fun q => φ (tubeInv Y t c r q)

theorem clm_apply_space (L : ℝ × Vec 2 →L[ℝ] ℝ) (v : Vec 2) :
    L (0, v) = vecDot v (fun i => L (0, basisVec i)) := by
  have hv : (0, v) = v 0 • ((0 : ℝ), basisVec (0 : Fin 2)) + v 1 • ((0 : ℝ), basisVec (1 : Fin 2)) := by
    refine Prod.ext (by simp) ?_
    funext j
    fin_cases j <;> simp [basisVec]
  rw [hv, map_add, map_smul, map_smul]
  simp [vecDot, Fin.sum_univ_two]

theorem clm_apply_split (L : ℝ × Vec 2 →L[ℝ] ℝ) (a : ℝ) (v : Vec 2) :
    L (a, v) = a * L (1, 0) + vecDot v (fun i => L (0, basisVec i)) := by
  have : ((a, v) : ℝ × Vec 2) = a • ((1 : ℝ), (0 : Vec 2)) + (0, v) := by
    refine Prod.ext (by simp) (by simp)
  rw [this, map_add, map_smul, clm_apply_space, smul_eq_mul]

section Deriv

variable {Y Yd : ℝ → Vec 2} {t c r : ℝ}

/-- The derivative of `tubeInv` at a point with time `s`. -/
def tubeInvLin (Yd : ℝ → Vec 2) (c r s : ℝ) : (ℝ × Vec 2) →L[ℝ] (ℝ × Vec 2) :=
  ((c⁻¹ • ContinuousLinearMap.fst ℝ ℝ (Vec 2)).prod
    (r⁻¹ • (ContinuousLinearMap.snd ℝ ℝ (Vec 2) -
      (ContinuousLinearMap.fst ℝ ℝ (Vec 2)).smulRight (Yd s))))

@[simp] theorem tubeInvLin_apply (Yd : ℝ → Vec 2) (c r s : ℝ) (v : ℝ × Vec 2) :
    tubeInvLin Yd c r s v = (c⁻¹ * v.1, r⁻¹ • (v.2 - v.1 • Yd s)) := by
  simp [tubeInvLin]

theorem hasFDerivAt_tubeInv (hYd : ∀ s, HasDerivAt Y (Yd s) s) (q : ℝ × Vec 2) :
    HasFDerivAt (tubeInv Y t c r) (tubeInvLin Yd c r q.1) q := by
  have hfst : HasFDerivAt (fun q : ℝ × Vec 2 => q.1) (ContinuousLinearMap.fst ℝ ℝ (Vec 2)) q :=
    (ContinuousLinearMap.fst ℝ ℝ (Vec 2)).hasFDerivAt
  have hsnd : HasFDerivAt (fun q : ℝ × Vec 2 => q.2) (ContinuousLinearMap.snd ℝ ℝ (Vec 2)) q :=
    (ContinuousLinearMap.snd ℝ ℝ (Vec 2)).hasFDerivAt
  have hY : HasFDerivAt (fun q : ℝ × Vec 2 => Y q.1)
      ((ContinuousLinearMap.fst ℝ ℝ (Vec 2)).smulRight (Yd q.1)) q := by
    have h1 := (hYd q.1).hasFDerivAt.comp q hfst
    exact h1.congr_fderiv (ContinuousLinearMap.ext fun v => by simp)
  have hA : HasFDerivAt (fun q : ℝ × Vec 2 => (q.1 - t) / c)
      (c⁻¹ • ContinuousLinearMap.fst ℝ ℝ (Vec 2)) q := by
    have := (hfst.sub_const t).const_smul c⁻¹
    convert this using 1
    funext q; simp [div_eq_inv_mul]
  have hB : HasFDerivAt (fun q : ℝ × Vec 2 => r⁻¹ • (q.2 - Y q.1))
      (r⁻¹ • (ContinuousLinearMap.snd ℝ ℝ (Vec 2) -
        (ContinuousLinearMap.fst ℝ ℝ (Vec 2)).smulRight (Yd q.1))) q :=
    (hsnd.sub hY).const_smul r⁻¹
  exact hA.prodMk hB

theorem fderiv_pullTest (hYd : ∀ s, HasDerivAt Y (Yd s) s) {φ : ℝ × Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (q v : ℝ × Vec 2) :
    fderiv ℝ (pullTest Y t c r φ) q v =
      fderiv ℝ φ (tubeInv Y t c r q) (c⁻¹ * v.1, r⁻¹ • (v.2 - v.1 • Yd q.1)) := by
  have hd : DifferentiableAt ℝ φ (tubeInv Y t c r q) :=
    (hφ.differentiable (by simp)).differentiableAt
  have hcomp := hd.hasFDerivAt.comp q (hasFDerivAt_tubeInv (t := t) (c := c) (r := r) hYd q)
  change fderiv ℝ (φ ∘ tubeInv Y t c r) q v = _
  rw [hcomp.fderiv]
  simp

theorem stTimeDeriv_pullTest (hYd : ∀ s, HasDerivAt Y (Yd s) s) {φ : ℝ × Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : c ≠ 0) (hr : r ≠ 0) (p : ℝ × Vec 2) :
    stTimeDeriv (pullTest Y t c r φ) (tubeMap Y t c r p) =
      c⁻¹ * stTimeDeriv φ p - r⁻¹ * vecDot (Yd (t + c * p.1)) (stSpaceGrad φ p) := by
  unfold stTimeDeriv
  rw [fderiv_pullTest hYd hφ, tubeInv_tubeMap hc hr]
  simp only [tubeMap]
  rw [clm_apply_split]
  simp only [mul_one, one_smul, zero_sub, smul_neg]
  rw [show vecDot (-(r⁻¹ • Yd (t + c * p.1))) (fun i => (fderiv ℝ φ p) (0, basisVec i)) =
    -(r⁻¹ * vecDot (Yd (t + c * p.1)) (fun i => (fderiv ℝ φ p) (0, basisVec i))) by
      simp only [vecDot, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring]
  rw [sub_eq_add_neg]
  rfl

theorem stSpaceGrad_pullTest (hYd : ∀ s, HasDerivAt Y (Yd s) s) {φ : ℝ × Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : c ≠ 0) (hr : r ≠ 0) (p : ℝ × Vec 2) :
    stSpaceGrad (pullTest Y t c r φ) (tubeMap Y t c r p) = r⁻¹ • stSpaceGrad φ p := by
  funext i
  unfold stSpaceGrad
  rw [fderiv_pullTest hYd hφ, tubeInv_tubeMap hc hr]
  simp only [zero_smul, sub_zero, mul_zero]
  rw [show ((0 : ℝ), r⁻¹ • basisVec i) = r⁻¹ • ((0 : ℝ), basisVec i) from by simp, map_smul]
  rfl

end Deriv

section Support

variable {Y : ℝ → Vec 2} {t c r : ℝ}

/-- `tubeMap` as a homeomorphism. -/
def tubeHomeo (hY : Continuous Y) (hc : c ≠ 0) (hr : r ≠ 0) :
    (ℝ × Vec 2) ≃ₜ (ℝ × Vec 2) where
  toFun := tubeMap Y t c r
  invFun := tubeInv Y t c r
  left_inv := tubeInv_tubeMap hc hr
  right_inv := tubeMap_tubeInv hc hr
  continuous_toFun := continuous_tubeMap hY
  continuous_invFun := continuous_tubeInv hY

theorem tsupport_pullTest (hY : Continuous Y) (hc : c ≠ 0) (hr : r ≠ 0) (φ : ℝ × Vec 2 → ℝ) :
    tsupport (pullTest Y t c r φ) = tubeMap Y t c r '' tsupport φ := by
  have hsupp : Function.support (pullTest Y t c r φ) =
      tubeInv Y t c r ⁻¹' Function.support φ := rfl
  have himg : ∀ A : Set (ℝ × Vec 2), tubeInv Y t c r ⁻¹' A = tubeMap Y t c r '' A := by
    intro A
    ext q
    constructor
    · intro hq
      exact ⟨tubeInv Y t c r q, hq, tubeMap_tubeInv hc hr q⟩
    · rintro ⟨p, hp, rfl⟩
      simpa [Set.mem_preimage, tubeInv_tubeMap hc hr] using hp
  unfold tsupport
  rw [hsupp, himg]
  exact ((tubeHomeo (t := t) hY hc hr).image_closure (Function.support φ)).symm

theorem contDiff_tubeInv (hY : ContDiff ℝ 1 Y) : ContDiff ℝ 1 (tubeInv Y t c r) := by
  unfold tubeInv
  refine ContDiff.prodMk ?_ ?_
  · exact (contDiff_fst.sub contDiff_const).div_const c
  · exact (contDiff_snd.sub (hY.comp contDiff_fst)).const_smul r⁻¹

theorem contDiff_pullTest (hY : ContDiff ℝ 1 Y) {φ : ℝ × Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) : ContDiff ℝ 1 (pullTest Y t c r φ) :=
  (hφ.of_le (by exact_mod_cast le_top)).comp (contDiff_tubeInv hY)

theorem hasCompactSupport_pullTest (hY : Continuous Y) (hc : c ≠ 0) (hr : r ≠ 0)
    {φ : ℝ × Vec 2 → ℝ} (hcs : HasCompactSupport φ) :
    HasCompactSupport (pullTest Y t c r φ) := by
  unfold HasCompactSupport
  rw [tsupport_pullTest hY hc hr]
  exact hcs.isCompact.image (continuous_tubeMap hY)

end Support
end

/-! # The rescaled weak formulation

`tubeU`, `tubeDU`, `tubeDrift` are the rescaled solution, gradient and relative drift of the
proof of Lemma 8.1 of the paper: for the pulled-back test
`φ = φ̃ ∘ Θ⁻¹` the weak formulation of `w` becomes, after the change of variables and a slice
integration by parts removing the `Ẏ·∇φ̃` term, the weak formulation of
`∂τU - ΔU + d·∇U = 0` in `Q₁`. -/

section
/-- The rescaled solution `U = w ∘ Θ`. -/
def tubeU (w : ℝ × Vec 2 → ℝ) (Y : ℝ → Vec 2) (t c r : ℝ) : ℝ × Vec 2 → ℝ :=
  fun p => w (tubeMap Y t c r p)

/-- The rescaled gradient `∇U = r (∇w) ∘ Θ`. -/
def tubeDU (Dw : ℝ × Vec 2 → Vec 2) (Y : ℝ → Vec 2) (t c r : ℝ) : ℝ × Vec 2 → Vec 2 :=
  fun p => r • Dw (tubeMap Y t c r p)

/-- The relative drift `d = (r/κ)(b(t', Y(t') + r y) - Ẏ(t'))`. -/
def tubeDrift (b : ℝ → Vec 2 → Vec 2) (Y Yd : ℝ → Vec 2) (t c r κ : ℝ) :
    ℝ × Vec 2 → Vec 2 :=
  fun p => (r / κ) • (b (t + c * p.1) (Y (t + c * p.1) + r • p.2) - Yd (t + c * p.1))

/-- The `Ẏ`-terms removed by slice integration by parts. -/
def tubeCorr (Yd : ℝ → Vec 2) (t c : ℝ) (U : ℝ × Vec 2 → ℝ) (DU : ℝ × Vec 2 → Vec 2)
    (φ : ℝ × Vec 2 → ℝ) (p : ℝ × Vec 2) : ℝ :=
  ∑ j : Fin 2, Yd (t + c * p.1) j * (U p * fderiv ℝ φ p (0, basisVec j) + DU p j * φ p)

theorem tube_pointwise {b : ℝ → Vec 2 → Vec 2} {w : ℝ × Vec 2 → ℝ} {Dw : ℝ × Vec 2 → Vec 2}
    {Y Yd : ℝ → Vec 2} {t c r κ : ℝ} (hYd : ∀ s, HasDerivAt Y (Yd s) s) {φ : ℝ × Vec 2 → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hr : 0 < r) (hκ : 0 < κ) (hc : c = r ^ 2 / κ)
    (p : ℝ × Vec 2) :
    (c * r ^ 2) * localWeakIntegrand b κ w Dw (pullTest Y t c r φ) (tubeMap Y t c r p) =
      r ^ 2 * (skewDriftIntegrand 0 (tubeDrift b Y Yd t c r κ) (tubeU w Y t c r)
        (tubeDU Dw Y t c r) φ p + (r / κ) * tubeCorr Yd t c (tubeU w Y t c r)
          (tubeDU Dw Y t c r) φ p) := by
  have hc0 : c ≠ 0 := by rw [hc]; positivity
  have hr0 : r ≠ 0 := hr.ne'
  have hκ0 : κ ≠ 0 := hκ.ne'
  have hpt : pullTest Y t c r φ (tubeMap Y t c r p) = φ p := by
    simp [pullTest, tubeInv_tubeMap hc0 hr0]
  unfold localWeakIntegrand skewDriftIntegrand tubeCorr
  rw [hpt, stTimeDeriv_pullTest hYd hφ hc0 hr0, stSpaceGrad_pullTest hYd hφ hc0 hr0]
  simp only [tubeU, tubeDU, tubeDrift, tubeMap, Pi.zero_apply,
    add_zero, Matrix.one_mulVec, vecDot, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul,
    Pi.sub_apply, stSpaceGrad]
  subst hc
  field_simp
  ring

section Integrability

variable {μ : Measure (ℝ × Vec 2)}

theorem integrable_mul_bdd_cont {f g : ℝ × Vec 2 → ℝ} (hf : Integrable f μ) (hg : Continuous g)
    {C : ℝ} (hC : ∀ p, ‖g p‖ ≤ C) : Integrable (fun p => f p * g p) μ :=
  hf.mul_bdd hg.aestronglyMeasurable (Filter.Eventually.of_forall hC)

theorem bound_of_compactSupport {g : ℝ × Vec 2 → ℝ} (hg : Continuous g) (hcs : HasCompactSupport g) :
    ∃ C, ∀ p, ‖g p‖ ≤ C := hg.bounded_above_of_compact_support hcs

theorem volume_openCyl_lt_top : volume (openCyl 0 1) < ⊤ := by
  refine lt_of_le_of_lt (measure_mono ?_) (lt_top_iff_ne_top.2
    (External.Campanato.cylinder_measure_ne_top (0 : ℝ × Vec 2) one_pos))
  intro p hp
  rw [mem_openCyl_zero_one_iff] at hp
  simp only [External.Campanato.cylinder, Set.mem_prod, Set.mem_Ioc, Prod.fst_zero,
    Prod.snd_zero, one_pow, zero_sub]
  exact ⟨⟨hp.1.1, hp.1.2.le⟩, by simpa [euclidBall] using hp.2⟩

theorem integrable_skewDriftIntegrand_zero {U : ℝ × Vec 2 → ℝ} {DU : ℝ × Vec 2 → Vec 2}
    {d : ℝ × Vec 2 → Vec 2} {φ : ℝ × Vec 2 → ℝ} (hU : Integrable U μ)
    (hDU : ∀ i : Fin 2, Integrable (fun p => DU p i) μ) (hd : Continuous d) {Bd : ℝ}
    (hdB : ∀ p, ‖d p‖ ≤ Bd) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ) :
    Integrable (skewDriftIntegrand 0 d U DU φ) μ := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  have hT := continuous_fderiv_apply_of_c1 hφ1 (1, 0)
  obtain ⟨CT, hCT⟩ := bound_of_compactSupport hT (hasCompactSupport_fderiv_apply hcs _)
  obtain ⟨Cφ, hCφ⟩ := bound_of_compactSupport hφ1.continuous hcs
  have hterm : ∀ i : Fin 2, Integrable (fun p => DU p i * (stSpaceGrad φ p i + d p i * φ p)) μ := by
    intro i
    have hG := continuous_fderiv_apply_of_c1 hφ1 (0, basisVec i)
    obtain ⟨Ci, hCi⟩ := bound_of_compactSupport hG (hasCompactSupport_fderiv_apply hcs _)
    have hcont : Continuous fun p => stSpaceGrad φ p i + d p i * φ p :=
      hG.add (((continuous_apply i).comp hd).mul hφ1.continuous)
    refine integrable_mul_bdd_cont (hDU i) hcont (C := Ci + Bd * Cφ) fun p => ?_
    calc ‖stSpaceGrad φ p i + d p i * φ p‖
        ≤ ‖stSpaceGrad φ p i‖ + ‖d p i * φ p‖ := norm_add_le _ _
      _ ≤ Ci + Bd * Cφ := by
        rw [norm_mul]
        exact add_le_add (hCi p) (mul_le_mul ((norm_le_pi_norm (d p) i).trans (hdB p)) (hCφ p)
          (norm_nonneg _) ((norm_nonneg _).trans (hdB p)))
  have heq : skewDriftIntegrand 0 d U DU φ = fun p => -(U p * stTimeDeriv φ p) +
      ∑ i : Fin 2, DU p i * (stSpaceGrad φ p i + d p i * φ p) := by
    funext p
    simp only [skewDriftIntegrand, Pi.zero_apply, add_zero, Matrix.one_mulVec, vecDot,
      Fin.sum_univ_two]
    ring
  rw [heq]
  exact (integrable_mul_bdd_cont hU hT hCT).neg.add (integrable_finsetSum _ fun i _ => hterm i)

theorem integrable_tubeCorr {Yd : ℝ → Vec 2} {t c : ℝ} (hYdc : Continuous Yd) {BY : ℝ}
    (hYdB : ∀ s, ‖Yd s‖ ≤ BY) {U : ℝ × Vec 2 → ℝ} {DU : ℝ × Vec 2 → Vec 2}
    {φ : ℝ × Vec 2 → ℝ} (hU : Integrable U μ) (hDU : ∀ i : Fin 2, Integrable (fun p => DU p i) μ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hcs : HasCompactSupport φ) :
    Integrable (tubeCorr Yd t c U DU φ) μ := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  obtain ⟨Cφ, hCφ⟩ := bound_of_compactSupport hφ1.continuous hcs
  have hY' : ∀ j : Fin 2, Continuous fun p : ℝ × Vec 2 => Yd (t + c * p.1) j := fun j =>
    (continuous_apply j).comp (hYdc.comp (continuous_const.add (continuous_const.mul
      continuous_fst)))
  have hterm : ∀ j : Fin 2, Integrable (fun p => Yd (t + c * p.1) j *
      (U p * fderiv ℝ φ p (0, basisVec j) + DU p j * φ p)) μ := by
    intro j
    have hG := continuous_fderiv_apply_of_c1 hφ1 (0, basisVec j)
    obtain ⟨Cj, hCj⟩ := bound_of_compactSupport hG (hasCompactSupport_fderiv_apply hcs _)
    have h1 : Integrable (fun p => (Yd (t + c * p.1) j * U p) * fderiv ℝ φ p (0, basisVec j)) μ :=
      integrable_mul_bdd_cont (hC := hCj) (by
        refine (integrable_mul_bdd_cont hU (hY' j) (C := BY) fun p => ?_).congr ?_
        · exact (norm_le_pi_norm _ j).trans (hYdB _)
        · exact Filter.Eventually.of_forall fun p => by simp [mul_comm]) hG
    have h2 : Integrable (fun p => (Yd (t + c * p.1) j * DU p j) * φ p) μ :=
      integrable_mul_bdd_cont (hC := hCφ) (by
        refine (integrable_mul_bdd_cont (hDU j) (hY' j) (C := BY) fun p => ?_).congr ?_
        · exact (norm_le_pi_norm _ j).trans (hYdB _)
        · exact Filter.Eventually.of_forall fun p => by simp [mul_comm]) hφ1.continuous
    refine (h1.add h2).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Pi.add_apply]
    ring
  exact integrable_finsetSum _ fun j _ => hterm j

theorem integrable_yd_mul {Yd : ℝ → Vec 2} {t c : ℝ} (hYdc : Continuous Yd) {BY : ℝ}
    (hYdB : ∀ s, ‖Yd s‖ ≤ BY) {f : ℝ × Vec 2 → ℝ} (hf : Integrable f μ) (j : Fin 2) :
    Integrable (fun p => Yd (t + c * p.1) j * f p) μ := by
  have hY' : Continuous fun p : ℝ × Vec 2 => Yd (t + c * p.1) j :=
    (continuous_apply j).comp (hYdc.comp (continuous_const.add (continuous_const.mul
      continuous_fst)))
  refine (integrable_mul_bdd_cont hf hY' (C := BY) fun p => ?_).congr
    (Filter.Eventually.of_forall fun p => by simp [mul_comm])
  exact (norm_le_pi_norm _ j).trans (hYdB _)

end Integrability

section Slice

/-- Constant multiples of weak partial derivatives. -/
theorem hasWeakPartialDerivOn_const_mul {B : Set (Vec 2)} {i : Fin 2} {u g : Vec 2 → ℝ} (a : ℝ)
    (h : HasWeakPartialDerivOn B i u g) :
    HasWeakPartialDerivOn B i (fun y => a * u y) (fun y => a * g y) := by
  intro φ hφ hcs hts
  have := h φ hφ hcs hts
  simp only [mul_assoc, integral_const_mul, this, neg_mul_eq_mul_neg]

theorem openCyl_zero_one_eq : openCyl 0 1 = Ioo (-1 : ℝ) 0 ×ˢ euclidBall 0 1 := by
  simp [openCyl]

/-- The slice integration by parts removing the `Ẏ`-terms. -/
theorem integral_tubeCorr_eq_zero {Yd : ℝ → Vec 2} {t c : ℝ} (hYdc : Continuous Yd) {BY : ℝ}
    (hYdB : ∀ s, ‖Yd s‖ ≤ BY) {U : ℝ × Vec 2 → ℝ} {DU : ℝ × Vec 2 → Vec 2}
    (hE : IsEnergyClassQ1 U DU) {φ : ℝ × Vec 2 → ℝ} (hφ : IsSTTest (openCyl 0 1) φ) :
    ∫ p in openCyl 0 1, tubeCorr Yd t c U DU φ p = 0 := by
  have hfin : IsFiniteMeasure (volume.restrict (openCyl 0 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact volume_openCyl_lt_top⟩
  have hU : Integrable U (volume.restrict (openCyl 0 1)) := hE.1.integrable one_le_two
  have hDU : ∀ i : Fin 2, Integrable (fun p => DU p i) (volume.restrict (openCyl 0 1)) :=
    fun i => (hE.2.1 i).integrable one_le_two
  have hφ1 : ContDiff ℝ 1 φ := hφ.1.of_le (by exact_mod_cast le_top)
  obtain ⟨Cφ, hCφ⟩ := bound_of_compactSupport hφ1.continuous hφ.2.1
  have hQ := openCyl_zero_one_eq
  have hψ : IsSTTest (Ioo (-1 : ℝ) 0 ×ˢ euclidBall 0 1) φ := by rwa [← hQ]
  have hj : ∀ j : Fin 2,
      ∫ p in openCyl 0 1, (Yd (t + c * p.1) j * U p) * fderiv ℝ φ p (0, basisVec j) =
        -∫ p in openCyl 0 1, (Yd (t + c * p.1) j * DU p j) * φ p := by
    intro j
    rw [hQ]
    refine integral_mul_partial_slice j ?_ ?_ ?_ hψ
    · rw [← hQ]; exact integrable_yd_mul hYdc hYdB hU j
    · rw [← hQ]; exact integrable_yd_mul hYdc hYdB (hDU j) j
    · filter_upwards [hE.2.2.1] with τ hτ
      exact hasWeakPartialDerivOn_const_mul (Yd (t + c * τ) j) (hτ j)
  have hG := fun j : Fin 2 => continuous_fderiv_apply_of_c1 hφ1 (0, basisVec j)
  have hI1 : ∀ j : Fin 2, Integrable (fun p => (Yd (t + c * p.1) j * U p) *
      fderiv ℝ φ p (0, basisVec j)) (volume.restrict (openCyl 0 1)) := fun j => by
    obtain ⟨Cj, hCj⟩ := bound_of_compactSupport (hG j) (hasCompactSupport_fderiv_apply hφ.2.1 _)
    exact integrable_mul_bdd_cont (integrable_yd_mul hYdc hYdB hU j) (hG j) hCj
  have hI2 : ∀ j : Fin 2, Integrable (fun p => (Yd (t + c * p.1) j * DU p j) * φ p)
      (volume.restrict (openCyl 0 1)) := fun j =>
    integrable_mul_bdd_cont (integrable_yd_mul hYdc hYdB (hDU j) j) hφ1.continuous hCφ
  have heq : tubeCorr Yd t c U DU φ = fun p => ∑ j : Fin 2,
      ((Yd (t + c * p.1) j * U p) * fderiv ℝ φ p (0, basisVec j) +
        (Yd (t + c * p.1) j * DU p j) * φ p) := by
    funext p
    unfold tubeCorr
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [heq]
  refine (integral_finsetSum (μ := volume.restrict (openCyl 0 1)) (Finset.univ : Finset (Fin 2))
    (f := fun j p => Yd (t + c * p.1) j * U p * fderiv ℝ φ p (0, basisVec j) +
      Yd (t + c * p.1) j * DU p j * φ p) fun j _ => (hI1 j).add (hI2 j)).trans ?_
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [integral_add (hI1 j) (hI2 j), hj j]
  ring

end Slice

section Main

variable {b : ℝ → Vec 2 → Vec 2} {w : ℝ × Vec 2 → ℝ} {Dw : ℝ × Vec 2 → Vec 2}
  {Y Yd : ℝ → Vec 2} {t r κ B : ℝ}

theorem continuous_tubeDrift {c : ℝ} (hbc : Continuous fun p : ℝ × Vec 2 => b p.1 p.2)
    (hY : Continuous Y) (hYdc : Continuous Yd) : Continuous (tubeDrift b Y Yd t c r κ) := by
  unfold tubeDrift
  have h1 : Continuous fun p : ℝ × Vec 2 => t + c * p.1 :=
    continuous_const.add (continuous_const.mul continuous_fst)
  have h3 : Continuous fun p : ℝ × Vec 2 => Y (t + c * p.1) + r • p.2 :=
    (hY.comp h1).add (continuous_snd.const_smul r)
  have h2 : Continuous fun p : ℝ × Vec 2 =>
      b (t + c * p.1) (Y (t + c * p.1) + r • p.2) := hbc.comp (h1.prodMk h3)
  exact (h2.sub (hYdc.comp h1)).const_smul (r / κ)

theorem norm_tubeDrift_le {c : ℝ} (hB : ∀ s y, ‖b s y‖ ≤ B) (hYdB : ∀ s, ‖Yd s‖ ≤ B)
    (p : ℝ × Vec 2) : ‖tubeDrift b Y Yd t c r κ p‖ ≤ |r / κ| * (B + B) := by
  unfold tubeDrift
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add (hB _ _) (hYdB _)))
    (abs_nonneg _)

/-- The rescaled solution is a weak solution of the small skew/drift problem with `K = 0`. -/
theorem tube_isSkewDriftWeak {O : Set (ℝ × Vec 2)} (hκ : 0 < κ) (hr : 0 < r) (hO : IsOpen O)
    (hw : IsLocalWeakSolution b κ O w Dw) (hbc : Continuous fun p : ℝ × Vec 2 => b p.1 p.2)
    (hB : ∀ s y, ‖b s y‖ ≤ B) (hY : ContDiff ℝ 1 Y) (hYd : ∀ s, HasDerivAt Y (Yd s) s)
    (hYdc : Continuous Yd) (hYdB : ∀ s, ‖Yd s‖ ≤ B) (hsub : closedTube Y t r κ ⊆ O)
    (hE : IsEnergyClassQ1 (tubeU w Y t (r ^ 2 / κ) r) (tubeDU Dw Y t (r ^ 2 / κ) r)) :
    IsSkewDriftWeak 0 (tubeDrift b Y Yd t (r ^ 2 / κ) r κ) (tubeU w Y t (r ^ 2 / κ) r)
      (tubeDU Dw Y t (r ^ 2 / κ) r) := by
  set c : ℝ := r ^ 2 / κ with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  have hr0 : r ≠ 0 := hr.ne'
  have hYm : Measurable Y := hY.continuous.measurable
  intro φ hφ
  -- the pulled-back test function
  have hφ1 : ContDiff ℝ 1 (pullTest Y t c r φ) := contDiff_pullTest hY hφ.1
  have hφcs : HasCompactSupport (pullTest Y t c r φ) :=
    hasCompactSupport_pullTest hY.continuous hc0.ne' hr0 hφ.2.1
  have hΘsub : tubeMap Y t c r '' openCyl 0 1 ⊆ O :=
    (tubeMap_image_subset_closedTube hr hκ).trans hsub
  have hφts : tsupport (pullTest Y t c r φ) ⊆ tubeMap Y t c r '' openCyl 0 1 := by
    rw [tsupport_pullTest hY.continuous hc0.ne' hr0]
    exact Set.image_mono hφ.2.2
  have h0 := weak_form_C1 hO hw hbc hB hφ1 hφcs (hφts.trans hΘsub)
  have hmeasΘ : MeasurableSet (tubeMap Y t c r '' openCyl 0 1) :=
    measurableSet_image_tubeMap hYm hc0 hr0 (openCyl_measurable 0 1)
  rw [setIntegral_localWeakIntegrand_eq hO.measurableSet hΘsub hφts] at h0
  have hcv := integral_tubeMap hYm hc0 hr0 (t := t)
    (localWeakIntegrand b κ w Dw (pullTest Y t c r φ)) (openCyl 0 1)
  rw [h0, mul_zero] at hcv
  change ∫ p in openCyl 0 1, skewDriftIntegrand 0 (tubeDrift b Y Yd t c r κ)
    (tubeU w Y t c r) (tubeDU Dw Y t c r) φ p = 0
  have hfin : IsFiniteMeasure (volume.restrict (openCyl 0 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact volume_openCyl_lt_top⟩
  have hU : Integrable (tubeU w Y t c r) (volume.restrict (openCyl 0 1)) :=
    hE.1.integrable one_le_two
  have hDU : ∀ i : Fin 2, Integrable (fun p => tubeDU Dw Y t c r p i)
      (volume.restrict (openCyl 0 1)) := fun i => (hE.2.1 i).integrable one_le_two
  have hS : Integrable (skewDriftIntegrand 0 (tubeDrift b Y Yd t c r κ) (tubeU w Y t c r)
      (tubeDU Dw Y t c r) φ) (volume.restrict (openCyl 0 1)) :=
    integrable_skewDriftIntegrand_zero hU hDU
      (continuous_tubeDrift (t := t) (r := r) (κ := κ) hbc hY.continuous hYdc)
      (norm_tubeDrift_le (t := t) (r := r) (κ := κ) hB hYdB) hφ.1 hφ.2.1
  have hR := integrable_tubeCorr (t := t) (c := c) hYdc hYdB hU hDU hφ.1 hφ.2.1
  have hR0 := integral_tubeCorr_eq_zero (t := t) (c := c) hYdc hYdB hE hφ
  have hpt : ∫ p in openCyl 0 1, (c * r ^ 2) * localWeakIntegrand b κ w Dw
      (pullTest Y t c r φ) (tubeMap Y t c r p) = ∫ p in openCyl 0 1, r ^ 2 *
        (skewDriftIntegrand 0 (tubeDrift b Y Yd t c r κ) (tubeU w Y t c r)
          (tubeDU Dw Y t c r) φ p + (r / κ) * tubeCorr Yd t c (tubeU w Y t c r)
            (tubeDU Dw Y t c r) φ p) :=
    setIntegral_congr_fun (openCyl_measurable 0 1) fun p _ =>
      tube_pointwise hYd hφ.1 hr hκ hc p
  rw [integral_const_mul, hcv, mul_zero, integral_const_mul,
    integral_add hS (hR.const_mul _), integral_const_mul, hR0] at hpt
  have hr2 : r ^ 2 ≠ 0 := by positivity
  have := (mul_eq_zero.1 hpt.symm).resolve_left hr2
  simpa using this

end Main
end

end AVRegularity.Applications
end
end
end
