-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Applications.Transfer.TubeK
import AVRegularity.Applications.Torus.TraceIdent
import AVRegularity.Applications.Microscopic.Main
import AVRegularity.Applications.LocalEnergy.Mollifier
import AVRegularity.Applications.TorusEnergy.LocalInt
import AVRegularity.Applications.TorusEnergy.StreamComparison
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Tactic.Monotonicity.Lemmas

@[expose] public section
noncomputable section

section
open MeasureTheory Filter Topology Homogenization AVenhance Set
namespace AVRegularity.Applications

/-! # One tube of the all-distance transfer

Fix `(t, z)`, a trajectory `Y` of `b_L` with `Y(t) = z`, and the rescaled functions. The finite
solution has oscillation `≲ S F ρ^s` in the tube (moving averages, `avg_const`), the difference
`u - v` has normalized `L²` norm `≲ ϑ F / ρ` (stream comparison), hence the rescaled full solution
has root mean square `≲ S F ρ^s + ϑ F/ρ` about the constant `c₀`, and the microscopic lemma gives
the profile `Wx` (as in the proof of Proposition 3.2 of the paper). -/

theorem vecNormSq_sigma_mulVec (e : Vec 2) : vecNormSq (sigmaMat.mulVec e) = vecNormSq e := by
  simp [sigmaMat, vecNormSq, vecDot, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem eNorm_le_one_of_mem {y : Vec 2} (hy : y ∈ euclidBall (0 : Vec 2) 1) : eNorm y ≤ 1 := by
  have : vecNormSq y < 1 := by simpa [euclidBall, vecNormSq, vecDot] using hy
  unfold eNorm; rw [Real.sqrt_le_one]; exact this.le

theorem volumeReal_openCyl_eq : volume.real (openCyl 0 1) = volume.real (euclidBall (0 : Vec 2) 1) := by
  rw [openCyl_zero_one_eq]
  unfold Measure.real
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  simp [Real.volume_Ioo]

theorem sq_split {f g c : ℝ} : (f - c) ^ 2 ≤ 2 * (f - g) ^ 2 + 2 * (g - c) ^ 2 := by
  nlinarith [sq_nonneg (f - 2 * g + c)]

theorem rms_split {α : Type*} [MeasurableSpace α] {μ : Measure α} {F G : α → ℝ} {c : ℝ}
    (hF : Integrable (fun p => (F p - c) ^ 2) μ) (h1 : Integrable (fun p => (F p - G p) ^ 2) μ)
    (h2 : Integrable (fun p => (G p - c) ^ 2) μ) :
    ∫ p, (F p - c) ^ 2 ∂μ ≤ 2 * ∫ p, (F p - G p) ^ 2 ∂μ + 2 * ∫ p, (G p - c) ^ 2 ∂μ := by
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (h1.const_mul 2) (h2.const_mul 2)]
  exact integral_mono hF ((h1.const_mul 2).add (h2.const_mul 2)) fun p => sq_split

theorem tube_step {a' η Ch : ℝ} (ha : 0 < a') (H : OcAt a' η Ch) (hCh : 0 ≤ Ch)
    {φ φL : ℝ → Vec 2 → ℝ} (hφ : IsFullStream φ) (hφL1 : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (φL t))
    (hφLc : Continuous fun p : ℝ × Vec 2 => φL p.1 p.2)
    (hbLc : Continuous fun p : ℝ × Vec 2 => streamVel φL p.1 p.2)
    {B : ℝ} (hBb : ∀ s y, ‖streamVel φ s y‖ ≤ B) (hBL : ∀ s y, ‖streamVel φL s y‖ ≤ B)
    {κ ρ DL ϑ : ℝ} (hκ : 0 < κ) (hρ : 0 < ρ) (hDL : 0 ≤ DL)
    (hlip : ∀ s x y, eNorm (streamVel φL s x - streamVel φL s y) ≤ DL * eNorm (x - y))
    (hψ : ∀ t x, |φ t x - φL t x| ≤ κ * ϑ) (hsm : ϑ + ρ ^ 2 / κ * DL ≤ η)
    {O : Set (ℝ × Vec 2)} (hO : IsOpen O) {u v : ℝ × Vec 2 → ℝ} {Du Dv : ℝ × Vec 2 → Vec 2}
    (hu : IsLocalWeakSolution (streamVel φ) κ O u Du)
    (hv : IsLocalWeakSolution (streamVel φL) κ O v Dv) (t : ℝ) (z : Vec 2)
    (hT : ∀ Y : ℝ → Vec 2, closedTube Y t ρ κ ⊆ O) {Au Av Aw : ℝ} (hAu0 : 0 ≤ Au) (hAw0 : 0 ≤ Aw)
    (hAu : ∀ᵐ s ∂(volume : Measure ℝ), ∀ y : Vec 2, euclidBall y ρ ⊆ timeSection O s →
      ∫ x in euclidBall y ρ, u (s, x) ^ 2 ≤ Au ^ 2)
    (hAv : ∀ᵐ s ∂(volume : Measure ℝ), ∀ y : Vec 2, euclidBall y ρ ⊆ timeSection O s →
      ∫ x in euclidBall y ρ, v (s, x) ^ 2 ≤ Av ^ 2)
    (hAw : ∀ᵐ s ∂(volume : Measure ℝ), ∀ y : Vec 2, euclidBall y ρ ⊆ timeSection O s →
      ∫ x in euclidBall y ρ, (u (s, x) - v (s, x)) ^ 2 ≤ Aw ^ 2)
    {Osc : ℝ} (hOsc : 0 ≤ Osc)
    (hVs : ∀ s ∈ Icc (t - ρ ^ 2 / κ) t, ∃ Vs : Vec 2 → ℝ,
      (∀ᵐ x ∂(volume : Measure (Vec 2)), v (s, x) = Vs x) ∧
      ∀ x x', eNorm (x - x') ≤ 2 * ρ → |Vs x - Vs x'| ≤ Osc) :
    ∃ Wx : Vec 2 → ℝ, ContinuousOn Wx (euclidBall z (ρ / 2)) ∧
      (∀ᶠ σ in 𝓝[<] t ⊓ ae (volume : Measure ℝ),
        IntegrableOn (fun y => (u (σ, y) - Wx y) ^ 2) (euclidBall z (ρ / 4))) ∧
      Tendsto (fun σ : ℝ => ∫ y in euclidBall z (ρ / 4), (u (σ, y) - Wx y) ^ 2)
        (𝓝[<] t ⊓ ae (volume : Measure ℝ)) (𝓝 0) ∧
      (∀ y ∈ euclidBall z (ρ / 2), |Wx y| ≤
        (Ch + 1) * ((Real.sqrt (volume.real (openCyl 0 1)))⁻¹ * (ρ⁻¹ * Au))) ∧
      (∀ y ∈ euclidBall z (ρ / 2), |Wx z - Wx y| ≤
        Ch * (Real.sqrt 2 * ((Real.sqrt (volume.real (openCyl 0 1)))⁻¹ * (ρ⁻¹ * Aw) +
          Osc * (1 + chiL1 + η * chiL2))) * (Real.sqrt (vecNormSq (z - y)) / ρ) ^ a') := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hBb 0 0)
  have hϑ : 0 ≤ ϑ := by
    by_contra h
    push Not at h
    have := (abs_nonneg (φ 0 0 - φL 0 0)).trans (hψ 0 0)
    nlinarith
  have hc : 0 < ρ ^ 2 / κ := by positivity
  set c := ρ ^ 2 / κ with hcdef
  obtain ⟨Y, hY1, hYt, hYd⟩ := exists_c1_trajectory hbLc ⟨B, hB0, hBL⟩ t z
  set Yd : ℝ → Vec 2 := fun s => streamVel φL (min s t) (Y (min s t)) with hYddef
  have hYdc : Continuous Yd := by
    have hmin : Continuous fun s : ℝ => min s t := continuous_id.min continuous_const
    exact hbLc.comp (hmin.prodMk (hY1.continuous.comp hmin))
  have hYdB : ∀ s, ‖Yd s‖ ≤ B := fun s => hBL _ _
  have hYd' : ∀ s, s ≤ t → Yd s = streamVel φL s (Y s) := fun s hs => by
    simp [hYddef, min_eq_left hs]
  have hsub := hT Y
  have hEu := tube_energyClass hY1.continuous hκ hρ hO hsub hu hAu
  have hEv := tube_energyClass hY1.continuous hκ hρ hO hsub hv hAv
  -- the finite drift
  set d := tubeDrift (streamVel φL) Y Yd t c ρ κ with hd
  have hdc : Continuous d := continuous_tubeDrift hbLc hY1.continuous hYdc
  have hdB : ∀ p, ‖d p‖ ≤ |ρ / κ| * (B + B) := norm_tubeDrift_le hBL hYdB
  set kd : ℝ := ρ ^ 2 / κ * DL with hkd
  have hkd0 : 0 ≤ kd := by positivity
  have hkdk : ∀ p ∈ openCyl 0 1, ‖d p‖ ≤ kd := fun p hp =>
    norm_tubeDrift_le_lip hDL hlip hρ hκ hcdef hYd' hp
  have hdiv : IsDivFreeQ1 d :=
    tube_divFree (fun s φ' h1 h2 => streamVel_integral_zero
      (fun t => (hφL1 t).of_le (by exact_mod_cast le_top)) s h1 h2) hbLc hρ
  -- finite solution: oscillation and constant
  have hWv := tube_isSkewDriftWeak hκ hρ hO hv hbLc hBL hY1 hYd hYdc hYdB hsub hEv
  have hosc : ∀ᵐ τ ∂(volume.restrict (Ioo (-1 : ℝ) 0)),
      ∀ᵐ y ∂(volume.restrict (euclidBall (0 : Vec 2) 1)),
        ∀ᵐ y' ∂(volume.restrict (euclidBall (0 : Vec 2) 1)),
          |tubeU v Y t c ρ (τ, y) - tubeU v Y t c ρ (τ, y')| ≤ Osc := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with τ hτ
    have hs : t + c * τ ∈ Icc (t - c) t := by
      obtain ⟨h1, h2⟩ := hτ
      constructor <;> nlinarith
    obtain ⟨Vs, hae, hosc⟩ := hVs _ hs
    have hy : ∀ᵐ y ∂(volume.restrict (euclidBall (0 : Vec 2) 1)),
        v (t + c * τ, spDil (Y (t + c * τ)) ρ y) = Vs (spDil (Y (t + c * τ)) ρ y) :=
      ae_restrict_spDil hρ.ne' (ae_restrict_of_ae hae)
    filter_upwards [hy, ae_restrict_mem (isOpen_euclidBall (0 : Vec 2) 1).measurableSet]
      with y hy1 hyb
    filter_upwards [hy, ae_restrict_mem (isOpen_euclidBall (0 : Vec 2) 1).measurableSet]
      with y' hy2 hy'b
    change |v (t + c * τ, Y (t + c * τ) + ρ • y) - v (t + c * τ, Y (t + c * τ) + ρ • y')| ≤ Osc
    have e1 : v (t + c * τ, Y (t + c * τ) + ρ • y) = Vs (Y (t + c * τ) + ρ • y) := hy1
    have e2 : v (t + c * τ, Y (t + c * τ) + ρ • y') = Vs (Y (t + c * τ) + ρ • y') := hy2
    rw [e1, e2]
    refine hosc _ _ ?_
    have h1 : Y (t + c * τ) + ρ • y - (Y (t + c * τ) + ρ • y') = ρ • (y - y') := by
      rw [add_sub_add_left_eq_sub, ← smul_sub]
    rw [h1]
    unfold eNorm
    rw [vecNormSq_smul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hρ.le]
    have h2 : Real.sqrt (vecNormSq (y - y')) ≤ 2 := by
      have := eNorm_add_le y (-y')
      rw [eNorm_neg, ← sub_eq_add_neg] at this
      have h3 := eNorm_le_one_of_mem hyb
      have h4 := eNorm_le_one_of_mem hy'b
      unfold eNorm at this h3 h4
      linarith
    nlinarith
  obtain ⟨c0, hc0⟩ := avg_const (V := tubeU v Y t c ρ) (DV := tubeDU Dv Y t c ρ) (d := d)
    (kd := kd) (O := Osc) (Bd := |ρ / κ| * (B + B)) hkd0 hOsc hEv hWv hdc hdB
    (fun τ i => tubeDrift_smooth hφL1 τ i)
    (fun τ y => tubeDrift_classical_div hφL1 τ y) hkdk hosc
  -- full solution
  set K : ℝ × Vec 2 → Matrix (Fin 2) (Fin 2) ℝ :=
    fun p => (tubePsi φ φL Y t c ρ p / κ) • sigmaMat with hK
  have hWu : IsSkewDriftWeak K d (tubeU u Y t c ρ) (tubeDU Du Y t c ρ) :=
    tube_skewData hφ hφL1 hφLc hbLc hBb hBL hκ hρ hO hu hY1 hYd hYdc hYdB hsub hψ hEu
  have hΨc : Continuous (tubePsi φ φL Y t c ρ) := by
    have hcont1 : Continuous fun p : ℝ × Vec 2 => t + c * p.1 :=
      continuous_const.add (continuous_const.mul continuous_fst)
    have hcomp : Continuous fun p : ℝ × Vec 2 =>
        (t + c * p.1, Y (t + c * p.1) + ρ • p.2) :=
      hcont1.prodMk ((hY1.continuous.comp hcont1).add (continuous_snd.const_smul ρ))
    exact (hφ.1.comp hcomp).sub (hφLc.comp hcomp)
  have hKbd : ∀ p, ∀ e : Vec 2, vecNormSq ((K p).mulVec e) ≤ ϑ ^ 2 * vecNormSq e := by
    intro p e
    have h1 : |tubePsi φ φL Y t c ρ p / κ| ≤ ϑ := by
      rw [abs_div, abs_of_pos hκ, div_le_iff₀ hκ]
      have := hψ (t + c * p.1) (Y (t + c * p.1) + ρ • p.2)
      simpa [tubePsi, mul_comm] using this
    simp only [hK, sigma_mulVec_smul, vecNormSq_smul, vecNormSq_sigma_mulVec]
    refine mul_le_mul_of_nonneg_right ?_ (vecNormSq_nonneg _)
    calc (tubePsi φ φL Y t c ρ p / κ) ^ 2 = |tubePsi φ φL Y t c ρ p / κ| ^ 2 := (sq_abs _).symm
      _ ≤ ϑ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hRu : rmsAbout (tubeU u Y t c ρ) 0 ≤ (Real.sqrt (volume.real (openCyl 0 1)))⁻¹ * (ρ⁻¹ * Au) := by
    have hv₁pos : 0 < volume.real (openCyl 0 1) := openCyl_volumeReal_pos
    have hint := integral_openCyl_sq_le (U := tubeU u Y t c ρ) hEu.1 (M := (ρ ^ 2)⁻¹ * Au ^ 2)
      (tube_slice_bound hκ hρ hsub hAu)
    have h1 : ⨍ p in openCyl 0 1, (tubeU u Y t c ρ p - 0) ^ 2 ≤
        ((Real.sqrt (volume.real (openCyl 0 1)))⁻¹ * (ρ⁻¹ * Au)) ^ 2 := by
      simp only [sub_zero]
      rw [setAverage_eq, smul_eq_mul]
      calc (volume.real (openCyl 0 1))⁻¹ * ∫ p in openCyl 0 1, tubeU u Y t c ρ p ^ 2
          ≤ (volume.real (openCyl 0 1))⁻¹ * ((ρ ^ 2)⁻¹ * Au ^ 2) :=
            mul_le_mul_of_nonneg_left hint (by positivity)
        _ = _ := by
            rw [mul_pow, mul_pow, inv_pow, inv_pow, Real.sq_sqrt hv₁pos.le]
    unfold rmsAbout
    calc _ ≤ Real.sqrt (((Real.sqrt (volume.real (openCyl 0 1)))⁻¹ * (ρ⁻¹ * Au)) ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = _ := Real.sqrt_sq (by positivity)
  have hv₁pos : 0 < volume.real (openCyl 0 1) := openCyl_volumeReal_pos
  have : IsFiniteMeasure (volume.restrict (openCyl 0 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact volume_openCyl_lt_top⟩
  set v₁ := volume.real (openCyl 0 1) with hv₁
  set Ov : ℝ := Osc + Osc * (chiL1 + kd * chiL2) with hOv
  set Ovc : ℝ := Osc * (1 + chiL1 + η * chiL2) with hOvc
  have hOv0 : 0 ≤ Ov := by
    have := chiL1_nonneg; have := chiL2_nonneg
    positivity
  have hkdη : kd ≤ η := by linarith
  have hOvle : Ov ≤ Ovc := by
    have h2 := chiL2_nonneg
    have : kd * chiL2 ≤ η * chiL2 := mul_le_mul_of_nonneg_right hkdη h2
    have := mul_le_mul_of_nonneg_left this hOsc
    simp only [hOv, hOvc]; nlinarith
  have hfinB : IsFiniteMeasure (volume.restrict (euclidBall (0 : Vec 2) 1)) :=
    isFiniteMeasure_restrict.mpr (volume_euclidBall_lt_top _ _).ne
  have hslV : ∀ᵐ τ ∂(volume.restrict (Ioo (-1 : ℝ) 0)),
      ∫ y in euclidBall (0 : Vec 2) 1, (tubeU v Y t c ρ (τ, y) - c0) ^ 2 ≤ v₁ * Ov ^ 2 := by
    filter_upwards [hc0] with τ hτ
    calc ∫ y in euclidBall (0 : Vec 2) 1, (tubeU v Y t c ρ (τ, y) - c0) ^ 2
        ≤ ∫ y in euclidBall (0 : Vec 2) 1, Ov ^ 2 := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun y => sq_nonneg _)
            (integrable_const _) ?_
          filter_upwards [hτ] with y hy
          exact sq_le_sq' (by linarith [abs_le.1 hy]) (by linarith [abs_le.1 hy])
      _ = v₁ * Ov ^ 2 := by
          rw [setIntegral_const, smul_eq_mul, hv₁, volumeReal_openCyl_eq]
  have hQv := integral_openCyl_sq_le (U := fun p => tubeU v Y t c ρ p - c0)
    (hEv.1.sub (memLp_const c0)) (M := v₁ * Ov ^ 2) hslV
  have hQw := integral_openCyl_sq_le (U := fun p => tubeU u Y t c ρ p - tubeU v Y t c ρ p)
    (hEu.1.sub hEv.1) (M := (ρ ^ 2)⁻¹ * Aw ^ 2)
    (tube_slice_bound (w := fun p => u p - v p) hκ hρ hsub hAw)
  have hsplit := rms_split (μ := volume.restrict (openCyl 0 1)) (F := tubeU u Y t c ρ)
    (G := tubeU v Y t c ρ) (c := c0)
    ((hEu.1.sub (memLp_const c0)).integrable_sq) ((hEu.1.sub hEv.1).integrable_sq)
    ((hEv.1.sub (memLp_const c0)).integrable_sq)
  have hrms : rmsAbout (tubeU u Y t c ρ) c0 ≤
      Real.sqrt 2 * ((Real.sqrt v₁)⁻¹ * (ρ⁻¹ * Aw) + Ovc) := by
    unfold rmsAbout
    set a := (Real.sqrt v₁)⁻¹ * (ρ⁻¹ * Aw) with ha0
    have ha : 0 ≤ a := by positivity
    have hOvc0 : 0 ≤ Ovc := hOv0.trans hOvle
    have h1 : ⨍ p in openCyl 0 1, (tubeU u Y t c ρ p - c0) ^ 2 ≤ (Real.sqrt 2 * (a + Ovc)) ^ 2 := by
      rw [setAverage_eq, smul_eq_mul]
      have h2 : ∫ p in openCyl 0 1, (tubeU u Y t c ρ p - c0) ^ 2 ≤
          2 * ((ρ ^ 2)⁻¹ * Aw ^ 2) + 2 * (v₁ * Ov ^ 2) :=
        hsplit.trans (by linarith)
      have h3 : v₁⁻¹ * (2 * ((ρ ^ 2)⁻¹ * Aw ^ 2) + 2 * (v₁ * Ov ^ 2)) = 2 * a ^ 2 + 2 * Ov ^ 2 := by
        have : a ^ 2 = v₁⁻¹ * ((ρ ^ 2)⁻¹ * Aw ^ 2) := by
          rw [ha0, mul_pow, mul_pow, inv_pow, inv_pow, Real.sq_sqrt hv₁pos.le]
        rw [this]; field_simp
      calc _ ≤ v₁⁻¹ * (2 * ((ρ ^ 2)⁻¹ * Aw ^ 2) + 2 * (v₁ * Ov ^ 2)) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = 2 * a ^ 2 + 2 * Ov ^ 2 := h3
        _ ≤ (Real.sqrt 2 * (a + Ovc)) ^ 2 := by
            have e2 : (Real.sqrt 2 * (a + Ovc)) ^ 2 = 2 * (a + Ovc) ^ 2 := by
              rw [mul_pow, Real.sq_sqrt (by norm_num)]
            rw [e2]
            nlinarith [mul_self_le_mul_self hOv0 hOvle]
    calc _ ≤ Real.sqrt ((Real.sqrt 2 * (a + Ovc)) ^ 2) := Real.sqrt_le_sqrt h1
      _ = _ := Real.sqrt_sq (by positivity)
  -- the microscopic lemma
  have hbdK : ∃ kK kd' : ℝ, 0 ≤ kK ∧ 0 ≤ kd' ∧ kK + kd' ≤ η ∧
      ∀ᵐ p ∂(volume.restrict (openCyl 0 1)),
        (∀ e : Vec 2, vecNormSq ((K p).mulVec e) ≤ kK ^ 2 * vecNormSq e) ∧
        vecNormSq (d p) ≤ kd' ^ 2 :=
    ⟨ϑ, kd, hϑ, hkd0, hsm, (ae_restrict_iff' (openCyl_measurable 0 1)).2
      (Eventually.of_forall fun p hp => ⟨hKbd p,
        vecNormSq_tubeDrift_le hlip hρ hκ hcdef hYd' hp⟩)⟩
  obtain ⟨Wx, hcont, hint, htr, hamp, -, hhol⟩ := tube_core ha H hCh (w := u) (Dw := Du)
    (Y := Y) (Yd := Yd) (t := t) (ρ := ρ) (κ := κ) (B := B) (Rb := (Real.sqrt v₁)⁻¹ * (ρ⁻¹ * Au))
    hκ hρ hY1 hYd hYdB hEu (K := K) (d := d)
    (fun i j => by
      refine Continuous.aestronglyMeasurable ?_
      simp only [hK, Matrix.smul_apply, smul_eq_mul]
      exact (hΨc.div_const κ).mul continuous_const)
    (fun i => ((continuous_apply i).comp hdc).aestronglyMeasurable)
    (Eventually.of_forall fun p => by
      ext i j; fin_cases i <;> fin_cases j <;> simp [hK, sigmaMat])
    hbdK hdiv hWu hRu
  rw [hYt] at hcont hint htr hamp hhol
  refine ⟨Wx, hcont, hint, htr, hamp, fun y hy => ?_⟩
  refine (hhol c0 y hy).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by positivity) _)
  exact mul_le_mul_of_nonneg_left hrms hCh

end AVRegularity.Applications
end

section
open MeasureTheory Homogenization AVenhance Set
namespace AVRegularity.Applications

/-! # Periodic functions equal on a cell, and pointwise values from `L²` bounds -/

theorem ae_eq_of_periodic_of_cube {g₁ g₂ : Vec 2 → ℝ}
    (h₁ : ∀ (n : Fin 2 → ℤ) x, g₁ (x + latticeShift n) = g₁ x)
    (h₂ : ∀ (n : Fin 2 → ℤ) x, g₂ (x + latticeShift n) = g₂ x)
    (h : ∀ᵐ x ∂(volume.restrict unitCube), g₁ x = g₂ x) :
    ∀ᵐ x ∂(volume : Measure (Vec 2)), g₁ x = g₂ x := by
  have hn : ∀ n : Fin 2 → ℤ, ∀ᵐ x ∂(volume.restrict (cubeShift n)), g₁ x = g₂ x := by
    intro n
    have hmp : MeasurePreserving (fun x : Vec 2 => x - latticeShift n) volume volume :=
      measurePreserving_sub_right volume _
    have := (hmp.restrict_preimage measurableSet_unitCube).quasiMeasurePreserving.ae h
    filter_upwards [this] with x hx
    have e1 := h₁ n (x - latticeShift n)
    have e2 := h₂ n (x - latticeShift n)
    simp only [sub_add_cancel] at e1 e2
    rw [e1, e2]; exact hx
  have hU : ∀ᵐ x ∂(volume.restrict (⋃ n : Fin 2 → ℤ, cubeShift n)), g₁ x = g₂ x :=
    (ae_restrict_iUnion_iff _ _).2 hn
  set N : Set (Vec 2) := ⋃ (i : Fin 2) (m : ℤ), {x : Vec 2 | x i = (m : ℝ)} with hN
  have hNnull : volume N = 0 := by
    refine measure_iUnion_null fun i => measure_iUnion_null fun m => ?_
    have := Measure.pi_hyperplane (fun _ : Fin 2 => (volume : Measure ℝ)) i (m : ℝ)
    rw [← volume_pi] at this
    exact this
  have hcompl : (⋃ n : Fin 2 → ℤ, cubeShift n)ᶜ ⊆ N := by
    intro x hx
    by_contra hxN
    apply hx
    simp only [hN, mem_iUnion, mem_ofPred_eq, not_exists] at hxN
    refine mem_iUnion.2 ⟨fun i => ⌊x i⌋, ?_⟩
    rw [mem_cubeShift]
    intro i
    have h1 : ((⌊x i⌋ : ℤ) : ℝ) ≤ x i := Int.floor_le _
    have h2 : x i < (⌊x i⌋ : ℝ) + 1 := Int.lt_floor_add_one _
    have h3 : x i ≠ (⌊x i⌋ : ℝ) := hxN i _
    exact ⟨by have := lt_of_le_of_ne h1 (Ne.symm h3); linarith, by linarith⟩
  have h0 : volume ((⋃ n : Fin 2 → ℤ, cubeShift n)ᶜ) = 0 := measure_mono_null hcompl hNnull
  refine ae_of_ae_restrict_of_ae_restrict_compl _ hU ?_
  rw [Measure.restrict_eq_zero.2 h0]
  rw [ae_zero]; exact Filter.eventually_bot

theorem volumeReal_euclidBall (x : Vec 2) {r : ℝ} (hr : 0 < r) :
    volume.real (euclidBall x r) = r ^ 2 * volume.real (euclidBall (0 : Vec 2) 1) := by
  have h := integral_spDil x hr.ne' (fun _ => (1 : ℝ)) (euclidBall 0 1)
  rw [image_spDil_euclidBall x hr, mul_one] at h
  simp only [integral_const, smul_eq_mul, mul_one] at h
  have h2 : (volume.restrict (euclidBall (0 : Vec 2) 1)).real univ =
      volume.real (euclidBall (0 : Vec 2) 1) := by simp [measureReal_def]
  have h3 : (volume.restrict (euclidBall x r)).real univ = volume.real (euclidBall x r) := by
    simp [measureReal_def]
  simp only [h2, h3] at h
  rw [h]
  field_simp

/-- A function that is `Λ`-close to its value at `x` on `B_r(x)` and has `L²(B_r(x))` norm at
most `Q` has `|Δ x| ≤ √2 ((vol B₁)^{-1/2} r⁻¹ Q + Λ)`. -/
theorem abs_le_of_ball_L2 {Δ : Vec 2 → ℝ} {x : Vec 2} {r Λ Q : ℝ} (hr : 0 < r) (hQ : 0 ≤ Q)
    (hΛ : ∀ y ∈ euclidBall x r, |Δ y - Δ x| ≤ Λ)
    (hint : IntegrableOn (fun y => Δ y ^ 2) (euclidBall x r))
    (hbound : ∫ y in euclidBall x r, Δ y ^ 2 ≤ Q ^ 2) :
    |Δ x| ≤ Real.sqrt 2 * ((Real.sqrt (volume.real (euclidBall (0 : Vec 2) 1)))⁻¹ * (r⁻¹ * Q) + Λ) := by
  have hvb : 0 < volume.real (euclidBall (0 : Vec 2) 1) := by
    rw [← volumeReal_openCyl_eq]
    exact openCyl_volumeReal_pos
  have hΛ0 : 0 ≤ Λ := (abs_nonneg _).trans (hΛ x (mem_euclidBall_self x hr))
  set vb := volume.real (euclidBall (0 : Vec 2) 1) with hvbdef
  have hvol : volume.real (euclidBall x r) = r ^ 2 * vb := volumeReal_euclidBall x hr
  have hfin : IsFiniteMeasure (volume.restrict (euclidBall x r)) :=
    isFiniteMeasure_restrict.mpr (volume_euclidBall_lt_top _ _).ne
  have hpt : ∀ y ∈ euclidBall x r, Δ x ^ 2 ≤ 2 * Δ y ^ 2 + 2 * Λ ^ 2 := by
    intro y hy
    have h1 := hΛ y hy
    have h2 : |Δ x| ≤ |Δ y| + Λ := by
      have := abs_sub_abs_le_abs_sub (Δ x) (Δ y)
      rw [abs_sub_comm] at this
      linarith
    have h3 : Δ x ^ 2 ≤ (|Δ y| + Λ) ^ 2 := by
      rw [← sq_abs (Δ x)]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
    nlinarith [sq_abs (Δ y), sq_nonneg (|Δ y| - Λ)]
  have hmono : ∫ y in euclidBall x r, Δ x ^ 2 ≤ ∫ y in euclidBall x r, (2 * Δ y ^ 2 + 2 * Λ ^ 2) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      ((hint.const_mul 2).add (integrable_const _)) ?_
    filter_upwards [ae_restrict_mem (isOpen_euclidBall x r).measurableSet] with y hy
    exact hpt y hy
  rw [integral_add (hint.const_mul 2) (integrable_const _), integral_const_mul, setIntegral_const,
    setIntegral_const, smul_eq_mul, smul_eq_mul, hvol] at hmono
  have h4 : r ^ 2 * vb * Δ x ^ 2 ≤ 2 * Q ^ 2 + r ^ 2 * vb * (2 * Λ ^ 2) := by
    linarith
  have h5 : Δ x ^ 2 ≤ 2 * ((Real.sqrt vb)⁻¹ * (r⁻¹ * Q)) ^ 2 + 2 * Λ ^ 2 := by
    have e : ((Real.sqrt vb)⁻¹ * (r⁻¹ * Q)) ^ 2 = (r ^ 2 * vb)⁻¹ * Q ^ 2 := by
      rw [mul_pow, mul_pow, inv_pow, inv_pow, Real.sq_sqrt hvb.le]; field_simp
    rw [e]
    have hp : 0 < r ^ 2 * vb := by positivity
    rw [← sub_nonneg]
    have : 2 * ((r ^ 2 * vb)⁻¹ * Q ^ 2) + 2 * Λ ^ 2 - Δ x ^ 2 =
        (r ^ 2 * vb)⁻¹ * (2 * Q ^ 2 + r ^ 2 * vb * (2 * Λ ^ 2) - r ^ 2 * vb * Δ x ^ 2) := by
      field_simp
    rw [this]
    exact mul_nonneg (by positivity) (by linarith)
  set a := (Real.sqrt vb)⁻¹ * (r⁻¹ * Q) with ha
  have ha0 : 0 ≤ a := by positivity
  have h6 : Δ x ^ 2 ≤ (Real.sqrt 2 * (a + Λ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    nlinarith [mul_nonneg ha0 hΛ0]
  have := abs_le_of_sq_le_sq' h6 (by positivity)
  exact (abs_le.2 this).trans' (le_refl _) |> fun h => by
    exact abs_le.2 ⟨by linarith [this.1], this.2⟩

end AVRegularity.Applications
end

section
open MeasureTheory Filter Topology Homogenization AVenhance Set
namespace AVRegularity.Applications

/-! # The transfer estimate at one time

Proposition 3.2 of the paper at one time: for every centre the microscopic lemma gives a
local continuous profile of `u(t)`; they glue to a periodic continuous function `W`, which is the
trace of `u(t)`, is within `D` of the finite solution, and has short increments, so
`holder_combine` bounds its `C^s(𝕋²)` norm. -/

/-- `(vol Q₁)^{-1/2}`. -/
def kap1 : ℝ := (Real.sqrt (volume.real (openCyl 0 1)))⁻¹

theorem kap1_nonneg : 0 ≤ kap1 := by unfold kap1; positivity

/-- The Hölder constant of the profile. -/
def lamOf (η s S F ϑ R : ℝ) : ℝ :=
  Real.sqrt 2 * (kap1 * ((R / 2)⁻¹ * (2 * (ϑ * F))) + S * F * R ^ s * (1 + chiL1 + η * chiL2))

/-- The bound for the distance to the finite solution. -/
def DOf (Ch η s S F ϑ R : ℝ) : ℝ :=
  Real.sqrt 2 * (kap1 * (((R / 2) / 4)⁻¹ * (2 * (ϑ * F))) +
    (Ch * lamOf η s S F ϑ R + S * F * R ^ s))

theorem ball_sq_le {g : Vec 2 → ℝ} (hper : IsZ2Periodic g) (hmem : MemL2On unitCube g) {ρ Q : ℝ}
    (hρ : 0 < ρ) (hρ2 : ρ ≤ 1 / 2) (hl : l2NormSq g ≤ Q ^ 2) (y : Vec 2) :
    ∫ x in euclidBall y ρ, g x ^ 2 ≤ (2 * Q) ^ 2 := by
  have h := ball_mass_le (f := fun x => g x ^ 2) (fun n x => by simp only [hper n x])
    (fun x => sq_nonneg _) hmem.integrable_sq hρ hρ2 y
  calc _ ≤ 4 * ∫ x in unitCube, g x ^ 2 := h
    _ ≤ 4 * Q ^ 2 := by unfold l2NormSq at hl; linarith
    _ = (2 * Q) ^ 2 := by ring

theorem diff_le_of_cs {s : ℝ} {g : Vec 2 → ℝ} {K : ℝ} (h : CsNormLe s g K) {y z : Vec 2}
    (hd : torusDist y z ≠ 0) : |g y - g z| ≤ K * torusDist y z ^ s := by
  have hdp : 0 < torusDist y z ^ s :=
    Real.rpow_pos_of_pos (lt_of_le_of_ne (torusDist_nonneg _ _) (Ne.symm hd)) s
  have := h y y z hd
  have h2 : |g y - g z| / torusDist y z ^ s ≤ K := by linarith [abs_nonneg (g y)]
  rwa [div_le_iff₀ hdp] at h2

theorem diff_le_of_cs_euclid {s R K : ℝ} (hs : 0 < s) {g : Vec 2 → ℝ} (h : CsNormLe s g K)
    (hK : 0 ≤ K) (hR : R ≤ 1 / 2) {y z : Vec 2} (hyz : eNorm (y - z) ≤ R) :
    |g y - g z| ≤ K * R ^ s := by
  by_cases hyz' : y = z
  · subst hyz'
    simp only [sub_self, abs_zero]
    exact mul_nonneg hK (Real.rpow_nonneg ((eNorm_nonneg _).trans hyz) _)
  · have hsmall : eNorm (y - z) ≤ 1 / 2 := hyz.trans hR
    have hpos := torusDist_pos_of_small hyz' hsmall
    have heq := torusDist_eq_of_small hsmall
    have := diff_le_of_cs h hpos.ne'
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hK)
    rw [heq]
    exact Real.rpow_le_rpow (eNorm_nonneg _) hyz hs.le

theorem eNorm_lt_iff_vecNormSq {y : Vec 2} {r : ℝ} (hr : 0 < r) :
    eNorm y < r ↔ vecNormSq y < r ^ 2 := by
  unfold eNorm
  rw [Real.sqrt_lt' hr]

/-! # The transfer estimate at one time (assembly) -/

theorem transfer_at {s a' η Ch : ℝ} (hs0 : 0 < s) (hsa : s ≤ a') (ha1 : a' < 1) (H : OcAt a' η Ch)
    (hCh : 0 ≤ Ch) {φ φL : ℝ → Vec 2 → ℝ} (hφ : IsFullStream φ)
    (hφL1 : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (φL t))
    (hφLc : Continuous fun p : ℝ × Vec 2 => φL p.1 p.2)
    (hbLc : Continuous fun p : ℝ × Vec 2 => streamVel φL p.1 p.2)
    {B : ℝ} (hBb : ∀ r y, ‖streamVel φ r y‖ ≤ B) (hBL : ∀ r y, ‖streamVel φL r y‖ ≤ B)
    {κ R DL ϑ S F tS tE t Cu Cv : ℝ} (hκ : 0 < κ) (hR0 : 0 < R) (hR8 : R ≤ 1 / 8) (hDL : 0 ≤ DL)
    (hS : 0 ≤ S) (hF : 0 ≤ F) (hCu : 0 ≤ Cu) (hCv : 0 ≤ Cv)
    (hlip : ∀ r x y, eNorm (streamVel φL r x - streamVel φL r y) ≤ DL * eNorm (x - y))
    (hψ : ∀ t x, |φ t x - φL t x| ≤ κ * ϑ) (hsm : ϑ + R ^ 2 / κ * DL ≤ η)
    (htS : tS < t - (R / 2) ^ 2 / κ) (htE : t < tE)
    {u v : ℝ → Vec 2 → ℝ} {Du Dv : ℝ × Vec 2 → Vec 2}
    (hu : IsLocalWeakSolution (streamVel φ) κ (Ioo tS tE ×ˢ (univ : Set (Vec 2)))
      (fun p => u p.1 p.2) Du)
    (hv : IsLocalWeakSolution (streamVel φL) κ (Ioo tS tE ×ˢ (univ : Set (Vec 2)))
      (fun p => v p.1 p.2) Dv)
    (hub : ∀ r ∈ Icc tS tE, IsZ2Periodic (u r) ∧ MemL2On unitCube (u r) ∧ l2NormSq (u r) ≤ Cu)
    (hvb : ∀ r ∈ Icc tS tE, IsZ2Periodic (v r) ∧ MemL2On unitCube (v r) ∧ l2NormSq (v r) ≤ Cv)
    (hcmp : ∀ r ∈ Icc tS tE, l2NormSq (fun x => u r x - v r x) ≤ (ϑ * F) ^ 2)
    (hV : ∀ r ∈ Icc (t - (R / 2) ^ 2 / κ) t, ∃ Vr : Vec 2 → ℝ, IsZ2Periodic Vr ∧
      Vr =ᵐ[volume.restrict unitCube] v r ∧ CsNormLe s Vr (S * F))
    (hident : ∀ W : Vec 2 → ℝ, Continuous W →
      (∀ x, Tendsto (fun σ : ℝ => ∫ y in euclidBall x (R / 2 / 4), (u σ y - W y) ^ 2)
        (𝓝[<] t ⊓ ae (volume : Measure ℝ)) (𝓝 0)) →
      W =ᵐ[volume.restrict unitCube] u t) :
    ∃ W : Vec 2 → ℝ, IsZ2Periodic W ∧ W =ᵐ[volume.restrict unitCube] u t ∧
      CsNormLe s W (S * F + 17 * DOf Ch η s S F ϑ R * R ^ (-s) +
        4 * (Ch * lamOf η s S F ϑ R) * R ^ (-s)) := by
  have hρ : 0 < R / 2 := by positivity
  have hρ2 : R / 2 ≤ 1 / 2 := by linarith
  have hϑ : 0 ≤ ϑ := by
    by_contra h
    push Not at h
    have := (abs_nonneg (φ 0 0 - φL 0 0)).trans (hψ 0 0)
    nlinarith
  have hSF : 0 ≤ S * F := mul_nonneg hS hF
  have hc : 0 < (R / 2) ^ 2 / κ := by positivity
  set ρ := R / 2 with hρdef
  set c := ρ ^ 2 / κ with hcdef
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hBb 0 0)
  have hsm' : ϑ + ρ ^ 2 / κ * DL ≤ η := by
    have : ρ ^ 2 / κ * DL ≤ R ^ 2 / κ * DL := by
      refine mul_le_mul_of_nonneg_right ?_ hDL
      refine div_le_div_of_nonneg_right ?_ hκ.le
      rw [hρdef]; nlinarith
    linarith
  have hO : IsOpen (Ioo tS tE ×ˢ (univ : Set (Vec 2))) := isOpen_Ioo.prod isOpen_univ
  have hTube : ∀ Y : ℝ → Vec 2, closedTube Y t ρ κ ⊆ Ioo tS tE ×ˢ (univ : Set (Vec 2)) := by
    intro Y p hp
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩
    · have := hp.1.1; linarith
    · have := hp.1.2; linarith
  have hmemO : ∀ {r : ℝ} {y : Vec 2}, euclidBall y ρ ⊆
      timeSection (Ioo tS tE ×ˢ (univ : Set (Vec 2))) r → r ∈ Icc tS tE := by
    intro r y h
    have := h (mem_euclidBall_self y hρ)
    exact ⟨this.1.1.le, this.1.2.le⟩
  -- slice bounds
  have hAu : ∀ᵐ r ∂(volume : Measure ℝ), ∀ y : Vec 2,
      euclidBall y ρ ⊆ timeSection (Ioo tS tE ×ˢ (univ : Set (Vec 2))) r →
      ∫ x in euclidBall y ρ, (fun p : ℝ × Vec 2 => u p.1 p.2) (r, x) ^ 2 ≤ (2 * Real.sqrt Cu) ^ 2 := by
    refine Eventually.of_forall fun r y hy => ?_
    obtain ⟨hp, hm, hl⟩ := hub r (hmemO hy)
    exact ball_sq_le hp hm hρ hρ2 (by rw [Real.sq_sqrt hCu]; exact hl) y
  have hAv : ∀ᵐ r ∂(volume : Measure ℝ), ∀ y : Vec 2,
      euclidBall y ρ ⊆ timeSection (Ioo tS tE ×ˢ (univ : Set (Vec 2))) r →
      ∫ x in euclidBall y ρ, (fun p : ℝ × Vec 2 => v p.1 p.2) (r, x) ^ 2 ≤ (2 * Real.sqrt Cv) ^ 2 := by
    refine Eventually.of_forall fun r y hy => ?_
    obtain ⟨hp, hm, hl⟩ := hvb r (hmemO hy)
    exact ball_sq_le hp hm hρ hρ2 (by rw [Real.sq_sqrt hCv]; exact hl) y
  have hAw : ∀ᵐ r ∂(volume : Measure ℝ), ∀ y : Vec 2,
      euclidBall y ρ ⊆ timeSection (Ioo tS tE ×ˢ (univ : Set (Vec 2))) r →
      ∫ x in euclidBall y ρ, ((fun p : ℝ × Vec 2 => u p.1 p.2) (r, x) -
        (fun p : ℝ × Vec 2 => v p.1 p.2) (r, x)) ^ 2 ≤ (2 * (ϑ * F)) ^ 2 := by
    refine Eventually.of_forall fun r y hy => ?_
    obtain ⟨hp, hm, -⟩ := hub r (hmemO hy)
    obtain ⟨hp', hm', -⟩ := hvb r (hmemO hy)
    exact ball_sq_le (g := fun x => u r x - v r x) (fun n x => by simp only [hp n x, hp' n x])
      (hm.sub hm') hρ hρ2 (hcmp r (hmemO hy)) y
  -- the oscillation of the finite solution
  have hOscV : ∀ r ∈ Icc (t - ρ ^ 2 / κ) t, ∃ Vs : Vec 2 → ℝ,
      (∀ᵐ x ∂(volume : Measure (Vec 2)),
        (fun p : ℝ × Vec 2 => v p.1 p.2) (r, x) = Vs x) ∧
      ∀ x x', eNorm (x - x') ≤ 2 * ρ → |Vs x - Vs x'| ≤ S * F * R ^ s := by
    intro r hr
    obtain ⟨Vr, hp, hae, hcs⟩ := hV r hr
    have hr' : r ∈ Icc tS tE := ⟨by linarith [hr.1], by linarith [hr.2]⟩
    refine ⟨Vr, ?_, fun x x' hx => ?_⟩
    · exact ae_eq_of_periodic_of_cube (hvb r hr').1 hp (hae.symm)
    · refine diff_le_of_cs_euclid hs0 hcs hSF (by linarith) ?_
      calc eNorm (x - x') ≤ 2 * ρ := hx
        _ = R := by rw [hρdef]; ring
  set hMamp : ℝ := (Ch + 1) * (kap1 * (ρ⁻¹ * (2 * Real.sqrt Cu))) with hMdef
  have hη : 0 ≤ η := by
    have : 0 ≤ ρ ^ 2 / κ * DL := by positivity
    linarith
  have hlam0 : 0 ≤ lamOf η s S F ϑ R := by
    have := chiL1_nonneg; have := chiL2_nonneg; have := kap1_nonneg
    unfold lamOf; positivity
  have ha0 : 0 < a' := hs0.trans_le hsa
  -- tube data at every centre
  have hTD : ∀ z : Vec 2, ∃ Wx : Vec 2 → ℝ, ContinuousOn Wx (euclidBall z (ρ / 2)) ∧
      (∀ᶠ σ in 𝓝[<] t ⊓ ae (volume : Measure ℝ),
        IntegrableOn (fun y => (u σ y - Wx y) ^ 2) (euclidBall z (ρ / 4))) ∧
      Tendsto (fun σ : ℝ => ∫ y in euclidBall z (ρ / 4), (u σ y - Wx y) ^ 2)
        (𝓝[<] t ⊓ ae (volume : Measure ℝ)) (𝓝 0) ∧
      (∀ y ∈ euclidBall z (ρ / 2), |Wx y| ≤ hMamp) ∧
      (∀ y ∈ euclidBall z (ρ / 2), |Wx z - Wx y| ≤
        Ch * lamOf η s S F ϑ R * (Real.sqrt (vecNormSq (z - y)) / ρ) ^ a') := by
    intro z
    obtain ⟨Wx, h1, h2, h3, h4, h5⟩ := tube_step (Au := 2 * Real.sqrt Cu) (Av := 2 * Real.sqrt Cv)
      (Aw := 2 * (ϑ * F)) (Osc := S * F * R ^ s) ha0 H hCh hφ hφL1 hφLc hbLc hBb hBL hκ hρ hDL
      hlip hψ hsm' hO hu hv t z hTube (by positivity) (by positivity) hAu hAv hAw
      (mul_nonneg hSF (Real.rpow_nonneg hR0.le _)) hOscV
    exact ⟨Wx, h1, h2, h3, h4, h5⟩
  choose Wf hWc hWi hWt hWa hWh using hTD
  have hperEv : ∀ᶠ σ in 𝓝[<] t ⊓ ae (volume : Measure ℝ),
      ∀ y (n : Fin 2 → ℤ), (fun p : ℝ × Vec 2 => u p.1 p.2) (σ, y + latticeShift n) =
        (fun p : ℝ × Vec 2 => u p.1 p.2) (σ, y) := by
    have : Ioo (t - c) t ∈ 𝓝[<] t := Ioo_mem_nhdsLT (by linarith)
    filter_upwards [mem_inf_of_left this] with σ hσ y n
    exact (hub σ ⟨by linarith [hσ.1], by linarith [hσ.2]⟩).1 n y
  obtain ⟨W, hWp, hWcont, hWeq, hWtr⟩ := glue_traces_periodic (w := fun p : ℝ × Vec 2 => u p.1 p.2)
    (t := t) (ρ := ρ) (M := hMamp) hρ hperEv hWc hWi hWt hWa
  have hWu : W =ᵐ[volume.restrict unitCube] u t := hident W hWcont hWtr
  obtain ⟨Vt, hVtp, hVtae, hVtcs⟩ := hV t ⟨by linarith, le_rfl⟩
  have htI : t ∈ Icc tS tE := ⟨by linarith, htE.le⟩
  obtain ⟨hup, hum, -⟩ := hub t htI
  obtain ⟨hvp, hvm, -⟩ := hvb t htI
  have hR2 : R ≤ 1 / 2 := by linarith
  have hr0 : 0 < ρ / 4 := by positivity
  have hr02 : ρ / 4 ≤ 1 / 2 := by linarith
  have hD : ∀ x, |W x - Vt x| ≤ DOf Ch η s S F ϑ R := by
    intro x
    set Δ : Vec 2 → ℝ := fun y => W y - Vt y with hΔ
    have hΔae : ∀ᵐ y ∂(volume : Measure (Vec 2)), Δ y = u t y - v t y := by
      refine ae_eq_of_periodic_of_cube (g₁ := Δ) (g₂ := fun y => u t y - v t y)
        (fun n y => by simp only [hΔ, hWp n y, hVtp n y]) (fun n y => by simp only [hup n y, hvp n y]) ?_
      filter_upwards [hWu, hVtae] with y h1 h2
      simp only [hΔ, h1, h2]
    have hΛ : ∀ y ∈ euclidBall x (ρ / 4), |Δ y - Δ x| ≤ Ch * lamOf η s S F ϑ R + S * F * R ^ s := by
      intro y hy
      have hy' : eNorm (y - x) < ρ / 4 := by
        rw [eNorm_lt_iff_vecNormSq hr0]; exact hy
      have hyb : y ∈ euclidBall x (ρ / 2) := euclidBall_mono x hr0.le (by linarith) hy
      have e1 : W y = Wf x y := hWeq x y hy
      have e2 : W x = Wf x x := hWeq x x (mem_euclidBall_self x hr0)
      have h1 : |W y - W x| ≤ Ch * lamOf η s S F ϑ R := by
        rw [e1, e2, abs_sub_comm]
        refine (hWh x y hyb).trans ?_
        have : Real.sqrt (vecNormSq (x - y)) / ρ ≤ 1 := by
          rw [div_le_one hρ]
          have : Real.sqrt (vecNormSq (x - y)) = eNorm (y - x) := by
            rw [← neg_sub, ← eNorm_neg]; rfl
          rw [this]; linarith
        have h2 := Real.rpow_le_one (by positivity) this ha0.le
        calc _ ≤ Ch * lamOf η s S F ϑ R * 1 :=
              mul_le_mul_of_nonneg_left h2 (mul_nonneg hCh hlam0)
          _ = _ := mul_one _
      have h2 : |Vt y - Vt x| ≤ S * F * R ^ s :=
        diff_le_of_cs_euclid hs0 hVtcs hSF hR2 (by linarith)
      have e3 : Δ y - Δ x = (W y - W x) - (Vt y - Vt x) := by simp only [hΔ]; ring
      rw [e3]
      exact (abs_sub _ _).trans (add_le_add h1 h2)
    have hint : IntegrableOn (fun y => Δ y ^ 2) (euclidBall x (ρ / 4)) := by
      have hm := memLp_ball_of_periodic (f := fun y => u t y - v t y)
        (fun n y => by simp only [hup n y, hvp n y]) (hum.sub hvm) hr0 hr02 x
      have := hm.integrable_sq
      refine this.congr ?_
      filter_upwards [ae_restrict_of_ae hΔae] with y hy
      simp only [hy]
    have hb : ∫ y in euclidBall x (ρ / 4), Δ y ^ 2 ≤ (2 * (ϑ * F)) ^ 2 := by
      have := ball_sq_le (g := fun y => u t y - v t y) (fun n y => by simp only [hup n y, hvp n y])
        (hum.sub hvm) hr0 hr02 (hcmp t htI) x
      refine le_trans (le_of_eq ?_) this
      refine integral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae hΔae] with y hy
      simp only [hy]
    have := abs_le_of_ball_L2 (Δ := Δ) (x := x) hr0 (by positivity : 0 ≤ 2 * (ϑ * F)) hΛ hint hb
    unfold DOf kap1
    rw [volumeReal_openCyl_eq]
    exact this
  have hD0 : 0 ≤ DOf Ch η s S F ϑ R := (abs_nonneg _).trans (hD 0)
  have hshort : ∀ z y, eNorm (y - z) < R / 8 →
      |W z - W y| ≤ Ch * lamOf η s S F ϑ R * (eNorm (y - z) / (R / 2)) ^ a' := by
    intro z y hzy
    have hr8 : R / 8 = ρ / 4 := by rw [hρdef]; ring
    rw [hr8] at hzy
    have hyb : y ∈ euclidBall z (ρ / 4) := by
      have := (eNorm_lt_iff_vecNormSq hr0).1 hzy
      exact this
    have hyb2 : y ∈ euclidBall z (ρ / 2) := euclidBall_mono z hr0.le (by linarith) hyb
    rw [hWeq z y hyb, hWeq z z (mem_euclidBall_self z hr0)]
    refine (hWh z y hyb2).trans (le_of_eq ?_)
    have : Real.sqrt (vecNormSq (z - y)) = eNorm (y - z) := by
      rw [← neg_sub, ← eNorm_neg]; rfl
    rw [this]
  refine ⟨W, hWp, hWu, ?_⟩
  exact holder_combine hs0 hsa (by linarith) hR0 (by linarith) (mul_nonneg hCh hlam0) hD0 hWp
    hVtcs hD hshort

end AVRegularity.Applications
end

section
open MeasureTheory Homogenization AVenhance Set
namespace AVRegularity.Applications

/-! # The constant of the all-distance transfer -/

/-- The coefficient of `S F`. -/
def transferC1 (Ch η : ℝ) : ℝ :=
  1 + 17 * Real.sqrt 2 + 17 * Real.sqrt 2 * Ch * Real.sqrt 2 * (1 + chiL1 + η * chiL2) +
    4 * Ch * Real.sqrt 2 * (1 + chiL1 + η * chiL2)

/-- The coefficient of `ϑ F R^{-1-s}`. -/
def transferC2 (Ch : ℝ) : ℝ :=
  17 * Real.sqrt 2 * 16 * kap1 + 17 * Real.sqrt 2 * Ch * Real.sqrt 2 * 4 * kap1 +
    4 * Ch * Real.sqrt 2 * 4 * kap1

/-- The constant of the transfer estimate. -/
def transferConst (Ch η : ℝ) : ℝ := transferC1 Ch η + transferC2 Ch

theorem transferC1_nonneg {Ch η : ℝ} (hCh : 0 ≤ Ch) (hη : 0 ≤ η) : 0 ≤ transferC1 Ch η := by
  have := chiL1_nonneg; have := chiL2_nonneg
  unfold transferC1; positivity

theorem transferC2_nonneg {Ch : ℝ} (hCh : 0 ≤ Ch) : 0 ≤ transferC2 Ch := by
  have := kap1_nonneg
  unfold transferC2; positivity

theorem transferConst_nonneg {Ch η : ℝ} (hCh : 0 ≤ Ch) (hη : 0 ≤ η) :
    0 ≤ transferConst Ch η :=
  add_nonneg (transferC1_nonneg hCh hη) (transferC2_nonneg hCh)

theorem kraw_le {Ch η s S F ϑ R : ℝ} (hCh : 0 ≤ Ch) (hη : 0 ≤ η) (hR0 : 0 < R) (hS : 0 ≤ S)
    (hF : 0 ≤ F) (hϑ : 0 ≤ ϑ) :
    S * F + 17 * DOf Ch η s S F ϑ R * R ^ (-s) + 4 * (Ch * lamOf η s S F ϑ R) * R ^ (-s) ≤
      transferConst Ch η * ((S + ϑ * R ^ (-1 - s)) * F) := by
  have hpq : R ^ (-s) * R ^ s = 1 := by
    rw [← Real.rpow_add hR0]; simp
  have hT : R ^ (-1 - s) = R⁻¹ * R ^ (-s) := by
    rw [show (-1 - s : ℝ) = -1 + -s by ring, Real.rpow_add hR0, Real.rpow_neg_one]
  set p := R ^ (-s) with hp
  set q := R ^ s with hq
  set T1 := S * F with hT1
  set T2 := ϑ * F * R ^ (-1 - s) with hT2
  have hT10 : 0 ≤ T1 := mul_nonneg hS hF
  have hT20 : 0 ≤ T2 := mul_nonneg (mul_nonneg hϑ hF) (Real.rpow_nonneg hR0.le _)
  have E1 : p * lamOf η s S F ϑ R =
      Real.sqrt 2 * (kap1 * (4 * T2) + T1 * (1 + chiL1 + η * chiL2)) := by
    unfold lamOf
    rw [hT2, hT, hT1]
    linear_combination (Real.sqrt 2 * (S * F) * (1 + chiL1 + η * chiL2)) * hpq
  have E2 : p * DOf Ch η s S F ϑ R =
      Real.sqrt 2 * (kap1 * (16 * T2) + Ch * (p * lamOf η s S F ϑ R) + T1) := by
    unfold DOf
    rw [hT2, hT, hT1]
    unfold lamOf
    linear_combination (Real.sqrt 2 * (S * F)) * hpq
  have hK : S * F + 17 * DOf Ch η s S F ϑ R * p + 4 * (Ch * lamOf η s S F ϑ R) * p =
      T1 + 17 * (p * DOf Ch η s S F ϑ R) + 4 * Ch * (p * lamOf η s S F ϑ R) := by ring
  rw [hK, E2, E1]
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hfin : transferConst Ch η * ((S + ϑ * R ^ (-1 - s)) * F) =
      (transferC1 Ch η + transferC2 Ch) * (T1 + T2) := by
    rw [hT1, hT2]; unfold transferConst; ring
  rw [hfin]
  have hc1 := transferC1_nonneg hCh hη
  have hc2 := transferC2_nonneg hCh
  have hk : kap1 ≥ 0 := kap1_nonneg
  have e : T1 + 17 * (Real.sqrt 2 * (kap1 * (16 * T2) + Ch * (Real.sqrt 2 * (kap1 * (4 * T2) +
      T1 * (1 + chiL1 + η * chiL2))) + T1)) + 4 * Ch * (Real.sqrt 2 * (kap1 * (4 * T2) +
      T1 * (1 + chiL1 + η * chiL2))) = transferC1 Ch η * T1 + transferC2 Ch * T2 := by
    unfold transferC1 transferC2; ring
  rw [e]
  nlinarith [mul_nonneg hc1 hT20, mul_nonneg hc2 hT10]

end AVRegularity.Applications
end

section
open MeasureTheory Filter Topology Homogenization AVenhance Set
namespace AVRegularity.Applications

/-! # The all-distance transfer

The exponent of the microscopic lemma is `a' = (1+s)/2`; the
streams are clamped in time to the window, the stream comparison gives the normalized `L²`
distance to the finite solution, and `transfer_at` handles one time. -/

/-- **All-distance transfer**. Proposition 3.2 of the paper follows from it. -/
theorem transfer_holds (s : ℝ) (hs₀ : 0 < s) (hs₁ : s < 1) : TransferStmt s := by
  have ha0 : 0 < (1 + s) / 2 := by linarith
  have ha1 : (1 + s) / 2 < 1 := by linarith
  have hsa : s ≤ (1 + s) / 2 := by linarith
  obtain ⟨η, Ch, hη, hCh, H⟩ := ocAt_of_statement ocMicroscopicStatement_holds ha0 ha1
  refine ⟨η, transferConst Ch η, hη, transferConst_nonneg hCh hη.le, ?_⟩
  intro φ φL hφ hφL DL κ ϑ R S F tS tE t₀ T f u v hlip hκ hψ hR0 hR8 hf hF hu hv htS ht₀T hTE
    hS hVhyp hsm t ht
  have hh : 0 < R ^ 2 / κ := by positivity
  have hRk : (R / 2) ^ 2 / κ ≤ R ^ 2 / κ := by
    refine div_le_div_of_nonneg_right ?_ hκ.le
    nlinarith
  have hab : tS ≤ tE := by linarith
  have h12 : tS < tE := by linarith [ht.2]
  -- nonnegativity of the constants
  have hϑ : 0 ≤ ϑ := by
    by_contra h
    push Not at h
    have := (abs_nonneg (φ 0 0 - φL 0 0)).trans (hψ 0 0)
    nlinarith
  have hDL : 0 ≤ DL := by
    by_contra h
    push Not at h
    have h1 := hlip 0 (fun _ => (1 : ℝ)) 0
    have h2 : 0 < eNorm ((fun _ : Fin 2 => (1 : ℝ)) - 0) := by
      unfold eNorm
      apply Real.sqrt_pos.mpr
      simp [vecNormSq, vecDot]
    nlinarith [eNorm_nonneg (streamVel φL 0 (fun _ => (1 : ℝ)) - streamVel φL 0 0)]
  have hF0 : 0 ≤ F := (Real.sqrt_nonneg _).trans hF
  -- the clamped streams
  set φc := clampStream tS tE φ with hφc
  set φLc := clampStream tS tE φL with hφLc
  have hφcF : IsFullStream φc := isFullStream_clamp hφ tS tE
  obtain ⟨hφLc1, hφLcv, ⟨BL, hBL⟩, -⟩ := clamp_smooth_stream hφL hab
  obtain ⟨Bb, hBb⟩ := hφ.2.2.2.1
  have hφLcont : Continuous fun p : ℝ × Vec 2 => φLc p.1 p.2 :=
    hφL.1.continuous.comp (((continuous_clampT tS tE).comp continuous_fst).prodMk continuous_snd)
  -- local solutions
  obtain ⟨Du, -, hlu⟩ := isLocalWeakSolution_of_isWeakSolutionOn
    (fun r _ => streamVel_periodic hφ.2.2.2.2 r) hu
  obtain ⟨Dv, -, hlv⟩ := isLocalWeakSolution_of_isWeakSolutionOn
    (fun r _ => streamVel_periodic hφL.2 r) hv
  have hO : IsOpen (Ioo tS tE ×ˢ (univ : Set (Vec 2))) := isOpen_Ioo.prod isOpen_univ
  have hlu' := hlu.congr_vel hO (v' := streamVel φc) (fun p hp => by
    rw [hφc, streamVel_clampStream, clampT_of_mem ⟨hp.1.1.le, hp.1.2.le⟩])
  have hlv' := hlv.congr_vel hO (v' := streamVel φLc) (fun p hp => by
    rw [hφLc, streamVel_clampStream, clampT_of_mem ⟨hp.1.1.le, hp.1.2.le⟩])
  -- energy bounds
  obtain ⟨Du0, hsu, ⟨Cu0, hCu0⟩, -⟩ := id hu
  obtain ⟨Dv0, hsv, ⟨Cv0, hCv0⟩, -⟩ := id hv
  have hcmp0 := stream_comparison hφ hφL hκ h12 hψ hf hu hv
  have hlf : l2NormSq f ≤ F ^ 2 := by
    have h0 : 0 ≤ l2NormSq f := integral_nonneg fun x => sq_nonneg _
    calc l2NormSq f = Real.sqrt (l2NormSq f) ^ 2 := (Real.sq_sqrt h0).symm
      _ ≤ F ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hF 2
  have hcmp : ∀ r ∈ Icc tS tE, l2NormSq (fun x => u r x - v r x) ≤ (ϑ * F) ^ 2 := by
    intro r hr
    refine (hcmp0 r hr).trans ?_
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hlf (sq_nonneg _)
  have hub : ∀ r ∈ Icc tS tE, IsZ2Periodic (u r) ∧ MemL2On unitCube (u r) ∧
      l2NormSq (u r) ≤ max Cu0 0 := fun r hr =>
    ⟨(hsu r hr).1, (hsu r hr).2, (hCu0 r hr).trans (le_max_left _ _)⟩
  have hvb : ∀ r ∈ Icc tS tE, IsZ2Periodic (v r) ∧ MemL2On unitCube (v r) ∧
      l2NormSq (v r) ≤ max Cv0 0 := fun r hr =>
    ⟨(hsv r hr).1, (hsv r hr).2, (hCv0 r hr).trans (le_max_left _ _)⟩
  -- the window
  have htS' : tS < t - (R / 2) ^ 2 / κ := by
    have := ht.1
    have h4 : (R / 2) ^ 2 / κ < R ^ 2 / κ := by
      refine div_lt_div_of_pos_right ?_ hκ
      nlinarith
    linarith
  have htE' : t < tE := by linarith [ht.2]
  have hV : ∀ r ∈ Icc (t - (R / 2) ^ 2 / κ) t, ∃ Vr : Vec 2 → ℝ, IsZ2Periodic Vr ∧
      Vr =ᵐ[volume.restrict unitCube] v r ∧ CsNormLe s Vr (S * F) := fun r hr =>
    hVhyp r ⟨by linarith [hr.1, ht.1], by linarith [hr.2, ht.2]⟩
  have hident : ∀ W : Vec 2 → ℝ, Continuous W →
      (∀ x, Tendsto (fun σ : ℝ => ∫ y in euclidBall x (R / 2 / 4), (u σ y - W y) ^ 2)
        (𝓝[<] t ⊓ ae (volume : Measure ℝ)) (𝓝 0)) →
      W =ᵐ[volume.restrict unitCube] u t := fun W hWc hW =>
    ae_eq_of_trace_from_below hu (by linarith [ht.1]) (by linarith [ht.2])
      (by positivity : 0 < R / 2 / 4) (by linarith) hWc hW
  obtain ⟨W, hWp, hWu, hWcs⟩ := transfer_at (s := s) (a' := (1 + s) / 2) (η := η) (Ch := Ch)
    hs₀ hsa ha1 H hCh hφcF hφLc1 hφLcont hφLcv (B := max Bb BL)
    (fun r y => by
      rw [hφc, streamVel_clampStream]; exact (hBb _ _).trans (le_max_left _ _))
    (fun r y => (hBL r y).trans (le_max_right _ _)) hκ hR0 hR8 hDL hS hF0
    (le_max_right _ _) (le_max_right _ _)
    (fun r x y => by rw [streamVel_clampStream]; exact hlip _ x y)
    (fun r x => hψ _ x) hsm htS' htE' hlu' hlv' hub hvb hcmp hV hident
  exact ⟨W, hWp, hWu, csNormLe_mono hWcs
    (by
      have := kraw_le (Ch := Ch) (η := η) (s := s) (S := S) (F := F) (ϑ := ϑ) hCh hη.le hR0 hS
        hF0 hϑ
      calc _ ≤ _ := this
        _ = _ := by ring)⟩

end AVRegularity.Applications
end
