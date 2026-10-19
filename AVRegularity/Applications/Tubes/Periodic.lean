-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Applications.Tubes.Trace
import AVRegularity.Applications.Torus.JointContinuityMain
public import AVRegularity.Applications.Microscopic.DilationTests
public import AVRegularity.Statements.Definitions.IsHolderDivFreeVelocity
public import AVRegularity.Statements.Definitions.TorusDist
public import AVenhance.Statements.Roots.UnitCube
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Monotonicity.Lemmas

section
section
/-! # One translating tube

For a point `(t, x)` and a backward trajectory ending there, the rescaled solution satisfies the
hypotheses of the microscopic oscillation lemma; reading the conclusion back gives a continuous
profile `Wx` on `B_{r/2}(x)` which is the `L²` trace of `w` at time `t` on `B_{r/4}(x)`, with the
amplitude and Hölder bounds (the proof of Lemma 8.1 of the paper). -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Homogenization Set AVRegularity.External.Campanato

namespace AVRegularity.Applications

theorem continuous_of_holder {α : ℝ} (hα : 0 < α) {b : ℝ → Vec 2 → Vec 2}
    (hb : IsHolderDivFreeVelocity α b) : Continuous fun p : ℝ × Vec 2 => b p.1 p.2 := by
  obtain ⟨C, hC⟩ := hb.2.2.2.1
  refine continuous_iff_continuousAt.2 fun p0 => ?_
  have hg : Continuous fun p : ℝ × Vec 2 =>
      |C| * (|p.1 - p0.1| + Real.sqrt (vecNormSq (p.2 - p0.2))) ^ α := by
    refine continuous_const.mul (Continuous.rpow_const ?_ fun _ => Or.inr hα.le)
    refine Continuous.add ?_ ?_
    · exact (continuous_fst.sub continuous_const).abs
    · refine Real.continuous_sqrt.comp ?_
      unfold vecNormSq vecDot
      fun_prop
  have h0 : Tendsto (fun p : ℝ × Vec 2 => |C| * (|p.1 - p0.1| +
      Real.sqrt (vecNormSq (p.2 - p0.2))) ^ α) (𝓝 p0) (𝓝 0) := by
    have := hg.tendsto p0
    simpa [vecNormSq, vecDot, Real.zero_rpow hα.ne'] using this
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun p => norm_nonneg _)
    (fun p => ?_) h0)
  calc ‖b p.1 p.2 - b p0.1 p0.2‖ ≤ C * (|p.1 - p0.1| + Real.sqrt (vecNormSq (p.2 - p0.2))) ^ α :=
        hC _ _ _ _
    _ ≤ |C| * (|p.1 - p0.1| + Real.sqrt (vecNormSq (p.2 - p0.2))) ^ α :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (by positivity) _)

theorem scale_bound {α η K0 κ r : ℝ} (hα : 0 < α) (hη : 0 < η) (hK0 : 0 < K0) (hκ : 0 < κ)
    (hr : 0 < r) (hrc : r ≤ (η / K0) ^ (1 / (1 + α)) * κ ^ (1 / (1 + α))) :
    r ^ (1 + α) ≤ η / K0 * κ := by
  have hp : 0 ≤ 1 + α := by linarith
  have hpne : 1 + α ≠ 0 := by linarith
  have h1 := Real.rpow_le_rpow hr.le hrc hp
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity),
    ← Real.rpow_mul hκ.le, one_div, inv_mul_cancel₀ hpne, Real.rpow_one, Real.rpow_one] at h1
  exact h1

theorem sqrt_vecNormSq_spDilInv (x z : Vec 2) {r : ℝ} (hr : 0 < r) :
    Real.sqrt (vecNormSq (spDilInv x r z)) = Real.sqrt (vecNormSq (x - z)) / r := by
  have h1 : spDilInv x r z = r⁻¹ • (z - x) := rfl
  have h2 : vecNormSq (z - x) = vecNormSq (x - z) := by
    rw [← vecNormSq_neg', neg_sub]
  rw [h1, vecNormSq_smul, h2, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  field_simp

theorem euclidBall_half_eq (x : Vec 2) (r : ℝ) : euclidBall x (r / 2) = euclidBall x (r * (1 / 2)) := by
  congr 1; ring

theorem openCyl_volumeReal_pos : 0 < volume.real (openCyl 0 1) := by
  have h1 : IsOpen (openCyl 0 1 : Set (ℝ × Vec 2)) := by
    unfold openCyl
    refine isOpen_Ioo.prod ?_
    have hcont : Continuous (fun x : Vec 2 => vecNormSq (x - 0)) := by
      unfold vecNormSq vecDot; fun_prop
    exact isOpen_lt hcont continuous_const
  have h2 : (openCyl 0 1 : Set (ℝ × Vec 2)).Nonempty := ⟨(-1 / 2, 0), by
    rw [mem_openCyl_zero_one_iff]
    refine ⟨⟨by norm_num, by norm_num⟩, by simp [vecNormSq, vecDot]⟩⟩
  exact ENNReal.toReal_pos (h1.measure_pos volume h2).ne' volume_openCyl_lt_top.ne

/-- The data attached to one tube. -/
theorem tube_data (hcamp : OcMicroscopicStatement) {α : ℝ} (hα₀ : 0 < α) {b : ℝ → Vec 2 → Vec 2}
    (hb : IsHolderDivFreeVelocity α b) {a' : ℝ} (ha0 : 0 < a') (ha1 : a' < 1) :
    ∃ c M₀ M₁ : ℝ, 0 < c ∧ 0 ≤ M₀ ∧ 0 ≤ M₁ ∧
      ∀ κ : ℝ, 0 < κ → ∀ O : Set (ℝ × Vec 2), IsOpen O →
      ∀ (w : ℝ × Vec 2 → ℝ) (Dw : ℝ × Vec 2 → Vec 2), IsLocalWeakSolution b κ O w Dw →
      ∀ A : ℝ, 0 ≤ A → ∀ r : ℝ, 0 < r → r ≤ c * κ ^ (1 / (1 + α)) →
        (∀ᵐ τ ∂(volume : Measure ℝ), ∀ y : Vec 2, euclidBall y r ⊆ timeSection O τ →
          ∫ x in euclidBall y r, w (τ, x) ^ 2 ≤ A ^ 2) →
      ∀ (t : ℝ) (x : Vec 2),
        (∀ X : ℝ → Vec 2, IsBackwardTrajectory b X t (r ^ 2 / κ) → X t = x →
          closedTube X t r κ ⊆ O) →
        ∃ Wx : Vec 2 → ℝ, ContinuousOn Wx (euclidBall x (r / 2)) ∧
          (∀ᶠ σ in 𝓝[<] t ⊓ ae (volume : Measure ℝ),
            IntegrableOn (fun y => (w (σ, y) - Wx y) ^ 2) (euclidBall x (r / 4))) ∧
          Tendsto (fun σ : ℝ => ∫ y in euclidBall x (r / 4), (w (σ, y) - Wx y) ^ 2)
            (𝓝[<] t ⊓ ae (volume : Measure ℝ)) (𝓝 0) ∧
          (∀ z ∈ euclidBall x (r / 2), |Wx z| ≤ M₀ * (r⁻¹ * A)) ∧
          ∀ z ∈ euclidBall x (r / 2),
            |Wx x - Wx z| ≤ M₁ * (r⁻¹ * A) * (Real.sqrt (vecNormSq (x - z)) / r) ^ a' := by
  obtain ⟨η, Ch, hη, hCh, H⟩ := ocAt_of_statement hcamp ha0 ha1
  obtain ⟨Cb, hCb⟩ := hb.2.2.2.1
  obtain ⟨Bb, hBb⟩ := hb.2.2.1
  have hbc := continuous_of_holder hα₀ hb
  set B : ℝ := max Bb 0 with hBdef
  have hB0 : 0 ≤ B := le_max_right _ _
  have hBb' : ∀ s y, ‖b s y‖ ≤ B := fun s y => (hBb s y).trans (le_max_left _ _)
  set K0 : ℝ := Real.sqrt 2 * |Cb| + 1 with hK0
  have hK0pos : 0 < K0 := by positivity
  set v₁ : ℝ := volume.real (openCyl 0 1) with hv₁
  have hv₁pos : 0 < v₁ := openCyl_volumeReal_pos
  set κ₁ : ℝ := (Real.sqrt v₁)⁻¹ with hκ₁
  have hκ₁pos : 0 < κ₁ := by positivity
  refine ⟨(η / K0) ^ (1 / (1 + α)), (Ch + 1) * κ₁, Ch * κ₁, by positivity, by positivity,
    by positivity, ?_⟩
  intro κ hκ O hO w Dw hw A hA0 r hr hrc hA t x hx
  have hc : 0 < r ^ 2 / κ := by positivity
  obtain ⟨Y, hY1, hYt, hYd⟩ := exists_c1_trajectory hbc ⟨B, hB0, hBb'⟩ t x
  set Yd : ℝ → Vec 2 := fun s => b (min s t) (Y (min s t)) with hYddef
  have hYdc : Continuous Yd := by
    have hYc : Continuous Y := hY1.continuous
    have hmin : Continuous fun s : ℝ => min s t := continuous_id.min continuous_const
    exact hbc.comp (hmin.prodMk (hYc.comp hmin))
  have hYdB : ∀ s, ‖Yd s‖ ≤ B := fun s => hBb' _ _
  have hsub : closedTube Y t r κ ⊆ O := hx Y (isBackwardTrajectory_of_hasDerivAt hYd) hYt
  have hE := tube_energyClass hY1.continuous hκ hr hO hsub hw hA
  have hW := tube_isSkewDriftWeak hκ hr hO hw hbc hBb' hY1 hYd hYdc hYdB hsub hE
  have hdiv := tube_divFree (fun s φ h1 h2 => hb.2.2.2.2 s φ h1 h2) hbc (Y := Y) (Yd := Yd) (t := t) (κ := κ) hr
  -- size of the drift
  have hscale := scale_bound hα₀ hη hK0pos hκ hr hrc
  set kd : ℝ := Real.sqrt 2 * |Cb| * r ^ (1 + α) / κ with hkd
  have hkd0 : 0 ≤ kd := by positivity
  have hkdη : kd ≤ η := by
    have h1 : r ^ (1 + α) / κ ≤ η / K0 := by
      rw [div_le_iff₀ hκ]; exact hscale
    calc kd = Real.sqrt 2 * |Cb| * (r ^ (1 + α) / κ) := by rw [hkd]; ring
      _ ≤ Real.sqrt 2 * |Cb| * (η / K0) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ K0 * (η / K0) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [hK0]; linarith
      _ = η := by field_simp
  have hYd' : ∀ s, s ≤ t → Yd s = b s (Y s) := fun s hs => by simp [hYddef, min_eq_left hs]
  have hdb : ∀ p ∈ openCyl 0 1,
      vecNormSq (tubeDrift b Y Yd t (r ^ 2 / κ) r κ p) ≤ kd ^ 2 :=
    fun p hp => tube_drift_bound hα₀ hCb hr hκ hYd' hp
  obtain ⟨Ut, hcont, htr, hhol, hbd⟩ := camp_apply ha0 H
    (continuous_tubeDrift hbc hY1.continuous hYdc) hkd0 hkdη hdb hdiv hE hW
  set U : ℝ × Vec 2 → ℝ := tubeU w Y t (r ^ 2 / κ) r with hU
  set R : ℝ := Real.sqrt (⨍ p in openCyl 0 1, U p ^ 2) with hR
  have hRle : R ≤ κ₁ * (r⁻¹ * A) := by
    have hint := integral_openCyl_sq_le (U := U) hE.1 (M := (r ^ 2)⁻¹ * A ^ 2)
      (tube_slice_bound hκ hr hsub hA)
    have h1 : ⨍ p in openCyl 0 1, U p ^ 2 ≤ (κ₁ * (r⁻¹ * A)) ^ 2 := by
      rw [setAverage_eq, smul_eq_mul]
      calc (volume.real (openCyl 0 1))⁻¹ * ∫ p in openCyl 0 1, U p ^ 2
          ≤ (volume.real (openCyl 0 1))⁻¹ * ((r ^ 2)⁻¹ * A ^ 2) :=
            mul_le_mul_of_nonneg_left hint (by positivity)
        _ = (κ₁ * (r⁻¹ * A)) ^ 2 := by
            rw [hκ₁, mul_pow, mul_pow, inv_pow, inv_pow, Real.sq_sqrt hv₁pos.le]
    calc R ≤ Real.sqrt ((κ₁ * (r⁻¹ * A)) ^ 2) := Real.sqrt_le_sqrt h1
      _ = κ₁ * (r⁻¹ * A) := Real.sqrt_sq (by positivity)
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hlip : ∀ s, ‖Y s - Y t‖ ≤ B * |s - t| := fun s => norm_sub_le_of_hasDerivAt hYd hYdB s t
  obtain ⟨hint, htrace⟩ := trace_package (w := w) (Ut := Ut) (Y := Y) (t := t) (r := r)
    (c := r ^ 2 / κ) (M₁ := Ch * R) (M₀ := (Ch + 1) * R) (a' := a') (B := B) hc hr ha0
    hY1.continuous hB0 hlip hcont hhol hbd htr (ae_slice_memLp hE.1)
  rw [hYt] at hint htrace
  have hz0 : ((0 : ℝ), (0 : Vec 2)) ∈ cylinder 0 (1 / 2) :=
    zero_mem_cylinder_of (by simp [euclidBall, vecNormSq, vecDot])
  have hprof : ∀ z ∈ euclidBall x (r / 2), spDilInv x r z ∈ euclidBall (0 : Vec 2) (1 / 2) := by
    intro z hz
    exact (mem_euclidBall_spDilInv hr).2 (by rwa [← euclidBall_half_eq])
  have hspx : spDilInv x r x = 0 := by simp [spDilInv]
  refine ⟨tubeProfile Ut x r, ?_, hint, htrace, ?_, ?_⟩
  · exact hcont.comp (by unfold spDilInv; fun_prop : Continuous fun y : Vec 2 =>
      ((0 : ℝ), spDilInv x r y)).continuousOn (fun y hy => zero_mem_cylinder_of (hprof y hy))
  · intro z hz
    have h1 : |tubeProfile Ut x r z| ≤ (Ch + 1) * R := hbd _ (zero_mem_cylinder_of (hprof z hz))
    calc |tubeProfile Ut x r z| ≤ (Ch + 1) * R := h1
      _ ≤ (Ch + 1) * (κ₁ * (r⁻¹ * A)) := mul_le_mul_of_nonneg_left hRle (by positivity)
      _ = (Ch + 1) * κ₁ * (r⁻¹ * A) := by ring
  · intro z hz
    have h0 : ((0 : Vec 2)) ∈ euclidBall (0 : Vec 2) (1 / 2) := by
      simp [euclidBall, vecNormSq, vecDot]
    have := holder_at_top hhol h0 (hprof z hz)
    rw [zero_sub, vecNormSq_neg', sqrt_vecNormSq_spDilInv x z hr] at this
    have h2 : tubeProfile Ut x r x = Ut (0, 0) := by simp only [tubeProfile, hspx]
    rw [h2]
    calc |Ut (0, 0) - tubeProfile Ut x r z| ≤ Ch * R * (Real.sqrt (vecNormSq (x - z)) / r) ^ a' :=
          this
      _ ≤ Ch * κ₁ * (r⁻¹ * A) * (Real.sqrt (vecNormSq (x - z)) / r) ^ a' := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by positivity) _)
          calc Ch * R ≤ Ch * (κ₁ * (r⁻¹ * A)) := mul_le_mul_of_nonneg_left hRle hCh
            _ = Ch * κ₁ * (r⁻¹ * A) := by ring

end AVRegularity.Applications
end
end
end

section
/-! # Gluing the tube representatives: `tube_regularity`

Representatives obtained from the tubes ending at different points `x ∈ K_t` agree on
overlapping discs (both are continuous `L²` limits of `w(σ,·)`), so they glue to a single
function `W`; the amplitude and Hölder bounds are read off the tube centered at the first point.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Homogenization Set

namespace AVRegularity.Applications

theorem isOpen_euclidBall (c : Vec 2) (ρ : ℝ) : IsOpen (euclidBall c ρ) := by
  have hcont : Continuous (fun x : Vec 2 => vecNormSq (x - c)) := by
    unfold vecNormSq vecDot; fun_prop
  exact isOpen_lt hcont continuous_const

theorem euclidBall_mono (c : Vec 2) {ρ ρ' : ℝ} (hρ : 0 ≤ ρ) (h : ρ ≤ ρ') :
    euclidBall c ρ ⊆ euclidBall c ρ' := by
  intro y hy
  simp only [euclidBall, Set.mem_ofPred_eq] at hy ⊢
  nlinarith

theorem mem_euclidBall_self (c : Vec 2) {ρ : ℝ} (hρ : 0 < ρ) : c ∈ euclidBall c ρ := by
  simp only [euclidBall, Set.mem_ofPred_eq, sub_self]
  simp [vecNormSq, vecDot]
  positivity

theorem vecNormSq_pos_of_ne {y z : Vec 2} (h : y ≠ z) : 0 < vecNormSq (y - z) := by
  rcases (vecNormSq_nonneg (y - z)).lt_or_eq with h' | h'
  · exact h'
  · exact absurd (sub_eq_zero.1 (vecNormSq_eq_zero h'.symm)) h

/-- The gluing theorem, together with the integrability of the traces. -/
theorem tube_regularity_aux (hcamp : OcMicroscopicStatement) {α : ℝ} (hα₀ : 0 < α)
    {b : ℝ → Vec 2 → Vec 2} (hb : IsHolderDivFreeVelocity α b) {s a' : ℝ} (hs₀ : 0 < s)
    (hsa : s < a') (ha₁ : a' < 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
      ∀ κ : ℝ, 0 < κ → ∀ O : Set (ℝ × Vec 2), IsOpen O →
      ∀ (w : ℝ × Vec 2 → ℝ) (Dw : ℝ × Vec 2 → Vec 2), IsLocalWeakSolution b κ O w Dw →
      ∀ A : ℝ, 0 ≤ A → ∀ r : ℝ, 0 < r → r ≤ 1 / 8 → r ≤ c * κ ^ (1 / (1 + α)) →
        (∀ᵐ τ ∂(volume : Measure ℝ), ∀ y : Vec 2, euclidBall y r ⊆ timeSection O τ →
          ∫ x in euclidBall y r, w (τ, x) ^ 2 ≤ A ^ 2) →
      ∀ (t : ℝ) (Kt : Set (Vec 2)),
        (∀ x ∈ Kt, ∀ X : ℝ → Vec 2, IsBackwardTrajectory b X t (r ^ 2 / κ) → X t = x →
          closedTube X t r κ ⊆ O) →
        ∃ W : Vec 2 → ℝ,
          ContinuousOn W (⋃ x ∈ Kt, euclidBall x (r / 4)) ∧
          (∀ x ∈ Kt, Tendsto (fun τ => ∫ y in euclidBall x (r / 4), (w (τ, y) - W y) ^ 2)
            (𝓝[<] t ⊓ ae volume) (𝓝 0)) ∧
          (∀ x ∈ Kt, ∀ᶠ σ in 𝓝[<] t ⊓ ae (volume : Measure ℝ),
            IntegrableOn (fun y => (w (σ, y) - W y) ^ 2) (euclidBall x (r / 4))) ∧
          ∀ x ∈ Kt, ∀ y ∈ Kt, ∀ z ∈ Kt, y ≠ z →
            |W x| + |W y - W z| / Real.sqrt (vecNormSq (y - z)) ^ s ≤ C * r ^ (-1 - s) * A := by
  have ha0 : 0 < a' := hs₀.trans hsa
  obtain ⟨c, M₀, M₁, hc, hM₀, hM₁, T⟩ := tube_data hcamp hα₀ hb ha0 ha₁
  refine ⟨c, M₀ + M₁ + 2 * 4 ^ s * M₀, hc, by positivity, ?_⟩
  intro κ hκ O hO w Dw hw A hA0 r hr hr8 hrc hA t Kt hKt
  have hex : ∀ x ∈ Kt, ∃ Wx : Vec 2 → ℝ, ContinuousOn Wx (euclidBall x (r / 2)) ∧
      (∀ᶠ σ in 𝓝[<] t ⊓ ae (volume : Measure ℝ),
        IntegrableOn (fun y => (w (σ, y) - Wx y) ^ 2) (euclidBall x (r / 4))) ∧
      Tendsto (fun σ : ℝ => ∫ y in euclidBall x (r / 4), (w (σ, y) - Wx y) ^ 2)
        (𝓝[<] t ⊓ ae (volume : Measure ℝ)) (𝓝 0) ∧
      (∀ z ∈ euclidBall x (r / 2), |Wx z| ≤ M₀ * (r⁻¹ * A)) ∧
      ∀ z ∈ euclidBall x (r / 2),
        |Wx x - Wx z| ≤ M₁ * (r⁻¹ * A) * (Real.sqrt (vecNormSq (x - z)) / r) ^ a' :=
    fun x hx => T κ hκ O hO w Dw hw A hA0 r hr hrc hA t x (hKt x hx)
  choose! Wf hcont hint htr hbd hhol using hex
  have hr4 : (0 : ℝ) ≤ r / 4 := by positivity
  have hsub4 : ∀ x : Vec 2, euclidBall x (r / 4) ⊆ euclidBall x (r / 2) := fun x =>
    euclidBall_mono x hr4 (by linarith)
  -- agreement on overlaps
  have hagree : ∀ x ∈ Kt, ∀ x' ∈ Kt, ∀ y ∈ euclidBall x (r / 4), y ∈ euclidBall x' (r / 4) →
      Wf x y = Wf x' y := by
    intro x hx x' hx' y hy hy'
    have hVo : IsOpen (euclidBall x (r / 4) ∩ euclidBall x' (r / 4)) :=
      (isOpen_euclidBall _ _).inter (isOpen_euclidBall _ _)
    refine traces_unique (t := t) (w := w) (M := M₀ * (r⁻¹ * A)) hVo
      (lt_of_le_of_lt (measure_mono inter_subset_left) (volume_euclidBall_lt_top _ _))
      inter_subset_left inter_subset_right
      ((hcont x hx).mono (inter_subset_left.trans (hsub4 x)))
      ((hcont x' hx').mono (inter_subset_right.trans (hsub4 x')))
      (fun z hz => hbd x hx z (hsub4 x hz.1)) (fun z hz => hbd x' hx' z (hsub4 x' hz.2))
      (hint x hx) (htr x hx) (hint x' hx') (htr x' hx') ⟨hy, hy'⟩
  classical
  let W : Vec 2 → ℝ := fun y =>
    if h : ∃ x ∈ Kt, y ∈ euclidBall x (r / 4) then Wf h.choose y else 0
  have hW : ∀ x ∈ Kt, ∀ y ∈ euclidBall x (r / 4), W y = Wf x y := by
    intro x hx y hy
    have h : ∃ x ∈ Kt, y ∈ euclidBall x (r / 4) := ⟨x, hx, hy⟩
    simp only [W, h, ↓reduceDIte]
    exact hagree _ h.choose_spec.1 x hx y h.choose_spec.2 hy
  have hWcongr : ∀ x ∈ Kt, ∀ σ : ℝ, ∫ y in euclidBall x (r / 4), (w (σ, y) - W y) ^ 2 =
      ∫ y in euclidBall x (r / 4), (w (σ, y) - Wf x y) ^ 2 := by
    intro x hx σ
    refine setIntegral_congr_fun (External.Campanato.euclidBall_measurable x _) fun y hy => ?_
    simp only [hW x hx y hy]
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · intro y hy
    simp only [mem_iUnion] at hy
    obtain ⟨x, hx, hyx⟩ := hy
    have hat : ContinuousAt (Wf x) y :=
      (hcont x hx).continuousAt ((isOpen_euclidBall x (r / 2)).mem_nhds (hsub4 x hyx))
    have heq : W =ᶠ[𝓝 y] Wf x :=
      Filter.eventuallyEq_of_mem ((isOpen_euclidBall x (r / 4)).mem_nhds hyx)
        fun z hz => hW x hx z hz
    exact (hat.congr heq.symm).continuousWithinAt
  · intro x hx
    simp only [hWcongr x hx]
    exact htr x hx
  · intro x hx
    refine (hint x hx).mono fun σ h => ?_
    exact h.congr_fun (fun y hy => by simp only [hW x hx y hy]) 
      (External.Campanato.euclidBall_measurable x _)
  · intro x hx y hy z hz hyz
    have hxx : x ∈ euclidBall x (r / 4) := mem_euclidBall_self x (by positivity)
    have hyy : y ∈ euclidBall y (r / 4) := mem_euclidBall_self y (by positivity)
    have hzz : z ∈ euclidBall z (r / 4) := mem_euclidBall_self z (by positivity)
    have hx2 : ∀ u ∈ Kt, |W u| ≤ M₀ * (r⁻¹ * A) := by
      intro u hu
      have huu : u ∈ euclidBall u (r / 4) := mem_euclidBall_self u (by positivity)
      rw [hW u hu u huu]
      exact hbd u hu u (hsub4 u huu)
    have hd0 : 0 < Real.sqrt (vecNormSq (y - z)) := Real.sqrt_pos.2 (vecNormSq_pos_of_ne hyz)
    have hr1 : r ≤ 1 := by linarith
    by_cases hd : Real.sqrt (vecNormSq (y - z)) < r / 4
    · have hzy : z ∈ euclidBall y (r / 4) := by
        simp only [euclidBall, Set.mem_ofPred_eq]
        have h1 : vecNormSq (z - y) = vecNormSq (y - z) := by
          rw [← vecNormSq_neg', neg_sub]
        rw [h1]
        have := Real.sqrt_lt' (by positivity) |>.1 hd
        exact this
      have hh := hhol y hy z (hsub4 y hzy)
      rw [hW y hy z hzy, hW y hy y hyy]
      have := bound_near hs₀ hsa hr hr1 hd0 (by linarith) hM₀ hM₁ hA0 (by
        have := hx2 x hx; exact this) (H := |Wf y y - Wf y z|) hh
      calc |W x| + |Wf y y - Wf y z| / Real.sqrt (vecNormSq (y - z)) ^ s
          ≤ (M₀ + M₁) * (r ^ (-1 - s) * A) := this
        _ ≤ (M₀ + M₁ + 2 * 4 ^ s * M₀) * r ^ (-1 - s) * A := by
          have : 0 ≤ r ^ (-1 - s) * A := by positivity
          nlinarith [this, mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2)
            (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 4) s)) hM₀]
    · have := bound_far hs₀ hr hr1 (not_lt.1 hd) hM₀ hA0 (hx2 x hx) (hx2 y hy) (hx2 z hz)
      calc |W x| + |W y - W z| / Real.sqrt (vecNormSq (y - z)) ^ s
          ≤ (M₀ + 2 * 4 ^ s * M₀) * (r ^ (-1 - s) * A) := this
        _ ≤ (M₀ + M₁ + 2 * 4 ^ s * M₀) * r ^ (-1 - s) * A := by
          have : 0 ≤ r ^ (-1 - s) * A := by positivity
          nlinarith [this]

/-- Interior regularity along translating tubes (full-velocity consequence of the microscopic
oscillation lemma), conditional on `OcMicroscopicStatement`. -/
theorem tube_regularity (hcamp : OcMicroscopicStatement) {α : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1)
    {b : ℝ → Vec 2 → Vec 2} (hb : IsHolderDivFreeVelocity α b) {s a' : ℝ} (hs₀ : 0 < s)
    (hsa : s < a') (ha₁ : a' < 1) :
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
            |W x| + |W y - W z| / Real.sqrt (vecNormSq (y - z)) ^ s ≤ C * r ^ (-1 - s) * A := by
  have _ := hα₁
  obtain ⟨c, C, hc, hC, H⟩ := tube_regularity_aux hcamp hα₀ hb hs₀ hsa ha₁
  refine ⟨c, C, hc, hC, fun κ hκ O hO w Dw hw A hA0 hA r hr hr8 hrc t Kt hKt => ?_⟩
  have hA' : ∀ᵐ τ ∂(volume : Measure ℝ), ∀ y : Vec 2, euclidBall y r ⊆ timeSection O τ →
      ∫ x in euclidBall y r, w (τ, x) ^ 2 ≤ A ^ 2 := by
    filter_upwards [hA] with τ ⟨hint, hle⟩ y hy
    exact (setIntegral_mono_set hint (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      (Filter.Eventually.of_forall hy)).trans hle
  obtain ⟨W, h1, h2, -, h4⟩ := H κ hκ O hO w Dw hw A hA0 r hr hr8 hrc hA' t Kt hKt
  exact ⟨W, h1, h2, h4⟩

end AVRegularity.Applications
end
end
end
end

section
section
/-! # Local mass on the torus

For a `ℤ²`-periodic `f ≥ 0` and `0 < ρ ≤ 1/2`, the disc `B_ρ(y)` meets at most four of the unit
squares `unitCube + n`, so `∫_{B_ρ(y)} f ≤ 4 ∫_{unitCube} f`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization Set

namespace AVRegularity.Applications

/-- The translate `unitCube + n`. -/
def cubeShift (n : Fin 2 → ℤ) : Set (Vec 2) :=
  (fun x => x - AVenhance.latticeShift n) ⁻¹' AVenhance.unitCube

theorem measurableSet_unitCube : MeasurableSet AVenhance.unitCube := by
  unfold AVenhance.unitCube
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ioo

theorem measurableSet_cubeShift (n : Fin 2 → ℤ) : MeasurableSet (cubeShift n) :=
  measurable_id.sub_const _ measurableSet_unitCube

theorem setIntegral_cubeShift {f : Vec 2 → ℝ} (n : Fin 2 → ℤ)
    (hper : ∀ x, f (x + AVenhance.latticeShift n) = f x) :
    ∫ x in cubeShift n, f x = ∫ x in AVenhance.unitCube, f x := by
  have h := setIntegral_map_equiv (μ := (volume : Measure (Vec 2)))
    (MeasurableEquiv.addRight (AVenhance.latticeShift n)) f (cubeShift n)
  have hmap : Measure.map (MeasurableEquiv.addRight (AVenhance.latticeShift n))
      (volume : Measure (Vec 2)) = volume := map_add_right_eq_self _ _
  rw [hmap] at h
  rw [h]
  have hpre : (MeasurableEquiv.addRight (AVenhance.latticeShift n)) ⁻¹' cubeShift n =
      AVenhance.unitCube := by
    ext x; simp [cubeShift]
  rw [hpre]
  exact setIntegral_congr_fun measurableSet_unitCube fun x _ => hper x

theorem integrableOn_cubeShift {f : Vec 2 → ℝ} (n : Fin 2 → ℤ)
    (hper : ∀ x, f (x + AVenhance.latticeShift n) = f x)
    (hint : IntegrableOn f AVenhance.unitCube) : IntegrableOn f (cubeShift n) := by
  have hemb := (MeasurableEquiv.addRight (AVenhance.latticeShift n)).measurableEmbedding
  have hmap : Measure.map (MeasurableEquiv.addRight (AVenhance.latticeShift n))
      (volume : Measure (Vec 2)) = volume := map_add_right_eq_self _ _
  have hpre : (MeasurableEquiv.addRight (AVenhance.latticeShift n)) ⁻¹' cubeShift n =
      AVenhance.unitCube := by
    ext x; simp [cubeShift]
  have h2 := hemb.integrableOn_map_iff (μ := (volume : Measure (Vec 2))) (f := f)
    (s := cubeShift n)
  rw [hmap, hpre] at h2
  refine h2.2 ?_
  exact (hint.congr_fun (fun x _ => (hper x).symm) measurableSet_unitCube)

theorem mem_cubeShift {n : Fin 2 → ℤ} {x : Vec 2} :
    x ∈ cubeShift n ↔ ∀ i, x i - (n i : ℝ) ∈ Ioo (0 : ℝ) 1 := by
  simp [cubeShift, AVenhance.unitCube, AVenhance.latticeShift, Set.mem_pi]

theorem ball_mass_le {f : Vec 2 → ℝ}
    (hper : ∀ (n : Fin 2 → ℤ) x, f (x + AVenhance.latticeShift n) = f x)
    (hf0 : ∀ x, 0 ≤ f x) (hint : IntegrableOn f AVenhance.unitCube) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ2 : ρ ≤ 1 / 2) (y : Vec 2) :
    ∫ x in euclidBall y ρ, f x ≤ 4 * ∫ x in AVenhance.unitCube, f x := by
  set k : Fin 2 → ℤ := fun i => ⌊y i - ρ⌋ with hk
  set mv : (Fin 2 → Fin 2) → (Fin 2 → ℤ) := fun e i => k i + ((e i : ℕ) : ℤ) with hmv
  set S : Set (Vec 2) := ⋃ e ∈ (Finset.univ : Finset (Fin 2 → Fin 2)), cubeShift (mv e) with hS
  have hSint : IntegrableOn f S := by
    refine (integrableOn_finset_iUnion).2 fun e _ => ?_
    exact integrableOn_cubeShift _ (hper _) hint
  -- the disc is a.e. contained in `S`
  set N : Set (Vec 2) := ⋃ (i : Fin 2) (m : ℤ), {x : Vec 2 | x i = (m : ℝ)} with hN
  have hNnull : volume N = 0 := by
    refine measure_iUnion_null fun i => measure_iUnion_null fun m => ?_
    have := Measure.pi_hyperplane (fun _ : Fin 2 => (volume : Measure ℝ)) i (m : ℝ)
    rw [← volume_pi] at this
    exact this
  have hcov : euclidBall y ρ ≤ᵐ[volume] S := by
    have hae : ∀ᵐ x ∂(volume : Measure (Vec 2)), x ∉ N := by
      rw [ae_iff]; simpa using hNnull
    filter_upwards [hae] with x hxN hxb
    simp only [hN, mem_iUnion, mem_ofPred_eq, not_exists] at hxN
    have hcoord : ∀ i, |x i - y i| < ρ := by
      intro i
      have h1 := sq_apply_le_vecNormSq (x - y) i
      have h2 : vecNormSq (x - y) < ρ ^ 2 := hxb
      simp only [Pi.sub_apply] at h1
      exact abs_lt_of_sq_lt_sq (lt_of_le_of_lt h1 h2) hρ.le
    simp only [hS, mem_iUnion, Finset.mem_univ, exists_true_left]
    refine ⟨fun i => if x i < (k i : ℝ) + 1 then 0 else 1, ?_⟩
    rw [mem_cubeShift]
    intro i
    have hi := abs_lt.1 (hcoord i)
    have hk1 : (k i : ℝ) ≤ y i - ρ := Int.floor_le _
    have hk2 : y i - ρ < (k i : ℝ) + 1 := Int.lt_floor_add_one _
    have hne := hxN i (k i + 1)
    push_cast at hne
    by_cases hlt : x i < (k i : ℝ) + 1
    · simp only [hmv, hlt, ↓reduceIte]
      push_cast
      constructor <;> simp <;> linarith [hi.1]
    · have hgt : (k i : ℝ) + 1 < x i := lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne)
      simp only [hmv, hlt, ↓reduceIte]
      push_cast
      constructor <;> simp <;> linarith [hi.2]
  have hdisj : (↑(Finset.univ : Finset (Fin 2 → Fin 2)) : Set (Fin 2 → Fin 2)).Pairwise
      (Function.onFun Disjoint fun e => cubeShift (mv e)) := by
    intro e _ e' _ hee'
    obtain ⟨i, hi⟩ : ∃ i, e i ≠ e' i := by
      by_contra h; push Not at h; exact hee' (funext h)
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    rw [mem_cubeShift] at hx hx'
    have a := hx i
    have b := hx' i
    simp only [hmv] at a b
    push_cast at a b
    have he : ∀ j : Fin 2, ((j : ℕ) : ℝ) = 0 ∨ ((j : ℕ) : ℝ) = 1 := by
      intro j; fin_cases j <;> simp
    rcases he (e i) with h1 | h1 <;> rcases he (e' i) with h2 | h2
    · exact hi (Fin.ext (by exact_mod_cast h1.trans h2.symm))
    · rw [h1] at a; rw [h2] at b; linarith [a.1, a.2, b.1, b.2]
    · rw [h1] at a; rw [h2] at b; linarith [a.1, a.2, b.1, b.2]
    · exact hi (Fin.ext (by exact_mod_cast h1.trans h2.symm))
  calc ∫ x in euclidBall y ρ, f x ≤ ∫ x in S, f x :=
        setIntegral_mono_set hSint (Filter.Eventually.of_forall hf0) hcov
    _ = ∑ e ∈ (Finset.univ : Finset (Fin 2 → Fin 2)), ∫ x in cubeShift (mv e), f x :=
        integral_biUnion_finset _ (fun e _ => measurableSet_cubeShift _) hdisj
          (fun e _ => integrableOn_cubeShift _ (hper _) hint)
    _ = ∑ e ∈ (Finset.univ : Finset (Fin 2 → Fin 2)), ∫ x in AVenhance.unitCube, f x :=
        Finset.sum_congr rfl fun e _ => setIntegral_cubeShift _ (hper _)
    _ = 4 * ∫ x in AVenhance.unitCube, f x := by
        rw [Finset.sum_const, Finset.card_univ]
        simp

end AVRegularity.Applications
end
end
end

section
/-! # The periodic form of `tube_regularity`

For `ℤ²`-periodic `w` the glued representative is `ℤ²`-periodic (uniqueness of the continuous
`L²` trace), and the Hölder bound holds for the torus distance: the bound for `(y, z + n)` holds
for every lattice vector `n`, and `torusDist y z` is the infimum of the corresponding
Euclidean distances. The mass hypothesis is the torus bound
`∫_{unitCube} w(τ)² ≤ A²`; discs of radius `≤ 1/2` meet at most four unit squares, so the
`L^∞L²` hypothesis of `tube_regularity` holds with `2A`. -/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Homogenization Set

namespace AVRegularity.Applications

theorem setIntegral_ball_add (g : Vec 2 → ℝ) (a x : Vec 2) (ρ : ℝ) :
    ∫ y in euclidBall x ρ, g (y + a) = ∫ y in euclidBall (x + a) ρ, g y := by
  have h := setIntegral_map_equiv (μ := (volume : Measure (Vec 2)))
    (MeasurableEquiv.addRight a) g (euclidBall (x + a) ρ)
  have hmap : Measure.map (MeasurableEquiv.addRight a) (volume : Measure (Vec 2)) = volume :=
    map_add_right_eq_self _ _
  rw [hmap] at h
  rw [h]
  have hpre : (MeasurableEquiv.addRight a) ⁻¹' euclidBall (x + a) ρ = euclidBall x ρ := by
    ext y; simp [euclidBall]
  rw [hpre]
  rfl

theorem integrableOn_ball_add {g : Vec 2 → ℝ} (a x : Vec 2) (ρ : ℝ)
    (h : IntegrableOn g (euclidBall (x + a) ρ)) :
    IntegrableOn (fun y => g (y + a)) (euclidBall x ρ) := by
  have hemb := (MeasurableEquiv.addRight a).measurableEmbedding
  have hmap : Measure.map (MeasurableEquiv.addRight a) (volume : Measure (Vec 2)) = volume :=
    map_add_right_eq_self _ _
  have hpre : (MeasurableEquiv.addRight a) ⁻¹' euclidBall (x + a) ρ = euclidBall x ρ := by
    ext y; simp [euclidBall]
  have h2 := hemb.integrableOn_map_iff (μ := (volume : Measure (Vec 2))) (f := g)
    (s := euclidBall (x + a) ρ)
  rw [hmap, hpre] at h2
  exact h2.1 h

/-- The torus-distance infimum argument. -/
theorem torus_bound_of_shifts {y z : Vec 2} {p q Mx s : ℝ} (hs : 0 < s) (hq : 0 ≤ q)
    (hρ : torusDist y z ≠ 0)
    (h : ∀ n : Fin 2 → ℤ, 0 < Real.sqrt (vecNormSq (y - z - AVenhance.latticeShift n)) ∧
      p + q / Real.sqrt (vecNormSq (y - z - AVenhance.latticeShift n)) ^ s ≤ Mx) :
    p + q / torusDist y z ^ s ≤ Mx := by
  have hρ0 : 0 < torusDist y z := lt_of_le_of_ne (torusDist_nonneg y z) (Ne.symm hρ)
  have hlim : Tendsto (fun δ : ℝ => q / (torusDist y z + δ) ^ s) (𝓝[>] 0)
      (𝓝 (q / torusDist y z ^ s)) := by
    have hc : ContinuousAt (fun δ : ℝ => q / (torusDist y z + δ) ^ s) 0 := by
      refine continuousAt_const.div ?_ ?_
      · exact ContinuousAt.rpow_const (continuousAt_const.add continuousAt_id) (Or.inr hs.le)
      · simpa using (Real.rpow_pos_of_pos hρ0 s).ne'
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), q / (torusDist y z + δ) ^ s ≤ Mx - p := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ' : (0 : ℝ) < δ := hδ
    have hlt : ⨅ n : Fin 2 → ℤ, Real.sqrt (vecNormSq (y - z - AVenhance.latticeShift n)) <
        torusDist y z + δ := by unfold torusDist; linarith
    obtain ⟨n, hn⟩ := exists_lt_of_ciInf_lt hlt
    obtain ⟨hn0, hn1⟩ := h n
    have h1 : Real.sqrt (vecNormSq (y - z - AVenhance.latticeShift n)) ^ s ≤
        (torusDist y z + δ) ^ s := Real.rpow_le_rpow hn0.le hn.le hs.le
    have h2 : 0 < Real.sqrt (vecNormSq (y - z - AVenhance.latticeShift n)) ^ s :=
      Real.rpow_pos_of_pos hn0 _
    calc q / (torusDist y z + δ) ^ s ≤ q / Real.sqrt (vecNormSq (y - z -
          AVenhance.latticeShift n)) ^ s := div_le_div_of_nonneg_left hq h2 h1
      _ ≤ Mx - p := by linarith
  have := le_of_tendsto hlim hev
  linarith

/-- Periodic form of `tube_regularity` with the torus distance. -/
theorem tube_regularity_periodic (hcamp : OcMicroscopicStatement) {α : ℝ} (hα₀ : 0 < α)
    (hα₁ : α < 1) {b : ℝ → Vec 2 → Vec 2} (hb : IsHolderDivFreeVelocity α b) {s a' : ℝ}
    (hs₀ : 0 < s) (hsa : s < a') (ha₁ : a' < 1) :
    ∃ c C : ℝ, 0 < c ∧ 0 ≤ C ∧
      ∀ κ : ℝ, 0 < κ → ∀ O : Set (ℝ × Vec 2), IsOpen O →
      (∀ p ∈ O, ∀ n : Fin 2 → ℤ, (p.1, p.2 + AVenhance.latticeShift n) ∈ O) →
      ∀ (w : ℝ × Vec 2 → ℝ) (Dw : ℝ × Vec 2 → Vec 2), IsLocalWeakSolution b κ O w Dw →
      (∀ τ y (n : Fin 2 → ℤ), w (τ, y + AVenhance.latticeShift n) = w (τ, y)) →
      ∀ A : ℝ, 0 ≤ A →
        (∀ᵐ τ ∂(volume : Measure ℝ), (∃ x, (τ, x) ∈ O) →
          IntegrableOn (fun y => w (τ, y) ^ 2) AVenhance.unitCube ∧
            ∫ y in AVenhance.unitCube, w (τ, y) ^ 2 ≤ A ^ 2) →
      ∀ r : ℝ, 0 < r → r ≤ 1 / 8 → r ≤ c * κ ^ (1 / (1 + α)) →
      ∀ (t : ℝ),
        (∀ x : Vec 2, ∀ X : ℝ → Vec 2, IsBackwardTrajectory b X t (r ^ 2 / κ) → X t = x →
          closedTube X t r κ ⊆ O) →
        ∃ W : Vec 2 → ℝ, AVenhance.IsZ2Periodic W ∧ Continuous W ∧
          (∀ x : Vec 2, Tendsto (fun τ => ∫ y in euclidBall x (r / 4), (w (τ, y) - W y) ^ 2)
            (𝓝[<] t ⊓ ae volume) (𝓝 0)) ∧
          ∀ x y z : Vec 2, torusDist y z ≠ 0 →
            |W x| + |W y - W z| / torusDist y z ^ s ≤ C * r ^ (-1 - s) * A := by
  have _ := hα₁
  obtain ⟨c, C₁, hc, hC₁, H⟩ := tube_regularity_aux hcamp hα₀ hb hs₀ hsa ha₁
  refine ⟨c, 2 * C₁, hc, by positivity, ?_⟩
  intro κ hκ O hO hOper w Dw hw hper A hA0 hT r hr hr8 hrc t hKt
  have _ := hOper
  -- the `L^∞L²` bound on discs
  have hA' : ∀ᵐ τ ∂(volume : Measure ℝ), ∀ y : Vec 2, euclidBall y r ⊆ timeSection O τ →
      ∫ x in euclidBall y r, w (τ, x) ^ 2 ≤ (2 * A) ^ 2 := by
    filter_upwards [hT] with τ hτ y hy
    obtain ⟨hint, hle⟩ := hτ ⟨y, hy (mem_euclidBall_self y hr)⟩
    have := ball_mass_le (f := fun x => w (τ, x) ^ 2) (fun n x => by rw [hper])
      (fun x => sq_nonneg _) hint hr (by linarith) y
    nlinarith
  obtain ⟨W, hW1, hW2, hW3, hW4⟩ := H κ hκ O hO w Dw hw (2 * A) (by positivity) r hr hr8 hrc hA' t
    univ (fun x _ => hKt x)
  -- uniform bound
  have hbd : ∀ u : Vec 2, |W u| ≤ C₁ * r ^ (-1 - s) * (2 * A) := by
    intro u
    have e0 : (basisVec (0 : Fin 2) : Vec 2) ≠ 0 := by
      intro h; have := congrFun h 0; simp [basisVec] at this
    have h := hW4 u (mem_univ _) u (mem_univ _) (u + basisVec 0) (mem_univ _) (by
      intro h; exact e0 (by simpa using h.symm))
    have : 0 ≤ |W u - W (u + basisVec 0)| / Real.sqrt (vecNormSq (u - (u + basisVec 0))) ^ s :=
      by positivity
    linarith
  -- periodicity
  have hperW : ∀ (n : Fin 2 → ℤ) (x : Vec 2), W (x + AVenhance.latticeShift n) = W x := by
    intro n x
    set a := AVenhance.latticeShift n with ha
    have hcontW : Continuous W := by
      have : (⋃ x ∈ (univ : Set (Vec 2)), euclidBall x (r / 4)) = univ := by
        ext y; simp only [mem_iUnion, mem_univ, exists_true_left, mem_univ, iff_true]
        exact ⟨y, mem_euclidBall_self y (by positivity)⟩
      rw [this] at hW1
      exact continuousOn_univ.1 hW1
    have hcont' : Continuous fun y => W (y + a) := hcontW.comp (continuous_id.add continuous_const)
    have key := traces_unique (t := t) (w := w) (W₁ := fun y => W (y + a)) (W₂ := W)
      (V := euclidBall x (r / 4)) (B₁ := euclidBall x (r / 4)) (B₂ := euclidBall x (r / 4))
      (M := C₁ * r ^ (-1 - s) * (2 * A)) (isOpen_euclidBall _ _)
      (volume_euclidBall_lt_top _ _) subset_rfl subset_rfl hcont'.continuousOn
      hcontW.continuousOn (fun y _ => hbd _) (fun y _ => hbd _)
      ?_ ?_ (hW3 x (mem_univ _)) (hW2 x (mem_univ _))
    · exact key (mem_euclidBall_self x (by positivity))
    · filter_upwards [hW3 (x + a) (mem_univ _)] with σ hσ
      have := integrableOn_ball_add a x (r / 4) hσ
      refine this.congr_fun (fun y _ => ?_) (External.Campanato.euclidBall_measurable x _)
      simp only [ha, hper]
    · have : ∀ σ : ℝ, ∫ y in euclidBall x (r / 4), (w (σ, y) - W (y + a)) ^ 2 =
          ∫ y in euclidBall (x + a) (r / 4), (w (σ, y) - W y) ^ 2 := by
        intro σ
        rw [← setIntegral_ball_add (fun y => (w (σ, y) - W y) ^ 2) a x (r / 4)]
        refine setIntegral_congr_fun (External.Campanato.euclidBall_measurable x _) fun y _ => ?_
        simp only [ha, hper]
      simp only [this]
      exact hW2 (x + a) (mem_univ _)
  have hcontW : Continuous W := by
    have : (⋃ x ∈ (univ : Set (Vec 2)), euclidBall x (r / 4)) = univ := by
      ext y; simp only [mem_iUnion, mem_univ, exists_true_left, iff_true]
      exact ⟨y, mem_euclidBall_self y (by positivity)⟩
    rw [this] at hW1
    exact continuousOn_univ.1 hW1
  refine ⟨W, fun n x => hperW n x, hcontW, fun x => hW2 x (mem_univ _), ?_⟩
  intro x y z hyz
  have hshift : ∀ n : Fin 2 → ℤ, 0 < Real.sqrt (vecNormSq (y - z - AVenhance.latticeShift n)) ∧
      |W x| + |W y - W z| / Real.sqrt (vecNormSq (y - z - AVenhance.latticeShift n)) ^ s ≤
        C₁ * r ^ (-1 - s) * (2 * A) := by
    intro n
    have hne : y ≠ z + AVenhance.latticeShift n := by
      intro h
      apply hyz
      have h0 : y - z - AVenhance.latticeShift n = 0 := by rw [h]; abel
      have : torusDist y z ≤ eNorm (y - z - AVenhance.latticeShift n) :=
        torusDist_le_shift y z n
      rw [h0] at this
      have he : eNorm (0 : Vec 2) = 0 := by simp [eNorm, vecNormSq, vecDot]
      rw [he] at this
      exact le_antisymm this (torusDist_nonneg y z)
    have hpos : 0 < Real.sqrt (vecNormSq (y - (z + AVenhance.latticeShift n))) :=
      Real.sqrt_pos.2 (vecNormSq_pos_of_ne hne)
    have e : y - (z + AVenhance.latticeShift n) = y - z - AVenhance.latticeShift n := by abel
    rw [e] at hpos
    refine ⟨hpos, ?_⟩
    have h := hW4 x (mem_univ _) y (mem_univ _) (z + AVenhance.latticeShift n) (mem_univ _) hne
    rw [e, hperW n z] at h
    exact h.trans_eq (by ring)
  have := torus_bound_of_shifts hs₀ (abs_nonneg (W y - W z)) hyz hshift
  calc |W x| + |W y - W z| / torusDist y z ^ s ≤ C₁ * r ^ (-1 - s) * (2 * A) := this
    _ = 2 * C₁ * r ^ (-1 - s) * A := by ring

end AVRegularity.Applications
end
end
end
end
