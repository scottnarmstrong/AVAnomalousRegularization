-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleReference.FluxFastDiscrepancy
public import AVRegularity.CycleReference.TransitionZero
import AVRegularity.CycleReference.CoreFlux
import AVRegularity.Velocity.ExistsLimitVelocity
import AVRegularity.CycleReference.MeanEnhancementScale
import AVenhance.Infra.Section4.Amnr.FieldTaylor
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Monotonicity.Lemmas

@[expose] public section

section
namespace AVRegularity.CycleReference

/-! Exact leading enhancement and the relative error of the prescribed scalar mean. -/

noncomputable def leadingMean (α q : ℝ) (Λ m : ℕ) (ν : ℝ) : ℝ :=
  ν + (9 / 80) * ocEpsilon q Λ m ^ (2 * (1 + α)) / ν

noncomputable def meanRelativeError (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ) (ν : ℝ) : ℝ :=
  (ocMeanFlux α q Λ ζ m ν - leadingMean α q Λ m ν) / leadingMean α q Λ m ν

theorem leadingMean_pos {α q : ℝ} {Λ m : ℕ} (hΛ : 1 ≤ Λ) {ν : ℝ} (hν : 0 < ν) :
    0 < leadingMean α q Λ m ν := by
  unfold leadingMean
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  positivity

theorem meanFlux_eq_leading_mul {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) {ν : ℝ} (hν : 0 < ν) :
    ocMeanFlux α q Λ ζ m ν =
      leadingMean α q Λ m ν * (1 + meanRelativeError α q Λ ζ m ν) := by
  unfold meanRelativeError
  have hpos := leadingMean_pos (α := α) (q := q) (m := m) hΛ hν
  field_simp
  ring

theorem meanRelativeError_bound {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ α q : ℝ, ∀ Λ m : ℕ, 1 ≤ Λ → ∀ ν : ℝ, 0 < ν →
      |meanRelativeError α q Λ ζ m ν| ≤ C *
        (ocEpsilon q Λ m ^ 2 / (ν * ocTau α q Λ m) +
          ocEpsilon q Λ (m - 1) ^ ocDelta α q) := by
  obtain ⟨C, hb⟩ := refFlux_mean_enhancement hζ
  let D := max C 0
  have hD : 0 ≤ D := le_max_right _ _
  refine ⟨D * (80 / 9), by positivity, ?_⟩
  intro α q Λ m hΛ ν hν
  let S := ocEpsilon q Λ m ^ (2 * (1 + α)) / ν
  let R := ocEpsilon q Λ m ^ 2 / (ν * ocTau α q Λ m) +
    ocEpsilon q Λ (m - 1) ^ ocDelta α q
  let F := leadingMean α q Λ m ν
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  have hS : 0 ≤ S := (div_pos (Real.rpow_pos_of_pos he _) hν).le
  have hτ := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
  have hE := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m - 1) hΛ
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hF : 0 < F := leadingMean_pos hΛ hν
  have hSF : S ≤ (80 / 9) * F := by
    have hf : F = ν + (9 / 80) * S := by dsimp [F, leadingMean, S]; ring
    rw [hf]
    linarith
  have herr : |ocMeanFlux α q Λ ζ m ν - F| ≤ D * S * R := by
    have h := hb α q Λ m hΛ ν hν
    have h' : |ocMeanFlux α q Λ ζ m ν - F| ≤ C * S * R := by
      convert h using 1
      congr 1
      dsimp [F, leadingMean, S]
      ring
    exact h'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left C 0) hS) hR)
  have hbound : D * S * R ≤ (D * (80 / 9)) * R * F := by
    have h := mul_le_mul_of_nonneg_left hSF (mul_nonneg hD hR)
    convert h using 1 <;> ring
  unfold meanRelativeError
  change |(ocMeanFlux α q Λ ζ m ν - F) / F| ≤ _
  rw [abs_div, abs_of_pos hF]
  exact (div_le_iff₀ hF).2 (herr.trans hbound)

end AVRegularity.CycleReference
end

section
open Homogenization
namespace AVRegularity.CycleReference

/-! Quantitative exponential tail of every time and space derivative array. -/

theorem pulseCorrector_quiet_array_bound {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (k : ℤ) (hk : Odd k) (a b : ℕ) (t : ℝ)
    (ht : ((k : ℝ) + 3 / 4) * ocTau α q Λ m ≤ t) (y : Vec 2) :
    derivArrayNorm (fun x => iteratedDeriv a
      (fun u => ocPulseCorrector α q Λ ζ m ν k u x) t) b y ≤
      (2 : ℝ) ^ (b + 1) *
        ((ocMu q Λ m ν) ^ a * (ocMu q Λ m ν)⁻¹ *
          (2 * Real.pi * ocEpsilon q Λ m ^ α) *
          (2 * Real.pi * (ocEpsilon q Λ m)⁻¹) ^ b) *
        Real.exp (-(ocMu q Λ m ν) * ocTau α q Λ m / 12) := by
  let μ := ocMu q Λ m ν
  let M := ocPulseMemory α q Λ ζ m ν k t
  have hμ : 0 < μ := ocMu_pos (q := q) (m := m) hΛ hν
  have hM : 0 ≤ M := (ocPulseMemory_range (α := α) (q := q) (m := m) hΛ hζ ν hν k t).1
  have hm := pulseMemory_quiet_tail hΛ hζ hν k t ht
  have heq : (fun x => iteratedDeriv a (fun u => ocPulseCorrector α q Λ ζ m ν k u x) t) =
      fun x => ((-μ) ^ a * (-M)) • ocShearVel α q Λ m k x := by
    funext x
    rw [pulseCorrector_quiet_time_derivative hΛ hζ ν k a t ht x, ocPulseCorrector, smul_smul]
  rw [heq]
  have hb := scaled_shear_array_bound (α := α) (q := q) (m := m) hΛ k hk ((-μ) ^ a * (-M)) b y
  rw [abs_mul, abs_pow, abs_neg, abs_of_pos hμ, abs_neg, abs_of_nonneg hM] at hb
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  have hc : 0 ≤ (2 : ℝ) ^ (b + 1) * μ ^ a * (2 * Real.pi * ocEpsilon q Λ m ^ α) *
      (2 * Real.pi * (ocEpsilon q Λ m)⁻¹) ^ b := by positivity
  have htbound := mul_le_mul_of_nonneg_left hm hc
  dsimp [μ, M] at hb htbound
  exact hb.trans (by convert htbound using 1 <;> ring)

end AVRegularity.CycleReference
end

section
open Homogenization MeasureTheory AVenhance AVenhance.Infra.Section5
open scoped Matrix
namespace AVRegularity.CycleReference

/-! The exact weak-gradient representative in a renewal chart. -/

theorem homeomorph_inverse_jacMatrix (X : Vec 2 ≃ₜ Vec 2)
    (hX : Differentiable ℝ (X : Vec 2 → Vec 2))
    (hY : Differentiable ℝ (X.symm : Vec 2 → Vec 2)) (y : Vec 2) :
    (jacMatrix (X.symm : Vec 2 → Vec 2) (X y))⁻¹ = jacMatrix (X : Vec 2 → Vec 2) y := by
  apply Matrix.inv_eq_right_inv
  have he := jacMatrix_comp y (hY (X y)) (hX y)
  have hf : (X.symm : Vec 2 → Vec 2) ∘ (X : Vec 2 → Vec 2) = id := by
    funext x
    exact X.symm_apply_apply x
  rw [hf, jacMatrix_identity] at he
  exact he.symm

theorem streamFlow_weakGradient {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (t s : ℝ) {u : Vec 2 → ℝ} {Du : Vec 2 → Vec 2}
    (hu : MemL2On Set.univ u) (hDu : GradMemL2On Set.univ Du)
    (hw : HasWeakGradientOn Set.univ u Du) :
    HasWeakGradientOn Set.univ (fun y => u (AVRegularity.streamFlow φ hφ t y s))
      (fun y => (jacMatrix (fun x => AVRegularity.streamFlow φ hφ t x s) y)ᵀ.mulVec
        (Du (AVRegularity.streamFlow φ hφ t y s))) := by
  let X := streamFlowHomeomorph hφ t s
  have hX : ContDiff ℝ (⊤ : ℕ∞) (X : Vec 2 → Vec 2) := streamFlow_spatial_smooth hφ t s
  have hY : ContDiff ℝ (⊤ : ℕ∞) (X.symm : Vec 2 → Vec 2) := streamFlow_spatial_smooth hφ s t
  have hd : ∀ x, (jacMatrix (X.symm : Vec 2 → Vec 2) x).det = 1 :=
    fun x => streamFlow_jacMatrix_det_one hφ s t x
  have hul : LocallyIntegrable u volume := by
    apply MemLp.locallyIntegrable _ (by norm_num : (1 : ENNReal) ≤ 2)
    simpa only [MemL2On, Measure.restrict_univ] using hu
  have hDul (i : Fin 2) : LocallyIntegrable (fun x => Du x i) volume := by
    apply MemLp.locallyIntegrable _ (by norm_num : (1 : ENNReal) ≤ 2)
    simpa only [MemL2On, Measure.restrict_univ] using hDu i
  have ht := weakGradient_homeomorph_piola X (streamFlow_measurePreserving hφ t s)
    hY hd hul hDul hw
  have hc (y : Vec 2) : rowCofactor (gradMatrix (X.symm : Vec 2 → Vec 2) (X y)) =
      jacMatrix (X : Vec 2 → Vec 2) y := by
    rw [rowCofactor_eq_jacMatrix_inverse (hY.differentiable (by simp)) _ (hd _)]
    exact homeomorph_inverse_jacMatrix X (hX.differentiable (by simp)) (hY.differentiable (by simp)) y
  simp_rw [hc] at ht
  exact ht

end AVRegularity.CycleReference
end

section
namespace AVRegularity.CycleReference

/-! Normalization of the actual reference diffusivity recurrence. -/

noncomputable def cycleAmplitude : ℝ := Real.sqrt (9 / 80)

noncomputable def normalizedDiffusivity (α q : ℝ) (Λ m : ℕ) (ν : ℝ) : ℝ :=
  ν / (cycleAmplitude * ocEpsilon q Λ m ^ ((1 + α) + ocGamma α q))

theorem cycleAmplitude_pos : 0 < cycleAmplitude := by
  unfold cycleAmplitude
  positivity

theorem cycleAmplitude_sq : cycleAmplitude ^ 2 = 9 / 80 := by
  unfold cycleAmplitude
  exact Real.sq_sqrt (by norm_num)

theorem normalizedDiffusivity_pos {α q : ℝ} {Λ m : ℕ} (hΛ : 1 ≤ Λ)
    {ν : ℝ} (hν : 0 < ν) : 0 < normalizedDiffusivity α q Λ m ν := by
  unfold normalizedDiffusivity
  exact div_pos hν (mul_pos cycleAmplitude_pos
    (Real.rpow_pos_of_pos (AVRegularity.Construction.Stream.ocEpsilon_pos hΛ) _))

theorem normalized_leading_mean {α q : ℝ} {Λ m : ℕ} (hq : 1 < q)
    (hΛ : 1 ≤ Λ) {ν : ℝ} (hν : 0 < ν) :
    normalizedDiffusivity α q Λ (m - 1) (leadingMean α q Λ m ν) =
      (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1) ^ q) ^ ((1 + α) - ocGamma α q) *
        (normalizedDiffusivity α q Λ m ν * ocEpsilon q Λ m ^ (2 * ocGamma α q) +
          (normalizedDiffusivity α q Λ m ν)⁻¹) := by
  have h := normalized_leading_update_algebra
    (e := ocEpsilon q Λ m) (E := ocEpsilon q Λ (m - 1))
    (A := cycleAmplitude) (ν := ν) (β := 1 + α) (γ := ocGamma α q) (q := q)
    (AVRegularity.Construction.Stream.ocEpsilon_pos hΛ)
    (AVRegularity.Construction.Stream.ocEpsilon_pos hΛ) cycleAmplitude_pos hν
    (enhancement_exponent_identity hq)
  rw [cycleAmplitude_sq] at h
  exact h

theorem normalized_mean_update {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hq : 1 < q) (hΛ : 1 ≤ Λ) {ν : ℝ} (hν : 0 < ν) :
    normalizedDiffusivity α q Λ (m - 1) (ocMeanFlux α q Λ ζ m ν) =
      (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1) ^ q) ^ ((1 + α) - ocGamma α q) *
        (normalizedDiffusivity α q Λ m ν * ocEpsilon q Λ m ^ (2 * ocGamma α q) +
          (normalizedDiffusivity α q Λ m ν)⁻¹) *
            (1 + meanRelativeError α q Λ ζ m ν) := by
  rw [← normalized_leading_mean hq hΛ hν, meanFlux_eq_leading_mul hΛ hν]
  unfold normalizedDiffusivity
  ring

end AVRegularity.CycleReference
end

section
open MeasureTheory
open scoped Matrix
namespace AVRegularity.CycleReference

/-! An anchored covariance bound, uniform in both endpoints. -/

theorem refFlux_covariance_primitive {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (α q : ℝ) (Λ m : ℕ), 1 ≤ Λ → ∀ ν : ℝ, 0 < ν →
    ∀ (s t : ℝ) (i j : Fin 2),
      |ocCovariance α q Λ ζ m ν (ocMeanFlux α q Λ ζ m ν) s t i j| ≤
      16 * ocHStar α q Λ m ν * ocTau α q Λ m +
      4 * ocHStar α q Λ m ν *
        (4 * ocTauPP α q Λ m * (K / (ocMu q Λ m ν * ocTau α q Λ m)) +
          16 * ocTauP α q Λ m) := by
  obtain ⟨K, hK, herr⟩ := refFlux_fast_cycle_discrepancy hζ
  refine ⟨K, hK, ?_⟩
  intro α q Λ m hΛ ν hν s t i j
  let H := ocHStar α q Λ m ν
  let h := ocTauPP α q Λ m
  let a := -h / 2
  let c := ν * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j
  let f := fastWeightedSquare ζ (ocTau α q Λ m) (fun k => ocPi k i j)
  let F := fun t => c + H * f t
  let J := fun t => ocRefFlux α q Λ ζ m ν t i j
  let B := ocMeanFlux α q Λ ζ m ν * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j
  have hH : 0 < H := ocHStar_pos hΛ hν
  have hh : 0 < h := AVRegularity.Construction.Stream.ocTauPP_pos hΛ
  obtain ⟨b, _hb, hm, hf⟩ := fast_entry_primitive (α := α) (q := q) (m := m) hΛ hζ i j
  have hfi (u v : ℝ) : IntervalIntegrable f volume u v :=
    fastWeightedSquare_intervalIntegrable hζ _ (fun k => ocPi_entry_range k i j) u v
  have hF (u v : ℝ) : IntervalIntegrable F volume u v :=
    intervalIntegrable_const.add ((hfi u v).const_mul H)
  have hJ (u v : ℝ) : IntervalIntegrable J volume u v :=
    refFlux_entry_intervalIntegrable hΛ hζ hν i j u v
  have hmeanJ : (∫ u in a..(a + 4 * h), J u - B) = 0 := by
    have he := refFlux_window_mean_entry (α := α) (q := q) (m := m) hΛ hζ hν a i j
    change (4 * h)⁻¹ * (∫ u in a..(a + 4 * h), J u) = B at he
    have hp : (4 * h) ≠ 0 := by positivity
    have he' := congrArg (fun x : ℝ => (4 * h) * x) he
    rw [← mul_assoc, mul_inv_cancel₀ hp, one_mul] at he'
    rw [intervalIntegral.integral_sub (hJ _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, he']
    simp only [smul_eq_mul]
    ring
  have hmeanF : (∫ u in a..(a + 4 * h), F u - (c + H * b)) = 0 := by
    have he : (fun u => F u - (c + H * b)) = fun u => H * (f u - b) := by
      funext u; dsimp [F]; ring
    rw [he, intervalIntegral.integral_const_mul]
    change H * (∫ u in a..(a + 4 * ocTauPP α q Λ m),
      fastWeightedSquare ζ (ocTau α q Λ m) (fun k => ocPi k i j) u - b) = 0
    rw [hm a, mul_zero]
  have hfast (v : ℝ) : |∫ u in a..v, F u - (c + H * b)| ≤
      8 * H * ocTau α q Λ m := by
    have he : (fun u => F u - (c + H * b)) = fun u => H * (f u - b) := by
      funext u; dsimp [F]; ring
    rw [he, intervalIntegral.integral_const_mul, abs_mul, abs_of_pos hH]
    have hhf := mul_le_mul_of_nonneg_left (hf a v) hH.le
    convert hhf using 1; ring
  have he := periodic_centered_bound_from_fast_approximation_at_base
    (a := a) (P := 4 * h) (B := B) (b := c + H * b) (by positivity)
    (refFlux_entry_periodic hΛ hζ hν i j) hJ hF hmeanJ hmeanF hfast
    (herr α q Λ m hΛ ν hν i j) s t
  change |∫ u in s..t, J u - B| ≤ _
  convert he using 1; dsimp [H]; ring

end AVRegularity.CycleReference
end

section
namespace AVRegularity.CycleReference

/-! Exact normalized relaxation-ratio identity. -/

theorem normalized_memory_algebra {e E A z ν τ β γ q t d : ℝ}
    (he : 0 < e) (hE : 0 < E) (hA : 0 < A) (hz : 0 < z) (hτ : 0 < τ)
    (hν : ν = A * z * e ^ (β + γ)) (hexp : q * (2 - (β + γ)) = t + d) :
    e ^ 2 / (ν * τ) = (e / E ^ q) ^ (2 - (β + γ)) / (A * z) *
      E ^ d * (E ^ t / τ) := by
  have her : e ^ (2 - (β + γ)) = e ^ 2 / e ^ (β + γ) := by
    rw [Real.rpow_sub he, Real.rpow_two]
  have hEpow : (E ^ q) ^ (2 - (β + γ)) = E ^ (t + d) := by
    rw [← Real.rpow_mul hE.le, hexp]
  have hratio : e ^ (2 - (β + γ)) =
      (e / E ^ q) ^ (2 - (β + γ)) * (E ^ t * E ^ d) := by
    rw [Real.div_rpow he.le (Real.rpow_pos_of_pos hE q).le, hEpow,
      ← Real.rpow_add hE, div_mul_cancel₀ _ (Real.rpow_pos_of_pos hE (t + d)).ne']
  calc
    _ = e ^ (2 - (β + γ)) / (A * z * τ) := by
      rw [her, hν]
      field_simp
    _ = _ := by rw [hratio]; ring

theorem normalized_memory_identity {α q : ℝ} {Λ m : ℕ} (hq : 1 < q)
    (hΛ : 1 ≤ Λ) {ν : ℝ} (hν : 0 < ν) :
    ocEpsilon q Λ m ^ 2 / (ν * ocTau α q Λ m) =
      (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1) ^ q) ^
        (2 - ((1 + α) + ocGamma α q)) /
          (cycleAmplitude * normalizedDiffusivity α q Λ m ν) *
            ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q) *
              (ocEpsilon q Λ (m - 1) ^ (2 - (1 + α) + 4 * ocDelta α q) /
                ocTau α q Λ m) := by
  apply normalized_memory_algebra
    (AVRegularity.Construction.Stream.ocEpsilon_pos hΛ)
    (AVRegularity.Construction.Stream.ocEpsilon_pos hΛ) cycleAmplitude_pos
    (normalizedDiffusivity_pos hΛ hν) (AVRegularity.Construction.Stream.ocTau_pos hΛ)
  · unfold normalizedDiffusivity
    have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
    have ha := cycleAmplitude_pos
    field_simp
  · have h := memory_exponent_identity (α := α) hq
    convert h using 1 <;> ring

/-! The separate terminal-band update puts the normalized recurrence in a fixed interval. -/

theorem normalized_pulse_factor_algebra {e A ν β γ : ℝ}
    (he : 0 < e) (hA : 0 < A) :
    ν / (A * e ^ (β + γ)) * e ^ (2 * γ) = ν / e ^ (β - γ) / A := by
  have hid : e ^ (β - γ) * e ^ (2 * γ) = e ^ (β + γ) := by
    rw [← Real.rpow_add he]
    congr 1
    ring
  have hp := Real.rpow_pos_of_pos he (β + γ)
  have hp' := Real.rpow_pos_of_pos he (β - γ)
  field_simp
  rw [← hid]
  ring_nf

theorem terminal_normalized_bounds {α q : ℝ} {Λ m : ℕ} {ν : ℝ}
    (hq : 1 < q) (hΛ : 128 ≤ Λ) (hγ : 0 ≤ ocGamma α q)
    (hband : ν ∈ ocBand α q Λ m) :
    (normalizedDiffusivity α q Λ m ν)⁻¹ ≤ 2 * cycleAmplitude ∧
      1 / (2 * cycleAmplitude) ≤ normalizedDiffusivity α q Λ m ν *
        ocEpsilon q Λ m ^ (2 * ocGamma α q) ∧
      normalizedDiffusivity α q Λ m ν * ocEpsilon q Λ m ^ (2 * ocGamma α q) ≤
        2 / cycleAmplitude := by
  have he := AVRegularity.Scales.epsilon_basic (m := m) hq hΛ
  have ha := cycleAmplitude_pos
  have hp := Real.rpow_pos_of_pos he.1 ((1 + α) - ocGamma α q)
  have hl : ocEpsilon q Λ m ^ ((1 + α) - ocGamma α q) / 2 ≤ ν := hband.1
  have hu : ν ≤ 2 * ocEpsilon q Λ m ^ ((1 + α) - ocGamma α q) := hband.2
  have hν : 0 < ν := lt_of_lt_of_le (div_pos hp (by norm_num)) hl
  have hfactor : normalizedDiffusivity α q Λ m ν * ocEpsilon q Λ m ^ (2 * ocGamma α q) =
      (ν / ocEpsilon q Λ m ^ ((1 + α) - ocGamma α q)) / cycleAmplitude :=
    normalized_pulse_factor_algebra he.1 ha
  have hdl : 1 / 2 ≤ ν / ocEpsilon q Λ m ^ ((1 + α) - ocGamma α q) := by
    apply (le_div_iff₀ hp).2
    linarith
  have hdu : ν / ocEpsilon q Λ m ^ ((1 + α) - ocGamma α q) ≤ 2 :=
    (div_le_iff₀ hp).2 hu
  have hlow : 1 / (2 * cycleAmplitude) ≤ normalizedDiffusivity α q Λ m ν *
      ocEpsilon q Λ m ^ (2 * ocGamma α q) := by
    rw [hfactor]
    convert div_le_div_of_nonneg_right hdl ha.le using 1; ring
  have hup : normalizedDiffusivity α q Λ m ν * ocEpsilon q Λ m ^ (2 * ocGamma α q) ≤
      2 / cycleAmplitude := by
    rw [hfactor]
    exact div_le_div_of_nonneg_right hdu ha.le
  have hz := normalizedDiffusivity_pos (α := α) (q := q) (Λ := Λ) (m := m) (by omega) hν
  have ht : ocEpsilon q Λ m ^ (2 * ocGamma α q) ≤ 1 :=
    Real.rpow_le_one he.1.le he.2.1 (by linarith)
  have hzinv : (normalizedDiffusivity α q Λ m ν)⁻¹ ≤ 2 * cycleAmplitude := by
    have hsmall : 1 / (2 * cycleAmplitude) ≤ normalizedDiffusivity α q Λ m ν :=
      hlow.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left ht hz.le)
    have h := (inv_le_inv₀ hz (div_pos (by norm_num) (mul_pos (by norm_num) ha))).2 hsmall
    simpa only [one_div, inv_inv] using h
  exact ⟨hzinv, hlow, hup⟩

theorem terminal_normalized_leading_size {α q : ℝ} {Λ m : ℕ} {ν : ℝ}
    (hq : 1 < q) (hΛ : 128 ≤ Λ) (hγ : 0 ≤ ocGamma α q)
    (hband : ν ∈ ocBand α q Λ m) :
    reciprocalSize (normalizedDiffusivity α q Λ m ν *
      ocEpsilon q Λ m ^ (2 * ocGamma α q) +
        (normalizedDiffusivity α q Λ m ν)⁻¹) ≤ 2 / cycleAmplitude + 4 * cycleAmplitude := by
  obtain ⟨hi, hl, hu⟩ := terminal_normalized_bounds hq hΛ hγ hband
  have ha := cycleAmplitude_pos
  have hν : 0 < ν := lt_of_lt_of_le
    (div_pos (Real.rpow_pos_of_pos (AVRegularity.Scales.epsilon_basic hq hΛ).1 _) (by norm_num))
    hband.1
  have hz := normalizedDiffusivity_pos (α := α) (q := q) (Λ := Λ) (m := m) (by omega) hν
  have hinv : 0 < (normalizedDiffusivity α q Λ m ν)⁻¹ := inv_pos.mpr hz
  have hbase : 0 < normalizedDiffusivity α q Λ m ν *
      ocEpsilon q Λ m ^ (2 * ocGamma α q) + (normalizedDiffusivity α q Λ m ν)⁻¹ :=
    add_pos_of_nonneg_of_pos (mul_nonneg hz.le (Real.rpow_nonneg
      (AVRegularity.Scales.epsilon_basic hq hΛ).1.le _)) hinv
  apply max_le
  · linarith
  · have hb : 1 / (2 * cycleAmplitude) ≤ normalizedDiffusivity α q Λ m ν *
        ocEpsilon q Λ m ^ (2 * ocGamma α q) + (normalizedDiffusivity α q Λ m ν)⁻¹ := by
      linarith
    have h := (inv_le_inv₀ hbase (div_pos (by norm_num) (mul_pos (by norm_num) ha))).2 hb
    have hb' : (normalizedDiffusivity α q Λ m ν * ocEpsilon q Λ m ^ (2 * ocGamma α q) +
        (normalizedDiffusivity α q Λ m ν)⁻¹)⁻¹ ≤ 2 * cycleAmplitude := by
      simpa only [one_div, inv_inv] using h
    have hp : 0 < 2 / cycleAmplitude := by positivity
    exact hb'.trans (by linarith)

/-! Construction-uniform normalized relaxation bound. -/

theorem normalized_memory_upper_bound {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) :
    ∃ K : ℝ, 0 < K ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ m : ℕ, Λ₀ ≤ Λ → 2 ≤ m →
      ∀ ν : ℝ, 0 < ν → ocEpsilon q Λ m ^ 2 / (ν * ocTau α q Λ m) ≤
        K * (normalizedDiffusivity α q Λ m ν)⁻¹ *
          ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q) := by
  let p := 2 - ((1 + α) + ocGamma α q)
  obtain ⟨K, hK, hb⟩ := rpow_positive_interval_bounds p
  obtain ⟨_, _, Λ₀, hΛ₀, hr⟩ := epsilon_q_ratio_power_error hq.1 p
  let c : ℝ := (2 : ℝ) ^ (-26 : ℤ) / 81
  have hc : 0 < c := by dsimp [c]; positivity
  have hA := cycleAmplitude_pos
  have hKpos : 0 < K := by linarith
  refine ⟨K / cycleAmplitude * c⁻¹, by positivity, Λ₀, hΛ₀, ?_⟩
  intro Λ m hΛ hm ν hν
  have h128 : 128 ≤ Λ := hΛ₀.trans hΛ
  have hΛ1 : 1 ≤ Λ := by omega
  have hE := AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 h128
  have hz := normalizedDiffusivity_pos (α := α) (q := q) (m := m) hΛ1 hν
  have hτ := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ1
  have hδ := (AVRegularity.Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq).2.1
  have hp : 0 ≤ 2 - (1 + α) + 2 * ocDelta α q := by linarith
  have ht := (ocTau_power_bounds hE.1 hE.2.1 hδ.le hp).1
  let T := ocEpsilon q Λ (m - 1) ^ (2 - (1 + α) + 4 * ocDelta α q) / ocTau α q Λ m
  have hT : T ≤ c⁻¹ := by
    apply (div_le_iff₀ hτ).2
    have h := mul_le_mul_of_nonneg_left ht (inv_pos.mpr hc).le
    have heq : c⁻¹ * (c * ocEpsilon q Λ (m - 1) ^
        (2 - (1 + α) + 4 * ocDelta α q)) =
        ocEpsilon q Λ (m - 1) ^ (2 - (1 + α) + 4 * ocDelta α q) := by
      rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
    rw [heq] at h
    exact h
  have hEpos := hE.1
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hratio := hr Λ m hΛ hm
  have hpow := (hb _ hratio.1 hratio.2.1).2
  have hden : 0 < cycleAmplitude * normalizedDiffusivity α q Λ m ν := mul_pos cycleAmplitude_pos hz
  have hD : 0 ≤ ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q) := Real.rpow_nonneg hE.1.le _
  rw [normalized_memory_identity hq.1 hΛ1 hν]
  change _ * _ * T ≤ _
  calc
    _ ≤ (K / (cycleAmplitude * normalizedDiffusivity α q Λ m ν) *
        ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q)) * c⁻¹ := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hpow hden.le) hD) hT hT0 (by positivity)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv]; ring

/-! Relative recurrence errors in normalized diffusivity variables. -/

theorem normalized_relative_error_bound {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ m : ℕ, Λ₀ ≤ Λ → 2 ≤ m →
      ∀ ν : ℝ, 0 < ν → |meanRelativeError α q Λ ζ m ν| ≤ C *
        ((normalizedDiffusivity α q Λ m ν)⁻¹ *
          ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q) +
            ocEpsilon q Λ (m - 1) ^ ocDelta α q) := by
  obtain ⟨K, hK, Λ₀, hΛ₀, hm⟩ := normalized_memory_upper_bound hα0 hα1 hs0 hs1 hq
  obtain ⟨C, hC, he⟩ := meanRelativeError_bound hζ
  refine ⟨C * (K + 1), by positivity, Λ₀, hΛ₀, ?_⟩
  intro Λ m hΛ hm2 ν hν
  have h128 := hΛ₀.trans hΛ
  have hΛ1 : 1 ≤ Λ := by omega
  let X := (normalizedDiffusivity α q Λ m ν)⁻¹ *
    ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q)
  let Y := ocEpsilon q Λ (m - 1) ^ ocDelta α q
  have hz := normalizedDiffusivity_pos (α := α) (q := q) (m := m) hΛ1 hν
  have hE := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m - 1) hΛ1
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hY : 0 ≤ Y := by dsimp [Y]; positivity
  have hR := hm Λ m hΛ hm2 ν hν
  apply (he α q Λ m hΛ1 ν hν).trans
  have hR' : ocEpsilon q Λ m ^ 2 / (ν * ocTau α q Λ m) ≤ K * X := by
    simpa only [X, mul_assoc] using hR
  apply le_trans (mul_le_mul_of_nonneg_left (add_le_add hR' (le_refl Y)) hC)
  change C * (K * X + Y) ≤ (C * (K + 1)) * (X + Y)
  have hXY : K * X + Y ≤ (K + 1) * (X + Y) := by nlinarith
  convert mul_le_mul_of_nonneg_left hXY hC using 1; ring

theorem relative_error_under_inverse_bound {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    {ν C R : ℝ} (hC : 0 ≤ C) (hν : 0 < ν) (hΛ : 1 ≤ Λ)
    (hE1 : ocEpsilon q Λ (m - 1) ≤ 1) (hδ : 0 ≤ ocDelta α q)
    (hzinv : (normalizedDiffusivity α q Λ m ν)⁻¹ ≤ R)
    (herr : |meanRelativeError α q Λ ζ m ν| ≤ C *
      ((normalizedDiffusivity α q Λ m ν)⁻¹ *
        ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q) +
          ocEpsilon q Λ (m - 1) ^ ocDelta α q)) :
    |meanRelativeError α q Λ ζ m ν| ≤ C * (R + 1) *
      ocEpsilon q Λ (m - 1) ^ ocDelta α q := by
  have hE := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m - 1) hΛ
  have hz := normalizedDiffusivity_pos (α := α) (q := q) (m := m) hΛ hν
  have hpow : ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q) ≤
      ocEpsilon q Λ (m - 1) ^ ocDelta α q :=
    Real.rpow_le_rpow_of_exponent_ge hE hE1 (by linarith)
  have hprod := (mul_le_mul_of_nonneg_left hpow (inv_pos.mpr hz).le).trans
    (mul_le_mul_of_nonneg_right hzinv (Real.rpow_pos_of_pos hE _).le)
  apply herr.trans
  have h := mul_le_mul_of_nonneg_left
    (add_le_add hprod (le_refl (ocEpsilon q Λ (m - 1) ^ ocDelta α q))) hC
  convert h using 1; ring

/-! Conditional one-step bootstrap estimate, with its scale-smallness conditions explicit. -/

theorem normalized_step_of_small_errors {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Cr Ce : ℝ, 0 ≤ Cr ∧ 0 ≤ Ce ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧
      ∀ Λ m : ℕ, Λ₀ ≤ Λ → 2 ≤ m → ∀ ν R : ℝ, 0 < ν →
        reciprocalSize (normalizedDiffusivity α q Λ m ν) ≤ R →
        Cr * ocEpsilon q Λ (m - 1) ≤ 1 / 2 →
        Ce * (R + 1) * ocEpsilon q Λ (m - 1) ^ ocDelta α q ≤ 1 / 2 →
        reciprocalSize (normalizedDiffusivity α q Λ (m - 1) (ocMeanFlux α q Λ ζ m ν)) ≤
          reciprocalSize (normalizedDiffusivity α q Λ m ν) *
            (1 + 16 * (Cr * ocEpsilon q Λ (m - 1) +
              ocEpsilon q Λ m ^ (2 * ocGamma α q) +
                Ce * (R + 1) * ocEpsilon q Λ (m - 1) ^ ocDelta α q)) := by
  obtain ⟨Ce, hCe, Le, hLe, he⟩ := normalized_relative_error_bound hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Cr, hCr, Lr, hLr, hr⟩ := epsilon_q_ratio_power_error hq.1 ((1 + α) - ocGamma α q)
  refine ⟨Cr, Ce, hCr, hCe, max Le Lr, hLe.trans (le_max_left _ _), ?_⟩
  intro Λ m hΛ hm ν R hν hsize hsmallr hsmalle
  have hΛe : Le ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛr : Lr ≤ Λ := (le_max_right _ _).trans hΛ
  have h128 : 128 ≤ Λ := hLe.trans hΛe
  have hΛ1 : 1 ≤ Λ := by omega
  have hE := AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 h128
  have hmE := AVRegularity.Scales.epsilon_basic (m := m) hq.1 h128
  have hz := normalizedDiffusivity_pos (α := α) (q := q) (m := m) hΛ1 hν
  have hR : 0 ≤ R := (reciprocalSize_nonneg hz).trans hsize
  have hparams := AVRegularity.Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq
  have herr := relative_error_under_inverse_bound hCe hν hΛ1 hE.2.1 hparams.2.1.le
    ((le_max_right _ _).trans hsize) (he Λ m hΛe hm ν hν)
  have ht : 0 ≤ ocEpsilon q Λ m ^ (2 * ocGamma α q) := Real.rpow_nonneg hmE.1.le _
  have ht1 : ocEpsilon q Λ m ^ (2 * ocGamma α q) ≤ 1 :=
    Real.rpow_le_one hmE.1.le hmE.2.1 (by linarith [hparams.1])
  have hre : 0 ≤ Cr * ocEpsilon q Λ (m - 1) := mul_nonneg hCr hE.1.le
  have hee : 0 ≤ Ce * (R + 1) * ocEpsilon q Λ (m - 1) ^ ocDelta α q := by
    exact mul_nonneg (mul_nonneg hCe (by linarith)) (Real.rpow_nonneg hE.1.le _)
  have hrec := reciprocalSize_perturbed_update_additive hz ht ht1 hre hsmallr hee hsmalle
    (hr Λ m hΛr hm).2.2
    (show |(1 + meanRelativeError α q Λ ζ m ν) - 1| ≤
      Ce * (R + 1) * ocEpsilon q Λ (m - 1) ^ ocDelta α q by
        simpa only [add_sub_cancel_left] using herr)
  rw [normalized_mean_update hq.1 hΛ1 hν]
  simpa only [mul_comm (normalizedDiffusivity α q Λ m ν)
    (ocEpsilon q Λ m ^ (2 * ocGamma α q))] using hrec

/-! Uniform starting bound after the separate terminal-band enhancement. -/

theorem terminal_normalized_start {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ B : ℝ, 0 < B ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ m : ℕ, Λ₀ ≤ Λ → 2 ≤ m →
      ∀ ν : ℝ, ν ∈ ocBand α q Λ m →
        reciprocalSize (normalizedDiffusivity α q Λ (m - 1) (ocMeanFlux α q Λ ζ m ν)) ≤ B := by
  have hparams := AVRegularity.Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq
  have hγ := hparams.1
  have hδ := hparams.2.1
  obtain ⟨C, hC, Lerr, herr128, herr⟩ := normalized_relative_error_bound hα0 hα1 hs0 hs1 hq hζ
  let p := (1 + α) - ocGamma α q
  obtain ⟨Kr, hKr, hrpow⟩ := rpow_positive_interval_bounds p
  obtain ⟨_, _, Lratio, hratio128, hratio⟩ := epsilon_q_ratio_power_error hq.1 p
  have ha := cycleAmplitude_pos
  let D := C * (2 * cycleAmplitude + 1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hη : 0 < 1 / (2 * (D + 1)) := by positivity
  obtain ⟨Lsmall, hsmall128, hsmall⟩ := exists_small_scale_error_budget hq.1 hδ hη
  let R := 2 / cycleAmplitude + 4 * cycleAmplitude
  have hR : 0 < R := by dsimp [R]; positivity
  have hKrpos : 0 < Kr := by linarith
  refine ⟨Kr * R * 2, by positivity, max Lerr (max Lratio Lsmall), ?_, ?_⟩
  · exact herr128.trans (le_max_left _ _)
  intro Λ m hΛ hm ν hband
  have hΛerr : Lerr ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛratio : Lratio ≤ Λ := (le_max_left _ _).trans ((le_max_right _ _).trans hΛ)
  have hΛsmall : Lsmall ≤ Λ := (le_max_right _ _).trans ((le_max_right _ _).trans hΛ)
  have h128 : 128 ≤ Λ := herr128.trans hΛerr
  have hΛ1 : 1 ≤ Λ := by omega
  have he := AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 h128
  have hν : 0 < ν := lt_of_lt_of_le
    (div_pos (Real.rpow_pos_of_pos (AVRegularity.Scales.epsilon_basic hq.1 h128).1 _) (by norm_num))
    hband.1
  have hzinv := (terminal_normalized_bounds hq.1 h128 hγ.le hband).1
  have heta := relative_error_under_inverse_bound hC hν hΛ1 he.2.1 hδ.le hzinv
    (herr Λ m hΛerr hm ν hν)
  have hEsmall : ocEpsilon q Λ (m - 1) ^ ocDelta α q ≤ 1 / (2 * (D + 1)) :=
    (epsilon_power_le_tail hq.1 hδ h128 (by omega)).trans (hsmall Λ hΛsmall).2
  have hetaHalf : |meanRelativeError α q Λ ζ m ν| ≤ 1 / 2 := by
    apply heta.trans
    change D * ocEpsilon q Λ (m - 1) ^ ocDelta α q ≤ 1 / 2
    apply (mul_le_mul_of_nonneg_left hEsmall hD).trans
    have hDp : 0 < 2 * (D + 1) := by positivity
    rw [one_div, ← div_eq_mul_inv]
    apply (div_le_iff₀ hDp).2
    linarith
  let z := normalizedDiffusivity α q Λ m ν
  let t := ocEpsilon q Λ m ^ (2 * ocGamma α q)
  let r := (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1) ^ q) ^ p
  let u := 1 + meanRelativeError α q Λ ζ m ν
  have hz : 0 < z := normalizedDiffusivity_pos hΛ1 hν
  have ht : 0 ≤ t := Real.rpow_nonneg (AVRegularity.Scales.epsilon_basic hq.1 h128).1.le _
  have hv : 0 < z * t + z⁻¹ := add_pos_of_nonneg_of_pos (mul_nonneg hz.le ht) (inv_pos.mpr hz)
  have hqrange := hratio Λ m hΛratio hm
  have hr : 0 < r := Real.rpow_pos_of_pos (by linarith [hqrange.1]) p
  have hrbounds := hrpow _ hqrange.1 hqrange.2.1
  have hrs : reciprocalSize r ≤ Kr := reciprocalSize_of_bounds hr hKrpos hrbounds.1 hrbounds.2
  have hvs : reciprocalSize (z * t + z⁻¹) ≤ R := terminal_normalized_leading_size hq.1 h128 hγ.le hband
  have hup : 0 < u := by dsimp [u]; linarith [(abs_le.mp hetaHalf).1]
  have hus : reciprocalSize u ≤ 2 := by
    have h := reciprocalSize_near_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1 / 2)
      (show |u - 1| ≤ 1 / 2 by simpa only [u, add_sub_cancel_left] using hetaHalf)
    norm_num at h
    exact h
  rw [normalized_mean_update hq.1 hΛ1 hν]
  change reciprocalSize (r * (z * t + z⁻¹) * u) ≤ Kr * R * 2
  apply (reciprocalSize_mul_le (mul_pos hr hv) hup).trans
  have hrv : reciprocalSize (r * (z * t + z⁻¹)) ≤ Kr * R :=
    (reciprocalSize_mul_le hr hv).trans
      (mul_le_mul hrs hvs (reciprocalSize_nonneg hv) hKrpos.le)
  exact mul_le_mul hrv hus (reciprocalSize_nonneg hup) (mul_pos hKrpos hR).le

end AVRegularity.CycleReference
end

section
open Homogenization AVenhance
open scoped Matrix
namespace AVRegularity.CycleReference

/-! Joint smoothness of the inverse-Jacobian vector pullback. -/

theorem chartJac_entry_smooth {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => chartJac hφ s p.1 p.2 i j) := by
  have hG : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 =>
      AVRegularity.streamFlow φ hφ p.1 p.2 s) :=
    (streamFlow_joint_smooth hφ).comp
      (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const))
  have hd := AVRegularity.Velocity.Port.Section2FlowRegularityCore.partialFDeriv_joint_contDiff _ hG
  exact (contDiff_apply ℝ ℝ i).comp (hd.clm_apply contDiff_const)

theorem chartJac_inverse_entry_smooth {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) (i j : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => (chartJac hφ s p.1 p.2)⁻¹ i j) := by
  have hd (p : ℝ × Vec 2) : (chartJac hφ s p.1 p.2).det = 1 :=
    streamFlow_jacMatrix_det_one hφ p.1 s p.2
  fin_cases i <;> fin_cases j
  · simpa [Matrix.inv_def, hd, Matrix.adjugate_fin_two] using chartJac_entry_smooth hφ s 1 1
  · simpa [Matrix.inv_def, hd, Matrix.adjugate_fin_two] using (chartJac_entry_smooth hφ s 0 1).neg
  · simpa [Matrix.inv_def, hd, Matrix.adjugate_fin_two] using (chartJac_entry_smooth hφ s 1 0).neg
  · simpa [Matrix.inv_def, hd, Matrix.adjugate_fin_two] using chartJac_entry_smooth hφ s 0 0

theorem chartVector_joint_smooth {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) {B : ℝ → Vec 2 → Vec 2}
    (hB : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => B p.1 p.2)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => chartVector hφ s B p.1 p.2) := by
  have hp : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => chartPull hφ s B p.1 p.2) :=
    hB.comp (contDiff_fst.prodMk ((streamFlow_joint_smooth hφ).comp
      (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const))))
  apply contDiff_pi.mpr
  intro i
  have he : (fun p : ℝ × Vec 2 => chartVector hφ s B p.1 p.2 i) =
      (fun p => (chartJac hφ s p.1 p.2)⁻¹ i 0 * chartPull hφ s B p.1 p.2 0 +
        (chartJac hφ s p.1 p.2)⁻¹ i 1 * chartPull hφ s B p.1 p.2 1) := by
    funext p
    simp [chartVector, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [he]
  exact ((chartJac_inverse_entry_smooth hφ s i 0).mul ((contDiff_apply ℝ ℝ 0).comp hp)).add
    ((chartJac_inverse_entry_smooth hφ s i 1).mul ((contDiff_apply ℝ ℝ 1).comp hp))

end AVRegularity.CycleReference
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleReference

/-! Quadratic remainder obtained from the actual second derivative. -/

theorem second_derivative_operator_bound {f : Vec 2 → Vec 2}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {R B : ℝ} (hR : 0 < R) (hB : 0 ≤ B)
    (hb : ∀ n i a, barNorm n R
      (fun x => jacMatrix f x i a - (1 : Matrix (Fin 2) (Fin 2) ℝ) i a) ≤ ENNReal.ofReal B)
    (x : Vec 2) : ‖iteratedFDeriv ℝ 2 f x‖ ≤ 4 * (B * R) := by
  let H := fderiv ℝ (fderiv ℝ f) x
  have he (a b : Fin 2) : ‖H (basisVec a) (basisVec b)‖ ≤ B * R := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hB hR.le)).2
    intro i
    have hp := jacMatrix_partial_bound hf hR hB hb 1 (by omega)
      (fun _ => a) x i b
    have hv : Fin.snoc (fun _ : Fin 1 => basisVec a) (basisVec b) =
        (fun j : Fin 2 => if j = 0 then basisVec a else basisVec b) := by
      ext j k
      fin_cases j <;> simp [Fin.snoc]
    rw [hv, iteratedFDeriv_two_apply] at hp
    have hd : B * R / (4 : ℝ) ≤ B * R := div_le_self (by positivity) (by norm_num)
    norm_num only [Nat.factorial_one, Nat.cast_one, pow_one, mul_one] at hp
    change |H (basisVec a) (basisVec b) i| ≤ B * R / 4 at hp
    simpa only [Real.norm_eq_abs] using hp.trans hd

  have hr (a : Fin 2) : ‖H (basisVec a)‖ ≤ 2 * (B * R) :=
    timeIncrement_clm_norm_le_two_basis (by positivity) (he a 0) (he a 1)
  have hH : ‖H‖ ≤ 2 * (2 * (B * R)) :=
    timeIncrement_clm_norm_le_two_basis (by positivity) (hr 0) (hr 1)
  rw [← norm_iteratedFDeriv_one (fderiv ℝ f), norm_iteratedFDeriv_fderiv] at hH
  simpa only [show 2 * (2 * (B * R)) = 4 * (B * R) by ring] using hH

theorem quadratic_euclidean_remainder_from_bar {f : Vec 2 → Vec 2}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {R B : ℝ} (hR : 0 < R) (hB : 0 ≤ B)
    (hb : ∀ n i a, barNorm n R
      (fun x => jacMatrix f x i a - (1 : Matrix (Fin 2) (Fin 2) ℝ) i a) ≤ ENNReal.ofReal B)
    (x y : Vec 2) :
    Real.sqrt (vecNormSq (f (x + y) - f x - (jacMatrix f x).mulVec y)) ≤
      8 * (B * R) * vecNormSq y := by
  have ht := AVenhance.Infra.Section4.amnr_field_quadratic_remainder hf
    (by positivity : 0 ≤ 4 * (B * R)) (second_derivative_operator_bound hf hR hB hb) x y
  have hm : (jacMatrix f x).mulVec y = fderiv ℝ f x y := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, jacMatrix]
    exact (AVRegularity.Velocity.Port.Section2FlowIdentities.linearMap_apply_two _ _ _).symm
  rw [hm]
  have hv := finite_euclidean_bound
    (norm_nonneg (f (x + y) - f x - fderiv ℝ f x y))
    (fun i : Fin 2 => (show |(f (x + y) - f x - fderiv ℝ f x y) i| ≤
        ‖f (x + y) - f x - fderiv ℝ f x y‖ from by
      simpa only [Real.norm_eq_abs] using
        (norm_le_pi_norm (f (x + y) - f x - fderiv ℝ f x y) i)))
  have hn : ‖y‖ * ‖y‖ ≤ vecNormSq y := by
    have h := AVRegularity.Velocity.velocity_norm_le_vecEuclidean y
    have hs := (sq_le_sq₀ (norm_nonneg y) (Real.sqrt_nonneg _)).2 h
    simpa only [pow_two, Real.mul_self_sqrt (vecNormSq_nonneg y)] using hs
  calc
    _ ≤ 2 * ‖f (x + y) - f x - fderiv ℝ f x y‖ := by
      simpa only [vecNormSq, vecDot, pow_two, Fintype.card_fin, Nat.cast_ofNat] using hv
    _ ≤ 2 * (4 * (B * R) * ‖y‖ * ‖y‖) := mul_le_mul_of_nonneg_left ht (by norm_num)
    _ = 8 * (B * R) * (‖y‖ * ‖y‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hn (by positivity)

/-! Uniform constants for the Euclidean transition estimates. -/

theorem transition_taylor_bounds_of_bar {f : Vec 2 → Vec 2}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {g E : ℝ} (hg : 0 ≤ g) (hE : 0 < E)
    (hb : ∀ n i a, barNorm n (2 ^ 11 * E⁻¹)
      (fun x => jacMatrix f x i a - (1 : Matrix (Fin 2) (Fin 2) ℝ) i a) ≤
      ENNReal.ofReal (2 ^ 23 * g)) :
    (∀ x, Real.sqrt (∑ i : Fin 2, ∑ a : Fin 2,
      (jacMatrix f x i a - (1 : Matrix (Fin 2) (Fin 2) ℝ) i a) ^ 2) ≤ 2 ^ 40 * g) ∧
    (∀ j : ℕ, 2 ≤ j → ∀ x, derivArrayNorm f j x ≤
      2 ^ 40 * g * (Nat.factorial (j - 1) : ℝ) * (2 ^ 40 / E) ^ (j - 1)) ∧
    (∀ x y, Real.sqrt (vecNormSq (f (x + y) - f x - (jacMatrix f x).mulVec y)) ≤
      2 ^ 40 * g * vecNormSq y / E) := by
  have hR : 0 < (2 : ℝ) ^ 11 * E⁻¹ := by positivity
  have hB : 0 ≤ (2 : ℝ) ^ 23 * g := by positivity
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have ht := finite_euclidean_bound hB (fun p : Fin 2 × Fin 2 =>
      jacMatrix_displacement_entry_bound hf hR hB hb x p.1 p.2)
    have hs : Real.sqrt (∑ i : Fin 2, ∑ a : Fin 2,
        (jacMatrix f x i a - (1 : Matrix (Fin 2) (Fin 2) ℝ) i a) ^ 2) ≤
        4 * (2 ^ 23 * g) := by
      simpa [Fintype.sum_prod_type] using ht
    have hc : 4 * ((2 : ℝ) ^ 23 * g) ≤ 2 ^ 40 * g := by
      norm_num only [Nat.reducePow]
      linarith only [hg]
    exact hs.trans hc
  · intro j hj x
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    have hn : 1 ≤ n := by omega
    have ht := derivArrayNorm_from_jacobian_bar hf hR hB hb n hn x
    have he : (2 : ℝ) ^ (n + 2) * (2 ^ 23 * g * (n.factorial : ℝ) *
        (2 ^ 11 * E⁻¹) ^ n) =
        (2 ^ 25 * g * (n.factorial : ℝ)) * (2 ^ 12 / E) ^ n := by
      calc
        _ = (2 ^ 25 * g * (n.factorial : ℝ)) *
            (2 ^ n * (2 ^ 11 * E⁻¹) ^ n) := by
          rw [pow_add]
          norm_num only [Nat.reducePow]
          ring
        _ = _ := by
          rw [← mul_pow]
          congr 2
          norm_num [div_eq_mul_inv]
          ring
    rw [he] at ht
    change derivArrayNorm f (n + 1) x ≤
      2 ^ 40 * g * (n.factorial : ℝ) * (2 ^ 40 / E) ^ n
    apply ht.trans
    gcongr <;> norm_num
  · intro x y
    have ht := quadratic_euclidean_remainder_from_bar hf hR hB hb x y
    have he : 8 * ((2 : ℝ) ^ 23 * g * (2 ^ 11 * E⁻¹)) * vecNormSq y =
        2 ^ 37 * g * vecNormSq y / E := by
      norm_num [div_eq_mul_inv]
      ring
    rw [he] at ht
    apply ht.trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num) hg) (vecNormSq_nonneg y)) hE.le

end AVRegularity.CycleReference
end
