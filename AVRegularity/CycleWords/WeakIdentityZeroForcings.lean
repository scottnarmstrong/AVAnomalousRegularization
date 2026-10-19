-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.FibreSeriesPeriodicReplacement
import AVRegularity.CycleWords.ShearFrequencyAlgebra
public import AVRegularity.Statements.Intermediate.CoupledEnergy.CoupledWeakIdentity
public import AVRegularity.CycleEvolution.ScalarEnergyDecay
import AVRegularity.CycleComparison.Residual.ChartTransport.Piola
import AVRegularity.Weighted.PlaneH1Readouts
public import AVRegularity.CoupledEnergyPlane.Fourier.HilbertNaturality
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleWords

/-! A quiet interval before the pulse gives the exponentially small adjoint memory. -/

theorem futureMemory_delay_identity (μ : ℝ) (p : ℝ → ℝ)
    (hp : Continuous p) (hc : HasCompactSupport p) (t d : ℝ) (hd : 0 ≤ d)
    (hz : ∀ s ∈ Set.Ico t (t + d), p s = 0) :
    futureMemory μ p t = Real.exp (-μ * d) * futureMemory μ p (t + d) := by
  let g := fun s : ℝ => p s * Real.exp (-μ * s)
  have hi : Integrable g := (hp.mul (by fun_prop)).integrable_of_hasCompactSupport hc.mul_right
  have he := intervalIntegral.integral_Ici_sub_Ici
    (hi.integrableOn : IntegrableOn g (Set.Ici t)) (show t ≤ t + d by linarith)
  have hz' : (∫ s in Set.Ico t (t + d), g s) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero (fun s hs => by dsimp [g]; rw [hz s hs, zero_mul])
  rw [hz'] at he
  have hh : (∫ s in Set.Ici t, g s) = ∫ s in Set.Ici (t + d), g s := sub_eq_zero.mp he
  unfold futureMemory
  change Real.exp (μ * t) * (∫ s in Set.Ici t, g s) = _
  rw [hh, ← mul_assoc, ← Real.exp_add, show -μ * d + μ * (t + d) = μ * t by ring]

theorem futureMemory_delay_bound {μ : ℝ} (hμ : 0 < μ) (p : ℝ → ℝ)
    (hp : Continuous p) (hc : HasCompactSupport p) (hb : ∀ s, p s ≤ 1)
    (t d : ℝ) (hd : 0 ≤ d) (hz : ∀ s ∈ Set.Ico t (t + d), p s = 0) :
    futureMemory μ p t ≤ Real.exp (-μ * d) * μ⁻¹ := by
  rw [futureMemory_delay_identity μ p hp hc t d hd hz]
  exact mul_le_mul_of_nonneg_left (futureMemory_le_inv hμ p hp hc hb (t + d))
    (Real.exp_pos _).le

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace AVRegularity.CycleWords

/-! Native L2 coordinate projections converge to the original field. -/

variable {X I E : Type*} [MeasurableSpace X] [Countable I] [DecidableEq I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure X}

omit [Countable I] in
theorem L2CoordinateProjection_remainder_norm
    (f : Lp (lp (fun _ : I => E) 2) 2 μ) (s : Finset I) :
    ‖f - (lpCoordinateProjection s).compLp f‖ =
      lpNorm (fun x => f x - ∑ i ∈ s, lp.single 2 i (f x i)) 2 μ := by
  rw [Lp.norm_def, toReal_eLpNorm]
  unfold lpNorm
  congr 1
  apply eLpNorm_congr_ae
  filter_upwards [Lp.coeFn_sub f ((lpCoordinateProjection s).compLp f),
    (lpCoordinateProjection s).coeFn_compLp f] with x hx hp
  rw [hx, Pi.sub_apply, hp, lpCoordinateProjection_apply]

theorem tendsto_L2CoordinateProjection (f : Lp (lp (fun _ : I => E) 2) 2 μ) :
    Tendsto (fun s : Finset I => (lpCoordinateProjection s).compLp f) atTop (𝓝 f) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hh := tendsto_lpNorm_coordinate_remainder f (Lp.memLp f)
  simpa only [dist_eq_norm, norm_sub_rev, L2CoordinateProjection_remainder_norm] using hh

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleWords

/-! Exact mixed jet scaling between normalized and dimensional slow labels. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mixedJet_dimensional_norm_eq {r q : ℕ} {f : Vec 2 → Vec 2 → E}
    (hf : IsBoxSmooth r q f) (s τ : ℝ) (Y z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y' => iteratedFDeriv ℝ q
      (fun z' => s • f (τ • Y') z') z) Y‖ =
      |s| * |τ| ^ r * ‖iteratedFDeriv ℝ r
        (fun X => iteratedFDeriv ℝ q (f X) z) (τ • Y)‖ := by
  have he (Y' : Vec 2) : iteratedFDeriv ℝ q (fun z' => s • f (τ • Y') z') z =
      s • iteratedFDeriv ℝ q (f (τ • Y')) z :=
    iteratedFDeriv_const_smul_apply'
      (((hf.1 (τ • Y')).of_le (by exact_mod_cast le_refl q)).contDiffAt)
  simp_rw [he]
  have hg : ContDiff ℝ (r : ℕ) (fun Y' => iteratedFDeriv ℝ q (f (τ • Y')) z) :=
    ((hf.2.1 q le_rfl z).of_le (by exact_mod_cast le_refl r)).comp (contDiff_id.const_smul τ)
  rw [iteratedFDeriv_const_smul_apply' hg.contDiffAt, norm_smul, Real.norm_eq_abs]
  have hh := normalizedJet_rescaling_eq r
    ((hf.2.1 q le_rfl z).of_le (by exact_mod_cast le_refl r)) 1 τ Y
  simp only [one_pow, one_mul] at hh
  rw [hh]
  ring

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Integer-indexed frequency tiling, with the exact fibre square-density integral. -/

theorem planeFrequency_lintegral_integer_tiling (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (f : Vec 2 → ℝ≥0∞) :
    (∫⁻ x, f x) = ∑' n : Fin 2 → ℤ,
      ∫⁻ θ in planeFrequencyCell a P, f (planeLatticeEmbedding P n + θ) := by
  rw [planeFrequency_lintegral_tiling a P hP]
  exact (planeLatticeEquiv P hP).tsum_eq
    (fun g => ∫⁻ θ in planeFrequencyCell a P, f ((g : Vec 2) + θ)) |>.symm

theorem planeFrequency_lintegral_fibre_tiling (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (f : Vec 2 → ℝ≥0∞) (hf : AEMeasurable f volume) :
    (∫⁻ x, f x) = ∫⁻ θ in planeFrequencyCell a P,
      ∑' n : Fin 2 → ℤ, f (planeLatticeEmbedding P n + θ) := by
  rw [planeFrequency_lintegral_integer_tiling a P hP, lintegral_tsum]
  intro n
  exact (hf.comp_quasiMeasurePreserving
    (measurePreserving_add_left volume (planeLatticeEmbedding P n)).quasiMeasurePreserving).mono_measure
      Measure.restrict_le_self

end AVRegularity.CycleWords
end
end

section
@[expose] public section
namespace AVRegularity.CycleWords

/-! A quiet cutoff residual is bounded by the inverse cell duration. -/

theorem quiet_residual_cell_bound {B T L τ E D C K R : ℝ}
    (hB : 0 < B) (hT : 0 < T) (hτ : 0 < τ) (hL : 0 ≤ L) (hE : 0 ≤ E)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hD0 : 0 ≤ D)
    (hD : D ^ 2 ≤ C * B * L ^ 2)
    (hdur : Real.sqrt T * L / τ * E ≤ 1)
    (hR : |R| ≤ (K / τ) * (E * D)) :
    |(L ^ 2 / Real.sqrt (B * T)) * R| ≤ K * (1 + C) * (L ^ 2 / T) := by
  have hr := Real.sqrt_pos.2 (mul_pos hB hT)
  have hx0 : 0 ≤ T / Real.sqrt (B * T) * (E * D / τ) := by positivity
  have hx := abs_le_one_add_of_sq_le hC
    (quiet_duration_normalized_sq hB hT hτ hL hE hC hD hdur)
  rw [abs_of_nonneg hx0] at hx
  have hn : |(T / Real.sqrt (B * T)) * R| ≤ K * (1 + C) := by
    rw [abs_mul, abs_of_pos (div_pos hT hr)]
    calc
      _ ≤ (T / Real.sqrt (B * T)) * ((K / τ) * (E * D)) :=
        mul_le_mul_of_nonneg_left hR (div_pos hT hr).le
      _ = K * (T / Real.sqrt (B * T) * (E * D / τ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hx hK
  have he : (L ^ 2 / Real.sqrt (B * T)) * R =
      (L ^ 2 / T) * ((T / Real.sqrt (B * T)) * R) := by field_simp
  rw [he, abs_mul, abs_of_nonneg (div_nonneg (sq_nonneg L) hT.le)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hn (div_nonneg (sq_nonneg L) hT.le)

end AVRegularity.CycleWords
end
end

section
@[expose] public section
open scoped Classical
namespace AVRegularity.CycleWords

/-! The sum of response fluxes differs from the actual fluxes by the negative
metric remainder, original source remainder, and terminal metric insertion. -/

variable {E : Type*} [AddCommGroup E]

theorem responseFlux_remainder_telescope (J : ℕ) (G T P H S : Fin (J + 1) → E) :
    (∑ j : Fin (J + 1), (G j + T j +
      ∑ j' : Fin (J + 1), if j.val = j'.val + 1 then P j' else 0)) -
    (∑ j : Fin (J + 1), (G j + P j + H j + T j + S j)) =
      -((∑ j, H j) + (∑ j, S j) + P (Fin.last J)) := by
  simp only [Finset.sum_add_distrib]
  rw [responsePreviousLevel_sum_telescope]
  abel

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
open scoped FourierTransform
namespace AVRegularity.CycleWords

/-! Smoothness of the literal real cosine cutoff kernel. -/

def seamDotPairing : Vec 2 →L[ℝ] Vec 2 →L[ℝ] ℝ :=
  ∑ j : Fin 2, (ContinuousLinearMap.proj j : Vec 2 →L[ℝ] ℝ).smulRight
    (ContinuousLinearMap.proj j : Vec 2 →L[ℝ] ℝ)

theorem seamDotPairing_apply (x y : Vec 2) : seamDotPairing x y = vecDot x y := by
  simp only [seamDotPairing, sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply,
    smul_apply, smul_eq_mul, vecDot]

def seamFourierPairing : Vec 2 →L[ℝ] Vec 2 →L[ℝ] ℝ :=
  (-(2 * Real.pi)⁻¹) • seamDotPairing

def seamCutoffFourier (m : Vec 2 → ℝ) : Vec 2 → ℂ :=
  VectorFourier.fourierIntegral 𝐞 volume seamFourierPairing.toLinearMap₁₂ (fun θ => (m θ : ℂ))

theorem seamCutoffFourier_contDiff (m : Vec 2 → ℝ) (R : ℝ)
    (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0) (hs : Continuous m) :
    ContDiff ℝ (⊤ : ℕ∞) (seamCutoffFourier m) := by
  apply VectorFourier.contDiff_fourierIntegral
  intro n _
  simpa only [Complex.norm_real] using seamCutoff_polynomial_integrable m R hm hs n

theorem cutoffKernel_eq_seamCutoffFourier_re (m : Vec 2 → ℝ) (R : ℝ)
    (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0) (hs : Continuous m) (x : Vec 2) :
    cutoffKernel m x = (2 * Real.pi)⁻¹ ^ 2 * (seamCutoffFourier m x).re := by
  have hi : Integrable (fun θ => (m θ : ℂ)) :=
    (hs.integrable_of_hasCompactSupport (seamCutoff_hasCompactSupport m R hm)).ofReal
  have hif := (VectorFourier.fourierIntegral_convergent_iff (L := seamFourierPairing.toLinearMap₁₂) Real.continuous_fourierChar
    (by apply seamFourierPairing.continuous₂) x).mpr hi
  unfold cutoffKernel seamCutoffFourier VectorFourier.fourierIntegral
  have hRe := integral_re hif
  change (∫ θ : Vec 2, (𝐞 (-seamFourierPairing θ x) • (m θ : ℂ)).re) =
    (∫ θ : Vec 2, 𝐞 (-seamFourierPairing θ x) • (m θ : ℂ)).re at hRe
  change (2 * Real.pi)⁻¹ ^ 2 * (∫ θ : Vec 2, m θ * Real.cos (vecDot θ x)) =
    (2 * Real.pi)⁻¹ ^ 2 * (∫ θ : Vec 2, 𝐞 (-seamFourierPairing θ x) • (m θ : ℂ)).re
  rw [← hRe]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with θ
  have hpair : 2 * Real.pi * (-seamFourierPairing θ x) = vecDot θ x := by
    simp only [seamFourierPairing, smul_apply, smul_eq_mul,
      seamDotPairing_apply]
    field_simp
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.exp_ofReal_mul_I_re]
  rw [hpair, mul_comm]

theorem seamCutoffKernel_contDiff (m : Vec 2 → ℝ) (R : ℝ)
    (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0) (hs : Continuous m) :
    ContDiff ℝ (⊤ : ℕ∞) (cutoffKernel m) := by
  have he : cutoffKernel m = fun x => (2 * Real.pi)⁻¹ ^ 2 * (seamCutoffFourier m x).re :=
    funext (cutoffKernel_eq_seamCutoffFourier_re m R hm hs)
  rw [he]
  exact contDiff_const.mul (Complex.reCLM.contDiff.comp (seamCutoffFourier_contDiff m R hm hs))

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.CycleWords

/-! Redistributing a literal flux preserves the full integrable weak identity. -/

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- An almost-everywhere time redistribution also preserves the weak identity,
provided the new spatial pairings are integrable at each stated time. -/
theorem coupledWeakIdentity_flux_ae_time_congr (μ : Measure (Vec 2)) (ν a t : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (u₀ f φ : Vec 2 → H) (dφ : Fin 2 → Vec 2 → H)
    (du : ℝ → Fin 2 → Vec 2 → H)
    (flux F flux' F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)) (g : ℝ → Vec 2 → H)
    (hs : CoupledWeakIdentity μ ν a t v u₀ f φ dφ du flux F g)
    (he : ∀ᵐ s ∂volume.restrict (Set.Ioc a t),
      (fun x => flux s x + F s x) =ᵐ[μ] (fun x => flux' s x + F' s x))
    (hi : ∀ s ∈ Set.Ioc a t, Integrable (fun x =>
      -(∑ k : Fin 2, v s x k * inner ℝ (du s k x) (φ x)) -
        ν * ∑ k : Fin 2, inner ℝ (du s k x) (dφ k x) -
        ∑ k : Fin 2, inner ℝ (flux' s x k + F' s x k) (dφ k x) +
        inner ℝ (g s x) (φ x)) μ) :
    CoupledWeakIdentity μ ν a t v u₀ f φ dφ du flux' F' g := by
  let rhs := fun (A B : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)) s x =>
    -(∑ k : Fin 2, v s x k * inner ℝ (du s k x) (φ x)) -
      ν * ∑ k : Fin 2, inner ℝ (du s k x) (dφ k x) -
      ∑ k : Fin 2, inner ℝ (A s x k + B s x k) (dφ k x) + inner ℝ (g s x) (φ x)
  have ht : (fun s => ∫ x, rhs flux F s x ∂μ) =ᵐ[volume.restrict (Set.Ioc a t)]
      (fun s => ∫ x, rhs flux' F' s x ∂μ) := by
    filter_upwards [he] with s hs
    apply integral_congr_ae
    filter_upwards [hs] with x hx
    have hk (k : Fin 2) : flux s x k + F s x k = flux' s x k + F' s x k :=
      congrArg (fun q : PiLp 2 (fun _ : Fin 2 => H) => q k) hx
    dsimp only [rhs]
    simp_rw [hk]
  rcases hs with ⟨hu, hf, _, htime, heq⟩
  exact ⟨hu, hf, hi, htime.congr ht, heq.trans (integral_congr_ae ht)⟩

/-- Changing the native gradient and flux on a null set of times preserves the
integrated identity when the replacement retains spatial integrability. -/
theorem coupledWeakIdentity_gradient_flux_ae_time_congr
    (μ : Measure (Vec 2)) (ν a t : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (u₀ f φ : Vec 2 → H) (dφ : Fin 2 → Vec 2 → H)
    (du du' : ℝ → Fin 2 → Vec 2 → H)
    (flux F flux' F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H))
    (g : ℝ → Vec 2 → H)
    (hs : CoupledWeakIdentity μ ν a t v u₀ f φ dφ du flux F g)
    (hd : ∀ᵐ s ∂volume.restrict (Set.Ioc a t), ∀ k, du s k =ᵐ[μ] du' s k)
    (he : ∀ᵐ s ∂volume.restrict (Set.Ioc a t),
      (fun x => flux s x + F s x) =ᵐ[μ] (fun x => flux' s x + F' s x))
    (hi : ∀ s ∈ Set.Ioc a t, Integrable (fun x =>
      -(∑ k : Fin 2, v s x k * inner ℝ (du' s k x) (φ x)) -
        ν * ∑ k : Fin 2, inner ℝ (du' s k x) (dφ k x) -
        ∑ k : Fin 2, inner ℝ (flux' s x k + F' s x k) (dφ k x) +
        inner ℝ (g s x) (φ x)) μ) :
    CoupledWeakIdentity μ ν a t v u₀ f φ dφ du' flux' F' g := by
  let rhs := fun (D : ℝ → Fin 2 → Vec 2 → H)
      (A B : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)) s x =>
    -(∑ k : Fin 2, v s x k * inner ℝ (D s k x) (φ x)) -
      ν * ∑ k : Fin 2, inner ℝ (D s k x) (dφ k x) -
      ∑ k : Fin 2, inner ℝ (A s x k + B s x k) (dφ k x) + inner ℝ (g s x) (φ x)
  have ht : (fun s => ∫ x, rhs du flux F s x ∂μ) =ᵐ[volume.restrict (Set.Ioc a t)]
      (fun s => ∫ x, rhs du' flux' F' s x ∂μ) := by
    filter_upwards [hd, he] with s hds hes
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hds, hes] with x hdx hx
    have hk (k : Fin 2) : flux s x k + F s x k = flux' s x k + F' s x k :=
      congrArg (fun q : PiLp 2 (fun _ : Fin 2 => H) => q k) hx
    dsimp only [rhs]
    simp_rw [hdx, hk]
  rcases hs with ⟨hu, hf, _, htime, heq⟩
  exact ⟨hu, hf, hi, htime.congr ht, heq.trans (integral_congr_ae ht)⟩
end

/-! Addition of integrable weak equations preserves all spatial and time integrability requirements. -/

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def weakEquationRhs (ν : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (φ : Vec 2 → H) (dφ : Fin 2 → Vec 2 → H)
    (du : ℝ → Fin 2 → Vec 2 → H)
    (flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H))
    (g : ℝ → Vec 2 → H) (s : ℝ) (x : Vec 2) : ℝ :=
  -(∑ k : Fin 2, v s x k * inner ℝ (du s k x) (φ x)) -
    ν * ∑ k : Fin 2, inner ℝ (du s k x) (dφ k x) -
    ∑ k : Fin 2, inner ℝ (flux s x k + F s x k) (dφ k x) + inner ℝ (g s x) (φ x)

theorem weakEquationRhs_add (ν : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (φ : Vec 2 → H) (dφ : Fin 2 → Vec 2 → H)
    (du₁ du₂ : ℝ → Fin 2 → Vec 2 → H)
    (A₁ A₂ F₁ F₂ : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H))
    (g₁ g₂ : ℝ → Vec 2 → H) (s : ℝ) (x : Vec 2) :
    weakEquationRhs ν v φ dφ (du₁ + du₂) (A₁ + A₂) (F₁ + F₂) (g₁ + g₂) s x =
      weakEquationRhs ν v φ dφ du₁ A₁ F₁ g₁ s x +
        weakEquationRhs ν v φ dφ du₂ A₂ F₂ g₂ s x := by
  simp only [weakEquationRhs, Pi.add_apply, PiLp.add_apply,
    inner_add_left, mul_add, Finset.sum_add_distrib]
  ring

theorem coupledWeakIdentity_add (μ : Measure (Vec 2)) (ν a t : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (u₁ u₂ f₁ f₂ φ : Vec 2 → H)
    (dφ : Fin 2 → Vec 2 → H) (du₁ du₂ : ℝ → Fin 2 → Vec 2 → H)
    (A₁ A₂ F₁ F₂ : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H))
    (g₁ g₂ : ℝ → Vec 2 → H)
    (h₁ : CoupledWeakIdentity μ ν a t v u₁ f₁ φ dφ du₁ A₁ F₁ g₁)
    (h₂ : CoupledWeakIdentity μ ν a t v u₂ f₂ φ dφ du₂ A₂ F₂ g₂) :
    CoupledWeakIdentity μ ν a t v (u₁ + u₂) (f₁ + f₂) φ dφ
      (du₁ + du₂) (A₁ + A₂) (F₁ + F₂) (g₁ + g₂) := by
  change Integrable _ μ ∧ Integrable _ μ ∧
    (∀ s ∈ Set.Ioc a t, Integrable (weakEquationRhs ν v φ dφ du₁ A₁ F₁ g₁ s) μ) ∧
    IntegrableOn (fun s => ∫ x, weakEquationRhs ν v φ dφ du₁ A₁ F₁ g₁ s x ∂μ) (Set.Ioc a t) ∧ _ at h₁
  change Integrable _ μ ∧ Integrable _ μ ∧
    (∀ s ∈ Set.Ioc a t, Integrable (weakEquationRhs ν v φ dφ du₂ A₂ F₂ g₂ s) μ) ∧
    IntegrableOn (fun s => ∫ x, weakEquationRhs ν v φ dφ du₂ A₂ F₂ g₂ s x ∂μ) (Set.Ioc a t) ∧ _ at h₂
  rcases h₁ with ⟨hu₁, hf₁, hs₁, ht₁, he₁⟩
  rcases h₂ with ⟨hu₂, hf₂, hs₂, ht₂, he₂⟩
  have hu : (fun x => inner ℝ ((u₁ + u₂) x) (φ x)) =
      (fun x => inner ℝ (u₁ x) (φ x) + inner ℝ (u₂ x) (φ x)) := by
    funext x; simp only [Pi.add_apply, inner_add_left]
  have hf : (fun x => inner ℝ ((f₁ + f₂) x) (φ x)) =
      (fun x => inner ℝ (f₁ x) (φ x) + inner ℝ (f₂ x) (φ x)) := by
    funext x; simp only [Pi.add_apply, inner_add_left]
  have hr : weakEquationRhs ν v φ dφ (du₁ + du₂) (A₁ + A₂) (F₁ + F₂) (g₁ + g₂) =
      fun s x => weakEquationRhs ν v φ dφ du₁ A₁ F₁ g₁ s x +
        weakEquationRhs ν v φ dφ du₂ A₂ F₂ g₂ s x := by
    funext s x; exact weakEquationRhs_add ν v φ dφ du₁ du₂ A₁ A₂ F₁ F₂ g₁ g₂ s x
  have hi (s : ℝ) (hs : s ∈ Set.Ioc a t) :
      (∫ x, weakEquationRhs ν v φ dφ (du₁ + du₂) (A₁ + A₂) (F₁ + F₂) (g₁ + g₂) s x ∂μ) =
      (∫ x, weakEquationRhs ν v φ dφ du₁ A₁ F₁ g₁ s x ∂μ) +
        ∫ x, weakEquationRhs ν v φ dφ du₂ A₂ F₂ g₂ s x ∂μ := by
    rw [hr]
    exact integral_add (hs₁ s hs) (hs₂ s hs)
  have hiAE : (fun s => ∫ x, weakEquationRhs ν v φ dφ (du₁ + du₂) (A₁ + A₂) (F₁ + F₂) (g₁ + g₂) s x ∂μ) =ᵐ[volume.restrict (Set.Ioc a t)]
      (fun s => (∫ x, weakEquationRhs ν v φ dφ du₁ A₁ F₁ g₁ s x ∂μ) +
        ∫ x, weakEquationRhs ν v φ dφ du₂ A₂ F₂ g₂ s x ∂μ) := (ae_restrict_mem (μ := volume) measurableSet_Ioc).mono hi
  change Integrable _ μ ∧ Integrable _ μ ∧
    (∀ s ∈ Set.Ioc a t, Integrable (weakEquationRhs ν v φ dφ (du₁ + du₂) (A₁ + A₂) (F₁ + F₂) (g₁ + g₂) s) μ) ∧
    IntegrableOn (fun s => ∫ x, weakEquationRhs ν v φ dφ (du₁ + du₂) (A₁ + A₂) (F₁ + F₂) (g₁ + g₂) s x ∂μ) (Set.Ioc a t) ∧ _
  refine ⟨by rw [hu]; exact hu₁.add hu₂, by rw [hf]; exact hf₁.add hf₂,
    ?_, (ht₁.add ht₂).congr hiAE.symm, ?_⟩
  · intro s hs
    rw [hr]
    exact (hs₁ s hs).add (hs₂ s hs)
  · change (∫ x, inner ℝ ((u₁ + u₂) x) (φ x) ∂μ) -
      (∫ x, inner ℝ ((f₁ + f₂) x) (φ x) ∂μ) =
      ∫ s in Set.Ioc a t, ∫ x, weakEquationRhs ν v φ dφ (du₁ + du₂) (A₁ + A₂) (F₁ + F₂) (g₁ + g₂) s x ∂μ
    rw [hu, hf, integral_add hu₁ hu₂, integral_add hf₁ hf₂,
      integral_congr_ae hiAE, integral_add ht₁ ht₂]
    simp only [weakEquationRhs]
    linarith only [he₁, he₂]
end

/-! Changing the native value representatives on spatial null sets preserves
both integrable endpoint pairings in the weak equation. -/

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem coupledWeakIdentity_value_congr (μ : Measure (Vec 2)) (ν a t : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (u f u' f' φ : Vec 2 → H) (dφ : Fin 2 → Vec 2 → H)
    (du : ℝ → Fin 2 → Vec 2 → H)
    (A F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)) (g : ℝ → Vec 2 → H)
    (hs : CoupledWeakIdentity μ ν a t v u f φ dφ du A F g)
    (hu : u =ᵐ[μ] u') (hf : f =ᵐ[μ] f') :
    CoupledWeakIdentity μ ν a t v u' f' φ dφ du A F g := by
  have hup : (fun x => inner ℝ (u x) (φ x)) =ᵐ[μ] (fun x => inner ℝ (u' x) (φ x)) :=
    hu.mono (fun x hx => congrArg (fun z => inner ℝ z (φ x)) hx)
  have hfp : (fun x => inner ℝ (f x) (φ x)) =ᵐ[μ] (fun x => inner ℝ (f' x) (φ x)) :=
    hf.mono (fun x hx => congrArg (fun z => inner ℝ z (φ x)) hx)
  rcases hs with ⟨huI, hfI, hspace, htime, heq⟩
  refine ⟨huI.congr hup, hfI.congr hfp, hspace, htime, ?_⟩
  rw [← integral_congr_ae hup, ← integral_congr_ae hfp]
  exact heq
end

end AVRegularity.CycleWords
end
end

section
public section
open Metric AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Uniform derivative bounds on a smaller complex line disc use only the original analytic value bound. -/

theorem analyticLine_interior_derivative_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (f : ℂ → E) (R r d M : ℝ) (hd : 0 < d) (hmargin : r + d < R)
    (ha : AnalyticOnNhd ℂ f (ball 0 R)) (hb : ∀ z ∈ ball 0 R, ‖f z‖ ≤ M)
    (z : ℂ) (hz : ‖z‖ ≤ r) (n : ℕ) :
    ‖iteratedDeriv n f z‖ ≤ analyticBallDerivativeConstant n * M / d ^ n := by
  have hs : ball z d ⊆ ball 0 R := by
    intro w hw
    have hw' : ‖w - z‖ < d := by simpa only [mem_ball, dist_eq_norm] using hw
    have ht := norm_add_le (w - z) z
    rw [sub_add_cancel] at ht
    rw [mem_ball, dist_zero_right]
    linarith only [ht, hw', hz, hmargin]
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact analytic_ball_iterated_derivative_le n hd (ha.mono hs) (fun w hw => hb w (hs hw))

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization UnitAddTorus
namespace AVRegularity.CycleWords

/-! Smooth ambient representatives of the actual complex torus Fourier basis. -/

def cellComplexFourierPhase (n : Fin 2 → ℤ) : Vec 2 →L[ℝ] ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I) •
    (Complex.ofRealCLM.comp (seamDotPairing (fun i => (n i : ℝ))))

def cellComplexFourierMode (n : Fin 2 → ℤ) (x : Vec 2) : ℂ :=
  Complex.exp (cellComplexFourierPhase n x)

theorem cellComplexFourierMode_contDiff (n : Fin 2 → ℤ) :
    ContDiff ℝ ⊤ (cellComplexFourierMode n) :=
  (cellComplexFourierPhase n).contDiff.cexp

theorem cellComplexFourierMode_eq (n : Fin 2 → ℤ) (x : Vec 2) :
    cellComplexFourierMode n x = mFourier n (fun i => (x i : UnitAddCircle)) := by
  simp only [cellComplexFourierMode, cellComplexFourierPhase,
    smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, seamDotPairing_apply, vecDot,
    Complex.ofReal_sum, Complex.ofReal_mul, smul_eq_mul, Finset.mul_sum]
  rw [Complex.exp_sum]
  simp only [mFourier, ContinuousMap.coe_mk, fourier_coe_apply]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Complex.ofReal_one, div_one]
  congr 1
  push_cast
  ring

theorem cellComplexFourierMode_fderiv (n : Fin 2 → ℤ) (x : Vec 2) :
    fderiv ℝ (cellComplexFourierMode n) x =
      cellComplexFourierMode n x • cellComplexFourierPhase n :=
  ((cellComplexFourierPhase n).hasFDerivAt.cexp).fderiv

theorem cellComplexFourierPhase_basisVec (n : Fin 2 → ℤ) (i : Fin 2) :
    cellComplexFourierPhase n (basisVec i) =
      (2 * (Real.pi : ℂ) * Complex.I) * (n i : ℂ) := by
  simp [cellComplexFourierPhase, seamDotPairing_apply, vecDot, basisVec_apply,
    smul_eq_mul]

theorem cellComplexFourierMode_directional_derivative (n : Fin 2 → ℤ)
    (x : Vec 2) (i : Fin 2) :
    fderiv ℝ (cellComplexFourierMode n) x (basisVec i) =
      ((2 * (Real.pi : ℂ) * Complex.I) * (n i : ℂ)) * cellComplexFourierMode n x := by
  rw [cellComplexFourierMode_fderiv, smul_apply, cellComplexFourierPhase_basisVec,
    smul_eq_mul, mul_comm]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.CycleWords

/-! The exact centered transition assumptions give a measure-preserving plane homeomorphism. -/

def centeredTransitionHomeomorph (Υ Υinv : Vec 2 → Vec 2) (g δ C : ℝ)
    (hΥ : IsCenteredTransition Υ Υinv g δ C 2) : Vec 2 ≃ₜ Vec 2 where
  toFun := Υ
  invFun := Υinv
  left_inv := hΥ.left_inv
  right_inv := hΥ.right_inv
  continuous_toFun := hΥ.smooth.1.continuous
  continuous_invFun := hΥ.smooth.2.continuous

theorem centeredTransition_measurePreserving (Υ Υinv : Vec 2 → Vec 2) (g δ C : ℝ)
    (hΥ : IsCenteredTransition Υ Υinv g δ C 2) : MeasurePreserving Υ volume volume := by
  apply ChartTransport.measurePreserving_of_det
    (hΥ.smooth.1.of_le (by norm_num)) hΥ.left_inv hΥ.right_inv
  intro z
  rw [← ChartTransport.det_fderiv_eq_jac]
  exact hΥ.volume z

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Finite ordered coefficient arrays inherit uniform operator bounds. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem coefficientDerivativeArray_norm_le_card_mul
    (C : Vec 2 → E →L[ℝ] F) (j : ℕ) (x : Vec 2) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ w : DerivativeWord2 j, ‖orderedCoefficientDerivative C j w x‖ ≤ B) :
    ‖coefficientDerivativeArray C j x‖ ≤ (Fintype.card (DerivativeWord2 j) : ℝ) * B := by
  classical
  let N : ℝ := Fintype.card (DerivativeWord2 j)
  have hN : 1 ≤ N := by
    change (1 : ℝ) ≤ (Fintype.card (DerivativeWord2 j) : ℝ)
    exact_mod_cast Nat.succ_le_of_lt
      (Fintype.card_pos_iff.mpr (inferInstance : Nonempty (DerivativeWord2 j)))
  apply (coefficientDerivativeArray C j x).opNorm_le_bound (mul_nonneg (by linarith) hB)
  intro e
  have hs : ‖coefficientDerivativeArray C j x e‖ ^ 2 ≤ N * (B * ‖e‖) ^ 2 := by
    rw [coefficientDerivativeArray_normSq]
    calc
      _ ≤ ∑ _w : DerivativeWord2 j, (B * ‖e‖) ^ 2 := by
        apply Finset.sum_le_sum
        intro w _
        have hh := ((orderedCoefficientDerivative C j w x).le_opNorm e).trans
          (mul_le_mul_of_nonneg_right (hb w) (norm_nonneg e))
        exact pow_le_pow_left₀ (norm_nonneg _) hh 2
      _ = _ := by simp [N]
  have hNN : N ≤ N ^ 2 := by nlinarith
  have ht := mul_le_mul_of_nonneg_right hNN (sq_nonneg (B * ‖e‖))
  have hn := norm_nonneg (coefficientDerivativeArray C j x e)
  have hprod : 0 ≤ N * B * ‖e‖ := mul_nonneg (mul_nonneg (by linarith) hB) (norm_nonneg e)
  change ‖coefficientDerivativeArray C j x e‖ ≤ N * B * ‖e‖
  nlinarith [hs.trans ht]

theorem coefficientDerivativeArray_norm_le_iterated_bound
    (C : Vec 2 → E →L[ℝ] F) (j : ℕ) (hC : ContDiff ℝ (j : ℕ) C)
    (x : Vec 2) (B : ℝ) (hB : 0 ≤ B) (hb : ‖iteratedFDeriv ℝ j C x‖ ≤ B) :
    ‖coefficientDerivativeArray C j x‖ ≤ (Fintype.card (DerivativeWord2 j) : ℝ) * B :=
  coefficientDerivativeArray_norm_le_card_mul C j x B hB
    (fun w => (Weighted.orderedCoefficientDerivative_norm_le C j hC w x).trans hb)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization Filter
open scoped Topology
namespace AVRegularity.CycleWords

/-! Expanding bump functions agree locally with one at every fixed point. -/

def expandingPlaneCutoff (n : ℕ) (x : Vec 2) : ℝ :=
  (default : ContDiffBump (0 : Vec 2)) (((n : ℝ) + 1)⁻¹ • x)

theorem expandingPlaneCutoff_eventually_local_one (x : Vec 2) :
    ∀ᶠ n : ℕ in atTop, expandingPlaneCutoff n =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
  let φ : ContDiffBump (0 : Vec 2) := default
  have he : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hs : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ • x) atTop (𝓝 (0 : Vec 2)) := by
    simpa only [zero_smul] using he.smul_const x
  have hb := hs.eventually (Metric.ball_mem_nhds (0 : Vec 2) φ.rIn_pos)
  filter_upwards [hb] with n hn
  have hφ := φ.eventuallyEq_one_of_mem_ball hn
  have hc : ContinuousAt (fun y : Vec 2 => ((n : ℝ) + 1)⁻¹ • y) x :=
    (continuous_const_smul _).continuousAt
  exact hφ.comp_tendsto hc.tendsto

theorem expandingPlaneCutoff_contDiff (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (expandingPlaneCutoff n) :=
  (default : ContDiffBump (0 : Vec 2)).contDiff.comp
    (((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ (Vec 2)).contDiff

theorem expandingPlaneCutoff_hasCompactSupport (n : ℕ) :
    HasCompactSupport (expandingPlaneCutoff n) :=
  (default : ContDiffBump (0 : Vec 2)).hasCompactSupport.comp_smul
    (inv_pos.mpr (by positivity : 0 < (n : ℝ) + 1)).ne'

theorem expandingPlaneCutoff_coefficient_jet_eventually_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : Vec 2) (j : ℕ) (w : Sobolev.DerivativeWord2 j) :
    ∀ᶠ n : ℕ in atTop,
      Sobolev.orderedCoefficientDerivative
        (fun y => expandingPlaneCutoff n y • ContinuousLinearMap.id ℝ E) j w x =
      Sobolev.orderedCoefficientDerivative
        (fun _ : Vec 2 => ContinuousLinearMap.id ℝ E) j w x := by
  filter_upwards [expandingPlaneCutoff_eventually_local_one x] with n hn
  have hc : (fun y => expandingPlaneCutoff n y • ContinuousLinearMap.id ℝ E) =ᶠ[𝓝 x]
      (fun _ : Vec 2 => ContinuousLinearMap.id ℝ E) := by
    filter_upwards [hn] with y hy
    simp only [hy, one_smul]
  exact orderedCoefficientDerivative_eq_of_eventuallyEq hc j w

end AVRegularity.CycleWords
end
end

section
@[expose] public section
open AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Finite chain rule budgets retain decreasing factorial weights. -/

theorem finite_weighted_square_budget {ι : Type*} [Fintype ι]
    (c u : ι → ℝ) (j : ι → ℕ) (n : ℕ) (r a : ℝ)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (ha : 0 ≤ a)
    (hj : ∀ i, j i ≤ n) (hb : a ≤ ∑ i, c i * u i) :
    factorialWeight r n * a ^ 2 ≤
      (Fintype.card ι : ℝ) * ∑ i, c i ^ 2 * (factorialWeight r (j i) * u i ^ 2) := by
  have hsq : a ^ 2 ≤ (∑ i, c i * u i) ^ 2 := pow_le_pow_left₀ ha hb 2
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => c i * u i)
  calc
    _ ≤ factorialWeight r n * ((Fintype.card ι : ℝ) * ∑ i, (c i * u i) ^ 2) :=
      mul_le_mul_of_nonneg_left (hsq.trans (by simpa using hcs)) (factorialWeight_nonneg r n)
    _ = (Fintype.card ι : ℝ) * ∑ i, c i ^ 2 * (factorialWeight r n * u i ^ 2) := by
      rw [mul_left_comm, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (factorialWeight_order_antitone hr hr1 (hj i)) (sq_nonneg _))
        (sq_nonneg _)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Fourier
open scoped ENNReal FourierTransform SchwartzMap
namespace AVRegularity.CycleWords

/-! Genuine bounded character modulation and unitary frequency translation on Hilbert L2. -/

local instance hilbertCharacterL2RealComplexSpace : NormedSpace ℝ ℂ :=
  NormedSpace.complexToReal

theorem hilbertModulationCharacter_norm (v x : HilbertTwo) :
    ‖hilbertModulationCharacter v x‖ = 1 := Circle.norm_coe _

theorem hilbertModulationCharacter_memLp_top (v : HilbertTwo) :
    MemLp (hilbertModulationCharacter v) ∞ (volume : Measure HilbertTwo) :=
  memLp_top_of_bound (hilbertModulationCharacter_temperate v).1.continuous.aestronglyMeasurable
    1 (Filter.Eventually.of_forall (fun x => le_of_eq (hilbertModulationCharacter_norm v x)))

def hilbertCharacterModulationOperator (v : HilbertTwo) :
    Lp ℂ 2 (volume : Measure HilbertTwo) →L[ℂ] Lp ℂ 2 (volume : Measure HilbertTwo) :=
  L2Multiplier.operator (hilbertModulationCharacter v) (hilbertModulationCharacter_memLp_top v)

theorem hilbertCharacterModulationOperator_ae (v : HilbertTwo)
    (f : Lp ℂ 2 (volume : Measure HilbertTwo)) :
    hilbertCharacterModulationOperator v f =ᵐ[volume]
      fun x => hilbertModulationCharacter v x * f x :=
  L2Multiplier.operator_ae _ _ f

theorem hilbertFrequencyTranslation_measurePreserving (v : HilbertTwo) :
    MeasurePreserving (fun ξ => ξ - v) (volume : Measure HilbertTwo) volume := by
  simpa only [sub_eq_add_neg] using measurePreserving_add_right volume (-v)

def hilbertFrequencyTranslation (v : HilbertTwo) :
    Lp ℂ 2 (volume : Measure HilbertTwo) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure HilbertTwo) :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun ξ => ξ - v) (hilbertFrequencyTranslation_measurePreserving v)

theorem hilbertFrequencyTranslation_ae (v : HilbertTwo)
    (f : Lp ℂ 2 (volume : Measure HilbertTwo)) :
    hilbertFrequencyTranslation v f =ᵐ[volume] fun ξ => f (ξ - v) :=
  Lp.coeFn_compMeasurePreserving f (hilbertFrequencyTranslation_measurePreserving v)

theorem hilbertCharacterModulationOperator_schwartz (v : HilbertTwo) (f : 𝓢(HilbertTwo, ℂ)) :
    hilbertCharacterModulationOperator v (f.toLp 2) = (hilbertSchwartzModulation v f).toLp 2 := by
  apply Lp.ext
  filter_upwards [hilbertCharacterModulationOperator_ae v (f.toLp 2), f.coeFn_toLp 2,
    (hilbertSchwartzModulation v f).coeFn_toLp 2] with x hx hf hm
  rw [hx, hf, hm, hilbertSchwartzModulation_apply]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Filter
open AVRegularity.CoupledEnergyPlane
open scoped ENNReal Topology
namespace AVRegularity.CycleWords

/-! Uniformly bounded almost-everywhere symbol convergence gives strong L2 convergence. -/

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem L2Multiplier_difference_ae (a b : X → ℂ) (ha : MemLp a ∞ μ)
    (hb : MemLp b ∞ μ) (f : Lp ℂ 2 μ) :
    L2Multiplier.operator a ha f - L2Multiplier.operator b hb f =ᵐ[μ]
      fun x => (a x - b x) * f x := by
  filter_upwards [Lp.coeFn_sub (L2Multiplier.operator a ha f) (L2Multiplier.operator b hb f),
    L2Multiplier.operator_ae a ha f, L2Multiplier.operator_ae b hb f] with x hx hax hbx
  rw [hx, Pi.sub_apply, hax, hbx, sub_mul]

theorem tendsto_L2Multiplier_of_ae (a : ℕ → X → ℂ) (b : X → ℂ)
    (ha : ∀ n, MemLp (a n) ∞ μ) (hb : MemLp b ∞ μ)
    (C : ℝ) (hC : 0 ≤ C) (haC : ∀ n, ∀ᵐ x ∂μ, ‖a n x‖ ≤ C)
    (hbC : ∀ᵐ x ∂μ, ‖b x‖ ≤ C)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => a n x) atTop (𝓝 (b x)))
    (f : Lp ℂ 2 μ) :
    Tendsto (fun n => L2Multiplier.operator (a n) (ha n) f) atTop
      (𝓝 (L2Multiplier.operator b hb f)) := by
  let r (n : ℕ) (x : X) := (a n x - b x) * f x
  have hr (n : ℕ) : MemLp (r n) 2 μ :=
    (Lp.memLp (L2Multiplier.operator (a n) (ha n) f - L2Multiplier.operator b hb f)).ae_eq
      (L2Multiplier_difference_ae (a n) b (ha n) hb f)
  let g (x : X) : ℂ := (2 * C : ℝ) • f x
  have hg : MemLp g 2 μ := (Lp.memLp f).const_smul (2 * C : ℝ)
  have hbound (n : ℕ) : ∀ᵐ x ∂μ, ‖r n x‖ ≤ ‖g x‖ := by
    filter_upwards [haC n, hbC] with x hax hbx
    have hd : ‖a n x - b x‖ ≤ 2 * C :=
      (norm_sub_le _ _).trans (by linarith)
    change ‖(a n x - b x) * f x‖ ≤ ‖(2 * C : ℝ) • f x‖
    rw [norm_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) hC)]
    exact mul_le_mul_of_nonneg_right hd (norm_nonneg _)
  have ht' : ∀ᵐ x ∂μ, Tendsto (fun n => r n x) atTop (𝓝 0) := by
    filter_upwards [ht] with x hx
    simpa [r] using (hx.sub_const (b x)).mul_const (f x)
  have hh := tendsto_lpNorm_two_of_dominated r g hr hg hbound ht'
  rw [tendsto_iff_dist_tendsto_zero]
  have he (n : ℕ) : dist (L2Multiplier.operator (a n) (ha n) f)
      (L2Multiplier.operator b hb f) = lpNorm (r n) 2 μ := by
    rw [dist_eq_norm, Lp.norm_def, toReal_eLpNorm]
    unfold lpNorm
    congr 1
    exact eLpNorm_congr_ae (L2Multiplier_difference_ae (a n) b (ha n) hb f)
  simpa only [he] using hh

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Native time curve addition through an explicitly typed finite sum avoids
elaborating the generic extended seminorm instance through the Sobolev graph. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem nativeTime_add_memLp {K : ℕ} (μ : Measure ℝ)
    (U V : ℝ → PlaneHk Set.univ K E) (hU : MemLp U 2 μ) (hV : MemLp V 2 μ) :
    MemLp (fun t => U t + V t) 2 μ := by
  classical
  let f : Fin 2 → ℝ → PlaneHk Set.univ K E := fun j => if j = 0 then U else V
  have hf (j : Fin 2) : MemLp (f j) 2 μ := by
    by_cases hj : j = 0
    · simpa only [f, ite_eq_left hj] using hU
    · simpa only [f, ite_eq_right hj] using hV
  have hh := memLp_finsetSum (ε' := PlaneHk Set.univ K E) (f := f) Finset.univ (fun j _ => hf j)
  simpa only [Fin.sum_univ_two, f, ite_true, show (1 : Fin 2) ≠ 0 by decide, ite_false] using hh

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
open scoped ENNReal NNReal
namespace AVRegularity.CycleWords

/-! L2 plane frequency data give square summable lattice fibres almost everywhere. -/

variable {E : Type*} [NormedAddCommGroup E]

theorem planeFrequency_L2_density_finite (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (f : Vec 2 → E) (hf : MemLp f 2 volume) :
    ∀ᵐ θ ∂volume.restrict (planeFrequencyCell a P),
      (∑' n : Fin 2 → ℤ, ‖f (planeLatticeEmbedding P n + θ)‖ₑ ^ (2 : ℝ)) < ⊤ := by
  have hm : AEMeasurable (fun x => ‖f x‖ₑ ^ (2 : ℝ)) volume :=
    hf.aestronglyMeasurable.enorm.pow_const _
  have hi : (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ)) < ⊤ := by
    simpa only [ENNReal.toReal_ofNat] using
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hf)
  rw [planeFrequency_lintegral_fibre_tiling a P hP _ hm] at hi
  apply ae_lt_top' _ hi.ne
  apply AEMeasurable.tsum
  intro n
  exact (hm.comp_quasiMeasurePreserving
    (measurePreserving_add_left volume (planeLatticeEmbedding P n)).quasiMeasurePreserving).mono_measure
      Measure.restrict_le_self

theorem planeFrequency_L2_fibre_memℓp (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (f : Vec 2 → E) (hf : MemLp f 2 volume) :
    ∀ᵐ θ ∂volume.restrict (planeFrequencyCell a P),
      Memℓp (fun n : Fin 2 → ℤ => f (planeLatticeEmbedding P n + θ)) 2 := by
  filter_upwards [planeFrequency_L2_density_finite a P hP f hf] with θ hθ
  apply memℓp_gen
  have hh : (∑' n : Fin 2 → ℤ, ((‖f (planeLatticeEmbedding P n + θ)‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞)) ≠ ⊤ := by
    simpa only [enorm_eq_nnnorm, ENNReal.rpow_two, ENNReal.coe_pow] using hθ.ne
  have hs := ENNReal.tsum_coe_ne_top_iff_summable_coe.mp hh
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, NNReal.coe_pow, coe_nnnorm] using hs

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.CycleWords

/-! Global finite-order Taylor bounds on the literal slow polynomial. -/

theorem norm_taylorSlow_remainder_le {f : Vec 2 → ℝ} (K : ℕ)
    (hf : ContDiff ℝ (K + 1 : ℕ) f) (B : ℝ)
    (hb : ∀ z, ‖iteratedFDeriv ℝ (K + 1) f z‖ ≤ B) (x y : Vec 2) :
    ‖f (x + y) - taylorSlow 0 K f x y‖ ≤ B * ‖y‖ ^ (K + 1) / ((K + 1).factorial : ℝ) := by
  have ht := map_add_eq_sum_add_integral_iteratedFDeriv (f := f) (x := x) (y := y) (n := K)
    (fun t _ => hf.contDiffAt)
  have hp : taylorSlow 0 K f x y =
      ∑ k ∈ Finset.range (K + 1), (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k f x (fun _ => y) := by
    simp only [taylorSlow, ← Nat.range_succ_eq_Icc_zero, smul_eq_mul]
  have hr : f (x + y) - taylorSlow 0 K f x y =
      (K.factorial : ℝ)⁻¹ • ∫ t : ℝ in (0 : ℝ)..1,
        (1 - t) ^ K • iteratedFDeriv ℝ (K + 1) f (x + t • y) (fun _ => y) := by
    rw [hp, ht, add_sub_cancel_left]
  rw [hr, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  calc
    _ ≤ (K.factorial : ℝ)⁻¹ * ∫ t : ℝ in (0 : ℝ)..1,
        (1 - t) ^ K * (B * ‖y‖ ^ (K + 1)) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
      apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
      · filter_upwards with t ht
        have hw : 0 ≤ (1 - t) ^ K := pow_nonneg (sub_nonneg.mpr ht.2) _
        rw [norm_smul, Real.norm_of_nonneg hw]
        apply mul_le_mul_of_nonneg_left _ hw
        exact ((iteratedFDeriv ℝ (K + 1) f (x + t • y)).le_opNorm _).trans
          (by simpa using mul_le_mul_of_nonneg_right (hb (x + t • y)) (by positivity : 0 ≤ ∏ _ : Fin (K + 1), ‖y‖))
      · exact (((continuous_const.sub continuous_id).pow K).mul continuous_const).intervalIntegrable _ _
    _ = _ := by
      rw [intervalIntegral.integral_mul_const, AVRegularity.Analysis.Convolution.integral_one_sub_pow, Nat.factorial_succ,
        Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-! Finite sums of component weak equations preserve every integrability clause. -/

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem coupledWeakIdentity_zero (μ : Measure (Vec 2)) (ν a t : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (φ : Vec 2 → H) (dφ : Fin 2 → Vec 2 → H) :
    CoupledWeakIdentity μ ν a t v 0 0 φ dφ 0 0 0 0 := by
  simp [CoupledWeakIdentity, PiLp.zero_apply]

theorem coupledWeakIdentity_finset_sum {ι : Type*} (S : Finset ι)
    (μ : Measure (Vec 2)) (ν a t : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (u f : ι → Vec 2 → H) (φ : Vec 2 → H) (dφ : Fin 2 → Vec 2 → H)
    (du : ι → ℝ → Fin 2 → Vec 2 → H)
    (A F : ι → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H))
    (g : ι → ℝ → Vec 2 → H)
    (h : ∀ j ∈ S, CoupledWeakIdentity μ ν a t v (u j) (f j) φ dφ (du j) (A j) (F j) (g j)) :
    CoupledWeakIdentity μ ν a t v (∑ j ∈ S, u j) (∑ j ∈ S, f j) φ dφ
      (∑ j ∈ S, du j) (∑ j ∈ S, A j) (∑ j ∈ S, F j) (∑ j ∈ S, g j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using coupledWeakIdentity_zero μ ν a t v φ dφ
  | @insert j S hj ih =>
    have hs : ∀ k ∈ S, CoupledWeakIdentity μ ν a t v (u k) (f k) φ dφ (du k) (A k) (F k) (g k) :=
      fun k hk => h k (Finset.mem_insert_of_mem hk)
    have hh := coupledWeakIdentity_add μ ν a t v (u j) (∑ k ∈ S, u k)
      (f j) (∑ k ∈ S, f k) φ dφ (du j) (∑ k ∈ S, du k)
      (A j) (∑ k ∈ S, A k) (F j) (∑ k ∈ S, F k) (g j) (∑ k ∈ S, g k)
      (h j (Finset.mem_insert_self j S)) (ih hs)
    simpa only [Finset.sum_insert hj] using hh
end

/-! Negation and subtraction preserve the complete integrable weak equation. -/

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem weakEquationRhs_neg (ν : ℝ) (v : ℝ → Vec 2 → Vec 2)
    (φ : Vec 2 → H) (dφ : Fin 2 → Vec 2 → H)
    (du : ℝ → Fin 2 → Vec 2 → H)
    (A F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H))
    (g : ℝ → Vec 2 → H) (s : ℝ) (x : Vec 2) :
    weakEquationRhs ν v φ dφ (-du) (-A) (-F) (-g) s x =
      -weakEquationRhs ν v φ dφ du A F g s x := by
  simp only [weakEquationRhs, Pi.neg_apply, PiLp.neg_apply, ← neg_add,
    inner_neg_left, mul_neg, Finset.sum_neg_distrib]
  ring

theorem coupledWeakIdentity_neg (μ : Measure (Vec 2)) (ν a t : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (u f φ : Vec 2 → H)
    (dφ : Fin 2 → Vec 2 → H) (du : ℝ → Fin 2 → Vec 2 → H)
    (A F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)) (g : ℝ → Vec 2 → H)
    (h : CoupledWeakIdentity μ ν a t v u f φ dφ du A F g) :
    CoupledWeakIdentity μ ν a t v (-u) (-f) φ dφ (-du) (-A) (-F) (-g) := by
  change Integrable _ μ ∧ Integrable _ μ ∧
    (∀ s ∈ Set.Ioc a t, Integrable (weakEquationRhs ν v φ dφ du A F g s) μ) ∧
    IntegrableOn (fun s => ∫ x, weakEquationRhs ν v φ dφ du A F g s x ∂μ) (Set.Ioc a t) ∧ _ at h
  rcases h with ⟨hu, hf, hs, ht, he⟩
  have hu' : (fun x => inner ℝ ((-u) x) (φ x)) = fun x => -inner ℝ (u x) (φ x) := by
    funext x; simp only [Pi.neg_apply, inner_neg_left]
  have hf' : (fun x => inner ℝ ((-f) x) (φ x)) = fun x => -inner ℝ (f x) (φ x) := by
    funext x; simp only [Pi.neg_apply, inner_neg_left]
  have hr : weakEquationRhs ν v φ dφ (-du) (-A) (-F) (-g) =
      fun s x => -weakEquationRhs ν v φ dφ du A F g s x := by
    funext s x; exact weakEquationRhs_neg ν v φ dφ du A F g s x
  change Integrable _ μ ∧ Integrable _ μ ∧
    (∀ s ∈ Set.Ioc a t, Integrable (weakEquationRhs ν v φ dφ (-du) (-A) (-F) (-g) s) μ) ∧
    IntegrableOn (fun s => ∫ x, weakEquationRhs ν v φ dφ (-du) (-A) (-F) (-g) s x ∂μ) (Set.Ioc a t) ∧ _
  refine ⟨by rw [hu']; exact hu.neg, by rw [hf']; exact hf.neg, ?_, ?_, ?_⟩
  · intro s hs'
    rw [hr]
    exact (hs s hs').neg
  · rw [hr]
    simp only [integral_neg]
    convert ht.neg using 1
  · change (∫ x, inner ℝ ((-u) x) (φ x) ∂μ) -
      (∫ x, inner ℝ ((-f) x) (φ x) ∂μ) =
      ∫ s in Set.Ioc a t, ∫ x, weakEquationRhs ν v φ dφ (-du) (-A) (-F) (-g) s x ∂μ
    rw [hu', hf', hr, integral_neg, integral_neg]
    simp only [integral_neg]
    simp only [weakEquationRhs]
    linarith only [he]

theorem coupledWeakIdentity_sub (μ : Measure (Vec 2)) (ν a t : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (u₁ u₂ f₁ f₂ φ : Vec 2 → H)
    (dφ : Fin 2 → Vec 2 → H) (du₁ du₂ : ℝ → Fin 2 → Vec 2 → H)
    (A₁ A₂ F₁ F₂ : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H))
    (g₁ g₂ : ℝ → Vec 2 → H)
    (h₁ : CoupledWeakIdentity μ ν a t v u₁ f₁ φ dφ du₁ A₁ F₁ g₁)
    (h₂ : CoupledWeakIdentity μ ν a t v u₂ f₂ φ dφ du₂ A₂ F₂ g₂) :
    CoupledWeakIdentity μ ν a t v (u₁ - u₂) (f₁ - f₂) φ dφ
      (du₁ - du₂) (A₁ - A₂) (F₁ - F₂) (g₁ - g₂) := by
  simpa only [sub_eq_add_neg] using coupledWeakIdentity_add μ ν a t v
    u₁ (-u₂) f₁ (-f₂) φ dφ du₁ (-du₂) A₁ (-A₂) F₁ (-F₂) g₁ (-g₂) h₁
    (coupledWeakIdentity_neg μ ν a t v u₂ f₂ φ dφ du₂ A₂ F₂ g₂ h₂)
end

/-! A zero native carrier has zero stored readout almost everywhere; replacing
these zero forcing representatives preserves every integrability clause. -/

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem coupledWeakIdentity_forcings_congr (μ : Measure (Vec 2)) (ν a t : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (u f φ : Vec 2 → H) (dφ : Fin 2 → Vec 2 → H)
    (du : ℝ → Fin 2 → Vec 2 → H)
    (A F F' : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)) (g g' : ℝ → Vec 2 → H)
    (hs : CoupledWeakIdentity μ ν a t v u f φ dφ du A F g)
    (hF : ∀ r, F r =ᵐ[μ] F' r) (hg : ∀ r, g r =ᵐ[μ] g' r) :
    CoupledWeakIdentity μ ν a t v u f φ dφ du A F' g' := by
  have hr (r : ℝ) : weakEquationRhs ν v φ dφ du A F g r =ᵐ[μ]
      weakEquationRhs ν v φ dφ du A F' g' r := by
    filter_upwards [hF r, hg r] with z hFz hgz
    simp only [weakEquationRhs, hFz, hgz]
  have ht : (fun r => ∫ z, weakEquationRhs ν v φ dφ du A F g r z ∂μ) =ᵐ[volume.restrict (Set.Ioc a t)]
      (fun r => ∫ z, weakEquationRhs ν v φ dφ du A F' g' r z ∂μ) :=
    Filter.Eventually.of_forall (fun r => integral_congr_ae (hr r))
  rcases hs with ⟨hu, hf, hspace, htime, heq⟩
  refine ⟨hu, hf, fun r hr' => (hspace r hr').congr (hr r), htime.congr ht, ?_⟩
  exact heq.trans (integral_congr_ae ht)

theorem coupledWeakIdentity_zero_forcings (μ : Measure (Vec 2)) (ν a t : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (u f φ : Vec 2 → H) (dφ : Fin 2 → Vec 2 → H)
    (du : ℝ → Fin 2 → Vec 2 → H)
    (A F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H)) (g : ℝ → Vec 2 → H)
    (hs : CoupledWeakIdentity μ ν a t v u f φ dφ du A F g)
    (hF : ∀ r, F r =ᵐ[μ] 0) (hg : ∀ r, g r =ᵐ[μ] 0) :
    CoupledWeakIdentity μ ν a t v u f φ dφ du A 0 0 := by
  exact coupledWeakIdentity_forcings_congr μ ν a t v u f φ dφ du A F 0 g 0 hs hF hg
end

end AVRegularity.CycleWords
end
end
