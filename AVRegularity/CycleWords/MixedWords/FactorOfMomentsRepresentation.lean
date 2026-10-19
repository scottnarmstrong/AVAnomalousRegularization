-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.GaugeJetsCore
public import AVRegularity.CycleWords.MixedWords.FibreDuality
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import Mathlib.Topology.Compactness.DeltaGeneratedSpace

section
@[expose] public noncomputable section
open MeasureTheory Set Filter Topology Metric Homogenization AVRegularity.CycleEvolution
open AVRegularity.CycleWords AVRegularity.Analysis
open scoped Nat
namespace AVRegularity.CycleWords.Assembly

/-! # The gauge jets

`gaugeJetsPiece : GaugeJetsPieceStatement` and `gaugeJets : GaugeJetsStatement`.
Both follow from `gauge_normalized_jet_le`: on a piece of duration `≤ C_H S`, for real `θ` with
`|ξ| ≤ ρ < ξ₀`, `ϖᵏ‖Dᵏ e^Ξ‖ ≤ k! Bᵏ (1 + x_ξ)ᵏ |e^Ξ|`, with `|e^Ξ| ≤ 1 + C_g ρ` on pieces
(`gauge_norm_le_of_real`) and `|e^Ξ| ≤ e^{-c_G x_ξ²}` on complete windows (`ScalarPackage.gauss`).
-/

variable {K : ScalarConstants} {η t0 S0 : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {v : ℝ → Vec 2 → Vec 2}

/-- The base `B ≥ 1` of the normalized gauge jets: it dominates `C_H` times the first-order
phase constant and every phase constant through order `m`. -/
def gaugeJetBase (K : ScalarConstants) (CH ρ : ℝ) (m : ℕ) : ℝ :=
  1 + |CH * ((8 + K.Cw * K.Cg) * (9 + (K.ξ0 / ((K.ξ0 - ρ) / 4)) ^ 2))| +
    ∑ i ∈ Finset.range (m + 1),
      |CH * ((8 + K.Cw * K.Cg) * K.ξ0 ^ 2 * (i : ℝ) ^ i / ((K.ξ0 - ρ) / 4) ^ i)|

theorem one_le_gaugeJetBase (K : ScalarConstants) (CH ρ : ℝ) (m : ℕ) :
    1 ≤ gaugeJetBase K CH ρ m := by
  unfold gaugeJetBase
  have := Finset.sum_nonneg (s := Finset.range (m + 1)) fun i _ =>
    abs_nonneg (CH * ((8 + K.Cw * K.Cg) * K.ξ0 ^ 2 * (i : ℝ) ^ i / ((K.ξ0 - ρ) / 4) ^ i))
  have := abs_nonneg (CH * ((8 + K.Cw * K.Cg) * (9 + (K.ξ0 / ((K.ξ0 - ρ) / 4)) ^ 2)))
  linarith

theorem le_gaugeJetBase_one (K : ScalarConstants) (CH ρ : ℝ) (m : ℕ) :
    |CH * ((8 + K.Cw * K.Cg) * (9 + (K.ξ0 / ((K.ξ0 - ρ) / 4)) ^ 2))| ≤
      gaugeJetBase K CH ρ m := by
  unfold gaugeJetBase
  have := Finset.sum_nonneg (s := Finset.range (m + 1)) fun i _ =>
    abs_nonneg (CH * ((8 + K.Cw * K.Cg) * K.ξ0 ^ 2 * (i : ℝ) ^ i / ((K.ξ0 - ρ) / 4) ^ i))
  linarith

theorem le_gaugeJetBase (K : ScalarConstants) (CH ρ : ℝ) {m i : ℕ} (hi : i ≤ m) :
    |CH * ((8 + K.Cw * K.Cg) * K.ξ0 ^ 2 * (i : ℝ) ^ i / ((K.ξ0 - ρ) / 4) ^ i)| ≤
      gaugeJetBase K CH ρ m := by
  unfold gaugeJetBase
  have h := Finset.single_le_sum (s := Finset.range (m + 1))
    (f := fun i : ℕ => |CH * ((8 + K.Cw * K.Cg) * K.ξ0 ^ 2 * (i : ℝ) ^ i /
      ((K.ξ0 - ρ) / 4) ^ i)|) (fun j _ => abs_nonneg _)
    (Finset.mem_range.2 (show i < m + 1 by omega))
  have := abs_nonneg (CH * ((8 + K.Cw * K.Cg) * (9 + (K.ξ0 / ((K.ξ0 - ρ) / 4)) ^ 2)))
  linarith

/-- The gauge in the plane frequency is `e^Ξ` composed with `fibreEmbed`. -/
theorem gauge_eq_comp (lam : ℕ × ℕ → ℝ → ℂ) (η a b : ℝ) :
    (fun θ => Complex.exp (blockGauge lam η a b θ)) =
      fun θ => (fun ξ => Complex.exp (phaseIntegral lam a b ξ)) (fibreEmbed η θ) := by
  funext θ
  rw [fibreEmbed_apply, blockGauge_eq_phaseIntegral]

/-- The gauge is smooth on the graph disc. -/
theorem gauge_contDiffOn (data : FibreScalarData K η G v t0 S0) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hCg : 0 ≤ K.Cg) (hCw : 0 ≤ K.Cw) (hG : IsCellMetric (fun t _ => G t)) (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ K.Cw) {a b : ℝ} (hab : a ≤ b)
    (m : ℕ) :
    ContDiffOn ℝ m (fun θ => Complex.exp (blockGauge data.lam η a b θ))
      {θ | fibreNorm (planeFibreFrequency η θ) < K.ξ0} := by
  have hU : IsOpen {ζ : Fin 2 → ℂ | fibreNorm ζ < K.ξ0} :=
    isOpen_lt fibreNorm_continuous continuous_const
  have hE : AnalyticOnNhd ℂ (fun ξ => Complex.exp (phaseIntegral data.lam a b ξ))
      {ζ : Fin 2 → ℂ | fibreNorm ζ < K.ξ0} := fun ξ hξ =>
    (phaseIntegral_analyticOnNhd data hη0 hη1 hCg hCw hG hv hw hab ξ hξ).cexp'
  have hEC : ContDiffOn ℂ (⊤ : ℕ∞) (fun ξ => Complex.exp (phaseIntegral data.lam a b ξ))
      {ζ : Fin 2 → ℂ | fibreNorm ζ < K.ξ0} := hE.contDiffOn hU.uniqueDiffOn
  have hset : {θ | fibreNorm (planeFibreFrequency η θ) < K.ξ0} =
      fibreEmbed η ⁻¹' {ζ : Fin 2 → ℂ | fibreNorm ζ < K.ξ0} := by
    ext θ
    simp [fibreEmbed_apply]
  rw [gauge_eq_comp, hset]
  exact ((hEC.restrict_scalars ℝ).comp_continuousLinearMap (fibreEmbed η)).of_le
    (by exact_mod_cast le_top)

/-- **The normalized gauge jets** on a piece: `ϖᵏ‖Dᵏ e^Ξ‖ ≤ k! Bᵏ (1 + x_ξ)ᵏ |e^Ξ|`. -/
theorem gauge_normalized_jet_le (data : FibreScalarData K η G v t0 S0) (hη : 0 < η)
    (hη1 : η ≤ 1) (hCg : 0 ≤ K.Cg) (hCw : 0 ≤ K.Cw) (hG : IsCellMetric (fun t _ => G t))
    (hv : IsCellDrift v) (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ K.Cw)
    {a b S ϖ CH ρ : ℝ} (hab : a ≤ b) (hS : 1 ≤ S) (hϖ : ϖ = Real.sqrt (η / S))
    (hba : b - a ≤ CH * S) (hρ : ρ < K.ξ0) {θ : Vec 2}
    (hθ : fibreNorm (planeFibreFrequency η θ) ≤ ρ) {k m : ℕ} (hk : k ≤ m) :
    ϖ ^ k * ‖iteratedFDeriv ℝ k (fun θ' => Complex.exp (blockGauge data.lam η a b θ')) θ‖ ≤
      k ! * gaugeJetBase K CH ρ m ^ k * (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ k *
        ‖Complex.exp (blockGauge data.lam η a b θ)‖ := by
  set ξ := planeFibreFrequency η θ with hξdef
  set s := fibreNorm ξ with hsdef
  have hs0 : 0 ≤ s := fibreNorm_nonneg ξ
  have hρ0 : 0 ≤ ρ := hs0.trans hθ
  have hS0 : 0 < S := by linarith
  have hsqS : 1 ≤ Real.sqrt S := by rw [Real.one_le_sqrt]; exact hS
  have hsqη : 0 < Real.sqrt η := Real.sqrt_pos.2 hη
  have hϖ' : ϖ = Real.sqrt η / Real.sqrt S := by rw [hϖ, Real.sqrt_div' _ hS0.le]
  have hϖ0 : 0 < ϖ := by rw [hϖ']; positivity
  have hba0 : 0 ≤ b - a := sub_nonneg.2 hab
  have hCH : 0 ≤ CH := by
    rcases le_or_gt 0 CH with h | h
    · exact h
    · nlinarith
  set B := gaugeJetBase K CH ρ m with hBdef
  have hB1 : 1 ≤ B := one_le_gaugeJetBase K CH ρ m
  set x := Real.sqrt (vecDot θ θ) / ϖ with hxdef
  have hx : x = Real.sqrt S * s := by
    rw [hxdef, hsdef, hξdef, fibreNorm_planeFibreFrequency_eq_div hη, hϖ']
    field_simp
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hU : IsOpen {ζ : Fin 2 → ℂ | fibreNorm ζ < K.ξ0} :=
    isOpen_lt fibreNorm_continuous continuous_const
  have hξU : fibreEmbed η θ ∈ {ζ : Fin 2 → ℂ | fibreNorm ζ < K.ξ0} := by
    change fibreNorm (fibreEmbed η θ) < K.ξ0
    rw [fibreEmbed_apply]
    exact hθ.trans_lt hρ
  have hΞ := phaseIntegral_analyticOnNhd data hη.le hη1 hCg hCw hG hv hw hab
  have hE : AnalyticOnNhd ℂ (fun ξ => Complex.exp (phaseIntegral data.lam a b ξ))
      {ζ : Fin 2 → ℂ | fibreNorm ζ < K.ξ0} := fun ξ hξ => (hΞ ξ hξ).cexp'
  -- the phase derivatives at `ξ`
  have hD : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℂ i (phaseIntegral data.lam a b)
      (fibreEmbed η θ)‖ ≤ (B * Real.sqrt S * (1 + x)) ^ i := by
    intro i hi1 hik
    rw [fibreEmbed_apply]
    rcases eq_or_lt_of_le hi1 with h1 | h2
    · subst h1
      have h := phaseIntegral_fderiv_le data hη.le hη1 hCg hCw hG hv hw hab hρ hθ
      rw [pow_one]
      refine h.trans ?_
      set A₁ := (8 + K.Cw * K.Cg) * (9 + (K.ξ0 / ((K.ξ0 - ρ) / 4)) ^ 2) with hA₁
      have hA₁0 : 0 ≤ A₁ := by positivity
      have hB' : CH * A₁ ≤ B := (le_abs_self _).trans (le_gaugeJetBase_one K CH ρ m)
      calc (b - a) * A₁ * s ≤ CH * S * A₁ * s :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hba hA₁0) hs0
        _ = CH * A₁ * Real.sqrt S * (Real.sqrt S * s) := by
            have hSS : Real.sqrt S * Real.sqrt S = S := Real.mul_self_sqrt hS0.le
            rw [show CH * A₁ * Real.sqrt S * (Real.sqrt S * s) =
              CH * A₁ * (Real.sqrt S * Real.sqrt S) * s by ring, hSS]
            ring
        _ = CH * A₁ * Real.sqrt S * x := by rw [hx]
        _ ≤ B * Real.sqrt S * (1 + x) := by
            have h3 : 0 ≤ Real.sqrt S := Real.sqrt_nonneg S
            have h4 : CH * A₁ * Real.sqrt S * x ≤ B * Real.sqrt S * x :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hB' h3) hx0
            have h5 : B * Real.sqrt S * x ≤ B * Real.sqrt S * (1 + x) :=
              mul_le_mul_of_nonneg_left (by linarith) (by positivity)
            linarith
    · have h := phaseIntegral_iteratedFDeriv_le data hη.le hη1 hCg hCw hG hv hw hab hρ0 hρ i hθ
      refine h.trans ?_
      set Ai := (8 + K.Cw * K.Cg) * K.ξ0 ^ 2 * (i : ℝ) ^ i / ((K.ξ0 - ρ) / 4) ^ i with hAi
      have hAi0 : 0 ≤ Ai := by
        have : 0 < (K.ξ0 - ρ) / 4 := by linarith
        positivity
      have hB' : CH * Ai ≤ B := (le_abs_self _).trans (le_gaugeJetBase K CH ρ (hik.trans hk))
      have heq : (b - a) * ((8 + K.Cw * K.Cg) * K.ξ0 ^ 2) * (i : ℝ) ^ i /
          ((K.ξ0 - ρ) / 4) ^ i = (b - a) * Ai := by rw [hAi]; ring
      rw [heq]
      have hSi : S ≤ Real.sqrt S ^ i := by
        have : Real.sqrt S ^ 2 ≤ Real.sqrt S ^ i := pow_le_pow_right₀ hsqS (by omega)
        rwa [Real.sq_sqrt hS0.le] at this
      have hBi : B ≤ B ^ i := le_self_pow₀ hB1 (by omega)
      have hxi : 1 ≤ (1 + x) ^ i := one_le_pow₀ (by linarith)
      calc (b - a) * Ai ≤ CH * S * Ai := mul_le_mul_of_nonneg_right hba hAi0
        _ = CH * Ai * S := by ring
        _ ≤ B * S := mul_le_mul_of_nonneg_right hB' hS0.le
        _ ≤ B ^ i * Real.sqrt S ^ i := mul_le_mul hBi hSi hS0.le (by positivity)
        _ ≤ B ^ i * Real.sqrt S ^ i * (1 + x) ^ i := le_mul_of_one_le_right (by positivity) hxi
        _ = (B * Real.sqrt S * (1 + x)) ^ i := by rw [mul_pow, mul_pow]
  -- Faà di Bruno and the real composition
  have hF := norm_iteratedFDeriv_cexp_comp_le hU hΞ hξU k hD
  have hR := norm_iteratedFDeriv_comp_clm_le hU hE (fibreEmbed η) hξU k
  have hL : ‖fibreEmbed η‖ ^ k ≤ (Real.sqrt η)⁻¹ ^ k :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_fibreEmbed_le hη) k
  rw [gauge_eq_comp]
  have hexp : ‖Complex.exp (blockGauge data.lam η a b θ)‖ =
      ‖Complex.exp (phaseIntegral data.lam a b (fibreEmbed η θ))‖ := by
    rw [fibreEmbed_apply, blockGauge_eq_phaseIntegral]
  rw [hexp]
  set e := ‖Complex.exp (phaseIntegral data.lam a b (fibreEmbed η θ))‖ with he
  have he0 : 0 ≤ e := norm_nonneg _
  have hscale : ϖ ^ k * (Real.sqrt η)⁻¹ ^ k * Real.sqrt S ^ k = 1 := by
    rw [hϖ', ← mul_pow, ← mul_pow]
    rw [show Real.sqrt η / Real.sqrt S * (Real.sqrt η)⁻¹ * Real.sqrt S = 1 by
      field_simp]
    simp
  calc ϖ ^ k * ‖iteratedFDeriv ℝ k
        (fun θ' => (fun ξ => Complex.exp (phaseIntegral data.lam a b ξ)) (fibreEmbed η θ')) θ‖
      ≤ ϖ ^ k * (‖iteratedFDeriv ℂ k (fun ξ => Complex.exp (phaseIntegral data.lam a b ξ))
          (fibreEmbed η θ)‖ * ‖fibreEmbed η‖ ^ k) :=
        mul_le_mul_of_nonneg_left hR (by positivity)
    _ ≤ ϖ ^ k * ((k ! * e * (B * Real.sqrt S * (1 + x)) ^ k) * (Real.sqrt η)⁻¹ ^ k) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul hF hL (by positivity) (by positivity))
          (by positivity)
    _ = k ! * B ^ k * (1 + x) ^ k * e * (ϖ ^ k * (Real.sqrt η)⁻¹ ^ k * Real.sqrt S ^ k) := by
        rw [mul_pow, mul_pow]
        ring
    _ = k ! * B ^ k * (1 + x) ^ k * e := by rw [hscale, mul_one]

/-- **Gauge jets on a piece.** -/
theorem gaugeJetsPiece : GaugeJetsPieceStatement := by
  intro K m CH ρ hρ
  refine ⟨(m ! : ℝ) * gaugeJetBase K CH ρ m ^ m * (1 + |K.Cg| * |ρ|), ?_, ?_⟩
  · have := one_le_gaugeJetBase K CH ρ m
    positivity
  intro η S t₀ Sw ϖ a b G v reg pkg hη hη1 hS hϖ hG hv hw hta hab hbt hba
  have hCg : 0 ≤ K.Cg := pkg.consts_pos.2.2.2.1.le
  have hCw : 0 ≤ K.Cw :=
    (by positivity : (0 : ℝ) ≤ Real.sqrt η * Real.sqrt (∑ i, v 0 0 i ^ 2)).trans (hw 0 0)
  refine ⟨gauge_contDiffOn pkg.actual hη.le hη1 hCg hCw hG hv hw hab m, ?_⟩
  intro θ hθ k hk
  have h := gauge_normalized_jet_le pkg.actual hη hη1 hCg hCw hG hv hw hab hS hϖ hba hρ hθ hk
  refine h.trans ?_
  have hρ0 : 0 ≤ ρ := (fibreNorm_nonneg _).trans hθ
  have hB1 := one_le_gaugeJetBase K CH ρ m
  have hexp : ‖Complex.exp (blockGauge pkg.actual.lam η a b θ)‖ ≤ 1 + |K.Cg| * |ρ| := by
    have h1 := gauge_norm_le_of_real pkg.actual (planeFibreFrequency_im η θ) (hθ.trans_lt hρ)
      hCg hab
    rw [abs_of_nonneg hCg, abs_of_nonneg hρ0]
    refine h1.trans ?_
    have := mul_le_mul_of_nonneg_left hθ hCg
    linarith
  have hk! : (k ! : ℝ) ≤ m ! := by exact_mod_cast Nat.factorial_le hk
  have hBk : gaugeJetBase K CH ρ m ^ k ≤ gaugeJetBase K CH ρ m ^ m := pow_le_pow_right₀ hB1 hk
  have hx : 0 ≤ (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ k := by
    have : 0 ≤ Real.sqrt (vecDot θ θ) / ϖ := by
      rw [hϖ]
      positivity
    positivity
  calc (k ! : ℝ) * gaugeJetBase K CH ρ m ^ k * (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ k *
        ‖Complex.exp (blockGauge pkg.actual.lam η a b θ)‖
      ≤ (m ! : ℝ) * gaugeJetBase K CH ρ m ^ m * (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ k *
          (1 + |K.Cg| * |ρ|) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul hk! hBk (by positivity)
          (by positivity)) hx) hexp (norm_nonneg _) (by positivity)
    _ = (m ! : ℝ) * gaugeJetBase K CH ρ m ^ m * (1 + |K.Cg| * |ρ|) *
          (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ k := by ring

/-- **Gauge jets with complete-window damping.** -/
theorem gaugeJets : GaugeJetsStatement := by
  intro K m
  by_cases hK : 0 < K.cGauss ∧ 2 * K.ξlo < K.ξ0 ∧ 0 < K.ξlo
  · refine ⟨(m ! : ℝ) * gaugeJetBase K 1 (2 * K.ξlo) m ^ m, K.cGauss, ?_, hK.1, ?_⟩
    · have := one_le_gaugeJetBase K 1 (2 * K.ξlo) m
      positivity
    intro η S t₀ ϖ G v reg pkg hη hη1 hS hϖ hG hv hw
    have hCg : 0 ≤ K.Cg := pkg.consts_pos.2.2.2.1.le
    have hCw : 0 ≤ K.Cw :=
      (by positivity : (0 : ℝ) ≤ Real.sqrt η * Real.sqrt (∑ i, v 0 0 i ^ 2)).trans (hw 0 0)
    have hS0 : 0 < S := by linarith
    have hab : t₀ ≤ t₀ + S := by linarith
    refine ⟨gauge_contDiffOn pkg.actual hη.le hη1 hCg hCw hG hv hw hab m, ?_⟩
    intro θ hθ k hk
    have h := gauge_normalized_jet_le pkg.actual hη hη1 hCg hCw hG hv hw hab hS hϖ
      (CH := 1) (by linarith) hK.2.1 hθ hk
    refine h.trans ?_
    have hB1 := one_le_gaugeJetBase K 1 (2 * K.ξlo) m
    -- the Gaussian
    have hgauss := (pkg.gauss (planeFibreFrequency η θ) (planeFibreFrequency_im η θ) hθ).1
    have hexp : ‖Complex.exp (blockGauge pkg.actual.lam η t₀ (t₀ + S) θ)‖ ≤
        Real.exp (-K.cGauss * (vecDot θ θ / ϖ ^ 2)) := by
      have hv0 : 0 ≤ vecDot θ θ := Finset.sum_nonneg fun i _ => mul_self_nonneg _
      rw [Complex.norm_exp]
      refine Real.exp_le_exp.2 (hgauss.trans (le_of_eq ?_))
      rw [fibreNorm_planeFibreFrequency_eq_div hη, hϖ, div_pow, Real.sq_sqrt hv0,
        Real.sq_sqrt hη.le, Real.sq_sqrt (div_nonneg hη.le hS0.le)]
      field_simp
    have hk! : (k ! : ℝ) ≤ m ! := by exact_mod_cast Nat.factorial_le hk
    have hBk : gaugeJetBase K 1 (2 * K.ξlo) m ^ k ≤ gaugeJetBase K 1 (2 * K.ξlo) m ^ m :=
      pow_le_pow_right₀ hB1 hk
    have hx : 0 ≤ (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ k := by
      have : 0 ≤ Real.sqrt (vecDot θ θ) / ϖ := by
        rw [hϖ]
        positivity
      positivity
    calc (k ! : ℝ) * gaugeJetBase K 1 (2 * K.ξlo) m ^ k * (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ k *
          ‖Complex.exp (blockGauge pkg.actual.lam η t₀ (t₀ + S) θ)‖
        ≤ (m ! : ℝ) * gaugeJetBase K 1 (2 * K.ξlo) m ^ m *
            (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ k *
            Real.exp (-K.cGauss * (vecDot θ θ / ϖ ^ 2)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul hk! hBk (by positivity)
            (by positivity)) hx) hexp (norm_nonneg _) (by positivity)
      _ = _ := rfl
  · refine ⟨1, 1, one_pos, one_pos, ?_⟩
    intro η S t₀ ϖ G v reg pkg
    exact absurd ⟨pkg.consts_pos.2.2.2.2.1, pkg.consts_pos.2.2.1, pkg.consts_pos.2.1⟩ hK

end AVRegularity.CycleWords.Assembly
end
end

section
section
/-! Buffered fast-part replacement from the original three package replacement fields. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-- One region, entrance and exit with the literal quiet replacement premises. -/
structure QuietFastFrame (K : ScalarConstants) (ρ : ℝ) where
  hρ : ρ < K.ξ0
  η : ℝ
  t₀ : ℝ
  S : ℝ
  ϖ : ℝ
  G : ℝ → Matrix (Fin 2) (Fin 2) ℝ
  v : ℝ → Vec 2 → Vec 2
  reg : BlockRegions
  pkg : CoreScalarPackage K η G v t₀ S ϖ reg
  hη : 0 < η
  hη1 : η ≤ 1
  hG : IsCellMetric (fun t _ => G t)
  hv : IsCellDrift v
  hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ K.Cw
  p : Fin reg.P
  ξ : Fin 2 → ℂ
  hre : ∀ i, (ξ i).im = 0
  hξ : fibreNorm ξ ≤ ρ
  s : ℝ
  t : ℝ
  hs : reg.lo p ≤ s
  hsh : s ≤ reg.hi p
  hst : s ≤ t
  ht : t ≤ reg.hi p + reg.buffer
  D : ℝ → RawJet2 1 ℂ
  hD : IsCellSolution (Icc s t) (fibreCoefficients η G v ξ (fun _ => 0))
    (fun _ _ => 0) (fun _ _ => 0) D

theorem QuietFastFrame.Cw_nonneg {K : ScalarConstants} {ρ : ℝ} (F : QuietFastFrame K ρ) :
    0 ≤ K.Cw := (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans (F.hw 0 0)

/-- The original entrance value is L2; no replacement of that representative is made. -/
theorem QuietFastFrame.entrance {K : ScalarConstants} {ρ : ℝ} (F : QuietFastFrame K ρ) :
    MemLp (cellValue F.D F.s) 2 (volume.restrict AVenhance.unitCube) :=
  (F.hD.2.2.1 F.s ⟨le_rfl, F.hst⟩).1

end AVRegularity.CycleWords.Assembly
end
end

section
/-! The two analytic ingredients of the moment-to-retained-factor reduction. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.CycleWords.Assembly
universe u v

/-- Retained Fourier representation and the globally smooth, gauged amplitude pair. -/
def FactorMomentConclusion {ι : Type u} [Fintype ι] {h : ι → Type v}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ) (m s P : ℕ) (ϖ η ξ0 L Bg B : ℝ) (χr mc : Vec 2 → ℝ)
    (φ g : ∀ x, Vec 2 → h x) (Φ : Vec 2 → ℂ) : Prop :=
  (∀ x, Integrable (g x)) ∧
  (∀ r : ℝ, 0 < r → (∀ θ : Vec 2, r ^ 2 < vecDot θ θ → mc θ = 0) → ∀ x,
    IsRetainedAmplitude (fourierCutoff mc (g x)) r (cutoffCosAmplitude mc (g x))
      (cutoffSinAmplitude mc (g x))) ∧
  (∀ x, ContDiff ℝ m (cutoffCosAmplitude mc (g x)) ∧ ContDiff ℝ m (cutoffSinAmplitude mc (g x))) ∧
  ∃ Ac As : ∀ x, Vec 2 → h x,
    (∀ x, ContDiff ℝ m (Ac x) ∧ ContDiff ℝ m (As x)) ∧
    (∀ θ : Vec 2, fibreNorm (planeFibreFrequency η θ) < ξ0 → ∀ x,
      cutoffCosAmplitude mc (g x) θ = (Complex.exp (Φ θ)).re • Ac x θ +
        (Complex.exp (Φ θ)).im • As x θ ∧
      cutoffSinAmplitude mc (g x) θ = (Complex.exp (Φ θ)).re • As x θ -
        (Complex.exp (Φ θ)).im • Ac x θ) ∧
    ∀ θ : Vec 2, fibreNorm (planeFibreFrequency η θ) < ξ0 →
      ampDerivNorm π m ϖ Ac As θ ≤
        ENNReal.ofReal (L * Bg * B * (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ (P + m)) *
          ∑ α ∈ momentIndices (m + s),
            ENNReal.ofReal (ϖ ^ (α.1 + α.2) / ((α.1.factorial * α.2.factorial : ℕ) : ℝ)) *
              blochFibreDerivNorm π (fun θ' => χr ((Real.sqrt η)⁻¹ • θ')) α φ θ

/-- Pure Fourier and cutoff calculus. All PDE information is the pointwise moment bound;
the inverse-gauge jet bound is an independently discharged analytic input. -/
def FactorMomentCalculusStatement : Prop :=
  ∀ (m s P : ℕ) (ξ0 ρ : ℝ) (χ ψ : Vec 2 → ℝ), ρ < ξ0 →
    ContDiff ℝ (⊤ : ℕ∞) χ → (∀ ξ, ρ ≤ Real.sqrt (vecDot ξ ξ) → χ ξ = 0) →
    ContDiff ℝ (⊤ : ℕ∞) ψ → (∀ k : ℕ, ∃ B : ℝ, ∀ θ, ‖iteratedFDeriv ℝ k ψ θ‖ ≤ B) →
  ∀ χr χ₃ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) χr →
    (∀ k : ℕ, ∃ B : ℝ, ∀ ξ, ‖iteratedFDeriv ℝ k χr ξ‖ ≤ B) → ContDiff ℝ (⊤ : ℕ∞) χ₃ →
    (∀ k : ℕ, ∃ B : ℝ, ∀ ξ, ‖iteratedFDeriv ℝ k χ₃ ξ‖ ≤ B) →
    (∀ ξ, χ ξ = χr ξ ^ (m + s + 1) * χ₃ ξ) →
  ∃ L : ℝ, 0 < L ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (π : ι → ℝ) (hπ : ∀ x, 0 < π x) (η ϖ Bg B : ℝ),
    0 < η → 0 < ϖ → ϖ ≤ 1 → ϖ / Real.sqrt η ≤ 1 → 0 ≤ Bg → 0 ≤ B →
  ∀ (φ g : ∀ x, Vec 2 → h x), (∀ x, StronglyMeasurable (φ x) ∧ HasCompactSupport (φ x)) →
    (∀ x (β : ℕ × ℕ), Integrable (fun y => (y 0 ^ β.1 * y 1 ^ β.2) • g x y)) →
  ∀ Φ : Vec 2 → ℂ,
    ContDiffOn ℝ m (fun θ => Complex.exp (-Φ θ)) {θ | fibreNorm (planeFibreFrequency η θ) < ξ0} →
    (∀ θ : Vec 2, fibreNorm (planeFibreFrequency η θ) ≤ ρ → ∀ l ≤ m,
      ϖ ^ l * ‖iteratedFDeriv ℝ l (fun θ' => Complex.exp (-Φ θ')) θ‖ ≤
        Bg * (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ l * Real.exp (-(Φ θ).re)) →
    (∀ θ : Vec 2, fibreNorm (planeFibreFrequency η θ) ≤ ρ → ∀ β ∈ momentIndices m,
      momentAmpNorm π ϖ β g θ ≤ ENNReal.ofReal (Real.exp (Φ θ).re * B *
        (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ P) * datumJets π ϖ (β.1 + β.2 + s) φ θ) →
    FactorMomentConclusion π m s P ϖ η ξ0 L Bg B χr (pieceCutoff χ ψ η) φ g Φ

/-- The inverse gauge has uniform normalized jets on every strict subdisc, for a piece. -/
def FactorInverseGaugeStatement : Prop :=
  ∀ (K : ScalarConstants) (m : ℕ) (CH ρ : ℝ), ρ < K.ξ0 →
  ∃ Bg : ℝ, 0 < Bg ∧
  ∀ {η t₀ Sw : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    (data : FibreScalarData K η G v t₀ Sw),
    0 < η → η ≤ 1 → 0 ≤ K.Cg → 0 ≤ K.Cw → IsCellMetric (fun t _ => G t) → IsCellDrift v →
    (∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ K.Cw) →
  ∀ (a b S ϖ : ℝ), a ≤ b → 1 ≤ S → ϖ = Real.sqrt (η / S) → b - a ≤ CH * S →
    ContDiffOn ℝ m (fun θ => Complex.exp (-blockGauge data.lam η a b θ))
      {θ | fibreNorm (planeFibreFrequency η θ) < K.ξ0} ∧
    ∀ θ : Vec 2, fibreNorm (planeFibreFrequency η θ) ≤ ρ → ∀ l ≤ m,
      ϖ ^ l * ‖iteratedFDeriv ℝ l (fun θ' => Complex.exp (-blockGauge data.lam η a b θ')) θ‖ ≤
        Bg * (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ l * Real.exp (-(blockGauge data.lam η a b θ).re)

end AVRegularity.CycleWords.Assembly
end
end

section
/-! Parameter integrals of sine and cosine for endpoints with all polynomial moments. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set Filter Topology AVRegularity.Sobolev
namespace AVRegularity.CycleWords.Assembly
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every ordinary polynomial moment is a Bochner integrable vector field. -/
def FactorHasAllMoments (g : Vec 2 → E) : Prop :=
  ∀ β : ℕ × ℕ, Integrable (fun y => (y 0 ^ β.1 * y 1 ^ β.2) • g y)

theorem FactorHasAllMoments.integrable {g : Vec 2 → E} (hg : FactorHasAllMoments g) :
    Integrable g := by
  simpa only [pow_zero, one_mul, one_smul] using hg (0, 0)

theorem FactorHasAllMoments.coord {g : Vec 2 → E} (hg : FactorHasAllMoments g) (i : Fin 2) :
    FactorHasAllMoments (fun y => y i • g y) := by
  intro β
  fin_cases i
  · convert hg (β.1 + 1, β.2) using 1
    funext y
    simp only [smul_smul, pow_succ, Fin.zero_eta]
    congr 1
    ring
  · convert hg (β.1, β.2 + 1) using 1
    funext y
    simp only [smul_smul, pow_succ, Fin.mk_one]
    congr 1
    ring

theorem FactorHasAllMoments.neg {g : Vec 2 → E} (hg : FactorHasAllMoments g) :
    FactorHasAllMoments (-g) := by
  intro β
  convert (hg β).neg using 1
  funext y
  exact smul_neg _ _

variable [CompleteSpace E]

/-- The full-space trigonometric integral, with the Fourier variable in the second slot. -/
def factorPhasePair (A B : Vec 2 → E) (θ : Vec 2) : E :=
  ∫ y, Real.cos (vecDot y θ) • A y + Real.sin (vecDot y θ) • B y

omit [CompleteSpace E] in
private theorem factorPhase_integrable {g : Vec 2 → E} (hg : Integrable g)
    (ψ : ℝ → ℝ) (hψ : Continuous ψ) (hb : ∀ z, |ψ z| ≤ 1) (θ : Vec 2) :
    Integrable (fun y => ψ (vecDot y θ) • g y) := by
  apply hg.norm.mono'
    ((hψ.comp (by unfold vecDot; fun_prop)).aestronglyMeasurable.smul hg.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun y => by
    change ‖ψ (vecDot y θ) • g y‖ ≤ ‖g y‖
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (hb _))

omit [CompleteSpace E] in
private theorem factorPhase_pair_integrable {A B : Vec 2 → E} (hA : Integrable A) (hB : Integrable B)
    (θ : Vec 2) : Integrable (fun y => Real.cos (vecDot y θ) • A y + Real.sin (vecDot y θ) • B y) :=
  (factorPhase_integrable hA Real.cos Real.continuous_cos Real.abs_cos_le_one θ).add
    (factorPhase_integrable hB Real.sin Real.continuous_sin Real.abs_sin_le_one θ)

omit [CompleteSpace E] in
private theorem factorPhase_deriv_integrable {A B : Vec 2 → E}
    (hA : FactorHasAllMoments A) (hB : FactorHasAllMoments B) (θ : Vec 2) :
    Integrable (fun y => ampIntegrandDeriv A B θ y) := by
  unfold ampIntegrandDeriv
  refine integrable_finsetSum (f := fun i y => coordSmulRight (E := E) i
    (Real.cos (vecDot y θ) • derivAmpA i B y + Real.sin (vecDot y θ) • derivAmpB i A y))
    Finset.univ (fun i _ => ?_)
  exact (coordSmulRight (E := E) i).integrable_comp (factorPhase_pair_integrable
    (hB.coord i).integrable (hA.coord i).neg.integrable θ)

omit [CompleteSpace E] in
private theorem factorPhase_deriv_bound (A B : Vec 2 → E) (θ y : Vec 2) :
    ‖ampIntegrandDeriv A B θ y‖ ≤
      ∑ i : Fin 2, (‖derivAmpA i B y‖ + ‖derivAmpB i A y‖) := by
  unfold ampIntegrandDeriv
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  refine (norm_coordSmulRight_le _ _).trans ((norm_add_le _ _).trans (add_le_add ?_ ?_))
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _)
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one _)

/-- Differentiation under the full-space integral is justified by the first moments. -/
theorem factorPhasePair_hasFDerivAt {A B : Vec 2 → E}
    (hA : FactorHasAllMoments A) (hB : FactorHasAllMoments B) (θ : Vec 2) :
    HasFDerivAt (factorPhasePair A B)
      (∑ i : Fin 2, coordSmulRight i (factorPhasePair (derivAmpA i B) (derivAmpB i A) θ)) θ := by
  have hi (i : Fin 2) : Integrable (fun y => coordSmulRight (E := E) i
      (Real.cos (vecDot y θ) • derivAmpA i B y + Real.sin (vecDot y θ) • derivAmpB i A y)) :=
    (coordSmulRight (E := E) i).integrable_comp
      (factorPhase_pair_integrable (hB.coord i).integrable (hA.coord i).neg.integrable θ)
  have he : (∫ y, ampIntegrandDeriv A B θ y) =
      ∑ i : Fin 2, coordSmulRight i (factorPhasePair (derivAmpA i B) (derivAmpB i A) θ) := by
    rw [show (fun y => ampIntegrandDeriv A B θ y) = (fun y => ∑ i : Fin 2,
      coordSmulRight i (Real.cos (vecDot y θ) • derivAmpA i B y +
        Real.sin (vecDot y θ) • derivAmpB i A y)) from rfl, integral_finsetSum _ (fun i _ => hi i)]
    apply Finset.sum_congr rfl
    intro i _
    exact (coordSmulRight (E := E) i).integral_comp_comm
      (factorPhase_pair_integrable (hB.coord i).integrable (hA.coord i).neg.integrable θ)
  rw [← he]
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (s := Set.univ)
    (bound := fun y => ∑ i : Fin 2, (‖derivAmpA i B y‖ + ‖derivAmpB i A y‖)) Filter.univ_mem
    (Filter.Eventually.of_forall (fun θ' => (factorPhase_pair_integrable hA.integrable hB.integrable θ').aestronglyMeasurable))
    (factorPhase_pair_integrable hA.integrable hB.integrable θ)
    (factorPhase_deriv_integrable hA hB θ).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun y θ' _ => factorPhase_deriv_bound A B θ' y))
    (integrable_finsetSum _ (fun i _ => (hB.coord i).integrable.norm.add (hA.coord i).neg.integrable.norm))
    (Filter.Eventually.of_forall (fun y θ' _ => hasFDerivAt_ampIntegrand A B y θ'))

/-- All polynomial moments imply smoothness of both trigonometric amplitudes. -/
theorem factorPhasePair_contDiff : ∀ (m : ℕ) {A B : Vec 2 → E},
    FactorHasAllMoments A → FactorHasAllMoments B → ContDiff ℝ m (factorPhasePair A B)
  | 0, A, B, hA, hB => by
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.mpr (fun θ => (factorPhasePair_hasFDerivAt hA hB θ).continuousAt)
  | m + 1, A, B, hA, hB => by
    rw [Nat.cast_succ]
    apply contDiff_succ_iff_fderiv.mpr
    refine ⟨fun θ => (factorPhasePair_hasFDerivAt hA hB θ).differentiableAt,
      fun h => absurd h (by simp), ?_⟩
    rw [show fderiv ℝ (factorPhasePair A B) = fun θ =>
      ∑ i : Fin 2, coordSmulRight i (factorPhasePair (derivAmpA i B) (derivAmpB i A) θ) from
      funext (fun θ => (factorPhasePair_hasFDerivAt hA hB θ).fderiv)]
    exact ContDiff.sum (fun i _ => (coordSmulRight (E := E) i).contDiff.comp
      (factorPhasePair_contDiff m (hB.coord i) (hA.coord i).neg))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] in
private theorem factorVecDot_comm (θ y : Vec 2) : vecDot θ y = vecDot y θ := by
  unfold vecDot
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

omit [CompleteSpace E] in
/-- The zero field has every integrable moment. -/
theorem factorHasAllMoments_zero : FactorHasAllMoments (0 : Vec 2 → E) := by
  intro β
  simp only [Pi.zero_apply, smul_zero]
  exact integrable_zero _ _ _

/-- Smoothness of the cosine transform follows from all polynomial moments. -/
theorem factorCos_contDiff {g : Vec 2 → E} (hg : FactorHasAllMoments g) (m : ℕ) :
    ContDiff ℝ m (fun θ => ∫ y, Real.cos (vecDot θ y) • g y) := by
  have he : (fun θ => ∫ y, Real.cos (vecDot θ y) • g y) = factorPhasePair g 0 := by
    funext θ
    simp only [factorPhasePair, Pi.zero_apply, smul_zero, add_zero, factorVecDot_comm θ]
  rw [he]
  exact factorPhasePair_contDiff m hg factorHasAllMoments_zero

/-- Smoothness of the sine transform follows from all polynomial moments. -/
theorem factorSin_contDiff {g : Vec 2 → E} (hg : FactorHasAllMoments g) (m : ℕ) :
    ContDiff ℝ m (fun θ => ∫ y, Real.sin (vecDot θ y) • g y) := by
  have he : (fun θ => ∫ y, Real.sin (vecDot θ y) • g y) = factorPhasePair 0 g := by
    funext θ
    simp only [factorPhasePair, Pi.zero_apply, smul_zero, zero_add, factorVecDot_comm θ]
  rw [he]
  exact factorPhasePair_contDiff m factorHasAllMoments_zero hg

/-- A smooth multiplier preserves smoothness of the trigonometric transform. -/
theorem factorCutoff_contDiff {g : Vec 2 → E} (hg : FactorHasAllMoments g)
    {mc : Vec 2 → ℝ} {m : ℕ} (hm : ContDiff ℝ m mc) :
    ContDiff ℝ m (cutoffCosAmplitude mc g) ∧ ContDiff ℝ m (cutoffSinAmplitude mc g) := by
  exact ⟨(contDiff_const.mul hm).smul (factorCos_contDiff hg m),
    (contDiff_const.mul hm).smul (factorSin_contDiff hg m)⟩

end AVRegularity.CycleWords.Assembly
end
end
end

section
section
/-! Inverse-gauge jets, by the same phase derivative estimates as the forward gauge. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set Filter Topology Metric AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CycleWords AVRegularity.Analysis
open scoped Nat
namespace AVRegularity.CycleWords.Assembly
variable {K : ScalarConstants} {η t0 S0 : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {v : ℝ → Vec 2 → Vec 2}

private theorem factorInverseGauge_eq_comp (lam : ℕ × ℕ → ℝ → ℂ) (η a b : ℝ) :
    (fun θ => Complex.exp (-blockGauge lam η a b θ)) =
      (fun θ => (fun ξ => Complex.exp (-phaseIntegral lam a b ξ)) (fibreEmbed η θ)) := by
  funext θ
  rw [fibreEmbed_apply, blockGauge_eq_phaseIntegral]

theorem factorInverseGauge_contDiffOn (data : FibreScalarData K η G v t0 S0) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hCg : 0 ≤ K.Cg) (hCw : 0 ≤ K.Cw) (hG : IsCellMetric (fun t _ => G t)) (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ K.Cw) {a b : ℝ} (hab : a ≤ b)
    (m : ℕ) :
    ContDiffOn ℝ m (fun θ => Complex.exp (-blockGauge data.lam η a b θ))
      {θ | fibreNorm (planeFibreFrequency η θ) < K.ξ0} := by
  have hU : IsOpen {ζ : Fin 2 → ℂ | fibreNorm ζ < K.ξ0} :=
    isOpen_lt fibreNorm_continuous continuous_const
  have hE : AnalyticOnNhd ℂ (fun ξ => Complex.exp (-phaseIntegral data.lam a b ξ))
      {ζ : Fin 2 → ℂ | fibreNorm ζ < K.ξ0} := fun ξ hξ =>
    ((phaseIntegral_analyticOnNhd data hη0 hη1 hCg hCw hG hv hw hab ξ hξ).neg).cexp'
  have hEC : ContDiffOn ℂ (⊤ : ℕ∞) (fun ξ => Complex.exp (-phaseIntegral data.lam a b ξ))
      {ζ : Fin 2 → ℂ | fibreNorm ζ < K.ξ0} := hE.contDiffOn hU.uniqueDiffOn
  have hset : {θ | fibreNorm (planeFibreFrequency η θ) < K.ξ0} =
      fibreEmbed η ⁻¹' {ζ : Fin 2 → ℂ | fibreNorm ζ < K.ξ0} := by
    ext θ
    simp [fibreEmbed_apply]
  rw [factorInverseGauge_eq_comp, hset]
  exact ((hEC.restrict_scalars ℝ).comp_continuousLinearMap (fibreEmbed η)).of_le
    (by exact_mod_cast le_top)

theorem factorInverseGauge_normalized_jet_le (data : FibreScalarData K η G v t0 S0) (hη : 0 < η)
    (hη1 : η ≤ 1) (hCg : 0 ≤ K.Cg) (hCw : 0 ≤ K.Cw) (hG : IsCellMetric (fun t _ => G t))
    (hv : IsCellDrift v) (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ K.Cw)
    {a b S ϖ CH ρ : ℝ} (hab : a ≤ b) (hS : 1 ≤ S) (hϖ : ϖ = Real.sqrt (η / S))
    (hba : b - a ≤ CH * S) (hρ : ρ < K.ξ0) {θ : Vec 2}
    (hθ : fibreNorm (planeFibreFrequency η θ) ≤ ρ) {k m : ℕ} (hk : k ≤ m) :
    ϖ ^ k * ‖iteratedFDeriv ℝ k (fun θ' => Complex.exp (-blockGauge data.lam η a b θ')) θ‖ ≤
      k ! * gaugeJetBase K CH ρ m ^ k * (1 + Real.sqrt (vecDot θ θ) / ϖ) ^ k *
        ‖Complex.exp (-blockGauge data.lam η a b θ)‖ := by
  set ξ := planeFibreFrequency η θ with hξdef
  set s := fibreNorm ξ with hsdef
  have hs0 : 0 ≤ s := fibreNorm_nonneg ξ
  have hρ0 : 0 ≤ ρ := hs0.trans hθ
  have hS0 : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have hsqS : 1 ≤ Real.sqrt S := by rw [Real.one_le_sqrt]; exact hS
  have hsqη : 0 < Real.sqrt η := Real.sqrt_pos.2 hη
  have hϖ' : ϖ = Real.sqrt η / Real.sqrt S := by rw [hϖ, Real.sqrt_div' _ hS0.le]
  have hϖ0 : 0 < ϖ := by rw [hϖ']; positivity
  have hba0 : 0 ≤ b - a := sub_nonneg.2 hab
  have hCH : 0 ≤ CH := by
    by_contra hc
    have hneg : CH * S < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hc) hS0
    exact not_lt_of_ge (hba0.trans hba) hneg
  set B := gaugeJetBase K CH ρ m with hBdef
  have hB1 : 1 ≤ B := one_le_gaugeJetBase K CH ρ m
  set x := Real.sqrt (vecDot θ θ) / ϖ with hxdef
  have hx : x = Real.sqrt S * s := by
    rw [hxdef, hsdef, hξdef, fibreNorm_planeFibreFrequency_eq_div hη, hϖ']
    field_simp
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hU : IsOpen {ζ : Fin 2 → ℂ | fibreNorm ζ < K.ξ0} :=
    isOpen_lt fibreNorm_continuous continuous_const
  have hξU : fibreEmbed η θ ∈ {ζ : Fin 2 → ℂ | fibreNorm ζ < K.ξ0} := by
    change fibreNorm (fibreEmbed η θ) < K.ξ0
    rw [fibreEmbed_apply]
    exact hθ.trans_lt hρ
  have hΞ := phaseIntegral_analyticOnNhd data hη.le hη1 hCg hCw hG hv hw hab
  have hE : AnalyticOnNhd ℂ (fun ξ => Complex.exp (-phaseIntegral data.lam a b ξ))
      {ζ : Fin 2 → ℂ | fibreNorm ζ < K.ξ0} := fun ξ hξ => ((hΞ ξ hξ).neg).cexp'
  -- the phase derivatives at `ξ`
  have hD : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℂ i (phaseIntegral data.lam a b)
      (fibreEmbed η θ)‖ ≤ (B * Real.sqrt S * (1 + x)) ^ i := by
    intro i hi1 hik
    rw [fibreEmbed_apply]
    rcases eq_or_lt_of_le hi1 with h1 | h2
    · subst h1
      have h := phaseIntegral_fderiv_le data hη.le hη1 hCg hCw hG hv hw hab hρ hθ
      rw [pow_one]
      refine h.trans ?_
      set A₁ := (8 + K.Cw * K.Cg) * (9 + (K.ξ0 / ((K.ξ0 - ρ) / 4)) ^ 2) with hA₁
      have hA₁0 : 0 ≤ A₁ := by positivity
      have hB' : CH * A₁ ≤ B := (le_abs_self _).trans (le_gaugeJetBase_one K CH ρ m)
      calc (b - a) * A₁ * s ≤ CH * S * A₁ * s :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hba hA₁0) hs0
        _ = CH * A₁ * Real.sqrt S * (Real.sqrt S * s) := by
            have hSS : Real.sqrt S * Real.sqrt S = S := Real.mul_self_sqrt hS0.le
            rw [show CH * A₁ * Real.sqrt S * (Real.sqrt S * s) =
              CH * A₁ * (Real.sqrt S * Real.sqrt S) * s by ring, hSS]
            ring
        _ = CH * A₁ * Real.sqrt S * x := by rw [hx]
        _ ≤ B * Real.sqrt S * (1 + x) := by
            have h3 : 0 ≤ Real.sqrt S := Real.sqrt_nonneg S
            have h4 : CH * A₁ * Real.sqrt S * x ≤ B * Real.sqrt S * x :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hB' h3) hx0
            have h5 : B * Real.sqrt S * x ≤ B * Real.sqrt S * (1 + x) :=
              mul_le_mul_of_nonneg_left (by linarith) (by positivity)
            linarith
    · have h := phaseIntegral_iteratedFDeriv_le data hη.le hη1 hCg hCw hG hv hw hab hρ0 hρ i hθ
      refine h.trans ?_
      set Ai := (8 + K.Cw * K.Cg) * K.ξ0 ^ 2 * (i : ℝ) ^ i / ((K.ξ0 - ρ) / 4) ^ i with hAi
      have hAi0 : 0 ≤ Ai := by
        have : 0 < (K.ξ0 - ρ) / 4 := by linarith
        positivity
      have hB' : CH * Ai ≤ B := (le_abs_self _).trans (le_gaugeJetBase K CH ρ (hik.trans hk))
      have heq : (b - a) * ((8 + K.Cw * K.Cg) * K.ξ0 ^ 2) * (i : ℝ) ^ i /
          ((K.ξ0 - ρ) / 4) ^ i = (b - a) * Ai := by rw [hAi]; ring
      rw [heq]
      have hSi : S ≤ Real.sqrt S ^ i := by
        have : Real.sqrt S ^ 2 ≤ Real.sqrt S ^ i := pow_le_pow_right₀ hsqS (by omega)
        rwa [Real.sq_sqrt hS0.le] at this
      have hBi : B ≤ B ^ i := le_self_pow₀ hB1 (by omega)
      have hxi : 1 ≤ (1 + x) ^ i := one_le_pow₀ (by linarith)
      calc (b - a) * Ai ≤ CH * S * Ai := mul_le_mul_of_nonneg_right hba hAi0
        _ = CH * Ai * S := by ring
        _ ≤ B * S := mul_le_mul_of_nonneg_right hB' hS0.le
        _ ≤ B ^ i * Real.sqrt S ^ i := mul_le_mul hBi hSi hS0.le (by positivity)
        _ ≤ B ^ i * Real.sqrt S ^ i * (1 + x) ^ i := le_mul_of_one_le_right (by positivity) hxi
        _ = (B * Real.sqrt S * (1 + x)) ^ i := by rw [mul_pow, mul_pow]
  -- Faà di Bruno and the real composition
  have hDn : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℂ i
      (fun ξ => -phaseIntegral data.lam a b ξ) (fibreEmbed η θ)‖ ≤
        (B * Real.sqrt S * (1 + x)) ^ i := by
    intro i hi hik
    change ‖iteratedFDeriv ℂ i (-(phaseIntegral data.lam a b)) (fibreEmbed η θ)‖ ≤ _
    rw [iteratedFDeriv_neg, Pi.neg_apply, norm_neg]
    exact hD i hi hik
  have hF := norm_iteratedFDeriv_cexp_comp_le hU hΞ.neg hξU k hDn
  have hR := norm_iteratedFDeriv_comp_clm_le hU hE (fibreEmbed η) hξU k
  have hL : ‖fibreEmbed η‖ ^ k ≤ (Real.sqrt η)⁻¹ ^ k :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_fibreEmbed_le hη) k
  rw [factorInverseGauge_eq_comp]
  have hexp : ‖Complex.exp (-blockGauge data.lam η a b θ)‖ =
      ‖Complex.exp (-phaseIntegral data.lam a b (fibreEmbed η θ))‖ := by
    rw [fibreEmbed_apply, blockGauge_eq_phaseIntegral]
  rw [hexp]
  set e := ‖Complex.exp (-phaseIntegral data.lam a b (fibreEmbed η θ))‖ with he
  have he0 : 0 ≤ e := norm_nonneg _
  have hscale : ϖ ^ k * (Real.sqrt η)⁻¹ ^ k * Real.sqrt S ^ k = 1 := by
    rw [hϖ', ← mul_pow, ← mul_pow]
    rw [show Real.sqrt η / Real.sqrt S * (Real.sqrt η)⁻¹ * Real.sqrt S = 1 by
      field_simp]
    simp
  calc ϖ ^ k * ‖iteratedFDeriv ℝ k
        (fun θ' => (fun ξ => Complex.exp (-phaseIntegral data.lam a b ξ)) (fibreEmbed η θ')) θ‖
      ≤ ϖ ^ k * (‖iteratedFDeriv ℂ k (fun ξ => Complex.exp (-phaseIntegral data.lam a b ξ))
          (fibreEmbed η θ)‖ * ‖fibreEmbed η‖ ^ k) :=
        mul_le_mul_of_nonneg_left hR (by positivity)
    _ ≤ ϖ ^ k * ((k ! * e * (B * Real.sqrt S * (1 + x)) ^ k) * (Real.sqrt η)⁻¹ ^ k) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul hF hL (by positivity) (by positivity))
          (by positivity)
    _ = k ! * B ^ k * (1 + x) ^ k * e * (ϖ ^ k * (Real.sqrt η)⁻¹ ^ k * Real.sqrt S ^ k) := by
        rw [mul_pow, mul_pow]
        ring
    _ = k ! * B ^ k * (1 + x) ^ k * e := by rw [hscale, mul_one]

/-- The closed inverse-gauge ingredient of the retained-factor assembly. -/
theorem factorInverseGauge : FactorInverseGaugeStatement := by
  intro K m CH ρ hρ
  let Bg := (m.factorial : ℝ) * gaugeJetBase K CH ρ m ^ m
  have hBg : 0 < Bg := mul_pos (by positivity)
    (pow_pos (lt_of_lt_of_le zero_lt_one (one_le_gaugeJetBase K CH ρ m)) _)
  refine ⟨Bg, hBg, ?_⟩
  intro η t₀ Sw G v data hη hη1 hCg hCw hG hv hw a b S ϖ hab hS hϖ hba
  refine ⟨factorInverseGauge_contDiffOn data hη.le hη1 hCg hCw hG hv hw hab m, ?_⟩
  intro θ hθ l hl
  have hn := factorInverseGauge_normalized_jet_le data hη hη1 hCg hCw hG hv hw hab hS hϖ hba hρ hθ hl
  have hf : (l.factorial : ℝ) ≤ m.factorial := by exact_mod_cast Nat.factorial_le hl
  have hp : gaugeJetBase K CH ρ m ^ l ≤ gaugeJetBase K CH ρ m ^ m :=
    pow_le_pow_right₀ (one_le_gaugeJetBase K CH ρ m) hl
  have hx : 0 ≤ 1 + Real.sqrt (vecDot θ θ) / ϖ := by
    have hϖ0 : 0 < ϖ := by
      rw [hϖ]
      exact Real.sqrt_pos.mpr (div_pos hη (lt_of_lt_of_le zero_lt_one hS))
    positivity
  have he : ‖Complex.exp (-blockGauge data.lam η a b θ)‖ =
      Real.exp (-(blockGauge data.lam η a b θ).re) := by rw [Complex.norm_exp, Complex.neg_re]
  rw [he] at hn
  have hbase : 0 ≤ gaugeJetBase K CH ρ m := zero_le_one.trans (one_le_gaugeJetBase K CH ρ m)
  exact hn.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul hf hp (by positivity) (by positivity))
      (pow_nonneg hx _)) (Real.exp_pos _).le)

end AVRegularity.CycleWords.Assembly
end
end

section
/-! Ordered frequency derivatives of the full-space Fourier amplitudes. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set Filter AVRegularity.Sobolev
namespace AVRegularity.CycleWords.Assembly
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Multiplication by any word monomial preserves the all-moments property. -/
theorem FactorHasAllMoments.word {g : Vec 2 → E} (hg : FactorHasAllMoments g) :
    ∀ {k : ℕ} (wd : DerivativeWord2 k), FactorHasAllMoments (fun y => wordMonomial wd y • g y)
  | 0, wd => by simpa only [wordMonomial, Fin.prod_univ_zero, one_smul] using hg
  | k + 1, wd => by
    have hm := (hg.word (fun i : Fin k => wd i.castSucc)).coord (wd (Fin.last k))
    simpa only [wordMonomial_succ, smul_smul] using hm

private theorem factorPhasePair_basis {A B : Vec 2 → E}
    (hA : FactorHasAllMoments A) (hB : FactorHasAllMoments B) (i : Fin 2) (θ : Vec 2) :
    fderiv ℝ (factorPhasePair A B) θ (basisVec i) =
      factorPhasePair (derivAmpA i B) (derivAmpB i A) θ := by
  rw [(factorPhasePair_hasFDerivAt hA hB θ).fderiv]
  fin_cases i <;> simp [coordSmulRight_apply, basisVec_apply, Fin.sum_univ_two]

/-- Every ordered derivative is another full-space trigonometric integral of a word moment. -/
theorem factorPhasePair_orderedDerivative : ∀ {k : ℕ} (wd : DerivativeWord2 k)
    {A B : Vec 2 → E}, FactorHasAllMoments A → FactorHasAllMoments B →
    orderedDerivative wd (factorPhasePair A B) =
      factorPhasePair
        (jRot k (fun y => wordMonomial wd y • A y, fun y => wordMonomial wd y • B y)).1
        (jRot k (fun y => wordMonomial wd y • A y, fun y => wordMonomial wd y • B y)).2
  | 0, wd, A, B, _, _ => by
    rw [AVRegularity.orderedDerivative_zero]
    simp only [jRot, wordMonomial, Fin.prod_univ_zero, one_smul]
  | k + 1, wd, A, B, hA, hB => by
    have hmem := jRot_mem (fun X : Vec 2 → E => FactorHasAllMoments X)
      (fun _ hx => hx.neg) k
      (p := (fun y => wordMonomial (fun i : Fin k => wd i.castSucc) y • A y,
        fun y => wordMonomial (fun i : Fin k => wd i.castSucc) y • B y))
      (hA.word (fun i : Fin k => wd i.castSucc)) (hB.word (fun i : Fin k => wd i.castSucc))
    rw [AVRegularity.orderedDerivative_succ,
      factorPhasePair_orderedDerivative (fun i : Fin k => wd i.castSucc) hA hB]
    funext θ
    rw [factorPhasePair_basis hmem.1 hmem.2]
    have hp : (fun y => wordMonomial wd y • A y, fun y => wordMonomial wd y • B y) =
        (fun y => y (wd (Fin.last k)) • (wordMonomial (fun i : Fin k => wd i.castSucc) y • A y),
          fun y => y (wd (Fin.last k)) • (wordMonomial (fun i : Fin k => wd i.castSucc) y • B y)) := by
      simp only [wordMonomial_succ, smul_smul]
    rw [hp, jRot_succ_smul]

omit [CompleteSpace E] in
/-- Simultaneous negation of the two input fields negates their trigonometric integral. -/
theorem factorPhasePair_neg (A B : Vec 2 → E) :
    factorPhasePair (-A) (-B) = -factorPhasePair A B := by
  funext θ
  simp only [factorPhasePair, Pi.neg_apply, smul_neg, ← neg_add, integral_neg]

omit [NormedSpace ℝ E] [CompleteSpace E] in
private theorem factorJRot_neg (j : ℕ) (A B : Vec 2 → E) :
    jRot j (-A, -B) = (-(jRot j (A, B)).1, -(jRot j (A, B)).2) := by
  exact jRot_comm (fun X : Vec 2 → E => -X) (fun _ => rfl) j (A, B)

omit [CompleteSpace E] in
/-- Quarter-turns preserve the squared pair of trigonometric integrals. -/
theorem factorPhasePair_rotation_sq (A B : Vec 2 → E) (j : ℕ) (θ : Vec 2) :
    ‖factorPhasePair (jRot j (A, B)).1 (jRot j (A, B)).2 θ‖ ^ 2 +
      ‖factorPhasePair (jRot j (B, -A)).1 (jRot j (B, -A)).2 θ‖ ^ 2 =
        ‖factorPhasePair A B θ‖ ^ 2 + ‖factorPhasePair B (-A) θ‖ ^ 2 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have h1 : jRot (j + 1) (A, B) = jRot j (B, -A) := jRot_add j 1 (A, B)
    have h2 : jRot (j + 1) (B, -A) = jRot j (-A, -B) := jRot_add j 1 (B, -A)
    rw [h1, h2, factorJRot_neg, factorPhasePair_neg, Pi.neg_apply, norm_neg, add_comm, ih]

omit [CompleteSpace E] in
private theorem factorFourierCos_eq_phasePair (g : Vec 2 → E) :
    (fun θ => ∫ y, Real.cos (vecDot θ y) • g y) = factorPhasePair g 0 := by
  funext θ
  simp only [factorPhasePair, Pi.zero_apply, smul_zero, add_zero]
  congr 1
  funext y
  congr 2
  unfold vecDot
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

omit [CompleteSpace E] in
private theorem factorFourierSin_eq_phasePair (g : Vec 2 → E) :
    (fun θ => ∫ y, Real.sin (vecDot θ y) • g y) = factorPhasePair 0 g := by
  funext θ
  simp only [factorPhasePair, Pi.zero_apply, smul_zero, zero_add]
  congr 1
  funext y
  congr 2
  unfold vecDot
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- An ordered Fourier derivative rotates the corresponding word moment without changing its
squared cosine/sine pair norm. -/
theorem factorFourier_ordered_sq {g : Vec 2 → E} (hg : FactorHasAllMoments g)
    {k : ℕ} (wd : DerivativeWord2 k) (θ : Vec 2) :
    ‖orderedDerivative wd (fun θ => ∫ y, Real.cos (vecDot θ y) • g y) θ‖ ^ 2 +
      ‖orderedDerivative wd (fun θ => ∫ y, Real.sin (vecDot θ y) • g y) θ‖ ^ 2 =
        ‖∫ y, Real.cos (vecDot θ y) • (wordMonomial wd y • g y)‖ ^ 2 +
          ‖∫ y, Real.sin (vecDot θ y) • (wordMonomial wd y • g y)‖ ^ 2 := by
  rw [factorFourierCos_eq_phasePair, factorFourierSin_eq_phasePair,
    factorPhasePair_orderedDerivative wd hg factorHasAllMoments_zero,
    factorPhasePair_orderedDerivative wd factorHasAllMoments_zero hg]
  simp only [Pi.zero_apply, smul_zero]
  let M : Vec 2 → E := fun y => wordMonomial wd y • g y
  have he := factorPhasePair_rotation_sq M 0 k θ
  have hn : jRot k (0, -M) = (-(jRot k (0, M)).1, -(jRot k (0, M)).2) := by
    simpa only [neg_zero] using factorJRot_neg k (0 : Vec 2 → E) M
  rw [hn, factorPhasePair_neg, Pi.neg_apply, norm_neg] at he
  have hneg : factorPhasePair 0 (-M) = -factorPhasePair 0 M := by
    simpa only [neg_zero] using factorPhasePair_neg (0 : Vec 2 → E) M
  rw [hneg, Pi.neg_apply, norm_neg] at he
  rw [← factorFourierCos_eq_phasePair M, ← factorFourierSin_eq_phasePair M] at he
  exact he

/-- Normalized ordered Fourier jets are exactly the normalized moment pairs. -/
theorem factorFourier_normalized_ordered_sq {g : Vec 2 → E} (hg : FactorHasAllMoments g)
    {k : ℕ} (wd : DerivativeWord2 k) (θ : Vec 2) {w : ℝ} (hw : 0 ≤ w) :
    (w ^ k * ‖orderedDerivative wd (fun θ => ∫ y, Real.cos (vecDot θ y) • g y) θ‖) ^ 2 +
      (w ^ k * ‖orderedDerivative wd (fun θ => ∫ y, Real.sin (vecDot θ y) • g y) θ‖) ^ 2 =
      ‖∫ y, (Real.cos (vecDot θ y) * (w * y 0) ^ (idxCount wd).1 *
        (w * y 1) ^ (idxCount wd).2) • g y‖ ^ 2 +
      ‖∫ y, (Real.sin (vecDot θ y) * (w * y 0) ^ (idxCount wd).1 *
        (w * y 1) ^ (idxCount wd).2) • g y‖ ^ 2 := by
  have he (ψ : ℝ → ℝ) : (∫ y, (ψ (vecDot θ y) * (w * y 0) ^ (idxCount wd).1 *
      (w * y 1) ^ (idxCount wd).2) • g y) =
      w ^ k • ∫ y, ψ (vecDot θ y) • (wordMonomial wd y • g y) := by
    rw [← integral_smul]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro y
    simp only [smul_smul]
    congr 1
    rw [show ψ (vecDot θ y) * (w * y 0) ^ (idxCount wd).1 * (w * y 1) ^ (idxCount wd).2 =
      ψ (vecDot θ y) * ((w * y 0) ^ (idxCount wd).1 * (w * y 1) ^ (idxCount wd).2) by ring,
      ← wordMonomial_smul_eq, wordMonomial_smul_eq_pow]
    ring
  rw [he Real.cos, he Real.sin]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hw k)]
  rw [mul_pow, mul_pow, ← mul_add, factorFourier_ordered_sq hg wd θ]
  ring

end AVRegularity.CycleWords.Assembly
end
end

section
/-! Fourier reconstruction of the real convolution cutoff by its cosine and sine amplitudes. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set Filter AVRegularity.Sobolev
namespace AVRegularity.CycleWords.Assembly
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
private theorem factorRep_phase_integrable {g : Vec 2 → E} (hg : Integrable g)
    (ψ : ℝ → ℝ) (hψ : Continuous ψ) (hb : ∀ x, |ψ x| ≤ 1) (θ : Vec 2) :
    Integrable (fun y => ψ (vecDot θ y) • g y) :=
  integrable_bdd_smul (hψ.comp (by unfold vecDot; fun_prop)) (fun y => hb _) hg

/-- Fubini turns the convolution definition into the full-frequency cosine/sine reconstruction. -/
theorem factorFourierCutoff_eq_integral {mc : Vec 2 → ℝ} (hm : Continuous mc)
    (hmi : Integrable mc) {g : Vec 2 → E} (hg : Integrable g) (z : Vec 2) :
    fourierCutoff mc g z = ∫ θ,
      Real.cos (vecDot θ z) • cutoffCosAmplitude mc g θ +
        Real.sin (vecDot θ z) • cutoffSinAmplitude mc g θ := by
  let F : Vec 2 → Vec 2 → E := fun θ y => (mc θ * Real.cos (vecDot θ (z - y))) • g y
  have hF : Integrable (Function.uncurry F) (volume.prod volume) := by
    refine (hmi.norm.mul_prod hg.norm).mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact ((hm.comp continuous_fst).mul
        (Real.continuous_cos.comp (by unfold vecDot; fun_prop))).aestronglyMeasurable.smul
          hg.aestronglyMeasurable.comp_snd
    · change ‖(mc p.1 * Real.cos (vecDot p.1 (z - p.2))) • g p.2‖ ≤ ‖mc p.1‖ * ‖g p.2‖
      rw [norm_smul, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)) (norm_nonneg _)
  have he : fourierCutoff mc g z = (2 * Real.pi)⁻¹ ^ 2 • ∫ y, ∫ θ, F θ y := by
    have ht := integral_sub_left_eq_self
      (fun y => cutoffKernel mc (z - y) • g y) volume z
    have ht' : fourierCutoff mc g z = ∫ y, cutoffKernel mc (z - y) • g y := by
      simpa only [sub_sub_cancel, fourierCutoff] using ht
    rw [ht', ← integral_smul]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by
      change ((2 * Real.pi)⁻¹ ^ 2 * ∫ θ, mc θ * Real.cos (vecDot θ (z - y))) • g y =
        (2 * Real.pi)⁻¹ ^ 2 • ∫ θ, F θ y
      rw [mul_smul, integral_smul_const]
  rw [he, ← integral_integral_swap hF, ← integral_smul]
  apply integral_congr_ae
  exact Eventually.of_forall fun θ => by
    have hc := factorRep_phase_integrable hg Real.cos Real.continuous_cos Real.abs_cos_le_one θ
    have hs := factorRep_phase_integrable hg Real.sin Real.continuous_sin Real.abs_sin_le_one θ
    have hp (y : Vec 2) : vecDot θ (z - y) = vecDot θ z - vecDot θ y := by
      simp only [vecDot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    have hpoint : F θ = fun y =>
        (mc θ * Real.cos (vecDot θ z)) • (Real.cos (vecDot θ y) • g y) +
          (mc θ * Real.sin (vecDot θ z)) • (Real.sin (vecDot θ y) • g y) := by
      funext y
      dsimp [F]
      rw [hp, Real.cos_sub]
      simp only [mul_add, add_smul, mul_smul]
    change (2 * Real.pi)⁻¹ ^ 2 • (∫ y, F θ y) =
      Real.cos (vecDot θ z) • cutoffCosAmplitude mc g θ +
        Real.sin (vecDot θ z) • cutoffSinAmplitude mc g θ
    have hci : Integrable (fun y => (mc θ * Real.cos (vecDot θ z)) •
        (Real.cos (vecDot θ y) • g y)) := hc.smul (mc θ * Real.cos (vecDot θ z))
    have hsi : Integrable (fun y => (mc θ * Real.sin (vecDot θ z)) •
        (Real.sin (vecDot θ y) • g y)) := hs.smul (mc θ * Real.sin (vecDot θ z))
    rw [hpoint]
    dsimp only
    rw [integral_add hci hsi, integral_smul, integral_smul]
    simp only [cutoffCosAmplitude, cutoffSinAmplitude, smul_add, smul_smul]
    congr 1 <;> congr 1 <;> ring

/-- Compact smooth multipliers give the exact retained amplitude required by B1.F. -/
theorem factorFourierCutoff_isRetained {mc : Vec 2 → ℝ} (hm : ContDiff ℝ (⊤ : ℕ∞) mc)
    (hmc : HasCompactSupport mc) {g : Vec 2 → E} (hg : FactorHasAllMoments g)
    (r : ℝ) (hs : ∀ θ : Vec 2, r ^ 2 < vecDot θ θ → mc θ = 0) :
    IsRetainedAmplitude (fourierCutoff mc g) r (cutoffCosAmplitude mc g)
      (cutoffSinAmplitude mc g) := by
  have hsA : HasCompactSupport (cutoffCosAmplitude mc g) := by
    exact hmc.mul_left.smul_right
  have hsB : HasCompactSupport (cutoffSinAmplitude mc g) := by
    exact hmc.mul_left.smul_right
  have hsm := factorCutoff_contDiff (m := 0) hg (hm.of_le (by exact_mod_cast le_top))
  refine ⟨fun θ hθ => ?_, (hsm.1.continuous.integrable_of_hasCompactSupport hsA).integrableOn,
    (hsm.2.continuous.integrable_of_hasCompactSupport hsB).integrableOn, fun z => ?_⟩
  · simp only [cutoffCosAmplitude, cutoffSinAmplitude, hs θ hθ, mul_zero, zero_smul, and_self]
  · rw [factorFourierCutoff_eq_integral hm.continuous
      (hm.continuous.integrable_of_hasCompactSupport hmc) hg.integrable]
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro θ hθ
    have hn : r ^ 2 < vecDot θ θ := lt_of_not_ge hθ
    simp only [cutoffCosAmplitude, cutoffSinAmplitude, hs θ hn, mul_zero, zero_smul, smul_zero, add_zero]

end AVRegularity.CycleWords.Assembly
end
end
end
