-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Assembly.BillBound
import AVRegularity.CycleReference.TorusChartEquation
import AVRegularity.Velocity.ExistsLimitVelocity
import AVRegularity.CycleComparison.Charts.ChartDeviation
public import AVRegularity.Weighted.DriftCoefficientEmbedding
import AVRegularity.Applications.Transfer.TubeK
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain
public import AVRegularity.Statements.Construction.IsOCStreamSeq
import AVRegularity.CycleComparison.LiftMeanEntrywise.Assembly
import AVRegularity.CycleComparison.Assembly.OcData
public import AVRegularity.CycleComparison.ActualMeans.Main
import AVRegularity.Proofs.Intermediate.CycleComparison.CycleResidualDifferentiated
public import AVRegularity.CycleComparison.Coarse.SecondOrderResponse
public import AVRegularity.Statements.Intermediate.Families.IsPointwiseAnalyticEnvelope
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyHasDepthAtMost
public import AVRegularity.CycleComparison.LiftMeanEntrywise.Letter
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVenhance.Statements.Construction.BarNorm
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Assembly

/-! The drift fields of `IsCoarseSetting` for the background velocity `𝐛_{m-1} = ∇^⊥φ_{m-1}` (the
coarse window of clause 6 of `cycle_comparison`): smoothness, incompressibility, periodicity,
boundedness, joint measurability, and the analytic jets
`‖∇^l 𝐛_{m-1}‖ ≤ a B₀^l l! λ^{1-l}` with `a = 2¹³‖ι‖ a_{m-1}`, `B₀ = 2¹¹`, `λ = E = ε_{m-1}`,
where `ι` is the embedding of a vector into the drift coefficient.

The jets come from the stream bound `⟦φ_{m-1}⟧_{n, 2⁸/E} ≤ 2⁵ a_{m-1} E² (n+2)²/(n+1)³`
(`Velocity.stream_regularity`), unpacked into pointwise word bounds; the `l`-th jet of the
velocity is an `(l+1)`-th jet of the stream. The two drift conditions at `ρ = R = √(Bτ_m'')`:
`B₀R/λ ≤ 1/2` from `R ≍ E^{1+γ/2+δ}` (the ledger) and `E ≤ Λ⁻¹`, and `a B₀ R² ≤ B/8` from
`a_{m-1} τ_m'' ≤ C E^{2δ}` (the ledger), both for `Λ ≥ Λ₀`. -/

/-! ### Abstract-real algebra -/

/-- `(N+2)² ≤ (N+1)³(N+1)²` for `N ≥ 2`. -/
theorem sq_add_two_le_pow {N : ℝ} (hN : 2 ≤ N) : (N + 2) ^ 2 ≤ (N + 1) ^ 3 * (N + 1) ^ 2 := by
  have h0 : 0 ≤ N := by linarith
  have h1 : (N + 2) ^ 2 ≤ 4 * (N + 1) ^ 2 := by linarith [mul_nonneg h0 h0]
  have h27 : (27 : ℝ) ≤ (N + 1) ^ 3 := by
    calc (27 : ℝ) = 3 ^ 3 := by norm_num
      _ ≤ (N + 1) ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
  have h3 : 4 * (N + 1) ^ 2 ≤ (N + 1) ^ 3 * (N + 1) ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  linarith

/-- The pointwise word bound of an `(l+1)`-th stream jet given by the stream regularity at
radius `2⁸/ε`: `B (l+1)!/(l+2)² R^{l+1}` with `B = 2⁵ A ε² (l+3)²/(l+2)³`. -/
def driftWordBound (ε A : ℝ) (l : ℕ) : ℝ :=
  2 ^ 5 * A * ε ^ 2 * ((((l + 1 : ℕ) : ℝ) + 2) ^ 2 / (((l + 1 : ℕ) : ℝ) + 1) ^ 3) *
    (((l + 1).factorial : ℝ) / (((l + 1 : ℕ) : ℝ) + 1) ^ 2) * (2 ^ 8 * ε⁻¹) ^ (l + 1)

theorem driftWordBound_nonneg {ε A : ℝ} (hε : 0 < ε) (hA : 0 ≤ A) (l : ℕ) :
    0 ≤ driftWordBound ε A l := by
  unfold driftWordBound
  positivity

/-- The constant of the velocity jets: `2^l K 2^l W_l ≤ 2¹³ K A (2¹¹)^l l! ε^{1-l}`. -/
theorem drift_jet_constant_le {ε A K : ℝ} (hε : 0 < ε) (hA : 0 ≤ A) (hK : 0 ≤ K) {l : ℕ}
    (hl : 1 ≤ l) :
    2 ^ l * K * (2 ^ l * driftWordBound ε A l) ≤
      2 ^ 13 * K * A * (2 ^ 11) ^ l * (l.factorial : ℝ) * ε ^ ((1 : ℤ) - l) := by
  unfold driftWordBound
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hN : (2 : ℝ) ≤ ((l + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hden : 0 < (((l + 1 : ℕ) : ℝ) + 1) ^ 3 * (((l + 1 : ℕ) : ℝ) + 1) ^ 2 := by positivity
  have hPF : ((((l + 1 : ℕ) : ℝ) + 2) ^ 2 / (((l + 1 : ℕ) : ℝ) + 1) ^ 3) *
      (((l + 1).factorial : ℝ) / (((l + 1 : ℕ) : ℝ) + 1) ^ 2) ≤ ((l + 1).factorial : ℝ) := by
    rw [div_mul_div_comm, div_le_iff₀ hden]
    calc (((l + 1 : ℕ) : ℝ) + 2) ^ 2 * ((l + 1).factorial : ℝ)
        = ((l + 1).factorial : ℝ) * (((l + 1 : ℕ) : ℝ) + 2) ^ 2 := mul_comm _ _
      _ ≤ ((l + 1).factorial : ℝ) *
          ((((l + 1 : ℕ) : ℝ) + 1) ^ 3 * (((l + 1 : ℕ) : ℝ) + 1) ^ 2) :=
        mul_le_mul_of_nonneg_left (sq_add_two_le_pow hN) (Nat.cast_nonneg _)
  have hfac : ((l + 1).factorial : ℝ) ≤ 2 ^ l * (l.factorial : ℝ) := by
    have h1 : l + 1 ≤ 2 ^ l := Nat.lt_two_pow_self
    have h2 : (l : ℝ) + 1 ≤ 2 ^ l := by exact_mod_cast h1
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    exact mul_le_mul_of_nonneg_right h2 (Nat.cast_nonneg _)
  have hR : (2 ^ 8 * ε⁻¹) ^ (l + 1) = 2 ^ 8 * (2 ^ 8) ^ l * (ε⁻¹ * ε⁻¹ ^ l) := by
    rw [mul_pow ((2 : ℝ) ^ 8) ε⁻¹ (l + 1), pow_succ ((2 : ℝ) ^ 8) l, pow_succ ε⁻¹ l]
    ring
  have hε2 : ε ^ 2 * ε⁻¹ = ε := by
    rw [sq, mul_assoc, mul_inv_cancel₀ hε.ne', mul_one]
  have hz : ε ^ ((1 : ℤ) - l) = ε * ε⁻¹ ^ l := by
    rw [zpow_sub₀ hε.ne', zpow_one, zpow_natCast, div_eq_mul_inv, inv_pow]
  have h11 : (2 : ℝ) ^ l * 2 ^ l * 2 ^ l * (2 ^ 8) ^ l = (2 ^ 11) ^ l := by
    rw [← mul_pow, ← mul_pow, ← mul_pow]
    norm_num
  calc 2 ^ l * K * (2 ^ l * (2 ^ 5 * A * ε ^ 2 *
          ((((l + 1 : ℕ) : ℝ) + 2) ^ 2 / (((l + 1 : ℕ) : ℝ) + 1) ^ 3) *
          (((l + 1).factorial : ℝ) / (((l + 1 : ℕ) : ℝ) + 1) ^ 2) * (2 ^ 8 * ε⁻¹) ^ (l + 1)))
      = 2 ^ l * K * 2 ^ l * 2 ^ 5 * A * (ε ^ 2 * ε⁻¹) * 2 ^ 8 * (2 ^ 8) ^ l * ε⁻¹ ^ l *
          (((((l + 1 : ℕ) : ℝ) + 2) ^ 2 / (((l + 1 : ℕ) : ℝ) + 1) ^ 3) *
            (((l + 1).factorial : ℝ) / (((l + 1 : ℕ) : ℝ) + 1) ^ 2)) := by
        rw [hR]
        ring
    _ ≤ 2 ^ l * K * 2 ^ l * 2 ^ 5 * A * (ε ^ 2 * ε⁻¹) * 2 ^ 8 * (2 ^ 8) ^ l * ε⁻¹ ^ l *
          ((l + 1).factorial : ℝ) :=
        mul_le_mul_of_nonneg_left hPF (by positivity)
    _ ≤ 2 ^ l * K * 2 ^ l * 2 ^ 5 * A * (ε ^ 2 * ε⁻¹) * 2 ^ 8 * (2 ^ 8) ^ l * ε⁻¹ ^ l *
          (2 ^ l * (l.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left hfac (by positivity)
    _ = 2 ^ 13 * K * A * (2 ^ l * 2 ^ l * 2 ^ l * (2 ^ 8) ^ l) * (l.factorial : ℝ) *
          (ε * ε⁻¹ ^ l) := by
        rw [hε2]
        ring
    _ = 2 ^ 13 * K * A * (2 ^ 11) ^ l * (l.factorial : ℝ) * ε ^ ((1 : ℤ) - l) := by
        rw [h11, hz]

/-! ### The jets of the velocity of a stream -/

/-- **Velocity jets from the stream bound.** If `⟦φ(t)⟧_{l+1, 2⁸/ε} ≤ 2⁵ A ε² (l+3)²/(l+2)³`,
the `l`-th jet of the drift coefficient of `∇^⊥φ(t)` is at most
`2¹³‖ι‖ A (2¹¹)^l l! ε^{1-l}`. -/
theorem streamVel_driftJet_le {φ : ℝ → Vec 2 → ℝ} {t ε A : ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) (φ t)) (hv : ContDiff ℝ (⊤ : ℕ∞) (streamVel φ t))
    (hε : 0 < ε) (hA : 0 ≤ A) {l : ℕ} (hl : 1 ≤ l)
    (hbar : barNorm (l + 1) (2 ^ 8 * ε⁻¹) (φ t) ≤ ENNReal.ofReal (2 ^ 5 * A * ε ^ 2 *
      ((((l + 1 : ℕ) : ℝ) + 2) ^ 2 / (((l + 1 : ℕ) : ℝ) + 1) ^ 3))) (x : Vec 2) :
    ‖coefficientDerivativeArray (driftCoefficient (streamVel φ t)) l x‖ ≤
      2 ^ 13 * ‖Weighted.driftCoefficientEmbedding‖ * A * (2 ^ 11) ^ l *
        (l.factorial : ℝ) * ε ^ ((1 : ℤ) - l) := by
  have hR : (0 : ℝ) < 2 ^ 8 * ε⁻¹ := by positivity
  have hB : (0 : ℝ) ≤ 2 ^ 5 * A * ε ^ 2 *
      ((((l + 1 : ℕ) : ℝ) + 2) ^ 2 / (((l + 1 : ℕ) : ℝ) + 1) ^ 3) := by positivity
  have hW0 := driftWordBound_nonneg hε hA l
  have hword : ∀ w : Fin (l + 1) → Fin 2,
      |iteratedFDeriv ℝ (l + 1) (φ t) x (fun k => basisVec (w k))| ≤ driftWordBound ε A l :=
    fun w => AVRegularity.CycleComparison.Charts.word_le_of_barNorm_le hR hB hf hbar w x
  have hcomp : ∀ (w : Fin l → Fin 2) (i : Fin 2),
      |iteratedFDeriv ℝ l (streamVel φ t) x (fun k => basisVec (w k)) i| ≤
        driftWordBound ε A l := by
    intro w
    have h0 : iteratedFDeriv ℝ l (fun y => streamVel φ t y 0) x (fun k => basisVec (w k)) =
        -iteratedFDeriv ℝ (l + 1) (φ t) x (Fin.snoc (fun k => basisVec (w k)) (basisVec 1)) :=
      AVRegularity.Velocity.Port.MaterialSpatial.streamVel_component0_iterated_eq hf l x w
    have h1 : iteratedFDeriv ℝ l (fun y => streamVel φ t y 1) x (fun k => basisVec (w k)) =
        iteratedFDeriv ℝ (l + 1) (φ t) x (Fin.snoc (fun k => basisVec (w k)) (basisVec 0)) :=
      AVRegularity.Velocity.Port.MaterialSpatial.streamVel_component1_iterated_eq hf l x w
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · rw [← AVRegularity.Velocity.Port.MaterialSpatial.iteratedFDeriv_component hv l x w 0, h0,
        abs_neg, AVRegularity.Velocity.Port.MaterialSpatial.basisVec_snoc w 1]
      exact hword _
    · rw [← AVRegularity.Velocity.Port.MaterialSpatial.iteratedFDeriv_component hv l x w 1, h1,
        AVRegularity.Velocity.Port.MaterialSpatial.basisVec_snoc w 0]
      exact hword _
  have hvec : ∀ w : Fin l → Fin 2,
      ‖iteratedFDeriv ℝ l (streamVel φ t) x (fun k => basisVec (w k))‖ ≤
        driftWordBound ε A l := fun w =>
    (pi_norm_le_iff_of_nonneg hW0).2 fun i => by
      rw [Real.norm_eq_abs]
      exact hcomp w i
  have hD : ‖iteratedFDeriv ℝ l (streamVel φ t) x‖ ≤ 2 ^ l * driftWordBound ε A l := by
    calc ‖iteratedFDeriv ℝ l (streamVel φ t) x‖
        ≤ ∑ w : DerivativeWord2 l,
            ‖iteratedFDeriv ℝ l (streamVel φ t) x (fun i => basisVec (w i))‖ :=
          norm_le_sum_basisVec _
      _ ≤ ∑ _w : DerivativeWord2 l, driftWordBound ε A l :=
          Finset.sum_le_sum fun w _ => hvec w
      _ = 2 ^ l * driftWordBound ε A l := by
          rw [Finset.sum_const, card_derivativeWord2]
          simp
  have harr := Weighted.driftCoefficient_array_norm_le_iterated (streamVel φ t) l
    (hv.of_le (by simp)) x
  have hcard : (Fintype.card (DerivativeWord2 l) : ℝ) = 2 ^ l := by simp
  calc ‖coefficientDerivativeArray (driftCoefficient (streamVel φ t)) l x‖
      ≤ ((Fintype.card (DerivativeWord2 l) : ℝ) * ‖Weighted.driftCoefficientEmbedding‖) *
          ‖iteratedFDeriv ℝ l (streamVel φ t) x‖ := harr
    _ = 2 ^ l * ‖Weighted.driftCoefficientEmbedding‖ *
          ‖iteratedFDeriv ℝ l (streamVel φ t) x‖ := by rw [hcard]
    _ ≤ 2 ^ l * ‖Weighted.driftCoefficientEmbedding‖ * (2 ^ l * driftWordBound ε A l) :=
        mul_le_mul_of_nonneg_left hD (by positivity)
    _ ≤ 2 ^ 13 * ‖Weighted.driftCoefficientEmbedding‖ * A * (2 ^ 11) ^ l *
          (l.factorial : ℝ) * ε ^ ((1 : ℤ) - l) :=
        drift_jet_constant_le hε hA (norm_nonneg Weighted.driftCoefficientEmbedding) hl

/-! ### The drift fields -/

/-- **The drift fields of the coarse setting** for the background velocity
`streamVel (Φ (m - 1))` at the radius `R = √(Bτ_m'')`. -/
theorem coarse_drift_fields (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s)
    (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ)
    (hζ : IsFastProfile ζ) :
    ∃ (Λ₀ : ℕ) (B₀ : ℝ), 128 ≤ Λ₀ ∧ 1 ≤ B₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ (Φ : ℕ → ℝ → Vec 2 → ℝ), IsOCStreamSeq α q Λ ζ Φ →
      ∀ (M' : ℕ) (κ : ℕ → ℝ), IsOCBandChain α q Λ ζ M' κ →
      ∀ m : ℕ, 2 ≤ m → m ≤ M' → ∀ ν B : ℝ, κ m = ν → κ (m - 1) = B →
      ∃ a lam : ℝ, 0 ≤ a ∧ 0 < lam ∧
        B₀ * Real.sqrt (B * ocTauPP α q Λ m) / lam ≤ 1 / 2 ∧
        a * B₀ * Real.sqrt (B * ocTauPP α q Λ m) ^ 2 ≤ B / 8 ∧
        (∀ l : ℕ, 1 ≤ l → ∀ (t : ℝ) (x : Vec 2),
          ‖coefficientDerivativeArray (driftCoefficient (streamVel (Φ (m - 1)) t)) l x‖ ≤
            a * B₀ ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l)) ∧
        (∀ t : ℝ, ContDiff ℝ (⊤ : ℕ∞) (streamVel (Φ (m - 1)) t)) ∧
        (∀ (t : ℝ) (x : Vec 2),
          ∑ k : Fin 2, fderiv ℝ (streamVel (Φ (m - 1)) t) x (basisVec k) k = 0) ∧
        (∀ t : ℝ, AVenhance.IsZ2Periodic (streamVel (Φ (m - 1)) t)) ∧
        (∀ t₀ t₁ : ℝ, ∃ C : ℝ, ∀ t ∈ Set.Icc t₀ t₁, ∀ x, ‖streamVel (Φ (m - 1)) t x‖ ≤ C) ∧
        (∀ t₀ t₁ : ℝ,
          Measurable fun p : Set.Icc t₀ t₁ × Vec 2 => streamVel (Φ (m - 1)) p.1 p.2) := by
  obtain ⟨C₀, hC₀, Λ₁, hΛ₁, hled⟩ :=
    AVRegularity.CycleReference.bandChain_uniform_ledger hα₀ hα₁ hs₀ hs₁ hq hζ
  have hexp := AVRegularity.Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq
  have hγ : 0 < ocGamma α q := hexp.1
  have hδ : 0 < ocDelta α q := hexp.2.1
  have hc : 0 < ocGamma α q / 2 + ocDelta α q := by linarith
  have h2δ : 0 < 2 * ocDelta α q := by linarith
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le one_pos hC₀
  have hM : 0 ≤ 2 ^ 27 * ‖Weighted.driftCoefficientEmbedding‖ * C₀ := by positivity
  refine ⟨max Λ₁ (max ⌈(2 ^ 12 * C₀) ^ (1 / (ocGamma α q / 2 + ocDelta α q))⌉₊
      ⌈(2 ^ 27 * ‖Weighted.driftCoefficientEmbedding‖ * C₀ + 1) ^ (1 / (2 * ocDelta α q))⌉₊),
    2 ^ 11, hΛ₁.trans (le_max_left _ _), by norm_num, ?_⟩
  intro Λ hΛ Φ hΦ M' κ hband m hm2 hmM ν B hν hB
  have hΛ₁' : Λ₁ ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛ₂ : ⌈(2 ^ 12 * C₀) ^ (1 / (ocGamma α q / 2 + ocDelta α q))⌉₊ ≤ Λ :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hΛ
  have hΛ₃ : ⌈(2 ^ 27 * ‖Weighted.driftCoefficientEmbedding‖ * C₀ + 1) ^
      (1 / (2 * ocDelta α q))⌉₊ ≤ Λ :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hΛ
  have h128 : 128 ≤ Λ := hΛ₁.trans hΛ₁'
  have hΛ1 : 1 ≤ Λ := by omega
  have hΛpos : (0 : ℝ) < (Λ : ℝ) := by exact_mod_cast (show 0 < Λ by omega)
  have hE : 0 < ocEpsilon q Λ (m - 1) :=
    (AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 h128).1
  have hEΛ : ocEpsilon q Λ (m - 1) ≤ (Λ : ℝ)⁻¹ :=
    AVRegularity.CycleReference.epsilon_le_inv_separation (m := m - 1) hq.1 h128 (by omega)
  have hτ'' : 0 < ocTauPP α q Λ m := AVRegularity.Construction.Stream.ocTauPP_pos hΛ1
  have hBpos : 0 < B := by
    rw [← hB]
    exact AVRegularity.CycleReference.bandChain_pos hΛ1 hζ hband (show m - 1 ≤ M' by omega)
  obtain ⟨_, _, _, _, hRh, _, _, _, _, _, _, _, hAτ, _⟩ :=
    (hled Λ hΛ₁' M' (by omega) κ hband).2 m hm2 hmM ν B hν hB
  unfold ocRh at hRh
  unfold ocC at hRh
  have hrad : 2 ^ 12 * Real.sqrt (B * ocTauPP α q Λ m) ≤ ocEpsilon q Λ (m - 1) := by
    refine le_of_powerLaw_of_small hE (by positivity : (0 : ℝ) < 2 ^ 12 * C₀) hc hΛpos hEΛ
      ((Nat.le_ceil ((2 ^ 12 * C₀) ^ (1 / (ocGamma α q / 2 + ocDelta α q)))).trans
        (Nat.cast_le.2 hΛ₂)) ?_
    calc 2 ^ 12 * Real.sqrt (B * ocTauPP α q Λ m)
        ≤ 2 ^ 12 * (C₀ * ocEpsilon q Λ (m - 1) ^ (1 + (ocGamma α q / 2 + ocDelta α q))) :=
          mul_le_mul_of_nonneg_left hRh.2 (by norm_num)
      _ = 2 ^ 12 * C₀ * ocEpsilon q Λ (m - 1) ^ (1 + (ocGamma α q / 2 + ocDelta α q)) :=
          (mul_assoc _ _ _).symm
  have hsmall : 2 ^ 27 * ‖Weighted.driftCoefficientEmbedding‖ * C₀ *
      ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q) ≤ 1 :=
    mul_rpow_le_one_of_small hE h2δ hΛpos hEΛ hM
      ((Nat.le_ceil ((2 ^ 27 * ‖Weighted.driftCoefficientEmbedding‖ * C₀ + 1) ^
        (1 / (2 * ocDelta α q)))).trans (Nat.cast_le.2 hΛ₃))
  have hA0 : 0 ≤ ocA α q Λ (m - 1) := by
    unfold ocA
    exact (Real.rpow_pos_of_pos hE _).le
  have hadm : IsAdmissibleStream (Φ (m - 1)) :=
    AVRegularity.Velocity.streamSeq_admissible hζ h128 hΦ (m - 1)
  have hsl : ∀ r : ℝ, ContDiff ℝ (⊤ : ℕ∞) (Φ (m - 1) r) := fun r =>
    hadm.1.comp (contDiff_const.prodMk contDiff_id)
  have hvs : ∀ r : ℝ, ContDiff ℝ (⊤ : ℕ∞) (streamVel (Φ (m - 1)) r) := fun r =>
    AVRegularity.Applications.streamVel_slice_smooth α q ζ hζ Λ h128 Φ hΦ (m - 1) r
  obtain ⟨_, _, hreg⟩ :=
    AVRegularity.Velocity.stream_regularity α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ h128 Φ hΦ
  refine ⟨2 ^ 13 * ‖Weighted.driftCoefficientEmbedding‖ * ocA α q Λ (m - 1),
    ocEpsilon q Λ (m - 1), by positivity, hE, ?_, ?_, ?_, hvs, ?_, ?_, ?_, ?_⟩
  · -- `B₀ R / λ ≤ 1/2`
    rw [div_le_iff₀ hE]
    linarith
  · -- `a B₀ R² ≤ B/8`
    calc 2 ^ 13 * ‖Weighted.driftCoefficientEmbedding‖ * ocA α q Λ (m - 1) * 2 ^ 11 *
          Real.sqrt (B * ocTauPP α q Λ m) ^ 2
        = 2 ^ 24 * ‖Weighted.driftCoefficientEmbedding‖ * B *
            (ocA α q Λ (m - 1) * ocTauPP α q Λ m) := by
          rw [Real.sq_sqrt (mul_nonneg hBpos.le hτ''.le)]
          ring
      _ ≤ 2 ^ 24 * ‖Weighted.driftCoefficientEmbedding‖ * B *
            (C₀ * ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q)) :=
          mul_le_mul_of_nonneg_left hAτ (by positivity)
      _ = B / 8 * (2 ^ 27 * ‖Weighted.driftCoefficientEmbedding‖ * C₀ *
            ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q)) := by ring
      _ ≤ B / 8 * 1 := mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = B / 8 := mul_one _
  · -- the analytic jets
    intro l hl t x
    exact streamVel_driftJet_le (φ := Φ (m - 1)) (t := t) (hsl t) (hvs t) hE hA0 hl
      ((hreg (m - 1) (by omega) t).2.1 (l + 1) (by omega)) x
  · -- incompressibility
    intro t x
    have h := AVRegularity.Applications.streamVel_classical_div hsl t x
    unfold AVRegularity.Applications.pd at h
    rw [AVRegularity.Velocity.Port.MaterialSpatial.fderiv_component_apply (hvs t) x 0 0,
      AVRegularity.Velocity.Port.MaterialSpatial.fderiv_component_apply (hvs t) x 1 1] at h
    rw [Fin.sum_univ_two]
    exact h
  · -- periodicity
    intro t
    exact AVRegularity.Velocity.streamSeq_velocity_spatial_periodic hζ h128 hΦ (m - 1) t
  · -- boundedness
    intro _ _
    exact ⟨AVRegularity.Applications.velBound α q Λ, fun t _ x =>
      AVRegularity.Applications.streamVel_norm_le α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ h128 Φ hΦ
        (m - 1) t x⟩
  · -- joint measurability
    intro _ _
    exact hadm.vel_continuous.measurable.comp
      ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)

end AVRegularity.CycleComparison.Assembly
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Assembly

/-! The chart-frame mean letters of one pulse, for every grade and degree at once: the
conclusions (a) to (g) of `cycle_lift_mean_entrywise` bundled over the grades `r ≤ H` and
the degrees `2 ≤ n ≤ N + D`. The clauses of `cycle_comparison` are stated about one such family
of letters per observed pulse. The letters are the explicit ones (`meanLetter`); at grade zero
they are the diagonal mean letters, whose order-two term is compared with the reference flux.
-/

/-- The mean letters `Lb r n` of the lift `(Q, Cc)` on the window `[t₀, t₁]`. -/
structure IsPulseLetters {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] {D : ℕ}
    (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h) (π : ι → ℝ) (b : ι → ι → ℝ)
    (t₀ t₁ lam C₂ : ℝ) (N H K : ℕ) (Lb : ℕ → ℕ → MeanCoeff ι h) : Prop where
  perm : ∀ r, r ≤ H → ∀ n, 2 ≤ n → n ≤ N + D →
    ∀ d (α : DerivativeWord2 (d - 1)) (σ : Equiv.Perm (Fin (d - 1))),
      Lb r n d (α ∘ σ) = Lb r n d α
  smooth : ∀ r, r ≤ H → ∀ n, 2 ≤ n → n ≤ N + D →
    ∀ d (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2) (v u : ι), ∀ t ∈ Set.Icc t₀ t₁,
      ContDiff ℝ ((K + 1 : ℕ) : ℕ∞) (fun X => Lb r n d α t X k₀ v u)
  meas : ∀ r, r ≤ H → ∀ n, 2 ≤ n → n ≤ N + D →
    ∀ d (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2) (v u : ι) (X : Vec 2),
      Measurable (fun t : Set.Icc t₀ t₁ => Lb r n d α t X k₀ v u)
  pres : ∀ r, r ≤ H → ∀ n, 2 ≤ n → n ≤ N + D →
    ∀ a₀ : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) a₀ → ∀ t ∈ Set.Icc t₀ t₁, ∀ X,
      liftMean Q Cc (fun _ => a₀) r n t X = meanApply n (Lb r n) (fun _ => a₀) t X
  bound : ∀ r, r ≤ H → ∀ n, 2 ≤ n → n ≤ N + D → ∀ d, 2 ≤ d → d ≤ n →
    ∀ (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2) (v u : ι), ∀ j, j ≤ K + 1 →
      ∀ t ∈ Set.Icc t₀ t₁, ∀ X,
        ‖iteratedFDeriv ℝ j (fun X' => Lb r n d α t X' k₀ v u) X‖ ≤
          C₂ * ((Matrix.of fun v' u' => b v' u' / Real.sqrt (π u' / π v')) ^ r) v u *
            lam ^ (n - d + j)
  diag : ∀ n, 2 ≤ n → n ≤ N + D →
    ∃ Ls : (d : ℕ) → DerivativeWord2 (d - 1) → ℝ → Vec 2 → Fin 2 → ℝ,
      ∀ d, 2 ≤ d → d ≤ n → ∀ (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2),
        ∀ t ∈ Set.Icc t₀ t₁, ∀ X,
          (∀ v, Lb 0 n d α t X k₀ v v = Ls d α t X k₀ • ContinuousLinearMap.id ℝ (h v)) ∧
          (∀ v u, v ≠ u → Lb 0 n d α t X k₀ v u = 0)
  shift : ∀ T : Vec 2, (∀ t X i j, Q.G t (X + T) i j = Q.G t X i j) →
    (∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α t X z, γ.coeff α t (X + T) z = γ.coeff α t X z) →
    ∀ r, r ≤ H → ∀ n, 2 ≤ n → n ≤ N + D →
      ∀ d (α : DerivativeWord2 (d - 1)) (k₀ : Fin 2) (v u : ι),
        ∀ t ∈ Set.Icc t₀ t₁, ∀ X, Lb r n d α t (X + T) k₀ v u = Lb r n d α t X k₀ v u
  explicit : ∀ r n, Lb r n = LiftMeanEntrywise.meanLetter Q Cc r n

/-- **The letters of a lift exist** (`cycle_lift_mean_entrywise`, for all grades and degrees): the
explicit ones. -/
theorem exists_pulseLetters (N K k L D H : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
        (Q : LiftOperatorData ι h D) (π : ι → ℝ)
        (t₀ t₁ e ν B ρ E ℓ dstar εc lam : ℝ) (par : Fin 2) (V : ℝ → ℝ → ℝ) (qs qf : ℕ)
        (b : ι → ι → ℝ) (Θ : ℝ),
        IsLiftSetting Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj b Θ →
      ∀ Cc : ℕ → ℕ → LiftCoeff ι h,
        IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) t₀ t₁ N H Cc →
        ∃ Lb : ℕ → ℕ → MeanCoeff ι h, IsPulseLetters Q Cc π b t₀ t₁ lam C₂ N H K Lb := by
  refine ⟨Lift.ambientMeanGradeConstant K N k L D H CG Cw Cj,
    Lift.ambientMeanGradeConstant_nonneg K N k L D H CG Cw Cj, ?_⟩
  intro ι _ _ h _ _ _ _ Q π t₀ t₁ e ν B ρ E ℓ dstar εc lam par V qs qf b Θ P Cc hseq
  let : ∀ i, MeasurableSpace (h i) := fun i => borel (h i)
  have : ∀ i, BorelSpace (h i) := fun _ => ⟨rfl⟩
  have hL := fun (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D) =>
    LiftMeanEntrywise.setting_meanLetter_entrywise P Cc hseq hh hhh n hn hnR
  refine ⟨LiftMeanEntrywise.meanLetter Q Cc, ?_⟩
  exact
    { perm := fun r hr n hn hnR => (hL r hr n hn hnR).1
      smooth := fun r hr n hn hnR => (hL r hr n hn hnR).2.1
      meas := fun r hr n hn hnR => (hL r hr n hn hnR).2.2.1
      pres := fun r hr n hn hnR => (hL r hr n hn hnR).2.2.2.1
      bound := fun r hr n hn hnR => (hL r hr n hn hnR).2.2.2.2.1
      diag := fun n hn hnR => (hL 0 (Nat.zero_le H) n hn hnR).2.2.2.2.2.1 rfl
      shift := fun T hG hc r hr n hn hnR => (hL r hr n hn hnR).2.2.2.2.2.2 T hG hc
      explicit := fun _ _ => rfl }

end AVRegularity.CycleComparison.Assembly
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Assembly

/-! The means stage of `cycle_comparison` (clauses 1 to 3), for a finite family of pulses with
their lift settings: the lift sequences exist (`cycle_lift_exists`), their chart-frame letters
exist (`cycle_lift_mean_entrywise`), the Eulerian letters `adLetter`, `ceLetter` present the glued
means, and the edge letters satisfy the means bound with the path products of the edge majorant.
The pulse data are abstract; the
renewal charts and the pulses of the construction are substituted by the consumer. -/

open AVRegularity.CycleComparison.ActualMeans

/-- Powers of an entrywise nonnegative matrix are entrywise nonnegative. -/
theorem matrix_pow_apply_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}
    (hA : ∀ v u, 0 ≤ A v u) (r : ℕ) (v u : ι) : 0 ≤ (A ^ r) v u := by
  induction r generalizing v u with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    split_ifs <;> norm_num
  | succ r ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun w _ => mul_nonneg (ih v w) (hA w u)

/-- The scalar letters used when every component space is trivial (the chart-frame letters then
carry no information): the order-two letter is the reference flux `-𝖩/B` at the physical time
`c s`, the others vanish. With them the diagonal letter `adLetter` is small in every case. -/
def refFallback (B c : ℝ) (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) :
    ℤ → (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ → Vec 2 → ℝ :=
  fun _ n d α l s _ => if n = 2 then -(B⁻¹ * jmEntry Jm (c * s) (d - 1) α l) else 0

theorem refFallback_two (B c : ℝ) (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (k : ℤ) (d : ℕ)
    (α : DerivativeWord2 (d - 1)) (l : Fin 2) (s : ℝ) (X : Vec 2) :
    refFallback B c Jm k 2 d α l s X = -(B⁻¹ * jmEntry Jm (c * s) (d - 1) α l) := by
  rw [refFallback, ite_eq_left rfl]

theorem refFallback_of_ne (B c : ℝ) (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (k : ℤ) {n : ℕ}
    (hn : n ≠ 2) (d : ℕ) (α : DerivativeWord2 (d - 1)) (l : Fin 2) (s : ℝ) (X : Vec 2) :
    refFallback B c Jm k n d α l s X = 0 := by
  rw [refFallback, ite_eq_right hn]

theorem contDiff_refFallback (B c : ℝ) (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (k : ℤ) (n d : ℕ)
    (α : DerivativeWord2 (d - 1)) (l : Fin 2) (s : ℝ) (m : ℕ∞) :
    ContDiff ℝ m (refFallback B c Jm k n d α l s) :=
  contDiff_const

theorem measurable_refFallback (B c : ℝ) {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hJm : ∀ i j, Measurable fun t => Jm t i j) (k : ℤ) (n d : ℕ)
    (α : DerivativeWord2 (d - 1)) (l : Fin 2) (X : Vec 2) (a b : ℝ) :
    Measurable (fun s : Set.Icc a b => refFallback B c Jm k n d α l s X) := by
  by_cases hn : n = 2
  · subst hn
    simp only [refFallback_two]
    exact ((measurable_jmEntry Jm hJm (d - 1) α l).comp
      (measurable_subtype_coe.const_mul c)).const_mul B⁻¹ |>.neg
  · simp only [refFallback_of_ne B c Jm k hn]
    exact measurable_const

/-- **The means stage.** -/
theorem means_stage (N K k L D H : ℕ) (hD : 2 ≤ D) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ)
    (Cχ : ℕ → ℝ) :
    ∃ C₂ C₁ Ct : ℝ, 0 ≤ C₂ ∧ 0 ≤ C₁ ∧ 0 ≤ Ct ∧
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
        (kset : Finset ℤ) (ϖ : ℤ → ℝ → ℝ) (T₀ T₁ e ν B ρ E ℓ dstar : ℝ) (π : ι → ℝ)
        (b : ι → ι → ℝ) (Θ : ℝ) (Q : ℤ → LiftOperatorData ι h D)
        (chart label : ℤ → ℝ → Vec 2 → Vec 2) (s₀ s₁ : ℤ → ℝ) (par : ℤ → Fin 2)
        (V : ℤ → ℝ → ℝ → ℝ) (qs qf : ℕ) (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ),
        (∀ x, 0 < π x) → (∀ v u, 0 ≤ b v u) →
        0 < ℓ → 0 < B → 0 < ρ → 0 < E → dstar = ℓ * Real.sqrt B → dstar ≤ ρ → ρ ≤ E →
        -- the lift setting of every pulse
        (∀ k₁ ∈ kset, IsLiftSetting (Q k₁) π (s₀ k₁) (s₁ k₁) e ν B ρ E ℓ dstar (dstar / ρ)
          (ρ / E) (par k₁) (V k₁) H N K k L qs qf CG Cw Cj b Θ) →
        (∀ i j, Measurable fun t => Jm t i j) →
        -- the partition
        (∀ k₁ ∈ kset, ∀ t, 0 ≤ ϖ k₁ t) → (∀ k₁ ∈ kset, Measurable (ϖ k₁)) →
        (∀ t ∈ Set.Icc T₀ T₁, ∑ k₁ ∈ kset, ϖ k₁ t = 1) →
        (∀ k₁ ∈ kset, ∀ t ∈ Set.Icc T₀ T₁, ϖ k₁ t ≠ 0 →
          (ℓ ^ 2)⁻¹ * t ∈ Set.Icc (s₀ k₁) (s₁ k₁)) →
        -- the charts
        (∀ k₁ ∈ kset, ∀ t y, label k₁ t (chart k₁ t y) = y) →
        (∀ k₁ ∈ kset, ∀ t x, chart k₁ t (label k₁ t x) = x) →
        (∀ k₁ ∈ kset, ∀ t (p : Fin 2 → ℤ) y,
          chart k₁ t (y + AVenhance.latticeShift p) = chart k₁ t y + AVenhance.latticeShift p) →
        (∀ k₁ ∈ kset, ∀ t y, (jacMatrix (chart k₁ t) y).det = 1) →
        (∀ k₁ ∈ kset, ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Vec 2 => chart k₁ q.1 q.2)) →
        (∀ k₁ ∈ kset, ContDiff ℝ (⊤ : ℕ∞) (fun q : ℝ × Vec 2 => label k₁ q.1 q.2)) →
        (∀ k₁ ∈ kset, ∀ t ∈ Set.Icc T₀ T₁, (ℓ ^ 2)⁻¹ * t ∈ Set.Icc (s₀ k₁) (s₁ k₁) →
          ∀ p, 1 ≤ p → p ≤ K + 1 + N + D → ∀ y,
          ‖iteratedFDeriv ℝ p (chart k₁ t) y‖ ≤ Cχ p * E⁻¹ ^ (p - 1) ∧
          ‖iteratedFDeriv ℝ p (label k₁ t) y‖ ≤ Cχ p * E⁻¹ ^ (p - 1)) →
        -- slow periodicity of the lift data
        (∀ k₁ ∈ kset, ∀ (p : Fin 2 → ℤ) t X i j,
          (Q k₁).G t (X + ρ⁻¹ • AVenhance.latticeShift p) i j = (Q k₁).G t X i j) →
        (∀ k₁ ∈ kset, ∀ (p : Fin 2 → ℤ) v u d, ∀ γ ∈ (Q k₁).edge v u d, ∀ α t X z,
          γ.coeff α t (X + ρ⁻¹ • AVenhance.latticeShift p) z = γ.coeff α t X z) →
      ∃ (Cc : ℤ → ℕ → ℕ → LiftCoeff ι h) (Lb : ℤ → ℕ → ℕ → MeanCoeff ι h)
        (Lsc : ℤ → (n d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ → Vec 2 → ℝ),
        (∀ k₁ ∈ kset, IsLiftSequence (Q k₁) (K + D + 2) (max (k + 1) (L + 2)) (s₀ k₁) (s₁ k₁)
          N H (Cc k₁)) ∧
        (∀ k₁ ∈ kset, IsPulseLetters (Q k₁) (Cc k₁) π b (s₀ k₁) (s₁ k₁) (ρ / E) C₂ N H K
          (Lb k₁)) ∧
        (∀ k₁ ∈ kset, ∀ n, 2 ≤ n → n ≤ N + D → ∀ d, 2 ≤ d → d ≤ n →
          ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2), ∀ s ∈ Set.Icc (s₀ k₁) (s₁ k₁), ∀ X,
            (∀ (v : ι) (ξ : h v), Lb k₁ 0 n d α s X l v v ξ = Lsc k₁ n d α l s X • ξ) ∧
            (∀ v u : ι, v ≠ u → Lb k₁ 0 n d α s X l v u = 0)) ∧
        (∀ k₁ ∈ kset, ∀ n, 2 ≤ n → n ≤ N + D → ∀ d, 2 ≤ d → d ≤ n →
          ∀ (α : DerivativeWord2 (d - 1)) (l : Fin 2), ∀ s ∈ Set.Icc (s₀ k₁) (s₁ k₁),
            ContDiff ℝ ((K + 1 : ℕ) : ℕ∞) (Lsc k₁ n d α l s)) ∧
        IsScalarReading (fun k₁ n => Lb k₁ 0 n) Lsc (refFallback B (ℓ ^ 2) Jm) ∧
        IsActualMeans N D H (K + 1) C₁ kset ϖ T₀ T₁ (ℓ ^ 2) ρ (dstar / ρ) (ρ / E) E Q Cc
          chart label s₀ s₁ Lb Jm
          (adLetter kset ϖ (ℓ ^ 2) ρ (dstar / ρ) (N + D) chart label s₀ s₁ Lsc Jm)
          (ceLetter kset ϖ (ℓ ^ 2) ρ (dstar / ρ) (N + D) chart label s₀ s₁ Lb) ∧
        (∀ r, 1 ≤ r → r ≤ H → ∀ K' : ℕ, K' ≤ K + 1 → ∀ v u,
          ENNReal.ofReal (Real.sqrt (π u / π v)) *
            ((∑ d : Finset.Icc 2 (N + D), coefficientSeminorm E K' T₀ T₁
                (ceLetter kset ϖ (ℓ ^ 2) ρ (dstar / ρ) (N + D) chart label s₀ s₁ Lb r v u d) *
                (ENNReal.ofReal (B * E ^ (d.1 - 2)))⁻¹) +
              ∑ d : Finset.Icc 2 (N + D), coefficientSeminorm ρ K' T₀ T₁
                (ceLetter kset ϖ (ℓ ^ 2) ρ (dstar / ρ) (N + D) chart label s₀ s₁ Lb r v u d) *
                (ENNReal.ofReal (B * ρ ^ (d.1 - 2)))⁻¹) ≤
            ENNReal.ofReal (2 * ((N + D : ℕ) : ℝ) ^ 2 * ((K' : ℝ) + 1) * (Ct * C₂) *
              (Real.sqrt (π u / π v) *
                ((Matrix.of fun v' u' => b v' u' / Real.sqrt (π u' / π v')) ^ r) v u))) := by
  obtain ⟨C₂, hC₂, hletters⟩ := exists_pulseLetters N K k L D H CG Cw Cj
  obtain ⟨C₁, hC₁, hmeans⟩ := actual_means_explicit N D H (K + 1) hD Cχ
  obtain ⟨Ct, hCt, hbound⟩ := ceLetter_means_bound N D (K + 1) Cχ
  refine ⟨C₂, C₁, Ct, hC₂, hC₁, hCt, ?_⟩
  intro ι _ _ h _ _ _ _ kset ϖ T₀ T₁ e ν B ρ E ℓ dstar π b Θ Q chart label s₀ s₁ par V qs qf Jm
    hπ hb hℓ hB hρ hE hd hdρ hρE hset hJm hϖ0 hϖm hϖ1 hsupp hlc hcl hequiv hdet hchartJ hlabelJ
    hjets hGper hcper
  -- the lift sequences
  choose! Cc hCc using fun k₁ (hk₁ : k₁ ∈ kset) =>
    Providers.cycle_lift_exists N K k L D H CG Cw Cj (Q k₁) π (s₀ k₁) (s₁ k₁) e ν B ρ E ℓ dstar
      (dstar / ρ) (ρ / E) (par k₁) (V k₁) qs qf b Θ (hset k₁ hk₁)
  -- the chart-frame letters
  choose! Lb hLb using fun k₁ (hk₁ : k₁ ∈ kset) =>
    hletters (Q k₁) π (s₀ k₁) (s₁ k₁) e ν B ρ E ℓ dstar (dstar / ρ) (ρ / E) (par k₁) (V k₁)
      qs qf b Θ (hset k₁ hk₁) (Cc k₁) (hCc k₁ hk₁)
  choose! Ls hLs using fun k₁ (hk₁ : k₁ ∈ kset) (n : ℕ) (hn : 2 ≤ n) (hnR : n ≤ N + D) =>
    (hLb k₁ hk₁).diag n hn hnR
  have hdstar : 0 ≤ dstar := by
    rw [hd]
    exact mul_nonneg hℓ.le (Real.sqrt_nonneg _)
  have hchart_t : ∀ k₁ ∈ kset, ∀ t, ContDiff ℝ (⊤ : ℕ∞) (chart k₁ t) := fun k₁ hk₁ t =>
    (hchartJ k₁ hk₁).comp ((contDiff_const (c := t)).prodMk contDiff_id)
  have hlabel_t : ∀ k₁ ∈ kset, ∀ t, ContDiff ℝ (⊤ : ℕ∞) (label k₁ t) := fun k₁ hk₁ t =>
    (hlabelJ k₁ hk₁).comp ((contDiff_const (c := t)).prodMk contDiff_id)
  -- the Eulerian letters
  obtain ⟨Lsc, hsc, hscC, hdeg, hAM⟩ := hmeans kset ϖ T₀ T₁ (ℓ ^ 2) ρ (dstar / ρ) (ρ / E) E Q Cc
    chart label s₀ s₁ Lb Ls (refFallback B (ℓ ^ 2) Jm) Jm (Nat.succ_le_succ (Nat.zero_le K))
    (pow_pos hℓ 2) hρ
    (div_nonneg hdstar hρ.le) hE rfl hJm hϖm hsupp hlc hcl hequiv hdet hchartJ hlabelJ hjets
    (fun k₁ hk₁ r hr n hn hnR => (hLb k₁ hk₁).pres r hr n hn hnR)
    (fun k₁ hk₁ r hr n hn hnR d _ _ α k₀ v u s hs =>
      (hLb k₁ hk₁).smooth r hr n hn hnR d α k₀ v u s hs)
    (fun k₁ hk₁ r hr n hn hnR d _ _ α k₀ v u X =>
      (hLb k₁ hk₁).meas r hr n hn hnR d α k₀ v u X)
    (fun k₁ hk₁ r hr n hn hnR d _ _ α k₀ v u s hs p X =>
      (hLb k₁ hk₁).shift (ρ⁻¹ • AVenhance.latticeShift p)
        (fun t X i j => hGper k₁ hk₁ p t X i j)
        (fun v u d γ hγ α t X z => hcper k₁ hk₁ p v u d γ hγ α t X z)
        r hr n hn hnR d α k₀ v u s hs X)
    (fun k₁ hk₁ n hn hnR d hd2 hdn α k₀ s hs X => hLs k₁ hk₁ n hn hnR d hd2 hdn α k₀ s hs X)
    (fun k₁ _ n _ _ d _ _ α l s _ => contDiff_refFallback B (ℓ ^ 2) Jm k₁ n d α l s _)
    (fun k₁ _ n _ _ d _ _ α l X => measurable_refFallback B (ℓ ^ 2) hJm k₁ n d α l X _ _)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl)
  refine ⟨Cc, Lb, Lsc, hCc, hLb, hsc, hscC, hdeg, hAM, ?_⟩
  -- clause 3
  intro r hr1 hrH K' hK' v u
  have hA0 : ∀ v' u', 0 ≤ (Matrix.of fun v' u' => b v' u' / Real.sqrt (π u' / π v')) v' u' :=
    fun v' u' => div_nonneg (hb v' u') (Real.sqrt_nonneg _)
  have hM0 : 0 ≤ C₂ * ((Matrix.of fun v' u' => b v' u' / Real.sqrt (π u' / π v')) ^ r) v u :=
    mul_nonneg hC₂ (matrix_pow_apply_nonneg hA0 r v u)
  have h3 := hbound kset ϖ ℓ B dstar ρ E T₀ T₁ chart label s₀ s₁ Lb r v u
    (C₂ * ((Matrix.of fun v' u' => b v' u' / Real.sqrt (π u' / π v')) ^ r) v u)
    hℓ hB hρ hd hdρ hρE hM0 hϖ0 hϖ1 hchart_t hlabel_t hjets
    (fun k₁ hk₁ n hn hnR d _ _ α k₀ s hs => (hLb k₁ hk₁).smooth r hrH n hn hnR d α k₀ v u s hs)
    (fun k₁ hk₁ n hn hnR d hd2 hdn α k₀ i hi s hs X =>
      (hLb k₁ hk₁).bound r hrH n hn hnR d hd2 hdn α k₀ v u i hi s hs X) K' hK'
  refine (mul_le_mul' le_rfl h3).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  congr 1
  ring

end AVRegularity.CycleComparison.Assembly
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Assembly

/-! The edge majorant masked by the edges of the charted family: the edges of the family
are the pairs `u → v` with a constituent identity (`Γ v u` nonempty). Masking keeps the
pointwise analytic envelope, the nonnegativity and the two weighted sums; the masked conjugated
majorant is nilpotent of order `H + 1` by the depth of the family; masked path products are at
most the unmasked ones; conjugation by the masses commutes with powers. -/

open AVRegularity.CycleComparison.Coarse

section Family

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- The edge relation of a charted family: `u → v` is an edge when `Γ v u` is nonempty. -/
def familyAdj (F : ChartedFamily ι h D P Ctx) (v u : ι) : Prop := Nonempty (F.Γ v u)

/-- The edge relation is decided classically. -/
noncomputable instance familyAdjDecidable (F : ChartedFamily ι h D P Ctx) :
    DecidableRel (familyAdj F) :=
  fun _ _ => Classical.propDecidable _

/-- An edge majorant masked by the edges of the family. -/
def familyMask (F : ChartedFamily ι h D P Ctx) (b : ι → ι → ℝ) : ι → ι → ℝ :=
  fun v u => maskedEdgeMatrix (familyAdj F) (Matrix.of b) v u

theorem familyMask_apply (F : ChartedFamily ι h D P Ctx) (b : ι → ι → ℝ) (v u : ι) :
    familyMask F b v u = if familyAdj F v u then b v u else 0 := rfl

theorem familyMask_nonneg (F : ChartedFamily ι h D P Ctx) {b : ι → ι → ℝ}
    (hb : ∀ v u, 0 ≤ b v u) (v u : ι) : 0 ≤ familyMask F b v u :=
  maskedEdgeMatrix_nonneg (familyAdj F) (Matrix.of b) hb v u

theorem familyMask_le (F : ChartedFamily ι h D P Ctx) {b : ι → ι → ℝ}
    (hb : ∀ v u, 0 ≤ b v u) (v u : ι) : familyMask F b v u ≤ b v u :=
  maskedEdgeMatrix_le (familyAdj F) (Matrix.of b) hb v u

theorem familyMask_row_le [Fintype ι] (F : ChartedFamily ι h D P Ctx) {b : ι → ι → ℝ}
    (hb : ∀ v u, 0 ≤ b v u) {S : ℝ} (hrow : ∀ v, ∑ u, b v u ≤ S) (v : ι) :
    ∑ u, familyMask F b v u ≤ S :=
  (Finset.sum_le_sum fun u _ => familyMask_le F hb v u).trans (hrow v)

theorem familyMask_col_le [Fintype ι] (F : ChartedFamily ι h D P Ctx) {b : ι → ι → ℝ}
    (hb : ∀ v u, 0 ≤ b v u) {S : ℝ} (hcol : ∀ u, ∑ v, b v u ≤ S) (u : ι) :
    ∑ v, familyMask F b v u ≤ S :=
  (Finset.sum_le_sum fun v _ => familyMask_le F hb v u).trans (hcol u)

/-- Masking keeps the pointwise analytic envelope: without an identity the edge sum is empty. -/
theorem pointwiseAnalyticEnvelope_familyMask (F : ChartedFamily ι h D P Ctx) (π : ι → ℝ)
    (dom : F.Domain) (E C : ℝ) (Ks Ls : ℕ) {b : ι → ι → ℝ}
    (hF : IsPointwiseAnalyticEnvelope F π dom E C Ks Ls b) :
    IsPointwiseAnalyticEnvelope F π dom E C Ks Ls (familyMask F b) := by
  refine ⟨hF.1, fun v u => ?_⟩
  by_cases hadj : familyAdj F v u
  · rw [familyMask_apply, ite_eq_left hadj]
    exact hF.2 v u
  · have : IsEmpty (F.Γ v u) := not_nonempty_iff.1 hadj
    rw [Fintype.sum_empty, mul_zero]
    exact zero_le

/-- Without a path of `H + 1` edges, the edge relation has no chain of `H + 1` steps. -/
theorem familyAdj_no_chain (F : ChartedFamily ι h D P Ctx) {H : ℕ} (hdepth : F.HasDepthAtMost H)
    (p : Fin (H + 2) → ι) : ∃ k : Fin (H + 1), ¬ familyAdj F (p k.castSucc) (p k.succ) := by
  obtain ⟨k, hk⟩ := hdepth (fun i => p (Fin.rev i))
  refine ⟨Fin.rev k, ?_⟩
  intro hadj
  have e1 : (Fin.rev k).castSucc = Fin.rev k.succ := (Fin.rev_succ k).symm
  have e2 : (Fin.rev k).succ = Fin.rev k.castSucc := (Fin.rev_castSucc k).symm
  rw [e1, e2] at hadj
  exact (not_nonempty_iff.2 hk) hadj

/-- **The masked majorant is nilpotent** of order `H + 1`. -/
theorem familyMask_pow_eq_zero [Fintype ι] [DecidableEq ι] (F : ChartedFamily ι h D P Ctx)
    {H : ℕ} (hdepth : F.HasDepthAtMost H) (b : ι → ι → ℝ) :
    (Matrix.of (familyMask F b)) ^ (H + 1) = 0 :=
  maskedEdgeMatrix_pow_eq_zero (familyAdj F) (Matrix.of b) H (familyAdj_no_chain F hdepth)

/-- The masked conjugated majorant is the conjugate of the masked physical majorant. -/
theorem familyMask_conj (F : ChartedFamily ι h D P Ctx) {π : ι → ℝ} (hπ : ∀ x, 0 < π x)
    (A : Matrix ι ι ℝ) :
    (Matrix.of fun v u => familyMask F (fun v' u' => Real.sqrt (π u' / π v') * A v' u') v u /
      Real.sqrt (π u / π v)) = maskedEdgeMatrix (familyAdj F) A := by
  ext v u
  have hs : Real.sqrt (π u / π v) ≠ 0 := (Real.sqrt_pos.2 (div_pos (hπ u) (hπ v))).ne'
  rw [Matrix.of_apply, familyMask_apply, maskedEdgeMatrix_apply]
  split_ifs
  · rw [mul_div_assoc, mul_comm, div_mul_cancel₀ _ hs]
  · rw [zero_div]

/-- The masked conjugated majorant is the conjugate of the masked physical majorant, entrywise. -/
theorem familyMask_eq_conj (F : ChartedFamily ι h D P Ctx) (π : ι → ℝ) (A : Matrix ι ι ℝ)
    (v u : ι) :
    familyMask F (fun v' u' => Real.sqrt (π u' / π v') * A v' u') v u =
      Real.sqrt (π u / π v) * maskedEdgeMatrix (familyAdj F) A v u := by
  rw [familyMask_apply, maskedEdgeMatrix_apply]
  split_ifs
  · rfl
  · rw [mul_zero]

end Family

section Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Conjugation by the masses commutes with powers:
`(√(π_u/π_v) M_{vu})^r = √(π_u/π_v) (M^r)_{vu}`. -/
theorem conj_pow_apply {π : ι → ℝ} (hπ : ∀ x, 0 < π x) (M : Matrix ι ι ℝ) (r : ℕ) (v u : ι) :
    ((Matrix.of fun v' u' => Real.sqrt (π u' / π v') * M v' u') ^ r) v u =
      Real.sqrt (π u / π v) * (M ^ r) v u := by
  induction r generalizing u with
  | zero =>
    rw [pow_zero, pow_zero, Matrix.one_apply]
    split_ifs with hvu
    · rw [hvu, div_self (hπ u).ne', Real.sqrt_one, mul_one]
    · rw [mul_zero]
  | succ r ih =>
    rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [ih w, Matrix.of_apply]
    have e : Real.sqrt (π w / π v) * Real.sqrt (π u / π w) = Real.sqrt (π u / π v) := by
      rw [← Real.sqrt_mul (div_pos (hπ w) (hπ v)).le]
      congr 1
      rw [div_mul_div_comm, mul_comm (π w) (π u), mul_div_mul_right _ _ (hπ w).ne']
    calc Real.sqrt (π w / π v) * (M ^ r) v w * (Real.sqrt (π u / π w) * M w u)
        = (Real.sqrt (π w / π v) * Real.sqrt (π u / π w)) * ((M ^ r) v w * M w u) := by ring
      _ = Real.sqrt (π u / π v) * ((M ^ r) v w * M w u) := by rw [e]

/-- Masked path products are at most the unmasked ones. -/
theorem maskedEdgeMatrix_pow_le (adj : ι → ι → Prop) [DecidableRel adj] {A : Matrix ι ι ℝ}
    (hA : ∀ v u, 0 ≤ A v u) (r : ℕ) (v u : ι) :
    (maskedEdgeMatrix adj A ^ r) v u ≤ (A ^ r) v u := by
  induction r generalizing u with
  | zero => exact le_rfl
  | succ r ih =>
    rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_le_sum fun w _ => ?_
    exact mul_le_mul (ih w) (maskedEdgeMatrix_le adj A hA w u)
      (maskedEdgeMatrix_nonneg adj A hA w u) (matrix_pow_apply_nonneg hA r v w)

end Matrix

end AVRegularity.CycleComparison.Assembly
end

section
open Homogenization
open scoped ENNReal
namespace AVRegularity.CycleComparison.Assembly

/-! The letter fields of the coarse setting `IsCoarseSetting` from the clauses of
`cycle_comparison`: a finite normalized sum of seminorms has
finite terms (`AD_fin`, `CE_fin`), and the entrywise means bound with path products of the
masked majorant gives `edge_mean` with `C_*^r (A_edge^r)_{vu}` for the conjugated masked
majorant. -/

/-- A term of a sum of seminorms divided by finite positive weights, bounded by a real number,
is finite. -/
theorem ne_top_of_sum_inv_le {N' : ℕ} (x : Finset.Icc 2 N' → ℝ≥0∞) (S : Finset.Icc 2 N' → ℝ)
    {c : ℝ} (h : ∑ d, x d * (ENNReal.ofReal (S d))⁻¹ ≤ ENNReal.ofReal c)
    (d : Finset.Icc 2 N') : x d ≠ ⊤ := by
  intro hx
  have h1 : x d * (ENNReal.ofReal (S d))⁻¹ ≤ ∑ d', x d' * (ENNReal.ofReal (S d'))⁻¹ :=
    Finset.single_le_sum (f := fun d' => x d' * (ENNReal.ofReal (S d'))⁻¹)
      (fun _ _ => zero_le) (Finset.mem_univ d)
  rw [hx, ENNReal.top_mul (ENNReal.inv_ne_zero.2 ENNReal.ofReal_ne_top)] at h1
  exact ENNReal.ofReal_ne_top (top_le_iff.1 (h1.trans h))

/-- **`edge_mean` from the means bound.** If the two normalized sums of a grade-`r` edge letter
are bounded by `c √(π_u/π_v) (M^r)_{vu}`, the second one is bounded by `C_*^r (A^r)_{vu}` for
the conjugated majorant `A_{vu} = √(π_u/π_v) M_{vu}` and any `C_* ≥ max 1 c`. -/
theorem edge_mean_of_bound {ι : Type*} [Fintype ι] [DecidableEq ι] {π : ι → ℝ}
    (hπ : ∀ x, 0 < π x) {M : Matrix ι ι ℝ} (hM : ∀ v u, 0 ≤ M v u) {c Cstar : ℝ}
    (hC : max 1 c ≤ Cstar) {r : ℕ} (hr : 1 ≤ r) {v u : ι} {X Y : ℝ≥0∞}
    (h : ENNReal.ofReal (Real.sqrt (π u / π v)) * (X + Y) ≤
      ENNReal.ofReal (c * (Real.sqrt (π u / π v) * (M ^ r) v u))) :
    ENNReal.ofReal (Real.sqrt (π u / π v)) * Y ≤
      ENNReal.ofReal (Cstar ^ r *
        ((Matrix.of fun v' u' => Real.sqrt (π u' / π v') * M v' u') ^ r) v u) := by
  refine (mul_le_mul' le_rfl le_add_self).trans (h.trans (ENNReal.ofReal_le_ofReal ?_))
  rw [conj_pow_apply hπ M r v u]
  have h0 : 0 ≤ Real.sqrt (π u / π v) * (M ^ r) v u :=
    mul_nonneg (Real.sqrt_nonneg _) (matrix_pow_apply_nonneg hM r v u)
  have h1 : (1 : ℝ) ≤ Cstar := (le_max_left 1 c).trans hC
  have hcC : c ≤ Cstar ^ r :=
    ((le_max_right 1 c).trans hC).trans (le_self_pow₀ h1 (by omega))
  exact mul_le_mul_of_nonneg_right hcC h0

end AVRegularity.CycleComparison.Assembly
end
