-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.CompactChainExistence
public import AVRegularity.CycleWords.Assembly.InteriorScalarIngredients
import AVRegularity.CycleEvolution.CellEnergySpaceRawDirectionalLimit

section
@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # The weight algebra

Write `g_r = r − τ(r)` for the age of the last activity.
* Above `1`, the weight is exactly `Λ e^{-c g_r}` (`activityWeight_eq_of_one_lt`).
* With activity, it is at least `Λ e^{-c g_r}` (`le_activityWeight`).
* The quiet lag of `[s, t]` and the age at `s` add up to at least the age at `t`
  (`age_le_add_lag`), since `τ(t) ≥ τ(s)`.

So the weight at `s` times the surplus of `[s, t]` is paid by the weight at `t`, with the
level drop `Λ₂ P_e^{Q} ≤ Λ₁` (`weight_surplus_le`). -/

variable {v : ℝ → Vec 2 → Vec 2} {t₀ : ℝ}

theorem activityWeight_eq_of_one_lt {Λ c r : ℝ} (h : 1 < activityWeight v t₀ Λ c r) :
    activityWeight v t₀ Λ c r = Λ * Real.exp (-c * (r - lastActive v t₀ r)) := by
  unfold activityWeight at h ⊢
  by_cases hne : (activeSet v t₀ r).Nonempty
  · simp only [hne, ite_true] at h ⊢
    rcases le_total 1 (Λ * Real.exp (-c * (r - lastActive v t₀ r))) with h' | h'
    · exact max_eq_right h'
    · rw [max_eq_left h'] at h
      exact absurd h (lt_irrefl _)
  · simp only [hne, ite_false] at h
    exact absurd h (lt_irrefl _)

theorem le_activityWeight {Λ c r : ℝ} (hne : (activeSet v t₀ r).Nonempty) :
    Λ * Real.exp (-c * (r - lastActive v t₀ r)) ≤ activityWeight v t₀ Λ c r := by
  unfold activityWeight
  simp only [hne, ite_true]
  exact le_max_right _ _

/-- The age at `t` is at most the age at `s` plus the quiet lag of `[s, t]`. -/
theorem age_le_add_lag {s t : ℝ} (hst : s ≤ t) (hne : (activeSet v t₀ s).Nonempty) :
    t - lastActive v t₀ t ≤ (s - lastActive v t₀ s) + quietLag v t₀ s t := by
  have hsub : activeSet v t₀ s ⊆ activeSet v t₀ t := fun x hx => ⟨⟨hx.1.1, hx.1.2.trans hst⟩, hx.2⟩
  have hnet : (activeSet v t₀ t).Nonempty := hne.mono hsub
  have hmono : lastActive v t₀ s ≤ lastActive v t₀ t :=
    csSup_le_csSup ⟨t, fun x hx => hx.1.2⟩ hne hsub
  have hτs : lastActive v t₀ s ≤ s := csSup_le hne fun x hx => hx.1.2
  unfold quietLag
  simp only [hnet, ite_true]
  rcases le_total (t - s) (t - lastActive v t₀ t) with h | h
  · rw [min_eq_left h]
    linarith
  · rw [min_eq_right h]
    linarith

/-- **The weight at `s` and the surplus of `[s, t]` are paid by the weight at `t`.** -/
theorem weight_surplus_le {Λ₁ Λ₂ c P : ℝ} {Q : ℕ} (hc : 0 ≤ c) (hP : 0 ≤ P) {s t : ℝ}
    (hst : s ≤ t) (hΩ : 1 < activityWeight v t₀ Λ₂ c s)
    (hΛ : Λ₂ * P ^ Q ≤ Λ₁) :
    activityWeight v t₀ Λ₂ c s * (P ^ Q * Real.exp (-c * quietLag v t₀ s t)) ≤
      activityWeight v t₀ Λ₁ c t := by
  have hne : (activeSet v t₀ s).Nonempty := by
    by_contra h
    unfold activityWeight at hΩ
    simp only [h, ite_false] at hΩ
    exact lt_irrefl _ hΩ
  have hsub : activeSet v t₀ s ⊆ activeSet v t₀ t := fun x hx => ⟨⟨hx.1.1, hx.1.2.trans hst⟩, hx.2⟩
  rw [activityWeight_eq_of_one_lt hΩ]
  refine le_trans ?_ (le_activityWeight (hne.mono hsub))
  have hage := age_le_add_lag hst hne
  have he : Real.exp (-c * (s - lastActive v t₀ s)) * Real.exp (-c * quietLag v t₀ s t) ≤
      Real.exp (-c * (t - lastActive v t₀ t)) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith)
  have hΛ₂ : 0 ≤ Λ₂ := by
    by_contra h
    push Not at h
    have := (activityWeight_eq_of_one_lt hΩ).symm ▸ hΩ
    have : Λ₂ * Real.exp (-c * (s - lastActive v t₀ s)) < 0 :=
      mul_neg_of_neg_of_pos h (Real.exp_pos _)
    linarith
  have hPQ : 0 ≤ P ^ Q := pow_nonneg hP Q
  calc Λ₂ * Real.exp (-c * (s - lastActive v t₀ s)) * (P ^ Q * Real.exp (-c * quietLag v t₀ s t))
      = (Λ₂ * P ^ Q) * (Real.exp (-c * (s - lastActive v t₀ s)) *
          Real.exp (-c * quietLag v t₀ s t)) := by ring
    _ ≤ Λ₁ * Real.exp (-c * (t - lastActive v t₀ t)) :=
        mul_le_mul hΛ he (by positivity) ((mul_nonneg hΛ₂ hPQ).trans hΛ)

theorem activeSet_nonempty_of_weight {Λ c r : ℝ} (h : 1 < activityWeight v t₀ Λ c r) :
    (activeSet v t₀ r).Nonempty := by
  by_contra hne
  unfold activityWeight at h
  simp only [hne, ite_false] at h
  exact lt_irrefl _ h

/-- The weight is at most its level. -/
theorem activityWeight_le {Λ c r : ℝ} (hΛ : 1 ≤ Λ) (hc : 0 ≤ c) :
    activityWeight v t₀ Λ c r ≤ Λ := by
  unfold activityWeight
  split_ifs with hne
  · refine max_le hΛ ?_
    have hτ : lastActive v t₀ r ≤ r := csSup_le hne fun x hx => hx.1.2
    have he : Real.exp (-c * (r - lastActive v t₀ r)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith)
    calc Λ * Real.exp (-c * (r - lastActive v t₀ r)) ≤ Λ * 1 :=
          mul_le_mul_of_nonneg_left he (by linarith)
      _ = Λ := mul_one Λ
  · exact hΛ

/-- A quiet gap `(γ − δ', γ]` behind `γ` gives the lag `δ ≤ min(γ − s, δ')`. -/
theorem quietLag_ge_of_gap {S s γ δ δ' : ℝ} (hγs : δ ≤ γ - s) (hδ : δ ≤ δ') (hγS : γ ≤ t₀ + S)
    (hgap : ∀ τ ∈ Ioc (γ - δ') γ, τ ∈ Icc t₀ (t₀ + S) → ¬ IsActiveTime v τ) :
    δ ≤ quietLag v t₀ s γ := by
  unfold quietLag
  split_ifs with hne
  · refine le_min hγs ?_
    have : lastActive v t₀ γ ≤ γ - δ' := csSup_le hne fun x hx => by
      by_contra hlt
      push Not at hlt
      exact hgap x ⟨hlt, hx.1.2⟩ ⟨hx.1.1, hx.1.2.trans hγS⟩ hx.2
    linarith
  · exact hγs

end AVRegularity.CycleWords.Assembly
end

section
namespace AVRegularity.CycleWords.Assembly

/-! # The regime and the sub-case arithmetic

All over the reals, so that the main proof only chains them.

* `regime_mono`: a regime with larger `C_b`, `Q` and smaller `c_b` implies the weaker one.
* `regime_half`: the regime gives `Λ e^{-(3π²/8)(D/2)} ≤ 1` (for the activity geometry, with
  `c_b ≤ 3π²/16`).
* `regime_quarter`: the regime gives `Λ₂ P^{Q_S} e^{-(3π²/8)(D/4)} ≤ 1` (for the crossing, with
  `c_b ≤ 3π²/32` and `Λ₂ P^{Q_S} ≤ Λ₁`).
* `alg_cross`: the weighted defect in the crossing.
* `alg_case_one`: `‖V_T‖ + Ω‖V_N‖` from the two parts, in case 1. -/

theorem regime_mono {Cb Cb' cb cb' Λ J P D : ℝ} {Q Q' : ℕ} (hCb : Cb' ≤ Cb)
    (hcb : cb ≤ cb') (hQ : Q' ≤ Q) (hΛ : 0 ≤ Λ) (hJ : 0 ≤ J) (hP : 1 ≤ P) (hD : 0 ≤ D)
    (h : Cb * Λ * J * P ^ Q * Real.exp (-cb * D) ≤ 1) :
    Cb' * Λ * J * P ^ Q' * Real.exp (-cb' * D) ≤ 1 := by
  rcases le_total Cb' 0 with hneg | hCb'
  · have : Cb' * Λ * J * P ^ Q' * Real.exp (-cb' * D) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hneg hΛ) hJ)
        (pow_nonneg (by linarith) _)) (Real.exp_pos _).le
    linarith
  have h1 : P ^ Q' ≤ P ^ Q := pow_le_pow_right₀ hP hQ
  have h2 : Real.exp (-cb' * D) ≤ Real.exp (-cb * D) := Real.exp_le_exp.2 (by nlinarith)
  have hP0 : 0 ≤ P ^ Q' := pow_nonneg (by linarith) _
  have hA : Cb' * Λ * J ≤ Cb * Λ * J :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCb hΛ) hJ
  have hA0 : 0 ≤ Cb' * Λ * J := mul_nonneg (mul_nonneg hCb' hΛ) hJ
  have hB : Cb' * Λ * J * P ^ Q' ≤ Cb * Λ * J * P ^ Q := mul_le_mul hA h1 hP0 (hA0.trans hA)
  have hB0 : 0 ≤ Cb' * Λ * J * P ^ Q' := mul_nonneg hA0 hP0
  exact (mul_le_mul hB h2 (Real.exp_pos _).le (hB0.trans hB)).trans h

/-- The regime controls `Λ e^{-c_b D}`. -/
theorem regime_base {Cb cb Λ J P D : ℝ} {Q : ℕ} (hCb : 1 ≤ Cb) (hΛ : 0 ≤ Λ) (hJ : 1 ≤ J)
    (hP : 1 ≤ P) (h : Cb * Λ * J * P ^ Q * Real.exp (-cb * D) ≤ 1) :
    Λ * Real.exp (-cb * D) ≤ 1 := by
  have hPQ : 1 ≤ P ^ Q := one_le_pow₀ hP
  have he := (Real.exp_pos (-cb * D)).le
  have hΛe : 0 ≤ Λ * Real.exp (-cb * D) := mul_nonneg hΛ he
  have hX : 1 ≤ Cb * J * P ^ Q := by
    have := mul_le_mul hCb hJ zero_le_one (by linarith)
    nlinarith
  calc Λ * Real.exp (-cb * D) ≤ (Cb * J * P ^ Q) * (Λ * Real.exp (-cb * D)) :=
        le_mul_of_one_le_left hΛe hX
    _ = Cb * Λ * J * P ^ Q * Real.exp (-cb * D) := by ring
    _ ≤ 1 := h

/-- **The regime gives the half-buffer bound of the activity geometry.** -/
theorem regime_half {Cb cb Λ Λ₁ J P D : ℝ} {Q : ℕ} (hCb : 1 ≤ Cb) (hΛ : Λ ≤ Λ₁) (hΛ1 : 0 ≤ Λ₁)
    (hJ : 1 ≤ J) (hP : 1 ≤ P) (hD : 0 ≤ D) (hcb : cb ≤ 3 * Real.pi ^ 2 / 16)
    (h : Cb * Λ₁ * J * P ^ Q * Real.exp (-cb * D) ≤ 1) :
    Λ * Real.exp (-(3 * Real.pi ^ 2 / 8) * (D / 2)) ≤ 1 := by
  have hb := regime_base hCb hΛ1 hJ hP h
  have he : Real.exp (-(3 * Real.pi ^ 2 / 8) * (D / 2)) ≤ Real.exp (-cb * D) :=
    Real.exp_le_exp.2 (by nlinarith)
  calc Λ * Real.exp (-(3 * Real.pi ^ 2 / 8) * (D / 2))
      ≤ Λ₁ * Real.exp (-cb * D) := by
        rcases le_total 0 Λ with h0 | h0
        · exact mul_le_mul hΛ he (Real.exp_pos _).le hΛ1
        · have := mul_nonpos_of_nonpos_of_nonneg h0 (Real.exp_pos
            (-(3 * Real.pi ^ 2 / 8) * (D / 2))).le
          have := mul_nonneg hΛ1 (Real.exp_pos (-cb * D)).le
          linarith
    _ ≤ 1 := hb

/-- **The regime gives the quarter-buffer bound of the crossing.** -/
theorem regime_quarter {Cb cb Λ₁ Λ₂ J P D : ℝ} {Q QS : ℕ} (hCb : 1 ≤ Cb) (hΛ2 : 0 ≤ Λ₂)
    (hΛ : Λ₂ * P ^ QS ≤ Λ₁) (hJ : 1 ≤ J) (hP : 1 ≤ P) (hD : 0 ≤ D)
    (hcb : cb ≤ 3 * Real.pi ^ 2 / 32) (h : Cb * Λ₁ * J * P ^ Q * Real.exp (-cb * D) ≤ 1) :
    Λ₂ * P ^ QS * Real.exp (-(3 * Real.pi ^ 2 / 8) * (D / 4)) ≤ 1 := by
  have hΛ1 : 0 ≤ Λ₁ := (mul_nonneg hΛ2 (pow_nonneg (by linarith) _)).trans hΛ
  have hb := regime_base hCb hΛ1 hJ hP h
  have he : Real.exp (-(3 * Real.pi ^ 2 / 8) * (D / 4)) ≤ Real.exp (-cb * D) :=
    Real.exp_le_exp.2 (by nlinarith)
  calc Λ₂ * P ^ QS * Real.exp (-(3 * Real.pi ^ 2 / 8) * (D / 4))
      ≤ Λ₁ * Real.exp (-cb * D) :=
        mul_le_mul hΛ he (Real.exp_pos _).le hΛ1
    _ ≤ 1 := hb

/-- The weighted defect in the crossing: `Ω₂ ‖V_N‖ ≤ 2 C_S C_A E R`. -/
theorem alg_cross {Ω₂ Λ₂ VN W Wγ CS CA PQ eL E₁ E₂ R : ℝ} (hΩ2 : Ω₂ ≤ Λ₂) (hΩ20 : 0 ≤ Ω₂)
    (hCS : 0 ≤ CS) (hPQ : 0 ≤ PQ) (heL : 0 ≤ eL) (hE₁ : 0 ≤ E₁) (hVN : VN ≤ 2 * W)
    (hW : W ≤ CS * PQ * eL * E₁ * Wγ) (hWγ : Wγ ≤ CA * E₂ * R) (hWγ0 : 0 ≤ Wγ)
    (hreg : Λ₂ * PQ * eL ≤ 1) :
    Ω₂ * VN ≤ 2 * CS * CA * (E₁ * E₂) * R := by
  have h1 : Ω₂ * VN ≤ Ω₂ * (2 * (CS * PQ * eL * E₁ * (CA * E₂ * R))) := by
    refine mul_le_mul_of_nonneg_left (hVN.trans ?_) hΩ20
    have : CS * PQ * eL * E₁ * Wγ ≤ CS * PQ * eL * E₁ * (CA * E₂ * R) :=
      mul_le_mul_of_nonneg_left hWγ (by positivity)
    linarith
  have hY : 0 ≤ CA * E₂ * R := hWγ0.trans hWγ
  have h2 : Ω₂ * (2 * (CS * PQ * eL * E₁ * (CA * E₂ * R))) =
      (Ω₂ * PQ * eL) * (2 * CS * E₁ * (CA * E₂ * R)) := by ring
  have h3 : Ω₂ * PQ * eL ≤ 1 := by
    have : Ω₂ * PQ * eL ≤ Λ₂ * PQ * eL :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hΩ2 hPQ) heL
    linarith
  have h4 : 0 ≤ 2 * CS * E₁ * (CA * E₂ * R) := by positivity
  calc Ω₂ * VN ≤ (Ω₂ * PQ * eL) * (2 * CS * E₁ * (CA * E₂ * R)) := h1.trans_eq h2
    _ ≤ 1 * (2 * CS * E₁ * (CA * E₂ * R)) := mul_le_mul_of_nonneg_right h3 h4
    _ = 2 * CS * CA * (E₁ * E₂) * R := by ring

/-- Case 1: `‖V_T‖ + Ω₂‖V_N‖ ≤ (5C_P + 6C_S) E (T + Ω₁N)`. -/
theorem alg_case_one {a b Ω₁ Ω₂ CP CS E F T N AH BH : ℝ} (hCP : 0 ≤ CP) (hCS : 0 ≤ CS)
    (hE : 0 ≤ E) (hT : 0 ≤ T) (hN : 0 ≤ N) (hΩ1 : 1 ≤ Ω₁) (hΩ2 : 0 ≤ Ω₂)
    (ha : a ≤ CP * E * AH) (hAH : AH ≤ T + 5 * N) (hb : b ≤ CS * F * E * BH)
    (hBH : BH ≤ 6 * N) (hBH0 : 0 ≤ BH) (hΩF : Ω₂ * F ≤ Ω₁) :
    a + Ω₂ * b ≤ (5 * CP + 6 * CS) * E * (T + Ω₁ * N) := by
  have hCPE : 0 ≤ CP * E := mul_nonneg hCP hE
  have hCSE : 0 ≤ CS * E := mul_nonneg hCS hE
  have h1 : a ≤ CP * E * (T + 5 * N) := ha.trans (mul_le_mul_of_nonneg_left hAH hCPE)
  have h2 : Ω₂ * b ≤ (Ω₂ * F) * (CS * E * BH) :=
    calc Ω₂ * b ≤ Ω₂ * (CS * F * E * BH) := mul_le_mul_of_nonneg_left hb hΩ2
      _ = (Ω₂ * F) * (CS * E * BH) := by ring
  have h3 : (Ω₂ * F) * (CS * E * BH) ≤ Ω₁ * (CS * E * BH) :=
    mul_le_mul_of_nonneg_right hΩF (mul_nonneg hCSE hBH0)
  have h4 : Ω₁ * (CS * E * BH) ≤ Ω₁ * (CS * E * (6 * N)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBH hCSE) (by linarith)
  have h5 : CP * E * N ≤ CP * E * (Ω₁ * N) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hN hΩ1) hCPE
  have h6 : 0 ≤ CP * E * T := mul_nonneg hCPE hT
  have h7 : 0 ≤ CS * E * T := mul_nonneg hCSE hT
  nlinarith

theorem exp_split {s γ t : ℝ} :
    Real.exp (-(Real.pi ^ 2 / 8) * (γ - s)) * Real.exp (-(Real.pi ^ 2 / 8) * (t - γ)) =
      Real.exp (-(Real.pi ^ 2 / 8) * (t - s)) := by
  rw [← Real.exp_add]
  congr 1
  ring

theorem exp_neg_mul_le {c x y : ℝ} (hc : 0 ≤ c) (h : y ≤ x) :
    Real.exp (-c * x) ≤ Real.exp (-c * y) :=
  Real.exp_le_exp.2 (by nlinarith)

theorem le_const_mul {X A C E R : ℝ} (hX : X ≤ A * E * R) (hAC : A ≤ C) (hE : 0 ≤ E)
    (hR : 0 ≤ R) : X ≤ C * E * R :=
  hX.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAC hE) hR)

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # The slow adjoint test, conserved pairing and regularity

The slow test `q` of the word fibre facts is the adjoint curve from `1` at `b`, `q(r) = conj u(-r)`
for the reversed curve `u` from `1` (`b1wSlowTest_full`). With `I_r = ∫_r^b λ`:

* the pairing with the forward slow mode is conserved: `⟨1 + r(r), q(r)⟩ = e^{I_r}`
  (`rowCurve_pair`);
* `‖q(r)‖ ≤ (1 + rowConst ρ) |e^{I_r}|` (the actual row, `actualRow_l2`, no `P_e`);
* `q(r)` has an `H^s` representative of norm `≤ C P_e^Q |e^{I_r}|` (conditional on the cell-equation
  regularity): within a unit time of `b` by the growth (G) from the constant `1`, before it by the
  smoothing (S) from the `L²` bound one unit later, with `|e^{I_{r+1}}| ≤ e^{π²/4}|e^{I_r}|`. -/

section
variable {K : ScalarConstants}

/-- **The slow adjoint test of the word fibre facts: conserved pairing, `L²` and `H^s` bounds** (the
`H^s` bound conditional on the cell-equation regularity). -/
theorem b1wSlowTest_full (hR : CellDriftRegularityStatement) (s : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (J : ℕ → ℝ) (hJ : ∀ l, 0 ≤ J l) :
    ∃ (C : ℝ) (Q : ℕ), 0 < C ∧
    ∀ (η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (ξ : Fin 2 → ℂ)
      (H : TransverseLocalHyp K η G v ξ) {t₀ S : ℝ} (data : FibreScalarData K η G v t₀ S),
      0 < η → fibreNorm ξ ≤ ρ → (∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
      (∀ (l : ℕ) t z, ‖iteratedFDeriv ℝ l (fun z' => Real.sqrt η • v t z') z‖ ≤ J l) →
    ∀ (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) {a b : ℝ}, a ≤ b →
    ∃ (q : ℝ → ComplexCellL2) (qs : ℝ → TorusHk 1 ℂ),
      CellWeakHilbertCurve a b q qs (fun t =>
        -cellDualDerivative (cellAdjointCoefficients
          ⟨fun t _ => G t, v, fun k => (Real.sqrt η : ℂ) * ξ k, 0⟩) H.hG V (cellDrift_neg H.hv).1
          (cellDrift_neg_bound hb) t (qs t) 0 0) ∧
      q b = cellConstantCLM 1 ∧
      ∀ r ∈ Icc a b,
        cellComplexPair (cellRawTrace (fibreSeriesJet data.r ξ) r + cellConstantCLM 1) (q r) =
          Complex.exp (∫ τ in r..b, fibreSeriesC data.lam ξ τ) ∧
        ‖q r‖ ≤ (1 + rowConst K (4 * (ρ + K.Cw)) ρ * ρ) *
          ‖Complex.exp (∫ τ in r..b, fibreSeriesC data.lam ξ τ)‖ ∧
        ∃ w : TorusHk s ℂ, torusHkValueCLM w = q r ∧
          ‖w‖ ≤ C * peFactor η ^ Q * ‖Complex.exp (∫ τ in r..b, fibreSeriesC data.lam ξ τ)‖ := by
  obtain ⟨C₀, Q, hC₀, hreg⟩ := hR s ρ hρ
  set B := ∑ l ∈ Finset.range (s + 2), J l with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun l _ => hJ l
  set E := Real.exp (Real.pi ^ 2 / 4) with hE
  have hE0 : 0 < E := Real.exp_pos _
  set M := rowConst K (4 * (ρ + K.Cw)) ρ with hM
  set W1 := ‖torusHigherConstant s (1 : ℂ)‖ with hW1
  set K1 := C₀ * (1 + B) ^ Q * E with hK1
  have hK10 : 0 ≤ K1 := by positivity
  have hW10 : 0 ≤ W1 := norm_nonneg _
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  set Ctot := K1 * (1 + W1 + (1 + |M| * ρ) * E) + 1 with hCtot
  have hCtot0 : 0 < Ctot := by
    have : 0 ≤ K1 * (1 + W1 + (1 + |M| * ρ) * E) := by positivity
    linarith
  refine ⟨Ctot, Q, hCtot0, ?_⟩
  intro η G v ξ H t₀ S data hη hξρ hvs hvj V hb a b hab
  have hb' : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2 := rev_bound hb
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have hP : 0 < peFactor η := by unfold peFactor; positivity
  have hCw := H.hCw
  have hCg := H.hCg
  have hM0 : 0 ≤ M := by rw [hM]; unfold rowConst; positivity
  set cj := cellFiberCLM Complex.conjCLE.toContinuousLinearMap with hcj
  obtain ⟨u, slice, hu, hu0⟩ := revCurve_exists H V hb' (a := -b) (b := -a) (by linarith)
    (cellConstantCLM 1)
  refine ⟨fun r => cj (u (-r)), fun r => cellH1Conj (slice (-r)),
    CellWeakHilbertCurve.reflected_adjoint (fun t _ => G t) H.hG H.hv V hb _ hu, ?_, ?_⟩
  · simp only [hcj, hu0, cellFiberConj_constant, star_one]
  intro r hr
  set I := ∫ τ in r..b, fibreSeriesC data.lam ξ τ with hI
  have hρ' : 0 ≤ ρ := hρ
  -- the conserved pairing
  have hpair := rowCurve_pair H data V hb' hu hu0 r hr
  -- the `L²` bound
  have hL2 : ‖u (-r)‖ ≤ (1 + M * ρ) * ‖Complex.exp I‖ := by
    have hrow := actualRow_l2 H data hξρ V hb' u slice hu hu0 r hr
    rw [cellScalarCLM_smul] at hrow
    have h1 : ‖Complex.exp (-I) • u (-r)‖ ≤ 1 + M * ρ := by
      calc ‖Complex.exp (-I) • u (-r)‖
          ≤ ‖Complex.exp (-I) • u (-r) - cellConstantCLM 1‖ + ‖cellConstantCLM (1 : ℂ)‖ :=
            norm_le_norm_sub_add _ _
        _ ≤ M * fibreNorm ξ + 1 := by
            rw [cellConstantCLM_norm, norm_one]
            exact add_le_add hrow le_rfl
        _ ≤ 1 + M * ρ := by
            have := mul_le_mul_of_nonneg_left hξρ hM0
            linarith
    have hu' : u (-r) = Complex.exp I • (Complex.exp (-I) • u (-r)) := by
      rw [smul_smul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_smul]
    rw [hu', norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  refine ⟨by simpa only [hcj] using hpair, by rw [cellFiberConj_norm]; exact hL2, ?_⟩
  -- the `H^s` bound, through the cell-equation regularity on the reversed curve
  set L := B / Real.sqrt η with hL
  have hL0 : 0 ≤ L := div_nonneg hB0 hs.le
  have hLP : (1 + L) ^ Q ≤ (1 + B) ^ Q * peFactor η ^ Q := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (one_add_div_sqrt_le hη hB0) Q
  have hjet : ∀ (l : ℕ) τ, l ≤ s + 1 → ∀ x,
      ‖iteratedFDeriv ℝ l (fun x => -v (-τ) x) x‖ ≤ L := by
    intro l τ hl x
    refine (revDrift_jet_le hη hvs hvj l τ x).trans ?_
    rw [hL]
    refine div_le_div_of_nonneg_right ?_ hs.le
    exact Finset.single_le_sum (fun l _ => hJ l) (Finset.mem_range.2 (by omega))
  set θ' : Vec 2 := fun k => -(Real.sqrt η * (ξ k).re) with hθ'
  have hθρ : Real.sqrt (vecDot θ' θ') ≤ ρ := by
    refine Real.sqrt_le_iff.mpr ⟨hρ, ?_⟩
    refine le_trans ?_ (pow_le_pow_left₀ (fibreNorm_nonneg ξ) hξρ 2)
    refine le_trans (le_of_eq ?_) (shift_sq_le H)
    simp only [vecDot, hθ', Fin.sum_univ_two]
    ring
  have hGr := cellMetric_timeReverse H.hG
  have hvr := cellDrift_timeReverse H.hv
  have hu' : ∀ a' b', -b ≤ a' → b' ≤ -a → CellWeakHilbertCurve a' b' u slice (fun τ =>
      cellDualDerivative ⟨fun s _ => G (-s), fun s x => -v (-s) x, fun k => (θ' k : ℂ), 0⟩
        hGr V hvr.1 hb' τ (slice τ) 0 0) := by
    intro a' b' ha' hb''
    have h := CellWeakHilbertCurve.mono hu (Icc_subset_Icc ha' hb'')
    refine CellWeakHilbertCurve.dual_congr h (Filter.Eventually.of_forall fun τ => ?_)
    exact cellDualDerivative_congr_coeff (revCoefficients_real H) _ _ V _ _ _ _ τ _ 0 0
  have hsmooth : ∀ τ, ContDiff ℝ (⊤ : ℕ∞) (fun x => -v (-τ) x) := fun τ => (hvs (-τ)).neg
  -- the phase over a unit time
  have hphase : ∀ r' ∈ Icc a b, r' ≤ r + 1 → r ≤ r' →
      ‖Complex.exp (∫ τ in r'..b, fibreSeriesC data.lam ξ τ)‖ ≤ E * ‖Complex.exp I‖ := by
    intro r' hr' h1 h2
    obtain ⟨hγ, -⟩ := phase_unit_bounds H data hξρ (s := r) (t := r') h2 h1
    have hint : ∀ c d, c ≤ d → IntervalIntegrable (fibreSeriesC data.lam ξ) volume c d :=
      fun c d hcd => (intervalIntegrable_iff_integrableOn_Ioc_of_le hcd).mpr
        (symbol_integrableOn data H.hη0 H.hη H.hCg H.hCw H.hG H.hv H.hw H.hξ c d)
    have hsplit : I = (∫ τ in r..r', fibreSeriesC data.lam ξ τ) +
        ∫ τ in r'..b, fibreSeriesC data.lam ξ τ := by
      rw [hI, intervalIntegral.integral_add_adjacent_intervals (hint r r' h2)
        (hint r' b hr'.2)]
    have he : Complex.exp (∫ τ in r'..b, fibreSeriesC data.lam ξ τ) =
        Complex.exp (-∫ τ in r..r', fibreSeriesC data.lam ξ τ) * Complex.exp I := by
      rw [← Complex.exp_add, hsplit]
      ring_nf
    rw [he, norm_mul]
    exact mul_le_mul_of_nonneg_right hγ (norm_nonneg _)
  have hCpos : 0 ≤ C₀ * (1 + B) ^ Q * E := by positivity
  by_cases h1 : b - r ≤ 1
  · -- within a unit time of `b`: the growth (G) from the constant `1`
    obtain ⟨w, hwv, hwn⟩ := (hreg (-b) (-r) L (fun s => G (-s)) hGr hvr V hb' θ'
      (by linarith [hr.2]) hL0 hθρ (fun τ _ => hsmooth τ) (fun l τ hl _ x => hjet l τ hl x) u
      slice (hu' (-b) (-r) le_rfl (by linarith [hr.1]))).1 (torusHigherConstant s 1)
      (by rw [torusHigherConstant_value, hu0]) (-r) ⟨by linarith [hr.2], le_rfl⟩
      (by linarith)
    refine ⟨torusHkConj w, by rw [torusHkConj_value, hwv], ?_⟩
    rw [torusHkConj_norm]
    have hlow : 1 ≤ E * ‖Complex.exp I‖ := by
      have h := hphase b ⟨hab, le_rfl⟩ (by linarith) hr.2
      simp only [intervalIntegral.integral_same, Complex.exp_zero, norm_one] at h
      exact h
    have hK1W : K1 * W1 ≤ Ctot := by
      have : K1 * W1 ≤ K1 * (1 + W1 + (1 + |M| * ρ) * E) :=
        mul_le_mul_of_nonneg_left (by have : 0 ≤ (1 + |M| * ρ) * E := by positivity
                                      linarith) hK10
      linarith
    have hX : 0 ≤ peFactor η ^ Q * ‖Complex.exp I‖ := by positivity
    calc ‖w‖ ≤ C₀ * (1 + L) ^ Q * W1 := hwn
      _ ≤ C₀ * ((1 + B) ^ Q * peFactor η ^ Q) * W1 := by gcongr
      _ ≤ C₀ * ((1 + B) ^ Q * peFactor η ^ Q) * W1 * (E * ‖Complex.exp I‖) :=
          le_mul_of_one_le_right (by positivity) hlow
      _ = (K1 * W1) * (peFactor η ^ Q * ‖Complex.exp I‖) := by rw [hK1]; ring
      _ ≤ Ctot * (peFactor η ^ Q * ‖Complex.exp I‖) := mul_le_mul_of_nonneg_right hK1W hX
      _ = Ctot * peFactor η ^ Q * ‖Complex.exp I‖ := by ring
  · -- before: the smoothing (S) from the `L²` bound one unit later
    push Not at h1
    have hr1 : r + 1 ∈ Icc a b := ⟨by linarith [hr.1], by linarith⟩
    obtain ⟨w, hwv, hwn⟩ := (hreg (-r - 1) (-r) L (fun s => G (-s)) hGr hvr V hb' θ'
      (by linarith) hL0 hθρ (fun τ _ => hsmooth τ) (fun l τ hl _ x => hjet l τ hl x) u slice
      (hu' (-r - 1) (-r) (by linarith) (by linarith [hr.1]))).2 (-r) ⟨by linarith, le_rfl⟩
      (by linarith) (by linarith)
    refine ⟨torusHkConj w, by rw [torusHkConj_value, hwv], ?_⟩
    rw [torusHkConj_norm]
    have hrow1 := actualRow_l2 H data hξρ V hb' u slice hu hu0 (r + 1) hr1
    have hneg : -(r + 1) = -r - 1 := by ring
    have hL2' : ‖u (-r - 1)‖ ≤ (1 + M * ρ) * (E * ‖Complex.exp I‖) := by
      rw [cellScalarCLM_smul] at hrow1
      set I' := ∫ τ in (r + 1)..b, fibreSeriesC data.lam ξ τ with hI'
      have h1' : ‖Complex.exp (-I') • u (-(r + 1))‖ ≤ 1 + M * ρ := by
        calc ‖Complex.exp (-I') • u (-(r + 1))‖
            ≤ ‖Complex.exp (-I') • u (-(r + 1)) - cellConstantCLM 1‖ +
                ‖cellConstantCLM (1 : ℂ)‖ := norm_le_norm_sub_add _ _
          _ ≤ M * fibreNorm ξ + 1 := by
              rw [cellConstantCLM_norm, norm_one]
              exact add_le_add hrow1 le_rfl
          _ ≤ 1 + M * ρ := by
              have := mul_le_mul_of_nonneg_left hξρ hM0
              linarith
      have hu'' : ‖u (-(r + 1))‖ =
          ‖Complex.exp I'‖ * ‖Complex.exp (-I') • u (-(r + 1))‖ := by
        rw [← norm_smul, smul_smul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero,
          one_smul]
      have hph := hphase (r + 1) hr1 le_rfl (by linarith)
      rw [← hneg, hu'', mul_comm]
      exact mul_le_mul h1' hph (norm_nonneg _) (by have := mul_nonneg hM0 hρ; linarith)
    have hMρ : 1 + M * ρ ≤ 1 + |M| * ρ := by
      have := mul_le_mul_of_nonneg_right (le_abs_self M) hρ
      linarith
    have hK1M : K1 * (1 + M * ρ) ≤ Ctot := by
      have h1' : K1 * (1 + M * ρ) ≤ K1 * ((1 + |M| * ρ) * E) := by
        refine mul_le_mul_of_nonneg_left ?_ hK10
        have h0 : 0 ≤ 1 + |M| * ρ := by positivity
        exact hMρ.trans (le_mul_of_one_le_right h0 hE1)
      have h2' : K1 * ((1 + |M| * ρ) * E) ≤ K1 * (1 + W1 + (1 + |M| * ρ) * E) :=
        mul_le_mul_of_nonneg_left (by linarith) hK10
      linarith
    have hX : 0 ≤ peFactor η ^ Q * ‖Complex.exp I‖ := by positivity
    calc ‖w‖ ≤ C₀ * (1 + L) ^ Q * ‖u (-r - 1)‖ := hwn
      _ ≤ C₀ * ((1 + B) ^ Q * peFactor η ^ Q) * ((1 + M * ρ) * (E * ‖Complex.exp I‖)) := by
          gcongr
      _ = (K1 * (1 + M * ρ)) * (peFactor η ^ Q * ‖Complex.exp I‖) := by rw [hK1]; ring
      _ ≤ Ctot * (peFactor η ^ Q * ‖Complex.exp I‖) := mul_le_mul_of_nonneg_right hK1M hX
      _ = Ctot * peFactor η ^ Q * ‖Complex.exp I‖ := by ring
end

/-! # The sharp slow test: the crude `H^s` bound for a given reversed curve

`b1wSlowTest_full` for a GIVEN reversed curve `u` from `1` at `-b` (the original constructs `u`). -/

section
variable {K : ScalarConstants}

/-- **Crude `H^s` bound of a given reversed curve from `1`** (copy of `b1wSlowTest_full`
without the construction). -/
theorem sharpSlow_crude_curve (hR : CellDriftRegularityStatement) (s : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (J : ℕ → ℝ) (hJ : ∀ l, 0 ≤ J l) :
    ∃ (C : ℝ) (Q : ℕ), 0 < C ∧
    ∀ (η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (ξ : Fin 2 → ℂ)
      (H : TransverseLocalHyp K η G v ξ) {t₀ S : ℝ} (data : FibreScalarData K η G v t₀ S),
      0 < η → fibreNorm ξ ≤ ρ → (∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
      (∀ (l : ℕ) t z, ‖iteratedFDeriv ℝ l (fun z' => Real.sqrt η • v t z') z‖ ≤ J l) →
    ∀ (V : ℝ) (hb' : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2) {a b : ℝ}, a ≤ b →
    ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ), IsRevCurve H V hb' (-b) (-a) u slice →
      u (-b) = cellConstantCLM 1 →
    ∀ r ∈ Icc a b, ∃ w : TorusHk s ℂ,
      torusHkValueCLM w = cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u (-r)) ∧
        ‖w‖ ≤ C * peFactor η ^ Q * ‖Complex.exp (∫ τ in r..b, fibreSeriesC data.lam ξ τ)‖ := by
  obtain ⟨C₀, Q, hC₀, hreg⟩ := hR s ρ hρ
  set B := ∑ l ∈ Finset.range (s + 2), J l with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun l _ => hJ l
  set E := Real.exp (Real.pi ^ 2 / 4) with hE
  have hE0 : 0 < E := Real.exp_pos _
  set M := rowConst K (4 * (ρ + K.Cw)) ρ with hM
  set W1 := ‖torusHigherConstant s (1 : ℂ)‖ with hW1
  set K1 := C₀ * (1 + B) ^ Q * E with hK1
  have hK10 : 0 ≤ K1 := by positivity
  have hW10 : 0 ≤ W1 := norm_nonneg _
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  set Ctot := K1 * (1 + W1 + (1 + |M| * ρ) * E) + 1 with hCtot
  have hCtot0 : 0 < Ctot := by
    have : 0 ≤ K1 * (1 + W1 + (1 + |M| * ρ) * E) := by positivity
    linarith
  refine ⟨Ctot, Q, hCtot0, ?_⟩
  intro η G v ξ H t₀ S data hη hξρ hvs hvj V hb' a b hab u slice hu hu0 r hr
  have hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2 := fun t x => by simpa only [Pi.neg_apply, neg_sq, neg_neg] using hb' (-t) x
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have hP : 0 < peFactor η := by unfold peFactor; positivity
  have hCw := H.hCw
  have hCg := H.hCg
  have hM0 : 0 ≤ M := by rw [hM]; unfold rowConst; positivity
  set cj := cellFiberCLM Complex.conjCLE.toContinuousLinearMap with hcj
  set cj := cellFiberCLM Complex.conjCLE.toContinuousLinearMap with hcj
  set I := ∫ τ in r..b, fibreSeriesC data.lam ξ τ with hI
  have hρ' : 0 ≤ ρ := hρ
  -- the conserved pairing
  have hpair := rowCurve_pair H data V hb' hu hu0 r hr
  -- the `L²` bound
  have hL2 : ‖u (-r)‖ ≤ (1 + M * ρ) * ‖Complex.exp I‖ := by
    have hrow := actualRow_l2 H data hξρ V hb' u slice hu hu0 r hr
    rw [cellScalarCLM_smul] at hrow
    have h1 : ‖Complex.exp (-I) • u (-r)‖ ≤ 1 + M * ρ := by
      calc ‖Complex.exp (-I) • u (-r)‖
          ≤ ‖Complex.exp (-I) • u (-r) - cellConstantCLM 1‖ + ‖cellConstantCLM (1 : ℂ)‖ :=
            norm_le_norm_sub_add _ _
        _ ≤ M * fibreNorm ξ + 1 := by
            rw [cellConstantCLM_norm, norm_one]
            exact add_le_add hrow le_rfl
        _ ≤ 1 + M * ρ := by
            have := mul_le_mul_of_nonneg_left hξρ hM0
            linarith
    have hu' : u (-r) = Complex.exp I • (Complex.exp (-I) • u (-r)) := by
      rw [smul_smul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_smul]
    rw [hu', norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  -- the `H^s` bound, through the crude bound on the reversed curve
  set L := B / Real.sqrt η with hL
  have hL0 : 0 ≤ L := div_nonneg hB0 hs.le
  have hLP : (1 + L) ^ Q ≤ (1 + B) ^ Q * peFactor η ^ Q := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (one_add_div_sqrt_le hη hB0) Q
  have hjet : ∀ (l : ℕ) τ, l ≤ s + 1 → ∀ x,
      ‖iteratedFDeriv ℝ l (fun x => -v (-τ) x) x‖ ≤ L := by
    intro l τ hl x
    refine (revDrift_jet_le hη hvs hvj l τ x).trans ?_
    rw [hL]
    refine div_le_div_of_nonneg_right ?_ hs.le
    exact Finset.single_le_sum (fun l _ => hJ l) (Finset.mem_range.2 (by omega))
  set θ' : Vec 2 := fun k => -(Real.sqrt η * (ξ k).re) with hθ'
  have hθρ : Real.sqrt (vecDot θ' θ') ≤ ρ := by
    refine Real.sqrt_le_iff.mpr ⟨hρ, ?_⟩
    refine le_trans ?_ (pow_le_pow_left₀ (fibreNorm_nonneg ξ) hξρ 2)
    refine le_trans (le_of_eq ?_) (shift_sq_le H)
    simp only [vecDot, hθ', Fin.sum_univ_two]
    ring
  have hGr := cellMetric_timeReverse H.hG
  have hvr := cellDrift_timeReverse H.hv
  have hu' : ∀ a' b', -b ≤ a' → b' ≤ -a → CellWeakHilbertCurve a' b' u slice (fun τ =>
      cellDualDerivative ⟨fun s _ => G (-s), fun s x => -v (-s) x, fun k => (θ' k : ℂ), 0⟩
        hGr V hvr.1 hb' τ (slice τ) 0 0) := by
    intro a' b' ha' hb''
    have h := CellWeakHilbertCurve.mono hu (Icc_subset_Icc ha' hb'')
    refine CellWeakHilbertCurve.dual_congr h (Filter.Eventually.of_forall fun τ => ?_)
    exact cellDualDerivative_congr_coeff (revCoefficients_real H) _ _ V _ _ _ _ τ _ 0 0
  have hsmooth : ∀ τ, ContDiff ℝ (⊤ : ℕ∞) (fun x => -v (-τ) x) := fun τ => (hvs (-τ)).neg
  -- the phase over a unit time
  have hphase : ∀ r' ∈ Icc a b, r' ≤ r + 1 → r ≤ r' →
      ‖Complex.exp (∫ τ in r'..b, fibreSeriesC data.lam ξ τ)‖ ≤ E * ‖Complex.exp I‖ := by
    intro r' hr' h1 h2
    obtain ⟨hγ, -⟩ := phase_unit_bounds H data hξρ (s := r) (t := r') h2 h1
    have hint : ∀ c d, c ≤ d → IntervalIntegrable (fibreSeriesC data.lam ξ) volume c d :=
      fun c d hcd => (intervalIntegrable_iff_integrableOn_Ioc_of_le hcd).mpr
        (symbol_integrableOn data H.hη0 H.hη H.hCg H.hCw H.hG H.hv H.hw H.hξ c d)
    have hsplit : I = (∫ τ in r..r', fibreSeriesC data.lam ξ τ) +
        ∫ τ in r'..b, fibreSeriesC data.lam ξ τ := by
      rw [hI, intervalIntegral.integral_add_adjacent_intervals (hint r r' h2)
        (hint r' b hr'.2)]
    have he : Complex.exp (∫ τ in r'..b, fibreSeriesC data.lam ξ τ) =
        Complex.exp (-∫ τ in r..r', fibreSeriesC data.lam ξ τ) * Complex.exp I := by
      rw [← Complex.exp_add, hsplit]
      ring_nf
    rw [he, norm_mul]
    exact mul_le_mul_of_nonneg_right hγ (norm_nonneg _)
  have hCpos : 0 ≤ C₀ * (1 + B) ^ Q * E := by positivity
  by_cases h1 : b - r ≤ 1
  · -- within a unit time of `b`: the growth (G) from the constant `1`
    obtain ⟨w, hwv, hwn⟩ := (hreg (-b) (-r) L (fun s => G (-s)) hGr hvr V hb' θ'
      (by linarith [hr.2]) hL0 hθρ (fun τ _ => hsmooth τ) (fun l τ hl _ x => hjet l τ hl x) u
      slice (hu' (-b) (-r) le_rfl (by linarith [hr.1]))).1 (torusHigherConstant s 1)
      (by rw [torusHigherConstant_value, hu0]) (-r) ⟨by linarith [hr.2], le_rfl⟩
      (by linarith)
    refine ⟨torusHkConj w, by rw [torusHkConj_value, hwv], ?_⟩
    rw [torusHkConj_norm]
    have hlow : 1 ≤ E * ‖Complex.exp I‖ := by
      have h := hphase b ⟨hab, le_rfl⟩ (by linarith) hr.2
      simp only [intervalIntegral.integral_same, Complex.exp_zero, norm_one] at h
      exact h
    have hK1W : K1 * W1 ≤ Ctot := by
      have : K1 * W1 ≤ K1 * (1 + W1 + (1 + |M| * ρ) * E) :=
        mul_le_mul_of_nonneg_left (by have : 0 ≤ (1 + |M| * ρ) * E := by positivity
                                      linarith) hK10
      linarith
    have hX : 0 ≤ peFactor η ^ Q * ‖Complex.exp I‖ := by positivity
    calc ‖w‖ ≤ C₀ * (1 + L) ^ Q * W1 := hwn
      _ ≤ C₀ * ((1 + B) ^ Q * peFactor η ^ Q) * W1 := by gcongr
      _ ≤ C₀ * ((1 + B) ^ Q * peFactor η ^ Q) * W1 * (E * ‖Complex.exp I‖) :=
          le_mul_of_one_le_right (by positivity) hlow
      _ = (K1 * W1) * (peFactor η ^ Q * ‖Complex.exp I‖) := by rw [hK1]; ring
      _ ≤ Ctot * (peFactor η ^ Q * ‖Complex.exp I‖) := mul_le_mul_of_nonneg_right hK1W hX
      _ = Ctot * peFactor η ^ Q * ‖Complex.exp I‖ := by ring
  · -- before: the smoothing (S) from the `L²` bound one unit later
    push Not at h1
    have hr1 : r + 1 ∈ Icc a b := ⟨by linarith [hr.1], by linarith⟩
    obtain ⟨w, hwv, hwn⟩ := (hreg (-r - 1) (-r) L (fun s => G (-s)) hGr hvr V hb' θ'
      (by linarith) hL0 hθρ (fun τ _ => hsmooth τ) (fun l τ hl _ x => hjet l τ hl x) u slice
      (hu' (-r - 1) (-r) (by linarith) (by linarith [hr.1]))).2 (-r) ⟨by linarith, le_rfl⟩
      (by linarith) (by linarith)
    refine ⟨torusHkConj w, by rw [torusHkConj_value, hwv], ?_⟩
    rw [torusHkConj_norm]
    have hrow1 := actualRow_l2 H data hξρ V hb' u slice hu hu0 (r + 1) hr1
    have hneg : -(r + 1) = -r - 1 := by ring
    have hL2' : ‖u (-r - 1)‖ ≤ (1 + M * ρ) * (E * ‖Complex.exp I‖) := by
      rw [cellScalarCLM_smul] at hrow1
      set I' := ∫ τ in (r + 1)..b, fibreSeriesC data.lam ξ τ with hI'
      have h1' : ‖Complex.exp (-I') • u (-(r + 1))‖ ≤ 1 + M * ρ := by
        calc ‖Complex.exp (-I') • u (-(r + 1))‖
            ≤ ‖Complex.exp (-I') • u (-(r + 1)) - cellConstantCLM 1‖ +
                ‖cellConstantCLM (1 : ℂ)‖ := norm_le_norm_sub_add _ _
          _ ≤ M * fibreNorm ξ + 1 := by
              rw [cellConstantCLM_norm, norm_one]
              exact add_le_add hrow1 le_rfl
          _ ≤ 1 + M * ρ := by
              have := mul_le_mul_of_nonneg_left hξρ hM0
              linarith
      have hu'' : ‖u (-(r + 1))‖ =
          ‖Complex.exp I'‖ * ‖Complex.exp (-I') • u (-(r + 1))‖ := by
        rw [← norm_smul, smul_smul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero,
          one_smul]
      have hph := hphase (r + 1) hr1 le_rfl (by linarith)
      rw [← hneg, hu'', mul_comm]
      exact mul_le_mul h1' hph (norm_nonneg _) (by have := mul_nonneg hM0 hρ; linarith)
    have hMρ : 1 + M * ρ ≤ 1 + |M| * ρ := by
      have := mul_le_mul_of_nonneg_right (le_abs_self M) hρ
      linarith
    have hK1M : K1 * (1 + M * ρ) ≤ Ctot := by
      have h1' : K1 * (1 + M * ρ) ≤ K1 * ((1 + |M| * ρ) * E) := by
        refine mul_le_mul_of_nonneg_left ?_ hK10
        have h0 : 0 ≤ 1 + |M| * ρ := by positivity
        exact hMρ.trans (le_mul_of_one_le_right h0 hE1)
      have h2' : K1 * ((1 + |M| * ρ) * E) ≤ K1 * (1 + W1 + (1 + |M| * ρ) * E) :=
        mul_le_mul_of_nonneg_left (by linarith) hK10
      linarith
    have hX : 0 ≤ peFactor η ^ Q * ‖Complex.exp I‖ := by positivity
    calc ‖w‖ ≤ C₀ * (1 + L) ^ Q * ‖u (-r - 1)‖ := hwn
      _ ≤ C₀ * ((1 + B) ^ Q * peFactor η ^ Q) * ((1 + M * ρ) * (E * ‖Complex.exp I‖)) := by
          gcongr
      _ = (K1 * (1 + M * ρ)) * (peFactor η ^ Q * ‖Complex.exp I‖) := by rw [hK1]; ring
      _ ≤ Ctot * (peFactor η ^ Q * ‖Complex.exp I‖) := mul_le_mul_of_nonneg_right hK1M hX
      _ = Ctot * peFactor η ^ Q * ‖Complex.exp I‖ := by ring
end

end AVRegularity.CycleWords.Assembly
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleWords.Assembly

/-! # The sharp pass (weighted norm): the adjoint fast curves with weighted bounds

The adjoint curve from an admissible test `ψ` at `T` is `Ψ(r) = conj u(−r)`, for the reversed curve
`u` from `conj ψ` (as in `b1w_crude_adjoint`). The weighted sharp decay bound
(`WeightedSharpDecayStatement`, a hypothesis here) applies to `u`. Conjugation preserves the `H^j`
norms (`torusHkConj_norm`) and commutes with the transverse projections
(`cellTransverseProjection_conjugate`). So a weighted splitting of `ψ` at `T` gives one of `Ψ(r)` at
every `r ∈ [a, T]`, for every pair of levels `Λ₂ P_e^{Q′} ≤ Λ₁`, along ONE curve
(`b1w_weighted_adjoint`). -/

theorem torusHkConj_add {n : ℕ} (U V : TorusHk n ℂ) :
    torusHkValueCLM (torusHkConj U + torusHkConj V) =
      cellFiberCLM Complex.conjCLE.toContinuousLinearMap (torusHkValueCLM (U + V)) := by
  rw [map_add, map_add, torusHkConj_value, torusHkConj_value, map_add]

theorem torusHkConj_transverse {n : ℕ} (e : Fin 2) (U : TorusHk n ℂ)
    (h : cellTransverseProjection e (torusHkValueCLM U) = torusHkValueCLM U) :
    cellTransverseProjection e (torusHkValueCLM (torusHkConj U)) =
      torusHkValueCLM (torusHkConj U) := by
  rw [torusHkConj_value, cellTransverseProjection_conjugate, h]

variable {K : ScalarConstants}

/-- **The adjoint fast curves with weighted bounds** (conditional on the weighted sharp decay). -/
theorem b1w_weighted_adjoint (hR : CellDriftRegularityStatement)
    (hW : WeightedSharpDecayStatement) (K : ScalarConstants) (s : ℕ → ℕ) (k : ℕ) {ρ : ℝ}
    (hρ : ρ < K.ξ0) (hρlo : ρ ≤ 2 * K.ξlo) (hρ0 : 0 ≤ ρ) :
    ∃ (C Cb cb : ℝ) (Q Q' : ℕ), 1 ≤ C ∧ 0 < cb ∧
    ∀ (η t₀ S ϖ : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (g : ℝ)
      (reg : BlockRegions) (pkg : CoreScalarPackage K η G v t₀ S ϖ reg),
      0 < η → (∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
      (∀ (i : ℕ) t z, ‖iteratedFDeriv ℝ i (fun z' => Real.sqrt η • v t z') z‖ ≤ K.Cvj i) →
      0 ≤ g → g ≤ K.g0 → IsMetricNearIdentity (fun t _ => G t) g →
    ∀ (ξ : Fin 2 → ℂ) (H : TransverseLocalHyp K η G v ξ), fibreNorm ξ ≤ ρ →
    ∀ (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) {a T : ℝ}, t₀ ≤ a → a ≤ T →
      T ≤ t₀ + S →
    ∀ ψ : ComplexCellL2, b1wAdm s (cellRawTrace (fibreSeriesJet pkg.actual.r ξ)) k T ψ →
      ∃ (Ψv : ℝ → ComplexCellL2) (Ψs : ℝ → TorusHk 1 ℂ),
        CellWeakHilbertCurve a T Ψv Ψs (fun r =>
          -cellDualDerivative (cellAdjointCoefficients
            ⟨fun t _ => G t, v, fun k => (Real.sqrt η : ℂ) * ξ k, 0⟩) H.hG V
            (cellDrift_neg H.hv).1 (cellDrift_neg_bound hb) r (Ψs r) 0 0) ∧
        Ψv T = ψ ∧
        (∀ r ∈ Icc a T, b1wAdm s (cellRawTrace (fibreSeriesJet pkg.actual.r ξ)) k r (Ψv r)) ∧
        ∀ UT UN : TorusHk (s k) ℂ, torusHkValueCLM (UT + UN) = ψ →
          cellTransverseProjection (activityOrient reg v t₀ T) (torusHkValueCLM UT) =
            torusHkValueCLM UT →
        ∀ Λ₁ Λ₂ : ℝ, 1 ≤ Λ₂ → Λ₂ * peFactor η ^ Q' ≤ Λ₁ →
          Cb * Λ₁ * (1 + (reg.joins : ℝ)) * peFactor η ^ Q * Real.exp (-cb * reg.buffer) ≤ 1 →
        ∀ r ∈ Icc a T, ∃ VT VN : TorusHk (s k) ℂ, torusHkValueCLM (VT + VN) = Ψv r ∧
          cellTransverseProjection (activityOrient reg v t₀ r) (torusHkValueCLM VT) =
            torusHkValueCLM VT ∧
          ‖VT‖ + activityWeight v t₀ Λ₂ (3 * Real.pi ^ 2 / 8) r * ‖VN‖ ≤
            C * Real.exp (-(Real.pi ^ 2 / 8) * (T - r)) *
              (‖UT‖ + activityWeight v t₀ Λ₁ (3 * Real.pi ^ 2 / 8) T * ‖UN‖) := by
  obtain ⟨C, Cb, cb, Q, Q', hC, hcb, hdec⟩ := hW K (s k) ρ hρ hρlo
  obtain ⟨Cc, Qc, hCc, hcrude⟩ := revCurve_crude_decay (K := K) hR (s k) hρ0
    (fun l => |K.Cvj l|) (fun l => abs_nonneg _)
  refine ⟨C, Cb, cb, Q, Q', hC, hcb, ?_⟩
  intro η t₀ S ϖ G v g reg pkg hη hvs hvj hg0 hg hnear ξ H hξρ V hb a T ht₀a haT hTS ψ hψ
  have hb' : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2 := rev_bound hb
  set cj := cellFiberCLM Complex.conjCLE.toContinuousLinearMap with hcj
  obtain ⟨u, slice, hu, hu0⟩ := revCurve_exists H V hb' (a := -T) (b := -a) (by linarith)
    (cj ψ)
  have hfastT : cellComplexPair (cellRawTrace (fibreSeriesJet pkg.actual.r ξ) T +
      cellConstantCLM 1) (cj (u (-T))) = 0 := by
    rw [hu0, hcj, cellFiberConj_involutive]
    exact hψ.2
  refine ⟨fun r => cj (u (-r)), fun r => cellH1Conj (slice (-r)),
    CellWeakHilbertCurve.reflected_adjoint (fun t _ => G t) H.hG H.hv V hb _ hu, ?_, ?_, ?_⟩
  · simp only [hu0, hcj, cellFiberConj_involutive]
  · intro r hr
    have hur : IsRevCurve H V hb' (-T) (-r) u slice :=
      CellWeakHilbertCurve.mono hu (Icc_subset_Icc le_rfl (by linarith [hr.1]))
    refine ⟨?_, ?_⟩
    · obtain ⟨U, hU⟩ := hψ.1
      obtain ⟨w, hwv, -⟩ := hcrude η G v ξ H pkg.actual hη hξρ hvs
        (fun l t z => (hvj l t z).trans (le_abs_self _)) V hb' hr.2 u slice hur
        hfastT (torusHkConj U) (by rw [torusHkConj_value, hU, hu0])
      exact ⟨torusHkConj w, by rw [torusHkConj_value, hwv]⟩
    · have hp := revCurve_pairing H.hη0 H.hη H.hCg H.hCw H.hG H.hv H.hm H.hw pkg.actual ξ H.hξ V
        hb' hu r hr
      rw [hp, hfastT, mul_zero]
  · intro UT UN hUv hUT Λ₁ Λ₂ hΛ₂ hΛ hreg r hr
    have hur : IsRevCurve H V hb' (-T) (-r) u slice :=
      CellWeakHilbertCurve.mono hu (Icc_subset_Icc le_rfl (by linarith [hr.1]))
    obtain ⟨VT, VN, hVv, hVT, hVn⟩ := hdec η t₀ S ϖ G v g reg pkg hη hvs hvj hg0 hg hnear ξ H
      hξρ Λ₁ Λ₂ hΛ₂ hΛ hreg V hb' (le_trans ht₀a hr.1) hr.2 hTS u slice hur hfastT
      (torusHkConj UT) (torusHkConj UN) (by rw [torusHkConj_add, hUv, hu0])
      (torusHkConj_transverse _ UT hUT)
    refine ⟨torusHkConj VT, torusHkConj VN, ?_, torusHkConj_transverse _ VT hVT, ?_⟩
    · rw [torusHkConj_add, hVv]
    · rw [torusHkConj_norm, torusHkConj_norm]
      rw [torusHkConj_norm, torusHkConj_norm] at hVn
      exact hVn

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords
namespace AVRegularity.CycleWords.Assembly

/-! # The sharp slow test: the mean part and the `L²` bound of `q`

For the slow test `q = conj u(-r)` of a setting: `‖q(r)‖ ≤ (1 + Mρ)|E(r)|` and the mean part
`⟨1, q(r)⟩ = E(r) + O(|ξ|)|E(r)|` (the conserved pairing with `1 + r(r)` and `‖r(r)‖_{L²} ≤ C_g|ξ|`).
Used by both cases of the one-step inequality. -/

variable {K : ScalarConstants} {ρ : ℝ}

/-- `‖q(r)‖ ≤ (1 + Mρ)|E(r)|`. -/
theorem sharpSlow_q_l2 (s : SharpSlowSetting K ρ) {r : ℝ} (hr : r ∈ Icc s.a s.b) :
    ‖s.q r‖ ≤ (1 + rowConst K (4 * (ρ + K.Cw)) ρ * ρ) * ‖s.E r‖ := by
  have hρ : 0 ≤ ρ := (fibreNorm_nonneg s.ξ).trans s.hξρ
  have hM0 : 0 ≤ rowConst K (4 * (ρ + K.Cw)) ρ := by
    have hCw := s.H.hCw
    have hCg := s.H.hCg
    unfold rowConst; positivity
  have hrow := actualRow_l2 s.H s.pkg.actual s.hξρ s.V s.hb' s.u s.slice s.hu s.hu1 r hr
  rw [cellScalarCLM_smul] at hrow
  set I := ∫ τ in r..s.b, fibreSeriesC s.pkg.actual.lam s.ξ τ with hI
  have h1 : ‖Complex.exp (-I) • s.u (-r)‖ ≤ 1 + rowConst K (4 * (ρ + K.Cw)) ρ * ρ := by
    calc ‖Complex.exp (-I) • s.u (-r)‖
        ≤ ‖Complex.exp (-I) • s.u (-r) - cellConstantCLM 1‖ + ‖cellConstantCLM (1 : ℂ)‖ :=
          norm_le_norm_sub_add _ _
      _ ≤ rowConst K (4 * (ρ + K.Cw)) ρ * fibreNorm s.ξ + 1 := by
          rw [cellConstantCLM_norm, norm_one]
          exact add_le_add hrow le_rfl
      _ ≤ 1 + rowConst K (4 * (ρ + K.Cw)) ρ * ρ := by
          have := mul_le_mul_of_nonneg_left s.hξρ hM0
          linarith
  have hu' : s.u (-r) = Complex.exp I • (Complex.exp (-I) • s.u (-r)) := by
    rw [smul_smul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_smul]
  unfold SharpSlowSetting.q SharpSlowSetting.E
  rw [cellFiberConj_norm]
  calc ‖s.u (-r)‖ = ‖Complex.exp I‖ * ‖Complex.exp (-I) • s.u (-r)‖ := by
        rw [← norm_smul, ← hu']
    _ ≤ _ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)

/-- **The mean part of `q`**: `|⟨1, q(r)⟩ - E(r)| ≤ C_g(1 + Mρ)|ξ||E(r)|`. -/
theorem sharpSlow_mean (s : SharpSlowSetting K ρ) {r : ℝ} (hr : r ∈ Icc s.a s.b) :
    ‖cellComplexPair (cellConstantCLM 1) (s.q r) - s.E r‖ ≤
      K.Cg * (1 + rowConst K (4 * (ρ + K.Cw)) ρ * ρ) * fibreNorm s.ξ * ‖s.E r‖ := by
  have hpair := rowCurve_pair s.H s.pkg.actual s.V s.hb' s.hu s.hu1 r hr
  have hE : cellComplexPair (cellRawTrace (fibreSeriesJet s.pkg.actual.r s.ξ) r +
      cellConstantCLM 1) (s.q r) = s.E r := hpair
  rw [cellComplexPair_add_left] at hE
  have heq : cellComplexPair (cellConstantCLM 1) (s.q r) - s.E r =
      -cellComplexPair (cellRawTrace (fibreSeriesJet s.pkg.actual.r s.ξ) r) (s.q r) := by
    rw [← hE]; ring
  rw [heq, norm_neg]
  have h1 := cellComplexPair_norm_le (cellRawTrace (fibreSeriesJet s.pkg.actual.r s.ξ) r)
    (s.q r)
  have h2 := scalarPackageGraphCorrection_norm_le s.pkg.actual s.H.hCg s.ξ s.H.hξ r
  have h3 := sharpSlow_q_l2 s hr
  have hn := fibreNorm_nonneg s.ξ
  calc _ ≤ _ := h1
    _ ≤ (K.Cg * fibreNorm s.ξ) * ((1 + rowConst K (4 * (ρ + K.Cw)) ρ * ρ) * ‖s.E r‖) :=
        mul_le_mul h2 h3 (norm_nonneg _) (by have := s.H.hCg; positivity)
    _ = _ := by ring

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! # The transverse fast part in `H^j`

Let `Ψ` solve the adjoint equation on `[-t, -s]` from a transverse `w₀ ∈ H^j`. With
`X₀ = ⟨1 + r(t), w₀⟩` (bilinear) and the normalized row `ℓ`, `w₀ = X₀ℓ(t) + f₀`, where `f₀` is in
the fast class (`⟨1 + r(t), ℓ(t)⟩ = 1`) and is `O(‖w₀‖_{H^j})` in `H^j`. The adjoint
solution from `X₀ℓ(t)` is `X₀e^{∫_s^t λ}ℓ(s)` (the multiple of the curve from `1`), so the rest
is the solution from `f₀`, which is transverse. Its `H^j` norm at `s` is bounded by (G)
when `t - s ≤ 1`. Otherwise it decays in `L²` at the rate `8π²/9 - |ξ|² ≥ π²/4`
(`revCurve_fast_decay`) up to `s + 1` and is then smoothed by (S). Both give
`Ce^{-π²(t-s)/8}‖w₀‖_{H^j}`. -/

variable {K : ScalarConstants} {η : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {v : ℝ → Vec 2 → Vec 2} {ξ : Fin 2 → ℂ}

/-- `L²` decay at a rate `a ≥ π²/4` in squared form gives decay at `π²/8` in norm. -/
theorem decay_norm_of_sq {a T z d : ℝ} (ha : Real.pi ^ 2 / 4 ≤ a) (hT : 0 ≤ T) (hz : 0 ≤ z)
    (hd : 0 ≤ d) (h : Real.exp (a * T) * z ^ 2 ≤ d ^ 2) :
    z ≤ Real.exp (-(Real.pi ^ 2 / 8) * T) * d := by
  have h1 : z ^ 2 ≤ Real.exp (-(a * T)) * d ^ 2 := by
    have he : Real.exp (-(a * T)) * Real.exp (a * T) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    calc z ^ 2 = Real.exp (-(a * T)) * (Real.exp (a * T) * z ^ 2) := by
          rw [← mul_assoc, he, one_mul]
      _ ≤ Real.exp (-(a * T)) * d ^ 2 := mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
  have h2 : Real.exp (-(a * T)) ≤ Real.exp (-(Real.pi ^ 2 / 8) * T) ^ 2 := by
    rw [sq, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h4 : Real.pi ^ 2 / 4 * T ≤ a * T := mul_le_mul_of_nonneg_right ha hT
    linarith
  have h3 : z ^ 2 ≤ (Real.exp (-(Real.pi ^ 2 / 8) * T) * d) ^ 2 := by
    rw [mul_pow]
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (sq_nonneg d))
  exact (pow_le_pow_iff_left₀ hz (by positivity) two_ne_zero).mp h3

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # Sharp fast decay: the quiet lemma

On a quiet stretch (drift zero) an actual-fast reversed curve decays in `H^j` at the rate `π²/2`,
with the constant `3` (`QuietHsDecayStatement` for the mean-free part; fastness bounds the mean by
the mean-free part, since `‖r‖ ≤ 1/3`). The constant does not depend on `P_e`. -/

section
variable {K : ScalarConstants} {η t₀ S : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {v : ℝ → Vec 2 → Vec 2} {ξ : Fin 2 → ℂ}

/-- Along an actual-fast reversed curve the mean is at most a third of the `L²` norm. -/
theorem sharpFast_mean_le (H : TransverseLocalHyp K η G v ξ)
    (data : FibreScalarData K η G v t₀ S) {s t : ℝ} (V : ℝ)
    (hb' : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2)
    {u : ℝ → ComplexCellL2} {slice : ℝ → TorusHk 1 ℂ} (hu : IsRevCurve H V hb' (-t) (-s) u slice)
    (hfast : cellComplexPair (cellRawTrace (fibreSeriesJet data.r ξ) t + cellConstantCLM 1)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u (-t))) = 0) :
    ∀ σ ∈ Icc s t, ‖cellMeanCLM (u (-σ))‖ ≤ (1 / 3) * ‖u (-σ)‖ := by
  set tr := cellRawTrace (fibreSeriesJet data.r ξ) with htr
  set cj := cellFiberCLM Complex.conjCLE.toContinuousLinearMap with hcj
  intro σ hσ
  have h0 : cellComplexPair (tr σ + cellConstantCLM 1) (cj (u (-σ))) = 0 := by
    rw [revCurve_pairing H.hη0 H.hη H.hCg H.hCw H.hG H.hv H.hm H.hw data ξ H.hξ V hb' hu σ hσ,
      hfast, mul_zero]
  have h1 := cellComplexPair_conjugate (tr σ + cellConstantCLM 1) (cj (u (-σ)))
  rw [h0, star_zero, hcj, cellFiberConj_involutive] at h1
  have h2 := cellComplexPair_symm (u (-σ)) (cj (tr σ + cellConstantCLM 1))
  rw [h1, star_zero, map_add, cellFiberConj_constant, star_one,
    cellComplexPair_add_right, cellComplexPair_one] at h2
  have hm' : cellMeanCLM (u (-σ)) = -cellComplexPair (u (-σ)) (cj (tr σ)) := by
    rw [cellMeanCLM_apply]
    linear_combination h2
  have hsmall := graphTrace_l2_small H.hη0 H.hη H.hCg H.hCw H.hG H.hv H.hm H.hw data ξ H.hreal
    H.hξ H.hsep σ
  have hnr : ‖tr σ‖ ≤ 1 / 3 := by
    have h0' := norm_nonneg (tr σ)
    nlinarith
  rw [hm', norm_neg]
  calc ‖cellComplexPair (u (-σ)) (cj (tr σ))‖
      ≤ ‖u (-σ)‖ * ‖cj (tr σ)‖ := cellComplexPair_norm_le _ _
    _ = ‖u (-σ)‖ * ‖tr σ‖ := by rw [hcj, cellFiberConj_norm]
    _ ≤ ‖u (-σ)‖ * (1 / 3) := mul_le_mul_of_nonneg_left hnr (norm_nonneg _)
    _ = (1 / 3) * ‖u (-σ)‖ := by ring

/-- **The quiet lemma.** On a quiet stretch `[σ, τ]` (the drift vanishes), an actual-fast reversed
curve decays in `H^j` at the rate `π²/2`, with the constant `3` (free of `P_e`). -/
theorem sharpQuiet_decay (hQ : QuietHsDecayStatement) (H : TransverseLocalHyp K η G v ξ)
    (data : FibreScalarData K η G v t₀ S) (j : ℕ) {σ τ : ℝ} (hστ : σ ≤ τ) (V : ℝ)
    (hb' : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2) (hquiet : ∀ t ∈ Icc σ τ, ∀ x, v t x = 0)
    {u : ℝ → ComplexCellL2} {slice : ℝ → TorusHk 1 ℂ} (hu : IsRevCurve H V hb' (-τ) (-σ) u slice)
    (hfast : cellComplexPair (cellRawTrace (fibreSeriesJet data.r ξ) τ + cellConstantCLM 1)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u (-τ))) = 0)
    (w₀ : TorusHk j ℂ) (hw₀ : torusHkValueCLM w₀ = u (-τ)) :
    ∃ w : TorusHk j ℂ, torusHkValueCLM w = u (-σ) ∧
      ‖w‖ ≤ 3 * Real.exp (-(Real.pi ^ 2 / 2) * (τ - σ)) * ‖w₀‖ := by
  obtain ⟨w₁, hw₁, hn₁⟩ := sharpMean_q0_rep j w₀
  rw [hw₀] at hw₁
  -- the shift
  have hfn : fibreNorm ξ ≤ Real.pi := by
    have h := H.hsep
    have hp : 0 ≤ K.Cw * K.Cg := mul_nonneg H.hCw H.hCg
    have hn0 := fibreNorm_nonneg ξ
    nlinarith [Real.pi_pos, sq_nonneg (fibreNorm ξ - Real.pi), mul_nonneg hp (sq_nonneg (fibreNorm ξ))]
  have hθ : ∀ i, ((-((fun k => (Real.sqrt η : ℂ) * ξ k) i)).im = 0 ∧
      |(-((fun k => (Real.sqrt η : ℂ) * ξ k) i)).re| ≤ Real.pi) := by
    intro i
    have hre := H.hreal i
    refine ⟨by simp [hre], ?_⟩
    have hsq := shift_sq_le H
    have hi : (Real.sqrt η * (ξ i).re) ^ 2 ≤ fibreNorm ξ ^ 2 :=
      le_trans (Finset.single_le_sum (f := fun j => (Real.sqrt η * (ξ j).re) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)) hsq
    have : |Real.sqrt η * (ξ i).re| ≤ fibreNorm ξ := abs_le_of_sq_le_sq' hi (fibreNorm_nonneg ξ)
      |> fun h => abs_le.2 h
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, abs_neg]
    linarith
  obtain ⟨w₂, hw₂, hn₂⟩ := hQ ⟨fun s _ => G (-s), fun s x => -v (-s) x,
      fun j => -((fun k => (Real.sqrt η : ℂ) * ξ k) j), 0⟩ (cellMetric_timeReverse H.hG) V
      (cellDrift_timeReverse H.hv).1 hb' (-τ) (-σ) u slice (by linarith)
      (fun t ht x => by
        have := hquiet (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩ x
        simp [this])
      (fun _ _ _ => rfl) (fun _ => rfl) hθ hu j w₁ (by rw [hw₁])
  have hmean := sharpFast_mean_le H data V hb' hu hfast σ ⟨le_rfl, hστ⟩
  obtain ⟨w, hw, hnw⟩ := sharpMean_add_const j w₂ (cellMeanCLM (u (-σ)))
  have hdecomp : u (-σ) = cellQ0CLM (u (-σ)) + cellConstantCLM (cellMeanCLM (u (-σ))) := by
    unfold cellQ0CLM
    simp
  refine ⟨w, by rw [hw, hw₂, ← hdecomp], ?_⟩
  have hq : ‖cellQ0CLM (u (-σ))‖ ≤ ‖w₂‖ := by
    rw [← hw₂]; exact PiLp.norm_apply_le w₂.val (valueIndex2 j)
  have hu' : ‖u (-σ)‖ ≤ ‖cellQ0CLM (u (-σ))‖ + ‖cellMeanCLM (u (-σ))‖ := by
    calc ‖u (-σ)‖ = ‖cellQ0CLM (u (-σ)) + cellConstantCLM (cellMeanCLM (u (-σ)))‖ := by
          rw [← hdecomp]
      _ ≤ _ := (norm_add_le _ _).trans (by rw [cellConstantCLM_norm])
  have hm2 : ‖cellMeanCLM (u (-σ))‖ ≤ ‖w₂‖ / 2 := by linarith
  have hrate : -σ - -τ = τ - σ := by ring
  rw [hrate] at hn₂
  have hexp := Real.exp_pos (-(Real.pi ^ 2 / 2) * (τ - σ))
  have hw₁n : ‖w₁‖ ≤ 2 * ‖w₀‖ := hn₁
  calc ‖w‖ ≤ ‖w₂‖ + ‖cellMeanCLM (u (-σ))‖ := hnw
    _ ≤ (3 / 2) * ‖w₂‖ := by linarith
    _ ≤ (3 / 2) * (Real.exp (-(Real.pi ^ 2 / 2) * (τ - σ)) * ‖w₁‖) := by gcongr
    _ ≤ (3 / 2) * (Real.exp (-(Real.pi ^ 2 / 2) * (τ - σ)) * (2 * ‖w₀‖)) := by gcongr
    _ = 3 * Real.exp (-(Real.pi ^ 2 / 2) * (τ - σ)) * ‖w₀‖ := by ring
end

/-! # Weighted plain decay: correction by the constant `1`

For the fast functional `ℓ(x) = ⟨F, conj x⟩` with `F = 1 + r`, `‖r‖ ≤ 1/3`, the split
`U_T + U_N = A + B` with `A = U_T + P U_N − κ·1`: the constant `κ` that makes `A` fast satisfies
`|κ| ≤ 2‖(1 − P) U_N‖`, because the total datum is fast. -/

/-- The fast functional of a constant. -/
theorem wpd_fast_const (F : ComplexCellL2) (κ : ℂ) :
    cellComplexPair F (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellConstantCLM κ)) =
      κ * cellMeanCLM F := by
  rw [cellFiberConj_constant, ← AVRegularity.CycleWords.cellScalarCLM_constant_one,
    cellComplexPair_scalar_right, cellComplexPair_const_one, star_star]

/-- The mean of `F = 1 + r` is at least `2/3` in modulus. -/
theorem wpd_mean_lower (F : ComplexCellL2) (hF : ‖F - cellConstantCLM 1‖ ≤ 1 / 3) :
    2 / 3 ≤ ‖cellMeanCLM F‖ := by
  have h1 : cellMeanCLM (F - cellConstantCLM 1) = cellMeanCLM F - 1 := by
    rw [map_sub, cellMeanCLM_one]
  have h2 : ‖cellMeanCLM F - 1‖ ≤ 1 / 3 := by
    rw [← h1]
    exact (cellMeanCLM_norm_le _).trans hF
  have h3 : ‖(1 : ℂ)‖ - ‖cellMeanCLM F‖ ≤ ‖cellMeanCLM F - 1‖ := by
    rw [norm_sub_rev]
    exact norm_sub_norm_le _ _
  rw [norm_one] at h3
  linarith

/-- The norm of `F = 1 + r`. -/
theorem wpd_norm_le (F : ComplexCellL2) (hF : ‖F - cellConstantCLM 1‖ ≤ 1 / 3) : ‖F‖ ≤ 4 / 3 := by
  have h : ‖F‖ ≤ ‖F - cellConstantCLM 1‖ + ‖cellConstantCLM (1 : ℂ)‖ := by
    have := norm_add_le (F - cellConstantCLM 1) (cellConstantCLM 1)
    simpa using this
  rw [cellConstantCLM_norm, norm_one] at h
  linarith

/-- **The constant that corrects fastness.** -/
theorem wpd_kappa (F X Y : ComplexCellL2) (hF : ‖F - cellConstantCLM 1‖ ≤ 1 / 3)
    (h : cellComplexPair F (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (X + Y)) = 0) :
    ∃ κ : ℂ, cellComplexPair F (cellFiberCLM Complex.conjCLE.toContinuousLinearMap
        (X - cellConstantCLM κ)) = 0 ∧ ‖κ‖ ≤ 2 * ‖Y‖ := by
  set cj := cellFiberCLM Complex.conjCLE.toContinuousLinearMap with hcj
  have hm := wpd_mean_lower F hF
  have hm0 : cellMeanCLM F ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hm
    linarith
  refine ⟨cellComplexPair F (cj X) / cellMeanCLM F, ?_, ?_⟩
  · rw [map_sub, cellComplexPair_sub_right, wpd_fast_const, div_mul_cancel₀ _ hm0, sub_self]
  · have hX : cellComplexPair F (cj X) = -cellComplexPair F (cj Y) := by
      rw [map_add, cellComplexPair_add_right] at h
      linear_combination h
    have hY : ‖cellComplexPair F (cj Y)‖ ≤ 4 / 3 * ‖Y‖ := by
      refine (cellComplexPair_norm_le _ _).trans ?_
      rw [hcj, cellFiberConj_norm]
      exact mul_le_mul_of_nonneg_right (wpd_norm_le F hF) (norm_nonneg _)
    rw [hX, norm_div, norm_neg, div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg Y]

/-- Constants are transverse. -/
theorem wpd_transverse_sub_const (e : Fin 2) (X : ComplexCellL2)
    (hX : cellTransverseProjection e X = X) (κ : ℂ) :
    cellTransverseProjection e (X - cellConstantCLM κ) = X - cellConstantCLM κ := by
  rw [map_sub, hX, ← AVRegularity.CycleWords.cellScalarCLM_constant_one,
    AVRegularity.CycleWords.cellTransverseProjection_scalar,
    AVRegularity.CycleWords.cellTransverseProjection_one]

end AVRegularity.CycleWords.Assembly
end
end
end
