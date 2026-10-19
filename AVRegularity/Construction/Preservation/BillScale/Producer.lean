-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Assembly.BillBound
import AVRegularity.Construction.Scales.Times
public import AVRegularity.Construction.Preservation.Assembly.PreparationJointInputs
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.CycleReference.TorusChartEquation
import AVRegularity.CycleReference.ChartCorrectionIntegrability
import Mathlib.Algebra.Order.Star.Real

section
section
/-! Scalar assembly of the successor bill. Its inputs are primitive amplitude/width bounds,
a closure bound and a quiet exponential bound; no bill estimate is an input.

Special cases: zero amplitudes and an empty identity family are allowed. The zeroth power
has its usual value one; the scheduled exponents decide when it can occur. The result does
not depend on component spaces, the metric, the seed edges or the sign of CQ and Cpr. -/

@[expose] public section
namespace AVRegularity.Construction.Preservation.BillScale

/-- Multiply a natural power estimate by the contrast power, retaining its sharp exponent. -/
theorem weighted_power_le {E x K a w Q : ℝ} (hE : 0 < E) (hE1 : E ≤ 1)
    (hx : 0 ≤ x) (hK : 0 ≤ K) (hxK : x ≤ K * E ^ a) (n : ℕ)
    (hexp : Q + w ≤ a * n) :
    E ^ (-w) * x ^ n ≤ K ^ n * E ^ Q := by
  have hp := CycleComparison.Assembly.powerLaw_pow hE hx hxK n
  calc
    _ ≤ E ^ (-w) * (K ^ n * E ^ (a * n)) :=
      mul_le_mul_of_nonneg_left hp (Real.rpow_pos_of_pos hE _).le
    _ = K ^ n * E ^ (a * n - w) := by
      rw [sub_eq_add_neg, Real.rpow_add hE]
      ring
    _ ≤ K ^ n * E ^ Q := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hE hE1 (by linarith)) (pow_nonneg hK n)

/-- The frontier terms have coefficient one after paying the contrast power. -/
theorem weighted_rpow_le {E a w Q : ℝ} (hE : 0 < E) (hE1 : E ≤ 1)
    (hexp : Q + w ≤ a) : E ^ (-w) * E ^ a ≤ E ^ Q := by
  rw [← Real.rpow_add hE]
  exact Real.rpow_le_rpow_of_exponent_ge hE hE1 (by linarith)

/-- Assemble the seven physical groups, keeping the two covariance powers together. -/
theorem bill_le_of_primitive_bounds {E ω eo ef ec Z ℓ τ T c w Q δ σ gf g₀ g₁ : ℝ}
    {Kω Ko Kf Kc Zc Kquiet : ℝ} {p Lc Lf N : ℕ}
    (hE : 0 < E) (hE1 : E ≤ 1)
    (hω : 0 ≤ ω) (heo : 0 ≤ eo) (hef : 0 ≤ ef) (hec : 0 ≤ ec)
    (hKω : 0 ≤ Kω) (hKo : 0 ≤ Ko) (hKf : 0 ≤ Kf) (hKc : 0 ≤ Kc)
    (hωb : ω ≤ Kω * E ^ δ) (heob : eo ≤ Ko * E ^ σ)
    (hefb : ef ≤ Kf * E ^ gf) (hecb : ec ≤ Kc * E ^ (3 * δ))
    (hZ0 : 0 ≤ Z) (hZ : Z ≤ Zc)
    (hp : Q + w ≤ δ * p) (hp1 : Q + w ≤ δ * (p + 1))
    (hLc : Q + w ≤ σ * Lc) (hg₀ : Q + w ≤ g₀)
    (hg₁ : Q + w ≤ g₁) (hN : Q ≤ 3 * δ * N)
    (hLf : Q ≤ gf * Lf)
    (hquiet : ℓ * Real.sqrt ((1 + T / τ) / τ) * Real.exp (-(c * τ / ℓ ^ 2)) ≤
      Kquiet * E ^ Q) :
    E ^ (-w) * (ω ^ p + ω ^ (p + 1) + eo ^ Lc + E ^ g₀ + E ^ g₁) +
        ec ^ N * (1 + Z) +
        ℓ * Real.sqrt ((1 + T / τ) / τ) * Real.exp (-(c * τ / ℓ ^ 2)) + ef ^ Lf ≤
      (Kω ^ p + Kω ^ (p + 1) + Ko ^ Lc + 2 + Kc ^ N * (1 + Zc) + Kquiet +
        Kf ^ Lf) * E ^ Q := by
  have h1 := weighted_power_le hE hE1 hω hKω hωb p hp
  have h2 := weighted_power_le hE hE1 hω hKω hωb (p + 1) (by simpa only [Nat.cast_add, Nat.cast_one] using hp1)
  have h3 := weighted_power_le hE hE1 heo hKo heob Lc hLc
  have h4 := weighted_rpow_le hE hE1 hg₀
  have h5 := weighted_rpow_le hE hE1 hg₁
  have h6 := CycleComparison.Assembly.bill_first_le hE hE1 hKc hec hecb hZ0 hZ hN
  have h7 := CycleComparison.Assembly.powerLaw_pow hE hef hefb Lf
  have h8 : ef ^ Lf ≤ Kf ^ Lf * E ^ Q := h7.trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hE hE1 hLf) (pow_nonneg hKf Lf))
  calc
    _ = E ^ (-w) * ω ^ p + E ^ (-w) * ω ^ (p + 1) + E ^ (-w) * eo ^ Lc +
        E ^ (-w) * E ^ g₀ + E ^ (-w) * E ^ g₁ + ec ^ N * (1 + Z) +
        ℓ * Real.sqrt ((1 + T / τ) / τ) * Real.exp (-(c * τ / ℓ ^ 2)) + ef ^ Lf := by ring
    _ ≤ Kω ^ p * E ^ Q + Kω ^ (p + 1) * E ^ Q + Ko ^ Lc * E ^ Q + E ^ Q + E ^ Q +
        Kc ^ N * (1 + Zc) * E ^ Q + Kquiet * E ^ Q + Kf ^ Lf * E ^ Q :=
      add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
        (add_le_add h1 h2) h3) h4) h5) h6) hquiet) h8
    _ = _ := by ring

end AVRegularity.Construction.Preservation.BillScale
end
end

section
/-! Uniform scalar contraction of the bill from amplitude, closure and clock estimates.
Special cases: zero covariance/width amplitudes are allowed, including empty families.
The interval may have length zero; no component, metric, seed-edge or data norm is used.
The constant is chosen before all scalar scales and all interval endpoints. -/

@[expose] public section
namespace AVRegularity.Construction.Preservation.BillScale
open AVRegularity.CycleComparison.Assembly

/-- The primitive physical-scale facts needed by the scalar contraction. -/
structure PhysicalScaleBounds (E ω eo ef ec r ℓ τ T K Ko Kf δ σ gf g A b : ℝ) : Prop where
  E_pos : 0 < E
  E_le_one : E ≤ 1
  omega_nonneg : 0 ≤ ω
  coarse_nonneg : 0 ≤ eo
  fine_nonneg : 0 ≤ ef
  cell_nonneg : 0 ≤ ec
  ratio_nonneg : 0 ≤ r
  ell_pos : 0 < ℓ
  tau_pos : 0 < τ
  time_nonneg : 0 ≤ T
  omega_le : ω ≤ K * E ^ δ
  coarse_le : eo ≤ Ko * E ^ σ
  fine_le : ef ≤ Kf * E ^ gf
  cell_le : ec ≤ K * E ^ (3 * δ)
  ratio_le : r ≤ K * E ^ g
  ell_inv_le : ℓ⁻¹ ≤ K * E ^ (-A)
  tau_inv_le : τ⁻¹ ≤ K * E ^ (-b)
  quiet_le : K⁻¹ * E ^ (-(4 * δ)) ≤ τ / ℓ ^ 2

/-- Choose the contraction constant before the physical scales. -/
theorem scalar_bill_contraction (Q w δ σ gf g A b K Ko Kf T₀ c gr len : ℝ)
    (p N Lc Lf Acl : ℕ) (hδ : 0 < δ) (hK : 0 < K)
    (hKo : 0 ≤ Ko) (hKf : 0 ≤ Kf) (hT₀ : 0 ≤ T₀) (hc : 0 < c)
    (hb : 0 ≤ b) (hw : 0 ≤ w)
    (hp : Q + w ≤ δ * p) (hLc : Q + w ≤ σ * Lc)
    (hN : Q + w ≤ 3 * δ * N) (hLf : Q ≤ gf * Lf)
    (hAcl : A ≤ g * Acl) (hgr : Q + w ≤ gr) (hlen : Q + w ≤ len) :
    ∃ C : ℝ, ∀ E ω eo ef ec r ℓ τ T : ℝ,
      PhysicalScaleBounds E ω eo ef ec r ℓ τ T K Ko Kf δ σ gf g A b → T ≤ T₀ →
      E ^ (-w) * (ω ^ p + ω ^ (p + 1) + eo ^ Lc + E ^ gr + E ^ len) +
        ec ^ N * (1 + Real.sqrt T / ℓ * r ^ Acl) +
        ℓ * Real.sqrt ((1 + T / τ) / τ) * Real.exp (-(c * τ / ℓ ^ 2)) + ef ^ Lf ≤
        C * E ^ Q := by
  obtain ⟨n, hn⟩ := exists_nat_ge ((Q + b) / (4 * δ))
  have hn' : Q + b ≤ 4 * δ * n := by
    simpa only [mul_comm] using (div_le_iff₀ (by positivity : 0 < 4 * δ)).mp hn
  let Zc := (1 + T₀) * K * K ^ Acl
  let Kquiet := (1 + 5 * K * (1 + T₀ * K)) * (K ^ n * (n.factorial : ℝ) / c ^ n)
  refine ⟨K ^ p + K ^ (p + 1) + Ko ^ Lc + 2 + K ^ N * (1 + Zc) + Kquiet + Kf ^ Lf, ?_⟩
  intro E ω eo ef ec r ℓ τ T h hT
  have hT' : T ≤ T₀ * E ^ (-(0 : ℝ)) := by simpa only [neg_zero, Real.rpow_zero, mul_one] using hT
  have hZ := billZ_le h.E_pos h.E_le_one hK.le (by norm_num : (0 : ℝ) ≤ 0)
    hT₀ h.time_nonneg hT' h.ell_pos h.ell_inv_le h.ratio_nonneg h.ratio_le
    (by simpa only [zero_add] using hAcl)
  have hBp : 1 + T / τ ≤ 5 * (1 + T₀ * K) * E ^ (-((0 : ℝ) + b)) := by
    apply pulseCount_le_powerLaw h.E_pos h.E_le_one
      (by norm_num : (0 : ℝ) ≤ 0) hb h.time_nonneg hT' h.tau_pos h.tau_inv_le
    have hpos : 0 ≤ 1 + T / τ := add_nonneg zero_le_one (div_nonneg h.time_nonneg h.tau_pos.le)
    linarith only [hpos]
  have hquiet := bill_third_le (n := n) h.E_pos h.E_le_one hδ.le hK hc hT₀
    (by simpa only [zero_add] using hb) h.ell_pos h.tau_pos
    (add_nonneg zero_le_one (div_nonneg h.time_nonneg h.tau_pos.le)) hBp h.quiet_le
    (by simpa only [zero_add] using hn')
  apply bill_le_of_primitive_bounds h.E_pos h.E_le_one h.omega_nonneg h.coarse_nonneg
    h.fine_nonneg h.cell_nonneg hK.le hKo hKf hK.le h.omega_le h.coarse_le h.fine_le
    h.cell_le (mul_nonneg (div_nonneg (Real.sqrt_nonneg T) h.ell_pos.le)
      (pow_nonneg h.ratio_nonneg Acl)) hZ hp (by linarith) hLc hgr hlen
    (by linarith only [hN, hw]) hLf hquiet

end AVRegularity.Construction.Preservation.BillScale
end
end
end

section
section
/-! The incoming invariant bounds the two kernel-width suprema in the successor bill.
Special cases: these estimates include EMPTY component/identity types (their real supremum
is zero), singleton families and seeds without edges. No solution, metric or preparation
constant enters, and zero derivative orders are allowed. -/

@[expose] public noncomputable section
namespace AVRegularity.Construction.Preservation.BillScale

/-- Fine widths, after the rounded epsilon step; no separation threshold depends on σf. -/
theorem fine_width_sup_le {ι : Type*} (Γ : ι → ι → Type*) (width : ∀ v u, Γ v u → ℝ)
    {e E q σf ρ C : ℝ} (hρ : 0 < ρ) (he : 0 ≤ e) (hE : 0 < E)
    (hC : 0 ≤ C) (hσ : 0 ≤ σf) (heE : e ≤ 2 * E ^ q)
    (hw : ∀ v u γ, width v u γ ≤ C * ρ * e ^ σf) :
    (⨆ v, ⨆ u, ⨆ γ, width v u γ / ρ) ≤ (C * 2 ^ σf) * E ^ (q * σf) := by
  have hp : e ^ σf ≤ 2 ^ σf * E ^ (q * σf) := by
    have h := Real.rpow_le_rpow he heE hσ
    rwa [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.rpow_pos_of_pos hE q).le,
      ← Real.rpow_mul hE.le] at h
  have hb : 0 ≤ (C * 2 ^ σf) * E ^ (q * σf) := by positivity
  apply Real.iSup_le _ hb
  intro v
  apply Real.iSup_le _ hb
  intro u
  apply Real.iSup_le _ hb
  intro γ
  calc
    _ ≤ C * e ^ σf := (div_le_iff₀ hρ).2 (by simpa only [mul_right_comm] using hw v u γ)
    _ ≤ C * (2 ^ σf * E ^ (q * σf)) := mul_le_mul_of_nonneg_left hp hC
    _ = _ := by ring

/-- Coarse widths with the max floor; the admissible inequality σ₀ < lamC is sufficient. -/
theorem coarse_width_sup_le {ι : Type*} (Γ : ι → ι → Type*) (width : ∀ v u, Γ v u → ℝ)
    {E σ lamC ρ C : ℝ} (hρ : 0 < ρ) (hE : 0 < E) (hE1 : E ≤ 1)
    (hC : 0 ≤ C) (hσ : σ ≤ lamC)
    (hw : ∀ v u γ, width v u γ ≤ C * ρ * E ^ lamC) :
    max (E ^ σ) (⨆ v, ⨆ u, ⨆ γ, width v u γ / ρ) ≤ max 1 C * E ^ σ := by
  have hCb : 0 ≤ max 1 C * E ^ σ := by positivity
  refine max_le ?_ ?_
  · exact le_mul_of_one_le_left (Real.rpow_pos_of_pos hE σ).le (le_max_left _ _)
  · apply Real.iSup_le _ hCb
    intro v
    apply Real.iSup_le _ hCb
    intro u
    apply Real.iSup_le _ hCb
    intro γ
    calc
      _ ≤ C * E ^ lamC := (div_le_iff₀ hρ).2 (by simpa only [mul_right_comm] using hw v u γ)
      _ ≤ C * E ^ σ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_ge hE hE1 hσ) hC
      _ ≤ max 1 C * E ^ σ := mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.rpow_pos_of_pos hE σ).le

end AVRegularity.Construction.Preservation.BillScale
end
end

section
/-! The inverse cell-length estimate used in Zcl. The general ScaleLaws inverse-length
bound loses too many powers here; the interior diffusivity comparison gives the sharp
relaxation exponent before taking the square root.

Special cases: the result is scalar and independent of component count, seed edges,
metric and CQ/Cpr. The level is an interior passage (2 ≤ m < M); no claim is made at
an extrapolated weak level. -/

@[expose] public section
namespace AVRegularity.Construction.Preservation.BillScale
open AVRegularity.CycleReference

/-- Four covariance entries, followed by the time supremum and enhanced-radius division. -/
theorem covariance_sum_sup_le {ι : Type*} (H : ι → Matrix (Fin 2) (Fin 2) ℝ)
    {R cr E C δ : ℝ} (hR : 0 < R) (hcr : 0 < cr) (hE : 0 < E) (hC : 0 ≤ C)
    (hentry : ∀ t i j, |H t i j| / R ^ 2 ≤ C * E ^ δ) :
    (⨆ t, ∑ i : Fin 2, ∑ j : Fin 2, |H t i j|) / (cr * R) ^ 2 ≤
      (4 * C / cr ^ 2) * E ^ δ := by
  have hpoint (t : ι) : (∑ i : Fin 2, ∑ j : Fin 2, |H t i j|) ≤
      4 * (C * E ^ δ * R ^ 2) := by
    calc
      _ ≤ ∑ _i : Fin 2, ∑ _j : Fin 2, C * E ^ δ * R ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        exact (div_le_iff₀ (pow_pos hR 2)).mp (hentry t i j)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hs := Real.iSup_le hpoint (by positivity : 0 ≤ 4 * (C * E ^ δ * R ^ 2))
  calc
    _ ≤ (4 * (C * E ^ δ * R ^ 2)) / (cr * R) ^ 2 :=
      div_le_div_of_nonneg_right hs (sq_nonneg _)
    _ = _ := by field_simp [hR.ne', hcr.ne']

theorem band_inverse_cell_length {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ M : ℕ, 1 ≤ M → ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
      ∀ m : ℕ, 2 ≤ m → m < M →
        (ocEll q Λ m (κ m))⁻¹ ≤ C * ocEpsilon q Λ (m - 1) ^
          (-(2 - (1 + α) + 8 * ocDelta α q)) := by
  obtain ⟨Ci, hCi, Li, hLi, hi⟩ := bandChain_interior_diffusivities hα0 hα1 hs0 hs1 hq hζ
  let p := 2 - ((1 + α) + ocGamma α q)
  obtain ⟨K, hK, Lk, hLk, hk⟩ := epsilon_power_scale_asymp hq.1 p
  have hCip : 0 < Ci := zero_lt_one.trans_le hCi
  have hKp : 0 < K := zero_lt_one.trans_le hK
  have hCK : 0 < Ci * K := mul_pos hCip hKp
  have hδ := (Scales.admissible_delta_mu_positive hα0 hα1 hs0 hs1 hq).1
  have hP : 0 ≤ 2 - (1 + α) + 8 * ocDelta α q := by linarith
  refine ⟨1 + Ci * K, le_add_of_nonneg_right hCK.le, max Li Lk, hLi.trans (le_max_left _ _), ?_⟩
  intro Λ hΛ M hM κ hκ m hm hmM
  have h128 := hLi.trans ((le_max_left _ _).trans hΛ)
  have he := (Scales.epsilon_basic (m := m) hq.1 h128).1
  have hE := (Scales.epsilon_basic (m := m - 1) hq.1 h128).1
  have hE1 := (Scales.epsilon_basic (m := m - 1) hq.1 h128).2.1
  have hν := bandChain_pos (by omega : 1 ≤ Λ) hζ hκ hmM.le
  have hnu := hi Λ ((le_max_left _ _).trans hΛ) M hM κ hκ m (by omega) hmM
  have hquot := asymp_div (by norm_num : (0 : ℝ) < 1) hCip
    (sq_nonneg (ocEpsilon q Λ m)) (Real.rpow_pos_of_pos he _) hν
    (asymp_one_self (ocEpsilon q Λ m ^ 2)) hnu
  have hpower : ocEpsilon q Λ m ^ 2 / ocEpsilon q Λ m ^ ((1 + α) + ocGamma α q) =
      ocEpsilon q Λ m ^ p := by
    rw [show p = 2 - ((1 + α) + ocGamma α q) by rfl, Real.rpow_sub he, Real.rpow_two]
  simp only [one_mul, hpower] at hquot
  have hexp : q * p = 2 - (1 + α) + 8 * ocDelta α q := by
    have h := memory_exponent_identity (α := α) hq.1
    dsimp [p]
    convert h using 1; ring
  have hscale := hk Λ m ((le_max_right _ _).trans hΛ) hm
  rw [hexp] at hscale
  have hsq := asymp_trans hCip hKp hquot hscale
  rw [← ocEll_sq_eq hν] at hsq
  have hℓ : 0 < ocEll q Λ m (κ m) := div_pos he (Real.sqrt_pos.mpr hν)
  have hroot := asymp_sqrt hCK (Real.rpow_pos_of_pos hE _).le hsq
  have hsqrt : Real.sqrt (ocEpsilon q Λ (m - 1) ^ (2 - (1 + α) + 8 * ocDelta α q)) =
      ocEpsilon q Λ (m - 1) ^ ((2 - (1 + α) + 8 * ocDelta α q) * (1 / 2)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hE.le]
  rw [Real.sqrt_sq hℓ.le, hsqrt] at hroot
  have hinv := CycleComparison.Assembly.inv_le_powerLaw hE (Real.sqrt_pos.mpr hCK) hroot.1
  calc
    _ ≤ Real.sqrt (Ci * K) * ocEpsilon q Λ (m - 1) ^
        (-((2 - (1 + α) + 8 * ocDelta α q) * (1 / 2))) := hinv
    _ ≤ (1 + Ci * K) * ocEpsilon q Λ (m - 1) ^
        (-((2 - (1 + α) + 8 * ocDelta α q) * (1 / 2))) :=
      mul_le_mul_of_nonneg_right (CycleComparison.Assembly.sqrt_le_one_add hCK.le)
        (Real.rpow_pos_of_pos hE _).le
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hE hE1 (by linarith)) (by positivity)

end AVRegularity.Construction.Preservation.BillScale
end
end

section
/-! The scalar successor bill, with the original order of all uniform choices.
Only preparation times, incoming widths and band-scale estimates are consumed.

Empty components and an edgeless seed retain the temporal scalar bill. Ain = 0 and signed
CQ/Cpr have no role in this scalar estimate. -/

@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.BillScale
open AVRegularity.CycleReference AVRegularity.CycleComparison.Assembly
open AVRegularity.Construction.Preservation.Assembly

/-- The scalar bill leaf follows from the diffusivity ledger and incoming widths. -/
theorem successor_bill_scale {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    SuccessorBillScaleStatement α s q ζ := by
  classical
  obtain ⟨Cb, hCb, Lb, hLb, hb⟩ := bandChain_uniform_ledger hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Cs, hCs, Ls, hLs, hs⟩ := scale_laws α s hα0 hα1 hs0 hs1 q hq ζ hζ
  obtain ⟨Ci, hCi, Li, _hLi, hi⟩ := band_inverse_cell_length hα0 hα1 hs0 hs1 hq hζ
  have hCb0 : 0 < Cb := zero_lt_one.trans_le hCb
  have hCs0 : 0 < Cs := zero_lt_one.trans_le hCs
  have hCi0 : 0 < Ci := zero_lt_one.trans_le hCi
  have hfact := Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq
  have hδ := hfact.2.1
  have hγ := hfact.1
  have hq0 : 0 < q := zero_lt_one.trans hq.1
  refine ⟨max Lb (max Ls Li), hLb.trans (le_max_left _ _), ?_⟩
  intro Λ hΛ
  have hΛb : Lb ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛs : Ls ≤ Λ := (le_max_left _ _).trans ((le_max_right _ _).trans hΛ)
  have hΛi : Li ≤ Λ := (le_max_right _ _).trans ((le_max_right _ _).trans hΛ)
  have h128 : 128 ≤ Λ := hLb.trans hΛb
  have hΛ1 : 1 ≤ Λ := by omega
  refine ⟨1, zero_lt_one, ?_⟩
  intro φ₀ hφ₀ _ _ _ _ bw _ _ Q T₀ _ hT₀ Ce τe kS r₀ D₀ _ _
    hc₀ _ hcr _ hσf _ H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ
    hsched _ _ _ _ _
  obtain ⟨hgr, hlen, hN, hp, hAcl, hσ₀, ha, haσ, _, _, hLc, hLf, _⟩ := hsched
  have hσ : 0 < σ₀ := by linarith only [hσ₀, ha, haσ]
  have hσfmin : 0 < min kS.σf (ocDelta α q + σ₀) := lt_min hσf (add_pos hδ hσ)
  refine ⟨{ kS with Cwid := 1 }, 1, 1, le_rfl, zero_lt_one, ?_⟩
  intro kI hkI
  obtain ⟨hc₀I, hcrI, _, _, _, hCwid, hσfI, hlamI, _⟩ := hkI
  change 1 ≤ kI.Cwid at hCwid
  have hCwid0 : 0 ≤ kI.Cwid := zero_le_one.trans hCwid
  have hσfI0 : 0 < kI.σf := hσfI.symm ▸ hσfmin
  have hcrI0 : 0 < kI.cr := hcrI.symm ▸ hcr
  have hc₀I0 : 0 < kI.c₀ := hc₀I.symm ▸ hc₀
  let K := Cb + Cs + Ci + Cb / kI.cr + 4 * Cb / kI.cr ^ 2 + 1
  have hdiv : 0 ≤ Cb / kI.cr := (div_pos hCb0 hcrI0).le
  have hdiv2 : 0 ≤ 4 * Cb / kI.cr ^ 2 := by positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hKb : Cb ≤ K := by dsimp [K]; linarith only [hCs0, hCi0, hdiv, hdiv2]
  have hKs : Cs ≤ K := by dsimp [K]; linarith only [hCb0, hCi0, hdiv, hdiv2]
  have hKi : Ci ≤ K := by dsimp [K]; linarith only [hCb0, hCs0, hdiv, hdiv2]
  have hKc : Cb / kI.cr ≤ K := by dsimp [K]; linarith only [hCb0, hCs0, hCi0, hdiv2]
  have hKω : 4 * Cb / kI.cr ^ 2 ≤ K := by dsimp [K]; linarith only [hCb0, hCs0, hCi0, hdiv]
  refine ⟨0, 0, ?_⟩
  intro CI Cw j₀ _ _ CQ Cpr c hc
  obtain ⟨C, hbound⟩ := scalar_bill_contraction Q (q * ocGamma α q) (ocDelta α q)
    σ₀ (q * kI.σf) (q * ocGamma α q + 3 * ocDelta α q)
    (2 - (1 + α) + 8 * ocDelta α q) (2 - (1 + α) + 4 * ocDelta α q)
    K (max 1 kI.Cwid) (kI.Cwid * 2 ^ kI.σf) T₀ c
    (succEta0 α q s / 8 * succSigmaH q H)
    (succTheta1 α q s σ₀ (succDstar D₀ N p H) + J * succTheta2 α q s σ₀ (succDstar D₀ N p H))
    p N Lc Lf Acl hδ hK (by positivity) (by positivity) hT₀.le hc
    (by linarith only [hα1, hδ]) (mul_pos hq0 hγ).le
    (by linarith only [hp]) (by linarith only [hLc]) (by linarith only [hN])
    (by rw [hσfI]; linarith only [hLf]) hAcl
    (by linarith only [hgr]) (by linarith only [hlen])
  refine ⟨C, 2, ?_⟩
  intro D hDα hDq hDΛ hDζ _ M hband hterm Mnat _ law _
    hr _ _ _ _ _ _ _ seedK freshK _ seed n tS tf _ m hm hn hnM
    tA s₀ _ _ hs₀tf htime G G' _ hlevel hG _ tp Preg hprep f Ain _
    Y0 Y Yw Yk _ _
  have hmM : m < M := hn.trans_lt hnM
  have hb := (hb Λ hΛb M (by omega) D.κ hband).2 m hm hmM.le (D.κ m) (D.κ (m - 1)) rfl rfl
  obtain ⟨_, _, _, _, _, _, _, hec, her, _, _, _, _, _, _, hcov⟩ := hb
  have hs := hs Λ hΛs M D.κ hband m hm hmM.le (D.κ m) (D.κ (m - 1)) rfl rfl
  have hi := hi Λ hΛi M (by omega) D.κ hband m hm hmM
  have hE := (Scales.epsilon_basic (m := m - 1) hq.1 h128).1
  have hE1 := (Scales.epsilon_basic (m := m - 1) hq.1 h128).2.1
  have he := (Scales.epsilon_basic (m := m) hq.1 h128).1
  have hB := bandChain_pos hΛ1 hζ hband (show m - 1 ≤ M by omega)
  have hτpp := Construction.Stream.ocTauPP_pos (α := α) (q := q) (m := m) hΛ1
  have hR : 0 < Real.sqrt (D.κ (m - 1) * ocTauPP α q Λ m) :=
    Real.sqrt_pos.mpr (mul_pos hB hτpp)
  have hρ : 0 < rhoEnh D kI.cr m := by
    simpa only [rhoEnh, hDα, hDq, hDΛ] using mul_pos hcrI0 hR
  have hA : 0 < ocA D.α D.q D.Λ m := Real.rpow_pos_of_pos
    (by simpa only [hDq, hDΛ] using he) _
  have hρs : 0 < rhoStar D kI.c₀ m := by
    apply mul_pos hc₀I0
    apply lt_min
    · simpa only [OCData.eps, hDq, hDΛ] using he
    · exact Real.sqrt_pos.mpr (div_pos hs.ν_pos hA)
  have hℓeq : Real.sqrt (D.cellScaleSq m) = ocEll q Λ m (D.κ m) := by
    rw [OCData.cellScaleSq, OCData.kap, hterm, Nat.min_eq_left hmM.le,
      OCData.eps, hDq, hDΛ, Real.sqrt_div (sq_nonneg _), Real.sqrt_sq he.le]
    rfl
  have hℓ : 0 < ocEll q Λ m (D.κ m) := div_pos he (Real.sqrt_pos.mpr hs.ν_pos)
  obtain ⟨_, _, _, _, _, _, _, _, hker, _⟩ := hG
  have hfine (v u) (γ : G.fam.Γ v u) := (hker v u γ).2.2.1
  have hcoarse (v u) (γ : G.fam.Γ v u) := (hker v u γ).2.2.2.1
  simp only [hlevel] at hfine hcoarse
  have hef := fine_width_sup_le G.fam.Γ (fun v u γ => (G.fam.identity v u γ).record.width)
    hρs (by simpa only [OCData.eps, hDq, hDΛ] using he.le) hE hCwid0 hσfI0.le
    (Scales.epsilon_q_step hq.1 hq.2.1 h128 (by omega))
    (by simpa only [OCData.eps, hDq, hDΛ] using hfine)
  have heo := coarse_width_sup_le G.fam.Γ (fun v u γ => (G.fam.identity v u γ).record.width)
    hρ hE hE1 hCwid0 hlamI.le (by simpa only [OCData.eps, hDq, hDΛ] using hcoarse)
  have hω := covariance_sum_sup_le (fun t : Set.Icc tp tf => covPrimitive D m t)
    hR hcrI0 hE hCb0.le (fun t i j => by
      simpa only [covPrimitive, hDα, hDq, hDΛ, hDζ, ocRh] using (hcov 0 t i j).2.2.2)
  have hρeq : rhoEnh D kI.cr m = kI.cr * ocRh α q Λ m (D.κ (m - 1)) := by
    simp only [rhoEnh, ocRh, hDα, hDq, hDΛ]
  have hec' : ocDStar q Λ m (D.κ m) (D.κ (m - 1)) / rhoEnh D kI.cr m ≤
      (Cb / kI.cr) * ocEpsilon q Λ (m - 1) ^ (3 * ocDelta α q) := by
    rw [hρeq]
    calc
      _ = (ocDStar q Λ m (D.κ m) (D.κ (m - 1)) / ocRh α q Λ m (D.κ (m - 1))) / kI.cr := by ring
      _ ≤ (Cb * ocEpsilon q Λ (m - 1) ^ (3 * ocDelta α q)) / kI.cr :=
        div_le_div_of_nonneg_right hec hcrI0.le
      _ = _ := by ring
  have her' : D.eps m / rhoEnh D kI.cr m ≤
      (Cb / kI.cr) * ocEpsilon q Λ (m - 1) ^ (q * ocGamma α q + 3 * ocDelta α q) := by
    rw [hρeq, OCData.eps, hDq, hDΛ]
    calc
      _ = (ocEpsilon q Λ m / ocRh α q Λ m (D.κ (m - 1))) / kI.cr := by ring
      _ ≤ (Cb * ocEpsilon q Λ (m - 1) ^ (q * ocGamma α q + 3 * ocDelta α q)) / kI.cr :=
        div_le_div_of_nonneg_right her.2 hcrI0.le
      _ = _ := by ring
  have hT : 0 ≤ tf - tp := by
    have htp := hprep.2.2.1
    simp only [hlevel, hDα, hDq, hDΛ] at htp
    linarith only [htp, hs₀tf]
  have hTle : tf - tp ≤ T₀ := by linarith only [hprep.2.1, htime]
  have hω0 : 0 ≤ (⨆ t : Set.Icc tp tf, ∑ i : Fin 2, ∑ j : Fin 2, |covPrimitive D m t i j|) /
      rhoEnh D kI.cr m ^ 2 := div_nonneg (Real.iSup_nonneg fun _ =>
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (sq_nonneg _)
  have hef0 : 0 ≤ (⨆ (v : CompIn G.comps) (u : CompIn G.comps) (γ : G.fam.Γ v u),
      (G.fam.identity v u γ).record.width / rhoStar D kI.c₀ m) :=
    Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ =>
      div_nonneg (ConstituentRecord.width_pos _).le hρs.le
  have hup {x a C₀ : ℝ} (hC₀ : C₀ ≤ K) (hx : x ≤ C₀ * ocEpsilon q Λ (m - 1) ^ a) :
      x ≤ K * ocEpsilon q Λ (m - 1) ^ a :=
    hx.trans (mul_le_mul_of_nonneg_right hC₀ (Real.rpow_pos_of_pos hE _).le)
  have hout := hbound (D.eps (m - 1))
    ((⨆ t : Set.Icc tp tf, ∑ i : Fin 2, ∑ j : Fin 2, |covPrimitive D m t i j|) / rhoEnh D kI.cr m ^ 2)
    (max (D.eps (m - 1) ^ σ₀) (⨆ (v : CompIn G.comps) (u : CompIn G.comps) (γ : G.fam.Γ v u),
      (G.fam.identity v u γ).record.width / rhoEnh D kI.cr m))
    (⨆ (v : CompIn G.comps) (u : CompIn G.comps) (γ : G.fam.Γ v u),
      (G.fam.identity v u γ).record.width / rhoStar D kI.c₀ m)
    (ocDStar q Λ m (D.κ m) (D.κ (m - 1)) / rhoEnh D kI.cr m)
    (D.eps m / rhoEnh D kI.cr m) (ocEll q Λ m (D.κ m)) (ocTau α q Λ m) (tf - tp) ?_ hTle
  · simpa only [succBill, hDα, hDq, hDΛ, hℓeq] using hout
  · simp only [OCData.eps, hDq, hDΛ] at hef heo her' ⊢
    refine ⟨hE, hE1, hω0, (Real.rpow_pos_of_pos hE _).le.trans (le_max_left _ _), hef0,
      div_nonneg (mul_nonneg he.le (Real.sqrt_nonneg _)) hρ.le,
      div_nonneg he.le hρ.le, hℓ, Construction.Stream.ocTau_pos hΛ1, hT,
      ?_, heo, hef, hup hKc hec', hup hKc her', hup hKi hi, hup hKs hs.tau_inv_le, ?_⟩
    · apply hup hKω
      simpa only [rhoEnh, hDα, hDq, hDΛ] using hω
    · exact (mul_le_mul_of_nonneg_right (inv_anti₀ hCs0 hKs)
        (Real.rpow_pos_of_pos hE _).le).trans hs.quiet_ge

end AVRegularity.Construction.Preservation.BillScale
end
end
end
