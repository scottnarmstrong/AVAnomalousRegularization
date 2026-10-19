-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.CascadeInvariants.Diag.SizeQ
public import AVRegularity.Proofs.CascadeInvariants.ReserveGrade
import AVRegularity.CycleReference.TorusChartEquation
import AVRegularity.Definitions.Finite.FiniteLiftBridge
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov

@[expose] public noncomputable section

section
open Homogenization AVRegularity AVRegularity.Sobolev
open scoped ENNReal NNReal
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger, first source: the algebra of the ledger.**
* `DiagConsts`: the constants of the ledger of the first source (reserve step, rates, budgets,
  the profile bounds `W_g, W_c, W_l, K_g, K_d`, the Cauchy constants, the dimensionless cost `s`
  of one label derivative at the length `ρ`, the ledger weight `W_r`);
* `diag_sigma`: the cost of one label derivative `σ = s/ε_i` satisfies the context, family and
  leaf conditions, and `σρ ≤ s`, `|ρ| C_slow/(ε_i Δ) ≤ S` for `ρ ≤ ε_i`;
* `diagKfs`, `diagThr`: the level-free constant of the first source and the threshold of `C_w`;
  `fsK_diag_le`: `fsK · ρ ≤ diagKfs · κ_i ε_i^δ` from the scale facts;
* `diag_record_le`: the record bound of the witnesses `θ = W_r |λ_d| fsK ρ^{d-1}`. -/

section
open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant AVRegularity.Providers.ComplexContext
  AVRegularity.Providers.ComplexFlow

/-! ### The constants -/

/-- **The constants of the ledger of the first source.** -/
structure DiagConsts (bw : ℝ) (Lstar : ℕ) (κc : MajConsts) (N p : ℕ) (Δ a a₀ : ℝ) (L₀ : ℕ)
    (s Wg Wc Wl Kg Kd S : ℝ≥0) (Wr Cold Cslow : ℝ) : Prop where
  hΔ : 0 < Δ
  ha3 : 3 * Real.pi * bw < a
  ha₀ : 0 ≤ a₀
  hLf : fsR N p (2 * N + 1) ≤ L₀
  hLN : N + 1 ≤ L₀
  hWg : ∀ L, L ≤ L₀ → geoW κc a L ≤ Wg
  hWc : ∀ L, L ≤ L₀ → wsum a L κc.child ≤ Wc
  hWl : ∀ L, L ≤ L₀ →
    wsum a L (fun h => ENNReal.ofReal (Real.exp (-(6 * Real.pi * bw * |(h : ℝ)|)))) ≤ Wl
  hKg : ∀ L, L ≤ L₀ → geoW κc a₀ L ≤ Kg
  hKd : ∀ (k : Fin 2) (L : ℕ), L ≤ L₀ → wsum a₀ L (κc.drift k) ≤ Kd
  hCold0 : 0 ≤ Cold
  hCslow0 : 0 ≤ Cslow
  hCold : κc.Cold ≤ ENNReal.ofReal Cold
  hCslow : κc.Cslow ≤ ENNReal.ofReal Cslow
  hs : Cold / Δ + 2 * Real.pi + Cslow / Δ + 12 / (bw * Δ) ≤ (s : ℝ)
  hS : Cslow / Δ ≤ (S : ℝ)
  hWr0 : 0 ≤ Wr
  hWr : wsum (3 * Real.pi * bw) Lstar (expProfile 1 a) ≤ ENNReal.ofReal Wr

/-- **The cost of one label derivative.** -/
theorem diag_sigma {bw : ℝ} {Lstar : ℕ} {κc : MajConsts} {N p : ℕ} {Δ a a₀ : ℝ} {L₀ : ℕ}
    {s Wg Wc Wl Kg Kd S : ℝ≥0} {Wr Cold Cslow : ℝ}
    (hC : DiagConsts bw Lstar κc N p Δ a a₀ L₀ s Wg Wc Wl Kg Kd S Wr Cold Cslow) (hb : 0 < bw)
    {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) (hρε : ρ ≤ ε) :
    κc.Cold / ENNReal.ofReal (ε * Δ) + ENNReal.ofReal (2 * Real.pi / ε) ≤
        ((s * (Real.toNNReal ε)⁻¹ : ℝ≥0) : ℝ≥0∞) ∧
      κc.Cslow / ENNReal.ofReal (ε * Δ) ≤ ((s * (Real.toNNReal ε)⁻¹ : ℝ≥0) : ℝ≥0∞) ∧
      ENNReal.ofReal (12 / bw) / ENNReal.ofReal (ε * Δ) ≤
        ((s * (Real.toNNReal ε)⁻¹ : ℝ≥0) : ℝ≥0∞) ∧
      s * (Real.toNNReal ε)⁻¹ * Real.toNNReal ρ ≤ s ∧
      ENNReal.ofReal |ρ| * (κc.Cslow / ENNReal.ofReal (ε * Δ)) ≤ (S : ℝ≥0∞) := by
  have hΔ := hC.hΔ
  have hεΔ : 0 < ε * Δ := mul_pos hε hΔ
  have hσ : ((s * (Real.toNNReal ε)⁻¹ : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal ((s : ℝ) / ε) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
    push_cast
    rw [Real.coe_toNNReal _ hε.le, div_eq_mul_inv]
  have hdiv : ∀ {x : ℝ≥0∞} {c : ℝ}, x ≤ ENNReal.ofReal c → 0 ≤ c →
      x / ENNReal.ofReal (ε * Δ) ≤ ENNReal.ofReal (c / (ε * Δ)) := by
    intro x c hx hc
    rw [ENNReal.ofReal_div_of_pos hεΔ]
    exact ENNReal.div_le_div_right hx _
  have hs := hC.hs
  have h12 : 0 ≤ 12 / bw := by positivity
  have hπ : 0 ≤ 2 * Real.pi := by positivity
  have hCo : 0 ≤ Cold / Δ := div_nonneg hC.hCold0 hΔ.le
  have hCs : 0 ≤ Cslow / Δ := div_nonneg hC.hCslow0 hΔ.le
  have hb12 : 12 / (bw * Δ) = 12 / bw / Δ := by rw [div_div]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hσ]
    refine (add_le_add (hdiv hC.hCold hC.hCold0) le_rfl).trans ?_
    rw [← ENNReal.ofReal_add (div_nonneg hC.hCold0 hεΔ.le) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have e : Cold / (ε * Δ) + 2 * Real.pi / ε = (Cold / Δ + 2 * Real.pi) / ε := by
      field_simp
    rw [e]
    refine div_le_div_of_nonneg_right ?_ hε.le
    have : 0 ≤ 12 / (bw * Δ) := by positivity
    linarith
  · rw [hσ]
    refine (hdiv hC.hCslow hC.hCslow0).trans (ENNReal.ofReal_le_ofReal ?_)
    have e : Cslow / (ε * Δ) = Cslow / Δ / ε := by field_simp
    rw [e]
    refine div_le_div_of_nonneg_right ?_ hε.le
    have : 0 ≤ 12 / (bw * Δ) := by positivity
    linarith
  · rw [hσ]
    refine (hdiv le_rfl h12).trans (ENNReal.ofReal_le_ofReal ?_)
    have e : 12 / bw / (ε * Δ) = 12 / (bw * Δ) / ε := by field_simp
    rw [e]
    refine div_le_div_of_nonneg_right ?_ hε.le
    linarith
  · rw [← NNReal.coe_le_coe]
    push_cast
    rw [Real.coe_toNNReal _ hε.le, Real.coe_toNNReal _ hρ.le]
    calc (s : ℝ) * ε⁻¹ * ρ = (s : ℝ) * (ρ / ε) := by ring
      _ ≤ (s : ℝ) * 1 := mul_le_mul_of_nonneg_left ((div_le_one hε).mpr hρε) s.2
      _ = s := mul_one _
  · rw [abs_of_pos hρ]
    calc ENNReal.ofReal ρ * (κc.Cslow / ENNReal.ofReal (ε * Δ))
        ≤ ENNReal.ofReal ρ * ENNReal.ofReal (Cslow / (ε * Δ)) :=
          mul_le_mul' le_rfl (hdiv hC.hCslow hC.hCslow0)
      _ = ENNReal.ofReal (ρ * (Cslow / (ε * Δ))) := (ENNReal.ofReal_mul hρ.le).symm
      _ ≤ ENNReal.ofReal (S : ℝ) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have e : ρ * (Cslow / (ε * Δ)) = ρ / ε * (Cslow / Δ) := by field_simp
          rw [e]
          calc ρ / ε * (Cslow / Δ) ≤ 1 * (Cslow / Δ) :=
                mul_le_mul_of_nonneg_right ((div_le_one hε).mpr hρε) hCs
            _ ≤ S := by rw [one_mul]; exact hC.hS
      _ = (S : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal

/-! ### The level-free constant of the first source -/

/-- The constant of the commutator arrays per unit. -/
def diagKJ (p : ℕ) (Wg : ℝ≥0) (Cu Ca : ℝ) : ℝ≥0 :=
  4 * 2 ^ (4 * p) * compC (invP Wg (4 * p)) (4 * p) * Wg * Real.toNNReal Cu * Real.toNNReal Ca

/-- The constant of the mean arrays of the degree `n ≥ 3` per unit. -/
def diagKn (X0 : GCtx) (Dm p n : ℕ) (s : ℝ≥0) (Cu : ℝ) : ℝ≥0 :=
  chartK (2 * p) n (invP X0.Kg (2 * p)) (s + 2 ^ (2 * p + n) * X0.Kg) *
    (compC (invP X0.Kg (2 * p)) (2 * p) * X0.Kg *
      (Real.toNNReal (Cu ^ (n - 2)) * UEnv.fluxXc X0 Dm (liftB X0 Dm) 0 n))

/-- The constant of the assembled mean arrays per unit. -/
def diagKF (X0 : GCtx) (Dm N p : ℕ) (s Wl Wc : ℝ≥0) (Cu Cd Cown : ℝ) : ℝ≥0 :=
  Wl * (compC (invP 2 (2 * p)) (2 * p) * 16 * Real.toNNReal (14 * (Cd ^ 2 + 1)) *
      Real.toNNReal Cown) +
    ∑ n ∈ Finset.Icc 3 (N + 1), Wc * diagKn X0 Dm p n s Cu

/-- **The level-free constant of the first source.** -/
def diagKfs (X0 : GCtx) (Dm N p : ℕ) (s Wg Wl Wc : ℝ≥0) (Cu Ca Cd Cown : ℝ) : ℝ≥0 :=
  fC N p s Wg (Real.toNNReal Cu) * (diagKJ p Wg Cu Ca * wE p s (Real.toNNReal Cu) +
    diagKF X0 Dm N p s Wl Wc Cu Cd Cown * wP N p s (Real.toNNReal Cu))

/-- **The threshold of `C_w` for the ledger of the first source.** -/
def diagThr (X0 : GCtx) (Dm N p : ℕ) (s Wg Wl Wc : ℝ≥0) (Cu Ca Cd Cown Wr cr : ℝ) : ℝ :=
  2 ^ (N + 1 + 4 * p) * Wr * cr⁻¹ ^ (N + 1 + 4 * p - 2) *
    (diagKfs X0 Dm N p s Wg Wl Wc Cu Ca Cd Cown : ℝ)

/-! ### The record bound -/

/-- **The record bound of the witnesses of the first source.** -/
theorem diag_record_le {ε cr ρ κ Wr K F Cw η δ : ℝ} {d Dmax : ℕ} (hd2 : 2 ≤ d)
    (hdD : d ≤ Dmax) (hε : 0 < ε) (hcr0 : 0 < cr) (hcr1 : cr ≤ 1) (hρ : 0 < ρ) (hκ : 0 < κ)
    (hWr : 0 ≤ Wr) (hK0 : 0 ≤ K) (hF : F * ρ ≤ K * (κ * ε ^ δ))
    (hthr : 2 ^ Dmax * Wr * cr⁻¹ ^ (Dmax - 2) * K ≤ Cw) :
    (ε / (cr * ρ)) ^ (d - 2) * ∑ _α : DerivativeWord2 (d - 1), ∑ _c : Fin 2,
        Wr * (|ε ^ (-η) * (κ * ε ^ (d - 2))⁻¹| * (F * ρ ^ (d - 1))) ≤ Cw * ε ^ (δ - η) := by
  have hA : 0 < ε ^ (-η) := Real.rpow_pos_of_pos hε _
  have hB : 0 < ε ^ δ := Real.rpow_pos_of_pos hε _
  have hrw : ε ^ (δ - η) = ε ^ δ * ε ^ (-η) := by rw [sub_eq_add_neg, Real.rpow_add hε]
  obtain ⟨j, rfl⟩ : ∃ j, d = j + 2 := ⟨d - 2, by omega⟩
  have hj1 : j + 2 - 1 = j + 1 := by omega
  have hj2 : j + 2 - 2 = j := by omega
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Finset.prod_const,
    Fintype.card_fin, nsmul_eq_mul, hj1, hj2, Nat.cast_pow, Nat.cast_ofNat]
  have hεj : 0 < ε ^ j := pow_pos hε j
  have hρj : 0 < ρ ^ j := pow_pos hρ j
  have hcrinv : 1 ≤ cr⁻¹ := one_le_inv_iff₀.mpr ⟨hcr0, hcr1⟩
  rw [abs_of_pos (mul_pos hA (inv_pos.mpr (mul_pos hκ hεj)))]
  have e1 : (ε / (cr * ρ)) ^ j * ((2 : ℝ) ^ (j + 1) * (2 * (Wr * (ε ^ (-η) * (κ * ε ^ j)⁻¹ *
      (F * ρ ^ (j + 1)))))) = 2 ^ (j + 2) * Wr * ε ^ (-η) * (F * ρ) * κ⁻¹ * (cr ^ j)⁻¹ := by
    rw [div_pow, mul_pow]
    field_simp
    ring
  rw [e1, hrw, ← inv_pow]
  have h2 : (2 : ℝ) ^ (j + 2) ≤ 2 ^ Dmax := pow_le_pow_right₀ one_le_two hdD
  have hcr : cr⁻¹ ^ j ≤ cr⁻¹ ^ (Dmax - 2) := pow_le_pow_right₀ hcrinv (by omega)
  have hκκ : κ * κ⁻¹ = 1 := mul_inv_cancel₀ hκ.ne'
  calc 2 ^ (j + 2) * Wr * ε ^ (-η) * (F * ρ) * κ⁻¹ * cr⁻¹ ^ j
      ≤ 2 ^ (j + 2) * Wr * ε ^ (-η) * (K * (κ * ε ^ δ)) * κ⁻¹ * cr⁻¹ ^ j := by gcongr
    _ = 2 ^ (j + 2) * Wr * cr⁻¹ ^ j * K * (ε ^ δ * ε ^ (-η)) := by
        rw [show 2 ^ (j + 2) * Wr * ε ^ (-η) * (K * (κ * ε ^ δ)) * κ⁻¹ * cr⁻¹ ^ j =
          2 ^ (j + 2) * Wr * cr⁻¹ ^ j * K * (ε ^ δ * ε ^ (-η)) * (κ * κ⁻¹) by ring, hκκ, mul_one]
    _ ≤ 2 ^ Dmax * Wr * cr⁻¹ ^ (Dmax - 2) * K * (ε ^ δ * ε ^ (-η)) := by gcongr
    _ ≤ Cw * (ε ^ δ * ε ^ (-η)) := mul_le_mul_of_nonneg_right hthr (by positivity)

/-! ### The unit bound of the first source -/

/-- **The mean arrays of the degree `n ≥ 3` at the length `ρ`.** -/
theorem childK_mul_le (D : OCData) (X0 : GCtx) (Dm m : ℕ) {ρ : ℝ} (hρ : 0 < ρ)
    (hc : 0 < D.cellScaleSq m) {n p : ℕ} (hn : 3 ≤ n) (s : ℝ≥0)
    (hDst : ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) ^ 2 = D.kap (m - 1) * D.cellScaleSq m)
    (hD0 : 0 ≤ ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1))) {Cu E δ : ℝ}
    (hDρ : ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) / ρ ≤ Cu * E ^ (3 * δ)) (hCu : 1 ≤ Cu)
    (hE0 : 0 < E) (hE1 : E ≤ 1) (hδ : 0 ≤ δ) (hκ : 0 ≤ D.kap (m - 1)) :
    childK D X0 Dm m ρ n (2 * p) s * Real.toNNReal ρ ≤
      diagKn X0 Dm p n s Cu * Real.toNNReal (D.kap (m - 1) * E ^ δ) := by
  have hpm0 : 0 ≤ LiftGenSetup.pmC D m ρ n := by
    unfold LiftGenSetup.pmC
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hc.le) (pow_nonneg (div_nonneg hD0 hρ.le) n))
      hρ.le
  have hpm : Real.toNNReal (LiftGenSetup.pmC D m ρ n) * Real.toNNReal ρ ≤
      Real.toNNReal (Cu ^ (n - 2)) * Real.toNNReal (D.kap (m - 1) * E ^ δ) := by
    rw [← Real.toNNReal_mul hpm0, ← Real.toNNReal_mul (pow_nonneg (by linarith) _)]
    refine Real.toNNReal_le_toNNReal ?_
    rw [pmC_mul_eq D m hρ.ne' hc.ne' (by omega) hDst]
    exact pmC_mul_le hn (div_nonneg hD0 hρ.le) hDρ hCu hE0 hE1 hδ hκ
  unfold childK diagKn
  calc chartK (2 * p) n (invP X0.Kg (2 * p)) (s + 2 ^ (2 * p + n) * X0.Kg) *
        (compC (invP X0.Kg (2 * p)) (2 * p) * X0.Kg *
          (Real.toNNReal (LiftGenSetup.pmC D m ρ n) * UEnv.fluxXc X0 Dm (liftB X0 Dm) 0 n)) *
        Real.toNNReal ρ
      = chartK (2 * p) n (invP X0.Kg (2 * p)) (s + 2 ^ (2 * p + n) * X0.Kg) *
          (compC (invP X0.Kg (2 * p)) (2 * p) * X0.Kg *
            ((Real.toNNReal (LiftGenSetup.pmC D m ρ n) * Real.toNNReal ρ) *
              UEnv.fluxXc X0 Dm (liftB X0 Dm) 0 n)) := by ring
    _ ≤ chartK (2 * p) n (invP X0.Kg (2 * p)) (s + 2 ^ (2 * p + n) * X0.Kg) *
          (compC (invP X0.Kg (2 * p)) (2 * p) * X0.Kg *
            ((Real.toNNReal (Cu ^ (n - 2)) * Real.toNNReal (D.kap (m - 1) * E ^ δ)) *
              UEnv.fluxXc X0 Dm (liftB X0 Dm) 0 n)) := by gcongr
    _ = _ := by ring

/-- **The constant of the first source at the length `ρ` is at most `diagKfs` units**
`κ_i E^δ`. -/
theorem fsK_diag_le (D : OCData) (i : ℕ) {X' : GCtx} {κc : MajConsts} {S Kg Kd : ℝ≥0}
    (hX : SameConsts X' (constCtx κc S Kg Kd)) (Dm N p : ℕ)
    (s Wg Wl Wc : ℝ≥0) {ρ τ Cu Ca Cd Cown E δ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ^ 2 = D.kap i * τ)
    (hκ : 0 ≤ D.kap i) (hCa : 0 ≤ Ca) (hCown : 0 ≤ Cown) (hE0 : 0 < E) (hE1 : E ≤ 1) (hδ : 0 ≤ δ)
    (haτ : ocA D.α D.q D.Λ i * τ ≤ Ca * E ^ δ) (hown : ownSize D (i + 1) ≤ Cown * E ^ δ)
    (hc : 0 < D.cellScaleSq (i + 1))
    (hDst : ocDStar D.q D.Λ (i + 1) (D.kap (i + 1)) (D.kap (i + 1 - 1)) ^ 2 =
      D.kap (i + 1 - 1) * D.cellScaleSq (i + 1))
    (hD0 : 0 ≤ ocDStar D.q D.Λ (i + 1) (D.kap (i + 1)) (D.kap (i + 1 - 1)))
    (hDρ : ocDStar D.q D.Λ (i + 1) (D.kap (i + 1)) (D.kap (i + 1 - 1)) / ρ ≤ Cu * E ^ (3 * δ))
    (hCu : 1 ≤ Cu) (hΛ : 1 ≤ D.Λ) :
    fsK N p s Wg (Real.toNNReal Cu)
        (jhK (4 * p) Wg (Real.toNNReal (ocA D.α D.q D.Λ i)) (Real.toNNReal Cu) (Real.toNNReal ρ))
        (dfK D X' Dm i ρ N p s (Wl * bleafK D i p Cd * (Real.toNNReal ρ)⁻¹) Wc) *
        Real.toNNReal ρ ≤
      diagKfs (constCtx κc S Kg Kd) Dm N p s Wg Wl Wc Cu Ca Cd Cown *
        Real.toNNReal (D.kap i * E ^ δ) := by
  have hw : Real.toNNReal ρ ≠ 0 := (Real.toNNReal_pos.mpr hρ).ne'
  have hEd : 0 ≤ E ^ δ := Real.rpow_nonneg hE0.le _
  have hA : 0 ≤ ocA D.α D.q D.Λ i :=
    (Real.rpow_pos_of_pos (AVRegularity.Construction.Stream.ocEpsilon_pos hΛ) _).le
  refine fsK_mul_le ?_ ?_
  · refine (jhK_mul_le (4 * p) Wg (Real.toNNReal Cu) hA hρ.le hρ2 hκ hCa hEd haτ).trans
      (le_of_eq ?_)
    unfold diagKJ
    ring
  · unfold dfK diagKF
    rw [add_mul, Finset.sum_mul, add_mul, Finset.sum_mul]
    refine add_le_add ?_ (Finset.sum_le_sum fun n hn => ?_)
    · rw [mul_assoc, inv_mul_cancel₀ hw, mul_one, mul_assoc]
      exact mul_le_mul' le_rfl (bleafK_le D i p Cd hown hκ hCown)
    · have hn3 := (Finset.mem_Icc.mp hn).1
      rw [childK_congr hX, mul_assoc, mul_assoc]
      refine mul_le_mul' le_rfl ?_
      have h := childK_mul_le D (constCtx κc S Kg Kd) Dm (i + 1) hρ hc hn3 s (p := p) hDst
        hD0 hDρ hCu hE0 hE1 hδ (by rw [Nat.add_sub_cancel]; exact hκ)
      rw [Nat.add_sub_cancel] at h
      exact h
end

/-! **Ledger, first source: the constants exist.**
* `exists_diagConsts`: the constants `DiagConsts` of the ledger of the first source exist for
  finite, decaying carrier constants (`MajOK`), with the outer rate `9πb/2`, the inner rate `3πb`
  and the fast-weight budget `fsR N p (2N + 1) + N + 1`;
* `exists_diagScales`: the scale facts of the first source with one constant for every passage of
  the band chain, from the diffusivity ledger (`bandChain_uniform_ledger`):
  `a_{m-1} τ''_m ≤ C_a ε_{m-1}^δ` and `ownSize m ≤ chainK (6/5) C_a ε_{m-1}^δ`. -/

section
open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant AVRegularity.Providers.ComplexContext
  AVRegularity.Providers.ComplexFlow

/-- **The constants of the ledger of the first source exist.** -/
theorem exists_diagConsts {bw : ℝ} (hb : 0 < bw) {κ : MajConsts} (hκ : MajOK bw κ)
    (Lstar N p : ℕ) {Δ : ℝ} (hΔ : 0 < Δ) :
    ∃ (a a₀ : ℝ) (L₀ : ℕ) (s Wg Wc Wl Kg Kd S : ℝ≥0) (Wr Cold Cslow : ℝ),
      DiagConsts bw Lstar κ N p Δ a a₀ L₀ s Wg Wc Wl Kg Kd S Wr Cold Cslow := by
  have hπb : 0 < Real.pi * bw := mul_pos Real.pi_pos hb
  have ha3 : 3 * Real.pi * bw < 9 / 2 * Real.pi * bw := by nlinarith
  have ha6 : 9 / 2 * Real.pi * bw < 6 * Real.pi * bw := by nlinarith
  have h36 : 3 * Real.pi * bw < 6 * Real.pi * bw := by nlinarith
  obtain ⟨Wr, hWr0, hWr⟩ := ledgerWeight_le ha3 Lstar
  obtain ⟨C, hg, hd, hc, hCo, hCs⟩ := hκ
  set L₀ := fsR N p (2 * N + 1) + N + 1 with hL₀
  have hA := wsum_expProfile_lt_top ha6 L₀ C
  have hA0 := wsum_expProfile_lt_top h36 L₀ C
  have hA1 := wsum_expProfile_lt_top ha6 L₀ 1
  refine ⟨9 / 2 * Real.pi * bw, 3 * Real.pi * bw, L₀,
    Real.toNNReal (κ.Cold.toReal / Δ + 2 * Real.pi + κ.Cslow.toReal / Δ + 12 / (bw * Δ)),
    (wsum (9 / 2 * Real.pi * bw) L₀ (expProfile C (6 * Real.pi * bw))).toNNReal,
    (wsum (9 / 2 * Real.pi * bw) L₀ (expProfile C (6 * Real.pi * bw))).toNNReal,
    (wsum (9 / 2 * Real.pi * bw) L₀ (expProfile 1 (6 * Real.pi * bw))).toNNReal,
    (wsum (3 * Real.pi * bw) L₀ (expProfile C (6 * Real.pi * bw))).toNNReal,
    (wsum (3 * Real.pi * bw) L₀ (expProfile C (6 * Real.pi * bw))).toNNReal,
    Real.toNNReal (κ.Cslow.toReal / Δ), Wr, κ.Cold.toReal, κ.Cslow.toReal,
    ⟨hΔ, ha3, by positivity, by omega, by omega, fun L hL => ?_, fun L hL => ?_, fun L hL => ?_,
      fun L hL => ?_, fun k L hL => ?_, ENNReal.toReal_nonneg, ENNReal.toReal_nonneg,
      (ENNReal.ofReal_toReal hCo).ge, (ENNReal.ofReal_toReal hCs).ge, Real.le_coe_toNNReal _,
      Real.le_coe_toNNReal _, hWr0, hWr⟩⟩
  · rw [ENNReal.coe_toNNReal hA.ne]
    exact iSup₂_le fun fr Lt => (wsum_mono fun h => hg fr Lt h).trans
      (wsum_mono_weight le_rfl hL _)
  · rw [ENNReal.coe_toNNReal hA.ne]
    exact (wsum_mono fun h => hc h).trans (wsum_mono_weight le_rfl hL _)
  · rw [ENNReal.coe_toNNReal hA1.ne]
    refine (wsum_mono fun h => le_of_eq ?_).trans (wsum_mono_weight le_rfl hL _)
    simp only [expProfile, one_mul]
  · rw [ENNReal.coe_toNNReal hA0.ne]
    exact iSup₂_le fun fr Lt => (wsum_mono fun h => hg fr Lt h).trans
      (wsum_mono_weight le_rfl hL _)
  · rw [ENNReal.coe_toNNReal hA0.ne]
    exact (wsum_mono fun h => hd k h).trans (wsum_mono_weight le_rfl hL _)

/-- **The scale facts of the first source** with one constant for every passage. -/
theorem exists_diagScales {α s q : ℝ} (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s)
    (hs1 : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Ca : ℝ, 0 ≤ Ca ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ D : OCData, D.α = α → D.q = q → D.ζ = ζ →
      Λ₀ ≤ D.Λ → IsOCBandChain α q D.Λ ζ D.term D.κ →
      ∀ m : ℕ, 2 ≤ m → m ≤ D.term →
        ocA D.α D.q D.Λ (m - 1) * ocTauPP D.α D.q D.Λ m ≤ Ca * D.eps (m - 1) ^ ocDelta D.α D.q ∧
        ownSize D m ≤ chainK * (6 / 5) * Ca * D.eps (m - 1) ^ ocDelta D.α D.q := by
  obtain ⟨C, hC, Λ₁, hΛ₁, hled⟩ := CycleReference.bandChain_uniform_ledger hα0 hα1 hs0 hs1 hq hζ
  have hδ : 0 < ocDelta α q := ocDelta_pos_of_admissible hα0 hq
  refine ⟨C, by linarith, Λ₁, hΛ₁, fun D hDα hDq hDζ hΛ hκ m hm hmM => ?_⟩
  subst hDα hDq hDζ
  have hΛ1 : 1 ≤ D.Λ := by omega
  obtain ⟨-, h2⟩ := hled D.Λ hΛ D.term (by omega) D.κ hκ
  have hAτ := (h2 m hm hmM (D.κ m) (D.κ (m - 1)) rfl rfl).2.2.2.2.2.2.2.2.2.2.2.2.1
  have hε : 0 < ocEpsilon D.q D.Λ (m - 1) := Construction.Stream.ocEpsilon_pos hΛ1
  have hε1 : ocEpsilon D.q D.Λ (m - 1) ≤ 1 := ocEpsilon_le_one hΛ1 _
  have h2δ : ocEpsilon D.q D.Λ (m - 1) ^ (2 * ocDelta D.α D.q) ≤
      ocEpsilon D.q D.Λ (m - 1) ^ ocDelta D.α D.q :=
    Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)
  have hA : ocA D.α D.q D.Λ (m - 1) * ocTauPP D.α D.q D.Λ m ≤
      C * D.eps (m - 1) ^ ocDelta D.α D.q :=
    hAτ.trans (mul_le_mul_of_nonneg_left h2δ (by linarith))
  refine ⟨hA, ?_⟩
  unfold ownSize
  have hK : (0 : ℝ) ≤ chainK * (6 / 5) := by unfold chainK; norm_num
  calc chainK * ocA D.α D.q D.Λ (m - 1) * (6 / 5 * ocTauPP D.α D.q D.Λ m)
      = chainK * (6 / 5) * (ocA D.α D.q D.Λ (m - 1) * ocTauPP D.α D.q D.Λ m) := by ring
    _ ≤ chainK * (6 / 5) * (C * D.eps (m - 1) ^ ocDelta D.α D.q) :=
        mul_le_mul_of_nonneg_left hA hK
    _ = chainK * (6 / 5) * C * D.eps (m - 1) ^ ocDelta D.α D.q := by ring
end

/-! **Ledger: the ledger of the first source** (conditional helper `diag_ledger_case`). For the
new identity `γ'` of `G'` whose source is the first source `𝖣` of the level `m = G.level`
(provenance `.letter m .diag []`), with the coefficients of `IsActualSuccessor` (the factor
`λ_d = ε_{m-1}^{-η₀} (κ_{m-1} ε_{m-1}^{d-2})⁻¹`) and the grade-zero lifts, the witnesses
`θ(d, α, c) = W_r |λ_d| fsK ρ^{d-1}` satisfy the conclusion of `successor_ledger`:
* the expressions are `λ_d ·` the sized context expressions of the slots
  (`slot_firstSource_ctxAlgQ`), generated, with the certified leaf map `bleaf` of the bridge
  leaves (`leavesCertified_bleaf`), and no uncertified solved node;
* the ledger sum is at most `W_r |λ_d| fsK ρ^{d-1}` (`ledgerSum_le`) at the reserve of the target
  component;
* the record bound holds with the record `(N + 1 + 4p, c_r ρ, C_w ε_{m-1}^{δ-η₀})` of the tags
  as soon as `diagThr ≤ C_w` (`diag_record_le`, `fsK_diag_le`).

Hypotheses beyond the passage (`StepFacts`): the chain environment (`ChainEnv`), the lift reserves
`max (N + 1) (2p) + D_m + 2 ≤ sX, sZ`, the coercivity bound
`ownSize m ≤ 1/100`, the scale facts `a_{m-1} τ''_m ≤ C_a ε_{m-1}^δ`,
`ownSize m ≤ C_own ε_{m-1}^δ`, the drift bound `ε_m^{1+α} ≤ C_d √(κ_m κ_{m-1})`, the constants
`DiagConsts`, a nonnegative reserve of the target component within the budget, and the threshold. -/

section
open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant AVRegularity.Providers.ComplexContext
  AVRegularity.Providers.ComplexFlow

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {kI : InvConsts}

open scoped Classical in
/-- **The ledger of the first source.** -/
theorem diag_ledger_case {Cw cr σ₀ η₀ Cu : ℝ} {N p : ℕ} {G G' : GenStage D hr Dm b j₀}
    (hF : StepFacts kI G G' (succProvParams D Cw cr σ₀ η₀ N p) Cu)
    {CH Υ : ℝ} (env : ChainEnv D b CH Υ j₀) (hij : j₀ ≤ G'.level)
    {v' u' : CompIn G'.comps} (γ' : G'.fam.Γ v' u')
    (hprov : G'.prov v' u' γ' = .letter G.level .diag [])
    (hN : 1 ≤ N) {sX sZ : ℕ}
    (hsX : max (N + 1) (2 * p) + Dm + 2 ≤ sX) (hsZ : max (N + 1) (2 * p) + Dm + 2 ≤ sZ)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (hDL : ∀ (k : ℤ) (A : RealChain), Odd k → IsAdmissibleChain D b j₀ G.level k A →
      IsLiftSequence (diagQ D Dm G.level k A (liftLength D G.level)) sX sZ
        (liftT0 D G.level k) (liftT1 D G.level k) N 0 (Cc0 k A))
    (hflux : ∀ (q : OddSlot) (ctx : StageCtx D b j₀ G'.level q) (d : ℕ)
      (I : DerivativeWord2 (d - 1)) (t : ℝ) (X z : Vec 2), 2 ≤ d →
      G'.fam.flux q ctx v' u' γ' d I t X z =
        if IsAdmissibleChain D b j₀ G'.level q.1 (ctx.1.recenter D (D.eps (G'.level - 1) • X))
        then (D.eps (G.level - 1) ^ (-η₀) * (D.κ G'.level * D.eps G'.level ^ (d - 2))⁻¹) •
          fluxCoeff (firstSourceFlux D b j₀ Dm G.level (liftLength D G.level) N p 0 Cc0 t
            (ctx.1.recenter D (D.eps (G'.level - 1) • X)) z) d I 0
        else 0)
    (hm : ownSize D G.level ≤ 1 / 100) {Ca Cown Cd : ℝ} (hCa : 0 ≤ Ca) (hCown : 0 ≤ Cown)
    (haτ : ocA D.α D.q D.Λ G'.level * ocTauPP D.α D.q D.Λ G.level ≤
      Ca * D.eps G'.level ^ ocDelta D.α D.q)
    (hown : ownSize D G.level ≤ Cown * D.eps G'.level ^ ocDelta D.α D.q)
    (hCd : D.eps G.level ^ (1 + D.α) ≤ Cd * Real.sqrt (D.kap G.level * D.kap G'.level))
    (κc : MajConsts) {Δ a a₀ : ℝ} {L₀ : ℕ} {s Wg Wc Wl Kg Kd S : ℝ≥0} {Wr Cold Cslow : ℝ}
    (hC : DiagConsts b kI.Lstar κc N p Δ a a₀ L₀ s Wg Wc Wl Kg Kd S Wr Cold Cslow)
    (hres0 : 0 ≤ compReserve kI v'.1)
    (hresΔ : compReserve kI v'.1 + ((fsR N p (2 * N + 1) : ℕ) : ℝ) * Δ ≤ 2)
    (hcr0 : 0 < cr) (hcr1 : cr ≤ 1)
    (hthr : diagThr (constCtx κc S Kg Kd) Dm N p s Wg Wl Wc Cu Ca Cd Cown Wr cr ≤ Cw) :
    LedgerConcl kI κc G' v' u' γ' := by
  have hlev : G.level = G'.level + 1 := hF.hlev
  rw [hlev] at hprov hDL hflux hm haτ hown hCd
  have hsc : PassScales D (G'.level + 1) Cu := hlev ▸ hF.hsc
  set i := G'.level with hi
  have hΛ := hF.hΛ1
  have hε : 0 < D.eps i := hF.hεpos i
  have hε1 : D.eps i ≤ 1 := hF.hεle i
  have hδ : 0 < ocDelta D.α D.q := hF.hδ
  have hκm : D.kap (i + 1) = D.κ (i + 1) := hsc.hκm
  have hκi : D.kap i = D.κ i := by simpa only [Nat.add_sub_cancel] using hsc.hκm'
  have hκ0 : 0 < D.kap i := by simpa only [Nat.add_sub_cancel] using hsc.hκ1
  have hκle : D.kap (i + 1) ≤ D.kap i := by simpa only [Nat.add_sub_cancel] using hsc.hκle
  set ρ := liftLength D (i + 1) with hρdef
  have hρ : 0 < ρ := hsc.hρ0
  have hρε : ρ ≤ D.eps i := by simpa only [Nat.add_sub_cancel] using hsc.hρE
  have hc : 0 < D.cellScaleSq (i + 1) :=
    EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hF.hζ hF.hκb _
  have hw : Real.toNNReal ρ ≠ 0 := (Real.toNNReal_pos.mpr hρ).ne'
  -- the cost of one label derivative
  obtain ⟨hσc, hσf, hσl, hσw, hSl⟩ := diag_sigma hC hF.hb hε hρ hρε
  set σ := s * (Real.toNNReal (D.eps i))⁻¹ with hσdef
  -- the constants
  set KB := bleafK D i p Cd with hKB
  set cB := Wl * KB * (Real.toNNReal ρ)⁻¹ with hcBdef
  have hcB : Wl * KB ≤ cB * Real.toNNReal ρ :=
    le_of_eq (by rw [hcBdef, mul_assoc (Wl * KB), inv_mul_cancel₀ hw, mul_one])
  have hCu0 : 0 ≤ Cu := le_trans zero_le_one hF.hCu
  have hcov : ∀ t a b, |covMat D (i + 1) 0 t a b| ≤
      ((Real.toNNReal Cu * Real.toNNReal ρ ^ 2 : ℝ≥0) : ℝ) := by
    intro t a b
    have h := hsc.hH t a b
    simp only [Nat.add_sub_cancel] at h
    push_cast
    rw [Real.coe_toNNReal _ hCu0, Real.coe_toNNReal _ hρ.le]
    have hE : D.eps i ^ ocDelta D.α D.q ≤ 1 := Real.rpow_le_one hε.le hε1 hδ.le
    calc |covMat D (i + 1) 0 t a b| ≤ Cu * D.eps i ^ ocDelta D.α D.q * ρ ^ 2 := h
      _ ≤ Cu * 1 * ρ ^ 2 := by gcongr
      _ = Cu * ρ ^ 2 := by ring
  -- the reserves
  have hR1 : N + 1 + Dm + 2 ≤ min sX sZ := by
    have := le_max_left (N + 1) (2 * p)
    exact le_min (by omega) (by omega)
  have hR2 : 2 * p + Dm + 2 ≤ min sX sZ := by
    have := le_max_right (N + 1) (2 * p)
    exact le_min (by omega) (by omega)
  -- the slot expressions
  have hslot := fun (pc : OddSlot) (d : ℕ) (I : DerivativeWord2 (d - 1)) (c : Fin 2) =>
    slot_firstSource_ctxAlgQ (𝒮 := G.exports) env hF.hκb hρ hN (min_le_left sX sZ)
      (min_le_right sX sZ) hR1 hR2 hsc.hDst hκm hκi hκle Cc0 hDL κc hC.hΔ hC.hLN hσc hσf hσw
      hC.hWg hC.hWc hC.hWl hC.hKg hC.hKd hSl hcov hcB pc d I c
  set X := diagX D b j₀ G.exports i (2 * p) κc Δ a a₀ L₀ σ KB with hXdef
  have hX : X.Ok := diagX_ok hC.hΔ.le
  set F := fsK N p s Wg (Real.toNNReal Cu)
    (jhK (4 * p) Wg (Real.toNNReal (ocA D.α D.q D.Λ i)) (Real.toNNReal Cu) (Real.toNNReal ρ))
    (dfK D (X.toG S Kg Kd) Dm i ρ N p s cB Wc) with hFdef
  set lamd : ℕ → ℝ := fun d => D.eps i ^ (-η₀) * (D.κ i * D.eps i ^ (d - 2))⁻¹ with hlamd
  -- the leaf map is certified
  have hstart := hF.hstart
  have hNR : N + Dm + 2 ≤ min sX sZ := by omega
  have hLC : LeavesCertified D b j₀ X.leaf := by
    have hB := fun pc : OddSlot => bridgeCtx_of hΛ hF.hζ hF.hκb hF.hb hstart G.exports hρ.ne' hN
      (min_le_left sX sZ) (min_le_right sX sZ) hNR hsc.hDst Cc0 hDL pc.1
    exact leavesCertified_bleaf env hij hF.hexpU hm hCd hc hκm hκle hC.hΔ le_rfl hσl
      (by omega) (by omega) _ _ _ hB fun x => exists_leafRep hΛ hF.hζ hF.hκb hF.hb hstart
        G.exports hρ.ne' hN (min_le_left sX sZ) (min_le_right sX sZ) hNR hsc.hDst Cc0 hDL hκm x.1.1
        x.2.1 x.2.2.1 (by have := Nat.lt_succ_iff.mp x.2.2.2.1.2; omega) (by omega) x.2.2.2.2
  have ha0 : 0 ≤ a := by have := mul_pos Real.pi_pos hF.hb; linarith [hC.ha3]
  refine ⟨fun d _ _ => Wr * (|lamd d| * ((F * Real.toNNReal ρ ^ (d - 1) : ℝ≥0) : ℝ)),
    fun d _ _ => mul_nonneg hC.hWr0 (mul_nonneg (abs_nonneg _) (NNReal.coe_nonneg _)),
    fun d hd hdD => ?_, fun d I c => ?_⟩
  · -- the record bound
    obtain ⟨hm', ho'⟩ := hF.hGT' v' u' γ'
    rw [hprov] at hm' ho'
    obtain ⟨h1, h2, h3⟩ := Prov.tags_letter (succProvParams D Cw cr σ₀ η₀ N p) (i + 1) .diag []
    rw [ho', h1] at hdD
    rw [hm'.1, hm'.2.2.2.1, h2, h3]
    simp only [succProvParams, Prov.pathTags, List.map_nil, List.prod_nil, mul_one, one_mul,
      letterOrder, freshLength, Nat.add_sub_cancel] at hdD ⊢
    have hρeq : cr * Real.sqrt (D.κ i * ocTauPP D.α D.q D.Λ (i + 1)) = cr * ρ := by
      rw [hρdef, liftLength, Nat.add_sub_cancel]
    rw [hρeq]
    have hFb := fsK_diag_le D i (X' := X.toG S Kg Kd) (κc := κc) ⟨rfl, rfl, rfl⟩ Dm N p s Wg Wl Wc
      (Cd := Cd) hρ
      (by rw [hρdef, liftLength, Nat.add_sub_cancel, Real.sq_sqrt
        (mul_nonneg (hκi ▸ hκ0.le) (Construction.Stream.ocTauPP_pos hΛ).le), hκi])
      hκ0.le hCa hCown hε hε1 hδ.le haτ hown hc hsc.hDst
      (mul_nonneg (Construction.Stream.ocEpsilon_pos hΛ).le (Real.sqrt_nonneg _))
      (by simpa only [Nat.add_sub_cancel] using hsc.hDρ) hF.hCu hΛ
    rw [← NNReal.coe_le_coe] at hFb
    simp only [NNReal.coe_mul, Real.coe_toNNReal _ hρ.le,
      Real.coe_toNNReal _ (mul_nonneg hκ0.le (Real.rpow_nonneg hε.le _))] at hFb
    have hκ' : 0 < D.κ i := hκi ▸ hκ0
    rw [hκi] at hFb
    unfold diagThr at hthr
    refine Eq.trans_le ?_ (diag_record_le (η := η₀) hd hdD hε hcr0 hcr1 hρ hκ' hC.hWr0
      (NNReal.coe_nonneg _) hFb hthr)
    congr 1
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun c _ => ?_
    simp only [hlamd, NNReal.coe_mul, NNReal.coe_pow, Real.coe_toNNReal _ hρ.le]
    rfl
  · -- the expressions
    by_cases hd : 2 ≤ d
    · choose φ E hφ hrep hsf hnm hbound using fun pc : OddSlot => hslot pc d I c
      refine ⟨fun pc => Gen.mul (Gen.time (.const (lamd d))) (E pc), Δ, X.leaf, fun q => ?_,
        hC.hΔ, hLC, fun pc => Or.inr ⟨trivial, hsf pc⟩, ?_⟩
      · obtain ⟨hs, hf, f, hd', hv⟩ := hrep q
        refine ⟨.mul (.timeConst _) hs, .mul (.time _) (fromSeed_mono hF.hexp hf), _,
          .mul (.time _) hd', fun ctx t ht X z => ?_⟩
        rw [hflux q ctx d I t X z hd]
        split_ifs with hadm
        · have hPz : slotCtx D b j₀ i q.1 t (ctx.1.recenter D (D.eps (i - 1) • X)) z :=
            And.intro hadm ht
          have h1 := hv t _ z hPz
          have h2 := hφ q ⟨(t, ctx.1.recenter D (D.eps (i - 1) • X), z), hPz⟩
          simp only [Pi.smul_apply, smul_eq_mul, GenSort.mul, GenSort.ofTime, TimeLetter.eval]
          rw [h1, ← h2]
          simp only [hlamd, Nat.add_sub_cancel]
          rfl
        · rfl
      · refine (ledgerSum_le D κc Δ a₀ X.leaf hC.ha₀
          (fun pc => Gen.mul (Gen.time (.const (lamd d))) (E pc)) ha0 (3 * Real.pi * b) kI.Lstar
          (compReserve kI v'.1) (ENNReal.ofReal |lamd d| *
            ((F * Real.toNNReal ρ ^ (d - 1) : ℝ≥0) : ℝ≥0∞)) fun pc t ht => ?_).trans ?_
        · rw [genNorm_mul_eq _ _ _ _ _ (hX.hshape _ (not_isMarkShape_mul _ _)),
            genNorm_const_eq _ _ _ _ _ _ (hX.hshape _ (not_isMarkShape_time _))]
          exact mul_le_mul' le_rfl (hbound pc t ht (compReserve kI v'.1) 0 hres0 hresΔ
            (by rw [zero_add]; exact hC.hLf))
        · calc wsum (3 * Real.pi * b) kI.Lstar (expProfile 1 a) * (ENNReal.ofReal |lamd d| *
                ((F * Real.toNNReal ρ ^ (d - 1) : ℝ≥0) : ℝ≥0∞))
              ≤ ENNReal.ofReal Wr * (ENNReal.ofReal |lamd d| *
                ((F * Real.toNNReal ρ ^ (d - 1) : ℝ≥0) : ℝ≥0∞)) := mul_le_mul' hC.hWr le_rfl
            _ = ENNReal.ofReal (Wr * (|lamd d| * ((F * Real.toNNReal ρ ^ (d - 1) : ℝ≥0) : ℝ))) := by
                rw [ENNReal.ofReal_mul hC.hWr0, ENNReal.ofReal_mul (abs_nonneg _),
                  ENNReal.ofReal_coe_nnreal]
    · refine ⟨fun pc => Gen.time (.const 0), Δ, X.leaf, fun q => ⟨.timeConst 0, .time _,
        GenSort.ofTime .ctx (TimeLetter.eval D (.const 0)), .time _, fun ctx t _ X z => ?_⟩,
        hC.hΔ, hLC, fun _ => trivial, ?_⟩
      · rw [G'.fam.flux_zero q ctx v' u' γ' d I (fun h => hd h.1)]
        split_ifs <;> simp [GenSort.ofTime, TimeLetter.eval]
      · refine (ledgerSum_le D κc Δ a₀ X.leaf hC.ha₀ (fun pc => Gen.time (.const 0)) ha0
          (3 * Real.pi * b) kI.Lstar (compReserve kI v'.1) 0 fun pc t _ => ?_).trans ?_
        · rw [genNorm_const_eq _ _ _ _ _ _ (hX.hshape _ (not_isMarkShape_time _))]
          simp
        · rw [mul_zero]
          exact zero_le
end

end AVRegularity.Providers.CascadeInvariants
end
