-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Lift.TransverseModeKernel
import AVRegularity.CycleReference.TorusChartEquation
import AVRegularity.Construction.Scales.Times
import AVRegularity.Construction.Stream.NextAdmissible
public import AVRegularity.Statements.Intermediate.CycleOutput.OcObsPulses
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Intermediate.CycleOutput.CompBill
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Monotonicity.Lemmas

section
section
/-! Abstract-real algebra for the coarse setting of clause 6 of `cycle_comparison`: a fixed
constant times a positive power of a small base is at most one, and the budget `ω ≤ 1` of the
reference covariance. No construction definition appears in this file. -/

@[expose] public noncomputable section

namespace AVRegularity.CycleComparison.Assembly

/-- A fixed constant times a positive power of a small base is at most one:
`M E^c ≤ 1` when `E ≤ L⁻¹` and `L ≥ (M+1)^{1/c}`. -/
theorem mul_rpow_le_one_of_small {E c L M : ℝ} (hE : 0 < E) (hc : 0 < c) (hL : 0 < L)
    (hEL : E ≤ L⁻¹) (hM : 0 ≤ M) (hLM : (M + 1) ^ (1 / c) ≤ L) : M * E ^ c ≤ 1 := by
  have hM1 : 0 < M + 1 := by linarith
  have h1 : ((M + 1) ^ (1 / c)) ^ c ≤ L ^ c :=
    Real.rpow_le_rpow (Real.rpow_nonneg hM1.le _) hLM hc.le
  have h2 : ((M + 1) ^ (1 / c)) ^ c = M + 1 := by
    rw [← Real.rpow_mul hM1.le (1 / c) c, one_div, inv_mul_cancel₀ hc.ne', Real.rpow_one]
  rw [h2] at h1
  have h3 : E ^ c ≤ (L ^ c)⁻¹ := by
    calc E ^ c ≤ L⁻¹ ^ c := Real.rpow_le_rpow hE.le hEL hc.le
      _ = (L ^ c)⁻¹ := Real.inv_rpow hL.le c
  have h4 : (L ^ c)⁻¹ ≤ (M + 1)⁻¹ := inv_anti₀ hM1 h1
  calc M * E ^ c ≤ M * (M + 1)⁻¹ := mul_le_mul_of_nonneg_left (h3.trans h4) hM
    _ = M / (M + 1) := (div_eq_mul_inv M (M + 1)).symm
    _ ≤ 1 := (div_le_one hM1).2 (by linarith)

/-- The budget of the reference covariance: with `H ≤ C B`, `τ, τ' ≤ τ'' e`, `r ≤ K C e` and
`C (80 + 16 K C) e ≤ 1`, the bound `16Hτ + 4H(4τ'' r + 16τ')` of the covariance primitive is
at most `B τ''`. -/
theorem covariance_budget_le {H B C K τ τ' τ'' r e : ℝ} (hH : H ≤ C * B) (hB : 0 < B)
    (hC : 0 ≤ C) (hτ0 : 0 ≤ τ) (hτ'0 : 0 ≤ τ') (hτ'' : 0 < τ'') (hr0 : 0 ≤ r)
    (hτ : τ ≤ τ'' * e) (hτ' : τ' ≤ τ'' * e) (hr : r ≤ K * C * e)
    (hsmall : C * (80 + 16 * K * C) * e ≤ 1) :
    16 * H * τ + 4 * H * (4 * τ'' * r + 16 * τ') ≤ B * τ'' := by
  have hbr : 4 * τ + 4 * τ'' * r + 16 * τ' ≤ τ'' * e * (20 + 4 * K * C) := by
    have h1 : τ'' * r ≤ τ'' * (K * C * e) := mul_le_mul_of_nonneg_left hr hτ''.le
    linarith
  have hbr0 : 0 ≤ 4 * τ + 4 * τ'' * r + 16 * τ' := by positivity
  calc 16 * H * τ + 4 * H * (4 * τ'' * r + 16 * τ')
      = 4 * H * (4 * τ + 4 * τ'' * r + 16 * τ') := by ring
    _ ≤ 4 * (C * B) * (τ'' * e * (20 + 4 * K * C)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hH (by norm_num)) hbr hbr0 (by positivity)
    _ = B * τ'' * (C * (80 + 16 * K * C) * e) := by ring
    _ ≤ B * τ'' * 1 := mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = B * τ'' := mul_one _

end AVRegularity.CycleComparison.Assembly
end
end

section
/-! Abstract-real power-law algebra for the scale laws of `cycle_comparison`:
bounds of the form `x ≤ C E^p` with
`0 < E ≤ 1` multiply, take natural powers and invert, and a positive margin is absorbed when
the base is small. No construction definition appears in this file. -/

@[expose] public noncomputable section

namespace AVRegularity.CycleComparison.Assembly

/-- Two power-law bounds multiply. -/
theorem powerLaw_mul {E x y C D p r : ℝ} (hE : 0 < E) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxp : x ≤ C * E ^ p) (hyr : y ≤ D * E ^ r) : x * y ≤ C * D * E ^ (p + r) := by
  have hCE : 0 ≤ C * E ^ p := hx.trans hxp
  calc x * y ≤ C * E ^ p * (D * E ^ r) := mul_le_mul hxp hyr hy hCE
    _ = C * D * E ^ (p + r) := by
      rw [Real.rpow_add hE p r]
      ring

/-- Natural powers of a power-law bound. -/
theorem powerLaw_pow {E x C p : ℝ} (hE : 0 < E) (hx : 0 ≤ x) (hxp : x ≤ C * E ^ p) (n : ℕ) :
    x ^ n ≤ C ^ n * E ^ (p * n) := by
  calc x ^ n ≤ (C * E ^ p) ^ n := pow_le_pow_left₀ hx hxp n
    _ = C ^ n * E ^ (p * n) := by
      rw [mul_pow C (E ^ p) n, Real.rpow_mul hE.le p (n : ℝ), Real.rpow_natCast (E ^ p) n]

/-- `1 + T₀ E^{-a} ≤ (1 + T₀) E^{-a}` for `0 < E ≤ 1` and `a ≥ 0`. -/
theorem one_add_le_powerLaw {E T₀ a : ℝ} (hE : 0 < E) (hE1 : E ≤ 1) (ha : 0 ≤ a) :
    1 + T₀ * E ^ (-a) ≤ (1 + T₀) * E ^ (-a) := by
  have h1 : 1 ≤ E ^ (-a) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hE hE1 (by linarith)
  linarith

/-- A lower power-law bound of `x` gives an upper power-law bound of `x⁻¹`. -/
theorem inv_le_powerLaw {E K x p : ℝ} (hE : 0 < E) (hK : 0 < K) (h : K⁻¹ * E ^ p ≤ x) :
    x⁻¹ ≤ K * E ^ (-p) := by
  have hpos : 0 < K⁻¹ * E ^ p := mul_pos (inv_pos.2 hK) (Real.rpow_pos_of_pos hE p)
  have h1 : x⁻¹ ≤ (K⁻¹ * E ^ p)⁻¹ := inv_anti₀ hpos h
  have h2 : (K⁻¹ * E ^ p)⁻¹ = K * E ^ (-p) := by
    rw [mul_inv K⁻¹ (E ^ p), inv_inv K, Real.rpow_neg hE.le p]
  rw [h2] at h1
  exact h1

/-- An upper power-law bound of `u / v` gives a lower power-law bound of `v / u`. -/
theorem div_ge_powerLaw {E C u v p : ℝ} (hE : 0 < E) (hu : 0 < u) (hv : 0 < v)
    (h : u / v ≤ C * E ^ p) : C⁻¹ * E ^ (-p) ≤ v / u := by
  have h1 : (C * E ^ p)⁻¹ ≤ (u / v)⁻¹ := inv_anti₀ (div_pos hu hv) h
  have h2 : (C * E ^ p)⁻¹ = C⁻¹ * E ^ (-p) := by
    rw [mul_inv C (E ^ p), Real.rpow_neg hE.le p]
  have h3 : (u / v)⁻¹ = v / u := inv_div u v
  rw [h2, h3] at h1
  exact h1

/-- Lower power-law bounds of `e / R` and of `R` bound `s / e` from above, for `s ≤ C₀`. -/
theorem div_le_powerLaw_of_lower {E C₀ p₁ p₂ e R s : ℝ} (hE : 0 < E) (hC₀ : 0 < C₀)
    (hR : 0 < R) (he : 0 < e) (h₁ : C₀⁻¹ * E ^ p₁ ≤ e / R) (h₂ : C₀⁻¹ * E ^ p₂ ≤ R)
    (hs : s ≤ C₀) : s / e ≤ C₀ ^ 3 * E ^ (-(p₁ + p₂)) := by
  have hP₁ : 0 < E ^ p₁ := Real.rpow_pos_of_pos hE p₁
  have hP₂ : 0 < E ^ p₂ := Real.rpow_pos_of_pos hE p₂
  have hN : 0 < E ^ (-(p₁ + p₂)) := Real.rpow_pos_of_pos hE _
  have h₁' : E ^ p₁ ≤ C₀ * (e / R) := (inv_mul_le_iff₀ hC₀).1 h₁
  have h₂' : E ^ p₂ ≤ C₀ * R := (inv_mul_le_iff₀ hC₀).1 h₂
  have h₃ : E ^ p₁ * E ^ p₂ ≤ C₀ ^ 2 * e := by
    calc E ^ p₁ * E ^ p₂ ≤ C₀ * (e / R) * (C₀ * R) :=
          mul_le_mul h₁' h₂' hP₂.le (hP₁.le.trans h₁')
      _ = C₀ ^ 2 * (e / R * R) := by ring
      _ = C₀ ^ 2 * e := by rw [div_mul_cancel₀ e hR.ne']
  have hprod : E ^ (-(p₁ + p₂)) * (E ^ p₁ * E ^ p₂) = 1 := by
    rw [← Real.rpow_add hE p₁ p₂, ← Real.rpow_add hE (-(p₁ + p₂)) (p₁ + p₂)]
    have h0 : -(p₁ + p₂) + (p₁ + p₂) = 0 := by ring
    rw [h0, Real.rpow_zero]
  rw [div_le_iff₀ he]
  calc s ≤ C₀ := hs
    _ = C₀ * (E ^ (-(p₁ + p₂)) * (E ^ p₁ * E ^ p₂)) := by rw [hprod, mul_one]
    _ ≤ C₀ * (E ^ (-(p₁ + p₂)) * (C₀ ^ 2 * e)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h₃ hN.le) hC₀.le
    _ = C₀ ^ 3 * E ^ (-(p₁ + p₂)) * e := by ring

/-- A power-law bound `R ≤ C₀ E^{1+c}` with a positive margin `c` gives `R ≤ E` as soon as
`E ≤ L⁻¹` with `L ≥ C₀^{1/c}`. -/
theorem le_of_powerLaw_of_small {E C₀ c L R : ℝ} (hE : 0 < E) (hC₀ : 0 < C₀) (hc : 0 < c)
    (hL : 0 < L) (hEL : E ≤ L⁻¹) (hLC : C₀ ^ (1 / c) ≤ L) (hR : R ≤ C₀ * E ^ (1 + c)) :
    R ≤ E := by
  have h1 : (C₀ ^ (1 / c)) ^ c ≤ L ^ c :=
    Real.rpow_le_rpow (Real.rpow_nonneg hC₀.le _) hLC hc.le
  have h2 : (C₀ ^ (1 / c)) ^ c = C₀ := by
    rw [← Real.rpow_mul hC₀.le (1 / c) c, one_div, inv_mul_cancel₀ hc.ne', Real.rpow_one]
  rw [h2] at h1
  have h3 : E ^ c ≤ (L ^ c)⁻¹ := by
    calc E ^ c ≤ L⁻¹ ^ c := Real.rpow_le_rpow hE.le hEL hc.le
      _ = (L ^ c)⁻¹ := Real.inv_rpow hL.le c
  have h4 : (L ^ c)⁻¹ ≤ C₀⁻¹ := inv_anti₀ hC₀ h1
  have h5 : C₀ * E ^ c ≤ 1 := by
    calc C₀ * E ^ c ≤ C₀ * C₀⁻¹ := mul_le_mul_of_nonneg_left (h3.trans h4) hC₀.le
      _ = 1 := mul_inv_cancel₀ hC₀.ne'
  calc R ≤ C₀ * E ^ (1 + c) := hR
    _ = E * (C₀ * E ^ c) := by
      rw [Real.rpow_add hE 1 c, Real.rpow_one]
      ring
    _ ≤ E * 1 := mul_le_mul_of_nonneg_left h5 hE.le
    _ = E := mul_one E

end AVRegularity.CycleComparison.Assembly
end
end

section
/-! Abstract-real algebra for the bill bound of `cycle_comparison`: choose `A'` so that `Z ≤ 1`,
then `3δN' > P+2`, `2δ(J'+1) > P+qγ+2` and `δp' > P+qγ+2`; the quiet exponential absorbs the
algebraic transition count and all fixed polynomial losses, and the chosen orders give
`𝔅 ≤ C_P E^P`.

The bill `𝔅 = ε_c^{N'}(1+Z) + [√(B/ν) + ε_c²(1+Z)]𝔱 + ℓ√(B_p/τ) exp(-cτ/ℓ²)` is written here
for abstract reals (`billShape`), and bounded by `billConst · E^P` from power-law bounds of its
scales in `E` with `0 < E ≤ 1`. No construction definition appears in this file. -/

@[expose] public noncomputable section

namespace AVRegularity.CycleComparison.Assembly

/-- `√y ≤ 1 + y` for `y ≥ 0`. -/
theorem sqrt_le_one_add {y : ℝ} (hy : 0 ≤ y) : Real.sqrt y ≤ 1 + y := by
  rw [Real.sqrt_le_left (by linarith : (0 : ℝ) ≤ 1 + y)]
  linarith [sq_nonneg y]

/-- `x ≤ c ⌈x/c⌉₊` for `c > 0`. -/
theorem le_mul_ceil_div {x c : ℝ} (hc : 0 < c) : x ≤ c * ((⌈x / c⌉₊ : ℕ) : ℝ) := by
  have h1 : x / c ≤ ((⌈x / c⌉₊ : ℕ) : ℝ) := Nat.le_ceil (x / c)
  rw [div_le_iff₀ hc] at h1
  calc x ≤ ((⌈x / c⌉₊ : ℕ) : ℝ) * c := h1
    _ = c * ((⌈x / c⌉₊ : ℕ) : ℝ) := mul_comm _ _

/-- An order above the threshold `⌈x/c⌉₊` satisfies `x ≤ c n`. -/
theorem le_mul_of_ceil_le {x c : ℝ} (hc : 0 < c) {n : ℕ} (hn : ⌈x / c⌉₊ ≤ n) :
    x ≤ c * (n : ℝ) :=
  (le_mul_ceil_div hc).trans (mul_le_mul_of_nonneg_left (Nat.cast_le.2 hn) hc.le)

/-- The observation window `T ≤ C_obs E^{-A_obs}` with arbitrary real `C_obs`, `A_obs` gives
`T ≤ max C_obs 0 · E^{-max A_obs 0}` for `0 < E ≤ 1`. -/
theorem window_le {E Cobs Aobs T : ℝ} (hE : 0 < E) (hE1 : E ≤ 1)
    (hT : T ≤ Cobs * E ^ (-Aobs)) : T ≤ max Cobs 0 * E ^ (-(max Aobs 0)) := by
  have h1 : E ^ (-Aobs) ≤ E ^ (-(max Aobs 0)) :=
    Real.rpow_le_rpow_of_exponent_ge hE hE1 (neg_le_neg (le_max_left Aobs 0))
  calc T ≤ Cobs * E ^ (-Aobs) := hT
    _ ≤ max Cobs 0 * E ^ (-Aobs) :=
        mul_le_mul_of_nonneg_right (le_max_left Cobs 0) (Real.rpow_pos_of_pos hE _).le
    _ ≤ max Cobs 0 * E ^ (-(max Aobs 0)) := mul_le_mul_of_nonneg_left h1 (le_max_right Cobs 0)

/-- The quiet exponential beats a power: from `c E^{-p} ≤ C y`,
`exp(-y) ≤ Cⁿ n!/cⁿ · E^{pn}` for every `n`. -/
theorem exp_neg_le_powerLaw {E c C y p : ℝ} (hE : 0 < E) (hc : 0 < c) (hC : 0 < C)
    (hy : 0 ≤ y) (h : c * E ^ (-p) ≤ C * y) (n : ℕ) :
    Real.exp (-y) ≤ C ^ n * (n.factorial : ℝ) / c ^ n * E ^ (p * n) := by
  have hu : 0 < E ^ (-p) := Real.rpow_pos_of_pos hE (-p)
  have hcu : 0 < c * E ^ (-p) := mul_pos hc hu
  have h1 : (c * E ^ (-p)) ^ n ≤ C ^ n * y ^ n := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hcu.le h n
  have h2 := AVRegularity.CycleComparison.Lift.pow_mul_exp_neg_le_factorial n y hy
  have h3 : (c * E ^ (-p)) ^ n * Real.exp (-y) ≤ C ^ n * (n.factorial : ℝ) := by
    calc (c * E ^ (-p)) ^ n * Real.exp (-y) ≤ C ^ n * y ^ n * Real.exp (-y) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = C ^ n * (y ^ n * Real.exp (-y)) := mul_assoc _ _ _
      _ ≤ C ^ n * (n.factorial : ℝ) := mul_le_mul_of_nonneg_left h2 (pow_nonneg hC.le n)
  have hcn : 0 < c ^ n := pow_pos hc n
  have h4 : (E ^ (-p)) ^ n * Real.exp (-y) ≤ C ^ n * (n.factorial : ℝ) / c ^ n := by
    rw [le_div_iff₀ hcn]
    calc (E ^ (-p)) ^ n * Real.exp (-y) * c ^ n = (c * E ^ (-p)) ^ n * Real.exp (-y) := by
          rw [mul_pow]
          ring
      _ ≤ C ^ n * (n.factorial : ℝ) := h3
  have hone : (E ^ (-p)) ^ n * E ^ (p * n) = 1 := by
    rw [← Real.rpow_natCast (E ^ (-p)) n, ← Real.rpow_mul hE.le (-p) (n : ℝ),
      ← Real.rpow_add hE (-p * n) (p * n)]
    have h0 : -p * (n : ℝ) + p * n = 0 := by ring
    rw [h0, Real.rpow_zero]
  calc Real.exp (-y) = (E ^ (-p)) ^ n * Real.exp (-y) * E ^ (p * n) := by
        calc Real.exp (-y) = Real.exp (-y) * ((E ^ (-p)) ^ n * E ^ (p * n)) := by
              rw [hone, mul_one]
          _ = (E ^ (-p)) ^ n * Real.exp (-y) * E ^ (p * n) := by ring
    _ ≤ C ^ n * (n.factorial : ℝ) / c ^ n * E ^ (p * n) :=
        mul_le_mul_of_nonneg_right h4 (Real.rpow_pos_of_pos hE _).le

/-- The transition count `B_p ≤ 5(1 + T/τ)` with `T ≤ T₀ E^{-a}` and `τ⁻¹ ≤ C₀ E^{-b₁}`. -/
theorem pulseCount_le_powerLaw {E Bp T T₀ a τ C₀ b₁ : ℝ} (hE : 0 < E) (hE1 : E ≤ 1)
    (ha : 0 ≤ a) (hb₁ : 0 ≤ b₁) (hT : 0 ≤ T) (hTle : T ≤ T₀ * E ^ (-a)) (hτ : 0 < τ)
    (hτinv : τ⁻¹ ≤ C₀ * E ^ (-b₁)) (hBp : Bp ≤ 5 * (1 + T / τ)) :
    Bp ≤ 5 * (1 + T₀ * C₀) * E ^ (-(a + b₁)) := by
  have hexp : -a + -b₁ = -(a + b₁) := by ring
  have h1 : T / τ ≤ T₀ * C₀ * E ^ (-(a + b₁)) := by
    rw [div_eq_mul_inv, ← hexp]
    exact powerLaw_mul hE hT (inv_nonneg.2 hτ.le) hTle hτinv
  have h2 := one_add_le_powerLaw (T₀ := T₀ * C₀) hE hE1 (add_nonneg ha hb₁)
  linarith

/-- The prefactor of the quiet exponential: `ℓ√(B_p/τ) ≤ 1 + C₀ B_p` when `ℓ²/τ ≤ C₀`. -/
theorem bill_prefactor_le {ℓ τ Bp C₀ : ℝ} (hℓ : 0 < ℓ) (hBp : 0 ≤ Bp) (hC₀ : 0 ≤ C₀)
    (hℓτ : ℓ ^ 2 / τ ≤ C₀) : ℓ * Real.sqrt (Bp / τ) ≤ 1 + C₀ * Bp := by
  have h1 : ℓ * Real.sqrt (Bp / τ) = Real.sqrt (ℓ ^ 2 * (Bp / τ)) := by
    rw [Real.sqrt_mul (sq_nonneg ℓ) (Bp / τ), Real.sqrt_sq hℓ.le]
  have h2 : ℓ ^ 2 * (Bp / τ) ≤ C₀ * Bp := by
    calc ℓ ^ 2 * (Bp / τ) = ℓ ^ 2 / τ * Bp := by ring
      _ ≤ C₀ * Bp := mul_le_mul_of_nonneg_right hℓτ hBp
  rw [h1]
  exact (Real.sqrt_le_sqrt h2).trans (sqrt_le_one_add (mul_nonneg hC₀ hBp))

/-- The factor `Z = (√T/ℓ) r^{A'}` is bounded once `g A' ≥ a + a₁`. -/
theorem billZ_le {E T T₀ a ℓ a₁ r g C₀ : ℝ} {Ac : ℕ} (hE : 0 < E) (hE1 : E ≤ 1)
    (hC₀ : 0 ≤ C₀) (ha : 0 ≤ a) (hT₀ : 0 ≤ T₀) (hT : 0 ≤ T) (hTle : T ≤ T₀ * E ^ (-a))
    (hℓ : 0 < ℓ) (hℓinv : ℓ⁻¹ ≤ C₀ * E ^ (-a₁)) (hr : 0 ≤ r) (hrle : r ≤ C₀ * E ^ g)
    (hAc : a + a₁ ≤ g * Ac) :
    Real.sqrt T / ℓ * r ^ Ac ≤ (1 + T₀) * C₀ * C₀ ^ Ac := by
  have hsT : Real.sqrt T ≤ (1 + T₀) * E ^ (-a) := by
    have h1 := sqrt_le_one_add hT
    have h2 := one_add_le_powerLaw (T₀ := T₀) hE hE1 ha
    linarith
  have h1 : Real.sqrt T / ℓ ≤ (1 + T₀) * C₀ * E ^ (-a + -a₁) := by
    rw [div_eq_mul_inv]
    exact powerLaw_mul hE (Real.sqrt_nonneg T) (inv_nonneg.2 hℓ.le) hsT hℓinv
  have h2 : r ^ Ac ≤ C₀ ^ Ac * E ^ (g * Ac) := powerLaw_pow hE hr hrle Ac
  have h3 := powerLaw_mul hE (div_nonneg (Real.sqrt_nonneg T) hℓ.le) (pow_nonneg hr Ac) h1 h2
  have h4 : E ^ (-a + -a₁ + g * Ac) ≤ 1 := Real.rpow_le_one hE.le hE1 (by linarith)
  have hK : 0 ≤ (1 + T₀) * C₀ * C₀ ^ Ac :=
    mul_nonneg (mul_nonneg (by linarith) hC₀) (pow_nonneg hC₀ Ac)
  calc Real.sqrt T / ℓ * r ^ Ac ≤ (1 + T₀) * C₀ * C₀ ^ Ac * E ^ (-a + -a₁ + g * Ac) := h3
    _ ≤ (1 + T₀) * C₀ * C₀ ^ Ac * 1 := mul_le_mul_of_nonneg_left h4 hK
    _ = (1 + T₀) * C₀ * C₀ ^ Ac := mul_one _

/-- The first term of the bill: `ε_c^{N'}(1+Z) ≤ C₀^{N'}(1+Z̄) E^P` once `3δN' ≥ P`. -/
theorem bill_first_le {E δ P εc Z Zc C₀ : ℝ} {Nc : ℕ} (hE : 0 < E) (hE1 : E ≤ 1)
    (hC₀ : 0 ≤ C₀) (hεc : 0 ≤ εc) (hεcle : εc ≤ C₀ * E ^ (3 * δ)) (hZ0 : 0 ≤ Z) (hZ : Z ≤ Zc)
    (hNc : P ≤ 3 * δ * Nc) :
    εc ^ Nc * (1 + Z) ≤ C₀ ^ Nc * (1 + Zc) * E ^ P := by
  have h1 : εc ^ Nc ≤ C₀ ^ Nc * E ^ (3 * δ * Nc) := powerLaw_pow hE hεc hεcle Nc
  have h2 : E ^ (3 * δ * Nc) ≤ E ^ P := Real.rpow_le_rpow_of_exponent_ge hE hE1 hNc
  have h3 : εc ^ Nc ≤ C₀ ^ Nc * E ^ P :=
    h1.trans (mul_le_mul_of_nonneg_left h2 (pow_nonneg hC₀ Nc))
  calc εc ^ Nc * (1 + Z) ≤ C₀ ^ Nc * E ^ P * (1 + Zc) :=
        mul_le_mul h3 (by linarith) (by linarith)
          (mul_nonneg (pow_nonneg hC₀ Nc) (Real.rpow_pos_of_pos hE P).le)
    _ = C₀ ^ Nc * (1 + Zc) * E ^ P := mul_right_comm _ _ _

/-- The second term of the bill: `[√(B/ν) + ε_c²(1+Z)]𝔱 ≤ 2(C₀ + C₀²(1+Z̄)) E^P` once
`2δJ' ≥ P + qγ` and `δp' ≥ P + qγ`. -/
theorem bill_second_le {E δ P γq εc Z Zc k C₀ : ℝ} {Jc pc : ℕ} (hE : 0 < E) (hE1 : E ≤ 1)
    (hδ : 0 ≤ δ) (hγq : 0 ≤ γq) (hC₀ : 0 ≤ C₀) (hεc : 0 ≤ εc)
    (hεcle : εc ≤ C₀ * E ^ (3 * δ)) (hk : k ≤ C₀ * E ^ (-γq)) (hZ0 : 0 ≤ Z) (hZ : Z ≤ Zc)
    (hJc : P + γq ≤ 2 * δ * Jc) (hpc : P + γq ≤ δ * pc) :
    (k + εc ^ 2 * (1 + Z)) * (E ^ (2 * δ * ((Jc : ℝ) + 1)) + E ^ (δ * (pc : ℝ))) ≤
      2 * (C₀ + C₀ ^ 2 * (1 + Zc)) * E ^ P := by
  have hεc1 : εc ≤ C₀ := by
    have h : E ^ (3 * δ) ≤ 1 := Real.rpow_le_one hE.le hE1 (by linarith)
    calc εc ≤ C₀ * E ^ (3 * δ) := hεcle
      _ ≤ C₀ * 1 := mul_le_mul_of_nonneg_left h hC₀
      _ = C₀ := mul_one C₀
  have hεc2 : εc ^ 2 ≤ C₀ ^ 2 := pow_le_pow_left₀ hεc hεc1 2
  have hK2 : 0 ≤ C₀ ^ 2 * (1 + Zc) := mul_nonneg (sq_nonneg C₀) (by linarith)
  have hX : εc ^ 2 * (1 + Z) ≤ C₀ ^ 2 * (1 + Zc) :=
    mul_le_mul hεc2 (by linarith) (by linarith) (sq_nonneg C₀)
  have hone : 1 ≤ E ^ (-γq) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hE hE1 (by linarith)
  have hX' : C₀ ^ 2 * (1 + Zc) ≤ C₀ ^ 2 * (1 + Zc) * E ^ (-γq) :=
    le_mul_of_one_le_right hK2 hone
  have hfirst : k + εc ^ 2 * (1 + Z) ≤ (C₀ + C₀ ^ 2 * (1 + Zc)) * E ^ (-γq) := by
    calc k + εc ^ 2 * (1 + Z) ≤ C₀ * E ^ (-γq) + C₀ ^ 2 * (1 + Zc) * E ^ (-γq) :=
          add_le_add hk (hX.trans hX')
      _ = (C₀ + C₀ ^ 2 * (1 + Zc)) * E ^ (-γq) := (add_mul _ _ _).symm
  have hJ : E ^ (2 * δ * ((Jc : ℝ) + 1)) ≤ E ^ (P + γq) :=
    Real.rpow_le_rpow_of_exponent_ge hE hE1 (by linarith)
  have hp : E ^ (δ * (pc : ℝ)) ≤ E ^ (P + γq) := Real.rpow_le_rpow_of_exponent_ge hE hE1 hpc
  have hS0 : 0 ≤ E ^ (2 * δ * ((Jc : ℝ) + 1)) + E ^ (δ * (pc : ℝ)) :=
    add_nonneg (Real.rpow_pos_of_pos hE _).le (Real.rpow_pos_of_pos hE _).le
  have hK : 0 ≤ (C₀ + C₀ ^ 2 * (1 + Zc)) * E ^ (-γq) :=
    mul_nonneg (add_nonneg hC₀ hK2) (Real.rpow_pos_of_pos hE _).le
  have hexp : -γq + (P + γq) = P := by ring
  calc (k + εc ^ 2 * (1 + Z)) * (E ^ (2 * δ * ((Jc : ℝ) + 1)) + E ^ (δ * (pc : ℝ)))
      ≤ (C₀ + C₀ ^ 2 * (1 + Zc)) * E ^ (-γq) *
          (E ^ (2 * δ * ((Jc : ℝ) + 1)) + E ^ (δ * (pc : ℝ))) :=
        mul_le_mul_of_nonneg_right hfirst hS0
    _ ≤ (C₀ + C₀ ^ 2 * (1 + Zc)) * E ^ (-γq) * (2 * E ^ (P + γq)) :=
        mul_le_mul_of_nonneg_left (by linarith) hK
    _ = 2 * (C₀ + C₀ ^ 2 * (1 + Zc)) * (E ^ (-γq) * E ^ (P + γq)) := by ring
    _ = 2 * (C₀ + C₀ ^ 2 * (1 + Zc)) * E ^ P := by
        rw [← Real.rpow_add hE (-γq) (P + γq), hexp]

/-- The third term of the bill: the quiet exponential absorbs the transition count, once
`4δn ≥ P + a + b₁`. -/
theorem bill_third_le {E δ P cb ℓ τ Bp C₀ T₀ a b₁ : ℝ} {n : ℕ} (hE : 0 < E) (hE1 : E ≤ 1)
    (hδ : 0 ≤ δ) (hC₀ : 0 < C₀) (hcb : 0 < cb) (hT₀ : 0 ≤ T₀) (hab : 0 ≤ a + b₁)
    (hℓ : 0 < ℓ) (hτ : 0 < τ) (hBp0 : 0 ≤ Bp)
    (hBp : Bp ≤ 5 * (1 + T₀ * C₀) * E ^ (-(a + b₁)))
    (hquiet : C₀⁻¹ * E ^ (-(4 * δ)) ≤ τ / ℓ ^ 2) (hn : P + (a + b₁) ≤ 4 * δ * n) :
    ℓ * Real.sqrt (Bp / τ) * Real.exp (-(cb * τ / ℓ ^ 2)) ≤
      (1 + 5 * C₀ * (1 + T₀ * C₀)) * (C₀ ^ n * (n.factorial : ℝ) / cb ^ n) * E ^ P := by
  have hq1 : E ^ (-(4 * δ)) ≤ C₀ * (τ / ℓ ^ 2) := (inv_mul_le_iff₀ hC₀).1 hquiet
  have hone : 1 ≤ E ^ (-(4 * δ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hE hE1 (by linarith)
  have hℓτ : ℓ ^ 2 / τ ≤ C₀ := by
    have h1 : 1 ≤ C₀ * τ / ℓ ^ 2 := by
      rw [mul_div_assoc C₀ τ (ℓ ^ 2)]
      exact hone.trans hq1
    rw [le_div_iff₀ (pow_pos hℓ 2), one_mul] at h1
    exact (div_le_iff₀ hτ).2 h1
  have hpre : ℓ * Real.sqrt (Bp / τ) ≤ (1 + 5 * C₀ * (1 + T₀ * C₀)) * E ^ (-(a + b₁)) := by
    have h1 := bill_prefactor_le hℓ hBp0 hC₀.le hℓτ
    have h2 : C₀ * Bp ≤ 5 * C₀ * (1 + T₀ * C₀) * E ^ (-(a + b₁)) := by
      calc C₀ * Bp ≤ C₀ * (5 * (1 + T₀ * C₀) * E ^ (-(a + b₁))) :=
            mul_le_mul_of_nonneg_left hBp hC₀.le
        _ = 5 * C₀ * (1 + T₀ * C₀) * E ^ (-(a + b₁)) := by ring
    have h3 := one_add_le_powerLaw (T₀ := 5 * C₀ * (1 + T₀ * C₀)) hE hE1 hab
    linarith
  have hexpb : Real.exp (-(cb * τ / ℓ ^ 2)) ≤
      C₀ ^ n * (n.factorial : ℝ) / cb ^ n * E ^ (4 * δ * n) := by
    have hy : 0 ≤ cb * τ / ℓ ^ 2 := div_nonneg (mul_nonneg hcb.le hτ.le) (sq_nonneg ℓ)
    have hh : cb * E ^ (-(4 * δ)) ≤ C₀ * (cb * τ / ℓ ^ 2) := by
      calc cb * E ^ (-(4 * δ)) ≤ cb * (C₀ * (τ / ℓ ^ 2)) := mul_le_mul_of_nonneg_left hq1 hcb.le
        _ = C₀ * (cb * τ / ℓ ^ 2) := by ring
    exact exp_neg_le_powerLaw hE hcb hC₀ hy hh n
  have hK : 0 ≤ (1 + 5 * C₀ * (1 + T₀ * C₀)) * (C₀ ^ n * (n.factorial : ℝ) / cb ^ n) := by
    positivity
  have hK1 : 0 ≤ (1 + 5 * C₀ * (1 + T₀ * C₀)) * E ^ (-(a + b₁)) := by positivity
  calc ℓ * Real.sqrt (Bp / τ) * Real.exp (-(cb * τ / ℓ ^ 2))
      ≤ (1 + 5 * C₀ * (1 + T₀ * C₀)) * E ^ (-(a + b₁)) *
          (C₀ ^ n * (n.factorial : ℝ) / cb ^ n * E ^ (4 * δ * n)) :=
        mul_le_mul hpre hexpb (Real.exp_pos _).le hK1
    _ = (1 + 5 * C₀ * (1 + T₀ * C₀)) * (C₀ ^ n * (n.factorial : ℝ) / cb ^ n) *
          (E ^ (-(a + b₁)) * E ^ (4 * δ * n)) := mul_mul_mul_comm _ _ _ _
    _ = (1 + 5 * C₀ * (1 + T₀ * C₀)) * (C₀ ^ n * (n.factorial : ℝ) / cb ^ n) *
          E ^ (-(a + b₁) + 4 * δ * n) := by
        rw [← Real.rpow_add hE (-(a + b₁)) (4 * δ * n)]
    _ ≤ (1 + 5 * C₀ * (1 + T₀ * C₀)) * (C₀ ^ n * (n.factorial : ℝ) / cb ^ n) * E ^ P :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hE hE1 (by linarith)) hK

/-- The bill `𝔅 = ε_c^{N'}(1+Z) + [k + ε_c²(1+Z)]𝔱 + ℓ√(B_p/τ) exp(-cτ/ℓ²)` for abstract
scales, with `Z = (√T/ℓ) r^{A'}`, `𝔱 = E^{2δ(J'+1)} + E^{δp'}`; it is `compBill` with
`ε_c = d_*/R`, `r = e/R`, `k = √(B/ν)`. -/
def billShape (E δ εc r k ℓ τ T cb Bp : ℝ) (Ac Nc Jc pc : ℕ) : ℝ :=
  εc ^ Nc * (1 + Real.sqrt T / ℓ * r ^ Ac)
    + (k + εc ^ 2 * (1 + Real.sqrt T / ℓ * r ^ Ac)) *
      (E ^ (2 * δ * ((Jc : ℝ) + 1)) + E ^ (δ * (pc : ℝ)))
    + ℓ * Real.sqrt (Bp / τ) * Real.exp (-(cb * τ / ℓ ^ 2))

/-- The constant of the bill bound. -/
def billConst (C₀ T₀ cb : ℝ) (Ac Nc n : ℕ) : ℝ :=
  C₀ ^ Nc * (1 + (1 + T₀) * C₀ * C₀ ^ Ac) + 2 * (C₀ + C₀ ^ 2 * (1 + (1 + T₀) * C₀ * C₀ ^ Ac))
    + (1 + 5 * C₀ * (1 + T₀ * C₀)) * (C₀ ^ n * (n.factorial : ℝ) / cb ^ n)

theorem billConst_nonneg {C₀ T₀ cb : ℝ} (Ac Nc n : ℕ) (hC₀ : 0 ≤ C₀) (hT₀ : 0 ≤ T₀)
    (hcb : 0 < cb) : 0 ≤ billConst C₀ T₀ cb Ac Nc n := by
  unfold billConst
  positivity

/-- `(x + y + z) w = x w + y w + z w`. -/
theorem add_mul_three (x y z w : ℝ) : (x + y + z) * w = x * w + y * w + z * w := by ring

/-- **The abstract bill bound.** -/
theorem billShape_le {E δ γq P εc r k ℓ τ T Bp cb C₀ T₀ a a₁ b₁ : ℝ} {Ac Nc Jc pc n : ℕ}
    (hE : 0 < E) (hE1 : E ≤ 1) (hδ : 0 < δ) (hγq : 0 ≤ γq) (hC₀ : 0 < C₀) (hcb : 0 < cb)
    (hT₀ : 0 ≤ T₀) (ha : 0 ≤ a) (hb₁ : 0 ≤ b₁)
    (hεc : 0 ≤ εc) (hεcle : εc ≤ C₀ * E ^ (3 * δ))
    (hr : 0 ≤ r) (hrle : r ≤ C₀ * E ^ (γq + 3 * δ))
    (hk : k ≤ C₀ * E ^ (-γq))
    (hℓ : 0 < ℓ) (hℓinv : ℓ⁻¹ ≤ C₀ * E ^ (-a₁))
    (hτ : 0 < τ) (hτinv : τ⁻¹ ≤ C₀ * E ^ (-b₁))
    (hquiet : C₀⁻¹ * E ^ (-(4 * δ)) ≤ τ / ℓ ^ 2)
    (hT : 0 ≤ T) (hTle : T ≤ T₀ * E ^ (-a))
    (hBp0 : 0 ≤ Bp) (hBp : Bp ≤ 5 * (1 + T / τ))
    (hAc : a + a₁ ≤ (γq + 3 * δ) * Ac) (hNc : P ≤ 3 * δ * Nc)
    (hJc : P + γq ≤ 2 * δ * Jc) (hpc : P + γq ≤ δ * pc) (hn : P + (a + b₁) ≤ 4 * δ * n) :
    billShape E δ εc r k ℓ τ T cb Bp Ac Nc Jc pc ≤ billConst C₀ T₀ cb Ac Nc n * E ^ P := by
  have hZ0 : 0 ≤ Real.sqrt T / ℓ * r ^ Ac :=
    mul_nonneg (div_nonneg (Real.sqrt_nonneg T) hℓ.le) (pow_nonneg hr Ac)
  have hZ := billZ_le hE hE1 hC₀.le ha hT₀ hT hTle hℓ hℓinv hr hrle hAc
  have h1 := bill_first_le hE hE1 hC₀.le hεc hεcle hZ0 hZ hNc
  have h2 := bill_second_le hE hE1 hδ.le hγq hC₀.le hεc hεcle hk hZ0 hZ hJc hpc
  have hcount := pulseCount_le_powerLaw hE hE1 ha hb₁ hT hTle hτ hτinv hBp
  have h3 := bill_third_le (cb := cb) hE hE1 hδ.le hC₀ hcb hT₀ (add_nonneg ha hb₁) hℓ hτ hBp0
    hcount hquiet hn
  have hsum := add_le_add (add_le_add h1 h2) h3
  calc billShape E δ εc r k ℓ τ T cb Bp Ac Nc Jc pc ≤ _ := hsum
    _ = billConst C₀ T₀ cb Ac Nc n * E ^ P := by
      unfold billConst
      exact (add_mul_three _ _ _ _).symm

end AVRegularity.CycleComparison.Assembly
end
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleComparison.Assembly

/-! The scale laws used by the clauses of `cycle_comparison`: `ε_c ≤ C E^{3δ}`,
`e/R ≤ C E^{qγ+3δ}` and `√(B/ν) ≤ C E^{-qγ}`, which fix the backward order choices, and the laws
for the switching price and the quiet exponential.

Notation: `E = ε_{m-1}`, `e = ε_m`, `ν = κ_m`, `B = κ_{m-1}` along a band chain, `τ = τ_m`,
`R = √(Bτ_m'')`, `ℓ = e/√ν`, `d_* = ℓ√B`, `ε_c = d_*/R`, `H_* = e^{2β}/(2ν)`.

All laws are consequences of the uniform diffusivity ledger `bandChain_uniform_ledger`
(the body of `cycle_diffusivities`), which holds for `Λ ≥ Λ₀`; they are collected in the
predicate `IsScaleLaws` with one constant `C`, uniform in `Λ ≥ Λ₀`, in the level, in the chain
and in its terminal index. The count of the observed pulses is elementary. -/

/-- The scale laws at one level `m` of a band chain, `ν = κ_m`, `B = κ_{m-1}`, with one
constant `C`. Here `E = ε_{m-1}`, `e = ε_m`, `R = √(Bτ_m'')`, `ℓ = e/√ν`. -/
structure IsScaleLaws (α q : ℝ) (Λ m : ℕ) (ν B C : ℝ) : Prop where
  /-- The fine diffusivity is positive. -/
  ν_pos : 0 < ν
  /-- The chain is monotone: `ν ≤ B`. -/
  ν_le : ν ≤ B
  /-- `ε_c = d_*/R ≤ C E^{3δ}`. -/
  εc_le : ocDStar q Λ m ν B / Real.sqrt (B * ocTauPP α q Λ m) ≤
    C * ocEpsilon q Λ (m - 1) ^ (3 * ocDelta α q)
  /-- `e/R ≤ C E^{qγ+3δ}`. -/
  eR_le : ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m) ≤
    C * ocEpsilon q Λ (m - 1) ^ (q * ocGamma α q + 3 * ocDelta α q)
  /-- `√(B/ν) ≤ C E^{-qγ}`. -/
  contrast_le : Real.sqrt (B / ν) ≤ C * ocEpsilon q Λ (m - 1) ^ (-(q * ocGamma α q))
  /-- The quiet exponential scale: `τ/ℓ² ≥ C⁻¹ E^{-4δ}`. -/
  quiet_ge : C⁻¹ * ocEpsilon q Λ (m - 1) ^ (-(4 * ocDelta α q)) ≤
    ocTau α q Λ m / ocEll q Λ m ν ^ 2
  /-- `H_* ≤ C B`. -/
  hstar_le : ocHStar α q Λ m ν ≤ C * B
  /-- The switching price, sharp exponent: `H_* ℓ²/τ ≤ C B E^{4δ}`. -/
  switching_four_le : ocHStar α q Λ m ν * ocEll q Λ m ν ^ 2 / ocTau α q Λ m ≤
    C * B * ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q)
  /-- The switching price: `H_* ℓ²/τ ≤ C B E^{2δ}`. -/
  switching_le : ocHStar α q Λ m ν * ocEll q Λ m ν ^ 2 / ocTau α q Λ m ≤
    C * B * ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q)
  /-- An algebraic lower bound of the cell length: `ℓ⁻¹ ≤ C E^{-(qγ+3δ+1+γ/2+δ)}`. -/
  ell_inv_le : (ocEll q Λ m ν)⁻¹ ≤ C * ocEpsilon q Λ (m - 1) ^
    (-(q * ocGamma α q + 3 * ocDelta α q + (1 + (ocGamma α q / 2 + ocDelta α q))))
  /-- An algebraic lower bound of the pulse time: `τ⁻¹ ≤ C E^{-(2-β+4δ)}`. -/
  tau_inv_le : (ocTau α q Λ m)⁻¹ ≤
    C * ocEpsilon q Λ (m - 1) ^ (-(2 - (1 + α) + 4 * ocDelta α q))
  /-- `R ≤ E` (the field `IsWindowCover.RE`). -/
  radius_le : Real.sqrt (B * ocTauPP α q Λ m) ≤ ocEpsilon q Λ (m - 1)

/-- **The scale laws.** One constant `C` and one separation threshold `Λ₀` for all levels
`2 ≤ m ≤ M'` of all band chains. -/
theorem scale_laws (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s)
    (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ)
    (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ (M' : ℕ) (κ : ℕ → ℝ), IsOCBandChain α q Λ ζ M' κ → ∀ m, 2 ≤ m → m ≤ M' →
      ∀ ν B, κ m = ν → κ (m - 1) = B → IsScaleLaws α q Λ m ν B C := by
  obtain ⟨C₀, hC₀, Λ₁, hΛ₁, hled⟩ :=
    AVRegularity.CycleReference.bandChain_uniform_ledger hα₀ hα₁ hs₀ hs₁ hq hζ
  have hexp := AVRegularity.Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq
  have hγ : 0 < ocGamma α q := hexp.1
  have hδ : 0 < ocDelta α q := hexp.2.1
  have hc : 0 < ocGamma α q / 2 + ocDelta α q := by linarith
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le one_pos hC₀
  -- the common constant `C₀³ 2³³`
  have hK1 : (1 : ℝ) ≤ C₀ ^ 3 := one_le_pow₀ hC₀
  have hK0 : (0 : ℝ) ≤ C₀ ^ 3 := zero_le_one.trans hK1
  have hC3 : C₀ ^ 3 ≤ C₀ ^ 3 * 2 ^ 33 := by
    calc C₀ ^ 3 = C₀ ^ 3 * 1 := (mul_one _).symm
      _ ≤ C₀ ^ 3 * 2 ^ 33 := mul_le_mul_of_nonneg_left (by norm_num) hK0
  have hC1 : C₀ ≤ C₀ ^ 3 * 2 ^ 33 := by
    calc C₀ = C₀ ^ 1 := (pow_one C₀).symm
      _ ≤ C₀ ^ 3 := pow_le_pow_right₀ hC₀ (by norm_num)
      _ ≤ C₀ ^ 3 * 2 ^ 33 := hC3
  have hC23 : C₀ ^ 2 ≤ C₀ ^ 3 := pow_le_pow_right₀ hC₀ (by norm_num)
  have hC2 : C₀ ^ 2 ≤ C₀ ^ 3 * 2 ^ 33 := hC23.trans hC3
  have hCτ : (2 : ℝ) ^ (26 : ℕ) * 81 ≤ C₀ ^ 3 * 2 ^ 33 := by
    calc (2 : ℝ) ^ (26 : ℕ) * 81 ≤ 1 * 2 ^ 33 := by norm_num
      _ ≤ C₀ ^ 3 * 2 ^ 33 := mul_le_mul_of_nonneg_right hK1 (by norm_num)
  have hCpos : (0 : ℝ) < C₀ ^ 3 * 2 ^ 33 := lt_of_lt_of_le hC₀pos hC1
  have hCinv : (C₀ ^ 3 * 2 ^ 33)⁻¹ ≤ C₀⁻¹ := inv_anti₀ hC₀pos hC1
  refine ⟨C₀ ^ 3 * 2 ^ 33, hC₀.trans hC1,
    max Λ₁ ⌈C₀ ^ (1 / (ocGamma α q / 2 + ocDelta α q))⌉₊, hΛ₁.trans (le_max_left _ _), ?_⟩
  intro Λ hΛ M' κ hband m hm2 hmM ν B hν hB
  have hΛ₁' : Λ₁ ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛ₂ : ⌈C₀ ^ (1 / (ocGamma α q / 2 + ocDelta α q))⌉₊ ≤ Λ := (le_max_right _ _).trans hΛ
  have h128 : 128 ≤ Λ := hΛ₁.trans hΛ₁'
  have hΛ1 : 1 ≤ Λ := by omega
  have hΛpos : (0 : ℝ) < (Λ : ℝ) := by exact_mod_cast (show 0 < Λ by omega)
  have hE : 0 < ocEpsilon q Λ (m - 1) :=
    (AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 h128).1
  have hE1 : ocEpsilon q Λ (m - 1) ≤ 1 :=
    (AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 h128).2.1
  have he : 0 < ocEpsilon q Λ m := (AVRegularity.Scales.epsilon_basic (m := m) hq.1 h128).1
  have hτ : 0 < ocTau α q Λ m := AVRegularity.Construction.Stream.ocTau_pos hΛ1
  have hτ'' : 0 < ocTauPP α q Λ m := AVRegularity.Construction.Stream.ocTauPP_pos hΛ1
  have hνpos : 0 < ν := by
    rw [← hν]
    exact AVRegularity.CycleReference.bandChain_pos hΛ1 hζ hband hmM
  have hBpos : 0 < B := by
    rw [← hB]
    exact AVRegularity.CycleReference.bandChain_pos hΛ1 hζ hband (show m - 1 ≤ M' by omega)
  have hR : 0 < Real.sqrt (B * ocTauPP α q Λ m) := Real.sqrt_pos.2 (mul_pos hBpos hτ'')
  have hℓ : 0 < ocEll q Λ m ν := by
    unfold ocEll
    exact div_pos he (Real.sqrt_pos.2 hνpos)
  have hpow (p : ℝ) : 0 ≤ ocEpsilon q Λ (m - 1) ^ p := (Real.rpow_pos_of_pos hE p).le
  have up {x y : ℝ} (hy : 0 ≤ y) (hx : x ≤ C₀ * y) : x ≤ C₀ ^ 3 * 2 ^ 33 * y :=
    hx.trans (mul_le_mul_of_nonneg_right hC1 hy)
  -- the ledger at this level
  obtain ⟨hνB, hB1, _, hH, hRh, _, _, hεc, heR, hℓτ, _, hk, _⟩ :=
    (hled Λ hΛ₁' M' (by omega) κ hband).2 m hm2 hmM ν B hν hB
  unfold ocRh at hRh hεc heR
  unfold ocC at hRh
  -- the flux amplitude `H_*` and the switching price
  have hX : 0 ≤ ocEpsilon q Λ m ^ (2 * (1 + α)) / ν :=
    div_nonneg (Real.rpow_pos_of_pos he _).le hνpos.le
  have hXle : ocEpsilon q Λ m ^ (2 * (1 + α)) / ν ≤ C₀ * B := by linarith
  have hHeq : ocHStar α q Λ m ν = ocEpsilon q Λ m ^ (2 * (1 + α)) / ν / 2 := by
    unfold ocHStar
    ring
  have hHle : ocHStar α q Λ m ν ≤ C₀ * B := by
    rw [hHeq]
    exact (half_le_self hX).trans hXle
  have hℓτ0 : 0 ≤ ocEll q Λ m ν ^ 2 / ocTau α q Λ m := div_nonneg (sq_nonneg _) hτ.le
  have hsw : ocHStar α q Λ m ν * ocEll q Λ m ν ^ 2 / ocTau α q Λ m ≤
      C₀ ^ 2 * B * ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q) := by
    rw [mul_div_assoc (ocHStar α q Λ m ν) (ocEll q Λ m ν ^ 2) (ocTau α q Λ m)]
    calc ocHStar α q Λ m ν * (ocEll q Λ m ν ^ 2 / ocTau α q Λ m)
        ≤ C₀ * B * (C₀ * ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q)) :=
          mul_le_mul hHle hℓτ hℓτ0 (mul_nonneg hC₀pos.le hBpos.le)
      _ = C₀ ^ 2 * B * ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q) := by ring
  have hsw4 : ocHStar α q Λ m ν * ocEll q Λ m ν ^ 2 / ocTau α q Λ m ≤
      C₀ ^ 3 * 2 ^ 33 * B * ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q) :=
    hsw.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC2 hBpos.le) (hpow _))
  have h42 : ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q) ≤
      ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q) :=
    Real.rpow_le_rpow_of_exponent_ge hE hE1 (by linarith)
  have hsw2 : ocHStar α q Λ m ν * ocEll q Λ m ν ^ 2 / ocTau α q Λ m ≤
      C₀ ^ 3 * 2 ^ 33 * B * ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q) :=
    hsw4.trans (mul_le_mul_of_nonneg_left h42 (mul_nonneg hCpos.le hBpos.le))
  -- the quiet exponential scale
  have hquiet : C₀⁻¹ * ocEpsilon q Λ (m - 1) ^ (-(4 * ocDelta α q)) ≤
      ocTau α q Λ m / ocEll q Λ m ν ^ 2 := div_ge_powerLaw hE (pow_pos hℓ 2) hτ hℓτ
  -- the cell length from below
  have hBle : B ≤ C₀ := by
    have h1 : ocEpsilon q Λ (m - 1) ^ ((1 + α) + ocGamma α q) ≤ 1 :=
      Real.rpow_le_one hE.le hE1 (by linarith)
    calc B ≤ C₀ * ocEpsilon q Λ (m - 1) ^ ((1 + α) + ocGamma α q) := hB1.2
      _ ≤ C₀ * 1 := mul_le_mul_of_nonneg_left h1 hC₀pos.le
      _ = C₀ := mul_one C₀
  have hsν : Real.sqrt ν ≤ C₀ := by
    rw [Real.sqrt_le_left hC₀pos.le]
    have h2 : 0 ≤ (C₀ - 1) * (C₀ - 1) := mul_nonneg (sub_nonneg.2 hC₀) (sub_nonneg.2 hC₀)
    linarith only [hνB, hBle, hC₀, h2]
  have hℓinv : (ocEll q Λ m ν)⁻¹ ≤ C₀ ^ 3 * ocEpsilon q Λ (m - 1) ^
      (-(q * ocGamma α q + 3 * ocDelta α q + (1 + (ocGamma α q / 2 + ocDelta α q)))) := by
    have h := div_le_powerLaw_of_lower hE hC₀pos hR he heR.1 hRh.1 hsν
    unfold ocEll
    rw [inv_div (ocEpsilon q Λ m) (Real.sqrt ν)]
    exact h
  -- the pulse time from below
  have hτas := AVRegularity.CycleReference.ocTau_asymp (m := m) hα₀ hα₁ hs₀ hs₁ hq h128
  have hτinv : (ocTau α q Λ m)⁻¹ ≤ 2 ^ (26 : ℕ) * 81 *
      ocEpsilon q Λ (m - 1) ^ (-(2 - (1 + α) + 4 * ocDelta α q)) :=
    inv_le_powerLaw hE (by norm_num) hτas.1
  -- the renewal radius against the parent wavelength
  have hEΛ : ocEpsilon q Λ (m - 1) ≤ (Λ : ℝ)⁻¹ :=
    AVRegularity.CycleReference.epsilon_le_inv_separation hq.1 h128 (by omega)
  have hLC : C₀ ^ (1 / (ocGamma α q / 2 + ocDelta α q)) ≤ (Λ : ℝ) :=
    (Nat.le_ceil (C₀ ^ (1 / (ocGamma α q / 2 + ocDelta α q)))).trans (Nat.cast_le.2 hΛ₂)
  have hrad : Real.sqrt (B * ocTauPP α q Λ m) ≤ ocEpsilon q Λ (m - 1) :=
    le_of_powerLaw_of_small hE hC₀pos hc hΛpos hEΛ hLC hRh.2
  exact
    { ν_pos := hνpos
      ν_le := hνB
      εc_le := up (hpow _) hεc
      eR_le := up (hpow _) heR.2
      contrast_le := up (hpow _) hk
      quiet_ge := (mul_le_mul_of_nonneg_right hCinv (hpow _)).trans hquiet
      hstar_le := up hBpos.le hHle
      switching_four_le := hsw4
      switching_le := hsw2
      ell_inv_le := hℓinv.trans (mul_le_mul_of_nonneg_right hC3 (hpow _))
      tau_inv_le := hτinv.trans (mul_le_mul_of_nonneg_right hCτ (hpow _))
      radius_le := hrad }

/-- The natural truncation of an integer is bounded by any nonnegative real bound of it. -/
theorem natCast_toNat_le {N : ℤ} {b : ℝ} (hb : 0 ≤ b) (h : (N : ℝ) ≤ b) :
    ((N.toNat : ℕ) : ℝ) ≤ b := by
  rcases le_total 0 N with hN | hN
  · have he : ((N.toNat : ℕ) : ℤ) = N := Int.toNat_of_nonneg hN
    have h1 : ((N.toNat : ℕ) : ℝ) = (N : ℝ) := by exact_mod_cast he
    rw [h1]
    exact h
  · rw [Int.toNat_of_nonpos hN, Nat.cast_zero]
    exact hb

/-- **The number of observed pulses** of a window of length `T_obs`:
`B_p ≤ C(1 + |I|/τ)`. -/
theorem obsPulses_card_le (α q : ℝ) {Λ : ℕ} (hΛ : 1 ≤ Λ) (m : ℕ) (tp : ℝ) {Tobs : ℝ}
    (hT : 0 ≤ Tobs) :
    ((ocObsPulses α q Λ m tp (tp + Tobs)).card : ℝ) ≤ 5 * (1 + Tobs / ocTau α q Λ m) := by
  classical
  have hτ : 0 < ocTau α q Λ m := AVRegularity.Construction.Stream.ocTau_pos hΛ
  have hq0 : 0 ≤ Tobs / ocTau α q Λ m := div_nonneg hT hτ.le
  have h0 : (ocObsPulses α q Λ m tp (tp + Tobs)).card ≤
      (Finset.Icc (⌊tp / ocTau α q Λ m⌋ - 1) (⌈(tp + Tobs) / ocTau α q Λ m⌉ + 1)).card := by
    unfold ocObsPulses
    exact Finset.card_filter_le _ _
  have h1 : (ocObsPulses α q Λ m tp (tp + Tobs)).card ≤
      (⌈(tp + Tobs) / ocTau α q Λ m⌉ + 1 + 1 - (⌊tp / ocTau α q Λ m⌋ - 1)).toNat :=
    h0.trans_eq (Int.card_Icc _ _)
  have hc := Int.ceil_lt_add_one ((tp + Tobs) / ocTau α q Λ m)
  have hf := Int.sub_one_lt_floor (tp / ocTau α q Λ m)
  have hsplit : (tp + Tobs) / ocTau α q Λ m =
      tp / ocTau α q Λ m + Tobs / ocTau α q Λ m := add_div _ _ _
  have hN : ((⌈(tp + Tobs) / ocTau α q Λ m⌉ + 1 + 1 - (⌊tp / ocTau α q Λ m⌋ - 1) : ℤ) : ℝ) ≤
      5 + Tobs / ocTau α q Λ m := by
    push_cast
    linarith
  have h2 := natCast_toNat_le (by linarith : (0 : ℝ) ≤ 5 + Tobs / ocTau α q Λ m) hN
  calc ((ocObsPulses α q Λ m tp (tp + Tobs)).card : ℝ)
      ≤ (((⌈(tp + Tobs) / ocTau α q Λ m⌉ + 1 + 1 -
          (⌊tp / ocTau α q Λ m⌋ - 1)).toNat : ℕ) : ℝ) := Nat.cast_le.2 h1
    _ ≤ 5 + Tobs / ocTau α q Λ m := h2
    _ ≤ 5 * (1 + Tobs / ocTau α q Λ m) := by linarith

/-! Clause 5 of `cycle_comparison`: the bill `𝔅` of the observed pulses of a window of
algebraic length is at most `C E^P`, for the backward order choices.

The orders are chosen from thresholds depending only on `(α, q, P, A_obs)`: with
`a = max A_obs 0`, `δ = ocDelta`, `γ = ocGamma`,
* `qγ+3δ` times `A'` exceeds `a + qγ + 3δ + 1 + γ/2 + δ` (so `Z ≤ C`);
* `3δN' ≥ P`, `2δJ' ≥ P + qγ`, `δp' ≥ P + qγ`.
The quiet exponential `exp(-cτ/ℓ²)` with `τ/ℓ² ≥ C⁻¹E^{-4δ}` absorbs the pulse count
`B_p ≤ 5(1 + T_obs/τ)` and the prefactor `ℓ√(B_p/τ)`. The scale laws come from
`scale_laws`, which needs `Λ ≥ Λ₀`. -/

/-- `compBill` is the abstract bill `billShape` at the scales of the construction. -/
theorem compBill_eq (α q : ℝ) (Λ m : ℕ) (ν B Tobs cb : ℝ) (Bp Ac Nc Jc pc : ℕ) :
    compBill α q Λ m ν B Tobs cb Bp Ac Nc Jc pc =
      billShape (ocEpsilon q Λ (m - 1)) (ocDelta α q)
        (ocDStar q Λ m ν B / Real.sqrt (B * ocTauPP α q Λ m))
        (ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)) (Real.sqrt (B / ν))
        (ocEll q Λ m ν) (ocTau α q Λ m) Tobs cb (Bp : ℝ) Ac Nc Jc pc :=
  rfl

/-- **The bill bound from the scale laws** at a fixed `Λ ≥ 128` and scale-law constant `C₀`. -/
theorem bill_bound_of_scaleLaws (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s)
    (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q) (Λ : ℕ) (hΛ : 128 ≤ Λ)
    (C₀ : ℝ) (hC₀ : 1 ≤ C₀) (Pacc Aobs Cobs : ℝ) :
    ∃ Ac₀ Nc₀ Jc₀ pc₀ : ℕ, ∀ Ac Nc Jc pc : ℕ, Ac₀ ≤ Ac → Nc₀ ≤ Nc → Jc₀ ≤ Jc → pc₀ ≤ pc →
      ∀ cb : ℝ, 0 < cb → ∃ C : ℝ, 0 ≤ C ∧
        ∀ (m : ℕ) (ν B : ℝ), IsScaleLaws α q Λ m ν B C₀ → ∀ tp Tobs : ℝ, 0 < Tobs →
          Tobs ≤ Cobs * ocEpsilon q Λ (m - 1) ^ (-Aobs) →
          compBill α q Λ m ν B Tobs cb (ocObsPulses α q Λ m tp (tp + Tobs)).card Ac Nc Jc pc ≤
            C * ocEpsilon q Λ (m - 1) ^ Pacc := by
  have hexp := AVRegularity.Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq
  have hγ : 0 < ocGamma α q := hexp.1
  have hδ : 0 < ocDelta α q := hexp.2.1
  have hγq : 0 ≤ q * ocGamma α q := (mul_pos (lt_trans zero_lt_one hq.1) hγ).le
  have hg : 0 < q * ocGamma α q + 3 * ocDelta α q := by linarith
  have hb₁ : 0 ≤ 2 - (1 + α) + 4 * ocDelta α q := by linarith
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le one_pos hC₀
  have ha : 0 ≤ max Aobs 0 := le_max_right Aobs 0
  have hT₀ : 0 ≤ max Cobs 0 := le_max_right Cobs 0
  refine ⟨⌈(max Aobs 0 + (q * ocGamma α q + 3 * ocDelta α q +
      (1 + (ocGamma α q / 2 + ocDelta α q)))) / (q * ocGamma α q + 3 * ocDelta α q)⌉₊,
    ⌈Pacc / (3 * ocDelta α q)⌉₊, ⌈(Pacc + q * ocGamma α q) / (2 * ocDelta α q)⌉₊,
    ⌈(Pacc + q * ocGamma α q) / ocDelta α q⌉₊, ?_⟩
  intro Ac Nc Jc pc hAc hNc hJc hpc cb hcb
  have hAc' : max Aobs 0 + (q * ocGamma α q + 3 * ocDelta α q +
      (1 + (ocGamma α q / 2 + ocDelta α q))) ≤
        (q * ocGamma α q + 3 * ocDelta α q) * (Ac : ℝ) :=
    le_mul_of_ceil_le hg hAc
  have hNc' : Pacc ≤ 3 * ocDelta α q * (Nc : ℝ) := le_mul_of_ceil_le (by linarith) hNc
  have hJc' : Pacc + q * ocGamma α q ≤ 2 * ocDelta α q * (Jc : ℝ) :=
    le_mul_of_ceil_le (by linarith) hJc
  have hpc' : Pacc + q * ocGamma α q ≤ ocDelta α q * (pc : ℝ) := le_mul_of_ceil_le hδ hpc
  have hn : Pacc + (max Aobs 0 + (2 - (1 + α) + 4 * ocDelta α q)) ≤ 4 * ocDelta α q *
      ((⌈(Pacc + (max Aobs 0 + (2 - (1 + α) + 4 * ocDelta α q))) /
        (4 * ocDelta α q)⌉₊ : ℕ) : ℝ) :=
    le_mul_ceil_div (by linarith)
  refine ⟨billConst C₀ (max Cobs 0) cb Ac Nc
      ⌈(Pacc + (max Aobs 0 + (2 - (1 + α) + 4 * ocDelta α q))) / (4 * ocDelta α q)⌉₊,
    billConst_nonneg Ac Nc _ hC₀pos.le hT₀ hcb, ?_⟩
  intro m ν B hL tp Tobs hT hTle
  have hE : 0 < ocEpsilon q Λ (m - 1) :=
    (AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 hΛ).1
  have hE1 : ocEpsilon q Λ (m - 1) ≤ 1 :=
    (AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 hΛ).2.1
  have he : 0 < ocEpsilon q Λ m := (AVRegularity.Scales.epsilon_basic (m := m) hq.1 hΛ).1
  have hΛ1 : 1 ≤ Λ := by omega
  have hτ : 0 < ocTau α q Λ m := AVRegularity.Construction.Stream.ocTau_pos hΛ1
  have hℓ : 0 < ocEll q Λ m ν := by
    unfold ocEll
    exact div_pos he (Real.sqrt_pos.2 hL.ν_pos)
  have hεc : 0 ≤ ocDStar q Λ m ν B / Real.sqrt (B * ocTauPP α q Λ m) := by
    unfold ocDStar
    exact div_nonneg (mul_nonneg he.le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hr : 0 ≤ ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m) :=
    div_nonneg he.le (Real.sqrt_nonneg _)
  have hcount := obsPulses_card_le α q hΛ1 m tp hT.le
  have hwin := window_le hE hE1 hTle
  rw [compBill_eq]
  exact billShape_le hE hE1 hδ hγq hC₀pos hcb hT₀ ha hb₁ hεc hL.εc_le hr hL.eR_le
    hL.contrast_le hℓ hL.ell_inv_le hτ hL.tau_inv_le hL.quiet_ge hT.le hwin
    (Nat.cast_nonneg _) hcount hAc' hNc' hJc' hpc' hn

/-- **Clause 5 of `cycle_comparison`: the bill bound.** After `Λ ≥ Λ₀`, the accuracy and the
window exponent, finite thresholds for the orders `(A', N', J', p')`; for all larger orders and
every decay constant `c > 0`, one constant `C` bounds the bill of every observation window of
algebraic length, at every level `2 ≤ m ≤ M'` of every band chain, by `C E^P`. -/
theorem bill_bound (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s)
    (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ)
    (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ Pacc : ℝ, 0 < Pacc → ∀ Aobs Cobs : ℝ,
      ∃ Ac₀ Nc₀ Jc₀ pc₀ : ℕ, ∀ Ac Nc Jc pc : ℕ, Ac₀ ≤ Ac → Nc₀ ≤ Nc → Jc₀ ≤ Jc → pc₀ ≤ pc →
        ∀ cb : ℝ, 0 < cb → ∃ C : ℝ, 0 ≤ C ∧
          ∀ (M' : ℕ) (κ : ℕ → ℝ), IsOCBandChain α q Λ ζ M' κ → ∀ m : ℕ, 2 ≤ m → m ≤ M' →
          ∀ ν B : ℝ, κ m = ν → κ (m - 1) = B → ∀ tp Tobs : ℝ, 0 < Tobs →
            Tobs ≤ Cobs * ocEpsilon q Λ (m - 1) ^ (-Aobs) →
            compBill α q Λ m ν B Tobs cb (ocObsPulses α q Λ m tp (tp + Tobs)).card
                Ac Nc Jc pc ≤
              C * ocEpsilon q Λ (m - 1) ^ Pacc := by
  obtain ⟨C₀, hC₀, Λ₀, hΛ₀, hlaws⟩ := scale_laws α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ Pacc _hP Aobs Cobs
  obtain ⟨Ac₀, Nc₀, Jc₀, pc₀, hord⟩ :=
    bill_bound_of_scaleLaws α s hα₀ hα₁ hs₀ hs₁ q hq Λ (hΛ₀.trans hΛ) C₀ hC₀ Pacc Aobs Cobs
  refine ⟨Ac₀, Nc₀, Jc₀, pc₀, ?_⟩
  intro Ac Nc Jc pc hAc hNc hJc hpc cb hcb
  obtain ⟨C, hC, hbill⟩ := hord Ac Nc Jc pc hAc hNc hJc hpc cb hcb
  refine ⟨C, hC, ?_⟩
  intro M' κ hband m hm2 hmM ν B hν hB tp Tobs hT hTle
  exact hbill m ν B (hlaws Λ hΛ M' κ hband m hm2 hmM ν B hν hB) tp Tobs hT hTle

end AVRegularity.CycleComparison.Assembly
end
end
