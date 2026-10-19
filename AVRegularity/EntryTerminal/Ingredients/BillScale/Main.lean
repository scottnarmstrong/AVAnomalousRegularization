-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Assembly.BillBound
import AVRegularity.CycleReference.TorusChartEquation
public import AVRegularity.EntryTerminal.Assembly.Route.EntryTerminalOfWeak
import AVRegularity.Construction.Scales.Times
import AVRegularity.Construction.Stream.NextAdmissible
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
namespace AVRegularity.EntryTerminal.BillScale

/-! Abstract-real bound of the terminal bill.

The bill `𝔅_T` of the terminal passage is written for abstract reals: `E` (the base scale),
`x` (with `x ≤ K E^q`), `r = x/ρ`, `w = r_w/ρ`, `εT = ε_T`, `k = √(B/ν)`, `ℓ`, `τ`, and the window
length `T`. Each of them is only assumed to satisfy a power-law bound in `E`. The constant `Cd` is
chosen before all scales (it depends on the power-law constants, the window bound, `c_gap` and
`C_g`). No construction definition appears here.

Special cases: `T ≤ 0` (the square roots are zero in Lean; the bound uses `max T 0`);
`C_g ≤ 0` (the last term is nonpositive); the least admissible orders (every exponent hypothesis
is a non-strict inequality `P ≤ …`, so equality is allowed). -/

section
open AVRegularity.CycleComparison.Assembly

/-- A natural power of a power-law bound with a large enough exponent. -/
theorem pow_le_powerLaw {E K a P x : ℝ} {n : ℕ} (hE : 0 < E) (hE1 : E ≤ 1) (hx : 0 ≤ x)
    (hK : 0 ≤ K) (hxK : x ≤ K * E ^ a) (hP : P ≤ a * n) : x ^ n ≤ K ^ n * E ^ P :=
  (powerLaw_pow hE hx hxK n).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hE hE1 hP) (pow_nonneg hK n))

/-- A real power of a power-law bound with a large enough exponent. -/
theorem rpow_le_powerLaw {E K q P x c : ℝ} (hE : 0 < E) (hE1 : E ≤ 1) (hx : 0 ≤ x)
    (hK : 0 ≤ K) (hxK : x ≤ K * E ^ q) (hc : 0 ≤ c) (hP : P ≤ q * c) :
    x ^ c ≤ K ^ c * E ^ P := by
  have h1 : x ^ c ≤ (K * E ^ q) ^ c := Real.rpow_le_rpow hx hxK hc
  rw [Real.mul_rpow hK (Real.rpow_nonneg hE.le q), ← Real.rpow_mul hE.le] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hE hE1 hP)
    (Real.rpow_nonneg hK c))

/-- The square root only sees the positive part. -/
theorem sqrt_eq_sqrt_max (T : ℝ) : Real.sqrt T = Real.sqrt (max T 0) := by
  rcases le_total T 0 with h | h
  · rw [max_eq_right h, Real.sqrt_zero]
    exact Real.sqrt_eq_zero_of_nonpos h
  · rw [max_eq_left h]

/-- The closure factor `Z` is bounded. -/
theorem closure_factor_le {E K a ζ r ℓ T T₀ : ℝ} {Ac : ℕ} (hE : 0 < E) (hE1 : E ≤ 1)
    (hK : 0 ≤ K) (hT₀ : 0 ≤ T₀) (hℓ : 0 < ℓ) (hℓi : ℓ⁻¹ ≤ K * E ^ (-a))
    (hr : 0 ≤ r) (hrK : r ≤ K * E ^ ζ) (hA : a ≤ ζ * Ac) (hT : T ≤ T₀) :
    Real.sqrt T / ℓ * r ^ Ac ≤ (1 + T₀) * K * K ^ Ac := by
  rw [sqrt_eq_sqrt_max T]
  exact billZ_le (a := 0) (a₁ := a) (g := ζ) hE hE1 hK le_rfl hT₀ (le_max_right _ _)
    (by simpa only [neg_zero, Real.rpow_zero, mul_one] using max_le hT hT₀) hℓ hℓi hr hrK
    (by simpa only [zero_add] using hA)

/-- The quiet term of the bill, with the factor `C E^{-C}`. -/
theorem quiet_term_le {E K b δ cgap C T₀ ℓ τ T : ℝ} {n : ℕ} (hE : 0 < E) (hE1 : E ≤ 1)
    (hK : 1 ≤ K) (hb : 0 ≤ b) (hδ : 0 < δ) (hcgap : 0 < cgap) (hC : 0 ≤ C) (hT₀ : 0 ≤ T₀)
    (hℓ : 0 < ℓ) (hτ : 0 < τ) (hτi : τ⁻¹ ≤ K * E ^ (-b))
    (hq : K⁻¹ * E ^ (-(4 * δ)) ≤ τ / ℓ ^ 2) (hT : T ≤ T₀) {P : ℝ}
    (hn : P + C + b ≤ 4 * δ * n) :
    C * E ^ (-C) * ℓ * Real.sqrt ((1 + T / τ) / (cgap * τ)) * Real.exp (-(cgap * τ / ℓ ^ 2)) ≤
      C * ((1 + 5 * K * (1 + T₀ * K)) * (K ^ n * (n.factorial : ℝ) / cgap ^ n) /
        Real.sqrt cgap) * E ^ P := by
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hT' : 0 ≤ max T 0 := le_max_right _ _
  have hT'le : max T 0 ≤ T₀ * E ^ (-(0 : ℝ)) := by
    simpa only [neg_zero, Real.rpow_zero, mul_one] using max_le hT hT₀
  have hBp0 : 0 ≤ 1 + max T 0 / τ := by positivity
  have hBp : 1 + max T 0 / τ ≤ 5 * (1 + T₀ * K) * E ^ (-((0 : ℝ) + b)) :=
    pulseCount_le_powerLaw hE hE1 le_rfl hb hT' hT'le hτ hτi (by linarith only [hBp0])
  have h3 := bill_third_le (P := P + C) (cb := cgap) (a := 0) (b₁ := b) hE hE1 hδ.le hK0 hcgap
    hT₀ (by simpa only [zero_add] using hb) hℓ hτ hBp0 hBp hq (by linarith only [hn])
  have hsq : Real.sqrt ((1 + T / τ) / (cgap * τ)) ≤
      Real.sqrt ((1 + max T 0 / τ) / τ) / Real.sqrt cgap := by
    rw [← Real.sqrt_div' _ hcgap.le]
    apply Real.sqrt_le_sqrt
    rw [show (1 + T / τ) / (cgap * τ) = ((1 + T / τ) / τ) / cgap by field_simp,
      show (1 + max T 0 / τ) / τ / cgap = ((1 + max T 0 / τ) / τ) / cgap from rfl]
    apply div_le_div_of_nonneg_right _ hcgap.le
    apply div_le_div_of_nonneg_right _ hτ.le
    have : T / τ ≤ max T 0 / τ := div_le_div_of_nonneg_right (le_max_left _ _) hτ.le
    linarith only [this]
  have hexp := (Real.exp_pos (-(cgap * τ / ℓ ^ 2))).le
  have hCE : 0 ≤ C * E ^ (-C) := mul_nonneg hC (Real.rpow_nonneg hE.le _)
  calc C * E ^ (-C) * ℓ * Real.sqrt ((1 + T / τ) / (cgap * τ)) * Real.exp (-(cgap * τ / ℓ ^ 2))
      = C * E ^ (-C) * (ℓ * Real.sqrt ((1 + T / τ) / (cgap * τ)) *
          Real.exp (-(cgap * τ / ℓ ^ 2))) := by ring
    _ ≤ C * E ^ (-C) * (ℓ * (Real.sqrt ((1 + max T 0 / τ) / τ) / Real.sqrt cgap) *
          Real.exp (-(cgap * τ / ℓ ^ 2))) := by
        apply mul_le_mul_of_nonneg_left _ hCE
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hℓ.le) hexp
    _ = C * E ^ (-C) * ((ℓ * Real.sqrt ((1 + max T 0 / τ) / τ) *
          Real.exp (-(cgap * τ / ℓ ^ 2))) / Real.sqrt cgap) := by ring
    _ ≤ C * E ^ (-C) * (((1 + 5 * K * (1 + T₀ * K)) * (K ^ n * (n.factorial : ℝ) / cgap ^ n) *
          E ^ (P + C)) / Real.sqrt cgap) := by
        apply mul_le_mul_of_nonneg_left _ hCE
        apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
        exact h3
    _ = C * ((1 + 5 * K * (1 + T₀ * K)) * (K ^ n * (n.factorial : ℝ) / cgap ^ n) /
          Real.sqrt cgap) * E ^ P := by
        have : E ^ (-C) * E ^ (P + C) = E ^ P := by
          rw [← Real.rpow_add hE]; congr 1; ring
        calc _ = C * ((1 + 5 * K * (1 + T₀ * K)) * (K ^ n * (n.factorial : ℝ) / cgap ^ n) /
              Real.sqrt cgap) * (E ^ (-C) * E ^ (P + C)) := by ring
          _ = _ := by rw [this]
end

/-! The abstract terminal bill bound, assembled from the term-by-term lemmas of `Abstract`.

The bill is `εT^N (1+Z) + (k + εT² (1+Z)) (E^{e₁} + E^{e₂} + E^{e₃} + x^χ w^{Lo})
 + x^{χ+σ Lf} + C_g E^{-C_g} ℓ √(B_p/d_gap) exp(-d_gap/ℓ²)` with `Z = (√T/ℓ) r^{Ac}`,
`B_p = 1 + T/τ`, `d_gap = c_gap τ`. -/

section
open AVRegularity.CycleComparison.Assembly

/-- The `x`-dependent bracket term `x^χ w^{Lo}`. -/
theorem fresh_tail_le {E K q ζ σ χ P x w : ℝ} {Lo : ℕ} (hE : 0 < E) (hE1 : E ≤ 1)
    (hx : 0 ≤ x) (hK : 0 ≤ K) (hxK : x ≤ K * E ^ q) (hw : 0 ≤ w)
    (hwK : w ≤ K * E ^ (ζ + q * σ)) (hχ : 0 ≤ χ)
    (hP : P ≤ q * χ + (ζ + q * σ) * Lo) :
    x ^ χ * w ^ Lo ≤ K ^ χ * K ^ Lo * E ^ P := by
  have h1 := rpow_le_powerLaw (P := q * χ) hE hE1 hx hK hxK hχ le_rfl
  have h2 := pow_le_powerLaw (P := (ζ + q * σ) * Lo) (n := Lo) hE hE1 hw hK hwK le_rfl
  have h3 := powerLaw_mul hE (Real.rpow_nonneg hx χ) (pow_nonneg hw Lo)
    (h1.trans_eq (by ring) : x ^ χ ≤ K ^ χ * E ^ (q * χ)) h2
  exact h3.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hE hE1 hP)
    (mul_nonneg (Real.rpow_nonneg hK χ) (pow_nonneg hK Lo)))

/-- The scale-independent constant of the bound. -/
def billCd (K T₀ cgap Cg χ σ : ℝ) (N Ac Lo Lf n : ℕ) : ℝ :=
  K ^ N * (1 + (1 + T₀) * K * K ^ Ac) +
    (K + K ^ 2 * (1 + (1 + T₀) * K * K ^ Ac)) * (3 + K ^ χ * K ^ Lo) +
    K ^ (χ + σ * Lf) +
    max Cg 0 * ((1 + 5 * K * (1 + T₀ * K)) * (K ^ n * (n.factorial : ℝ) / cgap ^ n) /
      Real.sqrt cgap)

theorem billCd_nonneg {K T₀ cgap Cg χ σ : ℝ} {N Ac Lo Lf n : ℕ} (hK : 1 ≤ K)
    (hT₀ : 0 ≤ T₀) (hcgap : 0 < cgap) :
    0 ≤ billCd K T₀ cgap Cg χ σ N Ac Lo Lf n := by
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  unfold billCd
  have : 0 ≤ max Cg 0 := le_max_right _ _
  positivity

/-- **The abstract terminal bill bound.** -/
theorem term_bill_le_abstract (P δ ζ q σ χ b a bT tT cgap Cg T₀ K : ℝ)
    (N p R Ac Lc Lo Lf : ℕ) (hδ : 0 < δ) (hζ : 0 ≤ ζ) (hσ : 0 ≤ σ) (hχ : 0 ≤ χ)
    (hb : 0 ≤ b) (hcgap : 0 < cgap) (hT₀ : 0 ≤ T₀) (hK : 1 ≤ K)
    (hN : P ≤ ζ * N) (hR : P ≤ δ * ((R : ℝ) + 1) / 2) (hp : P ≤ δ * p)
    (hLc : P ≤ bT + tT * Lc) (hLo : P ≤ q * χ + (ζ + q * σ) * Lo)
    (hLf : P ≤ q * (χ + σ * Lf)) (hA : a ≤ ζ * Ac) :
    ∃ n : ℕ, ∀ E x r w εT k ℓ τ T : ℝ, 0 < E → E ≤ 1 → 0 ≤ x → x ≤ K * E ^ q →
      0 ≤ r → r ≤ K * E ^ ζ → 0 ≤ w → w ≤ K * E ^ (ζ + q * σ) → 0 ≤ εT → εT ≤ K * E ^ ζ →
      0 ≤ k → k ≤ K → 0 < ℓ → ℓ⁻¹ ≤ K * E ^ (-a) → 0 < τ → τ⁻¹ ≤ K * E ^ (-b) →
      K⁻¹ * E ^ (-(4 * δ)) ≤ τ / ℓ ^ 2 → T ≤ T₀ →
      εT ^ N * (1 + Real.sqrt T / ℓ * r ^ Ac) +
        (k + εT ^ 2 * (1 + Real.sqrt T / ℓ * r ^ Ac)) *
          (E ^ (δ * ((R : ℝ) + 1) / 2) + E ^ (δ * p) + E ^ (bT + tT * Lc) + x ^ χ * w ^ Lo) +
        x ^ (χ + σ * Lf) +
        Cg * E ^ (-Cg) * ℓ * Real.sqrt ((1 + T / τ) / (cgap * τ)) *
          Real.exp (-(cgap * τ / ℓ ^ 2)) ≤
      billCd K T₀ cgap Cg χ σ N Ac Lo Lf n * E ^ P := by
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  obtain ⟨n, hn⟩ := exists_nat_ge ((P + max Cg 0 + b) / (4 * δ))
  have hn' : P + max Cg 0 + b ≤ 4 * δ * n := by
    simpa only [mul_comm] using (div_le_iff₀ (by positivity : 0 < 4 * δ)).mp hn
  refine ⟨n, ?_⟩
  intro E x r w εT k ℓ τ T hE hE1 hx hxK hr hrK hw hwK hε hεK hk hkK hℓ hℓi hτ hτi hq hT
  have hE0 := hE.le
  have hEP : 0 ≤ E ^ P := Real.rpow_nonneg hE0 P
  set Z := Real.sqrt T / ℓ * r ^ Ac with hZdef
  set Zc := (1 + T₀) * K * K ^ Ac with hZc
  have hZ0 : 0 ≤ Z := mul_nonneg (div_nonneg (Real.sqrt_nonneg _) hℓ.le) (pow_nonneg hr _)
  have hZ : Z ≤ Zc := closure_factor_le hE hE1 hK0.le hT₀ hℓ hℓi hr hrK hA hT
  -- term 1
  have h1 : εT ^ N * (1 + Z) ≤ K ^ N * (1 + Zc) * E ^ P := by
    have := pow_le_powerLaw (n := N) hE hE1 hε hK0.le hεK hN
    calc εT ^ N * (1 + Z) ≤ (K ^ N * E ^ P) * (1 + Zc) :=
          mul_le_mul this (by linarith only [hZ]) (by linarith only [hZ0]) (by positivity)
      _ = _ := by ring
  -- the bracket
  have hbr : E ^ (δ * ((R : ℝ) + 1) / 2) + E ^ (δ * p) + E ^ (bT + tT * Lc) + x ^ χ * w ^ Lo ≤
      (3 + K ^ χ * K ^ Lo) * E ^ P := by
    have e1 := Real.rpow_le_rpow_of_exponent_ge hE hE1 hR
    have e2 := Real.rpow_le_rpow_of_exponent_ge hE hE1 hp
    have e3 := Real.rpow_le_rpow_of_exponent_ge hE hE1 hLc
    have e4 := fresh_tail_le hE hE1 hx hK0.le hxK hw hwK hχ hLo
    linarith only [e1, e2, e3, e4]
  have hbr0 : 0 ≤ E ^ (δ * ((R : ℝ) + 1) / 2) + E ^ (δ * p) + E ^ (bT + tT * Lc) + x ^ χ * w ^ Lo := by
    have := Real.rpow_nonneg hE0 (δ * ((R : ℝ) + 1) / 2)
    have := Real.rpow_nonneg hE0 (δ * p)
    have := Real.rpow_nonneg hE0 (bT + tT * Lc)
    have := mul_nonneg (Real.rpow_nonneg hx χ) (pow_nonneg hw Lo)
    linarith only [‹0 ≤ E ^ (δ * ((R : ℝ) + 1) / 2)›, ‹0 ≤ E ^ (δ * p)›,
      ‹0 ≤ E ^ (bT + tT * Lc)›, this]
  have hEζ : E ^ ζ ≤ 1 := Real.rpow_le_one hE0 hE1 hζ
  have hεK' : εT ≤ K := hεK.trans (by nlinarith only [hEζ, hK0])
  have h2 : (k + εT ^ 2 * (1 + Z)) *
      (E ^ (δ * ((R : ℝ) + 1) / 2) + E ^ (δ * p) + E ^ (bT + tT * Lc) + x ^ χ * w ^ Lo) ≤
      (K + K ^ 2 * (1 + Zc)) * (3 + K ^ χ * K ^ Lo) * E ^ P := by
    have hε2 : εT ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ hε hεK' 2
    have hfac : k + εT ^ 2 * (1 + Z) ≤ K + K ^ 2 * (1 + Zc) :=
      add_le_add hkK (mul_le_mul hε2 (by linarith only [hZ]) (by linarith only [hZ0])
        (by positivity))
    calc _ ≤ (K + K ^ 2 * (1 + Zc)) * ((3 + K ^ χ * K ^ Lo) * E ^ P) :=
          mul_le_mul hfac hbr hbr0 (by positivity)
      _ = _ := by ring
  have h3 : x ^ (χ + σ * Lf) ≤ K ^ (χ + σ * Lf) * E ^ P :=
    rpow_le_powerLaw hE hE1 hx hK0.le hxK (by positivity) hLf
  have h4 : Cg * E ^ (-Cg) * ℓ * Real.sqrt ((1 + T / τ) / (cgap * τ)) *
      Real.exp (-(cgap * τ / ℓ ^ 2)) ≤
      max Cg 0 * ((1 + 5 * K * (1 + T₀ * K)) * (K ^ n * (n.factorial : ℝ) / cgap ^ n) /
        Real.sqrt cgap) * E ^ P := by
    have hKq : 0 ≤ max Cg 0 * ((1 + 5 * K * (1 + T₀ * K)) *
        (K ^ n * (n.factorial : ℝ) / cgap ^ n) / Real.sqrt cgap) := by positivity
    rcases le_or_gt Cg 0 with hC | hC
    · have hneg : Cg * E ^ (-Cg) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hC (Real.rpow_nonneg hE0 _)
      have hrest : 0 ≤ ℓ * Real.sqrt ((1 + T / τ) / (cgap * τ)) *
          Real.exp (-(cgap * τ / ℓ ^ 2)) :=
        mul_nonneg (mul_nonneg hℓ.le (Real.sqrt_nonneg _)) (Real.exp_pos _).le
      calc _ = (Cg * E ^ (-Cg)) * (ℓ * Real.sqrt ((1 + T / τ) / (cgap * τ)) *
            Real.exp (-(cgap * τ / ℓ ^ 2))) := by ring
        _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg hrest
        _ ≤ _ := mul_nonneg hKq hEP
    · have := quiet_term_le (C := Cg) (P := P) hE hE1 hK hb hδ hcgap hC.le hT₀ hℓ hτ hτi hq hT
        (n := n) (by rw [max_eq_left hC.le] at hn'; exact hn')
      rwa [max_eq_left hC.le]
  unfold billCd
  calc _ ≤ K ^ N * (1 + Zc) * E ^ P + (K + K ^ 2 * (1 + Zc)) * (3 + K ^ χ * K ^ Lo) * E ^ P +
        K ^ (χ + σ * Lf) * E ^ P + max Cg 0 * ((1 + 5 * K * (1 + T₀ * K)) *
          (K ^ n * (n.factorial : ℝ) / cgap ^ n) / Real.sqrt cgap) * E ^ P :=
        add_le_add (add_le_add (add_le_add h1 h2) h3) h4
    _ = _ := by ring
end

/-! The physical scale facts of the terminal passage `M → M-1`, from the diffusivity
ledger and the scale laws at the terminal level `m = M`.

With `E = ε_{M-1}`, `x = ε_M`, `ρ = c_r √(Bh)`, `ℓ = x/√ν`, `ζ = qγ + 3δ`, the facts are
`x ≤ K E^q`, `x/ρ ≤ K E^ζ`, `ε_T = d_*/ρ ≤ K E^ζ`, `r_w/ρ ≤ K E^{ζ+qσ_w}`, `√(B/ν) ≤ K`,
`ℓ⁻¹ ≤ K E^{-a}`, `τ⁻¹ ≤ K E^{-b}`, `K⁻¹ E^{-4δ} ≤ τ/ℓ²`. The last two are scale laws at
`m = M`; `√(B/ν) ≤ K` is the terminal clause `m = M → B/ν ≤ C` of the ledger.

Special cases: `σ_w = 0` is allowed; `c_r = 1` is allowed; the constant `K` depends on
`c_r` and `σ_w` and is chosen before the level `M`. -/

section
open AVRegularity AVRegularity.CycleComparison.Assembly AVRegularity.CycleReference
open AVRegularity.CycleComparison.Assembly (powerLaw_mul)

/-- A power-law bound with a smaller constant has the larger constant too. -/
theorem le_of_const_le {E C K x a : ℝ} (hE : 0 < E) (hC : C ≤ K)
    (hx : x ≤ C * E ^ a) : x ≤ K * E ^ a :=
  hx.trans (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hE.le _))

/-- The terminal scale facts, bundled. -/
structure TermScaleFacts (D : OCData) (M : ℕ) (cr σ K a b : ℝ) (α q : ℝ) (Λ : ℕ) : Prop where
  E_pos : 0 < D.eps (M - 1)
  E_le_one : D.eps (M - 1) ≤ 1
  x_nonneg : 0 ≤ D.eps M
  x_le : D.eps M ≤ K * D.eps (M - 1) ^ q
  r_nonneg : 0 ≤ D.eps M / D.termRho cr M
  r_le : D.eps M / D.termRho cr M ≤
    K * D.eps (M - 1) ^ (q * ocGamma α q + 3 * ocDelta α q)
  w_nonneg : 0 ≤ D.termRW σ M / D.termRho cr M
  w_le : D.termRW σ M / D.termRho cr M ≤
    K * D.eps (M - 1) ^ ((q * ocGamma α q + 3 * ocDelta α q) + q * σ)
  εT_nonneg : 0 ≤ D.termEpsCell cr M
  εT_le : D.termEpsCell cr M ≤ K * D.eps (M - 1) ^ (q * ocGamma α q + 3 * ocDelta α q)
  k_nonneg : 0 ≤ Real.sqrt (D.termB M / D.termNu M)
  k_le : Real.sqrt (D.termB M / D.termNu M) ≤ K
  ell_pos : 0 < Real.sqrt (D.termEllSq M)
  ell_inv_le : (Real.sqrt (D.termEllSq M))⁻¹ ≤ K * D.eps (M - 1) ^ (-a)
  tau_pos : 0 < ocTau α q Λ M
  tau_inv_le : (ocTau α q Λ M)⁻¹ ≤ K * D.eps (M - 1) ^ (-b)
  quiet_ge : K⁻¹ * D.eps (M - 1) ^ (-(4 * ocDelta α q)) ≤
    ocTau α q Λ M / Real.sqrt (D.termEllSq M) ^ 2

/-- The exponents `a` and `b` of the inverse cell length and the inverse pulse time. -/
def cellExp (α q : ℝ) : ℝ :=
  q * ocGamma α q + 3 * ocDelta α q + (1 + (ocGamma α q / 2 + ocDelta α q))

/-- The exponent `b` of the inverse pulse time. -/
def pulseExp (α q : ℝ) : ℝ := 2 - (1 + α) + 4 * ocDelta α q

/-- **The terminal scale facts**, uniform in the level. -/
theorem term_scale_facts {α s q : ℝ} {ζf : ℝ → ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (hζ : IsFastProfile ζf) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ cr σ : ℝ, 0 < cr → cr ≤ 1 → 0 ≤ σ →
      ∃ K : ℝ, 1 ≤ K ∧ ∀ M : ℕ, 2 ≤ M → ∀ D : OCData, D.α = α → D.q = q → D.Λ = Λ →
        IsOCBandChain α q Λ ζf M D.κ →
        TermScaleFacts D M cr σ K (cellExp α q) (pulseExp α q) α q Λ := by
  obtain ⟨Cl, hCl, Ll, hLl, hled⟩ := bandChain_uniform_ledger hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Cs, hCs, Ls, hLs, hsl⟩ := scale_laws α s hα0 hα1 hs0 hs1 q hq ζf hζ
  refine ⟨max Ll Ls, hLl.trans (le_max_left _ _), ?_⟩
  intro Λ hΛ cr σ hcr hcr1 hσ
  have hΛl : Ll ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛs : Ls ≤ Λ := (le_max_right _ _).trans hΛ
  have h128 : 128 ≤ Λ := hLl.trans hΛl
  have hCl0 : 0 < Cl := zero_lt_one.trans_le hCl
  have hCs0 : 0 < Cs := zero_lt_one.trans_le hCs
  have hcrinv : 0 ≤ Cl / cr := (div_pos hCl0 hcr).le
  refine ⟨2 + Cl + Cs + Cl ^ 2 / cr + 2 ^ σ * Cl / cr + Cl / cr, ?_, ?_⟩
  · have h1 : 0 ≤ Cl ^ 2 / cr := by positivity
    have h2 : 0 ≤ 2 ^ σ * Cl / cr := by positivity
    linarith only [hCl, hCs, h1, h2, hcrinv]
  intro M hM D hDα hDq hDΛ hband
  set K := 2 + Cl + Cs + Cl ^ 2 / cr + 2 ^ σ * Cl / cr + Cl / cr with hKdef
  have hn1 : 0 ≤ Cl ^ 2 / cr := by positivity
  have hn2 : 0 ≤ 2 ^ σ * Cl / cr := by positivity
  have hKCl : Cl ≤ K := by linarith only [hCs0, hn1, hn2, hcrinv]
  have hKCs : Cs ≤ K := by linarith only [hCl0, hn1, hn2, hcrinv]
  have hK2 : 2 ≤ K := by linarith only [hCl0, hCs0, hn1, hn2, hcrinv]
  have hKr : Cl / cr ≤ K := by linarith only [hCl0, hCs0, hn1, hn2]
  have hKe : Cl ^ 2 / cr ≤ K := by linarith only [hCl0, hCs0, hn2, hcrinv]
  have hKw : 2 ^ σ * Cl / cr ≤ K := by linarith only [hCl0, hCs0, hn1, hcrinv]
  have hK0 : 0 < K := by linarith only [hK2]
  have hmM : 2 ≤ M := hM
  have hE := (Scales.epsilon_basic (m := M - 1) hq.1 h128).1
  have hE1 := (Scales.epsilon_basic (m := M - 1) hq.1 h128).2.1
  have he := (Scales.epsilon_basic (m := M) hq.1 h128).1
  have hled' := (hled Λ hΛl M (by omega) D.κ hband).2 M hmM le_rfl (D.κ M) (D.κ (M - 1)) rfl rfl
  obtain ⟨_, _, _, _, _, _, _, _, her, _, _, _, _, _, hBν, _⟩ := hled'
  have hsl' := hsl Λ hΛs M D.κ hband M hmM le_rfl (D.κ M) (D.κ (M - 1)) rfl rfl
  have hxe : D.eps M = ocEpsilon q Λ M := by simp only [OCData.eps, hDq, hDΛ]
  have hEe : D.eps (M - 1) = ocEpsilon q Λ (M - 1) := by simp only [OCData.eps, hDq, hDΛ]
  have hρ : D.termRho cr M = cr * ocRh α q Λ M (D.κ (M - 1)) := by
    simp only [OCData.termRho, OCData.termB, OCData.termH, ocRh, hDα, hDq, hDΛ]
  have hℓ : Real.sqrt (D.termEllSq M) = ocEll q Λ M (D.κ M) := by
    rw [OCData.termEllSq, OCData.termNu, OCData.eps, hDq, hDΛ,
      Real.sqrt_div (sq_nonneg _), Real.sqrt_sq he.le]
    rfl
  have hk : Real.sqrt (D.termB M / D.termNu M) = Real.sqrt (D.κ (M - 1) / D.κ M) := rfl
  have hR0 : 0 ≤ ocRh α q Λ M (D.κ (M - 1)) := Real.sqrt_nonneg _
  have hx0 : 0 < D.eps M := by rw [hxe]; exact he
  have hr_eq : D.eps M / D.termRho cr M =
      (ocEpsilon q Λ M / ocRh α q Λ M (D.κ (M - 1))) / cr := by
    rw [hxe, hρ, div_div, mul_comm]
  have hr0 : 0 ≤ D.eps M / D.termRho cr M := by
    rw [hr_eq]; exact div_nonneg (div_nonneg he.le hR0) hcr.le
  have hr_le0 : D.eps M / D.termRho cr M ≤
      Cl / cr * D.eps (M - 1) ^ (q * ocGamma α q + 3 * ocDelta α q) := by
    rw [hr_eq, hEe]
    calc _ ≤ (Cl * ocEpsilon q Λ (M - 1) ^ (q * ocGamma α q + 3 * ocDelta α q)) / cr :=
          div_le_div_of_nonneg_right her.2 hcr.le
      _ = _ := by ring
  have hxK2 : D.eps M ≤ 2 * D.eps (M - 1) ^ q := by
    rw [hxe, hEe]; exact Scales.epsilon_q_step hq.1 hq.2.1 h128 (by omega)
  have hw_eq : D.termRW σ M / D.termRho cr M = D.eps M ^ σ * (D.eps M / D.termRho cr M) := by
    rw [OCData.termRW, Real.rpow_add hx0, Real.rpow_one]; ring
  have hk_le : Real.sqrt (D.termB M / D.termNu M) ≤ Cl := by
    rw [hk]
    exact Real.sqrt_le_iff.mpr ⟨hCl0.le, (hBν rfl).trans (by nlinarith only [hCl])⟩
  have hk0 : 0 ≤ Real.sqrt (D.termB M / D.termNu M) := Real.sqrt_nonneg _
  have hεeq : D.termEpsCell cr M =
      D.eps M / D.termRho cr M * Real.sqrt (D.termB M / D.termNu M) := by
    rw [OCData.termEpsCell, OCData.termDstar, mul_div_right_comm]
  have hEpos : 0 < D.eps (M - 1) := by rw [hEe]; exact hE
  have hE1' : D.eps (M - 1) ≤ 1 := by rw [hEe]; exact hE1
  refine ⟨hEpos, hE1', hx0.le, le_of_const_le hEpos hK2 hxK2, hr0,
    le_of_const_le hEpos hKr hr_le0, ?_, ?_, ?_, ?_, hk0, hk_le.trans hKCl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hw_eq]; exact mul_nonneg (Real.rpow_nonneg hx0.le _) hr0
  · rw [hw_eq]
    have h1 := rpow_le_powerLaw (P := q * σ) hEpos hE1' hx0.le (by norm_num : (0 : ℝ) ≤ 2)
      hxK2 hσ le_rfl
    have h2 := powerLaw_mul hEpos (Real.rpow_nonneg hx0.le σ) hr0 h1 hr_le0
    rw [add_comm (q * σ)] at h2
    refine le_of_const_le hEpos ?_ h2
    calc 2 ^ σ * (Cl / cr) = 2 ^ σ * Cl / cr := by ring
      _ ≤ K := hKw
  · rw [hεeq]; exact mul_nonneg hr0 hk0
  · rw [hεeq]
    have h2 := (mul_le_mul hr_le0 hk_le hk0 (by positivity)).trans_eq
      (mul_right_comm (Cl / cr) (D.eps (M - 1) ^ (q * ocGamma α q + 3 * ocDelta α q)) Cl)
    refine le_of_const_le hEpos ?_ h2
    calc Cl / cr * Cl = Cl ^ 2 / cr := by ring
      _ ≤ K := hKe
  · rw [hℓ]; exact div_pos he (Real.sqrt_pos.mpr hsl'.ν_pos)
  · rw [hℓ, hEe]; exact le_of_const_le hE hKCs hsl'.ell_inv_le
  · exact AVRegularity.Construction.Stream.ocTau_pos (by omega)
  · rw [hEe]; exact le_of_const_le hE hKCs hsl'.tau_inv_le
  · rw [hℓ, hEe]
    exact (mul_le_mul_of_nonneg_right (inv_anti₀ hCs0 hKCs)
      (Real.rpow_nonneg hE.le _)).trans hsl'.quiet_ge
end

/-! **The terminal bill scale**:
`termBill ≤ C_d E^{Q_T+2}` for every large level, every window of length at most `T₀`.

The scalar proof is `term_bill_le_abstract`; the scale facts are `term_scale_facts`; this module
checks the numerical order hypotheses against `IsTerminalSchedule` and matches the two.

Special cases: `t_p = t_f` (`Z_cl = 0`, `B_p = 1`), `C_g ≤ 0` (the last term is nonpositive),
`t_f < t_p` (the square roots are zero), `ζ N_T` just above `Q_T + 2` (the abstract hypotheses are
non-strict). -/

section
open AVRegularity AVRegularity.EntryTerminal.Route

/-- The exponent `qγ+3δ+1+γ/2+δ` of the inverse cell length is at most three. -/
theorem cellExp_le_three {α s q : ℝ} (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s)
    (hs1 : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) : cellExp α q ≤ 3 := by
  have hf := Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq
  have hγ0 := hf.1
  have hδ0 := hf.2.1
  obtain ⟨hq1, hq2, -, -⟩ := hq
  have hγ : ocGamma α q ≤ 1 / 2 := by
    unfold ocGamma
    rw [div_le_iff₀ (by linarith)]
    nlinarith only [hq1, hq2, hα0, hα1]
  have hδ : ocDelta α q ≤ 1 / 8 := by
    unfold ocDelta
    have hF : 1 - (2 * q + 1) * (1 + α) / (2 * q + 2) ≤ 1 := by
      have : 0 ≤ (2 * q + 1) * (1 + α) / (2 * q + 2) := by positivity
      linarith only [this]
    have hF0 : 0 ≤ 1 - (2 * q + 1) * (1 + α) / (2 * q + 2) := by
      by_contra hneg
      have : (q - 1) / 4 * (1 - (2 * q + 1) * (1 + α) / (2 * q + 2)) < 0 :=
        mul_neg_of_pos_of_neg (by linarith) (not_le.mp hneg)
      unfold ocDelta at hδ0
      linarith only [this, hδ0]
    calc (q - 1) / 4 * (1 - (2 * q + 1) * (1 + α) / (2 * q + 2))
        ≤ (q - 1) / 4 * 1 := mul_le_mul_of_nonneg_left hF (by linarith)
      _ ≤ 1 / 8 := by linarith only [hq2]
  unfold cellExp
  nlinarith only [hγ, hδ, hγ0, hδ0, hq1, hq2]

/-- The exponent `2 - β + 4δ` of the inverse pulse time is nonnegative. -/
theorem pulseExp_nonneg {α s q : ℝ} (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s)
    (hs1 : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) : 0 ≤ pulseExp α q := by
  have hδ0 := (Scales.admissible_exponent_facts hα0 hα1 hs0 hs1 hq).2.1
  unfold pulseExp
  linarith only [hα1, hδ0]

/-- **The terminal bill scale.** -/
theorem termBillScale : TermBillScaleStatement := by
  intro X
  have hf := Scales.admissible_exponent_facts X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq
  have hq1 : 1 < X.q := X.hq.1
  obtain ⟨Λ₀, hΛ₀, hfacts⟩ := term_scale_facts X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq X.hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro A hΛ hV cr cgap Cg hcr hcr1 hcgap
  obtain ⟨-, -, -, ⟨-, hτ, hτT, -, hσ, -, hχ, -, -⟩, -, hsched, -, -⟩ := hV
  unfold IsTerminalSchedule at hsched
  dsimp only at hsched
  obtain ⟨-, -, hAT, hNT, hRT, hpT, -, -, -, -, hLc, hLo, hLf, -⟩ := hsched
  have hT₀ : 0 ≤ A.T₀ := by linarith only [hτ, hτT]
  have hδ := hf.2.1
  have hζ : 0 ≤ X.q * ocGamma X.α X.q + 3 * ocDelta X.α X.q := by
    have := hf.1
    have : 0 < X.q * ocGamma X.α X.q := mul_pos (by linarith only [hq1]) this
    linarith only [this, hδ]
  have hA : cellExp X.α X.q ≤ (X.q * ocGamma X.α X.q + 3 * ocDelta X.α X.q) * A.AT := by
    have h3 := cellExp_le_three X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq
    linarith only [h3, hAT]
  obtain ⟨K, hK, hKfacts⟩ := hfacts A.Λ hΛ cr A.σw hcr hcr1 hσ.le
  obtain ⟨n, hn⟩ := term_bill_le_abstract (A.QT + 2) (ocDelta X.α X.q)
    (X.q * ocGamma X.α X.q + 3 * ocDelta X.α X.q) X.q A.σw A.χw (pulseExp X.α X.q)
    (cellExp X.α X.q)
    (ocDelta X.α X.q - A.η₀ - A.η₀ / 4 - A.tT * (termExcess A.NT A.pT
      (termAlphabet A.NT A.pT A.DW A.dW) : ℝ)) A.tT cgap Cg A.T₀ K
    A.NT A.pT A.RT A.AT A.LcT A.LoT A.LfT hδ hζ hσ.le hχ.le
    (pulseExp_nonneg X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq) hcgap hT₀ hK
    hNT.le hRT.le hpT.le hLc.le hLo.le hLf.le hA
  refine ⟨billCd K A.T₀ cgap Cg A.χw A.σw A.NT A.AT A.LoT A.LfT n,
    billCd_nonneg hK hT₀ hcgap, 2, ?_⟩
  intro M hM D hD tp tf htf
  obtain ⟨hDα, hDq, hDΛ, -, -, hband, -⟩ := hD
  have hF := hKfacts M hM D hDα hDq hDΛ hband
  unfold termBill
  rw [hDα, hDq, hDΛ]
  exact hn _ _ _ _ _ _ _ _ _ hF.E_pos hF.E_le_one hF.x_nonneg hF.x_le hF.r_nonneg hF.r_le
    hF.w_nonneg hF.w_le hF.εT_nonneg hF.εT_le hF.k_nonneg hF.k_le hF.ell_pos hF.ell_inv_le
    hF.tau_pos hF.tau_inv_le hF.quiet_ge htf
end

end AVRegularity.EntryTerminal.BillScale
end
