-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.TransverseHsProjection
import AVRegularity.CycleWords.MixedWords.B1WSourceL2
import AVRegularity.CycleDamping.ReferenceTimeEquation
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

section
@[expose] public noncomputable section
section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # The `L²` layer of the transverse estimate: the normalized adjoint row from `1`

Let `u` be the reversed (adjoint) curve on `[-B, -A]` from `u(-B) = 1` and
`ℓ(σ) = e^{-∫_σ^B λ} u(-σ)`. Then `⟨1 + r(σ), ℓ(σ)⟩ = 1` (bilinear; `rowCurve_pair`, from the
conserved pairing and `⟨r(B)⟩ = 0`), and `‖ℓ(σ) - 1‖_{L²} ≤ M|ξ|` on the whole window,
uniformly in its length (`rowCurve_l2_of_unit`).

On a unit step, `ℓ(σ+1) - 1` is in the fast class, which decays by `e^{-(4π²/9 - |ξ|²/2)}`
(`revCurve_fast_decay`). The phase over a unit step is at most `e^{π²/4}`
(`scalarPackageSymbol_quadratic_bound` and the separation condition), so the product is at most `1/2`
(`unit_step_half`). The slow part contributes `O(|ξ|)` by (C1). Hence
`‖ℓ(σ) - 1‖ ≤ ½‖ℓ(σ+1) - 1‖ + M₀|ξ|`, and the steps sum to `2M₀|ξ|`. -/

section
variable {K : ScalarConstants} {η t₀ S : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {v : ℝ → Vec 2 → Vec 2} {ξ : Fin 2 → ℂ}

/-- The value of an `H^K` element has `L²` norm at most its norm. -/
theorem torusHk_value_norm_le {k : ℕ} (U : TorusHk k ℂ) : ‖torusHkValueCLM U‖ ≤ ‖U‖ :=
  PiLp.norm_apply_le U.val (valueIndex2 k)

/-- `⟨1 + r(t), 1⟩ = 1`: the graph has mean zero. -/
theorem graph_pair_one (data : FibreScalarData K η G v t₀ S) (hξ : fibreNorm ξ < K.ξ0)
    (t : ℝ) :
    cellComplexPair (cellRawTrace (fibreSeriesJet data.r ξ) t + cellConstantCLM 1)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (cellConstantCLM 1)) = 1 := by
  rw [cellFiberConj_constant, star_one, cellComplexPair_one, ← cellMeanCLM_apply, map_add,
    graphTrace_mean_zero data hξ t, cellMeanCLM_constant, zero_add]

/-- The phase over at most a unit time: `|e^{-∫λ}| ≤ e^{π²/4}` and
`|e^{-∫λ} - 1| ≤ Lρe^{π²/4}|ξ|` with `L = 8 + C_w C_g`. -/
theorem phase_unit_bounds (H : TransverseLocalHyp K η G v ξ)
    (data : FibreScalarData K η G v t₀ S) {ρ : ℝ} (hξρ : fibreNorm ξ ≤ ρ) {s t : ℝ}
    (hst : s ≤ t) (h1 : t ≤ s + 1) :
    ‖Complex.exp (-∫ τ in s..t, fibreSeriesC data.lam ξ τ)‖ ≤ Real.exp (Real.pi ^ 2 / 4) ∧
      ‖Complex.exp (-∫ τ in s..t, fibreSeriesC data.lam ξ τ) - 1‖ ≤
        (8 + K.Cw * K.Cg) * ρ * Real.exp (Real.pi ^ 2 / 4) * fibreNorm ξ := by
  have hL := scalarPackageSymbol_quadratic_bound data H.hη0 H.hη H.hCg H.hCw H.hG H.hv H.hw ξ
    H.hξ
  have hp : 0 ≤ K.Cw * K.Cg := mul_nonneg H.hCw H.hCg
  have hq : 0 ≤ fibreNorm ξ ^ 2 := sq_nonneg _
  have hn0 := fibreNorm_nonneg ξ
  have hc : 0 ≤ (8 + K.Cw * K.Cg) * fibreNorm ξ ^ 2 := by positivity
  have hI : ‖∫ τ in s..t, fibreSeriesC data.lam ξ τ‖ ≤ (8 + K.Cw * K.Cg) * fibreNorm ξ ^ 2 := by
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (fun τ _ => hL τ)).trans ?_
    rw [abs_of_nonneg (sub_nonneg.mpr hst)]
    calc (8 + K.Cw * K.Cg) * fibreNorm ξ ^ 2 * (t - s)
        ≤ (8 + K.Cw * K.Cg) * fibreNorm ξ ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (by linarith) hc
      _ = _ := mul_one _
  have hpi : (8 + K.Cw * K.Cg) * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2 / 4 := by
    have h4 : (8 + K.Cw * K.Cg) * fibreNorm ξ ^ 2 ≤
        4 * ((2 + K.Cw * K.Cg) * fibreNorm ξ ^ 2) := by
      nlinarith [mul_nonneg hp hq]
    linarith [H.hsep]
  set I := ∫ τ in s..t, fibreSeriesC data.lam ξ τ with hIdef
  have hnI : ‖-I‖ ≤ Real.pi ^ 2 / 4 := by rw [norm_neg]; exact hI.trans hpi
  refine ⟨?_, ?_⟩
  · rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans hnI)
  · have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (-I) 1
    simp only [Finset.sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
      pow_one] at h
    refine h.trans ?_
    have hq' : fibreNorm ξ ^ 2 ≤ ρ * fibreNorm ξ := by
      rw [sq]
      exact mul_le_mul_of_nonneg_right hξρ hn0
    calc ‖-I‖ * Real.exp ‖-I‖
        ≤ ((8 + K.Cw * K.Cg) * fibreNorm ξ ^ 2) * Real.exp (Real.pi ^ 2 / 4) :=
          mul_le_mul (by rw [norm_neg]; exact hI) (Real.exp_le_exp.mpr hnI)
            (Real.exp_pos _).le hc
      _ ≤ ((8 + K.Cw * K.Cg) * (ρ * fibreNorm ξ)) * Real.exp (Real.pi ^ 2 / 4) := by
          gcongr
      _ = _ := by ring

/-- **Unit-step contraction.** A phase at most `e^{π²/4}` times a fast part that decayed over a
unit time at the rate `a ≥ 8π²/9 - π²/32` is at most half of the datum. -/
theorem unit_step_half {g z d a : ℝ} (hg0 : 0 ≤ g) (hz : 0 ≤ z) (hd : 0 ≤ d)
    (hgE : g ≤ Real.exp (Real.pi ^ 2 / 4)) (hdec : Real.exp a * z ^ 2 ≤ d ^ 2)
    (ha : 8 * Real.pi ^ 2 / 9 - Real.pi ^ 2 / 32 ≤ a) : g * z ≤ d / 2 := by
  have hpi : 9 ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hexp : Real.exp (Real.pi ^ 2 / 4) ^ 2 * Real.exp (-a) ≤ 1 / 4 := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    have hb : Real.pi ^ 2 / 4 + Real.pi ^ 2 / 4 + -a ≤ -3 := by linarith
    have h3 : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
    calc Real.exp (Real.pi ^ 2 / 4 + Real.pi ^ 2 / 4 + -a) ≤ Real.exp (-3) :=
          Real.exp_le_exp.mpr hb
      _ = (Real.exp 3)⁻¹ := Real.exp_neg 3
      _ ≤ 1 / 4 := by rw [one_div]; exact inv_anti₀ (by norm_num) h3
  have h2 : z ^ 2 = Real.exp (-a) * (Real.exp a * z ^ 2) := by
    rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  have hsq : (g * z) ^ 2 ≤ (d / 2) ^ 2 := by
    calc (g * z) ^ 2 ≤ Real.exp (Real.pi ^ 2 / 4) ^ 2 * z ^ 2 := by
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hg0 hgE 2) (sq_nonneg z)
      _ = Real.exp (Real.pi ^ 2 / 4) ^ 2 * Real.exp (-a) * (Real.exp a * z ^ 2) := by
          rw [mul_assoc, ← h2]
      _ ≤ (1 / 4) * d ^ 2 := mul_le_mul hexp hdec (by positivity) (by norm_num)
      _ = (d / 2) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (mul_nonneg hg0 hz) (by linarith) two_ne_zero).mp hsq

/-- **The row normalization.** For the reversed curve from `1` at `-B`,
`⟨1 + r(σ), u(-σ)⟩ = e^{∫_σ^B λ}` (bilinear). -/
theorem rowCurve_pair (H : TransverseLocalHyp K η G v ξ) (data : FibreScalarData K η G v t₀ S)
    (V : ℝ) (hb' : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2) {A B : ℝ}
    {u : ℝ → ComplexCellL2} {slice : ℝ → TorusHk 1 ℂ}
    (hu : IsRevCurve H V hb' (-B) (-A) u slice) (h1 : u (-B) = cellConstantCLM 1) :
    ∀ σ ∈ Icc A B, cellComplexPair (cellRawTrace (fibreSeriesJet data.r ξ) σ + cellConstantCLM 1)
        (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u (-σ))) =
      Complex.exp (∫ τ in σ..B, fibreSeriesC data.lam ξ τ) := by
  intro σ hσ
  rw [revCurve_pairing H.hη0 H.hη H.hCg H.hCw H.hG H.hv H.hm H.hw data ξ H.hξ V hb' hu σ hσ, h1,
    graph_pair_one data H.hξ B, mul_one]

/-- The row constant `2(e^{π²/4}C₁ + Lρe^{π²/4}) + 1`, `L = 8 + C_w C_g`. -/
def rowConst (K : ScalarConstants) (C1 ρ : ℝ) : ℝ :=
  2 * (Real.exp (Real.pi ^ 2 / 4) * C1 + (8 + K.Cw * K.Cg) * ρ * Real.exp (Real.pi ^ 2 / 4)) + 1

/-- **The normalized adjoint row is `L²`-close to `1` from its unit-time closeness.** If every
reversed curve from `1` inside `[A, B]` is `C₁|ξ|`-close to `1` within a unit time, then the
normalized row from `1` at `B` is `rowConst K C₁ ρ |ξ|`-close to `1` on all of `[A, B]`. -/
theorem rowCurve_l2_of_unit (H : TransverseLocalHyp K η G v ξ)
    (data : FibreScalarData K η G v t₀ S) {ρ C1 : ℝ} (hξρ : fibreNorm ξ ≤ ρ) (hC1 : 0 ≤ C1)
    (V : ℝ) (hb' : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2) {A B : ℝ}
    (hunit : ∀ A' B', A ≤ A' → B' ≤ B → ∀ (y : ℝ → ComplexCellL2) (ys : ℝ → TorusHk 1 ℂ),
      IsRevCurve H V hb' (-B') (-A') y ys → y (-B') = cellConstantCLM 1 →
      ∀ σ ∈ Icc A' B', B' ≤ σ + 1 → ‖y (-σ) - cellConstantCLM 1‖ ≤ C1 * fibreNorm ξ)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ) (hu : IsRevCurve H V hb' (-B) (-A) u slice)
    (h1 : u (-B) = cellConstantCLM 1) : ∀ σ ∈ Icc A B,
      ‖cellScalarCLM (Complex.exp (-∫ τ in σ..B, fibreSeriesC data.lam ξ τ)) (u (-σ)) -
          cellConstantCLM 1‖ ≤ rowConst K C1 ρ * fibreNorm ξ := by
  have hρ : 0 ≤ ρ := (fibreNorm_nonneg ξ).trans hξρ
  have hCw := H.hCw
  have hCg := H.hCg
  set E := Real.exp (Real.pi ^ 2 / 4) with hE
  set M0 := E * C1 + (8 + K.Cw * K.Cg) * ρ * E with hM0
  have hE0 : 0 < E := Real.exp_pos _
  have hM00 : 0 ≤ M0 := by positivity
  set lam := fibreSeriesC data.lam ξ with hlam
  set d : ℝ → ComplexCellL2 := fun σ =>
    cellScalarCLM (Complex.exp (-∫ τ in σ..B, lam τ)) (u (-σ)) - cellConstantCLM 1 with hd
  have hn0 := fibreNorm_nonneg ξ
  have hone : ‖cellConstantCLM (1 : ℂ)‖ = 1 := by rw [cellConstantCLM_norm, norm_one]
  have hint : ∀ a b, a ≤ b → IntervalIntegrable lam volume a b := fun a b hab =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
      (symbol_integrableOn data H.hη0 H.hη H.hCg H.hCw H.hG H.hv H.hw H.hξ a b)
  have hq32 : fibreNorm ξ ^ 2 ≤ Real.pi ^ 2 / 32 := by
    nlinarith [H.hsep, mul_nonneg (mul_nonneg H.hCw H.hCg) (sq_nonneg (fibreNorm ξ))]
  -- the slow part over at most a unit time, by (C1)
  have hslow : ∀ (γ : ℂ) (Y : ComplexCellL2), ‖γ‖ ≤ E →
      ‖γ - 1‖ ≤ (8 + K.Cw * K.Cg) * ρ * E * fibreNorm ξ →
      ‖Y - cellConstantCLM 1‖ ≤ C1 * fibreNorm ξ →
      ‖γ • (Y - cellConstantCLM 1) + (γ - 1) • cellConstantCLM 1‖ ≤ M0 * fibreNorm ξ := by
    intro γ Y hγ hγ1 hY
    calc ‖γ • (Y - cellConstantCLM 1) + (γ - 1) • cellConstantCLM 1‖
        ≤ ‖γ‖ * ‖Y - cellConstantCLM 1‖ + ‖γ - 1‖ * ‖cellConstantCLM (1 : ℂ)‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, norm_smul]
      _ ≤ E * (C1 * fibreNorm ξ) + (8 + K.Cw * K.Cg) * ρ * E * fibreNorm ξ * 1 := by
          rw [hone]
          gcongr
      _ = M0 * fibreNorm ξ := by rw [hM0]; ring
  -- the base: within a unit time of the terminal test
  have hbase : ∀ σ ∈ Icc A B, B ≤ σ + 1 → ‖d σ‖ ≤ M0 * fibreNorm ξ := by
    intro σ hσ hB
    obtain ⟨hγ, hγ1⟩ := phase_unit_bounds H data hξρ hσ.2 hB
    have hY : ‖u (-σ) - cellConstantCLM 1‖ ≤ C1 * fibreNorm ξ :=
      hunit A B le_rfl le_rfl u slice hu h1 σ hσ hB
    have hdec : d σ = Complex.exp (-∫ τ in σ..B, lam τ) • (u (-σ) - cellConstantCLM 1) +
        (Complex.exp (-∫ τ in σ..B, lam τ) - 1) • cellConstantCLM 1 := by
      simp only [hd, cellScalarCLM_smul]
      module
    rw [hdec]
    exact hslow _ _ hγ hγ1 hY
  -- the step: one unit of time
  have hstep : ∀ σ ∈ Icc A B, σ + 1 ≤ B → ‖d σ‖ ≤ (1 / 2) * ‖d (σ + 1)‖ + M0 * fibreNorm ξ := by
    intro σ hσ hB
    obtain ⟨y, ys, hy, hy0⟩ := revCurve_exists H V hb' (a := -(σ + 1)) (b := -σ) (by linarith)
      (cellConstantCLM 1)
    set c := Complex.exp (-∫ τ in (σ + 1)..B, lam τ) with hc
    have hus : IsRevCurve H V hb' (-(σ + 1)) (-σ) u slice :=
      CellWeakHilbertCurve.mono hu (Icc_subset_Icc (by linarith) (by linarith [hσ.1]))
    have hz := revCurve_smul_sub H V hb' hus hy c
    have hσ1 : σ + 1 ∈ Icc A B := ⟨by linarith [hσ.1], hB⟩
    have hfast : cellComplexPair
        (cellRawTrace (fibreSeriesJet data.r ξ) (σ + 1) + cellConstantCLM 1)
        (cellFiberCLM Complex.conjCLE.toContinuousLinearMap
          (cellScalarCLM c (u (-(σ + 1))) - y (-(σ + 1)))) = 0 := by
      rw [hy0, map_sub, cellFiberConj_scalar, cellComplexPair_sub_right,
        cellComplexPair_scalar_right, star_star, rowCurve_pair H data V hb' hu h1 (σ + 1) hσ1,
        graph_pair_one data H.hξ (σ + 1), hc, ← Complex.exp_add, neg_add_cancel,
        Complex.exp_zero, sub_self]
    have hdec := revCurve_fast_decay H.hη0 H.hη H.hCg H.hCw H.hG H.hv H.hm H.hw data ξ H.hreal
      H.hξ H.hsep (s := σ) (t := σ + 1) (by linarith) V hb' hz hfast
    have h11 : σ + 1 - σ = 1 := by ring
    rw [h11, mul_one] at hdec
    have hz1 : cellScalarCLM c (u (-(σ + 1))) - y (-(σ + 1)) = d (σ + 1) := by
      rw [hy0]
    rw [hz1] at hdec
    -- the phase over the step
    have hsplit : Complex.exp (-∫ τ in σ..B, lam τ) =
        Complex.exp (-∫ τ in σ..(σ + 1), lam τ) * c := by
      rw [hc, ← Complex.exp_add, ← neg_add,
        intervalIntegral.integral_add_adjacent_intervals (hint σ (σ + 1) (by linarith))
          (hint (σ + 1) B hB)]
    obtain ⟨hγ, hγ1⟩ := phase_unit_bounds H data hξρ (s := σ) (t := σ + 1) (by linarith) le_rfl
    set γ := Complex.exp (-∫ τ in σ..(σ + 1), lam τ) with hγdef
    have hY : ‖y (-σ) - cellConstantCLM 1‖ ≤ C1 * fibreNorm ξ :=
      hunit σ (σ + 1) hσ.1 hB y ys hy hy0 σ ⟨le_rfl, by linarith⟩ (by linarith)
    set Z := cellScalarCLM c (u (-σ)) - y (-σ) with hZ
    have hhalf : ‖γ‖ * ‖Z‖ ≤ ‖d (σ + 1)‖ / 2 :=
      unit_step_half (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hγ hdec
        (by linarith [hq32])
    have hdσ : d σ = γ • Z + (γ • (y (-σ) - cellConstantCLM 1) +
        (γ - 1) • cellConstantCLM 1) := by
      simp only [hd, hZ, hsplit, cellScalarCLM_smul]
      module
    rw [hdσ]
    calc ‖γ • Z + (γ • (y (-σ) - cellConstantCLM 1) + (γ - 1) • cellConstantCLM 1)‖
        ≤ ‖γ‖ * ‖Z‖ + ‖γ • (y (-σ) - cellConstantCLM 1) + (γ - 1) • cellConstantCLM 1‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul]
      _ ≤ ‖d (σ + 1)‖ / 2 + M0 * fibreNorm ξ := add_le_add hhalf (hslow _ _ hγ hγ1 hY)
      _ = (1 / 2) * ‖d (σ + 1)‖ + M0 * fibreNorm ξ := by ring
  -- induction over unit steps
  have hM0ξ : 0 ≤ M0 * fibreNorm ξ := mul_nonneg hM00 hn0
  have hind : ∀ n : ℕ, ∀ σ ∈ Icc A B, B - σ ≤ n + 1 → ‖d σ‖ ≤ 2 * (M0 * fibreNorm ξ) := by
    intro n
    induction n with
    | zero =>
      intro σ hσ hn
      have := hbase σ hσ (by push_cast at hn; linarith)
      linarith
    | succ n ih =>
      intro σ hσ hn
      by_cases hB : B ≤ σ + 1
      · have := hbase σ hσ hB
        linarith
      · push Not at hB
        have h1' := hstep σ hσ hB.le
        have h2' := ih (σ + 1) ⟨by linarith [hσ.1], hB.le⟩ (by push_cast at hn ⊢; linarith)
        linarith
  intro σ hσ
  have hfin := hind (Nat.ceil (B - σ)) σ hσ (by have := Nat.le_ceil (B - σ); linarith)
  calc ‖d σ‖ ≤ 2 * (M0 * fibreNorm ξ) := hfin
    _ ≤ rowConst K C1 ρ * fibreNorm ξ := by rw [rowConst]; nlinarith
end

/-! # The actual row from `1`, without `P_e`

For any drift with `√η|v| ≤ C_w` (no transversality), the reversed curve `y` from `1` stays
`4(ρ + C_w)|ξ|`-close to `1` over a unit time (`revCurve_unit_l2`). Testing the generator of the
constant against `m = y - 1` sees only means (`revGenerator_one_bound`, through
`cellComplexGenerator_opposite_drift` and `real_shift_mean_generator`), so
`|gen(1, m)| ≤ (2|ξ|² + 2C_w|ξ|)‖m‖`. The drift of `m` does no work for a real shift
(`cellDualDerivative_real_energy`), and Grönwall over a unit time closes.

With the unit-step induction (`rowCurve_l2_of_unit`) the normalized row from `1` is
`rowConst|ξ|`-close to `1` on any window (`actualRow_l2`). Hence the slow adjoint test of the word
fibre facts, `q` from `1` at `b`, satisfies `‖q(r)‖ ≤ (1 + rowConst·ρ)|e^{∫_r^b λ}|`
(`b1wSlowTest_full`). At `r = a` this is `(1 + rowConst·ρ)|N₀|`. Neither `P_e` nor the
smallness-free transverse regularity enters. -/

section
/-- The constant curve `1`. -/
theorem cellWeakHilbertCurve_one (a b : ℝ) :
    CellWeakHilbertCurve a b (fun _ => cellConstantCLM 1) (fun _ => cellH1One)
      (fun _ => 0) where
  trace := continuousOn_const
  state := memLp_const _
  dual := memLp_const _
  agrees := Filter.Eventually.of_forall fun _ => cellH1One_value.symm
  increment := fun _ _ _ _ _ _ => by simp

/-- The generator only depends on the coefficients. -/
theorem cellComplexGenerator_congr_coeff {C₁ C₂ : CellCoefficients} (e : C₁ = C₂)
    (hG₁ : IsCellMetric C₁.G) (hG₂ : IsCellMetric C₂.G) (V : ℝ)
    (hv₁ : Measurable (fun p : ℝ × Vec 2 => C₁.v p.1 p.2))
    (hv₂ : Measurable (fun p : ℝ × Vec 2 => C₂.v p.1 p.2))
    (hb₁ : ∀ t x, ∑ i, C₁.v t x i ^ 2 ≤ V ^ 2) (hb₂ : ∀ t x, ∑ i, C₂.v t x i ^ 2 ≤ V ^ 2)
    (t : ℝ) (u z : TorusHk 1 ℂ) :
    cellComplexGenerator C₁ hG₁ V hv₁ hb₁ t u z = cellComplexGenerator C₂ hG₂ V hv₂ hb₂ t u z := by
  subst e
  rfl

variable {K : ScalarConstants} {η : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {v : ℝ → Vec 2 → Vec 2} {ξ : Fin 2 → ℂ}

/-- A component of a real fibre frequency, scaled by `√η`, is at most `|ξ|` times `√η`. -/
theorem shift_component_le (ξ : Fin 2 → ℂ) (j : Fin 2) :
    |Real.sqrt η * (ξ j).re| ≤ Real.sqrt η * fibreNorm ξ := by
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg η)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg η)
  refine (Complex.abs_re_le_norm _).trans ?_
  unfold fibreNorm
  refine Real.le_sqrt_of_sq_le ?_
  have := Finset.single_le_sum (f := fun i => ‖ξ i‖ ^ 2) (fun i _ => sq_nonneg _)
    (Finset.mem_univ j)
  simpa using this

/-- The squared scaled shift is at most `|ξ|²`. -/
theorem shift_sq_le (H : TransverseLocalHyp K η G v ξ) :
    ∑ j, (Real.sqrt η * (ξ j).re) ^ 2 ≤ fibreNorm ξ ^ 2 := by
  have hs := (realShift_facts H.hη ξ H.hreal).2
  refine le_trans (le_of_eq ?_) hs
  refine Finset.sum_congr rfl fun j _ => ?_
  have hx : ξ j = ((ξ j).re : ℂ) := Complex.ext rfl (by simp [H.hreal j])
  rw [hx, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp

/-- **The forcing of the constant.** For the reversed coefficients of a real shift, the generator
of `1` tested against `m` sees only means: `|gen(1, m)| ≤ (2|ξ|² + 2C_w|ξ|)‖m‖`. -/
theorem revGenerator_one_bound (H : TransverseLocalHyp K η G v ξ) (V : ℝ)
    (hb' : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2) (t : ℝ) (m : TorusHk 1 ℂ) :
    ‖cellComplexGenerator ⟨fun s _ => G (-s), fun s x => -v (-s) x,
        fun j => -((fun k => (Real.sqrt η : ℂ) * ξ k) j), 0⟩ (cellMetric_timeReverse H.hG) V
        (cellDrift_timeReverse H.hv).1 hb' t cellH1One m‖ ≤
      (2 * fibreNorm ξ ^ 2 + 2 * K.Cw * fibreNorm ξ) * ‖torusHkValueCLM m‖ := by
  set θ' : Vec 2 := fun j => -(Real.sqrt η * (ξ j).re) with hθ'
  have hvr := cellDrift_timeReverse H.hv
  have hvn := cellDrift_neg hvr
  have hbn := cellDrift_neg_bound hb'
  rw [cellComplexGenerator_opposite_drift _ (cellMetric_timeReverse H.hG) V hvr hb' t cellH1One m,
    norm_star]
  have hcoef : cellAdjointCoefficients ⟨fun s _ => G (-s), fun s x => -v (-s) x,
      fun j => -((fun k => (Real.sqrt η : ℂ) * ξ k) j), 0⟩ =
      ⟨fun s _ => G (-s), fun t x => -(-v (-t) x), fun j => ((θ' j : ℝ) : ℂ), 0⟩ := by
    simp only [cellAdjointCoefficients, CellCoefficients.mk.injEq, true_and]
    refine ⟨funext fun j => ?_, funext fun t => ?_⟩
    · have hx : ξ j = ((ξ j).re : ℂ) := Complex.ext rfl (by simp [H.hreal j])
      rw [hx, hθ']
      simp [← Complex.ofReal_mul]
    · simp
  rw [cellComplexGenerator_congr_coeff hcoef (cellMetric_timeReverse H.hG)
    (cellMetric_timeReverse H.hG) V hvn.1 hvn.1 hbn hbn t m cellH1One,
    AVRegularity.CycleDamping.real_shift_mean_generator (G := fun s => G (-s))
      (cellMetric_timeReverse H.hG) (fun t x => -(-v (-t) x)) hvn V hbn θ' t m]
  set Mv := torusHkValueCLM m with hMv
  -- the metric term
  set q : ℝ := ∑ j : Fin 2, ∑ k : Fin 2, θ' k * G (-t) j k * θ' j with hq
  have hqc : (∑ j : Fin 2, ∑ k : Fin 2, (θ' k : ℂ) * (G (-t) j k : ℂ) * (θ' j : ℂ)) =
      (q : ℂ) := by
    rw [hq]
    push_cast
    rfl
  have hq0 : |q| ≤ 2 * fibreNorm ξ ^ 2 := by
    have hm := H.hG.2.2.2 (-t) 0 θ'
    have hsw : q = ∑ i, ∑ j, θ' i * G (-t) i j * θ' j := by
      rw [hq]
      simp only [Fin.sum_univ_two]
      ring
    have hθs : ∑ i, θ' i ^ 2 ≤ fibreNorm ξ ^ 2 := by
      refine le_trans (le_of_eq ?_) (shift_sq_le H)
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hθ']
      ring
    have hnn : 0 ≤ ∑ i, θ' i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [abs_le]
    constructor <;> nlinarith [hm.1, hm.2]
  have hmean : ‖cellMean Mv‖ ≤ ‖Mv‖ := by
    rw [← cellMeanCLM_apply]
    exact cellMeanCLM_norm_le Mv
  -- the drift term
  set D : Fin 2 → ComplexCellL2 := fun j => cellDriftEntryCLM
    ⟨fun s _ => G (-s), fun t x => -(-v (-t) x), 0, 0⟩ V hvn.1 hbn t j Mv with hD
  set X : ComplexCellL2 := ∑ j, (θ' j : ℂ) • D j with hX
  have hXmean : (∑ j : Fin 2, (θ' j : ℂ) * cellMean (D j)) = cellMean X := by
    rw [← cellMeanCLM_apply, hX, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← cellScalarCLM_smul, cellMeanCLM_apply, AVRegularity.CycleDamping.cellMean_scalar]
  have hXn : ‖X‖ ≤ (2 * K.Cw * fibreNorm ξ) * ‖Mv‖ := by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    have h0 := cellDriftEntryCLM_ae ⟨fun s _ => G (-s), fun t x => -(-v (-t) x), 0, 0⟩ V hvn.1
      hbn t 0 Mv
    have h1 := cellDriftEntryCLM_ae ⟨fun s _ => G (-s), fun t x => -(-v (-t) x), 0, 0⟩ V hvn.1
      hbn t 1 Mv
    have hXe : (X : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
        fun x => (θ' 0 : ℂ) * D 0 x + (θ' 1 : ℂ) * D 1 x := by
      rw [hX, Fin.sum_univ_two]
      filter_upwards [Lp.coeFn_add ((θ' 0 : ℂ) • D 0) ((θ' 1 : ℂ) • D 1),
        Lp.coeFn_smul (θ' 0 : ℂ) (D 0), Lp.coeFn_smul (θ' 1 : ℂ) (D 1)] with x ha hs0 hs1
      rw [ha, Pi.add_apply, hs0, hs1, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    filter_upwards [hXe, h0, h1] with x hx hx0 hx1
    rw [hx, hx0, hx1]
    simp only [neg_neg]
    have hv0 : ∀ i, |v (-t) x i| ≤ Real.sqrt (∑ l, v (-t) x l ^ 2) := fun i => by
      refine Real.abs_le_sqrt ?_
      exact Finset.single_le_sum (f := fun l => v (-t) x l ^ 2) (fun l _ => sq_nonneg _)
        (Finset.mem_univ i)
    have hw := H.hw (-t) x
    have hterm : ∀ i, |θ' i * v (-t) x i| ≤ K.Cw * fibreNorm ξ := fun i => by
      rw [abs_mul, hθ']
      simp only [abs_neg]
      calc |Real.sqrt η * (ξ i).re| * |v (-t) x i|
          ≤ (Real.sqrt η * fibreNorm ξ) * Real.sqrt (∑ l, v (-t) x l ^ 2) :=
            mul_le_mul (shift_component_le ξ i) (hv0 i) (abs_nonneg _)
              (mul_nonneg (Real.sqrt_nonneg _) (fibreNorm_nonneg ξ))
        _ = fibreNorm ξ * (Real.sqrt η * Real.sqrt (∑ l, v (-t) x l ^ 2)) := by ring
        _ ≤ fibreNorm ξ * K.Cw := mul_le_mul_of_nonneg_left hw (fibreNorm_nonneg ξ)
        _ = K.Cw * fibreNorm ξ := by ring
    have heq : (θ' 0 : ℂ) * ((v (-t) x 0 : ℂ) * Mv x) + (θ' 1 : ℂ) * ((v (-t) x 1 : ℂ) * Mv x) =
        ((θ' 0 * v (-t) x 0 + θ' 1 * v (-t) x 1 : ℝ) : ℂ) * Mv x := by
      push_cast
      ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc |θ' 0 * v (-t) x 0 + θ' 1 * v (-t) x 1|
        ≤ |θ' 0 * v (-t) x 0| + |θ' 1 * v (-t) x 1| := abs_add_le _ _
      _ ≤ K.Cw * fibreNorm ξ + K.Cw * fibreNorm ξ := add_le_add (hterm 0) (hterm 1)
      _ = 2 * K.Cw * fibreNorm ξ := by ring
  rw [hqc, hXmean]
  calc ‖-(q : ℂ) * cellMean Mv - Complex.I * cellMean X‖
      ≤ ‖-(q : ℂ) * cellMean Mv‖ + ‖Complex.I * cellMean X‖ := norm_sub_le _ _
    _ = |q| * ‖cellMean Mv‖ + ‖cellMean X‖ := by
        rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I,
          one_mul]
    _ ≤ (2 * fibreNorm ξ ^ 2) * ‖Mv‖ + ‖X‖ := by
        refine add_le_add (mul_le_mul hq0 hmean (norm_nonneg _) (by positivity)) ?_
        rw [← cellMeanCLM_apply]
        exact cellMeanCLM_norm_le X
    _ ≤ (2 * fibreNorm ξ ^ 2) * ‖Mv‖ + (2 * K.Cw * fibreNorm ξ) * ‖Mv‖ := by gcongr
    _ = (2 * fibreNorm ξ ^ 2 + 2 * K.Cw * fibreNorm ξ) * ‖Mv‖ := by ring

/-- **Unit-time closeness of the reversed curve from `1`**, for any drift. -/
theorem revCurve_unit_l2 (H : TransverseLocalHyp K η G v ξ) {ρ : ℝ} (hξρ : fibreNorm ξ ≤ ρ)
    (V : ℝ) (hb' : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2) {A' B' : ℝ}
    (y : ℝ → ComplexCellL2) (ys : ℝ → TorusHk 1 ℂ) (hy : IsRevCurve H V hb' (-B') (-A') y ys)
    (hy1 : y (-B') = cellConstantCLM 1) (σ : ℝ) (hσ : σ ∈ Icc A' B') (hσ1 : B' ≤ σ + 1) :
    ‖y (-σ) - cellConstantCLM 1‖ ≤ 4 * (ρ + K.Cw) * fibreNorm ξ := by
  obtain ⟨hθr, -⟩ := realShift_facts H.hη ξ H.hreal
  have hn0 := fibreNorm_nonneg ξ
  have hCw := H.hCw
  set c := 2 * fibreNorm ξ ^ 2 + 2 * K.Cw * fibreNorm ξ with hc
  have hc0 : 0 ≤ c := by positivity
  have hab : -B' ≤ -σ := by linarith [hσ.2]
  have hm := (CellWeakHilbertCurve.mono hy (Icc_subset_Icc le_rfl
    (by linarith [hσ.1] : -σ ≤ -A'))).sub (cellWeakHilbertCurve_one (-B') (-σ))
  have hGr := cellMetric_timeReverse H.hG
  have hvr := cellDrift_timeReverse H.hv
  have hθ : ∀ j, star ((fun j => -((fun k => (Real.sqrt η : ℂ) * ξ k) j)) j) =
      (fun j => -((fun k => (Real.sqrt η : ℂ) * ξ k) j)) j := fun j => by
    simp only [star_neg, hθr j]
  have hgrowth : ∀ᵐ τ ∂volume.restrict (Icc (-B') (-σ)),
      2 * inner ℝ (cellDualDerivative ⟨fun s _ => G (-s), fun s x => -v (-s) x,
        fun j => -((fun k => (Real.sqrt η : ℂ) * ξ k) j), 0⟩ hGr V hvr.1 hb' τ (ys τ) 0 0 - 0)
        (ys τ - cellH1One) + (fun _ => (0 : ℝ)) τ ≤
      1 * ‖y τ - cellConstantCLM 1‖ ^ 2 + (fun _ => c ^ 2) τ := by
    filter_upwards [hm.agrees] with τ hτ
    set C' : CellCoefficients := ⟨fun s _ => G (-s), fun s x => -v (-s) x,
      fun j => -((fun k => (Real.sqrt η : ℂ) * ξ k) j), 0⟩ with hC'
    set ms := ys τ - cellH1One with hms
    have hsplit : cellDualDerivative C' hGr V hvr.1 hb' τ (ys τ) 0 0 =
        cellDualDerivative C' hGr V hvr.1 hb' τ ms 0 0 +
          cellDualDerivative C' hGr V hvr.1 hb' τ cellH1One 0 0 := by
      rw [hms, ← cellDualDerivative_sub_zero C' hGr V hvr.1 hb' τ (ys τ) cellH1One,
        sub_add_cancel]
    have he1 : inner ℝ (cellDualDerivative C' hGr V hvr.1 hb' τ ms 0 0) ms ≤ 0 := by
      have h := cellDualDerivative_real_energy hGr hvr V hb' _ hθ τ ms
      have hnn : 0 ≤ (1 / 2) * ∑ j, ‖cellShiftedDerivativeCLM
          (fun j => -((fun k => (Real.sqrt η : ℂ) * ξ k) j)) j ms‖ ^ 2 := by positivity
      linarith
    have he2 : inner ℝ (cellDualDerivative C' hGr V hvr.1 hb' τ cellH1One 0 0) ms ≤
        c * ‖torusHkValueCLM ms‖ := by
      have hp := cellDualComplexPair_derivative C' hGr V hvr.1 hb' τ cellH1One ms 0 0
      have hz : cellComplexSource C'.θ 0 0 ms = 0 := by
        simpa only [show (fun _ : Fin 2 => (0 : ComplexCellL2)) = 0 from rfl] using
          cellComplexSource_zero C'.θ ms
      rw [hz, add_zero] at hp
      rw [← cellDualComplexPair_re, hp]
      exact (Complex.re_le_norm _).trans (revGenerator_one_bound H V hb' τ ms)
    have hval : ‖torusHkValueCLM ms‖ = ‖y τ - cellConstantCLM 1‖ := by rw [hτ]
    rw [sub_zero, hsplit, inner_add_left]
    rw [hval] at he2
    nlinarith [sq_nonneg (‖y τ - cellConstantCLM 1‖ - c)]
  have hE := hm.energy_dissipation_le_gronwall hab 1 zero_le_one (fun _ => c ^ 2) (fun _ => 0)
    intervalIntegrable_const intervalIntegrable_const
    (Filter.Eventually.of_forall fun _ => sq_nonneg c)
    (Filter.Eventually.of_forall fun _ => le_rfl) hgrowth (-σ) (right_mem_Icc.2 hab)
  simp only [hy1, sub_self, norm_zero, intervalIntegral.integral_zero, add_zero,
    intervalIntegral.integral_const, smul_eq_mul] at hE
  have hlen : -σ - -B' ≤ 1 := by linarith
  have hlen0 : 0 ≤ -σ - -B' := by linarith
  have hexp : Real.exp (1 * (-σ - -B')) ≤ 3 := by
    rw [one_mul]
    calc Real.exp (-σ - -B') ≤ Real.exp 1 := Real.exp_le_exp.mpr hlen
      _ ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have hsq : ‖y (-σ) - cellConstantCLM 1‖ ^ 2 ≤ (2 * c) ^ 2 := by
    have h1 : (0 ^ 2 + (-σ - -B') * c ^ 2) * Real.exp (1 * (-σ - -B')) ≤ 1 * c ^ 2 * 3 := by
      rw [zero_pow two_ne_zero, zero_add]
      exact mul_le_mul (mul_le_mul_of_nonneg_right hlen (sq_nonneg c)) hexp (Real.exp_pos _).le
        (by positivity)
    nlinarith
  have hfin := (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity : 0 ≤ 2 * c)
    two_ne_zero).mp hsq
  calc ‖y (-σ) - cellConstantCLM 1‖ ≤ 2 * c := hfin
    _ = 4 * fibreNorm ξ * fibreNorm ξ + 4 * K.Cw * fibreNorm ξ := by rw [hc]; ring
    _ ≤ 4 * ρ * fibreNorm ξ + 4 * K.Cw * fibreNorm ξ := by gcongr
    _ = 4 * (ρ + K.Cw) * fibreNorm ξ := by ring

/-- **The actual row from `1` is `L²`-close to `1`**, uniformly, with no `P_e`. -/
theorem actualRow_l2 (H : TransverseLocalHyp K η G v ξ) {t₀ S : ℝ}
    (data : FibreScalarData K η G v t₀ S) {ρ : ℝ} (hξρ : fibreNorm ξ ≤ ρ) (V : ℝ)
    (hb' : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2) {A B : ℝ} (u : ℝ → ComplexCellL2)
    (slice : ℝ → TorusHk 1 ℂ) (hu : IsRevCurve H V hb' (-B) (-A) u slice)
    (h1 : u (-B) = cellConstantCLM 1) : ∀ σ ∈ Icc A B,
      ‖cellScalarCLM (Complex.exp (-∫ τ in σ..B, fibreSeriesC data.lam ξ τ)) (u (-σ)) -
          cellConstantCLM 1‖ ≤ rowConst K (4 * (ρ + K.Cw)) ρ * fibreNorm ξ := by
  have hρ : 0 ≤ ρ := (fibreNorm_nonneg ξ).trans hξρ
  have hCw := H.hCw
  exact rowCurve_l2_of_unit H data hξρ (by positivity) V hb'
    (fun _ _ _ _ y ys hy hy1 σ hσ hσ1 => revCurve_unit_l2 H hξρ V hb' y ys hy hy1 σ hσ hσ1)
    u slice hu h1
end

/-! # Crude `H^s` decay of the adjoint fast class

For the actual drift (no transversality), a reversed (adjoint) curve whose datum is in the fast
class of the actual graph decays in `L²` at the rate `4π²/9 - |ξ|²/2 > π²/8`, with no `P_e`
(`revCurve_fast_decay`). The polynomial regularity of the cell equation (`CellDriftRegularityStatement`)
turns this into `H^s` decay at a `P_e^Q` price (`revCurve_crude_decay`): within a unit time by the
growth (G), after it by the smoothing (S) over the last unit time. The drift jets enter through
`L = ∑_{l ≤ s+1} J_l/√η`, and `1 + L ≤ (1 + ∑ J_l) P_e`. This is the decay half of the crude H4. -/

section
/-- The dual derivative only depends on the coefficients. -/
theorem cellDualDerivative_congr_coeff {C₁ C₂ : CellCoefficients} (e : C₁ = C₂)
    (hG₁ : IsCellMetric C₁.G) (hG₂ : IsCellMetric C₂.G) (V : ℝ)
    (hv₁ : Measurable (fun p : ℝ × Vec 2 => C₁.v p.1 p.2))
    (hv₂ : Measurable (fun p : ℝ × Vec 2 => C₂.v p.1 p.2))
    (hb₁ : ∀ t x, ∑ i, C₁.v t x i ^ 2 ≤ V ^ 2) (hb₂ : ∀ t x, ∑ i, C₂.v t x i ^ 2 ≤ V ^ 2)
    (t : ℝ) (u : TorusHk 1 ℂ) (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    cellDualDerivative C₁ hG₁ V hv₁ hb₁ t u S F = cellDualDerivative C₂ hG₂ V hv₂ hb₂ t u S F := by
  subst e
  rfl

variable {K : ScalarConstants} {η : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {v : ℝ → Vec 2 → Vec 2} {ξ : Fin 2 → ℂ}

/-- The jets of the reversed drift: `‖D^l(-v(-τ))‖ ≤ J_l/√η`. -/
theorem revDrift_jet_le (hη : 0 < η) (hvs : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t)) {J : ℕ → ℝ}
    (hvj : ∀ (l : ℕ) t z, ‖iteratedFDeriv ℝ l (fun z' => Real.sqrt η • v t z') z‖ ≤ J l)
    (l : ℕ) (τ : ℝ) (z : Vec 2) :
    ‖iteratedFDeriv ℝ l (fun x => -v (-τ) x) z‖ ≤ J l / Real.sqrt η := by
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have hneg : (fun x => -v (-τ) x) = -(v (-τ)) := rfl
  rw [hneg, iteratedFDeriv_neg_apply, norm_neg, le_div_iff₀ hs]
  have h := hvj l (-τ) z
  rw [iteratedFDeriv_const_smul_apply' (((hvs (-τ)).of_le (by exact_mod_cast le_top)).contDiffAt),
    norm_smul, Real.norm_of_nonneg hs.le] at h
  linarith

/-- `1 + B/√η ≤ (1 + B) P_e`. -/
theorem one_add_div_sqrt_le (hη : 0 < η) {B : ℝ} (hB : 0 ≤ B) :
    1 + B / Real.sqrt η ≤ (1 + B) * peFactor η := by
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  unfold peFactor
  rw [div_eq_mul_inv]
  have hi : 0 ≤ (Real.sqrt η)⁻¹ := inv_nonneg.mpr hs.le
  nlinarith [mul_nonneg hB hi]

/-- The reversed coefficients of a real shift, with the shift as a real vector. -/
theorem revCoefficients_real (H : TransverseLocalHyp K η G v ξ) :
    (⟨fun s _ => G (-s), fun s x => -v (-s) x,
        fun j => -((fun k => (Real.sqrt η : ℂ) * ξ k) j), 0⟩ : CellCoefficients) =
      ⟨fun s _ => G (-s), fun s x => -v (-s) x,
        fun k => ((-(Real.sqrt η * (ξ k).re) : ℝ) : ℂ), 0⟩ := by
  simp only [CellCoefficients.mk.injEq, true_and, and_true]
  funext j
  have hx : ξ j = ((ξ j).re : ℂ) := Complex.ext rfl (by simp [H.hreal j])
  rw [hx]
  push_cast
  simp

/-- **Crude `H^s` decay of the adjoint fast class** (the cell-equation regularity and the `P_e`-free `L²` decay). -/
theorem revCurve_crude_decay (hR : CellDriftRegularityStatement) (s : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (J : ℕ → ℝ) (hJ : ∀ l, 0 ≤ J l) :
    ∃ (C : ℝ) (Q : ℕ), 0 < C ∧
    ∀ (η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (ξ : Fin 2 → ℂ)
      (H : TransverseLocalHyp K η G v ξ) {t₀ S : ℝ} (data : FibreScalarData K η G v t₀ S),
      0 < η → fibreNorm ξ ≤ ρ → (∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
      (∀ (l : ℕ) t z, ‖iteratedFDeriv ℝ l (fun z' => Real.sqrt η • v t z') z‖ ≤ J l) →
    ∀ (V : ℝ) (hb' : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2) {a t : ℝ}, a ≤ t →
    ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ), IsRevCurve H V hb' (-t) (-a) u slice →
      cellComplexPair (cellRawTrace (fibreSeriesJet data.r ξ) t + cellConstantCLM 1)
        (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u (-t))) = 0 →
    ∀ w₀ : TorusHk s ℂ, torusHkValueCLM w₀ = u (-t) →
      ∃ w : TorusHk s ℂ, torusHkValueCLM w = u (-a) ∧
        ‖w‖ ≤ C * peFactor η ^ Q * Real.exp (-(Real.pi ^ 2 / 8) * (t - a)) * ‖w₀‖ := by
  obtain ⟨C₀, Q, hC₀, hreg⟩ := hR s ρ hρ
  set B := ∑ l ∈ Finset.range (s + 2), J l with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun l _ => hJ l
  set E := Real.exp (Real.pi ^ 2 / 8) with hE
  refine ⟨C₀ * (1 + B) ^ Q * E, Q, by positivity, ?_⟩
  intro η G v ξ H t₀ S data hη hξρ hvs hvj V hb' a t hat u slice hu hfast w₀ hw₀
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have hP : 0 < peFactor η := by unfold peFactor; positivity
  set L := B / Real.sqrt η with hL
  have hL0 : 0 ≤ L := div_nonneg hB0 hs.le
  have hLP : (1 + L) ^ Q ≤ (1 + B) ^ Q * peFactor η ^ Q := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (one_add_div_sqrt_le hη hB0) Q
  -- the jets of the reversed drift are at most `L`
  have hjet : ∀ (l : ℕ) τ, l ≤ s + 1 → ∀ x,
      ‖iteratedFDeriv ℝ l (fun x => -v (-τ) x) x‖ ≤ L := by
    intro l τ hl x
    refine (revDrift_jet_le hη hvs hvj l τ x).trans ?_
    rw [hL]
    refine div_le_div_of_nonneg_right ?_ hs.le
    exact Finset.single_le_sum (fun l _ => hJ l) (Finset.mem_range.2 (by omega))
  -- the shift as a real vector
  set θ' : Vec 2 := fun k => -(Real.sqrt η * (ξ k).re) with hθ'
  have hθρ : Real.sqrt (vecDot θ' θ') ≤ ρ := by
    refine Real.sqrt_le_iff.mpr ⟨hρ, ?_⟩
    refine le_trans ?_ (pow_le_pow_left₀ (fibreNorm_nonneg ξ) hξρ 2)
    refine le_trans (le_of_eq ?_) (shift_sq_le H)
    simp only [vecDot, hθ', Fin.sum_univ_two]
    ring
  have hGr := cellMetric_timeReverse H.hG
  have hvr := cellDrift_timeReverse H.hv
  -- the reversed curve in the form of the cell-equation regularity
  have hu' : ∀ a' b', -t ≤ a' → b' ≤ -a → CellWeakHilbertCurve a' b' u slice (fun τ =>
      cellDualDerivative ⟨fun s _ => G (-s), fun s x => -v (-s) x, fun k => (θ' k : ℂ), 0⟩
        hGr V hvr.1 hb' τ (slice τ) 0 0) := by
    intro a' b' ha' hb''
    have h := CellWeakHilbertCurve.mono hu (Icc_subset_Icc ha' hb'')
    refine CellWeakHilbertCurve.dual_congr h (Filter.Eventually.of_forall fun τ => ?_)
    exact cellDualDerivative_congr_coeff (revCoefficients_real H) _ _ V _ _ _ _ τ _ 0 0
  have hsmooth : ∀ τ, ContDiff ℝ (⊤ : ℕ∞) (fun x => -v (-τ) x) := fun τ => (hvs (-τ)).neg
  have hw0n : ‖u (-t)‖ ≤ ‖w₀‖ := hw₀ ▸ torusHk_value_norm_le w₀
  have hexp0 : 0 < Real.exp (-(Real.pi ^ 2 / 8) * (t - a)) := Real.exp_pos _
  by_cases h1 : t - a ≤ 1
  · -- within a unit time: the growth (G)
    obtain ⟨w, hwv, hwn⟩ := (hreg (-t) (-a) L (fun s => G (-s)) hGr hvr V hb' θ' (by linarith)
      hL0 hθρ (fun τ _ => hsmooth τ) (fun l τ hl _ x => hjet l τ hl x) u slice
      (hu' (-t) (-a) le_rfl le_rfl)).1 w₀ hw₀ (-a) ⟨by linarith, le_rfl⟩ (by linarith)
    refine ⟨w, hwv, hwn.trans ?_⟩
    have hE1 : 1 ≤ E * Real.exp (-(Real.pi ^ 2 / 8) * (t - a)) := by
      rw [hE, ← Real.exp_add]
      exact Real.one_le_exp (by nlinarith [Real.pi_pos])
    calc C₀ * (1 + L) ^ Q * ‖w₀‖ ≤ C₀ * ((1 + B) ^ Q * peFactor η ^ Q) * ‖w₀‖ := by gcongr
      _ ≤ C₀ * ((1 + B) ^ Q * peFactor η ^ Q) * ‖w₀‖ *
            (E * Real.exp (-(Real.pi ^ 2 / 8) * (t - a))) :=
          le_mul_of_one_le_right (by positivity) hE1
      _ = C₀ * (1 + B) ^ Q * E * peFactor η ^ Q *
            Real.exp (-(Real.pi ^ 2 / 8) * (t - a)) * ‖w₀‖ := by ring
  · -- after a unit time: `L²` decay, then the smoothing (S) over the last unit time
    push Not at h1
    obtain ⟨w, hwv, hwn⟩ := (hreg (-a - 1) (-a) L (fun s => G (-s)) hGr hvr V hb' θ'
      (by linarith) hL0 hθρ (fun τ _ => hsmooth τ) (fun l τ hl _ x => hjet l τ hl x) u slice
      (hu' (-a - 1) (-a) (by linarith) le_rfl)).2 (-a) ⟨by linarith, le_rfl⟩ (by linarith)
      (by linarith)
    refine ⟨w, hwv, hwn.trans ?_⟩
    -- the `L²` decay of the fast class on `[a + 1, t]`
    have hdec := revCurve_fast_decay H.hη0 H.hη H.hCg H.hCw H.hG H.hv H.hm H.hw data ξ H.hreal
      H.hξ H.hsep (s := a + 1) (t := t) (by linarith) V hb'
      (CellWeakHilbertCurve.mono hu (Icc_subset_Icc le_rfl (by linarith))) hfast
    have hq32 : fibreNorm ξ ^ 2 ≤ Real.pi ^ 2 / 32 := by
      nlinarith [H.hsep, mul_nonneg (mul_nonneg H.hCw H.hCg) (sq_nonneg (fibreNorm ξ))]
    have hrate : Real.exp (-(Real.pi ^ 2 / 8) * (t - (a + 1))) ^ 2 *
        Real.exp ((8 * Real.pi ^ 2 / 9 - fibreNorm ξ ^ 2) * (t - (a + 1))) ≥ 1 := by
      rw [sq, ← Real.exp_add, ← Real.exp_add]
      refine Real.one_le_exp ?_
      have hpi : 0 ≤ Real.pi ^ 2 := sq_nonneg _
      nlinarith
    have hneg : -(a + 1) = -a - 1 := by ring
    rw [hneg] at hdec
    have hL2 : ‖u (-a - 1)‖ ≤ Real.exp (-(Real.pi ^ 2 / 8) * (t - (a + 1))) * ‖w₀‖ := by
      have hsq : ‖u (-a - 1)‖ ^ 2 ≤ (Real.exp (-(Real.pi ^ 2 / 8) * (t - (a + 1))) * ‖w₀‖) ^ 2 := by
        have h2 : ‖u (-t)‖ ^ 2 ≤ ‖w₀‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw0n 2
        calc ‖u (-a - 1)‖ ^ 2 ≤ Real.exp (-(Real.pi ^ 2 / 8) * (t - (a + 1))) ^ 2 *
              Real.exp ((8 * Real.pi ^ 2 / 9 - fibreNorm ξ ^ 2) * (t - (a + 1))) *
                ‖u (-a - 1)‖ ^ 2 := le_mul_of_one_le_left (sq_nonneg _) hrate
          _ ≤ Real.exp (-(Real.pi ^ 2 / 8) * (t - (a + 1))) ^ 2 * ‖u (-t)‖ ^ 2 := by
              rw [mul_assoc]
              exact mul_le_mul_of_nonneg_left hdec (sq_nonneg _)
          _ ≤ Real.exp (-(Real.pi ^ 2 / 8) * (t - (a + 1))) ^ 2 * ‖w₀‖ ^ 2 :=
              mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
          _ = _ := by ring
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
    have hsplit : Real.exp (-(Real.pi ^ 2 / 8) * (t - (a + 1))) =
        E * Real.exp (-(Real.pi ^ 2 / 8) * (t - a)) := by
      rw [hE, ← Real.exp_add]
      congr 1
      ring
    calc C₀ * (1 + L) ^ Q * ‖u (-a - 1)‖
        ≤ C₀ * ((1 + B) ^ Q * peFactor η ^ Q) *
            (Real.exp (-(Real.pi ^ 2 / 8) * (t - (a + 1))) * ‖w₀‖) := by gcongr
      _ = C₀ * (1 + B) ^ Q * E * peFactor η ^ Q *
            Real.exp (-(Real.pi ^ 2 / 8) * (t - a)) * ‖w₀‖ := by rw [hsplit]; ring
end

end AVRegularity.CycleWords.Assembly
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped Pointwise
namespace AVRegularity.CycleWords.Assembly

/-! # The admissible fast tests and their norms (the crude class)

At stage `k` and time `r` a test `ψ ∈ L²(cell)` is admissible (`b1wAdm`) when it has an `H^{s_k}`
representative and lies in the fast class of the actual graph: `cellComplexPair (1 + r(r)) ψ = 0`.
The pairing is the one of the word fibre facts (sesquilinear, as in `fastRaw`), and their adjoint
evolution preserves this class exactly: an adjoint curve is `Ψ(r) = conj u(-r)` with `u` a reversed
curve, and `cellComplexPair (1 + r) (conj u)`, the bilinear pairing of the forward slow mode with
`u`, is conserved (`revCurve_pairing`). No transversality is asked; this is the class of the crude
pass (`b1w_crude_adjoint`), and the sharp pass adds transversality in pulses. The norm `b1wNu s k ψ`
is the infimum of the `H^{s_k}` norms of the representatives. These are the three properties the
abstract fibre word asks: a complex cone (`b1wAdm_smul`), homogeneity (`b1wNu_smul`) and domination
of the `L²` norm (`b1wNu_ge`). -/

/-- The admissible fast tests at stage `k`, time `r`: an `H^{s_k}` representative and the fast
class of the graph `tr` at `r`. -/
def b1wAdm (s : ℕ → ℕ) (tr : ℝ → ComplexCellL2) (k : ℕ) (r : ℝ) (ψ : ComplexCellL2) : Prop :=
  (∃ U : TorusHk (s k) ℂ, torusHkValueCLM U = ψ) ∧
    cellComplexPair (tr r + cellConstantCLM 1) ψ = 0

/-- The test norm at stage `k`: the infimum of the `H^{s_k}` norms of the representatives. -/
def b1wNu (s : ℕ → ℕ) (k : ℕ) (ψ : ComplexCellL2) : ℝ :=
  sInf {x : ℝ | ∃ U : TorusHk (s k) ℂ, torusHkValueCLM U = ψ ∧ ‖U‖ = x}

theorem b1wAdm_smul (s : ℕ → ℕ) (tr : ℝ → ComplexCellL2) (k : ℕ) (r : ℝ) (c : ℂ)
    (ψ : ComplexCellL2) (h : b1wAdm s tr k r ψ) : b1wAdm s tr k r (cellScalarCLM c ψ) := by
  obtain ⟨⟨U, hU⟩, hp⟩ := h
  refine ⟨⟨torusHigherScalarCLM (s k) c U, by rw [torusHigherScalarCLM_value, hU]⟩, ?_⟩
  rw [cellComplexPair_scalar_right, hp, mul_zero]

theorem b1wNu_nonneg (s : ℕ → ℕ) (k : ℕ) (ψ : ComplexCellL2) : 0 ≤ b1wNu s k ψ :=
  Real.sInf_nonneg fun _ ⟨_, _, hx⟩ => hx ▸ norm_nonneg _

/-- The test norm dominates the `L²` norm of a representable test. -/
theorem b1wNu_ge (s : ℕ → ℕ) (k : ℕ) (ψ : ComplexCellL2)
    (h : ∃ U : TorusHk (s k) ℂ, torusHkValueCLM U = ψ) : ‖ψ‖ ≤ b1wNu s k ψ := by
  obtain ⟨U, hU⟩ := h
  refine le_csInf ⟨‖U‖, U, hU, rfl⟩ ?_
  rintro x ⟨U', hU', rfl⟩
  rw [← hU']
  exact torusHk_value_norm_le U'

theorem b1wNu_le (s : ℕ → ℕ) (k : ℕ) {ψ : ComplexCellL2} (U : TorusHk (s k) ℂ)
    (hU : torusHkValueCLM U = ψ) : b1wNu s k ψ ≤ ‖U‖ :=
  csInf_le ⟨0, fun _ ⟨_, _, hx⟩ => hx ▸ norm_nonneg _⟩ ⟨U, hU, rfl⟩

/-- **Homogeneity of the test norm.** -/
theorem b1wNu_smul (s : ℕ → ℕ) (k : ℕ) (c : ℂ) (ψ : ComplexCellL2) :
    b1wNu s k (cellScalarCLM c ψ) = ‖c‖ * b1wNu s k ψ := by
  by_cases hc : c = 0
  · subst hc
    have h0 : cellScalarCLM 0 ψ = 0 := by rw [cellScalarCLM_smul, zero_smul]
    rw [h0, norm_zero, zero_mul]
    refine le_antisymm ?_ (b1wNu_nonneg s k 0)
    exact (b1wNu_le s k 0 (map_zero _)).trans_eq norm_zero
  · have hset : {x : ℝ | ∃ U : TorusHk (s k) ℂ, torusHkValueCLM U = cellScalarCLM c ψ ∧
        ‖U‖ = x} = ‖c‖ • {x : ℝ | ∃ U : TorusHk (s k) ℂ, torusHkValueCLM U = ψ ∧ ‖U‖ = x} := by
      ext x
      rw [Set.mem_smul_set]
      constructor
      · rintro ⟨U, hU, rfl⟩
        refine ⟨‖torusHigherScalarCLM (s k) c⁻¹ U‖, ⟨torusHigherScalarCLM (s k) c⁻¹ U, ?_, rfl⟩, ?_⟩
        · rw [torusHigherScalarCLM_value, hU, cellScalarCLM_smul, cellScalarCLM_smul, smul_smul,
            inv_mul_cancel₀ hc, one_smul]
        · rw [torusHigherScalarCLM_norm, smul_eq_mul, ← mul_assoc, norm_inv,
            mul_inv_cancel₀ (norm_ne_zero_iff.2 hc), one_mul]
      · rintro ⟨y, ⟨U, hU, rfl⟩, rfl⟩
        refine ⟨torusHigherScalarCLM (s k) c U, by rw [torusHigherScalarCLM_value, hU], ?_⟩
        rw [torusHigherScalarCLM_norm, smul_eq_mul]
    unfold b1wNu
    rw [hset, Real.sInf_smul_of_nonneg (norm_nonneg c), smul_eq_mul]

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # The slow/fast split of a test

At a time `r`, a test `Φ` splits along the slow adjoint test `q(r)` (`b1w_split`):
`Φ = κ q(r) + φ'` with `κ = conj(⟨1 + r(r), Φ⟩ / g)`, where `g = ⟨1 + r(r), q(r)⟩ ≠ 0` (it is
`e^{∫_r^b λ}`, the conserved pairing with the forward slow mode). Then `φ'` is in the fast class
of the actual graph, `|κ| ≤ ‖1 + r(r)‖ ‖Φ‖ / |g|`, and `ν(φ') ≤ ν(Φ) + |κ| ν(q(r))` when both have
`H^s` representatives (`b1wNu_add_le`). For a stage `W`, `⟨W, Φ⟩ = conj κ ⟨W, q⟩ + ⟨W, φ'⟩`, which
is the form of H3/H4 of the abstract fibre word. -/

/-- **The test norm is subadditive.** -/
theorem b1wNu_add_le (s : ℕ → ℕ) (k : ℕ) {ψ₁ ψ₂ : ComplexCellL2}
    (h₁ : ∃ U : TorusHk (s k) ℂ, torusHkValueCLM U = ψ₁)
    (h₂ : ∃ U : TorusHk (s k) ℂ, torusHkValueCLM U = ψ₂) :
    b1wNu s k (ψ₁ + ψ₂) ≤ b1wNu s k ψ₁ + b1wNu s k ψ₂ := by
  obtain ⟨U₁₀, hU₁₀⟩ := h₁
  obtain ⟨U₂₀, hU₂₀⟩ := h₂
  have key : ∀ U₁ U₂ : TorusHk (s k) ℂ, torusHkValueCLM U₁ = ψ₁ → torusHkValueCLM U₂ = ψ₂ →
      b1wNu s k (ψ₁ + ψ₂) ≤ ‖U₁‖ + ‖U₂‖ := fun U₁ U₂ hU₁ hU₂ =>
    (b1wNu_le s k (U₁ + U₂) (by rw [map_add, hU₁, hU₂])).trans (norm_add_le _ _)
  have h1 : ∀ U₂ : TorusHk (s k) ℂ, torusHkValueCLM U₂ = ψ₂ →
      b1wNu s k (ψ₁ + ψ₂) - ‖U₂‖ ≤ b1wNu s k ψ₁ := by
    intro U₂ hU₂
    refine le_csInf ⟨‖U₁₀‖, U₁₀, hU₁₀, rfl⟩ ?_
    rintro x ⟨U₁, hU₁, rfl⟩
    linarith [key U₁ U₂ hU₁ hU₂]
  have h2 : b1wNu s k (ψ₁ + ψ₂) - b1wNu s k ψ₁ ≤ b1wNu s k ψ₂ := by
    refine le_csInf ⟨‖U₂₀‖, U₂₀, hU₂₀, rfl⟩ ?_
    rintro x ⟨U₂, hU₂, rfl⟩
    linarith [h1 U₂ hU₂]
  linarith

/-- **The slow/fast split of a test.** -/
theorem b1w_split (s : ℕ → ℕ) (tr : ℝ → ComplexCellL2) (k : ℕ) (r : ℝ) (q Φ : ComplexCellL2)
    (hq : ∃ U : TorusHk (s k) ℂ, torusHkValueCLM U = q)
    (hΦ : ∃ U : TorusHk (s k) ℂ, torusHkValueCLM U = Φ)
    (hg : cellComplexPair (tr r + cellConstantCLM 1) q ≠ 0) :
    ∃ (κ : ℂ) (φ' : ComplexCellL2),
      Φ = cellScalarCLM κ q + φ' ∧
      b1wAdm s tr k r φ' ∧
      ‖κ‖ ≤ ‖tr r + cellConstantCLM 1‖ * ‖Φ‖ / ‖cellComplexPair (tr r + cellConstantCLM 1) q‖ ∧
      b1wNu s k φ' ≤ b1wNu s k Φ + ‖κ‖ * b1wNu s k q ∧
      ∀ W : ComplexCellL2,
        cellComplexPair W Φ = star κ * cellComplexPair W q + cellComplexPair W φ' := by
  set g := cellComplexPair (tr r + cellConstantCLM 1) q with hgdef
  set κ : ℂ := star (cellComplexPair (tr r + cellConstantCLM 1) Φ / g) with hκ
  refine ⟨κ, Φ - cellScalarCLM κ q, by abel, ⟨?_, ?_⟩, ?_, ?_, fun W => ?_⟩
  · obtain ⟨UΦ, hUΦ⟩ := hΦ
    obtain ⟨Uq, hUq⟩ := hq
    refine ⟨UΦ - torusHigherScalarCLM (s k) κ Uq, ?_⟩
    rw [map_sub, torusHigherScalarCLM_value, hUΦ, hUq]
  · rw [cellComplexPair_sub_right, cellComplexPair_scalar_right, hκ, star_star, ← hgdef,
      div_mul_cancel₀ _ hg, sub_self]
  · rw [hκ, norm_star, norm_div]
    exact div_le_div_of_nonneg_right (cellComplexPair_norm_le _ _) (norm_nonneg _)
  · have hsc : b1wNu s k (-(cellScalarCLM κ q)) = ‖κ‖ * b1wNu s k q := by
      rw [show -(cellScalarCLM κ q) = cellScalarCLM (-κ) q by
        rw [cellScalarCLM_smul, cellScalarCLM_smul, neg_smul], b1wNu_smul, norm_neg]
    rw [sub_eq_add_neg]
    refine (b1wNu_add_le s k hΦ ?_).trans (le_of_eq (by rw [hsc]))
    obtain ⟨Uq, hUq⟩ := hq
    exact ⟨-(torusHigherScalarCLM (s k) κ Uq),
      by rw [map_neg, torusHigherScalarCLM_value, hUq]⟩
  · rw [cellComplexPair_sub_right, cellComplexPair_scalar_right]
    ring

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped Pointwise
namespace AVRegularity.CycleWords.Assembly

/-! # The sharp pass: the activity-weighted test norm

The sharp pass measures a test at stage `k` and time `r` by the weighted norm
`ν_k(r)(ψ) = inf {‖U_T‖ + Ω(r)‖U_N‖}` (`b1wNuW`). The infimum runs over the splittings of an
`H^{s_k}` representative `U_T + U_N` of `ψ` with `U_T` transverse to `e(r)`.

* A time is **active** when the drift is nonzero somewhere (`IsActiveTime`). By the package
  (`cover`, `quiet_zero`, `ext_agree`, `ext_shear`), an active time has a unique shear orientation.
  Active times of different orientations are more than `D` apart, with a quiet buffer between.
* `τ(r)` is the last active time in `[t₀, r]` (`lastActive`). `e(r)` is the orientation of a window
  containing an active time in `(τ(r) − D, τ(r)]` (`activityOrient`).
* The weight is `Ω(r) = max(1, Λ e^{-c(r − τ(r))})`, and `1` without activity
  (`activityWeight`). The instantiation in the word fibre facts uses `Λ^{k+1}` at stage `k`, and
  `1` at the piece start.

The weighted norm has the properties the abstract fibre word uses:
* homogeneity (`b1wNuW_smul`);
* domination of the `L²` norm on representable tests (`b1wNuW_ge`);
* `ν ≤ Ω‖U‖` for every representative (`b1wNuW_le_mul`), and the splitting bound (`b1wNuW_le`). -/

/-- `τ` is an active time of the drift `v`: the drift is nonzero somewhere. -/
def IsActiveTime (v : ℝ → Vec 2 → Vec 2) (τ : ℝ) : Prop := ∃ z, v τ z ≠ 0

/-- The active times in `[t₀, r]`. -/
def activeSet (v : ℝ → Vec 2 → Vec 2) (t₀ r : ℝ) : Set ℝ :=
  {τ | τ ∈ Icc t₀ r ∧ IsActiveTime v τ}

/-- The last active time `τ(r)`: the supremum of the active times in `[t₀, r]`. -/
def lastActive (v : ℝ → Vec 2 → Vec 2) (t₀ r : ℝ) : ℝ := sSup (activeSet v t₀ r)

open Classical in
/-- The activity weight `Ω(r) = max(1, Λ e^{-c(r − τ(r))})`, and `1` without activity. -/
def activityWeight (v : ℝ → Vec 2 → Vec 2) (t₀ Λ c r : ℝ) : ℝ :=
  if (activeSet v t₀ r).Nonempty then max 1 (Λ * Real.exp (-c * (r - lastActive v t₀ r)))
  else 1

open Classical in
/-- The orientation `e(r)` of the last activity: the orientation of a window containing an active
time in `(τ(r) − D, τ(r)]`, and `0` if there is none. -/
def activityOrient (reg : BlockRegions) (v : ℝ → Vec 2 → Vec 2) (t₀ r : ℝ) : Fin 2 :=
  if h : ∃ p : Fin reg.P, ∃ τ ∈ activeSet v t₀ r, lastActive v t₀ r - reg.buffer < τ ∧
      τ ∈ Icc (reg.lo p) (reg.hi p) then reg.orient h.choose else 0

theorem one_le_activityWeight (v : ℝ → Vec 2 → Vec 2) (t₀ Λ c r : ℝ) :
    1 ≤ activityWeight v t₀ Λ c r := by
  unfold activityWeight
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

/-- **The weighted test norm** at stage `k` and time `r`: the infimum of `‖U_T‖ + Ω_k(r)‖U_N‖`
over the splittings of an `H^{s_k}` representative of `ψ`, with `U_T` transverse to `e(r)`. -/
def b1wNuW (s : ℕ → ℕ) (Ω : ℕ → ℝ → ℝ) (e : ℝ → Fin 2) (k : ℕ) (r : ℝ) (ψ : ComplexCellL2) :
    ℝ :=
  sInf {x : ℝ | ∃ UT UN : TorusHk (s k) ℂ, torusHkValueCLM (UT + UN) = ψ ∧
    cellTransverseProjection (e r) (torusHkValueCLM UT) = torusHkValueCLM UT ∧
    ‖UT‖ + Ω k r * ‖UN‖ = x}

section Norm

variable (s : ℕ → ℕ) (Ω : ℕ → ℝ → ℝ) (e : ℝ → Fin 2) (k : ℕ) (r : ℝ)

theorem b1wNuW_nonneg (hΩ : 0 ≤ Ω k r) (ψ : ComplexCellL2) : 0 ≤ b1wNuW s Ω e k r ψ :=
  Real.sInf_nonneg fun _ ⟨_, _, _, _, hx⟩ =>
    hx ▸ add_nonneg (norm_nonneg _) (mul_nonneg hΩ (norm_nonneg _))

/-- The splitting bound. -/
theorem b1wNuW_le (hΩ : 0 ≤ Ω k r) {ψ : ComplexCellL2} (UT UN : TorusHk (s k) ℂ)
    (hU : torusHkValueCLM (UT + UN) = ψ)
    (hT : cellTransverseProjection (e r) (torusHkValueCLM UT) = torusHkValueCLM UT) :
    b1wNuW s Ω e k r ψ ≤ ‖UT‖ + Ω k r * ‖UN‖ :=
  csInf_le ⟨0, fun _ ⟨_, _, _, _, hx⟩ =>
    hx ▸ add_nonneg (norm_nonneg _) (mul_nonneg hΩ (norm_nonneg _))⟩ ⟨UT, UN, hU, hT, rfl⟩

/-- Every representative bounds the weighted norm, with the weight. -/
theorem b1wNuW_le_mul (hΩ : 0 ≤ Ω k r) {ψ : ComplexCellL2} (U : TorusHk (s k) ℂ)
    (hU : torusHkValueCLM U = ψ) : b1wNuW s Ω e k r ψ ≤ Ω k r * ‖U‖ := by
  refine (b1wNuW_le s Ω e k r hΩ 0 U (by rw [zero_add, hU]) (by rw [map_zero, map_zero])).trans ?_
  rw [norm_zero, zero_add]

/-- **Domination of the `L²` norm** on representable tests. -/
theorem b1wNuW_ge (hΩ : 1 ≤ Ω k r) (ψ : ComplexCellL2)
    (h : ∃ U : TorusHk (s k) ℂ, torusHkValueCLM U = ψ) : ‖ψ‖ ≤ b1wNuW s Ω e k r ψ := by
  obtain ⟨U, hU⟩ := h
  refine le_csInf ⟨Ω k r * ‖U‖, 0, U, by rw [zero_add, hU], by rw [map_zero, map_zero],
    by rw [norm_zero, zero_add]⟩ ?_
  rintro x ⟨UT, UN, hv, -, rfl⟩
  rw [← hv]
  refine (torusHk_value_norm_le _).trans ((norm_add_le _ _).trans ?_)
  have := mul_le_mul_of_nonneg_right hΩ (norm_nonneg UN)
  linarith

/-- **Homogeneity of the weighted norm.** -/
theorem b1wNuW_smul (hΩ : 0 ≤ Ω k r) (c : ℂ) (ψ : ComplexCellL2) :
    b1wNuW s Ω e k r (cellScalarCLM c ψ) = ‖c‖ * b1wNuW s Ω e k r ψ := by
  by_cases hc : c = 0
  · subst hc
    have h0 : cellScalarCLM 0 ψ = 0 := by rw [cellScalarCLM_smul, zero_smul]
    rw [h0, norm_zero, zero_mul]
    refine le_antisymm ?_ (b1wNuW_nonneg s Ω e k r hΩ 0)
    refine (b1wNuW_le s Ω e k r hΩ 0 0 (by rw [add_zero, map_zero])
      (by rw [map_zero, map_zero])).trans_eq ?_
    rw [norm_zero, mul_zero, add_zero]
  · have hT : ∀ (d : ℂ) (U : TorusHk (s k) ℂ),
        cellTransverseProjection (e r) (torusHkValueCLM U) = torusHkValueCLM U →
        cellTransverseProjection (e r) (torusHkValueCLM (torusHigherScalarCLM (s k) d U)) =
          torusHkValueCLM (torusHigherScalarCLM (s k) d U) := by
      intro d U hU
      rw [torusHigherScalarCLM_value, cellScalarCLM_smul, cellTransverseProjection_complex_smul,
        hU]
    have hV : ∀ (d : ℂ) (UT UN : TorusHk (s k) ℂ),
        torusHkValueCLM (torusHigherScalarCLM (s k) d UT + torusHigherScalarCLM (s k) d UN) =
          cellScalarCLM d (torusHkValueCLM (UT + UN)) := by
      intro d UT UN
      rw [← map_add, torusHigherScalarCLM_value]
    have hset : {x : ℝ | ∃ UT UN : TorusHk (s k) ℂ,
        torusHkValueCLM (UT + UN) = cellScalarCLM c ψ ∧
        cellTransverseProjection (e r) (torusHkValueCLM UT) = torusHkValueCLM UT ∧
        ‖UT‖ + Ω k r * ‖UN‖ = x} =
        ‖c‖ • {x : ℝ | ∃ UT UN : TorusHk (s k) ℂ, torusHkValueCLM (UT + UN) = ψ ∧
          cellTransverseProjection (e r) (torusHkValueCLM UT) = torusHkValueCLM UT ∧
          ‖UT‖ + Ω k r * ‖UN‖ = x} := by
      ext x
      rw [Set.mem_smul_set]
      constructor
      · rintro ⟨UT, UN, hv, ht, rfl⟩
        refine ⟨‖torusHigherScalarCLM (s k) c⁻¹ UT‖ + Ω k r * ‖torusHigherScalarCLM (s k) c⁻¹ UN‖,
          ⟨torusHigherScalarCLM (s k) c⁻¹ UT, torusHigherScalarCLM (s k) c⁻¹ UN, ?_,
            hT c⁻¹ UT ht, rfl⟩, ?_⟩
        · rw [hV, hv, cellScalarCLM_smul, cellScalarCLM_smul, smul_smul, inv_mul_cancel₀ hc,
            one_smul]
        · rw [torusHigherScalarCLM_norm, torusHigherScalarCLM_norm, smul_eq_mul, norm_inv]
          field_simp
      · rintro ⟨y, ⟨UT, UN, hv, ht, rfl⟩, rfl⟩
        refine ⟨torusHigherScalarCLM (s k) c UT, torusHigherScalarCLM (s k) c UN, ?_,
          hT c UT ht, ?_⟩
        · rw [hV, hv]
        · rw [torusHigherScalarCLM_norm, torusHigherScalarCLM_norm, smul_eq_mul]
          ring
    unfold b1wNuW
    rw [hset, Real.sInf_smul_of_nonneg (norm_nonneg c), smul_eq_mul]

end Norm

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # The block decomposition from a stage representation

Suppose that at a time `r` a tested source `X` of stage `k` is a sum of pairings of earlier stage
values with test families, `X = ∑_{k' < k} ∑_{i' ∈ stage k'} ⟨W_{i'}, Φ_{i'}⟩`, and each family has
an `ℓ²` bound `B_{k'}` in the test norm `ν_{k'}`. Splitting every `Φ_{i'}` along the slow test `q`
(`b1w_split`) gives the decomposition asked by H3/H4 of the abstract fibre word
(`b1w_blocks_of_representation`):
`X = ∑ (κ_{i'} ⟨W_{i'}, q⟩ + ⟨W_{i'}, φ_{i'}⟩)` with admissible `φ_{i'}`,
`‖κ‖_{k'} ≤ c_R B_{k'}/|g|` and `(∑ ν_{k'}(φ_{i'})²)^{1/2} ≤ B_{k'} + Q c_R B_{k'}/|g|`. Here
`g = ⟨1 + r, q⟩` is the conserved pairing, `c_R ≥ ‖1 + r‖` and `Q` bounds `ν_{k'}(q)`. The `ℓ²` sums
use Minkowski (`sqrt_sum_add_sq_le`). -/

/-- **Minkowski for finite sums**: `(∑ (a + b)²)^{1/2} ≤ (∑ a²)^{1/2} + (∑ b²)^{1/2}`. -/
theorem sqrt_sum_add_sq_le {α : Type*} (s : Finset α) (a b : α → ℝ) :
    Real.sqrt (∑ i ∈ s, (a i + b i) ^ 2) ≤
      Real.sqrt (∑ i ∈ s, a i ^ 2) + Real.sqrt (∑ i ∈ s, b i ^ 2) := by
  have ha := Real.sqrt_nonneg (∑ i ∈ s, a i ^ 2)
  have hb := Real.sqrt_nonneg (∑ i ∈ s, b i ^ 2)
  refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  have hcs : ∑ i ∈ s, a i * b i ≤
      Real.sqrt (∑ i ∈ s, a i ^ 2) * Real.sqrt (∑ i ∈ s, b i ^ 2) := by
    rw [← Real.sqrt_mul (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    refine Real.le_sqrt_of_sq_le ?_
    exact Finset.sum_mul_sq_le_sq_mul_sq s a b
  have hA : Real.sqrt (∑ i ∈ s, a i ^ 2) ^ 2 = ∑ i ∈ s, a i ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (a i))
  have hB : Real.sqrt (∑ i ∈ s, b i ^ 2) ^ 2 = ∑ i ∈ s, b i ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (b i))
  have hexp : ∑ i ∈ s, (a i + b i) ^ 2 =
      ∑ i ∈ s, a i ^ 2 + 2 * ∑ i ∈ s, a i * b i + ∑ i ∈ s, b i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hexp]
  nlinarith [hcs]

variable {I : Type*} [Fintype I]

/-- **The block decomposition from a stage representation.** -/
theorem b1w_blocks_of_representation (s : ℕ → ℕ) (tr : ℝ → ComplexCellL2) (r : ℝ)
    (st : I → ℕ) (k : ℕ) (W : I → ComplexCellL2) (q : ComplexCellL2) (X : ℂ)
    (Φ : I → ComplexCellL2) (B : ℕ → ℝ) (cR Q : ℝ) (hcR : ‖tr r + cellConstantCLM 1‖ ≤ cR)
    (hQ0 : 0 ≤ Q)
    (hg : cellComplexPair (tr r + cellConstantCLM 1) q ≠ 0)
    (hq : ∀ k' < k, ∃ U : TorusHk (s k') ℂ, torusHkValueCLM U = q)
    (hνq : ∀ k' < k, b1wNu s k' q ≤ Q)
    (hΦ : ∀ k' < k, ∀ i' ∈ stageSet st k', ∃ U : TorusHk (s k') ℂ, torusHkValueCLM U = Φ i')
    (hB : ∀ k' < k, Real.sqrt (∑ i' ∈ stageSet st k', b1wNu s k' (Φ i') ^ 2) ≤ B k')
    (hX : X = ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet st k', cellComplexPair (W i') (Φ i')) :
    ∃ (κ : I → ℂ) (φ : I → ComplexCellL2),
      (∀ k' < k, ∀ i' ∈ stageSet st k', b1wAdm s tr k' r (φ i')) ∧
      (∀ k' < k, stageNorm st k' κ ≤
        cR * B k' / ‖cellComplexPair (tr r + cellConstantCLM 1) q‖) ∧
      (∀ k' < k, Real.sqrt (∑ i' ∈ stageSet st k', b1wNu s k' (φ i') ^ 2) ≤
        B k' + Q * (cR * B k' / ‖cellComplexPair (tr r + cellConstantCLM 1) q‖)) ∧
      X = ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet st k',
        (κ i' * cellComplexPair (W i') q + cellComplexPair (W i') (φ i')) := by
  classical
  set g := cellComplexPair (tr r + cellConstantCLM 1) q with hgdef
  have hgpos : 0 < ‖g‖ := norm_pos_iff.2 hg
  -- the split of each test, at the stage of its index
  have hsplit : ∀ i', ∃ (κ : ℂ) (φ' : ComplexCellL2),
      st i' < k → Φ i' = cellScalarCLM κ q + φ' ∧ b1wAdm s tr (st i') r φ' ∧
        ‖κ‖ ≤ ‖tr r + cellConstantCLM 1‖ * ‖Φ i'‖ / ‖g‖ ∧
        b1wNu s (st i') φ' ≤ b1wNu s (st i') (Φ i') + ‖κ‖ * b1wNu s (st i') q ∧
        ∀ Wv : ComplexCellL2, cellComplexPair Wv (Φ i') =
          star κ * cellComplexPair Wv q + cellComplexPair Wv φ' := by
    intro i'
    by_cases hi : st i' < k
    · obtain ⟨κ, φ', h1, h2, h3, h4, h5⟩ := b1w_split s tr (st i') r q (Φ i') (hq _ hi)
        (hΦ _ hi i' (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩)) hg
      exact ⟨κ, φ', fun _ => ⟨h1, h2, h3, h4, h5⟩⟩
    · exact ⟨0, 0, fun h => absurd h hi⟩
  choose κs φs hκφ using hsplit
  refine ⟨fun i' => star (κs i'), φs, ?_, ?_, ?_, ?_⟩
  · intro k' hk' i' hi'
    have hst : st i' = k' := (Finset.mem_filter.1 hi').2
    have := (hκφ i' (hst ▸ hk')).2.1
    rwa [hst] at this
  · intro k' hk'
    have hκle : ∀ i' ∈ stageSet st k', ‖star (κs i')‖ ≤ cR / ‖g‖ * b1wNu s k' (Φ i') := by
      intro i' hi'
      have hst : st i' = k' := (Finset.mem_filter.1 hi').2
      have h3 := (hκφ i' (hst ▸ hk')).2.2.1
      rw [norm_star]
      refine h3.trans ?_
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hgpos]
      refine mul_le_mul hcR (b1wNu_ge s k' (Φ i') (hΦ k' hk' i' hi')) (norm_nonneg _)
        ((norm_nonneg _).trans hcR)
    unfold stageNorm
    have hc : 0 ≤ cR / ‖g‖ := div_nonneg ((norm_nonneg _).trans hcR) hgpos.le
    calc Real.sqrt (∑ i ∈ stageSet st k', ‖star (κs i)‖ ^ 2)
        ≤ Real.sqrt (∑ i ∈ stageSet st k', (cR / ‖g‖ * b1wNu s k' (Φ i)) ^ 2) := by
          refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i hi => ?_)
          exact pow_le_pow_left₀ (norm_nonneg _) (hκle i hi) 2
      _ = cR / ‖g‖ * Real.sqrt (∑ i ∈ stageSet st k', b1wNu s k' (Φ i) ^ 2) := by
          simp only [mul_pow]
          rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc]
      _ ≤ cR / ‖g‖ * B k' := mul_le_mul_of_nonneg_left (hB k' hk') hc
      _ = cR * B k' / ‖g‖ := by ring
  · intro k' hk'
    have hc : 0 ≤ cR / ‖g‖ := div_nonneg ((norm_nonneg _).trans hcR) hgpos.le
    have hφle : ∀ i' ∈ stageSet st k', b1wNu s k' (φs i') ≤
        b1wNu s k' (Φ i') + Q * (cR / ‖g‖ * b1wNu s k' (Φ i')) := by
      intro i' hi'
      have hst : st i' = k' := (Finset.mem_filter.1 hi').2
      have h := hκφ i' (hst ▸ hk')
      rw [hst] at h
      refine h.2.2.2.1.trans (add_le_add le_rfl ?_)
      rw [mul_comm Q]
      refine mul_le_mul ?_ (hνq k' hk') (b1wNu_nonneg _ _ _) (mul_nonneg hc (b1wNu_nonneg _ _ _))
      refine h.2.2.1.trans ?_
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hgpos]
      exact mul_le_mul hcR (b1wNu_ge s k' (Φ i') (hΦ k' hk' i' hi')) (norm_nonneg _)
        ((norm_nonneg _).trans hcR)
    have hν0 : ∀ i', 0 ≤ b1wNu s k' (φs i') := fun i' => b1wNu_nonneg _ _ _
    calc Real.sqrt (∑ i' ∈ stageSet st k', b1wNu s k' (φs i') ^ 2)
        ≤ Real.sqrt (∑ i' ∈ stageSet st k', (b1wNu s k' (Φ i') +
            Q * (cR / ‖g‖ * b1wNu s k' (Φ i'))) ^ 2) := by
          refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i hi => ?_)
          exact pow_le_pow_left₀ (hν0 i) (hφle i hi) 2
      _ ≤ Real.sqrt (∑ i' ∈ stageSet st k', b1wNu s k' (Φ i') ^ 2) +
            Real.sqrt (∑ i' ∈ stageSet st k', (Q * (cR / ‖g‖ * b1wNu s k' (Φ i'))) ^ 2) :=
          sqrt_sum_add_sq_le _ _ _
      _ = Real.sqrt (∑ i' ∈ stageSet st k', b1wNu s k' (Φ i') ^ 2) * (1 + Q * (cR / ‖g‖)) := by
          have hQc : 0 ≤ Q * (cR / ‖g‖) := mul_nonneg hQ0 hc
          simp only [show ∀ x : ℝ, (Q * (cR / ‖g‖ * x)) ^ 2 = (Q * (cR / ‖g‖)) ^ 2 * x ^ 2 from
            fun x => by ring]
          rw [← Finset.mul_sum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hQc]
          ring
      _ ≤ B k' * (1 + Q * (cR / ‖g‖)) :=
          mul_le_mul_of_nonneg_right (hB k' hk') (by positivity)
      _ = B k' + Q * (cR * B k' / ‖g‖) := by ring
  · rw [hX]
    refine Finset.sum_congr rfl fun k' hk' => Finset.sum_congr rfl fun i' hi' => ?_
    have hst : st i' = k' := (Finset.mem_filter.1 hi').2
    have h := (hκφ i' (hst ▸ Finset.mem_range.1 hk')).2.2.2.2 (W i')
    rw [h]

end AVRegularity.CycleWords.Assembly
end
end
end
