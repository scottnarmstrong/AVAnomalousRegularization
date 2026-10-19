-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Applications.TorusEnergy.LocalInt
import AVRegularity.Applications.Dissipation.EntropyLimit
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Convex entropy inequality and positivity of weak solutions

For a divergence-free window drift and `κ ≥ 0`, every smooth convex `j` with bounded second
derivative satisfies `∫ j(θ(t)) ≤ ∫ j(f)` on the window. The proof runs on the finite real
Fourier cutoffs `θ_N` of the weak solution (the coefficient integral paths of upstream
`weak_solution_mode_integral_path`): the chain rule in time for `j(θ_N(t,x))`, the sign
`∫ j''(θ_N)|∇θ_N|² ≥ 0` by periodic integration by parts, and the passage `N → ∞` in spacetime
`L²`, where the transport term tends to `∫∫ b·∇(j(θ_N)) = 0` (modules `Dissipation.EntropyCutoff`
and `Dissipation.EntropyLimit`, on the unit window; transported here to `[t₁, t₂]`). Positivity
follows from the family `j_ε(r) = (√(r² + ε²) - r)²`: `0 ≤ j_ε'' ≤ 24`, `j_ε(r) ≥ 4 r²` for
`r < 0` and `j_ε ≤ ε²` on `[0, ∞)`. -/

public section

open MeasureTheory Homogenization AVenhance

namespace AVRegularity.Applications.Dissipation

/-- The unit cell has finite measure. -/
local instance dissipationPositivityFiniteCube : IsFiniteMeasure (volume.restrict unitCube) :=
  isFiniteMeasure_restrict.2 unitCube_measure_ne_top

/-! ### The profile `j_ε(r) = (√(r² + ε²) - r)²` -/

/-- The convex profile `j_ε(r) = (√(r² + ε²) - r)²`, a smooth stand-in for `4 (r⁻)²`. -/
noncomputable def negPartEntropy (ε r : ℝ) : ℝ := (Real.sqrt (r ^ 2 + ε ^ 2) - r) ^ 2

/-- Its first derivative `-2 (ρ - r)² / ρ`, `ρ = √(r² + ε²)`. -/
noncomputable def negPartEntropyDeriv (ε r : ℝ) : ℝ :=
  -2 * (Real.sqrt (r ^ 2 + ε ^ 2) - r) ^ 2 / Real.sqrt (r ^ 2 + ε ^ 2)

/-- Its second derivative `2 (ρ - r)² (2ρ + r) / ρ³`. -/
noncomputable def negPartEntropyDeriv2 (ε r : ℝ) : ℝ :=
  2 * (Real.sqrt (r ^ 2 + ε ^ 2) - r) ^ 2 * (2 * Real.sqrt (r ^ 2 + ε ^ 2) + r) /
    Real.sqrt (r ^ 2 + ε ^ 2) ^ 3

private theorem negPartEntropy_base_pos {ε : ℝ} (hε : ε ≠ 0) (r : ℝ) : 0 < r ^ 2 + ε ^ 2 := by
  have := sq_pos_of_ne_zero hε
  positivity

private theorem negPartEntropy_sqrt_pos {ε : ℝ} (hε : ε ≠ 0) (r : ℝ) :
    0 < Real.sqrt (r ^ 2 + ε ^ 2) :=
  Real.sqrt_pos.2 (negPartEntropy_base_pos hε r)

private theorem negPartEntropy_abs_le_sqrt (ε r : ℝ) : |r| ≤ Real.sqrt (r ^ 2 + ε ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ε])

private theorem negPartEntropy_hasDerivAt_sqrt {ε : ℝ} (hε : ε ≠ 0) (r : ℝ) :
    HasDerivAt (fun y => Real.sqrt (y ^ 2 + ε ^ 2))
      (r / Real.sqrt (r ^ 2 + ε ^ 2)) r := by
  have h := ((hasDerivAt_pow 2 r).add_const (ε ^ 2)).sqrt (negPartEntropy_base_pos hε r).ne'
  convert h using 1
  have hs := negPartEntropy_sqrt_pos hε r
  field_simp
  push_cast
  ring

theorem hasDerivAt_negPartEntropy {ε : ℝ} (hε : ε ≠ 0) (r : ℝ) :
    HasDerivAt (negPartEntropy ε) (negPartEntropyDeriv ε r) r := by
  have h := ((negPartEntropy_hasDerivAt_sqrt hε r).fun_sub (hasDerivAt_id' r)).fun_pow 2
  unfold negPartEntropy negPartEntropyDeriv
  convert h using 1
  have hs := (negPartEntropy_sqrt_pos hε r).ne'
  norm_num
  field_simp
  ring

theorem hasDerivAt_negPartEntropyDeriv {ε : ℝ} (hε : ε ≠ 0) (r : ℝ) :
    HasDerivAt (negPartEntropyDeriv ε) (negPartEntropyDeriv2 ε r) r := by
  have hρ := negPartEntropy_hasDerivAt_sqrt hε r
  have hs := (negPartEntropy_sqrt_pos hε r).ne'
  have h := ((((hρ.fun_sub (hasDerivAt_id' r)).fun_pow 2).const_mul (-2)).fun_div hρ hs)
  unfold negPartEntropyDeriv negPartEntropyDeriv2
  convert h using 1
  norm_num
  field_simp
  ring

theorem deriv_negPartEntropy {ε : ℝ} (hε : ε ≠ 0) :
    deriv (negPartEntropy ε) = negPartEntropyDeriv ε :=
  funext fun r => (hasDerivAt_negPartEntropy hε r).deriv

theorem deriv_deriv_negPartEntropy {ε : ℝ} (hε : ε ≠ 0) :
    deriv (deriv (negPartEntropy ε)) = negPartEntropyDeriv2 ε := by
  rw [deriv_negPartEntropy hε]
  exact funext fun r => (hasDerivAt_negPartEntropyDeriv hε r).deriv

theorem contDiff_negPartEntropy {ε : ℝ} (hε : ε ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (negPartEntropy ε) := by
  have hρ : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => Real.sqrt (y ^ 2 + ε ^ 2)) :=
    ((contDiff_id.pow 2).add contDiff_const).sqrt fun y => (negPartEntropy_base_pos hε y).ne'
  exact (hρ.sub contDiff_id).pow 2

theorem negPartEntropyDeriv2_nonneg {ε : ℝ} (hε : ε ≠ 0) (r : ℝ) :
    0 ≤ negPartEntropyDeriv2 ε r := by
  have hs := negPartEntropy_sqrt_pos hε r
  have habs := negPartEntropy_abs_le_sqrt ε r
  have h2 : 0 ≤ 2 * Real.sqrt (r ^ 2 + ε ^ 2) + r := by
    have := neg_abs_le r
    linarith
  unfold negPartEntropyDeriv2
  positivity

theorem negPartEntropyDeriv2_le {ε : ℝ} (hε : ε ≠ 0) (r : ℝ) :
    negPartEntropyDeriv2 ε r ≤ 24 := by
  have hs := negPartEntropy_sqrt_pos hε r
  have habs := negPartEntropy_abs_le_sqrt ε r
  set ρ := Real.sqrt (r ^ 2 + ε ^ 2) with hρ
  have hr1 : -ρ ≤ r := by have := neg_abs_le r; linarith
  have hr2 : r ≤ ρ := (le_abs_self r).trans habs
  have hφ : (ρ - r) ^ 2 ≤ 4 * ρ ^ 2 := by nlinarith
  have hl : 2 * ρ + r ≤ 3 * ρ := by linarith
  have hl0 : 0 ≤ 2 * ρ + r := by linarith
  unfold negPartEntropyDeriv2
  rw [← hρ, div_le_iff₀ (by positivity)]
  calc 2 * (ρ - r) ^ 2 * (2 * ρ + r) ≤ 2 * (4 * ρ ^ 2) * (3 * ρ) := by
        apply mul_le_mul (by linarith) hl hl0 (by positivity)
    _ = 24 * ρ ^ 3 := by ring

theorem four_mul_sq_le_negPartEntropy (ε : ℝ) {r : ℝ} (hr : r ≤ 0) :
    4 * r ^ 2 ≤ negPartEntropy ε r := by
  have habs := negPartEntropy_abs_le_sqrt ε r
  rw [abs_of_nonpos hr] at habs
  unfold negPartEntropy
  nlinarith

theorem negPartEntropy_le_sq {ε : ℝ} (hε : ε ≠ 0) {r : ℝ} (hr : 0 ≤ r) :
    negPartEntropy ε r ≤ ε ^ 2 := by
  have hs := negPartEntropy_sqrt_pos hε r
  have habs := negPartEntropy_abs_le_sqrt ε r
  set ρ := Real.sqrt (r ^ 2 + ε ^ 2) with hρ
  have hρ2 : ρ ^ 2 = r ^ 2 + ε ^ 2 := Real.sq_sqrt (negPartEntropy_base_pos hε r).le
  have hrρ : r ≤ ρ := (le_abs_self r).trans habs
  have hε' : ε ^ 2 ≤ ρ ^ 2 := by rw [hρ2]; nlinarith
  -- `(ρ - r)(ρ + r) = ε²`, so `0 ≤ ρ - r ≤ ε² / ρ` and `(ρ - r)² ≤ ε⁴ / ρ² ≤ ε²`
  have hprod : (ρ - r) * (ρ + r) = ε ^ 2 := by nlinarith
  have h1 : (ρ - r) * ρ ≤ ε ^ 2 := by nlinarith
  have h2 : 0 ≤ ρ - r := by linarith
  unfold negPartEntropy
  rw [← hρ]
  nlinarith [mul_le_mul h1 h1 (by positivity) (by positivity)]

/-! ### The window form -/

/-- **Convex entropy inequality.** For a smooth convex `j` with bounded second derivative,
`∫_{𝕋²} j(θ(t)) ≤ ∫_{𝕋²} j(f)` for every `t` in the window. -/
theorem integral_convex_le_of_isWeakSolutionOnWith {j : ℝ → ℝ} (hj : ContDiff ℝ (⊤ : ℕ∞) j)
    (hj₂ : ∀ r, 0 ≤ deriv (deriv j) r) (hjL : ∃ L : ℝ, ∀ r, deriv (deriv j) r ≤ L)
    {b : ℝ → Vec 2 → Vec 2} {κ t₁ t₂ : ℝ} (hκ : 0 ≤ κ) (h12 : t₁ < t₂)
    (hb : IsWindowDrift b t₁ t₂) {f : Vec 2 → ℝ} (hf : MemL2On unitCube f)
    {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2}
    (hθ : IsWeakSolutionOnWith b κ t₁ t₂ f θ Dθ) :
    ∀ t ∈ Set.Icc t₁ t₂, ∫ x in unitCube, j (θ t x) ≤ ∫ x in unitCube, j (f x) := by
  intro t ht
  obtain ⟨T, hT, rfl⟩ : ∃ T, 0 < T ∧ t₂ = t₁ + T := ⟨t₂ - t₁, by linarith, by ring⟩
  obtain ⟨hbm, ⟨C, hC⟩, hbp, hdiv⟩ := hb
  have hbridge := isWeakSolutionOnWith_to_isWeakSolutionGrad hT hθ
  have hrm : Measurable (fun p : ℝ × Vec 2 => Wellposed.rescaledDrift b t₁ T p.1 p.2) := by
    have h1 : Measurable (fun p : ℝ × Vec 2 => b (Wellposed.timeForward t₁ T p.1) p.2) :=
      hbm.comp (Wellposed.measurable_windowForward t₁ T)
    exact h1.const_smul T
  have hrb : ∃ C' : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ x, ‖Wellposed.rescaledDrift b t₁ T s x‖ ≤ C' := by
    refine ⟨T * C, fun s hs x => ?_⟩
    have := hC _ (Wellposed.timeForward_mem_Icc (t₁ := t₁) hT hs) x
    change ‖T • b (Wellposed.timeForward t₁ T s) x‖ ≤ T * C
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hT]
    exact mul_le_mul_of_nonneg_left this hT.le
  have hrp : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsZ2Periodic (Wellposed.rescaledDrift b t₁ T s) := by
    intro s hs k x
    change T • b (Wellposed.timeForward t₁ T s) (x + latticeShift k) =
      T • b (Wellposed.timeForward t₁ T s) x
    rw [hbp _ (Wellposed.timeForward_mem_Icc (t₁ := t₁) hT hs) k x]
  have hrd : IsDivFree (Wellposed.rescaledDrift b t₁ T) := by
    intro s hs φ hφ hφc
    have h0 := hdiv _ (Wellposed.timeForward_mem_Icc (t₁ := t₁) hT hs) φ hφ hφc
    change ∫ x, vecDot (T • b (Wellposed.timeForward t₁ T s) x) (spaceGrad φ x) = 0
    simp_rw [Homogenization.vecDot_smul_left]
    rw [integral_const_mul, h0, mul_zero]
  have hs : (t - t₁) / T ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (by linarith [ht.1]) hT.le, (div_le_one hT).2 (by linarith [ht.2])⟩
  have h := integral_convex_le_of_isWeakSolutionGrad (mul_nonneg hT.le hκ) hbridge hf
    hrm.aestronglyMeasurable hrb hrp hrd hj hj₂ hjL _ hs
  have htime : Wellposed.timeForward t₁ T ((t - t₁) / T) = t := by
    unfold Wellposed.timeForward
    field_simp
    ring
  simpa [Wellposed.stateToUnit, htime] using h

/-- **Positivity.** For a divergence-free window drift and `κ ≥ 0`, a weak solution with
nonnegative datum is nonnegative on every slice. -/
theorem ae_nonneg_of_isWeakSolutionOnWith {b : ℝ → Vec 2 → Vec 2} {κ t₁ t₂ : ℝ}
    (hκ : 0 ≤ κ) (h12 : t₁ < t₂) (hb : IsWindowDrift b t₁ t₂) {f : Vec 2 → ℝ}
    (hf : MemL2On unitCube f) (hf₀ : ∀ᵐ x ∂(volume.restrict unitCube), 0 ≤ f x)
    {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2}
    (hθ : IsWeakSolutionOnWith b κ t₁ t₂ f θ Dθ) :
    ∀ t ∈ Set.Icc t₁ t₂, ∀ᵐ x ∂(volume.restrict unitCube), 0 ≤ θ t x := by
  intro t ht
  have hθt : MemL2On unitCube (θ t) := (hθ.1 t ht).2
  have hvol : (volume : Measure (Vec 2)) unitCube = 1 := by
    unfold unitCube
    rw [volume_pi, Measure.pi_pi]
    simp [Real.volume_Ioo]
  have hneg : Integrable (fun x => 4 * min (θ t x) 0 ^ 2) (volume.restrict unitCube) := by
    refine (hθt.integrable_sq.const_mul 4).mono' ((hθt.aestronglyMeasurable.inf
      aestronglyMeasurable_const).pow 2 |>.const_mul 4) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * min (θ t x) 0 ^ 2)]
    have : min (θ t x) 0 ^ 2 ≤ θ t x ^ 2 := by
      rcases le_total (θ t x) 0 with h | h
      · rw [min_eq_left h]
      · rw [min_eq_right h]; nlinarith [sq_nonneg (θ t x)]
    linarith
  -- `∫ 4 (θ⁻)² ≤ ε²` for every `ε > 0`
  have hbound : ∀ ε : ℝ, 0 < ε → ∫ x in unitCube, 4 * min (θ t x) 0 ^ 2 ≤ ε ^ 2 := by
    intro ε hε
    have hε0 := hε.ne'
    have hL : ∀ r, |deriv (deriv (negPartEntropy ε)) r| ≤ 24 := fun r => by
      rw [deriv_deriv_negPartEntropy hε0, abs_of_nonneg (negPartEntropyDeriv2_nonneg hε0 r)]
      exact negPartEntropyDeriv2_le hε0 r
    have hent := integral_convex_le_of_isWeakSolutionOnWith (contDiff_negPartEntropy hε0)
      (fun r => by rw [deriv_deriv_negPartEntropy hε0]; exact negPartEntropyDeriv2_nonneg hε0 r)
      ⟨24, fun r => by rw [deriv_deriv_negPartEntropy hε0]; exact negPartEntropyDeriv2_le hε0 r⟩
      hκ h12 hb hf hθ t ht
    have h1 : ∫ x in unitCube, 4 * min (θ t x) 0 ^ 2 ≤
        ∫ x in unitCube, negPartEntropy ε (θ t x) := by
      refine integral_mono hneg (integrable_comp_of_abs_deriv2_le (contDiff_negPartEntropy hε0)
        hL hθt) fun x => ?_
      rcases le_total (θ t x) 0 with h | h
      · rw [min_eq_left h]
        exact four_mul_sq_le_negPartEntropy ε h
      · rw [min_eq_right h]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
        exact sq_nonneg _
    have h2 : ∫ x in unitCube, negPartEntropy ε (f x) ≤ ∫ x in unitCube, ε ^ 2 := by
      refine integral_mono_ae (integrable_comp_of_abs_deriv2_le (contDiff_negPartEntropy hε0)
        hL hf) (integrable_const _) ?_
      filter_upwards [hf₀] with x hx
      exact negPartEntropy_le_sq hε0 hx
    have h3 : ∫ x in unitCube, ε ^ 2 = ε ^ 2 := by
      rw [integral_const, Measure.real, Measure.restrict_apply_univ, hvol]
      simp
    linarith
  have hzero : ∫ x in unitCube, 4 * min (θ t x) 0 ^ 2 ≤ 0 := by
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have := hbound (Real.sqrt δ) (Real.sqrt_pos.2 hδ)
    rw [Real.sq_sqrt hδ.le] at this
    linarith
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => by simp only [Pi.zero_apply]; positivity)
    hneg).1
    (le_antisymm hzero (integral_nonneg fun x => by positivity))
  filter_upwards [hae] with x hx
  have : min (θ t x) 0 = 0 := by
    have h4 : 4 * min (θ t x) 0 ^ 2 = 0 := hx
    have h5 : min (θ t x) 0 ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff (two_ne_zero) |>.1 h5
  by_contra hlt
  push Not at hlt
  rw [min_eq_left hlt.le] at this
  linarith

end AVRegularity.Applications.Dissipation

end
