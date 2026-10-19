-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.MixedWords.WeightedPlainDecayKappa
import AVRegularity.CycleWords.MixedWords.SharpDecayLoop
public import AVRegularity.CycleWords.Assembly.MixedWordsB1SharpSlow
import AVRegularity.CycleWords.MixedWords.B1WData
public import AVRegularity.CycleWords.Assembly.InteriorScalarIngredients
import AVRegularity.CycleWords.MixedWords.StageExpansionLetter

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # Weighted plain decay: quiet stretch, then the crude decay

An actual-fast reversed curve decays on the quiet stretch `[σ, t]` at `π²/2` (constant `3`), and
then crudely at `π²/8` with the price `C_c P_e^Q` from `σ` down to `a`. -/

/-- Fastness persists along the reversed curve. -/
theorem wpd_fast_mid {K : ScalarConstants} {η t₀ S : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {v : ℝ → Vec 2 → Vec 2} {ξ : Fin 2 → ℂ} (H : TransverseLocalHyp K η G v ξ)
    (data : FibreScalarData K η G v t₀ S) {a t : ℝ} (V : ℝ)
    (hb' : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2)
    {u : ℝ → ComplexCellL2} {slice : ℝ → TorusHk 1 ℂ} (hu : IsRevCurve H V hb' (-t) (-a) u slice)
    (hfast : cellComplexPair (cellRawTrace (fibreSeriesJet data.r ξ) t + cellConstantCLM 1)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u (-t))) = 0) {σ : ℝ}
    (hσ : σ ∈ Icc a t) :
    cellComplexPair (cellRawTrace (fibreSeriesJet data.r ξ) σ + cellConstantCLM 1)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u (-σ))) = 0 := by
  rw [revCurve_pairing H.hη0 H.hη H.hCg H.hCw H.hG H.hv H.hm H.hw data ξ H.hξ V hb' hu σ hσ,
    hfast, mul_zero]

/-- Restriction of a reversed curve to a subinterval. -/
theorem wpd_isRev_mono {K : ScalarConstants} {η : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {v : ℝ → Vec 2 → Vec 2} {ξ : Fin 2 → ℂ} (H : TransverseLocalHyp K η G v ξ) (V : ℝ)
    (hb' : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2) {a b c d : ℝ}
    {u : ℝ → ComplexCellL2} {slice : ℝ → TorusHk 1 ℂ} (hu : IsRevCurve H V hb' a b u slice)
    (hca : a ≤ c) (hdb : d ≤ b) : IsRevCurve H V hb' c d u slice :=
  CellWeakHilbertCurve.mono hu (Icc_subset_Icc hca hdb)

/-- **Quiet stretch `[σ, t]`, then the crude decay down to `a`.** (For `σ = t` no quiet hypothesis.) -/
theorem wpd_quiet_crude (hQ : QuietHsDecayStatement) (K : ScalarConstants) (j : ℕ) (ρ : ℝ) :
    ∃ (C : ℝ) (Q : ℕ), 1 ≤ C ∧
    ∀ (η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (ξ : Fin 2 → ℂ)
      (H : TransverseLocalHyp K η G v ξ) {t₀ S : ℝ} (data : FibreScalarData K η G v t₀ S),
      0 < η → fibreNorm ξ ≤ ρ → (∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
      (∀ (l : ℕ) t z, ‖iteratedFDeriv ℝ l (fun z' => Real.sqrt η • v t z') z‖ ≤ K.Cvj l) →
    ∀ (V : ℝ) (hb' : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2) {a σ t : ℝ}, a ≤ σ → σ ≤ t →
      (σ < t → ∀ r ∈ Icc σ t, ∀ x, v r x = 0) →
    ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ), IsRevCurve H V hb' (-t) (-a) u slice →
      cellComplexPair (cellRawTrace (fibreSeriesJet data.r ξ) t + cellConstantCLM 1)
        (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u (-t))) = 0 →
    ∀ w₀ : TorusHk j ℂ, torusHkValueCLM w₀ = u (-t) →
      ∃ w : TorusHk j ℂ, torusHkValueCLM w = u (-a) ∧
        ‖w‖ ≤ C * peFactor η ^ Q * Real.exp (-(Real.pi ^ 2 / 2) * (t - σ)) *
          Real.exp (-(Real.pi ^ 2 / 8) * (σ - a)) * ‖w₀‖ := by
  obtain ⟨Cc, Q, hCc, hcrude⟩ := revCurve_crude_decay (K := K) cellDriftRegularity j
    (le_max_right ρ 0) (fun l => max (K.Cvj l) 0) (fun l => le_max_right _ _)
  refine ⟨max 1 (3 * Cc), Q, le_max_left _ _, ?_⟩
  intro η G v ξ H t₀ S data hη hξρ hvs hvj V hb' a σ t haσ hσt hquiet u slice hu hfast w₀ hw₀
  have hfσ := wpd_fast_mid H data V hb' hu hfast ⟨haσ, hσt⟩
  obtain ⟨w₁, hw₁, hn₁⟩ : ∃ w₁ : TorusHk j ℂ, torusHkValueCLM w₁ = u (-σ) ∧
      ‖w₁‖ ≤ 3 * Real.exp (-(Real.pi ^ 2 / 2) * (t - σ)) * ‖w₀‖ := by
    rcases hσt.eq_or_lt with h | h
    · subst h
      refine ⟨w₀, hw₀, ?_⟩
      simp only [sub_self, mul_zero, Real.exp_zero, mul_one]
      nlinarith [norm_nonneg w₀]
    · exact sharpQuiet_decay hQ H data j hσt V hb' (hquiet h)
        (wpd_isRev_mono H V hb' hu le_rfl (by linarith)) hfast w₀ hw₀
  obtain ⟨w, hw, hn⟩ := hcrude η G v ξ H data hη (hξρ.trans (le_max_left _ _)) hvs
    (fun l t z => (hvj l t z).trans (le_max_left _ _)) V hb' haσ u slice
    (wpd_isRev_mono H V hb' hu (by linarith) le_rfl) hfσ w₁ hw₁
  refine ⟨w, hw, hn.trans ?_⟩
  have hP : 0 ≤ peFactor η ^ Q := by
    have : 0 < peFactor η := by unfold peFactor; positivity
    positivity
  have he1 := Real.exp_pos (-(Real.pi ^ 2 / 8) * (σ - a))
  calc Cc * peFactor η ^ Q * Real.exp (-(Real.pi ^ 2 / 8) * (σ - a)) * ‖w₁‖
      ≤ Cc * peFactor η ^ Q * Real.exp (-(Real.pi ^ 2 / 8) * (σ - a)) *
        (3 * Real.exp (-(Real.pi ^ 2 / 2) * (t - σ)) * ‖w₀‖) := by gcongr
    _ = (3 * Cc) * peFactor η ^ Q * Real.exp (-(Real.pi ^ 2 / 2) * (t - σ)) *
          Real.exp (-(Real.pi ^ 2 / 8) * (σ - a)) * ‖w₀‖ := by ring
    _ ≤ _ := by
      have := le_max_right 1 (3 * Cc)
      have h2 : 0 ≤ peFactor η ^ Q * Real.exp (-(Real.pi ^ 2 / 2) * (t - σ)) *
          Real.exp (-(Real.pi ^ 2 / 8) * (σ - a)) * ‖w₀‖ := by positivity
      nlinarith

/-! # Sharp fast decay: the statements and the assembly

* `SharpWindowLemmaStatement`: the window lemma (OPEN, the last analytic input): on the extended
  window `t ∈ [lo_p, hi_p + D/2]`, a transverse actual-fast datum decays at `π²/8` back to every
  `s ∈ [lo_p − D, hi_p]`, with a constant free of `P_e`.
* The crossing lemma is `revCurve_crude_decay` (with `cellDriftRegularity`): a
  crude crossing costs `C P_e^Q` and keeps the rate `π²/8`; no transverse splitting is needed,
  because the quiet buffer to the left of the window restores the invariant `ε ≤ 1/(3 Bx)`
  (`SharpDecayLoop`).
* The quiet lemma is `sharpQuiet_decay`.
* `sharpFastDecay_of_window`: the assembly.

-/

/-- **The window lemma.** -/
def SharpWindowLemmaStatement : Prop :=
  ∀ (K : ScalarConstants) (j : ℕ) (ρ : ℝ), ρ < K.ξ0 → ρ ≤ 2 * K.ξlo →
  ∃ (C₁ Cb c : ℝ) (Q : ℕ), 1 ≤ C₁ ∧ 0 < c ∧
  ∀ (η t₀ S ϖ : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (g : ℝ)
    (reg : BlockRegions) (pkg : CoreScalarPackage K η G v t₀ S ϖ reg),
    0 < η → (∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
    (∀ (i : ℕ) t z, ‖iteratedFDeriv ℝ i (fun z' => Real.sqrt η • v t z') z‖ ≤ K.Cvj i) →
    0 ≤ g → g ≤ K.g0 → IsMetricNearIdentity (fun t _ => G t) g →
  ∀ (ξ : Fin 2 → ℂ) (H : TransverseLocalHyp K η G v ξ), fibreNorm ξ ≤ ρ →
    Cb * (1 + (reg.joins : ℝ)) * peFactor η ^ Q * Real.exp (-c * reg.buffer) ≤ 1 →
  ∀ (V : ℝ) (hb' : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2) {s t : ℝ}, t₀ ≤ s → s ≤ t →
    t ≤ t₀ + S →
  ∀ p : Fin reg.P, reg.lo p ≤ t → t ≤ reg.hi p + reg.buffer / 2 →
    reg.lo p - reg.buffer ≤ s → s ≤ reg.hi p → reg.lo p ≤ reg.hi p →
  ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ), IsRevCurve H V hb' (-t) (-s) u slice →
    cellComplexPair (cellRawTrace (fibreSeriesJet pkg.actual.r ξ) t + cellConstantCLM 1)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u (-t))) = 0 →
    cellTransverseProjection (reg.orient p) (u (-t)) = u (-t) →
  ∀ w₀ : TorusHk j ℂ, torusHkValueCLM w₀ = u (-t) →
    ∃ w : TorusHk j ℂ, torusHkValueCLM w = u (-s) ∧
      ‖w‖ ≤ C₁ * Real.exp (-(Real.pi ^ 2 / 8) * (t - s)) * ‖w₀‖

/-! # Weighted plain decay: splitting the reversed curve

A reversed curve `u` splits as `u_A + u_B`, where `u_A` is the reversed curve from a chosen datum
`A` and `u_B = u − u_A` is a reversed curve (`revCurve_smul_sub`). -/

/-- **The splitting of a reversed curve** by its datum at `−t`. -/
theorem wpd_split_curve {K : ScalarConstants} {η : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {v : ℝ → Vec 2 → Vec 2} {ξ : Fin 2 → ℂ} (H : TransverseLocalHyp K η G v ξ) (V : ℝ)
    (hb' : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2) {s t : ℝ} (hst : s ≤ t)
    {u : ℝ → ComplexCellL2} {slice : ℝ → TorusHk 1 ℂ} (hu : IsRevCurve H V hb' (-t) (-s) u slice)
    (A : ComplexCellL2) :
    ∃ (uA uB : ℝ → ComplexCellL2) (sA sB : ℝ → TorusHk 1 ℂ),
      IsRevCurve H V hb' (-t) (-s) uA sA ∧ IsRevCurve H V hb' (-t) (-s) uB sB ∧
      uA (-t) = A ∧ uB (-t) = u (-t) - A ∧ ∀ τ, uA τ + uB τ = u τ := by
  obtain ⟨uA, sA, huA, h0⟩ := revCurve_exists H V hb' (a := -t) (b := -s) (by linarith) A
  refine ⟨uA, fun τ => cellScalarCLM 1 (u τ) - uA τ, sA,
    fun τ => cellH1Scalar 1 (slice τ) - sA τ, huA, revCurve_smul_sub H V hb' hu huA 1, h0, ?_, ?_⟩
  · simp only [cellScalarCLM_smul, one_smul, h0]
  · intro τ
    simp only [cellScalarCLM_smul, one_smul]
    abel

/-- The graph trace is at most `1/3` in `L²`. -/
theorem wpd_trace_small {K : ScalarConstants} {η t₀ S : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {v : ℝ → Vec 2 → Vec 2} {ξ : Fin 2 → ℂ} (H : TransverseLocalHyp K η G v ξ)
    (data : FibreScalarData K η G v t₀ S) (t : ℝ) :
    ‖cellRawTrace (fibreSeriesJet data.r ξ) t + cellConstantCLM 1 - cellConstantCLM 1‖ ≤ 1 / 3 := by
  have hsmall := graphTrace_l2_small H.hη0 H.hη H.hCg H.hCw H.hG H.hv H.hm H.hw data ξ H.hreal
    H.hξ H.hsep t
  have h0' := norm_nonneg (cellRawTrace (fibreSeriesJet data.r ξ) t)
  rw [add_sub_cancel_right]
  nlinarith

theorem wpd_abel1 {M : Type*} [AddCommGroup M] (a b c : M) : a + b - c = a + b + -c := by
  abel

theorem wpd_abel2 {M : Type*} [AddCommGroup M] (a b c d : M) :
    a + b + -c + (d - b + c) = a + d := by abel

theorem wpd_abel3 {M : Type*} [AddCommGroup M] (a b d : M) : a + b + (d - b) = a + d := by
  abel

/-- The value identities of the split. -/
theorem wpd_values (j : ℕ) (P : TorusHk j ℂ →L[ℝ] TorusHk j ℂ) (UT UN AH BH : TorusHk j ℂ)
    (κ : ℂ)
    (hAH : torusHkValueCLM AH = torusHkValueCLM (UT + P UN) + cellConstantCLM (-κ))
    (hBH : torusHkValueCLM BH = torusHkValueCLM (UN - P UN) + cellConstantCLM κ) :
    torusHkValueCLM AH = torusHkValueCLM UT + torusHkValueCLM (P UN) - cellConstantCLM κ ∧
      torusHkValueCLM AH + torusHkValueCLM BH = torusHkValueCLM (UT + UN) := by
  have e1 : torusHkValueCLM (UT + P UN) = torusHkValueCLM UT + torusHkValueCLM (P UN) :=
    map_add _ _ _
  have e2 : torusHkValueCLM (UN - P UN) = torusHkValueCLM UN - torusHkValueCLM (P UN) :=
    map_sub _ _ _
  have e3 : cellConstantCLM (-κ) = -cellConstantCLM κ := map_neg _ _
  have e4 : torusHkValueCLM (UT + UN) = torusHkValueCLM UT + torusHkValueCLM UN := map_add _ _ _
  constructor
  · rw [hAH, e1, e3, wpd_abel1]
  · rw [hAH, hBH, e1, e2, e3, e4]
    exact wpd_abel2 _ _ _ _

/-- **The split of the datum** `U_T + U_N = A + B`, correcting by the constant `1`. -/
theorem wpd_split_data (F : ComplexCellL2) (hF : ‖F - cellConstantCLM 1‖ ≤ 1 / 3) (j : ℕ)
    (P : TorusHk j ℂ →L[ℝ] TorusHk j ℂ) (hPn : ∀ U, ‖P U‖ ≤ ‖U‖) (UT UN : TorusHk j ℂ)
    (hfast : cellComplexPair F (cellFiberCLM Complex.conjCLE.toContinuousLinearMap
      (torusHkValueCLM (UT + UN))) = 0) :
    ∃ (AH BH : TorusHk j ℂ) (κ : ℂ), ‖AH‖ ≤ ‖UT‖ + 5 * ‖UN‖ ∧ ‖BH‖ ≤ 6 * ‖UN‖ ∧
      torusHkValueCLM AH = torusHkValueCLM UT + torusHkValueCLM (P UN) - cellConstantCLM κ ∧
      torusHkValueCLM AH + torusHkValueCLM BH = torusHkValueCLM (UT + UN) ∧
      cellComplexPair F (cellFiberCLM Complex.conjCLE.toContinuousLinearMap
        (torusHkValueCLM AH)) = 0 := by
  have hXY : torusHkValueCLM UT + torusHkValueCLM (P UN) +
      (torusHkValueCLM UN - torusHkValueCLM (P UN)) = torusHkValueCLM (UT + UN) := by
    rw [map_add]; exact wpd_abel3 _ _ _
  obtain ⟨κ, hκf, hκn⟩ := wpd_kappa F (torusHkValueCLM UT + torusHkValueCLM (P UN))
    (torusHkValueCLM UN - torusHkValueCLM (P UN)) hF (by rw [hXY]; exact hfast)
  have hY : ‖torusHkValueCLM UN - torusHkValueCLM (P UN)‖ ≤ 2 * ‖UN‖ := by
    refine (norm_sub_le _ _).trans ?_
    have h1 := torusHk_value_norm_le UN
    have h2 := (torusHk_value_norm_le (P UN)).trans (hPn UN)
    linarith only [h1, h2]
  have hκ4 : ‖κ‖ ≤ 4 * ‖UN‖ := by linarith only [hκn, hY]
  obtain ⟨AH, hAH, hAn⟩ := sharpMean_add_const j (UT + P UN) (-κ)
  obtain ⟨BH, hBH, hBn⟩ := sharpMean_add_const j (UN - P UN) κ
  have hPUT : ‖UT + P UN‖ ≤ ‖UT‖ + ‖UN‖ := (norm_add_le _ _).trans (by linarith only [hPn UN])
  have hPUN : ‖UN - P UN‖ ≤ 2 * ‖UN‖ := (norm_sub_le _ _).trans (by linarith only [hPn UN])
  have hnk : ‖(-κ : ℂ)‖ = ‖κ‖ := norm_neg κ
  obtain ⟨hAval, hsum⟩ := wpd_values j P UT UN AH BH κ hAH hBH
  refine ⟨AH, BH, κ, by linarith only [hAn, hPUT, hκ4, hnk], by linarith only [hBn, hPUN, hκ4],
    hAval, hsum, ?_⟩
  rw [hAval]; exact hκf

/-! # Sharp fast decay: the assembly from the window lemma

`sharpFastDecay_of_window`: the quiet lemma (`sharpQuiet_decay`), the crude crossing
(`revCurve_crude_decay`, `cellDriftRegularity`) and the window lemma (hypothesis) give the sharp
fast decay, through the combinatorial loop of `SharpDecayLoop`. -/

theorem sharpAsm_exp_quiet (τ σ t : ℝ) :
    Real.exp (-(Real.pi ^ 2 / 2) * (τ - σ)) * Real.exp (-(Real.pi ^ 2 / 8) * (t - τ)) =
      Real.exp (-(3 * Real.pi ^ 2 / 8) * (τ - σ)) * Real.exp (-(Real.pi ^ 2 / 8) * (t - σ)) := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem sharpAsm_exp_crude (τ σ t : ℝ) :
    Real.exp (-(Real.pi ^ 2 / 8) * (τ - σ)) * Real.exp (-(Real.pi ^ 2 / 8) * (t - τ)) =
      Real.exp (-(Real.pi ^ 2 / 8) * (t - σ)) := by
  rw [← Real.exp_add]
  congr 1
  ring

theorem sharpAsm_ha (D x : ℝ) (hx : D / 4 ≤ x) :
    Real.exp (-(3 * Real.pi ^ 2 / 8) * x) ≤ Real.exp (-(3 * Real.pi ^ 2 / 32) * D) := by
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hx (show (0 : ℝ) ≤ 3 * Real.pi ^ 2 / 8 by positivity)
  linarith

theorem sharpAsm_peFactor_ge_one (η : ℝ) : 1 ≤ peFactor η := by
  unfold peFactor
  have : 0 ≤ (Real.sqrt η)⁻¹ := by positivity
  linarith

/-- **Sharp fast decay from the window lemma.** -/
theorem sharpFastDecay_of_window (hQ : QuietHsDecayStatement) (hW : SharpWindowLemmaStatement) :
    SharpFastDecayStatement := by
  intro K j ρ hρ0 hρ1
  obtain ⟨C₁, Cb₁, c₁, Q₁, hC₁, hc₁, hWC⟩ := hW K j ρ hρ0 hρ1
  obtain ⟨Cx, Qx, hCx, hcr⟩ := revCurve_crude_decay (K := K) cellDriftRegularity j
    (ρ := max ρ 0) (le_max_right _ _) (fun l => max (K.Cvj l) 0) (fun l => le_max_right _ _)
  have hCx1 : 1 ≤ max Cx 1 := le_max_right _ _
  have hCxle : Cx ≤ max Cx 1 := le_max_left _ _
  have hcpos : 0 < min c₁ (3 * Real.pi ^ 2 / 32) := lt_min hc₁ (by positivity)
  refine ⟨3 * C₁, |Cb₁| + 9 * C₁ * max Cx 1 + 2, min c₁ (3 * Real.pi ^ 2 / 32),
    max Qx Q₁, by linarith, hcpos, ?_⟩
  intro η t₀ S ϖ G v g reg pkg hη hvs hvj hg0 hg1 hmet ξ H hξρ hreg V hb' s t ht0 hst
    htS u slice hu hfast htrans w₀ hw₀
  have hP1 := sharpAsm_peFactor_ge_one η
  have hP0 : 0 < peFactor η := by linarith
  have hD0 := pkg.buffer_nonneg
  have hCb : 2 ≤ |Cb₁| + 9 * C₁ * max Cx 1 + 2 := by
    have := abs_nonneg Cb₁
    have : 0 ≤ 9 * C₁ * max Cx 1 := by positivity
    linarith
  have hA : (1 : ℝ) ≤ 1 + (reg.joins : ℝ) := by
    have : (0 : ℝ) ≤ reg.joins := Nat.cast_nonneg _
    linarith
  have hPQ : ∀ q ≤ max Qx Q₁, peFactor η ^ q ≤ peFactor η ^ (max Qx Q₁) :=
    fun q hq => pow_le_pow_right₀ hP1 hq
  have hPQ1 : 1 ≤ peFactor η ^ (max Qx Q₁) := one_le_pow₀ hP1
  have hD : 0 < reg.buffer := by
    rcases hD0.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at hreg
      simp only [mul_zero, Real.exp_zero, mul_one] at hreg
      have h1 : 1 ≤ (1 + (reg.joins : ℝ)) * peFactor η ^ (max Qx Q₁) :=
        one_le_mul_of_one_le_of_one_le hA hPQ1
      nlinarith
  have hcle1 : min c₁ (3 * Real.pi ^ 2 / 32) ≤ c₁ := min_le_left _ _
  have hcle2 : min c₁ (3 * Real.pi ^ 2 / 32) ≤ 3 * Real.pi ^ 2 / 32 := min_le_right _ _
  have he1 : Real.exp (-c₁ * reg.buffer) ≤ Real.exp (-(min c₁ (3 * Real.pi ^ 2 / 32)) * reg.buffer) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have he2 : Real.exp (-(3 * Real.pi ^ 2 / 32) * reg.buffer) ≤
      Real.exp (-(min c₁ (3 * Real.pi ^ 2 / 32)) * reg.buffer) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hX2 : 0 ≤ (1 + (reg.joins : ℝ)) * peFactor η ^ (max Qx Q₁) *
      Real.exp (-(min c₁ (3 * Real.pi ^ 2 / 32)) * reg.buffer) := by positivity
  have hWreg : Cb₁ * (1 + (reg.joins : ℝ)) * peFactor η ^ Q₁ * Real.exp (-c₁ * reg.buffer) ≤ 1 := by
    refine le_trans ?_ hreg
    have hX1 : 0 ≤ (1 + (reg.joins : ℝ)) * peFactor η ^ Q₁ * Real.exp (-c₁ * reg.buffer) := by
      positivity
    have hX12 : (1 + (reg.joins : ℝ)) * peFactor η ^ Q₁ * Real.exp (-c₁ * reg.buffer) ≤
        (1 + (reg.joins : ℝ)) * peFactor η ^ (max Qx Q₁) *
          Real.exp (-(min c₁ (3 * Real.pi ^ 2 / 32)) * reg.buffer) := by
      have := hPQ Q₁ (le_max_right _ _)
      have h0 : 0 < 1 + (reg.joins : ℝ) := by linarith
      calc (1 + (reg.joins : ℝ)) * peFactor η ^ Q₁ * Real.exp (-c₁ * reg.buffer)
          ≤ (1 + (reg.joins : ℝ)) * peFactor η ^ (max Qx Q₁) * Real.exp (-c₁ * reg.buffer) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this h0.le) (Real.exp_pos _).le
        _ ≤ _ := mul_le_mul_of_nonneg_left he1 (by positivity)
    have hCb1 : Cb₁ ≤ |Cb₁| + 9 * C₁ * max Cx 1 + 2 := by
      have := le_abs_self Cb₁
      have : 0 ≤ 9 * C₁ * max Cx 1 := by positivity
      linarith
    calc Cb₁ * (1 + (reg.joins : ℝ)) * peFactor η ^ Q₁ * Real.exp (-c₁ * reg.buffer)
        = Cb₁ * ((1 + (reg.joins : ℝ)) * peFactor η ^ Q₁ * Real.exp (-c₁ * reg.buffer)) := by ring
      _ ≤ (|Cb₁| + 9 * C₁ * max Cx 1 + 2) *
            ((1 + (reg.joins : ℝ)) * peFactor η ^ Q₁ * Real.exp (-c₁ * reg.buffer)) :=
          mul_le_mul_of_nonneg_right hCb1 hX1
      _ ≤ (|Cb₁| + 9 * C₁ * max Cx 1 + 2) * ((1 + (reg.joins : ℝ)) * peFactor η ^ (max Qx Q₁) *
            Real.exp (-(min c₁ (3 * Real.pi ^ 2 / 32)) * reg.buffer)) :=
          mul_le_mul_of_nonneg_left hX12 (by linarith)
      _ = _ := by ring
  have hnum : 9 * C₁ * (max Cx 1 * peFactor η ^ Qx) * Real.exp (-(3 * Real.pi ^ 2 / 32) * reg.buffer)
      ≤ 1 := by
    refine le_trans ?_ hreg
    have h9 : 9 * C₁ * max Cx 1 ≤ |Cb₁| + 9 * C₁ * max Cx 1 + 2 := by
      have := abs_nonneg Cb₁
      linarith
    have hy : peFactor η ^ Qx * Real.exp (-(3 * Real.pi ^ 2 / 32) * reg.buffer) ≤
        (1 + (reg.joins : ℝ)) * peFactor η ^ (max Qx Q₁) *
          Real.exp (-(min c₁ (3 * Real.pi ^ 2 / 32)) * reg.buffer) := by
      have h1 := hPQ Qx (le_max_left _ _)
      calc peFactor η ^ Qx * Real.exp (-(3 * Real.pi ^ 2 / 32) * reg.buffer)
          ≤ peFactor η ^ (max Qx Q₁) * Real.exp (-(min c₁ (3 * Real.pi ^ 2 / 32)) * reg.buffer) :=
            mul_le_mul h1 he2 (Real.exp_pos _).le (by positivity)
        _ = 1 * (peFactor η ^ (max Qx Q₁) *
              Real.exp (-(min c₁ (3 * Real.pi ^ 2 / 32)) * reg.buffer)) := by ring
        _ ≤ (1 + (reg.joins : ℝ)) * (peFactor η ^ (max Qx Q₁) *
              Real.exp (-(min c₁ (3 * Real.pi ^ 2 / 32)) * reg.buffer)) :=
            mul_le_mul_of_nonneg_right hA (by positivity)
        _ = _ := by ring
    calc 9 * C₁ * (max Cx 1 * peFactor η ^ Qx) * Real.exp (-(3 * Real.pi ^ 2 / 32) * reg.buffer)
        = (9 * C₁ * max Cx 1) * (peFactor η ^ Qx *
            Real.exp (-(3 * Real.pi ^ 2 / 32) * reg.buffer)) := by ring
      _ ≤ (|Cb₁| + 9 * C₁ * max Cx 1 + 2) * ((1 + (reg.joins : ℝ)) * peFactor η ^ (max Qx Q₁) *
            Real.exp (-(min c₁ (3 * Real.pi ^ 2 / 32)) * reg.buffer)) :=
          mul_le_mul h9 hy (by positivity) (by linarith)
      _ = _ := by ring
  -- the curve data
  have hfτ : ∀ τ, s ≤ τ → τ ≤ t →
      cellComplexPair (cellRawTrace (fibreSeriesJet pkg.actual.r ξ) τ + cellConstantCLM 1)
        (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u (-τ))) = 0 := by
    intro τ hsτ hτt
    rw [revCurve_pairing H.hη0 H.hη H.hCg H.hCw H.hG H.hv H.hm H.hw pkg.actual ξ H.hξ V hb' hu τ
      ⟨hsτ, hτt⟩, hfast, mul_zero]
  have hsub : ∀ σ τ, s ≤ σ → τ ≤ t → IsRevCurve H V hb' (-τ) (-σ) u slice := fun σ τ hσ hτ =>
    CellWeakHilbertCurve.mono hu (Icc_subset_Icc (neg_le_neg hτ) (neg_le_neg hσ))
  have hvj' : ∀ (l : ℕ) t z, ‖iteratedFDeriv ℝ l (fun z' => Real.sqrt η • v t z') z‖ ≤
      max (K.Cvj l) 0 := fun l t z => le_trans (hvj l t z) (le_max_left _ _)
  have hξρ' : fibreNorm ξ ≤ max ρ 0 := le_trans hξρ (le_max_left _ _)
  let Reach : ℝ → ℝ → Prop := fun τ ε => ∃ w : TorusHk j ℂ, torusHkValueCLM w = u (-τ) ∧
    ‖w‖ ≤ ε * Real.exp (-(Real.pi ^ 2 / 8) * (t - τ)) * ‖w₀‖
  have hd : SharpLoopData reg s t Reach (max Cx 1 * peFactor η ^ Qx) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rintro τ ε ε' hle ⟨w, hw, hn⟩
      exact ⟨w, hw, le_trans hn (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le) (norm_nonneg _))⟩
    · rintro σ τ ε hsσ hστ hτt hq ⟨w, hw, hn⟩
      have hquiet : ∀ x ∈ Icc σ τ, ∀ z, v x z = 0 := fun x hx z =>
        pkg.quiet_zero x ⟨hq hx, by constructor <;> linarith [hx.1, hx.2]⟩ z
      obtain ⟨w', hw', hn'⟩ := sharpQuiet_decay hQ H pkg.actual j hστ V hb' hquiet
        (hsub σ τ hsσ hτt) (hfτ τ (le_trans hsσ hστ) hτt) w hw
      refine ⟨w', hw', ?_⟩
      calc ‖w'‖ ≤ 3 * Real.exp (-(Real.pi ^ 2 / 2) * (τ - σ)) * ‖w‖ := hn'
        _ ≤ 3 * Real.exp (-(Real.pi ^ 2 / 2) * (τ - σ)) *
            (ε * Real.exp (-(Real.pi ^ 2 / 8) * (t - τ)) * ‖w₀‖) :=
          mul_le_mul_of_nonneg_left hn (by positivity)
        _ = 3 * ε * (Real.exp (-(Real.pi ^ 2 / 2) * (τ - σ)) *
              Real.exp (-(Real.pi ^ 2 / 8) * (t - τ))) * ‖w₀‖ := by ring
        _ = _ := by rw [sharpAsm_exp_quiet]; ring
    · rintro σ τ ε hsσ hστ hτt ⟨w, hw, hn⟩
      obtain ⟨w', hw', hn'⟩ := hcr η G v ξ H pkg.actual hη hξρ' hvs hvj' V hb' hστ u slice
        (hsub σ τ hsσ hτt) (hfτ τ (le_trans hsσ hστ) hτt) w hw
      refine ⟨w', hw', ?_⟩
      have hEx := sharpAsm_exp_crude τ σ t
      have hE0 := Real.exp_pos (-(Real.pi ^ 2 / 8) * (τ - σ))
      have hE1 := Real.exp_pos (-(Real.pi ^ 2 / 8) * (t - τ))
      have hPQ0 : 0 ≤ peFactor η ^ Qx := by positivity
      calc ‖w'‖ ≤ Cx * peFactor η ^ Qx * Real.exp (-(Real.pi ^ 2 / 8) * (τ - σ)) * ‖w‖ := hn'
        _ ≤ max Cx 1 * peFactor η ^ Qx * Real.exp (-(Real.pi ^ 2 / 8) * (τ - σ)) * ‖w‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCxle hPQ0) hE0.le) (norm_nonneg _)
        _ ≤ max Cx 1 * peFactor η ^ Qx * Real.exp (-(Real.pi ^ 2 / 8) * (τ - σ)) *
            (ε * Real.exp (-(Real.pi ^ 2 / 8) * (t - τ)) * ‖w₀‖) :=
          mul_le_mul_of_nonneg_left hn (by positivity)
        _ = max Cx 1 * peFactor η ^ Qx * ε * (Real.exp (-(Real.pi ^ 2 / 8) * (τ - σ)) *
              Real.exp (-(Real.pi ^ 2 / 8) * (t - τ))) * ‖w₀‖ := by ring
        _ = _ := by rw [hEx]
    · intro x hx
      rcases pkg.cover x ⟨le_trans ht0 hx.1, le_trans hx.2 htS⟩ with h | h
      · exact Or.inl h
      · exact Or.inr h
    · exact fun p => (pkg.buffer_quiet p).1
    · exact fun p => (pkg.buffer_quiet p).2
  have hBx : 1 ≤ max Cx 1 * peFactor η ^ Qx := by
    have : 1 ≤ peFactor η ^ Qx := one_le_pow₀ hP1
    nlinarith
  have h0 : Reach t 1 := ⟨w₀, hw₀, by simp⟩
  have key := sharpStart hd hD hBx (a := Real.exp (-(3 * Real.pi ^ 2 / 32) * reg.buffer))
    (C₁ := C₁) (fun x hx => sharpAsm_ha reg.buffer x hx) hC₁ hnum hst h0 ?_
  · exact key
  · intro p hlo hhi hlh hmin σ hsσ hlo' hσhi hσt
    obtain ⟨w, hw, hn⟩ := hWC η t₀ S ϖ G v g reg pkg hη hvs hvj hg0 hg1 hmet ξ H hξρ
      hWreg V hb' (s := σ) (t := t) (le_trans ht0 hsσ) hσt htS p hlo hhi hlo' hσhi hlh u slice
      (hsub σ t hsσ le_rfl) hfast (htrans p ⟨⟨hlo, hhi⟩, hlh, fun p' hlt hlh' hmem => hmin p' hlt hlh' hmem⟩)
      w₀ hw₀
    exact ⟨w, hw, hn⟩

/-! # The stage representation of the tested sources

At a time `r` where the stage expansion holds, the sum of the sources of a stage `k`
against tests `z_i` (with classical representatives `ψ̃_i`) is a sum of pairings of the earlier
stage values with test families (`b1w_stage_representation`):
`∑_{i ∈ k} ⟨S_i, F_i; z_i⟩ = ∑_{k' < k} ∑_{i' ∈ k'} ⟨W_{i'}, Φ_{i'}⟩`, where `Φ_{i'}` is the `L²`
class of `∑_i (c_i/c_{i'}) conj T_{i,i'}(conj ψ̃_i)` (provided, with its bound, by the transform
families). The steps: the tested source (`cellComplexSource_eq_testedSource`), the expansion, the
stage values
`W_{i'} = c_{i'} Stage_{i'}`, and the real scale ratio. A zero scale `c_{i'}` forces `c_i = 0` or
`T = 0` (`b1wScale_eq_zero_of_le`, `b1wTestTransform_zero_of_level`). Only earlier stages
contribute (`StageTransformEarlierStatement`). -/

section
universe u v

/-- Reindex a sum over the stages that vanishes from stage `k` on. -/
theorem sum_eq_sum_stages {I : Type*} [Fintype I] (st : I → ℕ) (k : ℕ) (f : I → ℂ)
    (hf : ∀ i, ¬ st i < k → f i = 0) :
    ∑ i, f i = ∑ k' ∈ Finset.range k, ∑ i ∈ stageSet st k', f i := by
  classical
  rw [← Finset.sum_filter_of_ne (p := fun i => st i < k) fun i _ hi => by
    by_contra hc
    exact hi (hf i hc)]
  rw [← Finset.sum_fiberwise_of_maps_to (g := st) (t := Finset.range k)
    fun i hi => Finset.mem_range.2 (Finset.mem_filter.1 hi).2]
  refine Finset.sum_congr rfl fun k' hk' => Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [stageSet, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    exact ⟨h ▸ Finset.mem_range.1 hk', h⟩

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- The scale ratios are real. -/
theorem b1wScaleRatio_star (π : ι → ℝ) (ϖ ηg : ℝ) (letters : Fin Nw → CycleLetter ι h D)
    (i i' : B1WIndex ι h Nw m Ks) :
    star (b1wScaleRatio π ϖ ηg letters i i') = b1wScaleRatio π ϖ ηg letters i i' := by
  unfold b1wScaleRatio b1wScale
  simp only [star_div₀, Complex.star_def, Complex.conj_ofReal]

/-- **The stage representation of the tested sources** at a time `r`. -/
theorem b1w_stage_representation {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (r : ℝ)
    (k : ℕ) (hπ : ∀ x, 0 < F.π x) (hϖ : 0 < F.ϖ)
    (W S : B1WIndex ι h Nw m Ks → ComplexCellL2)
    (Fl : B1WIndex ι h Nw m Ks → Fin 2 → ComplexCellL2)
    (z : B1WIndex ι h Nw m Ks → TorusHk 1 ℂ) (ψ : B1WIndex ι h Nw m Ks → Vec 2 → ℂ)
    (hψ : ∀ i ∈ stageSet b1wSt k, ContDiff ℝ 1 (ψ i))
    (hzψ : ∀ i ∈ stageSet b1wSt k, (torusHkValueCLM (z i) : Vec 2 → ℂ)
      =ᵐ[volume.restrict AVenhance.unitCube] ψ i)
    (hS : ∀ i ∈ stageSet b1wSt k, (S i : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun y => b1wScale F.π F.ϖ F.ηg F.letters i *
        amplitudeIdLiteralSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r y)
    (hF : ∀ i ∈ stageSet b1wSt k, ∀ j, (Fl i j : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun y => b1wScale F.π F.ϖ F.ηg F.letters i *
        amplitudeIdLiteralFlux F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r y j)
    (hExp : ∀ i ∈ stageSet b1wSt k,
      b1wTestedSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r (fun y => star (ψ i y)) =
        ∑ i' : B1WIndex ι h Nw m Ks, ∫ y in AVenhance.unitCube,
          b1wStageVal F θ i' r y * b1wTestTransform F θ i i' r (fun y => star (ψ i y)) y)
    (hearly : ∀ i ∈ stageSet b1wSt k, ∀ i', ¬ b1wSt i' < k →
      b1wTestTransform F θ i i' r (fun y => star (ψ i y)) = 0)
    (hW : ∀ i', (W i' : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun y => b1wScale F.π F.ϖ F.ηg F.letters i' * b1wStageVal F θ i' r y)
    (hint : ∀ i ∈ stageSet b1wSt k, ∀ i', b1wSt i' < k →
      Integrable (fun y => b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' * (W i' y *
        b1wTestTransform F θ i i' r (fun y => star (ψ i y)) y))
        (volume.restrict AVenhance.unitCube))
    (Φ : B1WIndex ι h Nw m Ks → ComplexCellL2)
    (hΦ : ∀ i', b1wSt i' < k → (Φ i' : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun y => ∑ i ∈ stageSet b1wSt k, b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
        star (b1wTestTransform F θ i i' r (fun y => star (ψ i y)) y)) :
    ∑ i ∈ stageSet b1wSt k, cellComplexSource (fun j => ((θ j : ℝ) : ℂ)) (S i) (Fl i) (z i) =
      ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet b1wSt k', cellComplexPair (W i') (Φ i') := by
  set c := b1wScale F.π F.ϖ F.ηg F.letters (Nw := Nw) (m := m) (Ks := Ks) with hc
  set T := fun (i i' : B1WIndex ι h Nw m Ks) => b1wTestTransform F θ i i' r
    (fun y => star (ψ i y)) with hT
  -- the ratio form of each term
  have hterm : ∀ i i', c i * ∫ y in AVenhance.unitCube, b1wStageVal F θ i' r y * T i i' y =
      b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
        ∫ y in AVenhance.unitCube, W i' y * T i i' y := by
    intro i i'
    have hWT : (∫ y in AVenhance.unitCube, W i' y * T i i' y) =
        c i' * ∫ y in AVenhance.unitCube, b1wStageVal F θ i' r y * T i i' y := by
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [hW i'] with y hy
      rw [hy]
      ring
    rw [hWT]
    unfold b1wScaleRatio
    by_cases hci : c i' = 0
    · by_cases hl : i'.1 ≤ i.1
      · have h0 : c i = 0 := b1wScale_eq_zero_of_le F.π F.ηg F.letters hπ hϖ i i' hl hci
        rw [← hc, h0, hci]
        simp
      · push Not at hl
        have hT0 : T i i' = 0 := b1wTestTransform_zero_of_level F θ i i' (ne_of_gt hl)
          (fun l hl' => by
            have h1 := hl'.1
            have h2 := hl'.2
            have : i'.1 < i.1 := by
              rw [h1, h2]
              exact Fin.castSucc_lt_succ
            exact absurd hl (not_lt.2 this.le)) r _
        rw [hT0]
        simp
    · rw [← hc]
      field_simp
  -- each source is its expansion, in ratio form
  have hsrc : ∀ i ∈ stageSet b1wSt k,
      cellComplexSource (fun j => ((θ j : ℝ) : ℂ)) (S i) (Fl i) (z i) =
        ∑ i' : B1WIndex ι h Nw m Ks, b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
          ∫ y in AVenhance.unitCube, W i' y * T i i' y := by
    intro i hi
    rw [cellComplexSource_eq_testedSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r (c i) (S i) (Fl i)
      (hS i hi) (hF i hi) (z i) (ψ i) (hψ i hi) (hzψ i hi), hExp i hi, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i' _ => hterm i i'
  rw [Finset.sum_congr rfl hsrc, Finset.sum_comm]
  -- the scale ratios are real
  have hreal : ∀ i i', star (b1wScaleRatio F.π F.ϖ F.ηg F.letters i i') =
      b1wScaleRatio F.π F.ϖ F.ηg F.letters (Nw := Nw) (m := m) (Ks := Ks) i i' :=
    b1wScaleRatio_star F.π F.ϖ F.ηg F.letters
  -- the pairing with the families
  have hpair : ∀ i', b1wSt i' < k → (∑ i ∈ stageSet b1wSt k,
      b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' * ∫ y in AVenhance.unitCube, W i' y * T i i' y) =
      cellComplexPair (W i') (Φ i') := by
    intro i' hi'
    unfold cellComplexPair
    have hsum : (∑ i ∈ stageSet b1wSt k, b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' *
        ∫ y in AVenhance.unitCube, W i' y * T i i' y) =
        ∫ y in AVenhance.unitCube, ∑ i ∈ stageSet b1wSt k,
          b1wScaleRatio F.π F.ϖ F.ηg F.letters i i' * (W i' y * T i i' y) := by
      rw [integral_finsetSum _ fun i hi => hint i hi i' hi']
      exact Finset.sum_congr rfl fun i _ => (integral_const_mul _ _).symm
    rw [hsum]
    refine integral_congr_ae ?_
    filter_upwards [hΦ i' hi'] with y hy
    rw [hy, star_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [star_mul', star_star, hreal i i']
    ring
  rw [sum_eq_sum_stages b1wSt k _ fun i' hi' => ?_]
  · refine Finset.sum_congr rfl fun k' hk' => Finset.sum_congr rfl fun i' hi' => ?_
    have hst : b1wSt i' < k := (Finset.mem_filter.1 hi').2 ▸ Finset.mem_range.1 hk'
    exact hpair i' hst
  · refine Finset.sum_eq_zero fun i hi => ?_
    rw [hT]
    simp only
    rw [hearly i hi i' hi']
    simp

end Frame
end

end AVRegularity.CycleWords.Assembly
end
