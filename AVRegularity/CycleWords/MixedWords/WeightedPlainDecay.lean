-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.B1WRepresentation
import AVRegularity.CycleWords.MixedWords.StageExpansionLetter
import AVRegularity.CycleWords.MixedWords.WeightedPlainDecayKappa
public import AVRegularity.CycleWords.MixedWords.CompactChainExistence
import AVRegularity.CycleWords.MixedWords.BlochContinuity
import AVRegularity.CycleWords.MixedWords.AdjointExists
import AVRegularity.CycleWords.MixedWords.FactorOfMomentsRepresentation
import AVRegularity.CycleWords.MixedWords.AmplitudePlancherel
import AVRegularity.CycleWords.MixedWords.AfwCrude
import AVRegularity.CycleWords.FibreGraphNativeSeries
import Mathlib.Analysis.Real.Pi.Bounds

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # Weighted plain decay: the surplus decay

`surplusDecay`: the quiet lemma on `[τ(t) + 1/2, t]`, then the crude decay; the half unit lost
is the constant `e^{3π²/16}`. -/

/-- The drift vanishes after the last activity. -/
theorem wpd_quiet_of_lag (v : ℝ → Vec 2 → Vec 2) {t₀ σ t : ℝ} (hσ : t₀ ≤ σ)
    (h : (activeSet v t₀ t).Nonempty → lastActive v t₀ t < σ) :
    ∀ r ∈ Icc σ t, ∀ x, v r x = 0 := by
  intro r hr x
  by_contra hx
  have hmem : r ∈ activeSet v t₀ t := ⟨⟨hσ.trans hr.1, hr.2⟩, ⟨x, hx⟩⟩
  have h1 := h ⟨r, hmem⟩
  have h2 : r ≤ lastActive v t₀ t := le_csSup ⟨t, fun y hy => hy.1.2⟩ hmem
  linarith [hr.1]

/-- The last activity is after `t₀`. -/
theorem wpd_t0_le_lastActive (v : ℝ → Vec 2 → Vec 2) {t₀ t : ℝ}
    (h : (activeSet v t₀ t).Nonempty) : t₀ ≤ lastActive v t₀ t := by
  obtain ⟨x, hx⟩ := h
  exact hx.1.1.trans (le_csSup ⟨t, fun y hy => hy.1.2⟩ hx)

/-- The exponent arithmetic of the surplus. -/
theorem wpd_surplus_arith (s σ t lag : ℝ) (h : lag - 1 / 2 ≤ t - σ) :
    Real.exp (-(Real.pi ^ 2 / 2) * (t - σ)) * Real.exp (-(Real.pi ^ 2 / 8) * (σ - s)) ≤
      Real.exp (3 * Real.pi ^ 2 / 8 / 2) * Real.exp (-(3 * Real.pi ^ 2 / 8) * lag) *
        Real.exp (-(Real.pi ^ 2 / 8) * (t - s)) := by
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.2
  have hc : 0 ≤ 3 * Real.pi ^ 2 / 8 := by positivity
  nlinarith [mul_nonneg hc (sub_nonneg.2 h)]

/-- `P_e ≥ 1`. -/
theorem wpd_one_le_pe (η : ℝ) : 1 ≤ peFactor η := by
  unfold peFactor
  have : 0 ≤ (Real.sqrt η)⁻¹ := inv_nonneg.2 (Real.sqrt_nonneg _)
  linarith

/-- **The surplus decay.** -/
theorem surplusDecay (hQ : QuietHsDecayStatement) : SurplusDecayStatement := by
  intro K j ρ _ _
  obtain ⟨Cq, Q, hCq, hq⟩ := wpd_quiet_crude hQ K j ρ
  have hE : 1 ≤ Real.exp (3 * Real.pi ^ 2 / 8 / 2) := Real.one_le_exp (by positivity)
  refine ⟨Cq * Real.exp (3 * Real.pi ^ 2 / 8 / 2), Q, by nlinarith, ?_⟩
  intro η t₀ S ϖ G v g reg pkg hη hvs hvj _ _ _ ξ H hξ V hb' s t hs hst _ u slice hu hfast w₀ hw₀
  have hP := wpd_one_le_pe η
  have fin : ∀ σ lag : ℝ, s ≤ σ → σ ≤ t → (σ < t → ∀ r ∈ Icc σ t, ∀ x, v r x = 0) →
      lag - 1 / 2 ≤ t - σ → quietLag v t₀ s t = lag →
      ∃ w : TorusHk j ℂ, torusHkValueCLM w = u (-s) ∧
        ‖w‖ ≤ Cq * Real.exp (3 * Real.pi ^ 2 / 8 / 2) * peFactor η ^ Q *
          Real.exp (-(3 * Real.pi ^ 2 / 8) * quietLag v t₀ s t) *
          Real.exp (-(Real.pi ^ 2 / 8) * (t - s)) * ‖w₀‖ := by
    intro σ lag hsσ hσt hquiet hlag hl
    obtain ⟨w, hw, hn⟩ := hq η G v ξ H pkg.actual hη hξ hvs hvj V hb' hsσ hσt hquiet u slice hu
      hfast w₀ hw₀
    refine ⟨w, hw, hn.trans ?_⟩
    rw [hl]
    have hpos : 0 ≤ Cq * peFactor η ^ Q * ‖w₀‖ := by
      have : 0 ≤ peFactor η ^ Q := pow_nonneg (by linarith) Q
      positivity
    calc Cq * peFactor η ^ Q * Real.exp (-(Real.pi ^ 2 / 2) * (t - σ)) *
          Real.exp (-(Real.pi ^ 2 / 8) * (σ - s)) * ‖w₀‖
        = (Cq * peFactor η ^ Q * ‖w₀‖) * (Real.exp (-(Real.pi ^ 2 / 2) * (t - σ)) *
          Real.exp (-(Real.pi ^ 2 / 8) * (σ - s))) := by ring
      _ ≤ (Cq * peFactor η ^ Q * ‖w₀‖) * (Real.exp (3 * Real.pi ^ 2 / 8 / 2) *
          Real.exp (-(3 * Real.pi ^ 2 / 8) * lag) * Real.exp (-(Real.pi ^ 2 / 8) * (t - s))) :=
        mul_le_mul_of_nonneg_left (wpd_surplus_arith s σ t lag hlag) hpos
      _ = _ := by ring
  by_cases hne : (activeSet v t₀ t).Nonempty
  · have hτ0 := wpd_t0_le_lastActive v hne
    by_cases hsτ : s ≤ lastActive v t₀ t
    · have hlag : quietLag v t₀ s t = t - lastActive v t₀ t := by
        simp only [quietLag, hne, ↓reduceIte]
        exact min_eq_right (by linarith)
      by_cases hτt : lastActive v t₀ t + 1 / 2 ≤ t
      · exact fin (lastActive v t₀ t + 1 / 2) (t - lastActive v t₀ t) (by linarith) hτt
          (fun _ => wpd_quiet_of_lag (t₀ := t₀) (t := t) v (by linarith) (fun _ => by linarith)) (by linarith) hlag
      · exact fin t (t - lastActive v t₀ t) hst le_rfl (fun h => absurd h (lt_irrefl _))
          (by linarith) hlag
    · push Not at hsτ
      have hlag : quietLag v t₀ s t = t - s := by
        simp only [quietLag, hne, ↓reduceIte]
        exact min_eq_left (by linarith)
      exact fin s (t - s) le_rfl hst (fun _ => wpd_quiet_of_lag (t₀ := t₀) (t := t) v hs (fun _ => hsτ))
        (by linarith) hlag
  · have hlag : quietLag v t₀ s t = t - s := by simp only [quietLag, hne, ↓reduceIte]
    exact fin s (t - s) le_rfl hst (fun _ => wpd_quiet_of_lag (t₀ := t₀) (t := t) v hs (fun h => absurd h hne))
      (by linarith) hlag

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleWords.Assembly

/-! # Weighted plain decay: the exponent and constant arithmetic

The regime of the weighted statement implies the regime of the sharp fast decay and the smallness
`Λ₁ e^{-(3π²/8) D/2} ≤ 1` that produces a least window; the weight bounds the surplus. -/

/-- The regime of the weighted statement gives the regime of the sharp fast decay and `Λ e^{-c D/2} ≤ 1`. -/
theorem wpd_regime (Cb25 c25 Λ Pq D J : ℝ) (hPq : 1 ≤ Pq) (hΛ : 1 ≤ Λ)
    (hD : 0 ≤ D) (hJ : 0 ≤ J)
    (h : max Cb25 1 * Λ * (1 + J) * Pq * Real.exp (-min c25 (3 * Real.pi ^ 2 / 16) * D) ≤ 1) :
    Cb25 * (1 + J) * Pq * Real.exp (-c25 * D) ≤ 1 ∧
      Λ * Real.exp (-(3 * Real.pi ^ 2 / 8) * (D / 2)) ≤ 1 := by
  have hm1 : min c25 (3 * Real.pi ^ 2 / 16) ≤ c25 := min_le_left _ _
  have hm2 : min c25 (3 * Real.pi ^ 2 / 16) ≤ 3 * Real.pi ^ 2 / 16 := min_le_right _ _
  have he1 : Real.exp (-c25 * D) ≤ Real.exp (-min c25 (3 * Real.pi ^ 2 / 16) * D) :=
    Real.exp_le_exp.2 (by nlinarith)
  have he2 : Real.exp (-(3 * Real.pi ^ 2 / 8) * (D / 2)) ≤
      Real.exp (-min c25 (3 * Real.pi ^ 2 / 16) * D) :=
    Real.exp_le_exp.2 (by nlinarith)
  have hE := Real.exp_pos (-min c25 (3 * Real.pi ^ 2 / 16) * D)
  have hE2 := Real.exp_pos (-(3 * Real.pi ^ 2 / 8) * (D / 2))
  have hmax1 : Cb25 ≤ max Cb25 1 := le_max_left _ _
  have hmax2 : 1 ≤ max Cb25 1 := le_max_right _ _
  have hJ1 : 1 ≤ 1 + J := by linarith
  have hE0 := hE.le
  constructor
  · by_cases hCb : 0 ≤ Cb25
    swap
    · push Not at hCb
      have h1 : 0 ≤ (1 + J) * Pq * Real.exp (-c25 * D) := by positivity
      nlinarith [mul_nonneg h1 (neg_nonneg.2 hCb.le)]
    calc Cb25 * (1 + J) * Pq * Real.exp (-c25 * D)
        ≤ max Cb25 1 * Λ * (1 + J) * Pq * Real.exp (-min c25 (3 * Real.pi ^ 2 / 16) * D) := by
          have h0 : 0 ≤ Cb25 * (1 + J) * Pq := by positivity
          calc Cb25 * (1 + J) * Pq * Real.exp (-c25 * D)
              ≤ Cb25 * (1 + J) * Pq * Real.exp (-min c25 (3 * Real.pi ^ 2 / 16) * D) :=
                mul_le_mul_of_nonneg_left he1 h0
            _ ≤ max Cb25 1 * Λ * (1 + J) * Pq *
                Real.exp (-min c25 (3 * Real.pi ^ 2 / 16) * D) := by
                apply mul_le_mul_of_nonneg_right _ hE0
                have : Cb25 ≤ max Cb25 1 * Λ := by nlinarith
                have hpos : 0 ≤ (1 + J) * Pq := by positivity
                nlinarith
      _ ≤ 1 := h
  · calc Λ * Real.exp (-(3 * Real.pi ^ 2 / 8) * (D / 2))
        ≤ max Cb25 1 * Λ * (1 + J) * Pq * Real.exp (-min c25 (3 * Real.pi ^ 2 / 16) * D) := by
          have hpos : 0 ≤ Λ := by linarith
          calc Λ * Real.exp (-(3 * Real.pi ^ 2 / 8) * (D / 2))
              ≤ Λ * Real.exp (-min c25 (3 * Real.pi ^ 2 / 16) * D) :=
                mul_le_mul_of_nonneg_left he2 hpos
            _ ≤ _ := by
                apply mul_le_mul_of_nonneg_right _ hE0
                have h1 : 1 ≤ max Cb25 1 * (1 + J) * Pq := by
                  have : 1 ≤ max Cb25 1 * (1 + J) := by nlinarith
                  nlinarith
                nlinarith
      _ ≤ 1 := h

/-- The final constant arithmetic of the split. -/
theorem wpd_combine (C25 Cs X W T N a b Pq Ee n : ℝ) (hC25 : 1 ≤ C25) (hCs : 1 ≤ Cs)
    (hX : 0 < X) (hW : 1 ≤ W) (hT : 0 ≤ T) (hN : 0 ≤ N)
    (hPE : Pq * Ee ≤ W) (hn : n ≤ 6 * N) (hn0 : 0 ≤ n)
    (hA : a ≤ C25 * X * (T + 5 * N)) (hB : b ≤ Cs * Pq * Ee * X * n) :
    a + b ≤ (3 + 5 * C25 + 6 * Cs) * X * (T + W * N) := by
  have h1 : C25 * X * (T + 5 * N) ≤ C25 * X * T + 5 * C25 * X * (W * N) := by
    have : 0 ≤ C25 * X * N * (W - 1) := by
      have : 0 ≤ C25 * X * N := by positivity
      exact mul_nonneg this (by linarith)
    nlinarith
  have h2 : Cs * Pq * Ee * X * n ≤ 6 * Cs * X * (W * N) := by
    have h3 : Cs * Pq * Ee * X * n = Cs * X * ((Pq * Ee) * n) := by ring
    rw [h3]
    have : (Pq * Ee) * n ≤ W * (6 * N) :=
      mul_le_mul hPE hn hn0 (by linarith)
    have hcs : 0 ≤ Cs * X := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this hcs]
  have h4 : 0 ≤ X * T := by positivity
  have h5 : 0 ≤ X * (W * N) := by positivity
  nlinarith [mul_nonneg h4 (by linarith : (0:ℝ) ≤ 3 + 5 * C25 + 6 * Cs - C25),
    mul_nonneg h5 (by linarith : (0:ℝ) ≤ 3 + 5 * C25 + 6 * Cs - (5 * C25 + 6 * Cs))]

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords
namespace AVRegularity.CycleWords.Assembly

/-! # The sharp slow test: tools for the quiet, defect and window steps

* mean and mean-free parts of `q = conj u(-r)` (`sharpSlowQ_mean_rep`, `sharpSlowQ_of_q0`);
* the growth of `E` at the slow rate `π²/16` (`sharpSlowQ_E_growth`);
* the quiet transfer of the mean-free part of `q` along a quiet stretch (`sharpSlowQ_q0_transfer`). -/

section
local notation "cjL" => cellFiberCLM Complex.conjCLE.toContinuousLinearMap

/-- The mean of the conjugate is the conjugate of the mean. -/
theorem sharpSlowQ_mean_conj (u : ComplexCellL2) :
    cellMeanCLM (cjL u) = star (cellMeanCLM u) := by
  rw [cellMeanCLM_apply, cellMeanCLM_apply, ← cellComplexPair_one, ← cellComplexPair_one]
  have h := cellComplexPair_conjugate u (cellConstantCLM 1)
  rw [cellFiberConj_constant, star_one] at h
  exact h

/-- The mean-free projection commutes with conjugation. -/
theorem sharpSlowQ_q0_conj (u : ComplexCellL2) : cellQ0CLM (cjL u) = cjL (cellQ0CLM u) := by
  unfold cellQ0CLM
  simp only [sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, map_sub, sharpSlowQ_mean_conj, cellFiberConj_constant]

/-- The constant `‖1‖ + ‖I‖` of `TorusHk j ℂ`. -/
def sharpSlowQKappa (j : ℕ) : ℝ := ‖torusHigherConstant j 1‖ + ‖torusHigherConstant j Complex.I‖

theorem sharpSlowQKappa_nonneg (j : ℕ) : 0 ≤ sharpSlowQKappa j := by
  unfold sharpSlowQKappa; positivity

/-- The mean-part constant `κ C_g (1 + M ρ)`. -/
def sharpSlowQMeanConst (K : ScalarConstants) (j : ℕ) (ρ : ℝ) : ℝ :=
  sharpSlowQKappa j * (K.Cg * (1 + rowConst K (4 * (ρ + K.Cw)) ρ * ρ))

variable {K : ScalarConstants} {ρ : ℝ} {η : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {v : ℝ → Vec 2 → Vec 2} {ξ : Fin 2 → ℂ}

/-- The mean part of `q - star E·1` has an `H^j` representative of size `O(|ξ|)|E|`. -/
theorem sharpSlowQ_mean_rep (s : SharpSlowSetting K ρ) {r : ℝ} (hr : r ∈ Icc s.a s.b) (j : ℕ) :
    ∃ w : TorusHk j ℂ, torusHkValueCLM w =
        cellConstantCLM (cellMeanCLM (s.q r) - star (s.E r)) ∧
      ‖w‖ ≤ sharpSlowQMeanConst K j ρ * fibreNorm s.ξ * ‖s.E r‖ := by
  refine ⟨torusHigherConstant j (cellMeanCLM (s.q r) - star (s.E r)),
    torusHigherConstant_value _ _, ?_⟩
  have hpair : cellComplexPair (cellConstantCLM 1) (s.q r) = star (cellMeanCLM (s.q r)) := by
    rw [cellComplexPair_symm, cellComplexPair_one, cellMeanCLM_apply]
  have hm := sharpSlow_mean s hr
  rw [hpair] at hm
  have hc : ‖cellMeanCLM (s.q r) - star (s.E r)‖ ≤
      K.Cg * (1 + rowConst K (4 * (ρ + K.Cw)) ρ * ρ) * fibreNorm s.ξ * ‖s.E r‖ := by
    rw [← norm_star, star_sub, star_star]
    exact hm
  have hk := sharpSlow_const_norm j (cellMeanCLM (s.q r) - star (s.E r))
  have hk0 := sharpSlowQKappa_nonneg j
  calc _ ≤ sharpSlowQKappa j * ‖cellMeanCLM (s.q r) - star (s.E r)‖ := hk
    _ ≤ sharpSlowQKappa j * (K.Cg * (1 + rowConst K (4 * (ρ + K.Cw)) ρ * ρ) * fibreNorm s.ξ *
        ‖s.E r‖) := mul_le_mul_of_nonneg_left hc hk0
    _ = _ := by unfold sharpSlowQMeanConst; ring

/-- From a representative of the mean-free part of `q(r)` to clause 1 at `r`. -/
theorem sharpSlowQ_of_q0 (s : SharpSlowSetting K ρ) {r : ℝ} (hr : r ∈ Icc s.a s.b) (j : ℕ)
    (w : TorusHk j ℂ) (hw : torusHkValueCLM w = cellQ0CLM (s.q r)) {B : ℝ}
    (hB : ‖w‖ ≤ B * ‖s.E r‖) :
    s.SlowBound j (sharpSlowQMeanConst K j ρ * fibreNorm s.ξ + B) r := by
  obtain ⟨wm, hwm, hnm⟩ := sharpSlowQ_mean_rep s hr j
  refine ⟨w + wm, ?_, ?_⟩
  · rw [map_add, hw, hwm]
    unfold cellQ0CLM
    simp only [sub_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.comp_apply, map_sub]
    abel
  · calc ‖w + wm‖ ≤ ‖w‖ + ‖wm‖ := norm_add_le _ _
      _ ≤ _ := by nlinarith

/-- `E` grows at most at the slow rate `π²/16` going forward. -/
theorem sharpSlowQ_E_growth (s : SharpSlowSetting K ρ) {r τ : ℝ} (hrτ : r ≤ τ) (hτ : τ ≤ s.b) :
    ‖s.E τ‖ ≤ Real.exp (Real.pi ^ 2 / 16 * (τ - r)) * ‖s.E r‖ := by
  have hint : ∀ c d, c ≤ d →
      IntervalIntegrable (fun τ => fibreSeriesC s.pkg.actual.lam s.ξ τ) volume c d :=
    fun c d h => (intervalIntegrable_iff_integrableOn_Icc_of_le h).mpr
      ((fibreGraph_symbol_memLp_top s.pkg.actual.graph s.H.hη0 s.H.hη s.H.hCw s.H.hG s.H.hv
        s.H.hw s.ξ s.H.hξ s.H.hCg c d).integrable le_top)
  have hsplit : s.E r = Complex.exp (∫ t in r..τ, fibreSeriesC s.pkg.actual.lam s.ξ t) *
      s.E τ := by
    unfold SharpSlowSetting.E
    rw [← Complex.exp_add, ← intervalIntegral.integral_add_adjacent_intervals (hint r τ hrτ)
      (hint τ s.b hτ)]
  have hlow := graphPhase_norm_lower s.H.hη0 s.H.hη s.H.hCg s.H.hCw s.H.hG s.H.hv s.H.hw
    s.pkg.actual s.ξ s.H.hreal s.H.hξ hrτ
  have hrate : Real.exp (-(Real.pi ^ 2 / 16) * (τ - r)) ≤
      ‖Complex.exp (∫ t in r..τ, fibreSeriesC s.pkg.actual.lam s.ξ t)‖ := by
    refine le_trans (Real.exp_le_exp.mpr ?_) hlow
    have := mul_le_mul_of_nonneg_right s.H.hsep (sub_nonneg.2 hrτ)
    nlinarith
  have h1 : Real.exp (-(Real.pi ^ 2 / 16) * (τ - r)) * ‖s.E τ‖ ≤ ‖s.E r‖ := by
    rw [hsplit, norm_mul]
    exact mul_le_mul_of_nonneg_right hrate (norm_nonneg _)
  have h2 : Real.exp (Real.pi ^ 2 / 16 * (τ - r)) * Real.exp (-(Real.pi ^ 2 / 16) * (τ - r)) = 1 := by
    rw [← Real.exp_add]; simp
  calc ‖s.E τ‖ = Real.exp (Real.pi ^ 2 / 16 * (τ - r)) *
        (Real.exp (-(Real.pi ^ 2 / 16) * (τ - r)) * ‖s.E τ‖) := by rw [← mul_assoc, h2, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le

/-- The shift of the reversed equation is admissible. -/
theorem sharpSlowQ_theta (H : TransverseLocalHyp K η G v ξ) :
    ∀ i, ((-((fun k => (Real.sqrt η : ℂ) * ξ k) i)).im = 0 ∧
      |(-((fun k => (Real.sqrt η : ℂ) * ξ k) i)).re| ≤ Real.pi) := by
  have hfn : fibreNorm ξ ≤ Real.pi := by
    have h := H.hsep
    have hp : 0 ≤ K.Cw * K.Cg := mul_nonneg H.hCw H.hCg
    have hn0 := fibreNorm_nonneg ξ
    nlinarith [Real.pi_pos, sq_nonneg (fibreNorm ξ - Real.pi), mul_nonneg hp (sq_nonneg (fibreNorm ξ))]
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

/-- **Quiet transfer.** Along a quiet stretch `[σ, τ] ⊆ [a, b]`, a representative of
`q(τ) - c·1` gives a representative of the mean-free part of `q(σ)`, smaller by `2e^{-π²(τ-σ)/2}`. -/
theorem sharpSlowQ_q0_transfer (hQ : QuietHsDecayStatement) (s : SharpSlowSetting K ρ) (j : ℕ)
    {σ τ : ℝ} (hσ : s.a ≤ σ) (hστ : σ ≤ τ) (hτ : τ ≤ s.b)
    (hquiet : ∀ t ∈ Icc σ τ, ∀ x, s.v t x = 0) (c : ℂ) (w₀ : TorusHk j ℂ)
    (hw₀ : torusHkValueCLM w₀ = s.q τ - cellConstantCLM c) :
    ∃ w : TorusHk j ℂ, torusHkValueCLM w = cellQ0CLM (s.q σ) ∧
      ‖w‖ ≤ 2 * Real.exp (-(Real.pi ^ 2 / 2) * (τ - σ)) * ‖w₀‖ := by
  obtain ⟨w₁, hw₁, hn₁⟩ := sharpMean_q0_rep j w₀
  have hconst : cellQ0CLM (cellConstantCLM c) = 0 := by
    unfold cellQ0CLM
    simp [cellMeanCLM_constant]
  have hq1 : torusHkValueCLM (torusHkConj w₁) = cellQ0CLM (s.u (-τ)) := by
    rw [torusHkConj_value, hw₁, hw₀, map_sub, hconst, sub_zero]
    unfold SharpSlowSetting.q
    rw [sharpSlowQ_q0_conj, cellFiberConj_involutive]
  obtain ⟨w₂, hw₂, hn₂⟩ := hQ ⟨fun s' _ => s.G (-s'), fun s' x => -s.v (-s') x,
      fun j => -((fun k => (Real.sqrt s.η : ℂ) * s.ξ k) j), 0⟩ (cellMetric_timeReverse s.H.hG) s.V
      (cellDrift_timeReverse s.H.hv).1 s.hb' (-τ) (-σ) s.u s.slice (by linarith)
      (fun t ht x => by
        have := hquiet (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩ x
        simp [this])
      (fun _ _ _ => rfl) (fun _ => rfl) (sharpSlowQ_theta s.H)
      (CellWeakHilbertCurve.mono s.hu (Icc_subset_Icc (by linarith) (by linarith))) j
      (torusHkConj w₁) hq1.symm.symm
  refine ⟨torusHkConj w₂, ?_, ?_⟩
  · rw [torusHkConj_value, hw₂]
    unfold SharpSlowSetting.q
    rw [sharpSlowQ_q0_conj]
  · rw [torusHkConj_norm]
    rw [torusHkConj_norm] at hn₂
    have hrate : -σ - -τ = τ - σ := by ring
    rw [hrate] at hn₂
    have hexp := Real.exp_pos (-(Real.pi ^ 2 / 2) * (τ - σ))
    calc ‖w₂‖ ≤ Real.exp (-(Real.pi ^ 2 / 2) * (τ - σ)) * ‖w₁‖ := hn₂
      _ ≤ Real.exp (-(Real.pi ^ 2 / 2) * (τ - σ)) * (2 * ‖w₀‖) := by gcongr
      _ = _ := by ring
end

/-! # The sharp slow test: the quiet (gap) step

For `r` in no extended window, `[r, min(r + D, b)]` is quiet by `cover`; the mean-free part of
`q(r)` is the `hQ` evolution of that of `q(min(r + D, b))`. -/

section
variable {K : ScalarConstants} {ρ : ℝ}

/-- `[r, τ]` is quiet when `r` is in no extended window and `τ ≤ r + D`. -/
theorem sharpSlowQ_quiet_stretch (s : SharpSlowSetting K ρ) {r τ : ℝ} (hr : r ∈ Icc s.a s.b)
    (hrτ : r ≤ τ) (hτ : τ ≤ s.b) (hD : τ ≤ r + s.reg.buffer) (hnw : ¬ InExtWindow s.reg r) :
    ∀ t ∈ Icc r τ, ∀ x, s.v t x = 0 := by
  intro t ht x
  have htS : t ∈ Icc s.t₀ (s.t₀ + s.S) :=
    ⟨le_trans s.ha (hr.1.trans ht.1), ht.2.trans (hτ.trans s.hbS)⟩
  rcases s.pkg.cover t htS with hq | ⟨p, hp⟩
  · exact s.pkg.quiet_zero t ⟨hq, htS⟩ x
  · exfalso
    apply hnw
    refine ⟨p, ?_, ?_⟩
    · linarith [hp.1, ht.2]
    · have := s.pkg.buffer_nonneg
      linarith [hp.2, ht.1]

/-- The mean-free part of `q(r)` for `r` in no extended window is small. -/
theorem sharpSlowQ_quiet_q0 (hQ : QuietHsDecayStatement) (s : SharpSlowSetting K ρ) (j : ℕ)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ r ∈ Icc s.a s.b, s.SlowBound j M r)
    (hD : 4 ≤ Real.exp s.reg.buffer) {r : ℝ} (hr : r ∈ Icc s.a s.b) (hnw : ¬ InExtWindow s.reg r) :
    ∃ w : TorusHk j ℂ, torusHkValueCLM w = cellQ0CLM (s.q r) ∧ ‖w‖ ≤ (M / 2) * ‖s.E r‖ := by
  have hD0 := s.pkg.buffer_nonneg
  by_cases hcase : r + s.reg.buffer ≤ s.b
  · have hτ : r + s.reg.buffer ∈ Icc s.a s.b := ⟨by linarith [hr.1], hcase⟩
    obtain ⟨w₀, hw₀, hn₀⟩ := hb _ hτ
    obtain ⟨w, hw, hn⟩ := sharpSlowQ_q0_transfer hQ s j hr.1 (by linarith) hcase
      (sharpSlowQ_quiet_stretch s hr (by linarith) hcase le_rfl hnw) _ w₀ hw₀
    refine ⟨w, hw, ?_⟩
    have hg := sharpSlowQ_E_growth s (r := r) (τ := r + s.reg.buffer) (by linarith) hcase
    have hpi : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    have hsub : r + s.reg.buffer - r = s.reg.buffer := by ring
    rw [hsub] at hn hg
    have hexp : Real.exp (-(Real.pi ^ 2 / 2) * s.reg.buffer) *
        Real.exp (Real.pi ^ 2 / 16 * s.reg.buffer) ≤ Real.exp (-s.reg.buffer) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith)
    have hinv : Real.exp (-s.reg.buffer) ≤ 1 / 4 := by
      rw [Real.exp_neg]
      calc (Real.exp s.reg.buffer)⁻¹ ≤ 4⁻¹ := inv_anti₀ (by norm_num) hD
        _ = 1 / 4 := by norm_num
    have hE0 := norm_nonneg (s.E r)
    have hE1 := norm_nonneg (s.E (r + s.reg.buffer))
    have hw0 := norm_nonneg w₀
    have hpos1 := Real.exp_pos (-(Real.pi ^ 2 / 2) * s.reg.buffer)
    calc ‖w‖ ≤ 2 * Real.exp (-(Real.pi ^ 2 / 2) * s.reg.buffer) * ‖w₀‖ := hn
      _ ≤ 2 * Real.exp (-(Real.pi ^ 2 / 2) * s.reg.buffer) *
          (M * ‖s.E (r + s.reg.buffer)‖) := by gcongr
      _ ≤ 2 * Real.exp (-(Real.pi ^ 2 / 2) * s.reg.buffer) *
          (M * (Real.exp (Real.pi ^ 2 / 16 * s.reg.buffer) * ‖s.E r‖)) := by gcongr
      _ = 2 * (Real.exp (-(Real.pi ^ 2 / 2) * s.reg.buffer) *
          Real.exp (Real.pi ^ 2 / 16 * s.reg.buffer)) * M * ‖s.E r‖ := by ring
      _ ≤ 2 * (1 / 4) * M * ‖s.E r‖ := by
          have := hexp.trans hinv
          gcongr
      _ = (M / 2) * ‖s.E r‖ := by ring
  · push Not at hcase
    have hb1 : s.b ∈ Icc s.a s.b := ⟨s.hab, le_rfl⟩
    have hqb : s.q s.b = cellConstantCLM 1 := by
      unfold SharpSlowSetting.q
      rw [s.hu1, cellFiberConj_constant, star_one]
    obtain ⟨w, hw, hn⟩ := sharpSlowQ_q0_transfer hQ s j hr.1 hr.2 le_rfl
      (sharpSlowQ_quiet_stretch s hr hr.2 le_rfl hcase.le hnw) 1 0
      (by rw [map_zero, hqb]; simp)
    refine ⟨w, hw, ?_⟩
    rw [norm_zero, mul_zero] at hn
    exact hn.trans (by positivity)

/-- The well-buffered regime `WB 4 1 0` gives `4 ≤ e^D`. -/
theorem sharpSlowQ_buffer_exp (s : SharpSlowSetting K ρ) (h : s.WB 4 1 0) :
    4 ≤ Real.exp s.reg.buffer := by
  unfold SharpSlowSetting.WB at h
  have hj : (0 : ℝ) ≤ (s.reg.joins : ℝ) := Nat.cast_nonneg _
  have he := Real.exp_pos (-1 * s.reg.buffer)
  have h1 : 4 * Real.exp (-1 * s.reg.buffer) ≤ 1 := by
    refine le_trans ?_ h
    rw [pow_zero]
    nlinarith
  have h2 : Real.exp s.reg.buffer * Real.exp (-1 * s.reg.buffer) = 1 := by
    rw [← Real.exp_add]; simp
  have h3 := Real.exp_pos s.reg.buffer
  nlinarith

/-- **The quiet step** (`SharpSlowQuietStepStatement`). -/
theorem sharpSlowQuietStep : SharpSlowQuietStepStatement := by
  intro hQ K j ρ hρ0 hρ1
  refine ⟨|sharpSlowQMeanConst K j ρ|, 4, 1, 0, abs_nonneg _, by norm_num, one_pos, ?_⟩
  intro s hs M hM hb r hr hnw
  obtain ⟨w, hw, hn⟩ := sharpSlowQ_quiet_q0 hQ s j hM hb (sharpSlowQ_buffer_exp s hs) hr hnw
  refine (sharpSlowQ_of_q0 s hr j w hw hn).mono ?_
  have := mul_le_mul_of_nonneg_right (le_abs_self (sharpSlowQMeanConst K j ρ))
    (fibreNorm_nonneg s.ξ)
  linarith
end

/-! # The sharp slow test: general reversed-curve tools

`L²` contraction of every reversed curve, and the crude `H^j` bound for a reversed curve from
arbitrary data. -/

section
variable {K : ScalarConstants} {η : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {v : ℝ → Vec 2 → Vec 2} {ξ : Fin 2 → ℂ}

/-- **Crude `H^s` bound of a reversed curve from arbitrary data** (`cellDriftRegularity`, price
`P_e^Q`): within a unit time of the datum, from an `H^s` representative of the datum; after
a unit time, from the `L²` size one unit earlier. -/
theorem sharpRev_crude_general (hR : CellDriftRegularityStatement) (s : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (J : ℕ → ℝ) (hJ : ∀ l, 0 ≤ J l) :
    ∃ (C : ℝ) (Q : ℕ), 0 ≤ C ∧
    ∀ (η : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (ξ : Fin 2 → ℂ)
      (H : TransverseLocalHyp K η G v ξ),
      0 < η → fibreNorm ξ ≤ ρ → (∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
      (∀ (l : ℕ) t z, ‖iteratedFDeriv ℝ l (fun z' => Real.sqrt η • v t z') z‖ ≤ J l) →
    ∀ (V : ℝ) (hb' : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2) {a b : ℝ}, a ≤ b →
    ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ), IsRevCurve H V hb' (-b) (-a) u slice →
    ∀ r ∈ Icc a b,
      (b - r ≤ 1 → ∀ w₀ : TorusHk s ℂ, torusHkValueCLM w₀ = u (-b) →
        ∃ w : TorusHk s ℂ, torusHkValueCLM w = u (-r) ∧ ‖w‖ ≤ C * peFactor η ^ Q * ‖w₀‖) ∧
      (1 ≤ b - r → ∃ w : TorusHk s ℂ, torusHkValueCLM w = u (-r) ∧
        ‖w‖ ≤ C * peFactor η ^ Q * ‖u (-r - 1)‖) := by
  obtain ⟨C₀, Q, hC₀, hreg⟩ := hR s ρ hρ
  set B := ∑ l ∈ Finset.range (s + 2), J l with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun l _ => hJ l
  refine ⟨C₀ * (1 + B) ^ Q, Q, by positivity, ?_⟩
  intro η G v ξ H hη hξρ hvs hvj V hb' a b hab u slice hu r hr
  have hs : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
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
  have hPQ : C₀ * (1 + L) ^ Q ≤ C₀ * (1 + B) ^ Q * peFactor η ^ Q := by
    calc C₀ * (1 + L) ^ Q ≤ C₀ * ((1 + B) ^ Q * peFactor η ^ Q) := by gcongr
      _ = _ := by ring
  refine ⟨fun h1 w₀ hw₀ => ?_, fun h1 => ?_⟩
  · obtain ⟨w, hwv, hwn⟩ := (hreg (-b) (-r) L (fun s => G (-s)) hGr hvr V hb' θ'
      (by linarith [hr.2]) hL0 hθρ (fun τ _ => hsmooth τ) (fun l τ hl _ x => hjet l τ hl x) u
      slice (hu' (-b) (-r) le_rfl (by linarith [hr.1]))).1 w₀ hw₀ (-r)
      ⟨by linarith [hr.2], le_rfl⟩ (by linarith)
    exact ⟨w, hwv, hwn.trans (mul_le_mul_of_nonneg_right hPQ (norm_nonneg _))⟩
  · obtain ⟨w, hwv, hwn⟩ := (hreg (-r - 1) (-r) L (fun s => G (-s)) hGr hvr V hb' θ'
      (by linarith) hL0 hθρ (fun τ _ => hsmooth τ) (fun l τ hl _ x => hjet l τ hl x) u slice
      (hu' (-r - 1) (-r) (by linarith [hr.2]) (by linarith [hr.1]))).2 (-r)
      ⟨by linarith, le_rfl⟩ (by linarith) (by linarith)
    exact ⟨w, hwv, hwn.trans (mul_le_mul_of_nonneg_right hPQ (norm_nonneg _))⟩
end

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # Sharp fast decay: the window lemma

A reversed curve of the actual drift that is actual-fast at `t` decays in `L²` at the rate `π²/8`
back to every earlier time (`revCurve_fast_decay`, the pairing is conserved by the actual graph).
On the window of a region the actual curve is a transverse reversed curve of the shear `ext p`
(`sharpRevCurve_congr`), so the `P_e`-free regularity of the reduced transverse equation turns the `L²` decay into `H^j`
decay. No splitting of `u` into a slow part and a fast part is needed, hence neither the transverse
row nor `replace_graph` is used. -/

section
variable {K : ScalarConstants} {η : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {v : ℝ → Vec 2 → Vec 2} {ξ : Fin 2 → ℂ} {t₀ S : ℝ}

/-- The `L²` decay of an actual-fast reversed curve at the rate `π²/8`. -/
theorem sharpActual_l2_decay (H : TransverseLocalHyp K η G v ξ) (data : FibreScalarData K η G v t₀ S)
    {s t : ℝ} (hst : s ≤ t) (V : ℝ) (hb' : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2)
    {u : ℝ → ComplexCellL2} {slice : ℝ → TorusHk 1 ℂ} (hu : IsRevCurve H V hb' (-t) (-s) u slice)
    (hfast : cellComplexPair (cellRawTrace (fibreSeriesJet data.r ξ) t + cellConstantCLM 1)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u (-t))) = 0) :
    ‖u (-s)‖ ≤ Real.exp (-(Real.pi ^ 2 / 8) * (t - s)) * ‖u (-t)‖ := by
  have hq32 : fibreNorm ξ ^ 2 ≤ Real.pi ^ 2 / 32 := by
    have h0 := mul_nonneg (mul_nonneg H.hCw H.hCg) (sq_nonneg (fibreNorm ξ))
    nlinarith only [H.hsep, h0]
  have hrate : Real.pi ^ 2 / 4 ≤ 8 * Real.pi ^ 2 / 9 - fibreNorm ξ ^ 2 := by
    have hp : 0 ≤ Real.pi ^ 2 := sq_nonneg _
    linarith only [hq32, hp]
  exact decay_norm_of_sq hrate (by linarith only [hst]) (norm_nonneg _) (norm_nonneg _)
    (revCurve_fast_decay H.hη0 H.hη H.hCg H.hCw H.hG H.hv H.hm H.hw data ξ H.hreal H.hξ H.hsep
      hst V hb' hu hfast)

/-- The exponential bookkeeping of the window lemma. -/
theorem sharpWindow_arith {Cr n z s t : ℝ} (hCr : 0 ≤ Cr) (hn : 0 ≤ n)
    (h : (t - s ≤ 1 ∧ z ≤ Cr * n) ∨
      (1 < t - s ∧ z ≤ Cr * (Real.exp (-(Real.pi ^ 2 / 8) * (t - (s + 1))) * n))) :
    z ≤ (Cr * Real.exp (Real.pi ^ 2 / 8) + 1) * Real.exp (-(Real.pi ^ 2 / 8) * (t - s)) * n := by
  have hX : 0 < Real.exp (Real.pi ^ 2 / 8) := Real.exp_pos _
  have hE : 0 < Real.exp (-(Real.pi ^ 2 / 8) * (t - s)) := Real.exp_pos _
  have hEn : 0 ≤ Real.exp (-(Real.pi ^ 2 / 8) * (t - s)) * n := mul_nonneg hE.le hn
  have e1 : Real.exp (-(Real.pi ^ 2 / 8) * (t - (s + 1))) =
      Real.exp (Real.pi ^ 2 / 8) * Real.exp (-(Real.pi ^ 2 / 8) * (t - s)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hfin : Cr * (Real.exp (Real.pi ^ 2 / 8) * (Real.exp (-(Real.pi ^ 2 / 8) * (t - s)) * n))
      ≤ (Cr * Real.exp (Real.pi ^ 2 / 8) + 1) * Real.exp (-(Real.pi ^ 2 / 8) * (t - s)) * n := by
    nlinarith only [hEn]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hge : 1 ≤ Real.exp (Real.pi ^ 2 / 8) * Real.exp (-(Real.pi ^ 2 / 8) * (t - s)) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by
        have hp : 0 ≤ Real.pi ^ 2 / 8 := by positivity
        nlinarith only [hp, h1])
    refine h2.trans (le_trans ?_ hfin)
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hge hn) hCr
    nlinarith only [this]
  · rw [e1] at h2
    refine h2.trans (le_trans (le_of_eq ?_) hfin)
    ring
end

/-! # Sharp fast decay: proof of `SharpWindowLemmaStatement` -/

/-- **The window lemma.** -/
theorem sharpWindowLemma : SharpWindowLemmaStatement := by
  intro K j ρ hρ0 hρlo
  by_cases hK : 0 ≤ K.Cw
  swap
  · refine ⟨1, 1, 1, 0, le_rfl, one_pos, ?_⟩
    intro η t₀ S ϖ G v g reg pkg _ _ _ _ _ _ ξ H
    exact absurd H.hCw hK
  obtain ⟨Cr, hCr, hreg⟩ := revCurve_regularity transverseRegularity j (max ρ 0)
    (fun l => max (K.Cvj l) 0) (le_max_right _ _) (fun l => le_max_right _ _) hK
  refine ⟨Cr * Real.exp (Real.pi ^ 2 / 8) + 1, 1, 1, 0, ?_, one_pos, ?_⟩
  · have := mul_nonneg hCr.le (Real.exp_pos (Real.pi ^ 2 / 8)).le
    linarith only [this]
  intro η t₀ S ϖ G v g reg pkg hη0 hvs hvj hg0 hg1 hgm ξ H hξρ _ V hb' s t _ hst _ p hl1 hl2 hl3 hl4 _
    u slice hu hfast htrans w₀ hw₀
  have hD := pkg.buffer_nonneg
  obtain ⟨hextv, hextm, hextw⟩ := pkg.ext_drift p
  have Hx : TransverseLocalHyp K η G (pkg.ext p) ξ :=
    ⟨H.hη0, H.hη, H.hCg, H.hCw, H.hG, hextv, hextm, hextw, H.hreal, H.hξ, H.hsep⟩
  have W : TransverseWindowHyp η (pkg.ext p) (reg.orient p) (reg.lo p - reg.buffer)
      (reg.hi p + reg.buffer) (fun l => max (K.Cvj l) 0) :=
    ⟨ext_parallel_invariant pkg p, ext_perp_zero pkg p, ext_window_contDiff pkg p hvs,
      fun l t ht x => (ext_window_jets pkg p hvj l t ht x).trans (le_max_left _ _)⟩
  obtain ⟨Vx, hVx⟩ := hextv.2.1
  have hbx := rev_bound hVx
  have hagree : ∀ τ ∈ Icc (-t) (-s), v (-τ) = pkg.ext p (-τ) := fun τ hτ =>
    funext fun z => (pkg.ext_agree p (-τ) ⟨by linarith [hτ.2], by linarith [hτ.1]⟩ z).symm
  have hux : IsRevCurve Hx Vx hbx (-t) (-s) u slice := sharpRevCurve_congr H Hx V Vx hb' hbx
    hagree hu
  have hAs : reg.lo p - reg.buffer ≤ s := hl3
  have htB : t ≤ reg.hi p + reg.buffer := by linarith only [hl2, hD]
  have hξ' : fibreNorm ξ ≤ max ρ 0 := hξρ.trans (le_max_left _ _)
  have hn : ‖u (-t)‖ ≤ ‖w₀‖ := by rw [← hw₀]; exact torusHk_value_norm_le w₀
  have hdec : ∀ σ, s ≤ σ → σ ≤ t →
      ‖u (-σ)‖ ≤ Real.exp (-(Real.pi ^ 2 / 8) * (t - σ)) * ‖u (-t)‖ := fun σ h1 h2 =>
    sharpActual_l2_decay H pkg.actual h2 V hb'
      (CellWeakHilbertCurve.mono hu (Icc_subset_Icc le_rfl (neg_le_neg h1))) hfast
  by_cases hts : t - s ≤ 1
  · obtain ⟨w', hw'v, hw'n⟩ := (hreg η G (pkg.ext p) ξ Hx Vx hbx (reg.orient p)
      (reg.lo p - reg.buffer) (reg.hi p + reg.buffer) W hξ' (-t) (-s) (neg_le_neg hst)
      (neg_le_neg htB) (neg_le_neg hAs) u slice hux htrans).1 w₀ hw₀ (-s)
      ⟨neg_le_neg hst, le_rfl⟩ (by linarith only [hts])
    exact ⟨w', hw'v, sharpWindow_arith hCr.le (norm_nonneg _) (Or.inl ⟨hts, hw'n⟩)⟩
  · push Not at hts
    have hsub : IsRevCurve Hx Vx hbx (-(s + 1)) (-s) u slice :=
      CellWeakHilbertCurve.mono hux (Icc_subset_Icc (by linarith only [hts]) le_rfl)
    have htr : cellTransverseProjection (reg.orient p) (u (-(s + 1))) = u (-(s + 1)) :=
      revCurve_transverse Hx Vx hbx (reg.orient p) W.ht (neg_le_neg hst) hux htrans (-(s + 1))
        ⟨by linarith only [hts], by linarith only⟩
    obtain ⟨w', hw'v, hw'n⟩ := (hreg η G (pkg.ext p) ξ Hx Vx hbx (reg.orient p)
      (reg.lo p - reg.buffer) (reg.hi p + reg.buffer) W hξ' (-(s + 1)) (-s) (by linarith only)
      (by linarith only [htB, hts]) (neg_le_neg hAs) u slice hsub htr).2.1 (-s)
      ⟨by linarith only, le_rfl⟩ (by linarith only) (by linarith only)
    refine ⟨w', hw'v, sharpWindow_arith hCr.le (norm_nonneg _) (Or.inr ⟨hts, ?_⟩)⟩
    refine hw'n.trans (mul_le_mul_of_nonneg_left ?_ hCr.le)
    refine (hdec (s + 1) (by linarith only) (by linarith only [hts])).trans ?_
    exact mul_le_mul_of_nonneg_left hn (Real.exp_pos _).le

/-- **Sharp fast decay.** -/
theorem sharpFastDecay (hQ : QuietHsDecayStatement) : SharpFastDecayStatement :=
  sharpFastDecay_of_window hQ sharpWindowLemma

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords
namespace AVRegularity.CycleWords.Assembly

/-! # The sharp slow test: the fast remainder

For a reversed curve `urow` from `1` at `-σ`, the curve `v1 = E(σ)·urow - u` is actual-fast at `-σ`
(the conserved pairing of `u` equals `E(σ)`, that of `urow` is `1`), so it decays in `L²` at the rate
`π²/8` (`sharpActual_l2_decay`) and is bounded in `H^j` at the price `P_e^Q`
(`sharpRev_crude_general`). Its datum is `-conj` of the representative of `q(σ) - star E(σ)·1`.
This is used by the defect and the window step. -/

local notation "cjL" => cellFiberCLM Complex.conjCLE.toContinuousLinearMap

variable {K : ScalarConstants}

/-- **The fast remainder.** -/
theorem sharpSlowRem (j : ℕ) (ρ : ℝ) :
    ∃ (C : ℝ) (Q : ℕ), 0 ≤ C ∧ ∀ (s : SharpSlowSetting K ρ) {r σ : ℝ}, s.a ≤ r → r ≤ σ → σ ≤ s.b →
    ∀ (urow : ℝ → ComplexCellL2) (srow : ℝ → TorusHk 1 ℂ),
      IsRevCurve s.H s.V s.hb' (-σ) (-r) urow srow → urow (-σ) = cellConstantCLM 1 →
    ∀ w₀ : TorusHk j ℂ, torusHkValueCLM w₀ = s.q σ - cellConstantCLM (star (s.E σ)) →
    ∃ w₁ : TorusHk j ℂ, torusHkValueCLM w₁ = cellScalarCLM (s.E σ) (urow (-r)) - s.u (-r) ∧
      ‖w₁‖ ≤ C * peFactor s.η ^ Q * Real.exp (-(Real.pi ^ 2 / 8) * (σ - r)) * ‖w₀‖ := by
  obtain ⟨Cg, Q, hCg, hgen⟩ := sharpRev_crude_general (K := K) cellDriftRegularity j
    (ρ := max ρ 0) (le_max_right _ _) (fun l => |K.Cvj l|) (fun l => abs_nonneg _)
  refine ⟨Cg * Real.exp (Real.pi ^ 2 / 8), Q, by positivity, ?_⟩
  intro s r σ hr hrσ hσ urow srow hurow h1 w₀ hw₀
  have hξ : fibreNorm s.ξ ≤ max ρ 0 := s.hξρ.trans (le_max_left _ _)
  have hvj : ∀ (l : ℕ) t z, ‖iteratedFDeriv ℝ l (fun z' => Real.sqrt s.η • s.v t z') z‖ ≤
      |K.Cvj l| := fun l t z => (s.hvj l t z).trans (le_abs_self _)
  have hσs : σ ∈ Icc s.a s.b := ⟨hr.trans hrσ, hσ⟩
  have hu_sub : IsRevCurve s.H s.V s.hb' (-σ) (-r) s.u s.slice :=
    CellWeakHilbertCurve.mono s.hu (Icc_subset_Icc (neg_le_neg hσ) (neg_le_neg hr))
  have hv1 := revCurve_smul_sub s.H s.V s.hb' hurow hu_sub (s.E σ)
  set v1 : ℝ → ComplexCellL2 := fun τ => cellScalarCLM (s.E σ) (urow τ) - s.u τ with hv1def
  -- the datum
  have hv1σ : v1 (-σ) = cellConstantCLM (s.E σ) - s.u (-σ) := by
    simp only [hv1def, h1, cellScalarCLM_constant_one]
  have hq : s.q σ = cjL (s.u (-σ)) := rfl
  have hcj : cjL (v1 (-σ)) = -torusHkValueCLM w₀ := by
    rw [hv1σ, hw₀, hq, map_sub, cellFiberConj_constant, neg_sub]
  have hv1w : v1 (-σ) = torusHkValueCLM (-torusHkConj w₀) := by
    rw [map_neg, torusHkConj_value, hw₀, hq, map_sub, cellFiberConj_involutive,
      cellFiberConj_constant, star_star, hv1σ]
    abel
  have hn0 : ‖v1 (-σ)‖ ≤ ‖w₀‖ := by
    rw [hv1w]
    exact (torusHk_value_norm_le _).trans (by rw [norm_neg, torusHkConj_norm])
  -- the fast class at `-σ`
  have hE := rowCurve_pair s.H s.pkg.actual s.V s.hb' s.hu s.hu1 σ hσs
  have h11 := graph_pair_one s.pkg.actual s.H.hξ σ
  rw [cellFiberConj_constant, star_one] at h11
  have hfast : cellComplexPair (cellRawTrace (fibreSeriesJet s.pkg.actual.r s.ξ) σ +
      cellConstantCLM 1) (cjL (v1 (-σ))) = 0 := by
    rw [hcj, hw₀, neg_sub, cellComplexPair_sub_right]
    have hc : cellConstantCLM (star (s.E σ)) = cellScalarCLM (star (s.E σ)) (cellConstantCLM 1) :=
      (cellScalarCLM_constant_one _).symm
    rw [hc, cellComplexPair_scalar_right, h11, star_star]
    have : cellComplexPair (cellRawTrace (fibreSeriesJet s.pkg.actual.r s.ξ) σ +
        cellConstantCLM 1) (s.q σ) = s.E σ := hE
    rw [this]; ring
  have hξ' : fibreNorm s.ξ ≤ max ρ 0 := hξ
  by_cases hcase : σ - r ≤ 1
  · obtain ⟨w, hwv, hwn⟩ := (hgen s.η s.G s.v s.ξ s.H s.hη hξ s.hvs hvj s.V s.hb' (a := r) (b := σ)
      hrσ v1 _ hv1 r ⟨le_rfl, hrσ⟩).1 hcase (-torusHkConj w₀) hv1w.symm
    refine ⟨w, hwv, hwn.trans ?_⟩
    rw [norm_neg, torusHkConj_norm]
    have hge : 1 ≤ Real.exp (Real.pi ^ 2 / 8) * Real.exp (-(Real.pi ^ 2 / 8) * (σ - r)) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith [sq_nonneg Real.pi])
    have hX : 0 ≤ Cg * peFactor s.η ^ Q * ‖w₀‖ := by
      have := AVRegularity.CycleWords.Assembly.one_le_peFactor s.η
      positivity
    calc Cg * peFactor s.η ^ Q * ‖w₀‖
        ≤ (Real.exp (Real.pi ^ 2 / 8) * Real.exp (-(Real.pi ^ 2 / 8) * (σ - r))) *
          (Cg * peFactor s.η ^ Q * ‖w₀‖) := le_mul_of_one_le_left hX hge
      _ = _ := by ring
  · push Not at hcase
    obtain ⟨w, hwv, hwn⟩ := (hgen s.η s.G s.v s.ξ s.H s.hη hξ s.hvs hvj s.V s.hb' (a := r) (b := σ)
      hrσ v1 _ hv1 r ⟨le_rfl, hrσ⟩).2 hcase.le
    refine ⟨w, hwv, hwn.trans ?_⟩
    have hsub : IsRevCurve s.H s.V s.hb' (-σ) (-(r + 1)) v1 _ :=
      CellWeakHilbertCurve.mono hv1 (Icc_subset_Icc le_rfl (neg_le_neg (by linarith)))
    have hdec := sharpActual_l2_decay s.H s.pkg.actual (s := r + 1) (t := σ) (by linarith) s.V
      s.hb' hsub hfast
    have hrw : -r - 1 = -(r + 1) := by ring
    rw [hrw]
    have e1 : Real.exp (-(Real.pi ^ 2 / 8) * (σ - (r + 1))) =
        Real.exp (Real.pi ^ 2 / 8) * Real.exp (-(Real.pi ^ 2 / 8) * (σ - r)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hP : 0 ≤ Cg * peFactor s.η ^ Q := by
      have := AVRegularity.CycleWords.Assembly.one_le_peFactor s.η
      positivity
    calc Cg * peFactor s.η ^ Q * ‖v1 (-(r + 1))‖
        ≤ Cg * peFactor s.η ^ Q * (Real.exp (-(Real.pi ^ 2 / 8) * (σ - (r + 1))) * ‖v1 (-σ)‖) :=
          mul_le_mul_of_nonneg_left hdec hP
      _ ≤ Cg * peFactor s.η ^ Q * (Real.exp (-(Real.pi ^ 2 / 8) * (σ - (r + 1))) * ‖w₀‖) := by
          gcongr
      _ = _ := by rw [e1]; ring

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public section
namespace AVRegularity.CycleWords.Assembly

/-! # `cycle_mixed_words` from four statements

With the leaves `chainCombination`, `compactChainExistence`, `compactDensity`,
`amplitudePlancherel`, `gaussianPlancherel`, `blochFibreContinuity`, `gaugeJets`
and the reductions (`compactChainGaussian_of_factor`, `retainedMapExists_of_leaves`,
`retainedModelJets_of_leaves`, `retainedGaussian_of_leaves`, `compactDiscard_of_parts`,
`chainDiscard_of_compact`), the five statements of `cycle_mixed_words_of_ingredients` follow from:

* `RetainedAmplitudeFactorStatement`,
* `ChainFullFieldStatement`,
* `QuietHighStatement`,
* `MarksBandStatement`. -/

universe u v

/-- The Gaussian bound for compact chains from `RetainedAmplitudeFactorStatement`. -/
theorem compactChainGaussian_of_open (hF : RetainedAmplitudeFactorStatement.{u, v}) :
    CompactChainGaussianStatement.{u, v} :=
  compactChainGaussian_of_factor hF gaugeJets

/-- **The ingredients of `cycle_mixed_words` from four statements.** -/
theorem mixedWordsIngredients_of_open (hF : RetainedAmplitudeFactorStatement.{u, v})
    (hFF : ChainFullFieldStatement.{u, v}) (hQH : QuietHighStatement.{u, v})
    (hMB : MarksBandStatement.{u, v}) :
    RetainedMapExistsStatement.{u, v} ∧ RetainedModelJetsStatement.{u, v} ∧
      ChainDiscardStatement.{u, v} ∧ RetainedGaussianStatement.{u, v} :=
  ⟨retainedMapExists_of_leaves chainCombination compactChainExistence compactDensity
      amplitudePlancherel (compactChainGaussian_of_open hF) gaussianPlancherel,
    retainedModelJets_of_leaves compactChainExistence compactDensity amplitudePlancherel
      (compactChainGaussian_of_open hF) gaussianPlancherel,
    chainDiscard_of_compact (compactDiscard_of_parts hQH hMB) hFF,
    retainedGaussian_of_leaves chainCombination compactChainExistence compactDensity
      amplitudePlancherel (compactChainGaussian_of_open hF) blochFibreContinuity⟩

end AVRegularity.CycleWords.Assembly
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # Weighted plain decay

`weightedPlainDecay`: estimate (a). If the weight exceeds `1`, a least window exists
with the orientation of the last activity; the datum splits as `A + B` with `A` transverse and fast
(sharp fast decay) and `B` fast (the surplus decay). Otherwise all of `u` is treated as a quiet or
surplus stretch. -/

/-- With activity, the weight is `max 1 (Λ e^{-c(t - τ)})`. -/
theorem wpd_weight_ge (v : ℝ → Vec 2 → Vec 2) (t₀ Λ c t : ℝ) (hne : (activeSet v t₀ t).Nonempty) :
    Λ * Real.exp (-c * (t - lastActive v t₀ t)) ≤ activityWeight v t₀ Λ c t := by
  simp only [activityWeight, hne, ↓reduceIte]
  exact le_max_right _ _

/-- The surplus factor is paid by the weight. -/
theorem wpd_surplus_paid (v : ℝ → Vec 2 → Vec 2) (t₀ Λ c t Pq : ℝ)
    (hne : (activeSet v t₀ t).Nonempty) (hPq : Pq ≤ Λ) :
    Pq * Real.exp (-c * (t - lastActive v t₀ t)) ≤ activityWeight v t₀ Λ c t :=
  (mul_le_mul_of_nonneg_right hPq (Real.exp_pos _).le).trans (wpd_weight_ge v t₀ Λ c t hne)

/-- With weight at most `1`, the surplus factor is at most `1`. -/
theorem wpd_surplus_le_one (v : ℝ → Vec 2 → Vec 2) (t₀ Λ c t Pq : ℝ)
    (hne : (activeSet v t₀ t).Nonempty) (hPq : Pq ≤ Λ)
    (hW : activityWeight v t₀ Λ c t ≤ 1) :
    Pq * Real.exp (-c * (t - lastActive v t₀ t)) ≤ 1 :=
  (wpd_surplus_paid v t₀ Λ c t Pq hne hPq).trans hW

/-- **Estimate (a): the plain decay from a weighted datum**. -/
theorem weightedPlainDecay (hQ : QuietHsDecayStatement) : WeightedPlainDecayStatement := by
  intro K j ρ hρ0 hρ1
  obtain ⟨C25, Cb25, c25, Q25, hC25, hc25, h25⟩ := sharpFastDecay hQ K j ρ hρ0 hρ1
  obtain ⟨Cs, Qs, hCs, hS⟩ := surplusDecay hQ K j ρ hρ0 hρ1
  have hc0 : (0 : ℝ) < 3 * Real.pi ^ 2 / 8 := by positivity
  refine ⟨3 + 5 * C25 + 6 * Cs, max Cb25 1, min c25 (3 * Real.pi ^ 2 / 16), Q25, Qs,
    by linarith, lt_min hc25 (by positivity), ?_⟩
  intro η t₀ S ϖ G v g reg pkg hη hvs hvj hg0 hg1 hmet ξ H hξ Λ₁ hΛ hreg V hb' s t hs hst hts
    u slice hu hfast UT UN hsum htr
  have hP1 := wpd_one_le_pe η
  have hΛ1 : 1 ≤ Λ₁ := (one_le_pow₀ hP1).trans hΛ
  set X := Real.exp (-(Real.pi ^ 2 / 8) * (t - s)) with hX
  have hX0 : 0 < X := Real.exp_pos _
  set W := activityWeight v t₀ Λ₁ (3 * Real.pi ^ 2 / 8) t with hWdef
  have hW1 : 1 ≤ W := one_le_activityWeight _ _ _ _ _
  have hC3 : 3 ≤ 3 + 5 * C25 + 6 * Cs := by linarith only [hC25, hCs]
  -- the quiet case
  have hquietcase : ((activeSet v t₀ t).Nonempty → lastActive v t₀ t < s) →
      ∃ w : TorusHk j ℂ, torusHkValueCLM w = u (-s) ∧
        ‖w‖ ≤ (3 + 5 * C25 + 6 * Cs) * X * (‖UT‖ + W * ‖UN‖) := by
    intro hl
    obtain ⟨w, hw, hn⟩ := sharpQuiet_decay hQ H pkg.actual j hst V hb'
      (wpd_quiet_of_lag (t₀ := t₀) (t := t) v hs hl) hu hfast (UT + UN) hsum
    refine ⟨w, hw, hn.trans ?_⟩
    have he : Real.exp (-(Real.pi ^ 2 / 2) * (t - s)) ≤ X :=
      Real.exp_le_exp.2 (by nlinarith only [mul_nonneg (sq_nonneg Real.pi) (sub_nonneg.2 hst)])
    have hN := norm_add_le UT UN
    have hNN : 0 ≤ ‖UN‖ := norm_nonneg _
    have hTT : 0 ≤ ‖UT‖ := norm_nonneg _
    have h1 : ‖UT + UN‖ ≤ ‖UT‖ + W * ‖UN‖ := by
      nlinarith only [hN, mul_nonneg (sub_nonneg.2 hW1) hNN]
    have h2 : 0 ≤ ‖UT + UN‖ := norm_nonneg _
    calc 3 * Real.exp (-(Real.pi ^ 2 / 2) * (t - s)) * ‖UT + UN‖
        ≤ 3 * X * (‖UT‖ + W * ‖UN‖) := by
          apply mul_le_mul (by linarith only [he]) h1 h2 (by positivity)
      _ ≤ _ := by
          have : 0 ≤ X * (‖UT‖ + W * ‖UN‖) := by positivity
          nlinarith only [this, hC3]
  by_cases hne : (activeSet v t₀ t).Nonempty
  swap
  · exact hquietcase (fun h => absurd h hne)
  by_cases hsτ : lastActive v t₀ t < s
  · exact hquietcase (fun _ => hsτ)
  push Not at hsτ
  have hlag : quietLag v t₀ s t = t - lastActive v t₀ t := by
    simp only [quietLag, hne, ↓reduceIte]
    exact min_eq_right (by linarith only [hsτ])
  by_cases hWgt : 1 < W
  swap
  · -- weight one: everything is surplus
    push Not at hWgt
    obtain ⟨w, hw, hn⟩ := hS η t₀ S ϖ G v g reg pkg hη hvs hvj hg0 hg1 hmet ξ H hξ V hb' hs hst
      hts u slice hu hfast (UT + UN) hsum
    refine ⟨w, hw, hn.trans ?_⟩
    rw [hlag]
    have hle := wpd_surplus_le_one v t₀ Λ₁ (3 * Real.pi ^ 2 / 8) t (peFactor η ^ Qs) hne hΛ hWgt
    have hN := norm_add_le UT UN
    have hNN : 0 ≤ ‖UN‖ := norm_nonneg _
    have hTT : 0 ≤ ‖UT‖ := norm_nonneg _
    have h1 : ‖UT + UN‖ ≤ ‖UT‖ + W * ‖UN‖ := by
      nlinarith only [hN, mul_nonneg (sub_nonneg.2 hW1) hNN]
    have hE := Real.exp_pos (-(3 * Real.pi ^ 2 / 8) * (t - lastActive v t₀ t))
    calc Cs * peFactor η ^ Qs * Real.exp (-(3 * Real.pi ^ 2 / 8) * (t - lastActive v t₀ t)) * X *
          ‖UT + UN‖
        = Cs * X * ((peFactor η ^ Qs * Real.exp (-(3 * Real.pi ^ 2 / 8) *
            (t - lastActive v t₀ t))) * ‖UT + UN‖) := by ring
      _ ≤ Cs * X * (1 * (‖UT‖ + W * ‖UN‖)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul hle h1 (norm_nonneg _) zero_le_one
      _ ≤ _ := by
          have : 0 ≤ X * (‖UT‖ + W * ‖UN‖) := by positivity
          nlinarith only [this, hCs, hC25, mul_nonneg (mul_nonneg (by linarith only [hCs] : (0:ℝ) ≤ Cs) hX0.le) (by positivity : 0 ≤ ‖UT‖ + W * ‖UN‖)]
  -- weight above one: the splitting `A + B`
  have hD := pkg.buffer_nonneg
  obtain ⟨hreg25, hΛD⟩ := wpd_regime Cb25 c25 Λ₁ (peFactor η ^ Q25) reg.buffer (reg.joins : ℝ)
    (one_le_pow₀ hP1) hΛ1 hD (Nat.cast_nonneg _) hreg
  have hr : t ∈ Icc t₀ (t₀ + S) := ⟨hs.trans hst, hts⟩
  have horient : ∀ p', IsLeastWindow reg p' t → reg.orient p' = activityOrient reg v t₀ t :=
    fun p' hp' => least_orient_eq_activityOrient pkg hc0 hΛD hr hWgt p' hp'
  obtain ⟨P, hPv, hPn⟩ := transverseHsProjection (activityOrient reg v t₀ t) j
  have hF := wpd_trace_small H pkg.actual t
  have hfast0 : cellComplexPair (cellRawTrace (fibreSeriesJet pkg.actual.r ξ) t +
      cellConstantCLM 1) (cellFiberCLM Complex.conjCLE.toContinuousLinearMap
        (torusHkValueCLM (UT + UN))) = 0 := by rw [hsum]; exact hfast
  obtain ⟨AH, BH, κ, hAn, hBn, hAv, hABsum, hAfast⟩ := wpd_split_data _ hF j P hPn UT UN hfast0
  obtain ⟨uA, uB, sA, sB, huA, huB, hA0, hB0, hAB⟩ :=
    wpd_split_curve H V hb' hst hu (torusHkValueCLM AH)
  have hfastA : cellComplexPair (cellRawTrace (fibreSeriesJet pkg.actual.r ξ) t +
      cellConstantCLM 1) (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (uA (-t))) = 0 := by
    rw [hA0]; exact hAfast
  have hfastB : cellComplexPair (cellRawTrace (fibreSeriesJet pkg.actual.r ξ) t +
      cellConstantCLM 1) (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (uB (-t))) = 0 := by
    rw [hB0, map_sub, cellComplexPair_sub_right, hfast, hAfast, sub_zero]
  have htrA : ∀ p', IsLeastWindow reg p' t →
      cellTransverseProjection (reg.orient p') (uA (-t)) = uA (-t) := by
    intro p' hp'
    rw [horient p' hp', hA0, hAv]
    apply wpd_transverse_sub_const
    rw [map_add, htr, hPv UN, AVRegularity.CycleWords.cellTransverseProjection_idempotent]
  obtain ⟨wA, hwA, hnA⟩ := h25 η t₀ S ϖ G v g reg pkg hη hvs hvj hg0 hg1 hmet ξ H hξ hreg25 V hb'
    hs hst hts uA sA huA hfastA htrA AH hA0.symm
  have hBv : torusHkValueCLM BH = uB (-t) := by
    rw [hB0, ← hsum]
    exact eq_sub_of_add_eq' hABsum
  obtain ⟨wB, hwB, hnB⟩ := hS η t₀ S ϖ G v g reg pkg hη hvs hvj hg0 hg1 hmet ξ H hξ V hb' hs hst
    hts uB sB huB hfastB BH hBv
  refine ⟨wA + wB, ?_, ?_⟩
  · rw [map_add, hwA, hwB]
    exact hAB (-s)
  · rw [hlag] at hnB
    have hle := wpd_surplus_paid v t₀ Λ₁ (3 * Real.pi ^ 2 / 8) t (peFactor η ^ Qs) hne hΛ
    have hnn : 0 ≤ ‖BH‖ := norm_nonneg _
    refine (norm_add_le wA wB).trans ?_
    exact wpd_combine C25 Cs X W ‖UT‖ ‖UN‖ ‖wA‖ ‖wB‖ (peFactor η ^ Qs)
      (Real.exp (-(3 * Real.pi ^ 2 / 8) * (t - lastActive v t₀ t))) ‖BH‖ hC25 hCs hX0 hW1
      (norm_nonneg _) (norm_nonneg _) hle hBn hnn
      (hnA.trans (by
        have := mul_le_mul_of_nonneg_left hAn (by positivity : 0 ≤ C25 * X)
        linarith only [this]))
      (by simpa only [mul_assoc] using hnB)

end AVRegularity.CycleWords.Assembly
end
end
