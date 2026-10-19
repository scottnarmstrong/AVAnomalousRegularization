-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.MixedWords.WeightedPlainDecay
import AVRegularity.CycleWords.MixedWords.WeightedPlainDecayKappa
import AVRegularity.CycleWords.MixedWords.StageExpansionLetter
public import AVRegularity.CycleWords.Assembly.InteriorScalarIngredients
public import AVRegularity.CycleWords.MixedWords.CompactChainExistence
import AVRegularity.CycleWords.FibreGraphNativeSeries
import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public noncomputable section
open AVRegularity.Sobolev
namespace AVRegularity.CycleWords.Assembly

/-- Head-class cache: the normed group of the periodic Sobolev carrier. -/
local instance transformBoundTorusNormed {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedAddCommGroup (TorusHk K E) := inferInstance
/-- Head-class cache: the inner product space of the periodic Sobolev carrier. -/
local instance transformBoundTorusInner {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    InnerProductSpace ℝ (TorusHk K E) := inferInstance
/-- Head-class cache: the normed space of the periodic Sobolev carrier. -/
local instance transformBoundTorusSpace {K : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] :
    NormedSpace ℝ (TorusHk K E) := inferInstance

end AVRegularity.CycleWords.Assembly
end

attribute [local instance] AVRegularity.CycleWords.Assembly.transformBoundTorusNormed
  AVRegularity.CycleWords.Assembly.transformBoundTorusInner
  AVRegularity.CycleWords.Assembly.transformBoundTorusSpace

section
/-! # The sharp slow test: the transversality defect

In the least window `p`, start at `σ = min(b, hi_p + D)`. The row curve `urow` from `1` at `-σ`
is transverse (a shear on the window); `u = E(σ)·urow - v1` with `v1` the fast remainder
(`sharpSlowRem`), hence `(1 - P)u(-r) = -(1 - P)v1(-r)`; `v1` decays at `π²/8` against the growth
`π²/16` of `E`, over a time `≥ D/2`. If `b < hi_p + D` then `v1 ≡ 0`. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords

namespace AVRegularity.CycleWords.Assembly

local notation "cjL" => cellFiberCLM Complex.conjCLE.toContinuousLinearMap

variable {K : ScalarConstants} {ρ : ℝ}

/-- The transverse row curve from `1` at `-σ` on the window of the least window `p`. -/
theorem sharpSlowD_row (s : SharpSlowSetting K ρ) (p : Fin s.reg.P) {r σ : ℝ}
    (hlo : s.reg.lo p - s.reg.buffer ≤ r) (hrσ : r ≤ σ) (hhi : σ ≤ s.reg.hi p + s.reg.buffer) :
    ∃ (urow : ℝ → ComplexCellL2) (srow : ℝ → TorusHk 1 ℂ),
      IsRevCurve s.H s.V s.hb' (-σ) (-r) urow srow ∧ urow (-σ) = cellConstantCLM 1 ∧
      ∀ τ ∈ Icc (-σ) (-r), cellTransverseProjection (s.reg.orient p) (urow τ) = urow τ := by
  obtain ⟨hextv, hextm, hextw⟩ := s.pkg.ext_drift p
  have Hx : TransverseLocalHyp K s.η s.G (s.pkg.ext p) s.ξ :=
    ⟨s.H.hη0, s.H.hη, s.H.hCg, s.H.hCw, s.H.hG, hextv, hextm, hextw, s.H.hreal, s.H.hξ,
      s.H.hsep⟩
  obtain ⟨Vx, hVx⟩ := hextv.2.1
  have hbx := rev_bound hVx
  obtain ⟨urow, srow, hurx, h1⟩ := revCurve_exists Hx Vx hbx (neg_le_neg hrσ) (cellConstantCLM 1)
  have htr := revCurve_transverse Hx Vx hbx (s.reg.orient p) (ext_parallel_invariant s.pkg p)
    (neg_le_neg hrσ) hurx (by rw [h1, cellTransverseProjection_one])
  have hagree : ∀ τ ∈ Icc (-σ) (-r), s.v (-τ) = s.pkg.ext p (-τ) := fun τ hτ =>
    funext fun z => (s.pkg.ext_agree p (-τ) ⟨by linarith [hτ.2], by linarith [hτ.1]⟩ z).symm
  exact ⟨urow, srow, sharpRevCurve_congr Hx s.H Vx s.V hbx s.hb'
    (fun τ hτ => (hagree τ hτ).symm) hurx, h1, htr⟩

/-- Algebra of the defect: from a representative of the fast remainder at `-r`. -/
theorem sharpSlowD_rep (s : SharpSlowSetting K ρ) (e : Fin 2) (j : ℕ)
    (Pj : TorusHk j ℂ →L[ℝ] TorusHk j ℂ)
    (hPv : ∀ U, torusHkValueCLM (Pj U) = cellTransverseProjection e (torusHkValueCLM U))
    (hPn : ∀ U, ‖Pj U‖ ≤ ‖U‖) {r : ℝ} (urow : ℝ → ComplexCellL2)
    (htr : cellTransverseProjection e (urow (-r)) = urow (-r)) (c : ℂ) (w₁ : TorusHk j ℂ)
    (hw₁ : torusHkValueCLM w₁ = cellScalarCLM c (urow (-r)) - s.u (-r)) :
    ∃ w : TorusHk j ℂ, torusHkValueCLM w = s.q r - cellTransverseProjection e (s.q r) ∧
      ‖w‖ ≤ 2 * ‖w₁‖ := by
  refine ⟨-torusHkConj (w₁ - Pj w₁), ?_, ?_⟩
  · simp only [map_neg, map_sub, torusHkConj_value, hPv, hw₁, SharpSlowSetting.q,
      cellTransverseProjection_scalar, htr, cellTransverseProjection_conjugate]
    abel
  · calc ‖-torusHkConj (w₁ - Pj w₁)‖ = ‖w₁ - Pj w₁‖ := by rw [norm_neg, torusHkConj_norm]
      _ ≤ ‖w₁‖ + ‖Pj w₁‖ := norm_sub_le _ _
      _ ≤ 2 * ‖w₁‖ := by linarith [hPn w₁]

/-- The heat-gap exponent over abstract reals. -/
private theorem sharpSlow_gap_exponent {P D B : ℝ} (hP : 8 ≤ P) (hB : 0 ≤ B) (hD : B / 2 ≤ D) :
    -(P / 8) * D + P / 16 * D ≤ -(1 / 4) * B := by
  nlinarith

/-- **The defect step** (`SharpSlowDefectStatement`). -/
theorem sharpSlowDefect : SharpSlowDefectStatement := by
  intro hQ K j ρ hρ0 hρ1
  obtain ⟨C, Q, hC, hrem⟩ := sharpSlowRem (K := K) j ρ
  refine ⟨2 * C, 0, 1 / 4, Q, by positivity, le_rfl, by norm_num, ?_⟩
  intro s _ M hM hb r hr p hp
  have hD := s.pkg.buffer_nonneg
  obtain ⟨Pj, hPv, hPn⟩ := transverseHsProjection (s.reg.orient p) j
  have hrp : r ∈ Icc (s.reg.lo p) (s.reg.hi p + s.reg.buffer / 2) := hp.1
  have hE0 := norm_nonneg (s.E r)
  have hpe : 1 ≤ peFactor s.η ^ Q := one_le_pow₀ (AVRegularity.CycleWords.Assembly.one_le_peFactor s.η)
  have hfn := fibreNorm_nonneg s.ξ
  have hfinal : 0 ≤ 2 * C * peFactor s.η ^ Q * Real.exp (-(1 / 4) * s.reg.buffer) *
      (fibreNorm s.ξ + M) := by positivity
  by_cases hcase : s.reg.hi p + s.reg.buffer ≤ s.b
  · -- start at `hi_p + D`
    set σ := s.reg.hi p + s.reg.buffer with hσ
    have hrσ : r ≤ σ := by linarith [hrp.2]
    obtain ⟨urow, srow, hcurve, h1, htr⟩ := sharpSlowD_row s p (r := r) (σ := σ)
      (by linarith [hrp.1]) hrσ le_rfl
    obtain ⟨w₀, hw₀, hn₀⟩ := hb σ ⟨hr.1.trans hrσ, hcase⟩
    obtain ⟨w₁, hw₁, hn₁⟩ := hrem s hr.1 hrσ hcase urow srow hcurve h1 w₀ hw₀
    obtain ⟨w, hw, hn⟩ := sharpSlowD_rep s (s.reg.orient p) j Pj hPv hPn urow
      (htr (-r) ⟨by linarith, le_rfl⟩) (s.E σ) w₁ hw₁
    refine ⟨w, hw, hn.trans ?_⟩
    have hg := sharpSlowQ_E_growth s hrσ hcase
    have hd : s.reg.buffer / 2 ≤ σ - r := by linarith [hrp.2]
    have hexp : Real.exp (-(Real.pi ^ 2 / 8) * (σ - r)) * Real.exp (Real.pi ^ 2 / 16 * (σ - r)) ≤
        Real.exp (-(1 / 4) * s.reg.buffer) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hp2 : (8 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
      exact sharpSlow_gap_exponent hp2 hD hd
    have hpos := Real.exp_pos (-(Real.pi ^ 2 / 8) * (σ - r))
    calc 2 * ‖w₁‖ ≤ 2 * (C * peFactor s.η ^ Q * Real.exp (-(Real.pi ^ 2 / 8) * (σ - r)) * ‖w₀‖) := by
          gcongr
      _ ≤ 2 * (C * peFactor s.η ^ Q * Real.exp (-(Real.pi ^ 2 / 8) * (σ - r)) *
            (M * ‖s.E σ‖)) := by gcongr
      _ ≤ 2 * (C * peFactor s.η ^ Q * Real.exp (-(Real.pi ^ 2 / 8) * (σ - r)) *
            (M * (Real.exp (Real.pi ^ 2 / 16 * (σ - r)) * ‖s.E r‖))) := by gcongr
      _ = 2 * C * peFactor s.η ^ Q * M *
            (Real.exp (-(Real.pi ^ 2 / 8) * (σ - r)) * Real.exp (Real.pi ^ 2 / 16 * (σ - r))) *
            ‖s.E r‖ := by ring
      _ ≤ 2 * C * peFactor s.η ^ Q * M * Real.exp (-(1 / 4) * s.reg.buffer) * ‖s.E r‖ := by
          gcongr
      _ ≤ _ := by
          have : 0 ≤ 2 * C * peFactor s.η ^ Q * Real.exp (-(1 / 4) * s.reg.buffer) := by positivity
          nlinarith [mul_nonneg this hfn, mul_nonneg this hM]
  · -- `b < hi_p + D`: start at `b`, `v1 ≡ 0`
    push Not at hcase
    have hrb : r ≤ s.b := hr.2
    obtain ⟨urow, srow, hcurve, h1, htr⟩ := sharpSlowD_row s p (r := r) (σ := s.b)
      (by linarith [hrp.1]) hrb hcase.le
    have hqb : s.q s.b = cellConstantCLM 1 := by
      unfold SharpSlowSetting.q
      rw [s.hu1, cellFiberConj_constant, star_one]
    have hEb : s.E s.b = 1 := by
      unfold SharpSlowSetting.E; simp
    obtain ⟨w₁, hw₁, hn₁⟩ := hrem s hr.1 hrb le_rfl urow srow hcurve h1 (0 : TorusHk j ℂ)
      (by rw [map_zero, hqb, hEb, star_one, sub_self])
    obtain ⟨w, hw, hn⟩ := sharpSlowD_rep s (s.reg.orient p) j Pj hPv hPn urow
      (htr (-r) ⟨by linarith, le_rfl⟩) (s.E s.b) w₁ hw₁
    refine ⟨w, hw, hn.trans ?_⟩
    rw [norm_zero, mul_zero] at hn₁
    have : ‖w₁‖ = 0 := le_antisymm hn₁ (norm_nonneg _)
    rw [this, mul_zero]
    positivity

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # The sharp slow test: the normalized actual row in `H^j`

For the transverse row curve `urow` from `1` at `-σ` on the window of the region `p`, the
normalized row `exp(-∫_r^σ λ_act)·urow(-r) - 1` has an `H^j` representative of norm `≤ C|ξ|`.
The `L²` input is `actualRow_l2` with the actual data; the regularity input is
`revCurve_regularity` for the shear `ext p` (the curve is transported by `sharpRevCurve_congr`). -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords

namespace AVRegularity.CycleWords.Assembly

variable {K : ScalarConstants} {ρ : ℝ}

/-- Transport of a reversed curve of the actual drift on the window to the shear `ext p`, with
the regularity clauses 2 and 3. -/
theorem sharpSlowRowHj_reg (hR : TransverseRegularityStatement) (j : ℕ) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (hCw : 0 ≤ K.Cw) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : SharpSlowSetting K ρ) (p : Fin s.reg.P) {a b : ℝ} (u : ℝ → ComplexCellL2)
      (slice : ℝ → TorusHk 1 ℂ), a ≤ b → -(s.reg.hi p + s.reg.buffer) ≤ a →
      b ≤ -(s.reg.lo p - s.reg.buffer) → IsRevCurve s.H s.V s.hb' a b u slice →
      cellTransverseProjection (s.reg.orient p) (u a) = u a →
      (∀ t ∈ Icc a b, a + 1 ≤ t → t ≤ a + 2 →
        ∃ w' : TorusHk j ℂ, torusHkValueCLM w' = u t ∧ ‖w'‖ ≤ C * ‖u a‖) ∧
      (u a = cellConstantCLM 1 → ∀ t ∈ Icc a b, t ≤ a + 2 →
        ∃ w' : TorusHk j ℂ, torusHkValueCLM w' = u t - cellConstantCLM 1 ∧
          ‖w'‖ ≤ C * fibreNorm s.ξ) := by
  obtain ⟨Cr, hCr, hreg⟩ := revCurve_regularity (K := K) hR j ρ (fun l => max (K.Cvj l) 0) hρ
    (fun l => le_max_right _ _) hCw
  refine ⟨Cr, hCr, ?_⟩
  intro s p a b u slice hab ha hb hu hi
  have hD := s.pkg.buffer_nonneg
  obtain ⟨hextv, hextm, hextw⟩ := s.pkg.ext_drift p
  have Hx : TransverseLocalHyp K s.η s.G (s.pkg.ext p) s.ξ :=
    ⟨s.H.hη0, s.H.hη, s.H.hCg, s.H.hCw, s.H.hG, hextv, hextm, hextw, s.H.hreal, s.H.hξ,
      s.H.hsep⟩
  have W : TransverseWindowHyp s.η (s.pkg.ext p) (s.reg.orient p) (s.reg.lo p - s.reg.buffer)
      (s.reg.hi p + s.reg.buffer) (fun l => max (K.Cvj l) 0) :=
    ⟨ext_parallel_invariant s.pkg p, ext_perp_zero s.pkg p, ext_window_contDiff s.pkg p s.hvs,
      fun l t ht x => (ext_window_jets s.pkg p s.hvj l t ht x).trans (le_max_left _ _)⟩
  obtain ⟨Vx, hVx⟩ := hextv.2.1
  have hbx := rev_bound hVx
  have hagree : ∀ τ ∈ Icc a b, s.v (-τ) = s.pkg.ext p (-τ) := fun τ hτ =>
    funext fun z => (s.pkg.ext_agree p (-τ) ⟨by linarith [hτ.2], by linarith [hτ.1]⟩ z).symm
  have hux : IsRevCurve Hx Vx hbx a b u slice :=
    sharpRevCurve_congr s.H Hx s.V Vx s.hb' hbx hagree hu
  have hξ' : fibreNorm s.ξ ≤ ρ := s.hξρ
  obtain ⟨_, h2, h3⟩ := hreg s.η s.G (s.pkg.ext p) s.ξ Hx Vx hbx (s.reg.orient p)
    (s.reg.lo p - s.reg.buffer) (s.reg.hi p + s.reg.buffer) W hξ' a b hab ha hb u slice hux hi
  exact ⟨h2, h3⟩


/-- **The normalized actual row in `H^j`.** -/
theorem sharpSlowRowHj (K : ScalarConstants) (j : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : SharpSlowSetting K ρ) (p : Fin s.reg.P) {r σ : ℝ},
      s.reg.lo p - s.reg.buffer ≤ r → r ≤ σ → σ ≤ s.reg.hi p + s.reg.buffer →
      ∀ (urow : ℝ → ComplexCellL2) (srow : ℝ → TorusHk 1 ℂ),
      IsRevCurve s.H s.V s.hb' (-σ) (-r) urow srow → urow (-σ) = cellConstantCLM 1 →
      (∀ τ ∈ Icc (-σ) (-r), cellTransverseProjection (s.reg.orient p) (urow τ) = urow τ) →
      ∃ W : TorusHk j ℂ, torusHkValueCLM W =
          cellScalarCLM (Complex.exp (-∫ τ in r..σ, fibreSeriesC s.pkg.actual.lam s.ξ τ))
            (urow (-r)) - cellConstantCLM 1 ∧ ‖W‖ ≤ C * fibreNorm s.ξ := by
  by_cases hK : 0 ≤ K.Cw ∧ 0 ≤ K.Cg
  swap
  · refine ⟨0, le_rfl, ?_⟩
    intro s
    exact absurd ⟨s.H.hCw, s.H.hCg⟩ hK
  obtain ⟨hCw, hCg⟩ := hK
  obtain ⟨Cr, hCr, hreg⟩ := sharpSlowRowHj_reg (K := K) transverseRegularity j ρ hρ hCw
  have hM : 0 ≤ rowConst K (4 * (ρ + K.Cw)) ρ := by unfold rowConst; positivity
  set M := rowConst K (4 * (ρ + K.Cw)) ρ with hMdef
  set E := Real.exp (Real.pi ^ 2 / 4) with hE
  have hE0 : 0 < E := Real.exp_pos _
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, ‖torusHigherScalarCLM j Complex.I‖ = κ := ⟨_, rfl⟩
  obtain ⟨κ1, hκ1⟩ : ∃ κ1 : ℝ, ‖torusHigherConstant j 1‖ = κ1 := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ := hκ ▸ ContinuousLinearMap.opNorm_nonneg _
  have hκ10 : 0 ≤ κ1 := hκ1 ▸ norm_nonneg _
  have hL0 : 0 ≤ 8 + K.Cw * K.Cg := by positivity
  refine ⟨(1 + κ) * (E * (Cr * M + Cr) + (8 + K.Cw * K.Cg) * ρ * E * κ1) + 1, by positivity, ?_⟩
  intro s p r σ hlo hrσ hhi urow srow hu h1 htr
  set lam := fibreSeriesC s.pkg.actual.lam s.ξ with hlam
  have hn0 := fibreNorm_nonneg s.ξ
  have hD := s.pkg.buffer_nonneg
  have hphase : ∀ (γ : ℂ) (Y : ComplexCellL2) (w : TorusHk j ℂ) (Bw : ℝ),
      torusHkValueCLM w = (1 : ℂ) • Y - cellConstantCLM 1 → ‖w‖ ≤ Bw * fibreNorm s.ξ →
      Bw ≤ Cr * M + Cr → ‖γ‖ ≤ E → ‖γ - 1‖ ≤ (8 + K.Cw * K.Cg) * ρ * E * fibreNorm s.ξ →
      ∃ W' : TorusHk j ℂ, torusHkValueCLM W' = γ • Y - cellConstantCLM 1 ∧
        ‖W'‖ ≤ ((1 + κ) * (E * (Cr * M + Cr) + (8 + K.Cw * K.Cg) * ρ * E * κ1) + 1) *
          fibreNorm s.ξ := by
    intro γ Y w Bw hw hwn hBw hγ hγ1
    refine ⟨torusHigherScalarCLM j γ w + torusHigherConstant j (γ - 1), ?_, ?_⟩
    · rw [torusHigherCorrection_phase_change_value j γ 1 Y w hw, mul_one]
    · refine (torusHigherCorrection_phase_change_norm_le j γ w).trans ?_
      rw [hκ, hκ1]
      have ha : ‖γ‖ * ‖w‖ ≤ E * ((Cr * M + Cr) * fibreNorm s.ξ) :=
        mul_le_mul hγ (hwn.trans (mul_le_mul_of_nonneg_right hBw hn0)) (norm_nonneg _) hE0.le
      have hb : ‖γ - 1‖ * κ1 ≤ ((8 + K.Cw * K.Cg) * ρ * E * fibreNorm s.ξ) * κ1 :=
        mul_le_mul_of_nonneg_right hγ1 hκ10
      calc (1 + κ) * (‖γ‖ * ‖w‖ + ‖γ - 1‖ * κ1)
          ≤ (1 + κ) * (E * ((Cr * M + Cr) * fibreNorm s.ξ) +
              ((8 + K.Cw * K.Cg) * ρ * E * fibreNorm s.ξ) * κ1) :=
            mul_le_mul_of_nonneg_left (add_le_add ha hb) (by positivity)
        _ = (1 + κ) * (E * (Cr * M + Cr) + (8 + K.Cw * K.Cg) * ρ * E * κ1) *
              fibreNorm s.ξ := by ring
        _ ≤ _ := by rw [add_mul, one_mul]; linarith
  have hu1 : cellTransverseProjection (s.reg.orient p) (urow (-σ)) = urow (-σ) := by
    rw [h1, cellTransverseProjection_one]
  have hmem : ∀ τ, -σ ≤ τ → τ ≤ -r → -(s.reg.hi p + s.reg.buffer) ≤ τ ∧
      τ ≤ -(s.reg.lo p - s.reg.buffer) := fun τ h₁ h₂ =>
    ⟨by linarith, by linarith⟩
  by_cases hBσ : σ ≤ r + 1
  · obtain ⟨w', hw'v, hw'n⟩ := (hreg s p urow srow (neg_le_neg hrσ) (by linarith) (by linarith)
      hu hu1).2 h1 (-r) ⟨neg_le_neg hrσ, le_rfl⟩ (by linarith)
    obtain ⟨hγ, hγ1⟩ := phase_unit_bounds s.H s.pkg.actual s.hξρ (s := r) (t := σ) hrσ hBσ
    obtain ⟨W', hW'v, hW'n⟩ := hphase _ (urow (-r)) w' Cr (by rw [hw'v, one_smul]) hw'n
      (by linarith [mul_nonneg hCr.le hM]) hγ hγ1
    exact ⟨W', by rw [hW'v, cellScalarCLM_smul], hW'n⟩
  · push Not at hBσ
    have hint : ∀ a b, a ≤ b → IntervalIntegrable lam volume a b := fun a b hab =>
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
        (symbol_integrableOn s.pkg.actual s.H.hη0 s.H.hη s.H.hCg s.H.hCw s.H.hG s.H.hv s.H.hw
          s.H.hξ a b)
    obtain ⟨y, ys, hy, hy0⟩ := revCurve_exists s.H s.V s.hb' (a := -(r + 1)) (b := -r)
      (by linarith) (cellConstantCLM 1)
    have hus : IsRevCurve s.H s.V s.hb' (-σ) (-r) urow srow := hu
    have hus' : IsRevCurve s.H s.V s.hb' (-(r + 1)) (-r) urow srow :=
      CellWeakHilbertCurve.mono hu (Icc_subset_Icc (by linarith) le_rfl)
    have hz := revCurve_smul_sub s.H s.V s.hb' hus' hy
      (Complex.exp (-∫ τ in (r + 1)..σ, lam τ))
    have hr1 : -(r + 1) ∈ Icc (-σ) (-r) := ⟨by linarith, by linarith⟩
    have hzt : cellTransverseProjection (s.reg.orient p)
        (cellScalarCLM (Complex.exp (-∫ τ in (r + 1)..σ, lam τ)) (urow (-(r + 1))) -
          y (-(r + 1))) =
        cellScalarCLM (Complex.exp (-∫ τ in (r + 1)..σ, lam τ)) (urow (-(r + 1))) -
          y (-(r + 1)) := by
      rw [map_sub, cellTransverseProjection_scalar, htr _ hr1, hy0, cellTransverseProjection_one]
    obtain ⟨wz, hwzv, hwzn⟩ := (hreg s p _ _ (by linarith) (by linarith) (by linarith) hz hzt).1
      (-r) ⟨by linarith, le_rfl⟩ (by linarith) (by linarith)
    have hzl2 : ‖cellScalarCLM (Complex.exp (-∫ τ in (r + 1)..σ, lam τ))
        (urow (-(r + 1))) - y (-(r + 1))‖ ≤ M * fibreNorm s.ξ := by
      rw [hy0]
      exact actualRow_l2 s.H s.pkg.actual (ρ := ρ) s.hξρ s.V s.hb' urow srow hu h1 (r + 1)
        ⟨by linarith, hBσ.le⟩
    obtain ⟨wy, hwyv, hwyn⟩ := (hreg s p y ys (by linarith) (by linarith) (by linarith) hy
      (by rw [hy0, cellTransverseProjection_one])).2 hy0 (-r) ⟨by linarith, le_rfl⟩
      (by linarith)
    have hsum : torusHkValueCLM (wz + wy) = (1 : ℂ) •
        (Complex.exp (-∫ τ in (r + 1)..σ, lam τ) • urow (-r)) - cellConstantCLM 1 := by
      rw [map_add, hwzv, hwyv, one_smul]
      simp only [cellScalarCLM_smul]
      abel
    have hwn : ‖wz + wy‖ ≤ (Cr * M + Cr) * fibreNorm s.ξ := by
      calc ‖wz + wy‖ ≤ ‖wz‖ + ‖wy‖ := norm_add_le _ _
        _ ≤ Cr * (M * fibreNorm s.ξ) + Cr * fibreNorm s.ξ :=
            add_le_add (hwzn.trans (mul_le_mul_of_nonneg_left hzl2 hCr.le)) hwyn
        _ = (Cr * M + Cr) * fibreNorm s.ξ := by ring
    obtain ⟨hγ, hγ1⟩ := phase_unit_bounds s.H s.pkg.actual s.hξρ (s := r) (t := r + 1)
      (by linarith) le_rfl
    obtain ⟨W', hW'v, hW'n⟩ := hphase _ _ (wz + wy) (Cr * M + Cr) hsum hwn le_rfl hγ hγ1
    refine ⟨W', ?_, hW'n⟩
    have hsplit : Complex.exp (-∫ τ in r..σ, lam τ) =
        Complex.exp (-∫ τ in r..(r + 1), lam τ) * Complex.exp (-∫ τ in (r + 1)..σ, lam τ) := by
      rw [← Complex.exp_add, ← neg_add,
        intervalIntegral.integral_add_adjacent_intervals (hint r (r + 1) (by linarith))
          (hint (r + 1) σ hBσ.le)]
    rw [hW'v, cellScalarCLM_smul, hsplit, mul_smul]

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # The sharp slow test: the window step, reduced to the row step

For `r` in an extended window `p` take `σ = min(b, hi_p + D)` and the transverse row curve `urow`
from `1` at `-σ` (`sharpSlowD_row`). Then `u = E(σ)·urow - v1` with `v1` the fast remainder
(`sharpSlowRem`): `v1` is bounded by `(M/2)|E(r)|` (decay `π²/8` against the growth `π²/16` of `E`
over a time `≥ D/2`, `WB`), and the slow part `E(σ)·urow(-r) - E(r)·1` is
`SharpSlowRowStepStatement` (proved as `sharpSlowRowStep`). -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords

namespace AVRegularity.CycleWords.Assembly

variable {K : ScalarConstants} {ρ : ℝ}

/-- **Row step.** On the window of the region `p` the row curve `urow` from `1` at `-σ`
satisfies `E(σ)·urow(-r) = E(r)·1 + O(|ξ|)|E(r)|` in `H^j`, at no price in `P_e`. This is the
`H^j` bound of the normalized row (for the shear `ext p` and `(ext_local p).lam`) with the actual
symbol in place of the symbol of the extension: `exp(-∫_r^σ λ_act)·urow(-r) - 1` is `H^j`-small. -/
def SharpSlowRowStepStatement : Prop :=
  ∀ (K : ScalarConstants) (j : ℕ) (ρ : ℝ), ρ < K.ξ0 → ρ ≤ 2 * K.ξlo →
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : SharpSlowSetting K ρ) (p : Fin s.reg.P) {r σ : ℝ}, s.a ≤ r →
    s.reg.lo p - s.reg.buffer ≤ r → r ≤ σ → σ ≤ s.b → σ ≤ s.reg.hi p + s.reg.buffer →
    ∀ (urow : ℝ → ComplexCellL2) (srow : ℝ → TorusHk 1 ℂ),
      IsRevCurve s.H s.V s.hb' (-σ) (-r) urow srow → urow (-σ) = cellConstantCLM 1 →
      (∀ τ ∈ Icc (-σ) (-r), cellTransverseProjection (s.reg.orient p) (urow τ) = urow τ) →
      ∃ w : TorusHk j ℂ, torusHkValueCLM w =
          cellScalarCLM (s.E σ) (urow (-r)) - cellConstantCLM (s.E r) ∧
        ‖w‖ ≤ C * fibreNorm s.ξ * ‖s.E r‖

local notation "cjL" => cellFiberCLM Complex.conjCLE.toContinuousLinearMap

/-- Window step, case `hi_p + D ≤ b`. -/
theorem sharpSlowW_hi (s : SharpSlowSetting K ρ) (j : ℕ) (C Cr : ℝ) (Q : ℕ) (hCr : 0 ≤ Cr)
    (hrem : ∀ {r σ : ℝ}, s.a ≤ r → r ≤ σ → σ ≤ s.b →
      ∀ (urow : ℝ → ComplexCellL2) (srow : ℝ → TorusHk 1 ℂ),
      IsRevCurve s.H s.V s.hb' (-σ) (-r) urow srow → urow (-σ) = cellConstantCLM 1 →
      ∀ w₀ : TorusHk j ℂ, torusHkValueCLM w₀ = s.q σ - cellConstantCLM (star (s.E σ)) →
      ∃ w₁ : TorusHk j ℂ, torusHkValueCLM w₁ = cellScalarCLM (s.E σ) (urow (-r)) - s.u (-r) ∧
        ‖w₁‖ ≤ Cr * peFactor s.η ^ Q * Real.exp (-(Real.pi ^ 2 / 8) * (σ - r)) * ‖w₀‖)
    (hrowK : ∀ (p : Fin s.reg.P) {r σ : ℝ}, s.a ≤ r →
      s.reg.lo p - s.reg.buffer ≤ r → r ≤ σ → σ ≤ s.b → σ ≤ s.reg.hi p + s.reg.buffer →
      ∀ (urow : ℝ → ComplexCellL2) (srow : ℝ → TorusHk 1 ℂ),
      IsRevCurve s.H s.V s.hb' (-σ) (-r) urow srow → urow (-σ) = cellConstantCLM 1 →
      (∀ τ ∈ Icc (-σ) (-r), cellTransverseProjection (s.reg.orient p) (urow τ) = urow τ) →
      ∃ w : TorusHk j ℂ, torusHkValueCLM w =
          cellScalarCLM (s.E σ) (urow (-r)) - cellConstantCLM (s.E r) ∧
        ‖w‖ ≤ C * fibreNorm s.ξ * ‖s.E r‖)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ r ∈ Icc s.a s.b, s.SlowBound j M r) {r : ℝ}
    (hr : r ∈ Icc s.a s.b) (p : Fin s.reg.P)
    (hrp : r ∈ Icc (s.reg.lo p - s.reg.buffer) (s.reg.hi p + s.reg.buffer / 2))
    (hhalf : Cr * peFactor s.η ^ Q * Real.exp (-(1 / 4) * s.reg.buffer) ≤ 1 / 2)
    (hcase : s.reg.hi p + s.reg.buffer ≤ s.b) :
    s.SlowBound j (C * fibreNorm s.ξ + M / 2) r := by
  have hD := s.pkg.buffer_nonneg
  have hE0 := norm_nonneg (s.E r)
  have hPe0 : 0 ≤ peFactor s.η ^ Q := (zero_le_one.trans (one_le_pow₀ (AVRegularity.CycleWords.Assembly.one_le_peFactor s.η)))
  set σ := s.reg.hi p + s.reg.buffer with hσ
  have hrσ : r ≤ σ := by linarith [hrp.2]
  obtain ⟨urow, srow, hcurve, h1, htr⟩ := sharpSlowD_row s p (r := r) (σ := σ) hrp.1 hrσ le_rfl
  obtain ⟨w₀, hw₀, hn₀⟩ := hb σ ⟨hr.1.trans hrσ, hcase⟩
  obtain ⟨w₁, hw₁, hn₁⟩ := hrem hr.1 hrσ hcase urow srow hcurve h1 w₀ hw₀
  obtain ⟨wr, hwr, hnr⟩ := hrowK p hr.1 hrp.1 hrσ hcase le_rfl urow srow hcurve h1 htr
  refine ⟨torusHkConj wr - torusHkConj w₁, ?_, ?_⟩
  · rw [map_sub, torusHkConj_value, torusHkConj_value, hwr, hw₁]
    unfold SharpSlowSetting.q
    simp only [map_sub, cellFiberConj_constant]
    abel
  · have hg := sharpSlowQ_E_growth s hrσ hcase
    have hd : s.reg.buffer / 2 ≤ σ - r := by linarith [hrp.2]
    have hexp : Real.exp (-(Real.pi ^ 2 / 8) * (σ - r)) *
        Real.exp (Real.pi ^ 2 / 16 * (σ - r)) ≤ Real.exp (-(1 / 4) * s.reg.buffer) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hp2 : (8 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
      exact sharpSlow_gap_exponent hp2 hD hd
    have hpos := Real.exp_pos (-(Real.pi ^ 2 / 8) * (σ - r))
    have hfast : ‖w₁‖ ≤ Cr * peFactor s.η ^ Q * Real.exp (-(1 / 4) * s.reg.buffer) * M *
        ‖s.E r‖ := by
      calc ‖w₁‖ ≤ Cr * peFactor s.η ^ Q * Real.exp (-(Real.pi ^ 2 / 8) * (σ - r)) * ‖w₀‖ := hn₁
        _ ≤ Cr * peFactor s.η ^ Q * Real.exp (-(Real.pi ^ 2 / 8) * (σ - r)) *
            (M * ‖s.E σ‖) := by gcongr
        _ ≤ Cr * peFactor s.η ^ Q * Real.exp (-(Real.pi ^ 2 / 8) * (σ - r)) *
            (M * (Real.exp (Real.pi ^ 2 / 16 * (σ - r)) * ‖s.E r‖)) := by gcongr
        _ = Cr * peFactor s.η ^ Q * M * (Real.exp (-(Real.pi ^ 2 / 8) * (σ - r)) *
            Real.exp (Real.pi ^ 2 / 16 * (σ - r))) * ‖s.E r‖ := by ring
        _ ≤ Cr * peFactor s.η ^ Q * M * Real.exp (-(1 / 4) * s.reg.buffer) * ‖s.E r‖ := by
            gcongr
        _ = _ := by ring
    have hhalf : Cr * peFactor s.η ^ Q * Real.exp (-(1 / 4) * s.reg.buffer) ≤ 1 / 2 := by
      have hx : 0 ≤ peFactor s.η ^ Q * Real.exp (-(1 / 4) * s.reg.buffer) := by positivity
      nlinarith
    calc ‖torusHkConj wr - torusHkConj w₁‖ ≤ ‖torusHkConj wr‖ + ‖torusHkConj w₁‖ :=
          norm_sub_le _ _
      _ = ‖wr‖ + ‖w₁‖ := by rw [torusHkConj_norm, torusHkConj_norm]
      _ ≤ C * fibreNorm s.ξ * ‖s.E r‖ + (Cr * peFactor s.η ^ Q *
          Real.exp (-(1 / 4) * s.reg.buffer) * M * ‖s.E r‖) := add_le_add hnr hfast
      _ ≤ (C * fibreNorm s.ξ + M / 2) * ‖s.E r‖ := by
          have := mul_le_mul_of_nonneg_right hhalf (mul_nonneg hM hE0)
          nlinarith

/-- Window step, case `b < hi_p + D`. -/
theorem sharpSlowW_b (s : SharpSlowSetting K ρ) (j : ℕ) (C Cr : ℝ) (Q : ℕ)
    (hrem : ∀ {r σ : ℝ}, s.a ≤ r → r ≤ σ → σ ≤ s.b →
      ∀ (urow : ℝ → ComplexCellL2) (srow : ℝ → TorusHk 1 ℂ),
      IsRevCurve s.H s.V s.hb' (-σ) (-r) urow srow → urow (-σ) = cellConstantCLM 1 →
      ∀ w₀ : TorusHk j ℂ, torusHkValueCLM w₀ = s.q σ - cellConstantCLM (star (s.E σ)) →
      ∃ w₁ : TorusHk j ℂ, torusHkValueCLM w₁ = cellScalarCLM (s.E σ) (urow (-r)) - s.u (-r) ∧
        ‖w₁‖ ≤ Cr * peFactor s.η ^ Q * Real.exp (-(Real.pi ^ 2 / 8) * (σ - r)) * ‖w₀‖)
    (hrowK : ∀ (p : Fin s.reg.P) {r σ : ℝ}, s.a ≤ r →
      s.reg.lo p - s.reg.buffer ≤ r → r ≤ σ → σ ≤ s.b → σ ≤ s.reg.hi p + s.reg.buffer →
      ∀ (urow : ℝ → ComplexCellL2) (srow : ℝ → TorusHk 1 ℂ),
      IsRevCurve s.H s.V s.hb' (-σ) (-r) urow srow → urow (-σ) = cellConstantCLM 1 →
      (∀ τ ∈ Icc (-σ) (-r), cellTransverseProjection (s.reg.orient p) (urow τ) = urow τ) →
      ∃ w : TorusHk j ℂ, torusHkValueCLM w =
          cellScalarCLM (s.E σ) (urow (-r)) - cellConstantCLM (s.E r) ∧
        ‖w‖ ≤ C * fibreNorm s.ξ * ‖s.E r‖)
    (M : ℝ) (hM : 0 ≤ M) {r : ℝ}
    (hr : r ∈ Icc s.a s.b) (p : Fin s.reg.P)
    (hrp : r ∈ Icc (s.reg.lo p - s.reg.buffer) (s.reg.hi p + s.reg.buffer / 2))
    (hcase : s.b < s.reg.hi p + s.reg.buffer) :
    s.SlowBound j (C * fibreNorm s.ξ + M / 2) r := by
  have hD := s.pkg.buffer_nonneg
  have hE0 := norm_nonneg (s.E r)
  have hrb : r ≤ s.b := hr.2
  obtain ⟨urow, srow, hcurve, h1, htr⟩ := sharpSlowD_row s p (r := r) (σ := s.b) hrp.1 hrb
    hcase.le
  have hqb : s.q s.b = cellConstantCLM 1 := by
    unfold SharpSlowSetting.q
    rw [s.hu1, cellFiberConj_constant, star_one]
  have hEb : s.E s.b = 1 := by
    unfold SharpSlowSetting.E; simp
  obtain ⟨w₁, hw₁, hn₁⟩ := hrem hr.1 hrb le_rfl urow srow hcurve h1 (0 : TorusHk j ℂ)
    (by rw [map_zero, hqb, hEb, star_one, sub_self])
  obtain ⟨wr, hwr, hnr⟩ := hrowK p hr.1 hrp.1 hrb le_rfl hcase.le urow srow hcurve h1 htr
  rw [norm_zero, mul_zero] at hn₁
  have h0 : ‖w₁‖ = 0 := le_antisymm hn₁ (norm_nonneg _)
  refine ⟨torusHkConj wr - torusHkConj w₁, ?_, ?_⟩
  · rw [map_sub, torusHkConj_value, torusHkConj_value, hwr, hw₁]
    unfold SharpSlowSetting.q
    simp only [map_sub, cellFiberConj_constant]
    abel
  · calc ‖torusHkConj wr - torusHkConj w₁‖ ≤ ‖torusHkConj wr‖ + ‖torusHkConj w₁‖ :=
          norm_sub_le _ _
      _ = ‖wr‖ + ‖w₁‖ := by rw [torusHkConj_norm, torusHkConj_norm]
      _ ≤ (C * fibreNorm s.ξ + M / 2) * ‖s.E r‖ := by
          rw [h0, add_zero]
          have := mul_nonneg hM hE0
          nlinarith


/-- **The window step from the row step.** -/
theorem sharpSlowWindowStep_of_row (hrow : SharpSlowRowStepStatement) :
    SharpSlowWindowStepStatement := by
  intro hQ K j ρ hρ0 hρ1
  obtain ⟨Cr, Q, hCr, hrem⟩ := sharpSlowRem (K := K) j ρ
  obtain ⟨C, hC, hrowK⟩ := hrow K j ρ hρ0 hρ1
  refine ⟨C, 2 * Cr + 1, 1 / 4, Q, hC, by positivity, by norm_num, ?_⟩
  intro s hs M hM hb r hr hext
  obtain ⟨p, hrp⟩ := hext
  have hpe : 1 ≤ peFactor s.η ^ Q := one_le_pow₀ (AVRegularity.CycleWords.Assembly.one_le_peFactor s.η)
  have hj : (0 : ℝ) ≤ (s.reg.joins : ℝ) := Nat.cast_nonneg _
  have hwb : (2 * Cr + 1) * peFactor s.η ^ Q * Real.exp (-(1 / 4) * s.reg.buffer) ≤ 1 := by
    have h := hs
    unfold SharpSlowSetting.WB at h
    refine le_trans ?_ h
    have hx : 0 ≤ (2 * Cr + 1) * peFactor s.η ^ Q * Real.exp (-(1 / 4) * s.reg.buffer) := by
      positivity
    nlinarith
  have hhalf : Cr * peFactor s.η ^ Q * Real.exp (-(1 / 4) * s.reg.buffer) ≤ 1 / 2 := by
    have hx : 0 ≤ peFactor s.η ^ Q * Real.exp (-(1 / 4) * s.reg.buffer) := by positivity
    nlinarith
  by_cases hcase : s.reg.hi p + s.reg.buffer ≤ s.b
  · exact sharpSlowW_hi s j C Cr Q hCr (hrem s) (hrowK s) M hM hb hr p hrp hhalf hcase
  · exact sharpSlowW_b s j C Cr Q (hrem s) (hrowK s) M hM hr p hrp (not_le.1 hcase)

/-- **Step W-window from the row step.** -/
theorem sharpSlowTest_of_row (hQ : QuietHsDecayStatement) (hrow : SharpSlowRowStepStatement) :
    SharpSlowTestStatement :=
  sharpSlowTest_of_cases hQ sharpSlowQuietStep (sharpSlowWindowStep_of_row hrow) sharpSlowDefect

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # The two cases where the weight at `s` exceeds `1`

Both lemmas take estimate (a) (`hPl`, the plain decay at the level `Λ₁`) and the surplus decay
(`hSd`) instantiated at the setting.

* `wsd_case_one`: every activity of `(s, t]` has the orientation `e(s)`. Then `e(t) = e(s)`, and
  the drift is invariant along `e(s)` on `[s, t]`. Split the datum as in 29a:
  - `A = U_T + P U_N − κ·1` is actual-fast and transverse, so `u_A` stays transverse
    (`revCurve_transverse_cut`), and estimate (a) bounds it;
  - `B = (1 − P) U_N + κ·1` is actual-fast, and the surplus decay bounds it. The weight
    `Ω_{Λ₂}(s)` is paid by `Λ₂ P_e^{Q_S} ≤ Λ₁` (`weight_surplus_le`).
  So `V_T = w_A`, `V_N = w_B`.
* `wsd_case_two`: an activity of the other orientation in `(s, t]`. At the crossing point `γ`
  (`crossing_point`), estimate (a) bounds `u(−γ)`, which is still actual-fast
  (`revCurve_pairing`). The surplus decay on `[s, γ]` has lag `≥ D/4`, and
  `Λ₂ P_e^{Q_S} e^{-(3π²/8)(D/4)} ≤ 1` pays the weight. So `V_T = 0`, `V_N = w_s`. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin

namespace AVRegularity.CycleWords.Assembly

variable {K : ScalarConstants} {η : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {v : ℝ → Vec 2 → Vec 2} {ξ : Fin 2 → ℂ} {t₀ S ϖ : ℝ} {reg : BlockRegions} {j : ℕ}

/-- **Case 1 of 29b.** -/
theorem wsd_case_one (pkg : CoreScalarPackage K η G v t₀ S ϖ reg)
    (H : TransverseLocalHyp K η G v ξ) (V : ℝ) (hb' : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2)
    {CP CS Λ₁ Λ₂ : ℝ} {QS : ℕ} (hCP : 0 ≤ CP) (hCS : 0 ≤ CS)
    (hPl : ∀ {s t : ℝ}, t₀ ≤ s → s ≤ t → t ≤ t₀ + S →
      ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ), IsRevCurve H V hb' (-t) (-s) u slice →
        cellComplexPair (cellRawTrace (fibreSeriesJet pkg.actual.r ξ) t + cellConstantCLM 1)
          (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u (-t))) = 0 →
      ∀ UT UN : TorusHk j ℂ, torusHkValueCLM (UT + UN) = u (-t) →
        cellTransverseProjection (activityOrient reg v t₀ t) (torusHkValueCLM UT) =
          torusHkValueCLM UT →
        ∃ w : TorusHk j ℂ, torusHkValueCLM w = u (-s) ∧
          ‖w‖ ≤ CP * Real.exp (-(Real.pi ^ 2 / 8) * (t - s)) *
            (‖UT‖ + activityWeight v t₀ Λ₁ (3 * Real.pi ^ 2 / 8) t * ‖UN‖))
    (hSd : ∀ {s t : ℝ}, t₀ ≤ s → s ≤ t → t ≤ t₀ + S →
      ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ), IsRevCurve H V hb' (-t) (-s) u slice →
        cellComplexPair (cellRawTrace (fibreSeriesJet pkg.actual.r ξ) t + cellConstantCLM 1)
          (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u (-t))) = 0 →
      ∀ w₀ : TorusHk j ℂ, torusHkValueCLM w₀ = u (-t) →
        ∃ w : TorusHk j ℂ, torusHkValueCLM w = u (-s) ∧
          ‖w‖ ≤ CS * peFactor η ^ QS * Real.exp (-(3 * Real.pi ^ 2 / 8) * quietLag v t₀ s t) *
            Real.exp (-(Real.pi ^ 2 / 8) * (t - s)) * ‖w₀‖)
    {s t : ℝ} (hs : t₀ ≤ s) (hst : s ≤ t) (ht : t ≤ t₀ + S) (hD : 0 < reg.buffer)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ) (hu : IsRevCurve H V hb' (-t) (-s) u slice)
    (hfast : cellComplexPair (cellRawTrace (fibreSeriesJet pkg.actual.r ξ) t + cellConstantCLM 1)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u (-t))) = 0)
    (UT UN : TorusHk j ℂ) (hsum : torusHkValueCLM (UT + UN) = u (-t))
    (htr : cellTransverseProjection (activityOrient reg v t₀ t) (torusHkValueCLM UT) =
      torusHkValueCLM UT)
    (hΩ : 1 < activityWeight v t₀ Λ₂ (3 * Real.pi ^ 2 / 8) s)
    (hΛ : Λ₂ * peFactor η ^ QS ≤ Λ₁)
    (hcase : ∀ τ ∈ Ioc s t, ∀ e', IsOrientedActive reg v τ e' →
      e' = activityOrient reg v t₀ s) :
    ∃ VT VN : TorusHk j ℂ, torusHkValueCLM (VT + VN) = u (-s) ∧
      cellTransverseProjection (activityOrient reg v t₀ s) (torusHkValueCLM VT) =
        torusHkValueCLM VT ∧
      ‖VT‖ + activityWeight v t₀ Λ₂ (3 * Real.pi ^ 2 / 8) s * ‖VN‖ ≤
        (5 * CP + 6 * CS) * Real.exp (-(Real.pi ^ 2 / 8) * (t - s)) *
          (‖UT‖ + activityWeight v t₀ Λ₁ (3 * Real.pi ^ 2 / 8) t * ‖UN‖) := by
  have hnes := activeSet_nonempty_of_weight hΩ
  have he : activityOrient reg v t₀ t = activityOrient reg v t₀ s :=
    same_orient_eq pkg hst ht hD hnes hcase
  have hinv := same_orient_invariant pkg hs hst ht hD hcase
  rw [he] at htr
  obtain ⟨P, hPv, hPn⟩ := transverseHsProjection (activityOrient reg v t₀ s) j
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
  have hAtr : cellTransverseProjection (activityOrient reg v t₀ s) (torusHkValueCLM AH) =
      torusHkValueCLM AH := by
    rw [hAv]
    apply wpd_transverse_sub_const
    rw [map_add, htr, hPv UN, AVRegularity.CycleWords.cellTransverseProjection_idempotent]
  have htrA := revCurve_transverse_cut H V hb' _ hst hinv huA (by rw [hA0]; exact hAtr)
  obtain ⟨wA, hwA, hnA⟩ := hPl hs hst ht uA sA huA hfastA AH 0 (by rw [add_zero, hA0])
    (by rw [he]; exact hAtr)
  have hBv : torusHkValueCLM BH = uB (-t) := by
    rw [hB0, ← hsum]
    exact eq_sub_of_add_eq' hABsum
  obtain ⟨wB, hwB, hnB⟩ := hSd hs hst ht uB sB huB hfastB BH hBv
  refine ⟨wA, wB, ?_, ?_, ?_⟩
  · rw [map_add, hwA, hwB]
    exact hAB (-s)
  · rw [hwA]
    exact htrA (-s) ⟨by linarith, le_rfl⟩
  · have hws := weight_surplus_le (v := v) (t₀ := t₀) (Λ₁ := Λ₁) (Λ₂ := Λ₂) (Q := QS)
      (c := 3 * Real.pi ^ 2 / 8) (P := peFactor η) (by positivity)
      (zero_le_one.trans (wpd_one_le_pe η)) hst hΩ hΛ
    rw [norm_zero, mul_zero, add_zero] at hnA
    have hb : ‖wB‖ ≤ CS * (peFactor η ^ QS *
        Real.exp (-(3 * Real.pi ^ 2 / 8) * quietLag v t₀ s t)) *
        Real.exp (-(Real.pi ^ 2 / 8) * (t - s)) * ‖BH‖ := hnB.trans_eq (by ring)
    exact alg_case_one hCP hCS (Real.exp_pos _).le (norm_nonneg _) (norm_nonneg _)
      (one_le_activityWeight _ _ _ _ _) (zero_le_one.trans (one_le_activityWeight _ _ _ _ _))
      hnA hAn hb hBn (norm_nonneg _) hws

/-- **Case 2 of 29b: the crossing.** -/
theorem wsd_case_two (pkg : CoreScalarPackage K η G v t₀ S ϖ reg)
    (H : TransverseLocalHyp K η G v ξ) (V : ℝ) (hb' : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2)
    {CP CS Λ₁ Λ₂ : ℝ} {QS : ℕ} (hCS : 0 ≤ CS)
    (hPl : ∀ {s t : ℝ}, t₀ ≤ s → s ≤ t → t ≤ t₀ + S →
      ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ), IsRevCurve H V hb' (-t) (-s) u slice →
        cellComplexPair (cellRawTrace (fibreSeriesJet pkg.actual.r ξ) t + cellConstantCLM 1)
          (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u (-t))) = 0 →
      ∀ UT UN : TorusHk j ℂ, torusHkValueCLM (UT + UN) = u (-t) →
        cellTransverseProjection (activityOrient reg v t₀ t) (torusHkValueCLM UT) =
          torusHkValueCLM UT →
        ∃ w : TorusHk j ℂ, torusHkValueCLM w = u (-s) ∧
          ‖w‖ ≤ CP * Real.exp (-(Real.pi ^ 2 / 8) * (t - s)) *
            (‖UT‖ + activityWeight v t₀ Λ₁ (3 * Real.pi ^ 2 / 8) t * ‖UN‖))
    (hSd : ∀ {s t : ℝ}, t₀ ≤ s → s ≤ t → t ≤ t₀ + S →
      ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ), IsRevCurve H V hb' (-t) (-s) u slice →
        cellComplexPair (cellRawTrace (fibreSeriesJet pkg.actual.r ξ) t + cellConstantCLM 1)
          (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u (-t))) = 0 →
      ∀ w₀ : TorusHk j ℂ, torusHkValueCLM w₀ = u (-t) →
        ∃ w : TorusHk j ℂ, torusHkValueCLM w = u (-s) ∧
          ‖w‖ ≤ CS * peFactor η ^ QS * Real.exp (-(3 * Real.pi ^ 2 / 8) * quietLag v t₀ s t) *
            Real.exp (-(Real.pi ^ 2 / 8) * (t - s)) * ‖w₀‖)
    {s t : ℝ} (hs : t₀ ≤ s) (hst : s ≤ t) (ht : t ≤ t₀ + S)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ) (hu : IsRevCurve H V hb' (-t) (-s) u slice)
    (hfast : cellComplexPair (cellRawTrace (fibreSeriesJet pkg.actual.r ξ) t + cellConstantCLM 1)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u (-t))) = 0)
    (UT UN : TorusHk j ℂ) (hsum : torusHkValueCLM (UT + UN) = u (-t))
    (htr : cellTransverseProjection (activityOrient reg v t₀ t) (torusHkValueCLM UT) =
      torusHkValueCLM UT)
    (hΛ2 : 1 ≤ Λ₂) (hΩ : 1 < activityWeight v t₀ Λ₂ (3 * Real.pi ^ 2 / 8) s)
    (hhalf : Λ₂ * Real.exp (-(3 * Real.pi ^ 2 / 8) * (reg.buffer / 2)) ≤ 1)
    (hquarter : Λ₂ * peFactor η ^ QS * Real.exp (-(3 * Real.pi ^ 2 / 8) * (reg.buffer / 4)) ≤ 1)
    {τ' : ℝ} {e' : Fin 2} (hτ' : τ' ∈ Ioc s t) (hor : IsOrientedActive reg v τ' e')
    (hne : e' ≠ activityOrient reg v t₀ s) :
    ∃ VT VN : TorusHk j ℂ, torusHkValueCLM (VT + VN) = u (-s) ∧
      cellTransverseProjection (activityOrient reg v t₀ s) (torusHkValueCLM VT) =
        torusHkValueCLM VT ∧
      ‖VT‖ + activityWeight v t₀ Λ₂ (3 * Real.pi ^ 2 / 8) s * ‖VN‖ ≤
        2 * CS * CP * Real.exp (-(Real.pi ^ 2 / 8) * (t - s)) *
          (‖UT‖ + activityWeight v t₀ Λ₁ (3 * Real.pi ^ 2 / 8) t * ‖UN‖) := by
  have hc : (0 : ℝ) < 3 * Real.pi ^ 2 / 8 := by positivity
  have hD := pkg.buffer_nonneg
  obtain ⟨γ, hγ, hγs, hgap⟩ := crossing_point pkg hc hhalf hst ht hΩ hτ' hor hne
  have huγ : IsRevCurve H V hb' (-t) (-γ) u slice :=
    CellWeakHilbertCurve.mono hu (Icc_subset_Icc le_rfl (by linarith [hγ.1]))
  have huγs : IsRevCurve H V hb' (-γ) (-s) u slice :=
    CellWeakHilbertCurve.mono hu (Icc_subset_Icc (by linarith [hγ.2]) le_rfl)
  obtain ⟨wγ, hwγ, hnγ⟩ := hPl (hs.trans hγ.1) hγ.2 ht u slice huγ hfast UT UN hsum htr
  have hfastγ : cellComplexPair (cellRawTrace (fibreSeriesJet pkg.actual.r ξ) γ +
      cellConstantCLM 1) (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u (-γ))) = 0 := by
    rw [revCurve_pairing H.hη0 H.hη H.hCg H.hCw H.hG H.hv H.hm H.hw pkg.actual ξ H.hξ V hb' hu
      γ hγ, hfast, mul_zero]
  obtain ⟨ws, hws, hns⟩ := hSd hs hγ.1 (hγ.2.trans ht) u slice huγs hfastγ wγ hwγ
  have hlag : reg.buffer / 4 ≤ quietLag v t₀ s γ :=
    quietLag_ge_of_gap hγs (by linarith) (hγ.2.trans ht) hgap
  have hreg : Λ₂ * peFactor η ^ QS *
      Real.exp (-(3 * Real.pi ^ 2 / 8) * quietLag v t₀ s γ) ≤ 1 :=
    le_trans (mul_le_mul_of_nonneg_left (exp_neg_mul_le hc.le hlag)
      (mul_nonneg (by linarith) (pow_nonneg (zero_le_one.trans (wpd_one_le_pe η)) _))) hquarter
  have hΩle : activityWeight v t₀ Λ₂ (3 * Real.pi ^ 2 / 8) s ≤ Λ₂ := activityWeight_le hΛ2 hc.le
  have hcross := alg_cross hΩle (zero_le_one.trans (one_le_activityWeight _ _ _ _ _)) hCS
    (pow_nonneg (zero_le_one.trans (wpd_one_le_pe η)) _) (Real.exp_pos _).le (Real.exp_pos _).le
    (show ‖ws‖ ≤ 2 * ‖ws‖ by linarith [norm_nonneg ws]) hns hnγ (norm_nonneg _) hreg
  rw [exp_split] at hcross
  refine ⟨0, ws, by rw [zero_add]; exact hws, by rw [map_zero, map_zero], ?_⟩
  rw [norm_zero, zero_add]
  exact hcross

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # The weighted sharp decay

`weightedSharpDecay (hQ) (ha) : WeightedSharpDecayStatement`, from estimate (a) (`ha`) and the
surplus decay (`surplusDecay hQ`). Three cases at `s`:
* `Ω_{Λ₂}(s) = 1`: estimate (a), with `V_T = 0`;
* `Ω_{Λ₂}(s) > 1`, and every activity of `(s, t]` has the orientation `e(s)`: `wsd_case_one`;
* `Ω_{Λ₂}(s) > 1`, with an activity of the other orientation in `(s, t]`: `wsd_case_two`.

Constants, with `(C_P, C_{b,P}, c_{b,P}, Q_P, Q_P')` of estimate (a) and `(C_S, Q_S)` of the
surplus decay: `C = 5C_P + 6C_S + 2C_S C_P`, `C_b = max C_{b,P} 1`,
`c_b = min c_{b,P} (3π²/32)`, `Q = Q_P`, `Q′ = max Q_S Q_P′`. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin

namespace AVRegularity.CycleWords.Assembly

/-- The constant `C` dominates the three cases. -/
theorem wsd_const {CP CS : ℝ} (hCP : 1 ≤ CP) (hCS : 1 ≤ CS) :
    1 ≤ 5 * CP + 6 * CS + 2 * CS * CP ∧ CP ≤ 5 * CP + 6 * CS + 2 * CS * CP ∧
      5 * CP + 6 * CS ≤ 5 * CP + 6 * CS + 2 * CS * CP ∧
      2 * CS * CP ≤ 5 * CP + 6 * CS + 2 * CS * CP := by
  have h := mul_nonneg (by linarith : (0 : ℝ) ≤ CS) (by linarith : (0 : ℝ) ≤ CP)
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem wsd_rate_le : 3 * Real.pi ^ 2 / 32 ≤ 3 * Real.pi ^ 2 / 16 := by
  have := sq_nonneg Real.pi
  linarith

/-- **The weighted sharp decay.** -/
theorem weightedSharpDecay (hQ : QuietHsDecayStatement) (ha : WeightedPlainDecayStatement) :
    WeightedSharpDecayStatement := by
  intro K j ρ hρ0 hρ1
  obtain ⟨CP, CbP, cbP, QP, QP', hCP, hcbP, hPl⟩ := ha K j ρ hρ0 hρ1
  obtain ⟨CS, QS, hCS, hS⟩ := surplusDecay hQ K j ρ hρ0 hρ1
  obtain ⟨hC1, hCa, hCb, hCc⟩ := wsd_const hCP hCS
  refine ⟨5 * CP + 6 * CS + 2 * CS * CP, max CbP 1, min cbP (3 * Real.pi ^ 2 / 32), QP,
    max QS QP', hC1, lt_min hcbP (by positivity), ?_⟩
  intro η t₀ S ϖ G v g reg pkg hη hvs hvj hg0 hg1 hmet ξ H hξ Λ₁ Λ₂ hΛ2 hΛ hreg V hb' s t hs
    hst ht u slice hu hfast UT UN hsum htr
  have hP1 := wpd_one_le_pe η
  have hP0 : (0 : ℝ) ≤ peFactor η := zero_le_one.trans hP1
  have hD := pkg.buffer_nonneg
  have hJ : (1 : ℝ) ≤ 1 + (reg.joins : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) reg.joins
    linarith
  -- the level drop
  have hΛS : Λ₂ * peFactor η ^ QS ≤ Λ₁ :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hP1 (le_max_left _ _)) (by linarith)).trans hΛ
  have hΛP : peFactor η ^ QP' ≤ Λ₁ :=
    (pow_le_pow_right₀ hP1 (le_max_right _ _)).trans
      ((le_mul_of_one_le_left (pow_nonneg hP0 _) hΛ2).trans hΛ)
  have hΛ12 : Λ₂ ≤ Λ₁ := (le_mul_of_one_le_right (by linarith) (one_le_pow₀ hP1)).trans hΛ
  have hΛ1 : 0 ≤ Λ₁ := by linarith
  -- the regimes
  have hregP : CbP * Λ₁ * (1 + (reg.joins : ℝ)) * peFactor η ^ QP *
      Real.exp (-cbP * reg.buffer) ≤ 1 :=
    regime_mono (le_max_left _ _) (min_le_left _ _) le_rfl hΛ1 (by linarith) hP1 hD hreg
  have hhalf : Λ₂ * Real.exp (-(3 * Real.pi ^ 2 / 8) * (reg.buffer / 2)) ≤ 1 :=
    regime_half (le_max_right _ _) hΛ12 hΛ1 hJ hP1 hD ((min_le_right _ _).trans wsd_rate_le) hreg
  have hquarter : Λ₂ * peFactor η ^ QS *
      Real.exp (-(3 * Real.pi ^ 2 / 8) * (reg.buffer / 4)) ≤ 1 :=
    regime_quarter (le_max_right _ _) (by linarith) hΛS hJ hP1 hD (min_le_right _ _) hreg
  -- the two estimates at the setting
  have hPlS := @hPl η t₀ S ϖ G v g reg pkg hη hvs hvj hg0 hg1 hmet ξ H hξ Λ₁ hΛP hregP V hb'
  have hSS := @hS η t₀ S ϖ G v g reg pkg hη hvs hvj hg0 hg1 hmet ξ H hξ V hb'
  have hE : 0 ≤ Real.exp (-(Real.pi ^ 2 / 8) * (t - s)) := (Real.exp_pos _).le
  have hR : 0 ≤ ‖UT‖ + activityWeight v t₀ Λ₁ (3 * Real.pi ^ 2 / 8) t * ‖UN‖ :=
    add_nonneg (norm_nonneg _)
      (mul_nonneg (zero_le_one.trans (one_le_activityWeight _ _ _ _ _)) (norm_nonneg _))
  by_cases hΩ : 1 < activityWeight v t₀ Λ₂ (3 * Real.pi ^ 2 / 8) s
  swap
  · -- weight one at `s`: estimate (a)
    have hΩ1 : activityWeight v t₀ Λ₂ (3 * Real.pi ^ 2 / 8) s = 1 :=
      le_antisymm (not_lt.1 hΩ) (one_le_activityWeight _ _ _ _ _)
    obtain ⟨w, hw, hn⟩ := hPlS hs hst ht u slice hu hfast UT UN hsum htr
    refine ⟨0, w, by rw [zero_add]; exact hw, by rw [map_zero, map_zero], ?_⟩
    rw [hΩ1, norm_zero, zero_add, one_mul]
    exact le_const_mul hn hCa hE hR
  have hc : (0 : ℝ) < 3 * Real.pi ^ 2 / 8 := by positivity
  obtain ⟨-, hDpos, -⟩ := weight_close (reg := reg) hc hhalf hΩ
  by_cases hcase : ∀ τ ∈ Ioc s t, ∀ e', IsOrientedActive reg v τ e' →
      e' = activityOrient reg v t₀ s
  · obtain ⟨VT, VN, h1, h2, h3⟩ := wsd_case_one pkg H V hb' (by linarith) (by linarith) hPlS
      hSS hs hst ht hDpos u slice hu hfast UT UN hsum htr hΩ hΛS hcase
    exact ⟨VT, VN, h1, h2, le_const_mul h3 hCb hE hR⟩
  · push Not at hcase
    obtain ⟨τ', hτ', e', hor, hne⟩ := hcase
    obtain ⟨VT, VN, h1, h2, h3⟩ := wsd_case_two pkg H V hb' (by linarith) hPlS hSS hs hst ht u
      slice hu hfast UT UN hsum htr hΛ2 hΩ hhalf hquarter hτ' hor hne
    exact ⟨VT, VN, h1, h2, le_const_mul h3 hCc hE hR⟩

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # The sharp slow test: the row step and the slow test

`E(σ) = exp(-∫_r^σ λ_act)·E(r)`, so the row step is the normalized actual row in `H^j`
(`sharpSlowRowHj`) multiplied by `E(r)`. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords

namespace AVRegularity.CycleWords.Assembly

variable {K : ScalarConstants} {ρ : ℝ}

/-- `E(σ) = exp(-∫_r^σ λ_act)·E(r)`. -/
theorem sharpSlowE_split (s : SharpSlowSetting K ρ) {r σ : ℝ} (hrσ : r ≤ σ) (hσ : σ ≤ s.b) :
    s.E σ = Complex.exp (-∫ τ in r..σ, fibreSeriesC s.pkg.actual.lam s.ξ τ) * s.E r := by
  have hint : ∀ c d, c ≤ d →
      IntervalIntegrable (fun τ => fibreSeriesC s.pkg.actual.lam s.ξ τ) volume c d :=
    fun c d h => (intervalIntegrable_iff_integrableOn_Icc_of_le h).mpr
      ((fibreGraph_symbol_memLp_top s.pkg.actual.graph s.H.hη0 s.H.hη s.H.hCw s.H.hG s.H.hv
        s.H.hw s.ξ s.H.hξ s.H.hCg c d).integrable le_top)
  have hsplit : s.E r = Complex.exp (∫ t in r..σ, fibreSeriesC s.pkg.actual.lam s.ξ t) *
      s.E σ := by
    unfold SharpSlowSetting.E
    rw [← Complex.exp_add, ← intervalIntegral.integral_add_adjacent_intervals (hint r σ hrσ)
      (hint σ s.b hσ)]
  rw [hsplit, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]

/-- **The row step** (`SharpSlowRowStepStatement`). -/
theorem sharpSlowRowStep : SharpSlowRowStepStatement := by
  intro K j ρ _ _
  by_cases hρ : 0 ≤ ρ
  swap
  · refine ⟨0, le_rfl, ?_⟩
    intro s
    exact absurd (s.hξρ.trans_lt (not_le.1 hρ)) (not_lt.2 (fibreNorm_nonneg s.ξ))
  obtain ⟨C, hC, hrow⟩ := sharpSlowRowHj K j ρ hρ
  refine ⟨C, hC, ?_⟩
  intro s p r σ _ hlo hrσ hσb hhi urow srow hu h1 htr
  obtain ⟨W, hWv, hWn⟩ := hrow s p hlo hrσ hhi urow srow hu h1 htr
  refine ⟨torusHigherScalarCLM j (s.E r) W, ?_, ?_⟩
  · rw [torusHigherScalarCLM_value, hWv, map_sub, cellScalarCLM_constant_one,
      sharpSlowE_split s hrσ hσb]
    simp only [cellScalarCLM_smul, smul_smul, mul_comm]
  · rw [torusHigherScalarCLM_norm]
    calc ‖s.E r‖ * ‖W‖ ≤ ‖s.E r‖ * (C * fibreNorm s.ξ) :=
          mul_le_mul_of_nonneg_left hWn (norm_nonneg _)
      _ = C * fibreNorm s.ξ * ‖s.E r‖ := by ring

/-- **The sharp slow test.** -/
theorem sharpSlowTest : SharpSlowTestStatement :=
  sharpSlowTest_of_row quietHsDecay sharpSlowRowStep

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # bounded maps on `TorusHk` for the stage transforms

The twisted derivative `∂_k + iθ_k : H^{K+1} → H^K` and the multiplication by a real smooth
periodic coefficient `c : H^K → H^K`, as real-linear bounded maps with their classical values. They
are the building blocks of the same-level and letter operators.  A classical `C¹`
representative of the argument suffices for the value of one derivative: the value is read on the
truncation to `H¹`. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
  AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Variational

namespace AVRegularity.CycleWords.Assembly

/-- Truncation does not change the value. -/
theorem torusHkValueCLM_truncate {K L : ℕ} (h : K ≤ L) (U : TorusHk L ℂ) :
    torusHkValueCLM (truncateTorusHk h U) = torusHkValueCLM U := by
  rfl

/-- The one-step derivative `∂_k : H^{K+1} → H^K`. -/
def tbDeriv (K : ℕ) (k : Fin 2) : TorusHk (K + 1) ℂ →L[ℝ] TorusHk K ℂ :=
  derivativeTorusHk (K := K) (r := 1) (fun _ => k)

/-- The truncation `H^{K+1} → H^K`. -/
def tbTrunc (K : ℕ) : TorusHk (K + 1) ℂ →L[ℝ] TorusHk K ℂ :=
  truncateTorusHk (Nat.le_succ K)

/-- The twisted derivative `∂_k + iθ_k`. -/
def tbTwist (K : ℕ) (θ : Vec 2) (k : Fin 2) : TorusHk (K + 1) ℂ →L[ℝ] TorusHk K ℂ :=
  tbDeriv K k + (torusHigherScalarCLM K (Complex.I * (θ k : ℂ))).comp (tbTrunc K)

theorem tbTwist_norm_le (K : ℕ) (θ : Vec 2) (k : Fin 2) : ‖tbTwist K θ k‖ ≤ 1 + |θ k| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun U => ?_
  have h1 : ‖tbDeriv K k U‖ ≤ ‖U‖ :=
    derivativeTorusHk_norm_le (K := K) (r := 1) (fun _ => k) U
  have h2 : ‖(torusHigherScalarCLM K (Complex.I * (θ k : ℂ))).comp (tbTrunc K) U‖ ≤
      |θ k| * ‖U‖ := by
    change ‖torusHigherScalarCLM K (Complex.I * (θ k : ℂ)) (tbTrunc K U)‖ ≤ _
    rw [torusHigherScalarCLM_norm]
    have : ‖Complex.I * (θ k : ℂ)‖ = |θ k| := by simp
    rw [this]
    exact mul_le_mul_of_nonneg_left
      (truncateTorusHk_norm_le (Nat.le_succ K) U) (abs_nonneg _)
  calc ‖tbTwist K θ k U‖ ≤ ‖tbDeriv K k U‖ + ‖(torusHigherScalarCLM K
        (Complex.I * (θ k : ℂ))).comp (tbTrunc K) U‖ := norm_add_le _ _
    _ ≤ (1 + |θ k|) * ‖U‖ := by linarith

/-- The value of the derivative of a class with a `C¹` representative. -/
theorem tbDeriv_value_ae (K : ℕ) (k : Fin 2) (U : TorusHk (K + 1) ℂ) (f : Vec 2 → ℂ)
    (hf : ContDiff ℝ 1 f)
    (hv : (torusHkValueCLM U : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] f) :
    (torusHkValueCLM (tbDeriv K k U) : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => fderiv ℝ f x (basisVec k) := by
  have h := cellDerivativeCLM_ae_of_smooth (truncateTorusHk (Nat.succ_le_succ (Nat.zero_le K)) U)
    f hf hv k
  have he : torusHkValueCLM (tbDeriv K k U) =
      cellDerivativeCLM k (truncateTorusHk (Nat.succ_le_succ (Nat.zero_le K)) U) := by
    have hidx : prefixJetIndex (K := K) (r := 1) (fun _ => k) (valueIndex2 K) =
        truncateJetIndex (Nat.succ_le_succ (Nat.zero_le K)) ⟨⟨1, by decide⟩, fun _ => k⟩ := by
      unfold prefixJetIndex truncateJetIndex valueIndex2 valueIndex
      simp
    change U.val (prefixJetIndex (K := K) (r := 1) (fun _ => k) (valueIndex2 K)) =
      U.val (truncateJetIndex (Nat.succ_le_succ (Nat.zero_le K))
        ⟨⟨1, by decide⟩, fun _ => k⟩)
    rw [hidx]
  rw [he]
  exact h

/-- The value of the twisted derivative of a class with a `C¹` representative. -/
theorem tbTwist_value_ae (K : ℕ) (θ : Vec 2) (k : Fin 2) (U : TorusHk (K + 1) ℂ)
    (f : Vec 2 → ℂ) (hf : ContDiff ℝ 1 f)
    (hv : (torusHkValueCLM U : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] f) :
    (torusHkValueCLM (tbTwist K θ k U) : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fibreCovDeriv θ k f := by
  have h1 := tbDeriv_value_ae K k U f hf hv
  have h2 := cellScalarCLM_ae (Complex.I * (θ k : ℂ)) (torusHkValueCLM (tbTrunc K U))
  have h3 := Lp.coeFn_add (torusHkValueCLM (tbDeriv K k U))
    (cellScalarCLM (Complex.I * (θ k : ℂ)) (torusHkValueCLM (tbTrunc K U)))
  have hvt : (torusHkValueCLM (tbTrunc K U) : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] f :=
    hv
  have he : torusHkValueCLM (tbTwist K θ k U) = torusHkValueCLM (tbDeriv K k U) +
      cellScalarCLM (Complex.I * (θ k : ℂ)) (torusHkValueCLM (tbTrunc K U)) := by
    change torusHkValueCLM (tbDeriv K k U +
      torusHigherScalarCLM K (Complex.I * (θ k : ℂ)) (tbTrunc K U)) = _
    rw [map_add, torusHigherScalarCLM_value]
  rw [he]
  filter_upwards [h1, h2, h3, hvt] with x e1 e2 e3 e4
  rw [e3, Pi.add_apply, e1, e2, e4]
  rfl

/-- The conjugate of the twisted derivative at `-θ` of the conjugate. -/
theorem tb_star_cov (θ : Vec 2) (k : Fin 2) (f : Vec 2 → ℂ) (z : Vec 2)
    (hf : DifferentiableAt ℝ f z) :
    star (fibreCovDeriv (-θ) k (fun y => star (f y)) z) = fibreCovDeriv θ k f z := by
  unfold fibreCovDeriv
  rw [fderiv_star_apply hf]
  simp [star_add, star_mul', Complex.conj_ofReal]

/-- Multiplication by a real smooth periodic coefficient, as a pointwise operator. -/
def tbCoeff (c : Vec 2 → ℝ) : Vec 2 → ℂ →L[ℝ] ℂ := fun x => realScalarMultiplierMap (c x)

theorem tbCoeff_contDiff {c : Vec 2 → ℝ} {K : ℕ} (hc : ContDiff ℝ (K : ℕ) c) :
    ContDiff ℝ (K : ℕ) (tbCoeff c) := realScalarMultiplierMap.contDiff.comp hc

theorem tbCoeff_periodic {c : Vec 2 → ℝ} (hp : AVenhance.IsZ2Periodic c) :
    AVenhance.IsZ2Periodic (tbCoeff c) := by
  intro k x
  unfold tbCoeff
  rw [hp k x]

theorem tbCoeff_array_bound {c : Vec 2 → ℝ} {K : ℕ} (hc : ContDiff ℝ (K : ℕ) c) {P : ℝ}
    (hP : ∀ l ≤ K, ∀ x, ‖iteratedFDeriv ℝ l c x‖ ≤ P) (l : ℕ) (hl : l ≤ K) (x : Vec 2) :
    ‖coefficientDerivativeArray (tbCoeff c) l x‖ ≤ cdrEntryJet l * P := by
  have hb := realScalarMultiplier_jet_array_bound c l (hc.of_le (by exact_mod_cast hl)) x
  exact hb.trans (by
    unfold cdrEntryJet
    exact mul_le_mul_of_nonneg_left (hP l hl x) (by positivity))

/-- The multiplier by a real coefficient with jets of order `≤ K` bounded by `P`. -/
def tbMulCLM (K : ℕ) {c : Vec 2 → ℝ} (hc : ContDiff ℝ (K : ℕ) c)
    (hp : AVenhance.IsZ2Periodic c) {P : ℝ} (hP : ∀ l ≤ K, ∀ x, ‖iteratedFDeriv ℝ l c x‖ ≤ P) :
    TorusHk K ℂ →L[ℝ] TorusHk K ℂ :=
  KernelEnergy.torusMultiplierCLM (tbCoeff c) (tbCoeff_contDiff hc) (tbCoeff_periodic hp)
    (fun l => cdrEntryJet l.val * P)
    (fun l x => tbCoeff_array_bound hc hP l.val (Nat.lt_succ_iff.mp l.2) x) 1 (by norm_num)

theorem tbMulCLM_norm_le (K : ℕ) {c : Vec 2 → ℝ} (hc : ContDiff ℝ (K : ℕ) c)
    (hp : AVenhance.IsZ2Periodic c) {P : ℝ} (hP : ∀ l ≤ K, ∀ x, ‖iteratedFDeriv ℝ l c x‖ ≤ P)
    (U : TorusHk K ℂ) : ‖tbMulCLM K hc hp hP U‖ ≤ cellDriftNativePrice K * P * ‖U‖ := by
  have h := KernelEnergy.torusMultiplier_norm_bound (tbCoeff c) (tbCoeff_contDiff hc)
    (tbCoeff_periodic hp) (fun l => cdrEntryJet l.val * P)
    (fun l x => tbCoeff_array_bound hc hP l.val (Nat.lt_succ_iff.mp l.2) x) 1 (by norm_num) U
  refine h.trans (le_of_eq ?_)
  unfold cellDriftNativePrice cdrEntryJet
  simp only [← mul_assoc, ← Finset.sum_mul]
  ring

theorem tbMulCLM_value_ae (K : ℕ) {c : Vec 2 → ℝ} (hc : ContDiff ℝ (K : ℕ) c)
    (hp : AVenhance.IsZ2Periodic c) {P : ℝ} (hP : ∀ l ≤ K, ∀ x, ‖iteratedFDeriv ℝ l c x‖ ≤ P)
    (U : TorusHk K ℂ) :
    (torusHkValueCLM (tbMulCLM K hc hp hP U) : Vec 2 → ℂ)
      =ᵐ[volume.restrict AVenhance.unitCube] fun x => (c x : ℂ) * torusHkValueCLM U x := by
  have hl := torusMulCoefficient_value_ae U (tbCoeff c) (tbCoeff_contDiff hc)
    (tbCoeff_periodic hp) (A := fun l => cdrEntryJet l.val * P)
    (fun l x => tbCoeff_array_bound hc hP l.val (Nat.lt_succ_iff.mp l.2) x)
  change (U.mulCoefficient (tbCoeff c) (tbCoeff_contDiff hc) (tbCoeff_periodic hp)
    (fun l x => tbCoeff_array_bound hc hP l.val (Nat.lt_succ_iff.mp l.2) x)).val
    (valueIndex2 K) =ᵐ[_] _
  filter_upwards [hl] with x hx
  rw [hx]
  rfl

end AVRegularity.CycleWords.Assembly
end
end
