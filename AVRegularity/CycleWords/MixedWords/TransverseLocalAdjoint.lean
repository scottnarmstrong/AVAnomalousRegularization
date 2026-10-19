-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.MixedWords.TransverseRegGrowth
import AVRegularity.CycleWords.MixedWords.ZeroAmplitudeWordStep
public import AVRegularity.CycleWords.Assembly.MixedWordsB1ZeroWord
public import AVRegularity.CycleWords.MixedWords.GaugeJetsCore
import AVRegularity.CycleWords.MixedWords.B1WSourceL2
import AVRegularity.CycleWords.FibreGraphNativeSeries
import AVRegularity.CycleDamping.ReferenceTimeEquation
public import AVRegularity.CycleWords.MixedWords.JetToValueStep
import AVRegularity.CycleEvolution.CellEnergySpaceRawDirectionalLimit
import Mathlib.CategoryTheory.Countable

section
section
/-! **(S): smoothing of the reduced transverse equation after unit time**.

`‖u(t)‖_{H^j} ≤ C ‖u(a)‖_{L²}` for `a + 1 ≤ t ≤ a + 2`, with `C` from `j, ρ, C_w, J` (no
smallness of `|ξ|`). Galerkin, by induction on the order `K ≤ j` with steps `δ = 1/(j + 1)`: at
order `K + 1` and time `t`, the order-`K` dissipation on `[t - δ, t]` gives a time `s` with
`‖lift_{K+1} y(s)‖² ≤ 2 e^{Γ_K} M_K ‖u(a)‖² / δ`, then the order-`K + 1` growth on `[s, t]`.

For `j = 0` this is the `L²` growth `e^{2Γ_0}` with no smoothing step, and for `a + 1 > b` the
statement is vacuous. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE

namespace AVRegularity.CycleWords

/-- The smoothing constants: `M_0 = e^{2Γ_0}` and `M_{K+1} = e^{Γ_{K+1}} · 2 e^{Γ_K} M_K (j + 1)`. -/
def transverseRegSmoothConst (j : ℕ) (ρ Cw : ℝ) (J : ℕ → ℝ) : ℕ → ℝ
  | 0 => Real.exp (2 * transverseRegGamma 0 ρ Cw J)
  | K + 1 => Real.exp (transverseRegGamma (K + 1) ρ Cw J) *
      (2 * Real.exp (transverseRegGamma K ρ Cw J) * transverseRegSmoothConst j ρ Cw J K *
        ((j : ℝ) + 1))

theorem transverseRegSmoothConst_nonneg (j : ℕ) (ρ Cw : ℝ) (J : ℕ → ℝ) (K : ℕ) :
    0 ≤ transverseRegSmoothConst j ρ Cw J K := by
  induction K with
  | zero => exact (Real.exp_pos _).le
  | succ K ih =>
    rw [transverseRegSmoothConst]
    exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (Real.exp_pos _).le) ih) (by positivity))

/-- **(S) for the finite transverse system**: order-`K` bounds after time `K/(j + 1)` from `L²`
data, on windows of length at most `2`. -/
theorem transverseRegGalerkin_smoothing (j N : ℕ) {a b η : ℝ} (hab : a ≤ b) (hη0 : 0 ≤ η)
    (hη : η ≤ 1) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (ξ : Fin 2 → ℂ) (ρ : ℝ)
    (hξ : fibreNorm ξ ≤ ρ) (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hfull : ∀ t ∈ Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t)) (J : ℕ → ℝ)
    (hj : ∀ l t, t ∈ Icc a b → ∀ x,
      ‖iteratedFDeriv ℝ l (fun x => Real.sqrt η • v t x) x‖ ≤ J l)
    (hc : ∀ t ∈ Icc a b, ContDiff ℝ (0 : ℕ) (v t)) (A : Fin 1 → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ t ∈ Icc a b, ∀ l x,
      ‖coefficientDerivativeArray (normalizedDriftCoefficient η v ξ t) l.val x‖ ≤ A l)
    (u₀ : ComplexCellL2) (y : ContinuousMap (Icc a b) (CellGalerkinSpace (E := ℂ) N))
    (hy : IsLinearIntegralSolution
      ((Icc a b).indicator (cellTransverseGalerkinOperator N a b η G hv ξ hc A hA hb 0))
      0 (cellGalerkinL2Initial N u₀) a b (extendCurve hab y)) :
    ∀ K : ℕ, ∀ t ∈ Icc a b, a + (K : ℝ) / ((j : ℝ) + 1) ≤ t → t ≤ a + 2 →
      ‖cellGalerkinNativeLiftCLM N K (extendCurve hab y t)‖ ^ 2 ≤
        transverseRegSmoothConst j ρ Cw J K * ‖u₀‖ ^ 2 := by
  have hρ : 0 ≤ ρ := (fibreNorm_nonneg ξ).trans hξ
  have hJ0 : ∀ l, 0 ≤ J l := fun l => (norm_nonneg _).trans (hj l a ⟨le_rfl, hab⟩ 0)
  have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = 1 / ((j : ℝ) + 1) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδdef, div_le_one hj1]
    linarith only [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hcont (K : ℕ) : Continuous (fun s => ‖cellGalerkinNativeLiftCLM N K (extendCurve hab y s)‖ ^ 2) :=
    ((cellGalerkinNativeLiftCLM N K).continuous.comp (continuous_extendCurve hab y)).norm.pow 2
  intro K
  induction K with
  | zero =>
    intro t ht _ ht2
    have hΓ := transverseRegGamma_nonneg 0 ρ Cw hρ J hJ0
    have hg := (transverseRegGalerkin_window_bounds 0 N hab hη0 hη G hG hv ξ ρ hξ Cw hCw hw hfull
      J hj hc A hA hb _ y hy ht.1 (Icc_subset_Icc le_rfl ht.2)).1
    rw [cellGalerkinNativeLiftCLM_zero_norm_sq, cellGalerkinNativeLiftCLM_zero_norm_sq,
      transverseRegGalerkin_initial N hab G hv ξ hc A hA hb _ y hy] at hg
    rw [cellGalerkinNativeLiftCLM_zero_norm_sq, transverseRegSmoothConst]
    have hi := pow_le_pow_left₀ (norm_nonneg _) (cellGalerkinL2Initial_norm_le N u₀) 2
    have hm := mul_le_mul_of_nonneg_left (by linarith only [ht2] : t - a ≤ 2) hΓ
    have he : Real.exp (transverseRegGamma 0 ρ Cw J * (t - a)) ≤
        Real.exp (2 * transverseRegGamma 0 ρ Cw J) :=
      Real.exp_le_exp.mpr (by linarith only [hm])
    exact hg.trans (mul_le_mul he hi (sq_nonneg _) (Real.exp_pos _).le)
  | succ K ih =>
    intro t ht hKt ht2
    have hΓK := transverseRegGamma_nonneg K ρ Cw hρ J hJ0
    have hΓK1 := transverseRegGamma_nonneg (K + 1) ρ Cw hρ J hJ0
    have hcast : ((K + 1 : ℕ) : ℝ) / ((j : ℝ) + 1) = (K : ℝ) / ((j : ℝ) + 1) + δ := by
      rw [hδdef]; push_cast; ring
    rw [hcast] at hKt
    have hK0 : 0 ≤ (K : ℝ) / ((j : ℝ) + 1) := by positivity
    have hca : a ≤ t - δ := by linarith only [hKt, hK0]
    have hsub : Icc (t - δ) t ⊆ Icc a b := Icc_subset_Icc hca ht.2
    have hIH := ih (t - δ) ⟨hca, by linarith only [ht.2, hδ]⟩ (by linarith only [hKt])
      (by linarith only [ht2, hδ])
    have hw2 := (transverseRegGalerkin_window_bounds K N hab hη0 hη G hG hv ξ ρ hξ Cw hCw hw hfull
      J hj hc A hA hb _ y hy (by linarith only [hδ] : t - δ ≤ t) hsub).2
    rw [sub_sub_cancel] at hw2
    have heK : Real.exp (transverseRegGamma K ρ Cw J * δ) ≤ Real.exp (transverseRegGamma K ρ Cw J) :=
      Real.exp_le_exp.mpr (mul_le_of_le_one_right hΓK hδ1)
    have hX : (∫ s in (t - δ)..t, ‖cellGalerkinNativeLiftCLM N (K + 1) (extendCurve hab y s)‖ ^ 2) ≤
        (t - (t - δ)) * ((2 * Real.exp (transverseRegGamma K ρ Cw J) *
          transverseRegSmoothConst j ρ Cw J K * ‖u₀‖ ^ 2) * ((j : ℝ) + 1)) := by
      have h1 := hw2.trans (mul_le_mul (mul_le_mul_of_nonneg_left heK (by norm_num)) hIH
        (sq_nonneg _) (mul_nonneg (by norm_num) (Real.exp_pos _).le))
      have h2 : (t - (t - δ)) * ((2 * Real.exp (transverseRegGamma K ρ Cw J) *
          transverseRegSmoothConst j ρ Cw J K * ‖u₀‖ ^ 2) * ((j : ℝ) + 1)) =
          2 * Real.exp (transverseRegGamma K ρ Cw J) *
            (transverseRegSmoothConst j ρ Cw J K * ‖u₀‖ ^ 2) := by
        rw [sub_sub_cancel, hδdef]
        field_simp
      rw [h2]
      exact h1
    obtain ⟨s, hs, hsb⟩ := exists_energy_le_integral_average
      (fun s => ‖cellGalerkinNativeLiftCLM N (K + 1) (extendCurve hab y s)‖ ^ 2) (t - δ) t _
      (by linarith only [hδ]) (hcont (K + 1)).continuousOn hX
    have hg := (transverseRegGalerkin_window_bounds (K + 1) N hab hη0 hη G hG hv ξ ρ hξ Cw hCw hw
      hfull J hj hc A hA hb _ y hy hs.2 (Icc_subset_Icc (hca.trans hs.1) ht.2)).1
    have heK1 : Real.exp (transverseRegGamma (K + 1) ρ Cw J * (t - s)) ≤
        Real.exp (transverseRegGamma (K + 1) ρ Cw J) :=
      Real.exp_le_exp.mpr (mul_le_of_le_one_right hΓK1 (by linarith only [hs.1, hδ1]))
    refine hg.trans ((mul_le_mul heK1 hsb (sq_nonneg _) (Real.exp_pos _).le).trans_eq ?_)
    rw [transverseRegSmoothConst]
    ring

end AVRegularity.CycleWords

namespace AVRegularity.CycleWords.Assembly

/-- **(S)**: smoothing on the second unit interval from the `L²` entrance alone. -/
theorem transverseRegSmoothing : TransverseRegSmoothingStatement := by
  intro j ρ Cw J _ _ hJ
  have hM := transverseRegSmoothConst_nonneg j ρ Cw J j
  refine ⟨transverseRegSmoothConst j ρ Cw J j + 1, by linarith only [hM], ?_⟩
  intro W t ht ht1 ht2
  have hab' : W.a < W.b := by linarith only [ht.2, ht1]
  have hc0 := transverseRegWindow_contDiff_zero W
  have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hjt : W.a + (j : ℝ) / ((j : ℝ) + 1) ≤ t := by
    have h := (div_le_one hj1).2 (by linarith only : (j : ℝ) ≤ (j : ℝ) + 1)
    linarith only [h, ht1]
  obtain ⟨w, hwv, hwb⟩ := transverseReg_transfer j hab' W.hη0 W.hη1 W.G W.hG W.hv W.ξ ρ
    W.hfreq Cw W.hCw W.hw W.hsmooth J W.hjets hc0 _
    (normalizedDriftJetBudget_nonneg 0 (fun l => J l.val) W.ξ (fun l => hJ l.val))
    (normalizedDriftJetBudget_window_bound 0 W.a W.b W.η W.v W.ξ hc0 (fun l => J l.val)
      (fun l t ht x => W.hjets l.val t ht x))
    W.u W.slice W.curve 0 (transverseRegSmoothConst j ρ Cw J j * ‖W.u W.a‖ ^ 2)
    (mul_nonneg hM (sq_nonneg _)) t ht
    (fun N y hy => ⟨cellGalerkinNativeLiftCLM N j (extendCurve hab'.le y t),
      (cellGalerkinNativeLiftCLM_value N j _).trans (sub_zero _).symm,
      transverseRegGalerkin_smoothing j N hab'.le W.hη0 W.hη1 W.G W.hG W.hv W.ξ ρ W.hfreq Cw
        W.hCw W.hw W.hsmooth J W.hjets hc0 _ _ _ (W.u W.a) y hy j t ht hjt ht2⟩)
  refine ⟨w, hwv.trans (sub_zero _), transverseReg_le_of_sq (norm_nonneg _) (norm_nonneg _)
    (by linarith only [hM]) (hwb.trans (mul_le_mul_of_nonneg_right (by linarith only) (sq_nonneg _)))⟩

end AVRegularity.CycleWords.Assembly
end
end

section
/-! Diagonal Fourier equations of the actual constant-in-space quiet diffusion. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set UnitAddTorus AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

local instance quietForcedFourierMeasure : MeasureSpace UnitAddCircle := instMeasureSpaceUnitAddCircle

/-- The physical frequency of one periodic mode at a real Bloch shift. -/
def quietFourierFrequency (θ : Vec 2) (n : Fin 2 → ℤ) : Vec 2 :=
  fun j => 2 * Real.pi * (n j : ℝ) + θ j

/-- Exact shifted weak derivative of the Fourier test. -/
theorem quietFourier_shifted_mode (θ : Vec 2) (n : Fin 2 → ℤ) (j : Fin 2) :
    cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j (cellComplexFourierModeH1 n) =
      cellScalarCLM (Complex.I * (quietFourierFrequency θ n j : ℂ))
        (scalarTorusToCell (mFourierLp 2 n)) := by
  change cellDerivativeCLM j (cellComplexFourierModeH1 n) +
    cellScalarCLM (Complex.I * (θ j : ℂ)) (torusHkValueCLM (cellComplexFourierModeH1 n)) = _
  rw [cellComplexFourierModeH1_derivative, cellComplexFourierModeH1_value]
  simp only [cellScalarCLM_smul]
  rw [← add_smul]
  congr 1
  dsimp only [quietFourierFrequency]
  push_cast
  ring

/-- Exact shifted weak derivative multiplier for an arbitrary H1 value. -/
theorem quietFourier_shifted_coefficient (θ : Vec 2) (n : Fin 2 → ℤ) (j : Fin 2)
    (u : TorusHk 1 ℂ) :
    cellComplexPair (cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j u)
      (scalarTorusToCell (mFourierLp 2 n)) =
      (Complex.I * (quietFourierFrequency θ n j : ℂ)) *
        cellComplexPair (torusHkValueCLM u) (scalarTorusToCell (mFourierLp 2 n)) := by
  rw [← scalarCellToTorus_fourierCoeff_pair, ← scalarCellToTorus_fourierCoeff_pair]
  change mFourierCoeff (scalarCellToTorus (cellDerivativeCLM j u +
    cellScalarCLM (Complex.I * (θ j : ℂ)) (torusHkValueCLM u))) n = _
  rw [scalarCellToTorus_fourierCoeff_add, scalarCellToTorus_fourierCoeff_scalar,
    cellH1_fourierDerivative]
  dsimp only [quietFourierFrequency]
  push_cast
  ring

/-- At a quiet time the actual generator is diagonal in the Fourier tests. -/
theorem quietFourier_generator
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2)
    (t : ℝ) (hquiet : ∀ x, v t x = 0) (n : Fin 2 → ℤ) (u : TorusHk 1 ℂ) :
    cellComplexGenerator ⟨fun t _ => G t, v, fun k => (θ k : ℂ), 0⟩ hG V hv.1 hb
      t u (cellComplexFourierModeH1 n) =
      -(∑ j, ∑ k, (G t j k : ℂ) * (quietFourierFrequency θ n j : ℂ) *
        (quietFourierFrequency θ n k : ℂ)) *
          cellComplexPair (torusHkValueCLM u) (scalarTorusToCell (mFourierLp 2 n)) := by
  have hd (j : Fin 2) : cellDriftEntryCLM
      ⟨fun t _ => G t, v, fun k => (θ k : ℂ), 0⟩ V hv.1 hb t j
        (cellShiftedDerivativeCLM (fun k => (θ k : ℂ)) j u) = 0 := by
    apply Lp.ext
    apply (cellDriftEntryCLM_ae _ V hv.1 hb t j _).trans
    filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := volume.restrict AVenhance.unitCube)] with x hx
    rw [hquiet x, Pi.zero_apply, Complex.ofReal_zero, zero_mul, hx, Pi.zero_apply]
  have hstar (r : ℝ) : star (Complex.I * (r : ℂ)) = -(Complex.I * (r : ℂ)) := by
    simp only [star_mul, Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
    ring
  simp only [cellComplexGenerator, Pi.zero_apply, hd, cellComplexPair_zero_left,
    Finset.sum_const_zero, sub_zero, Complex.star_def, Complex.conj_ofReal,
    cellComplexFourierModeH1_value, cellScalarCLM_smul, zero_smul, add_zero]
  simp only [quietFourier_shifted_mode, cellConstantMetricEntryCLM,
    cellComplexPair_scalar_left, cellComplexPair_scalar_right, quietFourier_shifted_coefficient, hstar]
  have hprod (a b c d : ℂ) : -(Complex.I * c) * (a * (Complex.I * b * d)) = a * b * c * d := by
    calc
      _ = -(Complex.I ^ 2) * (a * b * c * d) := by ring
      _ = _ := by rw [Complex.I_sq, neg_neg, one_mul]
  simp only [hprod]
  simp only [← Finset.sum_mul]
  ring

/-- A divergence source has the expected shifted Fourier multiplier. -/
theorem quietFourier_source (θ : Vec 2) (n : Fin 2 → ℤ) (F : Fin 2 → ComplexCellL2) :
    cellComplexSource (fun k => (θ k : ℂ)) 0 F (cellComplexFourierModeH1 n) =
      Complex.I * ∑ j, (quietFourierFrequency θ n j : ℂ) *
        cellComplexPair (F j) (scalarTorusToCell (mFourierLp 2 n)) := by
  have hstar (r : ℝ) : star (Complex.I * (r : ℂ)) = -(Complex.I * (r : ℂ)) := by
    simp only [star_mul, Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
    ring
  simp only [cellComplexSource, Complex.star_def, Complex.conj_ofReal, quietFourier_shifted_mode,
    cellComplexPair_zero_left, cellComplexPair_scalar_right, hstar, Fin.sum_univ_two]
  ring

/-- Each actual weak Fourier coefficient solves its measurable scalar inhomogeneous ODE. -/
theorem quietFourier_strongTime {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ) (F : ℝ → Fin 2 → ComplexCellL2)
    (h : CellWeakHilbertCurve a b u slice (fun t => cellDualDerivative
      ⟨fun t _ => G t, v, fun k => (θ k : ℂ), 0⟩ hG V hv.1 hb t (slice t) 0 (F t)))
    (hquiet : ∀ t ∈ Icc a b, ∀ x, v t x = 0) (n : Fin 2 → ℤ) :
    StrongTimeRegularity a b
      (fun t => cellComplexPair (u t) (scalarTorusToCell (mFourierLp 2 n)))
      (fun t => -(∑ j, ∑ k, (G t j k : ℂ) * (quietFourierFrequency θ n j : ℂ) *
        (quietFourierFrequency θ n k : ℂ)) *
          cellComplexPair (u t) (scalarTorusToCell (mFourierLp 2 n)) +
        Complex.I * ∑ j, (quietFourierFrequency θ n j : ℂ) *
          cellComplexPair (F t j) (scalarTorusToCell (mFourierLp 2 n))) := by
  have hs := h.complex_test_strongTime hab (cellComplexFourierModeH1 n)
  rw [cellComplexFourierModeH1_value] at hs
  refine ⟨hs.ac, ?_⟩
  have hd := hs.derivative
  rw [uIcc_of_le hab] at hd ⊢
  filter_upwards [hd, h.agrees, ae_restrict_mem measurableSet_Icc] with t ht ha hmem
  rw [cellDualComplexPair_actual, quietFourier_generator G hG hv V hb θ t (hquiet t hmem),
    quietFourier_source, ← ha] at ht
  exact ht

/-- The forcing in each Fourier ODE is integrable on the original closed window. -/
theorem quietFourier_forcing_integrable {a b : ℝ} (hab : a ≤ b)
    (θ : Vec 2) (n : Fin 2 → ℤ) (F : ℝ → Fin 2 → ComplexCellL2)
    (hF : ∀ j, MemLp (fun t => F t j) 2 (volume.restrict (Icc a b))) :
    IntervalIntegrable (fun t => Complex.I * ∑ j, (quietFourierFrequency θ n j : ℂ) *
      cellComplexPair (F t j) (scalarTorusToCell (mFourierLp 2 n))) volume a b := by
  apply ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr ?_).const_mul Complex.I
  change Integrable (fun t => ∑ j, (quietFourierFrequency θ n j : ℂ) *
    cellComplexPair (F t j) (scalarTorusToCell (mFourierLp 2 n))) (volume.restrict (Icc a b))
  have hi (j : Fin 2) : Integrable
      (fun t => cellComplexPair (F t j) (scalarTorusToCell (mFourierLp 2 n)))
        (volume.restrict (Icc a b)) := by
    have he : (fun t => cellComplexPair (F t j) (scalarTorusToCell (mFourierLp 2 n))) =
        ((innerSL ℂ (scalarTorusToCell (mFourierLp 2 n))).restrictScalars ℝ) ∘ (fun t => F t j) := by
      funext t
      exact cellComplexPair_eq_inner _ _
    rw [he]
    exact (((innerSL ℂ (scalarTorusToCell (mFourierLp 2 n))).restrictScalars ℝ).comp_memLp'
      (hF j)).integrable (by norm_num)
  convert (hi 0 |>.const_mul (quietFourierFrequency θ n 0 : ℂ)).add
    (hi 1 |>.const_mul (quietFourierFrequency θ n 1 : ℂ)) using 1
  funext t
  simp only [Fin.sum_univ_two, Pi.add_apply]

/-- Exact Duhamel equation of every Fourier coefficient, without constructing a new solution. -/
theorem quietFourier_evolution {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Vec 2)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ) (F : ℝ → Fin 2 → ComplexCellL2)
    (hF : ∀ j, MemLp (fun t => F t j) 2 (volume.restrict (Icc a b)))
    (h : CellWeakHilbertCurve a b u slice (fun t => cellDualDerivative
      ⟨fun t _ => G t, v, fun k => (θ k : ℂ), 0⟩ hG V hv.1 hb t (slice t) 0 (F t)))
    (hquiet : ∀ t ∈ Icc a b, ∀ x, v t x = 0) (n : Fin 2 → ℤ) :
    let lam := fun t => -(∑ j, ∑ k, (G t j k : ℂ) * (quietFourierFrequency θ n j : ℂ) *
      (quietFourierFrequency θ n k : ℂ))
    cellComplexPair (u b) (scalarTorusToCell (mFourierLp 2 n)) =
      Complex.exp (∫ t in a..b, lam t) *
        cellComplexPair (u a) (scalarTorusToCell (mFourierLp 2 n)) +
      ∫ t in a..b, Complex.exp (∫ r in t..b, lam r) *
        (Complex.I * ∑ j, (quietFourierFrequency θ n j : ℂ) *
          cellComplexPair (F t j) (scalarTorusToCell (mFourierLp 2 n))) := by
  apply quietForced_scalar_evolution hab
  · have hi := fibreMetricSymbol_intervalIntegrable 1 G hG
      (fun j => (quietFourierFrequency θ n j : ℂ)) a b
    have he : (fun t => -(1 : ℂ) * fibreQuad (G t)
        (fun j => (quietFourierFrequency θ n j : ℂ))) =
        (fun t => -(∑ j, ∑ k, (G t j k : ℂ) * (quietFourierFrequency θ n j : ℂ) *
          (quietFourierFrequency θ n k : ℂ))) := by
      funext t
      simp only [neg_one_mul, fibreQuad]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [Complex.ofReal_one, he] at hi
    exact hi
  · exact quietFourier_forcing_integrable hab θ n F hF
  · exact quietFourier_strongTime hab G hG hv V hb θ u slice F h hquiet n

/-- The quiet Fourier heat multiplier on the original measurable metric. -/
def quietFourierMultiplier (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (θ : Vec 2)
    (n : Fin 2 → ℤ) (s t : ℝ) : ℂ :=
  Complex.exp (-(∫ r in s..t, fibreQuad (G r) (fun j => (quietFourierFrequency θ n j : ℂ))))

/-- Measurable-time ellipticity gives the full quadratic Fourier damping. -/
theorem quietFourier_multiplier_bound
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Vec 2) (n : Fin 2 → ℤ) {s t : ℝ} (hst : s ≤ t) :
    ‖quietFourierMultiplier G θ n s t‖ ≤
      Real.exp (-(1 / 2) * (∑ j, quietFourierFrequency θ n j ^ 2) * (t - s)) := by
  let y := quietFourierFrequency θ n
  let q := fun r => fibreQuad (G r) (fun j => (y j : ℂ))
  have hi : IntervalIntegrable q volume s t := by
    convert (fibreMetricSymbol_intervalIntegrable 1 G hG (fun j => (y j : ℂ)) s t).neg using 1
    funext r
    simp only [Pi.neg_apply, Complex.ofReal_one, neg_one_mul, neg_neg]
    rfl
  have hr (r : ℝ) : (q r).re = ∑ j, ∑ k, y j * G r j k * y k := by
    simp only [q, fibreQuad, ← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.ofReal_re]
  have hlow := intervalIntegral.integral_mono_on hst
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 / 2) * ∑ j, y j ^ 2) volume s t)
    (intervalIntegrable_iff.mpr (Complex.reCLM.integrable_comp (intervalIntegrable_iff.mp hi))) (fun r _ => by rw [Complex.reCLM_apply, hr]; exact (hG.2.2.2 r 0 y).1)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hlow
  simp only [Complex.reCLM_apply] at hlow
  have he := Complex.reCLM.intervalIntegral_comp_comm hi
  change (∫ r in s..t, (q r).re) = (∫ r in s..t, q r).re at he
  rw [he] at hlow
  rw [quietFourierMultiplier, Complex.norm_exp, Complex.neg_re]
  apply Real.exp_le_exp.mpr
  change -(∫ r in s..t, q r).re ≤ -(1 / 2) * (∑ j, y j ^ 2) * (t - s)
  exact (neg_le_neg hlow).trans_eq (by ring)

/-- The mean-free modes retain the sharp homogeneous rate. -/
theorem quietFourier_multiplier_gap
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (θ : Vec 2) (hθ : ∀ j, |θ j| ≤ Real.pi) (n : Fin 2 → ℤ) (hn : n ≠ 0)
    {s t : ℝ} (hst : s ≤ t) :
    ‖quietFourierMultiplier G θ n s t‖ ≤ Real.exp (-(Real.pi ^ 2 / 2) * (t - s)) := by
  apply (quietFourier_multiplier_bound G hG θ n hst).trans
  apply Real.exp_le_exp.mpr
  have hg := CycleDamping.brillouin_mean_free_gap n hn θ hθ
  change Real.pi ^ 2 ≤ ∑ j, quietFourierFrequency θ n j ^ 2 at hg
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg (by norm_num : (0:ℝ) ≤ 1 / 2))
    (sub_nonneg.mpr hst)
  have he : -(1 / 2 * Real.pi ^ 2 * (t - s)) = -(Real.pi ^ 2 / 2) * (t - s) := by ring
  calc
    _ = -((1 / 2 * ∑ j, quietFourierFrequency θ n j ^ 2) * (t - s)) := by ring
    _ ≤ _ := (neg_le_neg hm).trans_eq he

end AVRegularity.CycleWords.Assembly
end
end
end

section
section
/-! # The gauge and the slow adjoint test

For a word piece of a `CoreScalarPackage` at a plane frequency `θ` with `|ξ| ≤ ρ ≤ 2ξ_lo`
(`ξ = planeFibreFrequency η θ`), with `Ξ(a, r) = blockGauge pkg.actual.lam η a r θ`:

* the gauge `Γ(r) = |e^{-Ξ(a,r)}|` is positive (`b1wGamma_pos`) and grows at most like
  `e^{π²/16 (s - r)}` (`b1wGamma_growth`, from `scalarPackage_gauge_growth` and the
  separation `(2 + C_w C_g)(2ξ_lo)² ≤ π²/16` of `consts_pos`);
* the normalization `N₀ = e^{Ξ(a,b)}` is nonzero, so the slow coordinate `⟨W, q⟩/N₀` is the
  gauged one: the adjoint curve from `q(b) = 1` is `q(r) ≈ N₀ e^{-Ξ(a,r)} ℓ(r)`;
* the slow adjoint test `q` from `1` at `b` exists (from `adjointCurve_exists`) for the actual
  fibre coefficients. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution

namespace AVRegularity.CycleWords.Assembly

/-- The gauge `Γ(r) = |e^{-Ξ(a,r)}|`. -/
def b1wGamma (lam : ℕ × ℕ → ℝ → ℂ) (η a : ℝ) (θ : Vec 2) (r : ℝ) : ℝ :=
  ‖Complex.exp (-blockGauge lam η a r θ)‖

theorem b1wGamma_pos (lam : ℕ × ℕ → ℝ → ℂ) (η a : ℝ) (θ : Vec 2) (r : ℝ) :
    0 < b1wGamma lam η a θ r :=
  norm_pos_iff.2 (Complex.exp_ne_zero _)

/-- **The gauge grows at most at the slow damping rate `π²/16`.** -/
theorem b1wGamma_growth {K : ScalarConstants} {η t₀ S : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {v : ℝ → Vec 2 → Vec 2} (data : FibreScalarData K η G v t₀ S) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hCg : 0 ≤ K.Cg) (hCw : 0 ≤ K.Cw) (hG : IsCellMetric (fun t _ => G t)) (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ K.Cw)
    (hsep : (2 + K.Cw * K.Cg) * (2 * K.ξlo) ^ 2 ≤ Real.pi ^ 2 / 16)
    {ρ : ℝ} (hρ : ρ < K.ξ0) (hρlo : ρ ≤ 2 * K.ξlo) (θ : Vec 2)
    (hθ : fibreNorm (planeFibreFrequency η θ) ≤ ρ) (hreal : ∀ i, (planeFibreFrequency η θ i).im = 0)
    (a : ℝ) {r s : ℝ} (har : a ≤ r) (hrs : r ≤ s) :
    b1wGamma data.lam η a θ s ≤
      Real.exp (Real.pi ^ 2 / 16 * (s - r)) * b1wGamma data.lam η a θ r := by
  set ξ := planeFibreFrequency η θ with hξdef
  have hξ0 : fibreNorm ξ < K.ξ0 := lt_of_le_of_lt hθ hρ
  have hint : ∀ c d, c ≤ d → IntervalIntegrable (fun τ => fibreSeriesC data.lam ξ τ) volume c d :=
    fun c d hcd => (intervalIntegrable_iff_integrableOn_Ioc_of_le hcd).mpr
      (symbol_integrableOn data hη0 hη1 hCg hCw hG hv hw hξ0 c d)
  have hgrow := scalarPackage_gauge_growth data hη0 hη1 hCg hCw hG hv hw ξ hreal hξ0
    (le_refl (fibreNorm ξ)) hrs (hint r s hrs)
  have hsplit : -blockGauge data.lam η a s θ =
      -blockGauge data.lam η a r θ + -∫ τ in r..s, fibreSeriesC data.lam ξ τ := by
    unfold blockGauge
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint a r har) (hint r s hrs)]
    ring
  have hn0 := fibreNorm_nonneg ξ
  have hrate : (2 + K.Cw * K.Cg) * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2 / 16 := by
    have h2 : fibreNorm ξ ^ 2 ≤ (2 * K.ξlo) ^ 2 := pow_le_pow_left₀ hn0 (hθ.trans hρlo) 2
    exact (mul_le_mul_of_nonneg_left h2 (by positivity)).trans hsep
  have hexp : Real.exp ((2 + K.Cw * K.Cg) * fibreNorm ξ ^ 2 * (s - r)) ≤
      Real.exp (Real.pi ^ 2 / 16 * (s - r)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hrate (sub_nonneg.2 hrs))
  unfold b1wGamma
  rw [hsplit, Complex.exp_add, norm_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hgrow.trans hexp) (norm_nonneg _)

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # The `L²` layer of the transverse estimate: the graph is small in `L²` on the whole disc

For a fibre graph `r` with slow damping `σ = (2 + C_w C_g)|ξ|² ≤ π²/16`, the slow mode
`h = e^{∫λ}(1 + r)` is a homogeneous solution (`fibreScalarData_graph_homogeneous_evolution`).
Its energy production is at most `-2π²‖Q₀h‖² + |θ|²‖h‖²` (sharp energy, shifted gradient,
Poincaré), and `‖h‖² = |e^{∫λ}|²(1 + y)`, `‖Q₀h‖² = |e^{∫λ}|² y` with `y = ‖r‖²`. Where
`y ≥ 1/10` this gives `1 + y(b) ≤ e^{-(π²/40)(b-a)}(1 + y(a))` (`graphTrace_interval_decay`), and a
barrier argument with the a priori bound `y ≤ (C_g|ξ|)²` gives `y ≤ 1/10` at all times
(`graphTrace_l2_small`). No smallness of `|ξ|` beyond the separation condition `(2 + C_w C_g)|ξ|² ≤ π²/16` is used. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal

namespace AVRegularity.CycleWords.Assembly

variable {K : ScalarConstants} {η t₀ S : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {v : ℝ → Vec 2 → Vec 2}

/-- The graph trace is mean zero. -/
theorem graphTrace_mean_zero (data : FibreScalarData K η G v t₀ S) {ξ : Fin 2 → ℂ}
    (hξ : fibreNorm ξ < K.ξ0) (t : ℝ) :
    cellMeanCLM (cellRawTrace (fibreSeriesJet data.r ξ) t) = 0 := by
  have hinv := (data.graph.2.1 ξ hξ).2.2.1
  have hmem := (hinv.1.2.2.1 t (Set.mem_univ t)).1
  rw [cellMeanCLM_apply, ← hinv.2.1 t]
  exact integral_congr_ae (cellRawTrace_ae _ t hmem)

/-- The graph trace is bounded by `C_g|ξ|`. -/
theorem graphTrace_norm_le (data : FibreScalarData K η G v t₀ S) {ξ : Fin 2 → ℂ}
    (hξ : fibreNorm ξ < K.ξ0) (hCg : 0 ≤ K.Cg) (t : ℝ) :
    ‖cellRawTrace (fibreSeriesJet data.r ξ) t‖ ≤ K.Cg * fibreNorm ξ := by
  have hinv := (data.graph.2.1 ξ hξ).2.2.1
  exact (cellRawTrace_norm_le_energy _ hinv.1 hinv.2.2 t).trans
    (ENNReal.toReal_le_of_le_ofReal (mul_nonneg hCg (fibreNorm_nonneg ξ))
      (data.graph.2.1 ξ hξ).2.2.2.2)

/-- The graph trace is continuous in time. -/
theorem graphTrace_continuous (data : FibreScalarData K η G v t₀ S) {ξ : Fin 2 → ℂ}
    (hξ : fibreNorm ξ < K.ξ0) : Continuous (cellRawTrace (fibreSeriesJet data.r ξ)) := by
  have hinv := (data.graph.2.1 ξ hξ).2.2.1
  exact continuousOn_univ.mp (cellRawTrace_continuous Set.univ _
    (fun t ht => (hinv.1.2.2.1 t ht).1) hinv.1.2.2.2.2.1)

/-- The norms of a slow-mode state `c(x + 1)` with `⟨x⟩ = 0`. -/
theorem slowState_norms (c : ℂ) (x : ComplexCellL2) (hx : cellMeanCLM x = 0) :
    ‖cellScalarCLM c (x + cellConstantCLM 1)‖ ^ 2 = ‖c‖ ^ 2 * (1 + ‖x‖ ^ 2) ∧
      ‖cellQ0CLM (cellScalarCLM c (x + cellConstantCLM 1))‖ ^ 2 = ‖c‖ ^ 2 * ‖x‖ ^ 2 := by
  have hs : ∀ y : ComplexCellL2, ‖cellScalarCLM c y‖ = ‖c‖ * ‖y‖ := fun y => by
    simp [cellScalarCLM, norm_smul]
  have hm1 : cellMeanCLM (x + cellConstantCLM 1) = 1 := by
    rw [map_add, hx, cellMeanCLM_one, zero_add]
  have hd1 := cellQ0CLM_norm_sq_decomposition (x + cellConstantCLM 1)
  have hq1 : cellQ0CLM (x + cellConstantCLM 1) = x := by
    change x + cellConstantCLM 1 - cellConstantCLM (cellMeanCLM (x + cellConstantCLM 1)) = x
    rw [hm1, add_sub_cancel_right]
  rw [hq1, ← cellMeanCLM_apply, hm1, norm_one, one_pow] at hd1
  have hmc : cellMeanCLM (cellScalarCLM c (x + cellConstantCLM 1)) = c := by
    rw [cellMeanCLM_apply, CycleDamping.cellMean_scalar, ← cellMeanCLM_apply, hm1, mul_one]
  have hd2 := cellQ0CLM_norm_sq_decomposition (cellScalarCLM c (x + cellConstantCLM 1))
  rw [← cellMeanCLM_apply, hmc, hs, mul_pow, hd1] at hd2
  refine ⟨by rw [hs, mul_pow, hd1]; ring, by linarith⟩

/-- The energy production of a real shift through the mean-free part. -/
theorem realShift_production_le {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : IsCellMetric G) {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Fin 2 → ℂ) (hθ : ∀ j, star (θ j) = θ j)
    (t : ℝ) (z : TorusHk 1 ℂ) :
    2 * inner ℝ (cellDualDerivative ⟨G, v, θ, 0⟩ hG V hv.1 hb t z 0 0) z ≤
      -(2 * Real.pi ^ 2) * ‖cellQ0CLM (torusHkValueCLM z)‖ ^ 2 +
        (∑ j, ‖θ j‖ ^ 2) * ‖torusHkValueCLM z‖ ^ 2 := by
  have h1 := cellDualDerivative_real_energy hG hv V hb θ hθ t z
  have h2 := shiftedDerivative_sq_lower θ z
  have h3 := cellH1_meanFree_poincare z
  have hπ : (0 : ℝ) < 4 * Real.pi ^ 2 := by positivity
  have h4 : 4 * Real.pi ^ 2 * ‖cellQ0CLM (torusHkValueCLM z)‖ ^ 2 ≤
      ∑ j, ‖cellDerivativeCLM j z‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_left h3 hπ.le
    rwa [← mul_assoc, mul_inv_cancel₀ hπ.ne', one_mul] at this
  nlinarith

/-- The shift `θ = √η ξ` of a real `ξ` is real, and `|θ| ≤ |ξ|`. -/
theorem realShift_facts (hη : η ≤ 1) (ξ : Fin 2 → ℂ)
    (hreal : ∀ i, (ξ i).im = 0) :
    (∀ j, star ((Real.sqrt η : ℂ) * ξ j) = (Real.sqrt η : ℂ) * ξ j) ∧
      ∑ j, ‖(Real.sqrt η : ℂ) * ξ j‖ ^ 2 ≤ fibreNorm ξ ^ 2 := by
  refine ⟨fun j => ?_, ?_⟩
  · have hx : ξ j = ((ξ j).re : ℂ) := Complex.ext rfl (by simp [hreal j])
    rw [hx]
    simp [← Complex.ofReal_mul]
  · have hs : Real.sqrt η ≤ 1 := Real.sqrt_le_one.mpr hη
    have hs0 := Real.sqrt_nonneg η
    have hn : fibreNorm ξ ^ 2 = ∑ j, ‖ξ j‖ ^ 2 := by
      unfold fibreNorm
      rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    rw [hn]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0, mul_pow]
    have h1 : Real.sqrt η ^ 2 ≤ 1 := by nlinarith
    have h2 := sq_nonneg ‖ξ j‖
    nlinarith

/-- **The slow-mode phase decays at most at the slow damping**:
`|e^{∫_a^b λ}| ≥ e^{-(2 + C_w C_g)|ξ|²(b-a)}`. -/
theorem graphPhase_norm_lower (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCg : 0 ≤ K.Cg)
    (hCw : 0 ≤ K.Cw) (hG : IsCellMetric (fun t _ => G t)) (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ K.Cw)
    (data : FibreScalarData K η G v t₀ S) (ξ : Fin 2 → ℂ) (hreal : ∀ i, (ξ i).im = 0)
    (hξ : fibreNorm ξ < K.ξ0) {a b : ℝ} (hab : a ≤ b) :
    Real.exp (-((2 + K.Cw * K.Cg) * fibreNorm ξ ^ 2) * (b - a)) ≤
      ‖Complex.exp (∫ τ in a..b, fibreSeriesC data.lam ξ τ)‖ := by
  have hl := fibreGraph_symbol_memLp_top data.graph hη0 hη hCw hG hv hw ξ hξ hCg a b
  have hint : IntervalIntegrable (fun τ => fibreSeriesC data.lam ξ τ) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr (hl.integrable le_top)
  have hgauge := scalarPackage_gauge_growth data hη0 hη hCg hCw hG hv hw ξ hreal hξ
    (le_refl (fibreNorm ξ)) hab hint
  have hpos : 0 < ‖Complex.exp (-∫ τ in a..b, fibreSeriesC data.lam ξ τ)‖ := by
    rw [norm_pos_iff]
    exact Complex.exp_ne_zero _
  have hinv : ‖Complex.exp (∫ τ in a..b, fibreSeriesC data.lam ξ τ)‖ =
      ‖Complex.exp (-∫ τ in a..b, fibreSeriesC data.lam ξ τ)‖⁻¹ := by
    simp only [Complex.exp_neg, norm_inv, inv_inv]
  rw [hinv, show -((2 + K.Cw * K.Cg) * fibreNorm ξ ^ 2) * (b - a) =
    -((2 + K.Cw * K.Cg) * fibreNorm ξ ^ 2 * (b - a)) by ring, Real.exp_neg]
  exact inv_anti₀ hpos hgauge

/-- **Interval decay of the graph size where it is at least `1/10`.** -/
theorem graphTrace_interval_decay (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCg : 0 ≤ K.Cg)
    (hCw : 0 ≤ K.Cw) (hG : IsCellMetric (fun t _ => G t)) (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ K.Cw)
    (data : FibreScalarData K η G v t₀ S) (ξ : Fin 2 → ℂ) (hreal : ∀ i, (ξ i).im = 0)
    (hξ : fibreNorm ξ < K.ξ0) (hsep : (2 + K.Cw * K.Cg) * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2 / 16)
    {a b : ℝ} (hab : a ≤ b)
    (hy : ∀ t ∈ Ioc a b, 1 / 10 ≤ ‖cellRawTrace (fibreSeriesJet data.r ξ) t‖ ^ 2) :
    1 + ‖cellRawTrace (fibreSeriesJet data.r ξ) b‖ ^ 2 ≤
      Real.exp (-(Real.pi ^ 2 / 40) * (b - a)) *
        (1 + ‖cellRawTrace (fibreSeriesJet data.r ξ) a‖ ^ 2) := by
  obtain ⟨V, hV⟩ := hv.2.1
  obtain ⟨hθr, hθn⟩ := realShift_facts hη ξ hreal
  have hcurve := fibreScalarData_graph_homogeneous_evolution K η t₀ S hη0 hη hCg hCw G hG v hv
    hm hw data V hV ξ hξ hab
  dsimp only at hcurve
  set n := fibreNorm ξ with hndef
  set y := fun t => ‖cellRawTrace (fibreSeriesJet data.r ξ) t‖ ^ 2 with hydef
  set ph := fun t => Complex.exp (∫ τ in a..t, fibreSeriesC data.lam ξ τ) with hphdef
  set c := 2 * Real.pi ^ 2 / 11 - ∑ j, ‖(Real.sqrt η : ℂ) * ξ j‖ ^ 2 with hcdef
  have hIoc : ∀ᵐ t ∂(volume.restrict (Icc a b)), t ∈ Ioc a b := by
    rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
    exact ae_restrict_mem measurableSet_Ioc
  have hwb := (hcurve.energy_strongTime hab).scalar_weighted_bound hab c (fun _ => 0)
    (fun _ => 0) intervalIntegrable_const intervalIntegrable_const (by
      filter_upwards [hcurve.agrees, hIoc] with t ht hti
      have hp := realShift_production_le hG hv V hV _ hθr t
        (cellH1Scalar (ph t) (cellH1Slice (fibreSeriesJet data.r ξ) t + cellH1One))
      rw [← ht] at hp
      obtain ⟨hn1, hn2⟩ := slowState_norms (ph t) (cellRawTrace (fibreSeriesJet data.r ξ) t)
        (graphTrace_mean_zero data hξ t)
      rw [hn1, hn2] at hp
      have hyt := hy t hti
      have hph0 := sq_nonneg ‖ph t‖
      have hθ0 : 0 ≤ ∑ j, ‖(Real.sqrt η : ℂ) * ξ j‖ ^ 2 :=
        Finset.sum_nonneg fun j _ => sq_nonneg _
      simp only [add_zero]
      rw [hn1]
      have key : -(2 * Real.pi ^ 2) * (‖ph t‖ ^ 2 * y t) +
          (∑ j, ‖(Real.sqrt η : ℂ) * ξ j‖ ^ 2) * (‖ph t‖ ^ 2 * (1 + y t)) +
          c * (‖ph t‖ ^ 2 * (1 + y t)) =
          ‖ph t‖ ^ 2 * (2 * Real.pi ^ 2 / 11) * (1 - 10 * y t) := by
        rw [hcdef]
        ring
      have hneg : ‖ph t‖ ^ 2 * (2 * Real.pi ^ 2 / 11) * (1 - 10 * y t) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (by simp only [hydef] at hyt ⊢; linarith)
      linarith)
  simp only [intervalIntegral.integral_zero, add_zero, mul_zero] at hwb
  -- the endpoint norms
  obtain ⟨hna, -⟩ := slowState_norms (ph a) (cellRawTrace (fibreSeriesJet data.r ξ) a)
    (graphTrace_mean_zero data hξ a)
  obtain ⟨hnb, -⟩ := slowState_norms (ph b) (cellRawTrace (fibreSeriesJet data.r ξ) b)
    (graphTrace_mean_zero data hξ b)
  have hpha : ‖ph a‖ = 1 := by simp [hphdef]
  rw [hna, hpha, one_pow, one_mul, hnb] at hwb
  -- the phase lower bound
  set σ := (2 + K.Cw * K.Cg) * n ^ 2 with hσdef
  have hphb : Real.exp (-σ * (b - a)) ≤ ‖ph b‖ :=
    graphPhase_norm_lower hη0 hη hCg hCw hG hv hw data ξ hreal hξ hab
  have hphb2 : Real.exp (-(2 * σ) * (b - a)) ≤ ‖ph b‖ ^ 2 := by
    have h0 : 0 ≤ Real.exp (-σ * (b - a)) := (Real.exp_pos _).le
    calc Real.exp (-(2 * σ) * (b - a)) = Real.exp (-σ * (b - a)) ^ 2 := by
          rw [← Real.exp_nat_mul]
          congr 1
          push_cast
          ring
      _ ≤ ‖ph b‖ ^ 2 := pow_le_pow_left₀ h0 hphb 2
  -- the rates
  have hn2 : n ^ 2 ≤ Real.pi ^ 2 / 32 := by
    have hcw : 0 ≤ K.Cw * K.Cg := mul_nonneg hCw hCg
    nlinarith [sq_nonneg n]
  have hrate : Real.pi ^ 2 / 40 ≤ c - 2 * σ := by
    have hpi := Real.pi_pos
    rw [hcdef, hσdef]
    nlinarith [hθn, hsep]
  have hy0 : 0 ≤ 1 + y b := by positivity
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  have hmain : Real.exp ((c - 2 * σ) * (b - a)) * (1 + y b) ≤ 1 + y a := by
    calc Real.exp ((c - 2 * σ) * (b - a)) * (1 + y b)
        = Real.exp (c * (b - a)) * (Real.exp (-(2 * σ) * (b - a)) * (1 + y b)) := by
          have he : Real.exp ((c - 2 * σ) * (b - a)) =
              Real.exp (c * (b - a)) * Real.exp (-(2 * σ) * (b - a)) := by
            rw [← Real.exp_add]
            ring_nf
          rw [he, mul_assoc]
      _ ≤ Real.exp (c * (b - a)) * (‖ph b‖ ^ 2 * (1 + y b)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hphb2 hy0) (Real.exp_pos _).le
      _ ≤ 1 + y a := by simpa [hydef, add_comm] using hwb
  have hexp : Real.exp (-(Real.pi ^ 2 / 40) * (b - a)) * Real.exp ((c - 2 * σ) * (b - a)) ≥ 1 := by
    rw [← Real.exp_add]
    exact Real.one_le_exp (by nlinarith)
  calc 1 + y b ≤ Real.exp (-(Real.pi ^ 2 / 40) * (b - a)) *
        (Real.exp ((c - 2 * σ) * (b - a)) * (1 + y b)) := by nlinarith
    _ ≤ Real.exp (-(Real.pi ^ 2 / 40) * (b - a)) * (1 + y a) :=
        mul_le_mul_of_nonneg_left hmain (Real.exp_pos _).le

/-- **The graph is small in `L²` at every time**: `‖r(t)‖² ≤ 1/10` on the whole disc allowed by
the separation condition. -/
theorem graphTrace_l2_small (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCg : 0 ≤ K.Cg)
    (hCw : 0 ≤ K.Cw) (hG : IsCellMetric (fun t _ => G t)) (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ K.Cw)
    (data : FibreScalarData K η G v t₀ S) (ξ : Fin 2 → ℂ) (hreal : ∀ i, (ξ i).im = 0)
    (hξ : fibreNorm ξ < K.ξ0) (hsep : (2 + K.Cw * K.Cg) * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2 / 16)
    (t₁ : ℝ) : ‖cellRawTrace (fibreSeriesJet data.r ξ) t₁‖ ^ 2 ≤ 1 / 10 := by
  by_contra hcon
  push Not at hcon
  have hyc : Continuous fun t => ‖cellRawTrace (fibreSeriesJet data.r ξ) t‖ ^ 2 :=
    ((graphTrace_continuous data hξ).norm).pow 2
  set M := (K.Cg * fibreNorm ξ) ^ 2 with hMdef
  have hM0 : 0 ≤ M := sq_nonneg _
  have hyM : ∀ t, ‖cellRawTrace (fibreSeriesJet data.r ξ) t‖ ^ 2 ≤ M := fun t =>
    pow_le_pow_left₀ (norm_nonneg _) (graphTrace_norm_le data hξ hCg t) 2
  have hpi : 0 < Real.pi ^ 2 := by positivity
  set T := 40 * (M + 1) / Real.pi ^ 2 with hTdef
  have hT0 : 0 < T := by positivity
  have hxT : Real.pi ^ 2 / 40 * T = M + 1 := by
    rw [hTdef]
    field_simp
  have hT : Real.exp (-(Real.pi ^ 2 / 40) * T) * (1 + M) < 1 := by
    have h1 : M + 1 + 1 ≤ Real.exp (Real.pi ^ 2 / 40 * T) := by
      rw [hxT]
      exact Real.add_one_le_exp _
    have hne : Real.exp (-(Real.pi ^ 2 / 40) * T) * Real.exp (Real.pi ^ 2 / 40 * T) = 1 := by
      rw [← Real.exp_add]
      simp
    have hp := Real.exp_pos (-(Real.pi ^ 2 / 40) * T)
    nlinarith
  set A := Icc (t₁ - T) t₁ ∩ {τ | ‖cellRawTrace (fibreSeriesJet data.r ξ) τ‖ ^ 2 ≤ 1 / 10}
    with hAdef
  have hAc : IsCompact A := isCompact_Icc.inter_right (isClosed_le hyc continuous_const)
  have hdecay := fun {a b : ℝ} (hab : a ≤ b) (hy : ∀ t ∈ Ioc a b,
      1 / 10 ≤ ‖cellRawTrace (fibreSeriesJet data.r ξ) t‖ ^ 2) =>
    graphTrace_interval_decay hη0 hη hCg hCw hG hv hm hw data ξ hreal hξ hsep hab hy
  by_cases hA : A.Nonempty
  · have hτ0 := hAc.sSup_mem hA
    set τ₀ := sSup A with hτ0def
    have hτ0le : τ₀ ≤ t₁ := hτ0.1.2
    have hτ0lt : τ₀ < t₁ := by
      refine lt_of_le_of_ne hτ0le fun h => ?_
      have := hτ0.2
      rw [h] at this
      simp only [Set.mem_ofPred_eq] at this
      linarith
    have hgt : ∀ t ∈ Ioc τ₀ t₁, 1 / 10 ≤ ‖cellRawTrace (fibreSeriesJet data.r ξ) t‖ ^ 2 := by
      intro t ht
      by_contra h
      push Not at h
      have hmem : t ∈ A := ⟨⟨le_trans hτ0.1.1 ht.1.le, ht.2⟩, h.le⟩
      have := le_csSup hAc.bddAbove hmem
      linarith [ht.1]
    have hd := hdecay hτ0lt.le hgt
    have hy0 : ‖cellRawTrace (fibreSeriesJet data.r ξ) τ₀‖ ^ 2 ≤ 1 / 10 := hτ0.2
    have hexp : Real.exp (-(Real.pi ^ 2 / 40) * (t₁ - τ₀)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    have hpos : 0 ≤ 1 + ‖cellRawTrace (fibreSeriesJet data.r ξ) τ₀‖ ^ 2 := by positivity
    have : 1 + ‖cellRawTrace (fibreSeriesJet data.r ξ) t₁‖ ^ 2 ≤ 1 + 1 / 10 :=
      hd.trans ((mul_le_of_le_one_left hpos hexp).trans (by linarith))
    linarith
  · have hgt : ∀ t ∈ Ioc (t₁ - T) t₁,
        1 / 10 ≤ ‖cellRawTrace (fibreSeriesJet data.r ξ) t‖ ^ 2 := by
      intro t ht
      by_contra h
      push Not at h
      exact hA ⟨t, ⟨ht.1.le, ht.2⟩, h.le⟩
    have hd := hdecay (by linarith : t₁ - T ≤ t₁) hgt
    have hsub : t₁ - (t₁ - T) = T := by ring
    rw [hsub] at hd
    have hb := hyM (t₁ - T)
    have hp := Real.exp_pos (-(Real.pi ^ 2 / 40) * T)
    have h2 : Real.exp (-(Real.pi ^ 2 / 40) * T) *
        (1 + ‖cellRawTrace (fibreSeriesJet data.r ξ) (t₁ - T)‖ ^ 2) ≤
        Real.exp (-(Real.pi ^ 2 / 40) * T) * (1 + M) :=
      mul_le_mul_of_nonneg_left (by linarith) hp.le
    have hy1 := sq_nonneg ‖cellRawTrace (fibreSeriesJet data.r ξ) t₁‖
    linarith

end AVRegularity.CycleWords.Assembly
end
end
end

section
section
/-! # The `L²` layer of the transverse estimate: the graph of a transverse drift is transverse on the whole disc

If the drift is invariant along `e_∥` (a shear), the transverse projection `Π` commutes with the
homogeneous cell evolution, so `d = h - Πh` is again a homogeneous solution, where `h` is the
slow mode `e^{∫λ}(1 + r)`. It is mean zero (`Π` keeps the mean), so it decays at the rate
`2π² - |θ|²` (`cellWeak_small_mean_decay` with `δ = 0`), while the phase decays at most at
`σ ≤ π²/16`. Hence `‖r - Πr‖² ≤ 4(C_g|ξ|)² e^{-π²T}` for every `T`: `r = Πr`, and its
continuous value is transverse. No contraction smallness of `|ξ|` is used; the separation
condition `(2 + C_w C_g)|ξ|² ≤ π²/16` is enough. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal

namespace AVRegularity.CycleWords.Assembly

/-- The dual derivative without sources is linear in the state. -/
theorem cellDualDerivative_sub_zero (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (u w : TorusHk 1 ℂ) :
    cellDualDerivative C hG V hv hb t u 0 0 - cellDualDerivative C hG V hv hb t w 0 0 =
      cellDualDerivative C hG V hv hb t (u - w) 0 0 := by
  have hs : cellSourceFunctional C.θ 0 0 = 0 := by
    ext z
    simp [cellSourceFunctional]
  simp only [cellDualDerivative, hs, add_zero, map_sub]

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # Zero-amplitude word, part 4: a level after a zero letter, or after a zero level, vanishes

For a frame of a word piece, the level `k + 1` vanishes on the piece when the letter `k` has
`θ = 0` (its coefficients vanish for almost every time) or when the level `k` vanishes (the letter
acts on `0`). -/

@[expose] public noncomputable section

open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleWords

namespace AVRegularity.CycleWords.Assembly

universe u v

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D Nw : ℕ}

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- The jet array of a vanishing element vanishes almost everywhere. -/
theorem zawJetArray_ae_zero {N : ℕ} (κ : Fin (N + 1) → ι → ℕ)
    (U : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (i i' : Fin (N + 1) × ι) (d : admissibleOrders (fun p => κ p.1 p.2) D i i')
    (hU : U i' = 0) : ∀ᵐ z ∂(volume : Measure (Vec 2)), wordChainJetArray κ U i i' d z = 0 := by
  have hj : d.1 - 1 ≤ κ i'.1 i'.2 + 1 := by
    have hd := (Finset.mem_filter.mp d.2).2
    dsimp only at hd
    omega
  have hae := ae_all_iff.mpr fun word : DerivativeWord2 (d.1 - 1) =>
    planeJetOrder_zero_ae (E := h i'.2) (K := κ i'.1 i'.2 + 1) hj word
  filter_upwards [hae] with z hz
  apply PiLp.ext
  intro word
  have := hz word
  simp only [planeJetOrder, hj, dite_true] at this
  simp only [wordChainJetArray, hU] 
  simpa using this

/-- The `w`-lift of a vanishing level vanishes for almost every time. -/
theorem zawFrame_w_zero {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (j : Fin (Nw + 1)) (x : ι)
    (hu : ∀ t ∈ Icc F.a F.b, planeValue (F.u j x t) =ᵐ[volume] 0) :
    ∀ᵐ r ∂volume.restrict (Icc F.a F.b), F.w j x r = 0 := by
  have hsol := (isPlaneChain_iff_from _ _ _ _ _ _ _ _ _).mp F.solution
  have h3 := hsol.2.2.1 (j, x)
  filter_upwards [h3, ae_restrict_mem measurableSet_Icc] with r hr hrm
  apply planeHk_eq_of_planeValue_ae
  have h1 : planeValue (truncatePlaneHk (Nat.le_succ (F.κ j x)) (F.w j x r)) = planeValue (F.w j x r) := by
    simp only [planeValue]
    exact planeJetOrder_truncate (Nat.le_succ _) (Nat.zero_le _) _ _
  have h2 : planeValue (F.u j x r) = planeValue (truncatePlaneHk (Nat.le_succ (F.κ j x)) (F.w j x r)) := by
    rw [← hr]
  rw [← h1, ← h2]
  exact (hu r hrm).trans (planeValue_zero_ae _).symm

/-- **A level after a zero letter, or after a zero level, vanishes on the piece.** -/
theorem zawFrame_level_succ {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (k : Fin Nw)
    (hk : (F.letters k).theta = 0 ∨
      ∀ x, ∀ t ∈ Icc F.a F.b, planeValue (F.u k.castSucc x t) =ᵐ[volume] 0) (x : ι) :
    ∀ t ∈ Icc F.a F.b, planeValue (F.u k.succ x t) =ᵐ[volume] 0 := by
  classical
  have hsol := (isPlaneChain_iff_from _ _ _ _ _ _ _ _ _).mp F.solution
  have hM : ∀ t (y : Vec 2), ∑ i, F.v t y i ^ 2 ≤ (K.Cw / Real.sqrt F.η) ^ 2 := by
    intro t y
    have hη := Real.sqrt_pos.mpr F.piece.hη
    have h1 := F.piece.hvw t y
    have h2 : Real.sqrt (∑ i, F.v t y i ^ 2) ≤ K.Cw / Real.sqrt F.η := by
      rw [le_div_iff₀ hη]
      linarith
    calc ∑ i, F.v t y i ^ 2 = Real.sqrt (∑ i, F.v t y i ^ 2) ^ 2 :=
          (Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)).symm
      _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
  refine zawLevel_succ_zero F.piece.hD F.G F.piece.hGm F.letters F.X₀ (F.ϖ * F.ηg) F.κ F.a F.b
    F.v F.piece.hv _ hM (fun p => chainDatum F.κ F.f p.1 p.2) (fun p => F.u p.1 p.2)
    (fun p => F.w p.1 p.2) hsol k x (by simp [chainDatum]) ?_
  rcases hk with hθ | hu
  · have hc := (ae_restrict_iff' measurableSet_Icc).mpr
      (zawCoeff_ae_all F.π F.piece.hπ (F.letters k) (Icc F.a F.b) _ _ (F.piece.hlet k) hθ)
    filter_upwards [hc] with r hr
    refine Filter.Eventually.of_forall fun z => zawPreviousFlux_eq_zero _ _ _ _ _ k x r z ?_
    intro u d
    have : slowEvalCoefficient
        (fun f z => taylorSlow (if (F.letters k).positive then 1 else 0)
          (F.letters k).slow f F.X₀ ((F.ϖ * F.ηg) • z))
        ((F.letters k).edge x u ⟨d.1, (Finset.mem_filter.mp d.2).1⟩) r z = 0 := by
      refine zawSlowEvalCoefficient_eq_zero
        (fun f z => taylorSlow (if (F.letters k).positive then 1 else 0)
          (F.letters k).slow f F.X₀ ((F.ϖ * F.ηg) • z))
        (fun z' => zaw_taylorSlow_zero _ _ _ _) _ r z ?_
      intro γ hγ
      obtain ⟨i, rfl⟩ := List.get_of_mem hγ
      by_cases hm : (((F.letters k).edge x u ⟨d.1, (Finset.mem_filter.mp d.2).1⟩).get i).map = 0
      · exact Or.inl hm
      · exact Or.inr fun w X z' => hr x u _ i hm w X z'
    rw [this]
    rfl
  · have hw := fun u => zawFrame_w_zero F k.castSucc u (hu u)
    have hw' : ∀ᵐ r ∂volume.restrict (Icc F.a F.b), ∀ u, F.w k.castSucc u r = 0 :=
      ae_all_iff.mpr hw
    filter_upwards [hw'] with r hr
    have hj : ∀ᵐ z ∂(volume : Measure (Vec 2)), ∀ (u : ι)
        (d : admissibleOrders (fun p => F.κ p.1 p.2) D (k.succ, x) (k.castSucc, u)),
        wordChainJetArray F.κ (fun p => F.w p.1 p.2 r) (k.succ, x) (k.castSucc, u) d z = 0 :=
      ae_all_iff.mpr fun u => ae_all_iff.mpr fun d =>
        zawJetArray_ae_zero F.κ (fun p => F.w p.1 p.2 r) _ _ d (hr u)
    filter_upwards [hj] with z hz
    refine zawPreviousFlux_eq_zero _ _ _ _ _ k x r z ?_
    intro u d
    rw [hz u d]
    exact map_zero _

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # A word of zero amplitude has no terminal level

Some letter `l` has `θ_l = 0` (`wordTheta` is a product and `0 < η_g`). The level `l + 1` vanishes
(`zawFrame_level_succ`, coefficients vanish for almost every time), and every later level vanishes
because the next letter acts on `0`. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory Set

namespace AVRegularity.CycleWords.Assembly

universe u v

/-- **A word of zero amplitude has no terminal level.** -/
theorem zeroAmplitudeWord : ZeroAmplitudeWordStatement.{u, v} := by
  intro K g₁ ι _ h _ _ _ _ _ _ D Nw F hθ x t ht
  classical
  obtain ⟨l, -, hl⟩ := Finset.prod_eq_zero_iff.mp hθ
  have hl0 : (F.letters l).theta = 0 := by
    rcases mul_eq_zero.mp hl with h0 | h0
    · exact h0
    · split_ifs at h0 with hp
      · exact absurd h0 F.piece.hηg.ne'
      · exact absurd h0 one_ne_zero
  have key : ∀ m : ℕ, l.val + 1 ≤ m → ∀ hm : m ≤ Nw, ∀ y, ∀ s ∈ Icc F.a F.b,
      planeValue (F.u ⟨m, Nat.lt_succ_of_le hm⟩ y s) =ᵐ[volume] 0 := by
    intro m hlm
    induction m, hlm using Nat.le_induction with
    | base =>
      intro hm y
      exact zawFrame_level_succ F l (Or.inl hl0) y
    | succ m hlm ih =>
      intro hm y
      have hmN : m < Nw := hm
      exact zawFrame_level_succ F ⟨m, hmN⟩
        (Or.inr fun y' => ih (Nat.le_of_lt hmN) y') y
  exact key Nw (Nat.succ_le_of_lt l.isLt) le_rfl x t ht

end AVRegularity.CycleWords.Assembly
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! # The `L²` layer of the transverse estimate: the adjoint solutions

Let `Ψ` solve the time-reversed (adjoint) fibre equation on `[-t, -s]`.

* If the drift is invariant along `e_∥` and `Ψ(-t)` is transverse, `Ψ` stays transverse
  (`cellActualWeak_transverse_invariant`).
* The pairing of `Ψ(-σ)` with the forward slow mode `e^{∫λ}(1 + r(σ))` is conserved
  (`cellWeakAdjointPairing_forced`). So the fast class
  `∫(1 + r(t))Ψ(-t) = 0` propagates to every `σ ∈ [s, t]`, where it gives
  `|⟨Ψ⟩| = |∫ r Ψ| ≤ ‖r‖‖Ψ‖ ≤ ‖Ψ‖/3` (`graphTrace_l2_small`). The `L²` energy then decays at the
  rate `2π²(2/3)² - |θ|² ≥ 8π²/9 - |ξ|²` (`revCurve_fast_decay`), with no smallness of `|ξ|`
  beyond the separation condition `(2 + C_w C_g)|ξ|² ≤ π²/16` and no transversality. -/

variable {K : ScalarConstants} {η t₀ S : ℝ} {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
  {v : ℝ → Vec 2 → Vec 2}

/-- **The pairing with the forward slow mode is conserved** (Hilbert form). For a reversed
curve `u` on `[-t, -s]`, `⟨1 + r(σ), u(-σ)⟩ = e^{∫_σ^t λ}⟨1 + r(t), u(-t)⟩` (bilinear). -/
theorem revCurve_pairing (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCg : 0 ≤ K.Cg)
    (hCw : 0 ≤ K.Cw) (hG : IsCellMetric (fun t _ => G t)) (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ K.Cw)
    (data : FibreScalarData K η G v t₀ S) (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ < K.ξ0)
    {s t : ℝ} (V : ℝ) (hb' : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2)
    {u : ℝ → ComplexCellL2} {slice : ℝ → TorusHk 1 ℂ}
    (hu : CellWeakHilbertCurve (-t) (-s) u slice (fun τ =>
      cellDualDerivative ⟨fun s _ => G (-s), fun s x => -v (-s) x,
        fun j => -((fun k => (Real.sqrt η : ℂ) * ξ k) j), 0⟩ (cellMetric_timeReverse hG) V
        (cellDrift_timeReverse hv).1 hb' τ (slice τ) 0 0)) :
    ∀ σ ∈ Icc s t, cellComplexPair (cellRawTrace (fibreSeriesJet data.r ξ) σ + cellConstantCLM 1)
        (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u (-σ))) =
      Complex.exp (∫ τ in σ..t, fibreSeriesC data.lam ξ τ) *
        cellComplexPair (cellRawTrace (fibreSeriesJet data.r ξ) t + cellConstantCLM 1)
          (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u (-t))) := by
  have hV : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2 := fun t x => by
    simpa only [neg_neg, Pi.neg_apply, neg_sq] using hb' (-t) x
  set θ : Fin 2 → ℂ := fun k => (Real.sqrt η : ℂ) * ξ k with hθdef
  have href := hu.reflected_adjoint (fun t _ => G t) hG hv V hV θ
  intro σ hσ
  have hcurve := fibreScalarData_graph_homogeneous_evolution K η t₀ S hη0 hη hCg hCw G hG v hv
    hm hw data V hV ξ hξ hσ.2
  dsimp only at hcurve
  have hp := cellWeakAdjointPairing_forced hσ.2 ⟨fun t _ => G t, v, θ, 0⟩ hG V hv hV
    (S := fun _ => 0) (F := fun _ => 0) hcurve (href.mono (Icc_subset_Icc hσ.1 le_rfl))
  have hz : ∀ z, cellComplexSource θ 0 0 z = 0 := fun z => cellComplexSource_zero θ z
  simp only [hz, intervalIntegral.integral_zero, cellComplexPair_scalar_left] at hp
  rw [intervalIntegral.integral_same, Complex.exp_zero, one_mul] at hp
  linear_combination -hp

/-- **The fast class of the adjoint decays in `L²`** (Hilbert form). -/
theorem revCurve_fast_decay (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCg : 0 ≤ K.Cg)
    (hCw : 0 ≤ K.Cw) (hG : IsCellMetric (fun t _ => G t)) (hv : IsCellDrift v)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ K.Cw)
    (data : FibreScalarData K η G v t₀ S) (ξ : Fin 2 → ℂ) (hreal : ∀ i, (ξ i).im = 0)
    (hξ : fibreNorm ξ < K.ξ0) (hsep : (2 + K.Cw * K.Cg) * fibreNorm ξ ^ 2 ≤ Real.pi ^ 2 / 16)
    {s t : ℝ} (hst : s ≤ t) (V : ℝ) (hb' : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2)
    {u : ℝ → ComplexCellL2} {slice : ℝ → TorusHk 1 ℂ}
    (hu : CellWeakHilbertCurve (-t) (-s) u slice (fun τ =>
      cellDualDerivative ⟨fun s _ => G (-s), fun s x => -v (-s) x,
        fun j => -((fun k => (Real.sqrt η : ℂ) * ξ k) j), 0⟩ (cellMetric_timeReverse hG) V
        (cellDrift_timeReverse hv).1 hb' τ (slice τ) 0 0))
    (hfast : cellComplexPair (cellRawTrace (fibreSeriesJet data.r ξ) t + cellConstantCLM 1)
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u (-t))) = 0) :
    Real.exp ((8 * Real.pi ^ 2 / 9 - fibreNorm ξ ^ 2) * (t - s)) *
        ‖u (-s)‖ ^ 2 ≤ ‖u (-t)‖ ^ 2 := by
  obtain ⟨hθr, hθn⟩ := realShift_facts hη ξ hreal
  set θ : Fin 2 → ℂ := fun k => (Real.sqrt η : ℂ) * ξ k with hθdef
  set tr := cellRawTrace (fibreSeriesJet data.r ξ) with htr
  set cj := cellFiberCLM Complex.conjCLE.toContinuousLinearMap with hcj
  -- the fast class at every intermediate time
  have hclass : ∀ σ ∈ Icc s t, cellComplexPair (tr σ + cellConstantCLM 1) (cj (u (-σ))) = 0 := by
    intro σ hσ
    rw [revCurve_pairing hη0 hη hCg hCw hG hv hm hw data ξ hξ V hb' hu σ hσ, hfast, mul_zero]
  -- the mean is small along the fast class
  have hmean : ∀ τ ∈ Icc (-t) (-s), ‖cellMeanCLM (u τ)‖ ≤ (1 / 3) * ‖u τ‖ := by
    intro τ hτ
    have hσ : -τ ∈ Icc s t := ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
    have h0 := hclass (-τ) hσ
    rw [neg_neg] at h0
    have h1 := cellComplexPair_conjugate (tr (-τ) + cellConstantCLM 1) (cj (u τ))
    rw [h0, star_zero, hcj, cellFiberConj_involutive] at h1
    have h2 := cellComplexPair_symm (u τ) (cj (tr (-τ) + cellConstantCLM 1))
    rw [h1, star_zero, map_add, cellFiberConj_constant, star_one,
      cellComplexPair_add_right, cellComplexPair_one] at h2
    have hm' : cellMeanCLM (u τ) = -cellComplexPair (u τ) (cj (tr (-τ))) := by
      rw [cellMeanCLM_apply]
      linear_combination h2
    have hsmall := graphTrace_l2_small hη0 hη hCg hCw hG hv hm hw data ξ hreal hξ hsep (-τ)
    have hnr : ‖tr (-τ)‖ ≤ 1 / 3 := by
      have h0' := norm_nonneg (tr (-τ))
      nlinarith
    rw [hm', norm_neg]
    calc ‖cellComplexPair (u τ) (cj (tr (-τ)))‖
        ≤ ‖u τ‖ * ‖cj (tr (-τ))‖ := cellComplexPair_norm_le _ _
      _ = ‖u τ‖ * ‖tr (-τ)‖ := by rw [hcj, cellFiberConj_norm]
      _ ≤ ‖u τ‖ * (1 / 3) := mul_le_mul_of_nonneg_left hnr (norm_nonneg _)
      _ = (1 / 3) * ‖u τ‖ := by ring
  have hθr' : ∀ j, star (-θ j) = -θ j := fun j => by rw [star_neg, hθr j]
  have hdec := cellWeak_small_mean_decay (neg_le_neg hst) (cellMetric_timeReverse hG)
    (cellDrift_timeReverse hv) V hb' (fun j => -θ j) hθr' (1 / 3) (by norm_num) hu hmean
  have hθn' : ∑ j, ‖-θ j‖ ^ 2 ≤ fibreNorm ξ ^ 2 := by
    simpa only [norm_neg] using hθn
  have hexp : Real.exp ((8 * Real.pi ^ 2 / 9 - fibreNorm ξ ^ 2) * (t - s)) ≤
      Real.exp ((2 * Real.pi ^ 2 * (1 - 1 / 3) ^ 2 - ∑ j, ‖-θ j‖ ^ 2) * (-s - -t)) := by
    apply Real.exp_le_exp.mpr
    have hts : 0 ≤ t - s := sub_nonneg.mpr hst
    have hrw : -s - -t = t - s := by ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_right (by nlinarith) hts
  calc Real.exp ((8 * Real.pi ^ 2 / 9 - fibreNorm ξ ^ 2) * (t - s)) * ‖u (-s)‖ ^ 2
      ≤ Real.exp ((2 * Real.pi ^ 2 * (1 - 1 / 3) ^ 2 - ∑ j, ‖-θ j‖ ^ 2) * (-s - -t)) *
          ‖u (-s)‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hexp (sq_nonneg _)
    _ ≤ ‖u (-t)‖ ^ 2 := hdec

end AVRegularity.CycleWords.Assembly
end
end
