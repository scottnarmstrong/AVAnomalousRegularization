-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Assembly.OcDiagonal
public import AVRegularity.CycleComparison.Reconstruction.PulseTail
public import AVRegularity.CycleComparison.Residual.TailDiff.Main
import AVRegularity.CycleComparison.Reconstruction.TailSample
public import AVRegularity.CycleComparison.Residual.ChartTransport.Part1
import AVRegularity.CycleComparison.Reconstruction.Tested
import AVRegularity.CycleComparison.Reconstruction.PiolaTested
import AVRegularity.CycleComparison.Lift.SettingConstructedLiftSequence
import AVRegularity.CycleComparison.Lift.SettingTailFluxCoefficientCellBound
import AVRegularity.CycleComparison.Reconstruction.Orders
import AVRegularity.CycleComparison.Reconstruction.PulseIdentity
import AVRegularity.CycleComparison.Residual.TailJets
import AVRegularity.CycleReference.CoreFlux
import AVRegularity.CycleReference.TransitionTaylorBounds
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public noncomputable section

section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleComparison.Assembly

/-! **The covariance of the reference flux is small at the window scale**.
`coarse_flux_fields` with the quantitative smallness `‖H_cov‖ ≤ C₂ R² E^δ` exposed (`coarse_flux_small`): the coarse defect bound needs
`ω = ‖H_cov‖/R² ≲ E^δ`, which `cov_small` (`ω ≤ 1`) alone does not give. -/

/-- The covariance budget without the final smallness: `≤ Bτ'' · C(80 + 16KC) e`. -/
theorem covariance_budget_small {H B C K τ τ' τ'' r e : ℝ} (hH : H ≤ C * B) (hB : 0 < B)
    (hC : 0 ≤ C) (hτ0 : 0 ≤ τ) (hτ'0 : 0 ≤ τ') (hτ'' : 0 < τ'') (hr0 : 0 ≤ r)
    (hτ : τ ≤ τ'' * e) (hτ' : τ' ≤ τ'' * e) (hr : r ≤ K * C * e) :
    16 * H * τ + 4 * H * (4 * τ'' * r + 16 * τ') ≤ B * τ'' * (C * (80 + 16 * K * C) * e) := by
  have hbr : 4 * τ + 4 * τ'' * r + 16 * τ' ≤ τ'' * e * (20 + 4 * K * C) := by
    have h1 : τ'' * r ≤ τ'' * (K * C * e) := mul_le_mul_of_nonneg_left hr hτ''.le
    linarith
  have hbr0 : 0 ≤ 4 * τ + 4 * τ'' * r + 16 * τ' := by positivity
  calc 16 * H * τ + 4 * H * (4 * τ'' * r + 16 * τ')
      = 4 * H * (4 * τ + 4 * τ'' * r + 16 * τ') := by ring
    _ ≤ 4 * (C * B) * (τ'' * e * (20 + 4 * K * C)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hH (by norm_num)) hbr hbr0 (by positivity)
    _ = B * τ'' * (C * (80 + 16 * K * C) * e) := by ring

/-- **The reference flux fields with the smallness of the covariance.** -/
theorem coarse_flux_small (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s)
    (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ)
    (hζ : IsFastProfile ζ) :
    ∃ (Λ₀ : ℕ) (C₂ : ℝ), 128 ≤ Λ₀ ∧ 0 ≤ C₂ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ (M' : ℕ) (κ : ℕ → ℝ), IsOCBandChain α q Λ ζ M' κ → ∀ m : ℕ, 2 ≤ m → m ≤ M' →
      ∀ ν B : ℝ, κ m = ν → κ (m - 1) = B → ∀ t₀ t₁ : ℝ,
        (∀ (t : ℝ) (i j : Fin 2), ocRefFlux α q Λ ζ m ν t i j = ocRefFlux α q Λ ζ m ν t j i) ∧
        (∀ i j : Fin 2, Measurable fun t => ocRefFlux α q Λ ζ m ν t i j) ∧
        matrixSupNorm (fun t => ocRefFlux α q Λ ζ m ν t - B • (1 : Matrix (Fin 2) (Fin 2) ℝ))
          t₀ t₁ ≠ ⊤ ∧
        matrixSupNorm (covarianceMatrix (ocRefFlux α q Λ ζ m ν) B t₀) t₀ t₁ ≤
          ENNReal.ofReal (Real.sqrt (B * ocTauPP α q Λ m) ^ 2) ∧
        matrixSupNorm (covarianceMatrix (ocRefFlux α q Λ ζ m ν) B t₀) t₀ t₁ ≤
          ENNReal.ofReal (C₂ * Real.sqrt (B * ocTauPP α q Λ m) ^ 2 *
            ocEpsilon q Λ (m - 1) ^ ocDelta α q) := by
  obtain ⟨C, hC, Λ₁, hΛ₁, hlaws⟩ := scale_laws α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨K, hK0, hprim⟩ := AVRegularity.CycleReference.refFlux_covariance_primitive hζ
  have hδ : 0 < ocDelta α q :=
    (AVRegularity.Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  have hCpos : 0 < C := lt_of_lt_of_le one_pos hC
  have hM : 0 ≤ C * (80 + 16 * K * C) := by positivity
  refine ⟨max Λ₁ ⌈(C * (80 + 16 * K * C) + 1) ^ (1 / ocDelta α q)⌉₊, C * (80 + 16 * K * C),
    hΛ₁.trans (le_max_left _ _), hM, ?_⟩
  intro Λ hΛ M' κ hband m hm2 hmM ν B hν hB t₀ t₁
  have hΛ₁' : Λ₁ ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛ₂ : ⌈(C * (80 + 16 * K * C) + 1) ^ (1 / ocDelta α q)⌉₊ ≤ Λ :=
    (le_max_right _ _).trans hΛ
  have h128 : 128 ≤ Λ := hΛ₁.trans hΛ₁'
  have hΛ1 : 1 ≤ Λ := by omega
  have hΛpos : (0 : ℝ) < (Λ : ℝ) := by exact_mod_cast (show 0 < Λ by omega)
  have hL := hlaws Λ hΛ₁' M' κ hband m hm2 hmM ν B hν hB
  have hνpos : 0 < ν := hL.ν_pos
  have hBpos : 0 < B := lt_of_lt_of_le hνpos hL.ν_le
  refine ⟨?_, fun i j => AVRegularity.CycleReference.refFlux_entry_measurable hΛ1 hζ hνpos i j,
    ?_, ?_, ?_⟩
  · -- symmetry: the reference flux is diagonal
    intro t
    have hd := AVRegularity.CycleReference.refFlux_diagonal (α := α) (q := q) (m := m)
      (ζ := ζ) (t := t) hΛ1 hζ hνpos
    refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨rfl, ?_⟩, Fin.forall_fin_two.2 ⟨?_, rfl⟩⟩
    · rw [hd.1, hd.2]
    · rw [hd.1, hd.2]
  · -- boundedness of `J - B I`
    have hbound : ∀ (t : ℝ) (i j : Fin 2),
        |(ocRefFlux α q Λ ζ m ν t - B • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j| ≤
          ν + ocHStar α q Λ m ν + B := by
      intro t i j
      rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      have h1 := refFlux_entry_abs_le (α := α) (q := q) (m := m) (ζ := ζ) hΛ1 hζ hνpos t i j
      have hone : |(1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 1 := by
        rw [Matrix.one_apply]
        split_ifs <;> simp
      have h2 : |B * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ B := by
        rw [abs_mul, abs_of_pos hBpos]
        calc B * |(1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ B * 1 :=
              mul_le_mul_of_nonneg_left hone hBpos.le
          _ = B := mul_one B
      calc |ocRefFlux α q Λ ζ m ν t i j - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j|
          = |ocRefFlux α q Λ ζ m ν t i j + -(B * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j)| := by
            rw [sub_eq_add_neg]
        _ ≤ |ocRefFlux α q Λ ζ m ν t i j| + |-(B * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j)| :=
            abs_add_le _ _
        _ = |ocRefFlux α q Λ ζ m ν t i j| + |B * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| := by
            rw [abs_neg]
        _ ≤ ν + ocHStar α q Λ m ν + B := add_le_add h1 h2
    have hle : matrixSupNorm
        (fun t => ocRefFlux α q Λ ζ m ν t - B • (1 : Matrix (Fin 2) (Fin 2) ℝ)) t₀ t₁ ≤
          ENNReal.ofReal (ν + ocHStar α q Λ m ν + B) := by
      unfold matrixSupNorm
      exact iSup₂_le fun t _ => iSup_le fun i => iSup_le fun j =>
        ENNReal.ofReal_le_ofReal (hbound t i j)
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  · -- the covariance anchored at `t₀`
    have hE : 0 < ocEpsilon q Λ (m - 1) :=
      (AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 h128).1
    have hE1 : ocEpsilon q Λ (m - 1) ≤ 1 :=
      (AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 h128).2.1
    have he : 0 < ocEpsilon q Λ m := (AVRegularity.Scales.epsilon_basic (m := m) hq.1 h128).1
    have hEΛ : ocEpsilon q Λ (m - 1) ≤ (Λ : ℝ)⁻¹ :=
      AVRegularity.CycleReference.epsilon_le_inv_separation (m := m - 1) hq.1 h128 (by omega)
    have hτ'' : 0 < ocTauPP α q Λ m := AVRegularity.Construction.Stream.ocTauPP_pos hΛ1
    have hτ : 0 < ocTau α q Λ m := AVRegularity.Construction.Stream.ocTau_pos hΛ1
    have hts := AVRegularity.Scales.admissible_time_scale_facts hα₀ hα₁ hs₀ hs₁ hq h128
      (m := m) (by omega)
    have hL5 : (5 : ℝ) ≤ (ocL α q Λ m : ℝ) := by exact_mod_cast hts.1
    have hLpos : (0 : ℝ) < (ocL α q Λ m : ℝ) := by linarith
    have hL1 : (1 : ℝ) ≤ (ocL α q Λ m : ℝ) := by linarith
    -- the block times against `τ'' E^δ`
    have hEδ : 0 < ocEpsilon q Λ (m - 1) ^ ocDelta α q := Real.rpow_pos_of_pos hE _
    have hcancel : ocEpsilon q Λ (m - 1) ^ ocDelta α q *
        ocEpsilon q Λ (m - 1) ^ (-ocDelta α q) = 1 := by
      rw [← Real.rpow_add hE, add_neg_cancel, Real.rpow_zero]
    have hEL : 1 ≤ ocEpsilon q Λ (m - 1) ^ ocDelta α q * (ocL α q Λ m : ℝ) := by
      have h0 : 0 ≤ ocEpsilon q Λ (m - 1) ^ (-ocDelta α q) := (Real.rpow_pos_of_pos hE _).le
      have h1 : ocEpsilon q Λ (m - 1) ^ (-ocDelta α q) ≤ (ocL α q Λ m : ℝ) := by
        linarith [hts.2.1]
      calc (1 : ℝ) = ocEpsilon q Λ (m - 1) ^ ocDelta α q *
            ocEpsilon q Λ (m - 1) ^ (-ocDelta α q) := hcancel.symm
        _ ≤ ocEpsilon q Λ (m - 1) ^ ocDelta α q * (ocL α q Λ m : ℝ) :=
            mul_le_mul_of_nonneg_left h1 hEδ.le
    have hτP : ocTauP α q Λ m ≤ ocTauPP α q Λ m * ocEpsilon q Λ (m - 1) ^ ocDelta α q := by
      unfold ocTauP
      rw [div_le_iff₀ hLpos]
      calc ocTauPP α q Λ m = ocTauPP α q Λ m * 1 := (mul_one _).symm
        _ ≤ ocTauPP α q Λ m * (ocEpsilon q Λ (m - 1) ^ ocDelta α q * (ocL α q Λ m : ℝ)) :=
            mul_le_mul_of_nonneg_left hEL hτ''.le
        _ = ocTauPP α q Λ m * ocEpsilon q Λ (m - 1) ^ ocDelta α q * (ocL α q Λ m : ℝ) :=
            (mul_assoc _ _ _).symm
    have hτP0 : 0 ≤ ocTauP α q Λ m := by
      unfold ocTauP
      exact div_nonneg hτ''.le hLpos.le
    have hτle : ocTau α q Λ m ≤ ocTauPP α q Λ m * ocEpsilon q Λ (m - 1) ^ ocDelta α q := by
      have heq : ocTau α q Λ m = ocTauP α q Λ m / (ocL α q Λ m : ℝ) := by
        unfold ocTau ocTauP
        rw [div_div, sq]
      rw [heq]
      exact (div_le_self hτP0 hL1).trans hτP
    -- the memory rate against `C⁻¹ E^{-δ}`
    have hℓ : 0 < ocEll q Λ m ν := by
      unfold ocEll
      exact div_pos he (Real.sqrt_pos.2 hνpos)
    have hμτ : ocMu q Λ m ν * ocTau α q Λ m =
        4 * Real.pi ^ 2 * (ocTau α q Λ m / ocEll q Λ m ν ^ 2) := by
      have hℓ2 : ocEll q Λ m ν ^ 2 ≠ 0 := (pow_pos hℓ 2).ne'
      calc ocMu q Λ m ν * ocTau α q Λ m
          = ocMu q Λ m ν * (ocEll q Λ m ν ^ 2 * (ocTau α q Λ m / ocEll q Λ m ν ^ 2)) := by
            rw [mul_div_cancel₀ _ hℓ2]
        _ = ocMu q Λ m ν * ocEll q Λ m ν ^ 2 * (ocTau α q Λ m / ocEll q Λ m ν ^ 2) :=
            (mul_assoc _ _ _).symm
        _ = 4 * Real.pi ^ 2 * (ocTau α q Λ m / ocEll q Λ m ν ^ 2) := by
            rw [ocMu_mul_ocEll_sq hΛ1 hνpos]
    have hπ : 1 ≤ 4 * Real.pi ^ 2 := by nlinarith only [Real.pi_gt_three]
    have hlow : C⁻¹ * ocEpsilon q Λ (m - 1) ^ (-ocDelta α q) ≤
        ocMu q Λ m ν * ocTau α q Λ m := by
      have h1 : ocEpsilon q Λ (m - 1) ^ (-ocDelta α q) ≤
          ocEpsilon q Λ (m - 1) ^ (-(4 * ocDelta α q)) :=
        Real.rpow_le_rpow_of_exponent_ge hE hE1 (by linarith)
      have h2 : 0 ≤ ocTau α q Λ m / ocEll q Λ m ν ^ 2 := div_nonneg hτ.le (sq_nonneg _)
      rw [hμτ]
      calc C⁻¹ * ocEpsilon q Λ (m - 1) ^ (-ocDelta α q)
          ≤ C⁻¹ * ocEpsilon q Λ (m - 1) ^ (-(4 * ocDelta α q)) :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hCpos.le)
        _ ≤ ocTau α q Λ m / ocEll q Λ m ν ^ 2 := hL.quiet_ge
        _ ≤ 4 * Real.pi ^ 2 * (ocTau α q Λ m / ocEll q Λ m ν ^ 2) :=
            le_mul_of_one_le_left h2 hπ
    have hlowpos : 0 < C⁻¹ * ocEpsilon q Λ (m - 1) ^ (-ocDelta α q) :=
      mul_pos (inv_pos.2 hCpos) (Real.rpow_pos_of_pos hE _)
    have hr : K / (ocMu q Λ m ν * ocTau α q Λ m) ≤
        K * C * ocEpsilon q Λ (m - 1) ^ ocDelta α q := by
      calc K / (ocMu q Λ m ν * ocTau α q Λ m)
          ≤ K / (C⁻¹ * ocEpsilon q Λ (m - 1) ^ (-ocDelta α q)) :=
            div_le_div_of_nonneg_left hK0 hlowpos hlow
        _ = K * C * ocEpsilon q Λ (m - 1) ^ ocDelta α q := by
            rw [div_eq_mul_inv, mul_inv, inv_inv, Real.rpow_neg hE.le, inv_inv]
            ring
    have hr0 : 0 ≤ K / (ocMu q Λ m ν * ocTau α q Λ m) :=
      div_nonneg hK0 (hlowpos.trans_le hlow).le
    have hsmall : C * (80 + 16 * K * C) * ocEpsilon q Λ (m - 1) ^ ocDelta α q ≤ 1 :=
      mul_rpow_le_one_of_small hE hδ hΛpos hEΛ hM
        ((Nat.le_ceil ((C * (80 + 16 * K * C) + 1) ^ (1 / ocDelta α q))).trans
          (Nat.cast_le.2 hΛ₂))
    have hbudget := covariance_budget_le hL.hstar_le hBpos hCpos.le hτ.le hτP0 hτ'' hr0 hτle
      hτP hr hsmall
    -- the mean flux is the coarse diffusivity
    have hBmean : B = ocMeanFlux α q Λ ζ m ν := by
      rw [← hB, ← hν]
      exact hband.2 m (by omega) hmM
    rw [Real.sq_sqrt (mul_nonneg hBpos.le hτ''.le)]
    unfold matrixSupNorm
    refine iSup₂_le fun t _ => iSup_le fun i => iSup_le fun j => ENNReal.ofReal_le_ofReal ?_
    have hprim' := hprim α q Λ m hΛ1 ν hνpos t₀ t i j
    rw [← hBmean] at hprim'
    exact hprim'.trans hbudget

  · -- the covariance anchored at `t₀`, with the smallness
    have hE : 0 < ocEpsilon q Λ (m - 1) :=
      (AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 h128).1
    have hE1 : ocEpsilon q Λ (m - 1) ≤ 1 :=
      (AVRegularity.Scales.epsilon_basic (m := m - 1) hq.1 h128).2.1
    have he : 0 < ocEpsilon q Λ m := (AVRegularity.Scales.epsilon_basic (m := m) hq.1 h128).1
    have hEΛ : ocEpsilon q Λ (m - 1) ≤ (Λ : ℝ)⁻¹ :=
      AVRegularity.CycleReference.epsilon_le_inv_separation (m := m - 1) hq.1 h128 (by omega)
    have hτ'' : 0 < ocTauPP α q Λ m := AVRegularity.Construction.Stream.ocTauPP_pos hΛ1
    have hτ : 0 < ocTau α q Λ m := AVRegularity.Construction.Stream.ocTau_pos hΛ1
    have hts := AVRegularity.Scales.admissible_time_scale_facts hα₀ hα₁ hs₀ hs₁ hq h128
      (m := m) (by omega)
    have hL5 : (5 : ℝ) ≤ (ocL α q Λ m : ℝ) := by exact_mod_cast hts.1
    have hLpos : (0 : ℝ) < (ocL α q Λ m : ℝ) := by linarith
    have hL1 : (1 : ℝ) ≤ (ocL α q Λ m : ℝ) := by linarith
    -- the block times against `τ'' E^δ`
    have hEδ : 0 < ocEpsilon q Λ (m - 1) ^ ocDelta α q := Real.rpow_pos_of_pos hE _
    have hcancel : ocEpsilon q Λ (m - 1) ^ ocDelta α q *
        ocEpsilon q Λ (m - 1) ^ (-ocDelta α q) = 1 := by
      rw [← Real.rpow_add hE, add_neg_cancel, Real.rpow_zero]
    have hEL : 1 ≤ ocEpsilon q Λ (m - 1) ^ ocDelta α q * (ocL α q Λ m : ℝ) := by
      have h0 : 0 ≤ ocEpsilon q Λ (m - 1) ^ (-ocDelta α q) := (Real.rpow_pos_of_pos hE _).le
      have h1 : ocEpsilon q Λ (m - 1) ^ (-ocDelta α q) ≤ (ocL α q Λ m : ℝ) := by
        linarith [hts.2.1]
      calc (1 : ℝ) = ocEpsilon q Λ (m - 1) ^ ocDelta α q *
            ocEpsilon q Λ (m - 1) ^ (-ocDelta α q) := hcancel.symm
        _ ≤ ocEpsilon q Λ (m - 1) ^ ocDelta α q * (ocL α q Λ m : ℝ) :=
            mul_le_mul_of_nonneg_left h1 hEδ.le
    have hτP : ocTauP α q Λ m ≤ ocTauPP α q Λ m * ocEpsilon q Λ (m - 1) ^ ocDelta α q := by
      unfold ocTauP
      rw [div_le_iff₀ hLpos]
      calc ocTauPP α q Λ m = ocTauPP α q Λ m * 1 := (mul_one _).symm
        _ ≤ ocTauPP α q Λ m * (ocEpsilon q Λ (m - 1) ^ ocDelta α q * (ocL α q Λ m : ℝ)) :=
            mul_le_mul_of_nonneg_left hEL hτ''.le
        _ = ocTauPP α q Λ m * ocEpsilon q Λ (m - 1) ^ ocDelta α q * (ocL α q Λ m : ℝ) :=
            (mul_assoc _ _ _).symm
    have hτP0 : 0 ≤ ocTauP α q Λ m := by
      unfold ocTauP
      exact div_nonneg hτ''.le hLpos.le
    have hτle : ocTau α q Λ m ≤ ocTauPP α q Λ m * ocEpsilon q Λ (m - 1) ^ ocDelta α q := by
      have heq : ocTau α q Λ m = ocTauP α q Λ m / (ocL α q Λ m : ℝ) := by
        unfold ocTau ocTauP
        rw [div_div, sq]
      rw [heq]
      exact (div_le_self hτP0 hL1).trans hτP
    -- the memory rate against `C⁻¹ E^{-δ}`
    have hℓ : 0 < ocEll q Λ m ν := by
      unfold ocEll
      exact div_pos he (Real.sqrt_pos.2 hνpos)
    have hμτ : ocMu q Λ m ν * ocTau α q Λ m =
        4 * Real.pi ^ 2 * (ocTau α q Λ m / ocEll q Λ m ν ^ 2) := by
      have hℓ2 : ocEll q Λ m ν ^ 2 ≠ 0 := (pow_pos hℓ 2).ne'
      calc ocMu q Λ m ν * ocTau α q Λ m
          = ocMu q Λ m ν * (ocEll q Λ m ν ^ 2 * (ocTau α q Λ m / ocEll q Λ m ν ^ 2)) := by
            rw [mul_div_cancel₀ _ hℓ2]
        _ = ocMu q Λ m ν * ocEll q Λ m ν ^ 2 * (ocTau α q Λ m / ocEll q Λ m ν ^ 2) :=
            (mul_assoc _ _ _).symm
        _ = 4 * Real.pi ^ 2 * (ocTau α q Λ m / ocEll q Λ m ν ^ 2) := by
            rw [ocMu_mul_ocEll_sq hΛ1 hνpos]
    have hπ : 1 ≤ 4 * Real.pi ^ 2 := by nlinarith only [Real.pi_gt_three]
    have hlow : C⁻¹ * ocEpsilon q Λ (m - 1) ^ (-ocDelta α q) ≤
        ocMu q Λ m ν * ocTau α q Λ m := by
      have h1 : ocEpsilon q Λ (m - 1) ^ (-ocDelta α q) ≤
          ocEpsilon q Λ (m - 1) ^ (-(4 * ocDelta α q)) :=
        Real.rpow_le_rpow_of_exponent_ge hE hE1 (by linarith)
      have h2 : 0 ≤ ocTau α q Λ m / ocEll q Λ m ν ^ 2 := div_nonneg hτ.le (sq_nonneg _)
      rw [hμτ]
      calc C⁻¹ * ocEpsilon q Λ (m - 1) ^ (-ocDelta α q)
          ≤ C⁻¹ * ocEpsilon q Λ (m - 1) ^ (-(4 * ocDelta α q)) :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hCpos.le)
        _ ≤ ocTau α q Λ m / ocEll q Λ m ν ^ 2 := hL.quiet_ge
        _ ≤ 4 * Real.pi ^ 2 * (ocTau α q Λ m / ocEll q Λ m ν ^ 2) :=
            le_mul_of_one_le_left h2 hπ
    have hlowpos : 0 < C⁻¹ * ocEpsilon q Λ (m - 1) ^ (-ocDelta α q) :=
      mul_pos (inv_pos.2 hCpos) (Real.rpow_pos_of_pos hE _)
    have hr : K / (ocMu q Λ m ν * ocTau α q Λ m) ≤
        K * C * ocEpsilon q Λ (m - 1) ^ ocDelta α q := by
      calc K / (ocMu q Λ m ν * ocTau α q Λ m)
          ≤ K / (C⁻¹ * ocEpsilon q Λ (m - 1) ^ (-ocDelta α q)) :=
            div_le_div_of_nonneg_left hK0 hlowpos hlow
        _ = K * C * ocEpsilon q Λ (m - 1) ^ ocDelta α q := by
            rw [div_eq_mul_inv, mul_inv, inv_inv, Real.rpow_neg hE.le, inv_inv]
            ring
    have hr0 : 0 ≤ K / (ocMu q Λ m ν * ocTau α q Λ m) :=
      div_nonneg hK0 (hlowpos.trans_le hlow).le
    have hsmall : C * (80 + 16 * K * C) * ocEpsilon q Λ (m - 1) ^ ocDelta α q ≤ 1 :=
      mul_rpow_le_one_of_small hE hδ hΛpos hEΛ hM
        ((Nat.le_ceil ((C * (80 + 16 * K * C) + 1) ^ (1 / ocDelta α q))).trans
          (Nat.cast_le.2 hΛ₂))
    have hbudget := covariance_budget_small hL.hstar_le hBpos hCpos.le hτ.le hτP0 hτ'' hr0 hτle
      hτP hr
    -- the mean flux is the coarse diffusivity
    have hBmean : B = ocMeanFlux α q Λ ζ m ν := by
      rw [← hB, ← hν]
      exact hband.2 m (by omega) hmM
    rw [Real.sq_sqrt (mul_nonneg hBpos.le hτ''.le),
      show C * (80 + 16 * K * C) * (B * ocTauPP α q Λ m) * ocEpsilon q Λ (m - 1) ^ ocDelta α q =
        B * ocTauPP α q Λ m * (C * (80 + 16 * K * C) * ocEpsilon q Λ (m - 1) ^ ocDelta α q) by
          ring]
    unfold matrixSupNorm
    refine iSup₂_le fun t _ => iSup_le fun i => iSup_le fun j => ENNReal.ofReal_le_ofReal ?_
    have hprim' := hprim α q Λ m hΛ1 ν hνpos t₀ t i j
    rw [← hBmean] at hprim'
    exact hprim'.trans hbudget

end AVRegularity.CycleComparison.Assembly
end

section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The reference flux minus the diffusivity is bounded by the diffusivity**. On
every window, `‖𝖩 - B I‖_∞ / B ≤ C₃` with a constant fixed before the level (`coarse_flux_offdiag`):
the entries of `𝖩` are at most `ν + h_*`, with `ν ≤ B` and `h_* ≤ C B` (the scale laws). This is
the quantity `k₀` of the coarse defect bound. -/

open AVRegularity.CycleComparison.Assembly in
/-- **The bound of `‖𝖩 - B I‖_∞ / B`.** -/
theorem coarse_flux_offdiag (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s)
    (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ)
    (hζ : IsFastProfile ζ) :
    ∃ (Λ₀ : ℕ) (C₃ : ℝ), 128 ≤ Λ₀ ∧ 0 ≤ C₃ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ (M' : ℕ) (κ : ℕ → ℝ), IsOCBandChain α q Λ ζ M' κ → ∀ m : ℕ, 2 ≤ m → m ≤ M' →
      ∀ ν B : ℝ, κ m = ν → κ (m - 1) = B → ∀ t₀ t₁ : ℝ,
        (matrixSupNorm (fun t => ocRefFlux α q Λ ζ m ν t - B • (1 : Matrix (Fin 2) (Fin 2) ℝ))
          t₀ t₁).toReal / B ≤ C₃ := by
  obtain ⟨C, hC, Λ₁, hΛ₁, hlaws⟩ := scale_laws α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₁, 2 + C, hΛ₁, by linarith, fun Λ hΛ M' κ hband m hm2 hmM ν B hν hB t₀ t₁ => ?_⟩
  have h128 : 128 ≤ Λ := hΛ₁.trans hΛ
  have hΛ1 : 1 ≤ Λ := by omega
  have hL := hlaws Λ hΛ M' κ hband m hm2 hmM ν B hν hB
  have hνpos : 0 < ν := hL.ν_pos
  have hBpos : 0 < B := lt_of_lt_of_le hνpos hL.ν_le
  have hbound : ∀ (t : ℝ) (i j : Fin 2),
      |(ocRefFlux α q Λ ζ m ν t - B • (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j| ≤
        ν + ocHStar α q Λ m ν + B := by
    intro t i j
    rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    have h1 := refFlux_entry_abs_le (α := α) (q := q) (m := m) (ζ := ζ) hΛ1 hζ hνpos t i j
    have hone : |(1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 1 := by
      rw [Matrix.one_apply]
      split_ifs <;> simp
    have h2 : |B * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ B := by
      rw [abs_mul, abs_of_pos hBpos]
      calc B * |(1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ B * 1 :=
            mul_le_mul_of_nonneg_left hone hBpos.le
        _ = B := mul_one B
    calc |ocRefFlux α q Λ ζ m ν t i j - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j|
        ≤ |ocRefFlux α q Λ ζ m ν t i j| + |B * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j| :=
          abs_sub _ _
      _ ≤ ν + ocHStar α q Λ m ν + B := add_le_add h1 h2
  have hle : matrixSupNorm
      (fun t => ocRefFlux α q Λ ζ m ν t - B • (1 : Matrix (Fin 2) (Fin 2) ℝ)) t₀ t₁ ≤
        ENNReal.ofReal (ν + ocHStar α q Λ m ν + B) := by
    unfold matrixSupNorm
    exact iSup₂_le fun t _ => iSup_le fun i => iSup_le fun j =>
      ENNReal.ofReal_le_ofReal (hbound t i j)
  have hreal := ENNReal.toReal_le_of_le_ofReal ((abs_nonneg _).trans (hbound t₀ 0 0)) hle
  rw [div_le_iff₀ hBpos]
  calc (matrixSupNorm (fun t => ocRefFlux α q Λ ζ m ν t - B • (1 : Matrix (Fin 2) (Fin 2) ℝ))
        t₀ t₁).toReal ≤ ν + ocHStar α q Λ m ν + B := hreal
    _ ≤ B + C * B + B := add_le_add (add_le_add hL.ν_le hL.hstar_le) le_rfl
    _ = (2 + C) * B := by ring

end AVRegularity.CycleComparison.Reconstruction
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Lift
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The data of one cell time of the tail of a charted lift**. For the explicit tail presentation
`(0, tailFluxCoefficient)` of the lift of a pulse (`setting_tail_presentation`), a physical field
`u` read in a chart `χ`, and a cleanup chain of the divided tail at one cell time, the data of the
differentiated tail residual estimate (`TailDiff.TailTime`) hold on the singleton time set, given a
bound `S` of the mixed slow/fast cell jets of the tail flux coefficients at that time
(`setting_tailTime`). The pointwise-in-time residual estimates of `TailDiff` then apply to the
sampled cleanup flux and remainder of the chain. -/

/-- The mixed cell jets of the zero field vanish. -/
theorem mixedCellJet_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (I : Set ℝ)
    (i : ℕ) {b : ℕ} (δ : DerivativeWord2 b) :
    MixedTail.mixedCellJet I i δ (fun (_ : ℝ) (_ _ : Vec 2) => (0 : E)) = 0 := by
  have hz : ∀ X z : Vec 2, iteratedFDeriv ℝ i (fun X' : Vec 2 => orderedDerivative δ
      (fun (_ : Vec 2) => (0 : E)) z) X = 0 := by
    intro X z
    have he : (fun X' : Vec 2 => orderedDerivative δ (fun (_ : Vec 2) => (0 : E)) z) =
        fun _ => 0 := funext fun _ => orderedDerivative_zero_fun δ z
    rw [he]
    exact congrFun (iteratedFDeriv_fun_zero (𝕜 := ℝ) (E := Vec 2)) X
  have h0 : eLpNorm (fun _ : Vec 2 => (0 : ContinuousMultilinearMap ℝ (fun _ : Fin i => Vec 2) E))
      2 (volume.restrict unitCube) = 0 := by
    have h := eLpNorm_le_of_ae_bound (p := 2) (μ := volume.restrict unitCube)
      (f := fun _ : Vec 2 => (0 : ContinuousMultilinearMap ℝ (fun _ : Fin i => Vec 2) E))
      (C := 0) aestronglyMeasurable_const (Filter.Eventually.of_forall fun _ => by simp)
    refine le_antisymm (h.trans ?_) bot_le
    simp
  unfold MixedTail.mixedCellJet
  simp only [hz, h0, ENNReal.iSup_eq_zero, implies_true]

/-- The mixed Schur jets of the zero coefficient array vanish. -/
theorem schurMixedJet_zero {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {κ : Type*} [Fintype κ]
    (π : ι → ℝ) (I : Set ℝ) (i : ℕ) {b : ℕ} (δ : DerivativeWord2 b) :
    MixedTail.schurMixedJet π I i δ
      (fun (_ : κ) (_ : ℝ) (_ _ : Vec 2) (v u : ι) => (0 : h u →L[ℝ] h v)) = 0 := by
  unfold MixedTail.schurMixedJet schurSums
  simp only [mixedCellJet_zero, Finset.sum_const_zero, mul_zero]
  rw [ENNReal.iSup_eq_zero.2 fun _ => rfl, max_self]

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
/-- **The data of one cell time of the tail of a charted lift.** -/
theorem setting_tailTime (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (Acl r m : ℕ) (hAcl : 1 ≤ Acl) (hX : Acl + 2 + r ≤ K + D + 2)
    (hZ : r + 1 ≤ max (k + 1) (L + 2)) (hord : Acl + 2 + r + (2 * N + D) ≤ m + 1)
    (hh : ℕ) (hhh : hh ≤ H) (S : ℝ) (u : ℝ → Vec 2 → ∀ i, h i)
    (χ : ℝ → Vec 2 → Vec 2) {t : ℝ} (ht : (ℓ ^ 2)⁻¹ * t ∈ Set.Icc a b)
    (hu : ContDiff ℝ ((m + 1 : ℕ) : ℕ∞) (fun y => u t (χ t y)))
    (hjet : ∀ n ∈ Finset.Icc (N + 1) (2 * N + D), ∀ bb, bb ≤ r → ∀ δ : DerivativeWord2 bb,
      ∀ i, i ≤ Acl + 2 + r → ∀ m',
        MixedTail.schurMixedJet π {(ℓ ^ 2)⁻¹ * t} i δ (fun q : DerivativeWord2 m' × Fin 2 =>
          tailFluxCoefficient par Q Cc N hh n q.2 m' q.1) ≤ ENNReal.ofReal S)
    (W : ℕ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hW : IsCleanupChain (Acl + 2 + r) (r + 1) Acl
      (tailScalarField (fun _ => 0) N D εc
        (fun s X => u (ℓ ^ 2 * s) (χ (ℓ ^ 2 * s) (ρ • X))) ((ℓ ^ 2)⁻¹ * t))
      (tailFluxField (fun n => tailFluxCoefficient par Q Cc N hh n) N D εc
        (fun s X => u (ℓ ^ 2 * s) (χ (ℓ ^ 2 * s) (ρ • X))) ((ℓ ^ 2)⁻¹ * t)) W) :
    TailDiff.TailTime π {(ℓ ^ 2)⁻¹ * t} N D Acl r m (fun _ => 0)
      (fun n => tailFluxCoefficient par Q Cc N hh n) εc (fun s y => u s (χ s y)) ℓ ρ t
      ((ℓ ^ 2)⁻¹ * t) S W := by
  have hℓ : 0 < ℓ := by rw [P.ℓ_eq]; exact div_pos P.e_pos (Real.sqrt_pos.2 P.ν_pos)
  have hc : ℓ ^ 2 ≠ 0 := by positivity
  have hεc : 0 ≤ εc := by
    rw [P.εc_eq, P.dstar_eq]
    exact div_nonneg (mul_nonneg hℓ.le (Real.sqrt_nonneg _)) P.ρ_pos.le
  have hgeo := fun (n : ℕ) (hn : n ∈ Finset.Icc (N + 1) (2 * N + D)) (dir : Fin 2) (m' : ℕ)
      (α : DerivativeWord2 m') (v u' : ι) =>
    setting_tailFluxCoefficient_geometry P sX sZ hsX hsZ Cc hseq hh hhh n
      (by have := (Finset.mem_Icc.1 hn).1; omega) (Finset.mem_Icc.1 hn).2 m' α u' v _ ht dir
  exact {
    mass_pos := P.mass_pos
    ε_nonneg := hεc
    ε_le := P.εc_le
    ρ_pos := P.ρ_pos
    τ_mem := rfl
    τ_eq := by field_simp
    hA := hAcl
    box := fun n hn => ⟨fun _ _ _ _ => isBoxSmooth_zero _ _,
      fun dir m' α v u' => (hgeo n hn dir m' α v u').1.mono hX hZ⟩
    per := fun n hn dir m' α v u' X => (hgeo n hn dir m' α v u').2 X
    zero := fun n _ => ⟨fun _ _ _ _ _ _ => rfl, fun dir α t' X z v u' =>
      tailFluxCoefficient_outside par dir Q Cc N hh n 0 α t' X z v u' (Or.inl rfl)⟩
    jet := fun n hn bb hb δ i hi m' => ⟨by
        have h0 := schurMixedJet_zero (h := h) (κ := DerivativeWord2 m') π
          {(ℓ ^ 2)⁻¹ * t} i δ
        exact h0.le.trans bot_le, hjet n hn bb hb δ i hi m'⟩
    order := hord
    smooth := hu
    chain := hW }

end AVRegularity.CycleComparison.Reconstruction
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity.ChartTransport
open AVRegularity.CycleComparison.Lift
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The data of one cell time of the lifted coarse flux of a charted pulse**. For a physical
flux `F`, the lift of a pulse acts on the chart-frame field of `div F`; with the inverse-Piola
pull-back `F' = (Dχ)⁻¹ F∘χ` this is `ρ⁻¹` times the coarse field of `F'`
(`coarseField_invPiola`). Hence `ρ` times the cleanup chains of the positive degrees of the lift
of `div F` are cleanup chains of the straight lifted coarse flux of `F'`, and the data of the
differentiated coarse-flux estimate (`CoarseFluxDiff.DiffTime`) hold at one cell time
(`setting_liftDiffTime`). The flux densities of `F'` and `F` are comparable at one time
(`fluxDensity_invPiola_le`). -/

section
section Field

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- The lift action of a multiple of a field. -/
theorem liftApply_smul_field (n : ℕ) (c : LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i) (ρ t : ℝ)
    (ha : ContDiff ℝ (n : ℕ∞) (a t)) (X z : Vec 2) :
    liftApply n c (fun s X' => ρ • a s X') t X z = ρ • liftApply n c a t X z := by
  funext v
  simp only [liftApply, Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun α _ =>
    Finset.sum_congr rfl fun u _ => ?_
  have hm' : m ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
  rw [CoarseFluxDiff.orderedDerivative_const_smul α ρ (ha.of_le (by exact_mod_cast hm'))]
  show (c m α t X z v u) ((ρ • orderedDerivative α (a t) X) u) = _
  rw [Pi.smul_apply, map_smul]

/-- The inverse-Piola pull-back of a `C^M` flux by a `C^{M+1}` chart with unit Jacobian
determinant is `C^M`, componentwise. -/
theorem contDiff_invPiola {χ : Vec 2 → Vec 2} {M : ℕ} (hχ : ContDiff ℝ ((M + 1 : ℕ) : ℕ∞) χ)
    (hd : ∀ y, (jacMatrix χ y).det = 1) {G : Vec 2 → Fin 2 → ∀ i, h i}
    (hG : ∀ l, ContDiff ℝ (M : ℕ∞) (fun x => G x l)) (k : Fin 2) :
    ContDiff ℝ (M : ℕ∞) (fun y => invPiola χ G y k) := by
  choose c a b hc hcab using fun l => inv_entry k l
  have hu : (fun y => invPiola χ G y k) =
      fun z => ∑ l : Fin 2, (c l * jacMatrix χ z (a l) (b l)) • (fun x => G x l) (χ z) := by
    funext z
    simp only [invPiola]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hcab l _ (hd z)]
  rw [hu]
  exact contDiff_piola_comb hχ hG c a b

end Field

section Density

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]

/-- **The flux density of the inverse-Piola pull-back at one time.** -/
theorem fluxDensity_invPiola_le {χ ψ : ℝ → Vec 2 → Vec 2} {t : ℝ} (hC : IsChart (χ t) (ψ t))
    {M Nχ : ℕ} (hMN : M + 1 ≤ Nχ) (hχ : ContDiff ℝ ((M + 1 : ℕ) : ℕ∞) (χ t)) {D Rχ ρ : ℝ}
    (hD : 1 ≤ D) (hρ : 0 < ρ) (hρR : ρ ≤ Rχ) (hJ : JetBound (χ t) Nχ D Rχ) (π : ι → ℝ)
    (F : ℝ → Vec 2 → Fin 2 → ∀ i, h i) (hF : ∀ k, ContDiff ℝ (M : ℕ∞) (fun x => F t x k))
    (hFp : ∀ k, IsZ2Periodic (fun x => F t x k)) :
    CoarseFluxDiff.fluxDensity ρ M π (fun s y k => invPiola (χ s) (F s) y k) t ≤
      ENNReal.ofReal (2 * ChartTransport.densConst M 0 2 (2 ^ Nχ * D * compConst D Nχ)) *
        CoarseFluxDiff.fluxDensity ρ M π F t := by
  unfold CoarseFluxDiff.fluxDensity
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun v _ => ?_
  have hG : ∀ l : Fin 2, ContDiff ℝ (M : ℕ∞) (fun x => F t x l v) := fun l =>
    (contDiff_pi.1 (hF l)) v
  have hGp : ∀ l : Fin 2, IsZ2Periodic (fun x => F t x l v) := fun l n x => by
    simpa using congrFun (hFp l n x) v
  have hk : ∀ k : Fin 2, classicalFactorialSq ρ M
        (fun x => invPiola (χ t) (F t) x k v) ≤
      ENNReal.ofReal (ChartTransport.densConst M 0 2 (2 ^ Nχ * D * compConst D Nχ)) *
        ∑ l : Fin 2, classicalFactorialSq ρ M (fun x => F t x l v) := by
    intro k
    choose c a b hc hcab using fun l => inv_entry k l
    have hu : (fun x => invPiola (χ t) (F t) x k v) =
        fun z => ∑ l : Fin 2, (c l * jacMatrix (χ t) z (a l) (b l)) • (fun x => F t x l v)
          (χ t z) := by
      funext z
      simp only [invPiola, Finset.sum_apply, Pi.smul_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hcab l _ (hC.det z)]
    have hcont : ContDiff ℝ (M : ℕ∞) (fun z => ∑ l : Fin 2,
        (c l * jacMatrix (χ t) z (a l) (b l)) • (fun x => F t x l v) (χ t z)) :=
      contDiff_piola_comb hχ hG c a b
    rw [hu, classicalFactorialSq_eq_fsum ρ M (by simpa using hcont)]
    simp only [fun l => classicalFactorialSq_eq_fsum ρ M (hG l)]
    exact fsum_piola_le (N := Nχ) hC hMN hG hGp hχ hc a b hD hρ hρR hJ _ rfl
  have hsum : ∑ k : Fin 2, classicalFactorialSq ρ M (fun x => invPiola (χ t) (F t) x k v) ≤
      ENNReal.ofReal (2 * ChartTransport.densConst M 0 2 (2 ^ Nχ * D * compConst D Nχ)) *
        ∑ k : Fin 2, classicalFactorialSq ρ M (fun x => F t x k v) := by
    calc ∑ k : Fin 2, classicalFactorialSq ρ M (fun x => invPiola (χ t) (F t) x k v)
        ≤ ∑ _k : Fin 2, ENNReal.ofReal (ChartTransport.densConst M 0 2
            (2 ^ Nχ * D * compConst D Nχ)) *
            ∑ l : Fin 2, classicalFactorialSq ρ M (fun x => F t x l v) :=
          Finset.sum_le_sum fun k _ => hk k
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            ENNReal.ofReal_mul (by norm_num), nsmul_eq_mul]
          norm_num
          ring
  calc ENNReal.ofReal (π v)⁻¹ *
        ∑ k : Fin 2, classicalFactorialSq ρ M (fun x => invPiola (χ t) (F t) x k v)
      ≤ ENNReal.ofReal (π v)⁻¹ * (ENNReal.ofReal (2 * ChartTransport.densConst M 0 2
          (2 ^ Nχ * D * compConst D Nχ)) *
          ∑ k : Fin 2, classicalFactorialSq ρ M (fun x => F t x k v)) := by gcongr
    _ = _ := by ring

end Density
end

/-! **The tail residual of one charted pulse at one time** (exact Piola transports flux by
`(DΦR)∘Φ⁻¹`, and chart jets pay the chain rule).

At one physical time `t`, for one pulse with lift data in a lift setting, chart `χ_t` with inverse
`ψ_t`, physical field `u`, and cleanup chains of the divided tails of the chart-frame field:

* `setting_tailLabel_word_slice`: every weighted word derivative `rs^i ∂^w` of the label tail
  flux (`tailFluxLabel`, the sum over the grades) has mass-weighted cell norm at most
  `(H+1)² C_i (ℓ⁻² ε_c^{N+1} e ρ S)²` times the gradient energy density of the pull-back
  `u ∘ χ` (`TailDiff.TailTime.flux_pointwise` for every grade, `fluxInt_sum_le`);
* `setting_tailPhys_word_slice`: the same for the physical tail flux (`tailFluxPhys`, the Piola
  transport) with the gradient energy density of `u` itself (`ChartTransport.flux_slice`,
  `gradDensity_comp_le`).

These are the time slices of the residual bound: they hold at every time, and the time integral
is taken once over the whole window. -/

section
/-- The sampled cleanup flux of chains box smooth of orders `≥ (r, r)` is `C^r`. -/
theorem contDiff_cleanupFlux_sample_of_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {sX sZ A r : ℕ} (hX : r ≤ sX) (hZ : r ≤ sZ) (c ρ e : ℝ)
    {W : ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E} (t : ℝ)
    (hW : ∀ j, j < A → IsBoxSmooth sX sZ (W j (c * t))) (k : Fin 2) :
    ContDiff ℝ (r : ℕ∞) (fun y => cleanupFlux c ρ e A W t y k) := by
  show ContDiff ℝ (r : ℕ∞) (fun y => e • ∑ j ∈ Finset.range A,
    (e / ρ) ^ j • W j (c * t) (ρ⁻¹ • y) (e⁻¹ • y) k)
  refine ContDiff.const_smul e (ContDiff.sum fun j hj => ContDiff.const_smul _ ?_)
  exact CoarseFluxDiff.contDiff_sample ((hW j (Finset.mem_range.1 hj)).clm_comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => E) k)) hX hZ ρ e

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
/-- **The weighted word derivatives of the label tail flux of one pulse at one time.** -/
theorem setting_tailLabel_word_slice (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (Acl r m : ℕ) (hAcl : 1 ≤ Acl) (hX : Acl + 2 + r ≤ K + D + 2)
    (hZ : r + 1 ≤ max (k + 1) (L + 2)) (hord : Acl + 2 + r + (2 * N + D) ≤ m + 1)
    (S : ℝ) (hS : 0 ≤ S) (u : ℝ → Vec 2 → ∀ i, h i) (χ : ℝ → Vec 2 → Vec 2) {t : ℝ}
    (ht : (ℓ ^ 2)⁻¹ * t ∈ Set.Icc a b)
    (hu : ContDiff ℝ ((m + 1 : ℕ) : ℕ∞) (fun y => u t (χ t y)))
    (hjet : ∀ hh, hh ≤ H → ∀ n ∈ Finset.Icc (N + 1) (2 * N + D), ∀ bb, bb ≤ r →
      ∀ δ : DerivativeWord2 bb, ∀ i, i ≤ Acl + 2 + r → ∀ m',
        MixedTail.schurMixedJet π {(ℓ ^ 2)⁻¹ * t} i δ (fun q : DerivativeWord2 m' × Fin 2 =>
          tailFluxCoefficient par Q Cc N hh n q.2 m' q.1) ≤ ENNReal.ofReal S)
    (Vc : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hV : ∀ hh, hh ≤ H → IsCleanupChain (Acl + 2 + r) (r + 1) Acl
      (tailScalarField (fun _ => 0) N D εc
        (fun s X => u (ℓ ^ 2 * s) (χ (ℓ ^ 2 * s) (ρ • X))) ((ℓ ^ 2)⁻¹ * t))
      (tailFluxField (fun n => tailFluxCoefficient par Q Cc N hh n) N D εc
        (fun s X => u (ℓ ^ 2 * s) (χ (ℓ ^ 2 * s) (ρ • X))) ((ℓ ^ 2)⁻¹ * t))
      (fun j => Vc hh j ((ℓ ^ 2)⁻¹ * t)))
    {rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ ρ) {M : ℕ} (hM : e⁻¹ = (M : ℝ))
    {i : ℕ} (hi : i ≤ r) (w : DerivativeWord2 i) :
    fluxInt π (fun x l => rs ^ i • orderedDerivative w
        (fun x' => tailFluxLabel H N Acl εc (ℓ ^ 2) ρ e Vc t x' l) x) ≤
      ENNReal.ofReal (((H + 1 : ℕ) : ℝ) ^ 2 * TailDiff.fluxConst N D Acl r i) *
        (ENNReal.ofReal (((ℓ ^ 2)⁻¹ * εc ^ (N + 1) * e * ρ * S) ^ 2) *
          ResidualTimeData.gradDensity π ρ m (fun s y => u s (χ s y)) t) := by
  have hℓ : 0 < ℓ := by rw [P.ℓ_eq]; exact div_pos P.e_pos (Real.sqrt_pos.2 P.ν_pos)
  have hεc : 0 ≤ εc := by
    rw [P.εc_eq, P.dstar_eq]
    exact div_nonneg (mul_nonneg hℓ.le (Real.sqrt_nonneg _)) P.ρ_pos.le
  have hpR0 : 0 ≤ (ℓ ^ 2)⁻¹ * εc ^ (N + 1) * e := by
    have := P.e_pos
    positivity
  have hTT := fun (hh : ℕ) (hhh : hh ≤ H) => setting_tailTime P sX sZ hsX hsZ Cc hseq Acl r m
    hAcl hX hZ hord hh hhh S u χ ht hu (hjet hh hhh) (fun j => Vc hh j ((ℓ ^ 2)⁻¹ * t))
    (hV hh hhh)
  -- the grade terms are smooth
  have hg : ∀ hh ∈ Finset.range (H + 1), ∀ l : Fin 2, ContDiff ℝ (i : ℕ∞)
      (fun x' => (ℓ ^ 2)⁻¹ • εc ^ (N + 1) • cleanupFlux (ℓ ^ 2)⁻¹ ρ e Acl (Vc hh) t x' l) := by
    intro hh hhm l
    have hhh : hh ≤ H := Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)
    have hd := hTT hh hhh
    refine ((contDiff_cleanupFlux_sample_of_le (sX := Acl + 2 + r) (sZ := r + 1)
      (by omega) (by omega) (ℓ ^ 2)⁻¹ ρ e t (fun j hj => ?_) l).const_smul _).const_smul _
    exact IsCleanupChain.isBoxSmooth hd.flux_box hd.chain j hj
  have e1 : (fun x l => rs ^ i • orderedDerivative w
      (fun x' => tailFluxLabel H N Acl εc (ℓ ^ 2) ρ e Vc t x' l) x) =
      fun x l => ∑ hh ∈ Finset.range (H + 1), rs ^ i • orderedDerivative w
        (fun x' => (ℓ ^ 2)⁻¹ • εc ^ (N + 1) • cleanupFlux (ℓ ^ 2)⁻¹ ρ e Acl (Vc hh) t x' l) x := by
    funext x l
    show rs ^ i • orderedDerivative w (fun x' => ∑ hh ∈ Finset.range (H + 1),
      (ℓ ^ 2)⁻¹ • εc ^ (N + 1) • cleanupFlux (ℓ ^ 2)⁻¹ ρ e Acl (Vc hh) t x' l) x = _
    rw [MixedTail.orderedDerivative_sum _ w fun hh hhm => hg hh hhm l, Finset.smul_sum]
  have hsum := fluxInt_sum_le (Finset.range (H + 1)) (fun hh x l => rs ^ i • orderedDerivative w
      (fun x' => (ℓ ^ 2)⁻¹ • εc ^ (N + 1) • cleanupFlux (ℓ ^ 2)⁻¹ ρ e Acl (Vc hh) t x' l) x)
    (fun hh hhm l => (continuous_orderedDerivative w (hg hh hhm l)).fun_const_smul (rs ^ i)) π
  refine (le_of_eq (congrArg (fluxInt π) e1)).trans (hsum.trans ?_)
  -- every grade
  have hgr : ∀ hh ∈ Finset.range (H + 1), fluxInt π (fun x l => rs ^ i • orderedDerivative w
      (fun x' => (ℓ ^ 2)⁻¹ • εc ^ (N + 1) • cleanupFlux (ℓ ^ 2)⁻¹ ρ e Acl (Vc hh) t x' l) x) ≤
      ENNReal.ofReal (TailDiff.fluxConst N D Acl r i) *
        (ENNReal.ofReal (((ℓ ^ 2)⁻¹ * εc ^ (N + 1) * e * ρ * S) ^ 2) *
          ResidualTimeData.gradDensity π ρ m (fun s y => u s (χ s y)) t) := by
    intro hh hhm
    have hhh : hh ≤ H := Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)
    have hb := (hTT hh hhh).flux_pointwise (Vc := Vc hh) hS hrs hrse heρ hM hi w hpR0
    refine hb.trans (le_of_eq ?_)
    have hfc := TailDiff.fluxConst_nonneg N D Acl r i
    rw [show ((ℓ ^ 2)⁻¹ * εc ^ (N + 1) * e * ρ * Real.sqrt (TailDiff.fluxConst N D Acl r i) * S)
        ^ 2 = TailDiff.fluxConst N D Acl r i * ((ℓ ^ 2)⁻¹ * εc ^ (N + 1) * e * ρ * S) ^ 2 by
      rw [mul_pow, mul_pow, Real.sq_sqrt hfc]; ring,
      ENNReal.ofReal_mul hfc, mul_assoc]
  calc ((Finset.range (H + 1)).card : ℝ≥0∞) * ∑ hh ∈ Finset.range (H + 1),
        fluxInt π (fun x l => rs ^ i • orderedDerivative w
          (fun x' => (ℓ ^ 2)⁻¹ • εc ^ (N + 1) • cleanupFlux (ℓ ^ 2)⁻¹ ρ e Acl (Vc hh) t x' l) x)
      ≤ ((Finset.range (H + 1)).card : ℝ≥0∞) * ∑ _hh ∈ Finset.range (H + 1),
          ENNReal.ofReal (TailDiff.fluxConst N D Acl r i) *
            (ENNReal.ofReal (((ℓ ^ 2)⁻¹ * εc ^ (N + 1) * e * ρ * S) ^ 2) *
              ResidualTimeData.gradDensity π ρ m (fun s y => u s (χ s y)) t) := by
        gcongr with hh hhm
        exact hgr hh hhm
    _ = _ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc, ← mul_assoc]
        congr 1
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
        ring

/-- The constant of the physical tail slice bound. -/
def tailPhysConst (H N D Acl r m : ℕ) (Dχ : ℝ) : ℝ :=
  2 * ChartTransport.fluxConst Dχ r *
    (∑ i ∈ Finset.range (r + 1), (2 : ℝ) ^ i *
      (((H + 1 : ℕ) : ℝ) ^ 2 * TailDiff.fluxConst N D Acl r i)) *
    ChartTransport.densConst m 1 1 ((m + 1).factorial * Dχ ^ (m + 1))

omit [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] in
theorem tailPhysConst_nonneg (H N D Acl r m : ℕ) (Dχ : ℝ) :
    0 ≤ tailPhysConst H N D Acl r m Dχ := by
  unfold tailPhysConst
  refine mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (fluxConst_nonneg r))
    (Finset.sum_nonneg fun i _ => mul_nonneg (by positivity)
      (mul_nonneg (by positivity) (TailDiff.fluxConst_nonneg N D Acl r i)))) ?_
  exact ChartTransport.densConst_nonneg m 1 1 _

include P in
/-- **The weighted word derivatives of the physical tail flux of one pulse at one time.** -/
theorem setting_tailPhys_word_slice (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (Acl r m : ℕ) (hAcl : 1 ≤ Acl) (hX : Acl + 2 + r ≤ K + D + 2)
    (hZ : r + 1 ≤ max (k + 1) (L + 2)) (hord : Acl + 2 + r + (2 * N + D) ≤ m + 1)
    (S : ℝ) (hS : 0 ≤ S) (u : ℝ → Vec 2 → ∀ i, h i) (χ ψ : ℝ → Vec 2 → Vec 2) {t : ℝ}
    (ht : (ℓ ^ 2)⁻¹ * t ∈ Set.Icc a b) (hu : ContDiff ℝ ((m + 1 : ℕ) : ℕ∞) (u t))
    (hup : IsZ2Periodic (u t)) (hC : IsChart (χ t) (ψ t))
    (hχr : ContDiff ℝ ((r + 1 : ℕ) : ℕ∞) (χ t)) (hχm : ContDiff ℝ ((m + 1 : ℕ) : ℕ∞) (χ t))
    (hψr : ContDiff ℝ (r : ℕ∞) (ψ t)) {Dχ Rχ : ℝ} (hDχ : 1 ≤ Dχ)
    (hJχr : JetBound (χ t) (r + 1) Dχ Rχ) (hJχm : JetBound (χ t) (m + 1) Dχ Rχ)
    (hJψ : JetBound (ψ t) r Dχ Rχ) (hρR : ρ ≤ Rχ)
    (hjet : ∀ hh, hh ≤ H → ∀ n ∈ Finset.Icc (N + 1) (2 * N + D), ∀ bb, bb ≤ r →
      ∀ δ : DerivativeWord2 bb, ∀ i, i ≤ Acl + 2 + r → ∀ m',
        MixedTail.schurMixedJet π {(ℓ ^ 2)⁻¹ * t} i δ (fun q : DerivativeWord2 m' × Fin 2 =>
          tailFluxCoefficient par Q Cc N hh n q.2 m' q.1) ≤ ENNReal.ofReal S)
    (Vc : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hV : ∀ hh, hh ≤ H → IsCleanupChain (Acl + 2 + r) (r + 1) Acl
      (tailScalarField (fun _ => 0) N D εc
        (fun s X => u (ℓ ^ 2 * s) (χ (ℓ ^ 2 * s) (ρ • X))) ((ℓ ^ 2)⁻¹ * t))
      (tailFluxField (fun n => tailFluxCoefficient par Q Cc N hh n) N D εc
        (fun s X => u (ℓ ^ 2 * s) (χ (ℓ ^ 2 * s) (ρ • X))) ((ℓ ^ 2)⁻¹ * t))
      (fun j => Vc hh j ((ℓ ^ 2)⁻¹ * t)))
    (hslow : ∀ hh, hh ≤ H → ∀ j, j < Acl → ∀ (n : Fin 2 → ℤ) (X : Vec 2),
      Vc hh j ((ℓ ^ 2)⁻¹ * t) (X + ρ⁻¹ • latticeShift n) = Vc hh j ((ℓ ^ 2)⁻¹ * t) X)
    {rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e) (hsR : rs ≤ Rχ) (heρ : e ≤ ρ) {M : ℕ}
    (hM : e⁻¹ = (M : ℝ)) {j : ℕ} (hj : j ≤ r) (β : DerivativeWord2 j) :
    fluxInt π (fun x a₀ => rs ^ j • orderedDerivative β
        (fun x' => tailFluxPhys (ψ t) H N Acl εc (ℓ ^ 2) ρ e Vc t x' a₀) x) ≤
      ENNReal.ofReal (tailPhysConst H N D Acl r m Dχ) *
        ENNReal.ofReal (((ℓ ^ 2)⁻¹ * εc ^ (N + 1) * e * ρ * S) ^ 2) *
          ResidualTimeData.gradDensity π ρ m u t := by
  have hu' : ContDiff ℝ ((m + 1 : ℕ) : ℕ∞) (fun y => u t (χ t y)) := hu.comp hχm
  have hpres := fun (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn1 : N + 1 ≤ n) (hn2 : n ≤ 2 * N + D) =>
    setting_tail_presentation P sX sZ hsX hsZ Cc hseq hh hhh n (by omega) hn2
  -- the label flux
  set G : Vec 2 → Fin 2 → ∀ i, h i := fun y l => tailFluxLabel H N Acl εc (ℓ ^ 2) ρ e Vc t y l
    with hGdef
  have hTT := fun (hh : ℕ) (hhh : hh ≤ H) => setting_tailTime P sX sZ hsX hsZ Cc hseq Acl r m
    hAcl hX hZ hord hh hhh S u χ ht hu' (hjet hh hhh) (fun j => Vc hh j ((ℓ ^ 2)⁻¹ * t))
    (hV hh hhh)
  have hbox : ∀ hh, hh ≤ H → ∀ j', j' < Acl → IsBoxSmooth (Acl + 2 + r) (r + 1)
      (Vc hh j' ((ℓ ^ 2)⁻¹ * t)) := fun hh hhh j' hj' =>
    IsCleanupChain.isBoxSmooth (hTT hh hhh).flux_box (hTT hh hhh).chain j' hj'
  have hfast : ∀ hh, hh ≤ H → ∀ j', j' < Acl → ∀ X,
      IsZ2Periodic (Vc hh j' ((ℓ ^ 2)⁻¹ * t) X) := fun hh hhh =>
    (hV hh hhh).periodic (tailFluxField_isZ2Periodic_of_presentation (f := fun _ => 0)
      (F := fun n => tailFluxCoefficient par Q Cc N hh n) (hpres hh hhh) εc
      (fun s X => u (ℓ ^ 2 * s) (χ (ℓ ^ 2 * s) (ρ • X))) ht)
  have hGc : ∀ l, ContDiff ℝ (r : ℕ∞) (fun y => G y l) := fun l =>
    ContDiff.sum fun hh hhm => ((contDiff_cleanupFlux_sample_of_le (sX := Acl + 2 + r)
      (sZ := r + 1) (by omega) (by omega) (ℓ ^ 2)⁻¹ ρ e t
      (hbox hh (Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm))) l).const_smul _).const_smul _
  have hGp : ∀ l, IsZ2Periodic (fun y => G y l) :=
    tailFluxLabel_isZ2Periodic H N Acl εc (ℓ ^ 2) ρ e Vc t M hM hslow hfast
  -- the physical flux is the Piola transport of the label flux
  have hχd : Differentiable ℝ (χ t) := hC.contΦ.differentiable one_ne_zero
  have hψd : Differentiable ℝ (ψ t) := hC.contΨ.differentiable one_ne_zero
  have hphys : (fun x a₀ => rs ^ j • orderedDerivative β
      (fun x' => tailFluxPhys (ψ t) H N Acl εc (ℓ ^ 2) ρ e Vc t x' a₀) x) =
      fun x a₀ => rs ^ j • orderedDerivative β
        (fun x' => ∑ l : Fin 2, jacMatrix (χ t) (ψ t x') a₀ l • G (ψ t x') l) x := by
    have he : ∀ a₀, (fun x' => tailFluxPhys (ψ t) H N Acl εc (ℓ ^ 2) ρ e Vc t x' a₀) =
        fun x' => ∑ l : Fin 2, jacMatrix (χ t) (ψ t x') a₀ l • G (ψ t x') l := fun a₀ => by
      funext x'
      show ∑ i₀ : Fin 2, chartInvJacobian (ψ t) x' a₀ i₀ • G (ψ t x') i₀ = _
      rw [chartInvJacobian_eq_of_inverse hχd hψd hC.left hC.right x',
        chartJacobian_eq_jacMatrix]
    funext x a₀
    rw [he a₀]
  rw [hphys]
  refine (flux_slice hC hj hχr hψr hGc hGp hDχ hrs hsR hJχr hJψ π β).trans ?_
  -- the label words
  set X0 : ℝ≥0∞ := ENNReal.ofReal (((ℓ ^ 2)⁻¹ * εc ^ (N + 1) * e * ρ * S) ^ 2) *
    ResidualTimeData.gradDensity π ρ m (fun s y => u s (χ s y)) t with hX0
  have hw : ∀ i ∈ Finset.range (j + 1), ∀ w : DerivativeWord2 i,
      fluxInt π (fun x l => rs ^ i • orderedDerivative w (fun x' => G x' l) x) ≤
        ENNReal.ofReal (((H + 1 : ℕ) : ℝ) ^ 2 * TailDiff.fluxConst N D Acl r i) * X0 :=
    fun i hi w => setting_tailLabel_word_slice P sX sZ hsX hsZ Cc hseq Acl r m hAcl hX hZ hord
      S hS u χ ht hu' hjet Vc hV hrs hrse heρ hM
      ((Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)).trans hj) w
  have hfcn : ∀ i, 0 ≤ ((H + 1 : ℕ) : ℝ) ^ 2 * TailDiff.fluxConst N D Acl r i := fun i =>
    mul_nonneg (by positivity) (TailDiff.fluxConst_nonneg N D Acl r i)
  have hsum : ∑ i ∈ Finset.range (j + 1), ∑ w : DerivativeWord2 i,
      fluxInt π (fun x l => rs ^ i • orderedDerivative w (fun x' => G x' l) x) ≤
      ENNReal.ofReal (∑ i ∈ Finset.range (r + 1), (2 : ℝ) ^ i *
        (((H + 1 : ℕ) : ℝ) ^ 2 * TailDiff.fluxConst N D Acl r i)) * X0 := by
    calc ∑ i ∈ Finset.range (j + 1), ∑ w : DerivativeWord2 i,
          fluxInt π (fun x l => rs ^ i • orderedDerivative w (fun x' => G x' l) x)
        ≤ ∑ i ∈ Finset.range (j + 1), ∑ _w : DerivativeWord2 i,
            ENNReal.ofReal (((H + 1 : ℕ) : ℝ) ^ 2 * TailDiff.fluxConst N D Acl r i) * X0 :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun w _ => hw i hi w
      _ = ENNReal.ofReal (∑ i ∈ Finset.range (j + 1), (2 : ℝ) ^ i *
            (((H + 1 : ℕ) : ℝ) ^ 2 * TailDiff.fluxConst N D Acl r i)) * X0 := by
          rw [ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg (by positivity) (hfcn i),
            Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          have h2 : ((2 ^ i : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) ^ i) := by
            rw [ENNReal.ofReal_pow (by norm_num)]
            simp
          rw [Finset.sum_const, card_derivativeWord2, nsmul_eq_mul, h2]
          conv_rhs => rw [ENNReal.ofReal_mul (by positivity)]
          rw [mul_assoc]
      _ ≤ _ := by
          gcongr ?_ * X0
          exact ENNReal.ofReal_le_ofReal
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ hj))
              fun i _ _ => mul_nonneg (by positivity) (hfcn i))
  have hgd := gradDensity_comp_le (Φ := χ) hC u hu hup hχm hDχ P.ρ_pos hρR hJχm π
  calc ENNReal.ofReal (2 * ChartTransport.fluxConst Dχ r) *
        ∑ i ∈ Finset.range (j + 1), ∑ w : DerivativeWord2 i,
          fluxInt π (fun x l => rs ^ i • orderedDerivative w (fun x' => G x' l) x)
      ≤ ENNReal.ofReal (2 * ChartTransport.fluxConst Dχ r) *
          (ENNReal.ofReal (∑ i ∈ Finset.range (r + 1), (2 : ℝ) ^ i *
            (((H + 1 : ℕ) : ℝ) ^ 2 * TailDiff.fluxConst N D Acl r i)) * X0) := by gcongr
    _ ≤ ENNReal.ofReal (2 * ChartTransport.fluxConst Dχ r) *
          (ENNReal.ofReal (∑ i ∈ Finset.range (r + 1), (2 : ℝ) ^ i *
            (((H + 1 : ℕ) : ℝ) ^ 2 * TailDiff.fluxConst N D Acl r i)) *
          (ENNReal.ofReal (((ℓ ^ 2)⁻¹ * εc ^ (N + 1) * e * ρ * S) ^ 2) *
            (ENNReal.ofReal (ChartTransport.densConst m 1 1 ((m + 1).factorial * Dχ ^ (m + 1))) *
              ResidualTimeData.gradDensity π ρ m u t))) := by
        rw [hX0]
        gcongr
    _ = _ := by
        unfold tailPhysConst
        have h1 : 0 ≤ 2 * ChartTransport.fluxConst Dχ r :=
          mul_nonneg (by norm_num) (fluxConst_nonneg r)
        have h2 : 0 ≤ ∑ i ∈ Finset.range (r + 1), (2 : ℝ) ^ i *
            (((H + 1 : ℕ) : ℝ) ^ 2 * TailDiff.fluxConst N D Acl r i) :=
          Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (hfcn i)
        rw [ENNReal.ofReal_mul (mul_nonneg h1 h2), ENNReal.ofReal_mul h1]
        ring
end

/-! **The tail force of one charted pulse at one time**. The scalar companion of
`setting_tailPhys_word_slice`: every weighted word derivative of the physical tail force
(`tailForcePhys`, the sum over the grades of the sampled cleanup remainders read at the label
`ψ x`) has mass-weighted cell norm at most a constant times
`(ℓ⁻² ε_c^{N+1} (e/ρ)^{A} ρ S)²` times the gradient energy density of the physical field
(`setting_tailForce_word_slice`; `TailDiff.TailTime.rem_pointwise` for every grade,
`scalInt_sum_le`, `ChartTransport.scalar_slice`, `gradDensity_comp_le`). -/

section
section Sample

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The sampled cleanup remainder of a chain invariant under the slow translations by `ρ⁻¹ℤ²` and
periodic in the fast variable is `ℤ²`-periodic when `e⁻¹ ∈ ℕ`. -/
theorem cleanupRemainder_isZ2Periodic (c ρ e : ℝ) {A : ℕ} (hA : 1 ≤ A)
    (W : ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E) (t : ℝ) (M : ℕ) (hM : e⁻¹ = M)
    (hslow : ∀ j, j < A → ∀ (n : Fin 2 → ℤ) (X : Vec 2),
      W j (c * t) (X + ρ⁻¹ • latticeShift n) = W j (c * t) X)
    (hfast : ∀ j, j < A → ∀ X, IsZ2Periodic (W j (c * t) X)) :
    IsZ2Periodic (fun y => cleanupRemainder c ρ e A W t y) := by
  intro n y
  have hX : ρ⁻¹ • (y + latticeShift n) = ρ⁻¹ • y + ρ⁻¹ • latticeShift n := smul_add _ _ _
  have hz : e⁻¹ • (y + latticeShift n) = e⁻¹ • y + latticeShift (fun i => (M : ℤ) * n i) := by
    rw [smul_add, hM, natCast_smul_latticeShift]
  show (e / ρ) ^ A • cleanupSource (fun j => W j (c * t)) A (ρ⁻¹ • (y + latticeShift n))
      (e⁻¹ • (y + latticeShift n)) =
    (e / ρ) ^ A • cleanupSource (fun j => W j (c * t)) A (ρ⁻¹ • y) (e⁻¹ • y)
  have hsl : cleanupSource (fun j => W j (c * t)) A (ρ⁻¹ • y + ρ⁻¹ • latticeShift n) =
      cleanupSource (fun j => W j (c * t)) A (ρ⁻¹ • y) := by
    have h1 := congrFun (cleanupSource_translate (fun j => W j (c * t)) A
      (ρ⁻¹ • latticeShift n)) (ρ⁻¹ • y)
    rw [← h1]
    refine congrFun (cleanupSource_congr (j := A) ?_) (ρ⁻¹ • y)
    funext X
    exact hslow (A - 1) (by omega) n X
  have hfa : cleanupSource (fun j => W j (c * t)) A (ρ⁻¹ • y)
      (e⁻¹ • y + latticeShift (fun i => (M : ℤ) * n i)) =
      cleanupSource (fun j => W j (c * t)) A (ρ⁻¹ • y) (e⁻¹ • y) :=
    AVRegularity.cleanupSource_periodic (V := fun j => W j (c * t)) (j := A)
      (hfast (A - 1) (by omega)) (ρ⁻¹ • y) (fun i => (M : ℤ) * n i) (e⁻¹ • y)
  rw [hX, hz, hsl, hfa]

end Sample

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

/-- The constant of the physical tail force slice bound. -/
def tailForceConst (H N D Acl r m : ℕ) (Dχ : ℝ) : ℝ :=
  ChartTransport.scalarConst Dχ r *
    (∑ i ∈ Finset.range (r + 1), (2 : ℝ) ^ i *
      (((H + 1 : ℕ) : ℝ) ^ 2 * TailDiff.remConst N D Acl r i)) *
    ChartTransport.densConst m 1 1 ((m + 1).factorial * Dχ ^ (m + 1))

omit [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] in
theorem tailForceConst_nonneg (H N D Acl r m : ℕ) (Dχ : ℝ) :
    0 ≤ tailForceConst H N D Acl r m Dχ := by
  unfold tailForceConst
  refine mul_nonneg (mul_nonneg (scalarConst_nonneg r)
    (Finset.sum_nonneg fun i _ => mul_nonneg (by positivity)
      (mul_nonneg (by positivity) (TailDiff.remConst_nonneg N D Acl r i)))) ?_
  exact ChartTransport.densConst_nonneg m 1 1 _

include P in
/-- **The weighted word derivatives of the physical tail force of one pulse at one time.** -/
theorem setting_tailForce_word_slice (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (Acl r m : ℕ) (hAcl : 1 ≤ Acl) (hX : Acl + 2 + r ≤ K + D + 2)
    (hZ : r + 1 ≤ max (k + 1) (L + 2)) (hord : Acl + 2 + r + (2 * N + D) ≤ m + 1)
    (S : ℝ) (hS : 0 ≤ S) (u : ℝ → Vec 2 → ∀ i, h i) (χ ψ : ℝ → Vec 2 → Vec 2) {t : ℝ}
    (ht : (ℓ ^ 2)⁻¹ * t ∈ Set.Icc a b) (hu : ContDiff ℝ ((m + 1 : ℕ) : ℕ∞) (u t))
    (hup : IsZ2Periodic (u t)) (hC : IsChart (χ t) (ψ t))
    (hχm : ContDiff ℝ ((m + 1 : ℕ) : ℕ∞) (χ t)) (hψr : ContDiff ℝ (r : ℕ∞) (ψ t))
    {Dχ Rχ : ℝ} (hDχ : 1 ≤ Dχ) (hJχm : JetBound (χ t) (m + 1) Dχ Rχ)
    (hJψ : JetBound (ψ t) r Dχ Rχ) (hρR : ρ ≤ Rχ)
    (hjet : ∀ hh, hh ≤ H → ∀ n ∈ Finset.Icc (N + 1) (2 * N + D), ∀ bb, bb ≤ r →
      ∀ δ : DerivativeWord2 bb, ∀ i, i ≤ Acl + 2 + r → ∀ m',
        MixedTail.schurMixedJet π {(ℓ ^ 2)⁻¹ * t} i δ (fun q : DerivativeWord2 m' × Fin 2 =>
          tailFluxCoefficient par Q Cc N hh n q.2 m' q.1) ≤ ENNReal.ofReal S)
    (Vc : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hV : ∀ hh, hh ≤ H → IsCleanupChain (Acl + 2 + r) (r + 1) Acl
      (tailScalarField (fun _ => 0) N D εc
        (fun s X => u (ℓ ^ 2 * s) (χ (ℓ ^ 2 * s) (ρ • X))) ((ℓ ^ 2)⁻¹ * t))
      (tailFluxField (fun n => tailFluxCoefficient par Q Cc N hh n) N D εc
        (fun s X => u (ℓ ^ 2 * s) (χ (ℓ ^ 2 * s) (ρ • X))) ((ℓ ^ 2)⁻¹ * t))
      (fun j => Vc hh j ((ℓ ^ 2)⁻¹ * t)))
    (hslow : ∀ hh, hh ≤ H → ∀ j, j < Acl → ∀ (n : Fin 2 → ℤ) (X : Vec 2),
      Vc hh j ((ℓ ^ 2)⁻¹ * t) (X + ρ⁻¹ • latticeShift n) = Vc hh j ((ℓ ^ 2)⁻¹ * t) X)
    {rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e) (hsR : rs ≤ Rχ) (heρ : e ≤ ρ) {M : ℕ}
    (hM : e⁻¹ = (M : ℝ)) {j : ℕ} (hj : j ≤ r) (β : DerivativeWord2 j) :
    scalInt π (fun x => rs ^ j • orderedDerivative β
        (fun x' => tailForcePhys (ψ t) H N Acl εc (ℓ ^ 2) ρ e Vc t x') x) ≤
      ENNReal.ofReal (tailForceConst H N D Acl r m Dχ) *
        ENNReal.ofReal (((ℓ ^ 2)⁻¹ * εc ^ (N + 1) * (e / ρ) ^ Acl * ρ * S) ^ 2) *
          ResidualTimeData.gradDensity π ρ m u t := by
  have hℓ : 0 < ℓ := by rw [P.ℓ_eq]; exact div_pos P.e_pos (Real.sqrt_pos.2 P.ν_pos)
  have hεc : 0 ≤ εc := by
    rw [P.εc_eq, P.dstar_eq]
    exact div_nonneg (mul_nonneg hℓ.le (Real.sqrt_nonneg _)) P.ρ_pos.le
  have hpq0 : 0 ≤ (ℓ ^ 2)⁻¹ * εc ^ (N + 1) * (e / ρ) ^ Acl := by
    have := P.e_pos
    have := P.ρ_pos
    positivity
  have hu' : ContDiff ℝ ((m + 1 : ℕ) : ℕ∞) (fun y => u t (χ t y)) := hu.comp hχm
  have hpres := fun (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn1 : N + 1 ≤ n) (hn2 : n ≤ 2 * N + D) =>
    setting_tail_presentation P sX sZ hsX hsZ Cc hseq hh hhh n (by omega) hn2
  have hTT := fun (hh : ℕ) (hhh : hh ≤ H) => setting_tailTime P sX sZ hsX hsZ Cc hseq Acl r m
    hAcl hX hZ hord hh hhh S u χ ht hu' (hjet hh hhh) (fun j => Vc hh j ((ℓ ^ 2)⁻¹ * t))
    (hV hh hhh)
  have hfast : ∀ hh, hh ≤ H → ∀ j', j' < Acl → ∀ X,
      IsZ2Periodic (Vc hh j' ((ℓ ^ 2)⁻¹ * t) X) := fun hh hhh =>
    (hV hh hhh).periodic (tailFluxField_isZ2Periodic_of_presentation (f := fun _ => 0)
      (F := fun n => tailFluxCoefficient par Q Cc N hh n) (hpres hh hhh) εc
      (fun s X => u (ℓ ^ 2 * s) (χ (ℓ ^ 2 * s) (ρ • X))) ht)
  -- the label force and its grade terms
  set q : Vec 2 → ∀ i, h i := fun y => ∑ hh ∈ Finset.range (H + 1),
    (ℓ ^ 2)⁻¹ • εc ^ (N + 1) • cleanupRemainder (ℓ ^ 2)⁻¹ ρ e Acl (Vc hh) t y with hqdef
  have hg : ∀ hh ∈ Finset.range (H + 1), ∀ i, i ≤ r → ContDiff ℝ (i : ℕ∞)
      (fun y => (ℓ ^ 2)⁻¹ • εc ^ (N + 1) • cleanupRemainder (ℓ ^ 2)⁻¹ ρ e Acl (Vc hh) t y) := by
    intro hh hhm i hi
    have hd := hTT (hh) (Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm))
    exact ((((hd.contDiff_source_sample hi e).const_smul ((e / ρ) ^ Acl)).const_smul _).const_smul
      _ : ContDiff ℝ (i : ℕ∞) (fun y => (ℓ ^ 2)⁻¹ • εc ^ (N + 1) • ((e / ρ) ^ Acl •
        cleanupSource (fun j => Vc hh j ((ℓ ^ 2)⁻¹ * t)) Acl (ρ⁻¹ • y) (e⁻¹ • y))))
  have hqc : ContDiff ℝ (r : ℕ∞) q := ContDiff.sum fun hh hhm => hg hh hhm r le_rfl
  have hqp : IsZ2Periodic q := by
    intro n y
    show ∑ hh ∈ Finset.range (H + 1), (ℓ ^ 2)⁻¹ • εc ^ (N + 1) •
        cleanupRemainder (ℓ ^ 2)⁻¹ ρ e Acl (Vc hh) t (y + latticeShift n) = _
    refine Finset.sum_congr rfl fun hh hhm => ?_
    have hhh : hh ≤ H := Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)
    have hp : cleanupRemainder (ℓ ^ 2)⁻¹ ρ e Acl (Vc hh) t (y + latticeShift n) =
        cleanupRemainder (ℓ ^ 2)⁻¹ ρ e Acl (Vc hh) t y :=
      cleanupRemainder_isZ2Periodic (ℓ ^ 2)⁻¹ ρ e hAcl (Vc hh) t M hM (hslow hh hhh)
        (hfast hh hhh) n y
    rw [hp]
  have hforce : (fun x => rs ^ j • orderedDerivative β
      (fun x' => tailForcePhys (ψ t) H N Acl εc (ℓ ^ 2) ρ e Vc t x') x) =
      fun x => rs ^ j • orderedDerivative β (fun x' => q (ψ t x')) x := rfl
  rw [hforce]
  refine (scalar_slice hC hj hψr hqc hqp hDχ hrs hsR hJψ π β).trans ?_
  -- the label words
  set X0 : ℝ≥0∞ := ENNReal.ofReal (((ℓ ^ 2)⁻¹ * εc ^ (N + 1) * (e / ρ) ^ Acl * ρ * S) ^ 2) *
    ResidualTimeData.gradDensity π ρ m (fun s y => u s (χ s y)) t with hX0
  have hw : ∀ i ∈ Finset.range (j + 1), ∀ w : DerivativeWord2 i,
      scalInt π (fun x => rs ^ i • orderedDerivative w q x) ≤
        ENNReal.ofReal (((H + 1 : ℕ) : ℝ) ^ 2 * TailDiff.remConst N D Acl r i) * X0 := by
    intro i hi w
    have hir : i ≤ r := (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)).trans hj
    have e1 : (fun x => rs ^ i • orderedDerivative w q x) = fun x =>
        ∑ hh ∈ Finset.range (H + 1), rs ^ i • orderedDerivative w (fun y => (ℓ ^ 2)⁻¹ •
          εc ^ (N + 1) • cleanupRemainder (ℓ ^ 2)⁻¹ ρ e Acl (Vc hh) t y) x := by
      funext x
      rw [MixedTail.orderedDerivative_sum _ w fun hh hhm => hg hh hhm i hir, Finset.smul_sum]
    have hsum := scalInt_sum_le (Finset.range (H + 1)) (fun hh x => rs ^ i • orderedDerivative w
        (fun y => (ℓ ^ 2)⁻¹ • εc ^ (N + 1) • cleanupRemainder (ℓ ^ 2)⁻¹ ρ e Acl (Vc hh) t y) x)
      (fun hh hhm => (continuous_orderedDerivative w (hg hh hhm i hir)).fun_const_smul (rs ^ i)) π
    refine (le_of_eq (congrArg (scalInt π) e1)).trans (hsum.trans ?_)
    have hgr : ∀ hh ∈ Finset.range (H + 1), scalInt π (fun x => rs ^ i • orderedDerivative w
        (fun y => (ℓ ^ 2)⁻¹ • εc ^ (N + 1) • cleanupRemainder (ℓ ^ 2)⁻¹ ρ e Acl (Vc hh) t y) x) ≤
        ENNReal.ofReal (TailDiff.remConst N D Acl r i) * X0 := by
      intro hh hhm
      have hhh : hh ≤ H := Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)
      have hb := (hTT hh hhh).rem_pointwise (Vc := Vc hh) hS hrs hrse heρ hM hir w hpq0
      refine hb.trans (le_of_eq ?_)
      have hrc := TailDiff.remConst_nonneg N D Acl r i
      rw [show ((ℓ ^ 2)⁻¹ * εc ^ (N + 1) * (e / ρ) ^ Acl * ρ *
          Real.sqrt (TailDiff.remConst N D Acl r i) * S) ^ 2 =
          TailDiff.remConst N D Acl r i * ((ℓ ^ 2)⁻¹ * εc ^ (N + 1) * (e / ρ) ^ Acl * ρ * S) ^ 2 by
        rw [mul_pow, mul_pow, Real.sq_sqrt hrc]; ring,
        ENNReal.ofReal_mul hrc, mul_assoc]
    calc ((Finset.range (H + 1)).card : ℝ≥0∞) * ∑ hh ∈ Finset.range (H + 1),
          scalInt π (fun x => rs ^ i • orderedDerivative w (fun y => (ℓ ^ 2)⁻¹ •
            εc ^ (N + 1) • cleanupRemainder (ℓ ^ 2)⁻¹ ρ e Acl (Vc hh) t y) x)
        ≤ ((Finset.range (H + 1)).card : ℝ≥0∞) * ∑ _hh ∈ Finset.range (H + 1),
            ENNReal.ofReal (TailDiff.remConst N D Acl r i) * X0 := by
          gcongr with hh hhm
          exact hgr hh hhm
      _ = _ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc, ← mul_assoc]
          congr 1
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
          ring
  have hfcn : ∀ i, 0 ≤ ((H + 1 : ℕ) : ℝ) ^ 2 * TailDiff.remConst N D Acl r i := fun i =>
    mul_nonneg (by positivity) (TailDiff.remConst_nonneg N D Acl r i)
  have hsum : ∑ i ∈ Finset.range (j + 1), ∑ w : DerivativeWord2 i,
      scalInt π (fun x => rs ^ i • orderedDerivative w q x) ≤
      ENNReal.ofReal (∑ i ∈ Finset.range (r + 1), (2 : ℝ) ^ i *
        (((H + 1 : ℕ) : ℝ) ^ 2 * TailDiff.remConst N D Acl r i)) * X0 := by
    calc ∑ i ∈ Finset.range (j + 1), ∑ w : DerivativeWord2 i,
          scalInt π (fun x => rs ^ i • orderedDerivative w q x)
        ≤ ∑ i ∈ Finset.range (j + 1), ∑ _w : DerivativeWord2 i,
            ENNReal.ofReal (((H + 1 : ℕ) : ℝ) ^ 2 * TailDiff.remConst N D Acl r i) * X0 :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun w _ => hw i hi w
      _ = ENNReal.ofReal (∑ i ∈ Finset.range (j + 1), (2 : ℝ) ^ i *
            (((H + 1 : ℕ) : ℝ) ^ 2 * TailDiff.remConst N D Acl r i)) * X0 := by
          rw [ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg (by positivity) (hfcn i),
            Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          have h2 : ((2 ^ i : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) ^ i) := by
            rw [ENNReal.ofReal_pow (by norm_num)]
            simp
          rw [Finset.sum_const, card_derivativeWord2, nsmul_eq_mul, h2]
          conv_rhs => rw [ENNReal.ofReal_mul (by positivity)]
          rw [mul_assoc]
      _ ≤ _ := by
          gcongr ?_ * X0
          exact ENNReal.ofReal_le_ofReal
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ hj))
              fun i _ _ => mul_nonneg (by positivity) (hfcn i))
  have hgd := gradDensity_comp_le (Φ := χ) hC u hu hup hχm hDχ P.ρ_pos hρR hJχm π
  calc ENNReal.ofReal (scalarConst Dχ r) *
        ∑ i ∈ Finset.range (j + 1), ∑ w : DerivativeWord2 i,
          scalInt π (fun x => rs ^ i • orderedDerivative w q x)
      ≤ ENNReal.ofReal (scalarConst Dχ r) *
          (ENNReal.ofReal (∑ i ∈ Finset.range (r + 1), (2 : ℝ) ^ i *
            (((H + 1 : ℕ) : ℝ) ^ 2 * TailDiff.remConst N D Acl r i)) * X0) := by gcongr
    _ ≤ ENNReal.ofReal (scalarConst Dχ r) *
          (ENNReal.ofReal (∑ i ∈ Finset.range (r + 1), (2 : ℝ) ^ i *
            (((H + 1 : ℕ) : ℝ) ^ 2 * TailDiff.remConst N D Acl r i)) *
          (ENNReal.ofReal (((ℓ ^ 2)⁻¹ * εc ^ (N + 1) * (e / ρ) ^ Acl * ρ * S) ^ 2) *
            (ENNReal.ofReal (ChartTransport.densConst m 1 1 ((m + 1).factorial * Dχ ^ (m + 1))) *
              ResidualTimeData.gradDensity π ρ m u t))) := by
        rw [hX0]
        gcongr
    _ = _ := by
        unfold tailForceConst
        have h1 : 0 ≤ scalarConst Dχ r := scalarConst_nonneg r
        have h2 : 0 ≤ ∑ i ∈ Finset.range (r + 1), (2 : ℝ) ^ i *
            (((H + 1 : ℕ) : ℝ) ^ 2 * TailDiff.remConst N D Acl r i) :=
          Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (hfcn i)
        rw [ENNReal.ofReal_mul (mul_nonneg h1 h2), ENNReal.ofReal_mul h1]
        ring
end

end AVRegularity.CycleComparison.Reconstruction
end
