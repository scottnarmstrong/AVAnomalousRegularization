-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleReference.TorusChartEquation
import AVRegularity.CycleReference.ChartCorrectionIntegrability
public import AVRegularity.Definitions.CycleReference.OcRefCorrector
public import AVRegularity.Definitions.CycleReference.OcAsymp
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain
public import AVRegularity.Statements.Intermediate.CycleReference.OcDStar
public import AVRegularity.Statements.Intermediate.CycleReference.OcEll
public import AVRegularity.Statements.Intermediate.CycleReference.OcMaterialMetric
public import AVRegularity.Statements.Intermediate.CycleReference.OcPulseStream
public import AVRegularity.Statements.Intermediate.CycleReference.OcRhoMol
public import AVRegularity.Statements.Intermediate.CycleReference.OcTransition
import AVRegularity.Construction.Scales.Times
import AVRegularity.Construction.Stream.NextAdmissible
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Order.CompletePartialOrder

@[expose] public section

section
open MeasureTheory Homogenization AVenhance
open scoped Matrix
namespace AVRegularity.Providers

/-! Proof of the reference-flux bounds and full-period mean statement. -/

/-- **Reference flux (bounds, periodicity, scalar mean)** (Lemma 6.10 of the paper). -/
theorem cycle_flux_bounds (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∀ Λ : ℕ, 128 ≤ Λ → ∀ m : ℕ, 1 ≤ m → ∀ ν : ℝ, 0 < ν →
      (∀ t : ℝ,
        (ocRefFlux α q Λ ζ m ν t - ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosSemidef ∧
        ((ν + ocHStar α q Λ m ν) • (1 : Matrix (Fin 2) (Fin 2) ℝ) - ocRefFlux α q Λ ζ m ν t).PosSemidef) ∧
      (∀ t : ℝ, ocRefFlux α q Λ ζ m ν t 0 1 = 0 ∧ ocRefFlux α q Λ ζ m ν t 1 0 = 0) ∧
      (∀ t : ℝ, ocRefFlux α q Λ ζ m ν (t + 4 * ocTauPP α q Λ m) = ocRefFlux α q Λ ζ m ν t) ∧
      (∀ t : ℝ, ocRefFlux α q Λ ζ m ν (t + 2 * ocTauPP α q Λ m) =
        sigmaMat * ocRefFlux α q Λ ζ m ν t * sigmaMatᵀ) ∧
      (∀ t : ℝ, ∃ v : Vec 2, v ≠ 0 ∧
        (ocRefFlux α q Λ ζ m ν t).mulVec v = ν • v) ∧
      (∀ t : ℝ, (∀ k : ℤ, Odd k → ocPulse α q Λ ζ m k t = 0) →
        ocRefFlux α q Λ ζ m ν t = ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
      (∀ s : ℝ, ∀ i j : Fin 2,
        (4 * ocTauPP α q Λ m)⁻¹ *
          ∫ t in s..(s + 4 * ocTauPP α q Λ m), ocRefFlux α q Λ ζ m ν t i j =
          ocMeanFlux α q Λ ζ m ν * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j) := by
  intro Λ hΛ m hm ν hν
  have hΛ' : 1 ≤ Λ := by omega
  clear hm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    exact CycleReference.refFlux_pointwise_posSemidef hΛ' hζ hν
  · intro t
    exact CycleReference.refFlux_diagonal hΛ' hζ hν
  · intro t
    exact CycleReference.refFlux_time_shift_four hΛ' ν t (ocTauPP α q Λ m) rfl
  · intro t
    exact CycleReference.refFlux_time_shift_two hΛ' hζ ν t (ocTauPP α q Λ m) rfl
  · intro t
    exact CycleReference.refFlux_has_molecular_eigenvector hΛ' hζ hν
  · intro t hp
    have hp' : ∀ k : {k : ℤ // Odd k}, ocPulse α q Λ ζ m k.1 t = 0 :=
      fun k => hp k.1 k.2
    unfold ocRefFlux
    rw [CycleReference.pulseMatrixSum_eq_zero_of_quiet
      (α := α) (q := q) (Λ := Λ) (m := m) (ζ := ζ) ν t hp']
    simp
  · intro s i j
    exact CycleReference.refFlux_window_mean_entry hΛ' hζ hν s i j

end AVRegularity.Providers
end

section
open Homogenization AVenhance
open scoped Matrix
open AVRegularity.CycleReference
namespace AVRegularity.Providers

/-- **Renewal transitions** (Lemma 6.7(b) of the paper). -/
theorem cycle_flux_transition (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (_hζ : IsFastProfile ζ) :
    ∀ Λ : ℕ, 128 ≤ Λ → ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
      ∀ m : ℕ, 1 ≤ m → ∀ hφ : IsAdmissibleStream (Φ (m - 1)), ∀ l : ℤ,
        (∀ t : ℝ, ∀ y : Vec 2,
          ocChart α q Λ m (Φ (m - 1)) hφ (l + 1) t y =
            ocChart α q Λ m (Φ (m - 1)) hφ l t (ocTransition α q Λ m (Φ (m - 1)) hφ l (l + 1) y)) ∧
        (∀ θ : ℝ → Vec 2 → ℝ, ∀ t : ℝ, ∀ y : Vec 2,
          θ t (ocChart α q Λ m (Φ (m - 1)) hφ (l + 1) t y) =
            θ t (ocChart α q Λ m (Φ (m - 1)) hφ l t (ocTransition α q Λ m (Φ (m - 1)) hφ l (l + 1) y))) ∧
        (∀ t : ℝ, ∀ y : Vec 2,
          ocMaterialMetric α q Λ m (Φ (m - 1)) hφ (l + 1) t y =
            (jacMatrix (ocTransition α q Λ m (Φ (m - 1)) hφ l (l + 1)) y)⁻¹ *
              ocMaterialMetric α q Λ m (Φ (m - 1)) hφ l t (ocTransition α q Λ m (Φ (m - 1)) hφ l (l + 1) y) *
              ((jacMatrix (ocTransition α q Λ m (Φ (m - 1)) hφ l (l + 1)) y)⁻¹)ᵀ) ∧
        (∀ y : Vec 2, (jacMatrix (ocTransition α q Λ m (Φ (m - 1)) hφ l (l + 1)) y).det = 1) :=
  by
    intro Λ _hΛ Φ _hseq m _hm hφ l
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact chart_transition_comp α q Λ m hφ l (l + 1)
    · intro θ t y
      rw [chart_transition_comp α q Λ m hφ l (l + 1) t y]
    · exact metric_transition α q Λ m hφ l (l + 1)
    · exact transition_jacMatrix_det_one α q Λ m hφ l (l + 1)

end AVRegularity.Providers
end

section
open MeasureTheory Homogenization AVenhance
open scoped Matrix
namespace AVRegularity.Providers

/-- **Reference corrector reproduces the flux** (Lemma 9.2(b) of the paper). -/
theorem cycle_flux_corrector_mean (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∀ Λ : ℕ, 128 ≤ Λ → ∀ m : ℕ, 1 ≤ m → ∀ ν : ℝ, 0 < ν → ∀ t : ℝ, ∀ i j : Fin 2,
      ∫ y in unitCube,
          ((ν • (1 : Matrix (Fin 2) (Fin 2) ℝ) + ocPulseStream α q Λ ζ m t y • sigmaMat) *
            ((1 : Matrix (Fin 2) (Fin 2) ℝ) + (jacMatrix (ocRefCorrector α q Λ ζ m ν t) y)ᵀ)) i j
        = ocRefFlux α q Λ ζ m ν t i j :=
 by
  intro Λ hΛ m hm ν hν t i j
  exact CycleReference.refCorrector_cell_mean (by omega) hm hζ hν t i j

end AVRegularity.Providers
end

section
open MeasureTheory Homogenization AVenhance
open AVRegularity.CycleReference
namespace AVRegularity.Providers

/-- **Complete cores and block coercivity**. -/
theorem cycle_flux_block_coercivity (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∀ Λ : ℕ, 128 ≤ Λ → ∀ m : ℕ, 1 ≤ m → ∀ ν : ℝ, 0 < ν →
      (∀ l : ℤ, ∀ r : ℤ, (r = 1 ∨ r = 3) →
        ∃ S : Finset ℤ, (ocL α q Λ m : ℝ) ^ 2 / 32 ≤ S.card ∧
          ∀ k ∈ S, k % 4 = r ∧ IsOCCompleteCore α q Λ m l k) ∧
      (6 ≤ ocMu q Λ m ν * ocTau α q Λ m →
        (∀ l : ℤ, ∀ v : Vec 2,
          (ν + (1 - Real.exp (-2)) / 96 * ocHStar α q Λ m ν) * ocTauPP α q Λ m * vecDot v v
            ≤ ∫ t in (((l : ℝ) - 1 / 2) * ocTauPP α q Λ m)..(((l : ℝ) + 1 / 2) * ocTauPP α q Λ m),
                vecDot v ((ocRefFlux α q Λ ζ m ν t).mulVec v)) ∧
        ((1 - Real.exp (-2)) / 96 * (ν + ocHStar α q Λ m ν) ≤ ocMeanFlux α q Λ ζ m ν ∧
          ocMeanFlux α q Λ ζ m ν ≤ ν + ocHStar α q Λ m ν) ∧
        (∀ s t : ℝ, 3 * ocTauPP α q Λ m ≤ t - s → ∀ v : Vec 2,
          (1 - Real.exp (-2)) / 96 / 3 * ocMeanFlux α q Λ ζ m ν * (t - s) * vecDot v v
            ≤ ∫ r in s..t, vecDot v ((ocRefFlux α q Λ ζ m ν r).mulVec v))) :=
  by
    intro Λ hΛ m _hm ν hν
    have hΛ' : 1 ≤ Λ := by omega
    refine ⟨complete_cores_exist hΛ', ?_⟩
    intro hrelax
    exact ⟨refFlux_block_qform_lower hΛ' hζ hν hrelax,
      refFlux_mean_core_bounds hΛ' hζ hν hrelax,
      refFlux_long_qform_lower hΛ' hζ hν hrelax⟩

end AVRegularity.Providers
end

section
open MeasureTheory Homogenization AVenhance
namespace AVRegularity.Providers

/-- **Corrector equation and switching residual** (Lemma 9.2(b) of the paper). -/
theorem cycle_flux_corrector_equation (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, ∀ Λ : ℕ, 128 ≤ Λ → ∀ m : ℕ, 1 ≤ m → ∀ ν : ℝ, 0 < ν →
      (∀ t : ℝ, ∀ y : Vec 2, ∀ j : Fin 2,
        deriv (fun s => ocRefCorrector α q Λ ζ m ν s y j) t
          - ν * ∑ i : Fin 2, fderiv ℝ
              (fun y' => fderiv ℝ (fun y'' => ocRefCorrector α q Λ ζ m ν t y'' j) y' (basisVec i)) y (basisVec i)
          + ∑ i : Fin 2, streamVel (ocPulseStream α q Λ ζ m) t y i
              * fderiv ℝ (fun y' => ocRefCorrector α q Λ ζ m ν t y' j) y (basisVec i)
          + streamVel (ocPulseStream α q Λ ζ m) t y j
        = ∑' k : {k : ℤ // Odd k},
            deriv (fun s => ocCutoff α q Λ m k.1 s) t * ocPulseCorrector α q Λ ζ m ν k.1 t y j) ∧
      (∀ t : ℝ, ∀ y : Vec 2,
        Real.sqrt (vecNormSq (∑' k : {k : ℤ // Odd k},
            deriv (fun s => ocCutoff α q Λ m k.1 s) t • ocPulseCorrector α q Λ ζ m ν k.1 t y))
          ≤ C * ocA α q Λ m * ocEpsilon q Λ m / (ocMu q Λ m ν * ocTau α q Λ m)
              * Real.exp (-(ocMu q Λ m ν) * ocTau α q Λ m / 12)) :=
 by
  obtain ⟨C, hC⟩ := CycleReference.switching_residual_bound (α := α) (q := q) hζ
  refine ⟨C, ?_⟩
  intro Λ hΛ m _hm ν hν
  have hΛ' : 1 ≤ Λ := by omega
  constructor
  · exact fun t y j => CycleReference.refCorrector_equation hΛ' hζ ν t y j
  · exact hC Λ hΛ' m ν hν

end AVRegularity.Providers
end

section
open AVRegularity.CycleReference
namespace AVRegularity.Providers

/-- **Mean enhancement**. -/
theorem cycle_flux_mean_enhancement (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, ∀ Λ : ℕ, 128 ≤ Λ → ∀ m : ℕ, 1 ≤ m → ∀ ν : ℝ, 0 < ν →
      |ocMeanFlux α q Λ ζ m ν - ν - 9 / 80 * ocEpsilon q Λ m ^ (2 * (1 + α)) / ν|
        ≤ C * (ocEpsilon q Λ m ^ (2 * (1 + α)) / ν) *
            (ocEpsilon q Λ m ^ 2 / (ν * ocTau α q Λ m)
              + ocEpsilon q Λ (m - 1) ^ ocDelta α q) :=
  by
    obtain ⟨C, hC⟩ := refFlux_mean_enhancement hζ
    refine ⟨C, ?_⟩
    intro Λ hΛ m _hm ν hν
    exact hC α q Λ m (by omega) ν hν

end AVRegularity.Providers
end

section
open Homogenization AVenhance
namespace AVRegularity.Providers

/-! Transition jets and remainder with a universal Euclidean norm constant. -/

/-- **Transition jets and Taylor remainder**. -/
theorem cycle_flux_transition_taylor (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, ∀ Λ : ℕ, 128 ≤ Λ → ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
      ∀ m : ℕ, 1 ≤ m → ∀ hφ : IsAdmissibleStream (Φ (m - 1)), ∀ l₁ l₂ : ℤ,
        (l₂ = l₁ + 1 ∨ l₁ = l₂ + 1) →
        (∀ y₀ : Vec 2,
          Real.sqrt (∑ i : Fin 2, ∑ j : Fin 2,
            (jacMatrix (ocTransition α q Λ m (Φ (m - 1)) hφ l₁ l₂) y₀ i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j) ^ 2)
            ≤ C * (ocA α q Λ (m - 1) * ocTauPP α q Λ m)) ∧
        (∀ j : ℕ, 2 ≤ j → ∀ y : Vec 2,
          derivArrayNorm (ocTransition α q Λ m (Φ (m - 1)) hφ l₁ l₂) j y
            ≤ C * (ocA α q Λ (m - 1) * ocTauPP α q Λ m) * (Nat.factorial (j - 1) : ℝ) * (C / ocEpsilon q Λ (m - 1)) ^ (j - 1)) ∧
        (∀ y₀ y : Vec 2,
          Real.sqrt (vecNormSq (ocTransition α q Λ m (Φ (m - 1)) hφ l₁ l₂ (y₀ + y) - ocTransition α q Λ m (Φ (m - 1)) hφ l₁ l₂ y₀ - (jacMatrix (ocTransition α q Λ m (Φ (m - 1)) hφ l₁ l₂) y₀).mulVec y))
            ≤ C * (ocA α q Λ (m - 1) * ocTauPP α q Λ m) * vecNormSq y / ocEpsilon q Λ (m - 1)) ∧
        (m = 1 → ∀ y : Vec 2, ocTransition α q Λ m (Φ (m - 1)) hφ l₁ l₂ y = y) := by
  refine ⟨2 ^ 40, ?_⟩
  intro Λ hΛ Φ hseq m hm hφ l₁ l₂ hl
  have hE := (Scales.epsilon_basic hq.1 hΛ (m := m - 1)).1
  have ha : 0 < ocA α q Λ (m - 1) := by
    exact Real.rpow_pos_of_pos hE _
  have hh := AVRegularity.Construction.Stream.ocTauPP_pos (α := α) (q := q)
    (Λ := Λ) (m := m) (by omega : 1 ≤ Λ)
  have hg : 0 ≤ ocA α q Λ (m - 1) * ocTauPP α q Λ m := (mul_pos ha hh).le
  have hf : ContDiff ℝ (⊤ : ℕ∞) (ocTransition α q Λ m (Φ (m - 1)) hφ l₁ l₂) :=
    CycleReference.streamFlow_spatial_smooth hφ _ _
  have hb : ∀ n i a, barNorm n (2 ^ 11 * (ocEpsilon q Λ (m - 1))⁻¹)
      (fun x => jacMatrix (ocTransition α q Λ m (Φ (m - 1)) hφ l₁ l₂) x i a -
        (1 : Matrix (Fin 2) (Fin 2) ℝ) i a) ≤
      ENNReal.ofReal (2 ^ 23 * (ocA α q Λ (m - 1) * ocTauPP α q Λ m)) := by
    by_cases h : m = 1
    · subst m
      rw [CycleReference.ocTransition_level_one hseq hφ l₁ l₂]
      intro n i a
      simp only [CycleReference.jacMatrix_identity, sub_self]
      rw [CycleReference.zero_barNorm]
      exact bot_le
    · exact CycleReference.transition_jacobian_bar_bounds α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
        Λ hΛ Φ hseq m (by omega) hφ l₁ l₂ hl
  obtain ⟨hjac, harr, hrem⟩ := CycleReference.transition_taylor_bounds_of_bar hf hg hE hb
  refine ⟨hjac, harr, hrem, ?_⟩
  intro h y
  subst m
  exact congrFun (CycleReference.ocTransition_level_one hseq hφ l₁ l₂) y

end AVRegularity.Providers
end

section
open MeasureTheory Homogenization AVenhance
open scoped Matrix
open AVRegularity.CycleReference
namespace AVRegularity.Providers

/-- **Material chart equation**. -/
theorem cycle_flux_chart_equation (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∀ Λ : ℕ, 128 ≤ Λ → ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
      ∀ m : ℕ, 1 ≤ m → ∀ hφ : IsAdmissibleStream (Φ (m - 1)), ∀ ν : ℝ, 0 < ν → ∀ l : ℤ,
        (∀ t : ℝ, ∀ u : Vec 2 → ℝ, MemL2On Set.univ u →
          ∫ y, u (ocChart α q Λ m (Φ (m - 1)) hφ l t y) ^ 2 = ∫ x, u x ^ 2) ∧
        (∀ t : ℝ, ∀ u : Vec 2 → ℝ, ∀ Du : Vec 2 → Vec 2,
          MemL2On Set.univ u → GradMemL2On Set.univ Du → HasWeakGradientOn Set.univ u Du →
          ∃ Du' : Vec 2 → Vec 2, GradMemL2On Set.univ Du' ∧
            HasWeakGradientOn Set.univ (fun y => u (ocChart α q Λ m (Φ (m - 1)) hφ l t y)) Du' ∧
            ∫ y, vecDot (Du' y) ((ocMaterialMetric α q Λ m (Φ (m - 1)) hφ l t y).mulVec (Du' y))
              = ∫ x, vecDot (Du x) (Du x)) ∧
        (∀ t₀ t₁ : ℝ, ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ t₀ → t₀ < t₁ →
          t₁ ≤ ((l : ℝ) + 1 / 2) * ocTauPP α q Λ m →
          ∀ (q' : ℝ → Vec 2 → Vec 2) (f : ℝ → Vec 2 → ℝ) (θ₀ : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ),
            IsPlaneEnergySolution (streamVel (Φ m)) (fun _ _ => ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)) t₀ t₁ q' f θ₀ θ ↔
            IsPlaneEnergySolution (fun _ _ => 0)
              (fun t y => ν • ocMaterialMetric α q Λ m (Φ (m - 1)) hφ l t y + ocPulseStream α q Λ ζ m t y • sigmaMat) t₀ t₁
              (fun t y => (jacMatrix (ocChart α q Λ m (Φ (m - 1)) hφ l t) y)⁻¹.mulVec (q' t (ocChart α q Λ m (Φ (m - 1)) hφ l t y)))
              (fun t y => f t (ocChart α q Λ m (Φ (m - 1)) hφ l t y))
              (fun y => θ₀ (ocChart α q Λ m (Φ (m - 1)) hφ l t₀ y))
              (fun t y => θ t (ocChart α q Λ m (Φ (m - 1)) hφ l t y))) :=
 by
  intro Λ hΛ Φ hseq m hm hφ ν _hν l
  refine ⟨?_, ?_, ?_⟩
  · intro t u _hu
    exact chart_integral α q Λ m hφ l t (fun x => u x ^ 2)
  · intro t u Du hu hDu hw
    exact chart_h1_energy α q Λ m hφ l t hu hDu hw
  · intro a c ha _hac hc q' f θ₀ θ
    exact ocChart_energy_solution_iff hζ hΛ hseq hm hφ ν l a c ha hc q' f θ θ₀

/-- **Material chart equation on the torus**. -/
theorem cycle_flux_chart_equation_torus (α s : ℝ) (_hα₀ : 0 < α) (_hα₁ : α < 1 / 3)
    (_hs₀ : 0 < s) (_hs₁ : s < (1 - α) / 2) (q : ℝ) (_hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∀ Λ : ℕ, 128 ≤ Λ → ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
      ∀ m : ℕ, 1 ≤ m → ∀ hφ : IsAdmissibleStream (Φ (m - 1)), ∀ ν : ℝ, 0 < ν → ∀ l : ℤ,
        (∀ t : ℝ, ∀ u : Vec 2 → ℝ, IsZ2Periodic u → MemL2On unitCube u →
          ∫ y in unitCube, u (ocChart α q Λ m (Φ (m - 1)) hφ l t y) ^ 2
            = ∫ x in unitCube, u x ^ 2) ∧
        (∀ t : ℝ, ∀ u : Vec 2 → ℝ, ∀ Du : Vec 2 → Vec 2, IsPeriodicH1With u Du →
          ∃ Du' : Vec 2 → Vec 2,
            IsPeriodicH1With (fun y => u (ocChart α q Λ m (Φ (m - 1)) hφ l t y)) Du' ∧
            ∫ y in unitCube,
                vecDot (Du' y) ((ocMaterialMetric α q Λ m (Φ (m - 1)) hφ l t y).mulVec (Du' y))
              = ∫ x in unitCube, vecDot (Du x) (Du x)) ∧
        (∀ t₀ t₁ : ℝ, ((l : ℝ) - 1 / 2) * ocTauPP α q Λ m ≤ t₀ → t₀ < t₁ →
          t₁ ≤ ((l : ℝ) + 1 / 2) * ocTauPP α q Λ m →
          ∀ (q' : ℝ → Vec 2 → Vec 2) (f : ℝ → Vec 2 → ℝ) (θ₀ : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ),
            (∀ t, IsZ2Periodic (q' t)) → (∀ t, IsZ2Periodic (f t)) → IsZ2Periodic θ₀ →
            (IsTorusEnergySolution (streamVel (Φ m)) (fun _ _ => ν • (1 : Matrix (Fin 2) (Fin 2) ℝ)) t₀ t₁ q' f θ₀ θ ↔
            IsTorusEnergySolution (fun _ _ => 0)
              (fun t y => ν • ocMaterialMetric α q Λ m (Φ (m - 1)) hφ l t y + ocPulseStream α q Λ ζ m t y • sigmaMat) t₀ t₁
              (fun t y => (jacMatrix (ocChart α q Λ m (Φ (m - 1)) hφ l t) y)⁻¹.mulVec (q' t (ocChart α q Λ m (Φ (m - 1)) hφ l t y)))
              (fun t y => f t (ocChart α q Λ m (Φ (m - 1)) hφ l t y))
              (fun y => θ₀ (ocChart α q Λ m (Φ (m - 1)) hφ l t₀ y))
              (fun t y => θ t (ocChart α q Λ m (Φ (m - 1)) hφ l t y)))) :=
  by
  intro Λ hΛ Φ hseq m hm hφ ν _hν l
  refine ⟨?_, ?_, ?_⟩
  · intro t u hp _hu
    exact streamFlow_cell_integral hφ t ((l : ℝ) * ocTauPP α q Λ m)
      (fun x => u x ^ 2) (fun k x => by dsimp only; rw [hp k x])
  · intro t u Du hu
    exact chart_cell_h1_energy α q Λ m hφ l t hu
  · intro a c ha hac hc q' f θ₀ θ hpq hpf hp₀
    exact ocChart_torus_energy_solution_iff hζ hΛ hseq hm hφ ν l a c ha hc q' f θ θ₀
      hac.le hpq hpf hp₀

end AVRegularity.Providers
end

section
open MeasureTheory Homogenization AVenhance
namespace AVRegularity.Providers

/-! Proof of the cycle diffusivity, covariance and quiet-memory statement. -/

/-- **Scales and time averaging**: the bands `ocBand` of display (1.18) of the paper are disjoint
and closed, and the scales of a band chain satisfy the listed relations. -/
theorem cycle_diffusivities (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      (∀ M M' : ℕ, 1 ≤ M → 1 ≤ M' → M ≠ M' → Disjoint (ocBand α q Λ M) (ocBand α q Λ M')) ∧
      (∀ M : ℕ, 1 ≤ M → IsClosed (ocBand α q Λ M)) ∧
      (∃ C : ℝ, 1 ≤ C ∧ ∀ M : ℕ, 1 ≤ M → ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
        (∀ m : ℕ, 1 ≤ m → m < M →
          ocAsymp C (κ m) (ocEpsilon q Λ m ^ ((1 + α) + ocGamma α q))) ∧
        (∀ m : ℕ, 2 ≤ m → m ≤ M → ∀ ν B : ℝ, κ m = ν → κ (m - 1) = B →
          ν ≤ B ∧
          ocAsymp C B (ocEpsilon q Λ (m - 1) ^ ((1 + α) + ocGamma α q)) ∧
          ocAsymp C B (ocEpsilon q Λ m ^ ((1 + α) - ocGamma α q)) ∧
          ν + ocEpsilon q Λ m ^ (2 * (1 + α)) / ν ≤ C * B ∧
          ocAsymp C (ocRh α q Λ m B) (ocEpsilon q Λ (m - 1) ^ (1 + ocC α q)) ∧
          ocDStar q Λ m ν B / ocEpsilon q Λ (m - 1) ≤ C * ocEpsilon q Λ (m - 1) ^ (ocGamma α q / 2 + 4 * ocDelta α q) ∧
          ocDStar q Λ m ν B / ocRhoPar α q Λ m ≤ C * ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q) ∧
          ocDStar q Λ m ν B / (ocRh α q Λ m B) ≤ C * ocEpsilon q Λ (m - 1) ^ (3 * ocDelta α q) ∧
          ocAsymp C (ocEpsilon q Λ m / (ocRh α q Λ m B)) (ocEpsilon q Λ (m - 1) ^ (q * ocGamma α q + 3 * ocDelta α q)) ∧
          ocEll q Λ m ν ^ 2 / ocTau α q Λ m ≤ C * ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q) ∧
          C⁻¹ * ocEpsilon q Λ (m - 1) ^ (-(6 * ocDelta α q)) ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2 ∧
          Real.sqrt (B / ν) ≤ C * ocEpsilon q Λ (m - 1) ^ (-(q * ocGamma α q)) ∧
          ocA α q Λ (m - 1) * ocTauPP α q Λ m ≤ C * ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q) ∧
          (m < M →
            ocAsymp C (ocDStar q Λ m ν B / ocEpsilon q Λ (m - 1)) (ocEpsilon q Λ (m - 1) ^ (ocGamma α q / 2 + 4 * ocDelta α q)) ∧
            ocAsymp C (ocDStar q Λ m ν B / ocRhoPar α q Λ m) (ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q)) ∧
            ocAsymp C (ocDStar q Λ m ν B / (ocRh α q Λ m B)) (ocEpsilon q Λ (m - 1) ^ (3 * ocDelta α q)) ∧
            ocAsymp C (ocEll q Λ m ν ^ 2 / ocTau α q Λ m) (ocEpsilon q Λ (m - 1) ^ (4 * ocDelta α q)) ∧
            ocAsymp C (ocTauPP α q Λ m / ocEll q Λ m ν ^ 2) (ocEpsilon q Λ (m - 1) ^ (-(6 * ocDelta α q))) ∧
            ocAsymp C (Real.sqrt (B / ν)) (ocEpsilon q Λ (m - 1) ^ (-(q * ocGamma α q))) ∧
            ∀ cMol : ℝ, 0 < cMol →
              ocAsymp C (ocRhoMol α q Λ m cMol ν) (cMol * ocEpsilon q Λ m ^ (1 + ocGamma α q / 2)) ∧
              ocRhoMol α q Λ m cMol ν / ocEpsilon q Λ m ^ (1 + ocC α q)
                ≤ C * cMol * ocEpsilon q Λ (m - 1) ^ (-(q * ocDelta α q))) ∧
          (m = M → B / ν ≤ C) ∧
          (∀ s t : ℝ, ∀ i j : Fin 2,
            |ocCovariance α q Λ ζ m ν B s t i j| ≤ C * B * ocTauP α q Λ m ∧
            |ocCovariance α q Λ ζ m ν B s t i j| / ocEpsilon q Λ (m - 1) ^ 2 ≤ C * ocEpsilon q Λ (m - 1) ^ (ocGamma α q + 3 * ocDelta α q) ∧
            |ocCovariance α q Λ ζ m ν B s t i j| / ocRhoPar α q Λ m ^ 2 + ocA α q Λ (m - 1) * |ocCovariance α q Λ ζ m ν B s t i j| / B ≤ C * ocEpsilon q Λ (m - 1) ^ (3 * ocDelta α q) ∧
            |ocCovariance α q Λ ζ m ν B s t i j| / (ocRh α q Λ m B) ^ 2 ≤ C * ocEpsilon q Λ (m - 1) ^ ocDelta α q))) ∧
      (∀ a b N : ℕ, ∃ mStar : ℕ, ∀ M : ℕ, ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
        ∀ m : ℕ, 2 ≤ m → mStar ≤ m → m ≤ M → ∀ k : ℤ, Odd k →
          ∀ t : ℝ, ((k : ℝ) + 3 / 4) * ocTau α q Λ m ≤ t → ∀ y : Vec 2,
            derivArrayNorm
              (fun y' => iteratedDeriv a
                (fun t' => ocPulseCorrector α q Λ ζ m (κ m) k t' y') t) b y
              ≤ ocEpsilon q Λ (m - 1) ^ (N : ℝ)) := by
  obtain ⟨C, hC, Ld, hLd, hd⟩ := CycleReference.bandChain_uniform_ledger hα₀ hα₁ hs₀ hs₁ hq hζ
  obtain ⟨Lq, hLq, hquiet⟩ := CycleReference.bandChain_quiet_derivatives hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨max Ld Lq, hLd.trans (le_max_left _ _), ?_⟩
  intro Λ hΛ
  have hΛd : Ld ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛq : Lq ≤ Λ := (le_max_right _ _).trans hΛ
  have h128 := hLd.trans hΛd
  refine ⟨?_, ?_, ⟨C, hC, hd Λ hΛd⟩, hquiet Λ hΛq⟩
  · intro M M' _hM _hM' hne
    exact CycleReference.bands_disjoint hα₀ hq h128 hne
  · intro M _hM
    exact CycleReference.band_isClosed α q Λ M

end AVRegularity.Providers
end
