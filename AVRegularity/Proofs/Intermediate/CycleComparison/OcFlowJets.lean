-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Residual.TailJets
public import AVRegularity.Statements.Intermediate.CycleComparison.ResidualNorm
public import AVRegularity.Statements.Intermediate.CycleReference.JacMatrix
public import AVRegularity.Definitions.CycleComparison.IsLiftTailPresentation
import AVRegularity.CycleComparison.Charts.ChartDeviation
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Construction.IsOCStreamSeq
public import AVRegularity.Statements.Construction.OcA
public import AVRegularity.Statements.Intermediate.CycleReference.StreamFlow
import AVRegularity.CycleComparison.CleanupChain.Main
import AVRegularity.CycleComparison.Residual.ChartTransport.Part1
import Mathlib.Tactic.Monotonicity.Lemmas

@[expose] public section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers

/-! Proof of `cycle_residual_cleanup`: the cleanup identity of the cell residual, from the
fixed-time identity `AVRegularity.cleanup_identity`. -/

/-- **Cycle residual: the cleanup identity** (used in the proof of Lemma 12.4 of the paper). -/
theorem cycle_residual_cleanup (Acl sX sZ : ℕ) (hA : 1 ≤ Acl) (hX : Acl + 1 ≤ sX) (hZ : 1 ≤ sZ) :
    ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
      (ρ e c : ℝ) (T : Set ℝ), 0 < ρ → 0 < e →
      ∀ (f₀ : ℝ → Vec 2 → Vec 2 → ∀ i, h i) (F₀ : ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
        (Vc : ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i),
        (∀ τ ∈ T, IsBoxSmooth sX sZ (F₀ τ)) →
        (∀ τ ∈ T, IsCleanupChain sX sZ Acl (f₀ τ) (F₀ τ) (fun j => Vc j τ)) →
        ∀ t, c * t ∈ T → ∀ x,
          diagSample c ρ e (fun τ X z => f₀ τ X z + ∑ k : Fin 2,
              fastPartial k (fun X' z' => F₀ τ X' z' k) X z) t x
            = ∑ k : Fin 2, fderiv ℝ (fun x' => cleanupFlux c ρ e Acl Vc t x' k) x (basisVec k)
              + cleanupRemainder c ρ e Acl Vc t x := by
  intro ι _ h _ _ _ _ ρ e c T hρ he f₀ F₀ Vc hF hV t ht x
  exact cleanup_identity hA (by omega) hZ hρ.ne' he.ne' (hF _ ht) (hV _ ht) x

/-! Proof of `cycle_residual_chart_transport` (exact chart transport of differentiated residual
presentations), assembled from the three parts in the module
`AVRegularity.CycleComparison.Residual.BoundPointwise`. -/

/-- **Exact chart transport of differentiated presentations** (Step 4 of the proof of Lemma 12.4 of
    the paper). -/
theorem cycle_residual_chart_transport (m r : ℕ) (Cχ : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
        (π : ι → ℝ) (ν B ρ rs Rχ t₀ t₁ : ℝ) (Φ Ψ : ℝ → Vec 2 → Vec 2),
        0 < rs → rs ≤ ρ → ρ ≤ Rχ →
        (∀ t y, Ψ t (Φ t y) = y) → (∀ t x, Φ t (Ψ t x) = x) →
        (∀ t (n : Fin 2 → ℤ) y,
          Φ t (y + AVenhance.latticeShift n) = Φ t y + AVenhance.latticeShift n) →
        (∀ t y, (jacMatrix (Φ t) y).det = 1) →
        (∀ t, ContDiff ℝ ((m + r + 2 : ℕ) : ℕ∞) (Φ t)) →
        (∀ t, ContDiff ℝ ((m + r + 2 : ℕ) : ℕ∞) (Ψ t)) →
        (∀ t ∈ Set.Icc t₀ t₁, ∀ p, 1 ≤ p → p ≤ m + r + 2 → ∀ y,
          ‖iteratedFDeriv ℝ p (Φ t) y‖ ≤ Cχ p * Rχ⁻¹ ^ (p - 1) ∧
          ‖iteratedFDeriv ℝ p (Ψ t) y‖ ≤ Cχ p * Rχ⁻¹ ^ (p - 1)) →
        (∀ (R : ℝ → Vec 2 → Fin 2 → ∀ i, h i) (q : ℝ → Vec 2 → ∀ i, h i),
          (∀ t k, ContDiff ℝ (r : ℕ∞) (fun x => R t x k)) → (∀ t, ContDiff ℝ (r : ℕ∞) (q t)) →
          (∀ t k, AVenhance.IsZ2Periodic (fun x => R t x k)) →
          (∀ t, AVenhance.IsZ2Periodic (q t)) →
          (∀ j', j' ≤ r → ∀ (β' : DerivativeWord2 j') (k : Fin 2) (v : ι),
            Measurable (fun p : ℝ × Vec 2 =>
              ‖orderedDerivative β' (fun x => R p.1 x k) p.2 v‖ₑ)) →
          (∀ j', j' ≤ r → ∀ (β' : DerivativeWord2 j') (v : ι),
            Measurable (fun p : ℝ × Vec 2 => ‖orderedDerivative β' (q p.1) p.2 v‖ₑ)) →
          ∀ j, j ≤ r → ∀ β : DerivativeWord2 j,
            residualNorm ν π (Set.Icc t₀ t₁)
                (fun t x k => rs ^ j • orderedDerivative β
                  (fun x' => ∑ l : Fin 2, jacMatrix (Φ t) (Ψ t x') k l • R t (Ψ t x') l) x)
                (fun t x => rs ^ j • orderedDerivative β (fun x' => q t (Ψ t x')) x)
              ≤ ENNReal.ofReal C *
                ∑ j' ∈ Finset.range (j + 1), ∑ β' : DerivativeWord2 j',
                  residualNorm ν π (Set.Icc t₀ t₁)
                    (fun t x k => rs ^ j' • orderedDerivative β' (fun x' => R t x' k) x)
                    (fun t x => rs ^ j' • orderedDerivative β' (q t) x)) ∧
        (∀ a : ℝ → Vec 2 → ∀ i, h i,
          (∀ t, ContDiff ℝ ((m + r + 1 : ℕ) : ℕ∞) (a t)) → (∀ t, AVenhance.IsZ2Periodic (a t)) →
          classicalStrongEnergy ρ B π (Set.Icc t₀ t₁) (m + r) (fun t y => a t (Φ t y))
            ≤ ENNReal.ofReal C * classicalStrongEnergy ρ B π (Set.Icc t₀ t₁) (m + r) a) ∧
        (∀ Fc : ℝ → Vec 2 → Fin 2 → ∀ i, h i,
          (∀ t k, ContDiff ℝ ((m + r + 1 : ℕ) : ℕ∞) (fun x => Fc t x k)) →
          (∀ t k, AVenhance.IsZ2Periodic (fun x => Fc t x k)) →
          classicalFluxL2H ρ π (Set.Icc t₀ t₁) (m + r)
              (fun t y k => ∑ l : Fin 2, (jacMatrix (Φ t) y)⁻¹ k l • Fc t (Φ t y) l)
            ≤ ENNReal.ofReal C * classicalFluxL2H ρ π (Set.Icc t₀ t₁) (m + r) Fc) := by
  obtain ⟨C₁, h₁, H₁⟩ := ChartTransport.part1 m r Cχ
  obtain ⟨C₂, h₂, H₂⟩ := ChartTransport.part2 m r Cχ
  obtain ⟨C₃, h₃, H₃⟩ := ChartTransport.part3 m r Cχ
  refine ⟨max C₁ (max C₂ C₃), le_max_of_le_left h₁, ?_⟩
  intro ι _ h _ _ _ _ π ν B ρ rs Rχ t₀ t₁ Φ Ψ hrs hrsρ hρR hl hr heq hdet hΦ hΨ hjet
  refine ⟨?_, ?_, ?_⟩
  · intro R q hR hq hRp hqp hmR hmq j hj β
    refine (H₁ π ν B ρ rs Rχ t₀ t₁ Φ Ψ hrs hrsρ hρR hl hr heq hdet hΦ hΨ hjet R q hR hq hRp hqp
      hmR hmq j hj β).trans ?_
    exact mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal (le_max_left _ _)) zero_le
  · intro a ha hap
    refine (H₂ π B ρ rs Rχ t₀ t₁ Φ Ψ hrs hrsρ hρR hl hr heq hdet hΦ hΨ hjet a ha hap).trans ?_
    exact mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal (le_trans (le_max_left _ _) (le_max_right _ _))) zero_le
  · intro Fc hF hFp
    refine (H₃ π ρ rs Rχ t₀ t₁ Φ Ψ hrs hrsρ hρR hl hr heq hdet hΦ hΨ hjet Fc hF hFp).trans ?_
    exact mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal (le_trans (le_max_right _ _) (le_max_right _ _))) zero_le

end AVRegularity.Providers
end

section
open Homogenization
namespace AVRegularity.Providers

/-! Proof of `cycle_cleanup_chain_exists`, from
`AVRegularity.CleanupChain.exists_isCleanupChain`. -/

/-- **Existence of the cleanup chain**. -/
theorem cycle_cleanup_chain_exists {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (sX sZ A : ℕ) (hsZ : 1 ≤ sZ)
    (f₀ : Vec 2 → Vec 2 → E) (F₀ : Vec 2 → Vec 2 → Fin 2 → E)
    (hf : IsBoxSmooth (sX + A) (sZ + 1) f₀) (hfp : ∀ X, AVenhance.IsZ2Periodic (f₀ X))
    (hfm : ∀ X, fieldCellMean (f₀ X) = 0)
    (hF : IsBoxSmooth (sX + A) (sZ + 1) F₀) (hFp : ∀ X, AVenhance.IsZ2Periodic (F₀ X))
    (hFm : ∀ X (k : Fin 2), fieldCellMean (fun z => F₀ X z k) = 0) :
    ∃ V : ℕ → Vec 2 → Vec 2 → Fin 2 → E, IsCleanupChain sX sZ A f₀ F₀ V :=
  CleanupChain.exists_isCleanupChain sX sZ A hsZ f₀ F₀ hf hfp hfm hF hFp hFm

end AVRegularity.Providers
end

section
open Homogenization AVenhance
namespace AVRegularity.Providers

/-! Proof of `oc_flow_jets`: the normalized jets of the short flow
charts, from the Section 2 inverse-flow bounds of the velocity construction
(`CycleComparison.Charts.oc_flow_jets_main`). -/

/-- **Normalized jets of the short flow charts**. -/
theorem oc_flow_jets (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ c C : ℝ, 0 < c ∧ 1 ≤ C ∧
      ∀ (Λ : ℕ), 128 ≤ Λ → ∀ (Φ : ℕ → ℝ → Vec 2 → ℝ), IsOCStreamSeq α q Λ ζ Φ →
      ∀ (m : ℕ), 2 ≤ m → ∀ (hφ : IsAdmissibleStream (Φ (m - 1))) (t t' : ℝ),
        ocA α q Λ (m - 1) * |t - t'| ≤ c →
        ∀ (n : ℕ) (y : Vec 2),
          ‖iteratedFDeriv ℝ n (fun x => fderiv ℝ (fun z => streamFlow (Φ (m - 1)) hφ t z t') x -
              ContinuousLinearMap.id ℝ (Vec 2)) y‖ ≤
            C * (n.factorial : ℝ) * (C / ocEpsilon q Λ (m - 1)) ^ n *
              (ocA α q Λ (m - 1) * |t - t'|) :=
  CycleComparison.Charts.oc_flow_jets_main α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

end AVRegularity.Providers
end
