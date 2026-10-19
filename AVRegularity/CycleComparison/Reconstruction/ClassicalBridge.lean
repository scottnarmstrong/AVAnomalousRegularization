-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Reconstruction.TorusSlices
public import AVRegularity.Statements.Intermediate.CycleOutput.IsClassicalRep
public import AVRegularity.CycleComparison.Reconstruction.PrimWeak
import Mathlib.Algebra.Order.Star.Real

/-! **Classical densities of classical representatives**. If `a` is a classical
representative of `W ∈ H^K(𝕋²)` at order `r`, then its classical factorial densities through
order `m ≤ r` (`classicalFactorialSq`, and `classicalGradFactorialSq` for `m + 1 ≤ r`) are the
truncated factorial norms of `W` (`classicalFactorialSq_eq_of_rep`,
`classicalGradFactorialSq_eq_of_rep`). The Galerkin cutoff contracts every jet, hence every
truncated factorial norm (`factorialNormSqUpTo_galerkinProj_le`,
`gradFactorialNormSqUpTo_galerkinProj_le`). -/

@[expose] public noncomputable section

open MeasureTheory Filter Topology Homogenization AVRegularity.Sobolev AVRegularity.ChartTransport
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal

namespace AVRegularity.CycleComparison.Reconstruction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]

/-- The jets of a torus Sobolev element with a classical representative are the cell `L²` norms
of the ordered derivatives of the representative. -/
theorem norm_val_of_classicalRep {K r : ℕ} {W : TorusHk K E} {a : Vec 2 → E}
    (ha : IsClassicalRep W a r) {j : ℕ} (hj : j ≤ r) (w : DerivativeWord2 j) :
    ‖W.val ⟨⟨j, Nat.lt_succ_of_le (hj.trans ha.1)⟩, w⟩‖ = cellL2 (orderedDerivative w a) := by
  have hjK : j ≤ K := hj.trans ha.1
  have hae : W.val ⟨⟨j, Nat.lt_succ_of_le hjK⟩, w⟩ =ᵐ[volume.restrict AVenhance.unitCube]
      orderedDerivative w a := by
    have h1 := ha.2.2.2 j hj w
    have h2 : torusJetOrder W j w = W.toFunction.jet ⟨⟨j, Nat.lt_succ_of_le hjK⟩, w⟩ := by
      funext x
      simp only [torusJetOrder, hjK, ↓reduceDIte]
    rw [h2] at h1
    exact (periodicJetRepresentative_ae W.val _).symm.trans h1
  rw [Lp.norm_def]
  unfold cellL2
  rw [eLpNorm_congr_ae hae]

/-- The squared jets of a classical representative, as lower integrals. -/
theorem ofReal_norm_val_sq_of_classicalRep {K r : ℕ} {W : TorusHk K E} {a : Vec 2 → E}
    (ha : IsClassicalRep W a r) {j : ℕ} (hj : j ≤ r) (w : DerivativeWord2 j) :
    ENNReal.ofReal (‖W.val ⟨⟨j, Nat.lt_succ_of_le (hj.trans ha.1)⟩, w⟩‖ ^ 2) =
      ∫⁻ x in AVenhance.unitCube, ‖orderedDerivative w a x‖ₑ ^ 2 := by
  rw [norm_val_of_classicalRep ha hj w]
  have hc : Continuous (orderedDerivative w a) :=
    continuous_orderedDerivative w (ha.2.1.of_le (by exact_mod_cast hj))
  exact ofReal_cellL2_sq (Coarse.memLp_two_cell_of_continuous hc)

/-- **The classical factorial density of a classical representative** is the truncated factorial
norm of the element. -/
theorem classicalFactorialSq_eq_of_rep {K r : ℕ} {W : TorusHk K E} {a : Vec 2 → E}
    (ha : IsClassicalRep W a r) (ρ : ℝ) {m : ℕ} (hm : m ≤ r) :
    classicalFactorialSq ρ m a = ENNReal.ofReal (factorialNormSqUpTo ρ m W.val) := by
  have hmK : m ≤ K := hm.trans ha.1
  set g : ℕ → ℝ≥0∞ := fun j => if j ≤ m then ENNReal.ofReal (factorialWeight ρ j) *
    ∑ w : DerivativeWord2 j, ∫⁻ x in AVenhance.unitCube, ‖orderedDerivative w a x‖ₑ ^ 2 else 0
    with hg
  have hterm : ∀ j : Fin (K + 1), ENNReal.ofReal (if j.val ≤ m then factorialWeight ρ j.val *
      derivativeNormSq W.val j else 0) = g j.val := by
    intro j
    by_cases hjm : j.val ≤ m
    · simp only [hg, hjm, ↓reduceIte]
      unfold derivativeNormSq
      rw [ENNReal.ofReal_mul (factorialWeight_nonneg _ _),
        ENNReal.ofReal_sum_of_nonneg fun _ _ => sq_nonneg _]
      congr 1
      refine Finset.sum_congr rfl fun w _ => ?_
      exact ofReal_norm_val_sq_of_classicalRep ha (hjm.trans hm) w
    · simp only [hg, hjm, ↓reduceIte, ENNReal.ofReal_zero]
  unfold factorialNormSqUpTo
  rw [ENNReal.ofReal_sum_of_nonneg fun j _ => by
    split_ifs
    · exact mul_nonneg (factorialWeight_nonneg _ _) (derivativeNormSq_nonneg _ _)
    · exact le_rfl]
  rw [Finset.sum_congr rfl fun j _ => hterm j, Fin.sum_univ_eq_sum_range g (K + 1)]
  unfold classicalFactorialSq
  rw [← Finset.sum_range_add_sum_Ico g (Nat.succ_le_succ hmK)]
  have hzero : ∑ j ∈ Finset.Ico (m + 1) (K + 1), g j = 0 :=
    Finset.sum_eq_zero fun j hj => by
      have := (Finset.mem_Ico.1 hj).1
      rw [hg]
      simp only [show ¬ j ≤ m by omega, ↓reduceIte]
  rw [hzero, add_zero]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [hg]
  simp only [Nat.lt_succ_iff.1 (Finset.mem_range.1 hj), ↓reduceIte]
  rfl

/-- **The classical gradient factorial density of a classical representative** is the truncated
gradient factorial norm of the element. -/
theorem classicalGradFactorialSq_eq_of_rep {K r : ℕ} {W : TorusHk K E} {a : Vec 2 → E}
    (ha : IsClassicalRep W a r) (ρ : ℝ) {m : ℕ} (hm : m + 1 ≤ r) :
    classicalGradFactorialSq ρ m a = ENNReal.ofReal (gradFactorialNormSqUpTo ρ m W.val) := by
  have hmK : m + 1 ≤ K := hm.trans ha.1
  set g : ℕ → ℝ≥0∞ := fun j => if 1 ≤ j ∧ j ≤ m + 1 then
    ENNReal.ofReal (factorialWeight ρ (j - 1)) *
      ∑ w : DerivativeWord2 j, ∫⁻ x in AVenhance.unitCube, ‖orderedDerivative w a x‖ₑ ^ 2
    else 0 with hg
  have hterm : ∀ j : Fin (K + 1), ENNReal.ofReal (if 1 ≤ j.val ∧ j.val ≤ m + 1 then
      factorialWeight ρ (j.val - 1) * derivativeNormSq W.val j else 0) = g j.val := by
    intro j
    by_cases hjm : 1 ≤ j.val ∧ j.val ≤ m + 1
    · simp only [hg, hjm.1, hjm.2, and_self, ↓reduceIte]
      unfold derivativeNormSq
      rw [ENNReal.ofReal_mul (factorialWeight_nonneg _ _),
        ENNReal.ofReal_sum_of_nonneg fun _ _ => sq_nonneg _]
      congr 1
      refine Finset.sum_congr rfl fun w _ => ?_
      exact ofReal_norm_val_sq_of_classicalRep ha (hjm.2.trans hm) w
    · simp only [hg, hjm, ↓reduceIte, ENNReal.ofReal_zero]
  unfold gradFactorialNormSqUpTo
  rw [ENNReal.ofReal_sum_of_nonneg fun j _ => by
    split_ifs
    · exact mul_nonneg (factorialWeight_nonneg _ _) (derivativeNormSq_nonneg _ _)
    · exact le_rfl]
  rw [Finset.sum_congr rfl fun j _ => hterm j, Fin.sum_univ_eq_sum_range g (K + 1)]
  unfold classicalGradFactorialSq
  have hz0 : g 0 = 0 := by simp [hg]
  have hz1 : ∑ i ∈ Finset.Ico (m + 1) K, g (i + 1) = 0 :=
    Finset.sum_eq_zero fun i hi => by
      have := (Finset.mem_Ico.1 hi).1
      rw [hg]
      simp only [show ¬ (1 ≤ i + 1 ∧ i + 1 ≤ m + 1) by omega, ↓reduceIte]
  conv_rhs => rw [Finset.sum_range_succ', ← Finset.sum_range_add_sum_Ico _ (by omega : m + 1 ≤ K),
    hz1, hz0, add_zero, add_zero]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < m + 1 := Finset.mem_range.1 hj
  rw [hg]
  simp only [show 1 ≤ j + 1 ∧ j + 1 ≤ m + 1 from ⟨by omega, by omega⟩, Nat.add_sub_cancel]
  rfl

/-- The Galerkin cutoff contracts the truncated factorial norms. -/
theorem factorialNormSqUpTo_galerkinProj_le [FiniteDimensional ℝ E] {K : ℕ} (n : ℕ) (ρ : ℝ) (m : ℕ)
    (f : TorusHk K E) :
    factorialNormSqUpTo ρ m (galerkinProj n f).val ≤ factorialNormSqUpTo ρ m f.val := by
  unfold factorialNormSqUpTo
  refine Finset.sum_le_sum fun j _ => ?_
  split_ifs
  · refine mul_le_mul_of_nonneg_left ?_ (factorialWeight_nonneg _ _)
    unfold derivativeNormSq
    refine Finset.sum_le_sum fun w _ => ?_
    rw [galerkinProj_val]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (cellJetFourierProjection_component_norm_le K n f.val ⟨j, w⟩) 2
  · exact le_rfl

/-- The Galerkin cutoff contracts the truncated gradient factorial norms. -/
theorem gradFactorialNormSqUpTo_galerkinProj_le [FiniteDimensional ℝ E] {K : ℕ} (n : ℕ) (ρ : ℝ) (m :
    ℕ)
    (f : TorusHk K E) :
    gradFactorialNormSqUpTo ρ m (galerkinProj n f).val ≤ gradFactorialNormSqUpTo ρ m f.val := by
  unfold gradFactorialNormSqUpTo
  refine Finset.sum_le_sum fun j _ => ?_
  split_ifs
  · refine mul_le_mul_of_nonneg_left ?_ (factorialWeight_nonneg _ _)
    unfold derivativeNormSq
    refine Finset.sum_le_sum fun w _ => ?_
    rw [galerkinProj_val]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (cellJetFourierProjection_component_norm_le K n f.val ⟨j, w⟩) 2
  · exact le_rfl

end AVRegularity.CycleComparison.Reconstruction
