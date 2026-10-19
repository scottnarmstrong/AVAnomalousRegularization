-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.FibreScalarSeriesHighIncrementBound
import AVRegularity.CycleEvolution.CellBochnerCarrier
import AVRegularity.CycleEvolution.CellMeanProjection
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

section
section
/-! Uniform weak-entry bounds for the measurable cell Galerkin generator. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational AVRegularity.CoupledEnergy.Galerkin

namespace AVRegularity.CycleEvolution

/-- A bounded scalar multiplier controls each L² test pairing. -/
theorem cellCoefficient_pairing_abs_le (c : Vec 2 → ℂ)
    (hc : AEStronglyMeasurable c (volume.restrict AVenhance.unitCube))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x, ‖c x‖ ≤ M)
    (u z : ComplexCellL2) :
    |inner ℝ (cellCoefficientCLM c hc M hM hb u) z| ≤ M * ‖u‖ * ‖z‖ := by
  exact measurableCoefficientL2_inner_abs_le
    (fun x => ContinuousLinearMap.mul ℝ ℂ (c x))
    ((ContinuousLinearMap.mul ℝ ℂ).continuous.comp_aestronglyMeasurable hc)
    M hM (fun x => (scalarMultiply_norm_bound (c x)).trans (hb x)) u z

/-- Metric-entry multiplication bounds a fixed weak entry. -/
theorem cellMetric_pairing_abs_le
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    (t : ℝ) (j k : Fin 2) (u z : ComplexCellL2) :
    |inner ℝ (cellMetricEntryCLM hG t j k u) z| ≤ 2 * ‖u‖ * ‖z‖ := by
  unfold cellMetricEntryCLM
  exact cellCoefficient_pairing_abs_le _ _ _ _ _ _ _

/-- Drift-entry multiplication bounds a fixed weak entry. -/
theorem cellDrift_pairing_abs_le
    (C : CellCoefficients) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (t : ℝ) (j : Fin 2) (u z : ComplexCellL2) :
    |inner ℝ (cellDriftEntryCLM C V hv hb t j u) z| ≤ |V| * ‖u‖ * ‖z‖ := by
  unfold cellDriftEntryCLM
  exact cellCoefficient_pairing_abs_le _ _ _ _ _ _ _

/-- Constant complex multiplication has the expected L² norm. -/
theorem cellScalarCLM_norm (c : ℂ) (u : ComplexCellL2) :
    ‖cellScalarCLM c u‖ = ‖c‖ * ‖u‖ := by
  exact norm_smul c u

/-- Uniform diffusion entry bounds depend only on the fixed trial and test fields. -/
theorem cellDiffusionForm_abs_le (C : CellCoefficients) (hG : IsCellMetric C.G)
    (t : ℝ) (u z : TorusHk 1 ℂ) :
    |cellDiffusionForm C hG t u z| ≤
      ∑ j : Fin 2, ∑ k : Fin 2,
        2 * ‖cellShiftedDerivativeCLM C.θ j u‖ *
          ‖cellShiftedDerivativeCLM (fun i => star (C.θ i)) k z‖ := by
  simp only [cellDiffusionForm, neg_apply, sum_apply, pullbackInnerCLM_apply,
    ContinuousLinearMap.comp_apply, abs_neg]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k _
  exact cellMetric_pairing_abs_le hG t j k _ _

end AVRegularity.CycleEvolution

namespace AVRegularity.CycleEvolution

/-- A uniform weak generator bound, before the finite mass matrix is inverted. -/
theorem cellGeneratorForm_abs_le
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (hκ : ∀ t, ‖C.κ t‖ ≤ k) (t : ℝ) (u z : TorusHk 1 ℂ) :
    |cellGeneratorForm C hG V hv hb t u z| ≤
      (∑ j : Fin 2, ∑ l : Fin 2,
        2 * ‖cellShiftedDerivativeCLM C.θ j u‖ *
          ‖cellShiftedDerivativeCLM (fun i => star (C.θ i)) l z‖)
      + (∑ j : Fin 2, |V| * ‖cellShiftedDerivativeCLM C.θ j u‖ * ‖torusHkValueCLM z‖)
      + k * ‖torusHkValueCLM u‖ * ‖torusHkValueCLM z‖ := by
  have hd := cellDiffusionForm_abs_le C hG t u z
  have hvb : |∑ j : Fin 2, inner ℝ
      (cellDriftEntryCLM C V hv hb t j (cellShiftedDerivativeCLM C.θ j u))
      (torusHkValueCLM z)| ≤
      ∑ j : Fin 2, |V| * ‖cellShiftedDerivativeCLM C.θ j u‖ * ‖torusHkValueCLM z‖ := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    exact Finset.sum_le_sum (fun j _ => cellDrift_pairing_abs_le C V hv hb t j _ _)
  have hp : |inner ℝ (cellScalarCLM (C.κ t) (torusHkValueCLM u))
      (torusHkValueCLM z)| ≤ k * ‖torusHkValueCLM u‖ * ‖torusHkValueCLM z‖ := by
    apply (abs_real_inner_le_norm _ _).trans
    rw [cellScalarCLM_norm]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hκ t) (norm_nonneg _)) (norm_nonneg _)
  simp only [cellGeneratorForm, add_apply, sub_apply, sum_apply,
    pullbackInnerCLM_apply, ContinuousLinearMap.comp_apply]
  exact (abs_add_le _ _).trans (add_le_add
    ((abs_sub _ _).trans (add_le_add hd hvb)) hp)

/-- Fixed tests bound the scalar and divergence source pairings. -/
theorem cellSourceFunctional_abs_le (θ : Fin 2 → ℂ)
    (src : ComplexCellL2) (F : Fin 2 → ComplexCellL2) (z : TorusHk 1 ℂ) :
    |cellSourceFunctional θ src F z| ≤
      ‖src‖ * ‖torusHkValueCLM z‖ +
        ∑ j : Fin 2, ‖F j‖ * ‖cellShiftedDerivativeCLM (fun i => star (θ i)) j z‖ := by
  simp only [cellSourceFunctional, sub_apply, sum_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply]
  apply (abs_sub _ _).trans
  apply add_le_add (abs_real_inner_le_norm _ _)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  exact Finset.sum_le_sum (fun j _ => abs_real_inner_le_norm _ _)

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The periodic H¹ norm in value and gradient coordinates. -/

/-- The H¹ carrier norm is exactly the sum of the value and gradient squares. -/
theorem cellH1_norm_sq (u : TorusHk 1 ℂ) :
    ‖u‖ ^ 2 = ‖torusHkValueCLM u‖ ^ 2 + ∑ j, ‖cellDerivativeCLM j u‖ ^ 2 := by
  change ‖u.val‖ ^ 2 = _
  rw [jet_norm_sq_eq_sum, Fin.sum_univ_two]
  have h0 : derivativeNormSq u.val (0 : Fin 2) = ‖torusHkValueCLM u‖ ^ 2 := by
    change (∑ w : Fin 0 → Fin 2, ‖u.val ⟨0, w⟩‖ ^ 2) = _
    rw [Fintype.sum_unique]
    rfl
  have h1 : derivativeNormSq u.val (1 : Fin 2) = ∑ j, ‖cellDerivativeCLM j u‖ ^ 2 := by
    change (∑ w : Fin 1 → Fin 2, ‖u.val ⟨1, w⟩‖ ^ 2) =
      ∑ j : Fin 2, ‖u.val ⟨1, fun _ => j⟩‖ ^ 2
    exact ((Equiv.funUnique (Fin 1) (Fin 2)).symm.sum_comp
      (fun w => ‖u.val ⟨1, w⟩‖ ^ 2)).symm
  rw [h0, h1]

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
namespace AVRegularity.CycleEvolution

/-! Variable complex scalars act continuously and measurably on the genuine cell L² space. -/

theorem cellScalarCLM_smul (c : ℂ) (u : ComplexCellL2) : cellScalarCLM c u = c • u := rfl

theorem cellScalarCLM_variable_continuousOn {I : Set ℝ} (c : ℝ → ℂ)
    (hc : ContinuousOn c I) (u : ℝ → ComplexCellL2) (hu : ContinuousOn u I) :
    ContinuousOn (fun t => cellScalarCLM (c t) (u t)) I := by
  simpa only [cellScalarCLM_smul, Pi.smul_def'] using hc.smul hu

theorem cellScalarCLM_variable_memLp {μ : Measure ℝ} (c : ℝ → ℂ) (hc : MemLp c ⊤ μ)
    (u : ℝ → ComplexCellL2) (hu : MemLp u 2 μ) :
    MemLp (fun t => cellScalarCLM (c t) (u t)) 2 μ := by
  have ha : MemLp (c • u) 2 μ := hc.smul hu
  simpa only [cellScalarCLM_smul, Pi.smul_def'] using ha

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Literal affine dependence of the Bloch derivative on its complex frequency. -/

theorem cellShiftedDerivativeCLM_add_shift (θ δ : Fin 2 → ℂ) (j : Fin 2)
    (u : TorusHk 1 ℂ) :
    cellShiftedDerivativeCLM (θ + δ) j u = cellShiftedDerivativeCLM θ j u +
      cellScalarCLM (Complex.I * δ j) (torusHkValueCLM u) := by
  change cellDerivativeCLM j u + (Complex.I * (θ j + δ j)) • torusHkValueCLM u =
    (cellDerivativeCLM j u + (Complex.I * θ j) • torusHkValueCLM u) +
      (Complex.I * δ j) • torusHkValueCLM u
  rw [mul_add, add_smul]
  abel

end AVRegularity.CycleEvolution
end
end

section
@[expose] public section
namespace AVRegularity.CycleEvolution

/-! Scalar and vector source estimates in an arbitrary real Hilbert space. -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Scalar Hilbert forcing uses one squared value and one squared source norm. -/
theorem hilbertScalarSource_young (S u : H) : 2 * inner ℝ S u ≤ ‖S‖ ^ 2 + ‖u‖ ^ 2 := by
  have h := (le_abs_self (inner ℝ S u)).trans (abs_real_inner_le_norm S u)
  nlinarith [sq_nonneg (‖S‖ - ‖u‖)]

/-- A flux uses only one eighth of gradient dissipation. -/
theorem hilbertFluxSource_young (F p : Fin 2 → H) :
    2 * (-(∑ j : Fin 2, inner ℝ (F j) (p j))) ≤
      (1 / 8) * ∑ j, ‖p j‖ ^ 2 + 8 * ∑ j, ‖F j‖ ^ 2 := by
  have h (j : Fin 2) := (neg_le_abs (inner ℝ (F j) (p j))).trans
    (abs_real_inner_le_norm (F j) (p j))
  have h0 := h 0
  have h1 := h 1
  simp only [Fin.sum_univ_two]
  nlinarith [sq_nonneg (‖p 0‖ / 4 - 2 * ‖F 0‖), sq_nonneg (‖p 1‖ / 4 - 2 * ‖F 1‖)]

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Small complex shifts admit source estimates with a fixed gradient budget. -/

theorem cellShiftedDerivativeCLM_norm_le (θ : Fin 2 → ℂ) (j : Fin 2)
    (u : TorusHk 1 ℂ) :
    ‖cellShiftedDerivativeCLM θ j u‖ ≤
      ‖cellDerivativeCLM j u‖ + ‖θ j‖ * ‖torusHkValueCLM u‖ := by
  change ‖cellDerivativeCLM j u + cellScalarCLM (Complex.I * θ j) (torusHkValueCLM u)‖ ≤ _
  simpa only [cellScalarCLM_norm, norm_mul, Complex.norm_I, one_mul] using
    norm_add_le (cellDerivativeCLM j u)
      (cellScalarCLM (Complex.I * θ j) (torusHkValueCLM u))

theorem cellBloch_smallShift_source_energy (θ : Fin 2 → ℂ) (hθ : ∀ j, ‖θ j‖ ≤ 1)
    (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) (u : TorusHk 1 ℂ) :
    cellSourceFunctional θ S F u ≤
      (1 / 8) * ∑ j, ‖cellDerivativeCLM j u‖ ^ 2 +
      (Real.pi ^ 2 / 2) * ‖torusHkValueCLM u‖ ^ 2 +
      2 * ‖S‖ ^ 2 + 6 * ∑ j, ‖F j‖ ^ 2 := by
  have hshift (j : Fin 2) :
      ‖cellShiftedDerivativeCLM (fun i => star (θ i)) j u‖ ≤
      ‖cellDerivativeCLM j u‖ + ‖torusHkValueCLM u‖ := by
    apply (cellShiftedDerivativeCLM_norm_le _ j u).trans
    simp only [norm_star]
    have ht := mul_le_mul_of_nonneg_right (hθ j) (norm_nonneg (torusHkValueCLM u))
    linarith
  have hs := (le_abs_self _).trans (cellSourceFunctional_abs_le θ S F u)
  have h0 := mul_le_mul_of_nonneg_left (hshift 0) (norm_nonneg (F 0))
  have h1 := mul_le_mul_of_nonneg_left (hshift 1) (norm_nonneg (F 1))
  have hpi : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.two_le_pi]
  have hp := mul_le_mul_of_nonneg_right hpi (sq_nonneg ‖torusHkValueCLM u‖)
  simp only [Fin.sum_univ_two] at hs ⊢
  nlinarith [sq_nonneg (4 * ‖S‖ - ‖torusHkValueCLM u‖),
    sq_nonneg (8 * ‖F 0‖ - ‖torusHkValueCLM u‖),
    sq_nonneg (8 * ‖F 1‖ - ‖torusHkValueCLM u‖),
    sq_nonneg (4 * ‖F 0‖ - ‖cellDerivativeCLM 0 u‖),
    sq_nonneg (4 * ‖F 1‖ - ‖cellDerivativeCLM 1 u‖)]

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! Continuous-in-time L2 traces of actual uniformly summable cell series. -/

/-- A uniformly summable family of continuous L2 traces has a continuous trace representing the literal pointwise series. -/
theorem cellContinuousL2Series {J : Type*} [Countable J]
    (f : J → ℝ → Vec 2 → ℂ) (u : J → ℝ → ComplexCellL2) (B : J → ℝ≥0∞)
    (huc : ∀ j, Continuous (u j))
    (huf : ∀ j t, (u j t : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] f j t)
    (huB : ∀ j t, ‖u j t‖ₑ ≤ B j) (hB : (∑' j, B j) < ⊤) :
    Continuous (fun t => ∑' j, u j t) ∧
      ∀ t, ((∑' j, u j t : ComplexCellL2) : Vec 2 → ℂ) =ᵐ[
        volume.restrict AVenhance.unitCube] (fun x => ∑' j, f j t x) ∧
        ‖∑' j, u j t‖ₑ ≤ ∑' j, B j := by
  have hfin j : B j < ⊤ := (ENNReal.le_tsum j).trans_lt hB
  have hnorm j t : ‖u j t‖ ≤ (B j).toReal := by
    simpa only [toReal_enorm] using ENNReal.toReal_mono (hfin j).ne (huB j t)
  refine ⟨continuous_tsum huc (ENNReal.summable_toReal hB.ne) hnorm, ?_⟩
  intro t
  have hsum : (∑' j, ‖u j t‖ₑ) < ⊤ :=
    (ENNReal.tsum_le_tsum (fun j => huB j t)).trans_lt hB
  have hall : ∀ᵐ x ∂volume.restrict AVenhance.unitCube, ∀ j, u j t x = f j t x :=
    ae_all_iff.mpr (fun j => huf j t)
  refine ⟨?_, (enorm_tsum_le_tsum_enorm (f := fun j => u j t)).trans
    (ENNReal.tsum_le_tsum (fun j => huB j t))⟩
  filter_upwards [Lp.coeFn_tsum hsum.ne, hall] with x hx hx'
  exact hx.trans (tsum_congr (fun j => hx' j))

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The H¹ Riesz representative of the actual H⁻¹ cell time derivative. -/

/-- Riesz representation of the generator plus scalar/divergence forcing. -/
def cellDualDerivative (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (t : ℝ) (u : TorusHk 1 ℂ) (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    TorusHk 1 ℂ :=
  (InnerProductSpace.toDual ℝ (TorusHk 1 ℂ)).symm
    (cellGeneratorForm C hG V hv hb t u + cellSourceFunctional C.θ S F)

/-- The Riesz derivative has exactly the actual weak form pairing. -/
theorem cellDualDerivative_pairing (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (t : ℝ) (u z : TorusHk 1 ℂ) (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    inner ℝ (cellDualDerivative C hG V hv hb t u S F) z =
      cellGeneratorForm C hG V hv hb t u z + cellSourceFunctional C.θ S F z := by
  exact InnerProductSpace.toDual_symm_apply

/-- Uniform coefficient bound of the H¹ generator, independent of the Galerkin cutoff. -/
theorem cellGeneratorForm_uniform_norm_bound
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (hκ : ∀ t, ‖C.κ t‖ ≤ k) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t u, ‖cellGeneratorForm C hG V hv hb t u‖ ≤ M * ‖u‖ := by
  let D := fun j => ‖cellShiftedDerivativeCLM C.θ j‖
  let T := fun j => ‖cellShiftedDerivativeCLM (fun i => star (C.θ i)) j‖
  let J := ‖torusHkValueCLM (E := ℂ) (K := 1)‖
  let M := (∑ j : Fin 2, ∑ l : Fin 2, 2 * D j * T l) +
    (∑ j : Fin 2, |V| * D j * J) + k * J * J
  have hk := (norm_nonneg (C.κ 0)).trans (hκ 0)
  have hM : 0 ≤ M := by dsimp only [M, D, T, J]; positivity
  refine ⟨M, hM, fun t u => ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hM (norm_nonneg u))
  intro z
  rw [Real.norm_eq_abs]
  apply (cellGeneratorForm_abs_le C hG V k hv hb hκ t u z).trans
  have hd (j : Fin 2) := (cellShiftedDerivativeCLM C.θ j).le_opNorm u
  have ht (j : Fin 2) := (cellShiftedDerivativeCLM (fun i => star (C.θ i)) j).le_opNorm z
  have hju := (torusHkValueCLM (E := ℂ) (K := 1)).le_opNorm u
  have hjz := (torusHkValueCLM (E := ℂ) (K := 1)).le_opNorm z
  calc
    _ ≤ (∑ j : Fin 2, ∑ l : Fin 2, 2 * (D j * ‖u‖) * (T l * ‖z‖)) +
        (∑ j : Fin 2, |V| * (D j * ‖u‖) * (J * ‖z‖)) +
        k * (J * ‖u‖) * (J * ‖z‖) := by
      apply add_le_add
      · apply add_le_add
        · exact Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun l _ => by
            dsimp only [D, T]; gcongr
            · exact hd j
            · exact ht l))
        · exact Finset.sum_le_sum (fun j _ => by
            dsimp only [D, J]; gcongr
            exact hd j)
      · gcongr
    _ = M * ‖u‖ * ‖z‖ := by dsimp only [M]; simp only [Fin.sum_univ_two]; ring

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Representative identities for the real Hilbert cell forms. -/

/-- Real complex inner product written with conjugation on the test. -/
theorem cellComplexInner_eq (a b : ℂ) : inner ℝ a b = (a * star b).re := by
  rw [real_inner_comm, Complex.inner]
  rfl

/-- Scalar multiplication agrees almost everywhere with the literal representative product. -/
theorem cellScalarCLM_ae (c : ℂ) (u : ComplexCellL2) :
    cellScalarCLM c u =ᵐ[volume.restrict AVenhance.unitCube] fun x => c * u x := by
  exact Lp.coeFn_smul c u

/-- Bloch derivative classes have their literal shifted-gradient representatives. -/
theorem cellShiftedDerivativeCLM_ae (θ : Fin 2 → ℂ) (j : Fin 2) (u : TorusHk 1 ℂ) :
    cellShiftedDerivativeCLM θ j u =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => cellDerivativeCLM j u x + Complex.I * θ j * torusHkValueCLM u x := by
  filter_upwards [Lp.coeFn_add (cellDerivativeCLM j u)
      (cellScalarCLM (Complex.I * θ j) (torusHkValueCLM u)),
    cellScalarCLM_ae (Complex.I * θ j) (torusHkValueCLM u)] with x ha hs
  change (cellDerivativeCLM j u + cellScalarCLM (Complex.I * θ j) (torusHkValueCLM u)) x = _
  rw [ha]
  simp only [Pi.add_apply]
  rw [hs]

/-- Scalar coefficient pairings have the literal complex bilinear test representation. -/
theorem cellCoefficient_pairing_eq_integral (c : Homogenization.Vec 2 → ℂ)
    (hc : AEStronglyMeasurable c (volume.restrict AVenhance.unitCube))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x, ‖c x‖ ≤ M) (u z : ComplexCellL2) :
    inner ℝ (cellCoefficientCLM c hc M hM hb u) z =
      ∫ x in AVenhance.unitCube, (c x * u x * star (z x)).re := by
  calc
    inner ℝ (cellCoefficientCLM c hc M hM hb u) z =
        ∫ x in AVenhance.unitCube, inner ℝ (c x * u x) (z x) :=
      measurableCoefficientL2_inner_eq_integral
        (fun x => ContinuousLinearMap.mul ℝ ℂ (c x))
        ((ContinuousLinearMap.mul ℝ ℂ).continuous.comp_aestronglyMeasurable hc)
        M hM (fun x => (scalarMultiply_norm_bound (c x)).trans (hb x)) u z
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => cellComplexInner_eq (c x * u x) (z x))

/-- The literal scalar coefficient/test product is genuinely integrable. -/
theorem cellCoefficient_pairing_integrable (c : Homogenization.Vec 2 → ℂ)
    (hc : AEStronglyMeasurable c (volume.restrict AVenhance.unitCube))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x, ‖c x‖ ≤ M) (u z : ComplexCellL2) :
    Integrable (fun x => (c x * u x * star (z x)).re)
      (volume.restrict AVenhance.unitCube) := by
  apply (L2.integrable_inner (𝕜 := ℝ) (cellCoefficientCLM c hc M hM hb u) z).congr
  filter_upwards [measurableCoefficientL2_ae
    (fun x => ContinuousLinearMap.mul ℝ ℂ (c x))
    ((ContinuousLinearMap.mul ℝ ℂ).continuous.comp_aestronglyMeasurable hc)
    M hM (fun x => (scalarMultiply_norm_bound (c x)).trans (hb x)) u] with x hx
  change cellCoefficientCLM c hc M hM hb u x = c x * u x at hx
  rw [hx, cellComplexInner_eq]

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! A canonical partial inverse of the actual H¹-to-L² embedding, with zero outside its range. -/

/-- The unique H¹ graph element representing an L² value, or zero if that value is outside H¹. -/
def cellH1CanonicalLift (u : ComplexCellL2) : TorusHk 1 ℂ := by
  classical
  exact if h : ∃ z : TorusHk 1 ℂ, torusHkValueCLM z = u then Classical.choose h else 0

/-- The actual periodic H¹ value embedding is injective. -/
theorem cellH1Value_injective : Function.Injective (torusHkValueCLM (E := ℂ) (K := 1)) := by
  intro u w he
  exact TorusHk.ext_value he

/-- The canonical lift recovers every actual H¹ graph element. -/
theorem cellH1CanonicalLift_of_H1 (z : TorusHk 1 ℂ) :
    cellH1CanonicalLift (torusHkValueCLM z) = z := by
  classical
  have h : ∃ w : TorusHk 1 ℂ, torusHkValueCLM w = torusHkValueCLM z := ⟨z, rfl⟩
  unfold cellH1CanonicalLift
  rw [dite_eq_left h]
  exact cellH1Value_injective (Classical.choose_spec h)

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Finite gradient energy of jointly L² raw cell jets. -/

/-- Joint L² membership of the jet coordinates gives joint L² membership of its pointwise gradient. -/
theorem cellRawGradient_memLp (I : Set ℝ) (D : ℝ → RawJet2 1 ℂ)
    (hD : ∀ a, MemLp (fun p : ℝ × Vec 2 => D p.1 a p.2) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    MemLp (fun p : ℝ × Vec 2 => cellGradient (D p.1) p.2) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)) :=
  cellFiniteArray_memLp (fun (p : ℝ × Vec 2) (j : Fin 2) => cellGradComp (D p.1) j p.2)
    (fun j => hD ⟨⟨1, by decide⟩, fun _ => j⟩)

/-- The raw gradient has finite cell energy on every closed subinterval. -/
theorem cellRawGradient_energy_finite {a b : ℝ} (D : ℝ → RawJet2 1 ℂ)
    (hD : ∀ j, MemLp (fun p : ℝ × Vec 2 => D p.1 j p.2) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) (ht : t ∈ Icc a b) :
    (∫⁻ r in Icc s t, cellL2Norm (cellGradient (D r)) ^ 2) < ⊤ := by
  have hf := cellProduct_cellNormSq_finite (Icc a b) (fun r => cellGradient (D r))
    (cellRawGradient_memLp (Icc a b) D hD)
  exact (lintegral_mono_set (Icc_subset_Icc hs.1 ht.2)).trans_lt hf

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Fixed-test moment identities for actual finite cell paths. -/

/-- A retained finite state has the same L² pairing against a test and its Fourier projection. -/
theorem cellGalerkinValue_projected_test_pairing (N : ℕ)
    (y : CellGalerkinSpace (E := ℂ) N) (z : TorusHk 1 ℂ) :
    inner ℝ (cellGalerkinValue N y) (torusHkValueCLM z) =
      inner ℝ (cellGalerkinValue N y) (cellGalerkinValue N (cellGalerkinInitial N z)) := by
  have hy := cellGalerkinValue_fourier_fixed N y
  calc
    _ = inner ℝ (cellVectorFourierProjection N (cellGalerkinValue N y))
        (torusHkValueCLM z) := by rw [hy]
    _ = inner ℝ (cellGalerkinValue N y) (cellVectorFourierProjection N (torusHkValueCLM z)) :=
      cellVectorFourierProjection_inner N _ _
    _ = _ := by
      rw [← cellGalerkinL2Initial_of_H1, cellGalerkinL2Initial_eq_fourier, cellL2FourierState_value]

/-- An actual finite time equation gives its full-test moment primitive, with projected RHS tests. -/
theorem cellGalerkin_full_test_primitive {a b : ℝ} (hab : a ≤ b) (N : ℕ)
    (B : ℝ → TorusHk 1 ℂ →ₗ[ℝ] TorusHk 1 ℂ →ₗ[ℝ] ℝ)
    (q : ℝ → TorusHk 1 ℂ →ₗ[ℝ] ℝ)
    (y dy : ℝ → CellGalerkinSpace (E := ℂ) N)
    (h : StrongVariationalSolution a b (cellGalerkinValue N).toLinearMap
      (fun t => cellGalerkinForm N (B t)) (fun t => cellGalerkinSource N (q t))
      (fun t => cellGalerkinValue N (y t)) (fun t => cellGalerkinValue N (dy t)) y)
    (initial : Lp ℂ 2 (volume.restrict AVenhance.unitCube))
    (hi : cellGalerkinValue N (y a) = cellGalerkinValue N (cellGalerkinL2Initial N initial))
    (z : TorusHk 1 ℂ) :
    ∀ t ∈ Icc a b, inner ℝ (cellGalerkinValue N (y t)) (torusHkValueCLM z) =
      inner ℝ initial (torusHkValueCLM (galerkinProj N z)) +
        ∫ r in a..t, B r (y r).val (galerkinProj N z) + q r (galerkinProj N z) := by
  intro t ht
  have hsub : uIcc a t ⊆ uIcc a b := by
    rw [uIcc_of_le ht.1, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl ht.2
  have he := (h.mono hsub).test_increment (cellGalerkinInitial N z)
  change inner ℝ (cellGalerkinValue N (y t)) (cellGalerkinValue N (cellGalerkinInitial N z)) -
    inner ℝ (cellGalerkinValue N (y a)) (cellGalerkinValue N (cellGalerkinInitial N z)) =
      ∫ r in a..t, B r (y r).val (galerkinProj N z) + q r (galerkinProj N z) at he
  rw [← cellGalerkinValue_projected_test_pairing N (y t) z, hi, cellGalerkinL2Initial_pairing] at he
  change inner ℝ (cellGalerkinValue N (y t)) (torusHkValueCLM z) -
    inner ℝ initial (torusHkValueCLM (galerkinProj N z)) =
      ∫ r in a..t, B r (y r).val (galerkinProj N z) + q r (galerkinProj N z) at he
  linarith

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleEvolution

/-! An L² scalar derivative times a bounded cell trace is a genuine L² field. -/

theorem cellScalarCLM_variable_memLp_L2_top {μ : Measure ℝ}
    (c : ℝ → ℂ) (hc : MemLp c 2 μ) (u : ℝ → ComplexCellL2) (hu : MemLp u ⊤ μ) :
    MemLp (fun t => cellScalarCLM (c t) (u t)) 2 μ := by
  have ha : MemLp (c • u) 2 μ := hc.smul hu
  simpa only [cellScalarCLM_smul, Pi.smul_def'] using ha

end AVRegularity.CycleEvolution
end
end

section
/-! Strong finite time derivatives extracted from the weak Hilbert cell time equation. -/

@[expose] public noncomputable section

open MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE

namespace AVRegularity.CycleEvolution

/-- The projected H⁻¹ derivative is integrable on the finite time interval. -/
theorem cellWeakDualMoment_intervalIntegrable {a b : ℝ} (hab : a ≤ b) (N : ℕ)
    (g : ℝ → TorusHk 1 ℂ) (hg : MemLp g 2 (volume.restrict (Icc a b))) :
    IntervalIntegrable (fun t => cellGalerkinDualMomentCLM N (g t)) volume a b := by
  have hm := (cellGalerkinDualMomentCLM N).comp_memLp' hg
  apply intervalIntegrable_iff.mpr
  rw [uIoc_of_le hab]
  exact (hm.integrable (by norm_num)).mono_measure
    (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)

/-- A fixed-test weak time equation gives the literal finite integral coefficient equation. -/
theorem CellWeakHilbertCurve.projected_integral_solution {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → Lp ℂ 2 (volume.restrict AVenhance.unitCube)}
    {slice g : ℝ → TorusHk 1 ℂ} (h : CellWeakHilbertCurve a b u slice g) (N : ℕ) :
    IsLinearIntegralSolution (fun _ => 0) (fun t => cellGalerkinDualMomentCLM N (g t))
      (cellGalerkinL2Initial N (u a)) a b (fun t => cellGalerkinL2Initial N (u t)) := by
  intro t ht
  change cellGalerkinL2Initial N (u t) = cellGalerkinL2Initial N (u a) +
    ∫ r in a..t, (0 : CellGalerkinSpace (E := ℂ) N →L[ℝ] CellGalerkinSpace (E := ℂ) N)
      (cellGalerkinL2Initial N (u r)) + cellGalerkinDualMomentCLM N (g r)
  simp only [zero_apply, zero_add]
  have hsub : uIcc a t ⊆ uIcc a b := by
    rw [uIcc_of_le ht.1, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl ht.2
  have hint := (cellWeakDualMoment_intervalIntegrable hab N g h.dual).mono_set hsub
  apply cellGalerkinMass_injective N
  ext z
  change inner ℝ (cellGalerkinValue N (cellGalerkinL2Initial N (u t))) (cellGalerkinValue N z) =
    inner ℝ (cellGalerkinValue N (cellGalerkinL2Initial N (u a) +
      ∫ r in a..t, cellGalerkinDualMomentCLM N (g r))) (cellGalerkinValue N z)
  rw [map_add, inner_add_left, cellGalerkinL2Initial_pairing, cellGalerkinL2Initial_pairing]
  have he : inner ℝ (cellGalerkinValue N (∫ r in a..t, cellGalerkinDualMomentCLM N (g r)))
      (cellGalerkinValue N z) = ∫ r in a..t, inner ℝ (g r) z.val := by
    let L := (innerSL ℝ (cellGalerkinValue N z)).comp (cellGalerkinValue N)
    calc
      _ = L (∫ r in a..t, cellGalerkinDualMomentCLM N (g r)) := real_inner_comm _ _
      _ = ∫ r in a..t, L (cellGalerkinDualMomentCLM N (g r)) :=
        (L.intervalIntegral_comp_comm hint).symm
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro r _
        exact (real_inner_comm _ _).trans (cellGalerkinDualMomentCLM_pairing N (g r) z)
  rw [he]
  change inner ℝ (u t) (torusHkValueCLM z.val) =
    inner ℝ (u a) (torusHkValueCLM z.val) + ∫ r in a..t, inner ℝ (g r) z.val
  have hw := h.increment a ⟨le_rfl, hab⟩ t ht ht.1 z.val
  linarith

end AVRegularity.CycleEvolution

namespace AVRegularity.CycleEvolution

/-- Finite Fourier projections have strong time derivatives even when the full derivative is H⁻¹. -/
theorem CellWeakHilbertCurve.projected_strongTime {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → Lp ℂ 2 (volume.restrict AVenhance.unitCube)}
    {slice g : ℝ → TorusHk 1 ℂ} (h : CellWeakHilbertCurve a b u slice g) (N : ℕ) :
    StrongTimeRegularity a b (fun t => cellGalerkinL2Initial N (u t))
      (fun t => cellGalerkinDualMomentCLM N (g t)) := by
  have hy := h.projected_integral_solution hab N
  have he : linearRhs (fun _ => (0 : CellGalerkinSpace (E := ℂ) N →L[ℝ]
      CellGalerkinSpace (E := ℂ) N)) (fun t => cellGalerkinDualMomentCLM N (g t))
      (fun t => cellGalerkinL2Initial N (u t)) =
      (fun t => cellGalerkinDualMomentCLM N (g t)) := by
    funext t
    change 0 + cellGalerkinDualMomentCLM N (g t) = _
    exact zero_add _
  have hint : IntervalIntegrable
      (linearRhs (fun _ => 0) (fun t => cellGalerkinDualMomentCLM N (g t))
        (fun t => cellGalerkinL2Initial N (u t))) volume a b := by
    rw [he]
    exact
      cellWeakDualMoment_intervalIntegrable hab N g h.dual
  refine ⟨hy.absolutelyContinuousOnInterval hab hint, ?_⟩
  apply (ae_restrict_iff' measurableSet_uIcc).mpr
  have hd := hy.ae_hasDerivAt hab hint
  filter_upwards [hd] with t ht
  simpa only [uIcc_of_le hab, he] using ht

end AVRegularity.CycleEvolution
end
end

section
@[expose] public section
namespace AVRegularity.CycleEvolution

/-! A small flux retains all but one thirty-second of the gradient energy. -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem hilbertSmallFlux_young (F p : Fin 2 → H) (B U : ℝ)
    (hF : ∀ j, ‖F j‖ ≤ B * U) :
    -(∑ j : Fin 2, inner ℝ (F j) (p j)) ≤
      (1 / 32) * ∑ j, ‖p j‖ ^ 2 + 16 * B ^ 2 * U ^ 2 := by
  have h (j : Fin 2) : -inner ℝ (F j) (p j) ≤ B * U * ‖p j‖ := by
    exact ((neg_le_abs _).trans (abs_real_inner_le_norm _ _)).trans
      (mul_le_mul_of_nonneg_right (hF j) (norm_nonneg _))
  have h0 := h 0
  have h1 := h 1
  simp only [Fin.sum_univ_two]
  nlinarith [sq_nonneg (‖p 0‖ - 16 * B * U),
    sq_nonneg (‖p 1‖ - 16 * B * U)]

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Operator norm bounds for actual scalar/flux forcing and the H⁻¹ cell derivative. -/

/-- The source functional has its direct H⁻¹ bound in terms of the L² source norms. -/
theorem cellSourceFunctional_norm_le (θ : Fin 2 → ℂ)
    (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    ‖cellSourceFunctional θ S F‖ ≤
      ‖torusHkValueCLM (E := ℂ) (K := 1)‖ * ‖S‖ +
        ∑ j, ‖cellShiftedDerivativeCLM (fun i => star (θ i)) j‖ * ‖F j‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  rw [Real.norm_eq_abs]
  apply (cellSourceFunctional_abs_le θ S F z).trans
  calc
    _ ≤ ‖S‖ * (‖torusHkValueCLM (E := ℂ) (K := 1)‖ * ‖z‖) +
        ∑ j, ‖F j‖ * (‖cellShiftedDerivativeCLM (fun i => star (θ i)) j‖ * ‖z‖) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (torusHkValueCLM.le_opNorm z) (norm_nonneg _)
      · exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left
          ((cellShiftedDerivativeCLM (fun i => star (θ i)) j).le_opNorm z) (norm_nonneg _))
    _ = _ := by simp only [Fin.sum_univ_two]; ring

/-- The actual dual derivative is bounded by the form functional and source budgets. -/
theorem cellDualDerivative_norm_le
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (t : ℝ) (u : TorusHk 1 ℂ) (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    ‖cellDualDerivative C hG V hv hb t u S F‖ ≤
      ‖cellGeneratorForm C hG V hv hb t u‖ +
      ‖torusHkValueCLM (E := ℂ) (K := 1)‖ * ‖S‖ +
        ∑ j, ‖cellShiftedDerivativeCLM (fun i => star (C.θ i)) j‖ * ‖F j‖ := by
  unfold cellDualDerivative
  rw [LinearIsometryEquiv.norm_map]
  exact (norm_add_le _ _).trans ((add_le_add le_rfl (cellSourceFunctional_norm_le C.θ S F)).trans_eq
    (add_assoc _ _ _).symm)

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped BigOperators
namespace AVRegularity.CycleEvolution

/-! Additivity of the complete actual generator and source Riesz derivative. -/

theorem cellDualDerivative_add (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (t : ℝ) (u v : TorusHk 1 ℂ) (S T : ComplexCellL2) (F H : Fin 2 → ComplexCellL2) :
    cellDualDerivative C hG V hv hb t (u + v) (S + T) (F + H) =
      cellDualDerivative C hG V hv hb t u S F + cellDualDerivative C hG V hv hb t v T H := by
  apply ext_inner_right ℝ
  intro z
  rw [inner_add_left, cellDualDerivative_pairing, cellDualDerivative_pairing,
    cellDualDerivative_pairing]
  simp only [map_add, add_apply, cellSourceFunctional, ContinuousLinearMap.comp_apply,
    sub_apply, innerSL_apply_apply, Pi.add_apply, Fin.sum_univ_two]
  ring

end AVRegularity.CycleEvolution
end
end

section
/-! Time measurability of the actual cell weak form at fixed trial and test functions. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin

namespace AVRegularity.CycleEvolution

/-- Joint scalar measurability suffices for every fixed L² multiplier pairing. -/
theorem cellCoefficient_pairing_stronglyMeasurable
    (c : ℝ → Vec 2 → ℂ) (hc : Measurable (Function.uncurry c))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ t x, ‖c t x‖ ≤ M)
    (u z : ComplexCellL2) :
    StronglyMeasurable (fun t => inner ℝ
      (cellCoefficientCLM (c t)
        ((hc.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
        M hM (hb t) u) z) := by
  have hcoef : Measurable (fun p : ℝ × Vec 2 => ContinuousLinearMap.mul ℝ ℂ (c p.1 p.2)) :=
    (ContinuousLinearMap.mul ℝ ℂ).continuous.measurable.comp hc
  have hm := coefficientPairing_stronglyMeasurable
    (fun t x => ContinuousLinearMap.mul ℝ ℂ (c t x)) hcoef u z
  convert hm using 1
  funext t
  exact measurableCoefficientL2_inner_eq_integral
    (fun x => ContinuousLinearMap.mul ℝ ℂ (c t x))
    ((ContinuousLinearMap.mul ℝ ℂ).continuous.comp_aestronglyMeasurable
      ((hc.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable))
    M hM (fun x => (scalarMultiply_norm_bound (c t x)).trans (hb t x)) u z

/-- Every metric-entry weak pairing is strongly measurable in time. -/
theorem cellMetric_pairing_stronglyMeasurable
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    (j k : Fin 2) (u z : ComplexCellL2) :
    StronglyMeasurable (fun t => inner ℝ (cellMetricEntryCLM hG t j k u) z) := by
  exact cellCoefficient_pairing_stronglyMeasurable
    (fun t x => (G t x j k : ℂ))
    (Complex.continuous_ofReal.measurable.comp (cellMetric_entry_measurable hG j k))
    2 (by norm_num) (fun t x => by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using cellMetric_entry_bound hG t x j k)
    u z

end AVRegularity.CycleEvolution

namespace AVRegularity.CycleEvolution

/-- The diffusion weak form has measurable time coefficients on every fixed pair. -/
theorem cellDiffusionForm_pairing_stronglyMeasurable
    (C : CellCoefficients) (hG : IsCellMetric C.G) (u z : TorusHk 1 ℂ) :
    StronglyMeasurable (fun t => cellDiffusionForm C hG t u z) := by
  simp only [cellDiffusionForm, Fin.sum_univ_two, neg_apply,
    add_apply, AVRegularity.CoupledEnergy.Variational.pullbackInnerCLM_apply,
    ContinuousLinearMap.comp_apply]
  exact (((cellMetric_pairing_stronglyMeasurable hG 0 0 _ _).add
    (cellMetric_pairing_stronglyMeasurable hG 0 1 _ _)).add
    ((cellMetric_pairing_stronglyMeasurable hG 1 0 _ _).add
      (cellMetric_pairing_stronglyMeasurable hG 1 1 _ _))).neg

/-- Every drift-entry weak pairing is strongly measurable in time. -/
theorem cellDrift_pairing_stronglyMeasurable
    (C : CellCoefficients) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (j : Fin 2) (u z : ComplexCellL2) :
    StronglyMeasurable (fun t => inner ℝ (cellDriftEntryCLM C V hv hb t j u) z) := by
  exact cellCoefficient_pairing_stronglyMeasurable
    (fun t x => (C.v t x j : ℂ))
    (Complex.continuous_ofReal.measurable.comp ((measurable_pi_apply j).comp hv))
    |V| (abs_nonneg V) (fun t x => by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using cellDrift_entry_bound hb t x j)
    u z

/-- The actual generator has measurable time coefficients on every fixed H¹ pair. -/
theorem cellGeneratorForm_pairing_stronglyMeasurable
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (hκ : Measurable C.κ) (u z : TorusHk 1 ℂ) :
    StronglyMeasurable (fun t => cellGeneratorForm C hG V hv hb t u z) := by
  have hp : Continuous (fun c : ℂ => inner ℝ
      (cellScalarCLM c (torusHkValueCLM u)) (torusHkValueCLM z)) :=
    ((ContinuousLinearMap.lsmul ℝ ℂ).continuous.clm_apply continuous_const).inner continuous_const
  have hpot := (hp.measurable.comp hκ).stronglyMeasurable
  simp only [cellGeneratorForm, Fin.sum_univ_two, add_apply,
    sub_apply,
    AVRegularity.CoupledEnergy.Variational.pullbackInnerCLM_apply,
    ContinuousLinearMap.comp_apply]
  exact ((cellDiffusionForm_pairing_stronglyMeasurable C hG u z).sub
    ((cellDrift_pairing_stronglyMeasurable C V hv hb 0 _ _).add
      (cellDrift_pairing_stronglyMeasurable C V hv hb 1 _ _))).add hpot

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Actual scalar and flux forcing in the finite cell mass systems. -/

/-- Scalar and flux sources as a time-dependent H¹ functional. -/
def cellRawSourceFunctional (θ : Fin 2 → ℂ) (src : ℝ → Vec 2 → ℂ)
    (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) (t : ℝ) :
    TorusHk 1 ℂ →ₗ[ℝ] ℝ :=
  (cellSourceFunctional θ (cellSourceSlice src t)
    (fun j => cellSourceSlice (fun s x => F s x j) t)).toLinearMap

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleEvolution

/-! Literal representatives of cell coefficient multiplication operators. -/

/-- Bounded measurable complex multiplication has the stated pointwise representative. -/
theorem cellCoefficientCLM_ae (c : Vec 2 → ℂ)
    (hc : AEStronglyMeasurable c (volume.restrict AVenhance.unitCube))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x, ‖c x‖ ≤ M) (u : ComplexCellL2) :
    cellCoefficientCLM c hc M hM hb u =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => c x * u x := by
  exact measurableCoefficientL2_ae
    (fun x => ContinuousLinearMap.mul ℝ ℂ (c x))
    ((ContinuousLinearMap.mul ℝ ℂ).continuous.comp_aestronglyMeasurable hc)
    M hM (fun x => (scalarMultiply_norm_bound (c x)).trans (hb x)) u

/-- Metric multiplication has the literal measurable metric entry representative. -/
theorem cellMetricEntryCLM_ae {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : IsCellMetric G) (t : ℝ) (j k : Fin 2) (u : ComplexCellL2) :
    cellMetricEntryCLM hG t j k u =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => (G t x j k : ℂ) * u x := by
  unfold cellMetricEntryCLM
  exact cellCoefficientCLM_ae _ _ _ _ _ u

/-- Drift multiplication has the literal measurable drift entry representative. -/
theorem cellDriftEntryCLM_ae (C : CellCoefficients) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (t : ℝ) (j : Fin 2) (u : ComplexCellL2) :
    cellDriftEntryCLM C V hv hb t j u =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => (C.v t x j : ℂ) * u x := by
  unfold cellDriftEntryCLM
  exact cellCoefficientCLM_ae _ _ _ _ _ u

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! Literal integrable spatial pairings of all terms in the complex cell form. -/

/-- The metric weak entry equals its literal bilinear complex integral. -/
theorem cellMetric_pairing_eq_integral
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    (t : ℝ) (j k : Fin 2) (u z : ComplexCellL2) :
    inner ℝ (cellMetricEntryCLM hG t j k u) z =
      ∫ x in AVenhance.unitCube, ((G t x j k : ℂ) * u x * star (z x)).re := by
  unfold cellMetricEntryCLM
  exact cellCoefficient_pairing_eq_integral _ _ _ _ _ _ _

/-- The metric/test product is integrable. -/
theorem cellMetric_pairing_integrable
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} (hG : IsCellMetric G)
    (t : ℝ) (j k : Fin 2) (u z : ComplexCellL2) :
    Integrable (fun x => ((G t x j k : ℂ) * u x * star (z x)).re)
      (volume.restrict AVenhance.unitCube) := by
  exact cellCoefficient_pairing_integrable (fun x => (G t x j k : ℂ))
    ((Complex.continuous_ofReal.measurable.comp
      ((cellMetric_entry_measurable hG j k).comp
        (measurable_const.prodMk measurable_id))).aestronglyMeasurable)
    2 (by norm_num) (fun x => by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using cellMetric_entry_bound hG t x j k) u z

/-- The drift weak entry equals its literal bilinear complex integral. -/
theorem cellDrift_pairing_eq_integral (C : CellCoefficients) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (j : Fin 2) (u z : ComplexCellL2) :
    inner ℝ (cellDriftEntryCLM C V hv hb t j u) z =
      ∫ x in AVenhance.unitCube, ((C.v t x j : ℂ) * u x * star (z x)).re := by
  unfold cellDriftEntryCLM
  exact cellCoefficient_pairing_eq_integral _ _ _ _ _ _ _

/-- The drift/test product is integrable. -/
theorem cellDrift_pairing_integrable (C : CellCoefficients) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (j : Fin 2) (u z : ComplexCellL2) :
    Integrable (fun x => ((C.v t x j : ℂ) * u x * star (z x)).re)
      (volume.restrict AVenhance.unitCube) := by
  exact cellCoefficient_pairing_integrable (fun x => (C.v t x j : ℂ))
    ((Complex.continuous_ofReal.measurable.comp
      (((measurable_pi_apply j).comp hv).comp
        (measurable_const.prodMk measurable_id))).aestronglyMeasurable)
    |V| (abs_nonneg V) (fun x => by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using cellDrift_entry_bound hb t x j) u z

/-- Constant potential multiplication has the literal integral pairing. -/
theorem cellScalar_pairing_eq_integral (c : ℂ) (u z : ComplexCellL2) :
    inner ℝ (cellScalarCLM c u) z = ∫ x in AVenhance.unitCube, (c * u x * star (z x)).re := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [cellScalarCLM_ae c u] with x hx
  rw [hx, cellComplexInner_eq]

/-- Constant potential/test products are integrable. -/
theorem cellScalar_pairing_integrable (c : ℂ) (u z : ComplexCellL2) :
    Integrable (fun x => (c * u x * star (z x)).re) (volume.restrict AVenhance.unitCube) := by
  apply (L2.integrable_inner (𝕜 := ℝ) (cellScalarCLM c u) z).congr
  filter_upwards [cellScalarCLM_ae c u] with x hx
  rw [hx, cellComplexInner_eq]

/-- Scalar/flux class pairings have their literal complex integral. -/
theorem cellPlain_pairing_eq_integral (u z : ComplexCellL2) :
    inner ℝ u z = ∫ x in AVenhance.unitCube, (u x * star (z x)).re := by
  rw [L2.inner_def]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun x => cellComplexInner_eq (u x) (z x)))

/-- Scalar/flux class pairings are integrable. -/
theorem cellPlain_pairing_integrable (u z : ComplexCellL2) :
    Integrable (fun x => (u x * star (z x)).re) (volume.restrict AVenhance.unitCube) := by
  apply (L2.integrable_inner (𝕜 := ℝ) u z).congr
  exact Filter.Eventually.of_forall (fun x => cellComplexInner_eq (u x) (z x))

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleEvolution

/-! Complex bilinear pairings recovered from the real Hilbert cell carrier. -/

/-- The complex test product of two cell L² classes is integrable. -/
theorem cellComplex_pairing_integrable (u z : ComplexCellL2) :
    Integrable (fun x => u x * star (z x)) (volume.restrict AVenhance.unitCube) := by
  have hi := memLp_one_iff_integrable.mp
    ((Lp.memLp u).mul (Lp.memLp z).star : MemLp _ 1 _)
  have he : ((u : Homogenization.Vec 2 → ℂ) * star (z : Homogenization.Vec 2 → ℂ)) =
      (fun x => u x * star (z x)) := by funext x; rfl
  rw [he] at hi
  exact hi

/-- Sesquilinear cell pairing, with conjugation on the test. -/
def cellComplexPair (u z : ComplexCellL2) : ℂ :=
  ∫ x in AVenhance.unitCube, u x * star (z x)

/-- Its real part is exactly the real Hilbert inner product. -/
theorem cellComplexPair_re (u z : ComplexCellL2) :
    (cellComplexPair u z).re = inner ℝ u z := by
  have he := Complex.reCLM.integral_comp_comm (cellComplex_pairing_integrable u z)
  change (∫ x in AVenhance.unitCube, (u x * star (z x)).re) = (cellComplexPair u z).re at he
  rw [← he]
  exact (cellPlain_pairing_eq_integral u z).symm

/-- Multiplication of the test by i extracts the imaginary part. -/
theorem cellComplexPair_im (u z : ComplexCellL2) :
    (cellComplexPair u z).im = inner ℝ u (cellScalarCLM Complex.I z) := by
  have he := Complex.imCLM.integral_comp_comm (cellComplex_pairing_integrable u z)
  change (∫ x in AVenhance.unitCube, (u x * star (z x)).im) = (cellComplexPair u z).im at he
  rw [← he, cellPlain_pairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [cellScalarCLM_ae Complex.I z] with x hx
  rw [hx]
  simp [Complex.mul_re, Complex.mul_im]
  ring

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleEvolution

/-! A spatially constant metric acts by its literal scalar entries on cell L². -/

theorem cellConstantMetricEntryCLM {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : IsCellMetric (fun t _ => G t)) (t : ℝ) (j k : Fin 2) (u : ComplexCellL2) :
    cellMetricEntryCLM hG t j k u = cellScalarCLM (G t j k : ℂ) u := by
  apply Lp.ext
  exact (cellMetricEntryCLM_ae hG t j k u).trans (cellScalarCLM_ae (G t j k : ℂ) u).symm

/-! Exact scalar algebra converting the mean-free graph forcing into the normalized Bloch equation. -/

section
local instance cellGraphSourceAlgebraProbCube : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using cellCube_volume_one⟩

theorem cellGraphSource_scalar_identity (b ρ : Vec 2 → ℂ)
    (hb : MemLp b 2 (volume.restrict AVenhance.unitCube))
    (hρ : MemLp ρ 2 (volume.restrict AVenhance.unitCube)) (hm : cellMean b = 0) (x : Vec 2) :
    cellQ0 (fun y => -Complex.I * (b y * (1 + ρ y))) x +
      Complex.I * ρ x * cellMean (fun y => b y * ρ y) =
        -Complex.I * b x * (1 + ρ x) +
          Complex.I * cellMean (fun y => b y * ρ y) * (1 + ρ x) := by
  have hp : Integrable (fun y => b y * ρ y) (volume.restrict AVenhance.unitCube) :=
    memLp_one_iff_integrable.mp (hb.mul hρ : MemLp _ 1 _)
  have he : (fun y => b y * (1 + ρ y)) = (fun y => b y + b y * ρ y) := by
    funext y
    ring
  have hmean : cellMean (fun y => b y * (1 + ρ y)) = cellMean (fun y => b y * ρ y) := by
    unfold cellMean
    rw [he, integral_add (hb.integrable (by norm_num)) hp]
    change cellMean b + cellMean (fun y => b y * ρ y) = _
    rw [hm, zero_add]
    rfl
  have hscalar : cellMean (fun y => -Complex.I * (b y * (1 + ρ y))) =
      -Complex.I * cellMean (fun y => b y * ρ y) := by
    unfold cellMean
    rw [integral_const_mul]
    change -Complex.I * cellMean (fun y => b y * (1 + ρ y)) = _
    rw [hmean]
    rfl
  unfold cellQ0
  rw [hscalar]
  ring
end

/-! Exact literal L2 norms of cell constants. -/

/-- Unit cell volume makes the literal L2 norm of a constant exactly its extended norm. -/
theorem cellL2Norm_const {E : Type*} [NormedAddCommGroup E] (c : E) :
    cellL2Norm (fun _ : Vec 2 => c) = ‖c‖ₑ := by
  change eLpNorm _ 2 _ = _
  rw [eLpNorm_const' c (by norm_num) (by simp), Measure.restrict_apply_univ,
    cellCube_volume_one]
  simp

end AVRegularity.CycleEvolution
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleEvolution

/-! The complex sesquilinear cell form underlying its real Hilbert equation. -/

/-- Literal complex generator, conjugate linear in its test. -/
def cellComplexGenerator (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (t : ℝ) (u z : TorusHk 1 ℂ) : ℂ :=
  -(∑ j : Fin 2, ∑ k : Fin 2, cellComplexPair
    (cellMetricEntryCLM hG t j k (cellShiftedDerivativeCLM C.θ j u))
    (cellShiftedDerivativeCLM (fun i => star (C.θ i)) k z)) -
  (∑ j : Fin 2, cellComplexPair
    (cellDriftEntryCLM C V hv hb t j (cellShiftedDerivativeCLM C.θ j u)) (torusHkValueCLM z)) +
  cellComplexPair (cellScalarCLM (C.κ t) (torusHkValueCLM u)) (torusHkValueCLM z)

/-- Literal complex scalar and divergence forcing. -/
def cellComplexSource (θ : Fin 2 → ℂ) (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2)
    (z : TorusHk 1 ℂ) : ℂ :=
  cellComplexPair S (torusHkValueCLM z) - ∑ j : Fin 2,
    cellComplexPair (F j) (cellShiftedDerivativeCLM (fun i => star (θ i)) j z)

/-- The complex generator has exactly the existing real Hilbert form as real part. -/
theorem cellComplexGenerator_re (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (u z : TorusHk 1 ℂ) :
    (cellComplexGenerator C hG V hv hb t u z).re = cellGeneratorForm C hG V hv hb t u z := by
  simp only [cellComplexGenerator, cellGeneratorForm, cellDiffusionForm, Fin.sum_univ_two,
    Complex.add_re, Complex.sub_re, Complex.neg_re, cellComplexPair_re,
    add_apply, sub_apply, neg_apply, pullbackInnerCLM_apply, ContinuousLinearMap.comp_apply]

/-- The complex forcing has exactly the existing real source functional as real part. -/
theorem cellComplexSource_re (θ : Fin 2 → ℂ) (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2)
    (z : TorusHk 1 ℂ) : (cellComplexSource θ S F z).re = cellSourceFunctional θ S F z := by
  simp only [cellComplexSource, cellSourceFunctional, Fin.sum_univ_two,
    Complex.add_re, Complex.sub_re, cellComplexPair_re, sub_apply, add_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply]

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleEvolution

/-! Real drift multipliers are self-adjoint and commute with complex scalars. -/

theorem cellDriftEntryCLM_complex_adjoint (C : CellCoefficients) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (j : Fin 2)
    (u z : ComplexCellL2) :
    cellComplexPair (cellDriftEntryCLM C V hv hb t j u) z =
      cellComplexPair u (cellDriftEntryCLM C V hv hb t j z) := by
  unfold cellComplexPair
  apply integral_congr_ae
  filter_upwards [cellDriftEntryCLM_ae C V hv hb t j u,
    cellDriftEntryCLM_ae C V hv hb t j z] with x hu hz
  rw [hu, hz, star_mul]
  simp only [Complex.star_def, Complex.conj_ofReal]
  ring

theorem cellDriftEntryCLM_scalar (C : CellCoefficients) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (j : Fin 2)
    (c : ℂ) (u : ComplexCellL2) :
    cellDriftEntryCLM C V hv hb t j (cellScalarCLM c u) =
      cellScalarCLM c (cellDriftEntryCLM C V hv hb t j u) := by
  apply Lp.ext
  filter_upwards [cellDriftEntryCLM_ae C V hv hb t j (cellScalarCLM c u),
    cellScalarCLM_ae c u, cellScalarCLM_ae c (cellDriftEntryCLM C V hv hb t j u),
    cellDriftEntryCLM_ae C V hv hb t j u] with x hdu hu hcu hd
  rw [hdu, hu, hcu, hd]
  ring

end AVRegularity.CycleEvolution
end
end
