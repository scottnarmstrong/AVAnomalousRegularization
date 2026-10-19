-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.CellJetSlices
public import AVRegularity.CycleEvolution.FibreReverseValueCoefficients
import AVRegularity.CycleEvolution.CellDriftSmoothEnergy
public import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Star.Real

section
/-! Real Hilbert forms for the complex Bloch cell equation with measurable coefficients. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational AVRegularity.CoupledEnergy.Galerkin

namespace AVRegularity.CycleEvolution

abbrev ComplexCellL2 := Lp ℂ 2 (volume.restrict AVenhance.unitCube)

/-- The weak derivative coordinate of a periodic H¹ class. -/
def cellDerivativeCLM (j : Fin 2) : TorusHk 1 ℂ →L[ℝ] ComplexCellL2 :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : JetIndex2 1 => ComplexCellL2)
    ⟨⟨1, by decide⟩, fun _ => j⟩).comp
    (torusHkGraph (E := ℂ) 1).toSubmodule.subtypeL

/-- Complex scalar multiplication on cell L², regarded as a real operator. -/
def cellScalarCLM (c : ℂ) : ComplexCellL2 →L[ℝ] ComplexCellL2 :=
  ContinuousLinearMap.lsmul ℝ ℂ c

/-- The Bloch derivative component ∂ⱼ + iθⱼ. -/
def cellShiftedDerivativeCLM (θ : Fin 2 → ℂ) (j : Fin 2) :
    TorusHk 1 ℂ →L[ℝ] ComplexCellL2 :=
  cellDerivativeCLM j + (cellScalarCLM (Complex.I * θ j)).comp torusHkValueCLM

/-- Scalar multiplication has its literal complex modulus bound. -/
theorem scalarMultiply_norm_bound (c : ℂ) :
    ‖ContinuousLinearMap.mul ℝ ℂ c‖ ≤ ‖c‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg c)
  intro x
  exact norm_mul_le c x

/-- Multiplication by a bounded measurable scalar coefficient on cell L². -/
def cellCoefficientCLM (c : Vec 2 → ℂ)
    (hc : AEStronglyMeasurable c (volume.restrict AVenhance.unitCube))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x, ‖c x‖ ≤ M) :
    ComplexCellL2 →L[ℝ] ComplexCellL2 :=
  measurableCoefficientL2CLM (fun x => ContinuousLinearMap.mul ℝ ℂ (c x))
    ((ContinuousLinearMap.mul ℝ ℂ).continuous.comp_aestronglyMeasurable hc)
    M hM (fun x => (scalarMultiply_norm_bound (c x)).trans (hb x))

/-- Measurable metric entry multiplication. -/
def cellMetricEntryCLM {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : IsCellMetric G) (t : ℝ) (j k : Fin 2) :
    ComplexCellL2 →L[ℝ] ComplexCellL2 :=
  cellCoefficientCLM (fun x => (G t x j k : ℂ))
    (((Complex.continuous_ofReal.measurable.comp
      ((cellMetric_entry_measurable hG j k).comp
        (measurable_const.prodMk measurable_id))).aestronglyMeasurable))
    2 (by norm_num) (fun x => by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using cellMetric_entry_bound hG t x j k)

/-- Diffusion form for complex θ: the test shift is conjugated in the real Hilbert pairing. -/
def cellDiffusionForm (C : CellCoefficients) (hG : IsCellMetric C.G) (t : ℝ) :
    TorusHk 1 ℂ →L[ℝ] TorusHk 1 ℂ →L[ℝ] ℝ :=
  -∑ j : Fin 2, ∑ k : Fin 2,
    pullbackInnerCLM
      ((cellMetricEntryCLM hG t j k).comp (cellShiftedDerivativeCLM C.θ j))
      (cellShiftedDerivativeCLM (fun i => star (C.θ i)) k)

end AVRegularity.CycleEvolution

namespace AVRegularity.CycleEvolution

/-- Measurable drift entry multiplication. -/
def cellDriftEntryCLM (C : CellCoefficients) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t z, ∑ i, C.v t z i ^ 2 ≤ V ^ 2) (t : ℝ) (j : Fin 2) :
    ComplexCellL2 →L[ℝ] ComplexCellL2 :=
  cellCoefficientCLM (fun x => (C.v t x j : ℂ))
    ((Complex.continuous_ofReal.measurable.comp
      (((measurable_pi_apply j).comp hv).comp
        (measurable_const.prodMk measurable_id))).aestronglyMeasurable)
    |V| (abs_nonneg V) (fun x => by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using cellDrift_entry_bound hb t x j)

/-- The real Hilbert generator form of the cell equation. -/
def cellGeneratorForm (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t z, ∑ i, C.v t z i ^ 2 ≤ V ^ 2) (t : ℝ) :
    TorusHk 1 ℂ →L[ℝ] TorusHk 1 ℂ →L[ℝ] ℝ :=
  cellDiffusionForm C hG t
    - ∑ j : Fin 2, pullbackInnerCLM
      ((cellDriftEntryCLM C V hv hb t j).comp (cellShiftedDerivativeCLM C.θ j))
      torusHkValueCLM
    + pullbackInnerCLM ((cellScalarCLM (C.κ t)).comp torusHkValueCLM) torusHkValueCLM

/-- The scalar and divergence source functional on periodic H¹. -/
def cellSourceFunctional (θ : Fin 2 → ℂ) (src : ComplexCellL2)
    (F : Fin 2 → ComplexCellL2) : TorusHk 1 ℂ →L[ℝ] ℝ :=
  (innerSL ℝ src).comp torusHkValueCLM
    - ∑ j : Fin 2, (innerSL ℝ (F j)).comp
      (cellShiftedDerivativeCLM (fun i => star (θ i)) j)

end AVRegularity.CycleEvolution

namespace AVRegularity.CycleEvolution

/-- The same generator form as an algebraic bilinear map for finite mass inversion. -/
def cellGeneratorB (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t z, ∑ i, C.v t z i ^ 2 ≤ V ^ 2) (t : ℝ) :
    TorusHk 1 ℂ →ₗ[ℝ] TorusHk 1 ℂ →ₗ[ℝ] ℝ :=
  (ContinuousLinearMap.coeLM ℝ).comp (cellGeneratorForm C hG V hv hb t).toLinearMap

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! An actual periodic raw jet and its total Sobolev slice have the same value representative. -/

theorem cellH1Slice_value_ae (D : ℝ → RawJet2 1 ℂ) (t : ℝ)
    (ht : HasPeriodicOrderedWeakJet (D t)) :
    torusHkValueCLM (cellH1Slice D t) =ᵐ[volume.restrict AVenhance.unitCube]
      cellValue D t := by
  rw [cellH1Slice_eq_toHk D t ht]
  exact torusJetToL2_ae (D t) ht.2.1 (valueIndex2 1)

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The actual reversed coefficient series is exactly the graph at opposite frequency and reversed time. -/

theorem fibreMonomial_neg (ξ : Fin 2 → ℂ) (p : ℕ × ℕ) :
    fibreMonomial (fun j => -ξ j) p = (-1 : ℂ) ^ (p.1 + p.2) * fibreMonomial ξ p := by
  change (-ξ 0) ^ p.1 * (-ξ 1) ^ p.2 =
    (-1 : ℂ) ^ (p.1 + p.2) * (ξ 0 ^ p.1 * ξ 1 ^ p.2)
  rw [show -ξ 0 = (-1 : ℂ) * ξ 0 from (neg_one_mul _).symm,
    show -ξ 1 = (-1 : ℂ) * ξ 1 from (neg_one_mul _).symm,
    mul_pow, mul_pow, pow_add]
  ring

theorem fibreReverseValueCoefficients_series (r : ℕ × ℕ → ℝ → RawJet2 1 ℂ)
    (ξ : Fin 2 → ℂ) (t : ℝ) (x : Vec 2) :
    fibreSeriesFun (fibreReverseValueCoefficients r) ξ t x =
      cellValue (fibreSeriesJet r (fun j => -ξ j)) (-t) x := by
  change (∑' p, fibreMonomial ξ p * ((-1 : ℂ) ^ (p.1 + p.2) * cellValue (r p) (-t) x)) =
    ∑' p, fibreMonomial (fun j => -ξ j) p * cellValue (r p) (-t) x
  apply tsum_congr
  intro p
  rw [fibreMonomial_neg]
  ring

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Literal scalar and divergence sources for a complex Bloch-frequency perturbation. -/

def cellBlochPerturbationFlux (C : CellCoefficients) (hG : IsCellMetric C.G)
    (δ : Fin 2 → ℂ) (t : ℝ) (u : TorusHk 1 ℂ) (k : Fin 2) : ComplexCellL2 :=
  ∑ j : Fin 2, cellMetricEntryCLM hG t j k
    (cellScalarCLM (Complex.I * δ j) (torusHkValueCLM u))

def cellBlochPerturbationScalar (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (δ : Fin 2 → ℂ) (q : ℝ → ℂ) (t : ℝ) (u : TorusHk 1 ℂ) : ComplexCellL2 :=
  (∑ k : Fin 2, cellScalarCLM (Complex.I * δ k)
    (∑ j : Fin 2, cellMetricEntryCLM hG t j k (cellShiftedDerivativeCLM (C.θ + δ) j u))) -
  (∑ j : Fin 2, cellDriftEntryCLM C V hv hb t j
    (cellScalarCLM (Complex.I * δ j) (torusHkValueCLM u))) +
  cellScalarCLM (q t) (torusHkValueCLM u)

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleEvolution

/-! A weighted Taylor majorant gives a two-power gain in every higher-order series increment. -/

theorem fibreScalarSeries_high_increment_bound (a : ℕ × ℕ → ℝ → ℂ) (R K M : ℝ)
    (hR : 0 < R) (hK : 0 ≤ K) (hM : 0 ≤ M) (hMR : M ≤ R / 2)
    (hz : ∀ p, p.1 + p.2 < 3 → ∀ t, a p t = 0)
    (ha : (∑' p, fibreCoefficientWeight (ENNReal.ofReal R) p * ⨆ s, ‖a p s‖ₑ) ≤ ENNReal.ofReal K)
    (ξ ζ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ M) (hζ : fibreNorm ζ ≤ M) (t : ℝ) :
    ‖fibreSeriesC a ξ t - fibreSeriesC a ζ t‖ ≤
      (3 * K * M ^ 2 / R ^ 3) * fibreNorm (fun j => ξ j - ζ j) := by
  let B := (3 * M ^ 2 / R ^ 3) * fibreNorm (fun j => ξ j - ζ j)
  have hB : 0 ≤ B := mul_nonneg
    (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg M)) (pow_nonneg hR.le 3))
    (fibreNorm_nonneg _)
  have hξR : fibreNorm ξ ≤ R := hξ.trans (by linarith)
  have hζR : fibreNorm ζ ≤ R := hζ.trans (by linarith)
  have hfinite := ha.trans_lt (ENNReal.ofReal_lt_top : ENNReal.ofReal K < ⊤)
  have hsξ := (fibreScalarSeries_summable_norm a R hfinite ξ hξR t).of_norm
  have hsζ := (fibreScalarSeries_summable_norm a R hfinite ζ hζR t).of_norm
  have he : fibreSeriesC a ξ t - fibreSeriesC a ζ t =
      ∑' p, (fibreMonomial ξ p - fibreMonomial ζ p) * a p t := by
    rw [fibreSeriesC, fibreSeriesC, ← hsξ.tsum_sub hsζ]
    apply tsum_congr
    intro p
    ring
  have hp (p : ℕ × ℕ) : ‖(fibreMonomial ξ p - fibreMonomial ζ p) * a p t‖ₑ ≤
      ENNReal.ofReal B * (fibreCoefficientWeight (ENNReal.ofReal R) p * ⨆ s, ‖a p s‖ₑ) := by
    by_cases hlow : p.1 + p.2 < 3
    · simp only [hz p hlow t, mul_zero, enorm_zero]
      exact bot_le
    · have hm := ENNReal.ofReal_le_ofReal
        (fibreMonomial_high_increment_bound ξ ζ R M hR hM hMR hξ hζ p (by omega))
      have hweight : ENNReal.ofReal ((3 * M ^ 2 / R ^ 3) * R ^ (p.1 + p.2) *
          fibreNorm (fun j => ξ j - ζ j)) =
          ENNReal.ofReal B * fibreCoefficientWeight (ENNReal.ofReal R) p := by
        have hr : (3 * M ^ 2 / R ^ 3) * R ^ (p.1 + p.2) * fibreNorm (fun j => ξ j - ζ j) =
            B * R ^ (p.1 + p.2) := by dsimp only [B]; ring
        rw [hr, ENNReal.ofReal_mul hB, ENNReal.ofReal_pow hR.le]
        rfl
      rw [hweight] at hm
      rw [enorm_mul, ← ofReal_norm, ← mul_assoc]
      exact mul_le_mul' hm (le_iSup (fun s => ‖a p s‖ₑ) t)
  have hen : ‖fibreSeriesC a ξ t - fibreSeriesC a ζ t‖ₑ ≤ ENNReal.ofReal (B * K) := by
    rw [he]
    calc
      _ ≤ ∑' p, ‖(fibreMonomial ξ p - fibreMonomial ζ p) * a p t‖ₑ := enorm_tsum_le_tsum_enorm
      _ ≤ ∑' p, ENNReal.ofReal B *
          (fibreCoefficientWeight (ENNReal.ofReal R) p * ⨆ s, ‖a p s‖ₑ) := ENNReal.tsum_le_tsum hp
      _ = ENNReal.ofReal B * ∑' p, fibreCoefficientWeight (ENNReal.ofReal R) p * ⨆ s, ‖a p s‖ₑ :=
        ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal B * ENNReal.ofReal K := mul_le_mul' le_rfl ha
      _ = _ := (ENNReal.ofReal_mul hB).symm
  rw [← ofReal_norm] at hen
  have hr := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hB hK)).mp hen
  exact hr.trans_eq (by dsimp only [B]; ring)

end AVRegularity.CycleEvolution
end
end
