-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.CellConjugateH1
import AVRegularity.CoupledEnergy.Galerkin.PlainVariationalEnergy
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
namespace AVRegularity.CycleEvolution

/-! Actual bounded bilinear evaluation of the named cell energy operator algebra. -/

def cellEnergyOperatorApplyCLM (a b : ℝ) :
    CellEnergyOperator a b →L[ℂ] CellEnergySpace a b →L[ℂ] CellEnergySpace a b :=
  ContinuousLinearMap.id ℂ (CellEnergyOperator a b)

theorem cellEnergyOperatorApply_analyticAt {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℂ X] (a b : ℝ)
    (T : X → CellEnergyOperator a b) (u : X → CellEnergySpace a b) (x : X)
    (hT : AnalyticAt ℂ T x) (hu : AnalyticAt ℂ u x) :
    AnalyticAt ℂ (fun y => cellEnergyOperatorApplyCLM a b (T y) (u y)) x :=
  ((cellEnergyOperatorApplyCLM a b).analyticAt_bilinear (T x, u x)).comp₂ hT hu

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleEvolution

/-! Quantitative energy control of the literal series of raw cell jets. -/

/-- Absolute energy summability controls the actual raw series in the energy seminorm. -/
theorem cellEnergyNorm_tsum_le {J : Type*} [Countable J]
    (D : J → ℝ → RawJet2 1 ℂ)
    (hD : ∀ j a, AEStronglyMeasurable (fun p : ℝ × Vec 2 => D j p.1 a p.2)
      ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)))
    (hs : (∑' j, cellEnergyNorm Set.univ (D j)) < ⊤) :
    cellEnergyNorm Set.univ (fun t a x => ∑' j, D j t a x) ≤
      2 * ∑' j, cellEnergyNorm Set.univ (D j) := by
  have hv t : cellL2Norm (cellValue (fun t a x => ∑' j, D j t a x) t) ≤
      ∑' j, cellEnergyNorm Set.univ (D j) := by
    have hb := fun j => cellValue_cellL2Norm_le_energy (D j) t
    have hseries := cellL2Series_memLp_bound (fun j => cellValue (D j) t)
      ((ENNReal.tsum_le_tsum hb).trans_lt hs)
    exact hseries.2.1.trans (ENNReal.tsum_le_tsum hb)
  have hg : (∑' j, cellUlNorm Set.univ (fun t => cellGradient (D j t))) ≤
      ∑' j, cellEnergyNorm Set.univ (D j) :=
    ENNReal.tsum_le_tsum (fun j => le_add_left le_rfl)
  have hgrad := (cellGradientSeries_cellUlNorm_le Set.univ D hD (hg.trans_lt hs)).trans hg
  change (⨆ t ∈ Set.univ, cellL2Norm (cellValue (fun t a x => ∑' j, D j t a x) t)) +
    cellUlNorm Set.univ (fun t => cellGradient (fun a x => ∑' j, D j t a x)) ≤
    2 * ∑' j, cellEnergyNorm Set.univ (D j)
  calc
    _ ≤ (∑' j, cellEnergyNorm Set.univ (D j)) + ∑' j, cellEnergyNorm Set.univ (D j) := by
      apply add_le_add _ hgrad
      apply iSup_le
      intro t
      apply iSup_le
      intro _
      exact hv t
    _ = _ := by ring

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
namespace AVRegularity.CycleEvolution

/-! Affine complex-linear Bloch derivative readouts of the finite energy carrier. -/

def cellFiniteEnergyTimeShiftedDerivativeCLM {a b : ℝ} (hab : a ≤ b)
    (θ : Fin 2 → ℂ) (j : Fin 2) :
    CellFiniteEnergyCarrier a b →L[ℂ] Lp ComplexCellL2 2 (volume.restrict (Icc a b)) :=
  cellFiniteEnergyTimeDerivativeCLM hab j +
    (Complex.I * θ j) • cellFiniteEnergyTimeValueCLM hab

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleEvolution

/-! A uniform-in-time finite cell L² bound derived from the actual energy estimate. -/

/-- The finite cell energy inequality implies an L² bound uniform on the time interval. -/
theorem cellFinite_energy_sup_bound {a b : ℝ} (hab : a ≤ b) (N : ℕ)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (hκ : ∀ t, ‖C.κ t‖ ≤ k)
    (S : ℝ → ComplexCellL2) (F : ℝ → Fin 2 → ComplexCellL2)
    (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (hF : ∀ j, MemLp (fun t => F t j) 2 (volume.restrict (Icc a b)))
    (u du : ℝ → ComplexCellL2) (y : ℝ → CellGalerkinSpace (E := ℂ) N)
    (hy : MemLp (fun t => (y t).val) 2 (volume.restrict (Icc a b)))
    (h : StrongVariationalSolution a b (cellGalerkinValue N).toLinearMap
      (fun t => cellGalerkinForm N (cellGeneratorB C hG V hv hb t))
      (fun t => cellGalerkinSource N (cellSourceFunctional C.θ (S t) (F t)).toLinearMap)
      u du y) :
    ∀ t ∈ Icc a b, ‖u t‖ ^ 2 ≤
      (‖u a‖ ^ 2 + ∫ s in a..b, ‖S s‖ ^ 2 + 9 * ∑ j, ‖F s j‖ ^ 2) *
        Real.exp (300 * (1 + ∑ j, ‖C.θ j‖ ^ 2 + V ^ 2 + k) * (b - a)) := by
  let R := 300 * (1 + ∑ j, ‖C.θ j‖ ^ 2 + V ^ 2 + k)
  let budget := ‖u a‖ ^ 2 + ∫ s in a..b, ‖S s‖ ^ 2 + 9 * ∑ j, ‖F s j‖ ^ 2
  have hR : 0 ≤ R := by
    have hk := (norm_nonneg (C.κ a)).trans (hκ a)
    dsimp only [R]
    positivity
  have hbudget : 0 ≤ budget := by
    have hi : 0 ≤ ∫ s in a..b, ‖S s‖ ^ 2 + 9 * ∑ j, ‖F s j‖ ^ 2 :=
      intervalIntegral.integral_nonneg_of_forall hab (fun s => by positivity)
    exact add_nonneg (sq_nonneg _) hi
  have he := cellFinite_energy_bound hab N C hG V k hv hb hκ S F hS hF u du y hy h
  intro t ht
  have het := he t ht
  have hd : 0 ≤ ∫ s in a..t, (1 / 2) * ∑ j, ‖cellDerivativeCLM j (y s).val‖ ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall ht.1 (fun s => by positivity)
  have hex : Real.exp (R * (t - a)) ≤ Real.exp (R * (b - a)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) hR
  have hm := mul_le_mul_of_nonneg_left hex hbudget
  dsimp only [R, budget] at hm
  linarith

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Hilbert representatives of the fixed-test generator entries used in weak limits. -/

/-- Riesz representative in the trial variable of a fixed generator test. -/
def cellGeneratorTest (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (t : ℝ) (z : TorusHk 1 ℂ) : TorusHk 1 ℂ :=
  (InnerProductSpace.toDual ℝ (TorusHk 1 ℂ)).symm
    ((cellGeneratorForm C hG V hv hb t).flip z)

/-- The fixed-test Riesz representative gives the literal generator entry. -/
theorem cellGeneratorTest_pairing (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (u z : TorusHk 1 ℂ) :
    inner ℝ u (cellGeneratorTest C hG V hv hb t z) = cellGeneratorForm C hG V hv hb t u z := by
  rw [real_inner_comm]
  exact InnerProductSpace.toDual_symm_apply

/-- Fixed-test generator representatives are strongly measurable in time. -/
theorem cellGeneratorTest_aestronglyMeasurable {μ : Measure ℝ}
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (hκ : Measurable C.κ) (z : TorusHk 1 ℂ) :
    AEStronglyMeasurable (fun t => cellGeneratorTest C hG V hv hb t z) μ := by
  apply cellH1_aestronglyMeasurable_of_pairings
  intro u
  simp only [real_inner_comm, cellGeneratorTest_pairing]
  exact (cellGeneratorForm_pairing_stronglyMeasurable C hG V hv hb hκ u z).aestronglyMeasurable

/-- A uniform form-functional bound also bounds its fixed-test Riesz representative. -/
theorem cellGeneratorTest_norm_le_of_bound
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ t u, ‖cellGeneratorForm C hG V hv hb t u‖ ≤ M * ‖u‖)
    (t : ℝ) (z : TorusHk 1 ℂ) : ‖cellGeneratorTest C hG V hv hb t z‖ ≤ M * ‖z‖ := by
  unfold cellGeneratorTest
  rw [LinearIsometryEquiv.norm_map]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hM (norm_nonneg z))
  intro u
  calc
    _ ≤ ‖cellGeneratorForm C hG V hv hb t u‖ * ‖z‖ :=
      (cellGeneratorForm C hG V hv hb t u).le_opNorm z
    _ ≤ (M * ‖u‖) * ‖z‖ := mul_le_mul_of_nonneg_right (hbound t u) (norm_nonneg z)
    _ = _ := by ring

/-- Actual fixed-test generator representatives belong to temporal L² on finite intervals. -/
theorem cellGeneratorTest_memLp (a b : ℝ)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (hκ : Measurable C.κ) (hκb : ∀ t, ‖C.κ t‖ ≤ k) (z : TorusHk 1 ℂ) :
    MemLp (fun t => cellGeneratorTest C hG V hv hb t z) 2 (volume.restrict (Icc a b)) := by
  obtain ⟨M, hM, hMb⟩ := cellGeneratorForm_uniform_norm_bound C hG V k hv hb hκb
  apply (memLp_const (M * ‖z‖)).of_le
    (cellGeneratorTest_aestronglyMeasurable C hG V hv hb hκ z)
  exact Filter.Eventually.of_forall (fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hM (norm_nonneg z))]
    exact cellGeneratorTest_norm_le_of_bound C hG V hv hb M hM hMb t z)

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The metric-gradient product difference has the expected bilinear norm estimate. -/

/-- Finite uniform coefficient sizes remain finite under subtraction. -/
theorem cellMetricSupNorm_sub_finite
    (G H : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : cellMetricSupNorm G < ⊤) (hH : cellMetricSupNorm H < ⊤) :
    cellMetricSupNorm (G - H) < ⊤ := by
  rw [sub_eq_add_neg]
  have h := cellMetricSupNorm_add G (-H)
  rw [cellMetricSupNorm_neg] at h
  exact h.trans_lt (ENNReal.add_lt_top.mpr ⟨hG, hH⟩)

/-- Coefficient and state errors separately control the uniformly local flux error. -/
theorem cellMetricFlux_difference_ul_bound (I : Set ℝ)
    (G H : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (D E : ℝ → RawJet2 1 ℂ)
    (hG : cellMetricSupNorm G < ⊤) (hH : cellMetricSupNorm H < ⊤)
    (hGm : Measurable (Function.uncurry G)) (hHm : Measurable (Function.uncurry H))
    (hD : ∀ a, AEStronglyMeasurable (fun p : ℝ × Vec 2 => D p.1 a p.2)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)))
    (hE : ∀ a, AEStronglyMeasurable (fun p : ℝ × Vec 2 => E p.1 a p.2)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    cellUlNorm I (cellMetricFlux G D - cellMetricFlux H E) ≤
      2 * cellMetricSupNorm (G - H) * cellEnergyNorm I D +
        2 * cellMetricSupNorm H * cellEnergyNorm I (D - E) := by
  have hDmE := fun a => (hD a).sub (hE a)
  have hdelta := cellMetricSupNorm_sub_finite G H hG hH
  have hdeltam := cellMetric_measurable_sub G H hGm hHm
  rw [cellMetricFlux_difference]
  have hh := cellUlNorm_add I (cellMetricFlux (G - H) D) (cellMetricFlux H (D - E))
    (cellMetricFlux_aestronglyMeasurable I (G - H) D hdeltam hD)
    (cellMetricFlux_aestronglyMeasurable I H (D - E) hHm hDmE)
  exact hh.trans (add_le_add
    (cellMetricFlux_ul_bound I (G - H) hdelta hdeltam D hD)
    (cellMetricFlux_ul_bound I H hH hHm (D - E) hDmE))

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The literal metric-jet flux is a finite real-linear sum of the bilinear perturbation fluxes. -/

/-- The strictly positive indices in the metric part of a cell jet equation. -/
def cellJetFluxIndices (α : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Iic α).filter (fun β => β ≠ 0)

/-- The binomial coefficient of a two-dimensional partial derivative. -/
def cellJetChoose (α β : ℕ × ℕ) : ℕ := α.1.choose β.1 * α.2.choose β.2

/-- Rewriting the public raw formula exposes its finite bilinear source sum. -/
theorem cellMetricJetFlux_eq_sum
    (Gj : ℕ × ℕ → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (cj : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (α : ℕ × ℕ) :
    cellMetricJetFlux Gj cj α = ∑ β ∈ cellJetFluxIndices α,
      (cellJetChoose α β : ℝ) • cellMetricFlux (Gj β) (cj (α.1 - β.1, α.2 - β.2)) := by
  funext t x
  apply PiLp.ext
  intro k
  simp only [cellMetricJetFlux, cellJetFluxIndices, cellJetChoose, Finset.sum_apply,
    WithLp.ofLp_sum, WithLp.ofLp_smul, Pi.smul_apply, cellMetricFlux, cellMetricFluxVector,
    cellGradient, Complex.real_smul, Complex.ofReal_natCast]

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The actual L² scalar source and divergence flux in the normalized frozen-metric graph equation. -/

def cellNormalizedGraphSourceClass (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : IsCellDrift v) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (θ : Fin 2 → ℂ) (κ : ℝ → ℂ) (t : ℝ) (u : TorusHk 1 ℂ) : ComplexCellL2 :=
  (∑ j : Fin 2, cellScalarCLM (-Complex.I * θ j)
    (cellDriftEntryCLM ⟨0, v, 0, 0⟩ V hv.1 hb t j (torusHkValueCLM u + cellConstantCLM 1))) +
  cellScalarCLM (κ t - ∑ j : Fin 2, ∑ k : Fin 2, (G t j k : ℂ) * θ j * θ k)
    (torusHkValueCLM u + cellConstantCLM 1)

def cellNormalizedGraphFluxClass (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (θ : Fin 2 → ℂ) (t : ℝ) (u : TorusHk 1 ℂ) (j : Fin 2) : ComplexCellL2 :=
  cellScalarCLM (2 * Complex.I * ∑ k : Fin 2, (G t j k : ℂ) * θ k) (torusHkValueCLM u)

/-! Actual linear scalar forcing of the unshifted formulation of the homogeneous Bloch equation. -/

def cellBlochLinearSourceClass (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ) (hv : IsCellDrift v)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (θ : Fin 2 → ℂ) (t : ℝ) (u : TorusHk 1 ℂ) : ComplexCellL2 :=
  (∑ j : Fin 2, cellScalarCLM (-Complex.I * θ j)
    (cellDriftEntryCLM ⟨0, v, 0, 0⟩ V hv.1 hb t j (torusHkValueCLM u))) +
  cellScalarCLM (-(∑ j : Fin 2, ∑ k : Fin 2, (G t j k : ℂ) * θ j * θ k))
    (torusHkValueCLM u)

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Exact scalar and divergence forcing identity for the complex Bloch generator. -/

theorem cellComplexGenerator_blochPerturbation (C : CellCoefficients) (hG : IsCellMetric C.G)
    (V : ℝ) (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (δ : Fin 2 → ℂ) (q : ℝ → ℂ) (t : ℝ) (u z : TorusHk 1 ℂ) :
    cellComplexGenerator { C with θ := C.θ + δ, κ := fun s => C.κ s + q s }
      hG V hv hb t u z = cellComplexGenerator C hG V hv hb t u z +
      cellComplexSource C.θ (cellBlochPerturbationScalar C hG V hv hb δ q t u)
        (cellBlochPerturbationFlux C hG δ t u) z := by
  have hstar : (fun j => star ((C.θ + δ) j)) =
      (fun j => star (C.θ j)) + (fun j => star (δ j)) := by
    funext j
    simp only [Pi.add_apply, star_add]
  change -(∑ j : Fin 2, ∑ k : Fin 2, cellComplexPair
    (cellMetricEntryCLM hG t j k (cellShiftedDerivativeCLM (C.θ + δ) j u))
    (cellShiftedDerivativeCLM (fun i => star ((C.θ + δ) i)) k z)) -
    (∑ j : Fin 2, cellComplexPair
      (cellDriftEntryCLM C V hv hb t j (cellShiftedDerivativeCLM (C.θ + δ) j u))
      (torusHkValueCLM z)) +
    cellComplexPair (cellScalarCLM (C.κ t + q t) (torusHkValueCLM u)) (torusHkValueCLM z) = _
  rw [hstar]
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  simp only [cellComplexGenerator, cellComplexSource, cellBlochPerturbationScalar,
    cellBlochPerturbationFlux, Fin.sum_univ_two, cellShiftedDerivativeCLM_add_shift,
    map_add, cellComplexPair_add_left, cellComplexPair_add_right,
    cellComplexPair_scalar_left, cellComplexPair_scalar_right,
    star_mul, star_star, hI]
  have hsub (x y w : ComplexCellL2) : cellComplexPair (x - y) w =
      cellComplexPair x w - cellComplexPair y w := by
    rw [sub_eq_add_neg, cellComplexPair_add_left]
    have hn : -y = cellScalarCLM (-1) y := by change -y = (-1 : ℂ) • y; simp
    rw [hn, cellComplexPair_scalar_left]
    ring
  rw [hsub]
  simp only [cellComplexPair_add_left, cellComplexPair_scalar_left]
  ring

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The constant test annihilates the actual unshifted complex drift form. -/

/-- The sum of drift pairings against one vanishes for every complex H¹ state. -/
theorem cellDrift_constant_pair_sum (C : CellCoefficients) (hv : IsCellDrift C.v) (V : ℝ)
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (u : TorusHk 1 ℂ) :
    (∑ j : Fin 2, cellComplexPair
      (cellDriftEntryCLM C V hv.1 hb t j (cellDerivativeCLM j u)) (cellConstantCLM 1)) = 0 := by
  let : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using cellCube_volume_one⟩
  have hi (j : Fin 2) : Integrable (fun x => (C.v t x j : ℂ) * cellDerivativeCLM j u x)
      (volume.restrict AVenhance.unitCube) := by
    exact ((Lp.memLp (cellDriftEntryCLM C V hv.1 hb t j (cellDerivativeCLM j u))).integrable
      (by norm_num)).congr (cellDriftEntryCLM_ae C V hv.1 hb t j (cellDerivativeCLM j u))
  have hp (j : Fin 2) : cellComplexPair
      (cellDriftEntryCLM C V hv.1 hb t j (cellDerivativeCLM j u)) (cellConstantCLM 1) =
      ∫ x in AVenhance.unitCube, (C.v t x j : ℂ) * cellDerivativeCLM j u x := by
    rw [cellComplexPair_one]
    exact integral_congr_ae (cellDriftEntryCLM_ae C V hv.1 hb t j (cellDerivativeCLM j u))
  simp_rw [hp]
  rw [← integral_finsetSum Finset.univ (fun j _ => hi j)]
  exact cellDrift_mean_zero hv V hb t u

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal BigOperators
namespace AVRegularity.CycleEvolution

/-! Quantitative control of literal finite sums of actual raw cell jets. -/

/-- An absolutely finite energy family has a literal finite-sum bound, obtained from the proved series bound. -/
theorem cellEnergyNorm_finset_sum_le_two {J : Type*} [DecidableEq J]
    (s : Finset J) (D : J → ℝ → RawJet2 1 ℂ)
    (hD : ∀ j ∈ s, ∀ a, AEStronglyMeasurable (fun p : ℝ × Vec 2 => D j p.1 a p.2)
      ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)))
    (hfinite : ∀ j ∈ s, cellEnergyNorm Set.univ (D j) < ⊤) :
    cellEnergyNorm Set.univ (∑ j ∈ s, D j) ≤ 2 * ∑ j ∈ s, cellEnergyNorm Set.univ (D j) := by
  let F := fun j : s => D j.1
  have hs : (∑' j : s, cellEnergyNorm Set.univ (F j)) < ⊤ := by
    rw [tsum_fintype]
    exact ENNReal.sum_lt_top.mpr (fun j _ => hfinite j.1 j.2)
  have hb := cellEnergyNorm_tsum_le F (fun j a => hD j.1 j.2 a) hs
  have he : (∑ j ∈ s, D j) = (fun t a x => ∑' j : s, F j t a x) := by
    funext t a x
    rw [tsum_fintype]
    simp only [Finset.sum_apply, F]
    exact (Finset.sum_finset_coe (fun j => D j t a x) s).symm
  have hn : (∑' j : s, cellEnergyNorm Set.univ (F j)) =
      ∑ j ∈ s, cellEnergyNorm Set.univ (D j) := by
    rw [tsum_fintype]
    exact Finset.sum_finset_coe (fun j => cellEnergyNorm Set.univ (D j)) s
  rw [← he, hn] at hb
  exact hb

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleEvolution

/-! An invertible actual cell perturbation identifies its weakly derived fixed point with the inverse formula. -/

theorem cellEnergyOperator_inverse_fixedPoint {a b : ℝ} (T : CellEnergyOperator a b)
    (hT : IsUnit (1 - T)) (u z : CellEnergySpace a b)
    (hz : z = u + cellEnergyOperatorApplyCLM a b T z) :
    z = cellEnergyOperatorApplyCLM a b (Ring.inverse (1 - T)) u := by
  have he := congrArg (fun L : CellEnergyOperator a b => cellEnergyOperatorApplyCLM a b L z)
    (Ring.inverse_mul_cancel (1 - T) hT)
  change cellEnergyOperatorApplyCLM a b (Ring.inverse (1 - T))
    (z - cellEnergyOperatorApplyCLM a b T z) = z at he
  have hs : z - cellEnergyOperatorApplyCLM a b T z = u := sub_eq_iff_eq_add.mpr hz
  rw [hs] at he
  exact he.symm

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.CycleEvolution

/-! Actual finite cell approximations have strong H¹-in-time L² traces. -/

/-- Construct a finite weak cell path and its square-integrable strong time derivative
under the coefficient/source assumptions, starting from arbitrary L² data. -/
theorem cellGalerkin_actual_exists_timeH1 {a b : ℝ} (hab : a ≤ b) (N : ℕ)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hvb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (hκ : Measurable C.κ) (hκb : ∀ t, ‖C.κ t‖ ≤ k)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrcm : Measurable (Function.uncurry src)) (hFm : Measurable (Function.uncurry F))
    (hsrc : ∫⁻ t in Icc a b, cellL2Norm (src t) ^ 2 < ⊤)
    (hF : ∫⁻ t in Icc a b, cellL2Norm (F t) ^ 2 < ⊤)
    (u₀ : Lp ℂ 2 (volume.restrict AVenhance.unitCube)) :
    let B := cellGeneratorB C hG V hv hvb
    let q := cellRawSourceFunctional C.θ src F
    let A := fun t => cellGalerkinOperator N (B t)
    let f := fun t => cellGalerkinForcing N (q t)
    ∃ y : ContinuousMap (Icc a b) (CellGalerkinSpace (E := ℂ) N),
      StrongVariationalSolution a b (cellGalerkinValue N).toLinearMap
        (fun t => cellGalerkinForm N (B t)) (fun t => cellGalerkinSource N (q t))
        (fun t => cellGalerkinValue N (extendCurve hab y t))
        (fun t => cellGalerkinValue N (linearRhs A f (extendCurve hab y) t))
        (extendCurve hab y) ∧
      MemLp (fun t => cellGalerkinValue N (linearRhs A f (extendCurve hab y) t))
        2 (volume.restrict (Icc a b)) ∧
      MemLp (fun t => (extendCurve hab y t).val) 2 (volume.restrict (Icc a b)) ∧
      cellGalerkinValue N (extendCurve hab y a) = cellGalerkinValue N (cellGalerkinL2Initial N u₀) := by
  dsimp only
  obtain ⟨M, hM, hMb⟩ := cellGalerkin_actualOperator_bounded N C hG V k hv hvb hκb
  have hA := cellGalerkin_actualOperator_aestronglyMeasurable N C hG V hv hvb hκ
  have hq := cellGalerkin_actualForcing_memLp N C.θ src F
    (cellSource_memLp_product (Icc a b) src hsrcm hsrc)
    (cellSource_memLp_product (Icc a b) F hFm hF)
  obtain ⟨y, hy, hdy, hstate, hinit⟩ := cellGalerkin_exists_timeH1 hab N
    (cellGeneratorB C hG V hv hvb) (cellRawSourceFunctional C.θ src F)
    (smoothFourierLift (K := 0) (L := 1) N (cellL2AsH0 u₀)) M hM hA hMb hq
  refine ⟨y, hy, hdy, hstate, ?_⟩
  change cellGalerkinValue N (extendCurve hab y a) = cellGalerkinValue N (cellL2FourierState N u₀)
    at hinit
  rw [← cellGalerkinL2Initial_eq_fourier] at hinit
  exact hinit

end AVRegularity.CycleEvolution
end
end

section
@[expose] public section
namespace AVRegularity.CycleEvolution

/-! Strictly lower-order dependencies in the triangular cell jet equations. -/

/-- Every metric-jet flux index is positive and componentwise below the given index. -/
theorem cellJetFluxIndices_mem {α β : ℕ × ℕ} (hβ : β ∈ cellJetFluxIndices α) :
    β.1 ≤ α.1 ∧ β.2 ≤ α.2 ∧ β ≠ 0 := by
  have h := Finset.mem_filter.mp hβ
  have hl := Finset.mem_Iic.mp h.1
  exact ⟨hl.1, hl.2, h.2⟩

/-- Every state in a metric-jet forcing has strictly smaller total derivative order. -/
theorem cellJetFluxIndices_lower_order {α β : ℕ × ℕ} (hβ : β ∈ cellJetFluxIndices α) :
    (α.1 - β.1) + (α.2 - β.2) < α.1 + α.2 := by
  obtain ⟨h1, h2, hne⟩ := cellJetFluxIndices_mem hβ
  have hp : 0 < β.1 + β.2 := by
    by_contra hn
    have hz : β = 0 := Prod.ext (by change β.1 = 0; omega) (by change β.2 = 0; omega)
    exact hne hz
  omega

/-- Metric derivatives appearing in a jet flux are within the given total order. -/
theorem cellJetFluxIndices_metric_order {α β : ℕ × ℕ} (hβ : β ∈ cellJetFluxIndices α) :
    β.1 + β.2 ≤ α.1 + α.2 := by
  obtain ⟨h1, h2, _⟩ := cellJetFluxIndices_mem hβ
  omega

/-- A zeroth-order jet has no metric-jet forcing. -/
theorem cellJetFluxIndices_zero : cellJetFluxIndices 0 = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro β hb
  obtain ⟨h1, h2, hn⟩ := cellJetFluxIndices_mem hb
  change β.1 ≤ 0 at h1
  change β.2 ≤ 0 at h2
  exact hn (Prod.ext (by change β.1 = 0; omega) (by change β.2 = 0; omega))

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleEvolution

/-! Uniform initial norm bound for the actual graph projection remainder. -/

theorem cellNormalized_remainder_norm (u R ell : ComplexCellL2)
    (hR : ‖R‖ ≤ 3) (hell : ‖ell‖ ≤ 4) :
    ‖u - cellScalarCLM (cellComplexPair u
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap ell)) R‖ ≤ 13 * ‖u‖ := by
  have hc := cellComplexPair_norm_le u (cellFiberCLM Complex.conjCLE.toContinuousLinearMap ell)
  rw [cellFiberConj_norm] at hc
  have hcn : ‖cellComplexPair u
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap ell)‖ ≤ 4 * ‖u‖ := by
    calc
      _ ≤ ‖u‖ * ‖ell‖ := hc
      _ ≤ ‖u‖ * 4 := mul_le_mul_of_nonneg_left hell (norm_nonneg _)
      _ = _ := mul_comm _ _
  calc
    _ ≤ ‖u‖ + ‖cellScalarCLM (cellComplexPair u
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap ell)) R‖ := norm_sub_le _ _
    _ = ‖u‖ + ‖cellComplexPair u
      (cellFiberCLM Complex.conjCLE.toContinuousLinearMap ell)‖ * ‖R‖ := by
        rw [cellScalarCLM_smul, norm_smul]
    _ ≤ ‖u‖ + (4 * ‖u‖) * 3 := by
      gcongr
    _ = _ := by ring

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Temporal Hilbert norms and value-gradient decomposition. -/

/-- The norm of a temporal L² class is the real norm-square integral of its representative. -/
theorem cellTimeL2_norm_sq_integral {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {μ : Measure ℝ} (f : ℝ → E) (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with t ht
  rw [ht, real_inner_self_eq_norm_sq]

/-- The gradient square of a Bochner H¹ state is integrable in time. -/
theorem cellTime_gradientSq_intervalIntegrable {a b : ℝ} (hab : a ≤ b)
    (f : ℝ → TorusHk 1 ℂ) (hf : MemLp f 2 (volume.restrict (Icc a b))) :
    IntervalIntegrable (fun t => ∑ j, ‖cellDerivativeCLM j (f t)‖ ^ 2) volume a b := by
  have hj (j : Fin 2) := cellTime_normSq_intervalIntegrable hab ((cellDerivativeCLM j).comp_memLp' hf)
  simpa only [Fin.sum_univ_two, Function.comp_def, Pi.add_def] using (hj 0).add (hj 1)

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Actual complex linearity of the literal Bloch generator. -/

theorem cellComplexGenerator_scalar (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (t : ℝ) (u z : TorusHk 1 ℂ) (c : ℂ) :
    cellComplexGenerator C hG V hv hb t (cellH1Scalar c u) z =
      c * cellComplexGenerator C hG V hv hb t u z := by
  simp only [cellComplexGenerator, cellH1Scalar_shift, cellH1Scalar_value,
    cellMetricEntryCLM_scalar, cellDriftEntryCLM_scalar, cellScalarCLM_mul,
    cellComplexPair_scalar_left, Fin.sum_univ_two]
  ring

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleEvolution

/-! Cutoff-independent temporal H¹ norm control for finite cell solutions. -/

/-- The finite cell energy estimate bounds the temporal H¹ norm independently of the cutoff. -/
theorem cellFinite_bochner_norm_bound {a b : ℝ} (hab : a ≤ b) (N : ℕ)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (hκ : ∀ t, ‖C.κ t‖ ≤ k)
    (S : ℝ → ComplexCellL2) (F : ℝ → Fin 2 → ComplexCellL2)
    (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (hF : ∀ j, MemLp (fun t => F t j) 2 (volume.restrict (Icc a b)))
    (u du : ℝ → ComplexCellL2) (y : ℝ → CellGalerkinSpace (E := ℂ) N)
    (hy : MemLp (fun t => (y t).val) 2 (volume.restrict (Icc a b)))
    (h : StrongVariationalSolution a b (cellGalerkinValue N).toLinearMap
      (fun t => cellGalerkinForm N (cellGeneratorB C hG V hv hb t))
      (fun t => cellGalerkinSource N (cellSourceFunctional C.θ (S t) (F t)).toLinearMap)
      u du y) :
    ‖hy.toLp (fun t => (y t).val)‖ ^ 2 ≤
      (b - a + 2) *
        ((‖u a‖ ^ 2 + ∫ s in a..b, ‖S s‖ ^ 2 + 9 * ∑ j, ‖F s j‖ ^ 2) *
          Real.exp (300 * (1 + ∑ j, ‖C.θ j‖ ^ 2 + V ^ 2 + k) * (b - a))) := by
  let R := 300 * (1 + ∑ j, ‖C.θ j‖ ^ 2 + V ^ 2 + k)
  let budget := ‖u a‖ ^ 2 + ∫ s in a..b, ‖S s‖ ^ 2 + 9 * ∑ j, ‖F s j‖ ^ 2
  let E := budget * Real.exp (R * (b - a))
  let grad := fun s => ∑ j, ‖cellDerivativeCLM j (y s).val‖ ^ 2
  have hR : 0 ≤ R := by
    have hk := (norm_nonneg (C.κ a)).trans (hκ a)
    dsimp only [R]
    positivity
  have hbgt : 0 ≤ budget := by
    have hi : 0 ≤ ∫ s in a..b, ‖S s‖ ^ 2 + 9 * ∑ j, ‖F s j‖ ^ 2 :=
      intervalIntegral.integral_nonneg_of_forall hab (fun s => by positivity)
    exact add_nonneg (sq_nonneg _) hi
  have he := cellFinite_energy_bound hab N C hG V k hv hb hκ S F hS hF u du y hy h
  have hucont : ContinuousOn (fun t => ‖u t‖ ^ 2) (Icc a b) := by
    simpa only [uIcc_of_le hab] using h.time.norm_sq_ac.continuousOn
  have hug : IntervalIntegrable (fun t => ‖u t‖ ^ 2) volume a b :=
    hucont.intervalIntegrable_of_Icc hab
  have hgint : IntervalIntegrable grad volume a b :=
    cellTime_gradientSq_intervalIntegrable hab _ hy
  have hepoint : ∀ t ∈ Icc a b, ‖u t‖ ^ 2 ≤ E := by
    intro t ht
    have het := he t ht
    have hd : 0 ≤ ∫ s in a..t, (1 / 2) * grad s :=
      intervalIntegral.integral_nonneg_of_forall ht.1 (fun s => by dsimp only [grad]; positivity)
    have hex : Real.exp (R * (t - a)) ≤ Real.exp (R * (b - a)) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) hR
    have hm := mul_le_mul_of_nonneg_left hex hbgt
    dsimp only [E, R, budget, grad] at hd hm ⊢
    linarith
  have hegrad : (∫ s in a..b, grad s) ≤ 2 * E := by
    have heb := he b ⟨hab, le_rfl⟩
    change ‖u b‖ ^ 2 + (∫ s in a..b, (1 / 2) * grad s) ≤ E at heb
    rw [intervalIntegral.integral_const_mul] at heb
    nlinarith [sq_nonneg ‖u b‖]
  have heu : (∫ s in a..b, ‖u s‖ ^ 2) ≤ (b - a) * E := by
    have hm := intervalIntegral.integral_mono_on hab hug
      (continuous_const.intervalIntegrable a b) (fun s hs => hepoint s ⟨hs.1, hs.2⟩)
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using hm
  have hi : (∫ s in a..b, ‖(y s).val‖ ^ 2) =
      (∫ s in a..b, ‖u s‖ ^ 2) + ∫ s in a..b, grad s := by
    rw [← intervalIntegral.integral_add hug hgint]
    apply intervalIntegral.integral_congr_ae_restrict
    have ha := h.agrees.filter_mono (ae_mono (Measure.restrict_mono uIoc_subset_uIcc le_rfl))
    filter_upwards [ha] with t ht
    rw [ht, cellH1_norm_sq]
    rfl
  have hn := cellTimeL2_norm_sq_integral (fun t => (y t).val) hy
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab, hi] at hn
  rw [hn]
  change (∫ s in a..b, ‖u s‖ ^ 2) + (∫ s in a..b, grad s) ≤ (b - a + 2) * E
  nlinarith

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.Torus
namespace AVRegularity.CycleEvolution

/-! Sharp mean-free Poincaré inequality for the finite cell Fourier approximants.
The upstream smooth theorem is used with its exact smoothness and zero-mean hypotheses. -/

/-- The sharp cell Poincaré bound for a projected H¹ class, with its mean removed. -/
theorem cellFinite_meanFree_poincare (u : TorusHk 1 ℂ) (N : ℕ) :
    ‖cellQ0CLM (torusHkValueCLM (galerkinProj N u))‖ ^ 2 ≤
      (4 * Real.pi ^ 2)⁻¹ * ∑ j, ‖cellDerivativeCLM j (galerkinProj N u)‖ ^ 2 := by
  let p := galerkinProj N u
  let q := smoothFourierJet (L := 1) N u (valueIndex2 1)
  have hq : ContDiff ℝ 1 q := (smoothFourierJet_contDiff N u _).of_le (by simp)
  have hp : AVenhance.IsZ2Periodic q := smoothFourierJet_periodic N u _
  have hq0 : ContDiff ℝ 1 (cellQ0 q) := hq.sub contDiff_const
  have hp0 : AVenhance.IsZ2Periodic (cellQ0 q) := by
    intro n x
    dsimp only [cellQ0]
    rw [hp n x]
  have hm0 := cellQ0_mean (smoothFourierJet_memLp (L := 1) N u (valueIndex2 1))
  have hm : (∫ x in unitCell 2, cellQ0 q x) = 0 := by
    rw [integral_unitCell_eq_unitCube]
    exact hm0
  have hP := meanZero_smoothPeriodic_poincare hq0 hp0 hm
  rw [integral_unitCell_eq_unitCube, integral_unitCell_eq_unitCube] at hP
  have hval : torusHkValueCLM p =ᵐ[volume.restrict AVenhance.unitCube] q :=
    galerkinProj_jet_ae_smooth N u (valueIndex2 1)
  have hmean : cellMean (torusHkValueCLM p) = cellMean q := integral_congr_ae hval
  have hQ : cellQ0CLM (torusHkValueCLM p) =ᵐ[volume.restrict AVenhance.unitCube] cellQ0 q := by
    filter_upwards [cellQ0CLM_ae (torusHkValueCLM p), hval] with x hx hv
    rw [hx]
    dsimp only [cellQ0]
    rw [hv, hmean]
  have hd (j : Fin 2) : cellDerivativeCLM j p =ᵐ[volume.restrict AVenhance.unitCube]
      coordDeriv j (cellQ0 q) := by
    have he := galerkinProj_jet_ae_smooth N u ⟨⟨1, by decide⟩, fun _ => j⟩
    filter_upwards [he] with x hx
    change cellDerivativeCLM j p x = _ at hx
    rw [hx]
    change smoothFourierJet (L := 1) N u (nextIndex2 (0 : Fin 1) Fin.elim0 j) x =
      fderiv ℝ (fun y => q y - cellMean q) x (basisVec j)
    rw [fderiv_sub_const]
    exact (smoothFourierJet_fderiv (L := 1) N u (0 : Fin 1) Fin.elim0 j x).symm
  have hi (j : Fin 2) := integrable_normSq_of_memLp (Lp.memLp (cellDerivativeCLM j p))
  have hR : (∫ x in AVenhance.unitCube, ∑ j : Fin 2, ‖coordDeriv j (cellQ0 q) x‖ ^ 2) =
      ∑ j : Fin 2, ‖cellDerivativeCLM j p‖ ^ 2 := by
    calc
      _ = (∫ x in AVenhance.unitCube, ∑ j : Fin 2, ‖cellDerivativeCLM j p x‖ ^ 2) := by
        apply integral_congr_ae
        filter_upwards [ae_all_iff.2 hd] with x hx
        simp only [hx]
      _ = ∑ j : Fin 2, ‖cellDerivativeCLM j p‖ ^ 2 := by
        rw [integral_finsetSum Finset.univ (fun j _ => hi j)]
        simp_rw [cellL2_norm_sq_integral]
  have hL : (∫ x in AVenhance.unitCube, ‖cellQ0 q x‖ ^ 2) =
      ‖cellQ0CLM (torusHkValueCLM p)‖ ^ 2 := by
    rw [← cellL2_norm_sq_integral]
    exact integral_congr_ae (hQ.mono (fun x hx => congrArg (fun z : ℂ => ‖z‖ ^ 2) hx.symm))
  rw [hL, hR] at hP
  exact hP

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
namespace AVRegularity.CycleEvolution

/-! Finite-time L2 class norms in the exact interval-integral form used by the actual energy inequality. -/

theorem cellLpL2_norm_sq_integral {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (μ : Measure X) (u : Lp E 2 μ) :
    ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp_rw [real_inner_self_eq_norm_sq]

theorem cellLpTime_norm_sq_intervalIntegral {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {a b : ℝ} (hab : a ≤ b)
    (u : Lp E 2 (volume.restrict (Icc a b))) :
    (∫ t in a..b, ‖u t‖ ^ 2) = ‖u‖ ^ 2 := by
  have h := cellTimeL2_norm_sq_integral (fun t => u t) (Lp.memLp u)
  rw [Lp.toLp_coeFn, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab] at h
  exact h.symm

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter Topology
namespace AVRegularity.CycleEvolution

/-! Bilinear norm continuity of the actual metric-gradient flux for arbitrary parameter filters. -/

/-- Coefficient and energy-state norm convergence imply uniformly local convergence of the flux. -/
theorem cellMetricFlux_tendsto {P : Type*} (l : Filter P)
    (A : P → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (B : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (E : P → ℝ → RawJet2 1 ℂ) (D : ℝ → RawJet2 1 ℂ)
    (hA : ∀ p, cellMetricSupNorm (A p) < ⊤ ∧ Measurable (Function.uncurry (A p)))
    (hB : cellMetricSupNorm B < ⊤ ∧ Measurable (Function.uncurry B))
    (hD : cellEnergyNorm univ D < ⊤)
    (hEm : ∀ p a, AEStronglyMeasurable (fun z : ℝ × Vec 2 => E p z.1 a z.2)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hDm : ∀ a, AEStronglyMeasurable (fun z : ℝ × Vec 2 => D z.1 a z.2)
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)))
    (hAc : Tendsto (fun p => cellMetricSupNorm (A p - B)) l (𝓝 0))
    (hEc : Tendsto (fun p => cellEnergyNorm univ (E p - D)) l (𝓝 0)) :
    Tendsto (fun p => cellUlNorm univ (cellMetricFlux (A p) (E p) - cellMetricFlux B D)) l (𝓝 0) := by
  have hb (p : P) : cellUlNorm univ (cellMetricFlux (A p) (E p) - cellMetricFlux B D) ≤
      2 * cellMetricSupNorm (A p - B) *
        (cellEnergyNorm univ (E p - D) + cellEnergyNorm univ D) +
      2 * cellMetricSupNorm B * cellEnergyNorm univ (E p - D) := by
    have hh := cellMetricFlux_difference_ul_bound univ (A p) B (E p) D
      (hA p).1 hB.1 (hA p).2 hB.2 (hEm p) hDm
    have he := cellEnergyNorm_le_sub_add univ (E p) D (hEm p) hDm
    exact hh.trans (by gcongr)
  have hde : Tendsto (fun p => cellEnergyNorm univ (E p - D) + cellEnergyNorm univ D)
      l (𝓝 (cellEnergyNorm univ D)) := by
    simpa only [zero_add] using hEc.add_const (cellEnergyNorm univ D)
  have hmul := ENNReal.Tendsto.mul hAc (Or.inr hD.ne) hde (Or.inr (by simp))
  have hmul2 := ENNReal.Tendsto.const_mul hmul (a := 2) (Or.inr (by norm_num))
  have hB2 : 2 * cellMetricSupNorm B ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hB.1.ne
  have hlast := ENNReal.Tendsto.const_mul hEc (a := 2 * cellMetricSupNorm B) (Or.inr hB2)
  have hlim : Tendsto (fun p => 2 * cellMetricSupNorm (A p - B) *
        (cellEnergyNorm univ (E p - D) + cellEnergyNorm univ D) +
      2 * cellMetricSupNorm B * cellEnergyNorm univ (E p - D)) l (𝓝 0) := by
    simpa only [mul_zero, zero_mul, zero_add, mul_assoc] using hmul2.add hlast
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) hb

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleEvolution

/-! The triangular jet flux depends only on strictly lower-order states. -/

/-- Changing higher-order states preserves a given metric-jet forcing exactly. -/
theorem cellMetricJetFlux_congr_lower
    (Gj : ℕ × ℕ → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (cj dj : ℕ × ℕ → ℝ → RawJet2 1 ℂ) (α : ℕ × ℕ)
    (he : ∀ γ : ℕ × ℕ, γ.1 + γ.2 < α.1 + α.2 → cj γ = dj γ) :
    cellMetricJetFlux Gj cj α = cellMetricJetFlux Gj dj α := by
  rw [cellMetricJetFlux_eq_sum, cellMetricJetFlux_eq_sum]
  apply Finset.sum_congr rfl
  intro β hβ
  rw [he (α.1 - β.1, α.2 - β.2) (cellJetFluxIndices_lower_order hβ)]

/-- The zeroth-order metric-jet flux is zero. -/
theorem cellMetricJetFlux_zero
    (Gj : ℕ × ℕ → ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (cj : ℕ × ℕ → ℝ → RawJet2 1 ℂ) : cellMetricJetFlux Gj cj 0 = 0 := by
  rw [cellMetricJetFlux_eq_sum, cellJetFluxIndices_zero, Finset.sum_empty]

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! The normalized graph source class has its actual literal spatial representative. -/

theorem cellNormalizedGraphSourceClass_ae (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (θ : Fin 2 → ℂ) (κ : ℝ → ℂ)
    (t : ℝ) (u : TorusHk 1 ℂ) :
    cellNormalizedGraphSourceClass G v V hv hb θ κ t u =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => -Complex.I * (∑ j : Fin 2, θ j * (v t x j : ℂ)) * (1 + torusHkValueCLM u x) +
        (κ t - ∑ j : Fin 2, ∑ k : Fin 2, (G t j k : ℂ) * θ j * θ k) *
          (1 + torusHkValueCLM u x) := by
  let R := torusHkValueCLM u + cellConstantCLM 1
  let q := κ t - ∑ j : Fin 2, ∑ k : Fin 2, (G t j k : ℂ) * θ j * θ k
  let A := fun j => cellScalarCLM (-Complex.I * θ j)
    (cellDriftEntryCLM ⟨0, v, 0, 0⟩ V hv.1 hb t j R)
  let P := cellScalarCLM q R
  have hR : R =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => torusHkValueCLM u x + 1 := by
    filter_upwards [Lp.coeFn_add (torusHkValueCLM u) (cellConstantCLM 1), cellConstantCLM_ae 1]
      with x ha h1
    rw [ha]
    change torusHkValueCLM u x + cellConstantCLM 1 x = _
    rw [h1]
  have hA (j : Fin 2) : A j =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => (-Complex.I * θ j) * ((v t x j : ℂ) * (torusHkValueCLM u x + 1)) := by
    filter_upwards [cellScalarCLM_ae (-Complex.I * θ j)
      (cellDriftEntryCLM ⟨0, v, 0, 0⟩ V hv.1 hb t j R),
      cellDriftEntryCLM_ae ⟨0, v, 0, 0⟩ V hv.1 hb t j R, hR] with x ha hd hr
    rw [ha, hd, hr]
  have hP : P =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => q * (torusHkValueCLM u x + 1) := by
    filter_upwards [cellScalarCLM_ae q R, hR] with x hp hr
    rw [hp, hr]
  filter_upwards [ae_all_iff.mpr hA, Lp.coeFn_fun_finsetSum Finset.univ A, hP,
    Lp.coeFn_add (∑ j : Fin 2, A j) P] with x ha hs hp hadd
  change ((∑ j : Fin 2, A j) + P) x = _
  rw [hadd]
  change (∑ j : Fin 2, A j) x + P x = _
  rw [hs, hp]
  simp only [Fin.sum_univ_two]
  rw [ha 0, ha 1]
  dsimp only [q]
  simp only [Fin.sum_univ_two]
  ring

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleEvolution

/-! Passing from the cell gradient to the Bloch covariant gradient. -/

theorem cellShiftedGradient_point_energy_le (θ : Fin 2 → ℂ) (q : ℝ)
    (hθ : ∀ j, ‖θ j‖ ≤ q) (u : TorusHk 1 ℂ) :
    (∑ j, ‖cellShiftedDerivativeCLM θ j u‖ ^ 2) ≤
      2 * (∑ j, ‖cellDerivativeCLM j u‖ ^ 2) + 4 * q ^ 2 * ‖torusHkValueCLM u‖ ^ 2 := by
  have hq : 0 ≤ q := (norm_nonneg (θ 0)).trans (hθ 0)
  have hj (j : Fin 2) : ‖cellShiftedDerivativeCLM θ j u‖ ^ 2 ≤
      2 * ‖cellDerivativeCLM j u‖ ^ 2 + 2 * q ^ 2 * ‖torusHkValueCLM u‖ ^ 2 := by
    have he : cellShiftedDerivativeCLM θ j u = cellDerivativeCLM j u +
        cellScalarCLM (Complex.I * θ j) (torusHkValueCLM u) := rfl
    have hn := norm_add_le (cellDerivativeCLM j u) (cellScalarCLM (Complex.I * θ j) (torusHkValueCLM u))
    rw [← he, cellScalarCLM_norm] at hn
    simp only [norm_mul, Complex.norm_I, one_mul] at hn
    have hsq := (sq_le_sq₀ (norm_nonneg (θ j)) hq).mpr (hθ j)
    have hm := mul_le_mul_of_nonneg_right hsq (sq_nonneg ‖torusHkValueCLM u‖)
    have hp := norm_nonneg (cellShiftedDerivativeCLM θ j u)
    have hd := norm_nonneg (cellDerivativeCLM j u)
    have ht := norm_nonneg (θ j)
    have hv := norm_nonneg (torusHkValueCLM u)
    nlinarith [sq_nonneg (‖cellDerivativeCLM j u‖ - ‖θ j‖ * ‖torusHkValueCLM u‖)]
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 2))) => hj j)
  simp only [Fin.sum_univ_two] at hs ⊢
  linarith

theorem cellShiftedGradient_integral_energy_le {a b : ℝ} (hab : a ≤ b)
    (θ : Fin 2 → ℂ) (q M : ℝ) (hθ : ∀ j, ‖θ j‖ ≤ q) (hM : 0 ≤ M)
    (slice : ℝ → TorusHk 1 ℂ) (hs : MemLp slice 2 (volume.restrict (Icc a b)))
    (hb : ∀ᵐ t ∂volume.restrict (Icc a b), ‖torusHkValueCLM (slice t)‖ ≤ M) :
    (∫ t in a..b, ∑ j, ‖cellShiftedDerivativeCLM θ j (slice t)‖ ^ 2) ≤
      2 * (∫ t in a..b, ∑ j, ‖cellDerivativeCLM j (slice t)‖ ^ 2) +
        4 * q ^ 2 * (b - a) * M ^ 2 := by
  have hgrad := cellTime_gradientSq_intervalIntegrable hab slice hs
  have hi (j : Fin 2) := cellTime_normSq_intervalIntegrable hab
    ((cellShiftedDerivativeCLM θ j).comp_memLp' hs)
  have hcov : IntervalIntegrable (fun t => ∑ j, ‖cellShiftedDerivativeCLM θ j (slice t)‖ ^ 2) volume a b := by
    simpa only [Fin.sum_univ_two, Pi.add_apply, Function.comp_def] using (hi 0).add (hi 1)
  have hconst : IntervalIntegrable (fun _ : ℝ => 4 * q ^ 2 * M ^ 2) volume a b := intervalIntegrable_const
  have he := intervalIntegral.integral_mono_ae_restrict hab hcov ((hgrad.const_mul 2).add hconst) (by
    filter_upwards [hb] with t ht
    have hsquare := (sq_le_sq₀ (norm_nonneg (torusHkValueCLM (slice t))) hM).mpr ht
    exact (cellShiftedGradient_point_energy_le θ q hθ (slice t)).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hsquare (by positivity))))
  rw [intervalIntegral.integral_add (hgrad.const_mul 2) hconst,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at he
  simpa only [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using he

end AVRegularity.CycleEvolution
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set
namespace AVRegularity.CycleEvolution

/-! The finite-time Cauchy--Schwarz estimate used by the forced scalar mean. -/

theorem cellTime_integral_norm_le_sqrt {E : Type*} [NormedAddCommGroup E]
    {a b : ℝ} (hab : a ≤ b) (f : ℝ → E)
    (hf : MemLp f 2 (volume.restrict (Icc a b))) :
    (∫ t in a..b, ‖f t‖) ≤ Real.sqrt (b - a) * Real.sqrt (∫ t in a..b, ‖f t‖ ^ 2) := by
  have hfn : MemLp (fun t => ‖f t‖) (ENNReal.ofReal 2) (volume.restrict (Icc a b)) := by
    simpa using hf.norm
  have hc : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal 2) (volume.restrict (Icc a b)) :=
    memLp_const 1
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hfn hc
  simp only [Real.norm_eq_abs, abs_norm, norm_one, mul_one, Real.rpow_two,
    one_pow, integral_const, smul_eq_mul, mul_one, ← Real.sqrt_eq_rpow] at h
  rw [Measure.real, Measure.restrict_apply_univ, Real.volume_Icc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab)] at h
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  simpa only [mul_comm] using h

end AVRegularity.CycleEvolution
end
end
