-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.CellGalerkinConstant
public import AVRegularity.Weighted.WeightedZeroCarrier
import AVRegularity.CycleJoint.WeightedGradientLiftComparison
import Mathlib.Algebra.Order.Star.Real
import Mathlib.CategoryTheory.Countable

section
@[expose] public noncomputable section

section
open Homogenization MeasureTheory UnitAddTorus AVRegularity.CycleEvolution
open scoped Classical
namespace AVRegularity.CycleWords

/-! The native transverse projection fixes constants and preserves the actual cell mean. -/

local instance cellTransverseMeanCommutationMeasure : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

theorem scalarTorusToCell_zero_mode :
    scalarTorusToCell (mFourierBasis (d := Fin 2) 0) = cellConstantCLM 1 := by
  apply Lp.ext
  have hb : (mFourierBasis (d := Fin 2) 0 : ScalarTorusL2) =ᵐ[volume] fun _ => 1 := by
    rw [coe_mFourierBasis]
    have hh := coeFn_mFourierLp 2 (0 : Fin 2 → ℤ)
    filter_upwards [hh] with y hy
    rw [hy, mFourier_zero]
    rfl
  filter_upwards [scalarTorusToCell_ae (mFourierBasis (d := Fin 2) 0),
    scalarTorusQuotient_measurePreserving.quasiMeasurePreserving.ae hb,
    cellConstantCLM_ae 1] with x hx hb' hc
  exact hx.trans (hb'.trans hc.symm)

theorem cellTransverseProjection_one (e : Fin 2) :
    cellTransverseProjection e (cellConstantCLM 1) = cellConstantCLM 1 := by
  rw [← scalarTorusToCell_zero_mode, cellTransverseProjection_torus]
  congr 1
  change hilbertBasisSectorProjection (mFourierBasis (d := Fin 2)) {n | n e = 0}
    (mFourierBasis (d := Fin 2) 0) = _
  rw [hilbertBasisSectorProjection_basis]
  simp only [Set.mem_ofPred_eq, Pi.zero_apply, ite_eq_left]

end AVRegularity.CycleWords
end

section
open MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Every retained Fourier cutoff preserves the literal complex cell mean. -/

theorem cellScalarCLM_constant_one (c : ℂ) :
    cellScalarCLM c (cellConstantCLM 1) = cellConstantCLM c := by
  apply Lp.ext
  filter_upwards [cellScalarCLM_ae c (cellConstantCLM 1), cellConstantCLM_ae 1,
    cellConstantCLM_ae c] with x hs h1 hc
  rw [hs, h1, mul_one, hc]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The actual finite initial correction is contractive in the original L2 datum. -/

theorem cellGalerkinL2Initial_sub_constant (N : ℕ) (u : ComplexCellL2) (c : ℂ) :
    cellGalerkinL2Initial N u - cellGalerkinConstant N c =
      cellGalerkinL2Initial N (u - cellConstantCLM c) := by
  have h := (cellGalerkinL2InitialCLM N).map_sub u (cellConstantCLM c)
  simp only [cellGalerkinL2InitialCLM_apply] at h
  exact h.symm

theorem cellGalerkin_initial_correction_norm_le {a b : ℝ} (hab : a ≤ b) (N : ℕ)
    (A : ℝ → CellGalerkinSpace (E := ℂ) N →L[ℝ] CellGalerkinSpace (E := ℂ) N)
    (f y : ℝ → CellGalerkinSpace (E := ℂ) N) (u : ComplexCellL2)
    (hy : AVenhance.Infra.ODE.IsLinearIntegralSolution A f (cellGalerkinL2Initial N u) a b y) :
    ‖cellGalerkinValue N (y a - cellGalerkinConstant N 1)‖ ≤ ‖u - cellConstantCLM 1‖ := by
  have hi : y a = cellGalerkinL2Initial N u := by
    simpa only [intervalIntegral.integral_same, add_zero] using hy a ⟨le_rfl, hab⟩
  have he := (congrArg (fun z : CellGalerkinSpace (E := ℂ) N => z - cellGalerkinConstant N 1) hi).trans
    (cellGalerkinL2Initial_sub_constant N u 1)
  exact (congrArg (fun z : CellGalerkinSpace (E := ℂ) N => ‖cellGalerkinValue N z‖) he).le.trans
    (cellGalerkinL2Initial_norm_le N (u - cellConstantCLM 1))

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory UnitAddTorus AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The physical Bloch derivative has exactly the plane Fourier frequency multiplier. -/

local instance cellH1PhysicalBlochFourierMeasure : MeasureSpace UnitAddCircle := instMeasureSpaceUnitAddCircle

theorem scalarCellToTorus_fourierCoeff_add (u v : ComplexCellL2) (n : Fin 2 → ℤ) :
    mFourierCoeff (scalarCellToTorus (u + v)) n =
      mFourierCoeff (scalarCellToTorus u) n + mFourierCoeff (scalarCellToTorus v) n := by
  simp only [scalarCellToTorus_fourierCoeff_pair, cellComplexPair_add_left]

theorem scalarCellToTorus_fourierCoeff_scalar (c : ℂ) (u : ComplexCellL2) (n : Fin 2 → ℤ) :
    mFourierCoeff (scalarCellToTorus (cellScalarCLM c u)) n =
      c * mFourierCoeff (scalarCellToTorus u) n := by
  simp only [scalarCellToTorus_fourierCoeff_pair, cellComplexPair_scalar_left]

theorem cellH1_physicalBlochFourier (u : TorusHk 1 ℂ) (θ : Vec 2)
    (i : Fin 2) (n : Fin 2 → ℤ) :
    mFourierCoeff (scalarCellToTorus (cellShiftedDerivativeCLM (planePhysicalBlochShift θ) i u)) n =
      (2 * (Real.pi : ℂ) * Complex.I) * (((n i : ℝ) + θ i : ℝ) : ℂ) *
        mFourierCoeff (scalarCellToTorus (torusHkValueCLM u)) n := by
  change mFourierCoeff (scalarCellToTorus (cellDerivativeCLM i u +
    cellScalarCLM (Complex.I * planePhysicalBlochShift θ i) (torusHkValueCLM u))) n = _
  rw [scalarCellToTorus_fourierCoeff_add, scalarCellToTorus_fourierCoeff_scalar,
    cellH1_fourierDerivative]
  dsimp only [planePhysicalBlochShift]
  push_cast
  ring

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! The native factorial energy is the integral of its finite word density. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def planeFactorialDensity {K : ℕ} (r : ℝ) (U : PlaneHk Set.univ K E) (z : Vec 2) : ℝ :=
  ∑ a : JetIndex2 K, factorialWeight r a.1.val * ‖planeJetOrder U a.1.val a.2 z‖ ^ 2

theorem planeFactorialDensity_nonneg {K : ℕ} (r : ℝ) (U : PlaneHk Set.univ K E) (z : Vec 2) :
    0 ≤ planeFactorialDensity r U z :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (factorialWeight_nonneg _ _) (sq_nonneg _))

theorem planeFactorialDensity_term_le {K j : ℕ} (hj : j ≤ K) (r : ℝ)
    (U : PlaneHk Set.univ K E) (w : DerivativeWord2 j) (z : Vec 2) :
    factorialWeight r j * ‖planeJetOrder U j w z‖ ^ 2 ≤ planeFactorialDensity r U z := by
  unfold planeFactorialDensity
  exact Finset.single_le_sum
    (f := fun a : JetIndex2 K => factorialWeight r a.1.val * ‖planeJetOrder U a.1.val a.2 z‖ ^ 2)
    (fun a _ => mul_nonneg (factorialWeight_nonneg r a.1.val) (sq_nonneg _))
    (Finset.mem_univ (⟨⟨j, Nat.lt_succ_of_le hj⟩, w⟩ : JetIndex2 K))

theorem storedChartFactorialEnergy_density {K : ℕ} (r : ℝ) (q : Vec 2 → ℝ)
    (hq : AEMeasurable q volume) (hq0 : ∀ z, 0 ≤ q z) (U : PlaneHk Set.univ K E) :
    Weighted.storedChartFactorialEnergy r q U =
      ∫⁻ z, ENNReal.ofReal (q z * planeFactorialDensity r U z) := by
  unfold planeFactorialDensity
  simp_rw [Finset.mul_sum]
  rw [show (fun z => ENNReal.ofReal (∑ a : JetIndex2 K,
      q z * (factorialWeight r a.1.val * ‖planeJetOrder U a.1.val a.2 z‖ ^ 2))) =
      (fun z => ∑ a : JetIndex2 K, ENNReal.ofReal
        (q z * (factorialWeight r a.1.val * ‖planeJetOrder U a.1.val a.2 z‖ ^ 2))) by
    funext z
    exact ENNReal.ofReal_sum_of_nonneg (fun a _ =>
      mul_nonneg (hq0 z) (mul_nonneg (factorialWeight_nonneg _ _) (sq_nonneg _)))]
  rw [lintegral_finsetSum' _ (fun a _ =>
    (hq.mul (aemeasurable_const.mul
      ((planeJetOrder_memLp (Nat.le_of_lt_succ a.1.isLt) U a.2).aestronglyMeasurable.norm.aemeasurable.pow_const 2))).ennreal_ofReal)]
  unfold Weighted.storedChartFactorialEnergy
  apply Finset.sum_congr rfl
  intro a _
  rw [show (fun z => ENNReal.ofReal (q z * (factorialWeight r a.1.val *
      ‖planeJetOrder U a.1.val a.2 z‖ ^ 2))) =
      (fun z => ENNReal.ofReal (factorialWeight r a.1.val) *
        ENNReal.ofReal (q z * ‖planeJetOrder U a.1.val a.2 z‖ ^ 2)) by
    funext z
    rw [mul_left_comm, ENNReal.ofReal_mul (factorialWeight_nonneg _ _)]]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  unfold Weighted.chartScalarEnergy
  apply lintegral_congr_ae
  filter_upwards [planeJetLpReadout_ae (Nat.le_of_lt_succ a.1.isLt) U a.2] with z hz
  rw [hz]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Filter AVRegularity.Sobolev
open scoped Topology
namespace AVRegularity.CycleWords

/-! Weighted jets of the actual compact cutoff carriers converge to the supplied native input jets. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem expandingCutoff_weighted_native_jet_limit {K : ℕ}
    (U : PlaneHk Set.univ K E) (q : Vec 2 → ℝ)
    (hw : JetMemL2On Set.univ (fun b x => q x • U.toFunction.jet b x))
    (A : Fin (K + 1) → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ n l x, ‖coefficientDerivativeArray (expandingPlaneCoefficient (E := E) n)
      l.val x‖ ≤ A l)
    (hb0 : ∀ l x, ‖coefficientDerivativeArray
      (fun _ : Vec 2 => ContinuousLinearMap.id ℝ E) l.val x‖ ≤ A l) (a : JetIndex2 K) :
    Tendsto (fun n => (weighted_multiplicationRawJet_memLp
      (expandingPlaneCoefficient (E := E) n)
      ((expandingPlaneCoefficient_contDiff n).of_le (by simp)) U.toFunction.jet q hw A (hb n) a).toLp
        (fun x => q x • multiplicationRawJet (expandingPlaneCoefficient (E := E) n)
          U.toFunction.jet a x)) atTop
      (𝓝 ((hw a).toLp (fun x => q x • U.toFunction.jet a x))) := by
  have ht := expandingPlaneCoefficient_weighted_raw_tendsto U.toFunction.jet q hw A hA hb hb0 a
  have hae := (identityCoefficient_rawJet_ae U A hb0 a).mono
    (fun x hx => congrArg (fun e : E => q x • e) hx)
  have he := MemLp.toLp_congr
    (weighted_multiplicationRawJet_memLp (fun _ : Vec 2 => ContinuousLinearMap.id ℝ E)
      contDiff_const U.toFunction.jet q hw A hb0 a) (hw a) hae
  rw [he] at ht
  exact ht

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Native zero has zero value and zero factorial density almost everywhere. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeJetOrder_zero_ae {K j : ℕ} (hj : j ≤ K) (w : DerivativeWord2 j) :
    planeJetOrder (0 : PlaneHk Set.univ K E) j w =ᵐ[volume] (fun _ => 0) := by
  have hh := (planeJetLpReadout_ae hj (0 : PlaneHk Set.univ K E) w).symm
  rw [map_zero] at hh
  exact hh.trans (Lp.coeFn_zero E 2 volume)

theorem planeValue_zero_ae (K : ℕ) :
    planeValue (0 : PlaneHk Set.univ K E) =ᵐ[volume] (fun _ => 0) :=
  planeJetOrder_zero_ae (Nat.zero_le K) (fun i => Fin.elim0 i)

theorem planeFactorialDensity_zero_ae (K : ℕ) (ρ : ℝ) :
    planeFactorialDensity ρ (0 : PlaneHk Set.univ K E) =ᵐ[volume] (fun _ => 0) := by
  have hh : ∀ᵐ x ∂volume, ∀ a : JetIndex2 K,
      planeJetOrder (0 : PlaneHk Set.univ K E) a.1.val a.2 x = 0 :=
    ae_all_iff.mpr (fun a => planeJetOrder_zero_ae (Nat.le_of_lt_succ a.1.isLt) a.2)
  filter_upwards [hh] with x hx
  simp only [planeFactorialDensity, hx, norm_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero, Finset.sum_const_zero]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory UnitAddTorus AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVenhance.Infra.Torus
namespace AVRegularity.CycleWords

/-! Original periodic transverse coefficients commute with the actual cell projection. -/

local instance cellTransverseCoefficientCommutationMeasure : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

theorem cellCoefficientCLM_periodic_torus
    (c : Vec 2 → ℂ) (hc : Measurable c) (hp : IsZdPeriodic c)
    (hm : AEStronglyMeasurable c (volume.restrict AVenhance.unitCube))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, ‖c x‖ ≤ C) (u : ScalarTorusL2) :
    cellCoefficientCLM c hm C hC hb (scalarTorusToCell u) =
      scalarTorusToCell (measurableTorusSymbolMultiplication (periodicToTorus c)
        (hc.comp (measurable_unitTorusRepresentative 2)) C (fun z => hb (unitTorusRepresentative 2 z)) u) := by
  have he := scalarTorusToCell_measurable_multiplier (periodicToTorus c)
    (hc.comp (measurable_unitTorusRepresentative 2)) C hC (fun z => hb (unitTorusRepresentative 2 z)) u
  have hpull : (fun x : Vec 2 => periodicToTorus c
      (AVRegularity.Analysis.Convolution.torusQuotient x)) = c :=
    fromUnitTorus_periodicToTorus hp
  simpa only [hpull] using he.symm

theorem cellTransverseProjection_coefficient
    (e : Fin 2) (c : Vec 2 → ℂ) (hc : Measurable c) (hp : IsZdPeriodic c)
    (ht : ∀ (z : Vec 2) (s : ℝ), c (z + s • basisVec e) = c z)
    (hm : AEStronglyMeasurable c (volume.restrict AVenhance.unitCube))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x, ‖c x‖ ≤ C) (u : ComplexCellL2) :
    cellTransverseProjection e (cellCoefficientCLM c hm C hC hb u) =
      cellCoefficientCLM c hm C hC hb (cellTransverseProjection e u) := by
  have hs : ∀ n : Fin 2 → ℤ, n e ≠ 0 → mFourierCoeff (periodicToTorus c) n = 0 := by
    intro n hn
    exact periodicToTorus_parallel_fourier_zero e c hp ht n hn
  have htcomm := scalarTorusTransverseProjection_multiplier_commutes e (periodicToTorus c)
    (hc.comp (measurable_unitTorusRepresentative 2)) C
    (fun z => hb (unitTorusRepresentative 2 z)) hs
  have he := congrArg (fun L : ScalarTorusL2 →L[ℂ] ScalarTorusL2 =>
    L (scalarCellToTorus u)) htcomm
  simp only [ContinuousLinearMap.comp_apply] at he
  have hu : u = scalarTorusToCell (scalarCellToTorus u) :=
    (scalarTorusToCell_scalarCellToTorus u).symm
  conv_lhs => rw [hu]
  rw [cellCoefficientCLM_periodic_torus c hc hp hm C hC hb,
    cellTransverseProjection_torus, cellTransverseProjection_apply,
    cellCoefficientCLM_periodic_torus c hc hp hm C hC hb]
  exact congrArg scalarTorusToCell he

end AVRegularity.CycleWords
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! A support bound on the value controls every stored factorial chart energy. -/

theorem storedChartFactorialEnergy_value_supported_bound {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}
    (ρ : ℝ) (q : Vec 2 → ℝ) (f : PlaneHk Set.univ K E)
    {A : Set (Vec 2)} (hA : IsClosed A)
    (hf : ∀ᵐ x ∂volume, x ∉ A → f.toFunction.jet (valueIndex2 K) x = 0)
    (C : ℝ) (hC : 0 ≤ C) (hq : ∀ x ∈ A, q x ≤ C) :
    storedChartFactorialEnergy ρ q f ≤
      ENNReal.ofReal C * ENNReal.ofReal (factorialNormSq ρ f.val) := by
  exact CycleJointProofs.storedChartFactorialEnergy_supported_bound ρ q f C hC
    (orderedWeakJet_supported_bound f.toFunction.memL2 f.toFunction.hasWeakJet hA hf q C hq)

theorem storedChartFactorialEnergy_value_supported_ne_top {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}
    (ρ : ℝ) (q : Vec 2 → ℝ) (f : PlaneHk Set.univ K E)
    {A : Set (Vec 2)} (hA : IsClosed A)
    (hf : ∀ᵐ x ∂volume, x ∉ A → f.toFunction.jet (valueIndex2 K) x = 0)
    (C : ℝ) (hC : 0 ≤ C) (hq : ∀ x ∈ A, q x ≤ C) :
    storedChartFactorialEnergy ρ q f ≠ ⊤ := by
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    (storedChartFactorialEnergy_value_supported_bound ρ q f hA hf C hC hq)

theorem storedChartFactorialEnergy_compact_value_ne_top {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}
    (ρ : ℝ) (q : Vec 2 → ℝ) (f : PlaneHk Set.univ K E)
    {A : Set (Vec 2)} (hA : IsCompact A)
    (hf : ∀ᵐ x ∂volume, x ∉ A → f.toFunction.jet (valueIndex2 K) x = 0)
    (hq : ContinuousOn q A) : storedChartFactorialEnergy ρ q f ≠ ⊤ := by
  obtain ⟨B, hB⟩ := hA.bddAbove_image hq
  apply storedChartFactorialEnergy_value_supported_ne_top ρ q f hA.isClosed hf
    (max B 0) (le_max_right _ _)
  intro x hx
  exact (hB (Set.mem_image_of_mem q hx)).trans (le_max_left _ _)

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Filter AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution
open scoped Topology
namespace AVRegularity.CycleWords

/-! Actual cutoff native jets converge in the same whole-plane L2 classes used by compact smoothing. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem expandingCutoff_volume_jet_limit {K : ℕ} (U : PlaneHk Set.univ K E)
    (q : Vec 2 → ℝ) (hw : JetMemL2On Set.univ (fun b x => q x • U.toFunction.jet b x))
    (A : Fin (K + 1) → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ n l x, ‖coefficientDerivativeArray (expandingPlaneCoefficient (E := E) n)
      l.val x‖ ≤ A l)
    (hb0 : ∀ l x, ‖coefficientDerivativeArray
      (fun _ : Vec 2 => ContinuousLinearMap.id ℝ E) l.val x‖ ≤ A l)
    (a : JetIndex2 K)
    (hm : ∀ n, MemLp (fun x => q x • (expandingCutoffPlaneHk U n A (hb n)).toFunction.jet a x)
      2 volume) (hU : MemLp (fun x => q x • U.toFunction.jet a x) 2 volume) :
    Tendsto (fun n => (hm n).toLp
      (fun x => q x • (expandingCutoffPlaneHk U n A (hb n)).toFunction.jet a x)) atTop
      (𝓝 (hU.toLp (fun x => q x • U.toFunction.jet a x))) := by
  let hp n := weighted_multiplicationRawJet_memLp (expandingPlaneCoefficient (E := E) n)
    ((expandingPlaneCoefficient_contDiff n).of_le (by simp)) U.toFunction.jet q hw A (hb n) a
  let p n x := q x • multiplicationRawJet (expandingPlaneCoefficient (E := E) n)
    U.toFunction.jet a x
  have ht := expandingCutoff_weighted_native_jet_limit U q hw A hA hb hb0 a
  have he n : univToPlane ((hp n).toLp (p n)) = (hm n).toLp
      (fun x => q x • (expandingCutoffPlaneHk U n A (hb n)).toFunction.jet a x) := by
    apply Lp.ext
    have ha := (hp n).coeFn_toLp
    have hr := expandingCutoffPlaneHk_raw_ae U n A (hb n) a
    simp only [Measure.restrict_univ] at ha hr
    have hq : (fun x => q x • (expandingCutoffPlaneHk U n A (hb n)).toFunction.jet a x)
        =ᵐ[volume] p n := hr.mono (fun x hx => congrArg (fun e : E => q x • e) hx)
    exact (univToPlane_ae ((hp n).toLp (p n))).trans
      (ha.trans (hq.symm.trans (hm n).coeFn_toLp.symm))
  have he0 := univToPlane_toLp_field (fun x => q x • U.toFunction.jet a x) (hw a) hU
  have ht' := (univToPlane.continuous.tendsto
    ((hw a).toLp (fun x => q x • U.toFunction.jet a x))).comp ht
  change Tendsto (fun n => univToPlane ((hp n).toLp (p n))) atTop
    (𝓝 (univToPlane ((hw a).toLp (fun x => q x • U.toFunction.jet a x)))) at ht'
  simpa only [he, he0] using ht'

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVenhance.Infra.Torus
namespace AVRegularity.CycleWords

/-! Merely measurable periodic transverse drift coefficients commute with the native sector projection. -/

theorem cellTransverseProjection_driftEntry
    (C : CellCoefficients) (hv : IsCellDrift C.v) (V : ℝ)
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (e : Fin 2)
    (ht : ∀ (t : ℝ) (z : Vec 2) (s : ℝ), C.v t (z + s • basisVec e) = C.v t z)
    (t : ℝ) (j : Fin 2) (u : ComplexCellL2) :
    cellTransverseProjection e (cellDriftEntryCLM C V hv.1 hb t j u) =
      cellDriftEntryCLM C V hv.1 hb t j (cellTransverseProjection e u) := by
  have hm : Measurable (fun x : Vec 2 => (C.v t x j : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp
      ((measurable_pi_apply j).comp (hv.1.comp (measurable_const.prodMk measurable_id)))
  have hp : IsZdPeriodic (fun x : Vec 2 => (C.v t x j : ℂ)) := by
    apply (isZdPeriodic_iff_frozen _).mpr
    intro n z
    exact congrArg (fun y : Vec 2 => (y j : ℂ)) (hv.2.2.1 t n z)
  have hs : ∀ (z : Vec 2) (s : ℝ), (C.v t (z + s • basisVec e) j : ℂ) =
      (C.v t z j : ℂ) := fun z s => congrArg (fun y : Vec 2 => (y j : ℂ)) (ht t z s)
  unfold cellDriftEntryCLM
  apply cellTransverseProjection_coefficient e _ hm hp hs

theorem shear_drift_parallel_invariant
    (v : ℝ → Vec 2 → Vec 2) (e : Fin 2) (V : ℝ → ℝ → ℝ)
    (hv : ∀ t z, v t z = V t (z e.rev) • basisVec e)
    (t : ℝ) (z : Vec 2) (s : ℝ) : v t (z + s • basisVec e) = v t z := by
  have hz : (z + s • basisVec e) e.rev = z e.rev := by
    fin_cases e <;> simp [basisVec_apply]
  rw [hv, hv, hz]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Literal raw product witnesses retain their factorial density after promotion to the Hilbert graph. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeFactorialDensity_eq_raw {K : ℕ} (ρ : ℝ) (U : PlaneHk Set.univ K E) :
    planeFactorialDensity ρ U = rawFactorialDensity ρ U.toFunction.jet := by
  funext x
  unfold planeFactorialDensity rawFactorialDensity
  apply Finset.sum_congr rfl
  intro a _
  rw [planeJetOrder_eq_stored (Nat.le_of_lt_succ a.1.isLt)]

end AVRegularity.CycleWords
end
end
end

section
section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleWords

/-! The redistributed scalar metric equation has integrable spatial pairings at every time. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeScalarRawRhs_integrable (K : ℕ)
    (v : Vec 2 → Vec 2) (hvc : ∀ k, Continuous (fun x => v x k))
    {Mv : ℝ} (hMv : 0 ≤ Mv) (hvb : ∀ k x, |v x k| ≤ Mv)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hGc : ∀ k j, Continuous (fun x => G x k j))
    {MG : ℝ} (hMG : 0 ≤ MG) (hGb : ∀ k j x, |G x k j| ≤ MG)
    (w : PlaneHk Set.univ (K + 1) E)
    (F : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (φ : PlaneHk Set.univ 1 E) :
    Integrable (planeScalarRawRhs K v G w F φ) volume := by
  let u := truncatePlaneHk (E := E) (show 1 ≤ K + 1 by omega) w
  let T := planeScalarTransport v hvc hMv hvb (planeH1GradientOperator (E := E) u)
  let Q := planeScalarDiffusion G hGc hMG hGb (planeH1GradientOperator (E := E) u) +
    planeFluxValueOperator (E := E) K F
  let z := planeHkValueOperator (E := E) 1 φ
  let dz := planeH1GradientOperator (E := E) φ
  have hi : Integrable (fun x => -inner ℝ (T x) (z x) -
      ∑ k : Fin 2, inner ℝ (Q k x) (dz k x)) volume :=
    (L2.integrable_inner T z).neg.sub
      (integrable_finsetSum Finset.univ (fun k _ => L2.integrable_inner (Q k) (dz k)))
  have hw : ∀ᵐ x ∂volume, ∀ k : Fin 2,
      planeH1GradientOperator (E := E) u k x =
        w.toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩ x :=
    ae_all_iff.mpr (fun _ => univToPlane_ae _)
  have hφ : ∀ᵐ x ∂volume, ∀ k : Fin 2, planeH1GradientOperator (E := E) φ k x =
      φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩ x :=
    ae_all_iff.mpr (fun _ => univToPlane_ae _)
  have hF : ∀ᵐ x ∂volume, ∀ k : Fin 2,
      planeFluxValueOperator (E := E) K F k x = F.toFunction.jet (valueIndex2 K) x k :=
    ae_all_iff.mpr (fun k => planeFluxValueOperator_ae K F k)
  have hzero : (0 : PlaneHk Set.univ K E).toFunction.jet (valueIndex2 K) =ᵐ[volume]
      fun _ => 0 := by
    change (fun x => ((0 : JetL2 (volume.restrict Set.univ) K E) (valueIndex2 K)) x) =ᵐ[volume] _
    simp only [PiLp.zero_apply]
    have hz := Lp.coeFn_zero E 2 (volume.restrict (Set.univ : Set (Vec 2)))
    change (∀ᵐ x ∂volume.restrict (Set.univ : Set (Vec 2)),
      (0 : Lp E 2 (volume.restrict Set.univ)) x = 0) at hz
    rw [ae_restrict_iff' MeasurableSet.univ] at hz
    filter_upwards [hz] with x hx
    exact hx (Set.mem_univ x)
  have ht := planeScalarTransport_ae v hvc hMv hvb (planeH1GradientOperator (E := E) u)
  have hd : ∀ᵐ x ∂volume, ∀ k : Fin 2,
      Q k x = (∑ j : Fin 2, G x k j • planeH1GradientOperator (E := E) u j x) +
        planeFluxValueOperator (E := E) K F k x := by
    apply ae_all_iff.mpr
    intro k
    filter_upwards [Lp.coeFn_add
      (planeScalarDiffusion G hGc hMG hGb (planeH1GradientOperator (E := E) u) k)
        (planeFluxValueOperator (E := E) K F k),
      planeScalarDiffusion_ae G hGc hMG hGb (planeH1GradientOperator (E := E) u) k]
      with x ha hm
    exact ha.trans (congrArg (fun q => q + planeFluxValueOperator (E := E) K F k x) hm)
  apply hi.congr
  filter_upwards [ht, hd, hw, hφ, hF, hzero, univToPlane_ae (φ.val (valueIndex2 1))]
    with x htx hdx hwx hφx hFx hzx hvx
  dsimp only [T, z, dz]
  rw [htx]
  simp only [sum_inner, real_inner_smul_left]
  simp_rw [hdx, hwx, hφx, hFx]
  simp only [planeHkValueOperator_apply, hvx, planeScalarRawRhs, hzx, inner_zero_left, add_zero]
  have ha := metricDeviation_weak_pairing (G x)
    (fun k => w.toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩ x)
    (fun k => φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩ x)
    (fun k => F.toFunction.jet (valueIndex2 K) x k)
  simp only [PlaneHk.toFunction, planeJetRepresentative] at ha ⊢
  linarith [ha]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Any genuine Sobolev carrier with the literal product jets satisfies the normalized density bound. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

theorem productReadout_density_le {K : ℕ} (U : PlaneHk Set.univ K E) (V : PlaneHk Set.univ K F)
    (C : Vec 2 → E →L[ℝ] F) (ρ A : ℝ) (hρ : 0 ≤ ρ) (q : Vec 2 → ℝ)
    (hb : ∀ l ≤ K, ∀ w : DerivativeWord2 l, ∀ x,
      ρ ^ l * ‖orderedCoefficientDerivative C l w x‖ ≤ A * q x)
    (hr : ∀ a, Weighted.planeJetReadoutOperator K a V =ᵐ[volume]
      multiplicationRawJet C U.toFunction.jet a) :
    ∀ᵐ x ∂volume, planeFactorialDensity ρ V x ≤
      multiplicationDensityBudget K * A ^ 2 * q x ^ 2 * planeFactorialDensity ρ U x := by
  have hh : ∀ᵐ x ∂volume, ∀ a : JetIndex2 K,
      planeJetOrder V a.1.val a.2 x = multiplicationRawJet C U.toFunction.jet a x := by
    apply ae_all_iff.mpr
    intro a
    exact (planeJetLpReadout_ae (Nat.le_of_lt_succ a.1.isLt) V a.2).symm.trans (hr a)
  filter_upwards [hh] with x hx
  have he : planeFactorialDensity ρ V x = rawFactorialDensity ρ (multiplicationRawJet C U.toFunction.jet) x := by
    unfold planeFactorialDensity rawFactorialDensity
    apply Finset.sum_congr rfl
    intro a _
    rw [hx a]
  rw [he, planeFactorialDensity_eq_raw]
  exact multiplicationRawJet_density_le C U.toFunction.jet hρ x (fun l hl w => hb l hl w x)

end AVRegularity.CycleWords
end
end

section
public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Higher Bloch derivative readouts and genuine periodic bilinear transposition. -/

theorem torusHigher_truncate_value {K L : ℕ} (h : K ≤ L) (U : TorusHk L ℂ) :
    torusHkValueCLM (truncateTorusHk h U) = torusHkValueCLM U := by
  change U.val (truncateJetIndex h (valueIndex2 K)) = U.val (valueIndex2 L)
  have hi : truncateJetIndex h (valueIndex2 K) = valueIndex2 L := rfl
  rw [hi]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Native finite flux sums retain the Hilbert factorial triangle estimate almost everywhere. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeJetOrder_finite_sum_ae {K j : ℕ} (hj : j ≤ K)
    {ι : Type*} [Fintype ι] (V : ι → PlaneHk Set.univ K E) (w : DerivativeWord2 j) :
    planeJetOrder (∑ i, V i) j w =ᵐ[volume] (fun x => ∑ i, planeJetOrder (V i) j w x) := by
  classical
  let a : JetIndex2 K := ⟨⟨j, Nat.lt_succ_of_le hj⟩, w⟩
  have hh : Weighted.planeJetReadoutOperator K a (∑ i, V i) =ᵐ[volume]
      (fun x => ∑ i, Weighted.planeJetReadoutOperator K a (V i) x) := by
    rw [map_sum]
    filter_upwards [Lp.coeFn_finsetSum Finset.univ
      (fun i => Weighted.planeJetReadoutOperator K a (V i))] with x hx
    simpa only [Finset.sum_apply] using hx
  have he : (fun x => ∑ i, Weighted.planeJetReadoutOperator K a (V i) x) =ᵐ[volume]
      (fun x => ∑ i, planeJetOrder (V i) j w x) := by
    have hall : ∀ᵐ x ∂volume, ∀ i, Weighted.planeJetReadoutOperator K a (V i) x =
        planeJetOrder (V i) j w x := ae_all_iff.mpr (fun i => planeJetLpReadout_ae hj (V i) w)
    filter_upwards [hall] with x hx
    exact Finset.sum_congr rfl (fun i _ => hx i)
  exact (planeJetLpReadout_ae hj (∑ i, V i) w).symm.trans (hh.trans he)

theorem nativeFactorialDensity_sum_price_le {K : ℕ} {ι : Type*} [Fintype ι]
    (ρ : ℝ) (V : ι → PlaneHk Set.univ K E) (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (B : Vec 2 → ℝ) (hB : ∀ x, 0 ≤ B x)
    (hb : ∀ i, ∀ᵐ x ∂volume, planeFactorialDensity ρ (V i) x ≤ (p i) ^ 2 * B x) :
    ∀ᵐ x ∂volume, planeFactorialDensity ρ (∑ i, V i) x ≤ (∑ i, p i) ^ 2 * B x := by
  have hsum : ∀ᵐ x ∂volume, ∀ a : JetIndex2 K,
      planeJetOrder (∑ i, V i) a.1.val a.2 x = ∑ i, planeJetOrder (V i) a.1.val a.2 x :=
    ae_all_iff.mpr (fun a => planeJetOrder_finite_sum_ae (Nat.le_of_lt_succ a.1.isLt) V a.2)
  have hterms : ∀ᵐ x ∂volume, ∀ i, planeFactorialDensity ρ (V i) x ≤ (p i) ^ 2 * B x :=
    ae_all_iff.mpr hb
  filter_upwards [hsum, hterms] with x hx ht
  let D := fun i (a : JetIndex2 K) (z : Vec 2) => planeJetOrder (V i) a.1.val a.2 z
  have hd (i : ι) : rawFactorialDensity ρ (D i) x = planeFactorialDensity ρ (V i) x := rfl
  have hh := rawFactorialDensity_sum_price_le ρ D x p hp (B x) (hB x)
    (fun i => by rw [hd]; exact ht i)
  have he : planeFactorialDensity ρ (∑ i, V i) x =
      rawFactorialDensity ρ (fun a z => ∑ i, D i a z) x := by
    unfold planeFactorialDensity rawFactorialDensity
    apply Finset.sum_congr rfl
    intro a _
    rw [hx a]
  rwa [← he] at hh

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Weighted factorial energy follows from literal normalized product readouts. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

theorem productReadout_energy_le {K : ℕ} (U : PlaneHk Set.univ K E) (V : PlaneHk Set.univ K F)
    (C : Vec 2 → E →L[ℝ] F) (ρ A : ℝ) (hρ : 0 ≤ ρ)
    (q : Vec 2 → ℝ) (hqm : AEMeasurable q volume)
    (hb : ∀ l ≤ K, ∀ w : DerivativeWord2 l, ∀ x,
      ρ ^ l * ‖orderedCoefficientDerivative C l w x‖ ≤ A * q x)
    (hr : ∀ a, Weighted.planeJetReadoutOperator K a V =ᵐ[volume]
      multiplicationRawJet C U.toFunction.jet a)
    (W : Vec 2 → ℝ) (hW : AEMeasurable W volume) (hW0 : ∀ x, 0 ≤ W x) :
    Weighted.storedChartFactorialEnergy ρ W V ≤
      ENNReal.ofReal (multiplicationDensityBudget K * A ^ 2) *
        Weighted.storedChartFactorialEnergy ρ (fun x => W x * q x ^ 2) U := by
  rw [storedChartFactorialEnergy_density ρ W hW hW0,
    storedChartFactorialEnergy_density ρ (fun x => W x * q x ^ 2)
      (by exact hW.mul (hqm.pow_const 2))
      (fun x => mul_nonneg (hW0 x) (sq_nonneg (q x)))]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [productReadout_density_le U V C ρ A hρ q hb hr] with x hx
  rw [← ENNReal.ofReal_mul (mul_nonneg (multiplicationDensityBudget_nonneg K) (sq_nonneg A))]
  apply ENNReal.ofReal_le_ofReal
  have hh := mul_le_mul_of_nonneg_left hx (hW0 x)
  convert hh using 1; ring

end AVRegularity.CycleWords
end
end

section
public noncomputable section
open AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Bloch derivative and Sobolev truncation commute on the original native states. -/

theorem torusHigher_truncate_comp {K L J : ℕ} (hKL : K ≤ L) (hLJ : L ≤ J)
    (U : TorusHk J ℂ) :
    truncateTorusHk hKL (truncateTorusHk hLJ U) = truncateTorusHk (hKL.trans hLJ) U := by
  apply TorusHk.ext_value
  change torusHkValueCLM (truncateTorusHk hKL (truncateTorusHk hLJ U)) =
    torusHkValueCLM (truncateTorusHk (hKL.trans hLJ) U)
  rw [torusHigher_truncate_value, torusHigher_truncate_value, torusHigher_truncate_value]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleWords

/-! The native transverse projection commutes with the full measurable-time cell equation. -/

theorem cellTransverseH1Projection_generatorForm
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (θ : Fin 2 → ℂ) (κ : ℝ → ℂ)
    (hv : IsCellDrift v) (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (e : Fin 2) (ht : ∀ (t : ℝ) (z : Vec 2) (s : ℝ), v t (z + s • basisVec e) = v t z)
    (t : ℝ) (u z : TorusHk 1 ℂ) :
    cellGeneratorForm ⟨fun t _ => G t, v, θ, κ⟩ hG V hv.1 hb t
      (cellTransverseH1Projection e u) z =
    cellGeneratorForm ⟨fun t _ => G t, v, θ, κ⟩ hG V hv.1 hb t
      u (cellTransverseH1Projection e z) := by
  let C : CellCoefficients := ⟨fun t _ => G t, v, θ, κ⟩
  have hd (j : Fin 2) :
      inner ℝ (cellDriftEntryCLM C V hv.1 hb t j
        (cellShiftedDerivativeCLM θ j (cellTransverseH1Projection e u)))
        (torusHkValueCLM z) =
      inner ℝ (cellDriftEntryCLM C V hv.1 hb t j (cellShiftedDerivativeCLM θ j u))
        (torusHkValueCLM (cellTransverseH1Projection e z)) := by
    rw [cellTransverseH1Projection_shifted_derivative,
      ← cellTransverseProjection_driftEntry C hv V hb e ht,
      cellTransverseProjection_inner]
    exact congrArg (inner ℝ (cellDriftEntryCLM C V hv.1 hb t j
      (cellShiftedDerivativeCLM θ j u))) (cellTransverseH1Projection_value e z).symm
  have hp :
      inner ℝ (cellScalarCLM (κ t) (torusHkValueCLM (cellTransverseH1Projection e u)))
        (torusHkValueCLM z) =
      inner ℝ (cellScalarCLM (κ t) (torusHkValueCLM u))
        (torusHkValueCLM (cellTransverseH1Projection e z)) := by
    rw [cellTransverseH1Projection_value, ← cellTransverseProjection_scalar,
      cellTransverseProjection_inner]
    exact congrArg (inner ℝ (cellScalarCLM (κ t) (torusHkValueCLM u)))
      (cellTransverseH1Projection_value e z).symm
  simp only [cellGeneratorForm, add_apply, sub_apply, sum_apply, pullbackInnerCLM_apply,
    ContinuousLinearMap.comp_apply]
  rw [cellTransverseH1Projection_diffusionForm, hp]
  congr 2
  exact Finset.sum_congr rfl (fun j _ => hd j)

theorem cellTransverseProjection_sourceFunctional
    (θ : Fin 2 → ℂ) (src : ComplexCellL2) (F : Fin 2 → ComplexCellL2)
    (e : Fin 2) (z : TorusHk 1 ℂ) :
    cellSourceFunctional θ (cellTransverseProjection e src)
      (fun j => cellTransverseProjection e (F j)) z =
    cellSourceFunctional θ src F (cellTransverseH1Projection e z) := by
  simp only [cellSourceFunctional, sub_apply, sum_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply]
  rw [cellTransverseProjection_inner, cellTransverseH1Projection_value]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [cellTransverseProjection_inner, cellTransverseH1Projection_shifted_derivative]

theorem cellTransverseH1Projection_dualDerivative
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (θ : Fin 2 → ℂ) (κ : ℝ → ℂ)
    (hv : IsCellDrift v) (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (e : Fin 2) (ht : ∀ (t : ℝ) (z : Vec 2) (s : ℝ), v t (z + s • basisVec e) = v t z)
    (t : ℝ) (u : TorusHk 1 ℂ) (src : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    cellTransverseH1Projection e
      (cellDualDerivative ⟨fun t _ => G t, v, θ, κ⟩ hG V hv.1 hb t u src F) =
    cellDualDerivative ⟨fun t _ => G t, v, θ, κ⟩ hG V hv.1 hb t
      (cellTransverseH1Projection e u) (cellTransverseProjection e src)
      (fun j => cellTransverseProjection e (F j)) := by
  apply ext_inner_right ℝ
  intro z
  rw [cellTransverseH1Projection_inner, cellDualDerivative_pairing,
    cellDualDerivative_pairing, cellTransverseH1Projection_generatorForm _ hG v θ κ hv V hb e ht,
    cellTransverseProjection_sourceFunctional]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Finite native flux sums retain the triangle bound with a separate source density for each term. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem nativeFactorialDensity_sum_variable_price_le {K : ℕ} {ι : Type*} [Fintype ι]
    (ρ : ℝ) (V : ι → PlaneHk Set.univ K E) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (B : ι → Vec 2 → ℝ) (hB : ∀ i x, 0 ≤ B i x)
    (hb : ∀ i, ∀ᵐ x ∂volume, planeFactorialDensity ρ (V i) x ≤ (p i) ^ 2 * B i x) :
    ∀ᵐ x ∂volume, planeFactorialDensity ρ (∑ i, V i) x ≤
      (∑ i, p i * Real.sqrt (B i x)) ^ 2 := by
  classical
  have hsum : ∀ᵐ x ∂volume, ∀ a : JetIndex2 K,
      planeJetOrder (∑ i, V i) a.1.val a.2 x = ∑ i, planeJetOrder (V i) a.1.val a.2 x :=
    ae_all_iff.mpr (fun a => planeJetOrder_finite_sum_ae (Nat.le_of_lt_succ a.1.isLt) V a.2)
  filter_upwards [hsum, ae_all_iff.mpr hb] with x hx ht
  let D := fun i (a : JetIndex2 K) z => planeJetOrder (V i) a.1.val a.2 z
  have hd (i : ι) : rawFactorialDensity ρ (D i) x = planeFactorialDensity ρ (V i) x := rfl
  have hh := rawFactorialDensity_sum_price_le ρ D x (fun i => p i * Real.sqrt (B i x))
    (fun i => mul_nonneg (hp i) (Real.sqrt_nonneg _)) 1 zero_le_one
    (fun i => by rw [hd, mul_one, mul_pow, Real.sq_sqrt (hB i x)]; exact ht i)
  have he : planeFactorialDensity ρ (∑ i, V i) x =
      rawFactorialDensity ρ (fun a z => ∑ i, D i a z) x := by
    unfold planeFactorialDensity rawFactorialDensity
    apply Finset.sum_congr rfl
    intro a _
    rw [hx a]
  simpa only [← he, mul_one] using hh
end

/-! The native factorial triangle inequality and the mass Schur estimate combine without a vertex count. -/

section
variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ v, NormedAddCommGroup (E v)] [∀ v, InnerProductSpace ℝ (E v)]
  [∀ v, MeasurableSpace (E v)] [∀ v, BorelSpace (E v)] [∀ v, CompleteSpace (E v)]

theorem nativeFluxGraph_density_budget (K : ι → ℕ) (ρ : ℝ)
    (V : ∀ v, ι → PlaneHk Set.univ (K v) (E v))
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (p : ι → ι → ℝ)
    (hp : ∀ v u, 0 ≤ p v u) (θ : ℝ) (hθ : 0 ≤ θ)
    (hrow : ∀ v, ∑ u, Real.sqrt (π u / π v) * p v u ≤ θ)
    (hcol : ∀ u, ∑ v, Real.sqrt (π u / π v) * p v u ≤ θ)
    (G : ι → Vec 2 → ℝ) (hG : ∀ u x, 0 ≤ G u x)
    (hb : ∀ v u, ∀ᵐ x ∂volume,
      planeFactorialDensity ρ (V v u) x ≤ (p v u) ^ 2 * G u x) :
    ∀ᵐ x ∂volume, (∑ v, (π v)⁻¹ * planeFactorialDensity ρ (∑ u, V v u) x) ≤
      θ ^ 2 * ∑ u, (π u)⁻¹ * G u x := by
  classical
  have hall : ∀ᵐ x ∂volume, ∀ v,
      planeFactorialDensity ρ (∑ u, V v u) x ≤
        (∑ u, p v u * Real.sqrt (G u x)) ^ 2 := by
    apply ae_all_iff.mpr
    intro v
    have hh : ∀ᵐ x ∂volume, ∀ u,
        planeFactorialDensity ρ (V v u) x ≤ (p v u * Real.sqrt (G u x)) ^ 2 := by
      filter_upwards [ae_all_iff.mpr (hb v)] with x hx u
      simpa only [mul_pow, Real.sq_sqrt (hG u x)] using hx u
    have hs : ∀ᵐ x ∂volume, planeFactorialDensity ρ (∑ u, V v u) x ≤
        (∑ u, p v u * Real.sqrt (G u x)) ^ 2 := by
      -- Freeze the common spatial point after all native readouts have been selected.
      have hsum : ∀ᵐ x ∂volume, ∀ a : JetIndex2 (K v),
          planeJetOrder (∑ u, V v u) a.1.val a.2 x =
            ∑ u, planeJetOrder (V v u) a.1.val a.2 x :=
        ae_all_iff.mpr (fun a => planeJetOrder_finite_sum_ae (Nat.le_of_lt_succ a.1.isLt) (V v) a.2)
      filter_upwards [hh, hsum] with x hx hxs
      let D := fun u (a : JetIndex2 (K v)) z => planeJetOrder (V v u) a.1.val a.2 z
      have ht := rawFactorialDensity_sum_price_le ρ D x
        (fun u => p v u * Real.sqrt (G u x))
        (fun u => mul_nonneg (hp v u) (Real.sqrt_nonneg _)) 1 zero_le_one
        (fun u => by
          have he : rawFactorialDensity ρ (D u) x = planeFactorialDensity ρ (V v u) x := rfl
          rw [he, mul_one]
          exact hx u)
      have he : planeFactorialDensity ρ (∑ u, V v u) x =
          rawFactorialDensity ρ (fun a z => ∑ u, D u a z) x := by
        unfold planeFactorialDensity rawFactorialDensity
        apply Finset.sum_congr rfl
        intro a _
        rw [hxs a]
      simpa only [← he, mul_one] using ht
    exact hs
  filter_upwards [hall] with x hx
  have hnon (v : ι) : 0 ≤ planeFactorialDensity ρ (∑ u, V v u) x :=
    Finset.sum_nonneg (fun a _ => mul_nonneg (factorialWeight_nonneg ρ _) (sq_nonneg _))
  have hf (v : ι) : Real.sqrt (planeFactorialDensity ρ (∑ u, V v u) x) ≤
      ∑ u, p v u * Real.sqrt (G u x) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (Finset.sum_nonneg
      (fun u _ => mul_nonneg (hp v u) (Real.sqrt_nonneg _)))).mp
    rw [Real.sq_sqrt (hnon v)]
    exact hx v
  have hs := finite_mass_schur_square_le π hπ p hp θ hθ hrow hcol
    (fun u => Real.sqrt (G u x))
    (fun v => Real.sqrt (planeFactorialDensity ρ (∑ u, V v u) x))
    (fun _ => Real.sqrt_nonneg _) hf
  simpa only [Real.sq_sqrt (hnon _), Real.sq_sqrt (hG _ x)] using hs
end

/-! Stored weak jets of an actual native difference agree with the difference
of the stored jets, including endpoint values and first derivatives. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeStoredJet_sub_sum_ae {K : ℕ} {L : Type*} [Fintype L]
    (U : PlaneHk Set.univ K E) (Z : L → PlaneHk Set.univ K E) (a : JetIndex2 K) :
    (U - ∑ j, Z j).toFunction.jet a =ᵐ[volume]
      (fun z => U.toFunction.jet a z - ∑ j, (Z j).toFunction.jet a z) := by
  classical
  rcases a with ⟨⟨r, hr⟩, w⟩
  have h := Nat.le_of_lt_succ hr
  have he : planeJetOrder (U - ∑ j, Z j) r w =ᵐ[volume]
      (fun z => planeJetOrder U r w z - ∑ j, planeJetOrder (Z j) r w z) := by
    filter_upwards [planeJetOrder_sub_ae h U (∑ j, Z j) w,
      planeJetOrder_finite_sum_ae h Z w] with z hz hs
    rw [hz, hs]
  simpa only [planeJetOrder_eq_stored h] using he
end

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory UnitAddTorus AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Native torus value and physical gradient fields of a cell H1 frequency field. -/

local instance centeredCellBlochReadoutMeasure : MeasureSpace UnitAddCircle := instMeasureSpaceUnitAddCircle

def centeredCellBlochValueField (u : Lp CellComplexH1 2 centeredPlaneFrequencyMeasure) :
    Lp ComplexCellL2 2 centeredPlaneFrequencyMeasure := cellComplexH1ValueCLM.compLp u

def centeredCellBlochGradientField (u : Lp CellComplexH1 2 centeredPlaneFrequencyMeasure)
    (i : Fin 2) : Lp ComplexCellL2 2 centeredPlaneFrequencyMeasure :=
  (centeredCellBlochGradient_memLp u i).toLp (fun θ =>
    cellShiftedDerivativeCLM (planePhysicalBlochShift θ) i (cellComplexH1RealEquiv (u θ)))

def centeredCellBlochTorusValue (u : Lp CellComplexH1 2 centeredPlaneFrequencyMeasure) :
    Lp ScalarTorusL2 2 centeredPlaneFrequencyMeasure :=
  scalarCellToTorusField centeredPlaneFrequencyMeasure (centeredCellBlochValueField u)

def centeredCellBlochTorusGradient (u : Lp CellComplexH1 2 centeredPlaneFrequencyMeasure)
    (i : Fin 2) : Lp ScalarTorusL2 2 centeredPlaneFrequencyMeasure :=
  scalarCellToTorusField centeredPlaneFrequencyMeasure (centeredCellBlochGradientField u i)

theorem centeredCellBlochTorus_fourierDerivative
    (u : Lp CellComplexH1 2 centeredPlaneFrequencyMeasure) (i : Fin 2) :
    ∀ᵐ θ ∂centeredPlaneFrequencyMeasure, ∀ n : Fin 2 → ℤ,
      mFourierCoeff (centeredCellBlochTorusGradient u i θ) n =
        (2 * (Real.pi : ℂ) * Complex.I) *
          ((planeLatticeEmbedding 1 n + θ) i : ℂ) *
            mFourierCoeff (centeredCellBlochTorusValue u θ) n := by
  have hv := scalarCellToTorusField_ae centeredPlaneFrequencyMeasure (centeredCellBlochValueField u)
  have hg := scalarCellToTorusField_ae centeredPlaneFrequencyMeasure (centeredCellBlochGradientField u i)
  have hval := cellComplexH1ValueCLM.coeFn_compLp u
  have hder := (centeredCellBlochGradient_memLp u i).coeFn_toLp
  filter_upwards [hv, hg, hval, hder] with θ hv' hg' hval' hder' n
  change centeredCellBlochTorusValue u θ = scalarCellToTorus (centeredCellBlochValueField u θ) at hv'
  change centeredCellBlochTorusGradient u i θ = scalarCellToTorus (centeredCellBlochGradientField u i θ) at hg'
  change centeredCellBlochValueField u θ = cellComplexH1ValueCLM (u θ) at hval'
  change centeredCellBlochGradientField u i θ =
    cellShiftedDerivativeCLM (planePhysicalBlochShift θ) i (cellComplexH1RealEquiv (u θ)) at hder'
  rw [hg', hder', hv', hval', cellComplexH1ValueCLM_eq]
  simpa [planeLatticeEmbedding] using
    cellH1_physicalBlochFourier (cellComplexH1RealEquiv (u θ)) θ i n

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! The actual native coupling flux respects subtraction and finite sums of
solutions at every admissible derivative order, on spatial a.e. classes. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

def nativeCoupledOrderFlux (D : ℕ) (K : ι → ℕ)
    (A : ∀ i u (d : admissibleOrders K D i u), Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.val - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (U : ∀ u, PlaneHk Set.univ (K u + 1) (h u)) (i : ι) (z : Vec 2) :
    PiLp 2 (fun _ : Fin 2 => h i) :=
  ∑ u, ∑ d : admissibleOrders K D i u,
    A i u d z (WithLp.toLp 2 (fun w : DerivativeWord2 (d.val - 1) =>
      planeJetOrder (U u) (d.val - 1) w z))

theorem nativeCoupledOrderFlux_sub_sum_ae {L : Type*} [Fintype L]
    (D : ℕ) (K : ι → ℕ)
    (A : ∀ i u (d : admissibleOrders K D i u), Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.val - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (U : ∀ u, PlaneHk Set.univ (K u + 1) (h u))
    (Z : ∀ (_ : L) u, PlaneHk Set.univ (K u + 1) (h u)) (i : ι) :
    nativeCoupledOrderFlux D K A (fun u => U u - ∑ j, Z j u) i =ᵐ[volume]
      (fun z => nativeCoupledOrderFlux D K A U i z - ∑ j, nativeCoupledOrderFlux D K A (Z j) i z) := by
  classical
  have hj (u : ι) (d : admissibleOrders K D i u) : d.val - 1 ≤ K u + 1 := by
    have hd := (Finset.mem_filter.mp d.property).2
    omega
  have he (u : ι) (d : admissibleOrders K D i u) (w : DerivativeWord2 (d.val - 1)) :
      planeJetOrder (U u - ∑ j, Z j u) (d.val - 1) w =ᵐ[volume]
        (fun z => planeJetOrder (U u) (d.val - 1) w z - ∑ j, planeJetOrder (Z j u) (d.val - 1) w z) := by
    filter_upwards [planeJetOrder_sub_ae (hj u d) (U u) (∑ j, Z j u) w,
      planeJetOrder_finite_sum_ae (hj u d) (fun j => Z j u) w] with z hz hs
    rw [hz, hs]
  filter_upwards [ae_all_iff.mpr (fun u => ae_all_iff.mpr (fun d => ae_all_iff.mpr (he u d)))] with z hz
  have hvector (u : ι) (d : admissibleOrders K D i u) :
      WithLp.toLp 2 (fun w : DerivativeWord2 (d.val - 1) => planeJetOrder (U u - ∑ j, Z j u) (d.val - 1) w z) =
      WithLp.toLp 2 (fun w : DerivativeWord2 (d.val - 1) => planeJetOrder (U u) (d.val - 1) w z) -
        ∑ j, WithLp.toLp 2 (fun w : DerivativeWord2 (d.val - 1) => planeJetOrder (Z j u) (d.val - 1) w z) := by
    apply PiLp.ext
    intro w
    simpa only [PiLp.sub_apply, WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_toLp] using hz u d w
  simp only [nativeCoupledOrderFlux]
  simp_rw [hvector, map_sub, map_sum, Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  exact Finset.sum_comm

end AVRegularity.CycleWords
end
end
end
