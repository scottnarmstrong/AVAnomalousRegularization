-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Weighted.ClippedValueTimeGrowth
import AVRegularity.CycleWords.SlowTaylorTimeCoefficient
public import AVRegularity.CycleWords.CenteredCellBlochGradientLp
import AVRegularity.Proofs.GenSem.CoeffArr.Mean
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Compact native value support propagates to every actual weak-jet readout. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeRawJet_supported {K : ℕ} (U : PlaneHk Set.univ K E)
    (A : Set (Vec 2)) (hA : IsClosed A)
    (hu : ∀ᵐ x ∂volume, x ∉ A → planeValue U x = 0) (a : JetIndex2 K) :
    ∀ᵐ x ∂volume, x ∉ A → U.toFunction.jet a x = 0 := by
  have h0 : U.toFunction.jet (valueIndex2 K) =ᵐ[volume.restrict Aᶜ] 0 := by
    change ∀ᵐ x ∂volume.restrict Aᶜ, U.toFunction.jet (valueIndex2 K) x = 0
    rw [ae_restrict_iff' hA.measurableSet.compl]
    exact hu
  have hh := orderedWeakJet_zero_on_open U.toFunction.memL2 U.toFunction.hasWeakJet
    hA.isOpen_compl h0 a
  change ∀ᵐ x ∂volume.restrict Aᶜ, U.toFunction.jet a x = 0 at hh
  exact (ae_restrict_iff' hA.measurableSet.compl).mp hh

theorem planeJetReadout_supported {K : ℕ} (U : PlaneHk Set.univ K E)
    (A : Set (Vec 2)) (hA : IsClosed A)
    (hu : ∀ᵐ x ∂volume, x ∉ A → planeValue U x = 0) (a : JetIndex2 K) :
    ∀ᵐ x ∂volume, x ∉ A → Weighted.planeJetReadoutOperator K a U x = 0 := by
  filter_upwards [Weighted.planeJetReadout_ae_raw U a,
    planeRawJet_supported U A hA hu a] with x hx hs
  intro hout
  rw [hx, hs hout]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Genuine joint integrability of the generator pairing used in the plane weak equation. -/

theorem cellPhysicalGenerator_joint_integrable (a b : ℝ)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (u : Lp CellComplexH1 2 (centeredPlaneFrequencyMeasure.prod (volume.restrict (Set.Icc a b))))
    (test : Lp CellComplexH1 2 centeredPlaneFrequencyMeasure) :
    Integrable (fun p : Vec 2 × ℝ => cellGeneratorForm
      ⟨fun t _ => G t, v, planePhysicalBlochShift p.1, 0⟩ hG V hv hb p.2
        (cellComplexH1RealEquiv (u p)) (cellComplexH1RealEquiv (test p.1)))
      (centeredPlaneFrequencyMeasure.prod (volume.restrict (Set.Icc a b))) := by
  have hm := cellPhysicalGenerator_variable_stronglyMeasurable G hG v V hv hb u
    (fun p : Vec 2 × ℝ => test p.1) (Lp.stronglyMeasurable u)
    ((Lp.stronglyMeasurable test).comp_measurable measurable_fst)
  have hd := (Lp.memLp u).norm.integrable_mul
    (((Lp.memLp test).norm).comp_fst (volume.restrict (Set.Icc a b)))
  apply (hd.const_mul (cellPhysicalGeneratorBound V)).mono' hm.aestronglyMeasurable
  have hp : ∀ᵐ θ ∂centeredPlaneFrequencyMeasure, ∀ i,
      ‖Complex.I * planePhysicalBlochShift θ i‖ ≤ 2 * Real.pi :=
    ae_all_iff.mpr centeredPhysicalBlochPhase_norm_le
  have hprod := (Measure.quasiMeasurePreserving_fst (μ := centeredPlaneFrequencyMeasure)
    (ν := volume.restrict (Set.Icc a b))).ae hp
  filter_upwards [hprod] with p hp'
  rw [Real.norm_eq_abs]
  have he := cellPhysicalGenerator_abs_le G hG v V hv hb p.1 hp' p.2
    (cellComplexH1RealEquiv (u p)) (cellComplexH1RealEquiv (test p.1))
  simpa only [cellComplexH1RealEquiv.norm_map, Pi.mul_apply, mul_assoc] using he

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory UnitAddTorus AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The actual transverse projections are compatible self-adjoint maps of the cell Hilbert pair. -/

local instance cellTransverseProjectionAdjointMeasure : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

theorem scalarTorusTransverseProjection_real_inner (e : Fin 2) (u v : ScalarTorusL2) :
    inner ℝ (scalarTorusTransverseProjection e u) v =
      inner ℝ u (scalarTorusTransverseProjection e v) := by
  let b := mFourierBasis (d := Fin 2)
  let R : ScalarTorusL2 →ₗᵢ[ℝ] lp (fun _ : Fin 2 → ℤ => ℂ) 2 :=
    { toLinearMap := b.repr.toLinearMap.restrictScalars ℝ
      norm_map' := b.repr.norm_map }
  rw [← R.inner_map_map (scalarTorusTransverseProjection e u) v,
    ← R.inner_map_map u (scalarTorusTransverseProjection e v),
    lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  have hu := hilbertBasisSectorProjection_repr b {k | k e = 0} u n
  have hv := hilbertBasisSectorProjection_repr b {k | k e = 0} v n
  have hl := congrArg (fun z : ℂ => inner ℝ z (b.repr v n)) hu
  have hr := congrArg (fun z : ℂ => inner ℝ (b.repr u n) z) hv
  apply hl.trans
  apply Eq.trans ?_ hr.symm
  split_ifs
  · rfl
  · simp only [inner_zero_left, inner_zero_right]

theorem cellTransverseProjection_inner (e : Fin 2) (u v : ComplexCellL2) :
    inner ℝ (cellTransverseProjection e u) v = inner ℝ u (cellTransverseProjection e v) := by
  calc
    _ = inner ℝ (scalarTorusTransverseProjection e (scalarTorusCellUnitary.symm u))
        (scalarTorusCellUnitary.symm v) := by
      rw [← scalarTorusCellUnitary.inner_map_map, scalarTorusCellUnitary.apply_symm_apply]
      rfl
    _ = inner ℝ (scalarTorusCellUnitary.symm u)
        (scalarTorusTransverseProjection e (scalarTorusCellUnitary.symm v)) :=
      scalarTorusTransverseProjection_real_inner e _ _
    _ = _ := by
      rw [← scalarTorusCellUnitary.inner_map_map, scalarTorusCellUnitary.apply_symm_apply]
      rfl

theorem cellTransverseH1Projection_coordinate (e : Fin 2) (u : TorusHk 1 ℂ)
    (a : JetIndex2 1) :
    (cellTransverseH1Projection e u).val a = cellTransverseProjection e (u.val a) := by
  rcases a with ⟨j, w⟩
  fin_cases j
  · have hw : w = Fin.elim0 := Subsingleton.elim _ _
    subst w
    exact cellTransverseH1Projection_value e u
  · have hw : w = fun _ => w 0 := by
      funext i
      congr 1
      exact Subsingleton.elim i 0
    rw [hw]
    exact cellTransverseH1Projection_derivative e (w 0) u

theorem cellTransverseH1Projection_inner (e : Fin 2) (u v : TorusHk 1 ℂ) :
    inner ℝ (cellTransverseH1Projection e u) v =
      inner ℝ u (cellTransverseH1Projection e v) := by
  change inner ℝ (cellTransverseH1Projection e u).val v.val =
    inner ℝ u.val (cellTransverseH1Projection e v).val
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [cellTransverseH1Projection_coordinate, cellTransverseH1Projection_coordinate]
  exact cellTransverseProjection_inner e _ _

theorem cellTransverseProjection_adjoint (e : Fin 2) :
    (cellTransverseProjection e).adjoint = cellTransverseProjection e := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_right ℝ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact (real_inner_comm _ _).trans
    ((cellTransverseProjection_inner e u v).trans (real_inner_comm _ _))

theorem cellTransverseH1Projection_adjoint (e : Fin 2) :
    (cellTransverseH1Projection e).adjoint = cellTransverseH1Projection e := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_right ℝ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact (real_inner_comm _ _).trans
    ((cellTransverseH1Projection_inner e u v).trans (real_inner_comm _ _))

theorem cellWeakHilbertCurve_transverse_projection {a b : ℝ}
    {u : ℝ → ComplexCellL2} {w g : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u w g) (e : Fin 2) :
    CellWeakHilbertCurve a b (fun t => cellTransverseProjection e (u t))
      (fun t => cellTransverseH1Projection e (w t))
      (fun t => cellTransverseH1Projection e (g t)) := by
  apply h.map (cellTransverseProjection e) (cellTransverseH1Projection e)
  · intro z
    exact (cellTransverseH1Projection_value e z).symm
  · intro z
    rw [cellTransverseProjection_adjoint, cellTransverseH1Projection_adjoint]
    exact (cellTransverseH1Projection_value e z).symm

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleWords

/-! A weight at least one controls the actual native Sobolev norm through its finite L2 jet array. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem weightedJetArray_native_norm_le {K : ℕ} (U : PlaneHk Set.univ K E)
    (q : Vec 2 → ℝ) (hq : ∀ x, 1 ≤ q x)
    (R : PiLp 2 (fun _ : JetIndex2 K => Lp E 2 (volume : Measure (Vec 2))))
    (hR : ∀ a, R a =ᵐ[volume] (fun x => q x • U.toFunction.jet a x)) :
    ‖U‖ ≤ (Fintype.card (JetIndex2 K) : ℝ) * ‖R‖ := by
  have hcomponent (a : JetIndex2 K) : ‖U.val a‖ ≤ ‖R a‖ := by
    rw [← univToPlane.norm_map (U.val a)]
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Weighted.planeJetReadout_ae_raw U a, hR a] with x hu hr
    change ‖Weighted.planeJetReadoutOperator K a U x‖ ≤ ‖R a x‖
    rw [hu, hr, norm_smul, Real.norm_of_nonneg (zero_le_one.trans (hq x))]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hq x)
      (norm_nonneg (U.toFunction.jet a x))
  change ‖U.val‖ ≤ _
  calc
    _ ≤ ∑ a, ‖U.val a‖ := finiteHilbert_norm_le_sum U.val
    _ ≤ ∑ _a : JetIndex2 K, ‖R‖ := by
      apply Finset.sum_le_sum
      intro a _
      exact (hcomponent a).trans (PiLp.norm_apply_le R a)
    _ = _ := by simp

theorem weightedJetArray_native_sub_norm_le {K : ℕ} (U V : PlaneHk Set.univ K E)
    (q : Vec 2 → ℝ) (hq : ∀ x, 1 ≤ q x)
    (R S : PiLp 2 (fun _ : JetIndex2 K => Lp E 2 (volume : Measure (Vec 2))))
    (hR : ∀ a, R a =ᵐ[volume] (fun x => q x • U.toFunction.jet a x))
    (hS : ∀ a, S a =ᵐ[volume] (fun x => q x • V.toFunction.jet a x)) :
    ‖U - V‖ ≤ (Fintype.card (JetIndex2 K) : ℝ) * ‖R - S‖ :=
  weightedJetArray_native_norm_le (U - V) q hq (R - S)
    (weightedJetArray_sub_ae U V q R S hR hS)

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory UnitAddTorus AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The actual transverse projection commutes with complex Bloch shifts. -/

local instance cellTransverseScalarCommutationMeasure : MeasureSpace UnitAddCircle :=
  instMeasureSpaceUnitAddCircle

theorem scalarCellToTorus_complex_smul (c : ℂ) (u : ComplexCellL2) :
    scalarCellToTorus (c • u) = c • scalarCellToTorus u := by
  apply scalarTorusToCell.injective
  rw [scalarTorusToCell_scalarCellToTorus, scalarTorusToCell_complex_smul,
    scalarTorusToCell_scalarCellToTorus]

theorem cellTransverseProjection_complex_smul (e : Fin 2) (c : ℂ) (u : ComplexCellL2) :
    cellTransverseProjection e (c • u) = c • cellTransverseProjection e u := by
  rw [cellTransverseProjection_apply, scalarCellToTorus_complex_smul, map_smul,
    scalarTorusToCell_complex_smul, cellTransverseProjection_apply]

theorem cellTransverseProjection_scalar (e : Fin 2) (c : ℂ) (u : ComplexCellL2) :
    cellTransverseProjection e (cellScalarCLM c u) =
      cellScalarCLM c (cellTransverseProjection e u) := by
  rw [cellScalarCLM_smul, cellScalarCLM_smul]
  exact cellTransverseProjection_complex_smul e c u

theorem cellTransverseH1Projection_shifted_derivative (e i : Fin 2)
    (θ : Fin 2 → ℂ) (u : TorusHk 1 ℂ) :
    cellShiftedDerivativeCLM θ i (cellTransverseH1Projection e u) =
      cellTransverseProjection e (cellShiftedDerivativeCLM θ i u) := by
  simp only [cellShiftedDerivativeCLM, add_apply, ContinuousLinearMap.comp_apply,
    cellTransverseH1Projection_derivative, cellTransverseH1Projection_value, map_add,
    cellTransverseProjection_scalar]

end AVRegularity.CycleWords
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleWords

/-! Clipped factorial state energy is time integrable for the actual energy carrier. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem rawWeightedFactorial_time_integrable {K : ℕ}
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {t₀ S ϖ : ℝ} {zc : Vec 2} {N : ℕ} {Cw : ℕ → ℝ}
    (C : ChartWeights G v t₀ S ϖ zc N Cw) (m : ℕ) (hm : m ≤ N)
    (B : ℝ) (hB : 0 < B) (ρ : ℝ) (μ : Measure ℝ)
    (U : ℝ → PlaneHk Set.univ K E) (hU : MemLp U 2 μ) :
    Integrable (fun t => rawWeightedFactorialEnergy ρ
      (fun x => clipWeight B (C.W m t x)) (U t).toFunction.jet) μ := by
  have hi (α : JetIndex2 K) := chartWeights_clipped_scalar_time_integrable
    C m hm B hB μ (fun t => planeJetReadoutOperator K α (U t))
    ((planeJetReadoutOperator (E := E) K α).comp_memLp' hU)
  have hsum := integrable_finsetSum (Finset.univ : Finset (JetIndex2 K))
    (fun α _ => (hi α).const_mul (factorialWeight ρ α.1.val))
  apply hsum.congr
  exact Filter.Eventually.of_forall (fun t => planeStoredWord_factorial_energy ρ _ (U t))

end AVRegularity.CycleWords
end

section
open AVRegularity.Sobolev AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Native Bloch flux pairings have two genuine nonempty-word endpoint gains. -/

theorem torusHigherValue_norm_le {K : ℕ} (U : TorusHk K ℂ) :
    ‖torusHkValueCLM U‖ ≤ ‖U‖ := PiLp.norm_apply_le U.val (valueIndex2 K)

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleWords

/-! Metric remainder coefficients retain their full Taylor remainder factor. -/

def metricRemainderTimeCoefficient (K : ℕ) (f : ℝ → Vec 2 → ℝ)
    (a b : ℝ) (t : ℝ) (z : Vec 2) : ℝ :=
  if t ∈ Set.Icc a b then f t z - taylorSlow 0 K (f t) 0 z else 0

theorem metricRemainder_time_coefficient_budget (K N : ℕ) (M : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℝ → Vec 2 → ℝ) (a b ϖ ρ ζ g : ℝ),
      (∀ X, Measurable (fun t => f t X)) →
      (∀ t ∈ Set.Icc a b, ContDiff ℝ (K + 1 + N : ℕ) (f t)) →
      0 < ϖ → 0 ≤ ρ → ρ * ϖ ≤ 1 → 0 ≤ ζ → ζ ≤ 1 → 0 ≤ g →
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ r, K + 1 ≤ r → r ≤ K + 1 + N →
        ∀ y, ‖iteratedFDeriv ℝ r (f t) y‖ ≤ M r * g * (ζ * ϖ) ^ r) →
      (∀ z, Measurable (fun t => metricRemainderTimeCoefficient K f a b t z)) ∧
      (∀ t, ContDiff ℝ (N : ℕ) (metricRemainderTimeCoefficient K f a b t)) ∧
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j ≤ N, ∀ z,
        ρ ^ j * ‖iteratedFDeriv ℝ j (metricRemainderTimeCoefficient K f a b t) z‖ ≤
          C * g * ζ ^ (K + 1) * polynomialMomentRoot ϖ z ^ (K + 1)) := by
  obtain ⟨C, hC, hb⟩ := geometryTaylor_remainder_envelope K N M
  refine ⟨C, hC, ?_⟩
  intro f a b ϖ ρ ζ g hm hf hϖ hρ hscale hζ hζ1 hg hjet
  refine ⟨?_, ?_, ?_⟩
  · intro z
    have hfs : ∀ t ∈ Set.Icc a b, ∀ _z : Vec 2, ContDiff ℝ (K : ℕ) (f t) := by
      intro t ht _
      exact (hf t ht).of_le (by exact_mod_cast (by omega : K ≤ K + 1 + N))
    have htaylor := Weighted.taylorSlow_time_window_measurable (Set.Icc a b) measurableSet_Icc
      0 K (fun t X _ => f t X) (fun X _ => hm X) hfs 0 1 z
    have hactual : Measurable (fun t => if t ∈ Set.Icc a b then f t z else 0) :=
      (hm z).piecewise measurableSet_Icc (measurable_const (a := (0 : ℝ)))
    convert hactual.sub htaylor using 1
    funext t
    by_cases ht : t ∈ Set.Icc a b
    · simp only [metricRemainderTimeCoefficient, Pi.sub_apply, ite_eq_left ht, one_smul]
    · simp only [metricRemainderTimeCoefficient, Pi.sub_apply, ite_eq_right ht, sub_self]
  · intro t
    by_cases ht : t ∈ Set.Icc a b
    · have he : metricRemainderTimeCoefficient K f a b t =
          fun z => f t z - taylorSlow 0 K (f t) 0 z := by
        funext z
        simp only [metricRemainderTimeCoefficient, ite_eq_left ht]
      rw [he]
      exact ((hf t ht).of_le (by exact_mod_cast (by omega : N ≤ K + 1 + N))).sub
        (metricTaylor_polynomial_contDiff 0 K N (f t))
    · have he : metricRemainderTimeCoefficient K f a b t = fun _ => (0 : ℝ) := by
        funext z
        simp only [metricRemainderTimeCoefficient, ite_eq_right ht]
      rw [he]
      exact contDiff_const
  · filter_upwards [hjet, ae_restrict_mem measurableSet_Icc] with t ht htI
    have he : metricRemainderTimeCoefficient K f a b t =
        fun z => f t z - taylorSlow 0 K (f t) 0 z := by
      funext z
      simp only [metricRemainderTimeCoefficient, ite_eq_left htI]
    rw [he]
    exact hb (f t) (hf t htI) ϖ ρ ζ g hϖ hρ hscale hζ hζ1 hg ht

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Filter AVRegularity.Sobolev
open scoped Topology
namespace AVRegularity.CycleWords

/-! Strong finite weighted jet arrays control native convergence and identify their actual limit fields. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem weightedJetArray_tendsto_native {K : ℕ} (UN : ℕ → PlaneHk Set.univ K E)
    (U : PlaneHk Set.univ K E) (q : Vec 2 → ℝ) (hq : ∀ x, 1 ≤ q x)
    (RN : ℕ → PiLp 2 (fun _ : JetIndex2 K => Lp E 2 (volume : Measure (Vec 2))))
    (R : PiLp 2 (fun _ : JetIndex2 K => Lp E 2 (volume : Measure (Vec 2))))
    (hRN : ∀ n a, RN n a =ᵐ[volume] (fun x => q x • (UN n).toFunction.jet a x))
    (hR : ∀ a, R a =ᵐ[volume] (fun x => q x • U.toFunction.jet a x))
    (ht : Tendsto RN atTop (𝓝 R)) : Tendsto UN atTop (𝓝 U) := by
  have hr : Tendsto (fun n => (Fintype.card (JetIndex2 K) : ℝ) * ‖RN n - R‖)
      atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero, mul_zero] using
      (ht.sub_const R).norm.const_mul (Fintype.card (JetIndex2 K) : ℝ)
  have hn : Tendsto (fun n => ‖UN n - U‖) atTop (𝓝 0) :=
    squeeze_zero (fun _ => norm_nonneg _)
      (fun n => weightedJetArray_native_sub_norm_le (UN n) U q hq (RN n) R (hRN n) hR) hr
  rw [tendsto_iff_dist_tendsto_zero]
  simpa only [dist_eq_norm] using hn

theorem weightedJetArray_limit_readout_ae {K : ℕ} (UN : ℕ → PlaneHk Set.univ K E)
    (U : PlaneHk Set.univ K E) (q : Vec 2 → ℝ)
    (RN : ℕ → PiLp 2 (fun _ : JetIndex2 K => Lp E 2 (volume : Measure (Vec 2))))
    (R : PiLp 2 (fun _ : JetIndex2 K => Lp E 2 (volume : Measure (Vec 2))))
    (hRN : ∀ n a, RN n a =ᵐ[volume] (fun x => q x • (UN n).toFunction.jet a x))
    (hU : Tendsto UN atTop (𝓝 U)) (hR : Tendsto RN atTop (𝓝 R)) (a : JetIndex2 K) :
    R a =ᵐ[volume] (fun x => q x • U.toFunction.jet a x) := by
  let A := Weighted.planeJetReadoutOperator (E := E) K a
  have hu : Tendsto (fun n => A (UN n)) atTop (𝓝 (A U)) := (A.continuous.tendsto U).comp hU
  have hr : Tendsto (fun n => RN n a) atTop (𝓝 (R a)) :=
    ((PiLp.continuous_apply 2 (fun _ : JetIndex2 K => Lp E 2 (volume : Measure (Vec 2))) a).tendsto R).comp hR
  have he (n : ℕ) : RN n a =ᵐ[volume] (fun x => q x • A (UN n) x) :=
    (hRN n a).trans ((Weighted.planeJetReadout_ae_raw (UN n) a).symm.mono
      (fun x hx => congrArg (fun e : E => q x • e) hx))
  have hl := L2_weighted_limit_ae (fun n => A (UN n)) (fun n => RN n a) (A U) (R a) q hu hr he
  exact hl.trans ((Weighted.planeJetReadout_ae_raw U a).mono
    (fun x hx => congrArg (fun e : E => q x • e) hx))

end AVRegularity.CycleWords
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! The spatial estimate for the actual compact clipped-weight scalar energy test. -/

open AVRegularity.Weighted

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem cellMetric_planeScalarDual_clipped_compact_estimate
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {t₀ S ϖ : ℝ} {zc : Vec 2} {N : ℕ} {Cw : ℕ → ℝ}
    (W : ChartWeights G v t₀ S ϖ zc N Cw) (m : ℕ) (hm : m ≤ N)
    (t : ℝ) (ht : t ∈ Icc t₀ (t₀ + S)) (B : ℝ) (hB : 0 < B)
    (hCell : IsCellMetric G)
    (hv : ContDiff ℝ 1 (v t))
    (hdiv : ∀ x, ∑ j : Fin 2, fderiv ℝ (v t) x (basisVec j) j = 0)
    (hGs : ∀ x, (G t x).IsSymm)
    (hG : ∀ i j : Fin 2, ContDiff ℝ 1 (fun x => G t x i j))
    (χ : Vec 2 → ℝ) (hχ : ContDiff ℝ 2 χ) (hsχ : HasCompactSupport χ)
    {M η : ℝ} (hM : 0 ≤ M) (hη : 0 ≤ η)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (hvb : ∀ x, ‖v t x‖ ≤ M) (hdχ : ∀ x, ‖fderiv ℝ χ x‖ ≤ η)
    (u z : PlaneHk Set.univ 1 E) (F : PlaneFluxL2 E)
    (hz : planeHkValueOperator (E := E) 1 z =ᵐ[volume]
      fun x => (χ x ^ 2 * clipWeight B (W.W m t x)) • planeHkValueOperator (E := E) 1 u x) :
    let q := fun x => clipWeight B (W.W m t x)
    let U := planeHkValueOperator (E := E) 1 u
    let du := planeH1GradientOperator (E := E) u
    2 * inner ℝ (planeWeakDualRepresentative
      (planeScalarTransport (v t) (fun k => (contDiff_pi.mp hv k).continuous) hM
        (fun k x => (by simpa only [← Real.norm_eq_abs] using
          (norm_le_pi_norm (v t x) k).trans (hvb x))))
      (planeScalarDiffusion (G t) (fun k j => (hG k j).continuous) (by norm_num : (0 : ℝ) ≤ 2)
        (fun k j x => CycleEvolution.cellMetric_entry_bound hCell t x k j)) u F) z +
    (∫ x, χ x ^ 2 * deriv (fun s => clipWeight B (W.W m s x)) t * ‖U x‖ ^ 2) +
    (∫ x, (1 / 2) * χ x ^ 2 * q x * ‖(WithLp.toLp 2 (fun i => du i x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) ≤
    18 * W.lam m * (∫ x, χ x ^ 2 * q x * ‖U x‖ ^ 2) +
    8 * (∫ x, q x * ‖(WithLp.toLp 2 (fun i => F i x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) +
    (4096 * η ^ 2 + 16 * M * η) * (∫ x, q x * ‖U x‖ ^ 2) := by
  let q := fun x => clipWeight B (W.W m t x)
  let Φ := fun i x => clipWeightDeriv B (W.W m t x) * W.Phi m t x i
  let dt := fun x => deriv (fun s => clipWeight B (W.W m s x)) t
  let U := planeHkValueOperator (E := E) 1 u
  let du := planeH1GradientOperator (E := E) u
  obtain ⟨hq, hΦ, hdt⟩ := chartWeights_clipped_spatial_regularity W m hm t B hB
  have hvcomp k x : |v t x k| ≤ M := by
    simpa only [← Real.norm_eq_abs] using (norm_le_pi_norm (v t x) k).trans (hvb x)
  have hGb k j x : |G t x k j| ≤ 2 :=
    CycleEvolution.cellMetric_entry_bound hCell t x k j
  obtain ⟨hidentity, hL⟩ := cellMetric_planeScalarDual_cutoff_production_identity (v t) hv hM hvcomp (G t)
    hG hGs (by norm_num : (0 : ℝ) ≤ 2) hGb q χ hq hχ hsχ Φ hΦ dt hdt u z F hz
  let L := fun x => cellMetricCutoffFluxProduction (G t) (v t) q χ Φ dt x
    (WithLp.toLp 2 (fun i => du i x)) (WithLp.toLp 2 (fun i => F i x)) (U x)
  let e := fun x => χ x ^ 2 * q x * ‖U x‖ ^ 2
  let f := fun x => q x * ‖(WithLp.toLp 2 (fun i => F i x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2
  let mass := fun x => q x * ‖U x‖ ^ 2
  have he : Integrable e volume := by
    apply compact_scalar_normSq_integrable U _ ((hχ.continuous.pow 2).mul hq.continuous)
    convert (hsχ.mul_right (f' := χ)).mul_right (f' := q) using 1
    funext x
    exact congrArg (fun r => r * q x) (pow_two (χ x))
  have hqb : ∀ᵐ x ∂volume, ‖q x‖ ≤ B := Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_of_nonneg (clipWeight_pos hB (W.pos m hm t x)).le]
    exact clipWeight_le_bound hB (W.pos m hm t x))
  have hf : Integrable f volume := bounded_scalar_finiteLp_normSq_integrable F q
    hq.continuous.aestronglyMeasurable hqb
  have hmass : Integrable mass volume := bounded_scalar_Lp_normSq_integrable U q
    hq.continuous.aestronglyMeasurable hqb
  have hpoint : ∀ᵐ x ∂volume, L x ≤ (18 * W.lam m) * e x + 8 * f x +
      (4096 * η ^ 2 + 16 * M * η) * mass x := Filter.Eventually.of_forall (fun x => by
    have hh := cellMetric_chartWeights_clipped_cutoff_energy_pointwise W m hm t ht B hB hCell
      hv hdiv hGs hG χ (hχ.differentiable (by norm_num)) x hM hη
      (hχ0 x) (hχ1 x) (hvb x) (hdχ x)
      (WithLp.toLp 2 (fun i => du i x)) (WithLp.toLp 2 (fun i => F i x)) (U x)
    dsimp only [L, e, f, mass]
    nlinarith only [hh])
  have hbudget := integral_three_term_bound L e f mass (18 * W.lam m) 8
    (4096 * η ^ 2 + 16 * M * η) hL he hf hmass hpoint
  rw [← hidentity] at hbudget
  exact hbudget

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleWords

/-! Transverse projection commutes with the actual spatially constant measurable-time metric form. -/

theorem cellMetricEntryCLM_constant
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (t : ℝ) (j k : Fin 2) (u : ComplexCellL2) :
    cellMetricEntryCLM hG t j k u = cellScalarCLM (G t j k : ℂ) u := by
  rw [cellScalarCLM_smul]
  apply Lp.ext
  filter_upwards [cellMetricEntryCLM_ae hG t j k u,
    Lp.coeFn_smul (G t j k : ℂ) u] with x hx hs
  rw [hx, hs]
  rfl

theorem cellTransverseProjection_metricEntry
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (e : Fin 2) (t : ℝ) (j k : Fin 2) (u : ComplexCellL2) :
    cellMetricEntryCLM hG t j k (cellTransverseProjection e u) =
      cellTransverseProjection e (cellMetricEntryCLM hG t j k u) := by
  rw [cellMetricEntryCLM_constant, cellMetricEntryCLM_constant, cellTransverseProjection_scalar]

theorem cellTransverseH1Projection_diffusionForm
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (θ : Fin 2 → ℂ) (κ : ℝ → ℂ)
    (e : Fin 2) (t : ℝ) (u z : TorusHk 1 ℂ) :
    cellDiffusionForm ⟨fun t _ => G t, v, θ, κ⟩ hG t (cellTransverseH1Projection e u) z =
      cellDiffusionForm ⟨fun t _ => G t, v, θ, κ⟩ hG t u (cellTransverseH1Projection e z) := by
  simp only [cellDiffusionForm, neg_apply, sum_apply, pullbackInnerCLM_apply,
    ContinuousLinearMap.comp_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [cellTransverseH1Projection_shifted_derivative,
    cellTransverseProjection_metricEntry, cellTransverseProjection_inner,
    cellTransverseH1Projection_shifted_derivative]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The normalized package graph is a genuine native cell L2 vector. -/

theorem scalarPackageGraph_memLp {K : ScalarConstants} {η t0 S : ℝ}
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    (data : FibreScalarData K η G v t0 S) (ξ : Fin 2 → ℂ)
    (hξ : fibreNorm ξ < K.ξ0) (t : ℝ) :
    MemLp (cellValue (fibreSeriesJet data.r ξ) t) 2
      (volume.restrict AVenhance.unitCube) :=
  (((data.graph.2.1 ξ hξ).2.2.1).1.2.2.1 t (Set.mem_univ t)).1

end AVRegularity.CycleWords
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted Filter
open scoped Topology
namespace AVRegularity.CycleWords

/-! Spatial cutoff limits for finite factorial sums of actual stored jets. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] in
theorem stored_factorial_spatial_cutoff_tendsto {K : ℕ}
    (χ : ℕ → Vec 2 → ℝ) (hχ : ∀ n, Continuous (χ n))
    (hχrange : ∀ n x, 0 ≤ χ n x ∧ χ n x ≤ 1)
    (hχlim : ∀ x, Tendsto (fun n => χ n x) atTop (𝓝 1))
    (q : Vec 2 → ℝ) (hq : Continuous q) (B : ℝ) (hqb : ∀ x, |q x| ≤ B)
    (ρ : ℝ) (U : PlaneHk Set.univ K E) :
    Tendsto (fun n => rawWeightedFactorialEnergy ρ (fun x => χ n x ^ 2 * q x)
      U.toFunction.jet) atTop (𝓝 (rawWeightedFactorialEnergy ρ q U.toFunction.jet)) := by
  have hi (α : JetIndex2 K) := bounded_scalar_Lp_normSq_integrable
    (planeJetReadoutOperator K α U) q hq.aestronglyMeasurable
    (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hqb x))
  have hl (α : JetIndex2 K) := integral_spatial_cutoff_tendsto χ
    (fun x => q x * ‖planeJetReadoutOperator K α U x‖ ^ 2)
    (fun n => (hχ n).aestronglyMeasurable) hχrange hχlim (hi α)
  have hs := tendsto_finsetSum Finset.univ (fun α _ => (hl α).const_mul (factorialWeight ρ α.1.val))
  convert hs using 1
  · funext n
    rw [← planeStoredWord_factorial_energy]
    apply Finset.sum_congr rfl
    intro α _
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by ring)
  · rw [← planeStoredWord_factorial_energy]

 theorem stored_gradient_spatial_cutoff_time_tendsto {K : ℕ}
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {t₀ S ϖ : ℝ} {zc : Vec 2} {N : ℕ} {Cw : ℕ → ℝ}
    (C : ChartWeights G v t₀ S ϖ zc N Cw) (m : ℕ) (hm : m ≤ N)
    (B : ℝ) (hB : 0 < B) (ρ : ℝ) (μ : Measure ℝ)
    (W : ℝ → PlaneHk Set.univ (K + 1) E) (hW : MemLp W 2 μ)
    (χ : ℕ → Vec 2 → ℝ) (hχ : ∀ n, Continuous (χ n))
    (hχrange : ∀ n x, 0 ≤ χ n x ∧ χ n x ≤ 1)
    (hχlim : ∀ x, Tendsto (fun n => χ n x) atTop (𝓝 1)) :
    Tendsto (fun n => ∫ t, rawWeightedGradientEnergy ρ
      (fun x => χ n x ^ 2 * clipWeight B (C.W m t x)) (W t).toFunction.jet ∂μ) atTop
      (𝓝 (∫ t, rawWeightedGradientEnergy ρ
        (fun x => clipWeight B (C.W m t x)) (W t).toFunction.jet ∂μ)) := by
  let Z := fun (α : JetIndex2 K) t => planeH1GradientOperator (planeWordH1SliceOperator K α (W t))
  have hz α : MemLp (Z α) 2 μ := (planeH1GradientOperator (E := E)).comp_memLp'
    ((planeWordH1SliceOperator (E := E) K α).comp_memLp' hW)
  obtain ⟨hqc, hqm, hqb⟩ := chartWeights_clipped_time_coefficient C m hm B hB
  have hi α := chartWeights_clipped_finite_time_integrable C m hm B hB μ (Z α) (hz α)
  have hic n α := chartWeights_clipped_cutoff_finite_time_integrable C m hm B hB
    (χ n) (hχ n) (fun x => (hχrange n x).1) (fun x => (hχrange n x).2) μ (Z α) (hz α)
  have hl α := finite_energy_spatial_cutoff_time_tendsto χ hχ hχrange hχlim
    (fun t x => clipWeight B (C.W m t x)) hqc hqm hB.le hqb
    (fun t x => (clipWeight_pos hB (C.pos m hm t x)).le) μ (Z α) (hz α)
  have hs := tendsto_finsetSum Finset.univ (fun α _ => (hl α).const_mul (factorialWeight ρ α.1.val))
  convert hs using 1
  · funext n
    simp_rw [← planeStoredWord_gradient_energy]
    rw [integral_finsetSum _ (fun α _ => (hic n α).const_mul (factorialWeight ρ α.1.val))]
    apply Finset.sum_congr rfl
    intro α _
    exact integral_const_mul _ _
  · simp_rw [← planeStoredWord_gradient_energy]
    rw [integral_finsetSum _ (fun α _ => (hi α).const_mul (factorialWeight ρ α.1.val))]
    congr 1
    apply Finset.sum_congr rfl
    intro α _
    exact integral_const_mul _ _

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Weighted jets on a fixed compact support have continuous native readouts. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem exists_compactWeightedJetReadout (K : ℕ) (a : JetIndex2 K)
    (A : Set (Vec 2)) (hA : IsCompact A) (q : Vec 2 → ℝ) (hq : Continuous q) :
    ∃ W : PlaneHk Set.univ K E →L[ℝ] Lp E 2 (volume : Measure (Vec 2)),
      ∀ U : PlaneHk Set.univ K E,
        (∀ᵐ x ∂volume, x ∉ A → planeValue U x = 0) →
        W U =ᵐ[volume] (fun x => q x • U.toFunction.jet a x) := by
  obtain ⟨W, hw⟩ := exists_compactWeightL2Operator (E := E) A hA q hq
  refine ⟨W.comp (Weighted.planeJetReadoutOperator K a), ?_⟩
  intro U hu
  have ha := hw (Weighted.planeJetReadoutOperator K a U)
    (planeJetReadout_supported U A hA.isClosed hu a)
  exact ha.trans ((Weighted.planeJetReadout_ae_raw U a).mono
    (fun x hx => congrArg (fun e : E => q x • e) hx))

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The original normalized graph has literal integral one at every time. -/

local instance scalarPackageGraphMeanOneProbCube : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using cellCube_volume_one⟩

theorem scalarPackageGraph_mean_one {K : ScalarConstants} {η t₀ S : ℝ}
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    (data : FibreScalarData K η G v t₀ S) (ξ : Fin 2 → ℂ)
    (hξ : fibreNorm ξ < K.ξ0) (t : ℝ) :
    (∫ x in AVenhance.unitCube, (1 + cellValue (fibreSeriesJet data.r ξ) t x)) = 1 := by
  have hm : cellMean (cellValue (fibreSeriesJet data.r ξ) t) = 0 :=
    ((data.graph.2.1 ξ hξ).2.2.1).2.1 t
  rw [integral_add (integrable_const _) ((scalarPackageGraph_memLp data ξ hξ t).integrable (by norm_num))]
  change (∫ _ in AVenhance.unitCube, (1 : ℂ)) + cellMean (cellValue (fibreSeriesJet data.r ξ) t) = 1
  rw [hm, add_zero]
  simp only [integral_const, Measure.real_def, Measure.restrict_apply_univ,
    cellCube_volume_one, ENNReal.toReal_one, one_smul]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Filter AVRegularity.Sobolev
open scoped Topology
namespace AVRegularity.CycleWords

/-! Cauchy weighted jet arrays have genuine native Sobolev limits with the stated weighted readouts. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] in
theorem weightedJetArray_cauchy_limit {K : ℕ} (UN : ℕ → PlaneHk Set.univ K E)
    (q : Vec 2 → ℝ) (hq : ∀ x, 1 ≤ q x)
    (RN : ℕ → PiLp 2 (fun _ : JetIndex2 K => Lp E 2 (volume : Measure (Vec 2))))
    (hRN : ∀ n a, RN n a =ᵐ[volume] (fun x => q x • (UN n).toFunction.jet a x))
    (hc : CauchySeq RN) :
    ∃ U : PlaneHk Set.univ K E,
    ∃ R : PiLp 2 (fun _ : JetIndex2 K => Lp E 2 (volume : Measure (Vec 2))),
      Tendsto UN atTop (𝓝 U) ∧ Tendsto RN atTop (𝓝 R) ∧
        ∀ a, R a =ᵐ[volume] (fun x => q x • U.toFunction.jet a x) := by
  have hu : CauchySeq UN := cauchySeq_of_norm_sub_le RN UN
    (Fintype.card (JetIndex2 K) : ℝ) hc (fun n m =>
      weightedJetArray_native_sub_norm_le (UN n) (UN m) q hq (RN n) (RN m) (hRN n) (hRN m))
  obtain ⟨U, hU⟩ := cauchySeq_tendsto_of_complete hu
  obtain ⟨R, hR⟩ := cauchySeq_tendsto_of_complete hc
  exact ⟨U, R, hU, hR, weightedJetArray_limit_readout_ae UN U q RN R hRN hU hR⟩

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Native low graph and row bounds have no Peclet cost. -/

theorem scalarPackageGraphCorrection_norm_le {K : ScalarConstants} {η t0 S : ℝ}
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    (data : FibreScalarData K η G v t0 S) (hCg : 0 ≤ K.Cg) (ξ : Fin 2 → ℂ)
    (hξ : fibreNorm ξ < K.ξ0) (t : ℝ) :
    ‖cellRawTrace (fibreSeriesJet data.r ξ) t‖ ≤ K.Cg * fibreNorm ξ := by
  have he := (cellValue_cellL2Norm_le_energy (fibreSeriesJet data.r ξ) t).trans
    (data.graph.2.1 ξ hξ).2.2.2.2
  rw [cellL2Norm_eq_of_class _ _ (cellRawTrace_ae _ t
    (scalarPackageGraph_memLp data ξ hξ t))] at he
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top he
  simpa only [ENNReal.toReal_ofReal (norm_nonneg _),
    ENNReal.toReal_ofReal (mul_nonneg hCg (fibreNorm_nonneg ξ))] using ht

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Expanding cutoff products are native plane weak carriers with their literal value support. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

def expandingCutoffPlaneHk {K : ℕ} (U : PlaneHk Set.univ K E) (n : ℕ)
    (A : Fin (K + 1) → ℝ)
    (hb : ∀ l x, ‖coefficientDerivativeArray (expandingPlaneCoefficient (E := E) n)
      l.val x‖ ≤ A l) : PlaneHk Set.univ K E :=
  (U.toFunction.mulCoefficient (expandingPlaneCoefficient (E := E) n)
    ((expandingPlaneCoefficient_contDiff n).of_le (by simp)) hb).toHk

theorem expandingCutoffPlaneHk_raw_ae {K : ℕ} (U : PlaneHk Set.univ K E) (n : ℕ)
    (A : Fin (K + 1) → ℝ)
    (hb : ∀ l x, ‖coefficientDerivativeArray (expandingPlaneCoefficient (E := E) n)
      l.val x‖ ≤ A l) (a : JetIndex2 K) :
    (expandingCutoffPlaneHk U n A hb).toFunction.jet a =ᵐ[volume.restrict Set.univ]
      multiplicationRawJet (expandingPlaneCoefficient (E := E) n) U.toFunction.jet a :=
  (U.toFunction.mulCoefficient (expandingPlaneCoefficient (E := E) n)
    ((expandingPlaneCoefficient_contDiff n).of_le (by simp)) hb).toHk_toFunction_ae a

theorem expandingCutoffPlaneHk_readout_ae {K : ℕ} (U : PlaneHk Set.univ K E) (n : ℕ)
    (A : Fin (K + 1) → ℝ)
    (hb : ∀ l x, ‖coefficientDerivativeArray (expandingPlaneCoefficient (E := E) n)
      l.val x‖ ≤ A l) (a : JetIndex2 K) :
    Weighted.planeJetReadoutOperator K a (expandingCutoffPlaneHk U n A hb) =ᵐ[volume]
      multiplicationRawJet (expandingPlaneCoefficient (E := E) n) U.toFunction.jet a := by
  have hh := (U.toFunction.mulCoefficient (expandingPlaneCoefficient (E := E) n)
    ((expandingPlaneCoefficient_contDiff n).of_le (by simp)) hb).toHk_toFunction_ae a
  simp only [Measure.restrict_univ] at hh
  exact (Weighted.planeJetReadout_ae_raw _ a).trans hh

theorem expandingCutoffPlaneHk_value_ae {K : ℕ} (U : PlaneHk Set.univ K E) (n : ℕ)
    (A : Fin (K + 1) → ℝ)
    (hb : ∀ l x, ‖coefficientDerivativeArray (expandingPlaneCoefficient (E := E) n)
      l.val x‖ ≤ A l) :
    planeValue (expandingCutoffPlaneHk U n A hb) =ᵐ[volume]
      (fun x => expandingPlaneCutoff n x • planeValue U x) := by
  have hcut := expandingCutoffPlaneHk_readout_ae U n A hb (valueIndex2 K)
  have hraw := Weighted.planeJetReadout_ae_raw U (valueIndex2 K)
  have hv : Weighted.planeJetReadoutOperator K (valueIndex2 K) U =ᵐ[volume] planeValue U := by
    rw [Weighted.planeJetReadoutOperator_apply, planeValue_eq_stored]
    exact Analysis.Convolution.univToPlane_ae _
  have hc : Weighted.planeJetReadoutOperator K (valueIndex2 K)
      (expandingCutoffPlaneHk U n A hb) =ᵐ[volume] planeValue (expandingCutoffPlaneHk U n A hb) := by
    rw [Weighted.planeJetReadoutOperator_apply, planeValue_eq_stored]
    exact Analysis.Convolution.univToPlane_ae _
  filter_upwards [hcut, hraw, hv, hc] with x hx hu hvx hcx
  rw [hcx] at hx
  rw [hvx] at hu
  rw [hx, multiplicationRawJet_value, expandingPlaneCoefficient,
    smul_apply, ContinuousLinearMap.id_apply, ← hu]

theorem expandingCutoffPlaneHk_supported {K : ℕ} (U : PlaneHk Set.univ K E) (n : ℕ)
    (A : Fin (K + 1) → ℝ)
    (hb : ∀ l x, ‖coefficientDerivativeArray (expandingPlaneCoefficient (E := E) n)
      l.val x‖ ≤ A l) :
    ∀ᵐ x ∂volume, x ∉ tsupport (expandingPlaneCutoff n) →
      planeValue (expandingCutoffPlaneHk U n A hb) x = 0 := by
  filter_upwards [expandingCutoffPlaneHk_value_ae U n A hb] with x hx
  intro hout
  have hz : expandingPlaneCutoff n x = 0 := by
    by_contra hne
    exact hout (subset_tsupport (expandingPlaneCutoff n) hne)
  rw [hx, hz, zero_smul]

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! A bounded metric gives the actual correction flux a uniform quadratic bound. -/

theorem row_dot_sq_bound {a b : ℝ} (ha : |a| ≤ 4) (hb : |b| ≤ 4) (x y : ℝ) :
    (a * x + b * y) ^ 2 ≤ 32 * (x ^ 2 + y ^ 2) := by
  have ha2 : a ^ 2 ≤ 16 := by
    have hh := (sq_le_sq₀ (abs_nonneg a) (by norm_num : (0 : ℝ) ≤ 4)).2 ha
    norm_num only [sq_abs] at hh
    exact hh
  have hb2 : b ^ 2 ≤ 16 := by
    have hh := (sq_le_sq₀ (abs_nonneg b) (by norm_num : (0 : ℝ) ≤ 4)).2 hb
    norm_num only [sq_abs] at hh
    exact hh
  have hc : (a * x + b * y) ^ 2 ≤ (a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2) := by
    nlinarith only [sq_nonneg (a * y - b * x)]
  exact hc.trans (mul_le_mul_of_nonneg_right (by linarith only [ha2, hb2]) (by positivity))

theorem metricCorrectionFlux_sq_sum_bound (W : Vec 2 → ℝ)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (z : Vec 2)
    (hG : ∀ i j : Fin 2, |G z i j| ≤ 5 / 4) :
    (∑ k : Fin 2, metricCorrectionFlux W G z k ^ 2) ≤
      64 * ∑ j : Fin 2, (fderiv ℝ W z (basisVec j)) ^ 2 := by
  have hb : ∀ i j : Fin 2, |(G z - 1) i j| ≤ 4 := by
    intro i j
    have hI : |(1 : Matrix (Fin 2) (Fin 2) ℝ) i j| ≤ 1 := by
      simp only [Matrix.one_apply]
      split_ifs <;> norm_num
    have hsub : |(G z - 1) i j| ≤ |G z i j| + |(1 : Matrix (Fin 2) (Fin 2) ℝ) i j| := by
      simpa only [Matrix.sub_apply, sub_zero, zero_sub, abs_neg] using
        abs_sub_le (G z i j) 0 ((1 : Matrix (Fin 2) (Fin 2) ℝ) i j)
    exact hsub.trans (by
      have hh := add_le_add (hG i j) hI
      norm_num at hh ⊢
      linarith only [hh])
  have he : ∀ k : Fin 2, metricCorrectionFlux W G z k =
      (G z - 1) k 0 * fderiv ℝ W z (basisVec 0) +
        (G z - 1) k 1 * fderiv ℝ W z (basisVec 1) := by
    intro k
    unfold metricCorrectionFlux
    simp only [Fin.sum_univ_two, Matrix.sub_apply, Matrix.one_apply]
    fin_cases k <;> norm_num <;> ring
  simp_rw [he]
  simp only [Fin.sum_univ_two]
  have h0 := row_dot_sq_bound (hb 0 0) (hb 0 1)
    (fderiv ℝ W z (basisVec 0)) (fderiv ℝ W z (basisVec 1))
  have h1 := row_dot_sq_bound (hb 1 0) (hb 1 1)
    (fderiv ℝ W z (basisVec 0)) (fderiv ℝ W z (basisVec 1))
  linarith only [h0, h1]

end AVRegularity.CycleWords
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! The spatial estimate for the actual compact clipped-weight scalar energy test. -/

open AVRegularity.Weighted

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem cellMetric_planeScalarDual_clipped_value_estimate
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {t₀ S ϖ : ℝ} {zc : Vec 2} {N : ℕ} {Cw : ℕ → ℝ}
    (W : ChartWeights G v t₀ S ϖ zc N Cw) (m : ℕ) (hm : m ≤ N)
    (t : ℝ) (ht : t ∈ Icc t₀ (t₀ + S)) (B : ℝ) (hB : 0 < B)
    (hCell : IsCellMetric G)
    (hv : ContDiff ℝ 1 (v t))
    (hdiv : ∀ x, ∑ j : Fin 2, fderiv ℝ (v t) x (basisVec j) j = 0)
    (hGs : ∀ x, (G t x).IsSymm)
    (hG : ∀ i j : Fin 2, ContDiff ℝ 1 (fun x => G t x i j))
    (χ : Vec 2 → ℝ) (hχ : ContDiff ℝ 2 χ) (hsχ : HasCompactSupport χ)
    {M η : ℝ} (hM : 0 ≤ M) (hη : 0 ≤ η)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (hvb : ∀ x, ‖v t x‖ ≤ M) (hdχ : ∀ x, ‖fderiv ℝ χ x‖ ≤ η)
    (u z : PlaneHk Set.univ 1 E) (F : PlaneFluxL2 E)
    (H : Lp E 2 (volume : Measure (Vec 2)))
    (hz : planeHkValueOperator (E := E) 1 z =ᵐ[volume]
      fun x => (χ x ^ 2 * clipWeight B (W.W m t x)) • planeHkValueOperator (E := E) 1 u x) :
    let q := fun x => clipWeight B (W.W m t x)
    let U := planeHkValueOperator (E := E) 1 u
    let du := planeH1GradientOperator (E := E) u
    2 * inner ℝ (planeValueForcedDual
      (planeScalarTransport (v t) (fun k => (contDiff_pi.mp hv k).continuous) hM
        (fun k x => (by simpa only [← Real.norm_eq_abs] using
          (norm_le_pi_norm (v t x) k).trans (hvb x))))
      (planeScalarDiffusion (G t) (fun k j => (hG k j).continuous) (by norm_num : (0 : ℝ) ≤ 2)
        (fun k j x => CycleEvolution.cellMetric_entry_bound hCell t x k j)) u F H) z +
    (∫ x, χ x ^ 2 * deriv (fun s => clipWeight B (W.W m s x)) t * ‖U x‖ ^ 2) +
    (∫ x, (1 / 2) * χ x ^ 2 * q x * ‖(WithLp.toLp 2 (fun i => du i x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) ≤
    18 * W.lam m * (∫ x, χ x ^ 2 * q x * ‖U x‖ ^ 2) +
    8 * (∫ x, q x * ‖(WithLp.toLp 2 (fun i => F i x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) +
    (4096 * η ^ 2 + 16 * M * η) * (∫ x, q x * ‖U x‖ ^ 2) +
      2 * (∫ x, (χ x ^ 2 * q x) * (‖H x‖ * ‖U x‖)) := by
  have hs := cellMetric_planeScalarDual_clipped_compact_estimate W m hm t ht B hB hCell
    hv hdiv hGs hG χ hχ hsχ hM hη hχ0 hχ1 hvb hdχ u z F hz
  obtain ⟨hq, _, _⟩ := chartWeights_clipped_spatial_regularity W m hm t B hB
  let q := fun x => χ x ^ 2 * clipWeight B (W.W m t x)
  have hq0 x : 0 ≤ q x := mul_nonneg (sq_nonneg _) (clipWeight_pos hB (W.pos m hm t x)).le
  have hqb x : ‖q x‖ ≤ B := by
    rw [Real.norm_of_nonneg (hq0 x)]
    have hc : χ x ^ 2 ≤ 1 := by nlinarith only [hχ0 x, hχ1 x]
    calc
      q x ≤ 1 * clipWeight B (W.W m t x) :=
        mul_le_mul_of_nonneg_right hc (clipWeight_pos hB (W.pos m hm t x)).le
      _ ≤ B := by rw [one_mul]; exact clipWeight_le_bound hB (W.pos m hm t x)
  have hqp : AEStronglyMeasurable q volume :=
    ((hχ.continuous.pow 2).mul hq.continuous).aestronglyMeasurable
  have hp := planeValueForcing_weighted_pair_abs_le H
    (planeHkValueOperator (E := E) 1 u) z q hqp
    (Filter.Eventually.of_forall hqb) (Filter.Eventually.of_forall hq0) hz
  rw [ContinuousLinearMap.adjoint_inner_left] at hp
  have hp' := (le_abs_self (inner ℝ H (planeHkValueOperator (E := E) 1 z))).trans hp
  dsimp only
  rw [planeValueForcedDual_pair, mul_add]
  dsimp only [q] at hp'
  linarith only [hs, hp']

end AVRegularity.CycleWords
end

section
open AVRegularity.Sobolev Filter Topology
open scoped ENNReal
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Uniform native bounds and actual value moments recover the rough limit in that reserve. -/

theorem cellNative_exists_of_bounded_moments (q : ℕ) (u : ℕ → TorusHk q ℂ)
    (U : ComplexCellL2) (E : ℝ) (hE : 0 ≤ E) (hb : ∀ n, ‖u n‖ ^ 2 ≤ E)
    (hm : ∀ z : TorusHk 1 ℂ,
      Tendsto (fun n => inner ℝ (torusHkValueCLM (u n)) (torusHkValueCLM z))
        atTop (𝓝 (inner ℝ U (torusHkValueCLM z)))) :
    ∃ V : TorusHk q ℂ, torusHkValueCLM V = U ∧ ‖V‖ ^ 2 ≤ E := by
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let : SecondCountableTopology (TorusHk q ℂ) := inferInstance
  obtain ⟨V, φ, hφ, hw⟩ := cellHilbert_weak_subsequence_clm u (E + 1)
    (fun n => cellNorm_le_budget_add_one (hb n))
  have hvalue : torusHkValueCLM V = U := by
    apply cellL2_eq_of_H1_pairings
    intro z
    let ell := (innerSL ℝ (torusHkValueCLM z)).comp (torusHkValueCLM (E := ℂ) (K := q))
    have hl := hw ell
    have hr := (hm z).comp hφ.tendsto_atTop
    change Tendsto (fun n => inner ℝ (torusHkValueCLM z) (torusHkValueCLM (u (φ n))))
      atTop (𝓝 (inner ℝ (torusHkValueCLM z) (torusHkValueCLM V))) at hl
    have hl' : Tendsto (fun n => inner ℝ (torusHkValueCLM (u (φ n))) (torusHkValueCLM z))
        atTop (𝓝 (inner ℝ (torusHkValueCLM V) (torusHkValueCLM z))) := by
      rw [real_inner_comm (torusHkValueCLM z) (torusHkValueCLM V)]
      exact hl.congr' (Eventually.of_forall (fun n => real_inner_comm _ _))
    exact tendsto_nhds_unique hl' hr
  refine ⟨V, hvalue, ?_⟩
  have ht : Tendsto (fun n => inner ℝ (u (φ n)) V) atTop (𝓝 (inner ℝ V V)) := by
    have hv := hw (innerSL ℝ V)
    change Tendsto (fun n => inner ℝ V (u (φ n))) atTop (𝓝 (inner ℝ V V)) at hv
    exact hv.congr' (Eventually.of_forall (fun n => real_inner_comm _ _))
  have hs : (inner ℝ V V) ^ 2 ≤ E * ‖V‖ ^ 2 := by
    apply le_of_tendsto (ht.pow 2)
    exact Eventually.of_forall (fun n => by
      have hi := abs_real_inner_le_norm (u (φ n)) V
      have hi2 := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hi
      rw [sq_abs, mul_pow] at hi2
      exact hi2.trans (mul_le_mul_of_nonneg_right (hb (φ n)) (sq_nonneg _)))
  rw [real_inner_self_eq_norm_sq] at hs
  nlinarith only [hs, hE, sq_nonneg ‖V‖]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! Literal constants belong to every finite Fourier space, with zero nonempty derivatives. -/

def cellGalerkinConstant (N : ℕ) (c : ℂ) : CellGalerkinSpace (E := ℂ) N :=
  cellGalerkinL2Initial N (cellConstantCLM c)

theorem cellGalerkinConstant_value (N : ℕ) (c : ℂ) :
    cellGalerkinValue N (cellGalerkinConstant N c) = cellConstantCLM c := by
  rw [cellGalerkinConstant, cellGalerkinL2Initial_eq_fourier, cellL2FourierState_value]
  exact cellVectorFourierProjection_constant N c

end AVRegularity.CycleWords
end
