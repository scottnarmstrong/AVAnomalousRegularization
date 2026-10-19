-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Sobolev.Basic
public import AVenhance.Infra.Parabolic.FourierGalerkin.WeakGradientPeriodization
public import AVenhance.Infra.Parabolic.FourierGalerkin.TestDensityBridge
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen

/-! Continuous integration-by-parts functionals on the ambient jet product. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization
open scoped ENNReal

namespace AVRegularity.Sobolev

open AVenhance.Infra.Torus AVenhance.Infra.Parabolic.FourierGalerkin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- Multiply a scalar `L²` test by a fixed value vector. -/
def testVectorL2 {U : Set (Vec 2)} (φ : WeakTest U) (e : E) :
    ComponentL2 (volume.restrict U) E :=
  ((ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) e).compLpL
    2 (volume.restrict U)) (φ.memL2.toLp φ.toFun)

/-- Multiply the coordinate derivative of a test by a fixed value vector. -/
def partialTestVectorL2 {U : Set (Vec 2)} (φ : WeakTest U) (i : Fin 2) (e : E) :
    ComponentL2 (volume.restrict U) E :=
  ((ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) e).compLpL
    2 (volume.restrict U)) ((φ.coordDeriv_memL2 i).toLp (φ.coordDeriv i))

/-- The continuous functional for one ordered weak derivative identity on `U`. -/
def weakJetConstraint {U : Set (Vec 2)} {K : ℕ} (j : Fin K)
    (w : DerivativeWord2 j.val) (i : Fin 2) (φ : WeakTest U) (e : E) :
    JetL2 (volume.restrict U) K E →L[ℝ] ℝ :=
  ((InnerProductSpace.toDual ℝ (ComponentL2 (volume.restrict U) E)
      (partialTestVectorL2 φ i e)).comp
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : JetIndex2 K => ComponentL2 (volume.restrict U) E)
      (lowerIndex2 j w))) +
  ((InnerProductSpace.toDual ℝ (ComponentL2 (volume.restrict U) E)
      (testVectorL2 φ e)).comp
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : JetIndex2 K => ComponentL2 (volume.restrict U) E)
      (nextIndex2 j w i)))

/-- The periodic extension of the cell representative of an ambient jet. -/
def periodicJetRepresentative {K : ℕ}
    (D : JetL2 (volume.restrict AVenhance.unitCube) K E) : RawJet2 K E :=
  fun a => fromUnitTorus (periodicToTorus (fun x => D a x))

omit [InnerProductSpace ℝ E] [BorelSpace E] [CompleteSpace E] in
/-- The canonical periodic representative agrees with its cell class almost everywhere. -/
theorem periodicJetRepresentative_ae {K : ℕ}
    (D : JetL2 (volume.restrict AVenhance.unitCube) K E) (a : JetIndex2 K) :
    periodicJetRepresentative D a =ᵐ[volume.restrict AVenhance.unitCube] D a := by
  have hm : MeasurableSet AVenhance.unitCube := by
    simpa [AVenhance.unitCube, Set.pi] using
      (MeasurableSet.univ_pi' (fun _ : Fin 2 =>
        (measurableSet_Ioo : MeasurableSet (Set.Ioo (0 : ℝ) 1))))
  filter_upwards [ae_restrict_mem hm] with x hx
  change D a (unitTorusRepresentative 2 (toUnitTorus 2 x)) = D a x
  rw [unitTorusRepresentative_eq_of_mem_unitCell]
  intro i
  have hi : 0 < x i ∧ x i < 1 := hx i (Set.mem_univ i)
  simpa using (show x i ∈ Set.Ioc (0 : ℝ) 1 from ⟨hi.1, hi.2.le⟩)

omit [InnerProductSpace ℝ E] [BorelSpace E] [CompleteSpace E] in
/-- The periodic representative retains the cell `L²` bounds of the ambient jet. -/
theorem periodicJetRepresentative_memL2 {K : ℕ}
    (D : JetL2 (volume.restrict AVenhance.unitCube) K E) :
    JetMemL2On AVenhance.unitCube (periodicJetRepresentative D) := by
  intro a
  exact (Lp.memLp (D a)).ae_eq (periodicJetRepresentative_ae D a).symm

omit [InnerProductSpace ℝ E] [BorelSpace E] [CompleteSpace E] in
/-- Every component of the canonical representative is literally `Z²` periodic. -/
theorem periodicJetRepresentative_periodic {K : ℕ}
    (D : JetL2 (volume.restrict AVenhance.unitCube) K E) (a : JetIndex2 K) :
    AVenhance.IsZ2Periodic (periodicJetRepresentative D a) :=
  (isZdPeriodic_iff_frozen _).mp (isZdPeriodic_fromUnitTorus _)

/-- Promote a scalar cell test to a vector-valued cell `L²` class. -/
def cellTestVectorL2 (ψ : Vec 2 → ℝ)
    (hψ : MemLp ψ 2 (volume.restrict AVenhance.unitCube)) (e : E) :
    ComponentL2 (volume.restrict AVenhance.unitCube) E :=
  ((ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) e).compLpL
    2 (volume.restrict AVenhance.unitCube)) (hψ.toLp ψ)

omit [BorelSpace E] [CompleteSpace E] in
/-- Cell-test multiplication has its expected almost-everywhere representative. -/
theorem cellTestVectorL2_ae (ψ : Vec 2 → ℝ)
    (hψ : MemLp ψ 2 (volume.restrict AVenhance.unitCube)) (e : E) :
    cellTestVectorL2 ψ hψ e =ᵐ[volume.restrict AVenhance.unitCube] fun x => ψ x • e := by
  have ht := ContinuousLinearMap.coeFn_compLpL
    (p := 2) (μ := volume.restrict AVenhance.unitCube)
    (L := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) e)
    (f := hψ.toLp ψ)
  filter_upwards [ht, hψ.coeFn_toLp] with x hx hψx
  simpa [cellTestVectorL2, hψx] using hx

/-- Periodize a compact test and multiply it by a fixed value vector. -/
def periodizedTestVectorL2 (φ : WeakTest (Set.univ : Set (Vec 2))) (e : E) :
    ComponentL2 (volume.restrict AVenhance.unitCube) E :=
  cellTestVectorL2 (compactTestPeriodization φ.toFun)
    (TestDensityBridge.bridge_continuous_memL2
      (compactTestPeriodization_contDiff φ.compact φ.smooth).continuous) e

/-- Periodize a compact test derivative and multiply it by a fixed value vector. -/
def periodizedPartialTestVectorL2
    (φ : WeakTest (Set.univ : Set (Vec 2))) (i : Fin 2) (e : E) :
    ComponentL2 (volume.restrict AVenhance.unitCube) E :=
  cellTestVectorL2 (compactTestPeriodization (φ.coordDeriv i))
    (TestDensityBridge.bridge_continuous_memL2
      (compactTestPeriodization_contDiff
        (φ.compact.fderiv_apply (𝕜 := ℝ) (basisVec i))
        ((φ.smooth.fderiv_right (by simp)).clm_apply contDiff_const)).continuous) e

/-- The continuous functional for a global periodic weak derivative identity. -/
def periodicWeakJetConstraint {K : ℕ} (j : Fin K) (w : DerivativeWord2 j.val)
    (i : Fin 2) (φ : WeakTest (Set.univ : Set (Vec 2))) (e : E) :
    JetL2 (volume.restrict AVenhance.unitCube) K E →L[ℝ] ℝ :=
  ((InnerProductSpace.toDual ℝ (ComponentL2 (volume.restrict AVenhance.unitCube) E)
      (periodizedPartialTestVectorL2 φ i e)).comp
    (PiLp.proj (𝕜 := ℝ) 2
      (fun _ : JetIndex2 K => ComponentL2 (volume.restrict AVenhance.unitCube) E)
      (lowerIndex2 j w))) +
  ((InnerProductSpace.toDual ℝ (ComponentL2 (volume.restrict AVenhance.unitCube) E)
      (periodizedTestVectorL2 φ e)).comp
    (PiLp.proj (𝕜 := ℝ) 2
      (fun _ : JetIndex2 K => ComponentL2 (volume.restrict AVenhance.unitCube) E)
      (nextIndex2 j w i)))

end AVRegularity.Sobolev
