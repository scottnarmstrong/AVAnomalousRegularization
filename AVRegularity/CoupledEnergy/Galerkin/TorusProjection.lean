-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Analysis.Convolution.Kernel.Commutation.TorusBridge
public import AVRegularity.CoupledEnergy.Galerkin.CoefficientPairing
public import AVenhance.Infra.Parabolic.WeakUniqueness.WeakProjection
import AVenhance.Infra.Parabolic.WeakUniqueness.WeakProjectionConvergence
public import AVenhance.Infra.Parabolic.WeakUniqueness.WeakAlgebra
import Homogenization.Sobolev.H1.BasicLemmas
import Mathlib.Tactic.Monotonicity.Lemmas

section
/-! Cell realizations of the finite vector-valued Fourier cutoff. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization
open AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution
open AVRegularity.CoupledEnergy.Galerkin

noncomputable local instance coupledEnergyTorusMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
noncomputable local instance coupledEnergyTorusAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
noncomputable local instance coupledEnergyTorusCircleProbability : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
noncomputable local instance coupledEnergyTorusProbability : IsProbabilityMeasure
    (volume : Measure (UnitAddTorus (Fin 2))) := inferInstance

theorem coupledEnergy_torusMeasure_eq_volume :
    AVRegularity.Analysis.Convolution.torusMeasure =
      (volume : Measure (UnitAddTorus (Fin 2))) := by
  rw [volume_pi]
  rfl

namespace AVRegularity.CoupledEnergy.Galerkin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

noncomputable def torusLpToVolume (f : Lp E 2
    AVRegularity.Analysis.Convolution.torusMeasure) :
    Lp E 2 (volume : Measure (UnitAddTorus (Fin 2))) :=
  coupledEnergy_torusMeasure_eq_volume ▸ f

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] in
theorem torusLpToVolume_coeFn (f : Lp E 2
    AVRegularity.Analysis.Convolution.torusMeasure) :
    torusLpToVolume f =ᵐ[volume] fun y => f y := by
  rfl

/-- The Fourier cutoff transported from the normalized torus to the unit-cell `L²` space. -/
def cellVectorFourierProjection (N : ℕ) :
    Lp E 2 (volume.restrict AVenhance.unitCube) →L[ℝ]
      Lp E 2 (volume.restrict AVenhance.unitCube) :=
  (torusToCell (E := E)).toContinuousLinearMap.comp
    ((vectorFourierProjection (E := E) N).comp
      (cellToTorus (E := E)).toContinuousLinearMap)

theorem cellVectorFourierProjection_norm_le (N : ℕ)
    (f : Lp E 2 (volume.restrict AVenhance.unitCube)) :
    ‖cellVectorFourierProjection (E := E) N f‖ ≤ ‖f‖ := by
  rw [cellVectorFourierProjection]
  calc
    ‖torusToCell ((vectorFourierProjection N) (cellToTorus f))‖ =
        ‖(vectorFourierProjection N) (cellToTorus f)‖ := by
          exact (torusToCell (E := E)).norm_map _
    _ ≤ ‖cellToTorus f‖ := vectorFourierProjection_norm_le N _
    _ = ‖f‖ := (cellToTorus (E := E)).norm_map _

theorem cellToTorus_cellVectorFourierProjection (N : ℕ)
    (f : Lp E 2 (volume.restrict AVenhance.unitCube)) :
    cellToTorus (cellVectorFourierProjection (E := E) N f) =
      vectorFourierProjection (E := E) N (cellToTorus f) := by
  change cellToTorus (torusToCell
    (vectorFourierProjection (E := E) N (cellToTorus f))) = _
  exact cellToTorus_torusToCell _

theorem vectorFourierProjection_idempotent_cellMeasure (N : ℕ)
    (f : Lp E 2 AVRegularity.Analysis.Convolution.torusMeasure) :
    vectorFourierProjection (E := E) N (vectorFourierProjection N f) =
      vectorFourierProjection N f := by
  unfold vectorFourierProjection
  apply finiteOrthonormalProjection_idempotent
  intro p q
  rcases p with ⟨i, j⟩
  rcases q with ⟨i', j'⟩
  exact vectorFourierMode_orthonormal N i i' j j'

theorem cellVectorFourierProjection_idempotent (N : ℕ)
    (f : Lp E 2 (volume.restrict AVenhance.unitCube)) :
    cellVectorFourierProjection (E := E) N
        (cellVectorFourierProjection N f) = cellVectorFourierProjection N f := by
  apply (cellToTorus (E := E)).injective
  rw [cellToTorus_cellVectorFourierProjection,
    cellToTorus_cellVectorFourierProjection,
    vectorFourierProjection_idempotent_cellMeasure]

theorem vectorFourierProjection_inner_cellMeasure (N : ℕ)
    (f g : Lp E 2 AVRegularity.Analysis.Convolution.torusMeasure) :
    inner ℝ (vectorFourierProjection (E := E) N f) g =
      inner ℝ f (vectorFourierProjection N g) := by
  unfold vectorFourierProjection
  exact finiteOrthonormalProjection_inner
    (fun p : VectorFourierIndex N E => vectorFourierMode N p.1 p.2) f g

theorem cellVectorFourierProjection_inner (N : ℕ)
    (f g : Lp E 2 (volume.restrict AVenhance.unitCube)) :
    inner ℝ (cellVectorFourierProjection (E := E) N f) g =
      inner ℝ f (cellVectorFourierProjection N g) := by
  calc
    inner ℝ (cellVectorFourierProjection (E := E) N f) g =
        inner ℝ (cellToTorus (cellVectorFourierProjection N f)) (cellToTorus g) :=
      (cellToTorus (E := E)).inner_map_map _ _ |>.symm
    _ = inner ℝ (vectorFourierProjection (E := E) N (cellToTorus f))
          (cellToTorus g) := by
      rw [cellToTorus_cellVectorFourierProjection]
      rfl
    _ = inner ℝ (cellToTorus f)
          (vectorFourierProjection (E := E) N (cellToTorus g)) :=
      vectorFourierProjection_inner_cellMeasure N _ _
    _ = inner ℝ (cellToTorus f)
          (cellToTorus (cellVectorFourierProjection N g)) := by
      rw [cellToTorus_cellVectorFourierProjection]
    _ = inner ℝ f (cellVectorFourierProjection (E := E) N g) :=
      (cellToTorus (E := E)).inner_map_map _ _

omit [MeasurableSpace E] [BorelSpace E] in
theorem cellToTorus_coordinate_raw (D : Lp E 2
      (volume.restrict AVenhance.unitCube)) (F : Vec 2 → E)
    (j : Fin (Module.finrank ℝ E))
    (hD : D =ᵐ[volume.restrict AVenhance.unitCube] F)
    (hF : MemLp (fun x => inner ℝ ((stdOrthonormalBasis ℝ E) j) (F x)) 2
      (volume.restrict AVenhance.unitCube)) :
    vectorFourierCoordinate (E := E) j (torusLpToVolume (cellToTorus D)) =
      torusLpToVolume (E := ℝ)
        ((hF.comp_measurePreserving measurePreserving_unitTorusRepresentative_cell).toLp
          (fun y => inner ℝ ((stdOrthonormalBasis ℝ E) j)
            (F (AVenhance.Infra.Torus.unitTorusRepresentative 2 y)))) := by
  cases coupledEnergy_torusMeasure_eq_volume
  apply Lp.ext
  have hcell := cellToTorus_ae (E := E) D
  have hcellV : (cellToTorus D : UnitAddTorus (Fin 2) → E) =ᵐ[volume]
      AVenhance.Infra.Torus.periodicToTorus D := by
    rw [← coupledEnergy_torusMeasure_eq_volume]
    exact hcell
  have hinput := torusLpToVolume_coeFn (cellToTorus D)
  have hrep := measurePreserving_unitTorusRepresentative_cell.quasiMeasurePreserving.ae hD
  have hrepV : ∀ᵐ y : UnitAddTorus (Fin 2) ∂volume,
      D (AVenhance.Infra.Torus.unitTorusRepresentative 2 y) =
        F (AVenhance.Infra.Torus.unitTorusRepresentative 2 y) := by
    rw [← coupledEnergy_torusMeasure_eq_volume]
    exact hrep
  have hcoord := ContinuousLinearMap.coeFn_compLpL
    (L := InnerProductSpace.toDual ℝ E ((stdOrthonormalBasis ℝ E) j))
    (torusLpToVolume (cellToTorus D))
  have hrightLp := hF.comp_measurePreserving measurePreserving_unitTorusRepresentative_cell
  have hright := torusLpToVolume_coeFn (hrightLp.toLp _)
  have hrightRaw : (hrightLp.toLp _ : UnitAddTorus (Fin 2) → ℝ) =ᵐ[volume]
      fun y => inner ℝ ((stdOrthonormalBasis ℝ E) j) (F
        (AVenhance.Infra.Torus.unitTorusRepresentative 2 y)) := by
    rw [← coupledEnergy_torusMeasure_eq_volume]
    exact hrightLp.coeFn_toLp
  filter_upwards [hinput, hcellV, hrepV, hcoord, hright, hrightRaw]
    with y hyinput hycell hyrep hycoord hyright hyrightRaw
  change ((InnerProductSpace.toDual ℝ E ((stdOrthonormalBasis ℝ E) j)).compLpL
      2 volume (torusLpToVolume (cellToTorus D))) y =
    (torusLpToVolume (hrightLp.toLp _)) y
  rw [hycoord, hyinput, hycell, hyright]
  simp only [AVenhance.Infra.Torus.periodicToTorus]
  rw [hyrightRaw]
  change inner ℝ ((stdOrthonormalBasis ℝ E) j)
      (D (AVenhance.Infra.Torus.unitTorusRepresentative 2 y)) =
    inner ℝ ((stdOrthonormalBasis ℝ E) j)
      (F (AVenhance.Infra.Torus.unitTorusRepresentative 2 y))
  exact congrArg (inner ℝ ((stdOrthonormalBasis ℝ E) j)) hyrep

/-- Apply the same component cutoff to every entry of a finite jet. -/
def cellJetFourierProjection (K N : ℕ) :
    JetL2 (volume.restrict AVenhance.unitCube) K E →L[ℝ]
      JetL2 (volume.restrict AVenhance.unitCube) K E :=
  (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : JetIndex2 K => Lp E 2 (volume.restrict AVenhance.unitCube))).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun a =>
      (cellVectorFourierProjection (E := E) N).comp
        (PiLp.proj (𝕜 := ℝ) 2
          (fun _ : JetIndex2 K => Lp E 2 (volume.restrict AVenhance.unitCube)) a))

@[simp] theorem cellJetFourierProjection_apply (K N : ℕ)
    (D : JetL2 (volume.restrict AVenhance.unitCube) K E) (a : JetIndex2 K) :
    cellJetFourierProjection (E := E) K N D a = cellVectorFourierProjection N (D a) := rfl

theorem cellJetFourierProjection_idempotent (K N : ℕ)
    (D : JetL2 (volume.restrict AVenhance.unitCube) K E) :
    cellJetFourierProjection (E := E) K N
        (cellJetFourierProjection K N D) = cellJetFourierProjection K N D := by
  apply PiLp.ext
  intro a
  rw [cellJetFourierProjection_apply, cellJetFourierProjection_apply,
    cellVectorFourierProjection_idempotent]

theorem cellJetFourierProjection_component_norm_le (K N : ℕ)
    (D : JetL2 (volume.restrict AVenhance.unitCube) K E) (a : JetIndex2 K) :
    ‖cellJetFourierProjection (E := E) K N D a‖ ≤ ‖D a‖ := by
  rw [cellJetFourierProjection_apply]
  exact cellVectorFourierProjection_norm_le N _

theorem cellJetFourierProjection_derivativeNormSq_le (K N : ℕ)
    (D : JetL2 (volume.restrict AVenhance.unitCube) K E) (j : Fin (K + 1)) :
    derivativeNormSq (cellJetFourierProjection (E := E) K N D) j ≤
      derivativeNormSq D j := by
  unfold derivativeNormSq
  apply Finset.sum_le_sum
  intro w hw
  have hn := cellJetFourierProjection_component_norm_le (E := E) K N D ⟨j, w⟩
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hn

/-- The cell jet cutoff is contractive in every squared factorial weight, including at
nonpositive radii where some levels can have zero weight. -/
theorem cellJetFourierProjection_factorialNormSq_le (K N : ℕ) (ρ : ℝ)
    (D : JetL2 (volume.restrict AVenhance.unitCube) K E) :
    factorialNormSq ρ (cellJetFourierProjection (E := E) K N D) ≤
      factorialNormSq ρ D := by
  unfold factorialNormSq
  apply Finset.sum_le_sum
  intro j hj
  exact mul_le_mul_of_nonneg_left
    (cellJetFourierProjection_derivativeNormSq_le (E := E) K N D j)
    (factorialWeight_nonneg ρ j.val)

end AVRegularity.CoupledEnergy.Galerkin

end
end
end

section
/-! Finite dimensionality of the cell cutoff range. -/

@[expose] public section

noncomputable section

open MeasureTheory AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.Analysis.Convolution
open AVenhance.Infra.Parabolic.FourierGalerkin
open AVRegularity.Sobolev

local instance coupledFiniteRangeMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance coupledFiniteRangeAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance coupledFiniteRangeCircleProbability : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance coupledFiniteRangeTorusProbability : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance

namespace AVRegularity.CoupledEnergy.Galerkin

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

private theorem finiteDimensional_pi_constant_submodule {ι V : Type*}
    [Fintype ι] [NormedAddCommGroup V] [Module ℝ V]
    (S : Submodule ℝ V) [FiniteDimensional ℝ S] :
    FiniteDimensional ℝ (Submodule.pi Set.univ (fun _ : ι => S)) := by
  let coords : Submodule.pi Set.univ (fun _ : ι => S) →ₗ[ℝ] (ι → S) :=
    LinearMap.pi fun i =>
      LinearMap.codRestrict S
        ((LinearMap.proj i).comp
          (Submodule.subtype (Submodule.pi Set.univ (fun _ : ι => S))))
        (fun x => (Submodule.mem_pi.mp x.property) i (Set.mem_univ i))
  have hcoords : Function.Injective coords := by
    intro x y h
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun h i)
  exact FiniteDimensional.of_injective coords hcoords

local instance coupledFiniteDimensionalFourierCoefficients (N : ℕ) :
    FiniteDimensional ℝ (PiLp 2 (fun _ : VectorFourierIndex N E => ℝ)) := by
  apply FiniteDimensional.of_injective
    (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : VectorFourierIndex N E => ℝ)).toLinearEquiv.toLinearMap
    (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : VectorFourierIndex N E => ℝ)).injective

theorem cellVectorFourierProjection_range_finite (N : ℕ) :
    FiniteDimensional ℝ
      (cellVectorFourierProjection (E := E) N).toLinearMap.range := by
  let v : VectorFourierIndex N E → Lp E 2 (volume : Measure (UnitAddTorus (Fin 2))) :=
    fun p => vectorFourierMode N p.1 p.2
  let syn : PiLp 2 (fun _ : VectorFourierIndex N E => ℝ) →L[ℝ]
      Lp E 2 (volume.restrict AVenhance.unitCube) :=
    (torusToCell (E := E)).toContinuousLinearMap.comp
      (finiteProjectionSynthesisCLM v)
  have hsub : (cellVectorFourierProjection (E := E) N).toLinearMap.range ≤
      syn.toLinearMap.range := by
    intro y hy
    rcases hy with ⟨x, rfl⟩
    refine ⟨finiteProjectionCoefficientsCLM v (cellToTorus x), ?_⟩
    rfl
  have hfinS : FiniteDimensional ℝ syn.toLinearMap.range := by
    exact @Module.Finite.range ℝ _ _ _ _ _ _ _
      (coupledFiniteDimensionalFourierCoefficients (E := E) N) syn.toLinearMap
  exact @Submodule.finiteDimensional_of_le ℝ _ _ _ _ _ _ hfinS hsub

local instance coupledEnergyCellVectorRangeFinite (N : ℕ) :
    FiniteDimensional ℝ
      (cellVectorFourierProjection (E := E) N).toLinearMap.range :=
  cellVectorFourierProjection_range_finite (E := E) N

def cellJetFourierProductRange (K N : ℕ) :
    Submodule ℝ (∀ _ : JetIndex2 K,
      Lp E 2 (volume.restrict AVenhance.unitCube)) :=
  Submodule.pi Set.univ (fun _ : JetIndex2 K =>
    (cellVectorFourierProjection (E := E) N).toLinearMap.range)

local instance coupledEnergyCellJetProductRangeFinite (K N : ℕ) :
    FiniteDimensional ℝ (cellJetFourierProductRange (E := E) K N) := by
  unfold cellJetFourierProductRange
  apply finiteDimensional_pi_constant_submodule

theorem cellJetFourierProjection_range_finite (K N : ℕ) :
    FiniteDimensional ℝ
      (cellJetFourierProjection (E := E) K N).toLinearMap.range := by
  let e := PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : JetIndex2 K => Lp E 2 (volume.restrict AVenhance.unitCube))
  let T := (cellJetFourierProductRange (E := E) K N).map
    e.symm.toLinearEquiv.toLinearMap
  have hsub : (cellJetFourierProjection (E := E) K N).toLinearMap.range ≤ T := by
    intro y hy
    rcases hy with ⟨x, rfl⟩
    apply Submodule.mem_map.mpr
    refine ⟨(fun a => cellVectorFourierProjection (E := E) N (x a)), ?_, ?_⟩
    · apply Submodule.mem_pi.mpr
      intro a ha
      exact ⟨x a, rfl⟩
    · apply PiLp.ext
      intro a
      rfl
  have hfinT : FiniteDimensional ℝ T := by
    exact @Module.Finite.map ℝ _ _ _ _ _ _ _
      (cellJetFourierProductRange (E := E) K N)
      (coupledEnergyCellJetProductRangeFinite (E := E) K N)
      e.symm.toLinearEquiv.toLinearMap
  exact @Submodule.finiteDimensional_of_le ℝ _ _ _ _ _ _ hfinT hsub

end AVRegularity.CoupledEnergy.Galerkin

end
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory
open Filter
open scoped Topology
open AVRegularity.Analysis.Convolution
open AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
open AVenhance.Infra.Parabolic.FourierGalerkin
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Strong convergence of finite vector Fourier cutoffs on the torus. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance convergenceTorusMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance convergenceTorusAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance convergenceTorusCircleProbability : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance convergenceTorusProbability : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance

/-- Every scalar Fourier cutoff converges strongly in torus `L²`. -/
theorem scalarFourierProjection_tendsto (f : ScalarTorusL2) :
    Tendsto (fun N => scalarFourierProjection N f) atTop (𝓝 f) := by
  simpa [scalarFourierProjection_eq_realFourierScalarMap,
    realFourierProjectionCoefficients] using tendsto_realFourierProjection f

noncomputable def vectorCoordinateFamily :
    Lp E 2 (volume : Measure Torus) →L[ℝ]
      PiLp 2 (fun _ : Fin (Module.finrank ℝ E) => ScalarTorusL2) :=
  (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin (Module.finrank ℝ E) => ScalarTorusL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j => vectorFourierCoordinate (E := E) j)

omit [MeasurableSpace E] [BorelSpace E] in
theorem vectorCoordinateFamily_apply (f : Lp E 2 (volume : Measure Torus))
    (j : Fin (Module.finrank ℝ E)) :
    vectorCoordinateFamily (E := E) f j = vectorFourierCoordinate (E := E) j f := rfl

noncomputable def vectorCoordinateSynthesis :
    PiLp 2 (fun _ : Fin (Module.finrank ℝ E) => ScalarTorusL2) →L[ℝ]
      Lp E 2 (volume : Measure Torus) :=
  ∑ j : Fin (Module.finrank ℝ E),
    ((ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
      ((stdOrthonormalBasis ℝ E) j)).compLpL 2 volume).comp
        (PiLp.proj (𝕜 := ℝ) 2
          (fun _ : Fin (Module.finrank ℝ E) => ScalarTorusL2) j)

omit [MeasurableSpace E] [BorelSpace E] in
omit [MeasurableSpace E] [BorelSpace E] in
theorem vectorCoordinateFamily_reconstruct (f : Lp E 2 (volume : Measure Torus)) :
    vectorCoordinateSynthesis (E := E) (vectorCoordinateFamily (E := E) f) = f := by
  apply Lp.ext
  have hsum := Lp.coeFn_finsetSum Finset.univ (fun j : Fin (Module.finrank ℝ E) =>
    ((ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
      ((stdOrthonormalBasis ℝ E) j)).compLpL 2 volume)
      ((vectorCoordinateFamily (E := E) f) j))
  have hcoords : ∀ᵐ x ∂volume, ∀ j : Fin (Module.finrank ℝ E),
      (vectorCoordinateFamily (E := E) f) j x =
        inner ℝ ((stdOrthonormalBasis ℝ E) j) (f x) := by
    apply ae_all_iff.2
    intro j
    have hcoord := ContinuousLinearMap.coeFn_compLpL
      (L := InnerProductSpace.toDual ℝ E ((stdOrthonormalBasis ℝ E) j)) f
    filter_upwards [hcoord] with x hx
    rw [vectorCoordinateFamily_apply]
    exact hx
  have hmaps : ∀ᵐ x ∂volume, ∀ j : Fin (Module.finrank ℝ E),
      (((ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
        ((stdOrthonormalBasis ℝ E) j)).compLpL 2 volume)
        ((vectorCoordinateFamily (E := E) f) j)) x =
        (vectorCoordinateFamily (E := E) f) j x • ((stdOrthonormalBasis ℝ E) j) := by
    apply ae_all_iff.2
    intro j
    exact ContinuousLinearMap.coeFn_compLpL
      (L := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
        ((stdOrthonormalBasis ℝ E) j)) ((vectorCoordinateFamily (E := E) f) j)
  filter_upwards [hsum, hcoords, hmaps] with x hs hc hm
  simp only [vectorCoordinateSynthesis, sum_apply,
    ContinuousLinearMap.comp_apply, PiLp.proj_apply] at ⊢
  rw [hs, Finset.sum_apply]
  calc
    (∑ j : Fin (Module.finrank ℝ E),
      (((ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
        ((stdOrthonormalBasis ℝ E) j)).compLpL 2 volume)
        ((vectorCoordinateFamily (E := E) f) j)) x) =
      ∑ j : Fin (Module.finrank ℝ E),
        inner ℝ ((stdOrthonormalBasis ℝ E) j) (f x) • ((stdOrthonormalBasis ℝ E) j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hm j, hc j]
    _ = f x := (stdOrthonormalBasis ℝ E).sum_repr' (f x)

theorem vectorFourierProjection_eq_synthesis (N : ℕ)
    (f : Lp E 2 (volume : Measure Torus)) :
    vectorFourierProjection (E := E) N f =
      vectorCoordinateSynthesis (E := E)
        (WithLp.toLp 2 fun j => scalarFourierProjection N
          (vectorFourierCoordinate (E := E) j f)) := by
  have hcoords : vectorCoordinateFamily (E := E)
      (vectorFourierProjection (E := E) N f) =
      WithLp.toLp 2 (fun j : Fin (Module.finrank ℝ E) =>
        scalarFourierProjection N (vectorFourierCoordinate (E := E) j f)) := by
    apply PiLp.ext
    intro j
    change vectorFourierCoordinate (E := E) j
      (vectorFourierProjection (E := E) N f) = _
    rw [vectorFourierProjection_coordinate]
  calc
    vectorFourierProjection (E := E) N f =
        vectorCoordinateSynthesis (E := E)
          (vectorCoordinateFamily (E := E) (vectorFourierProjection N f)) :=
      (vectorCoordinateFamily_reconstruct (vectorFourierProjection N f)).symm
    _ = vectorCoordinateSynthesis (E := E)
        (WithLp.toLp 2 (fun j : Fin (Module.finrank ℝ E) =>
          scalarFourierProjection N (vectorFourierCoordinate (E := E) j f))) :=
      congrArg (vectorCoordinateSynthesis (E := E)) hcoords

theorem vectorFourierProjection_tendsto (f : Lp E 2 (volume : Measure Torus)) :
    Tendsto (fun N => vectorFourierProjection (E := E) N f) atTop (𝓝 f) := by
  have hcoords : Tendsto
      (fun N => WithLp.toLp 2 (fun j : Fin (Module.finrank ℝ E) =>
        scalarFourierProjection N (vectorFourierCoordinate (E := E) j f)))
      atTop (𝓝 (vectorCoordinateFamily (E := E) f)) := by
    have hpi : Tendsto
        (fun N : ℕ => fun j : Fin (Module.finrank ℝ E) =>
          scalarFourierProjection N (vectorFourierCoordinate (E := E) j f))
        atTop (𝓝 fun j => vectorFourierCoordinate (E := E) j f) :=
      (tendsto_pi_nhds).2 (fun j => scalarFourierProjection_tendsto
        (vectorFourierCoordinate (E := E) j f))
    have hpi' := ((PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin (Module.finrank ℝ E) => ScalarTorusL2)).symm.continuous.continuousAt.tendsto).comp hpi
    have hfamily : vectorCoordinateFamily (E := E) f =
        WithLp.toLp 2 (fun j : Fin (Module.finrank ℝ E) =>
          vectorFourierCoordinate (E := E) j f) := by
      apply PiLp.ext
      intro j
      exact vectorCoordinateFamily_apply f j
    rw [hfamily]
    exact hpi'
  have hrec := vectorCoordinateFamily_reconstruct (E := E) f
  have := (vectorCoordinateSynthesis (E := E)).continuous.continuousAt.tendsto.comp hcoords
  convert this using 1
  · funext N
    exact vectorFourierProjection_eq_synthesis N f
  · simp [hrec]

theorem cellVectorFourierProjection_tendsto (f :
    Lp E 2 (volume.restrict AVenhance.unitCube)) :
    Tendsto (fun N => cellVectorFourierProjection (E := E) N f) atTop (𝓝 f) := by
  have htorus := vectorFourierProjection_tendsto (cellToTorus f)
  have hcell := (torusToCell (E := E)).toContinuousLinearMap.continuous.continuousAt.tendsto.comp
    htorus
  convert hcell using 1
  · funext N
    rfl
  · simp [torusToCell_cellToTorus]

theorem cellJetFourierProjection_tendsto (K : ℕ)
    (D : JetL2 (volume.restrict AVenhance.unitCube) K E) :
    Tendsto (fun N => cellJetFourierProjection (E := E) K N D) atTop (𝓝 D) := by
  let e := PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : JetIndex2 K => Lp E 2 (volume.restrict AVenhance.unitCube))
  have hpi : Tendsto (fun N : ℕ => fun a : JetIndex2 K =>
      cellVectorFourierProjection (E := E) N (D a)) atTop
      (𝓝 fun a : JetIndex2 K => D a) := by
    apply (tendsto_pi_nhds).2
    intro a
    exact cellVectorFourierProjection_tendsto (D a)
  have hp : Tendsto (fun N => e.symm (fun a : JetIndex2 K =>
      cellVectorFourierProjection (E := E) N (D a))) atTop
      (𝓝 (e.symm fun a : JetIndex2 K => D a)) :=
    e.symm.continuous.continuousAt.tendsto.comp hpi
  convert hp using 1
  · funext N
    apply PiLp.ext
    intro a
    rfl
  · rfl

end AVRegularity.CoupledEnergy.Galerkin
end
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Filter Homogenization
open AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution
open AVRegularity.CoupledEnergy.Galerkin
open AVenhance.Infra.Torus AVenhance.Infra.Classical
open AVenhance.Infra.Parabolic.FourierGalerkin
open AVenhance.Infra.Parabolic.WeakUniqueness
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Restrict the cell Fourier cutoff to the periodic weak-jet carrier. -/

local instance torusProjectionMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance torusProjectionAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance torusProjectionCircleProbability : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance torusProjectionProbability : IsProbabilityMeasure
    (volume : Measure Torus) := inferInstance
local instance torusProjectionCellFinite : IsFiniteMeasure
    (volume.restrict AVenhance.unitCube) := by
  exact ⟨by
    simpa only [Measure.restrict_apply_univ] using
      AVenhance.Infra.Parabolic.WeakUniqueness.WeakAlgebra.weak_unitCube_volume_lt_top⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The vector-valued smooth jet obtained by cutting off each fiber coordinate. -/
noncomputable def torusJetFourierPolynomial {K : ℕ} (N : ℕ)
    (f : TorusHk K E) (a : JetIndex2 K) : Vec 2 → E := fun x =>
  ∑ j : Fin (Module.finrank ℝ E),
    torusJetCoordinateFourierPolynomial N f a ((stdOrthonormalBasis ℝ E) j) x •
      (stdOrthonormalBasis ℝ E) j

theorem torusJetFourierPolynomial_periodic {K : ℕ} (N : ℕ)
    (f : TorusHk K E) (a : JetIndex2 K) :
    AVenhance.IsZ2Periodic (torusJetFourierPolynomial N f a) := by
  intro n x
  simp only [torusJetFourierPolynomial]
  apply Finset.sum_congr rfl
  intro j hj
  rw [torusJetCoordinateFourierPolynomial_periodic]

theorem torusJetFourierPolynomial_inner_eq_sum {K : ℕ} (N : ℕ)
    (f : TorusHk K E) (a : JetIndex2 K) (e : E) (x : Vec 2) :
    inner ℝ e (torusJetFourierPolynomial N f a x) =
      ∑ j : Fin (Module.finrank ℝ E),
        torusJetCoordinateFourierPolynomial N f a ((stdOrthonormalBasis ℝ E) j) x *
          inner ℝ e ((stdOrthonormalBasis ℝ E) j) := by
  simp only [torusJetFourierPolynomial, inner_sum, real_inner_smul_right]

theorem torusJetFourierPolynomial_inner_contDiff {K : ℕ} (N : ℕ)
    (f : TorusHk K E) (a : JetIndex2 K) (e : E) :
    ContDiff ℝ ⊤ (fun x => inner ℝ e (torusJetFourierPolynomial N f a x)) := by
  rw [show (fun x => inner ℝ e (torusJetFourierPolynomial N f a x)) =
      fun x => ∑ j : Fin (Module.finrank ℝ E),
        torusJetCoordinateFourierPolynomial N f a ((stdOrthonormalBasis ℝ E) j) x *
          inner ℝ e ((stdOrthonormalBasis ℝ E) j) by
    funext x
    exact torusJetFourierPolynomial_inner_eq_sum N f a e x]
  apply ContDiff.sum
  intro j hj
  exact (torusJetCoordinateFourierPolynomial_contDiff N f a
    ((stdOrthonormalBasis ℝ E) j)).mul contDiff_const

theorem torusJetFourierPolynomial_inner_derivative {K : ℕ} (N : ℕ)
    (f : TorusHk K E) (j : Fin K) (w : DerivativeWord2 j.val) (e : E)
    (i : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad
        (fun y => inner ℝ e
          (torusJetFourierPolynomial N f (lowerIndex2 j w) y)) x i =
      inner ℝ e
        (torusJetFourierPolynomial N f (nextIndex2 j w i) x) := by
  rw [show (fun y => inner ℝ e
      (torusJetFourierPolynomial N f (lowerIndex2 j w) y)) =
      fun y => ∑ k : Fin (Module.finrank ℝ E),
        torusJetCoordinateFourierPolynomial N f (lowerIndex2 j w)
          ((stdOrthonormalBasis ℝ E) k) y * inner ℝ e ((stdOrthonormalBasis ℝ E) k) by
    funext y
    exact torusJetFourierPolynomial_inner_eq_sum N f (lowerIndex2 j w) e y]
  rw [GalerkinModeCalculus.spaceGrad_finset_sum Finset.univ]
  · rw [torusJetFourierPolynomial_inner_eq_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [show (fun y => torusJetCoordinateFourierPolynomial N f (lowerIndex2 j w)
        ((stdOrthonormalBasis ℝ E) k) y * inner ℝ e ((stdOrthonormalBasis ℝ E) k)) =
        fun y => inner ℝ e ((stdOrthonormalBasis ℝ E) k) *
          torusJetCoordinateFourierPolynomial N f (lowerIndex2 j w)
            ((stdOrthonormalBasis ℝ E) k) y by
      funext y
      ring]
    rw [GalerkinModeCalculus.spaceGrad_realConstant_mul
      ((torusJetCoordinateFourierPolynomial_contDiff N f (lowerIndex2 j w)
        ((stdOrthonormalBasis ℝ E) k)).of_le
          (show (1 : WithTop ℕ∞) ≤ ⊤ by exact le_top))]
    rw [torusJetCoordinateFourierPolynomial_derivative]
    ring
  · intro k hk
    exact (torusJetCoordinateFourierPolynomial_contDiff N f
      (lowerIndex2 j w) ((stdOrthonormalBasis ℝ E) k)).mul contDiff_const

noncomputable def torusJetCoordinatePolynomialCellLp {K : ℕ} (N : ℕ)
    (f : TorusHk K E) (a : JetIndex2 K) (e : E) :
    Lp ℝ 2 (volume.restrict AVenhance.unitCube) :=
  (weak_continuous_memL2On
    (torusJetCoordinateFourierPolynomial_contDiff N f a e).continuous).toLp
      (torusJetCoordinateFourierPolynomial N f a e)

noncomputable def torusJetFourierPolynomialCellLp {K : ℕ} (N : ℕ)
    (f : TorusHk K E) (a : JetIndex2 K) :
    Lp E 2 (volume.restrict AVenhance.unitCube) :=
  ∑ j : Fin (Module.finrank ℝ E),
    ((ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
      ((stdOrthonormalBasis ℝ E) j)).compLpL 2
        (volume.restrict AVenhance.unitCube))
      (torusJetCoordinatePolynomialCellLp N f a ((stdOrthonormalBasis ℝ E) j))

theorem torusJetFourierPolynomial_cellLp_ae {K : ℕ} (N : ℕ)
    (f : TorusHk K E) (a : JetIndex2 K) :
    torusJetFourierPolynomialCellLp N f a =ᵐ[volume.restrict AVenhance.unitCube]
      torusJetFourierPolynomial N f a := by
  have hsum := Lp.coeFn_finsetSum Finset.univ (fun j : Fin (Module.finrank ℝ E) =>
    ((ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
      ((stdOrthonormalBasis ℝ E) j)).compLpL 2
        (volume.restrict AVenhance.unitCube))
      (torusJetCoordinatePolynomialCellLp N f a ((stdOrthonormalBasis ℝ E) j)))
  have hterms : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube),
      ∀ j : Fin (Module.finrank ℝ E),
        (((ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
          ((stdOrthonormalBasis ℝ E) j)).compLpL 2
            (volume.restrict AVenhance.unitCube))
          (torusJetCoordinatePolynomialCellLp N f a ((stdOrthonormalBasis ℝ E) j))) x =
        torusJetCoordinateFourierPolynomial N f a ((stdOrthonormalBasis ℝ E) j) x •
          (stdOrthonormalBasis ℝ E) j := by
    apply ae_all_iff.2
    intro j
    have hmap := ContinuousLinearMap.coeFn_compLpL
      (L := ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
        ((stdOrthonormalBasis ℝ E) j))
      (torusJetCoordinatePolynomialCellLp N f a ((stdOrthonormalBasis ℝ E) j))
    have hq := (weak_continuous_memL2On
      (torusJetCoordinateFourierPolynomial_contDiff N f a
        ((stdOrthonormalBasis ℝ E) j)).continuous).coeFn_toLp
    filter_upwards [hmap, hq] with x hmap hq
    rw [hmap]
    simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply]
    change ((weak_continuous_memL2On
      (torusJetCoordinateFourierPolynomial_contDiff N f a
        ((stdOrthonormalBasis ℝ E) j)).continuous).toLp
        (torusJetCoordinateFourierPolynomial N f a
          ((stdOrthonormalBasis ℝ E) j))) x • (stdOrthonormalBasis ℝ E) j = _
    rw [hq]
  filter_upwards [hsum, hterms] with x hsum hterms
  change (∑ j : Fin (Module.finrank ℝ E),
      ((ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ)
        ((stdOrthonormalBasis ℝ E) j)).compLpL 2
        (volume.restrict AVenhance.unitCube))
        (torusJetCoordinatePolynomialCellLp N f a ((stdOrthonormalBasis ℝ E) j))) x =
    ∑ j : Fin (Module.finrank ℝ E),
      torusJetCoordinateFourierPolynomial N f a ((stdOrthonormalBasis ℝ E) j) x •
        (stdOrthonormalBasis ℝ E) j
  rw [hsum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  exact hterms j

theorem torusJetFourierPolynomial_memLp {K : ℕ} (N : ℕ)
    (f : TorusHk K E) (a : JetIndex2 K) :
    MemLp (torusJetFourierPolynomial N f a) 2
      (volume.restrict AVenhance.unitCube) := by
  exact (memLp_congr_ae (torusJetFourierPolynomial_cellLp_ae N f a)).1
    (Lp.memLp (torusJetFourierPolynomialCellLp N f a))

theorem torusJetFourierPolynomial_hasWeakJet {K : ℕ} (N : ℕ)
    (f : TorusHk K E) :
    HasOrderedWeakJetOn Set.univ (torusJetFourierPolynomial N f) := by
  intro j w i e
  have hcont := torusJetFourierPolynomial_inner_contDiff N f (lowerIndex2 j w) e
  have hcont1 : ContDiff ℝ (1 : WithTop ℕ∞)
      (fun x => inner ℝ e (torusJetFourierPolynomial N f (lowerIndex2 j w) x)) :=
    hcont.of_le (show (1 : WithTop ℕ∞) ≤ ⊤ by exact le_top)
  have hweak := HasWeakPartialDerivOn.of_contDiff (U := Set.univ) (i := i) hcont1
  have hderiv : (fun x =>
      (fderiv ℝ (fun y => inner ℝ e
        (torusJetFourierPolynomial N f (lowerIndex2 j w) y)) x) (basisVec i)) =
      fun x => inner ℝ e (torusJetFourierPolynomial N f (nextIndex2 j w i) x) := by
    funext x
    simpa [AVenhance.spaceGrad] using
      torusJetFourierPolynomial_inner_derivative N f j w e i x
  intro φ hφ hc hs
  rw [← hderiv]
  exact hweak φ hφ hc hs

noncomputable def torusJetFourierPolynomialFunction {K : ℕ} (N : ℕ)
    (f : TorusHk K E) : TorusHkFunction K E where
  jet := torusJetFourierPolynomial N f
  hasPeriodicWeakJet := ⟨torusJetFourierPolynomial_periodic N f,
    torusJetFourierPolynomial_memLp N f,
    torusJetFourierPolynomial_hasWeakJet N f⟩

noncomputable def torusJetFourierPolynomialToHk {K : ℕ} (N : ℕ)
    (f : TorusHk K E) : TorusHk K E :=
  (torusJetFourierPolynomialFunction N f).toHk

theorem torusJetCoordinate_cellToTorus_eq {K : ℕ} (f : TorusHk K E)
    (a : JetIndex2 K) (j : Fin (Module.finrank ℝ E)) :
    vectorFourierCoordinate (E := E) j
      (torusLpToVolume (cellToTorus (f.val a))) =
    torusLpToVolume
      ((weakProjection_realCellToTorus_memLp
        ((InnerProductSpace.toDual ℝ E ((stdOrthonormalBasis ℝ E) j)).comp_memLp'
          (f.toFunction.hasPeriodicWeakJet.2.1 a))).toLp
        (AVenhance.Infra.Torus.periodicToTorus
          (torusJetCoordinateValue f a ((stdOrthonormalBasis ℝ E) j)))) := by
  cases coupledEnergy_torusMeasure_eq_volume
  let e := (stdOrthonormalBasis ℝ E) j
  have hFW := f.toFunction.hasPeriodicWeakJet
  have hF : MemLp (torusJetCoordinateValue f a e) 2
      (volume.restrict AVenhance.unitCube) :=
    (InnerProductSpace.toDual ℝ E e).comp_memLp' (hFW.2.1 a)
  have hLpEq :
      (weakProjection_realCellToTorus_memLp hF).toLp
          (AVenhance.Infra.Torus.periodicToTorus (torusJetCoordinateValue f a e)) =
        (hF.comp_measurePreserving
          measurePreserving_unitTorusRepresentative_cell).toLp
          (fun y => torusJetCoordinateValue f a e
            (AVenhance.Infra.Torus.unitTorusRepresentative 2 y)) := by
    apply Lp.ext
    rfl
  have hD : f.val a =ᵐ[volume.restrict AVenhance.unitCube] f.toFunction.jet a := by
    exact (periodicJetRepresentative_ae f.val a).symm
  have hraw := cellToTorus_coordinate_raw (D := f.val a)
    (F := f.toFunction.jet a) j hD hF
  change vectorFourierCoordinate (E := E) j
      (torusLpToVolume (cellToTorus (f.val a))) =
      torusLpToVolume
        ((hF.comp_measurePreserving
          measurePreserving_unitTorusRepresentative_cell).toLp
          (fun y => torusJetCoordinateValue f a e
            (AVenhance.Infra.Torus.unitTorusRepresentative 2 y))) at hraw
  rw [← hLpEq] at hraw
  exact hraw

private theorem lp_ae_eq_of_eq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : Lp ℝ 2 μ} (h : f = g) : f =ᵐ[μ] g := by
  have hsub : f - g = 0 := sub_eq_zero.mpr h
  have hcoe := Lp.coeFn_sub f g
  rw [hsub] at hcoe
  filter_upwards [hcoe.symm, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ)]
    with x hx hz
  change f x - g x = ((0 : Lp ℝ 2 μ) : α → ℝ) x at hx
  have hx' : f x - g x = 0 := by
    rw [hz] at hx
    exact hx
  exact sub_eq_zero.mp hx'

noncomputable def torusJetCoordinatePolynomialTorusLp {K : ℕ} (N : ℕ)
    (f : TorusHk K E) (a : JetIndex2 K) (e : E) : ScalarTorusL2 :=
  (weakProjection_realCellToTorus_memLp
    (weak_continuous_memL2On
      (torusJetCoordinateFourierPolynomial_contDiff N f a e).continuous)).toLp
    (AVenhance.Infra.Torus.periodicToTorus
      (torusJetCoordinateFourierPolynomial N f a e))

theorem scalarFourierProjection_torusJetCoordinate {K : ℕ} (N : ℕ)
    (f : TorusHk K E) (a : JetIndex2 K) (j : Fin (Module.finrank ℝ E)) :
    scalarFourierProjection N
      (vectorFourierCoordinate (E := E) j
        (torusLpToVolume (cellToTorus (f.val a)))) =
      torusJetCoordinatePolynomialTorusLp N f a ((stdOrthonormalBasis ℝ E) j) := by
  cases coupledEnergy_torusMeasure_eq_volume
  have hsource := torusJetCoordinate_cellToTorus_eq f a j
  have hsourceAE := lp_ae_eq_of_eq hsource
  let raw := torusJetCoordinateValue f a ((stdOrthonormalBasis ℝ E) j)
  have hF : MemLp raw 2 (volume.restrict AVenhance.unitCube) :=
    (InnerProductSpace.toDual ℝ E ((stdOrthonormalBasis ℝ E) j)).comp_memLp'
      (f.toFunction.hasPeriodicWeakJet.2.1 a)
  have hmem := weakProjection_realCellToTorus_memLp hF
  have hclassAE : torusLpToVolume (hmem.toLp (AVenhance.Infra.Torus.periodicToTorus raw))
      =ᵐ[volume] AVenhance.Infra.Torus.periodicToTorus raw := by
    filter_upwards [torusLpToVolume_coeFn
      (hmem.toLp (AVenhance.Infra.Torus.periodicToTorus raw)), hmem.coeFn_toLp]
      with x hx₁ hx₂
    exact hx₁.trans hx₂
  have hcoordinateAE :
      vectorFourierCoordinate (E := E) j
          (torusLpToVolume (cellToTorus (f.val a))) =ᵐ[volume]
        AVenhance.Infra.Torus.periodicToTorus raw := by
    exact hsourceAE.trans hclassAE
  have hcoeff :
      modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
        (fun x => vectorFourierCoordinate (E := E) j
          (torusLpToVolume (cellToTorus (f.val a))) x) =
      modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
        (AVenhance.Infra.Torus.periodicToTorus
          (torusJetCoordinateValue f a ((stdOrthonormalBasis ℝ E) j))) := by
    apply PiLp.ext
    intro k
    simp only [modeProjectionCoefficients, PiLp.toLp_apply]
    apply integral_congr_ae
    filter_upwards [hcoordinateAE] with x hx
    rw [hx]
  rw [scalarFourierProjection_eq_realFourierScalarMap]
  rw [hcoeff]
  simpa [torusJetCoordinatePolynomialTorusLp, torusJetCoordinateFourierPolynomial,
    AVenhance.Infra.Torus.periodicToTorus] using
      WeakProjectionConvergence.weakFourierSynthesis_eq_expansionTransfer N
        (modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
          (AVenhance.Infra.Torus.periodicToTorus
            (torusJetCoordinateValue f a ((stdOrthonormalBasis ℝ E) j))))

theorem torusJetFourierPolynomialCellLp_coordinate_toTorus {K : ℕ} (N : ℕ)
    (f : TorusHk K E) (a : JetIndex2 K) (j : Fin (Module.finrank ℝ E)) :
    vectorFourierCoordinate (E := E) j
        (torusLpToVolume (cellToTorus
          (torusJetFourierPolynomialCellLp N f a))) =
      torusJetCoordinatePolynomialTorusLp N f a ((stdOrthonormalBasis ℝ E) j) := by
  cases coupledEnergy_torusMeasure_eq_volume
  apply Lp.ext
  have hclass := torusLpToVolume_coeFn (cellToTorus
    (torusJetFourierPolynomialCellLp N f a))
  have htransfer := cellToTorus_ae (torusJetFourierPolynomialCellLp N f a)
  have hpoly := torusJetFourierPolynomial_cellLp_ae N f a
  have hpolyRep := measurePreserving_unitTorusRepresentative_cell.quasiMeasurePreserving.ae hpoly
  have hcoord := ContinuousLinearMap.coeFn_compLpL
    (L := InnerProductSpace.toDual ℝ E ((stdOrthonormalBasis ℝ E) j))
    (torusLpToVolume (cellToTorus (torusJetFourierPolynomialCellLp N f a)))
  have htargetMem := weakProjection_realCellToTorus_memLp
    (weak_continuous_memL2On
      (torusJetCoordinateFourierPolynomial_contDiff N f a
        ((stdOrthonormalBasis ℝ E) j)).continuous)
  have htargetClass := torusLpToVolume_coeFn
    (torusJetCoordinatePolynomialTorusLp N f a ((stdOrthonormalBasis ℝ E) j))
  have htargetRaw :
      torusJetCoordinatePolynomialTorusLp N f a ((stdOrthonormalBasis ℝ E) j) =ᵐ[volume]
        AVenhance.Infra.Torus.periodicToTorus
          (torusJetCoordinateFourierPolynomial N f a ((stdOrthonormalBasis ℝ E) j)) := by
    exact htargetMem.coeFn_toLp
  filter_upwards [hclass, htransfer, hpolyRep, hcoord, htargetClass, htargetRaw]
    with x hclassx htransferx hpolyx hcoordx htargetClassx htargetRawx
  change ((InnerProductSpace.toDual ℝ E ((stdOrthonormalBasis ℝ E) j)).compLpL
      2 volume (torusLpToVolume (cellToTorus
        (torusJetFourierPolynomialCellLp N f a))) x) =
    torusJetCoordinatePolynomialTorusLp N f a ((stdOrthonormalBasis ℝ E) j) x
  rw [hcoordx, hclassx, htransferx]
  change inner ℝ ((stdOrthonormalBasis ℝ E) j)
      (torusJetFourierPolynomialCellLp N f a (AVenhance.Infra.Torus.unitTorusRepresentative 2 x)) =
    torusJetCoordinatePolynomialTorusLp N f a ((stdOrthonormalBasis ℝ E) j) x
  rw [hpolyx]
  rw [torusJetFourierPolynomial_inner_eq_sum]
  simp only [OrthonormalBasis.inner_eq_ite]
  simp
  rw [htargetRawx]
  rfl

theorem cellVectorFourierProjection_eq_polynomialCellLp {K : ℕ} (N : ℕ)
    (f : TorusHk K E) (a : JetIndex2 K) :
    cellVectorFourierProjection (E := E) N (f.val a) =
      torusJetFourierPolynomialCellLp N f a := by
  cases coupledEnergy_torusMeasure_eq_volume
  apply (cellToTorus (E := E)).injective
  have h1 := cellToTorus_cellVectorFourierProjection N (f.val a)
  have h2 := vectorFourierProjection_eq_synthesis N (cellToTorus (f.val a))
  have h3 :
      WithLp.toLp 2 (fun j : Fin (Module.finrank ℝ E) =>
        scalarFourierProjection N
          (vectorFourierCoordinate (E := E) j (cellToTorus (f.val a)))) =
      WithLp.toLp 2 (fun j : Fin (Module.finrank ℝ E) =>
        torusLpToVolume
          (torusJetCoordinatePolynomialTorusLp N f a ((stdOrthonormalBasis ℝ E) j))) := by
    apply PiLp.ext
    intro j
    simpa only [torusLpToVolume] using
      scalarFourierProjection_torusJetCoordinate N f a j
  have h4 :
      WithLp.toLp 2 (fun j : Fin (Module.finrank ℝ E) =>
        torusJetCoordinatePolynomialTorusLp N f a ((stdOrthonormalBasis ℝ E) j)) =
      vectorCoordinateFamily (E := E) (torusLpToVolume (cellToTorus
        (torusJetFourierPolynomialCellLp N f a))) := by
    apply PiLp.ext
    intro j
    simpa only [vectorCoordinateFamily_apply] using
      (torusJetFourierPolynomialCellLp_coordinate_toTorus N f a j).symm
  have h5 := vectorCoordinateFamily_reconstruct
    (torusLpToVolume (cellToTorus (torusJetFourierPolynomialCellLp N f a)))
  exact h1.trans (h2.trans (congrArg (vectorCoordinateSynthesis (E := E)) h3 |>.trans
    (congrArg (vectorCoordinateSynthesis (E := E)) h4 |>.trans h5)))

theorem cellJetFourierProjection_eq_polynomialToHk {K : ℕ} (N : ℕ)
    (f : TorusHk K E) :
    cellJetFourierProjection (E := E) K N f.val =
      (torusJetFourierPolynomialToHk N f).val := by
  apply PiLp.ext
  intro a
  calc
    cellJetFourierProjection (E := E) K N f.val a =
        cellVectorFourierProjection (E := E) N (f.val a) := rfl
    _ = torusJetFourierPolynomialCellLp N f a :=
      cellVectorFourierProjection_eq_polynomialCellLp N f a
    _ = (torusJetFourierPolynomialToHk N f).val a := by
      apply Lp.ext
      filter_upwards [torusJetFourierPolynomial_cellLp_ae N f a,
        torusJetToL2_ae (torusJetFourierPolynomial N f)
          (torusJetFourierPolynomial_memLp N f) a] with x h₁ h₂
      exact h₁.trans h₂.symm

end AVRegularity.CoupledEnergy.Galerkin
end
end
end
