-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Analysis.Convolution.Kernel.Spatial
public import AVRegularity.Sobolev.FactorialShift
public import AVenhance.Infra.Parabolic.FourierGalerkin.ProductGradientRepresentative

/-! Probability torus and open-cell L² identifications for convolution. -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization
open AVenhance.Infra.Torus AVenhance.Infra.Parabolic.FourierGalerkin

namespace AVRegularity.Analysis.Convolution

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem measurePreserving_torusQuotient_cell :
    MeasurePreserving torusQuotient (volume.restrict AVenhance.unitCube) torusMeasure :=
  measurePreserving_toUnitTorus_unitCube

theorem torusQuotient_latticeShift (k : Fin 2 → ℤ) :
    torusQuotient (AVenhance.latticeShift k) = 0 := by
  ext i
  change ((k i : ℝ) : AddCircle (1 : ℝ)) = 0
  simp

theorem ae_torusQuotient {p : UnitAddTorus (Fin 2) → Prop}
    (hp : ∀ᵐ t ∂torusMeasure, p t) :
    ∀ᵐ x ∂(volume : Measure (Vec 2)), p (torusQuotient x) := by
  have hcell := measurePreserving_torusQuotient_cell.quasiMeasurePreserving.ae hp
  rw [← Measure.restrict_congr_set WeakGradientPeriodization.periodCell_ae_unitCube] at hcell
  have hcell' := (ae_restrict_iff' WeakGradientPeriodization.periodCell_measurable).mp hcell
  have htrans (z : WeakGradientPeriodization.PeriodTranslations) :
      ∀ᵐ x ∂(volume : Measure (Vec 2)),
        (z : Vec 2) + x ∈ WeakGradientPeriodization.PeriodCell → p (torusQuotient x) := by
    have h := (measurePreserving_add_left volume (z : Vec 2)).quasiMeasurePreserving.ae hcell'
    obtain ⟨k, hk⟩ := WeakGradientPeriodization.periodTranslation_integerVector z
    filter_upwards [h] with x hx
    rw [map_add, hk, torusQuotient_latticeShift, zero_add] at hx
    simpa only [hk] using hx
  have hall := ae_all_iff.mpr htrans
  filter_upwards [hall, WeakGradientPeriodization.periodTranslations_fundamentalDomain.ae_covers]
    with x hx hcover
  obtain ⟨z, hz⟩ := hcover
  exact hx z hz

theorem measurePreserving_unitTorusRepresentative_cell :
    MeasurePreserving (unitTorusRepresentative 2) torusMeasure
      (volume.restrict AVenhance.unitCube) := by
  let e := UnitAddTorus.measurableEquivPiIoc (fun _ : Fin 2 => (0 : ℝ))
  have hg : Measurable (unitTorusRepresentative 2) := by
    change Measurable (Subtype.val ∘ e)
    exact measurable_subtype_coe.comp e.measurable
  have hgf : ((unitTorusRepresentative 2) ∘ torusQuotient) =ᵐ[volume.restrict AVenhance.unitCube] id := by
    have hm : MeasurableSet AVenhance.unitCube := by
      simpa [AVenhance.unitCube, Set.pi] using
        (MeasurableSet.univ_pi' (fun _ : Fin 2 =>
          (measurableSet_Ioo : MeasurableSet (Set.Ioo (0 : ℝ) 1))))
    filter_upwards [ae_restrict_mem hm] with x hx
    change unitTorusRepresentative 2 (toUnitTorus 2 x) = x
    apply unitTorusRepresentative_eq_of_mem_unitCell
    intro i
    have hi := hx i (Set.mem_univ i)
    simpa using (show x i ∈ Set.Ioc (0 : ℝ) 1 from ⟨hi.1, hi.2.le⟩)
  refine ⟨hg, ?_⟩
  rw [← measurePreserving_torusQuotient_cell.map_eq,
    Measure.map_map hg measurePreserving_torusQuotient_cell.measurable,
    Measure.map_congr hgf, Measure.map_id]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Pullback from the normalized torus to the cell Sobolev L² measure. -/
def torusToCell : Lp E 2 torusMeasure →ₗᵢ[ℝ]
    Lp E 2 (volume.restrict AVenhance.unitCube) :=
  Lp.compMeasurePreservingₗᵢ ℝ torusQuotient measurePreserving_torusQuotient_cell

/-- Transfer from the cell to the normalized torus by its half-open selector. -/
def cellToTorus : Lp E 2 (volume.restrict AVenhance.unitCube) →ₗᵢ[ℝ]
    Lp E 2 torusMeasure :=
  Lp.compMeasurePreservingₗᵢ ℝ (unitTorusRepresentative 2)
    measurePreserving_unitTorusRepresentative_cell

theorem torusToCell_ae (f : Lp E 2 torusMeasure) :
    torusToCell f =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => f (torusQuotient x) :=
  Lp.coeFn_compMeasurePreserving f measurePreserving_torusQuotient_cell

theorem cellToTorus_ae (f : Lp E 2 (volume.restrict AVenhance.unitCube)) :
    cellToTorus f =ᵐ[torusMeasure] periodicToTorus f :=
  Lp.coeFn_compMeasurePreserving f measurePreserving_unitTorusRepresentative_cell

theorem torusToCell_cellToTorus (f : Lp E 2 (volume.restrict AVenhance.unitCube)) :
    torusToCell (cellToTorus f) = f := by
  apply Lp.ext
  have hf := measurePreserving_torusQuotient_cell.quasiMeasurePreserving.ae
    (cellToTorus_ae f)
  have hm : MeasurableSet AVenhance.unitCube := by
    simpa [AVenhance.unitCube, Set.pi] using
      (MeasurableSet.univ_pi' (fun _ : Fin 2 =>
        (measurableSet_Ioo : MeasurableSet (Set.Ioo (0 : ℝ) 1))))
  filter_upwards [torusToCell_ae (cellToTorus f), hf, ae_restrict_mem hm] with x hx hfx hxcell
  rw [hx, hfx]
  change f (unitTorusRepresentative 2 (toUnitTorus 2 x)) = f x
  rw [unitTorusRepresentative_eq_of_mem_unitCell]
  intro i
  have hi := hxcell i (Set.mem_univ i)
  simpa using (show x i ∈ Set.Ioc (0 : ℝ) 1 from ⟨hi.1, hi.2.le⟩)

theorem cellToTorus_torusToCell (f : Lp E 2 torusMeasure) : cellToTorus (torusToCell f) = f := by
  apply Lp.ext
  have hf := measurePreserving_unitTorusRepresentative_cell.quasiMeasurePreserving.ae
    (torusToCell_ae f)
  filter_upwards [cellToTorus_ae (torusToCell f), hf] with x hx hfx
  rw [hx]
  change torusToCell f (unitTorusRepresentative 2 x) = f x
  rw [hfx]
  exact congrArg f (toUnitTorus_unitTorusRepresentative 2 x)

end AVRegularity.Analysis.Convolution
