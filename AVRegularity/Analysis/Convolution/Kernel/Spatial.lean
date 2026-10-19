-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Analysis.Convolution.Kernel.MultiplierUniformOrder
public import AVenhance.Infra.Torus.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! Plane and torus realizations of the fixed-displacement averages. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization

namespace AVRegularity.Analysis.Convolution

/-- Spatial displacement `z ↦ r H z`. -/
def displacement (r : ℝ) (H : Vec 2 →L[ℝ] Vec 2) : Vec 2 →+ Vec 2 :=
  (r • H).toLinearMap.toAddMonoidHom

@[simp] theorem displacement_apply (r : ℝ) (H : Vec 2 →L[ℝ] Vec 2) (z : Vec 2) :
    displacement r H z = r • H z := rfl

theorem continuous_displacement (r : ℝ) (H : Vec 2 →L[ℝ] Vec 2) :
    Continuous (displacement r H) := (r • H).continuous

/-- Quotient the project coordinates to the unit torus. -/
def torusQuotient : Vec 2 →+ UnitAddTorus (Fin 2) where
  toFun := AVenhance.Infra.Torus.toUnitTorus 2
  map_zero' := by
    ext i
    exact AddCircle.coe_zero (1 : ℝ)
  map_add' := by
    intro x y
    ext i
    exact AddCircle.coe_add (1 : ℝ) (x i) (y i)

theorem continuous_torusQuotient : Continuous torusQuotient := by
  apply continuous_pi
  intro i
  change Continuous (fun x : Vec 2 => (x i : UnitAddCircle))
  exact (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_apply i)

/-- Probability Haar measure matching integration over the unit cell. -/
def torusMeasure : Measure (UnitAddTorus (Fin 2)) :=
  Measure.pi (fun _ : Fin 2 => AddCircle.haarAddCircle)

instance : torusMeasure.IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure
    (Measure.pi (fun _ : Fin 2 => AddCircle.haarAddCircle)))

instance : IsProbabilityMeasure torusMeasure :=
  inferInstanceAs (IsProbabilityMeasure
    (Measure.pi (fun _ : Fin 2 => AddCircle.haarAddCircle)))

/-- `S_{r,H}` on plane-valued `L²`. -/
def planeAveragingOperator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (r : ℝ) (H : Vec 2 →L[ℝ] Vec 2)
    (k : Vec 2 → ℝ) (hk : Integrable k) :
    Lp E 2 (volume : Measure (Vec 2)) →L[ℝ] Lp E 2 (volume : Measure (Vec 2)) :=
  averagingOperator (displacement r H) (continuous_displacement r H) k hk

/-- `S_{r,H}` on the normalized two-dimensional torus. -/
def torusAveragingOperator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (r : ℝ) (H : Vec 2 →L[ℝ] Vec 2)
    (k : Vec 2 → ℝ) (hk : Integrable k) :
    Lp E 2 torusMeasure →L[ℝ] Lp E 2 torusMeasure :=
  averagingOperator (torusQuotient.comp (displacement r H))
    (continuous_torusQuotient.comp (continuous_displacement r H)) k hk

end AVRegularity.Analysis.Convolution
