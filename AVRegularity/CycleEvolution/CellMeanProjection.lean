-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.FibreScalarSeriesHighIncrementBound
public import AVRegularity.Definitions.CycleEvolution.IsFibreGraph
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Integral.Prod

/-! The actual mean-free cell projection: measurability, zero mean, and an L² operator. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev

namespace AVRegularity.CycleEvolution

/-- The unit cell has volume one. -/
theorem cellCube_volume_one : volume AVenhance.unitCube = 1 := by
  unfold AVenhance.unitCube
  rw [volume_pi, Measure.pi_pi]
  simp [Real.volume_Ioo]

local instance : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using cellCube_volume_one⟩

/-- Constants as cell L² classes. -/
def cellConstantCLM : ℂ →L[ℝ] ComplexCellL2 :=
  Lp.constL 2 (volume.restrict AVenhance.unitCube) ℝ

/-- A constant class has its literal constant representative almost everywhere. -/
theorem cellConstantCLM_ae (c : ℂ) : cellConstantCLM c =ᵐ[volume.restrict AVenhance.unitCube]
    fun _ => c := Lp.coeFn_const 2 _ c

/-- The cell mean preserves joint measurability of the source. -/
theorem cellMean_measurable {f : ℝ → Vec 2 → ℂ}
    (hf : Measurable fun p : ℝ × Vec 2 => f p.1 p.2) :
    Measurable (fun t => cellMean (f t)) :=
  hf.stronglyMeasurable.integral_prod_right.measurable

/-- Mean subtraction preserves joint measurability. -/
theorem cellQ0_measurable {f : ℝ → Vec 2 → ℂ}
    (hf : Measurable fun p : ℝ × Vec 2 => f p.1 p.2) :
    Measurable (fun p : ℝ × Vec 2 => cellQ0 (f p.1) p.2) :=
  hf.sub ((cellMean_measurable hf).comp measurable_fst)

/-- Mean subtraction preserves L² membership on the unit cell. -/
theorem cellQ0_memLp {f : Vec 2 → ℂ} (hf : MemLp f 2 (volume.restrict AVenhance.unitCube)) :
    MemLp (cellQ0 f) 2 (volume.restrict AVenhance.unitCube) :=
  hf.sub (memLp_const (cellMean f))

/-- The mean-free projection has mean zero for every cell L² function. -/
theorem cellQ0_mean {f : Vec 2 → ℂ} (hf : MemLp f 2 (volume.restrict AVenhance.unitCube)) :
    cellMean (cellQ0 f) = 0 := by
  unfold cellMean cellQ0
  rw [integral_sub (hf.integrable (by norm_num)) (integrable_const _), integral_const]
  simp [cellMean]

end AVRegularity.CycleEvolution
