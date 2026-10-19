-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.Frontier.GradeRows.Producer
import AVRegularity.Construction.Preservation.Frontier.MarkerReadout.Producer
public import AVRegularity.Construction.Preservation.Assembly.SuccessorResidualIdentitiesOfIngredients

/-! The grade frontier: the three grade productions, combined, give `GradeFrontierStatement`. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Frontier

/-- The grade case of the frontier production statement. -/
theorem grade_frontier {α s q : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    Assembly.GradeFrontierStatement α s q ζ :=
  frontier_production_of_analytic_inputs α s q ζ hζ true
    (frontier_analytic_production_and α s q ζ hζ hq.1 true
      (grade_rows_production hα₀ hα₁ hs₀ hs₁ hq hζ)
      (marker_readout_production hα₀ hα₁ hs₀ hs₁ hq ζ true)
      (grade_source_energy_production hα₀ hα₁ hs₀ hs₁ hq hζ))

end AVRegularity.Construction.Preservation.Frontier
