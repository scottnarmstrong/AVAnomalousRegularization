-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Reconstruction.PhysicalLiftProof
public import AVRegularity.CycleComparison.Assembly.OfPhysicalLift

section
/-! **The assembled statements of the comparison proposition**. The physical
reconstruction (`Reconstruction.physicalLift_proof`) is the statement
`PhysicalLiftStatement`; with the error clause it gives the reconstruction
(`reconstruction_of_physicalLift`), and with the remaining ingredients
`cycle_comparison` (`cycle_comparison_of_ingredients`). One declaration per step keeps each
definitional unfolding of a statement in its own declaration. -/

@[expose] public section

universe u v w x

namespace AVRegularity.CycleComparison.Assembly

/-- The physical reconstruction, as the statement `PhysicalLiftStatement`. -/
theorem physicalLift_holds : PhysicalLiftStatement.{u, v, w, x} :=
  Reconstruction.physicalLift_proof

/-- The reconstruction, as the statement `ReconstructionStatement`. -/
theorem reconstruction_holds : ReconstructionStatement.{u, v, w, x} :=
  reconstruction_of_physicalLift physicalLift_holds

/-- `cycle_comparison`, as the statement `ComparisonStatement`. -/
theorem comparison_holds : ComparisonStatement.{u, v, w, x} :=
  cycle_comparison_of_ingredients reconstruction_holds ocTrimmedQuietTimes
    fun _ _ _ _ _ _ => subset_rfl

end AVRegularity.CycleComparison.Assembly
end
end

section
/-! # The comparison proposition on the trimmed quiet times

`CycleComparisonTrimmedStatement` is the statement of `cycle_comparison`, whose premise `hquiet`
asserts fast independence on the trimmed quiet times
`ocTrimmedQuietTimes α q Λ ζ m ∩ Set.Icc tp (tp + Tobs)`. The text is
`Assembly.ComparisonStatement`, and `cycle_comparison_trimmed` proves it. The proof reads the
premise `T.IsQuiet` only through fast independence and the summed transport identity.

The trimmed set is contained in the quiet times, so the premise follows from fast independence on
all quiet times. The assembly proves the text for every quiet-time set containing the trimmed one
(`ComparisonStatementOn`, `cycle_comparison_of_ingredients`); the statement on all quiet times is
its instance at `ocQuietTimes`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal

universe u v w x

namespace AVRegularity.CycleComparison.Assembly

/-- **The comparison proposition**: `cycle_comparison`, with `hquiet` on the trimmed quiet times. -/
def CycleComparisonTrimmedStatement : Prop :=
  ComparisonStatement.{u, v, w, x}

/-- **`cycle_comparison`.** -/
theorem cycle_comparison_trimmed : CycleComparisonTrimmedStatement.{u, v, w, x} :=
  comparison_holds

end AVRegularity.CycleComparison.Assembly
end
end
