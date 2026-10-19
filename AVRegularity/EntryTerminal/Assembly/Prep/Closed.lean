-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.EntryTerminal.Ingredients.PrepAnchor.PrepAnchor
import AVRegularity.EntryTerminal.Ingredients.PrepCover.PrepCover
import AVRegularity.EntryTerminal.Ingredients.PrepChart.Chart
import AVRegularity.EntryTerminal.Ingredients.PrepFamily.PrepFamily
import AVRegularity.EntryTerminal.Ingredients.RawJointAbs.RawJointAbs
import AVRegularity.EntryTerminal.Ingredients.PrepCore.PrepCore
import AVRegularity.EntryTerminal.Ingredients.PrepNorm.PrepNorm
import AVRegularity.EntryTerminal.Ingredients.PrepInterp.PrepInterp
import AVRegularity.EntryTerminal.Ingredients.ScaleFacts.ScaleFacts
import AVRegularity.CycleJoint.Assembly.ScalarResidualContraction
import AVRegularity.CycleJoint.Assembly.CycleJointOfSeam
import AVRegularity.CycleWords.Seam.S3CycleSeam
import AVRegularity.CycleWords.Seam.B1PlainStage
public import AVRegularity.CycleJoint.Assembly.SeamStatement
public import AVRegularity.EntryTerminal.Assembly.Route.Ingredients

@[expose] public section

section
open AVRegularity.EntryTerminal.Ingredients AVRegularity.CycleJointProofs.Assembly
namespace AVRegularity.EntryTerminal.Route

/-! **The capped preparation from `cycle_seam`.** Every part of `preparation_of_split` is proved except
`RawJointAbsStatement`. That is the `RawJointGenStatement` (`rawJointAbs_of_gen`), assembled from
the patches by `rawJointGen_of_patches`: `patchJointGen` needs `CycleSeamStatement`, and the rest
(the weighted pullback, word-chain uniqueness, `planeTorus`, `periodizedSum`,
`centreCounting`, `scalarContraction`) are proved. So `entry_terminal_preparation` depends
only on `cycle_seam`. -/

/-- **The capped preparation, from `cycle_seam` alone.** -/
theorem preparation_of_seam (hseam : CycleSeamStatement.{0, 0}) : PreparationStatement :=
  preparation_of_split prepAnchor prepCover prepChart prepFamilyPart
    (rawJointAbs_of_gen (rawJointGen_of_patches (patchJointGen weightedPullback hseam wordChainUnique)
      planeTorus (periodizedRadialSum_of_periodizedSum periodizedSum) centreCounting
      (scalarContractionVanishing_of_scalarContraction scalarContraction)))
    prepCore prepNorm prepInterp scaleFacts

end AVRegularity.EntryTerminal.Route
end

section
namespace AVRegularity.EntryTerminal.Route

/-! **The capped preparation is proved.** `cycle_seam` is proved (`cycleSeamStatement_of_quietMarginDatum`
at the `quietMarginDatum`), and `preparation_of_seam` depends only on it. So the text
copy `PreparationStatement` of `entry_terminal_preparation` holds. -/

/-- **The terminal capped preparation** (the text of `entry_terminal_preparation`). -/
theorem terminalPreparation : PreparationStatement :=
  preparation_of_seam (CycleWords.Seam.cycleSeamStatement_of_quietMarginDatum.{0, 0}
    CycleWords.Seam.quietMarginDatum)

end AVRegularity.EntryTerminal.Route
end
