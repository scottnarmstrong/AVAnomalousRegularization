-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.

module

import AVRegularity.Statements.Main.InteriorRegularity
import AVRegularity.Statements.Main.InteriorRegularityConstruction
import AVRegularity.Statements.Main.UniformAnomalousDissipation
import AVRegularity.Statements.Main.UniformAnomalousDissipationConstruction
import AVRegularity.Statements.Main.InteriorRegularityAndDissipation
import AVRegularity.Statements.Main.LocalInteriorRegularity
import AVRegularity.Statements.Main.VanishingDiffusivityLimits
import AVRegularity.Statements.Main.VanishingDiffusivityLimitsLocal
import AVRegularity.Statements.Construction.ExistsFastProfile
import AVRegularity.Statements.Construction.ExistsOCStreamSeq
import AVRegularitySolution

/-!
# Axioms of the main results

Prints the axioms of every main theorem, of the two existence theorems for the
construction, and of the 11 theorems of the comparator Challenge as proved in the
Solution. Run as `lake env lean scripts/Axioms.lean`;
`python3 scripts/check-axioms.py` runs it and checks that each theorem depends on
no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms AVRegularity.interior_regularity
#print axioms AVRegularity.interior_regularity_construction
#print axioms AVRegularity.uniform_anomalous_dissipation
#print axioms AVRegularity.uniform_anomalous_dissipation_construction
#print axioms AVRegularity.interior_regularity_and_dissipation
#print axioms AVRegularity.local_interior_regularity
#print axioms AVRegularity.vanishing_diffusivity_limits
#print axioms AVRegularity.vanishing_diffusivity_limits_local
#print axioms AVRegularity.exists_isFastProfile
#print axioms AVRegularity.exists_isOCStreamSeq
#print axioms AVRegularityChallenge.interior_regularity
#print axioms AVRegularityChallenge.uniform_anomalous_dissipation
#print axioms AVRegularityChallenge.interior_regularity_and_dissipation
#print axioms AVRegularityChallenge.exists_isFastProfile
#print axioms AVRegularityChallenge.existsUnique_streamFlow
#print axioms AVRegularityChallenge.exists_isOCStreamSeq
#print axioms AVRegularityChallenge.interior_regularity_construction
#print axioms AVRegularityChallenge.uniform_anomalous_dissipation_construction
#print axioms AVRegularityChallenge.local_interior_regularity
#print axioms AVRegularityChallenge.vanishing_diffusivity_limits
#print axioms AVRegularityChallenge.vanishing_diffusivity_limits_local
