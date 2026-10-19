-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.EntryTerminal.Ingredients.SeedEnvelope.Assembly
import AVRegularity.EntryTerminal.Assembly.Seed.OfParts
import AVRegularity.EntryTerminal.Assembly.Seed.SeedRepricing
public import AVRegularity.EntryTerminal.Assembly.Route.Ingredients

/-! **The seed clauses are proved.** The four pieces of `SeedEnvelopePart` are proved:
- the sampled bound (`seedSampledPart`);
- the envelope input (`seedEnvInputPart`);
- the ledger (`seedLedgerPart`);
- the Schur bound (`seedSchurPart`).

So `SeedEnvelopePart` holds, and with the other five parts, `SeedClausesStatement` holds.

Special cases: those of the parts. -/

@[expose] public noncomputable section

namespace AVRegularity.EntryTerminal.Ingredients

open AVRegularity.EntryTerminal.Route

/-- **The seed clauses.** -/
theorem seedClauses : SeedClausesStatement :=
  seedClauses_of_ledger_schur seedLedgerPart seedSchurPart

end AVRegularity.EntryTerminal.Ingredients
