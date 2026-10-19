-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.IsQuietTransition
public import AVRegularity.Statements.Intermediate.Families.FamilyDomain

/-! The chart transitions of a charted family. An atlas stores the valid overlaps and the
identification of the two descriptions of the same context; chart identities, inverses and
cocycles follow from the supplied flow charts, and arbitrary unrelated representatives are not
admissible. An atlas selects the adjacent pairs of pieces, the transition `Υ` and overlap of
each, and which contexts of the two pieces are the same retained history. The cycle statements
require the exact quiet transition (`IsQuietOverlap`) on every adjacent pair, an atlas containing
the transitions between the consecutive or equal renewal labels that meet the window
(`IsConsecutiveClosed`), and overlaps containing every quiet time of the window at which both
pieces are output (`CoversQuiet`): the trimmed quiet overlap. -/

@[expose] public noncomputable section

open Homogenization

namespace AVRegularity

namespace ChartedFamily

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- The transitions between pieces: adjacency, the transition map and overlap, and the
identification of contexts. -/
structure Atlas (F : ChartedFamily ι h D P Ctx) where
  /-- The pairs of pieces with a stored transition. -/
  adjacent : P → P → Prop
  /-- The transition `y = Υ(y')` from the chart of `p` to the chart of `q`. -/
  tr : ∀ p q, adjacent p q → ChartTransition (F.piece p) (F.piece q)
  /-- The contexts of `p` and `q` that are two descriptions of the same retained history. -/
  sameCtx : ∀ p q, adjacent p q → Ctx p → Ctx q → Prop

end ChartedFamily

end AVRegularity
