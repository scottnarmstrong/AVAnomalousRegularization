-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.FamilyAtlas
public import AVRegularity.Statements.Intermediate.Families.IsQuietTransition
public import AVRegularity.Statements.Intermediate.Families.FamilyDomain

/-! Consecutive-label closure of an atlas. -/

@[expose] public noncomputable section

open Homogenization

namespace AVRegularity

namespace ChartedFamily

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

namespace Atlas

variable {F : ChartedFamily ι h D P Ctx}

/-- Distinct pieces with consecutive or equal renewal labels whose outputs meet the window are
adjacent (pulse pieces of one chart block share a label and overlap in the quiet gaps). -/
def IsConsecutiveClosed (T : F.Atlas) (W : Set ℝ) : Prop :=
  ∀ p q, p ≠ q →
    ((F.piece q).label = (F.piece p).label + 1 ∨ (F.piece q).label = (F.piece p).label) →
    ((F.piece p).output ∩ (F.piece q).output ∩ W).Nonempty → T.adjacent p q

end Atlas

end ChartedFamily

end AVRegularity
