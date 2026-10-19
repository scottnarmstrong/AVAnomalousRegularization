-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.FamilyAtlas
public import AVRegularity.Statements.Intermediate.Families.IsQuietTransition
public import AVRegularity.Statements.Intermediate.Families.FamilyDomain

/-! Overlaps cover the quiet times of the window. -/

@[expose] public noncomputable section

open Homogenization

namespace AVRegularity

namespace ChartedFamily

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

namespace Atlas

variable {F : ChartedFamily ι h D P Ctx}

/-- Every quiet time of the window at which both pieces are output lies in the overlap, for every
slow label. -/
def CoversQuiet (T : F.Atlas) (quiet W : Set ℝ) : Prop :=
  ∀ p q (hpq : T.adjacent p q), ∀ t ∈ quiet ∩ W ∩ (F.piece p).output ∩ (F.piece q).output,
    ∀ Y : Vec 2, (t, Y) ∈ (T.tr p q hpq).overlap

end Atlas

end ChartedFamily

end AVRegularity
