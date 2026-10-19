-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.FamilyAtlas
public import AVRegularity.Statements.Intermediate.Families.IsQuietTransition
public import AVRegularity.Statements.Intermediate.Families.FamilyDomain
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsQuietOverlap

/-! The exact quiet transition on every adjacent pair. -/

@[expose] public noncomputable section

open Homogenization

namespace AVRegularity

namespace ChartedFamily

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

namespace Atlas

variable {F : ChartedFamily ι h D P Ctx}

/-- The exact quiet transition on every adjacent pair. -/
def IsQuiet (T : F.Atlas) (ν e E : ℝ) : Prop :=
  ∀ p q (hpq : T.adjacent p q), F.IsQuietOverlap ν e E (T.tr p q hpq) (T.sameCtx p q hpq)

end Atlas

end ChartedFamily

end AVRegularity
