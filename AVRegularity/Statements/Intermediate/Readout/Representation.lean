-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import Homogenization.Ambient.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The data of a representation `U = F + ∑_l G_l` with recorded labels `λ_l`. -/

@[expose] public section

open Homogenization

namespace AVRegularity

/-- A specified representation (no infimum is taken): a base field `F`, and a finite ordered
list of profiles `G_l`, each recorded with its label `λ_l`. This is data only; regularity and the
label constraints are `IsRepresentationAt`. -/
structure Representation (H : Type*) where
  /-- The base field `F`. -/
  base : Vec 2 → H
  /-- The profiles `G_l` with their labels `λ_l`. -/
  profiles : List ((Vec 2 → H) × ℝ)

end AVRegularity
