-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.ChartedFamily
public import AVRegularity.Sobolev.Basic

/-! The flux in the dimensional slow label. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

namespace ChartedFamily

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- The flux field in the dimensional slow label `Y = E X`: `(t, Y, z) ↦ a♭(t, Y/E, z)`. -/
def slowFlux (F : ChartedFamily ι h D P Ctx) (E : ℝ) (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u)
    (d : ℕ) (I : DerivativeWord2 (d - 1)) : ℝ → Vec 2 → Vec 2 → Vec 2 :=
  fun t Y z => F.flux p c v u γ d I t (E⁻¹ • Y) z

end ChartedFamily

end AVRegularity
