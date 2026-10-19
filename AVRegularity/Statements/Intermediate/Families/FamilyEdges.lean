-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.ChartedFamily

/-! Graph-level predicates of a charted family, on identities.
An edge `u → v` exists exactly when `Γ v u` is nonempty.
Descending slots are required at the maximal current order `D_γ ≤ d^birth_γ` of each identity:
lower orders then satisfy them a fortiori. -/

@[expose] public section

namespace AVRegularity

namespace ChartedFamily

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- `K v + D_γ ≤ K u + 2` for every identity `γ` of every edge `u → v`. -/
def IsDescending (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ) : Prop :=
  ∀ v u (γ : F.Γ v u), K v + (F.identity v u γ).maxOrder ≤ K u + 2

end ChartedFamily

end AVRegularity
