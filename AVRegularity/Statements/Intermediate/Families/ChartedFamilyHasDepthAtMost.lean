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

/-- There is no directed path of `H + 1` edges. -/
def HasDepthAtMost (F : ChartedFamily ι h D P Ctx) (H : ℕ) : Prop :=
  ∀ p : Fin (H + 2) → ι, ∃ k : Fin (H + 1), IsEmpty (F.Γ (p k.succ) (p k.castSucc))

end ChartedFamily

end AVRegularity
