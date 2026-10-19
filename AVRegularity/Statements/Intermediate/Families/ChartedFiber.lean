-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.Families.ChartedFamily
public import AVRegularity.Statements.Intermediate.Families.ConstituentEdges

/-! The one-chart view of a charted family and its converse (the single-chart definitions are
the one-piece specialization of charted families). `ChartedFamily.fiber F p c` is the
chart-frame edge family of the piece `p` in the context `c`: for each order `d` the list of the
order-`d` constituents of the identities with `d ≤ D_γ`, each with the (shared) record of its
identity. Cell-level statements (lifts, words,
cell problems) are about one fixed frame and use this view; the record-level quantities of the
family (sizes, ledgers) are computed on identities, never on fibers, since a fiber repeats an
identity once per current order. `ChartedFamily.ofFiber` embeds a one-chart edge family as a
family with the single trivial piece and context. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity

namespace ChartedFamily

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- The chart-frame edge family of the piece `p` in the context `c`. -/
def fiber (F : ChartedFamily ι h D P Ctx) (p : P) (c : Ctx p) : ConstituentEdges D h :=
  fun v u d => (Finset.univ.toList : List (F.Γ v u)).filterMap fun γ =>
    if hd : d.1 ≤ (F.identity v u γ).maxOrder then
      some
        { map := (F.identity v u γ).map
          coeff := F.flux p c v u γ d.1
          periodic := F.flux_periodic p c v u γ d.1
          record := (F.identity v u γ).record
          birthExcess_ge := le_trans hd (F.identity v u γ).le_birth }
    else none

end ChartedFamily

end AVRegularity
