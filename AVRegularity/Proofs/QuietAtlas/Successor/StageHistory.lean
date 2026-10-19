-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Proofs.QuietAtlas.Successor.QuietMatching
import AVRegularity.Proofs.QuietAtlas.FirstSourceHistory
public import AVRegularity.Definitions.Construction.Preparation
public import AVRegularity.Statements.Construction.IsFastProfile

/-! **The carried history invariant of an actual successor, from its parent** (the
stage invariant carries `StageHistoryInvariant G M`, so every producer of a successor's invariant
must supply it). The successor is presented by its own witness (`successorQuietPresentation`); its
finer operators read only the history (`successorFinerHistory_of_covariant`: the parent's
invariant and covariance, and the diagonal lifts through `diagLabelHistoryInvariant_of_diagLifts`);
one-passage preservation for presentations with transfers and first sources
(`quietHistoryPreservation_of_firstSourceHistory` with `firstSourceHistory`) gives the
successor's invariant. Restriction to the retained family, and the encodings, are
`stageHistoryInvariant_retained`, `stageHistoryInvariant_encoded`, `stageHistoryInvariant_seed`
(`EntryTerminal/Ingredients/SeedQuiet/History.lean`).

Special cases:
- A successor without identities: vacuous.
- A successor of transfers only: the first-source statement is not used.
- The parent's invariant at the same `Mtop`: the successor's level is below it. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity.Providers.QuietAtlas

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **The history invariant of an actual successor of a generated parent.** -/
theorem successor_stageHistoryInvariant {P : ProvParams} {Mn : SuccMenu}
    {G G' : GenStage D hr Dm b j₀} (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hb : 0 < b)
    (hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
      2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ b / (64 * (8 * Real.pi ^ 2)))
    (hc2 : 0 < D.cellScaleSq G.level) (hSucc : IsActualSuccessor D P Mn G G')
    (hgen : G.IsGenerated) {Mtop : ℕ} (hlt : G'.level < Mtop)
    (hinv : StageHistoryInvariant G Mtop) : StageHistoryInvariant G' Mtop := by
  obtain ⟨hG, hG', -, -, -, -, ⟨w⟩⟩ := (isActualSuccessor_iff_nonempty_witness P Mn G G').mp hSucc
  obtain ⟨P', hP'⟩ := successorQuietPresentation P Mn G G' hG hG' w
  exact quietHistoryPreservation_of_firstSourceHistory firstSourceHistory hΛ hζ hb hstart G' P'
    Mtop hlt (successorFinerHistory_of_covariant hG hG' hζ hΛ hc2 w P' hP'
      (fluxRecenterCovariantOnPulses_of_generated hζ hgen) hinv
      (diagLabelHistoryInvariant_of_diagLifts hζ hc2 w.diag Mtop))

/-- The same, from a carrier start with `1 ≤ CH`, `1 ≤ Υ` (the start bound of the appended
children, `startBound_of_carrierStart`). -/
theorem successor_stageHistoryInvariant_of_carrier {P : ProvParams} {Mn : SuccMenu}
    {G G' : GenStage D hr Dm b j₀} (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hb : 0 < b)
    {CH Υ : ℝ} (hCH : 1 ≤ CH) (hΥ : 1 ≤ Υ) (hcar : IsCarrierStart D.α D.q D.Λ b CH Υ j₀)
    (hc2 : 0 < D.cellScaleSq G.level) (hSucc : IsActualSuccessor D P Mn G G')
    (hgen : G.IsGenerated) {Mtop : ℕ} (hlt : G'.level < Mtop)
    (hinv : StageHistoryInvariant G Mtop) : StageHistoryInvariant G' Mtop :=
  successor_stageHistoryInvariant hΛ hζ hb (GenSem.startBound_of_carrierStart hΛ hCH hΥ hcar)
    hc2 hSucc hgen hlt hinv

end AVRegularity.Providers.QuietAtlas
