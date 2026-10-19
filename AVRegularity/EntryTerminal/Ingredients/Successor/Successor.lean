-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Assembly.Route.Ingredients
import AVRegularity.Construction.StageSuccessor.RealizedFields
import AVRegularity.EntryTerminal.Ingredients.SeedQuiet.Proof
import AVRegularity.EntryTerminal.Ingredients.SeedStruct.SeedStruct
import AVRegularity.CycleReference.FluxFastDiscrepancy

/-! **The terminal successor**, from the stage-generic producer
`stage_successor_exists` (`Construction/StageSuccessor/RealizedFields.lean`).

For the weak stage `Gw` at level `M ≥ j₀ + 2`, the input of the producer at the terminal
provenance parameters `A.Pt D Cw cr M`, the terminal menu `A.Mt M sXT sZT tp cr` and `Gw` is
supplied field by field: the data (`IsTermData`, `A.Valid`), the projections of `IsWeakStage`
(level, depth, natural pieces, tags, context certificate, no old births), the positivity of the
terminal scales, and `terminal_source_orders_and_paths`. The carrier pair is `(1, 1)`, the lift
floors are `0`.

Special cases:
- An empty weak family: only natural renewal charts are needed.
- `c_r = 1`: allowed.
- `C_w = 0`: `witness_constant` holds with equality. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev

namespace AVRegularity.EntryTerminal.Ingredients

open AVRegularity.EntryTerminal.Route

/-- **The terminal successor exists.** -/
theorem terminalSuccessor : SuccessorStatement := by
  intro X
  refine ⟨128, le_rfl, fun A hΛ hA => ⟨0, 0, fun sXT sZT _ _ Lt nW cr kS hcr _ cK CL Cχ kW
    _ _ _ => ⟨1, 1, le_rfl, one_pos, fun j₀ _ => ⟨j₀ + 2, fun M hM => ?_⟩⟩⟩⟩
  intro D hD a lawW PW Gw aM hweak tp Cw hCw
  obtain ⟨hDα, hDq, hDΛ, hDζ, -, hband, hterm⟩ := hD
  have hΛD : 128 ≤ D.Λ := by rw [hDΛ]; exact hΛ
  have hq1 : 1 < D.q := hDq ▸ X.hq.1
  have hζ : IsFastProfile D.ζ := by rw [hDζ]; exact X.hζ
  have hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    rw [hDα, hDq, hDΛ, hDζ, hterm]; exact hband
  have hlev : Gw.level = M := hweak.2.2.1
  have hinv := hweak.2.2.2.2.2.2.2.2.2
  have hεpos : ∀ i, 0 < D.eps i := fun i => (Scales.epsilon_basic hq1 hΛD).1
  have hν : 0 < D.κ (M - 1) :=
    CycleReference.bandChain_pos (by omega : 1 ≤ A.Λ) X.hζ hband (Nat.sub_le M 1)
  have hh : 0 < D.termH M := Construction.Stream.ocTauPP_pos (by omega)
  have hρ : 0 < D.termRho cr M := mul_pos hcr (Real.sqrt_pos.2 (mul_pos hν hh))
  have hNT := one_le_NT_of_valid A hA
  have hsrc := Construction.StageSuccessor.terminal_source_orders_and_paths Gw A.NT A.pT A.DW
    A.dW hNT hweak.2.2.2.1
  exact Construction.StageSuccessor.stage_successor_exists (A.Pt D Cw cr M)
    (A.Mt M sXT sZT tp cr) Gw
    { base := by omega
      profile := hζ
      band := hκ
      bandwidth := hA.2.2.1.1
      level := by omega
      top := by omega
      order := le_trans (by norm_num) (le_max_left _ _)
      cutoff := hNT
      length_factor := hcr
      natural := hinv.1
      tags := hasTags_of_seed hinv.2.1 hweak.2.2.2.2.2.1.1
      context := ⟨kW, hinv.2.2.2.2.2.1⟩
      old_births := fun v hv e he => by
        rw [show v.births = [] from hweak.2.2.2.2.1 ⟨v, hv⟩] at he
        exact absurd he (List.not_mem_nil)
      finite_paths := ⟨A.dW, hsrc.2⟩
      witness_constant := hCw
      birth_weights := fun _ => zero_le_one
      birth_scales := hεpos
      birth_length := hρ
      birth_width := mul_pos hρ (Real.rpow_pos_of_pos (hεpos _) _)
      cutoff_eq := rfl
      covariance_eq := rfl
      letter_orders := hsrc.1 }

end AVRegularity.EntryTerminal.Ingredients
