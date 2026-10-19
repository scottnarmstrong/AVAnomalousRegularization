-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.EntryTerminal.Ingredients.ErrorEnergy.ResidualFromNative
public import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.Flux
public import AVRegularity.EntryTerminal.Assembly.Route.EntryTerminalOfWeak
import AVRegularity.EntryTerminal.Assembly.Prep.Closed
import AVRegularity.EntryTerminal.Ingredients.Successor.Successor
import AVRegularity.EntryTerminal.Ingredients.SeedEncoding.SeedEncoding
import AVRegularity.EntryTerminal.Ingredients.SeedEnvelope.Closed
import AVRegularity.EntryTerminal.Ingredients.CoarseFamily.CoarseFamily
import AVRegularity.EntryTerminal.Ingredients.LiftField.LiftSeq
import AVRegularity.EntryTerminal.Ingredients.Readout.EnergyReadout
import AVRegularity.EntryTerminal.Ingredients.Truncation.Truncation
import AVRegularity.EntryTerminal.Ingredients.TruncationParts.TruncationParts
import AVRegularity.EntryTerminal.Ingredients.Plan.Plan
import AVRegularity.EntryTerminal.Ingredients.ReadoutScale.ReadoutScale
import AVRegularity.EntryTerminal.Ingredients.ScaleFacts.ScaleFacts
import AVRegularity.Proofs.Results.EntryWeak.WeakPassageComparison
import AVRegularity.EntryTerminal.Ingredients.Deadline.Deadline

section
@[expose] public noncomputable section
namespace AVRegularity.EntryTerminal.Route

/-! # The error-energy statement from the native temporal representatives

`errorEnergyStatement_of_native`: `ErrorEnergyStatement` (the text of
`entry_terminal_error_energy`) from `NativeTemporalRepresentativesStatement` alone, by
`errorEnergyBundled_of_native` and the unbundling `errorEnergyStatement_of_bundled`. Once
`NativeTemporalRepresentativesStatement` is proved, this theorem proves the error-energy statement. -/

open AVRegularity.Construction.Preservation.Residual.CovarianceTransport

/-- **The error-energy statement from the native temporal representatives.** -/
theorem errorEnergyStatement_of_native (hN : NativeTemporalRepresentativesStatement) :
    ErrorEnergyStatement :=
  errorEnergyStatement_of_bundled (errorEnergyBundled_of_native hN)

end AVRegularity.EntryTerminal.Route
end
end

section
@[expose] public noncomputable section
section
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.EntryTerminal.Route

/-! **The terminal entry from the native temporal representatives.** Every ingredient
of the terminal route is proved except the error energy, which depends only on
`NativeTemporalRepresentativesStatement` (`errorEnergyBundled_of_native`):
- `terminalPreparation`, `terminalSuccessor`, `seedEncoding`, `seedClauses`,
  `coarseFamily`, `liftField`, `readoutGlue`, `truncation`, `truncationParts`;
- the plan, the deadline, the readout scale, the scale facts and the monotonicity of the
  preparation.

So `entry_terminal_of_weak` (its text copy) depends only on
`NativeTemporalRepresentativesStatement`; the full entry is in `EntryTerminalOfNative.lean`. -/

/-- **`entry_terminal_of_weak` from the error energy over the bundled data**, with every other ingredient of the
route proved. -/
theorem entryTerminalOfWeak_of_errorEnergy (h9 : ErrorEnergyBundled) :
    Assembly.EntryTerminalOfWeakStatement := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λ₀, h128, h⟩ := route_tail_of_bundled terminalPreparation
    Ingredients.terminalSuccessor seedEncoding Ingredients.seedClauses Ingredients.coarseFamily
    Ingredients.liftField h9 readoutGlue truncation Ingredients.truncationParts plan deadline
    readoutScale scaleFacts prepMonotone ⟨α, s, q, ζ, hα₀, hα₁, hs₀, hs₁, hq, hζ⟩
  refine ⟨Λ₀, h128, ?_⟩
  intro Λ hΛ c₀max hc0 φ₀ hφ₀ hφs hφn hφm hφsupp bw hbw0 hbw1 Jw Lw dW DW L0w τ T₀ Pw σw χw η₀
    hJw hDW hτ hτT hPw hσw0 hσw1 hχw hη0 hη1 PT hPT NT pT RT AT k₀ LcT LoT LfT LpT tT QT hsched τe lamE
    hexp σ₀ H J N p Kres Lpr Lc Lf nT hfresh Kout
  exact h ⟨Λ, c₀max, φ₀, hφ₀, bw, Jw, Lw, dW, DW, L0w, τ, T₀, Pw, σw, χw, η₀, PT, NT, pT, RT, AT,
      k₀, LcT, LoT, LfT, LpT, tT, QT, τe, lamE, σ₀, H, J, N, p, Kres, Lpr, Lc, Lf, nT⟩ hΛ
    ⟨hc0, ⟨hφs, hφn, hφm, hφsupp⟩, ⟨hbw0, hbw1⟩, ⟨hJw, hτ, hτT, hPw, hσw0, hσw1, hχw, hη0, hη1⟩,
      hPT, hsched, hexp, hfresh, hDW⟩ Kout

/-- **`entry_terminal_of_weak` from the native temporal representatives.** -/
theorem entryTerminalOfWeak_of_native (hN : NativeTemporalRepresentativesStatement) :
    Assembly.EntryTerminalOfWeakStatement :=
  entryTerminalOfWeak_of_errorEnergy (errorEnergyBundled_of_native hN)

/-! **The full terminal entry from the native temporal representatives.** With
`entry_weak` (proved) and `entry_terminal_of_ingredients`,
`entry_terminal` (its text copy) depends only on `NativeTemporalRepresentativesStatement`
(`entryTerminalOfWeak_of_native`). -/

/-- The text copy of `entry_weak` holds (`entry_weak`). -/
theorem entryWeak_copy : Assembly.EntryWeakStatement :=
  Providers.entry_weak

/-- **The full terminal entry from the native temporal representatives.** -/
theorem entryTerminal_of_native (hN : NativeTemporalRepresentativesStatement) :
    Assembly.EntryTerminalStatement :=
  Assembly.entry_terminal_of_ingredients entryWeak_copy (entryTerminalOfWeak_of_native hN)

end AVRegularity.EntryTerminal.Route
end
end
end
