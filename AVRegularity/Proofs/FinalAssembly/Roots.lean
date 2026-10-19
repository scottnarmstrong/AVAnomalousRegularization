-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.IterationPassage.Assembly.IterationCascadeAssemblyProbe
import AVRegularity.IterationPassage.Cascade.OfOpenLeaves
public import AVRegularity.Finite.Assembly.TerminalLiftProfileBoundsOfIngredients
public import AVRegularity.EntryTerminal.Assembly.EntryTerminalOfIngredients
import AVRegularity.EntryTerminal.Assembly.Prep.Closed
import AVRegularity.EntryTerminal.Ingredients.Successor.Successor
import AVRegularity.EntryTerminal.Ingredients.SeedEncoding.SeedEncoding
import AVRegularity.EntryTerminal.Ingredients.SeedEnvelope.Assembly
import AVRegularity.EntryTerminal.Assembly.Seed.OfParts
import AVRegularity.EntryTerminal.Assembly.Seed.SeedRepricing
import AVRegularity.EntryTerminal.Ingredients.CoarseFamily.CoarseFamily
import AVRegularity.EntryTerminal.Ingredients.LiftField.LiftSeq
import AVRegularity.EntryTerminal.Ingredients.Readout.EnergyReadout
import AVRegularity.EntryTerminal.Ingredients.Truncation.Truncation
import AVRegularity.EntryTerminal.Ingredients.TruncationParts.TruncationParts
import AVRegularity.EntryTerminal.Ingredients.Plan.Plan
import AVRegularity.EntryTerminal.Ingredients.Deadline.Deadline
import AVRegularity.EntryTerminal.Ingredients.ReadoutScale.ReadoutScale
import AVRegularity.EntryTerminal.Ingredients.ScaleFacts.ScaleFacts
import AVRegularity.CycleWords.Seam.S3CycleSeam
import AVRegularity.CycleWords.Seam.B1PlainStage
import AVRegularity.Proofs.Results.EntryWeak.WeakPassageComparison
import AVRegularity.Finite.TerminalLift.PositiveTransfer
import AVRegularity.Proofs.Results.Finite.TerminalLiftRep
public import AVRegularity.Assembly.TopWiring.Summary
import AVRegularity.EntryTerminal.Assembly.Route.EntryTerminalOfNative
import AVRegularity.Proofs.Results.Construction.PreservationSuccessor
import AVRegularity.Proofs.Results.Entry.EntryTerminal
public import AVRegularity.Construction.Preservation.Assembly.PreparationJointInputs
public import AVRegularity.EntryTerminal.Assembly.Route.Ingredients
import AVRegularity.Construction.Preservation.Residual.CovarianceTransport.GluedClosed

section
section
/-! # Endgame: the iteration statements from `preservation_successor` and `successor_bill`

Conditional assemblies:
* `iterationCascade_of_schedule`: `iteration_cascade` (text copy
  `Finite.Assembly.IterationCascadeStatement`) from `iteration_cascade_of_schedule` (text copy
  `IterationCascadeOfScheduleStatement`), through `iteration_cascade_of_ingredients`.
* `iterationCascadeOfSchedule_of_targets`, `iterationCascade_of_targets`: from the two
  statements of the preservation argument, `preservation_successor` and `successor_bill`, in the form
  `∀ α s …, PreservationSuccessorStatement α s q ζ` (definitionally the statements), through
  `iteration_cascade_of_schedule_of_open_leaves`. -/

@[expose] public section

open AVRegularity.Construction.Preservation.Assembly

namespace AVRegularity.Providers.Endgame

/-- **`iteration_cascade` from `iteration_cascade_of_schedule`.** -/
theorem iterationCascade_of_schedule
    (h : IterationPassage.Assembly.IterationCascadeOfScheduleStatement) :
    Finite.Assembly.IterationCascadeStatement := fun α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ =>
  IterationPassage.Assembly.iteration_cascade_of_ingredients h α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

/-- **`iteration_cascade_of_schedule` from `preservation_successor` and `successor_bill`.** -/
theorem iterationCascadeOfSchedule_of_targets
    (hps : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PreservationSuccessorStatement α s q ζ)
    (hbill : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ → SuccessorBillStatement α s q ζ) :
    IterationPassage.Assembly.IterationCascadeOfScheduleStatement :=
  IterationPassage.Cascade.iteration_cascade_of_schedule_of_open_leaves hps hbill

/-- **`iteration_cascade` from `preservation_successor` and `successor_bill`.** -/
theorem iterationCascade_of_targets
    (hps : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PreservationSuccessorStatement α s q ζ)
    (hbill : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ → SuccessorBillStatement α s q ζ) :
    Finite.Assembly.IterationCascadeStatement :=
  iterationCascade_of_schedule (iterationCascadeOfSchedule_of_targets hps hbill)

end AVRegularity.Providers.Endgame
end
end

section
/-! # Endgame: the entry-terminal statements from the error energy bound

Conditional assemblies:
* `entryTerminalPreparation`: `entry_terminal_preparation` (the text copy
  `EntryTerminal.Route.PreparationStatement`), proved: `preparation_of_seam` at
  `cycleSeamStatement_of_quietMarginDatum quietMarginDatum`.
* `entryWeak`: `entry_weak` in the text copy
  `EntryTerminal.Assembly.EntryWeakStatement`.
* `entryTerminalOfWeak_of_errorEnergy'`: `entry_terminal_of_weak` from the error energy bound
  (`entry_terminal_error_energy`, text copy `EntryTerminal.Route.ErrorEnergyStatement`) alone:
  `entry_terminal_of_weak_of_route` with the preparation above and the thirteen proved route ingredients.
* `entryTerminal_of_ofWeak`, `entryTerminal_of_errorEnergy`: `entry_terminal` from
  `entry_terminal_of_weak`, resp. from the error energy bound alone (`entry_terminal_of_ingredients` with `entry_weak`).
The text copies are definitionally the statements. -/

@[expose] public section

namespace AVRegularity.Providers.Endgame

/-- **The preparation, proved** (from `cycle_seam`). -/
theorem entryTerminalPreparation : EntryTerminal.Route.PreparationStatement :=
  EntryTerminal.Route.preparation_of_seam
    (CycleWords.Seam.cycleSeamStatement_of_quietMarginDatum CycleWords.Seam.quietMarginDatum)

/-- `entry_weak` in the text copy of the entry-terminal assembly. -/
theorem entryWeak : EntryTerminal.Assembly.EntryWeakStatement :=
  fun α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ => Providers.entry_weak α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

/-- **`entry_terminal_of_weak` from the error energy bound alone.** -/
theorem entryTerminalOfWeak_of_errorEnergy' (h9 : EntryTerminal.Route.ErrorEnergyStatement) :
    EntryTerminal.Assembly.EntryTerminalOfWeakStatement :=
  EntryTerminal.Route.entry_terminal_of_weak_of_route entryTerminalPreparation
    EntryTerminal.Ingredients.terminalSuccessor EntryTerminal.Route.seedEncoding
    (EntryTerminal.Ingredients.seedClauses_of_ledger_schur EntryTerminal.Route.seedLedgerPart
      EntryTerminal.Route.seedSchurPart)
    EntryTerminal.Ingredients.coarseFamily EntryTerminal.Ingredients.liftField h9
    EntryTerminal.Route.readoutGlue EntryTerminal.Route.truncation
    EntryTerminal.Ingredients.truncationParts EntryTerminal.Route.plan EntryTerminal.Route.deadline
    EntryTerminal.Route.readoutScale EntryTerminal.Route.scaleFacts EntryTerminal.Route.prepMonotone

/-- **`entry_terminal` from `entry_terminal_of_weak`.** -/
theorem entryTerminal_of_ofWeak (h : EntryTerminal.Assembly.EntryTerminalOfWeakStatement) :
    EntryTerminal.Assembly.EntryTerminalStatement :=
  EntryTerminal.Assembly.entry_terminal_of_ingredients entryWeak h

/-- **`entry_terminal` from the error energy bound alone.** -/
theorem entryTerminal_of_errorEnergy (h9 : EntryTerminal.Route.ErrorEnergyStatement) :
    EntryTerminal.Assembly.EntryTerminalStatement :=
  entryTerminal_of_ofWeak (entryTerminalOfWeak_of_errorEnergy' h9)

/-- The finite assembly's text copy of `entry_terminal` (which does not record the reserve-plan
values `m_env = 0`, `K_an = L_an = J_m = K_s` of the seed constants, the weak reserve floor
`L_t + (1 + J_wN_w) + max{L_w + 5, k₀} ≤ K_w`, the value `c_r = 1` and the weak orders of the menu,
and has `L_w ≤ J_wN_w` for `L_w = J_wN_w`) from `entry_terminal`. -/
theorem finiteEntryTerminal_of_assembly (h : EntryTerminal.Assembly.EntryTerminalStatement) :
    Finite.Assembly.EntryTerminalStatement := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  obtain ⟨Λ₀, hΛ₀, h⟩ := h α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, fun Λ hΛ c₀max hc₀ φ₀ hφ₀ hφs hφn hφm hφsupp bw hbw hbw1 Jw τ T₀ Pw η₀ hJw hτ
    hτT hPw hη hηδ => ?_⟩
  obtain ⟨Nw, Rw, Lw, hNw, hLw, -, -, h⟩ := h Λ hΛ c₀max hc₀ φ₀ hφ₀ hφs hφn hφm hφsupp bw hbw hbw1 Jw τ T₀
    Pw η₀ hJw hτ hτT hPw hη hηδ
  refine ⟨Nw, Rw, Lw, hNw, hLw.le, fun σw hσw hσw1 PT hPT NT pT RT AT k₀ LcT LoT LfT LpT tT QT hsched
    τe lamE hexp σ₀ H J N p Kres Lpr Lc Lf nT hnT Kout => ?_⟩
  obtain ⟨SX, SZ, h⟩ := h σw hσw hσw1 PT hPT NT pT RT AT k₀ LcT LoT LfT LpT tT QT hsched τe lamE hexp
    σ₀ H J N p Kres Lpr Lc Lf nT hnT Kout
  refine ⟨SX, SZ, fun sXT sZT hX hZ => ?_⟩
  exact (h sXT sZT hX hZ).elim fun Kw h => h.elim fun Lt h => h.elim fun nW h =>
    h.elim fun hk₀w h => h.elim fun hLw' h => h.elim fun cr h => h.elim fun kS h =>
      ⟨Kw, Lt, nW, hk₀w, hLw', cr, kS, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
        h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1,
        h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

end AVRegularity.Providers.Endgame
end
end
end

section
section
/-! # Endgame: `oc_finite`, `oc_global` and the five roots from the remaining statements

Conditional assemblies:
* `ocFiniteTarget_of_targets`: `oc_finite` (text copy `OcFiniteTargetStatement`, TopWiring) from
  `entry_terminal` and `iteration_cascade` (text copies `Finite.Assembly.EntryTerminalStatement`,
  `Finite.Assembly.IterationCascadeStatement`), through `oc_finite_of_ingredients` with the proved
  `terminal_lift_rep` (`terminal_lift_rep_proved`) and the `weak_lift_rep` proof.
* `ocFiniteTarget_of_leaves`: `oc_finite` from the three statements at the bottom of the two
  chains: `entry_terminal_error_energy`, `preservation_successor`, `successor_bill`.
* `ocGlobalTarget_of_leaves`, `roots_of_leaves`: `oc_global` and the five roots
  (`ocGlobalTarget_of_finiteTarget`, `roots_of_finiteTarget` of TopWiring) from the same three. -/

@[expose] public section

open AVRegularity.Construction.Preservation.Assembly AVRegularity.Assembly.TopWiring

namespace AVRegularity.Providers.Endgame

/-- **`oc_finite` from `entry_terminal` and `iteration_cascade`.** -/
theorem ocFiniteTarget_of_targets (hE : Finite.Assembly.EntryTerminalStatement)
    (hI : Finite.Assembly.IterationCascadeStatement) : OcFiniteTargetStatement :=
  fun α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ =>
    Finite.Assembly.oc_finite_of_ingredients hE hI Finite.TerminalLift.terminal_lift_rep_proved
      (fun α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ => Providers.weak_lift_rep α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)
      α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

/-- **`oc_finite` from the error energy bound, `preservation_successor` and `successor_bill`.** -/
theorem ocFiniteTarget_of_leaves (h9 : EntryTerminal.Route.ErrorEnergyStatement)
    (hps : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PreservationSuccessorStatement α s q ζ)
    (hbill : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ → SuccessorBillStatement α s q ζ) :
    OcFiniteTargetStatement :=
  ocFiniteTarget_of_targets (finiteEntryTerminal_of_assembly (entryTerminal_of_errorEnergy h9))
    (iterationCascade_of_targets hps hbill)

/-- **`oc_global` from the error energy bound, `preservation_successor` and `successor_bill`.** -/
theorem ocGlobalTarget_of_leaves (h9 : EntryTerminal.Route.ErrorEnergyStatement)
    (hps : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PreservationSuccessorStatement α s q ζ)
    (hbill : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ → SuccessorBillStatement α s q ζ) :
    OcGlobalTargetStatement :=
  ocGlobalTarget_of_finiteTarget (ocFiniteTarget_of_leaves h9 hps hbill)

/-- **The five root statements from the error energy bound, `preservation_successor` and
`successor_bill`.** -/
theorem roots_of_leaves (h9 : EntryTerminal.Route.ErrorEnergyStatement)
    (hps : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PreservationSuccessorStatement α s q ζ)
    (hbill : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ → SuccessorBillStatement α s q ζ) :
    InteriorRegularityRootStatement ∧ InteriorRegularityConstructionRootStatement ∧
      LocalInteriorRegularityRootStatement ∧ VanishingDiffusivityLimitsRootStatement ∧
      VanishingDiffusivityLimitsLocalRootStatement :=
  roots_of_finiteTarget (ocFiniteTarget_of_leaves h9 hps hbill)

end AVRegularity.Providers.Endgame
end
end

section
/-! # Endgame: `oc_finite` and `oc_global` conditional on `preservation_successor` alone

* `errorEnergy'`: the error energy bound (`entry_terminal_error_energy`, text copy
  `EntryTerminal.Route.ErrorEnergyStatement`), proved: `errorEnergyStatement_of_native` at
  `nativeTemporalRepresentatives`.
* `successorBill_all`: the proof `Providers.successor_bill` in the form
  `∀ α s …, SuccessorBillStatement α s q ζ`.
* `ocFinite_of_preservation`, `ocGlobal_of_preservation`: the conclusions of
  `oc_finite` and `oc_global` (texts verbatim) from `preservation_successor` alone, through
  `ocFiniteTarget_of_leaves` and `ocGlobalTarget_of_leaves`.

Conditional assemblies with distinct names. -/

@[expose] public section

open MeasureTheory Filter Topology Homogenization AVenhance
open AVRegularity.Construction.Preservation.Assembly

namespace AVRegularity.Providers.Endgame

/-- **The error energy bound, closed**: `entry_terminal_error_energy` (text copy) from the native temporal
representatives. -/
theorem errorEnergy' : EntryTerminal.Route.ErrorEnergyStatement :=
  EntryTerminal.Route.errorEnergyStatement_of_native
    Construction.Preservation.Residual.CovarianceTransport.nativeTemporalRepresentatives

/-- The `successor_bill` proof in the form of the assemblies. -/
theorem successorBill_all : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
    ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ → SuccessorBillStatement α s q ζ :=
  fun α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ => Providers.successor_bill α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

/-- **`oc_finite` from `preservation_successor` alone.** -/
theorem ocFinite_of_preservation
    (hps : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PreservationSuccessorStatement α s q ζ)
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
    ∀ J : ℕ, 1 ≤ J → ∀ t₀ T : ℝ, 0 < t₀ → t₀ < T →
    ∃ (Mstar : ℕ) (C : ℝ), ∀ M : ℕ, Mstar ≤ M →
    ∀ κ ∈ Set.Icc (ocEpsilon q Λ M ^ ((1 + α) - ocGamma α q) / 2)
        (2 * ocEpsilon q Λ M ^ ((1 + α) - ocGamma α q)),
    ∀ a : ℝ, ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
    ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn (streamVel (Φ (M + J))) κ a (a + T) f θ →
    ∀ t ∈ Set.Icc (a + t₀) (a + T), ∃ Θt : Vec 2 → ℝ,
      IsZ2Periodic Θt ∧ Θt =ᵐ[volume.restrict unitCube] θ t ∧
      CsNormLe s Θt (C * Real.sqrt (l2NormSq f)) :=
  ocFiniteTarget_of_leaves errorEnergy' hps successorBill_all
    α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

/-- **`oc_global` from `preservation_successor` alone.** -/
theorem ocGlobal_of_preservation
    (hps : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PreservationSuccessorStatement α s q ζ)
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
        ∀ b : ℝ → Vec 2 → Vec 2,
          (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) →
          ∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∃ C : ℝ,
            ∀ a : ℝ, ∀ κ ∈ ocBandSet α q Λ, ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
            ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a (a + T) f θ →
              ∃ Θ : ℝ → Vec 2 → ℝ,
                ContinuousOn (fun p : ℝ × Vec 2 => Θ p.1 p.2)
                  (Set.Icc (a + t₀) (a + T) ×ˢ Set.univ) ∧
                ∀ t ∈ Set.Icc (a + t₀) (a + T),
                  IsZ2Periodic (Θ t) ∧ Θ t =ᵐ[volume.restrict unitCube] θ t ∧
                  CsNormLe s (Θ t) (C * Real.sqrt (l2NormSq f)) :=
  ocGlobalTarget_of_leaves errorEnergy' hps successorBill_all
    α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

end AVRegularity.Providers.Endgame
end
end

section
/-! # Endgame: the five root statements from `preservation_successor` alone

`roots_of_preservation`: the five root statements (text copies `…RootStatement`, TopWiring)
from `preservation_successor` (in the form `∀ α s …, PreservationSuccessorStatement α s q ζ`)
alone: `roots_of_leaves` at the proofs
`Providers.entry_terminal_error_energy` and `Providers.successor_bill`.

`<root>_of_preservation`, one per root: the binders and statement,
verbatim, with `preservation_successor` as the one named hypothesis `hps`.
Conditional assemblies with distinct names. -/

@[expose] public section

open MeasureTheory Filter Topology Homogenization AVenhance
open AVRegularity.Construction.Preservation.Assembly AVRegularity.Assembly.TopWiring

namespace AVRegularity.Providers.Endgame

/-- **The five root statements from `preservation_successor` alone.** -/
theorem roots_of_preservation
    (hps : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PreservationSuccessorStatement α s q ζ) :
    InteriorRegularityRootStatement ∧ InteriorRegularityConstructionRootStatement ∧
      LocalInteriorRegularityRootStatement ∧ VanishingDiffusivityLimitsRootStatement ∧
      VanishingDiffusivityLimitsLocalRootStatement :=
  roots_of_leaves
    (fun α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ =>
      Providers.entry_terminal_error_energy α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)
    hps
    (fun α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ => Providers.successor_bill α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)

/-- **`interior_regularity` (statement verbatim) from
`preservation_successor` alone.** -/
theorem interior_regularity_of_preservation
    (hps : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PreservationSuccessorStatement α s q ζ)
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) :
    ∃ b : ℝ → Vec 2 → Vec 2, IsHolderDivFreeVelocity α b ∧
    ∃ κc : ℕ → ℝ, (∀ M, 0 < κc M) ∧ (∀ M, 4 * κc (M + 1) < κc M) ∧
    ∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∃ C : ℝ,
      ∀ a : ℝ, ∀ κ ∈ ⋃ M : ℕ, Set.Icc (κc M / 2) (2 * κc M),
      ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
        (∃ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a (a + T) f θ) ∧
        ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a (a + T) f θ →
          ∃ Θ : ℝ → Vec 2 → ℝ,
            ContinuousOn (fun p : ℝ × Vec 2 => Θ p.1 p.2)
              (Set.Icc (a + t₀) (a + T) ×ˢ Set.univ) ∧
            ∀ t ∈ Set.Icc (a + t₀) (a + T),
              IsZ2Periodic (Θ t) ∧ Θ t =ᵐ[volume.restrict unitCube] θ t ∧
              CsNormLe s (Θ t) (C * Real.sqrt (l2NormSq f)) :=
  (roots_of_preservation hps).1 α s hα₀ hα₁ hs₀ hs₁

/-- **`interior_regularity_construction` (statement verbatim) from
`preservation_successor` alone.** -/
theorem interior_regularity_construction_of_preservation
    (hps : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PreservationSuccessorStatement α s q ζ)
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      (∃ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ) ∧
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
        ∃ b : ℝ → Vec 2 → Vec 2,
          (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) ∧
          IsHolderDivFreeVelocity α b ∧
          ∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∃ C : ℝ,
            ∀ a : ℝ,
            ∀ κ ∈ ocBandSet α q Λ,
            ∀ f : Vec 2 → ℝ, MemL2On unitCube f →
              (∃ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a (a + T) f θ) ∧
              ∀ θ : ℝ → Vec 2 → ℝ, IsWeakSolutionOn b κ a (a + T) f θ →
                ∃ Θ : ℝ → Vec 2 → ℝ,
                  ContinuousOn (fun p : ℝ × Vec 2 => Θ p.1 p.2)
                    (Set.Icc (a + t₀) (a + T) ×ˢ Set.univ) ∧
                  ∀ t ∈ Set.Icc (a + t₀) (a + T),
                    IsZ2Periodic (Θ t) ∧ Θ t =ᵐ[volume.restrict unitCube] θ t ∧
                    CsNormLe s (Θ t) (C * Real.sqrt (l2NormSq f)) :=
  (roots_of_preservation hps).2.1 α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

/-- **`local_interior_regularity` (statement verbatim) from
`preservation_successor` alone.** -/
theorem local_interior_regularity_of_preservation
    (hps : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PreservationSuccessorStatement α s q ζ)
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
        ∃ b : ℝ → Vec 2 → Vec 2,
          (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) ∧
          ∀ cT CT : ℝ, 0 < cT → 0 < CT → ∃ C₁ : ℝ, 0 < C₁ ∧
            ∀ (n : ℕ) (T R ϱ ϑ : ℝ), 2 ≤ n → 0 < T → 0 < R → 0 < ϱ → ϱ < 1 / 8 →
              0 < ϑ → ϑ < 4 →
              cT * ocTauPP α q Λ (n - 1) ≤ T → T ≤ CT * ocTauPP α q Λ (n - 1) →
              8 * T * ocA α q Λ (n - 2) ≤ ocCStar →
              C₁ * max (ocEpsilon q Λ (n - 1) ^ α * T)
                  (Real.sqrt (sSup (ocBandSet α q Λ) * T)) ≤ R →
              R ≤ 1 / 8 →
              ∃ C : ℝ, ∀ t₁ : ℝ, ∀ X : ℝ → Vec 2 → ℝ → Vec 2,
                IsFlow (streamVel (Φ (n - 2))) X →
                ∀ κ ∈ ocBandSet α q Λ, ∀ θ : ℝ → Vec 2 → ℝ,
                  IsLocalEnergySolution b κ (fun t y => X t y t₁) t₁ T R θ →
                  ∃ Θ : ℝ → Vec 2 → ℝ, ∀ t ∈ Set.Icc (t₁ - ϑ * T) t₁,
                    ContinuousOn (Θ t) ((fun y => X t y t₁) '' euclidBall 0 (ϱ * R)) ∧
                    Tendsto (fun r => ∫ y in euclidBall 0 (ϱ * R),
                        (θ r (X r y t₁) - Θ t (X t y t₁)) ^ 2)
                      (𝓝[<] t ⊓ ae volume) (𝓝 0) ∧
                    ∀ x ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R),
                    ∀ y ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R),
                    ∀ z ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R), y ≠ z →
                      |Θ t x| + |Θ t y - Θ t z| / Real.sqrt (vecNormSq (y - z)) ^ s ≤
                        C * Real.sqrt ((volume (outerPipe (fun t y => X t y t₁) t₁ T R)).toReal⁻¹ *
                          ∫ p in outerPipe (fun t y => X t y t₁) t₁ T R, θ p.1 p.2 ^ 2) :=
  (roots_of_preservation hps).2.2.1 α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

/-- **`vanishing_diffusivity_limits` (statement verbatim) from
`preservation_successor` alone.** -/
theorem vanishing_diffusivity_limits_of_preservation
    (hps : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PreservationSuccessorStatement α s q ζ)
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
        ∃ b : ℝ → Vec 2 → Vec 2,
          (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) ∧
          ∃ Cthm : ℝ → ℝ → ℝ,
          ∀ (a F : ℝ) (κ : ℕ → ℝ) (f : ℕ → Vec 2 → ℝ) (θ : ℕ → ℝ → Vec 2 → ℝ),
            (∀ i, κ i ∈ ocBandSet α q Λ) → Tendsto κ atTop (𝓝 0) →
            (∀ i, MemL2On unitCube (f i) ∧ Real.sqrt (l2NormSq (f i)) ≤ F) →
            (∀ i, ∀ T : ℝ, 0 < T → IsWeakSolutionOn b (κ i) a (a + T) (f i) (θ i)) →
            ∃ (σ : ℕ → ℕ) (fstar : Vec 2 → ℝ) (Θ : ℕ → ℝ → Vec 2 → ℝ)
                (θstar : ℝ → Vec 2 → ℝ),
              StrictMono σ ∧ MemL2On unitCube fstar ∧
              (∀ g : Vec 2 → ℝ, MemL2On unitCube g →
                Tendsto (fun i => ∫ x in unitCube, f (σ i) x * g x) atTop
                  (𝓝 (∫ x in unitCube, fstar x * g x))) ∧
              (∀ i, ContinuousOn (fun p : ℝ × Vec 2 => Θ i p.1 p.2) (Set.Ioi a ×ˢ Set.univ) ∧
                ∀ t, a < t → IsZ2Periodic (Θ i t) ∧ Θ i t =ᵐ[volume.restrict unitCube] θ i t) ∧
              TendstoLocallyUniformlyOn (fun i (p : ℝ × Vec 2) => Θ (σ i) p.1 p.2)
                (fun p : ℝ × Vec 2 => θstar p.1 p.2) atTop (Set.Ioi a ×ˢ Set.univ) ∧
              (∀ φ : ℝ × Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
                tsupport φ ⊆ Set.Ioi a ×ˢ Set.univ →
                ∫ p, θstar p.1 p.2 *
                  (fderiv ℝ φ p (1, 0) + ∑ j : Fin 2, b p.1 p.2 j * fderiv ℝ φ p (0, basisVec j))
                  = 0) ∧
              (∀ g : Vec 2 → ℝ, MemL2On unitCube g →
                Tendsto (fun t => ∫ x in unitCube, θstar t x * g x) (𝓝[>] a)
                  (𝓝 (∫ x in unitCube, fstar x * g x))) ∧
              (∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∀ t ∈ Set.Icc (a + t₀) (a + T),
                IsZ2Periodic (θstar t) ∧ CsNormLe s (θstar t) (Cthm t₀ T * F)) ∧
              (∀ t₀ T : ℝ, 0 < t₀ → t₀ < T → ∃ C' : ℝ,
                ∀ t ∈ Set.Icc (a + t₀) (a + T), ∀ t' ∈ Set.Icc (a + t₀) (a + T), ∀ x : Vec 2,
                  |θstar t x - θstar t' x| ≤ C' * |t - t'| ^ (s / (1 + s))) ∧
              (∀ (Mi : ℕ → ℕ) (θ' : ℕ → ℝ → Vec 2 → ℝ),
                (∀ i, 1 ≤ Mi i ∧ κ i ∈ Set.Icc
                  (ocEpsilon q Λ (Mi i) ^ ((1 + α) - ocGamma α q) / 2)
                  (2 * ocEpsilon q Λ (Mi i) ^ ((1 + α) - ocGamma α q))) →
                (∀ i, ∀ T : ℝ, 0 < T →
                  IsWeakSolutionOn (streamVel (Φ (Mi i))) (κ i) a (a + T) (f i) (θ' i)) →
                ∀ φ : ℝ × Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
                  tsupport φ ⊆ Set.Ioi a ×ˢ Set.univ →
                  Tendsto (fun i => ∫ p, (θ i p.1 p.2 - θ' i p.1 p.2) * φ p) atTop (𝓝 0)) :=
  (roots_of_preservation hps).2.2.2.1 α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

/-- **`vanishing_diffusivity_limits_local` (statement verbatim) from
`preservation_successor` alone.** -/
theorem vanishing_diffusivity_limits_local_of_preservation
    (hps : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PreservationSuccessorStatement α s q ζ)
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ Φ : ℕ → ℝ → Vec 2 → ℝ, IsOCStreamSeq α q Λ ζ Φ →
        ∃ b : ℝ → Vec 2 → Vec 2,
          (∀ t x, Tendsto (fun M => streamVel (Φ M) t x) atTop (𝓝 (b t x))) ∧
          ∀ cT CT : ℝ, 0 < cT → 0 < CT → ∃ C₁ : ℝ, 0 < C₁ ∧
            ∀ (n : ℕ) (T R : ℝ), 2 ≤ n → 0 < T → 0 < R →
              cT * ocTauPP α q Λ (n - 1) ≤ T → T ≤ CT * ocTauPP α q Λ (n - 1) →
              8 * T * ocA α q Λ (n - 2) ≤ ocCStar →
              C₁ * max (ocEpsilon q Λ (n - 1) ^ α * T)
                  (Real.sqrt (sSup (ocBandSet α q Λ) * T)) ≤ R →
              R ≤ 1 / 8 →
              ∃ C : ℝ → ℝ → ℝ, ∀ t₁ : ℝ, ∀ X : ℝ → Vec 2 → ℝ → Vec 2,
                IsFlow (streamVel (Φ (n - 2))) X →
                ∀ (F : ℝ) (κ : ℕ → ℝ) (θ : ℕ → ℝ → Vec 2 → ℝ),
                  (∀ i, κ i ∈ ocBandSet α q Λ) → Tendsto κ atTop (𝓝 0) →
                  (∀ i, IsLocalEnergySolution b (κ i) (fun t y => X t y t₁) t₁ T R (θ i)) →
                  (∀ i, Real.sqrt ((volume (outerPipe (fun t y => X t y t₁) t₁ T R)).toReal⁻¹ *
                      ∫ p in outerPipe (fun t y => X t y t₁) t₁ T R, θ i p.1 p.2 ^ 2) ≤ F) →
                  ∃ (σ : ℕ → ℕ) (Θ : ℕ → ℝ → Vec 2 → ℝ) (θstar : ℝ → Vec 2 → ℝ),
                    StrictMono σ ∧
                    (∀ i, ContinuousOn (fun p : ℝ × Vec 2 => Θ i p.1 p.2)
                        {p | t₁ - 4 * T < p.1 ∧ p.1 ≤ t₁ ∧
                          ∃ y ∈ euclidBall 0 (R / 8), p.2 = X p.1 y t₁} ∧
                      (fun p : ℝ × Vec 2 => Θ i p.1 p.2) =ᵐ[volume.restrict
                        {p | t₁ - 4 * T < p.1 ∧ p.1 ≤ t₁ ∧
                          ∃ y ∈ euclidBall 0 (R / 8), p.2 = X p.1 y t₁}]
                        (fun p : ℝ × Vec 2 => θ i p.1 p.2)) ∧
                    (∀ K ⊆ {p : ℝ × Vec 2 | t₁ - 4 * T < p.1 ∧ p.1 ≤ t₁ ∧
                          ∃ y ∈ euclidBall 0 (R / 8), p.2 = X p.1 y t₁}, IsCompact K →
                      TendstoUniformlyOn (fun i (p : ℝ × Vec 2) => Θ (σ i) p.1 p.2)
                        (fun p : ℝ × Vec 2 => θstar p.1 p.2) atTop K) ∧
                    ContinuousOn (fun p : ℝ × Vec 2 => θstar p.1 p.2)
                      {p | t₁ - 4 * T < p.1 ∧ p.1 ≤ t₁ ∧
                        ∃ y ∈ euclidBall 0 (R / 8), p.2 = X p.1 y t₁} ∧
                    (∀ φ : ℝ × Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
                      tsupport φ ⊆ interior {p : ℝ × Vec 2 | t₁ - 4 * T < p.1 ∧ p.1 ≤ t₁ ∧
                          ∃ y ∈ euclidBall 0 (R / 8), p.2 = X p.1 y t₁} →
                      ∫ p, θstar p.1 p.2 *
                        (fderiv ℝ φ p (1, 0) +
                          ∑ j : Fin 2, b p.1 p.2 j * fderiv ℝ φ p (0, basisVec j)) = 0) ∧
                    ∀ ϱ ϑ : ℝ, 0 < ϱ → ϱ < 1 / 8 → 0 < ϑ → ϑ < 4 →
                    ∀ t ∈ Set.Icc (t₁ - ϑ * T) t₁,
                    ∀ x ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R),
                    ∀ y ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R),
                    ∀ z ∈ (fun y => X t y t₁) '' euclidBall 0 (ϱ * R), y ≠ z →
                      |θstar t x| + |θstar t y - θstar t z| /
                        Real.sqrt (vecNormSq (y - z)) ^ s ≤ C ϱ ϑ * F :=
  (roots_of_preservation hps).2.2.2.2 α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

end AVRegularity.Providers.Endgame
end
end
end
