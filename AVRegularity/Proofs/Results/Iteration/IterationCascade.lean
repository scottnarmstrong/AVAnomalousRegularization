-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Proofs.Results.Construction.PreservationSuccessor
import AVRegularity.IterationPassage.Cascade.OfOpenLeaves
public import AVRegularity.Definitions.Iteration.CascadeStatement
public import AVRegularity.Construction.Preservation.Assembly.PreparationJointInputs

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Assembly
namespace AVRegularity.Providers

/-! Toward the proof of `iteration_cascade_of_schedule`
(the statement below is a copy of its text).

`iteration_cascade_of_schedule_of_preservation`: the cascade from a schedule, conditional on
`preservation_successor` only (in the form of its text copy `PreservationSuccessorStatement`):
`iteration_cascade_of_schedule_of_open_leaves` (all leaves of the iteration argument proved,
`cascadeBottom` included), with the proof of `successor_bill`. When `preservation_successor` is
proved, the proof of `iteration_cascade_of_schedule` is this theorem applied to it, one
line. -/

/-- **The cascade from a schedule, conditional on `preservation_successor`.** -/
theorem iteration_cascade_of_schedule_of_preservation
    (hps0 : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PreservationSuccessorStatement α s q ζ)
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (K : ℕ) (Pacc t₀ T₀ : ℝ), 3 ≤ K → 0 < Pacc → 0 < t₀ → t₀ < T₀ →
    ∀ (r₀ D₀ : ℕ) (τe lamE σE : ℝ), 0 < τe → 0 < lamE → 0 < σE →
    ∀ (Q : ℝ) (H J N p nk Lc Lf Lpr Acl Naux Nout Kres L : ℕ) (σ₀ a σ : ℝ),
      IsCascadeSchedule α s q K Pacc lamE σE D₀ Q H J N p nk Lc Lf Lpr Acl Naux Nout Kres L σ₀ a σ →
      succReconFloor r₀ D₀ H J N p Acl Lc ≤ Naux →
      ∀ npad : ℕ, ∃ SX SZ Kneed : ℕ, ∀ sX sZ : ℕ, SX ≤ sX → SZ ≤ sZ →
      CascadeTail α s q ζ Λ c₀max φ₀ hφ₀ bw K Pacc t₀ T₀ r₀ D₀ τe lamE σE Q H J N p nk Lc Lf Lpr
        Naux Nout Kres npad sX sZ Kneed σ₀ :=
  IterationPassage.Cascade.iteration_cascade_of_schedule_of_open_leaves hps0
    (fun α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ => successor_bill α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)
    α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

/-- **The cascade from a schedule** (`t.iteration.cascade#conditional`). -/
theorem iteration_cascade_of_schedule (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (K : ℕ) (Pacc t₀ T₀ : ℝ), 3 ≤ K → 0 < Pacc → 0 < t₀ → t₀ < T₀ →
    ∀ (r₀ D₀ : ℕ) (τe lamE σE : ℝ), 0 < τe → 0 < lamE → 0 < σE →
    ∀ (Q : ℝ) (H J N p nk Lc Lf Lpr Acl Naux Nout Kres L : ℕ) (σ₀ a σ : ℝ),
      IsCascadeSchedule α s q K Pacc lamE σE D₀ Q H J N p nk Lc Lf Lpr Acl Naux Nout Kres L σ₀ a σ →
      succReconFloor r₀ D₀ H J N p Acl Lc ≤ Naux →
      ∀ npad : ℕ, ∃ SX SZ Kneed : ℕ, ∀ sX sZ : ℕ, SX ≤ sX → SZ ≤ sZ →
      CascadeTail α s q ζ Λ c₀max φ₀ hφ₀ bw K Pacc t₀ T₀ r₀ D₀ τe lamE σE Q H J N p nk Lc Lf Lpr
        Naux Nout Kres npad sX sZ Kneed σ₀ :=
  iteration_cascade_of_schedule_of_preservation preservation_successor
    α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

/-! Toward the proof of `iteration_passage`
(the statement below is a copy of its text).

`iteration_passage_of_preservation`: the iteration passage, conditional on
`preservation_successor` only (in the form of its text copy `PreservationSuccessorStatement`):
`iteration_passage_of_open_leaves` (all leaves of the iteration argument proved), with the proof of
`successor_bill`. When `preservation_successor` is proved, the proof of `iteration_passage`
is this theorem applied to it, one line. -/

/-- **The iteration passage, conditional on `preservation_successor`.** -/
theorem iteration_passage_of_preservation
    (hps0 : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PreservationSuccessorStatement α s q ζ)
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (K : ℕ) (Pacc : ℝ), 3 ≤ K → 0 < Pacc →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ → Pacc + q * iterZ α q s K + 4 < Q / 2 →
    ∀ (r₀ D₀ : ℕ) (τe lamE σE : ℝ), 0 < τe → 0 < lamE → 0 < σE →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min σE (ocDelta α q + σ₀)) lamE D₀ H J N p nk Lc Lf Lpr
        Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
      succReconFloor r₀ D₀ H J N p Acl Lc ≤ Naux →
    ∀ L : ℕ, IsPassageOrders α q s K Pacc σ₀ L N p nk Naux →
      IsCascadeWidths α q lamE a σ (succDstar D₀ N p H) →
    ∃ SX SZ Kneed : ℕ, ∀ sX sZ : ℕ, SX ≤ sX → SZ ≤ sZ →
    ∀ (Ce : ℝ) (kS : InvConsts), 1 ≤ Ce →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → kS.σf = σE → kS.lamC = lamE →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
      Kneed ≤ kS.Ks → Kneed ≤ kS.Kan → Kneed ≤ kS.Lan → Kneed ≤ kS.Jm →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∃ (C CQ : ℝ) (mStar : ℕ),
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
      IsSeedPointwiseMolecular law kS seed tS tf →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ (tA s₀ : ℝ), tS ≤ tA → tA + 3 * ocTau α q Λ m ≤ s₀ → s₀ + 4 * ocTauPP α q Λ m ≤ tf →
      tf - s₀ ≤ T₀ →
    ∀ (G G' : GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
    ∃ (tp : ℝ) (Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn G.comps, TorusHk Nout (ScalarH v.1.root))),
      PassageFrame law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seedK freshK φ₀ hφ₀ Mnat kI CI τe
        seed G (G'.retained m H J) m (succEta0 α q s) Kres
        (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card p Nout Naux Q CQ C tA s₀ tf
        tp Preg ∧
      PassageOutput law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀ G
        (G'.retained m H J) m p N (succSchedR r₀ J H) sX sZ K Naux s (succEta0 α q s)
        (ocMuS α q s) (ocDelta α q - 2 * σ₀) Pacc Q C kI.cr kI.c₀ s₀ tp tf (freshK (m - 1)) Preg :=
  IterationPassage.Cascade.iteration_passage_of_open_leaves hps0
    (fun α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ => successor_bill α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ)
    α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

/-- **The iteration passage**. -/
theorem iteration_passage (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (K : ℕ) (Pacc : ℝ), 3 ≤ K → 0 < Pacc →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ → Pacc + q * iterZ α q s K + 4 < Q / 2 →
    ∀ (r₀ D₀ : ℕ) (τe lamE σE : ℝ), 0 < τe → 0 < lamE → 0 < σE →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min σE (ocDelta α q + σ₀)) lamE D₀ H J N p nk Lc Lf Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
      succReconFloor r₀ D₀ H J N p Acl Lc ≤ Naux →
    ∀ L : ℕ, IsPassageOrders α q s K Pacc σ₀ L N p nk Naux →
      IsCascadeWidths α q lamE a σ (succDstar D₀ N p H) →
    ∃ SX SZ Kneed : ℕ, ∀ sX sZ : ℕ, SX ≤ sX → SZ ≤ sZ →
    ∀ (Ce : ℝ) (kS : InvConsts), 1 ≤ Ce →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → kS.σf = σE → kS.lamC = lamE →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
      Kneed ≤ kS.Ks → Kneed ≤ kS.Kan → Kneed ≤ kS.Lan → Kneed ≤ kS.Jm →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∃ (C CQ : ℝ) (mStar : ℕ),
    ∀ (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ → IsOCStreamSeq α q Λ ζ D.Φ →
    ∀ (M : ℕ), IsOCBandChain α q Λ ζ M D.κ → D.term = M → ∀ Mnat : ℕ, M ≤ Mnat →
    ∀ (law : BirthLaw),
      IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law →
    ∀ (seedK freshK : ℕ → KernelSpec),
      (∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')) →
    ∀ (seed : GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀) (n : ℕ) (tS tf : ℝ),
      IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀
        Mnat kS seed n tS tf Ce τe r₀ D₀ →
      IsSeedPointwiseMolecular law kS seed tS tf →
    ∀ (m : ℕ), mStar ≤ m → m ≤ n → n < M →
    ∀ (tA s₀ : ℝ), tS ≤ tA → tA + 3 * ocTau α q Λ m ≤ s₀ → s₀ + 4 * ocTauPP α q Λ m ≤ tf →
      tf - s₀ ≤ T₀ →
    ∀ (G G' : GenStage D ScalarH (succSchedD D₀ N p (H + 1)) bw j₀),
      IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G →
      G.level = m →
      IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
        hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
        (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G →
      IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G' →
    ∃ (tp : ℝ) (Preg : (∀ v : CompIn G.comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
        (∀ v : CompIn G.comps, TorusHk Nout (ScalarH v.1.root))),
      PassageFrame law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
        (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seedK freshK φ₀ hφ₀ Mnat kI CI τe
        seed G (G'.retained m H J) m (succEta0 α q s) Kres
        (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card p Nout Naux Q CQ C tA s₀ tf
        tp Preg ∧
      PassageOutput law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀ hφ₀ G
        (G'.retained m H J) m p N (succSchedR r₀ J H) sX sZ K Naux s (succEta0 α q s)
        (ocMuS α q s) (ocDelta α q - 2 * σ₀) Pacc Q C kI.cr kI.c₀ s₀ tp tf (freshK (m - 1)) Preg :=
  iteration_passage_of_preservation preservation_successor
    α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

/-! Toward the proof of `iteration_cascade`
(the statement below is a copy of its text).

`iteration_cascade_of_preservation`: the cascade, conditional on `preservation_successor` only
(in the form of its text copy `PreservationSuccessorStatement`): `iteration_cascade_of_ingredients`
(the order-choice proof) at `iteration_cascade_of_schedule_of_open_leaves`, with the
proof of `successor_bill`. When `preservation_successor` is proved, the proof of
`iteration_cascade` is this theorem applied to it, one line. -/

/-- **The cascade, conditional on `preservation_successor`.** -/
theorem iteration_cascade_of_preservation
    (hps0 : ∀ (α s : ℝ), 0 < α → α < 1 / 3 → 0 < s → s < (1 - α) / 2 →
      ∀ q, IsAdmissibleQ α s q → ∀ ζ : ℝ → ℝ, IsFastProfile ζ →
        PreservationSuccessorStatement α s q ζ)
    (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (K : ℕ) (Pacc t₀ T₀ : ℝ), 3 ≤ K → 0 < Pacc → 0 < t₀ → t₀ < T₀ →
    ∀ (r₀ D₀ : ℕ) (τe lamE σE : ℝ), 0 < τe → 0 < lamE → 0 < σE →
    ∃ (Q : ℝ) (H J N p nk Lc Lf Lpr Acl Naux Nout Kres L : ℕ) (σ₀ a σ : ℝ),
      IsCascadeSchedule α s q K Pacc lamE σE D₀ Q H J N p nk Lc Lf Lpr Acl Naux Nout Kres L σ₀ a σ ∧
      ∀ npad : ℕ, ∃ SX SZ Kneed : ℕ, ∀ sX sZ : ℕ, SX ≤ sX → SZ ≤ sZ →
      CascadeTail α s q ζ Λ c₀max φ₀ hφ₀ bw K Pacc t₀ T₀ r₀ D₀ τe lamE σE Q H J N p nk Lc Lf Lpr
        Naux Nout Kres npad sX sZ Kneed σ₀ :=
  IterationPassage.Assembly.iteration_cascade_of_ingredients
    (IterationPassage.Cascade.iteration_cascade_of_schedule_of_open_leaves hps0
      (fun α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ => successor_bill α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ))
    α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

/-- **The cascade**. -/
theorem iteration_cascade (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (K : ℕ) (Pacc t₀ T₀ : ℝ), 3 ≤ K → 0 < Pacc → 0 < t₀ → t₀ < T₀ →
    ∀ (r₀ D₀ : ℕ) (τe lamE σE : ℝ), 0 < τe → 0 < lamE → 0 < σE →
    ∃ (Q : ℝ) (H J N p nk Lc Lf Lpr Acl Naux Nout Kres L : ℕ) (σ₀ a σ : ℝ),
      IsCascadeSchedule α s q K Pacc lamE σE D₀ Q H J N p nk Lc Lf Lpr Acl Naux Nout Kres L σ₀ a σ ∧
      ∀ npad : ℕ, ∃ SX SZ Kneed : ℕ, ∀ sX sZ : ℕ, SX ≤ sX → SZ ≤ sZ →
      CascadeTail α s q ζ Λ c₀max φ₀ hφ₀ bw K Pacc t₀ T₀ r₀ D₀ τe lamE σE Q H J N p nk Lc Lf Lpr
        Naux Nout Kres npad sX sZ Kneed σ₀ :=
  iteration_cascade_of_preservation preservation_successor
    α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ

end AVRegularity.Providers
end
