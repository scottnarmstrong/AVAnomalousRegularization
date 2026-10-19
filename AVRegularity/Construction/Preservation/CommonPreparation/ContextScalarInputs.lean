-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.CommonPreparation.UniformAssembly
public import AVRegularity.Construction.Preservation.CommonPreparation.IncomingRecordRadii
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Assembly
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! **The literal prefix of `UniformCommonPreparationRouteStatement`, once**.

`UniformCommonPreparationRouteStatement α s q ζ` (module `CommonPreparation.UniformAssembly`)
chooses its constants in a fixed order: `Λ₀ → c₀max →` template, carrier width `→ Q, T₀ →
r₀, D₀, τ_e, λ_E, σ_E →` the schedule and the reserves `→ H_pr, K_need →` the slow and fast
orders `→ C_e, k_S` (with the `K_need` floors) `→` thresholds `thr, C_H, Υ → k_I →` ledger
thresholds `→ C_I, C_w, j₀ →` the constants `C_exp, C_joint, C_jet, m_*` and the data.

* `PrepPrefix α s q hprf Data`: that prefix around a predicate `Data` on the choices and on
  constants `x : X` chosen last, with a COMMON `H_pr = hprf(…)` given as a function of the choices
  before it (so that pieces stated with the same `hprf` join), and `K_need` existential.
* `PrepPrefix.and`: two statements with the same `hprf` give their conjunction (`K_need` by
  `max`, the thresholds by `certificateThresholdJoin`, the carrier and ledger thresholds by
  maxima, `c₀max` by a minimum, `Λ₀` by a maximum).
* `PrepPrefix.imp`: a consequence at fixed choices, with the hypotheses of the prefix as one
  structure `PrepFacts`.
* `uniformRoute_of_prefix`: `UniformCommonPreparationRouteStatement` from the prefix form whose
  data is `CommonPreparationRouteDataStatement` at `H_pr` and the constants `x`.

No witness is constructed here.

For `X = Unit` the statement is trivial, and `.and` of a statement with itself is again such
a statement. -/

/-- The choices before `H_pr`, as the arguments of the function choosing it. -/
abbrev PrepHpr : Type :=
  ℕ → (Vec 2 → ℝ) → ℝ → ℝ → ℝ → ℕ → ℕ → ℝ → ℝ → ℝ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ →
    ℕ → ℕ → ℕ → ℝ → ℝ → ℝ → ℕ

/-- A data statement of the preparation: a predicate on the choices
`Λ, φ₀, b, Q, T₀, r₀, D₀, τ_e, λ_E, σ_E, H, J, N, p, n_k, L_c, L_f, L_pr, A_cl, N_aux, N_out,
K_res, n_pad, σ₀, a, σ, H_pr, s_X, s_Z, C_e, k_S, k_I, C_I, C_w, j₀` and on the constants `x`. -/
abbrev PrepData (X : Type) : Type :=
  ℕ → (φ₀ : Vec 2 → ℝ) → Integrable φ₀ → ℝ → ℝ → ℝ → ℕ → ℕ → ℝ → ℝ → ℝ → ℕ → ℕ → ℕ → ℕ → ℕ →
    ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℝ → ℝ → ℝ → ℕ → ℕ → ℕ → ℝ → InvConsts → InvConsts → ℝ →
    ℝ → ℕ → X → Prop

/-- **The literal prefix of `UniformCommonPreparationRouteStatement`** around a data statement,
with `H_pr = hprf(…)`. -/
def PrepPrefix (α s q : ℝ) (hprf : PrepHpr) {X : Type} (Data : PrepData X) : Prop :=
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ c₀max : ℝ, 0 < c₀max ∧
    ∀ (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀), ContDiff ℝ (⊤ : ℕ∞) φ₀ → (∀ z, 0 ≤ φ₀ z) →
      ∫ z, φ₀ z = 1 → Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall →
    ∀ (bw : ℝ), 0 < bw → bw ≤ 1 / 10000 →
    ∀ (Q T₀ : ℝ), 0 < Q → 0 < T₀ →
    ∀ (r₀ D₀ : ℕ) (τe lamE σE : ℝ), 0 < τe → 0 < lamE → 0 < σE →
    ∀ (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad : ℕ) (σ₀ a σ : ℝ),
      IsSuccessorSchedule α q s Q σ₀ a σ (min σE (ocDelta α q + σ₀)) lamE D₀ H J N p nk Lc Lf
        Lpr Acl Naux Nout →
      Naux ≤ Kres → Kres + 2 * p ≤ Nout →
    ∃ Kneed : ℕ, ∀ sX sZ : ℕ,
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sX →
      max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sZ →
    ∀ (Ce : ℝ) (kS : InvConsts), 1 ≤ Ce →
      0 < kS.c₀ → kS.c₀ ≤ c₀max → 0 < kS.cr → kS.cr ≤ 1 → kS.σf = σE → kS.lamC = lamE →
      IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf →
      Kneed ≤ kS.Ks → Kneed ≤ kS.Kan → Kneed ≤ kS.Lan → Kneed ≤ kS.Jm →
    ∃ (thr : InvConsts) (CH Υ : ℝ), 1 ≤ CH ∧ 0 < Υ ∧ ∀ kI : InvConsts,
      IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q) →
    ∃ CIthr Cwthr : ℝ, ∀ (CI Cw : ℝ) (j₀ : ℕ), IsLedgerAdmissible Ce CI Cw CIthr Cwthr →
      IsCarrierStart α q Λ bw CH Υ j₀ →
    ∃ x : X, Data Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad
      σ₀ a σ (hprf Λ φ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a
        σ) sX sZ Ce kS kI CI Cw j₀ x

/-- The hypotheses of the prefix at fixed choices (the thresholds, which are chosen by the
statement, appear existentially). -/
structure PrepFacts (α s q : ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (bw Q T₀ : ℝ) (r₀ D₀ : ℕ)
    (τe lamE σE : ℝ) (H J N p nk Lc Lf Lpr Acl Naux Nout Kres : ℕ) (σ₀ a σ : ℝ) (sX sZ : ℕ)
    (Ce : ℝ) (kS kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) : Prop where
  hΛ : 128 ≤ Λ
  smooth : ContDiff ℝ (⊤ : ℕ∞) φ₀
  nonneg : ∀ z, 0 ≤ φ₀ z
  mass : ∫ z, φ₀ z = 1
  support : Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall
  hbw : 0 < bw
  hbw_le : bw ≤ 1 / 10000
  hQ : 0 < Q
  hT₀ : 0 < T₀
  hτe : 0 < τe
  hlamE : 0 < lamE
  hσE : 0 < σE
  sched : IsSuccessorSchedule α q s Q σ₀ a σ (min σE (ocDelta α q + σ₀)) lamE D₀ H J N p nk Lc
    Lf Lpr Acl Naux Nout
  hNaux : Naux ≤ Kres
  hNout : Kres + 2 * p ≤ Nout
  hsX : max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sX
  hsZ : max (N + succSchedD D₀ N p H) (2 * p) + succSchedD D₀ N p (H + 1) + 2 ≤ sZ
  hCe : 1 ≤ Ce
  hc₀ : 0 < kS.c₀
  hcr : 0 < kS.cr
  hcr_le : kS.cr ≤ 1
  hσf : kS.σf = σE
  hlamC : kS.lamC = lamE
  alloc : IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf
  admissible : ∃ thr : InvConsts,
    IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q (ocC α q)
  ledger : ∃ CIthr Cwthr : ℝ, IsLedgerAdmissible Ce CI Cw CIthr Cwthr
  start : ∃ CH Υ : ℝ, 1 ≤ CH ∧ 0 < Υ ∧ IsCarrierStart α q Λ bw CH Υ j₀

variable {α s q : ℝ} {hprf : PrepHpr} {X₁ X₂ : Type}

/-- **Two statements in prefix form with the same `H_pr` give their conjunction**, each with its
own constants; `K_need` is the maximum. -/
theorem PrepPrefix.and {D₁ : PrepData X₁} {D₂ : PrepData X₂}
    (h₁ : PrepPrefix α s q hprf D₁) (h₂ : PrepPrefix α s q hprf D₂) :
    PrepPrefix α s q hprf (X := X₁ × X₂)
      (fun Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ
        Hpr sX sZ Ce kS kI CI Cw j₀ x =>
        D₁ Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ
          Hpr sX sZ Ce kS kI CI Cw j₀ x.1 ∧
          D₂ Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ
            Hpr sX sZ Ce kS kI CI Cw j₀ x.2) := by
  obtain ⟨Λa, hΛa, ha⟩ := h₁
  obtain ⟨Λb, hΛb, hb⟩ := h₂
  refine ⟨max Λa Λb, by omega, ?_⟩
  intro Λ hΛ
  obtain ⟨ca, hca, ha⟩ := ha Λ (by omega)
  obtain ⟨cb, hcb, hb⟩ := hb Λ (by omega)
  refine ⟨min ca cb, lt_min hca hcb, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀ r₀ D₀ τe lamE σE hτe
    hlamE hσE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ hsched hNaux hNout
  obtain ⟨Ka, ha⟩ := ha φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀ r₀ D₀
    τe lamE σE hτe hlamE hσE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ hsched hNaux
    hNout
  obtain ⟨Kb, hb⟩ := hb φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀ r₀ D₀
    τe lamE σE hτe hlamE hσE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ hsched hNaux
    hNout
  refine ⟨max Ka Kb, ?_⟩
  intro sX sZ hsX hsZ Ce kS hCe hc₀ hc₀upper hcr hcrupper hσf hlamC halloc hKs hKan hLan hJm
  obtain ⟨ta, CHa, Υa, hCHa, hΥa, ha⟩ := ha sX sZ hsX hsZ Ce kS hCe hc₀
    (hc₀upper.trans (min_le_left _ _)) hcr hcrupper hσf hlamC halloc
    ((le_max_left _ _).trans hKs) ((le_max_left _ _).trans hKan) ((le_max_left _ _).trans hLan)
    ((le_max_left _ _).trans hJm)
  obtain ⟨tb, CHb, Υb, hCHb, hΥb, hb⟩ := hb sX sZ hsX hsZ Ce kS hCe hc₀
    (hc₀upper.trans (min_le_right _ _)) hcr hcrupper hσf hlamC halloc
    ((le_max_right _ _).trans hKs) ((le_max_right _ _).trans hKan)
    ((le_max_right _ _).trans hLan) ((le_max_right _ _).trans hJm)
  refine ⟨certificateThresholdJoin ta tb, max CHa CHb, max Υa Υb,
    hCHa.trans (le_max_left _ _), hΥa.trans_le (le_max_left _ _), ?_⟩
  intro kI hkI
  obtain ⟨CIa, Cwa, ha⟩ := ha kI (invariant_admissible_threshold_left hkI)
  obtain ⟨CIb, Cwb, hb⟩ := hb kI (invariant_admissible_threshold_right hkI)
  refine ⟨max CIa CIb, max Cwa Cwb, ?_⟩
  intro CI Cw j₀ hledger hstart
  have hLa : IsLedgerAdmissible Ce CI Cw CIa Cwa :=
    ⟨hledger.1, (le_max_left _ _).trans hledger.2.1,
      (le_max_left _ _).trans hledger.2.2.1, hledger.2.2.2⟩
  have hLb : IsLedgerAdmissible Ce CI Cw CIb Cwb :=
    ⟨hledger.1, (le_max_right _ _).trans hledger.2.1,
      (le_max_right _ _).trans hledger.2.2.1, hledger.2.2.2⟩
  have hA : ∀ i, 0 ≤ ocA α q Λ i := fun _ => (Real.rpow_pos_of_pos
    (Construction.Stream.ocEpsilon_pos (by omega : 1 ≤ Λ)) _).le
  have hT : ∀ i, 0 ≤ ocTauPP α q Λ i := fun _ => (Construction.Stream.ocTauPP_pos (by omega)).le
  obtain ⟨xa, ha⟩ := ha CI Cw j₀ hLa (IsCarrierStart.mono hA hT
    (le_max_left _ _) (le_max_left _ _) (zero_le_one.trans hCHa) hΥa.le hstart)
  obtain ⟨xb, hb⟩ := hb CI Cw j₀ hLb (IsCarrierStart.mono hA hT
    (le_max_right _ _) (le_max_right _ _) (zero_le_one.trans hCHb) hΥb.le hstart)
  exact ⟨(xa, xb), ha, hb⟩

/-- **A consequence at fixed choices**, with the hypotheses of the prefix available. -/
theorem PrepPrefix.imp {D₁ : PrepData X₁} {D₂ : PrepData X₂}
    (h : PrepPrefix α s q hprf D₁)
    (himp : ∀ (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (bw Q T₀ : ℝ) (r₀ D₀ : ℕ)
      (τe lamE σE : ℝ) (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad : ℕ) (σ₀ a σ : ℝ)
      (sX sZ : ℕ) (Ce : ℝ) (kS kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ),
      PrepFacts α s q Λ φ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres
        σ₀ a σ sX sZ Ce kS kI CI Cw j₀ →
      ∀ x : X₁, D₁ Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad
        σ₀ a σ (hprf Λ φ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀
        a σ) sX sZ Ce kS kI CI Cw j₀ x →
        ∃ y : X₂, D₂ Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad
          σ₀ a σ (hprf Λ φ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad
          σ₀ a σ) sX sZ Ce kS kI CI Cw j₀ y) :
    PrepPrefix α s q hprf D₂ := by
  obtain ⟨Λ₀, hΛ₀, h⟩ := h
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ
  obtain ⟨c₀max, hc₀max, h⟩ := h Λ hΛ
  refine ⟨c₀max, hc₀max, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀ r₀ D₀ τe lamE σE hτe
    hlamE hσE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ hsched hNaux hNout
  obtain ⟨Kneed, h⟩ := h φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀ r₀
    D₀ τe lamE σE hτe hlamE hσE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ hsched hNaux
    hNout
  refine ⟨Kneed, ?_⟩
  intro sX sZ hsX hsZ Ce kS hCe hc₀ hc₀upper hcr hcrupper hσf hlamC halloc hKs hKan hLan hJm
  obtain ⟨thr, CH, Υ, hCH, hΥ, h⟩ := h sX sZ hsX hsZ Ce kS hCe hc₀ hc₀upper hcr hcrupper hσf
    hlamC halloc hKs hKan hLan hJm
  refine ⟨thr, CH, Υ, hCH, hΥ, ?_⟩
  intro kI hkI
  obtain ⟨CIthr, Cwthr, h⟩ := h kI hkI
  refine ⟨CIthr, Cwthr, ?_⟩
  intro CI Cw j₀ hledger hstart
  obtain ⟨x, hx⟩ := h CI Cw j₀ hledger hstart
  exact himp Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ
    sX sZ Ce kS kI CI Cw j₀
    { hΛ := hΛ₀.trans hΛ, smooth := hφsmooth, nonneg := hφpos, mass := hφint,
      support := hφsupport, hbw := hbw, hbw_le := hbwupper, hQ := hQ, hT₀ := hT₀, hτe := hτe,
      hlamE := hlamE, hσE := hσE, sched := hsched, hNaux := hNaux, hNout := hNout, hsX := hsX,
      hsZ := hsZ, hCe := hCe, hc₀ := hc₀, hcr := hcr, hcr_le := hcrupper, hσf := hσf,
      hlamC := hlamC, alloc := halloc, admissible := ⟨thr, hkI⟩,
      ledger := ⟨CIthr, Cwthr, hledger⟩, start := ⟨CH, Υ, hCH, hΥ, hstart⟩ } x hx

/-- **`UniformCommonPreparationRouteStatement` from its prefix form**: the data is the route data
statement at `H_pr = hprf(…)` and the constants `x = (C_exp, C_joint, C_jet, m_*)`. -/
theorem uniformRoute_of_prefix {ζ : ℝ → ℝ}
    (h : PrepPrefix α s q hprf (X := ℝ × ℝ × ℝ × ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe _lamE _σE H J N p nk _Lc _Lf _Lpr _Acl Naux Nout _Kres npad σ₀
          _a _σ Hpr sX sZ Ce kS kI CI Cw j₀ x =>
        CommonPreparationRouteDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux
          Nout npad sX sZ σ₀ kI CI Cw j₀ Hpr x.1 x.2.1 x.2.2.1 Q T₀ x.2.2.2)) :
    UniformCommonPreparationRouteStatement α s q ζ := by
  obtain ⟨Λ₀, hΛ₀, h⟩ := h
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ
  obtain ⟨c₀max, hc₀max, h⟩ := h Λ hΛ
  refine ⟨c₀max, hc₀max, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀ r₀ D₀ τe lamE σE hτe
    hlamE hσE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ hsched hNaux hNout
  obtain ⟨Kneed, h⟩ := h φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀ r₀
    D₀ τe lamE σE hτe hlamE hσE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ hsched hNaux
    hNout
  refine ⟨hprf Λ φ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ,
    Kneed, ?_⟩
  intro sX sZ hsX hsZ Ce kS hCe hc₀ hc₀upper hcr hcrupper hσf hlamC halloc hKs hKan hLan hJm
  obtain ⟨thr, CH, Υ, hCH, hΥ, h⟩ := h sX sZ hsX hsZ Ce kS hCe hc₀ hc₀upper hcr hcrupper hσf
    hlamC halloc hKs hKan hLan hJm
  refine ⟨thr, CH, Υ, hCH, hΥ, ?_⟩
  intro kI hkI
  obtain ⟨CIthr, Cwthr, h⟩ := h kI hkI
  refine ⟨CIthr, Cwthr, ?_⟩
  intro CI Cw j₀ hledger hstart
  obtain ⟨x, hx⟩ := h CI Cw j₀ hledger hstart
  exact ⟨x.1, x.2.1, x.2.2.1, x.2.2.2, hx⟩

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open Homogenization
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Numeric source and tail inputs at the actual preparation choices.
The schedule already pays q sigma_f Lpr, the seed allocation supplies the
actual moment reserve, and the ledger admission gives CI >= 1. The early
insertion depth then pays the kernel tail before every stage datum.
The degenerate cases are included: empty, singleton and edgeless families need no nonzero
coefficient; the smallest requested orders satisfy the same literal schedule. No
constant is obtained by dividing a datum norm or using a nonempty fibre. -/

variable {α s q : ℝ} {Λ : ℕ} {φ₀ : Vec 2 → ℝ} {bw Q T₀ : ℝ} {r₀ D₀ : ℕ}
  {τe lamE σE : ℝ} {H J N p nk Lc Lf Lpr Acl Naux Nout Kres : ℕ}
  {σ₀ a σ : ℝ} {sX sZ : ℕ} {Ce CI Cw : ℝ} {kS kI : InvConsts} {j₀ : ℕ}

/-- The existing prefix hypotheses give every numeric reserve/sign used
by the same native, copied, moment and finite-expansion route. -/
theorem preparation_context_numeric_orders
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q)
    (f : PrepFacts α s q Λ φ₀ bw Q T₀ r₀ D₀ τe lamE σE
      H J N p nk Lc Lf Lpr Acl Naux Nout Kres σ₀ a σ sX sZ Ce kS kI CI Cw j₀) :
    0 < kI.c₀ ∧ 0 < kI.cr ∧ 1 ≤ CI ∧ Lpr ≤ kI.Lker ∧
      0 < kI.σf ∧ Q < q * kI.σf * (Lpr : ℝ) ∧
      Naux + 2 * p ≤ Nout ∧
      0 < min (ocDelta α q / 4) τe ∧
      1 ≤ preparationInsertionDepth (q * min (ocDelta α q / 4) τe) Q ∧
      Q < q * min (ocDelta α q / 4) τe *
        ((preparationInsertionDepth (q * min (ocDelta α q / 4) τe) Q : ℝ) + 1) := by
  obtain ⟨thr, hk⟩ := f.admissible
  obtain ⟨hc₀, hcr, _, _, _, _, hσf, _, _, _, _, _, _, _, hmoment, _⟩ := hk
  rw [f.hσf] at hσf
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hgain, _⟩ := f.sched
  rw [← hσf] at hgain
  have hq₀ : 0 < q := zero_lt_one.trans hq.1
  have hprod : 0 < q * kI.σf * (Lpr : ℝ) :=
    (add_pos f.hQ (by norm_num : (0 : ℝ) < 3)).trans hgain
  have hσ : 0 < kI.σf := pos_of_mul_pos_right
    (pos_of_mul_pos_left hprod (Nat.cast_nonneg Lpr)) hq₀.le
  obtain ⟨CIthr, Cwthr, hledger⟩ := f.ledger
  have hδ := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  have hθ : 0 < min (ocDelta α q / 4) τe :=
    lt_min (div_pos hδ (by norm_num)) f.hτe
  have hdepth := preparation_insertion_tail_order (mul_pos hq₀ hθ) Q
  exact ⟨hc₀.symm ▸ f.hc₀, hcr.symm ▸ f.hcr, f.hCe.trans hledger.1,
    (le_max_left _ _).trans hmoment, hσ,
    (lt_add_of_pos_right Q (by norm_num : (0 : ℝ) < 3)).trans hgain,
    (Nat.add_le_add_right f.hNaux _).trans f.hNout,
    hθ, hdepth.1, hdepth.2⟩

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Assembly
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! **The data of the common preparation as one context**.

* `PrepCtx`: the binders of `CommonPreparationRouteDataStatement` from the scale data `D` to the
  actual successor `G'`, without the level
  threshold `m_* ≤ m`, as one structure.
* `PrepCtx.request`: the literal `Request` of the statement (law, provenance parameters,
  kernels, template, incoming stage, `c_r = k_I.c_r`, `c₀ = k_I.c₀`, `Q`, `s = s₀`, `t_f`, `p`,
  `N_out`, `N_aux`, `H_pr`).
* `prepRouteData_of_ctx`: `CommonPreparationRouteDataStatement` from its form over contexts,
  `∀ c, m_* ≤ c.m → Nonempty (PreparationRouteWitness c.request C_exp C_joint C_jet)`.
* `uniformRoute_of_ctx`: `UniformCommonPreparationRouteStatement` from the prefix form
  (`PrepPrefix`) of that statement over contexts.
* elementary facts of a context: the level, `m < term`, the band chain in the letters of `D`,
  `κ_m, κ_{m-1} > 0`, the masses are positive, the window.

No witness is constructed here.

An empty component family is a context, and `t_p` does not occur (the endpoint is a field of
the witness). -/

/-- The data of a preparation request after the choices of the prefix. -/
structure PrepCtx (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ) (Hpr : ℕ) (Q T₀ : ℝ)
    (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] where
  D : OCData
  hα : D.α = α
  hq : D.q = q
  hΛ : D.Λ = Λ
  hζ : D.ζ = ζ
  hseq : IsOCStreamSeq α q Λ ζ D.Φ
  M : ℕ
  hband : IsOCBandChain α q Λ ζ M D.κ
  hterm : D.term = M
  Mnat : ℕ
  hMnat : M ≤ Mnat
  law : BirthLaw
  hlaw : IsSuccessorLaw α q s (wordsUpTo (succAlphabetOf r₀ D₀ H J N p npad) (J + 1)).card law
  seedK : ℕ → KernelSpec
  freshK : ℕ → KernelSpec
  hfresh : ∀ b', 1 ≤ b' → b' < M → IsFreshKernel D kI.cr σ₀ nk.toPNat' b' (freshK b')
  seed : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀
  n : ℕ
  tS : ℝ
  tf : ℝ
  hseed : IsGeneratedSeed law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
    hφ₀ Mnat kS seed n tS tf Ce τe r₀ D₀
  hpw : IsSeedPointwiseMolecular law kS seed tS tf
  m : ℕ
  hmn : m ≤ n
  hnM : n < M
  tA : ℝ
  s₀ : ℝ
  htA : tS ≤ tA
  hs₀ : tA + 3 * ocTau α q Λ m ≤ s₀
  htf : s₀ + 4 * ocTauPP α q Λ m ≤ tf
  hT₀ : tf - s₀ ≤ T₀
  G : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀
  G' : GenStage D hr (succSchedD D₀ N p (H + 1)) bw j₀
  hcascade : IsCascadeStage D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
    (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) seed G
  hlevel : G.level = m
  hinv : IsStageInvariant law (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p) seedK freshK φ₀
    hφ₀ Mnat kI tA tf (CI * D.eps m ^ min (ocDelta α q / 4) τe)
    (CI * D.eps (m - 1) ^ (q * min (ocDelta α q / 4) τe)) G
  hactual : IsActualSuccessor D (succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p)
    (succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) G G'

namespace PrepCtx

variable {α s q : ℝ} {ζ : ℝ → ℝ} {Λ : ℕ} {φ₀ : Vec 2 → ℝ} {hφ₀ : Integrable φ₀}
  {bw Ce τe : ℝ} {kS : InvConsts} {r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ} {σ₀ : ℝ}
  {kI : InvConsts} {CI Cw : ℝ} {j₀ Hpr : ℕ} {Q T₀ : ℝ}
  {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
  (c : PrepCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
    j₀ Hpr Q T₀ hr)

/-- **The literal request of the route data statement.** -/
def request : Request hr c.D (succSchedD D₀ N p (H + 1)) bw j₀ :=
  { law := c.law, P := succProvParams c.D Cw kI.cr σ₀ (succEta0 α q s) N p,
    seedK := c.seedK, freshK := c.freshK, φ₀ := φ₀, hφ₀ := hφ₀, G := c.G,
    cr := kI.cr, c₀ := kI.c₀, Q := Q, s := c.s₀, tf := c.tf, p := p,
    Nout := Nout, Naux := Naux, Hpr := Hpr }

theorem request_level : c.request.G.level = c.m := c.hlevel

theorem m_le_M : c.m ≤ c.M := le_trans c.hmn c.hnM.le

/-- The level of a context is strictly below the terminal level. -/
theorem m_lt_term : c.m < c.D.term := by
  rw [c.hterm]
  exact lt_of_le_of_lt c.hmn c.hnM

theorem m_le_term : c.m ≤ c.D.term := c.m_lt_term.le

/-- The band chain in the letters of the data. -/
theorem bandD : IsOCBandChain c.D.α c.D.q c.D.Λ c.D.ζ c.D.term c.D.κ := by
  rw [c.hα, c.hq, c.hΛ, c.hζ, c.hterm]
  exact c.hband

theorem lambda_ge (hΛ : 128 ≤ Λ) : 128 ≤ c.D.Λ := by
  rw [c.hΛ]
  exact hΛ

theorem q_gt (hq : 1 < q) : 1 < c.D.q := by
  rw [c.hq]
  exact hq

/-- The diffusivity of the level. -/
theorem kappa_pos (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) : 0 < c.D.κ c.m :=
  CycleReference.bandChain_pos hΛ hζ c.hband c.m_le_M

/-- The diffusivity of the parent level. -/
theorem kappa_pred_pos (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) : 0 < c.D.κ (c.m - 1) :=
  CycleReference.bandChain_pos hΛ hζ c.hband (le_trans (Nat.sub_le _ _) c.m_le_M)

/-- The cell diffusivity of the incoming stage is the diffusivity of the level. -/
theorem kap_eq : c.D.kap c.G.level = c.D.κ c.m := by
  unfold OCData.kap
  rw [c.hlevel, min_eq_left c.m_le_term]

/-- The masses of the incoming stage are positive. -/
theorem mass_pos (hq : 1 < q) (hΛ : 128 ≤ Λ) (v : CompIn c.G.comps) :
    0 < c.G.mass c.law v := by
  unfold GenStage.mass
  exact Construction.Preservation.Buffer.birth_compMass_pos (c.q_gt hq) (c.lambda_ge hΛ) c.law v.1

/-- The start of the preparation is after the start of the invariant. -/
theorem tA_le_s₀ (hΛ : 1 ≤ Λ) : c.tA ≤ c.s₀ := by
  have h := c.hs₀
  have hτ : 0 < ocTau α q Λ c.m := Construction.Stream.ocTau_pos hΛ
  linarith

/-- The window of the preparation. -/
theorem s₀_le_tf (hΛ : 1 ≤ Λ) : c.s₀ ≤ c.tf := by
  have h := c.htf
  have hτ : 0 < ocTauPP α q Λ c.m := Construction.Stream.ocTauPP_pos hΛ
  linarith

end PrepCtx

/-- **The route data statement from its form over contexts.** -/
theorem prepRouteData_of_ctx {α s q : ℝ} {ζ : ℝ → ℝ} {Λ : ℕ} {φ₀ : Vec 2 → ℝ}
    {hφ₀ : Integrable φ₀} {bw Ce τe : ℝ} {kS : InvConsts}
    {r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ} {σ₀ : ℝ} {kI : InvConsts} {CI Cw : ℝ}
    {j₀ Hpr : ℕ} {Cexp Cjoint Cjet Q T₀ : ℝ} {mStar : ℕ}
    (h : ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
      [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
      (c : PrepCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI
        CI Cw j₀ Hpr Q T₀ hr), mStar ≤ c.m →
      Nonempty (PreparationRouteWitness c.request Cexp Cjoint Cjet)) :
    CommonPreparationRouteDataStatement α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout
      npad sX sZ σ₀ kI CI Cw j₀ Hpr Cexp Cjoint Cjet Q T₀ mStar := by
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw hr _ _ _ _ _ _ _ seedK freshK
    hfresh seed n tS tf hseed hpw m hm hmn hnM tA s₀ htA hs₀ htf hT₀ G G' hcascade hlevel hinv
    hactual
  exact h
    { D := D, hα := hDα, hq := hDq, hΛ := hDΛ, hζ := hDζ, hseq := hseq, M := M, hband := hband,
      hterm := hterm, Mnat := Mnat, hMnat := hMnat, law := law, hlaw := hlaw, seedK := seedK,
      freshK := freshK, hfresh := hfresh, seed := seed, n := n, tS := tS, tf := tf,
      hseed := hseed, hpw := hpw, m := m, hmn := hmn, hnM := hnM, tA := tA, s₀ := s₀,
      htA := htA, hs₀ := hs₀, htf := htf, hT₀ := hT₀, G := G, G' := G', hcascade := hcascade,
      hlevel := hlevel, hinv := hinv, hactual := hactual }
    hm

/-- The route witnesses at every context of level `≥ m_*`, with the constants
`x = (C_exp, C_joint, C_jet, m_*)`. -/
def PrepWitnessCtxAt (α s q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (bw Ce τe : ℝ) (kS : InvConsts) (r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ) (σ₀ : ℝ)
    (kI : InvConsts) (CI Cw : ℝ) (j₀ Hpr : ℕ) (Q T₀ : ℝ) (x : ℝ × ℝ × ℝ × ℕ) : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
    [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
    (c : PrepCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI
      Cw j₀ Hpr Q T₀ hr), x.2.2.2 ≤ c.m →
    Nonempty (PreparationRouteWitness c.request x.1 x.2.1 x.2.2.1)

/-- **`UniformCommonPreparationRouteStatement` from the route witnesses at every context**, in
the prefix form with `H_pr = hprf(…)`. -/
theorem uniformRoute_of_ctx {α s q : ℝ} {ζ : ℝ → ℝ} {hprf : PrepHpr}
    (h : PrepPrefix α s q hprf (X := ℝ × ℝ × ℝ × ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe _lamE _σE H J N p nk _Lc _Lf _Lpr _Acl Naux Nout _Kres npad σ₀
          _a _σ Hpr sX sZ Ce kS kI CI Cw j₀ x =>
        PrepWitnessCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀
          kI CI Cw j₀ Hpr Q T₀ x)) :
    UniformCommonPreparationRouteStatement α s q ζ := by
  refine uniformRoute_of_prefix (h.imp ?_)
  intro Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ
    sX sZ Ce kS kI CI Cw j₀ _hfacts x hx
  exact ⟨x, prepRouteData_of_ctx (fun c hm => hx c hm)⟩

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Requested envelopes of the ORIGINAL incoming stage, in the literal
uniform prefix. All finite order functions are chosen before Ce and kS.
The seed uses its supplied pointwise envelope and reserve; strict
descendants use the shared context estimate and IncomingRecordRadii.
For actual contexts the inner reserve can be zero: no uniform gap between
kI.mEnv and the minimum producer reserve is assumed.

The case Hpr=0, empty or singleton components and an edgeless seed all use the same actual
family. The output precedes masses and data. The seed's radius is never inferred
from its original record lengths. This is a bounded uniform envelope join,
not a common-preparation witness or a prepared model. -/

/-- Any finite requested caps chosen at the allowed prefix are supported by
the seed reserve and by a common threshold on Ca/Cm, uniformly at late stages. -/
def OriginalStageEnvelopeJoinStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  ∀ hprf ksFn kanFn lanFn jmFn : PrepHpr,
    PrepPrefix α s q hprf (X := ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout
          Kres npad σ₀ a σ Hpr sX sZ Ce kS kI CI Cw j₀ mStar =>
        let cap := fun f : PrepHpr =>
          f Λ φ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ
        ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
          [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
          [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
          (c : PrepCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀
            kI CI Cw j₀ Hpr Q T₀ hr), mStar ≤ c.m →
        ∀ K : CompIn c.G.comps × Fin (Hpr + 1) → ℕ, (∀ v, K v ≤ cap ksFn) →
          NativeCopyEnvelopesStatement c.G
            (preparationEnvelopeOrders kI (cap ksFn) (cap kanFn) (cap lanFn) (cap jmFn))
            (Set.Icc c.s₀ c.tf) (rhoStar c.D kI.c₀ c.G.level) Hpr K)

end AVRegularity.Construction.Preservation.CommonPreparation
end
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! Instantiate the scalar prefix at the ORIGINAL incoming context and its
actual buffer endpoint. The same radius, delay, drift and cover are used by
the native frame and the joint preparation of the copied family; no preparation witness is
chosen. The degenerate cases are included: empty and singleton families, interior seed, zero
finite orders, identity geometry, edgeless stages and arbitrary buffer starts use the same
scalars. No lower endpoint bound is inferred from a nonempty component. -/

open AVRegularity.Construction.Preservation.Assembly WindowCover

variable {α s q : ℝ} {ζ : ℝ → ℝ} {Λ : ℕ} {φ₀ : Vec 2 → ℝ} {hφ₀ : Integrable φ₀}
  {bw Ce τe : ℝ} {kS : InvConsts} {r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ} {σ₀ : ℝ}
  {kI : InvConsts} {CI Cw : ℝ} {j₀ Hpr : ℕ} {Q T₀ : ℝ}
  {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]
  (c : PrepCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw
    j₀ Hpr Q T₀ hr)

/-- Actual scalar inputs shared by the native path and the joint preparation of the copied
family. -/
structure PreparationContextScales (g₀ cOld Crat : ℝ) : Prop where
  diffusivity_pos : 0 < c.D.κ c.m
  radius_pos : 0 < rhoStar c.D kI.c₀ c.G.level
  radius_molecular : rhoStar c.D kI.c₀ c.G.level = ocRhoMol α q Λ c.m kI.c₀ (c.D.κ c.m)
  entrance_pos : 0 < cOld * ocEpsilon q Λ c.m ^ (1 + ocGamma α q / 2 + ocDelta α q)
  entrance_le : cOld * ocEpsilon q Λ c.m ^ (1 + ocGamma α q / 2 + ocDelta α q) ≤
    rhoStar c.D kI.c₀ c.G.level
  radius_ratio : rhoStar c.D kI.c₀ c.G.level /
      (cOld * ocEpsilon q Λ c.m ^ (1 + ocGamma α q / 2 + ocDelta α q)) ≤
    Crat * ocEpsilon q Λ (c.m - 1) ^ (-(q * ocDelta α q))
  buffer_after : c.s₀ ≤ c.request.bufferEnd
  buffer_delay : c.request.bufferEnd ≤ c.s₀ + 2 * ocTauPP α q Λ c.m
  model_window : Set.Icc c.request.bufferEnd
      (c.request.bufferEnd + 2 * ocTauPP α q Λ c.m) ⊆ Set.Icc c.s₀ c.tf
  drift : ∀ (a b : ℝ) (Kmax : ℕ), Providers.WeakGen.Comparison.TorusDriftData
    (c.D.κ c.m) (rhoStar c.D kI.c₀ c.G.level) a b (streamVel (c.D.Φ c.m)) Kmax
  cover : ∀ (hφ : IsAdmissibleStream (c.D.Φ (c.m - 1))) (qJ Kmax : ℕ),
    ∃ (l₀ : ℤ) (P : ℕ), 1 ≤ P ∧
      ((l₀ : ℝ) - 1 / 2) * ocTauPP α q Λ c.m ≤ c.request.bufferEnd ∧
      c.request.bufferEnd < ((l₀ : ℝ) + 1 / 2) * ocTauPP α q Λ c.m ∧
      c.request.bufferEnd + 2 * ocTauPP α q Λ c.m ≤
        ((l₀ : ℝ) + P - 1 / 2) * ocTauPP α q Λ c.m ∧
      CommonPreparationWindowCoverStatement α q Λ c.m ζ c.D.Φ hφ
        (c.D.κ c.m) (c.D.κ (c.m - 1)) c.request.bufferEnd 2 kI.c₀
        (windowCoverCg * (ocA α q Λ (c.m - 1) * ocTauPP α q Λ c.m)) g₀
        (windowCoverCd * ocA α q Λ c.m * ocEpsilon q Λ c.m ^ 2 / c.D.κ c.m)
        windowCoverB0 1 windowCoverCb qJ Kmax windowCoverCG l₀ P 0

/-- Radius rewriting and scalar interval algebra instantiate the actual
prefix; all drift/cover analysis is already the scalar environment. -/
theorem preparation_context_scalar_inputs (hΛ : 128 ≤ Λ) (hζ : IsFastProfile ζ)
    (hc₀ : 0 < kI.c₀) (g₀ cOld Crat : ℝ) (mStar : ℕ)
    (henv : PreparationScalarEnvironmentAt α q ζ Λ g₀ kI.c₀ cOld Crat mStar)
    (hm : mStar ≤ c.m) : PreparationContextScales c g₀ cOld Crat := by
  have hΛ1 : 1 ≤ Λ := (by norm_num : 1 ≤ 128).trans hΛ
  have hκ := c.kappa_pos hΛ1 hζ
  have he : 0 < ocEpsilon q Λ c.m := Stream.ocEpsilon_pos hΛ1
  have ha : 0 < ocA α q Λ c.m := Real.rpow_pos_of_pos he _
  let ρ := kI.c₀ * min (ocEpsilon q Λ c.m) (Real.sqrt (c.D.κ c.m / ocA α q Λ c.m))
  have hρ : rhoStar c.D kI.c₀ c.G.level = ρ := by
    simp only [rhoStar, OCData.eps, c.hlevel, c.hq, c.hΛ, c.hα, ρ]
  have hρpos : 0 < ρ := (Buffer.molecular_radius_bounds hc₀ he hκ ha).1
  have hscalar := henv c.M c.D.κ c.hband c.m hm (c.hmn.trans_lt c.hnM)
  obtain ⟨hradii, hdelay, hdrift, hcover⟩ :=
    And.intro hscalar.1 (hscalar.2 c.D.Φ c.hseq)
  have hbuf : c.request.bufferEnd = c.s₀ + ρ ^ 2 / c.D.κ c.m := by
    change c.s₀ + rhoStar c.D kI.c₀ c.G.level ^ 2 / c.D.κ c.G.level = _
    rw [hρ, c.hlevel]
  have hafter : c.s₀ ≤ c.request.bufferEnd := by
    rw [hbuf]
    exact le_add_of_nonneg_right (div_nonneg (sq_nonneg ρ) hκ.le)
  have hupper : c.request.bufferEnd ≤ c.s₀ + 2 * ocTauPP α q Λ c.m := by
    rw [hbuf]
    exact add_le_add le_rfl hdelay
  refine ⟨hκ, hρ ▸ hρpos, hρ.trans hradii.1, hradii.2.1,
    hradii.2.2.1.trans_eq hρ.symm, ?_, hafter, hupper, ?_, ?_, ?_⟩
  · rw [hρ]
    exact hradii.2.2.2
  · intro t ht
    refine ⟨hafter.trans ht.1, ?_⟩
    calc t ≤ c.request.bufferEnd + 2 * ocTauPP α q Λ c.m := ht.2
      _ ≤ (c.s₀ + 2 * ocTauPP α q Λ c.m) + 2 * ocTauPP α q Λ c.m :=
        add_le_add hupper le_rfl
      _ = c.s₀ + 4 * ocTauPP α q Λ c.m := by ring
      _ ≤ c.tf := c.htf
  · intro a b Kmax
    rw [hρ]
    exact hdrift a b Kmax
  · intro hφ qJ Kmax
    exact hcover hφ c.request.bufferEnd qJ Kmax

end AVRegularity.Construction.Preservation.CommonPreparation
end
end
