-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Construction.Preservation.CommonPreparation.ContextScalarInputs
public import AVRegularity.Construction.StageEnvelopes.SuccessorPreparation
import AVRegularity.Construction.StageEnvelopes.Cauchy.Assembly
import AVRegularity.Construction.Preservation.Assembly.PreparationJointOfInputs
import AVRegularity.Proofs.Results.CycleJoint.CycleJoint
import AVRegularity.Definitions.Finite.FiniteLiftBridge

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The final prefix assembly transports the same-route context producer
under the literal uniform choices. Its two named inputs are the produced
numeric prefix and the pointwise join of the staffed frame/finite/model
ingredients. The statement takes the context
producer as a hypothesis.
The degenerate cases are included: empty and singleton roots, Hpr=0, smallest orders,
identity geometry, zero datum and an edgeless seed retain the same quantifier order. In
particular no root instance, mass or datum can affect the early reserves. -/

/-- Logical join of the actual fixed-choice context producer into the
uniform route. All constants are chosen in the prefix order;
the last callback must produce witnesses of the SAME three route joins. -/
def UniformPreparationPrefixAssemblyStatement (α s q : ℝ) (ζ : ℝ → ℝ)
    (hprf : PrepHpr) {X : Type} (Data : PrepData X)
    (_prefix : PrepPrefix α s q hprf Data)
    (_contexts : ∀ (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
      (bw Q T₀ : ℝ) (r₀ D₀ : ℕ) (τe lamE σE : ℝ)
      (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad : ℕ) (σ₀ a σ : ℝ)
      (sX sZ : ℕ) (Ce : ℝ) (kS kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ),
      PrepFacts α s q Λ φ₀ bw Q T₀ r₀ D₀ τe lamE σE
        H J N p nk Lc Lf Lpr Acl Naux Nout Kres σ₀ a σ sX sZ Ce kS kI CI Cw j₀ →
      ∀ x : X, Data Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE
        H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ
        (hprf Λ φ₀ bw Q T₀ r₀ D₀ τe lamE σE
          H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ)
        sX sZ Ce kS kI CI Cw j₀ x →
      ∃ y : ℝ × ℝ × ℝ × ℕ,
        PrepWitnessCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS
          r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw j₀
          (hprf Λ φ₀ bw Q T₀ r₀ D₀ τe lamE σE
            H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ) Q T₀ y) : Prop :=
  UniformCommonPreparationRouteStatement α s q ζ

/-! **The final prefix assembly of the common preparation**
(`UniformPreparationPrefixAssemblyStatement`).

`uniformPreparationPrefixAssembly`: from a statement in the literal prefix form
(`PrepPrefix` with the supplied `H_pr = hprf(…)`) and a producer of the route witnesses at
every context from its data at fixed choices (with the facts of the prefix), the uniform route
`UniformCommonPreparationRouteStatement`, by ONE `PrepPrefix.imp` and
`uniformRoute_of_ctx`. This is a conditional logical assembly: both inputs are hypotheses.

For `X = Unit` or the data statement `True` the join is trivial, and empty component
families are allowed. -/

/-- **The final prefix assembly**: the uniform route from the prefix form and the producer of the
route witnesses at fixed choices. -/
theorem uniformPreparationPrefixAssembly (α s q : ℝ) (ζ : ℝ → ℝ)
    (hprf : PrepHpr) {X : Type} (Data : PrepData X)
    (hpre : PrepPrefix α s q hprf Data)
    (hctx : ∀ (Λ : ℕ) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
      (bw Q T₀ : ℝ) (r₀ D₀ : ℕ) (τe lamE σE : ℝ)
      (H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad : ℕ) (σ₀ a σ : ℝ)
      (sX sZ : ℕ) (Ce : ℝ) (kS kI : InvConsts) (CI Cw : ℝ) (j₀ : ℕ),
      PrepFacts α s q Λ φ₀ bw Q T₀ r₀ D₀ τe lamE σE
        H J N p nk Lc Lf Lpr Acl Naux Nout Kres σ₀ a σ sX sZ Ce kS kI CI Cw j₀ →
      ∀ x : X, Data Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE
        H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ
        (hprf Λ φ₀ bw Q T₀ r₀ D₀ τe lamE σE
          H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ)
        sX sZ Ce kS kI CI Cw j₀ x →
      ∃ y : ℝ × ℝ × ℝ × ℕ,
        PrepWitnessCtxAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS
          r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI Cw j₀
          (hprf Λ φ₀ bw Q T₀ r₀ D₀ τe lamE σE
            H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ) Q T₀ y) :
    UniformPreparationPrefixAssemblyStatement α s q ζ hprf Data hpre hctx :=
  uniformRoute_of_ctx (hpre.imp hctx)

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.StageEnvelopes
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! **The requested envelopes of the original incoming stage at a preparation context, by
case** (the original-stage envelope join).

At a context `c` (`PrepCtx`) the incoming stage `c.G` is a cascade stage of the generated seed.

* `ctx_seedCopyEnvelopes`: if `c.G` is the seed, the copied envelopes at the requested orders
  and the constants of `k_I` on `[s₀, t_f]` from the seed invariant and the supplied pointwise
  envelope (`seedCopyEnvelopes`).
* `ctx_descendantCopyEnvelopes`: if `c.G` lies strictly below the seed, the same from the
  shared context estimate `est` at the successor envelope parameters of `k_S` with the requested
  orders (`native_copy_envelopes_of_context`): the context certificate and the natural pieces of
  the incoming invariant, the retained grade bound (reserve `2/(H_prod+1)`), the inner reserve
  `k_I.𝗆_env < 1/(H_prod+1)`, the carrier environment and the higher record lengths (an input,
  given by `incoming_higher_record_radii`).
* `ctx_incomingLengths`: those lengths from `IncomingHigherRecordRadiiStatement`'s clause.

The cases `H_pr = 0`, an empty family and `c.m = c.n` (the seed) are included. -/

variable {α s q : ℝ} {ζ : ℝ → ℝ} {Λ : ℕ} {φ₀ : Vec 2 → ℝ} {hφ₀ : Integrable φ₀}
  {bw Ce τe : ℝ} {kS : InvConsts} {r₀ D₀ H J N p nk Naux Nout npad sX sZ : ℕ} {σ₀ : ℝ}
  {kI : InvConsts} {CI Cw : ℝ} {j₀ Hpr : ℕ} {Q T₀ : ℝ}
  {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)]

/-- The window of the preparation lies in the window of the seed. -/
theorem ctx_window_sub (c : PrepCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux
    Nout npad sX sZ σ₀ kI CI Cw j₀ Hpr Q T₀ hr) (hΛ : 1 ≤ Λ) :
    Set.Icc c.s₀ c.tf ⊆ Set.Icc c.tS c.tf :=
  Set.Icc_subset_Icc (c.htA.trans (c.tA_le_s₀ hΛ)) le_rfl

/-- **The seed case at a context.** -/
theorem ctx_seedCopyEnvelopes (c : PrepCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk
    Naux Nout npad sX sZ σ₀ kI CI Cw j₀ Hpr Q T₀ hr) (hGS : c.G = c.seed) (hq : 1 < q)
    (hΛ : 128 ≤ Λ) (h1 : 1 ≤ c.m) (hj : j₀ ≤ c.m) (K : CompIn c.G.comps × Fin (Hpr + 1) → ℕ)
    {Ks Kan Lan Jm : ℕ} (hK : ∀ v, K v ≤ Ks) (hKs : Ks ≤ kS.Ks) (hKan : Kan ≤ kS.Kan)
    (hLan : Lan ≤ kS.Lan) (hJm : Jm ≤ kS.Jm) (hCa : kS.Ca ≤ kI.Ca)
    (hCm : ∀ j, kS.Cm j ≤ kI.Cm j) (hc : kI.c₀ = kS.c₀) :
    NativeCopyEnvelopesStatement c.G (preparationEnvelopeOrders kI Ks Kan Lan Jm)
      (Set.Icc c.s₀ c.tf) (rhoStar c.D kI.c₀ c.G.level) Hpr K := by
  obtain ⟨_, _, _, _, _, _, _, hinvS, _⟩ := c.hseed
  have hlev : c.seed.level = c.m := by rw [← hGS, c.hlevel]
  exact seedCopyEnvelopes c.G c.seed hGS c.law kS kI _ c.seedK c.freshK φ₀ hφ₀ c.Mnat c.tS
    c.tf _ _ hinvS c.hpw (c.q_gt hq) (c.lambda_ge hΛ) (by rw [hlev]; exact h1)
    (by rw [hlev]; exact hj) (ctx_window_sub c (by omega)) Hpr K hK hKs hKan hLan hJm hCa
    hCm hc

/-- **The higher record lengths of the incoming stage** at a context strictly below its seed, from
the clause of `IncomingHigherRecordRadiiStatement` at `Λ` and `c₀`. -/
theorem ctx_incomingLengths (c : PrepCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk
    Naux Nout npad sX sZ σ₀ kI CI Cw j₀ Hpr Q T₀ hr) {c₀ : ℝ} {m₀ : ℕ}
    (hrad : ∀ (hr : ℕ → Type) [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
      (D : OCData), D.α = α → D.q = q → D.Λ = Λ → D.ζ = ζ →
      IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ →
      ∀ (Dm : ℕ) (bw : ℝ) (j₀ : ℕ) (Mn : SuccMenu) (Cw cr σ₀ η₀ : ℝ) (N p : ℕ), cr ≤ 1 →
      ∀ (seed G : GenStage D hr Dm bw j₀),
        seed.HasTags (succProvParams D Cw cr σ₀ η₀ N p) →
        (∀ v u (γ : seed.fam.Γ v u), 1 ≤ (seed.fam.identity v u γ).record.birthExcess →
          (seed.fam.identity v u γ).record.length ≤ D.eps seed.level) →
        seed.level ≤ D.term →
        IsCascadeStage D (succProvParams D Cw cr σ₀ η₀ N p) Mn seed G →
        m₀ ≤ G.level → G.level < seed.level →
        ∀ v u (γ : G.fam.Γ v u), 3 ≤ (G.fam.identity v u γ).maxOrder →
          (G.fam.identity v u γ).record.length ≤ rhoStar D c₀ G.level)
    (hcr : kI.cr ≤ 1) (hm₀ : m₀ ≤ c.m) (hlt : c.G.level < c.seed.level) :
    ∀ v u (γ : c.G.fam.Γ v u), 3 ≤ (c.G.fam.identity v u γ).maxOrder →
      (c.G.fam.identity v u γ).record.length ≤ rhoStar c.D c₀ c.G.level := by
  obtain ⟨hsl, _, _, _, _, hid, _, hinvS, _⟩ := c.hseed
  have hseedterm : c.seed.level ≤ c.D.term := by
    rw [hsl, c.hterm]
    exact c.hnM.le
  exact hrad hr c.D c.hα c.hq c.hΛ c.hζ c.bandD _ bw j₀ _ Cw kI.cr σ₀ (succEta0 α q s) N p hcr
    c.seed c.G hinvS.2.1 (fun v u γ hbe =>
      ((hid v u γ).2.2 hbe).trans_eq (congrArg c.D.eps hsl.symm)) hseedterm
    c.hcascade (by rw [c.hlevel]; exact hm₀) hlt

/-- **The descendant case at a context**: the copied envelopes at the requested orders from the
shared context estimate at the successor envelope parameters with those orders. -/
theorem ctx_descendantCopyEnvelopes (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s)
    (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) (hΛ : 128 ≤ Λ) (hζ : IsFastProfile ζ)
    (hbw : 0 < bw) (hbwupper : bw ≤ 1 / 10000) {thr : InvConsts} {Kres Lpr Lc Lf : ℕ}
    (hkI : IsInvariantAdmissible kS thr kI H J N p nk Kres Lpr Lc Lf σ₀ (ocDelta α q) q
      (ocC α q)) (hc₀ : 0 < kS.c₀) (hc₀one : kS.c₀ ≤ 1) {CH Υ : ℝ}
    (hcarrier : CarrierOK 100 CH Υ) (hstart : IsCarrierStart α q Λ bw CH Υ j₀)
    (Ks Kan Lan Jm : ℕ)
    (est : ContextEnvelopeEstimate
      { successorEnvelopeParameters α s q Λ ζ hα₀ hα₁ hs₀ hs₁ hq hΛ hζ bw hbw hbwupper kS
          (succSchedD D₀ N p (H + 1)) with Ks := Ks, Kan := Kan, Lan := Lan, Jm := Jm })
    (hCa : est.Ca ≤ kI.Ca) (hCm : ∀ j, est.Cm j ≤ kI.Cm j)
    (c : PrepCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad sX sZ σ₀ kI CI
      Cw j₀ Hpr Q T₀ hr) (hfloor : est.levelFloor ≤ c.m) (h1 : 1 ≤ c.m) (hj : j₀ ≤ c.m)
    (hlt : c.G.level < c.seed.level)
    (hlen : ∀ v u (γ : c.G.fam.Γ v u), 3 ≤ (c.G.fam.identity v u γ).maxOrder →
      (c.G.fam.identity v u γ).record.length ≤ rhoStar c.D kI.c₀ c.G.level)
    (K : CompIn c.G.comps × Fin (Hpr + 1) → ℕ) (hK : ∀ v, K v ≤ Ks) :
    NativeCopyEnvelopesStatement c.G (preparationEnvelopeOrders kI Ks Kan Lan Jm)
      (Set.Icc c.s₀ c.tf) (rhoStar c.D kI.c₀ c.G.level) Hpr K := by
  have hgrade := cascade_grade_le c.hcascade hlt
  rcases hkI with ⟨hcEq, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hKs, _, hKan, _,
    hLan, _, hJm, _, _, _, hHprod, hprod, henvnonneg, _, henvlt⟩
  have hΛ1 : 1 ≤ Λ := by omega
  have hqD : 1 < c.D.q := c.q_gt hq.1
  have hΛD : 128 ≤ c.D.Λ := c.lambda_ge hΛ
  have hε (i : ℕ) : 0 < c.D.eps i := Construction.Stream.ocEpsilon_pos (by omega)
  have hκ : 0 < c.D.κ c.G.level := by
    rw [c.hlevel]
    exact c.kappa_pos hΛ1 hζ
  have hcI : 0 < kI.c₀ := hcEq.symm ▸ hc₀
  have hcIone : kI.c₀ ≤ 1 := hcEq.symm ▸ hc₀one
  have hinner : kI.mEnv ≤ 1 / ((kS.Hprod : ℝ) + 1) := by
    rw [← hHprod]
    exact henvlt.le
  have hres (v : CompIn c.G.comps) : 2 / ((kS.Hprod : ℝ) + 1) ≤ compReserve kI v.1 := by
    rw [← hHprod]
    exact retained_compReserve_ge hprod (hgrade v)
  have hinput : ContextEnvelopeInput
      (successorEnvelopeParameters α s q Λ ζ hα₀ hα₁ hs₀ hs₁ hq hΛ hζ bw hbw hbwupper kS
        (succSchedD D₀ N p (H + 1))) c.G kI kI.mEnv (rhoStar c.D kI.c₀ c.G.level) :=
    { bw_eq := rfl
      alpha_eq := c.hα
      q_eq := c.hq
      base_eq := c.hΛ
      profile_eq := c.hζ
      stream := c.hseq
      natural := ⟨c.Mnat, c.hinv.1⟩
      certified := c.hinv.2.2.2.2.2.1
      level_pos := by rw [c.hlevel]; exact h1
      carrier_start := by rw [c.hlevel]; exact hj
      carrier_environment := ⟨CH, Υ, hcarrier, by rw [c.hα, c.hq, c.hΛ]; exact hstart⟩
      q_pos := hqD
      large := hΛD
      kap_pos := by rw [c.kap_eq]; exact c.kappa_pos hΛ1 hζ
      radius_pos := mul_pos hcI
        (lt_min (hε _) (Real.sqrt_pos.mpr (div_pos hκ (Real.rpow_pos_of_pos (hε _) _))))
      radius_le := (mul_le_mul_of_nonneg_left (min_le_left _ _) hcI.le).trans
        (mul_le_of_le_one_left (hε _).le hcIone)
      wavelength_le := Providers.CascadeInvariants.eps_le_of_le hqD hΛD (Nat.sub_le _ _)
      inner_nonneg := henvnonneg
      inner_le := hinner
      reserve_le := hres
      reserve_upper := fun v => (Buffer.compReserve_le_one kI v.1).trans (by norm_num)
      slot_order := hKs
      slow_order := hKan
      fast_order := hLan
      molecular_order := hJm
      source_order := fun v u γ => (c.G.fam.identity v u γ).le_D
      higher_length := hlen }
  exact native_copy_envelopes_of_context _ Ks Kan Lan Jm est c.G c.law kI subset_rfl _ Hpr K hK
    hinput (by rw [c.hlevel]; exact hfloor) hCa hCm

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The original-stage operator tower under the literal uniform prefix.
The order is an early function, never bounded by kI.Ks. Normalized
regularizer constants depend on kI, so the operator-price constant may be
chosen after kI but before CI/Cw/j0 and every actual stage datum; its
late-level floor is then chosen after CI/j0, exactly as the native
operator producer does. The degenerate cases are included: empty and singleton families, the seed
itself, order zero, Dm=2, identity geometry and an edgeless stage use the same clauses.
The constant/kernel/width equalities are the unchanged tower fields. -/

/-- The native source and tower producer instantiated at every
original context in the uniform prefix. No retained successor is substituted. -/
def NativePreparationOperatorPrefixStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  ∀ hprf KbufFn : PrepHpr,
    PrepPrefix α s q hprf (X := ℝ × ℕ)
      (fun Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout
          Kres npad σ₀ a σ Hpr sX sZ Ce kS kI CI Cw j₀ x =>
        let Kbuf := KbufFn Λ φ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout
          Kres npad σ₀ a σ
        0 ≤ x.1 ∧ 2 ≤ x.2 ∧
        ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
          [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
          [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)] [∀ r, Nontrivial (hr r)]
          (c : PrepCtx α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk Naux Nout npad
            sX sZ σ₀ kI CI Cw j₀ Hpr Q T₀ hr), x.2 ≤ c.m →
          Nonempty (PreparationNativeTower c.request Kbuf (fun j => max (kI.cker j) 0)
            (x.1 * (CI * c.D.eps c.m ^ min (ocDelta α q / 4) τe))))

end AVRegularity.Construction.Preservation.CommonPreparation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Assembly
open AVRegularity.Construction.StageEnvelopes
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! **The original-stage envelope join** (`OriginalStageEnvelopeJoinStatement`).

`originalStageEnvelopeJoin`: for all order functions `H_pr, K_s, K_an, L_an, J_m` of the
choices before `H_pr`, the requested copied envelopes of the original incoming stage on
`[s₀, t_f]` at the radius `ρ_*(k_I.c₀)`, in the literal prefix `PrepPrefix`. The choices:

* `K_need` is the maximum of the four requested caps, `c₀^max = 1`;
* after `k_S`: the shared context estimate `est` (`context_stage_envelopes`) at the successor
  envelope parameters of `k_S` (`successorEnvelopeParameters`, `D_* = D_{succ}(H+1)`) with the
  requested caps; the thresholds `{k_S with C_a := est.C_a, C_m := est.C_m}`; `C_H = 1` and `Υ`
  from `common_carrier_constants`;
* after `j₀`: `m_* = max m₀ (max (j₀+2) est.levelFloor)`, with `m₀ ≥ 2` the floor of
  `incoming_higher_record_radii` at `Λ` and `k_I.c₀`.

At a context the incoming stage is the seed (`ctx_seedCopyEnvelopes`: the seed invariant and
the supplied pointwise envelope at `k_S`, the caps at most `K_need ≤` the orders of `k_S`) or
lies strictly below it (`ctx_descendantCopyEnvelopes` with `ctx_incomingLengths`).

The cases `K_need = 0`, `H_pr = 0`, the seed level `c.m = c.n` and an empty family are
included. -/

/-- **The original-stage envelope join.** -/
theorem originalStageEnvelopeJoin (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s)
    (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ)
    (hζ : IsFastProfile ζ) : OriginalStageEnvelopeJoinStatement α s q ζ := by
  intro hprf ksFn kanFn lanFn jmFn
  obtain ⟨Λr, hΛr, hrad⟩ := incoming_higher_record_radii hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨Λr, hΛr, ?_⟩
  intro Λ hΛ
  have h128 : 128 ≤ Λ := by omega
  refine ⟨1, one_pos, ?_⟩
  intro φ₀ hφ₀ _ _ _ _ bw hbw hbwupper Q T₀ _ _ r₀ D₀ τe lamE σE _ _ _ H J N p nk Lc Lf Lpr Acl
    Naux Nout Kres npad σ₀ a σ _ _ _
  let cap : PrepHpr → ℕ := fun f =>
    f Λ φ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ
  refine ⟨max (cap ksFn) (max (cap kanFn) (max (cap lanFn) (cap jmFn))), ?_⟩
  intro sX sZ _ _ Ce kS _ hc₀ hc₀upper _ hcrupper _ _ _ hKsN hKanN hLanN hJmN
  have hKs : cap ksFn ≤ kS.Ks := (le_max_left _ _).trans hKsN
  have hKan : cap kanFn ≤ kS.Kan := ((le_max_left _ _).trans (le_max_right _ _)).trans hKanN
  have hLan : cap lanFn ≤ kS.Lan :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hLanN
  have hJm : cap jmFn ≤ kS.Jm :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hJmN
  obtain ⟨est⟩ := Cauchy.context_stage_envelopes
    { successorEnvelopeParameters α s q Λ ζ hα₀ hα₁ hs₀ hs₁ hq h128 hζ bw hbw hbwupper kS
        (succSchedD D₀ N p (H + 1)) with
      Ks := cap ksFn, Kan := cap kanFn, Lan := cap lanFn, Jm := cap jmFn }
  obtain ⟨Υ, hcarrier, _⟩ :=
    Cauchy.common_carrier_constants (α := α) (q := q) (b := bw) h128 le_rfl one_pos
  have hΥ : 0 < Υ := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hcarrier.2)
  refine ⟨{ kS with Ca := est.Ca, Cm := est.Cm }, 1, Υ, le_rfl, hΥ, ?_⟩
  intro kI hkI
  have hkI' := hkI
  rcases hkI' with ⟨hcEq, hcrEq, _, _, _, _, _, _, _, _, hCaS, hCa, hCm, _⟩
  have hcI : 0 < kI.c₀ := hcEq.symm ▸ hc₀
  have hcrI : kI.cr ≤ 1 := hcrEq.symm ▸ hcrupper
  refine ⟨0, 0, ?_⟩
  intro CI Cw j₀ _ hstart
  obtain ⟨m₀, hm₀, hrad'⟩ := hrad Λ hΛ kI.c₀ hcI
  refine ⟨max m₀ (max (j₀ + 2) est.levelFloor), ?_⟩
  dsimp only
  intro hr _ _ _ _ _ _ _ c hm K hK
  have h1 : 1 ≤ c.m := by omega
  have hj : j₀ ≤ c.m := by omega
  have hG1 : 1 ≤ c.G.level := by rw [c.hlevel]; exact h1
  rcases cascade_lt_or_eq c.hcascade hG1 with hlt | hGS
  · exact ctx_descendantCopyEnvelopes hα₀ hα₁ hs₀ hs₁ hq h128 hζ hbw hbwupper hkI hc₀
      hc₀upper hcarrier hstart (cap ksFn) (cap kanFn) (cap lanFn) (cap jmFn) est hCa
      (fun j => (hCm j).2) c (by omega) h1 hj hlt
      (ctx_incomingLengths c hrad' hcrI (by omega) hlt) K hK
  · exact ctx_seedCopyEnvelopes c hGS hq.1 h128 h1 hj K hK hKs hKan hLan hJm hCaS
      (fun j => (hCm j).1) hcEq

end AVRegularity.Construction.Preservation.CommonPreparation
end
end
end

section
section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-! The shared scalar environment in the literal preparation choice order.
The g0 of the joint preparation is a function of frequency fixed before every finite
request and seed. The molecular cap and common late-level floor respect
that order. This prefix can be conjoined with the proved original-envelope
prefix using PrepPrefix.and, without strengthening the joint preparation.
The selected radius cap is retained in the callback data for the native
buffer, as well as used in the threshold choice.
The degenerate cases are included: arbitrary depth function, zero reserves, empty and singleton
roots, identity geometry and an edgeless seed have the same choices. All interior
levels, streams, finite drift requests and buffer starts remain quantified. -/

/-- The scalar constants in the data part of the uniform prefix. -/
def preparationScalarPrefixData (α q : ℝ) (ζ : ℝ → ℝ) (g₀ : ℕ → ℝ) :
    PrepData (ℝ × ℝ × ℕ) :=
  fun Λ _φ₀ _hφ₀ _bw _Q _T₀ _r₀ _D₀ _τe _lamE _σE
      _H _J _N _p _nk _Lc _Lf _Lpr _Acl _Naux _Nout _Kres _npad _σ₀ _a _σ
      _Hpr _sX _sZ _Ce _kS kI _CI _Cw _j₀ x =>
    0 < x.1 ∧ 0 < x.2.1 ∧ 2 ≤ x.2.2 ∧
      PreparationScalarEnvironmentAt α q ζ Λ (g₀ Λ) kI.c₀ x.1 x.2.1 x.2.2 ∧
      kI.c₀ ≤ Buffer.exists_molecular_uniform_constants.choose ∧ kI.c₀ ≤ 1

/-- The scalar prefix for any early insertion-depth function and any
positive frequency-wise cover tolerance of the joint preparation. -/
def PreparationScalarPrefixStatement (α s q : ℝ) (ζ : ℝ → ℝ) : Prop :=
  ∀ (hprf : PrepHpr) (g₀ : ℕ → ℝ), (∀ Λ, 128 ≤ Λ → 0 < g₀ Λ) →
    PrepPrefix α s q hprf (preparationScalarPrefixData α q ζ g₀)

/-- Scalar choices fit the literal prefix: radii of kI equal those of kS,
and all other threshold and carrier choices are harmless lower bounds.
There is no dependence on an actual root, stage, window or datum. -/
theorem preparation_scalar_prefix {α s q : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    PreparationScalarPrefixStatement α s q ζ := by
  intro hprf g₀ hg₀
  obtain ⟨Λ₀, hΛ₀, cmax, hcmax, hcbuffer, hc1, henv⟩ :=
    preparation_scalar_environment hα₀ hα₁ hs₀ hs₁ hq hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ
  refine ⟨cmax, hcmax, ?_⟩
  intro φ₀ hφ₀ _ _ _ _ bw _ _ Q T₀ _ _ r₀ D₀ τe lamE σE _ _ _
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ _ _ _
  refine ⟨0, ?_⟩
  intro sX sZ _ _ Ce kS _ hc₀ hc₀max _ _ _ _ _ _ _ _ _
  refine ⟨kS, 1, 1, le_rfl, zero_lt_one, ?_⟩
  intro kI hkI
  refine ⟨0, 0, ?_⟩
  intro CI Cw j₀ _ _
  have hcI : 0 < kI.c₀ := hkI.1.symm ▸ hc₀
  have hcImax : kI.c₀ ≤ cmax := hkI.1.symm ▸ hc₀max
  obtain ⟨cOld, Crat, hcOld, hCrat, mStar, hmStar, hscalar⟩ :=
    henv Λ hΛ (g₀ Λ) kI.c₀ (hg₀ Λ (hΛ₀.trans hΛ)) hcI hcImax
  exact ⟨(cOld, Crat, mStar), hcOld, hCrat, hmStar, hscalar, hcImax.trans hcbuffer, hcImax.trans hc1⟩

end AVRegularity.Construction.Preservation.CommonPreparation
end
end

section
section
/-! Common prefix for the scalar environment and the original incoming
stage envelopes. One max of reserve floors and common carrier/certificate
thresholds precedes all actual contexts; no retained successor replaces G.
This is an unconditional ingredient prefix, not the uniform route itself.
The degenerate cases (empty and singleton components, the seed itself, any insertion depth, zero
finite caps, identity geometry and edgeless seeds) are included in the two producers. The same
depth function is used by both. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-- The original-stage envelopes as the data part of the uniform prefix. -/
def preparationEnvelopePrefixData (α s q : ℝ) (ζ : ℝ → ℝ)
    (ksFn kanFn lanFn jmFn : PrepHpr) : PrepData ℕ :=
  fun Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout
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
            (Set.Icc c.s₀ c.tf) (rhoStar c.D kI.c₀ c.G.level) Hpr K

/-- The paired inputs share all thresholds and early choices. The raw
constants are retained so the final callback can select one common level. -/
def preparationJoinedPrefixData (α s q : ℝ) (ζ : ℝ → ℝ)
    (ksFn kanFn lanFn jmFn : PrepHpr) (g₀ : ℕ → ℝ) :
    PrepData (ℕ × (ℝ × ℝ × ℕ)) :=
  fun Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout
      Kres npad σ₀ a σ Hpr sX sZ Ce kS kI CI Cw j₀ x =>
    preparationEnvelopePrefixData α s q ζ ksFn kanFn lanFn jmFn
      Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout
      Kres npad σ₀ a σ Hpr sX sZ Ce kS kI CI Cw j₀ x.1 ∧
    preparationScalarPrefixData α q ζ g₀
      Λ φ₀ hφ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout
      Kres npad σ₀ a σ Hpr sX sZ Ce kS kI CI Cw j₀ x.2

/-- Original envelopes and scalar buffer and joint-preparation inputs under ONE common
literal prefix; the max/min threshold construction is the proved .and. -/
theorem preparation_scalar_and_envelope_prefix {α s q : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (hprf ksFn kanFn lanFn jmFn : PrepHpr) (g₀ : ℕ → ℝ)
    (hg₀ : ∀ Λ, 128 ≤ Λ → 0 < g₀ Λ) :
    PrepPrefix α s q hprf
      (preparationJoinedPrefixData α s q ζ ksFn kanFn lanFn jmFn g₀) := by
  have henv : PrepPrefix α s q hprf
      (preparationEnvelopePrefixData α s q ζ ksFn kanFn lanFn jmFn) :=
    originalStageEnvelopeJoin α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
      hprf ksFn kanFn lanFn jmFn
  have hscalar := preparation_scalar_prefix hα₀ hα₁ hs₀ hs₁ hq hζ hprf g₀ hg₀
  exact henv.and hscalar

end AVRegularity.Construction.Preservation.CommonPreparation
end
end

section
/-! The original-stage operator tower under the literal uniform prefix, from proved native
producer `preparation_native_operators` and source package
`preparation_source_of_generated_seed`, at the original request `c.request` of each context.

Choices: `Λ₀` is given by the native operator; `c₀max = 1`; `K_need = 0`; the certificate thresholds
are `kS` and `C_H = Υ = 1` (neutral); `C_I`/`C_w` thresholds are `0`. After `kI`, the order is the
early `KbufFn` value, `Dm = succSchedD D₀ N p (H+1)`, and `CK = max (kI.cker ·) 0`; the native
operator then fixes the price constant `A` before `C_I`, `C_w`, `j₀`, and its late-level floor `m_*`
after `C_I` and `j₀`. The source package reads only the context's seed, cascade and invariant
clauses together with `kI.c₀ = kS.c₀ ≤ 1`, `kI.cr = kS.cr ≤ 1` and `kI.Hprod = kI.G0 + H + 1`
(admissibility). No retained successor, no `Kbuf ≤ kI.Ks` and no stored-order premise.
The degenerate cases are included: empty/singleton component families, the seed itself (`m = n`),
order zero, an edgeless stage and identity geometry pass through the same clauses. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Assembly
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-- The orders of the successor schedule are at least two. -/
theorem opPrefix_two_le_succSchedD (D₀ N p H : ℕ) : 2 ≤ succSchedD D₀ N p (H + 1) := by
  show 2 ≤ succSchedD D₀ N p H + 2 * N + 4 * p + 4
  omega

/-- **The native operator tower in the literal uniform prefix.** -/
theorem nativePreparationOperatorPrefix (α s : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1 / 3)
    (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2) (q : ℝ) (hq : IsAdmissibleQ α s q)
    (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) : NativePreparationOperatorPrefixStatement α s q ζ := by
  intro hprf KbufFn
  obtain ⟨Λ₀, hΛ₀, hW⟩ := preparation_native_operators α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  have hδ : 0 < ocDelta α q := ocDelta_pos_of_admissible hα₀ hq
  refine ⟨Λ₀, hΛ₀, fun Λ hΛ => ⟨1, one_pos, ?_⟩⟩
  intro φ₀ hφ₀ _ _ _ _ bw hbw _ Q T₀ _ _ r₀ D₀ τe lamE σE hτe _ _ H J N p nk Lc Lf Lpr Acl Naux
    Nout Kres npad σ₀ a σ _ _ _
  refine ⟨0, ?_⟩
  intro sX sZ _ _ Ce kS _ hc₀ hc₀upper _ hcrupper _ _ _ _ _ _ _
  refine ⟨kS, 1, 1, le_rfl, one_pos, ?_⟩
  intro kI hkI
  obtain ⟨hc0I, hcrI, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, hprodI, -, -, -⟩ := hkI
  refine ⟨0, 0, ?_⟩
  intro CI Cw j₀ _ _
  obtain ⟨A, hA, hW⟩ := hW Λ hΛ bw hbw
    (KbufFn Λ φ₀ bw Q T₀ r₀ D₀ τe lamE σE H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ)
    (succSchedD D₀ N p (H + 1)) (opPrefix_two_le_succSchedD D₀ N p H)
    (fun j => max (kI.cker j) 0) (fun j _ => le_max_right _ _)
  obtain ⟨mStar, hmStar, hW⟩ := hW CI (min (ocDelta α q / 4) τe) kI.c₀
    (lt_min (by positivity) hτe) (hc0I ▸ hc₀) (hc0I ▸ hc₀upper) j₀
  refine ⟨(A, mStar), ?_⟩
  dsimp only
  refine ⟨hA, hmStar, ?_⟩
  intro hr _ _ _ _ _ _ _ c hm
  have h1 : 1 ≤ Λ := le_trans (by norm_num) (hΛ₀.trans hΛ)
  have hterm : c.seed.level ≤ c.D.term := by
    rw [c.hseed.1, c.hterm]
    exact c.hnM.le
  obtain ⟨src⟩ := preparation_source_of_generated_seed c.request kS kI c.Mnat c.n r₀ D₀
    c.tS c.tA Ce τe (CI * c.D.eps c.m ^ min (ocDelta α q / 4) τe)
    (CI * c.D.eps (c.m - 1) ^ (q * min (ocDelta α q / 4) τe)) c.seed
    (succMenu c.Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)) Cw kI.cr σ₀ (succEta0 α q s) N p
    rfl (hcrI ▸ hcrupper) c.hseed hterm c.hcascade hprodI rfl c.hinv
  have hout := hW hr c.D c.hα c.hq c.hΛ c.hζ c.hseq c.M c.hband c.hterm c.request rfl
    (by rw [c.request_level]; exact hm) (by rw [c.request_level]; exact c.m_le_M)
    kI c.Mnat c.tA (CI * c.D.eps (c.m - 1) ^ (q * min (ocDelta α q / 4) τe))
    (by rw [c.request_level]; exact src) (c.tA_le_s₀ h1) (c.s₀_le_tf h1)
    (fun j _ => le_max_left _ _)
  rw [c.request_level] at hout
  exact hout

end AVRegularity.Construction.Preservation.CommonPreparation
end
end

section
/-! The finite order choices of the joint preparation, before envelope constants, seed
constants, stage families, masses and data. A package keeps its continuation
at exactly those orders and with duration two. It determines the early
reserve functions used by the proved original-envelope prefix.
The degenerate cases are included: H=0, empty and singleton components, smallest D=2 and
order zero, identity geometry and an edgeless seed retain the literal assumptions of the joint
preparation;
the package does not claim an envelope or construct another model. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation
open AVRegularity.Construction.Preservation.Assembly

/-- The joint preparation after the finite requests, with its duration equality
substituted. Its one tp/Pd/Pg witness still precedes every positive mass; the actual
copied family is an instance, using its produced copied envelopes directly. -/
def PreparationGateAfterOrders (α q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ) (g₀ Q : ℝ)
    (Mout H D Kmax Ks Ls Jm qJ Jchart : ℕ) : Prop :=
      ∀ (Ca Cth Cb cMol cOld COld Crat : ℝ) (Cm CG Cchart : ℕ → ℝ) (Cpad Cage : ℝ) (Npad : ℕ), 0 < cMol → 0 < cOld →
      ∃ (C CP c : ℝ) (mStar : ℕ), 0 < c ∧
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {h : ι → Type}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
        [∀ i, CompleteSpace (h i)]
        (K : ι → ℕ) (_hK : ∀ x, K x ≤ Kmax)
        (Φ : ℕ → ℝ → Vec 2 → ℝ) (_hΦ : IsOCStreamSeq α q Λ ζ Φ)
        (M' : ℕ) (κ : ℕ → ℝ) (_hband : IsOCBandChain α q Λ ζ M' κ)
        (m : ℕ) (_hm2 : 2 ≤ m) (_hmStar : mStar ≤ m) (_hmM : m ≤ M') (ν B : ℝ)
        (_hν : κ m = ν) (_hB : κ (m - 1) = B)
        (hφ : IsAdmissibleStream (Φ (m - 1)))
        (tS g a B₀ lam : ℝ) (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2)
        (_cov : CommonPreparationWindowCoverStatement α q Λ m ζ Φ hφ ν B tS 2 cMol g g₀ a B₀
          lam Cb qJ Kmax CG l₀ P y₀)
        {P' : Type} {Ctx : P' → Type} (F : ChartedFamily ι h D P' Ctx)
        (_hwmeas : ∀ p, Measurable (F.weight p))
        (_hprep : IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ
          tS (tS + 2 * ocTauPP α q Λ m) Cpad Cage Npad Jchart Cchart l₀ P F)
        (actual : ∀ p, Ctx p) (_hdepth : F.HasDepthAtMost H) (_hdesc : F.IsDescending K)
        (_htorus : IsTorusCompatible F actual (ocEpsilon q Λ (m - 1)))
        (_hcover : Set.Icc tS (tS + 2 * ocTauPP α q Λ m) ⊆ ⋃ p, (F.piece p).output)
        (_hmeas : F.IsTimeMeasurable)
        (A : Matrix ι ι ℝ) (Θ : ℝ) (_hΘ₀ : 0 ≤ Θ) (_hΘ₁ : Θ ≤ 1)
        (_htrans : F.IsTransverseOnPulses
          (fun k : {k : ℤ // Odd k} => Set.Icc (((k.1 : ℝ) - 3 / 4) * ocTau α q Λ m)
            (((k.1 : ℝ) + 3 / 4) * ocTau α q Λ m) ∩ Set.Icc tS (tS + 2 * ocTauPP α q Λ m))
          (fun k : {k : ℤ // Odd k} => if k.1 % 4 = 3 then (0 : Fin 2) else 1))
        (_hquiet : F.IsFastIndependentOn
          (ocTrimmedQuietTimes α q Λ ζ m ∩ Set.Icc tS (tS + 2 * ocTauPP α q Λ m)))
        (T : F.Atlas)
        (_hTcons : T.IsConsecutiveClosed (Set.Icc tS (tS + 2 * ocTauPP α q Λ m)))
        (_hTcov : T.CoversQuiet (ocQuietTimes α q Λ ζ m)
          (Set.Icc tS (tS + 2 * ocTauPP α q Λ m)))
        (_hTq : T.IsQuiet ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)))
        (ρold : ℝ)
        (_hρold : cOld * ocEpsilon q Λ m ^ (1 + ocGamma α q / 2 + ocDelta α q) ≤ ρold ∧
          ρold ≤ COld * ocEpsilon q Λ m ^ (1 + ocGamma α q / 2 + ocDelta α q))
        (_hρrat : ocRhoMol α q Λ m cMol ν / ρold ≤
          Crat * ocEpsilon q Λ (m - 1) ^ (-(q * ocDelta α q))),
      ∃ (tp : ℝ) (Pd : ∀ v, TorusHk 0 (h v) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v))
        (Pg : ℕ → ∀ v u, TorusHk 0 (h u) →ₗ[ℝ] TorusHk (max Mout (K v)) (h v)),
        tp ∈ Set.Ioc tS (tS + 2 * ocTauPP α q Λ m) ∧
        tS ≤ tp ∧ tp ≤ tS + 4 * ocTauPP α q Λ m ∧ tp ∈ ocQuietTimes α q Λ ζ m ∧
        Set.Icc (tp - ocTauP α q Λ m) (tp + ocTauP α q Λ m) ⊆ ocQuietTimes α q Λ ζ m ∧
        ∀ (π : ι → ℝ) (_hπ : ∀ x, 0 < π x)
          (_henv : IsEnvelope F π K
            (ChartedFamily.Domain.onWindow F (Set.Icc tS (tS + 2 * ocTauPP α q Λ m))) ν
            (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) (ocRhoMol α q Λ m cMol ν)
            (fun v u => Real.sqrt (π u / π v) * A v u) (Cth * Θ) Ca Ks Ls Cm Jm)
          (_hpointwise : IsPointwiseMolecularEnvelope F π K
            (ChartedFamily.Domain.onWindow F (Set.Icc tS (tS + 2 * ocTauPP α q Λ m))) ν
            (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) (ocRhoMol α q Λ m cMol ν)
            Cm Jm (fun v u => Real.sqrt (π u / π v) * A v u)),
          IsJointModel π K Mout H F A Θ (ocEpsilon q Λ (m - 1)) Q
            (c * Real.sqrt (B * ocTauPP α q Λ m)) C CP Pd Pg ∧
          IsJointError π K Mout H D ν tS tp (ocRhoMol α q Λ m cMol ν) ρold
            (ocEpsilon q Λ (m - 1)) Q CP (streamVel (Φ m))
            (edgeCoefficient F ν (ocEpsilon q Λ m) (ocEpsilon q Λ (m - 1)) actual K) Pd Pg


/-- Finite orders of the joint preparation together with its unchanged continuation. -/
structure PreparationGateOrderPackage (α q : ℝ) (ζ : ℝ → ℝ) (Λ : ℕ)
    (g₀ Q : ℝ) (Mout H D Kmax : ℕ) where
  Ks : ℕ
  Ls : ℕ
  Jm : ℕ
  qJ : ℕ
  Jchart : ℕ
  run : PreparationGateAfterOrders α q ζ Λ g₀ Q Mout H D Kmax Ks Ls Jm qJ Jchart

/-- The proof of the joint preparation supplies all finite packages in the
permitted early choice order; no stage or seed is selected here. -/
theorem preparation_joint_gate_packages (α s : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ → ∃ g₀ : ℝ, 0 < g₀ ∧
      ∀ Q : ℝ, 0 < Q → ∀ Mout H D Kmax : ℕ, 2 ≤ D →
        Nonempty (PreparationGateOrderPackage α q ζ Λ g₀ Q Mout H D Kmax) := by
  have hJoint : PreservationCycleJointStatement.{0, 0, 0, 0} := Providers.cycle_joint
  have hprep := cycle_joint_preparation_of_inputs hJoint
  obtain ⟨Λ₀, hΛ₀, hprep⟩ := hprep α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ
  obtain ⟨g₀, hg₀, hprep⟩ := hprep Λ hΛ
  refine ⟨g₀, hg₀, ?_⟩
  intro Q hQ Mout H D Kmax hD
  obtain ⟨Ks, Ls, Jm, qJ, Jchart, CH, _hCH, hCHtwo, hrun⟩ :=
    hprep Q hQ Mout H D Kmax hD
  subst CH
  exact ⟨⟨Ks, Ls, Jm, qJ, Jchart, hrun⟩⟩

end AVRegularity.Construction.Preservation.CommonPreparation
end
end

section
/-! Canonical finite choices for the joint preparation as functions of the EARLY numerical
request. No seed constant, producer grade offset, root space, mass or datum
occurs. The tolerance is positive at every frequency; the actual continuation of the joint
preparation is asserted only above its frequency floor and for Q>0.
The auxiliary numeric choices are total, including requests outside this
asserted domain, without claiming a model for such requests.
The degenerate cases are included: empty and singleton families, identity geometry and edgeless
data have identical choices; Dm>=4 follows from the successor schedule even for zero starting
orders.
The tail and buffer choices use the exact formulas of UniformOrders. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-- Only numerical choices preceding Ce and kS enter the finite request of the joint
preparation. -/
structure PreparationEarlyOrderRequest where
  Λ : ℕ
  Q : ℝ
  τe : ℝ
  D₀ : ℕ
  H : ℕ
  N : ℕ
  p : ℕ
  Lpr : ℕ
  Nout : ℕ

/-- The original incoming stage has the common successor-order bound. -/
def PreparationEarlyOrderRequest.dimension (E : PreparationEarlyOrderRequest) : ℕ :=
  succSchedD E.D₀ E.N E.p (E.H + 1)

/-- The finite insertion depth is independent of all seed constants. -/
def PreparationEarlyOrderRequest.depth (E : PreparationEarlyOrderRequest) (α q : ℝ) : ℕ :=
  preparationInsertionDepth (q * min (ocDelta α q / 4) E.τe) E.Q

/-- Descending copies retain the output and the actual moment reserve. -/
def PreparationEarlyOrderRequest.base (E : PreparationEarlyOrderRequest) : ℕ :=
  preparationPlainBaseOrder E.dimension E.Nout E.Lpr

/-- One higher buffered datum contains all finite copy slots. -/
def PreparationEarlyOrderRequest.buffer (E : PreparationEarlyOrderRequest) (α q : ℝ) : ℕ :=
  preparationBufferOrder E.dimension E.Nout E.Lpr (E.depth α q)

/-- The five early requests of the joint preparation, without stage data. -/
structure PreparationGateNumericOrders where
  Ks : ℕ
  Ls : ℕ
  Jm : ℕ
  qJ : ℕ
  Jchart : ℕ

private theorem preparation_early_dimension_ge_two (E : PreparationEarlyOrderRequest) :
    2 ≤ E.dimension := by
  unfold PreparationEarlyOrderRequest.dimension
  rw [succSchedD]
  omega

/-- Early order functions preserve the actual continuation of the joint preparation at every
valid request. The tolerance and orders are chosen before all seed data. -/
theorem preparation_uniform_gate_selection (α s : ℝ)
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (q : ℝ) (hq : IsAdmissibleQ α s q) (ζ : ℝ → ℝ) (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∃ g₀ : ℕ → ℝ, (∀ Λ, 0 < g₀ Λ) ∧
      ∃ orders : PreparationEarlyOrderRequest → PreparationGateNumericOrders,
      ∀ E : PreparationEarlyOrderRequest, Λ₀ ≤ E.Λ → 0 < E.Q →
        PreparationGateAfterOrders α q ζ E.Λ (g₀ E.Λ) E.Q E.Nout
          (E.depth α q) E.dimension (E.buffer α q)
          (orders E).Ks (orders E).Ls (orders E).Jm (orders E).qJ (orders E).Jchart := by
  classical
  obtain ⟨Λ₀, hΛ₀, hgate⟩ :=
    preparation_joint_gate_packages α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  have hfreq : ∀ Λ : ℕ, ∃ g : ℝ, 0 < g ∧
      (Λ₀ ≤ Λ → ∀ Q : ℝ, 0 < Q → ∀ Mout H D Kmax : ℕ, 2 ≤ D →
        Nonempty (PreparationGateOrderPackage α q ζ Λ g Q Mout H D Kmax)) := by
    intro Λ
    by_cases hΛ : Λ₀ ≤ Λ
    · obtain ⟨g, hg, hrun⟩ := hgate Λ hΛ
      exact ⟨g, hg, fun _ => hrun⟩
    · exact ⟨1, zero_lt_one, fun h => (hΛ h).elim⟩
  choose g₀ hg₀ hpackages using hfreq
  have horders : ∀ E : PreparationEarlyOrderRequest, ∃ o : PreparationGateNumericOrders,
      Λ₀ ≤ E.Λ → 0 < E.Q → PreparationGateAfterOrders α q ζ E.Λ (g₀ E.Λ) E.Q E.Nout
        (E.depth α q) E.dimension (E.buffer α q) o.Ks o.Ls o.Jm o.qJ o.Jchart := by
    intro E
    by_cases hv : Λ₀ ≤ E.Λ ∧ 0 < E.Q
    · obtain ⟨P⟩ := hpackages E.Λ hv.1 E.Q hv.2 E.Nout (E.depth α q)
        E.dimension (E.buffer α q) (preparation_early_dimension_ge_two E)
      exact ⟨⟨P.Ks, P.Ls, P.Jm, P.qJ, P.Jchart⟩, fun _ _ => P.run⟩
    · exact ⟨⟨0, 0, 0, 0, 0⟩, fun hΛ hQ => (hv ⟨hΛ, hQ⟩).elim⟩
  choose orders horders using horders
  exact ⟨Λ₀, hΛ₀, g₀, hg₀, orders, horders⟩

end AVRegularity.Construction.Preservation.CommonPreparation
end
end

section
/-! Turn the early numerical choices for the joint preparation into the literal order functions
of the common prefix. The original-stage seed reserve contains the buffer,
all requested analytic derivatives and the full molecular sampling reserve.
No function reads Ce, kS, G0, Hprod, root spaces, masses or data. A separate
frequency-floor prefix makes the selected continuation of the joint preparation available.
The degenerate cases are included: zero starting orders, every finite depth, empty and singleton
families, identity geometry, an edgeless seed and all valid positive requests use the
same formulas; the scalar prefix itself has no data-dependent floor. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.CommonPreparation

/-- Lift a numerical early request function to the full prefix.
Irrelevant template, carrier and schedule parameters are not inspected. -/
def preparationOrderFunction (f : PreparationEarlyOrderRequest → ℕ) : PrepHpr :=
  fun Λ _φ₀ _bw Q _T₀ _r₀ D₀ τe _lamE _σE H _J N p _nk _Lc _Lf Lpr _Acl
      _Naux Nout _Kres _npad _σ₀ _a _σ =>
    f { Λ := Λ, Q := Q, τe := τe, D₀ := D₀, H := H, N := N, p := p,
        Lpr := Lpr, Nout := Nout }

/-- Depth precedes all seed constants. -/
def preparationDepthFunction (α q : ℝ) : PrepHpr :=
  preparationOrderFunction (fun E => E.depth α q)

/-- The seed's molecular slots contain the buffer and the slow requests of the joint
preparation. -/
def preparationKsFunction (α q : ℝ)
    (orders : PreparationEarlyOrderRequest → PreparationGateNumericOrders) : PrepHpr :=
  preparationOrderFunction (fun E => max (E.buffer α q) (orders E).Ks)

/-- Analytic slow derivatives are exactly those requested by the joint preparation. -/
def preparationKanFunction
    (orders : PreparationEarlyOrderRequest → PreparationGateNumericOrders) : PrepHpr :=
  preparationOrderFunction (fun E => (orders E).Ks)

/-- Analytic fast derivatives are exactly those requested by the joint preparation. -/
def preparationLanFunction
    (orders : PreparationEarlyOrderRequest → PreparationGateNumericOrders) : PrepHpr :=
  preparationOrderFunction (fun E => (orders E).Ls)

/-- Sampling contains the physical order loss in addition to the jets of the joint
preparation. -/
def preparationJmFunction (α q : ℝ)
    (orders : PreparationEarlyOrderRequest → PreparationGateNumericOrders) : PrepHpr :=
  preparationOrderFunction (fun E => max (E.buffer α q + E.dimension + 2) (orders E).Jm)

/-- The frequency clause carried by the final pointwise context callback. -/
def preparationGateFloorData (Λg : ℕ) : PrepData Unit :=
  fun Λ _φ₀ _hφ₀ _bw _Q _T₀ _r₀ _D₀ _τe _lamE _σE
      _H _J _N _p _nk _Lc _Lf _Lpr _Acl _Naux _Nout _Kres _npad _σ₀ _a _σ
      _Hpr _sX _sZ _Ce _kS _kI _CI _Cw _j₀ _x => Λg ≤ Λ

/-- Carry an early frequency floor through the literal prefix, so the
actual callback has it as data. All other choices use neutral lower bounds. -/
theorem preparation_gate_frequency_prefix (α s q : ℝ) (hprf : PrepHpr) (Λg : ℕ) :
    PrepPrefix α s q hprf (preparationGateFloorData Λg) := by
  refine ⟨max 128 Λg, le_max_left _ _, ?_⟩
  intro Λ hΛ
  refine ⟨1, zero_lt_one, ?_⟩
  intro φ₀ hφ₀ _ _ _ _ bw _ _ Q T₀ _ _ r₀ D₀ τe lamE σE _ _ _
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad σ₀ a σ _ _ _
  refine ⟨0, ?_⟩
  intro sX sZ _ _ Ce kS _ _ _ _ _ _ _ _ _ _ _ _
  refine ⟨kS, 1, 1, le_rfl, zero_lt_one, ?_⟩
  intro kI _
  refine ⟨0, 0, ?_⟩
  intro CI Cw j₀ _ _
  exact ⟨(), (le_max_right _ _).trans hΛ⟩

end AVRegularity.Construction.Preservation.CommonPreparation
end
end
end
end
