-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeakAssembly.Assembly.PassageInterfaces
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
import AVRegularity.Proofs.CascadeInvariants.CopyDirNorm
import AVRegularity.Applications.Global.CompactRangeMain
public import AVRegularity.Proofs.ComplexContext.Assemble

section
@[expose] public noncomputable section
open Homogenization AVRegularity AVRegularity.Sobolev AVRegularity.WeakEntryProofs.Assembly
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen

/-! **Weak entry, generation and certificate steps: assembly**. The two leaves
`WeakStageExprStatement` (generated expressions and certified exports of the encoded weak stage)
and `WeakStageCertificateStatement` (its context certificate) of the assembly of
`entry_coefficients` follow from two statements about **one weak passage**:
* the generation step `WeakPassageGenStatement`: a passage keeps `WeakHolGen` (every coefficient is denoted by a
  scheduled expression built from the ordinary constructors alone, with no export and no solved
  node, and has a holomorphic extension to the outer carrier);
* the certificate step `WeakPassageCertStatement`: a passage keeps `WeakCertified` (the same, with the context size
  at most `C Θ̂ (R_γ/ε_i)^{n-2}`), from the reserve `1 + (i-M)/J_w` and the weight
  `L_* + (i-M)(4D_* + 4)` of the incoming level to those of the outgoing level, with the constant
  `C ↦ K_c(C)`.

Route: on the output interval of a slot the cell drift of a weak
passage is the shear of its pulse (a parallel field of the transverse phase), the molecular metric
is cell independent, and the incoming coefficients are slotwise transverse. So the two-dimensional
cell inverse acts on functions of the transverse phase only and is the
transverse inverse: no `solved` node and no export registry are needed, the export clause is
vacuous, and the holomorphic calculus is that of the carrier calculus.

The slotwise transversality of an incoming stage, which the transverse lifts need, follows from
`WeakHolGen` by generation (`GenSem.slotTransverse_of_generated`, with no export), inside each step.

Assembly (proved here): the root has no identity; the two invariants descend from the root by
induction; the encoded stage relabels the bottom stage (`WeakStageCorr`), with the record sizes
multiplied by at least `2^{2+J_wN_w} K_c^{J_w}(1)`. -/

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The registry with no export. -/
def noExports : SeedExports := fun _ => False

open scoped Classical in
/-- The component `c` of the coefficient `(γ, d, I)` of `G` is `f p` at the admissible recentered
contexts of every slot `p` on its output window, and zero off them. -/
def CoeffIs (G : GenStage D ScalarH Dm b j₀) (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) (c : Fin 2) (f : OddSlot → GenSort.Sem .ctx) : Prop :=
  ∀ (p : OddSlot) (ctx : StageCtx D b j₀ G.level p) (t : ℝ),
    t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1 → ∀ (X z : Vec 2),
    G.fam.flux p ctx v u γ d I t X z c =
      if IsAdmissibleChain D b j₀ G.level p.1 (ctx.1.recenter D (D.eps (G.level - 1) • X))
      then f p t (ctx.1.recenter D (D.eps (G.level - 1) • X)) z else 0

/-- **Holomorphically generated with no export**: every coefficient of `G` is denoted by
scheduled expressions with no export (hence no solved node) and has holomorphic extensions. -/
def WeakHolGen (G : GenStage D ScalarH Dm b j₀) : Prop :=
  ∀ v u (γ : G.fam.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1)) (c : Fin 2),
    ∃ (f : OddSlot → GenSort.Sem .ctx)
      (F : OddSlot → ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ),
      (∀ p : OddSlot, IsGeneratedCtxFrom D b j₀ noExports G.level p.1 (f p) ∧
        IsHolExtension D b j₀ G.level p.1 (f p) (F p)) ∧ CoeffIs G v u γ d I c f

/-- **The weak size certificate** at the constant `C`, the reserve `mres` and the weight `L`:
`WeakHolGen` with the context size of every coefficient at most `C Θ̂ (R_γ/ε_i)^{n-2}`, `Θ̂` the
record size, `R_γ` the record length and `n` the maximal order of the identity. -/
def WeakCertified (C mres : ℝ) (L : ℕ) (G : GenStage D ScalarH Dm b j₀) : Prop :=
  ∀ v u (γ : G.fam.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1)) (c : Fin 2),
    ∃ (f : OddSlot → GenSort.Sem .ctx)
      (F : OddSlot → ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ),
      (∀ p : OddSlot, IsGeneratedCtxFrom D b j₀ noExports G.level p.1 (f p) ∧
        IsHolExtension D b j₀ G.level p.1 (f p) (F p)) ∧ CoeffIs G v u γ d I c f ∧
      ctxSize D b j₀ G.level F mres L ≤
        ENNReal.ofReal (C * (G.fam.identity v u γ).record.size *
          ((G.fam.identity v u γ).record.length / D.eps G.level) ^
            ((G.fam.identity v u γ).maxOrder - 2))

theorem WeakCertified.weakHolGen {C mres : ℝ} {L : ℕ} {G : GenStage D ScalarH Dm b j₀}
    (h : WeakCertified C mres L G) : WeakHolGen G := fun v u γ d I c => by
  obtain ⟨f, F, hf, hc, -⟩ := h v u γ d I c
  exact ⟨f, F, hf, hc⟩

/-! ### The schedules and the statements -/

/-- The reserve of the stage `i`: `1 + (i - M)/J_w`. -/
def weakReserve {plan : WeakCoefficientPlan} (x : WeakCoefficientInstance plan) (i : ℕ) : ℝ :=
  1 + ((i - x.M : ℕ) : ℝ) / (x.physical.Jw : ℝ)

/-- The weight of the stage `i`: `L_* + (i - M)(4D_* + 4)`, `D_* = 1 + J_wN_w`. -/
def weakWeight {plan : WeakCoefficientPlan} (x : WeakCoefficientInstance plan) (i : ℕ) : ℕ :=
  (plan.constants x.request).kW.Lstar +
    (i - x.M) * (4 * (1 + x.physical.Jw * x.physical.Nw) + 4)

/-- A constant map of one passage, chosen with the requests. -/
abbrev WeakConstFn : Type :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}, WeakCoefficientRequest A → ℝ → ℝ

/-- **Generation**: one weak passage keeps holomorphic generation with no export. -/
def WeakPassageGenStatement (plan : WeakCoefficientPlan) : Prop :=
  ∀ (c : WeakCoefficientCase plan) (i : ℕ), c.inst.M < i → i ≤ c.inst.M + c.inst.physical.Jw →
    WeakHolGen (c.stage i) → WeakHolGen (c.stage (i - 1))

/-- **Certificate**: one weak passage keeps the weak size certificate, with the constant map `Kc`. -/
def WeakPassageCertStatement (plan : WeakCoefficientPlan) (Kc : WeakConstFn) : Prop :=
  ∀ (c : WeakCoefficientCase plan) (i : ℕ), c.inst.M < i → i ≤ c.inst.M + c.inst.physical.Jw →
    ∀ C : ℝ, 0 ≤ C → WeakCertified C (weakReserve c.inst i) (weakWeight c.inst i) (c.stage i) →
      0 ≤ Kc c.inst.request C ∧
        WeakCertified (Kc c.inst.request C) (weakReserve c.inst (i - 1)) (weakWeight c.inst (i - 1))
          (c.stage (i - 1))

/-! ### One passage of a partial construction -/

/-- A partial weak construction down to the level `i`: the root at `M + J_w` and the weak passages
of the levels in `(i, M + J_w]`, with the tags of their outputs. -/
def IsPartialWeakConstruction {plan : WeakCoefficientPlan} (x : WeakCoefficientInstance plan)
    (i : ℕ) (stage : ℕ → GenStage x.D ScalarH x.Dm x.physical.bw x.j₀) : Prop :=
  IsWeakRoot (x.M + x.physical.Jw) 0 (stage (x.M + x.physical.Jw)) ∧
    ∀ i', i < i' → i' ≤ x.M + x.physical.Jw →
      IsWeakPassage x.D x.P x.menu (x.D.termRW x.physical.σw x.M)
          (1 + (x.M + x.physical.Jw - i') * x.menu.N) (stage i') (stage (i' - 1)) ∧
        (stage (i' - 1)).HasTags x.P

/-- **One passage of a partial construction**: the passage from the level `i > M` to `i - 1`. -/
structure WeakPassageAt (plan : WeakCoefficientPlan) where
  inst : WeakCoefficientInstance plan
  i : ℕ
  hi : inst.M < i
  hiJ : i ≤ inst.M + inst.physical.Jw
  stage : ℕ → GenStage inst.D ScalarH inst.Dm inst.physical.bw inst.j₀
  pc : IsPartialWeakConstruction inst (i - 1) stage

/-- A construction is a partial construction down to every level `≥ M`. -/
theorem isPartialWeakConstruction_of_case {plan : WeakCoefficientPlan}
    (c : WeakCoefficientCase plan) {i : ℕ} (hi : c.inst.M ≤ i) :
    IsPartialWeakConstruction c.inst i c.stage :=
  ⟨c.construction.2.1, fun i' hi' hi'J => c.construction.2.2 i' (by omega) hi'J⟩

/-- The passage of a construction from the level `i`. -/
def _root_.AVRegularity.WeakEntryProofs.Assembly.WeakCoefficientCase.passageAt {plan : WeakCoefficientPlan} (c : WeakCoefficientCase plan)
    (i : ℕ) (hi : c.inst.M < i) (hiJ : i ≤ c.inst.M + c.inst.physical.Jw) : WeakPassageAt plan :=
  ⟨c.inst, i, hi, hiJ, c.stage, isPartialWeakConstruction_of_case c (by omega)⟩

/-- The stages of a partial construction have their levels. -/
theorem IsPartialWeakConstruction.level {plan : WeakCoefficientPlan}
    {x : WeakCoefficientInstance plan} {i : ℕ}
    {stage : ℕ → GenStage x.D ScalarH x.Dm x.physical.bw x.j₀}
    (h : IsPartialWeakConstruction x i stage) :
    ∀ j, i ≤ j → j ≤ x.M + x.physical.Jw → (stage j).level = j := by
  have main : ∀ n, n ≤ x.M + x.physical.Jw - i →
      (stage (x.M + x.physical.Jw - n)).level = x.M + x.physical.Jw - n := by
    intro n
    induction n with
    | zero => intro _; simpa using h.1.1
    | succ n ih =>
      intro hn
      have hp := (h.2 (x.M + x.physical.Jw - n) (by omega) (by omega)).1
      rw [show x.M + x.physical.Jw - (n + 1) = x.M + x.physical.Jw - n - 1 by omega, hp.2.1,
        ih (by omega)]
  intro j hj hjJ
  have := main (x.M + x.physical.Jw - j) (by omega)
  rwa [show x.M + x.physical.Jw - (x.M + x.physical.Jw - j) = j by omega] at this

/-- **The certificate, one passage**: a passage of a partial construction keeps the weak size certificate. -/
def WeakPassageCert1Statement (plan : WeakCoefficientPlan) (Kc : WeakConstFn) : Prop :=
  ∀ (x : WeakPassageAt plan) (C : ℝ), 0 ≤ C →
    WeakCertified C (weakReserve x.inst x.i) (weakWeight x.inst x.i) (x.stage x.i) →
    0 ≤ Kc x.inst.request C ∧
      WeakCertified (Kc x.inst.request C) (weakReserve x.inst (x.i - 1))
        (weakWeight x.inst (x.i - 1)) (x.stage (x.i - 1))

/-- The one-passage statement gives the statement along every construction. -/
theorem weakPassageCert_of_one {plan : WeakCoefficientPlan} {Kc : WeakConstFn}
    (h : WeakPassageCert1Statement plan Kc) : WeakPassageCertStatement plan Kc :=
  fun c i hi hiJ C hC hW => h (c.passageAt i hi hiJ) C hC hW

/-- `Gw` relabels `G`: the same level, bijections of the components and of the identities that
keep the record lengths, the maximal orders and the fluxes, and multiply the record sizes by at
least `K`. -/
def WeakStageCorr (G Gw : GenStage D ScalarH Dm b j₀) (K : ℝ) : Prop :=
  Gw.level = G.level ∧
    ∃ (ι : CompIn G.comps ≃ CompIn Gw.comps) (e : ∀ v u, G.fam.Γ v u ≃ Gw.fam.Γ (ι v) (ι u)),
      ∀ v u (γ : G.fam.Γ v u),
        K * (G.fam.identity v u γ).record.size ≤
            (Gw.fam.identity (ι v) (ι u) (e v u γ)).record.size ∧
          (Gw.fam.identity (ι v) (ι u) (e v u γ)).record.length =
            (G.fam.identity v u γ).record.length ∧
          (Gw.fam.identity (ι v) (ι u) (e v u γ)).maxOrder = (G.fam.identity v u γ).maxOrder ∧
          ∀ (p : OddSlot) (c : StageCtx D b j₀ Gw.level p) (c' : StageCtx D b j₀ G.level p),
            c.1 = c'.1 → ∀ (d : ℕ) (I : DerivativeWord2 (d - 1)) (t : ℝ) (X z : Vec 2),
              Gw.fam.flux p c (ι v) (ι u) (e v u γ) d I t X z = G.fam.flux p c' v u γ d I t X z

/-- An encoding is a relabeling with the factor `1`. -/
theorem WeakStageCorr.of_encoding {N J : ℕ} {η₀ : ℝ} {rootM rootR : ℕ → ℝ}
    {G Gw : GenStage D ScalarH Dm b j₀} {ι : CompIn G.comps ≃ CompIn Gw.comps}
    (henc : IsWeakEncoding N J η₀ rootM rootR G Gw ι) : WeakStageCorr G Gw 1 := by
  obtain ⟨hlev, -, -, -, -, -, Cθ, e, _, hCθ, -, hall⟩ := henc
  refine ⟨hlev, ι, e, fun v u γ => ?_⟩
  obtain ⟨-, -, hsize, -, -, hlen, -, -, hord, hflux⟩ := hall v u γ
  refine ⟨?_, hlen, hord, hflux⟩
  rw [hsize, one_mul]
  exact le_mul_of_one_le_left (G.fam.identity v u γ).record.size_nonneg hCθ

/-- The certificate factor of the encoded stage: `2^{2+J_wN_w} K_c^{J_w}(1)`. -/
def weakCertFactor {plan : WeakCoefficientPlan} (Kc : WeakConstFn) (c : WeakCoefficientCase plan) :
    ℝ :=
  2 ^ (2 + c.inst.physical.Jw * c.inst.physical.Nw) * (Kc c.inst.request)^[c.inst.physical.Jw] 1

/-! ### The root and the descent -/

section Descent

variable {plan : WeakCoefficientPlan} (c : WeakCoefficientCase plan)

theorem root_isEmpty (v u : CompIn (c.stage (c.inst.M + c.inst.physical.Jw)).comps) :
    IsEmpty ((c.stage (c.inst.M + c.inst.physical.Jw)).fam.Γ v u) :=
  c.construction.2.1.2.2.1 v u

theorem weakCertified_root (C mres : ℝ) (L : ℕ) :
    WeakCertified C mres L (c.stage (c.inst.M + c.inst.physical.Jw)) :=
  fun v u γ => ((root_isEmpty c v u).false γ).elim

theorem weakHolGen_root : WeakHolGen (c.stage (c.inst.M + c.inst.physical.Jw)) :=
  (weakCertified_root c 0 0 0).weakHolGen

/-- **Holomorphic generation descends from the root**. -/
theorem weakHolGen_stage (hgen : WeakPassageGenStatement plan) :
    ∀ k ≤ c.inst.physical.Jw, WeakHolGen (c.stage (c.inst.M + c.inst.physical.Jw - k)) := by
  intro k hk
  induction k with
  | zero => simpa using weakHolGen_root c
  | succ k ih =>
    have h := hgen c (c.inst.M + c.inst.physical.Jw - k) (by omega) (by omega) (ih (by omega))
    rwa [show c.inst.M + c.inst.physical.Jw - k - 1 = c.inst.M + c.inst.physical.Jw - (k + 1)
      by omega] at h

/-- **The weak size certificate descends from the root**, with the constants `K_c^k(1)`. -/
theorem weakCertified_stage {Kc : WeakConstFn} (hcert : WeakPassageCertStatement plan Kc) :
    ∀ k ≤ c.inst.physical.Jw, 0 ≤ (Kc c.inst.request)^[k] 1 ∧
      WeakCertified ((Kc c.inst.request)^[k] 1)
        (weakReserve c.inst (c.inst.M + c.inst.physical.Jw - k))
        (weakWeight c.inst (c.inst.M + c.inst.physical.Jw - k))
        (c.stage (c.inst.M + c.inst.physical.Jw - k)) := by
  intro k hk
  induction k with
  | zero => exact ⟨zero_le_one, by simpa using weakCertified_root c _ _ _⟩
  | succ k ih =>
    obtain ⟨hC, hW⟩ := ih (by omega)
    have h := hcert c (c.inst.M + c.inst.physical.Jw - k) (by omega) (by omega) _ hC hW
    rw [show c.inst.M + c.inst.physical.Jw - k - 1 = c.inst.M + c.inst.physical.Jw - (k + 1)
      by omega] at h
    rw [Function.iterate_succ_apply']
    exact h

end Descent

/-! ### Transfer to the encoded stage -/

section Transfer

variable {G Gw : GenStage D ScalarH Dm b j₀} {K : ℝ}

open scoped Classical in
/-- The coefficients of a relabeled stage are those of the stage. -/
theorem WeakStageCorr.coeffIs (hcorr : WeakStageCorr G Gw K) :
    ∀ v' u' (γ' : Gw.fam.Γ v' u'), ∃ (v u : CompIn G.comps) (γ : G.fam.Γ v u),
      (Gw.fam.identity v' u' γ').record.length = (G.fam.identity v u γ).record.length ∧
      (Gw.fam.identity v' u' γ').maxOrder = (G.fam.identity v u γ).maxOrder ∧
      K * (G.fam.identity v u γ).record.size ≤ (Gw.fam.identity v' u' γ').record.size ∧
      ∀ (d : ℕ) (I : DerivativeWord2 (d - 1)) (c : Fin 2) (f : OddSlot → GenSort.Sem .ctx),
        CoeffIs G v u γ d I c f → CoeffIs Gw v' u' γ' d I c f := by
  obtain ⟨hlev, ι, e, hall⟩ := hcorr
  intro v' u' γ'
  obtain ⟨v, rfl⟩ := ι.surjective v'
  obtain ⟨u, rfl⟩ := ι.surjective u'
  obtain ⟨γ, rfl⟩ := (e v u).surjective γ'
  obtain ⟨hsize, hlen, hord, hflux⟩ := hall v u γ
  refine ⟨v, u, γ, hlen, hord, hsize, fun d I c f hf p ctx t ht X z => ?_⟩
  have hadm : IsAdmissibleChain D b j₀ G.level p.1 ctx.1 := hlev ▸ ctx.2
  rw [hflux p ctx ⟨ctx.1, hadm⟩ rfl d I t X z, hf p ⟨ctx.1, hadm⟩ t (hlev ▸ ht) X z]
  simp only [hlev]

end Transfer

/-! ### The two leaves of the assembly -/

/-- Seed provenance with no export gives seed provenance for every registry. -/
theorem isGeneratedCtxFrom_of_noExports {𝒮 : SeedExports} {i : ℕ} {p : ℤ}
    {f : GenSort.Sem .ctx} (h : IsGeneratedCtxFrom D b j₀ noExports i p f) :
    IsGeneratedCtxFrom D b j₀ 𝒮 i p f := by
  obtain ⟨e, hsch, hfs, hden⟩ := h
  exact ⟨e, hsch, GenSem.fromSeed_mono (fun _ h => (h : False).elim) hfs, hden⟩

/-- The context size grows with the reserve. -/
theorem ctxSize_mono_reserve (hb : 0 ≤ b) (hε : ∀ k, 0 ≤ D.eps k) {i : ℕ}
    {F : OddSlot → ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ} {mres mres' : ℝ}
    (hm : mres ≤ mres') (L : ℕ) :
    ctxSize D b j₀ i F mres L ≤ ctxSize D b j₀ i F mres' L :=
  ENNReal.tsum_le_tsum fun h => mul_le_mul' le_rfl
    (iSup_mono fun p => CascadeInvariants.ctxModeSup_mono D hb hε j₀ i p.1 (F p) hm h)

/-- The algebra of the witness inequality: with `0 < ρ ≤ 1` and `2 ≤ d ≤ n ≤ N`,
`ρ^{-(d-2)} 2^d C s ρ^{n-2} ≤ 2^N C s`. -/
theorem witness_algebra {ρ C s : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hC : 0 ≤ C) (hs : 0 ≤ s)
    {d n N : ℕ} (hd : 2 ≤ d) (hdn : d ≤ n) (hnN : n ≤ N) :
    ρ⁻¹ ^ (d - 2) * (2 ^ d * (C * s * ρ ^ (n - 2))) ≤ 2 ^ N * C * s := by
  have hsplit : ρ ^ (n - 2) = ρ ^ (d - 2) * ρ ^ (n - d) := by
    rw [← pow_add]; congr 1; omega
  have hcancel : ρ⁻¹ ^ (d - 2) * ρ ^ (d - 2) = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hρ0.ne', one_pow]
  have hrest : ρ ^ (n - d) ≤ 1 := pow_le_one₀ hρ0.le hρ1
  have h2 : (2 : ℝ) ^ d ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) (hdn.trans hnN)
  calc ρ⁻¹ ^ (d - 2) * (2 ^ d * (C * s * ρ ^ (n - 2)))
      = 2 ^ d * C * s * ρ ^ (n - d) * (ρ⁻¹ ^ (d - 2) * ρ ^ (d - 2)) := by rw [hsplit]; ring
    _ = 2 ^ d * C * s * ρ ^ (n - d) := by rw [hcancel, mul_one]
    _ ≤ 2 ^ d * C * s * 1 := by gcongr
    _ ≤ 2 ^ N * C * s := by rw [mul_one]; gcongr

variable {plan : WeakCoefficientPlan}

/-- The scales of an instance: `0 < ε_k`, and `ε_{M+1} ≤ ε_M`. -/
theorem case_eps_pos (x : WeakCoefficientInstance plan) (k : ℕ) : 0 < x.D.eps k := by
  have hq : 1 < x.D.q := by rw [x.hq]; exact x.base.hq.1
  have hΛ : 128 ≤ x.D.Λ := by
    rw [x.hΛ]; exact (plan.baseThreshold_ge _).trans x.base_large
  exact Applications.eps_pos hq hΛ

theorem case_eps_succ_le (x : WeakCoefficientInstance plan) :
    x.D.eps (x.M + 1) ≤ x.D.eps x.M := by
  have hq : 1 < x.D.q := by rw [x.hq]; exact x.base.hq.1
  have hΛ : 128 ≤ x.D.Λ := by
    rw [x.hΛ]; exact (plan.baseThreshold_ge _).trans x.base_large
  exact Applications.eps_antitone hq hΛ (Nat.le_succ _)

/-- **The generation leaf of the assembly** (`WeakStageExprStatement`) from the generation step, for an encoding with no
export. -/
theorem weakStageExpr_of_ingredients (encode : WeakCoefficientEncodingChoice plan)
    (hgen : WeakPassageGenStatement plan)
    (hI4 : WeakEncodingTransportStatement plan encode)
    (hexp : ∀ (c : WeakCoefficientCase plan) (i : ℕ) (p : ℤ) (e : Gen .ctx i p),
      ¬ (encode c).stage.exports e) :
    WeakStageExprStatement plan encode := by
  intro c
  have hG := weakHolGen_stage c hgen c.inst.physical.Jw le_rfl
  rw [Nat.add_sub_cancel] at hG
  have hcorr := WeakStageCorr.of_encoding (hI4 c).1
  refine ⟨fun p v' u' γ' d I k => ?_, fun i p e he => (hexp c i p e he).elim,
    fun {i} {p} e he => (hexp c i p e he).elim⟩
  obtain ⟨v, u, γ, -, -, -, hco⟩ := hcorr.coeffIs v' u' γ'
  obtain ⟨f, F, hf, hc⟩ := hG v u γ d I k
  refine ⟨f p, ?_, hco d I k f hc p⟩
  rw [hcorr.1]
  exact isGeneratedCtxFrom_of_noExports (hf p).1

/-- **The certificate leaf of the assembly** (`WeakStageCertificateStatement`) from the certificate step, for an encoding that
relabels the bottom stage with the factor `weakCertFactor Kc`. -/
theorem weakStageCertificate_of_ingredients (encode : WeakCoefficientEncodingChoice plan)
    (Kc : WeakConstFn) (hcert : WeakPassageCertStatement plan Kc)
    (hcorr : ∀ c : WeakCoefficientCase plan,
      WeakStageCorr (c.stage c.inst.M) (encode c).stage (weakCertFactor Kc c)) :
    WeakStageCertificateStatement plan encode := by
  intro c
  obtain ⟨hC0, hW⟩ := weakCertified_stage c hcert c.inst.physical.Jw le_rfl
  rw [Nat.add_sub_cancel] at hW
  have hres : weakReserve c.inst c.inst.M = 1 := by simp [weakReserve]
  have hwt : weakWeight c.inst c.inst.M = (plan.constants c.inst.request).kW.Lstar := by
    simp [weakWeight]
  rw [hres, hwt] at hW
  have hlevM : (c.stage c.inst.M).level = c.inst.M :=
    EntryWeakProofs.weakConstruction_level c.inst.P c.inst.menu c.inst.M c.inst.physical.Jw 0
      _ c.stage c.construction c.inst.M le_rfl (by omega)
  have hb : 0 ≤ c.inst.physical.bw := c.inst.physical.bw_pos.le
  have hε : ∀ k, 0 ≤ c.inst.D.eps k := fun k => (case_eps_pos c.inst k).le
  obtain ⟨hlevw, -⟩ := hcorr c
  intro v' u' γ'
  obtain ⟨v, u, γ, hlen, hord, hsize, hco⟩ := (hcorr c).coeffIs v' u' γ'
  set Cm := (Kc c.inst.request)^[c.inst.physical.Jw] 1 with hCm
  have hlenM : ((c.stage c.inst.M).fam.identity v u γ).record.length = c.inst.D.eps (c.inst.M + 1) :=
    (WeakEntryProofs.weakConstruction_output_records c.inst.P c.inst.menu c.inst.M
      c.inst.physical.Jw 0 _ c.stage c.construction c.inst.physical.Jw_pos v u γ).1
  have hordM : ((c.stage c.inst.M).fam.identity v u γ).maxOrder ≤ 1 + c.inst.physical.Jw * c.inst.physical.Nw :=
    EntryWeakProofs.weakConstruction_output_maxOrder_bound c.inst.P c.inst.menu c.inst.M
      c.inst.physical.Jw _ 0 c.stage c.construction c.inst.M le_rfl
      (by have := c.inst.physical.Jw_pos; omega) v u γ
  set ρ := ((c.stage c.inst.M).fam.identity v u γ).record.length / c.inst.D.eps (c.stage c.inst.M).level with hρ
  have hρ0 : 0 < ρ := div_pos ((c.stage c.inst.M).fam.identity v u γ).record.length_pos (case_eps_pos c.inst _)
  have hρ1 : ρ ≤ 1 := by
    rw [hρ, hlenM, hlevM, div_le_one (case_eps_pos c.inst _)]
    exact case_eps_succ_le c.inst
  set θ₀ := Cm * ((c.stage c.inst.M).fam.identity v u γ).record.size * ρ ^ (((c.stage c.inst.M).fam.identity v u γ).maxOrder - 2)
    with hθ₀
  have hθ₀0 : 0 ≤ θ₀ :=
    mul_nonneg (mul_nonneg hC0 ((c.stage c.inst.M).fam.identity v u γ).record.size_nonneg) (pow_nonneg hρ0.le _)
  refine ⟨fun _ _ _ => θ₀, fun _ _ _ => hθ₀0, fun d hd hdn => ?_, fun d α k => ?_⟩
  · -- the witness inequality
    rw [hord] at hdn
    have hsum : ∑ _α : DerivativeWord2 (d - 1), ∑ _k : Fin 2, θ₀ = 2 ^ d * θ₀ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        DerivativeWord2, DerivativeWord, Fintype.card_fun]
      push_cast
      rw [← mul_assoc, ← pow_succ]
      congr 2
      omega
    have hratio : c.inst.D.eps (encode c).stage.level /
        ((encode c).stage.fam.identity v' u' γ').record.length = ρ⁻¹ := by
      rw [hρ, hlen, hlevw, inv_div]
    rw [hsum, hratio]
    calc ρ⁻¹ ^ (d - 2) * (2 ^ d * θ₀)
        ≤ 2 ^ (2 + c.inst.physical.Jw * c.inst.physical.Nw) * Cm *
            ((c.stage c.inst.M).fam.identity v u γ).record.size :=
          witness_algebra hρ0 hρ1 hC0 ((c.stage c.inst.M).fam.identity v u γ).record.size_nonneg hd hdn
            (by omega)
      _ = weakCertFactor Kc c * ((c.stage c.inst.M).fam.identity v u γ).record.size := by
          rw [weakCertFactor, hCm]
      _ ≤ ((encode c).stage.fam.identity v' u' γ').record.size := hsize
  · -- the extensions
    obtain ⟨f, F, hf, hc, hsz⟩ := hW v u γ d α k
    refine ⟨f, F, fun p => ⟨?_, ?_, hco d α k f hc p⟩, ?_⟩
    · rw [hlevw]; exact isGeneratedCtxFrom_of_noExports (hf p).1
    · rw [hlevw]; exact (hf p).2
    · rw [hlevw]
      have hμ : compReserve (plan.constants c.inst.request).kW v'.1 ≤ 1 := by
        unfold compReserve
        have : (0 : ℝ) ≤ (((plan.constants c.inst.request).kW.G0 + compGrade v'.1 : ℕ) : ℝ) /
            (((plan.constants c.inst.request).kW.Hprod : ℝ) + 1) := by positivity
        linarith
      exact (ctxSize_mono_reserve hb hε hμ _).trans hsz

end AVRegularity.Providers.WeakGen
end
end

section
section
/-! **Weak entry, certificate sub-assembly**. One weak passage keeps the weak size
certificate (`WeakPassageCertStatement`) once two statements hold:
* the **weak ledger** `WeakPassageLedgerStatement` of the passage `i → i - 1`. From the
  certificate of the incoming stage, it produces for every coefficient of the outgoing stage
  scheduled expressions with no export, with the incoming coefficients as certified leaves and
  with drift letters only at levels `≥ i` (`ComplexContext.DriftIn`). Their weighted sum of
  majorants (`genMode`, with the letter profiles `weakKappa c i`, drift profile
  `π · ε_i^{1+α}/√(κ_iκ_{i-1})`, the Péclet number of the passage) is at most
  `K_c(C) Θ̂ (R_γ/ε_{i-1})^{n-2}`. Its parts are the eddy letters (two Péclet factors), the
  inherited path means (the product of the incoming witnesses, the path-mean ledger), and the
  transfer;
* **the carrier calculus with the drift constant of one level** `WeakLevelComplexContextStatement`: such a ledger is
  a certificate. The induction of the carrier calculus asks the drift bound only at the levels of the drift letters
  (`ComplexContext.genInv_of_denotes` with the level predicate `i ≤ ·`); at the weak levels `≥ i` the
  diffusivity is the terminal one and the wavelengths decrease, so the Péclet number of the level
  `i` bounds them all.
The assembly is the composition, with the reserve `1 + (i - 1 - M)/J_w ∈ [1, 2]` of the outgoing
stage. Everything is stated for one passage of a partial construction (`WeakPassageAt`), so that
the existence of the construction and the certificates can be proved by one induction over the
passages. -/

@[expose] public noncomputable section

open Homogenization AVRegularity AVRegularity.Sobolev AVRegularity.WeakEntryProofs.Assembly
open scoped ENNReal

namespace AVRegularity.Providers.WeakGen

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

variable {plan : WeakCoefficientPlan}

/-- The drift constant of the passage at the level `i`: `ε_i^{1+α}/√(κ_iκ_{i-1})` (the Péclet
number `Pe_i` at a weak level, `κ_i = κ_{i-1} = κ_M`). -/
def weakCd (x : WeakCoefficientInstance plan) (i : ℕ) : ℝ :=
  x.D.eps i ^ (1 + x.D.α) / Real.sqrt (x.D.kap i * x.D.kap (i - 1))

/-- The letter profiles of the passage at the level `i`: those of the carrier calculus, with the drift constant of
the level. -/
def weakKappa (x : WeakCoefficientInstance plan) (i : ℕ) : MajConsts :=
  ComplexContext.complexContextKappa x.physical.bw (weakCd x i)

/-- **One entry of the weak ledger**: the identity `γ` of the outgoing stage `G'` of the passage at
the level `i`, at the constant `C`, the reserve `mres` and the weight `L`. Every coefficient of `γ`
has scheduled expressions with no export, certified leaves, no uncertified solved node and drift
letters only at levels `≥ i`. The weighted sum of their majorants, with the profiles
`weakKappa c i`, is at most `C Θ̂ (R_γ/ε_{i-1})^{n-2}`. -/
def WeakLedgerEntry (x : WeakPassageAt plan) (C mres : ℝ) (L : ℕ)
    (v u : CompIn (x.stage (x.i - 1)).comps) (γ : (x.stage (x.i - 1)).fam.Γ v u) : Prop :=
  ∀ (d : ℕ) (I : DerivativeWord2 (d - 1)) (k : Fin 2),
    ∃ (e : (p : OddSlot) → Gen .ctx (x.stage (x.i - 1)).level p.1) (Δ : ℝ)
      (leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞)),
      (∀ p : OddSlot, Gen.IsScheduled x.inst.D (e p) ∧ Gen.FromSeed noExports (e p)) ∧
      (∃ f : OddSlot → GenSort.Sem .ctx,
        (∀ p : OddSlot, Gen.Denotes x.inst.D x.inst.physical.bw x.inst.j₀ (e p) (f p)) ∧
          CoeffIs (x.stage (x.i - 1)) v u γ d I k f) ∧
      0 < Δ ∧ LeavesCertified x.inst.D x.inst.physical.bw x.inst.j₀ leaf ∧
      (∀ p : OddSlot, Gen.SolvedFree leaf (e p)) ∧ (∀ p : OddSlot, ComplexContext.DriftIn leaf (x.i ≤ ·) (e p)) ∧
      ∑' h : ℤ, ENNReal.ofReal (Real.exp (3 * Real.pi * x.inst.physical.bw * |(h : ℝ)|) *
          (1 + |(h : ℝ)|) ^ L) *
        ⨆ p : OddSlot, ⨆ t ∈ ocPulseWindow x.inst.D.α x.inst.D.q x.inst.D.Λ (x.stage (x.i - 1)).level p.1,
          genMode x.inst.D (weakKappa x.inst x.i) Δ leaf (e p) mres h t
        ≤ ENNReal.ofReal (C * ((x.stage (x.i - 1)).fam.identity v u γ).record.size *
          (((x.stage (x.i - 1)).fam.identity v u γ).record.length / x.inst.D.eps (x.stage (x.i - 1)).level) ^
            (((x.stage (x.i - 1)).fam.identity v u γ).maxOrder - 2))

/-- **The weak ledger** of the outgoing stage `G'`: every identity has its entry. -/
def WeakLedgerAt (x : WeakPassageAt plan) (C mres : ℝ) (L : ℕ) : Prop :=
  ∀ v u (γ : (x.stage (x.i - 1)).fam.Γ v u), WeakLedgerEntry x C mres L v u γ

/-- **The carrier calculus with the drift constant of one level.** At a passage of the construction, a
weak ledger of the outgoing stage at a reserve in `[0, 2]` is a weak size certificate. -/
def WeakLevelComplexContextStatement (plan : WeakCoefficientPlan) : Prop :=
  ∀ (x : WeakPassageAt plan) (C mres : ℝ) (L : ℕ), 0 ≤ mres → mres ≤ 2 →
    WeakLedgerAt x C mres L → WeakCertified C mres L (x.stage (x.i - 1))

/-- **The weak ledger of one passage**, with the constant map `Kc`. -/
def WeakPassageLedgerStatement (plan : WeakCoefficientPlan) (Kc : WeakConstFn) : Prop :=
  ∀ (x : WeakPassageAt plan) (C : ℝ), 0 ≤ C →
    WeakCertified C (weakReserve x.inst x.i) (weakWeight x.inst x.i) (x.stage x.i) →
      0 ≤ Kc x.inst.request C ∧
        WeakLedgerAt x (Kc x.inst.request C) (weakReserve x.inst (x.i - 1))
          (weakWeight x.inst (x.i - 1))

/-- The reserve of a stage of the construction lies in `[1, 2]`. -/
theorem weakReserve_mem (x : WeakCoefficientInstance plan) {i : ℕ}
    (hi : i ≤ x.M + x.physical.Jw) :
    1 ≤ weakReserve x i ∧ weakReserve x i ≤ 2 := by
  have hJ : (0 : ℝ) < x.physical.Jw := by exact_mod_cast x.physical.Jw_pos
  have hle : ((i - x.M : ℕ) : ℝ) ≤ x.physical.Jw := by exact_mod_cast (by omega)
  have h0 : (0 : ℝ) ≤ ((i - x.M : ℕ) : ℝ) / x.physical.Jw := by positivity
  have h1 : ((i - x.M : ℕ) : ℝ) / x.physical.Jw ≤ 1 := (div_le_one hJ).mpr hle
  unfold weakReserve
  constructor <;> linarith

/-- **The certificate from the carrier-calculus step and the weak ledger.** -/
theorem weakPassageCert_of_ingredients (Kc : WeakConstFn) (h6a : WeakLevelComplexContextStatement plan)
    (h6b : WeakPassageLedgerStatement plan Kc) : WeakPassageCert1Statement plan Kc := by
  intro x C hC hW
  obtain ⟨hK, hL⟩ := h6b x C hC hW
  have hr := weakReserve_mem x.inst (i := x.i - 1) (by have := x.hiJ; omega)
  exact ⟨hK, h6a x _ _ _ (by linarith [hr.1]) hr.2 hL⟩

end AVRegularity.Providers.WeakGen
end
end

section
/-! **Weak entry, ledger sub-assembly**. The weak ledger of one passage
(`WeakPassageLedgerStatement`) follows from its two kinds of entries, read through the data of the
passage (`WeakPassageWitness`: the bijection of the identities with the valid sources, the indices,
and the lifts):
* the inherited ledger `WeakInheritedLedgerStatement`: the entries of the identities with an inherited source,
  that is the path means of the incoming stage. These go through the path-mean ledger over
  the certified incoming coefficients (`GenStage.OldCert`), with the weak scales `d_* = ε_i`,
  `ρ = ε_{i-1}` and the product of the incoming witnesses;
* the eddy ledger `WeakEddyLedgerStatement`: the entries of the identities with an eddy source, that is
  the mean of the drift against a grade-zero lift. They carry two Péclet factors, one from the
  drift letter and one from the lift: the drift-free part of a grade-zero lift of positive degree
  is cell independent and is removed by the centering.
Both use lifts of a high reserve, which agree with the lifts of the passage on the windows and on
the grades the fluxes read (`WeakHighReserveLiftsStatement`). The
constant map of the ledger is the larger of the two. All statements are for one passage of a
partial construction (`WeakPassageAt`). -/

@[expose] public noncomputable section

open Homogenization AVRegularity AVRegularity.Sobolev AVRegularity.WeakEntryProofs.Assembly
open scoped ENNReal

namespace AVRegularity.Providers.WeakGen

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- An inherited source. -/
def _root_.AVRegularity.WeakSource.IsInherited {hr : ℕ → Type}
    [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
    {G : GenStage D hr Dm b j₀} : WeakSource G → Prop
  | .inherited .. => True
  | .eddy .. => False

open scoped Classical in
/-- **The data of a weak passage** `G → G'` (the existential part of `IsWeakPassage`). -/
structure WeakPassageWitness (P : ProvParams) (Mn : WeakMenu) (rW : ℝ) (Din : ℕ)
    (G G' : GenStage D ScalarH Dm b j₀) where
  e : ∀ v' u', G'.fam.Γ v' u' ≃ {s : WeakSource G //
    s.Valid Mn.N Mn.R Din ∧ s.srcComp G.level = u'.1 ∧ s.tgtComp G.level = v'.1}
  idx : ∀ v' u', G'.fam.Γ v' u' → ℕ
  Cc : ∀ s : WeakSource G, ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ)
  Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)
  lifts : ∀ s : WeakSource G, s.IsLiftFamily Mn.sX Mn.sZ Mn.N (D.eps (G.level - 1)) (Cc s)
  lifts0 : ∀ (k : ℤ) (A : RealChain), Odd k → IsAdmissibleChain D b j₀ G.level k A →
    IsLiftSequence (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D G.level k A
        (D.eps (G.level - 1)) (fun _ _ _ => []))
      Mn.sX Mn.sZ (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) Mn.N 0
      (Cc0 k A)
  idx_inj : ∀ v' u' (γ' : G'.fam.Γ v' u') v'' u'' (γ'' : G'.fam.Γ v'' u''),
    idx v' u' γ' = idx v'' u'' γ'' → v' = v'' ∧ u' = u'' ∧ HEq γ' γ''
  prov : ∀ v' u' (γ' : G'.fam.Γ v' u'),
    G'.prov v' u' γ' = .seed (idx v' u' γ') ((e v' u' γ').1.weakTag P G.level rW Mn.η0)
  map : ∀ v' u' (γ' : G'.fam.Γ v' u'),
    (G'.fam.identity v' u' γ').map = rootPathMap ScalarH u'.1.root [] v'.1.root
  flux : ∀ v' u' (γ' : G'.fam.Γ v' u') (p : OddSlot) (c : StageCtx D b j₀ G'.level p) (d : ℕ)
    (I : DerivativeWord2 (d - 1)) (t : ℝ) (X z : Vec 2), 2 ≤ d →
    G'.fam.flux p c v' u' γ' d I t X z =
      if IsAdmissibleChain D b j₀ G'.level p.1 (c.1.recenter D (D.eps (G'.level - 1) • X))
      then transferAt D G.level p.1 ((e v' u' γ').1.lam G.level Mn.η0)
        (e v' u' γ').1.degree
        ((e v' u' γ').1.fluxOp (D.eps (G.level - 1)) (Cc (e v' u' γ').1) Cc0) t
        (c.1.recenter D (D.eps (G'.level - 1) • X)) z d I
      else 0

/-- A weak passage has its data. -/
theorem IsWeakPassage.witness {P : ProvParams} {Mn : WeakMenu} {rW : ℝ} {Din : ℕ}
    {G G' : GenStage D ScalarH Dm b j₀} (h : IsWeakPassage D P Mn rW Din G G') :
    Nonempty (WeakPassageWitness P Mn rW Din G G') := by
  obtain ⟨-, -, -, -, -, e, idx, Cc, Cc0, hL, hL0, hinj, hall⟩ := h
  exact ⟨WeakPassageWitness.mk e idx Cc Cc0 hL hL0 hinj (fun v' u' γ' => (hall v' u' γ').1)
    (fun v' u' γ' => (hall v' u' γ').2.1) (fun v' u' γ' => (hall v' u' γ').2.2)⟩

variable {plan : WeakCoefficientPlan}

/-- The data of a passage of a partial construction. -/
abbrev CaseWitness (x : WeakPassageAt plan) :=
  WeakPassageWitness x.inst.P x.inst.menu (x.inst.D.termRW x.inst.physical.σw x.inst.M)
    (1 + (x.inst.M + x.inst.physical.Jw - x.i) * x.inst.menu.N) (x.stage x.i) (x.stage (x.i - 1))

/-- The data of each passage exist. -/
theorem caseWitness_nonempty (x : WeakPassageAt plan) : Nonempty (CaseWitness x) :=
  IsWeakPassage.witness (x.pc.2 x.i (by have := x.hi; omega) x.hiJ).1

/-- The original window of the slot `k` of the level `m`, in cell time. -/
def liftWindowOf (D : OCData) (m : ℕ) (k : ℤ) : Set ℝ :=
  Set.Icc (D.slotStart m k / D.cellScaleSq m)
    ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m)

/-- **High-reserve lifts of a passage**: for an incoming stage
holomorphically generated with no export, lift families of every reserve that agree with the lifts
of the passage on the windows and the admissible offsets, on the grades constrained by the lift
relation: the inherited sources on their grades `hh ≤ pathLen` (a path mean reads only those),
and the grade-zero lifts at the grade `0` (the eddy letters read only those; the arrays `Cc` of
an eddy source are not read, and its lift family is `True`). -/
def WeakHighReserveLiftsStatement (plan : WeakCoefficientPlan) : Prop :=
  ∀ (x : WeakPassageAt plan), WeakHolGen (x.stage x.i) → ∀ (w : CaseWitness x) (R : ℕ),
    ∃ (Cc' : ∀ s : WeakSource (x.stage x.i), ℤ → RealChain → ℕ → ℕ →
          LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ))
      (Cc0' : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)),
      (∀ s : WeakSource (x.stage x.i), s.IsLiftFamily R R x.inst.physical.Nw
        (x.inst.D.eps ((x.stage x.i).level - 1)) (Cc' s)) ∧
      (∀ (k : ℤ) (A : RealChain), Odd k →
        IsAdmissibleChain x.inst.D x.inst.physical.bw x.inst.j₀ (x.stage x.i).level k A →
        IsLiftSequence (familyLiftData (Dm := x.inst.Dm) (hv := fun _ : Fin 1 => ℝ) x.inst.D
            (x.stage x.i).level k A (x.inst.D.eps ((x.stage x.i).level - 1)) (fun _ _ _ => []))
          R R (x.inst.D.slotStart (x.stage x.i).level k / x.inst.D.cellScaleSq (x.stage x.i).level)
          ((((k : ℝ) + 61 / 48) * ocTau x.inst.D.α x.inst.D.q x.inst.D.Λ (x.stage x.i).level) /
            x.inst.D.cellScaleSq (x.stage x.i).level)
          x.inst.physical.Nw 0 (Cc0' k A)) ∧
      (∀ (s : WeakSource (x.stage x.i)), s.IsInherited → ∀ (k : ℤ) (A : RealChain),
        IsAdmissibleChain x.inst.D x.inst.physical.bw x.inst.j₀ (x.stage x.i).level k A →
        ∀ τ ∈ liftWindowOf x.inst.D (x.stage x.i).level k,
        ∀ X ∈ ladderOmega x.inst.D x.inst.physical.bw x.inst.j₀ (x.stage x.i).level k A
          (x.inst.D.eps ((x.stage x.i).level - 1)),
        ∀ hh ≤ s.pathLen, ∀ n m (α : DerivativeWord2 m) z v u,
          Cc' s k A hh n m α τ X z v u = w.Cc s k A hh n m α τ X z v u) ∧
      (∀ (k : ℤ) (A : RealChain), Odd k →
        IsAdmissibleChain x.inst.D x.inst.physical.bw x.inst.j₀ (x.stage x.i).level k A →
        ∀ τ ∈ liftWindowOf x.inst.D (x.stage x.i).level k, ∀ n m (α : DerivativeWord2 m) X z v u,
          Cc0' k A 0 n m α τ X z v u = w.Cc0 k A 0 n m α τ X z v u)

/-- **The inherited ledger: the entries of the inherited sources**, with the constant map `Kinh`. -/
def WeakInheritedLedgerStatement (plan : WeakCoefficientPlan) (Kinh : WeakConstFn) : Prop :=
  ∀ (x : WeakPassageAt plan) (C : ℝ), 0 ≤ C →
    WeakCertified C (weakReserve x.inst x.i) (weakWeight x.inst x.i) (x.stage x.i) →
      0 ≤ Kinh x.inst.request C ∧
      ∀ (w : CaseWitness x) v' u' (γ' : (x.stage (x.i - 1)).fam.Γ v' u'),
        (w.e v' u' γ').1.IsInherited →
        WeakLedgerEntry x (Kinh x.inst.request C) (weakReserve x.inst (x.i - 1))
          (weakWeight x.inst (x.i - 1)) v' u' γ'

/-- **The eddy ledger: the entries of the eddy sources**, with the constant map `Keddy`. -/
def WeakEddyLedgerStatement (plan : WeakCoefficientPlan) (Keddy : WeakConstFn) : Prop :=
  ∀ (x : WeakPassageAt plan) (C : ℝ), 0 ≤ C →
    WeakCertified C (weakReserve x.inst x.i) (weakWeight x.inst x.i) (x.stage x.i) →
      0 ≤ Keddy x.inst.request C ∧
      ∀ (w : CaseWitness x) v' u' (γ' : (x.stage (x.i - 1)).fam.Γ v' u'),
        ¬ (w.e v' u' γ').1.IsInherited →
        WeakLedgerEntry x (Keddy x.inst.request C) (weakReserve x.inst (x.i - 1))
          (weakWeight x.inst (x.i - 1)) v' u' γ'

/-- A ledger entry stays an entry for a larger constant. -/
theorem WeakLedgerEntry.mono {x : WeakPassageAt plan} {C C' mres : ℝ} {L : ℕ}
    {v u : CompIn (x.stage (x.i - 1)).comps} {γ : (x.stage (x.i - 1)).fam.Γ v u}
    (h : WeakLedgerEntry x C mres L v u γ) (hCC : C ≤ C') : WeakLedgerEntry x C' mres L v u γ := by
  intro d I k
  obtain ⟨e, Δ, leaf, hE, hf, hΔ, hL, hSF, hDr, hsum⟩ := h d I k
  refine ⟨e, Δ, leaf, hE, hf, hΔ, hL, hSF, hDr, hsum.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hs := ((x.stage (x.i - 1)).fam.identity v u γ).record.size_nonneg
  have hr : 0 ≤ (((x.stage (x.i - 1)).fam.identity v u γ).record.length /
      x.inst.D.eps (x.stage (x.i - 1)).level) ^
      (((x.stage (x.i - 1)).fam.identity v u γ).maxOrder - 2) :=
    pow_nonneg (div_nonneg ((x.stage (x.i - 1)).fam.identity v u γ).record.length_pos.le
      (case_eps_pos x.inst _).le) _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC hs) hr

/-- **The weak ledger from the inherited and the eddy entries.** -/
theorem weakPassageLedger_of_ingredients (Kinh Keddy : WeakConstFn)
    (hinh : WeakInheritedLedgerStatement plan Kinh) (heddy : WeakEddyLedgerStatement plan Keddy) :
    WeakPassageLedgerStatement plan (fun R C => max (Kinh R C) (Keddy R C)) := by
  intro x C hC hW
  obtain ⟨w⟩ := caseWitness_nonempty x
  obtain ⟨hK1, hE1⟩ := hinh x C hC hW
  obtain ⟨hK2, hE2⟩ := heddy x C hC hW
  refine ⟨le_max_of_le_left hK1, fun v' u' γ' => ?_⟩
  by_cases hk : (w.e v' u' γ').1.IsInherited
  · exact (hE1 w v' u' γ' hk).mono (le_max_left _ _)
  · exact (hE2 w v' u' γ' hk).mono (le_max_right _ _)

end AVRegularity.Providers.WeakGen
end
end
end
