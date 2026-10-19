-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.EntryScales.TerminalCore
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
public import AVRegularity.Proofs.CascadeInvariants.Menu.FirstSource
import AVRegularity.Proofs.CascadeInvariants.Menu.LedgerAll
import AVRegularity.CycleReference.TorusStreamFluxEquation
import AVRegularity.EntryTerminal.Ingredients.SeedQuiet.Proof
public import AVRegularity.EntryTerminal.Assembly.Route.Ingredients
import AVRegularity.Definitions.Finite.FiniteLiftBridge
import AVRegularity.Proofs.CascadeInvariants.LedgerAll
import Mathlib.Data.Int.Star

section
section
/-! **The level floor `C ε_{M+1} ≤ ε_M`** for large `M` (for the field `hlen` of `StepFacts`: the
lengths of the weak stage are at most `C_L ε_{M+1}`, those required are at most `ε_M`).
From `epsilon_q_ratio_error`: `ε_{M+1} ≤ (1+K) ε_M^q`, and `ε_M^{q-1} → 0`.

Degenerate case: `C ≤ 0` holds for every `M`. -/

@[expose] public section

open Filter Topology

namespace AVRegularity.EntryTerminal.Route

theorem eps_floor {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ) (C : ℝ) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → C * ocEpsilon q Λ (M + 1) ≤ ocEpsilon q Λ M := by
  obtain ⟨K, hK, hb⟩ := CycleReference.epsilon_q_ratio_error hq
  have hpos : 0 < |C| * (1 + K) + 1 := by positivity
  have ht := AVRegularity.EntryScales.epsilon_rpow_tendsto_zero (p := q - 1) hq hΛ (by linarith)
  have hev : ∀ᶠ M : ℕ in atTop, ocEpsilon q Λ M ^ (q - 1) < (|C| * (1 + K) + 1)⁻¹ :=
    (tendsto_order.1 ht).2 _ (inv_pos.mpr hpos)
  obtain ⟨M₁, hM₁⟩ := eventually_atTop.1 hev
  refine ⟨max M₁ 1, fun M hM => ?_⟩
  have hM1 : M₁ ≤ M := (le_max_left _ _).trans hM
  have hM2 : 1 ≤ M := (le_max_right _ _).trans hM
  have he := (AVRegularity.Scales.epsilon_basic (m := M) hq hΛ).1
  have he1 := (AVRegularity.Scales.epsilon_basic (m := M + 1) hq hΛ).1
  have hle1 := (AVRegularity.Scales.epsilon_basic (m := M) hq hΛ).2.1
  have hr := hb Λ (M + 1) hΛ (by omega)
  rw [Nat.add_sub_cancel] at hr
  have hq0 : 0 < ocEpsilon q Λ M ^ q := Real.rpow_pos_of_pos he q
  have h1 : ocEpsilon q Λ (M + 1) / ocEpsilon q Λ M ^ q ≤ 1 + K := by
    have := (abs_le.1 hr).2
    nlinarith
  have h2 : ocEpsilon q Λ (M + 1) ≤ (1 + K) * ocEpsilon q Λ M ^ q := by
    rw [div_le_iff₀ hq0] at h1
    linarith
  have h3 : ocEpsilon q Λ M ^ q = ocEpsilon q Λ M ^ (q - 1) * ocEpsilon q Λ M := by
    rw [Real.rpow_sub_one he.ne']
    field_simp
  have ht := hM₁ M hM1
  set t := ocEpsilon q Λ M ^ (q - 1)
  have ht0 : 0 ≤ t := Real.rpow_nonneg he.le _
  have hCa : C * ocEpsilon q Λ (M + 1) ≤ |C| * ocEpsilon q Λ (M + 1) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) he1.le
  have hkey : |C| * (1 + K) * t ≤ 1 := by
    have h := mul_lt_mul_of_pos_right ht hpos
    rw [inv_mul_cancel₀ hpos.ne'] at h
    nlinarith [abs_nonneg C]
  calc C * ocEpsilon q Λ (M + 1) ≤ |C| * ocEpsilon q Λ (M + 1) := hCa
    _ ≤ |C| * ((1 + K) * (t * ocEpsilon q Λ M)) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
        rw [← h3]; exact h2
    _ = (|C| * (1 + K) * t) * ocEpsilon q Λ M := by ring
    _ ≤ 1 * ocEpsilon q Λ M := mul_le_mul_of_nonneg_right hkey he.le
    _ = _ := one_mul _

end AVRegularity.EntryTerminal.Route
end
end

section
/-! **Monotonicity of the context certificate and transport along the re-rooting.**

* `ctxModeSup_mono_mres`, `ctxSize_mono`: the context size is monotone in the reserve and in the
  weight exponent `L` (the carrier `carrierC` grows with the reserve);
* `isContextCertified_seed_of_encoding`: if `Gt` is certified at `kW`, the re-rooting `seed` of
  `Gt` (`IsSeedEncoding`, same exports) is certified at `kS` as soon as the reserve of `(ι v)` at
  `kS` is at most the reserve of `v` at `kW` and `kS.Lstar ≤ kW.Lstar`. The witnesses `θ` are
  those of `Gt`: the records, orders and fluxes agree.

Degenerate cases: a seed with no identities (vacuous); `kS = kW` and `ι = id`. -/

@[expose] public section

open Homogenization AVRegularity AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity.GenStage

theorem carrierC_mono {D : OCData} {b : ℝ} {dd : ChainData} {n : ℕ} {m m' : ℝ}
    (hε : ∀ k, 0 ≤ D.eps k) (hb : 0 ≤ b) (h : m ≤ m') :
    carrierC D b dd n m ⊆ carrierC D b dd n m' := by
  intro x hx
  obtain ⟨h1, h2, h3⟩ := hx
  have hbm := mul_nonneg hb (sub_nonneg.2 h)
  refine ⟨lt_of_lt_of_le h1 ?_, fun k => ?_, lt_of_lt_of_le h3 (by nlinarith)⟩
  · have := mul_nonneg (hε dd.baseLevel) (sub_nonneg.2 h)
    nlinarith
  · obtain ⟨a1, a2⟩ := h2 k
    refine ⟨lt_of_lt_of_le a1 ?_, lt_of_lt_of_le a2 (by nlinarith)⟩
    have := mul_nonneg (mul_nonneg (hε (dd.baseLevel + 1 + k)) hb) (sub_nonneg.2 h)
    nlinarith

theorem ctxModeSup_mono_mres {D : OCData} {b : ℝ} {j₀ i : ℕ} {p : ℤ}
    {F : ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ} {m m' : ℝ} (hε : ∀ k, 0 ≤ D.eps k)
    (hb : 0 ≤ b) (h : m ≤ m') (hh : ℤ) :
    ctxModeSup D b j₀ i p F m hh ≤ ctxModeSup D b j₀ i p F m' hh := by
  unfold ctxModeSup
  refine iSup_le fun dd => iSup_le fun n => iSup_le fun hex => iSup_le fun t => iSup_le fun ht =>
    iSup_le fun x => iSup_le fun hx => iSup_le fun hre => ?_
  exact le_iSup_of_le dd (le_iSup_of_le n (le_iSup_of_le hex (le_iSup_of_le t
    (le_iSup_of_le ht (le_iSup_of_le x (le_iSup_of_le (carrierC_mono hε hb h hx)
    (le_iSup_of_le hre le_rfl)))))))

theorem ctxSize_mono {D : OCData} {b : ℝ} {j₀ i : ℕ}
    {F : {k : ℤ // Odd k} → ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ} {m m' : ℝ} {L L' : ℕ}
    (hε : ∀ k, 0 ≤ D.eps k) (hb : 0 ≤ b) (hm : m ≤ m') (hL : L ≤ L') :
    ctxSize D b j₀ i F m L ≤ ctxSize D b j₀ i F m' L' := by
  unfold ctxSize
  refine ENNReal.tsum_le_tsum fun hh => mul_le_mul' ?_ (iSup_mono fun p =>
    ctxModeSup_mono_mres hε hb hm hh)
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  exact pow_le_pow_right₀ (by linarith [abs_nonneg (hh : ℝ)]) hL

end AVRegularity.GenStage
end
end

section
/-! **The certificate passes to the re-rooted seed** (`isContextCertified_seed_of_encoding`),
using `IsSeedEncoding` (levels, records, orders, fluxes agree) and the equality of the exports. The
witnesses `θ`, `f`, `F` are those of the terminal family; only the reserve and the weight exponent
are changed (`ctxSize_mono`).

Degenerate case: `seed = Gt`, `ι = id`, `kS = kW`. -/

@[expose] public section

open Homogenization AVRegularity AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity.GenStage

theorem stageCtx_cast_val {D : OCData} {b : ℝ} {j₀ l l' : ℕ} {p : OddSlot} (h : l = l')
    (c : StageCtx D b j₀ l p) : (h ▸ c : StageCtx D b j₀ l' p).1 = c.1 := by
  subst h; rfl

theorem isContextCertified_seed_of_encoding {D : OCData} {b : ℝ} {j₀ Dt Ds : ℕ}
    {Pt : ProvParams} {lawT : BirthLaw} {rootM rootR : ℕ → ℝ} {seedKt freshKt seedKc : ℕ → KernelSpec}
    {Gt : GenStage D ScalarH Dt b j₀} {seed : GenStage D ScalarH Ds b j₀}
    {ι : CompIn Gt.comps ≃ CompIn seed.comps}
    (henc : IsSeedEncoding Pt lawT rootM rootR seedKt freshKt seedKc Gt seed ι)
    (hexp : ∀ (i : ℕ) (p : ℤ) (e : Gen .ctx i p), seed.exports e ↔ Gt.exports e)
    {kW kS : InvConsts} (hcert : Gt.IsContextCertified kW)
    (hres : ∀ v : CompIn Gt.comps, compReserve kS (ι v).1 ≤ compReserve kW v.1)
    (hL : kS.Lstar ≤ kW.Lstar) (hε : ∀ k, 0 ≤ D.eps k) (hb : 0 ≤ b) :
    seed.IsContextCertified kS := by
  obtain ⟨hlev, -, -, -, -, -, e, idx, -, hdata⟩ := henc
  have hE : (@seed.exports : SeedExports) = (@Gt.exports : SeedExports) := by
    funext i p x
    exact propext (hexp i p x)
  intro v' u' γ'
  obtain ⟨v, rfl⟩ := ι.surjective v'
  obtain ⟨u, rfl⟩ := ι.surjective u'
  obtain ⟨γ, rfl⟩ := (e v u).surjective γ'
  obtain ⟨-, -, -, hrec, hord, hflux⟩ := hdata v u γ
  obtain ⟨θ, hθ0, hθr, hθ⟩ := hcert v u γ
  refine ⟨θ, hθ0, ?_, fun d α c => ?_⟩
  · intro d hd hdo
    rw [hrec]
    rw [hord] at hdo
    rw [hlev]
    exact hθr d hd hdo
  · obtain ⟨f, F, hfF, hsize⟩ := hθ d α c
    refine ⟨f, F, fun p => ?_, ?_⟩
    · obtain ⟨hg, hh, hfl⟩ := hfF p
      refine ⟨?_, ?_, fun ctx t ht X z => ?_⟩
      · rw [hlev, hE]; exact hg
      · rw [hlev]; exact hh
      · obtain ⟨c', hc'⟩ : ∃ c' : StageCtx D b j₀ Gt.level p, ctx.1 = c'.1 :=
          ⟨hlev ▸ ctx, (stageCtx_cast_val hlev ctx).symm⟩
        have hc := hflux p ctx c' hc' d α t X z
        rw [hc, hc']
        have := hfl c' t (by rw [← hlev]; exact ht) X z
        rw [hlev]
        exact this
    · refine le_trans ?_ hsize
      rw [hlev]
      exact ctxSize_mono hε hb (hres v) hL

end AVRegularity.GenStage
end
end

section
/-! **The structural conjuncts of the seed certificate**. The seed is a
re-rooted copy of the retained family `Gt'.retained M 1 R_T` (`IsSeedEncoding`): same level,
pieces, weights, actual chains, identity maps, records, orders and fluxes. Its provenance is
`.seed (idx γ) (seedTagOf (tags γ))`. So naturalness, tags, generatedness, shift invariance and
slotwise transversality pass:
- from a stage to its restriction (`*_restrict`; transversality and shift invariance have their
  own restriction lemmas);
- from the restricted stage to the seed (`seed_*_of_encoding`).

`isGenerated_of_exprFor` turns the expressions of `terminalSuccessor_generation` into
`IsGenerated`.

Degenerate cases: a stage without identities (every clause is vacuous); an empty retained family. -/

@[expose] public section

open Homogenization AVRegularity AVRegularity.Sobolev

namespace AVRegularity.EntryTerminal.Ingredients

variable {D : OCData} {b : ℝ} {j₀ : ℕ}

section Restrict

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {Dm : ℕ}

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
theorem seedCert_isNatural_restrict {G : GenStage D hr Dm b j₀} {N : ℕ} (hG : G.IsNatural N)
    (S : Finset Comp) (hS : S ⊆ G.comps) : (G.restrict S hS).IsNatural N :=
  ⟨hG.1, hG.2.1, hG.2.2.1, fun v u => hG.2.2.2 ⟨v.1, hS v.2⟩ ⟨u.1, hS u.2⟩⟩

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
theorem seedCert_hasTags_restrict {G : GenStage D hr Dm b j₀} {P : ProvParams} (hG : G.HasTags P)
    (S : Finset Comp) (hS : S ⊆ G.comps) : (G.restrict S hS).HasTags P :=
  fun v u γ => hG ⟨v.1, hS v.2⟩ ⟨u.1, hS u.2⟩ γ

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
theorem seedCert_isGenerated_restrict {G : GenStage D hr Dm b j₀} (hG : G.IsGenerated)
    (S : Finset Comp) (hS : S ⊆ G.comps) : (G.restrict S hS).IsGenerated :=
  fun p v u γ d I k => hG p ⟨v.1, hS v.2⟩ ⟨u.1, hS u.2⟩ γ d I k

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- The expressions of `terminalSuccessor_generation` give `IsGenerated`. -/
theorem isGenerated_of_exprFor {G : GenStage D hr Dm b j₀}
    (h : ∀ v u (γ : G.fam.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1)) (c : Fin 2),
      ∃ e : (q : OddSlot) → Gen .ctx G.level q.1, G.IsExprFor v u γ d I c e) :
    G.IsGenerated := by
  intro p v u γ d I k
  obtain ⟨e, he⟩ := h v u γ d I k
  obtain ⟨hs, hfs, f, hd, hf⟩ := he p
  exact ⟨f, ⟨e p, hs, hfs, hd⟩, hf⟩

end Restrict

section Seed

variable {Dt Ds : ℕ} {Pt : ProvParams} {lawT : BirthLaw} {rootM rootR : ℕ → ℝ}
  {seedKt freshKt seedKc : ℕ → KernelSpec}
  {Gt : GenStage D ScalarH Dt b j₀} {seed : GenStage D ScalarH Ds b j₀}
  {ι : CompIn Gt.comps ≃ CompIn seed.comps}

theorem seed_isNatural_of_encoding
    (he : IsSeedEncoding Pt lawT rootM rootR seedKt freshKt seedKc Gt seed ι) {N : ℕ}
    (hG : Gt.IsNatural N) : seed.IsNatural N := by
  obtain ⟨hlev, -, -, hact, hpiece, hweight, e, idx, hidx, hdata⟩ := he
  obtain ⟨h1, h2, h3, h4⟩ := hG
  refine ⟨fun p => ?_, fun p t => ?_, fun p => ?_, fun v u => ?_⟩
  · rw [hpiece, hlev]; exact h1 p
  · rw [hweight, hlev]; exact h2 p t
  · rw [hact, hlev]; exact h3 p
  · obtain ⟨v₀, rfl⟩ := ι.surjective v
    obtain ⟨u₀, rfl⟩ := ι.surjective u
    intro γ₁ γ₂ heq
    obtain ⟨g₁, rfl⟩ := (e v₀ u₀).surjective γ₁
    obtain ⟨g₂, rfl⟩ := (e v₀ u₀).surjective γ₂
    rw [(hdata v₀ u₀ g₁).1, (hdata v₀ u₀ g₂).1] at heq
    injection heq with hk _
    obtain ⟨-, -, hg⟩ := hidx v₀ u₀ g₁ v₀ u₀ g₂ hk
    rw [eq_of_heq hg]

theorem seed_hasTags_of_encoding
    (he : IsSeedEncoding Pt lawT rootM rootR seedKt freshKt seedKc Gt seed ι)
    (hG : Gt.HasTags Pt) (P : ProvParams) : seed.HasTags P := by
  obtain ⟨-, -, -, -, -, -, e, idx, -, hdata⟩ := he
  intro v u γ
  obtain ⟨v₀, rfl⟩ := ι.surjective v
  obtain ⟨u₀, rfl⟩ := ι.surjective u
  obtain ⟨γ₀, rfl⟩ := (e v₀ u₀).surjective γ
  obtain ⟨hprov, -, -, hrec, hord, -⟩ := hdata v₀ u₀ γ₀
  rw [hprov, hrec, hord]
  exact hG v₀ u₀ γ₀

theorem seed_isGenerated_of_encoding
    (he : IsSeedEncoding Pt lawT rootM rootR seedKt freshKt seedKc Gt seed ι)
    (hexp : ∀ (i : ℕ) (p : ℤ) (e : Gen .ctx i p), seed.exports e ↔ Gt.exports e)
    (hG : Gt.IsGenerated) : seed.IsGenerated := by
  obtain ⟨hlev, -, -, -, -, -, e, idx, -, hdata⟩ := he
  intro p v u γ d I k
  obtain ⟨v₀, rfl⟩ := ι.surjective v
  obtain ⟨u₀, rfl⟩ := ι.surjective u
  obtain ⟨γ₀, rfl⟩ := (e v₀ u₀).surjective γ
  obtain ⟨f, ⟨g, hs, hfs, hd⟩, hf⟩ := hG p v₀ u₀ γ₀ d I k
  have hflux := (hdata v₀ u₀ γ₀).2.2.2.2.2
  refine ⟨f, ?_, ?_⟩
  · rw [hlev]
    exact ⟨g, hs, Providers.GenSem.fromSeed_mono (fun e' h => (hexp _ _ e').2 h) hfs, hd⟩
  · rintro ⟨ch, hch⟩ t ht X z
    rw [hflux p ⟨ch, hch⟩ ⟨ch, hlev ▸ hch⟩ rfl d I t X z,
      hf ⟨ch, hlev ▸ hch⟩ t (hlev ▸ ht) X z]
    dsimp only
    by_cases h1 : IsAdmissibleChain D b j₀ Gt.level p.1
        (RealChain.recenter D ch (D.eps (Gt.level - 1) • X))
    · have h2 : IsAdmissibleChain D b j₀ seed.level p.1
          (RealChain.recenter D ch (D.eps (seed.level - 1) • X)) := by rw [hlev]; exact h1
      simp only [h1, h2, ite_true]
      rw [hlev]
    · have h2 : ¬ IsAdmissibleChain D b j₀ seed.level p.1
          (RealChain.recenter D ch (D.eps (seed.level - 1) • X)) := by rw [hlev]; exact h1
      simp only [h1, h2, ite_false]

theorem seed_isSlotTransverse_of_encoding
    (he : IsSeedEncoding Pt lawT rootM rootR seedKt freshKt seedKc Gt seed ι)
    (hG : Gt.IsSlotTransverse) : seed.IsSlotTransverse := by
  obtain ⟨hlev, -, -, -, -, -, e, idx, -, hdata⟩ := he
  rintro p ⟨ch, hch⟩ v u γ d I t ht X z s
  obtain ⟨v₀, rfl⟩ := ι.surjective v
  obtain ⟨u₀, rfl⟩ := ι.surjective u
  obtain ⟨γ₀, rfl⟩ := (e v₀ u₀).surjective γ
  have hflux := (hdata v₀ u₀ γ₀).2.2.2.2.2 p ⟨ch, hch⟩ ⟨ch, hlev ▸ hch⟩ rfl d I t
  rw [hflux, hflux]
  rw [hlev] at ht
  exact hG p ⟨ch, hlev ▸ hch⟩ v₀ u₀ γ₀ d I t ht X z s

theorem seed_isShiftInvariant_of_encoding
    (he : IsSeedEncoding Pt lawT rootM rootR seedKt freshKt seedKc Gt seed ι)
    (hG : Gt.IsShiftInvariant) : seed.IsShiftInvariant := by
  obtain ⟨hlev, -, -, -, -, -, e, idx, -, hdata⟩ := he
  refine ⟨?_, ?_⟩
  · rintro p ⟨ch, hch⟩ ⟨ch', hch'⟩ n hcc v u γ d I
    obtain ⟨v₀, rfl⟩ := ι.surjective v
    obtain ⟨u₀, rfl⟩ := ι.surjective u
    obtain ⟨γ₀, rfl⟩ := (e v₀ u₀).surjective γ
    funext t X z
    rw [(hdata v₀ u₀ γ₀).2.2.2.2.2 p ⟨ch', hch'⟩ ⟨ch', hlev ▸ hch'⟩ rfl d I t X z,
      (hdata v₀ u₀ γ₀).2.2.2.2.2 p ⟨ch, hch⟩ ⟨ch, hlev ▸ hch⟩ rfl d I t X z]
    exact congrFun (congrFun (congrFun (hG.1 p ⟨ch, hlev ▸ hch⟩ ⟨ch', hlev ▸ hch'⟩ n hcc
      v₀ u₀ γ₀ d I) t) X) z
  · rintro p ⟨ch, hch⟩ ⟨ch', hch'⟩ n hchild hcc v u γ d I t X z
    obtain ⟨v₀, rfl⟩ := ι.surjective v
    obtain ⟨u₀, rfl⟩ := ι.surjective u
    obtain ⟨γ₀, rfl⟩ := (e v₀ u₀).surjective γ
    rw [(hdata v₀ u₀ γ₀).2.2.2.2.2 p ⟨ch', hch'⟩ ⟨ch', hlev ▸ hch'⟩ rfl d I t X z,
      (hdata v₀ u₀ γ₀).2.2.2.2.2 p ⟨ch, hch⟩ ⟨ch, hlev ▸ hch⟩ rfl d I t _ z]
    have hε : D.eps (seed.level - 1) = D.eps (Gt.level - 1) := by rw [hlev]
    rw [hε]
    exact hG.2 p ⟨ch, hlev ▸ hch⟩ ⟨ch', hlev ▸ hch'⟩ n hchild hcc v₀ u₀ γ₀ d I t X z

end Seed

end AVRegularity.EntryTerminal.Ingredients
end
end

section
/-! **The terminal menu: the facts of the terminal passage that the generic
ledger bundle asks for**.

The generic ledger (`Providers/CascadeInvariants/Menu`) is a theorem about an arbitrary menu `Mn`, tag parameters
`P` and a bundle `MenuFacts`, two budgets and a chain environment. The terminal supplies the bundle
at `G := Gw`, `G' := Gt'`, `P := A.Pt D Cw cr M`, `Mn := A.Mt M sXT sZT tp cr`, `kI := kW`,
`nMax := termNMax A`, `hMax := d_W`, `npad := 0`, record factor `1`, `Dm := A.Dt`.

The statements (each a `Prop`):
* `TermScaleConstsStmt`: one constant `Cu` for the scale facts of the passage `M → M - 1`
  (`PassScales`, the displacement and covariance at the terminal radius `c_r ρ` and anchor `t_p`,
  the first-source scales);
* `TermStepFactsStmt`: `StepFacts kW Gw Gt' P Cu` from `IsWeakStage`;
* `TermMenuFieldsStmt`: the menu fields of `MenuFacts` (alphabet, orders, reserves, depth,
  weight floor, radius, tags);
* `TermLedgerBudgetStmt`, `TermDiagBudgetStmt`: the two budgets, with thresholds on `C_w`;
* `TermChainEnvStmt`: the chain environment of the carrier pair.

`terminal_ledger_concl` assembles them and the generic ledger `LedgerAllMenuStatement` into the
conclusion `LedgerConcl` (no ledger hypothesis: `ledger_all_menu` proves the ledger) for every
identity of `Gt'`.

Degenerate cases. `d_W = 0`: no mean or covariance letter, the alphabet does not read `nMax`, so
`termNMax` is `N_T + 1` and the order cap `nMax + 4 p_T ≤ D̄₀` holds (the diagonal letter has order
`N_T + 1 + 4 p_T`). `c_r = 1`: every factor `c_r` disappears. A weak stage without identities:
the budgets are only used by the first source. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance

namespace AVRegularity.EntryTerminal.Route

open AVRegularity.Providers.CascadeInvariants AVRegularity.Providers.CascadeInvariants.Menu AVRegularity.Providers.GenSem
  AVRegularity.Providers.Majorant AVRegularity.Providers.ComplexContext AVRegularity.Providers.ComplexFlow

/-- The alphabet bound handed to the generic ledger: `N_T + D_W` when the weak depth is positive
(the letters of the terminal alphabet reach it), and `N_T + 1` otherwise (then the alphabet does
not read the bound, and `N_T + 1 + 4 p_T ≤ D̄₀`). -/
def termNMax {X : TermConstruction} (A : TermArgs X) : ℕ :=
  A.NT + (if A.dW = 0 then 1 else A.DW)

/-- The per-level context of the terminal passage: the first conjuncts of `SeedCtx`. -/
def TermPassCtx {X : TermConstruction} (A : TermArgs X) (sXT sZT : ℕ) (nW : ℕ+)
    (cr CL Cχ : ℝ) (kW : InvConsts) (cP CP cH Cw : ℝ) {j₀ : ℕ} (M : ℕ) (D : OCData) (a : ℝ)
    (lawW : BirthLaw) (PW : ProvParams) (Gw : GenStage D ScalarH A.Dt A.bw j₀) (aM tp : ℝ)
    (lawT : BirthLaw) (Gt' : GenStage D ScalarH A.Dt A.bw j₀) : Prop :=
  IsTermData X A.Λ M D ∧
    IsWeakStage lawW PW A.φ₀ A.hφ₀ M (M + A.Jw) A.Jw A.dW A.DW nW kW a A.T₀ A.σw CL Cχ A.χw
      Gw aM ∧
    tp ∈ ocQuietTimes D.α D.q D.Λ D.ζ M ∧ aM + cP * D.termH M ≤ tp ∧ tp ≤ aM + CP * D.termH M ∧
    IsTerminalLaw lawW lawT cH A.η₀ A.nWords ∧
    IsActualSuccessor D (A.Pt D Cw cr M) (A.Mt M sXT sZT tp cr) Gw Gt'

theorem TermPassCtx.of_seedCtx {X : TermConstruction} {A : TermArgs X} {sXT sZT : ℕ} {nW : ℕ+}
    {cr CL Cχ : ℝ} {kW : InvConsts} {cP CP cH Cw : ℝ} {j₀ M : ℕ} {D : OCData} {a : ℝ}
    {lawW : BirthLaw} {PW : ProvParams} {Gw : GenStage D ScalarH A.Dt A.bw j₀} {aM tp : ℝ}
    {lawT : BirthLaw} {Gt' : GenStage D ScalarH A.Dt A.bw j₀} {seed : GenStage D ScalarH A.Ds A.bw j₀}
    {rootM rootR : ℕ → ℝ} {seedKc : ℕ → KernelSpec}
    {ι : CompIn (Gt'.retained M 1 A.RT).comps ≃ CompIn seed.comps}
    (h : SeedCtx A sXT sZT nW cr CL Cχ kW cP CP cH Cw M D a lawW PW Gw aM tp lawT Gt' seed rootM
      rootR seedKc ι) :
    TermPassCtx A sXT sZT nW cr CL Cχ kW cP CP cH Cw M D a lawW PW Gw aM tp lawT Gt' :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

/-- The hypotheses on the constants that the terminal passage uses: the data are valid, `Λ ≥ 128`,
the floor `liftWt D̄₀ d_W n_max ≤ kW.Lstar` (explicit; from `IsSeedAllocation` on the seed side, see
`termPlanHyp_of_plan`), the producer reserve `kW.G0 ≤ kW.Hprod`, and the reserves of the menu. -/
structure TermPlanHyp {X : TermConstruction} (A : TermArgs X) (sXT sZT : ℕ) (nW : ℕ+) (cr : ℝ)
    (kW : InvConsts) : Prop where
  valid : A.Valid
  hΛ : 128 ≤ A.Λ
  hLstar : UEnv.liftWt A.Dt A.dW (termNMax A) ≤ kW.Lstar
  hGH : kW.G0 ≤ kW.Hprod
  hsX : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sXT
  hsZ : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sZT

/-- **The scale facts of the terminal passage `M → M - 1` with one constant `Cu`**, uniform in the
level `M ≥ 2`, the datum `D` and the anchor: `PassScales`, the displacement and covariance at the
terminal radius `c_r ρ_M` (anchor `t_p` arbitrary), the cost of the anchor-zero representation, and
the first-source scales (`a_{M-1}τ''_M`, `ownSize`, the drift). -/
structure TermScaleConsts {X : TermConstruction} (A : TermArgs X) (cr Cu : ℝ) : Prop where
  hCu : 1 ≤ Cu
  hsc : ∀ (M : ℕ) (D : OCData), IsTermData X A.Λ M D → 2 ≤ M → PassScales D M Cu
  displacement : ∀ (M : ℕ) (D : OCData), IsTermData X A.Λ M D → 2 ≤ M →
    ocDStar D.q D.Λ M (D.kap M) (D.kap (M - 1)) / (cr * liftLength D M) ≤
      Cu * D.eps (M - 1) ^ (3 * ocDelta D.α D.q)
  covariance : ∀ (M : ℕ) (D : OCData), IsTermData X A.Λ M D → 2 ≤ M → ∀ (tp t : ℝ) (i j : Fin 2),
    |ocCovariance D.α D.q D.Λ D.ζ M (D.κ M) (D.κ (M - 1)) tp t i j| ≤
      Cu * D.eps (M - 1) ^ ocDelta D.α D.q * (cr * liftLength D M) ^ 2
  covariance_cost : ∀ (M : ℕ) (D : OCData), IsTermData X A.Λ M D → 2 ≤ M →
    ∀ (tp t : ℝ) (i j : Fin 2),
    |ocCovariance D.α D.q D.Λ D.ζ M (D.κ M) (D.κ (M - 1)) 0 t i j| +
      |ocCovariance D.α D.q D.Λ D.ζ M (D.κ M) (D.κ (M - 1)) 0 tp i j| ≤
      Cu * D.eps (M - 1) ^ ocDelta D.α D.q * (cr * liftLength D M) ^ 2
  diag : ∃ Ca Cown Cd : ℝ, 0 ≤ Ca ∧ 0 ≤ Cown ∧ ∀ (M : ℕ) (D : OCData), IsTermData X A.Λ M D →
    2 ≤ M →
    ocA D.α D.q D.Λ (M - 1) * (cr ^ 2 * ocTauPP D.α D.q D.Λ M) ≤
        Ca * D.eps (M - 1) ^ ocDelta D.α D.q ∧
      ownSize D M ≤ Cown * D.eps (M - 1) ^ ocDelta D.α D.q ∧
      D.eps M ^ (1 + D.α) ≤ Cd * Real.sqrt (D.kap M * D.kap (M - 1))

/-- **The scale constant exists** (`exists_passScales`, `bandChain_covariance_estimates`,
`exists_diagScales`, `ComplexContext.drift_scale_bound`; `Cu` is `max` of the constants, divided by `c_r²`). -/
def TermScaleConstsStmt : Prop :=
  ∀ X : TermConstruction, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ A : TermArgs X, Λ₀ ≤ A.Λ →
    ∀ cr : ℝ, 0 < cr → cr ≤ 1 → ∃ Cu : ℝ, TermScaleConsts A cr Cu

/-- **The standing facts of the passage from `Gw` to `Gt'`** (`StepFacts`), from
`IsWeakStage`, `IsActualSuccessor` and the carrier start. The level floor `M₀` carries
`C_L ε_{M+1} ≤ ε_M` (for `hlen`), `2 ≤ M`. -/
def TermStepFactsStmt : Prop :=
  ∀ (X : TermConstruction) (A : TermArgs X) (sXT sZT : ℕ) (nW : ℕ+) (cr : ℝ) (kW : InvConsts), TermPlanHyp A sXT sZT nW cr kW →
  ∀ (CL Cχ Cu CH Υ : ℝ) (j₀ : ℕ), TermScaleConsts A cr Cu → 1 ≤ CH → 1 ≤ Υ →
    IsCarrierStart X.α X.q A.Λ A.bw CH Υ j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
  ∀ (cP CP cH Cw : ℝ) (D : OCData) (a : ℝ) (lawW : BirthLaw) (PW : ProvParams)
    (Gw : GenStage D ScalarH A.Dt A.bw j₀) (aM tp : ℝ) (lawT : BirthLaw)
    (Gt' : GenStage D ScalarH A.Dt A.bw j₀),
    TermPassCtx A sXT sZT nW cr CL Cχ kW cP CP cH Cw M D a lawW PW Gw aM tp lawT Gt' →
    StepFacts kW Gw Gt' (A.Pt D Cw cr M) Cu

/-- The menu fields of `MenuFacts` that are neither the stage facts nor the scale facts. -/
structure TermMenuFields {X : TermConstruction} (A : TermArgs X) (sXT sZT : ℕ) (kW : InvConsts)
    (M : ℕ) (D : OCData) {j₀ : ℕ} (Gw : GenStage D ScalarH A.Dt A.bw j₀) (P : ProvParams)
    (Mn : SuccMenu) : Prop where
  alphabet : Mn.A = succAlphabet (termNMax A) A.dW Mn.p 0
  degree : 2 ≤ Mn.N
  degree_cap : Mn.N ≤ termNMax A
  order_cap : ∀ a ∈ Mn.A, letterOrder Mn.N Mn.p a ≤ A.Dt
  reserveX : max (termNMax A) (2 * Mn.p) + A.Dt + 2 ≤ Mn.sX
  reserveZ : max (termNMax A) (2 * Mn.p) + A.Dt + 2 ≤ Mn.sZ
  diagonal_reserveX : max (Mn.N + 1) (2 * Mn.p) + A.Dt + 2 ≤ Mn.sX
  diagonal_reserveZ : max (Mn.N + 1) (2 * Mn.p) + A.Dt + 2 ≤ Mn.sZ
  depth : Gw.fam.HasDepthAtMost A.dW
  weight : UEnv.liftWt A.Dt A.dW (termNMax A) ≤ kW.Lstar
  radius_pos : 0 < Mn.lenFactor
  radius_le : Mn.lenFactor ≤ 1
  tag_degree : P.N = Mn.N
  tag_covariance : P.p = Mn.p
  tag_epsilon : P.eps = D.eps
  tag_delta : P.δ = ocDelta D.α D.q
  tag_eta : P.η0 = Mn.η0
  tag_inflation : P.w (Gw.level - 1) = 1
  tag_length : P.Rb (Gw.level - 1) = 1 * (Mn.lenFactor * liftLength D Gw.level)

/-- **The menu fields** at `termMenu`, `termProvParams`. -/
def TermMenuFieldsStmt : Prop :=
  ∀ (X : TermConstruction) (A : TermArgs X) (sXT sZT : ℕ) (nW : ℕ+) (cr : ℝ) (kW : InvConsts), TermPlanHyp A sXT sZT nW cr kW →
  ∀ (CL Cχ : ℝ) (j₀ M : ℕ), 2 ≤ M →
  ∀ (cP CP cH Cw : ℝ) (D : OCData) (a : ℝ) (lawW : BirthLaw) (PW : ProvParams)
    (Gw : GenStage D ScalarH A.Dt A.bw j₀) (aM tp : ℝ) (lawT : BirthLaw)
    (Gt' : GenStage D ScalarH A.Dt A.bw j₀),
    TermPassCtx A sXT sZT nW cr CL Cχ kW cP CP cH Cw M D a lawW PW Gw aM tp lawT Gt' →
    0 < cr → cr ≤ 1 →
    TermMenuFields A sXT sZT kW M D Gw (A.Pt D Cw cr M) (A.Mt M sXT sZT tp cr)

/-- **The budget of the four non-diagonal sources.** One threshold on `C_w`, independent of
the level, the datum and the stage. -/
def TermLedgerBudgetStmt : Prop :=
  ∀ (X : TermConstruction) (A : TermArgs X) (kW : InvConsts) (Cu : ℝ) (κc : MajConsts),
    MajOK A.bw κc → 0 < A.bw → 1 ≤ Cu →
    ∃ thr : ℝ, ∀ (P : ProvParams) (Mn : SuccMenu), Mn.p = A.pT → thr ≤ P.C →
      Nonempty (MenuLedgerBudget kW P Mn Cu 1 (termNMax A) A.dW κc A.bw A.Dt)

/-- **The budget of the first source.** The scale hypotheses are those of
`TermScaleConsts.diag`; one threshold on `C_w`. -/
def TermDiagBudgetStmt : Prop :=
  ∀ (X : TermConstruction) (A : TermArgs X) (kW : InvConsts) (Cu Ca Cown Cd : ℝ) (κc : MajConsts),
    MajOK A.bw κc → 0 < A.bw → 1 ≤ Cu → 0 ≤ Ca → 0 ≤ Cown →
    ∃ thr : ℝ, ∀ (D : OCData) (j₀ : ℕ) (Gw : GenStage D ScalarH A.Dt A.bw j₀) (P : ProvParams)
      (Mn : SuccMenu), Mn.N = A.NT → Mn.p = A.pT → 0 < Mn.lenFactor → Mn.lenFactor ≤ 1 →
      ownSize D Gw.level ≤ 1 / 100 →
      ocA D.α D.q D.Λ (Gw.level - 1) * (Mn.lenFactor ^ 2 * ocTauPP D.α D.q D.Λ Gw.level) ≤
        Ca * D.eps (Gw.level - 1) ^ ocDelta D.α D.q →
      ownSize D Gw.level ≤ Cown * D.eps (Gw.level - 1) ^ ocDelta D.α D.q →
      D.eps Gw.level ^ (1 + D.α) ≤ Cd * Real.sqrt (D.kap Gw.level * D.kap (Gw.level - 1)) →
      thr ≤ P.C → Nonempty (MenuDiagBudget kW Gw P Mn Cu 1 κc)

/-- **The chain environment** of a carrier pair (`velC_spec`). -/
def TermChainEnvStmt : Prop :=
  ∀ X : TermConstruction, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ A : TermArgs X, Λ₀ ≤ A.Λ → 0 < A.bw →
    A.bw ≤ 1 / 10000 → ∀ (CH Υ : ℝ) (j₀ : ℕ), 1 ≤ CH → 1 ≤ Υ →
    IsCarrierStart X.α X.q A.Λ A.bw CH Υ j₀ → ∀ (M : ℕ) (D : OCData), IsTermData X A.Λ M D →
      ChainEnv D A.bw CH Υ j₀

/-! ### The compiled construction of the bundle -/

/-- **The bundle `MenuFacts` at the terminal menu**, from its parts. -/
theorem termMenuFacts_of_parts {X : TermConstruction} {A : TermArgs X} {sXT sZT : ℕ}
    {kW : InvConsts} {cr Cu : ℝ} {M : ℕ} {D : OCData} {j₀ : ℕ}
    {Gw Gt' : GenStage D ScalarH A.Dt A.bw j₀} {Cw tp : ℝ}
    (hstep : StepFacts kW Gw Gt' (A.Pt D Cw cr M) Cu) (hsc : TermScaleConsts A cr Cu)
    (hdata : IsTermData X A.Λ M D) (hM : 2 ≤ M) (hlev : Gw.level = M)
    (hf : TermMenuFields A sXT sZT kW M D Gw (A.Pt D Cw cr M) (A.Mt M sXT sZT tp cr)) :
    MenuFacts kW Gw Gt' (A.Pt D Cw cr M) (A.Mt M sXT sZT tp cr) Cu 1 (termNMax A) A.dW 0 where
  stage := hstep
  alphabet := hf.alphabet
  degree := hf.degree
  degree_cap := hf.degree_cap
  order_cap := hf.order_cap
  reserveX := hf.reserveX
  reserveZ := hf.reserveZ
  diagonal_reserveX := hf.diagonal_reserveX
  diagonal_reserveZ := hf.diagonal_reserveZ
  depth := hf.depth
  weight := hf.weight
  radius_pos := hf.radius_pos
  radius_le := hf.radius_le
  record_pos := one_pos
  record_le := le_rfl
  tag_degree := hf.tag_degree
  tag_covariance := hf.tag_covariance
  tag_epsilon := hf.tag_epsilon
  tag_delta := hf.tag_delta
  tag_eta := hf.tag_eta
  tag_inflation := hf.tag_inflation
  tag_length := hf.tag_length
  displacement := by
    rw [hlev]
    exact hsc.displacement M D hdata hM
  covariance := by
    rw [hlev]
    exact fun t i j => hsc.covariance M D hdata hM tp t i j
  covariance_cost := by
    rw [hlev]
    exact fun t i j => hsc.covariance_cost M D hdata hM tp t i j

/-- **The ledger of the terminal successor, from the generic ledger and the parts.** -/
theorem terminal_ledger_concl {X : TermConstruction} {A : TermArgs X} {sXT sZT : ℕ}
    {kW : InvConsts} {κc : MajConsts} {cr Cu : ℝ} {M : ℕ} {D : OCData} {j₀ : ℕ}
    {Gw Gt' : GenStage D ScalarH A.Dt A.bw j₀} {Cw tp CH Υ : ℝ}
    (hF : MenuFacts kW Gw Gt' (A.Pt D Cw cr M) (A.Mt M sXT sZT tp cr) Cu 1 (termNMax A) A.dW 0)
    (hB : Nonempty (MenuLedgerBudget kW (A.Pt D Cw cr M) (A.Mt M sXT sZT tp cr) Cu 1
      (termNMax A) A.dW κc A.bw A.Dt))
    (hBd : Nonempty (MenuDiagBudget kW Gw (A.Pt D Cw cr M) (A.Mt M sXT sZT tp cr) Cu 1 κc))
    (hE : ChainEnv D A.bw CH Υ j₀) (hj : j₀ ≤ Gt'.level)
    (hSucc : IsActualSuccessor D (A.Pt D Cw cr M) (A.Mt M sXT sZT tp cr) Gw Gt') :
    ∀ (v' u' : CompIn Gt'.comps) (γ' : Gt'.fam.Γ v' u'), 0 ≤ compReserve kW v'.1 →
      LedgerConcl kW κc Gt' v' u' γ' := by
  obtain ⟨B⟩ := hB
  obtain ⟨Bd⟩ := hBd
  exact fun v' u' γ' hres => ledger_all_menu kW κc Gw Gt' _ _ Cu 1 (termNMax A) A.dW 0 hF B Bd CH Υ hE hj hSucc v' u' γ' hres

end AVRegularity.EntryTerminal.Route
end
end

section
/-! **The chain environment of the terminal passage** (`TermChainEnvStmt`), from
`ComplexFlow.velC_spec` exactly as in the cascade instance of the ledger.

Degenerate case: `Λ₀ = 128`; the carrier pair is only used through `1 ≤ CH`, `1 ≤ Υ`. -/

@[expose] public noncomputable section

open Homogenization AVRegularity AVRegularity.Sobolev

namespace AVRegularity.EntryTerminal.Route

open AVRegularity.Providers.ComplexFlow

theorem termChainEnv_stmt : TermChainEnvStmt := by
  intro X
  refine ⟨128, le_rfl, fun A hΛ hb0 hb1 CH Υ j₀ hCH hΥ hcs M D hD => ?_⟩
  obtain ⟨hα, hq, hΛD, hζ, hΦ, -, -⟩ := hD
  have hvel := velC_spec X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq hΛ X.hζ hΦ
  cases D
  dsimp only at hα hq hΛD hζ ⊢
  subst hα hq hΛD hζ
  exact
    { hq := X.hq.1
      hΛ := hΛ
      hα := X.hα₁
      hζ := X.hζ
      hvel := fun m => (hvel m).1
      hag := fun m t x => (hvel m).2 t x
      hb0 := hb0
      hb1 := hb1
      hCH := hCH
      hΥ := hΥ
      hcs := hcs }

end AVRegularity.EntryTerminal.Route
end
end
end

section
section
/-! **The two budgets of the terminal passage** (`TermLedgerBudgetStmt`,
`TermDiagBudgetStmt`), as in the cascade instance (`successor_ledger`): the reserve step
`Δ = 1/((H_prod + 1)(D + 4 n + 10 p + 1))` for the path sources, `Δ_D = 1/(fsR + 1)` for the first
source, the constants of `exists_ledgerConsts`, `exists_diagConsts`, and the thresholds `ledgerThr`,
`diagThr` as the thresholds on `C_w`. They read `A.pT`, `A.NT`, `A.Dt`, `d_W`, `n_max`, `k_W`,
`κ_c`, `C_u`, never the level, the datum or the stage.

The premise `1 ≤ p_T` is not used, so `p_T = 0` is included; for `d_W = 0`, `fluxMax` sums over
`h ≤ 0`. -/

@[expose] public noncomputable section

open Homogenization AVRegularity AVRegularity.Sobolev
open scoped NNReal

namespace AVRegularity.EntryTerminal.Route

open AVRegularity.Providers.CascadeInvariants AVRegularity.Providers.CascadeInvariants.Menu AVRegularity.Providers.Majorant
  AVRegularity.Providers.GenSem AVRegularity.Providers.ComplexContext

theorem termLedgerBudget_stmt : TermLedgerBudgetStmt := by
  intro X A kW Cu κc hκ hb hCu
  have hH0 : (0 : ℝ) < (kW.Hprod : ℝ) + 1 := by positivity
  have hX0 : (0 : ℝ) < ((A.Dt + (4 * termNMax A + 10 * A.pT) + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos _
  obtain ⟨Δ, hΔdef⟩ : ∃ Δ : ℝ, Δ = 1 / (((kW.Hprod : ℝ) + 1) *
      ((A.Dt + (4 * termNMax A + 10 * A.pT) + 1 : ℕ) : ℝ)) := ⟨_, rfl⟩
  have hΔ : 0 < Δ := by rw [hΔdef]; positivity
  have hΔD : (A.Dt : ℝ) * Δ ≤ 1 / ((kW.Hprod : ℝ) + 1) := by
    rw [hΔdef]
    exact step_mul_le hH0 hX0 (by exact_mod_cast (by omega))
  have hΔR : ((4 * termNMax A + 10 * A.pT : ℕ) : ℝ) * Δ ≤ 1 / ((kW.Hprod : ℝ) + 1) := by
    rw [hΔdef]
    exact step_mul_le hH0 hX0 (by exact_mod_cast (by omega))
  obtain ⟨ar, K, W, Cold, Wr, S, Kg, Kd, hC⟩ := exists_ledgerConsts hb hκ A.Dt kW.Lstar hΔ
  refine ⟨ledgerThr A.Dt A.dW (termNMax A) A.pT K W Cold Wr Δ 1 Cu
    (fluxMax κc S Kg Kd A.Dt A.dW (termNMax A)) (covKMax S Kg (termNMax A) A.pT), ?_⟩
  intro P Mn hp hthr
  refine ⟨⟨ar, Δ, K, W, Cold, Wr, S, Kg, Kd, hC, hΔD, ?_, ?_⟩⟩
  · rw [hp]; exact hΔR
  · rw [hp]; exact hthr

theorem termDiagBudget_stmt : TermDiagBudgetStmt := by
  intro X A kW Cu Ca Cown Cd κc hκ hb hCu hCa hCown
  have hΔD0 : (0 : ℝ) < 1 / ((fsR A.NT A.pT (2 * A.NT + 1) : ℝ) + 1) := by positivity
  obtain ⟨aD, a₀D, L₀, sD, Wg, Wc, Wl, KgD, KdD, SD, WrD, ColdD, CslowD, hCD⟩ :=
    exists_diagConsts hb hκ kW.Lstar A.NT A.pT hΔD0
  have hΔfs : ((fsR A.NT A.pT (2 * A.NT + 1) : ℕ) : ℝ) *
      (1 / ((fsR A.NT A.pT (2 * A.NT + 1) : ℝ) + 1)) ≤ 1 := by
    rw [mul_one_div, div_le_one (by positivity)]
    linarith
  refine ⟨diagThr (constCtx κc SD KgD KdD) A.Dt A.NT A.pT sD Wg Wl Wc Cu Ca Cd Cown WrD 1, ?_⟩
  intro D j₀ Gw P Mn hN hp hl0 hl1 hsmall hamp hown hdrift hthr
  refine ⟨⟨Ca, Cown, Cd, 1 / ((fsR A.NT A.pT (2 * A.NT + 1) : ℝ) + 1), aD, a₀D, L₀, sD, Wg, Wc, Wl, KgD, KdD, SD, WrD, ColdD, CslowD,
    hsmall, hCa, hCown, hamp, hown, hdrift, ?_, ?_, ?_⟩⟩
  · rw [hN, hp]; exact hCD
  · rw [hN, hp]; exact hΔfs
  · rw [hN, hp]; exact hthr

end AVRegularity.EntryTerminal.Route
end
end

section
/-! **The scale constant of the terminal passage** (`TermScaleConstsStmt`).

`Cu = 1 + C₁/c_r + 2 C₂/c_r²`, with `C₁` the constant of `exists_passScales` and `C₂` the constant
of the fourth estimate of `bandChain_covariance_estimates` (`|𝖧|/ρ² ≤ C₂ ε^δ`, `ρ = ocRh`); the
first-source constants are those of `exists_diagScales` and `ComplexContext.drift_scale_bound`.

Degenerate case: `c_r = 1` gives `Cu = 1 + C₁ + 2C₂`. -/

@[expose] public section

open Homogenization AVRegularity AVRegularity.Sobolev

namespace AVRegularity.EntryTerminal.Route

open AVRegularity.Providers.CascadeInvariants AVRegularity.Providers.ComplexContext

theorem termPassScales_mono {D : OCData} {m : ℕ} {C C' : ℝ} (h : PassScales D m C)
    (hC : C ≤ C') (hΛ : 1 ≤ D.Λ) : PassScales D m C' := by
  have hε : ∀ x : ℝ, 0 ≤ D.eps (m - 1) ^ x := fun x =>
    Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ).le _
  exact { h with
    hDρ := h.hDρ.trans (mul_le_mul_of_nonneg_right hC (hε _))
    hH := fun t i j => (h.hH t i j).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC (hε _)) (sq_nonneg _)) }

theorem ocA_nonneg_scales (D : OCData) (hΛ : 1 ≤ D.Λ) (m : ℕ) : 0 ≤ ocA D.α D.q D.Λ m := by
  unfold ocA
  exact Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ).le _

theorem termScaleConsts_stmt : TermScaleConstsStmt := by
  intro X
  obtain ⟨C1, hC1, Λ1, hΛ1, hps⟩ :=
    exists_passScales X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq X.hζ
  obtain ⟨C2, hC2, Λ2, hΛ2, hcov⟩ :=
    CycleReference.bandChain_covariance_estimates X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq X.hζ
  obtain ⟨Ca, hCa, Λ3, hΛ3, hds⟩ := exists_diagScales X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq X.hζ
  obtain ⟨Λ4, hΛ4, hdr⟩ := drift_scale_bound X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq X.hζ
  refine ⟨max Λ1 (max Λ2 (max Λ3 Λ4)), le_max_of_le_left hΛ1, fun A hA cr hcr0 hcr1 => ?_⟩
  have h1 : Λ1 ≤ A.Λ := (le_max_left _ _).trans hA
  have h2 : Λ2 ≤ A.Λ := ((le_max_left _ _).trans (le_max_right _ _)).trans hA
  have h3 : Λ3 ≤ A.Λ :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hA
  have h4 : Λ4 ≤ A.Λ :=
    (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans hA
  obtain ⟨Cd, hCd0, hCd⟩ := hdr A.Λ h4
  have hcr2 : 0 < cr ^ 2 := by positivity
  refine ⟨1 + C1 / cr + 2 * C2 / cr ^ 2, ?_⟩
  have hu1 : C1 / cr ≤ 1 + C1 / cr + 2 * C2 / cr ^ 2 := by
    have : 0 ≤ 2 * C2 / cr ^ 2 := by positivity
    linarith
  have hu2 : 2 * C2 / cr ^ 2 ≤ 1 + C1 / cr + 2 * C2 / cr ^ 2 := by
    have : 0 ≤ C1 / cr := by positivity
    linarith
  have hC1p : 0 ≤ C1 / cr := by positivity
  have hC2p : 0 ≤ 2 * C2 / cr ^ 2 := by positivity
  -- unpack the datum
  have key : ∀ (M : ℕ) (D : OCData), IsTermData X A.Λ M D → 2 ≤ M →
      1 ≤ D.Λ ∧ PassScales D M C1 ∧
      (∀ tp t (i j : Fin 2), |ocCovariance D.α D.q D.Λ D.ζ M (D.κ M) (D.κ (M - 1)) tp t i j| ≤
        C2 * D.eps (M - 1) ^ ocDelta D.α D.q * liftLength D M ^ 2) ∧
      (ocA D.α D.q D.Λ (M - 1) * ocTauPP D.α D.q D.Λ M ≤
          Ca * D.eps (M - 1) ^ ocDelta D.α D.q ∧
        ownSize D M ≤ AVRegularity.Providers.ComplexFlow.chainK * (6 / 5) * Ca *
          D.eps (M - 1) ^ ocDelta D.α D.q) ∧
      D.eps M ^ (1 + D.α) ≤ Cd * Real.sqrt (D.kap M * D.kap (M - 1)) := by
    intro M D hD hM
    have hD' := hD
    obtain ⟨hα, hq, hΛD, hζ, -, hκ, hterm⟩ := hD
    have hΛ1' : 1 ≤ A.Λ := by omega
    have hps' := hps D hα hq hζ (by rw [hΛD]; exact h1) (by rw [hΛD, hterm]; exact hκ) M hM
      hterm.symm.le
    have hds' := hds D hα hq hζ (by rw [hΛD]; exact h3) (by rw [hΛD, hterm]; exact hκ) M hM
      hterm.symm.le
    have hdr' := hCd M D.κ hκ M (by omega)
    have hcov' := hcov A.Λ h2 M (by omega) D.κ hκ M hM le_rfl
    have hρ := hps'.hρ0
    rcases D with ⟨α', q', Λ', ζ', Φ', hΦ', κ', t'⟩
    dsimp only at hα hq hΛD hζ hterm hps' hds' hρ hdr' hcov' hκ ⊢
    subst hα hq hΛD hζ hterm
    refine ⟨hΛ1', hps', fun tp t i j => ?_, hds', ?_⟩
    · have h := (hcov' tp t i j).2.2.2
      rw [div_le_iff₀ (by positivity)] at h
      exact h
    · exact hdr'
  have hC1le : C1 ≤ 1 + C1 / cr + 2 * C2 / cr ^ 2 := by
    have : C1 ≤ C1 / cr := by rw [le_div_iff₀ hcr0]; nlinarith
    linarith
  refine
    { hCu := by linarith
      hsc := fun M D hD hM => termPassScales_mono (key M D hD hM).2.1 hC1le (key M D hD hM).1
      displacement := fun M D hD hM => ?_
      covariance := fun M D hD hM tp t i j => ?_
      covariance_cost := fun M D hD hM tp t i j => ?_
      diag := ⟨Ca, AVRegularity.Providers.ComplexFlow.chainK * (6 / 5) * Ca, Cd, hCa,
        mul_nonneg (by unfold AVRegularity.Providers.ComplexFlow.chainK; norm_num) hCa,
        fun M D hD hM => ?_⟩ }
  · obtain ⟨hΛ, hP, -, -, -⟩ := key M D hD hM
    have hρ := hP.hρ0
    have hd := hP.hDρ
    rw [div_le_iff₀ hρ] at hd
    rw [div_le_iff₀ (mul_pos hcr0 hρ)]
    have hε : 0 ≤ D.eps (M - 1) ^ (3 * ocDelta D.α D.q) :=
      Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ).le _
    have hCu1 : C1 / cr ≤ 1 + C1 / cr + 2 * C2 / cr ^ 2 := hu1
    calc ocDStar D.q D.Λ M (D.kap M) (D.kap (M - 1))
        ≤ C1 * D.eps (M - 1) ^ (3 * ocDelta D.α D.q) * liftLength D M := hd
      _ = C1 / cr * D.eps (M - 1) ^ (3 * ocDelta D.α D.q) * (cr * liftLength D M) := by
          field_simp
      _ ≤ _ := by
          gcongr
  · obtain ⟨hΛ, hP, hc, -, -⟩ := key M D hD hM
    have hε : 0 ≤ D.eps (M - 1) ^ ocDelta D.α D.q :=
      Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ).le _
    calc _ ≤ C2 * D.eps (M - 1) ^ ocDelta D.α D.q * liftLength D M ^ 2 := hc tp t i j
      _ = 2 * C2 / cr ^ 2 / 2 * D.eps (M - 1) ^ ocDelta D.α D.q * (cr * liftLength D M) ^ 2 := by
          field_simp
      _ ≤ _ := by
          gcongr
          linarith
  · obtain ⟨hΛ, hP, hc, -, -⟩ := key M D hD hM
    have hε : 0 ≤ D.eps (M - 1) ^ ocDelta D.α D.q :=
      Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos hΛ).le _
    have := hc 0 t i j
    have := hc 0 tp i j
    calc _ ≤ C2 * D.eps (M - 1) ^ ocDelta D.α D.q * liftLength D M ^ 2 +
          C2 * D.eps (M - 1) ^ ocDelta D.α D.q * liftLength D M ^ 2 := by linarith
      _ = 2 * C2 / cr ^ 2 * D.eps (M - 1) ^ ocDelta D.α D.q * (cr * liftLength D M) ^ 2 := by
          field_simp
          ring
      _ ≤ _ := by
          gcongr
  · obtain ⟨hΛ, -, -, ⟨ha, ho⟩, hdd⟩ := key M D hD hM
    refine ⟨?_, ho, hdd⟩
    have hA := ocA_nonneg_scales D hΛ (M - 1)
    have hτ := (Construction.Stream.ocTauPP_pos (α := D.α) (q := D.q) (m := M) hΛ).le
    calc ocA D.α D.q D.Λ (M - 1) * (cr ^ 2 * ocTauPP D.α D.q D.Λ M)
        = cr ^ 2 * (ocA D.α D.q D.Λ (M - 1) * ocTauPP D.α D.q D.Λ M) := by ring
      _ ≤ 1 * (ocA D.α D.q D.Λ (M - 1) * ocTauPP D.α D.q D.Λ M) := by
          gcongr
          nlinarith
      _ ≤ _ := by rw [one_mul]; exact ha

end AVRegularity.EntryTerminal.Route
end
end

section
/-! **The standing facts of the passage from `Gw` to `Gt'`** (`TermStepFactsStmt`), from
`IsWeakStage` and `IsActualSuccessor`, as in `terminalSuccessor_generation`: the certificate, the
transversality and generation of `Gw` and the uniqueness of the denotations of its exports come
from the stage invariant and `HasCertifiedExports` (whose third component is `AgreeOn .ctx`);
`hGT` holds because the identities of `Gw` have seed provenance, whose tags do not read the
parameters; all grades are `0` (`births = []`); `hlen` uses the level floor
`C_L ε_{M+1} ≤ ε_M` (`eps_floor`), which is the `M₀`.

Degenerate cases: a weak stage without identities (`hgrade`, `hlen` vacuous); `C_L ≤ 0`. -/

@[expose] public section

open Homogenization AVRegularity AVRegularity.Sobolev

namespace AVRegularity.EntryTerminal.Route

open AVRegularity.Providers.CascadeInvariants AVRegularity.Providers.GenSem

theorem termStepFacts_stmt : TermStepFactsStmt := by
  intro X A sXT sZT nW cr kW hP CL Cχ Cu CH Υ j₀ hsc hCH hΥ hcs
  obtain ⟨M₁, hM₁⟩ := eps_floor X.hq.1 hP.hΛ CL
  refine ⟨max M₁ 2, fun M hM cP CP cH Cw D a lawW PW Gw aM tp lawT Gt' hctx => ?_⟩
  obtain ⟨hdata, hw, -, -, -, -, hSucc⟩ := hctx
  have hM1 : M₁ ≤ M := (le_max_left _ _).trans hM
  have hM2 : 2 ≤ M := (le_max_right _ _).trans hM
  obtain ⟨eα, eq', eΛ, eζ, hΦ', hκ, eterm⟩ := hdata
  obtain ⟨-, -, hlev, -, hbirth, ⟨hprov, hexpw, -⟩, hid, -, -, hinv⟩ := hw
  obtain ⟨-, hGT, hG, -, hT, hcert, -⟩ := hinv
  have hcs' : IsCarrierStart D.α D.q D.Λ A.bw CH Υ j₀ := by rw [eα, eq', eΛ]; exact hcs
  have hΛD : 128 ≤ D.Λ := by rw [eΛ]; exact hP.hΛ
  have hq1 : 1 < D.q := by rw [eq']; exact X.hq.1
  have hb : 0 < A.bw := hP.valid.2.2.1.1
  have hsucc1 := hSucc.1
  have hsucc2 := hSucc.2.1
  exact
    { hζ := by rw [eζ]; exact X.hζ
      hΛ := hΛD
      hq := hq1
      hb := hb
      hκb := by rw [eα, eq', eΛ, eζ, eterm]; exact hκ
      hstart := startBound_of_carrierStart (by omega) hCH hΥ hcs'
      hcert := hcert
      hT := hT
      hGen := hG
      hexpU := fun e he f f' hf hf' => (hexpw.1 _ _ e he).2.2 f f' hf hf'
      hexp := fun e he => (hSucc.2.2.2.2.2.1 _ _ e).mpr he
      hlev := by omega
      hGT := by
        intro v u γ
        obtain ⟨k, tag, h⟩ := hprov v u γ
        have := hGT v u γ
        rw [h] at this ⊢
        exact this
      hGT' := hSucc.2.2.2.2.1
      hgrade := fun v u γ => by simp [compGrade, hbirth v, hbirth u]
      hlen := fun v u γ _ => by
        refine (hid v u γ).2.2.1.trans ?_
        have := hM₁ M hM1
        rw [hlev]
        show CL * ocEpsilon D.q D.Λ (M + 1) ≤ ocEpsilon D.q D.Λ M
        rw [eq', eΛ]
        exact this
      hsc := by rw [hlev]; exact hsc.hsc M D ⟨eα, eq', eΛ, eζ, hΦ', hκ, eterm⟩ hM2
      hCu := hsc.hCu
      hδ := by rw [eα, eq']; exact ocDelta_pos_of_admissible X.hα₀ X.hq }

end AVRegularity.EntryTerminal.Route
end
end

section
/-! **The menu fields, part 1: the order, alphabet and weight fields of the terminal menu.**

* `termAlphabet_eq_succAlphabet_termNMax`: the terminal alphabet is `succAlphabet (termNMax A) …`;
* `termNMax_add_le_Dt`: `nMax + 4 p_T ≤ D̄₀` (the covariance letter of order `N_T + D_W + 4p_T` for
  `d_W, p_T ≥ 1`, the mean letter for `p_T = 0`, the diagonal letter for `d_W = 0`);
* `termWeight_le`: `liftWt D̄₀ d_W nMax ≤ kS.Lstar` from the fast-weight clause of `IsSeedAllocation`.

Degenerate cases: `d_W = 0`; `p_T = 0`. -/

@[expose] public section

open Homogenization AVRegularity AVRegularity.Sobolev

namespace AVRegularity.EntryTerminal.Route

theorem termNMax_le {X : TermConstruction} (A : TermArgs X) (hDW : 1 ≤ A.DW) :
    termNMax A ≤ A.NT + A.DW := by
  unfold termNMax; split_ifs <;> omega

theorem termAlphabet_eq_succAlphabet_termNMax {X : TermConstruction} (A : TermArgs X) :
    A.alph = succAlphabet (termNMax A) A.dW A.pT 0 := by
  unfold TermArgs.alph termAlphabet termNMax
  by_cases h : A.dW = 0
  · simp [h, succAlphabet]
  · simp [h]

theorem succAlphabet_diag_mem (n h p k : ℕ) : WordLetter.diag ∈ succAlphabet n h p k := by
  simp [succAlphabet]

theorem succAlphabet_mean_mem {n h p k nn hh : ℕ} (h3 : 3 ≤ nn) (hn : nn ≤ n) (h1 : 1 ≤ hh)
    (hh' : hh ≤ h) : WordLetter.mean nn hh ∈ succAlphabet n h p k := by
  unfold succAlphabet
  refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
    (Finset.mem_image.mpr ⟨(nn, hh), ?_, rfl⟩)))
  simp only [Finset.mem_product, Finset.mem_Icc]
  exact ⟨⟨h3, hn⟩, h1, hh'⟩

theorem succAlphabet_cov_mem {n h p k nn hh a a' : ℕ} (h2 : 2 ≤ nn) (hn : nn ≤ n) (h1 : 1 ≤ hh)
    (hh' : hh ≤ h) (ha : a ≤ p) (ha' : a' ≤ p) (haa : 1 ≤ a + a') :
    WordLetter.covariance nn hh a a' ∈ succAlphabet n h p k := by
  unfold succAlphabet
  refine Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr
    ⟨((nn, hh), (a, a')), Finset.mem_filter.mpr ⟨?_, haa⟩, rfl⟩))
  simp only [Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
  exact ⟨⟨⟨h2, hn⟩, h1, hh'⟩, by omega, by omega⟩

theorem termNMax_add_le_Dt {X : TermConstruction} (A : TermArgs X) (hA : A.Valid) :
    termNMax A + 4 * A.pT ≤ A.Dt := by
  have hN := AVRegularity.EntryTerminal.Ingredients.two_le_NT_of_valid A hA
  have hDW : 1 ≤ A.DW := hA.2.2.2.2.2.2.2.2
  have hsup : ∀ l ∈ termAlphabet A.NT A.pT A.DW A.dW, letterOrder A.NT A.pT l ≤ A.Dt := fun l hl =>
    ((Finset.le_sup (f := letterOrder A.NT A.pT) hl)).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  unfold termNMax
  by_cases h0 : A.dW = 0
  · have := hsup .diag (succAlphabet_diag_mem _ _ _ _)
    simp only [letterOrder] at this
    simp [h0]; omega
  · simp only [h0, ite_false]
    by_cases hp : A.pT = 0
    · have := hsup (.mean (A.NT + A.DW) 1)
        (succAlphabet_mean_mem (by omega) le_rfl le_rfl (by omega))
      simp only [letterOrder] at this
      rw [hp]; omega
    · have := hsup (.covariance (A.NT + A.DW) 1 A.pT A.pT)
        (succAlphabet_cov_mem (by omega) le_rfl le_rfl (by omega) le_rfl le_rfl (by omega))
      simp only [letterOrder] at this
      omega

end AVRegularity.EntryTerminal.Route
end
end

section
/-! **The menu fields, part 2: the weight floor** `liftWt D̄₀ d_W n_max ≤ k_W.Lstar`:
from the fast-weight clause `succLstar K_res G₀ H J N p ≤ k_S.Lstar` of `IsSeedAllocation`
(in `SeedPlan`), its schedule clauses at `g = H + 1`, `r̄₀ ≥ d_W`, `n_max ≤ D̄₀`, and
`k_S.Lstar ≤ k_W.Lstar` (`IsWeakAllocation`).

Degenerate case: `d_W = 0` (then `liftWt = n_max ≤ D̄₀`). -/

@[expose] public section

open Homogenization AVRegularity AVRegularity.Sobolev

namespace AVRegularity.EntryTerminal.Route

open AVRegularity.Providers.GenSem

theorem succSchedR_ge (r J : ℕ) : ∀ g, r ≤ succSchedR r J g
  | 0 => le_rfl
  | g + 1 => by
      have := succSchedR_ge r J g
      show r ≤ (J + 2) * (succSchedR r J g + 1) - 1
      have h : succSchedR r J g + 1 ≤ (J + 2) * (succSchedR r J g + 1) :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega

theorem succSchedD_ge (D₀ N p : ℕ) : ∀ g, D₀ ≤ succSchedD D₀ N p g
  | 0 => le_rfl
  | g + 1 => by
      have := succSchedD_ge D₀ N p g
      show D₀ ≤ succSchedD D₀ N p g + 2 * N + 4 * p + 4
      omega

theorem termWeight_arith (n dW Dt R Dd X K : ℕ) (hn : n ≤ Dt) (hR : dW ≤ R) (hD : Dt ≤ Dd) :
    UEnv.liftWt Dt dW n ≤ K + (R + 1) * (X + Dd + 2) * (Dd + 2) := by
  unfold UEnv.liftWt
  have h1 : n + dW * (Dt + 1) ≤ (dW + 1) * (Dt + 2) := by nlinarith
  have h2 : (dW + 1) * (Dt + 2) ≤ (R + 1) * (Dd + 2) := Nat.mul_le_mul (by omega) (by omega)
  have h3 : (R + 1) * (Dd + 2) ≤ (R + 1) * (X + Dd + 2) * (Dd + 2) := by
    have : 1 ≤ X + Dd + 2 := by omega
    calc (R + 1) * (Dd + 2) ≤ (R + 1) * (Dd + 2) * (X + Dd + 2) := Nat.le_mul_of_pos_right _ (by omega)
      _ = (R + 1) * (X + Dd + 2) * (Dd + 2) := by ring
  omega

theorem termR0bar_ge (RT dW : ℕ) : dW ≤ termR0bar RT dW := by
  unfold termR0bar
  refine le_trans ?_ (le_max_right _ _)
  have : 2 * (dW + 1) ≤ (RT + 2) * (dW + 1) := Nat.mul_le_mul_right _ (by omega)
  omega

theorem termWeight_le {X : TermConstruction} {A : TermArgs X} {nW : ℕ+} {cr : ℝ}
    {kS kW : InvConsts} {Lt KS : ℕ} {F : SeedFloors} (hvalid : A.Valid)
    (hplan : SeedPlan A KS F Lt nW cr kS) (halloc : IsWeakAllocation kW kS Lt) :
    UEnv.liftWt A.Dt A.dW (termNMax A) ≤ kW.Lstar := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hsa, -⟩ := hplan
  obtain ⟨-, -, -, -, -, hL, hR, hDD, -, -, -⟩ := hsa
  obtain ⟨-, -, -, -, hLst, -⟩ := halloc
  have hcap := termNMax_add_le_Dt A hvalid
  have hR1 := hR (A.H + 1)
  have hD1 := hDD (A.H + 1)
  have e : kS.G0 + (A.H + 1) = kS.G0 + A.H + 1 := by omega
  rw [e] at hR1 hD1
  have hR2 : A.dW ≤ succSchedR 0 A.J (kS.G0 + A.H + 1) :=
    (termR0bar_ge A.RT A.dW).trans ((succSchedR_ge _ _ _).trans hR1)
  have hD2 : A.Dt ≤ succSchedD 2 A.N A.p (kS.G0 + A.H + 1) :=
    (succSchedD_ge _ _ _ _).trans hD1
  refine le_trans ?_ (hL.trans hLst)
  exact termWeight_arith _ _ _ _ _ (2 * A.N + 4) _ (by omega) hR2 hD2

end AVRegularity.EntryTerminal.Route

namespace AVRegularity.EntryTerminal.Route

/-- The seed-side corollary: the hypotheses of `TermPlanHyp` from the seed plan and the weak
allocation (`IsSeedAllocation`: `succLstar` floor, `kS.Hprod = kS.G0 + H + 1`). -/
theorem termPlanHyp_of_plan {X : TermConstruction} {A : TermArgs X} {sXT sZT : ℕ} {nW : ℕ+}
    {cr : ℝ} {kS kW : InvConsts} {Lt KS : ℕ} {F : SeedFloors} (hvalid : A.Valid)
    (hΛ : 128 ≤ A.Λ) (hplan : SeedPlan A KS F Lt nW cr kS) (halloc : IsWeakAllocation kW kS Lt)
    (hsX : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sXT)
    (hsZ : max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 ≤ sZT) :
    TermPlanHyp A sXT sZT nW cr kW := by
  have hw := termWeight_le hvalid hplan halloc
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hsa, -⟩ := hplan
  obtain ⟨-, -, -, -, -, -, -, -, hHp, -, -⟩ := hsa
  obtain ⟨-, -, -, -, -, hG0, hH, -⟩ := halloc
  exact ⟨hvalid, hΛ, hw, by omega, hsX, hsZ⟩

end AVRegularity.EntryTerminal.Route
end
end

section
/-! **The menu fields** (`TermMenuFieldsStmt`) at `termMenu`, `termProvParams`: the order,
alphabet and weight lemmas of the menu fields and of the weights, the reserves from `TermPlanHyp`,
the depth from `IsWeakStage`, and the tags by unfolding
(`termRho c_r M = 1 · (c_r · liftLength D M)`).

Degenerate cases: `d_W = 0`; `c_r = 1`. -/

@[expose] public section

open Homogenization AVRegularity AVRegularity.Sobolev

namespace AVRegularity.EntryTerminal.Route

theorem termMenuFields_stmt : TermMenuFieldsStmt := by
  intro X A sXT sZT nW cr kW hP CL Cχ j₀ M hM cP CP cH Cw D a lawW PW Gw aM tp lawT Gt'
    hctx hcr0 hcr1
  obtain ⟨hdata, hw, -⟩ := hctx
  obtain ⟨-, -, hlev, hdep, -, -, -, -, -, -⟩ := hw
  have hN := AVRegularity.EntryTerminal.Ingredients.two_le_NT_of_valid A hP.valid
  have hDW : 1 ≤ A.DW := hP.valid.2.2.2.2.2.2.2.2
  have hle := termNMax_le A hDW
  have hX := hP.hsX
  have hZ := hP.hsZ
  have hnm : A.NT ≤ termNMax A := by unfold termNMax; split_ifs <;> omega
  refine
    { alphabet := termAlphabet_eq_succAlphabet_termNMax A
      degree := hN
      degree_cap := hnm
      order_cap := fun l hl =>
        ((Finset.le_sup (f := letterOrder A.NT A.pT) hl)).trans
          ((le_max_right _ _).trans (le_max_right _ _))
      reserveX := ?_
      reserveZ := ?_
      diagonal_reserveX := ?_
      diagonal_reserveZ := ?_
      depth := hdep
      weight := hP.hLstar
      radius_pos := hcr0
      radius_le := hcr1
      tag_degree := rfl
      tag_covariance := rfl
      tag_epsilon := rfl
      tag_delta := rfl
      tag_eta := rfl
      tag_inflation := rfl
      tag_length := ?_ }
  · show max (termNMax A) (2 * A.pT) + A.Dt + 2 ≤ sXT
    omega
  · show max (termNMax A) (2 * A.pT) + A.Dt + 2 ≤ sZT
    omega
  · show max (A.NT + 1) (2 * A.pT) + A.Dt + 2 ≤ sXT
    omega
  · show max (A.NT + 1) (2 * A.pT) + A.Dt + 2 ≤ sZT
    omega
  · rw [hlev]
    simp [TermArgs.Pt, termProvParams, OCData.termRho, OCData.termB, OCData.termH, liftLength,
      TermArgs.Mt, termMenu]

end AVRegularity.EntryTerminal.Route
end
end
end
