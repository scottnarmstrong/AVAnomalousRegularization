-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.QuietAtlas.QuietPulse
public import AVRegularity.EntryTerminal.Assembly.Seed.RetainedGeneric
import AVRegularity.Proofs.QuietAtlas.Successor.QuietMatching
import AVRegularity.Proofs.QuietAtlas.Successor.StageHistory
import AVRegularity.EntryWeak.MolecularHilbertToRawSolution
import AVRegularity.Proofs.GenSem.SuccessorGeneration.Terminal
import AVRegularity.CycleReference.FluxFastDiscrepancy
import Mathlib.Algebra.Order.Star.Real

section
section
/-! **The quiet-matching clause passes to a restriction** (E5, `SeedQuietPart`, step 2). A
restriction of a stage keeps its pieces, weights, actual contexts and level, and its identities and
fluxes are those of the kept components. The atlas of the stage is an atlas of the restriction, and
every clause of `QuietMatchingOn` (consecutive closure, quiet cover, quiet transitions, actual
contexts, transversality, fast independence) is the clause of the stage at the kept components.

Special cases:
- The restriction to all components: the clause itself.
- The restriction to no component: the identity clauses are vacuous; the atlas clauses remain.
- The retained family `G'.retained m H J` (a restriction). -/

@[expose] public noncomputable section

open Homogenization

namespace AVRegularity.EntryTerminal.Ingredients

open AVRegularity.Providers.QuietAtlas

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The atlas of a stage as an atlas of a restriction (the pieces are the same). -/
def restrictAtlas (G : GenStage D hr Dm b j₀) (S' : Finset Comp) (hS : S' ⊆ G.comps)
    (T : G.fam.Atlas) : (G.restrict S' hS).fam.Atlas :=
  ⟨T.adjacent, T.tr, T.sameCtx⟩

/-- **Step 2**: the quiet-matching clause of a stage holds for every restriction. -/
theorem quietMatchingOn_restrict (G : GenStage D hr Dm b j₀) (S' : Finset Comp)
    (hS : S' ⊆ G.comps) (S W : Set ℝ) (h : QuietMatchingOn G S W) :
    QuietMatchingOn (G.restrict S' hS) S W := by
  obtain ⟨⟨T, hcons, hcov, hq, hact, hctx⟩, htrans, hfast⟩ := h
  refine ⟨⟨restrictAtlas G S' hS T, hcons, hcov, ?_, hact, hctx⟩, ?_, ?_⟩
  · intro p q hpq c c' hcc
    obtain ⟨h1, h2⟩ := hq p q hpq c c' hcc
    exact ⟨fun tY htY v u γ d I z z' => h1 tY htY _ _ γ d I z z',
      fun tY htY z v u γ r A => h2 tY htY z _ _ γ r A⟩
  · exact fun k p c v u γ d I => htrans k p c _ _ γ d I
  · exact fun p c v u γ d I => hfast p c _ _ γ d I

/-- The clause for the retained part of a stage. -/
theorem quietMatchingOn_retained (G : GenStage D hr Dm b j₀) (m H J : ℕ) (S W : Set ℝ)
    (h : QuietMatchingOn G S W) : QuietMatchingOn (G.retained m H J) S W :=
  quietMatchingOn_restrict G _ _ S W h

end AVRegularity.EntryTerminal.Ingredients
end
end

section
/-! **The quiet-matching clause passes along an encoding** (E5, `SeedQuietPart`, step 3). Let a
stage `G₂` (the seed) encode a stage `G₁` (the retained terminal family): equal levels, pieces and
actual chains; a bijection `ι` of the components and bijections `e` of the identities, with equal
maximal orders and equal fluxes at contexts with equal chains. The atlas of `G₁` transports to `G₂`
(the transitions are those of `G₁`, read between the equal pieces; contexts are compared through
their chains), and every clause of `QuietMatchingOn` transports.

Special cases:
- `G₂ = G₁`, `ι = e = id`: the clause itself.
- No components: the identity clauses are vacuous; the atlas clauses transport through the pieces.
- Different maximal orders of the families (`D₁ ≠ D₂`): the clause does not see them. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity.EntryTerminal.Ingredients

open AVRegularity.Providers.QuietAtlas

/-- A chart transition between equal pieces. -/
def chartTransitionCongr {p q p' q' : ChartPiece} (hp : p' = p) (hq : q' = q)
    (tr : ChartTransition p q) : ChartTransition p' q' where
  Υ := tr.Υ
  smooth := tr.smooth
  det_one := tr.det_one
  compat := by
    subst hp hq
    exact tr.compat
  overlap := tr.overlap

/-- A context of one level as a context of an equal level (the same chain). -/
def stageCtxCast {D : OCData} {b : ℝ} {j₀ i i' : ℕ} (hi : i = i') {p : OddSlot}
    (c : StageCtx D b j₀ i p) : StageCtx D b j₀ i' p :=
  ⟨c.1, hi ▸ c.2⟩

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {D₁ D₂ : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The atlas of `G₁` read on `G₂`. -/
def encodedAtlas (G₁ : GenStage D hr D₁ b j₀) (G₂ : GenStage D hr D₂ b j₀)
    (hlev : G₂.level = G₁.level) (hpiece : ∀ p, G₂.fam.piece p = G₁.fam.piece p)
    (T : G₁.fam.Atlas) : G₂.fam.Atlas where
  adjacent := T.adjacent
  tr := fun p q hpq => chartTransitionCongr (hpiece p) (hpiece q) (T.tr p q hpq)
  sameCtx := fun p q hpq c c' => T.sameCtx p q hpq (stageCtxCast hlev c) (stageCtxCast hlev c')

/-- The fluxes of an encoded identity, as functions. -/
theorem encoded_flux_eq (G₁ : GenStage D hr D₁ b j₀) (G₂ : GenStage D hr D₂ b j₀)
    (hlev : G₂.level = G₁.level) (ι : CompIn G₁.comps ≃ CompIn G₂.comps)
    (e : ∀ v u, G₁.fam.Γ v u ≃ G₂.fam.Γ (ι v) (ι u))
    (hflux : ∀ v u (γ : G₁.fam.Γ v u) (p : OddSlot) (c : StageCtx D b j₀ G₂.level p)
      (c' : StageCtx D b j₀ G₁.level p), c.1 = c'.1 → ∀ (d : ℕ) (I : DerivativeWord2 (d - 1))
      (t : ℝ) (X z : Vec 2), G₂.fam.flux p c (ι v) (ι u) (e v u γ) d I t X z =
        G₁.fam.flux p c' v u γ d I t X z)
    (v u : CompIn G₁.comps) (γ : G₁.fam.Γ v u) (p : OddSlot) (c : StageCtx D b j₀ G₂.level p)
    (d : ℕ) (I : DerivativeWord2 (d - 1)) :
    G₂.fam.flux p c (ι v) (ι u) (e v u γ) d I = G₁.fam.flux p (stageCtxCast hlev c) v u γ d I := by
  funext t X z
  exact hflux v u γ p c _ rfl d I t X z

/-- **Step 3**: the quiet-matching clause of `G₁` holds for an encoding `G₂` of it. -/
theorem quietMatchingOn_encoded (G₁ : GenStage D hr D₁ b j₀) (G₂ : GenStage D hr D₂ b j₀)
    (hlev : G₂.level = G₁.level) (hpiece : ∀ p, G₂.fam.piece p = G₁.fam.piece p)
    (hact : ∀ p, (G₂.actual p).1 = (G₁.actual p).1)
    (ι : CompIn G₁.comps ≃ CompIn G₂.comps) (e : ∀ v u, G₁.fam.Γ v u ≃ G₂.fam.Γ (ι v) (ι u))
    (hmax : ∀ v u (γ : G₁.fam.Γ v u),
      (G₂.fam.identity (ι v) (ι u) (e v u γ)).maxOrder = (G₁.fam.identity v u γ).maxOrder)
    (hflux : ∀ v u (γ : G₁.fam.Γ v u) (p : OddSlot) (c : StageCtx D b j₀ G₂.level p)
      (c' : StageCtx D b j₀ G₁.level p), c.1 = c'.1 → ∀ (d : ℕ) (I : DerivativeWord2 (d - 1))
      (t : ℝ) (X z : Vec 2), G₂.fam.flux p c (ι v) (ι u) (e v u γ) d I t X z =
        G₁.fam.flux p c' v u γ d I t X z)
    (S W : Set ℝ) (h : QuietMatchingOn G₁ S W) : QuietMatchingOn G₂ S W := by
  obtain ⟨⟨T, hcons, hcov, hq, hactc, hctx⟩, htrans, hfast⟩ := h
  have hF := encoded_flux_eq G₁ G₂ hlev ι e hflux
  have hF' : ∀ v u (γ : G₁.fam.Γ v u) (p : OddSlot) (c : StageCtx D b j₀ G₂.level p) (d : ℕ)
      (I : DerivativeWord2 (d - 1)) (t : ℝ) (X z : Vec 2),
      G₂.fam.flux p c (ι v) (ι u) (e v u γ) d I t X z =
        G₁.fam.flux p (stageCtxCast hlev c) v u γ d I t X z :=
    fun v u γ p c d I t X z => hflux v u γ p c _ rfl d I t X z
  have hA : ∀ p, stageCtxCast hlev (G₂.actual p) = G₁.actual p := fun p => Subtype.ext (hact p)
  refine ⟨⟨encodedAtlas G₁ G₂ hlev hpiece T, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro p q hpq hlab hne
    rw [hpiece, hpiece] at hlab hne
    exact hcons p q hpq hlab hne
  · intro p q hpq t ht Y
    have hQ : ocQuietTimes D.α D.q D.Λ D.ζ G₂.level = ocQuietTimes D.α D.q D.Λ D.ζ G₁.level := by
      rw [hlev]
    rw [hQ, hpiece, hpiece] at ht
    exact hcov p q hpq t ht Y
  · intro p q hpq c c' hcc
    obtain ⟨h1, h2⟩ := hq p q hpq _ _ hcc
    have hk : D.kap G₂.level = D.kap G₁.level := congrArg D.kap hlev
    have he : D.eps G₂.level = D.eps G₁.level := congrArg D.eps hlev
    have hE : D.eps (G₂.level - 1) = D.eps (G₁.level - 1) := by rw [hlev]
    rw [hk, he, hE]
    refine ⟨fun tY htY v₂ u₂ γ₂ d I z z' => ?_, fun tY htY z v₂ u₂ γ₂ r A => ?_⟩
    · obtain ⟨v, rfl⟩ := ι.surjective v₂
      obtain ⟨u, rfl⟩ := ι.surjective u₂
      obtain ⟨γ, rfl⟩ := (e v u).surjective γ₂
      simp only [hF']
      exact h1 tY htY v u γ d I z z'
    · obtain ⟨v, rfl⟩ := ι.surjective v₂
      obtain ⟨u, rfl⟩ := ι.surjective u₂
      obtain ⟨γ, rfl⟩ := (e v u).surjective γ₂
      have h2' := h2 tY htY z v u γ r A
      simp only [ChartedFamily.dimFlux, ChartedFamily.slowFlux] at h2' ⊢
      simp only [hF', hmax v u γ]
      exact h2'
  · intro p q hpq hne
    rw [hpiece, hpiece] at hne
    show T.sameCtx p q hpq (stageCtxCast hlev (G₂.actual p)) (stageCtxCast hlev (G₂.actual q))
    rw [hA, hA]
    exact hactc p q hpq hne
  · intro p q hpq c c' hcc
    obtain ⟨h1, h2⟩ := hctx p q hpq _ _ hcc
    exact ⟨Subtype.ext ((congrArg Subtype.val h1).trans (hact p).symm),
      Subtype.ext ((congrArg Subtype.val h2).trans (hact q).symm)⟩
  · intro k p c v₂ u₂ γ₂ d I
    obtain ⟨v, rfl⟩ := ι.surjective v₂
    obtain ⟨u, rfl⟩ := ι.surjective u₂
    obtain ⟨γ, rfl⟩ := (e v u).surjective γ₂
    have hpulse : enlargedPulse D G₂.level W = enlargedPulse D G₁.level W := by rw [hlev]
    rw [hF v u γ p c, hpiece, hpulse]
    exact htrans k p _ v u γ d I
  · intro p c v₂ u₂ γ₂ d I
    obtain ⟨v, rfl⟩ := ι.surjective v₂
    obtain ⟨u, rfl⟩ := ι.surjective u₂
    obtain ⟨γ, rfl⟩ := (e v u).surjective γ₂
    rw [hF v u γ p c, hpiece]
    exact hfast p _ v u γ d I

end AVRegularity.EntryTerminal.Ingredients
end
end

section
/-! **The quiet structure of the terminal seed at one level, from the successor's clause**
(`SeedQuietPart`). The seed encodes the retained part `Π G'_T` of the actual terminal successor
(`IsSeedEncoding`: equal level, pieces and actual chains; bijections of components and identities
with equal maximal orders and fluxes). So the quiet-matching clause of `G'_T` on the window
`[t_p + h, a + T₀]`, with fast independence on the trimmed quiet times, passes to `Π G'_T` (step 2)
and then to the seed (step 3). With the carried history invariant of the seed (supplied by
the caller, `SeedQuiet/Successor.lean`), this is `SeedQuietAtM`.

Special cases:
- An empty retained family: the identity clauses are vacuous; the atlas clauses transport.
- A window inside one quiet interval: the atlas has the transitions of the successor there.
- The trimmed set of the seed's level is that of the successor's level (`seed.level = level`). -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity.EntryTerminal.Ingredients

open AVRegularity.Providers.QuietAtlas AVRegularity.EntryTerminal.Route

/-- **`SeedQuietAtM` from the quiet-matching clause of the terminal successor.** -/
theorem seedQuietAtM_of_successor_clause {X : TermConstruction} (A : TermArgs X) (sXT sZT : ℕ)
    (nW : ℕ+) (cr CL Cχ : ℝ) (kW : InvConsts) (cP CP cH Cw : ℝ) (j₀ M : ℕ)
    (h1 : ∀ (D : OCData) (a : ℝ) (lawW : BirthLaw) (PW : ProvParams)
      (Gw : GenStage D ScalarH A.Dt A.bw j₀) (aM tp : ℝ) (lawT : BirthLaw)
      (Gt' : GenStage D ScalarH A.Dt A.bw j₀) (seed : GenStage D ScalarH A.Ds A.bw j₀)
      (rootM rootR : ℕ → ℝ) (seedKc : ℕ → KernelSpec)
      (ι : CompIn (Gt'.retained M 1 A.RT).comps ≃ CompIn seed.comps),
      SeedCtx A sXT sZT nW cr CL Cχ kW cP CP cH Cw M D a lawW PW Gw aM tp lawT Gt' seed rootM
        rootR seedKc ι →
      QuietMatchingOn Gt' (ocTrimmedQuietTimes D.α D.q D.Λ D.ζ Gt'.level)
        (Set.Icc (tp + D.termH M) (a + A.T₀)))
    (h2 : ∀ (D : OCData) (a : ℝ) (lawW : BirthLaw) (PW : ProvParams)
      (Gw : GenStage D ScalarH A.Dt A.bw j₀) (aM tp : ℝ) (lawT : BirthLaw)
      (Gt' : GenStage D ScalarH A.Dt A.bw j₀) (seed : GenStage D ScalarH A.Ds A.bw j₀)
      (rootM rootR : ℕ → ℝ) (seedKc : ℕ → KernelSpec)
      (ι : CompIn (Gt'.retained M 1 A.RT).comps ≃ CompIn seed.comps),
      SeedCtx A sXT sZT nW cr CL Cχ kW cP CP cH Cw M D a lawW PW Gw aM tp lawT Gt' seed rootM
        rootR seedKc ι →
      StageHistoryInvariant seed (M + A.Jw)) :
    SeedQuietAtM A sXT sZT nW cr CL Cχ kW cP CP cH Cw j₀ M := by
  intro D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx
  have hhist := h2 D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx
  have hq := quietMatchingOn_retained Gt' M 1 A.RT _ _
    (h1 D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx)
  obtain ⟨-, -, -, -, -, -, -, henc, -⟩ := hctx
  obtain ⟨hlev, -, -, hact, hpiece, -, e, _, _, he⟩ := henc
  have hs := quietMatchingOn_encoded _ seed hlev hpiece hact ι e
    (fun v u γ => (he v u γ).2.2.2.2.1) (fun v u γ p c c' hc => (he v u γ).2.2.2.2.2 p c c' hc)
    _ _ hq
  have hS : ocTrimmedQuietTimes D.α D.q D.Λ D.ζ seed.level =
      ocTrimmedQuietTimes D.α D.q D.Λ D.ζ Gt'.level := by
    rw [hlev]
    rfl
  rw [hS]
  exact ⟨hs.1, hs.2.1, hs.2.2, hhist⟩

end AVRegularity.EntryTerminal.Ingredients
end
end

section
/-! **The carried history invariant passes to restrictions and along encodings** (the stage
invariant contains `StageHistoryInvariant G M`, so the terminal seed must carry it). The analogues of
`quietMatchingOn_restrict` and `quietMatchingOn_encoded`:
- a restriction keeps the level, the contexts and the fluxes of the kept components
  (`stageHistoryInvariant_restrict`, `stageHistoryInvariant_retained`);
- an encoding has the level and fluxes of the encoded stage at contexts with equal chains, and its
  components and identities are images of bijections (`stageHistoryInvariant_encoded`);
- for the terminal seed, the invariant of the actual successor passes to the seed through its
  retained family and the seed encoding (`stageHistoryInvariant_seed`). The successor's own
  invariant comes from `successorFinerHistory_of_covariant` and the preservation step.

Special cases:
- `G₂ = G₁` with identity bijections: the invariant itself.
- An empty retained family: vacuous.
- Different maximal orders of the two families: the invariant does not see them. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev Filter Topology

namespace AVRegularity.EntryTerminal.Ingredients

open AVRegularity.Providers.QuietAtlas

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {D₁ D₂ : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The carried history invariant of a stage holds for every restriction. -/
theorem stageHistoryInvariant_restrict (G : GenStage D hr D₁ b j₀) (S' : Finset Comp)
    (hS : S' ⊆ G.comps) {Mtop : ℕ} (h : StageHistoryInvariant G Mtop) :
    StageHistoryInvariant (G.restrict S' hS) Mtop :=
  fun p ch ch' hs t ht _ _ γ d I z => h p ch ch' hs t ht _ _ γ d I z

/-- The invariant for the retained part of a stage. -/
theorem stageHistoryInvariant_retained (G : GenStage D hr D₁ b j₀) (m H J : ℕ) {Mtop : ℕ}
    (h : StageHistoryInvariant G Mtop) : StageHistoryInvariant (G.retained m H J) Mtop :=
  stageHistoryInvariant_restrict G _ _ h

/-- **The invariant along an encoding.** -/
theorem stageHistoryInvariant_encoded (G₁ : GenStage D hr D₁ b j₀) (G₂ : GenStage D hr D₂ b j₀)
    (hlev : G₂.level = G₁.level) (ι : CompIn G₁.comps ≃ CompIn G₂.comps)
    (e : ∀ v u, G₁.fam.Γ v u ≃ G₂.fam.Γ (ι v) (ι u))
    (hflux : ∀ v u (γ : G₁.fam.Γ v u) (p : OddSlot) (c : StageCtx D b j₀ G₂.level p)
      (c' : StageCtx D b j₀ G₁.level p), c.1 = c'.1 → ∀ (d : ℕ) (I : DerivativeWord2 (d - 1))
      (t : ℝ) (X z : Vec 2), G₂.fam.flux p c (ι v) (ι u) (e v u γ) d I t X z =
        G₁.fam.flux p c' v u γ d I t X z)
    {Mtop : ℕ} (h : StageHistoryInvariant G₁ Mtop) : StageHistoryInvariant G₂ Mtop := by
  intro p ch ch' hs t ht v₂ u₂ γ₂ d I z
  obtain ⟨v, rfl⟩ := ι.surjective v₂
  obtain ⟨u, rfl⟩ := ι.surjective u₂
  obtain ⟨γ, rfl⟩ := (e v u).surjective γ₂
  obtain ⟨A, hA⟩ := ch
  obtain ⟨A', hA'⟩ := ch'
  change SameHistoryGeometry D Mtop G₂.level p.1 A A' at hs
  rw [hlev] at hs ht
  simp only [encoded_flux_eq G₁ G₂ hlev ι e hflux]
  exact h p (stageCtxCast hlev ⟨A, hA⟩) (stageCtxCast hlev ⟨A', hA'⟩) hs t ht v u γ d I z

/-- **The invariant of the terminal seed** from that of the actual successor, through its retained
family and the seed encoding. -/
theorem stageHistoryInvariant_seed {Dt Ds : ℕ} {D : OCData} {b : ℝ} {j₀ : ℕ} (Pt : ProvParams)
    (lawT : BirthLaw) (rootM rootR : ℕ → ℝ) (seedKt freshKt seedKc : ℕ → KernelSpec)
    (Gt' : GenStage D ScalarH Dt b j₀) (M RT : ℕ) (seed : GenStage D ScalarH Ds b j₀)
    (ι : CompIn (Gt'.retained M 1 RT).comps ≃ CompIn seed.comps)
    (henc : IsSeedEncoding Pt lawT rootM rootR seedKt freshKt seedKc (Gt'.retained M 1 RT) seed ι)
    {Mtop : ℕ} (h : StageHistoryInvariant Gt' Mtop) : StageHistoryInvariant seed Mtop := by
  obtain ⟨hlev, -, -, -, -, -, e, _, _, he⟩ := henc
  exact stageHistoryInvariant_encoded (hr := ScalarH) _ seed hlev ι e
    (fun v u γ p c c' hc => (he v u γ).2.2.2.2.2 p c c' hc)
    (stageHistoryInvariant_retained Gt' M 1 RT h)

end AVRegularity.EntryTerminal.Ingredients
end
end
end

section
section
/-! **The input of the quiet part of the seed from the successor's clause** (`SeedQuietPart`).
The clause of the terminal successor `Gt'` of
the weak stage `Gw` (`successorQuietMatching_of_generated`) needs one premise that the seed context
does not give:
- `SeedSuccTransversePart`: slot transversality of the terminal successor (`terminalSuccessor_generation` at the terminal
  menu), with the prefix and the block quantifiers of `SeedQuietPart` and its own `M₀`.

The carried history invariant of `Gw` is the last
conjunct of `IsStageInvariant`, so it comes by projection from `IsWeakStage`
(`stageHistoryInvariant_of_isStageInvariant`, `SeedQuiet/Successor.lean`).

Special cases:
- A successor without identities: slot transversality is vacuous.
- `M + J_w` as the finest level: the availability intervals are those of the terminal menu
  (`termMenu (M + J_w) …`). -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev

namespace AVRegularity.EntryTerminal.Route

open AVRegularity.Providers.QuietAtlas

/-- **Slot transversality of the terminal successor** at one level. -/
def SeedSuccTransverseAtM {X : TermConstruction} (A : TermArgs X) (sXT sZT : ℕ) (nW : ℕ+)
    (cr CL Cχ : ℝ) (kW : InvConsts) (cP CP cH Cw : ℝ) (j₀ M : ℕ) : Prop :=
  ∀ (D : OCData) (a : ℝ) (lawW : BirthLaw) (PW : ProvParams) (Gw : GenStage D ScalarH A.Dt A.bw j₀)
    (aM tp : ℝ) (lawT : BirthLaw) (Gt' : GenStage D ScalarH A.Dt A.bw j₀)
    (seed : GenStage D ScalarH A.Ds A.bw j₀) (rootM rootR : ℕ → ℝ) (seedKc : ℕ → KernelSpec)
    (ι : CompIn (Gt'.retained M 1 A.RT).comps ≃ CompIn seed.comps),
    SeedCtx A sXT sZT nW cr CL Cχ kW cP CP cH Cw M D a lawW PW Gw aM tp lawT Gt' seed rootM rootR
      seedKc ι →
    Gt'.IsSlotTransverse

/-- The block of `SeedSuccTransverseAtM`: a carrier pair and a threshold, as `SeedQuietBlock`. -/
def SeedSuccTransverseBlock {X : TermConstruction} (A : TermArgs X) (sXT sZT : ℕ) (nW : ℕ+)
    (cr CL Cχ : ℝ) (kW : InvConsts) (cP CP : ℝ) : Prop :=
  ∀ cH Cw : ℝ, 0 < cH → 0 ≤ Cw → ∃ (CHe Υe : ℝ), 1 ≤ CHe ∧ 0 < Υe ∧
    ∀ j₀ : ℕ, IsCarrierStart X.α X.q A.Λ A.bw CHe Υe j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      SeedSuccTransverseAtM A sXT sZT nW cr CL Cχ kW cP CP cH Cw j₀ M

/-- **Slot transversality of the terminal successor**, with the prefix of the parts of the seed clauses. -/
def SeedSuccTransversePart : Prop :=
  SeedPartPrefix fun _ A _ sXT sZT _ nW cr _ CL Cχ kW cP CP =>
    SeedSuccTransverseBlock A sXT sZT nW cr CL Cχ kW cP CP

end AVRegularity.EntryTerminal.Route
end
end

section
/-! **`SeedQuietPart` from the quiet matching of an actual successor**.
At one level:
- the clause of the terminal successor `Gt'` of the weak stage `Gw` is
  `successorQuietMatching_of_generated` on `S = ocTrimmedQuietTimes` and the seed window, with
  - the parent generated (`IsWeakStage` → `IsStageInvariant` → `IsGenerated`),
  - its history invariant at `M + J_w` by projection from `IsWeakStage` (the last conjunct of
    `IsStageInvariant`),
  - the slot transversality of `Gt'` from `SeedSuccTransverseAtM`,
  - the remaining premises from the data (`IsTermData`, `A.Valid`), the plan (`0 < c_r`), the lift
    floor `2 p_T + D_t + 2 ≤ s_X, s_Z` (this part's `SX, SZ`) and `j₀ + 2 ≤ M` (its `M₀`);
- it passes to the seed (`seedQuietAtM_of_successor_clause`: restriction, then encoding).
The seed's history invariant: the successor's (`successor_stageHistoryInvariant_of_carrier`,
(finer history and one-passage preservation), restricted and encoded
(`stageHistoryInvariant_seed`). The constants of the part are those of the transverse input, with
`Υ` raised to at least `1` (`IsCarrierStart.mono`).

Special cases:
- An empty successor: every clause is vacuous.
- No diagonal letter: the first-source inputs are vacuous.
- `sXT = 2 p_T + D_t + 2`: the minimal lift reserve. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev

namespace AVRegularity.EntryTerminal.Ingredients

open AVRegularity.Providers.QuietAtlas AVRegularity.EntryTerminal.Route

/-- `1 ≤ N_T` from the terminal schedule. -/
theorem one_le_NT_of_valid {X : TermConstruction} (A : TermArgs X) (hA : A.Valid) : 1 ≤ A.NT := by
  have hPT : 0 < A.PT := hA.2.2.2.2.1
  have hsch := hA.2.2.2.2.2.1
  dsimp only [IsTerminalSchedule] at hsch
  have hQT := hsch.2.1
  have hNT := hsch.2.2.2.1
  have hpos : 0 < X.q ^ (A.Jw + 1) * (1 + X.s) :=
    mul_pos (pow_pos (by linarith [X.hq.1]) _) (by linarith [X.hs₀])
  by_contra h
  have h0 : A.NT = 0 := by omega
  rw [h0, Nat.cast_zero, mul_zero] at hNT
  linarith

/-- The carried history invariant of a stage, by projection from its stage invariant. -/
theorem stageHistoryInvariant_of_isStageInvariant {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    {law : BirthLaw} {P : ProvParams} {seedK freshK : ℕ → KernelSpec} {φ₀ : Vec 2 → ℝ}
    {hφ₀ : Integrable φ₀} {Mnat : ℕ} {k : InvConsts} {tA tB S θK : ℝ}
    {G : GenStage D ScalarH Dm b j₀}
    (h : IsStageInvariant law P seedK freshK φ₀ hφ₀ Mnat k tA tB S θK G) :
    StageHistoryInvariant G Mnat := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hhist⟩ := h
  exact hhist

/-- **`SeedQuietAtM` from the clause of the terminal successor**, at one level. -/
theorem seedQuietAtM_of_successor {X : TermConstruction} (A : TermArgs X) (hA : A.Valid)
    (hΛA : 128 ≤ A.Λ) (sXT sZT : ℕ) (hX : 2 * A.pT + A.Dt + 2 ≤ sXT)
    (hZ : 2 * A.pT + A.Dt + 2 ≤ sZT) (nW : ℕ+) (cr : ℝ) (hcr : 0 < cr) (CL Cχ : ℝ)
    (kW : InvConsts) (cP CP cH Cw CH Υ : ℝ) (hCH : 1 ≤ CH) (hΥ : 1 ≤ Υ) (j₀ : ℕ)
    (hj₀ : IsCarrierStart X.α X.q A.Λ A.bw CH Υ j₀) (M : ℕ) (hM : j₀ + 2 ≤ M)
    (hT : SeedSuccTransverseAtM A sXT sZT nW cr CL Cχ kW cP CP cH Cw j₀ M) :
    SeedQuietAtM A sXT sZT nW cr CL Cχ kW cP CP cH Cw j₀ M := by
  refine seedQuietAtM_of_successor_clause A sXT sZT nW cr CL Cχ kW cP CP cH Cw j₀ M ?h1 ?h2
  case h2 =>
    intro D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx
    have hweak := hctx.2.1
    have hsucc := hctx.2.2.2.2.2.2.1
    have henc := hctx.2.2.2.2.2.2.2.1
    obtain ⟨hα, hq, hΛD, hζD, -, hband, hterm⟩ := hctx.1
    have hΛ : 1 ≤ D.Λ := by rw [hΛD]; omega
    have hζ : IsFastProfile D.ζ := by rw [hζD]; exact X.hζ
    have hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
      rw [hα, hq, hΛD, hζD, hterm]; exact hband
    have hb : 0 < A.bw := hA.2.2.1.1
    have hlev : Gw.level = M := hweak.2.2.1
    have hinvW := hweak.2.2.2.2.2.2.2.2.2
    obtain ⟨-, hG', -, -, -, -, -⟩ := (isActualSuccessor_iff_nonempty_witness _ _ Gw Gt').1 hsucc
    have hc2 : 0 < D.cellScaleSq Gw.level :=
      EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hκ _
    have hstart : IsCarrierStart D.α D.q D.Λ A.bw CH Υ j₀ := by rw [hα, hq, hΛD]; exact hj₀
    have hlt : Gt'.level < M + A.Jw := by omega
    exact stageHistoryInvariant_seed _ lawT rootM rootR _ _ seedKc Gt' M A.RT seed ι henc
      (successor_stageHistoryInvariant_of_carrier hΛ hζ hb hCH hΥ hstart hc2 hsucc
        hinvW.2.2.1 hlt (stageHistoryInvariant_of_isStageInvariant hinvW))
  intro D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx
  have hTr := hT D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx
  have hweak := hctx.2.1
  have hsucc := hctx.2.2.2.2.2.2.1
  obtain ⟨hα, hq, hΛD, hζD, -, hband, hterm⟩ := hctx.1
  have hΛ : 1 ≤ D.Λ := by rw [hΛD]; omega
  have hζ : IsFastProfile D.ζ := by rw [hζD]; exact X.hζ
  have hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    rw [hα, hq, hΛD, hζD, hterm]; exact hband
  have hb : 0 < A.bw := hA.2.2.1.1
  have hlev : Gw.level = M := hweak.2.2.1
  have hinvW := hweak.2.2.2.2.2.2.2.2.2
  obtain ⟨hG1, hG', -, hnat, -, -, ⟨w⟩⟩ :=
    (isActualSuccessor_iff_nonempty_witness _ _ Gw Gt').1 hsucc
  have hc2 : 0 < D.cellScaleSq Gw.level := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hκ _
  have hρ : cr * liftLength D Gw.level ≠ 0 := by
    refine mul_ne_zero hcr.ne' (Real.sqrt_pos.mpr (mul_pos ?_
      (Construction.Stream.ocTauPP_pos hΛ))).ne'
    exact CycleReference.bandChain_pos (by omega) X.hζ hband (by omega)
  have hi : 1 ≤ Gt'.level := by omega
  have hj : j₀ ≤ Gt'.level := by omega
  have hstart : IsCarrierStart D.α D.q D.Λ A.bw CH Υ j₀ := by rw [hα, hq, hΛD]; exact hj₀
  have hS : IsHistoryQuiet D (M + A.Jw) Gt'.level
      (ocTrimmedQuietTimes D.α D.q D.Λ D.ζ Gt'.level) :=
    isHistoryQuiet_ocTrimmedQuiet hΛ hCH hstart _ _ hj
  have hinv : StageHistoryInvariant Gw (M + A.Jw) := stageHistoryInvariant_of_isStageInvariant hinvW
  exact successorQuietMatching_of_generated (hr := ScalarH) hG1 hG' hζ hΛ hb hc2
    (one_le_NT_of_valid A hA) hX hZ hρ hi hj hCH hstart w hinvW.2.2.1 hnat hS hinv hTr

/-- **`SeedQuietPart` from the slot transversality of the terminal successor.** -/
theorem seedQuietPart_of_successor (hT : SeedSuccTransversePart) : SeedQuietPart := by
  intro X
  obtain ⟨Λ₀, hΛ₀, hT1⟩ := hT X
  refine ⟨Λ₀, hΛ₀, fun A hΛ hA Kout => ?_⟩
  obtain ⟨SX, SZ, hT2⟩ := hT1 A hΛ hA Kout
  refine ⟨max SX (2 * A.pT + A.Dt + 2), max SZ (2 * A.pT + A.Dt + 2), fun sXT sZT hX hZ => ?_⟩
  obtain ⟨KS, F, hT3⟩ := hT2 sXT sZT (le_of_max_le_left hX) (le_of_max_le_left hZ)
  refine ⟨KS, F, fun Lt nW cr kS hplan => ?_⟩
  intro cK CL Cχ kW hcK hkW hWA cP CP hcP cH Cw hcH hCw
  obtain ⟨CHe, Υe, hCHe, hΥe, hT4⟩ :=
    hT3 Lt nW cr kS hplan cK CL Cχ kW hcK hkW hWA cP CP hcP cH Cw hcH hCw
  have h1Λ : 1 ≤ A.Λ := by omega
  have hAnn : ∀ k, 0 ≤ ocA X.α X.q A.Λ k := fun k => by
    unfold ocA
    exact Real.rpow_nonneg (Construction.Stream.ocEpsilon_pos h1Λ).le _
  have hTnn : ∀ k, 0 ≤ ocTauPP X.α X.q A.Λ k := fun k => (Construction.Stream.ocTauPP_pos h1Λ).le
  refine ⟨CHe, max Υe 1, hCHe, lt_of_lt_of_le hΥe (le_max_left _ _), fun j₀ hj₀ => ?_⟩
  obtain ⟨M₀, hT5⟩ := hT4 j₀ (IsCarrierStart.mono hAnn hTnn le_rfl (le_max_left _ _)
    (zero_le_one.trans hCHe) hΥe.le hj₀)
  refine ⟨max M₀ (j₀ + 2), fun M hM => ?_⟩
  exact seedQuietAtM_of_successor A hA (le_trans hΛ₀ hΛ) sXT sZT (le_of_max_le_right hX)
    (le_of_max_le_right hZ) nW cr hplan.2.2.2.2.1 CL Cχ kW cP CP cH Cw CHe (max Υe 1) hCHe
    (le_max_right _ _) j₀ hj₀ M (le_of_max_le_right hM) (hT5 M (le_of_max_le_left hM))

end AVRegularity.EntryTerminal.Ingredients
end
end

section
/-! **`2 ≤ N_T` from the terminal schedule.** In the admissible regime
`1 < q < 17/16`, `0 < α < 1/3` one has `ζ = qγ + 3δ < 6`, while the schedule gives
`ζ N_T > Q_T + 2 > 6`.

Special cases:
- `N_T = 2`: allowed.
- `N_T = 1`: excluded, as `ζ N_T = ζ < 6`. -/

@[expose] public noncomputable section

namespace AVRegularity.EntryTerminal.Ingredients

open AVRegularity AVRegularity.EntryTerminal.Route

/-- In the admissible regime `q γ + 3 δ ≤ 6`. -/
theorem zeta_le_six {α s q : ℝ} (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s)
    (hs₁ : s < (1 - α) / 2) (hq : IsAdmissibleQ α s q) :
    q * ocGamma α q + 3 * ocDelta α q ≤ 6 := by
  have hf := Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq
  have hγ := hf.1
  have hδ := hf.2.1
  have hq' := hq
  obtain ⟨hq₀, hq₁, -, -⟩ := hq'
  have hden : 0 < q + 1 := by linarith
  have hγ1 : ocGamma α q ≤ 1 := by
    unfold ocGamma
    rw [div_le_one hden]
    nlinarith
  have hδ1 : ocDelta α q ≤ 1 := by
    unfold ocDelta
    have hf : 0 ≤ (2 * q + 1) * (1 + α) / (2 * q + 2) := by positivity
    have h1 : 0 ≤ (q - 1) / 4 := by linarith
    have h2 : (q - 1) / 4 ≤ 1 := by linarith
    nlinarith
  nlinarith

/-- **`2 ≤ N_T`** from the terminal schedule. -/
theorem two_le_NT_of_valid {X : TermConstruction} (A : TermArgs X) (hA : A.Valid) : 2 ≤ A.NT := by
  have hPT : 0 < A.PT := hA.2.2.2.2.1
  have hsch := hA.2.2.2.2.2.1
  dsimp only [IsTerminalSchedule] at hsch
  have hQT := hsch.2.1
  have hNT := hsch.2.2.2.1
  have hpos : 0 < X.q ^ (A.Jw + 1) * (1 + X.s) :=
    mul_pos (pow_pos (by linarith [X.hq.1]) _) (by linarith [X.hs₀])
  have hz := zeta_le_six X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq
  have hz0 : 0 ≤ X.q * ocGamma X.α X.q + 3 * ocDelta X.α X.q := by
    have := Scales.admissible_exponent_facts X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq
    have hq0 : 0 < X.q := by linarith [X.hq.1]
    nlinarith [this.1, this.2.1]
  by_contra h
  have h1 : (A.NT : ℝ) ≤ 1 := by exact_mod_cast (by omega : A.NT ≤ 1)
  have h2 := mul_le_mul_of_nonneg_left h1 hz0
  linarith
end AVRegularity.EntryTerminal.Ingredients
end
end

section
/-! **Slot transversality of the terminal successor** (`SeedSuccTransversePart`).
`terminalSuccessor_generation` at terminal entry gives `Gt'.IsSlotTransverse` from the
seed context:
- the data (`IsTermData`), the weak stage and the successor of `SeedCtx`;
- the plan's `0 < c_r`;
- the lift floors `s_X, s_Z ≥ max(N_T + D_W, 2p_T) + D̄₀ + 2` (this part's `SX, SZ`);
- the carrier pair `C_H = Υ = 1`;
- `2 ≤ N_T` (`two_le_NT_of_valid`) and `1 ≤ D_W` (in `A.Valid`).

Special cases:
- A successor without identities: vacuous.
- `D_W = 1`: the first-source reserve `N_T + 1 ≤ N_T + D_W` is tight.
- `c_r = 1`: allowed. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev

namespace AVRegularity.EntryTerminal.Ingredients

open AVRegularity.EntryTerminal.Route

/-- **Slot transversality of the terminal successor.** -/
theorem seedSuccTransversePart : SeedSuccTransversePart := by
  intro X
  refine ⟨128, le_rfl, fun A hΛ hA Kout => ?_⟩
  have hN : 2 ≤ A.NT := two_le_NT_of_valid A hA
  have hDW : 1 ≤ A.DW := hA.2.2.2.2.2.2.2.2
  have hb : 0 < A.bw := hA.2.2.1.1
  set S := max (A.NT + A.DW) (2 * A.pT) + A.Dt + 2 with hS
  refine ⟨S, S, fun sXT sZT hX hZ => ⟨0, ⟨fun _ _ => 0, fun _ => 0, fun _ => 0, fun _ => 0,
    fun _ _ => 0, fun _ _ => 0, fun _ _ _ => 0⟩, fun Lt nW cr kS hplan => ?_⟩⟩
  intro cK CL Cχ kW _ _ _ cP CP _ cH Cw _ _
  have hcr : cr ≠ 0 := (hplan.2.2.2.2.1).ne'
  refine ⟨1, 1, le_rfl, one_pos, fun j₀ hj₀ => ⟨0, fun M _ => ?_⟩⟩
  intro D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx
  obtain ⟨hα, hq, hΛD, hζD, -, hband, hterm⟩ := hctx.1
  have hΛ1 : 1 ≤ D.Λ := by rw [hΛD]; omega
  have hζ : IsFastProfile D.ζ := by rw [hζD]; exact X.hζ
  have hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ := by
    rw [hα, hq, hΛD, hζD, hterm]; exact hband
  have hcar : IsCarrierStart D.α D.q D.Λ A.bw 1 1 j₀ := by rw [hα, hq, hΛD]; exact hj₀
  exact (Providers.GenSem.terminalSuccessor_generation hΛ1 hζ hκ hb le_rfl le_rfl hcar hterm hctx.2.1
    hN hDW hcr hX hZ hctx.2.2.2.2.2.2.1).2

end AVRegularity.EntryTerminal.Ingredients
end
end

section
/-! **E5 part 5 proved**: `seedQuietPart_of_successor` applied to the proved slot transversality
`seedSuccTransversePart`. -/

@[expose] public section

namespace AVRegularity.EntryTerminal.Ingredients

/-- **The quiet structure of the seed** (`SeedQuietPart`). -/
theorem seedQuietPart : AVRegularity.EntryTerminal.Route.SeedQuietPart :=
  seedQuietPart_of_successor seedSuccTransversePart

end AVRegularity.EntryTerminal.Ingredients
end
end
end
