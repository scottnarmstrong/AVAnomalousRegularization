-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Assembly.Route.Ingredients
import AVRegularity.EntryTerminal.Assembly.Route.EntryTerminalOfWeak
import AVRegularity.Construction.Preservation.FullLift.NativePhysicalAllOrderSeminorm
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarCellStrongTime
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer

section
@[expose] public noncomputable section
namespace AVRegularity

/-! **kernel widths and lengths of the tags of a successor** (the record-width identification and the record length
clause of the identity price).

A tag is *good* when the width of its kernel key is its width and its length is at most `L`. The
tags of every source of a successor are good once the tags of the old stage are good and the fresh
tags (`P.rb`, `P.Rb`) are: direct transports keep the tags, a quadratic conversion takes the tags
of a widest input (or the fresh tags on an empty path), a letter is fresh. An empty stage has no sources besides letters. -/

/-- The width of the kernel key is the width of the tag, and the length is at most `L`. -/
def GoodTag (kw : KernelKey → ℝ) (L : ℝ) (t : ProvTags) : Prop :=
  kw t.kernel = t.width ∧ t.length ≤ L

theorem widestTags_good {kw : KernelKey → ℝ} {L : ℝ} :
    ∀ {ts : List ProvTags}, (∀ t ∈ ts, GoodTag kw L t) → ∀ {w : ProvTags},
      widestTags ts = some w → GoodTag kw L w
  | [], _, w, hw => by simp [widestTags] at hw
  | t :: ts, h, w, hw => by
    have hts : ∀ s ∈ ts, GoodTag kw L s := fun s hs => h s (List.mem_cons_of_mem _ hs)
    have ht : GoodTag kw L t := h t List.mem_cons_self
    unfold widestTags at hw
    cases h' : widestTags ts with
    | none => rw [h'] at hw; simp at hw; rw [← hw]; exact ht
    | some t' =>
      rw [h'] at hw
      have ht' := widestTags_good hts h'
      by_cases hlt : t.width < t'.width
      · simp only [hlt, ite_true, Option.some.injEq] at hw; rw [← hw]; exact ht'
      · simp only [hlt, ite_false, Option.some.injEq] at hw; rw [← hw]; exact ht

theorem pathTags_mem (P : ProvParams) :
    ∀ {path : List (Comp × Comp × Prov)} {t : ProvTags}, t ∈ Prov.pathTags P path →
      ∃ x ∈ path, t = x.2.2.tags P
  | [], t, ht => by simp [Prov.pathTags] at ht
  | (a, c, y) :: rest, t, ht => by
    simp only [Prov.pathTags, List.mem_cons] at ht
    rcases ht with ht | ht
    · exact ⟨(a, c, y), List.mem_cons_self, ht⟩
    · obtain ⟨x, hx, hxt⟩ := pathTags_mem P ht
      exact ⟨x, List.mem_cons_of_mem _ hx, hxt⟩

section Source

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

/-- **The tags of every source of the successor are good** (old tags good, fresh tags good). -/
theorem succSource_tags_good {Gw : GenStage D hr Dm bw j₀} (P : ProvParams) {kw : KernelKey → ℝ}
    {L : ℝ} (hgood : ∀ v u (γ : Gw.fam.Γ v u), GoodTag kw L ((Gw.prov v u γ).tags P))
    (hfresh : ∀ b, kw (.fresh b) = P.rb b) (hL : ∀ b, P.Rb b ≤ L) (m : ℕ) (s : SuccSource Gw) :
    GoodTag kw L ((s.prov m).tags P) := by
  have hlet : ∀ (l : WordLetter) (path : List (Comp × Comp × Prov)),
      GoodTag kw L ((Prov.letter m l path).tags P) := fun l path =>
    ⟨hfresh (m - 1), hL (m - 1)⟩
  cases s with
  | copyDir t v u γ => exact hgood v u γ
  | copyQuad t h π =>
    have hpath : ∀ x ∈ π.provList, GoodTag kw L (x.2.2.tags P) := by
      intro x hx
      unfold StagePath.provList at hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hx
      exact hgood _ _ _
    have hall : ∀ t ∈ Prov.pathTags P π.provList, GoodTag kw L t := by
      intro t ht
      obtain ⟨x, hx, rfl⟩ := pathTags_mem P ht
      exact hpath x hx
    show GoodTag kw L ((Prov.quad m π.provList).tags P)
    unfold Prov.tags
    dsimp only
    split
    · exact ⟨hfresh (m - 1), hL (m - 1)⟩
    · rename_i tw hw
      exact (widestTags_good (w := tw) hall hw : GoodTag kw L tw)
  | letterDiag t u => exact hlet _ _
  | letterMean t n h π => exact hlet _ _
  | letterCov t n h a a' π => exact hlet _ _

end Source

end AVRegularity
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.EntryTerminal.Route

/-! **The parts of the seed clauses statement** (`SeedClausesStatement`), the terminal coefficient
production. Each part concludes one group of clauses of `TerminalSeedClauses` (through
`IsGeneratedSeed` and `IsStageInvariant`) or of `TerminalRetainedClauses`, at the per-level
context `SeedCtx`.

| Part | Clauses | Instance |
|---|---|---|
| `SeedStructPart` | level, births, seed provenance, depth `≤ r̄₀`, orders `≤ D̄₀`, widths and lengths `≤ ε_n`, the two mass sums `< 5/6`; the law constant `c_H` | the re-rooting, the schedule, `(1+1/4)·2/3` |
| `SeedCertPart` | natural, tags, generated, shift invariant, slot transverse, context certified, exports | certification at the anchor `t_p` and slow-length factor `c_r`; `successor_torus_compatible`; the weak registry |
| `SeedKernelPart` | kernels admissible, widths, regularizers | `isoPairedKernel` facts |
| `SeedEnvelopePart` | the sampled bound, both envelopes, the pointwise molecular envelope, the ledger, the kernel price | `ContextStageEnvelopesStatement` (envelopes and pointwise envelopes of a context-certified stage) and the kernel-price Schur lemma `kernel_schur_of_identity_prices` |
| `SeedQuietPart` | the quiet atlas, transversality on pulses, fast independence | The stage-generic quiet matching (the quiet set is a parameter) |
| `SeedRetainedPart` | `TerminalRetainedClauses` at `K̂` | the kernel-price lemma on the retained family; coefficient regularity |

Order of the constants: the law constant `c_H` (structure), then the witness constant `C_w`
(certification, from above), then the seed constant `C_e` (envelopes, from above); the kernel
constants are the plan's `k_S.c_ker` (above the floors `F`). Each part has its own lift floors,
reserve floor, constant floors and carrier pair; the assembly takes maxima.

For an empty retained family every per-component clause is vacuous, the mass sums are `0 < 5/6`
and the ledger is `0`. A seed with one root and no identities has no kernels, and its envelopes
are empty sums. -/

/-- Structure at one level: level, births, provenance, depth, orders, widths, lengths, masses. -/
def SeedStructAtM {X : TermConstruction} (A : TermArgs X) (sXT sZT : ℕ) (nW : ℕ+)
    (cr CL Cχ : ℝ) (kW : InvConsts) (cP CP cH Cw : ℝ) (j₀ M : ℕ) : Prop :=
  ∀ (D : OCData) (a : ℝ) (lawW : BirthLaw) (PW : ProvParams) (Gw : GenStage D ScalarH A.Dt A.bw j₀)
    (aM tp : ℝ) (lawT : BirthLaw) (Gt' : GenStage D ScalarH A.Dt A.bw j₀)
    (seed : GenStage D ScalarH A.Ds A.bw j₀) (rootM rootR : ℕ → ℝ) (seedKc : ℕ → KernelSpec)
    (ι : CompIn (Gt'.retained M 1 A.RT).comps ≃ CompIn seed.comps),
    SeedCtx A sXT sZT nW cr CL Cχ kW cP CP cH Cw M D a lawW PW Gw aM tp lawT Gt' seed rootM rootR
      seedKc ι →
    seed.level = M - 1 ∧ (∀ v : CompIn seed.comps, v.1.births = []) ∧
      (∀ v u (γ : seed.fam.Γ v u), ∃ k tag, seed.prov v u γ = .seed k tag) ∧
      seed.fam.HasDepthAtMost A.r0 ∧
      (∀ v u (γ : seed.fam.Γ v u), (seed.fam.identity v u γ).maxOrder ≤ A.Dt ∧
        (seed.fam.identity v u γ).record.width ≤ D.eps (M - 1) ∧
        (1 ≤ (seed.fam.identity v u γ).record.birthExcess →
          (seed.fam.identity v u γ).record.length ≤ D.eps (M - 1))) ∧
      ∀ law : BirthLaw, law.rootMass = rootM → law.rootReadout = rootR →
        ∑ v, seed.mass law v < 5 / 6 ∧ ∑ v, seed.readoutWeight law v ^ 2 * seed.mass law v < 5 / 6

/-- Certification at one level: membership, tags, transversality, context certificate, exports. -/
def SeedCertAtM {X : TermConstruction} (A : TermArgs X) (sXT sZT : ℕ) (nW : ℕ+) (cr : ℝ)
    (kS : InvConsts) (CL Cχ : ℝ) (kW : InvConsts) (cP CP cH Cw : ℝ) (j₀ M : ℕ) : Prop :=
  ∀ (D : OCData) (a : ℝ) (lawW : BirthLaw) (PW : ProvParams) (Gw : GenStage D ScalarH A.Dt A.bw j₀)
    (aM tp : ℝ) (lawT : BirthLaw) (Gt' : GenStage D ScalarH A.Dt A.bw j₀)
    (seed : GenStage D ScalarH A.Ds A.bw j₀) (rootM rootR : ℕ → ℝ) (seedKc : ℕ → KernelSpec)
    (ι : CompIn (Gt'.retained M 1 A.RT).comps ≃ CompIn seed.comps),
    SeedCtx A sXT sZT nW cr CL Cχ kW cP CP cH Cw M D a lawW PW Gw aM tp lawT Gt' seed rootM rootR
      seedKc ι →
    seed.IsNatural (M + A.Jw) ∧ (∀ P : ProvParams, seed.HasTags P) ∧ seed.IsGenerated ∧
      seed.IsShiftInvariant ∧ seed.IsSlotTransverse ∧ seed.IsContextCertified kS ∧
      (∀ (i : ℕ) (p : ℤ) (e : Gen .ctx i p), seed.exports e →
        Gen.IsScheduled D e ∧ (∀ f : GenSort.Sem .ctx, Gen.Denotes D A.bw j₀ e f →
          IsSlotParInvCtx D A.bw j₀ i p f) ∧
        ∀ f f' : GenSort.Sem .ctx, Gen.Denotes D A.bw j₀ e f → Gen.Denotes D A.bw j₀ e f' →
          ∀ t ∈ ocPulseWindow D.α D.q D.Λ i p, ∀ ch : RealChain, IsAdmissibleChain D A.bw j₀ i p ch →
            ∀ ζ : Vec 2, f t ch ζ = f' t ch ζ) ∧
      SeedExports.Above (fun {_ _} e => seed.exports e) (M - 1)

/-- Kernels at one level: admissibility, widths, regularizers. -/
def SeedKernelAtM {X : TermConstruction} (A : TermArgs X) (sXT sZT : ℕ) (nW : ℕ+) (cr : ℝ)
    (kS : InvConsts) (CL Cχ : ℝ) (kW : InvConsts) (cP CP cH Cw : ℝ) (j₀ M : ℕ) : Prop :=
  ∀ (D : OCData) (a : ℝ) (lawW : BirthLaw) (PW : ProvParams) (Gw : GenStage D ScalarH A.Dt A.bw j₀)
    (aM tp : ℝ) (lawT : BirthLaw) (Gt' : GenStage D ScalarH A.Dt A.bw j₀)
    (seed : GenStage D ScalarH A.Ds A.bw j₀) (rootM rootR : ℕ → ℝ) (seedKc : ℕ → KernelSpec)
    (ι : CompIn (Gt'.retained M 1 A.RT).comps ≃ CompIn seed.comps),
    SeedCtx A sXT sZT nW cr CL Cχ kW cP CP cH Cw M D a lawW PW Gw aM tp lawT Gt' seed rootM rootR
      seedKc ι →
    ∀ (P : ProvParams) (freshK : ℕ → KernelSpec) (v u : CompIn seed.comps) (γ : seed.fam.Γ v u),
      (seed.kernelOf P seedKc freshK v u γ).IsAdmissible kS.Γk kS.Lker ∧
      (seed.kernelOf P seedKc freshK v u γ).width = (seed.fam.identity v u γ).record.width ∧
      (seed.fam.identity v u γ).record.width ≤
        kS.Cwid * rhoStar D kS.c₀ seed.level * D.eps seed.level ^ kS.σf ∧
      (seed.fam.identity v u γ).record.width ≤
        kS.Cwid * rhoEnh D kS.cr seed.level * D.eps (seed.level - 1) ^ kS.lamC ∧
      ∀ ϱ : ℝ, 0 < ϱ → ∀ kk ≤ kS.Ks,
        IsSpatialRegularizerTorus ϱ kk A.Ds (tp + D.termH M) (a + A.T₀) kS.cker
          (seed.kernelOf P seedKc freshK v u γ).width
          (seed.sysS P seedKc freshK A.φ₀ A.hφ₀ v u γ)

/-- Envelopes at one level: the sampled bound, both envelopes, the ledger, the kernel price, the
pointwise molecular envelope, at the seed constant `C_e`. The naturalness and the context
certificate of the seed are premises: the certification part (`SeedCertAtM`) gives them at the
same level, and the envelope estimate reads them (`ContextEnvelopeInput`). -/
def SeedEnvelopeAtM {X : TermConstruction} (A : TermArgs X) (sXT sZT : ℕ) (nW : ℕ+) (cr : ℝ)
    (kS : InvConsts) (CL Cχ : ℝ) (kW : InvConsts) (cP CP cH Cw Ce : ℝ) (j₀ M : ℕ) : Prop :=
  ∀ (D : OCData) (a : ℝ) (lawW : BirthLaw) (PW : ProvParams) (Gw : GenStage D ScalarH A.Dt A.bw j₀)
    (aM tp : ℝ) (lawT : BirthLaw) (Gt' : GenStage D ScalarH A.Dt A.bw j₀)
    (seed : GenStage D ScalarH A.Ds A.bw j₀) (rootM rootR : ℕ → ℝ) (seedKc : ℕ → KernelSpec)
    (ι : CompIn (Gt'.retained M 1 A.RT).comps ≃ CompIn seed.comps),
    SeedCtx A sXT sZT nW cr CL Cχ kW cP CP cH Cw M D a lawW PW Gw aM tp lawT Gt' seed rootM rootR
      seedKc ι →
    seed.IsNatural (M + A.Jw) → seed.IsContextCertified kS →
    ∀ law : BirthLaw, law.rootMass = rootM → law.rootReadout = rootR →
    (∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ D.eps (M - 1) → ∀ k ≤ kS.Ks, ∀ v u (γ : seed.fam.Γ v u) (d : ℕ), 2 ≤ d →
      d ≤ (seed.fam.identity v u γ).maxOrder →
      coefficientSeminorm ϱ k (tp + D.termH M) (a + A.T₀) (seed.physCoeff v u γ d) ≤
        ENNReal.ofReal (Ce * (seed.fam.identity v u γ).record.size * D.κ (M - 1) *
          (seed.fam.identity v u γ).record.length ^ (d - 2))) ∧
    (∀ K : CompIn seed.comps → ℕ, (∀ v, K v ≤ kS.Ks) →
      IsEnvelope seed.fam (seed.mass law) K
          (seed.innerDomain (Set.Icc (tp + D.termH M) (a + A.T₀)) kS.mEnv)
          (D.kap seed.level) (D.eps seed.level) (D.eps (seed.level - 1)) (rhoStar D kS.c₀ seed.level)
          (recordMajorant (seed.mass law) seed.fam) (Ce * D.eps (M - 1) ^ A.τe) kS.Ca kS.Kan kS.Lan
          kS.Cm kS.Jm ∧
        IsEnvelope (markerConj (seed.marker law) seed.fam) (seed.mass law) K
          (seed.innerDomain (Set.Icc (tp + D.termH M) (a + A.T₀)) kS.mEnv)
          (D.kap seed.level) (D.eps seed.level) (D.eps (seed.level - 1)) (rhoStar D kS.c₀ seed.level)
          (fun v u => seed.marker law v / seed.marker law u * recordMajorant (seed.mass law) seed.fam v u)
          (Ce * D.eps (M - 1) ^ A.τe) kS.Ca kS.Kan kS.Lan kS.Cm kS.Jm) ∧
    markedLedger (seed.mass law) (seed.marker law) seed.fam ≤ Ce * D.eps (M - 1) ^ A.τe ∧
    (∀ (P : ProvParams) (freshK : ℕ → KernelSpec), ∀ kk ≤ kS.Ks, ∀ w : CompIn seed.comps → ℝ,
      (w = fun _ => 1) ∨ w = seed.marker law →
      SchurBound (Ce * D.eps (M - 1 - 1) ^ (D.q * A.τe))
        (kernelSchurMatrix (ι := CompIn seed.comps) (h := fun v => ScalarH v.1.root)
          (Γ := seed.fam.Γ) (G := fun _ u _ => ScalarH u.1.root) (D.kap seed.level)
          (rhoStar D kS.c₀ seed.level) (fun v => seed.mass law v / w v ^ 2) kk A.Ds
          (tp + D.termH M) (a + A.T₀) kS.cker
          (fun v u γ => (seed.kernelOf P seedKc freshK v u γ).width)
          (fun _ u _ => ContinuousLinearMap.id ℝ (ScalarH u.1.root))
          (fun v u γ d => seed.physCoeff v u γ d.1))) ∧
    IsSeedPointwiseMolecular law kS seed (tp + D.termH M) (a + A.T₀)

/-- The quiet structure at one level (the untrimmed quiet set), and the carried
history invariant of the seed at the natural level `M + J_w`. -/
def SeedQuietAtM {X : TermConstruction} (A : TermArgs X) (sXT sZT : ℕ) (nW : ℕ+) (cr CL Cχ : ℝ)
    (kW : InvConsts) (cP CP cH Cw : ℝ) (j₀ M : ℕ) : Prop :=
  ∀ (D : OCData) (a : ℝ) (lawW : BirthLaw) (PW : ProvParams) (Gw : GenStage D ScalarH A.Dt A.bw j₀)
    (aM tp : ℝ) (lawT : BirthLaw) (Gt' : GenStage D ScalarH A.Dt A.bw j₀)
    (seed : GenStage D ScalarH A.Ds A.bw j₀) (rootM rootR : ℕ → ℝ) (seedKc : ℕ → KernelSpec)
    (ι : CompIn (Gt'.retained M 1 A.RT).comps ≃ CompIn seed.comps),
    SeedCtx A sXT sZT nW cr CL Cχ kW cP CP cH Cw M D a lawW PW Gw aM tp lawT Gt' seed rootM rootR
      seedKc ι →
    (∃ T : seed.fam.Atlas,
      T.IsConsecutiveClosed (Set.Icc (tp + D.termH M) (a + A.T₀)) ∧
      T.CoversQuiet (ocQuietTimes D.α D.q D.Λ D.ζ seed.level) (Set.Icc (tp + D.termH M) (a + A.T₀)) ∧
      T.IsQuiet (D.kap seed.level) (D.eps seed.level) (D.eps (seed.level - 1)) ∧
      (∀ p q (hpq : T.adjacent p q),
        ((seed.fam.piece p).output ∩ (seed.fam.piece q).output ∩
          Set.Icc (tp + D.termH M) (a + A.T₀)).Nonempty →
        T.sameCtx p q hpq (seed.actual p) (seed.actual q)) ∧
      (∀ p q (hpq : T.adjacent p q) c c', T.sameCtx p q hpq c c' →
        c = seed.actual p ∧ c' = seed.actual q)) ∧
    seed.fam.IsTransverseOnPulses (enlargedPulse D seed.level (Set.Icc (tp + D.termH M) (a + A.T₀)))
      parallelIndex ∧
    seed.fam.IsFastIndependentOn
      (ocTrimmedQuietTimes D.α D.q D.Λ D.ζ seed.level ∩ Set.Icc (tp + D.termH M) (a + A.T₀)) ∧
    StageHistoryInvariant seed (M + A.Jw)

/-- The certificates of the retained family at one level, at the plan's kernel constants. -/
def SeedRetainedAtM {X : TermConstruction} (A : TermArgs X) (Kout sXT sZT : ℕ) (nW : ℕ+) (cr : ℝ)
    (kS : InvConsts) (CL Cχ : ℝ) (kW : InvConsts) (cP CP cH Cw : ℝ) (j₀ M : ℕ) : Prop :=
  ∀ (D : OCData) (a : ℝ) (lawW : BirthLaw) (PW : ProvParams) (Gw : GenStage D ScalarH A.Dt A.bw j₀)
    (aM tp : ℝ) (lawT : BirthLaw) (Gt' : GenStage D ScalarH A.Dt A.bw j₀)
    (seed : GenStage D ScalarH A.Ds A.bw j₀) (rootM rootR : ℕ → ℝ) (seedKc : ℕ → KernelSpec)
    (ι : CompIn (Gt'.retained M 1 A.RT).comps ≃ CompIn seed.comps),
    SeedCtx A sXT sZT nW cr CL Cχ kW cP CP cH Cw M D a lawW PW Gw aM tp lawT Gt' seed rootM rootR
      seedKc ι →
    TerminalRetainedClauses lawT (A.Pt D Cw cr M) (A.Kw_ D M nW) (A.Kn_ D M cr) A.φ₀ A.hφ₀
      kS.cker M (A.Khat Kout) cr tp (a + A.T₀) (Gt'.retained M 1 A.RT)

/-! **The seed clauses statement from its parts** (`seedClauses_of_parts`).

Each part is stated with the prefix of the seed clauses statement (lift floors, reserve floor, constant floors `F`, plan,
weak constants, preparation constants) and its own block of constants (`SeedStructBlock`, …):
- the structure part chooses `c_H`;
- certification chooses a floor for `C_w` and a carrier pair;
- envelopes choose a floor for `C_e` (after `c_H`, `C_w`) and a carrier pair;
- the quiet part chooses a carrier pair.

The assembly takes maxima of the floors, the floor sets `F` (`SeedFloors.sup`) and the carrier
pairs (`IsCarrierStart.mono`). It puts `C_w :=` the certification floor, `C_e := max C_e⁰ 1`,
`c_ker := k_S.c_ker`, and combines the six per-level conclusions into `SeedAtM`
(`seedAtM_of_parts`). -/

/-- The pointwise maximum of two floor sets. -/
def SeedFloors.sup (F G : SeedFloors) : SeedFloors where
  cker := fun n j => max (F.cker n j) (G.cker n j)
  Γk := fun n => max (F.Γk n) (G.Γk n)
  Cwid := fun n => max (F.Cwid n) (G.Cwid n)
  Ca := fun n => max (F.Ca n) (G.Ca n)
  Cm := fun n j => max (F.Cm n j) (G.Cm n j)
  CaO := fun n k => max (F.CaO n k) (G.CaO n k)
  CmO := fun n k j => max (F.CmO n k j) (G.CmO n k j)

theorem SeedFloors.Meets.left {F G : SeedFloors} {nW : ℕ+} {kS : InvConsts}
    (h : (F.sup G).Meets nW kS) : F.Meets nW kS :=
  ⟨fun j => le_trans (le_max_left _ _) (h.1 j), le_trans (le_max_left _ _) h.2.1,
    le_trans (le_max_left _ _) h.2.2.1, le_trans (le_max_left _ _) h.2.2.2.1,
    fun j => le_trans (le_max_left _ _) (h.2.2.2.2.1 j),
    le_trans (le_max_left _ _) h.2.2.2.2.2.1, fun j => le_trans (le_max_left _ _) (h.2.2.2.2.2.2 j)⟩

theorem SeedFloors.Meets.right {F G : SeedFloors} {nW : ℕ+} {kS : InvConsts}
    (h : (F.sup G).Meets nW kS) : G.Meets nW kS :=
  ⟨fun j => le_trans (le_max_right _ _) (h.1 j), le_trans (le_max_right _ _) h.2.1,
    le_trans (le_max_right _ _) h.2.2.1, le_trans (le_max_right _ _) h.2.2.2.1,
    fun j => le_trans (le_max_right _ _) (h.2.2.2.2.1 j),
    le_trans (le_max_right _ _) h.2.2.2.2.2.1, fun j => le_trans (le_max_right _ _) (h.2.2.2.2.2.2 j)⟩

/-- A plan for larger floors is a plan for smaller ones. -/
theorem SeedPlan.weaken {X : TermConstruction} {A : TermArgs X} {KS KS' : ℕ} {F F' : SeedFloors}
    {Lt : ℕ} {nW : ℕ+} {cr : ℝ} {kS : InvConsts} (h : SeedPlan A KS F Lt nW cr kS)
    (hKS : KS' ≤ KS) (hF : F.Meets nW kS → F'.Meets nW kS) : SeedPlan A KS' F' Lt nW cr kS := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, le_trans hKS h10, h11, h12, h13, h14, h15, hF h16⟩

/-- **The six parts at one level give the seed clauses statement at that level.** -/
theorem seedAtM_of_parts {X : TermConstruction} (A : TermArgs X) (Kout sXT sZT : ℕ) (nW : ℕ+)
    (cr : ℝ) (kS : InvConsts) (CL Cχ : ℝ) (kW : InvConsts) (cP CP cH Ce Cw : ℝ) (j₀ M : ℕ)
    (hCe : 1 ≤ Ce)
    (hS : SeedStructAtM A sXT sZT nW cr CL Cχ kW cP CP cH Cw j₀ M)
    (hC : SeedCertAtM A sXT sZT nW cr kS CL Cχ kW cP CP cH Cw j₀ M)
    (hK : SeedKernelAtM A sXT sZT nW cr kS CL Cχ kW cP CP cH Cw j₀ M)
    (hE : SeedEnvelopeAtM A sXT sZT nW cr kS CL Cχ kW cP CP cH Cw Ce j₀ M)
    (hQ : SeedQuietAtM A sXT sZT nW cr CL Cχ kW cP CP cH Cw j₀ M)
    (hR : SeedRetainedAtM A Kout sXT sZT nW cr kS CL Cχ kW cP CP cH Cw j₀ M) :
    SeedAtM A Kout sXT sZT nW cr kS CL Cχ kW cP CP cH Ce Cw kS.cker j₀ M := by
  intro D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx
  obtain ⟨hlev, hbirths, hprov, hdepth, horders, hmass⟩ :=
    hS D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx
  obtain ⟨hnat, htags, hgen, hshift, hslot, hcert, hexp, habove⟩ :=
    hC D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx
  have hker := hK D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx
  have henv := hE D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx hnat hcert
  obtain ⟨hatlas, htrans, hfast, hhist⟩ := hQ D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx
  have hret := hR D a lawW PW Gw aM tp lawT Gt' seed rootM rootR seedKc ι hctx
  have hrM : ∀ r, 0 < rootM r := hctx.2.2.2.2.2.2.2.2.2.1
  have hrR : ∀ r, 0 < rootR r := hctx.2.2.2.2.2.2.2.2.2.2
  refine ⟨⟨hrM, hrR, fun law hm hr => ?_⟩, hret⟩
  obtain ⟨hsampled, henvs, hledger, hschur, hpoint⟩ := henv law hm hr
  obtain ⟨hm1, hm2⟩ := hmass law hm hr
  refine ⟨fun P freshK => ⟨hlev, hbirths, hprov, ?_, hdepth, horders, hsampled,
    ⟨hnat, htags P, hgen, hshift, hslot, hcert, henvs, hledger,
      fun v u γ => hker P freshK v u γ, hschur P freshK, hatlas, htrans, hfast, hhist⟩, hexp, habove⟩,
    hpoint, hm1, hm2⟩
  exact le_trans (le_of_lt (lt_trans hm1 (by norm_num))) hCe

/-- The prefix of the parts of the seed clauses statement: lift floors, reserve floor, constant floors, plan, weak
constants, preparation constants. -/
def SeedPartPrefix (B : (X : TermConstruction) → TermArgs X → ℕ → ℕ → ℕ → ℕ → ℕ+ → ℝ →
    InvConsts → ℝ → ℝ → InvConsts → ℝ → ℝ → Prop) : Prop :=
  ∀ X : TermConstruction, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ A : TermArgs X, Λ₀ ≤ A.Λ → A.Valid →
  ∀ Kout : ℕ, ∃ SX SZ : ℕ, ∀ sXT sZT : ℕ, SX ≤ sXT → SZ ≤ sZT →
  ∃ (KS : ℕ) (F : SeedFloors),
  ∀ (Lt : ℕ) (nW : ℕ+) (cr : ℝ) (kS : InvConsts), SeedPlan A KS F Lt nW cr kS →
  ∀ (cK CL Cχ : ℝ) (kW : InvConsts), 0 < cK → kW.c₀ = cK → IsWeakAllocation kW kS Lt →
  ∀ (cP CP : ℝ), 0 < cP → B X A Kout sXT sZT Lt nW cr kS CL Cχ kW cP CP

/-- The structure part's constants: the law constant `c_H`. -/
def SeedStructBlock {X : TermConstruction} (A : TermArgs X) (sXT sZT : ℕ) (nW : ℕ+) (cr CL Cχ : ℝ)
    (kW : InvConsts) (cP CP : ℝ) : Prop :=
  ∃ cH : ℝ, 0 < cH ∧ cH ≤ 1 ∧ ∀ Cw : ℝ, 0 ≤ Cw → ∀ j₀ : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    SeedStructAtM A sXT sZT nW cr CL Cχ kW cP CP cH Cw j₀ M

/-- The certification part's constants: a floor for `C_w` and a carrier pair. -/
def SeedCertBlock {X : TermConstruction} (A : TermArgs X) (sXT sZT : ℕ) (nW : ℕ+) (cr : ℝ)
    (kS : InvConsts) (CL Cχ : ℝ) (kW : InvConsts) (cP CP : ℝ) : Prop :=
  ∀ cH : ℝ, 0 < cH → ∃ (Cw₀ CHe Υe : ℝ), 0 ≤ Cw₀ ∧ 1 ≤ CHe ∧ 0 < Υe ∧ ∀ Cw : ℝ, Cw₀ ≤ Cw →
    ∀ j₀ : ℕ, IsCarrierStart X.α X.q A.Λ A.bw CHe Υe j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      SeedCertAtM A sXT sZT nW cr kS CL Cχ kW cP CP cH Cw j₀ M

/-- The kernel part has no constants of its own (the plan's `k_S` meets the floors). -/
def SeedKernelBlock {X : TermConstruction} (A : TermArgs X) (sXT sZT : ℕ) (nW : ℕ+) (cr : ℝ)
    (kS : InvConsts) (CL Cχ : ℝ) (kW : InvConsts) (cP CP : ℝ) : Prop :=
  ∀ cH Cw : ℝ, 0 < cH → 0 ≤ Cw → ∀ j₀ : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
    SeedKernelAtM A sXT sZT nW cr kS CL Cχ kW cP CP cH Cw j₀ M

/-- The envelope part's constants: a floor for `C_e` and a carrier pair. -/
def SeedEnvelopeBlock {X : TermConstruction} (A : TermArgs X) (sXT sZT : ℕ) (nW : ℕ+) (cr : ℝ)
    (kS : InvConsts) (CL Cχ : ℝ) (kW : InvConsts) (cP CP : ℝ) : Prop :=
  ∀ cH Cw : ℝ, 0 < cH → 0 ≤ Cw → ∃ (Ce₀ CHe Υe : ℝ), 1 ≤ CHe ∧ 0 < Υe ∧ ∀ Ce : ℝ, Ce₀ ≤ Ce →
    ∀ j₀ : ℕ, IsCarrierStart X.α X.q A.Λ A.bw CHe Υe j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      SeedEnvelopeAtM A sXT sZT nW cr kS CL Cχ kW cP CP cH Cw Ce j₀ M

/-- The quiet part's constants: a carrier pair. -/
def SeedQuietBlock {X : TermConstruction} (A : TermArgs X) (sXT sZT : ℕ) (nW : ℕ+) (cr CL Cχ : ℝ)
    (kW : InvConsts) (cP CP : ℝ) : Prop :=
  ∀ cH Cw : ℝ, 0 < cH → 0 ≤ Cw → ∃ (CHe Υe : ℝ), 1 ≤ CHe ∧ 0 < Υe ∧
    ∀ j₀ : ℕ, IsCarrierStart X.α X.q A.Λ A.bw CHe Υe j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      SeedQuietAtM A sXT sZT nW cr CL Cχ kW cP CP cH Cw j₀ M

/-- The retained part: a floor for `C_w` and a carrier pair, as for the certification (the certificate of `Gt'`, `termCertBlock_exists`, needs
both). -/
def SeedRetainedBlock {X : TermConstruction} (A : TermArgs X) (Kout sXT sZT : ℕ) (nW : ℕ+)
    (cr : ℝ) (kS : InvConsts) (CL Cχ : ℝ) (kW : InvConsts) (cP CP : ℝ) : Prop :=
  ∀ cH : ℝ, 0 < cH → ∃ (Cw₀ CHe Υe : ℝ), 0 ≤ Cw₀ ∧ 1 ≤ CHe ∧ 0 < Υe ∧ ∀ Cw : ℝ, Cw₀ ≤ Cw →
    ∀ j₀ : ℕ, IsCarrierStart X.α X.q A.Λ A.bw CHe Υe j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      SeedRetainedAtM A Kout sXT sZT nW cr kS CL Cχ kW cP CP cH Cw j₀ M

/-- **Part 1, structure.** For an empty seed the sums are `0 < 5/6`. -/
def SeedStructPart : Prop :=
  SeedPartPrefix fun _ A _ sXT sZT _ nW cr _ CL Cχ kW cP CP => SeedStructBlock A sXT sZT nW cr CL Cχ kW cP CP

/-- **Part 2, certification** (certification at the terminal anchor; `successor_torus_compatible`;
the weak registry). -/
def SeedCertPart : Prop :=
  SeedPartPrefix fun _ A _ sXT sZT _ nW cr kS CL Cχ kW cP CP =>
    SeedCertBlock A sXT sZT nW cr kS CL Cχ kW cP CP

/-- **Part 3, kernels.** -/
def SeedKernelPart : Prop :=
  SeedPartPrefix fun _ A _ sXT sZT _ nW cr kS CL Cχ kW cP CP =>
    SeedKernelBlock A sXT sZT nW cr kS CL Cχ kW cP CP

/-- **Part 4, envelopes** (`ContextStageEnvelopesStatement`, `kernel_schur_of_identity_prices`).
For an empty seed the ledger is zero. -/
def SeedEnvelopePart : Prop :=
  SeedPartPrefix fun _ A _ sXT sZT _ nW cr kS CL Cχ kW cP CP =>
    SeedEnvelopeBlock A sXT sZT nW cr kS CL Cχ kW cP CP

/-- **Part 5, the quiet structure** (stage-generic quiet matching). A window with no
pulse lies inside one quiet interval. -/
def SeedQuietPart : Prop :=
  SeedPartPrefix fun _ A _ sXT sZT _ nW cr _ CL Cχ kW cP CP => SeedQuietBlock A sXT sZT nW cr CL Cχ kW cP CP

/-- **Part 6, the retained certificates** (the kernel-price lemma on the retained family). -/
def SeedRetainedPart : Prop :=
  SeedPartPrefix fun _ A Kout sXT sZT _ nW cr kS CL Cχ kW cP CP =>
    SeedRetainedBlock A Kout sXT sZT nW cr kS CL Cχ kW cP CP

/-- The constants of the seed clauses statement from the blocks of the six parts. -/
theorem seed_consts_of_blocks {X : TermConstruction} (A : TermArgs X) (Kout sXT sZT : ℕ) (nW : ℕ+)
    (cr : ℝ) (kS : InvConsts) (CL Cχ : ℝ) (kW : InvConsts) (cP CP : ℝ)
    (hAnn : ∀ k, 0 ≤ ocA X.α X.q A.Λ k) (hTnn : ∀ k, 0 ≤ ocTauPP X.α X.q A.Λ k)
    (hS : SeedStructBlock A sXT sZT nW cr CL Cχ kW cP CP)
    (hC : SeedCertBlock A sXT sZT nW cr kS CL Cχ kW cP CP)
    (hK : SeedKernelBlock A sXT sZT nW cr kS CL Cχ kW cP CP)
    (hE : SeedEnvelopeBlock A sXT sZT nW cr kS CL Cχ kW cP CP)
    (hQ : SeedQuietBlock A sXT sZT nW cr CL Cχ kW cP CP)
    (hR : SeedRetainedBlock A Kout sXT sZT nW cr kS CL Cχ kW cP CP) :
    ∃ cH : ℝ, 0 < cH ∧ cH ≤ 1 ∧ ∃ Cw₀ : ℝ, ∀ Cw : ℝ, Cw₀ ≤ Cw →
    ∃ (Ce CHe Υe : ℝ) (cker : ℕ → ℝ), 1 ≤ Ce ∧ 0 ≤ Cw ∧ 1 ≤ CHe ∧ 0 < Υe ∧
    ∀ j₀ : ℕ, IsCarrierStart X.α X.q A.Λ A.bw CHe Υe j₀ → ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      SeedAtM A Kout sXT sZT nW cr kS CL Cχ kW cP CP cH Ce Cw cker j₀ M := by
  obtain ⟨cH, hcH, hcH1, hS'⟩ := hS
  obtain ⟨Cw₀, CHc, Υc, hCw₀, hCHc, hΥc, hC'⟩ := hC cH hcH
  obtain ⟨CwR, CHr, Υr, -, hCHr, hΥr, hR'⟩ := hR cH hcH
  refine ⟨cH, hcH, hcH1, max Cw₀ CwR, fun Cw hCwCR => ?_⟩
  have hCwC : Cw₀ ≤ Cw := le_trans (le_max_left _ _) hCwCR
  have hCwR : CwR ≤ Cw := le_trans (le_max_right _ _) hCwCR
  have hCw : 0 ≤ Cw := le_trans hCw₀ hCwC
  obtain ⟨Ce₀, CHe, Υe, hCHe, hΥe, hE'⟩ := hE cH Cw hcH hCw
  obtain ⟨CHq, Υq, hCHq, hΥq, hQ'⟩ := hQ cH Cw hcH hCw
  refine ⟨max Ce₀ 1, max (max CHc CHr) (max CHe CHq), max (max Υc Υr) (max Υe Υq), kS.cker,
    le_max_right _ _, hCw, le_trans hCHc (le_trans (le_max_left _ _) (le_max_left _ _)),
    lt_of_lt_of_le hΥc (le_trans (le_max_left _ _) (le_max_left _ _)), fun j₀ hj₀ => ?_⟩
  have hjC : IsCarrierStart X.α X.q A.Λ A.bw CHc Υc j₀ :=
    IsCarrierStart.mono hAnn hTnn (le_trans (le_max_left _ _) (le_max_left _ _))
      (le_trans (le_max_left _ _) (le_max_left _ _)) (zero_le_one.trans hCHc) hΥc.le hj₀
  have hjR : IsCarrierStart X.α X.q A.Λ A.bw CHr Υr j₀ :=
    IsCarrierStart.mono hAnn hTnn (le_trans (le_max_right _ _) (le_max_left _ _))
      (le_trans (le_max_right _ _) (le_max_left _ _)) (zero_le_one.trans hCHr) hΥr.le hj₀
  have hjE : IsCarrierStart X.α X.q A.Λ A.bw CHe Υe j₀ :=
    IsCarrierStart.mono hAnn hTnn (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_trans (le_max_left _ _) (le_max_right _ _)) (zero_le_one.trans hCHe) hΥe.le hj₀
  have hjQ : IsCarrierStart X.α X.q A.Λ A.bw CHq Υq j₀ :=
    IsCarrierStart.mono hAnn hTnn (le_trans (le_max_right _ _) (le_max_right _ _))
      (le_trans (le_max_right _ _) (le_max_right _ _)) (zero_le_one.trans hCHq) hΥq.le hj₀
  obtain ⟨M1, h1⟩ := hS' Cw hCw j₀
  obtain ⟨M2, h2⟩ := hC' Cw hCwC j₀ hjC
  obtain ⟨M3, h3⟩ := hK cH Cw hcH hCw j₀
  obtain ⟨M4, h4⟩ := hE' (max Ce₀ 1) (le_max_left _ _) j₀ hjE
  obtain ⟨M5, h5⟩ := hQ' j₀ hjQ
  obtain ⟨M6, h6⟩ := hR' Cw hCwR j₀ hjR
  refine ⟨max (max M1 M2) (max (max M3 M4) (max M5 M6)), fun M hM => ?_⟩
  exact seedAtM_of_parts A Kout sXT sZT nW cr kS CL Cχ kW cP CP cH (max Ce₀ 1) Cw j₀ M
    (le_max_right _ _) (h1 M (m2l (m2l hM))) (h2 M (m2r (m2l hM))) (h3 M (m2l (m2l (m2r hM))))
    (h4 M (m2r (m2l (m2r hM)))) (h5 M (m2l (m2r (m2r hM)))) (h6 M (m2r (m2r (m2r hM))))

/-- **The seed clauses statement from its six parts** (and the positivity of the scales). -/
theorem seedClauses_of_parts (hS : SeedStructPart) (hC : SeedCertPart) (hK : SeedKernelPart)
    (hE : SeedEnvelopePart) (hQ : SeedQuietPart) (hR : SeedRetainedPart)
    (hsf : ScaleFactsStatement) : SeedClausesStatement := by
  intro X
  obtain ⟨Λ1, h1Λ, hS1⟩ := hS X
  obtain ⟨Λ2, h2Λ, hC1⟩ := hC X
  obtain ⟨Λ3, h3Λ, hK1⟩ := hK X
  obtain ⟨Λ4, h4Λ, hE1⟩ := hE X
  obtain ⟨Λ5, h5Λ, hQ1⟩ := hQ X
  obtain ⟨Λ6, h6Λ, hR1⟩ := hR X
  refine ⟨max (max Λ1 Λ2) (max (max Λ3 Λ4) (max Λ5 Λ6)),
    le_trans h1Λ (le_trans (le_max_left _ _) (le_max_left _ _)), fun A hΛ hA Kout => ?_⟩
  obtain ⟨hAnn, hTnn, -⟩ := hsf X A.Λ (le_trans h1Λ (m2l (m2l hΛ)))
  obtain ⟨SX1, SZ1, hS2⟩ := hS1 A (m2l (m2l hΛ)) hA Kout
  obtain ⟨SX2, SZ2, hC2⟩ := hC1 A (m2r (m2l hΛ)) hA Kout
  obtain ⟨SX3, SZ3, hK2⟩ := hK1 A (m2l (m2l (m2r hΛ))) hA Kout
  obtain ⟨SX4, SZ4, hE2⟩ := hE1 A (m2r (m2l (m2r hΛ))) hA Kout
  obtain ⟨SX5, SZ5, hQ2⟩ := hQ1 A (m2l (m2r (m2r hΛ))) hA Kout
  obtain ⟨SX6, SZ6, hR2⟩ := hR1 A (m2r (m2r (m2r hΛ))) hA Kout
  refine ⟨max (max SX1 SX2) (max (max SX3 SX4) (max SX5 SX6)),
    max (max SZ1 SZ2) (max (max SZ3 SZ4) (max SZ5 SZ6)), fun sXT sZT hX hZ => ?_⟩
  obtain ⟨KS1, F1, hS3⟩ := hS2 sXT sZT (m2l (m2l hX)) (m2l (m2l hZ))
  obtain ⟨KS2, F2, hC3⟩ := hC2 sXT sZT (m2r (m2l hX)) (m2r (m2l hZ))
  obtain ⟨KS3, F3, hK3⟩ := hK2 sXT sZT (m2l (m2l (m2r hX))) (m2l (m2l (m2r hZ)))
  obtain ⟨KS4, F4, hE3⟩ := hE2 sXT sZT (m2r (m2l (m2r hX))) (m2r (m2l (m2r hZ)))
  obtain ⟨KS5, F5, hQ3⟩ := hQ2 sXT sZT (m2l (m2r (m2r hX))) (m2l (m2r (m2r hZ)))
  obtain ⟨KS6, F6, hR3⟩ := hR2 sXT sZT (m2r (m2r (m2r hX))) (m2r (m2r (m2r hZ)))
  refine ⟨max (max KS1 KS2) (max (max KS3 KS4) (max KS5 KS6)),
    (F1.sup F2).sup ((F3.sup F4).sup (F5.sup F6)), fun Lt nW cr kS hplan => ?_⟩
  intro cK CL Cχ kW hcK hkW hWA cP CP hcP
  exact seed_consts_of_blocks A Kout sXT sZT nW cr kS CL Cχ kW cP CP hAnn hTnn
    (hS3 Lt nW cr kS (hplan.weaken (m2l (m2l le_rfl)) fun h => h.left.left) cK CL Cχ kW hcK hkW hWA
      cP CP hcP)
    (hC3 Lt nW cr kS (hplan.weaken (m2r (m2l le_rfl)) fun h => h.left.right) cK CL Cχ kW hcK hkW hWA
      cP CP hcP)
    (hK3 Lt nW cr kS (hplan.weaken (m2l (m2l (m2r le_rfl))) fun h => h.right.left.left) cK CL Cχ kW
      hcK hkW hWA cP CP hcP)
    (hE3 Lt nW cr kS (hplan.weaken (m2r (m2l (m2r le_rfl))) fun h => h.right.left.right) cK CL Cχ kW
      hcK hkW hWA cP CP hcP)
    (hQ3 Lt nW cr kS (hplan.weaken (m2l (m2r (m2r le_rfl))) fun h => h.right.right.left) cK CL Cχ kW
      hcK hkW hWA cP CP hcP)
    (hR3 Lt nW cr kS (hplan.weaken (m2r (m2r (m2r le_rfl))) fun h => h.right.right.right) cK CL Cχ kW
      hcK hkW hWA cP CP hcP)

end AVRegularity.EntryTerminal.Route
end
end

section
@[expose] public section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.FullLift
open AVRegularity.Construction.Preservation.Buffer
namespace AVRegularity.EntryTerminal.Route

/-! **`TerminalRetainedClauses` of a context-certified stage, from its zero-order data.**

For a stage `G` with a context certificate, slot transversality, naturality and shift invariance,
the last two conjuncts of `TerminalRetainedClauses` (the regularizers at every radius and order
`≤ K`, and the coefficient premises of `kernel_energy_torus`) follow from the zero-order
regularizer of every kernel at every radius (`spatial_regularizer_all_orders`) and the native
coefficient lemmas. The Schur conjunct stays a hypothesis: it is the price statement. For an empty family every clause is vacuous. -/

/-- **The retained clauses from the native lemmas and the Schur bound.** -/
theorem terminalRetained_of_native {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (lawT : BirthLaw) (Pt : ProvParams) (seedKt freshKt : ℕ → KernelSpec)
    (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀) (cker : ℕ → ℝ) (M K : ℕ) (cr tp tf : ℝ)
    (G : GenStage D ScalarH Dm b j₀) {kI : InvConsts} {Mn : ℕ}
    (hG : G.IsContextCertified kI) (hpar : G.IsSlotTransverse) (hnat : G.IsNatural Mn)
    (hshift : G.IsShiftInvariant) (hΛ : 1 ≤ D.Λ) (hi : 1 ≤ G.level) (hj : j₀ ≤ G.level)
    (hb : 0 < b) (hε : 0 < D.eps (G.level - 1))
    (hm : ∀ v : CompIn G.comps, 0 ≤ compReserve kI v.1)
    (hm2 : ∀ v : CompIn G.comps, compReserve kI v.1 ≤ 2)
    (hρ : 0 < D.termRho cr M) (hρε : D.termRho cr M ≤ D.eps (G.level - 1))
    (hSzero : ∀ v u (γ : G.fam.Γ v u), ∀ ϱ : ℝ, 0 < ϱ →
      IsSpatialRegularizerTorus ϱ 0 Dm tp tf cker (G.kernelOf Pt seedKt freshKt v u γ).width
        (G.sysS Pt seedKt freshKt φ₀ hφ₀ v u γ))
    (hschur : ∀ kk ≤ K, SchurBound (1 / 8) (kernelSchurMatrix (ι := CompIn G.comps)
      (h := fun v => ScalarH v.1.root) (Γ := G.fam.Γ) (G := fun _ u _ => ScalarH u.1.root)
      (D.κ (M - 1)) (D.termRho cr M) (fun v => G.mass lawT v) kk Dm tp tf cker
      (fun v u γ => (G.kernelOf Pt seedKt freshKt v u γ).width)
      (fun _ u _ => ContinuousLinearMap.id ℝ (ScalarH u.1.root))
      (fun v u γ d => G.physCoeff v u γ d.1))) :
    TerminalRetainedClauses lawT Pt seedKt freshKt φ₀ hφ₀ cker M K cr tp tf G := by
  refine ⟨hschur, fun v u γ ϱ hϱ kk _ => ?_, fun v u γ d => ?_⟩
  · exact spatial_regularizer_all_orders ϱ Dm tp tf cker _ _ (hSzero v u γ ϱ hϱ) kk
  · refine ⟨native_physCoeff_joint_measurable_of_context hG hpar hnat hΛ hi hj hb hε tp tf hm hm2
      v u γ d.1, fun t ht => native_physCoeff_all_order_smooth hG hpar hnat hi hj hb hε tp tf
      v u γ (hm v) (hm2 v) K d.1 t ht, fun t _ => native_physCoeff_periodic hnat hshift v u γ d.1 t,
      native_physCoeff_all_order_seminorm_finite hG hpar hnat hi hj hb hε tp tf v u γ (hm v)
      (hm2 v) _ hρ hρε K d.1⟩

end AVRegularity.EntryTerminal.Route
end
end
