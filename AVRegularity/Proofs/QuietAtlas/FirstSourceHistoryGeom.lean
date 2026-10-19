-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.QuietAtlas.SummedTransition
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev Filter Topology
open scoped Classical
namespace AVRegularity.Providers.QuietAtlas

/-! **Quiet matching of an actual successor: the named statements.**

The quiet-matching clause of an actual successor is needed by the terminal seed (the successor of
the weak stage) and by the cascade (`StageQuietMatchingClause`). Both need the same
three pieces, stated here once for every `IsActualSuccessor`. This file holds statements only.

* `ActualSuccessorWitness`: the witness of `IsActualSuccessor` as data: the source equivalence
  `e`, the lift coefficients `Cc`, `Cc0`, and the flux clauses. `IsActualSuccessor` is its
  `Nonempty` (`isActualSuccessor_iff_nonempty_witness`).
* `successorQuietSource`: the quiet source of an identity of the successor. It is the first source
  for a diagonal letter, and a transfer of the parent's sources otherwise. These are the two flux
  clauses of `IsActualSuccessor`, read as `QuietSource.array` at the level `G'.level + 1 = G.level`.
* **(a)** `SuccessorQuietPresentationStatement`: a `QuietPresentation` of the successor with these
  sources. It reads only the successor's own witness; no presentation of the parent is needed.
* **(b)** `FinerHistoryInvariant` of that presentation (`successorFinerHistory_of_covariant`), from
  the parent's carried invariant `StageHistoryInvariant G Mtop`, its recenter covariance, and the
  separately named first-source hypothesis `DiagLabelHistoryInvariant`.
* **(c)** `FirstSourceArrayFormStatement`: `FirstSourceArrayForm` of that presentation, packaging
  `firstSourceFlux_applyArr`.
* **Assembly**: `QuietMatchingOn` of the successor. It goes through (a), (b), (c),
  `quietPhaseBlind_of_finerHistory`, `quietReanchors_of_finerHistory` and
  `quietMatching_of_firstSource` (`successorQuietMatching_of_generated`).
* `FirstSourceHistoryStatement`: the first-source analog of `transferAt_eq_of_histEq`. From it,
  `quietHistoryPreservation_of_firstSourceHistory` carries `StageHistoryInvariant` to any presented
  stage (transfers and first sources) from its `FinerHistoryInvariant`: the cascade's step from a
  parent to its successor. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **The witness of `IsActualSuccessor`, as data**: the source equivalence, the lift
coefficients, and the clauses of the actual construction. -/
structure ActualSuccessorWitness (D : OCData) (P : ProvParams) (Mn : SuccMenu)
    (G G' : GenStage D hr Dm b j₀) where
  e : ∀ v' u', G'.fam.Γ v' u' ≃ {s : SuccSource G //
    s.Valid Mn.A Mn.J ∧ s.srcComp G.level = u'.1 ∧ s.tgtComp G.level = v'.1}
  Cc : ∀ s : SuccSource G, ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ)
  Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)
  lifts : ∀ s : SuccSource G, s.IsLiftFamily Mn (Cc s)
  diag : IsDiagLifts D Dm b j₀ Mn G.level Cc0
  clauses : ∀ v' u' (γ' : G'.fam.Γ v' u'),
    G'.prov v' u' γ' = (e v' u' γ').1.prov G.level ∧
    (G'.fam.identity v' u' γ').map = rootPathMap hr u'.1.root (e v' u' γ').1.maps v'.1.root ∧
    ((¬ (e v' u' γ').1.IsDiag →
      ∀ (p : OddSlot) (c : StageCtx D b j₀ G'.level p) (d : ℕ) (I : DerivativeWord2 (d - 1))
        (t : ℝ) (X z : Vec 2), 2 ≤ d →
        G'.fam.flux p c v' u' γ' d I t X z =
          if IsAdmissibleChain D b j₀ G'.level p.1 (c.1.recenter D (D.eps (G'.level - 1) • X))
          then transferAt D G.level p.1 ((e v' u' γ').1.lam G.level Mn.η0)
            (((e v' u' γ').1.prov G.level).tags P).order
            ((e v' u' γ').1.fluxOp (Mn.lenFactor * liftLength D G.level) Mn.anchor
              (Cc (e v' u' γ').1)) t
            (c.1.recenter D (D.eps (G'.level - 1) • X)) z d I
          else 0) ∧
     ((e v' u' γ').1.IsDiag →
      ∀ (p : OddSlot) (c : StageCtx D b j₀ G'.level p) (d : ℕ) (I : DerivativeWord2 (d - 1))
        (t : ℝ) (X z : Vec 2), 2 ≤ d →
        G'.fam.flux p c v' u' γ' d I t X z =
          if IsAdmissibleChain D b j₀ G'.level p.1 (c.1.recenter D (D.eps (G'.level - 1) • X))
          then ((e v' u' γ').1.lam G.level Mn.η0 *
              (D.κ G'.level * D.eps G'.level ^ (d - 2))⁻¹) •
            fluxCoeff (firstSourceFlux D b j₀ Dm G.level (Mn.lenFactor * liftLength D G.level)
              Mn.N Mn.p Mn.anchor Cc0 t
              (c.1.recenter D (D.eps (G'.level - 1) • X)) z) d I 0
          else 0))

/-- `IsActualSuccessor` is the nonemptiness of its witness, together with the level, component,
naturality, tag and export clauses. -/
theorem isActualSuccessor_iff_nonempty_witness (P : ProvParams) (Mn : SuccMenu)
    (G G' : GenStage D hr Dm b j₀) :
    IsActualSuccessor D P Mn G G' ↔
      1 ≤ G.level ∧ G'.level = G.level - 1 ∧
        G'.comps = succExtComps G.level Mn.A Mn.J G.comps ∧ G'.IsNatural Mn.M ∧ G'.HasTags P ∧
        (∀ (i : ℕ) (p : ℤ) (e : Gen .ctx i p), G'.exports e ↔ G.exports e) ∧
        Nonempty (ActualSuccessorWitness D P Mn G G') := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, e, Cc, Cc0, hl, hd, hc⟩
    exact ⟨h1, h2, h3, h4, h5, h6, ⟨⟨e, Cc, Cc0, hl, hd, hc⟩⟩⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, ⟨w⟩⟩
    exact ⟨h1, h2, h3, h4, h5, h6, w.e, w.Cc, w.Cc0, w.lifts, w.diag, w.clauses⟩

/-- **The quiet source of an identity of the successor**: the first source for a diagonal letter,
the transfer of the parent's sources otherwise. -/
def successorQuietSource {P : ProvParams} {Mn : SuccMenu} {G G' : GenStage D hr Dm b j₀}
    (w : ActualSuccessorWitness D P Mn G G') (v' u' : CompIn G'.comps) (γ' : G'.fam.Γ v' u') :
    QuietSource :=
  if (w.e v' u' γ').1.IsDiag then
    .first ((w.e v' u' γ').1.lam G.level Mn.η0) (Mn.lenFactor * liftLength D G.level) Mn.anchor
      Mn.N Mn.p w.Cc0
  else
    .transfer ((w.e v' u' γ').1.lam G.level Mn.η0)
      (((w.e v' u' γ').1.prov G.level).tags P).order
      ((w.e v' u' γ').1.fluxOp (Mn.lenFactor * liftLength D G.level) Mn.anchor
        (w.Cc (w.e v' u' γ').1))

/-- **(a) The quiet presentation of an actual successor**: its flux clauses are the source arrays
of `successorQuietSource` at the level `G'.level + 1 = G.level`. -/
def SuccessorQuietPresentationStatement : Prop :=
  ∀ (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀),
    1 ≤ G.level → G'.level = G.level - 1 → ∀ w : ActualSuccessorWitness D P Mn G G',
      ∃ P' : QuietPresentation G', P'.source = successorQuietSource w

/-- **The history dependence of the diagonal-letter flux** (the first-source hypothesis of (b)).
The label flux of the grade-zero lifts at the appended children of level `m`, as a germ, depends
only on the history geometry of the context over the availability interval.

The hypothesis comes from the successor's own witness, not from a stage invariant. `IsDiagLifts`
makes `Cc0 k A` the lift sequence of the edgeless family
`familyLiftData D m k A ρ (fun _ _ _ => [])`. Its data read only the history
(`familyLiftData_G_eq_of_histEq`), and lift sequences are unique. This is the argument of
`pathMeanFlux_germ_of_histEq` with no path, so no `StageHistoryInvariant` is used. The cascade
(`IsStageInvariant`) and the terminal entry (`IsWeakStage`) can therefore both supply it through
`IsActualSuccessor`'s `IsDiagLifts`. -/
def DiagLabelHistoryInvariant (D : OCData) (Dm : ℕ) (b : ℝ) (j₀ m : ℕ) (ρ : ℝ) (N : ℕ)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) (Mtop : ℕ) : Prop :=
  ∀ n ∈ insert 2 (Set.Icc 3 (N + 1)), ∀ (k : OddSlot) (ch ch' : StageCtx D b j₀ m k),
    SameHistoryGeometry D Mtop m k.1 ch.1 ch'.1 →
    ∀ t ∈ ocPulseWindow D.α D.q D.Λ m k.1, ∀ f : Vec 2 → ℝ,
      diagLabelFlux D Dm m ρ Cc0 k.1 ch.1 n t f =ᶠ[𝓝 0] diagLabelFlux D Dm m ρ Cc0 k.1 ch'.1 n t f

/-- **(c) The array form of the first sources of an actual successor**: `firstSourceFlux_applyArr`
packaged as `FirstSourceArrayForm` on every set of times. -/
def FirstSourceArrayFormStatement : Prop :=
  ∀ (P : ProvParams) (Mn : SuccMenu) (G G' : GenStage D hr Dm b j₀),
    1 ≤ G.level → G'.level = G.level - 1 → IsFastProfile D.ζ → 1 ≤ D.Λ →
    0 < D.cellScaleSq G.level → 1 ≤ Mn.N → 2 * Mn.p + Dm + 2 ≤ Mn.sX →
    2 * Mn.p + Dm + 2 ≤ Mn.sZ → Mn.lenFactor * liftLength D G.level ≠ 0 →
    ∀ (w : ActualSuccessorWitness D P Mn G G') (P' : QuietPresentation G'),
      P'.source = successorQuietSource w → ∀ U : Set ℝ, FirstSourceArrayForm G' P' U

/-! ### Carrying the invariant to a stage with first sources -/

/-- **The first-source analog of `transferAt_eq_of_histEq`**: two
admissible contexts of level `m` with the same history geometry have the same first-source array,
when the finer diagonal-label fluxes of every degree `n ∈ {2} ∪ [3, N+1]` read only the history (the
`.first` case of `FinerHistoryInvariant`). The flux reads, besides those, the centered map of the
context and its inverse at `t`, the context strain at the recentered contexts, and time-only
covariance and reference letters. -/
def FirstSourceHistoryStatement : Prop :=
  ∀ (D : OCData) (Dm : ℕ) (b : ℝ) (j₀ : ℕ), 1 ≤ D.Λ → IsFastProfile D.ζ → 0 < b →
    (∀ k : ℕ, j₀ ≤ k + 1 →
      2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ b / (64 * (8 * Real.pi ^ 2))) →
    ∀ {Mtop m : ℕ}, m < Mtop → ∀ {p : ℤ} {C C' : RealChain},
    IsAdmissibleChain D b j₀ m p C → IsAdmissibleChain D b j₀ m p C' →
    HistEq (C.geom D) (C'.geom D) (availInterval D Mtop m p) →
    ∀ (ρ s₀ : ℝ) (N pc : ℕ) (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)),
    (∀ n ∈ (insert 2 (Set.Icc 3 (N + 1)) : Set ℕ), ∀ k : ℤ, Odd k → ∀ A A' : RealChain,
      IsAdmissibleChain D b j₀ (m + 1) k A → IsAdmissibleChain D b j₀ (m + 1) k A' →
      SameHistoryGeometry D Mtop (m + 1) k A A' →
      ∀ t ∈ ocPulseWindow D.α D.q D.Λ (m + 1) k, ∀ f : Vec 2 → ℝ,
        diagLabelFlux D Dm (m + 1) ρ Cc0 k A n t f =ᶠ[𝓝 0]
          diagLabelFlux D Dm (m + 1) ρ Cc0 k A' n t f) →
    ∀ {t : ℝ}, t ∈ ocPulseWindow D.α D.q D.Λ m p →
    ∀ (z : Vec 2) (d : ℕ) (I : DerivativeWord2 (d - 1)),
      fluxCoeff (firstSourceFlux D b j₀ Dm (m + 1) ρ N pc s₀ Cc0 t C z) d I 0 =
        fluxCoeff (firstSourceFlux D b j₀ Dm (m + 1) ρ N pc s₀ Cc0 t C' z) d I 0

/-- **One-passage preservation of the carried invariant for any presentation**, transfers and
first sources, from `FirstSourceHistoryStatement`. The transfer case is
`transferAt_eq_of_histEq`; the rest is the proof of `quietHistoryPreservation_of_allTransfer_core`.
-/
theorem quietHistoryPreservation_of_firstSourceHistory (hfirst : FirstSourceHistoryStatement)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hb : 0 < b)
    (hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
      2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ b / (64 * (8 * Real.pi ^ 2)))
    (G : GenStage D hr Dm b j₀) (P : QuietPresentation G) (Mtop : ℕ) (hlt : G.level < Mtop)
    (hF : FinerHistoryInvariant G P Mtop) : StageHistoryInvariant G Mtop := by
  intro p ch ch' hsame t ht v u γ d I z
  by_cases hd : 2 ≤ d ∧ d ≤ (G.fam.identity v u γ).maxOrder
  swap
  · rw [G.fam.flux_zero p ch v u γ d I hd, G.fam.flux_zero p ch' v u γ d I hd]
  have hl : ch.1.WellSlotted := ch.2.2.2.1
  have hl' : ch'.1.WellSlotted := ch'.2.2.2.1
  have hanc : (ch.1.geom D).2.2 = (ch'.1.geom D).2.2 := by
    rw [geom_anchor D ch.1 hl, geom_anchor D ch'.1 hl', ch.2.1, ch.2.2.2.2.1, ch'.2.1,
      ch'.2.2.2.2.1]
  have hh := (histEq_iff_sameHistory D ch.1 ch'.1 hanc).mpr hsame
  have htend : Tendsto (fun Y : Vec 2 => D.eps (G.level - 1) • Y) (𝓝 0) (𝓝 0) := by
    have := (continuous_const_smul (D.eps (G.level - 1))).tendsto (0 : Vec 2)
    rwa [smul_zero] at this
  have hev := (htend.eventually (GenSem.recenter_eventually D hζ b j₀ G.level p.1 ch.2)).and
    (htend.eventually (GenSem.recenter_eventually D hζ b j₀ G.level p.1 ch'.2))
  have hFv := hF v u γ
  filter_upwards [hev] with Y hY
  rw [P.represents p ch v u γ d I t Y z hd.1, P.represents p ch' v u γ d I t Y z hd.1]
  split_ifs with h1 h2 h2
  · have hrh := histEq_recenter D hζ hl hl' hh (D.eps (G.level - 1) • Y)
    rcases hsrc : P.source v u γ with ⟨lam, order, fop⟩ | ⟨lam, ρ, s₀, N, pc, Cc0⟩
    · have hF' := hFv 0 (by rw [hsrc]; rfl)
      rw [hsrc] at hF'
      simp only [QuietSource.finer] at hF'
      simp only [QuietSource.array]
      exact transferAt_eq_of_histEq D hΛ hζ hb hstart hlt hY.1 hY.2 hrh
        (fun k hk A A' hA hA' hs t' ht' f => hF' ⟨k, hk⟩ ⟨A, hA⟩ ⟨A', hA'⟩ hs t' ht' f)
        lam order ht z d I
    · simp only [QuietSource.array]
      rw [hfirst D Dm b j₀ hΛ hζ hb hstart hlt hY.1 hY.2 hrh ρ s₀ N pc Cc0
        (fun n hn k hk A A' hA hA' hs t' ht' f => by
          have hF' := hFv n (by rw [hsrc]; exact hn)
          rw [hsrc] at hF'
          simp only [QuietSource.finer] at hF'
          exact hF' ⟨k, hk⟩ ⟨A, hA⟩ ⟨A', hA'⟩ hs t' ht' f) ht z d I]
  · exact absurd hY.2 h2
  · exact absurd hY.1 h1
  · rfl

end AVRegularity.Providers.QuietAtlas
end

section
open Homogenization Filter Topology
namespace AVRegularity.Providers.QuietAtlas

/-! **What the first-source flux reads of its context, under equal history geometry.**
For two chains with the same history geometry on a set `I`:
* the centered maps and their inverses agree at every time of `I` (`famMap_eq_of_histEq`,
  `famMapInv_eq_of_famMap_eq`);
* the time derivatives of the Jacobians agree at every time of a nondegenerate closed interval
  inside `I`, endpoints included (`deriv_famJac_eq_of_histEq`). The Jacobian is `C¹` in time for
  every chain (`geomJacC1_geom`), so the derivative is the one-sided derivative within the
  interval, which the interval determines. No interior condition on the time is needed;
* hence the context strains agree, at every recentering (`contextStrain_eq_of_histEq`).
The covariance operator and its polynomials only read germs (`covOperator_eventuallyEq`,
`covPolyQ_eq_of_eventuallyEq`). -/

variable (D : OCData)

/-- The entries of the Jacobian of a chain are differentiable in time. -/
theorem differentiable_famJac (hζ : IsFastProfile D.ζ) (ch : RealChain) (a b : Fin 2) :
    Differentiable ℝ (fun u => ch.famJac D u a b) := by
  have h1 := (GenSem.geomJacC1_geom D hζ ch (ch.geom D).2.2).differentiable one_ne_zero
  have h2 : Differentiable ℝ (fun u : ℝ => ((u, (ch.geom D).2.1) : ℝ × Vec 2)) :=
    differentiable_id.prodMk (differentiable_const _)
  have h3 : Differentiable ℝ (fun u : ℝ =>
      fderiv ℝ (fun y => (ch.geom D).1 u y (ch.geom D).2.2) (ch.geom D).2.1 (basisVec b)) :=
    fun u => ((h1.comp h2) u).clm_apply (differentiableAt_const _)
  intro u
  exact differentiableAt_pi.1 (h3 u) a

/-- **The time derivative of the Jacobian is read on any nondegenerate closed interval of the
history**, endpoints included. -/
theorem deriv_famJac_eq_of_histEq (hζ : IsFastProfile D.ζ) {ch ch' : RealChain} {I : Set ℝ}
    (h : HistEq (ch.geom D) (ch'.geom D) I) {l r : ℝ} (hlr : l < r)
    (hW : Set.Icc l r ⊆ I) {t : ℝ} (ht : t ∈ Set.Icc l r) (a b : Fin 2) :
    deriv (fun u => ch.famJac D u a b) t = deriv (fun u => ch'.famJac D u a b) t := by
  have hd := ((differentiable_famJac D hζ ch a b) t).hasDerivAt.hasDerivWithinAt
    (s := Set.Icc l r)
  have hd' := ((differentiable_famJac D hζ ch' a b) t).hasDerivAt.hasDerivWithinAt
    (s := Set.Icc l r)
  have hd'' : HasDerivWithinAt (fun u => ch.famJac D u a b)
      (deriv (fun u => ch'.famJac D u a b) t) (Set.Icc l r) t :=
    hd'.congr_of_mem (fun u hu => by rw [famJac_eq_of_histEq D h (hW hu)]) ht
  exact (uniqueDiffOn_Icc hlr t ht).eq_deriv _ hd hd''

/-- Equal history geometry on a nondegenerate closed interval gives the same strain at its
times. -/
theorem famStrain_eq_of_histEq (hζ : IsFastProfile D.ζ) {ch ch' : RealChain} {I : Set ℝ}
    (h : HistEq (ch.geom D) (ch'.geom D) I) {l r : ℝ} (hlr : l < r)
    (hW : Set.Icc l r ⊆ I) {t : ℝ} (ht : t ∈ Set.Icc l r) :
    ch.famStrain D t = ch'.famStrain D t := by
  unfold RealChain.famStrain
  rw [famJac_eq_of_histEq D h (hW ht)]
  congr 1
  ext a b
  simp only [Matrix.of_apply]
  exact deriv_famJac_eq_of_histEq D hζ h hlr hW ht a b

/-- **Equal history geometry gives the same context strain**, at every time of a nondegenerate
closed interval of the history. -/
theorem contextStrain_eq_of_histEq (hζ : IsFastProfile D.ζ) {ch ch' : RealChain}
    (hl : ch.WellSlotted) (hl' : ch'.WellSlotted) {I : Set ℝ}
    (h : HistEq (ch.geom D) (ch'.geom D) I) {l r : ℝ} (hlr : l < r)
    (hW : Set.Icc l r ⊆ I) {t : ℝ} (ht : t ∈ Set.Icc l r) (i : ℕ) (pc : ℤ) (ζ : Vec 2) :
    contextStrain D i pc t ch ζ = contextStrain D i pc t ch' ζ := by
  have hrec : ∀ a c : Fin 2, (fun H : Vec 2 => (ch.recenter D H).famJac D t a c) =
      fun H : Vec 2 => (ch'.recenter D H).famJac D t a c := fun a c =>
    funext fun H => by rw [famJac_eq_of_histEq D (histEq_recenter D hζ hl hl' h H) (hW ht)]
  unfold contextStrain
  rw [famStrain_eq_of_histEq D hζ h hlr hW ht, famJac_eq_of_histEq D h (hW ht)]
  simp only [hrec]

end AVRegularity.Providers.QuietAtlas
end
