-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.QuietAtlas.FirstSourceHistoryGeom
import AVRegularity.Proofs.WeakGen.WeakStageHistory
import AVRegularity.Proofs.GenSem.Op.FamChart
import AVRegularity.Proofs.GenSem.Jet.Chart
public import AVRegularity.Proofs.GenSem.First.Identity
import AVRegularity.Proofs.GenSem.SuccessorGeneration.Terminal
public import AVRegularity.EntryWeak.SourceLocalMetricCongruence
import AVRegularity.Proofs.GenSem.LiftOn.Omega

section
section
/-! **Path means of two chains with the same history** (the path letters). The
weak passage's versions (`WeakGen.pathEdges_slowOpenEdgeEq`, `WeakGen.pathMeanFlux_germ_of_histEq`)
are restated for a stage on any spaces `hr` and any lift slow length `ρ`, as in the successor
(`ρ = lenFactor · liftLength`). The argument is unchanged:
- on the common admissible slow offsets, the lifted path edges agree, through the carried history
  invariant of the stage and its recenter covariance at the output times
  (`FluxRecenterCovariantOnPulses`: from a presentation, or from `IsGenerated`;
  `pathEdges_slowOpenEdgeEq_of_histEq`);
- the metrics agree at the cell times of the window;
- so the lift coefficients agree there (`familyLift_cross_unique`), and so do the path means near
  the label `0` (`pathMeanFlux_germ_of_histEq_gen`).

Unlike the weak lemma, every degree `n` is allowed: the coefficients agree at every grade and
degree, and `Uniqueness.liftFluxX_locEq` replaces the predecessor congruence.

The degenerate cases are included:
- `A = A'`: both sides are the same path mean.
- A path whose identities have maximal order below every edge order: the edges are empty.
- `ρ = 0`: the slow offsets of both carriers are all of `Vec 2`, and the germs are constant. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev Filter Topology

namespace AVRegularity.Providers.QuietAtlas

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The flux at a label is the flux at the label `0` of the recentered context, at the output
times of the slot (`WeakGen.FluxRecenterCovariant` on the pulse windows). -/
def FluxRecenterCovariantOnPulses (G : GenStage D hr Dm b j₀) : Prop :=
  ∀ (p : OddSlot) (c : StageCtx D b j₀ G.level p) v u (γ : G.fam.Γ v u) d
    (I : DerivativeWord2 (d - 1)) t, t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1 → ∀ (Y z : Vec 2)
    (hadm : IsAdmissibleChain D b j₀ G.level p.1 (c.1.recenter D (D.eps (G.level - 1) • Y))),
    G.fam.flux p c v u γ d I t Y z = G.fam.flux p ⟨_, hadm⟩ v u γ d I t 0 z

/-- A generated stage is covariant at the output times. -/
theorem fluxRecenterCovariantOnPulses_of_generated (hζ : IsFastProfile D.ζ)
    {G : GenStage D hr Dm b j₀} (hG : G.IsGenerated) : FluxRecenterCovariantOnPulses G := by
  intro p c v u γ d I t ht Y z hadm
  funext k
  obtain ⟨f, -, hf⟩ := hG p v u γ d I k
  rw [hf c t ht Y z, hf ⟨_, hadm⟩ t ht 0 z]
  simp only [smul_zero, GenSem.recenter_zero D hζ, hadm, ↓reduceIte]

/-- **Equal history geometry gives equal fluxes** at the output times, wherever both recentered
contexts are admissible (`WeakGen.flux_eq_of_histEq` with the covariance on the pulse windows). -/
theorem flux_eq_of_histEq_onPulses (hζ : IsFastProfile D.ζ) {G : GenStage D hr Dm b j₀}
    {Mtop : ℕ} (hcov : FluxRecenterCovariantOnPulses G) (hinv : StageHistoryInvariant G Mtop)
    (p : OddSlot) {A A' : RealChain} (hA : IsAdmissibleChain D b j₀ G.level p.1 A)
    (hA' : IsAdmissibleChain D b j₀ G.level p.1 A')
    (hh : HistEq (A.geom D) (A'.geom D) (availInterval D Mtop G.level p.1)) {t : ℝ}
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1) (v u : CompIn G.comps)
    (γ : G.fam.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1)) {Y : Vec 2}
    (hY : IsAdmissibleChain D b j₀ G.level p.1 (A.recenter D (D.eps (G.level - 1) • Y)))
    (hY' : IsAdmissibleChain D b j₀ G.level p.1 (A'.recenter D (D.eps (G.level - 1) • Y)))
    (z : Vec 2) :
    G.fam.flux p ⟨A, hA⟩ v u γ d I t Y z = G.fam.flux p ⟨A', hA'⟩ v u γ d I t Y z := by
  rw [hcov p ⟨A, hA⟩ v u γ d I t ht Y z hY, hcov p ⟨A', hA'⟩ v u γ d I t ht Y z hY']
  have hl : A.WellSlotted := hA.2.2.1
  have hl' : A'.WellSlotted := hA'.2.2.1
  have hrh := histEq_recenter D hζ hl hl' hh (D.eps (G.level - 1) • Y)
  have hsame := (histEq_iff_sameHistory D _ _ hrh.1).mp hrh
  exact (hinv p ⟨_, hY⟩ ⟨_, hY'⟩ hsame t ht v u γ d I z).eq_of_nhds

/-- **The lifted path edges agree on both carriers.** -/
theorem pathEdges_slowOpenEdgeEq_of_histEq (hζ : IsFastProfile D.ζ) {G : GenStage D hr Dm b j₀}
    {Mtop : ℕ} (hcov : FluxRecenterCovariantOnPulses G) (hinv : StageHistoryInvariant G Mtop)
    (k : OddSlot) {A A' : RealChain} (hA : IsAdmissibleChain D b j₀ G.level k.1 A)
    (hA' : IsAdmissibleChain D b j₀ G.level k.1 A')
    (hh : HistEq (A.geom D) (A'.geom D) (availInterval D Mtop G.level k.1)) {h : ℕ}
    (π : StagePath G h) {ρ : ℝ} (hε : D.eps (G.level - 1) ≠ 0) {U : Set (Vec 2)}
    (hU : U ⊆ ladderOmega D b j₀ G.level k.1 A ρ ∩ ladderOmega D b j₀ G.level k.1 A' ρ)
    {s : ℝ} (hs : D.cellScaleSq G.level * s ∈ ocPulseWindow D.α D.q D.Λ G.level k.1) :
    EntryWeakProofs.SlowOpenEdgeEq U s
      (liftEdges (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) (pathEdges G π k ⟨A', hA'⟩))
      (liftEdges (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) (pathEdges G π k ⟨A, hA⟩)) := by
  intro v u d
  have hsc : ∀ X : Vec 2, D.eps (G.level - 1) • ((ρ / D.eps (G.level - 1)) • X) = ρ • X :=
    fun X => by rw [smul_smul, mul_div_cancel₀ _ hε]
  unfold liftEdges pathEdges
  split_ifs with hvu hd
  · simp only [List.map_cons, List.map_nil, List.forall₂_cons, List.forall₂_nil_left_iff,
      and_true]
    refine ⟨trivial, fun α X hX z => ?_⟩
    obtain ⟨hXA, hXA'⟩ := hU hX
    have hY : IsAdmissibleChain D b j₀ G.level k.1
        (A.recenter D (D.eps (G.level - 1) • ((ρ / D.eps (G.level - 1)) • X))) := by
      rw [hsc]; exact hXA
    have hY' : IsAdmissibleChain D b j₀ G.level k.1
        (A'.recenter D (D.eps (G.level - 1) • ((ρ / D.eps (G.level - 1)) • X))) := by
      rw [hsc]; exact hXA'
    exact (flux_eq_of_histEq_onPulses hζ hcov hinv k hA hA' hh hs _ _ _ d.1 α hY hY' z).symm
  · exact List.Forall₂.nil
  · exact List.Forall₂.nil

/-- **The path means of two chains with the same history agree as germs**, at every degree. -/
theorem pathMeanFlux_germ_of_histEq_gen (hζ : IsFastProfile D.ζ) (hΛ : 1 ≤ D.Λ)
    {G : GenStage D hr Dm b j₀} (hc2 : 0 < D.cellScaleSq G.level) {Mtop : ℕ}
    (hcov : FluxRecenterCovariantOnPulses G) (hinv : StageHistoryInvariant G Mtop) (k : OddSlot)
    {A A' : RealChain} (hA : IsAdmissibleChain D b j₀ G.level k.1 A)
    (hA' : IsAdmissibleChain D b j₀ G.level k.1 A')
    (hh : HistEq (A.geom D) (A'.geom D) (availInterval D Mtop G.level k.1)) {h : ℕ}
    (π : StagePath G h) (ρ : ℝ) (sX sZ sX' sZ' N : ℕ)
    (Cc Dc : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ))
    (hc : IsLiftSequenceOn (ladderOmega D b j₀ G.level k.1 A ρ)
      (familyLiftData D G.level k.1 A ρ (pathEdges G π k ⟨A, hA⟩)) sX sZ
      (D.slotStart G.level k.1 / D.cellScaleSq G.level)
      ((((k.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) N h Cc)
    (hd : IsLiftSequenceOn (ladderOmega D b j₀ G.level k.1 A' ρ)
      (familyLiftData D G.level k.1 A' ρ (pathEdges G π k ⟨A', hA'⟩)) sX' sZ'
      (D.slotStart G.level k.1 / D.cellScaleSq G.level)
      ((((k.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) N h Dc)
    (n : ℕ) {t : ℝ} (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level k.1) (f : Vec 2 → ℝ) :
    pathMeanFlux D G.level ρ (familyLiftData D G.level k.1 A ρ (pathEdges G π k ⟨A, hA⟩)) Cc n t f
      =ᶠ[𝓝 0] pathMeanFlux D G.level ρ
        (familyLiftData D G.level k.1 A' ρ (pathEdges G π k ⟨A', hA'⟩)) Dc n t f := by
  have hε : D.eps (G.level - 1) ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  set U := ladderOmega D b j₀ G.level k.1 A ρ ∩ ladderOmega D b j₀ G.level k.1 A' ρ
  have hU : IsOpen U :=
    (WeakGen.isOpen_ladderOmega b j₀ _ _ _ _).inter (WeakGen.isOpen_ladderOmega b j₀ _ _ _ _)
  have h0U : (0 : Vec 2) ∈ U :=
    ⟨WeakGen.zero_mem_ladderOmega hζ hA ρ, WeakGen.zero_mem_ladderOmega hζ hA' ρ⟩
  have hl : A.WellSlotted := hA.2.2.1
  have hl' : A'.WellSlotted := hA'.2.2.1
  have hwin : ∀ s ∈ Set.Icc (D.slotStart G.level k.1 / D.cellScaleSq G.level)
      ((((k.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level),
      D.cellScaleSq G.level * s ∈ ocPulseWindow D.α D.q D.Λ G.level k.1 :=
    fun s hs => WeakGen.mul_mem_ocPulseWindow hc2 hs
  have hav := ocPulseWindow_subset_availInterval D Mtop G.level k.1
  have hG : ∀ s ∈ Set.Icc (D.slotStart G.level k.1 / D.cellScaleSq G.level)
      ((((k.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level), ∀ X ∈ U,
      (familyLiftData D G.level k.1 A' ρ (pathEdges G π k ⟨A', hA'⟩)).G s X =
        (familyLiftData D G.level k.1 A ρ (pathEdges G π k ⟨A, hA⟩)).G s X :=
    fun s hs X _ => WeakGen.familyLiftData_G_eq_of_histEq hζ hl hl' hh G.level k.1 ρ _ _
      (hav (hwin s hs)) X
  have hE : ∀ s ∈ Set.Icc (D.slotStart G.level k.1 / D.cellScaleSq G.level)
      ((((k.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level),
      EntryWeakProofs.SlowOpenEdgeEq U s
        (familyLiftData D G.level k.1 A' ρ (pathEdges G π k ⟨A', hA'⟩)).edge
        (familyLiftData D G.level k.1 A ρ (pathEdges G π k ⟨A, hA⟩)).edge :=
    fun s hs => pathEdges_slowOpenEdgeEq_of_histEq hζ hcov hinv k hA hA' hh π hε le_rfl (hwin s hs)
  have hE' : ∀ s ∈ Set.Icc (D.slotStart G.level k.1 / D.cellScaleSq G.level)
      ((((k.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level),
      EntryWeakProofs.SlowOpenEdgeEq U s
        (familyLiftData D G.level k.1 A ρ (pathEdges G π k ⟨A, hA⟩)).edge
        (familyLiftData D G.level k.1 A' ρ (pathEdges G π k ⟨A', hA'⟩)).edge :=
    fun s hs => pathEdges_slowOpenEdgeEq_of_histEq hζ hcov hinv k hA' hA hh.symm π hε
      (fun X hX => ⟨hX.2, hX.1⟩) (hwin s hs)
  have hts : (D.cellScaleSq G.level)⁻¹ * t ∈ Set.Icc (D.slotStart G.level k.1 /
      D.cellScaleSq G.level)
      ((((k.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) :=
    WeakGen.inv_mul_mem_liftWindowOf hc2 ht
  have hab := hts.1.trans hts.2
  have hcoef := WeakGen.familyLift_cross_unique D hζ G.level k.1 k.2 A A' ρ _ _ hU
    Set.inter_subset_left Set.inter_subset_right _ _ hab N h sX sZ sX' sZ' Cc Dc hc hd hG hE
  have hev : ∀ᶠ y in 𝓝 (0 : Vec 2), ρ⁻¹ • y ∈ U := by
    have htend : Filter.Tendsto (fun y : Vec 2 => ρ⁻¹ • y) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_const_smul ρ⁻¹).tendsto (0 : Vec 2)
    exact htend (hU.mem_nhds h0U)
  have hP : ∀ hh' ≤ h, ∀ n' m' (α : DerivativeWord2 m'), ∀ X ∈ U,
      Cc hh' n' m' α ((D.cellScaleSq G.level)⁻¹ * t) X =
        Dc hh' n' m' α ((D.cellScaleSq G.level)⁻¹ * t) X :=
    fun hh' hh'h n' m' α X hX => funext fun z => funext fun v => funext fun u =>
      hcoef hh' hh'h n' m' α _ hts X hX z v u
  filter_upwards [hev] with y hy
  have hz : ∀ z k', liftFluxX (familyLiftData D G.level k.1 A ρ (pathEdges G π k ⟨A, hA⟩)) Cc
        (fun _ X => Pi.single (0 : Fin (h + 1)) (f (ρ • X))) h n
        ((D.cellScaleSq G.level)⁻¹ * t) (ρ⁻¹ • y) z k' =
      liftFluxX (familyLiftData D G.level k.1 A' ρ (pathEdges G π k ⟨A', hA'⟩)) Dc
        (fun _ X => Pi.single (0 : Fin (h + 1)) (f (ρ • X))) h n
        ((D.cellScaleSq G.level)⁻¹ * t) (ρ⁻¹ • y) z k' := by
    intro z k'
    refine (Uniqueness.liftFluxX_locEq _ _ h n _ hU hP k' _ hy z).trans ?_
    refine (EntryWeakProofs.liftFluxX_edge_slow_open_congr hU _ _ Dc _ h n _ (hE' _ hts) k' _
      hy z).trans ?_
    exact WeakGen.liftFluxX_data_point_congr
      (Q := {familyLiftData D G.level k.1 A ρ (pathEdges G π k ⟨A, hA⟩) with
        edge := (familyLiftData D G.level k.1 A' ρ (pathEdges G π k ⟨A', hA'⟩)).edge})
      (Q' := familyLiftData D G.level k.1 A' ρ (pathEdges G π k ⟨A', hA'⟩)) rfl rfl rfl Dc _ h n
      _ _ (hG _ hts _ hy).symm z k'
  unfold pathMeanFlux
  simp only [hz]

end AVRegularity.Providers.QuietAtlas
end
end

section
/-! **(a) The quiet presentation of an actual successor.** The flux clauses of the
witness of `IsActualSuccessor` are the source arrays of `successorQuietSource` at the level
`G'.level + 1 = G.level`:
- a transfer clause is `transferAt D G.level`;
- a first-source clause is the normalized first source of level `G.level`.

The degenerate cases are included:
- No identity: the presentation has no source and every clause is vacuous.
- No diagonal letter: every source is a transfer (the weak analog is `weakPassagePresentation`).
- Orders `d < 2`: `represents` asks nothing there. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity.Providers.QuietAtlas

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **(a)**: the presentation of an actual successor by `successorQuietSource`. -/
theorem successorQuietPresentation :
    SuccessorQuietPresentationStatement (hr := hr) (D := D) (Dm := Dm) (b := b) (j₀ := j₀) := by
  intro P Mn G G' hG hG' w
  have hL : G'.level + 1 = G.level := by omega
  refine ⟨⟨successorQuietSource w, fun p c v u γ d I t Y z hd => ?_⟩, rfl⟩
  obtain ⟨-, -, hnd, hdg⟩ := w.clauses v u γ
  unfold successorQuietSource
  by_cases hdiag : (w.e v u γ).1.IsDiag
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hdiag), hdg hdiag p c d I t Y z hd]
    simp only [QuietSource.array]
    rw [hL]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hdiag), hnd hdiag p c d I t Y z hd]
    simp only [QuietSource.array]
    rw [hL]

end AVRegularity.Providers.QuietAtlas
end
end

section
/-! **The history dependence of the diagonal-letter flux.** The grade-zero
lifts `Cc0 k A` (`IsDiagLifts`) are global lift sequences of the edgeless family on `A`. For two
contexts with the same history geometry:
- the lift data agree at the cell times of the window: the metric reads only the history
  (`WeakGen.familyLiftData_G_eq_of_histEq`), and there are no edges;
- so the lifts agree everywhere (`familyLift_cross_unique` on `univ`), and so do the label fluxes.
The first-source hypothesis `DiagLabelHistoryInvariant` of (b) is then a consequence of the
successor's own witness (`w.diag`), with no stage invariant.

The degenerate cases are included:
- `ch = ch'`: reflexive.
- `n = 2`: the lowest mean-flux degree; the argument does not see `n`.
- `Mn.N = 0`: only the degrees `2` and `3` are read, and the lifts are the coarse field. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev Filter Topology

namespace AVRegularity.Providers.QuietAtlas

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The path mean reads the metric of the lift data only at its point. -/
theorem pathMeanFlux_data_point_congr (m : ℕ) (ρ : ℝ) {h : ℕ}
    (Q Q' : LiftOperatorData (Fin (h + 1)) (fun _ => ℝ) Dm) (hη : Q.η = Q'.η) (hvv : Q.v = Q'.v)
    (he : Q.edge = Q'.edge) (Cc : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)) (n : ℕ) (t : ℝ)
    (f : Vec 2 → ℝ) (y : Vec 2)
    (hG : Q.G ((D.cellScaleSq m)⁻¹ * t) (ρ⁻¹ • y) = Q'.G ((D.cellScaleSq m)⁻¹ * t) (ρ⁻¹ • y)) :
    pathMeanFlux D m ρ Q Cc n t f y = pathMeanFlux D m ρ Q' Cc n t f y := by
  have hz : ∀ z k, liftFluxX Q Cc (fun _ X => Pi.single (0 : Fin (h + 1)) (f (ρ • X))) h n
        ((D.cellScaleSq m)⁻¹ * t) (ρ⁻¹ • y) z k =
      liftFluxX Q' Cc (fun _ X => Pi.single (0 : Fin (h + 1)) (f (ρ • X))) h n
        ((D.cellScaleSq m)⁻¹ * t) (ρ⁻¹ • y) z k :=
    fun z k => WeakGen.liftFluxX_data_point_congr Q Q' hη hvv he Cc _ h n _ _ hG z k
  unfold pathMeanFlux
  simp only [hz]

/-- **`DiagLabelHistoryInvariant` from the grade-zero lifts.** -/
theorem diagLabelHistoryInvariant_of_diagLifts (hζ : IsFastProfile D.ζ) {Mn : SuccMenu} {m : ℕ}
    (hc2 : 0 < D.cellScaleSq m) {Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)}
    (hDL : IsDiagLifts D Dm b j₀ Mn m Cc0) (Mtop : ℕ) :
    DiagLabelHistoryInvariant D Dm b j₀ m (Mn.lenFactor * liftLength D m) Mn.N Cc0 Mtop := by
  intro n _ k ch ch' hsame t ht f
  have hl : ch.1.WellSlotted := ch.2.2.2.1
  have hl' : ch'.1.WellSlotted := ch'.2.2.2.1
  have hanc : (ch.1.geom D).2.2 = (ch'.1.geom D).2.2 := by
    rw [geom_anchor D ch.1 hl, geom_anchor D ch'.1 hl', ch.2.1, ch.2.2.2.2.1, ch'.2.1,
      ch'.2.2.2.2.1]
  have hh := (histEq_iff_sameHistory D _ _ hanc).mpr hsame
  have hav := ocPulseWindow_subset_availInterval D Mtop m k.1
  have hts : (D.cellScaleSq m)⁻¹ * t ∈ Set.Icc (D.slotStart m k.1 / D.cellScaleSq m)
      ((((k.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) :=
    WeakGen.inv_mul_mem_liftWindowOf hc2 ht
  have hG : ∀ s ∈ Set.Icc (D.slotStart m k.1 / D.cellScaleSq m)
      ((((k.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m), ∀ X : Vec 2,
      (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D m k.1 ch'.1
          (Mn.lenFactor * liftLength D m) (fun _ _ _ => [])).G s X =
        (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D m k.1 ch.1
          (Mn.lenFactor * liftLength D m) (fun _ _ _ => [])).G s X :=
    fun s hs X => WeakGen.familyLiftData_G_eq_of_histEq hζ hl hl' hh m k.1 _ _ _
      (hav (WeakGen.mul_mem_ocPulseWindow hc2 hs)) X
  have hcoef := WeakGen.familyLift_cross_unique D hζ m k.1 k.2 ch.1 ch'.1
    (Mn.lenFactor * liftLength D m) (fun _ _ _ => []) (fun _ _ _ => []) isOpen_univ
    (Set.subset_univ _) (Set.subset_univ _) _ _ (hts.1.trans hts.2) Mn.N 0 Mn.sX Mn.sZ Mn.sX Mn.sZ
    (Cc0 k.1 ch.1) (Cc0 k.1 ch'.1)
    (WeakEntryProofs.liftSequenceOn_of_global Set.univ _ Mn.sX Mn.sZ _ _ Mn.N 0 _
      (hDL k.1 ch.1 k.2 ch.2))
    (WeakEntryProofs.liftSequenceOn_of_global Set.univ _ Mn.sX Mn.sZ _ _ Mn.N 0 _
      (hDL k.1 ch'.1 k.2 ch'.2))
    (fun s hs X _ => hG s hs X) (fun s _ v u d => by simp [familyLiftData, liftEdges])
  have hP : ∀ hh' ≤ 0, ∀ n' m' (α : DerivativeWord2 m'), ∀ X ∈ (Set.univ : Set (Vec 2)),
      Cc0 k.1 ch.1 hh' n' m' α ((D.cellScaleSq m)⁻¹ * t) X =
        Cc0 k.1 ch'.1 hh' n' m' α ((D.cellScaleSq m)⁻¹ * t) X :=
    fun hh' hh'h n' m' α X hX => funext fun z => funext fun v => funext fun u =>
      hcoef hh' hh'h n' m' α _ hts X hX z v u
  refine Filter.Eventually.of_forall fun y => ?_
  unfold diagLabelFlux
  rw [Uniqueness.pathMeanFlux_eq_of_agreeOn D m _ _ _ _ n t isOpen_univ hP f y (Set.mem_univ _)]
  exact pathMeanFlux_data_point_congr m _
    (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D m k.1 ch.1
      (Mn.lenFactor * liftLength D m) (fun _ _ _ => []))
    (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D m k.1 ch'.1
      (Mn.lenFactor * liftLength D m) (fun _ _ _ => []))
    rfl rfl rfl _ n t f y (hG _ hts ((Mn.lenFactor * liftLength D m)⁻¹ • y)).symm

end AVRegularity.Providers.QuietAtlas
end
end
end

section
section
/-! **The finer outputs of the sources of a successor read only the history** (the
transfers). Two chains admissible over the same slot, with the same history geometry over the
availability interval, give the same finer output germ at the label `0`, for every source of the
successor with its lifts (`fluxOp_germ_of_histEq`). By the case of the source:
- a direct transport (`directFlux`): the fluxes of the stage agree on the common admissible labels
  (`flux_eq_of_histEq_onPulses`), a neighbourhood of `0` (`directFlux_germ_of_histEq`);
- a path mean: `pathMeanFlux_germ_of_histEq_gen`;
- a mean letter: the path mean minus the direct part of its edge;
- a covariance letter: the chart maps of the two chains agree at the time
  (`famMap_eq_of_histEq`, `famMapInv_eq_of_famMap_eq`). Push-forward, the covariance iterates and
  the Piola pullback preserve germs at `0` (`pushFlux_germ`, `covOperator_iterate_germ`,
  `pullFlux_germ`);
- the first source: its finer output vanishes.

The degenerate cases are included:
- `A = A'`: every germ equality is reflexive.
- A covariance letter with `a = a' = 0`: push-forward and pullback of the path mean.
- A mean letter on a path of length other than `1`: no direct part. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev Filter Topology

namespace AVRegularity.Providers.QuietAtlas

variable {D : OCData}

/-- Equal history geometry at a time gives the same centered map there. -/
theorem famMap_eq_of_histEq {ch ch' : RealChain} {I : Set ℝ}
    (h : HistEq (ch.geom D) (ch'.geom D) I) {u : ℝ} (hu : u ∈ I) :
    ch.famMap D u = ch'.famMap D u := by
  funext w
  have h0 := h.2 u hu 0
  rw [add_zero, add_zero] at h0
  simp only [RealChain.famMap]
  rw [h.2 u hu w, h0]

/-- Equal centered maps have equal inverses. -/
theorem famMapInv_eq_of_famMap_eq (hζ : IsFastProfile D.ζ) {ch ch' : RealChain} {u : ℝ}
    (h : ch.famMap D u = ch'.famMap D u) : ch.famMapInv D u = ch'.famMapInv D u := by
  funext x
  calc ch.famMapInv D u x = ch'.famMapInv D u (ch'.famMap D u (ch.famMapInv D u x)) :=
        (GenSem.famMapInv_famMap hζ ch' u _).symm
    _ = ch'.famMapInv D u (ch.famMap D u (ch.famMapInv D u x)) := by rw [h]
    _ = ch'.famMapInv D u x := by rw [GenSem.famMap_famMapInv hζ ch u x]

/-- The Piola pullback by a chart germ fixing `0` preserves germs at `0`. -/
theorem pullFlux_germ {Φ Φinv : Vec 2 → Vec 2} (hc : ContinuousAt Φ 0) (h0 : Φ 0 = 0)
    {F F' : (Vec 2 → ℝ) → Vec 2 → Vec 2} (hF : ∀ g, F g =ᶠ[𝓝 0] F' g) (u : Vec 2 → ℝ) :
    pullFlux Φ Φinv F u =ᶠ[𝓝 0] pullFlux Φ Φinv F' u := by
  have hmem := hc.preimage_mem_nhds (by rw [h0]; exact hF (u ∘ Φinv))
  filter_upwards [hmem] with y hy
  unfold pullFlux
  rw [show F (u ∘ Φinv) (Φ y) = F' (u ∘ Φinv) (Φ y) from hy]

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **The direct parts of two chains with the same history agree as germs.** -/
theorem directFlux_germ_of_histEq (hζ : IsFastProfile D.ζ) (hΛ : 1 ≤ D.Λ)
    {G : GenStage D hr Dm b j₀} {Mtop : ℕ} (hcov : FluxRecenterCovariantOnPulses G)
    (hinv : StageHistoryInvariant G Mtop) (k : OddSlot) {A A' : RealChain}
    (hA : IsAdmissibleChain D b j₀ G.level k.1 A) (hA' : IsAdmissibleChain D b j₀ G.level k.1 A')
    (hh : HistEq (A.geom D) (A'.geom D) (availInterval D Mtop G.level k.1)) {t : ℝ}
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level k.1) {v u : CompIn G.comps}
    (γ : G.fam.Γ v u) (ords : Finset ℕ) (f : Vec 2 → ℝ) :
    directFlux G k ⟨A, hA⟩ γ ords t f =ᶠ[𝓝 0] directFlux G k ⟨A', hA'⟩ γ ords t f := by
  have hε : D.eps (G.level - 1) ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  set V := {y : Vec 2 | IsAdmissibleChain D b j₀ G.level k.1 (A.recenter D y)} ∩
    {y : Vec 2 | IsAdmissibleChain D b j₀ G.level k.1 (A'.recenter D y)}
  have hV : IsOpen V := (GenSem.isOpen_admissible_recenter D b j₀ _ _ A).inter
    (GenSem.isOpen_admissible_recenter D b j₀ _ _ A')
  have h0V : (0 : Vec 2) ∈ V := by
    refine ⟨?_, ?_⟩
    · show IsAdmissibleChain D b j₀ G.level k.1 (A.recenter D 0)
      rw [GenSem.recenter_zero D hζ]; exact hA
    · show IsAdmissibleChain D b j₀ G.level k.1 (A'.recenter D 0)
      rw [GenSem.recenter_zero D hζ]; exact hA'
  filter_upwards [hV.mem_nhds h0V] with y hy
  have hsc : D.eps (G.level - 1) • ((D.eps (G.level - 1))⁻¹ • y) = y := smul_inv_smul₀ hε y
  have hY : IsAdmissibleChain D b j₀ G.level k.1
      (A.recenter D (D.eps (G.level - 1) • ((D.eps (G.level - 1))⁻¹ • y))) := by
    rw [hsc]; exact hy.1
  have hY' : IsAdmissibleChain D b j₀ G.level k.1
      (A'.recenter D (D.eps (G.level - 1) • ((D.eps (G.level - 1))⁻¹ • y))) := by
    rw [hsc]; exact hy.2
  unfold directFlux
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun α _ => ?_
  rw [show (fun z => G.fam.flux k ⟨A, hA⟩ v u γ d α t ((D.eps (G.level - 1))⁻¹ • y) z) =
      (fun z => G.fam.flux k ⟨A', hA'⟩ v u γ d α t ((D.eps (G.level - 1))⁻¹ • y) z) from
    funext fun z => flux_eq_of_histEq_onPulses hζ hcov hinv k hA hA' hh ht v u γ d α hY hY' z]

open scoped Classical in
/-- **The finer outputs of two chains with the same history agree as germs** at the label `0`,
for every source of the successor with its lifts. -/
theorem fluxOp_germ_of_histEq (hζ : IsFastProfile D.ζ) (hΛ : 1 ≤ D.Λ)
    {G : GenStage D hr Dm b j₀} (hc2 : 0 < D.cellScaleSq G.level) {Mtop : ℕ}
    (hcov : FluxRecenterCovariantOnPulses G) (hinv : StageHistoryInvariant G Mtop)
    (Mn : SuccMenu) (s₀ : ℝ) (s : SuccSource G)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ))
    (hlift : s.IsLiftFamily Mn Cc) (k : OddSlot) {A A' : RealChain}
    (hA : IsAdmissibleChain D b j₀ G.level k.1 A) (hA' : IsAdmissibleChain D b j₀ G.level k.1 A')
    (hh : HistEq (A.geom D) (A'.geom D) (availInterval D Mtop G.level k.1)) {t : ℝ}
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level k.1) (f : Vec 2 → ℝ) :
    s.fluxOp (Mn.lenFactor * liftLength D G.level) s₀ Cc k.1 t A f =ᶠ[𝓝 0]
      s.fluxOp (Mn.lenFactor * liftLength D G.level) s₀ Cc k.1 t A' f := by
  have htI := ocPulseWindow_subset_availInterval D Mtop G.level k.1 ht
  have hΦ : A.famMap D t = A'.famMap D t := famMap_eq_of_histEq hh htI
  have hΦi : A.famMapInv D t = A'.famMapInv D t := famMapInv_eq_of_famMap_eq hζ hΦ
  unfold SuccSource.fluxOp
  rw [dite_eq_left ⟨hA, k.2⟩, dite_eq_left ⟨hA', k.2⟩]
  cases s with
  | copyDir t' v u γ => exact directFlux_germ_of_histEq hζ hΛ hcov hinv k hA hA' hh ht γ _ f
  | letterDiag t' u => exact EventuallyEq.rfl
  | copyQuad t' h π =>
    exact pathMeanFlux_germ_of_histEq_gen hζ hΛ hc2 hcov hinv k hA hA' hh π _ Mn.sX Mn.sZ Mn.sX
      Mn.sZ Mn.N _ _ (hlift k.1 A ⟨hA, k.2⟩) (hlift k.1 A' ⟨hA', k.2⟩) 2 ht f
  | letterMean t' n h π =>
    have hpm := pathMeanFlux_germ_of_histEq_gen hζ hΛ hc2 hcov hinv k hA hA' hh π _ Mn.sX Mn.sZ
      Mn.sX Mn.sZ Mn.N _ _ (hlift k.1 A ⟨hA, k.2⟩) (hlift k.1 A' ⟨hA', k.2⟩) n ht f
    by_cases h1 : h = 1
    · subst h1
      have hdir := directFlux_germ_of_histEq hζ hΛ hcov hinv k hA hA' hh ht
        (π.step ⟨0, by omega⟩).2.2 {n} f
      filter_upwards [hpm, hdir] with y hy1 hy2
      simp only [↓reduceDIte]
      rw [hy1, hy2]
    · filter_upwards [hpm] with y hy1
      simp only [h1, ↓reduceDIte]
      rw [hy1]
  | letterCov t' n h a a' π =>
    rw [← hΦ, ← hΦi]
    have hpush : ∀ g : Vec 2 → ℝ,
        pushFlux (A.famMap D t) (A.famMapInv D t)
          (pathMeanFlux D G.level (Mn.lenFactor * liftLength D G.level)
            (familyLiftData D G.level k.1 A (Mn.lenFactor * liftLength D G.level)
              (pathEdges G π k ⟨A, hA⟩)) (Cc k.1 A) n t) g =ᶠ[𝓝 0]
        pushFlux (A.famMap D t) (A.famMapInv D t)
          (pathMeanFlux D G.level (Mn.lenFactor * liftLength D G.level)
            (familyLiftData D G.level k.1 A' (Mn.lenFactor * liftLength D G.level)
              (pathEdges G π k ⟨A', hA'⟩)) (Cc k.1 A') n t) g :=
      fun g => Uniqueness.pushFlux_germ (GenSem.contDiff_famMapInv A t).continuous.continuousAt
        (GenSem.famMapInv_zero hζ A t)
        (fun g' => pathMeanFlux_germ_of_histEq_gen hζ hΛ hc2 hcov hinv k hA hA' hh π _ Mn.sX
          Mn.sZ Mn.sX Mn.sZ Mn.N _ _ (hlift k.1 A ⟨hA, k.2⟩) (hlift k.1 A' ⟨hA', k.2⟩) n ht g') g
    refine pullFlux_germ (GenSem.contDiff_famMap A t).continuous.continuousAt
      (GenSem.famMap_zero A t) (fun g => ?_) f
    have hcg := Uniqueness.covOperator_iterate_germ
      (ocCovariance D.α D.q D.Λ D.ζ G.level (D.κ G.level) (D.κ (G.level - 1)) s₀ t) a
      (hpush ((SuccSource.covAt D G.level s₀ t)^[a'] g))
    filter_upwards [hcg] with x hx
    simp only [SuccSource.covAtFlux]
    rw [hx]

end AVRegularity.Providers.QuietAtlas
end
end

section
/-! **(b) The carried finer-operator invariant of an actual successor.** For the
presentation by `successorQuietSource`:
- a diagonal letter reads the label flux of the grade-zero lifts, whose history dependence is the
  named hypothesis `DiagLabelHistoryInvariant`;
- a transfer reads the finer output of its source, which depends only on the history through the
  parent's carried invariant and its recenter covariance at the output times
  (`fluxOp_germ_of_histEq`). The covariance comes from the parent's presentation or from
  `IsGenerated` (used by `successorQuietMatching_of_generated`);
  `successorFinerHistory_of_covariant` takes it as a hypothesis.
Two contexts over the slot with the same history geometry have the same anchor, so the geometry
agrees as `HistEq` (`histEq_iff_sameHistory`).

The `ChainEnv` premise of the statement is not used.

The degenerate cases are included:
- No diagonal letter: `DiagLabelHistoryInvariant` is not read.
- A parent without identities: every transfer source has no path and no direct part.
- `ch = ch'`: reflexive. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev Filter Topology

namespace AVRegularity.Providers.QuietAtlas

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **(b), from the parent's covariance at the output times.** -/
theorem successorFinerHistory_of_covariant {P : ProvParams} {Mn : SuccMenu}
    {G G' : GenStage D hr Dm b j₀} (hG : 1 ≤ G.level) (hG' : G'.level = G.level - 1)
    (hζ : IsFastProfile D.ζ) (hΛ : 1 ≤ D.Λ) (hc2 : 0 < D.cellScaleSq G.level)
    (w : ActualSuccessorWitness D P Mn G G') (P' : QuietPresentation G')
    (hP' : P'.source = successorQuietSource w) (hcov : FluxRecenterCovariantOnPulses G)
    {Mtop : ℕ} (hinv : StageHistoryInvariant G Mtop)
    (hdiag : DiagLabelHistoryInvariant D Dm b j₀ G.level (Mn.lenFactor * liftLength D G.level)
      Mn.N w.Cc0 Mtop) :
    FinerHistoryInvariant G' P' Mtop := by
  have hL : G'.level + 1 = G.level := by omega
  intro v' u' γ' n hn k ch ch' hsame t ht f
  rw [hP'] at hn ⊢
  unfold successorQuietSource at hn ⊢
  by_cases hd : (w.e v' u' γ').1.IsDiag
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hd)] at hn ⊢
    simp only [QuietSource.finer, QuietSource.degrees] at hn ⊢
    generalize Mn.lenFactor * liftLength D G.level = ρ at hdiag ⊢
    rw [← hL] at hdiag
    exact hdiag n hn k ch ch' hsame t ht f
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hd)]
    simp only [QuietSource.finer]
    have hA : IsAdmissibleChain D b j₀ G.level k.1 ch.1 := by rw [← hL]; exact ch.2
    have hA' : IsAdmissibleChain D b j₀ G.level k.1 ch'.1 := by rw [← hL]; exact ch'.2
    have ht' : t ∈ ocPulseWindow D.α D.q D.Λ G.level k.1 := by rw [← hL]; exact ht
    have hanc : (ch.1.geom D).2.2 = (ch'.1.geom D).2.2 := by
      rw [geom_anchor D ch.1 ch.2.2.2.1, geom_anchor D ch'.1 ch'.2.2.2.1, ch.2.1, ch.2.2.2.2.1,
        ch'.2.1, ch'.2.2.2.2.1]
    have hh : HistEq (ch.1.geom D) (ch'.1.geom D) (availInterval D Mtop G.level k.1) := by
      rw [← hL]
      exact (histEq_iff_sameHistory D _ _ hanc).mpr hsame
    exact fluxOp_germ_of_histEq hζ hΛ hc2 hcov hinv Mn Mn.anchor _ _ (w.lifts _) k hA hA' hh ht' f

end AVRegularity.Providers.QuietAtlas
end
end

section
/-! **(c) The array form of the first sources of an actual successor.**
`firstSourceFlux_applyArr` at a native context `(nativeChain i p).recenter D X` of level `i`
(`firstSourceFlux_native_applyArr`). Its inputs:
- the scheduled finer slots form a finite set (`scheduledSlots_finite`);
- the context strain of a well-slotted chain is smooth (`contDiff_contextStrain_recenter`);
- the grade-zero lifts are global lift sequences of the edgeless family (`IsDiagLifts`), so
  regular of every order at most `min sX sZ` (`liftRegular_of_isLiftSequence`). This is used at
  the cell time of a physical time with a nonzero finer cutoff.
The successor's first sources are these (`successorFirstSourceArrayForm`).

The degenerate cases are included:
- No diagonal letter: no source is a first source, and the clause is vacuous.
- `2 * p + Dm + 2 = sX = sZ`: the minimal reserves; the lifts are regular of exactly that order.
- A time with no scheduled finer slot with nonzero cutoff: the regularity premise is vacuous. -/

@[expose] public noncomputable section

open Set Homogenization AVRegularity.Sobolev

namespace AVRegularity.Providers.QuietAtlas

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **The first source at a native context is an array operator** on smooth test fields. -/
theorem firstSourceFlux_native_applyArr (hζ : IsFastProfile D.ζ) (hΛ : 1 ≤ D.Λ) {i : ℕ}
    (hc : 0 < D.cellScaleSq (i + 1)) {ρ : ℝ} (hρ : ρ ≠ 0) {N pc : ℕ} (hN : 1 ≤ N) {sX sZ : ℕ}
    (hRX : 2 * pc + Dm + 2 ≤ sX) (hRZ : 2 * pc + Dm + 2 ≤ sZ) (s₀ : ℝ)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (hDL : ∀ (k : ℤ) (A : RealChain), Odd k → IsAdmissibleChain D b j₀ (i + 1) k A →
      IsLiftSequence (GenSem.diagQ D Dm (i + 1) k A ρ) sX sZ
        (D.slotStart (i + 1) k / D.cellScaleSq (i + 1))
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ (i + 1)) / D.cellScaleSq (i + 1)) N 0
        (Cc0 k A))
    (p : ℤ) (t : ℝ) (X z : Vec 2) :
    ∃ (K : ℕ) (Arr : Fin 2 → GenSem.CArr), ∀ g : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → ∀ c,
      firstSourceFlux D b j₀ Dm (i + 1) ρ N pc s₀ Cc0 t ((nativeChain i p).recenter D X) z g 0 c =
        GenSem.applyArr K (Arr c) g 0 0 := by
  have hτ : 0 < ocTau D.α D.q D.Λ (i + 1) := Construction.Stream.ocTau_pos hΛ
  have hfin := GenSem.scheduledSlots_finite D i p hτ
  set ch := (nativeChain i p).recenter D X with hch
  have hl : ch.WellSlotted := rfl
  refine ⟨2 * pc + (N + 1 + 2 * pc),
    fun c => GenSem.fsArr D b j₀ Dm (i + 1) ρ N pc s₀ Cc0 hfin.toFinset t ch z c,
    fun g hg c => ?_⟩
  refine GenSem.firstSourceFlux_applyArr hζ hρ hN t ch z hfin.toFinset ?_ ?_ ?_ hg 0 c
  · intro k
    rw [Nat.add_sub_cancel]
    exact hfin.mem_toFinset
  · intro a c'
    have htop : ∀ r : ℕ, ((r : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := fun r => by
      exact_mod_cast le_top
    have e : (fun x => GenSem.strainAt D (i + 1) t ch z x a c') =
        (fun y => contextStrain D i ch.slot t (ch.recenter D y) (z + (D.eps i)⁻¹ • y) a c') ∘
          ch.famMapInv D t := by
      funext x
      simp only [GenSem.strainAt, Function.comp_apply, Nat.add_sub_cancel]
    rw [e]
    exact ((GenSem.contDiff_contextStrain_recenter D hζ i ch.slot t ch hl z a c').comp
      (GenSem.contDiff_famMapInv ch t)).of_le (htop (4 * pc))
  · intro n _ _ k hk hA hcut
    have ht := GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hcut
    have hts : (D.cellScaleSq (i + 1))⁻¹ * t ∈ Icc (D.slotStart (i + 1) k / D.cellScaleSq (i + 1))
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ (i + 1)) / D.cellScaleSq (i + 1)) := by
      rw [inv_mul_eq_div]
      exact ⟨div_le_div_of_nonneg_right ht.1 hc.le, div_le_div_of_nonneg_right ht.2 hc.le⟩
    exact GenSem.liftRegular_of_isLiftSequence D (i + 1) k hA.2.2.1 ρ
      (hDL k _ (hfin.mem_toFinset.1 hk).1 hA) hRX hRZ 0 le_rfl n _ hts 0

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]

/-- **(c)**: the first sources of an actual successor are array operators. -/
theorem successorFirstSourceArrayForm :
    FirstSourceArrayFormStatement (hr := hr) (D := D) (Dm := Dm) (b := b) (j₀ := j₀) := by
  intro P Mn G G' hG hG' hζ hΛ hc hN hRX hRZ hρ w P' hP' U v u γ lam ρ s₀ N pc Cc0 hsrc p t _ _
    X z
  have hL : G'.level + 1 = G.level := by omega
  rw [hP'] at hsrc
  unfold successorQuietSource at hsrc
  by_cases hdiag : (w.e v u γ).1.IsDiag
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hdiag)] at hsrc
    cases hsrc
    have hDL := w.diag
    rw [← hL] at hDL hc hρ
    rw [← hL]
    exact firstSourceFlux_native_applyArr hζ hΛ hc hρ hN hRX hRZ Mn.anchor w.Cc0
      (fun k A hk hA => hDL k A hk hA) p.1 t X z
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hdiag)] at hsrc
    cases hsrc

end AVRegularity.Providers.QuietAtlas
end
end

section
/-! **The quiet matching of an actual successor**: the assembly with (a)
`successorQuietPresentation`, (b) `successorFinerHistory_of_covariant` and (c)
`successorFirstSourceArrayForm`.

Its inputs at a parent are `StageHistoryInvariant G Mtop`, `DiagLabelHistoryInvariant`, a
presentation of the parent, and the data premises; nothing else is assumed. The degenerate cases
are included:
- No diagonal letter: the first-source inputs are vacuous.
- An empty successor: every clause is vacuous.

`successorQuietMatching_of_generated` is the same clause for a generated parent with no
presentation (the terminal parent `Gw`, whose `IsWeakStage` gives `IsGenerated` but no
construction). The first-source hypothesis comes from the witness
(`diagLabelHistoryInvariant_of_diagLifts`), and no `ChainEnv` is needed. -/

@[expose] public noncomputable section

namespace AVRegularity.Providers.QuietAtlas

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **The quiet matching of an actual successor of a generated parent.** -/
theorem successorQuietMatching_of_generated {P : ProvParams} {Mn : SuccMenu}
    {G G' : GenStage D hr Dm b j₀} (hG : 1 ≤ G.level) (hG' : G'.level = G.level - 1)
    (hζ : IsFastProfile D.ζ) (hΛ : 1 ≤ D.Λ) (hb : 0 < b) (hc2 : 0 < D.cellScaleSq G.level)
    (hN : 1 ≤ Mn.N) (hRX : 2 * Mn.p + Dm + 2 ≤ Mn.sX) (hRZ : 2 * Mn.p + Dm + 2 ≤ Mn.sZ)
    (hρ : Mn.lenFactor * liftLength D G.level ≠ 0) (hi : 1 ≤ G'.level) (hj : j₀ ≤ G'.level)
    {CH Υ : ℝ} (hCH : 1 ≤ CH) (hstart : IsCarrierStart D.α D.q D.Λ b CH Υ j₀)
    (w : ActualSuccessorWitness D P Mn G G') (hgen : G.IsGenerated) {Mtop : ℕ} {S W : Set ℝ}
    (hnat : G'.IsNatural Mtop) (hS : IsHistoryQuiet D Mtop G'.level S)
    (hinv : StageHistoryInvariant G Mtop) (hT : G'.IsSlotTransverse) : QuietMatchingOn G' S W := by
  obtain ⟨P', hP'⟩ := successorQuietPresentation P Mn G G' hG hG' w
  have hF := successorFinerHistory_of_covariant hG hG' hζ hΛ hc2 w P' hP'
    (fluxRecenterCovariantOnPulses_of_generated hζ hgen) hinv
    (diagLabelHistoryInvariant_of_diagLifts hζ hc2 w.diag Mtop)
  have hSQ := hS.union (isHistoryQuiet_ocTrimmedQuiet hΛ hCH hstart Mtop G'.level hj)
  exact quietMatching_of_firstSource (quietSourcePhase D) G' P' Mtop S W hΛ hζ hb hi hj CH Υ hCH
    hstart hnat hS (quietPhaseBlind_of_finerHistory hb hΛ hζ G' P' Mtop _ hSQ hF)
    (quietReanchors_of_finerHistory hb hΛ hζ G' P' Mtop _ hi hj hSQ hF)
    (successorFirstSourceArrayForm P Mn G G' hG hG' hζ hΛ hc2 hN hRX hRZ hρ w P' hP' _) hT

end AVRegularity.Providers.QuietAtlas
end
end
end
